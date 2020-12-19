Module NatList.
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Require Import FunInd FMapInterface.
From Coq Require Import Ascii.
Import ListNotations.
Require Import Le Gt Minus Min Bool.
Require Import Setoid.

Set Implicit Arguments.

(* SINTAXA *)
Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.

Definition Env := string -> nat.

Inductive aexp :=
| avar : string -> aexp
| anum : nat -> aexp
| aplus : aexp -> aexp -> aexp
| aminus : aexp -> aexp -> aexp 
| adivision : aexp -> aexp -> aexp 
| amodulo : aexp -> aexp -> aexp 
| amul : aexp -> aexp -> aexp.

Coercion anum : nat >-> aexp.
Coercion avar : string >-> aexp.

Fixpoint divmod x y q u :=
  match x with
    | 0 => (q,u)
    | S x' => match u with
                | 0 => divmod x' y (S q) y
                | S u' => divmod x' y q u'
              end
  end.
Definition div x y :=
  match y with
    | 0 => y
    | S y' => fst (divmod x y' 0 y')
  end.

Definition nmodulo x y :=
  match y with
    | 0 => y
    | S y' => y' - snd (divmod x y' 0 y')
  end.

Infix "/" := div : nat_scope.
Infix "mod" := nmodulo (at level 40, no associativity) : nat_scope.

Fixpoint aeval_fun (a : aexp) (env : Env) : nat :=
  match a with
  | avar k => env k
  | anum v => v
  | aplus a1 a2 => (aeval_fun a1 env) + (aeval_fun a2 env)
  | aminus a1 a2 => (aeval_fun a1 env) - (aeval_fun a2 env) 
  | adivision a1 a2 => (aeval_fun a1 env) / (aeval_fun a2 env) 
  | amodulo a1 a2 => (aeval_fun a1 env) mod (aeval_fun a2 env) 
  | amul a1 a2 => (aeval_fun a1 env) * (aeval_fun a2 env)
  end.


Inductive bexp :=
| btrue : bexp
| bfalse : bexp
| blessthan : aexp -> aexp -> bexp
| bequal : aexp -> aexp -> bexp
| bnot : bexp -> bexp
| band : bexp -> bexp -> bexp.

Fixpoint beval_fun (b : bexp) (env : Env) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | blessthan a1 a2 => Nat.leb (aeval_fun a1 env) (aeval_fun a2 env)
  | bequal a1 a2 => (aeval_fun a1 env) =? (aeval_fun a2 env)
  | bnot b' => negb (beval_fun b' env)
  | band b1 b2 => match (beval_fun b1 env), (beval_fun b2 env) with
                  | true, true => false
                  | true, false => true
                  | false, true => true
                  | false, false => false
                  end
  end.
(*Inductive listNat : Type :=
| nil
| cons ( n : string ) ( l : listNat) .*)

Notation "'declare' var" :=(avar var) (at level 40). 
Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (aminus A B) (at level 48).  
Notation "A //' B" := (adivision A B) (at level 46).  
Notation "A %' B" := (amodulo A B) (at level 46).  
Notation "A *' B" := (amul A B) (at level 46).

Notation "'~' A" := (bnot A) (at level 75, right associativity).
Notation "A <=' B" := (blessthan A B) (at level 53).
Notation "A ==' B" := (bequal A B) (at level 70, no associativity).
Notation "A >=' B" := (blessthan B A) (at level 53).
Infix "and'" := band (at level 80).

(*Notation " x :=: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).*)

Inductive Stmt :=
| assignment : string -> aexp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : bexp -> Stmt -> Stmt
| iff : bexp -> Stmt -> Stmt -> Stmt
| iffsimpl : bexp -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'ifs' cond 'den' { stmt }" := (iffsimpl cond stmt) (at level 93).
Notation "'ifd' cond 'denn' { stmt1 } 'els' { stmt2 }" := (iff cond stmt1 stmt2) (at level 93).
Notation "'While' ( B ) { S }" := (while B S) (at level 97).
Notation "'phor' ( s1 ~ cond ~ s2 ) { stmt }" := (s1 ;; While ( cond ) { stmt ;; s2 }  ) (at level 97).
Notation "'do' { stmt } 'whilee' ( cond )" := ( stmt ;; While ( cond ) { stmt } ) (at level 97).

Require Import String.
Open Scope string_scope.
(* itoa *)
Class Shows A : Type :=
  {
    itoa : A -> string;
  }.
Class Shown A : Type :=
  {
    atoi : A -> nat
  }.
Fixpoint nat_to_string_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in (*append*)
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => nat_to_string_aux time' n' acc'
      end
  end.

Definition nat_to_string (n : nat) : string :=
  nat_to_string_aux n n "".
Instance showNat : Shows nat :=
  {
    itoa := nat_to_string
  }.
Compute (itoa 42).

Definition is_nat (x : ascii) : nat :=
  match x with
  | "0" => 0
  | "1" => 1
  | "2" => 2
  | "3" => 3
  | "4" => 4
  | "5" => 5
  | "6" => 6
  | "7" => 7
  | "8" => 8
  | "9" => 9
  | _ =>   0
  end%char.


Definition first_ch (l:list ascii) : ascii := (* Preia primul elem din lista *)
    match l with
      | nil => " "
      | a :: nill => a
    end.
Definition remuve_first_ch (l:list ascii) : list ascii := (* Sterge primul elem din lista *)
    match l with
      | nil => []
      | a :: m => m
    end.
Fixpoint list_ascii_of_string (s : string) : list ascii (* De la string la lista ascii *)
  := match s with
     | EmptyString => []
     | String ch s => cons ch (list_ascii_of_string s)
     end.



