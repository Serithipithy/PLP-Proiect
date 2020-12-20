Module NatList.
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Ascii.




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

Inductive bexp :=
| btrue : bexp
| bfalse : bexp
| blessthan : aexp -> aexp -> bexp
| bequal : aexp -> aexp -> bexp
| bnot : bexp -> bexp
| band : bexp -> bexp -> bexp.

(* Stiva *)
Inductive listNat : Type :=
| nil
| cons ( n : nat ) ( l : listNat) .

Inductive Stiva : Type :=
| stiva : string -> listNat -> Stiva.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Notation " name { x ; y ; .. ; z }" := ( stiva name (cons x (cons y .. (cons z nil) ..))) (at level 30) .

Inductive stexp1 :=
| push : nat -> stexp1
| top : Stiva -> stexp1.

Inductive stexp2 :=
| pop : Stiva -> stexp2
| stempty : Stiva -> stexp2.


(* Stings *)

Require Import String.
Open Scope string_scope.
(* itoa *)
Fixpoint nat_to_string_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => nat_to_string_aux time' n' acc'
      end
  end.

(* atoi *)

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

Fixpoint reverse_string ( s: string ) : string :=
match s with
| EmptyString => EmptyString
| String ch rest => (reverse_string rest) ++ (String ch EmptyString)
end.

Fixpoint string_to_nat_aux ( s : string ) : nat :=
match s with
  | EmptyString => 0
  | String ch rest =>
    match ( is_nat ch ), (string_to_nat_aux rest) with
      | x, y => x +  y * 10
    end
end.

Definition string_to_nat ( s: string ) : nat :=
match string_to_nat_aux(reverse_string s) with
  | n => n
end.

(* Lambda *)

(* stmt *)
Inductive Stmt :=
| declarare_var : string -> Stmt 
| declarare_string : string -> Stmt
| declarare_stiva : Stiva -> Stmt
| assignment : string -> aexp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : bexp -> Stmt -> Stmt
| iff : bexp -> Stmt -> Stmt -> Stmt
| iffsimpl : bexp -> Stmt -> Stmt.

Notation "'int' var" :=(declarare_var var) (at level 40).
Notation "'int_stack' var" :=(declarare_stiva var) (at level 40).
Notation "'str' var" :=(declarare_string var) (at level 40).
Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'ifs' cond 'den' { stmt }" := (iffsimpl cond stmt) (at level 93).
Notation "'ifd' cond 'denn' { stmt1 } 'els' { stmt2 }" := (iff cond stmt1 stmt2) (at level 93).
Notation "'While' ( B ) { S }" := (while B S) (at level 97).
Notation "'phor' ( s1 ~ cond ~ s2 ) { stmt }" := (s1 ;; While ( cond ) { stmt ;; s2 }  ) (at level 97).
Notation "'do' { stmt } 'whilee' ( cond )" := ( stmt ;; While ( cond ) { stmt } ) (at level 97).

