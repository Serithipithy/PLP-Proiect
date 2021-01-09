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
Require Import String.
Open Scope string_scope.
Scheme Equality for string.

Set Implicit Arguments.


Definition Variabila := string -> nat. (* Pt expresii aritmetice*)

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

Inductive bexp :=
| btrue : bexp
| bfalse : bexp
| blessthan : aexp -> aexp -> bexp
| bequal : aexp -> aexp -> bexp
| bnot : bexp -> bexp
| band : bexp -> bexp -> bexp.

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

Compute 10 +' 11.
Compute 15 +' "a".
Compute "b" +' 3.
Compute "a" +' "b".

Compute 10 -' 11.
Compute 15 -' "a".
Compute "b" -' 3.
Compute ("a") -' ("b").

Compute 10 *' 11.
Compute 15 *' "a".
Compute "b" *' 3.
Compute ("a") *' ("b").

Compute 10 //' 11.
Compute 15 //' "a".
Compute "b" //' 3.
Compute ("a") //' ("b").

Compute 10 %' 11.
Compute 15 %' "a".
Compute "b" %' 3.
Compute ("a") %' ("b"). 


(* Stiva *)
Inductive listNat : Type :=
| nil
| cons ( n : nat ) ( l : listNat) .

Definition Stiva := string -> listNat. (* Pt stive *)

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Infix "::" := cons (at level 60, right associativity) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Compute [ 10 ; 15 ; 16 ; 5].

Inductive stexp :=
| sstack : listNat ->stexp
| push : listNat -> nat -> stexp
| pop : listNat -> stexp
| stempty : listNat -> stexp.
Inductive stexp2 :=
| top : listNat -> stexp2.

Notation "'push'( stack , x )" := ( push stack x ) (at level 60).
Notation "'top'( stack )" := ( top stack ) (at level 60).
Notation "'pop'( stack )" := ( pop stack ) (at level 60).
Notation "'empty_stack'( stack )" := ( stempty stack ) (at level 60).

Compute push ([10 ; 15 ; 16 ; 5])  (10).
Compute top ([10 ; 15 ; 16 ; 5]).
Compute pop ([10 ; 15 ; 16 ; 5]).
Compute stempty ([10 ; 15 ; 16 ; 5]).

Definition Strings := string -> string. (* Pt strings *)

Inductive strexp1 :=
| atoi : string -> strexp1.

Inductive strexp2 :=
| itoa : nat -> strexp2.

Compute (atoi "13").

(* stmt *)
Inductive Stmt :=
| assignment_string : string -> string -> Stmt
| assignment_stiva : string -> listNat -> Stmt
| assignment : string -> aexp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : bexp -> Stmt -> Stmt
| iff : bexp -> Stmt -> Stmt -> Stmt
| iffsimpl : bexp -> Stmt -> Stmt.

Notation "'stack' var :=: variabile" :=(assignment_stiva var variabile) (at level 40).
Notation "'str' var <<->> ass" :=(assignment_string var ass) (at level 40).
Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'ifs' cond 'den' { stmt }" := (iffsimpl cond stmt) (at level 93).
Notation "'ifd' cond 'denn' { stmt1 } 'els' { stmt2 }" := (iff cond stmt1 stmt2) (at level 93).
Notation "'While' ( B ) { S }" := (while B S) (at level 97).
Notation "'phor' ( s1 ~ cond ~ s2 ) { stmt }" := (s1 ;; While ( cond ) { stmt ;; s2 }  ) (at level 97).
Notation "'do' { stmt } 'whilee' ( cond )" := ( stmt ;; While ( cond ) { stmt } ) (at level 97).


Example ex1 :=
stack "a" :=: [ 1 ; 2 ; 3] ;;
"c" ::= 10 ;;
str "b" <<->> "ana"
.
Compute ex1.

Inductive Configuration := 
| conf: Variabila -> Strings -> Stiva -> Configuration.

(* SEMANTICA *)
Definition e_var : Variabila :=  (* Pt expresii aritmetice*)
  fun x =>
    if (string_eq_dec x "fix")
    then 10
    else 0.
Check e_var.

Definition update_var (c : Configuration) (x : string) (v : nat) : Variabila :=
match c with
| conf vvar vstring vstiva =>   fun y =>
                                    if (string_eq_dec y x)
                                    then v
                                    else (vvar y)
end.
Notation "S [ V /' X ]" := (update_var S X V) (at level 0).

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

Fixpoint aeval_fun (a : aexp) (c :Configuration) : nat :=
match c with
| conf vvar vstring vstiva => 
                              match a with
                                | avar k => vvar k
                                | anum v => v
                                | aplus a1 a2 => (aeval_fun a1 c) + (aeval_fun a2 c)
                                | aminus a1 a2 => (aeval_fun a1 c) - (aeval_fun a2 c) 
                                | adivision a1 a2 => (aeval_fun a1 c) / (aeval_fun a2 c) 
                                | amodulo a1 a2 => (aeval_fun a1 c) mod (aeval_fun a2 c) 
                                | amul a1 a2 => (aeval_fun a1 c) * (aeval_fun a2 c)
                                end
end.
Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive aeval : aexp -> Variabila -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n (* <n,sigma> => <n> *) 
| var : forall v sigma, avar v =[ sigma ]=> (sigma v) (* <v,sigma> => sigma(x) *)
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| minus : forall a1 a2 i1 i2 sigma n, 
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 / i2 ->
    a1 //' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 mod i2 ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Fixpoint beval_fun (b : bexp) (c : Configuration) : bool :=
match c with
| conf bvar bstring bstiva => 
                            match b with
                            | btrue => true
                            | bfalse => false
                            | blessthan a1 a2 => Nat.leb (aeval_fun a1 c) (aeval_fun a2 c)
                            | bequal a1 a2 => Nat.eqb (aeval_fun a1 c) (aeval_fun a2 c)
                            | bnot b' => negb (beval_fun b' c)
                            | band b1 b2 => match (beval_fun b1 c), (beval_fun b2 c) with
                                            | true, true => false
                                            | true, false => true
                                            | false, true => true
                                            | false, false => false
                                            end
  end
end.

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : bexp -> Variabila -> bool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.leb i1 i2 ->
    a1 <=' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
where "B ={ S }=> B'" := (beval B S B').

(* Stiva *)

Definition e_stiva : Stiva :=  (* Pt stive *)
  fun x =>
    if (string_eq_dec x "fix2")
    then [ ]
    else [ ].
Check e_stiva.

Definition update_stiva (c : Configuration) (x : string) (v : listNat ) : Stiva :=
match c with
| conf svar sstring sstiva =>   fun y =>
                                    if (string_eq_dec y x)
                                    then v
                                    else (sstiva y)
end.

Notation "S [[ V /' X ]]" := (update_stiva S X V) (at level 0).
Fixpoint pop_stack ( l: listNat) : listNat :=
match l with
| nil => nil
| [ a ] => []
| a :: l => a :: pop_stack l
end.

Fixpoint push_stack ( l: listNat) ( x : nat ) : listNat :=
match l with
| nil => [x]
| a :: l => a :: push_stack l x
end.

Fixpoint top_stack (l:listNat ) (d:nat) {struct l} : nat :=
match l with
| nil => d
| a :: nil => a
| a :: l => top_stack l d
end.

Definition sempty_stack ( l: listNat) : listNat :=
match l with
| [] => []
| a :: l => []
end.

Compute pop_stack ([10 ; 15 ; 16 ; 5]).
Compute push_stack ([10 ; 15 ; 16 ; 5]) (10).
Compute top_stack ([10 ; 15 ; 16 ; 5]).
Compute sempty_stack ([10 ; 15 ; 16 ; 5]).

Definition seval_fun ( s : stexp ) (env : Stiva) : listNat :=
match s with
| sstack x => x
| push a b => push_stack a b
| pop a => pop_stack a
| stempty a => sempty_stack a
end.

Definition seval_fun2 ( s : stexp2 ) ( a : nat ) (env : Stiva) : nat :=
match s with
| top x => top_stack x a
end.

(* Strings *)
Definition e_string : Strings :=  (* Pt strings *)
  fun x =>
    if (string_eq_dec x "fix3")
    then ""
    else "".
Check e_string.
Definition update_string (c : Configuration) (x : string) (v : string ) : Strings :=
match c with
| conf svar sstring sstiva =>   fun y =>
                                    if (string_eq_dec y x)
                                    then v
                                    else (sstring y)
end.

Notation "S [[[ V /' X ]]]" := (update_string S X V) (at level 0).
(* itoa *)
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

Definition streval_fun2 ( s : strexp2 ) (env : Strings) : string :=
match s with
| itoa n => nat_to_string n
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

Definition streval_fun1 ( s : strexp1 ) (env : Strings) : nat :=
match s with
| atoi n => string_to_nat n
end.

Compute streval_fun1 (atoi "12") e_string.
Compute streval_fun2 (itoa 652) e_string.
Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
(*Inductive Stmt :=
| assignment_string : string -> string -> Stmt
| assignment_stiva : string -> listNat -> Stmt
| assignment : string -> aexp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : bexp -> Stmt -> Stmt
| iff : bexp -> Stmt -> Stmt -> Stmt
| iffsimpl : bexp -> Stmt -> Stmt.*)

Fixpoint eval (s : Stmt) ( c : Configuration) (gas : nat) : Configuration :=
  match gas with
  | 0 => c
  | S gas' => match c with
              | conf env3 env2 env =>
                       match s with
                      | assignment_string s1 s2 => conf env3 (update_string c s1 s2) env
                      | assignment_stiva s1 s2 => conf env3 env2 (update_stiva c s1 s2)
                      | assignment s1 s2 => conf (update_var c s1 (aeval_fun s2 c)) env2 env
                      | sequence S1 S2 => eval S2 (eval S1 c gas') gas'
                      | while cond s' => if (beval_fun cond c)
                                         then eval (s' ;; (while cond s')) c gas'
                                         else c
                      | iff cond s1 s2 => if (beval_fun cond c)
                                          then eval s1 c gas'
                                          else eval s2 c gas'
                      | iffsimpl cond s1 => if (beval_fun cond c)
                                            then eval s1 c gas'
                                            else c
                      end
        end
end.


(*Inductive e_eval : Stmt -> Env -> Env -> Prop :=
| e_assignment: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_if_then_elsetrue : forall b s s2 sigma sigma',
    b ={ sigma }=> true ->
    s -{ sigma }-> sigma' ->
    iff b s s2 -{ sigma }-> sigma'
| e_if_then_elsefalse : forall b s s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    iff b s s2 -{ sigma }-> sigma'
| e_ifsimpl_true : forall b s sigma sigma',
    b ={ sigma }=> true ->
    s -{ sigma }-> sigma' ->
    iffsimpl b s -{ sigma }-> sigma'
| e_ifsimpl_false : forall b s sigma,
    b ={ sigma }=> false ->
    iffsimpl b s -{ sigma }-> sigma
where "s -{ sigma }-> sigma'" := (e_eval s sigma sigma').
