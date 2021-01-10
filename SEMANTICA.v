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
Definition Strings := string -> string. (* Pt strings *)
Inductive listNat : Type :=
| nil
| cons ( n : nat ) ( l : listNat) .

Definition Stiva := string -> listNat. (* Pt stive *)
Inductive Configuration := 
| conf: Variabila -> Strings -> Stiva -> Configuration.

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

Inductive strexp1 :=
| atoi : string -> strexp1.

Inductive strexp2 :=
| itoa : nat -> strexp2.

Inductive stexp :=
| sstack : listNat -> stexp
| stack : string -> stexp
| push : stexp -> nat -> stexp
| push_var : stexp -> string -> stexp
| pop : stexp -> stexp
| stempty : stexp -> stexp.
Inductive stexp2 :=
| top_string : string -> stexp2
| top_list : listNat -> stexp2.

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

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Infix "::" := cons (at level 60, right associativity) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Notation "'push'( stack , x )" := ( push stack x ) (at level 60).
Notation "'top_var'( stack )" := ( top_string stack ) (at level 60).
Notation "'top_l'( stack )" := ( top_list stack ) (at level 60).
Notation "'pop'( stack )" := ( pop stack ) (at level 60).
Notation "'empty_stack'( stack )" := ( stempty stack ) (at level 60).

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

Compute (atoi "13").
Compute (itoa 12).

Compute [ 10 ; 15 ; 16 ; 5].
Compute push (sstack ([10 ; 15 ; 16 ; 5]))  (10).
Compute push_var (sstack ([10 ; 15 ; 16 ; 5]))  "x".
Compute top_list ([10 ; 15 ; 16 ; 5]).
Compute top_string ("a").
Compute pop (sstack ([10 ; 15 ; 16 ; 5])).
Compute stempty (sstack ([10 ; 15 ; 16 ; 5])).

(* stmt *)
Inductive Stmt :=
| assignment_string : string -> string -> Stmt
| assignment_stiva : string -> listNat -> Stmt
| assignment : string -> aexp -> Stmt
| string_atoi: string -> string -> Stmt
| string_itoa: string -> nat -> Stmt
| stack_top: string -> string -> Stmt
| stack_pop: string -> stexp -> Stmt
| stack_push: string -> stexp -> nat -> Stmt
| stack_push_var: string -> stexp -> string -> Stmt
| stack_sempty: string -> stexp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : bexp -> Stmt -> Stmt
| iff : bexp -> Stmt -> Stmt -> Stmt
| iffsimpl : bexp -> Stmt -> Stmt.

Notation "'stackk' var :=: variabile" :=(assignment_stiva var variabile) (at level 40).
Notation "'str' var <<->> ass" :=(assignment_string var ass) (at level 40).
Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'ifs' cond 'den' { stmt }" := (iffsimpl cond stmt) (at level 93).
Notation "'ifd' cond 'denn' { stmt1 } 'els' { stmt2 }" := (iff cond stmt1 stmt2) (at level 93).
Notation "'While' ( B ) { S }" := (while B S) (at level 97).
Notation "'phor' ( s1 ~ cond ~ s2 ) { stmt }" := (s1 ;; While ( cond ) { stmt ;; s2 }  ) (at level 97).
Notation "'do' { stmt } 'whilee' ( cond )" := ( stmt ;; while ( cond ) ( stmt ) ) (at level 97).

Example ex1 :=
stackk "a" :=: [ 1 ; 2 ; 3] ;;
"c" ::= 10 ;;
str "b" <<->> "ana" ;;
string_atoi "c" "123" ;;
string_itoa "d" 123 ;;
stack_top "c" "a" ;;
stack_pop "a" (stack "a") ;;
stack_push "a" (stack "a") 12 ;;
stack_push_var "a" (stack "a") "c" ;;
stack_sempty "a" (stack "a") ;;
(ifs (2 <=' "c") 
  den  
    { "s" ::= 11 ;; 
      "s" ::= "s" +' 1 
    }) ;;
(ifd (2 <=' "c") 
  denn 
    { "s" ::= 11 ;; 
      "s" ::= "s" +' 1 
    } els 
        { stack_pop "a" (stack "a") ;; 
          "s" ::= 45 
        }) ;;
(While ( "c" <=' 11 ) 
    { "c" ::= "c" +' 1 }) ;;
(phor ( ("i" ::= 1) ~ ("i" <=' 3) ~ ("i" ::= "i" +' 1) ) 
      { "c" ::= "c" *' 2 }) ;;
do {
     ("c" ::= "c" *' 2) 
    } whilee ( "c" <=' 30 )
.

Example ex2 :=
stackk "s" :=: [ 1 ; 2 ; 3 ; 4 ; 5] ;;
"a" ::= 6 ;;
stack_top "c" "a" .
Compute ex1.
Compute ex2.

(* SEMANTICA *)

(* Variabile *)
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

(* Stiva *)
Definition e_stiva : Stiva :=  (* Pt stive *)
  fun x =>
    if (string_eq_dec x "fix2")
    then [ ]
    else [ ].
Check e_stiva.
Notation "S [[[ V /' X ]]]" := (update_string S X V) (at level 0).

Definition update_stiva (c : Configuration) (x : string) (v : listNat ) : Stiva :=
match c with
| conf svar sstring sstiva =>   fun y =>
                                    if (string_eq_dec y x)
                                    then v
                                    else (sstiva y)
end.

Notation "S [[ V /' X ]]" := (update_stiva S X V) (at level 0).

Definition config1 : Configuration :=  conf e_var e_string e_stiva. 

(* Variabile *)


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

Compute aeval_fun (10 +' 11) config1.
Compute aeval_fun (15 +' "a") config1.
Compute aeval_fun ("b" +' 3) config1.
Compute aeval_fun  ("a" +' "b") config1.

Compute aeval_fun (11 -' 10) config1.
Compute aeval_fun (15 -' "a") config1.
Compute aeval_fun ("b" -' 3) config1.
Compute aeval_fun (("a") -' ("b")) config1.

Compute aeval_fun (10 *' 11) config1.
Compute aeval_fun (15 *' "a") config1.
Compute aeval_fun ("b" *' 3) config1.
Compute aeval_fun (("a") *' ("b")) config1.

Compute aeval_fun (10 //' 3) config1.
Compute aeval_fun (15 //' "a") config1.
Compute aeval_fun ("b" //' 3) config1.
Compute aeval_fun (("a") //' ("b")) config1.

Compute aeval_fun (10 %' 4) config1.
Compute aeval_fun (15 %' "a") config1.
Compute aeval_fun ("b" %' 3) config1.
Compute aeval_fun (("a") %' ("b")) config1.

Compute aeval_fun ((((300 +' 23 -'76 +' (2 *' 10))) //' 2) %' 4) config1.

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

(* Strings *)
(*itoa*)
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

Definition streval_fun2 ( s : strexp2 ) (c : Configuration) : string :=
match c with
| conf svar sstring sstiva => 
                              match s with
                              | itoa n => nat_to_string n
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

Definition streval_fun1 ( s : strexp1 ) (c : Configuration) : nat :=
match c with
| conf svar sstring sstiva => 
                              match s with
                              | atoi n => string_to_nat n
                              end
end.

Compute streval_fun1 (atoi "12") config1.
Compute streval_fun2 (itoa 652) config1.

(* Stiva *)

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


Fixpoint seval_fun ( s : stexp ) (c : Configuration) : listNat :=
match c with
| conf svar sstring sstiva => 
                            match s with
                            | sstack x => x
                            | stack y => sstiva y
                            | push a b => push_stack (seval_fun a c) b
                            | push_var a b => push_stack (seval_fun a c) (svar b)
                            | pop a => pop_stack (seval_fun a c)
                            | stempty a => sempty_stack (seval_fun a c)
                            end
end.

Definition seval_fun2 ( s : stexp2 ) (c : Configuration) : nat :=
match c with
| conf svar sstring sstiva => 
                            match s with
                            | top_string x => top_stack (sstiva x) 1 
                            | top_list x => top_stack x 1
                            end
end.
Check seval_fun2.

Compute seval_fun (push (sstack ([10 ; 15 ; 16 ; 5]))  (10)) config1.
Compute seval_fun2 (top_list ([10 ; 15 ; 16 ; 5])) config1.
Compute seval_fun2 (top_string ("a")) config1.
Compute seval_fun (pop (sstack ([10 ; 15 ; 16 ; 5]))) config1.
Compute seval_fun (stempty (sstack ([10 ; 15 ; 16 ; 5]))) config1.

(* Stmt *)

(*Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).*)

Fixpoint eval (s : Stmt) ( c : Configuration) (gas : nat) : Configuration :=
  match gas with
  | 0 => c
  | S gas' => match c with
              | conf env3 env2 env =>
                       match s with
                      | assignment_string s1 s2 => conf env3 (update_string c s1 s2) env
                      | assignment_stiva s1 s2 => conf env3 env2 (update_stiva c s1 s2)
                      | assignment s1 s2 => conf (update_var c s1 (aeval_fun s2 c)) env2 env
                      | string_atoi vari stri => conf (update_var c vari (streval_fun1 (atoi stri) c)) env2 env
                      | string_itoa stri vari => conf env3 (update_string c stri (streval_fun2 (itoa vari)c)) env
                      | stack_top slist stri => conf (update_var c stri (seval_fun2 (top_string slist)c)) env2 env
                      | stack_pop s1 s2 => conf env3 env2 (update_stiva c s1 (seval_fun (pop s2)c))
                      | stack_push s1 s2 nat => conf env3 env2 (update_stiva c s1 (seval_fun (push s2 nat)c))
                      | stack_push_var s1 s2 var => conf env3 env2 (update_stiva c s1 (seval_fun (push_var s2 var)c))
                      | stack_sempty s1 s2 => conf env3 env2 (update_stiva c s1 (seval_fun (stempty s2)c))
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
Definition get_nat (c : Configuration) ( s: string ) : nat :=
match c with 
| conf env3 env2 env => (env3 s) 
end.

Definition get_string (c : Configuration) ( s: string ) : string :=
match c with 
| conf env3 env2 env => (env2 s) 
end.

Definition get_stack (c : Configuration) ( s: string ) : listNat :=
match c with 
| conf env3 env2 env => (env s) 
end.


Definition config2 : Configuration := eval ("x" ::= 123 +' 34 //' 10 ;; str "b" <<->> "ana" ;; stackk "a" :=: [ 1 ; 2 ; 3] ) config1 300.

Compute get_string config2 "b".
Compute get_nat config2 "x".
Compute get_stack config2 "a".

Definition config3 : Configuration := eval ex1 config1 300.
Compute get_string config3 "b".
Compute get_nat config3 "c".
Compute get_nat config3 "s".
Compute get_nat config3 "i".
Compute get_stack config3 "a".

Example p_ex2 :=
stackk "s" :=: [ 1 ; 2 ; 3 ; 4 ; 5] ;;
"a" ::= 6 ;;
stack_top "s" "a" .

Definition config4 : Configuration := eval p_ex2 config1 300.
Compute get_nat config4 "a".
Compute get_stack config4 "s".

Example p_ex3 :=
stackk "s" :=: [ 1 ; 2 ; 3 ; 4 ; 5] ;;
"a" ::= 6 ;;
stack_top "s" "a" ;;
stack_pop "s" (stack "s") .

Definition config5 : Configuration := eval p_ex3 config1 300.
Compute get_stack config5 "s".

Example p_ex4 :=
stackk "s" :=: [ 1 ; 2 ; 3 ; 4 ; 5] ;;
"a" ::= 6 ;;
stack_top "s" "a" ;;
stack_pop "s" (stack "s") ;;
stack_push "s" (stack "s") 12 .

Definition config6 : Configuration := eval p_ex4 config1 300.
Compute get_stack config6 "s".

Example p_ex5 :=
string_atoi "c" "123" ;;
string_itoa "d" 35.

Definition config7 : Configuration := eval p_ex5 config1 300.
Compute get_nat config7 "c".
Compute get_string config7 "d".

Example p_ex6 :=
stackk "s" :=: [ 34 ; 2 ; 11 ; 23 ; 129] ;;
"i" ::= 10 ;;
While ( "i" <=' 12 ) 
    { stack_pop "s" (stack "s") ;;
     "i" ::= ("i" +' 1) }
.

Definition config8 : Configuration := eval p_ex6 config1 300.
Compute get_nat config8 "i".
Compute get_stack config8 "s".

Example p_ex7 :=
stackk "s" :=: [ 34 ; 2 ; 11 ; 23 ; 129] ;;
"i" ::= 10 ;; 
do { stack_pop "s" (stack "s") ;;
     "i" ::= ("i" +' 1) }
whilee ( "i" <=' 11 )
.

Definition config9 : Configuration := eval p_ex7 config1 300.
Compute get_nat config9 "i".
Compute get_stack config9 "s".

Example p_ex8 :=
stackk "s" :=: [ 34 ; 2 ; 11 ; 23 ; 129] ;;
stackk "x" :=: [ ] ;;
"nr" ::= 111 ;;
phor ( ("i" ::= 1) ~ ("i" <=' 3) ~ ("i" ::= "i" +' 1) ) 
      { stack_pop "s" (stack "s") ;;
        stack_push_var "x" (stack "x") "nr" ;;
        "nr" ::= "nr" +' 20
       }
.

Definition config10 : Configuration := eval p_ex8 config1 300.
Compute get_nat config10 "i".
Compute get_stack config10 "s".
Compute get_stack config10 "x".
