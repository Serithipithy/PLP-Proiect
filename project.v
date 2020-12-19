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
  | _ =>  0
  end%char.



(* scoti pe rand ultimul element si dupa il tergi  *)
  Definition first_ch (l:list ascii) : ascii :=
    match l with
      | nil => " "
      | a :: nill => a
    end.
  Definition remove_first_ch (l:list ascii) : list ascii :=
    match l with
      | nil => []
      | a :: m => m
    end.
Fixpoint list_ascii_of_string (s : string) : list ascii
  := match s with
     | EmptyString => []
     | String ch s => cons ch (list_ascii_of_string s)
     end.

Compute first_ch(list_ascii_of_string("bunica")).
Compute remove_first_ch(list_ascii_of_string("bunica")).

  Fixpoint removelast (l:list ascii) {struct l} : list ascii :=
    match l with
      | nil => nil
      | a :: nil => nil
      | a :: l => a :: removelast l
    end.



