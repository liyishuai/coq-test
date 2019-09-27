From Coq Require Import
     List.
From Test Require Import
     Testable.
Import
  ListNotations.

Class TestableType (T : Type) :=
  { Testable_eq {x y : T} : Testable (x = y) }.

Fixpoint test_In {T} `{TestableType T} (a : T) (l : list T) (fuel : nat) :
  option bool :=
  match l with
  | [] => Some false
  | a' :: l' =>
    match @test (a = a') Testable_eq fuel, test_In a l' fuel with
    | Some false, Some false => Some false
    | Some true , _          => Some true
    | _         , Some true  => Some true
    | _         , _          => None
    end
  end.

Global Instance Testable_In {T} `{TestableType T, a : T, l : list T} :
  Testable (In a l) := { test := test_In a l }.
