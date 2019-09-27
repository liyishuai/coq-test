From Coq Require Import
     DecidableClass.
From ExtLib Require Import
     Functor
     OptionMonad.
Import FunctorNotation.

Class Testable (P : Prop) :=
  { test : nat -> option bool }.

Arguments test _ {_} _.

Global Instance Decidable__Testable {P} `{Decidable P} : Testable P :=
  {| test _ := Some Decidable_witness |}.

Global Instance Testable_neg {P} `{Testable P} : Testable (~ P) :=
  { test fuel := negb <$> test P fuel }.

Global Instance Testable_conj {P Q} `{Testable P, Testable Q} :
  Testable (P /\ Q) :=
  { test fuel :=
      match test P fuel, test Q fuel with
      | Some true , Some true  => Some true
      | Some false, _          => Some false
      | _         , Some false => Some false
      | _         , _          => None
      end }.

Global Instance Testable_disj {P Q} `{Testable P, Testable Q} :
  Testable (P \/ Q) :=
  { test fuel :=
      match test P fuel, test Q fuel with
      | Some false, Some false => Some false
      | Some true , _          => Some true
      | _         , Some true  => Some true
      | _         , _          => None
      end }.

Global Instance Testable_impl {P Q} `{Testable P, Testable Q} :
  Testable (P -> Q) | 100 :=
  { test fuel :=
      match test P fuel, test Q fuel with
      | Some true , Some false => Some false
      | Some false, _          => Some true
      | _         , Some true  => Some true
      | _         , _          => None
      end }.
