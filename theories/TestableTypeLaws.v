From Coq Require Import
     List.
From Test Require Import
     Testable
     TestableType
     TestableLaws.
Import
  ListNotations.
Open Scope bool_scope.

Class TestableTypeLaws (T : Type) `{TestableType T} :=
  { TestableLaws_eq {x y : T} : @TestableLaws (x = y) Testable_eq }.

Global Instance TestableLaws_In {T} `{TestableTypeLaws T, a : T, l : list T} :
  TestableLaws (In a l).
Proof with auto.
  destruct H0.
  induction l.
  - split...
    + exists 0. exists false...
    + intros. discriminate H0.
  - destruct (TestableLaws_eq0 a a0).
    destruct IHl.
    split; intros.
    + destruct test_live  as [fuel  [result ]].
      destruct test_live0 as [fuel0 [result0]].
      exists (max fuel fuel0); exists (result || result0); simpl in *.
      rewrite (test_monotone  fuel  result )...
      rewrite (test_monotone0 fuel0 result0)...
      destruct result; destruct result0...
    + simpl in *.
      destruct (test (a = a0) fuel) as [[]|] eqn:Htest.
      * rewrite (test_monotone fuel true )...
      * rewrite (test_monotone fuel false)...
        destruct (test_In a l fuel) as [[]|] eqn:Htest0; inversion H0;
        rewrite (test_monotone0 fuel result); subst...
      * destruct (test_In a l fuel) as [[]|] eqn:Htest0; inversion H0; subst.
        rewrite (test_monotone0 fuel true)...
        destruct (test (a = a0) fuel') as [[]|]...
    + simpl in *.
      destruct (test (a = a0) fuel) as [[]|] eqn:Htest ;
      destruct (test_In a l   fuel) as [[]|] eqn:Htest0;
      inversion H0;
      try apply test_sound_true  in Htest;
      try apply test_sound_true0 in Htest0...
    + simpl in *.
      destruct (test (a = a0) fuel) as [[]|] eqn:Htest ;
      destruct (test_In a l   fuel) as [[]|] eqn:Htest0;
      inversion H0.
      apply test_sound_false  in Htest .
      apply test_sound_false0 in Htest0.
      intro. destruct H1...
Defined.
