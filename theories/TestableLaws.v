From Coq Require Import
     Bool
     DecidableClass
     List.

From Test Require Import
     Testable.

Class TestableLaws (P : Prop) `{Testable P} :=
  { test_live        : exists fuel result, test P fuel  = Some result
  ; test_monotone    : forall fuel result, test P fuel  = Some result ->
              forall fuel', fuel <= fuel' -> test P fuel' = Some result
  ; test_sound_true  : forall fuel,        test P fuel  = Some true   ->   P
  ; test_sound_false : forall fuel,        test P fuel  = Some false  -> ~ P
  }.

Hint Resolve test_live.
Hint Resolve test_monotone.
Hint Resolve test_sound_false.

Global Instance Decidable__TestableLaws {P} `{Decidable P} : TestableLaws P.
Proof with eauto.
  split; intros; simpl in *...
  - exists 0. eexists...
  - inversion H0. apply Decidable_spec...
  - intro HP. apply Decidable_spec in HP. rewrite HP in H0. discriminate H0.
Defined.

Global Instance TestableLaws_neg {P} `{TestableLaws P} : TestableLaws (~ P).
Proof with eauto.
  split.
  { inversion H0 as [[fuel []]]. exists fuel. eexists. simpl. rewrite H1... }
  all: intros; simpl in *; destruct (test P fuel) eqn:Htest; inversion H1...
  - rewrite (test_monotone _ _ Htest)...
  - apply negb_true_iff  in H3; subst...
  - apply negb_false_iff in H3; subst.
    assert P... eapply test_sound_true...
Defined.

Hint Resolve Max.le_max_l.
Hint Resolve Max.le_max_r.

Global Instance TestableLaws_conj {P Q} `{TestableLaws P, TestableLaws Q} :
  TestableLaws (P /\ Q).
Proof with eauto.
  split; intros; simpl in *.
  { inversion H0 as [[fuel0 [[]]]]; inversion H2 as [[fuel1 []]];
    exists (max fuel0 fuel1); eexists;
    erewrite test_monotone0; eauto; simpl...
    erewrite test_monotone1... destruct x... }
  { destruct (test P fuel) as [[]|] eqn:HtestP...
    1,2: erewrite test_monotone; eauto; simpl...
    all: destruct (test Q fuel) as [[]|] eqn:HtestQ; inversion H3; subst...
    1,2: erewrite test_monotone; eauto; simpl...
    destruct (test P fuel') as [[]|]; eauto;
    erewrite test_monotone; eauto; simpl... }
  all: destruct (test P fuel) as [[]|] eqn:HtestP; inversion H3; eauto;
       destruct (test Q fuel) as [[]|] eqn:HtestQ; inversion H3...
  { apply test_sound_true in HtestP.
    apply test_sound_true in HtestQ... }
  all: intro; destruct H4;
  try apply test_sound_false in HtestP;
  try apply test_sound_false in HtestQ...
Defined.

Global Instance TestableLaws_disj {P Q} `{TestableLaws P, TestableLaws Q} :
  TestableLaws (P \/ Q).
Proof with eauto.
  split; intros; simpl in *.
  { inversion H0 as [[fuel0 [[]]]]; inversion H2 as [[fuel1 []]];
    exists (max fuel0 fuel1); eexists; erewrite test_monotone0; eauto; simpl...
    erewrite test_monotone1... destruct x... }
  { destruct (test P fuel) as [[]|] eqn:HtestP...
    1,2: erewrite test_monotone; eauto; simpl...
    all: destruct (test Q fuel) as [[]|] eqn:HtestQ; inversion H3; subst; eauto;
    erewrite (@test_monotone Q _ _ fuel'); eauto; simpl...
    destruct (test P fuel') as [[]|]... }
  all: destruct (test P fuel) as [[]|] eqn:HtestP; inversion H3; eauto;
       destruct (test Q fuel) as [[]|] eqn:HtestQ; inversion H3;
       try apply test_sound_true in HtestP;
       try apply test_sound_true in HtestQ...
  apply test_sound_false in HtestP.
  apply test_sound_false in HtestQ.
  intro. destruct H4...
Defined.

Global Instance TestableLaws_impl {P Q} `{TestableLaws P, TestableLaws Q} :
  TestableLaws (P -> Q).
Proof with eauto.
  split; intros; simpl in *.
  { inversion H0 as [[fuel0 [[]]]]; inversion H2 as [[fuel1 [[]]]];
    exists (max fuel0 fuel1); eexists; erewrite test_monotone0; simpl; eauto;
    erewrite test_monotone1; eauto; simpl... }
  { destruct (test P fuel) as [[]|] eqn:HtestP...
    1,2: erewrite test_monotone; eauto; simpl...
    all: destruct (test Q fuel) as [[]|] eqn:HtestQ; inversion H3; subst...
    1,2: erewrite test_monotone; eauto; simpl...
    destruct (test P fuel') as [[]|]; eauto;
    erewrite test_monotone; eauto; simpl... }
  all: destruct (test P fuel) as [[]|] eqn:HtestP; inversion H3; eauto;
       destruct (test Q fuel) as [[]|] eqn:HtestQ; inversion H3;
       try apply test_sound_true  in HtestQ; eauto;
       try apply test_sound_false in HtestP...
  1,2: exfalso...
  apply test_sound_true  in HtestP.
  apply test_sound_false in HtestQ.
  intro...
Defined.
