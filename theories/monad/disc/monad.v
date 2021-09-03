From discprob.prob Require Import double rearrange.
From discprob.prob Require Import prob finite stochastic_order.
From discprob.prob Require Export countable.
From discprob.basic Require Import base sval order monad bigop_ext.
From discprob.basic Require Export classic_proof_irrel.
From discprob.prob Require Export countable dep_prod.
Require Import Reals Psatz.
Require ClassicalEpsilon.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice bigop.
Global Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.

Record mdist X :=
  {
    mdist_idx : countType;
    mdist_distrib : distrib mdist_idx;
    mdist_ind : mdist_idx → X;
  }.

Arguments mdist_idx {_} _.
Arguments mdist_distrib {_} _.
Arguments mdist_ind {_} _.

Definition gen_eqP (X: Type) :
  Equality.axiom (fun x y: X => ClassicalEpsilon.excluded_middle_informative (x = y) ).
Proof. move => x y. apply sumboolP. Qed.

Definition gen_eqMixin (X: Type) := EqMixin (gen_eqP X).
Definition gen_eqType (X : Type) := Eval hnf in EqType _ (gen_eqMixin X).

Definition rvar_of_mdist {X} (md: mdist X) : rvar (mdist_distrib md) (gen_eqType X).
  refine (mkRvar (mdist_distrib md) _).
  { apply mdist_ind. }
Defined.

Definition In_support {X: Type} (x: X) (I : mdist X) :=
  ∃ i, mdist_ind I i = x ∧ (pmf (mdist_distrib I) i > 0).
Definition msupport {X} I := { x : X | In_support x I }.

Definition eq_mdist {X} (I1 I2: mdist X) :=
  (∀ x, pr_eq (rvar_of_mdist I1) x = pr_eq (rvar_of_mdist I2) x).

Lemma eq_mdist_refl {X} (I: mdist X): eq_mdist I I.
Proof. intros ?; eauto. Qed.

Lemma eq_mdist_sym {X} (I1 I2: mdist X): eq_mdist I1 I2 → eq_mdist I2 I1.
Proof. intros Heq x. symmetry. apply Heq. Qed.

Lemma eq_mdist_trans {X} (I1 I2 I3: mdist X): eq_mdist I1 I2 → eq_mdist I2 I3 → eq_mdist I1 I3.
Proof. intros Heq1 Heq2 x. etransitivity; first eapply Heq1. apply Heq2. Qed.

(* TODO: move *)
(* TODO: should we just use { x :unit | false} as empty ? *)
Lemma eqeP : Equality.axiom (λ x y : Empty_set, true).
Proof. intros []. Qed.

Canonical empty_eqMixin := EqMixin eqeP.
Canonical empty_eqType := Eval hnf in EqType Empty_set empty_eqMixin.

Fact empty_choiceMixin: choiceMixin Empty_set.
Proof.
  exists (λ P n, None).
  - intros ?? [].
  - intros ? [[]].
  - intros ?? ? x. done.
Qed.
Canonical empty_choiceType := Eval hnf in ChoiceType Empty_set empty_choiceMixin.

Definition empty_pickle (x: Empty_set) := Empty_set_rect (λ x, nat) x.
Definition empty_unpickle (n: nat) : option Empty_set := None.
Lemma empty_pickleK : pcancel empty_pickle empty_unpickle.
Proof. intros []. Qed.

Definition empty_countMixin := CountMixin (empty_pickleK).
Canonical empty_countType := Eval hnf in CountType Empty_set empty_countMixin.

Lemma empty_enumP : @Finite.axiom [eqType of Empty_set] [::].
Proof. intros []. Qed.
Definition empty_finMixin := Eval hnf in FinMixin empty_enumP.
Canonical empty_finType := Eval hnf in FinType Empty_set empty_finMixin.


Global Instance eq_mdist_Transitivite {Y}: Transitive (@eq_mdist Y).
Proof. intros ???. apply eq_mdist_trans. Qed.
Global Instance eq_mdist_Reflexive {Y}: Reflexive (@eq_mdist Y).
Proof. intros ?. apply eq_mdist_refl. Qed.
Global Instance eq_mdist_Symmetry {Y}: Symmetric (@eq_mdist Y).
Proof. intros ??. apply eq_mdist_sym. Qed.
Global Instance eq_mdist_Equivalence {Y}: Equivalence (@eq_mdist Y).
Proof. split; apply _. Qed.

Ltac abs_simpl :=
  match goal with
  | [ H: context [ Rabs ?p ] |- _ ]  =>
    rewrite (Rabs_right p) in H; last by nra
  | [ |- context [ Rabs ?p ] ] =>
    rewrite (Rabs_right p); last by nra
  end.

Definition dirac_unit : distrib [finType of unit].
  refine {| pmf := λ _, 1 |}.
  { abstract (intros; nra). }
  { abstract (apply SeriesF_is_seriesC'; rewrite big_const card_unit //=; nra). }
Defined.

Global Instance mdist_ret: MRet mdist.
refine(λ A x, {| mdist_idx := [finType of unit]; mdist_distrib := dirac_unit; mdist_ind := (λ _, x)|}).
Defined.

Definition mdist_bind_idx  {A B} (f: A → mdist B) (I : mdist A) :=
  [countType of { i: mdist_idx I & mdist_idx (f (mdist_ind I i)) }].

Definition mdist_bind_pmf {A B} (f : A → mdist B) (I: mdist A) : mdist_bind_idx f I → R :=
  (λ ip, pmf (mdist_distrib I) (projT1 ip)
                           * pmf (mdist_distrib (f (mdist_ind I (projT1 ip)))) (projT2 ip)).

Lemma mdist_bind_pmf_nonneg {A B} (f: A → mdist B) (I : mdist A) :
  ∀ a : mdist_bind_idx f I, mdist_bind_pmf f I a >= 0.
Proof.
  intros a. rewrite /mdist_bind_pmf. apply Rle_ge.
  apply Rmult_le_pos; apply Rge_le, pmf_pos.
Qed.

Lemma mdist_bind_series_1 {A B} (f: A → mdist B) (I : mdist A) :
  is_series (countable_sum (mdist_bind_pmf f I)) 1.
Proof.
  rewrite /mdist_bind_pmf.
  eapply is_series_ext; last first.
  { unshelve (eapply (dep_prod.prod_pmf_pos_sum1 (mdist_idx I))).
    { intros i. apply (mdist_idx (f (mdist_ind I i))). }
    { apply (mdist_distrib I). }
    { intros i. apply (mdist_distrib (f (mdist_ind I i))). }
  }
  rewrite /dep_prod_pmf. eauto.
Qed.

Definition mdist_bind_distrib {A B} (f: A → mdist B) (I : mdist A) : distrib (mdist_bind_idx f I).
  refine ({| pmf := mdist_bind_pmf f I |}).
  - apply mdist_bind_pmf_nonneg.
  - apply mdist_bind_series_1.
Defined.

Global Instance mdist_bind: MBind mdist :=
  λ A B f I,
  {| mdist_idx := mdist_bind_idx f I;
     mdist_ind := (λ ip, mdist_ind (f (mdist_ind I (projT1 ip))) (projT2 ip));
     mdist_distrib := mdist_bind_distrib f I;
  |}.

Global Instance mdist_join: MJoin mdist :=
  λ A I, mbind (λ x, x) I.

Lemma mdist_left_id {A B: Type} (x: A) (f: A → mdist B):
  eq_mdist (mbind f (mret x)) (f x).
Proof. Admitted.

Lemma mdist_right_id {A: Type} (m: mdist A):
  eq_mdist (mbind mret m) m.
Proof. Admitted.

Lemma mdist_assoc {A B C} (m: mdist A) (f: A → mdist B) (g: B → mdist C) :
  eq_mdist (mbind g (mbind f m)) (mbind (λ x, mbind g (f x)) m).
Proof. Admitted.

Lemma mdist_bind_congr {A B} (m1 m2: mdist A) (f1 f2: A → mdist B) :
  eq_mdist m1 m2 →
  (∀ a, eq_mdist (f1 a) (f2 a)) →
  eq_mdist (mbind f1 m1) (mbind f2 m2).
Proof. Admitted.

Global Instance ibind_proper {X Y}:
  Proper ((pointwise_relation _ (@eq_mdist Y)) ==> @eq_mdist X ==> @eq_mdist Y) (@mbind mdist _ X Y).
Proof. intros ?? ? ?? ?. apply mdist_bind_congr; eauto. Qed.

Lemma mdist_bind_comm_aux {A1 A2} (I1: mdist A1) (I2: mdist A2) :
  eq_mdist (x ← I1; y ← I2; mret (x, y)) (y ← I2; x ← I1; mret (x, y)).
Proof. Admitted.

Lemma mdist_bind_comm {A1 A2 A3} (I1: mdist A1) (I2: mdist A2) (f: A1 → A2 → mdist A3):
  eq_mdist (x ← I1; y ← I2; f x y) (y ← I2; x ← I1; f x y).
Proof.
  transitivity (xy ← (x ← I1; y ← I2; mret (x, y)); f (fst xy) (snd xy)).
  - setoid_rewrite mdist_assoc.
    eapply mdist_bind_congr; first by reflexivity.
    intros x.
    setoid_rewrite mdist_assoc.
    eapply mdist_bind_congr; first by reflexivity.
    intros y.
    setoid_rewrite mdist_left_id; reflexivity.
  - setoid_rewrite mdist_bind_comm_aux.
    setoid_rewrite mdist_assoc.
    eapply mdist_bind_congr; first by reflexivity.
    intros x.
    setoid_rewrite mdist_assoc.
    eapply mdist_bind_congr; first by reflexivity.
    intros y.
    setoid_rewrite mdist_left_id; reflexivity.
Qed.

