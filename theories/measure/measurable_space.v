Require Import Reals Psatz Omega ClassicalEpsilon.
From stdpp Require Import tactics.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.measure Require Export sets sigma_algebra.

Class measurable_space (A: Type) := { measurable_space_sigma : sigma_algebra A }.
Coercion measurable_space_sigma : measurable_space >-> sigma_algebra.

Section measurable_space.

Context `{F: measurable_space A}.

Definition is_measurable (s: A → Prop) :=
  sigma_sets _ F s.

Lemma is_measurable_empty : is_measurable ∅.
Proof. apply sigma_empty_set. Qed.

Lemma is_measurable_pair_union X Y:
  is_measurable X → is_measurable Y → is_measurable (X ∪ Y).
Proof. apply sigma_closed_pair_union. Qed.

Lemma is_measurable_pair_intersect X Y:
  is_measurable X → is_measurable Y → is_measurable (X ∩ Y).
Proof. apply sigma_closed_pair_intersect. Qed.

Lemma is_measurable_minus X Y:
  is_measurable X → is_measurable Y → is_measurable (X ∖ Y).
Proof. apply sigma_closed_set_minus. Qed.

Lemma is_measurable_compl X:
  is_measurable X → is_measurable (compl X).
Proof. apply sigma_closed_complements. Qed.

Lemma is_measurable_full:
  is_measurable (λ _, True).
Proof. apply sigma_full. Qed.

Lemma is_measurable_union (Ps : nat → (A → Prop)):
  (∀ i, is_measurable (Ps i)) →
  is_measurable (unionF Ps).
Proof. apply sigma_closed_unions. Qed.

Lemma is_measurable_intersect (Ps : nat → (A → Prop)):
  (∀ i, is_measurable (Ps i)) →
  is_measurable (intersectF Ps).
Proof. apply sigma_closed_intersections. Qed.

End measurable_space.

Definition measurable `{F1: measurable_space A} `{F2: measurable_space B} (f: A → B) : Prop :=
  sigma_measurable f F1 F2.

Section measurable_functions.

  Context {A: Type} {FA: measurable_space A}.
  Context {B: Type} {FB: measurable_space B}.
  Context {C: Type} {FC: measurable_space C}.

Lemma measurable_ext (f1 f2: A → B) :
  (∀ x, f1 x = f2 x) →
  measurable f1 →
  measurable f2.
Proof. apply sigma_measurable_ext. Qed.

Lemma measurable_comp (f: A → B) (g: B → C) :
  measurable f →
  measurable g →
  measurable (λ x, g (f x)).
Proof. apply sigma_measurable_comp. Qed.

Lemma measurable_id:
  measurable (@id A).
Proof. apply sigma_measurable_id. Qed.

Lemma measurable_const (b: B):
  measurable (λ a : A, b).
Proof. apply sigma_measurable_const. Qed.

Lemma measurable_eta (f: A → B) :
  measurable f →
  measurable (λ x, f x).
Proof. apply sigma_measurable_ext; eauto. Qed.

End measurable_functions.

Global Instance measurable_proper {A B: Type} {F1 F2} :
  Proper (pointwise_relation _ eq ==> iff) (@measurable A F1 B F2).
Proof. intros ?? Heq. rewrite /measurable. by rewrite Heq. Qed.

(*
(* Any function f : A  → B on a sigma_measurable space A induces a sigma algebra on B *)
Definition fun_sigma {A B: Type} (F: sigma_algebra A) (f: A → B) : sigma_algebra B.
  refine {| sigma_sets := λ U, F (fun_inv f U) |}.
  - abstract (by intros ?? ->).
  - abstract (rewrite //=).
  - abstract (intros P HF; rewrite fun_inv_compl; auto).
  - abstract (intros Ps HF; rewrite fun_inv_unionF; auto).
Defined.

Lemma sigma_measurable_intersection {I} {A B: Type} f (F1: sigma_algebra A) (F2 : I → sigma_algebra B):
  (∃ i, sigma_measurable f F1 (F2 i)) →
  sigma_measurable f F1 (intersection_sigma _ F2).
Proof.
  intros HF2 U HminU.
  cut (le_prop (intersection_sigma _ F2) (fun_sigma F1 f)).
  { intros Hle. by apply Hle. }
  intros V. rewrite /fun_sigma//=. intros Hin.
  edestruct HF2 as (i&Hmeas). eapply Hmeas; eauto.
Qed.

Lemma sigma_measurable_generating_sets {A B: Type} f (F1: sigma_algebra A) (F2 : (B → Prop) → Prop):
  (∀ U, F2 U → F1 (fun_inv f U)) →
  sigma_measurable f F1 (minimal_sigma F2).
Proof.
  intros HF2 U HminU.
  cut (le_prop (minimal_sigma F2) (fun_sigma F1 f)).
  { intros Hle. by apply Hle. }
  apply minimal_sigma_lub. rewrite /fun_sigma//=.
Qed.
*)

Global Instance measurable_space_sum (A1 A2: Type) {F1: measurable_space A1} {F2: measurable_space A2}
  : measurable_space (A1 + A2).
Proof. econstructor; apply disjoint_sum_sigma; [ apply F1 | apply F2 ]. Defined.

Global Instance measurable_space_unit : measurable_space unit.
Proof. econstructor; apply discrete_algebra. Defined.

Global Instance measurable_space_nat : measurable_space nat.
Proof. econstructor; apply discrete_algebra. Defined.

(*
Lemma inv_union {A B: Type} (f: A → B) (Us: nat → B → Prop):
    eq_prop (fun_inv f (unionF Us))
            (unionF (λ i : nat, fun_inv f (Us i))).
Proof. intros z. split; firstorder. Qed.

Definition discrete_algebra (A: Type) : sigma_algebra A.
Proof.
  refine {| sigma_sets := λ _, True |}; abstract (auto).
Defined.

Definition initial_algebra {I: Type} {A: Type} {B: Type} (Y : sigma_algebra B) (f: I → A → B)
  : sigma_algebra A.
Proof.
  set (S := { σ : sigma_algebra A | ∀ i, sigma_measurable (f i) σ Y }).
  exact (intersection_sigma S sval).
Defined.

Lemma initial_algebra_meas {I} {A B: Type} (Y: sigma_algebra B) (f: I → A → B) (i: I):
  sigma_measurable (f i) (initial_algebra Y f) Y.
Proof.
  intros U HYU (σ&Hspec) => //=.
  eapply Hspec. eauto.
Qed.

Lemma initial_algebra_lb {I} {A B: Type} (Y: sigma_algebra B) (f: I → A → B) (X: sigma_algebra A):
  (∀ i, sigma_measurable (f i) X Y) →
  le_sigma (initial_algebra Y f) X.
Proof.
  intros Hmeas. intros U HU.
  apply (HU (exist _ X Hmeas)).
Qed.

Lemma initial_algebra_codom_meas {I} {C A B: Type} (X: sigma_algebra C)
      (Y: sigma_algebra B) (f: I → A → B) g:
  (∀ i, sigma_measurable (λ x, (f i (g x))) X Y) →
  sigma_measurable g X (initial_algebra Y f).
Proof.
  intros Hspec.
  apply sigma_measurable_intersection.
  unshelve (eexists).
  { exists (fun_sigma X g). eauto. }
  rewrite //=.
Qed.

Lemma initial_algebra_in {I} {A B: Type} (Y: sigma_algebra B) (f: I → A → B) U:
  (∃ i U', Y U' ∧ U ≡ fun_inv (f i) U') →
  initial_algebra Y f U.
Proof.
  intros (i&U'&Hin&Heq).
  rewrite Heq. apply initial_algebra_meas. eauto.
Qed.




Definition initial_algebra1 {A: Type} {B: Type} (Y : sigma_algebra B) (f: A → B)
  : sigma_algebra A := @initial_algebra unit A B Y (λ _, f).

Lemma initial_algebra1_meas {A B: Type} (Y: sigma_algebra B) (f: A → B) :
  sigma_measurable f (initial_algebra1 Y f) Y.
Proof.
  eapply sigma_measurable_ext; last first.
  { eapply (initial_algebra_meas _ _ tt).  }
  done.
Qed.


Lemma initial_algebra1_codom_meas {C A B: Type} (X: sigma_algebra C)
      (Y: sigma_algebra B) (f: A → B) g:
  sigma_measurable (λ x, (f (g x))) X Y →
  sigma_measurable g X (initial_algebra1 Y f).
Proof. intros. by eapply initial_algebra_codom_meas. Qed.

Lemma initial_algebra1_lb {A B: Type} (Y: sigma_algebra B) (f: A → B) (X: sigma_algebra A):
  sigma_measurable f X Y →
  le_sigma (initial_algebra1 Y f) X.
Proof. intros. eapply initial_algebra_lb; eauto. Qed.

Lemma initial_algebra1_in {A B: Type} (Y: sigma_algebra B) (f: A → B) U:
  (∃ U', Y U' ∧ U ≡ fun_inv f U') →
  initial_algebra1 Y f U.
Proof.
  intros (U'&Hin&Heq).
  rewrite Heq. apply initial_algebra1_meas. eauto.
Qed.

Lemma initial_algebra1_eq_min {A B: Type} (Y: sigma_algebra B) (f: A → B):
  eq_sigma (initial_algebra1 Y f) (minimal_sigma (λ U, ∃ U', U ≡ fun_inv f U' ∧ Y U')).
Proof.
  rewrite /eq_sigma. apply le_prop_antisym.
  - apply initial_algebra_lb. intros _. intros U HYU.
    apply minimal_sigma_ub. eexists; split; eauto.
  - apply minimal_sigma_lub. intros U (U'&Hequiv&HY).
    rewrite Hequiv. by apply initial_algebra1_meas.
Qed.

(*
Lemma initial_algebra1_img {A B: Type} (Y: sigma_algebra B) (f: A → B) U:
  initial_algebra1 Y f U →
  Y (fun_img f U).
Proof.
  intros Hinit.
  apply initial_algebra1_eq_min in Hinit.
  cut ((λ U : A → Prop, ∃ U' : B → Prop, U ≡ fun_inv f U' ∧ Y U') U).
  { intros Halt.  destruct Halt as (U'&Hequiv&?).
    eapply sigma_proper; eauto. intros z.
    rewrite /fun_img. split.
    intros (x&HU&Heq).
    * subst. eapply Hequiv in HU. eauto.
    * intros HU'z.
    setoid_rewrite Hequiv.
    rewrite /fun_ing.
    rewrite Hequiv.
  destruct Hinit.
*)
*)
