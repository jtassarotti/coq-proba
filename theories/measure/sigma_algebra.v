Require Import Reals Psatz Omega ClassicalEpsilon.
From stdpp Require Import tactics.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.measure Require Export sets.

Record sigma_algebra (A: Type) :=
  mkSigma {
      sigma_sets:> (A → Prop) → Prop;
      sigma_proper : Proper (@eq_prop A ==> iff) sigma_sets;
      sigma_full : sigma_sets (λ _, True);
      sigma_closed_complements :
        ∀ P, sigma_sets P → sigma_sets (compl P);
      sigma_closed_unions :
               ∀ Ps : nat → (A → Prop), (∀ i, sigma_sets (Ps i)) →
                                        sigma_sets (unionF Ps)
    }.

Definition eq_sigma {A: Type} (F1 F2: sigma_algebra A) := eq_prop F1 F2.
Definition le_sigma {A: Type} (F1 F2: sigma_algebra A) := le_prop F1 F2.

(*
Global Instance le_sigma_Transitive {X}: Transitive (@le_sigma X).
Proof. rewrite /le_sigma => ??? Heq1 Heq2 x. intros. by apply Heq2, Heq1. Qed.
Global Instance le_sigma_Reflexive {X}: Reflexive (@le_sigma X).
Proof. rewrite /le_sigma //=. intros ??. done. Qed.

Global Instance eq_sigma_Transitive {X}: Transitive (@eq_sigma X).
Proof. rewrite /eq_sigma/eq_prop => ??? Heq1 Heq2 x. by rewrite Heq1 Heq2.  Qed.
Global Instance eq_sigma_Reflexive {X}: Reflexive (@eq_sigma X).
Proof. rewrite /eq_sigma. by apply eq_prop_Reflexive. Qed.
Global Instance eq_sigma_Symmetry {X}: Symmetric (@eq_sigma X).
Proof. rewrite /eq_sigma/eq_prop => ?? Heq x. by rewrite Heq. Qed.
Global Instance eq_sigma_Equivalence {X}: Equivalence (@eq_sigma X).
Proof. split; apply _. Qed.
*)


Global Instance sigma_algebra_proper {A: Type} X : Proper (@eq_prop A ==> iff) (@sigma_sets A X).
Proof. apply sigma_proper. Qed.

Lemma sigma_closed_intersections {A: Type} (X: sigma_algebra A) (Ps: nat → (A → Prop)) :
  (∀ i, X (Ps i)) → X (intersectF Ps).
Proof.
  intros Hmem.
  assert (eq_prop (λ x : A, ∀ i, Ps i x) (λ x, ¬ (∃ i, ¬ (Ps i x)))) as ->.
  { intros x; split.
    - intros Hall (i&Hnot). apply Hnot. auto.
    - intros Hnot i. eapply Classical_Pred_Type.not_ex_not_all in Hnot. eauto.
  }
  apply sigma_closed_complements, sigma_closed_unions.
  intros i. apply sigma_closed_complements. auto.
Qed.

Lemma union_pair_unionF {A: Type} (X Y: A → Prop) :
  eq_prop (X ∪ Y)
          (unionF (λ n : nat, match n with
                              | O => X
                              | S O => Y
                              | _ => ∅ end)).
Proof.
  rewrite /eq_prop/union/unionF; split.
  * intros [?|?]; [exists O | exists (S O)]; auto.
  * intros (n&H).
    destruct n; first by left.
    destruct n; first by right.
    inversion H.
Qed.

Lemma intersect_pair_intersectF {A: Type} (X Y: A → Prop) :
  eq_prop (X ∩ Y)
          (intersectF (λ n : nat, match n with
                              | O => X
                              | S O => Y
                              | _ => (λ _, True) end)).
Proof.
  rewrite /eq_prop/intersect/intersectF; split.
  * intros [? ?] [|[|]]; auto.
  * intros H; split.
    ** apply (H O).
    ** apply (H (S O)).
Qed.

Lemma sigma_empty_set {A: Type} (F: sigma_algebra A) :
  F ∅.
Proof.
  eapply sigma_proper; last apply sigma_closed_complements, sigma_full.
  intros x; split => [] []; auto.
Qed.

Hint Resolve sigma_empty_set sigma_full sigma_closed_complements sigma_closed_unions.

Lemma sigma_closed_pair_union {A: Type} (F: sigma_algebra A) X Y:
  F X → F Y → F (X ∪ Y).
Proof.
  intros. rewrite union_pair_unionF.  apply sigma_closed_unions.
  intros [|[|]]; auto.
Qed.

Lemma range_union_S {A: Type} (Us: nat → A → Prop) n:
  (λ x, ∃ i, (i <= S n)%nat ∧ Us i x) ≡ (λ x, ∃i, (i <= n)%nat ∧ Us i x) ∪ (Us (S n)).
Proof.
  intros x; split.
  - intros (?&Hle&?). inversion Hle; subst; firstorder.
  - firstorder.
Qed.

Lemma sigma_closed_range_union {A: Type} (F: sigma_algebra A) Us n:
  (∀ i, (i <= n)%nat → F (Us i)) → F (λ x, ∃ i, (i <= n)%nat ∧ Us i x).
Proof.
  induction n.
  - intros Hle. apply (sigma_proper _ _ (Us O)); eauto.
    intros x; split.
    * firstorder.
    * intros (i&Hle'&?). inversion Hle'; firstorder.
  - intros.  setoid_rewrite range_union_S. apply sigma_closed_pair_union; eauto.
Qed.

Lemma sigma_closed_list_union {A: Type} (F: sigma_algebra A) l:
  (∀ U, In U l → F U) → F (union_list l).
Proof.
  induction l => //=.
  intros. apply sigma_closed_pair_union; eauto.
Qed.

Lemma sigma_closed_pair_intersect {A: Type} (F: sigma_algebra A) X Y:
  F X → F Y → F (X ∩ Y).
Proof.
  intros. rewrite intersect_pair_intersectF. apply sigma_closed_intersections.
  intros [|[|]]; auto.
Qed.

Lemma sigma_closed_set_minus {A: Type} (F: sigma_algebra A) X Y:
  F X → F Y → F (X ∖ Y).
Proof.
  intros HX HY.
  rewrite set_minus_union_complement.
  apply sigma_closed_pair_intersect; auto.
Qed.

Hint Resolve sigma_closed_pair_union sigma_closed_pair_intersect sigma_closed_set_minus.

Definition intersection_sigma {A: Type} (I: Type) (U: I → sigma_algebra A) : sigma_algebra A.
  refine {| sigma_sets := λ x, ∀ i, (U i) x |}.
  - abstract (intros X X' Heq; split => H i; [ rewrite -Heq | rewrite Heq ]; auto).
  - abstract (intros; by apply sigma_full).
  - abstract (intros; by apply sigma_closed_complements).
  - abstract (intros; by apply sigma_closed_unions).
Defined.

Definition minimal_sigma {A: Type} (F: (A → Prop) → Prop) : sigma_algebra A :=
  intersection_sigma { F' : sigma_algebra A | le_prop F F' } sval.

Lemma minimal_sigma_ub {A: Type} (F : (A → Prop) → Prop) :
  le_prop F (minimal_sigma F).
Proof.
  intros i HF (F'&Hle) => //=. by apply Hle.
Qed.

Lemma minimal_sigma_lub {A: Type} (F : (A → Prop) → Prop) (F': sigma_algebra A) :
  le_prop F F' → le_prop (minimal_sigma F) F'.
Proof.
  intros Hle X. rewrite /minimal_sigma/intersection_sigma => //=.
  intros H. specialize (H (exist _ F' Hle)). apply H.
Qed.

Definition sigma_measurable {A B: Type} f (F1: sigma_algebra A) (F2: sigma_algebra B) :=
  ∀ U, F2 U → F1 (fun_inv f U).


Lemma sigma_measurable_proper {A B: Type} f :
  Proper (@eq_sigma A ==> @eq_sigma B ==> iff) (@sigma_measurable A B f).
Proof.
  intros F1 F1' Heq1 F2 F2' Heq2.
  split; intros Hmeasure U.
  - rewrite -Heq1 -Heq2. auto.
  - rewrite Heq1 Heq2. auto.
Qed.

Global Instance sigma_measurable_proper' {A B: Type} :
  Proper (pointwise_relation _ eq ==> eq ==> eq ==> iff) (@sigma_measurable A B).
Proof.
  intros f1 f2 Heq ?? ? ?? ?; subst.
  assert (Heq': eq_fun f1 f2).
  { intros x; eauto. }
  split; intros Hmeasure U.
  - rewrite -Heq'. eauto.
  - rewrite Heq'. eauto.
Qed.

Lemma sigma_measurable_ext {A B: Type} F1 F2 f1 f2 :
  (∀ x, f1 x = f2 x) →
  @sigma_measurable A B f1 F1 F2 →
  @sigma_measurable A B f2 F1 F2.
Proof.
  intros Heq Hmeas. eapply sigma_measurable_proper'; eauto.
  intros x. done.
Qed.

Global Instance sigma_measurable_mono {A B: Type} f :
  Proper (@le_sigma A ==> @le_sigma B --> impl) (@sigma_measurable A B f).
Proof.
  intros F1 F1' Heq1 F2 F2' Heq2.
  intros Hmeas U HU. by apply Heq2, Hmeas, Heq1 in HU.
Qed.

Lemma sigma_measurable_comp {A B C: Type} (f: A → B) (g: B → C) F1 F2 F3 :
  sigma_measurable f F1 F2 →
  sigma_measurable g F2 F3 →
  sigma_measurable (λ x, g (f x)) F1 F3.
Proof. intros Hf Hg ? HU. by apply Hg, Hf in HU. Qed.

Lemma sigma_measurable_id {A: Type}  F:
  sigma_measurable (@id A) F F.
Proof. intros U HF => //=. Qed.

Lemma sigma_measurable_const {A B: Type} (b: B) F G:
  sigma_measurable (λ a : A, b) F G.
Proof.
  intros U HF => //=.
  destruct (Classical_Prop.classic (U b)).
  - eapply sigma_proper; last eapply sigma_full. rewrite /fun_inv.
    split; intuition.
  - eapply sigma_proper; last eapply sigma_empty_set. rewrite /fun_inv.
    split.
    * contradiction.
    * inversion 1.
Qed.

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

Definition disjoint_sum_sigma {A1 A2: Type} (F1: sigma_algebra A1) (F2: sigma_algebra A2)
  : sigma_algebra (A1 + A2).
Proof.
  refine {| sigma_sets := λ U, F1 (fun_inv inl U) ∧ F2 (fun_inv inr U) |}.
  - intros U1 U2 Heq. rewrite Heq. done.
  - split; rewrite //=.
  - intros U (HF1&HF2).
    split.
    * apply sigma_closed_complements in HF1. eapply sigma_proper; eauto.
      firstorder.
    * apply sigma_closed_complements in HF2. eapply sigma_proper; eauto.
      firstorder.
  - intros Us.
    intros Hi. split.
    * assert (Hinl: ∀ i, F1 (fun_inv inl (Us i))); first by firstorder.
      apply sigma_closed_unions in Hinl.
      eapply sigma_proper; eauto.
      firstorder.
    * assert (Hinr: ∀ i, F2 (fun_inv inr (Us i))); first by firstorder.
      apply sigma_closed_unions in Hinr.
      eapply sigma_proper; eauto.
      firstorder.
Defined.

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
