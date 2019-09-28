Require Import Reals Psatz Omega Fourier.
From stdpp Require Import tactics list.
From discprob.basic Require Import seq_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.measure Require Export integral dynkin borel isomorphism.
Require Import ClassicalEpsilon.

Definition product_sigma {A B: Type} (F1: sigma_algebra A) (F2: sigma_algebra B) :=
  minimal_sigma (λ UV, ∃ U V, F1 U ∧ F2 V ∧ UV ≡ (λ ab, U (fst ab) ∧ V (snd ab))).

Definition left_section {A B: Type} (E: A * B → Prop) (a: A) : B → Prop :=
  λ b, E (a, b).

Definition right_section {A B: Type} (E: A * B → Prop) (b: B) : A → Prop :=
  λ a, E (a, b).

Global Instance left_section_proper {A B}:
  Proper (@eq_prop (A * B) ==> eq ==> eq_prop) left_section.
Proof. intros U U' Heq ?? ->. rewrite /left_section; split; eapply Heq. Qed.

Global Instance right_section_proper {A B}:
  Proper (@eq_prop (A * B) ==> eq ==> eq_prop) right_section.
Proof. intros U U' Heq ?? ->. rewrite /right_section; split; eapply Heq. Qed.

Lemma disjointF_left_section {A B: Type} (Us: nat → A * B → Prop) x:
  disjointF Us →
  disjointF (λ j : nat, left_section (Us j) x).
Proof.
  intros Hdisj. rewrite /left_section.
  intros i j Hneq y (Hin1&Hin2).
  eapply Hdisj; eauto.
Qed.

Lemma disjointF_right_section {A B: Type} (Us: nat → A * B → Prop) x:
  disjointF Us →
  disjointF (λ j : nat, right_section (Us j) x).
Proof.
  intros Hdisj. rewrite /right_section.
  intros i j Hneq y (Hin1&Hin2).
  eapply Hdisj; eauto.
Qed.

Definition left_section_sigma {A B: Type} (F2: sigma_algebra B) (a: A)
  : sigma_algebra (A * B).
Proof.
  refine {| sigma_sets := (λ UV, F2 (left_section UV a)) |}.
  - intros UV UV' Heq. by setoid_rewrite Heq.
  - eapply sigma_proper; last apply sigma_full.
    firstorder.
  - intros P. intros HF.
    eapply sigma_proper; last eapply sigma_closed_complements; eauto.
    firstorder.
  - intros Ps. intros HF.
    eapply sigma_proper; last eapply sigma_closed_unions; last first.
    { intros i. eapply (HF i). }
    firstorder.
Defined.

Definition right_section_sigma {A B: Type} (F2: sigma_algebra A) (a: B)
  : sigma_algebra (A * B).
Proof.
  refine {| sigma_sets := (λ UV, F2 (right_section UV a)) |}.
  - intros UV UV' Heq. by setoid_rewrite Heq.
  - eapply sigma_proper; last apply sigma_full.
    firstorder.
  - intros P. intros HF.
    eapply sigma_proper; last eapply sigma_closed_complements; eauto.
    firstorder.
  - intros Ps. intros HF.
    eapply sigma_proper; last eapply sigma_closed_unions; last first.
    { intros i. eapply (HF i). }
    firstorder.
Defined.

Lemma left_section_measurable {A B: Type} {F1 F2} (E: A * B → Prop) x:
  product_sigma F1 F2 E →
  F2 (left_section E x).
Proof.
  revert E.
  cut (le_prop (product_sigma F1 F2) (left_section_sigma F2 x)).
  { intros Hle. eapply Hle; eauto. }
  apply minimal_sigma_lub.
  intros UV (U&V&?&?&->).
  rewrite //=.
  rewrite /left_section//=.
  destruct (Classical_Prop.classic (U x)).
  - eapply sigma_proper; eauto.
    firstorder.
  - eapply sigma_proper; last eapply sigma_empty_set.
    firstorder.
Qed.

Lemma right_section_measurable {A B: Type} {F1 F2} (E: A * B → Prop) x :
  product_sigma F1 F2 E →
  F1 (right_section E x).
Proof.
  revert E.
  cut (le_prop (product_sigma F1 F2) (right_section_sigma F1 x)).
  { intros Hle. eapply Hle; eauto. }
  apply minimal_sigma_lub.
  intros UV (U&V&?&?&->).
  rewrite //=.
  rewrite /left_section//=.
  destruct (Classical_Prop.classic (V x)).
  - eapply sigma_proper; eauto.
    firstorder.
  - eapply sigma_proper; last eapply sigma_empty_set.
    firstorder.
Qed.

Lemma fun_left_measurable {A B C: Type} F1 F2 F3 (f : A * B → C) x:
  measurable f (product_sigma F1 F2) F3 →
  measurable (λ y, f (x, y)) F2 F3.
Proof.
  intros Hmeas U HU.
  eapply sigma_proper; last eapply (left_section_measurable (fun_inv f U) x);
    eauto; firstorder.
Qed.

Lemma fun_right_measurable {A B C: Type} F1 F2 F3 (f : A * B → C) y:
  measurable f (product_sigma F1 F2) F3 →
  measurable (λ x, f (x, y)) F1 F3.
Proof.
  intros Hmeas U HU.
  eapply sigma_proper; last eapply (right_section_measurable (fun_inv f U) y);
    eauto; firstorder.
Qed.

Lemma pair_measurable {A B C: Type} F1 F2 F3 (f : A → B) (g: A → C):
  measurable f F1 F2 →
  measurable g F1 F3 →
  measurable (λ x, (f x, g x)) F1 (product_sigma F2 F3).
Proof.
  intros Hmeasf Hmeasg.
  apply measurable_generating_sets.
  intros ? (U&V&HU&HV&->).
  rewrite /fun_inv//=.
  assert ((λ a, U (f a) ∧ V (g a)) ≡ fun_inv f U ∩ fun_inv g V) as ->.
  { intuition. }
  apply sigma_closed_pair_intersect; eauto.
Qed.

Section product_measure.
  Context {A B: Type}.
  Context {F1: sigma_algebra A} {F2: sigma_algebra B}.
  Context (μ: measure F1) (ν: measure F2).

  Lemma wpt_indicator_left_section U (Hmeas : product_sigma F1 F2 U) x:
    (∀ y, wpt_fun (wpt_indicator U Hmeas) (x, y) =
          wpt_fun (wpt_indicator (left_section U x) (left_section_measurable _ _ Hmeas)) y).
  Proof. intros y. rewrite ?wpt_indicator_spec/left_section//=. Qed.

  Lemma wpt_indicator_right_section U (Hmeas : product_sigma F1 F2 U) y:
    (∀ x, wpt_fun (wpt_indicator U Hmeas) (x, y) =
          wpt_fun (wpt_indicator (right_section U y) (right_section_measurable _ _ Hmeas)) x).
  Proof. intros x. rewrite ?wpt_indicator_spec/right_section//=. Qed.

  Lemma measure_left_section_rectangle (U: A → Prop) (V: B → Prop) (x: A) (Hmeas: F1 U):
    ν (left_section (λ x, U (fst x) ∧ V (snd x)) x) =
    ν V * (wpt_fun (wpt_indicator U Hmeas) x).
  Proof.
    rewrite /left_section wpt_indicator_spec.
    destruct (excluded_middle_informative).
    * rewrite Rmult_1_r. apply measure_proper.
      split; intuition.
    * rewrite Rmult_0_r. etransitivity; last eapply measure_empty.
      apply measure_proper. split.
      ** intros (?&?); intuition. 
      ** inversion 1.
  Qed.

  Lemma measure_right_section_rectangle (U: A → Prop) (V: B → Prop) (y: B) (Hmeas: F2 V):
    μ (right_section (λ x, U (fst x) ∧ V (snd x)) y) =
    μ U * (wpt_fun (wpt_indicator V Hmeas) y).
  Proof.
    rewrite /right_section wpt_indicator_spec.
    destruct (excluded_middle_informative).
    * rewrite Rmult_1_r. apply measure_proper.
      split; intuition.
    * rewrite Rmult_0_r. etransitivity; last eapply measure_empty.
      apply measure_proper. split.
      ** intros (?&?); intuition. 
      ** inversion 1.
  Qed.

  Lemma measurable_measure_left U:
    product_sigma F1 F2 U →
    measurable (λ x : A, ν (left_section U x)) F1 (borel R_UniformSpace).
  Proof.
    intros HU.
    set (F := (λ U, product_sigma F1 F2 U ∧ measurable (λ x, ν (left_section U x)) F1 (borel _))).
    cut (eq_prop (product_sigma F1 F2) F).
    { intros Heq. destruct (Heq U) as (Himpl1&Himpl2); eauto.
      destruct (Himpl1); eauto. }
    apply le_prop_antisym; last first.
    { intros ? (?&?); eauto. }
    assert (HFproper: Proper (eq_prop ==> iff) F).
    { intros ?? Heq. rewrite /F. setoid_rewrite Heq. auto. }
    assert (HFfull: F (λ _, True)).
    { split; first apply sigma_full.
      assert ((λ _ : A * B, True) ≡ (λ x : A * B, (λ _ :A , True) (fst x) ∧ (λ _ :B , True) (snd x)))
             as Heq.
      { split; auto. }
      eapply measurable_ext.
      { intros x. apply measure_proper. by rewrite Heq.  }
      eapply measurable_ext.
      { intros x. rewrite (measure_left_section_rectangle (λ _, True) (λ _, True)). done. }
      measurable.
      apply wpt_fun_measurable. 
    }
    assert (HFset_minus: ∀ P Q, F P → F Q → Q ⊆ P → F (set_minus P Q)).
    { 
      intros P Q (HP&?) (HQ&?) Hsub.
      rewrite /F; split; first (apply sigma_closed_set_minus; auto).
      assert (∀ x, ν (left_section (set_minus P Q) x) =
                   ν (left_section P x) - ν (left_section Q x)) as Heq.
      { intros x. rewrite -measure_set_minus; eauto using left_section_measurable.
        clear -Hsub. firstorder.
      }
      setoid_rewrite Heq.
      measurable.
    }
    assert (HF_closed_unions : ∀ Ps, (∀ i, F (Ps i)) → (∀ i, Ps i ⊆ Ps (S i)) → F (unionF Ps)).
    { intros Ps HPs Hmono. split.
      * apply sigma_closed_unions. intros i.
        destruct (HPs i); eauto.
      * assert (∀ x, ν (left_section (unionF Ps) x) =
                     Lim_seq (λ i, ν (left_section (Ps i) x))) as Heq.
        { intros x.  symmetry.
          cut (is_lim_seq (λ i, ν (left_section (Ps i) x)) (ν (left_section (unionF Ps) x))).
          { intros Heq. apply is_lim_seq_unique in Heq.
            rewrite Heq => //=. }
          assert (eq_prop (left_section (unionF Ps) x) (unionF (λ i, left_section (Ps i) x))) as ->.
          { clear. firstorder. }
          apply measure_incr_seq; eauto.
          * intros i. specialize (HPs i) as (?&?). eapply left_section_measurable; eauto.
          * clear -Hmono. firstorder.
        }
        setoid_rewrite Heq.
        apply measurable_Lim'.
        intros i. destruct (HPs i); eauto.
    }
    set (pi := (λ UV, ∃ U V, F1 U ∧ F2 V ∧ UV ≡ (λ ab, U (fst ab) ∧ V (snd ab)))).
    assert (Hpiproper: Proper (eq_prop ==> iff) pi).
    { intros ?? Heq. rewrite /pi. by setoid_rewrite Heq. }
    assert (Hpiclosed: ∀ P Q, pi P → pi Q → pi (P ∩ Q)).
    { intros P Q HP HQ.
      destruct HP as (A1&B1&?&?&HequivP).
      destruct HQ as (A2&B2&?&?&HequivQ).
      exists (A1 ∩ A2). exists (B1 ∩ B2).
      split_and!; try apply sigma_closed_pair_intersect; eauto.
      { rewrite HequivP HequivQ; clear; firstorder. }
    }
    set (pi' := mkPiSystem _ pi Hpiproper Hpiclosed).
    assert (eq_prop (product_sigma F1 F2) (minimal_sigma pi')) as ->.
    { apply le_prop_antisym.
      - apply minimal_sigma_lub.
        intros ? (U'&V'&?&?&->).
        apply minimal_sigma_ub; do 2 eexists; split_and!; eauto.
      - apply minimal_sigma_lub.
        intros ? (U'&V'&?&?&->).
        apply minimal_sigma_ub; do 2 eexists; split_and!; eauto.
    }
    set (F' := mkDynkin _ F HFproper HFfull HFset_minus HF_closed_unions).
    transitivity F'; last by rewrite //=.
    assert (le_prop (minimal_dynkin pi') F') as <-.
    { apply minimal_dynkin_lub. intros ? (U'&V'&?&?&->). rewrite /F'//=.
      split; eauto.
      * apply minimal_sigma_ub; do 2 eexists; split_and!; eauto.
      * eapply measurable_ext.
        { intros x'. rewrite measure_left_section_rectangle. done. }
        measurable. apply wpt_fun_measurable.
    }
    rewrite pi_sigma_equiv_dynkin. done.
  Qed.

  Lemma measurable_measure_right V:
    product_sigma F1 F2 V →
    measurable (λ x : B, μ (right_section V x)) F2 (borel R_UniformSpace).
  Proof.
    intros HU.
    set (F := (λ U, product_sigma F1 F2 U ∧ measurable (λ x, μ (right_section U x)) F2 (borel _))).
    cut (eq_prop (product_sigma F1 F2) F).
    { intros Heq. destruct (Heq V) as (Himpl1&Himpl2); eauto.
      destruct (Himpl1); eauto. }
    apply le_prop_antisym; last first.
    { intros ? (?&?); eauto. }
    assert (HFproper: Proper (eq_prop ==> iff) F).
    { intros ?? Heq. rewrite /F. setoid_rewrite Heq. auto. }
    assert (HFfull: F (λ _, True)).
    { split; first apply sigma_full.
      assert ((λ _ : A * B, True) ≡ (λ x : A * B, (λ _ :A , True) (fst x) ∧ (λ _ :B , True) (snd x)))
             as Heq.
      { split; auto. }
      eapply measurable_ext.
      { intros x. apply measure_proper. by rewrite Heq.  }
      eapply measurable_ext.
      { intros x. rewrite (measure_right_section_rectangle (λ _, True) (λ _, True)). done. }
      measurable.
      apply wpt_fun_measurable. 
    }
    assert (HFset_minus: ∀ P Q, F P → F Q → Q ⊆ P → F (set_minus P Q)).
    { 
      intros P Q (HP&?) (HQ&?) Hsub.
      rewrite /F; split; first (apply sigma_closed_set_minus; auto).
      assert (∀ x, μ (right_section (set_minus P Q) x) =
                   μ (right_section P x) - μ (right_section Q x)) as Heq.
      { intros x. rewrite -measure_set_minus; eauto using right_section_measurable.
        clear -Hsub. firstorder.
      }
      setoid_rewrite Heq.
      measurable.
    }
    assert (HF_closed_unions : ∀ Ps, (∀ i, F (Ps i)) → (∀ i, Ps i ⊆ Ps (S i)) → F (unionF Ps)).
    { intros Ps HPs Hmono. split.
      * apply sigma_closed_unions. intros i.
        destruct (HPs i); eauto.
      * assert (∀ x, μ (right_section (unionF Ps) x) =
                     Lim_seq (λ i, μ (right_section (Ps i) x))) as Heq.
        { intros x.  symmetry.
          cut (is_lim_seq (λ i, μ (right_section (Ps i) x)) (μ (right_section (unionF Ps) x))).
          { intros Heq. apply is_lim_seq_unique in Heq.
            rewrite Heq => //=. }
          assert (eq_prop (right_section (unionF Ps) x) (unionF (λ i, right_section (Ps i) x))) as ->.
          { clear. firstorder. }
          apply measure_incr_seq; eauto.
          * intros i. specialize (HPs i) as (?&?). eapply right_section_measurable; eauto.
          * clear -Hmono. firstorder.
        }
        setoid_rewrite Heq.
        apply measurable_Lim'.
        intros i. destruct (HPs i); eauto.
    }
    set (pi := (λ UV, ∃ U V, F1 U ∧ F2 V ∧ UV ≡ (λ ab, U (fst ab) ∧ V (snd ab)))).
    assert (Hpiproper: Proper (eq_prop ==> iff) pi).
    { intros ?? Heq. rewrite /pi. by setoid_rewrite Heq. }
    assert (Hpiclosed: ∀ P Q, pi P → pi Q → pi (P ∩ Q)).
    { intros P Q HP HQ.
      destruct HP as (A1&B1&?&?&HequivP).
      destruct HQ as (A2&B2&?&?&HequivQ).
      exists (A1 ∩ A2). exists (B1 ∩ B2).
      split_and!; try apply sigma_closed_pair_intersect; eauto.
      { rewrite HequivP HequivQ; clear; firstorder. }
    }
    set (pi' := mkPiSystem _ pi Hpiproper Hpiclosed).
    assert (eq_prop (product_sigma F1 F2) (minimal_sigma pi')) as ->.
    { apply le_prop_antisym.
      - apply minimal_sigma_lub.
        intros ? (U'&V'&?&?&->).
        apply minimal_sigma_ub; do 2 eexists; split_and!; eauto.
      - apply minimal_sigma_lub.
        intros ? (U'&V'&?&?&->).
        apply minimal_sigma_ub; do 2 eexists; split_and!; eauto.
    }
    set (F' := mkDynkin _ F HFproper HFfull HFset_minus HF_closed_unions).
    transitivity F'; last by rewrite //=.
    assert (le_prop (minimal_dynkin pi') F') as <-.
    { apply minimal_dynkin_lub. intros ? (U'&V'&?&?&->). rewrite /F'//=.
      split; eauto.
      * apply minimal_sigma_ub; do 2 eexists; split_and!; eauto.
      * eapply measurable_ext.
        { intros x'. rewrite measure_right_section_rectangle. done. }
        measurable. apply wpt_fun_measurable.
    }
    rewrite pi_sigma_equiv_dynkin. done.
  Qed.

  Lemma  product_measure_additivity1 (Us : nat → A * B → Prop):
    (∀ i : nat, (product_sigma F1 F2) (Us i)) →
    disjointF Us →
    is_series (λ n : nat, Integral μ (λ x : A, ν (left_section (Us n) x)))
        (Integral μ (λ x : A, ν (left_section (unionF Us) x))).
  Proof.
    intros HUs Hdisj.
    rewrite /is_series.
    assert (∀ n', ex_integral μ (λ x : A, ν (left_section (Us n') x))).
    { intros n'. apply (ex_integral_mono_ex _ _ (λ x, ν (λ _, True))).
      * intros x. rewrite Rabs_right; last auto.
        apply measure_mono; auto.
        { eapply left_section_measurable; eauto. }
        { clear. firstorder. }
      * apply measurable_measure_left. auto.
      * apply ex_integral_const.
    }
    cut (is_lim_seq (sum_n (λ n : nat, Integral μ (λ x : A, ν (left_section (Us n) x))))
                    (Integral μ (λ x, ν (left_section (unionF Us) x)))); first by auto.
    {
      eapply is_lim_seq_ext.
      { intros. apply Integral_sum_n. intros n' Hle; eauto. }
      edestruct (is_integral_levi_pos_ex μ) as (?&His); last eapply His.
      { apply measurable_measure_left. auto. }
      { intros x. rewrite //=.
        eapply measure_additivity; eauto.
        * intros i. eapply left_section_measurable; eauto.
        * intros i j Hneq z Hfalse.
          eapply Hdisj; eauto.
      }
      {
        intros x n => //=. induction n => //=.
        - rewrite sum_O. by apply Rge_le.
        - rewrite sum_Sn => //=. rewrite /plus//=.
          specialize (measure_nonneg ν (left_section (Us (S n)) x)).
          nra.
      }
      {
        intros x n => //=. rewrite sum_Sn. rewrite /plus//=.
        specialize (measure_nonneg ν (left_section (Us (S n)) x)).
        nra.
      }
      { intros n. apply ex_integral_sum_n; eauto. }
      { 
        exists (μ (λ _, True) * ν (λ _, True)).
        intros ? (n&His).
        eapply (is_integral_mono _ _ _ (λ x_, ν (λ _, True))); eauto.
        { intros; rewrite //=. rewrite -measure_sum_n_additivity.
          * apply measure_mono; last by done; auto.
            ** apply sigma_closed_range_union. intros.
               eapply left_section_measurable; eauto.
            ** auto.
          * intros; eapply left_section_measurable; eauto.
          * apply disjointF_left_section; auto. 
        }
        rewrite Rmult_comm.
        apply is_integral_const.
      }
    }
  Qed.

  Lemma  product_measure_additivity2 (Us : nat → A * B → Prop):
    (∀ i : nat, (product_sigma F1 F2) (Us i)) →
    disjointF Us →
    is_series (λ n : nat, Integral ν (λ x : B, μ (right_section (Us n) x)))
        (Integral ν (λ x : B, μ (right_section (unionF Us) x))).
  Proof.
    intros HUs Hdisj.
    rewrite /is_series.
    assert (∀ n', ex_integral ν (λ x : B, μ (right_section (Us n') x))).
    { intros n'. apply (ex_integral_mono_ex _ _ (λ x, μ (λ _, True))).
      * intros x. rewrite Rabs_right; last auto.
        apply measure_mono; auto.
        { eapply right_section_measurable; eauto. }
        { clear. firstorder. }
      * apply measurable_measure_right. auto.
      * apply ex_integral_const.
    }
    cut (is_lim_seq (sum_n (λ n : nat, Integral ν (λ x : B, μ (right_section (Us n) x))))
                    (Integral ν (λ x, μ (right_section (unionF Us) x)))); first by auto.
    {
      eapply is_lim_seq_ext.
      { intros. apply Integral_sum_n. intros n' Hle; eauto. }
      edestruct (is_integral_levi_pos_ex ν) as (?&His); last eapply His.
      { apply measurable_measure_right. auto. }
      { intros x. rewrite //=.
        eapply measure_additivity; eauto.
        * intros i. eapply right_section_measurable; eauto.
        * intros i j Hneq z Hfalse.
          eapply Hdisj; eauto.
      }
      {
        intros x n => //=. induction n => //=.
        - rewrite sum_O. by apply Rge_le.
        - rewrite sum_Sn => //=. rewrite /plus//=.
          specialize (measure_nonneg μ (right_section (Us (S n)) x)).
          nra.
      }
      {
        intros x n => //=. rewrite sum_Sn. rewrite /plus//=.
        specialize (measure_nonneg μ (right_section (Us (S n)) x)).
        nra.
      }
      { intros n. apply ex_integral_sum_n; eauto. }
      { 
        exists (μ (λ _, True) * ν (λ _, True)).
        intros ? (n&His).
        eapply (is_integral_mono _ _ _ (λ x_, μ (λ _, True))); eauto.
        { intros; rewrite //=. rewrite -measure_sum_n_additivity.
          * apply measure_mono; last by done; auto.
            ** apply sigma_closed_range_union. intros.
               eapply right_section_measurable; eauto.
            ** auto.
          * intros; eapply right_section_measurable; eauto.
          * apply disjointF_right_section; auto. 
        }
        apply is_integral_const.
      }
    }
  Qed.

  Definition product_measure : measure (product_sigma F1 F2).
  Proof.
    refine {| measure_fun := λ UV, Integral μ (λ x, ν (left_section UV x)) |}.
    - abstract (intros UV UV' Heq; setoid_rewrite Heq; done).
    - abstract (intros; apply Integral_ge0; intros; apply Rge_le; auto).
    - assert (∀ x : A, left_section (empty_set : A * B → Prop) x ≡ ∅) as Heq by auto.
      abstract (setoid_rewrite Heq; setoid_rewrite measure_empty; apply Integral_0).
    - apply product_measure_additivity1. 
  Defined.

  Definition product_measure_alt : measure (product_sigma F1 F2).
  Proof.
    refine {| measure_fun := λ UV, Integral ν (λ x, μ (right_section UV x)) |}.
    - abstract (intros UV UV' Heq; setoid_rewrite Heq; done).
    - abstract (intros; apply Integral_ge0; intros; apply Rge_le; auto).
    - assert (∀ x : B, right_section (empty_set : A * B → Prop) x ≡ ∅) as Heq by auto.
      abstract (setoid_rewrite Heq; setoid_rewrite measure_empty; apply Integral_0).
    - apply product_measure_additivity2.
  Defined.
    
  Lemma product_measure_equiv UV:
    product_sigma F1 F2 UV →
    product_measure UV = product_measure_alt UV.
  Proof.
    eapply pi_measure_equiv.
    - split.
      * intros ?? Heq. setoid_rewrite Heq. done.
      * intros P Q (U1&V1&?&?&Heq1) (U2&V2&?&?&Heq2).
        exists (U1 ∩ U2), (V1 ∩ V2).
        split_and!; auto.
        rewrite Heq1 Heq2. clear; firstorder.
    - rewrite //=. rewrite /left_section/right_section ?Integral_const. nra.
    - intros ? (U&V&HU&HV&->).
      rewrite //=. rewrite /left_section/right_section //=.
      assert (∀ x, (λ x : A, ν (λ b : B, U x ∧ V b)) x =
                   ν V * wpt_fun (wpt_indicator _ HU) x) as Heq.
      { intros x. rewrite wpt_indicator_spec. destruct excluded_middle_informative => //=.
        * rewrite Rmult_1_r. apply measure_proper; split; intros; intuition.
        * rewrite Rmult_0_r. rewrite -(measure_empty _ ν).
          apply measure_proper; split.
          ** intuition.
          ** inversion 1.
      }
      setoid_rewrite Heq. rewrite Integral_scal; last apply ex_integral_wpt.
      rewrite Integral_wpt wpt_integral_indicator.
      assert (∀ x, (λ x : B, μ (λ a : A, U a ∧ V x)) x =
                   μ U * wpt_fun (wpt_indicator _ HV) x) as Heq'.
      { intros x. rewrite wpt_indicator_spec. destruct excluded_middle_informative => //=.
        * rewrite Rmult_1_r. apply measure_proper; split; intros; intuition.
        * rewrite Rmult_0_r. rewrite -(measure_empty _ μ).
          apply measure_proper; split.
          ** intuition.
          ** inversion 1.
      }
      setoid_rewrite Heq'. rewrite Integral_scal; last apply ex_integral_wpt.
      rewrite Integral_wpt wpt_integral_indicator.
      nra.
  Qed.

End product_measure.

Definition swap {A1 A2: Type} (a: A1 * A2) := (snd a, fst a).

Lemma swap_measurable {A1 A2 F1 F2}:
  measurable (@swap A1 A2) (product_sigma F1 F2) (product_sigma F2 F1).
Proof.
  apply measurable_generating_sets.
  intros ? (V&U&HV&HU&->).
  apply minimal_sigma_ub.
  exists U, V; split_and!; eauto.
  firstorder.
Qed.

Lemma swap_is_pt_iso {A1 A2 F1 F2} (μ1: measure F1) (μ2: measure F2):
  is_pt_iso (@swap A1 A2) (product_measure μ1 μ2) (product_measure μ2 μ1).
Proof.
  split.
  - intros (?&?) (?&?); inversion 1; subst; eauto.
  - intros (a2&a1); exists (a1,a2); auto.
  - intros U HU. eapply sigma_proper; last first.
    { eapply swap_measurable; eauto. }
    rewrite /fun_img/fun_inv//=. clear. intros (x2&x1); split.
    * intros ((?&?)&HU&Heq). inversion Heq; subst. auto.
    * rewrite //=. intros. exists (x1, x2); split; auto.
  - apply swap_measurable.
  - intros U HU.
    rewrite [a in a = _]product_measure_equiv //=.
    apply Integral_ext => y.
    apply measure_proper.
    intros z. clear. split.
    * firstorder.
    * intros ((?&?)&?&Heq). inversion Heq. subst. firstorder.
  - intros U HU.
    rewrite [a in a = _]product_measure_equiv //=.
Qed.

Section fubini_tonelli_lr.

  Context {A B: Type}.
  Context {F1: sigma_algebra A} {F2: sigma_algebra B}.
  Context (μ: measure F1) (ν: measure F2).

  Definition wpt_proj2 (wpt: weighted_partition (product_sigma F1 F2)) (x: A)
    : weighted_partition F2.
  Proof.
    refine (wpt_indicator_scal_list (map (λ rU, (fst rU, left_section (snd rU) x)) wpt) _).
    { abstract (intros r U (rU&Heq&Hin)%in_map_iff;
                inversion Heq; subst; eapply (@left_section_measurable _ _ F1); eauto;
                eapply In_wpt_snd_measurable; eauto). }
  Defined.

  Lemma wpt_proj2_spec wpt x y:
    wpt_fun (wpt_proj2 wpt x) y = wpt_fun wpt (x, y).
  Proof.
    rewrite /wpt_proj2.
    edestruct (@wpt_indicator_scal_list_spec2) as [(Hneg&->)|Hcase]. 
    { specialize (wpt_map_snd_disjoint wpt).
      generalize (wpt_list wpt). clear. induction l.
      * rewrite //=. intros. econstructor.
      * rewrite //=. inversion 1 as [|?? Hdisj]; subst.
        econstructor; last eauto.
        intros z (Hin1&Hin2).
        apply (Hdisj (x, z)).
        split; auto.
        apply union_list_inv in Hin2 as (V&Hin&?).
        apply in_map_iff in Hin as ((?&?)&?&Hin). subst.
        apply in_map_iff in Hin as ((?&V')&Heq&?); subst. inversion Heq; subst.
        eapply (union_list_intro _ _ V'); eauto.
        apply in_map_iff. exists (r, V'); auto.
    }
    - exfalso. destruct (partition_union (wpt_part wpt) (x, y)) as (UV&?&?); first done.
      eapply (Hneg (wpt_fun wpt (x, y)) (left_section UV x)).
      * apply in_map_iff. exists (wpt_fun wpt (x, y), UV) => //=.
        split; eauto. apply wpt_fun_eq1; eauto. 
      * auto.
    - destruct Hcase as (r&U&Hin&HU&->).
      symmetry. apply in_map_iff in Hin.
      destruct Hin as ((r'&U')&Heq&Hin). rewrite //= in Hin.
      inversion Heq; subst.
      eapply wpt_fun_eq2; eauto.
  Qed.


  Lemma tonelli_lr_measurable_wpt wpt:
    measurable (λ x, Integral ν (λ y, @wpt_fun _ (product_sigma F1 F2) wpt (x, y))) F1 (borel _).
  Proof.
    induction wpt using wpt_induction.
    - eapply measurable_proper'; eauto.
      intros x. apply Integral_ext; eauto.
    - setoid_rewrite wpt_indicator_left_section => //=.
      setoid_rewrite Integral_wpt.
      setoid_rewrite wpt_integral_indicator.
      apply measurable_measure_left. auto.
    - eapply measurable_ext.
      { intros x. symmetry. setoid_rewrite wpt_plus_spec at 1. rewrite Integral_plus. done.
        * setoid_rewrite <-wpt_proj2_spec. apply ex_integral_wpt.
        * setoid_rewrite <-wpt_proj2_spec. apply ex_integral_wpt.
      }
      apply measurable_plus; eauto.
    - eapply measurable_ext.
      { intros x. symmetry. setoid_rewrite wpt_scal_spec at 1. rewrite Integral_scal. done.
        setoid_rewrite <-wpt_proj2_spec. apply ex_integral_wpt.
      }
      apply measurable_scal; eauto.
  Qed.

  Lemma tonelli_lr_pos_measurable (f: A * B → R):
    (∀ x, 0 <= f x) →
    measurable f (product_sigma F1 F2) (borel _) →
    measurable (λ x : A, Integral ν (λ y, f (x, y))) F1 (borel _).
  Proof.
    intros Hpos Hmeas.
    edestruct (wpt_approx_measurable _ Hpos Hmeas) as (wptn&?&?&?&?).
    assert (∀ x, (λ x : A, Integral ν (λ y : B, f (x, y))) x =
                 (λ x : A, Lim_seq (λ n, Integral ν (wpt_fun (wpt_proj2 (wptn n) x)))) x) as Heq.
    { intros x. symmetry.
      apply Integral_pos_mct; eauto.
      { eapply (fun_left_measurable F1 F2 _ _ x); eauto. }
      { intros. rewrite //=. setoid_rewrite wpt_proj2_spec. eauto.  }
      { intros. rewrite ?wpt_proj2_spec; eauto. }
      { intros. rewrite ?wpt_proj2_spec; eauto. }
    }
    setoid_rewrite Heq.
    apply measurable_Lim'.
    intros n. eapply measurable_ext; last eapply (tonelli_lr_measurable_wpt (wptn n)).
    intros x => //=. apply Integral_ext => ?. by rewrite wpt_proj2_spec.
  Qed.

  Lemma tonelli_lr_measurable (f: A * B → R):
    measurable f (product_sigma F1 F2) (borel _) →
    measurable (λ x : A, Integral ν (λ y, f (x, y))) F1 (borel _).
  Proof.
    intros. rewrite /Integral.
    eapply measurable_ext.
    { intros x. rewrite -?Integral_equiv_Pos_integral; eauto using Rmax_r. }
    { apply measurable_plus; last (apply measurable_opp).
      - eapply (tonelli_lr_pos_measurable (λ x, Rmax (f x) 0)); eauto using Rmax_r.
        apply measurable_Rmax; measurable.
      - eapply (tonelli_lr_pos_measurable (λ x, Rmax (-f x) 0)); eauto using Rmax_r.
        apply measurable_Rmax; measurable.
    }
  Qed.

  Lemma ex_integral_left_section_measure U:
    product_sigma F1 F2 U →
    ex_integral μ (λ x : A, ν (left_section U x)).
  Proof.
    intros Hsigma.
    apply (ex_integral_mono_ex _ _ (λ x, ν (λ _, True))).
    { intros x. rewrite Rabs_right; auto.
      apply measure_mono; eauto using left_section_measurable; done. }
    { by apply measurable_measure_left. }
    { apply ex_integral_const. }
  Qed.

  Lemma ex_integral_left_wpt (wpt: weighted_partition (product_sigma F1 F2)) x:
    ex_integral ν (λ y, wpt_fun wpt (x, y)).
  Proof.
    eapply (ex_integral_ext _ (wpt_fun (wpt_proj2 wpt x))).
    { intros ?. by rewrite wpt_proj2_spec. }
    apply ex_integral_wpt.
  Qed.

  Hint Resolve ex_integral_left_wpt.

  Lemma tonelli_lr_integral_wpt (wpt : weighted_partition (product_sigma F1 F2)):
    is_integral μ (λ x, Integral ν (λ y, wpt_fun wpt (x, y)))
                (Integral (product_measure μ ν) (wpt_fun wpt)).
  Proof.
    induction wpt as [wpt1 wpt2 Heq| | | ] using wpt_induction.
    - eapply is_integral_ext.
      { intros x. eapply Integral_ext => y. rewrite -(Heq (x, y)). done. }
      rewrite -(Integral_ext _ (wpt_fun wpt1) (wpt_fun wpt2)) //.
    - rewrite Integral_wpt wpt_integral_indicator //=.
      setoid_rewrite wpt_indicator_left_section.
      setoid_rewrite Integral_wpt. setoid_rewrite wpt_integral_indicator.
      apply Integral_correct, ex_integral_left_section_measure.
      done.
    - rewrite Integral_wpt wpt_integral_plus.
      setoid_rewrite wpt_plus_spec. 
      eapply is_integral_ext.
      { intros x. rewrite Integral_plus; eauto. }
      apply is_integral_plus; rewrite -Integral_wpt; done.
    - rewrite Integral_wpt wpt_integral_scal.
      setoid_rewrite wpt_scal_spec. 
      eapply is_integral_ext.
      { intros x. rewrite Integral_scal; eauto. }
      apply is_integral_scal; rewrite -Integral_wpt; done.
  Qed.

  Global Instance is_lim_seq_Proper:
    Proper (pointwise_relation _ eq ==> eq ==> iff) is_lim_seq.
  Proof.
    intros ?? Heq ?? Heq'. split; subst; apply is_lim_seq_ext; done.
  Qed.

  Global Instance Lim_seq_Proper:
    Proper (pointwise_relation _ eq ==> eq) Lim_seq.
  Proof.
    intros ?? Heq. apply Lim_seq_ext; eauto.
  Qed.

  Lemma tonelli_lr_Integral_wpt (wpt : weighted_partition (product_sigma F1 F2)):
    Integral μ (λ x, Integral ν (λ y, wpt_fun wpt (x, y))) =
                (Integral (product_measure μ ν) (wpt_fun wpt)).
  Proof.
    apply is_integral_unique, tonelli_lr_integral_wpt.
  Qed.

  Lemma fubini_lr_pos_integral_aux (f: A * B → R):
    (∀ x, 0 <= f x) →
    measurable f (product_sigma F1 F2) (borel _) →
    ex_integral (product_measure μ ν) f →
    almost_everywhere_meas μ (λ x, ex_integral ν (λ y, f (x, y))) →
    is_integral μ (λ x, Integral ν (λ y, f (x, y)))
                (Integral (product_measure μ ν) f).
  Proof.
    intros Hpos Hmeas Hae Hex.
    edestruct (wpt_approx_measurable _ Hpos Hmeas) as (wptn&?&?&?&?).
    feed pose proof (is_integral_mct_ex (product_measure μ ν) (λ n, wpt_fun (wptn n)) f f)
      as Hmct; eauto using ex_integral_wpt.
    { intros x n. rewrite Rabs_right; eauto. }
    destruct Hmct as (_&His).
    generalize His => His_alt.
    setoid_rewrite <-tonelli_lr_Integral_wpt in His.
    feed pose proof (is_integral_levi_ae_ex μ (λ n, λ x, Integral ν (λ y, (wpt_fun (wptn n) (x, y))))
                                        (λ x, Integral ν (λ y, f (x, y)))) as Hlevi; eauto.
    { apply tonelli_lr_measurable; eauto. }
    { eapply almost_everywhere_meas_mono; eauto.
      { measurable; eauto.
        * intros n. apply tonelli_lr_measurable_wpt.
        * eapply measurable_comp; first apply tonelli_lr_measurable; eauto.
          eapply measurable_Finite.
      }
      intros x Hbound.
      eapply is_integral_mct_ex; eauto.
      intros. rewrite Rabs_right; eauto.
    }
    { apply almost_everywhere_meas_everywhere.
      intros. apply Integral_mono; eauto using ex_integral_wpt. }
    { intros; eexists; eapply tonelli_lr_integral_wpt. }
    { exists (Integral (product_measure μ ν) f).  intros r (n&His_r).
      apply is_integral_unique in His_r as <-.
      eapply is_lim_seq_incr_compare in His; eauto.
      { intros n'.  rewrite ?tonelli_lr_Integral_wpt.
        eapply Integral_mono; eauto using ex_integral_wpt. }
    }
    destruct Hlevi as (Hex'&His').
    eauto.
    cut ((Integral μ (λ x : A, Integral ν (λ y : B, f (x, y)))) =
         (Integral (product_measure μ ν) f)).
    { intros <-. by apply Integral_correct. }
    apply is_lim_seq_unique in His.
    apply is_lim_seq_unique in His'. congruence.
  Qed.

  Lemma fubini_lr_pos_integral_ae (f: A * B → R):
    (∀ x, 0 <= f x) →
    measurable f (product_sigma F1 F2) (borel _) →
    ex_integral (product_measure μ ν) f →
    almost_everywhere_meas μ (λ x, ex_integral ν (λ y, f (x, y))).
  Proof.
    intros Hpos Hmeas Hex.
    assert (Himp: ∀ P Q : Prop, P ∧ (P → Q) → P ∧ Q) by intuition.
    assert (∀ i,
        measurable (λ x : A, Integral ν (λ y : B, Rmin (f (x, y)) (INR i))) F1 (borel _)).
    { 
      intros i.
      apply (tonelli_lr_measurable (λ ab, Rmin (f ab) (INR i))).
      apply measurable_Rmin; measurable.
    }
    apply Himp.
    split.
    { apply sigma_closed_complements.
      eapply (sigma_proper _ F1
              (λ x, ex_finite_lim_seq (λ n, Integral ν (λ y, Rmin (f (x, y)) (INR n))))).
      { intros x. rewrite -ex_integral_ex_finite_lim_min; eauto using fun_left_measurable. }
      measurable.
    }
    intros HF.
    apply Rle_antisym; last apply Rge_le, measure_nonneg.
    apply Rnot_gt_le. intros Hgt.
    destruct Hex as (v&His).
    feed pose proof (is_integral_ge0 (product_measure μ ν) f v); eauto.

    cut (∀ k, F1 (unionF (λ n x, INR (S k) <= Integral ν (λ y, Rmin (f (x, y)) (INR n)))) ∧
              μ (unionF (λ n x, INR (S k) <= Integral ν (λ y, Rmin (f (x, y)) (INR n))))
              <= (v + 1) / INR (S k)).
    { intros Hsmall.
      edestruct (archimed_cor1 (μ (compl (λ x : A, ex_integral ν (λ y : B, f (x, y)))) / (v + 1))) as
          (n&Hr1&Hr2).
      { apply Rdiv_lt_0_compat; auto.
        nra. }
      destruct n as [| n]; first by omega.
      destruct (Hsmall n) as (Hmeas'&Hsize).
      cut (μ (compl (λ x : A, ex_integral ν (λ y : B, f (x, y)))) <=
           μ (unionF (λ n0 (x : A), INR (S n) <= Integral ν (λ y : B, Rmin (f (x, y)) (INR n0))))).
      { intros Hle.
        apply (Rmult_lt_compat_r (v + 1)) in Hr1; last by nra.
        field_simplify in Hr1; try nra.
        feed pose proof (pos_INR' (S n)); auto. nra.
      }
      clear -HF Hpos Hmeas Hmeas'. 
      apply measure_mono; auto.
      intros x Hneg.
      apply Classical_Pred_Type.not_all_not_ex.
      intros Hall.
      apply Hneg. apply ex_integral_sup_min; eauto.
      { eapply fun_left_measurable; eauto. }
      exists (INR (S n)).
      intros ? (?&<-).
      left. apply Rnot_le_gt. eauto.
    }
    intros k. apply Himp. 
    split.
    { apply sigma_closed_unions => i; apply measurable_fun_ge; eauto. }
    intros Hmeas'.
    feed pose proof (ex_integral_Rmin (product_measure μ ν) f) as Hex; eauto.
    assert (Hlen: ∀ n , μ (λ x, INR (S k) <= Integral ν (λ y : B, Rmin (f (x, y)) (INR n)))
                         <= (v + 1) / INR (S k)).
    { 
      intros n.
      specialize (Hex n).
      destruct Hex as (v'&His').
      assert (v' <= v + 1).
      { transitivity v; last nra.
        eapply is_integral_mono; eauto.
        intros => //=. apply Rmin_l. }
      transitivity (v' / INR (S k)); last first.
      { rewrite /Rdiv. apply Rmult_le_compat_r; auto. left.
        apply Rinv_0_lt_compat. apply pos_INR'. omega. }
      apply is_integral_bound_measure_above; auto.
      - intros. apply Rge_le, Integral_ge0. intros; apply Rmin_case_strong; eauto using pos_INR.
      - rewrite -(is_integral_unique _ _ _ His').
        apply (fubini_lr_pos_integral_aux (λ x, Rmin (f x) (INR n))).
        * intros. apply Rmin_case_strong; eauto using pos_INR.
        * apply measurable_Rmin; measurable.
        * apply ex_integral_Rmin; eauto.
        * apply almost_everywhere_meas_everywhere. intros x.
          apply ex_integral_Rmin; eauto.
          eapply fun_left_measurable; eauto.
      - apply pos_INR'; omega.
    }
    eapply (is_lim_seq_le _ _ (Finite _) (Finite _)); last eapply is_lim_seq_const.
    { intros n. apply Hlen. }
    apply measure_incr_seq.
    - intros n. apply measurable_fun_ge; eauto.
    - intros i x Hle. etransitivity; eauto.
      apply Integral_mono; eauto.
      * intros. apply Rle_min_compat_l, le_INR. omega.
      * apply ex_integral_Rmin; eauto.
        eapply fun_left_measurable; eauto.
      * apply ex_integral_Rmin; eauto.
        eapply fun_left_measurable; eauto.
  Qed.

  Lemma fubini_lr_pos_integral (f: A * B → R):
    (∀ x, 0 <= f x) →
    ex_integral (product_measure μ ν) f →
    is_integral μ (λ x, Integral ν (λ y, f (x, y)))
                (Integral ((product_measure μ ν)) f).
  Proof.
    intros Hpos Hex.
    apply fubini_lr_pos_integral_aux; eauto.
    apply fubini_lr_pos_integral_ae; eauto.
  Qed.

  Lemma fubini_lr_pos_Integral (f: A * B → R):
    (∀ x, 0 <= f x) →
    ex_integral (product_measure μ ν) f →
    Integral μ (λ x, Integral ν (λ y, f (x, y))) =
                (Integral ((product_measure μ ν)) f).
  Proof.
    intros Hpos Hex.
    apply is_integral_unique, fubini_lr_pos_integral; eauto.
  Qed.

  Lemma fubini_lr_integral (f: A * B → R):
    ex_integral (product_measure μ ν) f →
    is_integral μ (λ x, Integral ν (λ y, f (x, y)))
                (Integral ((product_measure μ ν)) f).
  Proof.
    intros Hex.
    cut (ex_integral μ (λ x, Integral ν (λ y, f (x, y))) ∧
         (Integral μ (λ x, Integral ν (λ y, f (x, y))) = Integral (product_measure μ ν) f)).
    { intros (Hex'&His). rewrite -His. apply Integral_correct; eauto. }
    assert (Himp: ∀ P Q : Prop, P ∧ (P → Q) → P ∧ Q) by intuition.
    apply Himp; clear Himp; split.
    - apply ex_integral_Rabs.
      { apply tonelli_lr_measurable. destruct Hex. eapply is_integral_measurable; eauto. }
      feed pose proof (fubini_lr_pos_integral_ae (λ x, Rabs (f x))); eauto.
      { measurable. eauto. }
      { apply ex_integral_Rabs in Hex; eauto. }
      eapply (ex_integral_ae_mono_ex _ _ (λ x, Integral ν (λ y, Rabs (f (x, y))))).
      {
        eapply almost_everywhere_meas_mono; last eauto.
        { apply measurable_fun_le_inv.
          * apply measurable_Rabs, measurable_Rabs. apply tonelli_lr_measurable.
            eauto.
          * apply (tonelli_lr_measurable (λ x, Rabs (f x))).
            measurable. eauto.
        }
        intros x Hex'. rewrite Rabs_right; last eauto.
        apply Integral_Rabs.
        right; split; eauto.
        eapply fun_left_measurable; eauto. 
      }
      * apply measurable_Rabs.
        apply tonelli_lr_measurable; eauto.
      * eexists. eapply (fubini_lr_pos_integral_aux (λ x, Rabs (f x))); eauto.
        { apply measurable_Rabs; eauto. }
        { apply ex_integral_Rabs in Hex; eauto. }
    - rewrite [a in _ = a]Integral_alt.
      apply ex_integral_alt in Hex as (?&?&?).
      feed pose proof (fubini_lr_pos_integral (λ x, Rmax (f x) 0)) as Hfb1; eauto using Rmax_r.
      feed pose proof (fubini_lr_pos_integral (λ x, Rmax (- f x) 0)) as Hfb2; eauto using Rmax_r.
      rewrite -(is_integral_unique _ _ _ Hfb1).
      rewrite -(is_integral_unique _ _ _ Hfb2).
      rewrite -Integral_minus; try (eexists; eauto).
      feed pose proof (fubini_lr_pos_integral_ae (λ x, Rmax (f x) 0)) as Hfb1';
        eauto using Rmax_r.
      feed pose proof (fubini_lr_pos_integral_ae (λ x, Rmax (- f x) 0)) as Hfb2';
        eauto using Rmax_r.
      generalize (almost_everywhere_meas_conj _ _ _ Hfb1' Hfb2').
      intros Hae. apply Integral_ae_ext_weak; last first.
      { apply measurable_minus; eauto. }
      eapply almost_everywhere_meas_mono; last eapply Hae.
      { apply measurable_fun_eq_inv; eauto.
        * apply tonelli_lr_measurable; auto.  
        * apply measurable_minus; eauto.
      }
      intros x (Hex1&Hex2).
      rewrite -Integral_minus; eauto.
      apply Integral_ext.
      intros y. do 2 apply Rmax_case_strong; nra.
  Qed.

  Lemma fubini_lr_integral_ae (f: A * B → R):
    ex_integral (product_measure μ ν) f →
    almost_everywhere_meas μ (λ x, ex_integral ν (λ y, f (x, y))).
  Proof.
    intros Hex.
    feed pose proof (fubini_lr_pos_integral_ae (λ x, Rabs (f x))); eauto.
    { measurable. eauto. }
    { apply ex_integral_Rabs in Hex; eauto. }
    eapply almost_everywhere_meas_ext; eauto.
    intros x. symmetry. apply ex_integral_Rabs; eauto using fun_left_measurable.
  Qed.

  Lemma fubini_lr_Integral (f: A * B → R):
    ex_integral (product_measure μ ν) f →
    Integral μ (λ x, Integral ν (λ y, f (x, y))) = (Integral ((product_measure μ ν)) f).
  Proof.
    intros. eapply is_integral_unique, fubini_lr_integral; auto.
  Qed.

  Lemma tonelli_lr_integral (f: A * B → R):
    (∀ x, 0 <= f x) →
    measurable f (product_sigma F1 F2) (borel _) →
    almost_everywhere_meas μ (λ x, ex_integral ν (λ y, f (x, y))) →
    ex_integral μ (λ x, Integral ν (λ y, f (x, y))) →
    ex_integral (product_measure μ ν) f.
  Proof.
    intros Hpos Hmeas Hae Hex.
    apply ex_integral_sup_min; eauto.
    destruct Hex as (v&His).
    exists v. intros ? (n&<-).
    rewrite -(is_integral_unique _ _ _ His).
    rewrite -fubini_lr_Integral; last first.
    { apply ex_integral_Rmin; eauto. }
    apply Integral_ae_mono.
    { eapply almost_everywhere_meas_mono; eauto.
      { apply measurable_fun_le_inv; eauto.
        apply (tonelli_lr_measurable (λ x, Rmin (f x) (INR n))).
        measurable. }
      intros x Hex. apply Integral_mono; eauto using ex_integral_Rmin.
      intros. apply Rmin_l.
    }
    { eexists. eapply (fubini_lr_integral (λ x, Rmin (f x) (INR n))), ex_integral_Rmin; eauto. }
    { eexists; eauto. }
  Qed.

End fubini_tonelli_lr.


Section fubini_tonelli_rl.
  Context {A B: Type}.
  Context {F1: sigma_algebra A} {F2: sigma_algebra B}.
  Context (μ: measure F1) (ν: measure F2).

  Lemma tonelli_rl_measurable (f: A * B → R):
    measurable f (product_sigma F1 F2) (borel _) →
    measurable (λ y : B, Integral μ (λ x, f (x, y))) F2 (borel _).
  Proof.
    intros Hmeas. eapply (measurable_ext _ _ (λ y : B, Integral μ (λ x, f (swap (y, x))))).
    { rewrite //=. }
    apply (tonelli_lr_measurable _ (λ x, f (swap x))). 
    eapply (measurable_comp); eauto.
    apply swap_measurable.
  Qed.
  
  Lemma ex_integral_swap (f: A * B → R) :
    ex_integral (product_measure μ ν) f →
    ex_integral (product_measure ν μ) (λ x : B * A, f (swap x)).
  Proof.
    eapply ex_integral_iso; first apply swap_is_pt_iso.
  Qed.

  Lemma fubini_rl_integral_ae (f: A * B → R):
    ex_integral (product_measure μ ν) f →
    almost_everywhere_meas ν (λ y, ex_integral μ (λ x, f (x, y))).
  Proof.
    intros Hex. 
    feed pose proof (fubini_lr_integral_ae ν μ (λ x, f (swap x))).
    { by apply ex_integral_swap. }
    eapply almost_everywhere_meas_ext; eauto.
    intros x. rewrite /swap//=.
  Qed.

  Lemma fubini_rl_integral (f: A * B → R):
    ex_integral (product_measure μ ν) f →
    is_integral ν (λ y, Integral μ (λ x, f (x, y)))
                (Integral ((product_measure μ ν)) f).
  Proof.
    intros Hex. eapply (is_integral_ext _ (λ y, Integral μ (λ x, f (swap (y, x))))).
    { rewrite //=. }
    feed pose proof (fubini_lr_integral ν μ (λ x, f (swap x))) as Hfub.
    { by eapply ex_integral_swap. }
    rewrite (Integral_iso swap _ (product_measure μ ν)) in Hfub; eauto.
    { apply swap_is_pt_iso. }
  Qed.

  Lemma tonelli_rl_integral (f: A * B → R):
    (∀ x, 0 <= f x) →
    measurable f (product_sigma F1 F2) (borel _) →
    almost_everywhere_meas ν (λ y, ex_integral μ (λ x, f (x, y))) →
    ex_integral ν (λ y, Integral μ (λ x, f (x, y))) →
    ex_integral (product_measure μ ν) f.
  Proof.
    intros.
    eapply ex_integral_iso; first apply swap_is_pt_iso.
    eapply (tonelli_lr_integral ν μ); eauto.
    eapply measurable_comp; eauto.
    eapply (iso_measurable (product_measure ν μ)); eapply swap_is_pt_iso.
  Qed.

End fubini_tonelli_rl.