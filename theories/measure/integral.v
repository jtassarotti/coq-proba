Require Import Reals Psatz Omega Fourier.
From stdpp Require Import tactics list.
From discprob.basic Require Import seq_ext.
From mathcomp Require Import bigop.
From discprob.measure Require Export measures borel convergence integral_prelim.
Require Import ClassicalEpsilon SetoidList.

Section integral.
  Context {A: Type}.
  Context {F: measurable_space A}.
  Context (μ: measure A).

  Local Notation is_pos_integral := (@is_pos_integral A F μ).
  Local Notation ex_pos_integral := (@ex_pos_integral A F μ).
  Local Notation Pos_integral := (@Pos_integral A F μ).

  Definition is_integral (f: A → R) v :=
    measurable f ∧
    ∃ v1 v2, is_pos_integral (λ x, Rmax (f x) 0) v1 ∧
             is_pos_integral (λ x, Rmax (- f x) 0) v2 ∧
             v = v1 - v2.

  Definition ex_integral (f: A → R) :=
    ∃ v, is_integral f v.

  Definition Integral (f : A → R) : R :=
    Pos_integral (λ x, Rmax (f x) 0) - Pos_integral (λ x, Rmax (- f x) 0).

  Definition is_integral_over (U : A → Prop) (f: A → R) v :=
    F U ∧ is_integral (λ x, f x *  match excluded_middle_informative (U x) with
                                   | left _ => 1
                                   | right _ => 0
                                   end) v.

  Definition ex_integral_over U f := ∃ v, is_integral_over U f v.

  Definition Integral_over U f :=
    Integral (λ x, f x * match excluded_middle_informative (U x) with
                         | left _ => 1
                         | right _ => 0
                         end).

  Lemma is_integral_unique f v :
    is_integral f v → Integral f = v.
  Proof.
    rewrite /is_integral. intros (Hmeas&v1&v2&?&?&Heq).
    rewrite /Integral.
    erewrite is_pos_integral_unique; eauto.
    erewrite is_pos_integral_unique; eauto.
  Qed.

  Lemma Integral_correct f: ex_integral f → is_integral f (Integral f).
  Proof.
    intros [v Hpos]. rewrite (is_integral_unique f v) //=.
  Qed.

  Lemma is_pos_integral_diff f1 f2 g1 g2 v1 v2 v1' v2':
    (∀ x, 0 <= f1 x) →
    (∀ x, 0 <= f2 x) →
    (∀ x, 0 <= g1 x) →
    (∀ x, 0 <= g2 x) →
    (∀ x, f1 x - f2 x = g1 x - g2 x) →
    is_pos_integral f1 v1 →
    is_pos_integral f2 v2 →
    is_pos_integral g1 v1' →
    is_pos_integral g2 v2' →
    v1 - v2 = v1' - v2'.
  Proof.
    intros ???? Hdiff Hi1 Hi2 Hi1' Hi2'.
    assert (Hsum: ∀ x, f1 x + g2 x = g1 x + f2 x).
    { intros x. specialize (Hdiff x). nra. }
    cut (v1 + v2' = v1' + v2); first by nra.
    feed pose proof (is_pos_integral_plus μ f1 v1 g2 v2'); eauto.
    feed pose proof (is_pos_integral_plus μ g1 v1' f2 v2); eauto.
    etransitivity; last apply is_pos_integral_unique; eauto.
    symmetry. apply is_pos_integral_unique.
    setoid_rewrite <-Hsum. done.
  Qed.

  Lemma is_integral_scal k f v:
    is_integral f v → is_integral (λ x, k * f x) (k * v).
  Proof.
    destruct (Rle_dec 0 k).
    - intros (Hmeas&v1&v2&Hpos1&Hpos2&Hdiff).
      split.
      { by apply measurable_scal. }
      exists (k * v1), (k * v2).
      split_and!.
      * eapply is_pos_integral_ext; last first.
        { eapply is_pos_integral_scal; auto; last eauto.
          intros x => //=. apply Rmax_r. }
        intros x => //=.
        replace 0 with (k * 0) at 2 by field.
        rewrite Rmult_comm Rmax_mult; auto.
        f_equal; nra.
      * eapply is_pos_integral_ext; last first.
        { eapply is_pos_integral_scal; auto; last apply Hpos2.
          intros x => //=. apply Rmax_r. }
        intros x => //=.
        replace 0 with (k * 0) at 2 by field.
        rewrite Rmult_comm Rmax_mult; auto.
        f_equal; nra.
      * nra.
    - intros (Hmeas&v1&v2&Hpos1&Hpos2&Hdiff).
      split.
      { by apply measurable_scal. }
      exists (-k * v2), (-k * v1).
      split_and!.
      * eapply is_pos_integral_ext; last first.
        { eapply is_pos_integral_scal; auto; last eauto; try nra.
          intros x => //=. apply Rmax_r. }
        intros x => //=.
        replace 0 with (- k * 0) at 2 by field.
        rewrite Rmult_comm Rmax_mult; auto; last nra.
        f_equal; nra.
      * eapply is_pos_integral_ext; last first.
        { eapply is_pos_integral_scal; auto; last eauto; try nra.
          intros x => //=. apply Rmax_r. }
        intros x => //=.
        replace 0 with (- k * 0) at 2 by field.
        rewrite Rmult_comm Rmax_mult; auto; last nra.
        f_equal; nra.
      * nra.
  Qed.

  Lemma ex_integral_scal k f:
    ex_integral f →
    ex_integral (λ x, k * f x).
  Proof.
    intros (v1&?); eexists; eapply is_integral_scal; eauto.
  Qed.

  Lemma Integral_scal k f:
    ex_integral f →
    Integral (λ x, k * f x) = k * Integral f.
  Proof.
    intros Hex.
    apply is_integral_unique.
    apply is_integral_scal; apply Integral_correct; eauto.
  Qed.

  Lemma is_integral_plus f1 v1 f2 v2:
    is_integral f1 v1 →
    is_integral f2 v2 →
    is_integral (λ x, f1 x + f2 x) (v1 + v2).
  Proof.
    intros Hi1 Hi2.
    destruct Hi1 as (Hmeas1&v1p&v1n&Hi1p&Hi1n&Hdiff1).
    destruct Hi2 as (Hmeas2&v2p&v2n&Hi2p&Hi2n&Hdiff2).
    split.
    - apply measurable_plus; auto.
    - exists (Pos_integral (λ x, (Rmax (f1 x + f2 x) 0))).
      exists (Pos_integral (λ x, (Rmax (-(f1 x + f2 x)) 0))).
      assert (ex_pos_integral (λ x, (Rmax (f1 x + f2 x) 0))).
      {
        edestruct (is_pos_integral_mono_ex μ
                     (λ x, Rmax (f1 x + f2 x) 0)
                     (λ x, Rmax (f1 x) 0 + Rmax (f2 x) 0)) as (Hex&?); eauto.
        ** intros x => //=. apply Rmax_r.
        ** intros x => //=. repeat apply Rmax_case_strong; nra.
        ** apply measurable_Rmax.
           *** apply measurable_plus; auto.
           *** eapply measurable_const.
        ** apply is_pos_integral_plus; eauto using Rmax_r.
      }
      assert (ex_pos_integral (λ x, (Rmax (- (f1 x + f2 x)) 0))).
      {
        edestruct (is_pos_integral_mono_ex μ
                     (λ x, Rmax (- (f1 x + f2 x)) 0)
                     (λ x, Rmax (- f1 x) 0 + Rmax (- f2 x) 0)) as (Hex&?); eauto.
        ** intros x => //=. apply Rmax_r.
        ** intros x => //=. repeat apply Rmax_case_strong; nra.
        ** apply measurable_Rmax.
           *** eapply measurable_opp. apply measurable_plus; auto.
           *** eapply measurable_const.
        ** apply is_pos_integral_plus; eauto using Rmax_r.
      }
      split_and!.
      * apply Pos_integral_correct; eauto.
      * apply Pos_integral_correct; eauto.
      * replace (v1 + v2) with ((v1p + v2p) - (v1n + v2n)) by nra.
        eapply (is_pos_integral_diff (λ x, Rmax (f1 x) 0 + Rmax (f2 x) 0)
                                     (λ x, Rmax (- f1 x) 0 + Rmax (- f2 x) 0));
          try (eapply Pos_integral_correct; eauto);
          try (intros x; eapply Rmax_r; eauto).
        ** intros; repeat apply Rmax_case_strong; nra.
        ** intros; repeat apply Rmax_case_strong; nra.
        ** intros; repeat apply Rmax_case_strong; nra.
        ** apply is_pos_integral_plus; auto using Rmax_r.
        ** apply is_pos_integral_plus; auto using Rmax_r.
  Qed.

  Lemma ex_integral_plus f1 f2:
    ex_integral f1 →
    ex_integral f2 →
    ex_integral (λ x, f1 x + f2 x).
  Proof.
    intros (v1&?) (v2&?).
    eexists; eauto using is_integral_plus.
  Qed.

  Lemma Integral_plus f1 f2:
    ex_integral f1 →
    ex_integral f2 →
    Integral (λ x, f1 x + f2 x) = Integral f1 + Integral f2.
  Proof.
    intros Hex1 Hex2.
    apply is_integral_unique.
    apply is_integral_plus; apply Integral_correct; eauto.
  Qed.


  Lemma is_integral_ext f1 f2 v:
    (∀ x, f1 x = f2 x) →
    is_integral f1 v →
    is_integral f2 v.
  Proof.
    intros Heq (Hmeas&Hp).
    split.
    - eapply measurable_proper.
      * intros x. rewrite -Heq. reflexivity.
      * eauto.
    - destruct Hp as (v1&v2&?&?&?).
      exists v1, v2; split_and!; eauto.
      * setoid_rewrite <-Heq. auto.
      * setoid_rewrite <-Heq. auto.
  Qed.

  Lemma ex_integral_ext f1 f2:
    (∀ x, f1 x = f2 x) →
    ex_integral f1 →
    ex_integral f2.
  Proof.
    intros Hex (v1&?). exists v1. eapply is_integral_ext; eauto.
  Qed.

  Lemma Integral_ext f1 f2:
    (∀ x, f1 x = f2 x) →
    Integral f1 = Integral f2.
  Proof.
    intros Hex. rewrite /Integral. f_equal; apply Pos_integral_ext => x; rewrite Hex; done.
  Qed.

  Global Instance is_integral_Proper:
    Proper (pointwise_relation _ eq ==> eq ==> iff) (is_integral).
  Proof.
    intros ?? Heq ?? ->. split; eapply is_integral_ext; eauto.
  Qed.

  Global Instance ex_integral_Proper:
    Proper (pointwise_relation _ eq ==> iff) (ex_integral).
  Proof.
    intros ?? Heq. split; eapply ex_integral_ext; eauto.
  Qed.

  Global Instance Integral_Proper:
    Proper (pointwise_relation _ eq ==> eq) Integral.
  Proof.
    intros ?? Heq. by apply Integral_ext.
  Qed.

  Lemma is_integral_minus f1 v1 f2 v2:
    is_integral f1 v1 →
    is_integral f2 v2 →
    is_integral (λ x, f2 x - f1 x) (v2 - v1).
  Proof.
    intros Hi1 Hi2.
    assert (Heq: ∀ x, f2 x - f1 x = f2 x + -1 * f1 x) by (intros; nra).
    replace (v2 - v1) with (v2 + - 1 * v1) by field.
    setoid_rewrite Heq.
    apply is_integral_plus; auto.
    apply is_integral_scal. done.
  Qed.

  Lemma ex_integral_minus f1 f2:
    ex_integral f1 →
    ex_integral f2 →
    ex_integral (λ x, f2 x - f1 x).
  Proof.
    intros (v1&?) (v2&?); eexists; eapply is_integral_minus; eauto.
  Qed.

  Lemma Integral_minus f1 f2:
    ex_integral f1 →
    ex_integral f2 →
    Integral (λ x, f1 x - f2 x) = Integral f1 - Integral f2.
  Proof.
    intros Hex1 Hex2.
    apply is_integral_unique.
    apply is_integral_minus; apply Integral_correct; eauto.
  Qed.

  Lemma is_pos_integral_0:
    is_pos_integral (λ _, 0) 0.
  Proof.
    split.
    - apply measurable_const.
    - split.
      * intros ? (wpt&?&?). subst.
        replace 0 with (wpt_integral μ (wpt_const 0)).
        { apply wpt_integral_mono => //=. intros. rewrite wpt_const_spec.
          done. }
        rewrite wpt_integral_const; nra.
      * intros ? H. apply H.
        exists (wpt_const 0); split.
        ** intros; rewrite wpt_const_spec; nra.
        ** rewrite wpt_integral_const; nra.
  Qed.

  Lemma Pos_integral_0:
    Pos_integral (λ _, 0) = 0.
  Proof. apply is_pos_integral_unique, is_pos_integral_0. Qed.

  Hint Resolve is_pos_integral_measurable.

  Lemma is_integral_equiv_pos_integral f v:
    (∀ x, 0 <= f x) →
    is_integral f v ↔ is_pos_integral f v.
  Proof.
    intros Hpos; split.
    - intros (Hmeas&v1&v2&?&Hp2&?).
      cut (v2 = 0).
      { intros. replace v with v1 by nra.
        eapply is_pos_integral_ext; try eassumption.
        intros => //=. rewrite Rmax_left; eauto.
      }
      assert (Heq: ∀ x, Rmax (- f x) 0 = 0).
      { intros. rewrite Rmax_right; auto.
        apply Rge_le, Ropp_0_le_ge_contravar. eauto.
      }
      setoid_rewrite Heq in Hp2.
      erewrite <-(is_pos_integral_unique μ _ v2); eauto.
      apply is_pos_integral_unique. apply is_pos_integral_0.
    - intros Hpos'. split; eauto.
      * exists v, 0; split_and!; last field.
        ** eapply is_pos_integral_ext; last eassumption.
           intros x. rewrite Rmax_left; eauto.
        ** eapply is_pos_integral_ext; last eapply is_pos_integral_0.
           intros x. rewrite Rmax_right; eauto.
           apply Rge_le, Ropp_0_le_ge_contravar. eauto.
  Qed.

  Lemma ex_integral_equiv_pos_integral f:
    (∀ x, 0 <= f x) →
    ex_integral f ↔ ex_pos_integral f.
  Proof.
    intros Hpos. split; intros (v&?); eexists; eapply is_integral_equiv_pos_integral; eauto.
  Qed.

  Lemma Integral_equiv_Pos_integral f:
    (∀ x, 0 <= f x) →
    Integral f = Pos_integral f.
  Proof.
    intros Hpos. rewrite /Integral.
    assert (Hequiv: ∀ x, (λ x, Rmax (- f x) 0) x = 0).
    { intros x. specialize (Hpos x). apply Rmax_case_strong; nra. }
    setoid_rewrite Hequiv. rewrite Pos_integral_0 Rminus_0_r.
    apply Pos_integral_ext.
    intros x. rewrite Rmax_left; auto.
  Qed.

  Lemma is_integral_mono f1 v1 f2 v2:
    (∀ x, f1 x <= f2 x) →
    is_integral f1 v1 →
    is_integral f2 v2 →
    v1 <= v2.
  Proof.
    intros Hle Hint1 Hint2.
    cut (0 <= v2 - v1); first by nra.
    assert (His: is_integral (λ x, f2 x - f1 x) (v2 - v1)).
    { apply is_integral_minus; auto. }
    apply is_integral_equiv_pos_integral in His; last by (intros x; specialize (Hle x); nra).
    eapply is_pos_integral_mono in His; first eassumption; try eapply is_pos_integral_0.
    intros x => //=. specialize (Hle x); nra.
  Qed.

  Lemma Integral_mono f1 f2:
    (∀ x, f1 x <= f2 x) →
    ex_integral f1 →
    ex_integral f2 →
    Integral f1 <= Integral f2.
  Proof.
    intros Hmono (v1&Heq1) (v2&Heq2).
    rewrite (is_integral_unique _ _ Heq1).
    rewrite (is_integral_unique _ _ Heq2).
    eapply is_integral_mono; eauto.
  Qed.

  Lemma is_integral_measurable f v:
    is_integral f v → measurable f.
  Proof. destruct 1; eauto. Qed.

  Lemma ex_integral_measurable f:
    ex_integral f → measurable f.
  Proof. destruct 1 as (?&?); eauto using is_integral_measurable. Qed.

  Hint Resolve is_integral_measurable ex_integral_measurable.

  Lemma is_pos_integral_wpt wpt:
    (∀ x, 0 <= wpt_fun wpt x) →
    is_pos_integral (wpt_fun wpt) (wpt_integral μ wpt).
  Proof.
    intros Hpos.
    eapply (is_pos_integral_mct_wpt μ (λ n, wpt)).
    - apply wpt_fun_measurable.
    - intros; apply is_lim_seq_const.
    - intros; reflexivity.
    - apply is_lim_seq_const.
  Qed.

  Lemma is_integral_wpt wpt:
    is_integral (wpt_fun wpt) (wpt_integral μ wpt).
  Proof.
    induction wpt using wpt_induction.
    - eapply is_integral_ext; eauto.
      rewrite (wpt_integral_proper _ wpt2 wpt1); auto.
        by symmetry.
    - apply is_integral_equiv_pos_integral.
      { intros x. rewrite wpt_indicator_spec; destruct excluded_middle_informative => //=; nra. }
      apply is_pos_integral_wpt.
      { intros x. rewrite wpt_indicator_spec; destruct excluded_middle_informative => //=; nra. }
    - rewrite wpt_integral_plus.
      eapply is_integral_ext.
      { intros x; by rewrite wpt_plus_spec. }
      apply is_integral_plus; eauto.
    - rewrite wpt_integral_scal.
      eapply is_integral_ext.
      { intros x; by rewrite wpt_scal_spec. }
      apply is_integral_scal; eauto.
  Qed.

  Lemma ex_integral_wpt wpt:
    ex_integral (wpt_fun wpt).
  Proof.
    eexists. eapply is_integral_wpt.
  Qed.

  Lemma Integral_wpt wpt:
    Integral (wpt_fun wpt) = wpt_integral μ wpt.
  Proof. apply is_integral_unique, is_integral_wpt. Qed.

  Lemma is_integral_0:
    is_integral (λ _, 0) 0.
  Proof. apply is_integral_equiv_pos_integral; first reflexivity. apply is_pos_integral_0. Qed.

  Lemma Integral_0:
    Integral (λ _, 0) = 0.
  Proof. apply is_integral_unique, is_integral_0. Qed.

  Lemma ex_integral_sum_n fn m:
    (∀ n, (n <= m)%nat → ex_integral (fn n)) →
    ex_integral (λ x, sum_n (λ n, fn n x) m).
  Proof.
    induction m.
    - intros Hex. setoid_rewrite sum_O. eauto.
    - intros Hex. setoid_rewrite sum_Sn. apply ex_integral_plus; auto.
  Qed.

  Lemma Integral_sum_n fn m:
    (∀ n, (n <= m)%nat → ex_integral (fn n)) →
    Integral (λ x, sum_n (λ n, fn n x) m) =
    sum_n (λ n, Integral (fn n)) m.
  Proof.
    induction m.
    - intros Hex. setoid_rewrite sum_O. done.
    - intros Hex. setoid_rewrite sum_Sn. rewrite /plus//=.
      rewrite Integral_plus; eauto using ex_integral_sum_n.
      f_equal; eauto.
  Qed.

  Lemma is_integral_ge0 f v:
    (∀ x, 0 <= f x) →
    is_integral f v →
    v >= 0.
  Proof.
    intros Hpos His.
    apply Rle_ge.
    eapply is_integral_mono.
    - eapply Hpos.
    - apply is_integral_0.
    - eauto.
  Qed.

  Lemma Pos_integral_ge0 f:
    (∀ x, 0 <= f x) →
    Pos_integral f >= 0.
  Proof.
    intros Hpos. rewrite /Pos_integral.
    destruct excluded_middle_informative; last nra.
    destruct excluded_middle_informative; last nra.
    apply Rle_ge. eapply (Rle_trans _ (wpt_integral μ (wpt_indicator empty_set (sigma_empty_set F)))).
    { rewrite wpt_integral_indicator measure_empty. nra. }
    destruct (completeness _) as (?&Hlub).
    apply Hlub. eexists. split; eauto.
    intros x'. rewrite wpt_indicator_spec. destruct (excluded_middle_informative) as [[]|]; auto.
  Qed.

  Lemma Integral_ge0 f:
    (∀ x, 0 <= f x) →
    Integral f >= 0.
  Proof.
    intros Hpos.
    rewrite /Integral. cut (Pos_integral (λ x, Rmax (- f x) 0) = 0).
    { intros ->. feed pose proof (Pos_integral_ge0 (λ x, Rmax (f x) 0)).
      { intros. apply Rmax_case_strong; nra. }
      nra.
    }
    rewrite -{2}Pos_integral_0. apply Pos_integral_ext. intros.
    specialize (Hpos x). apply Rmax_case_strong => //=; nra.
  Qed.

  Hint Resolve is_integral_wpt ex_integral_wpt.

  Lemma ex_integral_mono_ex f1 f2:
    (∀ x, Rabs (f1 x) <= f2 x) →
    measurable f1 →
    ex_integral f2 →
    ex_integral f1.
  Proof.
    intros Hb Hmeas (v&(?&?&?&?&?&?)).
    edestruct (is_pos_integral_mono_ex μ (λ x, Rmax (f1 x) 0) (λ x, Rmax (f2 x) 0)) as ((xp&?)&?).
    { intros ?; apply Rmax_case_strong; nra. }
    { intros x' => //=. specialize (Hb x'). move: Hb.
      apply Rabs_case; do 2 apply Rmax_case_strong; nra. }
    { apply measurable_Rmax; eauto. measurable. }
    { eauto.  }

    edestruct (is_pos_integral_mono_ex μ (λ x, Rmax (- f1 x) 0) (λ x, Rmax (f2 x) 0)) as ((xn&?)&?).
    { intros ?; apply Rmax_case_strong; nra. }
    { intros x' => //=. generalize (Hb x').
      apply Rabs_case; do 2 apply Rmax_case_strong; nra. }
    { apply measurable_Rmax; eauto; measurable. }
    { eauto.  }
    exists (xp - xn).
    split; auto. exists xp, xn.
    eauto.
  Qed.

  Lemma ex_integral_Rabs f:
    measurable f →
    ex_integral f ↔ ex_integral (λ x, Rabs (f x)).
  Proof.
    intros Hmeas.
    split.
    - intros (v&Hmeas'&(v1&v2&His1&His2&Heq)).
      assert (∀ x, Rabs (f x) = Rmax (f x) 0 + Rmax (- f x) 0) as Hequiv.
      { intros; apply Rabs_case; do 2 apply Rmax_case_strong; nra. }
      setoid_rewrite Hequiv.
      apply ex_integral_plus.
      * apply ex_integral_equiv_pos_integral; last by eexists; eauto.
        intros. apply Rmax_case_strong; nra.
      * apply ex_integral_equiv_pos_integral; last by eexists; eauto.
        intros. apply Rmax_case_strong; nra.
    - intros. eapply ex_integral_mono_ex; eauto.
      intros x. rewrite //=. reflexivity.
  Qed.

  Lemma Integral_mono_pos f1 f2:
    (∀ x, 0 <= f1 x) →
    (∀ x, f1 x <= f2 x) →
    measurable f1 →
    ex_integral f2 →
    Integral f1 <= Integral f2.
  Proof.
    intros Hpos Hmono Hmeas Hex. eapply Integral_mono; eauto.
    eapply ex_integral_mono_ex. eauto.
    { intros. rewrite Rabs_right; eauto. }
    { auto. }
    { auto. }
  Qed.

  Lemma is_integral_wpt_ae_0 wpt:
    (∀ x, 0 <= wpt_fun wpt x) →
    almost_everywhere_meas μ (λ x, wpt_fun wpt x = 0) →
    is_integral (wpt_fun wpt) 0.
  Proof.
    intros Hpos.
    eapply (wpt_pos_induction
        (λ wpt, almost_everywhere_meas μ (λ x : A, wpt_fun wpt x = 0) → is_integral (wpt_fun wpt) 0)).
    - intros wpt1 wpt2 Heq IH Hae.
      eapply is_integral_ext; last eapply IH; eauto.
      eapply almost_everywhere_meas_ext; eauto.
      intros ?. by rewrite Heq.
    - intros U Hmeas Hae.  cut (Integral (wpt_fun (wpt_indicator U Hmeas)) = 0).
      { intros <-. apply Integral_correct; auto. }
      rewrite Integral_wpt wpt_integral_indicator.
      destruct Hae as (?&His0).
      apply Rle_antisym; last by apply Rge_le, measure_nonneg.
      rewrite -His0. apply measure_mono; auto.
      intros x HU Hneg. rewrite wpt_indicator_spec in Hneg.
      destruct (excluded_middle_informative); try contradiction. simpl in Hneg; nra.
    - intros wpt1 wpt2 Hpos1 IH1 Hpos2 IH2 Hae.
      replace 0 with (0 + 0) by nra.
      eapply is_integral_ext.
      { intros x; by rewrite wpt_plus_spec. }
      apply is_integral_plus.
      * eapply IH1. eapply almost_everywhere_meas_mono; eauto.
        { apply measurable_fun_eq_0; auto. }
        intros x. rewrite wpt_plus_spec. specialize (Hpos1 x). specialize (Hpos2 x).
        nra.
      * eapply IH2. eapply almost_everywhere_meas_mono; eauto.
        { apply measurable_fun_eq_0; auto. }
        intros x. rewrite wpt_plus_spec. specialize (Hpos1 x). specialize (Hpos2 x).
        nra.
    - intros k wpt1 Hkpos Hpos1 IH1 Hae.
      replace 0 with (k * 0) by field.
      eapply is_integral_ext.
      { intros x. rewrite wpt_scal_spec. done. }
      destruct Hkpos; last first.
      { subst. setoid_rewrite Rmult_0_l. apply is_integral_0. }
      apply is_integral_scal.
      eapply IH1. eapply almost_everywhere_meas_mono; eauto.
        { apply measurable_fun_eq_0; auto. }
      intros x. rewrite wpt_scal_spec. nra.
    - auto.
  Qed.

  Lemma is_integral_pos_ae_0 f:
    measurable f →
    (∀ x, 0 <= f x) →
    almost_everywhere_meas μ (λ x, f x = 0) →
    is_integral f 0.
  Proof.
    intros Hmeas Hpos.
    edestruct (wpt_approx_measurable _ Hpos Hmeas) as (wptn&?&?&Hle&Hposn).
    intros Hae. apply is_integral_equiv_pos_integral; eauto.
    eapply is_pos_integral_mct_wpt; eauto.
    eapply is_lim_seq_ext; last eapply is_lim_seq_const.
    intros n => //=. rewrite -Integral_wpt. symmetry.
    apply is_integral_unique. apply is_integral_wpt_ae_0; eauto.
    eapply almost_everywhere_meas_mono; eauto.
    { apply measurable_fun_eq_0; auto. }
    intros x Heq0. specialize (Hle n x). specialize (Hposn n x). nra.
  Qed.

  Lemma is_integral_alt (f: A → R) v :
    (measurable f ∧
    ∃ v1 v2, is_integral (λ x, Rmax (f x) 0) v1 ∧
             is_integral (λ x, Rmax (- f x) 0) v2 ∧
             v = v1 - v2) ↔ is_integral f v.
  Proof.
    split.
    - intros (?&v1&v2&?&?&?).
      split; auto. exists v1, v2.
      split_and!; auto; apply is_integral_equiv_pos_integral; eauto;
        intros x; apply Rmax_case_strong; nra.
    - intros (Hmeas&(v1&v2&?&?&?)). split; auto.
      exists v1, v2; split_and!; auto.
      * apply is_integral_equiv_pos_integral; auto using Rmax_r.
      * apply is_integral_equiv_pos_integral; auto using Rmax_r.
  Qed.

  Lemma ex_integral_alt (f: A → R) :
    (measurable f ∧
     ex_integral (λ x, Rmax (f x) 0) ∧
     ex_integral (λ x, Rmax (- f x) 0))
    ↔ ex_integral f.
  Proof.
    split.
    - intros (Hmeas&Hex1&Hex2).
      destruct Hex1 as (v1&His1). destruct Hex2 as (v2&His2).
      exists (v1 - v2). apply is_integral_alt.
      split; auto.
      exists v1, v2; split_and!; eauto.
    - intros (Hmeas&His).
      apply is_integral_alt in His as (?&?&?&?&?&?).
      split; auto. split; eexists; eauto.
  Qed.

  Lemma Integral_alt f:
    Integral f = Integral (λ x, Rmax (f x) 0) - Integral (λ x, Rmax (- f x) 0).
  Proof.
    rewrite {1}/Integral; f_equal; symmetry; apply Integral_equiv_Pos_integral; auto using Rmax_r.
  Qed.

  Lemma is_integral_ae_0 f:
    measurable f →
    almost_everywhere_meas μ (λ x, f x = 0) →
    is_integral f 0.
  Proof.
    intros Hmeas Hae. apply is_integral_alt; split; auto.
    exists 0, 0; split_and!; last field.
    - apply is_integral_pos_ae_0.
      * apply measurable_Rmax; measurable.
      * intros; apply Rmax_case_strong; nra.
      * eapply almost_everywhere_meas_mono; eauto.
        ** apply measurable_fun_eq_0; auto.
           apply measurable_Rmax; measurable.
        ** intros x ->. apply Rmax_case_strong; auto.
    - apply is_integral_pos_ae_0.
      * apply measurable_Rmax; measurable.
      * intros; apply Rmax_case_strong; nra.
      * eapply almost_everywhere_meas_mono; eauto.
        ** apply measurable_fun_eq_0; auto.
           apply measurable_Rmax; measurable.
        ** intros x ->. apply Rmax_case_strong; auto. nra.
  Qed.

  Lemma is_integral_ae_ext f1 f2 v:
    almost_everywhere_meas μ (λ x, f1 x = f2 x) →
    measurable f2 →
    is_integral f1 v →
    is_integral f2 v.
  Proof.
    intros Hae Hmeas His.
    feed pose proof (is_integral_ae_0 (λ x, f2 x - f1 x)) as Hisdiff.
    { measurable. eauto. }
    { eapply almost_everywhere_meas_ext; eauto. split; intros; nra. }
    specialize (is_integral_plus _ _ _ _ His Hisdiff).
    rewrite Rplus_0_r. apply is_integral_ext. intros; field.
  Qed.

  Lemma ex_integral_ae_ext f1 f2:
    almost_everywhere_meas μ (λ x, f1 x = f2 x) →
    measurable f2 →
    ex_integral f1 →
    ex_integral f2.
  Proof.
    intros Hae Hmeas (v&His). exists v. eapply is_integral_ae_ext; eauto.
  Qed.

  Lemma Integral_ae_ext_weak f1 f2:
    almost_everywhere_meas μ (λ x, f1 x = f2 x) →
    measurable f2 →
    ex_integral f1 →
    Integral f1 = Integral f2.
  Proof.
    intros Hae ? Hex. symmetry. apply is_integral_unique.
    eapply is_integral_ae_ext; eauto.
    by apply Integral_correct.
  Qed.


  Lemma is_integral_levi_pos_ex fn f:
    measurable f →
    (∀ x, is_lim_seq (λ n, fn n x) (f x : R)) →
    (∀ x, ∀ n, 0 <= fn n x) →
    (∀ x, ∀ n, fn n x <= fn (S n) x) →
    (∀ n, ex_integral (fn n)) →
    bound (λ r, ∃ n, is_integral (fn n) r) →
    ex_integral f ∧ is_lim_seq (λ n, Integral (fn n)) (Integral f).
  Proof.
    intros Hmeas Hlim Hpos Hmono Hint_fn Hbounded_int.
    assert (Hfpos: ∀ x, 0 <= f x).
    { intros x. eapply is_lim_seq_pos; eauto.
      intros n. apply Rle_ge; eauto. }
    assert (Hfn_bounded_fpos: ∀ n x, fn n x <= f x).
    { intros n x.
      apply: (is_lim_seq_incr_compare (λ n, fn n x) (f x)); eauto.
    }
    assert (Hfn_meas: ∀ n, measurable (fn n)).
    { intros n. auto. }
    set (gnk_wit := λ n, constructive_indefinite_description _
                    (wpt_approx_measurable (fn n) (λ x, Hpos x n) (Hfn_meas n))).
    set (gnk := λ n, sval (gnk_wit n)).
    set (hnk := λ n k, nat_rect (λ _, weighted_partition)
                                (wpt_const 0)
                                (λ m w, wpt_max w (gnk m n)) (S k)).
    set (hn := λ n, hnk n n).
    assert (Hhnk_mono1: ∀ n k, ∀ x, wpt_fun (hnk n k) x <= wpt_fun (hnk (S n) k) x).
    {
      intros n k x. revert n. rewrite /hnk. generalize (wpt_const 0).  generalize (S k); clear k.
      intros k. induction k => //= w n.
      - reflexivity.
      - rewrite ?wpt_max_spec. apply Rmax_le_compat.
        * eapply IHk.
        * rewrite /gnk/gnk_wit. destruct constructive_indefinite_description as (?&?&?&?); eauto.
    }
    assert (Hhnk_mono2: ∀ n k, ∀ x, wpt_fun (hnk n k) x <= wpt_fun (hnk n (S k)) x).
    {
      intros n k x. revert n. rewrite /hnk. generalize (wpt_const 0).  generalize (S k); clear k.
      intros k. induction k => //= w n.
      - rewrite wpt_max_spec. apply Rmax_l.
      - rewrite ?wpt_max_spec. apply Rmax_l.
    }
    assert (Hhnk_mono: ∀ n k, (∀ n' k', (n' <= n)%nat → (k' <= k)%nat →
                                        ∀ x, wpt_fun (hnk n' k') x <= wpt_fun (hnk n k) x)).
    { intros n k n' k' Hle1 Hle2.
      revert k' k Hle2. induction Hle1.
      * intros. induction Hle2.
        ** reflexivity.
        ** etransitivity; first eauto. eapply Hhnk_mono2.
      * intros. etransitivity; first eapply IHHle1; eauto.
    }
    assert (Hhnk_gnk: ∀ n k, ∀ x, wpt_fun (gnk k n) x <= wpt_fun (hnk n k) x).
    { intros. rewrite wpt_max_spec. apply Rmax_r. }
    assert (Hhnk_ub: ∀ n k, (∀ n' k', (n' <= n)%nat → (k' <= k)%nat →
                                   ∀ x, wpt_fun (gnk k' n') x <= wpt_fun (hnk n k) x)).
    { intros ???? Hle1 Hle2 x. etransitivity; first eapply Hhnk_gnk.
      apply Hhnk_mono; eauto. }
    assert (Hgnk_bounded_fn: ∀ n k, ∀ x, wpt_fun (gnk n k) x <= fn n x).
    { rewrite /gnk/gnk_wit => n k x.
      destruct constructive_indefinite_description as (?&?&?&Hbn&?) => //=.
    }
    assert (Hgnk_bounded_f: ∀ n k, ∀ x, wpt_fun (gnk n k) x <= f x).
    { intros. transitivity (fn n x); eauto. }
    assert (Hhnk_bounded_fn: ∀ n k, ∀ x, wpt_fun (hnk n k) x <= fn k x).
    { intros n k x. rewrite /hnk.
      assert (Hle: ∀ k, wpt_fun (wpt_const 0) x <= fn k x).
      { rewrite wpt_const_spec. eauto. }
      rewrite //=. rewrite wpt_max_spec.
      apply Rmax_lub; last by eauto.
      revert Hle. generalize (wpt_const 0).
      induction k => //=.
      - intros w Hle.
        rewrite wpt_max_spec. apply Rmax_lub; eauto.
        etransitivity; first eapply IHk; eauto.
        transitivity (fn k x); eauto.
    }
    assert (Hhnk_bounded_f: ∀ n k, ∀ x, wpt_fun (hnk n k) x <= f x).
    { intros. transitivity (fn k x); eauto. }
    assert (∀ n x, 0 <= wpt_fun (hn n) x ).
    { rewrite /hn. etransitivity; last eapply Hhnk_gnk.
      rewrite /gnk. destruct (gnk_wit) as (?&?&?&?&?); eauto.
    }
    edestruct (is_pos_integral_mct_wpt_ex μ hn f).
    { auto. }
    { intros x P => //= Hloc.
      destruct Hloc as (eps&Heps).
      edestruct (Hlim x (ball (f x) (pos_div_2 eps))) as (n1&Hn1).
      { rewrite //=. apply (locally_ball _ (pos_div_2 eps)). }
      destruct (proj2_sig (gnk_wit n1)) as (Hlb&Hlim_gnk&Hbounded_gnk&?).
      destruct (Hlim_gnk x (ball (fn n1 x) (pos_div_2 (pos_div_2 eps)))) as (n2&Hn2).
      { rewrite //=. apply (locally_ball _ (pos_div_2 (pos_div_2 eps))). }
      exists (max n1 n2).
      intros n Hge.
      apply Heps.
      rewrite /ball//=/AbsRing_ball/abs/minus/plus/opp//=.
      rewrite Rabs_left1; last first.
      { rewrite /hn. specialize (Hhnk_bounded_f n n x); eauto. nra. }

      feed pose proof (Hn1 n1) as Hn1'.
      { etransitivity; last eauto. reflexivity. }
      rewrite /ball//=/AbsRing_ball/abs/minus/plus/opp//= in Hn1'.
      rewrite Rabs_left1 in Hn1'; last first.
      { specialize (Hfn_bounded_fpos n1 x). nra. }

      feed pose proof (Hn2 n) as Hn2'.
      { etransitivity; last eauto. apply Nat.le_max_r. }
      rewrite /ball//=/AbsRing_ball/abs/minus/plus/opp//= in Hn2'.
      rewrite Rabs_left1 in Hn2'; last first.
      { specialize (Hbounded_gnk n x). nra.  }


      specialize (Hbounded_gnk n x).
      specialize (Hgnk_bounded_f n n x).
      rewrite /gnk in Hgnk_bounded_f.
      specialize (Hhnk_bounded_f n n x).
      feed pose proof (Hhnk_ub n n n n1) as Hhn_ub.
      { reflexivity. }
      { etransitivity; last eauto. apply Nat.le_max_l. }
      specialize (Hhn_ub x). rewrite /hn. rewrite /gnk in Hhn_ub.
      destruct eps as (eps&hgt0) => //=.
      rewrite //= in Hn1' Hn2'.
      nra.
    }
    { eauto.  }
    { destruct Hbounded_int as (v&Hspec).
      exists v. intros r (n&<-).
      transitivity (Integral (fn n)); first eapply (is_integral_mono (λ x, wpt_fun (hn n) x) _ (fn n));
        last eauto.
      - intros x. rewrite /hn. eauto.
      - eapply is_integral_equiv_pos_integral; eauto.
        eapply is_pos_integral_wpt; eauto.
      - apply Integral_correct; eauto.
      - eapply Hspec. exists n; eauto using Integral_correct.
    }
    split.
    * apply ex_integral_equiv_pos_integral; eauto.
    * rewrite Integral_equiv_Pos_integral; eauto.
      apply (is_lim_seq_le_le (λ n, wpt_integral μ (hn n)) _ (λ n, Pos_integral f)); first split; eauto.
      { eapply (is_integral_mono (wpt_fun (hn n)) _ (fn n) _).
        * eauto.
        * apply is_integral_equiv_pos_integral; eauto.
          eapply is_pos_integral_wpt; eauto.
        * apply Integral_correct. eauto.
      }
      rewrite Integral_equiv_Pos_integral; eauto.
      eapply (is_pos_integral_mono μ (fn n) f); eauto.
      ** apply Pos_integral_correct.
         apply ex_integral_equiv_pos_integral; eauto.
      ** by apply Pos_integral_correct.
      ** apply is_lim_seq_const.
  Qed.

  Lemma is_integral_levi_ex fn f:
    measurable f →
    (∀ x, is_lim_seq (λ n, fn n x) (f x : R)) →
    (∀ x, ∀ n, fn n x <= fn (S n) x) →
    (∀ n, ex_integral (fn n)) →
    bound (λ r, ∃ n, is_integral (fn n) r) →
    ex_integral f ∧ is_lim_seq (λ n, Integral (fn n)) (Integral f).
  Proof.
    intros Hmeas Hlim Hmono Hex Hbounded_int.
    set (fn' := λ n x, fn n x - fn O x).
    set (f' := λ x, f x - fn O x).
    assert (∀ n : nat, ex_integral (fn' n)).
    { intros n. rewrite /fn'. apply ex_integral_minus; eauto. }
    edestruct (is_integral_levi_pos_ex fn' f').
    - rewrite /f'. apply measurable_minus; eauto.
    - rewrite /fn'/f' => x. eapply is_lim_seq_minus; eauto.
      * apply is_lim_seq_const.
      * rewrite //=.
    - intros x n. rewrite /fn'.
      cut (fn O x <= fn n x); first nra.
      clear -Hmono; induction n.
      * nra.
      * etransitivity; eauto.
    - rewrite /fn'; intros; apply Rplus_le_compat; eauto. reflexivity.
    - intros n. rewrite /fn'. apply ex_integral_minus; eauto.
    - destruct Hbounded_int as (v&Hbound).
      exists (v - Integral (fn O)).
      intros r (n&His).
      rewrite /fn' in His.
      assert (r = Integral (λ x, fn n x - fn O x)) as ->.
      { symmetry. apply is_integral_unique; eauto. }
      rewrite Integral_minus; eauto.
      cut (Integral (fn n) <= v); first by nra.
      eapply Hbound. exists n. apply Integral_correct; eauto.
    - assert (Hext: ∀ x : A, f' x + fn O x = f x).
      { rewrite /f' => x. nra. }
      assert (Hextn: ∀ n x, fn' n x + fn O x = fn n x).
      { rewrite /fn' => n x. nra. }
      assert (ex_integral f).
      {  eapply (ex_integral_ext (λ x, f' x + fn O x)); eauto.
         apply ex_integral_plus; eauto. }
      split; auto.
      * eapply is_lim_seq_ext.
        { intros n. apply Integral_ext; first eapply Hextn. }
        eapply is_lim_seq_ext.
        ** intros n. rewrite Integral_plus; eauto.
        ** rewrite -(Integral_ext _ _ Hext); auto using ex_integral_plus.
           rewrite Integral_plus; eauto.
           eapply is_lim_seq_plus; eauto.
           { apply is_lim_seq_const. }
           rewrite //=.
  Qed.

  Lemma ae_equal_mult_indicator_compl_0:
    ∀ f U Hmeas, measurable f → μ (compl U) = 0 →
                 almost_everywhere_meas μ (λ x, f x * wpt_fun (wpt_indicator U Hmeas) x = f x).
  Proof.
    intros g U Hmeas Hmeasg Heq0.
    eapply almost_everywhere_meas_mono; last first.
    { split; eauto.  }
    { intros x. rewrite wpt_indicator_spec.
      intros. destruct excluded_middle_informative.
      * rewrite Rmult_1_r. done.
      * contradiction.
    }
    { apply measurable_fun_eq_inv; measurable. }
  Qed.

  Lemma ae_equal_mult_indicator_compl_0':
    ∀ f U Hmeas, measurable f → μ (compl U) = 0 →
                 almost_everywhere_meas μ (λ x, f x = f x * wpt_fun (wpt_indicator U Hmeas) x).
  Proof.
    intros.
    eapply almost_everywhere_meas_ext; last eapply ae_equal_mult_indicator_compl_0; try eassumption.
    intros x. split; by symmetry; eauto.
  Qed.

  Lemma is_integral_levi_ae_ex fn f:
    measurable f →
    almost_everywhere_meas μ (λ x, is_lim_seq (λ n, fn n x) (f x : R)) →
    almost_everywhere_meas μ (λ x, ∀ n, fn n x <= fn (S n) x) →
    (∀ n, ex_integral (fn n)) →
    bound (λ r, ∃ n, is_integral (fn n) r) →
    ex_integral f ∧ is_lim_seq (λ n, Integral (fn n)) (Integral f).
  Proof.
    generalize ae_equal_mult_indicator_compl_0 => Hae.
    intros Hmeas Hlim Hmono Hex Hbound.
    specialize (almost_everywhere_meas_conj μ _ _ Hlim Hmono).
    intros (HF&Hμ0).
    apply sigma_closed_complements in HF.
    rewrite compl_involutive in HF * => HF.
    feed pose proof (is_integral_levi_ex (λ n, λ x, fn n x * wpt_fun (wpt_indicator _ HF) x)
                                         (λ x, f x * wpt_fun (wpt_indicator _ HF) x))
         as Hlevi.
    { measurable. }
    { intros x. setoid_rewrite wpt_indicator_spec.
      destruct excluded_middle_informative as [(Hlim'&?)|Hnotin].
      * setoid_rewrite Rmult_1_r. eauto.
      * setoid_rewrite Rmult_0_r. apply is_lim_seq_const.
    }
    { intros x n. rewrite wpt_indicator_spec.
      destruct excluded_middle_informative as [(Hlim'&?)|Hnotin].
      * setoid_rewrite Rmult_1_r. eauto.
      * setoid_rewrite Rmult_0_r. reflexivity.
    }
    { intros n. eapply ex_integral_ae_ext; eauto.
      { eapply almost_everywhere_meas_ext; last eapply ae_equal_mult_indicator_compl_0.
        * intros ?; split; symmetry; eauto.
        * measurable.
        * eauto.
      }
      measurable.
    }
    { destruct Hbound as (r&Hub). exists r.
      intros ? (n&His). eapply is_integral_ae_ext in His; auto.
      eapply Hub; eauto. }
    destruct Hlevi as (Hlevi_ex&Hlevi_lim).
    assert (ex_integral f).
    { eapply ex_integral_ae_ext; eauto. eapply ae_equal_mult_indicator_compl_0; measurable. }
    split; auto.
    setoid_rewrite <-(Integral_ae_ext_weak) in Hlevi_lim; eauto.
    { eapply is_lim_seq_ext; last eauto.
      intros n => //=.
      symmetry. apply Integral_ae_ext_weak; eauto.
      { eapply almost_everywhere_meas_ext; last eapply ae_equal_mult_indicator_compl_0.
        * intros ?; split; symmetry; eauto.
        * measurable.
        * eauto.
      }
      measurable.
    }
    { eapply almost_everywhere_meas_ext; last eapply ae_equal_mult_indicator_compl_0.
      * intros ?; split; symmetry; eauto.
      * measurable.
      * eauto.
    }
  Qed.

  Lemma is_integral_mct_ex fn f g:
    measurable f →
    (∀ x, is_lim_seq (λ n, fn n x) (f x : R)) →
    (∀ x, ∀ n, fn n x <= fn (S n) x) →
    (∀ x, ∀ n, Rabs (fn n x) <= g x) →
    (∀ n, ex_integral (fn n)) →
    ex_integral g →
    ex_integral f ∧ is_lim_seq (λ n, Integral (fn n)) (Integral f).
  Proof.
    intros Hmeas Hlim Hmono Hbounded Hex Hexg.
    edestruct (is_integral_levi_ex fn f); eauto.
    destruct Hexg as (v&Hisg).
    exists v.
    intros r (n&His).
    eapply (is_integral_mono (fn n) _ g); eauto.
    intros. specialize (Hbounded x n). move: Hbounded.
    apply Rabs_case; nra.
  Qed.


  Lemma is_integral_const k :
    is_integral (λ _, k) (k * μ (λ _, True)).
  Proof.
    setoid_rewrite <-(wpt_const_spec k) at 1.
    rewrite -wpt_integral_const.
    apply is_integral_wpt.
  Qed.

  Lemma ex_integral_const k :
    ex_integral (λ _, k).
  Proof. eexists. apply is_integral_const. Qed.

  Lemma Integral_const k :
    Integral (λ _, k) = (k * μ (λ _, True)).
  Proof.
    apply is_integral_unique, is_integral_const.
  Qed.

  Lemma measurable_non_ex_pos_integral_0 f:
    measurable f →
    ¬ ex_pos_integral f →
    Pos_integral f = 0.
  Proof.
    intros Hmeas Hnex. rewrite /Pos_integral.
    destruct excluded_middle_informative; auto.
    destruct excluded_middle_informative; auto.
    exfalso; apply Hnex; apply measurable_bounded_simple_ex_pos_integral; eauto.
  Qed.

  Lemma Integral_pos_mct fn f:
    measurable f →
    (∀ x, is_lim_seq (λ n, fn n x) (f x : R)) →
    (∀ x, ∀ n, 0 <= fn n x) →
    (∀ x, ∀ n, fn n x <= fn (S n) x) →
    (∀ n, ex_integral (fn n)) →
    real (Lim_seq (λ n, Integral (fn n))) = Integral f.
  Proof.
    intros Hmeas Hlim Hpos Hmono Hex.
    destruct (Classical_Prop.classic (bound (λ r, ∃ n, is_integral (fn n) r))) as [Hbound|Hunbounded].
    { feed pose proof (is_integral_levi_ex fn f) as Hlevi; eauto.
      destruct Hlevi as (Hex_f&Hlim_int).
      apply is_lim_seq_unique in Hlim_int. rewrite Hlim_int. done. }
    transitivity 0.
    - cut (Lim_seq (λ n, Integral (fn n)) = p_infty).
      { intros ->. done. }
      apply is_lim_seq_unique.
      intros P Hlocal. rewrite /Rbar_locally in Hlocal.
      destruct Hlocal as (K&HK).
      assert (∃ n, K < Integral (fn n)) as (n&HKn).
      { apply Classical_Prop.NNPP. intros Hnex.
        apply Hunbounded. exists K. intros r (n&Heqr).
        apply Rnot_lt_le. intros Hlt. apply Hnex; exists n.
        apply is_integral_unique in Heqr as ->. done. }
      exists n. intros n' Hge. apply HK.
      eapply Rlt_le_trans; first eauto. clear -Hge Hmono Hex.
      induction Hge; first reflexivity.
      etransitivity; eauto. apply Integral_mono; eauto.
    - symmetry.
      assert (∀ x, 0 <= f x).
      { intros x. eapply is_lim_seq_pos; eauto. eauto. }

      rewrite Integral_equiv_Pos_integral //.

      assert (Hneg: ¬ ex_integral f).
      { intros (v&Hexf). apply Hunbounded.
        exists v. intros r (n&Heq).
        eapply (is_integral_mono (fn n) _ f _).
        - intros x. specialize (Hlim x). eapply is_lim_seq_incr_compare in Hlim; eauto.
        - done.
        - done.
      }
      apply measurable_non_ex_pos_integral_0; auto.
      intros Hex'. apply Hneg. apply ex_integral_equiv_pos_integral; eauto.
  Qed.

  Lemma is_lim_seq_Rmin_pos r:
    0 <= r →
    is_lim_seq (λ n : nat, Rmin r (INR n)) r.
  Proof.
    intros Hle. edestruct archimed_pos as (k&?); eauto.
    intros P Hloc.
    exists (S k) => n Hle'.
    rewrite Rmin_left.
    - rewrite /Rbar_locally/locally in Hloc.
      destruct Hloc as (eps&HP). apply HP. apply ball_center.
    - transitivity (INR (S k)); first nra.
      apply le_INR. done.
  Qed.

  Lemma ex_integral_Rmin f:
    (∀ x, 0 <= f x) →
    measurable f →
    ∀ n, ex_integral (λ x, Rmin (f x) (INR n)).
  Proof.
    { intros Hpos Hmeas n. apply (ex_integral_mono_ex _ (λ x, INR n)).
      { intros x. rewrite Rabs_right; auto. apply Rmin_r.
        apply Rmin_case_strong; auto.
        intros. apply Rle_ge, pos_INR. }
      { apply measurable_Rmin; eauto. apply measurable_const. }
      { apply ex_integral_const. }
    }
  Qed.

  Lemma ex_integral_ex_finite_lim_min f:
    (∀ x, 0 <= f x) →
    measurable f →
    ex_finite_lim_seq (λ n, Integral (λ x, Rmin (f x) (INR n))) ↔
            ex_integral f.
  Proof.
    intros Hpos Hmeas.
    assert (∀ n x, 0 <= Rmin (f x) (INR n)).
    { intros => //=. apply Rmin_case_strong; auto.
      intros. apply pos_INR. }
    generalize (ex_integral_Rmin _ Hpos Hmeas) => ?.
    split.
    - intros Hbounded.
      edestruct (is_integral_levi_pos_ex (λ n, λ x, Rmin (f x) (INR n))); eauto.
      { intros x => //=. eapply is_lim_seq_Rmin_pos; eauto. }
      { intros. apply Rle_min_compat_l. apply le_INR. auto. }
      destruct Hbounded as (r&Hub). exists r. intros z (n&His).
      rewrite -(is_integral_unique _ _ His).
      eapply (is_lim_seq_incr_compare (λ n, Integral (λ x, Rmin (f x) (INR n)))); eauto.
      intros n'. apply Integral_mono; eauto.
      intros x. apply Rle_min_compat_l, le_INR; lia.
    - intros (v&Hex). exists v.
      rewrite -(is_integral_unique _ _ Hex).
      edestruct (is_integral_mct_ex (λ n, (λ x, Rmin (f x) (INR n))) f f); eauto.
      { intros x => //=.
        apply is_lim_seq_Rmin_pos; eauto. }
      { intros. apply Rle_min_compat_l, le_INR; lia. }
      { rewrite //= => ??. apply Rmin_case_strong; intros; rewrite Rabs_right; try nra; eauto.
        apply Rle_ge, pos_INR. }
      eexists; eauto.
  Qed.

  Lemma ex_integral_sup_min f:
    (∀ x, 0 <= f x) →
    measurable f →
    bound (λ r, ∃ n, Integral (λ x, Rmin (f x) (INR n)) = r) ↔
            ex_integral f.
  Proof.
    intros Hpos Hmeas.
    assert (∀ n x, 0 <= Rmin (f x) (INR n)).
    { intros => //=. apply Rmin_case_strong; auto.
      intros. apply pos_INR. }
    generalize (ex_integral_Rmin _ Hpos Hmeas) => ?.
    split.
    - intros Hbounded.
      edestruct (is_integral_levi_pos_ex (λ n, λ x, Rmin (f x) (INR n))); eauto.
      { intros x => //=. eapply is_lim_seq_Rmin_pos; eauto. }
      { intros. apply Rle_min_compat_l. apply le_INR. auto. }
      destruct Hbounded as (r&Hub). exists r. intros z (n&?).
      apply Hub. exists n. apply is_integral_unique; eauto.
    - intros (v&Hex). exists v.
      intros r (n&<-).
      rewrite -(is_integral_unique _ _ Hex).
      apply Integral_mono; eauto.
      intros; apply Rmin_l.
      eexists; eauto.
  Qed.

  Lemma is_integral_bound_measure_above f v t:
    (∀ x, 0 <= f x) →
    is_integral f v →
    0 < t →
    μ (λ x, t <= f x) <= v / t.
  Proof.
    intros Hpos His Htpos.
    apply Rnot_gt_le.
    intros Hgt.
    cut (v < Integral f).
    { intros Hlt. rewrite (is_integral_unique _ _ His) in Hlt. nra. }
    apply (Rlt_le_trans _ (t * (μ (λ x, t <= f x)))).
    { apply (Rmult_lt_reg_r (/t)).
      { apply Rinv_0_lt_compat; nra. }
      { field_simplify; try nra. }
    }
    assert (Hm: F (λ x, t <= f x)).
    { apply measurable_fun_ge. eauto. }
    transitivity (Integral (wpt_fun (wpt_scal t (wpt_indicator _ Hm)))).
    { right. rewrite Integral_wpt wpt_integral_scal wpt_integral_indicator. done. }
    apply Integral_mono; eauto.
    - intros x. rewrite wpt_scal_spec wpt_indicator_spec.
      destruct excluded_middle_informative; auto; simpl; try nra. rewrite Rmult_0_r. eauto.
    - eexists; eauto.
  Qed.

  Lemma Integral_Rabs f:
    (ex_integral f ∨ (measurable f ∧ ex_integral (λ x, Rabs (f x)))) →
    Rabs (Integral f) <= Integral (λ x, (Rabs (f x))).
  Proof.
    intros Hex.
    assert (ex_integral f).
    { destruct Hex; auto. apply ex_integral_Rabs; intuition. }
    assert (ex_integral (λ x, Rabs (f x))).
    { destruct Hex; auto.
      - apply (ex_integral_Rabs f); eauto.
      - intuition.
    }
    apply Rabs_case => ?.
    - apply Integral_mono; eauto. intros. apply Rabs_case; nra.
    - replace (- Integral f) with (-1 * Integral f) by nra.
      rewrite -Integral_scal; eauto.
      apply Integral_mono; eauto.
      * intros. apply Rabs_case; nra.
      * by apply ex_integral_scal.
  Qed.

  Lemma is_integral_ae_ge0 f v:
    almost_everywhere_meas μ (λ x, f x >= 0) →
    is_integral f v →
    v >= 0.
  Proof.
    intros Hae His.
    destruct Hae as (Hmeas&Hmeas0).
    generalize (sigma_closed_complements _ F _ Hmeas). rewrite compl_involutive => HF.
    eapply (is_integral_ae_ext _ (λ x, f x * wpt_fun (wpt_indicator _ HF) x))  in His.
    { eapply is_integral_ge0; eauto. intros. rewrite //= wpt_indicator_spec.
      destruct excluded_middle_informative as [Hc|Hnc]; simpl; nra.
    }
    - eapply ae_equal_mult_indicator_compl_0'; auto.
      eauto.
    - measurable. eauto.
  Qed.

  Lemma is_integral_ae_mono f1 v1 f2 v2:
    almost_everywhere_meas μ (λ x, f1 x <= f2 x) →
    is_integral f1 v1 →
    is_integral f2 v2 →
    v1 <= v2.
  Proof.
    intros Hle Hint1 Hint2.
    cut (0 <= v2 - v1); first by nra.
    assert (His: is_integral (λ x, f2 x - f1 x) (v2 - v1)).
    { apply is_integral_minus; auto. }
    apply is_integral_ae_ge0 in His; first nra.
    eapply almost_everywhere_meas_ext; eauto.
    intros x; split; nra.
  Qed.

  Lemma Integral_ae_mono f1 f2:
    almost_everywhere_meas μ (λ x, f1 x <= f2 x) →
    ex_integral f1 →
    ex_integral f2 →
    Integral f1 <= Integral f2.
  Proof.
    intros Hmono (v1&Heq1) (v2&Heq2).
    rewrite (is_integral_unique _ _ Heq1).
    rewrite (is_integral_unique _ _ Heq2).
    eapply is_integral_ae_mono; eauto.
  Qed.


  Lemma ex_integral_ae_mono_ex f1 f2:
    almost_everywhere_meas μ (λ x, Rabs (f1 x) <= f2 x) →
    measurable f1 →
    ex_integral f2 →
    ex_integral f1.
  Proof.
    intros Hae Hmeas Hex.
    destruct Hae as (Hmeas'&Hneg).
    generalize (sigma_closed_complements _ _ _ Hmeas') => H'.
    setoid_rewrite compl_involutive in H'.
    cut (ex_integral (λ x, f2 x * wpt_fun (wpt_indicator _ H') x)).
    {
      intros Hex_indic.
      assert (Hex': ex_integral (λ x, f1 x * wpt_fun (wpt_indicator _ H') x)).
      { eapply ex_integral_mono_ex; last eapply Hex_indic.
        * intros x => //=.
          rewrite ?wpt_indicator_spec.
          destruct excluded_middle_informative; rewrite ?Rmult_1_r ?Rmult_0_r; try nra.
          rewrite Rabs_right; nra.
        * measurable.
      }
      eapply ex_integral_ae_ext; last eapply Hex'; auto.
      apply ae_equal_mult_indicator_compl_0; eauto.
    }
    eapply ex_integral_ae_ext; eauto.
    { eapply ae_equal_mult_indicator_compl_0'; eauto. }
    measurable.
  Qed.

End integral.

Hint Resolve is_integral_measurable ex_integral_measurable ex_integral_wpt ex_integral_const.

Arguments weighted_partition {_} _.
