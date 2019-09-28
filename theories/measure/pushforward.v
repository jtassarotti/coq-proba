Require Import Reals Psatz Omega Fourier.
From stdpp Require Import tactics list.
From discprob.basic Require Import seq_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.measure Require Export dynkin borel integral isomorphism.
Require Import ClassicalEpsilon.

Section pushforward.
  Context {A1 A2: Type}.
  Context {F1 : sigma_algebra A1}.
  Context {F2 : sigma_algebra A2}.
  Context (μ: measure F1).
  Context (f: A1 → A2).
  Context (Hmeas: measurable f F1 F2).

  Definition pushforward : measure F2.
  Proof.
    refine {| measure_fun := λ U, μ (fun_inv f U) |}.
    - abstract (by intros ?? ->).
    - intros; apply measure_nonneg.
    - abstract (rewrite fun_inv_empty measure_empty //).
    - abstract (intros Us Hin Hdisj;
                rewrite fun_inv_unionF;
                apply measure_additivity;
                  by [ intros; eapply Hmeas | apply fun_inv_disjointF; auto]).
  Defined.
  
  Lemma wpt_hom_aux (wpt: weighted_partition F2):
    ∀ (r : R) (U : A1 → Prop),
      In (r, U) (map (λ rU : R * (A2 → Prop), (rU.1, fun_inv f rU.2)) wpt) → F1 U.
  Proof.
    intros r U Hin. apply in_map_iff in Hin as ((r'&U')&Heq&Hin).
    inversion Heq; subst. eapply Hmeas. 
    by apply In_wpt_snd_measurable in Hin.
  Qed.

  Lemma wpt_hom_spec:
    ∀ wpt2 : weighted_partition F2, ∃ wpt1 : weighted_partition F1,
      ∀ x, wpt_fun wpt2 (f x) = wpt_fun wpt1 x.
  Proof.
    apply wpt_induction.
    - intros wpt1 wpt2 Heq.
      intros (wpt&?). exists wpt => ?. by rewrite -Heq.
    - intros U HmeasU.
      exists (wpt_indicator (fun_inv f U) (Hmeas _ HmeasU)).
      intros. rewrite ?wpt_indicator_spec.
      destruct excluded_middle_informative; eauto.
    - intros wpt1 wpt2 (wpt1'&Heq1') (wpt2'&Heq2').
      exists (wpt_plus wpt1' wpt2'). intros x.
      rewrite ?wpt_plus_spec. rewrite Heq1' Heq2'. done.
    - intros k wpt (wpt'&Heq').
      exists (wpt_scal k wpt'). intros x. rewrite ?wpt_scal_spec Heq'. auto.
  Qed.

  Lemma wpt_hom_fun (wpt: weighted_partition F2): weighted_partition F1.
  Proof.
    specialize (wpt_hom_spec wpt) => Hspec.
    apply constructive_indefinite_description in Hspec as (wpt'&?).
    exact wpt'.
  Defined.

  Lemma wpt_hom_fun_spec wpt: ∀ x, wpt_fun wpt (f x) = wpt_fun (wpt_hom_fun wpt) x.
  Proof.
    intros x.
    rewrite /wpt_hom_fun; destruct constructive_indefinite_description; eauto.
  Qed.

  Lemma wpt_change_of_variables (wpt1: weighted_partition F1) (wpt2: weighted_partition F2):
    (∀ x, wpt_fun wpt2 (f x) = wpt_fun wpt1 x) →
    wpt_integral μ wpt1 = wpt_integral pushforward wpt2.
  Proof.
    revert wpt2 wpt1. 
    eapply (@wpt_induction _ F2 (λ wpt2, ∀ wpt1, (∀ x, wpt_fun wpt2 (f x) = wpt_fun wpt1 x) →
                                wpt_integral μ wpt1 = wpt_integral pushforward wpt2)).
    - intros wpt1 wpt1' Heq Hres1 wpt2 Heq2.
      rewrite Hres1.
      * apply wpt_integral_proper; by symmetry.
      * congruence.
    - intros U HmeasU wpt1 Heq.
      rewrite ?wpt_integral_indicator.
      transitivity (wpt_integral μ (wpt_indicator (fun_inv f U) (Hmeas _ HmeasU))).
      {
        apply wpt_integral_proper.
        intros z. rewrite -Heq ?wpt_indicator_spec //=.
      }
      rewrite wpt_integral_indicator //=.
    - intros wpt1 wpt2 Hspec1 Hspec2 wpt Heq.
      rewrite wpt_integral_plus.
      destruct (wpt_hom_spec wpt1) as (wpt1'&?).
      destruct (wpt_hom_spec wpt2) as (wpt2'&?).
      transitivity (wpt_integral μ (wpt_plus wpt1' wpt2')).
      {
        apply wpt_integral_proper => z. rewrite -Heq. rewrite ?wpt_plus_spec; congruence.
      }
      rewrite wpt_integral_plus; f_equal; eauto.
    - intros k wpt Hspec kwpt Heq.
      destruct (wpt_hom_spec wpt) as (wpt'&?).
      transitivity (wpt_integral μ (wpt_scal k wpt')).
      { 
        apply wpt_integral_proper => z. rewrite -Heq. rewrite ?wpt_scal_spec; congruence.
      }
      rewrite ?wpt_integral_scal; f_equal; eauto.
  Qed.

  Lemma is_pos_integral_change_of_variables (g: A2 → R) (Hmeasg: measurable g F2 (borel _)) v:
    (∀ x, 0 <= g x) →
    is_pos_integral μ (λ x, g (f x)) v ↔ is_pos_integral pushforward g v.
  Proof.
    intros Hpos.
    edestruct (wpt_approx_measurable g Hpos Hmeasg) as (wpt&Hincr&Hlim'&Hbound); eauto.
    split.
    - intros His_pos.
      eapply is_pos_integral_mct_wpt; eauto.
      eapply (is_lim_seq_ext (λ n, wpt_integral μ (wpt_hom_fun (wpt n)))).
      { intros n. apply wpt_change_of_variables. intros x.
        rewrite /wpt_hom_fun. destruct constructive_indefinite_description; eauto.
      }
      eapply (is_pos_integral_mct_wpt' μ (λ n, wpt_hom_fun (wpt n)));
        try eapply His_pos; eauto.
      * intros x. eapply is_lim_seq_ext; last eapply Hlim'.
        intros n => //=. apply wpt_hom_fun_spec.
      * intros x n. rewrite -?wpt_hom_fun_spec; eauto.
    - intros His_pos.
      eapply (is_pos_integral_mct_wpt _ (λ n, wpt_hom_fun (wpt n))); eauto.
      * eapply measurable_comp; eauto.
      * intros x. eapply is_lim_seq_ext; last eapply Hlim'.
        intros n => //=. apply wpt_hom_fun_spec.
      * intros x n. rewrite -?wpt_hom_fun_spec; eauto.
      * 
      eapply (is_lim_seq_ext (λ n, wpt_integral pushforward (wpt n))). 
      { intros n. symmetry. apply wpt_change_of_variables. intros x.
        rewrite /wpt_hom_fun. destruct constructive_indefinite_description; eauto.
      }
      eapply is_pos_integral_mct_wpt'; eauto.
  Qed.

  Lemma is_integral_change_of_variables (g: A2 → R) (Hmeasg: measurable g F2 (borel _)) v:
    is_integral μ (λ x, g (f x)) v ↔ is_integral pushforward g v.
  Proof.
    split.
    - rewrite /is_integral. intros (Hmeas'&(v1&v2&Hpos1&Hpos2&Heq)).
      split; eauto. exists v1, v2.
      split_and!; auto.
      * eapply is_pos_integral_change_of_variables; eauto; first measurable.
        intros; apply Rmax_case_strong; nra.
      * eapply is_pos_integral_change_of_variables; eauto; first measurable.
        intros; apply Rmax_case_strong; nra.
    - rewrite /is_integral. intros (Hmeas'&(v1&v2&Hpos1&Hpos2&Heq)).
      split; eauto.
      { eapply measurable_comp; eauto. }
      exists v1, v2.
      split_and!; auto.
      * eapply is_pos_integral_change_of_variables in Hpos1; eauto; first measurable.
        intros; apply Rmax_case_strong; nra.
      * eapply is_pos_integral_change_of_variables in Hpos2; eauto; first measurable.
        intros; apply Rmax_case_strong; nra.
  Qed.

  Lemma Pos_integral_change_of_variables (g: A2 → R) (Hmeasg: measurable g F2 (borel _)):
    (∀ x, 0 <= g x) →
    Pos_integral μ (λ x, g (f x)) = Pos_integral pushforward g.
  Proof.
    intros Hpos.
    destruct (Classical_Prop.classic (∃ v, is_pos_integral pushforward g v)) as [(v&Hex)|Hnex].
    { rewrite (is_pos_integral_unique _ _ _ Hex).
      apply is_pos_integral_unique.
      apply is_pos_integral_change_of_variables; eauto.
    }
    transitivity 0.
    * apply measurable_non_ex_pos_integral_0.
      ** eapply measurable_comp; eauto. 
      ** intros (v&Hex).  eapply Hnex. exists v. apply is_pos_integral_change_of_variables; eauto.
    * symmetry; apply measurable_non_ex_pos_integral_0; eauto.
  Qed.

  Lemma Integral_change_of_variables (g: A2 → R) (Hmeasg: measurable g F2 (borel _)):
    Integral μ (λ x, g (f x)) = Integral pushforward g.
  Proof.
    rewrite /Integral; f_equal.
    * eapply (Pos_integral_change_of_variables (λ x, Rmax (g x) 0)); eauto; first measurable.
      intros; apply Rmax_case_strong; nra.
    * eapply (Pos_integral_change_of_variables (λ x, Rmax (- g x) 0)); eauto; first measurable.
      intros; apply Rmax_case_strong; nra.
  Qed.
    
End pushforward.

Definition measure_restrict {A: Type} (F F': sigma_algebra A) (μ: measure F') (Hle: le_sigma F F'):
  measure F.
Proof.
  apply (pushforward μ id); abstract auto.
Defined.
