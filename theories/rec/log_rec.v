
From discprob.basic Require Import base order nify exp_ext.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.rec Require Import karp quickselect_rec.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From Coquelicot Require Import Derive.
From Coquelicot Require AutoDerive.
Require Import Reals Fourier FunctionalExtensionality.
Require Import Psatz.
Require Import Coq.omega.Omega.
Require Import Ranalysis5.


Module Type rec_factor.
  Parameter alpha : R.
  Parameter alpha_range: 1/2 < alpha < 1.
  Parameter ln_alpha: -/ln alpha > 1/alpha.
End rec_factor.

Module recurrence_log (ALPHA: rec_factor).
  Import ALPHA.
  Definition d := 1.
  Definition umin := 1.

  Definition a x := 
    match Rle_dec x 1 with
      | left _ => 0
      | _ =>
        match Rlt_dec x 2 with
        | left _ => (x - 1)
        | _ => 1
        end
    end.

  Definition m x :=
    match Rlt_dec x (1/alpha) with
      | left _ => 0
      | _ => x * alpha
    end.

  Definition k := -/ ln(alpha).

  Definition u x := 
    match Rle_dec x 1 with 
      | left _ => 1
      | _ => ((k * ln x + 1))
    end.

  Definition u' x :=
    match Rle_dec x 1 with
      | left _ => 1
      | _ => exp ((x - 1) / k)
    end.

  Lemma umin_non_neg: 0 ≤ umin.
  Proof. rewrite /umin; fourier. Qed.

  Lemma Rlt_0_ln x: 1 < x → 0 < ln x.
  Proof.
    intros Hlt; rewrite -ln_1; apply ln_increasing; fourier.
  Qed.

  Lemma one_lt_inv_alpha:
    1 < / alpha.
  Proof.
    generalize (alpha_range), ln_alpha; intros.
    apply (Rmult_lt_reg_l alpha); first nra. field_simplify; nra.
  Qed.

  Lemma kgt1: 1 < k.
  Proof.
    generalize (alpha_range), ln_alpha; intros.
    rewrite /k. 
    transitivity (/ alpha); last auto; try nra.
    apply one_lt_inv_alpha.
  Qed.
  

  Lemma kgt0: 0 < k.
  Proof.
    etransitivity; last apply kgt1. fourier.
  Qed.
  
  Lemma u_mono x y: x ≤ y → u x ≤ u y.
  Proof.
    rewrite /u/a/m/d => Hle.
    destruct (Rle_dec) as [Hle'|Hnle']; try nra;
    destruct (Rle_dec) as [Hle''|Hnle'']; try nra.
    - 
      cut (0 ≤ ln y).
      { 
        intros. generalize kgt1 => ?.
        assert (k * ln y ≥ 0). 
        { transitivity (1 * ln y); last fourier.
          apply Rle_ge, Rmult_le_compat; try fourier.
        }
        fourier.
      }
      left. apply Rlt_0_ln; nra.
    - specialize (kgt0) => Hk.
      apply Rplus_le_compat; last nra.
      cut (ln x ≤ ln y).
      { 
        specialize (kgt0); cut (0 ≤ ln x); intros; first apply Rmult_le_compat; auto; try fourier.
        rewrite -(ln_1). left; apply ln_increasing; nra.
      }
      * inversion Hle; auto; subst; last by nra. left. apply ln_increasing; intros; nra.
  Qed.

  (* This basically covers half the case for the above, so could remove some redundancy *)
  Lemma u_strict_inc x y: x ≥ d → x < y → u x < u y.
  Proof.
    rewrite /u/a/m/d => Hle Hlt.
    destruct (Rle_dec) as [Hle'|Hnle']; try nra;
    destruct (Rle_dec) as [Hle''|Hnle'']; try nra.
    - specialize (kgt0) => Hk.
      assert (0 < k * ln y).
      { 
        apply Rmult_lt_0_compat; first nra.
        apply Rlt_0_ln; fourier.
      }
      rewrite ?Rmult_1_r //=; nra.
    - specialize (kgt0) => Hk.
      apply Rplus_lt_compat_r.
      cut (ln x < ln y).
      { 
        specialize (kgt0); cut (0 < ln x); intros; first apply Rmult_lt_compat_l; auto; try fourier.
        rewrite -(ln_1). apply ln_increasing; nra.
      }
      apply ln_increasing; nra.
  Qed.

  Lemma u'_mono x y: x ≤ y → u' x ≤ u' y.
  Proof.
    rewrite /u'/a/m/d => Hle.
    destruct (Rle_dec) as [Hle'|Hnle']; try nra;
    destruct (Rle_dec) as [Hle''|Hnle'']; try nra.
    - rewrite -{1}exp_0.
      left; apply exp_increasing.
      rewrite /Rdiv. apply Rlt_mult_inv_pos; last apply kgt0. nra.
    - apply exp_increasing_le.
      generalize (kgt0) => Hk.
      apply Rdiv_le_compat_contra; nra.
  Qed.
  
  Lemma u'_pos x: u' x > 0.
  Proof.                      
    rewrite /u'/a/m/d.
    destruct (Rle_dec _); try nra.
    apply exp_pos.
  Qed.

  Lemma u'_inv_above x: d < x → u' (u x) = x.
  Proof.     
    rewrite /u/u'/d.
    destruct (Rle_dec) as [Hc1|Hc1] => //=; try nra;
    destruct (Rle_dec) as [Hc2|Hc2] => //=; try nra.
    - intros. exfalso.
      assert (0 < ln x) by (apply Rlt_0_ln; auto).
      assert (0 < k * ln x) by (apply Rmult_lt_0_compat; auto using kgt0).
      assert (0 < (k * ln x) * (k * ln x)) by (repeat apply Rmult_lt_0_compat; auto using kgt0).
      nra.
    - rewrite -[a in _ = a]exp_ln; last nra.
      intros; do 1 f_equal. 
      assert (0 < ln x) by (apply Rlt_0_ln; auto).
      assert (0 < k * ln x) by (apply Rmult_lt_0_compat; auto using kgt0).
      field. apply Rgt_not_eq, kgt0.
  Qed.

  Lemma u'u x: x ≤ u' (u x).
  Proof.
    destruct (Rlt_dec 1 x) as [Hlt|Hnlt].
    - rewrite u'_inv_above //. reflexivity.
    - rewrite /u/u'.
      apply Rnot_lt_le in Hnlt.
      destruct (Rle_dec) => //=; try nra.
      destruct (Rle_dec) => //=; try nra.
  Qed.
  
  Lemma u_inv_above x: umin < x → u (u' x) = x.
  Proof.
    rewrite /u/u'/umin.
    destruct (Rle_dec) as [Hc1|?] => //=; try nra;
    destruct (Rle_dec) as [?|?] => //=; try nra.
    - exfalso. rewrite -{2}exp_0 in Hc1.
      apply exp_le_embedding in Hc1. 
      specialize (kgt1) => Hk.
      cut (0 < (x - 1) / k). 
      { by intros ?%Rlt_not_le. }
      apply Rdiv_lt_0_compat; nra.
    - rewrite ln_exp. rewrite /Rdiv. intros.
      field. apply Rgt_not_eq, kgt0. 
  Qed.

  Lemma ud_umin: u d = umin.
  Proof.
    rewrite /u/d/umin//=.
    destruct (Rle_dec); nra.
  Qed.
  
  Lemma u_cont: continuity u.
  Proof.
    apply piecewise_continuity' with (g := λ x, (k * ln x + 1))
                                      (f := λ x, 1) (z := 1).
    - intros; apply continuity_const => ? //.
    - intros. repeat apply continuity_pt_mult.
      * apply continuity_pt_plus.
        ** apply continuity_pt_mult.
           *** apply continuity_pt_const => ? //.
           *** apply ln_continuity_pt; fourier.
        ** apply continuity_pt_const => ? //.
    - rewrite /u => x. destruct (Rle_dec); nra.
    - rewrite /u => x.
      destruct (Rle_dec); intros.
      * assert (x = 1) as -> by (apply Rle_antisym; fourier).
        rewrite ln_1 Rmult_0_r Rplus_0_l. done.
      * done.
  Qed.

  Lemma a_cont_pt: ∀ x, d < x → continuity_pt a x.
  Proof.
    rewrite /d. intros. 
    apply piecewise_continuity_pt with (P := λ x, d < x)
                                               (g := λ x,  
                                                     match Rlt_dec x 2 with
                                                     | left _ => (x - 1)
                                                     | _ => 1
                                                     end)
                                               (f := λ x, 0) (z := 1).
    - intros. apply continuity_const => ??. done.
    - intros. apply piecewise_continuity_pt with (g := λ x, 1)
                                                 (f := λ x, (x - 1))
                                                 (z := 2) 
                                                 (P := λ x, d < x);
                try (intros; destruct (Rlt_dec); nra); try nra.
      * rewrite /d. intros.
        ** apply continuity_minus.
           *** apply continuity_id => ??.
           *** apply continuity_const => ??. done.
      * intros. apply continuity_const => ?? //=.
    - intros x'. rewrite /a. destruct Rle_dec; try nra; destruct Rlt_dec; nra. 
    - intros x'. rewrite /a. destruct Rle_dec; nra. 
    - rewrite /d. intros. fourier.
    - rewrite /d. fourier.
  Qed.
  
  Lemma kinv: /k = ln (/alpha).
  Proof.
    rewrite /k.
    generalize (alpha_range), ln_alpha; intros.
    rewrite ln_Rinv; last by nra. 
    assert (0 < ln (/alpha)).
    { rewrite -ln_1. apply ln_increasing; first nra. apply one_lt_inv_alpha. }
    rewrite Ropp_inv_permute. 
    - rewrite Rinv_involutive //.
      cut (ln alpha ≠ 0); first by nra.
      apply Rlt_not_eq. rewrite -ln_1.
      apply ln_increasing; nra.
    - cut (ln alpha ≠ 0); first by nra.
      apply Rlt_not_eq. rewrite -ln_1.
      apply ln_increasing; nra.
  Qed.

  Lemma urec0 x: x > d → u x ≥ a x + u (m x).
  Proof.
    generalize (alpha_range), ln_alpha => ??.
    rewrite /u/a/m/d. 
    destruct (Rle_dec) as [Hc1|Hc1] => //=; first nra.
    destruct (Rle_dec) as [Hc2|Hc2] => //=.
    - destruct (Rlt_dec) as [?|?]. 
      { 
        destruct (Rlt_dec) as [?|?]; try nra; last first.
        { intros.
          assert (1 / alpha < 2). 
          { destruct alpha_range as (Hlt&?).
            apply Rinv_lt_contravar in Hlt; last nra.
            nra.
          }
          nra.
        }
        intros.
        transitivity (x - 1 +  1); last first.
        { right. field. }
        cut (k * ln x > x - 1); first by (intros; fourier).
        cut (k * ln x - (x - 1) > 0); first by (intros; fourier).
        apply Rlt_gt.
        eapply (Rle_lt_trans _ (k * ln(1) - (1 - 1))).
        { right. rewrite ln_1 Rmult_0_r. field. }
        eapply incr_function_le with (f := λ x, k * ln x - (x - 1))
                                               (x := 1)
                                               (y := x)
                                               (a := 1)
                                               (b := /alpha)
                                               (df := λ x, k * 1/x - 1); try fourier; eauto.
        * rewrite //= => ???. AutoDerive.auto_derive; nra.
        * rewrite //=. intros x' ? ?.
          cut (k */ x' > 1).
          { intros. set (p := k */ x'). assert (p > 1) by (rewrite /p; auto).
            nra.
          }
          apply Rlt_gt, (Rmult_lt_reg_r x'); first fourier.
          rewrite Rmult_assoc Rinv_l; first (rewrite /k; nra).
          apply Rgt_not_eq; fourier.
        * rewrite //=. nra.
        * rewrite //=. nra.
      }
      assert (x = /alpha) as ->.
      { 
        apply (Rmult_le_compat_r (/alpha)) in Hc2; last first.
        {  
          left. transitivity 1; first nra. apply one_lt_inv_alpha.
        }
        rewrite Rmult_assoc Rinv_r in Hc2; last first.
        { apply Rgt_not_eq. nra. }
        rewrite Rmult_1_l Rmult_1_r in Hc2.
        apply Rle_antisym; nra.
      }
      destruct (Rlt_dec); last by nra.
      intros; rewrite -kinv Rinv_r; first nra.
      apply Rgt_not_eq, kgt0.
    - assert (0 < ln x) by (apply Rlt_0_ln; nra).
      destruct (Rlt_dec); first by nra; intros.
      intros; rewrite ln_mult; try nra.
      rewrite (Rmult_plus_distr_l k _).
      assert (k * ln (alpha) = -1) as ->.
      { rewrite /k. field. apply Rlt_not_eq.
        rewrite -(ln_1). apply ln_increasing; nra.
      }
      destruct Rlt_dec.
      * field_simplify; last nra.
      * rewrite /Rdiv; first fourier.
  Qed.

  Lemma alower: ∀ x, x ≤ d → a x = 0.
  Proof.
    rewrite /a => x; destruct (Rle_dec) => //=; nra.
  Qed.

  Lemma a_nonneg: ∀ x, a x ≥ 0.
  Proof.
    intros. rewrite /a. destruct (Rlt_dec); destruct (Rle_dec); nra.
  Qed.

  Lemma a_pos: ∀ x, d < x → 0 < a x.
  Proof.
    rewrite /d/a => ??. destruct (Rlt_dec); destruct (Rle_dec); nra.
  Qed.

  Lemma a_mono: Rmono a. 
  Proof.                                        
    rewrite /Rmono. intros x x' Hle.
    inversion Hle; subst; try reflexivity.
    destruct (Rle_dec d x) as [?|?%Rnot_le_gt].
    * rewrite /a. do 2 (destruct (Rle_dec); try destruct (Rlt_dec)); nra.
    * rewrite alower; auto; try fourier. apply Rge_le, a_nonneg.
  Qed.

  Lemma mnondec: ∀ y y', 0 < y → y ≤ y' → (m y / y) ≤ (m y' / y').
  Proof.
    generalize (alpha_range), ln_alpha => ??.
    intros y y' Hlt Hle.
    rewrite /m.
    destruct (Rlt_dec).
    {  destruct (Rlt_dec). 
       - intros. rewrite /Rdiv ?Rmult_0_l. fourier.
       - intros. rewrite /Rdiv ?Rmult_0_l.
         rewrite Rmult_comm -Rmult_assoc Rinv_l; nra.
    }
    destruct (Rlt_dec); first by nra.
    intros. right. field. split; apply Rgt_not_eq; fourier.
  Qed.

  Lemma d_non_neg: 0 ≤ d.
  Proof.
    rewrite /d. fourier.
  Qed.

End recurrence_log.