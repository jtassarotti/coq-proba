Require Export Reals Psatz Fourier.
From discprob.basic Require Export exp_ext.
From discprob.prob Require Export prob countable stochastic_order markov indep bernoulli.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From Coquelicot Require Import Derive Continuity.
From Coquelicot Require AutoDerive.
From Interval Require Import Interval_tactic.


(* See Chapter 4 of Mitzenmacher-Upfal, 2nd edition. *)

Lemma generic_chernoff_upper {A} {Ω: distrib A} (X: rrvar Ω) t a:
  t > 0 →
  ex_Ex (rvar_comp X (λ x, exp (t * x))) →
  pr_ge X a <= Ex (rvar_comp X (λ x, exp (t * x))) / (exp (t * a)).
Proof.
  intros Ht Hex.
  transitivity (pr_ge (rvar_comp X (λ x, exp (t * x))) (exp (t * a))).
  - right. apply pr_eq_pred' => x.
    destruct (Rge_dec) as [Hge|Hnge] => //=.
    * apply Rgt_lt in Ht.
      apply Rge_le in Hge. 
      apply (Rmult_le_compat_l t) in Hge; last by nra.
      apply exp_increasing_le in Hge.
      destruct (Rge_dec) as [?|Hnge'] => //=.
      exfalso; apply Hnge'. by apply Rle_ge.
    * destruct (Rge_dec) as [Hge|Hnge'] => //=.
      exfalso. apply Hnge.
      apply Rge_le, exp_le_embedding in Hge.
      apply Rmult_le_reg_l in Hge;  auto. 
  - apply markov => //=.
    * intros. apply Rle_ge; left; apply exp_pos.
    * intros. apply Rlt_gt; apply exp_pos.
Qed.

Local Open Scope R_scope.

Lemma chernoff_bernoulli_upper {A} {Ω: distrib A} (lX: list (rrvar Ω)) δ:
  (∀ X, In X lX → ∃ p, is_bernoulli X p) →
  independent lX →
  δ > 0 →
  pr_ge (sum_list_rrvar lX) ((1 + δ) * Ex (sum_list_rrvar lX))
    <= Rpower (exp(δ) / (Rpower (1 + δ) (1 + δ))) (Ex (sum_list_rrvar lX)).
Proof.
  intros Hbern Hindep Hdelta_pos.
  assert (Hext: ∀ a : A,
             (prod_list_rrvar (map (rvar_comp^~ (λ x : R_eqType, exp (ln (1 + δ) * x))) lX)) a =
             (rvar_comp (sum_list_rrvar lX) (λ x : [eqType of R], exp (ln (1 + δ) * x))) a).
  {
    * intros a => //=. induction lX.
      ** rewrite //=. by rewrite Rmult_0_r exp_0.
      ** rewrite //=. rewrite Rmult_plus_distr_l exp_plus. f_equal.
         eapply IHlX.
         *** intros.  eapply Hbern. by right.
         *** eapply independent_tl. eauto.
  }

  assert (Hex_Ex_prod:
            ex_Ex (prod_list_rrvar (map (rvar_comp^~ (λ x : R_eqType, exp (ln (1 + δ) * x))) lX))).
  {
    * apply ex_Ex_indep_prod_list.
      ** by apply indep_fn.
      ** intros ? (X&Heq&Hin)%in_map_iff.
         rewrite -Heq. edestruct (Hbern _ Hin) as (p&His_bern).
         eapply is_bernoulli_ex_Ex; eauto.
  }

  assert (Hpow_pos: 0 < Rpower (1 + δ) (1 + δ)).
  { rewrite /Rpower. apply exp_pos. }

  etransitivity; first eapply generic_chernoff_upper with (t := ln (1 + δ)).
  - rewrite -ln_1. apply Rlt_gt. apply ln_increasing; nra.
  - apply (ex_Ex_ext (prod_list_rrvar (map (λ X, rvar_comp X (λ x, exp (ln (1 + δ) * x))) lX )));
      eauto.
  - rewrite -(Ex_ext _ _ _ Hext) //. rewrite Ex_sum_list; last first.
    { intros ? Hin. edestruct (Hbern _ Hin) as (p&?); eapply is_bernoulli_ex_Ex with (f := id).
      eauto. }
    rewrite Ex_indep_prod_list.
    *
      rewrite /Rdiv -Rpower_mult_distr.
      assert (Hpow_opp': ∀ x y, 0 < x → Rpower (/ x) y = / Rpower x y).
      { 
        intros x y.
        rewrite -Rpower_Ropp.
        rewrite /Rpower.
        intros; rewrite ln_Rinv //.
        f_equal. nra.
      }
      rewrite Hpow_opp'.
      rewrite /Rpower.
      assert (exp (ln (1 + δ) * ((1 + δ) * fold_right Rplus 0 (seq.map Ex lX))) =
              exp (fold_right Rplus 0 (seq.map Ex lX) * ln (exp ((1 + δ) * ln (1 + δ)))))
        as ->.
      {
        f_equal. rewrite ln_exp. nra.
      }
      apply Rmult_le_compat_r.
      ** left. apply Rinv_0_lt_compat, exp_pos.
      ** rewrite /Rpower. rewrite fold_right_plus_mult exp_fold_plus. 
         rewrite ?seq_ext.map_legacy ?map_map => //=.
         apply fold_right_map_Rmult_le => X Hin. 
         destruct (Hbern X Hin) as (p&HXbern).
         rewrite (EGF_is_bernoulli _ p HXbern (ln (1 + δ))).
         rewrite (Ex_is_bernoulli _ p HXbern). 
         rewrite exp_ln; last by nra.
         destruct (is_bernoulli_range _ _ HXbern) as (?&?).
         split.
         *** nra.
         *** ring_simplify. 
             rewrite ln_exp. rewrite Rplus_comm. apply exp_ineq1_le. nra.
      ** auto. 
      ** apply exp_pos.
      ** by apply Rinv_0_lt_compat. 
    * by apply indep_fn.
    * intros ? (X&Heq&Hin)%in_map_iff.
      rewrite -Heq. destruct (Hbern _ Hin) as (p&HXbern).
      eapply is_bernoulli_ex_Ex; eauto.
Qed.

Lemma Ex_sum_bernoulli_non_neg {A} {Ω: distrib A} (lX : list (rrvar Ω)):
  (∀ X, In X lX → ∃ p, is_bernoulli X p) →
  0 <= Ex (sum_list_rrvar lX).
Proof.
  intros Hbern. rewrite Ex_sum_list.
  - induction lX as [| X lX]=> //=; first reflexivity.
    destruct (Hbern X) as (p&HXbern); first by left.
    rewrite (Ex_is_bernoulli _ _ HXbern).
    destruct (is_bernoulli_range _ _ HXbern) as (?&?).
    rewrite -[a in a <= _]Rplus_0_r. apply Rplus_le_compat; auto.
    eapply IHlX. intros. apply Hbern. by right. 
  - intros X Hin.
    destruct (Hbern X) as (p&HXbern); auto.
    eapply is_bernoulli_ex_Ex with (f := id); eauto.
Qed.


      
Lemma non_decr_function_le: ∀ (f : R → R) (a b : Rbar) (df : R → R),
       (∀ x : R, Rbar_le a x → Rbar_le x b → is_derive f x (df x))
       → (∀ x : R, Rbar_le a x → Rbar_le x b → df x >= 0)
         → ∀ x y : R, Rbar_le a x → x <= y → Rbar_le y b → f x <= f y.
Proof.
  intros f a b df Hderiv Hderiv_non_neg x y Hrange1 Hrange2 Hrange3.
  edestruct (MVT_gen f x y) as (c&(Hrange1'&Hrange2')&Heq).
  - intros x'. rewrite Rmin_left //= Rmax_right //=. intros [? ?]. eapply Hderiv.
    * eapply Rbar_le_trans; eauto. by rewrite /Rbar_le; left.
    * eapply Rbar_le_trans; eauto. by rewrite /Rbar_le; left.
  - intros x'. rewrite Rmin_left //= Rmax_right //=. intros [? ?].
    assert (continuous f x').
    apply: ex_derive_continuous; eauto.
    econstructor. eapply Hderiv; eauto.
    * eapply Rbar_le_trans; eauto. 
    * eapply Rbar_le_trans; eauto. rewrite /Rbar_le; auto.
    * by apply continuity_pt_filterlim.
  - rewrite //= in Heq.
    assert (df c >= 0).
    { apply Hderiv_non_neg.
      * rewrite Rmin_left in Hrange1'; auto. eapply Rbar_le_trans; eauto. 
      * rewrite Rmax_right in Hrange2'; auto. eapply Rbar_le_trans; eauto. 
        rewrite /Rbar_le //=.
    }
    nra.
Qed.

Lemma chernoff_bernoulli_upper_alt {A} {Ω: distrib A} (lX: list (rrvar Ω)) δ:
  (∀ X, In X lX → ∃ p, is_bernoulli X p) →
  independent lX →
  0 < δ <= 1 →
  pr_ge (sum_list_rrvar lX) ((1 + δ) * Ex (sum_list_rrvar lX))
    <= exp (- Ex (sum_list_rrvar (lX)) * δ^2 / 3).
Proof.
  intros Hbern Hindep Hdelta.
  etransitivity; first eapply chernoff_bernoulli_upper; eauto; try nra; [].
  rewrite /Rpower.
  apply exp_increasing_le.
  rewrite ln_div ?ln_exp.
  - cut (0 <= - (δ - (1 + δ) * ln (1 + δ) + δ^2 / 3) ).
    { intros. specialize (Ex_sum_bernoulli_non_neg _ Hbern) => ?; nra. }
    set (f := λ δ, - (δ - (1 + δ) * ln (1 + δ) + δ^2 / 3)).
    rewrite -/(f δ). transitivity (f 0).
    * right. rewrite /f ?Rplus_0_r ln_1. nra.
    * set (f' := λ δ, - (1 - (1 + δ) / (1 + δ) - ln (1 + δ) + (2 / 3) * δ)).
      set (f'' := λ δ, - (- 1 / (1 + δ) + (2 / 3))).
      apply non_decr_function_le with (a := 0) (b := δ) (df := f').
      ** rewrite /Rbar_le //=. intros x Hr1 Hr2. rewrite /f/f'. AutoDerive.auto_derive; nra.
      ** rewrite /Rbar_le //=. intros x Hr1 Hr2.
         apply Rle_ge.
         assert (x < 1/2 ∨ x = 1/2 ∨ 1/2 < x) as [Hlt|[Heq|Hgt]] by nra.
         {
           transitivity (f' 0). 
             { right. rewrite /f'. rewrite Rplus_0_r ln_1. field. } 
             apply non_decr_function_le with (a := 0) (b := x) (df := f'').
           *** rewrite /Rbar_le //=. intros x' ??; rewrite /f'/f''. AutoDerive.auto_derive.
               **** repeat split; auto; try nra. 
               **** field. nra.
           *** rewrite /Rbar_le //=. intros x' ??; rewrite /f'/f''. 
               field_simplify; last by nra.
               apply Rle_ge. replace (0 / 1) with 0 by nra.
               apply Rdiv_le_0_compat; nra.
           *** rewrite //=. reflexivity.
           *** nra.
           *** rewrite //=. reflexivity.
         }
         { rewrite /f'. subst. interval. }
         { 
           transitivity (f' 1).
           { rewrite /f'. interval. }
           cut (- f' x <= - f' 1); first by (intros; nra). 
           apply non_decr_function_le with (f := λ x, - f' x) (a := 1/2) (b := 3/2) (df := λ x, - f'' x).
           *** rewrite /Rbar_le //=. intros x' ??; rewrite /f'/f''. AutoDerive.auto_derive.
               **** repeat split; auto; try nra. 
               **** field. nra.
           *** rewrite /Rbar_le //=. intros x' ??; rewrite /f'/f''. 
               field_simplify; last by nra.
               apply Rle_ge. replace (0 / 1) with 0 by nra.
               apply Rdiv_le_0_compat; nra.
           *** rewrite //=.  nra.
           *** nra.
           *** rewrite //=. nra.
         }
      ** rewrite //=. nra.
      ** rewrite //=. nra.
      ** rewrite //=. nra.
  - apply exp_pos.
  - apply exp_pos.
Qed.