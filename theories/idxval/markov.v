From discprob.basic Require Import base sval order monad bigop_ext nify seq_ext.
Require Import Reals Psatz Omega.

Require ClassicalEpsilon.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
Global Set Bullet Behavior "Strict Subproofs".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq div choice fintype finset finfun bigop.
Require Import stdpp.tactics.

Local Open Scope R_scope.
From discprob.idxval Require Import ival pival ival_dist pival_dist pidist_singleton extrema pidist_post_cond.
From discprob.prob Require Import prob countable finite stochastic_order.

Import Lub.


Local Set Printing Coercions.

Lemma general_markov_inequality {X} (f: X → R) (Is: pidist X) (h: R → R) (a: R)
      (Hmono: ∀ x y, x <= y → h x <= h y) (Hpos: ∀ x, 0 <= x → 0 <= h x)
      (Hapos: 0 <= a) (Hhapos: 0 < h a):
  is_finite (Ex_max (λ x, h (Rabs (f x))) Is) →
  ex_Ex_extrema (λ x, h (Rabs (f x))) Is →
  Rbar_le (Pr_max (λ x, f x > a) Is)
          (Rbar_mult (/(h a)) (Ex_max (λ x, h (Rabs (f x))) Is)).
Proof.
  intros Hfin Hex.
  rewrite -Ex_max_scale_const; last first.
  { apply Rle_ge; left. apply Rinv_0_lt_compat; auto. }
  apply Ex_max_le_ext.
  - intros x.  destruct (ClassicalEpsilon.excluded_middle_informative _) => //=.
    * cut (h a <= h (Rabs (f x))).
      { intros. apply (Rmult_le_reg_l (h a)); try nra.
        field_simplify; nra. }
      apply Hmono. transitivity (f x); first nra.
      apply Rle_abs.
    * apply Rmult_le_pos; try nra.
      { left. apply Rinv_0_lt_compat; auto. }
      apply Hpos; auto with *.
  - apply ex_Ex_extrema_scale_const_l; auto.
Qed.

Lemma markov_inequality {X} (f: X → R) (Is: pidist X) (a: R):
  a > 0 →
  is_finite (Ex_max f Is) →
  ex_Ex_extrema f Is →
  pspec Is (λ x, f x >= 0) →
  Rbar_le (Pr_max (λ x, f x > a) Is)
          (Rbar_mult (/a) (Ex_max (λ x, f x) Is)).
Proof.
  intros Hgt0 Hfin Hex Hnonneg.
  assert (Ex_max (λ x, Rabs (f x)) Is =
            Ex_max f Is) as Heq.
  { eapply Ex_max_eq_ext_supp. intros; rewrite Rabs_right; auto. }
  etransitivity; first eapply (general_markov_inequality f Is id a); try auto; try nra.
  * rewrite Heq //=.
  * eapply ex_Ex_extrema_proper_supp; try eassumption.
    intros; rewrite Rabs_right; auto.
  * rewrite Heq //.
Qed.

Lemma Rabs_gt_iff_square x k:
  k > 0 →
  (Rabs x > k ↔ x^2 > k^2).
Proof.
  intros Hgt.
  split.
  - assert (x^2 = (Rabs x)^2) as ->.
    { rewrite //=. apply Rabs_case; nra. }
    nra.
  - intros. apply Rlt_gt.
    replace k with (Rabs k) by (rewrite Rabs_right; nra).
    rewrite -?sqrt_Rsqr_abs.
    apply sqrt_lt_1; rewrite /Rsqr; intros; nra.
Qed.

Lemma chebyshev_inequality {X} (f: X → R) (Is: pidist X) (k: R) (μ: R):
  k > 0 →
  is_finite (Ex_max (λ x, (f x - μ)^2) Is) →
  ex_Ex_extrema (λ x, (f x - μ)^2) Is →
  Rbar_le (Pr_max (λ x, Rabs (f x - μ) > k) Is)
          (Rbar_mult (/(k^2)) (Ex_max (λ x, (f x - μ)^2) Is)).
Proof.
  intros.
  transitivity (Pr_max (λ x, (f x - μ)^2 > k^2) Is).
  - refl_right. apply Ex_max_eq_ext.
    intros x.
    destruct ClassicalEpsilon.excluded_middle_informative as [r|n] => //=;
    destruct ClassicalEpsilon.excluded_middle_informative as [r'|n'] => //=.
    * rewrite Rabs_gt_iff_square in r *; nra.
    * rewrite -Rabs_gt_iff_square in r' *; nra.
  - eapply markov_inequality; try nra; eauto.
    intros ??. apply Rle_ge, pow2_ge_0.
Qed.

Lemma ex_Ex_ivd_max_const {X} (f: X → R) I r:
  ex_Ex_ivd f I ↔ ex_Ex_ivd (λ x, Rmax r (Rabs (f x))) I.
Proof.
  split.
  - intros Hex%ex_Ex_ival_to_Rabs.
    eapply (ex_Ex_ivd_plus_const _ _ (Rabs r)) in Hex.
    eapply ex_Ex_ival_le; last eassumption.
    intros. rewrite Rabs_right; last first.
    { apply Rle_ge. setoid_rewrite <-Rmax_r. apply Rabs_pos. }
    rewrite [a in _ <= a]Rabs_right; last first.
    { specialize (Rabs_pos (f x)). specialize (Rabs_pos r). nra. }
    specialize (Rle_abs r) => Habs.
    specialize (Rabs_pos (f x)) => Hpos.
    specialize (Rabs_pos r) => Hpos'.
    apply Rmax_case; nra.
  - intros. eapply ex_Ex_ival_le; last eassumption.
    intros. rewrite //=. setoid_rewrite <-RRle_abs at 2.
    apply Rmax_r.
Qed.

Lemma ex_Ex_ivd_moments {X} (f: X → R) (I: ivdist X) m n:
  (m <= n)%nat →
  ex_Ex_ivd (λ x, (f x)^n) I →
  ex_Ex_ivd (λ x, (f x)^m) I.
Proof.
  intros Hle.
  rewrite (ex_Ex_ivd_max_const _ _ 1) => Hex.
  rewrite (ex_Ex_ivd_max_const _ _ 1).
  eapply ex_Ex_ival_le; last eassumption.
  intros x => //=. 
  rewrite Rabs_right; last first.
  { apply Rle_ge. setoid_rewrite <-Rmax_r. apply Rabs_pos. }
  rewrite [a in _ <= a]Rabs_right; last first.
  { apply Rle_ge. setoid_rewrite <-Rmax_r. apply Rabs_pos. }
  destruct (Rge_dec (Rabs (f x)) 1).
  - apply Rmax_le_compat; first done.
    rewrite -?RPow_abs. apply Rle_pow; auto. nra.
  - rewrite ?Rmax_left; first done.
    * rewrite -RPow_abs.
      destruct n; first by auto.
       left. apply pow_lt_1_compat; last by omega.
       split; try nra.
       apply Rabs_pos.
    * rewrite -RPow_abs.
      destruct m; first by auto.
       left. apply pow_lt_1_compat; last by omega.
       split; try nra.
       apply Rabs_pos.
Qed.

Lemma ex_Ex_ivd_moments_1 {X} (f: X → R) (I: ivdist X) n:
  (1 <= n)%nat →
  ex_Ex_ivd (λ x, (f x)^n) I →
  ex_Ex_ivd f I.
Proof.
  intros. eapply ex_Ex_ival_proper'; last first.
  { eapply (ex_Ex_ivd_moments f I 1); eauto. }
  { reflexivity. }
  rewrite //= => ?. ring.
Qed.

Lemma ex_Ex_extrema_moments {X} (f: X → R) (Is: pidist X) m n:
  (m <= n)%nat →
  ex_Ex_extrema (λ x, (f x)^n) Is →
  ex_Ex_extrema (λ x, (f x)^m) Is.
Proof.
  intros Hle Hex I Hin.
  eapply (ex_Ex_ivd_moments f ({| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |})); eauto.
  eapply Hex; eauto.
Qed.

Lemma ex_Ex_extrema_moments_1 {X} (f: X → R) (Is: pidist X) n:
  (1 <= n)%nat →
  ex_Ex_extrema (λ x, (f x)^n) Is →
  ex_Ex_extrema f Is.
Proof.
  intros Hle Hex I Hin.
  eapply (ex_Ex_ivd_moments_1 f ({| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |})); eauto.
  eapply Hex; eauto.
Qed.
  
Lemma is_Ex_ival_variance {X} (f: X → R) (I: ivdist X) (μ: R):
  ex_Ex_ival (λ x, (f x)^2) I →
  is_Ex_ival (λ x, (f x - μ)^2) I (Ex_ival (λ x, (f x)^2) I - 2 * μ * Ex_ival f I + μ^2).
Proof.
  intros Hex.
  eapply (is_Ex_ival_proper' (λ x, (f x)^2 - 2 * μ * (f x) + μ^2)).
  { rewrite //= => ?. field. }
  { reflexivity. }
  apply is_Ex_ival_sum; last apply is_Ex_ivd_const.
  apply is_Ex_ival_sum.
  - apply Ex_ival_correct; auto.
  - apply: is_Ex_ival_negate.
    apply: is_Ex_ival_scal_l.
    apply Ex_ival_correct. apply: ex_Ex_ivd_moments_1; try eassumption. omega.
Qed.

Lemma Finite_Rplus x y:
  Finite (x + y) = Rbar_plus (Finite x) (Finite y).
Proof. done. Qed.

Lemma Finite_Rmult x y:
  Finite (x * y) = Rbar_mult (Finite x) (Finite y).
Proof. done. Qed.

Lemma Finite_Ropp x:
  Finite (- x) = Rbar_opp (Finite x).
Proof. done. Qed.

Lemma Rbar_mult_finite_le_compat_l :
  ∀ (r: R) (r1 r2 : Rbar), 0 <= r → Rbar_le r1 r2 → Rbar_le (Rbar_mult r r1) (Rbar_mult r r2).
Proof.
  intros. destruct r1, r2 => //=; try destruct Rle_dec; try auto; try nra.
  * apply Rmult_le_compat_l; eauto.
  * destruct Rle_lt_or_eq_dec; eauto; subst => //=. nra.
  * destruct Rle_lt_or_eq_dec; eauto; subst => //=. nra.
  * destruct Rle_lt_or_eq_dec; eauto; subst => //=.
Qed.

Lemma Rabs_pow2 (x: R):
  Rabs (x^2) = x^2.
Proof.
  rewrite  Rabs_mult Rmult_1_r. apply Rabs_case; nra.
Qed.

Lemma bounded_psupp_variance_moment1 {X} (f: X → R) Is μ:
  bounded_fun_on (λ x, (f x - μ) ^ 2) (λ x, In_psupport x Is) ↔
  bounded_fun_on f (λ x, In_psupport x Is).
Proof.
  split.
  - intros (c&Hmax). exists (sqrt c + Rabs μ).
    intros x Hin. specialize (Hmax x Hin).
    assert (0 <= c).
    { etransitivity; last eauto. apply Rabs_pos. } 
    apply sqrt_le_1_alt in Hmax.
    replace (Rabs ((f x - μ)^2)) with ((Rabs (f x - μ))^2) in Hmax; last first.
    { rewrite pow2_abs Rabs_pow2 //=. }
    rewrite sqrt_pow2 in Hmax; last apply Rabs_pos.
    move: Hmax. repeat apply Rabs_case; nra.
  - intros (c&Hmax). exists (c^2 + 2 * c * Rabs μ + μ^2).
    intros x Hin. specialize (Hmax x Hin).
    rewrite Rabs_pow2. ring_simplify.
    cut (f x ^2 ≤ c^2 + 2 * c * Rabs μ + 2 * f x * μ); first by nra.
    specialize (pow_maj_Rabs _ _ 2 Hmax) => H.
    cut (0 <= 2 * c * Rabs μ + 2 * f x * μ); first nra.
    move: Hmax. do 2 apply Rabs_case; nra.
Qed.

Lemma bounded_psupp_moment1_moment2 {X} (f: X → R) Is:
  bounded_fun_on f (λ x, In_psupport x Is)
  ↔ bounded_fun_on (λ x, (f x) ^ 2) (λ x, In_psupport x Is).
Proof.
  split.
  - intros (c&Hmax). exists (c^2).
    intros x Hin. specialize (Hmax x Hin).
    rewrite Rabs_pow2.
    specialize (pow_maj_Rabs _ _ 2 Hmax) => H; nra.
  - intros (c&Hmax). exists (sqrt c).
    intros x Hin. specialize (Hmax x Hin).
    rewrite ?Rabs_mult in Hmax. replace (Rabs 1) with 1 in Hmax by (rewrite Rabs_right; nra).
    apply sqrt_le_1_alt in Hmax. rewrite (sqrt_pow2 (Rabs (f x))) in Hmax; auto using Rabs_pos.
Qed.

Lemma bounded_psupp_variance_moment2 {X} (f: X → R) Is μ:
  bounded_fun_on (λ x, (f x - μ) ^ 2) (λ x, In_psupport x Is)
  ↔ bounded_fun_on (λ x, (f x) ^ 2) (λ x, In_psupport x Is).
Proof.
  rewrite bounded_psupp_variance_moment1.
  apply bounded_psupp_moment1_moment2.
Qed.

Lemma Ex_max_variance {X} (f: X → R) (Is: pidist X) (μ: R):
  ex_Ex_extrema (λ x, (f x)^2) Is →
  μ >= 0 →
  Rbar_le (Ex_max (λ x, (f x - μ)^2) Is)
          (Rbar_plus (Ex_max (λ x, (f x)^2) Is)
                     (Rbar_plus (Rbar_mult (- 2 * μ) (Ex_min f Is)) (Finite (μ^2)))).
Proof.
  intros Hex Hpos.
  apply Ex_max_spec2. intros r Hin.
  destruct Hin as (I&Hin&His).
  erewrite (is_Ex_ival_unique' (λ x, (f x - μ)^2) I r); auto; last first.
  { apply (is_Ex_ival_variance _ {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |}).
    eapply Hex. eauto. }
  rewrite Rplus_assoc.
  rewrite ?Finite_Rplus.
  apply Rbar_plus_le_compat.
  { apply Ex_max_spec1'; eauto. }
  apply Rbar_plus_le_compat; last done.
  rewrite Finite_Ropp.
  rewrite -Ropp_mult_distr_l.
  rewrite Finite_Ropp.
  rewrite Rbar_mult_opp_l.
  apply Rbar_opp_le.
  rewrite [a in Rbar_le _ a]Finite_Rmult.
  apply Rbar_mult_finite_le_compat_l; try nra.
  apply Ex_min_spec1'; eauto.
  eapply ex_Ex_extrema_moments_1 in Hex; eauto.
Qed.