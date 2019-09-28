From discprob.prob Require Export prob countable stochastic_order.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
Require Export Reals Psatz.

(* There are some refinements to this that can be proved:
   e.g.: we only needf to assume X x >= 0 for x such that Ω x > 0 *) 

Lemma markov {A} {Ω: distrib A} (X: rrvar Ω) a :
  (∀ x, X x >= 0) →
  a > 0 →
  ex_Ex X →
  pr_ge X a <= Ex X / a.
Proof.
  intros Hnonneg Hgt0 Hex.
  cut (a * pr_ge X a <= Ex X).
  {
    intros. apply (Rmult_le_reg_l a); first by nra.
    etransitivity; first eauto. right. field. nra.
  }
  rewrite /pr_ge pr_ge_to_indicator.
  rewrite -Ex_indicator -Ex_scal_l; last apply ex_Ex_indicator.
  apply Ex_ext_le; auto.
  * apply ex_Ex_scal_l, ex_Ex_indicator.
  * intros x. rewrite //=.
    destruct Rge_dec => //=.
    ** nra. 
    ** rewrite Rmult_0_r. apply Rge_le; auto. 
Qed.

Lemma chebyshev {A} {Ω: distrib A} (X: rrvar Ω) a :
  a > 0 →
  ex_Var X →
  pr_ge (mkRvar Ω (λ a, Rabs (X a - Ex X))) a <= Var X / a^2.
Proof.
  intros Hgt0 Hvar.
  specialize (markov (mkRvar Ω (λ a, (X a - Ex X)^2)) (a^2)).
  intros Hmark. etransitivity; last eapply Hmark.
  * right. rewrite /pr_ge. apply pr_eq_pred'.
    intros i.
    destruct Rge_dec as [Hge1|Hnge1];
    destruct Rge_dec as [Hge2|Hnge2]; try (rewrite //=; done).
    ** exfalso. apply Hnge2.
       apply Rle_ge. rewrite //= ?Rmult_1_r. apply Rsqr_le_abs_1.
       apply Rge_le in Hge1.
       etransitivity; last eapply Hge1.
       rewrite Rabs_right //; nra.
    ** exfalso. apply Hnge1.
       apply Rle_ge. rewrite //=.
       rewrite -(Rabs_right a); last by nra.
       apply Rsqr_le_abs_0.
       apply Rge_le in Hge2.
       rewrite //= ?Rmult_1_r in Hge2. done.
  * rewrite //= => i. rewrite Rmult_1_r.
    apply Rle_ge, Rle_0_sqr.
  * nra.
  * destruct Hvar; auto.
Qed.