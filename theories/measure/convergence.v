Require Import Reals Psatz Omega.
From stdpp Require Import tactics list.
From discprob.basic Require Import seq_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.measure Require Export measures borel.
Require Import ClassicalEpsilon SetoidList.

Section convergence.

  Context {A: Type}.
  Context {F: sigma_algebra A}.
  Context (μ: measure F).

  Definition converge_in_measure (fn: nat → A → R) (f: A → R) :=
    ∀ (eps : posreal), is_lim_seq (λ n, μ (λ x, Rabs (fn n x - f x) > eps)) 0.

  Lemma convergence_ae_measure fn (f: A → R):
    (∀ n, measurable (fn n) F (borel _)) →
    measurable f F (borel _) →
    (* I think this next assumption could be weakened or removed *)
    F (λ x, ¬ is_lim_seq (λ n, fn n x) (f x))→
    μ (λ x, ¬ is_lim_seq (λ n, fn n x) (f x)) = 0 →
    converge_in_measure fn f.
  Proof.
    intros Hmeas_fn Hmeas Hmeas0 Hae.
    intros eps.
    set (h := λ n x, Rabs (fn n x - f x)).
    assert (Hh_meas: ∀ n, measurable (h n) F (borel _)).
    { intros n. rewrite /h. measurable. }
    set (An := λ n, (fun_inv (h n) (λ x, x > eps))).
    set (Bn := λ n, unionF (λ k, An (n + k)%nat)).
    assert (∀ n, F (An n)).
    { intros n. rewrite /An. apply Hh_meas, open_ray_borel_gt. }
    assert (∀ n, F (Bn n)).
    { intros n. rewrite /Bn. apply sigma_closed_unions; eauto. }
    rewrite //=.
    assert (intersectF Bn ⊆ (λ x : A, ¬ is_lim_seq (fn^~ x) (f x))).
    { intros x Hin Hlim.
      destruct (Hlim (ball (f x) eps)) as (n'&Hlim'); first by apply locally_ball.
      destruct (Hin n') as (n''&HinA).
      rewrite /An/fun_inv/h//= in HinA.
      feed pose proof (Hlim' (n' + n'')%nat) as Hball.
      { omega. }
      rewrite /ball//=/AbsRing_ball//=/abs/minus/plus/opp//= in Hball.
      clear -HinA Hball. apply Rgt_not_le in HinA. apply HinA. left. done.
    }
    assert (Hinter: μ (intersectF Bn) = 0).
    { apply Rle_antisym; last apply Rge_le, measure_nonneg. rewrite -Hae.
      apply measure_mono; eauto using sigma_closed_intersections.
    }
    assert (Hlim: is_lim_seq (λ n, μ (Bn n)) 0).
    { 
      rewrite -Hinter. apply measure_decr_seq; eauto. 
      clear. rewrite /Bn. intros i x (n&Hin). exists (S n).
      replace (i + S n)%nat with (S i + n)%nat by omega.
      auto.
    }
    eapply (is_lim_seq_le_le (λ n, 0) _ (λ n, μ (Bn n))).
    - intros n; split.
      * apply Rge_le, measure_nonneg. 
      * apply measure_mono; eauto.
        rewrite /Bn/An. intros x ?. exists O. replace (n + O)%nat with n by omega.
        eauto.
    - apply is_lim_seq_const.
    - auto.
  Qed.

  Lemma convergence_pointwise_measure fn (f: A → R):
    (∀ n, measurable (fn n) F (borel _)) →
    measurable f F (borel _) →
    (∀ x, is_lim_seq (λ n, fn n x) (f x)) →
    converge_in_measure fn f.
  Proof.
    intros Hmeas_fn Hmeas Hlim.
    assert (Hequiv: (λ x : A, ¬ is_lim_seq (fn^~ x) (f x)) ≡ ∅).
    { 
      intros x; split.
      - intros Hfalse. exfalso. apply Hfalse. eapply Hlim. 
      - inversion 1.
    }
    eapply convergence_ae_measure; auto.
    - rewrite Hequiv. apply sigma_empty_set.
    - rewrite Hequiv. apply measure_empty.
  Qed.
End convergence.