(* Discrete uniform distribution as an ival *)
From discprob.basic Require Import base sval order monad nify.
Require Import Reals Psatz Omega.

Require ClassicalEpsilon.
From discprob.prob Require Import double rearrange.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
Global Set Bullet Behavior "Strict Subproofs".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype finset finfun bigop.

Local Open Scope R_scope.
From discprob.idxval Require Import ival ival_dist extrema markov.
From discprob.prob Require Import prob finite stochastic_order.
From discprob.prob Require Export countable.

Lemma iter_Rplus: ∀ m n p, iter n (Rplus m) p = (m * INR n + p).
Proof.
  intros m n. revert m. induction n => m p; first (rewrite //=; field).
  rewrite iterS IHn S_INR. field.
Qed.

Lemma is_seriesC_unif n:
  is_series (countable_sum (λ _ : [finType of 'I_n.+1], 1 / INR n.+1)) 1.
Proof.
  apply SeriesF_is_seriesC'. rewrite /val big_const iter_Rplus.
  rewrite card_ord. field; rewrite S_INR; specialize (pos_INR n); nra.
Qed.

Definition ival_unif (n: nat) : ivdist nat.
  unshelve (econstructor).
  - refine {| idx := [finType of ordinal (S n)]; ind := @nat_of_ord (S n);
              val := λ x, 1 / INR (S n)|}.
    abstract (intros; apply Rle_ge; left;
              rewrite S_INR; apply Rdiv_lt_0_compat; specialize (pos_INR n); nra).
  - apply is_seriesC_unif.
Defined.

Lemma Pr_eq_ival_unif (n: nat) k:
  (k <= n)%coq_nat →
  Pr (λ x, x = k) (ival_unif n) = 1 / INR (S n).
Proof.
  intros Hle. rewrite /Pr/Ex_ival.
  f_equal.
  apply is_series_unique. 
  assert (k < S n)%nat as Hlt by (nify; omega).
  eapply is_seriesC_ext; last apply (is_seriesC_bump [finType of ordinal (S n)] (Ordinal Hlt)).
  intros [n' Hlt']. rewrite //=.
  destruct ClassicalEpsilon.excluded_middle_informative.
  * subst. rewrite //=.
    case: ifP; first (intros; ring).
    move /eqP => Hneq. exfalso. apply Hneq. apply ord_inj => //=.
  * subst. rewrite //=.
    case: ifP; last (intros; ring).
    move /eqP => Hneq. inversion Hneq; subst; eauto.
    contradiction.
Qed.

Lemma ival_unif_primitive (n: nat) : ival_primitive (ival_unif n).
Proof.
  intros [i1 ?] [i2 ?] => //= Heq.
  subst. apply ord_inj => //=.
Qed.
  