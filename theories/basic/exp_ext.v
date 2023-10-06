From discprob.basic Require Import base order nify.
From discprob.basic Require Export Reals_ext.
Require Import Ranalysis5.
Require Import Reals Fourier FunctionalExtensionality.
Require Import List.
Require Import Psatz.

Lemma exp_le_embedding x y:
  exp x <= exp y → x <= y.
Proof.
  intros Hle. apply Rnot_lt_le => Hlt.
  apply exp_increasing in Hlt. nra.
Qed.

Lemma exp_increasing_le: ∀ x y : R, x <= y → exp x <= exp y.
Proof.
  inversion 1.
  - left. by apply exp_increasing.
  - subst. reflexivity.
Qed.

Lemma exp_ge_2: 2 <= exp 1.
Proof. apply Rlt_le. apply exp_ineq1. nra. Qed.

Lemma Rlt_0_ln x: 1 < x → 0 < ln x.
Proof.
  intros Hlt; rewrite -ln_1; apply ln_increasing; fourier.
Qed.

Lemma exp_ineq1_le x: 0 <= x → 1 + x <= exp x.
Proof.
  intros [Hlt|Heq].
  * left. apply exp_ineq1. nra.
  * rewrite -Heq exp_0. nra.
Qed.
Lemma exp_fold_plus (l: list R):
  exp (fold_right Rplus 0 l) = fold_right Rmult 1 (map exp l).
Proof.
  induction l => //=.
  - rewrite exp_0; done.
  - rewrite exp_plus IHl. done.
Qed.
