From discprob.basic Require Import base sval order monad bigop_ext nify seq_ext.
Require Import Reals Psatz Omega.

Require ClassicalEpsilon.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
Global Set Bullet Behavior "Strict Subproofs".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq div choice fintype finset finfun bigop.
Require Import stdpp.tactics.
Local Open Scope R_scope.
From discprob.idxval Require Import ival pival ival_dist pival_dist pidist_singleton extrema.
From discprob.prob Require Import prob countable finite stochastic_order.

Definition pspec {A: Type} (m: pidist A) (P: A → Prop) :=
  ∀ y, In_psupport y m → P y.


Section pspec.

  Context {A: Type}.
  Implicit Types m : pidist A.
  Implicit Types P : A → Prop.
          
Lemma pspec_mret (x: A) P:
  P x → pspec (mret x) P.
Proof.
  intros HP y. intros (I&i&Hin&Heq&Hgt).
  rewrite -Heq. inversion Hin as [Heq']. subst => //=.
Qed.

Lemma pspec_union m1 m2 P:
  pspec m1 P → pspec m2 P → pspec (pidist_union m1 m2) P.
Proof.
  intros HP1 HP2. intros a (I&i&Hin&?&?).
  destruct Hin.
  * eapply HP1; eauto. eexists; eauto. 
  * eapply HP2; eauto. eexists; eauto. 
Qed.

Lemma pspec_union_inv_l m1 m2 P:
  pspec (pidist_union m1 m2) P →
  pspec m1 P.
Proof.
  intros HP. intros a (I&i&Hin&?&?).
  eapply HP. eapply In_psupport_alt. exists I; split_and!; eauto.
  * by left.
  * eexists; eauto.
Qed.

Lemma pspec_union_inv_r m1 m2 P:
  pspec (pidist_union m1 m2) P →
  pspec m2 P.
Proof.
  intros HP. intros a (I&i&Hin&?&?).
  eapply HP. eapply In_psupport_alt. exists I; split_and!; eauto.
  * by right.
  * eexists; eauto.
Qed.

Lemma In_isupport_proper (a: A) (I1 I2: ival A):
  eq_ival I1 I2 →
  In_isupport a I1 →
  In_isupport a I2.
Proof.
  intros Heq Hin.
  destruct Heq as (w1&w2&?&?&Hind&Hval).
  destruct Hin as (i1&Heq&Hgt).
  assert (Hgti: Rgt_dec (val I1 i1) 0).
  { destruct Rgt_dec => //=. }
  unshelve (eexists).
  { exact (sval (w1 (exist _ i1 Hgti))).  }
  rewrite Hind Hval //=.
Qed.

Lemma In_psupport_proper (a: A) (I1 I2: pival A):
  eq_pival I1 I2 →
  In_psupport a I1 →
  In_psupport a I2.
Proof.
  intros Heqpi (I&i&Hin&Heq&Hval).
  apply In_psupport_alt.
  destruct (Heqpi) as (Hle1&Hle2).
  destruct (Hle1 _ Hin) as (I'&HeqI'&Hin').
  exists I'; split; auto. eapply In_isupport_proper; try eassumption.
  subst. eexists; eauto.
Qed.

Global Instance pspec_proper:
  Proper (@eq_pidist A ==> pointwise_relation A iff ==> iff) pspec.
Proof.
  intros m1 m2 Heq P1 P2 Hiff.
  split.
  - intros Hm x Hin. apply Hiff. apply Hm. eapply In_psupport_proper; eauto.
    by symmetry.
  - intros Hm x Hin. apply Hiff. apply Hm. eapply In_psupport_proper; eauto.
Qed.

Lemma In_isupport_iscale p (I: ival A) x:
  In_isupport x (iscale p I) → In_isupport x I.
Proof.
  intros (i&Heq&Hval).
  subst. rewrite //=. exists i; split; eauto.
  rewrite //= in Hval.
  apply Rlt_gt.
  destruct (Rabs_pos p).
  * eapply Rmult_gt_reg_l; first eassumption.
    nra.
  * nra.
Qed.

Lemma In_psupport_pscale p (Is: pival A) x:
  In_psupport x (pscale p Is) → In_psupport x Is.
Proof.
  intros (I&i&Hin&Heq&Hval).
  apply pscale_in_inv in Hin as (I'&?&?).
  apply In_psupport_alt.
  exists I'; split; eauto.
  eapply In_isupport_iscale.
  eapply In_isupport_proper; eauto. subst.
  eexists; eauto.
Qed.

Lemma pspec_pidist_plus p Hpf m1 m2 P:
  pspec m1 P → pspec m2 P → pspec (pidist_plus p Hpf m1 m2) P.
Proof.
  intros HP1 HP2. intros a (I&i&Hin&?&Hval).
  destruct Hin as (I1&I2&Hin1&Hin2&Heq).
  subst. rewrite //= in Hval. destruct i as [i|i].
  * eapply HP1. rewrite //=. eapply In_psupport_pscale; eauto.
    exists I1; eauto.
  * eapply HP2. rewrite //=. eapply In_psupport_pscale; eauto.
    exists I2; eauto.
Qed.

Lemma pspec_conseq m (P Q: A → Prop):
  pspec m P → (∀ a, P a → Q a) → pspec m Q.
Proof.
  intros HP HPQ a Hin. apply HPQ; eauto.
Qed.

Lemma pspec_mbind {B: Type} (f: A → pidist B) m (P: A → Prop) (Q: B → Prop):
  pspec m P →
  (∀ a, P a → pspec (f a) Q) →
  pspec (mbind f m) Q.
Proof.
  intros Hinput Hbody b Hin.
  edestruct (@In_psupport_bind_inv) as (x&Hin'&I&i&?&?); eauto.
  eapply Hbody; eauto. exists I, i. eauto.
Qed.

Lemma pspec_bounded m (f: A → R):
  (∃ c, pspec m (λ x, Rabs (f x) <= c)) →
  bounded_fun_on f (λ x, In_psupport x m).
Proof.
  intros (c&Hspec). exists c. intros. eapply Hspec; eauto.
Qed.

Lemma bounded_psupp_pidist_plus f p Hpf (Is1 Is2: pidist A):
    bounded_fun_on f (λ i, In_psupport i Is1) →
    bounded_fun_on f (λ i, In_psupport i Is2) →
    bounded_fun_on f (λ i, In_psupport i (pidist_plus p Hpf Is1 Is2)).
Proof.
  intros (max1&Hm1).
  intros (max2&Hm2).
  exists (Rmax max1 max2).
  eapply pspec_pidist_plus.
  * eapply pspec_conseq; rewrite /pspec; first apply Hm1.
    intros. setoid_rewrite <-Rmax_l. auto.
  * eapply pspec_conseq; rewrite /pspec; first apply Hm2.
    intros. setoid_rewrite <-Rmax_r. auto.
Qed.

End pspec.

Tactic Notation "pbind" open_constr(P) :=
  match goal with
  | [ |- pspec (mbind ?f ?m) ?Q ] =>
    intros; eapply (@pspec_mbind _ _ f m P); auto
  end.
