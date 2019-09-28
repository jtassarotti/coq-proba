
Require ClassicalEpsilon.
Require Import Reals Psatz.
From stdpp Require Import tactics.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice bigop.
From discprob.basic Require Import base sval order monad bigop_ext nify.
From discprob.idxval Require Import pival_dist pival ival_dist ival ival_pair pidist_singleton idist_pidist_pair extrema irrel_equiv.
From discprob.prob Require Import prob countable finite stochastic_order.

Import Lub.

Record ival_couplingP' {A1 A2} (Is1: ivdist A1) (Is2: ivdist A2) (P: A1 → A2 → Prop) : Type :=
  mkICoupling { ic_witness :> ivdist {xy: A1 * A2 | P (fst xy) (snd xy)};
     ic_proj1: eq_ivd_prob Is1 (x ← ic_witness; mret (fst (sval x)));
     ic_proj2: eq_ivd_prob Is2 (x ← ic_witness; mret (snd (sval x)));
     }.

Record idist_pidist_couplingP' {A1 A2} (I1: ivdist A1) (I2: pidist A2) (P: A1 → A2 → Prop) : Type :=
  mkIPCoupling { elem_coupling : ivdist A2;
                 elem_member : irrel_pidist (singleton elem_coupling) I2;
                 elem_coupled :> ival_couplingP' I1 elem_coupling P }.

Lemma irrel_ivd_alt {A} (I1 I2: ivdist A):
  irrel_ivd I1 I2 ↔ (∀ f, bounded_fun f → Ex_ival f I1 = Ex_ival f I2).
Proof.
  split.
  - intros Hirrel.
    intros f Hb. apply Ex_ival_irrel_proper; eauto using ex_Ex_ivd_bounded_fun.
  - intros Hf.
    apply eq_ivd_prob_to_irrel_ivd.
    apply eq_ivd_prob_alt.
    rewrite /Ex_ival in Hf.
    rewrite /idx_eq_ind.
    intros x.
    efeed pose proof (Hf (λ y, if is_left (ClassicalEpsilon.excluded_middle_informative (y = x)) then
                                 1
                               else
                                 0)) as H'.
    {
      rewrite /bounded_fun. exists 1.  intros.
      destruct ClassicalEpsilon.excluded_middle_informative; rewrite ?Rabs_R1 ?Rabs_R0; nra.
    }
    rewrite //= in H'.
    setoid_rewrite Rmult_if_distrib in H'.
    setoid_rewrite Rmult_0_l in H'.
    setoid_rewrite Rmult_1_l in H'. eauto.
Qed.

Lemma irrel_couplingP_to_alt {A1 A2} (I1: ivdist A1) (Is2: pidist A2) (P: A1 → A2 → Prop) :
  irrel_couplingP I1 Is2 P → idist_pidist_couplingP' I1 Is2 P.
Proof.
  intros [I1' Is2' Hirrel1 Hirrel2 Hcoup].
  destruct Hcoup as [I2 Hle Hcoup].
  exists I2.
  * setoid_rewrite <-Hirrel2. 
    eapply irrel_pidist_proper; first eassumption; try reflexivity.
  * apply ic_coupling_to_id in Hcoup.
    destruct Hcoup as [Ic Hp1 Hp2]. 
    exists Ic; apply irrel_ivd_to_eq_ivd_prob.
    ** setoid_rewrite Hirrel1. setoid_rewrite Hp1. reflexivity.
    ** setoid_rewrite Hp2. reflexivity.
Qed.

Lemma alt_to_irrel_couplingP {A1 A2} (I1: ivdist A1) (Is2: pidist A2) (P: A1 → A2 → Prop) :
  idist_pidist_couplingP' I1 Is2 P → irrel_couplingP I1 Is2 P.
Proof.
  intros [I2 Heq Hcoup].
  destruct Hcoup as [Ic Hp1 Hp2].
  unshelve (econstructor).
  { exact (Ic ≫= (λ x : {xy : A1 * A2 | P xy.1 xy.2}, mret (sval x).1)). }
  { exact (singleton (Ic ≫= (λ x : {xy : A1 * A2 | P xy.1 xy.2}, mret (sval x).2))). }
  { apply eq_ivd_prob_to_irrel_ivd. eassumption. }
  { etransitivity; last eapply Heq.
    eapply irrel_pidist_proper_irrel; [ | apply le_pidist_irrel_refl | reflexivity].
    { intros ? Hin. exists I2.
      inversion Hin as [Heq']; split.
      * apply eq_ivd_prob_to_irrel_ivd.  rewrite Hp2.
        cut (eq_ivd I (Ic ≫= (λ x : {xy : A1 * A2 | P xy.1 xy.2}, mret (sval x).2))).
        { intros ->. reflexivity. }
        { rewrite /eq_ivd -Heq' //=. }
      * rewrite //=.
    }
  }
  eexists; first reflexivity.
  exists Ic; reflexivity.
Qed.

