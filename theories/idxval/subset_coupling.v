Require Import Reals Psatz.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
From discprob.basic Require Import base sval order monad bigop_ext nify.
From discprob.idxval Require Import pival_dist pival ival_dist ival ival_pair pidist_singleton.
From discprob.prob Require Import prob countable finite stochastic_order.

(*
Definition subset_couplingP {A1 A2} (Is1: pidist A1) (Is2: pidist A2) (P: A1 → A2 → Prop) :=
  ∀ (I1: ival A1), In (I1 : ival A1) Is1 →
  { I2 : { I2: ival A2 | In (I2 : ival A2) Is2 } & ival_couplingP I1 (sval I2) P }.
*)

Definition subset_couplingP {A1 A2} (Is1: pidist A1) (Is2: pidist A2) (P: A1 → A2 → Prop) : Prop :=
  ∀ (I1: ival A1), In (I1 : ival A1) Is1 →
  ∃ (I2: ival A2), In (I2 : ival A2) Is2 ∧ ∃ (C: ival_couplingP I1 I2 P), True.

Lemma subset_coupling_eq {A} (Is1 Is2: pidist A)
      (Ic: subset_couplingP Is1 Is2 (λ x y, x = y)): le_pidist Is1 Is2. 
Proof.
  intros I1 Hin.
  specialize (Ic (lift_In_pidist I1 Hin) Hin).
  destruct Ic as (I2&Hin2&(Hcouple&_)).
  exists I2; split; auto.
  eapply ival_coupling_eq in Hcouple; done.
Qed.

Lemma singleton_coupling_eq {A} (I1 : ivdist A) (Is2: pidist A)
      (Ic: subset_couplingP (singleton I1) Is2 (λ x y, x = y)): In_pidist I1 Is2. 
Proof.
  by apply In_pidist_le_singleton, subset_coupling_eq.
Qed.

Lemma subset_coupling_bind {A1 A2 B1 B2} (f1: A1 → pidist B1) (f2: A2 → pidist B2)
      Is1 Is2 P Q (Ic: subset_couplingP Is1 Is2 P):
  (∀ x y, P x y → subset_couplingP (f1 x) (f2 y) Q) →
  subset_couplingP (mbind f1 Is1) (mbind f2 Is2) Q.
Proof.
  intros Hfc.
  intros I1 Hin.
  edestruct (pival_mbind_in_inv_idxOf Is1 f1 I1) as (I1_0&h1&Hin1_0&Hh1&Heq); auto.
  specialize (Ic I1_0 Hin1_0). 
  destruct Ic as (I2_0&Hin2_0&(Hcouple&_)).
  apply ival_coupling_idxOf in Hcouple.
  destruct Hcouple as ((Rel&Hfunc)&[Ic_0 Hp1 Hp2]).
  apply ClassicalEpsilon.constructive_indefinite_description in Hp1.
  destruct Hp1 as (hidx1&Hp1).
  apply ClassicalEpsilon.constructive_indefinite_description in Hp1.
  destruct Hp1 as (hidx1'&?&?&Hind1&?).

  apply ClassicalEpsilon.constructive_indefinite_description in Hp2.
  destruct Hp2 as (hidx2&Hp2).
  apply ClassicalEpsilon.constructive_indefinite_description in Hp2.
  destruct Hp2 as (hidx2'&?&?&Hind2&?).


  unshelve (edestruct (pival_mbind_in_alt2_idxOf Is2 f2 I2_0) as (Ib&Heqb&Hinb)).
  { intros i2. 
    destruct (Rgt_dec (val I2_0 i2) 0) as [Hgt|Hngt]; last (exact zero_ival).
    destruct (hidx2 (coerce_supp _ _ Hgt)) as ((i0&[])&Hgt0).
    destruct (ind Ic_0 i0) as ((i1&i2')&(HP&Hsup1&Hsup2)).
    specialize (Hfc _ _ HP (h1 i1) (Hh1 _ Hsup1)).
    apply ClassicalEpsilon.constructive_indefinite_description in Hfc.
    destruct Hfc as (I2&?).
    exact I2.
  }
  - exists I2_0; split; auto; reflexivity. 
  - intros. 
    simpl. destruct Rgt_dec as [r|?] => //=.
    specialize (Hind2 ((coerce_supp (val I2_0) i r))).
    destruct (hidx2) as ((i0&[])&Hgt0) => //=.
    rewrite //= in Hind2.
    case_eq (ind Ic_0 i0). intros (i1&i2') (HP&Hsup1&Hsup2&HQ) Heq0.
    rewrite Heq0. rewrite Heq0 in Hind2.
    destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?); auto.
    subst. done. 
  - exists Ib; split; auto.
    unshelve (eexists); last done.
    eapply ival_coupling_proper.
    * eauto.
    * eauto.
    * eapply (ival_coupling_bind _ _ _ _
          (λ x y, P (ind I1_0 x) (ind I2_0 y) ∧ val I1_0 x > 0 ∧ val I2_0 y > 0 ∧ Rel x y)).
      { exists Ic_0. exists hidx1; eauto. exists hidx2; eauto.  }
      intros x y (HP&Hgtx&Hgty&HRel).
      destruct Rgt_dec as [r|?] => //=.
    specialize (Hind2 ((coerce_supp (val I2_0) y r))).
    destruct (hidx2) as ((i0&[])&Hgt0) => //=.
    rewrite //= in Hind2.
    case_eq (ind Ic_0 i0). intros (i1&i2') (HP'&Hsup1&Hsup2&HQ) Heq0.
    rewrite Heq0. rewrite Heq0 in Hind2.
      destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&Hc).
      apply ClassicalEpsilon.constructive_indefinite_description in Hc as (Hc&?).
      cut (x = i1).
      { intros.  subst. auto. }
      eapply Hfunc.
      eauto. clear -HQ Hind2. rewrite //= in Hind2. rewrite -Hind2. rewrite //= in HQ.
Qed.

Lemma subset_coupling_le {X Y} Is1 Is1' Is2 Is2' (P: X → Y → Prop) :
  le_pidist Is1' Is1 → 
  le_pidist Is2 Is2' → 
  subset_couplingP Is1 Is2 P → 
  subset_couplingP Is1' Is2' P.
Proof.
  intros Hle1 Hle2 Hsub.
  intros I1' Hin1'.
  destruct (Hle1 _ Hin1') as (I1&Heq&Hin1).
  destruct (Hsub _ Hin1) as (I2&Hin2&Hc&_).
  destruct (Hle2 _ Hin2) as (I2'&Heq2&Hin2').
  exists I2'; split; auto.
  eexists; last by done.
  eapply ival_coupling_proper; try eassumption.
    by symmetry.
Qed.
  
Lemma subset_coupling_proper {X Y} Is1 Is1' Is2 Is2' (P: X → Y → Prop) :
  eq_pidist Is1 Is1' → 
  eq_pidist Is2 Is2' → 
  subset_couplingP Is1 Is2 P → 
  subset_couplingP Is1' Is2' P.
Proof.
  intros Heq1 Heq2. eapply subset_coupling_le; eauto.
  - setoid_rewrite Heq1; reflexivity.
  - setoid_rewrite Heq2; reflexivity.
Qed.

Lemma subset_coupling_support {X Y} I1 I2 (P: X → Y → Prop) :
  subset_couplingP I1 I2 P → 
  subset_couplingP I1 I2 (λ x y, P x y ∧ In_psupport x I1 ∧ In_psupport y I2).
Proof.
  intros Hsub I Hin.
  edestruct (Hsub I Hin) as (I'&Hin'&Ic&_).
  exists I'; split; first done.
  unshelve (eexists); last done.
  eapply ival_coupling_conseq; last first.
  { apply (ival_coupling_support _ _ _ Ic). }
  intros x y (Hpf&Hin1&Hin2&?); repeat split; auto.
  - exists I; auto. edestruct Hin1; eexists; eauto. 
  - exists I'; auto. edestruct Hin2; eexists; eauto. 
Qed.
  
Lemma subset_coupling_plus {A1 A2} p Hpf p' Hpf'
      (P : A1 → A2 → Prop) (Is1 Is1': pidist A1) (Is2 Is2': pidist A2) :
  p = p' →
  subset_couplingP Is1 Is2 P →
  subset_couplingP Is1' Is2' P →
  subset_couplingP (pidist_plus p Hpf Is1 Is1') (pidist_plus p' Hpf' Is2 Is2') P.
Proof.
  intros Hp Hsub Hsub'.
  subst.
  intros I (I1&I1'&Hin1&Hin1'&Heq1)%pidist_plus_in_inv.
  subst.

  edestruct (Hsub _ Hin1) as (I2&Hin&Hequiv&?).
  edestruct (Hsub' _ Hin1') as (I2'&Hin'&Hequiv'&?).
  exists (iplus (iscale p' I2) (iscale (1 - p') I2')).
  split.
  - apply pplus_in; apply pscale_in; auto.
  - unshelve (eexists); auto.
    apply ival_coupling_plus'; auto.
Qed.