Require Export RelationClasses Morphisms.
From discprob.basic Require Import base.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Coquelicot Require Import Hierarchy.

Require Import Reals.
Instance Rge_Transitive: Transitive Rge.
Proof. intros ???. eapply Rge_trans. Qed.
Instance Rle_Transitive: Transitive Rle.
Proof. intros ???. eapply Rle_trans. Qed.
Instance Rge_Reflexive: Reflexive Rge.
Proof. intros ?. eapply Rge_refl. Qed.
Instance Rle_Reflexive: Reflexive Rle.
Proof. intros ?. eapply Rle_refl. Qed.
Instance Rgt_Transitive: Transitive Rgt.
Proof. intros ???. eapply Rgt_trans. Qed.
Instance Rlt_Transitive: Transitive Rlt.
Proof. intros ???. eapply Rlt_trans. Qed.

Import Rbar.
Instance Rbar_le_Transitive: Transitive Rbar_le.
Proof. intros ???. eapply Rbar_le_trans. Qed.
Instance Rbar_le_Reflexive: Reflexive Rbar_le.
Proof. intros ?. eapply Rbar_le_refl. Qed.
Instance Rbar_lt_Transitive: Transitive Rbar_lt.
Proof. intros ???. eapply Rbar_lt_trans. Qed.

Instance ge_Transitive: Transitive ge.
Proof. intros ???. auto with *. Qed.
Instance le_Transitive: Transitive le.
Proof. intros ???. auto with *. Qed.
Instance ge_Reflexive: Reflexive ge.
Proof. intros ?. auto with *. Qed.
Instance le_Reflexive: Reflexive le.
Proof. intros ?. auto with *. Qed.
Instance gt_Transitive: Transitive gt.
Proof. intros ???. auto with *. Qed.
Instance lt_Transitive: Transitive lt.
Proof. intros ???. auto with *. Qed.

(* To be compatible with ssreflect in various ways it's nice to make R
   into an eqType *)

Definition R_eqP : Equality.axiom (fun x y: R => Req_EM_T x y).
Proof. move => x y. apply sumboolP. Qed.

Canonical R_eqMixin := EqMixin R_eqP.
Canonical R_eqType := Eval hnf in EqType R R_eqMixin.

Require Import Psatz.
Instance Rlt_plus_proper: Proper (Rlt ==> Rlt ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. apply Rplus_lt_compat; auto.
Qed.
Instance Rlt_plus_proper': Proper (Rlt ==> eq ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. subst. nra.
Qed.
Instance Rlt_plus_proper'': Proper (Rlt ==> Rle ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. subst. nra.
Qed.

Instance Rle_plus_proper_left: Proper (Rle ==> eq ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.
Instance Rle_plus_proper_right: Proper (eq ==> Rle ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.
Instance Rle_plus_proper: Proper (Rle ==> Rle ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.


Lemma Rmax_INR a b: Rmax (INR a) (INR b) = INR (max a b).
Proof.
  apply Rmax_case_strong; intros ?%INR_le; f_equal;
    [ rewrite Max.max_l // | rewrite Max.max_r //].
Qed.
