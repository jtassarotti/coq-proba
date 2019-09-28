Require Import Reals Psatz Omega ClassicalEpsilon.
From discprob.basic Require Export base Series_Ext order bigop_ext sval Reals_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From Coquelicot Require Export Rcomplements Rbar Series Lim_seq Hierarchy Markov Continuity.
From stdpp Require Export base.

Definition le_prop {X} (P1 P2: X → Prop) :=
  ∀ x, P1 x → P2 x.

Definition eq_prop {X} (P1 P2: X → Prop) :=
  ∀ x, P1 x ↔ P2 x.

Lemma le_prop_antisym {X} (P1 P2: X → Prop) :
  le_prop P1 P2 → le_prop P2 P1 → eq_prop P1 P2.
Proof. firstorder. Qed.

Global Instance le_prop_Transitivite {X}: Transitive (@le_prop X).
Proof. rewrite /le_prop => ??? Heq1 Heq2 x. intros. by apply Heq2, Heq1. Qed.
Global Instance le_prop_Reflexive {X}: Reflexive (@le_prop X).
Proof. rewrite /le_prop //=. Qed.

Global Instance eq_prop_Transitivite {X}: Transitive (@eq_prop X).
Proof. rewrite /eq_prop => ??? Heq1 Heq2 x. by rewrite Heq1 Heq2.  Qed.
Global Instance eq_prop_Reflexive {X}: Reflexive (@eq_prop X).
Proof. rewrite /eq_prop //=. Qed.
Global Instance eq_prop_Symmetry {X}: Symmetric (@eq_prop X).
Proof. rewrite /eq_prop => ?? Heq x. by rewrite Heq. Qed.
Global Instance eq_prop_Equiv {X} : Equiv (X → Prop) := eq_prop.
Global Instance eq_prop_Equivalence {X}: Equivalence (@eq_prop X).
Proof. split; apply _. Qed. 

Global Instance le_prop_proper {A: Type} : Proper (@eq_prop A ==> @eq_prop A ==> iff) (@le_prop A).
Proof. firstorder. Qed.

Definition union {A: Type} X Y : A → Prop :=
  λ a, (X a ∨ Y a).
Definition intersect {A: Type} X Y : A → Prop :=
  λ a, (X a ∧ Y a).
Definition compl {A: Type} X : A → Prop :=
  λ a, ¬ (X a).
Definition set_minus {A: Type} X Y : A → Prop :=
  λ a, X a ∧ ¬ Y a.
Definition unionF {A: Type} {I: Type} (U: I → (A → Prop)) : A → Prop :=
  λ a, ∃ i, U i a.
Definition unionL {A: Type} (l: list (A → Prop)) : A → Prop :=
  λ a, ∃ U, In U l ∧ U a.
Definition intersectF {A: Type} {I: Type} (U: I → (A → Prop)) : A → Prop :=
  λ a, ∀ i, U i a.
Definition disjoint {A: Type} (X Y: A → Prop) :=
  ∀ a, ¬ (X a ∧ Y a).
Definition empty_set {A: Type} : A → Prop := λ _, False.
Definition singleton {A: Type} a : A → Prop  := λ x, x = a.

Global Instance empty_Empty {A} : Empty (A → Prop) := @empty_set A.
Global Instance union_Union {A} : Union (A → Prop) := @union A.
Global Instance intersect_Intersection {A} : Intersection (A → Prop) := @intersect A.
Global Instance set_minus_Difference {A} : Difference (A → Prop) := @set_minus A.
Global Instance le_prop_SubsetEq {A} : SubsetEq (A → Prop) := @le_prop A.
Global Instance disjoint_Disjoint {A} : Disjoint (A → Prop) := @disjoint A.
Global Instance singleton_Singleton {A} : Singleton A (A → Prop) := @singleton A.

Definition disjointF {A: Type} {I: Type} (U: I → (A → Prop)) :=
  ∀ i j, i ≠ j → U i ## U j.

Lemma mono_proper2 {A: Type} op :
  Proper (@le_prop A ==> @le_prop A ==> @le_prop A) op →
  Proper (@eq_prop A ==> @eq_prop A ==> @eq_prop A) op.
Proof.
  intros Hle U U' HeqU V V' HeqV.
  apply le_prop_antisym; apply Hle; rewrite ?HeqU ?HeqV; reflexivity.
Qed.

Global Instance union_mono {A: Type} :
  Proper (@le_prop A ==> @le_prop A ==> @le_prop A) union.
Proof. firstorder. Qed.
Global Instance union_proper {A: Type} :
  Proper (@eq_prop A ==> @eq_prop A ==> @eq_prop A) union := mono_proper2 union _.
  
Global Instance intersect_mono {A: Type} :
  Proper (@le_prop A ==> @le_prop A ==> @le_prop A) intersect.
Proof. firstorder. Qed.
Global Instance intersect_proper {A: Type} :
  Proper (@eq_prop A ==> @eq_prop A ==> @eq_prop A) intersect := mono_proper2 intersect _.

Global Instance compl_anti {A: Type} :
  Proper (@le_prop A --> @le_prop A) compl.
Proof. firstorder. Qed.
Global Instance compl_proper {A: Type} :
  Proper (@eq_prop A ==> @eq_prop A) compl.
Proof. firstorder. Qed.

Global Instance set_minus_mono {A: Type} :
  Proper (@le_prop A ==> @le_prop A --> @le_prop A) set_minus.
Proof. firstorder. Qed.
Global Instance set_minus_proper {A: Type} :
  Proper (@eq_prop A ==> @eq_prop A --> @eq_prop A) set_minus.
Proof. firstorder. Qed.

Lemma union_intersect_l {A: Type} (U V Z: A → Prop) :
  U ∪ (V ∩ Z) ≡ (U ∪ V) ∩ (U ∪ Z).
Proof. firstorder. Qed.

Lemma union_intersectF_l {A: Type} {I} (U : A → Prop) Vs :
  U ∪ (intersectF Vs) ≡ intersectF (λ i : I, U ∪ Vs i).
Proof.
  intros x; split.
  - intros [Hu|Hinter] => i; by [left|right].
  - intros Hinter. 
    destruct (Classical_Prop.classic (U x)); auto.
    * by left.
    * right => i. destruct (Hinter i); eauto.
      intuition.
Qed.

Lemma intersect_union_l {A: Type} (U V Z: A → Prop) :
 U ∩ (V ∪ Z) ≡ (U ∩ V) ∪ (U ∩ Z).
Proof. firstorder. Qed. 

Lemma intersect_unionF_l {A: Type} {I} (U : A → Prop) Vs :
  U ∩ (unionF Vs) ≡ unionF (λ i : I, U ∩ Vs i).
Proof.
  intros x; split.
  - intros (HU&(i&?)). exists i; split; eauto.
  - intros (i&(?&?)).
    split; auto. exists i. done.
Qed.

Global Instance union_assoc {A: Type} : Assoc (≡) (@union A).
Proof. firstorder. Qed.
  
Global Instance intersect_assoc {A: Type} : Assoc (≡) (@intersect A).
Proof. firstorder. Qed.

Global Instance union_comm {A: Type} : Comm (≡) (@union A).
Proof. firstorder. Qed.

Global Instance intersect_comm {A: Type} : Comm (≡) (@intersect A).
Proof. firstorder. Qed.

Lemma union_compl {A: Type} (U: A → Prop) :
  U ∪ (compl U) ≡ (λ _, True).
Proof.
  intros x; split; rewrite /union/compl; intuition.
  apply Classical_Prop.classic.
Qed.

Lemma compl_top {A: Type} :
  (compl (λ _ : A , True)) ≡ ∅.
Proof. firstorder. Qed.

Lemma compl_empty {A: Type} :
  (compl ∅) ≡ (λ _ : A, True).
Proof. firstorder. Qed.

Lemma compl_involutive {A: Type} (U: A → Prop):
  compl (compl U) ≡ U.
Proof. rewrite /compl//=. intros x; split; auto. apply Classical_Prop.NNPP. Qed.

Lemma compl_union {A: Type} (U1 U2: A → Prop):
  compl (U1 ∪ U2) ≡ (compl U1) ∩ (compl U2).
Proof. firstorder. Qed.

Lemma compl_intersect {A: Type} (U1 U2: A → Prop):
  compl (U1 ∩ U2) ≡ (compl U1) ∪ (compl U2).
Proof.
  split.
  - intros Hneg. by apply Classical_Prop.not_and_or.
  - firstorder.
Qed.
 
Lemma intersect_top {A: Type} (U: A → Prop) :
  U ∩ (λ _, True) ≡ U.
Proof. firstorder. Qed.

Lemma set_minus_union_complement {A: Type} (X Y: A → Prop) :
  X ∖ Y ≡ (X ∩ (compl Y)).
Proof. firstorder. Qed.

Lemma set_minus_union_complement' {A: Type} (X Y: A → Prop) :
  set_minus X Y ≡ (X ∩ (compl Y)).
Proof. firstorder. Qed.

Lemma disjoint_comm {A: Type} (X Y: A → Prop):
  X ## Y ↔ Y ## X.
Proof. firstorder. Qed.

Lemma disjoint_empty_set_l {A: Type} (X: A → Prop):
  ∅ ## X.
Proof. firstorder. Qed.

Lemma disjoint_empty_set_r {A: Type} (X: A → Prop):
  X ## ∅.
Proof. firstorder. Qed. 

Lemma disjoint_set_minus {A: Type} (X Y: A → Prop) :
 (X ∖ Y) ## Y.
Proof. firstorder. Qed. 

Lemma disjoint_elim {A: Type} (U1 U2: A → Prop) x :
  U1 ## U2 → U1 x → ¬ U2 x.
Proof. firstorder. Qed.

Lemma le_minus_union {A: Type} (X Y: A → Prop) :
  X ⊆ Y → Y ∖ X ∪ X ≡ Y.
Proof.
  intros Hle; split.
  - intros [(?&?)|Hx] => //=.
    apply Hle; eauto.
  - intros HY. destruct (Classical_Prop.classic (X x)) as [HX|HnX]; by [left | right].
Qed.

Global Instance union_empty_RightId {A: Type} : RightId (≡) (@empty_set A) union.
Proof. firstorder. Qed.
Global Instance union_empty_LeftId {A: Type} : LeftId (≡) (@empty_set A) union.
Proof. firstorder. Qed.
Global Instance union_top_RightAbsorb {A: Type} : RightAbsorb (≡) (λ _ : A, True) union.
Proof. firstorder. Qed.
Global Instance union_top_LeftAbsorb {A: Type} : LeftAbsorb (≡) (λ _ : A, True) union.
Proof. firstorder. Qed.

Global Instance intersect_top_RightId {A: Type} : RightId (≡) (λ _ : A, True) intersect.
Proof. firstorder. Qed.
Global Instance intersect_top_LeftId {A: Type} : LeftId (≡) (λ _ : A, True) intersect.
Proof. firstorder. Qed.
Global Instance intersect_empty_RightAbsorb {A: Type} : RightAbsorb (≡) (@empty_set A) intersect.
Proof. firstorder. Qed.
Global Instance intersect_empty_LeftAbsorb {A: Type} : LeftAbsorb (≡) (@empty_set A) intersect.
Proof. firstorder. Qed.

Hint Resolve disjoint_empty_set_l disjoint_empty_set_r disjoint_set_minus.

Section diff_below.
Context {A: Type}.
Definition diff_below (Us: nat → A → Prop) :=
  (λ i, Us i ∩ (λ x, ∀ i', (i' < i)%nat → ¬ Us i' x)).

Lemma diff_below_unionF Us:
  unionF Us ≡ unionF (diff_below Us).
Proof.
  intros x; split.
  - intros (i&Hin). clear -Hin.
    induction i using lt_wf_ind.
    * destruct (Classical_Prop.classic  (∃ i', (i' < i)%nat ∧ Us i' x)) as [(i'&(?&?))|Hne].
      ** eauto.
      ** exists i; split; auto. intros i' ? HU. apply Hne; eauto. 
  - clear. firstorder.
Qed.

Lemma diff_below_incr_sub Us j k:
  (∀ j, Us j ⊆ Us (S j)) →
  (j <= k)%nat → diff_below Us j ⊆ Us k.
Proof.
  intros Hsub. induction 1.
  { induction j => //=; clear; firstorder. }
  etransitivity; eauto.
Qed.

Lemma diff_below_disjoint Us:
  disjointF (diff_below Us).
Proof.
  cut (∀ j k: nat, (j < k)%nat → (diff_below Us j ## diff_below Us k)).
  { intros Hlt j k Hneq. assert (j < k ∨ k < j)%nat as [|] by omega; eauto.
      rewrite disjoint_comm. eauto. }
  intros j k Hlt. destruct k. omega. 
  rewrite //=. intros z. assert (Hle: (j <= k)%nat) by omega.
  rewrite /diff_below.
  intros [Hdb1 Hdb2]. 
  exfalso. destruct Hdb2 as [Hsat Hfalse]. eapply Hfalse; eauto.
  destruct Hdb1; eauto.
Qed.

Lemma diff_below_fin_union (Us: nat → A → Prop) i:
  (∀ j, Us j ⊆ Us (S j)) →
  Us i ≡ (λ x, ∃ j, (j <= i)%nat ∧ diff_below Us j x).
Proof.
  intros Hbelow x; split.
  - intros Hin. clear -Hin.
    induction i as [i Hih] using lt_wf_ind.
    * destruct (Classical_Prop.classic  (∃ i', (i' < i)%nat ∧ Us i' x)) as [(i'&(?&?))|Hne].
      ** edestruct (Hih i') as (j&?&?); eauto. exists j. split; auto. omega.
      ** exists i; split; auto. rewrite /diff_below; split; auto.
         intros ?? HU. eapply Hne. eauto.
  - intros (j&?&?). eapply diff_below_incr_sub; eauto.
Qed.
End diff_below.

  

Definition eq_fun {A B} (f: A → B) (g: A → B) :=
  ∀ x, f x = g x.

Global Instance eq_fun_Transitivite {X Y}: Transitive (@eq_fun X Y).
Proof. rewrite /eq_fun => ??? Heq1 Heq2 x. by rewrite Heq1 Heq2.  Qed.
Global Instance eq_fun_Reflexive {X Y}: Reflexive (@eq_fun X Y).
Proof. rewrite /eq_fun //=. Qed.
Global Instance eq_fun_Symmetry {X Y}: Symmetric (@eq_fun X Y).
Proof. rewrite /eq_fun => ?? Heq x. by rewrite Heq. Qed.
Global Instance eq_fun_Equivalence {X Y}: Equivalence (@eq_fun X Y).
Proof. split; apply _. Qed. 

Definition fun_inv {A B : Type} (f: A → B) : (B → Prop) → (A → Prop) :=
  λ U, λ a, U (f a).

(*
Global Instance fun_inv_proper {A B: Type} f :
  Proper (@eq_prop B ==> @eq_prop A) (fun_inv f).
Proof.
  intros U U' Heq x; rewrite /fun_inv. apply Heq.
Qed.
*)
Global Instance fun_inv_proper {A B: Type}:
  Proper (@eq_fun A B ==> eq_prop ==> eq_prop) (@fun_inv A B).
Proof.
  intros f1 f2 Heqf U U' HeqU x; rewrite /fun_inv. rewrite Heqf. apply HeqU.
Qed.

Lemma fun_inv_compl {A B: Type} (f: A → B) U :
  eq_prop (fun_inv f (compl U)) (compl (fun_inv f U)).
Proof. done. Qed.

Lemma fun_inv_unionF {A B I: Type} (f: A → B) F :
  eq_prop (fun_inv f (unionF F)) (unionF (λ i : I, fun_inv f (F i))).
Proof. done. Qed.

Lemma fun_inv_empty {A B: Type} (f: A → B) :
  eq_prop (fun_inv f empty_set) empty_set.
Proof. done. Qed.

Lemma fun_inv_disjointF {I} {A B: Type} (f: A → B) Us:
  disjointF Us → disjointF (λ i : I, fun_inv f (Us i)).
Proof.
  intros Hdisj i j Hneq z (Hin1&Hin2).
  eapply (Hdisj i j Hneq (f z)); eauto.
Qed.


Definition fun_img {A B: Type} (f: A → B) (U: A → Prop) :=
  λ y, ∃ x, U x ∧ f x = y.

Lemma fun_img_id {A: Type} (U : A → Prop): fun_img id U ≡ U.
Proof. firstorder. Qed.

Lemma fun_img_union {A B: Type} (f: A → B) (Us: nat → A → Prop):
    eq_prop (fun_img f (unionF Us))
            (unionF (λ i : nat, fun_img f (Us i))).
Proof.
  intros z. split.
  * intros (x&Hunion&Heq').
    destruct Hunion as (i&Hi). exists i.
    eexists; split; eauto.
  * intros (i&(x&Hi&Heq)).
    exists x. split; auto. exists i; done.
Qed.

Definition img_union := @fun_img_union.

(*
Lemma fun_img_compl_inj {A B: Type} (f: A → B) U :
  (∀ x y, f x = f y → x = y) →
  eq_prop (fun_img f (compl U)) (compl (fun_img f U)).
Proof.
  intros Hinj z. split.
  * rewrite /fun_img.  intros (x&Hcompl&Hf).
    subst. intros Hfalse. destruct Hfalse as (a&HU&Himg).
    eapply Hinj in Himg. subst; eauto.
  * rewrite /fun_img. intros Hcompl. apply Classical_Prop.NNPP.
    intros Hnot. eapply Hcompl. 
    apply Classical_Prop.NNPP. intros Hnot'. eapply Hnot.; eapply Hcompl.
    eapply H
*)

Definition bij_inv {A B: Type} (f: A → B) (Hinj: ∀ x y, f x = f y → x = y) (Hsurj: ∀ y, ∃ x, f x = y):
  B → A.
Proof.
  intros a2. specialize (Hsurj a2).
  apply constructive_indefinite_description in Hsurj as (x&?). exact x.
Defined.

Lemma bij_inv_img {A B: Type} (f: A → B) Hinj Hsurj U:
  fun_img (bij_inv f Hinj Hsurj) U ≡ fun_inv f U.
Proof.
  intros x. rewrite /fun_img/fun_inv/bij_inv; split.
  - intros (y&HU&?). destruct constructive_indefinite_description. congruence.
  - intros HU. exists (f x); split; eauto.
    destruct constructive_indefinite_description. eapply Hinj; eauto.
Qed.

Lemma img_bij_inv {A B: Type} (f: A → B) Hinj Hsurj U:
  fun_img f U ≡ fun_inv (bij_inv f Hinj Hsurj) U.
Proof.
  intros x. rewrite /fun_img/fun_inv/bij_inv; split.
  - intros (y&HU&?). destruct constructive_indefinite_description as (y'&?).
    assert (y = y').
    { eapply Hinj; eauto. congruence. }
    intros; subst; eauto.
  - intros HU. 
    destruct constructive_indefinite_description as (x'&?).
    exists x'; split; eauto.
Qed.
