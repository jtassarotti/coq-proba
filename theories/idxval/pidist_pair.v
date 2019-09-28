From discprob.basic Require Import base sval order monad bigop_ext nify.
From discprob.idxval Require Import pival_dist pival extrema.
From discprob.prob Require Import prob countable finite stochastic_order.

Record pidist_couplingP {A1 A2} (Is1: pidist A1) (Is2: pidist A2) (P: A1 → A2 → Prop) : Type :=
  mkCoupling { pc_witness :> pidist {xy: A1 * A2 | P (fst xy) (snd xy)};
     pc_proj1: eq_pidist Is1 (x ← pc_witness; mret (fst (sval x)));
     pc_proj2: eq_pidist Is2 (x ← pc_witness; mret (snd (sval x)));
     }.
Require Import Reals Psatz Omega.

Definition lsupport {A1 A2 Is1 Is2 P} (Icouple: pidist_couplingP Is1 Is2 P) (y: A2) :=
  { x : A1 |  ∃ I Hpf i, pival.In I Icouple ∧ ival.ind I i = (exist _ (x, y) Hpf)
                         ∧ ival.val I i > 0 }.
Definition rsupport {A1 A2 Is1 Is2 P} (Icouple: pidist_couplingP Is1 Is2 P) (x: A1) :=
  { y : A2 |  ∃ I Hpf i, pival.In I Icouple ∧ ival.ind I i = (exist _ (x, y) Hpf)
                         ∧ ival.val I i > 0 }.

Lemma pidist_coupling_sym {A1 A2} (Is1: pidist A1) (Is2: pidist A2) P
      (Ic: pidist_couplingP Is1 Is2 P): pidist_couplingP Is2 Is1 (λ x y, P y x).
Proof.
  destruct Ic as [Ic Hp1 Hp2].
  unshelve (eexists).
  { refine (mbind _ Ic). intros ((x&y)&HP).
    refine (mret (exist _ (y, x) _)); auto. }
  * setoid_rewrite Hp2. setoid_rewrite pidist_assoc; apply pidist_bind_congr; first by reflexivity.
    intros ((x&y)&Hpf). setoid_rewrite pidist_left_id => //=. reflexivity.
  * setoid_rewrite Hp1. setoid_rewrite pidist_assoc; apply pidist_bind_congr; first by reflexivity.
    intros ((x&y)&Hpf). setoid_rewrite pidist_left_id => //=. reflexivity.
Qed.
    
Lemma pidist_coupling_eq {A} (Is1 Is2: pidist A)
      (Ic: pidist_couplingP Is1 Is2 (λ x y, x = y)): eq_pidist Is1 Is2.
Proof.
  destruct Ic as [Ic Hp1 Hp2].
  setoid_rewrite Hp1. setoid_rewrite Hp2.
  apply pidist_bind_congr; first by reflexivity.
  intros ((x&y)&Heq) => //=. rewrite //= in Heq; subst; reflexivity.
Qed.

Lemma pidist_coupling_ext {A B} (Is1 Is1': pidist A) (Is2 Is2': pidist B) (P P': A → B → Prop) :
  eq_pidist Is1 Is1' →
  eq_pidist Is2 Is2' →
  (∀ x y, P x y ↔ P' x y) →
  pidist_couplingP Is1 Is2 P →
  pidist_couplingP Is1' Is2' P'.
Proof.
  intros Heq1 Heq2 HP [pc_wit Hproj1 Hproj2].
  unshelve (econstructor).
  - refine (x ← pc_wit; mret (exist _ (proj1_sig x) _)).
    { destruct x as (?&?). eapply HP => //=. }
  - rewrite -Heq1 Hproj1. rewrite pidist_assoc.
    eapply pidist_bind_congr; first reflexivity.
    intros ((x&y)&HPxy). rewrite pidist_left_id => //=; reflexivity.
  - rewrite -Heq2 Hproj2. rewrite pidist_assoc.
    eapply pidist_bind_congr; first reflexivity.
    intros ((x&y)&HPxy). rewrite pidist_left_id => //=; reflexivity.
Qed.

Lemma pidist_coupling_eq_inv {A} (Is1 Is2: pidist A):
      eq_pidist Is1 Is2 →
      pidist_couplingP Is1 Is2 (λ x y, x = y).
Proof.
  intros Heq.
  unshelve (econstructor).
  - refine (x ← Is1; mret (exist _ (x, x) _)) => //=.
  - rewrite pidist_assoc. rewrite -[a in eq_pidist a _]pidist_right_id. 
    eapply pidist_bind_congr; first reflexivity.
    intros a. rewrite pidist_left_id => //=.
    reflexivity.
  - rewrite Heq. rewrite pidist_assoc. rewrite -[a in eq_pidist a _]pidist_right_id. 
    eapply pidist_bind_congr; first reflexivity.
    intros a. rewrite pidist_left_id => //=.
    reflexivity.
Qed.

Lemma pidist_coupling_Ex_min {A1 A2} f g (Is1 : pidist A1) (Is2: pidist A2)
      (Ic: pidist_couplingP Is1 Is2 (λ x y, f x ≤ g y)):
  ex_Ex_extrema f Is1 →
  Rbar_le (Ex_min f Is1) (Ex_min g Is2).
Proof.
  intros Hex.
  destruct Ic as [Ic Hp1 Hp2].
  setoid_rewrite Hp1. setoid_rewrite Hp2.
  apply Ex_min_bind_le.
  *  rewrite /mbind/base.mbind in Hp1 *. rewrite -Hp1 //.
  * intros (?&?). rewrite ?Ex_min_mret => //=.
Qed.

Lemma pidist_coupling_Ex_max {A1 A2} f g (Is1 : pidist A1) (Is2: pidist A2)
      (Ic: pidist_couplingP Is1 Is2 (λ x y, f x ≤ g y)):
  ex_Ex_extrema g Is2 →
  Rbar_le (Ex_max f Is1) (Ex_max g Is2).
Proof.
  intros Hex.
  destruct Ic as [Ic Hp1 Hp2].
  setoid_rewrite Hp1. setoid_rewrite Hp2.
  apply Ex_max_bind_le.
  *  rewrite /mbind/base.mbind in Hp2 *. rewrite -Hp2 //.
  * intros (?&?). rewrite ?Ex_max_mret => //=.
Qed.

Lemma pidist_coupling_bind {A1 A2 B1 B2} (f1: A1 → pidist B1) (f2: A2 → pidist B2)
      Is1 Is2 P Q (Ic: pidist_couplingP Is1 Is2 P):
  (∀ x y, P x y → pidist_couplingP (f1 x) (f2 y) Q) →
  pidist_couplingP (mbind f1 Is1) (mbind f2 Is2) Q.
Proof.
  intros Hfc.
  destruct Ic as [Ic Hp1 Hp2].
  unshelve (eexists).
  { refine (xy ← Ic; _). destruct xy as ((x&y)&HP).
    exact (Hfc _ _ HP).
  }
  - setoid_rewrite Hp1; setoid_rewrite pidist_assoc;
      apply pidist_bind_congr; first by reflexivity.
    intros ((x&y)&HP). setoid_rewrite pidist_left_id => //=.
    destruct (Hfc x y); auto.
  - setoid_rewrite Hp2; setoid_rewrite pidist_assoc;
      apply pidist_bind_congr; first by reflexivity.
    intros ((x&y)&HP). setoid_rewrite pidist_left_id => //=.
    destruct (Hfc x y); auto.
Qed.

Lemma pidist_coupling_mret {A1 A2} x y (P: A1 → A2 → Prop):
  P x y →
  pidist_couplingP (mret x) (mret y) P.
Proof.
  intros HP. exists (mret (exist _ (x, y) HP)); setoid_rewrite pidist_left_id => //=; reflexivity.
Qed.

Lemma pidist_coupling_plus {A1 A2} p Hpf Is1 Is2 Is1' Is2' (P: A1 → A2 → Prop):
  pidist_couplingP Is1 Is2 P →
  pidist_couplingP Is1' Is2' P →
  pidist_couplingP (pidist_plus p Hpf Is1 Is1') (pidist_plus p Hpf Is2 Is2') P.
Proof.
  intros [Ic Hproj1 Hproj2].
  intros [Ic' Hproj1' Hproj2'].
  exists (pidist_plus p Hpf Ic Ic').
  - setoid_rewrite Hproj1. setoid_rewrite Hproj1'.
    symmetry; apply pidist_plus_bind.
  - setoid_rewrite Hproj2. setoid_rewrite Hproj2'.
    symmetry; apply pidist_plus_bind.
Qed.
    
Lemma pidist_coupling_union {A1 A2} Is1 Is2 Is1' Is2' (P: A1 → A2 → Prop):
  pidist_couplingP Is1 Is2 P →
  pidist_couplingP Is1' Is2' P →
  pidist_couplingP (pidist_union Is1 Is1') (pidist_union Is2 Is2') P.
Proof.
  intros [Ic Hproj1 Hproj2].
  intros [Ic' Hproj1' Hproj2'].
  exists (pidist_union Ic Ic').
  - setoid_rewrite Hproj1. setoid_rewrite Hproj1'.
    symmetry; apply pidist_union_bind.
  - setoid_rewrite Hproj2. setoid_rewrite Hproj2'.
    symmetry; apply pidist_union_bind.
Qed.

Lemma pidist_coupling_join {Idx1} {A1 A2} (i1: Idx1)
      (Iss1: Idx1 → pidist A1) (Is2: pidist A2) (P: A1 → A2 → Prop):
  (∀ i1', pidist_couplingP (Iss1 i1') Is2 P) →
  pidist_couplingP (pidist_join i1 Iss1) Is2 P.
Proof.
  intros Ics.
  exists (pidist_join i1 (λ i, Ics i)). 
  - setoid_rewrite pidist_join_bind. split.
    * intros I (i&Hin).
      destruct (Ics i) as [Ic Hproj1 Hproj2] eqn:Heqi.
      destruct Hproj1 as (Hle1a&Hle1b).
      destruct (Hle1a _ Hin) as (I'&Heq'&Hin').
      exists I'. split; auto.
      exists i; eauto. rewrite Heqi => //=.
    * intros I (i&Hin).
      destruct (Ics i) as [Ic Hproj1 Hproj2] eqn:Heqi.
      destruct Hproj1 as (Hle1a&Hle1b).
      destruct (Hle1b _ Hin) as (I'&Heq'&Hin').
      exists I'. split; auto.
      exists i; eauto.
  - setoid_rewrite pidist_join_bind. split.
    * intros I Hin.
      destruct (Ics i1) as [Ic Hproj1 Hproj2] eqn:Heqi.
      destruct Hproj2 as (Hle1a&Hle1b).
      destruct (Hle1a _ Hin) as (I'&Heq'&Hin').
      exists I'. split; auto.
      exists i1; eauto. rewrite Heqi => //=.
    * intros I (i&Hin).
      destruct (Ics i) as [Ic Hproj1 Hproj2] eqn:Heqi.
      destruct Hproj2 as (Hle1a&Hle1b).
      destruct (Hle1b _ Hin) as (I'&Heq'&Hin').
      exists I'. split; auto.
Qed.