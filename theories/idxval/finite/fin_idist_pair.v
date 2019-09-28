
From discprob.basic Require Import base sval order monad bigop_ext nify.
From discprob.idxval Require Import fin_ival_dist fin_ival.
From discprob.prob Require Import prob countable finite stochastic_order.

Record ivdist_couplingP {A1 A2} (Is1: ivdist A1) (Is2: ivdist A2) (P: A1 → A2 → Prop) : Type :=
  mkCoupling { pc_witness :> ivdist {xy: A1 * A2 | P (fst xy) (snd xy)};
     pc_proj1: eq_ivd Is1 (x ← pc_witness; mret (fst (sval x)));
     pc_proj2: eq_ivd Is2 (x ← pc_witness; mret (snd (sval x)));
     }.
Require Import Reals Psatz Omega.

Lemma ivdist_coupling_sym {A1 A2} (Is1: ivdist A1) (Is2: ivdist A2) P
      (Ic: ivdist_couplingP Is1 Is2 P): ivdist_couplingP Is2 Is1 (λ x y, P y x).
Proof.
  destruct Ic as [Ic Hp1 Hp2].
  unshelve (eexists).
  { refine (mbind _ Ic). intros ((x&y)&HP).
    refine (mret (exist _ (y, x) _)); auto. }
  * setoid_rewrite Hp2. setoid_rewrite ivd_assoc. apply ivd_bind_congr; first by reflexivity.
    intros ((x&y)&Hpf). setoid_rewrite ivd_left_id => //=. reflexivity.
  * setoid_rewrite Hp1. setoid_rewrite ivd_assoc; apply ivd_bind_congr; first by reflexivity.
    intros ((x&y)&Hpf). setoid_rewrite ivd_left_id => //=. reflexivity.
Qed.
    
Lemma ivdist_coupling_eq {A} (Is1 Is2: ivdist A)
      (Ic: ivdist_couplingP Is1 Is2 (λ x y, x = y)): eq_ivd Is1 Is2.
Proof.
  destruct Ic as [Ic Hp1 Hp2].
  setoid_rewrite Hp1. setoid_rewrite Hp2.
  apply ivd_bind_congr; first by reflexivity.
  intros ((x&y)&Heq) => //=. rewrite //= in Heq; subst; reflexivity.
Qed.

Lemma ivdist_coupling_bind {A1 A2 B1 B2} (f1: A1 → ivdist B1) (f2: A2 → ivdist B2)
      Is1 Is2 P Q (Ic: ivdist_couplingP Is1 Is2 P):
  (∀ x y, P x y → ivdist_couplingP (f1 x) (f2 y) Q) →
  ivdist_couplingP (mbind f1 Is1) (mbind f2 Is2) Q.
Proof.
  intros Hfc.
  destruct Ic as [Ic Hp1 Hp2].
  unshelve (eexists).
  { refine (xy ← Ic; _). destruct xy as ((x&y)&HP).
    exact (Hfc _ _ HP).
  }
  - setoid_rewrite Hp1; setoid_rewrite ivd_assoc;
      apply ivd_bind_congr; first by reflexivity.
    intros ((x&y)&HP). setoid_rewrite ivd_left_id => //=.
    destruct (Hfc x y); auto.
  - setoid_rewrite Hp2; setoid_rewrite ivd_assoc;
      apply ivd_bind_congr; first by reflexivity.
    intros ((x&y)&HP). setoid_rewrite ivd_left_id => //=.
    destruct (Hfc x y); auto.
Qed.

Lemma ivdist_coupling_mret {A1 A2} x y (P: A1 → A2 → Prop):
  P x y →
  ivdist_couplingP (mret x) (mret y) P.
Proof.
  intros HP. exists (mret (exist _ (x, y) HP)); setoid_rewrite ivd_left_id => //=; reflexivity.
Qed.

Lemma ivdist_coupling_plus {A1 A2} p Hpf Is1 Is2 Is1' Is2' (P: A1 → A2 → Prop):
  ivdist_couplingP Is1 Is2 P →
  ivdist_couplingP Is1' Is2' P →
  ivdist_couplingP (ivdplus p Hpf Is1 Is1') (ivdplus p Hpf Is2 Is2') P.
Proof.
  intros [Ic Hproj1 Hproj2].
  intros [Ic' Hproj1' Hproj2'].
  exists (ivdplus p Hpf Ic Ic').
  - setoid_rewrite Hproj1. setoid_rewrite Hproj1'.
    symmetry; apply ivd_plus_bind.
  - setoid_rewrite Hproj2. setoid_rewrite Hproj2'.
    symmetry; apply ivd_plus_bind.
Qed.