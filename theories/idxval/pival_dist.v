(* Here we consider pivals which are sets of ivals that can be interpreted as distributions *)

From discprob.basic Require Import base sval order monad bigop_ext nify.
Require Import Reals Psatz Omega.

Require ClassicalEpsilon.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
Global Set Bullet Behavior "Strict Subproofs".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype finset finfun bigop.

Local Open Scope R_scope.
From discprob.idxval Require Import ival pival ival_dist.
From discprob.prob Require Import prob countable finite stochastic_order.



(*
Record pidist (X: Type) := { choices :> list (ivdist X); nonempty : ∃ I, In I choices }.
*)
Record pidist (X: Type) := { pidist_pival :> pival X;
                             all_sum1: ∀ I, In I pidist_pival →
                                            is_series (countable_sum (val I)) 1
                           }.

Arguments pidist_pival {_}.
Arguments all_sum1 {_}.

Definition lift_In_pidist {X} {Is: pidist X} (I: ival X)  (Pf: In I Is) : ivdist X :=
  {| ivd_ival := I; val_sum1 := (all_sum1 Is I Pf) |}.


Definition eq_pidist {X} (Is1 Is2: pidist X) :=
  eq_pival Is1 Is2.
Definition le_pidist {X} (Is1 Is2: pidist X) :=
  le_pival Is1 Is2.

Global Instance eq_pidist_Transitivite {X}: Transitive (@eq_pidist X).
Proof. intros ???. apply eq_pival_trans. Qed.
Global Instance eq_pidist_Reflexive {X}: Reflexive (@eq_pidist X).
Proof. intros ?. apply eq_pival_refl. Qed.
Global Instance eq_pidist_Symmetry {X}: Symmetric (@eq_pidist X).
Proof. intros ??. apply eq_pival_sym. Qed.
Global Instance eq_pidist_Equivalence {X}: Equivalence (@eq_pidist X).
Proof. split; apply _. Qed.

Global Instance le_pidist_Transitivite {X}: Transitive (@le_pidist X).
Proof. intros ???. apply le_pival_trans. Qed.
Global Instance le_pidist_Reflexive {X}: Reflexive (@le_pidist X).
Proof. intros ?. apply le_pival_refl. Qed.
Global Instance le_pidist_proper {X}: Proper (@eq_pidist X ==> @eq_pidist X ==> iff) (@le_pidist X).
Proof. rewrite /eq_pidist/le_pidist//= => ?? Heq1 ?? Heq2.
       setoid_rewrite Heq1. setoid_rewrite Heq2.
       done.
Qed.

Definition eq_pidist_prob {X} (Is1 Is2: pidist X) :=
  eq_pival_prob Is1 Is2.
Definition le_pidist_prob {X} (Is1 Is2: pidist X) :=
  le_pival_prob Is1 Is2.

Global Instance eq_pidist_prob_Transitivite {X}: Transitive (@eq_pidist_prob X).
Proof. intros ???. apply eq_pival_prob_trans. Qed.
Global Instance eq_pidist_prob_Reflexive {X}: Reflexive (@eq_pidist_prob X).
Proof. intros ?. apply eq_pival_prob_refl. Qed.
Global Instance eq_pidist_prob_Symmetry {X}: Symmetric (@eq_pidist_prob X).
Proof. intros ??. apply eq_pival_prob_sym. Qed.
Global Instance eq_pidist_prob_Equivalence {X}: Equivalence (@eq_pidist_prob X).
Proof. split; apply _. Qed.

Global Instance le_pidist_prob_Transitivite {X}: Transitive (@le_pidist_prob X).
Proof. intros ???. apply le_pival_prob_trans. Qed.
Global Instance le_pidist_prob_Reflexive {X}: Reflexive (@le_pidist_prob X).
Proof. intros ?. apply le_pival_prob_refl. Qed.

Global Instance le_pidist_prob_proper {X}: Proper (@eq_pidist_prob X ==> @eq_pidist_prob X ==> iff) (@le_pidist_prob X).
Proof.
  rewrite /eq_pidist_prob/le_pidist_prob//= => ?? Heq1 ?? Heq2.
  setoid_rewrite Heq1. setoid_rewrite Heq2. done.
Qed.

Global Instance pidist_ret: MRet pidist.
refine(λ A x, {| pidist_pival := mret x;
                 all_sum1 := _ |}).
{ abstract (intros I Hin;
            rewrite Hin; apply: is_seriesC_bump; exact tt). }
Defined.

Lemma pidist_bind_aux {A B: Type} (f: A → pidist B) (Is: pidist A) :
  ∀ I : ival B, In I ((x ← pidist_pival Is; pidist_pival (f x)) : pival B)
                → is_series (countable_sum (val I)) 1.
Proof.
  intros I Hin.
  apply pival_mbind_in_inv in Hin as (Ix&h&Hpf&Hin&Hhspec&Heq).
  eapply eq_ival_series; eauto.
  rewrite //=.
  apply all_sum1 in Hin.
  eapply (ivd_bind_sum1' h (idxOf Ix)).
  - rewrite //=.
  - rewrite //=. intros. eapply all_sum1; eapply Hhspec; eauto.
Qed.

Global Instance pidist_bind: MBind pidist :=
 (λ A B f Is, {| pidist_pival := mbind (λ x, pidist_pival (f x)) (pidist_pival Is);
                     all_sum1 := pidist_bind_aux f Is |}).

Lemma pidist_assoc {A B C} (m: pidist A) (f: A → pidist B) (g: B → pidist C) :
  eq_pidist (mbind g (mbind f m)) (mbind (λ x, mbind g (f x)) m).
Proof.
  rewrite /eq_pidist. setoid_rewrite pival_assoc. reflexivity.
Qed.

Lemma pidist_left_id {A B: Type} (x: A) (f: A → pidist B):
  eq_pidist (mbind f (mret x)) (f x).
Proof.
  rewrite /eq_pidist. setoid_rewrite pival_left_id. reflexivity.
Qed.

Lemma pidist_right_id {A: Type} (m: pidist A):
  eq_pidist (mbind mret m) m.
Proof.
  rewrite /eq_pidist. setoid_rewrite pival_right_id. reflexivity.
Qed.

Lemma pidist_plus_aux {X} (p: R) (Hrange: 0 <= p <= 1) (Is1 Is2: pidist X) :
  ∀ I : ival X, In I (pplus (pscale p Is1) (pscale (1 - p) Is2)) →
                is_series (countable_sum (val I)) 1.
Proof.
  intros I Hin.
  destruct Hin as (I1&I2&Hin1&Hin2&Heq).
  rewrite Heq.
  destruct Hin1 as (I1'&Hin1%all_sum1&Heq1').
  destruct Hin2 as (I2'&Hin2%all_sum1&Heq2').
  subst.
  unshelve (eapply (ivdplus_sum1 p Hrange {| ivd_ival := I1' |} {| ivd_ival := I2' |})); eauto.
Qed.

Definition pidist_plus {X} (p: R) (Hrange: 0 <= p <= 1) (Is1 Is2: pidist X) : pidist X :=
  {| pidist_pival := pplus (pscale p Is1) (pscale (1 - p) Is2);
     all_sum1 := pidist_plus_aux p Hrange _ _ |}.

Definition pidist_union {X} (Is1 Is2: pidist X) : pidist X.
  refine {| pidist_pival := punion Is1 Is2;
            all_sum1 := _ |}.
  abstract (intros I [Hin|Hin]; by eapply all_sum1; eauto).
Defined.

Global Instance pidist_plus_mono:
  ∀ (X : Type) r Hpf, Proper (@le_pidist X ==> @le_pidist X ==> @le_pidist X) (pidist_plus r Hpf).
Proof.
  intros X r Hpf Is1 Is1' Hle1 Is2 Is2' Hle2.
  rewrite /le_pidist/pidist_plus//=.
  rewrite /le_pidist in Hle1, Hle2.
  setoid_rewrite Hle1. setoid_rewrite Hle2.
  reflexivity.
Qed.

Lemma pidist_plus_proper:
  ∀ (X : Type) r Hpf Hpf' (I1 I1' I2 I2': pidist X),
    eq_pidist I1 I1' →
    eq_pidist I2 I2' →
    eq_pidist (pidist_plus r Hpf I1 I2) (pidist_plus r Hpf' I1' I2').
Proof.
  intros X r Hpf Hpf' Is1 Is1' Is2 Is2' Hle1 Hle2.
  rewrite /eq_pidist/pidist_plus//=.
  rewrite /eq_pidist in Hle1, Hle2.
  setoid_rewrite Hle1. setoid_rewrite Hle2.
  reflexivity.
Qed.

Global Instance pidist_plus_proper_instance:
  ∀ (X : Type) r Hpf, Proper (@eq_pidist X ==> @eq_pidist X ==> @eq_pidist X) (pidist_plus r Hpf).
Proof.
  intros X r Hpf Is1 Is1' Heq1 Is2 Is2' Heq2.
  eapply pidist_plus_proper; eauto.
Qed.

Global Instance pidist_union_mono:
  ∀ (X : Type), Proper (@le_pidist X ==> @le_pidist X ==> @le_pidist X) (pidist_union).
Proof.
  intros X Is1 Is1' Hle1 Is2 Is2' Hle2.
  rewrite /pidist_union/le_pidist//=.
  rewrite /le_pidist in Hle1, Hle2.
  setoid_rewrite Hle1. setoid_rewrite Hle2.
  reflexivity.
Qed.

Global Instance pidist_union_proper:
  ∀ (X : Type), Proper (@eq_pidist X ==> @eq_pidist X ==> @eq_pidist X) (pidist_union).
Proof.
  intros X Is1 Is1' Hle1 Is2 Is2' Hle2.
  rewrite /pidist_union/eq_pidist//=.
  rewrite /eq_pidist in Hle1, Hle2.
  setoid_rewrite Hle1. setoid_rewrite Hle2.
  reflexivity.
Qed.

Global Instance pidist_bind_mono X Y :
  Proper (pointwise_relation X (@le_pidist Y) ==> @le_pidist X ==> @le_pidist Y) (pidist_bind X Y).
Proof. intros ?? ? ?? ?. eapply pival_bind_mono; eauto. Qed.

Global Instance pidist_bind_proper X Y :
  Proper (pointwise_relation X (@eq_pidist Y) ==> @eq_pidist X ==> @eq_pidist Y) (pidist_bind X Y).
Proof. intros ?? ? ?? ?. eapply pival_bind_proper; eauto. Qed.


Lemma pidist_union_comm:
  ∀ (X : Type) (Is1 Is2 : pidist X), eq_pidist (pidist_union Is1 Is2) (pidist_union Is2 Is1).
Proof. intros. rewrite /eq_pidist/pidist_union//=. apply punion_comm. Qed.

Lemma pidist_union_assoc:
  ∀ (X : Type) (Is1 Is2 Is3 : pidist X),
    eq_pidist (pidist_union Is1 (pidist_union Is2 Is3)) (pidist_union (pidist_union Is1 Is2) Is3).
Proof. intros. rewrite /eq_pidist/pidist_union//=. apply punion_assoc. Qed.

Lemma pidist_union_le: ∀ (X : Type) (Is Is' : pidist X), le_pidist Is (pidist_union Is Is').
Proof. intros. rewrite /eq_pidist/pidist_union//=. apply punion_le. Qed.

Lemma pidist_union_le_l:
  ∀ (X : Type) (Is Is1 Is2 : pidist X),
    le_pidist Is Is1 →
    le_pidist Is (pidist_union Is1 Is2).
Proof. intros. rewrite /eq_pidist/pidist_union//=. by apply punion_le_l. Qed.

Lemma pidist_union_le_r:
  ∀ (X : Type) (Is Is1 Is2 : pidist X),
    le_pidist Is Is2 →
    le_pidist Is (pidist_union Is1 Is2).
Proof. intros. rewrite /eq_pidist/pidist_union//=. by apply punion_le_r. Qed.

Lemma pidist_union_le_id:
  ∀ (X : Type) (Is1 Is2 : pidist X),
    le_pidist Is1 Is2 → eq_pidist (pidist_union Is1 Is2) Is2.
Proof. intros. rewrite /eq_pidist/pidist_union//=. by apply punion_le_id. Qed.

Lemma pidist_union_idemp: ∀ (X : Type) (Is : pidist X), eq_pidist (pidist_union Is Is) Is.
Proof. intros. rewrite /eq_pidist/pidist_union//=. by apply punion_idemp. Qed.

Lemma pidist_plus_union_distrib (X : Type) r Hpf (Is Is1 Is2 : pidist X):
    eq_pidist (pidist_plus r Hpf Is (pidist_union Is1 Is2))
              (pidist_union (pidist_plus r Hpf Is Is1) (pidist_plus r Hpf Is Is2)).
Proof.
  rewrite /eq_pidist/pidist_union/pidist_plus//=.
  setoid_rewrite pscale_punion_distrib.
  setoid_rewrite <-pplus_punion_distrib.
  reflexivity.
Qed.

Lemma pidist_union_bind:
  ∀ (A B : Type) (m1 m2 : pidist A) (f : A → pidist B),
    eq_pidist (x ← pidist_union m1 m2; f x) (pidist_union (x ← m1; f x) (x ← m2; f x)).
Proof.
  intros A B m1 m2 f. rewrite /eq_pidist/pidist_union/pidist_bind//=.
  apply pival_union_bind.
Qed.

Lemma pidist_plus_bind:
  ∀ (A B : Type) p Hpf (m1 m2 : pidist A) (f : A → pidist B),
    eq_pidist (x ← pidist_plus p Hpf m1 m2; f x) (pidist_plus p Hpf (x ← m1; f x) (x ← m2; f x)).
Proof.
  intros A B p Hpf m1 m2 f.
  rewrite /eq_pidist. rewrite /pidist_plus/pidist_bind.
  setoid_rewrite pival_plus_bind.
  setoid_rewrite pival_scale_bind.
  reflexivity.
Qed.

Lemma pidist_bind_congr_le_supp {A B} (m1 m2: pidist A) (f1 f2: A → pidist B) :
  le_pidist m1 m2 →
  (∀ a, In_psupport a m1 → le_pidist (f1 a) (f2 a)) →
  le_pidist (x ← m1; f1 x) (x ← m2; f2 x).
Proof.
  intros Hlem Hlef.
  rewrite /le_pidist.
  apply pival_bind_congr_le_supp; eauto.
Qed.

Lemma pidist_bind_congr_le {A B} (m1 m2: pidist A) (f1 f2: A → pidist B) :
  le_pidist m1 m2 →
  (∀ a, le_pidist (f1 a) (f2 a)) →
  le_pidist (x ← m1; f1 x) (x ← m2; f2 x).
Proof.
  intros Hlem Hlef.
  rewrite /le_pidist.
  apply pival_bind_congr_le; eauto.
Qed.

Lemma pidist_bind_congr {A B} (m1 m2: pidist A) (f1 f2: A → pidist B) :
  eq_pidist m1 m2 →
  (∀ a, eq_pidist (f1 a) (f2 a)) →
  eq_pidist (x ← m1; f1 x) (x ← m2; f2 x).
Proof.
  intros Hlem Hlef.
  rewrite /le_pidist.
  apply pival_bind_congr; eauto.
Qed.

Definition dist_of_pidist {X} (I: ival X) (Is: pidist X) (Hin: In I Is) : distrib (idx I) :=
  dist_of_ivdist {| ivd_ival := I; val_sum1 := (all_sum1 Is I Hin) |}.

Definition rvar_of_pidist {X: eqType} (I: ival X) (Is: pidist X) (Hin: In I Is) : rvar _ X :=
  rvar_of_ivdist {| ivd_ival := I; val_sum1 := (all_sum1 Is I Hin) |}.

Lemma pidist_plus_in_inv {A} p Hpf (Is1 Is2: pidist A) I:
  In I (pidist_plus p Hpf Is1 Is2) →
  ∃ (I1 I2: ivdist A), In (ivd_ival I1) Is1 ∧ In (ivd_ival I2) Is2
                       ∧ I = (ivdplus p Hpf I1 I2).
Proof.
  intros Hin. rewrite /ivdplus //=.
  destruct Hin as (I1a&I2a&Hin1a&Hin2a&Heq). subst.
  destruct Hin1a as (I1b&Hin1b&Heq). subst.
  destruct Hin2a as (I2b&Hin2b&Heq). subst.
  exists {| ivd_ival := I1b; val_sum1 := all_sum1 _ _ Hin1b |}.
  exists {| ivd_ival := I2b; val_sum1 := all_sum1 _ _ Hin2b |}.
  repeat split => //=.
Qed.

Lemma rvar_of_pidist_ivd {X: eqType} (I: ivdist X) (Is: pidist X) Hpf:
  eq_dist (rvar_of_pidist (ivd_ival I) Is Hpf) (rvar_of_ivdist I).
Proof.
  rewrite /rvar_of_pidist//=.
Qed.

Lemma pidist_plus_comm {X} (p: R) Hpf Hpf' (I1 I2: pidist X):
  eq_pidist (pidist_plus p Hpf I1 I2) (pidist_plus (1 - p) Hpf' I2 I1).
Proof.
  rewrite /eq_pidist/pidist_union/pidist_plus//=.
  replace (1 - (1 - p)) with p by nra.
  apply pplus_comm.
Qed.

Lemma pidist_plus_choice1 {X} Hpf (I1 I2: pidist X):
  eq_pidist (pidist_plus 1 Hpf I1 I2) I1.
Proof.
  rewrite /eq_pidist/pidist_union/pidist_plus//=.
  replace (1 - 1) with 0 by nra.
  setoid_rewrite pscale_1.
  setoid_rewrite pscale_0.
  apply pplus_0.
Qed.

(* The case where p = 0 or q = 0 can be simplified by other means *)
Lemma pidist_plus_plus {X} (Is1 Is2 Is3: pidist X) (p q: R) Hpf1 Hpf2 Hpf3 Hpf4 :
  0 < p →
  0 < q →
  le_pidist (pidist_plus p Hpf1 Is1 (pidist_plus q Hpf2 Is2 Is3))
            (pidist_plus (1 - (1 - p) * (1 - q)) Hpf3
                         (pidist_plus (p / (1 - (1 - p) * (1 - q))) Hpf4 Is1 Is2)
                         Is3).
Proof.
  intros.
  rewrite /pidist_plus/le_pidist//=.
  setoid_rewrite pscale_distrib.
  setoid_rewrite pplus_assoc.
  setoid_rewrite pscale_assoc.
  eapply pplus_proper.
  * eapply pplus_proper.
    ** eapply pscale_proper; try reflexivity.
       field. nra.
    ** eapply pscale_proper; try reflexivity.
       field. nra.
  * eapply pscale_proper; try reflexivity.
    field.
Qed.

Global Opaque pidist_ret.
Global Opaque pidist_bind.



Lemma eq_ival_support_coerce_aux {X} (I1 I2: ival X) :
  eq_ival I1 I2 →
  ∀ x, (∃ i2, ind I2 i2 = x ∧ val I2 i2 > 0) → (∃ i1, ind I1 i1 = x ∧ val I1 i1 > 0).
Proof.
  intros Hequiv x (i2&Hind&Hval).
  symmetry in Hequiv.
  destruct Hequiv as (h1&h2&?&?&Hind'&Hval').
  destruct (h1 (coerce_supp _ _ Hval)) as (i1&Hgt).
  exists (sval (h1 (coerce_supp _ _ Hval))).
  split.
  * rewrite Hind' => //=.
  * destruct (h1 _) => //=; repeat destruct Rgt_dec => //=.
Qed.

Lemma eq_ival_support_coerce {X} (I1 I2: ivdist X) :
  eq_ival I1 I2 →
  ∀ x, (∃ i2, ind I2 i2 = x ∧ val I2 i2 > 0) ↔ (∃ i1, ind I1 i1 = x ∧ val I1 i1 > 0).
Proof.
  intros; split; eapply eq_ival_support_coerce_aux; eauto; by symmetry.
Qed.

Lemma In_psupport_alt {X: Type} (x: X) (Is : pival X) :
  (∃ I, In I Is ∧ In_isupport x I) → In_psupport x Is.
Proof.
  intros (I&Hin&i&?&?).
  exists I, i; repeat split => //=.
Qed.

Lemma le_pidist_support_coerce_aux {X} (Is1 Is2: pidist X) :
  le_pidist Is2 Is1 →
  ∀ x, In_psupport x Is2 → In_psupport x Is1.
Proof.
  intros Hle x (I2&i2&Hin2&?&Hval).
  destruct (Hle I2 Hin2) as (I1&Heq&Hin1).
  symmetry in Heq.
  exists I1. edestruct (eq_ival_support_coerce_aux _ _ Heq) as (i1&?&?).
  { exists i2. split; eauto. }
  exists i1; repeat split; eauto.
Qed.

Lemma In_psupport_mret {X} (x : X) : In_psupport x (mret x).
Proof.
  eexists. unshelve (eexists); repeat split; try (by left).
  * rewrite //=.
  * rewrite //=. nra.
Qed.

Lemma In_psupport_mret_inv {X} (x y : X) : In_psupport x (mret y) → x = y.
Proof.
  intros (?&?&Hin&?&?). subst. rewrite //=.
  rewrite /mret//= in Hin. subst => //=.
Qed.

Lemma In_psupport_bind {X Y: Type} (Is: pival X) (f: X → pival Y) (x: X) (y: Y):
  In_psupport x Is →
  In_psupport y (f x) →
  In_psupport y (mbind f Is).
Proof.
  intros (I1&i1&Hin&Hind&Hval) (If&ifx&Hinf&Hindf&Hvalf).
    unshelve (edestruct (pival_mbind_in Is f I1) as (Ix&?&Heq&HIn); auto).
    { intros i2.
      destruct (eqVneq i1 i2).
      - exact If.
      - destruct (f (ind I1 i2)) as [Is' Hne].
        apply ClassicalEpsilon.constructive_indefinite_description in Hne as (I'&?).
       exact I'.
    }
    {
    intros i2.
    rewrite //=.
    destruct (eqVneq).
    * subst; auto.
    * intros. destruct (f (ind I1 i2)) as [Is' Hne] => //=.
      destruct ClassicalEpsilon.constructive_indefinite_description => //=.
    }
    apply In_psupport_alt.
    exists Ix; split; first done.
    rewrite /In_isupport.
    symmetry in Heq.
    rewrite //= in Heq.
    eapply (eq_ival_support_coerce_aux _ _ Heq).
    unshelve (eexists).
    { rewrite //=.
      exists i1. destruct eqVneq as [?|Hneq]; last first.
      { rewrite eq_refl in Hneq. exfalso; auto. }
      eauto.
    }
    split.
    * rewrite //=.
      subst. destruct eqVneq as [?|Hneq] => //=; last first.
      { exfalso. rewrite eq_refl in Hneq. auto. }
    * rewrite //=.
      subst. destruct eqVneq as [?|Hneq] => //=; last first.
      { exfalso. rewrite eq_refl in Hneq. auto. }
      clear -Hval Hvalf. nra.
Qed.

Lemma pidist_union_foldleft_proper {X} l (m1 m2: pidist X):
  eq_pidist m1 m2 →
  eq_pidist (fold_left pidist_union l m1)
            (fold_left pidist_union l m2).
Proof.
  revert m1 m2; induction l => m1 m2 //=.
  intros Hequiv. eapply IHl.
  setoid_rewrite Hequiv.
  reflexivity.
Qed.

Lemma pidist_union_foldright_proper {X} l (m1 m2: pidist X):
  eq_pidist m1 m2 →
  eq_pidist (fold_right pidist_union m1 l)
            (fold_right pidist_union m2 l).
Proof.
  revert m1 m2; induction l => m1 m2 //=.
  intros Hequiv. setoid_rewrite IHl; first reflexivity; eauto.
  reflexivity.
Qed.

Lemma pidist_union_foldleft_hd {X} (l: list (pidist X)) (m1 m2: pidist X):
  eq_pidist (pidist_union m2 (fold_left pidist_union l m1))
            (fold_left pidist_union l (pidist_union m2 m1)).
Proof.
  revert m1 m2; induction l => m1 m2 //=; try reflexivity.
  setoid_rewrite IHl.
  eapply pidist_union_foldleft_proper.
  setoid_rewrite pidist_union_assoc.
  reflexivity.
Qed.

Lemma pidist_union_foldright_hd {X} (l: list (pidist X)) (m1 m2: pidist X):
  eq_pidist (pidist_union m2 (fold_right pidist_union m1 l))
            (fold_right pidist_union (pidist_union m2 m1) l).
Proof.
  revert m1 m2; induction l => m1 m2 //=; try reflexivity.
  setoid_rewrite IHl.
  setoid_rewrite IHl.
  eapply pidist_union_foldright_proper.
  setoid_rewrite pidist_union_assoc.
  setoid_rewrite (pidist_union_comm _ a m2).
  reflexivity.
Qed.

Lemma fold_left_right_pidist_union {X} (l: list (pidist X)) (m: pidist X):
  eq_pidist (fold_left pidist_union l m)
            (fold_right pidist_union m l).
Proof.
  revert m.
  induction l => m //=; try reflexivity.
  setoid_rewrite <-IHl.
  setoid_rewrite pidist_union_foldleft_hd.
  apply pidist_union_foldleft_proper.
  setoid_rewrite pidist_union_comm at 1.
  reflexivity.
Qed.

Lemma pidist_union_foldleft_bind (A B: Type) (l: list (pidist A)) (m: pidist A)
      (f: A → pidist B) :
  eq_pidist (x ← fold_left pidist_union l m; f x)
            (fold_left pidist_union (map (mbind f) l) (mbind f m)).
Proof.
  revert m.
  induction l => m //=; first reflexivity.
  setoid_rewrite <-pidist_union_foldleft_hd.
  setoid_rewrite pidist_union_bind.
  setoid_rewrite IHl. setoid_rewrite pidist_union_foldleft_hd. reflexivity.
Qed.

Lemma pidist_join {X A: Type} (INH: X) (Iss: X → pidist A) : pidist A.
  unshelve econstructor.
  - exact (pival_join INH Iss).
  - abstract (intros I (Is&?); eapply all_sum1; eauto).
Defined.

Lemma pidist_join_bind {X A B: Type} (INH: X) Iss (f: A → pidist B) :
  eq_pidist (a ← pidist_join INH Iss; f a)
           (pidist_join INH (λ x, a ← Iss x; f a)).
Proof. apply pival_join_bind. Qed.

Lemma pidist_join_ext {X A: Type} (INH INH': X) (Iss Iss': X → pidist A):
  (∀ x : X, eq_pidist (Iss x) (Iss' x)) →
  eq_pidist (pidist_join INH Iss) (pidist_join INH' Iss').
Proof. apply pival_join_ext. Qed.

Lemma pidist_join_equiv {X A: Type} (INH: X) (Iss: X → pidist A) (Is: pidist A):
  (∀ x : X, eq_pidist (Iss x) Is) →
  eq_pival (pidist_join INH Iss) Is.
Proof. apply pival_join_equiv. Qed.

Global Instance pidist_join_Proper {X A: Type} :
  Proper (eq ==> pointwise_relation X (eq_pidist) ==> @eq_pidist A) pidist_join.
Proof.
  intros ?? Heq ?? Heq'.
  eapply pidist_join_ext; eauto.
Qed.

Lemma easy_fix_eq:
  ∀ (A : Type) (R : A → A → Prop) (Rwf : well_founded R) (P : A → Type)
    (F : ∀ x : A, (∀ y : A, R y x → P y) → P x),
    ∀ x : A, Fix Rwf P F x = F x (λ (y : A) (_ : R y x), Fix Rwf P F y).
Proof.
  intros. apply Init.Wf.Fix_eq.
  intros. assert (f = g) as ->; last done.
  apply FunctionalExtensionality.functional_extensionality_dep => ?.
  apply FunctionalExtensionality.functional_extensionality_dep => ?. done.
Qed.

Inductive Ord :=
  | OrdO : Ord
  | OrdS : Ord → Ord
  | OrdLim : (nat → Ord) → Ord.

Inductive Ord_lt_gen : Ord → Ord → Prop :=
  | Ord_lt_gen_S O: Ord_lt_gen O (OrdS O)
  | Ord_lt_gen_Lim f i: Ord_lt_gen (f i) (OrdLim f).

Definition Ord_lt := Relation_Operators.clos_trans _ Ord_lt_gen.

Require Import Program.Wf Wellfounded Wellfounded.Transitive_Closure.


Lemma wf_Ord_lt: well_founded Ord_lt.
Proof.
  apply wf_clos_trans.
  intros O.
  induction O.
  - econstructor. intros y Hlt. remember OrdO as x eqn:Heq. revert Heq.
    induction Hlt; try congruence.
  - econstructor. intros y Hlt. inversion Hlt. subst. eauto.
  - econstructor. intros y Hlt. inversion Hlt. subst. eauto.
Qed.

Lemma Ord_lt_O o: o ≠ OrdO → { x: Ord | Ord_lt x o }.
Proof.
  induction o.
  - congruence.
  - intros. exists o. do 2 econstructor.
  - intros. exists (o O). do 2 econstructor.
Qed.

Lemma Ord_lt_lim o: { x: Ord | Ord_lt x (OrdLim o) }.
Proof.
  eapply Ord_lt_O; eauto.
Qed.

Lemma Ord_lt_S o: { x: Ord | Ord_lt x (OrdS o) }.
Proof.
  eapply Ord_lt_O; eauto.
Qed.

Definition pidist_iter_aux {A: Type} (m: A → pidist A) : Ord → A → pidist A.
  refine(Fix wf_Ord_lt (fun _ => A → pidist A)
             (fun o rec =>
               λ a,
               match o as o' return (o = o' → pidist A) with
               | OrdO => λ eq, mret a
               | _ => λ eq,
                  x ← m a;
                  @pidist_join { o'' : Ord | Ord_lt o'' o } _ _
                               (λ n', rec (proj1_sig n') (proj2_sig n') x)
               end Init.Logic.eq_refl)).
  { subst; apply Ord_lt_S. }
  { subst; apply Ord_lt_lim. }
Defined.

Definition pidist_iter {A: Type} (m: A → pidist A) : A → pidist A.
  intros a. eapply (@pidist_join Ord _ OrdO (λ n, pidist_iter_aux m n a)).
Defined.

Lemma pidist_iter_aux_unfold_lim {A: Type} (m: A → pidist A) o a:
  pidist_iter_aux m (OrdLim o) a =
  x ← m a;
  @pidist_join { o'' : Ord | Ord_lt o'' (OrdLim o) } _ (Ord_lt_lim o)
               (λ n', pidist_iter_aux m (proj1_sig n') x).
Proof.
  rewrite /pidist_iter_aux//= easy_fix_eq //=; eauto.
Qed.

Lemma pidist_iter_aux_unfold_S {A: Type} (m: A → pidist A) o a:
  pidist_iter_aux m (OrdS o) a =
  x ← m a;
  @pidist_join { o'' : Ord | Ord_lt o'' (OrdS o) } _ (Ord_lt_S o)
               (λ n', pidist_iter_aux m (proj1_sig n') x).
Proof.
  rewrite /pidist_iter_aux//= easy_fix_eq //=; eauto.
Qed.

Lemma pidist_iter_unfold_l {A: Type} (m: A → pidist A) (a: A):
    le_pidist (mret a)
              (pidist_iter m a).
Proof.
  intros I Hin. exists I. split; first done. exists OrdO => //=.
  rewrite /pidist_iter_aux//= easy_fix_eq //=.
Qed.

Lemma pidist_iter_unfold_r {A: Type} (m: A → pidist A) (a: A):
    le_pidist (x ← m a; pidist_iter m x)
              (pidist_iter m a).
Proof.
  intros I Hin.
  edestruct (pival_mbind_in_inv_idxOf (m a) (pidist_iter m))
    as (I'&h&?&Hhspec&Heq); eauto.
  assert (∃ fn, ∀ i, ival.val I' i > 0 →
                    In (h i) (pidist_iter_aux m (fn (choice.pickle i)) (ival.ind I' i))) as (fn&Hn).
  { unshelve (eexists).
    { intros n.
      * destruct (@choice.pickle_inv (ival.idx I') n) as [i|].
        ** destruct (ClassicalEpsilon.excluded_middle_informative (ival.val I' i > 0)) as [Hgt|].
           *** specialize (Hhspec i Hgt) as Hhspec; eauto.
               apply ClassicalEpsilon.constructive_indefinite_description in Hhspec
                 as (o&?).
               exact o.
           *** exact OrdO.
        ** exact OrdO.
    }
    intros i. rewrite //= pickleK_inv.
    intros Hgt.
    destruct ClassicalEpsilon.excluded_middle_informative; last (exfalso; eauto).
    destruct ClassicalEpsilon.constructive_indefinite_description.
    eauto.
  }
  edestruct (pival_mbind_in_alt2_idxOf
               (m a)
               (λ x, @pidist_join { o'' : Ord | Ord_lt o'' (OrdLim fn) } _ (Ord_lt_lim _)
                               (λ n', pidist_iter_aux m (proj1_sig n') x)) _ h)
    as (I''&?&Hin2).
    { eexists; split; eauto.  }
    { intros. rewrite //=.
      unshelve (eexists).
      { exists (fn (pickle i)). do 2 econstructor. }
      rewrite //=.
      eapply Hn. eauto.
    }
    eexists. split; last first.
    { exists (OrdLim fn).
      rewrite pidist_iter_aux_unfold_lim. eapply Hin2.
    }
    rewrite -Heq. eauto.
Qed.

Lemma pidist_iter_unfold {A: Type} (m: A → pidist A) (a: A):
  eq_pidist (pidist_iter m a)
            (pidist_union (mret a) (x ← m a; pidist_iter m x)).
Proof.
  split.
  - intros I Hin.
    destruct Hin as (o&Hin).
    destruct o.
    * exists I. split; first done.
      left. rewrite /pidist_iter_aux easy_fix_eq in Hin. done.
    * rewrite pidist_iter_aux_unfold_S in Hin.
      eapply pidist_bind_congr_le in Hin as (I'&Heq&Hin).
      { exists I'; split; first done. right. eapply Hin. }
      { reflexivity. }
      intros a' I' (o'&Hin').
      exists I'; split; eauto. exists (sval o'). eauto.
    * rewrite pidist_iter_aux_unfold_lim in Hin.
      eapply pidist_bind_congr_le in Hin as (I'&Heq&Hin).
      { exists I'; split; first done. right. eapply Hin. }
      { reflexivity. }
      intros a' I' (o'&Hin').
      exists I'; split; eauto. exists (sval o'). eauto.
  - intros I [Hin1|Hin2].
    * eapply pidist_iter_unfold_l; eauto.
    * eapply pidist_iter_unfold_r; eauto.
Qed.

Lemma pidist_union_fold_left_join {X: Type} (l: list (pidist X)) (m: pidist X):
  eq_pidist (fold_left pidist_union l m)
            (@pidist_join { x | List.In x (m :: l) } X (exist _ m (or_introl Logic.eq_refl)) sval).
Proof.
  revert m.
  induction l as [| a l] => m.
  - rewrite //=. split.
    * intros I Hin. exists I; split; first done. unshelve eexists.
      { exists m. by left. }
      rewrite //=.
    * intros I ((m'&[|[]])&Hin). subst.
      exists I. split; auto.
  - rewrite //= -pidist_union_foldleft_hd.
    split.
    * intros I [Hin|Hin].
      ** exists I; split; first done. unshelve eexists.
         { exists m. by left. }
         rewrite //=.
      ** destruct (IHl a) as [Hle1 Hle2].
         specialize (Hle1 _ Hin). edestruct Hle1 as (I'&Heq&Hin').
         exists I'; split; auto.
         destruct Hin' as ((m'&Hinl)&Hin').
         unshelve eexists.
         { exists m'. right. auto. }
         rewrite //=.
    * intros I ((m'&Hinl)&Hin).
      destruct Hinl as [Hhd|Hinl'].
      ** subst.  exists I; split; auto. left. auto.
      ** edestruct (IHl a) as [Hle1 Hle2].
         rewrite //= in Hin.
         edestruct (Hle2 I) as (I'&?&?).
         { unshelve (eexists).
           { exists m'. auto. }
           rewrite //=.
         }
         exists I'; split; auto.
         right. eauto.
Qed.