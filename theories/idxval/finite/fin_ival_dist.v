(* Here we consider indexed valuations that can be interpreted as probability
   distributions; that is, those in which the sum of the weights is equal to 0 *)

From discprob.basic Require Import base sval order monad.
Require Import Reals Psatz.

Require ClassicalEpsilon.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
Global Set Bullet Behavior "Strict Subproofs".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype finset finfun bigop.

Local Open Scope R_scope.
From discprob.idxval Require Import fin_ival.
From discprob.prob Require Import prob countable finite stochastic_order.

Record ivdist X :=
  { ivd_ival :> ival X;
    val_sum1: \big[Rplus/0]_(i : idx ivd_ival) val ivd_ival i = R1
  }.

Arguments ivd_ival {_}.
Arguments val_sum1 {_}.

Definition eq_ivd {X} (I1 I2: ivdist X) :=
  eq_ival I1 I2.

Global Instance eq_ivd_Transitivite {X}: Transitive (@eq_ivd X).
Proof. intros ???. apply eq_ival_trans. Qed.
Global Instance eq_ivd_Reflexive {X}: Reflexive (@eq_ivd X).
Proof. intros ?. apply eq_ival_refl. Qed.
Global Instance eq_ivd_Symmetry {X}: Symmetric (@eq_ivd X).
Proof. intros ??. apply eq_ival_sym. Qed.
Global Instance eq_ival_Equivalence {X}: Equivalence (@eq_ivd X).
Proof. split; apply _. Qed.

Definition ivdplus {X} (p: R) (Hrange: 0 <= p <= 1) (I1 I2: ivdist X) : ivdist X.
Proof.
  refine {| ivd_ival := iplus (iscale p I1) (iscale (1 - p) I2) |}.
  abstract (rewrite //=;
  rewrite /index_enum {1}[@Finite.enum]unlock /sum_enum big_cat ?big_map //=;
  rewrite -?big_distrr //= ?val_sum1;
  rewrite ?Rabs_right; nra).
Defined.

Global Instance ivdist_plus_proper:
  ∀ (X : Type) r Hpf, Proper (@eq_ivd X ==> @eq_ivd X ==> @eq_ivd X) (ivdplus r Hpf).
Proof.
  intros X r Hpf Is1 Is1' Hle1 Is2 Is2' Hle2.
  rewrite /eq_ivd/ivdplus//=.
  rewrite /eq_ivd in Hle1, Hle2.
  setoid_rewrite Hle1. setoid_rewrite Hle2.
  reflexivity.
Qed.

Lemma ivdplus_comm {X} (p: R) Hpf Hpf' (I1 I2: ivdist X) :
  eq_ivd (ivdplus p Hpf I1 I2) (ivdplus (1 - p) Hpf' I2 I1).
Proof.
  rewrite /eq_ivd/ivdplus//=.
  replace (1 - (1 - p)) with p by nra.
  apply iplus_comm.
Qed.

Lemma ivdplus_eq_ival {X} p Hpf (I1 I1' I2 I2': ivdist X):
  eq_ivd I1 I1' →
  eq_ivd I2 I2' →
  eq_ival (ivdplus p Hpf I1 I2) (ivdplus p Hpf I1' I2').
Proof.
  rewrite /eq_ivd/ivdplus => Heq1 Heq2 //=.
  setoid_rewrite Heq1.
  setoid_rewrite Heq2.
  reflexivity.
Qed.

Global Instance ivd_ret: MRet ivdist.
refine(λ A x, {| ivd_ival := mret x;
                 val_sum1 := _ |}).
{ abstract (rewrite /index_enum {1}[@Finite.enum]unlock //= big_seq1 //). }
Defined.

Global Instance ivd_bind: MBind ivdist.
refine(λ A B f I, {| ivd_ival := mbind (λ x, ivd_ival (f x)) (ivd_ival I);
                     val_sum1 := _ |}).
{ abstract (rewrite /index_enum {1}[@Finite.enum]unlock //=;
  rewrite /tag_enum big_flatten //= big_map;
  rewrite -(val_sum1 I); apply eq_bigr => i _;
  rewrite big_map //= -big_distrr val_sum1 /= Rmult_1_r //=).
}
Defined.

Global Instance ivd_bind_proper X Y :
  Proper (pointwise_relation X (@eq_ivd Y) ==> @eq_ivd X ==> @eq_ivd Y) (ivd_bind X Y).
Proof. intros ?? ? ?? ?. eapply ibind_proper; eauto. Qed. 

Lemma ivd_assoc {A B C} (m: ivdist A) (f: A → ivdist B) (g: B → ivdist C) :
  eq_ivd (mbind g (mbind f m)) (mbind (λ x, mbind g (f x)) m).
Proof.
  rewrite /eq_ivd. setoid_rewrite ival_assoc. reflexivity.
Qed.

Lemma ivd_left_id {A B: Type} (x: A) (f: A → ivdist B):
  eq_ivd (mbind f (mret x)) (f x).
Proof.
  rewrite /eq_ivd. setoid_rewrite ival_left_id. reflexivity.
Qed.

Lemma ivd_right_id {A: Type} (m: ivdist A):
  eq_ivd (mbind mret m) m.
Proof.
  rewrite /eq_ivd. setoid_rewrite ival_right_id. reflexivity.
Qed.

Lemma ivd_bind_congr {A B} (m1 m2: ivdist A) (f1 f2: A → ivdist B) :
  eq_ivd m1 m2 →
  (∀ a, eq_ivd (f1 a) (f2 a)) →
  eq_ivd (x ← m1; f1 x) (x ← m2; f2 x).
Proof. 
  intros Hlem Hlef.
  rewrite /eq_ivd.
  apply ival_bind_congr; eauto.
Qed.

Lemma ivd_plus_bind:
  ∀ (A B : Type) p Hpf (m1 m2 : ivdist A) (f : A → ivdist B),
    eq_ivd (x ← ivdplus p Hpf m1 m2; f x) (ivdplus p Hpf (x ← m1; f x) (x ← m2; f x)).
Proof.
  intros A B p Hpf m1 m2 f.
  rewrite /eq_ivd. rewrite /ivdplus/ivd_bind.
  setoid_rewrite ival_plus_bind.
  setoid_rewrite ival_scale_bind.
  reflexivity.
Qed.
  
Lemma eq_ival_sum {X} (I1 I2: ival X) P:
  eq_ival I1 I2 →
  \big[Rplus/0]_(i | P (ind I1 i)) (val I1 i) = 
  \big[Rplus/0]_(i | P (ind I2 i)) (val I2 i). 
Proof.
  intros Heq.
  transitivity (\big[Rplus/0]_(i : support (val I1) | P (ind I1 (sval i))) (val I1 (sval i))).
  - symmetry.  rewrite /index_enum. apply sum_reidx_map with (h := sval) => //=.
    * intros (a&Hgt) ?? => //=. rewrite -enumT mem_enum //=.
    * intros b _ HP Hneq. specialize (val_nonneg I1 b).
      destruct 1 as [Hgt|Heq0]; auto.
      exfalso. apply Hneq.
      exists (coerce_supp _ _ Hgt); repeat split; auto.
      rewrite -enumT mem_enum //=.
    * rewrite -enumT. apply enum_uniq.
    * rewrite -enumT. apply enum_uniq.
    * intros. by apply sval_inj_pred.
  - destruct Heq as (h1&h2&Hh12&Hh21&Hind&Hval).
    rewrite /index_enum. apply sum_reidx_map with (h := λ x, sval (h1 x)).
    * intros (a&Hgt) ? => //=. rewrite Hval. done.
    * intros (a&Hgt) ?? => //=. split; first by rewrite -enumT mem_enum //=.
      rewrite Hind. done.
    * intros b _ HP Hneq. specialize (val_nonneg I2 b).
      destruct 1 as [Hgt|Heq0]; auto.
      exfalso. apply Hneq.
      exists (h2 (coerce_supp _ _ Hgt)); repeat split; auto.
      ** rewrite -enumT mem_enum //=.
      ** rewrite -Hind Hh21. done.
      ** rewrite Hh21 //=.
    * rewrite -enumT. apply enum_uniq.
    * rewrite -enumT. apply enum_uniq.
    * intros x x' _ ?%sval_inj_pred.
      rewrite -(Hh12 x).
      rewrite -(Hh12 x').
      congruence.
Qed.

(*
Lemma img_rvar_of_ivdist {A: eqType} (h: ivdist A):
  map sval (Finite.enum [finType of (imgT (rvar_of_ivdist h))]) = undup [seq i.2 | i <- h].
Proof.  
  rewrite {1}[@Finite.enum]unlock //=. rewrite img_fin_enum_sval.
  assert (a: A).
  { destruct h as (l, pf1, pf2). destruct l.
    - rewrite big_nil in pf2. move /eqP in pf2. exfalso.
      rewrite //= in pf2. fourier.
    - exact (snd p).
  }
  f_equal.
  etransitivity.
  - apply (@eq_map _ _ _ (λ n, nth a [seq i.2 | i <- h] (nat_of_ord n))).
    { intro i. erewrite set_nth_default; auto. rewrite size_map. done. }
  - rewrite -enumT. rewrite (nat_of_ord_map_iota (size h) (λ n, nth a [seq (snd i) | i <- h] n)). 
  destruct h as (l, pf1, pf2) => //=; clear pf1 pf2.
  rewrite -(size_map snd l) map_nth_iota //.
Qed.
*)

Lemma primitive_ivdplus {X} p HPf (I1 I2: ivdist X):
  ival_primitive I1 →
  ival_primitive I2 →
  ¬ (∃ i1 i2, ind I1 i1 = ind I2 i2) →
  ival_primitive (ivdplus p HPf I1 I2).
Proof.
  intros Hprim1 Hprim2 Hdisj ia ib.
  destruct ia, ib => //=.
  - intros Heq. f_equal. apply Hprim1; eauto.
  - intros Heq. exfalso; eapply Hdisj; eauto.
  - intros Heq. exfalso; eapply Hdisj; eauto.
  - intros Heq. f_equal. apply Hprim2; eauto.
Qed.
  
Lemma primitive_ivdplus_mret {X} p HPf (x1 x2: X):
  x1 ≠ x2 →
  ival_primitive (ivdplus p HPf (mret x1) (mret x2)).
Proof. intros ? [[]|[]] [[]|[]] => //=; intros; try f_equal; try congruence. Qed.

Lemma ivd_isupport_inhabited {X} (I: ivdist X) : isupport I.
Proof.
  destruct I as [I Hsum].
  destruct I as [idx ind val].
  rewrite //= in Hsum *.
  rewrite //=/index_enum//= in Hsum *.
  assert (0 < \big[Rplus/0]_(i <- Finite.enum idx) val i) as Hlt0.
  { nra.  }
  edestruct (ClassicalEpsilon.constructive_indefinite_description _
              (Rlt_0_big_inv val (Finite.enum idx) (λ x, true) Hlt0)) as (i&?&?&?).
  exists (ind i) => //=.
  exists i; split; auto.
Qed.