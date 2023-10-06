From discprob.basic Require Import base Series_Ext.
Require Import Reals Fourier Lia Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.

(*

   The ssreflect library defines a notion of countable types, which
   are types A with a map pickle : A → nat such that pickle has a left inverse
   unpickle: nat → option A and a partial right inverse pickle_inv.

   Here we define series indexed by countable types and develop some
   additional properties and facts about countable types that are needed.

*)

Definition support {X} (v: X → R) := { x : X | is_true (Rgt_dec (v x) 0) }.

Definition countable_sum {A: countType} (f: A → R) :=
  λ n: nat, oapp f R0 (@pickle_inv A n).

Lemma countable_sum_ext {A: countType} (f f': A → R) n :
  (∀ n, f n = f' n) → countable_sum f n = countable_sum f' n.
Proof.
  intros Hext. rewrite /countable_sum. destruct (pickle_inv) => //=.
Qed.

Lemma countable_sum_le {A: countType} (f f': A → R) n :
  (∀ n, f n <= f' n) → countable_sum f n <= countable_sum f' n.
Proof.
  intros Hext. rewrite /countable_sum. destruct (pickle_inv) => //=; nra.
Qed.

Lemma LPO_count {A: countType} (P: A → Prop):
      (∀ a, P a ∨ ¬ P a) → {a : A | P a} + {(∀ a, ¬ P a)}.
Proof.
  set (P' := λ n, match (@unpickle A n) with
                    | Some a => P a
                    | None => False
                  end).
  intros.
  destruct (LPO P') as [(n&HP)|Hnot].
  { intros n. rewrite /P'. destruct (unpickle n); auto. }
  - left. rewrite /P' in HP. destruct (unpickle n); eauto; done.
  - right. intros a Ha. apply (Hnot (pickle a)). rewrite /P'.
    by rewrite pickleK.
Qed.

Lemma LPO_countb {A: countType} (P: A → bool):
      {a : A | P a} + {(∀ a, ¬ P a)}.
Proof.
  apply LPO_count => a. destruct (P a); auto.
Qed.

Definition exC {A: countType} (B: pred A) : bool := LPO_countb B.

Lemma exCP {A: countType} (B: pred A) : reflect (∃ x, B x) (exC B).
Proof.
  rewrite /exC. destruct (LPO_countb) as [(a&HB)|Hfalse]; econstructor.
  - eexists; eauto.
  - intros (x'&HB). eapply Hfalse; eauto.
Qed.

Lemma pickle_inv_some_inv {A: countType} n a':
  @pickle_inv A n = Some a' →
  pickle a' = n.
Proof.
  intros Heq.
  assert (H: @oapp _ _ (@pickle A) n (@pickle_inv A n) = n) by rewrite pickle_invK //.
  rewrite Heq in H. done.
Qed.

Lemma pickle_inv_some_inj {A: countType} n n' a':
  @pickle_inv A n = Some a' →
  @pickle_inv A n = @pickle_inv A n' →
  n = n'.
Proof.
  intros. transitivity (pickle a').
  - by symmetry; apply pickle_inv_some_inv.
  - apply pickle_inv_some_inv. congruence.
Qed.

Lemma pickle_inj {A: countType} (a a': A):
  pickle a = pickle a' → a = a'.
Proof.
  intros Hpickle.
  apply (f_equal (@pickle_inv A)) in Hpickle.
  rewrite ?pickleK_inv in Hpickle.
  congruence.
Qed.

(* The image of a countable type is also a countable type *)

Definition img {A: countType} {B: eqType} (f: A → B ) : pred B := λ y, exC (λ x, f x == y).
Definition imgT {A: countType} {B: eqType} (f: A → B) := {y | y \in img f}.

Definition img_pickle {A: countType} {B: eqType} (f: A → B) : { y | exC (λ x, f x == y) } → nat.
Proof.
  intros (y&Hex).
  destruct (LPO (λ n, omap f (unpickle n) == Some y)) as [(n&HP)|Hfalse].
  { abstract (intros n => //=; rewrite /omap/obind/oapp//=;
              destruct (unpickle n); destruct (_ == _) => //; auto). }
  - exact n.
  - exfalso. move /exCP in Hex.
    abstract (edestruct Hex as (a&Heq);
              apply (Hfalse (pickle a)) => //=;
              rewrite pickleK //=; subst; done).
Defined.

Definition img_unpickle {A: countType} {B: eqType} (f: A → B) (n: nat)
  : option { y | exC (λ x, f x == y) } :=
 (match unpickle n with
 | Some a =>
     Some (exist (λ y : B, exC (λ x : A, f x == y)) (f a)
          (introT (exCP (λ x : A, f x == f a)) (ex_intro (λ x : A, f x == f a) a (eqxx (T:=B) (f a)))))
 | None => None
 end).

Lemma pickle_imgK {A: countType} {B: eqType} (f: A → B):
  pcancel (img_pickle f) (img_unpickle f).
Proof.
  rewrite /img_pickle/img_unpickle//=.
  intros (b&HexC) => //=.
  destruct LPO as [(n&Heq')|];
    last by (exfalso; eapply img_pickle_subproof0; eauto; apply (elimT (exCP _))).
  destruct (unpickle n); rewrite //= in Heq'.
  move /eqP in Heq'. inversion Heq'; subst.
  do 2!f_equal.
  apply bool_irrelevance.
Qed.

Definition img_choiceMixin {A: countType} {B: eqType} (f: A → B) :=
  PcanChoiceMixin (pickle_imgK f).
Canonical img_choiceType {A: countType} {B: eqType} {f: A → B} :=
  Eval hnf in ChoiceType (imgT f) (@img_choiceMixin A B f).

Definition img_countMixin {A: countType} {B: eqType} (f: A → B) :=
  PcanCountMixin (pickle_imgK f).
Canonical img_countType {A: countType} {B: eqType} (f: A → B) :=
  Eval hnf in CountType (imgT f) (@img_countMixin A B f).

(* Some facts about series over countable types *)

Section countable_series_facts.
Variable (A: countType).
Implicit Types (a b: A → R).

(*
Lemma countable_sum_finType {B: finType} (a: B → R):
  Series (countable_sum a) = \big[Rplus/0]_(i : B) (a i).
Proof.
  rewrite /countable_sum.
  transitivity (\big[Rplus/0]_(i < |B|) (
  rewrite /pickle_inv/pickle/Countable.pickle//=.k
  int
*)

Lemma countable_sum_scal c a:
  ∀ n, countable_sum (λ x, scal c (a x)) n = (λ n, scal c (countable_sum a n)) n.
Proof.
  intros. rewrite //=/countable_sum/scal//=/mult//=; destruct pickle_inv => //=; nra.
Qed.

Lemma is_seriesC_0 a: (∀ n, a n = 0) → is_series (countable_sum a) 0.
Proof.
  intros Heq0. apply is_series_0 => n. rewrite /countable_sum/oapp.
  destruct (@pickle_inv A n); auto.
Qed.

Lemma is_seriesC_ext a b l:
  (∀ n, a n = b n) → is_series (countable_sum a) l → is_series (countable_sum b) l.
Proof.
  intros Heq. apply is_series_ext.
  intros n. rewrite /countable_sum. destruct (@pickle_inv A n); eauto.
Qed.

Lemma ex_seriesC_ext a b:
  (∀ n, a n = b n) → ex_series (countable_sum a) → ex_series (countable_sum b).
Proof.
  intros Heq. apply ex_series_ext.
  intros n. rewrite /countable_sum. destruct (@pickle_inv A n); eauto.
Qed.

Global Instance is_series_Proper:
  Proper (pointwise_relation nat (@eq R) ==> @eq R ==> iff) is_series.
Proof.
  intros ?? ? ?? ?; subst; split; eapply is_series_ext; eauto.
Qed.

Global Instance ex_series_Proper:
  Proper (pointwise_relation nat (@eq R) ==> iff) ex_series.
Proof.
  intros ?? ?; split; eapply ex_series_ext; eauto.
Qed.

Global Instance Series_Proper:
  Proper (pointwise_relation nat (@eq R) ==> eq) Series.
Proof.
  intros ?? ?; eapply Series_ext; eauto.
Qed.

Global Instance countable_sum_Proper:
  Proper (pointwise_relation A (@eq R) ==> pointwise_relation nat (@eq R)) countable_sum.
Proof.
  intros ?? ? x. rewrite /countable_sum. destruct pickle_inv; eauto.
Qed.

Global Instance countable_sum_Proper' {B: countType}:
  Proper (pointwise_relation B (@eq R) ==> eq ==> eq) countable_sum.
Proof.
  intros ?? ? x ??. subst. eapply countable_sum_ext; eauto.
Qed.

Lemma is_seriesC_filter_pos a (P: pred A) (v: R):
  (∀ n, a n >= 0) →
  is_series (countable_sum a) v → ex_series (countable_sum (λ n, if P n then a n else 0)).
Proof.
  intros Hge Hconv.
  apply: ex_series_le; last by (exists v; eauto).
  intros n. rewrite /norm//=/abs//=.
  rewrite /countable_sum//=.
  destruct (pickle_inv) as [x|] => //=.
  - destruct (P x); rewrite Rabs_right => //=; try nra.
    specialize (Hge x); nra.
  - rewrite Rabs_right; nra.
Qed.

Lemma is_seriesC_filter_PQ a (P Q: pred A) (v: R):
  (∀ n, a n >= 0) →
  is_series (countable_sum (λ n, if P n then a n else 0)) v →
  (∀ n, Q n → P n) →
  ex_series (countable_sum (λ n, if Q n then a n else 0)).
Proof.
  intros Hge Hconv Himp. apply ex_series_Rabs.
  apply: ex_series_le; last by (exists v; eauto).
  intros n. rewrite /norm//=/abs//=.
  rewrite /countable_sum//=.
  destruct (pickle_inv) as [x|] => //=.
  - specialize (Himp x); specialize (Hge x).
    destruct (P x), (Q x); rewrite Rabs_Rabsolu Rabs_right => //=; try nra.
    exfalso; auto.
  - rewrite Rabs_Rabsolu Rabs_right; nra.
Qed.

Lemma ex_seriesC_filter_PQ a (P Q: pred A):
  (∀ n, a n >= 0) →
  ex_series (countable_sum (λ n, if P n then a n else 0)) →
  (∀ n, Q n → P n) →
  ex_series (countable_sum (λ n, if Q n then a n else 0)).
Proof.
  intros ? [v His] ?. eapply is_seriesC_filter_PQ; eauto.
Qed.

Lemma ex_seriesC_filter_P a (Q: pred A):
  (∀ n, a n >= 0) →
  ex_series (countable_sum a) →
  ex_series (countable_sum (λ n, if Q n then a n else 0)).
Proof.
  intros ? [v His]. eapply is_seriesC_filter_PQ with (P := xpredT); eauto.
Qed.

Lemma is_seriesC_filter_split a (P: pred A) (v: R):
  (∀ n, a n >= 0) →
  is_series (countable_sum a) v →
  Series (countable_sum (λ n, if P n then a n else 0)) +
  Series (countable_sum (λ n, if ~~ P n then a n else 0)) = v.
Proof.
  intros.
  rewrite -Series_plus; try (eapply is_seriesC_filter_pos; eauto).
  rewrite -(is_series_unique (countable_sum a) v) //.
  apply Series_ext => n.
  rewrite /countable_sum//=.
  destruct (pickle_inv) as [x|] => //=; last by nra.
  destruct (P x) => //=; nra.
Qed.

Lemma is_seriesC_filter_union a (P Q: pred A) (v: R):
  (∀ n, a n >= 0) →
  is_series (countable_sum (λ n, if P n || Q n then a n else 0)) v →
  Series (countable_sum (λ n, if P n then a n else 0)) +
  Series (countable_sum (λ n, if Q n then a n else 0))
    - Series (countable_sum (λ n, if P n && Q n then a n else 0)) = v.
Proof.
  intros Hge Hexists.
  rewrite -Series_plus; try (eapply (is_seriesC_filter_PQ _ _ _ _ Hge Hexists); eauto;
                             try (intros n; destruct (P n), (Q n); auto)).
  rewrite -Series_minus; try (eapply (is_seriesC_filter_PQ _ _ _ _ Hge Hexists); eauto;
                             try (intros n; destruct (P n), (Q n); auto)).
  - rewrite -(is_series_unique _ v Hexists).
    apply Series_ext => n.
    rewrite /countable_sum//=.
    destruct (pickle_inv) as [x|] => //=; last by nra.
    destruct (P x) => //=; nra.
  - apply: (ex_series_le _ (countable_sum (λ n, scal 2 (if P n || Q n then a n else 0)))).
    + intros n.
      rewrite /countable_sum//=.
      rewrite /norm//=/abs//=/scal//=/mult/=.
      destruct (pickle_inv) as [x|] => //=.
      * specialize (Hge x). destruct (P x), (Q x) => //=; rewrite Rabs_right; nra.
      * rewrite Rabs_right; nra.
    + exists (scal 2 v).
      apply (is_series_ext _ _ _
              (λ n, Logic.eq_sym (countable_sum_scal 2 (λ x, if P x || Q x then a x else 0) n))).
      by apply: is_series_scal.
Qed.

Lemma SeriesC_ext a b:
  (∀ n, a n = b n) →
  Series (countable_sum a) = Series (countable_sum b).
Proof.
  intros Hext. apply Series_ext => // n. rewrite /countable_sum.
  destruct (pickle_inv) => //=; nra.
Qed.

Lemma SeriesC_le a b:
  (∀ n, 0 <= a n <= b n) → ex_series (countable_sum b) →
  Series (countable_sum a) <= Series (countable_sum b).
Proof.
  intros Hrange Hex. apply Series_le => // n. rewrite /countable_sum.
  destruct (pickle_inv) => //=; nra.
Qed.

Lemma SeriesC_le' a b:
  (∀ n,  a n <= b n) →
  ex_series (countable_sum a) → ex_series (countable_sum b) →
  Series (countable_sum a) <= Series (countable_sum b).
Proof.
  intros Hrange Hex1 Hex2. apply Series_le' => //= n. rewrite /countable_sum.
  destruct (pickle_inv) => //=. nra.
Qed.

Lemma countable_sum_plus a b:
  ∀ n, (countable_sum (λ x, a x + b x) n = (λ n, countable_sum a n + countable_sum b n) n).
Proof.
  intros. rewrite //=/countable_sum; destruct pickle_inv => //=. nra.
Qed.

Lemma countable_sum_Rabs a:
  ∀ n, (countable_sum (λ x, Rabs (a x)) n) = (λ n, Rabs (countable_sum a n)) n.
Proof.
  intros. rewrite //=/countable_sum; destruct pickle_inv => //=. rewrite Rabs_R0 //=.
Qed.

Lemma ex_seriesC_le a b:
  (∀ n, 0 <= a n <= b n) → ex_series (countable_sum b) →
  ex_series (countable_sum a).
Proof.
  intros Hle Hex. unshelve (apply: ex_series_le; eauto).
  intros n. rewrite /norm//=/abs//=.
  rewrite -countable_sum_Rabs. apply countable_sum_le.
  intros x. destruct (Hle x); eauto. rewrite Rabs_right; eauto; nra.
Qed.

Lemma countable_sum_scal_l c a:
  ∀ n, (countable_sum (λ x, c * a x) n = (λ n, c * (countable_sum a n)) n).
Proof.
  intros. rewrite //=/countable_sum; destruct pickle_inv => //=. nra.
Qed.

Lemma countable_sum_scal_r c a:
  ∀ n, (countable_sum (λ x, a x * c) n = (λ n, (countable_sum a n) * c) n).
Proof.
  intros. rewrite //=/countable_sum; destruct pickle_inv => //=. nra.
Qed.

Lemma SeriesC_scal_l (c : R) a:
  Series (λ n, countable_sum (λ x, c * a x) n) = c * Series (countable_sum a).
Proof.
  intros. rewrite -Series_scal_l. apply Series_ext. apply countable_sum_scal_l.
Qed.

Lemma SeriesC_scal_r (c : R) a:
  Series (λ n, countable_sum (λ x, a x * c) n) = Series (countable_sum a) * c.
Proof.
  intros. rewrite -Series_scal_r. apply Series_ext. apply countable_sum_scal_r.
Qed.

Lemma ex_seriesC_scal_l (c : R) a:
  ex_series (countable_sum a) →
  ex_series (countable_sum (λ x, c * a x)).
Proof.
  intros. eapply ex_series_ext.
  { intros n. rewrite countable_sum_scal_l. done. }
  apply: ex_series_scal_l; eauto.
Qed.

Lemma ex_seriesC_scal_r (c : R) a:
  ex_series (countable_sum a) →
  ex_series (countable_sum (λ x, a x * c)).
Proof.
  intros. eapply ex_series_ext.
  { intros n. rewrite countable_sum_scal_r. done. }
  apply: ex_series_scal_r; eauto.
Qed.

Lemma ex_seriesC_plus a b:
  ex_series (countable_sum a) →
  ex_series (countable_sum b) →
  ex_series (countable_sum (λ x, a x + b x)).
Proof.
  intros. eapply ex_series_ext.
  { intros n. rewrite countable_sum_plus. done. }
  apply: ex_series_plus; eauto.
Qed.

Lemma is_seriesC_scal_l (c : R) a v:
  is_series (countable_sum a) v →
  is_series (countable_sum (λ x, c * a x)) (c * v).
Proof.
  intros. eapply is_series_ext.
  { intros n. rewrite countable_sum_scal_l. done. }
  apply: is_series_scal_l; eauto.
Qed.

Lemma is_seriesC_scal_r (c : R) a v:
  is_series (countable_sum a) v →
  is_series (countable_sum (λ x, a x * c)) (v * c).
Proof.
  intros. eapply is_series_ext.
  { intros n. rewrite countable_sum_scal_r. done. }
  apply: is_series_scal_r; eauto.
Qed.

Lemma is_seriesC_plus a b v1 v2:
  is_series (countable_sum a) v1 →
  is_series (countable_sum b) v2 →
  is_series (countable_sum (λ x, a x + b x)) (v1 + v2).
Proof.
  intros. eapply is_series_ext.
  { intros n. rewrite countable_sum_plus. done. }
  apply: is_series_plus; eauto.
Qed.


Lemma is_seriesC_bump (x' : A) v:
  is_series (countable_sum (λ x, if x == x' then v else 0)) v.
Proof.
  eapply is_series_ext; last apply (is_series_bump (pickle x')).
  intros n => //=.
  destruct (eq_nat_dec n (pickle x')) as [Heq|Hneq].
  - rewrite /countable_sum. subst. by rewrite pickleK_inv //= eq_refl.
  - rewrite /countable_sum//=. case_eq (@pickle_inv A n).
    * intros s Heq => //=. case: ifP.
      ** move /eqP; intros; subst. exfalso.
         apply Hneq. symmetry; apply pickle_inv_some_inv; eauto.
      ** done.
    * rewrite //=.
Qed.

Lemma ex_seriesC_Rabs a:
  ex_series (countable_sum (λ x, Rabs (a x))) →
  ex_series (countable_sum a).
Proof.
  intros. eapply ex_series_Rabs.
  eapply ex_series_ext.
  { intros n. rewrite -countable_sum_Rabs. done. }
  eauto.
Qed.

Lemma SeriesC_bump (x' : A) v:
  Series (countable_sum (λ x, if x == x' then v else 0)) = v.
Proof.
  apply is_series_unique, is_seriesC_bump.
Qed.

Lemma SeriesC_0 a:
  (∀ x, a x = 0) →
  Series (countable_sum a) = 0.
Proof.
  intros Heq0. apply Series_0 => n. rewrite /countable_sum.
  destruct (pickle_inv); eauto.
Qed.

End countable_series_facts.
