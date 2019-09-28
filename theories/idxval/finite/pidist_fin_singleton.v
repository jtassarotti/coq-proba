Require Import Reals Psatz Omega.
Local Open Scope R_scope.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
From discprob.basic Require Import base sval order monad bigop_ext nify.
From discprob.idxval Require Import pival_dist pival fin_ival fin_ival_dist.
From discprob.prob Require Import finite.
Require Import stdpp.tactics.

From discprob.idxval Require pidist_singleton.

Definition fin_coerce {X} (I: ival X) : ival.ival X.
  unshelve (econstructor).
  - exact (idx I). 
  - exact (val I).
  - exact (ind I).
  - exact (val_nonneg I).
Defined.

Definition fin_coerce_ivd {X} (I: ivdist X) : ival_dist.ivdist X.
  unshelve (econstructor).
  - exact (fin_coerce I). 
  - abstract (destruct I as [[] ?] => //=;
              apply prob.Series_correct';
              [ rewrite finite.SeriesC_SeriesF SeriesF_big_op; apply val_sum1 |
                eexists; apply SeriesF_is_seriesC]).
Defined.

Lemma ival_idx_coerce {X} (I: ival X): ival.idx (fin_coerce I) = idx I.
Proof.
  destruct I => //=.
Qed.

Lemma fin_coerce_bind {X A} (I: ival X) (f: X → ival A) :
  ival.eq_ival (fin_coerce (x ← I; f x))
               (x ← (fin_coerce I); fin_coerce (f x)).
Proof.
  rewrite /ival.ival_bind //=.
  rewrite /fin_coerce//=. apply ival.eq_ival_quasi_refl.
Qed.

Lemma fin_coerce_plus_unfold {X} (I1 I2: ival X) :
  fin_coerce (iplus I1 I2) =
               (ival.iplus (fin_coerce I1) (fin_coerce I2)).
Proof. rewrite //=. Qed.

Lemma fin_coerce_scale_unfold {X} p (I1: ival X):
  fin_coerce (iscale p I1) = ival.iscale p (fin_coerce I1).
Proof. rewrite /iscale/ival.iscale//=/fin_coerce//=. f_equal.
       apply classical_proof_irrelevance.
Qed.

Lemma fin_coerce_ivdplus_unfold {X} p (I1 I2: ival X) :
  ival.eq_ival (fin_coerce (iplus (iscale p I1) (iscale (1 - p) I2)))
               (ival.iplus (ival.iscale p (fin_coerce I1)) (ival.iscale (1 - p) (fin_coerce I2))).
Proof.
  rewrite /fin_coerce/ival.iplus/ival.iscale//=.
  apply ival.eq_ival_quasi_refl.
Qed.

Definition singleton {X} (I: ivdist X) : pidist X.
Proof.
  unshelve (econstructor).
  { refine {| choices := λ I', (fin_coerce I) = I' |}.
    abstract (eexists; eauto). }
  - abstract (intros I' <-; destruct I as [[] ?] => //=;
              apply prob.Series_correct';
              [ rewrite finite.SeriesC_SeriesF SeriesF_big_op; apply val_sum1 |
                eexists; apply SeriesF_is_seriesC]).
Defined.

Global Instance singleton_proper X : Proper (@eq_ivd X ==> @eq_pidist X) singleton.
Proof.
  intros Is1 Is2 Heq.
  rewrite /eq_pidist/eq_pival; split.
  - intros ? <-.
    exists (fin_coerce Is2). split.
    * rewrite /ival.eq_ival.
      destruct Is1 as [[] ?].
      destruct Is2 as [[] ?] => //=.
    * rewrite //=.
  - intros ? <-.
    exists (fin_coerce Is1).
    destruct Is1 as [[] ?] => //=.
Qed.

Transparent pidist_ret.
Lemma singleton_mret {X} (x: X) : eq_pidist (singleton (mret x)) (mret x).
Proof.
  rewrite //=/singleton/base.mret//=/pidist_ret//=/base.mret//=.
  split.
  - intros I <-. subst.
    eexists; split; last first.
    { eexists. }
    rewrite //=.
    unshelve (eexists); first by eauto.
    unshelve (eexists); first by eauto.
    repeat split => //=.
  - intros I ->. subst.
    eexists; split; last first.
    { eexists. }
    rewrite //=.
    unshelve (eexists); first by eauto.
    unshelve (eexists); first by eauto.
    repeat split => //=.
Qed.

Lemma singleton_bind {X Y} (I: ivdist X) (f: X → ivdist Y) :
  eq_pidist (singleton (mbind f I)) (x ← singleton I; singleton (f x)).
Proof.
  split.
  - intros ? <-; subst.
    edestruct (pival_mbind_in (singleton I) (λ x, singleton (f x))
                              (fin_coerce I)
                              (λ i, fin_coerce (f (ival.ind (fin_coerce I) i))))
      as (Ib&pf&Heq&Hin); eauto.
    * done.
    * intros. done.
  - intros I' Hin.
    apply pival_mbind_in_inv in Hin as (Ix&h&Hhgt0&Hin&Hin'&?).
    eexists; split; last first;
    rewrite /In/singleton//= in Hin. subst.
    etransitivity; first by (symmetry; eauto).

    eapply ival.eq_ival_nondep_option_suffice.
    unshelve (eexists).
    { 
      intros (i&ih).
      destruct (Rgt_dec (val I i) 0) as [Hgt|Hngt].
      * assert (h i = fin_coerce (f (ind I i))) as Heq.
        {
          feed pose proof (Hin' i); eauto.
        }
        apply Some.
        exists i.
        rewrite Heq in ih. exact ih.
      * exact None.
    }
    unshelve (eexists).
    { 
      intros (i&ifx).
      destruct (Rgt_dec (val I i) 0) as [Hgt|Hngt].
      * assert (h i = fin_coerce (f (ind I i))) as Heq.
        {
          feed pose proof (Hin' i); eauto.
        }
        apply Some.
        exists i. rewrite Heq. exact ifx.
      * exact None.
    }
    repeat split => //=.
    * intros (i&ifx) => //=.
      intros Hgt. destruct Rgt_dec => //=; last first.
      { specialize (val_nonneg (f (ind I i)) ifx). nra. }
      destruct (Hin' i r) => //=.
    * intros (i&ih) => //=.
      intros Hgt. case_eq (Rgt_dec (val I i) 0); last first.
      { intros. specialize (ival.val_nonneg (h i) ih). nra. }
      intros Hgt1 => ->.
      f_equal. f_equal.
      destruct (Hin' i _) => //=.
    * intros (i&ifx) => //=.
      intros Hgt. case_eq (Rgt_dec (val I i) 0); last first.
      { specialize (val_nonneg (f (ind I i)) ifx). intros. nra. }
      intros Hgt1 => ->.
      f_equal. f_equal.
      destruct (Hin' _ _) => //=.
    * intros (i&ih) => //=.
      intros Hgt. case_eq (Rgt_dec (val I i) 0); last first.
      { intros. specialize (ival.val_nonneg (h i) ih). nra. }
      intros Hgt1 ?. rewrite //=.
      destruct (Hin' i Hgt1) => //=.
    * intros (i&ih) => //=.
      intros Hgt. case_eq (Rgt_dec (val I i) 0); last first.
      { intros. specialize (ival.val_nonneg (h i) ih). nra. }
      intros Hgt1 ?. rewrite //=.
      destruct (Hin' i Hgt1) => //=.
Qed.

Lemma singleton_plus {X} p Hpf (I1 I2: ivdist X) :
  eq_pidist (singleton (ivdplus p Hpf I1 I2)) (pidist_plus p Hpf (singleton I1) (singleton I2)).
Proof.
  split.
  - intros ? <-.
    eexists; split.
    { rewrite fin_coerce_ivdplus_unfold. reflexivity. }
    { rewrite //=/pidist_plus//=/pplus_aux/In//=.
      do 2 eexists; split_and!; eauto;
      rewrite /pscale_aux;  try (eexists; split; eauto; done).
    }
  - intros ? (?&?&Hin1&Hin2&->).
    inversion Hin1 as (I1'&Hin1'&Heq1').
    inversion Hin2 as (I2'&Hin2'&Heq2').
    subst. rewrite -Hin1' -Hin2'.

    eexists; split.
    { rewrite -fin_coerce_ivdplus_unfold. reflexivity. } 
    split; eauto.
Qed.

Lemma fin_singleton_equiv_singleton {X} (I: ivdist X):
  eq_pidist (singleton I) (pidist_singleton.singleton (fin_coerce_ivd I)).
Proof.
  split.
  - intros I' <-. 
    eexists; split.
    * reflexivity. 
    * rewrite //=.
  - intros I' <-. 
    eexists; split.
    * reflexivity. 
    * rewrite //=.
Qed.