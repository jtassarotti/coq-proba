Require Import Reals Psatz Omega.
Local Open Scope R_scope.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
From discprob.basic Require Import base sval order monad bigop_ext nify.
From discprob.idxval Require Import pival_dist pival ival ival_dist.
Require Import stdpp.tactics.


Definition singleton {X} (I: ivdist X) : pidist X.
Proof.
  unshelve (econstructor).
  { refine {| choices := λ I', ivd_ival I = I' |}.
    abstract (eexists; eauto). }
  - abstract (intros I' <-; apply val_sum1). 
Defined.

Definition In_pidist {X} (I: ivdist X) (Is: pidist X) : Prop :=
  ∃ I', eq_ival I I' ∧ In I' Is.

Lemma In_pidist_le_singleton {X} (I: ivdist X) Is:
  In_pidist I Is ↔ le_pidist (singleton I) Is.
Proof.
  split.
  - rewrite /In_pidist/singleton//=. intros Hin I' <-. eauto.
  - rewrite /In_pidist/singleton/le_pidist/le_pival//=. 
    intros Hle. apply Hle.
    rewrite /In. done.
Qed.

Global Instance singleton_proper X : Proper (@eq_ivd X ==> @eq_pidist X) singleton.
Proof.
  intros Is1 Is2 Heq.
  rewrite /eq_pidist/eq_pival; split.
  - intros ? <-.
    exists Is2. split; first done.
    done.
  - intros ? <-.
    exists Is1. split; first by (symmetry).
    done.
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
                              I (λ i, f (ind I i)))
      as (Ib&pf&Heq&Hin); eauto.
    * done.
    * intros. done.
  - intros I' Hin.
    apply pival_mbind_in_inv in Hin as (Ix&h&Hhgt0&Hin&Hin'&?).
    eexists; split; last first;
    rewrite /In/singleton//= in Hin. subst.
    etransitivity; first by (symmetry; eauto).

    eapply eq_ival_nondep_option_suffice.
    unshelve (eexists).
    { 
      intros (i&ih).
      destruct (Rgt_dec (val I i) 0) as [Hgt|Hngt].
      * assert (h i = f (ind I i)) as Heq.
        {
          feed pose proof (Hin' i); eauto.
        }
        apply Some.
        exists i. rewrite -Heq. exact ih.
      * exact None.
    }
    unshelve (eexists).
    { 
      intros (i&ifx).
      destruct (Rgt_dec (val I i) 0) as [Hgt|Hngt].
      * assert (h i = f (ind I i)) as Heq.
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
      match goal with
      | [ |- context [ eq_rect_r _ _ ?Hpf ] ] => destruct Hpf => //=
      end.
    * intros (i&ih) => //=.
      intros Hgt. case_eq (Rgt_dec (val I i) 0); last first.
      { intros. specialize (val_nonneg (h i) ih). nra. }
      intros Hgt1 => ->.
      f_equal. f_equal.
      rewrite rew_opp_l. done.
    * intros (i&ifx) => //=.
      intros Hgt. case_eq (Rgt_dec (val I i) 0); last first.
      { specialize (val_nonneg (f (ind I i)) ifx). intros. nra. }
      intros Hgt1 => ->.
      f_equal. f_equal.
      rewrite rew_opp_r. done.
    * intros (i&ih) => //=.
      intros Hgt. case_eq (Rgt_dec (val I i) 0); last first.
      { intros. specialize (val_nonneg (h i) ih). nra. }
      intros Hgt1 ?. rewrite //=.
      destruct (Hin' i Hgt1) => //=.
    * intros (i&ih) => //=.
      intros Hgt. case_eq (Rgt_dec (val I i) 0); last first.
      { intros. specialize (val_nonneg (h i) ih). nra. }
      intros Hgt1 ?. rewrite //=.
      destruct (Hin' i Hgt1) => //=.
Qed.

Lemma singleton_plus {X} p Hpf (I1 I2: ivdist X) :
  eq_pidist (singleton (ivdplus p Hpf I1 I2)) (pidist_plus p Hpf (singleton I1) (singleton I2)).
Proof.
  split.
  - intros ? <-.
    eexists; split; eauto.
    { rewrite //=/pidist_plus//=/pplus_aux/In//=.
      do 2 eexists; split_and!; eauto;
      rewrite /pscale_aux;  eexists; split; eauto; done.
    }
  - intros ? (?&?&Hin1&Hin2&->).
    eexists; split; eauto.
    rewrite /singleton//=/In.
    f_equal.
    * rewrite /pscale/pscale_aux//= in Hin1.
      firstorder.
    * rewrite /pscale/pscale_aux//= in Hin2.
      firstorder.
Qed.

Lemma singleton_bind_comm {X Y Z} (I1: ivdist X) (I2: ivdist Y) (f: X → Y → pidist Z) :
  eq_pidist (x ← singleton I1; y ← singleton I2; f x y)
            (y ← singleton I2; x ← singleton I1; f x y).
Proof.
  transitivity (z ← (x ← singleton I1; y ← singleton I2; mret (x, y)); f (fst z) (snd z)).
  { setoid_rewrite pidist_assoc.
    apply pidist_bind_congr; first reflexivity.
    intros.
    setoid_rewrite pidist_assoc.
    apply pidist_bind_congr; first reflexivity.
    setoid_rewrite pidist_left_id.
    rewrite //=.
  }
  transitivity (z ← (y ← singleton I2; x ← singleton I1; mret (x, y)); f (fst z) (snd z)).
  {
    apply pidist_bind_congr; last reflexivity.
    setoid_rewrite <-singleton_mret.
    setoid_rewrite <-singleton_bind.
    setoid_rewrite <-singleton_bind.
    apply singleton_proper.
    apply ival_bind_comm.
  }
  { setoid_rewrite pidist_assoc.
    apply pidist_bind_congr; first reflexivity.
    intros.
    setoid_rewrite pidist_assoc.
    apply pidist_bind_congr; first reflexivity.
    setoid_rewrite pidist_left_id.
    rewrite //=.
  }
Qed.
  