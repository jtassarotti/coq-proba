From discprob.basic Require Import base sval order monad bigop_ext nify seq_ext.
Require Import Reals Psatz Omega.

Require ClassicalEpsilon.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
Global Set Bullet Behavior "Strict Subproofs".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype finset finfun bigop.

Local Open Scope R_scope.
From discprob.idxval Require Import fin_ival pival fin_ival_dist pival_dist.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.idxval Require extrema.

Import List.

Definition Ex_ival {X} (f: X → R) (I: ival X) : R :=
  \big[Rplus/0]_(i in idx I)
              (f (ind I i) * val I i).


Section Ex_ival_properties.

  Lemma Ex_ival_mret {X} f (r: X):
    Ex_ival f (mret r) = f r.
  Proof.
    rewrite /Ex_ival/index_enum {1}[@Finite.enum]unlock //= big_cons big_nil //=.
    nra.
  Qed.

  Lemma Ex_ival_iplus {X} f (I1 I2: ival X) :
    Ex_ival f (iplus I1 I2) = (Ex_ival f I1) + (Ex_ival f I2).
  Proof.
    rewrite /Ex_ival/index_enum {1}[@Finite.enum]unlock
            /sum_enum big_cat ?big_map //= -?big_distrr //=.
  Qed.

  Lemma Ex_ival_iscale {X} f p (I: ival X) :
    Ex_ival f (iscale p I) =  Rabs p * (Ex_ival f I).
  Proof.
    rewrite /Ex_ival big_distrr //=.
    apply eq_bigr => i ?; nra.
  Qed.

  Lemma Ex_ival_negate {X} f (I: ival X) :
    Ex_ival (λ x, - f x) I = - Ex_ival f I.
  Proof.
    replace (- Ex_ival f I) with (-1 * Ex_ival f I); last by nra.
    rewrite /Ex_ival big_distrr //=.
    apply eq_bigr => ?. nra.
  Qed.
   
  Lemma Ex_ival_sum_support' {X} (I: ival X) f P :
    \big[Rplus/0]_(i : idx I | P i) (f i * val I i)
      = \big[Rplus/0]_(i : support (val I) | P (sval i)) (f (sval i) * val I (sval i)).
  Proof.
    symmetry.  rewrite /index_enum. apply sum_reidx_map with (h := sval) => //=.
    * intros (a&Hgt) ?? => //=. rewrite -enumT mem_enum //=.
    * intros b _ HP Hneq. specialize (val_nonneg I b).
      destruct 1 as [Hgt|Heq0]; auto.
      exfalso. apply Hneq.
      exists (coerce_supp _ _ Hgt); repeat split; auto.
      rewrite -enumT mem_enum //=.
      rewrite Heq0. nra.
    * rewrite -enumT. apply enum_uniq.
    * rewrite -enumT. apply enum_uniq.
    * intros. by apply sval_inj_pred.
  Qed.

  Lemma Ex_ival_sum_support {X} f (I: ival X) :
    Ex_ival f I
      = \big[Rplus/0]_(i : support (val I)) (f (ind I (sval i)) * val I (sval i)).
  Proof.
    rewrite /Ex_ival. apply (Ex_ival_sum_support' I (λ x, f (ind I x)) (λ x, true)).
  Qed.

  Lemma Ex_ival_sum_support_pred {X} f (I: ival X) :
    Ex_ival f I
      = \big[Rplus/0]_(i | Rgt_dec (val I i) 0) (f (ind I i) * val I i).
  Proof.
    rewrite /Ex_ival.
    rewrite bigop_cond_non0.
    symmetry.
    rewrite bigop_cond_non0.
    apply eq_bigl => //=.
    intros i. destruct Rgt_dec => //=.
    destruct (val_nonneg I i) as [Hgt|Heq] => //=; try nra. 
    rewrite Heq Rmult_0_r eq_refl //=.
  Qed.

  Lemma Ex_ival_mono {X} f1 f2 (I: ival X):
    (∀ x, f1 x ≤ f2 x) →
    Ex_ival f1 I ≤ Ex_ival f2 I.
  Proof.
    intros Hf.
    rewrite /Ex_ival; apply Rle_bigr => i Hin.
    specialize (val_nonneg I i) => ?.
    specialize (Hf (ind I i)). nra.
  Qed.

  Lemma Ex_ival_mono_support {X} f1 f2 (I: ival X):
    (∀ x, val I x > 0 → f1 (ind I x) ≤ f2 (ind I x)) →
    Ex_ival f1 I ≤ Ex_ival f2 I.
  Proof.
    intros Hf.
    rewrite /Ex_ival; apply Rle_bigr => i Hin.
    destruct (val_nonneg I i) as [Hgt|Heq0].
    * specialize (Hf i Hgt); nra.
    * rewrite Heq0. nra.
  Qed.

  Lemma Ex_ival_proper' {X} f1 f2 (I1 I2: ival X):
    (∀ x, f1 x = f2 x) →
    eq_ival I1 I2 →
    Ex_ival f1 I1 = Ex_ival f2 I2.
  Proof.
    intros Hext Heq.
    rewrite ?Ex_ival_sum_support.
    destruct Heq as (h1&h2&Hinv&?&Hind&Hval).
    apply (sum_reidx_surj1 _ _ _ _ _ _ (h1)).
    - intros. by rewrite Hext ?Hind ?Hval.
    - intros. split; auto.
      rewrite /index_enum -enumT mem_enum //=.
    - intros b. exists (h2 b). split; auto.
      rewrite /index_enum -enumT mem_enum //=.
    - rewrite /index_enum -enumT. apply enum_uniq.
    - rewrite /index_enum -enumT. apply enum_uniq.
    - intros x1 x2.  intros Heq%(f_equal h2).
      by rewrite ?Hinv in Heq.
  Qed.
    
  Lemma Ex_ival_proper {X} f (I1 I2: ival X):
    eq_ival I1 I2 →
    Ex_ival f I1 = Ex_ival f I2.
  Proof. intros; by apply Ex_ival_proper'. Qed.

  Global Instance Ex_ival_proper_instance:
    ∀ (X : Type), Proper ((pointwise_relation _ eq) ==> @eq_ival X ==> eq) (Ex_ival).
  Proof.
    intros X f1 f2 ? I1 I2 Heq.
    by apply Ex_ival_proper'.
  Qed.


  Lemma Ex_ival_bind_irrel {X Y} f (I: ival X) (m: ival Y):
    \big[Rplus/0]_i (val m i) = 1 →
    Ex_ival f (mbind (λ x, I) (m: ival Y)) = Ex_ival f I.
  Proof.
    intros Hsum1.
    rewrite {1}/Ex_ival//=.
    rewrite /index_enum {1}[@Finite.enum]unlock //=.
    rewrite /tag_enum big_flatten //= big_map.
    etransitivity.
    eapply eq_bigr => i ?. 
    { rewrite ?big_map /=.
      etransitivity; first eapply eq_bigr => j ?.
      { 
        rewrite -Rmult_assoc Rmult_comm -Rmult_assoc.
        done.
      }
      rewrite /= -big_distrl /= .
      rewrite (eq_bigl (λ x, true)); first done.
      intros j => //=.
    }
    rewrite //=.
    rewrite -big_distrr //=.
    rewrite -[a in _ = a]Rmult_1_r.
    f_equal.
    { rewrite /Ex_ival/index_enum//=. apply congr_big; auto.
      intros; nra. }
    apply Hsum1.
  Qed.

  Lemma Ex_ival_bind_le {X Y1 Y2} f1 f2 (I: ival X) (h1 : X → ival Y1) (h2: X → ival Y2):
    (∀ a, (∃ x, val I x > 0 ∧ ind I x = a) →
                Ex_ival f1 (h1 a) ≤ Ex_ival f2 (h2 a)) →
    Ex_ival f1 (mbind h1 I) ≤ Ex_ival f2 (mbind h2 I).
  Proof.
    intros Hh.
    rewrite ?Ex_ival_sum_support_pred.
    rewrite /index_enum {1}[@Finite.enum]unlock //=.
    rewrite /tag_enum big_flatten //= big_map.
    rewrite /index_enum {3}[@Finite.enum]unlock //=.
    rewrite /tag_enum big_flatten //= big_map.
    eapply Rle_bigr => i ?.
    rewrite ?big_map //=.
    destruct (val_nonneg I i) as [Hgt|Heq]; last first.
    { rewrite Heq //=. transitivity 0; right.
      * rewrite big1 //= => i'. rewrite Rmult_0_l. destruct Rgt_dec => //=; nra.
      * rewrite big1 //= => i'. rewrite Rmult_0_l. destruct Rgt_dec => //=; nra.
    }
    assert ( val I i * Ex_ival f1 (h1 (ind I i)) ≤ val I i * Ex_ival f2 (h2 (ind I i))) as Hle'.
    { apply Rmult_le_compat_l; first apply Rge_le, val_nonneg.
      eapply Hh; eauto.
    }
    etransitivity; first (etransitivity; last eapply Hle').
    - rewrite Ex_ival_sum_support_pred.
      rewrite big_distrr.
      rewrite //=.
      right. apply congr_big  => //=.
      * intros i' => //=. repeat destruct Rgt_dec => //=; nra.
      * intros i' Hgt'. nra.
    - rewrite Ex_ival_sum_support_pred.
      rewrite big_distrr.
      rewrite //=.
      right. apply congr_big  => //=.
      * intros i' => //=. repeat destruct Rgt_dec => //=; nra.
      * intros i' Hgt'. nra.
  Qed.

  Lemma Ex_ival_bind_eq {X Y1 Y2} f1 f2 (I: ival X) (h1: X → ival Y1) (h2: X → ival Y2):
    (∀ a, (∃ x, val I x > 0 ∧ ind I x = a) →
                Ex_ival f1 (h1 a) = Ex_ival f2 (h2 a)) →
    Ex_ival f1 (mbind h1 I) = Ex_ival f2 (mbind h2 I).
  Proof.
    intros Hcontinue; apply Rle_antisym; apply Ex_ival_bind_le.
    - intros a (?&?&?). 
      right; apply Hcontinue; eauto.
    - intros a (?&?&?). 
      right; symmetry; apply Hcontinue; eauto.
  Qed.
    
  Lemma Ex_ival_ivdplus {X} f p Hpf (I1 I2: ivdist X) :
    Ex_ival f (ivdplus p Hpf I1 I2 : ival X) = p * Ex_ival f I1 + (1 - p) * Ex_ival f I2.
  Proof.
    rewrite /ivdplus//= Ex_ival_iplus !Ex_ival_iscale.
    rewrite ?Rabs_right //=; nra.
  Qed.

  Lemma Ex_ival_bind_post {X Y} f (I: ival X) (h: X → ival Y):
    Ex_ival f (x ← I; h x) = Ex_ival (λ x, Ex_ival f (h x)) I.
  Proof.
    rewrite /Ex_ival//=.
    rewrite /index_enum {1}[@Finite.enum]unlock //=.
    rewrite /tag_enum big_flatten //= big_map.
    apply eq_bigr => i Hin.
    rewrite big_map => //=.
    rewrite big_distrl => //=.
    apply eq_bigr => ??.
    nra.
  Qed.

End Ex_ival_properties.

Definition Ex_ivd {X} (f: X → R) (I: ivdist X) : R := Ex_ival f I.

Section Ex_ivd_properties.

  Lemma Ex_ivd_plus {X} f p Hpf (I1 I2: ivdist X) :
    Ex_ivd f (ivdplus p Hpf I1 I2) = p * Ex_ivd f I1 + (1 - p) * Ex_ivd f I2.
  Proof. apply Ex_ival_ivdplus. Qed.

  Lemma Ex_ivd_bind_irrel {X Y} f (I: ivdist X) (m: ivdist Y):
    Ex_ivd f (mbind (λ x, I) m) = Ex_ivd f I.
  Proof.
    rewrite /Ex_ivd//=.
    apply Ex_ival_bind_irrel, val_sum1.
  Qed.

  Lemma Ex_ivd_plus_const {X} f (I: ivdist X) k:
    Ex_ivd (λ x, f x + k) I = Ex_ivd f I + k.
  Proof.
    rewrite /Ex_ival.
    etransitivity.
    { eapply eq_bigr => i Hin.
      rewrite Rmult_plus_distr_r. done.
    }
    rewrite big_split => //=; f_equal.
    rewrite -big_distrr.
    rewrite val_sum1 => //=. nra.
  Qed.

  Lemma Ex_ivd_scale_const {X} f (I: ivdist X) k:
    Ex_ivd (λ x, k * (f x)) I = k * (Ex_ivd f I).
  Proof.
    rewrite /Ex_ivd/Ex_ival//=.
    rewrite big_distrr => //=.
    apply eq_bigr => ??; nra.
  Qed.

  Lemma Ex_ivd_const {X} (I: ivdist X) k:
    Ex_ivd (λ x, k) I = k.
  Proof.
    rewrite /Ex_ivd/Ex_ival//=.
    rewrite -big_distrr val_sum1 => //=; nra.
  Qed.

  Lemma Ex_ivd_ivdplus {X} f p Hpf (I1 I2: ivdist X) :
    Ex_ivd f (ivdplus p Hpf I1 I2) = p * Ex_ivd f I1 + (1 - p) * Ex_ivd f I2.
  Proof.
    rewrite /Ex_ivd. rewrite Ex_ival_ivdplus //=.
  Qed.

  Lemma Ex_ivd_sum {X} (f1 f2: X → R) (I: ivdist X):
    Ex_ivd (λ x, f1 x + f2 x) I = Ex_ivd f1 I + Ex_ivd f2 I.
  Proof.
    rewrite /Ex_ivd/Ex_ival. etransitivity.
    { eapply eq_bigr => i ?. ring_simplify. done. }
    rewrite //=. apply big_split.
  Qed.

  Global Instance Ex_ivd_proper_instance:
    ∀ (X : Type), Proper ((pointwise_relation _ eq) ==> @eq_ivd X ==> eq) (Ex_ivd).
  Proof.
    intros X f1 f2 ? I1 I2 Heq.
    by apply Ex_ival_proper'.
  Qed.

End Ex_ivd_properties.

From discprob.idxval Require Import pidist_fin_singleton.

Lemma ex_Ex_extrema_singleton {X} f (I: ivdist X):
  extrema.ex_Ex_extrema f (singleton I).
Proof.
  intros I' <-.
  rewrite /extrema.ex_Ex_ival.
  rewrite //=. eexists. apply SeriesF_is_seriesC.
Qed.

Lemma is_Ex_ival_fin {X} f (I: ival X):
  extrema.is_Ex_ival f (fin_coerce I) (Ex_ival f I).
Proof.
  rewrite /extrema.is_Ex_ival/extrema.ex_Ex_ival.
  split.
  * rewrite //=. eexists. apply SeriesF_is_seriesC.
  * rewrite //=. apply Series_correct'.
    ** rewrite SeriesC_SeriesF SeriesF_big_op //=.
    ** eexists; apply SeriesF_is_seriesC.
Qed.

Import Lub Rbar.

Lemma Ex_min_singleton {X} f (I: ivdist X):
  extrema.Ex_min f (singleton I) = Finite (Ex_ival f I).
Proof.
  rewrite fin_singleton_equiv_singleton extrema.Ex_min_singleton.
  * rewrite //=. f_equal. apply extrema.is_Ex_ival_unique.
    apply is_Ex_ival_fin.
  * rewrite //=. eapply extrema.is_Ex_ival_ex. apply is_Ex_ival_fin.
Qed.

Lemma Ex_max_singleton {X} f (I: ivdist X):
  extrema.Ex_max f (singleton I) = Finite (Ex_ival f I).
Proof.
  rewrite fin_singleton_equiv_singleton extrema.Ex_max_singleton.
  * rewrite //=. f_equal. apply extrema.is_Ex_ival_unique.
    apply is_Ex_ival_fin.
  * rewrite //=. eapply extrema.is_Ex_ival_ex. apply is_Ex_ival_fin.
Qed.