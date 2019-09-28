From discprob.basic Require Import base sval order monad bigop_ext nify seq_ext.
Require Import Reals Psatz Omega.

Require ClassicalEpsilon.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
Global Set Bullet Behavior "Strict Subproofs".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq div choice fintype finset finfun bigop.
Require Import stdpp.tactics.

Local Open Scope R_scope.
From discprob.idxval Require Import ival pival ival_dist pival_dist pidist_singleton.
From discprob.prob Require Import prob countable finite stochastic_order.

Import Lub.

Definition Ex_ival {X} (f: X → R) (I: ival X) : R :=
  Series (countable_sum (λ i, f (ind I i) * val I i)).

Definition ex_Ex_ival {X} (f: X → R) (I: ival X) :=
  ex_series (countable_sum (λ i, Rabs (f (ind I i) * val I i))).

Definition is_Ex_ival {X} (f: X → R) (I: ival X) (v: R) :=
  ex_Ex_ival f I ∧ is_series (countable_sum (λ i, f (ind I i) * val I i)) v.

Section Ex_ival_properties.

  Lemma ex_Ex_ival_is {X} (f: X → R) (I: ival X) :
    ex_Ex_ival f I →
    ∃ v, is_Ex_ival f I v.
  Proof.
    intros Hex.
    rewrite /ex_Ex_ival in Hex. specialize (ex_seriesC_Rabs _ _ Hex).
    intros (v&His).
    exists v. split; eauto.
  Qed.

  Lemma is_Ex_ival_ex {X} f (I: ival X) v:
    is_Ex_ival f I v →
    ex_Ex_ival f I.
  Proof.
    intros (Hex&His).
    auto.
  Qed.

  Lemma is_Ex_ival_unique {X} f (I: ival X) v:
    is_Ex_ival f I v →
    Ex_ival f I = v.
  Proof.
    intros (Hex&His).
    rewrite /Ex_ival. by apply is_series_unique.
  Qed.

  Lemma is_Ex_ival_unique' {X} f (I: ival X) v1 v2:
    is_Ex_ival f I v1 →
    is_Ex_ival f I v2 →
    v1 = v2.
  Proof.
    intros. transitivity (Ex_ival f I).
    { symmetry; apply is_Ex_ival_unique; eauto. }
    apply is_Ex_ival_unique; eauto.
  Qed.

  Lemma Ex_ival_correct {X} (f: X → R) (I: ival X) :
    ex_Ex_ival f I →
    is_Ex_ival f I (Ex_ival f I).
  Proof.
    intros (v&His)%ex_Ex_ival_is.
    rewrite (is_Ex_ival_unique _ _ _ His).
    auto.
  Qed.

  Lemma ex_Ex_ival_ex_series {X} (f: X → R) (I: ival X):
    ex_Ex_ival f I →
    ex_series (countable_sum (λ i, (f (ind I i) * val I i))).
  Proof.
    rewrite /ex_Ex_ival => Hex.
    apply ex_series_Rabs.
    eapply ex_series_ext; last eassumption.
    { intros n. rewrite /countable_sum; destruct (pickle_inv) => //=.
      by rewrite Rabs_R0.
    }
  Qed.

  Lemma ex_Ex_ival_mret {X} f (r: X):
    ex_Ex_ival f (mret r).
  Proof. rewrite /ex_Ex_ival. eexists. eapply SeriesF_is_seriesC. Qed.

  Lemma Ex_ival_mret {X} f (r: X):
    Ex_ival f (mret r) = f r.
  Proof.
    rewrite /Ex_ival.
    rewrite SeriesC_fin_big /index_enum {1}[@Finite.enum]unlock //= big_cons big_nil //=.
    nra.
  Qed.

  Lemma is_Ex_ival_mret {X} f (r: X):
    is_Ex_ival f (mret r) (f r).
  Proof. rewrite -Ex_ival_mret. apply Ex_ival_correct, ex_Ex_ival_mret. Qed.

  Lemma ex_Ex_ival_iscale {X} f p (I: ival X):
    ex_Ex_ival f I →
    ex_Ex_ival f (iscale p I).
  Proof.
    rewrite /ex_Ex_ival//=. intros Hex.
    setoid_rewrite Rabs_mult.
    setoid_rewrite Rabs_mult.
    setoid_rewrite Rmult_comm.
    setoid_rewrite Rmult_assoc.
    eapply ex_series_ext.
    { intros n. rewrite (countable_sum_scal_l _ (Rabs (Rabs p))). done. }
    apply: ex_series_scal.
    setoid_rewrite Rmult_comm; eauto.
    setoid_rewrite Rabs_mult in Hex. eauto.
  Qed.

  Lemma ex_Ex_ival_to_Rabs {X} f (I: ival X):
    ex_Ex_ival f I →
    ex_Ex_ival (λ x, Rabs (f x)) I.
  Proof.
    rewrite /ex_Ex_ival.
    intros. eapply ex_series_ext; last eassumption.
    intros n. apply countable_sum_ext => ?. rewrite ?Rabs_mult.
    f_equal. by rewrite Rabs_Rabsolu. 
  Qed.

  Lemma ex_Ex_ival_from_Rabs {X} f (I: ival X):
    ex_Ex_ival (λ x, Rabs (f x)) I →
    ex_Ex_ival f I.
  Proof.
    rewrite /ex_Ex_ival.
    intros. eapply ex_series_ext; last eassumption.
    intros n. apply countable_sum_ext => ?. rewrite ?Rabs_mult.
    f_equal. by rewrite Rabs_Rabsolu. 
  Qed.

  Lemma Ex_ival_iscale {X} f p (I: ival X) :
    Ex_ival f (iscale p I) =  Rabs p * (Ex_ival f I).
  Proof.
    rewrite /Ex_ival. rewrite //=. 
    setoid_rewrite Rmult_comm.
    setoid_rewrite Rmult_assoc.
    rewrite SeriesC_scal_l => //=.
    rewrite Rmult_comm; f_equal.
    setoid_rewrite Rmult_comm at 1; eauto.
  Qed.

  Lemma is_Ex_ival_iscale {X} f p (I: ival X) :
    ex_Ex_ival f I →
    is_Ex_ival f (iscale p I) (Rabs p * (Ex_ival f I)).
  Proof.
    intros. rewrite -Ex_ival_iscale.
    eapply Ex_ival_correct, ex_Ex_ival_iscale; auto.
  Qed.

  Lemma Ex_ival_scal_l {X} f (I: ival X) c:
    Ex_ival (λ x, c * f x) I = c * Ex_ival f I.
  Proof.
    rewrite /Ex_ival. setoid_rewrite Rmult_assoc. apply SeriesC_scal_l.
  Qed.

  Lemma Ex_ival_scal_r {X} f (I: ival X) c:
    Ex_ival (λ x, f x * c) I = Ex_ival f I * c.
  Proof.
    rewrite /Ex_ival. setoid_rewrite Rmult_comm. setoid_rewrite <-Rmult_assoc.
    rewrite SeriesC_scal_r.
    rewrite Rmult_comm; f_equal.
    setoid_rewrite Rmult_comm at 1; eauto.
  Qed.

  Lemma Ex_ival_negate {X} f (I: ival X) :
    Ex_ival (λ x, - f x) I = - Ex_ival f I.
  Proof.
    replace (- Ex_ival f I) with (-1 * Ex_ival f I); last by nra.
    rewrite - Ex_ival_scal_l.
    rewrite /Ex_ival; eapply SeriesC_ext; eauto.
    intros n; nra.
  Qed.

  (*
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
   *)

  Lemma Ex_ival_mono {X} f1 f2 (I: ival X):
    (∀ x, f1 x ≤ f2 x) →
    ex_Ex_ival f1 I →
    ex_Ex_ival f2 I →
    Ex_ival f1 I ≤ Ex_ival f2 I.
  Proof.
    intros Hf.
    rewrite /Ex_ival.
    intros. eapply Series_le'; eauto using ex_Ex_ival_ex_series.
    intros n. rewrite /countable_sum; destruct pickle_inv => //=; try nra.
    apply Rmult_le_compat_r.
    * apply Rge_le, val_nonneg. 
    * eauto.
  Qed.

  Lemma is_Ex_ival_mono {X} f1 f2 (I: ival X) v1 v2:
    (∀ x, f1 x ≤ f2 x) →
    is_Ex_ival f1 I v1 →
    is_Ex_ival f2 I v2 →
    v1 ≤ v2.
  Proof.
    intros Hle His1 His2.
    rewrite -(is_Ex_ival_unique _ _ _ His1).
    rewrite -(is_Ex_ival_unique _ _ _ His2).
    eapply Ex_ival_mono; eauto; eapply is_Ex_ival_ex; eauto.
  Qed.

  Lemma Ex_ival_mono_support {X} f1 f2 (I: ival X):
    (∀ x, val I x > 0 → f1 (ind I x) ≤ f2 (ind I x)) →
    ex_Ex_ival f1 I →
    ex_Ex_ival f2 I →
    Ex_ival f1 I ≤ Ex_ival f2 I.
  Proof.
    intros Hf.
    intros. eapply Series_le'; eauto using ex_Ex_ival_ex_series.
    intros n. rewrite /countable_sum; destruct pickle_inv as [i|] => //=; try nra.
    destruct (val_nonneg I i) as [Hgt|Heq0].
    * specialize (Hf i Hgt); nra.
    * rewrite Heq0. nra.
  Qed.

  Lemma is_Ex_ival_mono_support {X} f1 f2 (I: ival X) v1 v2:
    (∀ x, val I x > 0 → f1 (ind I x) ≤ f2 (ind I x)) →
    is_Ex_ival f1 I v1 →
    is_Ex_ival f2 I v2 →
    v1 ≤ v2.
  Proof.
    intros Hle His1 His2.
    rewrite -(is_Ex_ival_unique _ _ _ His1).
    rewrite -(is_Ex_ival_unique _ _ _ His2).
    eapply Ex_ival_mono_support; eauto; eapply is_Ex_ival_ex; eauto.
  Qed.

  Lemma is_Ex_ival_proper_fun_support {X} f1 f2 (I: ival X) v:
    (∀ x, val I x > 0 → f1 (ind I x) = f2 (ind I x)) →
    is_Ex_ival f1 I v →
    is_Ex_ival f2 I v.
  Proof.
    intros Hext.
    intros ((z&His_abs)&His).
    rewrite /is_Ex_ival/ex_Ex_ival.
    edestruct (eq_ival_series_fun I I (λ x y, f1 x * y)); eauto.
    { intros; rewrite //=; nra. }
    split.
    * exists z. eapply is_series_ext; last eassumption.
      intros n. eapply countable_sum_ext.
      intros ii. f_equal. destruct (val_nonneg I ii) as [?|Heq0].
      ** rewrite Hext //=. 
      ** rewrite Heq0. nra.
    * eapply is_series_unique in His. rewrite -His.
      eapply is_series_ext; last eassumption.
      intros n. eapply countable_sum_ext.
      intros ii. destruct (val_nonneg I ii) as [?|Heq0].
      ** rewrite Hext //=. 
      ** rewrite Heq0. nra.
  Qed.

  Lemma is_Ex_ival_proper' {X} f1 f2 (I1 I2: ival X) v:
    (∀ x, f1 x = f2 x) →
    eq_ival I1 I2 →
    is_Ex_ival f1 I1 v →
    is_Ex_ival f2 I2 v.
  Proof.
    intros Hext Heq.
    rewrite ?Ex_ival_sum_support.
    intros ((z&His_abs)&His).
    rewrite /is_Ex_ival/ex_Ex_ival.
    edestruct (eq_ival_series_fun I1 I2 (λ x y, f1 x * y)); eauto.
    { intros; rewrite //=; nra. }
    split.
    * exists z. eapply is_series_ext; last eassumption.
      intros n. eapply countable_sum_ext.
      intros. f_equal. rewrite Hext. done.
    * eapply is_series_unique in His. rewrite -His.
      eapply is_series_ext; last eassumption.
      intros n. eapply countable_sum_ext. intros; rewrite Hext; done.
  Qed.

  Lemma ex_Ex_ival_proper' {X} f1 f2 (I1 I2: ival X):
    (∀ x, f1 x = f2 x) →
    eq_ival I1 I2 →
    ex_Ex_ival f1 I1 →
    ex_Ex_ival f2 I2.
  Proof.
    intros Hext Heq Hex.
    apply ex_Ex_ival_is in Hex as (v&His).
    eapply is_Ex_ival_ex. eapply is_Ex_ival_proper'; eauto.
  Qed.

  Lemma is_Ex_ival_proper {X} f (I1 I2: ival X) v:
    eq_ival I1 I2 →
    is_Ex_ival f I1 v →
    is_Ex_ival f I2 v.
  Proof.
    intros. eapply is_Ex_ival_proper'; eauto.
  Qed.

  Lemma ex_Ex_ival_proper {X} f (I1 I2: ival X):
    eq_ival I1 I2 →
    ex_Ex_ival f I1 →
    ex_Ex_ival f I2.
  Proof.
    intros. eapply ex_Ex_ival_proper'; eauto.
  Qed.

  Lemma ex_Ex_ival_le_supp {X} f1 f2 (I: ival X):
    (∀ x, In_isupport x I → Rabs (f1 x) <= Rabs (f2 x)) →
    ex_Ex_ival f2 I →
    ex_Ex_ival f1 I.
  Proof.
    rewrite /ex_Ex_ival.
    intros Hle Hex.
    eapply ex_seriesC_le; last eassumption.
    intros i; split.
    - apply Rabs_pos.
    - rewrite ?Rabs_mult. rewrite Rabs_val.
      destruct (val_nonneg I i) as [?|Heq].
      *  apply Rmult_le_compat_r; first try nra.
         eapply Hle. eexists; eauto.
      * rewrite Heq. nra.
  Qed.

  Lemma ex_Ex_ival_le {X} f1 f2 (I: ival X):
    (∀ x, Rabs (f1 x) <= Rabs (f2 x)) →
    ex_Ex_ival f2 I →
    ex_Ex_ival f1 I.
  Proof.
    intros; eapply ex_Ex_ival_le_supp; eauto.
  Qed.

  Lemma Ex_ival_proper' {X} f1 f2 (I1 I2: ival X):
    (∀ x, f1 x = f2 x) →
    eq_ival I1 I2 →
    ex_Ex_ival f1 I1 →
    Ex_ival f1 I1 = Ex_ival f2 I2.
  Proof.
    intros Hext Heq Hex.
    symmetry. eapply is_Ex_ival_unique.
    apply ex_Ex_ival_is in Hex as (v&His).
    rewrite (is_Ex_ival_unique _ _ _ His).
    eapply is_Ex_ival_proper'; eauto.
  Qed.
    
  Lemma Ex_ival_proper {X} f (I1 I2: ival X):
    eq_ival I1 I2 →
    ex_Ex_ival f I1 →
    Ex_ival f I1 = Ex_ival f I2.
  Proof. intros; by apply Ex_ival_proper'. Qed.

  Global Instance is_Ex_ival_proper_instance:
    ∀ (X : Type), Proper ((pointwise_relation _ eq) ==> @eq_ival X ==> eq ==> iff) (is_Ex_ival).
  Proof.
    intros X f1 f2 ? I1 I2 Heq ?? ->.
    split; eapply is_Ex_ival_proper'; eauto.
    by symmetry.
  Qed.

  Global Instance ex_Ex_ival_proper_instance:
    ∀ (X : Type), Proper ((pointwise_relation _ eq) ==> @eq_ival X ==> iff) (ex_Ex_ival).
  Proof.
    intros X f1 f2 ? I1 I2 Heq.
    split; eapply ex_Ex_ival_proper'; eauto.
    by symmetry.
  Qed.

  (*
  Global Instance Ex_ival_proper_instance:
    ∀ (X : Type), Proper ((pointwise_relation _ eq) ==> @eq_ival X ==> eq) (Ex_ival).
  Proof.
    intros X f1 f2 ? I1 I2 Heq.
    by apply Ex_ival_proper'.
  Qed.
   *)

  Lemma ex_Ex_ival_scal_l {X} f (I: ival X) c:
    ex_Ex_ival f I →
    ex_Ex_ival (λ x, c * f x) I.
  Proof.
    intros Hex.
    rewrite /ex_Ex_ival.
    setoid_rewrite Rmult_assoc.
    setoid_rewrite Rabs_mult.
    apply ex_seriesC_scal_l.
    eauto.
  Qed.

  Lemma is_Ex_ival_scal_l {X} f (I: ival X) c v:
    is_Ex_ival f I v →
    is_Ex_ival (λ x, c * f x) I (c * v).
  Proof.
    intros His.
    rewrite -(is_Ex_ival_unique _ _ _ His).
    rewrite -Ex_ival_scal_l. apply Ex_ival_correct. 
    apply ex_Ex_ival_scal_l.
    eapply is_Ex_ival_ex; eauto.
  Qed.

  Lemma is_Ex_ival_scal_l_inv {X} f (I: ival X) c v:
    c ≠ 0 →
    is_Ex_ival (λ x, c * f x) I v →
    is_Ex_ival f I (/c * v).
  Proof.
    intros Hneq0 His.
    apply (is_Ex_ival_scal_l _ _ (/c)) in His.
    eapply is_Ex_ival_proper'; last eassumption.
    { intros => //=. field. auto. }
    reflexivity.
  Qed.

  Lemma ex_Ex_ival_negate {X} f (I: ival X):
    ex_Ex_ival f I →
    ex_Ex_ival (λ x, - f x) I.
  Proof.
    intros.
    eapply (ex_Ex_ival_proper' (λ x, -1 * f x)).
    { intros x. field. }
    { reflexivity.  }
    { apply ex_Ex_ival_scal_l. eauto. }
  Qed.

  Lemma is_Ex_ival_negate {X} f (I: ival X) v:
    is_Ex_ival f I v →
    is_Ex_ival (λ x, - f x) I (- v).
  Proof.
    intros His.
    rewrite -(is_Ex_ival_unique _ _ _ His).
    rewrite -Ex_ival_negate. apply Ex_ival_correct. 
    apply ex_Ex_ival_negate, His.
  Qed.

  Lemma is_Ex_ival_bind_bounded {X Y} f (g: X → ival Y) (I: ival X) b:
    (∀ i, val I i > 0 → ∃ v, is_Ex_ival (λ x, Rabs (f x)) (g (ind I i)) v ∧ v <= b) →
    ex_series (countable_sum (val I)) → 
    ∃ v, is_series (countable_sum (λ i : idx I, Ex_ival f (g (ind I i)) * val I i)) v ∧
    is_Ex_ival f (mbind g I) v.
  Proof.
    intros Hbounded (v&His_val).
    assert (Hex: ∀ i, val I i > 0 → ∃ v0 : R, is_series
                        (countable_sum (λ i' : idx (g (ind I i)),
                        Rabs (f (ind (g (ind I i)) i') * val (g (ind I i)) i'))) v0 ∧ v0 ≤ b).
    { intros. edestruct Hbounded as (v'&His&Hle); eauto.
      exists v'. split; auto. rewrite /is_Ex_ival in His.
      destruct His. eapply is_series_ext; last eassumption.
      intros n. eapply countable_sum_ext => //= ?. rewrite Rabs_mult.
      f_equal. symmetry; apply Rabs_right; last apply val_nonneg. }
    feed pose proof (ival_dist.prod_pmf_sum g f I) as His_bind.
    { eapply (ival_dist.aprod_double_summable g f v b); eauto. } 
    feed pose proof (ival_dist.ex_series_pmf_row g f I) as Hex_bind; eauto.
    { eapply (ival_dist.aprod_double_summable g f v b); eauto. } 
    destruct Hex_bind as (?&His).
    eexists; split; eauto.
    rewrite /is_Ex_ival//=; split; eauto.
    { rewrite /ex_Ex_ival//=.
      feed pose proof (ival_dist.prod_pmf_sum g (λ x, Rabs (f x)) I) as His_bind'; eauto.
      { eapply (ival_dist.aprod_double_summable g _ v b); eauto.
      intros. edestruct Hex as (v'&His'&Hle); eauto.
      exists v'; split; auto. eapply is_series_ext; last by eassumption.
      intros; eapply countable_sum_ext => ?.
      { rewrite ?Rabs_mult Rabs_Rabsolu. done. } }
      { eexists. rewrite /ival_dist.prod_pmf//= in His_bind'.
        eapply is_series_ext; last eapply His_bind'.
        intros; eapply countable_sum_ext => ?. rewrite Rabs_mult.
        rewrite Rabs_mult.
        rewrite (Rabs_right (val _ _)); last apply val_nonneg.
        rewrite (Rabs_right (val _ _)); last apply val_nonneg.
        nra.
      }
    }
    rewrite -(is_series_unique _ _ His).
    eapply is_series_ext; last eassumption.
    intros; eapply countable_sum_ext => ?.
    rewrite /ival_dist.prod_pmf //=. nra.
  Qed.
    
  Lemma Ex_ival_bind_bounded {X Y} f (g: X → ival Y) (I: ival X) b:
    (∀ i, val I i > 0 → ∃ v, is_Ex_ival (λ x, Rabs (f x)) (g (ind I i)) v ∧ v <= b) →
    ex_series (countable_sum (val I)) → 
    Ex_ival f (mbind g I) = 
    Series (countable_sum (λ i : idx I, Ex_ival f (g (ind I i)) * val I i)).
  Proof.
    intros Hgt Hex. apply is_Ex_ival_unique.
    edestruct (is_Ex_ival_bind_bounded _ _ _ _ Hgt Hex) as (v&His&?).
    rewrite (is_series_unique _ _ His). eauto.
  Qed.

  Lemma is_Ex_ival_bind_irrel {X Y} f (I: ival X) (m: ival Y) v:
    is_series (countable_sum (val m)) 1 → 
    is_Ex_ival f I v →
    is_Ex_ival f (mbind (λ x, I) m) v.
  Proof.
    intros His Hex.
    feed pose proof (ex_Ex_ival_to_Rabs f I) as Hex_abs.
    { destruct Hex; auto. }
    apply ex_Ex_ival_is in Hex_abs as (vabs&His_abs).
    feed pose proof (is_Ex_ival_bind_bounded f (λ _, I) m vabs) as Hbind.
    { intros. exists vabs; split; eauto. reflexivity. }
    { eexists; eauto. }
    destruct Hbind as (v'&Hsum&Hv').
    cut (v = v'); intros; subst; eauto.
    etransitivity.
    { symmetry. eapply is_Ex_ival_unique; eauto. }
    eapply is_series_unique in Hsum.
    rewrite -Hsum. rewrite SeriesC_scal_l.
    rewrite (is_series_unique _ _ His). nra.
  Qed.

  Lemma is_Ex_ival_bind_alt {X Y} f (g: X → ival Y) (I: ival X) v:
    is_Ex_ival f (mbind g I) v →
    is_series (countable_sum (λ i : idx I, Ex_ival f (g (ind I i)) * val I i)) v.
  Proof.
    intros Hex.
    assert (Hex': ex_series
                   (countable_sum
                      (λ c : tag_countType (I:=idx I) (λ i : idx I, idx (g (ind I i))),
                             Rabs (ival_dist.prod_pmf g f I c)))).
    { destruct Hex as ((v'&His_abs)&His).
      exists v'. eapply is_seriesC_ext; last eassumption.
      intros => //=. rewrite /ival_dist.prod_pmf //=.
      rewrite ?Rabs_mult. nra.
    }
    feed pose proof (ival_dist.prod_pmf_sum_inv g f I) as His_bind; eauto.
    feed pose proof (ival_dist.ex_series_pmf_row g f I) as Hex_bind; eauto.
    { eapply ival_dist.prod_pmf_sum_inv_ds; eauto. }
    rewrite /Ex_ival.
    destruct Hex as (?&His).
    apply Series_correct'; auto.
    rewrite -(is_series_unique _ _ His).
    symmetry. eapply is_series_unique; eauto.
    eapply is_seriesC_ext; last eassumption.
    rewrite /ival_dist.prod_pmf //= => n. nra.
  Qed.

  Lemma Ex_ival_bind_alt {X Y} f (g: X → ival Y) (I: ival X):
    ex_Ex_ival f (mbind g I) →
    Ex_ival f (mbind g I) =
    Series (countable_sum (λ i : idx I, Ex_ival f (g (ind I i)) * val I i)).
  Proof.
    symmetry. apply is_series_unique.
    eapply is_Ex_ival_bind_alt.
    apply Ex_ival_correct.
    eauto.
  Qed.

  Lemma ex_Ex_ival_bind_inv {X Y} f (g: X → ival Y) (I: ival X):
    ex_Ex_ival f (mbind g I) →
    ∀ i, val I i > 0 → ex_Ex_ival f (g (ind I i)).
  Proof.
    intros Hex.
    apply ex_Ex_ival_is in Hex as (v&His).
    intros i Hgt.
    assert (Hex': ex_series
                   (countable_sum
                      (λ c : tag_countType (I:=idx I) (λ i : idx I, idx (g (ind I i))),
                             Rabs (ival_dist.prod_pmf g f I c)))).
    { destruct His as ((v'&His_abs)&His).
      exists v'. eapply is_seriesC_ext; last eassumption.
      intros => //=. rewrite /ival_dist.prod_pmf //=.
      rewrite ?Rabs_mult. nra.
    }
    feed pose proof (ival_dist.prod_pmf_sum_inv g f I) as His_bind; eauto.
    rewrite /ex_Ex_ival.
    feed pose proof (ival_dist.ex_series_pmf_abs_each_row g f I) as Hex_bind; eauto.
    { eapply ival_dist.prod_pmf_sum_inv_ds; eauto. }
    specialize (Hex_bind i).
    eapply (ex_seriesC_scal_r _ (/(val I i))) in Hex_bind.
    eapply ex_seriesC_ext; last eassumption. 
    intros n => //=. rewrite ?Rabs_mult.
    rewrite (Rabs_right (val I i)); last apply val_nonneg.
    field. nra.
  Qed.

  Lemma is_Ex_ival_iplus {X} f (I1 I2: ival X) v1 v2:
    is_Ex_ival f I1 v1 →
    is_Ex_ival f I2 v2 →
    is_Ex_ival f (iplus I1 I2) (v1 + v2).
  Proof.
    intros Hex1 Hex2.
    eapply (is_Ex_ival_proper f (x ← iplus (mret true) (mret false);
                                 if x then I1 else I2)).
    { setoid_rewrite ival_plus_bind.  apply iplus_proper; rewrite ival_left_id; reflexivity. }
    feed pose proof (ex_Ex_ival_to_Rabs f I1) as Habs. 
    { eapply is_Ex_ival_ex; eauto. }
    apply ex_Ex_ival_is in Habs as (v1'&?).
    
    feed pose proof (ex_Ex_ival_to_Rabs f I2) as Habs.
    { eapply is_Ex_ival_ex; eauto. }
    apply ex_Ex_ival_is in Habs as (v2'&?).

    edestruct (is_Ex_ival_bind_bounded f (λ x, if x then I1 else I2)
                                       (iplus (mret true) (mret false)) (Rmax v1' v2'))
              as (v&Hsum&His).
    { intros [|] ?.
      * exists v1' => //=. split; eauto.
        apply Rmax_l.
      * exists v2' => //=. split; eauto.
        apply Rmax_r.
    }
    { eexists. eapply SeriesF_is_seriesC. }
    cut (v = v1 + v2); intros; subst; eauto.
    eapply is_series_unique in Hsum.
    rewrite -Hsum.
    rewrite SeriesC_fin_big.
    rewrite /index_enum {1}[@Finite.enum]unlock //=.
    rewrite /sum_enum ?[@Finite.enum]unlock //= ?big_cons big_nil //=.
    apply is_Ex_ival_unique in Hex1.
    apply is_Ex_ival_unique in Hex2. subst. nra.
  Qed.

  Lemma Ex_ival_iplus {X} f (I1 I2: ival X) :
    ex_Ex_ival f I1 →
    ex_Ex_ival f I2 →
    Ex_ival f (iplus I1 I2) = (Ex_ival f I1) + (Ex_ival f I2).
  Proof.
    intros Hex1 Hex2.
    eapply is_Ex_ival_unique.
    apply is_Ex_ival_iplus; apply Ex_ival_correct; auto.
  Qed.

  Lemma is_Ex_ival_sum {X} f1 f2 (I: ival X) v1 v2:
    is_Ex_ival f1 I v1 →
    is_Ex_ival f2 I v2 →
    is_Ex_ival (λ x, f1 x + f2 x) I (v1 + v2).
  Proof.
    rewrite /is_Ex_ival/ex_Ex_ival.
    intros (Hex1&His1) (Hex2&His2).
    split.
    * eapply (ex_seriesC_le _ _ (λ i, (Rabs (f1 (ind I i) * val I i))
                                      + (Rabs (f2 (ind I i) * val I i)))).
      { intros n. split; first auto with *.
        rewrite ?Rabs_mult Rabs_val.
        rewrite -Rmult_plus_distr_r.
        apply Rmult_le_compat_r; first apply Rge_le, val_nonneg.
        apply Rabs_triang.
      }
      eapply ex_seriesC_plus; eauto.
    * setoid_rewrite Rmult_plus_distr_r.
      apply is_seriesC_plus; eauto.
  Qed.

  Lemma Ex_ival_sum {X} f1 f2 (I: ival X):
    ex_Ex_ival f1 I →
    ex_Ex_ival f2 I →
    Ex_ival (λ x, f1 x + f2 x) I = Ex_ival f1 I + Ex_ival f2 I.
  Proof.
    intros Hex1 Hex2.
    apply is_Ex_ival_unique.
    apply is_Ex_ival_sum; apply Ex_ival_correct; auto.
  Qed.

  Lemma Ex_ival_bind_le {X Y1 Y2} f1 f2 (I: ival X) (h1 : X → ival Y1) (h2: X → ival Y2):
    (∀ a, (∃ x, val I x > 0 ∧ ind I x = a) →
                Ex_ival f1 (h1 a) ≤ Ex_ival f2 (h2 a)) →
    ex_Ex_ival f1 (mbind h1 I) →
    ex_Ex_ival f2 (mbind h2 I) →
    Ex_ival f1 (mbind h1 I) ≤ Ex_ival f2 (mbind h2 I).
  Proof.
    intros Hslice Hex1 Hex2. rewrite ?Ex_ival_bind_alt //=. 
    eapply SeriesC_le'.
    - intros i.
      destruct (val_nonneg I i) as [Hgt|Heq0]; last first.
      { rewrite ?Heq0. nra. }
      apply Rmult_le_compat_r; first nra.
      eapply Hslice; eauto.
    -  apply ex_Ex_ival_is in Hex1 as (v&?).
       eexists. eapply is_Ex_ival_bind_alt; eauto.
    -  apply ex_Ex_ival_is in Hex2 as (v&?).
       eexists. eapply is_Ex_ival_bind_alt; eauto.
  Qed.

  Lemma is_Ex_ival_bind_le {X Y1 Y2} f1 f2 (I: ival X) (h1 : X → ival Y1) (h2: X → ival Y2) v1 v2:
    (∀ a, (∃ x, val I x > 0 ∧ ind I x = a) →
                Ex_ival f1 (h1 a) ≤ Ex_ival f2 (h2 a)) →
    is_Ex_ival f1 (mbind h1 I) v1 →
    is_Ex_ival f2 (mbind h2 I) v2 →
    v1 <= v2.
  Proof.
    intros ? His1 His2.
    rewrite -(is_Ex_ival_unique _ _ _ His1).
    rewrite -(is_Ex_ival_unique _ _ _ His2).
    apply Ex_ival_bind_le; eauto using is_Ex_ival_ex.
  Qed.

  (*
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
   *)

  Lemma is_Ex_ival_ivdplus {X} f p Hpf (I1 I2: ivdist X) :
    ex_Ex_ival f I1 →
    ex_Ex_ival f I2 →
    is_Ex_ival f (ivdplus p Hpf I1 I2 : ival X) (p * Ex_ival f I1 + (1 - p) * Ex_ival f I2).
  Proof.
    intros.
    eapply is_Ex_ival_iplus.
    - replace p with (Rabs p) at 2; last first.
      { rewrite Rabs_right; nra. }
      eapply is_Ex_ival_iscale; eauto.
    - replace (1 - p) with (Rabs (1 - p)) at 2; last first.
      { rewrite Rabs_right; nra. }
      eapply is_Ex_ival_iscale; eauto.
  Qed.

  Lemma ex_Ex_ival_ivdplus {X} f p Hpf (I1 I2: ivdist X) :
    ex_Ex_ival f I1 →
    ex_Ex_ival f I2 →
    ex_Ex_ival f (ivdplus p Hpf I1 I2 : ival X).
  Proof.
    intros. eapply is_Ex_ival_ex. eapply is_Ex_ival_ivdplus; eauto.
  Qed.
    
  Lemma Ex_ival_ivdplus {X} f p Hpf (I1 I2: ivdist X) :
    ex_Ex_ival f I1 →
    ex_Ex_ival f I2 →
    Ex_ival f (ivdplus p Hpf I1 I2 : ival X) = p * Ex_ival f I1 + (1 - p) * Ex_ival f I2.
  Proof.
    intros. apply is_Ex_ival_unique, is_Ex_ival_ivdplus; eauto.
  Qed.

  Lemma Ex_ival_bind_post {X Y} f (I: ival X) (h: X → ival Y):
    ex_Ex_ival f (x ← I; h x) →
    Ex_ival f (x ← I; h x) = Ex_ival (λ x, Ex_ival f (h x)) I.
  Proof.
    intros Hex.
    rewrite Ex_ival_bind_alt //=.
  Qed.

  Lemma ex_Ex_ival_bind_post {X Y} f (I: ival X) (h: X → ival Y):
    ex_Ex_ival f (x ← I; h x) →
    ex_Ex_ival (λ x, Ex_ival f (h x)) I.
  Proof.
    intros Hex.
    rewrite /ex_Ex_ival.
    assert (Hex': ex_series
                   (countable_sum
                      (λ c : tag_countType (I:=idx I) (λ i : idx I, idx (h (ind I i))),
                             Rabs (ival_dist.prod_pmf h f I c)))).
    { apply ex_Ex_ival_is in Hex  as (v&Hex).
      destruct Hex as ((v'&His_abs)&His).
      exists v'. eapply is_seriesC_ext; last eassumption.
      intros => //=. rewrite /ival_dist.prod_pmf //=.
      rewrite ?Rabs_mult. nra.
    }
    feed pose proof (ival_dist.prod_pmf_sum_inv h f I) as His_bind; eauto.
    feed pose proof (ival_dist.ex_series_pmf_abs_row h f I) as Hex_bind; eauto.
    { eapply ival_dist.prod_pmf_sum_inv_ds; eauto. }
    rewrite /Ex_ival.
    eapply ex_seriesC_ext; last eassumption.
    intros n => //=. rewrite Rabs_mult; f_equal. rewrite Rabs_right //=.
    apply val_nonneg.
  Qed.
  
  Lemma ex_Ex_ival_bind_post_inv {X Y} f (I: ival X) (h: X → ival Y):
    (∀ x, f x >= 0) →
    (∀ x, val I x > 0 → ex_Ex_ival f (h (ind I x))) →
    ex_Ex_ival (λ x, Ex_ival f (h x)) I →
    ex_Ex_ival f (x ← I; h x).
  Proof.
    intros Hpos Hall Hex.
    rewrite /ex_Ex_ival.
    apply ex_Ex_ival_is in Hex as (v&His).
    feed pose proof (ival_dist.prod_pmf_sum_by_row h f I) as His_bind; eauto.
    { rewrite /is_Ex_ival in His. destruct His as (Hex&His).
      eexists; eauto. }
    rewrite /ival_dist.prod_pmf in His_bind.
    eapply ex_seriesC_ext; last first.
    { eexists; eauto. }
    intros n => //=. rewrite ?Rabs_mult ?Rabs_val Rabs_right; eauto; nra.
  Qed.

  Definition bounded_fun {A: Type} (f: A → R) : Prop :=
    ∃ c, ∀ x, Rabs (f x) <= c.

  Definition bounded_fun_on {A: Type} (f: A → R) P: Prop :=
    ∃ c, ∀ x, P x → Rabs (f x) <= c.

  Global Instance bounded_fun_proper {X: Type}:
    Proper (pointwise_relation X eq ==> iff) bounded_fun.
  Proof.
    intros ?? Heq; split.
    * intros (c&?). exists c => z. rewrite -Heq; eauto.
    * intros (c&?). exists c => z. rewrite Heq; eauto.
  Qed.

  Global Instance bounded_fun_on_proper {X: Type}:
    Proper (pointwise_relation X eq ==> pointwise_relation _ iff ==> iff) bounded_fun_on.
  Proof.
    intros ?? Heq ?? Heq'; split.
    * intros (c&?). exists c => z. rewrite -Heq -Heq'; eauto.
    * intros (c&?). exists c => z. rewrite Heq Heq'; eauto.
  Qed.

  Lemma bounded_fun_on_anti {A: Type} (f: A → R) P P' :
    bounded_fun_on f P → (∀ a, P' a → P a) → bounded_fun_on f P'.
  Proof.
    intros (c&Hbf) Himpl.
    exists c. intros. intuition.
  Qed.

  Lemma bounded_isupp_fun_bind_post {X Y} f (I: ival X) (h: X → ival Y):
    bounded_fun_on f (λ y, In_isupport y (z ← I; h z)) →
    ∀ x, In_isupport x I → bounded_fun_on f (λ y, In_isupport y (h x)).
  Proof.
    intros Hbf x Hin.
    eapply bounded_fun_on_anti; try eassumption.
    intros a' Hin'.
    destruct Hin as (ix&Heqix&?).
    destruct Hin' as (iy&Heqiy&?).
    subst. exists (existT ix iy).
    rewrite //=. split; eauto. nra.
  Qed.

  Lemma ex_Ex_ival_fmap {X Y} (g: Y → R) f (I: ival X):
    ex_Ex_ival (λ x, g (f x)) I ↔
    ex_Ex_ival g (x ← I; mret (f x)).
  Proof.
    split.
    - rewrite /ex_Ex_ival //=. 
      intros Hex. destruct Hex as (v&His).
      setoid_rewrite Rmult_1_r.
      unshelve (edestruct (@rearrange.countable_series_rearrange_covering_match_fun) as (His1&His2));
        try eapply His; last (eexists; eapply His1).
      { rewrite //=. intros ((x&[])&?). exists x. eauto. }
      { intros ((?&[])&?) ((?&[])&?) => //=.
        inversion 1; subst; eauto. apply sval_inj_pi => //=. }
      { intros (x&Hpf). exists (exist _ (existT x tt) Hpf) => //=. }
      { intros ((?&[])&?) => //=. }
    - intros Hex.
      apply ex_Ex_ival_bind_post in Hex.
      setoid_rewrite Ex_ival_mret in Hex. eauto.
  Qed.
               
End Ex_ival_properties.

Definition is_Ex_ivd {X} (f: X → R) (I: ivdist X) v := is_Ex_ival f I v.
Definition ex_Ex_ivd {X} (f: X → R) (I: ivdist X) := ex_Ex_ival f I.
Definition Ex_ivd {X} (f: X → R) (I: ivdist X) : R := Ex_ival f I.

Section Ex_ivd_properties.

  Lemma is_Ex_ivd_ivdplus {X} f p Hpf (I1 I2: ivdist X) :
    ex_Ex_ivd f I1 →
    ex_Ex_ivd f I2 →
    is_Ex_ivd f (ivdplus p Hpf I1 I2) (p * Ex_ival f I1 + (1 - p) * Ex_ival f I2).
  Proof. intros. by apply is_Ex_ival_ivdplus. Qed.

  Lemma Ex_ivd_plus {X} f p Hpf (I1 I2: ivdist X) :
    ex_Ex_ivd f I1 →
    ex_Ex_ivd f I2 →
    Ex_ivd f (ivdplus p Hpf I1 I2) = p * Ex_ivd f I1 + (1 - p) * Ex_ivd f I2.
  Proof. apply Ex_ival_ivdplus. Qed.

  Lemma Ex_ivd_rvar (I: ivdist R) :
    ex_Ex_ival id I →
    Ex_ivd id I = Ex (rvar_of_ivdist I).
  Proof.
    rewrite /Ex_ivd/Ex_ival/ex_Ex_ival => Hex.
    rewrite Ex_pt//=.
    {
      apply ex_Ex_by_pt => //=.
      eapply ex_series_ext; last eassumption.
      intros n. eapply countable_sum_ext => ?. setoid_rewrite Rabs_mult.
      f_equal. rewrite Rabs_right //=; apply val_nonneg.
    }
  Qed.

  Lemma is_Ex_ivd_bind_irrel {X Y} f (I: ivdist X) (m: ivdist Y) v:
    is_Ex_ivd f I v →
    is_Ex_ivd f (mbind (λ x, I) m) v.
  Proof.
    apply is_Ex_ival_bind_irrel, val_sum1.
  Qed.

  Lemma is_Ex_ivd_plus_const {X} f (I: ivdist X) k v:
    is_Ex_ivd f I v →
    is_Ex_ivd (λ x, f x + k) I (v + k).
  Proof.
    rewrite /is_Ex_ivd/is_Ex_ival/ex_Ex_ival//=.
    intros (Hex&His); split.
    * setoid_rewrite Rabs_mult.
      apply: (ex_series_le _ (countable_sum (λ i, Rabs (f (ind I i)) * val I i
                                                   + Rabs k * val I i))); last first.
      { apply: ex_seriesC_plus.
        * eapply ex_series_ext; last eassumption.
          intros n. eapply countable_sum_ext => ?. rewrite Rabs_mult; f_equal.
          rewrite Rabs_right; eauto. apply val_nonneg.
        * apply: ex_seriesC_scal_l. exists 1; apply val_sum1.
      }
      rewrite /norm//=/abs//=.
      intros. rewrite -countable_sum_Rabs.
      apply countable_sum_le => m.
      rewrite ?Rabs_mult !Rabs_Rabsolu.
      rewrite (Rabs_right (val I m)); last apply val_nonneg.
      specialize (val_nonneg I m) => Hval.
      repeat apply Rabs_case; intros; nra.
    * setoid_rewrite Rmult_plus_distr_r.
      apply is_seriesC_plus; eauto.
      replace k with (k * 1) at 1; last nra.
      apply is_seriesC_scal_l. apply val_sum1.
  Qed.

  Lemma Ex_ivd_plus_const {X} f (I: ivdist X) k:
    ex_Ex_ivd f I →
    Ex_ivd (λ x, f x + k) I = Ex_ivd f I + k.
  Proof.
    intros Hex. apply is_Ex_ival_unique, is_Ex_ivd_plus_const, Ex_ival_correct; auto.
  Qed.

  Lemma ex_Ex_ivd_plus_const {X} f (I: ivdist X) k:
    ex_Ex_ivd f I →
    ex_Ex_ivd (λ x, f x + k) I.
  Proof.
    intros Hex. apply ex_Ex_ival_is in Hex as (v&His).
    eapply is_Ex_ival_ex. eapply is_Ex_ivd_plus_const; eauto.
  Qed.

  Lemma is_Ex_ivd_plus_const_r_inv {X} f (I: ivdist X) k v:
    is_Ex_ivd (λ x, f x + k) I v →
    is_Ex_ivd f I (v - k).
  Proof.
    intros His. apply (is_Ex_ivd_plus_const _ _ (-k)) in His.
    rewrite /Rminus.
    eapply is_Ex_ival_proper'; last eassumption.
    - intros x => //=; field.
    - reflexivity.
  Qed.

  Lemma is_Ex_ivd_scale_const {X} f (I: ivdist X) k v:
    is_Ex_ivd f I v →
    is_Ex_ivd (λ x, k * (f x)) I (k * v). 
  Proof.
    rewrite /is_Ex_ivd/is_Ex_ival/ex_Ex_ival//=. 
    intros (Hex&His).
    split.
    - setoid_rewrite Rmult_assoc.
      setoid_rewrite Rabs_mult. 
      apply ex_seriesC_scal_l; auto.
    - setoid_rewrite Rmult_assoc.
      apply: is_seriesC_scal_l; auto.
  Qed.

  Lemma ex_Ex_ivd_scale_const {X} f (I: ivdist X) k:
    ex_Ex_ivd f I →
    ex_Ex_ivd (λ x, k * (f x)) I.
  Proof.
    intros Hex. apply ex_Ex_ival_is in Hex as (v&His).
    eapply is_Ex_ival_ex, is_Ex_ivd_scale_const; eauto.
  Qed.

  Lemma Ex_ivd_scale_const {X} f (I: ivdist X) k:
    Ex_ivd (λ x, k * (f x)) I = k * (Ex_ivd f I).
  Proof.
    rewrite /Ex_ivd/Ex_ival//=.
    setoid_rewrite Rmult_assoc.
    rewrite SeriesC_scal_l //.
  Qed.

  Lemma Ex_ivd_const {X} (I: ivdist X) k:
    Ex_ivd (λ x, k) I = k.
  Proof.
    rewrite /Ex_ivd/Ex_ival//=.
    rewrite SeriesC_scal_l.
    rewrite val_sum1_Series. nra.
  Qed.

  Lemma is_Ex_ivd_const {X} (I: ivdist X) k:
    is_Ex_ivd (λ x, k) I k.
  Proof.
    rewrite -{2}(Ex_ivd_const I k).
    apply Ex_ival_correct.
    rewrite /ex_Ex_ival. eapply (ex_seriesC_ext _ (λ i, Rabs k * val I i)).
    { intros; rewrite Rabs_mult; f_equal; rewrite Rabs_right //; apply val_nonneg. }
    apply ex_seriesC_scal_l. exists 1; apply val_sum1.
  Qed.

  Lemma ex_Ex_ivd_const {X} (I: ivdist X) k:
    ex_Ex_ivd (λ x, k) I.
  Proof.
    eapply is_Ex_ival_ex, is_Ex_ivd_const.
  Qed.

  Lemma ex_Ex_ivd_bounded_fun {X} f (I: ivdist X):
    bounded_fun f →
    ex_Ex_ival f I.
  Proof.
    intros (c&HRabs). 
    rewrite /ex_Ex_ival. eapply (ex_seriesC_le _ _ (λ i, Rabs c * val I i)).
    * intros n. split; first apply Rabs_pos.
      rewrite Rabs_mult Rabs_val. apply Rmult_le_compat_r.
      ** apply Rge_le, val_nonneg. 
      ** transitivity c; eauto. apply Rabs_case; nra.
    * specialize (ex_Ex_ivd_const I c). rewrite /ex_Ex_ivd/ex_Ex_ival//=.
      setoid_rewrite Rabs_mult. setoid_rewrite Rabs_val.
      done.
  Qed.

  Lemma ex_Ex_ivd_bounded_supp_fun {X} f (I: ivdist X):
    bounded_fun_on f (λ i, In_isupport i I) →
    ex_Ex_ival f I.
  Proof.
    intros (c&HRabs). 
    rewrite /ex_Ex_ival. eapply (ex_seriesC_le _ _ (λ i, Rabs c * val I i)).
    * intros n. split; first apply Rabs_pos.
      rewrite Rabs_mult Rabs_val.
      destruct (val_nonneg I n) as [|Heq]; last first.
      { rewrite ?Heq. nra. }
      apply Rmult_le_compat_r.
      ** apply Rge_le, val_nonneg. 
      ** transitivity c; eauto.
         *** eapply HRabs. eexists; eauto.
         *** apply Rabs_case; nra.
    * specialize (ex_Ex_ivd_const I c). rewrite /ex_Ex_ivd/ex_Ex_ival//=.
      setoid_rewrite Rabs_mult. setoid_rewrite Rabs_val.
      done.
  Qed.

  Lemma Ex_ivd_bounded_below {X} f (I: ivdist X) c: 
    (∀ x, c <= f x) →
    ex_Ex_ival f I →
    c <= Ex_ival f I.
  Proof.
    intros. rewrite /Ex_ival. 
    rewrite -(Ex_ivd_const I c).
    rewrite /Ex_ivd/Ex_ival.
    apply SeriesC_le'.
    * intros; apply Rmult_le_compat_r.
      ** apply Rge_le, val_nonneg. 
      ** eauto.
    * specialize (ex_Ex_ivd_const I c). rewrite /ex_Ex_ivd/ex_Ex_ival//=.
      apply ex_seriesC_Rabs.
    * eapply ex_seriesC_Rabs; eauto.
  Qed.

  Lemma Ex_ivd_bounded_above {X} f (I: ivdist X) c: 
    (∀ x, f x <= c) →
    ex_Ex_ival f I →
    Ex_ival f I <= c.
  Proof.
    intros. rewrite /Ex_ival. 
    rewrite -(Ex_ivd_const I c).
    rewrite /Ex_ivd/Ex_ival.
    apply SeriesC_le'.
    * intros; apply Rmult_le_compat_r.
      ** apply Rge_le, val_nonneg. 
      ** eauto.
    * eapply ex_seriesC_Rabs; eauto.
    * specialize (ex_Ex_ivd_const I c). rewrite /ex_Ex_ivd/ex_Ex_ival//=.
      apply ex_seriesC_Rabs.
  Qed.

  Lemma Ex_ivd_bounded_fun {X} f (I: ivdist X) c: 
    (∀ x, Rabs (f x) <= c) →
    Rabs (Ex_ival f I) <= c.
  Proof.
    intros Habs. apply Rabs_case.
    - intros.
      apply Ex_ivd_bounded_above; eauto.
      { intros x. transitivity (Rabs (f x)); eauto. apply Rabs_case; nra. }
      apply ex_Ex_ivd_bounded_fun; eexists; eauto.
    - intros. 
      apply Ropp_le_cancel. rewrite Ropp_involutive.
      apply Ex_ivd_bounded_below; eauto.
      { intros x. generalize (Habs x). apply Rabs_case; nra. }
      apply ex_Ex_ivd_bounded_fun; eexists; eauto.
  Qed.

  Lemma Ex_ivd_bounded_supp_below {X} f (I: ivdist X) c: 
    (∀ x, In_isupport x I → c <= f x) →
    ex_Ex_ival f I →
    c <= Ex_ival f I.
  Proof.
    intros Hle Hex. rewrite /Ex_ival. 
    rewrite -(Ex_ivd_const I c).
    rewrite /Ex_ivd/Ex_ival.
    apply SeriesC_le'.
    * intros.
      destruct (val_nonneg I n) as [|Heq]; last first.
      { rewrite ?Heq. nra. }
      apply Rmult_le_compat_r.
      ** apply Rge_le, val_nonneg. 
      ** eapply Hle; eauto. eexists; eauto.
    * specialize (ex_Ex_ivd_const I c). rewrite /ex_Ex_ivd/ex_Ex_ival//=.
      apply ex_seriesC_Rabs.
    * eapply ex_seriesC_Rabs; eauto.
  Qed.

  Lemma Ex_ivd_bounded_supp_above {X} f (I: ivdist X) c: 
    (∀ x, In_isupport x I → f x <= c) →
    ex_Ex_ival f I →
    Ex_ival f I <= c.
  Proof.
    intros Hle Hex. rewrite /Ex_ival. 
    rewrite -(Ex_ivd_const I c).
    rewrite /Ex_ivd/Ex_ival.
    apply SeriesC_le'.
    * intros.
      destruct (val_nonneg I n) as [|Heq]; last first.
      { rewrite ?Heq. nra. }
      apply Rmult_le_compat_r.
      ** apply Rge_le, val_nonneg. 
      ** eapply Hle; eauto. eexists; eauto.
    * eapply ex_seriesC_Rabs; eauto.
    * specialize (ex_Ex_ivd_const I c). rewrite /ex_Ex_ivd/ex_Ex_ival//=.
      apply ex_seriesC_Rabs.
  Qed.

  Lemma Ex_ivd_bounded_supp_fun {X} f (I: ivdist X) c: 
    (∀ x, In_isupport x I → Rabs (f x) <= c) →
    Rabs (Ex_ival f I) <= c.
  Proof.
    intros Habs. apply Rabs_case.
    - intros.
      apply Ex_ivd_bounded_supp_above; eauto.
      { intros x. transitivity (Rabs (f x)); eauto. apply Rabs_case; nra. }
      apply ex_Ex_ivd_bounded_supp_fun; eexists; eauto.
    - intros. 
      apply Ropp_le_cancel. rewrite Ropp_involutive.
      apply Ex_ivd_bounded_supp_below; eauto.
      { intros x Hin. generalize (Habs x Hin). apply Rabs_case; intros; eauto; try nra. }
      apply ex_Ex_ivd_bounded_supp_fun; eexists; eauto.
  Qed.

End Ex_ivd_properties.
  

Definition Ex_pival {X} (f : X → R) (Is: pival X) : R → Prop :=
  λ r, ∃ I, Is I ∧ is_Ex_ival f I r.

Definition Ex_pidist {X} (f : X → R) (Is: pidist X) :=
  Ex_pival f Is.

Definition Ex_min {X} (f: X → R) (Is: pidist X): Rbar := Glb_Rbar (Ex_pidist f Is).
Definition Ex_max {X} (f: X → R) (Is: pidist X): Rbar := Lub_Rbar (Ex_pidist f Is).
Definition ex_Ex_extrema {X} (f: X → R) (Is: pidist X) : Prop :=
  ∀ I, In I Is → ex_Ex_ival f I.

Section Ex_extrema_properties.

  Context {X: Type}.
  Implicit Types f: X → R.

Lemma ex_Ex_extrema_fun_pres f g Is :
  ex_Ex_extrema f Is →
  (∀ I, ex_Ex_ival f I → ex_Ex_ival g I) →
  ex_Ex_extrema g Is.
Proof.
  intros Hex Himpl.
  intros I Hin; eauto.
Qed.

Lemma ex_Ex_extrema_plus_const_l f Is c:
  ex_Ex_extrema f Is →
  ex_Ex_extrema (λ x, c + f x) Is.
Proof.
  intros Hex I Hin.
  setoid_rewrite Rplus_comm.
  apply (ex_Ex_ivd_plus_const f {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |}).
  eapply Hex; eauto.
Qed.

Lemma ex_Ex_extrema_scale_const_l f Is c:
  ex_Ex_extrema f Is →
  ex_Ex_extrema (λ x, c * f x) Is.
Proof.
  intros Hex I Hin.
  apply (ex_Ex_ivd_scale_const f {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |}).
  eapply Hex; eauto.
Qed.

Lemma ex_Ex_extrema_negate f Is :
  ex_Ex_extrema f Is →
  ex_Ex_extrema (λ x, - f x) Is.
Proof.
  intros. eapply ex_Ex_extrema_fun_pres; try eassumption.
  intros. by apply ex_Ex_ival_negate.
Qed.

Lemma ex_Ex_extrema_bounded_fun f Is:
  bounded_fun f →
  ex_Ex_extrema f Is.
Proof.
  intros Hb I Hin. apply (ex_Ex_ivd_bounded_fun f {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |}).
  eauto.
Qed.

Lemma ex_Ex_extrema_bounded_supp_fun f (Is: pidist X):
  bounded_fun_on f (λ x, In_psupport x Is) →
  ex_Ex_extrema f Is.
Proof.
  intros Hb I Hin.
  apply (ex_Ex_ivd_bounded_supp_fun f {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |}).
  eapply bounded_fun_on_anti; eauto.
  intros a Hin'.
  eapply In_psupport_alt. eexists; eauto.
Qed.

Lemma ex_Ex_extrema_proper' {Y} (f1 f2: Y → R) Is1 Is2 :
  (∀ x, f1 x = f2 x) →
  eq_pidist Is1 Is2 →
  ex_Ex_extrema f1 Is1 →
  ex_Ex_extrema f2 Is2.
Proof.
  intros Heq_fun Heq Hex.
  intros I Hin; eauto.
  destruct Heq as (Hle1&Hle2).
  destruct (Hle2 _ Hin) as (I'&Hin'&Heq).
  eapply ex_Ex_ival_proper'; last first.
  { eapply Hex; eauto. }
  * by symmetry. 
  * eauto.
Qed.

Lemma ex_Ex_extrema_proper_supp {Y} (f1 f2: Y → R) (Is: pidist Y) :
  (∀ x, In_psupport x Is → f1 x = f2 x) →
  ex_Ex_extrema f1 Is →
  ex_Ex_extrema f2 Is.
Proof.
  intros Heq_fun Hex.
  intros I Hin; eauto.
  generalize (Hex _ Hin) => Hex'.
  apply ex_Ex_ival_is in Hex' as (v&His).
  eapply is_Ex_ival_ex. 
  eapply is_Ex_ival_proper_fun_support; last first.
  { eapply His; eauto. }
  intros. eapply Heq_fun.
  apply In_psupport_alt. eexists; split; eauto.
  eexists; eauto.
Qed.

Lemma bounded_psupp_fun_bind_inv {Y} (f: Y → R) (Is: pidist X) (h: X → pidist Y):
  bounded_fun_on f (λ y, In_psupport y (pidist_bind _ _ h Is)) →
  ∀ x, In_psupport x Is → bounded_fun_on f (λ y, In_psupport y (h x)).
Proof.
  intros Hbf x Hin.
  eapply bounded_fun_on_anti; try eassumption.
  intros a' Hin'.
  eapply In_psupport_bind; eauto.
Qed.

Lemma bounded_psupp_fun_bind_inv_strong {Y} (f: Y → R) (Is: pidist X) (h: X → pidist Y):
  bounded_fun_on f (λ y, In_psupport y (pidist_bind _ _ h Is)) →
  ∃ c, ∀ x, In_psupport x Is →
            ∀ y, In_psupport y (h x) → Rabs (f y) <= c.
Proof.
  intros (c&Hb).
  exists c. intros x Hin y Hin'.
  eapply Hb. eapply In_psupport_bind; eauto.
Qed.

Lemma In_psupport_bind_inv {Y} (Is: pidist X) (h: X → pidist Y) y:
  In_psupport y (pidist_bind X Y h Is) →
  ∃ x, In_psupport x Is ∧ In_psupport y (h x).
Proof.
  intros Hin.
  destruct Hin as (I&i&Hin&?).
  apply pival_mbind_in_inv_idxOf in Hin as (Ix&?&?&?&Heq).
  symmetry in Heq.
  destruct Heq as (w2&w1&?&?&Hind&Hval).
  assert (Hgti: Rgt_dec (val I i) 0).
  { abstract (intuition; destruct Rgt_dec; eauto).  }
  unshelve eexists.
  { refine (ind Ix _).
    { refine (projT1 (sval _)).
      { eapply w2. exists i. apply Hgti. }
    }
  }
  split_and!.
  - exists Ix. eexists; split_and!; eauto.
    destruct (w2 _) as (x1&Hpf) => //=.
    rewrite //= in Hpf.
    clear Hgti.
    destruct Rgt_dec as [Hgt|] => //=. destruct (val_nonneg Ix (projT1 x1)) as [|Heq0]; eauto.
    { exfalso. clear -Heq0 Hgt. rewrite Heq0 //= in Hgt. nra. }
  - unshelve (eexists).
    { refine (x (projT1 (sval (w2 (exist _ i Hgti))))).  }
    unshelve (eexists).
    { refine ((projT2 (sval (w2 (exist _ i Hgti))))).  }
    split_and!; eauto.
    * eapply H1.  destruct (w2 _). rewrite //= in i0 *.
      clear Hgti.
      destruct Rgt_dec as [Hgt|] => //=. destruct (val_nonneg Ix (projT1 x0)) as [|Heq0]; eauto.
      { exfalso. clear -Heq0 Hgt. rewrite Heq0 //= in Hgt. nra. }
    * specialize (Hind (i ↾ Hgti)). rewrite //= in Hind. rewrite Hind. intuition.
    * specialize (Hval (i ↾ Hgti)). rewrite //= in Hval.
      edestruct @val_nonneg as [Hgt|Hngt]; first eapply Hgt.
      rewrite Hngt in Hval. nra.
Qed.

Lemma bounded_psupp_fun_bind {Y} (f: Y → R) (Is: pidist X) (h: X → pidist Y):
  (∃ c, ∀ x, In_psupport x Is → ∀ y, In_psupport y (h x) → Rabs (f y) <= c) →
  bounded_fun_on f (λ y, In_psupport y (pidist_bind _ _ h Is)).
Proof.
  intros Hbf. destruct Hbf as (c&Hb).
  exists c. intros x Hin.
  eapply In_psupport_bind_inv in Hin as (x'&Hin1'&Hin2').
  eapply Hb; eauto.
Qed.

Global Instance ex_Ex_extrema_proper_instance:
  ∀ (X : Type), Proper ((pointwise_relation _ eq) ==> @eq_pidist X ==> iff) (ex_Ex_extrema).
Proof.
  intros Y f1 f2 ? I1 I2 Heq.
  split; eapply ex_Ex_extrema_proper'; eauto.
    by symmetry.
Qed.

Lemma ex_Ex_extrema_const {Y} (Is: pidist Y) k :
  ex_Ex_extrema (λ _, k) Is.
Proof.
  intros I Hin. apply (ex_Ex_ivd_const {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |}).
Qed.

Lemma ex_Ex_extrema_mret f (x: X):
  ex_Ex_extrema f (mret x).
Proof.
  intros I Hin. rewrite /In//= in Hin. inversion Hin.
  subst => //=. eapply ex_Ex_ival_proper; last eapply ex_Ex_ival_mret.
  rewrite /mret/ival_ret. apply eq_ival_quasi_refl.
Qed.

Lemma Ex_pidist_spec1 f (I: ival X) (Is: pidist X) (Hin: In I Is):
  ex_Ex_ival f I →
  In (Ex_ival f I) (Ex_pidist f Is).
Proof. intros Hex. exists I; split; auto. by apply Ex_ival_correct. Qed.

Lemma Ex_pidist_spec2 r f (Is: pidist X):
      In r (Ex_pidist f Is) →
      ∃ I (Hin: In I Is), is_Ex_ival f I r.
Proof. intros (I&?&?). exists I; eauto. Qed.

Lemma Ex_min_spec1 f Is:
  ∀ r, In r (Ex_pidist f Is) → Rbar_le (Ex_min f Is) r.
Proof. intros; destruct (Glb_Rbar_correct (Ex_pidist f Is)); eauto. Qed.

Lemma Ex_min_spec1' f I (Is: pidist X) (Hpf: In I Is) :
  ex_Ex_ival f I →
  Rbar_le (Ex_min f Is) (Ex_ival f I).
Proof. intros; by apply Ex_min_spec1, Ex_pidist_spec1. Qed.

Lemma Ex_min_spec2 f Is r:
  (∀ r', In r' (Ex_pidist f Is) → Rbar_le r r') → Rbar_le r (Ex_min f Is).
Proof.
  intros; destruct (Glb_Rbar_correct (Ex_pidist f Is)) as (?&Hglb).
  eapply Hglb; intros ? Hin; apply H; eauto.
Qed.

Lemma Ex_min_spec_witness f (Is: pidist X) (eps: R) (Hgt: 0 < eps):
  is_finite (Ex_min f Is) →
  ∃ I, In I Is ∧ ex_Ex_ival f I ∧ Ex_min f Is <= Ex_ival f I <= Ex_min f Is + eps.
Proof.
  intros Hfin.
  apply Classical_Pred_Type.not_all_not_ex.
  intros Hall.
  rewrite /Ex_min in Hfin Hall.
  destruct (Glb_Rbar_correct (Ex_pidist f Is)) as (Hlb&Hglb).
  feed pose proof (Hglb (Rbar_plus (Ex_min f Is) eps)) as Hglb_alt.
  - intros r (I&Hin&His). 
    apply Rbar_not_lt_le.
    intros Hlt. eapply Hall; split_and!; eauto.
    * eapply is_Ex_ival_ex; eauto.
    * cut (Rbar_le (Glb_Rbar (Ex_pidist f Is)) (Ex_ival f I)).
      { rewrite -Hfin //=. }
      apply Ex_min_spec1. apply Ex_pidist_spec1; eauto.
      eapply is_Ex_ival_ex; eauto.
    * rewrite /Ex_min -Hfin //= in Hlt. 
      rewrite (is_Ex_ival_unique _ _ _ His). nra.
  - rewrite /Ex_min -Hfin //= in Hglb_alt.
    nra.
Qed.


(*
Lemma Ex_min_spec_witness f (Is: pidist X):
  ∃ I, In I Is ∧ Ex_ival f I = Ex_min f Is.
Proof.
  destruct Is as [[Is Hne] Hsum].
  destruct Is as [| I Is].
  - rewrite //=. destruct Hne as (?&[]).
  - rewrite /Ex_min/Ex_pidist//=. 
    match goal with
    | [ |- context [ fold_left Rmin ?l ?x ] ] =>
      edestruct (fold_left_Rmin_witness1 l x) as [(r&Hin&<-)|(Hmin&Heq)]
    end.
    * apply in_map_iff in Hin as (I'&?&?).
      exists I'; split; auto.
    * exists I; split; auto.
Qed.

Lemma Ex_pidist_union f Is1 Is2:
  Ex_pidist f (pidist_union Is1 Is2) = Ex_pidist f Is1 ++ Ex_pidist f Is2.
Proof. by rewrite /Ex_pidist/Ex_pival map_app. Qed.
*)

Lemma Ex_min_pidist_union f Is1 Is2:
  Ex_min f (pidist_union Is1 Is2) = Rbar_min (Ex_min f Is1) (Ex_min f Is2).
Proof.
  apply Rbar_le_antisym.
  - apply Rbar_min_case_strong.
    * intros Hle1. apply Ex_min_spec2. intros ? (I&?&?). apply Ex_min_spec1.
      rewrite /Ex_pidist//=/Ex_pival//=.
      exists I; split; auto.
    * intros Hle1. apply Ex_min_spec2. intros ? (I&?&?). apply Ex_min_spec1.
      rewrite /Ex_pidist//=/Ex_pival//=.
      exists I; split; auto.
  - apply Ex_min_spec2. intros ? (I&Hin&?).
    destruct Hin.
    * etransitivity; first apply Rbar_min_l. apply Ex_min_spec1; exists I; eauto.
    * etransitivity; first apply Rbar_min_r. apply Ex_min_spec1; exists I; eauto.
Qed.

Lemma Ex_min_pidist_join {A: Type} (a: A) f (Iss: A → pidist X):
  (∀ a, is_finite (Ex_min f (Iss a))) →
  Ex_min f (pidist_join a Iss) =
  Glb_Rbar (λ r, ∃ a, Ex_min f (Iss a) = r).
Proof.
  intros Hfin.
  apply is_glb_Rbar_unique.
  split.
  - intros r (I&Hin&His).
    destruct Hin as (a'&Hin).
    destruct (Glb_Rbar_correct (λ r, ∃ a, Ex_min f (Iss a) = r)) as (Hlb&Hglb).
    etransitivity.
    { apply Hlb. exists a'. rewrite -Hfin. reflexivity. }
    rewrite Hfin. apply Ex_min_spec1. eexists; eauto.
  - intros r Hlb.
    destruct (Glb_Rbar_correct (λ r, ∃ a, Ex_min f (Iss a) = r)) as (Hlb'&Hglb).
    apply Hglb.
    intros r' (a'&<-). 
    apply Ex_min_spec2.
    intros r'' (I'&Hin'&Heq).
    eapply Hlb. exists I'; split; auto.
    eexists; eauto.
Qed.

Lemma Ex_min_pidist_union_l f Is1 Is2:
  Rbar_le (Ex_min f (pidist_union Is1 Is2)) (Ex_min f Is1).
Proof.
  rewrite Ex_min_pidist_union. apply Rbar_min_l.
Qed.

Lemma Ex_min_pidist_union_r f Is1 Is2:
  Rbar_le (Ex_min f (pidist_union Is1 Is2)) (Ex_min f Is2).
Proof.
  rewrite Ex_min_pidist_union. apply Rbar_min_r.
Qed.

Lemma Ex_min_eq_pidist_aux f Is1 Is2:
  eq_pidist Is1 Is2 →
  Rbar_le (Ex_min f Is1) (Ex_min f Is2).
Proof.
  intros Heq.
  apply Ex_min_spec2.
  intros r' Hin. apply Ex_min_spec1.
  apply Ex_pidist_spec2 in Hin as (I2&Hin2&Heq').
  destruct Heq as (Heq1&Heq2). destruct (Heq2 _ Hin2) as (I1&Hequiv&Hin1).
  eexists; split; eauto.
  setoid_rewrite <-Hequiv.
  eauto.
Qed.

Lemma Ex_min_le_ext f1 f2 Is:
  (∀ x, f1 x ≤ f2 x) →
  ex_Ex_extrema f1 Is →
  Rbar_le (Ex_min f1 Is) (Ex_min f2 Is).
Proof.
  intros Hf12 Hex.
  apply Ex_min_spec2. intros r' (I&Hin&His).
  feed pose proof (Hex I Hin) as Hex.
  apply ex_Ex_ival_is in Hex as (v&His').
  transitivity v.
  - eapply Ex_min_spec1. exists I; split; eauto.
  - rewrite //=. eapply is_Ex_ival_mono; eauto.
Qed.

Lemma Ex_min_le_supp_ext f1 f2 Is:
  (∀ x, In_psupport x (Is: pidist X) → f1 x ≤ f2 x) →
  ex_Ex_extrema f1 Is →
  Rbar_le (Ex_min f1 Is) (Ex_min f2 Is).
Proof.
  intros Hf12 Hex.
  apply Ex_min_spec2. intros r' (I&Hin&His).
  feed pose proof (Hex I Hin) as Hex.
  apply ex_Ex_ival_is in Hex as (v&His').
  transitivity v.
  - eapply Ex_min_spec1. exists I; split; eauto.
  - rewrite //=. eapply is_Ex_ival_mono_support; eauto.
    { intros x Hgt.  eapply Hf12. eexists; eauto. }
Qed.

Lemma Ex_min_eq_ext f1 f2 Is:
  (∀ x, f1 x = f2 x) → Ex_min f1 Is = Ex_min f2 Is.
Proof.
  intros Hext.
  apply Rbar_le_antisym.
  - apply Ex_min_spec2. intros r' (I&Hin&His).
    eapply Ex_min_spec1. exists I; split; eauto.
    eapply is_Ex_ival_proper'; last eassumption; eauto.
  - apply Ex_min_spec2. intros r' (I&Hin&His).
    eapply Ex_min_spec1. exists I; split; eauto.
    eapply is_Ex_ival_proper'; last eassumption; eauto.
Qed.

Lemma Ex_min_eq_ext_supp f1 f2 (Is: pidist X):
  (∀ x, In_psupport x Is → f1 x = f2 x) → Ex_min f1 Is = Ex_min f2 Is.
Proof.
  intros Hext.
  apply Rbar_le_antisym.
  - apply Ex_min_spec2. intros r' (I&Hin&His).
    eapply Ex_min_spec1. exists I; split; eauto.
    eapply is_Ex_ival_proper_fun_support; last eassumption; eauto.
    { intros; symmetry. eapply Hext.
      eapply In_psupport_alt; eexists; split; eauto. eexists; eauto. }
  - apply Ex_min_spec2. intros r' (I&Hin&His).
    eapply Ex_min_spec1. exists I; split; eauto.
    eapply is_Ex_ival_proper_fun_support; last eassumption; eauto.
    { intros. eapply Hext.
      eapply In_psupport_alt; eexists; split; eauto. eexists; eauto. }
Qed.

Lemma bounded_fun_on_to_bounded f (P: X → Prop):
  bounded_fun_on f P →
  ∃ g, bounded_fun g ∧ (∀ x, P x → f x = g x).
Proof.
  intros Hbf.
  unshelve (eexists).
  { intros x.
    destruct (ClassicalEpsilon.excluded_middle_informative (P x)).
    * exact (f x).
    * exact 0.
  }
  split.
  - destruct Hbf as (c&Hb).
    exists (Rmax 0 c). intros x. destruct ClassicalEpsilon.excluded_middle_informative => //=.
    * etransitivity; last apply Rmax_r. eapply Hb; eauto.
    * etransitivity; last apply Rmax_l. apply Rabs_case; nra.
  - intros x HP. destruct ClassicalEpsilon.excluded_middle_informative => //=.
Qed.

Lemma Ex_min_eq_pidist f Is1 Is2:
  eq_pidist Is1 Is2 →
  Ex_min f Is1 = Ex_min f Is2.
Proof.
  intros. apply Rbar_le_antisym.
  - apply Ex_min_eq_pidist_aux; done.
  - apply Ex_min_eq_pidist_aux. symmetry; done.
Qed.

Lemma Ex_min_le_pidist f Is1 Is2:
  le_pidist Is1 Is2 →
  Rbar_le (Ex_min f Is2) (Ex_min f Is1).
Proof.
  intros Hle.
  transitivity (Ex_min f (pidist_union Is2 Is1)).
  - erewrite Ex_min_eq_pidist; first reflexivity.
    setoid_rewrite pidist_union_comm. setoid_rewrite pidist_union_le_id; eauto; reflexivity.
  - apply Ex_min_pidist_union_r.
Qed.

Lemma ex_Ex_extrema_min_neq_p_infty f (Is: pidist X):
  ex_Ex_extrema f Is →
  Ex_min f Is ≠ p_infty.
Proof.
  intros Hex Hinf.
  assert (∃ I, In I Is) as (I&Hin).
  { destruct Is as ((Is&(I&Hin))&?). eauto. }
  feed pose proof (Ex_min_spec1' f I Is) as Hmin; eauto.
  rewrite Hinf //= in Hmin.
Qed.

Lemma le_pidist_finite_Ex_min f (Is Is': pidist X) :
  le_pidist Is' Is →
  ex_Ex_extrema f Is' →
  is_finite (Ex_min f Is) →
  is_finite (Ex_min f Is').
Proof.
  intros Hle Hex Hfin.
  feed pose proof (Ex_min_le_pidist f _ _ Hle) as Hle_min.
  rewrite -Hfin in Hle_min.
  specialize (ex_Ex_extrema_min_neq_p_infty f Is' Hex) => ?.
  destruct (Ex_min f Is') => //=.
Qed.

Lemma ex_Ex_extrema_le_pidist f (Is Is': pidist X) :
  le_pidist Is' Is →
  ex_Ex_extrema f Is →
  ex_Ex_extrema f Is'.
Proof.
  intros Hle Hex I Hin.
  edestruct Hle as (?&Heq'&Hin'); eauto.
  rewrite Heq'. eapply Hex; eauto.
Qed.

Lemma ex_Ex_extrema_fmap {Y} (g: X → R) h (Is: pidist Y):
  ex_Ex_extrema (λ x, g (h x)) Is ↔ ex_Ex_extrema g (x ← Is; mret (h x)).
Proof.
  split.
  - intros Hex I Hin.
    edestruct (pival_mbind_in_inv_idxOf Is (λ x, mret (h x))) as (I'&h'&Hin'&Hhspec&Heq); eauto.
    assert (eq_ival I (mbind (λ x, mret (h (ind I' x))) (idxOf I'))) as Heq'.
    { rewrite -Heq. eapply ival_bind_pos_congr; first reflexivity.
      intros i [(i'&Heqidx&Hval)|(i'&Heqidx&Hval)].
      * rewrite //= in Heqidx Hval. subst.
        feed pose proof (Hhspec i) as Hhin; eauto.
        inversion Hhin as [Heqh]. rewrite Heqh => //=.
        rewrite /mret/ival_ret. apply eq_ival_quasi_refl.
      * rewrite //= in Heqidx Hval. subst.
        feed pose proof (Hhspec i) as Hhin; eauto.
        inversion Hhin as [Heqh]. rewrite Heqh => //=.
        rewrite /mret/ival_ret. apply eq_ival_quasi_refl.
    }
    assert (eq_ival I (mbind (λ x, mret (h x)) I')) as ->.
    { 
      rewrite Heq'.
      specialize (ival_bind_mret_mret (idxOf I') (ind I') h). intros Heq''.
      rewrite /monad.mret/monad.mbind in Heq''.  rewrite -Heq''.
      eapply ival_bind_congr; last reflexivity.
      symmetry. eapply eq_ival_idxOf.
    }
    rewrite -ex_Ex_ival_fmap. 
    eapply Hex. eauto.
  - intros Hex I Hin.
    apply ex_Ex_ival_fmap.
    edestruct (pival_mbind_in_alt Is (λ x, mret (h x)) I (λ x, mret (h (ind I x))))
      as (Ib&Hpf&Heq&HinIb); eauto.
    * intros. rewrite /mret/pival_ret/In/ival_ret//=.
      eexists; split; first eapply eq_ival_quasi_refl.
      rewrite //=.
    * eapply ex_Ex_ival_proper; last first.
      { eapply Hex. eauto. }
      rewrite -Heq.
      rewrite //=. rewrite /mbind/ival_bind//=.
      eapply eq_ival_quasi_refl.
Qed.

Lemma Ex_min_bounded_below f Is c:
  (∀ x, c <= f x) →
  Rbar_le (Finite c) (Ex_min f Is).
Proof.
  intros Hle. eapply Ex_min_spec2.
  intros r (I&Hin&His).
  rewrite //=.
  rewrite -(is_Ex_ival_unique _ _ _ His).
  eapply (Ex_ivd_bounded_below _ {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |}); eauto.
  eapply is_Ex_ival_ex; eauto.
Qed.

Lemma Ex_min_bounded_supp_below f (Is: pidist X) c:
  (∀ x, In_psupport x Is → c <= f x) →
  Rbar_le (Finite c) (Ex_min f Is).
Proof.
  intros Hle. eapply Ex_min_spec2.
  intros r (I&Hin&His).
  rewrite //=.
  rewrite -(is_Ex_ival_unique _ _ _ His).
  eapply (Ex_ivd_bounded_supp_below _ {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |}); eauto.
  { intros; eapply Hle. eapply In_psupport_alt; eexists; eauto. }
  eapply is_Ex_ival_ex; eauto.
Qed.

Lemma Ex_min_bounded_above f Is c:
  (∀ x, f x <= c) →
  ex_Ex_extrema f Is →
  Rbar_le (Ex_min f Is) (Finite c).
Proof.
  intros Hle. intros Hex.
  destruct Is as ((Is&(I&Hin))&Hall).
  transitivity (Ex_ival f I).
  - eapply Ex_min_spec1' => //=. eapply Hex; eauto.
  - eapply (Ex_ivd_bounded_above _ {| ivd_ival := I; val_sum1 := Hall _ Hin |}); eauto.
Qed.

Lemma Ex_min_bounded_supp_above f (Is: pidist X) c:
  (∀ x, In_psupport x Is → f x <= c) →
  ex_Ex_extrema f Is →
  Rbar_le (Ex_min f Is) (Finite c).
Proof.
  intros Hle. intros Hex.
  destruct Is as ((Is&(I&Hin))&Hall).
  transitivity (Ex_ival f I).
  - eapply Ex_min_spec1' => //=. eapply Hex; eauto.
  - eapply (Ex_ivd_bounded_supp_above _ {| ivd_ival := I; val_sum1 := Hall _ Hin |}); eauto.
    intros. eapply Hle. eapply In_psupport_alt; eexists; eauto.
Qed.

Lemma Ex_min_bounded_fun_finite f Is:
  bounded_fun f →
  is_finite (Ex_min f Is).
Proof.
  intros Hbounded.
  destruct (Ex_min f Is) eqn:Heq.
  * rewrite //=.
  * exfalso. eapply ex_Ex_extrema_min_neq_p_infty; eauto.
    eapply ex_Ex_extrema_bounded_fun; eauto.
  * exfalso. destruct Hbounded as (c&Hlb).
    feed pose proof (Ex_min_bounded_below f Is (-c)) as Hle.
    { intros x. move: (Hlb x). apply Rabs_case; nra. }
    rewrite Heq //= in Hle.
Qed.

Lemma Ex_min_bounded_supp_fun_finite f (Is: pidist X):
  bounded_fun_on f (λ x, In_psupport x Is) →
  is_finite (Ex_min f Is).
Proof.
  intros Hbounded.
  destruct (Ex_min f Is) eqn:Heq.
  * rewrite //=.
  * exfalso. eapply ex_Ex_extrema_min_neq_p_infty; eauto.
    eapply ex_Ex_extrema_bounded_supp_fun; eauto.
  * exfalso. destruct Hbounded as (c&Hlb).
    feed pose proof (Ex_min_bounded_supp_below f Is (-c)) as Hle.
    { intros x Hin. move: (Hlb x Hin).  apply Rabs_case; nra. }
    rewrite Heq //= in Hle.
Qed.

Lemma Ex_min_bounded_is_bounded {A} f Is:
  bounded_fun f →
  bounded_fun (λ x : A, Ex_min f (Is x)).
Proof.
  intros Hb.
  assert (∀ x, ex_Ex_extrema f (Is x)).
  { intros; eapply ex_Ex_extrema_bounded_fun; eauto. }
  assert (Hfin: ∀ x, is_finite (Ex_min f (Is x))).
  { intros; eapply Ex_min_bounded_fun_finite; eauto. }
  destruct Hb as (c&Hb).
  exists c.
  * intros. apply Rabs_case.
    ** intros.
       feed pose proof (Ex_min_bounded_above f (Is x) c) as Hrble; eauto.
       { intros x'. move: (Hb x'); apply Rabs_case; nra. }
       rewrite -Hfin in Hrble. eauto.
    ** intros. apply Ropp_le_cancel. rewrite Ropp_involutive.
       feed pose proof (Ex_min_bounded_below f (Is x) (-c)) as Hrble; eauto.
       { intros x'. move: (Hb x'); apply Rabs_case; nra. }
       rewrite -Hfin in Hrble. eauto.
Qed.

(*
Lemma Ex_min_bounded_supp_is_bounded {A} f (Is: A → pidist X):
  (∀ a, bounded_fun_on f (λ x, In_psupport x (Is a))) →
  bounded_fun (λ x : A, Ex_min f (Is x)).
Proof.
  intros Hb.
  assert (∀ x, ex_Ex_extrema f (Is x)).
  { intros; eapply ex_Ex_extrema_bounded_supp_fun; eauto. }
  assert (Hfin: ∀ x, is_finite (Ex_min f (Is x))).
  { intros; eapply Ex_min_bounded_supp_fun_finite; eauto. }
  destruct Hb as (c&Hb).
  exists c.
  * intros. apply Rabs_case.
    ** intros.
       feed pose proof (Ex_min_bounded_above f (Is x) c) as Hrble; eauto.
       { intros x'. move: (Hb x'); apply Rabs_case; nra. }
       rewrite -Hfin in Hrble. eauto.
    ** intros. apply Ropp_le_cancel. rewrite Ropp_involutive.
       feed pose proof (Ex_min_bounded_below f (Is x) (-c)) as Hrble; eauto.
       { intros x'. move: (Hb x'); apply Rabs_case; nra. }
       rewrite -Hfin in Hrble. eauto.
Qed.
*)

Global Instance Ex_min_proper :
  Proper (pointwise_relation X (@eq R) ==> @eq_pidist X ==> @eq Rbar) (Ex_min).
Proof.
  intros ?? Heq ?? Heq'.
  erewrite Ex_min_eq_ext; last eauto.
    by apply Ex_min_eq_pidist.
Qed. 

Lemma Ex_min_fun_const c (Is: pidist X):
  Ex_min (λ _ : X, c) Is = c.
Proof.
  rewrite /Ex_min.
  apply is_glb_Rbar_unique.
  split.
  - intros r (I&Hin&His).
    cut (c = r).
    { intros; subst => //=. }
    eapply is_Ex_ival_unique'; eauto.
    apply (is_Ex_ivd_const {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |}).
  - intros b His.
    apply His. destruct Is as (Is&?).
    destruct Is as (Is&(I&Hin)).
    exists I; split; auto.
    apply (is_Ex_ivd_const {| ivd_ival := I; val_sum1 := all_sum1 _ Hin |}).
Qed.

Lemma Ex_min_singleton f (I: ivdist X):
  ex_Ex_ival f I →
  Ex_min f (singleton I) = Ex_ival f I.
Proof.
  intros.
  apply is_glb_Rbar_unique.
  split.
  * intros r (I'&Hin&His).
    rewrite Hin. rewrite (is_Ex_ival_unique _ _ _ His). done.
  * intros b Hlb. apply Hlb.
    exists I; split; auto.
    ** done.
    ** apply Ex_ival_correct; auto.
Qed.

Lemma ex_Ex_extrema_singleton f (I: ivdist X):
  ex_Ex_ival f I →
  ex_Ex_extrema f (singleton I).
Proof.
  intros Hex I' <- => //=.
Qed.

Lemma ex_Ex_extrema_pidist_plus f p Hpf Is1 Is2:
  ex_Ex_extrema f Is1 →
  ex_Ex_extrema f Is2 →
  ex_Ex_extrema f (pidist_plus p Hpf Is1 Is2).
Proof.
  intros Hex1 Hex2.
  intros I Hin.
  apply pidist_plus_in_inv in Hin.
  destruct Hin as (I1&I2&Hin1&Hin2&->).
  apply ex_Ex_ival_ivdplus; eauto.
Qed.
    
(* TODO: move *)
Lemma Rbar_mult_to_mult_pos c (k: R) Hgt:
  Rbar_mult c k = Rbar_mult_pos c {| pos := k; cond_pos := Hgt |}.
Proof.
  rewrite /Rbar_mult_pos/Rbar_mult/Rbar_mult'//=.
  destruct c; eauto => //=; try destruct Rle_dec; eauto;
    try destruct (Rle_lt_or_eq_dec); eauto; try nra.
Qed.

Lemma Rbar_div_mult_pos_inv c (k: R) Hgt:
  Rbar_div_pos (Rbar_mult_pos c {| pos := k; cond_pos := Hgt |}) {| pos := k; cond_pos := Hgt |}
               = c.
Proof.
  rewrite /Rbar_div_pos/Rbar_mult_pos/Rbar_mult/Rbar_mult'//=.
  destruct c; eauto => //=; try destruct Rle_dec; eauto;
    try destruct (Rle_lt_or_eq_dec); eauto; try nra.
  f_equal; field; nra.
Qed.

Lemma Rbar_plus_minus (c: Rbar) (k: R):
  c = Rbar_plus (Rbar_plus c (-k)) k.
Proof.
  rewrite /Rbar_plus/Rbar_plus'//=; destruct c; auto.
  f_equal. nra.
Qed.

Lemma Ex_min_scale_const f (Is: pidist X) k:
  k ≥ 0 →
  Ex_min (λ x, k * (f x)) Is = Rbar_mult k (Ex_min f Is).
Proof.
  intros Hge0.
  destruct Hge0 as [Hgt|Heq0]; last first.
  { subst. rewrite //=.
    rewrite Rbar_mult_0_l.
    setoid_rewrite Rmult_0_l.
    apply Ex_min_fun_const.
  }
  apply is_glb_Rbar_unique.
  split.
  - intros i (I&Hin&His).
    apply is_Ex_ival_scal_l_inv in His; last by nra.
    apply Rgt_lt in Hgt.
    apply (Rbar_div_pos_le _ _ {| pos := k; cond_pos := Hgt |}).
    rewrite //=.
    replace (i /k) with (/k * i) by nra.
    rewrite Rbar_mult_comm.
    rewrite (Rbar_mult_to_mult_pos _ k Hgt).
    rewrite (Rbar_div_mult_pos_inv).
    apply Ex_min_spec1. exists I; split; auto.
  - intros b His. 
    apply Rgt_lt in Hgt.
    rewrite Rbar_mult_comm.
    rewrite (Rbar_mult_to_mult_pos _ k Hgt).
    apply (Rbar_div_pos_le _ _ {| pos := k; cond_pos := Hgt |}).
    rewrite (Rbar_div_mult_pos_inv).
    apply Ex_min_spec2.
    intros r (I&Hin&His').
    apply (is_Ex_ival_scal_l _ _ k) in His'.
    feed pose proof (His (k * r)) as Hle; eauto.
    { exists I; split; eauto. }
    apply (Rbar_div_pos_le _ _ {| pos := k; cond_pos := Hgt |}) in Hle.
    rewrite //= in Hle.
    replace (k * r /k) with r in Hle by (field; nra).
    eauto.
Qed.

Lemma Ex_min_plus_const_r f (Is: pidist X) k:
  Ex_min (λ x, f x + k) Is = Rbar_plus (Ex_min f Is) k.
Proof.
  apply is_glb_Rbar_unique.
  split.
  - intros i (I&Hin&His).
    apply (is_Ex_ivd_plus_const_r_inv _ {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin|} k) in His.
    replace (Finite i) with (Rbar_plus (i - k) k ); last first.
    { rewrite //=. f_equal. nra. }
    apply Rbar_plus_le_compat; last by reflexivity.
    apply Ex_min_spec1.
    exists I; split; auto.
  - intros b Hlb.
    rewrite (Rbar_plus_minus b k).
    apply Rbar_plus_le_compat; last by reflexivity.
    apply Ex_min_spec2.
    intros r (I&Hin&His).
    rewrite (Rbar_plus_minus r (-k)).
    apply Rbar_plus_le_compat; last by reflexivity.
    eapply Hlb. exists I; split; auto.
    rewrite Ropp_involutive.
    apply (is_Ex_ivd_plus_const _ {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |} k).
    eauto.
Qed.

Lemma Ex_min_plus_const_l f (Is: pidist X) k:
  Ex_min (λ x, k + f x) Is = Rbar_plus k (Ex_min f Is).
Proof.
  rewrite Rbar_plus_comm. rewrite -Ex_min_plus_const_r.
  apply Ex_min_eq_ext; intros; nra.
Qed.
  
Lemma Ex_min_left_id {A} f (x : A) (h : A → pidist X):
   Ex_min f (x ← mret x; h x) = Ex_min f (h x).
Proof. by setoid_rewrite pidist_left_id. Qed.

Lemma Ex_max_spec1 f Is:
  ∀ r, In r (Ex_pidist f Is) → Rbar_le r (Ex_max f Is).
Proof. intros; destruct (Lub_Rbar_correct (Ex_pidist f Is)); eauto. Qed.

Lemma Ex_max_spec1' f I (Is: pidist X) (Hpf: In I Is) :
  ex_Ex_ival f I →
  Rbar_le (Ex_ival f I) (Ex_max f Is).
Proof. intros; by apply Ex_max_spec1, Ex_pidist_spec1. Qed.

Lemma Ex_max_spec2 f Is r:
  (∀ r', In r' (Ex_pidist f Is) → Rbar_le r' r) → Rbar_le (Ex_max f Is) r.
Proof.
  intros; destruct (Lub_Rbar_correct (Ex_pidist f Is)) as (?&Hglb).
  eapply Hglb; intros ? Hin; apply H; eauto.
Qed.

(*
Lemma Ex_max_spec_witness f (Is: pidist X):
  ∃ I, In I Is ∧ Ex_ival f I = Ex_max f Is.
Proof.
  destruct Is as [[Is Hne] Hsum].
  destruct Is as [| I Is].
  - rewrite //=. destruct Hne as (?&[]).
  - rewrite /Ex_max/Ex_pidist//=. 
    match goal with
    | [ |- context [ fold_left Rmax ?l ?x ] ] =>
      edestruct (fold_left_Rmax_witness1 l x) as [(r&Hin&<-)|(Hmin&Heq)]
    end.
    * apply in_map_iff in Hin as (I'&?&?).
      exists I'; split; auto.
    * exists I; split; auto.
Qed.
*)

Lemma Ex_max_pidist_union f Is1 Is2:
  Ex_max f (pidist_union Is1 Is2) = Rbar_max (Ex_max f Is1) (Ex_max f Is2).
Proof.
  apply Rbar_le_antisym.
  - apply Ex_max_spec2. intros ? (I&Hin&?).
    destruct Hin.
    * etransitivity; last apply Rbar_max_l. apply Ex_max_spec1; exists I; eauto.
    * etransitivity; last apply Rbar_max_r. apply Ex_max_spec1; exists I; eauto.
  - apply Rbar_max_case_strong.
    * intros Hle1. apply Ex_max_spec2. intros ? (I&?&?). apply Ex_max_spec1.
      rewrite /Ex_pidist//=/Ex_pival//=.
      exists I; split; auto.
    * intros Hle1. apply Ex_max_spec2. intros ? (I&?&?). apply Ex_max_spec1.
      rewrite /Ex_pidist//=/Ex_pival//=.
      exists I; split; auto.
Qed.

Lemma Ex_max_pidist_join {A: Type} (a: A) f (Iss: A → pidist X):
  (∀ a, is_finite (Ex_max f (Iss a))) →
  Ex_max f (pidist_join a Iss) =
  Lub_Rbar (λ r, ∃ a, Ex_max f (Iss a) = r).
Proof.
  intros Hfin.
  apply is_lub_Rbar_unique.
  split.
  - intros r (I&Hin&His).
    destruct Hin as (a'&Hin).
    destruct (Lub_Rbar_correct (λ r, ∃ a, Ex_max f (Iss a) = r)) as (Hlb&Hglb).
    etransitivity; last first.
    { apply Hlb. exists a'. rewrite -Hfin. reflexivity. }
    rewrite Hfin. apply Ex_max_spec1. eexists; eauto.
  - intros r Hlb.
    destruct (Lub_Rbar_correct (λ r, ∃ a, Ex_max f (Iss a) = r)) as (Hlb'&Hglb).
    apply Hglb.
    intros r' (a'&<-). 
    apply Ex_max_spec2.
    intros r'' (I'&Hin'&Heq).
    eapply Hlb. exists I'; split; auto.
    eexists; eauto.
Qed.

Lemma Ex_max_pidist_union_l f Is1 Is2:
  Rbar_le (Ex_max f Is1) (Ex_max f (pidist_union Is1 Is2)).
Proof.
  rewrite Ex_max_pidist_union. apply Rbar_max_l.
Qed.

Lemma Ex_max_pidist_union_r f Is1 Is2:
   Rbar_le (Ex_max f Is2) (Ex_max f (pidist_union Is1 Is2)).
Proof.
  rewrite Ex_max_pidist_union. apply Rbar_max_r.
Qed.

Lemma Ex_max_eq_pidist_aux f Is1 Is2:
  eq_pidist Is1 Is2 →
  Rbar_le (Ex_max f Is1) (Ex_max f Is2).
Proof.
  intros Heq.
  apply Ex_max_spec2.
  intros r' Hin. apply Ex_max_spec1.
  apply Ex_pidist_spec2 in Hin as (I2&Hin2&Heq').
  destruct Heq as (Heq1&Heq2). destruct (Heq1 _ Hin2) as (I1&Hequiv&Hin1).
  eexists; split; eauto.
  setoid_rewrite <-Hequiv.
  eauto.
Qed.

Lemma Ex_max_eq_pidist f Is1 Is2:
  eq_pidist Is1 Is2 →
  Ex_max f Is1 = Ex_max f Is2.
Proof.
  intros. apply Rbar_le_antisym.
  - apply Ex_max_eq_pidist_aux; done.
  - apply Ex_max_eq_pidist_aux. symmetry; done.
Qed.

Lemma Ex_max_le_pidist f Is1 Is2:
  le_pidist Is1 Is2 →
  Rbar_le (Ex_max f Is1) (Ex_max f Is2).
Proof.
  intros Hle.
  transitivity (Ex_max f (pidist_union Is2 Is1)).
  - apply Ex_max_pidist_union_r.
  - erewrite Ex_max_eq_pidist; first reflexivity.
    setoid_rewrite pidist_union_comm. setoid_rewrite pidist_union_le_id; eauto; reflexivity.
Qed.
  
Global Instance Ex_max_mono f: Proper (@le_pidist X ==> Rbar_le) (Ex_max f).
Proof. intros ??. apply Ex_max_le_pidist. Qed. 

Lemma Ex_max_eq_ext f1 f2 (Is: pidist X) :
  (∀ x, f1 x = f2 x) → Ex_max f1 Is = Ex_max f2 Is.
Proof.
  intros Hext.
  apply Rbar_le_antisym.
  - apply Ex_max_spec2. intros r' (I&Hin&His).
    eapply Ex_max_spec1. exists I; split; eauto.
    eapply is_Ex_ival_proper'; last eassumption; eauto.
  - apply Ex_max_spec2. intros r' (I&Hin&His).
    eapply Ex_max_spec1. exists I; split; eauto.
    eapply is_Ex_ival_proper'; last eassumption; eauto.
Qed.

Global Instance Ex_max_proper :
  Proper (pointwise_relation X (@eq R) ==> @eq_pidist X ==> @eq Rbar) (Ex_max).
Proof.
  intros ?? Heq ?? Heq'.
  erewrite Ex_max_eq_ext; last eauto.
    by apply Ex_max_eq_pidist.
Qed. 

Lemma Ex_max_left_id {A} f (x : A) (h : A → pidist X):
   Ex_max f (x ← mret x; h x) = Ex_max f (h x).
Proof. by setoid_rewrite pidist_left_id. Qed.

End Ex_extrema_properties.

(* TODO: This lemma could be used to prove many of the facts about Ex_max automatically
   from the fact about Ex_min *)
Lemma Ex_max_neg_min {X} f (Is: pidist X) :
  Ex_max f Is = Rbar_opp (Ex_min (λ x, - f x) Is).
Proof.
  rewrite /Ex_max/Ex_pidist/Ex_pival//=.
  apply is_lub_Rbar_unique.
  split.
  * intros r (I&Hin&His).
    apply is_Ex_ival_negate in His.
    apply Rbar_opp_le.
    rewrite Rbar_opp_involutive.
    apply Ex_min_spec1.
    eexists; eauto.
  * intros b Hub.
    apply Rbar_opp_le.
    rewrite Rbar_opp_involutive.
    eapply Ex_min_spec2.
    intros r (I&Hin&His). apply is_Ex_ival_negate in His.
    setoid_rewrite Ropp_involutive in His.
    feed pose proof (Hub (- r)).
    { eexists; split; eauto. }
    apply Rbar_opp_le.
    rewrite Rbar_opp_involutive //.
Qed.

Lemma Ex_max_eq_ext_supp {X} f1 f2 (Is: pidist X):
  (∀ x, In_psupport x Is → f1 x = f2 x) → Ex_max f1 Is = Ex_max f2 Is.
Proof.
  intros Hsupp. rewrite ?Ex_max_neg_min. f_equal.
  apply Ex_min_eq_ext_supp. intros. f_equal; eauto.
Qed.
  
Lemma Ex_max_le_ext {X} f1 f2 (Is: pidist X):
  (∀ x, f1 x ≤ f2 x) →
  ex_Ex_extrema f2 Is →
  Rbar_le (Ex_max f1 Is) (Ex_max f2 Is).
Proof.
  intros Hf12 Hex.
  rewrite ?Ex_max_neg_min.
  apply Rbar_opp_le.
  apply Ex_min_le_ext.
  * intros x. specialize (Hf12 x). nra.
  * apply ex_Ex_extrema_negate; eauto.
Qed.

Lemma Ex_max_scale_const {X} f (Is: pidist X) k:
  k ≥ 0 →
  Ex_max (λ x, k * (f x)) Is = Rbar_mult k (Ex_max f Is).
Proof.
  rewrite ?Ex_max_neg_min.
  transitivity (Rbar_mult ( - k) ((Ex_min (λ x : X, - f x) Is))).
  { replace (Finite (- k)) with (Rbar_opp (k)); auto. 
    rewrite Rbar_mult_opp_l.
    setoid_rewrite Ropp_mult_distr_r.
    rewrite Ex_min_scale_const //=. 
  }
  replace (Finite (- k)) with (Rbar_opp k); auto.
  rewrite Rbar_mult_opp_l.
  rewrite Rbar_mult_opp_r //=.
Qed.

Lemma Ex_max_plus_const_r {X} f (Is: pidist X) k:
  Ex_max (λ x, f x + k) Is = Rbar_plus (Ex_max f Is) k.
Proof.
  rewrite ?Ex_max_neg_min.
  transitivity (Rbar_plus (Rbar_opp (Ex_min (λ x : X, - f x) Is)) (- - k)).
  { replace (Finite (- - k)) with (Rbar_opp (- k)); auto. rewrite Rbar_plus_opp. 
    f_equal.
    setoid_rewrite Ropp_plus_distr.
    apply Ex_min_plus_const_r.
  }
  f_equal. rewrite Ropp_involutive //=.
Qed.

Lemma Ex_max_plus_const_l {X} f (Is: pidist X) k:
  Ex_max (λ x, k + f x) Is = Rbar_plus k (Ex_max f Is).
Proof.
  rewrite Rbar_plus_comm. rewrite -Ex_max_plus_const_r.
  apply Ex_max_eq_ext; intros; nra.
Qed.

Transparent pidist_ret.
Transparent pidist_bind.

Lemma Ex_min_mret {X} f (r: X):
  Ex_min f (mret r) = f r.
Proof.
  rewrite /Ex_min//=. rewrite -(Ex_ival_mret f r).
  apply is_glb_Rbar_unique.
  split.
  - intros r' (I&Hin&His).
    inversion Hin; subst. rewrite //= in His.
    rewrite -(is_Ex_ival_unique _ _ _ His) => //=.
  - intros b Hlb.
    eapply Hlb. eexists; split; eauto.
    * rewrite //=.
    * eapply is_Ex_ival_proper; last apply Ex_ival_correct, ex_Ex_ival_mret.
      apply eq_ival_quasi_refl.
Qed.

Lemma Ex_min_pair_bound_witness {X1 X2} f1 f2 (m1 : pidist X1) (m2: pidist X2) I (Hpf: In I m2) eps:
  0 < eps →
  is_Ex_ival f2 I (Ex_ival f2 I) →
  Rbar_le (Ex_min f1 m1) (Ex_min f2 m2) →
  ∃ I', In I' m1 ∧ ex_Ex_ival f1 I' ∧ Ex_ival f1 I' ≤ Ex_ival f2 I + eps.
Proof.
  intros ?? Hle.
  apply Classical_Pred_Type.not_all_not_ex.
  intros Hall.
  apply Rbar_le_not_lt in Hle. apply Hle.
  eapply (Rbar_le_lt_trans _ (Ex_ival f2 I)).
  apply Ex_min_spec1.
  { exists I; split; eauto. }
  eapply (Rbar_lt_le_trans _ (Ex_ival f2 I + eps)).
  { rewrite //=. nra. }
  eapply Ex_min_spec2. 
  intros r' (I'&Hin&His). rewrite //=.
  apply Rnot_lt_le.
  intros Hlt.
  eapply Hall; split_and!; eauto.
  { eapply is_Ex_ival_ex; eauto.  }
  rewrite (is_Ex_ival_unique _ _ _ His). nra.
Qed.

Lemma Idist_wit {X} (Is: pidist X) : {I : ival X | In I Is}.
Proof.
  destruct Is as [Is ?].
  destruct Is as (Is&Hne) => //=.
  clear all_sum1.
  apply ClassicalEpsilon.constructive_indefinite_description in Hne.
  exact Hne.
Defined.

Lemma Rbar_le_epsilon:
  ∀ r1 r2 : Rbar, (∀ eps : R, 0 < eps → Rbar_le r1 (Rbar_plus r2 eps)) → Rbar_le r1 r2.
Proof.
  intros r1 r2 Heps.
  rewrite /Rbar_le.
  destruct r1, r2 => //=; auto.
  * apply le_epsilon, Heps.
  * rewrite //= in Heps. eapply (Heps 1); nra.
  * rewrite //= in Heps. eapply (Heps 1); nra.
  * rewrite //= in Heps. eapply (Heps 1); nra.
Qed.

Lemma Ex_min_bind_le {A Y1 Y2} (m: pidist A) (f1: Y1 → R) (f2: Y2 → R)
      (g1: A → pidist Y1) (g2: A → pidist Y2):
  ex_Ex_extrema f1 (mbind g1 m) →
  (∀ a, In_psupport a m → Rbar_le (Ex_min f1 (g1 a)) (Ex_min f2 (g2 a))) →
  Rbar_le (Ex_min f1 (mbind g1 m)) (Ex_min f2 (mbind g2 m)).
Proof.
  intros Hex_Ex Hlef.
  apply Ex_min_spec2 => r' Hin.
  apply Ex_pidist_spec2 in Hin as (I&Hin&Hex).
  apply Rbar_le_epsilon.
  intros eps Hpos.
      edestruct (pival_mbind_in_inv_idxOf _ _ _ Hin) as (Ix&h&Hinx&Hhspec&Heq).
      edestruct (pival_mbind_in_alt2_idxOf m g1 Ix) as (I'&Heq'&Hin'); auto.
      { Unshelve. all: swap 1 2.
        { intros i. 
          destruct (Rgt_dec (val Ix i) 0) as [Hgt|Hngt]; last exact zero_ival.
          specialize (Hlef (ind Ix i)). 
          specialize (Hhspec _ Hgt).
          assert (In_psupport (ind Ix i) m) as Hsupp.
          { do 2 eexists; split; eauto. } 
          feed pose proof (Ex_min_pair_bound_witness f1 f2 (g1 (ind Ix i)) (g2 (ind Ix i)) (h i)
                                                Hhspec eps Hpos) as Hwit.
          { apply Ex_ival_correct.
            eapply (ex_Ex_ival_bind_inv f2 h (idxOf Ix)); eauto.
            eapply ex_Ex_ival_proper.
            { by symmetry. }
            { eapply is_Ex_ival_ex; eauto. }
          }
          { eapply Hlef. eauto. }
          apply ClassicalEpsilon.constructive_indefinite_description in Hwit as (I'&?).
          exact I'.
        }
        eexists; split; eauto.
      }
      {
        intros i Hgt0. rewrite //=. destruct Rgt_dec => //=.
        destruct ClassicalEpsilon.constructive_indefinite_description as (I'&?&?).
        done.
      }
      assert (In I' (choices (pidist_pival (x ← m; g1 x : pidist Y1)))) as Hin''.
      { trivial.  }
      transitivity (Ex_ival f1 I').
      { apply Ex_min_spec1'. eauto.
        eapply Hex_Ex. eauto. }
      rewrite -(is_Ex_ival_unique _ _ _ Hex).
      rewrite //=.
      generalize (eq_ival_Symmetry _ _ Heq) => Heq_sym.

      rewrite -(Ex_ivd_plus_const f2
                                  {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin  |}
                                  eps); last first. 
      { eapply is_Ex_ival_ex; eauto. }
      feed pose proof (is_Ex_ivd_plus_const f2 {| ivd_ival := I;
                                                  val_sum1 := all_sum1 _ _ Hin  |}
                                                                   eps r').
      { eauto.  }
      rewrite /Ex_ivd.
      rewrite (Ex_ival_proper _ _ _ Heq_sym); last first.
      { eapply is_Ex_ival_ex; eauto. }
      symmetry in Heq'.
      rewrite (Ex_ival_proper _ _ _ Heq'); last first.
      { apply Hex_Ex. eauto. } 
     
      eapply Ex_ival_bind_le.
      { intros a Hdom.
        destruct Rgt_dec as [Hgt|Hn] => //=; last first.
        { exfalso. destruct Hdom as (?&?&?). subst. rewrite //= in Hn. }
        destruct ClassicalEpsilon.constructive_indefinite_description as (I0&Hpf&?&?).
        etransitivity; eauto.
        right. symmetry.
        feed pose proof (Hhspec a) as Hinh.
        { eauto. }
        eapply (Ex_ivd_plus_const f2 {| ivd_ival := (h a);
                                        val_sum1 := all_sum1 _ _ Hinh |}).
        rewrite /ex_Ex_ivd//=.
        clear -Heq Hex Hinh Hgt.
        eapply (ex_Ex_ival_bind_inv f2 h (idxOf Ix)); eauto.
        eapply ex_Ex_ival_proper.
        { by symmetry. }
        { eapply is_Ex_ival_ex; eauto. }
      }
      { eapply ex_Ex_ival_proper; eauto. }
      { eapply ex_Ex_ival_proper; eauto.
        eapply is_Ex_ival_ex; eauto. }
Qed.
  
Lemma Ex_min_bind_congr {A Y1 Y2} (m1 m2: pidist A) (f1: Y1 → R) (f2: Y2 → R)
      (g1: A → pidist Y1) (g2: A → pidist Y2):
  eq_pidist m1 m2 →
  ex_Ex_extrema f1 (m2 ≫= g1) →
  (∀ a, Rbar_le (Ex_min f1 (g1 a)) (Ex_min f2 (g2 a))) →
  Rbar_le (Ex_min f1 (mbind g1 m1)) (Ex_min f2 (mbind g2 m2)).
Proof.
  intros Heq. 
  setoid_rewrite Heq.
  intros. apply Ex_min_bind_le; eauto.
Qed.

Lemma Ex_min_bind_post_aux1 {X Y} f (h: X → pidist Y) (Is: pidist X):
  is_finite (Ex_min (λ x, Ex_min f (h x)) Is) →
  (∀ x, is_finite (Ex_min f (h x))) →
  ex_Ex_extrema f (x ← Is; h x) →
  Rbar_le (Ex_min f (x ← Is; h x)) (Ex_min (λ x, Ex_min f (h x)) Is).
Proof.
  intros Hfin Hfin_all Hex.
  assert (∀ eps, 0 < eps →
                 ∃ hmin : X → ival Y, ∀ x, In (hmin x) (h x) ∧
                                           Ex_min f (h x) <= Ex_ival f (hmin x)
                                           <= Ex_min f (h x) + eps)
   as Hhminfun.
  { 
    intros eps Hpos.
    unshelve (eexists).
    { intros x. specialize (Ex_min_spec_witness f (h x) eps) => Hwit.
      apply ClassicalEpsilon.constructive_indefinite_description in Hwit
        as (I&?).
      * exact I.
      * eauto.
      * eauto.
    }
    intros x => //=;
                  destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?&?);
                  split; auto.
  }
  apply Rbar_le_epsilon => eps Hpos_eps.
  assert (0 < eps/2) as Hpos_eps2.
  { nra. }
  edestruct (Ex_min_spec_witness (λ x, Ex_min f (h x)) Is _ Hpos_eps2) as (Ialt&Hin_alt&Heq_alt).
  { eauto. }
  destruct (Hhminfun _ Hpos_eps2) as (hmin&Hhminspec).
  transitivity (Ex_ival f (x ← Ialt; hmin x)).
  ** edestruct (pival_mbind_in_alt2_idxOf Is h Ialt (λ x, hmin (ind Ialt x))) as (?&Hequiv'&?).
    { eexists; split; eauto; reflexivity. }
    { intros i Hgt0. edestruct Hhminspec; eauto. }
    assert (eq_ival (i ← Ialt; hmin i)
                    (i ← idxOf Ialt; hmin (ind Ialt i))) as Hequiv''.
    {
      setoid_rewrite eq_ival_idxOf at 3.
      setoid_rewrite ival_assoc.
      apply ival_bind_congr; first reflexivity.
      intros ix. setoid_rewrite ival_left_id; reflexivity.
    }
    setoid_rewrite <-Hequiv'' in Hequiv'.
    symmetry in Hequiv'.
    rewrite -(Ex_ival_proper _ _ _ Hequiv'); last first.
    { eapply Hex; eauto. }
    apply Ex_min_spec1'; eauto.
  ** destruct Heq_alt as (?&Hbound1&Hbound2).
     assert (ex_Ex_ival f (Ialt ≫= [eta hmin])).
     {
       edestruct (pival_mbind_in_alt2_idxOf Is h Ialt (λ ix, hmin (ind Ialt ix)))
         as (I'&Heq&Hin); eauto.
       { intros. eapply Hhminspec. }
       eapply (ex_Ex_ival_proper _ I'); last first.
       { eapply Hex; eauto. }
       rewrite -Heq.
       etransitivity; last first.
       { eapply ival_bind_congr.
         * symmetry; eapply eq_ival_idxOf.
         * reflexivity.
       }
       rewrite ival_assoc. eapply ival_bind_congr; first reflexivity.
       intros x. rewrite ival_left_id. done.
     }
     rewrite Ex_ival_bind_post; last auto.
     rewrite -Hfin //= in Hbound1 Hbound2 *.
     replace eps with (eps/2 + eps/2); last by field.
     rewrite -Rplus_assoc.
     apply (Rplus_le_compat_r (eps/2)) in Hbound2.
     setoid_rewrite <-Hbound2.
     rewrite -(Ex_ivd_plus_const (λ x, Ex_min f (h x))
                                 {| ivd_ival := Ialt; val_sum1 := all_sum1 _ _ Hin_alt |});
       auto. rewrite /Ex_ivd//=.
     eapply Ex_ival_mono.
     * intros x. edestruct (Hhminspec x). nra.
     * apply ex_Ex_ival_bind_post; eauto.
     * eapply (ex_Ex_ivd_plus_const (λ x, Ex_min f (h x))
                                 {| ivd_ival := Ialt; val_sum1 := all_sum1 _ _ Hin_alt |}).
       eauto.
Qed.

Lemma Ex_min_bind_post_aux2 {X Y} f (h: X → pidist Y) (Is: pidist X):
  is_finite (Ex_min (λ x, Ex_min f (h x)) Is) →
  (∀ x, is_finite (Ex_min f (h x))) →
  ex_Ex_extrema (λ x, Ex_min f (h x)) Is →
  Rbar_le (Ex_min (λ x, Ex_min f (h x)) Is) (Ex_min f (x ← Is; h x)).
Proof.
  intros Hfin1 Hfin_all Hex.
  eapply Ex_min_spec2.
  intros r (I&Hin&His).
  rewrite -(is_Ex_ival_unique _ _ _ His).  
  rewrite -Hfin1 //=.
  edestruct (pival_mbind_in_inv_idxOf Is h I) as (Ialt&h'&Hin'&Hhspec'&Heq'); eauto.
  symmetry in Heq'.
  rewrite (Ex_ival_proper _ _ _ Heq'); last first.
  { eapply is_Ex_ival_ex; eauto. }
  transitivity (Ex_ival (λ x, Ex_min f (h x)) Ialt).
  { feed pose proof (Ex_min_spec1' (λ x, Ex_min f (h x))  Ialt Is) as Hle; eauto.
    rewrite -Hfin1 //= in Hle. }
  
  rewrite (Ex_ival_proper _ Ialt _ (eq_ival_idxOf Ialt)); eauto.
  assert (ex_Ex_ival (λ x : X, Ex_min f (h x))
                     (idxOf Ialt ≫= (λ x : idx Ialt, monad.mret (ind Ialt x)))).
  { 
    eapply ex_Ex_ival_proper.
    * eapply eq_ival_idxOf.
    * apply Hex; eauto. 
  }
  assert (ex_Ex_ival f (idxOf Ialt ≫= [eta h'])).
  { eapply ex_Ex_ival_proper; try eassumption.
    eapply is_Ex_ival_ex; eauto. }
  rewrite ?Ex_ival_bind_post //.
  - eapply Ex_ival_mono_support.
    * intros x ?. rewrite Ex_ival_mret.
      feed pose proof (Ex_min_spec1' f (h' x) (h (ind Ialt x))) as Hle; eauto.
      { apply (ex_Ex_ival_bind_inv _ _ (idxOf Ialt)); auto. }
      rewrite -Hfin_all //= in Hle.
    * eapply ex_Ex_ival_bind_post; eauto. 
    * eapply ex_Ex_ival_bind_post; eauto. 
Qed.

Lemma Ex_min_bind_post {X Y} f (h: X → pidist Y) (Is: pidist X):
  is_finite (Ex_min (λ x, Ex_min f (h x)) Is) →
  (∀ x, is_finite (Ex_min f (h x))) →
  ex_Ex_extrema f (x ← Is; h x) →
  ex_Ex_extrema (λ x, Ex_min f (h x)) Is →
 Ex_min f (x ← Is; h x) =  Ex_min (λ x, Ex_min f (h x)) Is.
Proof.
  intros Hfin ???.
  apply Rbar_le_antisym.
  - apply Ex_min_bind_post_aux1; eauto.
  - apply Ex_min_bind_post_aux2; eauto.
Qed.

Lemma Ex_min_comp {X Y} f (g: Y → R) (Is: pidist X):
  is_finite (Ex_min (λ x, g (f x)) Is) →
  ex_Ex_extrema (λ x, g (f x)) Is →
 Ex_min (λ x, g (f x)) Is = Ex_min g (x ← Is; mret (f x)).
Proof.
  intros Hfin Hex. 
  symmetry.
  assert ((Ex_min (λ x : X, Ex_min g (mret (f x))) Is) =
          (Ex_min (λ x, g (f x)) Is)) as Hex_eq.
  { apply Ex_min_proper; eauto.
    { intros z. rewrite Ex_min_mret //=. }
    { reflexivity. }
  }
  rewrite (@Ex_min_bind_post X Y g (λ x, mret (f x)) Is) //=.
  { rewrite Hex_eq.  eauto. }
  { intros x. rewrite Ex_min_mret. rewrite //=. }
  { intros I Hin.
    edestruct (pival_mbind_in_inv_idxOf Is (λ x, mret (f x))) as (I'&h'&Hin'&Hh&Heq); eauto.
    setoid_rewrite <-Heq.
    assert (∀ i, val I' i > 0 → h' i = mret (f (ind I' i))) as Hheq.
    { intros ? Hgt. specialize (Hh _ Hgt). inversion Hh as [Heqh]. rewrite /mret/ival_ret.
      rewrite Heqh. f_equal. apply classical_proof_irrelevance. }
    eapply (ex_Ex_ival_proper _ (x ← I'; mret (f x))).
    * setoid_rewrite (eq_ival_idxOf I') at 1.
      setoid_rewrite ival_assoc. apply ival_bind_pos_congr; first reflexivity.
      intros a [(i&Heqi&Hgt)|(i&Heqi&Hgt)].
      ** setoid_rewrite ival_left_id. rewrite Hheq; first reflexivity.
         subst. rewrite //=.
      ** setoid_rewrite ival_left_id. rewrite Hheq; first reflexivity.
         subst. rewrite //=.
    * rewrite -ex_Ex_ival_fmap. eapply Hex. eauto.
  }
  {  eapply ex_Ex_extrema_proper'.
     * intros. rewrite Ex_min_mret. eauto.
     * reflexivity.
     * eassumption.
  }
Qed.

Ltac refl_right :=
  match goal with
  | [ |- ?X ?A ?B ] => cut (A = B); first by (intros ->; reflexivity)
  end.

Lemma Ex_min_bind_union {X A} f (m: pidist X) (m1 m2: pidist A) (h: A → pidist X):
  Rbar_le (Ex_min f m) (Ex_min f (mbind h m1)) →
  Rbar_le (Ex_min f m) (Ex_min f (mbind h m2)) →
  Rbar_le (Ex_min f m) (Ex_min f (mbind h (pidist_union m1 m2 : pidist A))).
Proof.
  intros Hle1 Hle2.
  transitivity (Ex_min f (pidist_union (x ← m1; h x) (x ← m2; h x))).
  { rewrite Ex_min_pidist_union.
    apply Rbar_min_case; auto. }
  refl_right. apply Ex_min_eq_pidist. rewrite /eq_pidist/pidist_union//=.
  symmetry. apply pival_union_bind.
Qed.

Lemma Ex_rvar_of_pidist_ivd  (I: ivdist R) (Is: pidist R) Hpf:
  Ex (rvar_of_pidist (ivd_ival I) Is Hpf) = Ex (rvar_of_ivdist I).
Proof.
  rewrite /rvar_of_pidist//=.
Qed.

Lemma Ex_min_pidist_plus {X} f p Hpf (Is1 Is2 : pidist X):
  is_finite (Ex_min f Is1) →
  is_finite (Ex_min f Is2) →
  ex_Ex_extrema f (pidist_plus p Hpf Is1 Is2) →
  Ex_min f (pidist_plus p Hpf Is1 Is2) =
  Rbar_plus (Rbar_mult p (Ex_min f Is1))
            (Rbar_mult (1 - p) (Ex_min f Is2)).
Proof.
  intros Hf1 Hf2.
  transitivity (Ex_min f (x ← singleton (ivdplus p Hpf (mret true) (mret false));
                          if x then Is1 else Is2)).
  { eapply Ex_min_proper; first done.
    * rewrite singleton_plus. 
      setoid_rewrite pidist_plus_bind.
      apply pidist_plus_proper.
      ** rewrite singleton_mret pidist_left_id //=.
      ** rewrite singleton_mret pidist_left_id //=.
  }
  assert (Heq: Ex_min (λ x : bool, Ex_min f (if x then Is1 else Is2))
                 (singleton (ivdplus p Hpf (mret true) (mret false)))
          = Rbar_plus (Rbar_mult p (Ex_min f Is1)) (Rbar_mult (1 - p) (Ex_min f Is2))).
  { rewrite Ex_min_singleton.
    ** rewrite Ex_ival_ivdplus; try apply ex_Ex_ival_mret.
       rewrite ?Ex_ival_mret.
       rewrite -Hf1 -Hf2 //=.
    ** apply ex_Ex_ival_ivdplus; apply ex_Ex_ival_mret.
  }
  rewrite Ex_min_bind_post; auto.
  * rewrite Heq -Hf1 -Hf2 //=.
  * intros []; eauto.
  * setoid_rewrite singleton_plus. setoid_rewrite pidist_plus_bind.
    rewrite ?singleton_mret ?pidist_left_id //=.
  * apply ex_Ex_extrema_singleton, ex_Ex_ival_ivdplus; apply ex_Ex_ival_mret.
Qed.

(*
Lemma Ex_min_pidist_plus_le_l {X Y} (f: X → R) (g: Y → R) p Hpf Is1 Is2 m:
  Rbar_le (Ex_min f Is1) (Ex_min g m) →
  Rbar_le (Ex_min f Is2) (Ex_min g m) →
  Ex_min f (pidist_plus p Hpf Is1 Is2) ≤ Ex_min g m.
Proof. rewrite Ex_min_pidist_plus. intros. nra. Qed.

Lemma Ex_min_pidist_plus_le_r {X Y} (f: X → R) (g: Y → R) p Hpf Is1 Is2 m:
  Ex_min f m ≤ Ex_min g Is1 →
  Ex_min f m ≤ Ex_min g Is2 →
  Ex_min f m ≤ Ex_min g (pidist_plus p Hpf Is1 Is2).
Proof. rewrite Ex_min_pidist_plus. intros. nra. Qed.

Lemma Ex_min_pidist_plus_le_compat {X Y} (f: X → R) (g: Y → R) p Hpf Is1 Is1' Is2 Is2':
  Ex_min f Is1 ≤ Ex_min g Is1' →
  Ex_min f Is2 ≤ Ex_min g Is2' →
  Ex_min f (pidist_plus p Hpf Is1 Is2) ≤
  Ex_min g (pidist_plus p Hpf Is1' Is2').
Proof. rewrite ?Ex_min_pidist_plus. intros. nra. Qed.
*)

Lemma Ex_min_pidist_plus_bind {A X} f p Hpf (Is1 Is2: pidist A) (g: A → pidist X):
  is_finite (Ex_min f (x ← Is1; g x)) →
  is_finite (Ex_min f (x ← Is2; g x)) →
  ex_Ex_extrema f (x ← pidist_plus p Hpf Is1 Is2; g x) →
  Ex_min f (x ← pidist_plus p Hpf Is1 Is2; g x) =
  p * (Ex_min f (x ← Is1; g x)) + (1 - p) * (Ex_min f (x ← Is2; g x)).
Proof.
  intros Hfin1 Hfin2 Hex; setoid_rewrite pidist_plus_bind.
  rewrite Ex_min_pidist_plus; eauto.
  * rewrite -Hfin1 -Hfin2 //=.
  * rewrite -pidist_plus_bind //.
Qed.

(*
Lemma Ex_min_pidist_plus_bind_le_l {A Y X} f f' p Hpf (Is1 Is2: pidist A)
      (m: pidist Y) (g: A → pidist X):
  Ex_min f (x ← Is1; g x) ≤ Ex_min f' m →
  Ex_min f (x ← Is2; g x) ≤ Ex_min f' m →
  Ex_min f (x ← pidist_plus p Hpf Is1 Is2; g x) ≤ Ex_min f' m.
Proof. intros. setoid_rewrite pidist_plus_bind. apply Ex_min_pidist_plus_le_l; eauto. Qed.

Lemma Ex_min_pidist_plus_bind_le_r {A Y X} f f' p Hpf (Is1 Is2: pidist A) (m: pidist Y)
      (g: A → pidist X):
  Ex_min f m ≤ Ex_min f' (x ← Is1; g x) →
  Ex_min f m ≤ Ex_min f' (x ← Is2; g x) →
  Ex_min f m ≤ Ex_min f' (x ← pidist_plus p Hpf Is1 Is2; g x).
Proof. intros. setoid_rewrite pidist_plus_bind. apply Ex_min_pidist_plus_le_r; eauto. Qed.

Lemma Ex_min_pidist_plus_bind_le_compat {A A' X X'} f g p Hpf
      (Is1 Is2: pidist A) (Is1' Is2': pidist A') (h: A → pidist X) (h': A' → pidist X'):
  Ex_min f (x ← Is1; h x) ≤ Ex_min g (x ← Is1'; h' x)  →
  Ex_min f (x ← Is2; h x) ≤ Ex_min g (x ← Is2'; h' x)  →
  Ex_min f (x ← pidist_plus p Hpf Is1 Is2; h x) ≤
  Ex_min g (x ← pidist_plus p Hpf Is1' Is2'; h' x).
Proof. intros. setoid_rewrite pidist_plus_bind. apply Ex_min_pidist_plus_le_compat; eauto. Qed.
*)

Lemma Ex_min_const {A} (m: pidist A) k:
  Ex_min (λ x, k) m = k.
Proof.
  apply is_glb_Rbar_unique; split.
  - intros r (I&Hin&His).
    cut (k = r); first by (intros; subst; auto).
    rewrite -(Ex_ivd_const {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin |} k) //=.
    apply is_Ex_ival_unique; auto.
  - intros b Hle. apply Hle.
    destruct m as ((Is&(I&Hin))&Hall).
    exists I => //=; split; intuition.
    apply (is_Ex_ivd_const {| ivd_ival := I; val_sum1 := Hall _ Hin |} k).
Qed.

(* this could be generalized *)
Lemma ex_Ex_extrema_bind_irrel_const {A} (m1: pidist A) k:
  ex_Ex_extrema id (m1 ≫= (λ _ : A, mret k)).
Proof.
  intros I Hin.
  edestruct (pival_mbind_in_inv_idxOf m1 (λ _, mret k) I) as (Ix&h&Hin'&Hhspec&Heq); eauto.
  setoid_rewrite <-Heq.
  assert (eq_ival (x ← idxOf Ix; h x) (x ← idxOf Ix; mret k)) as Hsimpl_eq.
  { eapply ival_bind_pos_congr; first reflexivity.
    intros ix [(i&Heq_ind&Hpos)|(i&Heq_ind&Hpos)].
    * subst. feed pose proof (Hhspec i) as Hin''; eauto.
      rewrite //=. inversion Hin'' as [Heq'']. rewrite Heq''.
      apply eq_ival_quasi_refl.
    * subst. feed pose proof (Hhspec i) as Hin''; eauto.
      rewrite //=. inversion Hin'' as [Heq'']. rewrite Heq''.
      apply eq_ival_quasi_refl.
  }
  setoid_rewrite Hsimpl_eq.
  eapply (is_Ex_ival_ex _ _ k).
  apply is_Ex_ival_bind_irrel.
  { rewrite //=. eapply all_sum1; eauto. }
  apply is_Ex_ival_mret.
Qed.
      
Lemma Ex_min_bind_const {A Y1} (m1: pidist A) (f1: Y1 → R)
      (g1: A → pidist Y1)  (k: R):
  ex_Ex_extrema f1 (m1 ≫= g1) →
  (∀ a, Ex_min f1 (g1 a) = Finite k) →
  Ex_min f1 (mbind g1 m1) = Finite k.
Proof.
  intros Hex Hconst.
  transitivity (Ex_min id (x ← m1; mret k)).
  { 
    apply Rbar_le_antisym.
    - eapply Ex_min_bind_congr; first reflexivity; auto.
      intros. rewrite Hconst Ex_min_mret. reflexivity.
    - eapply Ex_min_bind_congr; first reflexivity; eauto.
      { eapply ex_Ex_extrema_bind_irrel_const. }
      intros; rewrite Hconst Ex_min_mret. reflexivity.
  }
  rewrite Ex_min_bind_post.
  * setoid_rewrite Ex_min_const. by rewrite Ex_min_mret.
  * setoid_rewrite Ex_min_const. by rewrite Ex_min_mret.
  * intros. by rewrite Ex_min_mret.
  * eapply ex_Ex_extrema_bind_irrel_const.
  * setoid_rewrite Ex_min_mret. eapply ex_Ex_extrema_const.
Qed.

Lemma Ex_min_bind_const_le {A Y1} (m1: pidist A) (f1: Y1 → R)
      (g1: A → pidist Y1)  (k: R):
  ex_Ex_extrema f1 (m1 ≫= g1) →
  (∀ a, Rbar_le (Ex_min f1 (g1 a)) k) →
  Rbar_le (Ex_min f1 (mbind g1 m1)) k.
Proof.
  intros Hex Hconst.
  transitivity (Ex_min id (x ← m1; mret k)).
  { 
    eapply Ex_min_bind_congr; first reflexivity; eauto.
    intros. rewrite Ex_min_mret. eauto.
  }
  rewrite Ex_min_bind_post.
  * setoid_rewrite Ex_min_const. by rewrite Ex_min_mret.
  * setoid_rewrite Ex_min_const. by rewrite Ex_min_mret.
  * intros. by rewrite Ex_min_mret.
  * eapply ex_Ex_extrema_bind_irrel_const.
  * setoid_rewrite Ex_min_mret. eapply ex_Ex_extrema_const.
Qed.

Lemma Ex_min_bind_const_ge {A Y1} (m1: pidist A) (f1: Y1 → R)
      (g1: A → pidist Y1)  (k: R):
  (∀ a, Rbar_le k (Ex_min f1 (g1 a))) →
  Rbar_le k (Ex_min f1 (mbind g1 m1)).
Proof.
  intros Hconst.
  transitivity (Ex_min id (x ← m1; mret k)); last first.
  { 
    eapply Ex_min_bind_congr; first reflexivity.
    * apply ex_Ex_extrema_bind_irrel_const. 
    * intros. rewrite Ex_min_mret. eauto.
  }
  rewrite Ex_min_bind_post.
  * setoid_rewrite Ex_min_const. by rewrite Ex_min_mret.
  * setoid_rewrite Ex_min_const. by rewrite Ex_min_mret.
  * intros. by rewrite Ex_min_mret.
  * eapply ex_Ex_extrema_bind_irrel_const.
  * setoid_rewrite Ex_min_mret. eapply ex_Ex_extrema_const.
Qed.

Lemma Ex_min_bind_irrel {X Y} f (Is: pidist X) (m: pidist Y) :
  ex_Ex_extrema f (mbind (λ x, Is) m) →
  is_finite (Ex_min f Is) →
  Ex_min f (mbind (λ x, Is) m) = Ex_min f Is.
Proof.
  intros Hex Hfin. rewrite -Hfin.
  apply Rbar_le_antisym.
  - apply Ex_min_bind_const_le; eauto; intros. rewrite Hfin. reflexivity.
  - apply Ex_min_bind_const_ge; eauto; intros. rewrite Hfin. reflexivity.
Qed.

(*
Lemma Ex_min_bind_irrel' {X Y} f (Is: pidist X) (m: pidist Y) :
  Ex_min f (mbind (λ x, Is) m) = Ex_min f Is.
Proof.
  symmetry.
  apply is_glb_Rbar_unique.
  split.
  intros r (I&Hin&His).
  - 
  - intros b Hlb. apply Ex_min_spec2.
   intros r (I&Hin&His).
    edestruct (pival_mbind_in_inv_idxOf m (λ _, Is)) as (I'&h'&Hin'&Hhspec&Heq); eauto.
    rewrite -Heq in His * => His.
    rewrite -(is_Ex_ival_unique _ _ _ His).
    rewrite /Ex_ival. 
    assert (Ex_min f Is ≠ p_infty).
    { intros Hp.
      destruct (ivd_support_idx {| ivd_ival := idxOf I'; val_sum1 := all_sum1 _ _ Hin'|})
        as (i&Hgt).
      rewrite //= in i Hgt. 
  rewrite -Hfin.
  apply Rbar_le_antisym.
  - apply Ex_min_bind_const_le; eauto; intros. rewrite Hfin. reflexivity.
  - apply Ex_min_bind_const_ge; eauto; intros. rewrite Hfin. reflexivity.
Qed.
*)

Lemma Ex_max_bind_const {A Y1} (m1: pidist A) (f1: Y1 → R)
      (g1: A → pidist Y1)  k:
  ex_Ex_extrema f1 (m1 ≫= g1) →
  (∀ a, Ex_max f1 (g1 a) = Finite k) →
  Ex_max f1 (mbind g1 m1) = Finite k.
Proof.
  intros Hex Hconst.
  rewrite Ex_max_neg_min.
  rewrite (Ex_min_bind_const _ _ _ (-k)).
  { clear. rewrite //=. by rewrite Ropp_involutive. }
  { apply ex_Ex_extrema_negate; eauto. }
  intros a. replace (Finite (-k)) with (Rbar_opp (Finite k)) by auto. rewrite -(Hconst a).
  rewrite -[a in a = _]Rbar_opp_involutive.
  rewrite -Ex_max_neg_min. auto.
Qed.

Lemma Ex_max_mret {X} f (r: X):
  Ex_max f (mret r) = f r.
Proof.
  rewrite Ex_max_neg_min Ex_min_mret //= Ropp_involutive //=.
Qed.

Lemma Ex_max_pair_bound_witness {X1 X2} f1 f2 (m1 : pidist X1) (m2: pidist X2) I (Hpf: In I m2) eps:
  0 < eps →
  is_Ex_ival f2 I (Ex_ival f2 I) →
  Rbar_le (Ex_max f2 m2) (Ex_max f1 m1) →
  ∃ I', In I' m1 ∧ ex_Ex_ival f1 I' ∧ Ex_ival f2 I ≤ Ex_ival f1 I' + eps.
Proof.
  intros ?? Hle.
  apply Classical_Pred_Type.not_all_not_ex.
  intros Hall.
  apply Rbar_le_not_lt in Hle. apply Hle.
  eapply (Rbar_lt_le_trans _ (Ex_ival f2 I)); last first.
  apply Ex_max_spec1.
  { exists I; split; eauto. }
  eapply (Rbar_le_lt_trans _ (Ex_ival f2 I - eps)); last first.
  { rewrite //=. nra. }
  eapply Ex_max_spec2. 
  intros r' (I'&Hin&His). rewrite //=.
  apply Rnot_lt_le.
  intros Hlt.
  eapply Hall; split_and!; eauto.
  { eapply is_Ex_ival_ex; eauto.  }
  rewrite (is_Ex_ival_unique _ _ _ His). nra.
Qed.

Lemma Ex_max_bind_le {A Y1 Y2} (m: pidist A) (f1: Y1 → R) (f2: Y2 → R)
      (g1: A → pidist Y1) (g2: A → pidist Y2):
  ex_Ex_extrema f2 (mbind g2 m) →
  (∀ a, In_psupport a m → Rbar_le (Ex_max f1 (g1 a)) (Ex_max f2 (g2 a))) →
  Rbar_le (Ex_max f1 (mbind g1 m)) (Ex_max f2 (mbind g2 m)).
Proof.
  intros Hex_Ex Hlef.
  rewrite ?Ex_max_neg_min.
  apply Rbar_opp_le.
  eapply Ex_min_bind_le.
  { apply ex_Ex_extrema_negate; auto. }
  intros. apply Rbar_opp_le. rewrite -?Ex_max_neg_min; eauto.
Qed.

(*
Lemma Ex_max_bind_irrel {X Y} f (Is: pidist X) (m: pidist Y) :
  ex_Ex_extrema f (mbind (λ x, Is) m) →
  is_finite (Ex_max f Is) →
  Ex_max f (mbind (λ x, Is) m) = Ex_max f Is.
Proof.
  intros Hex Hfin. apply  rewrite -Hfin.
  apply Rbar_le_antisym.
  - apply Ex_max_bind_const_le; eauto; intros. rewrite Hfin. reflexivity.
  - apply Ex_min_bind_const_ge; eauto; intros. rewrite Hfin. reflexivity.
Qed.
*)
  
Lemma Ex_max_bind_congr {A Y1 Y2} (m1 m2: pidist A) (f1: Y1 → R) (f2: Y2 → R)
      (g1: A → pidist Y1) (g2: A → pidist Y2):
  eq_pidist m1 m2 →
  ex_Ex_extrema f2 (m2 ≫= g2) →
  (∀ a, Rbar_le (Ex_max f1 (g1 a)) (Ex_max f2 (g2 a))) →
  Rbar_le (Ex_max f1 (mbind g1 m1)) (Ex_max f2 (mbind g2 m1)).
Proof.
  intros Heq Hex. 
  setoid_rewrite Heq.
  intros. by apply Ex_max_bind_le.
Qed.

Lemma Ex_max_bind_union {X A} f (m: pidist X) (m1 m2: pidist A) (h: A → pidist X):
  Rbar_le (Ex_max f (mbind h m1)) (Ex_max f m) →
  Rbar_le (Ex_max f (mbind h m2)) (Ex_max f m) →
  Rbar_le (Ex_max f (mbind h (pidist_union m1 m2 : pidist A))) (Ex_max f m).
Proof.
  intros Hle1 Hle2.
  transitivity (Ex_max f (pidist_union (x ← m1; h x) (x ← m2; h x))); last first.
  { rewrite Ex_max_pidist_union.
    apply Rbar_max_case; auto. }
  refl_right. apply Ex_max_eq_pidist. rewrite /eq_pidist/pidist_union//=.
  apply pival_union_bind.
Qed.

Lemma is_finite_Ex_max_to_min {X} (f: X → R) I:
  is_finite (Ex_max f I) →
  is_finite (Ex_min (λ x0, - f x0) I).
Proof.
  intros Hfin. rewrite -[a in is_finite a]Rbar_opp_involutive -Ex_max_neg_min -Hfin //=.
Qed.

Lemma Ex_max_pidist_plus {X} f p Hpf (Is1 Is2 : pidist X):
  is_finite (Ex_max f Is1) →
  is_finite (Ex_max f Is2) →
  ex_Ex_extrema f (pidist_plus p Hpf Is1 Is2) →
  Ex_max f (pidist_plus p Hpf Is1 Is2) =
  Rbar_plus (Rbar_mult p (Ex_max f Is1)) (Rbar_mult (1 - p) (Ex_max f Is2)).
Proof.
  intros Hfin1 Hfin2 Hex. rewrite Ex_max_neg_min Ex_min_pidist_plus.
  { rewrite -Rbar_plus_opp -?Rbar_mult_opp_r -?Ex_max_neg_min //=. }
  { apply is_finite_Ex_max_to_min; auto. } 
  { apply is_finite_Ex_max_to_min; auto. } 
  apply ex_Ex_extrema_negate; auto.
Qed.

(*
Lemma Ex_max_pidist_plus_le_l {X Y} (f: X → R) (g: Y → R) p Hpf Is1 Is2 m:
  Ex_max f Is1 ≤ Ex_max g m →
  Ex_max f Is2 ≤ Ex_max g m →
  Ex_max f (pidist_plus p Hpf Is1 Is2) ≤ Ex_max g m.
Proof. rewrite Ex_max_pidist_plus. intros. nra. Qed.

Lemma Ex_max_pidist_plus_le_r {X Y} (f: X → R) (g: Y → R) p Hpf Is1 Is2 m:
  Ex_max f m ≤ Ex_max g Is1 →
  Ex_max f m ≤ Ex_max g Is2 →
  Ex_max f m ≤ Ex_max g (pidist_plus p Hpf Is1 Is2).
Proof. rewrite Ex_max_pidist_plus. intros. nra. Qed.

Lemma Ex_max_pidist_plus_le_compat {X Y} (f: X → R) (g: Y → R) p Hpf Is1 Is1' Is2 Is2':
  Ex_max f Is1 ≤ Ex_max g Is1' →
  Ex_max f Is2 ≤ Ex_max g Is2' →
  Ex_max f (pidist_plus p Hpf Is1 Is2) ≤
  Ex_max g (pidist_plus p Hpf Is1' Is2').
Proof. rewrite ?Ex_max_pidist_plus. intros. nra. Qed.
*)

Lemma Ex_max_pidist_plus_bind {A X} f p Hpf (Is1 Is2: pidist A) (g: A → pidist X):
  is_finite (Ex_max f (x ← Is1; g x)) →
  is_finite (Ex_max f (x ← Is2; g x)) →
  ex_Ex_extrema f (x ← pidist_plus p Hpf Is1 Is2; g x) →
  Ex_max f (x ← pidist_plus p Hpf Is1 Is2; g x) =
  p * (Ex_max f (x ← Is1; g x)) + (1 - p) * (Ex_max f (x ← Is2; g x)).
Proof.
  intros Hfin1 Hfin2 Hex; setoid_rewrite pidist_plus_bind.
  rewrite Ex_max_pidist_plus; eauto.
  * rewrite -Hfin1 -Hfin2 //=.
  * rewrite -pidist_plus_bind //.
Qed.

(*
Lemma Ex_max_pidist_plus_bind_le_l {A Y X} f f' p Hpf (Is1 Is2: pidist A)
      (m: pidist Y) (g: A → pidist X):
  Ex_max f (x ← Is1; g x) ≤ Ex_max f' m →
  Ex_max f (x ← Is2; g x) ≤ Ex_max f' m →
  Ex_max f (x ← pidist_plus p Hpf Is1 Is2; g x) ≤ Ex_max f' m.
Proof. intros. setoid_rewrite pidist_plus_bind. apply Ex_max_pidist_plus_le_l; eauto. Qed.

Lemma Ex_max_pidist_plus_bind_le_r {A Y X} f f' p Hpf (Is1 Is2: pidist A) (m: pidist Y)
      (g: A → pidist X):
  Ex_max f m ≤ Ex_max f' (x ← Is1; g x) →
  Ex_max f m ≤ Ex_max f' (x ← Is2; g x) →
  Ex_max f m ≤ Ex_max f' (x ← pidist_plus p Hpf Is1 Is2; g x).
Proof. intros. setoid_rewrite pidist_plus_bind. apply Ex_max_pidist_plus_le_r; eauto. Qed.

Lemma Ex_max_pidist_plus_bind_le_compat {A A' X X'} f g p Hpf
      (Is1 Is2: pidist A) (Is1' Is2': pidist A') (h: A → pidist X) (h': A' → pidist X'):
  Ex_max f (x ← Is1; h x) ≤ Ex_max g (x ← Is1'; h' x)  →
  Ex_max f (x ← Is2; h x) ≤ Ex_max g (x ← Is2'; h' x)  →
  Ex_max f (x ← pidist_plus p Hpf Is1 Is2; h x) ≤
  Ex_max g (x ← pidist_plus p Hpf Is1' Is2'; h' x).
Proof. intros. setoid_rewrite pidist_plus_bind. apply Ex_max_pidist_plus_le_compat; eauto. Qed.
*)

Lemma Ex_max_bind_post {X Y} f (h: X → pidist Y) (Is: pidist X):
  is_finite (Ex_max (λ x, Ex_max f (h x)) Is) →
  (∀ x, is_finite (Ex_max f (h x))) →
  ex_Ex_extrema f (x ← Is; h x) →
  ex_Ex_extrema (λ x, Ex_max f (h x)) Is →
  Ex_max f (x ← Is; h x) = Ex_max (λ x, Ex_max f (h x)) Is.
Proof.
  intros Hfin Hfin_all Hex1 Hex2.
  rewrite ?Ex_max_neg_min.
  f_equal. rewrite Ex_min_bind_post.
  { eapply Ex_min_eq_ext. intros x.
    rewrite Ex_max_neg_min //=. destruct (Ex_min _ _) => //=; nra.
  }
  { setoid_rewrite <-Rbar_opp_involutive at 2.
    setoid_rewrite <-Ex_max_neg_min.
    setoid_rewrite Rbar_opp_real.
    setoid_rewrite <-Rbar_opp_involutive at 1.
    setoid_rewrite <-Ex_max_neg_min.
    rewrite -Hfin //=.
  }
  { intros. by apply is_finite_Ex_max_to_min.  }
  { intros. apply ex_Ex_extrema_negate; auto. }
  { intros. eapply ex_Ex_extrema_negate in Hex2.
    eapply ex_Ex_extrema_proper'; last eassumption; try reflexivity.
    intros => //=. rewrite -(Hfin_all x). rewrite Ex_max_neg_min //= Rbar_opp_real //=.
    rewrite Ropp_involutive //=.
  }
Qed.
    
Lemma Ex_max_bounded_supp_fun_finite {X} f (Is: pidist X):
  bounded_fun_on f (λ x, In_psupport x Is) →
  is_finite (Ex_max f Is).
Proof.
  intros Hbounded.
  rewrite Ex_max_neg_min. rewrite -Ex_min_bounded_supp_fun_finite //=.
  destruct Hbounded as (c&Hb).
  exists c. intros. rewrite Rabs_Ropp. eauto.
Qed.

Lemma Ex_max_singleton {X} f (I: ivdist X):
  ex_Ex_ival f I →
  Ex_max f (singleton I) = Ex_ival f I.
Proof.
  intros.
  apply is_lub_Rbar_unique.
  split.
  * intros r (I'&Hin&His).
    rewrite Hin. rewrite (is_Ex_ival_unique _ _ _ His). done.
  * intros b Hlb. apply Hlb.
    exists I; split; auto.
    ** done.
    ** apply Ex_ival_correct; auto.
Qed.

Definition Pr {X} (A: X → Prop) (Is: ivdist X): R :=
  Ex_ival (λ x, if ClassicalEpsilon.excluded_middle_informative (A x) then 1 else 0) Is.
Definition Pr_max {X} (A: X → Prop) (Is: pidist X): Rbar :=
  Ex_max (λ x, if ClassicalEpsilon.excluded_middle_informative (A x) then 1 else 0) Is.
Definition Pr_min {X} (A: X → Prop) (Is: pidist X): Rbar :=
  Ex_min (λ x, if ClassicalEpsilon.excluded_middle_informative (A x) then 1 else 0) Is.

Lemma Pr_isupp_bounded {X} (A: X → Prop) (Is: ivdist X):
  bounded_fun_on (λ x, if ClassicalEpsilon.excluded_middle_informative (A x) then 1 else 0)
                 (In_isupport^~ Is).
Proof.
  exists 1. intros. destruct (is_left); rewrite Rabs_right; nra.
Qed.

Lemma Pr_psupp_bounded {X} (A: X → Prop) (Is: pidist X):
  bounded_fun_on (λ x, if ClassicalEpsilon.excluded_middle_informative (A x) then 1 else 0)
                 (In_psupport^~ Is).
Proof.
  exists 1. intros. destruct (is_left); rewrite Rabs_right; nra.
Qed.

Hint Resolve Pr_psupp_bounded Pr_isupp_bounded.

Lemma ex_Pr {X} (A: X → Prop) (Is: ivdist X): 
  ex_Ex_ival (λ x, if ClassicalEpsilon.excluded_middle_informative (A x) then 1 else 0) Is.
Proof. apply ex_Ex_ivd_bounded_supp_fun; auto. Qed.

Lemma Pr_max_fin {X} (A: X → Prop) Is :
  is_finite (Pr_max A Is).
Proof. apply Ex_max_bounded_supp_fun_finite; auto. Qed.

Lemma Pr_min_fin {X} (A: X → Prop) Is :
  is_finite (Pr_min A Is).
Proof. apply Ex_min_bounded_supp_fun_finite; auto. Qed.