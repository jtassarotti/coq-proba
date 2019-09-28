Require ClassicalEpsilon.
Require Import Reals Psatz.
From stdpp Require Import tactics.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice bigop.
From discprob.basic Require Import base sval order monad bigop_ext nify.
From discprob.idxval Require Import pival_dist pival ival_dist ival ival_pair pidist_singleton idist_pidist_pair extrema.
From discprob.prob Require Import prob countable finite stochastic_order.

Import Lub.

(* This is an inductive characterization of eq_ivd_prob, as is proved later *)
Inductive irrel_ivd : ∀ X, ivdist X → ivdist X → Prop :=
  | irrel_ivd_refl X : ∀ (I: ivdist X), irrel_ivd X I I
  | irrel_ivd_sym X : ∀ I1 I2, irrel_ivd X I1 I2 → irrel_ivd X I2 I1
  | irrel_ivd_trans X : ∀ I1 I2 I3, irrel_ivd X I1 I2 → irrel_ivd X I2 I3 → irrel_ivd X I1 I3
  | irrel_ivd_proper X :
      ∀ I1 I1' I2 I2', eq_ivd I1 I1' → eq_ivd I2 I2' → irrel_ivd X I1 I2 → irrel_ivd X I1' I2'
  | irrel_ivd_irrel X : ∀ {Y} I1 (I0: ivdist Y), irrel_ivd X I1 (x ← I0; I1)
  | irrel_ivd_bind X Y: ∀ (I1 I2: ivdist X) (f1 f2: X → ivdist Y),
      irrel_ivd X I1 I2 →
      (∀ x, irrel_ivd Y (f1 x) (f2 x)) →
      irrel_ivd Y (x ← I1; f1 x) (x ← I2; f2 x).

Arguments irrel_ivd {_}.

Definition le_pidist_irrel :=
  λ {X : Type} (Is1 Is2 : pidist X), ∀ I : ivdist X, In (I: ival X) Is1 → ∃ I' : ivdist X, irrel_ivd I I' ∧ In (I': ival X) Is2.

Lemma le_pidist_irrel_refl {X: Type} (Is1: pidist X):
  le_pidist_irrel Is1 Is1.
Proof.
  intros I Hin. exists I; split; eauto. apply irrel_ivd_refl.
Qed.

Lemma irrel_ivd_support_coerce {X} (I1 I2: ivdist X) :
  irrel_ivd I1 I2 →
  ∀ x, (∃ i2, ind I2 i2 = x ∧ val I2 i2 > 0) ↔ (∃ i1, ind I1 i1 = x ∧ val I1 i1 > 0).
Proof.
  induction 1.
  - split; intros; auto. 
  - intros. by rewrite (IHirrel_ivd x).
  - intros. by rewrite (IHirrel_ivd2 x).
  - intros.
    rewrite (eq_ival_support_coerce I1 I1'); eauto.
    rewrite (eq_ival_support_coerce I2 I2'); eauto.
  - intros.
    * split.
      ** intros ((i0&i1)&Heq&Hgt). exists i1.
         rewrite //= in Heq Hgt.
         split; auto. specialize (val_nonneg I0 i0); nra.
      ** intros (i1&Heq&Hgt).
         edestruct (ivd_support_idx I0) as (i0&Hgt').
         exists (existT i0 i1); split => //=; nra.
  - intros x. split.
    * intros ((i2&if2)&Hind&Hval).
      rewrite //= in Hind.
      edestruct (IHirrel_ivd (ind I2 i2)) as (HI2&_).
      edestruct (HI2) as (i1&Hindeq&?).
      { eexists.  split; eauto. rewrite //= in Hval. specialize (val_nonneg (f2 (ind I2 i2)) if2).
        nra. }
      edestruct (H1 (ind I2 i2)) as (Hf2&_).
      edestruct Hf2 as (if1&?&?).
      { eexists.  split; eauto. rewrite //= in Hval.
        specialize (val_nonneg I2 i2); nra. }
      unshelve (eexists).
      { exists i1. rewrite Hindeq; exact if1.  }
      split => //=; destruct Hindeq.
      ** rewrite /eq_rect_r//=.
      ** rewrite /eq_rect_r//=. nra.
    * intros ((i2&if2)&Hind&Hval).
      rewrite //= in Hind.
      edestruct (IHirrel_ivd (ind I1 i2)) as (_&HI2).
      edestruct (HI2) as (i1&Hindeq&?).
      { eexists.  split; eauto. rewrite //= in Hval. specialize (val_nonneg (f1 (ind I1 i2)) if2).
        nra. }
      edestruct (H1 (ind I1 i2)) as (_&Hf2).
      edestruct Hf2 as (if1&?&?).
      { eexists.  split; eauto. rewrite //= in Hval.
        specialize (val_nonneg I1 i2); nra. }
      unshelve (eexists).
      { exists i1. rewrite Hindeq; exact if1.  }
      split => //=; destruct Hindeq.
      ** rewrite /eq_rect_r//=.
      ** rewrite /eq_rect_r//=. nra.
Qed.

Lemma le_pidist_irrel_support_coerce_aux {X} (Is1 Is2: pidist X) :
  le_pidist_irrel Is2 Is1 →
  ∀ x, In_psupport x Is2 → In_psupport x Is1.
Proof.
  intros Hle x (I2&i2&Hin2&?&Hval).
  destruct (Hle {| ivd_ival := I2; val_sum1 := all_sum1 Is2 _ Hin2|}) as (I1&Heq&Hin1); eauto.
  exists I1. edestruct (irrel_ivd_support_coerce _ _ Heq) as (i1&?&?).
  { eauto. }
  eexists; split; eauto. 
Qed.

Global Instance irrel_ivd_proper_instance : Proper (@eq_ivd X ==> @eq_ivd X ==> iff) (@irrel_ivd X).
Proof.
  intros ? I1 I1' Heq1 I2 I2' Heq2.
  split; intros; eapply irrel_ivd_proper; eauto; try by symmetry.
Qed.

Global Instance irrel_ivd_Transitivite {X}: Transitive (@irrel_ivd X).
Proof. intros ???. apply irrel_ivd_trans. Qed.
Global Instance irrel_ivd_Reflexive {X}: Reflexive (@irrel_ivd X).
Proof. intros ?. apply irrel_ivd_refl. Qed.
Global Instance irrel_ivd_Symmetry {X}: Symmetric (@irrel_ivd X).
Proof. intros ??. apply irrel_ivd_sym. Qed.

Lemma is_Ex_ival_irrel_proper_bind {X Y} f (f1 f2: X → ivdist Y) (I1 I2: ivdist X) v
      (Hirrel_ivd : irrel_ivd I1 I2)
      (Hall_irrel : ∀ x : X, irrel_ivd (f1 x) (f2 x))
      (IHinner : ∀ (x : X) (f : Y → R) (v : R), is_Ex_ival f (f1 x) v ↔ is_Ex_ival f (f2 x) v)
      (IHirrel_ivd : ∀ (f : X → R) (v : R), is_Ex_ival f I1 v ↔ is_Ex_ival f I2 v):
  is_Ex_ival f (ivd_bind _ _ f1 I1) v → is_Ex_ival f (ivd_bind _ _ f2 I2) v.
Proof.
  intros His.
  assert (ex_Ex_ival f (ivd_bind _ _ f1 I1)).
  { eapply is_Ex_ival_ex; eauto. }
  rewrite -(is_Ex_ival_unique _ _ _ His).
  feed pose proof (ex_Ex_ival_bind_post (λ x, Rabs (f x)) I1 f1) as Hex_I1.
  { eapply ex_Ex_ival_to_Rabs, is_Ex_ival_ex. eauto. }
  feed pose proof (ex_Ex_ival_bind_post f I1 f1) as Hex_I1'.
  { eapply is_Ex_ival_ex. eauto. }
  rewrite Ex_ival_bind_post //=.
  assert (ex_Ex_ival f (ivd_bind _ _ f2 I2)).
  { 
    apply ex_Ex_ival_from_Rabs, ex_Ex_ival_bind_post_inv; eauto using Rabs_pos, Rle_ge.
    ** intros.
       apply is_Ex_ival_ex, ex_Ex_ival_to_Rabs in His.
       edestruct (irrel_ivd_support_coerce I1 I2) as (Hlr&Hrl); eauto.
       edestruct Hlr as (i1&Heqi1&Hvali1); eauto.
       eapply ex_Ex_ival_bind_inv in His; eauto.
       eapply ex_Ex_ival_is in His as (v'&His).
       rewrite -Heqi1.
       eapply is_Ex_ival_ex. eapply IHinner; eauto.
    ** apply ex_Ex_ival_is in Hex_I1 as (v'&His').
       eapply is_Ex_ival_ex; eapply IHirrel_ivd.
       eapply is_Ex_ival_proper_fun_support; eauto.
       intros x Hsupport => //=.
       symmetry.
       apply is_Ex_ival_unique.
       eapply IHinner.
       eapply Ex_ival_correct. eapply (ex_Ex_ival_bind_inv (λ x, Rabs (f x)) f1 I1); eauto.
       apply ex_Ex_ival_to_Rabs. eapply is_Ex_ival_ex; eauto.
  }
  cut (Ex_ival f (ivd_bind _ _ f2 I2) = (Ex_ival (λ x, Ex_ival f (f1 x)) I1)).
  { intros HEx. rewrite -HEx. apply Ex_ival_correct; eauto. }
  rewrite Ex_ival_bind_post //=.
  apply is_Ex_ival_unique.
  eapply IHirrel_ivd.
  eapply is_Ex_ival_proper_fun_support; last first.
  { eapply Ex_ival_correct. eauto. }
  intros => //=.
  symmetry.
  apply is_Ex_ival_unique.
  eapply IHinner.
  eapply Ex_ival_correct. eapply (ex_Ex_ival_bind_inv f f1 I1); eauto.
Qed.

Lemma is_Ex_ival_irrel_proper {A} f (I I': ivdist A) v :
  irrel_ivd I I' →
  is_Ex_ival f I v ↔
  is_Ex_ival f I' v.
Proof.
  intros irrel_ivd.
  revert v.
  induction irrel_ivd; auto; intros.
  - symmetry.  eapply IHirrel_ivd.
  - rewrite IHirrel_ivd1. auto.
  - rewrite /eq_ivd in H.
    etransitivity; first etransitivity; try eapply IHirrel_ivd.
    { split; apply is_Ex_ival_proper; eauto. by symmetry. }
    { split; apply is_Ex_ival_proper; eauto. by symmetry. }
  - split. apply is_Ex_ival_bind_irrel, val_sum1.
    intros His. cut (ex_Ex_ival f I1).  
    { intros Hex. apply Ex_ival_correct in Hex.
      cut (Ex_ival f I1 = v); intros; subst; eauto.
      eapply is_Ex_ival_unique'; last eassumption.
      apply is_Ex_ivd_bind_irrel; eauto.
    }
    apply is_Ex_ival_ex in His.
    unshelve (eapply ex_Ex_ival_bind_inv in His; eauto).
    { exact (sval (ivd_support_idx I0)). }
    destruct (ivd_support_idx _) => //=.
  - split; eapply is_Ex_ival_irrel_proper_bind; eauto; try (intros; by symmetry).
Qed.

Lemma ex_Ex_ival_irrel_proper {A} f (I I': ivdist A) :
  irrel_ivd I I' →
  ex_Ex_ival f I →
  ex_Ex_ival f I'.
Proof.
  intros Hirrel (v&His)%ex_Ex_ival_is.
  eapply is_Ex_ival_ex.
  eapply is_Ex_ival_irrel_proper; eauto.
    by symmetry.
Qed.


Lemma Ex_ival_irrel_proper {A} f (I I': ivdist A) :
  irrel_ivd I I' →
  ex_Ex_ival f I →
  Ex_ival f I = Ex_ival f I'.
Proof.
  intros. symmetry. apply is_Ex_ival_unique.
  eapply is_Ex_ival_irrel_proper; eauto.
  * symmetry. eauto.
  * apply Ex_ival_correct; eauto.
Qed.

Lemma irrel_ivd_to_eq_ivd_prob {X} (I1 I2: ivdist X):
  irrel_ivd I1 I2 →
  eq_ivd_prob I1 I2.
Proof.
  intros Hirrel.
  apply eq_ivd_prob_alt.
  intros x.
  transitivity ((Pr (λ v, v = x) I1)).
  { rewrite /Ex_ival/idx_eq_ind//=. eapply SeriesC_ext; intros.
    destruct ClassicalEpsilon.excluded_middle_informative => //=; nra.
  }
  transitivity ((Pr (λ v, v = x) I2)); last first.
  { rewrite /Ex_ival/idx_eq_ind//=. eapply SeriesC_ext; intros.
    destruct ClassicalEpsilon.excluded_middle_informative => //=; nra.
  }
  apply Ex_ival_irrel_proper; eauto.
  apply ex_Pr.
Qed.

Lemma In_isupport_pr_gt_0 {X: Type} (I: ivdist X) (x: X):
  In_isupport x I →
  0 < Pr (eq ^~ x) I.
Proof.
  rewrite /Pr/Ex_ival => Hin.
  destruct Hin as (i&?&?).
  eapply (Series_strict_pos _ (pickle i)).
  { intros.  rewrite /countable_sum/oapp.
    destruct pickle_inv; try nra.
    destruct ClassicalEpsilon.excluded_middle_informative => //=; try nra.
    rewrite Rmult_1_l. apply val_nonneg.
  }
  { intros.  rewrite /countable_sum/oapp.
    rewrite pickleK_inv. 
    destruct ClassicalEpsilon.excluded_middle_informative => //=; try nra.
  }
  feed pose proof (ex_Pr (eq^~ x) I).
  apply ex_Ex_ival_is in H1 as (v&?).
  rewrite /is_Ex_ival in H1.
  destruct H1 as (Hex&His).
  eexists. eauto.
Qed.

Lemma pr_gt_0_In_isupport {X: Type} (I: ivdist X) (x: X):
  0 < Pr (eq ^~ x) I →
  In_isupport x I.
Proof.
  rewrite /Pr/Ex_ival => Hin.
  eapply (Series_strict_pos_inv) in Hin as (n&?).
  {
   destruct (pickle_inv (idx I) n) as [i|] eqn:Heq.
   - exists i. rewrite  //=/countable_sum//= Heq //= in H.
    destruct ClassicalEpsilon.excluded_middle_informative => //=; try nra.
    * rewrite //= in H. split; eauto. nra.
    * rewrite //= in H. nra.
   - rewrite //=/countable_sum//= Heq //= in H ; nra.
  }
  intros n. rewrite /countable_sum. destruct pickle_inv => //=; last nra.
    destruct ClassicalEpsilon.excluded_middle_informative => //=; try nra.
    rewrite Rmult_1_l. apply val_nonneg.
Qed.

(* This is a kind of conditional distribution *)
Lemma ival_slice_proof1 (X : Type) (I : ivdist X) (x : X):
  ∀ i : idx I, (if ClassicalEpsilon.excluded_middle_informative (In_isupport x I)
                then
                 (if ClassicalEpsilon.excluded_middle_informative (ind I i = x) then val I i else 0) /
                 Pr (eq^~ x) I
                else val I i) ≥ 0.
Proof.
  intros i. 
  destruct ClassicalEpsilon.excluded_middle_informative; eauto; last apply val_nonneg.
  apply Rle_ge, Rdiv_le_0_compat.
  { destruct ClassicalEpsilon.excluded_middle_informative; eauto; try nra. 
    apply Rge_le, val_nonneg. }
  { apply In_isupport_pr_gt_0; eauto. }
Qed.

Definition ival_slice {X} (I: ivdist X) (x: X) : ival X.
  refine {| idx := idx I;
            ind := ind I;
            val := λ i,
                   if ClassicalEpsilon.excluded_middle_informative (In_isupport x I) then
                   (if ClassicalEpsilon.excluded_middle_informative (ind I i = x) then
                          val I i
                        else
                          0) / Pr (λ i, i = x) I
                   else
                     val I i|}.
  apply ival_slice_proof1.
Defined.

Lemma ival_slice_proof2 (X : Type) (I : ivdist X) (x : X):
  is_series (countable_sum (val (ival_slice I x))) 1.
Proof.
  rewrite //=. destruct ClassicalEpsilon.excluded_middle_informative; last apply val_sum1.
  replace 1 with (Pr (eq^~ x) I */ Pr (eq^~ x) I); last first.
  { field. apply Rgt_not_eq, In_isupport_pr_gt_0; auto. }
  apply is_seriesC_scal_r.
  rewrite /Pr/Ex_ival.
  apply (is_seriesC_ext _ (λ i0 : idx I, (if is_left (ClassicalEpsilon.excluded_middle_informative (ind I i0 = x))
                          then 1
                          else 0) * val I i0)).
  { intros.  destruct ClassicalEpsilon.excluded_middle_informative => //=; try nra. }

  {
  feed pose proof (ex_Pr (eq^~ x) I) as Hpr.
  apply ex_Ex_ival_is in Hpr as (v&Hpr).
  rewrite /is_Ex_ival in Hpr.
  destruct Hpr as (Hex&His).
  eapply Series_correct; eexists; eauto. }
Qed.


Definition ivdist_slice {X} (I: ivdist X) (x: X) : ivdist X.
Proof.
  exists (ival_slice I x).
  apply ival_slice_proof2.
Defined.

Lemma eq_ivd_prob_Pr_eq {X} (I1 I2: ivdist X) x:
  eq_ivd_prob I1 I2 →
  Pr (eq^~ x) I1 = Pr (eq^~ x) I2.
Proof. 
  rewrite /Pr/Ex_ival => Heq.
  unshelve (eapply eq_ivd_prob_alt in Heq); first exact x.
  rewrite /idx_eq_ind in Heq.
  setoid_rewrite Rmult_if_distrib.
  setoid_rewrite Rmult_0_l.
  setoid_rewrite Rmult_1_l.
  eauto.
Qed.

Lemma eq_ivd_prob_In_isupport {X: Type} I1 I2 (x: X):
  eq_ivd_prob I1 I2 →
  In_isupport x I1 →
  In_isupport x I2.
Proof.
  intros Heq Hin%In_isupport_pr_gt_0.
  apply pr_gt_0_In_isupport.
  erewrite <-eq_ivd_prob_Pr_eq; last eassumption.
  eauto.
Qed.
      
Lemma eq_ivd_prob_to_irrel_ivd {X} (I1 I2: ivdist X):
  eq_ivd_prob I1 I2 →
  irrel_ivd I1 I2.
Proof.
  intros Heq.
  transitivity (x ← I1; _ ← ivdist_slice I2 x; mret x).
  { transitivity (x ← I1; mret x).
    { rewrite ivd_right_id. reflexivity. } 
    apply irrel_ivd_bind; first reflexivity.
    intros x. apply irrel_ivd_irrel.
  }
  transitivity (x ← I2; _ ← ivdist_slice I1 x; mret x); last first.
  { symmetry.
    transitivity (x ← I2; mret x).
    { rewrite ivd_right_id. reflexivity. } 
    apply irrel_ivd_bind; first reflexivity.
    intros x. apply irrel_ivd_irrel.
  }
  cut (eq_ivd (I1 ≫= (λ x : X, ivdist_slice I2 x ≫= (λ _ : X, mret x)))
    (I2 ≫= (λ x : X, ivdist_slice I1 x ≫= (λ _ : X, mret x)))).
  { intros ->.  reflexivity. }

  apply eq_ival_nondep_inj_surj_suffice.
  apply eq_ival_nondep_inj_surj'_helper.
  unshelve eexists.
  { intros (i1&i2&?). exists i2. exists i1. exact tt. }
  rewrite //=.
  split_and!.
  * intros (i1&i2&[]) (i1'&i2'&[]) _ _ => //=.
    inversion 1; subst. auto.
  * intros (i2&i1&[]). 
    unshelve (eexists).
    { exists i1.  exists i2. exact tt. }
    split_and!; eauto => //=.
    repeat  destruct ClassicalEpsilon.excluded_middle_informative; try nra; try congruence.
    ** intros Hgt. eapply Rge_gt_trans; last  eassumption.
       right. rewrite //=.
       cut (Pr (eq^~ (ind I2 i2)) I1 = Pr (eq^~ (ind I1 i1)) I2).
       { intros ->.  nra. }
       rewrite e0; eapply eq_ivd_prob_Pr_eq; eauto.
    ** intros; exfalso. eapply n. rewrite e.
       eapply eq_ivd_prob_In_isupport; eauto.
    ** intros; exfalso. eapply n. rewrite e.
       eapply eq_ivd_prob_In_isupport; eauto.
       by symmetry.
    ** cut (val I2 i2 = 0).
       { intros ->. nra. }
       destruct (val_nonneg I2 i2); last auto.
       exfalso. eapply n. 
       eapply eq_ivd_prob_In_isupport; eauto.
       { by symmetry. }
       eexists; eauto.
  * intros (i1&i2&[]) => //=.
    repeat  destruct ClassicalEpsilon.excluded_middle_informative; try nra; try congruence.
    cut (val I1 i1 = 0).
    { intros ->.  nra. }
    destruct (val_nonneg I1 i1); last auto.
    exfalso. eapply n. 
    eapply eq_ivd_prob_In_isupport; eauto.
    eexists; eauto.
  * intros (i1&i2&[]) => //=.
    repeat  destruct ClassicalEpsilon.excluded_middle_informative => //=; try nra; try congruence.
    ** intros Hgt.
       cut (Pr (eq^~ (ind I2 i2)) I1 = Pr (eq^~ (ind I1 i1)) I2).
       { intros ->.  nra. }
       rewrite e0; eapply eq_ivd_prob_Pr_eq; eauto.
    ** intros; exfalso. eapply n. rewrite e.
       eapply eq_ivd_prob_In_isupport; eauto.
       by symmetry.
    ** intros; exfalso. eapply n. rewrite e.
       eapply eq_ivd_prob_In_isupport; eauto.
    ** cut (val I1 i1 = 0).
       { intros ->. nra. }
       destruct (val_nonneg I1 i1); last auto.
       exfalso. eapply n. 
       eapply eq_ivd_prob_In_isupport; eauto.
       eexists; eauto.
Qed.

Lemma irrel_ivd_choice {X} (I1 I1' I2 I2': ivdist X) p Hpf Hpf':
      irrel_ivd I1 I2 →
      irrel_ivd I1' I2' →
      irrel_ivd (ivdplus p Hpf I1 I1') (ivdplus p Hpf' I2 I2').
Proof.
  intros Hirrel1 Hirrel2.
  transitivity (b ← ivdplus p Hpf (mret true) (mret false);
                if (b: bool) then I1 else I1').
  { rewrite ivd_plus_bind ?ivd_left_id. reflexivity. }
  transitivity (b ← ivdplus p Hpf' (mret true) (mret false);
                if (b: bool) then I2 else I2'); last first.
  { rewrite ivd_plus_bind ?ivd_left_id. reflexivity. }
  apply irrel_ivd_bind.
  { cut (eq_ivd (ivdplus p Hpf (mret true) (mret false)) (ivdplus p Hpf' (mret true) (mret false))).
    { intros ->; reflexivity. }
    apply ivdist_plus_proper; reflexivity.
  }
  intros [|]; eauto.
Qed.

Definition irrel_pidist {X: Type} (Is1 Is2: pidist X) :=
  ∀ f, bounded_fun f → Rbar_le (Ex_min f Is2) (Ex_min f Is1).

Lemma irrel_pidist_Ex_max {X: Type} (Is1 Is2: pidist X) :
    irrel_pidist Is1 Is2 → ∀ f, bounded_fun f → Rbar_le (Ex_max f Is1) (Ex_max f Is2).
Proof.
  intros Hirrel f Hb.
  rewrite ?Ex_max_neg_min.
  apply Rbar_opp_le.
  apply Hirrel.
  destruct Hb as (c&?).
  exists c => x. rewrite Rabs_Ropp; eauto.
Qed.

Lemma Ex_max_irrel_pidist {X: Type} (Is1 Is2: pidist X) :
  (∀ f, bounded_fun f → Rbar_le (Ex_max f Is1) (Ex_max f Is2)) →
  irrel_pidist Is1 Is2.
Proof.
  intros Hirrel f Hb.
  specialize (Hirrel (λ x, (- f x))).
  rewrite ?Ex_max_neg_min in Hirrel.
  apply Rbar_opp_le.
  setoid_rewrite Ropp_involutive in Hirrel.
  eapply Hirrel. destruct Hb as (c&?). exists c.
  intros x. rewrite Rabs_Ropp; eauto.
Qed.

Lemma irrel_pidist_refl {X} : ∀ I, @irrel_pidist X I I.
Proof. intros f Hb; reflexivity. Qed.

Lemma irrel_pidist_trans {X} :
   ∀ I1 I2 I3, @irrel_pidist X I1 I2 → @irrel_pidist X I2 I3 → @irrel_pidist X I1 I3.
Proof.
  intros I1 I2 I3 Hi1 Hi2 f Hb.
  specialize (Hi1 f Hb). 
  specialize (Hi2 f Hb). 
  etransitivity; eauto.
Qed.

Lemma bounded_supp_fun_le_pidist {A} f (Is Is': pidist A):
  le_pidist Is Is' →
  bounded_fun_on f (λ x, In_psupport x Is') →
  bounded_fun_on f (λ x, In_psupport x Is).
Proof.
  intros Hle Hbf.
  eapply bounded_fun_on_anti; try eassumption.
  intros a. eapply le_pidist_support_coerce_aux; eauto.
Qed.

Lemma Ex_min_le_pidist_irrel {X} (f: X → R) Is1 Is2:
  le_pidist_irrel Is1 Is2 →
  Rbar_le (Ex_min f Is2) (Ex_min f Is1).
Proof.
  intros Hle.
  rewrite /Ex_min.
  destruct (Glb_Rbar_correct (Ex_pidist f Is1)) as (Hlb&Hglb).
  apply Hglb. intros r Hex. destruct Hex as (I&Hin&Hex).
  edestruct (Hle {| ivd_ival := I; val_sum1 := all_sum1 Is1 _ Hin |}) as (I2&Heq&Hin2).
  { rewrite //=. }
  { eapply (is_Ex_ival_irrel_proper f) in Heq; last eauto.
    destruct (Glb_Rbar_correct (Ex_pidist f Is2)) as (Hlb2&Hglb2).
    eapply Hlb2. eexists; split; eauto.
    eapply Heq => //=.
  }
Qed.

Lemma Ex_max_le_pidist_irrel {X} (f: X → R) Is1 Is2:
  le_pidist_irrel Is1 Is2 →
  Rbar_le (Ex_max f Is1) (Ex_max f Is2).
Proof.
  rewrite ?Ex_max_neg_min.
  intros Hle.
  apply Rbar_opp_le.
  apply Ex_min_le_pidist_irrel; eauto.
Qed.

Lemma irrel_pidist_proper_irrel {X} :
  ∀ I1 I1' I2 I2', le_pidist_irrel I1' I1 → le_pidist_irrel I2 I2' →
                   @irrel_pidist X I1 I2 → @irrel_pidist X I1' I2'.
Proof.
  intros I1 I1' I2 I2' Hle1 Hle2 Hirrel12.
  intros f Hb.
  etransitivity.
  { apply Ex_min_le_pidist_irrel; eauto. }
  etransitivity.
  { eapply Hirrel12; eauto. } 
  { apply Ex_min_le_pidist_irrel; eauto. }
Qed.

Lemma irrel_pidist_bind1 {X Y}: ∀ (I1 I2: pidist X) (f: X → pidist Y),
      @irrel_pidist X I1 I2 →
      @irrel_pidist Y (x ← I1; f x) (x ← I2; f x).
Proof.
  intros I1 I2 f Hirrel.
  intros g Hb.
  rewrite ?Ex_min_bind_post;
    eauto using Ex_min_bounded_is_bounded, ex_Ex_extrema_bounded_fun,
    Ex_min_bounded_fun_finite.
Qed.

Lemma irrel_pidist_bind {X Y}: ∀ (I1 I2: pidist X) (f1 f2: X → pidist Y),
      @irrel_pidist X I1 I2 →
      (∀ x, @irrel_pidist Y (f1 x) (f2 x)) →
      @irrel_pidist Y (x ← I1; f1 x) (x ← I2; f2 x).
Proof.
  intros I1 I2 f1 f2 Hirrel Hirrelfun.
  eapply irrel_pidist_trans.
  { eapply irrel_pidist_bind1; eauto. }
  intros f Hb. eapply Ex_min_bind_le;
    eauto using Ex_min_bounded_is_bounded, ex_Ex_extrema_bounded_fun,
    Ex_min_bounded_fun_finite.
  intros a ?. eapply Hirrelfun; eauto.
Qed.

Lemma irrel_pidist_proper X :
  ∀ (I1 I1' I2 I2': pidist X), le_pidist I1' I1 → le_pidist I2 I2'
                               → irrel_pidist I1 I2 → irrel_pidist I1' I2'.
Proof.
  intros ???? Hle1 Hle2. eapply irrel_pidist_proper_irrel.
  { intros x Hin. edestruct (Hle1 x) as (x'&Heq&Hin'); eauto.
    exists {| ivd_ival := x'; val_sum1 := all_sum1 I1 _ Hin'|}; split; auto.
    eapply irrel_ivd_proper; eauto; last apply irrel_ivd_refl.
    reflexivity.
  }
  { intros x Hin. edestruct (Hle2 x) as (x'&Heq&Hin'); eauto.
    exists {| ivd_ival := x'; val_sum1 := all_sum1 I2' _ Hin'|}; split; auto.
    eapply irrel_ivd_proper; eauto; last apply irrel_ivd_refl.
    reflexivity.
  }
Qed.

Global Instance irrel_pidist_mono_instance : Proper (@le_pidist X --> @le_pidist X ==> Coq.Program.Basics.impl) (@irrel_pidist X).
Proof.
  intros X I1 I1' Heq1 I2 I2' Heq2.
  intros Hirrel. eapply irrel_pidist_proper; eauto.
Qed.

Global Instance irrel_pidist_proper_instance : Proper (@eq_pidist X ==> @eq_pidist X ==> iff) (@irrel_pidist X).
Proof.
  intros X I1 I1' Heq1 I2 I2' Heq2.
  split; intros Hirrel; eapply irrel_pidist_proper; eauto;
    try (setoid_rewrite Heq1; reflexivity);
    try (setoid_rewrite Heq2; reflexivity).
Qed.

Global Instance irrel_pidist_Transitivite {X}: Transitive (@irrel_pidist X).
Proof. intros ???. apply irrel_pidist_trans. Qed.
Global Instance irrel_pidist_Reflexive {X}: Reflexive (@irrel_pidist X).
Proof. intros ?. apply irrel_pidist_refl. Qed.



Record irrel_couplingP {A1 A2} (I1: ivdist A1) (Is2: pidist A2) (P: A1 → A2 → Prop) : Type :=
  { irrel_I : ivdist A1;
    irrel_Is : pidist A2;
    irrel_rel_I : irrel_ivd I1 irrel_I;
    irrel_rel_Is : irrel_pidist irrel_Is Is2;
    irrel_couple_wit :> idist_pidist_couplingP irrel_I irrel_Is P
  }.

Definition lsupport {A1 A2 Is1 Is2 P} (Icouple: irrel_couplingP Is1 Is2 P) (y: A2) :=
  { x : A1 |  ∃ i Hpf, ival.ind Icouple i = (exist _ (x, y) Hpf) ∧ ival.val Icouple i > 0 }.
Definition rsupport {A1 A2 Is1 Is2 P} (Icouple: irrel_couplingP Is1 Is2 P) (x: A1) :=
  { y : A2 |  ∃ i Hpf, ival.ind Icouple i = (exist _ (x, y) Hpf) ∧ ival.val Icouple i > 0 }.


Definition irrel_coupling_propP {A1 A2} (I1: ivdist A1) (Is2: pidist A2) P : Prop :=
  ∃ (ic: irrel_couplingP I1 Is2 P), True.

Lemma ic_wit_to_prop {A1 A2} (I1 : ivdist A1) (Is2: pidist A2) P :
  irrel_couplingP I1 Is2 P →
  irrel_coupling_propP I1 Is2 P.
Proof.
  intros; eexists; eauto.
Qed.

Lemma ic_prop_to_wit {A1 A2} (I1 : ivdist A1) (Is2: pidist A2) P :
  irrel_coupling_propP I1 Is2 P →
  irrel_couplingP I1 Is2 P.
Proof.
  intros (?&_)%ClassicalEpsilon.constructive_indefinite_description; auto.
Qed.
  
Lemma irrel_pidist_support_coerce {X} (I1 I2: pidist X) :
  irrel_pidist I2 I1 →
  ∀ x, In_psupport x I2 → In_psupport x I1. 
Proof.
  intros Hirrel x Hin.
  destruct Hin as (I&i&Hin&Hind&Hval).
  assert (0 < Pr (eq ^~ x) {| ivd_ival := I; val_sum1 := all_sum1 _ _ Hin|}).
  {  eapply In_isupport_pr_gt_0.
     eexists; eauto. }
  assert (Rbar_lt 0 (Pr_max (eq^~ x) I1)) as Hmax.
  { 
    apply (Rbar_lt_le_trans _ (Pr_max (eq^~ x) I2)); last first.
    { eapply irrel_pidist_Ex_max; eauto.
      exists 1. intros. destruct (is_left); rewrite Rabs_right; nra.
    }
    apply (Rbar_lt_le_trans _ (Pr (eq^~ x) {| ivd_ival := I; val_sum1 := all_sum1 I2 I Hin |}));
      first done.
    apply Ex_max_spec1' => //=.
    eapply (ex_Pr (eq^~x) {| ivd_ival := I; val_sum1 := all_sum1 I2 I Hin |}).
  }
  assert (∃ I' : ivdist X, In (I': ival X) I1 ∧ 0 < Pr (eq^~x) I') as (I'&Hin'&Hpr').
  {
    apply Classical_Pred_Type.not_all_not_ex. intros Hneg.
    apply Rbar_lt_not_le in Hmax. apply Hmax.
    apply Ex_max_spec2.
    intros r' (I'&Hin'&Heq).
    apply Rbar_not_lt_le. intros Hlt.
    exfalso; eapply (Hneg {| ivd_ival := I'; val_sum1 := all_sum1 _ _ Hin'|}).
    split; first done.
    rewrite /Pr. erewrite is_Ex_ival_unique; last eassumption.
    auto.
  }
  exists I'. apply pr_gt_0_In_isupport in Hpr'.
  destruct Hpr' as (?&?&?). eexists; split_and!; eauto.
Qed.
    
Lemma irrel_pidist_choice {X} (I1 I1' I2 I2': pidist X) p Hpf Hpf':
      irrel_pidist I1 I2 →
      irrel_pidist I1' I2' →
      irrel_pidist (pidist_plus p Hpf I1 I1') (pidist_plus p Hpf' I2 I2').
Proof.
  intros Hirrel1 Hirrel2.
  transitivity (b ← pidist_plus p Hpf (mret true) (mret false);
                if (b: bool) then I1 else I1').
  { rewrite pidist_plus_bind ?pidist_left_id. reflexivity. }
  transitivity (b ← pidist_plus p Hpf' (mret true) (mret false);
                if (b: bool) then I2 else I2'); last first.
  { rewrite pidist_plus_bind ?pidist_left_id. reflexivity. }
  apply irrel_pidist_bind.
  { cut (eq_pidist (pidist_plus p Hpf (mret true) (mret false))
                   (pidist_plus p Hpf' (mret true) (mret false))).
    { intros ->; reflexivity. }
    apply pidist_plus_proper; reflexivity.
  }
  intros [|]; eauto.
Qed.

Lemma irrel_pidist_irrel {X Y}: ∀ I1 (I0: pidist Y), @irrel_pidist X (x ← I0; I1) I1.
Proof.
  intros. intros f Hbounded.
  rewrite Ex_min_bind_irrel //=; try reflexivity;
    eauto using Ex_min_bounded_is_bounded, ex_Ex_extrema_bounded_fun,
    Ex_min_bounded_fun_finite.
Qed.

Lemma irrel_coupling_proper {A1 A2} (I1 I2 : ivdist A1) (Is1 Is2: pidist A2) P:
  eq_ivd I1 I2 → 
  eq_pidist Is1 Is2 → 
  irrel_couplingP I1 Is1 P → 
  irrel_couplingP I2 Is2 P.
Proof.
  intros HeqI HeqIs [I1' Is1' HeqI1 HeqIs1 Hcouple].
  exists I1' Is1'.
  - setoid_rewrite <-HeqI. done.
  - setoid_rewrite <-HeqIs. done.
  - done.
Qed.

Lemma irrel_coupling_mono {A1 A2} (I1 I2 : ivdist A1) (Is1 Is2: pidist A2) P:
  eq_ivd I1 I2 → 
  le_pidist Is1 Is2 → 
  irrel_couplingP I1 Is1 P → 
  irrel_couplingP I2 Is2 P.
Proof.
  intros HeqI HeqIs [I1' Is1' HeqI1 HeqIs1 Hcouple].
  exists I1' Is1'.
  - setoid_rewrite <-HeqI. done.
  - setoid_rewrite <-HeqIs. done.
  - done.
Qed.

Lemma irrel_coupling_mono_irrel {A1 A2} (I1 I2 : ivdist A1) (Is1 Is2: pidist A2) P:
  eq_ivd I1 I2 → 
  irrel_pidist Is1 Is2 → 
  irrel_couplingP I1 Is1 P → 
  irrel_couplingP I2 Is2 P.
Proof.
  intros HeqI HeqIs [I1' Is1' HeqI1 HeqIs1 Hcouple].
  exists I1' Is1'.
  - setoid_rewrite <-HeqI. done.
  - setoid_rewrite <-HeqIs. done.
  - done.
Qed.

Lemma irrel_coupling_mono_irrel' {A1 A2} (I1 I2 : ivdist A1) (Is1 Is2: pidist A2) P:
  irrel_ivd I1 I2 → 
  irrel_pidist Is1 Is2 → 
  irrel_couplingP I1 Is1 P → 
  irrel_couplingP I2 Is2 P.
Proof.
  intros HeqI HeqIs [I1' Is1' HeqI1 HeqIs1 Hcouple].
  exists I1' Is1'.
  - setoid_rewrite <-HeqI. done.
  - setoid_rewrite <-HeqIs. done.
  - done.
Qed.

Global Instance irrel_coupling_prop_Proper {A1 A2}:
  Proper (@eq_ivd A1 ==> @le_pidist A2 ==> eq ==> impl) irrel_coupling_propP.
Proof.
  intros ?? Heq ?? Hle ?? ->. 
  intros H%ic_prop_to_wit.
  apply ic_wit_to_prop.
  eapply irrel_coupling_mono; eauto.
Qed.

Global Instance irrel_coupling_prop_irrel_Proper {A1 A2}:
  Proper (@eq_ivd A1 ==> @irrel_pidist A2 ==> eq ==> impl) irrel_coupling_propP.
Proof.
  intros ?? Heq ?? Hle ?? ->. 
  intros H%ic_prop_to_wit.
  apply ic_wit_to_prop.
  eapply irrel_coupling_mono_irrel; eauto.
Qed.

Lemma irrel_coupling_mret {A1 A2} (P: A1 → A2 → Prop) x y:
  P x y →
  irrel_couplingP (mret x) (mret y) P.
Proof.
  intros HP. exists (mret x) (mret y); try reflexivity.
  by apply ip_coupling_mret.
Qed.

Lemma irrel_coupling_prop_mret {A1 A2} (P: A1 → A2 → Prop) x y:
  P x y →
  irrel_coupling_propP (mret x) (mret y) P.
Proof.
  intros; apply ic_wit_to_prop, irrel_coupling_mret; auto.
Qed.
  
Lemma irrel_coupling_bind {A1 A2 B1 B2} P (f1: A1 → ivdist B1) (f2: A2 → pidist B2)
      I1 Is2 Q (Ic: irrel_couplingP I1 Is2 P):
  (∀ x y, P x y → irrel_couplingP (f1 x) (f2 y) Q) →
  irrel_couplingP (mbind f1 I1) (mbind f2 Is2) Q.
Proof.
  intros Hfc.
  destruct Ic as [I1' Is2' HeqI HeqIs Hcouple].
  destruct Hcouple as [I2' ? [Ic ? ?]%ic_coupling_to_id].
  unshelve (eexists).
  - refine (xy ← Ic; _).
     destruct xy as ((x&y)&HP).
     destruct (Hfc _ _ HP).
     exact irrel_I0.
  - refine (xy ← singleton Ic; _).
    destruct xy as ((x&y)&HP).
    destruct (Hfc x y HP).
    exact irrel_Is0.
  - etransitivity.
    { eapply irrel_ivd_bind.  eauto. reflexivity. }
    etransitivity.
    { eapply irrel_ivd_bind. setoid_rewrite idc_proj1. reflexivity. reflexivity.  }
    setoid_rewrite ivd_assoc. eapply irrel_ivd_bind; first reflexivity.
    intros ((x&y)&HP).
    destruct (Hfc _ _ _) as [? ? ?]. rewrite /irrel_I.
    rewrite /sval.  setoid_rewrite ivd_left_id. done.
  - etransitivity; last first.
    { eapply irrel_pidist_bind.
      - etransitivity; last by eauto. eapply irrel_pidist_proper; first by eauto.
        reflexivity. reflexivity.
      - intros; reflexivity.
    }
    setoid_rewrite idc_proj2. setoid_rewrite singleton_bind.
    setoid_rewrite pidist_assoc.
    eapply irrel_pidist_bind; first reflexivity.
    intros ((x&y)&HP).
    destruct (Hfc _ _ _) as [? ? ?]. rewrite /irrel_I.
    rewrite /sval. setoid_rewrite singleton_mret. setoid_rewrite pidist_left_id.
    eauto.
  - eapply (ip_coupling_bind _ _ _ _ (λ x y, x = y)).
    * apply ip_coupling_singleton.
    * intros ((?&?)&HP1) ((x&y)&HP2).
      inversion 1; subst.
      rewrite //=.
      assert (HP1 = HP2). { apply classical_proof_irrelevance. } 
      subst. 
      destruct (Hfc x y HP2). eauto.
Qed.

Lemma irrel_coupling_prop_bind {A1 A2 B1 B2} P (f1: A1 → ivdist B1) (f2: A2 → pidist B2)
      I1 Is2 Q (Ic: irrel_coupling_propP I1 Is2 P):
  (∀ x y, P x y → irrel_coupling_propP (f1 x) (f2 y) Q) →
  irrel_coupling_propP (mbind f1 I1) (mbind f2 Is2) Q.
Proof.
  intros; eapply ic_wit_to_prop, irrel_coupling_bind; intros; apply ic_prop_to_wit; eauto.
Qed.

Lemma irrel_coupling_trivial {A1 A2} (I: ivdist A1) (Is: pidist A2):
  irrel_couplingP I Is (λ x y, True).
Proof.
  assert ({ I' : ivdist A2 | In (I': ival A2) Is}) as (I'&Hin).
  { destruct Is as [(Is&Hne) Hall] => //=.
    rewrite //= in Hall.
    apply ClassicalEpsilon.constructive_indefinite_description in Hne as (I'&His).
    exists {| ivd_ival := I'; val_sum1 := Hall _ His |}.
    auto.
  }
  exists (x ← I'; I) (singleton (x ← I; I')).
  { eapply irrel_ivd_irrel. }
  { eapply irrel_pidist_proper_irrel; [| apply le_pidist_irrel_refl | reflexivity ].
    intros I0 Hin'. inversion Hin' as [Heq].
    exists I'; split; auto.
    eapply (irrel_ivd_proper _ (x ← I; I')).
    { rewrite /eq_ivd. rewrite -Heq //=. }
    { reflexivity. }
    symmetry. apply irrel_ivd_irrel.
  }
  exists (x ← I; I').
  { intros ?. eapply In_pidist_le_singleton. eexists; split; first reflexivity.
    rewrite /In/singleton//=. }
  unshelve (eexists).
  { refine (ivd_ival (x ← I; y ← I'; mret _)).
    exists (x, y); done. }
  - setoid_rewrite ival_bind_comm. setoid_rewrite ival_assoc.
    eapply ival_bind_congr; first reflexivity.
    intros.  setoid_rewrite ival_bind_mret_mret. setoid_rewrite ival_right_id. reflexivity.
  - setoid_rewrite ival_assoc.
    eapply ival_bind_congr; first reflexivity.
    intros.  setoid_rewrite ival_bind_mret_mret. setoid_rewrite ival_right_id. reflexivity.
Qed.

Lemma irrel_coupling_prop_trivial {A1 A2} (I: ivdist A1) (Is: pidist A2):
  irrel_coupling_propP I Is (λ x y, True).
Proof.
  apply ic_wit_to_prop, irrel_coupling_trivial.
Qed.

Lemma irrel_coupling_conseq {A1 A2} (P1 P2: A1 → A2 → Prop) (I: ivdist A1) (Is: pidist A2):
  (∀ x y, P1 x y → P2 x y) →
  irrel_couplingP I Is P1 →
  irrel_couplingP I Is P2.
Proof.
  intros HP Hirrel.
  destruct Hirrel as [I0 Is0 ? ? ?]. 
  exists I0 Is0; auto.
  eapply ip_coupling_conseq; eauto.
Qed.

Lemma irrel_coupling_plus {A1 A2} p Hpf p' Hpf'
      (P : A1 → A2 → Prop) (Is1 Is1': ivdist A1) (Is2 Is2': pidist A2) :
  p = p' →
  irrel_couplingP Is1 Is2 P →
  irrel_couplingP Is1' Is2' P →
  irrel_couplingP (ivdplus p Hpf Is1 Is1') (pidist_plus p' Hpf' Is2 Is2') P.
Proof.
  intros Hpeq Hic Hic'. subst.
  destruct Hic as [I1i Is2i Hirrel1i Hirrel2i Hwit].
  destruct Hic' as [I1i' Is2i' Hirrel1i' Hirrel2i' Hwit'].
  exists (ivdplus p' Hpf I1i I1i') (pidist_plus p' Hpf' Is2i Is2i').
  { eapply irrel_ivd_choice; eauto. }
  { eapply irrel_pidist_choice; eauto. }
  apply ip_coupling_plus; eauto.
Qed.

Lemma irrel_coupling_bind_condition {A1 B1 B2} (f1: A1 → ivdist B1) (f2: A1 → pidist B2)
      I Is Q x:
  (le_pidist (singleton I) Is ) →
  (irrel_couplingP (f1 x) (f2 x) Q) →
  irrel_couplingP (x ← I; y ← f1 x; mret (x, y))
                  (x ← Is; y ← f2 x; mret (x, y)) 
                  (λ xy1 xy2, fst xy1 = x → fst xy2 = x → Q (snd xy1) (snd xy2)).
Proof.
  intros Hle Hc.
  eapply (irrel_coupling_bind (λ x y, x = y)).
  { exists I Is; try reflexivity.
    exists I; eauto. apply ival_coupling_refl.
  }
  intros ? y ?; subst.
  destruct (ClassicalEpsilon.excluded_middle_informative (x = y)).
  - intros; subst. eapply irrel_coupling_bind; eauto.
    intros. apply irrel_coupling_mret => ? //=. 
  - intros. eapply irrel_coupling_bind.
    * apply irrel_coupling_trivial. 
    * intros. apply irrel_coupling_mret => ? //=. intros. congruence.
Qed.

Lemma irrel_coupling_support {X Y} I1 I2 (P: X → Y → Prop):
  ∀ (Ic: irrel_couplingP I1 I2 P), 
  irrel_couplingP I1 I2 (λ x y, ∃ Hpf: P x y,  In_isupport x I1 ∧ In_psupport y I2 ∧
                        In_isupport (exist _ (x, y) Hpf) Ic).
Proof.
  intros [? ? Heq1 Heq2 Ic].
  specialize (ip_coupling_support _ _ _ Ic).
  eexists; eauto.
  eapply ip_coupling_conseq; eauto.
  intros x y (Hpf&Hin1&Hin2&?); exists Hpf; repeat split; auto.
  -  edestruct Hin1 as (i&?&?).
     edestruct (irrel_ivd_support_coerce _ _ Heq1) as (Hcoerce&_).
     apply Hcoerce; eauto.
  - eapply irrel_pidist_support_coerce; eauto. 
Qed.

Lemma irrel_coupling_support_wit {X Y} I1 I2 (P: X → Y → Prop):
  ∀ (Ic: irrel_couplingP I1 I2 P), 
    { xy : X * Y | ∃ Hpf : P (fst xy) (snd xy),
        In_isupport (fst xy) I1 ∧ In_psupport (snd xy) I2 ∧ In_isupport (exist _ xy Hpf) Ic }.
Proof.
  intros [? ? Heq1 Heq2 Ic].
  specialize (ip_coupling_support_wit _ _ _ Ic).
  rewrite //=. 
  intros ((x&y)&Hpf).
  exists (x, y).
  destruct Hpf as (Hpf&Hin1&Hin2&?).
  exists Hpf; repeat split; auto.
  -  edestruct Hin1 as (i&?&?).
     edestruct (irrel_ivd_support_coerce _ _ Heq1) as (Hcoerce&_).
     apply Hcoerce; eauto.
  - eapply irrel_pidist_support_coerce; eauto. 
Qed.

Lemma rsupport_support_right {X Y} (Ix: ivdist X) (x: X) Is (P: X → Y → Prop)
      (Ic: irrel_couplingP Ix Is P)  (c: rsupport Ic x) :
  In_psupport (proj1_sig c) Is.
Proof.
  destruct c as (y'&ic&HP&Hind&Hgt).
  rewrite //=. destruct Ic as [Ix' Is' Hirrel_ivd Hirrel_pidist Ic].
  eapply irrel_pidist_support_coerce; eauto.
  destruct Ic as [Iy Hle Ic].
  rewrite //= in ic Hind Hgt.
  clear Hirrel_pidist.

  destruct (irrel_ivd_support_coerce _ _ Hirrel_ivd x) as (Hcoerce&_).
  destruct (Hle Iy) as (Iy'&Heq&Hin); first by auto.
  destruct Ic as [Ic Hproj1 Hproj2].
  rewrite //= in ic Hind Hgt.

  symmetry in Hproj2.
  setoid_rewrite Heq in Hproj2.
  destruct Hproj2 as (h1&h2&?&?&Hindic&Hvalic).


  assert (val (x0 ← Ic; mret (sval x0).2) (existT ic tt) > 0) as Hgt'.
  { rewrite //= Rmult_1_r //=. }
  specialize (Hindic (coerce_supp _ _ Hgt')).
  specialize (Hvalic (coerce_supp _ _ Hgt')).
  rewrite //= in Hindic Hvalic.



  exists Iy'.
  exists (sval (h1 (coerce_supp _ _ Hgt'))).
  repeat split; auto.
  - rewrite Hindic Hind //=.
  - rewrite Hvalic //=.
Qed.

Lemma rsupport_post {X Y} (Ix: ivdist X) (x: X) Is (P: X → Y → Prop)
      (Ic: irrel_couplingP Ix Is P)  (c: rsupport Ic x) :
  P x (proj1_sig c).
Proof.
  destruct c as (y&I&i&Hind&?).
  rewrite //=.
Qed.
  
Transparent pidist_ret.
Lemma rsupport_mret_right {X Y} (Ix: ivdist X) (x: X) (y: Y) (P: X → Y → Prop)
      (Ic: irrel_couplingP Ix (mret y) P)  (c: rsupport Ic x) :
  proj1_sig c = y.
Proof.
  edestruct (rsupport_support_right _ _ _ _ Ic c) as (Iy&iy&Hin&Hind&?).
  subst; rewrite -Hind //=.
  rewrite /In/mret/base.mret//= in Hin.
  subst. destruct iy => //=.
Qed.
Opaque pidist_ret.


Lemma ip_irrel_coupling {A1 A2} (I: ivdist A1) (Is: pidist A2) (P: A1 → A2 → Prop):
  idist_pidist_couplingP I Is P →
  irrel_couplingP I Is P.
Proof.
  intros.
  exists I Is; try reflexivity; eauto.
Qed.


Lemma irrel_bounded_supp_fun {A} f (Is Is': pidist A):
  irrel_pidist Is Is' →
  bounded_fun_on f (λ x, In_psupport x Is') →
  bounded_fun_on f (λ x, In_psupport x Is).
Proof.
  intros Hle Hbf.
  eapply bounded_fun_on_anti; try eassumption.
  eapply irrel_pidist_support_coerce; eauto.
Qed.

Lemma irrel_pidist_bounded_supp_Ex_max {A} f (Is Is': pidist A):
  irrel_pidist Is Is' →
  bounded_fun_on f (λ x, In_psupport x Is') →
  Rbar_le (Ex_max f Is) (Ex_max f Is').
Proof.
  intros Hi Hb1.
  feed pose proof (irrel_bounded_supp_fun f Is Is') as Hb2; eauto.
  assert (bounded_fun_on f (λ x, In_psupport x Is ∨ In_psupport x Is')) as Hb.
  { destruct Hb1 as (c1&?).
    destruct Hb2 as (c2&?).
    exists (Rmax c1 c2).
    intros x [Hin1|Hin2]; rewrite Rmax_Rle; intuition.
  }
  clear Hb1. clear Hb2.
  edestruct (bounded_fun_on_to_bounded f) as (g'&Hb'&Heq); eauto.
  feed pose proof (irrel_pidist_Ex_max Is Is' Hi g' Hb'); eauto.
  erewrite (Ex_max_eq_ext_supp f g' Is'); eauto. 
  etransitivity; eauto.
  erewrite (Ex_max_eq_ext_supp f g' Is); eauto; first reflexivity.
Qed.

Lemma Ex_min_irrel_anti {A} f (Is Is': pidist A) :
  irrel_pidist Is Is' →
  bounded_fun f →
  Rbar_le (Ex_min f Is') (Ex_min f Is).
Proof. eauto. Qed.

Lemma irrel_coupling_eq_ex_Ex {A1 A2} f g (I: ivdist A1) (Is: pidist A2) :
  irrel_couplingP I Is (λ x y, f x = g y) →
  bounded_fun g →
  ex_Ex_ival f I.
Proof.
  intros [Is1_irrel Is2_irrel Hirrel_ivd Hirrel_pidst Ic] Hex.
  assert (idist_pidist_couplingP (x ← Is1_irrel; mret (f x))
                                 (x ← Is2_irrel; mret (g x))
                                 (λ x y, x = y)) as Ic'.
  { eapply ip_coupling_bind; eauto => ???.
    apply ip_coupling_mret; auto. }
                                    
  destruct Ic' as [I2 Hmem Ic'].
  apply ival_coupling_eq in Ic'.
  eapply ex_Ex_ival_irrel_proper.
  { symmetry; eauto. }

  rewrite (ex_Ex_ival_fmap id f).
  setoid_rewrite Ic'.
  cut (ex_Ex_extrema id (x ← Is2_irrel; mret (g x))).
  { intros Hex'. edestruct (Hmem I2) as (I2'&Heq'&?); first done.
    rewrite Heq'. eapply Hex'; eauto. }
  rewrite -ex_Ex_extrema_fmap. eauto.
  eapply ex_Ex_extrema_bounded_fun.
  eauto.
Qed.

Lemma irrel_coupling_eq_Ex_min {A1 A2} f g (I: ivdist A1) (Is: pidist A2) :
  irrel_couplingP I Is (λ x y, f x = g y) →
  bounded_fun g →
  Rbar_le (Ex_min g Is) (Ex_ival f I).
Proof.
  intros Hirrel Hb.
  feed pose proof (irrel_coupling_eq_ex_Ex f g I Is) as Hex; eauto.
  destruct Hirrel as [Is1_irrel Is2_irrel Hirrel_ivd Hirrel_pidst Ic].
  assert (idist_pidist_couplingP (x ← Is1_irrel; mret (f x))
                                 (x ← Is2_irrel; mret (g x))
                                 (λ x y, x = y)) as Ic'.
  { eapply ip_coupling_bind; eauto => ???.
    apply ip_coupling_mret; auto. }
                                    
  destruct Ic' as [I2 Hmem Ic'].
  apply ival_coupling_eq in Ic'.

  etransitivity; first apply Ex_min_irrel_anti; eauto.
  erewrite Ex_ival_irrel_proper; eauto.

  transitivity (Ex_min (λ x, Ex_min id (mret (g x))) Is2_irrel).
  { apply Ex_min_le_ext. 
    * intros. rewrite Ex_min_mret. reflexivity.
    * eapply ex_Ex_extrema_bounded_fun; eauto.
  }
  assert (ex_Ex_ival f Is1_irrel).
  { eapply ex_Ex_ival_irrel_proper; eauto. }
  etransitivity; first eapply Ex_min_bind_post_aux2; last first.
  - transitivity (Ex_ival (λ x, Ex_ival id (mret (f x))) Is1_irrel); last first.
    { apply Ex_ival_mono.
      * intros. rewrite Ex_ival_mret. reflexivity.
      * setoid_rewrite Ex_ival_mret. 
        eapply ex_Ex_ival_irrel_proper; eauto.
      * eapply ex_Ex_ival_irrel_proper; eauto.
    }
    rewrite -Ex_ival_bind_post; last first.
    { rewrite -ex_Ex_ival_fmap. eauto. }
    transitivity (Ex_ival id I2); last first.
    { refl_right. f_equal. symmetry. eapply Ex_ival_proper; eauto.
      rewrite -ex_Ex_ival_fmap. eauto. }
    
    apply In_pidist_le_singleton in Hmem.
    destruct Hmem as (I2'&Heq22'&?).
    transitivity (Ex_ival id I2'); last first.
    { refl_right. f_equal. symmetry. eapply Ex_ival_proper; eauto.
      eapply ex_Ex_ival_proper; eauto.
      rewrite -ex_Ex_ival_fmap. eauto. }
    apply Ex_min_spec1'; auto.
    eapply ex_Ex_ival_proper; eauto.
    eapply ex_Ex_ival_proper; eauto.
    rewrite -ex_Ex_ival_fmap. eauto.
  - setoid_rewrite Ex_min_mret.
    apply ex_Ex_extrema_bounded_fun; eauto.
  - intros. setoid_rewrite Ex_min_mret. rewrite //=.
  - apply Ex_min_bounded_fun_finite.
    setoid_rewrite Ex_min_mret. eauto.
Qed.

Lemma irrel_coupling_eq_Ex_min' {A1 A2 A3} f g (h : A3 → R) (I: ivdist A1) (Is: pidist A2) :
  irrel_couplingP I Is (λ x y, f x = g y) →
  bounded_fun (λ x, h (g x)) →
  Rbar_le (Ex_min (λ x, h (g x)) Is) (Ex_ival (λ x, h (f x)) I).
Proof.
  intros Hic Hb.
  eapply irrel_coupling_eq_Ex_min; eauto.
  eapply irrel_coupling_conseq; eauto.
  rewrite //=. intros x y ->. done.
Qed.

Lemma irrel_coupling_eq_Ex_max {A1 A2} f g (I: ivdist A1) (Is: pidist A2):
  irrel_couplingP I Is (λ x y, f x = g y) →
  bounded_fun g →
  Rbar_le (Ex_ival f I) (Ex_max g Is).
Proof.
  intros HIc Hb.
  apply Rbar_opp_le.
  rewrite Ex_max_neg_min Rbar_opp_involutive.
  rewrite /Rbar_opp//=.
  rewrite -Ex_ival_negate.
  apply irrel_coupling_eq_Ex_min; eauto.
  - eapply irrel_coupling_conseq; eauto => x y ?.
    nra.
  - destruct Hb as (c&Hb). exists c; intros x. specialize (Hb x).
    move: Hb. do 2 apply Rabs_case; nra.
Qed.


Lemma irrel_coupling_eq_ex_Ex_supp {A1 A2} f g (I: ivdist A1) (Is: pidist A2) :
  irrel_couplingP I Is (λ x y, f x = g y) →
  bounded_fun_on g (λ x, In_psupport x Is) →
  ex_Ex_ival f I.
Proof.
  intros Hi Hex.
  edestruct (bounded_fun_on_to_bounded g) as (g'&?Hb&Heq); eauto.
  feed pose proof (irrel_coupling_eq_ex_Ex f g' I Is); eauto.
  eapply irrel_coupling_conseq; last first.
  { unshelve (eapply @irrel_coupling_support); last eapply Hi. }
  rewrite //=. intros x y (Hpf&Hin&Hinp&?).
  rewrite -Heq; eauto.
Qed.

Lemma irrel_coupling_eq_Ex_min_supp {A1 A2} f g (I: ivdist A1) (Is: pidist A2) :
  irrel_couplingP I Is (λ x y, f x = g y) →
  bounded_fun_on g (λ x, In_psupport x Is) →
  Rbar_le (Ex_min g Is) (Ex_ival f I).
Proof.
  intros Hi Hex.
  edestruct (bounded_fun_on_to_bounded g) as (g'&?Hb&Heq); eauto.
  feed pose proof (irrel_coupling_eq_Ex_min f g' I Is); eauto.
  eapply irrel_coupling_conseq; last first.
  { unshelve (eapply @irrel_coupling_support); last eapply Hi. }
  rewrite //=. intros x y (Hpf&Hin&Hinp&?).
  rewrite -Heq; eauto.
  etransitivity; last eassumption.
  refl_right.
  eapply Ex_min_eq_ext_supp.
  eauto.
Qed.

Lemma irrel_coupling_eq_Ex_max_supp {A1 A2} f g (I: ivdist A1) (Is: pidist A2):
  irrel_couplingP I Is (λ x y, f x = g y) →
  bounded_fun_on g (λ x, In_psupport x Is) →
  Rbar_le (Ex_ival f I) (Ex_max g Is).
Proof.
  intros HIc Hb.
  apply Rbar_opp_le.
  rewrite Ex_max_neg_min Rbar_opp_involutive.
  rewrite /Rbar_opp//=.
  rewrite -Ex_ival_negate.
  apply irrel_coupling_eq_Ex_min_supp; eauto.
  - eapply irrel_coupling_conseq; eauto => x y ?.
    nra.
  - destruct Hb as (c&Hb). exists c; intros x Hin. specialize (Hb x Hin).
    move: Hb. do 2 apply Rabs_case; nra.
Qed.