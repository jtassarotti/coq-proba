Require Import Reals Psatz Omega Fourier.
From stdpp Require Import tactics list.
From discprob.basic Require Import seq_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.measure Require Export dynkin borel integral.
Require Import ClassicalEpsilon.

Record is_pt_hom {A1 A2} {F1 : measurable_space A1} {F2: measurable_space A2}
       (f: A1 → A2) (μ1: measure A1) (μ2: measure A2) : Prop :=
  {
    pt_hom_sigma:
      ∀ U, F2 U → F1 (fun_inv f U);
    pt_hom_meas:
      ∀ U, F2 U → μ2 U = μ1 (fun_inv f U)
  }.

Record is_pt_img_hom {A1 A2} {F1 : measurable_space A1} {F2: measurable_space A2}
       (f: A1 → A2) (μ1: measure A1) (μ2: measure A2) : Prop :=
  {
    pt_img_hom_sigma:
      ∀ U, F1 U → F2 (fun_img f U);
    pt_img_hom_meas:
      ∀ U, F1 U → μ1 U = μ2 (fun_img f U)
  }.

Record is_pt_iso {A1 A2} {F1 : measurable_space A1} {F2: measurable_space A2}
       (f: A1 → A2) (μ1: measure A1) (μ2: measure A2) : Prop :=
  { pt_iso_inj: ∀ x y, f x = f y → x = y;
    pt_iso_surj: ∀ y, ∃ x, f x = y;
    pt_iso_sigma1:
      ∀ U, F1 U → F2 (fun_img f U);
    pt_iso_sigma2:
      ∀ U, F2 U → F1 (fun_inv f U);
    pt_iso_meas1:
      ∀ U, F1 U → μ1 U = μ2 (fun_img f U);
    pt_iso_meas2:
      ∀ U, F2 U → μ2 U = μ1 (fun_inv f U)
  }.

Lemma is_pt_hom_comp {A1 A2 A3} {F1 : measurable_space A1} {F2 : measurable_space A2} {F3: measurable_space A3}
      (f1: A1 → A2) (f2 : A2 → A3) (μ1: measure A1) (μ2: measure A2) (μ3: measure A3):
  is_pt_hom f1 μ1 μ2 →
  is_pt_hom f2 μ2 μ3 →
  is_pt_hom (λ x, f2 (f1 x)) μ1 μ3.
Proof.
  intros Hhom1 Hhom2.
  split.
  - intros. eapply measurable_comp; eauto.
    * intros ?. eapply pt_hom_sigma; eauto.
    * intros ?. eapply pt_hom_sigma; eauto.
  - intros U HU.
    rewrite (pt_hom_meas _ _ _ Hhom2) //.
    rewrite (pt_hom_meas _ _ _ Hhom1) //.
    eapply pt_hom_sigma; eauto.
Qed.

Lemma is_pt_hom_id {A} {F: measurable_space A} (μ : measure A) :
  is_pt_hom id μ μ.
Proof.
  split; rewrite //=.
Qed.

Lemma is_pt_img_hom_inl {A1 A2} {F1 : measurable_space A1} {F2 : measurable_space A2}
      (μ1: measure A1) (μ2: measure A2):
  is_pt_img_hom inl μ1 (disjoint_sum_measure μ1 μ2).
Proof.
  split.
  - intros U ?. split; eauto.
    * eapply sigma_proper; eauto.
      clear; firstorder.
    * eapply (sigma_proper _ _ _ empty_set).
      ** clear; firstorder.
      ** apply sigma_empty_set.
  - rewrite //=. intros U HF. rewrite -[a in a = _](Rplus_0_r).
    f_equal.
    * apply measure_proper. clear; firstorder.
    * symmetry. erewrite <-measure_empty; first apply measure_proper.
      clear; firstorder.
Qed.

Lemma is_pt_img_hom_inr {A1 A2} {F1 : measurable_space A1} {F2 : measurable_space A2}
      (μ1: measure A1) (μ2: measure A2):
  is_pt_img_hom inr μ2 (disjoint_sum_measure μ1 μ2).
Proof.
  split.
  - intros U ?. split; eauto.
    * eapply (sigma_proper _ _ _ empty_set).
      ** clear; firstorder.
      ** apply sigma_empty_set.
    * eapply sigma_proper; eauto.
      clear; firstorder.
  - rewrite //=. intros U HF. rewrite -[a in a = _](Rplus_0_l).
    f_equal.
    * symmetry.
      assert (@fun_inv A1 (A1 + A2) inl (fun_img inr U) ≡ ∅) as ->; first by (clear; firstorder).
      apply measure_empty.
    * apply measure_proper. clear; firstorder.
Qed.

Lemma measurable_inl {A1 A2} {F1: measurable_space A1} {F2: measurable_space A2}:
  measurable (@inl A1 A2).
Proof. intros ? (?&?); done. Qed.

Lemma measurable_inr {A1 A2} {F1: measurable_space A1} {F2: measurable_space A2}:
  measurable (@inr A1 A2).
Proof. intros ? (?&?); done. Qed.

Lemma is_pt_hom_sum {A1 A2 A1' A2'} F1 F2 F1' F2'
      (μ1: @measure _ F1) (μ2: @measure _ F2) (μ1': @measure _ F1') (μ2': @measure _ F2')
      (f1: A1 → A1') (f2: A2 → A2'):
  is_pt_hom f1 μ1 μ1' →
  is_pt_hom f2 μ2 μ2' →
  is_pt_hom (λ x : A1 + A2, match x with
                            | inl x1 => inl (f1 x1)
                            | inr x2 => inr (f2 x2)
                            end)
            (disjoint_sum_measure μ1 μ2) (disjoint_sum_measure μ1' μ2').
Proof.
  intros Hhom1 Hhom2.
  split.
  - intros U (?&?). split.
    * eapply (sigma_proper _ _ _ (fun_inv f1 (fun_inv inl U))).
      { split; clear; firstorder. }
      eapply pt_hom_sigma; eauto.
    * eapply (sigma_proper _ _ _ (fun_inv f2 (fun_inv inr U))).
      { split; clear; firstorder. }
      eapply pt_hom_sigma; eauto.
  - intros U (?&?); rewrite //=. f_equal.
    * rewrite (pt_hom_meas _ _ _ Hhom1); eauto.
    * rewrite (pt_hom_meas _ _ _ Hhom2); eauto.
Qed.

Lemma is_pt_hom_sum_swap {A1 A2} F1 F2
      (μ1: @measure A1 F1) (μ2: @measure A2 F2):
  is_pt_hom (λ x : A1 + A2, match x with
                            | inl x1 => inr x1
                            | inr x2 => inl x2
                            end)
            (disjoint_sum_measure μ1 μ2) (disjoint_sum_measure μ2 μ1).
Proof.
  split.
  - intros U (?&?). split; auto.
  - intros U (?&?). rewrite //=. rewrite Rplus_comm. f_equal.
Qed.

Lemma is_pt_hom_sum_assoc {A1 A2 A3} F1 F2 F3
      (μ1: @measure A1 F1) (μ2: @measure A2 F2) (μ3: @measure A3 F3):
        is_pt_hom (λ x : (A1 + A2) + A3,
                         match x with
                         | inl (inl x1) => inl x1
                         | inl (inr x2) => inr (inl x2)
                         | inr x3 => inr (inr x3)
                         end)
                  (disjoint_sum_measure (disjoint_sum_measure μ1 μ2) μ3)
                  (disjoint_sum_measure μ1 (disjoint_sum_measure μ2 μ3)).
Proof.
  split.
  - intros U (?&(?&?)). split; auto. split; auto.
  - intros U (?&(?&?)). rewrite //=. rewrite Rplus_assoc. f_equal.
Qed.

Lemma is_pt_img_hom_sum {A1 A2 A1' A2'} F1 F2 F1' F2'
      (μ1: @measure A1 F1) (μ2: @measure A2 F2) (μ1': @measure A1' F1') (μ2': @measure A2' F2')
      (f1: A1 → A1') (f2: A2 → A2'):
  is_pt_img_hom f1 μ1 μ1' →
  is_pt_img_hom f2 μ2 μ2' →
  is_pt_img_hom (λ x : A1 + A2, match x with
                            | inl x1 => inl (f1 x1)
                            | inr x2 => inr (f2 x2)
                            end)
            (disjoint_sum_measure μ1 μ2) (disjoint_sum_measure μ1' μ2').
Proof.
  intros Hhom1 Hhom2.
  split.
  - intros U (?&?). split.
    * eapply (sigma_proper _ _ _ (fun_img f1 (fun_inv inl U))).
      { intros z; split; clear; try (firstorder; done).
        intros x. firstorder. destruct x; try firstorder. congruence.  }
      eapply pt_img_hom_sigma; eauto.
    * eapply (sigma_proper _ _ _ (fun_img f2 (fun_inv inr U))).
      { intros z; split; clear; try (firstorder; done).
        intros x. firstorder. destruct x; try firstorder. congruence.  }
      eapply pt_img_hom_sigma; eauto.
  - intros U (?&?); rewrite //=. f_equal.
    * rewrite (pt_img_hom_meas _ _ _ Hhom1); eauto.
      { eapply measure_proper.
        { intros z; split; clear; try (firstorder; done).
          intros x. firstorder. destruct x; try firstorder. congruence.  }
      }
    * rewrite (pt_img_hom_meas _ _ _ Hhom2); eauto.
      { apply measure_proper.
        { intros z; split; clear; try (firstorder; done).
          intros x. firstorder. destruct x; try firstorder. congruence.  }
      }
Qed.

Lemma is_pt_img_hom_sum_swap {A1 A2} F1 F2
      (μ1: @measure A1 F1) (μ2: @measure A2 F2):
  is_pt_img_hom (λ x : A1 + A2, match x with
                            | inl x1 => inr x1
                            | inr x2 => inl x2
                            end)
            (disjoint_sum_measure μ1 μ2) (disjoint_sum_measure μ2 μ1).
Proof.
  split.
  - intros U (?&?). split; auto.
    * eapply sigma_proper; eauto.
      intros z. clear; split.
      ** intros ([|]&?&Heq); inversion Heq; subst; eauto.
      ** firstorder.
    * eapply sigma_proper; eauto.
      intros z. clear; split.
      ** intros ([|]&?&Heq); inversion Heq; subst; eauto.
      ** firstorder.
  - rewrite //=. intros U (?&?). rewrite Rplus_comm; f_equal.
    * apply measure_proper.
      intros z. clear; split.
      ** firstorder.
      ** intros ([|]&?&Heq); inversion Heq; subst; eauto.
    * apply measure_proper.
      intros z. clear; split.
      ** firstorder.
      ** intros ([|]&?&Heq); inversion Heq; subst; eauto.
Qed.

Lemma is_pt_img_hom_sum_assoc {A1 A2 A3} F1 F2 F3
      (μ1: @measure A1 F1) (μ2: @measure A2 F2) (μ3: @measure A3 F3):
        is_pt_img_hom (λ x : (A1 + A2) + A3,
                         match x with
                         | inl (inl x1) => inl x1
                         | inl (inr x2) => inr (inl x2)
                         | inr x3 => inr (inr x3)
                         end)
                  (disjoint_sum_measure (disjoint_sum_measure μ1 μ2) μ3)
                  (disjoint_sum_measure μ1 (disjoint_sum_measure μ2 μ3)).
Proof.
  split.
  - intros U ((?&?)&?); split; auto.
    * eapply sigma_proper; eauto.
      intros z. clear; split.
      ** intros ([[|]|]&?&Heq); inversion Heq; subst; eauto.
      ** firstorder.
    * split.
      ** eapply sigma_proper; eauto.
         intros z. clear; split.
         *** intros ([[|]|]&?&Heq); inversion Heq; subst; eauto.
         *** firstorder.
      ** eapply sigma_proper; eauto.
         intros z. clear; split.
         *** intros ([[|]|]&?&Heq); inversion Heq; subst; eauto.
         *** firstorder.
  - intros U ((?&?)&?).
    rewrite //=. rewrite Rplus_assoc. f_equal; [| f_equal].
    * apply measure_proper.
      intros z. clear; split.
      ** firstorder.
      ** intros ([[|]|]&?&Heq); inversion Heq; subst; eauto.
    * apply measure_proper.
      intros z. clear; split.
      ** firstorder.
      ** intros ([[|]|]&?&Heq); inversion Heq; subst; eauto.
    * apply measure_proper.
      intros z. clear; split.
      ** firstorder.
      ** intros ([[|]|]&?&Heq); inversion Heq; subst; eauto.
Qed.

Lemma is_pt_img_hom_comp {A1 A2 A3} {F1 : measurable_space A1} {F2 : measurable_space A2}
      {F3: measurable_space A3}
      (f1: A1 → A2) (f2 : A2 → A3) (μ1: @measure A1 F1) (μ2: @measure A2 F2) (μ3: @measure A3 F3):
  is_pt_img_hom f1 μ1 μ2 →
  is_pt_img_hom f2 μ2 μ3 →
  is_pt_img_hom (λ x, f2 (f1 x)) μ1 μ3.
Proof.
  intros Hhom1 Hhom2.
  assert (∀ U, fun_img (λ x, f2 (f1 x)) U ≡ fun_img f2 (fun_img f1 U)) as Hequiv.
  { clear; firstorder. }
  split.
  - intros. rewrite Hequiv.
    apply Hhom2, Hhom1; eauto.
  - intros U HU.
    rewrite (pt_img_hom_meas _ _ _ Hhom1) //.
    rewrite (pt_img_hom_meas _ _ _ Hhom2) //.
    * rewrite Hequiv; eauto.
    * eapply pt_img_hom_sigma; eauto.
Qed.

Lemma is_pt_img_hom_id {A} {F: measurable_space A} (μ : @measure A F) :
  is_pt_img_hom id μ μ.
Proof.
  split; rewrite //=.
  * intros U HFU. eapply sigma_proper; eauto; clear; firstorder.
  * intros U HFU. eapply measure_proper; clear; firstorder.
Qed.

Lemma is_pt_hom_ae {A1 A2} {F1: measurable_space A1} {F2: measurable_space A2}
      (μ1: @measure _ F1) (μ2: @measure _ F2) f U:
  is_pt_hom f μ1 μ2 →
  almost_everywhere_meas μ2 U → almost_everywhere_meas μ1 (λ a, U (f a)).
Proof.
  intros Hhom (Hm&Heq0).
  assert (Hequiv: eq_prop (compl (λ a : A1, U (f a))) (fun_inv f (compl U))).
  { clear; firstorder. }
  split.
  - eapply @pt_hom_sigma in Hm; last eapply Hhom.
    eapply sigma_proper; eauto.
  - rewrite Hequiv. rewrite -Heq0.
    symmetry; eapply pt_hom_meas; eauto.
Qed.

Section iso_props.

  Context {A1 A2: Type}.
  Context {F1 : measurable_space A1}.
  Context {F2 : measurable_space A2}.
  Context (μ1: measure A1).
  Context (μ2: measure A2).
  Context (f: A1 → A2).

  Lemma is_pt_iso_inv_hom:
    is_pt_hom f μ1 μ2 →
    (∃ f', is_pt_hom f' μ2 μ1 ∧
      (∀ x, f (f' x) = x) ∧ (∀ y, f' (f y) = y)) →
    is_pt_iso f μ1 μ2.
  Proof.
    intros Hhom (f'&Hhom'&Hrl&Hlr).
    assert (∀ U, F1 U → fun_img f U ≡ fun_inv f' U) as Hequiv.
    { intros U HF x. rewrite /fun_img/fun_inv; split.
      * intros (y&HU&Hf). rewrite -Hf Hlr. done.
      * intros HU. exists (f' x); split; eauto.
    }
    split.
    - intros x y Heq. rewrite -(Hlr x) -(Hlr y).
      by f_equal.
    - intros y. exists (f' y). done.
    - intros U HF. rewrite Hequiv; eauto.
      eapply pt_hom_sigma; eauto.
    - eapply pt_hom_sigma; eauto.
    - intros U HU. rewrite Hequiv //. eapply pt_hom_meas; eauto.
    - eapply pt_hom_meas; eauto.
  Qed.

  Lemma is_pt_iso_bij_hom:
    is_pt_hom f μ1 μ2 →
    is_pt_img_hom f μ1 μ2 →
    (∀ x y, f x = f y → x = y) →
    (∀ y, ∃ x, f x = y) →
    is_pt_iso f μ1 μ2.
  Proof.
    intros Hhom Himg_hom Hinj Hsurj.
    split; eauto.
    - eapply pt_img_hom_sigma; eauto.
    - eapply pt_hom_sigma; eauto.
    - eapply pt_img_hom_meas; eauto.
    - eapply pt_hom_meas; eauto.
  Qed.


  Context (Hiso: is_pt_iso f μ1 μ2).

  Lemma is_pt_hom_iso:
    is_pt_hom f μ1 μ2.
  Proof.
    split.
    - eapply pt_iso_sigma2; eauto.
    - eapply pt_iso_meas2; eauto.
  Qed.

  Lemma is_pt_img_hom_iso:
    is_pt_img_hom f μ1 μ2.
  Proof.
    split.
    - eapply pt_iso_sigma1; eauto.
    - eapply pt_iso_meas1; eauto.
  Qed.

  Definition iso_inv : A2 → A1.
  Proof.
    intros a2. specialize (pt_iso_surj _ _ _ Hiso a2) => Hex.
    apply constructive_indefinite_description in Hex as (x&?). exact x.
  Defined.

  Lemma iso_inv_img U:
    fun_img iso_inv U ≡ fun_inv f U.
  Proof.
    intros x. rewrite /fun_img/fun_inv/iso_inv; split.
    - intros (y&HU&?). destruct constructive_indefinite_description. congruence.
    - intros HU. exists (f x); split; eauto.
      destruct constructive_indefinite_description. eapply pt_iso_inj; eauto.
  Qed.

  Lemma img_iso_inv U:
    fun_img f U ≡ fun_inv iso_inv U.
  Proof.
    intros x. rewrite /fun_img/fun_inv/iso_inv; split.
    - intros (y&HU&?). destruct constructive_indefinite_description as (y'&?).
      assert (y = y').
      { eapply pt_iso_inj; eauto. congruence. }
      intros; subst; eauto.
    - intros HU.
      destruct constructive_indefinite_description as (x'&?).
      exists x'; split; eauto.
  Qed.

  Lemma iso_measurable: measurable f.
  Proof. intros U ?; eapply pt_iso_sigma2; eauto. Qed.

  Lemma iso_inv_iso: is_pt_iso iso_inv μ2 μ1.
  Proof.
    split.
    - intros x y. rewrite /iso_inv. do 2 destruct constructive_indefinite_description; congruence.
    - intros x. exists (f x).
      rewrite /iso_inv; destruct constructive_indefinite_description.
      eapply pt_iso_inj; eauto.
    - intros U HU. rewrite iso_inv_img. eapply pt_iso_sigma2; eauto.
    - intros U HU. rewrite -img_iso_inv. eapply pt_iso_sigma1; eauto.
    - intros U HU. rewrite iso_inv_img. eapply pt_iso_meas2; eauto.
    - intros U HU. rewrite -img_iso_inv. eapply pt_iso_meas1; eauto.
  Qed.

  Lemma iso_inv_rinv x: f (iso_inv x) = x.
  Proof.
    rewrite /iso_inv; destruct constructive_indefinite_description; eauto.
  Qed.

  Lemma iso_inv_linv x: iso_inv (f x) = x.
  Proof.
    rewrite /iso_inv; destruct constructive_indefinite_description as (?&Heq); eauto.
    eapply pt_iso_inj in Heq; eauto.
  Qed.

  Lemma iso_ae (U: A2 → Prop) :
    almost_everywhere_meas μ2 U → almost_everywhere_meas μ1 (λ a, U (f a)).
  Proof. intros. eapply is_pt_hom_ae; eauto. apply is_pt_hom_iso. Qed.

  Lemma iso_ae_img (U: A1 → Prop) :
    almost_everywhere_meas μ1 U → almost_everywhere_meas μ2 (fun_img f U).
  Proof.
    intros (Hm&Heq0).
    assert (Hequiv: eq_prop (compl (fun_img f U)) (fun_img f (compl U))).
    { split.
      * intros Hcomp. edestruct (pt_iso_surj f _ _ Hiso x) as (y&?).
        eexists. split; eauto. intros HU. apply Hcomp. eexists; eauto.
      * intros (x1&Hcomp&Hf).
        intros Hcomp'. apply Hcomp. destruct (Hcomp') as (x1'&HU&?).
        subst.
        assert (x1 = x1') as ->; eauto.
        { eapply pt_iso_inj; eauto.  }
    }
    split.
    - eapply pt_iso_sigma1 in Hm; eauto.
      eapply sigma_proper; eauto.
    - rewrite Hequiv. rewrite -Heq0.
      symmetry; eapply pt_iso_meas1; eauto.
  Qed.

End iso_props.

Lemma is_pt_iso_id {A} (F: measurable_space A) (μ: @measure A F):
  is_pt_iso id μ μ.
Proof.
  apply is_pt_iso_bij_hom.
  - apply is_pt_hom_id.
  - apply is_pt_img_hom_id.
  - auto.
  - intros; eexists; eauto.
Qed.

Lemma is_pt_iso_sum_swap {A1 A2} F1 F2
      (μ1: @measure A1 F1) (μ2: @measure A2 F2):
    is_pt_iso (λ x : A1 + A2, match x with
                              | inl x1 => inr x1
                              | inr x2 => inl x2
                              end)
            (disjoint_sum_measure μ1 μ2) (disjoint_sum_measure μ2 μ1).
Proof.
  apply is_pt_iso_bij_hom.
  - apply is_pt_hom_sum_swap.
  - apply is_pt_img_hom_sum_swap.
  - intros [|] [|]; auto; try congruence.
  -  intros [a2|a1].
     * exists (inr a2); eauto.
     * exists (inl a1); eauto.
Qed.

Lemma is_pt_iso_sum_assoc {A1 A2 A3} F1 F2 F3
      (μ1: @measure A1 F1) (μ2: @measure A2 F2) (μ3: @measure A3 F3):
        is_pt_iso (λ x : (A1 + A2) + A3,
                         match x with
                         | inl (inl x1) => inl x1
                         | inl (inr x2) => inr (inl x2)
                         | inr x3 => inr (inr x3)
                         end)
                  (disjoint_sum_measure (disjoint_sum_measure μ1 μ2) μ3)
                  (disjoint_sum_measure μ1 (disjoint_sum_measure μ2 μ3)).
Proof.
  apply is_pt_iso_bij_hom.
  - apply is_pt_hom_sum_assoc.
  - apply is_pt_img_hom_sum_assoc.
  - intros [[|]|] [[|]|]; auto; try congruence.
  - intros [a1|[a2|a3]].
    * by exists (inl (inl a1)).
    * by exists (inl (inr a2)).
    * by exists (inr a3).
Qed.

Arguments iso_inv_iso {_ _ _ _ _ _} _ _.
Arguments iso_inv {_ _ _ _ _ _} _ _.

Section wpt.
  Context {A1 A2: Type}.
  Context {F1 : measurable_space A1}.
  Context {F2 : measurable_space A2}.
  Context (μ1: measure A1).
  Context (μ2: measure A2).
  Context (f: A1 → A2).


  Context (Hiso: is_pt_iso f μ1 μ2).

  Lemma wpt_iso_aux1 (wpt: weighted_partition F1):
    ∀ (r : R) (U : A2 → Prop),
      In (r, U) (map (λ rU : R * (A1 → Prop), (rU.1, fun_img f rU.2)) wpt) → F2 U.
  Proof.
    intros r U Hin. apply in_map_iff in Hin as ((r'&U')&Heq&Hin).
    inversion Heq; subst. eapply pt_iso_sigma1; eauto.
    by apply In_wpt_snd_measurable in Hin.
  Qed.

  Definition wpt_iso (wpt : weighted_partition F1) : weighted_partition F2 :=
    wpt_indicator_scal_list (map (λ rU, (fst rU, fun_img f (snd rU))) wpt) (wpt_iso_aux1 wpt).

  Lemma wpt_iso_spec wpt x:
    wpt_fun (wpt_iso wpt) (f x) = wpt_fun wpt x.
  Proof.
    symmetry.
    rewrite /wpt_iso.
    feed pose proof (@wpt_indicator_scal_list_spec2 _ F2 _ (wpt_iso_aux1 wpt)) as Hindc.
    { rewrite map_map //=.
      assert (Hdisj: ## map snd wpt).
      { rewrite wpt_partition_spec1. apply partition_disjoint. }
      revert Hdisj. generalize (wpt_list wpt).
      clear -Hiso. induction l.
      * intros. rewrite //=. econstructor.
      * intros. rewrite //=. econstructor.
        ** inversion Hdisj as [| ?? Hdisj']; subst.
           intros z (Hin1&Hin2).
           apply union_list_inv in Hin2 as (U'&Hin_list&Hz).
           destruct Hin1 as (a1&?&?).
           eapply Hdisj'.
           { split; eauto. apply in_map_iff in Hin_list as ((?&U'')&?&?).
             apply (union_list_intro _ _ U''); subst.
             * apply in_map_iff. eexists; split; eauto. done.
             * destruct Hz as (?&?&Heq). eapply pt_iso_inj in Heq; eauto. subst.
               eauto.
           }
        ** eapply IHl. inversion Hdisj; eauto.
    }
    specialize (Hindc (f x)).
    destruct Hindc as [Hc1|Hc2].
    - destruct Hc1 as (Hnin&Hval).
      exfalso. destruct (partition_union (wpt_part wpt) x) as (U&Hin&HU); first done.
      eapply (Hnin (wpt_fun wpt x) (fun_img f U)).
      { apply in_map_iff. exists (wpt_fun wpt x, U); split; eauto.
        apply wpt_fun_eq1; eauto. }
      eexists; eauto.
    - destruct Hc2 as (r&U&Hin&HU&->).
      apply in_map_iff in Hin.
      destruct Hin as ((r'&U')&Heq&Hin').
      inversion Heq; subst.
      eapply wpt_fun_eq2; eauto.
      destruct HU as (x'&HU'&Heq').
      eapply pt_iso_inj in Heq'; eauto.
      congruence.
  Qed.

  Lemma wpt_integral_iso wpt:
    wpt_integral μ2 (wpt_iso wpt) = wpt_integral μ1 wpt.
  Proof.
    symmetry.
    induction wpt using wpt_induction.
    - transitivity (wpt_integral μ1 wpt1).
      { eapply wpt_integral_proper; eauto. by symmetry. }
      rewrite IHwpt1.
      apply wpt_integral_proper.
      intros x.
      edestruct (pt_iso_surj _ _ _ Hiso x).
      subst. rewrite ?wpt_iso_spec. done.
    - rewrite /wpt_iso//=.
      rewrite ?wpt_integral_plus ?wpt_integral_scal ?wpt_integral_indicator measure_empty.
      ring_simplify. eapply pt_iso_meas1; eauto.
    - rewrite ?wpt_integral_plus IHwpt1 IHwpt2 -wpt_integral_plus.
      apply wpt_integral_proper.
      intros z.
      edestruct (pt_iso_surj _ _ _ Hiso z).
      subst. rewrite wpt_iso_spec ?wpt_plus_spec; f_equal; apply wpt_iso_spec.
    - rewrite wpt_integral_scal IHwpt.
      symmetry. transitivity (wpt_integral μ2 (wpt_scal k (wpt_iso wpt))).
      { apply wpt_integral_proper; intros z.
        edestruct (pt_iso_surj _ _ _ Hiso z). subst.
        rewrite wpt_iso_spec.
        rewrite ?wpt_scal_spec. f_equal.
        symmetry; apply wpt_iso_spec.
      }
      rewrite wpt_integral_scal; f_equal.
  Qed.
End wpt.

Arguments wpt_iso {_ _ _ _ _ _} _ _ _.

Section integral1.
  Context {A1 A2: Type}.
  Context {F1 : measurable_space A1}.
  Context {F2 : measurable_space A2}.
  Context (f: A1 → A2).
  Context (μ1: measure A1).
  Context (μ2: measure A2).
  Context (Hiso: is_pt_iso f μ1 μ2).

  Lemma is_pos_integral_iso g v:
    is_pos_integral μ2 g v → is_pos_integral μ1 (λ x, g (f x)) v.
  Proof.
    rewrite /is_pos_integral. intros (Hmeas&Hlub).
    split.
    - eapply measurable_comp; eauto. eapply iso_measurable; eauto.
    - split.
      * intros ? (wpt&Hspec&<-).
        apply Hlub. exists (wpt_iso f Hiso wpt); split.
        ** intros x.
           edestruct (pt_iso_surj _ _ _ Hiso x). subst.
           rewrite wpt_iso_spec. eauto.
        ** apply wpt_integral_iso.
      * intros b Hub. eapply Hlub.
        intros ? (wpt&Hspec&<-).
        apply Hub. exists (wpt_iso (iso_inv _ Hiso) (iso_inv_iso _ Hiso) wpt).
        split.
        ** intros x. destruct (pt_iso_surj _ _ _ (iso_inv_iso _ Hiso) x).
           subst. rewrite wpt_iso_spec iso_inv_rinv. eauto.
        ** apply wpt_integral_iso.
  Qed.

  Lemma is_integral_iso' g v:
    is_integral μ2 g v → is_integral μ1 (λ x, g (f x)) v.
  Proof.
    intros (Hm&(v1&v2&Hp1&Hp2&Heq)).
    split.
    { eapply measurable_comp; eauto. eapply iso_measurable; eauto. }
    exists v1, v2; split_and!; eauto.
    - by apply is_pos_integral_iso in Hp1.
    - by apply is_pos_integral_iso in Hp2.
  Qed.
End integral1.

Section integral2.
  Context {A1 A2: Type}.
  Context {F1 : measurable_space A1}.
  Context {F2 : measurable_space A2}.
  Context (f: A1 → A2).
  Context (μ1: @measure A1 F1).
  Context (μ2: @measure A2 F2).
  Context (Hiso: is_pt_iso f μ1 μ2).

  Lemma is_integral_iso g v:
    is_integral μ2 g v ↔ is_integral μ1 (λ x, g (f x)) v.
  Proof.
    split.
    - by apply is_integral_iso'.
    - intros His. eapply is_integral_iso' in His.
      { setoid_rewrite (iso_inv_rinv) in His; eauto. }
      apply iso_inv_iso.
  Qed.

  Lemma ex_integral_iso g:
    ex_integral μ2 g ↔ ex_integral μ1 (λ x, g (f x)).
  Proof.
    split; intros (v&His); exists v; by apply is_integral_iso.
  Qed.

  Lemma Pos_integral_iso g:
    (∀ x, 0 <= g x) →
    measurable g →
    Pos_integral μ1 (λ x, g (f x)) = Pos_integral μ2 g.
  Proof.
    intros Hpos Hmeas.
    destruct (Classical_Prop.classic (ex_pos_integral μ2 g)) as [Hex|Hnex].
    { destruct Hex as (v&His).
      transitivity v.
      * apply is_pos_integral_unique. apply is_integral_equiv_pos_integral; eauto.
        apply is_integral_iso; eauto.
        apply is_integral_equiv_pos_integral; eauto.
      * symmetry. apply is_pos_integral_unique. done.
    }
    rewrite [a in _ = a]measurable_non_ex_pos_integral_0; eauto.
    apply measurable_non_ex_pos_integral_0.
    * eapply measurable_comp; eauto. eapply iso_measurable; eauto.
    * intros Hex. apply ex_integral_equiv_pos_integral in Hex; eauto.
      apply ex_integral_iso in Hex. apply Hnex. by apply ex_integral_equiv_pos_integral.
  Qed.

  Lemma Integral_iso g:
    measurable g →
    Integral μ1 (λ x, g (f x)) = Integral μ2 g.
  Proof.
    intros Hmeas.
    rewrite /Integral.
    f_equal.
    - eapply (Pos_integral_iso (λ x, Rmax (g x) 0)); eauto using Rmax_r.
      measurable.
    - eapply (Pos_integral_iso (λ x, Rmax (- g x) 0)); eauto using Rmax_r.
      measurable.
  Qed.

End integral2.

Lemma sub_sigma_closed {A: Type} (F: sigma_algebra A) (U: A → Prop) :
  ∀ Ps, (∀ i : nat, ∃ V' : A → Prop, F V' ∧ (∀ x : {x : A | U x}, Ps i x ↔ V' (projT1 x)))
        → ∃ V' : A → Prop, F V' ∧ (∀ x : {x : A | U x}, unionF Ps x ↔ V' (projT1 x)).
Proof.
  intros Ps HPs.
  unshelve eexists.
  { eapply (@unionF _ nat). intros i a. specialize (HPs i).
    apply constructive_indefinite_description in HPs as (V'&?).
    exact (V' a).
  }
  split.
  * apply sigma_closed_unions => i.
    rewrite //=. destruct constructive_indefinite_description; intuition.
  * intros x. split.
    ** intros (i&?). exists i => //=.
       destruct constructive_indefinite_description; firstorder.
    ** intros (i&Hi). exists i.
       destruct (HPs i) as (?&?). intuition.
       edestruct constructive_indefinite_description in Hi. firstorder.
Qed.

Definition sub_sigma {A: Type} (F: sigma_algebra A) (U : A → Prop) : sigma_algebra (sig U).
  refine ({| sigma_sets := λ V : (sig U → Prop), ∃ V' : A → Prop,
                               F V' ∧ (∀ x : sig U, V x ↔ V' (projT1 x)) |}).
  - abstract firstorder.
  - abstract (exists (λ x, True); split; auto).
  - intros P (V'&HFV'&HV'). exists (compl V'); split; auto.
    abstract firstorder.
  - apply sub_sigma_closed.
Defined.

Instance sub_measurable_space {A: Type} (F: measurable_space A) (U : A → Prop) : measurable_space (sig U).
Proof. econstructor. apply sub_sigma, measurable_space_sigma. Defined.

Definition sub_measure {A: Type} {F: measurable_space A} (μ: @measure A F) U (HU: F U)
  : measure (sig U).
  refine {| measure_fun := λ A, μ (λ x, ∃ Hp, A (exist _ x Hp)) |}.
  - intros V V' Heq.
    apply measure_proper.
    intros x. split.
    * intros (HP&?). exists HP. by apply Heq.
    * intros (HP&?). exists HP. by apply Heq.
  - intros; apply measure_nonneg.
  - rewrite -(measure_empty _ μ). apply measure_proper.
    intros x; split.
    * intros (?&[]).
    * inversion 1.
  - intros Ps HFsub Hdisj.
    set (Ps' := λ i, λ x, ∃ Hp : U x, Ps i (exist _ x Hp)).
    assert (Heq: ∀ i, Ps' i ≡ (λ x, ∃ Hp, Ps i (exist _ x Hp))).
    { intros i. split.
      - intros (?&?). eexists; eauto.
      - intros (?&?). eexists; eauto.
    }
    assert (Heq_unionF: unionF Ps' ≡ (λ x, ∃ Hp, unionF Ps (exist _ x Hp))).
    { intros x; split.
      * intros (i&(?&?)); eexists; exists i; eauto.
      * intros (i&(?&?)); eexists; exists i; eauto.
    }
    eapply is_series_ext.
    { intros n. rewrite -Heq. done. }
    rewrite -Heq_unionF.
    apply measure_additivity.
    * intros i. rewrite /Ps'.
      destruct (HFsub i) as (V'&?&?). eapply (sigma_proper _ _ (V' ∩ U)); eauto.
      intros z. split.
      ** intros (HP&HU'). exists HU'. eapply H0 => //=.
      ** intros (?&?). eexists; eauto. eapply (H0 (exist _ _ x)). eauto.
    * clear -Hdisj. intros i j Hneq x (Hin1&Hin2).
      destruct Hin1 as (HU1&HP1).
      destruct Hin2 as (HU2&HP2).
      assert (HU1 = HU2).
      { apply classical_proof_irrelevance. }
      subst. eapply (Hdisj i j Hneq); split; eauto.
Defined.


Record is_mod0_iso {A1 A2} {F1} {F2}
       (U1 : A1 → Prop) (U2 : A2 → Prop)
       (f: sig U1 → sig U2) (μ1: @measure A1 F1) (μ2: @measure A2 F2) : Prop :=
  {
    mod0_iso_ae1: almost_everywhere_meas μ1 U1;
    mod0_iso_ae2: almost_everywhere_meas μ2 U2;
    mod0_iso_is_iso: is_pt_iso f
                       (sub_measure μ1 U1 (almost_everywhere_meas_meas μ1 _ mod0_iso_ae1))
                       (sub_measure μ2 U2 (almost_everywhere_meas_meas μ2 _ mod0_iso_ae2))
  }.

Record is_mod0_hom {A1 A2} {F1} {F2}
       (U1 : A1 → Prop) (U2 : A2 → Prop)
       (f: sig U1 → sig U2) (μ1: @measure A1 F1) (μ2: @measure A2 F2) : Prop :=
  {
    mod0_hom_ae1: almost_everywhere_meas μ1 U1;
    mod0_hom_ae2: almost_everywhere_meas μ2 U2;
    mod0_hom_is_hom: is_pt_hom f
                       (sub_measure μ1 U1 (almost_everywhere_meas_meas μ1 _ mod0_hom_ae1))
                       (sub_measure μ2 U2 (almost_everywhere_meas_meas μ2 _ mod0_hom_ae2))
  }.

Record is_mod0_embedding {A1 A2} {F1} {F2}
       (f : A1 → A2) (μ1: @measure A1 F1) (μ2: @measure A2 F2) : Prop :=
  {
    mod0_embedding_ae: almost_everywhere_meas μ2 (fun_img f (λ _, True));
    mod0_embedding_inj: ∀ x y, f x = f y → x = y;
    mod0_embedding_hom: is_pt_hom f μ1 μ2;
    mod0_embedding_img_hom: is_pt_img_hom f μ1 μ2
  }.

Lemma almost_everywhere_meas_inter_measure
      {A: Type} {F} {μ1: @measure A F} (U1 U2: A → Prop) (HF: F U2):
   almost_everywhere_meas μ1 U1 →
   μ1 U2 = μ1 (U2 ∩ U1).
Proof.
  intros Hae. rewrite -(compl_involutive U1) -set_minus_union_complement.
  destruct Hae as (?&Heq0).
  apply Rle_antisym.
  * etransitivity; last first.
    { apply Rge_le, measure_set_minus'; eauto. }
    rewrite Heq0. nra.
  * apply measure_mono; eauto; clear; firstorder.
Qed.

Lemma is_pt_hom_ae_sval {A: Type} {F} (μ1: @measure A F) (U1: A → Prop) (HU: F U1)
  (Hae: almost_everywhere_meas μ1 U1):
  is_pt_hom sval (sub_measure μ1 U1 HU) μ1.
Proof.
  split.
  - intros U HF. exists U; split; eauto.
  - intros U HF. rewrite //=.
    rewrite (almost_everywhere_meas_inter_measure _ _ _ Hae); eauto.
    apply measure_proper. intros x; split.
      * intros (?&HU1). exists HU1; eauto.
      * intros (?&?). split; eauto.
Qed.

Lemma is_pt_img_hom_ae_sval {A: Type} {F} (μ1: @measure A F) (U1: A → Prop) (HU: F U1)
  (Hae: almost_everywhere_meas μ1 U1):
  is_pt_img_hom sval (sub_measure μ1 U1 HU) μ1.
Proof.
  split.
  - intros U (V&?&Hequiv). eapply (sigma_proper _ _ _ (U1 ∩ V)); eauto.
    intros z; split.
    ** intros (x&?&<-). split.
       *** destruct x; eauto.
       *** by apply Hequiv.
    ** intros (HU1&HV). exists (exist _ _ HU1); split; eauto.
       apply Hequiv => //=.
  - intros U HF. rewrite //=.
    apply measure_proper.
    split.
    * intros (Hp&?). exists (exist _ _ Hp); split; eauto.
    * intros ((z&Hpf)&?&?). subst => //=. exists Hpf; auto.
Qed.

Lemma mod0_embedding_sigma_inv {A1 A2: Type} F1 F2
  (μ1: @measure A1 F1) (μ2: @measure A2 F2) f U:
    is_mod0_embedding f μ1 μ2 →
    F2 U →
    F1 (fun_inv f U).
Proof.
  intros Hmod. eapply pt_hom_sigma; eauto. apply mod0_embedding_hom. eauto.
Qed.

Lemma mod0_embedding_sigma_img {A1 A2: Type} F1 F2
  (μ1: @measure A1 F1) (μ2: @measure A2 F2) f U:
    is_mod0_embedding f μ1 μ2 →
    F1 U →
    F2 (fun_img f U).
Proof.
  intros Hmod. eapply pt_img_hom_sigma; eauto. apply mod0_embedding_img_hom. eauto.
Qed.

Lemma mod0_embedding_meas_inv {A1 A2: Type} F1 F2
  (μ1: @measure A1 F1) (μ2: @measure A2 F2) f U:
    is_mod0_embedding f μ1 μ2 →
    F2 U →
    μ1 (fun_inv f U) = μ2 U.
Proof.
  intros Hmod. symmetry. eapply pt_hom_meas; eauto. apply mod0_embedding_hom. done.
Qed.

Lemma mod0_embedding_meas_img {A1 A2: Type} F1 F2
  (μ1: @measure A1 F1) (μ2: @measure A2 F2) f U:
    is_mod0_embedding f μ1 μ2 →
    F1 U →
    μ2 (fun_img f U) = μ1 U.
Proof.
  intros Hmod. symmetry. eapply pt_img_hom_meas; eauto. apply mod0_embedding_img_hom. done.
Qed.

Lemma mod0_embedding_meas_full {A1 A2: Type} F1 F2
      (μ1: @measure A1 F1) (μ2: @measure A2 F2) f:
    is_mod0_embedding f μ1 μ2 →
    μ1 (λ _, True) = μ2 (λ _, True).
Proof.
  intros He. transitivity (μ1 (fun_inv f (λ _, True))).
  { apply measure_proper. clear; split; intros; firstorder. }
  apply mod0_embedding_meas_inv; eauto.
Qed.

Lemma mod0_embedding_ae_inv  {A1 A2: Type} F1 F2
      (μ1: @measure A1 F1) (μ2: @measure A2 F2) f U:
    is_mod0_embedding f μ1 μ2 →
    almost_everywhere_meas μ2 U →
    almost_everywhere_meas μ1 (fun_inv f U).
Proof.
  intros Hmod (HF&Hmea).
  assert (F1 (compl (fun_inv f U))).
  { apply sigma_closed_complements. eapply mod0_embedding_sigma_inv; eauto.
    apply sigma_closed_complements in HF. rewrite compl_involutive in HF *. done. }
  split; auto.
  apply compl_meas_0_full; auto.
  erewrite mod0_embedding_meas_inv; eauto; last first.
  { apply sigma_closed_complements in HF. rewrite compl_involutive in HF *. done. }
  transitivity (μ2 (λ _, True)).
  { apply almost_everywhere_meas_meas_full. split; eauto. }
  symmetry; eapply mod0_embedding_meas_full; eauto.
Qed.

Lemma mod0_embedding_ae_img  {A1 A2: Type} F1 F2
      (μ1: @measure A1 F1) (μ2: @measure A2 F2) f U:
    is_mod0_embedding f μ1 μ2 →
    almost_everywhere_meas μ1 U →
    almost_everywhere_meas μ2 (fun_img f U).
Proof.
  intros Hmod (HF&Hmea).
  assert (F2 (compl (fun_img f U))).
  { apply sigma_closed_complements. eapply mod0_embedding_sigma_img; eauto.
    apply sigma_closed_complements in HF. rewrite compl_involutive in HF *. done. }
  split; auto.
  apply compl_meas_0_full; auto.
  erewrite mod0_embedding_meas_img; eauto; last first.
  { apply sigma_closed_complements in HF. rewrite compl_involutive in HF *. done. }
  transitivity (μ1 (λ _, True)).
  { apply almost_everywhere_meas_meas_full. split; eauto. }
  eapply mod0_embedding_meas_full; eauto.
Qed.

Lemma fun_img_comp {A B C: Type} (f1: A → B) (f2: B → C) U:
  fun_img (λ x, f2 (f1 x)) U ≡ fun_img f2 (fun_img f1 U).
Proof.
  intros z. split; firstorder.
Qed.

Lemma is_mod0_embedding_id {A} {F} (μ: @measure A F):
  is_mod0_embedding id μ μ.
Proof.
  assert (Hequiv: ∀ U : (A → Prop), fun_img id U ≡ U).
  { intros U. rewrite /fun_img. clear. split; firstorder. }
  split.
  - rewrite Hequiv. apply almost_everywhere_meas_True.
  - done.
  - apply is_pt_hom_id.
  - apply is_pt_img_hom_id.
Qed.

Lemma is_mod0_embedding_comp {A1 A2 A3}
      F1 F2 F3
      (f1: A1 → A2) (f2 : A2 → A3) (μ1: @measure A1 F1) (μ2: @measure A2 F2) (μ3: @measure A3 F3):
  is_mod0_embedding f1 μ1 μ2 →
  is_mod0_embedding f2 μ2 μ3 →
  is_mod0_embedding (λ x, f2 (f1 x)) μ1 μ3.
Proof.
  intros Hhom1 Hhom2.
  split.
  - rewrite fun_img_comp.
    eapply (mod0_embedding_ae_img); eauto.
    eapply (mod0_embedding_ae_img); eauto.
  - intros x y Heq.
    eapply mod0_embedding_inj in Heq; eauto.
    eapply mod0_embedding_inj in Heq; eauto.
  - eapply is_pt_hom_comp.
    eapply mod0_embedding_hom; first eauto.
    eapply mod0_embedding_hom; first eauto.
  - eapply is_pt_img_hom_comp.
    * eapply mod0_embedding_img_hom. eauto.
    * eapply mod0_embedding_img_hom. eauto.
Qed.

Section mod0_props.

  Context {A1 A2: Type}.
  Context {F1 : measurable_space A1}.
  Context {F2 : measurable_space A2}.
  Context (μ1: @measure A1 F1).
  Context (μ2: @measure A2 F2).

  Lemma is_mod0_iso_inv_hom U1 U2 f:
    is_mod0_hom U1 U2 f μ1 μ2 →
    (∃ f', is_mod0_hom U2 U1 f' μ2 μ1 ∧
      (∀ x, f (f' x) = x) ∧ (∀ y, f' (f y) = y)) →
    is_mod0_iso U1 U2 f μ1 μ2.
  Proof.
    intros Hhom (f'&Hhom'&Hrl&Hlr).
    unshelve (econstructor).
    - eapply mod0_hom_ae1. eauto.
    - eapply @mod0_hom_ae2 in Hhom. eauto.
    - apply is_pt_iso_inv_hom.
      * apply mod0_hom_is_hom.
      * exists f'. split.
        ** assert (mod0_hom_ae2 U1 U2 f μ1 μ2 Hhom =
                   mod0_hom_ae1 U2 U1 f' μ2 μ1 Hhom') as -> by apply classical_proof_irrelevance.
           assert (mod0_hom_ae1 U1 U2 f μ1 μ2 Hhom =
                   mod0_hom_ae2 U2 U1 f' μ2 μ1 Hhom') as -> by apply classical_proof_irrelevance.
           eapply (mod0_hom_is_hom _ _ _ _ _ Hhom').
        ** split; eauto.
  Qed.

  Lemma is_mod0_iso_common_embedding U1 U2 f:
    is_mod0_iso U1 U2 f μ1 μ2 →
    (∃ (G: measurable_space (sig U1)) (μ: @measure _ G),
        is_mod0_embedding sval μ μ1 ∧ is_mod0_embedding (λ x, sval (f x)) μ μ2).
  Proof.
    intros Hiso.
    eexists.
    exists (sub_measure μ1 U1 (almost_everywhere_meas_meas μ1 _ (mod0_iso_ae1 _ _ _ _ _ Hiso))).
    split.
    * split.
      ** eapply almost_everywhere_meas_ext; last first.
         { eapply mod0_iso_ae1; eauto. }
         rewrite /fun_img. intros x.
         split.
         *** intros HU. exists (exist _ _ HU); split; auto.
         *** intros ((?&?)&(?&?)); eauto. subst => //=.
      ** intros. by apply sval_inj_pi.
      ** apply is_pt_hom_ae_sval. eapply mod0_iso_ae1; eauto.
      ** apply is_pt_img_hom_ae_sval. eapply mod0_iso_ae1; eauto.
    * split.
      ** eapply almost_everywhere_meas_ext; last first.
         { eapply mod0_iso_ae2 in Hiso. eauto. }
         rewrite /fun_img. intros x.
         split.
         *** intros HU.
             exists (iso_inv f (mod0_iso_is_iso _ _ _ _ _ Hiso) (exist _ _ HU)).
             rewrite iso_inv_rinv. done.
         *** intros (?&?&<-). destruct (f _) => //=.
      ** intros ?? ?%sval_inj_pi.
         destruct Hiso as [? ? is_iso].
         eapply pt_iso_inj in is_iso; eauto.
      ** eapply is_pt_hom_comp.
         *** eapply is_pt_hom_iso. eapply (mod0_iso_is_iso _ _ _ _ _ Hiso).
         *** apply is_pt_hom_ae_sval. eapply mod0_iso_ae2 in Hiso; eauto.
      ** eapply is_pt_img_hom_comp.
         *** eapply is_pt_img_hom_iso. eapply (mod0_iso_is_iso _ _ _ _ _ Hiso).
         *** apply is_pt_img_hom_ae_sval. eapply mod0_iso_ae2 in Hiso; eauto.
  Qed.

  Lemma is_mod0_iso_common_embedding':
    (∃ U1 U2 f, is_mod0_iso U1 U2 f μ1 μ2) →
    (∃ B (G : measurable_space B) (μ: @measure _ G) f1 f2, is_mod0_embedding f1 μ μ1 ∧
                                                     is_mod0_embedding f2 μ μ2).
  Proof.
    intros (U1&U2&f&Hmod).
    edestruct (is_mod0_iso_common_embedding) as (?&?&?&?); eauto.
    do 5 eexists; split; eauto.
  Qed.

  Definition common_embedding {B} (f1: B → A1) (f2: B → A2) :
    {x : A1 | fun_img f1 (λ _ : B, True) x} → {x : A2 | fun_img f2 (λ _: B, True) x} :=
    (λ X : {x : A1 | fun_img f1 (λ _ : B, True) x},
           match X with
           | exist z Hex =>
             match constructive_indefinite_description (λ x : B, True ∧ f1 x = z) Hex with
             | exist b (conj H _) =>
               f2 b ↾ ex_intro (λ x : B, True ∧ f2 x = f2 b) b (conj H (erefl (f2 b)))
             end
           end).


  Lemma common_embedding_is_mod0_iso
        B (G : measurable_space B) (μ: @measure _ G) f1 f2:
    is_mod0_embedding f1 μ μ1 →
    is_mod0_embedding f2 μ μ2 →
    is_mod0_iso (fun_img f1 (λ _, True)) (fun_img f2 (λ _, True))
                (common_embedding f1 f2) μ1 μ2.
  Proof.
    intros Hmod1 Hmod2. rewrite /common_embedding.
    unshelve (econstructor).
    * eapply mod0_embedding_ae; eauto.
    * eapply mod0_embedding_ae; eauto.
    * split.
      ** intros (x&?) (y&?).
         destruct constructive_indefinite_description as (?&(?&?)) => //=.
         destruct constructive_indefinite_description as (?&(?&?)) => //=.
         subst. inversion 1. apply sval_inj_pi => //=. f_equal.
         eapply (mod0_embedding_inj f2); eauto.
      ** intros (y&(b&(?&Heq))).
         unshelve (eexists).
         { exists (f1 b). eexists; eauto. }
         rewrite //=.
         destruct constructive_indefinite_description as (?&(?&?)) => //=.
         subst. apply sval_inj_pi => //=. f_equal.
         eapply (mod0_embedding_inj f1); eauto.
      ** intros U (V&?&HVspec).
         exists (fun_img f2 (fun_inv f1 V)). split.
         *** eapply pt_img_hom_sigma; first eapply mod0_embedding_img_hom; eauto.
             eapply pt_hom_sigma; first eapply mod0_embedding_hom; eauto.
         *** intros (?&?). rewrite //=.
             split.
             **** intros ((?&Himg)&Hspec).
                  destruct constructive_indefinite_description as (x1&?&Heq).
                  destruct Hspec as (?&Heq').
                  subst. exists x1; split; eauto.
                  ***** rewrite /fun_inv. by eapply (HVspec (exist _ _ Himg)).
                  ***** inversion Heq'. done.
             **** intros (b&Hinv&?). subst.
                  rewrite /fun_inv in Hinv.
                  unshelve (eexists (exist _ (f1 b) _)).
                  { eexists; eauto. }
                  split.
                  ***** eapply HVspec => //=.
                  ***** destruct constructive_indefinite_description as (?&?&?).
                  apply sval_inj_pi => //=.
                  f_equal. eapply (mod0_embedding_inj f1); eauto.
      ** intros U (V&?&HVspec).
         exists (fun_img f1 (fun_inv f2 V)). split.
         *** eapply pt_img_hom_sigma; first eapply mod0_embedding_img_hom; eauto.
             eapply pt_hom_sigma; first eapply mod0_embedding_hom; eauto.
         *** intros (?&?). rewrite //=.
             split.
             **** rewrite /fun_inv.
                  destruct constructive_indefinite_description as (x1&?&Heq).
                  subst. rewrite /fun_img. intros HU. exists x1; split; eauto.
                  eapply HVspec in HU. eauto.
             **** rewrite /fun_inv.
                  intros (b&Hinv&?). subst.
                  destruct constructive_indefinite_description as (x1&?&Heq).
                  eapply HVspec. rewrite //=. cut (x1 = b); intros; subst; eauto.
                  eapply (mod0_embedding_inj f1); eauto.
      ** intros U (V&?&HVspec). rewrite //=.
         transitivity (μ (fun_inv f1 V)).
         { erewrite <-pt_hom_meas; eauto; last first.
           { eapply mod0_embedding_hom; eauto. }
           rewrite [a in _ = a](almost_everywhere_meas_inter_measure _ _ _
                                                                (mod0_embedding_ae _ _ _ Hmod1))
           //.
           apply measure_proper. intros x.
           split.
           - intros (HP&?). split; auto. eapply (HVspec (exist _ _ HP)). eauto.
           - intros (HV&HU). exists HU. apply HVspec. eauto. }
         transitivity (μ2 (fun_img f2 (fun_inv f1 V))).
         { apply pt_img_hom_meas; eauto.
           * apply mod0_embedding_img_hom; eauto.
           * eapply pt_hom_sigma; first eapply mod0_embedding_hom; eauto.
         }
         eapply measure_proper.
         intros x. split.
         *** intros (z&Hinv&Heq).
             subst. unshelve (eexists).
             { exists z. eauto. }
             rewrite /fun_inv in Hinv.
             unshelve (eexists).
             { exists (f1 z). eexists; eauto. }
             split.
             **** eapply HVspec; eauto.
             **** destruct constructive_indefinite_description as (x1&?&Heq).
                  apply sval_inj_pi => //=.
                  f_equal.
                  eapply (mod0_embedding_inj f1); eauto.
         *** rewrite /fun_img => //=. intros ((x'&?&Heq)&Hspec).
             subst. eexists; split; eauto.
             destruct Hspec as ((?&?)&HU&?).
             destruct constructive_indefinite_description as (x1&?&Heq).
             subst. rewrite /fun_inv.
             inversion H0. subst.
             assert (x' = x1).
             { eapply (mod0_embedding_inj f2); eauto. }
             subst. eapply HVspec in HU. eauto.
      ** intros U (V&?&HVspec). rewrite //=.
         transitivity (μ (fun_inv f2 V)).
         { erewrite <-pt_hom_meas; eauto; last first.
           { eapply mod0_embedding_hom; eauto. }
           rewrite [a in _ = a](almost_everywhere_meas_inter_measure _ _ _
                                                                (mod0_embedding_ae _ _ _ Hmod2))
           //.
           apply measure_proper. intros x.
           split.
           - intros (HP&?). split; auto. eapply (HVspec (exist _ _ HP)). eauto.
           - intros (HV&HU). exists HU. apply HVspec. eauto. }
         transitivity (μ1 (fun_img f1 (fun_inv f2 V))).
         { apply pt_img_hom_meas; eauto.
           * apply mod0_embedding_img_hom; eauto.
           * eapply pt_hom_sigma; first eapply mod0_embedding_hom; eauto.
         }
         eapply measure_proper.
         intros x. split.
         *** intros (z&Hinv&Heq).
             subst. unshelve (eexists).
             { exists z. eauto. }
             rewrite /fun_inv in Hinv.
             rewrite /fun_inv.
             destruct constructive_indefinite_description as (x1&?&Heq).
             eapply HVspec => //=.
             assert (x1 = z).
             { eapply (mod0_embedding_inj f1); eauto. }
             subst. eauto.
         *** intros (Hpf&Hinv).
             rewrite /fun_inv in Hinv.
             rewrite /fun_inv.
             destruct constructive_indefinite_description as (x1&?&Heq).
             rewrite /fun_img. eexists. split; eauto. eapply HVspec in Hinv.
             rewrite //= in Hinv.
  Qed.

  Lemma common_embedding_is_mod0_iso':
    (∃ B (G : measurable_space B) (μ: @measure _ G) f1 f2, is_mod0_embedding f1 μ μ1 ∧
                                                     is_mod0_embedding f2 μ μ2) →
    (∃ U1 U2 f, is_mod0_iso U1 U2 f μ1 μ2).
  Proof.
    - intros (B&G&μ&f1&f2&Hmod1&Hmod2).
      exists (fun_img f1 (λ _, True)), (fun_img f2 (λ _, True)).
      eexists.
      eapply common_embedding_is_mod0_iso; eauto.
  Qed.


  Section pullback.
  Context {C: Type}.
  Context (G: measurable_space C).
  Context (μ: @measure C G).
  Context (f1: A1 → C).
  Context (f2: A2 → C).
  Context (Hmod1: is_mod0_embedding f1 μ1 μ).
  Context (Hmod2: is_mod0_embedding f2 μ2 μ).

  Definition mod0_pullback : Type := { bs: A1 * A2 | f1 (fst bs) = f2 (snd bs) }.

  Lemma mod0_pullback_sigma_top:
    G (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f1 (sval x).1)
               (λ _ : mod0_pullback, True)).
  Proof.
    rewrite //=.
    specialize (mod0_embedding_ae _ _ _ Hmod1) => Hae1.
    apply almost_everywhere_meas_meas in Hae1.
    specialize (mod0_embedding_ae _ _ _ Hmod2) => Hae2.
    apply almost_everywhere_meas_meas in Hae2.
    eapply sigma_proper; last first.
    { eapply sigma_closed_pair_intersect; [ apply Hae1 | apply Hae2 ]. }
    intros z. split.
    * intros (((a1&a2)&Heqa)&HU&Heq').
      split.
      ** exists a1. eauto.
      ** exists a2. rewrite //= in Heq'. rewrite //= in Heqa. split; congruence.
    * intros (Hf1&Hf2). destruct Hf1 as (a1&(?&Heq1)). destruct Hf2 as (a2&(?&Heq2)).
      subst. symmetry in Heq2. exists (exist _ (a1, a2) Heq2). split; eauto.
  Qed.

  Lemma mod0_pullback_sigma_compl U:
    G (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f1 (sval x).1) U)
    → G (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f1 (sval x).1) (compl U)).
  Proof.
    intros HG%sigma_closed_complements.
    eapply sigma_proper; last first.
    { apply sigma_closed_pair_intersect.
      - apply HG.
      - apply mod0_pullback_sigma_top.
    }
    intros z. split.
    * intros (((a1&a2)&hpf)&Hcomp&Heq').
      split.
      {
        intros (((a1'&a2')&hpf')&?&Heq'').
        eapply Hcomp.
        assert (exist _ _ hpf = exist _ _ hpf') as ->; eauto.
        apply sval_inj_pi => //=. f_equal.
        ** eapply (mod0_embedding_inj f1); eauto.
           rewrite //= in Heq' Heq''. congruence.
        ** eapply (mod0_embedding_inj f2); eauto.
           clear -Heq' Heq'' hpf hpf'. rewrite //= in Heq' Heq''.
           rewrite //= in hpf hpf'. congruence.
      }
      { eexists; split; eauto. }
    * intros (Hcomp&Himg).
      destruct Himg as (x&?&Heq).
      exists x. split; auto.
      intros HU. eapply Hcomp. eexists; split; eauto.
  Qed.

  Lemma mod0_pullback_sigma_union Ps:
    (∀ i : nat, G (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f1 (sval x).1) (Ps i)))
    → G (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f1 (sval x).1) (unionF Ps)).
  Proof.
    intros HPs%sigma_closed_unions.
    rewrite img_union. done.
  Qed.

  Definition mod0_pullback_sigma : sigma_algebra mod0_pullback.
  Proof.
    unshelve (econstructor).
    - intros U. exact (G (fun_img (λ x, f1 (fst (sval x))) U)).
    - intros U U' Heq. rewrite /fun_img.
      assert (eq_prop (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f1 (sval x).1) U')
                      (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f1 (sval x).1) U))
             as ->; eauto.
      intros z; rewrite /fun_img; split.
      * intros (x&HU&Heq'). exists x. split; eauto. eapply Heq. done.
      * intros (x&HU&Heq'). exists x. split; eauto. eapply Heq. done.
    - apply mod0_pullback_sigma_top.
    - apply mod0_pullback_sigma_compl.
    - apply mod0_pullback_sigma_union.
  Defined.

  Instance mod0_pullback_measurable_space : measurable_space mod0_pullback.
  Proof. econstructor. eapply mod0_pullback_sigma. Defined.

  Definition mod0_pullback_measure: measure mod0_pullback.
  Proof.
    unshelve (econstructor).
    - intros U. apply (μ1 (fun_img (λ x, (fst (sval x))) U)).
    - intros U U' Heq.
      assert (eq_prop (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, (sval x).1) U')
                      (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, (sval x).1) U))
             as ->; eauto.
      intros z; rewrite /fun_img; split.
      * intros (x&HU&Heq'). exists x. split; eauto. eapply Heq. done.
      * intros (x&HU&Heq'). exists x. split; eauto. eapply Heq. done.
    - rewrite //=.
    - rewrite //=. etransitivity; first (apply measure_proper); last apply measure_empty.
      intros z. split.
      * intros (?&[]&?).
      * inversion 1.
    - rewrite //= => Us Hin Hdisj.
      setoid_rewrite img_union.
      eapply measure_additivity.
      * intros i. specialize (Hin i).
        eapply @pt_hom_sigma in Hin; last (eapply (mod0_embedding_hom _ _ _ Hmod1); eauto).
        eapply sigma_proper; last eapply Hin.
        intros z; split.
        ** intros (?&?&?). eexists; split; eauto. f_equal; done.
        ** rewrite /fun_inv. intros (?&?&?).
           eexists; split; eauto. eapply (mod0_embedding_inj f1); eauto.
      * intros i j Hneq x (Hin1&Hin2).
        destruct Hin1 as (((a1&a2)&Hpf)&?&Heq).
        destruct Hin2 as (((a1'&a2')&Hpf')&?&Heq').
        assert (a1' = a1).
        { rewrite //= in Heq Heq'. congruence. }
        subst.
        assert (a2' = a2).
        { eapply (mod0_embedding_inj f2); eauto. clear -Hpf Hpf'. rewrite //= in Hpf Hpf'.
          congruence. }
        subst.
        eapply (Hdisj i j); eauto. split; eauto.
        assert (Hpf = Hpf') as ->; eauto.
        { apply classical_proof_irrelevance. }
  Defined.

  Lemma mod0_pullback_embedding1_hom:
    is_pt_hom (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, (sval x).1) mod0_pullback_measure μ1.
  Proof.
    assert (Hequiv: ∀ U, F1 U →
                 eq_prop (fun_img f1 U ∩ fun_img f2 (λ _ : A2, True))
                         (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f1 (sval x).1)
                                  (fun_inv (λ x, (sval x).1) U))).
    { intros ?? z. split.
        - intros (Himg1&Himg2).
          destruct Himg1 as (x1&HU&Heq1).
          destruct Himg2 as (x2&?&Heq2).
          subst. symmetry in Heq2.
          rewrite /fun_inv//=. exists (exist _ (x1, x2) Heq2) => //=; split; eauto.
        - intros (((x1&x2)&Hpf)&?&Heqz).
          split.
          * eexists; eauto.
          * exists x2; eauto. split; auto. clear -Hpf Heqz. rewrite //= in Hpf Heqz.
            congruence.
    }
    assert (∀ U, F1 U → mod0_pullback_sigma (fun_inv (λ x, (sval x).1) U)).
    {
      intros U HF. rewrite //=. rewrite -Hequiv; eauto.
      eapply sigma_closed_pair_intersect.
      - eapply mod0_embedding_sigma_img; eauto.
      - eapply mod0_embedding_sigma_img; eauto.
    }
    split; auto.
    intros U HU. symmetry. rewrite //=.
    transitivity (μ1 (U ∩ fun_inv f1 (fun_img f2 (λ _, True)))).
    { apply measure_proper.
      intros z; split.
      - intros (((x1&x2)&Hpf)&Hin&Heqz).
        rewrite //= in Hin Heqz.
        subst. split.
        * rewrite /fun_inv//= in Hin.
        * rewrite /fun_inv//=. eexists. eauto.
      - intros (HU'&(x1&?&Hpf)). symmetry in Hpf.
        exists (exist _ (z, x1) Hpf) => //=.
    }
    symmetry; apply almost_everywhere_meas_inter_measure; eauto.
    eapply mod0_embedding_ae_inv; eauto.
    eapply mod0_embedding_ae_img; eauto.
  Qed.

  Lemma mod0_pullback_embedding1_img_hom:
    is_pt_img_hom (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, (sval x).1) mod0_pullback_measure μ1.
  Proof.
    split; auto.
    rewrite //=. intros U HF.
    eapply (mod0_embedding_sigma_inv) in HF; last eapply Hmod1.
    eapply sigma_proper; eauto.
    intros z. split.
    - intros (((x1&x2)&Hpf)&HU&Heq1).
      subst. eexists; split; eauto.
    - intros (((x1&x2)&Hpf)&HU&Heq1).
      subst. eexists; split; eauto => //=.
      rewrite //= in Heq1. eapply (mod0_embedding_inj f1); eauto.
  Qed.

  Lemma mod0_pullback_embedding1:
    is_mod0_embedding (λ x, (fst (sval x))) mod0_pullback_measure μ1.
  Proof.
    split.
    - eapply (almost_everywhere_meas_ext _ (fun_inv f1 (fun_img f2 (λ _, True)))); last first.
      {
        eapply mod0_embedding_ae_inv; eauto.
        eapply mod0_embedding_ae_img; eauto.
      }
      intros x. split.
      * intros (x'&?&Hpf).
        symmetry in Hpf.
        exists (exist _ (x, x') Hpf).
        split; eauto.
      * intros ((?&x')&?&Hpf).
        subst. rewrite //=. eexists; split; eauto.
    - intros ((a1&a2)&Hpf) ((a1'&a2')&Hpf'). rewrite //= => ?; subst.
      apply sval_inj_pi => //=. f_equal.
      rewrite //= in Hpf Hpf'.
      eapply (mod0_embedding_inj f2); eauto. congruence.
    - apply mod0_pullback_embedding1_hom.
    - apply mod0_pullback_embedding1_img_hom.
  Qed.

  Lemma mod0_pullback_embedding2_hom:
    is_pt_hom (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, (sval x).2) mod0_pullback_measure μ2.
  Proof.
    assert (Hequiv: ∀ U, F2 U →
                 eq_prop (fun_img f2 U ∩ fun_img f1 (λ _ : A1, True))
                         (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f2 (sval x).2)
                                  (fun_inv (λ x, (sval x).2) U))).
    { intros ?? z. split.
        - intros (Himg1&Himg2).
          destruct Himg1 as (x1&HU&Heq1).
          destruct Himg2 as (x2&?&Heq2).
          subst.
          rewrite /fun_inv//=. exists (exist _ (x2, x1) Heq2) => //=; split; eauto.
        - intros (((x1&x2)&Hpf)&?&Heqz).
          split.
          * eexists; eauto.
          * exists x1; eauto. split; auto. clear -Hpf Heqz. rewrite //= in Hpf Heqz.
            congruence.
    }
    assert (Hequiv':
              ∀ U, eq_prop (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f2 (sval x).2) U)
                           (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, f1 (sval x).1) U)).
    { intros U z.  split.
      - intros (x&?&Hf2). eexists; split ;eauto.
        destruct x as (?&Heq). rewrite //= in Hf2 *. congruence.
      - intros (x&?&Hf1). eexists; split ;eauto.
        destruct x as (?&Heq). rewrite //= in Hf1 *. congruence.
    }
    assert (∀ U, F2 U → mod0_pullback_sigma (fun_inv (λ x, (sval x).2) U)).
    {
      intros U HF. rewrite //=. rewrite -Hequiv' -Hequiv; eauto.
      eapply sigma_closed_pair_intersect.
      - eapply mod0_embedding_sigma_img; eauto.
      - eapply mod0_embedding_sigma_img; eauto.
    }
    split; auto.
    intros U HU. symmetry. rewrite //=.
    transitivity (μ (fun_img f2 U)); last first.
    { apply mod0_embedding_meas_img; eauto. }
    symmetry.
    specialize (mod0_embedding_ae _ _ _ Hmod1) => Hae.
    erewrite almost_everywhere_meas_inter_measure; eauto; last first.
    { eapply mod0_embedding_sigma_img; eauto. }
    erewrite <-(mod0_embedding_meas_inv _ _ _ _ _ _ Hmod1); last first.
    { apply sigma_closed_pair_intersect.
      - eapply mod0_embedding_sigma_img; eauto.
      - eapply mod0_embedding_sigma_img; eauto.
    }
    apply measure_proper.
    intros x1. split.
    - rewrite /fun_inv.
      intros (Himg2&Himg1).
      destruct Himg2 as (x2&?&Heq).
      symmetry in Heq.
      exists (exist _ (x1, x2) Heq). split; eauto.
    - intros (((x1'&x2')&Hpf)&?&Heq).
      rewrite //= in Heq. subst.
      eexists.
      * eexists; eauto.
      * eexists; eauto.
  Qed.

  Lemma mod0_pullback_embedding2_img_hom:
    is_pt_img_hom (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2}, (sval x).2) mod0_pullback_measure μ2.
  Proof.
    assert (∀ U : {bs : A1 * A2 | f1 bs.1 = f2 bs.2} → Prop,
               mod0_pullback_sigma U → F2 (fun_img (λ x : {bs : A1 * A2 | f1 bs.1 = f2 bs.2},
                                                          (sval x).2) U)).
    {
      rewrite //=. intros U HF.
      eapply (mod0_embedding_sigma_inv) in HF; last eapply Hmod2.
      eapply sigma_proper; eauto.
      {
        intros z. split.
        - intros (((x1&x2)&Hpf)&HU&Heq1).
          subst. eexists; split; eauto.
        - intros (((x1&x2)&Hpf)&HU&Heq1).
          subst. eexists; split; eauto => //=.
          rewrite //= in Heq1. eapply (mod0_embedding_inj f2); eauto.
          rewrite //= in Hpf HU. congruence.
      }
    }
    split; auto.
    - rewrite //= => U HG.
      erewrite <-(mod0_embedding_meas_img _ _ _ _ _ _ Hmod1); eauto; last first.
      { eapply mod0_pullback_embedding1_img_hom. eauto. }
      symmetry.
      erewrite <-(mod0_embedding_meas_img _ _ _ _ _ _ Hmod2); eauto.
      apply measure_proper.
      intros z; split.
      * intros (x2&Himg&?).
        destruct Himg as (((x1&x2')&Hpf)&Heq1&Heq2).
        exists x1. rewrite /fun_img; split.
        **  exists (exist _ (x1, x2') Hpf).
            rewrite //=.
        ** subst. rewrite //=.
      * intros (x1&Himg&?).
        destruct Himg as (((x1'&x2)&Hpf)&Heq1&Heq2).
        exists x2. rewrite /fun_img; split.
        **  exists (exist _ (x1', x2) Hpf).
            rewrite //=.
        ** subst. rewrite //=.
  Qed.

  Lemma mod0_pullback_embedding2:
    is_mod0_embedding (λ x, (snd (sval x))) mod0_pullback_measure μ2.
  Proof.
    split.
    - eapply (almost_everywhere_meas_ext _ (fun_inv f2 (fun_img f1 (λ _, True)))); last first.
      {
        eapply mod0_embedding_ae_inv; eauto.
        eapply mod0_embedding_ae_img; eauto.
      }
      intros x. split.
      * intros (x'&?&Hpf).
        exists (exist _ (x', x) Hpf).
        split; eauto.
      * intros ((?&x')&?&Hpf).
        subst. rewrite //=. eexists; split; eauto.
    - intros ((a1&a2)&Hpf) ((a1'&a2')&Hpf'). rewrite //= => ?; subst.
      apply sval_inj_pi => //=. f_equal.
      rewrite //= in Hpf Hpf'.
      eapply (mod0_embedding_inj f1); eauto. congruence.
    - apply mod0_pullback_embedding2_hom.
    - apply mod0_pullback_embedding2_img_hom.
  Qed.
  End pullback.

  Lemma mod0_embedding_scal p f1:
    is_mod0_embedding f1 μ1 μ2 →
    is_mod0_embedding f1 (scal_measure p μ1) (scal_measure p μ2).
  Proof.
    intros Hmod.
    split.
    - destruct (mod0_embedding_ae _ _ _ Hmod) as (?&Heq). split; auto.
      rewrite //= Heq. nra.
    - intros x y ?. eapply mod0_embedding_inj; eauto.
    - split.
      * intros. eapply mod0_embedding_sigma_inv; eauto.
      * intros U H => //=. erewrite mod0_embedding_meas_inv; eauto.
    - split.
      * intros. eapply mod0_embedding_sigma_img; eauto.
      * intros U H => //=. erewrite mod0_embedding_meas_img; eauto.
  Qed.

  Lemma mod0_embedding_sum
    {A1' A2': Type}
    {F1' : measurable_space A1'}
    {F2' : measurable_space A2'}
    (μ1': @measure _ F1')
    (μ2': @measure _ F2')
    f1 f2:
    is_mod0_embedding f1 μ1 μ1' →
    is_mod0_embedding f2 μ2 μ2' →
    is_mod0_embedding (λ x, match x with
                            | inl x1 => inl (f1 x1)
                            | inr x2 => inr (f2 x2)
                            end)
                      (disjoint_sum_measure μ1 μ2) (disjoint_sum_measure μ1' μ2').
  Proof.
    intros Hmod1 Hmod2.
    assert (Hequiv1: compl (fun_img f1 (λ _ : A1, True)) ≡
                     fun_inv inl (compl
                                    (fun_img (λ x : A1 + A2, match x with
                                                             | inl x1 => inl (f1 x1)
                                                             | inr x2 => inr (f2 x2)
                                                             end)
                                             (λ _ : A1 + A2, True)))).
    {
      intros z. split.
      * intros Hcomp. rewrite /fun_inv//=. intros Hfalse.
        apply Hcomp. destruct Hfalse as ([a1|a2]&?&?); last done.
        exists a1. split; eauto. congruence.
      * rewrite /fun_inv. intros Hcomp.
        intros Hfalse. destruct Hfalse as (a1&?&?).
        eapply Hcomp. exists (inl a1). subst. split; auto.
    }
    assert (Hequiv2: compl (fun_img f2 (λ _ : A2, True)) ≡
                     fun_inv inr (compl
                                    (fun_img (λ x : A1 + A2, match x with
                                                             | inl x1 => inl (f1 x1)
                                                             | inr x2 => inr (f2 x2)
                                                             end)
                                             (λ _ : A1 + A2, True)))).
    {
      intros z. split.
      * intros Hcomp. rewrite /fun_inv//=. intros Hfalse.
        apply Hcomp. destruct Hfalse as ([a1|a2]&?&?); first done.
        exists a2. split; eauto. congruence.
      * rewrite /fun_inv. intros Hcomp.
        intros Hfalse. destruct Hfalse as (a1&?&?).
        eapply Hcomp. exists (inr a1). subst. split; auto.
    }
    split.
    - split.
      * split.
        ** rewrite -Hequiv1.
           apply sigma_closed_complements.
           eapply mod0_embedding_sigma_img; eauto.
        ** rewrite -Hequiv2.
           apply sigma_closed_complements.
           eapply mod0_embedding_sigma_img; eauto.
      * rewrite //=. rewrite -Hequiv1 -Hequiv2.
        destruct (mod0_embedding_ae _ _ _ Hmod1) as (?&->).
        destruct (mod0_embedding_ae _ _ _ Hmod2) as (?&->).
        nra.
    - intros [|] [|]; inversion 1 as [Heq]; f_equal.
      * eapply (mod0_embedding_inj f1); eauto.
      * eapply (mod0_embedding_inj f2); eauto.
    - eapply (mod0_embedding_hom) in Hmod1.
      eapply (mod0_embedding_hom) in Hmod2.
      apply is_pt_hom_sum; eauto. 
    - eapply (mod0_embedding_img_hom) in Hmod1.
      eapply (mod0_embedding_img_hom) in Hmod2.
      apply is_pt_img_hom_sum; eauto.
  Qed.

  Lemma is_pt_iso_mod0_embedding f:
    is_pt_iso f μ1 μ2 →
    is_mod0_embedding f μ1 μ2.
  Proof.
    intros Hiso.
    split.
    - eapply iso_ae_img; eauto.
    - intros; eapply pt_iso_inj; eauto.
    - by apply is_pt_hom_iso.
    - by apply is_pt_img_hom_iso.
  Qed.

End mod0_props.



(*
Record mod0_iso {A1 A2} {F1 : sigma_algebra A1} {F2: sigma_algebra A2}
       (μ1: measure F1) (μ2: measure F2) :=
  {
    mod0_iso_s1: A1 → Prop;
    mod0_iso_s2: A2 → Prop;
    mod0_iso_ae1: almost_everywhere_meas μ1 mod0_iso_s1;
    mod0_iso_ae2: almost_everywhere_meas μ2 mod0_iso_s2;
    mod0_iso_fun :> sig mod0_iso_s1 → sig mod0_iso_s2;
    mod0_iso_is_iso: is_pt_iso mod0_iso_fun
                       (sub_measure μ1 mod0_iso_s1 (almost_everywhere_meas_meas μ1 _ mod0_iso_ae1))
                       (sub_measure μ2 mod0_iso_s2 (almost_everywhere_meas_meas μ2 _ mod0_iso_ae2))
  }.

Arguments mod0_iso_s1 {_ _ _ _ _ _} _.
Arguments mod0_iso_s2 {_ _ _ _ _ _} _.
*)
Arguments mod0_iso_ae1 {_ _ _ _ _ _ _ _} _.
Arguments mod0_iso_ae2 {_ _ _ _ _ _ _ _} _.
(*
Arguments mod0_iso_fun {_ _ _ _ _ _} _.
*)
Arguments mod0_iso_is_iso {_ _ _ _ _ _ _ _ _} _.
