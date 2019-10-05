Require Import Reals Psatz Omega.
From discprob.measure Require Export measures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.

Record outer_measure (A: Type)  :=
  { outer_measure_fun :> (A → Prop) → R;
    outer_measure_mono : Proper (@le_prop A ==> Rle) outer_measure_fun;
    outer_measure_empty : outer_measure_fun ∅ = 0;
    outer_measure_subadditivity : ∀ U: nat → (A → Prop),
        ex_series (λ n, outer_measure_fun (U n)) →
        outer_measure_fun (unionF U) <= Series (λ n, outer_measure_fun (U n))
  }.

Arguments outer_measure_empty {_} _.
Arguments outer_measure_subadditivity {_}.

Global Instance outer_measure_proper {A: Type} (μ: outer_measure A) :
  Proper (@eq_prop A ==> eq) (@outer_measure_fun _ μ).
Proof.
  intros U U' Heq.
  apply Rle_antisym; apply outer_measure_mono; rewrite Heq; done.
Qed.

Definition outer_measurable {A} (μ: outer_measure A) (U: A → Prop) :=
  ∀ V, μ V = μ (V ∩ U) + μ (V ∩ (compl U)).

Global Instance outer_measurable_proper {A: Type} (μ: outer_measure A) :
  Proper (@eq_prop A ==> iff) (@outer_measurable _ μ).
Proof.
  intros U V Heq.
  rewrite /outer_measurable; split.
  - intros ??. rewrite -Heq. eauto.
  - intros ??. rewrite Heq. eauto.
Qed.

Hint Resolve outer_measure_empty.

Section outer_measure_props.
  Context {A: Type}.
  Context (μ : @outer_measure A).

  Lemma outer_measure_nonneg U:
    0 <= μ U.
  Proof.
    rewrite -(outer_measure_empty μ). apply outer_measure_mono. intros x [].
  Qed.

  Hint Resolve outer_measure_nonneg Rle_ge Rge_le.

  Lemma outer_measure_finite_sub_additivity X Y:
    μ (X ∪ Y) <= μ X + μ Y.
  Proof.
    rewrite union_pair_unionF.
    assert (ex_series (λ n : nat, μ match n with
                          | 0%nat => X
                          | 1%nat => Y
                          | S (S _) => empty_set
                          end)).
    { do 2 apply ex_series_incr_1. exists 0. rewrite outer_measure_empty.
      apply is_series_0 => //=. }

    etransitivity; first eapply outer_measure_subadditivity; auto.
    rewrite Series_incr_1 // Series_incr_1; last first.
    { apply ex_series_incr_1; exists 0; rewrite outer_measure_empty; apply is_series_0 => //=. }
    rewrite outer_measure_empty. rewrite Series_0 => //=. nra.
  Qed.

  Lemma outer_measurable_ge U :
    (∀ V, μ V >= μ (V ∩ U) + μ (V ∩ (compl U))) →
    outer_measurable μ U.
  Proof.
    intros Hge V. apply Rle_antisym; last by (apply Rge_le, Hge).
    setoid_rewrite <-outer_measure_finite_sub_additivity.
    right. apply outer_measure_proper.
    rewrite -intersect_union_l union_compl intersect_top. done.
  Qed.

  Lemma null_outer_measurable U:
    μ U = 0 → outer_measurable μ U.
  Proof.
    intros HU. apply outer_measurable_ge => V.
    assert (μ (V ∩ U) = 0) as ->.
    { apply Rle_antisym; auto. rewrite -HU. apply outer_measure_mono.
      firstorder. }
    rewrite Rplus_0_l. apply Rle_ge, outer_measure_mono.
    firstorder.
  Qed.

  Lemma null_compl_outer_measurable U:
    μ (compl U) = 0 → outer_measurable μ U.
  Proof.
    intros HU. apply outer_measurable_ge => V.
    assert (μ (V ∩ (compl U)) = 0) as ->.
    { apply Rle_antisym; auto. rewrite -HU. apply outer_measure_mono.
      firstorder. }
    rewrite Rplus_0_r. apply Rle_ge, outer_measure_mono.
    firstorder.
  Qed.

  Lemma top_outer_measurable:
    outer_measurable μ (λ _, True).
  Proof. apply null_compl_outer_measurable. by rewrite compl_top. Qed.

  Lemma empty_outer_measurable:
    outer_measurable μ ∅.
  Proof. by apply null_outer_measurable. Qed.

  Lemma compl_outer_measurable U:
    outer_measurable μ U → outer_measurable μ (compl U).
  Proof.
    rewrite /outer_measurable => HU V.
    rewrite HU. rewrite compl_involutive Rplus_comm //.
  Qed.

  Lemma union_outer_measurable U1 U2:
    outer_measurable μ U1 → outer_measurable μ U2 → outer_measurable μ (U1 ∪ U2).
  Proof.
    rewrite /outer_measurable => HU1 HU2 V.
    generalize (HU1 (V ∩ (U1 ∪ U2))).
    assert ((V ∩ (U1 ∪ U2)) ∩ U1 ≡ V ∩ U1) as Hsimpl1
           by firstorder.
    assert ((V ∩ (U1 ∪ U2)) ∩ compl U1 ≡
            ((V ∩ (compl U1)) ∩ U2)) as Hsimpl2
        by firstorder.
    rewrite compl_union.
    rewrite Hsimpl1 Hsimpl2 => ->.
    rewrite Rplus_assoc ?assoc.
    rewrite -HU2. apply HU1.
  Qed.

  Lemma intersect_outer_measurable U1 U2:
    outer_measurable μ U1 → outer_measurable μ U2 → outer_measurable μ (U1 ∩ U2).
  Proof.
    intros. rewrite -(compl_involutive (U1 ∩ U2)) compl_intersect.
    by apply compl_outer_measurable, union_outer_measurable; apply compl_outer_measurable.
  Qed.

  Hint Resolve intersect_outer_measurable union_outer_measurable
               top_outer_measurable empty_outer_measurable compl_outer_measurable.

  Lemma disjoint_unionF_outer_measurable_inequality_sum_n Us:
    disjointF Us →
    (∀ i : nat, outer_measurable μ (Us i)) →
    ∀ V n, sum_n (λ i, μ (V ∩ (Us i))) n <= μ V - μ (V ∩ (compl (unionF Us))).
  Proof.
    intros Hdisj Houter.
    assert (Hind: ∀ n, ∀ V, μ V = sum_n (λ i, μ (V ∩ (Us i))) n
                            + μ (V ∩ (λ x, ∀ i, i ≤ n → ¬ Us i x))).
    { induction n => V.
      - rewrite sum_O. rewrite (Houter O V). f_equal.
        apply outer_measure_proper. intros a.
        split.
        * intros [Hv Hcompl]; split; auto => i' Hle. by inversion Hle; subst.
        * intros [Hv Hcompl]; split; auto. by apply Hcompl.
      - rewrite IHn. rewrite sum_Sn /plus//= Rplus_assoc. f_equal.
        rewrite (Houter (S n) (V ∩ (λ x : A, ∀ i : nat, i ≤ n → ¬ Us i x))).
        f_equal; apply outer_measure_proper.
        * rewrite -assoc. apply intersect_proper; first by reflexivity.
          intros x; split; first by firstorder.
          intros Hin; split; auto. intros i Hle.
          eapply disjoint_elim; try eassumption. apply Hdisj. omega.
        * rewrite -assoc. apply intersect_proper; first by reflexivity.
          intros x; split.
          ** intros [Hin1 Hin2] i. inversion 1; subst; eauto.
          ** intros Hin; split; auto. by apply Hin.
    }
    assert (Hind': ∀ n, ∀ V, μ V >= sum_n (λ i, μ (V ∩ (Us i))) n
                            + μ (V ∩ (compl (unionF Us)))).
    { intros. rewrite (Hind n). apply Rle_ge.
      apply Rplus_le_compat; first reflexivity.
      apply outer_measure_mono. apply intersect_mono; first done.
      firstorder.
    }
    intros. specialize (Hind' n V). nra.
  Qed.

  Lemma disjoint_unionF_outer_measurable_inequality Us:
    disjointF Us →
    (∀ i : nat, outer_measurable μ (Us i)) →
    ∀ V, ex_series (λ i : nat, μ (V ∩ Us i)) ∧
         Series (λ i : nat, μ (V ∩ Us i)) <= μ V - μ (V ∩ compl (unionF Us)).
  Proof.
    intros Hdisj Hmeasurable.
    specialize (disjoint_unionF_outer_measurable_inequality_sum_n Us Hdisj Hmeasurable) => Hind''.
    intros V.
    eapply (ex_series_non_neg_le_const (λ i, μ (V ∩ Us i))) in Hind'' as (Hex&?); auto.
  Qed.

  Lemma disjoint_unionF_outer_measurable Us:
    disjointF Us →
    (∀ i : nat, outer_measurable μ (Us i)) →
    outer_measurable μ (unionF Us).
  Proof.
    intros Hdisj Hmeasurable.
    apply outer_measurable_ge => V.
    edestruct (disjoint_unionF_outer_measurable_inequality Us) as (Hex&?); eauto.
    specialize (outer_measure_subadditivity μ (λ i, V ∩ Us i) Hex); eauto.
    intros Hle. rewrite intersect_unionF_l. nra.
  Qed.

  Lemma unionF_outer_measurable Us:
    (∀ i : nat, outer_measurable μ (Us i)) →
    outer_measurable μ (unionF Us).
  Proof.
    intros Hmeasure.
    rewrite diff_below_unionF.
    apply disjoint_unionF_outer_measurable.
    - apply diff_below_disjoint.
    - apply diff_below_measurable'.
      * auto.
      * apply outer_measurable_proper.
      * apply empty_outer_measurable.
      * apply compl_outer_measurable.
      * apply intersect_outer_measurable.
  Qed.

  Definition outer_measure_sigma : sigma_algebra A.
    refine {| sigma_sets := outer_measurable μ |}.
    - apply top_outer_measurable.
    - apply compl_outer_measurable.
    - apply unionF_outer_measurable.
  Defined.

  Lemma outer_measurable_additivity Us:
    (∀ i, outer_measurable μ (Us i)) →
    disjointF Us →
    is_series (λ n, μ (Us n)) (μ (unionF Us)).
  Proof.
    intros Hmeasur Hdisj.
    assert (Hsimpl1: ∀ i, (unionF Us ∩ Us i) ≡ Us i).
    {
      intros i x; split.
      * intros (?&H); done.
      * intros; split; auto. exists i; auto.
    }
    assert (Hsimpl2: (unionF Us ∩ compl (unionF Us)) ≡ ∅).
    {
      intros x; split; firstorder.
    }
    cut (ex_series (λ i, μ (Us i)) ∧ (Series (λ i, μ (Us i)) = (μ (unionF Us)))).
    { intros (?&<-). by apply Series_correct. }
    specialize (disjoint_unionF_outer_measurable_inequality Us Hdisj Hmeasur (unionF Us)).
    intros (Hex&Hseries). split; auto.
    - eapply ex_series_ext; try eassumption.
      intros n. apply outer_measure_proper, Hsimpl1.
    - rewrite Hsimpl2 outer_measure_empty Rminus_0_r in Hseries * => Hseries.
      apply Rle_antisym.
      * etransitivity; last eapply Hseries.
        right. apply Series_ext => n. by rewrite Hsimpl1.
      * apply outer_measure_subadditivity.
        eapply ex_series_ext; try eassumption.
        intros n. apply outer_measure_proper, Hsimpl1.
  Qed.

  Definition outer_measure_measure {F: measurable_space A} :
    eq_sigma F (outer_measure_sigma) →
    measure A.
  Proof.
    intros Heq.
    refine {| measure_fun := μ |}.
    - abstract (auto).
    - apply outer_measure_empty.
    - abstract (intros; apply outer_measurable_additivity; auto; try (intros; by eapply Heq)).
  Defined.

End outer_measure_props.

Definition full_measure_is_outer {A: Type} {F: measurable_space A} (μ: measure A)
          (Hfull: eq_prop F (λ _, True)) : outer_measure A.
Proof.
  refine {| outer_measure_fun := measure_fun _ μ |}.
  - abstract (intros ?? Hle; apply measure_mono; eauto; try eapply Hfull; done).
  - apply measure_empty.
  - abstract (intros; by apply measure_countable_subadditivity; eauto; intros i; eapply Hfull).
Defined.

Definition outer_pt_measure : outer_measure ().
Proof.
  refine (full_measure_is_outer pt_measure _).
  { rewrite //=. }
Defined.

Lemma outer_pt_measure_sigma_full : ∀ U, outer_measurable (outer_pt_measure) U.
Proof.
  intros U. rewrite /outer_measurable => V //=.
  destruct ClassicalEpsilon.excluded_middle_informative as [HVfull|HVempty].
  {
    destruct (ClassicalEpsilon.excluded_middle_informative (eq_prop U (λ _, True))) as
        [HUfull|HUempty].
    * assert (eq_prop (V ∩ U) (λ _, True)).
      { firstorder. }
      assert (¬ (eq_prop (V ∩ compl U) (λ _, True))).
      { firstorder. exact tt.  }
      do 2 destruct ClassicalEpsilon.excluded_middle_informative; eauto; try nra;
        intuition.
    * assert (¬ (eq_prop (V ∩ U) (λ _, True))).
      { firstorder. }
      assert (eq_prop (compl U) (λ _, True)) as Heq0.
      { intros []; split; auto. intros ? HU. apply HUempty. intros []. split; eauto. }
      assert ((eq_prop (V ∩ compl U) (λ _, True))).
      { rewrite Heq0. firstorder. }
      do 2 destruct ClassicalEpsilon.excluded_middle_informative; eauto; try nra;
        intuition.
  }
  {
    assert (¬ (eq_prop (V ∩ U) (λ _, True))).
    { firstorder. }
    assert (¬ (eq_prop (V ∩ compl U) (λ _, True))).
    { firstorder. }
      do 2 destruct ClassicalEpsilon.excluded_middle_informative; eauto; try nra;
        intuition.
  }
Qed.
