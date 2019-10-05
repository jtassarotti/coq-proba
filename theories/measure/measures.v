Require Import Reals Psatz Omega ClassicalEpsilon.
From stdpp Require Import tactics.
From discprob.basic Require Export base Series_Ext order bigop_ext sval Reals_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From Coquelicot Require Export Rcomplements Rbar Series Lim_seq Hierarchy Markov Continuity ElemFct.
From discprob.measure Require Export measurable_space.
From discprob.measure Require Import dynkin.


Record measure A {F: measurable_space A} :=
  { measure_fun :> (A → Prop) → R;
    measure_proper : Proper (@eq_prop A ==> eq) measure_fun;
    measure_nonneg : ∀ X, measure_fun X >= 0;
    measure_empty : measure_fun (empty_set) = 0;
    measure_additivity : ∀ U: nat → (A → Prop),
        (∀ i, F (U i)) → disjointF U → is_series (λ n, measure_fun (U n)) (measure_fun (unionF U))
  }.


Arguments measure_nonneg {_ _} _.

Hint Resolve measure_nonneg measure_empty measure_additivity.

Global Existing Instance measure_proper.

Section measure_props.

  Context `(μ : @measure A F).

  Lemma measure_additivity_Series U :
        (∀ i, F (U i)) → disjointF U → μ (unionF U) = Series (λ x, μ (U x)).
  Proof.
    intros. symmetry; apply is_series_unique, measure_additivity => //=.
  Qed.

  Lemma measure_finite_additivity X Y:
    F X → F Y →
    X ## Y →
    μ (X ∪ Y) = μ X + μ Y.
  Proof.
    intros HFX HFY Hdisj.
    assert (HdisjF: disjointF (λ n : nat, match n with
                                             | O => X
                                             | S O => Y
                                             | _ => ∅ end)).
    {
      rewrite /eq_prop/disjointF. intros i j.
      destruct i as [|[|]];
      destruct j as [|[|]] => //= Hneq.
      by rewrite disjoint_comm.
    }

    assert (∀ i, F (match i with | O => X | 1 => Y | _ => ∅ end)).
    { intros [|[|]] => //=.  }


    rewrite union_pair_unionF.
    rewrite measure_additivity_Series => //=.
    rewrite (Series_incr_n _ 2); [ | omega | ]; last first.
    { eexists. apply measure_additivity; auto. }

    rewrite //=. rewrite measure_empty Series_0 //. nra.
  Qed.

  Lemma measure_list_additivity l:
    (∀ U, In U l → F U) →
    ## l →
    μ (union_list l) = \big[Rplus/0]_(U <- l) μ U.
  Proof.
    induction l => //=.
    * intros. by rewrite big_nil measure_empty.
    * intros Hin Hdisj. rewrite big_cons measure_finite_additivity.
      ** f_equal. apply IHl; eauto. inversion Hdisj; eauto.
      ** apply Hin. by left.
      ** apply sigma_closed_list_union; eauto.
      ** inversion Hdisj; auto.
  Qed.

  Lemma measure_sum_n_additivity Us n:
    (∀ i, (i <= n)%nat → F (Us i)) →
    disjointF Us →
    μ (λ x, ∃ j, (j <= n)%nat ∧ Us j x) = sum_n (λ j, μ (Us j)) n.
  Proof.
    intros Hin.
    induction n => //=.
    * intros. rewrite sum_O. apply measure_proper.
      intros x; split.
      ** intros (?&Hle&?). inversion Hle. subst. done.
      ** intros. exists O. split; auto.
    * intros Hdisj. rewrite sum_Sn /plus//= range_union_S.
      rewrite measure_finite_additivity.
      { f_equal; eauto. }
      ** apply sigma_closed_range_union. auto.
      ** apply Hin. auto.
      ** intros z (Hin1&Hin2). destruct Hin1 as (j&?&?).
         eapply (Hdisj j (S n)); eauto.
         omega.
  Qed.

  Lemma measure_set_minus X Y:
    F X → F Y →
    le_prop X Y → μ (Y ∖ X) = μ Y - μ X.
  Proof.
    intros ?? Hle.
    symmetry. rewrite -{1}(le_minus_union _ _ Hle) measure_finite_additivity //=; auto.
    nra.
  Qed.

  Lemma measure_mono X Y:
    F X → F Y →
    le_prop X Y → μ X <= μ Y.
  Proof.
    intros ?? Hle.
    cut (μ Y - μ X >= 0); first by nra.
    rewrite -measure_set_minus //=.
  Qed.

  Lemma measure_set_minus' X Y:
    F X → F Y →
    μ (Y ∖ X) >= μ Y - μ X.
  Proof.
    intros ??.
    transitivity (μ (set_minus Y (Y ∩ X))).
    { apply Rle_ge, measure_mono; eauto.
      * apply sigma_closed_set_minus; eauto.
      * clear; firstorder.
    }
    rewrite measure_set_minus //=.
    * cut (μ (Y ∩ X) <= μ X); first by nra.
      apply measure_mono; eauto.
      clear; firstorder.
    * eauto.
    * clear; firstorder.
  Qed.

  Lemma diff_below_measurable' (G: (A → Prop) → Prop) Us
        (Hmeas: ∀ i, G (Us i))
        (Hproper: ∀ U1 U2, U1 ≡ U2 → G U2 → G U1)
        (Hempty: G ∅)
        (Hcompl: ∀ U, G U → G (compl U))
        (Hinter: ∀ U1 U2, G U1 → G U2 → G (U1 ∩ U2)):
    ∀ i, G (diff_below Us i).
  Proof.
    intros. apply Hinter; auto.
    induction i.
    * eapply Hproper; last (apply Hcompl, Hempty). clear.
      firstorder.
    * assert ((λ x : A, ∀ i' : nat, (i' < S i)%nat → ¬ Us i' x)
                ≡ compl (Us i) ∩ ((λ x : A, ∀ i' : nat, (i' < i)%nat → ¬ Us i' x))) as Heq.
      { intros x; split.
        ** intros Hin; split; auto.
           apply (Hin i). omega.
        ** intros (Hin1&Hin2); intros i'. inversion 1; subst; auto.
      }
      eapply Hproper; first eapply Heq.
      apply Hinter; eauto.
  Qed.

  Lemma diff_below_measurable Us (Hmeas: ∀ i, F (Us i)):
    ∀ i, F (diff_below Us i).
  Proof.
    intros i. apply diff_below_measurable'; eauto.
    intros ?? ->. done.
  Qed.

  Lemma measure_incr_mono (Us : nat → (A → Prop)) j k (Hle: (j <= k)%nat) :
    (∀ i, Us i ⊆ Us (S i)) →
    Us j ⊆ Us k.
  Proof.
    intros Hsub. induction Hle.
    - reflexivity.
    - etransitivity; eauto.
  Qed.

  Lemma measure_incr_seq (Us: nat → (A → Prop)) :
    (∀ i, F (Us i)) →
    (∀ i, Us i ⊆ Us (S i)) →
    is_lim_seq (λ i, μ (Us i)) (μ (unionF Us)).
  Proof.
    intros Hmeas Hincr.
    rewrite diff_below_unionF.
    eapply (is_lim_seq_ext (λ n, sum_n (λ i, μ (diff_below Us i)) n)).
    { intros n. induction n => //=.
      * rewrite sum_O. apply measure_proper. clear; firstorder.
      * rewrite sum_Sn /plus IHn //=.
        rewrite -measure_finite_additivity; auto using diff_below_measurable.
        ** apply measure_proper. intros x; split.
           *** intros [Hle1|(?&?)]; eauto. eapply Hincr; done.
           *** intros HU. rewrite /diff_below.
               destruct (Classical_Prop.classic (Us n x)) as [Hn|Hnotn]; first by left.
               right; split; auto. intros i' Hlt Hsat.
               apply Hnotn. eapply (measure_incr_mono Us i'); eauto. omega.
        ** clear. intros x (Hin1&Hin2). destruct Hin2 as (?&Hfalse).
           eapply Hfalse; eauto.
    }
    apply measure_additivity.
    * apply diff_below_measurable; eauto.
    * apply diff_below_disjoint.
  Qed.

  Lemma measure_decr_seq (Us: nat → (A → Prop)) :
    (∀ i, F (Us i)) →
    (∀ i, Us (S i) ⊆ Us i) →
    is_lim_seq (λ i, μ (Us i)) (μ (intersectF Us)).
  Proof.
    intros Hmeas Hdecr.
    set (Vs := λ n,  (Us O) ∖ (Us n)).
    assert (HmeasV: ∀ i, F (Vs i)).
    { intros.  rewrite /Vs. apply sigma_closed_set_minus; eauto. }
    assert (Hincr: ∀ i, Vs i ⊆ Vs (S i)).
    { intros i.  rewrite /Vs. clear -Hdecr. firstorder. }
    specialize (measure_incr_seq Vs HmeasV Hincr) => Hlim.
    assert (Hequiv: unionF Vs ≡  Us O ∖ intersectF Us).
    { clear. rewrite /Vs. intros x; split.
      * firstorder.
      * intros (HUs0&Hninter).
        apply Classical_Pred_Type.not_all_ex_not in Hninter as (n&Hnot).
        exists n. split; auto.
    }
    rewrite Hequiv in Hlim *.
    rewrite measure_set_minus /Rminus; eauto.
    { rewrite Rplus_comm. intros. eapply is_lim_seq_opp_inv.
      eapply (is_lim_seq_plus_inv _ (λ _, μ (Us O)) _ (μ (Us O))).
      * eapply is_lim_seq_ext; last eassumption.
        intros n. rewrite /Vs => //=. rewrite measure_set_minus; first field; eauto.
        { induction n; first reflexivity. etransitivity; eauto. eapply Hdecr. }
      * apply is_lim_seq_const.
    }
    - apply sigma_closed_intersections; auto.
    - intros x; clear; firstorder.
  Qed.

  Lemma measure_finite_subadditivity U1 U2:
    F U1 → F U2 →
    μ (U1 ∪ U2) <= μ U1 + μ U2.
  Proof.
    intros HF1 Hf2.
    assert (U1 ∪ U2 ≡ U1 ∪ (set_minus U2 U1)) as ->.
    { split; clear; destruct (Classical_Prop.classic (U1 x)); firstorder. }
    rewrite measure_finite_additivity; eauto using sigma_closed_set_minus.
    * apply Rplus_le_compat; apply measure_mono; eauto using sigma_closed_set_minus.
      ** reflexivity.
      ** clear; firstorder.
    * apply disjoint_comm, disjoint_set_minus.
  Qed.

  Lemma measure_sum_n_subadditivity Us n:
    (∀ i, (i <= n)%nat → F (Us i)) →
    μ (λ x, ∃ j, (j <= n)%nat ∧ Us j x) <= sum_n (λ j, μ (Us j)) n.
  Proof.
    intros Hin.
    induction n => //=.
    * intros. rewrite sum_O. right. apply measure_proper.
      intros x; split.
      ** intros (?&Hle&?). inversion Hle. subst. done.
      ** intros. exists O. split; auto.
    * rewrite sum_Sn /plus//= range_union_S.
      etransitivity; first eapply measure_finite_subadditivity.
      ** apply sigma_closed_range_union. auto.
      ** apply Hin. auto.
      ** apply Rplus_le_compat; eauto.
         reflexivity.
  Qed.

  Lemma measure_countable_subadditivity (Us: nat → (A → Prop)):
    (∀ i, F (Us i)) →
    ex_series (λ n, μ (Us n)) →
    μ (unionF Us) <= Series (λ n, μ (Us n)).
  Proof.
    intros.
    set (Us' := λ n, (λ x, ∃ j, (j <= n)%nat ∧ Us j x)).
    assert (unionF Us ≡ unionF Us') as ->.
    { split.
      * intros (j&?). exists j. exists j. auto.
      * intros (j&(j'&?)). exists j'. intuition.
    }
    eapply (is_lim_seq_le (λ n, μ (Us' n)) (sum_n (λ i, μ (Us i)))
                          (μ (unionF Us')) (Series (λ n, μ (Us n)))).
    { intros. eapply measure_sum_n_subadditivity; eauto. }
    { apply (measure_incr_seq Us').
      { rewrite /Us'. intros i. apply sigma_closed_range_union. auto. }
      { intros i x (j&?&?). exists j; split; auto. }
    }
    apply ex_series_is_lim_seq; eauto.
  Qed.

  (* TODO: there's now a shorter proof as a consequence of subadditivity *)
  Lemma measure_countable_subadditivity0 (Us: nat → (A → Prop)):
    (∀ i, F (Us i)) →
    (∀ i, μ (Us i) = 0) →
    μ (unionF Us) = 0.
  Proof.
    intros HF Hzero.
    set (Us' := λ n, (λ x, ∃ j, (j <= n)%nat ∧ Us j x)).
    assert (unionF Us ≡ unionF Us') as ->.
    { split.
      * intros (j&?). exists j. exists j. auto.
      * intros (j&(j'&?)). exists j'. intuition.
    }
    feed pose proof (measure_incr_seq Us') as Hlim.
    { rewrite /Us'. intros i. apply sigma_closed_range_union. auto. }
    { intros i x (j&?&?). exists j; split; auto. }
    eapply (is_lim_seq_ext _ (λ _, 0)) in Hlim; last first.
    { intros n. apply Rle_antisym; last apply Rge_le, measure_nonneg.
      etransitivity; first eapply measure_sum_n_subadditivity; eauto.
      clear -Hzero. right.
      induction n => //=.
      * by rewrite sum_O Hzero.
      * by rewrite sum_Sn IHn Hzero plus_zero_l.
    }
    replace 0 with (real (Finite 0)); auto.
    rewrite -(Lim_seq_const 0).
    symmetry. apply is_lim_seq_unique in Hlim. rewrite Hlim. done.
  Qed.

End measure_props.


Definition almost_everywhere `(μ : @measure A F) (U: A → Prop) :=
  ∃ V, F (compl V) ∧ μ (compl V) = 0 ∧ (∀ a, V a → U a).

Definition almost_everywhere_meas `(μ : @measure A F) (U: A → Prop) :=
  F (compl U) ∧ μ (compl U) = 0.

Section ae.
Context {A: Type}.
Context {F: measurable_space A}.

Implicit Types μ: @measure A F.
Implicit Types U: A → Prop.

Lemma ae_to_aem μ U :
  F U → almost_everywhere μ U → almost_everywhere_meas μ U.
Proof.
  intros HF (V&?&Hzero&?).
  split; auto.
  apply Rle_antisym; last apply Rge_le, measure_nonneg.
  rewrite -Hzero. apply measure_mono; eauto.
  intros z Hnu Hv. apply Hnu. eauto.
Qed.

Lemma aem_to_ae μ U :
  almost_everywhere_meas μ U → almost_everywhere μ U ∧ F U.
Proof.
  intros (HF&?). split; auto.
  - exists U. split_and!; eauto.
  - apply sigma_closed_complements in HF. rewrite compl_involutive in HF *.
    done.
Qed.

Lemma almost_everywhere_conj μ U1 U2:
  almost_everywhere μ U1 →
  almost_everywhere μ U2 →
  almost_everywhere μ (U1 ∩ U2).
Proof.
  intros (V1&HF1&Hmeas1&Himpl1).
  intros (V2&HF2&Hmeas2&Himpl2).
  exists (V1 ∩ V2).
  split_and!; eauto.
  - apply sigma_closed_complements. apply sigma_closed_pair_intersect.
    * apply sigma_closed_complements in HF1. rewrite compl_involutive in HF1 *.
       auto.
    * apply sigma_closed_complements in HF2. rewrite compl_involutive in HF2 *.
       auto.
  - rewrite compl_intersect. apply Rle_antisym.
    * etransitivity; first eapply measure_finite_subadditivity; eauto.
      nra.
    * apply Rge_le, measure_nonneg.
  - firstorder.
Qed.

Lemma almost_everywhere_meas_conj μ U1 U2:
  almost_everywhere_meas μ U1 →
  almost_everywhere_meas μ U2 →
  almost_everywhere_meas μ (U1 ∩ U2).
Proof.
  intros (?&?)%aem_to_ae (?&?)%aem_to_ae.
  apply ae_to_aem; auto.
  apply almost_everywhere_conj; auto.
Qed.

Lemma almost_everywhere_meas_ext μ U1 U2:
  eq_prop U1 U2 →
  almost_everywhere_meas μ U1 →
  almost_everywhere_meas μ U2.
Proof.
  intros Heq (?&?).
  split.
  - by rewrite -Heq.
  - by rewrite -Heq.
Qed.

Lemma almost_everywhere_meas_mono μ U1 U2:
  F U2 → U1 ⊆ U2 →
  almost_everywhere_meas μ U1 →
  almost_everywhere_meas μ U2.
Proof.
  intros HF Hsub (HF1&Hmeas).
  split.
  - apply sigma_closed_complements; auto.
  - apply Rle_antisym; last apply Rge_le, measure_nonneg.
    rewrite -Hmeas. apply measure_mono; auto.
    firstorder.
Qed.

Lemma almost_everywhere_mono μ U1 U2:
  U1 ⊆ U2 →
  almost_everywhere μ U1 →
  almost_everywhere μ U2.
Proof.
  intros Hsub (V1&HF1&Hmeas&Himpl). exists V1.
  split_and!; auto.
Qed.

Lemma almost_everywhere_ext μ U1 U2:
  eq_prop U1 U2 →
  almost_everywhere μ U1 →
  almost_everywhere μ U2.
Proof.
  intros Heq. apply almost_everywhere_mono; eauto. by rewrite Heq.
Qed.

Lemma almost_everywhere_meas_everywhere μ U:
  (∀ x : A, U x) →
  almost_everywhere_meas μ U.
Proof.
  intros HU. eapply (almost_everywhere_meas_ext _ (λ x, True)).
  { clear -HU; firstorder. }
  { split; auto. rewrite -(measure_empty _ μ). apply measure_proper.
    clear; firstorder. }
Qed.

Lemma almost_everywhere_meas_meas μ U:
  almost_everywhere_meas μ U →
  F U.
Proof.
  intros (HU&?).
  apply sigma_closed_complements in HU.
  rewrite compl_involutive in HU * => //=.
Qed.

Lemma almost_everywhere_meas_meas_full μ U:
  almost_everywhere_meas μ U →
  μ U = μ (λ _, True).
Proof.
  intros (HU&?).
  transitivity (μ (set_minus (λ _, True) (compl U))).
  { apply measure_proper. clear; split; firstorder. apply Classical_Prop.NNPP => HnU.
    eauto. }
  rewrite measure_set_minus; eauto.
  - nra.
  - clear; firstorder.
Qed.

Global Instance almost_everywhere_meas_Proper μ:
  Proper (eq_prop ==> iff) (almost_everywhere_meas μ).
Proof.
  intros ?? Heq. split; eapply almost_everywhere_meas_ext; eauto.
    by symmetry.
Qed.

Lemma almost_everywhere_meas_True μ:
  almost_everywhere_meas μ (λ _, True).
Proof.
  split.
  - apply sigma_closed_complements, sigma_full.
  - rewrite compl_top measure_empty //.
Qed.

Lemma almost_everywhere_meas_conj_inv μ U1 U2:
  F U1 → almost_everywhere_meas μ (U1 ∩ U2) →
  almost_everywhere_meas μ U1.
Proof.
  intros ? Hae; split; auto.
  apply Rle_antisym; last (apply Rge_le, measure_nonneg).
  destruct Hae as (?&<-).
  apply measure_mono; auto using sigma_closed_complements.
  { clear. firstorder. }
Qed.
End ae.

Lemma compl_meas_0_full {A: Type} {F: measurable_space A} (μ: measure A) U:
  F (compl U) →
  μ U = μ (λ _, True) →
  μ (compl U) = 0.
Proof.
  intros HF Hμ.
  transitivity (μ (set_minus (λ _, True) U)).
  { apply measure_proper. clear; firstorder. }
  rewrite measure_set_minus; eauto.
  * nra.
  * apply sigma_closed_complements in HF. rewrite compl_involutive in HF *. done.
  * clear; firstorder.
Qed.

Hint Resolve almost_everywhere_meas_True.

Lemma disjoint_sum_measure_additivity {A1 A2: Type} {F1: measurable_space A1} {F2: measurable_space A2}
      (μ1: measure A1) (μ2: measure A2) Us:
  (∀ i, (measurable_space_sum A1 A2) (Us i)) →
  disjointF Us →
  is_series (λ n : nat, μ1 (fun_inv inl (Us n)) + μ2 (fun_inv inr (Us n)))
            (μ1 (fun_inv inl (unionF Us)) + μ2 (fun_inv inr (unionF Us))).
Proof.
  intros HUs Hdisj.
  apply: is_series_plus.
  - rewrite inv_union. apply measure_additivity.
    * eapply HUs.
    * intros i j Hneq.
      intros z (Hin1&Hin2).
      eapply (Hdisj i j Hneq (inl z)).
      split; auto.
  - rewrite inv_union. apply measure_additivity.
    * eapply HUs.
    * intros i j Hneq.
      intros z (Hin1&Hin2).
      eapply (Hdisj i j Hneq (inr z)).
      split; auto.
Qed.

Definition disjoint_sum_measure {A1 A2} {F1: measurable_space A1} {F2: measurable_space A2}
           (μ1: measure A1) (μ2: measure A2): measure (A1 + A2).
Proof.
  refine {| measure_fun := λ U, μ1 (fun_inv inl U) + μ2 (fun_inv inr U) |}.
  - intros U1 U2 Heq. by rewrite Heq.
  - intros X.
    specialize (measure_nonneg μ1 (fun_inv inl X)).
    specialize (measure_nonneg μ2 (fun_inv inr X)).
    abstract nra.
  - abstract (rewrite ?measure_empty; field).
  - apply disjoint_sum_measure_additivity.
Defined.

Definition scal_measure {A: Type} {F: measurable_space A} (p: R) (μ: measure A) :
           measure A.
Proof.
  refine {| measure_fun := λ U, Rabs p * μ U |}.
  - abstract (by intros ?? ->).
  - abstract (intros X; specialize (measure_nonneg μ X); specialize (Rabs_pos p); nra).
  - abstract (rewrite measure_empty; nra).
  - abstract (intros ???; apply: is_series_scal; apply measure_additivity; eauto).
Defined.

Definition trivial_measure0 {A: Type} (F: measurable_space A) : measure A.
Proof.
  refine {| measure_fun := λ _, 0 |}.
  - abstract (intro; nra).
  - auto.
  - abstract (intros; by apply is_series_0).
Defined.

Definition pt_measure_fun :=
  λ U : unit → Prop,
        match excluded_middle_informative (eq_prop U (λ _, True)) with
        | left _ => 1
        | _ => 0
        end.

Lemma pt_measure_additivity:
  ∀ U : nat → () → Prop,
  (∀ i : nat, (discrete_algebra ()) (U i))
  → disjointF U
    → is_series (λ n, pt_measure_fun (U n)) (pt_measure_fun (unionF U)).
Proof.
  intros Us _ Hdisj. rewrite /pt_measure_fun.
  destruct excluded_middle_informative as [HeqU|HneqU].
  * assert (∃ i, (Us i) ≡ (λ _, True)) as Hex.
    { assert (unionF Us ()) as (i&Hsat). by apply HeqU.
      exists i. intros []; split; auto. }
    destruct Hex as (i&Hequiv).
    assert (Helse: ∀ j, j ≠ i → Us j ≢ (λ _, True)).
    {  intros j Hneq. intros Heq.
       eapply (Hdisj j i Hneq ()).
       split.
       * apply Heq. eauto.
       * apply Hequiv. eauto.
    }
    eapply is_series_ext; last first.
    { apply (is_series_bump i). }
    intros n => //=.  destruct Nat.eq_dec.
    ** subst. destruct excluded_middle_informative as [|n]; eauto. exfalso; eapply n; eauto.
    ** destruct excluded_middle_informative as [e|n']; eauto.
       exfalso; eapply Helse; eauto.
  * eapply is_series_0.
    intros n. destruct excluded_middle_informative as [Heq|Hn]; auto.
    exfalso; eapply HneqU. intros []; split; auto.
    intros. exists n. by eapply Heq.
Qed.

Definition pt_measure : measure unit.
Proof.
  refine {| measure_fun :=
              λ U : unit → Prop, match excluded_middle_informative (eq_prop U (λ _, True)) with
                              | left _ => 1
                              | _ => 0
                              end
         |}.
  - intros ?? Heq.
    destruct excluded_middle_informative as [|n1]; auto;
    destruct excluded_middle_informative as [|n2]; auto.
    * exfalso. eapply n2. rewrite -Heq. done.
    * exfalso. eapply n1. rewrite Heq. done.
  - abstract(intros U; destruct excluded_middle_informative; nra).
  - abstract (destruct excluded_middle_informative as [e|n]; auto;
              exfalso; specialize (e tt); destruct e as (?&Hfalse);
                by apply Hfalse).
  - apply pt_measure_additivity.
Defined.

Lemma pi_measure_equiv {A: Type} {F: measurable_space A} (pi: (A → Prop) → Prop) (μ ν : measure A):
  is_pi_system pi →
  eq_sigma F (minimal_sigma pi) →
  μ (λ _, True) = ν (λ _, True) →
  (∀ U, pi U → μ U = ν U) →
  (∀ U, (minimal_sigma pi) U → μ U = ν U).
Proof.
  intros His_pi Heq Hfull Hpi.
  set (D := λ U, minimal_sigma pi U ∧ μ U = ν U).
  assert (HDfull: D (λ _, True)).
  { rewrite /D//=. }
  assert (HDproper: Proper (eq_prop ==> iff) D).
  { rewrite /D. by intros ?? ->. }
  assert (HDclosed_minus: ∀ P Q, D P → D Q → Q ⊆ P → D (set_minus P Q)).
  { rewrite /D. intros P Q (?&HP) (?&HQ) Hsub.
    split.
    - apply sigma_closed_set_minus; auto.
    - rewrite ?measure_set_minus ?Heq; auto. nra.
  }
  assert (HDunion: ∀ Ps : nat → (A → Prop), (∀ i, D (Ps i)) →
                                            (∀ i, Ps i ⊆ Ps (S i)) → D (unionF Ps)).
  {
    rewrite /D. intros Ps HD Hmono; split.
    - apply sigma_closed_unions. intros i. destruct (HD i); eauto.
    - feed pose proof (measure_incr_seq μ Ps); auto.
      { intros i. destruct (HD i); rewrite ?Heq; eauto. }
      feed pose proof (measure_incr_seq ν Ps) as Hnu; auto.
      { intros i. destruct (HD i); rewrite ?Heq; eauto. }
      eapply is_lim_seq_ext in Hnu; last first.
      { intros n. destruct (HD n) as (?&Heq'). symmetry; apply Heq'. }
      cut (Finite (μ (unionF Ps)) = Finite (ν (unionF Ps))).
      { congruence. }
      etransitivity; last eapply is_lim_seq_unique; eauto.
      symmetry. by apply is_lim_seq_unique.
  }
  set (D' := mkDynkin _ D HDproper HDfull HDclosed_minus HDunion).
  intros ? HU. replace pi with (pi_sets _ (pi_of_is_pi_system _ His_pi)) in HU by auto.
  apply pi_sigma_equiv_dynkin in HU.
  assert (D' U) as (?&?); last by done.
  { eapply minimal_dynkin_lub in HU; eauto.
    intros V. rewrite //=/D => HV. split; auto.
    apply minimal_sigma_ub. done.
  }
Qed.
