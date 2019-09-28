Require Import Reals Psatz Omega ClassicalEpsilon.
From stdpp Require Import tactics.
From discprob.basic Require Export base Series_Ext order bigop_ext sval Reals_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From Coquelicot Require Export Rcomplements Rbar Series Lim_seq Hierarchy Markov Continuity ElemFct.
From discprob.measure Require Export sets.

Record sigma_algebra (A: Type) :=
  mkSigma {
      sigma_sets:> (A → Prop) → Prop;
      sigma_proper : Proper (@eq_prop A ==> iff) sigma_sets;
      sigma_full : sigma_sets (λ _, True);
      sigma_closed_complements :
        ∀ P, sigma_sets P → sigma_sets (compl P);
      sigma_closed_unions :
               ∀ Ps : nat → (A → Prop), (∀ i, sigma_sets (Ps i)) →
                                        sigma_sets (unionF Ps)
    }.

Definition eq_sigma {A: Type} (F1 F2: sigma_algebra A) := eq_prop F1 F2.
Definition le_sigma {A: Type} (F1 F2: sigma_algebra A) := le_prop F1 F2.

(*
Global Instance le_sigma_Transitive {X}: Transitive (@le_sigma X).
Proof. rewrite /le_sigma => ??? Heq1 Heq2 x. intros. by apply Heq2, Heq1. Qed.
Global Instance le_sigma_Reflexive {X}: Reflexive (@le_sigma X).
Proof. rewrite /le_sigma //=. intros ??. done. Qed. 

Global Instance eq_sigma_Transitive {X}: Transitive (@eq_sigma X).
Proof. rewrite /eq_sigma/eq_prop => ??? Heq1 Heq2 x. by rewrite Heq1 Heq2.  Qed.
Global Instance eq_sigma_Reflexive {X}: Reflexive (@eq_sigma X).
Proof. rewrite /eq_sigma. by apply eq_prop_Reflexive. Qed.
Global Instance eq_sigma_Symmetry {X}: Symmetric (@eq_sigma X).
Proof. rewrite /eq_sigma/eq_prop => ?? Heq x. by rewrite Heq. Qed.
Global Instance eq_sigma_Equivalence {X}: Equivalence (@eq_sigma X).
Proof. split; apply _. Qed. 
*)

Global Instance sigma_algebra_proper {A: Type} X : Proper (@eq_prop A ==> iff) (@sigma_sets A X).
Proof. apply sigma_proper. Qed.

Lemma sigma_closed_intersections {A: Type} (X: sigma_algebra A) (Ps: nat → (A → Prop)) :
  (∀ i, X (Ps i)) → X (intersectF Ps).
Proof.
  intros Hmem.
  assert (eq_prop (λ x : A, ∀ i, Ps i x) (λ x, ¬ (∃ i, ¬ (Ps i x)))) as ->.
  { intros x; split.
    - intros Hall (i&Hnot). apply Hnot. auto.
    - intros Hnot i. eapply Classical_Pred_Type.not_ex_not_all in Hnot. eauto.
  }
  apply sigma_closed_complements, sigma_closed_unions.
  intros i. apply sigma_closed_complements. auto.
Qed.

Lemma union_pair_unionF {A: Type} (X Y: A → Prop) :
  eq_prop (X ∪ Y)
          (unionF (λ n : nat, match n with
                              | O => X
                              | S O => Y
                              | _ => ∅ end)). 
Proof.
  rewrite /eq_prop/union/unionF; split.
  * intros [?|?]; [exists O | exists (S O)]; auto. 
  * intros (n&H).
    destruct n; first by left.
    destruct n; first by right.
    inversion H.
Qed.

Lemma intersect_pair_intersectF {A: Type} (X Y: A → Prop) :
  eq_prop (X ∩ Y)
          (intersectF (λ n : nat, match n with
                              | O => X
                              | S O => Y
                              | _ => (λ _, True) end)). 
Proof.
  rewrite /eq_prop/intersect/intersectF; split.
  * intros [? ?] [|[|]]; auto.
  * intros H; split.
    ** apply (H O).
    ** apply (H (S O)).
Qed.

Lemma sigma_empty_set {A: Type} (F: sigma_algebra A) :
  F ∅.
Proof.
  eapply sigma_proper; last apply sigma_closed_complements, sigma_full.
  intros x; split => [] []; auto.
Qed.

Hint Resolve sigma_empty_set sigma_full sigma_closed_complements sigma_closed_unions.

Lemma sigma_closed_pair_union {A: Type} (F: sigma_algebra A) X Y:
  F X → F Y → F (X ∪ Y). 
Proof.
  intros. rewrite union_pair_unionF.  apply sigma_closed_unions.
  intros [|[|]]; auto.
Qed.

Lemma range_union_S {A: Type} (Us: nat → A → Prop) n:  
  (λ x, ∃ i, (i <= S n)%nat ∧ Us i x) ≡ (λ x, ∃i, (i <= n)%nat ∧ Us i x) ∪ (Us (S n)).
Proof.
  intros x; split.
  - intros (?&Hle&?). inversion Hle; subst; firstorder.
  - firstorder.
Qed.

Lemma sigma_closed_range_union {A: Type} (F: sigma_algebra A) Us n:
  (∀ i, (i <= n)%nat → F (Us i)) → F (λ x, ∃ i, (i <= n)%nat ∧ Us i x).
Proof.
  induction n.
  - intros Hle. apply (sigma_proper _ _ (Us O)); eauto.
    intros x; split.
    * firstorder.
    * intros (i&Hle'&?). inversion Hle'; firstorder.
  - intros.  setoid_rewrite range_union_S. apply sigma_closed_pair_union; eauto.
Qed.

Lemma sigma_closed_list_union {A: Type} (F: sigma_algebra A) l:
  (∀ U, In U l → F U) → F (union_list l). 
Proof.
  induction l => //=.
  intros. apply sigma_closed_pair_union; eauto.
Qed.

Lemma sigma_closed_pair_intersect {A: Type} (F: sigma_algebra A) X Y:
  F X → F Y → F (X ∩ Y). 
Proof.
  intros. rewrite intersect_pair_intersectF. apply sigma_closed_intersections.
  intros [|[|]]; auto.
Qed.

Lemma sigma_closed_set_minus {A: Type} (F: sigma_algebra A) X Y:
  F X → F Y → F (X ∖ Y).
Proof.
  intros HX HY.
  rewrite set_minus_union_complement.
  apply sigma_closed_pair_intersect; auto.
Qed.
  
Hint Resolve sigma_closed_pair_union sigma_closed_pair_intersect sigma_closed_set_minus.

Definition intersection_sigma {A: Type} (I: Type) (U: I → sigma_algebra A) : sigma_algebra A.
  refine {| sigma_sets := λ x, ∀ i, (U i) x |}.
  - abstract (intros X X' Heq; split => H i; [ rewrite -Heq | rewrite Heq ]; auto).
  - abstract (intros; by apply sigma_full).
  - abstract (intros; by apply sigma_closed_complements).
  - abstract (intros; by apply sigma_closed_unions).
Defined.

Definition minimal_sigma {A: Type} (F: (A → Prop) → Prop) : sigma_algebra A :=
  intersection_sigma { F' : sigma_algebra A | le_prop F F' } sval.
  
Lemma minimal_sigma_ub {A: Type} (F : (A → Prop) → Prop) :
  le_prop F (minimal_sigma F).
Proof.
  intros i HF (F'&Hle) => //=. by apply Hle.
Qed.

Lemma minimal_sigma_lub {A: Type} (F : (A → Prop) → Prop) (F': sigma_algebra A) :
  le_prop F F' → le_prop (minimal_sigma F) F'.
Proof.
  intros Hle X. rewrite /minimal_sigma/intersection_sigma => //=.
  intros H. specialize (H (exist _ F' Hle)). apply H.
Qed.


Record measure {A: Type} (F: sigma_algebra A) :=
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

  Context {A: Type}.
  Context {F: sigma_algebra A}.
  Context (μ : @measure A F).

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


Definition measurable {A B: Type} f (F1: sigma_algebra A) (F2: sigma_algebra B) :=
  ∀ U, F2 U → F1 (fun_inv f U).

Lemma measurable_proper {A B: Type} f :
  Proper (@eq_sigma A ==> @eq_sigma B ==> iff) (@measurable A B f).
Proof.
  intros F1 F1' Heq1 F2 F2' Heq2.
  split; intros Hmeasure U.
  - rewrite -Heq1 -Heq2. auto.
  - rewrite Heq1 Heq2. auto.
Qed.

Global Instance measurable_proper' {A B: Type} :
  Proper (pointwise_relation _ eq ==> eq ==> eq ==> iff) (@measurable A B).
Proof.
  intros f1 f2 Heq ?? ? ?? ?; subst.
  assert (Heq': eq_fun f1 f2).
  { intros x; eauto. }
  split; intros Hmeasure U.
  - rewrite -Heq'. eauto.
  - rewrite Heq'. eauto.
Qed.

Lemma measurable_ext {A B: Type} F1 F2 f1 f2 :
  (∀ x, f1 x = f2 x) →
  @measurable A B f1 F1 F2 →
  @measurable A B f2 F1 F2.
Proof.
  intros Heq Hmeas. eapply measurable_proper'; eauto.
  intros x. done.
Qed.

Global Instance measurable_mono {A B: Type} f :
  Proper (@le_sigma A ==> @le_sigma B --> impl) (@measurable A B f).
Proof.
  intros F1 F1' Heq1 F2 F2' Heq2.
  intros Hmeas U HU. by apply Heq2, Hmeas, Heq1 in HU.
Qed.

Lemma measurable_comp {A B C: Type} (f: A → B) (g: B → C) F1 F2 F3 :
  measurable f F1 F2 →
  measurable g F2 F3 →
  measurable (λ x, g (f x)) F1 F3.
Proof. intros Hf Hg ? HU. by apply Hg, Hf in HU. Qed.

Lemma measurable_id {A: Type}  F:
  measurable (@id A) F F.
Proof. intros U HF => //=. Qed.

Lemma measurable_const {A B: Type} (b: B) F G:
  measurable (λ a : A, b) F G.
Proof.
  intros U HF => //=.
  destruct (Classical_Prop.classic (U b)).
  - eapply sigma_proper; last eapply sigma_full. rewrite /fun_inv.
    split; intuition.
  - eapply sigma_proper; last eapply sigma_empty_set. rewrite /fun_inv.
    split.
    * contradiction. 
    * inversion 1.
Qed.

(* Any function f : A  → B on a measurable space A induces a sigma algebra on B *)
Definition fun_sigma {A B: Type} (F: sigma_algebra A) (f: A → B) : sigma_algebra B.
  refine {| sigma_sets := λ U, F (fun_inv f U) |}. 
  - abstract (by intros ?? ->).
  - abstract (rewrite //=).
  - abstract (intros P HF; rewrite fun_inv_compl; auto).
  - abstract (intros Ps HF; rewrite fun_inv_unionF; auto).
Defined.

Lemma measurable_intersection {I} {A B: Type} f (F1: sigma_algebra A) (F2 : I → sigma_algebra B):
  (∃ i, measurable f F1 (F2 i)) →
  measurable f F1 (intersection_sigma _ F2).
Proof.
  intros HF2 U HminU. 
  cut (le_prop (intersection_sigma _ F2) (fun_sigma F1 f)).
  { intros Hle. by apply Hle. }
  intros V. rewrite /fun_sigma//=. intros Hin.
  edestruct HF2 as (i&Hmeas). eapply Hmeas; eauto.
Qed.

Lemma measurable_generating_sets {A B: Type} f (F1: sigma_algebra A) (F2 : (B → Prop) → Prop):
  (∀ U, F2 U → F1 (fun_inv f U)) →
  measurable f F1 (minimal_sigma F2).
Proof.
  intros HF2 U HminU. 
  cut (le_prop (minimal_sigma F2) (fun_sigma F1 f)).
  { intros Hle. by apply Hle. }
  apply minimal_sigma_lub. rewrite /fun_sigma//=.
Qed.
  
Definition almost_everywhere {A: Type} {F: sigma_algebra A} (μ : measure F) (U: A → Prop) :=
  ∃ V, F (compl V) ∧ μ (compl V) = 0 ∧ (∀ a, V a → U a).

Definition almost_everywhere_meas {A: Type} {F: sigma_algebra A} (μ : measure F) (U: A → Prop) :=
  F (compl U) ∧ μ (compl U) = 0.

Lemma ae_to_aem {A F} (μ: measure F) (U: A → Prop) :
  F U → almost_everywhere μ U → almost_everywhere_meas μ U.
Proof.
  intros HF (V&?&Hzero&?).
  split; auto.
  apply Rle_antisym; last apply Rge_le, measure_nonneg.
  rewrite -Hzero. apply measure_mono; eauto.
  intros z Hnu Hv. apply Hnu. eauto.
Qed.

Lemma aem_to_ae {A F} (μ: measure F) (U: A → Prop) :
  almost_everywhere_meas μ U → almost_everywhere μ U ∧ F U.
Proof.
  intros (HF&?). split; auto.
  - exists U. split_and!; eauto.
  - apply sigma_closed_complements in HF. rewrite compl_involutive in HF *.
    done.
Qed.
  
Lemma almost_everywhere_conj {A F} (μ: measure F) (U1 U2: A → Prop):
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

Lemma almost_everywhere_meas_conj {A F} (μ: measure F) (U1 U2: A → Prop):
  almost_everywhere_meas μ U1 →
  almost_everywhere_meas μ U2 →
  almost_everywhere_meas μ (U1 ∩ U2). 
Proof.
  intros (?&?)%aem_to_ae (?&?)%aem_to_ae.
  apply ae_to_aem; auto.
  apply almost_everywhere_conj; auto.
Qed.


Lemma almost_everywhere_meas_ext {A: Type} {F: sigma_algebra A} (μ : measure F) (U1 U2: A → Prop):
  eq_prop U1 U2 →
  almost_everywhere_meas μ U1 →
  almost_everywhere_meas μ U2.
Proof.
  intros Heq (?&?).
  split.
  - by rewrite -Heq.
  - by rewrite -Heq.
Qed.

Lemma almost_everywhere_meas_mono {A: Type} {F: sigma_algebra A} (μ : measure F) (U1 U2: A → Prop):
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

Lemma almost_everywhere_mono {A: Type} {F: sigma_algebra A} (μ : measure F) (U1 U2: A → Prop):
  U1 ⊆ U2 →
  almost_everywhere μ U1 →
  almost_everywhere μ U2.
Proof.
  intros Hsub (V1&HF1&Hmeas&Himpl). exists V1.
  split_and!; auto.
Qed.

Lemma almost_everywhere_ext {A: Type} {F: sigma_algebra A} (μ : measure F) (U1 U2: A → Prop):
  eq_prop U1 U2 →
  almost_everywhere μ U1 →
  almost_everywhere μ U2.
Proof.
  intros Heq. apply almost_everywhere_mono; eauto. by rewrite Heq.
Qed.

Lemma almost_everywhere_meas_everywhere {A: Type} {F: sigma_algebra A} (μ : measure F) (U: A → Prop):
  (∀ x : A, U x) →
  almost_everywhere_meas μ U.
Proof.
  intros HU. eapply (almost_everywhere_meas_ext _ (λ x, True)).
  { clear -HU; firstorder. }
  { split; auto. rewrite -(measure_empty _ μ). apply measure_proper.
    clear; firstorder. }
Qed.

Lemma almost_everywhere_meas_meas {A: Type} {F: sigma_algebra A} (μ : measure F) (U: A → Prop):
  almost_everywhere_meas μ U →
  F U.
Proof.
  intros (HU&?).
  apply sigma_closed_complements in HU.
  rewrite compl_involutive in HU * => //=.
Qed.

Lemma almost_everywhere_meas_meas_full {A: Type} {F: sigma_algebra A} (μ : measure F) (U: A → Prop):
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

Global Instance almost_everywhere_meas_Proper {A: Type} {F: sigma_algebra A} (μ : measure F):
  Proper (eq_prop ==> iff) (almost_everywhere_meas μ).
Proof.
  intros ?? Heq. split; eapply almost_everywhere_meas_ext; eauto.
    by symmetry.
Qed.

Lemma almost_everywhere_meas_True {A: Type} {F: sigma_algebra A} (μ : measure F):
  almost_everywhere_meas μ (λ _, True).
Proof.
  split.
  - apply sigma_closed_complements, sigma_full.
  - rewrite compl_top measure_empty //.
Qed.

Lemma almost_everywhere_meas_conj_inv {A: Type} {F : sigma_algebra A}
      (μ : measure F) (U1 U2 : A → Prop):
  F U1 → almost_everywhere_meas μ (U1 ∩ U2) →
  almost_everywhere_meas μ U1.
Proof.
  intros ? Hae; split; auto.
  apply Rle_antisym; last (apply Rge_le, measure_nonneg).
  destruct Hae as (?&<-).
  apply measure_mono; auto using sigma_closed_complements.
  { clear. firstorder. }
Qed.

Lemma compl_meas_0_full {A: Type} (F: sigma_algebra A) (μ: measure F) U:
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

Definition disjoint_sum_sigma {A1 A2: Type} (F1: sigma_algebra A1) (F2: sigma_algebra A2)
  : sigma_algebra (A1 + A2).
Proof.
  refine {| sigma_sets := λ U, F1 (fun_inv inl U) ∧ F2 (fun_inv inr U) |}.
  - intros U1 U2 Heq. rewrite Heq. done.
  - split; rewrite //=. 
  - intros U (HF1&HF2).
    split.
    * apply sigma_closed_complements in HF1. eapply sigma_proper; eauto.
      firstorder.
    * apply sigma_closed_complements in HF2. eapply sigma_proper; eauto.
      firstorder.
  - intros Us.
    intros Hi. split.
    * assert (Hinl: ∀ i, F1 (fun_inv inl (Us i))); first by firstorder.
      apply sigma_closed_unions in Hinl.
      eapply sigma_proper; eauto.
      firstorder.
    * assert (Hinr: ∀ i, F2 (fun_inv inr (Us i))); first by firstorder.
      apply sigma_closed_unions in Hinr.
      eapply sigma_proper; eauto.
      firstorder.
Defined.

Lemma inv_union {A B: Type} (f: A → B) (Us: nat → B → Prop):
    eq_prop (fun_inv f (unionF Us))
            (unionF (λ i : nat, fun_inv f (Us i))).
Proof. intros z. split; firstorder. Qed.

Lemma disjoint_sum_measure_additivity {A1 A2: Type} {F1: sigma_algebra A1} {F2: sigma_algebra A2}
      (μ1: measure F1) (μ2: measure F2) Us:
  (∀ i, (disjoint_sum_sigma F1 F2) (Us i))
  → disjointF Us
    → is_series (λ n : nat, μ1 (fun_inv inl (Us n)) + μ2 (fun_inv inr (Us n)))
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
 
Definition disjoint_sum_measure {A1 A2: Type} {F1: sigma_algebra A1} {F2: sigma_algebra A2}
           (μ1: measure F1) (μ2: measure F2): measure (disjoint_sum_sigma F1 F2).
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

Definition scal_measure {A: Type} {F: sigma_algebra A} (p: R) (μ: measure F) :
           measure F.
Proof.
  refine {| measure_fun := λ U, Rabs p * μ U |}.
  - abstract (by intros ?? ->).
  - abstract (intros X; specialize (measure_nonneg μ X); specialize (Rabs_pos p); nra).
  - abstract (rewrite measure_empty; nra).
  - abstract (intros ???; apply: is_series_scal; apply measure_additivity; eauto).
Defined.

Definition discrete_algebra (A: Type) : sigma_algebra A. 
Proof.
  refine {| sigma_sets := λ _, True |}; abstract (auto).
Defined.

Definition trivial_measure0 {A: Type} (F: sigma_algebra A) : measure F. 
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

Definition pt_measure : measure (discrete_algebra unit).
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

(*
Definition finite_pmf_measure {A: finType} (pmf: A → R) (pmf_nonneg: ∀ x, pmf x >= 0)
  : measure (discrete_algebra A).
Proof.
  refine {| measure_fun :=
              λ U, \big[Rplus/0]_(i : A | is_left (excluded_middle_informative (U i)))
                    pmf i |}.
  - intros ?? Heq. apply eq_big.
    * intros i.
      destruct excluded_middle_informative as [|n1]; auto;
      destruct excluded_middle_informative as [|n2]; auto.
      ** exfalso; apply n2. eapply Heq. eauto.
      ** exfalso; apply n1. eapply Heq. eauto.
    * auto.
  - abstract (intros X; apply Rle_ge, Rle_big0; intros; apply Rge_le; eauto).
  - abstract (apply big1; intros i; destruct excluded_middle_informative => //=).
  - intros U _ Hdisj.
SearchAbout measure.
    abstract (apply big1; intros i; destruct excluded_middle_informative => //=).

    inversion 1. destruct excluded_middle_informative; inversion 1.destruct H.

    Rbig_eq0. apply eq_bigr. intros X. apply Rle_ge, Rle_big0; intros. apply Rge_le; eauto.
    * auto.
      exfalso. eapply n.


      destruct excluded_middle_informative.  rewrite //=.
    f_equal. rewrite Heq.
*)

Definition initial_algebra {I: Type} {A: Type} {B: Type} (Y : sigma_algebra B) (f: I → A → B)
  : sigma_algebra A.
Proof.
  set (S := { σ : sigma_algebra A | ∀ i, measurable (f i) σ Y }).
  exact (intersection_sigma S sval).
Defined.

Lemma initial_algebra_meas {I} {A B: Type} (Y: sigma_algebra B) (f: I → A → B) (i: I):
  measurable (f i) (initial_algebra Y f) Y.
Proof.
  intros U HYU (σ&Hspec) => //=.
  eapply Hspec. eauto.
Qed.

Lemma initial_algebra_lb {I} {A B: Type} (Y: sigma_algebra B) (f: I → A → B) (X: sigma_algebra A):
  (∀ i, measurable (f i) X Y) →
  le_sigma (initial_algebra Y f) X.
Proof.
  intros Hmeas. intros U HU.
  apply (HU (exist _ X Hmeas)).
Qed.

Lemma initial_algebra_codom_meas {I} {C A B: Type} (X: sigma_algebra C)
      (Y: sigma_algebra B) (f: I → A → B) g:
  (∀ i, measurable (λ x, (f i (g x))) X Y) →
  measurable g X (initial_algebra Y f).
Proof.
  intros Hspec.
  apply measurable_intersection.
  unshelve (eexists).
  { exists (fun_sigma X g). eauto. }
  rewrite //=.
Qed.

Lemma initial_algebra_in {I} {A B: Type} (Y: sigma_algebra B) (f: I → A → B) U:
  (∃ i U', Y U' ∧ U ≡ fun_inv (f i) U') →
  initial_algebra Y f U.
Proof.
  intros (i&U'&Hin&Heq).
  rewrite Heq. apply initial_algebra_meas. eauto.
Qed.

  
  

Definition initial_algebra1 {A: Type} {B: Type} (Y : sigma_algebra B) (f: A → B)
  : sigma_algebra A := @initial_algebra unit A B Y (λ _, f).

Lemma initial_algebra1_meas {A B: Type} (Y: sigma_algebra B) (f: A → B) :
  measurable f (initial_algebra1 Y f) Y.
Proof.
  eapply measurable_ext; last first.
  { eapply (initial_algebra_meas _ _ tt).  }
  done.
Qed.


Lemma initial_algebra1_codom_meas {C A B: Type} (X: sigma_algebra C)
      (Y: sigma_algebra B) (f: A → B) g:
  measurable (λ x, (f (g x))) X Y →
  measurable g X (initial_algebra1 Y f).
Proof. intros. by eapply initial_algebra_codom_meas. Qed.

Lemma initial_algebra1_lb {A B: Type} (Y: sigma_algebra B) (f: A → B) (X: sigma_algebra A):
  measurable f X Y →
  le_sigma (initial_algebra1 Y f) X.
Proof. intros. eapply initial_algebra_lb; eauto. Qed.

Lemma initial_algebra1_in {A B: Type} (Y: sigma_algebra B) (f: A → B) U:
  (∃ U', Y U' ∧ U ≡ fun_inv f U') →
  initial_algebra1 Y f U.
Proof.
  intros (U'&Hin&Heq).
  rewrite Heq. apply initial_algebra1_meas. eauto.
Qed.

Lemma initial_algebra1_eq_min {A B: Type} (Y: sigma_algebra B) (f: A → B):
  eq_sigma (initial_algebra1 Y f) (minimal_sigma (λ U, ∃ U', U ≡ fun_inv f U' ∧ Y U')).
Proof.
  rewrite /eq_sigma. apply le_prop_antisym.
  - apply initial_algebra_lb. intros _. intros U HYU.
    apply minimal_sigma_ub. eexists; split; eauto.
  - apply minimal_sigma_lub. intros U (U'&Hequiv&HY).
    rewrite Hequiv. by apply initial_algebra1_meas.
Qed.

(*
Lemma initial_algebra1_img {A B: Type} (Y: sigma_algebra B) (f: A → B) U:
  initial_algebra1 Y f U →
  Y (fun_img f U).
Proof.
  intros Hinit. 
  apply initial_algebra1_eq_min in Hinit.
  cut ((λ U : A → Prop, ∃ U' : B → Prop, U ≡ fun_inv f U' ∧ Y U') U).
  { intros Halt.  destruct Halt as (U'&Hequiv&?).
    eapply sigma_proper; eauto. intros z.
    rewrite /fun_img. split.
    intros (x&HU&Heq).
    * subst. eapply Hequiv in HU. eauto.
    * intros HU'z. 
    setoid_rewrite Hequiv.
    rewrite /fun_ing.
    rewrite Hequiv.
  destruct Hinit.
*)
