Require Import Reals Psatz Omega Fourier.
From stdpp Require Import tactics list.
From discprob.basic Require Import seq_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.measure Require Export integral dynkin borel isomorphism outer_measure.
Require Import ClassicalEpsilon.

Section dep_sum_sigma.
Context {A: Type} {B: A → Type} {C: Type}.
Context (F1: sigma_algebra A).
Context (F2: ∀ a, sigma_algebra (B a)).
Context (F3: sigma_algebra C).
Context (f: ∀ a, B a → C).
Context (Hfmeas: ∀ a, measurable (f a) (F2 a) F3).

Definition dep_sum_sigma :=
  minimal_sigma (λ UV, ∃ U Vc, F1 U ∧ F3 Vc ∧
                               UV ≡ (λ ab, U (projT1 ab) ∧ fun_inv (f (projT1 ab)) Vc (projT2 ab))).

Definition dep_section (E: sigT B → Prop) (a: A) : B a → Prop :=
  λ b, E (existT a b).

Global Instance dep_section_proper (a : A):
  Proper (@eq_prop (sigT B) ==> eq_prop) (λ E, dep_section E a).
Proof. intros U U' Heq. rewrite /dep_section; split; eapply Heq. Qed.

Lemma disjointF_dep_section (Us: nat → sigT B → Prop) x:
  disjointF Us →
  disjointF (λ j : nat, dep_section (Us j) x).
Proof.
  intros Hdisj. rewrite /dep_section.
  intros i j Hneq y (Hin1&Hin2).
  eapply Hdisj; eauto.
Qed.

Definition dep_section_sigma (a: A) : sigma_algebra (sigT B).
Proof.
  refine {| sigma_sets := (λ UV, F2 a (dep_section UV a)) |}.
  - intros UV UV' Heq. rewrite dep_section_proper; eauto. 
  - eapply sigma_proper; last apply sigma_full.
    firstorder.
  - intros P. intros HF.
    eapply sigma_proper; last eapply sigma_closed_complements; eauto.
    firstorder.
  - intros Ps. intros HF.
    eapply sigma_proper; last eapply sigma_closed_unions; last first.
    { intros i. eapply (HF i). }
    firstorder.
Defined.

Lemma dep_section_measurable (E: sigT B → Prop) x:
  dep_sum_sigma E →
  F2 x (dep_section E x).
Proof.
  revert E.
  cut (le_prop (dep_sum_sigma) (dep_section_sigma x)).
  { intros Hle. eapply Hle; eauto. }
  apply minimal_sigma_lub.
  intros UV (U&V&?&HV&->).
  rewrite //=.
  rewrite /dep_section//=.
  destruct (Classical_Prop.classic (U x)).
  - eapply sigma_closed_pair_intersect; eauto.
    * eapply sigma_proper; last eapply sigma_full.
      firstorder.
    * by apply Hfmeas.
  - eapply sigma_proper; last eapply sigma_empty_set.
    firstorder.
Qed.

(*
Definition dep_proj_sigma (a: A) : sigma_algebra (sigT B).
Proof.
  refine {| sigma_sets := (λ UV, F2 a (dep_section UV a)) |}.
  - intros UV UV' Heq. rewrite dep_section_proper; eauto. 
  - eapply sigma_proper; last apply sigma_full.
    firstorder.
  - intros P. intros HF.
    eapply sigma_proper; last eapply sigma_closed_complements; eauto.
    firstorder.
  - intros Ps. intros HF.
    eapply sigma_proper; last eapply sigma_closed_unions; last first.
    { intros i. eapply (HF i). }
    firstorder.
Defined.
*)

(*
Lemma dep_sum_sigma_elim UV:
  dep_sum_sigma UV →
  F3 (fun_img (λ ab, f (projT1 ab) (projT2 ab)) UV).
Proof.
  intros Hdep.
  


  intros Hdep.
  unshelve (efeed pose proof Hdep).
  { exists dep_sum_sigma; eauto. intros UV'.
    intros Hspec. SearchAbout minimal_sigma.
    apply minimal_sigma_ub; eauto.
  }
  rewrite //= in H.
    _lb. eexists.
    intros (?&?&?&
*)

Lemma fun_dep_measurable {D: Type} F (g : sigT B → D) x:
  measurable g dep_sum_sigma F →
  measurable (λ y, g (existT x y)) (F2 x) F.
Proof.
  intros Hmeas U HU.
  eapply sigma_proper; last eapply (dep_section_measurable (fun_inv g U) x);
    eauto; firstorder.
Qed.

(*
Lemma fun_dep_measurable' {D: Type} F (g : sigT B → D):
  (∀ x, measurable (λ y, g (existT x y)) (F2 x) F) →
  measurable g dep_sum_sigma F.
Proof.
  intros Hmeas U HU.
  apply minimal_sigma_ub.

  eapply sigma_
  eapply sigma_proper; last eapply (dep_section_measurable (fun_inv g U) x);
    eauto; firstorder.
Qed.
*)

Lemma fun_decode_measurable:
  measurable (λ xy, f (projT1 xy) (projT2 xy)) dep_sum_sigma F3.
Proof.
  intros V HV Hspec.
  destruct Hspec as (F'&Hle).
  eapply Hle.
  eexists. exists V.
  split_and!; auto.
  split.
  * firstorder. 
  * firstorder. 
Qed.

(*
Lemma dep_sum_sigma_initial :
  eq_sigma (dep_sum_sigma) (initial_algebra1 F3 (λ xy, f (projT1 xy) (projT2 xy))).
Proof.
  apply le_prop_antisym.
  - eapply minimal_sigma_lub.
    intros UV (U&Vc&?&?&->).
    intros (σ&Hspec). rewrite //=.
    eapply sigma_closed_pair_intersect; last first.
    { eapply Hspec; eauto. exact tt. }

    eapply sigma_proper; last eapply Hspec;  [| exact tt |]; eauto.

    eapply sigma_proper; last eapply Hspec;


    eapply sigma_proper; last eapply Hspec;  [| exact tt |]; eauto.
    rewrite /fun_inv; eauto.

    eapply Hspec.
    intros.
    intros Hdep.
    rewrite /initial_algebra1/initial_algebra.
    intros σ. 
    intros.
  Focus 2. apply initial_algebra1_lb. apply fun_decode_measurable.
*)
    

(*
Lemma dep_pair_measurable {A} B C: Type} F1 F2 F3 (f : A → B) (g: ∀ a, C):
  measurable f F1 F2 →
  (∀ a, measurable (g a) F1 (F3 a) →
  measurable (λ x, (f x, g x)) F1 (dep_sum_sigma F2 F3).
Proof.
  intros Hmeasf Hmeasg.
  apply measurable_generating_sets.
  intros ? (U&V&HU&HV&->).
  rewrite /fun_inv//=.
  assert ((λ a, U (f a) ∧ V (g a)) ≡ fun_inv f U ∩ fun_inv g V) as ->.
  { intuition. }
  apply sigma_closed_pair_intersect; eauto.
Qed.
*)

Section dep_sum_measure.
  Context (μ: measure F1) (ν: ∀ a, measure (F2 a)).
  Context (Hmeas_meas: ∀ W,
              F3 W → measurable (λ x : A, (ν x) (fun_inv (f x) W)) F1 (borel R_UniformSpace)).
  Context (Mbound: R).
  Context (Hbounded: ∀ a, ν a (λ _, True) <= Mbound).
  (*
  Context (Hmeas1: measurable (λ x : A, (ν x) (λ _ : B x, True)) F1 (borel R_UniformSpace)).
   *)

  Lemma wpt_indicator_dep_section U (Hmeas : dep_sum_sigma U) x:
    (∀ y, wpt_fun (wpt_indicator U Hmeas) (existT x y) =
          wpt_fun (wpt_indicator (dep_section U x) (dep_section_measurable _ _ Hmeas)) y).
  Proof. intros y. rewrite ?wpt_indicator_spec/dep_section//=. Qed.

  Lemma measure_dep_section_rectangle (U: A → Prop) (V: ∀ a, B a → Prop) (x: A) (Hmeas: F1 U):
    ν x (dep_section (λ x, U (projT1 x) ∧ V (projT1 x) (projT2 x)) x) =
    ν x (V x) * (wpt_fun (wpt_indicator U Hmeas) x).
  Proof.
    rewrite /dep_section wpt_indicator_spec.
    destruct (excluded_middle_informative).
    * rewrite Rmult_1_r. apply measure_proper.
      split; intuition.
    * rewrite Rmult_0_r. etransitivity; last eapply measure_empty.
      apply measure_proper. split.
      ** intros (?&?); intuition. 
      ** inversion 1.
  Qed.

  Lemma measure_dep_section_fun_inv (U: A → Prop) V (x: A) (Hmeas: F1 U):
    ν x (dep_section (λ x, U (projT1 x) ∧ fun_inv (f (projT1 x)) V (projT2 x)) x) =
    ν x (fun_inv (f x) V) * (wpt_fun (wpt_indicator U Hmeas) x).
  Proof.
    eapply (measure_dep_section_rectangle U (λ a, fun_inv (f a) V)).
  Qed.

  Lemma measurable_measure_dep U:
    dep_sum_sigma U →
    measurable (λ x : A, ν x (dep_section U x)) F1 (borel R_UniformSpace).
  Proof.
    intros HU.
    set (F := (λ U, dep_sum_sigma U ∧ measurable (λ x, ν x (dep_section U x)) F1 (borel _))).
    cut (eq_prop (dep_sum_sigma) F).
    { intros Heq. destruct (Heq U) as (Himpl1&Himpl2); eauto.
      destruct (Himpl1); eauto. }
    apply le_prop_antisym; last first.
    { intros ? (?&?); eauto. }
    assert (HFproper: Proper (eq_prop ==> iff) F).
    { intros ?? Heq. rewrite /F.
      split.
      * split.
        ** setoid_rewrite <-Heq. intuition.
        ** eapply measurable_ext.
           intros z. rewrite -(dep_section_proper _ _ y); eauto.
           intuition.
      * split.
        ** setoid_rewrite Heq. intuition.
        ** eapply measurable_ext.
           intros z. rewrite (dep_section_proper _ _ y); eauto.
           intuition.
    }
    assert (HFfull: F (λ _, True)).
    { split; first apply sigma_full.
      assert ((λ _ : _, True) ≡ (λ x : _, (λ _ :A , True) (projT1 x) ∧ (λ _ :B (projT1 x) , True) (projT2 x)))
             as Heq.
      { split; auto. }
      eapply measurable_ext.
      { intros x. apply measure_proper. by rewrite (dep_section_proper _ _ _ Heq). }
      eapply measurable_ext.
      { intros x. rewrite (measure_dep_section_rectangle (λ _, True) (λ _ _, True)). done. }
      measurable.
      * eapply measurable_ext; last eapply (Hmeas_meas (λ _, True)); eauto.
      * apply wpt_fun_measurable. 
    }
    assert (HFset_minus: ∀ P Q, F P → F Q → Q ⊆ P → F (set_minus P Q)).
    { 
      intros P Q (HP&?) (HQ&?) Hsub.
      rewrite /F; split; first (apply sigma_closed_set_minus; auto).
      assert (∀ x, ν x (dep_section (set_minus P Q) x) =
                   ν x (dep_section P x) - ν x (dep_section Q x)) as Heq.
      { intros x. rewrite -measure_set_minus; eauto using dep_section_measurable.
        clear -Hsub. firstorder.
      }
      setoid_rewrite Heq.
      measurable.
    }
    assert (HF_closed_unions : ∀ Ps, (∀ i, F (Ps i)) → (∀ i, Ps i ⊆ Ps (S i)) → F (unionF Ps)).
    { intros Ps HPs Hmono. split.
      * apply sigma_closed_unions. intros i.
        destruct (HPs i); eauto.
      * assert (∀ x, ν x (dep_section (unionF Ps) x) =
                     Lim_seq (λ i, ν x (dep_section (Ps i) x))) as Heq.
        { intros x.  symmetry.
          cut (is_lim_seq (λ i, ν x (dep_section (Ps i) x)) (ν x (dep_section (unionF Ps) x))).
          { intros Heq. apply is_lim_seq_unique in Heq.
            rewrite Heq => //=. }
          assert (eq_prop (dep_section (unionF Ps) x) (unionF (λ i, dep_section (Ps i) x))) as ->.
          { clear. firstorder. }
          apply measure_incr_seq; eauto.
          * intros i. specialize (HPs i) as (?&?). eapply dep_section_measurable; eauto.
          * clear -Hmono. firstorder.
        }
        setoid_rewrite Heq.
        apply measurable_Lim'.
        intros i. destruct (HPs i); eauto.
    }
    set (pi :=
           (λ UV, ∃ U Vc, F1 U ∧ F3 Vc ∧
                          UV ≡ (λ ab, U (projT1 ab) ∧ fun_inv (f (projT1 ab)) Vc (projT2 ab)))).
    (*
    set (pi := (λ UV, ∃ U V, F1 U ∧ F2 V ∧ UV ≡ (λ ab, U (fst ab) ∧ V (snd ab)))).
     *)
    assert (Hpiproper: Proper (eq_prop ==> iff) pi).
    { intros ?? Heq. rewrite /pi. by setoid_rewrite Heq. }
    assert (Hpiclosed: ∀ P Q, pi P → pi Q → pi (P ∩ Q)).
    { intros P Q HP HQ.
      destruct HP as (A1&B1&?&?&HequivP).
      destruct HQ as (A2&B2&?&?&HequivQ).
      exists (A1 ∩ A2). exists (B1 ∩ B2). 
      split_and!; try apply sigma_closed_pair_intersect; eauto.
      { rewrite HequivP HequivQ; clear; firstorder. }
    }
    set (pi' := mkPiSystem _ pi Hpiproper Hpiclosed).
    assert (eq_prop (dep_sum_sigma) (minimal_sigma pi')) as ->.
    { apply le_prop_antisym.
      - apply minimal_sigma_lub.
        intros ? (U'&V'&?&?&->).
        apply minimal_sigma_ub; do 2 eexists; split_and!; eauto.
      - apply minimal_sigma_lub.
        intros ? (U'&V'&?&?&->).
        apply minimal_sigma_ub; do 2 eexists; split_and!; eauto.
    }
    set (F' := mkDynkin _ F HFproper HFfull HFset_minus HF_closed_unions).
    transitivity F'; last by rewrite //=.
    assert (le_prop (minimal_dynkin pi') F') as <-.
    { apply minimal_dynkin_lub. intros ? (U'&V'&?&?&->). rewrite /F'//=.
      split; eauto.
      * apply minimal_sigma_ub; do 2 eexists; split_and!; eauto.
      * eapply measurable_ext.
        { intros x'. rewrite (measure_dep_section_fun_inv). done. }
        measurable. apply wpt_fun_measurable.
    }
    rewrite pi_sigma_equiv_dynkin. done.
  Qed.

  Lemma dep_sum_measure_ex_integral UV:
    dep_sum_sigma UV → ex_integral μ (λ x, ν x (dep_section UV x)).
  Proof.
    intros Hin.
    apply (ex_integral_mono_ex _ _ (λ x, Mbound)).
    * intros x. rewrite Rabs_right; last auto.
      transitivity ( ν x (λ _, True)); eauto.
      apply measure_mono; auto.
      { eapply dep_section_measurable; eauto. }
      { clear. firstorder. }
    * apply measurable_measure_dep. auto.
    * apply ex_integral_const.
  Qed.

  Lemma  dep_sum_measure_additivity1 (Us : nat → sigT B → Prop):
    (∀ i : nat, dep_sum_sigma (Us i)) →
    disjointF Us →
    is_series (λ n : nat, Integral μ (λ x : A, ν x (dep_section (Us n) x)))
        (Integral μ (λ x : A, ν x (dep_section (unionF Us) x))).
  Proof.
    intros HUs Hdisj.
    rewrite /is_series.
    assert (∀ n', ex_integral μ (λ x : A, ν x (dep_section (Us n') x))).
    { intros n'. eapply dep_sum_measure_ex_integral. eauto. }
    cut (is_lim_seq (sum_n (λ n : nat, Integral μ (λ x : A, ν x (dep_section (Us n) x))))
                    (Integral μ (λ x, ν x (dep_section (unionF Us) x)))); first by auto.
    {
      eapply is_lim_seq_ext.
      { intros. apply Integral_sum_n. intros n' Hle; eauto. }
      edestruct (is_integral_levi_pos_ex μ) as (?&His); last eapply His.
      { apply measurable_measure_dep. auto. }
      { intros x. rewrite //=.
        eapply measure_additivity; eauto.
        * intros i. eapply dep_section_measurable; eauto.
        * intros i j Hneq z Hfalse.
          eapply Hdisj; eauto.
      }
      {
        intros x n => //=. induction n => //=.
        - rewrite sum_O. by apply Rge_le.
        - rewrite sum_Sn => //=. rewrite /plus//=.
          specialize (measure_nonneg (ν x) (dep_section (Us (S n)) x)).
          nra.
      }
      {
        intros x n => //=. rewrite sum_Sn. rewrite /plus//=.
        specialize (measure_nonneg (ν x) (dep_section (Us (S n)) x)).
        nra.
      }
      { intros n. apply ex_integral_sum_n; eauto. }
      { 
        exists (μ (λ _, True) * Mbound).
        intros ? (n&His).
        eapply (is_integral_mono _ _ _ (λ x_, Mbound)); eauto.
        (* eapply (is_integral_mono _ _ _ (λ x_, ν (λ _, True))); eauto. *)
        { intros a; rewrite //=; etransitivity; last eapply (Hbounded a).
         rewrite -measure_sum_n_additivity.
          * apply measure_mono; last by done; auto.
            ** apply sigma_closed_range_union. intros.
               eapply dep_section_measurable; eauto.
            ** auto.
          * intros; eapply dep_section_measurable; eauto.
          * apply disjointF_dep_section; auto. 
        }
        rewrite Rmult_comm.
        apply is_integral_const.
      }
    }
  Qed.

  Lemma dep_sum_measure_proper:
    Proper (eq_prop ==> eq)
           (λ UV : {x : A & B x} → Prop, Integral μ (λ x : A, (ν x) (dep_section UV x))).
  Proof.
    intros UV UV' Heq. apply Integral_ext.
    intros x. by apply measure_proper, dep_section_proper.
  Qed.

  Definition dep_sum_measure : measure dep_sum_sigma.
  Proof.
    refine {| measure_fun := λ UV, Integral μ (λ x, ν x (dep_section UV x)) |}.
    - apply dep_sum_measure_proper.
    - abstract (intros; apply Integral_ge0; intros; apply Rge_le; auto).
    - assert (∀ x : A, dep_section (empty_set : _ → Prop) x ≡ ∅) as Heq by auto.
      abstract (setoid_rewrite Heq; setoid_rewrite measure_empty; apply Integral_0).
    - apply dep_sum_measure_additivity1. 
  Defined.

  Lemma dep_sum_measure_ex_integral' UV P:
    dep_sum_sigma UV →
    (ex_integral μ (λ x, ν x (dep_section UV x)) → P (dep_sum_measure UV)) →
    P (dep_sum_measure UV).
  Proof.
    intros ? HP. apply HP. eapply dep_sum_measure_ex_integral; eauto.
  Qed.

  Lemma dep_sum_measure_ex_integral_eq UV v:
    dep_sum_sigma UV →
    (ex_integral μ (λ x, ν x (dep_section UV x)) → dep_sum_measure UV = v) →
    dep_sum_measure UV = v.
  Proof.
    intros. apply dep_sum_measure_ex_integral'; eauto.
  Qed.

  Lemma dep_sum_measure_bound :
    dep_sum_measure (λ _, True) <= Mbound * μ (λ _, True).
  Proof.
    rewrite -Integral_const.
    eapply Integral_mono_pos.
      * intros x. apply Rge_le, measure_nonneg.
      * eauto.
      * apply measurable_measure_dep. eauto.
      * apply ex_integral_const.
  Qed.
  

  Definition wpt_dep_proj (wpt: weighted_partition (dep_sum_sigma)) (x: A)
    : weighted_partition (F2 x).
  Proof.
    refine (wpt_indicator_scal_list (map (λ rU, (fst rU, dep_section (snd rU) x)) wpt) _).
    { abstract (intros r U (rU&Heq&Hin)%in_map_iff;
                inversion Heq; subst; eapply (@dep_section_measurable _ _); eauto;
                eapply In_wpt_snd_measurable; eauto). }
  Defined.

  Lemma wpt_dep_spec wpt x y:
    wpt_fun (wpt_dep_proj wpt x) y = wpt_fun wpt (existT x y).
  Proof.
    rewrite /wpt_dep_proj.
    edestruct (@wpt_indicator_scal_list_spec2) as [(Hneg&->)|Hcase]. 
    { specialize (wpt_map_snd_disjoint wpt).
      generalize (wpt_list wpt). clear. induction l.
      * rewrite //=. intros. econstructor.
      * rewrite //=. inversion 1 as [|?? Hdisj]; subst.
        econstructor; last eauto.
        intros z (Hin1&Hin2).
        apply (Hdisj (existT x z)).
        split; auto.
        apply union_list_inv in Hin2 as (V&Hin&?).
        apply in_map_iff in Hin as ((?&?)&?&Hin). subst.
        apply in_map_iff in Hin as ((?&V')&Heq&?); subst. inversion Heq; subst.
        eapply (union_list_intro _ _ V'); eauto.
        apply in_map_iff. exists (r, V'); auto.
    }
    - exfalso. destruct (partition_union (wpt_part wpt) (existT x y)) as (UV&?&?); first done.
      eapply (Hneg (wpt_fun wpt (existT x y)) (dep_section UV x)).
      * apply in_map_iff. exists (wpt_fun wpt (existT x y), UV) => //=.
        split; eauto. apply wpt_fun_eq1; eauto. 
      * auto.
    - destruct Hcase as (r&U&Hin&HU&->).
      symmetry. apply in_map_iff in Hin.
      destruct Hin as ((r'&U')&Heq&Hin). rewrite //= in Hin.
      inversion Heq; subst.
      eapply wpt_fun_eq2; eauto.
  Qed.

  Lemma tonelli_dep_measurable_wpt wpt:
    measurable (λ x, Integral (ν x) (λ y, @wpt_fun _ (dep_sum_sigma) wpt (existT x y))) F1 (borel _).
  Proof.
    induction wpt using wpt_induction.
    - eapply measurable_proper'; eauto.
      intros x. apply Integral_ext; eauto.
    - setoid_rewrite wpt_indicator_dep_section => //=.
      setoid_rewrite Integral_wpt.
      setoid_rewrite wpt_integral_indicator.
      apply measurable_measure_dep. auto.
    - eapply measurable_ext.
      { intros x. symmetry. setoid_rewrite wpt_plus_spec at 1. rewrite Integral_plus. done.
        * setoid_rewrite <-wpt_dep_spec. apply ex_integral_wpt.
        * setoid_rewrite <-wpt_dep_spec. apply ex_integral_wpt.
      }
      apply measurable_plus; eauto.
    - eapply measurable_ext.
      { intros x. symmetry. setoid_rewrite wpt_scal_spec at 1. rewrite Integral_scal. done.
        setoid_rewrite <-wpt_dep_spec. apply ex_integral_wpt.
      }
      apply measurable_scal; eauto.
  Qed.

  Lemma tonelli_dep_pos_measurable (g: sigT B → R):
    (∀ x, 0 <= g x) →
    measurable g (dep_sum_sigma) (borel _) →
    measurable (λ x : A, Integral (ν x) (λ y, g (existT x y))) F1 (borel _).
  Proof.
    intros Hpos Hmeas.
    edestruct (wpt_approx_measurable _ Hpos Hmeas) as (wptn&?&?&?&?).
    assert (∀ x, (λ x : A, Integral (ν x) (λ y, g (existT x y))) x =
                 (λ x : A, Lim_seq (λ n, Integral (ν x) (wpt_fun (wpt_dep_proj (wptn n) x)))) x)
      as Heq.
    { intros x. symmetry.
      apply Integral_pos_mct; eauto.
      { eapply (fun_dep_measurable). eauto. }
      { intros. rewrite //=. setoid_rewrite wpt_dep_spec. eauto.  }
      { intros. rewrite ?wpt_dep_spec; eauto. }
      { intros. rewrite ?wpt_dep_spec; eauto. }
    }
    setoid_rewrite Heq.
    apply measurable_Lim'.
    intros n. eapply measurable_ext; last eapply (tonelli_dep_measurable_wpt (wptn n)).
    intros x => //=. apply Integral_ext => ?. by rewrite wpt_dep_spec.
  Qed.

  Lemma tonelli_dep_measurable (g : sigT B → R):
    measurable g dep_sum_sigma (borel _) →
    measurable (λ x : A, Integral (ν x) (λ y, g (existT x y))) F1 (borel _).
  Proof.
    intros. rewrite /Integral.
    eapply measurable_ext.
    { intros x. rewrite -?Integral_equiv_Pos_integral; eauto using Rmax_r. }
    { apply measurable_plus; last (apply measurable_opp).
      - eapply (tonelli_dep_pos_measurable (λ x, Rmax (g x) 0)); eauto using Rmax_r.
        apply measurable_Rmax; measurable.
      - eapply (tonelli_dep_pos_measurable (λ x, Rmax (-g x) 0)); eauto using Rmax_r.
        apply measurable_Rmax; measurable.
    }
  Qed.

  Lemma ex_integral_left_section_measure U:
    dep_sum_sigma U →
    ex_integral μ (λ x : A, ν x (dep_section U x)).
  Proof.
    intros Hsigma.
    apply (ex_integral_mono_ex _ _ (λ x, Mbound)).
    * intros x. rewrite Rabs_right; last auto.
      transitivity ( ν x (λ _, True)); eauto.
      apply measure_mono; auto.
      { eapply dep_section_measurable; eauto. }
      { clear. firstorder. }
    * apply measurable_measure_dep. auto.
    * apply ex_integral_const.
  Qed.

  Lemma ex_integral_dep_wpt (wpt: weighted_partition (dep_sum_sigma)) x:
    ex_integral (ν x) (λ y, wpt_fun wpt (existT x y)).
  Proof.
    eapply (ex_integral_ext _ (wpt_fun (wpt_dep_proj wpt x))).
    { intros ?. by rewrite wpt_dep_spec. }
    apply ex_integral_wpt.
  Qed.

  Hint Resolve ex_integral_dep_wpt.

  Lemma tonelli_dep_integral_wpt (wpt : weighted_partition (dep_sum_sigma)):
    is_integral μ (λ x, Integral (ν x) (λ y, wpt_fun wpt (existT x y)))
                (Integral (dep_sum_measure) (wpt_fun wpt)).
  Proof.
    induction wpt as [wpt1 wpt2 Heq| | | ] using wpt_induction.
    - eapply is_integral_ext.
      { intros x. eapply Integral_ext => y. rewrite -(Heq _). done. }
      rewrite -(Integral_ext _ (wpt_fun wpt1) (wpt_fun wpt2)) //.
    - rewrite Integral_wpt wpt_integral_indicator //=.
      setoid_rewrite wpt_indicator_dep_section.
      setoid_rewrite Integral_wpt. setoid_rewrite wpt_integral_indicator.
      apply Integral_correct, ex_integral_left_section_measure.
      done.
    - rewrite Integral_wpt wpt_integral_plus.
      setoid_rewrite wpt_plus_spec. 
      eapply is_integral_ext.
      { intros x. rewrite Integral_plus; eauto. }
      apply is_integral_plus; rewrite -Integral_wpt; done.
    - rewrite Integral_wpt wpt_integral_scal.
      setoid_rewrite wpt_scal_spec. 
      eapply is_integral_ext.
      { intros x. rewrite Integral_scal; eauto. }
      apply is_integral_scal; rewrite -Integral_wpt; done.
  Qed.

  Global Instance is_lim_seq_Proper:
    Proper (pointwise_relation _ eq ==> eq ==> iff) is_lim_seq.
  Proof.
    intros ?? Heq ?? Heq'. split; subst; apply is_lim_seq_ext; done.
  Qed.

  Global Instance Lim_seq_Proper:
    Proper (pointwise_relation _ eq ==> eq) Lim_seq.
  Proof.
    intros ?? Heq. apply Lim_seq_ext; eauto.
  Qed.

  Lemma tonelli_dep_Integral_wpt (wpt : weighted_partition (dep_sum_sigma)):
    Integral μ (λ x, Integral (ν x) (λ y, wpt_fun wpt (existT x y))) =
                (Integral (dep_sum_measure) (wpt_fun wpt)).
  Proof.
    apply is_integral_unique, tonelli_dep_integral_wpt.
  Qed.

  Lemma fubini_dep_pos_integral_aux g:
    (∀ x, 0 <= g x) →
    measurable g (dep_sum_sigma) (borel _) →
    ex_integral (dep_sum_measure) g →
    almost_everywhere_meas μ (λ x, ex_integral (ν x) (λ y, g (existT x y))) →
    is_integral μ (λ x, Integral (ν x) (λ y, g (existT x y)))
                (Integral (dep_sum_measure) g).
  Proof.
    intros Hpos Hmeas Hae Hex.
    edestruct (wpt_approx_measurable _ Hpos Hmeas) as (wptn&?&?&?&?).
    feed pose proof (is_integral_mct_ex (dep_sum_measure) (λ n, wpt_fun (wptn n)) g g)
      as Hmct; eauto using ex_integral_wpt.
    { intros x n. rewrite Rabs_right; eauto. }
    destruct Hmct as (_&His).
    generalize His => His_alt.
    setoid_rewrite <-tonelli_dep_Integral_wpt in His.
    feed pose proof (is_integral_levi_ae_ex μ
                             (λ n, λ x, Integral (ν x) (λ y, (wpt_fun (wptn n) (existT x y))))
                             (λ x, Integral (ν x) (λ y, g (existT x y)))) as Hlevi; eauto.
    { apply tonelli_dep_measurable; eauto. }
    { eapply almost_everywhere_meas_mono; eauto.
      { measurable; eauto.
        * intros n. apply tonelli_dep_measurable_wpt.
        * eapply measurable_comp; first apply tonelli_dep_measurable; eauto.
          eapply measurable_Finite.
      }
      intros x Hbound.
      eapply is_integral_mct_ex; eauto.
      intros. rewrite Rabs_right; eauto.
    }
    { apply almost_everywhere_meas_everywhere.
      intros. apply Integral_mono; eauto using ex_integral_wpt. }
    { intros; eexists; eapply tonelli_dep_integral_wpt. }
    { exists (Integral (dep_sum_measure) g).  intros r (n&His_r).
      apply is_integral_unique in His_r as <-.
      eapply is_lim_seq_incr_compare in His; eauto.
      { intros n'.  rewrite ?tonelli_dep_Integral_wpt.
        eapply Integral_mono; eauto using ex_integral_wpt. }
    }
    destruct Hlevi as (Hex'&His').
    eauto.
    cut ((Integral μ (λ x : A, Integral (ν x) (λ y, g (existT x y)))) =
         (Integral (dep_sum_measure) g)).
    { intros <-. by apply Integral_correct. }
    apply is_lim_seq_unique in His.
    apply is_lim_seq_unique in His'. congruence.
  Qed.

  Lemma fubini_dep_pos_integral_ae g:
    (∀ x, 0 <= g x) →
    measurable g (dep_sum_sigma) (borel _) →
    ex_integral (dep_sum_measure) g →
    almost_everywhere_meas μ (λ x, ex_integral (ν x) (λ y, g (existT x y))).
  Proof.
    intros Hpos Hmeas Hex.
    assert (Himp: ∀ P Q : Prop, P ∧ (P → Q) → P ∧ Q) by intuition.
    assert (∀ i,
        measurable (λ x : A, Integral (ν x) (λ y, Rmin (g (existT x y)) (INR i))) F1 (borel _)).
    { 
      intros i.
      apply (tonelli_dep_measurable (λ ab, Rmin (g ab) (INR i))).
      apply measurable_Rmin; measurable.
    }
    apply Himp.
    split.
    { apply sigma_closed_complements.
      eapply (sigma_proper _ F1
              (λ x, ex_finite_lim_seq (λ n, Integral (ν x) (λ y, Rmin (g (existT x y)) (INR n))))).
      { intros x. rewrite -ex_integral_ex_finite_lim_min; eauto using fun_dep_measurable. }
      measurable.
    }
    intros HF.
    apply Rle_antisym; last apply Rge_le, measure_nonneg.
    apply Rnot_gt_le. intros Hgt.
    destruct Hex as (v&His).
    feed pose proof (is_integral_ge0 (dep_sum_measure) g v); eauto.

    cut (∀ k, F1 (unionF (λ n x, INR (S k) <= Integral (ν x) (λ y, Rmin (g (existT x y)) (INR n)))) ∧
              μ (unionF (λ n x, INR (S k) <= Integral (ν x) (λ y, Rmin (g (existT x y)) (INR n))))
              <= (v + 1) / INR (S k)).
    { intros Hsmall.
      edestruct (archimed_cor1 (μ (compl (λ x : A, ex_integral (ν x) (λ y, g (existT x y)))) / (v + 1))) as
          (n&Hr1&Hr2).
      { apply Rdiv_lt_0_compat; auto.
        nra. }
      destruct n as [| n]; first by omega.
      destruct (Hsmall n) as (Hmeas'&Hsize).
      cut (μ (compl (λ x : A, ex_integral (ν x) (λ y, g (existT x y)))) <=
           μ (unionF (λ n0 (x : A), INR (S n) <= Integral (ν x) (λ y, Rmin (g (existT x y)) (INR n0))))).
      { intros Hle.
        apply (Rmult_lt_compat_r (v + 1)) in Hr1; last by nra.
        field_simplify in Hr1; try nra.
        feed pose proof (pos_INR' (S n)); auto. nra.
      }
      clear -HF Hpos Hmeas Hmeas' Hfmeas. 
      apply measure_mono; auto.
      intros x Hneg.
      apply Classical_Pred_Type.not_all_not_ex.
      intros Hall.
      apply Hneg. apply ex_integral_sup_min; eauto.
      { eapply fun_dep_measurable; eauto. }
      exists (INR (S n)).
      intros ? (?&<-).
      left. apply Rnot_le_gt. eauto.
    }
    intros k. apply Himp. 
    split.
    { apply sigma_closed_unions => i; apply measurable_fun_ge; eauto. }
    intros Hmeas'.
    feed pose proof (ex_integral_Rmin (dep_sum_measure) g) as Hex; eauto.
    assert (Hlen: ∀ n , μ (λ x, INR (S k) <= Integral (ν x) (λ y, Rmin (g (existT x y)) (INR n)))
                         <= (v + 1) / INR (S k)).
    { 
      intros n.
      specialize (Hex n).
      destruct Hex as (v'&His').
      assert (v' <= v + 1).
      { transitivity v; last nra.
        eapply is_integral_mono; eauto.
        intros => //=. apply Rmin_l. }
      transitivity (v' / INR (S k)); last first.
      { rewrite /Rdiv. apply Rmult_le_compat_r; auto. left.
        apply Rinv_0_lt_compat. apply pos_INR'. omega. }
      apply is_integral_bound_measure_above; auto.
      - intros. apply Rge_le, Integral_ge0. intros; apply Rmin_case_strong; eauto using pos_INR.
      - rewrite -(is_integral_unique _ _ _ His').
        apply (fubini_dep_pos_integral_aux (λ x, Rmin (g x) (INR n))).
        * intros. apply Rmin_case_strong; eauto using pos_INR.
        * apply measurable_Rmin; measurable.
        * apply ex_integral_Rmin; eauto.
        * apply almost_everywhere_meas_everywhere. intros x.
          apply ex_integral_Rmin; eauto.
          eapply fun_dep_measurable; eauto.
      - apply pos_INR'; omega.
    }
    eapply (is_lim_seq_le _ _ (Finite _) (Finite _)); last eapply is_lim_seq_const.
    { intros n. apply Hlen. }
    apply measure_incr_seq.
    - intros n. apply measurable_fun_ge; eauto.
    - intros i x Hle. etransitivity; eauto.
      apply Integral_mono; eauto.
      * intros. apply Rle_min_compat_l, le_INR. omega.
      * apply ex_integral_Rmin; eauto.
        eapply fun_dep_measurable; eauto.
      * apply ex_integral_Rmin; eauto.
        eapply fun_dep_measurable; eauto.
  Qed.

  Lemma fubini_dep_pos_integral g:
    (∀ x, 0 <= g x) →
    ex_integral (dep_sum_measure) g →
    is_integral μ (λ x, Integral (ν x) (λ y, g (existT x y)))
                (Integral ((dep_sum_measure)) g).
  Proof.
    intros Hpos Hex.
    apply fubini_dep_pos_integral_aux; eauto.
    apply fubini_dep_pos_integral_ae; eauto.
  Qed.

  Lemma fubini_dep_pos_Integral g:
    (∀ x, 0 <= g x) →
    ex_integral (dep_sum_measure) g →
    Integral μ (λ x, Integral (ν x) (λ y, g (existT x y))) =
                (Integral ((dep_sum_measure)) g).
  Proof.
    intros Hpos Hex.
    apply is_integral_unique, fubini_dep_pos_integral; eauto.
  Qed.

  Lemma fubini_dep_integral g:
    ex_integral (dep_sum_measure) g →
    is_integral μ (λ x, Integral (ν x) (λ y, g (existT x y)))
                (Integral ((dep_sum_measure)) g).
  Proof.
    intros Hex.
    cut (ex_integral μ (λ x, Integral (ν x) (λ y, g (existT x y))) ∧
         (Integral μ (λ x, Integral (ν x) (λ y, g (existT x y))) = Integral (dep_sum_measure) g)).
    { intros (Hex'&His). rewrite -His. apply Integral_correct; eauto. }
    assert (Himp: ∀ P Q : Prop, P ∧ (P → Q) → P ∧ Q) by intuition.
    apply Himp; clear Himp; split.
    - apply ex_integral_Rabs.
      { apply tonelli_dep_measurable. destruct Hex. eapply is_integral_measurable; eauto. }
      feed pose proof (fubini_dep_pos_integral_ae (λ x, Rabs (g x))); eauto.
      { measurable. eauto. }
      { apply ex_integral_Rabs in Hex; eauto. }
      eapply (ex_integral_ae_mono_ex _ _ (λ x, Integral (ν x) (λ y, Rabs (g (existT x y))))).
      {
        eapply almost_everywhere_meas_mono; last eauto.
        { apply measurable_fun_le_inv.
          * apply measurable_Rabs, measurable_Rabs. apply tonelli_dep_measurable.
            eauto.
          * apply (tonelli_dep_measurable (λ x, Rabs (g x))).
            measurable. eauto.
        }
        intros x Hex'. rewrite Rabs_right; last eauto.
        apply Integral_Rabs.
        right; split; eauto.
        eapply fun_dep_measurable; eauto. 
      }
      * apply measurable_Rabs.
        apply tonelli_dep_measurable; eauto.
      * eexists. eapply (fubini_dep_pos_integral_aux (λ x, Rabs (g x))); eauto.
        { apply measurable_Rabs; eauto. }
        { apply ex_integral_Rabs in Hex; eauto. }
    - rewrite [a in _ = a]Integral_alt.
      apply ex_integral_alt in Hex as (?&?&?).
      feed pose proof (fubini_dep_pos_integral (λ x, Rmax (g x) 0)) as Hfb1; eauto using Rmax_r.
      feed pose proof (fubini_dep_pos_integral (λ x, Rmax (- g x) 0)) as Hfb2; eauto using Rmax_r.
      rewrite -(is_integral_unique _ _ _ Hfb1).
      rewrite -(is_integral_unique _ _ _ Hfb2).
      rewrite -Integral_minus; try (eexists; eauto).
      feed pose proof (fubini_dep_pos_integral_ae (λ x, Rmax (g x) 0)) as Hfb1';
        eauto using Rmax_r.
      feed pose proof (fubini_dep_pos_integral_ae (λ x, Rmax (- g x) 0)) as Hfb2';
        eauto using Rmax_r.
      generalize (almost_everywhere_meas_conj _ _ _ Hfb1' Hfb2').
      intros Hae. apply Integral_ae_ext_weak; last first.
      { apply measurable_minus; eauto. }
      eapply almost_everywhere_meas_mono; last eapply Hae.
      { apply measurable_fun_eq_inv; eauto.
        * apply tonelli_dep_measurable; auto.  
        * apply measurable_minus; eauto.
      }
      intros x (Hex1&Hex2).
      rewrite -Integral_minus; eauto.
      apply Integral_ext.
      intros y. do 2 apply Rmax_case_strong; nra.
  Qed.

  Lemma fubini_dep_integral_ae g:
    ex_integral (dep_sum_measure) g →
    almost_everywhere_meas μ (λ x, ex_integral (ν x) (λ y, g (existT x y))).
  Proof.
    intros Hex.
    feed pose proof (fubini_dep_pos_integral_ae (λ x, Rabs (g x))); eauto.
    { measurable. eauto. }
    { apply ex_integral_Rabs in Hex; eauto. }
    eapply almost_everywhere_meas_ext; eauto.
    intros x. symmetry. apply ex_integral_Rabs; eauto using fun_dep_measurable.
  Qed.

  Lemma fubini_dep_Integral g:
    ex_integral (dep_sum_measure) g →
    Integral μ (λ x, Integral (ν x) (λ y, g (existT x y))) = (Integral ((dep_sum_measure)) g).
  Proof.
    intros. eapply is_integral_unique, fubini_dep_integral; auto.
  Qed.

  Lemma tonelli_dep_integral g:
    (∀ x, 0 <= g x) →
    measurable g (dep_sum_sigma) (borel _) →
    almost_everywhere_meas μ (λ x, ex_integral (ν x) (λ y, g (existT x y))) →
    ex_integral μ (λ x, Integral (ν x) (λ y, g (existT x y))) →
    ex_integral (dep_sum_measure) g.
  Proof.
    intros Hpos Hmeas Hae Hex.
    apply ex_integral_sup_min; eauto.
    destruct Hex as (v&His).
    exists v. intros ? (n&<-).
    rewrite -(is_integral_unique _ _ _ His).
    rewrite -fubini_dep_Integral; last first.
    { apply ex_integral_Rmin; eauto. }
    apply Integral_ae_mono.
    { eapply almost_everywhere_meas_mono; eauto.
      { apply measurable_fun_le_inv; eauto.
        apply (tonelli_dep_measurable (λ x, Rmin (g x) (INR n))).
        measurable. }
      intros x Hex. apply Integral_mono; eauto using ex_integral_Rmin.
      intros. apply Rmin_l.
    }
    { eexists. eapply (fubini_dep_integral (λ x, Rmin (g x) (INR n))), ex_integral_Rmin; eauto. }
    { eexists; eauto. }
  Qed.

  Lemma dep_sum_ae (P: A → Prop) (Q: ∀ a, B a → Prop):
    almost_everywhere_meas μ P →
    (∀ a, almost_everywhere_meas (ν a) (Q a)) →
    dep_sum_sigma (λ ip, Q (projT1 ip) (projT2 ip)) →
    almost_everywhere_meas dep_sum_measure (λ ip, Q (projT1 ip) (projT2 ip)).
  Proof.
    intros. split; auto.
    rewrite //=. 
    erewrite <-Integral_0.
    apply Integral_ext.
    intros a. destruct (H0 a); eauto.
  Qed.
  
End dep_sum_measure.

End dep_sum_sigma.