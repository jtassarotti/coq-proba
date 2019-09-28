Require Import Reals Psatz Omega Fourier.
From stdpp Require Import tactics.
From discprob.measure Require Export measures borel outer_measure.
From discprob.prob Require Import countable rearrange double.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
Require ClassicalEpsilon ClassicalEpsilon.

Definition Interval a b : Type := { x : R | a <= x <= b }.
Coercion interval_R {a b} (x : Interval a b) : R := (sval x).

Hint Resolve Rabs_pos Rle_ge.
Hint Resolve disc_neighbourhood.
    
(* Lebesgue number lemma. Most pencil and paper proofs don't seem
   to use this, but I think it makes the proof that the outer measure
   of intervals is equal to their length simpler *)

Lemma lebesgue_number_lemma (I: Type) D (U: I → (R → Prop)) :
  compact D →
  (∀ x, D x → ∃ i, U i x) →
  (∀ i, open (U i)) →
  ∃ δ, 0 < δ ∧ ∀ x, D x → ∃ i, (∀ z, D z → ball x δ z → U i z).
Proof.
  intros Hcompact Hcover Hopen.
  apply Classical_Pred_Type.not_all_not_ex => Hnot.
  assert (Hneg: ∀ y, 0 < y → (∃ x, D x ∧ ∀ i, ∃ z, D z ∧ ball x y z ∧ ¬ U i z)).
  { 
    intros y. specialize (Hnot y) => Hpos.
    apply Classical_Prop.not_and_or in Hnot as [?|Hnot]; first by auto.
    apply Classical_Pred_Type.not_all_ex_not in Hnot.
    destruct Hnot as (x&Hnot).
    apply Classical_Prop.imply_to_and in Hnot as (HDx&Hnot).
    exists x; split; auto. intros i.
    unshelve (eapply Classical_Pred_Type.not_ex_all_not in Hnot); first by exact i.
    apply Classical_Pred_Type.not_all_ex_not in Hnot.
    destruct Hnot as (r&Hnot).
    exists r.
    apply Classical_Prop.imply_to_and in Hnot as (?&Hnot).
    apply Classical_Prop.imply_to_and in Hnot as (?&Hnot).
    split_and!; auto.
  }
  unshelve (refine (let un : nat → R := _ in _)).
  { intros n.  specialize (Hneg (/(INR (n+1)))).
    apply ClassicalEpsilon.constructive_indefinite_description in Hneg as (x&Hspec).
    exact x.
    abstract (apply Rinv_0_lt_compat, pos_INR'; omega).
  }
  edestruct (Bolzano_Weierstrass un) as (x&Hneighbor); eauto.
  { intros.  rewrite /un. destruct ClassicalEpsilon.constructive_indefinite_description.
    intuition.
  }
  rewrite /ValAdh in Hneighbor.
  assert (D x).
  {
    apply adherence_P2; first by apply compact_P2.
    rewrite /adherence/point_adherent => V Hneighbor'.
    edestruct (Hneighbor V O) as (p&Hge&HV); eauto. 
    exists (un p). rewrite /intersection_domain; split; auto.
    rewrite /un. destruct ClassicalEpsilon.constructive_indefinite_description; intuition.
  }
  edestruct (Hcover x) as (i&HU); auto.
  destruct (open_included_disc (U i) x) as (δ&Hsub); eauto.
  edestruct (archimed_cor1 (δ / 2)) as (N&HleN&?).
  { destruct δ => //=. nra. }
  destruct (Hneighbor (ball x (δ/2)) N) as (N'&Hle&Hin).
  { apply ball_neighbourhood. destruct δ => //=. nra. }
  rewrite /un in Hin.
  destruct (ClassicalEpsilon.constructive_indefinite_description) as (xbad&?&Hneg').
  specialize (Hneg' i). destruct Hneg' as (z&HD&Hball&Hneg').
  apply Hneg'. apply Hsub. 
  apply disc_ball.
  apply: (ball_le _ (δ/2 + (/ (INR (N' + 1))))).
  { destruct δ as (δ&?) => //=.
     replace δ with (δ/2 + δ/2) at 2 by nra.
     apply Rplus_le_compat_l.
     transitivity (/ (INR N)); last (rewrite //= in HleN; nra).
     left; apply Rinv_lt_contravar.
     * assert (0 < INR N) by (apply pos_INR'; omega).
       assert (0 < INR (N' + 1)) by (apply pos_INR'; omega).
       nra.
     * apply lt_INR. omega.
  }
  eapply ball_triangle; eauto. 
Qed.

Hint Resolve Rabs_pos Rle_ge.

Section Interval_UniformSpace.
  Variable a b : R.
  Implicit Types x y : Interval a b.
  
  Definition Interval_ball (x: Interval a b) eps y := ball (x : R) eps y.
  Definition Interval_ball_center x (e: posreal) : Interval_ball x e x := @ball_center _ _ _.
  Definition Interval_ball_sym x y e := @ball_sym _ (x : R) y e.
  Definition Interval_ball_triangle x y e := @ball_triangle _ (x : R) y e.
  Definition Interval_UniformSpace_mixin : UniformSpace.mixin_of (Interval a b).
  Proof.
    apply (UniformSpace.Mixin _ Interval_ball
                              Interval_ball_center
                              Interval_ball_sym
                              Interval_ball_triangle).   
  Defined.

  Canonical Interval_UniformSpace := UniformSpace.Pack _ Interval_UniformSpace_mixin (Interval a b).
End Interval_UniformSpace.

(* Lebesgue measure restricted to finite intervals of the Reals *)

Section lebesgue_measure.
  Context {a b : R}.

  (* TODO: deduce these from the versions on R in borel.v *)
  Lemma borel_gen_closed_ray1 :
    le_prop (minimal_sigma (λ (U: Interval a b → Prop), ∃ x y, U = (λ z, x < z <= y)))
            (minimal_sigma (λ (U : Interval a b → Prop), ∃ x, U = (λ z, z <= x))).
  Proof.
    apply minimal_sigma_lub. intros ? (x&y&?); subst.
    assert ((λ z : Interval a b, x < z ∧ z <= y) ≡
            (λ z : Interval a b, z <= y) ∩ compl (λ z : Interval a b, z <= x)) as Heq.
    { intros z; split => //=.
      * intros (?&?). split => //=; intros Hneg. nra.
      * intros (?&Hcomp). split => //=. apply Rnot_ge_lt. intros Hge.
        apply Hcomp. nra.
    }
    rewrite Heq.
    apply sigma_closed_pair_intersect.
    * apply minimal_sigma_ub. eexists; eauto.
    * apply sigma_closed_complements,  minimal_sigma_ub. eexists; eauto.
  Qed.

  Lemma borel_gen_closed_ray2 :
    le_prop (borel (Interval_UniformSpace a b))
    (minimal_sigma (λ (U : Interval a b → Prop), ∃ x, U = (λ z, z <= x))).
  Proof.
    etransitivity; last eapply borel_gen_closed_ray1.
    apply minimal_sigma_lub => U HopenU.
    unshelve (eapply sigma_proper; last eapply sigma_closed_unions).
    {
      intros n.
      destruct (pickle_inv [countType of (nat * nat * nat)] n) as [((x&y)&N)|]; last exact ∅.
      set (V := (λ z : Interval a b, a + (INR x / INR y) - (1/(INR N)) < z ∧
                                     z <= a + (INR x / INR y))).
      destruct (ClassicalEpsilon.excluded_middle_informative
                  (V ⊆ U)).
      * exact V.
      * exact ∅.
    }
    { 
      split.
      * intros HUz. specialize (HopenU _ HUz).
        destruct HopenU as ((δ&Hpos)&Hdelta).
        destruct x as (x&Hx1&Hx2) => //=.
        edestruct (archimed_cor1 δ) as (K&?&?); first by nra.
        assert (0 < / INR K).
        { apply Rinv_0_lt_compat, pos_INR'; done. }
        edestruct (archimed_rat_dense1 (/INR K) (x - a)) as (n&m&(?&?)&?); auto; try nra.
        exists (pickle (n, m, K)).
        rewrite pickleK_inv.
        destruct ClassicalEpsilon.excluded_middle_informative as [Hsub|Hnsub]; last first.
        { exfalso. destruct Hnsub.
          intros (z&?&?). rewrite //=. intros [? ?].
          apply Hdelta => //=.
          rewrite /ball//=/Interval_ball/ball//=/AbsRing_ball//=/abs//=.
          rewrite /minus/opp/plus//=.
          assert (z - a >= z - x) by nra.
          apply Rabs_case => Hcase; try nra.
        }
        rewrite //=. nra.
      * intros (n&HUn).
        destruct pickle_inv as [((n'&m')&K)|]; rewrite //= in HUn.
        destruct ClassicalEpsilon.excluded_middle_informative as [Hsub|Hnsub];
          rewrite //= in HUn.
        by apply Hsub.
    }
    intros i.
    destruct (pickle_inv [countType of nat * nat * nat] i) as [((n&m)&K)|] eqn:Heq; rewrite Heq.
    * set (V := λ z : Interval a b, a + INR n / INR m - 1 / INR K < z ∧ z <= a + INR n / INR m).
      destruct (Classical_Prop.classic (V ⊆ U)) as [Hsub|Hnsub].
      ** apply minimal_sigma_ub. do 2 eexists. rewrite /V.
         destruct ClassicalEpsilon.excluded_middle_informative as [|Hnsub]; first reflexivity.
         exfalso; apply Hnsub. eauto.
      ** eapply sigma_proper; last eapply sigma_empty_set; rewrite //=.
         destruct ClassicalEpsilon.excluded_middle_informative as [Hsub'|]; last reflexivity.
         exfalso; apply Hnsub; eauto.
    * apply sigma_empty_set.
  Qed.

  Definition leb_outer_set_cand (U : Interval a b → Prop)  (Us: nat → R * R) :=
    U ⊆ unionF (λ i, open_interval (fst (Us i)) (snd (Us i))).

  Definition leb_outer_set U Us :=
    leb_outer_set_cand U Us ∧ ex_series (λ i, Rabs (snd (Us i) - fst (Us i))).


  Lemma leb_outer_set_proj2 U Us :
    leb_outer_set U Us →
    ex_series (λ i, Rabs (snd (Us i) - fst (Us i))).
  Proof. intros [? ?]; auto. Qed.

  Hint Resolve leb_outer_set_proj2.

  Definition trivial_outer_set (i : nat) :=
    match i with
    | O => (a - 1, b + 1)
    | _ => (a, a)
    end.

  Lemma leb_outer_set_non_empty U : leb_outer_set U (trivial_outer_set).
  Proof.
    split.
    - intros (x&Hl&Hu) _. exists O. split => //=; nra.
    - apply ex_series_incr_1 => //=.
      exists 0. apply is_series_0 => ? //=.
        by rewrite Rminus_eq_0 Rabs_R0.
  Qed.

  Definition leb_outer_pre_fun U r :=
    ∃ Us, leb_outer_set U Us ∧ - Series (λ i, Rabs (snd (Us i) - fst (Us i))) = r.

  Lemma leb_outer_pre_fun_non_empty U : ∃ r, leb_outer_pre_fun U r.
  Proof.
    eexists. exists trivial_outer_set.
    split; first apply leb_outer_set_non_empty. reflexivity.
  Qed.

  Lemma leb_outer_pre_fun_bound U : bound (leb_outer_pre_fun U).
  Proof.
    exists 0. intros ? (Us&(Hcand&Hex)&<-).
    apply Ropp_le_cancel. rewrite Ropp_involutive Ropp_0.
    apply Series_pos => n. auto.
  Qed.

  Definition leb_outer_fun (U : Interval a b → Prop) : R.
    refine (- sval (completeness (leb_outer_pre_fun U) _ _)).
    - apply leb_outer_pre_fun_bound.
    - apply leb_outer_pre_fun_non_empty.
  Defined.

  Lemma leb_outer_fun_glb U r :
    (∀ Us, leb_outer_set U Us → r <= Series (λ i, Rabs (snd (Us i) - fst (Us i)))) →
    r <= leb_outer_fun U.
  Proof.
    intros HUs. rewrite /leb_outer_fun. destruct (completeness) as (r'&Hlub).
    rewrite //=. destruct Hlub as (?&Hlub).
    cut (r' <= - r).
    { nra.  }
    apply Hlub. intros x (?&(?&<-)).
    apply Ropp_le_contravar. auto.
  Qed.
  
  Lemma leb_outer_fun_lb U Us:
    leb_outer_set U Us → leb_outer_fun U <= Series (λ i, Rabs (snd (Us i) - fst (Us i))).
  Proof.
    intros HUs. rewrite /leb_outer_fun. destruct (completeness) as (r'&Hlub).
    rewrite //=. destruct Hlub as (Hub&Hlub).
    rewrite /is_upper_bound in Hub.
    apply Ropp_le_cancel. rewrite Ropp_involutive. etransitivity; last eapply Hub.
    { reflexivity. }
    eexists; eauto.
  Qed.

  Global Instance is_upper_bound_proper : Proper (eq_prop ==> eq ==> iff) is_upper_bound.
  Proof.
    intros U U' Heq ?? ->. firstorder.
  Qed.

  Lemma completeness_proper E E' Hpf1 Hpf1' Hpf2 Hpf2' :
    eq_prop E E' → sval (completeness E Hpf1 Hpf2) = sval (completeness E' Hpf1' Hpf2').
  Proof.
    intros Heq.
    destruct completeness as (x&Hub&Hlub).
    destruct completeness as (x'&Hub'&Hlub').
    rewrite //=.
    apply Rle_antisym.
    - apply Hlub. rewrite Heq; done.
    - apply Hlub'. rewrite -Heq; done.
  Qed.

  Global Instance leb_outer_set_anti : Proper (le_prop --> eq ==> impl) leb_outer_set.
  Proof.
    intros U U' Hle Us Us' ->. rewrite /leb_outer_set/leb_outer_set_cand.
    intros (?&?); split; auto.
    transitivity U;
    etransitivity; eauto.
  Qed.

  Global Instance leb_outer_set_proper : Proper (eq_prop ==> eq ==> iff) leb_outer_set.
  Proof.
    intros U U' Heq Us Us' ->. rewrite /leb_outer_set/leb_outer_set_cand.
    rewrite Heq. done.
  Qed.

  Global Instance leb_outer_pre_fun_proper : Proper (eq_prop ==> eq ==> iff) leb_outer_pre_fun.
  Proof.
    intros U U' Heq ?? ->. rewrite /leb_outer_pre_fun. setoid_rewrite Heq. done.
  Qed.
    
  Global Instance leb_outer_fun_proper : Proper (eq_prop ==> eq) leb_outer_fun.
  Proof.
    intros U U' Heq.
    rewrite /leb_outer_fun => //=. apply Ropp_eq_compat.
    apply completeness_proper. intros x. by rewrite Heq.
  Qed.

  Lemma leb_outer_fun_empty :
    leb_outer_fun ∅ = 0.
  Proof.
    apply Rle_antisym.
    etransitivity; first eapply (leb_outer_fun_lb _ (λ i, (a, a))).
    { split => //=. exists 0. apply is_series_0 => ?.
        by rewrite Rminus_eq_0 Rabs_R0. }
    right. apply Series_0 => ? //=. by rewrite Rminus_eq_0 Rabs_R0.
    apply leb_outer_fun_glb => Us ?.
    apply Series_pos => ?. auto.
  Qed.

  Instance leb_outer_fun_mono : Proper (le_prop ==> Rle) leb_outer_fun.
  Proof.
    intros U U' Hle.
    apply leb_outer_fun_glb => Us.
    intros H. apply leb_outer_fun_lb.
    setoid_rewrite <-Hle in H. done.
  Qed.

  Lemma leb_outer_eps_close U eps :
    0 < eps → 
    ∃ Us, leb_outer_set U Us
          ∧ Series (λ i, Rabs (snd (Us i) - fst (Us i))) < leb_outer_fun U + eps.
  Proof.
    intros Hpos.
    apply Classical_Pred_Type.not_all_not_ex.
    intros Hneg.
    apply (Rlt_not_ge (leb_outer_fun U) (leb_outer_fun U + eps)); first nra. 
    apply Rle_ge, leb_outer_fun_glb => Us Hin.
    apply Rnot_gt_le. intros Hgt. apply (Hneg Us).
    split; auto.
  Qed.

  Lemma leb_outer_eps_close' U eps :
    0 < eps → 
    { Us : _ | leb_outer_set U Us
          ∧ Series (λ i, Rabs (snd (Us i) - fst (Us i))) < leb_outer_fun U + eps }.
  Proof.
    intros.
    apply (ClassicalEpsilon.constructive_indefinite_description).
    by apply leb_outer_eps_close.
  Qed.

  Lemma ex_series_double_shift aseq:
    (∀ j k, j = O ∨ k = O → aseq (j, k) = 0) →
    ex_series (λ j : nat, Series (λ k : nat, Rabs (aseq (S j, S k)))) →
    ex_series (λ j : nat, Series (λ k : nat, Rabs (aseq (j, k)))).
  Proof.
    intros Hjk Hex.
    eapply (ex_series_ext (λ j : nat, Series (λ k : nat, Rabs (aseq (j, S k))))).
    { intros j. destruct j.
      * apply Series_ext => k. rewrite ?Hjk //=; by left.
      * symmetry. rewrite Series_incr_1_aux; last first.
        { rewrite Hjk; last by right. rewrite Rabs_R0. done. }
        done.
    }
      by apply ex_series_incr_1.
  Qed.

  Definition int_len := λ xy, Rabs (snd xy - fst xy).

  Lemma Series_double_shift aseq:
    (∀ j k, j = O ∨ k = O → aseq (j, k) = 0) →
    (Series (λ j : nat, Series (λ n : nat, aseq (j, n)))) =
    (Series (λ j : nat, Series (λ n : nat, aseq (S j, S n)))).
  Proof.
    intros. rewrite Series_incr_1_aux.
    * apply Series_ext.
      intros n'. rewrite Series_incr_1_aux; eauto.
    * rewrite Series_0; eauto.
  Qed.
  
  Lemma leb_outer_fun_subadditivity Us :
    ex_series (λ n, leb_outer_fun (Us n)) →
    leb_outer_fun (unionF Us) <= Series (λ n, leb_outer_fun (Us n)).
  Proof.
    intros Hex.
    apply le_epsilon => eps Hpos.
    assert (Hpos_scale: ∀ n, 0 < eps/2 * (pow (1/2) n)).
    { intros n. cut (0 < (1 /2)^n); first by (intros; nra).
      apply pow_lt. nra. }
    set (Us' := λ n : nat, match pickle_inv [countType of nat * nat] n with
                           | Some (n, i) =>
                             (sval (leb_outer_eps_close' (Us n) (eps/2 * (pow (1/2) n))
                                                         (Hpos_scale n)) i)
                           | None => (a, a)
                           end).
    assert (unionF Us ⊆ unionF (λ i, open_interval (fst (Us' i)) (snd (Us' i)))).
    { intros x (n&Hin).
      destruct (leb_outer_eps_close' (Us n) _ (Hpos_scale n)) as (Vs&(Hcover&?)&?) eqn:Heq.
      generalize (Hcover x Hin). intros (i&Hin').
      exists (pickle (n, i)).
      rewrite /Us'. rewrite pickleK_inv => //=.
      rewrite Heq. auto.
    }

    set (len := λ xy, Rabs (snd xy - fst xy)).
    set (aseq0 := λ mn, match mn with
                       | (S m, S n) => 
                         (sval (leb_outer_eps_close' (Us m) (eps/2 * (pow (1/2) m))
                                                         (Hpos_scale m)) n)
                       | (_, _) => (a, a)
                    end).
    set (aseq := λ mn, len (aseq0 mn)). 
    set (σ := λ n, match pickle_inv [countType of nat * nat] n with
                   | Some (m, n) => (S m, S n)
                   | _ => (O, O)
                   end).
    assert (∀ n, (aseq \o σ) n = len (Us' n)).
    { intros n.   rewrite /aseq/σ/Us'//=.
      destruct pickle_inv as [(?&?)|] => //=.
    }
    assert (His_plus: is_series (λ n : nat, leb_outer_fun (Us n) + eps/2 * (pow (1/2) n))
                                (Series (λ n, leb_outer_fun (Us n)) + eps)).
    { apply: is_series_plus.
      * apply Series_correct; auto.
      * assert (eps = (eps/2 * / ( 1 - 1/2))) as Heq by field. rewrite {2}Heq.
        apply: is_series_scal.
        apply: is_series_geom.
        rewrite Rabs_right; nra.
    }
    assert (double.double_summable aseq).
    { 
      apply ex_series_rows_ds.
      intros j.
      * rewrite /aseq/aseq0.
        destruct j => //=.
        ** eexists; eapply is_series_0. by rewrite /aseq/aseq0 /len Rminus_eq_0 ?Rabs_R0.
        ** apply ex_series_incr_1 => //=.
           destruct (leb_outer_eps_close') as (?&Hex'&?); auto.
           eapply ex_series_ext; last eapply Hex'.
           intros ?. rewrite /len Rabs_Rabsolu => //=. 
      * apply: ex_series_double_shift.
        { intros j k [?|?]; subst => //=; try destruct j;
                                       rewrite /aseq/aseq0 /len ?Rminus_eq_0 ?Rabs_R0 //.
        }
        apply: ex_series_le; last by (eexists; eapply His_plus).
        intros n. rewrite /aseq//=.
        destruct (leb_outer_eps_close') as (?&Hex'&Hlt); auto.
        etransitivity; last by (left; eapply Hlt).
        right. rewrite /norm//=/abs//=. rewrite Rabs_right.
        ** apply Series_ext => ? //=. by rewrite Rabs_Rabsolu.
        ** apply Rle_ge, Series_pos => ?. auto. 
    }
    feed pose proof (series_double_covering' aseq σ) as His; auto.
    { intros n n'. rewrite /σ/aseq.
      specialize (pickle_invK [countType of nat * nat] n).
      specialize (pickle_invK [countType of nat * nat] n').
      destruct (pickle_inv) as [(?&?)|] => //=; destruct (pickle_inv) as [(?&?)|] => //=.
      intros <- ? ?. inversion 1. subst => //=.
      rewrite /len//= Rminus_eq_0 Rabs_R0 //=.
    }
    { rewrite /aseq/aseq0. intros ([|m]&[|n]) => //=;
      rewrite /len ?Rminus_eq_0 ?Rabs_R0 //=.
      exists (pickle (m, n)). 
      rewrite /σ pickleK_inv => //=. }
    etransitivity.
    * apply (leb_outer_fun_lb _ (aseq0 \o σ)). split.
      ** intros x (n&Hin). 
         destruct (leb_outer_eps_close' (Us n) _ (Hpos_scale n)) as (Vs&(Hcover&?)&?) eqn:Heq.
         generalize (Hcover x Hin). intros (i&Hin').
         exists (pickle (n, i)).
         rewrite /aseq0/σ//=. rewrite pickleK_inv => //=.
         rewrite Heq. auto.
      ** eexists; eauto.
    * rewrite (is_series_unique _ _ His).
      rewrite -(is_series_unique _ _ His_plus). 
      rewrite Series_double_shift; last first.
      { intros ?? [?|?]; subst; try destruct j; rewrite /aseq/len//= ?Rminus_eq_0 ?Rabs_R0 //=. }
      apply Series_le; last by (eexists; eauto).
      intros n.
      split.
      ** apply Series_pos => n'. rewrite /aseq/len//=. apply Rle_ge, Rabs_pos.
      ** rewrite /aseq/aseq0//=. destruct (leb_outer_eps_close') as (?&?&Hdone); eauto.
         rewrite /len//=. nra.
  Qed.
  
  Lemma Rabs_Rminus_eq_0 x:
    Rabs (x - x) = 0.
  Proof.
    rewrite Rminus_eq_0 Rabs_R0 //.
  Qed.

  Hint Resolve Rabs_Rminus_eq_0.

  Inductive decreasing_intervals : list (R * R) → Prop :=
      | di_nil: decreasing_intervals nil
      | di_singleton a b: a <= b → decreasing_intervals ((a, b) :: nil)
      | di_cons a1 b1 a2 b2 l:
          b1 <= a2 <= b2 →
          decreasing_intervals ((a1, b1) :: l) →
          decreasing_intervals ((a2, b2) :: (a1, b1) :: l).

  Lemma open_interval_subset_len x1 y1 x2 y2:
    x1 <= y1 →
    open_interval x1 y1 ⊆ open_interval x2 y2 →
    Rabs (y1 - x1) <= Rabs (y2 - x2).
  Proof.
    intros Hle Hsubseteq. rewrite Rabs_right; last by nra.
    destruct Hle; last first.
    - assert (y1 - x1 = 0) as -> by nra. auto.
    - specialize (Rabs_pos (y2 - x2)). intros Hpos.
      apply le_epsilon => eps ?.
      destruct (Rlt_dec (eps) (y1 - x1)) as [?|?]; last by nra.
      destruct (Hsubseteq (x1 + eps/2)).
      { split; nra. }
      rewrite Rabs_right; last by nra. 
      destruct (Hsubseteq (y1 - eps/2)).
      { split; nra. }
      nra.
  Qed.

  Lemma open_interval_subset_left_ordering x1 y1 x2 y2:
    x1 < y1 →
    open_interval x1 y1 ⊆ open_interval x2 y2 →
    x2 <= x1.
  Proof.
    intros Hle Hsubseteq. 
    cut (∀ eps : R, 0 < eps → eps < (y1 - x1) → x2 <= x1 + eps).
    { intros Hcut. apply le_epsilon.
      intros eps Hlt.
      destruct (Rlt_dec (eps) (y1 - x1)) as [?|?].
      * eauto.
      * transitivity (x1 + (y1 - x1)/2); eauto.
        { eapply Hcut; nra.  }
        nra.
    }
    intros.
    destruct (Hsubseteq (x1 + eps/2)).
    { split; nra. }
    destruct (Hsubseteq (y1 - eps/2)).
    { split; nra. }
    nra.
  Qed.

  Lemma open_interval_subset_right_ordering x1 y1 x2 y2:
    x1 < y1 →
    open_interval x1 y1 ⊆ open_interval x2 y2 →
    y1 <= y2.
  Proof.
    intros Hle Hsubseteq. 
    cut (∀ eps : R, 0 < eps → eps < (y1 - x1) → y1 <= y2 + eps).
    { intros Hcut. apply le_epsilon.
      intros eps Hlt.
      destruct (Rlt_dec (eps) (y1 - x1)) as [?|?].
      * eauto.
      * transitivity (y2 + (y1 - x1)/2); eauto.
        { eapply Hcut; nra.  }
        nra.
    }
    intros.
    destruct (Hsubseteq (x1 + eps/2)).
    { split; nra. }
    destruct (Hsubseteq (y1 - eps/2)).
    { split; nra. }
    nra.
  Qed.

  Lemma open_interval_subset_non_empty x1 y1 x2 y2:
    x1 < y1 →
    open_interval x1 y1 ⊆ open_interval x2 y2 →
    x2 <= y2.
  Proof.
    intros Hle Hopen.
    transitivity x1.
    { eapply open_interval_subset_left_ordering; eauto; nra.  }
    transitivity y1; first nra.
    { eapply open_interval_subset_right_ordering; eauto; nra.  }
  Qed.

  Hint Resolve open_interval_subset_non_empty.

  Lemma decreasing_intervals_1 l
    (Hdec : decreasing_intervals l):
    ∀ x' y', In (x', y') l → x' <= y'.
  Proof.
    induction Hdec => //=.
    - intros ??. destruct 1 as [Heq|[]]. inversion Heq; subst; done.
    - intros ??. destruct 1 as [Heq|[]].
      * inversion Heq; subst; nra.
      * eapply IHHdec. by left.
      * eapply IHHdec. by right. 
  Qed.

  Lemma decreasing_intervals_2 x1 y1 l
    (Hdec : decreasing_intervals ((x1, y1) :: l)):
    ∀ x' y', In (x', y') l → y' <= x1.
  Proof.
    remember ((x1, y1) :: l) as l0 eqn:Heql. revert x1 y1 l Heql.
    induction Hdec.
    - congruence. 
    - intros x1 y1 l. inversion 1; subst. intros ?? [].
    - intros x1 y1 l0. inversion 1; subst.
      intros ??. inversion 1.
      * inversion H1.  subst. intuition.
      * assert (y' <= a1); eauto.
        assert (a1 <= b1).
        { eapply decreasing_intervals_1. eauto. by left. }
        nra.
  Qed.

  Lemma decreasing_intervals_3 x1 y1 l
    (Hdec : decreasing_intervals ((x1, y1) :: l)):
    ∀ x' y', In (x', y') ((x1, y1) :: l) → y' <= y1.
  Proof.
    intros ?? [Heq1|Htl].
    - inversion Heq1; reflexivity.
    - transitivity x1.
      * eapply decreasing_intervals_2; eauto. 
      * eapply decreasing_intervals_1; eauto; by left.
  Qed.

  Lemma intervals_contained_length Us (l: list (R * R)) :
    decreasing_intervals l → 
    ex_series (λ i : nat, Rabs ((Us i).2 - (Us i).1)) →
    (∀ a b, In (a, b) l → ∃ i, (open_interval a b) ⊆ open_interval (Us i).1 (Us i).2) →
    fold_right Rplus 0 (map int_len l) <= Series (λ i : nat, Rabs ((Us i).2 - (Us i).1)).
  Proof.
    intros Hdec. revert Us.
    induction Hdec as [ | x y | x1 y1 x2 y2 l] => Us Hex Hcov.
    - rewrite //=. apply Series_pos => n; auto.
    - rewrite //= Rplus_0_r.
      destruct (Hcov x y) as (i&Hsub); first by left.
      rewrite -(Series_bump i (int_len (x, y))).
      apply Series_le.
      * intros n. destruct Nat.eq_dec => //=; split; rewrite /int_len; auto; try nra.
        apply open_interval_subset_len => //=. subst; done.
      * auto.
    - rewrite //=.
      destruct (Req_dec x2 y2).
      { subst.  rewrite /int_len//=. rewrite Rabs_Rminus_eq_0 Rplus_0_l.
        apply IHHdec; eauto. intros. eapply Hcov. by right. }
      edestruct (Hcov x2 y2) as (i&Hsubseteq).
      { by left. }
      assert (ex_series
                (λ i0 : nat, Rabs
       ((match Nat.eq_dec i0 i with | left _ => ((Us i).1, x2) | _ => Us i0 end).2 -
       ((match Nat.eq_dec i0 i with | left _ => ((Us i).1, x2) | _ => Us i0 end).1)))).
      { 
        apply: ex_series_le; eauto.
        intros n. rewrite /norm//=/abs//= Rabs_Rabsolu.
        destruct Nat.eq_dec => //=; last reflexivity.
        subst.
        apply open_interval_subset_len.
        * apply open_interval_subset_left_ordering in Hsubseteq; nra.
        * apply open_interval_subset_right_ordering in Hsubseteq; last by nra.
          intros x [? ?]. split; nra.
      }
      feed pose proof (IHHdec (λ n, match eq_nat_dec n i with
                                    | left _ => ((Us i).1, x2)
                                    | _ => Us n
                                    end)); auto.
      { 
        intros a' b' Hin. edestruct (Hcov a' b') as (n&Hin'); first by right.
        exists n. destruct Nat.eq_dec => //=; subst.
        intros x Hrange. specialize (Hin' _ Hrange) as (?&?).
        destruct Hrange as (?&?).
        split; first nra.
        eapply (Rlt_le_trans _ b'); first eassumption.
        transitivity y1; last by nra.
        eapply decreasing_intervals_3; eauto.
      }
      rewrite //= in H1.
      etransitivity.
      { eapply Rplus_le_compat_l. eassumption. }
      rewrite -(Series_bump i (int_len (x2, y2))).
      rewrite -Series_plus; auto; last by (eexists; eapply is_series_bump).
      apply: Series_le; eauto.
      intros n; split.
      * destruct Nat.eq_dec => //=; ring_simplify; auto.
        rewrite /int_len.
        replace 0 with (0 + 0) by nra. apply Rplus_le_compat; auto.
      * destruct Nat.eq_dec => //=; ring_simplify; auto; try reflexivity.
        rewrite /int_len//=.
        subst.
        rewrite ?Rabs_right.
        { ring_simplify.  cut (y2 <= snd (Us i)); first (intros; nra).
          eapply open_interval_subset_right_ordering; eauto. nra.
        }
        ** eapply open_interval_subset_non_empty in Hsubseteq; nra. 
        ** eapply open_interval_subset_left_ordering in Hsubseteq; nra. 
        ** eapply open_interval_subset_right_ordering in Hsubseteq; nra. 
  Qed.


  Fixpoint decreasing_intervals_delta x δ n :=
    match n with
      0 => []
    | S n' => (x - δ, x) :: decreasing_intervals_delta (x - δ) δ n'
    end.

  Lemma decreasing_intervals_delta1  x δ n :
    0 < δ →
    decreasing_intervals (decreasing_intervals_delta x δ n).
  Proof.
    intros Hpos.
    revert x. induction n => x //=.
    - constructor.
    - induction n => //=.
      * constructor. nra.
      * econstructor; eauto. nra.
  Qed.

  Lemma decreasing_intervals_delta2  x δ n :
    0 < δ →
    ∀ a' b', In (a', b') (decreasing_intervals_delta x δ n) →
             ∃ x0, x - (δ * INR n) <= x0 <= x ∧ open_interval a' b' ⊆ ball x0 (δ/2) ∧
                   (∀ z, ball x0 (δ/2) z → x - (δ * INR n) <= z <= x).
  Proof.
    intros Hpos.
    revert x. induction n => x.
    - done. 
    - intros a' b'. intros [Hhd|Htl].
      * exists (x - δ/2); split_and!.
        ** rewrite //=. destruct n; try nra. specialize (pos_INR (S n)) => H. nra.
        ** nra.
        ** inversion Hhd. subst => z [Hr1 Hr2].
           rewrite /ball//=/AbsRing_ball/abs//=/minus/plus/opp//=.
           apply Rabs_case => H; nra.
        ** rewrite S_INR //=. inversion Hhd. subst => z.
           rewrite /ball//=/AbsRing_ball/abs//=/minus/plus/opp//=.
           specialize (pos_INR n).
           apply Rabs_case => H1 H2; nra.
      * edestruct IHn as (x0&(Hlb&?)&?&Hrange); eauto.
        exists x0. split_and!; auto; try nra.
        ** rewrite S_INR. nra.
        ** intros. edestruct Hrange; eauto. rewrite S_INR. nra. 
  Qed.

  Lemma decreasing_intervals_delta3  x δ n :
    0 < δ →
    fold_right Rplus 0 (map int_len (decreasing_intervals_delta x δ n)) = (INR n * δ).
  Proof.
    intros Hpos.
    revert x. induction n => x.
    - rewrite //=. nra.
    - rewrite S_INR //= IHn.
      rewrite /int_len Rabs_right //=; nra.
  Qed.

  Lemma decreasing_interval_covering x y δ:
    0 < δ →
    a <= x → x <= y → y <= b →
    ∃ l, decreasing_intervals l ∧
         (∀ a' b', In (a', b') l → ∃ x0, x <= x0 <= y ∧ open_interval a' b' ⊆ ball x0 (δ/2) ∧
                   (∀ z, open_interval a' b' z → x <= z <= y)) ∧
         fold_right Rplus 0 (map int_len l) = (y - x).
  Proof.
    intros Hpos Hle1 Hle2 Hle3.
    destruct Hle2 as [Hlt|Heq]; last first.
    { subst. exists []; split_and! => //=.
      * econstructor. 
      * nra.
    }
    assert (∃ N, (y - x) / INR N < δ ∧ (0 < N)%nat) as (N&Hsize&HposN).
    { edestruct (archimed_cor1 (δ / (y - x))) as (N&?&Hpos').
      { apply Rdiv_lt_0_compat; nra. }
      exists N; split_and!; auto.
      apply pos_INR' in Hpos'.  rewrite /Rdiv.
      apply (Rmult_lt_reg_r (/ (y - x))).
      { apply Rinv_0_lt_compat; nra. }
      field_simplify; nra.
    }
    assert (0 < INR N) by (apply pos_INR'; auto).
    assert (0 < (/ INR N)) by (apply Rinv_0_lt_compat; auto).
    assert (0 < ((y - x)/ INR N)).
    { rewrite /Rdiv. nra. }
    exists (decreasing_intervals_delta y (( y - x) / INR N) N).
    split_and!.
    - by apply decreasing_intervals_delta1.
    - intros a' b' Hin.
      edestruct (decreasing_intervals_delta2 y ((y - x)/INR N) N) as (x0&(Hlb&Hub)&?&Hrange); eauto.
      exists x0. split_and!.
      * field_simplify in Hlb; nra.
      * auto.
      * etransitivity; eauto. intros z. apply ball_le.
        nra.
      * intros z ?. edestruct Hrange as (Hlb'&Hub'); eauto.
        split; auto. field_simplify in Hlb'; try nra.
    - rewrite decreasing_intervals_delta3 //=. field; nra.
  Qed.

  Lemma leb_outer_fun_interval_length x y :
    a <= x → x <= y → y <= b →
    leb_outer_fun (λ z, x <= z <= y) = y - x.
  Proof.
    intros Hle1 Hle2 Hle3.
    apply Rle_antisym.
    - apply le_epsilon => eps Hpos.
      set (aseq := (λ i, match i with
                         | O => (x - eps/2, y + eps/2)
                         | _ => (a, a)
                         end)).
      assert (ex_series (λ i : nat, Rabs ((aseq i).2 - (aseq i).1))).
      { apply ex_series_incr_1. exists 0. by apply is_series_0. }
      etransitivity.
      * eapply (leb_outer_fun_lb _ aseq).
        split.
        ** intros t [? ?]. exists O. rewrite /open_interval => //=. nra.
        ** apply ex_series_incr_1. exists 0. apply is_series_0.
           rewrite //= Rminus_eq_0 Rabs_R0 //.
      * rewrite Series_incr_1 //=. rewrite Series_0; auto.
        rewrite Rabs_right; nra.
    - apply leb_outer_fun_glb => Us Houter.
      edestruct (lebesgue_number_lemma nat (λ z, x <= z <= y)
                                       (λ n, open_interval (fst (Us n)) (snd (Us n))))
                as (δ&Hpos&Hdelta).
      { apply (compact_P3 x y). }
      { intros x' Hin.
        assert (Hrange: a <= x' <= b) by nra.
        destruct Houter as (Hcov&?).
        destruct (Hcov (exist _ x' Hrange)); eauto. }
      { intros. apply open_interval_open. }
      edestruct (decreasing_interval_covering x y δ) as (l&Hdec&Hin&Hlen); eauto.
      rewrite -Hlen.
      apply intervals_contained_length; eauto.
      intros.
      edestruct Hin as (x0&?&Hball&Hrange); eauto.
      edestruct (Hdelta x0) as (n&Hsub); eauto.
      exists n. intros z' Hin'. eapply Hsub; eauto.
      eapply ball_le; last eapply Hball; eauto. nra.
  Qed.

  Lemma leb_outer_fun_interval_length_arbitrary1 x y :
    leb_outer_fun (λ z, x <= z <= y) <= Rabs (y - x).
  Proof.
    destruct (Rle_dec a y) as [?|Hnle]; last first.
    { apply Rnot_le_gt in Hnle. transitivity 0; last by auto.
      right. rewrite (leb_outer_fun_proper _ ∅); first by rewrite leb_outer_fun_empty.
      intros (z&?&?) => //=; split => //=. intros. nra. }
    destruct (Rle_dec x b) as [?|Hnle]; last first.
    { apply Rnot_le_gt in Hnle. transitivity 0; last by auto.
      right. rewrite (leb_outer_fun_proper _ ∅); first by rewrite leb_outer_fun_empty.
      intros (z&?&?) => //=; split => //=. intros. nra. }
    destruct (Rle_dec a b) as [Hle|Hnle]; last first.
    { apply Rnot_le_gt in Hnle. transitivity 0; last by auto.
      right. rewrite (leb_outer_fun_proper _ ∅); first by rewrite leb_outer_fun_empty.
      intros (z&?&?) => //=; split => //=. intros. nra. }
    destruct (Rle_dec x y) as [Hle'|Hnle]; last first.
    { apply Rnot_le_gt in Hnle. transitivity 0; last by auto.
      right. rewrite (leb_outer_fun_proper _ ∅); first by rewrite leb_outer_fun_empty.
      intros (z&?&?) => //=; split => //=. intros. nra. }
    transitivity (leb_outer_fun (λ z, Rmax a x <= z <= Rmin y b)).
    {
      apply leb_outer_fun_mono. intros (z&(?&?)) => //=. intros (?&?); split.
      * apply Rmax_case_strong; intros; try nra.  
      * apply Rmin_case_strong; intros; try nra.  
    }
    rewrite leb_outer_fun_interval_length; auto using Rmax_r, Rmax_l, Rmin_r, Rmin_l.
    - apply Rmax_case_strong; apply Rmin_case_strong; intros; rewrite ?Rabs_right; nra.
    - apply Rmax_case_strong; apply Rmin_case_strong; intros; nra.
  Qed.

  Lemma leb_outer_fun_interval_length_arbitrary2 x y :
    leb_outer_fun (λ z, x < z <= y) <= Rabs (y - x).
  Proof.
    etransitivity; last eapply leb_outer_fun_interval_length_arbitrary1.
    apply leb_outer_fun_mono => z; nra.
  Qed.

  Lemma leb_outer_fun_interval_length_arbitrary3 x y :
    leb_outer_fun (λ z, x < z < y) <= Rabs (y - x).
  Proof.
    etransitivity; last eapply leb_outer_fun_interval_length_arbitrary1.
    apply leb_outer_fun_mono => z; nra.
  Qed.
  
  Definition leb_outer_measure : outer_measure (Interval a b).
  refine {| outer_measure_fun := leb_outer_fun |}.
  - apply leb_outer_fun_empty. 
  - apply leb_outer_fun_subadditivity.
  Defined.

  Definition leb_measure := outer_measure_measure leb_outer_measure.
  
  Lemma norm_R_right (r: R):
    0 <= r → norm r = r.
  Proof. intros; rewrite /norm//=/abs//= Rabs_right; nra. Qed.

  Lemma leb_borel_measurable :
    le_prop (borel _) (outer_measure_sigma leb_outer_measure).
  Proof.
    etransitivity; first apply borel_gen_closed_ray2.
    apply minimal_sigma_lub. intros ? (x&->).
    apply outer_measurable_ge => V.
    apply Rle_ge, le_epsilon => eps Hpos.
    edestruct (leb_outer_eps_close V eps) as (Us&HUs_spec&?); auto.
    assert (Hbound: ∀ n, Rabs ((Us n).2 - (Us n).1) >=
                 leb_outer_measure (open_interval (Us n).1 (Us n).2 ∩
                                                 (λ z, z <= x)) +
                 leb_outer_measure (open_interval (Us n).1 (Us n).2 ∩
                                                 compl (λ z, z <= x))).
    { intros n. 
      destruct (Rle_dec x (Us n).1).
      {
        assert (eq_prop (λ x0 : Interval a b, (open_interval (Us n).1 (Us n).2 ∩ Rle^~ x) x0)
                        ∅) as Heq1.
        { intros (z&?&?) => //=. split.
          * intros ((Hr1&Hr2)&Hr3); try nra.
          * inversion 1.
        }
        assert (eq_prop
                  (λ x0 : Interval a b, (open_interval (Us n).1 (Us n).2 ∩ compl (Rle^~ x)) x0)
                  (open_interval (Us n).1 (Us n).2)) as Heq2.
        { intros (z&?&?) => //=. split.
          * rewrite /compl. intros ((Hr1&Hr2)&Hr3); split; try nra.
          * rewrite /compl/open_interval; intros (Hr1&Hr2); split_and!; try nra.
        }
        rewrite Heq1 Heq2.
        rewrite /leb_outer_measure//= leb_outer_fun_empty Rplus_0_l.
        apply Rle_ge. apply leb_outer_fun_interval_length_arbitrary3.
      }
      destruct (Rlt_dec x (Us n).2).
      * assert (eq_prop (λ x0 : Interval a b, (open_interval (Us n).1 (Us n).2 ∩ Rle^~ x) x0)
                      (λ x0, (Us n).1 < x0 <= x)) as Heq1.
        { intros (z&?&?) => //=. split.
          * intros ((Hr1&Hr2)&Hr3); split; nra.
          * rewrite /open_interval; intros; split_and!; try nra. 
        }
        assert (eq_prop
                  (λ x0 : Interval a b, (open_interval (Us n).1 (Us n).2 ∩ compl (Rle^~ x)) x0)
                  (λ x0, x < x0 < (Us n).2)) as Heq2.
        { intros (z&?&?) => //=. split.
          * rewrite /compl. intros ((Hr1&Hr2)&Hr3); split; try nra.
          * rewrite /compl/open_interval; intros; split_and!; nra.
        }
        rewrite Heq1 Heq2.
        apply Rle_ge.
        setoid_rewrite leb_outer_fun_interval_length_arbitrary2.
        setoid_rewrite leb_outer_fun_interval_length_arbitrary3.
        repeat apply Rabs_case; intros; try nra.
      * assert (eq_prop (λ x0 : Interval a b, (open_interval (Us n).1 (Us n).2 ∩ Rle^~ x) x0)
                        (open_interval (Us n).1 (Us n).2)) as Heq1.
        { intros (z&?&?) => //=. split.
          * intros ((Hr1&Hr2)&Hr3); split; nra.
          * rewrite /open_interval; intros; split_and!; try nra. 
        }
        assert (eq_prop
                  (λ x0 : Interval a b, (open_interval (Us n).1 (Us n).2 ∩ compl (Rle^~ x)) x0)
                  ∅) as Heq2.
        { intros (z&?&?) => //=. split.
          * rewrite /compl. intros ((Hr1&Hr2)&Hr3); try nra.
          * inversion 1.
        }
        rewrite Heq1 Heq2.
        rewrite /leb_outer_measure//= leb_outer_fun_empty Rplus_0_r.
        apply Rle_ge. apply leb_outer_fun_interval_length_arbitrary3.
    }
    assert (ex_series (λ n : nat,
         leb_outer_measure (open_interval (Us n).1 (Us n).2 ∩ Rle^~ x))).
    { apply: ex_series_le; eauto => n. rewrite norm_R_right; last apply outer_measure_nonneg.
      specialize (Hbound n). apply Rge_le in Hbound.
      etransitivity; eauto. rewrite -[a in a <= _]Rplus_0_r.
      apply Rplus_le_compat_l; auto using outer_measure_nonneg.
    }
    assert (ex_series (λ n : nat,
         leb_outer_measure (open_interval (Us n).1 (Us n).2 ∩ compl (Rle^~ x)))).
    { apply: ex_series_le; last (destruct HUs_spec as (?&Hex); eapply Hex).
      eauto => n. rewrite norm_R_right; last apply outer_measure_nonneg.
      specialize (Hbound n). apply Rge_le in Hbound.
      etransitivity; eauto. rewrite -[a in a <= _]Rplus_0_l.
      apply Rplus_le_compat_r; auto using outer_measure_nonneg.
    }
    etransitivity; last (by left; eassumption).
    etransitivity; last first.
    { apply Series_le with (a := λ n,
           leb_outer_measure (λ x0 : Interval a b, (open_interval (Us n).1 (Us n).2 ∩ Rle^~ x) x0) +
           leb_outer_measure
             (λ x0 : Interval a b, (open_interval (Us n).1 (Us n).2 ∩ compl (Rle^~ x)) x0));
        last eauto.
      intros n. split; eauto.
      * replace 0 with (0 + 0) by field. apply Rplus_le_compat; apply outer_measure_nonneg.
      * apply Rge_le. eapply Hbound.
    }
    rewrite Series_plus; eauto.
    apply Rplus_le_compat.
    * rewrite /leb_outer_measure//=.
      etransitivity; last eapply leb_outer_fun_subadditivity; eauto.
      apply leb_outer_fun_mono. intros z (HinV&Hrange).
      edestruct (HUs_spec) as (HUs1&HUs2). edestruct (HUs1 _ HinV) as (n&?).
      exists n. split; auto.
    * rewrite /leb_outer_measure//=.
      etransitivity; last eapply leb_outer_fun_subadditivity; eauto.
      apply leb_outer_fun_mono. intros z (HinV&Hrange).
      edestruct (HUs_spec) as (HUs1&HUs2). edestruct (HUs1 _ HinV) as (n&?).
      exists n. split; auto.
  Qed.

End lebesgue_measure.