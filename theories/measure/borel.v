From stdpp Require Import tactics.
Require Import Reals Psatz Omega Fourier.
From discprob.measure Require Export measurable_space.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
Require ClassicalEpsilon.


(* Usually the Borel sigma algebra is defined for more general topological spaces,
   but the Coquelicot hierarchy is oriented around uniform spaces, and in any case
   that will be good enough *)
Definition borel_sigma (A: UniformSpace) : sigma_algebra A := minimal_sigma (@open A).

(* Todo: should we make it global? or only if second countable *)
Instance borel (A: UniformSpace) : measurable_space A :=
  {| measurable_space_sigma := borel_sigma A |}.

Lemma continuous_inverse_open (A B: UniformSpace) (f: A → B) :
  (∀ x, continuous f x) →
  ∀ U, open U → open (fun_inv f U).
Proof.
  rewrite /open. intros Hcont U Hopen x Hf.
  rewrite /continuous_on in Hcont.
  rewrite /fun_inv. specialize (Hcont x). edestruct Hcont as [eps ?]; first eauto.
  exists eps. auto.
Qed.

Lemma continuous_borel_measurable (A B: UniformSpace) (f: A → B) :
  (∀ x, continuous f x) →
  measurable f.
Proof.
  intros Hcont. apply sigma_measurable_generating_sets => U Hopen. apply minimal_sigma_ub.
  by apply continuous_inverse_open.
Qed.

Lemma closed_compl {A: UniformSpace} (U: A → Prop) :
  open U → closed (compl U).
Proof. by apply closed_not. Qed.
Lemma closed_compl' {A: UniformSpace} (U: A → Prop) :
  open (compl U) → closed U.
Proof. intros. eapply closed_ext; last eapply closed_compl; eauto. apply compl_involutive. Qed.
Lemma open_compl {A: UniformSpace} (U: A → Prop) :
  closed U → open (compl U).
Proof. by apply open_not. Qed.
Lemma open_compl' {A: UniformSpace} (U: A → Prop) :
  closed (compl U) → open U.
Proof. intros. eapply open_ext; last eapply open_compl; eauto. apply compl_involutive. Qed.

Hint Resolve closed_compl open_compl closed_compl' open_compl'.

Lemma borel_gen_closed (A: UniformSpace) : eq_sigma (borel A) (minimal_sigma (@closed A)).
Proof.
  rewrite /eq_sigma/eq_prop/borel => U; split; apply minimal_sigma_lub => U' ?;
    rewrite -(compl_involutive U'); apply sigma_closed_complements;
    apply minimal_sigma_ub; auto.
Qed.

Lemma borel_closed (A: UniformSpace) U : closed U → (borel A) U.
Proof.
  intros Hclosed. rewrite borel_gen_closed. by apply minimal_sigma_ub.
Qed.

(* Technically this would be the Borel sigma algebra on the extended reals,
 but we do not have the UniformSpace structure on Rbar *)
Definition Rbar_sigma : sigma_algebra Rbar :=
  minimal_sigma (λ U, ∃ x, U = (λ z, Rbar_le z x)).
Instance Rbar_measurable_space : measurable_space Rbar :=
  {| measurable_space_sigma := Rbar_sigma |}.

Section borel_R.

  Lemma Rbar_sigma_p_infty:
    Rbar_sigma {[p_infty]}.
  Proof.
    assert (Hequiv: eq_prop ({[p_infty]}) (intersectF (λ n, compl (Rbar_le^~ (INR n))))).
    { split.
      - inversion 1; subst.
        intros n. rewrite /compl//=.
      - intros Hall. destruct x as [r | |].
        * exfalso.
          destruct (Rle_dec 0 r).
          ** destruct (archimed_pos r) as (n&Hrange); auto.
             rewrite S_INR in Hrange. eapply (Hall (S n)). rewrite S_INR //=.
             nra.
          ** apply (Hall O) => //=. nra.
        * rewrite //=.
        * exfalso. apply (Hall O) => //=.
    }
    rewrite Hequiv.
    apply sigma_closed_intersections => n.
    apply sigma_closed_complements.
    apply minimal_sigma_ub. exists (INR n). auto.
  Qed.

  Lemma Rbar_sigma_m_infty:
    Rbar_sigma {[m_infty]}.
  Proof.
    assert (Hequiv: eq_prop ({[m_infty]}) (intersectF (λ n, Rbar_le^~ -(INR n)))).
    { split.
      - inversion 1; subst.
        intros n. rewrite /compl//=.
      - intros Hall. destruct x as [r | |].
        * exfalso. destruct (Rle_dec 0 r).
          ** exfalso. feed pose proof (Hall (S O)) as H. rewrite //= in H. nra.
          ** destruct (archimed_pos (-r)) as (n'&?); first nra.
             feed pose proof (Hall (S n')) as H'. rewrite S_INR //= in H' H.
             apply Ropp_le_ge_contravar in H'.
             rewrite Ropp_involutive in H'.
             nra.
        * exfalso. destruct (Hall O).
        * done.
    }
    rewrite Hequiv.
    apply sigma_closed_intersections => n.
    apply minimal_sigma_ub. exists (-INR n). auto.
  Qed.

  Lemma borel_gen_closed_ray1 :
    le_prop (minimal_sigma (λ (U: R → Prop), ∃ x y, U = (λ z, x < z <= y)))
            (minimal_sigma (λ (U : R  → Prop), ∃ x, U = (λ z, z <= x))).
  Proof.
    apply minimal_sigma_lub. intros ? (x&y&?); subst.
    assert ((λ z : R, x < z ∧ z <= y) ≡
            (λ z : R, z <= y) ∩ compl (λ z : R, z <= x)) as Heq.
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
    le_prop (borel (R_UniformSpace))
    (minimal_sigma (λ (U : R → Prop), ∃ x, U = (λ z, z <= x))).
  Proof.
    etransitivity; last eapply borel_gen_closed_ray1.
    apply minimal_sigma_lub => U HopenU.
    unshelve (eapply sigma_proper; last eapply sigma_closed_unions).
    {
      intros n.
      destruct (@pickle_inv [countType of (bool * (nat * nat * nat))] n) as [(b&(x&y)&N)|];
        last exact ∅.
      set (V := (λ z, match b with
                        | true => (INR x / INR y) - (1/(INR N)) < z ∧
                                  z <= (INR x / INR y)
                        | false => - ((INR x / INR y)) - (1/(INR N)) < z ∧
                                  z <= - (INR x / INR y)
                      end)).
      destruct (ClassicalEpsilon.excluded_middle_informative
                  (V ⊆ U)).
      * exact V.
      * exact ∅.
    }
    {
      split.
      * intros HUz. specialize (HopenU _ HUz).
        destruct HopenU as ((δ&Hpos)&Hdelta).
        destruct (Rle_dec 0 x) as [Hle|Hnle].
        ** edestruct (archimed_cor1 δ) as (K&?&?); first by nra.
           assert (0 < / INR K).
           { apply Rinv_0_lt_compat, pos_INR'; done. }
           edestruct (archimed_rat_dense1 (/INR K) x) as (n&m&(?&?)&?); auto; try nra.
           exists (pickle (true, (n, m, K))).
           rewrite pickleK_inv => //=.
           destruct ClassicalEpsilon.excluded_middle_informative as [Hsub|Hnsub]; last first.
           { exfalso. destruct Hnsub.
             intros z. rewrite //=. intros [? ?].
             apply Hdelta => //=.
             rewrite /ball//=/ball//=/AbsRing_ball//=/abs//=.
             rewrite /minus/opp/plus//=.
             assert (z >= z - x) by nra.
             apply Rabs_case => Hcase; try nra.
           }
           rewrite //=. nra.
        ** edestruct (archimed_cor1 δ) as (K&?&?); first by nra.
           assert (0 < / INR K).
           { apply Rinv_0_lt_compat, pos_INR'; done. }
           edestruct (archimed_rat_dense2 (/INR K) x) as (n&m&(?&?)&?); auto; try nra.
           exists (pickle (false, (n, m, K))).
           rewrite pickleK_inv => //=.
           destruct ClassicalEpsilon.excluded_middle_informative as [Hsub|Hnsub]; last first.
           { exfalso. destruct Hnsub.
             intros z. rewrite //=. intros [? ?].
             apply Hdelta => //=.
             rewrite /ball//=/ball//=/AbsRing_ball//=/abs//=.
             rewrite /minus/opp/plus//=.
             assert (z >= z + x) by nra.
             apply Rabs_case => Hcase; try nra.
           }
           rewrite //=. nra.
      * intros (n&HUn).
        destruct pickle_inv as [(b&(n'&m')&K)|]; rewrite //= in HUn.
        destruct ClassicalEpsilon.excluded_middle_informative as [Hsub|Hnsub];
          rewrite //= in HUn.
        by apply Hsub.
    }
    intros i.
    destruct (@pickle_inv [countType of bool * (nat * nat * nat)] i) as
        [(b&(n&m)&K)|] eqn:Heq; rewrite Heq; last by apply sigma_empty_set.
    destruct b.
    * set (V := λ z, INR n / INR m - 1 / INR K < z ∧ z <= INR n / INR m).
      destruct (Classical_Prop.classic (V ⊆ U)) as [Hsub|Hnsub].
      ** apply minimal_sigma_ub. do 2 eexists. rewrite /V.
         destruct ClassicalEpsilon.excluded_middle_informative as [|Hnsub]; first reflexivity.
         exfalso; apply Hnsub. eauto.
      ** eapply sigma_proper; last eapply sigma_empty_set; rewrite //=.
         destruct ClassicalEpsilon.excluded_middle_informative as [Hsub'|]; last reflexivity.
         exfalso; apply Hnsub; eauto.
    * set (V := λ z, - (INR n / INR m) - 1 / INR K < z ∧ z <= - (INR n / INR m)).
      destruct (Classical_Prop.classic (V ⊆ U)) as [Hsub|Hnsub].
      ** apply minimal_sigma_ub. do 2 eexists. rewrite /V.
         destruct ClassicalEpsilon.excluded_middle_informative as [|Hnsub]; first reflexivity.
         exfalso; apply Hnsub. eauto.
      ** eapply sigma_proper; last eapply sigma_empty_set; rewrite //=.
         destruct ClassicalEpsilon.excluded_middle_informative as [Hsub'|]; last reflexivity.
         exfalso; apply Hnsub; eauto.
  Qed.

  Lemma borel_gen_open_ray_gt:
    le_prop (borel (R_UniformSpace))
    (minimal_sigma (λ (U : R → Prop), ∃ x, U = (λ z, x < z))).
  Proof.
    etransitivity; first apply borel_gen_closed_ray2.
    apply minimal_sigma_lub => U. intros (x&Heq).
    subst. eapply (sigma_proper _ _ (compl (λ z, x < z))).
    * rewrite /compl//=. split; nra.
    * apply sigma_closed_complements. apply minimal_sigma_ub.
      eexists; eauto.
  Qed.

  Lemma open_ray_borel_gt z:
    borel _ (λ x, z < x).
  Proof.
    apply minimal_sigma_ub.
    apply open_gt.
  Qed.

  Lemma open_ray_borel_lt z:
    borel _ (λ x, x < z).
  Proof.
    apply minimal_sigma_ub.
    apply open_lt.
  Qed.

  Lemma closed_ray_borel_ge z:
    borel _ (λ x, z <= x).
  Proof.
    apply borel_closed. apply closed_compl'.
    eapply open_ext; last eapply (open_lt z).
    intros x => //=. rewrite /compl.
    nra.
  Qed.

  Lemma closed_ray_borel_le z:
    borel _ (λ x, x <= z).
  Proof.
    apply borel_closed. apply closed_compl'.
    eapply open_ext; last eapply (open_gt z).
    intros x => //=. rewrite /compl.
    nra.
  Qed.

  Lemma closed_interval_borel a b:
    borel _ (λ x, a <= x <= b).
  Proof.
    assert ((λ x, a <= x <= b) ≡ (λ x, a <= x) ∩ (λ x, x <= b)) as ->.
    { split; intros; rewrite //=; nra. }
    eapply sigma_closed_pair_intersect; auto using closed_ray_borel_le, closed_ray_borel_ge.
  Qed.

  Lemma borel_equiv_closed_ray :
    eq_sigma (borel (R_UniformSpace))
    (minimal_sigma (λ (U : R → Prop), ∃ x, U = (λ z, z <= x))).
  Proof.
    intros z; split.
    * apply borel_gen_closed_ray2.
    * apply minimal_sigma_lub. intros U (?&Heq). subst.
      apply (closed_ray_borel_le x).
  Qed.

  Lemma measurable_plus {A: Type} {F: measurable_space A} (f1 f2: A → R) :
    measurable f1 →
    measurable f2 →
    measurable (λ x, f1 x + f2 x).
  Proof.
    intros Hmeas1 Hmeas2.
    eapply sigma_measurable_mono.
    { rewrite /le_sigma; reflexivity. }
    { rewrite /le_sigma/flip. apply borel_gen_open_ray_gt. }
    eapply sigma_measurable_generating_sets.
    intros ? (t&->). rewrite /fun_inv.
    cut (eq_prop (λ a, t < f1 a + f2 a)
                 (unionF (λ n, match @pickle_inv [countType of (bool * (nat * nat))] n with
                               | None => empty_set
                               | Some (b, (n, m)) =>
                                 let r := if b then INR n / INR m else - (INR n / INR m) in
                                 (fun_inv f1 (λ x, Rlt r x)) ∩ (fun_inv f2  (λ x, Rlt (t - r) x))
                               end))).
    { intros ->. apply sigma_closed_unions => i.
      destruct (pickle_inv) as [(b&(n&m))|]; last apply sigma_empty_set.
      destruct b => //=; apply sigma_closed_pair_intersect;
                      first [ apply Hmeas1 | apply Hmeas2 ]; apply open_ray_borel_gt.
    }
    intros a; split.
    - intros Hlt.
      destruct (Rtotal_order 0 (f1 a)) as [Hgt0|[Heq|Hlt0]].
      * set (δ := Rmin ((f1 a + f2 a) - t) (f1 a / 2)).
        edestruct (archimed_rat_dense1 (δ/2) (f1 a - δ/2)) as (n&m&Hnm&?); rewrite /δ; auto; try nra.
        { apply Rmin_case_strong; intros; try nra. }
        { apply Rmin_case_strong; intros; try nra. }
        exists (pickle (true, (n, m))).
        rewrite pickleK_inv //=; split; rewrite /fun_inv.
        ** nra.
        ** rewrite /δ in Hnm. move: Hnm.
           apply Rmin_case_strong; nra.
      * set (δ := ((f1 a + f2 a) - t) / 2).
        edestruct (archimed_rat_dense2 (δ/2) (-δ/2)) as (n&m&Hnm&?); rewrite /δ; auto; try nra.
        exists (pickle (false, (n, m))).
        rewrite pickleK_inv //=; split; rewrite /fun_inv.
        ** nra.
        ** rewrite /δ in Hnm. move: Hnm.
           rewrite -?Heq //=. nra.
      * set (δ := ((f1 a + f2 a) - t) / 2).
        edestruct (archimed_rat_dense2 (δ/2) (f1 a - δ/2)) as (n&m&Hnm&?); rewrite /δ; auto; try nra.
        exists (pickle (false, (n, m))).
        rewrite pickleK_inv //=; split; rewrite /fun_inv.
        ** nra.
        ** rewrite /δ in Hnm. move: Hnm.
           rewrite -?Heq //=. nra.
    - intros (bnm&Hspec). destruct (pickle_inv) as [(b&(n&m))|].
      * destruct b; rewrite /fun_inv//= in Hspec; destruct Hspec as [H1 H2]; nra.
      * destruct Hspec.
  Qed.

  Lemma measurable_scal {A: Type} {F: measurable_space A} (f: A → R) (c: R):
    measurable f →
    measurable (λ x, c * f x).
  Proof.
    intros Hmeas.
    destruct (Rtotal_order 0 c) as [Hgt0|[Heq|Hlt0]].
    - eapply sigma_measurable_mono.
      { rewrite /le_sigma; reflexivity. }
      { rewrite /le_sigma/flip. apply borel_gen_open_ray_gt. }
      eapply sigma_measurable_generating_sets.
      intros ? (x&->).
      rewrite /fun_inv. eapply (sigma_proper _ _ (λ a, x /c < f a)).
      { intros z; split.
        * intros. eapply (Rmult_lt_reg_r (1/c)). move: Hgt0. clear.
          rewrite /Rinv. apply Rlt_mult_inv_pos; nra.
          field_simplify; nra.
        * intros. eapply (Rmult_lt_reg_r c); first nra.
          field_simplify; nra.
      }
      apply Hmeas, open_ray_borel_gt.
    - subst. intros U HU. rewrite /fun_inv.
      destruct (Classical_Prop.classic (U 0)).
      * eapply sigma_proper; last apply sigma_full.
        intros x; rewrite Rmult_0_l; split; auto.
      * eapply sigma_proper; last apply sigma_empty_set.
        intros x; rewrite Rmult_0_l; split; auto.
        inversion 1.
    - eapply sigma_measurable_mono.
      { rewrite /le_sigma; reflexivity. }
      { rewrite /le_sigma/flip. apply borel_gen_open_ray_gt. }
      eapply sigma_measurable_generating_sets.
      intros ? (x&->).
      rewrite /fun_inv. eapply (sigma_proper _ _ (λ a, x /c > f a)).
      { intros z; split.
        * intros Hineq%(Rmult_lt_gt_compat_neg_l c); last nra.
          field_simplify in Hineq; nra.
        * intros Hineq%(Rmult_lt_gt_compat_neg_l (1/c)); last first.
          { rewrite /Rdiv Rmult_1_l. apply Rinv_lt_0_compat. nra. }
          field_simplify in Hineq; nra.
      }
      apply: Hmeas. apply open_ray_borel_lt.
  Qed.

  Lemma measurable_square {A: Type} {F: measurable_space A} (f: A → R) :
    measurable f →
    measurable (λ x, f x * f x).
  Proof.
    intros Hmeas.
    eapply sigma_measurable_mono.
    { rewrite /le_sigma; reflexivity. }
    { rewrite /le_sigma/flip. apply borel_gen_closed_ray2. }
    eapply sigma_measurable_generating_sets.
    intros ? (t&->).
    rewrite /fun_inv//=.
    destruct (Rlt_dec t 0) as [Hlt|Hnlt].
    - eapply sigma_proper; last eapply sigma_empty_set.
      intros x; split.
      * intros Hle. assert (f x * f x >= 0).
        { apply Rle_ge. apply Rle_0_sqr. }
        nra.
      * inversion 1.
    - apply Rnot_lt_ge, Rge_le in Hnlt.
      assert (eq_prop (λ a, f a * f a <= t) (fun_inv f (λ a, - sqrt t <= a <= sqrt t))) as ->.
      { rewrite /fun_inv//=. intros a; split.
        * intros Hsqr. apply sqrt_le_1_alt in Hsqr.
          rewrite sqrt_Rsqr_abs in Hsqr.
          move: Hsqr. apply Rabs_case; nra.
        * intros Hrange.
          replace (f a * f a) with (Rsqr (f a)) by auto.
          rewrite (Rsqr_abs (f a)).
          apply sqrt_le_0; try nra.
          ** apply Rle_0_sqr.
          ** rewrite sqrt_Rsqr; last by auto.
             move: Hrange. apply Rabs_case; nra.
      }
      apply Hmeas, closed_interval_borel.
  Qed.

  Lemma measurable_opp {A: Type} {F: measurable_space A} (f: A → R) :
    measurable f →
    measurable (λ x, - f x).
  Proof.
    intros. eapply measurable_comp.
    * eauto.
    * apply continuous_borel_measurable. rewrite //=.
      intros x. apply: continuous_opp. apply: continuous_id.
  Qed.

  Lemma measurable_minus {A: Type} {F: measurable_space A} (f1 f2: A → R) :
    measurable f1 →
    measurable f2 →
    measurable (λ x, f1 x - f2 x).
  Proof.
    intros Hmeas1 Hmeas2. rewrite /Rminus.
    apply measurable_plus; auto.
    eapply measurable_comp; eauto.
    apply measurable_opp, measurable_id.
  Qed.

  Lemma measurable_mult {A: Type} {F: measurable_space A} (f1 f2: A → R) :
    measurable f1 →
    measurable f2 →
    measurable (λ x, f1 x * f2 x).
  Proof.
    intros Hmeas1 Hmeas2.
    assert (∀ x, f1 x * f2 x = /2 * ((f1 x + f2 x) * (f1 x + f2 x)) -
                               /2 * (f1 x * f1 x) - /2 * (f2 x * f2 x)) as Heq.
    { intros x. field. }
    setoid_rewrite Heq.
    repeat (apply measurable_plus || apply measurable_minus ||
            apply measurable_scal || apply measurable_opp ||
            apply measurable_square || auto).
  Qed.


  Ltac measurable := repeat (apply measurable_plus || apply measurable_minus ||
                             apply measurable_scal || apply measurable_opp ||
                             apply measurable_square || apply measurable_mult ||
                             apply measurable_const || auto).

  Lemma measurable_Rabs {A: Type} {F: measurable_space A} f1:
    measurable f1 →
    measurable (λ x, Rabs (f1 x)).
  Proof.
    intros Hmeas. eapply measurable_comp; eauto.
    apply continuous_borel_measurable => x.
    apply: continuous_abs.
  Qed.

  Lemma measurable_Rmax {A: Type} {F: measurable_space A} (f1 f2: A → R) :
    measurable f1 →
    measurable f2 →
    measurable (λ x, Rmax (f1 x) (f2 x)).
  Proof.
    intros. assert (Heq: ∀ x, Rmax (f1 x) (f2 x) = /2 * ((f1 x + f2 x) + Rabs (f1 x - f2 x))).
    { intros. apply Rmax_case_strong; apply Rabs_case; nra. }
    setoid_rewrite Heq.
    measurable.
    apply measurable_Rabs.
    apply measurable_minus; auto.
  Qed.

  Lemma measurable_Rmin {A: Type} {F: measurable_space A} (f1 f2: A → R) :
    measurable f1 →
    measurable f2 →
    measurable (λ x, Rmin (f1 x) (f2 x)).
  Proof.
    intros. assert (Heq: ∀ x, Rmin (f1 x) (f2 x) = /2 * ((f1 x + f2 x) - Rabs (f1 x - f2 x))).
    { intros. apply Rmin_case_strong; apply Rabs_case; nra. }
    setoid_rewrite Heq.
    measurable.
    apply measurable_Rabs.
    apply measurable_minus; auto.
  Qed.

  Lemma measurable_real:
    measurable real.
  Proof.
    eapply sigma_measurable_mono.
    { rewrite /le_sigma; reflexivity. }
    { rewrite /le_sigma/flip. apply borel_gen_closed_ray2. }
    eapply sigma_measurable_generating_sets.
    intros ? (t&->).
    destruct (Rlt_dec t 0).
    - eapply (sigma_proper _ _ (Rbar_le^~ t ∩ compl ({[m_infty]}))).
      * intros x; split.
        ** intros (Hle&Hm); destruct x => //=.
           exfalso. apply Hm. done.
        ** destruct x; rewrite /fun_inv//=; nra.
      * apply sigma_closed_pair_intersect.
        ** eapply minimal_sigma_ub. exists t => //=.
        ** apply sigma_closed_complements, Rbar_sigma_m_infty.
    - eapply (sigma_proper _ _ (Rbar_le^~ t ∪ ({[m_infty]} ∪ {[p_infty]}))).
      * intros x; split.
        ** intros [Hle|[Hm|Hp]]; destruct x => //=; rewrite /fun_inv/real; nra.
        ** rewrite /fun_inv/real//=.
           destruct x => //=; try firstorder.
      * apply sigma_closed_pair_union.
        ** eapply minimal_sigma_ub. exists t => //=.
        ** apply sigma_closed_pair_union.
           *** apply Rbar_sigma_m_infty.
           *** apply Rbar_sigma_p_infty.
  Qed.

  Lemma measurable_Finite:
    measurable Finite.
  Proof.
    intros.
    eapply sigma_measurable_generating_sets.
    intros ? (t&->).
    destruct t as [r | | ].
    - assert (eq_prop (fun_inv Finite (Rbar_le^~ r))
                      (Rle^~ r)) as ->.
      { intros x. split => //=. }
      apply closed_ray_borel_le.
    - eapply sigma_proper; last eapply sigma_full.
      split; auto.
    - eapply sigma_proper; last eapply sigma_empty_set.
      split; auto.
  Qed.

  Lemma Rbar_sigma_real_pt r:
    Rbar_sigma {[Finite r]}.
  Proof.
    assert (eq_prop {[Finite r]}
                    (fun_inv real {[r]} ∩ compl {[p_infty]} ∩ compl {[m_infty]})) as ->.
    { split.
      * inversion 1; subst. rewrite /compl/fun_inv//=.
      * rewrite /compl/fun_inv//=. intros ((Heq&?)&?); destruct x; try firstorder.
        ** inversion Heq as [Heq'].
           rewrite //= in Heq'. subst. done.
    }
    apply sigma_closed_pair_intersect; first apply sigma_closed_pair_intersect.
    * apply measurable_real. apply borel_closed. apply closed_eq.
    * apply sigma_closed_complements, Rbar_sigma_p_infty.
    * apply sigma_closed_complements, Rbar_sigma_m_infty.
  Qed.

  Lemma Rbar_sigma_pt r:
    Rbar_sigma {[r]}.
  Proof.
    destruct r; auto using Rbar_sigma_real_pt, Rbar_sigma_p_infty, Rbar_sigma_m_infty.
  Qed.

  Lemma Rbar_sigma_gen_ge_ray:
    le_prop (minimal_sigma (λ U, ∃ x, U = (λ z, Rbar_le x z))) Rbar_sigma.
  Proof.
    apply minimal_sigma_lub.
    intros ? (x&->).
    assert (eq_prop [eta Rbar_le x] (compl (λ z, Rbar_le z x) ∪ {[x]})) as ->.
    { intros z; split.
      * intros [Hlt|Heq]%Rbar_le_lt_or_eq_dec.
        ** left. by apply Rbar_lt_not_le.
        ** right; subst; done.
      * intros [Hnle|Heq].
        ** apply Rbar_not_le_lt in Hnle. by apply Rbar_lt_le.
        ** inversion Heq; subst; apply Rbar_le_refl.
    }
    apply sigma_closed_pair_union.
    - apply sigma_closed_complements.
      apply minimal_sigma_ub; eexists. reflexivity.
    - apply Rbar_sigma_pt.
  Qed.


  Lemma measurable_Rbar_opp {A: Type} {F: measurable_space A} (f: A → Rbar) :
    measurable f →
    measurable (λ x, Rbar_opp (f x)).
  Proof.
    intros Hmeas.
    apply sigma_measurable_generating_sets.
    intros ? (t&->).
    assert (fun_inv (λ x, Rbar_opp (f x)) (Rbar_le^~t) ≡
                    fun_inv f (Rbar_le (Rbar_opp t))) as ->.
    { rewrite /fun_inv//= => x. rewrite -{1}(Rbar_opp_involutive t).
      apply Rbar_opp_le. }
    apply Hmeas. apply Rbar_sigma_gen_ge_ray.
    apply minimal_sigma_ub. eauto.
  Qed.

  Lemma Sup_seq_minor_Rbar_le (u : nat → Rbar) (M : Rbar) (n : nat):
    Rbar_le M (u n) → Rbar_le M (Sup_seq u).
  Proof.
    intros Hle.
    rewrite Rbar_sup_eq_lub. rewrite /Lub.Rbar_lub.
    destruct (Lub.Rbar_ex_lub) as (?&r).
    rewrite /=. eapply Rbar_le_trans; eauto. apply r.  eauto.
  Qed.

  Lemma measurable_Sup {A: Type} {F: measurable_space A} (fn : nat → A → Rbar):
    (∀ n, measurable (fn n)) →
    measurable (λ x, Sup_seq (λ n, fn n x)).
  Proof.
    intros Hmeas.
    eapply sigma_measurable_generating_sets.
    intros ? (t&->).
    assert (eq_prop (λ x, Rbar_le (Sup_seq (λ n, fn n x)) t)
                    (intersectF (λ n, fun_inv (fn n) (λ x, Rbar_le x t)))) as ->.
    { split.
      - intros Hsup n. rewrite /fun_inv.
        eapply Rbar_le_trans; eauto.
        eapply Sup_seq_minor_Rbar_le; eauto.
        apply Rbar_le_refl.
      - intros Hle.
        rewrite Rbar_sup_eq_lub. rewrite /Lub.Rbar_lub.
        destruct (Lub.Rbar_ex_lub) as (?&(Hub&Hlub)).
        apply Hlub => //=.
        intros r (?&->); eapply Hle.
    }
    apply sigma_closed_intersections. intros. apply Hmeas.
    apply minimal_sigma_ub. eauto.
  Qed.

  Lemma measurable_Inf {A: Type} {F: measurable_space A} (fn : nat → A → Rbar):
    (∀ n, measurable (fn n)) →
    measurable (λ x, Inf_seq (λ n, fn n x)).
  Proof.
    intros.
    setoid_rewrite Inf_opp_sup.
    apply measurable_Rbar_opp.
    apply measurable_Sup.
    intros n. apply measurable_Rbar_opp. done.
  Qed.

  Lemma measurable_LimSup {A: Type} {F: measurable_space A} (fn : nat → A → R):
    (∀ n, measurable (fn n)) →
    measurable (λ x, LimSup_seq (λ n, fn n x)).
  Proof.
    intros Hmeas.
    setoid_rewrite LimSup_InfSup_seq.
    apply measurable_Inf => n.
    apply measurable_Sup => m.
    eapply measurable_comp; last apply measurable_Finite.
    eauto.
  Qed.

  Lemma measurable_LimInf {A: Type} {F: measurable_space A} (fn : nat → A → R):
    (∀ n, measurable (fn n)) →
    measurable (λ x, LimInf_seq (λ n, fn n x)).
  Proof.
    intros Hmeas.
    setoid_rewrite LimInf_SupInf_seq.
    apply measurable_Sup => m.
    apply measurable_Inf => n.
    eapply measurable_comp; last apply measurable_Finite.
    eauto.
  Qed.

  Lemma measurable_Sup_seq {A: Type} {F: measurable_space A} (fn : nat → A → R):
    (∀ n, measurable (fn n)) →
    measurable (λ x, Sup_seq (λ n, fn n x) : R).
  Proof.
    intros Hmeas. eapply measurable_comp. apply measurable_Sup.
    { intros n. eapply measurable_comp; last apply measurable_Finite.
      eauto. }
    apply measurable_real.
  Qed.

  Lemma measurable_Inf_seq {A: Type} {F: measurable_space A} (fn : nat → A → R):
    (∀ n, measurable (fn n)) →
    measurable (λ x, Inf_seq (λ n, fn n x) : R).
  Proof.
    intros Hmeas. eapply measurable_comp. apply measurable_Inf.
    { intros n. eapply measurable_comp; last apply measurable_Finite.
      eauto. }
    apply measurable_real.
  Qed.

  Lemma measurable_Rbar_div_pos y:
    measurable (Rbar_div_pos^~ y).
  Proof.
    apply sigma_measurable_generating_sets.
    intros ? (t&->).
    destruct t as [r | | ].
    - assert (fun_inv (Rbar_div_pos^~y) (Rbar_le^~r) ≡
                      Rbar_le^~(r * y)) as ->.
      { rewrite /fun_inv//=; intros [ r' | |] => //=; apply Rle_div_l; destruct y; done. }
      apply minimal_sigma_ub; eauto.
    - eapply sigma_proper; last apply sigma_full.
      intros [ | |] => //=.
    - eapply sigma_proper; last apply Rbar_sigma_m_infty.
      intros [ | |] => //=.
  Qed.

  Lemma measurable_Rbar_plus {A: Type} {F: measurable_space A} (f1 f2: A → Rbar) :
    measurable f1 →
    measurable f2 →
    measurable (λ x, Rbar_plus (f1 x) (f2 x)).
  Proof.
    intros Hmeas1 Hmeas2.
    apply sigma_measurable_generating_sets.
    intros ? (t&->).
    destruct t as [r | | ].
    -
      destruct (Rle_dec 0 r) as [Hle0|Hnle0].
      {
        assert (fun_inv (λ x, Rbar_plus (f1 x) (f2 x)) (Rbar_le^~ r) ≡
                        (fun_inv (λ x, Rplus (f1 x) (f2 x)) (Rle^~ r)
                                 ∩ compl (fun_inv f1 ({[p_infty]} ∪ {[m_infty]}))
                                 ∩ compl (fun_inv f2 ({[p_infty]} ∪ {[m_infty]}))) ∪
                        fun_inv f1 {[m_infty]} ∪ fun_inv f2 {[m_infty]}) as ->.
        { intros a; split; rewrite /fun_inv.
          - rewrite /base.union/union_Union/union/intersection/intersect_Intersection/intersect/compl.
            destruct (f1 a), (f2 a); rewrite //=;
                                             try (left; right; firstorder; done);
            try (right; firstorder; done).
            intros Hle. do 2 left. split_and!; auto; firstorder.
          - rewrite /base.union/union_Union/union/intersection/intersect_Intersection/intersect/compl.
            intros [[((Hplus&Hnot1)&Hnot2)|Hinf1]|Hinf2].
            * destruct (f1 a), (f2 a) => //=;
                                           try nra;
                                           try (exfalso; apply Hnot1; firstorder; done);
                                           try (exfalso; apply Hnot2; firstorder; done).
            * inversion Hinf1 as [Heq]. rewrite Heq => //=.
              destruct (f2 a) => //=.
            * inversion Hinf2 as [Heq]. rewrite Heq => //=.
              destruct (f1 a) => //=.
        }
        apply sigma_closed_pair_union; eauto using Rbar_sigma_m_infty.
        apply sigma_closed_pair_union; eauto using Rbar_sigma_m_infty.
        repeat apply sigma_closed_pair_intersect.
        * apply measurable_plus; try eapply measurable_comp; eauto using measurable_real.
          apply closed_ray_borel_le.
        * apply sigma_closed_complements; eapply Hmeas1.
          apply sigma_closed_pair_union; eauto using Rbar_sigma_m_infty, Rbar_sigma_p_infty.
        * apply sigma_closed_complements; eapply Hmeas2.
          apply sigma_closed_pair_union; eauto using Rbar_sigma_m_infty, Rbar_sigma_p_infty.
      }
      {
        assert (fun_inv (λ x, Rbar_plus (f1 x) (f2 x)) (Rbar_le^~ r) ≡
                        (fun_inv (λ x, Rplus (f1 x) (f2 x)) (Rle^~ r)
                                 ∩ compl (fun_inv f1 ({[p_infty]} ∪ {[m_infty]}))
                                 ∩ compl (fun_inv f2 ({[p_infty]} ∪ {[m_infty]}))) ∪
                        (compl (fun_inv f2 {[p_infty]}) ∩ fun_inv f1 {[m_infty]}) ∪
                        (compl (fun_inv f1 {[p_infty]}) ∩ fun_inv f2 {[m_infty]})) as ->.
        { intros a; split; rewrite /fun_inv.
          - rewrite /base.union/union_Union/union/intersection/intersect_Intersection/intersect/compl.
            destruct (f1 a), (f2 a); rewrite //=;
                                             try (left; right; firstorder; done);
            try (right; firstorder; done).
            intros Hle. do 2 left. split_and!; auto; firstorder.
          - rewrite /base.union/union_Union/union/intersection/intersect_Intersection/intersect/compl.
            intros [[((Hplus&Hnot1)&Hnot2)|(Hn1&Hinf1)]|(Hn2&Hinf2)].
            * destruct (f1 a), (f2 a) => //=;
                                           try nra;
                                           try (exfalso; apply Hnot1; firstorder; done);
                                           try (exfalso; apply Hnot2; firstorder; done).
            * inversion Hinf1 as [Heq]. rewrite Heq => //=.
              destruct (f2 a) => //=. firstorder.
            * inversion Hinf2 as [Heq]. rewrite Heq => //=.
              destruct (f1 a) => //=. firstorder.
        }
        apply sigma_closed_pair_union; eauto using Rbar_sigma_m_infty;
        first apply sigma_closed_pair_union; eauto using Rbar_sigma_m_infty;
        first repeat apply sigma_closed_pair_intersect.
        * apply measurable_plus; try eapply measurable_comp; eauto using measurable_comp, measurable_real.
          apply closed_ray_borel_le.
        * apply sigma_closed_complements; eapply Hmeas1.
          apply sigma_closed_pair_union; eauto using Rbar_sigma_pt.
        * apply sigma_closed_complements; eapply Hmeas2.
          apply sigma_closed_pair_union; eauto using Rbar_sigma_pt.
        * apply sigma_closed_pair_intersect.
          ** apply sigma_closed_complements.
             apply Hmeas2; eauto using Rbar_sigma_pt.
          ** apply Hmeas1; eauto using Rbar_sigma_pt.
        * apply sigma_closed_pair_intersect.
          ** apply sigma_closed_complements.
             apply Hmeas1; eauto using Rbar_sigma_pt.
          ** apply Hmeas2; eauto using Rbar_sigma_pt.
      }
    - eapply sigma_proper; last eapply sigma_full.
      intros x; split; auto. rewrite /fun_inv//=. by destruct (Rbar_plus).
    - assert (fun_inv (λ x, Rbar_plus (f1 x) (f2 x)) (Rbar_le^~ m_infty) ≡
                      (fun_inv f1 (compl {[p_infty]}) ∩
                       fun_inv f2 {[m_infty]}) ∪
                      (fun_inv f2 (compl {[p_infty]}) ∩
                       fun_inv f1 {[m_infty]})) as ->.
      { intros a; split; rewrite /fun_inv.
          - rewrite /base.union/union_Union/union/intersection/intersect_Intersection/intersect/compl.
            destruct (f1 a), (f2 a); firstorder; done.
          - rewrite /base.union/union_Union/union/intersection/intersect_Intersection/intersect/compl.
            destruct (f1 a), (f2 a); firstorder.
      }
      apply sigma_closed_pair_union; apply sigma_closed_pair_intersect.
      * eapply Hmeas1. apply sigma_closed_complements; eauto using Rbar_sigma_pt.
      * eapply Hmeas2. eauto using Rbar_sigma_pt.
      * eapply Hmeas2. apply sigma_closed_complements; eauto using Rbar_sigma_pt.
      * eapply Hmeas1. eauto using Rbar_sigma_pt.
  Qed.

  Lemma measurable_Lim {A: Type} {F: measurable_space A} (fn : nat → A → R):
    (∀ n, measurable (fn n)) →
    measurable (λ x, Lim_seq (λ n, fn n x)).
  Proof.
    intros Hmeas. rewrite /Lim_seq//=.
    eapply (measurable_comp _ (Rbar_div_pos^~{| pos := 2 ; cond_pos := Rlt_R0_R2|}));
      eauto using measurable_Rbar_div_pos.
    apply measurable_Rbar_plus.
    * apply measurable_LimSup. done.
    * apply measurable_LimInf. done.
  Qed.

  Lemma measurable_Lim' {A: Type} {F: measurable_space A} (fn : nat → A → R):
    (∀ n, measurable (fn n)) →
    measurable (λ x, real (Lim_seq (λ n, fn n x))).
  Proof.
    intros. eapply measurable_comp; eauto using measurable_real.
    apply measurable_Lim. done.
  Qed.

  Lemma measurable_fun_eq_0 {A: Type} {F: measurable_space A} f:
    measurable f →
    is_measurable (λ x, f x = 0).
  Proof.
    intros Hmeas. eapply (Hmeas (λ x, x = 0)).
    apply borel_closed, closed_eq.
  Qed.

  Lemma measurable_fun_eq_0_Rbar {A: Type} {F: measurable_space A} (f: A → Rbar):
    measurable f →
    is_measurable (λ x, f x = 0).
  Proof.
    intros Hmeas. eapply (Hmeas (λ x, x = 0)).
    apply Rbar_sigma_pt.
  Qed.

  Lemma measurable_fun_ge {A: Type} {F: measurable_space A} f k:
    measurable f →
    is_measurable (λ x, k <= f x).
  Proof.
    intros Hmeas. eapply (Hmeas (λ x, k <= x)).
    apply closed_ray_borel_ge.
  Qed.

  Lemma measurable_fun_le_const {A: Type} {F: measurable_space A} f k:
    measurable f →
    is_measurable (λ x, f x <= k).
  Proof.
    intros Hmeas. eapply (Hmeas (λ x, x <= k)).
    apply closed_ray_borel_le.
  Qed.

  Lemma measurable_fun_lt_p_infty {A: Type} {F: measurable_space A} f:
    measurable f →
    is_measurable (λ x, Rbar_lt (f x) p_infty).
  Proof.
    intros Hmeas.
    rewrite /is_measurable.
    assert ((λ x, Rbar_lt (f x) p_infty)  ≡ compl (fun_inv f {[p_infty]})) as ->.
    { intros x. rewrite /fun_inv/compl//=. split.
      - intros Hlt Heq. inversion Heq as [Heq']. rewrite Heq' in Hlt.
        rewrite //= in Hlt.
      - intros Heq. destruct (f x) => //=. apply Heq. done.
    }
    apply sigma_closed_complements.
    eapply Hmeas.
    apply Rbar_sigma_pt.
  Qed.

  Lemma measurable_fun_eq_inv {A: Type} {F: measurable_space A} (f g: A → R):
    measurable f →
    measurable g →
    is_measurable (λ x, f x = g x).
  Proof.
    intros Hmeas1 Hmeas2.
    apply (sigma_proper _ _ (λ x, f x - g x = 0)).
    { intros x; split; nra. }
    apply measurable_fun_eq_0. measurable.
  Qed.

  Lemma measurable_fun_le_inv {A: Type} {F: measurable_space A} f g:
    measurable f →
    measurable g →
    is_measurable (λ x, f x <= g x).
  Proof.
    intros Hmeas1 Hmeas2.
    apply (sigma_proper _ _ (λ x, f x - g x <= 0)).
    { intros x; split; nra. }
    apply measurable_fun_le_const. measurable.
  Qed.

  Lemma measurable_fun_eq_inv_Rbar {A: Type} {F: measurable_space A} (f g: A → Rbar):
    measurable f →
    measurable g →
    is_measurable (λ x, f x = g x).
  Proof.
    intros Hmeas1 Hmeas2.
    apply (sigma_proper _ _ (λ x, Rbar_minus (f x) (g x) = 0)).
    { intros x; split.
      - destruct (f x), (g x) => //=.
        inversion 1; subst; f_equal; nra.
      - destruct (f x), (g x) => //=.
        intros Heq. inversion Heq; subst. f_equal. nra.
    }
    apply measurable_fun_eq_0_Rbar. rewrite /Rbar_minus.
    apply measurable_Rbar_plus, measurable_Rbar_opp; auto.
  Qed.

  Lemma measure_ex_lim_seq {A: Type} {F: measurable_space A} (fn : nat → A → R):
    (∀ n, measurable (fn n)) →
    is_measurable (λ x, ex_lim_seq (λ n, fn n x)).
  Proof.
    intros Hmeas.
    eapply sigma_proper.
    { intros x. apply ex_lim_LimSup_LimInf_seq. }
    apply measurable_fun_eq_inv_Rbar; auto using measurable_LimSup, measurable_LimInf.
  Qed.

  Lemma measure_ex_finite_lim_seq {A: Type} {F: measurable_space A} (fn : nat → A → R):
    (∀ n, measurable (fn n)) →
    is_measurable (λ x, ex_finite_lim_seq (λ n, fn n x)).
  Proof.
    intros Hmeas.
    eapply (sigma_proper _ _ ((λ x, ex_lim_seq (λ n, fn n x))
                                ∩ (fun_inv (λ x, Lim_seq (λ n, fn n x)) (compl {[p_infty]}))
                                ∩ (fun_inv (λ x, Lim_seq (λ n, fn n x)) (compl {[m_infty]})))).
    { intros x. rewrite /fun_inv. split.
      - intros ((Hex&Hlim1)&Hlim2).
        destruct Hex as (v&His).
        destruct v as [r | |].
        * exists r; eauto.
        * rewrite (is_lim_seq_unique _ _ His) //= in Hlim1. exfalso; apply Hlim1; done.
        * rewrite (is_lim_seq_unique _ _ His) //= in Hlim2. exfalso; apply Hlim2; done.
      - intros (v&His).
        split; first split.
        * eexists; eauto.
        * rewrite //= (is_lim_seq_unique _ _ His) //=.
        * rewrite //= (is_lim_seq_unique _ _ His) //=.
    }
    apply sigma_closed_pair_intersect; first apply sigma_closed_pair_intersect.
    - apply measure_ex_lim_seq; auto.
    - apply measurable_Lim; eauto. apply sigma_closed_complements, Rbar_sigma_pt.
    - apply measurable_Lim; eauto. apply sigma_closed_complements, Rbar_sigma_pt.
  Qed.

  Lemma measure_is_lim_seq {A: Type} {F: measurable_space A} (fn : nat → A → R) (f: A → Rbar):
    (∀ n, measurable (fn n)) →
    measurable f →
    is_measurable (λ x, is_lim_seq (λ n, fn n x) (f x)).
  Proof.
    intros.
    assert (Hequiv: (λ x, is_lim_seq (λ n, fn n x) (f x))
                      ≡ (λ x, ex_lim_seq (λ n, fn n x)) ∩ (λ x, Lim_seq (λ n, fn n x) = f x)).
    {
      intros x. split.
      - intros His; split; first by (eexists; eauto).
        by apply is_lim_seq_unique.
      - intros (Hex&Heq). rewrite -Heq. apply Lim_seq_correct; eauto.
    }
    rewrite /is_measurable.
    rewrite Hequiv. apply sigma_closed_pair_intersect.
    - apply measure_ex_lim_seq; eauto.
    - apply measurable_fun_eq_inv_Rbar; eauto using measurable_Lim.
  Qed.


End borel_R.


Ltac measurable := repeat (apply measurable_plus || apply measurable_minus ||
                           apply measurable_scal || apply measurable_opp ||
                           apply measurable_square || apply measurable_mult ||
                           apply measurable_const || apply measurable_real ||
                           apply measurable_Rabs ||
                           apply measurable_Rmax || apply measurable_Rmin ||
                           apply measure_is_lim_seq || apply measure_ex_lim_seq ||
                           apply measure_ex_finite_lim_seq ||
                           apply measurable_fun_le_inv ||
                           apply measurable_fun_eq_inv ||
                           auto).
