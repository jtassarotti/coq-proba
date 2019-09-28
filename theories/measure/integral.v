Require Import Reals Psatz Omega Fourier.
From stdpp Require Import tactics list.
From discprob.basic Require Import seq_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.measure Require Export measures borel convergence.
Require Import ClassicalEpsilon SetoidList.

Lemma R_singleton_closed (x: R): closed {[x]}.
Proof.
  rewrite /closed => y Hlocal. destruct (Req_dec x y); subst; first done.
  exfalso. apply Hlocal.
  rewrite /locally. unshelve (eexists).
  exists (Rabs (y - x)).
  { abstract (apply Rabs_pos_lt; nra). }
  intros y'. rewrite /ball//=/AbsRing_ball//=/abs//=/minus/plus/opp//=.
  rewrite /base.singleton/singleton_Singleton/singleton//=.
  repeat apply Rabs_case; nra.
Qed.
Hint Resolve R_singleton_closed.

Section integral.

  Context {A: Type}.
  Context {F: sigma_algebra A}.
  Context (μ: measure F).

  Record partition :=
    { partition_list :> list (A → Prop);
      partition_union : le_prop (λ _, True) (unionL partition_list);
      partition_disjoint : ## (partition_list);
      partition_measurable: ∀ U, In U partition_list → F U
    }.

  Definition le_partition (P1 P2: partition) :=
    ∀ U1, In U1 P1 → ∃ U2, In U2 P2 ∧ U1 ⊆ U2.
  Global Instance le_partition_Transitive : Transitive le_partition.
  Proof.
    rewrite /le_partition => P1 P2 P3 Hle1 Hle2 U Hin.
    edestruct Hle1 as (?&?&?); eauto.
    edestruct Hle2 as (?&?&?); eauto.
    eexists; split; eauto.
    etransitivity; eauto.
  Qed.
  Global Instance le_partition_Reflexive : Reflexive (le_partition).
  Proof. rewrite /le_partition. intros ???; eexists; split; eauto. Qed.

  Lemma union_list_inv (l: list (A → Prop)) (a: A):
    (⋃ l) a → ∃ U, In U l ∧ U a.
  Proof.
    induction l as [| U l] => //=.
    destruct 1 as [Hinhd|Hintl].
    * exists U. intuition. 
    * edestruct IHl as (?&?&?); eauto.
  Qed.

  Lemma union_list_intro (l: list (A → Prop)) (a: A) U:
    In U l → U a → (union_list l) a.
  Proof.
    intros Hin HU.
    induction l as [| U' l] => //=.
    inversion Hin; subst.
    * by left. 
    * right. eauto.
  Qed.

  Lemma disjoint_list_app (l1 l2: list (A → Prop)):
    ## l1 → ## l2 →
    (∀ U1 U2, In U1 l1 → In U2 l2 → U1 ## U2) →
    ## (l1 ++ l2).
  Proof.
    intros HNoDup1. revert l2. induction HNoDup1 as [| U0 l Hdisj1 Hdisj2].
    - rewrite //=.
    - intros l2 HNoDup2.
      intros Hinter. rewrite //=. constructor.
      * intros a (Hin1&(U'&Hin&HU')%union_list_inv).
        apply in_app_or in Hin as [Hin1'|Hin2'].
        ** eapply Hdisj1. split; eauto. eapply union_list_intro; eauto. 
        ** eapply (Hinter U0 U'); eauto. by left.
      * eapply IHHNoDup1; eauto. intros. eapply Hinter; auto.
          by right.
  Qed.

  Lemma disjoint_list_inv (U: A → Prop) l:
    ## (U :: l) → ∀ U', In U' l → U ## U'.
  Proof.
    inversion 1 as [|? ? Hdisj HdisjL]; subst. intros U' Hin a (?&?).
    eapply Hdisj; split; eauto. eapply union_list_intro; eauto.
  Qed.

  Lemma disjoint_list_inv' a (U: A → Prop) l:
    ## (U :: l) → ∀ U', In U' l → U a → U' a → False.
  Proof.
    intros. eapply disjoint_list_inv; eauto.
  Qed.

  Lemma disjoint_list_prod (P1 P2 : partition):
    ## (map (λ UU : (A → Prop) * (A → Prop), UU.1 ∩ UU.2) (list_prod P1 P2)).
  Proof.
    - revert P2. destruct P1 as [l ? HNoDup Hmeas]. rewrite //=. clear -HNoDup.
      induction HNoDup as [| ? ? Hdisj ?].
      * rewrite //=. econstructor.
      * rewrite //= => P2. rewrite map_app.
        apply disjoint_list_app.
        ** destruct P2 as [l2 ? HNoDup2 Hmeas2] => //=. clear -HNoDup2.
           induction l2 as [|U' l2] => //=.
           constructor.
           *** intros a (Hin1&Hin2).
               apply union_list_inv in Hin2 as (U''&Hin&?).
               apply in_map_iff in Hin as ((U''_a&U''b)&Heq&Hin).
               apply in_map_iff in Hin as (?&Heq'&?) => //=; subst.
               inversion Heq'; subst => //=.
               rewrite //= in H. eapply (disjoint_list_inv' a); first eapply HNoDup2; eauto;
               firstorder.
           *** eapply IHl2; eauto. inversion HNoDup2; eauto.
        ** eapply IHHNoDup. 
        ** destruct P2 as [l2 ? HNoDup2 Hmeas2] => //=.
           intros U1 U2 Hin1 Hin2.
           apply in_map_iff in Hin1 as (?&Heq&Hin1).
           apply in_map_iff in Hin1 as (U1'&Heq'&Hin1'). subst => //=.

           apply in_map_iff in Hin2 as ((U2a&U2b)&Heq2&Hin2).
           apply in_prod_iff in Hin2 as (?&?).
           subst => //=. 
           intros a (?&?). eapply (Hdisj a); split; eauto.
           *** firstorder.
           *** eapply union_list_intro; eauto. firstorder.
  Qed.

  Lemma common_refinement (P1 P2: partition) :
    ∃ P : partition, le_partition P P1 ∧ le_partition P P2.
  Proof.
    unshelve (eexists).
    refine {| partition_list := map (λ UU, (fst UU) ∩ (snd UU)) (list_prod P1 P2) |}.
    - intros x _.
      edestruct (partition_union P1 x) as (U1&?&?); first by done.
      edestruct (partition_union P2 x) as (U2&?&?); first by done.
      exists (U1 ∩ U2); split; last by intuition.
      apply in_map_iff.
      exists (U1, U2); split; auto.
      apply in_prod_iff; intuition.
    - apply disjoint_list_prod. 
    - intros U ((U1&U2)&Heq&Hin)%in_map_iff; subst.
      apply in_prod_iff in Hin as (?&?).
      rewrite //=. apply sigma_closed_pair_intersect; eapply partition_measurable; eauto.
    - rewrite /le_partition => //=; split.
      * intros U ((U1&U2)&Heq&Hin)%in_map_iff.
        subst => //=.
        apply in_prod_iff in Hin as (?&?).
        exists U1. split; auto. clear. firstorder.
      * intros U ((U1&U2)&Heq&Hin)%in_map_iff.
        subst => //=.
        apply in_prod_iff in Hin as (?&?).
        exists U2. split; auto. clear. firstorder.
  Qed.

  Record weighted_partition :=
    { wpt_list :> list (R * (A → Prop));
      wpt_part : partition;
      wpt_partition_spec1: map snd wpt_list = wpt_part
    }.

  Definition wpt_fun (wpt: weighted_partition) : A → R :=
    λ x, 
    \big[Rplus/0]_(aU <- wpt)
     (if excluded_middle_informative (aU.2 x) then
        (aU.1)
      else
        0).

  Definition wpt_integral (wpt: weighted_partition) : R :=
    \big[Rplus/0]_(aU <- wpt) (aU.1 * μ (aU.2)).

  Definition wpt_refinement (wpt: weighted_partition) (P : partition) :
    le_partition P (wpt_part wpt) → weighted_partition.
  Proof.
    rewrite /le_partition => Hle. 
    unshelve (refine {| wpt_part := P |}).
      * destruct P as [l ? ? ?]. rewrite //= in Hle. clear -Hle.
        induction l as [|U l].
        ** exact [].
        ** apply cons.
           *** specialize (Hle U).
               apply (constructive_indefinite_description) in Hle; last by left.
               destruct Hle as (U'&Hin&Hsub).
               rewrite -(wpt_partition_spec1) in Hin.
               apply in_map_iff in Hin.
               apply (constructive_indefinite_description) in Hin as ((x&?)&?&?).
               destruct (excluded_middle_informative (∃ x, U x)) as [Hex|Hnon].
               { exact (x, U). }
               { exact (0, U). }
           *** eapply IHl; intros; eauto.
               edestruct Hle as (?&?&?); first by (right; eauto).
               eexists; split; eauto.
      * rewrite //=. destruct P as [l H1 H2 H3].
        rewrite //=. revert Hle. rewrite //=.  clear H1 H2 H3 => Hle.
        induction l => //=.
        destruct (constructive_indefinite_description) as (?&?&?) => //=.
        f_equal.
        ** clear IHl. destruct (wpt_partition_spec1 wpt) => //=.
           destruct (constructive_indefinite_description) as ((?&?)&?&?) => //=.
           destruct excluded_middle_informative; eauto.
        ** eapply IHl.
  Defined.

  Lemma wpt_fun_eq1 wpt (x : A) (U: A → Prop):
    U x → In U (wpt_part wpt) → In ((wpt_fun wpt) x, U) wpt.
  Proof.
    intros HU. destruct wpt as [l p Hspec] => //=.
    rewrite /wpt_fun => //= Hin.
    assert (Hdisj: ## (map snd l)).
    { rewrite Hspec. apply partition_disjoint. }
    rewrite -Hspec in Hin.
    clear p Hspec.
    induction l as [|(r, U') l] => //=.
    * rewrite //=. inversion Hin; subst.
      ** left. f_equal.
         rewrite big_cons.
         destruct (excluded_middle_informative) => //=.
         rewrite big1_In; first nra.
         intros (r'&U'') _ Hin'. rewrite //=. destruct excluded_middle_informative => //=.
         exfalso.
         rewrite map_cons in Hdisj.
         eapply (disjoint_list_inv' x); eauto.
         eapply in_map_iff;  eexists; split; eauto. rewrite //=.
      ** right. rewrite big_cons.
         destruct excluded_middle_informative => //=.
         { exfalso. eapply (disjoint_list_inv' x); eauto. }
         rewrite Rplus_0_l. eapply IHl; eauto.
         rewrite //= in Hdisj.
         apply disjoint_list_cons in Hdisj. intuition.
  Qed.

  Lemma NoDup_inhabited_disjoint (U: A → Prop) l x :
    ## (U :: l) → U x → ¬ In U l.
  Proof.
    revert U x. induction l => //=.
    * intros. done.
    * intros U x Hdisj HU.
      intros Hin.
      eapply (disjoint_list_inv' x); eauto.
  Qed.

  Lemma wpt_fun_eq2 (wpt: weighted_partition) U1 x r1:
    In (r1, U1) wpt → U1 x → wpt_fun wpt x = r1.
  Proof.
    destruct wpt as [l p Heq] => //=.
    assert (Hdisj: ## (map snd l)).
    { rewrite Heq. apply partition_disjoint. }
    rewrite /wpt_fun //=.
    clear p Heq. 
    induction l as [| rU' l].
    * inversion 1.
    * inversion 1 as [Hhd1|Htl1]; subst.
      ** intros HU.
         rewrite big_cons. destruct excluded_middle_informative => //=.
         rewrite big1_In; first by field.
         intros i _ Hin. destruct excluded_middle_informative => //=.
         exfalso. rewrite //= in Hdisj.
         eapply (disjoint_list_inv' x U1); first eassumption.
         *** eapply in_map_iff; eexists; split; eauto; done.
         *** eauto.
         *** eauto.
      ** intros HU. rewrite big_cons. destruct excluded_middle_informative => //=.
         exfalso. rewrite //= in Hdisj.
         eapply (disjoint_list_inv' x (snd rU')); first eassumption.
         *** eapply in_map_iff; eexists; split; eauto; done.
         *** eauto.
         *** eauto.
         *** rewrite Rplus_0_l. eapply IHl; eauto.
             inversion Hdisj; eauto.
  Qed.

  Lemma wpt_inhabited_fst_eq (wpt: weighted_partition) U1 U2 x r1 r2:
    In (r1, U1) wpt → In (r2, U2) wpt → U1 x → U2 x → r1 = r2.
  Proof.
    intros Hin1 Hin2 HU1 HU2.
    transitivity (wpt_fun wpt x); first symmetry; eapply wpt_fun_eq2; eauto.
  Qed.

  Lemma wpt_inhabited_fst_eq' (wpt: weighted_partition) U x r1 r2:
    In (r1, U) wpt → In (r2, U) wpt → U x → r1 = r2.
  Proof.
    intros. eapply wpt_inhabited_fst_eq; eauto.
  Qed.

  Lemma wpt_fun_eq3 (wpt: weighted_partition) U1 x y r1:
    In (r1, U1) wpt → U1 x → U1 y → wpt_fun wpt x = wpt_fun wpt y.
  Proof.
    intros. eapply (wpt_inhabited_fst_eq' wpt); eauto.
    - assert (wpt_fun wpt x = r1).
      { by eapply wpt_fun_eq2; eauto. }
      subst. auto.
    - assert (wpt_fun wpt y = r1).
      { by eapply wpt_fun_eq2; eauto. }
      subst. auto.
  Qed.

  Lemma wpt_fun_inv (wpt: weighted_partition) x:
    ∃ U, In (wpt_fun wpt x, U) wpt.
  Proof.
    destruct wpt as [l part Heq].
    destruct part as [p Hall ? ?].
    destruct (Hall x) as (U&?&?); first done.
    exists U. rewrite //=. assert (Hin: In U (map snd l)).
    { rewrite Heq. done. }
    apply in_map_iff in Hin.
    destruct Hin as ((r'&U')&Heq'&Hin).
    subst. rewrite //=.
    rewrite (wpt_fun_eq2 _ U' x r') //=.
  Qed.

  Lemma wpt_fun_eq3' (wpt: weighted_partition) U1 x y:
    In U1 (wpt_part wpt) → U1 x → U1 y → wpt_fun wpt x = wpt_fun wpt y.
  Proof.
    intros. eapply (wpt_inhabited_fst_eq' wpt); eauto.
    - apply wpt_fun_eq1; eauto.
    - apply wpt_fun_eq1; eauto.
  Qed.

  Lemma In_wpt_intro (wpt: weighted_partition) r U:
    In (r, U) wpt → In U (wpt_part wpt).
  Proof.
    intros Hin. destruct wpt as [? ? Heq]. rewrite //=.
    rewrite -Heq. eapply in_map_iff; eexists; split; eauto. done.
  Qed.

  Lemma wpt_refinement_spec1 (wpt: weighted_partition) (P : partition) Hle:
    wpt_part (wpt_refinement wpt P Hle) = P.
  Proof.
    rewrite /wpt_refinement//=.
  Qed.

  Definition set_fun_map (f: A → R) (U: A → Prop) : R.
  Proof.
    destruct (excluded_middle_informative (∃ x : A, U x)) as [Hex|Hnex].
    - apply constructive_indefinite_description in Hex as (x&HU).
      exact (f x).
    - exact 0.
  Defined.

  Lemma set_fun_map_spec1 f (U: A → Prop) x:
    U x → (∀ x', U x' → f x' = f x) → set_fun_map f U = f x.
  Proof.
    intros HU. rewrite /set_fun_map.
    destruct excluded_middle_informative as [Hex|Hnex]; last first.
    { exfalso. apply Hnex. eexists; eauto. }
    intros Heq. destruct constructive_indefinite_description.
    eauto.
  Qed.

  Lemma set_fun_map_spec2 f (U: A → Prop):
    ¬ (∃ x, U x) → set_fun_map f U = 0.
  Proof.
    intros Hnex. rewrite /set_fun_map.
    destruct excluded_middle_informative as [Hex|Hnex'] => //=.
  Qed.
    
  Lemma set_fun_map_proper (U : A → Prop) f f':
    eq_fun f f' → set_fun_map f U = set_fun_map f' U.
  Proof.
    intros Hex. rewrite /set_fun_map.
    destruct excluded_middle_informative; eauto.
    destruct constructive_indefinite_description; eauto.
  Qed.


  Lemma wpt_refinement_spec2 (wpt: weighted_partition) (P : partition) Hle:
    ∀ x U, In (x, U) (wpt_refinement wpt P Hle) → (∃ a, U a) → ∃ U', U ⊆ U' ∧ In (x, U') wpt.
  Proof.
    rewrite /wpt_refinement//=.
    destruct P as [l H1 H2 H3 ].
    revert Hle. rewrite /le_partition//= => Hle.
    clear H1 H2 H3 => //=.
    induction l => x U Hin Hex.
    * inversion Hin. 
    * inversion Hin as [Hhd|tl]; last first.
      { eapply IHl => //=. eauto. }
      destruct constructive_indefinite_description as (?&?&Hsub).
      destruct (wpt_partition_spec1 wpt). rewrite //= in Hhd.
      destruct constructive_indefinite_description as ((?&?)&?&?).
      destruct excluded_middle_informative as [Hex'|Hnex]; eauto.
      ** inversion Hhd; subst => //=. eexists; split; eauto.
      ** exfalso. eapply Hnex; eauto. inversion Hhd; subst.
         edestruct Hex as (a&HU). exists a. eauto.
  Qed.

  Lemma wpt_refinement_spec3 (wpt: weighted_partition) (P : partition) Hle:
    ∀ x U, In (x, U) (wpt_refinement wpt P Hle) → ¬ (∃ a, U a) →
           x = 0 ∧ ∃ x' U', U ⊆ U' ∧ In (x', U') wpt.
  Proof.
    rewrite /wpt_refinement//=.
    destruct P as [l H1 H2 H3 ].
    revert Hle. rewrite /le_partition//= => Hle.
    clear H1 H2 H3 => //=.
    induction l => x U Hin Hnex.
    * inversion Hin. 
    * inversion Hin as [Hhd|tl]; last first.
      { eapply IHl => //=. eauto. }
      destruct constructive_indefinite_description as (?&?&Hsub).
      destruct (wpt_partition_spec1 wpt). rewrite //= in Hhd.
      destruct constructive_indefinite_description as ((?&?)&?&?).
      destruct excluded_middle_informative as [Hex'|Hnex']; eauto.
      ** exfalso. eapply Hnex; eauto.  inversion Hhd; subst.
         eauto.
      ** inversion Hhd; subst => //=. split; auto.
         do 2 eexists; split; eauto.
  Qed.

  Lemma wpt_refinement_list (wpt: weighted_partition) P Hle:
    wpt_list (wpt_refinement wpt P Hle) = map (λ U, (set_fun_map (wpt_fun wpt) U, U)) P.
  Proof.
    rewrite /wpt_refinement//=.
    destruct P as [l H1 H2 H3].
    rewrite //=. revert Hle. rewrite /le_partition//= => Hle. 
    clear H1 H2 H3.
    induction l as [| a l].
    * rewrite //=.
    * rewrite //=. f_equal.
      ** rewrite /set_fun_map.
         destruct constructive_indefinite_description as (?&?&Hsub1).
         destruct (wpt_partition_spec1 wpt). rewrite //=.
         destruct constructive_indefinite_description as ((?&?)&?&?).
         destruct excluded_middle_informative as [(a'&?)|] => //=.
         subst. f_equal.
         transitivity ((wpt_fun wpt) a').
         { symmetry. eapply wpt_fun_eq2; eauto. apply Hsub1. done. }
         destruct constructive_indefinite_description as (?&?).
         eapply (wpt_fun_eq3 wpt P); eauto; eapply Hsub1; eauto.
      ** eauto. 
  Qed.

  Opaque set_fun_map.

  Lemma wpt_refinement_proper_list (wpt wpt': weighted_partition) P Hle Hle':
    eq_fun (wpt_fun wpt) (wpt_fun wpt') →
    wpt_list (wpt_refinement wpt P Hle) = wpt_list (wpt_refinement wpt' P Hle').
  Proof.
    intros Heq.
    rewrite ?wpt_refinement_list. apply map_ext => a.
    f_equal. by apply set_fun_map_proper.
  Qed.

  Lemma wpt_refinement_proper (wpt wpt': weighted_partition) P Hle Hle':
    eq_fun (wpt_fun wpt) (wpt_fun wpt') →
    wpt_refinement wpt P Hle = wpt_refinement wpt' P Hle'.
  Proof.
    intros Hequiv.
    eapply (wpt_refinement_proper_list _ _ P Hle Hle') in Hequiv.
    destruct (wpt_refinement _ _ _) as [l p Hs], (wpt_refinement _ _ _) as [l' p' Hs'].
    assert (l = l').
    { simpl in Hequiv. rewrite //= in Hequiv. }
    subst.
    assert (Hpl: partition_list p = partition_list p').
    { congruence. }
    assert (p = p').
    { destruct p as [pl ? ? ?].
      destruct p' as [pl' ? ? ?].
      rewrite //= in Hpl. subst. f_equal; apply classical_proof_irrelevance. }
    subst. f_equal; apply classical_proof_irrelevance.
  Qed.

  Opaque wpt_refinement.

  Lemma wpt_refinement_sum (wpt: weighted_partition) (P : partition) Hle:
    eq_fun (wpt_fun wpt) (wpt_fun (wpt_refinement wpt P Hle)).
  Proof.
    intros a.
    destruct (partition_union P a) as (U&Hin&HU) => //=.
    edestruct (wpt_refinement_spec2 wpt P Hle (wpt_fun (wpt_refinement _ _ Hle) a) U)
              as (U'&Hsubseteq&Hin').
    { apply wpt_fun_eq1; eauto. }
    { eexists; eauto. }
    eapply wpt_inhabited_fst_eq'; eauto.
    apply wpt_fun_eq1; eauto.
    eapply In_wpt_intro; eauto.
  Qed.

  Lemma In_wpt_snd_measurable rU (wpt: weighted_partition) :
    In rU wpt → F (snd rU).
  Proof.
    intros Hin. destruct wpt as [l p Hspec].
    rewrite //= in Hin.
    apply (partition_measurable p). rewrite -Hspec.
    apply in_map_iff; eexists; split; eauto; done.
  Qed.

  Lemma measurable_indicator U:
    F U →
    measurable (λ x, if excluded_middle_informative (U x) then
                           1
                         else
                           0) F (borel R_UniformSpace).
  Proof.
    intros HU V HV.
    rewrite /fun_inv.
    destruct (Classical_Prop.classic (V 1));
    destruct (Classical_Prop.classic (V 0)).
    * eapply sigma_proper; last eapply sigma_full.
      intros a. destruct excluded_middle_informative; split; auto.
    * eapply sigma_proper; last eapply HU.
      intros a. destruct excluded_middle_informative; split; auto.
      ** intros. contradiction; eauto.
      ** intros. contradiction; eauto.
    * eapply sigma_proper; last eapply sigma_closed_complements, HU. 
      intros a. destruct excluded_middle_informative; split; auto.
      ** intros. contradiction; eauto.
      ** intros. contradiction; eauto.
    * eapply sigma_proper; last eapply sigma_empty_set.
      intros a. destruct excluded_middle_informative; split; auto.
      ** intros. contradiction; eauto.
      ** intros. contradiction; eauto.
  Qed.

  Lemma wpt_fun_measurable wpt : measurable (wpt_fun wpt) F (borel _).
  Proof.
    assert (Hmeas: ∀ r U, In (r, U) wpt → F U).
    { intros. eapply In_wpt_snd_measurable with (rU := (r, U)); eauto. }
    destruct wpt as [l p Heq] => //=. rewrite //= in Hmeas.
    rewrite /wpt_fun => //=.
    clear p Heq. induction l as [| (r, U) l].
    * rewrite //= => U HU. rewrite /fun_inv.
      destruct (Classical_Prop.classic (U 0)).
      ** eapply sigma_proper; last eapply sigma_full.
         intros a; split; auto. rewrite big_nil => //=.
      ** eapply sigma_proper; last eapply sigma_empty_set.
         intros a; split; auto; last by intros [].
         rewrite big_nil. auto.
    * eapply (measurable_proper'
              (λ x, r * (if excluded_middle_informative (U x) then 1 else 0)
                    + \big[Rplus/0]_(aU <- l) (if excluded_middle_informative (aU.2 x) then
                                                 aU.1
                                               else 0))).
      { intros x.
        rewrite big_cons. f_equal. destruct excluded_middle_informative; auto =>//=; nra.
      }
      { reflexivity. }
      { reflexivity. }
      apply measurable_plus; last first.
      { eapply IHl. intros. eapply Hmeas. right. eauto.  }
      apply measurable_scal. 
      apply measurable_indicator. 
      eapply Hmeas. left; eauto.
  Qed.

  Lemma In_wpt_fst_fun rU (wpt: weighted_partition) a:
    In rU wpt → (snd rU) a → fst rU = wpt_fun wpt a.
  Proof.
    intros Hin HUa. symmetry. eapply wpt_fun_eq2; eauto.
    destruct rU; eauto.
  Qed.

  Lemma wpt_map_snd_disjoint (wpt: weighted_partition):
    ## (map snd wpt).
  Proof.
    destruct wpt as [l ? Hspec]. rewrite //= Hspec. apply partition_disjoint.
  Qed.

  Definition wpt_fun_lb (wpt: weighted_partition): R :=
    fold_left Rmin (map fst wpt) 0.

  Definition wpt_fun_ub (wpt: weighted_partition): R :=
    fold_left Rmax (map fst wpt) 0.

  Lemma wpt_fun_lb_spec wpt:
    ∀ x, wpt_fun_lb wpt <= wpt_fun wpt x.
  Proof.
    intros x. edestruct (wpt_fun_inv wpt x).
    eapply fold_left_Rmin_lb.
    apply in_map_iff; eexists; split; eauto. done.
  Qed.
  
  Lemma wpt_fun_ub_spec wpt:
    ∀ x, wpt_fun wpt x <= wpt_fun_ub wpt.
  Proof.
    intros x. edestruct (wpt_fun_inv wpt x).
    eapply fold_left_Rmax_ub.
    apply in_map_iff; eexists; split; eauto. done.
  Qed.

  Lemma measure_intersect_wpt U (wpt: weighted_partition) :
    F U →
    μ U = \big[Rplus/0]_(aU' <- wpt) (μ (U ∩ (snd aU'))).
  Proof.
    intros HF.
    rewrite -(measure_proper _ _ (union_list (map (λ U', U ∩ U'.2) (wpt_list wpt))));
      last first.
    { intros a; split.
      * intros (?&Hin'&Ha)%union_list_inv.
        apply in_map_iff in Hin' as (?&?&?); subst. destruct Ha; eauto.
      * intros Ha.
        destruct (partition_union (wpt_part wpt) a) as (U'&Hin'&HU') => //=.
        rewrite -wpt_partition_spec1 in Hin'.  
        apply in_map_iff in Hin' as (xU'&?&Hin'); subst.
        apply (union_list_intro _ _ (U ∩ snd xU')).
        ** apply in_map_iff. eexists; split; eauto.
        ** split; eauto.
    }
    rewrite measure_list_additivity; first by rewrite big_map.
    * intros U'' Hin''. apply in_map_iff in Hin'' as (?&?&?).
      subst. apply sigma_closed_pair_intersect; auto. eapply In_wpt_snd_measurable; eauto.
    * specialize (wpt_map_snd_disjoint wpt).
      clear. destruct wpt as [l ? ?].
      rewrite //=. clear -l. induction l as [| a l] => //=.
      inversion 1; subst. apply disjoint_list_cons; split; eauto.
      intros x (Hin1&Hin2).
      destruct Hin1 as (Hin1a&Hin1b).
      apply union_list_inv in Hin2 as (?&Hin2&Hsat).
      apply in_map_iff in Hin2 as (U'&Heq&Hin); subst.
      destruct Hsat as (?&?).
      eapply (disjoint_list_inv' x (snd a)); eauto.
      eapply in_map_iff; eexists; split; eauto; done.
  Qed.

  Lemma wpt_integral_refinement (wpt: weighted_partition) (P : partition) Hle:
    wpt_integral wpt = wpt_integral (wpt_refinement wpt P Hle).
  Proof.
    rewrite /wpt_integral.
    transitivity (\big[Rplus/0]_(aU <- wpt)
                   (\big[Rplus/0]_(aU' <- wpt_refinement _ _ Hle) (aU.1 * μ (aU.2 ∩ aU'.2)))).
    { 
      apply eq_bigr_In => i _ Hin => //=.
      rewrite -big_distrr //=. f_equal.
      apply measure_intersect_wpt.
      eapply In_wpt_snd_measurable; eauto.
    }
    rewrite exchange_big //=. apply eq_bigr_In.
    intros i _ Hin.
    transitivity (\big[Rplus/0]_(i0 <- wpt) (fst i * μ (i0.2 ∩ i.2))).
    { apply eq_bigr_In => i' -_ Hin'.
      destruct i as (r&U).
      destruct i' as (r'&U').
      rewrite //=. 
      destruct (Classical_Prop.classic (∃ x, (U' ∩ U) x)) as [Hex|Hemp]; last first.
      { assert (U' ∩ U ≡ ∅) as Hnull.
        { split.
          * intros. exfalso; eauto.
          * inversion 1.
        }
        rewrite Hnull. rewrite measure_empty. nra.
      }
      destruct Hex as (a&(HinU'&HinU)).
      f_equal. edestruct wpt_refinement_spec2 as (U''&?&?); eauto.
      eapply wpt_inhabited_fst_eq; eauto.
    }
    rewrite -big_distrr. f_equal.
    symmetry. 
    rewrite (measure_intersect_wpt _ wpt); last
      eapply In_wpt_snd_measurable; eauto.
    apply eq_bigr. intros. rewrite [a in μ (a) = _]comm. done.
  Qed.


  Lemma wpt_integral_proper (wpt wpt': weighted_partition):
    eq_fun (wpt_fun wpt) (wpt_fun wpt') → 
    wpt_integral wpt = wpt_integral wpt'. 
  Proof.
    intros Heq.
    edestruct (common_refinement (wpt_part wpt) (wpt_part wpt')) as (P&Hle&Hle').
    rewrite (wpt_integral_refinement wpt P Hle).
    rewrite (wpt_integral_refinement wpt' P Hle').
    rewrite /wpt_integral//=.
    rewrite (wpt_refinement_proper _ _ _ _ _ Heq). done.
  Qed.

  Lemma measure_pos_inhabited U: μ U > 0 → ∃ a, U a.
  Proof.
    intros Hgt0. apply Classical_Prop.NNPP => Hnex.
    cut (μ U = 0); first by nra.
    rewrite (measure_proper _ _ _ ∅); first apply measure_empty.
    intros x; split.
    * intros HU. exfalso; eapply Hnex. eexists; eauto.
    * inversion 1.
  Qed.

  Definition wpt_comp (f : R → R) (wpt : weighted_partition) : weighted_partition.
    refine {| wpt_list := map (λ rU, (f (fst rU), snd rU)) (wpt_list wpt);
              wpt_part := wpt_part wpt;
              wpt_partition_spec1 := _ |}.
    { abstract (rewrite -wpt_partition_spec1 map_map => //=). }
  Defined.

  Lemma wpt_comp_spec f wpt:
    ∀ x, wpt_fun (wpt_comp f wpt) x = f (wpt_fun wpt x).
  Proof.
    intros x.
    destruct (partition_union (wpt_part wpt) x) as (U&Hin&HU) => //=.
    eapply wpt_fun_eq2; eauto. rewrite /wpt_comp//=. apply in_map_iff.
    exists (wpt_fun wpt x, U); split; eauto.
    apply wpt_fun_eq1; eauto.
  Qed.

  Definition partition_indicator U (Hmeas: F U) : partition.
    refine {| partition_list := U :: compl U :: nil |}.
    * clear. rewrite /unionL//= => x.
      intros. destruct (Classical_Prop.classic (U x)).
      ** exists U; eauto.
      ** exists (compl U); eauto.
    * clear. econstructor => //=; last econstructor; firstorder; econstructor.
    * intros U'. inversion 1 as [| Hin ]; subst; auto; try apply sigma_closed_complements.
      inversion Hin as [| []]; subst; auto.
  Defined.

  Definition wpt_indicator U (Hmeas: F U) : weighted_partition.
    refine {| wpt_list := (1, U) :: (0, compl U) :: nil; wpt_part := partition_indicator U Hmeas |}.
    rewrite //=.
  Defined.

  Lemma wpt_indicator_spec U Hmeas :
    ∀ x, wpt_fun (wpt_indicator U Hmeas) x =
         if (excluded_middle_informative (U x)) then 1 else 0.
  Proof.
    rewrite /wpt_fun//= => x. rewrite ?big_cons big_nil //=.
    do 2 destruct excluded_middle_informative; nra.
  Qed.

  Definition wpt_bin_op (f: R → R → R) (wpt1 wpt2 : weighted_partition)  : weighted_partition.
    specialize (common_refinement (wpt_part wpt1) (wpt_part wpt2)).
    intros (P&Hle1&Hle2)%constructive_indefinite_description.
    refine {| wpt_list := map (λ U, (set_fun_map (λ x, f (wpt_fun wpt1 x) (wpt_fun wpt2 x)) U, U)) P;
              wpt_part := P;
              wpt_partition_spec1 := _ |}.
    { abstract (rewrite map_map map_id => //=). }
  Defined.

  Lemma wpt_bin_op_spec f wpt1 wpt2:
    ∀ x, wpt_fun (wpt_bin_op f wpt1 wpt2) x = f (wpt_fun wpt1 x) (wpt_fun wpt2 x).
  Proof.
    intros x. 
    rewrite /wpt_bin_op. destruct (constructive_indefinite_description) as (P&Hle1&Hle2).
    destruct (partition_union P x) as (U&Hin&HU) => //=.
    eapply wpt_fun_eq2; eauto. rewrite /wpt_comp//=. apply in_map_iff.
    exists U; split; auto.
    f_equal. rewrite (set_fun_map_spec1 _ _ x); auto.
    intros x' HU'; f_equal.
    - edestruct (Hle1 U) as (U1&?&Hsub1); auto.
      eapply (wpt_fun_eq3' wpt1 U1); eauto.
    - edestruct (Hle2 U) as (U1&?&Hsub1); auto.
      eapply (wpt_fun_eq3' wpt2 U1); eauto.
  Qed.
  

  Definition wpt_plus := wpt_bin_op Rplus.

  Lemma wpt_plus_spec wpt1 wpt2:
    ∀ x, wpt_fun (wpt_plus wpt1 wpt2) x = wpt_fun wpt1 x + wpt_fun wpt2 x.
  Proof. apply wpt_bin_op_spec. Qed.

  Definition wpt_min  := wpt_bin_op Rmin.
  Definition wpt_max  := wpt_bin_op Rmax.

  Lemma wpt_min_spec wpt1 wpt2:
    ∀ x, wpt_fun (wpt_min wpt1 wpt2) x = Rmin (wpt_fun wpt1 x) (wpt_fun wpt2 x).
  Proof. apply wpt_bin_op_spec. Qed.

  Lemma wpt_max_spec wpt1 wpt2:
    ∀ x, wpt_fun (wpt_max wpt1 wpt2) x = Rmax (wpt_fun wpt1 x) (wpt_fun wpt2 x).
  Proof. apply wpt_bin_op_spec. Qed.

  Definition wpt_scal (k: R) (wpt : weighted_partition) :=
    wpt_comp (λ x, k * x) wpt.

  Lemma wpt_scal_spec k wpt:
    ∀ x, wpt_fun (wpt_scal k wpt) x = k * wpt_fun wpt x.
  Proof.
    intros x. by rewrite wpt_comp_spec.
  Qed.

  Definition wpt_const (k: R) : weighted_partition :=
    wpt_scal k (wpt_indicator (λ x, True) (sigma_full _ _)).

  Lemma wpt_const_spec k :
    ∀ x, wpt_fun (wpt_const k) x = k.
  Proof.
    intros x. rewrite wpt_scal_spec wpt_indicator_spec.
    destruct excluded_middle_informative => //=. ring.
  Qed.

  Definition wpt_indicator_scal_list l (Hmeas: ∀ r U, In (r: R, U) l → F U) : weighted_partition.
    induction l as [| (r, U) l].
    - exact (wpt_indicator empty_set (sigma_empty_set F)). 
    - eapply wpt_plus.
      * refine (wpt_scal r (wpt_indicator U _)).
        abstract (eapply Hmeas; by left).
      * eapply IHl. abstract(intros r' U' Hin; eapply Hmeas; right; eauto).
  Defined.

  Lemma wpt_indicator_scal_list_spec1 l Hmeas:
    ∀ x, wpt_fun (wpt_indicator_scal_list l Hmeas) x =
         \big[Rplus/0]_(aU <- l)
          (if excluded_middle_informative (aU.2 x) then
             (aU.1)
           else
             0).
  Proof.
    induction l as [| (r, U) l].
    - intros x. rewrite /wpt_indicator_scal_list//= wpt_indicator_spec big_nil.
      destruct excluded_middle_informative as [[]|]; auto.
    - intros x. rewrite wpt_plus_spec. rewrite big_cons. f_equal.
      * rewrite wpt_scal_spec wpt_indicator_spec //=. destruct excluded_middle_informative; nra.
      * eapply IHl.
  Qed.

  Lemma wpt_indicator_scal_list_spec_cons r U l Hmeas:
    ∃ pf1 pf2, ∀ x, wpt_fun (wpt_indicator_scal_list ((r, U) :: l) Hmeas) x =
         wpt_fun (wpt_plus (wpt_scal r (wpt_indicator U pf1))
                           (wpt_indicator_scal_list l pf2)) x.
  Proof.
    rewrite /wpt_indicator_scal_list //=. do 2 eexists. intros x.
    f_equal.
  Qed.

  Lemma wpt_integral_ge0 wpt:
    (∀ x, wpt_fun wpt x >= 0) →
    wpt_integral wpt >= 0. 
  Proof.
    intros Hge. rewrite /wpt_integral.
    apply Rle_ge, Rle_big0_In.
    intros i _ Hin. destruct (measure_nonneg μ (snd i)) as [Hgt0|Heq0].
    * edestruct measure_pos_inhabited as (a&Hina); eauto.
      rewrite (In_wpt_fst_fun _ wpt a); auto.
      specialize (Hge a). nra.
    * rewrite Heq0. nra.
  Qed.

  Lemma wpt_integral_abs1 wpt:
    Rabs (wpt_integral wpt) <= wpt_integral (wpt_comp Rabs wpt).
  Proof.
    rewrite /wpt_integral. rewrite /wpt_comp//= big_map//=.
    etransitivity; first eapply Rabs_bigop_triang => //=.
    right. eapply eq_bigr => i _. rewrite Rabs_mult. f_equal.
    apply Rabs_right. apply measure_nonneg.
  Qed.

  Lemma wpt_integral_plus wpt1 wpt2:
    wpt_integral (wpt_plus wpt1 wpt2) = wpt_integral wpt1 + wpt_integral wpt2.
  Proof.
    rewrite /wpt_plus/wpt_bin_op.
    destruct constructive_indefinite_description as (P&Hle1&Hle2) => //=.
    rewrite (wpt_integral_refinement wpt1 _ Hle1).
    rewrite (wpt_integral_refinement wpt2 _ Hle2).
    rewrite /wpt_integral//=. rewrite ?wpt_refinement_list.
    rewrite ?big_map -big_split //=.
    apply eq_bigr_In. 
    intros i _ Hin. destruct (measure_nonneg μ i) as [Hgt0|Heq0].
    * edestruct measure_pos_inhabited as (a&Hina); eauto.
      rewrite ?(set_fun_map_spec1 _ _ a) //=; first nra.
      ** intros. edestruct (Hle2 _ Hin) as (U&Ua&Hsub).
         eapply (wpt_fun_eq3' _ U); eauto.
      ** intros. edestruct (Hle1 _ Hin) as (U&Ua&Hsub).
         eapply (wpt_fun_eq3' _ U); eauto.
      ** {
          intros; f_equal.
          ** intros. edestruct (Hle1 _ Hin) as (U&Ua&Hsub).
             eapply (wpt_fun_eq3' _ U); eauto.
          ** intros. edestruct (Hle2 _ Hin) as (U&Ua&Hsub).
             eapply (wpt_fun_eq3' _ U); eauto.
         }
    * rewrite Heq0. nra.
  Qed.

  Lemma wpt_integral_scal k wpt:
    wpt_integral (wpt_scal k wpt) = k * (wpt_integral wpt).
  Proof.
    rewrite /wpt_integral/wpt_scal/wpt_comp//=. rewrite big_map.
    rewrite big_distrr => //=. apply eq_bigr; intros; nra.
  Qed.

  Lemma wpt_integral_indicator U Hmeas:
    wpt_integral (wpt_indicator U Hmeas) = μ U. 
  Proof.
    rewrite /wpt_integral/wpt_indicator. rewrite ?big_cons big_nil //=.
    field.
  Qed.

  Lemma wpt_integral_const k :
    wpt_integral (wpt_const k) = k * μ (λ _, True).
  Proof.
    rewrite wpt_integral_scal wpt_integral_indicator //.
  Qed.


  (*
  Lemma wpt_integral_mono_ae wpt1 wpt2:
    almost_everywhere_meas μ (λ x, wpt_fun wpt1 x <= wpt_fun wpt2 x) →
    wpt_integral wpt1 <= wpt_integral wpt2.
  Proof.
   *)

  Lemma wpt_integral_mono wpt1 wpt2:
    (∀ x, wpt_fun wpt1 x <= wpt_fun wpt2 x) →
    wpt_integral wpt1 <= wpt_integral wpt2.
  Proof.
    intros Hle.
    cut (0 <= wpt_integral wpt2 + -1 * wpt_integral wpt1).
    { intros; nra. }
    rewrite -wpt_integral_scal -wpt_integral_plus.
    apply Rge_le, wpt_integral_ge0 => x.
    rewrite wpt_plus_spec wpt_scal_spec. specialize (Hle x). nra.
  Qed.

  Lemma Lim_seq_correct' (u: nat → R) v : ex_lim_seq u → Lim_seq u = v → is_lim_seq u v.
  Proof.
    intros Hex <-. apply Lim_seq_correct. done.
  Qed.

  Lemma wpt_indicator_scal_list_spec2 l Hmeas:
    ## (map snd l) →
    ∀ x, ((∀ r U, In (r, U) l → ¬ U x) ∧ wpt_fun (wpt_indicator_scal_list l Hmeas) x = 0) ∨
         (∃ r U, In (r, U) l ∧ U x ∧ wpt_fun (wpt_indicator_scal_list l Hmeas) x = r).
  Proof.
    induction l as [|(r, U) l].
    - rewrite //=.  intros. left. rewrite wpt_indicator_spec; split.
      * auto. 
      * destruct excluded_middle_informative as [[]|]; auto.
    - intros Hdisj x. destruct (Classical_Prop.classic (U x)).
      * assert (Hnin: (∀ (r0 : R) (U0 : A → Prop), In (r0, U0) l → ¬ U0 x)).
        {
          intros ? U' Hin. intros HU'. rewrite //= in Hdisj. eapply disjoint_list_inv; eauto.
          apply in_map_iff; eexists; split; eauto; done.
        }
        right. exists r, U; split_and!; first by left.
        ** auto.
        ** edestruct (wpt_indicator_scal_list_spec_cons) as (?&?&->).
           rewrite wpt_plus_spec. rewrite -[a in _ = a]Rplus_0_r; f_equal.
           *** rewrite wpt_scal_spec wpt_indicator_spec;
                 destruct excluded_middle_informative; eauto; first nra.
               contradiction; eauto.
           *** edestruct IHl as [(?&?)|(?&?&Hfalse&?&?)].
               **** inversion Hdisj; eauto.
               **** eauto.
               **** exfalso. eapply Hnin; eauto.
      * edestruct (wpt_indicator_scal_list_spec_cons) as (?&?&->).
        edestruct IHl as [(?&?)|(?&?&?&?&?)].
        { inversion Hdisj; eauto. }
        ** left. split; eauto.
           *** intros ??; inversion 1 as [Heq|]; subst.
               **** inversion Heq; subst; eauto.
               **** eauto.
           *** rewrite wpt_plus_spec. rewrite -[a in _ = a]Rplus_0_r; f_equal; eauto.
               rewrite wpt_scal_spec wpt_indicator_spec.
               destruct excluded_middle_informative; eauto; try nra; try contradiction.
        ** right. do 2 eexists; split_and!; eauto.
           right. rewrite wpt_plus_spec.
           rewrite wpt_scal_spec wpt_indicator_spec.
           destruct excluded_middle_informative; eauto; try contradiction.
           rewrite Rmult_0_r Rplus_0_l. congruence.
  Qed.

  Lemma wpt_integral_indicator_scal_list l Hmeas:
    wpt_integral (wpt_indicator_scal_list l Hmeas) = \big[Rplus/0]_(aU <- l) (aU.1 * μ (aU.2)).
  Proof.
    induction l as [|(r&U) l].
    - by rewrite /wpt_indicator_scal_list//= big_nil wpt_integral_indicator
                 measure_empty.
    - rewrite big_cons wpt_integral_plus. f_equal.
      * rewrite wpt_integral_scal wpt_integral_indicator //=.
      * eauto.
  Qed.

  Lemma is_lim_seq_big_op {X: Type} (f: X → R) (fn: nat → X → R) (l: list X) :
    (∀ x, In x l → is_lim_seq (λ n, fn n x) (f x)) →
    is_lim_seq (λ n : nat, \big[Rplus/0]_(j <- l) (fn n j))
               (\big[Rplus/0]_(i <- l) (f i)).
  Proof.
    intros Hin.
    induction l.
    - rewrite big_nil. eapply is_lim_seq_ext.
      { intros n. rewrite big_nil. done. }
      eapply is_lim_seq_const.
    - rewrite big_cons. eapply is_lim_seq_ext.
      { intros n. rewrite big_cons. done. }
      eapply is_lim_seq_plus.
      * eapply Hin. by left.
      * eapply IHl. intros. eapply Hin; by right.
      * rewrite //=.
  Qed.

  Lemma wpt_integral_mct_pos (wpt_n: nat → weighted_partition) (wpt: weighted_partition) :
    (∀ x, is_lim_seq (λ n, wpt_fun (wpt_n n) x) (wpt_fun wpt x)) →
    (∀ x, ∀ n, 0 <= wpt_fun (wpt_n n) x) →
    (∀ x, ∀ n, wpt_fun (wpt_n n) x <= wpt_fun (wpt_n (S n)) x) →
    is_lim_seq (λ n, wpt_integral (wpt_n n)) (wpt_integral wpt).
  Proof.
    intros Hlim Hpos_fn Hmono.
    assert (ex_finite_lim_seq ((λ n, wpt_integral (wpt_n n)))) as Hex_fin.
    { eapply ex_finite_lim_seq_incr.
      - intros. apply wpt_integral_mono; eauto.
      - intros n.  apply wpt_integral_mono; eauto.
        intros x. eapply is_lim_seq_incr_compare in Hlim; eauto.
    }
    apply ex_finite_lim_seq_correct in Hex_fin as (Hex&Hfin).
    apply Lim_seq_correct'; eauto.
    apply Rbar_le_antisym.
    { rewrite -Lim_seq_const. apply Lim_seq_le_loc. exists O => ??.
      apply wpt_integral_mono; intros. 
      eapply is_lim_seq_incr_compare in Hlim; eauto.
    }
    apply is_finite_correct in Hfin as (y&Heq). rewrite Heq.
    assert (Hpos_f: ∀ x, 0 <= wpt_fun wpt x).
    { intros x. etransitivity; first eapply (Hpos_fn x O).
      eapply is_lim_seq_incr_compare in Hlim; eauto.
    }
    assert (0 <= wpt_integral wpt) as [Hwpt_int_pos|Hwpt_int0];
      auto using Rge_le, wpt_integral_ge0; last first.
    { rewrite -Hwpt_int0 //=.
      eapply (is_lim_seq_pos (λ n, wpt_integral (wpt_n n))).
      * intros. apply wpt_integral_ge0; auto.
      * apply Lim_seq_correct'; eauto.
    }

    rewrite /Rbar_le. apply le_epsilon => eps0 Hpos0.
    set (eps := eps0 / wpt_integral wpt).
    assert (Hpos: 0 < eps).
    { rewrite /eps. rewrite /Rdiv. 
      apply Rmult_lt_0_compat; auto. apply Rinv_0_lt_compat; auto. }

    set (An := λ n r U, U ∩ fun_inv (wpt_fun (wpt_n n)) (λ x, (1 - eps) * r <= x)).
    assert (HmeasAn: ∀ n r U, F U → F (An n r U)).
    { intros n r U HF. rewrite /An.
      apply sigma_closed_pair_intersect; auto.
      apply wpt_fun_measurable, closed_ray_borel_ge.
    }
    assert (HdisjAn: ∀ n l, ## (map snd l) → ## (map (λ x, An n (fst x) (snd x))) l).
    { 
      clear. intros m l Hdisj. induction l as [| (r, U) l] => //=.
      econstructor.
      * intros x [[Ha _] HU]. rewrite //= in Hdisj.
        apply union_list_inv in HU as (?&Hin&Hsat).
        apply in_map_iff in Hin as (?&?&Hin). subst.
        destruct Hsat as [Ha' _].
        eapply disjoint_list_inv in Hdisj; eauto.
        eapply Hdisj; split; eauto.
        apply in_map. eauto.
      * eapply IHl. inversion Hdisj; eauto.
    }
    set (gn_list := λ n, map (λ rU, ((1 - eps) * fst rU, An n (fst rU) (snd rU))) wpt).
    assert (Hmeas_gn: ∀ n r U, In (r, U) (gn_list n) → F U).
    { intros n r U.  clear -An HmeasAn.  rewrite /gn_list.
      intros ((r'&U')&Heq&Hin%In_wpt_snd_measurable)%in_map_iff.
      inversion Heq; subst. apply HmeasAn. auto.
    }
    set (gn := λ n, wpt_indicator_scal_list (gn_list n) (Hmeas_gn _)).
    assert (∀ n x, wpt_fun (gn n) x <= wpt_fun (wpt_n n) x).
    { 
      intros n x. rewrite /gn.
      edestruct (wpt_indicator_scal_list_spec2 (gn_list n)) as [(?&Hzero)|Halt]; eauto.
      { rewrite /gn_list. rewrite map_map//=. eapply HdisjAn. eapply wpt_map_snd_disjoint. }
      * rewrite Hzero. eauto.
      * destruct Halt as (r&U&Hin&HU&->). 
        rewrite /gn_list in Hin. apply in_map_iff in Hin.
        destruct Hin as ((r'&?)&Heq'&Hin).
        inversion Heq'; subst.
        destruct HU as [HU' Hinv].
        rewrite //=/fun_inv in Hinv.
    }
    assert (Hrpos: ∀ r U, (∃ x, U x) → In (r, U) wpt → 0 <= r).
    {
      intros r U (x&HUx) Hin. rewrite -(wpt_fun_eq2 wpt U x r); eauto.
    }
    assert (Hunion: ∀ r U, In (r, U) wpt → U ≡ unionF (λ n, An n r U)).
    { 
      intros r U a; split.
      - intros HU. rewrite /An.
        destruct (Hrpos r U) as [Hrpos'|Hr0]; last first; eauto.
        { subst. exists O; split; auto => //=. rewrite /fun_inv Rmult_0_r.
          eauto. }
        edestruct (Hlim x (λ x, x >= (1 - eps) * r)) as (n&Hgen).
        { rewrite //= /locally.
          unshelve (eexists).
          { exists (eps * r). abstract (nra). }
          intros r' => //=. rewrite /ball//=/AbsRing_ball/abs//=/minus/plus/opp//=.
          rewrite (wpt_fun_eq2 wpt U x r) //=.
          apply Rabs_case; nra.
        }
        exists n; split; auto. rewrite /fun_inv//=. apply Rge_le, Hgen. auto.
      - intros (n&(?&?)). auto.
    }
    assert (is_lim_seq (λ n, wpt_integral (gn n)) ((1 - eps) * wpt_integral wpt)).
    { 
      rewrite {2}/wpt_integral.
      eapply is_lim_seq_ext.
      { intros n.  rewrite /gn. rewrite wpt_integral_indicator_scal_list/gn_list.
        rewrite big_map//=. }
      rewrite big_distrr //=.
      apply is_lim_seq_big_op. intros (r&U) Hin.
      rewrite -Rmult_assoc.
      rewrite //=.
      apply (is_lim_seq_scal_l (λ n, μ (An n r U)) ((1 - eps) * r) (μ U)).
      rewrite {2}(Hunion r U) //.
      apply measure_incr_seq.
      * intros i.  apply HmeasAn. apply (In_wpt_snd_measurable (r, U) wpt); eauto.
      * rewrite /An/fun_inv => i. intros x (HU&Hinv); split; auto.
        etransitivity; eauto.
    }
    assert (Hineq: (1 - eps) * (wpt_integral wpt) <= y).
    {
      apply (is_lim_seq_le (λ n, wpt_integral (gn n)) (λ n, wpt_integral (wpt_n n))
                           ((1 - eps) * (wpt_integral wpt)) y); eauto.
      { intros n; eapply wpt_integral_mono; eauto. }
      { apply Lim_seq_correct'; eauto. }
    }
    rewrite /eps in Hineq. field_simplify in Hineq; last by nra.
    nra.
  Qed.

  Lemma wpt_integral_mct (wpt_n: nat → weighted_partition) (wpt: weighted_partition) :
    (∀ x, is_lim_seq (λ n, wpt_fun (wpt_n n) x) (wpt_fun wpt x)) →
    (∀ x, ∀ n, wpt_fun (wpt_n n) x <= wpt_fun (wpt_n (S n)) x) →
    is_lim_seq (λ n, wpt_integral (wpt_n n)) (wpt_integral wpt).
  Proof.
    intros. 
    set (wpt_n' := λ n, wpt_plus (wpt_n n) (wpt_const (-wpt_fun_lb (wpt_n O)))).
    set (wpt' := wpt_plus wpt (wpt_const (-wpt_fun_lb (wpt_n O)))).
    assert (Hlim: is_lim_seq (λ n, wpt_integral (wpt_n' n)) (wpt_integral wpt')).
    { apply wpt_integral_mct_pos.
      - intros x. rewrite wpt_plus_spec.
        eapply is_lim_seq_ext.
        { intros n. by rewrite wpt_plus_spec. }
        eapply is_lim_seq_plus; eauto.
        * apply is_lim_seq_const.
        * rewrite //=.
      - intros x n. rewrite wpt_plus_spec.
        transitivity (wpt_fun (wpt_n O) x + wpt_fun (wpt_const (- wpt_fun_lb (wpt_n O))) x).
        { specialize (wpt_fun_lb_spec (wpt_n O) x). rewrite wpt_const_spec.  nra. }
        apply Rplus_le_compat; last reflexivity.
        induction n; first reflexivity.
        etransitivity; eauto.
      - intros x n. rewrite ?wpt_plus_spec.
        apply Rplus_le_compat; eauto; reflexivity.
    }
    rewrite wpt_integral_plus wpt_integral_const // in Hlim.
    apply (is_lim_seq_ext _ (λ n, wpt_integral (wpt_n n)
                                  + - wpt_fun_lb (wpt_n O) * μ (λ _, True))) in Hlim;
      last first.
    { intros n. rewrite wpt_integral_plus wpt_integral_const //. }
    eapply (is_lim_seq_plus_inv _ (λ n, - wpt_fun_lb (wpt_n O) * μ (λ _, True))); eauto.
    apply is_lim_seq_const.
  Qed.

  Lemma wpt_rep_aux1 wpt : ∀ r U, In (r, U) (wpt_list wpt) → F U.
  Proof.
    intros r U Hin. eapply (partition_measurable (wpt_part wpt)).
    rewrite -wpt_partition_spec1. apply in_map_iff; eexists; split; eauto; done.
  Qed.

  Lemma wpt_rep_indicator_scal_list wpt :
    ∀ x, wpt_fun wpt x = wpt_fun (wpt_indicator_scal_list wpt (wpt_rep_aux1 wpt)) x.
  Proof.
    intros x. destruct (partition_union (wpt_part wpt) x) as (U&Hin&HU).
    { done. }
    feed pose proof (wpt_fun_eq1 wpt x U); eauto.
    feed pose proof (wpt_indicator_scal_list_spec2 wpt (wpt_rep_aux1 wpt)) as Hspec; eauto.
    { rewrite wpt_partition_spec1. apply partition_disjoint. } 
    destruct (Hspec x) as [(Hnin&?)|(r&U'&Hin'&HU'&Heq)].
    - exfalso. eapply Hnin; eauto.
    - rewrite Heq.
      eapply wpt_fun_eq2; eauto.
  Qed.

  Lemma wpt_induction (P : weighted_partition → Prop):
    (∀ wpt1 wpt2, eq_fun (wpt_fun wpt1) (wpt_fun wpt2) → P wpt1 → P wpt2) →
    (∀ U Hmeas, P (wpt_indicator U Hmeas)) →
    (∀ wpt1 wpt2, P wpt1 → P wpt2 → P (wpt_plus wpt1 wpt2)) →
    (∀ k wpt1, P wpt1 → P (wpt_scal k wpt1)) →
    (∀ wpt, P wpt).
  Proof.
    intros Hext Hind Hsum Hscal.
    intros wpt. eapply Hext.
    { symmetry. intros x. apply wpt_rep_indicator_scal_list. }
    generalize (wpt_rep_aux1 wpt) as HU.
    generalize (wpt_list wpt) as l.
    clear wpt. induction l as [| (r, U) l].
    - rewrite //=.
    - intros Hmeas.
      edestruct (wpt_indicator_scal_list_spec_cons r U l Hmeas) as (pf1&pf2&Heq).
      eapply Hext.
      { symmetry. intros x. apply Heq. }
      apply Hsum; eauto.
  Qed.

    
  Lemma wpt_pos_induction (P : weighted_partition → Prop):
    (∀ wpt1 wpt2, eq_fun (wpt_fun wpt1) (wpt_fun wpt2) → P wpt1 → P wpt2) →
    (∀ U Hmeas, P (wpt_indicator U Hmeas)) →
    (∀ wpt1 wpt2, (∀ x, 0 <= wpt_fun wpt1 x) → P wpt1 →
                  (∀ x, 0 <= wpt_fun wpt2 x) → P wpt2 →
                  P (wpt_plus wpt1 wpt2)) →
    (∀ k wpt1, 0 <= k → (∀ x, 0 <= wpt_fun wpt1 x) → P wpt1 → P (wpt_scal k wpt1)) →
    (∀ wpt, (∀ x, 0 <= wpt_fun wpt x) → P wpt).
  Proof.
    intros Hext Hind Hsum Hscal.
    intros wpt Hpos.
    assert (Heq: ∀ x, wpt_fun wpt x = wpt_fun (wpt_indicator_scal_list wpt (wpt_rep_aux1 wpt)) x).
    { intros x. apply wpt_rep_indicator_scal_list. }
    eapply Hext.
    { symmetry. intros x. apply Heq. }
    assert (Hpos_scal: ∀ x, 0 <= wpt_fun (wpt_indicator_scal_list wpt (wpt_rep_aux1 wpt)) x).
    { intros x.  rewrite -Heq. done. }
    move: Hpos_scal.
    generalize (wpt_rep_aux1 wpt) as HU.
    assert (Hpos_in: ∀ r U, In (r, U) wpt → (∃ x, U x) → 0 <= r).
    { intros r U Hin (x&HU). specialize (Hpos x); etransitivity; eauto.
      right. eapply wpt_fun_eq2; eauto. }
    generalize Hpos_in.
    generalize (wpt_list wpt) as l.
    clear Hpos Hpos_in Heq.
    clear wpt. induction l as [| (r, U) l].
    - rewrite //=.
    - intros Hpos Hmeas Hpos_val.
      edestruct (wpt_indicator_scal_list_spec_cons r U l Hmeas) as (pf1&pf2&Heq).
      eapply Hext.
      { symmetry. intros x. apply Heq. }
      assert (Hscal_val: ∀ x : A, 0 <= wpt_fun (wpt_scal r (wpt_indicator U pf1)) x).
      { intros. rewrite wpt_scal_spec wpt_indicator_spec.
        destruct excluded_middle_informative; last nra.
        rewrite Rmult_1_r. eapply Hpos; first by left. eauto. }
      assert (∀ x : A, 0 <= wpt_fun (wpt_indicator_scal_list l pf2) x).
      { intros x. rewrite wpt_indicator_scal_list_spec1.
        apply Rle_big0_In. intros (?&?) _ Hin.
        destruct excluded_middle_informative; last reflexivity.
        eapply Hpos; eauto. by right. }
      apply Hsum; eauto.
      * destruct (Classical_Prop.classic (∃ x, U x)) as [(x&HU)|Hnex].
        ** apply Hscal; eauto.
           *** eapply Hpos; first by left. eauto.
           *** intros x'. rewrite wpt_indicator_spec. destruct excluded_middle_informative; nra.
        ** eapply (Hext (wpt_indicator U pf1)); last apply Hind.
           intros x'. rewrite wpt_scal_spec ?wpt_indicator_spec.
           destruct excluded_middle_informative; try nra.
           exfalso. apply Hnex; eauto.
      * apply IHl.
        ** intros. eapply Hpos; eauto. by right.
        ** auto.
  Qed.

  Definition is_pos_integral (f: A → R) v :=
    measurable f F (borel R_UniformSpace) ∧
    is_lub (λ r, ∃ wpt, (∀ x, wpt_fun wpt x <= f x) ∧ wpt_integral wpt = r) v.

  Definition ex_pos_integral f := ∃ v, is_pos_integral f v.

  Definition Pos_integral (f : A → R) : R.
  Proof.
    destruct (excluded_middle_informative
                (bound (λ r, ∃ wpt, (∀ x, wpt_fun wpt x <= f x) ∧ wpt_integral wpt = r)))
      as [Hb|Hnb]; last exact 0.
    destruct (excluded_middle_informative
                (∃ x, (λ r, ∃ wpt, (∀ x, wpt_fun wpt x <= f x) ∧ wpt_integral wpt = r) x))
      as [Hex|Hnex]; last exact 0.
    exact (sval (completeness _ Hb Hex)).
  Defined.

  Lemma is_pos_integral_ext f1 f2 v:
    (∀ x, f1 x = f2 x) →
    is_pos_integral f1 v →
    is_pos_integral f2 v.
  Proof.
    intros H (Hmeas&Hlub).
    split.
    - eapply measurable_proper'.
      * intros x. rewrite -H. reflexivity.
      * reflexivity.
      * reflexivity.
      *  eauto.
    - split.
      * intros ? (wpt&?&?). apply Hlub; exists wpt; split_and!; eauto.
        intros. rewrite H. done.
      * intros b H'. apply Hlub. intros r (wpt&?&?). apply H'.
        exists wpt; split_and!; eauto.
        intros. rewrite -H. done.
  Qed.

  Global Instance is_pos_integral_Proper:
    Proper (pointwise_relation _ eq ==> eq ==> iff) (is_pos_integral).
  Proof.
    intros ?? Heq ?? ->. split; eapply is_pos_integral_ext; eauto.
  Qed.

  Lemma is_lub_inhabited E r: is_lub E r → (∃ x, E x).
  Proof.
    intros Hlub. apply Classical_Prop.NNPP => Hnex.
    destruct Hlub as [Hub Hlub]. eapply (Rle_not_gt r (r - 1)); last by nra.
    apply Hlub. intros x HEx. exfalso. apply Hnex; eauto.
  Qed.

  Lemma is_pos_integral_unique f v :
    is_pos_integral f v → Pos_integral f = v.
  Proof.
    rewrite /is_pos_integral/Pos_integral. intros [Hmeasure Hlub].
    destruct excluded_middle_informative as [Hb|Hnb] => //=; last first.
    { exfalso. apply Hnb. exists v. destruct Hlub; auto. }
    destruct excluded_middle_informative as [Hex|Hnex] => //=; last first.
    { exfalso. apply Hnex; eapply is_lub_inhabited; eauto. }
    eapply is_lub_u; eauto. destruct (completeness _) => //=.
  Qed.

  Lemma Pos_integral_correct f: ex_pos_integral f → is_pos_integral f (Pos_integral f).
  Proof.
    intros [v Hpos]. rewrite (is_pos_integral_unique f v) //=.
  Qed.

  (*
  Lemma Pos_integral_alt_case f:
    (∃ v, is_pos_integral f v ∧ Pos_integral f = v) ∨
    ((¬ ∃ v, is_pos_integral f v) ∧ Pos_integral f = 0).
  Proof.
    destruct (Classical_Prop.classic (∃ v, is_pos_integral f v)) as [(v&?)|Hne].
    - left. exists v; split; auto. apply is_pos_integral_unique; eauto.   
    - right. split; auto.
      rewrite /Pos_integral.
      destruct excluded_middle_informative as [Hb|Hnb]; auto.
      destruct excluded_middle_informative as [Hb'|Hnb]; auto.
      exfalso. apply Hne. eexists.
      split.
   *)

  Lemma is_lub_ext_u E E' x y:
    eq_prop E E' →
    is_lub E x → is_lub E' y → x = y.
  Proof.
    intros Hext (Hub1&Hlub1) (Hub2&Hlub2).
    apply Rle_antisym.
    - apply Hlub1. intros ? ?%Hext. apply Hub2. eauto.
    - apply Hlub2. intros ? ?%Hext. apply Hub1. eauto.
  Qed.

  Lemma Pos_integral_ext f1 f2 :
    (∀ x, f1 x = f2 x) →
    Pos_integral f1 = Pos_integral f2.
  Proof.
    intros Hext. rewrite /Pos_integral.
    destruct excluded_middle_informative as [Hb|Hnb]; last first.
    { symmetry.  destruct excluded_middle_informative as [Hb|]; auto.
      exfalso. apply Hnb.  destruct Hb as (v&Hv).
      exists v. intros r (wpt&?&<-).
      apply Hv. eexists; split; eauto. intros; rewrite -Hext. done.
    }
    destruct excluded_middle_informative as [Hinh|Hninh]; last first.
    { symmetry.
      destruct excluded_middle_informative as [Hb'|Hnb']; auto.
      destruct excluded_middle_informative as [Hinh'|]; auto.
      exfalso. apply Hninh.
      destruct Hinh' as (x&wpt&?&?). exists x, wpt; split; eauto.
      intros x'. rewrite Hext. done.
    }
    destruct excluded_middle_informative as [Hb'|Hnb]; last first.
    {
      exfalso. apply Hnb.  destruct Hb as (v&Hv).
      exists v. intros r (wpt&?&<-).
      apply Hv. eexists; split; eauto. intros; rewrite Hext. done.
    }
    destruct excluded_middle_informative as [Hinh'|Hninh]; last first.
    {
      exfalso. apply Hninh.
      destruct Hinh as (x&wpt&?&?). exists x, wpt; split; eauto.
      intros x'. rewrite -Hext. done.
    }
    destruct (completeness).
    destruct (completeness).
    rewrite //=.
    eapply is_lub_ext_u; eauto.
    intros x'; setoid_rewrite Hext; auto.
  Qed.

  Global Instance Pos_integral_Proper:
    Proper (pointwise_relation _ eq ==> eq) Pos_integral.
  Proof.
    intros ?? Heq. by apply Pos_integral_ext.
  Qed.

  Definition pos_int_simple_below (f: A → R) :=
    (λ r, ∃ wpt, (∀ x, wpt_fun wpt x <= f x) ∧ wpt_integral wpt = r).

  Lemma measurable_bounded_simple_ex_pos_integral (f: A → R):
    measurable f F (borel R_UniformSpace) →
    bound (pos_int_simple_below f) →
    (∃ r, pos_int_simple_below f r) →
    ex_pos_integral f.
  Proof.
    intros Hmeas Hbound Hex.
    exists (sval (completeness _ Hbound Hex)).
    rewrite /is_pos_integral; split; auto.
    destruct (completeness _); eauto.
  Qed.

  Lemma wpt_mono_le wpt_n:
    (∀ (x : A) (n : nat), wpt_fun (wpt_n n) x <= wpt_fun (wpt_n (S n)) x) →
    (∀ (x : A) (n n' : nat), (n <= n')%nat → wpt_fun (wpt_n n) x <= wpt_fun (wpt_n n') x).
  Proof.
    intros Hle x n n'. induction 1.
    - reflexivity.
    - etransitivity; eauto.
  Qed.

  Lemma wpt_mono_limit_ub wpt_n f:
    (∀ x, is_lim_seq (λ n, wpt_fun (wpt_n n) x) (f x : R)) →
    (∀ x, ∀ n, wpt_fun (wpt_n n) x <= wpt_fun (wpt_n (S n)) x) →
    ∀ x, ∀ n, wpt_fun (wpt_n n) x <= f x.
  Proof.
    intros Hlim Hmono x n.
    eapply is_lim_seq_incr_compare in Hlim; eauto.
  Qed.

  Lemma Pos_integral_ub wpt f:
    ex_pos_integral f →
    (∀ x, wpt_fun wpt x <= f x) →
    wpt_integral wpt <= Pos_integral f.
  Proof.
    intros Hex Hmono. destruct Hex as (v&His).
    erewrite is_pos_integral_unique; eauto.
    destruct His as (?&Hlub). apply Hlub; eexists; split; eauto; done.
  Qed.

  Lemma Pos_integral_lub f y:
    ex_pos_integral f →
    (∀ wpt, (∀ x, wpt_fun wpt x <= f x) → wpt_integral wpt <= y) →
    Pos_integral f <= y.
  Proof.
    intros Hex Hub.
    destruct Hex as (v&His). 
    erewrite is_pos_integral_unique; eauto.
    destruct His as (?&Hlub). apply Hlub.
    intros ? (?&?&<-). eauto.
  Qed.

  Lemma wpt_mono_lim_ex_eps wpt_n f:
    measurable f F (borel _) →
    (∀ x, is_lim_seq (λ n, wpt_fun (wpt_n n) x) (f x : R)) →
    (∀ x, ∀ n, wpt_fun (wpt_n n) x <= wpt_fun (wpt_n (S n)) x) →
    ∀ wpt, (∀ x, wpt_fun wpt x <= f x) →
           ∀ eps, 0 < eps → ∃ n, wpt_integral wpt <= wpt_integral (wpt_n n) + eps.
  Proof.
    intros Hmeas Hlim Hmono.
      intros wpt Hbound' eps0 Hpos0.
      set (μ' := Rmax 1 (μ (λ _, True))).
      assert (0 < μ').
      { rewrite /μ'. apply Rmax_case_strong; nra. }
      set (eps := eps0 / μ').
      assert (Hpos: 0 < eps).
      { rewrite /eps. apply Rdiv_lt_0_compat; nra. }
      assert (Hpos': 0 < eps / 2).
      { nra. }

      set (M := Rmax 1 (wpt_fun_ub (wpt_plus wpt (wpt_scal (-1) (wpt_n O))))).
      feed pose proof (convergence_pointwise_measure μ (λ n, wpt_fun (wpt_n n)) f) as Hconv; auto.
      { intros n. apply wpt_fun_measurable. } 

      specialize (Hconv {| cond_pos := Hpos'|}).
      destruct (Hconv (ball 0 (eps / (2 * M)))) as (n&Hnball).
      { unshelve (eexists).
        {  exists (eps /(2 * M)). abstract (apply Rdiv_lt_0_compat; eauto; rewrite /M;
                                            apply Rmax_case_strong; eauto; nra). }
        rewrite //=.
      }
      exists n.
      assert (Hmeasinv: F (λ x : A, Rabs (wpt_fun (wpt_n n) x - f x) > eps / 2)).
      { measurable.
        * apply wpt_fun_measurable.
        * apply open_ray_borel_gt.
      }
      feed pose proof (Hnball n) as Hball; first omega.
      replace eps0 with (eps0/2 + eps0/2) by field.
      assert (Hepsa: wpt_integral (wpt_scal (eps/2) (wpt_indicator _ (sigma_full _ _))) <= eps0 / 2).
      { rewrite wpt_integral_scal wpt_integral_indicator. rewrite /eps/μ'.
        apply Rmax_case_strong; auto; first nra. intros.
        field_simplify; nra. }
      assert (Hepsb: wpt_integral (wpt_scal M (wpt_indicator _ Hmeasinv)) <= eps0 / 2).
      { rewrite wpt_integral_scal wpt_integral_indicator.
        rewrite /ball//=/AbsRing_ball/abs//=/minus/plus/opp//= in Hball.
        rewrite Ropp_0 Rplus_0_r Rabs_right in Hball; last apply measure_nonneg.
        transitivity (eps / 2); auto.
        { move: Hball. rewrite /M. apply Rmax_case_strong; intros; try nra.
          apply Rlt_le in Hball.
          apply (Rmult_le_compat_r (wpt_fun_ub (wpt_plus wpt (wpt_scal (-1) (wpt_n O))))) in Hball;
            last nra.
          field_simplify in Hball; nra.
        }

        rewrite /eps/μ'. apply Rmax_case_strong; auto; try nra. clear -Hpos0; intros.
        apply Rdiv_le_compat_contra; try nra.
        left. apply Rdiv_lt_0_compat; nra.
        replace (eps0) with (eps0/1) at 2 by field.
        apply Rdiv_le_compat_contra; try nra.
      }
      etransitivity; last first.
      { apply Rplus_le_compat; first reflexivity.
        apply Rplus_le_compat; [ eapply Hepsa | eapply Hepsb ].
      }
      rewrite -?wpt_integral_plus.
      apply wpt_integral_mono.
      intros x. rewrite ?wpt_plus_spec ?wpt_scal_spec ?wpt_indicator_spec.
      destruct (excluded_middle_informative) => //=.
      destruct (excluded_middle_informative) as [?|Hn0].
      * intros.
        feed pose proof (wpt_mono_le _ Hmono x O n).
        { omega. }
        rewrite /M. specialize (wpt_fun_ub_spec (wpt_plus wpt (wpt_scal (-1) (wpt_n O))) x).
        rewrite ?wpt_plus_spec ?wpt_scal_spec => Hle'.
        apply Rmax_case_strong; nra.
      * transitivity (f x); first by eauto.
        apply Rnot_gt_le in Hn0. move: Hn0.
        apply Rabs_case; nra.
  Qed.

  Lemma is_pos_integral_mct_wpt_ex wpt_n f:
    measurable f F (borel _) →
    (∀ x, is_lim_seq (λ n, wpt_fun (wpt_n n) x) (f x : R)) →
    (∀ x, ∀ n, wpt_fun (wpt_n n) x <= wpt_fun (wpt_n (S n)) x) →
    bound (λ r, ∃ n, wpt_integral (wpt_n n) = r) →
    ex_pos_integral f ∧ 
    is_lim_seq (λ n, wpt_integral (wpt_n n)) (Pos_integral f). 
  Proof.
    intros Hmeas Hlim Hmono Hbounded.
    destruct Hbounded as (r&Hbounded).
    assert (ex_finite_lim_seq ((λ n, wpt_integral (wpt_n n)))) as Hex_fin.
    { eapply ex_finite_lim_seq_incr.
      - intros. apply wpt_integral_mono; eauto.
      - intros n. eapply Hbounded. eauto.
    }
    feed pose proof (wpt_mono_lim_ex_eps wpt_n f) as Hex_eps; auto.
    assert (Hex_pos_int: ex_pos_integral f).
    {
      apply measurable_bounded_simple_ex_pos_integral; auto.
      * exists r. intros ? (wpt&Hbound'&<-).
        apply le_epsilon => eps0 Hpos0.
        edestruct Hex_eps.
        { eauto. }
        { eauto. } 
        etransitivity; first eauto.
        apply Rplus_le_compat; eauto.
        reflexivity.
      * exists (wpt_integral (wpt_n O)).
        rewrite /pos_int_simple_below. eexists; split; eauto.
        intros.
        apply wpt_mono_limit_ub; eauto.
    }
    split; auto.
    apply ex_finite_lim_seq_correct in Hex_fin as (Hex&Hfin).
    apply Lim_seq_correct'; eauto.
    apply Rbar_le_antisym.
    { rewrite -Lim_seq_const. apply Lim_seq_le_loc. exists O => ??.
      eapply Pos_integral_ub; eauto. intros.
      apply wpt_mono_limit_ub; eauto. }
    rewrite //=.
    apply is_finite_correct in Hfin as (y&Heq). rewrite Heq.
    apply Pos_integral_lub; auto.
    intros wpt' Hle_wpt'.
    set (wpt'_n := λ n, wpt_min wpt' (wpt_n n)).
    assert (Hlim_wpt': ∀ x, is_lim_seq (λ n, wpt_fun (wpt'_n n) x) (wpt_fun wpt' x)).
    { intros x.
      assert (wpt_fun wpt' x = Rmin (wpt_fun wpt' x) (f x)) as ->.
      { rewrite Rmin_left; auto. }
      eapply (is_lim_seq_ext).
      { intros n.  rewrite /wpt'_n wpt_min_spec. done. }
      eapply is_lim_seq_continuous; eauto.
      apply continuity_pt_filterlim.
      apply: continuous_Rmin_l.
    }
    feed pose proof (wpt_integral_mct wpt'_n wpt'); eauto.
    { intros x n. rewrite ?wpt_min_spec.
      apply Rle_min_compat_l; eauto.
    }
    cut (Rbar_le (Lim_seq (λ n, wpt_integral (wpt'_n n))) (Lim_seq (λ n, wpt_integral (wpt_n n)))).
    { rewrite /Rbar_le Heq.
      erewrite is_lim_seq_unique; eauto.
      rewrite //=.
    }
    apply Lim_seq_le_loc. exists O.
    intros. apply wpt_integral_mono => ?. rewrite wpt_min_spec.
    apply Rmin_r.
  Qed.

  Lemma is_pos_integral_mct_wpt wpt_n f (v: R):
    measurable f F (borel _) →
    (∀ x, is_lim_seq (λ n, wpt_fun (wpt_n n) x) (f x : R)) →
    (∀ x, ∀ n, wpt_fun (wpt_n n) x <= wpt_fun (wpt_n (S n)) x) →
    is_lim_seq (λ n, wpt_integral (wpt_n n)) v →
    is_pos_integral f v.
  Proof.
    intros Hmeas Hlim1 ? Hlim2.
    assert (Hbound: ∀ n, wpt_integral (wpt_n n) <= v). 
    { intros n.
      eapply (is_lim_seq_incr_compare (λ n, wpt_integral (wpt_n n)) v); eauto.
      intros. apply wpt_integral_mono; eauto. }
    edestruct is_pos_integral_mct_wpt_ex; eauto.
    - exists v. intros ? (n&<-). eauto.
    - split; eauto. split.
      * intros ? (wpt&?&<-).
        apply le_epsilon => eps Hpos.
        edestruct (wpt_mono_lim_ex_eps) as (n&?); eauto.
        etransitivity; eauto. specialize (Hbound n). nra.
      * intros v' Hub.
        eapply (is_lim_seq_le (λ n, wpt_integral (wpt_n n)) (λ _, v') v v').
        { intros. eapply Hub; eexists; split; eauto. intros. apply wpt_mono_limit_ub; eauto. }
        { eauto. }
        { apply is_lim_seq_const. }
  Qed.

  Lemma not_in_list l x:
    (∀ (r : R) (U : A → Prop), In (r, U) l → ¬ U x) → ¬ (union_list (map snd l)) x.
  Proof.
    intros Hnin Hin. apply union_list_inv in Hin as (U&Hin&HU).
    apply in_map_iff in Hin as ((?&?)&?&?); subst.
    eapply Hnin; eauto.
  Qed.

  Lemma pow_2_increasing: ∀ n, (n <= 2^n)%nat.
  Proof.
    cut (∀ n, (n <= 2^n) ∧ (1 <= 2^n))%nat.
    { intros H n. destruct (H n); eauto. }
    intros n. induction n => //=; first omega.
    split; omega.
  Qed.

  Lemma pow_2_pos: ∀ n, (0 < 2^n)%nat.
  Proof.
    induction n => //=; omega.
  Qed.
  
  Lemma wpt_approx_measurable1 f:
    (∀ x, 0 <= f x) →
    measurable f F (borel _) →
    ∃ wpt_n, (∀ n x, wpt_fun (wpt_n n) x <= wpt_fun (wpt_n (S n)) x) ∧
             (∀ x, is_lim_seq (λ n, wpt_fun (wpt_n n) x) (f x)) ∧
             (∀ n x, 0 <= wpt_fun (wpt_n n) x).
  Proof.
    intros Hpos Hmeas.
    set (Ank := λ n k, fun_inv f (λ x, (INR k) / 2^n <= x) ∩ fun_inv f (λ x, x < INR (S k) / 2^n)).
    assert (∀ n k, F (Ank n k)).
    { intros n k. apply sigma_closed_pair_intersect.
      - apply Hmeas. apply closed_ray_borel_ge.
      - apply Hmeas. apply open_ray_borel_lt. 
    }
    set (ln := λ n n', nat_rect (λ _, list (R * (A → Prop)))
                             (nil (* (INR O / 2^n, Ank n O) :: nil) *))
                             (λ k l, ((INR k / 2^n, Ank n k) :: l)) n').
    assert (Hln: ∀ n n' r U, In (r, U) (ln n n') → F U).
    { rewrite /ln. intros n n'. revert n. induction n' => n r U. rewrite //=.
      * rewrite //=. inversion 1 as [Heq|?].
        ** inversion Heq; subst. eauto.
        ** eauto.
    }
    set (fn := λ n, (wpt_indicator_scal_list (ln n (n * 2^n)%nat) (Hln n (n * 2^n)%nat))).
    set (An_compl := λ n, compl (union_list (map snd (ln n (n * 2^n)%nat)))).
    assert (Hmeas_gn: ∀ n, F (An_compl n)).
    { intros n. apply sigma_closed_complements.
      apply sigma_closed_list_union. intros U ((?&?)&?&?)%in_map_iff.
      subst => //=. eapply Hln; eauto. }
    set (gn := λ n, wpt_scal (INR n) (wpt_indicator _ (Hmeas_gn n))).
    assert (Hln_in: ∀ n n' r P, In (r, P) (ln n n') →
                                ∃ k, P = Ank n k ∧ r = (INR  k / 2^n) ∧ (k < n')%nat).
    { induction n' => //=.
      * intros r P. inversion 1 as [Heq|]; eauto.
        ** inversion Heq; subst. eexists; split_and!; auto. 
        ** edestruct (IHn') as (k&?&?&?); first eauto.
           exists k; split_and!; eauto.
    }
    assert (Hln_intro: ∀ n n' k, (k < n')%nat → In (Ank n k) (map snd (ln n n'))).
    { 
      intros n n'. induction 1.
      - rewrite //=. by left.
      - rewrite //=.  by right.
    }
    assert (Hln_disj: ∀ n n', ## map snd (ln n n')).
    { intros n n'. revert n. induction n' => n //=.
      * econstructor => //=.
      * econstructor; eauto. intros x (Hin1&Hin2).
        apply union_list_inv in Hin2 as (U&Hin&HU).
        apply in_map_iff in Hin as ((?&?)&Heq&Hin).
        apply Hln_in in Hin as (k&?&?&Hlt); subst.
        rewrite //= in  HU.
        rewrite /Ank/fun_inv ?S_INR in Hin1 HU.
        destruct Hin1, HU.
        specialize (Hpos x).
        assert (Hdiff: INR n' - INR k < 1). nra.
        assert (n' = k).
        { eapply INR_diff_lt_1_eq; split; try nra.
          apply lt_INR in Hlt. nra.
        }
        omega.
    }
    assert (Hpown: ∀ n, 2^ n  > 0).
    { clear. induction n => //=; nra. }
    set (fgn := λ n, wpt_plus (fn n) (gn n)). 
    assert (Hfgn_val :
              ∀ x (n: nat), ((f x >= INR n) ∧ wpt_fun (fgn n) x = INR n) ∨
                   (∃ k, (k < n * 2^n)%nat ∧ INR k / 2^n <= f x < INR (S k) / 2^n ∧
                         wpt_fun (fgn n) x = INR k /2^n)).
    {
      intros x n. destruct (Rge_dec (f x) (INR n)) as [Hge|Hnge].
      - left.  split; auto. rewrite ?wpt_plus_spec.
        edestruct (wpt_indicator_scal_list_spec2 _ (Hln n (n * 2^n)%nat) (Hln_disj _ _) x)
                as [(Hnin&Heq0)|(r&U&Hin&HU&Heq)].
        * rewrite Heq0 Rplus_0_l wpt_scal_spec wpt_indicator_spec.
          destruct (excluded_middle_informative) as [?|Hneg]; first field.
          exfalso. apply Hneg. apply not_in_list in Hnin.
          apply Hnin.
        * edestruct (Hln_in) as (k&Heq'&Hr&Hlt); eauto.
          subst. exfalso. destruct HU as (Hrange1&Hrange2).
          rewrite S_INR /fun_inv//= in Hrange1 Hrange2.
          assert (Haux: f x < INR (n * 2^n) / 2^n).
          { eapply Rlt_le_trans; eauto.
            apply Rle_div_l; auto. specialize (Hpown n). field_simplify; last nra.
            rewrite /Rdiv Rinv_1 ?Rmult_1_r.
            rewrite -S_INR. apply le_INR.
            omega.
          }
          rewrite mult_INR in Haux.
          replace (INR (2^n)) with (2^n) in Haux; last first.
          { rewrite pow_INR; f_equal. } 
          specialize (Hpown n).
          field_simplify in Haux; nra.
      - right.
        edestruct (archimed_pos (f x * (2^n))) as (k&?&?).
        { apply Rmult_le_0_compat; auto. specialize (Hpown n). nra. }
        exists k. specialize (Hpown n).
        split_and!.
        * apply INR_lt. eapply Rle_lt_trans; eauto. 
          rewrite mult_INR pow_INR. replace (INR 2) with 2 by auto.
          apply Rmult_lt_compat_r; nra.
        * apply (Rmult_le_reg_r (2^n)); try nra. 
          field_simplify; nra.
        * apply (Rmult_lt_reg_r (2^n)); try nra. 
          field_simplify; nra.
        * rewrite wpt_plus_spec wpt_scal_spec wpt_indicator_spec.
          assert (Ank n k x).
          { 
            rewrite /Ank/fun_inv; split.
            ** apply (Rmult_le_reg_r (2^n)); try nra. 
               field_simplify; nra.
            ** apply (Rmult_lt_reg_r (2^n)); try nra. 
               field_simplify; nra.
          }
          assert (In (Ank n k) (map snd (ln n (n * 2 ^ n)%nat))).
          { 
            apply Hln_intro.
            apply INR_lt. rewrite mult_INR pow_INR.
            replace (INR 2) with 2; auto.
            nra.
          }
          destruct excluded_middle_informative as [Hcompl|Hncompl].
          { exfalso. apply Hcompl. apply (union_list_intro _ _ (Ank n k)).
            ** auto.
            ** rewrite /Ank/fun_inv; split.
               *** apply (Rmult_le_reg_r (2^n)); try nra. 
                   field_simplify; nra.
               *** apply (Rmult_lt_reg_r (2^n)); try nra. 
                   field_simplify; nra.
          }
          rewrite Rmult_0_r Rplus_0_r.
          edestruct (wpt_indicator_scal_list_spec2 _ (Hln n (n * 2^n)%nat) (Hln_disj _ _) x)
            as [(Hnin&Heq0)|(r&U&Hin&HU&Heq)].
          ** apply not_in_list in Hnin. exfalso. rewrite /An_compl in Hncompl.
             auto.
          ** rewrite Heq. apply Hln_in in Hin as (k'&?&?&?). subst.
             destruct HU as [Hrange1 Hrange2]. rewrite /fun_inv in Hrange1 Hrange2.
             apply (Rmult_le_compat_r (2^n)) in Hrange1; try nra. 
             apply (Rmult_lt_compat_r (2^n)) in Hrange2; try nra. 
             rewrite S_INR in H1.
             rewrite S_INR in Hrange2.
             field_simplify in Hrange1; try nra.
             field_simplify in Hrange2; try nra.
             f_equal. destruct (Rle_dec (INR k) (INR k')); auto.
             *** assert (INR k' - INR k < 1) by nra.
                 f_equal. apply INR_diff_lt_1_eq; split; try nra.
             *** assert (INR k - INR k' < 1) by nra.
                 symmetry. f_equal. apply INR_diff_lt_1_eq; split; try nra.
    }
    exists (fgn); split_and!.
    * intros n x.
      destruct (Hfgn_val x n) as [(Hc1&->)|Hc2];
        destruct (Hfgn_val x (S n)) as [(Hc1'&->)|Hc2'];
        try nra.
      ** rewrite S_INR. nra.
      ** destruct Hc2' as (k&Hlt&(?&?)&->).
         specialize (Hpown (S n)).
         *** apply (Rmult_le_reg_r (2^ (S n))); eauto.
             field_simplify; last nra.
             rewrite /Rdiv Rinv_1 ?Rmult_1_r.
             replace 2 with (INR 2) by auto.
             rewrite -pow_INR -mult_INR.
             assert (Hineq: INR n < INR (S k) / 2 ^ (S n)) by nra.
             apply (Rmult_lt_compat_r (2^(S n))) in Hineq; last nra.
             field_simplify in Hineq; last nra.
             rewrite /Rdiv Rinv_1 ?Rmult_1_r in Hineq.
             replace 2 with (INR 2) in Hineq by auto.
             rewrite -pow_INR -mult_INR in Hineq.
             apply le_INR. apply INR_lt in Hineq. omega.
      ** destruct Hc2 as (k&Hr1&(Hr2a&Hr2b)&Heq).
         rewrite Heq. specialize (Hpown n).
         apply (Rmult_le_reg_r (2^n)); first nra.
         field_simplify; last nra.
         rewrite /Rdiv Rinv_1 ?Rmult_1_r.
         replace 2 with (INR 2) by auto.
         rewrite -pow_INR -mult_INR.
         apply le_INR. rewrite mult_comm.
         transitivity (n * 2^ n)%nat; first omega.
         apply mult_le_compat_r. auto.
      ** destruct Hc2 as (k&Hr1&(Hr2a&Hr2b)&Heq).
         destruct Hc2' as (k'&Hr1'&(Hr2a'&Hr2b')&Heq').
         rewrite Heq Heq'.
         assert (Hineq: INR k / 2^ n < INR (S k') / 2^ S n) by nra.
         generalize (Hpown (S n)).
         generalize (Hpown (n)); intros.
         apply (Rmult_lt_compat_r (2^(S n))) in Hineq; last nra.
         rewrite S_INR in Hineq.
         rewrite //= in Hineq.
         field_simplify in Hineq; try nra.
         rewrite -S_INR /Rdiv Rinv_1 ?Rmult_1_r in Hineq.
         replace 2 with (INR 2) in Hineq by auto. rewrite -mult_INR in Hineq.
         apply INR_lt in Hineq.
         apply (Rmult_le_reg_r (2^(S n))); first nra.
         rewrite //=.
         field_simplify; try nra.
         rewrite /Rdiv Rinv_1 ?Rmult_1_r.
         replace 2 with (INR 2) by auto. rewrite -mult_INR.
         apply le_INR. omega.
    * intros x. intros P (eps&HP).
      destruct (archimed_pos (f x)) as (n1&?&?); eauto.
      destruct (archimed_cor1 eps) as (n2&?&?); try (destruct eps; eauto; done).
      set (N := max (S n1) (S n2)).
      assert (/ INR (2^N) < eps).
      { eapply Rle_lt_trans; last eauto.
        apply Rinv_le_contravar.
        { by apply pos_INR'. } 
        apply le_INR.
        transitivity (2 ^ n2)%nat; first apply pow_2_increasing.
        apply Nat.pow_le_mono_r; first omega.
        rewrite /N. etransitivity; last eapply Nat.le_max_r; omega.
      }
      exists N.
      intros n Hle. apply HP.
      edestruct (Hfgn_val x n) as [(Hfalse&Heq)|Hcase].
      { exfalso. assert (Hbad: INR n < INR (S n1)) by nra.
        apply INR_lt in Hbad. specialize (Nat.le_max_l (S n1) (S n2)).
        intros. rewrite /N in Hbad Hle. omega.
      }
      destruct Hcase as (k&Hr1&(Hr2a&Hr2b)&Heq).
      rewrite /ball//=/AbsRing_ball/abs//=/minus/plus/opp//=.
      rewrite Rabs_left1; last by nra.
      eapply (Rle_lt_trans _ (1 / 2^n)).
      { rewrite S_INR in Hr2b. nra. }
      eapply (Rle_lt_trans _ (1 / INR (2^ N))); last nra.
      apply Rdiv_le_compat_contra; try nra.
      - replace 0 with (INR 0) by auto.
        apply lt_INR, pow_2_pos.
      - replace 2 with (INR 2) by auto.
        rewrite -pow_INR. apply le_INR.
        apply Nat.pow_le_mono_r; first omega.
        auto.
    * intros n x. edestruct (Hfgn_val x n) as [(Hpos1&?)|Hc2]; eauto.
      ** specialize (pos_INR n). nra.
      ** destruct Hc2 as (k&?&?&Heq).
         rewrite Heq. apply Rdiv_le_0_compat; first apply pos_INR.
         clear. induction n => //=; first nra. nra.
  Qed.

  Lemma wpt_approx_measurable f:
    (∀ x, 0 <= f x) →
    measurable f F (borel _) →
    ∃ wpt_n, (∀ n x, wpt_fun (wpt_n n) x <= wpt_fun (wpt_n (S n)) x) ∧
             (∀ x, is_lim_seq (λ n, wpt_fun (wpt_n n) x) (f x)) ∧
             (∀ n x, wpt_fun (wpt_n n) x <= f x) ∧
             (∀ n x, 0 <= wpt_fun (wpt_n n) x).
  Proof.
    intros ??. edestruct (wpt_approx_measurable1 f) as (wpt_n&?&Hlim&?); eauto.
    exists wpt_n; split_and!; eauto.
    intros. eapply is_lim_seq_incr_compare in Hlim; eauto.
  Qed.

  Lemma is_pos_integral_measurable f v:
    is_pos_integral f v → measurable f F (borel R_UniformSpace).
  Proof. destruct 1; eauto. Qed.

  Hint Resolve is_pos_integral_measurable.

  Global Instance is_lim_seq_Proper:
    Proper (pointwise_relation _ eq ==> eq ==> iff) (is_lim_seq).
  Proof.
    intros ?? Heq ?? ->. split; eapply is_lim_seq_ext; eauto.
  Qed.

  Lemma is_lim_seq_scal_l' (u : nat → R) (a : R) (lu : R):
    is_lim_seq u lu → is_lim_seq (λ n : nat, a * u n) (a * lu).
  Proof. intros H. eapply (is_lim_seq_scal_l _ a) in H => //=. Qed.

  Lemma is_pos_integral_ub f v wpt:
    is_pos_integral f v →
    (∀ x, wpt_fun wpt x <=  f x) → wpt_integral wpt <= v.
  Proof.
    intros (Hmeas&Hub) Hle. apply Hub. eexists; split; eauto.
  Qed.

  Lemma is_pos_integral_lub f v1 v2:
    is_pos_integral f v1 →
    (∀ wpt, (∀ x, wpt_fun wpt x <= f x) → wpt_integral wpt <= v2) → v1 <= v2.
  Proof.
    intros (Hmeas&Hub) Hle. apply Hub.
    intros r (wpt&?&<-). eapply Hle; eauto.
  Qed.

  Lemma is_pos_integral_mct_wpt' wpt_n f (v: R):
    measurable f F (borel _) →
    (∀ x, is_lim_seq (λ n, wpt_fun (wpt_n n) x) (f x : R)) →
    (∀ x, ∀ n, wpt_fun (wpt_n n) x <= wpt_fun (wpt_n (S n)) x) →
    is_pos_integral f v →
    is_lim_seq (λ n, wpt_integral (wpt_n n)) v.
  Proof.
    intros. cut (Pos_integral f = v).
    { intros <-. eapply is_pos_integral_mct_wpt_ex; eauto.
      exists (Pos_integral f).
      intros r (n&<-). eapply is_pos_integral_ub; eauto.
      intros; apply wpt_mono_limit_ub; eauto.
    }
    apply is_pos_integral_unique; eauto.
  Qed.
  
  Lemma is_pos_integral_scal k f v:
    0 <= k →
    (∀ x, 0 <= f x) →
    is_pos_integral f v → is_pos_integral (λ x, k * f x) (k * v).
  Proof.
    intros Hpos1 Hpos2 Hlim.
    edestruct (wpt_approx_measurable) as (wpt&Hincr&Hlim'&Hbound); eauto.
    eapply (is_pos_integral_mct_wpt (λ n, wpt_scal k (wpt n)) (λ x, k * f x)).
    { apply measurable_scal; eauto. }
    { intros. rewrite //=. setoid_rewrite wpt_scal_spec.
      apply: is_lim_seq_scal_l'. auto. }
    { intros x n. rewrite ?wpt_scal_spec. apply Rmult_le_compat_l; eauto. }
    { setoid_rewrite wpt_integral_scal.
      apply: is_lim_seq_scal_l'. eapply is_pos_integral_mct_wpt'; eauto. }
  Qed.
      
  Lemma is_pos_integral_plus f1 v1 f2 v2:
    (∀ x, 0 <= f1 x) →
    (∀ x, 0 <= f2 x) →
    is_pos_integral f1 v1 →
    is_pos_integral f2 v2 →
    is_pos_integral (λ x, f1 x + f2 x) (v1 + v2).
  Proof.
    intros Hpos Hpos2 Hint1 Hint2.
    edestruct (wpt_approx_measurable f1) as (wpt1&Hincr1&Hlim1&Hbound1); eauto.
    edestruct (wpt_approx_measurable f2) as (wpt2&Hincr2&Hlim2&Hbound2); eauto.
    eapply (is_pos_integral_mct_wpt (λ n, wpt_plus (wpt1 n) (wpt2 n)) (λ x, f1 x + f2 x)).
    { apply measurable_plus; eauto. }
    { intros.  setoid_rewrite wpt_plus_spec.
      apply: is_lim_seq_plus; auto. rewrite //=. }
    { intros x n. rewrite ?wpt_plus_spec. apply Rplus_le_compat; eauto. }
    { setoid_rewrite wpt_integral_plus.
      apply: is_lim_seq_plus.
      - eapply (is_pos_integral_mct_wpt' _ f1 v1); eauto.
      - eapply (is_pos_integral_mct_wpt' _ f2 v2); eauto.
      - rewrite /is_Rbar_plus//=.
    }
  Qed.

  Lemma is_pos_integral_mono f1 f2 v1 v2:
    (∀ x, f1 x <= f2 x) →
    is_pos_integral f1 v1 →
    is_pos_integral f2 v2 →
    v1 <= v2.
  Proof.
    intros Hb Hpos1 Hpos2.
    eapply is_pos_integral_lub; eauto.
    intros wpt Hle. eapply is_pos_integral_ub; eauto.
    intros x. specialize (Hb x). specialize (Hle x). nra.
  Qed.

  Lemma all_pos_int_simple_below_0 f1:
    (∀ x, 0 <= f1 x) →
    pos_int_simple_below f1 0.
  Proof.
    intros Hpos.
    exists (wpt_indicator ∅ (sigma_empty_set _)).
    split.
    - intros. rewrite wpt_indicator_spec //=.
      destruct excluded_middle_informative => //=.
    - rewrite wpt_integral_indicator measure_empty //.
  Qed.

  Lemma is_pos_integral_mono_ex f1 f2 v2:
    (∀ x, 0 <= f1 x) →
    (∀ x, f1 x <= f2 x) →
    measurable f1 F (borel _) →
    is_pos_integral f2 v2 →
    ex_pos_integral f1 ∧ Pos_integral f1 <= v2.
  Proof.
    intros Hpos Hb Hmeas Hpos2.
    assert (Hex: ex_pos_integral f1).
    { apply measurable_bounded_simple_ex_pos_integral; auto.
      - exists v2. intros ? (wpt&Hb1&Heq). rewrite -Heq.
        eapply is_pos_integral_ub; eauto. intros a.
        specialize (Hb a). specialize (Hb1 a).
        nra.
      - exists 0. apply all_pos_int_simple_below_0; auto.
    }
    split; auto.
    eapply is_pos_integral_mono; eauto.
    apply Pos_integral_correct. done.
  Qed.

  Definition is_integral (f: A → R) v :=
    measurable f F (borel R_UniformSpace) ∧
    ∃ v1 v2, is_pos_integral (λ x, Rmax (f x) 0) v1 ∧
             is_pos_integral (λ x, Rmax (- f x) 0) v2 ∧
             v = v1 - v2.

  Definition ex_integral (f: A → R) :=
    ∃ v, is_integral f v.

  Definition Integral (f : A → R) : R :=
    Pos_integral (λ x, Rmax (f x) 0) - Pos_integral (λ x, Rmax (- f x) 0).

  Lemma is_integral_unique f v :
    is_integral f v → Integral f = v.
  Proof.
    rewrite /is_integral. intros (Hmeas&v1&v2&?&?&Heq).
    rewrite /Integral.
    erewrite is_pos_integral_unique; eauto.
    erewrite is_pos_integral_unique; eauto.
  Qed.

  Lemma Integral_correct f: ex_integral f → is_integral f (Integral f).
  Proof.
    intros [v Hpos]. rewrite (is_integral_unique f v) //=.
  Qed.

  Lemma is_pos_integral_diff f1 f2 g1 g2 v1 v2 v1' v2':
    (∀ x, 0 <= f1 x) →
    (∀ x, 0 <= f2 x) →
    (∀ x, 0 <= g1 x) →
    (∀ x, 0 <= g2 x) →
    (∀ x, f1 x - f2 x = g1 x - g2 x) →
    is_pos_integral f1 v1 →
    is_pos_integral f2 v2 →
    is_pos_integral g1 v1' →
    is_pos_integral g2 v2' →
    v1 - v2 = v1' - v2'.
  Proof.
    intros ???? Hdiff Hi1 Hi2 Hi1' Hi2'.
    assert (Hsum: ∀ x, f1 x + g2 x = g1 x + f2 x).
    { intros x. specialize (Hdiff x). nra. }
    cut (v1 + v2' = v1' + v2); first by nra.
    feed pose proof (is_pos_integral_plus f1 v1 g2 v2'); eauto.
    feed pose proof (is_pos_integral_plus g1 v1' f2 v2); eauto.
    etransitivity; last apply is_pos_integral_unique; eauto.
    symmetry. apply is_pos_integral_unique.
    setoid_rewrite <-Hsum. done.
  Qed.

  Lemma is_integral_scal k f v:
    is_integral f v → is_integral (λ x, k * f x) (k * v).
  Proof.
    destruct (Rle_dec 0 k).
    - intros (Hmeas&v1&v2&Hpos1&Hpos2&Hdiff). 
      split.
      { by apply measurable_scal. }
      exists (k * v1), (k * v2).
      split_and!.
      * eapply is_pos_integral_ext; last first.
        { eapply is_pos_integral_scal; auto; last eauto.
          intros x => //=. apply Rmax_r. }
        intros x => //=.
        replace 0 with (k * 0) at 2 by field.
        rewrite Rmult_comm Rmax_mult; auto.
        f_equal; nra.
      * eapply is_pos_integral_ext; last first.
        { eapply is_pos_integral_scal; auto; last apply Hpos2.
          intros x => //=. apply Rmax_r. }
        intros x => //=.
        replace 0 with (k * 0) at 2 by field.
        rewrite Rmult_comm Rmax_mult; auto.
        f_equal; nra.
      * nra. 
    - intros (Hmeas&v1&v2&Hpos1&Hpos2&Hdiff). 
      split.
      { by apply measurable_scal. }
      exists (-k * v2), (-k * v1).
      split_and!.
      * eapply is_pos_integral_ext; last first.
        { eapply is_pos_integral_scal; auto; last eauto; try nra.
          intros x => //=. apply Rmax_r. }
        intros x => //=.
        replace 0 with (- k * 0) at 2 by field.
        rewrite Rmult_comm Rmax_mult; auto; last nra.
        f_equal; nra.
      * eapply is_pos_integral_ext; last first.
        { eapply is_pos_integral_scal; auto; last eauto; try nra.
          intros x => //=. apply Rmax_r. }
        intros x => //=.
        replace 0 with (- k * 0) at 2 by field.
        rewrite Rmult_comm Rmax_mult; auto; last nra.
        f_equal; nra.
      * nra.
  Qed.

  Lemma ex_integral_scal k f:
    ex_integral f →
    ex_integral (λ x, k * f x). 
  Proof.
    intros (v1&?); eexists; eapply is_integral_scal; eauto.
  Qed.

  Lemma Integral_scal k f:
    ex_integral f →
    Integral (λ x, k * f x) = k * Integral f.
  Proof.
    intros Hex.
    apply is_integral_unique.
    apply is_integral_scal; apply Integral_correct; eauto.
  Qed.

  Lemma is_integral_plus f1 v1 f2 v2:
    is_integral f1 v1 →
    is_integral f2 v2 →
    is_integral (λ x, f1 x + f2 x) (v1 + v2).
  Proof.
    intros Hi1 Hi2.
    destruct Hi1 as (Hmeas1&v1p&v1n&Hi1p&Hi1n&Hdiff1).
    destruct Hi2 as (Hmeas2&v2p&v2n&Hi2p&Hi2n&Hdiff2).
    split.
    - apply measurable_plus; auto. 
    - exists (Pos_integral (λ x, (Rmax (f1 x + f2 x) 0))).
      exists (Pos_integral (λ x, (Rmax (-(f1 x + f2 x)) 0))).
      assert (ex_pos_integral (λ x, (Rmax (f1 x + f2 x) 0))).
      { 
        edestruct (is_pos_integral_mono_ex
                     (λ x, Rmax (f1 x + f2 x) 0)
                     (λ x, Rmax (f1 x) 0 + Rmax (f2 x) 0)) as (Hex&?); eauto.
        ** intros x => //=. apply Rmax_r.
        ** intros x => //=. repeat apply Rmax_case_strong; nra.
        ** apply measurable_Rmax.
           *** apply measurable_plus; auto.
           *** eapply measurable_const. 
        ** apply is_pos_integral_plus; eauto using Rmax_r.
      }
      assert (ex_pos_integral (λ x, (Rmax (- (f1 x + f2 x)) 0))).
      {
        edestruct (is_pos_integral_mono_ex
                     (λ x, Rmax (- (f1 x + f2 x)) 0)
                     (λ x, Rmax (- f1 x) 0 + Rmax (- f2 x) 0)) as (Hex&?); eauto.
        ** intros x => //=. apply Rmax_r.
        ** intros x => //=. repeat apply Rmax_case_strong; nra.
        ** apply measurable_Rmax.
           *** eapply measurable_opp. apply measurable_plus; auto.
           *** eapply measurable_const. 
        ** apply is_pos_integral_plus; eauto using Rmax_r.
      }
      split_and!.
      * apply Pos_integral_correct; eauto.
      * apply Pos_integral_correct; eauto.
      * replace (v1 + v2) with ((v1p + v2p) - (v1n + v2n)) by nra.
        eapply (is_pos_integral_diff (λ x, Rmax (f1 x) 0 + Rmax (f2 x) 0)
                                     (λ x, Rmax (- f1 x) 0 + Rmax (- f2 x) 0));
          try (eapply Pos_integral_correct; eauto);
          try (intros x; eapply Rmax_r; eauto).
        ** intros; repeat apply Rmax_case_strong; nra.
        ** intros; repeat apply Rmax_case_strong; nra.
        ** intros; repeat apply Rmax_case_strong; nra.
        ** apply is_pos_integral_plus; auto using Rmax_r.
        ** apply is_pos_integral_plus; auto using Rmax_r.
  Qed.

  Lemma ex_integral_plus f1 f2:
    ex_integral f1 →
    ex_integral f2 →
    ex_integral (λ x, f1 x + f2 x). 
  Proof.
    intros (v1&?) (v2&?).
    eexists; eauto using is_integral_plus.
  Qed.

  Lemma Integral_plus f1 f2:
    ex_integral f1 →
    ex_integral f2 →
    Integral (λ x, f1 x + f2 x) = Integral f1 + Integral f2.
  Proof.
    intros Hex1 Hex2.
    apply is_integral_unique.
    apply is_integral_plus; apply Integral_correct; eauto.
  Qed.


  Lemma is_integral_ext f1 f2 v:
    (∀ x, f1 x = f2 x) →
    is_integral f1 v →
    is_integral f2 v.
  Proof.
    intros Heq (Hmeas&Hp).
    split.
    - eapply measurable_proper'.
      * intros x. rewrite -Heq. reflexivity.
      * reflexivity.
      * reflexivity.
      * eauto.
    - destruct Hp as (v1&v2&?&?&?).
      exists v1, v2; split_and!; eauto.
      * setoid_rewrite <-Heq. auto.
      * setoid_rewrite <-Heq. auto.
  Qed.

  Lemma ex_integral_ext f1 f2:
    (∀ x, f1 x = f2 x) →
    ex_integral f1 →
    ex_integral f2.
  Proof.
    intros Hex (v1&?). exists v1. eapply is_integral_ext; eauto.
  Qed.

  Lemma Integral_ext f1 f2:
    (∀ x, f1 x = f2 x) →
    Integral f1 = Integral f2.
  Proof.
    intros Hex. rewrite /Integral. f_equal; apply Pos_integral_ext => x; rewrite Hex; done.
  Qed.

  Global Instance is_integral_Proper:
    Proper (pointwise_relation _ eq ==> eq ==> iff) (is_integral).
  Proof.
    intros ?? Heq ?? ->. split; eapply is_integral_ext; eauto.
  Qed.

  Global Instance ex_integral_Proper:
    Proper (pointwise_relation _ eq ==> iff) (ex_integral).
  Proof.
    intros ?? Heq. split; eapply ex_integral_ext; eauto.
  Qed.

  Global Instance Integral_Proper:
    Proper (pointwise_relation _ eq ==> eq) Integral.
  Proof.
    intros ?? Heq. by apply Integral_ext.
  Qed.

  Lemma is_integral_minus f1 v1 f2 v2:
    is_integral f1 v1 →
    is_integral f2 v2 →
    is_integral (λ x, f2 x - f1 x) (v2 - v1).
  Proof.
    intros Hi1 Hi2.
    assert (Heq: ∀ x, f2 x - f1 x = f2 x + -1 * f1 x) by (intros; nra).
    replace (v2 - v1) with (v2 + - 1 * v1) by field.
    setoid_rewrite Heq.
    apply is_integral_plus; auto.
    apply is_integral_scal. done.
  Qed.

  Lemma ex_integral_minus f1 f2:
    ex_integral f1 →
    ex_integral f2 →
    ex_integral (λ x, f2 x - f1 x).
  Proof.
    intros (v1&?) (v2&?); eexists; eapply is_integral_minus; eauto.
  Qed.

  Lemma Integral_minus f1 f2:
    ex_integral f1 →
    ex_integral f2 →
    Integral (λ x, f1 x - f2 x) = Integral f1 - Integral f2.
  Proof.
    intros Hex1 Hex2.
    apply is_integral_unique.
    apply is_integral_minus; apply Integral_correct; eauto.
  Qed.

  Lemma is_pos_integral_0:
    is_pos_integral (λ _, 0) 0.
  Proof.
    split.
    - apply measurable_const.
    - split.
      * intros ? (wpt&?&?). subst.
        replace 0 with (wpt_integral (wpt_const 0)).
        { apply wpt_integral_mono => //=. intros. rewrite wpt_const_spec.
          done. }
        rewrite wpt_integral_const; nra.
      * intros ? H. apply H.
        exists (wpt_const 0); split.
        ** intros; rewrite wpt_const_spec; nra.
        ** rewrite wpt_integral_const; nra.
  Qed.

  Lemma Pos_integral_0:
    Pos_integral (λ _, 0) = 0.
  Proof. apply is_pos_integral_unique, is_pos_integral_0. Qed.

  Lemma is_integral_equiv_pos_integral f v:
    (∀ x, 0 <= f x) →
    is_integral f v ↔ is_pos_integral f v.
  Proof.
    intros Hpos; split.
    - intros (Hmeas&v1&v2&?&Hp2&?). 
      cut (v2 = 0).
      { intros. replace v with v1 by nra.
        eapply is_pos_integral_ext; try eassumption.
        intros => //=. rewrite Rmax_left; eauto.
      }
      assert (Heq: ∀ x, Rmax (- f x) 0 = 0).
      { intros. rewrite Rmax_right; auto.
        apply Rge_le, Ropp_0_le_ge_contravar. eauto.
      }
      setoid_rewrite Heq in Hp2.
      erewrite <-(is_pos_integral_unique _ v2); eauto.
      apply is_pos_integral_unique. apply is_pos_integral_0.
    - intros Hpos'. split; eauto.
      * exists v, 0; split_and!; last field.
        ** eapply is_pos_integral_ext; last eassumption.
           intros x. rewrite Rmax_left; eauto.
        ** eapply is_pos_integral_ext; last eapply is_pos_integral_0.
           intros x. rewrite Rmax_right; eauto.
           apply Rge_le, Ropp_0_le_ge_contravar. eauto.
  Qed.

  Lemma ex_integral_equiv_pos_integral f:
    (∀ x, 0 <= f x) →
    ex_integral f ↔ ex_pos_integral f.
  Proof.
    intros Hpos. split; intros (v&?); eexists; eapply is_integral_equiv_pos_integral; eauto.
  Qed.

  Lemma Integral_equiv_Pos_integral f:
    (∀ x, 0 <= f x) →
    Integral f = Pos_integral f.
  Proof.
    intros Hpos. rewrite /Integral.
    assert (Hequiv: ∀ x, (λ x, Rmax (- f x) 0) x = 0).
    { intros x. specialize (Hpos x). apply Rmax_case_strong; nra. }
    setoid_rewrite Hequiv. rewrite Pos_integral_0 Rminus_0_r.
    apply Pos_integral_ext.
    intros x. rewrite Rmax_left; auto.
  Qed.

  Lemma is_integral_mono f1 v1 f2 v2:
    (∀ x, f1 x <= f2 x) →
    is_integral f1 v1 →
    is_integral f2 v2 →
    v1 <= v2.
  Proof.
    intros Hle Hint1 Hint2.
    cut (0 <= v2 - v1); first by nra.
    assert (His: is_integral (λ x, f2 x - f1 x) (v2 - v1)).
    { apply is_integral_minus; auto. }
    apply is_integral_equiv_pos_integral in His; last by (intros x; specialize (Hle x); nra).
    eapply is_pos_integral_mono in His; first eassumption; try eapply is_pos_integral_0.
    intros x => //=. specialize (Hle x); nra.
  Qed.

  Lemma Integral_mono f1 f2:
    (∀ x, f1 x <= f2 x) →
    ex_integral f1 →
    ex_integral f2 →
    Integral f1 <= Integral f2.
  Proof.
    intros Hmono (v1&Heq1) (v2&Heq2).
    rewrite (is_integral_unique _ _ Heq1).
    rewrite (is_integral_unique _ _ Heq2).
    eapply is_integral_mono; eauto.
  Qed.

  Lemma is_integral_measurable f v:
    is_integral f v → measurable f F (borel R_UniformSpace).
  Proof. destruct 1; eauto. Qed.

  Lemma ex_integral_measurable f:
    ex_integral f → measurable f F (borel R_UniformSpace).
  Proof. destruct 1 as (?&?); eauto using is_integral_measurable. Qed.

  Hint Resolve is_integral_measurable ex_integral_measurable.

  Lemma is_pos_integral_wpt wpt:
    (∀ x, 0 <= wpt_fun wpt x) →
    is_pos_integral (wpt_fun wpt) (wpt_integral wpt).
  Proof.
    intros Hpos. 
    eapply (is_pos_integral_mct_wpt (λ n, wpt)).
    - apply wpt_fun_measurable. 
    - intros; apply is_lim_seq_const.
    - intros; reflexivity.
    - apply is_lim_seq_const.
  Qed.

  Lemma is_integral_wpt wpt:
    is_integral (wpt_fun wpt) (wpt_integral wpt).
  Proof.
    induction wpt using wpt_induction.
    - eapply is_integral_ext; eauto.
      rewrite (wpt_integral_proper wpt2 wpt1); auto.
        by symmetry.
    - apply is_integral_equiv_pos_integral.
      { intros x. rewrite wpt_indicator_spec; destruct excluded_middle_informative; nra. }
      apply is_pos_integral_wpt.
      { intros x. rewrite wpt_indicator_spec; destruct excluded_middle_informative; nra. }
    - rewrite wpt_integral_plus.
      eapply is_integral_ext.
      { intros x; by rewrite wpt_plus_spec. }
      apply is_integral_plus; eauto.
    - rewrite wpt_integral_scal.
      eapply is_integral_ext.
      { intros x; by rewrite wpt_scal_spec. }
      apply is_integral_scal; eauto.
  Qed.
      
  Lemma ex_integral_wpt wpt:
    ex_integral (wpt_fun wpt).
  Proof.
    eexists. eapply is_integral_wpt.
  Qed.

  Lemma Integral_wpt wpt:
    Integral (wpt_fun wpt) = wpt_integral wpt.
  Proof. apply is_integral_unique, is_integral_wpt. Qed.

  Lemma is_integral_0:
    is_integral (λ _, 0) 0.
  Proof. apply is_integral_equiv_pos_integral; first reflexivity. apply is_pos_integral_0. Qed.

  Lemma Integral_0:
    Integral (λ _, 0) = 0.
  Proof. apply is_integral_unique, is_integral_0. Qed.

  Lemma ex_integral_sum_n fn m:
    (∀ n, (n <= m)%nat → ex_integral (fn n)) →
    ex_integral (λ x, sum_n (λ n, fn n x) m).
  Proof.
    induction m.
    - intros Hex. setoid_rewrite sum_O. eauto.
    - intros Hex. setoid_rewrite sum_Sn. apply ex_integral_plus; auto.
  Qed.

  Lemma Integral_sum_n fn m:
    (∀ n, (n <= m)%nat → ex_integral (fn n)) →
    Integral (λ x, sum_n (λ n, fn n x) m) =
    sum_n (λ n, Integral (fn n)) m.
  Proof.
    induction m.
    - intros Hex. setoid_rewrite sum_O. done.
    - intros Hex. setoid_rewrite sum_Sn. rewrite /plus//=.
      rewrite Integral_plus; eauto using ex_integral_sum_n.
      f_equal; eauto.
  Qed.

  Lemma is_integral_ge0 f v:
    (∀ x, 0 <= f x) →
    is_integral f v →
    v >= 0.
  Proof.
    intros Hpos His.
    apply Rle_ge.
    eapply is_integral_mono.
    - eapply Hpos. 
    - apply is_integral_0.
    - eauto.
  Qed.

  Lemma Pos_integral_ge0 f:
    (∀ x, 0 <= f x) →
    Pos_integral f >= 0.
  Proof.
    intros Hpos. rewrite /Pos_integral.
    destruct excluded_middle_informative; last nra.
    destruct excluded_middle_informative; last nra.
    apply Rle_ge. eapply (Rle_trans _ (wpt_integral (wpt_indicator empty_set (sigma_empty_set F)))).
    { rewrite wpt_integral_indicator measure_empty. nra. } 
    destruct (completeness _) as (?&Hlub).
    apply Hlub. eexists. split; eauto.
    intros x'. rewrite wpt_indicator_spec. destruct (excluded_middle_informative) as [[]|]; auto.
  Qed.

  Lemma Integral_ge0 f:
    (∀ x, 0 <= f x) →
    Integral f >= 0.
  Proof.
    intros Hpos.
    rewrite /Integral. cut (Pos_integral (λ x, Rmax (- f x) 0) = 0).
    { intros ->. feed pose proof (Pos_integral_ge0 (λ x, Rmax (f x) 0)).
      { intros. apply Rmax_case_strong; nra. }
      nra.
    }
    rewrite -{2}Pos_integral_0. apply Pos_integral_ext. intros.
    specialize (Hpos x). apply Rmax_case_strong => //=; nra.
  Qed.

  Hint Resolve is_integral_wpt ex_integral_wpt.

  Lemma ex_integral_mono_ex f1 f2:
    (∀ x, Rabs (f1 x) <= f2 x) →
    measurable f1 F (borel _) →
    ex_integral f2 →
    ex_integral f1.
  Proof.
    intros Hb Hmeas (v&(?&?&?&?&?&?)).
    edestruct (is_pos_integral_mono_ex (λ x, Rmax (f1 x) 0) (λ x, Rmax (f2 x) 0)) as ((xp&?)&?).
    { intros ?; apply Rmax_case_strong; nra. }
    { intros x' => //=. specialize (Hb x'). move: Hb.
      apply Rabs_case; do 2 apply Rmax_case_strong; nra. }
    { apply measurable_Rmax; eauto. measurable. }
    { eauto.  }

    edestruct (is_pos_integral_mono_ex (λ x, Rmax (- f1 x) 0) (λ x, Rmax (f2 x) 0)) as ((xn&?)&?).
    { intros ?; apply Rmax_case_strong; nra. }
    { intros x' => //=. generalize (Hb x'). 
      apply Rabs_case; do 2 apply Rmax_case_strong; nra. }
    { apply measurable_Rmax; eauto; measurable. }
    { eauto.  }
    exists (xp - xn).
    split; auto. exists xp, xn.
    eauto.
  Qed.

  Lemma ex_integral_Rabs f:
    measurable f F (borel _) →
    ex_integral f ↔ ex_integral (λ x, Rabs (f x)).
  Proof.
    intros Hmeas.
    split.
    - intros (v&Hmeas'&(v1&v2&His1&His2&Heq)).
      assert (∀ x, Rabs (f x) = Rmax (f x) 0 + Rmax (- f x) 0) as Hequiv.
      { intros; apply Rabs_case; do 2 apply Rmax_case_strong; nra. }
      setoid_rewrite Hequiv.
      apply ex_integral_plus.
      * apply ex_integral_equiv_pos_integral; last by eexists; eauto.
        intros. apply Rmax_case_strong; nra.
      * apply ex_integral_equiv_pos_integral; last by eexists; eauto.
        intros. apply Rmax_case_strong; nra.
    - intros. eapply ex_integral_mono_ex; eauto.
      intros x. rewrite //=. reflexivity.
  Qed.

  Lemma Integral_mono_pos f1 f2:
    (∀ x, 0 <= f1 x) →
    (∀ x, f1 x <= f2 x) →
    measurable f1 F (borel _) →
    ex_integral f2 →
    Integral f1 <= Integral f2.
  Proof.
    intros Hpos Hmono Hmeas Hex. eapply Integral_mono; eauto.
    eapply ex_integral_mono_ex. eauto.
    { intros. rewrite Rabs_right; eauto. }
    { auto. }
    { auto. }
  Qed.

  Lemma is_integral_wpt_ae_0 wpt:
    (∀ x, 0 <= wpt_fun wpt x) →
    almost_everywhere_meas μ (λ x, wpt_fun wpt x = 0) →
    is_integral (wpt_fun wpt) 0.
  Proof.
    intros Hpos.
    eapply (wpt_pos_induction 
        (λ wpt, almost_everywhere_meas μ (λ x : A, wpt_fun wpt x = 0) → is_integral (wpt_fun wpt) 0)).
    - intros wpt1 wpt2 Heq IH Hae.
      eapply is_integral_ext; last eapply IH; eauto.
      eapply almost_everywhere_meas_ext; eauto.
      intros ?. by rewrite Heq.
    - intros U Hmeas Hae.  cut (Integral (wpt_fun (wpt_indicator U Hmeas)) = 0).
      { intros <-. apply Integral_correct; auto. }
      rewrite Integral_wpt wpt_integral_indicator.
      destruct Hae as (?&His0).
      apply Rle_antisym; last by apply Rge_le, measure_nonneg.
      rewrite -His0. apply measure_mono; auto.
      intros x HU Hneg. rewrite wpt_indicator_spec in Hneg.
      destruct (excluded_middle_informative); try contradiction. nra.
    - intros wpt1 wpt2 Hpos1 IH1 Hpos2 IH2 Hae.
      replace 0 with (0 + 0) by nra.
      eapply is_integral_ext.
      { intros x; by rewrite wpt_plus_spec. }
      apply is_integral_plus.
      * eapply IH1. eapply almost_everywhere_meas_mono; eauto.
        { apply measurable_fun_eq_0; auto. }
        intros x. rewrite wpt_plus_spec. specialize (Hpos1 x). specialize (Hpos2 x).
        nra.
      * eapply IH2. eapply almost_everywhere_meas_mono; eauto.
        { apply measurable_fun_eq_0; auto. }
        intros x. rewrite wpt_plus_spec. specialize (Hpos1 x). specialize (Hpos2 x).
        nra.
    - intros k wpt1 Hkpos Hpos1 IH1 Hae.
      replace 0 with (k * 0) by field.
      eapply is_integral_ext.
      { intros x. rewrite wpt_scal_spec. done. }
      destruct Hkpos; last first.
      { subst. setoid_rewrite Rmult_0_l. apply is_integral_0. }
      apply is_integral_scal.
      eapply IH1. eapply almost_everywhere_meas_mono; eauto.
        { apply measurable_fun_eq_0; auto. }
      intros x. rewrite wpt_scal_spec. nra.
    - auto.
  Qed.

  Lemma is_integral_pos_ae_0 f:
    measurable f F (borel _) →
    (∀ x, 0 <= f x) →
    almost_everywhere_meas μ (λ x, f x = 0) →
    is_integral f 0.
  Proof.
    intros Hmeas Hpos.
    edestruct (wpt_approx_measurable _ Hpos Hmeas) as (wptn&?&?&Hle&Hposn).
    intros Hae. apply is_integral_equiv_pos_integral; eauto.
    eapply is_pos_integral_mct_wpt; eauto.
    eapply is_lim_seq_ext; last eapply is_lim_seq_const.
    intros n => //=. rewrite -Integral_wpt. symmetry.
    apply is_integral_unique. apply is_integral_wpt_ae_0; eauto.
    eapply almost_everywhere_meas_mono; eauto.
    { apply measurable_fun_eq_0; auto. }
    intros x Heq0. specialize (Hle n x). specialize (Hposn n x). nra.
  Qed.

  Lemma is_integral_alt (f: A → R) v :
    (measurable f F (borel R_UniformSpace) ∧
    ∃ v1 v2, is_integral (λ x, Rmax (f x) 0) v1 ∧
             is_integral (λ x, Rmax (- f x) 0) v2 ∧
             v = v1 - v2) ↔ is_integral f v.
  Proof.
    split.
    - intros (?&v1&v2&?&?&?).
      split; auto. exists v1, v2.
      split_and!; auto; apply is_integral_equiv_pos_integral; eauto;
        intros x; apply Rmax_case_strong; nra.
    - intros (Hmeas&(v1&v2&?&?&?)). split; auto.
      exists v1, v2; split_and!; auto.
      * apply is_integral_equiv_pos_integral; auto using Rmax_r.
      * apply is_integral_equiv_pos_integral; auto using Rmax_r.
  Qed.

  Lemma ex_integral_alt (f: A → R) :
    (measurable f F (borel R_UniformSpace) ∧
     ex_integral (λ x, Rmax (f x) 0) ∧
     ex_integral (λ x, Rmax (- f x) 0))
    ↔ ex_integral f.
  Proof.
    split.
    - intros (Hmeas&Hex1&Hex2).
      destruct Hex1 as (v1&His1). destruct Hex2 as (v2&His2).
      exists (v1 - v2). apply is_integral_alt.
      split; auto.
      exists v1, v2; split_and!; eauto.
    - intros (Hmeas&His).
      apply is_integral_alt in His as (?&?&?&?&?&?).
      split; auto. split; eexists; eauto.
  Qed.

  Lemma Integral_alt f:
    Integral f = Integral (λ x, Rmax (f x) 0) - Integral (λ x, Rmax (- f x) 0).
  Proof.
    rewrite {1}/Integral; f_equal; symmetry; apply Integral_equiv_Pos_integral; auto using Rmax_r.
  Qed.

  Lemma is_integral_ae_0 f:
    measurable f F (borel _) →
    almost_everywhere_meas μ (λ x, f x = 0) →
    is_integral f 0.
  Proof.
    intros Hmeas Hae. apply is_integral_alt; split; auto.
    exists 0, 0; split_and!; last field.
    - apply is_integral_pos_ae_0.
      * apply measurable_Rmax; measurable.
      * intros; apply Rmax_case_strong; nra.
      * eapply almost_everywhere_meas_mono; eauto.
        ** apply measurable_fun_eq_0; auto.
           apply measurable_Rmax; measurable.
        ** intros x ->. apply Rmax_case_strong; auto.
    - apply is_integral_pos_ae_0.
      * apply measurable_Rmax; measurable.
      * intros; apply Rmax_case_strong; nra.
      * eapply almost_everywhere_meas_mono; eauto.
        ** apply measurable_fun_eq_0; auto.
           apply measurable_Rmax; measurable.
        ** intros x ->. apply Rmax_case_strong; auto. nra.
  Qed.

  Lemma is_integral_ae_ext f1 f2 v:
    almost_everywhere_meas μ (λ x, f1 x = f2 x) →
    measurable f2 F (borel _) →
    is_integral f1 v →
    is_integral f2 v.
  Proof.
    intros Hae Hmeas His.
    feed pose proof (is_integral_ae_0 (λ x, f2 x - f1 x)) as Hisdiff.
    { measurable. eauto. }
    { eapply almost_everywhere_meas_ext; eauto. split; intros; nra. }
    specialize (is_integral_plus _ _ _ _ His Hisdiff).
    rewrite Rplus_0_r. apply is_integral_ext. intros; field.
  Qed.

  Lemma ex_integral_ae_ext f1 f2:
    almost_everywhere_meas μ (λ x, f1 x = f2 x) →
    measurable f2 F (borel _) →
    ex_integral f1 →
    ex_integral f2.
  Proof.
    intros Hae Hmeas (v&His). exists v. eapply is_integral_ae_ext; eauto.
  Qed.

  Lemma Integral_ae_ext_weak f1 f2:
    almost_everywhere_meas μ (λ x, f1 x = f2 x) →
    measurable f2 F (borel _) →
    ex_integral f1 →
    Integral f1 = Integral f2.
  Proof.
    intros Hae ? Hex. symmetry. apply is_integral_unique.
    eapply is_integral_ae_ext; eauto.
    by apply Integral_correct.
  Qed.


  Lemma is_integral_levi_pos_ex fn f:
    measurable f F (borel _) →
    (∀ x, is_lim_seq (λ n, fn n x) (f x : R)) →
    (∀ x, ∀ n, 0 <= fn n x) →
    (∀ x, ∀ n, fn n x <= fn (S n) x) →
    (∀ n, ex_integral (fn n)) →
    bound (λ r, ∃ n, is_integral (fn n) r) →
    ex_integral f ∧ is_lim_seq (λ n, Integral (fn n)) (Integral f). 
  Proof.
    intros Hmeas Hlim Hpos Hmono Hint_fn Hbounded_int.
    assert (Hfpos: ∀ x, 0 <= f x).
    { intros x. eapply is_lim_seq_pos; eauto.
      intros n. apply Rle_ge; eauto. }
    assert (Hfn_bounded_fpos: ∀ n x, fn n x <= f x).
    { intros n x.
      apply: (is_lim_seq_incr_compare (λ n, fn n x) (f x)); eauto.
    }
    (*
    assert (Hf_bounded_g: ∀ x, f x <= g x).
    { intros x.
      apply (is_lim_seq_le (λ n, fn n x) (λ _, g x) (f x) (g x)); eauto.
      apply is_lim_seq_const.
    }
     *)
    assert (Hfn_meas: ∀ n, measurable (fn n) F (borel _)).
    { intros n. auto. }
    set (gnk_wit := λ n, constructive_indefinite_description _
                    (wpt_approx_measurable (fn n) (λ x, Hpos x n) (Hfn_meas n))).
    set (gnk := λ n, sval (gnk_wit n)).
    set (hnk := λ n k, nat_rect (λ _, weighted_partition)
                                (wpt_const 0)
                                (λ m w, wpt_max w (gnk m n)) (S k)).
    set (hn := λ n, hnk n n).  
    assert (Hhnk_mono1: ∀ n k, ∀ x, wpt_fun (hnk n k) x <= wpt_fun (hnk (S n) k) x).
    { 
      intros n k x. revert n. rewrite /hnk. generalize (wpt_const 0).  generalize (S k); clear k.
      intros k. induction k => //= w n.
      - reflexivity.
      - rewrite ?wpt_max_spec. apply Rmax_le_compat. 
        * eapply IHk.
        * rewrite /gnk/gnk_wit. destruct constructive_indefinite_description as (?&?&?&?); eauto.
    }
    assert (Hhnk_mono2: ∀ n k, ∀ x, wpt_fun (hnk n k) x <= wpt_fun (hnk n (S k)) x).
    { 
      intros n k x. revert n. rewrite /hnk. generalize (wpt_const 0).  generalize (S k); clear k.
      intros k. induction k => //= w n.
      - rewrite wpt_max_spec. apply Rmax_l.
      - rewrite ?wpt_max_spec. apply Rmax_l.
    }
    assert (Hhnk_mono: ∀ n k, (∀ n' k', (n' <= n)%nat → (k' <= k)%nat →
                                        ∀ x, wpt_fun (hnk n' k') x <= wpt_fun (hnk n k) x)).
    { intros n k n' k' Hle1 Hle2.
      revert k' k Hle2. induction Hle1.
      * intros. induction Hle2.
        ** reflexivity.
        ** etransitivity; first eauto. eapply Hhnk_mono2.
      * intros. etransitivity; first eapply IHHle1; eauto.
    }
    assert (Hhnk_gnk: ∀ n k, ∀ x, wpt_fun (gnk k n) x <= wpt_fun (hnk n k) x).
    { intros. rewrite wpt_max_spec. apply Rmax_r. } 
    assert (Hhnk_ub: ∀ n k, (∀ n' k', (n' <= n)%nat → (k' <= k)%nat →
                                   ∀ x, wpt_fun (gnk k' n') x <= wpt_fun (hnk n k) x)).
    { intros ???? Hle1 Hle2 x. etransitivity; first eapply Hhnk_gnk.
      apply Hhnk_mono; eauto. }
    assert (Hgnk_bounded_fn: ∀ n k, ∀ x, wpt_fun (gnk n k) x <= fn n x).
    { rewrite /gnk/gnk_wit => n k x.
      destruct constructive_indefinite_description as (?&?&?&Hbn&?) => //=.
    }
    assert (Hgnk_bounded_f: ∀ n k, ∀ x, wpt_fun (gnk n k) x <= f x).
    { intros. transitivity (fn n x); eauto. }
    assert (Hhnk_bounded_fn: ∀ n k, ∀ x, wpt_fun (hnk n k) x <= fn k x).
    { intros n k x. rewrite /hnk.
      assert (Hle: ∀ k, wpt_fun (wpt_const 0) x <= fn k x).
      { rewrite wpt_const_spec. eauto. }
      rewrite //=. rewrite wpt_max_spec.
      apply Rmax_lub; last by eauto.
      revert Hle. generalize (wpt_const 0).
      induction k => //=.
      - intros w Hle. 
        rewrite wpt_max_spec. apply Rmax_lub; eauto.
        etransitivity; first eapply IHk; eauto.
        transitivity (fn k x); eauto.
    }
    assert (Hhnk_bounded_f: ∀ n k, ∀ x, wpt_fun (hnk n k) x <= f x).
    { intros. transitivity (fn k x); eauto. }
    assert (∀ n x, 0 <= wpt_fun (hn n) x ).
    { rewrite /hn. etransitivity; last eapply Hhnk_gnk.
      rewrite /gnk. destruct (gnk_wit) as (?&?&?&?&?); eauto.
    }
    edestruct (is_pos_integral_mct_wpt_ex hn f).
    { auto. }
    { intros x P => //= Hloc.
      destruct Hloc as (eps&Heps).
      edestruct (Hlim x (ball (f x) (pos_div_2 eps))) as (n1&Hn1).
      { rewrite //=. apply (locally_ball _ (pos_div_2 eps)). }
      destruct (proj2_sig (gnk_wit n1)) as (Hlb&Hlim_gnk&Hbounded_gnk&?).
      destruct (Hlim_gnk x (ball (fn n1 x) (pos_div_2 (pos_div_2 eps)))) as (n2&Hn2).
      { rewrite //=. apply (locally_ball _ (pos_div_2 (pos_div_2 eps))). }
      exists (max n1 n2).
      intros n Hge.
      apply Heps.
      rewrite /ball//=/AbsRing_ball/abs/minus/plus/opp//=.
      rewrite Rabs_left1; last first.
      { rewrite /hn. specialize (Hhnk_bounded_f n n x); eauto. nra. }

      feed pose proof (Hn1 n1) as Hn1'.
      { etransitivity; last eauto. reflexivity. } 
      rewrite /ball//=/AbsRing_ball/abs/minus/plus/opp//= in Hn1'.
      rewrite Rabs_left1 in Hn1'; last first.
      { specialize (Hfn_bounded_fpos n1 x). nra. }

      feed pose proof (Hn2 n) as Hn2'.
      { etransitivity; last eauto. apply Nat.le_max_r. } 
      rewrite /ball//=/AbsRing_ball/abs/minus/plus/opp//= in Hn2'.
      rewrite Rabs_left1 in Hn2'; last first.
      { specialize (Hbounded_gnk n x). nra.  }


      specialize (Hbounded_gnk n x).
      specialize (Hgnk_bounded_f n n x).
      rewrite /gnk in Hgnk_bounded_f.
      specialize (Hhnk_bounded_f n n x).
      feed pose proof (Hhnk_ub n n n n1) as Hhn_ub.
      { reflexivity. } 
      { etransitivity; last eauto. apply Nat.le_max_l. } 
      specialize (Hhn_ub x). rewrite /hn. rewrite /gnk in Hhn_ub.
      destruct eps as (eps&hgt0) => //=.
      rewrite //= in Hn1' Hn2'.
      nra.
    }
    { eauto.  }
    { destruct Hbounded_int as (v&Hspec).
      exists v. intros r (n&<-).
      transitivity (Integral (fn n)); first eapply (is_integral_mono (λ x, wpt_fun (hn n) x) _ (fn n));
        last eauto.
      - intros x. rewrite /hn. eauto.
      - eapply is_integral_equiv_pos_integral; eauto.
        eapply is_pos_integral_wpt; eauto.
      - apply Integral_correct; eauto.
      - eapply Hspec. exists n; eauto using Integral_correct.
    }
    split.
    * apply ex_integral_equiv_pos_integral; eauto. 
    * rewrite Integral_equiv_Pos_integral; eauto.
      apply (is_lim_seq_le_le (λ n, wpt_integral (hn n)) _ (λ n, Pos_integral f)); first split; eauto.
      { eapply (is_integral_mono (wpt_fun (hn n)) _ (fn n) _).
        * eauto.
        * apply is_integral_equiv_pos_integral; eauto.
          eapply is_pos_integral_wpt; eauto.
        * apply Integral_correct. eauto.
      }
      rewrite Integral_equiv_Pos_integral; eauto.
      eapply (is_pos_integral_mono (fn n) f); eauto.
      ** apply Pos_integral_correct.
         apply ex_integral_equiv_pos_integral; eauto.
      ** by apply Pos_integral_correct.
      ** apply is_lim_seq_const.
  Qed.

  Lemma is_integral_levi_ex fn f:
    measurable f F (borel _) →
    (∀ x, is_lim_seq (λ n, fn n x) (f x : R)) →
    (∀ x, ∀ n, fn n x <= fn (S n) x) →
    (∀ n, ex_integral (fn n)) →
    bound (λ r, ∃ n, is_integral (fn n) r) →
    ex_integral f ∧ is_lim_seq (λ n, Integral (fn n)) (Integral f). 
  Proof.
    intros Hmeas Hlim Hmono Hex Hbounded_int.
    set (fn' := λ n x, fn n x - fn O x).
    set (f' := λ x, f x - fn O x).
    assert (∀ n : nat, ex_integral (fn' n)).
    { intros n. rewrite /fn'. apply ex_integral_minus; eauto. }
    edestruct (is_integral_levi_pos_ex fn' f').
    - rewrite /f'. apply measurable_minus; eauto.
    - rewrite /fn'/f' => x. eapply is_lim_seq_minus; eauto.
      * apply is_lim_seq_const.
      * rewrite //=.
    - intros x n. rewrite /fn'.
      cut (fn O x <= fn n x); first nra.
      clear -Hmono; induction n.
      * nra. 
      * etransitivity; eauto.
    - rewrite /fn'; intros; apply Rplus_le_compat; eauto. reflexivity.
    - intros n. rewrite /fn'. apply ex_integral_minus; eauto.
    - destruct Hbounded_int as (v&Hbound).
      exists (v - Integral (fn O)).
      intros r (n&His).
      rewrite /fn' in His.
      assert (r = Integral (λ x, fn n x - fn O x)) as ->.
      { symmetry. apply is_integral_unique; eauto. }
      rewrite Integral_minus; eauto.
      cut (Integral (fn n) <= v); first by nra.
      eapply Hbound. exists n. apply Integral_correct; eauto.
    - assert (Hext: ∀ x : A, f' x + fn O x = f x).
      { rewrite /f' => x. nra. }
      assert (Hextn: ∀ n x, fn' n x + fn O x = fn n x).
      { rewrite /fn' => n x. nra. }
      assert (ex_integral f).
      {  eapply (ex_integral_ext (λ x, f' x + fn O x)); eauto.
         apply ex_integral_plus; eauto. }
      split; auto.
      * eapply is_lim_seq_ext.
        { intros n. apply Integral_ext; first eapply Hextn. }
        eapply is_lim_seq_ext.
        ** intros n. rewrite Integral_plus; eauto.
        ** rewrite -(Integral_ext _ _ Hext); auto using ex_integral_plus.
           rewrite Integral_plus; eauto.
           eapply is_lim_seq_plus; eauto.
           { apply is_lim_seq_const. }
           rewrite //=.
  Qed.

  Lemma ae_equal_mult_indicator_compl_0:
    ∀ f U Hmeas, measurable f F (borel _) → μ (compl U) = 0 →
                 almost_everywhere_meas μ (λ x, f x * wpt_fun (wpt_indicator U Hmeas) x = f x).
  Proof.
    intros g U Hmeas Hmeasg Heq0.
    eapply almost_everywhere_meas_mono; last first.
    { split; eauto.  }
    { intros x. rewrite wpt_indicator_spec. 
      intros. destruct excluded_middle_informative.
      * rewrite Rmult_1_r. done.
      * contradiction.
    }
    { apply measurable_fun_eq_inv; measurable. }
  Qed.

  Lemma ae_equal_mult_indicator_compl_0':
    ∀ f U Hmeas, measurable f F (borel _) → μ (compl U) = 0 →
                 almost_everywhere_meas μ (λ x, f x = f x * wpt_fun (wpt_indicator U Hmeas) x).
  Proof.
    intros.
    eapply almost_everywhere_meas_ext; last eapply ae_equal_mult_indicator_compl_0; try eassumption.
    intros x. split; by symmetry; eauto.
  Qed.
    
  Lemma is_integral_levi_ae_ex fn f:
    measurable f F (borel _) →
    almost_everywhere_meas μ (λ x, is_lim_seq (λ n, fn n x) (f x : R)) →
    almost_everywhere_meas μ (λ x, ∀ n, fn n x <= fn (S n) x) →
    (∀ n, ex_integral (fn n)) →
    bound (λ r, ∃ n, is_integral (fn n) r) →
    ex_integral f ∧ is_lim_seq (λ n, Integral (fn n)) (Integral f). 
  Proof.
    generalize ae_equal_mult_indicator_compl_0 => Hae.
    intros Hmeas Hlim Hmono Hex Hbound.
    specialize (almost_everywhere_meas_conj μ _ _ Hlim Hmono).
    intros (HF&Hμ0).
    apply sigma_closed_complements in HF.
    rewrite compl_involutive in HF * => HF.
    feed pose proof (is_integral_levi_ex (λ n, λ x, fn n x * wpt_fun (wpt_indicator _ HF) x)
                                         (λ x, f x * wpt_fun (wpt_indicator _ HF) x))
         as Hlevi.
    { measurable. }
    { intros x. setoid_rewrite wpt_indicator_spec.
      destruct excluded_middle_informative as [(Hlim'&?)|Hnotin].
      * setoid_rewrite Rmult_1_r. eauto.
      * setoid_rewrite Rmult_0_r. apply is_lim_seq_const.
    }
    { intros x n. rewrite wpt_indicator_spec.
      destruct excluded_middle_informative as [(Hlim'&?)|Hnotin].
      * setoid_rewrite Rmult_1_r. eauto.
      * setoid_rewrite Rmult_0_r. reflexivity.
    }
    { intros n. eapply ex_integral_ae_ext; eauto.
      { eapply almost_everywhere_meas_ext; last eapply ae_equal_mult_indicator_compl_0.
        * intros ?; split; symmetry; eauto.
        * measurable.
        * eauto.
      }
      measurable.
    }
    { destruct Hbound as (r&Hub). exists r.
      intros ? (n&His). eapply is_integral_ae_ext in His; auto.
      eapply Hub; eauto. }
    destruct Hlevi as (Hlevi_ex&Hlevi_lim).
    assert (ex_integral f).
    { eapply ex_integral_ae_ext; eauto. eapply ae_equal_mult_indicator_compl_0; measurable. }
    split; auto.
    setoid_rewrite <-(Integral_ae_ext_weak) in Hlevi_lim; eauto.
    { eapply is_lim_seq_ext; last eauto.
      intros n => //=.
      symmetry. apply Integral_ae_ext_weak; eauto.
      { eapply almost_everywhere_meas_ext; last eapply ae_equal_mult_indicator_compl_0.
        * intros ?; split; symmetry; eauto.
        * measurable.
        * eauto.
      }
      measurable.
    }
    { eapply almost_everywhere_meas_ext; last eapply ae_equal_mult_indicator_compl_0.
      * intros ?; split; symmetry; eauto.
      * measurable.
      * eauto.
    }
  Qed.

  Lemma is_integral_mct_ex fn f g:
    measurable f F (borel _) →
    (∀ x, is_lim_seq (λ n, fn n x) (f x : R)) →
    (∀ x, ∀ n, fn n x <= fn (S n) x) →
    (∀ x, ∀ n, Rabs (fn n x) <= g x) →
    (∀ n, ex_integral (fn n)) →
    ex_integral g →
    ex_integral f ∧ is_lim_seq (λ n, Integral (fn n)) (Integral f). 
  Proof.
    intros Hmeas Hlim Hmono Hbounded Hex Hexg.
    edestruct (is_integral_levi_ex fn f); eauto.
    destruct Hexg as (v&Hisg).
    exists v.
    intros r (n&His).
    eapply (is_integral_mono (fn n) _ g); eauto.
    intros. specialize (Hbounded x n). move: Hbounded.
    apply Rabs_case; nra.
  Qed.


  Lemma is_integral_const k :
    is_integral (λ _, k) (k * μ (λ _, True)).
  Proof.
    setoid_rewrite <-(wpt_const_spec k) at 1.
    rewrite -wpt_integral_const.
    apply is_integral_wpt.
  Qed.

  Lemma ex_integral_const k :
    ex_integral (λ _, k).
  Proof. eexists. apply is_integral_const. Qed.

  Lemma Integral_const k :
    Integral (λ _, k) = (k * μ (λ _, True)).
  Proof.
    apply is_integral_unique, is_integral_const.
  Qed.

  Lemma measurable_non_ex_pos_integral_0 f:
    measurable f F (borel R_UniformSpace) →
    ¬ ex_pos_integral f →
    Pos_integral f = 0.
  Proof.
    intros Hmeas Hnex. rewrite /Pos_integral.
    destruct excluded_middle_informative; auto.
    destruct excluded_middle_informative; auto.
    exfalso; apply Hnex; apply measurable_bounded_simple_ex_pos_integral; eauto.
  Qed.

  Lemma Integral_pos_mct fn f:
    measurable f F (borel _) →
    (∀ x, is_lim_seq (λ n, fn n x) (f x : R)) →
    (∀ x, ∀ n, 0 <= fn n x) →
    (∀ x, ∀ n, fn n x <= fn (S n) x) →
    (∀ n, ex_integral (fn n)) →
    real (Lim_seq (λ n, Integral (fn n))) = Integral f.
  Proof.
    intros Hmeas Hlim Hpos Hmono Hex.
    destruct (Classical_Prop.classic (bound (λ r, ∃ n, is_integral (fn n) r))) as [Hbound|Hunbounded].
    { feed pose proof (is_integral_levi_ex fn f) as Hlevi; eauto.
      destruct Hlevi as (Hex_f&Hlim_int).
      apply is_lim_seq_unique in Hlim_int. rewrite Hlim_int. done. }
    transitivity 0.
    - cut (Lim_seq (λ n, Integral (fn n)) = p_infty).
      { intros ->. done. }
      apply is_lim_seq_unique.
      intros P Hlocal. rewrite /Rbar_locally in Hlocal.
      destruct Hlocal as (K&HK).
      assert (∃ n, K < Integral (fn n)) as (n&HKn).
      { apply Classical_Prop.NNPP. intros Hnex.
        apply Hunbounded. exists K. intros r (n&Heqr).
        apply Rnot_lt_le. intros Hlt. apply Hnex; exists n.
        apply is_integral_unique in Heqr as ->. done. }
      exists n. intros n' Hge. apply HK.
      eapply Rlt_le_trans; first eauto. clear -Hge Hmono Hex.
      induction Hge; first reflexivity.
      etransitivity; eauto. apply Integral_mono; eauto.
    - symmetry.
      assert (∀ x, 0 <= f x).
      { intros x. eapply is_lim_seq_pos; eauto. eauto. }

      rewrite Integral_equiv_Pos_integral //. 

      assert (Hneg: ¬ ex_integral f).
      { intros (v&Hexf). apply Hunbounded.
        exists v. intros r (n&Heq).
        eapply (is_integral_mono (fn n) _ f _).
        - intros x. specialize (Hlim x). eapply is_lim_seq_incr_compare in Hlim; eauto.
        - done.
        - done.
      }
      apply measurable_non_ex_pos_integral_0; auto.
      intros Hex'. apply Hneg. apply ex_integral_equiv_pos_integral; eauto.
  Qed.

  Lemma is_lim_seq_Rmin_pos r:
    0 <= r →
    is_lim_seq (λ n : nat, Rmin r (INR n)) r.
  Proof.
    intros Hle. edestruct archimed_pos as (k&?); eauto.
    intros P Hloc.
    exists (S k) => n Hle'.
    rewrite Rmin_left.
    - rewrite /Rbar_locally/locally in Hloc.
      destruct Hloc as (eps&HP). apply HP. apply ball_center. 
    - transitivity (INR (S k)); first nra. 
      apply le_INR. done.
  Qed.

  Lemma ex_integral_Rmin f:
    (∀ x, 0 <= f x) →
    measurable f F (borel _) →
    ∀ n, ex_integral (λ x, Rmin (f x) (INR n)).
  Proof.
    { intros Hpos Hmeas n. apply (ex_integral_mono_ex _ (λ x, INR n)).
      { intros x. rewrite Rabs_right; auto. apply Rmin_r.
        apply Rmin_case_strong; auto.
        intros. apply Rle_ge, pos_INR. }
      { apply measurable_Rmin; eauto. apply measurable_const. }
      { apply ex_integral_const. }
    }
  Qed.

  Lemma ex_integral_ex_finite_lim_min f:
    (∀ x, 0 <= f x) →
    measurable f F (borel _) →
    ex_finite_lim_seq (λ n, Integral (λ x, Rmin (f x) (INR n))) ↔
            ex_integral f.
  Proof.
    intros Hpos Hmeas.
    assert (∀ n x, 0 <= Rmin (f x) (INR n)).
    { intros => //=. apply Rmin_case_strong; auto.
      intros. apply pos_INR. }
    generalize (ex_integral_Rmin _ Hpos Hmeas) => ?.
    split.
    - intros Hbounded.
      edestruct (is_integral_levi_pos_ex (λ n, λ x, Rmin (f x) (INR n))); eauto.
      { intros x => //=. eapply is_lim_seq_Rmin_pos; eauto. }
      { intros. apply Rle_min_compat_l. apply le_INR. auto. }
      destruct Hbounded as (r&Hub). exists r. intros z (n&His).
      rewrite -(is_integral_unique _ _ His).
      eapply (is_lim_seq_incr_compare (λ n, Integral (λ x, Rmin (f x) (INR n)))); eauto.
      intros n'. apply Integral_mono; eauto.
      intros x. apply Rle_min_compat_l, le_INR; omega.
    - intros (v&Hex). exists v.
      rewrite -(is_integral_unique _ _ Hex).
      edestruct (is_integral_mct_ex (λ n, (λ x, Rmin (f x) (INR n))) f f); eauto.
      { intros x => //=.
        apply is_lim_seq_Rmin_pos; eauto. }
      { intros. apply Rle_min_compat_l, le_INR; omega. }
      { rewrite //= => ??. apply Rmin_case_strong; intros; rewrite Rabs_right; try nra; eauto.
        apply Rle_ge, pos_INR. }
      eexists; eauto.
  Qed.

  Lemma ex_integral_sup_min f:
    (∀ x, 0 <= f x) →
    measurable f F (borel _) →
    bound (λ r, ∃ n, Integral (λ x, Rmin (f x) (INR n)) = r) ↔
            ex_integral f.
  Proof.
    intros Hpos Hmeas.
    assert (∀ n x, 0 <= Rmin (f x) (INR n)).
    { intros => //=. apply Rmin_case_strong; auto.
      intros. apply pos_INR. }
    generalize (ex_integral_Rmin _ Hpos Hmeas) => ?.
    split.
    - intros Hbounded.
      edestruct (is_integral_levi_pos_ex (λ n, λ x, Rmin (f x) (INR n))); eauto.
      { intros x => //=. eapply is_lim_seq_Rmin_pos; eauto. }
      { intros. apply Rle_min_compat_l. apply le_INR. auto. }
      destruct Hbounded as (r&Hub). exists r. intros z (n&?).
      apply Hub. exists n. apply is_integral_unique; eauto.
    - intros (v&Hex). exists v.
      intros r (n&<-).
      rewrite -(is_integral_unique _ _ Hex).
      apply Integral_mono; eauto.
      intros; apply Rmin_l.
      eexists; eauto.
  Qed.

  Lemma is_integral_bound_measure_above f v t:
    (∀ x, 0 <= f x) →
    is_integral f v →
    0 < t →
    μ (λ x, t <= f x) <= v / t. 
  Proof.
    intros Hpos His Htpos.
    apply Rnot_gt_le.
    intros Hgt.
    cut (v < Integral f).
    { intros Hlt. rewrite (is_integral_unique _ _ His) in Hlt. nra. }
    apply (Rlt_le_trans _ (t * (μ (λ x, t <= f x)))).
    { apply (Rmult_lt_reg_r (/t)).
      { apply Rinv_0_lt_compat; nra. }
      { field_simplify; try nra. }
    }
    assert (Hm: F (λ x, t <= f x)).
    { apply measurable_fun_ge. eauto. }
    transitivity (Integral (wpt_fun (wpt_scal t (wpt_indicator _ Hm)))).
    { right. rewrite Integral_wpt wpt_integral_scal wpt_integral_indicator. done. }
    apply Integral_mono; eauto.
    - intros x. rewrite wpt_scal_spec wpt_indicator_spec.
      destruct excluded_middle_informative; auto; try nra. rewrite Rmult_0_r. eauto.
    - eexists; eauto.
  Qed.

  Lemma Integral_Rabs f:
    (ex_integral f ∨ (measurable f F (borel _) ∧ ex_integral (λ x, Rabs (f x)))) →
    Rabs (Integral f) <= Integral (λ x, (Rabs (f x))).
  Proof.
    intros Hex.
    assert (ex_integral f).
    { destruct Hex; auto. apply ex_integral_Rabs; intuition. }
    assert (ex_integral (λ x, Rabs (f x))).
    { destruct Hex; auto.
      - apply (ex_integral_Rabs f); eauto.
      - intuition.
    }
    apply Rabs_case => ?.
    - apply Integral_mono; eauto. intros. apply Rabs_case; nra.
    - replace (- Integral f) with (-1 * Integral f) by nra.
      rewrite -Integral_scal; eauto.
      apply Integral_mono; eauto.
      * intros. apply Rabs_case; nra.
      * by apply ex_integral_scal.
  Qed.

  Lemma is_integral_ae_ge0 f v:
    almost_everywhere_meas μ (λ x, f x >= 0) →
    is_integral f v →
    v >= 0.
  Proof.
    intros Hae His.
    destruct Hae as (Hmeas&Hmeas0).
    generalize (sigma_closed_complements _ F _ Hmeas). rewrite compl_involutive => HF.
    eapply (is_integral_ae_ext _ (λ x, f x * wpt_fun (wpt_indicator _ HF) x))  in His.
    { eapply is_integral_ge0; eauto. intros. rewrite //= wpt_indicator_spec.
      destruct excluded_middle_informative as [Hc|Hnc]; nra.
    }
    - eapply ae_equal_mult_indicator_compl_0'; auto.
      eauto.
    - measurable. eauto.
  Qed.

  Lemma is_integral_ae_mono f1 v1 f2 v2:
    almost_everywhere_meas μ (λ x, f1 x <= f2 x) →
    is_integral f1 v1 →
    is_integral f2 v2 →
    v1 <= v2.
  Proof.
    intros Hle Hint1 Hint2.
    cut (0 <= v2 - v1); first by nra.
    assert (His: is_integral (λ x, f2 x - f1 x) (v2 - v1)).
    { apply is_integral_minus; auto. }
    apply is_integral_ae_ge0 in His; first nra.
    eapply almost_everywhere_meas_ext; eauto.
    intros x; split; nra.
  Qed.

  Lemma Integral_ae_mono f1 f2:
    almost_everywhere_meas μ (λ x, f1 x <= f2 x) →
    ex_integral f1 →
    ex_integral f2 →
    Integral f1 <= Integral f2.
  Proof.
    intros Hmono (v1&Heq1) (v2&Heq2).
    rewrite (is_integral_unique _ _ Heq1).
    rewrite (is_integral_unique _ _ Heq2).
    eapply is_integral_ae_mono; eauto.
  Qed.


  Lemma ex_integral_ae_mono_ex f1 f2:
    almost_everywhere_meas μ (λ x, Rabs (f1 x) <= f2 x) →
    measurable f1 F (borel _) →
    ex_integral f2 →
    ex_integral f1.
  Proof.
    intros Hae Hmeas Hex.
    destruct Hae as (Hmeas'&Hneg).
    generalize (sigma_closed_complements _ _ _ Hmeas') => H'.
    setoid_rewrite compl_involutive in H'.
    cut (ex_integral (λ x, f2 x * wpt_fun (wpt_indicator _ H') x)).
    {
      intros Hex_indic.
      assert (Hex': ex_integral (λ x, f1 x * wpt_fun (wpt_indicator _ H') x)).
      { eapply ex_integral_mono_ex; last eapply Hex_indic.
        * intros x => //=.
          rewrite ?wpt_indicator_spec. 
          destruct excluded_middle_informative; rewrite ?Rmult_1_r ?Rmult_0_r; try nra.
          rewrite Rabs_right; nra.
        * measurable.
      }
      eapply ex_integral_ae_ext; last eapply Hex'; auto.
      apply ae_equal_mult_indicator_compl_0; eauto.
    }
    eapply ex_integral_ae_ext; eauto.
    { eapply ae_equal_mult_indicator_compl_0'; eauto. }
    measurable.
  Qed.
    
End integral.

Hint Resolve is_integral_measurable ex_integral_measurable ex_integral_wpt ex_integral_const.

Arguments weighted_partition {_} _.