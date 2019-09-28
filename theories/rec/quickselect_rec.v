(* Use of Karp's theorem to bound probabilistic recurrence arising from quickselect *)
From discprob.basic Require Import base order nify exp_ext.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.rec Require Import karp.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier FunctionalExtensionality.
Require Import Psatz.
Require Import Coq.omega.Omega.
Require Import Ranalysis5.

Lemma Rabs_le_compat_pos x y:
  x ≤ y → 0 ≤ x → Rabs x ≤ Rabs y.
Proof.
  rewrite /Rabs. repeat destruct (Rcase_abs); intros; fourier.
Qed.

(* There must be a more general version of this in standard library *)
Lemma piecewise_continuity z f g r:
  continuity f →
  continuity g →
  (∀ x, x ≤ z → r x = f x) →
  (∀ x, x ≥ z → r x = g x) →
  continuity r.
Proof.
  rewrite /continuity/continuity_pt/continue_in/limit1_in/limit_in//=/R_dist/D_x//=.
  intros Hfc Hgc Hle Hge x eps Hgt0.
  destruct (Hfc x eps Hgt0) as (alpf&?&Hfc').
  destruct (Hgc x eps Hgt0) as (alpg&?&Hgc').
  case (Req_dec (x - z) 0).
  - intros Hdiff0. assert (x = z) as <- by (apply Rminus_diag_uniq; auto).
    exists (Rmin alpf alpg); split.
    + repeat apply Rmin_case; auto.
    + intros x'. 
      case: (Rle_dec x' x).
      * intros Hle'. rewrite (Hle x') // (Hle x) //=; last reflexivity. 
        intros (?&?); eapply Hfc'; split; auto.
        eapply Rlt_le_trans; eauto.
        apply Rmin_l.
      * move /Rnot_le_gt/Rgt_ge. intros Hge'. rewrite (Hge x') // (Hge x) //=; last fourier.
        intros (?&?); eapply Hgc'; split; auto.
        eapply Rlt_le_trans; eauto.
        apply Rmin_r.
  - intros Hneq. 
    exists (Rmin (Rmin alpf alpg) (Rabs (x - z))); split.
    + repeat apply Rmin_case; auto.
        by apply Rabs_pos_lt.
    + intros x'. 
      case: (Rle_dec x' z).
      * intros Hle'. 
        intros (?&Hmin).
        assert (x ≤ z).
        { apply Rnot_gt_le.
          intros Hgt. assert (x - z ≤ x - x') as Hdiff by fourier.
          apply Rabs_le_compat_pos in Hdiff; last fourier.
          eapply Rlt_le_trans in Hmin; last apply Rmin_r.
          rewrite (Rabs_minus_sym x x') in Hdiff.
          fourier.
        }
        rewrite (Hle x') // (Hle x) //=.
        eapply Hfc'; split; auto.
        eapply Rlt_le_trans; eauto.
        etransitivity; [apply Rmin_l | apply Rmin_l].
      * move /Rnot_le_gt/Rgt_ge => Hge'.
        intros (?&Hmin).
        assert (x ≥ z).
        { apply Rnot_lt_ge.
          intros Hgt. assert (z - x ≤ x' - x) as Hdiff by fourier.
          apply Rabs_le_compat_pos in Hdiff; last fourier.
          eapply Rlt_le_trans in Hmin; last apply Rmin_r.
          rewrite (Rabs_minus_sym z x) in Hdiff.
          fourier.
        }
        rewrite (Hge x') // (Hge x) //=.
        eapply Hgc'; split; auto.
        eapply Rlt_le_trans; eauto.
        etransitivity; [apply Rmin_l | apply Rmin_r].
Qed.

Lemma ln_continuity_pt: ∀ x, 0 < x → continuity_pt ln x.
Proof.
  move: ln_continue. rewrite /continuity_pt/continuity_pt.
  intros Hln x Hx z Hgt.
  edestruct (Hln x Hx z) as (alp&?&Halp); auto.
  exists (Rmin x alp). split.
  { apply Rmin_case; fourier. }
  intros x' ((?&?)&Hdist).
  eapply Halp; split; auto.
  - rewrite /D_x; split; auto.
    rewrite /Rlimit.dist //= /R_dist in Hdist. 
    eapply Rlt_le_trans in Hdist; last apply Rmin_l.
    destruct (Rge_dec x' x) as [?|?%Rnot_ge_lt]; first by fourier.
    rewrite Rabs_left in Hdist; fourier.
  - eapply Rlt_le_trans; last apply Rmin_r; eauto.
Qed.

Lemma piecewise_continuity' z f g r:
  (∀ x, x ≤ z → continuity_pt f x) →
  (∀ x, x ≥ z → continuity_pt g x) →
  (∀ x, x ≤ z → r x = f x) →
  (∀ x, x ≥ z → r x = g x) →
  continuity r.
Proof.
  rewrite /continuity/continuity_pt/continue_in/limit1_in/limit_in//=/R_dist/D_x//=.
  intros Hfc Hgc Hle Hge x eps Hgt0.
  destruct (Rtotal_order x z) as [Hlt|[<-|Hgt]].
  - destruct (Hfc x (Rlt_le _ _ Hlt) eps Hgt0) as (alpf&?&Hfc').
    exists (Rmin alpf (Rabs (x - z))); split.
    + repeat apply Rmin_case; auto.
        apply Rabs_pos_lt, Rlt_not_eq; fourier.
    + intros x'. 
      intros ((?&?)&Hmin).
        assert (x' ≤ z).
        { apply Rnot_gt_le.
          intros Hgt. assert (z - x ≤ x' - x) as Hdiff by fourier.
          apply Rabs_le_compat_pos in Hdiff; last fourier.
          eapply Rlt_le_trans in Hmin; last apply Rmin_r.
          rewrite (Rabs_minus_sym z x) in Hdiff.
          fourier.
        }
        rewrite (Hle x') // (Hle x) //=; try fourier.
        eapply Hfc'; split; auto.
        eapply Rlt_le_trans; eauto using Rmin_l. 
  - destruct (Hfc x (Rle_refl x) eps Hgt0) as (alpf&?&Hfc').
    destruct (Hgc x (Rge_refl x) eps Hgt0) as (alpg&?&Hgc').
    exists (Rmin alpf alpg); split.
    + repeat apply Rmin_case; auto.
    + intros x'. 
      case: (Rle_dec x' x).
      * intros Hle'. rewrite (Hle x') // (Hle x) //=; last reflexivity. 
        intros (?&?); eapply Hfc'; split; auto.
        eapply Rlt_le_trans; eauto.
        apply Rmin_l.
      * move /Rnot_le_gt/Rgt_ge. intros Hge'. rewrite (Hge x') // (Hge x) //=; last fourier.
        intros (?&?); eapply Hgc'; split; auto.
        eapply Rlt_le_trans; eauto.
        apply Rmin_r.
  - destruct (Hgc x (Rgt_ge _ _ Hgt) eps Hgt0) as (alpg&?&Hgc').
    exists (Rmin alpg (Rabs (x - z))); split.
    + repeat apply Rmin_case; auto.
        apply Rabs_pos_lt, Rgt_not_eq; fourier.
    + intros x'. 
      intros ((?&?)&Hmin).
        assert (x' ≥ z).
        { apply Rnot_lt_ge.
          intros Hlt. assert (x - z ≤ x - x') as Hdiff by fourier.
          apply Rabs_le_compat_pos in Hdiff; last fourier.
          eapply Rlt_le_trans in Hmin; last apply Rmin_r.
          rewrite (Rabs_minus_sym x x') in Hdiff.
          fourier.
        }
        rewrite (Hge x') // (Hge x) //=; try fourier.
        eapply Hgc'; split; auto.
        eapply Rlt_le_trans; eauto using Rmin_l. 
Qed.

Lemma piecewise_continuity_pt P z f g r:
  (∀ x, P x → x ≤ z → continuity_pt f x) →
  (∀ x, P x → x ≥ z → continuity_pt g x) →
  (∀ x, x < z → r x = f x) →
  (∀ x, x > z → r x = g x) →
  (P z → f z = g z ∧ f z = r z) →
  ∀ x, P x → continuity_pt r x.
Proof.
  rewrite /continuity/continuity_pt/continue_in/limit1_in/limit_in//=/R_dist/D_x//=.
  intros Hfc Hgc Hle Hge Hjoin x HP eps Hgt0.
  destruct (Rtotal_order x z) as [Hlt|[<-|Hgt]].
  - destruct (Hfc x HP (Rlt_le _ _ Hlt) eps Hgt0) as (alpf&?&Hfc').
    exists (Rmin alpf (Rabs (x - z))); split.
    + repeat apply Rmin_case; auto.
        apply Rabs_pos_lt, Rlt_not_eq; fourier.
    + intros x'. 
      intros ((?&?)&Hmin).
        assert (x' < z).
        { apply Rnot_ge_lt.
          intros Hgt. assert (z - x ≤ x' - x) as Hdiff by fourier.
          apply Rabs_le_compat_pos in Hdiff; last fourier.
          eapply Rlt_le_trans in Hmin; last apply Rmin_r.
          rewrite (Rabs_minus_sym z x) in Hdiff.
          fourier.
        }
        rewrite (Hle x') // (Hle x) //=; try fourier.
        eapply Hfc'; split; auto.
        eapply Rlt_le_trans; eauto using Rmin_l. 
  - destruct (Hfc x HP (Rle_refl x) eps Hgt0) as (alpf&?&Hfc').
    destruct (Hgc x HP (Rge_refl x) eps Hgt0) as (alpg&?&Hgc').
    exists (Rmin alpf alpg); split.
    + repeat apply Rmin_case; auto.
    + intros x'. 
      case: (Rle_dec x' x).
      * intros Hle'. 
        destruct Hle'.
        { rewrite (Hle x') //.
          destruct Hjoin as (Heq1&Heq2); auto.
          rewrite -Heq2.
          intros (?&?); eapply Hfc'; split; auto.
          eapply Rlt_le_trans; eauto.
          apply Rmin_l.
        }
        subst. intros. rewrite Rminus_diag_eq //. rewrite Rabs_R0. auto.
      * move /Rnot_le_gt/Rgt_ge. intros Hge'. 
        destruct Hge'.
        { rewrite (Hge x') //.
          destruct Hjoin as (Heq1&Heq2); auto.
          rewrite -Heq2 Heq1.
          intros (?&?); eapply Hgc'; split; auto.
          eapply Rlt_le_trans; eauto.
          apply Rmin_r.
        }
        subst. intros. rewrite Rminus_diag_eq //. rewrite Rabs_R0. auto.
  - destruct (Hgc x HP (Rgt_ge _ _ Hgt) eps Hgt0) as (alpg&?&Hgc').
    exists (Rmin alpg (Rabs (x - z))); split.
    + repeat apply Rmin_case; auto.
        apply Rabs_pos_lt, Rgt_not_eq; fourier.
    + intros x'. 
      intros ((?&?)&Hmin).
        assert (x' > z).
        { apply Rnot_le_gt.
          intros Hlt. assert (x - z ≤ x - x') as Hdiff by fourier.
          apply Rabs_le_compat_pos in Hdiff; last fourier.
          eapply Rlt_le_trans in Hmin; last apply Rmin_r.
          rewrite (Rabs_minus_sym x x') in Hdiff.
          fourier.
        }
        rewrite (Hge x') // (Hge x) //=; try fourier.
        eapply Hgc'; split; auto.
        eapply Rlt_le_trans; eauto using Rmin_l. 
Qed.

Lemma continuity_id: continuity id.
Proof.
  rewrite /continuity/continuity_pt/continue_in/limit1_in/limit_in//=/R_dist/D_x//=.
  intros x eps Hgt. 
  exists eps. split; auto.
  firstorder.
Qed.

Module recurrence_work.
Section recurrence_work.
  Definition X := list nat.
  Variable A B : X → finType.
  Variable ΩT : ∀ x : X, distrib (A x).
  Variable Ωh : ∀ x : X, distrib (B x).
  Variable T: ∀ x: X, rrvar (ΩT x).
  Variable h: ∀ x: X, rvar (Ωh x) [eqType of X].
  Definition d := 1.
  Definition size (x: X) := INR (length x).
  Hypothesis T_non_neg: ∀ x n, (T x) n ≥ 0.
  Hypothesis hrange1: ∀ x n, size ((h x) n) ≤ size x.
  Hypothesis hrange2: ∀ x n, 0 ≤ size x →  0 ≤ size ((h x) n).
  Definition umin := 4.

  Hypothesis Tbelow: ∀ x e, size x ≤ d → (T x) e ≤ umin.


  Definition a x := 
    if (Rle_dec x 1) then 
      0
    else
      x - 1.

  Hypothesis Trec: 
  ∀ x r,  pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h x)) 
                ((pr_eq (h x) (sval x')) * pr_gt (T (sval x')) (r - a (size x))).

  Definition m x := x * (3 / 4).

  Definition u x := 
    match Rle_dec x 1 with 
      | left _ => 4
      | _ => 4 * x
    end.

  Definition u' x :=
    match Rle_dec x 4 with
      | left _ => 1
      | _ => x / 4
    end.

  Lemma umin_non_neg: 0 ≤ umin.
  Proof. rewrite /umin; fourier. Qed.

  Variable m_bound_Eh: ∀ x, Ex (rvar_comp (h x) size) ≤ m (size x).
  
  Lemma u_mono x y: x ≤ y → u x ≤ u y.
  Proof.
    rewrite /u/a/m/d => Hle.
    do 2 destruct (Rle_dec) => //=; nra.
  Qed.

  Lemma u_strict_inc x y: x ≥ d → x < y → u x < u y.
  Proof.
    rewrite /u/a/m/d => Hle Hlt.
    do 2 destruct (Rle_dec) => //=; nra.
  Qed.

  Lemma u'_mono x y: x ≤ y → u' x ≤ u' y.
  Proof.
    rewrite /u'/a/m/d => Hle.
    do 2 destruct (Rle_dec) => //=; nra.
  Qed.
  
  Lemma u'_pos x: u' x > 0.
  Proof.                      
    rewrite /u'/a/m/d.
    do 1 destruct (Rle_dec) => //=; nra.
  Qed.

  Lemma u'u x: x ≤ u' (u x).
  Proof.
    rewrite /u/u'.
    do 2 destruct (Rle_dec) => //=; nra.
  Qed.

  Lemma u'_inv_above x: d < x → u' (u x) = x.
  Proof.     
    rewrite /u/u'/d.
    do 2 destruct (Rle_dec) => //=; nra.
  Qed.
  
  Lemma u_inv_above x: umin < x → u (u' x) = x.
  Proof.
    rewrite /u/u'/umin.
    do 2 destruct (Rle_dec) => //=; nra.
  Qed.
  
  Lemma ud_umin: u d = umin.
  Proof.
    rewrite /u/d/umin//=. destruct (Rle_dec) => //=; field. 
  Qed.
  

  Lemma u_cont: continuity u.
  Proof.
    apply piecewise_continuity with (g := λ x, 4 * x) (f := λ x, 4) (z := 1).
    - apply continuity_const => ? //.
    - apply continuity_mult.
      * apply continuity_const => ? //.
      * apply continuity_id.
    - rewrite /u => x. destruct (Rle_dec) => //=.
    - rewrite /u => x.
      destruct (Rle_dec) => //=; nra.
  Qed.

  Lemma a_cont: continuity a.
  Proof.
    apply piecewise_continuity with (g := λ x, x - 1) (f := λ x, 0) (z := 1).
    - apply continuity_const => ? //.
    - apply continuity_minus.
      * apply continuity_id.
      * apply continuity_const => ? //.
    - rewrite /a => x. destruct (Rle_dec) => //=.
    - rewrite /a => x.
      destruct (Rle_dec) => //=; nra.
  Qed.

  Lemma urec x: x > d → u x ≥ a x + u (m x).
  Proof.
    rewrite /u/a/m/d. 
    replace (4 * (x * (3 /4))) with (3 * x) by field.
    do 2 destruct Rle_dec => //=; nra.
  Qed.
  
  Lemma alower: ∀ x, x ≤ d → a x = 0.
  Proof.
    rewrite /a => x. destruct (Rle_dec) => //=; intros; nra.
  Qed.

  Lemma ainc: ∀ x x', d ≤ x → x < x' → a x < a x'.
  Proof.                                        
    rewrite /a/d => x x' Hle Hlt.
    assert (Hgt: x' > 1) by fourier.
    do 2 destruct (Rle_dec) => //=; intros; nra.
  Qed.
  
  Lemma a_nonneg: ∀ x, a x ≥ 0.
  Proof.
    intros. rewrite /a. 
    do 1 destruct (Rle_dec) => //=; intros; nra.
  Qed.

  Lemma a_pos: ∀ x, d < x → 0 < a x.
  Proof.
    rewrite /d/a => ??. 
    do 1 destruct (Rle_dec) => //=; intros; nra.
  Qed.

  Lemma a_mono: Rmono a. 
  Proof.                                        
    rewrite /a/d => x x' Hle.
    do 2 destruct (Rle_dec) => //=; intros; nra.
  Qed.

  Lemma mnondec: ∀ y y', 0 < y → y ≤ y' → (m y / y) ≤ (m y' / y').
  Proof.
    intros y y' Hlt Hle.
    rewrite /m.
    transitivity (3 /4); right; field; apply Rgt_not_eq; fourier.
  Qed.

  Lemma d_non_neg: 0 ≤ d.
  Proof. rewrite /d. fourier. Qed.

  (* Technically this follows solely from the assumption on m, but it also
     is a trivial consquence of the fact that (h x) <= ceil(x) - 1, we should
     prove it from the assumption on m, but we need more facts about recn *)
  Hypothesis hinf_0: ∀ a eps, eps > 0 → ∃ n, pr_gt (rvar_comp (recN_rvar h a n) size) d < eps. 

  Theorem bound x w: 
    size x > 1 →  pr_gt (T x) (4 * size x + INR w * (size x - 1)) ≤ (3/4)^w.
  Proof.
    intros Hgt1.
    replace (4 * size x) with (u (size x)); last first.
    {  rewrite /u. destruct (Rle_dec); first nra. done. }
    replace (size x - 1) with (a (size x)); last first.
    {  rewrite /a. destruct (Rle_dec); first nra. done. }
    etransitivity; first
    eapply karp_bound_simple with 
      (A := A)
      (B := B)
      (P := λ x, true)
      (T := T)
      (h := h)
      (umin := umin) 
      (d := d) 
      (u := u) 
      (a := a) 
      (m := m)
      (w := w).
    - apply umin_non_neg.
    - intros x' Hgt. 
      transitivity (a x' + u (m x') - a x').
      { rewrite /u/umin/d/m/a. do 2 destruct (Rle_dec) => //=; nra. }
      specialize (urec x'). nra.
    - apply u_mono.
    - apply u_strict_inc.
    - apply u'_mono.
    - apply u'_pos.
    - apply u'u.
    - apply u'_inv_above.
    - apply u_inv_above.
    - apply ud_umin.
    - apply m_bound_Eh.
    - intros. apply u_cont.
    - intros. eapply a_cont.
    - intros. apply Trec.
    - apply urec.
    - auto.
    - apply hrange1.
    - rewrite /d; intros. specialize (hrange2 x0). eapply hrange2. fourier. 
    - apply alower.
    - apply a_nonneg. 
    - apply a_mono.
    - apply a_pos.
    - apply mnondec.
    - apply d_non_neg.
    - apply hinf_0.
    - apply Tbelow.
    - rewrite /m. intros. fourier.
    - auto.
    - done.
    - rewrite /m. right. f_equal. field; nra.
  Qed.


End recurrence_work.
End recurrence_work.

Module recurrence_span.
Section recurrence_span.
  Definition X := list nat.
  Variable A B : X → finType.
  Variable ΩT: ∀ x: X, distrib (A x).
  Variable Ωh: ∀ x: X, distrib (B x).
  Variable T: ∀ x: X, rrvar (ΩT x).
  Variable h: ∀ x: X, rvar (Ωh x) [eqType of X].
  Definition d := 1.
  Definition size (x: X) := INR (length x).
  Hypothesis T_non_neg: ∀ x n, (T x) n ≥ 0.
  Hypothesis hrange1: ∀ x n, size ((h x) n) ≤ size x.
  Hypothesis hrange2: ∀ x n, 0 ≤ size x →  0 ≤ size ((h x) n).
  Definition umin := 1.
  Hypothesis Tbelow: ∀ x e, size x ≤ d → (T x) e ≤ umin.

  Definition a x := 
    match Rle_dec x 1 with
      | left _ => 0
      | _ => ln x
    end.

  Hypothesis Trec: 
    ∀ x r,  pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h x)) 
                  ((pr_eq (h x) (sval x')) * pr_gt (T (sval x')) (r - a (size x))).

  Definition m x := x * (3 / 4).
  
  Definition k := -/ ln(3/4).

  Definition u x := 
    match Rle_dec x 1 with 
      | left _ => 1
      | _ => ((k * ln x + 1) * (k * ln x + 1))
    end.

  Definition u' x :=
    match Rle_dec x 1 with
      | left _ => 1
      | _ => exp ((sqrt x - 1) / k)
    end.

  Lemma umin_non_neg: 0 ≤ umin.
  Proof. rewrite /umin; fourier. Qed.

  Variable m_bound_Eh: ∀ x, Ex (rvar_comp (h x) size) ≤ m (size x).

  Lemma kgt1: 1 < k.
  Proof.
    rewrite /k. replace (3 / 4) with (/ (4 /3)) by field.
    rewrite ln_Rinv; last fourier.
    assert (0 < ln (4 / 3)).
    { rewrite -ln_1. apply ln_increasing; fourier. }
    rewrite Ropp_inv_permute. 
    - rewrite Ropp_involutive.
      replace 1 with (/1) at 1 by field.
      apply Rinv_lt_contravar; first rewrite Rmult_1_r //.
      rewrite -[a in _ < a](ln_exp 1).
      apply ln_increasing; first fourier.
      apply (Rlt_le_trans _ 2); first fourier. 
      apply exp_ge_2.
    - apply Rlt_not_eq. fourier.
  Qed.

  Lemma kgt0: 0 < k.
  Proof.
    etransitivity; last apply kgt1. fourier.
  Qed.
  
  Lemma u_mono x y: x ≤ y → u x ≤ u y.
  Proof.
    rewrite /u/a/m/d => Hle.
    destruct (Rle_dec) as [Hle'|Hnle']; try nra;
    destruct (Rle_dec) as [Hle''|Hnle'']; try nra.
    - cut (0 ≤ ln y).
      { 
        intros. generalize kgt1 => ?.
        assert (k * ln y ≥ 0). 
        { transitivity (1 * ln y); last fourier.
          apply Rle_ge, Rmult_le_compat; try fourier.
        }
        rewrite -{1}Rsqr_1.
        apply Rsqr_incr_1; fourier.
      }
      left. by apply Rlt_0_ln; nra.
    - specialize (kgt0) => Hk.
      apply Rsqr_incr_1.
      apply Rplus_le_compat; last fourier.
      cut (ln x ≤ ln y).
      { 
        specialize (kgt0); cut (0 ≤ ln x); intros; first apply Rmult_le_compat; auto; try fourier.
        rewrite -(ln_1). left; apply ln_increasing; nra.
      }
      * inversion Hle; auto; subst; last by nra. left. apply ln_increasing; intros; nra.
      * apply Rnot_le_gt, ln_increasing in Hnle'; last fourier.
        rewrite (ln_1) in Hnle'. nra.
      * apply Rnot_le_gt, ln_increasing in Hnle''; last fourier.
        rewrite (ln_1) in Hnle''. nra.
  Qed.

  (* This basically covers half the case for the above, so could remove some redundancy *)
  Lemma u_strict_inc x y: x ≥ d → x < y → u x < u y.
  Proof.
    rewrite /u/a/m/d => Hle Hlt.
    destruct (Rle_dec) as [Hle'|Hnle']; try nra;
    destruct (Rle_dec) as [Hle''|Hnle'']; try nra.
    - specialize (kgt0) => Hk.
      replace 1 with (Rsqr 1) by (rewrite /Rsqr; field).
      assert (0 < k * ln y).
      { 
        apply Rmult_lt_0_compat; try fourier.
        apply Rlt_0_ln; fourier.
      }
      apply Rsqr_incrst_1; rewrite /Rsqr ?Rmult_1_r //=; try fourier.
    - specialize (kgt0) => Hk.
      apply Rsqr_incrst_1.
      apply Rplus_lt_compat_r.
      cut (ln x < ln y).
      { 
        specialize (kgt0); cut (0 < ln x); intros; first apply Rmult_lt_compat_l; auto; try fourier.
        rewrite -(ln_1); apply ln_increasing; nra.
      }
      * apply ln_increasing; intros; fourier.
      * apply Rnot_le_gt, ln_increasing in Hnle'; last fourier.
        rewrite (ln_1) in Hnle'.
        assert (0 ≤ k * ln x); nra.
      * apply Rnot_le_gt, ln_increasing in Hnle''; last fourier.
        rewrite (ln_1) in Hnle''.
        assert (0 ≤ k * ln y); nra.
  Qed.

  Lemma u'_mono x y: x ≤ y → u' x ≤ u' y.
  Proof.
    rewrite /u'/a/m/d => Hle.
    destruct (Rle_dec) as [Hle'|Hnle']; try nra;
    destruct (Rle_dec) as [Hle''|Hnle'']; try nra.
    - rewrite -{1}exp_0.
      left; apply exp_increasing.
      rewrite /Rdiv.
      apply Rlt_mult_inv_pos; last apply kgt0.
      cut (sqrt y > 1); intros; first fourier.
      rewrite -sqrt_1.
      apply Rnot_le_gt in Hnle''.
      apply Rlt_gt. 
      apply sqrt_lt_1; fourier.
    - apply Rnot_le_gt in Hnle'.
      apply Rnot_le_gt in Hnle''.
      apply exp_increasing_le.
      generalize (kgt0) => Hk.
      apply Rdiv_le_compat_contra; try fourier.
      * assert (1 < sqrt x).
        { rewrite -sqrt_1. apply sqrt_lt_1; fourier. }
        nra.
      * rewrite /Rminus. apply Rplus_le_compat_r.
        apply sqrt_le_1; fourier.
  Qed.
  
  Lemma u'_pos x: u' x > 0.
  Proof.                      
    rewrite /u'/a/m/d.
    do 1 destruct (Rle_dec) => //=; try nra.
    apply exp_pos.
  Qed.

  Lemma u'_inv_above x: d < x → u' (u x) = x.
  Proof.     
    rewrite /u/u'/d.
    destruct (Rle_dec) as [Hc1|?] => //=; try nra;
    destruct (Rle_dec) => //=; try nra.
    - intros. exfalso.
      assert (0 < ln x) by (apply Rlt_0_ln; auto).
      assert (0 < k * ln x) by (apply Rmult_lt_0_compat; auto using kgt0).
      assert (0 < (k * ln x) * (k * ln x)) by (repeat apply Rmult_lt_0_compat; auto using kgt0).
      rewrite ?Rmult_plus_distr_r in Hc1.
      rewrite ?Rmult_plus_distr_l in Hc1.
      fourier.
    - intros. rewrite -[a in _ = a]exp_ln; last fourier.
      f_equal.
      assert (0 < ln x) by (apply Rlt_0_ln; auto).
      assert (0 < k * ln x) by (apply Rmult_lt_0_compat; auto using kgt0).
      rewrite sqrt_Rsqr; last fourier.
      field. apply Rgt_not_eq, kgt0.
  Qed.

  Lemma u'u x: x ≤ u' (u x).
  Proof.
    destruct (Rlt_dec 1 x) as [Hlt|Hnlt].
    - rewrite u'_inv_above //. reflexivity.
    - rewrite /u/u'.
      apply Rnot_lt_le in Hnlt.
      destruct (Rle_dec) => //=; try nra.
      destruct (Rle_dec) => //=; try nra.
  Qed.
  
  Lemma u_inv_above x: umin < x → u (u' x) = x.
  Proof.
    rewrite /u/u'/umin.
    destruct (Rle_dec) as [Hc1|?] => //=; try nra;
    destruct (Rle_dec) as [?|?] => //=; try nra.
    - exfalso. rewrite -{2}exp_0 in Hc1.
      apply exp_le_embedding in Hc1. 
      assert (1 < sqrt x).
      { rewrite -sqrt_1. apply sqrt_lt_1; nra. }
      specialize (kgt1) => Hk.
      cut (0 < (sqrt x - 1) / k). 
      { by intros ?%Rlt_not_le. }
      apply Rdiv_lt_0_compat; fourier.
    - rewrite ln_exp. rewrite /Rdiv.
      transitivity (sqrt x * sqrt x).
      * field. apply Rgt_not_eq, kgt0. 
      * apply sqrt_sqrt. fourier.
  Qed.

  Lemma ud_umin: u d = umin.
  Proof.
    rewrite /u/d/umin//=. destruct (Rle_dec) => //=; nra.
  Qed.
  
  Lemma u_cont: continuity u.
  Proof.
    apply piecewise_continuity' with (g := λ x, (k * ln x + 1) * (k * ln x + 1))
                                      (f := λ x, 1) (z := 1).
    - intros; apply continuity_const => ? //.
    - intros. repeat apply continuity_pt_mult.
      * apply continuity_pt_plus.
        ** apply continuity_pt_mult.
           *** apply continuity_pt_const => ? //.
           *** apply ln_continuity_pt; fourier.
        ** apply continuity_pt_const => ? //.
      * apply continuity_pt_plus.
        ** apply continuity_pt_mult.
           *** apply continuity_pt_const => ? //.
           *** apply ln_continuity_pt; fourier.
        ** apply continuity_pt_const => ? //.
    - rewrite /u => x. destruct (Rle_dec) => //=; nra.
    - rewrite /u => x.
      destruct (Rle_dec) => //=; try nra; intros.
      assert (x = 1) as -> by (apply Rle_antisym; nra). 
      rewrite ln_1 Rmult_0_r Rplus_0_l Rmult_1_l. done.
  Qed.

  Lemma a_cont: continuity a.
  Proof.
    apply piecewise_continuity' with (g := ln) (f := λ x, 0) (z := 1).
    - intros; apply continuity_const => ? //.
    - intros. apply ln_continuity_pt; fourier.
    - rewrite /a => x. destruct (Rle_dec) => //=.
    - rewrite /a => x.
      destruct (Rle_dec) => //=; try nra; []; intros.
      assert (x = 1) as -> by (apply Rle_antisym; fourier).
      rewrite ln_1. done.
  Qed.

  Lemma urec x: x > d → u x ≥ a x + u (m x).
  Proof.
    rewrite /u/a/m/d. 
    destruct (Rle_dec) as [Hc1|Hc1] => //=; first by nra.
    destruct (Rle_dec) as [Hc2|Hc2] => //=.
    - transitivity ((k * ln x) * (k * ln x) + 2 * k * (ln x) + 1).
      { right. field. }
      assert (0 < ln x) by (apply Rlt_0_ln; auto).
      assert (0 < (k * ln x) * (k * ln x)) by (repeat apply Rmult_lt_0_compat; auto using kgt0).
      assert (2 * k * ln x > ln x). 
      { apply Rlt_gt. rewrite -[a in a < _](Rmult_1_l).
        apply Rmult_lt_compat_r; auto.
        generalize kgt1 =>?. fourier.
      }
      fourier.
    - assert (0 < ln x) by (apply Rlt_0_ln; auto; nra).
      rewrite ln_mult; try nra; [].
      rewrite (Rmult_plus_distr_l k _).
      assert (k * ln (3 / 4) = -1) as ->.
      { rewrite /k. field. apply Rlt_not_eq.
        rewrite -(ln_1). apply ln_increasing; fourier.
      }
      rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
      rewrite ?(Rmult_plus_distr_l).
      rewrite ?(Rmult_plus_distr_r).
      assert (k * ln x > ln x). 
      { apply Rlt_gt. rewrite -[a in a < _](Rmult_1_l).
        apply Rmult_lt_compat_r; auto.
        generalize kgt1 =>?. fourier.
      }
      nra.
  Qed.
  
  
  Lemma alower: ∀ x, x ≤ d → a x = 0.
  Proof.
    rewrite /a => x. destruct (Rle_dec) => //=; nra.
  Qed.

  Lemma a_nonneg: ∀ x, a x ≥ 0.
  Proof.
    intros. rewrite /a. destruct (Rle_dec) => //; first nra.
    left. apply Rlt_gt. apply Rlt_0_ln; nra.
  Qed.

  Lemma a_pos: ∀ x, d < x → 0 < a x.
  Proof.
    rewrite /d/a => ??. destruct (Rle_dec) => //; first nra.
    apply Rlt_gt. apply Rlt_0_ln; fourier.
  Qed.

  Lemma ainc: ∀ x x', d ≤ x → x < x' → a x < a x'.
  Proof.                                        
    rewrite /a/d => x x' Hle Hlt.
    assert (Hgt: x' > 1) by fourier.
    destruct (Rle_dec) => //;
    destruct (Rle_dec) => //; try nra; [|].
    - rewrite -ln_1. apply ln_increasing; fourier.
    - apply ln_increasing; fourier.
  Qed.

  Lemma a_mono: Rmono a. 
  Proof.                                        
    rewrite /Rmono. intros x x' Hle.
    inversion Hle; subst; try reflexivity.
    destruct (Rle_dec d x) as [?|?%Rnot_le_gt].
    * left. apply ainc; eauto.
    * rewrite alower; auto; try fourier.
      rewrite /a. destruct (Rle_dec).
      ** intros; fourier.
      ** left. apply Rlt_0_ln. nra.
  Qed.

  Lemma mnondec: ∀ y y', 0 < y → y ≤ y' → (m y / y) ≤ (m y' / y').
  Proof.
    intros y y' Hlt Hle.
    rewrite /m. transitivity (3 /4).
    -  right. field. apply Rgt_not_eq; fourier.
    -  right. field. apply Rgt_not_eq; fourier.
  Qed.

  Lemma d_non_neg: 0 ≤ d.
  Proof.
    rewrite /d. fourier.
  Qed.

  (* Technically this follows solely from the assumption on m, but it also
     is a trivial consquence of the fact that (h x) <= ceil(x) - 1, we should
     prove it from the assumption on m, but we need more facts about recn *)
  Hypothesis hinf_0: ∀ a eps, eps > 0 → ∃ n, pr_gt (rvar_comp (recN_rvar h a n) size) d < eps. 

  Theorem bound x w: 
    size x > 1 →  
    pr_gt (T x) ((k * ln (size x) + 1)² + INR w * ln (size x)) ≤ (3/4)^w.
  Proof.
    intros Hgt1.
    replace ((k * ln (size x) + 1)²) with (u (size x)); last first.
    {  rewrite /u. destruct (Rle_dec); first nra. rewrite //=. }
    replace (ln (size x) )with (a (size x)); last first.
    {  rewrite /a. destruct (Rle_dec); first nra. done. }
    etransitivity; first
    eapply karp_bound_simple with 
      (A := A)
      (B := B)
      (T := T)
      (P := λ x, true)
      (h := h)
      (umin := umin) 
      (d := d) 
      (u := u) 
      (a := a) 
      (m := m).
    - apply umin_non_neg.
    - cut (∀ x, umin ≤ u x).
      { intros Hcut x'. specialize (Hcut (m x')). intros. etransitivity; first eauto.
        specialize (urec x'). nra.
      }
      intros x'. destruct (Rle_dec x' d) as [Hle|Hnle%Rnot_le_gt].
      * rewrite /umin/u. move: Hle. rewrite /d. destruct (Rle_dec) => //=.  intros. nra.
      * rewrite -ud_umin. apply u_mono. fourier.
    - apply u_mono.
    - apply u_strict_inc.
    - apply u'_mono.
    - apply u'_pos.
    - apply u'u.
    - apply u'_inv_above.
    - apply u_inv_above.
    - apply ud_umin.
    - apply m_bound_Eh.
    - intros; apply u_cont.
    - intros; apply a_cont.
    - intros; apply Trec.
    - apply urec.
    - auto.
    - apply hrange1.
    - rewrite /d; intros. specialize (hrange2 x0). eapply hrange2. fourier. 
    - apply alower.
    - apply a_nonneg.
    - apply a_mono.
    - apply a_pos.
    - apply mnondec.
    - apply d_non_neg.
    - apply hinf_0.
    - apply Tbelow.
    - rewrite /m. intros. fourier.
    - auto.
    - done.
    - right. rewrite /m. f_equal. field. nra.
  Qed.


End recurrence_span.
End recurrence_span.
