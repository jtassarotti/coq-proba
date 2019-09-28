(* Use of Karp's theorem to bound probabilistic recurrence arising from quicksort *)
From discprob.basic Require Import base order nify exp_ext.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.rec Require Import karp span2 work2 quickselect_rec decreasing_rec.
From discprob.rec Require log_rec.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From Coquelicot Require Import Derive.
From Coquelicot Require AutoDerive.
From Interval Require Import Interval_tactic.
Require Import Reals Fourier FunctionalExtensionality.
Require Import Psatz.
Require Import Coq.omega.Omega.
Require Import Ranalysis5.

(* Assuming flatten takes log n *)
Module recurrence_span.
Section recurrence_span.
  Definition X := list nat.
  Variable A B : X → finType.
  Variable ΩT: ∀ x, distrib (A x).
  Variable Ωh: ∀ x, distrib (B x).
  Variable T: ∀ x: X, rrvar (ΩT x).
  Variable h: ∀ x: X, rvar (Ωh x) [eqType of X * X].
  Definition d := 1.
  Definition size (x: X) := INR (length x).
  Hypothesis T_non_neg: ∀ x n, (T x) n ≥ 0.
  Hypothesis hrange_sum: ∀ x n, size (fst ((h x) n)) + size (snd ((h x) n)) ≤ size x.
  Hypothesis hrange_sum': 
    ∀ x n, size x > 1 → size (fst ((h x) n)) + size (snd ((h x) n)) ≤ size x - 1.
  Hypothesis hrange11: ∀ x n, size (fst ((h x) n)) ≤ size x.
  Hypothesis hrange21: ∀ x n, size (snd ((h x) n)) ≤ size x.
  Hypothesis hrange12: ∀ x n, d < size x →  0 ≤ size (fst ((h x) n)).
  Hypothesis hrange22: ∀ x n, d < size x →  0 ≤ size (snd ((h x) n)).
  Definition umin := 1.

  Hypothesis Tbelow: ∀ x e, size x ≤ d → (T x) e ≤ umin.

  Definition a x := 
    match (Rle_dec x 1) with
      | left _ => 0
      | _ => ln x
    end.

  Hypothesis Trec: 
    ∀ x r, size x > d →  pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h x)) 
                        (pr_eq (h x) (sval x') * 
                         pr_gt (rvar_comp (rvar_pair (T (fst (sval x'))) (T (snd (sval x'))))
                                          (fun xy => Rmax (fst xy) (snd xy))) (r - a (size x))).

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

  Variable m_bound_Eh: 
    ∀ x, Ex (rvar_comp (h x) (λ x, Rmax (size (fst x)) (size (snd x)))) ≤ m (size x).
  Lemma Rlt_0_ln x: 1 < x → 0 < ln x.
  Proof.
    intros Hlt; rewrite -ln_1; apply ln_increasing; fourier.
  Qed.

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
  

  Theorem overhead_span_bound x w: 
    size x > 1 →  
    pr_gt (T x) ((k * ln (size x) + 1)² + INR w * ln (size x)) ≤ (size x) * (3/4)^w.
  Proof.
    intros Hgt1.
    replace ((k * ln (size x) + 1))² with (u (size x)); last first.
    { rewrite /u. destruct (Rle_dec); first nra. rewrite //=. }
    replace (ln (size x)) with (a (size x)); last first.
    { rewrite /a. destruct (Rle_dec); first nra. rewrite //=. }
    etransitivity. 
    eapply span_bound_simple with 
      (A := A)
      (B := B)
      (T := T)
      (h := h)
      (P := λ x, true)
      (umin := umin) 
      (d := d) 
      (u := u) 
      (a := a) 
      (m := m)
      (g := id).
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
    - intros. apply u_cont.
    - intros. apply a_cont.
    - intros. apply Trec; auto.
    - apply urec.
    - auto.
    - rewrite //=. intros. apply hrange_sum.
    - apply hrange11.
    - apply hrange21.
    - apply hrange12.
    - apply hrange22.
    - apply alower.
    - apply a_nonneg.
    - apply a_mono.
    - apply a_pos.
    - apply mnondec.
    - apply d_non_neg.
    - rewrite /m. intros. fourier.
    - eapply decreasing_rec.decreasing_rec_binary.hinf_0; eauto. 
      rewrite /d. fourier.
    - apply Tbelow.
    - rewrite /d/id //= => ??. fourier.
    - rewrite /d/id //= => ?.
    - intros => ??. rewrite /id => ?. fourier.
    - auto.
    - rewrite /d; auto.
    - auto.
    - right. rewrite /id/m.  f_equal. f_equal.
      field. nra.
  Qed.
End recurrence_span.
End recurrence_span.

(* Assuming flatten takes 0 time *)
Module recurrence_span2.
  
  Import log_rec.
  Module qs_factor <: rec_factor.
    Definition alpha := 3/4.
    Lemma alpha_range: 1/2 < alpha < 1.
    Proof. rewrite /alpha.  split; nra. Qed.
    Lemma ln_alpha: -/ln alpha > 1 /alpha. 
    Proof. rewrite /alpha. interval. Qed.
  End qs_factor.

  Module rec_solution := recurrence_log (qs_factor).
  Import rec_solution. 

  Section recurrence_span2_sec.
  Definition X := list nat.
  Variable A B : X → finType.
  Variable ΩT: ∀ x, distrib (A x).
  Variable Ωh: ∀ x, distrib (B x).
  Variable T: ∀ x: X, rrvar (ΩT x).
  Variable h: ∀ x: X, rvar (Ωh x) [eqType of X * X].
  Variable P: X → Prop.
  Variable hP: ∀ x n, P x → P (fst ((h x) n)) ∧ P (snd ((h x) n)).
  Definition size (x: X) := INR (length x).
  Hypothesis T_non_neg: ∀ x n, (T x) n ≥ 0.
  Hypothesis hrange_sum: ∀ x n, size (fst ((h x) n)) + size (snd ((h x) n)) ≤ size x.
  Hypothesis hrange_sum': 
    ∀ x n, size x > 1 → size (fst ((h x) n)) + size (snd ((h x) n)) ≤ size x - 1.
  Lemma hrange11: ∀ x n, size (fst ((h x) n)) ≤ size x.
  Proof.
    intros x n.
    generalize (hrange_sum x n). rewrite /size -?plus_INR.
    move /INR_le => ?. apply le_INR. nify. omega.
  Qed.
  Lemma hrange21: ∀ x n, size (snd ((h x) n)) ≤ size x.
  Proof.
    intros x n.
    generalize (hrange_sum x n). rewrite /size -?plus_INR.
    move /INR_le => ?. apply le_INR. nify. omega.
  Qed.
  Lemma hrange12: ∀ x n, d < size x →  0 ≤ size (fst ((h x) n)).
    intros x n. rewrite /size => ?. apply pos_INR.
  Qed.
  Lemma hrange22: ∀ x n, d < size x →  0 ≤ size (snd ((h x) n)).
    intros x n. rewrite /size => ?. apply pos_INR.
  Qed.

  Hypothesis Tbelow: ∀ x e, size x ≤ d → (T x) e = 0.

  Hypothesis Trec: 
  ∀ x r, P x → pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h x)) 
                        (pr_eq (h x) (sval x') * 
                         pr_gt (rvar_comp (rvar_pair (T (fst (sval x'))) (T (snd (sval x'))))
                                          (fun xy => Rmax (fst xy) (snd xy))) (r - a (size x))).
  Variable m_bound_Eh:
    ∀ x, Ex (rvar_comp (h x) (λ x, Rmax (size (fst x)) (size (snd x)))) ≤ m (size x).
  
  Lemma Rlt_0_ln x: 1 < x → 0 < ln x.
  Proof.
    intros Hlt; rewrite -ln_1; apply ln_increasing; fourier.
  Qed.

  Lemma size_non_neg x: 0 ≤ size x.
  Proof.
    rewrite /size. 
    induction x => //=.
    - rewrite /INR //=. fourier.
    - destruct (length x); nra.
  Qed.

  Lemma size_x_int x: size x > 1 → size x < 2 → False.
  Proof.
    rewrite /size.
    replace 2 with (INR 2) by auto.
    replace 1 with (INR 1) by auto.
    intros ?%INR_lt ?%INR_lt.
    omega.
  Qed.

  Import qs_factor.
                         
  Theorem qs_span_bound x w: 
    P x →
    size x > 1 →  
    pr_gt (T x) ((k * ln (size x) + 1) + INR w)
       ≤ (size x) * (3/4)^w.
  Proof.
    intros HP Hgt1.
    replace ((k * ln (size x) + 1)) with (u (size x)); last first.
    { rewrite /u. destruct (Rle_dec); first nra. rewrite //=. }
    replace (INR w) with (INR w * (a (size x))); last first.
    { rewrite /a. destruct (Rle_dec); try destruct (Rlt_dec); try nra. 
      exfalso; eapply size_x_int; eauto. }
    etransitivity; first
    eapply span_bound_simple with 
      (A := A)
      (B := B)
      (T := T)
      (h := h)
      (P := P)
      (umin := umin) 
      (d := d) 
      (u := u) 
      (a := a) 
      (g := id) 
      (m := m).
    - apply umin_non_neg.
    - cut (∀ x, umin ≤ u x).
      { intros Hcut x'. specialize (Hcut (m x')). intros. etransitivity; first eauto.
        specialize (urec0 x'). nra.
      }
      intros x'. destruct (Rle_dec x' d) as [Hle|Hnle%Rnot_le_gt].
      * rewrite /umin/u. move: Hle. rewrite /d. destruct (Rle_dec); nra.
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
    - intros. apply u_cont.
    - intros. apply a_cont_pt. done.
    - intros. apply Trec; auto.
    - apply urec0.
    - intros. auto.
    - intros. apply hrange_sum; auto.
    - apply hrange11.
    - apply hrange21.
    - apply hrange12.
    - apply hrange22.
    - apply alower.
    - apply a_nonneg. 
    - apply a_mono. 
    - apply a_pos.
    - apply mnondec.
    - apply d_non_neg.
    - rewrite /m/alpha. intros.
      destruct (Rlt_dec); nra.
    - eapply decreasing_rec.decreasing_rec_binary.hinf_0;
        eauto using hrange11, hrange12, hrange21, hrange22.
      rewrite /d. fourier.
    - intros. rewrite Tbelow // /umin. nra.
    - rewrite /d/id; intros; nra.
    - rewrite /d/id; intros; nra.
    - intros => ??? => //=; nra. 
    - auto.
    - rewrite /d; auto.
    - auto.
    - right. rewrite /id/m/alpha. destruct Rlt_dec.
      { exfalso.  eapply size_x_int; first eauto. nra. }
      f_equal. f_equal. field. nra.
  Qed.
      
End recurrence_span2_sec.
End recurrence_span2.

Module recurrence_work3.
Section recurrence_work3.
  Definition X := list nat.
  Variable A B : X → finType.
  Variable ΩT: ∀ x, distrib (A x).
  Variable Ωh: ∀ x, distrib (B x).
  Variable T: ∀ x: X, rrvar (ΩT x).
  Variable h: ∀ x: X, rvar (Ωh x) [eqType of X * X].
  Definition d := 1.
  Definition size (x: X) := INR (length x).
  Hypothesis T_non_neg: ∀ x n, (T x) n ≥ 0.
  Hypothesis hrange_sum: ∀ x n, size (fst ((h x) n)) + size (snd ((h x) n)) ≤ size x.
  Hypothesis hrange_sum': 
    ∀ x n, size x > 1 → size (fst ((h x) n)) + size (snd ((h x) n)) ≤ size x - 1.
  Lemma hrange11: ∀ x n, size (fst ((h x) n)) ≤ size x.
  Proof.
    intros x n.
    generalize (hrange_sum x n). rewrite /size -?plus_INR.
    move /INR_le => ?. apply le_INR. nify. omega.
  Qed.
  Lemma hrange21: ∀ x n, size (snd ((h x) n)) ≤ size x.
  Proof.
    intros x n.
    generalize (hrange_sum x n). rewrite /size -?plus_INR.
    move /INR_le => ?. apply le_INR. nify. omega.
  Qed.
  Lemma hrange12: ∀ x n, d < size x →  0 ≤ size (fst ((h x) n)).
    intros x n. rewrite /size => ?. apply pos_INR.
  Qed.
  Lemma hrange22: ∀ x n, d < size x →  0 ≤ size (snd ((h x) n)).
    intros x n. rewrite /size => ?. apply pos_INR.
  Qed.
  Definition umin := 1.

  Hypothesis Tbelow: ∀ x e, size x ≤ d → (T x) e = 0.

  Definition a x := 
    match Rle_dec x 1 with
      | left _ => 0
      | _ => x
    end.

  Definition g x := 
    match Rle_dec x 1 with
      | left _ => 1/2
      | _ =>
        match Rlt_dec x 2 with
        | left _ => x / (x - 1)
        | _ => x
        end
    end.

  Hypothesis Trec: 
  ∀ x r, pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h x)) 
                        (pr_eq (h x) (sval x') * 
                         pr_gt (rvar_comp (rvar_pair (T (fst (sval x'))) (T (snd (sval x'))))
                                          (fun xy => fst xy + snd xy)) (r - a (size x))).
  Definition m x :=
    match Rlt_dec x (4/3) with
      | left _ => 0
      | _ => x * (3 / 4)
    end.


  Definition k := -/ ln(3/4).

  Definition u x := 
    match Rle_dec x 1 with 
      | left _ => 1
      | _ => ((k * ln x + 1))
    end.

  Definition u' x :=
    match Rle_dec x 1 with
      | left _ => 1
      | _ => exp ((x - 1) / k)
    end.

  Lemma umin_non_neg: 0 ≤ umin.
  Proof. rewrite /umin; fourier. Qed.

  Variable m_bound_Eh:
    ∀ x, Ex (rvar_comp (h x) (λ x, Rmax (size (fst x)) (size (snd x)))) ≤ m (size x).
  
  Lemma Rlt_0_ln x: 1 < x → 0 < ln x.
  Proof.
    intros Hlt; rewrite -ln_1; apply ln_increasing; fourier.
  Qed.

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
    - 
      cut (0 ≤ ln y).
      { 
        intros. generalize kgt1 => ?.
        assert (k * ln y ≥ 0). 
        { transitivity (1 * ln y); last fourier.
          apply Rle_ge, Rmult_le_compat; try fourier.
        }
        fourier.
      }
      left. apply Rlt_0_ln; nra.
    - specialize (kgt0) => Hk.
      apply Rplus_le_compat; last nra.
      cut (ln x ≤ ln y).
      { 
        specialize (kgt0); cut (0 ≤ ln x); intros; first apply Rmult_le_compat; auto; try fourier.
        rewrite -(ln_1). left; apply ln_increasing; nra.
      }
      * inversion Hle; auto; subst; last by nra. left. apply ln_increasing; intros; nra.
  Qed.

  (* This basically covers half the case for the above, so could remove some redundancy *)
  Lemma u_strict_inc x y: x ≥ d → x < y → u x < u y.
  Proof.
    rewrite /u/a/m/d => Hle Hlt.
    destruct (Rle_dec) as [Hle'|Hnle']; try nra;
    destruct (Rle_dec) as [Hle''|Hnle'']; try nra.
    - specialize (kgt0) => Hk.
      assert (0 < k * ln y).
      { 
        apply Rmult_lt_0_compat; first nra.
        apply Rlt_0_ln; fourier.
      }
      rewrite ?Rmult_1_r //=; nra.
    - specialize (kgt0) => Hk.
      apply Rplus_lt_compat_r.
      cut (ln x < ln y).
      { 
        specialize (kgt0); cut (0 < ln x); intros; first apply Rmult_lt_compat_l; auto; try fourier.
        rewrite -(ln_1). apply ln_increasing; nra.
      }
      apply ln_increasing; nra.
  Qed.

  Lemma u'_mono x y: x ≤ y → u' x ≤ u' y.
  Proof.
    rewrite /u'/a/m/d => Hle.
    destruct (Rle_dec) as [Hle'|Hnle']; try nra;
    destruct (Rle_dec) as [Hle''|Hnle'']; try nra.
    - rewrite -{1}exp_0.
      left; apply exp_increasing.
      rewrite /Rdiv. apply Rlt_mult_inv_pos; last apply kgt0. nra.
    - apply exp_increasing_le.
      generalize (kgt0) => Hk.
      apply Rdiv_le_compat_contra; nra.
  Qed.
  
  Lemma u'_pos x: u' x > 0.
  Proof.                      
    rewrite /u'/a/m/d.
    destruct (Rle_dec _); try nra.
    apply exp_pos.
  Qed.

  Lemma u'_inv_above x: d < x → u' (u x) = x.
  Proof.     
    rewrite /u/u'/d.
    destruct (Rle_dec) as [Hc1|Hc1] => //=; try nra;
    destruct (Rle_dec) as [Hc2|Hc2] => //=; try nra.
    - intros. exfalso.
      assert (0 < ln x) by (apply Rlt_0_ln; auto).
      assert (0 < k * ln x) by (apply Rmult_lt_0_compat; auto using kgt0).
      assert (0 < (k * ln x) * (k * ln x)) by (repeat apply Rmult_lt_0_compat; auto using kgt0).
      nra.
    - rewrite -[a in _ = a]exp_ln; last nra.
      intros; do 1 f_equal. 
      assert (0 < ln x) by (apply Rlt_0_ln; auto).
      assert (0 < k * ln x) by (apply Rmult_lt_0_compat; auto using kgt0).
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
      specialize (kgt1) => Hk.
      cut (0 < (x - 1) / k). 
      { by intros ?%Rlt_not_le. }
      apply Rdiv_lt_0_compat; nra.
    - rewrite ln_exp. rewrite /Rdiv. intros.
      field. apply Rgt_not_eq, kgt0. 
  Qed.

  Lemma ud_umin: u d = umin.
  Proof.
    rewrite /u/d/umin//=.
    destruct (Rle_dec); nra.
  Qed.
  
  Lemma u_cont: continuity u.
  Proof.
    apply piecewise_continuity' with (g := λ x, (k * ln x + 1))
                                      (f := λ x, 1) (z := 1).
    - intros; apply continuity_const => ? //.
    - intros. repeat apply continuity_pt_mult.
      * apply continuity_pt_plus.
        ** apply continuity_pt_mult.
           *** apply continuity_pt_const => ? //.
           *** apply ln_continuity_pt; fourier.
        ** apply continuity_pt_const => ? //.
    - rewrite /u => x. destruct (Rle_dec); nra.
    - rewrite /u => x.
      destruct (Rle_dec); intros.
      * assert (x = 1) as -> by (apply Rle_antisym; fourier).
        rewrite ln_1 Rmult_0_r Rplus_0_l. done.
      * done.
  Qed.

  Lemma a_cont: ∀ x, d < x → continuity_pt a x.
  Proof.
    apply piecewise_continuity_pt with (g := λ x, x) (f := λ x, 0) (z := 1).
    - intros; apply continuity_const => ? //.
    - intros. apply continuity_id.
    - rewrite /a => x'. destruct (Rle_dec); nra.
    - rewrite /a => x'. destruct (Rle_dec); nra. 
    - rewrite /d; intros. fourier.
  Qed.

  Lemma g_cont_pt: ∀ x, d < x → continuity_pt g x.
  Proof.
    rewrite /d. intros. 
    apply piecewise_continuity_pt with (P := λ x, d < x)
                                               (g := λ x,  
                                                     match Rlt_dec x 2 with
                                                     | left _ => x / (x - 1)
                                                     | _ => x
                                                     end)
                                               (f := λ x, 1/2) (z := 1).
    - intros. apply continuity_const => ??. done.
    - intros. apply piecewise_continuity_pt with (g := λ x, x)
                                                 (f := λ x, x / (x - 1))
                                                 (z := 2) 
                                                 (P := λ x, d < x);
                try (intros; destruct (Rlt_dec); nra); try nra.
      * rewrite /d. intros. apply continuity_pt_div.
        ** apply continuity_id. 
        ** apply continuity_minus.
           *** apply continuity_id => ??.
           *** apply continuity_const => ??. done.
        ** nra. 
      * intros. apply continuity_id.
    - intros x'. rewrite /g. destruct Rle_dec; try nra; destruct Rlt_dec; nra. 
    - intros x'. rewrite /g. destruct Rle_dec; nra. 
    - rewrite /d. intros. fourier.
    - rewrite /d. fourier.
  Qed.
  
  Lemma k_ge_43:
    k > 4/3.
  Proof.
    (* k ~ 3.449 
      Sketch of proof strategy: suffices to show 4/3 log(4/3) < 1
      that is, (4/3)^(4/3) < e
      Have (4/3)^(4/3) < (4/3)^2 = 64/49 <= 2 < e.
    *) 
    assert (k = 1/ln(4/3)) as ->.
    { rewrite /k. rewrite Ropp_inv_permute; last first.
      { apply Rlt_not_eq. rewrite -ln_1. apply ln_increasing; fourier. }
      rewrite -ln_Rinv; last fourier. rewrite /Rdiv Rmult_1_l. f_equal.
      f_equal. field.
    }
    apply Rlt_gt. apply (Rmult_lt_reg_l (ln (4/3))).
    { rewrite -ln_1. apply ln_increasing; fourier. }
    rewrite /Rdiv Rmult_1_l Rinv_r; last first.
    { apply Rgt_not_eq, Rlt_gt. rewrite -ln_1. apply ln_increasing; fourier. }
    apply (Rle_lt_trans _ (ln (4 */ 3) * INR 2)).
    { apply Rmult_le_compat_l.
      * rewrite -ln_1. left. apply ln_increasing; nra.
      * rewrite /INR //=. fourier.
    }
    apply exp_lt_inv.
    replace (ln (4 */ 3) * INR 2) with (ln (4 */ 3) + ln (4 */ 3)); last by (rewrite //=; nra).
    rewrite exp_plus exp_ln //=; last fourier.
    eapply (Rlt_le_trans _  2); first fourier.
    apply exp_ge_2.
  Qed.

  Lemma kinv: /k = ln (4 / 3).
  Proof.
    rewrite /k. replace (3 / 4) with (/ (4 /3)) by field.
    rewrite ln_Rinv; last fourier.
    assert (0 < ln (4 / 3)).
    { rewrite -ln_1. apply ln_increasing; fourier. }
    rewrite Ropp_inv_permute. 
    - rewrite Ropp_involutive Rinv_involutive //.
      apply Rgt_not_eq; auto.
    - apply Rlt_not_eq. fourier.
  Qed.

  Lemma size_non_neg x: 0 ≤ size x.
  Proof.
    rewrite /size. 
    induction x => //=.
    - rewrite /INR //=. fourier.
    - destruct (length x); nra.
  Qed.

  Lemma size_x_int x: size x > 1 → size x < 2 → False.
  Proof.
    rewrite /size.
    replace 2 with (INR 2) by auto.
    replace 1 with (INR 1) by auto.
    intros ?%INR_lt ?%INR_lt.
    omega.
  Qed.

  Lemma ghrange_sum: ∀ x n, size x > d →
                            g (size (fst ((h x) n))) + g (size (snd ((h x) n))) ≤ g (size x).
  Proof.
    rewrite /d/g => x n Hgt.
    apply Rge_le. 
    repeat (destruct (Rle_dec); rewrite //=); repeat (destruct (Rlt_dec); rewrite //=); try nra;
    try (exfalso; eapply size_x_int; eauto; fail).
    - exfalso. eapply (size_x_int ((h x) n).2); eauto. 
      apply Rnot_le_gt. done.
    - generalize (size_non_neg ((h x) n).1) => //= ?.
      generalize (size_non_neg ((h x) n).2) => //= ?.
      generalize (hrange_sum' x n Hgt) => //= ?; nra.
    - exfalso. eapply (size_x_int ((h x) n).1); eauto. 
      apply Rnot_le_gt. done.
    - generalize (size_non_neg ((h x) n).1) => //= ?.
      generalize (size_non_neg ((h x) n).2) => //= ?.
      generalize (hrange_sum' x n Hgt) => //= ?; nra.
    - exfalso. eapply (size_x_int ((h x) n).2); eauto. 
      apply Rnot_le_gt. done.
    - exfalso. eapply (size_x_int ((h x) n).1); eauto. 
      apply Rnot_le_gt. done.
    - exfalso. eapply (size_x_int ((h x) n).2); eauto. 
      apply Rnot_le_gt. done.
    - generalize (size_non_neg ((h x) n).1) => //= ?.
      generalize (size_non_neg ((h x) n).2) => //= ?.
      generalize (hrange_sum' x n Hgt) => //= ?; nra.
  Qed.

  (* This could be cleaned up. *)
  Lemma urec0 x: x > d → u x ≥ a x / g x + u (m x).
  Proof.
    rewrite /u/a/m/d. 
    destruct (Rle_dec) as [Hc1|Hc1] => //=; first nra.
    destruct (Rle_dec) as [Hc2|Hc2] => //=.
    - rewrite /g. 
      destruct (Rle_dec) as [Hc3|Hc3]; try nra; [].
      destruct (Rlt_dec) as [?|?]. 
      { 
        destruct (Rlt_dec) as [?|?]; try nra; [].
        intros.
        transitivity (x - 1 +  1); last first.
        { right. field. nra. }
        cut (k * ln x > x - 1); first by (intros; fourier).
        cut (k * ln x - (x - 1) > 0); first by (intros; fourier).
        apply Rlt_gt.
        eapply (Rle_lt_trans _ (k * ln(1) - (1 - 1))).
        { right. rewrite ln_1 Rmult_0_r. field. }
        eapply incr_function_le with (f := λ x, k * ln x - (x - 1))
                                               (x := 1)
                                               (y := x)
                                               (a := 1)
                                               (b := 4/3)
                                               (df := λ x, k * 1/x - 1); try fourier; eauto.
        * rewrite //= => ???. AutoDerive.auto_derive; nra.
        * rewrite //=. intros x' ? ?.
          specialize (k_ge_43). intros. 
          cut (k */ x' > 1).
          { intros. set (p := k */ x'). assert (p > 1). rewrite /p. auto.
            nra.
          }
          apply Rlt_gt, (Rmult_lt_reg_r x'); first fourier.
          rewrite Rmult_assoc Rinv_l; first fourier.
          apply Rgt_not_eq; fourier.
        * rewrite //=. nra.
        * rewrite //=. nra.
      }
      assert (x = 4/3) as ->.
      { 
        apply (Rmult_le_compat_r (/(3/4))) in Hc2; last fourier.
        rewrite Rmult_assoc Rinv_r in Hc2; last first.
        { apply Rgt_not_eq. fourier. }
        replace (/ (3/4)) with (4/3) in Hc2 by field.
        rewrite Rmult_1_l Rmult_1_r in Hc2.
        apply Rle_antisym; nra.
      }
      destruct (Rlt_dec); last by nra.
      intros; rewrite -kinv Rinv_r; first fourier.
      apply Rgt_not_eq, kgt0.
    - assert (0 < ln x) by (apply Rlt_0_ln; nra).
      rewrite /g.
      destruct (Rle_dec); first by nra; intros.
      destruct (Rlt_dec); first by nra; intros.
      intros; rewrite ln_mult; try nra.
      rewrite (Rmult_plus_distr_l k _).
      assert (k * ln (3 / 4) = -1) as ->.
      { rewrite /k. field. apply Rlt_not_eq.
        rewrite -(ln_1). apply ln_increasing; fourier.
      }
      destruct Rlt_dec.
      * field_simplify; last nra.
        rewrite /Rdiv Rinv_1 Rmult_1_r. nra. 
      * rewrite /Rdiv Rinv_r; first fourier.
        apply Rgt_not_eq; fourier.
  Qed.

  Lemma alower: ∀ x, x ≤ d → a x = 0.
  Proof.
    rewrite /a => x; destruct (Rle_dec) => //=; nra.
  Qed.

  Lemma ainc: ∀ x x', d ≤ x → x < x' → a x < a x'.
  Proof.                                        
    rewrite /a/d => x x' Hle Hlt.
    assert (Hgt: x' > 1) by fourier.
    do 2 destruct (Rle_dec) => //=; try nra.
  Qed.

  Lemma a_nonneg: ∀ x, a x ≥ 0.
  Proof.
    intros. rewrite /a. destruct (Rle_dec); nra.
  Qed.

  Lemma a_pos: ∀ x, d < x → 0 < a x.
  Proof.
    rewrite /d/a => ??. destruct (Rle_dec); nra.
  Qed.

  Lemma a_mono: Rmono a. 
  Proof.                                        
    rewrite /Rmono. intros x x' Hle.
    inversion Hle; subst; try reflexivity.
    destruct (Rle_dec d x) as [?|?%Rnot_le_gt].
    * left. apply ainc; eauto.
    * rewrite alower; auto; try fourier.
      rewrite /a. destruct (Rle_dec); nra.
  Qed.

  Lemma mnondec: ∀ y y', 0 < y → y ≤ y' → (m y / y) ≤ (m y' / y').
  Proof.
    intros y y' Hlt Hle.
    rewrite /m.
    destruct (Rlt_dec).
    {  destruct (Rlt_dec). 
       - intros. rewrite /Rdiv ?Rmult_0_l. fourier.
       - intros. rewrite /Rdiv ?Rmult_0_l.
         rewrite Rmult_comm -Rmult_assoc Rinv_l; nra.
    }
    destruct (Rlt_dec); first by nra.
    intros. right. field. split; apply Rgt_not_eq; fourier.
  Qed.

  Lemma d_non_neg: 0 ≤ d.
  Proof.
    rewrite /d. fourier.
  Qed.
  
                         
  Theorem qs_work_bound x w: 
    size x > 1 →  
    pr_gt (T x) (size x * (k * ln (size x) + 1) + INR w * (size x))
       ≤ (size x) * (3/4)^w.
  Proof.
    intros Hgt1.
    replace ((k * ln (size x) + 1)) with (u (size x)); last first.
    {  rewrite /u. destruct (Rle_dec); first nra. rewrite //=. }
    assert (size x = a (size x)) as Heq.
    {  rewrite /a. destruct (Rle_dec); first nra. done. }
    rewrite {3}Heq; clear Heq.
    assert (size x = g (size x)) as Heq'.
    {  rewrite /g. destruct (Rle_dec); try destruct Rlt_dec; try nra.
       exfalso; eapply size_x_int; eauto. }
    rewrite {1}Heq'; clear Heq'.
    etransitivity; first
    eapply work_bound_simple with 
      (A := A)
      (B := B)
      (T := T)
      (h := h)
      (P := λ x, true)
      (umin := umin) 
      (d := d) 
      (u := u) 
      (a := a) 
      (g2 := g) 
      (g1 := id) 
      (m := m).
    - apply umin_non_neg.
    - cut (∀ x, umin ≤ u x).
      { intros Hcut x'. specialize (Hcut (m x')). intros. etransitivity; first eauto.
        specialize (urec0 x'). nra.
      }
      intros x'. destruct (Rle_dec x' d) as [Hle|Hnle%Rnot_le_gt].
      * rewrite /umin/u. move: Hle. rewrite /d. destruct (Rle_dec); nra.
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
    - intros. apply u_cont.
    - intros. apply a_cont. done.
    - eapply g_cont_pt.
    - apply T_non_neg.
    - intros; apply Trec.
    - apply urec0.
    - auto.
    - intros. apply hrange_sum; auto.
    - intros. apply ghrange_sum; auto.
    - apply hrange11.
    - apply hrange21.
    - apply hrange12.
    - apply hrange22.
    - rewrite /g => x'. destruct (Rle_dec); first by nra.
      destruct (Rlt_dec); last nra.
      transitivity 1; last nra.
      apply (Rmult_lt_reg_l (x' - 1)); first nra.
      field_simplify; nra. 
    - rewrite /g/d. intros. destruct (Rle_dec); last destruct (Rlt_dec); try nra. reflexivity.
    - intros. rewrite alower; auto. rewrite /Rdiv Rmult_0_l //.
    - intros x0. rewrite /a/g.
      destruct (Rle_dec); first by nra.
      apply Rle_ge. left. apply Rdiv_lt_0_compat.
        * nra.
        * destruct (Rlt_dec); last nra.
          transitivity 1; first nra. 
          apply (Rmult_lt_reg_l (x0 - 1)); first nra.
          field_simplify; nra. 
    - intros y z Hle. rewrite /a/g; destruct (Rle_dec) => //=. 
      * destruct Rle_dec => //=. 
        ** reflexivity. 
        ** rewrite {1}/Rdiv ?Rmult_0_l.
           left. apply Rdiv_lt_0_compat; first nra.
           destruct (Rlt_dec); last nra.
           transitivity 1; first nra. 
           apply (Rmult_lt_reg_l (z - 1)); first nra.
           field_simplify; last nra; nra. 
      * destruct (Rlt_dec).
        ** destruct (Rle_dec); first nra. 
           destruct (Rlt_dec); by (field_simplify; nra).
        ** destruct (Rle_dec); first nra. 
           destruct (Rlt_dec); first nra. 
           rewrite /Rdiv ?Rinv_r; nra.
    - intros x0 ?. apply Rdiv_lt_0_compat.
      * by apply a_pos.
      * rewrite /g. destruct (Rle_dec); last destruct (Rlt_dec); try nra; [].
        transitivity 1; first nra. 
        apply (Rmult_lt_reg_l (x0 - 1)); first nra.
        field_simplify; nra.
    - apply mnondec.
    - apply d_non_neg.
    - rewrite /m. intros.
      destruct (Rlt_dec); nra.
    - rewrite /d/id // => ??. fourier.
    - rewrite /d/id // => ??.
    - rewrite /id => ???. fourier.
    - eapply decreasing_rec.decreasing_rec_binary.hinf_0;
        eauto using hrange11, hrange12, hrange21, hrange22.
      rewrite /d. fourier.
    - intros. rewrite Tbelow // /Rdiv Rmult_0_l /umin; fourier.
    - auto.
    - rewrite /d; auto.
    - auto. 
    - right. rewrite /id/m. destruct Rlt_dec.
      { exfalso.  eapply size_x_int; first eauto. nra. }
      f_equal. f_equal. field. nra.
  Qed.
End recurrence_work3.
End recurrence_work3.
