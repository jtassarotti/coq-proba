From discprob.basic Require Import base order nify.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.rec Require Import karp quickselect_rec log_rec decreasing_rec.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From Coquelicot Require Import Derive.
From Coquelicot Require AutoDerive.
From Interval Require Import Interval_tactic.
Require Import Reals Fourier FunctionalExtensionality.
Require Import Psatz.
Require Import Coq.omega.Omega.
Require Import Ranalysis5.

Module recurrence_leader.
  Import log_rec.
  Module count_factor <: rec_factor.
    Definition alpha := 3/4.
    Lemma alpha_range: 1/2 < alpha < 1.
    Proof. rewrite /alpha.  split; nra. Qed.
    Lemma ln_alpha: -/ln alpha > 1 /alpha. 
    Proof. rewrite /alpha. interval. Qed.
  End count_factor.
  
  Module rec_solution := recurrence_log (count_factor).
  Import rec_solution. 


Section recurrence_leader_sec.
  Definition X := (nat * nat)%type.
  Variable A B : X → finType.
  Variable ΩT : ∀ x : X, distrib (A x).
  Variable Ωh : ∀ x : X, distrib (B x).
  Variable T: ∀ x: X, rrvar (ΩT x).
  Variable h: ∀ x: X, rvar (Ωh x) [eqType of X].
  Variable P: X → Prop.
  Variable hP: ∀ x n, P x → P (((h x) n)).
  Definition size (x: X) :=
    match fst x with
    | O => 0
    | _ => INR (snd x)
    end.
  Definition msr (x: X) := INR (fst x).
  Hypothesis T_non_neg: ∀ x n, (T x) n ≥ 0.
  Hypothesis hmsr_dec: ∀ x n, size x > 1 → msr ((h x) n) ≤ msr x - 1.
  Hypothesis hrange1: ∀ x n, size ((h x) n) ≤ size x.
  Hypothesis hrange2: ∀ x n, d < size x →  0 ≤ size ((h x) n).

  Hypothesis Tbelow: ∀ x e, size x ≤ d → (T x) e = 0.

  Hypothesis Trec: 
    ∀ x r,  pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h x)) 
                  ((pr_eq (h x) (sval x')) * pr_gt (T (sval x')) (r - a (size x))).

  Variable m_bound_Eh: ∀ x, Ex (rvar_comp (h x) size) ≤ m (size x).
  
  Lemma size_x_int x: size x > 1 → size x < 2 → False.
  Proof.
    rewrite /size.
    replace 2 with (INR 2) by auto.
    replace 1 with (INR 1) by auto.
    replace 0 with (INR 0) by auto.
    destruct x. rewrite /fst. destruct n; rewrite /snd;
    intros ?%INR_lt ?%INR_lt; omega.
  Qed.
                         
  Theorem leader_bound x w: 
    P x →
    size x > 1 →  
    pr_gt (T x) ((k * ln (size x) + 1) + INR w) ≤ (3/4)^w.
  Proof.
    intros HP Hgt1.
    replace ((k * ln (size x) + 1)) with (u (size x)); last first.
    {  rewrite /u. destruct (Rle_dec); first nra. rewrite //=. }
    replace (INR w) with (INR w * a (size x)); last first.
    { rewrite /a.  destruct Rle_dec; try destruct Rlt_dec; try nra.
      exfalso; eapply size_x_int; eauto. } 
    etransitivity; first
    eapply karp_bound_simple with 
      (A := A)
      (B := B)
      (T := T)
      (h := h)
      (P := P)
      (umin := umin) 
      (d := d) 
      (u := u) 
      (a := a) 
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
    - intros. apply hrange1; auto.
    - intros. apply hrange2. nra. 
    - apply alower.
    - apply a_nonneg. 
    - apply a_mono. 
    - apply a_pos.
    - apply mnondec.
    - apply d_non_neg.
    - eapply decreasing_rec.decreasing_rec.hinf_0 with (msr := msr) (msr_cutoff := 0);
        rewrite /d; eauto using hmsr_dec, hrange1, hrange2.
      nra. rewrite /msr/size. intros (r, p) ? Hle. etransitivity; eauto.
      rewrite /size//=. rewrite //= in Hle.
      destruct r; try nra.
      rewrite S_INR in Hle. specialize (pos_INR r). nra.
    - intros. rewrite Tbelow // /umin. nra.
    - rewrite /m/count_factor.alpha. intros.
      destruct (Rlt_dec); nra.
    - auto.
    - done. 
    - right. rewrite /id/m/count_factor.alpha. destruct Rlt_dec.
      { exfalso.  eapply size_x_int; first eauto. nra. }
      f_equal. field. nra.
  Qed.
      

End recurrence_leader_sec.
End recurrence_leader.