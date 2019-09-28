(*

   We show here that under certain circumstances, finding tail bounds for work-like recurrences
   can be reduced to finding bounds for span-like recurrences of the form covered in span2.v.

 *)
From discprob.basic Require Import base order nify.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.rec Require Import karp span2.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier FunctionalExtensionality.
Require Import Psatz.
Require Import Coq.omega.Omega.
Require Import Ranalysis5.
Global Set Bullet Behavior "Strict Subproofs".

Section work_bound_sec.

Variable X: eqType.
Variable size: X → R.
Variable A B : X → finType.
Variable ΩT: ∀ x, distrib (A x).
Variable Ωh: ∀ x, distrib (B x).
Variable T: ∀ x: X, rrvar (ΩT x).
Variable h: ∀ x: X, rvar (Ωh x) [eqType of X * X]%type.
Variable P: X → Prop.
Variable g1 g2: R → R.
Variable a: R → R.
Variable m: R → R.
Variable u u': R → R.
Variable d: R.
Hypothesis umin: R.
Hypothesis umin_non_neg: 0 ≤ umin.
Hypothesis umin_lb: ∀ x, x > d → umin ≤ u x - a x / g2 x.
Variable u_mono: ∀ x y, x ≤ y → u x ≤ u y.
Variable u_strict_inc: ∀ x y, x ≥ d → x < y → u x < u y.
Variable u'_mono: ∀ x y, x ≤ y → u' x ≤ u' y.
Variable u'_pos: ∀ x,  u' x > 0.
Variable u'u: ∀ x, (* d < x → *) x ≤ u' (u x).
Variable u'_inv_above: ∀ z, d < z → u' (u z) = z.
Variable u_inv_above: ∀ z, umin < z → u (u' z) = z.
Variable ud_umin: u d = umin.
Variable m_bound_Eh: ∀ x, Ex (rvar_comp (h x) (λ x, Rmax (size (fst x)) (size (snd x)))) ≤ m (size x).

Variable u_cont: ∀ x, d < x → continuity_pt u x.
Variable a_cont: ∀ x, d < x → continuity_pt a x.
Variable g_cont: ∀ x, d < x → continuity_pt g2 x.

Hypothesis T_non_neg: ∀ x n, (T x) n ≥ 0.

Hypothesis Trec: 
  ∀ x r, P x → pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h x)) 
                        (pr_eq (h x) (sval x') * 
                         pr_gt (rvar_comp (rvar_pair (T (fst (sval x'))) (T (snd (sval x'))))
                                          (fun xy => fst xy + snd xy)) (r - a (size x))).

Hypothesis urec: 
  ∀ x, x > d →  u x ≥ a x / g2 x + u (m x).

Hypothesis hP: ∀ x n, P x → P (fst ((h x) n)) ∧ P (snd ((h x) n)).
Hypothesis hg1range_sum:
  ∀ x n, size x > d → g1 (size (fst ((h x) n))) + g1 (size (snd ((h x) n))) ≤ g1 (size x).
Hypothesis hg2range_sum:
  ∀ x n, size x > d → g2 (size (fst ((h x) n))) + g2 (size (snd ((h x) n))) ≤ g2 (size x).
Hypothesis hrange11: ∀ x n, size (fst ((h x) n)) ≤ size x.
Hypothesis hrange21: ∀ x n, size (snd ((h x) n)) ≤ size x.
Hypothesis hrange12: ∀ x n, d < size x →  0 ≤ size (fst ((h x) n)).
Hypothesis hrange22: ∀ x n, d < size x →  0 ≤ size (snd ((h x) n)).

Hypothesis g1_pos: ∀ x, g1 x > 0.
Hypothesis g2_pos: ∀ x, g2 x > 0.
Hypothesis gmin: R.
Hypothesis g_below: ∀ x, x ≤ d → g2 x = gmin.
Hypothesis aglower: ∀ x, x ≤ d → a x / g2 x = 0.
Hypothesis ag_nonneg: ∀ x, a x / g2 x ≥ 0.
Hypothesis ag_mono: Rmono (λ x, a x / g2 x).
Hypothesis ag_pos: ∀ x, d < x → 0 < a x / g2 x.
Hypothesis mnondec: ∀ y y', 0 < y → y ≤ y' → (m y / y) ≤ (m y' / y').
Hypothesis d_non_neg: 0 ≤ d.
Hypothesis mpos: ∀ x, 0 ≤ x → 0 ≤ m x.
Hypothesis g1d: ∀ x, x > d → g1 x ≥ 1.
Hypothesis g1pos: ∀ x, 0 ≤ x → 0 ≤ g1 x.
Hypothesis g1_mono: Rmono g1.

Definition Bn (nx: nat * X) : finType := B (snd nx).
Definition Ωn (nx: nat * X) := Ωh (snd nx).
Definition hpath (φ: nat → bool) (nx: nat * X) : rvar (Ωn nx) [eqType of nat * X].
  destruct nx as (n, x).
  apply mkRvar.
  intros i.
  exact (match (φ n) with
         | true =>  (S n, fst ((h x) i))
         | false => (S n, snd ((h x) i))
         end).
Defined.

(* This could be weakend; I think what's needed is to say it in the limit 
   it's bounded above by 2^-n *)
Hypothesis hinf_0: ∀ a, ∃ n, ∀ φ, pr_gt (rvar_comp (recN_rvar (hpath φ) (O, a) n)
                                                  (λ x, size (snd x))) d = 0.

Hypothesis Tbelow: ∀ x e, size x ≤ d → (T x) e / gmin  ≤ umin.


Definition K r z := pr (rvar_dist (T z)) (λ n, Rgt_dec ((T z) n) r).

Definition H (x: X) : rrvar (ΩT x) := rvar_comp (T x) (λ v, v / (g2 (size x))).

Definition Kg r z := pr (rvar_dist (H z)) (λ n, Rgt_dec ((H z) n) r).

Lemma umin_lb_simple: ∀ x, x ≥ d → umin ≤ u x.
Proof.
  rewrite /Rge => x [Hgt|Heq].
  - transitivity (u x - a x / g2 x); first auto. assert (a x / g2 x > 0) by (apply ag_pos; auto).
    nra.
  - subst. reflexivity.
Qed.

Lemma Kg_K r z: g2 (size z) > 0 → Kg r z = K (g2 (size z) * r) z.
Proof.                  
  intros Hsize.
  rewrite /Kg /K /H. 
  rewrite pr_gt_alt_comp pr_gt_alt. 
  apply eq_bigr => i ?.
  destruct (Rgt_dec) as [Hlt|Hge]; rewrite /is_left.
  - rewrite /Rdiv in Hlt. apply (Rmult_lt_compat_r (g2 (size z))) in Hlt; last first.
    { fourier. }
    rewrite Rmult_assoc Rinv_l in Hlt; last first.
    { apply Rgt_not_eq; eauto. }
    rewrite Rmult_1_r Rmult_comm in Hlt.
    destruct (Rgt_dec) => //=.
  - apply Rnot_gt_ge in Hge.
    rewrite /Rdiv in Hge. apply (Rmult_ge_compat_r (g2 (size z))) in Hge; last first.
    { left. eauto. }
    rewrite Rmult_assoc Rinv_l in Hge; last first.
    { apply Rgt_not_eq; eauto. }
    rewrite Rmult_1_r Rmult_comm in Hge.
    apply Rge_not_lt in Hge.
    destruct (Rgt_dec) => //=.
Qed.

Lemma K_Kg r z: g2 (size z) > 0 → K r z = Kg (r / g2 (size z)) z.
Proof.
  intros; rewrite Kg_K; eauto. replace (g2 (size z) * (r / g2 (size z))) with r; auto.
  field. apply Rgt_not_eq; eauto.
Qed.


Lemma Hrec: 
  ∀ x r, P x → size x > d →  pr_gt (H x) r ≤ \big[Rplus/0]_(x' : imgT (h x)) 
                        ((pr_eq (h x) (sval x')) *
                         pr_gt (rvar_comp (rvar_pair (H (fst (sval x'))) (H (snd (sval x'))))
                                        (fun xy => Rmax (fst xy) (snd xy))) 
                                              (r - a (size x) / g2 (size x))).
Proof.
 intros.
 rewrite /pr_gt. specialize (Kg_K); rewrite /Kg; intros ->; last by eauto.
 etransitivity. rewrite /K. apply Trec; auto.
 apply Rle_bigr => i Hin.
 apply Rmult_le_compat_l. 
 { rewrite /pr_eq. apply Rge_le, ge_pr_0. }
 rewrite /pr_gt /pr. 
 rewrite ?SeriesC_fin_big.
 rewrite -?big_mkcondr.
 apply Rle_bigr' => i' Hin'; auto.
 * intros. split; last reflexivity.
   move /andP in Hin'. destruct Hin' as (Hin'&Hgt).
   apply /andP; split; auto.
   destruct (Rgt_dec) as [Hgt'|?] => //= ; [].
   destruct (Rgt_dec) as [?|Hngt] => //=; [].
   exfalso; apply Hngt.
   destruct i as (i&?). rewrite //=.
   assert (∃ n, h x n = i) as (n&Hh).
   { apply img_alt. done. }
   subst.
   generalize Hgt'; intros Hlt%Rgt_lt.
   apply (Rplus_lt_compat_r (a (size x))) in Hlt.
   rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_r in Hlt.
   apply (Rmult_lt_compat_l (/g2 (size x))) in Hlt; last first.
   { apply Rinv_0_lt_compat. apply g2_pos; auto. }
   rewrite -Rmult_assoc Rinv_l in Hlt; last first.
   { apply Rgt_not_eq; eauto. }
   rewrite Rmult_1_l in Hlt. 
   rewrite ?Rmult_plus_distr_l in Hlt.
   rewrite /Rminus.
   apply (Rplus_lt_compat_r (- (/ g2 (size x) * a (size x)))) in Hlt.
   rewrite /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r in Hlt.
   rewrite /Rdiv. rewrite Rmult_comm. rewrite //= in Hlt. 
   eapply Rlt_le_trans. 
   { rewrite Rmult_comm. apply Hlt. }
   assert (T ((h x) n).1 i'.1 =
   ( g2 (size ((h x) n).1) * (T ((h x) n).1) i'.1 * / g2 (size ((h x) n).1))) as Hdiv1.
   { rewrite Rmult_comm -Rmult_assoc Rinv_l; first by rewrite Rmult_1_l. 
     apply Rgt_not_eq, g2_pos. }
   assert (T ((h x) n).2 i'.2 =
   ( g2 (size ((h x) n).2) * (T ((h x) n).2) i'.2 * / g2 (size ((h x) n).2))) as Hdiv2.
   { rewrite Rmult_comm -Rmult_assoc Rinv_l; first by rewrite Rmult_1_l. 
     apply Rgt_not_eq, g2_pos. }
   rewrite {1}Hdiv1.
   rewrite {1}Hdiv2.
   apply Rmax_case_strong => Hle.
   ** etransitivity.
      { apply Rplus_le_compat_l.
        apply Rmult_le_compat_l.
        { apply Rinv_pos, g2_pos. }
        rewrite Rmult_assoc.
        apply Rmult_le_compat_l.
        { left. apply g2_pos. } 
        apply Hle.
      }
      rewrite Rmult_assoc. 
      rewrite -Rmult_plus_distr_l.
      rewrite (Rmult_comm (T _ _)).
      rewrite -Rmult_plus_distr_r.
      rewrite -Rmult_assoc.
      rewrite -[a in _ ≤ a]Rmult_1_l. apply Rmult_le_compat_r.
      { rewrite Rmult_comm. apply Rle_mult_inv_pos.
        - apply Rge_le, T_non_neg.
        - apply g2_pos.
      }
      apply (Rmult_le_reg_l (g2 (size x))).
      { apply g2_pos. }
      rewrite -Rmult_assoc Rinv_r //; last first.
      { apply Rgt_not_eq, g2_pos. }
      rewrite Rmult_1_l Rmult_1_r. eauto.
   ** etransitivity.
      { apply Rplus_le_compat_r.
        apply Rmult_le_compat_l.
        { apply Rinv_pos, g2_pos. }
        rewrite Rmult_assoc.
        apply Rmult_le_compat_l.
        { left. apply g2_pos. } 
        rewrite Rmult_comm; apply Hle.
      }
      rewrite Rmult_assoc. 
      rewrite -Rmult_plus_distr_l.
      rewrite -Rmult_plus_distr_r.
      rewrite -Rmult_assoc.
      rewrite -[a in _ ≤ a]Rmult_1_l. apply Rmult_le_compat_r.
      { apply Rle_mult_inv_pos.
        - apply Rge_le, T_non_neg.
        - apply g2_pos.
      }
      apply (Rmult_le_reg_l (g2 (size x))).
      { apply g2_pos. }
      rewrite -Rmult_assoc Rinv_r //; last first.
      { apply Rgt_not_eq, g2_pos. }
      rewrite Rmult_1_l Rmult_1_r. eauto.
 * intros. apply Rge_le, pmf_pos.
Qed.

Lemma Kg_work_bound: 
  ∀ r x, P x → Kg r x ≤ span2.D g1 (λ x, a x / g2 x) m u u' d (umin)  r (size x).
Proof.
  intros. 
  eapply span_bound; eauto.
  - intros. apply continuity_pt_div; auto.
    apply Rgt_not_eq, g2_pos; fourier.
  - apply Hrec.
  - rewrite /H //=.  intros. 
    rewrite g_below /Rdiv; eauto.
Qed.

Lemma work_bound: ∀ r x, P x → K r x ≤ span2.D g1 (λ x, a x / g2 x) m u u' d umin (r / g2 (size x)) (size x).
  intros. rewrite K_Kg; last apply g2_pos.
  apply Kg_work_bound; auto.
Qed.

Lemma work_bound_simple w x:
  g1 (size x) > 1 →
  size x > d →
  P x → pr_gt (T x) (g2 (size x) * u (size x) + INR w * a (size x)) 
              ≤ g1 (size x) * (m (size x) / size x) ^ w.
Proof.
  set (r := g2 (size x) * (u (size x)) + INR w * (a (size x))).
  intros.
  transitivity (span2.D g1 (λ x, a x / g2 x) m u u' d umin (r / g2 (size x)) (size x)).
  - apply work_bound.  auto.
  - rewrite /D/r.
  destruct (Rle_dec) as [Hle|?].
     { rewrite //=. destruct w; first by (rewrite //=; nra).
         assert (umin <= u (size x)) by (apply umin_lb_simple; nra).
         assert (a (size x) / g2 (size x) > 0) as Hag by (apply ag_pos; nra).
         specialize (g2_pos (size x)).
         assert (a (size x) > 0). 
         { apply Rgt_lt, (Rmult_lt_compat_r (g2 (size x))) in Hag; last by nra.
           rewrite /Rdiv Rmult_assoc Rinv_l in Hag; last by nra.
           nra.
         }
         specialize (pos_INR w).
         intros. rewrite S_INR in Hle. exfalso.
         rewrite /Rdiv Rmult_plus_distr_r in Hle.
         rewrite /Rdiv in Hag.
         rewrite Rmult_comm in Hle. 
         rewrite -Rmult_assoc in Hle. 
         rewrite Rinv_l in Hle; last nra.
         rewrite Rmult_1_l in Hle. nra.
     }
     rewrite //=. 
     destruct Rle_dec => //=; try nra; [].
     destruct Rle_dec as [Hle|?].
     { intros. rewrite //=.
       destruct w. 
       { replace (INR 0) with 0 by auto. rewrite Rmult_0_l Rplus_0_r.
         specialize (g2_pos (size x)).
         rewrite /Rdiv Rmult_comm -Rmult_assoc Rinv_l; last by nra.
         rewrite Rmult_1_l.
         rewrite u'_inv_above; last nra.
         apply Rmax_case_strong; nra. 
       }
       assert (umin <= u (size x)) by (apply umin_lb_simple; nra).
         assert (a (size x) / g2 (size x) > 0) as Hag by (apply ag_pos; nra).
         specialize (g2_pos (size x)).
         assert (a (size x) > 0). 
         { apply Rgt_lt, (Rmult_lt_compat_r (g2 (size x))) in Hag; last by nra.
           rewrite /Rdiv Rmult_assoc Rinv_l in Hag; last by nra.
           nra.
         }
         specialize (pos_INR w).
         intros. rewrite S_INR in Hle. exfalso. 
         rewrite /Rdiv Rmult_plus_distr_r in Hle.
         rewrite /Rdiv in Hag.
         rewrite Rmult_comm in Hle. 
         rewrite -Rmult_assoc in Hle. 
         rewrite Rinv_l in Hle; last nra.
         rewrite Rmult_1_l in Hle. nra.
     }
     rewrite //=.
     assert ((round (λ x0 : R, a x0 / g2 x0) u
         ((g2 (size x) * u (size x) + INR w * a (size x)) / g2 (size x)) 
         (size x)) = (Z_of_nat w)) as Hround.
     { 
       rewrite /round.
       assert ((((g2 (size x) * u (size x) + INR w * a (size x)) / g2 (size x) 
                 - u (size x)) / (a (size x) / g2 (size x))) = INR w) as ->.
       { assert (a (size x) / g2 (size x) > 0) as Hag by (apply ag_pos; nra).
         specialize (g2_pos (size x)).
         assert (a (size x) > 0). 
         { apply Rgt_lt, (Rmult_lt_compat_r (g2 (size x))) in Hag; last by nra.
           rewrite /Rdiv Rmult_assoc Rinv_l in Hag; last by nra.
           nra.
         }
         field.
         split; nra.
       }
        rewrite INR_IZR_INZ Rceil_IZR. done.
     }
     rewrite Hround //= INR_IZR_INZ. 
     rewrite (Rmult_comm (IZR _)).
     assert ((g2 (size x) * u (size x) + a (size x) * IZR (Z.of_nat w)) / g2 (size x)
             - a (size x) / g2 (size x) * IZR (Z.of_nat w)
             = u (size x)) as ->.
     { field. specialize (g2_pos (size x)); nra.  }
     rewrite u'_inv_above; last by nra.
     rewrite /Rdiv. rewrite (Rmult_assoc (g1 (size x))). 
     rewrite Rinv_r; last by nra. rewrite Rmult_1_r.
      rewrite Nat2Z.id. nra.
Qed.

End work_bound_sec.
