From discprob.basic Require Import base order nify.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.rec Require Import karp.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier FunctionalExtensionality.
Require Import Psatz.
Require Import Coq.omega.Omega.
Require Import Ranalysis5.
Global Set Bullet Behavior "Strict Subproofs".

Lemma Rlt_plus_reg a b a' b': a + b < a' + b' → (a < a') ∨ (b < b').
Proof.
  intros.
  destruct (Rlt_dec a a') as [|?%Rnot_lt_ge]; first by auto. 
  destruct (Rlt_dec b b') as [|?%Rnot_lt_ge]; first by auto. 
  fourier.
Qed.

Section lemma31_simplex.

Variable A: finType.
Variable B: eqType.
Variable Ω: distrib A.
Variable X: rvar Ω [eqType of B * B].
Variable size: B → R.
Variable g: R → R.
Variable f: R → R.
Variable x c: R.

Hypothesis xgt : x > 0.
Hypothesis cgt : c > 0.
Hypothesis Xrange11: ∀ r,  r \in img X → 0 ≤ size (fst r).
Hypothesis Xrange21: ∀ r,  r \in img X → 0 ≤ size (snd r).
Hypothesis Xrange12: ∀ r,  r \in img X → size (fst r) ≤ x.
Hypothesis Xrange22: ∀ r,  r \in img X → size (snd r) ≤ x.
Hypothesis grange1: ∀ r,  r \in img X → 0 ≤ g (size (fst r)).
Hypothesis grange2: ∀ r,  r \in img X → 0 ≤ g (size (snd r)).
Hypothesis grange_sum: ∀ r,  r \in img X → g (size (fst r)) + g (size (snd r)) ≤ g x.

Hypothesis f0: f 0 = 0.
Hypothesis frange1: ∀ x,  0 ≤ f x. 
Variable z : R.
Hypothesis zgt1 : z ≥ 1.
Hypothesis frange2: ∀ y, y ≥ c → f y = z.

Hypothesis fnondec: ∀ y y', 
    (y ≤ y') ∧ 
    (0 < y ∧ y ≤ c) ∧
    (0 < y' ∧ y' ≤ c) →
    (f y / y) ≤ (f y' / y').

Lemma min_xc_gt: Rmin x c > 0.
Proof. by apply Rmin_case. Qed.
Lemma min_xc_neq0: Rmin x c ≠ 0.
Proof. eapply Rlt_not_eq'. apply min_xc_gt. Qed.

Lemma fmono_aux y y': 
  0 ≤ y → y ≤ y' → y' ≤ c → f y ≤ f y'.
Proof.
  intros Hge0 Hle Hlec.
  inversion Hge0; last first.
  { subst. rewrite f0; eauto. }
  assert (f y / y ≤ f y' / y') as Hdiv.
  { eapply fnondec. repeat split; eauto; try fourier. }
  apply (Rmult_le_reg_r (/ y')).
  { apply Rinv_0_lt_compat; fourier. }
  transitivity (f y / y); last by auto.
  rewrite /Rdiv. apply Rmult_le_compat; auto; try fourier.
  * left. apply Rinv_0_lt_compat; fourier.
  * apply Rinv_le_contravar; fourier.
Qed.

Lemma fmono y y': 
  0 ≤ y → y ≤ y' → f y ≤ f y'.
Proof.
  intros Hge0 Hle.
  destruct (Rle_dec y' c) as [?|Hgt%Rnot_le_gt]; first apply fmono_aux; eauto.
  destruct (Rle_dec y c) as [?|Hgt'%Rnot_le_gt].
  - rewrite (frange2 y'); last fourier.
    rewrite -(frange2 c); last fourier.
    apply fmono_aux; auto; fourier.
  - rewrite (frange2 y'); last fourier.
    rewrite (frange2 y); last fourier.
    reflexivity.
Qed.

Lemma lemma31_simplex: Ex (rvar_comp X (λ r, (g (size (fst r))) * f (size (fst r)) +
                                           (g (size (snd r))) * f (size (snd r))))
                                   ≤ (Ex (rvar_comp X (λ r, Rmax (size (fst r)) (size (snd r)))))
                                          * (g x * f (Rmin x c) / (Rmin x c)).
Proof.
  rewrite /Rdiv Rmult_comm.
  rewrite ?Ex_fin_pt.
  rewrite big_distrr//=.
  apply (Rle_bigr) => r Hin. 
  - rewrite -?Rmult_assoc.  
    apply (Rmult_le_compat_r (rvar_dist X r)); first by (auto using Rge_le, pmf_pos).
     etransitivity.
     { apply Rplus_le_compat; apply Rmult_le_compat_l.
       - apply grange1, img_alt. exists r. auto. 
       - apply (fmono _ (Rmax (size (fst (X r))) (size (snd (X r))))).
         * apply Xrange11, img_alt. exists r. auto. 
         * apply Rmax_l. 
       - apply grange2, img_alt. exists r. auto. 
       - apply (fmono _ (Rmax (size (fst (X r))) (size (snd (X r))))).
         * apply Xrange21, img_alt. exists r. auto. 
         * apply Rmax_r. 
     }
     rewrite -Rmult_plus_distr_r.
     rewrite ?Rmult_assoc.
     apply Rmult_le_compat; eauto.
     {
       - replace 0 with (0 + 0) by field.
         apply Rplus_le_compat.
         * apply grange1, img_alt. exists r. auto. 
         * apply grange2, img_alt. exists r. auto. 
     }
     { apply grange_sum, img_alt. exists r. auto. }
     set (y := Rmax (size (fst (X r))) (size (snd (X r)))).
     rewrite -?/y.
     assert (y ≤ x).
     { 
       rewrite /y. apply Rmax_case.
       * apply Xrange12, img_alt; eauto.
       * apply Xrange22, img_alt; eauto.
     }
     assert (g y ≤ g x).
     { 
       assert (0 ≤ (g (size ((fst (X r)))))); first apply grange1, img_alt; eauto.
       assert (0 ≤ (g (size ((snd (X r)))))); first apply grange2, img_alt; eauto.
       rewrite /y; transitivity (g (size (X r).1) + g (size (X r).2)).
       - apply Rmax_case; fourier.
       - apply grange_sum, img_alt; eauto.
     }
     assert (0 ≤ y) as [Hgt|HX0].
     { 
       rewrite /y; apply Rmax_case; [ eapply Xrange11 | eapply Xrange21]; apply img_alt; 
       exists r; eauto. 
     }
     * apply (Rmult_le_reg_r (Rdiv 1 y)). 
         apply Rdiv_lt_0_compat; fourier. 
         transitivity (f (Rmin x c) / (Rmin x c)); last first.
         *** apply Req_le. field; split.
             **** by apply Rlt_not_eq'.
             **** apply min_xc_neq0.
         *** rewrite -Rmult_assoc.
             rewrite Rmult_1_r.
             destruct (Rlt_or_le y c).
             **** eapply fnondec; repeat split; auto; try fourier.
                  { apply Rmin_case; fourier. }
                  { apply Rmin_case; fourier. }
                  { apply Rmin_r. }
             **** assert (Rmin x c = c) as ->.
                  { apply Rmin_right. fourier. }
                  rewrite frange2; last fourier.
                  rewrite frange2; last fourier.
                  rewrite /Rdiv. apply Rmult_le_compat; try fourier.
                  { apply Rlt_le. apply Rinv_0_lt_compat. fourier. }
                  eapply Rinv_le_contravar; fourier.
     * rewrite -HX0 f0 Rmult_0_r. fourier.
Qed.

End lemma31_simplex.

Section span_bound_sec.

Variable X: eqType.
Variable size: X → R.
Variable g: R → R.
Variable A B : X → finType.
Variable ΩT: ∀ x, distrib (A x).
Variable Ωh: ∀ x, distrib (B x).
Variable T: ∀ x: X, rrvar (ΩT x).
Variable h: ∀ x: X, rvar (Ωh x) [eqType of X * X]%type.
Variable P: X → Prop.
Variable a: R → R.
Variable m: R → R.
Variable u u': R → R.
Variable d: R.
Hypothesis umin: R.
Hypothesis umin_non_neg: 0 ≤ umin.
Hypothesis umin_lb: ∀ x, x > d → umin ≤ u x - a x.
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

Hypothesis T_non_neg: ∀ x n, (T x) n ≥ 0.

Hypothesis Trec: 
  ∀ x r, P x → size x > d →  pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h x)) 
                        (pr_eq (h x) (sval x') * 
                         pr_gt (rvar_comp (rvar_pair (T (fst (sval x'))) (T (snd (sval x'))))
                                          (fun xy => Rmax (fst xy) (snd xy))) (r - a (size x))).
(*
Hypothesis Trec: 
  ∀ x r,  pr (T x) r = \rsum_(x' <- img (h x)) 
                        (pr (h x) x') * pr (comp_rv (pair_rv (T (fst x')) (T (snd x')))
                                        (fun xy => Rmax (fst xy) (snd xy))) (r - a (size x)).
*)

Hypothesis urec: 
  ∀ x, x > d →  u x ≥ a x + u (m x).

Hypothesis hP: ∀ x n, P x → P (fst ((h x) n)) ∧ P (snd ((h x) n)).
(* Hypothesis hrange_sum: ∀ x n, size (fst ((h x) n)) + size (snd ((h x) n)) ≤ size x. *)
Hypothesis hgrange_sum: ∀ x n, size x > d → g (size (fst ((h x) n))) + g (size (snd ((h x) n))) ≤ g (size x).
(* FIXME: 11, 21 follow from sum And 12 22 *)
Hypothesis hrange11: ∀ x n, size (fst ((h x) n)) ≤ size x.
Hypothesis hrange21: ∀ x n, size (snd ((h x) n)) ≤ size x.
Hypothesis hrange12: ∀ x n, d < size x →  0 ≤ size (fst ((h x) n)).
Hypothesis hrange22: ∀ x n, d < size x →  0 ≤ size (snd ((h x) n)).

Hypothesis alower: ∀ x, x ≤ d → a x = 0.
Hypothesis a_nonneg: ∀ x, a x ≥ 0.
Hypothesis a_mono: Rmono a.
Hypothesis a_pos: ∀ x, d < x → 0 < a x.
Hypothesis mnondec: ∀ y y', 0 < y → y ≤ y' → (m y / y) ≤ (m y' / y').
Hypothesis d_non_neg: 0 ≤ d.
Hypothesis mpos: ∀ x, 0 ≤ x → 0 ≤ m x.

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

(*
Definition Krecfun φ (i: nat) r x : R := Krec _ (λ x, size (snd x)) _ (hpath φ) a umin i r x.
*)

(* This could be weakend; I think what's needed is to say it in the limit 
   it's bounded above by 2^-n *)
Hypothesis hinf_0: ∀ a, ∃ n, ∀ φ, pr_gt (rvar_comp (recN_rvar (hpath φ) (O, a) n)
                                                  (λ x, size (snd x))) d = 0.

Hypothesis Tbelow: ∀ x e, size x ≤ d → (T x) e ≤ umin.
Hypothesis gd: ∀ x, x > d → g x ≥ 1.
Hypothesis gpos: ∀ x, 0 ≤ x → 0 ≤ g x. 
Hypothesis g_mono: Rmono g.


Definition K r z := pr (rvar_dist (T z)) (λ n, Rgt_dec ((T z) n) r).

Lemma umin_lb_simple: ∀ x, x ≥ d → umin ≤ u x.
Proof.
  rewrite /Rge => x [Hgt|Heq].
  - transitivity (u x - a x); first auto. assert (a x > 0) by (apply a_pos; auto).
    fourier.
  - subst. reflexivity.
Qed.

Lemma K_alt4 r z: 
  P z →
  size z > d →
  K r z ≤ \big[Rplus/0]_(i : imgT (h z)) ((pr_eq (h z) (sval i) 
                                             * ((K (r - (a (size z))) (fst (sval i))) +
                                                (K (r - (a (size z))) (snd (sval i)))))).
Proof.
  rewrite {1}/K. 
  etransitivity. 
  { etransitivity; first apply Trec; last reflexivity; auto. }
  apply Rle_bigr.  intros (x'&Hin) _. 
  set (Trecpair := rvar_comp (rvar_pair (T x'.1) (T x'.2)) (λ xy, Rmax (fst xy) (snd xy))); 
    rewrite -/Trecpair.
  apply Rmult_le_compat_l; first by (rewrite /pr_eq; apply Rge_le, ge_pr_0). 
  set (pred_combined := (fun x: (A (fst x')) * A (snd x') =>
                           Rgt_dec (Rmax ((T x'.1) x.1) (T x'.2 x.2)) 
                                   (r - a (size z))) : pred (A (fst x') * A (snd x'))).
  set (predA := (fun x: (A (fst x')) * A (snd x') =>
                           Rgt_dec (T (fst x') (fst x))
                                   (r - a (size z))) : pred (A (fst x') * A (snd x'))).
  set (predB := (fun x: (A (fst x')) * A (snd x') =>
                           Rgt_dec (T (snd x') (snd x))
                                   (r - a (size z))) : pred (A (fst x') * A (snd x'))).
    assert (Heq: pred_combined =i predU predA predB). 
    { 
      intros y. rewrite /in_mem//=/pred_combined/predA/predB/predU.
      apply Rmax_case_strong => Hcase; 
      destruct (Rgt_dec) as [Hgt|Hnotgt] => //=; try nra;
      destruct (Rgt_dec) as [Hgt'|Hnotgt'] => //=; try nra;
      rewrite //= in Hgt', Hnotgt, Hcase; nra. 
    }
   rewrite /pr_gt.
   rewrite (pr_eq_pred _ _ _ Heq).
   etransitivity; first apply pr_union_le.
   rewrite /K/Trecpair//=.
   apply Rplus_le_compat; right.
   - rewrite /predA.
     by rewrite (rvar_pair_marginal1 (T (fst x')) (T (snd x'))
                 ((λ x, Rgt_dec ((T x'.1) x) (r - a (size z))))).
   - rewrite /predB.
     by rewrite (rvar_pair_marginal2 (T (fst x')) (T (snd x'))
                 ((λ x, Rgt_dec ((T x'.2) x) (r - a (size z))))).
Qed.


Definition K0 r (z: X) :=
  if (Rlt_dec r umin) then
    1
  else
    0.

Fixpoint Krec i r x := 
  match i with
    | 0 => K0 r x
    | S i' => Rmin 1 (Ex (rvar_comp (h x) (fun x' => Krec i' (r - a (size x)) (fst x') + 
                                           Krec i' (r - a (size x)) (snd x'))))
  end.


Definition round r x := Rceil ((r - u x) / a x).

Definition D r x := 
  if Rle_dec r umin then
    1
  else
    if Rle_dec x d then
        0
    else
      if Rle_dec r (u x) then
         Rmax 1 (g (u' r))
      else
        (m x / x)^(Z.to_nat (round r x)) * (g(x) * x / (u' (r - a(x) * IZR (round r x)))).

Definition Dalt r x := 
  if Rle_dec r umin then
    1
  else
    if Rle_dec x d then
        0
    else
      if Rlt_dec r (u x) then
         Rmax 1 (g (u' r))
      else
        (m x / x)^(Z.to_nat (round r x)) * (g(x) * x / (u' (r - a(x) * IZR (round r x)))).


Lemma D_Dalt_equiv r x:
  D r x = Dalt r x.
Proof.
  rewrite /Dalt /D.
  destruct (Rle_dec) as [?|Hgt] => //=. 
  apply Rnot_le_gt in Hgt.
  destruct (Rle_dec) as [?|Hgt'] => //=. 
  apply Rnot_le_gt in Hgt'.
  destruct (Rle_dec) as [Hle|?] => //=.
  - inversion Hle as [Hlt|Heq].
    * destruct (Rlt_dec) => //=.
    * subst. destruct (Rlt_dec) => //=.
      assert (round (u x) x = 0%Z) as ->.
      { 
        rewrite /round. rewrite -Rceil_0. f_equal.
        rewrite Rminus_diag_eq // /Rdiv Rmult_0_l //.
      }
      rewrite //= Rmult_0_r /Rminus Ropp_0 Rplus_0_r u'_inv_above //=.
      rewrite /Rdiv Rmult_1_l. rewrite Rmax_right; first field. 
      ** apply Rgt_not_eq; nra.
      ** apply Rge_le, gd; fourier.
  - destruct (Rlt_dec) => //=. 
    intros. exfalso. nra. 
Qed.

Lemma K_0 r z: r < 0 → K r z = 1.
Proof.
  intros Hlt. rewrite /K /pr.
  rewrite -(pmf_sum1_Series (rvar_dist (T z))).
  rewrite ?SeriesC_fin_big.
  eapply eq_big; auto. 
  intros x Hin.
  destruct (Rgt_dec) as [?|Hngt] => //=.
  exfalso; apply Hngt.
  eapply Rlt_le_trans; eauto.
  apply Rge_le, T_non_neg.
Qed.

Lemma K_unfold r x: P x → size x > d → 
                    K r x ≤ Ex (rvar_comp (h x) (fun x' => K (r - a (size x)) (fst x') +
                                                         K (r - a (size x)) (snd x'))).
Proof.
  intros; etransitivity; first apply K_alt4; auto.
  rewrite Ex_fin_comp. 
  right; apply eq_bigr => ??. by rewrite Rmult_comm.
Qed.
  
Lemma Krec_non_decS: ∀ (i: nat) r x, Krec i r x ≤ Krec (S i) r x.
Proof.
  induction i as [|i'] => r x.
  - rewrite /Krec. rewrite Ex_fin_pt //= /K0.
    destruct (Rlt_dec) as [H|H];
    rewrite //= /rvar_comp //=.
    * destruct Rlt_dec as [|Hfalse]. 
      ** apply Rmin_case_strong; intros; first nra.
         rewrite //=. rewrite -big_distrr //=. rewrite -SeriesC_fin_big pmf_sum1_Series. nra.
      ** exfalso. eapply Hfalse.
         specialize (a_nonneg (size x)). nra.
    * destruct Rlt_dec as [|].
      ** apply Rmin_case_strong; intros; first fourier.
         rewrite //=. rewrite -big_distrr //=. rewrite -SeriesC_fin_big pmf_sum1_Series. nra.
      ** apply Rmin_case_strong; intros; first fourier. 
         rewrite //=. rewrite -big_distrr //=. rewrite -SeriesC_fin_big pmf_sum1_Series. nra.
  - rewrite /Krec -/Krec. apply Rle_min_compat_l.
    rewrite ?Ex_fin_pt.
    apply (Rle_bigr) => i hin. 
    rewrite //=. etransitivity. 
    * apply Rmult_le_compat_r.
      { apply Rge_le, pmf_pos. }
      { apply Rplus_le_compat; eapply IHi'. }
    * rewrite //= ?Ex_fin_pt /rvar_comp //=; reflexivity.
Qed.

Lemma Krec_non_dec (i i': nat) r x: (i ≤ i')%nat → Krec i r x ≤ Krec i' r x.
Proof.
  induction 1; first reflexivity.
  etransitivity; [ apply IHle | apply Krec_non_decS ]. 
Qed.

Lemma Krec_bound0 r x i: 0 ≤ Krec i r x.
Proof.
  revert r x.
  induction i => r x. 
  - rewrite //=. rewrite /K0. destruct Rlt_dec => //=; nra.
  - rewrite /Krec -/Krec Ex_fin_pt /rvar_comp //=.
    apply Rmin_case; first fourier.
    apply Rle_big0 => ??. 
    rewrite -[a in a ≤ _](Rmult_0_l 0).
    apply Rmult_le_compat; try fourier.
    * replace 0 with (R0 + R0) by rewrite Rplus_0_l //=. apply Rplus_le_compat; eauto.
    * apply Rge_le, pmf_pos.
Qed.

Lemma Krec0_bound01 r x: 0 ≤ Krec 0 r x ∧ Krec 0 r x ≤ 1.
Proof.
  revert r x.
  rewrite //= /K0. split; destruct Rlt_dec => //=; nra.
Qed.

Lemma Krec_bound01 r x i: 0 ≤ Krec i r x ∧ Krec i r x ≤ 1.
Proof.
  revert r x.
  induction i => r x; (split; first (apply Krec_bound0; rewrite //=)).
  - rewrite //=/K0. destruct Rlt_dec => //=; nra.
  - rewrite /Krec -/Krec Ex_fin_pt /rvar_comp //=.
    apply Rmin_l.
Qed.

Lemma Krec_bound r x: bound (fun v => ∃ i, Krec i r x = v).
Proof.
  rewrite /bound /is_upper_bound. exists 1 => v [i <-].
  edestruct Krec_bound01; eauto.
Qed.

Definition Krec_sup (r: R) x : R :=
  proj1_sig (completeness (fun v => ∃ i, Krec i r x = v) 
                          (Krec_bound r x) 
                          (ex_intro _ (Krec 0 r x) (ex_intro _ O erefl))).

Lemma Krec_sup_is_lub r x: is_lub (fun v => ∃ i, Krec i r x = v) (Krec_sup r x).
Proof.
  rewrite /Krec_sup //=. by destruct (completeness _).
Qed.


Lemma K_Krec_leq_below i r x: size x ≤ d → K r x ≤ Krec i r x.
Proof.
  revert r x. induction i as [| i'] => r x Hle.
  - rewrite /K /Krec /K0 //=.
    destruct (Rlt_dec).
    + rewrite /is_left. apply pr_le_1. 
    + rewrite /pr//=.  right. rewrite SeriesC_fin_big. eapply big1 => b ?. 
      rewrite //=. destruct (Rgt_dec) as [?|Hnlt] => //=; try nra.
      specialize (Tbelow _ b Hle).
      exfalso. destruct (T x); simpl in *. nra. 
  - etransitivity; first eapply IHi'; eauto.
    apply Krec_non_decS.
Qed.

Lemma K_Krec_bounded_gap i r x: K r x ≤ Krec i r x + 1.
Proof.
  transitivity 1; first apply pr_le_1.
  specialize (Krec_bound0 r x i) =>?. fourier.
Qed.

Definition recN_a {i: nat} φ x (b: @recN_space _ _ _ (hpath φ) x i) : R.
  revert x b. induction i.
  - intros x ?. exact 0.
  - intros x (b&b'). 
    exact (a (size (snd x)) + IHi ((hpath φ x) b) b').
Defined.

Lemma Rge_not_gt_eq x y: x >= y → (¬ x > y) → x = y.      
Proof. nra. Qed.

Lemma Rge_not_eq_gt x y: x >= y → (¬ x = y) → x > y.      
Proof. nra. Qed.

Lemma pr_gt_path_shift:
  ∀ k φ b r j x,
  pr_gt (rvar_comp (recN_rvar (hpath φ) (j, x) k) (λ x, size (snd x))) r=
  pr_gt (rvar_comp (recN_rvar (hpath (λ n, match n with
                                         | O => b
                                         | S n' => φ n'
                                         end)) (S j, x) k) (λ x, size (snd x))) r.
Proof.    
  induction k; intros. 
  - rewrite //=. 
  - rewrite ?recN_pr_gt. 
    rewrite /index_enum.
    rewrite [@Finite.enum]unlock //=.
    rewrite (img_fin_big' _ (λ i, (pr_eq _ i * pr_gt (rvar_comp (recN_rvar _ i _) _) _)) (λ x, true)). 
    rewrite (img_fin_big' _ (λ i, (pr_eq _ i * pr_gt (rvar_comp (recN_rvar _ i _) _) _)) (λ x, true)). 
    eapply (sum_reidx_map _ _ _ _ (λ x, (S (fst x), snd x))); auto.
    * intros (?&?) Hin; f_equal. 
      ** rewrite /pr_eq/pr ?SeriesC_fin_big.
         apply eq_big => //=.
         intros ? _. destruct (φ j); auto.
      ** rewrite //=.
    * rewrite //=. intros (n&x'). rewrite ?img_alt'. intros (i&Hin) _.
      split; auto. exists i. move: Hin. rewrite //=. 
      case: ifP; intros; inversion Hin; subst; f_equal; auto; omega.
    * rewrite //=. intros (n&x') Hin _ Hfalse.
      apply Rmult_eq_0_compat. right.

      rewrite /pr_gt.
      apply Rge_not_gt_eq; first apply ge_pr_0.
      intros Hgt.
      apply Rlt_gt, pr_img_gt in Hgt as (r'&Hgt&Himg). 
      apply img_alt in Himg as (i&Himg).
      apply img_alt' in Hin as (i'&Himg').
      rewrite //= in Himg, Himg'.
      contradiction (Hfalse). 
      move: Himg'. case: ifP => ? [? ?].
      ** exists (S j, x'). rewrite img_alt'. repeat split; auto. 
         *** eexists; f_equal; eauto.
         *** f_equal; rewrite //=; try congruence; try omega.
      ** exists (S j, x'). rewrite img_alt'. repeat split; auto. 
         *** eexists; f_equal; eauto.
         *** f_equal; rewrite //=; try congruence; try omega.
    * rewrite /img. apply undup_uniq.
    * rewrite /img. apply undup_uniq.
    * intros (?&?) (?&?). rewrite //= => _. inversion 1. subst; done.
Qed.

Lemma Krec_le_K_non_zero_path r x i:
  P x →
  Krec i r x < K r x →
  ∃ φ, pr_gt (rvar_comp (recN_rvar (hpath φ) (O, x) i) (λ x, size (snd x))) d > 0.
Proof.
  revert r x.
  induction i => r x HP Hlt.
  - destruct (Rle_dec (size x) d) as [Hlt2|Hnlt].
    * exfalso. apply Rlt_not_le in Hlt. apply Hlt.
      by apply K_Krec_leq_below.
    * exists (fun x => true).
      rewrite /pr_gt /pr //=.
      apply Rnot_le_gt in Hnlt.
      destruct (Rgt_dec) => //=.
      rewrite SeriesC_fin_big.
      rewrite /index_enum. rewrite (eq_bigl predT).
      ** rewrite /index_enum {1}[@Finite.enum]unlock big_seq1 //=. fourier.
      ** intros ?. rewrite /in_mem//=. 
  - destruct (Rle_dec (size x) d) as [Hlt2|Hnlt%Rnot_le_gt].
    { exfalso. apply Rlt_not_le in Hlt. apply Hlt.
      by apply K_Krec_leq_below. }
    rewrite /Krec -/Krec in Hlt. move: Hlt. apply Rmin_case.
    { intros Hfalse%Rlt_not_le. contradiction Hfalse.
      rewrite /K. apply pr_le_1. }
    intros Hlt. 
    eapply Rlt_le_trans in Hlt; last apply K_alt4; auto.
    rewrite Ex_fin_comp in Hlt. 
    rewrite /index_enum [@Finite.enum]unlock //= in Hlt.
    rewrite (img_fin_big' _ (λ i, (pr_eq _ i * (Krec _ _ (fst i) + Krec _ _ (snd i)))) (λ x, true))
            in Hlt.
    rewrite (img_fin_big' _ (λ i, (pr_eq _ i * (K _ (fst i) + K _ (snd i)))) (λ x, true))
            in Hlt.
    apply Rlt_big_inv in Hlt as (b&Hin&_&Hlt).
    assert (pr_eq (h x) b > 0) as HPrb.
    { rewrite /pr_eq; apply Rge_not_eq_gt; first apply (ge_pr_0).
      intros Heq.
      rewrite /pr_eq ?Heq in Hlt. nra.
    }
    apply Rmult_lt_reg_l in Hlt; last auto.
    apply Rlt_plus_reg in Hlt as [Hlt1|Hlt2].
    * assert (P (fst b)) as HPb.
      { rewrite img_alt' in Hin *. intros (n&<-). eapply hP. eauto. }
      edestruct (IHi _ _ HPb Hlt1) as (φ&Hpr).
      exists (λ n, match n with
                | O => true
                | S n' => φ n'
                end).
      rewrite recN_pr_gt => //=.
      rewrite /index_enum.
      rewrite [@Finite.enum]unlock //=.
      rewrite (img_fin_big' _ (λ i, (pr_eq _ i * pr_gt (rvar_comp (recN_rvar _ i _) _) _)) 
                            (λ x, true)). 
      eapply (Rle_lt_trans); first (right; symmetry; apply big1; reflexivity).
      eapply Rlt_bigr.
      ** intros; apply Rmult_le_pos; apply Rge_le, ge_pr_0.
      ** rewrite //=. 
         exists (S O, fst b); repeat split.
         *** apply img_alt'. apply img_alt' in Hin.
             destruct Hin as (s&Heq). exists s. rewrite Heq. done.
         *** rewrite //=. apply Rmult_lt_0_compat.
             **** eapply Rlt_le_trans; first apply HPrb.
                  rewrite /pr_eq /pr ?SeriesC_fin_big /index_enum /Bn /=.  
                  rewrite -?big_mkcondr.
                  apply Rle_bigr'; try nra.
                  ***** intros ?. move /andP => [_ Heq]. move /eqP in Heq; subst. 
                        split; try nra. apply /andP; split; auto. 
                        rewrite //= in Hpr. rewrite /Ωn//=. nra.
                  ***** intros. apply Rge_le, pmf_pos.
             **** eapply Rlt_le_trans; first apply Hpr.
                  right. apply pr_gt_path_shift.
    * assert (P (snd b)) as HPb.
      { rewrite img_alt' in Hin *. intros (n&<-). eapply hP. eauto. }
      edestruct (IHi _ _ HPb Hlt2) as (φ&Hpr).
      exists (λ n, match n with
                | O => false
                | S n' => φ n'
                end).
      rewrite recN_pr_gt => //=.
      rewrite /index_enum.
      rewrite [@Finite.enum]unlock //=.
      rewrite (img_fin_big' _ (λ i, (pr_eq _ i * pr_gt (rvar_comp (recN_rvar _ i _) _) _)) 
                            (λ x, true)). 
      eapply (Rle_lt_trans); first (right; symmetry; apply big1; reflexivity).
      eapply Rlt_bigr.
      ** intros; apply Rmult_le_pos; apply Rge_le, ge_pr_0.
      ** exists (S O, (snd b)).
         repeat split.
         *** apply img_alt'. apply img_alt' in Hin.
             destruct Hin as (s&Heq). exists s. rewrite Heq. done.
         *** rewrite //=. apply Rmult_lt_0_compat.
             **** eapply Rlt_le_trans; first apply HPrb.
                  rewrite /pr_eq /pr /index_enum /Bn /= ?SeriesC_fin_big.
                  rewrite -?big_mkcondr.
                  apply Rle_bigr'; try nra.
                  ***** intros ?. move /andP => [_ Heq]. move /eqP in Heq; subst. 
                        split; try nra. apply /andP; split; auto. 
                        rewrite /Ωn //=. reflexivity.
                  ***** intros. apply Rge_le, pmf_pos.
             **** eapply Rlt_le_trans; first apply Hpr.
                  right. apply pr_gt_path_shift.
Qed.

Lemma K_le_supKrec r x: P x → K r x ≤ Krec_sup r x.
Proof.
  intros HP.
  apply Rnot_gt_le.
  intros Hgt.
  destruct (hinf_0 x) as [n Hpath0].
  destruct (Krec_sup_is_lub r x) as [Hub _].
  specialize (Hub (Krec n r x)).
  edestruct (Krec_le_K_non_zero_path r x n) as (φbad&Hbad); auto.
  { eapply (Rle_lt_trans _ (Krec_sup r x)); auto. apply Hub. eauto. }
  specialize (Hpath0 φbad). fourier.
Qed.


Lemma D0_aux r x:
   0 < x → 0 ≤ ((m x) / x) ^ Z.to_nat (round r x) 
                                          * (g(x) * x / u' (r - a x * IZR (round r x))).
Proof.                                             
  intros Hlt.
    eapply Rmult_pos. 
    * eapply pow_le. rewrite /Rdiv.
      eapply Rle_mult_inv_pos; eauto.
      apply mpos. fourier.
    * rewrite /round //=. 
      eapply Rle_mult_inv_pos.
      ** apply Rmult_le_pos; eauto.
         *** eapply gpos; fourier.
         *** fourier.
      ** eapply u'_pos.
Qed.

Lemma D0 r x:
  0 ≤ D r x.
Proof.                                             
  rewrite /D.
  destruct (Rle_dec) => //=; intros; try nra.
  destruct (Rle_dec) => //=; intros; try nra.
  destruct (Rle_dec) => //=; intros; try nra.
  intros. 
  { transitivity 1; first fourier. apply Rmax_l. }
  apply D0_aux. nra.
Qed.

Lemma uu'_adjoint x y: (* d < x → *) umin < y → x ≤ u' y ↔ u x ≤ y.
Proof.
  split.
  - intros ?%u_mono. transitivity (u (u' y)); eauto. right. by rewrite u_inv_above.
  - transitivity (u' (u x)); eauto.
Qed.

Lemma uu'_adjointrl x y: umin < y → x ≤ u' y → u x ≤ y.
Proof.
  eapply uu'_adjoint.
Qed.

Lemma uu'_adjointlr x y: (* d < x → *) u x ≤ y → x ≤ u' y.
Proof.
  transitivity (u' (u x)); eauto.
Qed.

Lemma uu': ∀ x, umin < x → u (u' x) ≤ x.
Proof.
  intros. apply uu'_adjointrl; auto; reflexivity.
Qed.

Definition kD := karp.D a m u u' d umin.

Lemma D_karpD r x:
  r > umin →
  (0 ≤ x ∧ x ≤ (u' r)) →
  D r x = g(x) * kD r x.
Proof.
  intros Hr (?&Hrange).
  rewrite D_Dalt_equiv. 
  rewrite /kD. erewrite karp.D_Dalt_equiv; eauto.
  rewrite /Dalt /karp.Dalt.
  destruct (Rle_dec); first nra.
  rewrite /is_left.
  destruct (Rle_dec); first nra.
  rewrite /is_left.
  destruct (Rlt_dec). 
  { intros. apply uu'_adjointrl in Hrange; last fourier.
  apply Rle_not_gt in Hrange. nra. }
  rewrite /karp.round/round.
  field; apply Rgt_not_eq, u'_pos.
Qed.


Lemma D_karpD' r x:
  r > umin →
  (0 ≤ x) →
  D r x ≤ g x * kD r x.
Proof.
  intros Hr ?.
  rewrite D_Dalt_equiv. 
  rewrite /kD. erewrite karp.D_Dalt_equiv; eauto.
  rewrite /Dalt /karp.Dalt.
  destruct (Rle_dec) as [|?]; first nra.
  rewrite /is_left.
  destruct (Rle_dec) as [|Hled]; first nra.
  rewrite /is_left.
  destruct (Rlt_dec) as [Hr'%Rlt_le|?]. 
  { intros. rewrite Rmult_1_r.
    apply u'_mono in Hr'. rewrite u'_inv_above in Hr'; eauto; try nra.
    apply Rmax_case_strong; intros.
    * apply Rge_le, gd. nra.
    * apply g_mono; eauto.
  }
  rewrite /karp.round/round.
  right. field; apply Rgt_not_eq, u'_pos.
Qed.

Lemma D_karpD'' r x:
  g x > 1 →
  D r x ≤ g x * kD r x.
Proof.
  intros Hgt.
  rewrite D_Dalt_equiv. 
  rewrite /kD. erewrite karp.D_Dalt_equiv; eauto.
  rewrite /Dalt /karp.Dalt.
  destruct (Rle_dec) as [|?]; first by nra.
  rewrite /is_left.
  destruct (Rle_dec) as [|Hled]; first nra.
  rewrite /is_left.
  destruct (Rlt_dec) as [Hr'%Rlt_le|?]. 
  { intros. rewrite Rmult_1_r.
    apply u'_mono in Hr'. rewrite u'_inv_above in Hr'; eauto; try nra.
    apply Rmax_case_strong; intros.
    * apply Rge_le, gd. nra.
    * apply g_mono; eauto.
  }
  rewrite /karp.round/round.
  right. field; apply Rgt_not_eq, u'_pos.
Qed.

Lemma Rmin_le_right x y z: y ≤ z → Rmin x y ≤ z.
Proof.
  intros. apply Rmin_case_strong; intros; fourier.
Qed.

Lemma Rceil_1 x: (0 < x) → (x ≤ 1) → Rceil x = 1%Z.
Proof.          
  intros Hgt Hle.
  rewrite /Rceil. 
  move: Hgt.
  case: ifP.
  - apply Int_part_mono in Hle.
    replace (Int_part 1) with 1%Z in Hle; last first.
    { replace 1 with (IZR 1) by auto. rewrite Int_part_IZR //=. }
    move /eqP => Heq.
    rewrite {1}(Int_frac_decompose x) Heq.
    destruct (Z_le_dec (Int_part x) 0) as [l|nl].
    * apply IZR_le in l. replace (IZR 0) with 0 in l by auto. intros; fourier.
    * intros. omega.
  - move /eqP => Hnfp0 Hgt.
    assert (Int_part x = 1 ∨ Int_part x = 0)%Z as [?|?].
    { 
      apply Rlt_le in Hgt. apply Int_part_mono in Hgt.
      replace (Int_part 0) with 0%Z in Hgt; last first.
      { replace 0 with (IZR 0) by auto. rewrite Int_part_IZR //=. }
      apply Int_part_mono in Hle.
      replace (Int_part 1) with 1%Z in Hle; last first.
      { replace 1 with (IZR 1) by auto. rewrite Int_part_IZR //=. }
      assert (Int_part x = 1 ∨ Int_part x = 0)%Z as [?|?] by omega; omega.
    }
    * exfalso. rewrite {1}(Int_frac_decompose x) in Hle.
      destruct (base_fp x) as [Hge0 ?].
      inversion Hge0; last by nra.
      rewrite H in Hle. replace (IZR 1) with 1 in Hle by auto. fourier.
    * omega.
Qed.


Lemma Krec_le_D: ∀ i r x, Krec i r x ≤ D r (size x).
Proof.
  induction i => r x.
  - rewrite /K /D. 
    destruct (Rle_dec) as [|Hgtmin]; first by (edestruct Krec0_bound01; eauto).
    rewrite /is_left.
    destruct (Rle_dec) as [Hge|Hnge].
    { right. rewrite //= /K0 //=. destruct (Rlt_dec) => //=; try nra. }
    rewrite /is_left.
    destruct (Rle_dec) as [Hge|Hnge'].
    { edestruct (Krec_bound01 r x O); eauto. 
      transitivity 1; first nra. apply Rmax_l. }
    rewrite //= /K0.
    destruct (Rlt_dec) as [|Hnlt].
    { intros. exfalso; eapply Hgtmin. fourier. }
    eapply D0_aux. nra.
  - rewrite /K /D.
    destruct (Rle_dec) as [|Hgtmin]; first (clear IHi; edestruct Krec_bound01; eauto).
    destruct (Rle_dec) as [Hge|Hnge].
    { 
      clear IHi.
      right. revert r x Hgtmin Hge. induction (S i).
      * rewrite //= /K0 //=. intros. destruct Rlt_dec; last reflexivity.
        exfalso; eapply Hgtmin. nra. 
      * intros. rewrite /Krec -/Krec Ex_fin_pt /rvar_comp //=. 
        rewrite alower; last fourier. rewrite Rminus_0_r.
        etransitivity; last (apply (Rmin_right)); f_equal; try nra.
        eapply big1 => b ?.  rewrite ?IHn //=; auto; try nra. 
        ** transitivity (size x) => //. 
        ** transitivity (size x) => //.
    }
    rewrite /is_left.
    destruct (Rle_dec) as [Hge|Hnge'].
    { clear IHi; transitivity 1; last apply Rmax_l. edestruct Krec_bound01; eauto. }
    assert (r - a (size x) > umin) as Hgt.
    {
      apply Rgt_ge_trans with (r2 := u (size x) - a (size x)); first by nra.
      apply /Rle_ge/umin_lb. nra.
    }
    destruct (Rge_dec d (u' (r - a (size x)))) as [Hge|Hlt]; [| apply Rnot_ge_lt in Hlt].
    {
      exfalso. apply Rge_le in Hge. apply u_mono in Hge.
      rewrite u_inv_above //= in Hge. fourier.
    }
    rewrite /Krec -/Krec.
    transitivity
      (Ex (rvar_comp (h x) (λ x', (g (size (fst x'))) * kD (r - a (size x)) (size (fst x')) +
                                  (g (size (snd x'))) * kD (r - a (size x)) (size (snd x'))))).
    { 
      apply Rmin_le_right.
      rewrite ?Ex_fin_pt //=.
      apply Rle_bigr => z ?.
      * apply Rmult_le_compat_r. apply Rge_le, pmf_pos.
        apply Rplus_le_compat.
        ** etransitivity; last apply D_karpD'; eauto.
           eapply hrange12. nra.
        ** etransitivity; last apply D_karpD'; eauto.
           eapply hrange22. nra.
    }
    etransitivity.
    { 
    eapply lemma31_simplex with (g := g) (size := size) (X := h x) (c := u' (r - a (size x))) 
                                          (f := (λ z, kD (r - a (size x)) z))
                                          (x := size x)
                                          (z := 1).
        * nra.
        * apply u'_pos.
        * intros p. rewrite img_alt. intros (n&?). subst.
          eapply hrange12. nra.  
        * intros p. rewrite img_alt. intros (n&?). subst.
          eapply hrange22. nra.
        * intros p. rewrite img_alt. intros (n&?). subst.
          eauto.
        * intros p. rewrite img_alt. intros (n&?). subst.
          eauto.
        * intros p. rewrite img_alt. intros (n&?). subst.
          eapply gpos, hrange12. nra.
        * intros p. rewrite img_alt. intros (n&?). subst.
          eapply gpos, hrange22. nra.
        * intros p. rewrite img_alt. intros (n&?). subst.
          eauto. eapply hgrange_sum. nra. 
        * rewrite /kD/karp.D.
          repeat (destruct (Rle_dec); rewrite /is_left; try nra).
        * rewrite /kD; apply karp.D0; eauto.
        * fourier.
        * intros y Hley.
          rewrite /kD/karp.D.
          repeat (destruct (Rle_dec); rewrite /is_left; try nra).
          apply Rge_le, u_mono in Hley. rewrite u_inv_above // in Hley.
        * intros. eapply karp.Dnondec; eauto.
    }
    rewrite /Rdiv ?Rmult_assoc. etransitivity. 
    {
      apply Rmult_le_compat_r; last (apply m_bound_Eh).
      apply Rmult_le_pos.
      - apply gpos. nra. 
      - apply Rle_mult_inv_pos; auto. 
          * rewrite /kD. apply karp.D0; eauto.
          * apply Rmin_case; nra.
    }
    assert (round r (size x) = 1 + round (r - a (size x)) (size x))%Z as Hplus.
    {  rewrite /round. rewrite Zplus_comm -Rceil_plus_1; f_equal.
       field. apply Rgt_not_eq. apply a_pos. nra.
    }
    assert (Hrgt0: (round r (size x) > 0)%Z).
    { 
      rewrite /round. rewrite -Rceil_0. apply Zlt_gt, Rceil_mono_strict. apply frac_part_0.
      apply Rdiv_lt_0_compat.
      - nra.
      - apply a_pos. nra.
    }
    assert (0 <= round (r - a (size x)) (size x))%Z by omega.
    apply Rmin_case_strong.
    * rewrite Hplus.
      intros Hminl. rewrite /kD. erewrite karp.D_Dalt_equiv; eauto. rewrite /karp.Dalt //.
      destruct (Rle_dec); rewrite /is_left; first nra.
      destruct (Rle_dec); rewrite /is_left; first nra.
      destruct (Rlt_dec).
      { move: Hminl. move /uu'_adjointrl/Rle_ge/Rge_not_lt. nra. }
      right. 
      rewrite Z2Nat.inj_add; try omega.
      rewrite plus_IZR. replace (IZR 1) with 1 by auto.
      rewrite //=.
      rewrite Rmult_plus_distr_l Rmult_1_r.
      rewrite /Rminus. rewrite Ropp_plus_distr.
      rewrite Rplus_assoc.
      rewrite /round/karp.round.
      rewrite /Rdiv. field.
      split.
      ** apply Rgt_not_eq, u'_pos.
      ** apply Rgt_not_eq. nra.
    * intros Hminr. rewrite /kD. erewrite karp.D_Dalt_equiv; eauto. rewrite /karp.Dalt //.
      destruct (Rle_dec); rewrite /is_left; first nra.
      destruct (Rle_dec); rewrite /is_left; first nra.
      destruct (Rlt_dec) as [Hbad|].
      { move: Hbad. rewrite u_inv_above; nra. }
      right. symmetry.
      assert (round (r - a (size x)) (u' (r - a (size x))) = 0)%Z as Hround0'.
      { 
        rewrite /round -Rceil_0. f_equal.
        rewrite u_inv_above /Rdiv; last done.
        apply Rmult_eq_0_compat_r; ring.
      }
      rewrite /karp.round. rewrite /round in Hround0'. rewrite Hround0'.
      rewrite //= Rmult_0_r Rminus_0_r Rmult_1_l /Rdiv Rinv_r;
        last by apply Rgt_not_eq, u'_pos.
      rewrite Rmult_1_l.
      assert (round r (size x) = 1)%Z as ->.
      { rewrite /round. apply Rceil_positive_le1. 
        - move: Hrgt0. rewrite /round. done. 
        - apply (Rmult_le_reg_r (a (size x))).
          * apply a_pos. nra.
          * rewrite Rmult_1_l /Rdiv Rmult_assoc Rinv_l.
            ** rewrite Rmult_1_r. apply u_mono in Hminr.
               rewrite u_inv_above in Hminr; nra.
            ** apply Rgt_not_eq, a_pos. nra.
      }
      replace (IZR 1) with 1 by auto. rewrite //= ?Rmult_1_r.
      field; split.
      ** apply Rgt_not_eq, u'_pos.
      ** nra.
Qed.

Theorem span_bound r x: P x → K r x ≤ D r (size x). 
Proof.
  transitivity (Krec_sup r x).
  - apply K_le_supKrec; auto.
  - apply (proj2 (Krec_sup_is_lub r x)).
    intros ? (i&<-); apply Krec_le_D.
Qed.


Theorem span_bound_simple w x: 
  g (size x) > 1 →
  size x > d →
  P x → pr_gt (T x) (u (size x) + INR w * a (size x)) ≤ g (size x) * (m (size x) / size x) ^ w.
Proof.
  set (r := u (size x) + INR w * a (size x)).
  transitivity (D r (size x)).
  - apply span_bound; auto.
  -  rewrite /D/r. destruct (Rle_dec) as [Hle|?].
     { rewrite //=. destruct w; first by (rewrite //=; nra).
         assert (umin <= u (size x)) by (apply umin_lb_simple; nra).
         assert (a (size x) > 0) by (apply a_pos; nra).
         specialize (pos_INR w).
         intros. rewrite S_INR in Hle. exfalso. nra.
     }
     rewrite //=. 
     destruct Rle_dec => //=; try nra; [].
     destruct Rle_dec as [Hle|?].
     { intros. rewrite //=.
       destruct w. 
       { replace (INR 0) with 0 by auto. rewrite Rmult_0_l Rplus_0_r.
         rewrite u'_inv_above; last nra.
         apply Rmax_case_strong; nra. 
       }
       assert (umin <= u (size x)) by (apply umin_lb_simple; nra).
       assert (a (size x) > 0) by (apply a_pos; nra).
       specialize (pos_INR w).
       intros. exfalso.  rewrite S_INR in Hle. exfalso. nra.
     }
     rewrite //=.
     assert (round (u (size x) + INR w * a (size x)) (size x) = Z_of_nat w) as Hround.
     { 
       rewrite /round.
       assert ((u (size x) + INR w * a (size x) - u (size x)) / a (size x)=
               INR w) as ->.
       { field. specialize (a_pos (size x)). nra. }
        rewrite INR_IZR_INZ Rceil_IZR. done.
     }
     rewrite Hround //=. rewrite INR_IZR_INZ. 
     rewrite (Rmult_comm (IZR _)).
     assert (u (size x) + a (size x) * IZR (Z.of_nat w) - a (size x) * IZR (Z.of_nat w) 
             = u (size x)) as -> by field.
     rewrite u'_inv_above; last by nra.
     rewrite /Rdiv. rewrite (Rmult_assoc (g (size x))). rewrite Rinv_r; last by nra. rewrite Rmult_1_r.
      rewrite Nat2Z.id. nra.
Qed.

End span_bound_sec.