(* A proof of Karp's theorem about probabilistic recurrence relations  *)

From discprob.basic Require Import base order nify.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.rec Require Export rec_convert.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier FunctionalExtensionality.
Require Import Psatz.
Require Import Coq.omega.Omega.
Require Import Ranalysis5.
Global Set Bullet Behavior "Strict Subproofs".

Notation "x ≤ y" := (le x y) (at level 70, no associativity) : nat_scope.
Notation "x ≥ y" := (ge x y) (at level 70, no associativity) : nat_scope.
Notation "x ≤ y" := (Rle x y) (at level 70, no associativity).
Notation "x ≥ y" := (Rge x y) (at level 70, no associativity).


Definition Rceil x := 
  match (frac_part x) == R0 with
    | true => Int_part x
    | false => (Int_part x + 1)%Z
  end.

Lemma Int_part_minus x x': (Int_part (x - x') <= Int_part x - Int_part x')%Z. 
Proof.
  assert (frac_part x ≥ frac_part x' ∨ frac_part x < frac_part x') as [Hge|Hlt].
  { destruct (total_order_T (frac_part x) (frac_part x')) as [[Hlt|Heq]|Hgt]; auto.
    - rewrite Heq. left. right. auto.
    - left. left. auto.
  }
  rewrite Rminus_Int_part1; eauto. omega.
  rewrite Rminus_Int_part2; eauto. omega.
Qed.

Lemma Int_part_pos x: 0 ≤ x → (0 <= Int_part x)%Z.
Proof.
  rewrite /Int_part => Hpos.
  apply le_IZR. rewrite minus_IZR. 
  replace (IZR 1) with 1 by auto.
  replace (IZR 0) with 0 by auto.
  case (Rge_dec x 1).
  - edestruct (archimed x). intros. nra.
  - edestruct (archimed x). intros.
    assert (up x = (0 + 1)%Z) as ->.
    { symmetry. apply up_tech; eauto. rewrite //=. nra. }
    rewrite //=. nra.
Qed.

Lemma Int_part_mono x x': x ≤ x' → (Int_part x <= Int_part x')%Z.
Proof.
  intros.
  cut (0 <= Int_part x' - Int_part x)%Z; first by omega.
  etransitivity; last eapply Int_part_minus.
  apply Int_part_pos; fourier.
Qed.

Lemma up_mono x x': x ≤ x' → (up x <= up x')%Z.
Proof.
  intros Hint%Int_part_mono.
  rewrite /Int_part in Hint. omega.
Qed.

Lemma Int_frac_decompose x: x = IZR (Int_part x) + frac_part x.
Proof.
  rewrite /frac_part/Int_part minus_IZR. ring.
Qed.

Lemma Rceil_mono x x': x ≤ x' → (Rceil x <= Rceil x')%Z.
Proof.
  rewrite /Rceil. 
  case: ifP. 
  - case: ifP; intros ?? ?%Int_part_mono; omega.
  - case: ifP.
    * move /eqP => Heq0. 
      move /eqP => Hneq0.
      intros Hle.
      cut (Int_part x < Int_part x')%Z; first by omega.
      specialize (Int_frac_decompose x) => Hde.
      specialize (Int_frac_decompose x') => Hde'.
      rewrite Hde Hde' in Hle.
      rewrite Heq0 in Hle. 
      assert (frac_part x > 0). 
      { edestruct (base_fp x). inversion H; auto. nra. }
      intros. apply lt_IZR. fourier.
    * intros ?? ?%Int_part_mono; omega.
Qed.

Definition Rmono (f: R → R): Prop := ∀ x x', x ≤ x' → f x ≤ f x'.
Definition Rantimono (f: R → R): Prop := ∀ x x', x ≤ x' → f x ≥ f x'.
Definition Rmono_P P (f: R → R): Prop := ∀ x x', P x → P x' → x ≤ x' → f x ≤ f x'.
Definition Rantimono_P P (f: R → R): Prop := ∀ x x', P x → P x' → x ≤ x' → f x ≥ f x'.

Lemma Int_part_IZR z: Int_part (IZR z) = z.
Proof.
  rewrite /Int_part -(up_tech (IZR z) z) //=; try reflexivity; try fourier; try omega.
  apply IZR_lt; omega.
Qed.

Lemma Rceil_IZR z: Rceil (IZR z) = z.
Proof.
  rewrite /Rceil.
  case: ifP.
  - rewrite Int_part_IZR //.
  - move /eqP => Hnonz. contradiction (Hnonz).
    generalize (Int_frac_decompose (IZR z)). rewrite Int_part_IZR. 
    intros Heq%(Rplus_eq_compat_l (- (IZR z))).
    by rewrite -Rplus_assoc ?Rplus_opp_l Rplus_0_l in Heq.
Qed.

Lemma Rceil_interval_decompose (f: Z → R → R) (g: R → R):
  (∀ k, Rmono (f k)) →
  (∀ k x, g x = IZR k → f k x = f (k + 1)%Z x) →
  Rantimono g →
  continuity g →
  Rmono (λ z, f (Rceil (g z)) z).
Proof.
  intros Hfmono Hboundary Hganti Hcontinuity. rewrite /Rmono => x x' Hle. 
  assert (∃ k,  Rceil (g x) - Rceil (g x') = Z_of_nat k)%Z as (k&Heqk).
  { 
    apply Hganti, Rge_le, Rceil_mono in Hle.
    eapply Z_of_nat_complete. omega.
  }
  revert x x' Hle Heqk. induction k; (* [|induction k]; *) intros x x'.
  - rewrite //= => Hle Heq0. 
    assert (Rceil (g x) = Rceil (g x')) as <- by omega. 
    apply (Hfmono (Rceil (g x))); auto.
  - intros. rewrite Nat2Z.inj_succ in Heqk.
    cut (∃ y, x ≤ y ∧ y ≤ x' ∧ (g y) = IZR (Rceil (g x) - 1))%Z. 
    {
      intros (y&?&?&Hedge).
      apply Hganti, Rge_le, Rceil_mono in Hle.
      generalize (f_equal Rceil Hedge) => Hedge'. 
      rewrite Rceil_IZR in Hedge'.
      transitivity (f (Rceil (g y)) y).
      * rewrite (Hboundary _ y) Hedge' //. 
        rewrite Zplus_comm Zplus_minus.
        apply Hfmono; auto.
      * eapply IHk; eauto. omega.
    }
    inversion Hle as [Hlt|Heq]; last first.
    { 
      rewrite Heq in Heqk. rewrite -Zminus_diag_reverse in Heqk. exfalso.
      specialize (Zle_0_nat k). rewrite Heqk. omega.
    }
    destruct (f_interv_is_interv (λ z, - g z) x x' (- IZR (Rceil (g x) - 1))) as (y&(?&?)&Hneg);
      eauto.
    * split; apply Ropp_ge_le_contravar. 
      ** rewrite {1}(Int_frac_decompose (g x)).
         rewrite /Rceil. case: ifP. 
         *** move /eqP => ->.
             rewrite minus_IZR. replace (IZR 1) with 1 by (rewrite /IZR //=). fourier.
         *** move /eqP.
             destruct (base_fp (g x)) as (?&?).
             rewrite minus_IZR. rewrite plus_IZR. 
             intros. fourier.
      ** transitivity (IZR (Rceil (g x'))); first (apply IZR_ge; omega).
         rewrite {2}(Int_frac_decompose (g x')).
         rewrite /Rceil. case: ifP. 
         *** move /eqP => ->.
             fourier.
         *** move /eqP. 
             destruct (base_fp (g x')) as (?&?).
             rewrite plus_IZR.
             replace (IZR 1) with 1 by (rewrite /IZR //=). 
             intros. fourier.
    * intros. apply continuity_opp; auto.
    * exists y. repeat split; auto.
      rewrite -(Ropp_involutive (g y)).
      rewrite -(Ropp_involutive (IZR _)).
      by apply Ropp_eq_compat.
Qed.

Definition convex (P: R → Prop) := ∀ x y, P x → P y → ∀ z, x ≤ z → z ≤ y → P z.

Lemma Rceil_interval_decompose_P P (f: Z → R → R) (g: R → R):
  convex P →
  (∀ k, (∃ x, P x ∧ Rceil (g x) = k) → Rmono_P P (f k)) →
  (∀ k x, P x → g x = IZR k → f k x ≥ f (k + 1)%Z x) →
  Rantimono_P P g →
  (∀ x, P x → continuity_pt g x) →
  Rmono_P P (λ z, f (Rceil (g z)) z).
Proof.
  intros Hconvex Hfmono Hboundary Hganti Hcontinuity. rewrite /Rmono => x x' HP HP' Hle. 
  assert (∃ k,  Rceil (g x) - Rceil (g x') = Z_of_nat k)%Z as (k&Heqk).
  { 
    apply Hganti, Rge_le, Rceil_mono in Hle; eauto.
    eapply Z_of_nat_complete. omega.
  }
  revert x x' HP HP' Hle Heqk. induction k; (* [|induction k]; *) intros x x' HP HP'.
  - rewrite //= => Hle Heq0. 
    assert (Rceil (g x) = Rceil (g x')) as <- by omega. 
    apply (Hfmono (Rceil (g x))); auto.
    exists x; eauto.
  - intros. rewrite Nat2Z.inj_succ in Heqk.
    cut (∃ y, x ≤ y ∧ y ≤ x' ∧ (g y) = IZR (Rceil (g x) - 1))%Z. 
    {
      intros (y&?&?&Hedge).
      apply Hganti, Rge_le, Rceil_mono in Hle; eauto.
      generalize (f_equal Rceil Hedge) => Hedge'. 
      rewrite Rceil_IZR in Hedge'.
      transitivity (f (Rceil (g y)) y).
      * transitivity (f (Rceil (g x)) y); first eapply Hfmono; eauto.
        rewrite Hedge' //. apply Rge_le.
        replace (Rceil (g x)) with ((Rceil (g x) - 1) + 1)%Z at 2 by omega.
        apply Hboundary; eauto. 
      * eapply IHk; eauto. omega.
    }
    inversion Hle as [Hlt|Heq]; last first.
    { 
      rewrite Heq in Heqk. rewrite -Zminus_diag_reverse in Heqk. exfalso.
      specialize (Zle_0_nat k). rewrite Heqk. omega.
    }
    destruct (f_interv_is_interv (λ z, - g z) x x' (- IZR (Rceil (g x) - 1))) as (y&(?&?)&Hneg);
      eauto.
    * split; apply Ropp_ge_le_contravar. 
      ** rewrite {1}(Int_frac_decompose (g x)).
         rewrite /Rceil. case: ifP. 
         *** move /eqP => ->.
             rewrite minus_IZR. replace (IZR 1) with 1 by (rewrite /IZR //=). fourier.
         *** move /eqP.
             destruct (base_fp (g x)) as (?&?).
             rewrite minus_IZR. rewrite plus_IZR. 
             intros. fourier.
      ** transitivity (IZR (Rceil (g x'))); first (apply IZR_ge; omega).
         rewrite {2}(Int_frac_decompose (g x')).
         rewrite /Rceil. case: ifP. 
         *** move /eqP => ->.
             fourier.
         *** move /eqP. 
             destruct (base_fp (g x')) as (?&?).
             rewrite plus_IZR.
             replace (IZR 1) with 1 by (rewrite /IZR //=). 
             intros. fourier.
    * intros ? (?&?). apply continuity_pt_opp.
      eapply Hcontinuity, (Hconvex x x'); eauto; fourier.
    * exists y. repeat split; auto.
      rewrite -(Ropp_involutive (g y)).
      rewrite -(Ropp_involutive (IZR _)).
      by apply Ropp_eq_compat.
Qed.

Section rec_var.
Variable X: eqType.
Variable B : X → finType.
Variable Ω : ∀ x, distrib (B x).
Variable h: ∀ x: X, rvar (Ω x) X.

Fixpoint recN_space (x: X) (n: nat) : finType :=
  match n with 
    | O => [finType of unit]
    | S n' => [finType of {i : B x & (recN_space ((h x) i) n')}]
  end. 

Fixpoint recN_pmf (a: X) (n: nat) : recN_space a n → R.
Proof.
  induction n as [| n']. 
  - intros _. exact 1.
  - intros (i&?). exact ((rvar_dist (h a)) i * (recN_pmf ((h a) i) n' s)).
Defined.

Lemma recN_0 a n x: recN_pmf a n x ≥ 0.
Proof.
  revert a x.
  induction n as [| n'] => //=.
  - intros; fourier.
  - intros ? (i&s) => //=.
    apply Rle_ge, Rmult_le_pos; eauto using Rge_le, pmf_pos. 
Qed.

Lemma in_tagged (I: eqType) a (T_i: I → finType) X' (i: {x : I & T_i x}):
  i \in [seq @Tagged I a (λ x0 : I, T_i x0) x | x <- X'] → projT1 i = a.
Proof.          
  induction X' => //=.
  rewrite in_cons. case: eqP => // -> //=.
Qed.

Lemma recN_1_aux a n: \big[Rplus/0]_(x in (recN_space a n)) ((recN_pmf a n) x) = 1%R. 
Proof.
  revert a. induction n as [| n'] => //=.
  - intros ?. by rewrite /index_enum {1}[@Finite.enum]unlock big_seq1.
  - intros a. rewrite /index_enum {1}[@Finite.enum]unlock //=.
    rewrite /tag_enum. 
    rewrite big_flatten //=. 
    transitivity (\big[Rplus/0]_(i <- Finite.enum (B a)) (rvar_dist (h a)) i).
    + induction (Finite.enum (B a)). rewrite //=.
      rewrite ?big_nil //=.
      rewrite ?big_cons //=.
      f_equal; eauto.
      rewrite big_seq_cond.
      rewrite //=.
      etransitivity; first
      eapply (eq_bigr (λ (i: {x: B a & recN_space ((h a) x) n'}), 
                       (rvar_dist (h a) a0 * (let (x, s) := i in recN_pmf ((h a) x) n' s)))).
      * intros i. move /andP. intros (Hin&_).
        move: (in_tagged _ _ _ _ _ Hin).
        destruct i as (i'&s). 
        clear. rewrite //=. intros ->. done.
      * rewrite -big_seq_cond -big_distrr //=. 
        rewrite -[a in _ = a]Rmult_1_r; f_equal.
        specialize (IHn' ((h a) a0)). 
        rewrite -IHn'. 
        rewrite big_map //=.
    + rewrite -SeriesC_fin_big. apply is_series_unique. eapply pmf_sum1.
Qed.

Lemma recN_1 a n: is_series (countable_sum (recN_pmf a n)) 1.
Proof.  
  rewrite -(recN_1_aux a n) -SeriesF_big_op. apply SeriesF_is_seriesC.
Qed.

Definition recN_dist a n : distrib (recN_space a n) :=
  @mkDistrib _ (recN_pmf a n) (recN_0 a n) (recN_1 a n).

Fixpoint recN_fun a n : recN_space a n → X.
Proof.
  induction n as [| n'].
  - intro. exact a.
  - intros (x&s). exact (recN_fun ((h a) x) n' s).
Defined.

Definition recN_rvar a n := mkRvar (recN_dist a n) (recN_fun a n).

Fixpoint pr_rec a n v :=
  match n with
    | 0 => if (a == v) then 1 else 0
    | S n => \big[Rplus/0]_(a' : imgT (h a)) (pr_eq (h a) (sval a') * pr_rec (sval a') n v)
  end.

Lemma recN_pr_base v v':
  pr_eq (recN_rvar v' 0) v = (if v' == v then 1 else 0).
Proof.
  rewrite /pr_eq/pr//=. rewrite SeriesC_fin_big.
  rewrite ?/index_enum {1}[@Finite.enum]unlock //=.
  case: ifP; move /eqP => Heq;
  rewrite big_cons big_nil //=; nra. 
Qed.

Lemma recN_pr_comp_base {C: eqType} (f: X → C) (v: C) (v': X):
  pr_eq (rvar_comp (recN_rvar v' 0) f) v = (if f v' == v then 1 else 0).
Proof.
  rewrite /pr_eq/pr//=. 
  rewrite SeriesC_fin_big ?/index_enum {1}[@Finite.enum]unlock //=.
  case: ifP; move /eqP => Heq;
  rewrite big_cons big_nil //=; nra. 
Qed.

Lemma nested_sum_recN_space x n F:
  \big[Rplus/0]_(i in B x)
     (\big[Rplus/0]_(b in recN_space ((h x) i) n)
       F i b) =
  \big[Rplus/0]_(ib in pred_of_argType {i : B x & recN_space ((h x) i) n})
     let (i, b) := ib in F i b.
Proof.
  - symmetry. rewrite ?/index_enum {1}[@Finite.enum]unlock //=.
     rewrite /tag_enum. rewrite big_flatten //=. 
     induction (Finite.enum (B x)).
     * rewrite //= ?big_nil //.
     * rewrite ?big_cons_Rplus //=. f_equal; auto.
       clear.
       induction (Finite.enum (recN_space ((h x) a) n)).
       ** rewrite //= ?big_nil //.
       ** rewrite //= ?big_cons_Rplus //=.
          f_equal; auto. 
Qed.

(* TODO: refactor using above lemma *)
Lemma recN_pr_unfold a n v:
  pr_eq (recN_rvar a (S n)) v =
  \big[Rplus/0]_(a' : imgT (h a)) (pr_eq (h a) (sval a') * pr_eq (recN_rvar (sval a') n) v).
Proof.
  transitivity (Ex (rvar_comp (h a) (fun a' =>  pr_eq (recN_rvar a' n) v))). 
  - rewrite Ex_fin_pt. rewrite /pr_eq/pr //= SeriesC_fin_big.
     rewrite ?/index_enum {1}[@Finite.enum]unlock //=.
     rewrite /tag_enum. rewrite big_flatten //=. 
     induction (Finite.enum (B a)).
     * rewrite //= ?big_nil //.
     * rewrite 2!big_cons_Rplus //=. f_equal; auto.
       rewrite ?SeriesC_fin_big.
       rewrite ?/index_enum. 
       induction (Finite.enum (recN_space ((h a) a0) n)).
       ** by rewrite //= ?big_nil Rmult_0_l.
       ** rewrite //= ?big_cons_Rplus //=.
          rewrite Rmult_plus_distr_r.
          f_equal; auto. rewrite Rmult_if_distrib Rmult_0_l Rmult_comm.
          apply if_case_match.
          rewrite ?in_set //=. 
  - rewrite Ex_fin_comp. done. 
Qed.

Lemma recN_pr_unfold_comp (f: X → R) a n v:
  pr_eq (rvar_comp (recN_rvar a (S n)) f) v =
  \big[Rplus/0]_(a' : imgT (h a)) (pr_eq (h a) (sval a') 
                                  * pr_eq (rvar_comp (recN_rvar (sval a') n) f) v).
Proof.
  transitivity (Ex (rvar_comp (h a) (fun a' =>  pr_eq (rvar_comp (recN_rvar a' n) f) v))). 
  - rewrite Ex_fin_pt. rewrite /pr_eq/pr //= ?SeriesC_fin_big.
     rewrite ?/index_enum {1}[@Finite.enum]unlock //=.
     rewrite /tag_enum. rewrite big_flatten //=. 
     induction (Finite.enum (B a)).
     * rewrite //= ?big_nil //.
     * rewrite 2!big_cons_Rplus //=. f_equal; auto.
       rewrite ?SeriesC_fin_big.
       rewrite ?/index_enum. 
       induction (Finite.enum (recN_space ((h a) a0) n)).
       ** by rewrite //= ?big_nil Rmult_0_l.
       ** rewrite //= ?big_cons_Rplus //=.
          rewrite Rmult_plus_distr_r.
          f_equal; auto. rewrite Rmult_if_distrib Rmult_0_l Rmult_comm.
          apply if_case_match.
          rewrite ?in_set //=. 
  - rewrite Ex_fin_comp. apply eq_bigr => ?. rewrite Rmult_comm //.
Qed.

Lemma recN_pr_pr_rec a n v:
  pr_eq (recN_rvar a n) v = pr_rec a n v.
Proof.
  revert a v. induction n => a v //=. 
  - eapply recN_pr_base.
  - rewrite recN_pr_unfold. 
    apply eq_bigr => ??. rewrite IHn //=.
Qed.

Lemma recN_pr_gt f n z v: 
  pr_gt (rvar_comp (recN_rvar z (S n)) f) v = 
    \big[Rplus/0]_(i : (imgT (h z))) (pr_eq (h z) (sval i) 
                                      * pr_gt (rvar_comp (recN_rvar (sval i) n) f) v).
Proof.
  rewrite /pr_gt pr_gt_alt3.
  etransitivity.
  { apply eq_bigr. intros ??. rewrite recN_pr_unfold_comp //. }
  rewrite exchange_big.
  apply eq_bigr => x' _.
  rewrite -big_distrr.
  eapply Rmult_eq_0_inv_r => Hneq.
  rewrite pr_gt_alt3.
  symmetry.
  rewrite !big_filter //=.
  rewrite [@Finite.enum]unlock //=.
  rewrite (img_fin_big' _ (λ i, (pr_eq (rvar_comp _ _) i)) (λ x, Rgt_dec x v)). 
  rewrite (img_fin_big' _ (λ i, (pr_eq (rvar_comp _ _) i)) (λ x, Rgt_dec x v)). 
  eapply sum_reidx_map with (h0 := λ x, x); auto.
  - intros a Hin' ->; split; auto.
    apply img_alt'.
    destruct x' as (x&Hin). rewrite //= in Hneq. rewrite //= in Hin'.
    apply img_alt in Hin as (x0&?).
    apply img_alt' in Hin' as (x1&?).
    subst; exists (existT (x0) x1). done.
  - intros b Hin' Hgt Hfalse.
    assert (∀ x, 0 ≤ x → (x > 0 → False) → x = 0) as Hcases.
    {
      inversion 1. intros Hbad. exfalso. apply Hbad. fourier.
      done.
    }
    apply Hcases.
    * apply Rge_le; first apply ge_pr_0.
    * intros Hin''%pr_img.
      apply Hfalse. exists b. split; auto.
      apply img_alt'. apply img_alt. auto.
  - rewrite /img. apply undup_uniq.
  - rewrite /img. apply undup_uniq.
Qed.


Lemma recN_pr_unfold' a n v:
  pr_eq (recN_rvar a (S n)) v =
  \big[Rplus/0]_(a' : imgT (recN_rvar a n)) (pr_eq (h (sval a')) v * pr_eq (recN_rvar a n) (sval a')).
Proof.
  revert a v.
  induction n => a v.
  - rewrite recN_pr_pr_rec //=. symmetry. etransitivity. eapply eq_bigr.
    intros; rewrite (recN_pr_base _ a). done.
    rewrite ?recN_pr_unfold.
    rewrite //= /enum_mem/index_enum {1}[@Finite.enum]unlock //=.
    rewrite (img_fin_big' _ (λ i, pr_eq (h i) v * (if a == i then 1 else 0)) (λ x, true)) //=.
    rewrite //= /enum_mem/index_enum {1}[@Finite.enum]unlock //=.
    rewrite big_seq1.
    rewrite eq_refl Rmult_1_r.
    symmetry; etransitivity; first eapply eq_bigr.
    { intros. rewrite Rmult_comm Rmult_if_distrib Rmult_0_l Rmult_1_l //. }
    rewrite -big_mkcondr.
    rewrite /pr_eq.
    destruct (ge_pr_0 (rvar_dist (h a)) (λ a0 : B a, (h a) a0 == v)) as [Hlt|Heq0]. 
    * apply pr_img in Hlt => //=.
      rewrite //= /enum_mem/index_enum {1}[@Finite.enum]unlock //=.
      rewrite -(big_map sval (λ i, i == v) (λ i, pr (rvar_dist (h a)) (λ a0 : B a, (h a) a0 == i))).
      rewrite img_fin_enum_sval. 
      rewrite -big_filter.
      rewrite filter_pred1_uniq; auto.
      ** rewrite /rvar_dist //= big_cons big_nil //=; field.
      ** apply undup_uniq.
      ** apply img_alt'. apply img_alt. auto.
    * rewrite Heq0. 
      rewrite big_seq_cond.
      apply big1 => i.
      rewrite //=. move /andP => [Hin Heq']. move /eqP in Heq'.
      subst. auto.
  - rewrite recN_pr_unfold.
    etransitivity. 
    { eapply eq_bigr.
      intros. rewrite IHn. reflexivity. }
    rewrite //=.
    symmetry.
    etransitivity. 
    { intros. eapply eq_bigr. intros. rewrite recN_pr_unfold.
      reflexivity. }
    rewrite //=.
    etransitivity.
    { eapply eq_bigr. intros. rewrite big_distrr.
      reflexivity. }
    rewrite //=.
    rewrite exchange_big. rewrite //=.
    eapply eq_bigr.
    intros i _. 
    rewrite big_distrr //=.
    symmetry.
    rewrite /index_enum. 
  rewrite [@Finite.enum]unlock //=.
  rewrite (img_fin_big' _ 
       (λ x, (pr_eq (h a) (sval i) * (pr_eq (h x) v * pr_eq (recN_rvar (sval i) n) x)))
       (λ x, true)).
  rewrite (img_fin_big' _ 
       (λ x, (pr_eq (h x) v * (pr_eq (h a) (sval i) * pr_eq (recN_rvar (sval i) n) x)))
       (λ x, true)).
  destruct i as (i&Hin).
  destruct (proj1  (img_alt _ _) Hin) as (x&Heq).
    eapply sum_reidx_map with (h0 := λ x, x).
    * intros; field.
    * intros a' (s&Heq')%img_alt' _.
      split; auto. apply img_alt'.
      subst. exists (existT (x) s). done.
    * intros b Hin' Hgt Hfalse.
      rewrite /pr.
      destruct (ge_pr_0 (rvar_dist (recN_rvar i n))
                        (λ x, (recN_rvar i n) x == b)) as [Hlt|Heq'].
      ** contradiction Hfalse.
         apply Rlt_gt, pr_img in Hlt.
         exists b. repeat split; auto. apply img_alt', img_alt. done.
      ** rewrite /pr_eq.  rewrite ?Heq'. field.
  * rewrite /img. apply undup_uniq.
  * rewrite /img. apply undup_uniq.
  * intros ??. trivial.
Qed.

Lemma recN_pr_unfold_comp' (f: X → R) a n v:
  pr_eq (rvar_comp (recN_rvar a (S n)) f) v =
  \big[Rplus/0]_(a' : imgT (recN_rvar a n)) (pr_eq (rvar_comp (h (sval a')) f) v
                                             * pr_eq (recN_rvar a n) (sval a')).
Proof.
  revert a v.
  induction n => a v.
  - rewrite recN_pr_unfold_comp //=. symmetry. etransitivity. eapply eq_bigr.
    intros; rewrite (recN_pr_base _ a). done.
    rewrite ?recN_pr_unfold_comp.
    rewrite //= /enum_mem/index_enum {1}[@Finite.enum]unlock //=.
    rewrite (img_fin_big' _ (λ i, pr_eq (rvar_comp (h i) f) v 
                                  * (if a == i then 1 else 0)) (λ x, true)) //=.
    rewrite //= /enum_mem/index_enum {1}[@Finite.enum]unlock //=.
    rewrite big_seq1.
    rewrite eq_refl Rmult_1_r.
    symmetry; etransitivity; first eapply eq_bigr.
    { intros. rewrite recN_pr_comp_base Rmult_comm Rmult_if_distrib Rmult_0_l Rmult_1_l //. }
    rewrite /pr_eq. rewrite pr_eq_alt_comp. rewrite /index_enum. eauto.
  - rewrite recN_pr_unfold_comp.
    etransitivity. 
    { eapply eq_bigr. intros. rewrite IHn.
      reflexivity. }
    rewrite //=.
    symmetry.
    etransitivity. 
    { intros. eapply eq_bigr. intros. rewrite recN_pr_unfold.
      reflexivity. }
    rewrite //=.
    etransitivity.
    { eapply eq_bigr. intros. rewrite big_distrr.
      reflexivity. }
    rewrite //=.
    rewrite exchange_big. rewrite //=.
    eapply eq_bigr.
    intros i _. 
    rewrite big_distrr //=.
    symmetry.
    rewrite /index_enum. 
    rewrite [@Finite.enum]unlock //=.
    rewrite (img_fin_big' _ 
       (λ x, (pr_eq (h a) (sval i) * (pr_eq (rvar_comp (h x) f) v * pr_eq (recN_rvar (sval i) n) x)))
       (λ x, true)).
    rewrite (img_fin_big' _ 
       (λ x, (pr_eq (rvar_comp (h x) f) v * (pr_eq (h a) (sval i) * pr_eq (recN_rvar (sval i) n) x)))
       (λ x, true)).
    destruct i as (i&Hin).
    destruct (proj1  (img_alt _ _) Hin) as (x&Heq).
    eapply sum_reidx_map with (h0 := λ x, x).
    * intros; field.
    * intros a' (s&Heq')%img_alt' _.
      split; auto. apply img_alt'.
      subst; exists (existT (x) s). done.
    * intros b Hin' Hgt Hfalse.
      rewrite /pr.
      destruct (ge_pr_0 (rvar_dist (recN_rvar i n))
                        (λ x, (recN_rvar i n) x == b)) as [Hlt|Heq'].
      ** contradiction Hfalse.
         apply Rlt_gt, pr_img in Hlt.
         exists b. repeat split; auto. apply img_alt', img_alt. done.
      ** rewrite /pr_eq.  rewrite ?Heq'. field.
  * rewrite /img. apply undup_uniq.
  * rewrite /img. apply undup_uniq.
  * intros ??. trivial.
Qed.

Lemma recN_space_snoc n z (xn: recN_space z n) (xSn: B (recN_fun z n xn)) : recN_space z (S n).
Proof.
  revert z xn xSn.
  induction n => z xn xSn.
  - exact (existT (xSn) tt).
  - destruct xn as (x0&xn'). 
    exact (existT x0 (IHn _ xn' xSn)).
Defined.

Lemma h_recN_space_snoc n z xn xSn:
  h (recN_rvar z n xn) xSn = recN_fun (h z (projT1 (recN_space_snoc n z xn xSn)))
                                         n (projT2 (recN_space_snoc n z xn xSn)).
Proof.
  revert z xn xSn.
  induction n; rewrite //=.
  destruct xn => //= xSn. rewrite IHn. 
  destruct (recN_space_snoc _ _ _) => //.
Qed.

Lemma recN_pr_gt' f n z v: 
  pr_gt (rvar_comp (recN_rvar z (S n)) f) v = 
    \big[Rplus/0]_(i : imgT (recN_rvar z n))
     (pr_eq (recN_rvar z n) (sval i)  * pr_gt (rvar_comp (h (sval i)) f) v).
Proof.
  rewrite /pr_gt pr_gt_alt3.
  etransitivity.
  { apply eq_bigr. intros ??. rewrite recN_pr_unfold_comp' //. }
  rewrite exchange_big.
  apply eq_bigr => x' _.
  rewrite -big_distrl Rmult_comm.
  eapply Rmult_eq_0_inv_l => Hneq.
  rewrite pr_gt_alt3.
  symmetry.
  rewrite !big_filter //=.
  rewrite [@Finite.enum]unlock //=.
  rewrite (img_fin_big' _ (λ i, (pr_eq (rvar_comp _ _) i)) (λ x, Rgt_dec x v)). 
  rewrite (img_fin_big' _ (λ i, (pr_eq (rvar_comp _ _) i)) (λ x, Rgt_dec x v)). 
  eapply sum_reidx_map with (h0 := λ x, x); auto.
  - intros a Hin' ->; split; auto.
    apply img_alt'.
    destruct x' as (x&Hin). rewrite //= in Hneq. rewrite //= in Hin'.
    apply img_alt in Hin as (x0&Hx0).
    apply img_alt' in Hin' as (x1&?).
    subst.
    specialize (h_recN_space_snoc n _ x0 x1) => Hhrec.
    edestruct (recN_space_snoc n _ x0 x1) as (x&s).
    exists (existT x s).  rewrite Hhrec => //.
  - intros ??? Hfalse.
      destruct (ge_pr_0 (rvar_dist (rvar_comp (h (sval x')) f))
                        (λ x, f ((h (sval x')) x) == b)) as [Hlt|Heq']; 
        last by rewrite //=.
      contradiction Hfalse.
      apply Rlt_gt in Hlt.
      apply (pr_img (rvar_comp (h (sval x')) f)) in Hlt.
      exists b. repeat split; auto. apply img_alt', img_alt; auto.
  - rewrite /img. apply undup_uniq.
  - rewrite /img. apply undup_uniq.
Qed.
End rec_var.

Arguments recN_space {_ _ _} _ _ _.
Arguments recN_rvar {_ _ _} _ _ _.


Section lemma31.


Variable A : finType.
Variable Ω: distrib A.
Variable X: rrvar Ω.
Variable f: R → R.
Variable x c: R.

Hypothesis xgt : x > 0.
Hypothesis cgt : c > 0.
Hypothesis Xrange: ∀ r,  r \in img X → 0 ≤ r ∧ r ≤ x.

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

Lemma lemma31: Ex (rvar_comp X f) ≤ Ex X * f (Rmin x c) / (Rmin x c).
Proof.
  rewrite /Rdiv Rmult_assoc Rmult_comm.
  rewrite ?Ex_fin_pt//=.
  rewrite big_distrr//=.
  apply Rle_bigr => i Hin.
  rewrite -Rmult_assoc.
  apply Rmult_le_compat; auto; try reflexivity.
    * apply Rge_le, pmf_pos. 
    * destruct (Xrange (X i)) as ([Hgt|HX0]&?).
      { apply img_alt; eauto. }
      ** apply (Rmult_le_reg_r (Rdiv 1 (X i))). 
         apply Rdiv_lt_0_compat; fourier. 
         transitivity (f (Rmin x c) / (Rmin x c)); last first.
         *** apply Req_le. rewrite //=. rewrite /Rdiv. field; split.
             **** by apply Rlt_not_eq'.
             **** apply min_xc_neq0.
         *** rewrite -Rmult_assoc.
             rewrite Rmult_1_r.
             destruct (Rlt_or_le (X i) c) as [?|Hge'].
             **** eapply fnondec; repeat split; auto; try fourier.
                  { apply Rmin_case; fourier. }
                  { apply Rmin_case; fourier. }
                  { apply Rmin_r. }
             **** assert (Rmin x c = c) as ->.
                  { apply Rmin_right. fourier. }
                  rewrite //= in Hge'.
                  rewrite frange2; last fourier.
                  rewrite frange2; last fourier.
                  rewrite /Rdiv. apply Rmult_le_compat; try fourier.
                  { apply Rlt_le. apply Rinv_0_lt_compat. fourier. }
                  eapply Rinv_le_contravar; auto. 
      ** rewrite -HX0 f0 Rmult_0_r. fourier.
Qed.

End lemma31.

Section karp_bound_sec.

Variable X: eqType.
Variable size: X → R.
Variable A B : X → finType.
Variable ΩT : ∀ x : X, distrib (A x).
Variable Ωh : ∀ x : X, distrib (B x).
Variable T: ∀ x: X, rrvar (ΩT x).
Variable h: ∀ x: X, rvar (Ωh x) X.

(* Sometimes it is natural to only consider cases where an invariant
   is preserved throughout the recurrence. We use this parameter P for
   such invariants rather than subtyping X because it can be more natural
   *)
Variable P: X → Prop.
Variable a m: R → R.
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
Variable m_bound_Eh: ∀ x, Ex (rvar_comp (h x) size) ≤ m (size x).


Variable u_cont: ∀ x, d < x → continuity_pt u x.
Variable a_cont: ∀ x, d < x → continuity_pt a x.

(* Technically, I don't think Karp states this assumption but it appears to be needed *)
Hypothesis T_non_neg: ∀ x n, (T x) n ≥ 0.

Hypothesis Trec: 
  ∀ x r, P x → pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h x)) 
                ((pr_eq (h x) (sval x')) * pr_gt (T (sval x')) (r - a (size x))).

Hypothesis urec: 
  ∀ x, x > d →  u x ≥ a x + u (m x). 

Hypothesis hP: ∀ x n, P x → P ((h x) n).
Hypothesis hrange1: ∀ x n, size ((h x) n) ≤ size x.
Hypothesis hrange2: ∀ x n, d < size x →  0 ≤ size ((h x) n).

Hypothesis alower: ∀ x, x ≤ d → a x = 0.
Hypothesis a_nonneg: ∀ x, a x ≥ 0.
Hypothesis a_mono: Rmono a.
Hypothesis a_pos: ∀ x, d < x → 0 < a x.
Hypothesis mnondec: ∀ y y', 0 < y → y ≤ y' → (m y / y) ≤ (m y' / y').
Hypothesis d_non_neg: 0 ≤ d.

(* Karp does not state this assumption, but Neal Young has suggested that _some_ additional
   assumption is needed, and the following suffices *)
(* In any case, I believe this follows from prior assumptions + Markov's inequality
   if lim_(n -> infty) m^n(x) < d. *)
Hypothesis hinf_0: ∀ a eps, eps > 0 → ∃ n, pr_gt (rvar_comp (recN_rvar h a n) size) d < eps. 

(* Karp does not have an assumption like the following either. *)
Hypothesis Tbelow: ∀ x e, size x ≤ d → (T x) e ≤ umin.

Hypothesis mpos: ∀ x, 0 ≤ x → 0 ≤ m x.

Definition K r z := pr (rvar_dist (T z)) (λ n, Rgt_dec ((T z) n) r).

Lemma umin_lb_simple: ∀ x, x ≥ d → umin ≤ u x.
Proof.
  rewrite /Rge => x [Hgt|Heq].
  - transitivity (u x - a x); first auto. assert (a x > 0) by (apply a_pos; auto).
    fourier.
  - subst. reflexivity.
Qed.

Lemma K_alt4 r z: 
  P z → K r z ≤ \big[Rplus/0]_(i : imgT (h z)) (pr_eq (h z) (sval i) * (K (r - (a (size z))) (sval i))).
Proof.
  rewrite /K; eauto.
Qed.

Definition K0 r (z: X) :=
  if (Rlt_dec r umin) then
    1
  else
    0.

Fixpoint Krec i r x := 
  match i with
    | 0 => K0 r x
    | S i' => Ex (rvar_comp (h x) (Krec i' (r - a (size x))))
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
         1
      else
        (m x / x)^(Z.to_nat (round r x)) * (x / (u' (r - a(x) * IZR (round r x)))).

Definition Dalt r x := 
  if Rle_dec r umin then
    1
  else
    if Rle_dec x d then
        0
    else
      if Rlt_dec r (u x) then
         1
      else
        (m x / x)^(Z.to_nat (round r x)) * (x / (u' (r - a(x) * IZR (round r x)))).

Lemma Rceil_0: Rceil 0 = 0%Z.
Proof.          
  rewrite /Rceil. replace 0 with (IZR 0) by auto.
  rewrite fp_R0 eq_refl. rewrite Int_part_IZR //=.
Qed.

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
      rewrite /Rdiv Rmult_1_l Rinv_r //.
      apply Rgt_not_eq. fourier.
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

Lemma K_unfold r x: P x → K r x ≤ Ex (rvar_comp (h x) (K (r - a (size x)))).
Proof.
  etransitivity; first apply K_alt4; auto.
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
      ** rewrite //=. rewrite -big_distrr //=. rewrite -SeriesC_fin_big pmf_sum1_Series. nra.
      ** exfalso. eapply Hfalse.
         specialize (a_nonneg (size x)). intros. 
         fourier.
    * destruct Rlt_dec as [|].
      ** rewrite //=. rewrite -big_distrr //=. rewrite -SeriesC_fin_big pmf_sum1_Series. nra.
      ** rewrite //=. right. symmetry; apply big1 => ??. nra.
  - rewrite /Krec ?Ex_fin_pt. 
    apply Rle_bigr => i ?.
    etransitivity. 
    * apply Rmult_le_compat_r.
      { apply Rge_le, pmf_pos. }
      { eapply IHi'. }
    * rewrite //= ?Ex_fin_pt /rvar_comp //=; reflexivity.
Qed.

Lemma Krec_non_dec (i i': nat) r x: (i ≤ i')%nat → Krec i r x ≤ Krec i' r x.
Proof.
  induction 1; first reflexivity.
  etransitivity; [ apply IHle | apply Krec_non_decS ]. 
Qed.

Lemma Krec_bound01 r x i: 0 ≤ Krec i r x ∧ Krec i r x ≤ 1.
Proof.
  revert r x.
  induction i => r x. 
  - rewrite //= /K0. split; destruct Rlt_dec => //=; fourier. 
  - rewrite /Krec. rewrite Ex_fin_pt /rvar_comp //=; split. 
    * eapply Rle_big0 => ??.
      rewrite -[a in a ≤ _](Rmult_0_l 0).
      apply Rmult_le_compat; try fourier; last (apply Rge_le, pmf_pos).
      edestruct IHi; eauto.
    * transitivity (\big[Rplus/0]_(a in B x) (rvar_dist (h x) a)).
      ** eapply Rle_bigr => a' ?. specialize (IHi (r - a (size x)) ((h x) a')). 
         rewrite -[a in _ ≤ a](Rmult_1_l).
         eapply Rmult_le_compat_r; first (apply Rge_le, pmf_pos).
         edestruct IHi; eauto.
      ** right. rewrite -SeriesC_fin_big. apply pmf_sum1_Series.
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


Lemma Rle_lub_eps x E v: 
  is_lub E v → 
  (∀ eps, eps > 0 → ∃ v, E v ∧ x ≤ v + eps) →
  x ≤ v.
Proof.
  intros [Hub ?] Hle. eapply le_epsilon => eps Hgt0.
  destruct (Hle eps Hgt0) as (v'&HE&Hle'). 
  specialize (Hub v' HE). fourier.
Qed.

Lemma K_Krec_leq_below i r x: size x ≤ d → K r x ≤ Krec i r x.
Proof.
  revert r x. induction i as [| i'] => r x Hle.
  - rewrite /K /Krec /K0 //=.
    destruct (Rlt_dec).
    + intros. eapply pr_le_1. 
    + rewrite /pr//=. right. rewrite SeriesC_fin_big. eapply big1 => b ?. 
      rewrite //=. destruct (Rgt_dec) as [?|Hnlt] => //=; try nra.
      specialize (Tbelow _ b Hle).
      exfalso. destruct (T x); simpl in *. nra. 
  - etransitivity; first eapply IHi'; eauto.
    apply Krec_non_decS.
Qed.

Lemma K_Krec_bounded_gap i r x: K r x ≤ Krec i r x + 1.
Proof.
  transitivity 1; first apply pr_le_1.
  destruct (Krec_bound01 r x i). fourier.
Qed.

Definition recN_a {i: nat} x (b: @recN_space _ _ _ h x i) : R.
  revert x b. induction i.
  - intros x ?. exact 0.
  - intros x (b&b'). 
    exact (a (size x) + IHi ((h x) b) b').
Defined.

Lemma Krec_unfold_recN_varS r x i: 
  Krec i r x = \big[Rplus/0]_(b in @recN_space _ _ _ h x i) (Krec 0 (r - recN_a x b) (recN_rvar h x i b) 
                                                * `(rvar_dist (recN_rvar h x i)) b).
Proof.
  revert r x.
  induction i => r x.
  - by rewrite /index_enum {1}[@Finite.enum]unlock big_seq1 //= Rmult_1_r Rminus_0_r.
  - rewrite {1}/Krec -/Krec Ex_fin_pt //=/rvar_comp. 
    etransitivity. 
    * eapply eq_bigr. intros. rewrite IHi big_distrl. reflexivity. 
    * rewrite //=. 
      rewrite nested_sum_recN_space //=.
      apply eq_bigr => ib H. destruct ib. 
      rewrite Rmult_assoc.
      f_equal.
      ** f_equal. by rewrite /Rminus Ropp_plus_distr Rplus_assoc.
      ** by rewrite Rmult_comm.
Qed.

Lemma K_unfold_recN_varS r x i: 
  P x →
  K r x ≤ \big[Rplus/0]_(b in @recN_space _ _ _ h x i) (K (r - recN_a x b) (recN_rvar h x i b) 
                                                * (rvar_dist (recN_rvar h x i)) b).
Proof.
  revert r x.
  induction i => r x HP.
  - right. by rewrite /index_enum {1}[@Finite.enum]unlock big_seq1 //= Rmult_1_r Rminus_0_r.
  - etransitivity; first apply K_unfold; auto.
    rewrite /K Ex_fin_pt /rvar_comp //=.
    etransitivity. 
    * etransitivity.
      ** eapply Rle_bigr. intros. 
         apply Rmult_le_compat_r. 
         *** apply Rge_le, pmf_pos. 
         *** apply IHi. eauto.
      ** right. apply eq_bigr => ??. rewrite big_distrl; reflexivity.
    * rewrite //=. 
      rewrite nested_sum_recN_space //=.
      right.
      apply eq_bigr => ib H. destruct ib. 
      rewrite Rmult_assoc.
      f_equal.
      ** f_equal. by rewrite /Rminus Ropp_plus_distr Rplus_assoc.
      ** by rewrite Rmult_comm.
Qed.

Lemma diff_bound x y z: 0 ≤ x → x ≤ z → 0 ≤ y → y ≤ z → x + -y ≤ z.
Proof. intros; fourier. Qed.

Lemma Rle_plus_minus x y z: x - y ≤ z → x ≤ z + y.
Proof. intros. fourier. Qed.                                        

Require Import Coq.Classes.Morphisms.
Instance Rle_plus_proper: Proper (Rle ==> Rle ==> Rle) Rplus.
Proof.
  intros ?? Hle ?? Hle'. apply Rplus_le_compat; auto.
Qed.

Lemma K_le_supKrec r x: P x → K r x ≤ Krec_sup r x.
Proof.
  intros HP.
  eapply (Rle_lub_eps _ _ _ (Krec_sup_is_lub _ _)) => eps Hgt0.
  destruct (hinf_0 x eps Hgt0) as [i Hhlt].
  exists (Krec i r x); split; eauto.
  rewrite Krec_unfold_recN_varS. 
  setoid_rewrite (K_unfold_recN_varS _ _ i); last done.
  rewrite (bigID (λ b, Rgt_dec (size ((recN_rvar h x i) b)) d)) //=.
  rewrite [a in _ ≤ a + _](bigID (λ b, Rgt_dec (size ((recN_rvar h x i) b)) d)) //=.
  rewrite [a in _ ≤ a]Rplus_comm -Rplus_assoc.
  eapply Rplus_le_compat.
  - apply Rle_plus_minus, diff_bound.
    * eapply Rle_big0 => ??.
      rewrite -[a in a ≤ _](Rmult_0_l 0).
      apply Rmult_le_compat; try fourier; eauto using Rge_le, pmf_pos, recN_0, ge_pr_0.
    * etransitivity; last (by rewrite /pr_gt /pr_eq /pr in Hhlt; left; eapply Hhlt).
      rewrite SeriesC_fin_big.
      rewrite /index_enum. 
      eapply Rle_bigr'.
      ** intros ?. destruct (Rgt_dec) => //= _. split; auto.
         rewrite //=. rewrite -[a in _  ≤ a]Rmult_1_l; 
            apply Rmult_le_compat; try nra; eauto.
           *** apply Rge_le, ge_pr_0. 
           *** apply Rge_le, recN_0.
           *** apply pr_le_1.
      ** intros. rewrite //=. destruct (Rgt_dec) => //=. reflexivity.
    * eapply Rle_big0 => ??.
      rewrite -[a in a ≤ _](Rmult_0_l 0).
      apply Rmult_le_compat; try fourier; eauto using Rge_le, ge_pr_0, recN_0. 
      eapply (proj1 (Krec_bound01 _ _ 0)). 
    * etransitivity; last (rewrite /pr_gt /pr_eq /pr in Hhlt; left; eapply Hhlt).
      rewrite SeriesC_fin_big.
      rewrite /index_enum. 
      eapply Rle_bigr'.
      ** intros ?. destruct (Rgt_dec) => //= _. split; auto.
         rewrite //=. rewrite -[a in _  ≤ a]Rmult_1_l; 
            apply Rmult_le_compat; try nra; eauto.
          *** eapply (proj1 (Krec_bound01 _ _ 0)). 
          *** apply Rge_le, recN_0.
          *** eapply (proj2 (Krec_bound01 _ _ 0)). 
      ** intros. destruct (Rgt_dec) => //=. reflexivity.
  - apply Rle_bigr => b //=.
    move /negP. destruct (Rgt_dec) as [|Hngt] => //= _.
    apply Rmult_le_compat_r.
    * apply Rge_le, recN_0.
    * apply (K_Krec_leq_below 0).
      apply Rnot_lt_ge in Hngt. fourier.
Qed.


Lemma Rmult_pos x y: 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
Proof. 
  intros. rewrite -[a in a ≤ _](Rmult_0_l 0).
  apply Rmult_le_compat; eauto; try reflexivity.
Qed.

Lemma D0_aux r x:
   0 < x → 0 ≤ (m x / x) ^ Z.to_nat (round r x) * (x / u' (r - a x * IZR (round r x))).
Proof.                                             
  intros Hlt.
    eapply Rmult_pos. 
    * eapply pow_le. rewrite /Rdiv.
      eapply Rle_mult_inv_pos; eauto.
      eapply mpos. left. done.
    * rewrite /round //=. 
      eapply Rle_mult_inv_pos.
      ** fourier.
      ** eapply u'_pos.
Qed.

Lemma D0 r x:
  0 ≤ D r x.
Proof.                                             
  rewrite /D.
  destruct (Rle_dec) => //=; intros; try nra.
  destruct (Rle_dec) => //=; intros; try nra.
  destruct (Rle_dec) => //=; intros; try nra.
  intros. apply D0_aux. 
  nra.
Qed.

Lemma Rmult_nonneg x y: 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
Proof.
  intros. rewrite -(Rmult_0_l 0). apply Rmult_le_compat; eauto; try reflexivity.
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

Lemma Rinv_pos z: 0 < z → 0 ≤ / z.
Proof.
  intros. rewrite -(Rmult_1_l (/ z)). apply Rle_mult_inv_pos; auto; fourier.
Qed.

Lemma Dnondec r x x':
    r > umin →
    (x ≤ x') ∧ 
    (0 < x ∧ x ≤ (u' r)) ∧
    (0 < x' ∧ x' ≤ (u' r)) →
    (D r x / x) ≤ (D r x' / x').
Proof.
  intros Hr (Hle&(Hxrange1&Hxrange2)&(Hx'range1&Hx'range2)).
  assert (0 < r) by fourier.
  rewrite ?D_Dalt_equiv.
  rewrite /Dalt //=.
  destruct (Rle_dec) => //=; first nra.
  destruct (Rle_dec) => //=.
  { 
    destruct (Rle_dec) => //=; first nra.
    rewrite /Rdiv ?Rmult_0_l //=. 
    destruct (Rlt_dec) => //=; eapply Rle_mult_inv_pos; try fourier.
    eapply D0_aux; eauto.
  }
  destruct (Rlt_dec) => //=.
  { 
    destruct (Rle_dec) => //=.
    { exfalso. nra. }
    destruct (Rlt_dec) => //=.
    {assert (x = x') as ->.
      { destruct Hle as [Hlt|]; auto.
        exfalso. eapply u_strict_inc in Hlt; eauto; try nra.
        apply u_mono in Hxrange2. apply u_mono in Hx'range2.
        assert (u x ≤ r) by (etransitivity; eauto using uu').
        assert (u x' ≤ r) by (etransitivity; eauto using uu').
        fourier.
      }
      reflexivity.
    }
    exfalso. assert (u x' < u x) by nra.
    destruct Hle as [Hlt|]; subst.
    - apply u_strict_inc in Hlt; nra.
    - nra.
  }
  destruct (Rle_dec) => //=.
  { intros; exfalso; nra. }
  destruct (Rlt_dec) => //=.
  { 
    exfalso. apply u_mono in Hx'range2. assert (u x' ≤ r) by (etransitivity; eauto using uu').
    nra.
  }
  eapply (Rceil_interval_decompose_P
            (λ x, 0 < x ∧ d < x ∧ x ≤ u' r)
            (λ z x, (m x / x) ^ Z.to_nat z * (x / u' (r - a x * IZR z)) / x)
            (λ x,  (r - u x) / a x)); eauto.
  - intros ?? (?&(?&?)) (?&(?&?)) z; repeat split; fourier.
  - intros k (xk&Hxk) z z' (?&(?&?)) (?&(?&?)) Hlez.
    assert (Hpow_pos: ∀ k z, 0 < z → 0 ≤ (m z / z) ^ k).
    { intros k' ? Hgt; induction k' => //=; try fourier.
      apply Rmult_nonneg; auto.
      apply Rle_mult_inv_pos; auto. apply mpos; fourier.
    }
    rewrite ?/Rdiv.
    rewrite Rmult_assoc.
    rewrite [a in _ ≤ a]Rmult_assoc.
    apply Rmult_le_compat; eauto; try fourier.
    * apply Rmult_nonneg; auto.
      ** apply Rle_mult_inv_pos; first fourier. apply Rgt_lt, u'_pos.
      ** rewrite -(Rmult_1_l (/ z)). apply Rle_mult_inv_pos; fourier.
    * induction (Z.to_nat k) => //=; try fourier.
      apply Rmult_le_compat; eauto.
      ** move: (Hpow_pos 1%nat z). rewrite //= Rmult_1_r. eauto.
    * assert (∀ a b, 0 < a → a * b * / a = b) as Hcancel.
      { clear. intros. rewrite (Rmult_comm a) Rmult_assoc.
        rewrite Rinv_r; first rewrite Rmult_1_r //.
        by apply Rgt_not_eq.
      }
      rewrite ?Hcancel //.
     apply Rinv_le_contravar; try eapply u'_pos. apply u'_mono.
      specialize (a_mono z z' Hlez). intros.
      assert (IZR k ≥ 0).
      { apply Rle_ge. replace 0 with (IZR 0) by auto.
        apply IZR_le. 
        destruct Hxk as ((?&(?&?%uu'_adjoint))&<-).
        replace 0%Z with (Rceil 0); last first.
        { 
          rewrite /Rceil. replace 0 with (IZR 0) by auto.
          rewrite fp_R0 eq_refl. rewrite Int_part_IZR //=.
        }
        apply Rceil_mono.
        apply Rle_mult_inv_pos; auto; try fourier.
        - fourier.
      }
      generalize (a_nonneg z) => ?.
      specialize (a_nonneg z'); intros.
      rewrite /Rminus. apply Rplus_le_compat_l.
      apply Ropp_le_contravar.
      apply Rmult_le_compat; fourier.
  -  intros k z (?&?&Hzle) Heq. 
     assert (Hkpos: (0 <= k)%Z). 
     { apply le_IZR. replace (IZR 0) with 0 by auto.
       rewrite -Heq. 
       apply Rle_mult_inv_pos; auto using a_pos. 
       rewrite uu'_adjoint in Hzle *; intros; fourier.
     }
     destruct (Req_dec (m z) 0) as [Heq0|Hneq0].
     { 
       rewrite ?Heq0. apply Rle_ge.
       rewrite Z2Nat.inj_add //=.
       rewrite (plus_comm) //=.
       rewrite /Rdiv. rewrite ?Rmult_0_l ?Rmult_1_l.
       repeat apply Rmult_pos; try fourier.
       * induction (Z.to_nat) => //=; try fourier.
       * apply Rinv_pos, u'_pos.
       * apply Rinv_pos; fourier.
     }
     assert (0 < m z).
     { edestruct (mpos z); try fourier. congruence. }
     apply (Rmult_eq_compat_r (a z)) in Heq.
     rewrite /Rdiv Rmult_assoc Rinv_l in Heq; last apply Rgt_not_eq, a_pos; auto.
     rewrite Rmult_1_r Rmult_comm in Heq.
     apply (Rplus_eq_compat_r (u z)) in Heq.
     rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_r in Heq.
     apply (Rplus_eq_compat_l (-(a z * IZR k))) in Heq.
     rewrite -Rplus_assoc Rplus_opp_l Rplus_0_l Rplus_comm in Heq.
     rewrite /Rminus.
     generalize (urec z) => Hrec.
     rewrite -Heq in Hrec.
     assert (Heq': u (m z) ≤ r + - (a z * (IZR (k+ 1)))).
     { rewrite plus_IZR. replace (IZR 1) with 1 by auto. 
       rewrite Rmult_plus_distr_l Rmult_1_r.
       rewrite Ropp_plus_distr. apply (Rplus_ge_compat_r (- a z)), Rge_le in Hrec; auto.
       rewrite Rplus_comm -Rplus_assoc Rplus_opp_l Rplus_0_l ?Rplus_assoc in Hrec; auto.
     }
     intros.
     apply uu'_adjointlr in Heq'; auto.
     apply Rle_ge. 
     apply (f_equal u') in Heq.
     rewrite u'_inv_above // in Heq.
     rewrite Heq.
     etransitivity.
     *  apply Rmult_le_compat.
        ** apply Rmult_pos. 
           *** induction (Z.to_nat _) => //=; try fourier.
               apply Rmult_pos; auto.
               apply Rle_mult_inv_pos; auto. apply mpos; fourier.
           *** apply Rle_mult_inv_pos; auto; try fourier. 
        ** apply Rinv_pos; auto.
        ** apply Rmult_le_compat.
           *** induction (Z.to_nat _) => //=; try fourier.
               apply Rmult_pos; auto.
               apply Rle_mult_inv_pos; auto. apply mpos; fourier.
           *** apply Rle_mult_inv_pos; auto; try fourier.
           *** reflexivity.
           *** apply Rdiv_le_compat_contra; last first.
               **** apply Heq'.
               **** reflexivity.
               **** auto.
               **** fourier.
        ** reflexivity.
     * rewrite /Rdiv. rewrite (Z2Nat.inj_add) //= plus_comm //=. 
       rewrite (Rmult_comm (m z / z)).
       right. rewrite ?Rmult_assoc. field.
       split; auto. apply Rgt_not_eq. fourier.
  - intros z z' (?&?&Hltu'1) (?&?&Hltu'2) Hlez.
    apply Rle_ge. apply Rdiv_le_compat_contra.
    * rewrite uu'_adjoint // in Hltu'2 *; intros; fourier.
    * apply a_pos; auto.
    * apply u_mono in Hlez. fourier.
    * apply a_mono in Hlez. fourier.
  - intros z (?&?&?). 
    apply continuity_pt_div; auto.
    apply continuity_pt_minus; auto. by apply continuity_pt_const. 
    apply Rgt_not_eq. by apply a_pos. 
  - repeat split; nra.
  - split; nra.
Qed.

Lemma fp_plus_fp0 x y:
  frac_part y = 0 →
  frac_part (x + y) = frac_part x.
Proof.
  intros Hfp0. 
  case (Rge_dec (frac_part x + frac_part y) 1).
  - rewrite Hfp0 Rplus_0_r.  intros. 
    edestruct (base_fp x); fourier.
  - intros ?%Rnot_ge_lt; by rewrite plus_frac_part2 // Hfp0 Rplus_0_r.
Qed.

Lemma frac_part_1: 
  frac_part 1 = 0.
Proof.
  rewrite /frac_part. replace 1 with (IZR 1) by auto.
  rewrite Int_part_IZR //. ring.
Qed.

Lemma frac_part_n1: 
  frac_part (-1) = 0.
Proof.
  rewrite /frac_part. replace (-1) with (IZR (-1)) by auto.
  rewrite Int_part_IZR //. ring.
Qed.

Lemma frac_part_0: 
  frac_part 0 = 0.
Proof.
  rewrite /frac_part. replace 0 with (IZR 0) at 1 2 by auto.
  rewrite Int_part_IZR //. ring.
Qed.

Lemma Rceil_plus_1 x:
  (Rceil (x + 1) = Rceil x + 1)%Z.
Proof.
  rewrite /Rceil fp_plus_fp0 //; auto using frac_part_1.
  rewrite plus_Int_part2 //=; last first.
  { rewrite frac_part_1. destruct (base_fp x); fourier. }
  replace 1 with (IZR 1) by auto. rewrite Int_part_IZR //. 
  case: ifP; intros; omega.
Qed.

Lemma Rceil_minus_1 x:
  (Rceil (x - 1) = Rceil x - 1)%Z.
Proof.
  rewrite /Rceil fp_plus_fp0 //; auto using frac_part_n1.
  rewrite plus_Int_part2 //=; last first.
  { rewrite frac_part_n1. destruct (base_fp x); fourier. }
  replace (-(1)) with (IZR (-1)) by auto. rewrite Int_part_IZR //. 
  case: ifP; intros; omega.
Qed.

Lemma Rceil_mono_strict x x': frac_part x = 0 → x < x' → (Rceil x < Rceil x')%Z.
Proof.
  rewrite /Rceil. 
  rewrite {2}(Int_frac_decompose x).
  rewrite {1}(Int_frac_decompose x').
  move => -> //. rewrite eq_refl //=.
  case: ifP. 
  - move /eqP => ->. rewrite ?Rplus_0_r. apply lt_IZR.
  - intros. apply lt_IZR. rewrite plus_IZR.
    replace (IZR 1) with 1 by auto.
    destruct (base_fp x'). fourier.
Qed.

Lemma Rceil_positive_le1 x:
  (Rceil x > 0)%Z → x ≤ 1 → Rceil x = 1%Z.
Proof.
  rewrite /Rceil => Hgt. rewrite {1}(Int_frac_decompose x).
  move:Hgt.
  case: ifP. 
  - move /eqP => Hfp0 Hgt.
    rewrite Hfp0 Rplus_0_r.
    replace 1 with (IZR 1) by auto. move /le_IZR => ?; omega.
  - move /eqP => ?. intros. cut (Int_part x < 1)%Z; first by (intros; omega).
    apply lt_IZR. destruct (base_fp x) as (Hge0&Hlt1). replace (IZR 1) with 1 by auto. 
    move: Hgt. move /Zgt_lt/IZR_lt.
    rewrite plus_IZR. replace (IZR 1) with 1 by auto.
    replace (IZR 0) with 0 by auto. inversion Hge0; intros; [fourier|nra].
Qed.

Lemma Krec_le_D: ∀ i r x, Krec i r x ≤ D r (size x).
Proof.
  induction i => r x.
  - rewrite /K /D. 
    destruct (Rle_dec) as [|Hgtmin]; first by (edestruct Krec_bound01; eauto).
    rewrite //=.
    destruct (Rle_dec) as [Hge|Hnge].
    { 
      right. rewrite //= /K0 //=. destruct (Rlt_dec) => //=; try nra.
    }
    rewrite //=.
    destruct (Rle_dec) as [Hge|Hnge']. 
    { rewrite //=. edestruct (Krec_bound01 r x O); eauto. }
    rewrite //= /K0.
    destruct (Rlt_dec) => //=.
    { exfalso; eapply Hgtmin. nra. } 
    eapply D0_aux. apply Rnot_le_gt in Hnge. fourier.
  - rewrite /D. 
    destruct (Rle_dec) as [|Hgtmin]. 
    { rewrite /is_left. edestruct (Krec_bound01 r x (S i)); auto. }
    destruct (Rle_dec) as [Hge|Hnge].
    { right. revert r x Hgtmin Hge. induction (S i).
      * rewrite //= /K0 //=. intros. destruct Rlt_dec => //=; auto. 
        intros. exfalso. apply Hgtmin. nra.
      * intros. rewrite {1}/Krec -/Krec Ex_fin_pt /rvar_comp //=.
        rewrite alower; last fourier. rewrite Rminus_0_r.
        eapply big1 => b ?.  rewrite IHn //=; try nra. 
        transitivity (size x) => //.
    }
    destruct (Rle_dec) as [Hge|Hnge']; first by (edestruct (Krec_bound01 r x (S i)); auto).
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
    transitivity (Ex (rvar_comp (rvar_comp (h x) size) (λ x', D (r - a (size x)) x'))).
    * rewrite /Krec -/Krec ?Ex_fin_pt //=.
      apply Rle_bigr => z ?.
      apply Rmult_le_compat_r; eauto using Rge_le, pmf_pos.
    * etransitivity; first eapply lemma31 with (x := size x) (c := u' (r - a (size x))) (z := 1).
      ** nra.
      ** apply u'_pos.
      ** intros p. rewrite img_alt. intros (n&?). subst. split; rewrite //=; eauto. 
         eapply hrange2. nra. 
      ** rewrite /D.
         destruct (Rle_dec) => //=; first by nra.
         destruct (Rle_dec) => //=.
      ** intros. eapply D0.
      ** fourier.
      ** intros y Hley.
         rewrite /D.
         repeat (destruct (Rle_dec) => //=; try nra); [].
         apply Rge_le, u_mono in Hley. rewrite u_inv_above // in Hley.
      ** intros. eapply Dnondec; eauto.
      ** rewrite /Rdiv Rmult_assoc. etransitivity. apply Rmult_le_compat_r; last apply m_bound_Eh.
         { intros. 
           apply Rle_mult_inv_pos; auto. 
           **** apply D0.
           **** apply Rmin_case; nra.
         }
         assert (round r (size x) = 1 + round (r - a (size x)) (size x))%Z as Hplus.
         {  rewrite /round. 
            rewrite Zplus_comm -Rceil_plus_1; f_equal.
            field. apply Rgt_not_eq. apply a_pos. nra.
         }
         assert (Hrgt0: (round r (size x) > 0)%Z).
         { 
           rewrite /round.
           rewrite -Rceil_0. apply Zlt_gt, Rceil_mono_strict. apply frac_part_0.
           apply Rdiv_lt_0_compat.
           - nra. 
           - apply a_pos. nra.
         }
         assert (0 <= round (r - a (size x)) (size x))%Z by omega.
         apply Rmin_case_strong.
         *** rewrite Hplus.
             intros Hminl. rewrite D_Dalt_equiv. rewrite /Dalt //.
             destruct (Rle_dec); rewrite /is_left; first by (nra).
             destruct (Rle_dec); rewrite /is_left; first by (nra).
             destruct (Rlt_dec) as [Hlt'|?]; rewrite /is_left.
             { exfalso.  apply uu'_adjointrl in Hminl; nra. }
             right. 
             rewrite Z2Nat.inj_add; try omega.
            rewrite plus_IZR. replace (IZR 1) with 1 by auto.
            rewrite //=.
            rewrite Rmult_plus_distr_l Rmult_1_r.
            rewrite /Rminus. rewrite Ropp_plus_distr.
            rewrite Rplus_assoc.
            rewrite /Rdiv; field.
            split.
            **** apply Rgt_not_eq, u'_pos.
            **** apply Rgt_not_eq. nra. 
        *** intros Hminr. rewrite D_Dalt_equiv /Dalt.
            destruct (Rle_dec); rewrite /is_left; first by nra.
            destruct (Rle_dec); rewrite /is_left; first by nra.
            destruct (Rlt_dec) as [Hlt'|?]; rewrite /is_left.
            { rewrite u_inv_above in Hlt'; nra. }
            right. 
            symmetry.
            assert (round (r - a (size x)) (u' (r - a (size x))) = 0)%Z as ->.
            { 
              rewrite /round -Rceil_0. f_equal.
              rewrite u_inv_above /Rdiv; last done.
              apply Rmult_eq_0_compat_r; ring.
            }
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
                  ** apply Rgt_not_eq, a_pos; nra.
            }
            replace (IZR 1) with 1 by auto. rewrite //= ?Rmult_1_r.
            field; split; nra.
Qed.
  
Theorem karp_bound r x: P x → K r x ≤ D r (size x). 
Proof.
  transitivity (Krec_sup r x).
  - apply K_le_supKrec; auto.
  - apply (proj2 (Krec_sup_is_lub r x)).
    intros ? (i&<-); apply Krec_le_D.
Qed.

(* N.B. the parameter P here can be used to restrict attention to recurrences
   that preserve some invariant throughout execution. *)
Theorem karp_bound_simple w x: 
  size x > d →
  P x → pr_gt (T x) (u (size x) + INR w * a (size x)) ≤ (m (size x) / size x) ^ w.
Proof.
  set (r := u (size x) + INR w * a (size x)).
  transitivity (D r (size x)).
  - apply karp_bound; auto.
  -  rewrite /D/r. destruct (Rle_dec) as [Hle|?].
     { rewrite //=. destruct w; first by (rewrite //=; reflexivity).
         assert (umin <= u (size x)) by (apply umin_lb_simple; nra).
         assert (a (size x) > 0) by (apply a_pos; nra).
         specialize (pos_INR w).
         intros. rewrite S_INR in Hle. exfalso. nra.
     }
     rewrite //=. 
     destruct Rle_dec => //=; try nra; [].
     destruct Rle_dec as [Hle|?].
     { intros. rewrite //=. destruct w; first by (rewrite //=; reflexivity).
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
     rewrite /Rdiv. rewrite Rinv_r; last by nra. rewrite Rmult_1_r.
      rewrite Nat2Z.id. reflexivity.
Qed.

End karp_bound_sec.
