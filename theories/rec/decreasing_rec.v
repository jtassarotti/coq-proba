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

Module decreasing_rec.
Section decreasing_rec.
Variable X: eqType.
Variable B : X → finType.
Variable size: X → R.
Variable msr: X → R.
Variable Ωh: ∀ x, distrib (B x).
Variable h: ∀ x: X, rvar (Ωh x) X.
Variable d: R.
Variable msr_cutoff: R.
Hypothesis cutoff_non_neg: 0 ≤ msr_cutoff.
Hypothesis hmsr_shrink: 
  ∀ z i, d < size z → msr (h z i) ≤ msr z - 1.
Hypothesis hmsr_below: ∀ x n, msr x ≤ msr_cutoff → size ((h x) n) <= d.
Hypothesis hrange1: ∀ x n, size ((h x) n) ≤ size x.
Hypothesis hrange2: ∀ x n, d < size x →  0 ≤ size ((h x) n).

Lemma recN_h_decreasing n z x:
  (rvar_comp (recN_rvar h z n) size) x ≤ size z.
Proof.
  revert z x; induction n as [| n IH]; rewrite //=.
  - reflexivity.
  - intros. destruct x as (x&s). 
    specialize (IH ((h z) x) s). rewrite //= in IH.
    specialize (hrange2 z x). etransitivity; eauto.
Qed.

Lemma hinf_0_aux1:
  ∀ r z, size z ≤ r → pr_gt (rvar_comp (h z) size) r = 0.
Proof.
  intros r z Hbelow.
  rewrite /pr_gt /pr SeriesC_fin_big.
  apply big1 => i ?.
  destruct (Rgt_dec) as [Hgt|?] => //=.
  apply Rgt_not_le in Hgt.
  exfalso; apply Hgt. specialize (hrange1 z i). etransitivity; eauto.
Qed.

Lemma hinf_0_aux2:
  ∀ r z n, size z ≤ r → pr_gt (rvar_comp (recN_rvar h z n) size) r = 0.
Proof.
  intros r z n Hbelow.
  rewrite /pr_gt /pr SeriesC_fin_big.
  apply big1 => i ?. 
  destruct (Rgt_dec) as [Hgt|?] => //=.
  apply Rgt_not_le in Hgt.
  exfalso; apply Hgt. 
  etransitivity; first apply recN_h_decreasing; eauto.
Qed.

Lemma hinf_decreasingS:
  ∀ z r n, pr_gt (rvar_comp (recN_rvar h z (S n)) size) r
               ≤ pr_gt (rvar_comp (recN_rvar h z n) size) r.
Proof.
  intros z r n.
  rewrite recN_pr_gt'.
  rewrite /pr_gt.
  rewrite pr_gt_alt_comp.
  rewrite /index_enum.
  rewrite [@Finite.enum]unlock //=.
  rewrite (img_fin_big' _ (λ i, (pr_eq _ i * pr (rvar_dist (rvar_comp (h i) size))
                                                (λ a, Rgt_dec ((rvar_comp (h i) size) a) r)))
                          (λ i, true)).
  rewrite (img_fin_big' _ (λ i, if ((Rgt_dec (size i) r)) then 
                                  pr_eq _ i 
                                else 
                                  0) (λ i, true)).
  eapply Rle_bigr => i _.
  destruct (Rgt_dec) as [?|Hngt] => //=.
 -  rewrite -[a in _ ≤ a]Rmult_1_r.
    apply Rmult_le_compat_l.
    * apply Rge_le, ge_pr_0.
    * apply pr_le_1.
  - apply Rnot_gt_le in Hngt. specialize (hinf_0_aux1 _ _ Hngt).
    rewrite /pr_gt //= => ->; fourier.
Qed.

Lemma hinf_decreasing:
  ∀ z r n n', (le n n') → 
              pr_gt (rvar_comp (recN_rvar h z n') size) r
                    ≤ pr_gt (rvar_comp (recN_rvar h z n) size) r.
Proof.
  induction 1 as [| ? ? IHle].
  - reflexivity.
  - etransitivity; first apply hinf_decreasingS. done.
Qed.

Lemma hinf_decreasing0:
  ∀ z r n n', (le n n') → 
              pr_gt (rvar_comp (recN_rvar h z n) size) r = 0 →
              pr_gt (rvar_comp (recN_rvar h z n') size) r = 0.
Proof.
  intros ???? Hle Hgt. apply (Rle_antisym).
  - etransitivity; last (right; apply Hgt).
    apply hinf_decreasing; auto.
  - rewrite /pr_gt. apply Rge_le, ge_pr_0.
Qed.

Lemma hinf_0_aux3:
  ∀ z, pr_gt (rvar_comp (recN_rvar h z (S (Z.to_nat (Rceil (msr z))))) size) d = 0.
Proof.
  intros z.
  remember (Z.to_nat (Rceil (msr z))) as k eqn:Hk.
  revert z Hk.
  induction k as [k IH] using lt_wf_ind. intros z (* Hlt *) Hk.
  destruct k.
  * rewrite /pr_gt.
    assert (msr z ≤ msr_cutoff) as Hbelow.
    { 
      case (Rle_dec (msr z) msr_cutoff) as [Hle|Hnle]; auto.
      cut (msr z ≤ 0); first (intros; fourier).
      apply Rnot_le_gt in Hnle.
      assert (0 <= (Rceil (msr z)))%Z.
      { rewrite -Rceil_0. apply Rceil_mono. fourier. }
      assert ( Rceil 0 = (Rceil (msr z)))%Z as Hz.
      { 
        rewrite Rceil_0. replace 0%nat with (Z.to_nat 0) in Hk by auto.
        apply Z2Nat.inj; omega.
      }
      apply Rnot_lt_le => Hlt'. apply Rceil_mono_strict in Hlt';
          last apply frac_part_0.
      omega.
    } 
    rewrite //=.
    rewrite /pr_gt /pr //= ?SeriesC_fin_big.
    apply big1.  intros (i&?) Hin.
    destruct (Rgt_dec) as [Hgt|Hngt] => //.
    exfalso. apply Rgt_not_le in Hgt. apply Hgt.
    apply hmsr_below. eauto.
  * case (Rlt_dec d (size z)) as [Hlt|Hnlt]; last (by apply hinf_0_aux2, Rnot_lt_le).
    rewrite recN_pr_gt.
    rewrite big_seq_cond.
    apply big1. intros i. move/andP=>[Hin _]. 
    destruct i as (i&Hin').
    clear Hin. generalize Hin'. apply img_alt in Hin' as (x&Hin) => Hin'.
    generalize (hmsr_shrink z x) => Hle_size; rewrite Hin in Hle_size.
    apply Rmult_eq_0_compat_l.
    rewrite /sval.
    destruct (Rle_dec 0 (msr i)) as [Hlei|Hlt0%Rnot_le_gt]; last first.
    { 
      assert (msr i ≤ msr_cutoff) as Hbelow by nra.
      assert (1 <= (S k))%coq_nat as Hto1 by omega.
      apply (hinf_decreasing0 _ _ _ _ Hto1).
      rewrite //=.
      rewrite /pr_gt /pr //= ?SeriesC_fin_big.
      apply big1.  intros (i'&?) _.
      destruct (Rgt_dec) as [Hgt|Hngt] => //.
      exfalso. apply Rgt_not_le in Hgt. apply Hgt.
      apply hmsr_below. eauto.
    }
    assert (le (Z.to_nat (Rceil (msr i))) k) as Hlek.
    { 
    apply Rceil_mono in Hle_size.
    rewrite Rceil_minus_1 in Hle_size.
    apply Z2Nat.inj_le in Hle_size.
    - rewrite Z2Nat.inj_sub in Hle_size; last omega.
      replace (Z.to_nat 1) with 1%nat in Hle_size by auto with *.
      omega.
    - rewrite -Rceil_0. apply Rceil_mono. done.
    - transitivity (Rceil (msr i)); auto.
      rewrite -Rceil_0. apply Rceil_mono. done.
    - done.
    }
    assert (le (S (Z.to_nat (Rceil (msr i)))) (S k)) as HleSk.
    { omega. }
    apply (hinf_decreasing0 _ _ _ _ HleSk).
    apply IH; auto; try omega.
Qed.

Lemma hinf_0: 
  ∀ z eps, eps > 0 → ∃ n, pr_gt (rvar_comp (recN_rvar h z n) size) d < eps.
Proof.
  intros z eps Hgt0.
  exists (S (Z.to_nat (Rceil (msr z)))).
  apply (Rle_lt_trans _ 0); last fourier.
  right; apply hinf_0_aux3.
Qed.
End decreasing_rec.
End decreasing_rec.

Module decreasing_rec_binary.
Section decreasing_rec_binary.
Variable X: eqType.
Variable B : X → finType.
Variable size: X → R.
Variable Ωh: ∀ x, distrib (B x).
Variable h: ∀ x: X, rvar (Ωh x) [eqType of X * X].
Variable d: R.
Hypothesis d_non_neg: 0 ≤ d.
Hypothesis hrange_shrink: 
  ∀ x n, d < size x → size (fst ((h x) n)) + size (snd ((h x) n)) ≤ size x - 1.
Hypothesis hrange11: ∀ x n, size (fst ((h x) n)) ≤ size x.
Hypothesis hrange21: ∀ x n, size (snd ((h x) n)) ≤ size x.
Hypothesis hrange12: ∀ x n, d < size x →  0 ≤ size (fst ((h x) n)).
Hypothesis hrange22: ∀ x n, d < size x →  0 ≤ size (snd ((h x) n)).

Lemma recN_h_decreasing n z φ k x:
  (rvar_comp (recN_rvar (hpath _ _ _ h φ) (k, z) n) (λ x, size (snd x))) x ≤ size z.
Proof.
  revert z k x; induction n as [| n IH]; rewrite //=.
  - reflexivity.
  - intros. destruct x as (x&s). 
    destruct (φ k).
    * move: x s. rewrite /Bn//= => x s. 
      specialize (IH (fst ((h z) x)) (S k)).
      rewrite //= in IH. specialize (hrange12 z x). etransitivity; eauto.
    * move: x s. rewrite /Bn//= => x s. 
      specialize (IH (snd ((h z) x)) (S k)).
      rewrite //= in IH. specialize (hrange22 z x). etransitivity; eauto.
Qed.

Lemma hinf_0_aux11:
  ∀ r z, size z ≤ r → pr_gt (rvar_comp (h z) (λ x, size (fst x))) r = 0.
Proof.
  intros r z Hbelow.
  rewrite /pr_gt /pr SeriesC_fin_big.
  apply big1 => i _.
  destruct (Rgt_dec) as [Hgt|?] => //=; [].
  rewrite //= in Hgt. generalize (hrange11 z i) => //=; nra.
Qed.

Lemma hinf_0_aux21:
  ∀ r z, size z ≤ r → pr_gt (rvar_comp (h z) (λ x, size (snd x))) r = 0.
Proof.
  intros r z Hbelow.
  rewrite /pr_gt /pr SeriesC_fin_big. 
  apply big1 => i _.
  destruct (Rgt_dec) as [Hgt|?] => //=; [].
  rewrite //= in Hgt. generalize (hrange21 z i) => //=; nra.
Qed.

Lemma hinf_0_aux_below:
  ∀ r z n φ k, 
    size z ≤ r → pr_gt (rvar_comp (recN_rvar (hpath _ _ _ h φ) (k, z) n) (λ x, size (snd x))) r = 0.
Proof.
  intros r z n φ k Hbelow.
  rewrite /pr_gt /pr SeriesC_fin_big.
  apply big1 => i _. 
  destruct (Rgt_dec) as [Hgt|?] => //=; [].
  apply Rgt_not_le in Hgt. exfalso; apply Hgt.
  etransitivity; first apply recN_h_decreasing; eauto.
Qed.

Lemma hinf_decreasingS:
  ∀ z r n φ k, pr_gt (rvar_comp (recN_rvar (hpath _ _ _ h φ) (k, z) (S n)) (λ x, size (snd x))) r
               ≤ pr_gt (rvar_comp (recN_rvar (hpath _ _ _ h φ) (k, z) n) (λ x, size (snd x))) r.
Proof.
  intros z r n φ k.
  rewrite recN_pr_gt'.
  rewrite /pr_gt.
  rewrite pr_gt_alt_comp.
  eapply Rle_bigr => i Hin. 
  destruct (Rgt_dec) as [?|Hle] => //=.
  - rewrite -[a in _ ≤ a]Rmult_1_r.
    apply Rmult_le_compat_l.
    * apply Rge_le, ge_pr_0.
    * apply pr_le_1.
  - rewrite //=. destruct i as ((k'&?)&?). rewrite /hpath//=.
    rewrite //= in Hle. apply Rnot_gt_le in Hle.
    destruct (φ k').
    * specialize (hinf_0_aux11 _ _ Hle).
      rewrite /pr_gt //= => ->; fourier.
    * specialize (hinf_0_aux21 _ _ Hle).
      rewrite /pr_gt //= => ->; fourier.
Qed.

Lemma hinf_decreasing:
  ∀ z r n n' φ k,  
    (le n n') → 
    pr_gt (rvar_comp (recN_rvar (hpath _ _ _ h φ) (k, z) n') (λ x, size (snd x))) r
          ≤ pr_gt (rvar_comp (recN_rvar (hpath _ _ _ h φ) (k, z) n) (λ x, size (snd x))) r.
Proof.
  induction 1 as [| ? ? IHle].
  - reflexivity.
  - etransitivity; first apply hinf_decreasingS. done.
Qed.

Lemma hinf_decreasing0:
  ∀ z r n n' φ k, (le n n') → 
    pr_gt (rvar_comp (recN_rvar (hpath _ _ _ h φ) (k, z) n) (λ x, size (snd x))) r = 0 →
    pr_gt (rvar_comp (recN_rvar (hpath _ _ _ h φ) (k, z) n') (λ x, size (snd x))) r = 0.
Proof.
  intros ?????? Hle Hgt. apply (Rle_antisym).
  - etransitivity; last (right; apply Hgt).
    apply hinf_decreasing; auto.
  - rewrite /pr_gt. apply Rge_le, ge_pr_0. 
Qed.

Lemma hinf_0_aux3:
  ∀ z φ sidx, 
    pr_gt (rvar_comp (recN_rvar (hpath _ _ _ h φ) (sidx, z) (Z.to_nat (Rceil (size z)))) 
                   (λ x, size (snd x))) d = 0.
Proof.
  intros z φ sidx.
  remember (Z.to_nat (Rceil (size z))) as k eqn:Hk.
  revert z Hk sidx.
  induction k as [k IH] using lt_wf_ind. intros z (* Hlt *) Hk sidx.
  destruct k.
  * rewrite /pr_gt.
    assert (size z ≤ d) as Hbelow.
    { 
      case (Rle_dec (size z) d) as [Hle|Hnle]; auto.
      cut (size z ≤ 0); first (intros; fourier).
      apply Rnot_le_gt in Hnle.
      assert (0 <= (Rceil (size z)))%Z.
      { rewrite -Rceil_0. apply Rceil_mono. fourier. }
      assert ( Rceil 0 = (Rceil (size z)))%Z as Hz.
      { 
        rewrite Rceil_0. replace 0%nat with (Z.to_nat 0) in Hk by auto.
        apply Z2Nat.inj; omega.
      }
      apply Rnot_lt_le => Hlt'. apply Rceil_mono_strict in Hlt';
          last apply frac_part_0.
      omega.
    } 
    rewrite //=.
    rewrite /pr_gt /pr //= SeriesC_fin_big.
    rewrite /index_enum {1}[@Finite.enum]unlock //=.
    rewrite big_seq1 => //=.
    destruct (Rgt_dec) => //=. nra.
  * case (Rlt_dec d (size z)) as [Hlt|Hnlt]; last (by apply hinf_0_aux_below, Rnot_lt_le).
    rewrite recN_pr_gt.
    rewrite big_seq_cond.
    apply big1. intros ((sidx', i)&Hin'). move/andP=>[Hin _]. 
    clear Hin. generalize Hin'. apply img_alt in Hin' as (x&Hin) => Hin'.
    generalize (hrange_shrink z x) => Hle_size. (* rewrite Hin in Hle_size. *)
    apply Rmult_eq_0_compat_l.
    destruct (Rle_dec 0 (size i)) as [Hlei|?%Rnot_le_gt]; last first.
    { apply hinf_0_aux_below. fourier. }
    assert (le (Z.to_nat (Rceil (size i))) k) as Hlek.
    { 
      specialize (Hle_size Hlt).
      assert (Hle_size1: size (fst ((h z) x)) ≤ size z - 1).
      { generalize (hrange22 _ x Hlt). rewrite //= => ?.
        rewrite //= in Hle_size. fourier. }
      assert (Hle_size2: size (snd ((h z) x)) ≤ size z - 1).
      { generalize (hrange12 _ x Hlt). rewrite //= => ?.
        rewrite //= in Hle_size. fourier. }
    apply Rceil_mono in Hle_size1.
    apply Rceil_mono in Hle_size2.
    rewrite //= in Hin. destruct (φ sidx).
    - inversion Hin. subst. rewrite Rceil_minus_1 in Hle_size1.
      apply Z2Nat.inj_le in Hle_size1.
      * rewrite Z2Nat.inj_sub in Hle_size1; last omega.
        replace (Z.to_nat 1) with 1%nat in Hle_size1 by auto with *.
        rewrite -Hk //= in Hle_size1. omega. 
      * rewrite -Rceil_0. apply Rceil_mono. done.
      * transitivity (Rceil (size (fst ((h z) x)))); auto.
        rewrite -Rceil_0. apply Rceil_mono. done.
    - inversion Hin. subst. rewrite Rceil_minus_1 in Hle_size2.
      apply Z2Nat.inj_le in Hle_size2.
      * rewrite Z2Nat.inj_sub in Hle_size2; last omega.
        replace (Z.to_nat 1) with 1%nat in Hle_size1 by auto with *.
        rewrite -Hk //= in Hle_size2. omega. 
      * rewrite -Rceil_0. apply Rceil_mono. done.
      * transitivity (Rceil (size (snd ((h z) x)))); auto.
        rewrite -Rceil_0. apply Rceil_mono. done.
    }
    apply (hinf_decreasing0 _ _ _ _ _ _ Hlek).
    apply IH; auto; try omega.
Qed.

Lemma hinf_0: ∀ a, ∃ n, ∀ φ, pr_gt (rvar_comp (recN_rvar (hpath _ _ _ h φ) (O, a) n)
                                                  (λ x, size (snd x))) d = 0.
Proof.
  intros z.
  exists (Z.to_nat (Rceil (size z))) => φ.
  apply hinf_0_aux3.
Qed.
End decreasing_rec_binary.
End decreasing_rec_binary.