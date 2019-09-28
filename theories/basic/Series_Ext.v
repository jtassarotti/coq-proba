(* Some facts about series that are not in Coquelicot *)
From discprob.basic Require Import base order bigop_ext.
Require Import Reals Fourier Psatz.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.

Lemma Rbar_le_fin x y: 0 <= y → Rbar_le x (Finite y) → Rle (real x) y.
Proof.
  rewrite /Rbar_le. destruct x => //=.
Qed.

Lemma Rbar_le_fin' x y: 0 <= y → Rbar_le x y → Rle x (real y).
Proof.
  rewrite /Rbar_le. destruct x => //=.
Qed.

Lemma Rbar_eq_fin x y: x = (Finite y) → (real x) = y.
Proof.
  destruct x => //=. inversion 1; auto. 
Qed.

Lemma is_series_0 a: (∀ n, a n = 0) → is_series a 0.
Proof.
  intros Ha. apply (is_series_ext (λ x, 0)); auto.
  rewrite /is_series.
  apply (filterlim_ext (λ x, 0)).
  - intros m. rewrite sum_n_const Rmult_0_r //.
  - apply filterlim_const.
Qed.

Lemma Series_0 a: (∀ n, a n = 0) → Series a = 0.
Proof.
  intros Heq. apply is_series_unique, is_series_0. done. 
Qed.

Lemma is_lim_seq_pos a (v: R):
  (∀ n, a n >= 0) →
  is_lim_seq a v →
  0 <= v.
Proof.
  rewrite /is_lim_seq => Hn; intros.
  cut (Rbar_le 0 v); first by auto.
  apply (@filterlim_le _ eventually _ (λ x, 0) a); auto.
  - exists O; intros. apply Rge_le; auto.
  - apply filterlim_const.
Qed.

Lemma Lim_seq_pos a:
  (∀ n, a n >= 0) →
  0 <= Lim_seq a.
Proof.
  intros.
  cut (Rbar_le 0 (Lim_seq a)).
  { rewrite //=. rewrite /real. destruct Lim_seq; nra. }
  rewrite -Lim_seq_const. apply Lim_seq_le_loc.
  exists O. intros. apply Rge_le; auto. 
Qed.

Lemma Series_pos a:
  (∀ n, a n >= 0) →
  0 <= Series a.
Proof.
  intros Hpos.
  rewrite /Series. apply Lim_seq_pos. induction n.
  - rewrite sum_O.  auto.
  - rewrite sum_Sn /plus//=. specialize (Hpos (S n)). nra.
Qed.

Lemma Series_strict_pos_inv a:
  (∀ n, a n >= 0) →
  0 < Series a →
  ∃ n, a n > 0.
Proof.
  intros Hge Hlt.
  destruct (LPO (λ n, a n > 0)) as [Hs|Heq0].
  - intros n. destruct (Rgt_dec (a n) 0) => //=; auto.
  - destruct Hs as (n&Hgt0); exists n; done.
  - exfalso. assert (Series a = 0).
    { apply Series_0. intros n. destruct (Hge n) => //=.
      exfalso; eapply Heq0; eauto.
    }
    nra.
Qed.

Lemma is_lim_seq_unique_series a v:
  is_series a v → Lim_seq (sum_n a) = v.
Proof.
  intros. apply is_lim_seq_unique. rewrite //=. 
Qed.

Lemma is_series_partial_pos a n v:
  (∀ n, a n >= 0) →
  is_series a v →
  sum_n a n <= v.
Proof.
  intros Hpos His_series. 
  assert (Hpos' : ∀ n : nat, sum_n a n >= 0).
  { intros n'. induction n' => //=; rewrite ?sum_O ?sum_Sn; eauto. 
    specialize (Hpos (S n')). rewrite /plus//=. nra. }
  replace (sum_n a n) with (real (sum_n a n)) by auto.
  rewrite -(is_series_unique _ _ His_series).
  eapply Rbar_le_fin'.
  - case_eq (Lim_seq (sum_n a)) => //=; try nra.
    intros r Heq. 
    rewrite /is_series in His_series.
    assert (ex_lim_seq (sum_n a)).
    { exists v. eauto. }
    eapply is_lim_seq_pos; eauto. 
    rewrite -Heq. apply Lim_seq_correct; eauto.
  -  rewrite -Lim_seq_const.
     case_eq (Lim_seq (sum_n a)) => //=; try nra.
     * intros r Heq. rewrite -Heq.
       apply Lim_seq_le_loc. exists n.
       intros m; induction 1.
       ** reflexivity.
       ** rewrite sum_Sn /plus//=. specialize (Hpos (S m)). nra.
     * intros Heq_infty. apply is_lim_seq_unique_series in His_series. exfalso.
       rewrite Heq_infty in His_series. congruence.
     * intros Heq_infty. apply is_lim_seq_unique_series in His_series. exfalso.
       rewrite Heq_infty in His_series. congruence.
Qed.

Lemma sum_n_partial_pos a :
  (∀ n, a n >= 0) →
   ∀ n : nat, sum_n a n >= 0.
Proof.
  intros Hpos n'; induction n' => //=; rewrite ?sum_O ?sum_Sn; eauto. 
    specialize (Hpos (S n')). rewrite /plus//=. nra. 
Qed.

Lemma sum_n_pos a (n: nat):
  (∀ n, a n >= 0) →
  0 <= sum_n a n.
Proof.
  intros Hge. induction n => //=.
  - rewrite sum_O. by apply Rge_le.
  - rewrite sum_Sn /plus//=. specialize (Hge (S n)). nra.
Qed.

Lemma sum_n_strict_pos a (n: nat):
  (∀ n, a n >= 0) →
  a n > 0 →
  0 < sum_n a n.
Proof.
  intros Hge Hgt.
  destruct n => //=.
  - rewrite sum_O. nra.
  - rewrite sum_Sn /plus//=. specialize (sum_n_pos a n Hge).
    nra.
Qed.

Lemma Series_partial_pos a (n: nat):
  (∀ n, a n >= 0) →
  ex_finite_lim_seq (sum_n a) →
  sum_n a n <= Series a.
Proof.
  intros Hpos Hfin.
  specialize (sum_n_partial_pos a Hpos) => Hpos'.
  replace (sum_n a n) with (real (sum_n a n)) by auto.
  eapply Rbar_le_fin'.
  - case_eq (Lim_seq (sum_n a)) => //=; try nra.
    intros r Heq'.
    etransitivity; first apply Lim_seq_pos; eauto.
    move: Heq'. destruct Lim_seq => //=. inversion 1. nra.
  - destruct Hfin as (?&Hfin).
    rewrite -Lim_seq_const.
     case_eq (Lim_seq (sum_n a)) => //=; try nra.
     * intros r Heq'. rewrite -Heq'.
       apply Lim_seq_le_loc. exists n.
       intros m; induction 1.
       ** reflexivity.
       ** rewrite sum_Sn /plus//=. specialize (Hpos (S m)). nra.
     * apply is_lim_seq_unique in Hfin. congruence.
     * apply is_lim_seq_unique in Hfin. congruence.
Qed.

Lemma Series_strict_pos a (n: nat):
  (∀ n, a n >= 0) →
  a n > 0 →
  ex_finite_lim_seq (sum_n a) →
  0 < Series a.
Proof.
  intros. eapply Rlt_le_trans; last eapply Series_partial_pos; eauto.
  eapply sum_n_strict_pos; eauto.
Qed.

Lemma is_series_filter_pos a (P: pred nat) (v: R):
  (∀ n, a n >= 0) →
  is_series a v → ex_series (λ n, if P n then a n else 0).
Proof.
  intros Hge Hconv. apply ex_series_Rabs.
  apply: ex_series_le; last by (exists v; eauto).
  intros n. rewrite /norm//=/abs//=. 
  destruct (P n); rewrite Rabs_Rabsolu Rabs_right => //=; try nra.
  specialize (Hge n); nra.
Qed.

Lemma is_series_filter_PQ a (P Q: pred nat) (v: R):
  (∀ n, a n >= 0) →
  is_series (λ n, if P n then a n else 0) v →
  (∀ n, Q n → P n) →
  ex_series (λ n, if Q n then a n else 0).
Proof.
  intros Hge Hconv Himp. apply ex_series_Rabs.
  apply: ex_series_le; last by (exists v; eauto).
  intros n. rewrite /norm//=/abs//=. 
  specialize (Himp n); specialize (Hge n).
  destruct (P n), (Q n); rewrite Rabs_Rabsolu Rabs_right => //=; try nra.
  exfalso; auto.
Qed.

Lemma is_series_filter_split a (P: pred nat) (v: R):
  (∀ n, a n >= 0) →
  is_series a v → 
  Series (λ n, if P n then a n else 0) + Series (λ n, if ~~ P n then a n else 0) = v.
Proof.
  intros.
  rewrite -Series_plus; try (eapply is_series_filter_pos; eauto).
  rewrite -(is_series_unique a v) //.
  apply Series_ext => n; destruct (P n) => //=; nra.
Qed.

Lemma is_series_filter_union a (P Q: pred nat) (v: R):
  (∀ n, a n >= 0) →
  is_series (λ n, if P n || Q n then a n else 0) v → 
  Series (λ n, if P n then a n else 0) + Series (λ n, if Q n then a n else 0)
    - Series (λ n, if P n && Q n then a n else 0) = v.
Proof.
  intros Hge Hexists.
  rewrite -Series_plus; try (eapply (is_series_filter_PQ _ _ _ _ Hge Hexists); eauto; 
                             try (intros n; destruct (P n), (Q n); auto)).
  rewrite -Series_minus; try (eapply (is_series_filter_PQ _ _ _ _ Hge Hexists); eauto;
                             try (intros n; destruct (P n), (Q n); auto)).
  - rewrite -(is_series_unique _ v Hexists). 
    apply Series_ext => n; destruct (P n) => //=; nra.
  - apply: (ex_series_le _ (λ n, scal 2 (if P n || Q n then a n else 0))). 
    + intros n. specialize (Hge n). destruct (P n), (Q n) => //=; 
      rewrite /norm//=/abs//=/scal//=/mult/=; rewrite Rabs_right; nra.
    + exists (scal 2 v). by apply: is_series_scal.
Qed.

Lemma is_series_bump_hd v:
  is_series (λ x, if eq_nat_dec x 0 then v else 0) v.
Proof.
  apply is_series_decr_1.
  rewrite //=. rewrite plus_opp_r. 
  by apply is_series_0.
Qed.

Lemma is_series_bump n v:
  is_series (λ x, if eq_nat_dec x n then v else 0) v.
Proof.
  induction n.
  - apply is_series_bump_hd.
  - apply is_series_decr_1. 
    destruct eq_nat_dec; first by done.
    rewrite opp_zero plus_zero_r.
    eapply is_series_ext; eauto.
    intros n' => //=.
    destruct eq_nat_dec => //=. 
Qed.

Lemma Series_bump n v:
  Series (λ x, if eq_nat_dec x n then v else 0) = v.
Proof.
  apply is_series_unique, is_series_bump.
Qed.

Lemma Series_le':
  ∀ a b : nat → R, (∀ n : nat, a n <= b n) → ex_series a → ex_series b → Series a <= Series b.
Proof.
  intros a b Hle Hexa Hexb.
  destruct Hexa as [av Hav].
  destruct Hexb as [bv Hbv].
  cut (av <= bv).
  { intros Hle'.
    erewrite is_series_unique; eauto.
    erewrite is_series_unique; eauto.
  }
  cut (Rbar_le av bv); auto.
  eapply @filterlim_le; eauto.
  - apply Proper_StrongProper, eventually_filter.
  - exists O => n Hn.
    rewrite ?sum_n_bigop. apply Rle_bigr. done.
Qed.

Lemma is_lub_seq_eps_below a x:
  is_lub (λ r : R, ∃ n : nat, a n = r) x →
  ∀ eps : posreal , ∃ n, x - eps < a n <= x.
Proof.
  intros Hlub eps. apply Classical_Pred_Type.not_all_not_ex => Hn.
  destruct Hlub as [Hub Hlub].
  eapply Rgt_not_le; last eapply (Hlub (x - eps)).
  { destruct eps as (?&?); auto => //=. nra. }
  intros ? (n&<-).
  apply Rnot_gt_le => Hgt.
  specialize (Hn n).
  apply Hn; split; first nra.
  apply Hub; eauto.
Qed.

Lemma is_lub_seq_eps_ball a x:
  is_lub (λ r : R, ∃ n : nat, a n = r) x →
  ∀ eps : posreal , ∃ n, ball x eps (a n).
Proof.
  intros Hlub eps. edestruct (is_lub_seq_eps_below a x Hlub eps) as (n&?).
  destruct Hlub as [Hub Hlub].
  exists n. rewrite /ball//=/AbsRing_ball/abs/minus/plus/opp//=.
  rewrite Rabs_left1; last first.
  { cut (a n <= x); first by intros; nra. apply Hub. eauto. }
  nra.
Qed.

Lemma sum_n_nonneg_terms_increasing a n n':
  n ≤ n' → (∀ n, a n >= 0) → sum_n a n <= sum_n a n'.
Proof.
  induction 1; first reflexivity.
  intros Hpos. etransitivity; first eapply IHle; auto.
  rewrite sum_Sn /plus//=. specialize (Hpos (S m)). nra.
Qed.

Lemma Lim_seq_le_loc_const u v:
  0 <= v → 
  eventually (λ n : nat, u n <= v) → Lim_seq u <= v.
Proof.
  intros.
  cut (Rbar_le (Lim_seq u) v).
  { destruct (Lim_seq u) => //=. }
  rewrite -Lim_seq_const.
  by apply Lim_seq_le_loc.
Qed.

Lemma ex_series_non_neg_le_const a v:
  (∀ n : nat, 0 <= a n) → (∀ n, sum_n a n <= v) → ex_series a ∧ Series a <= v.
Proof.
  intros Hnonneg Hbounded.
  rewrite /ex_series/is_series/Series.
  edestruct (completeness (λ r, ∃ n, sum_n a n = r)) as (x&Hlub).
  { exists v => r [n <-]. done. }
  { exists (sum_n a O); exists O; done. }
  split.
  - exists x. intros P. rewrite /locally//=. intros (eps&Heps).
    edestruct (is_lub_seq_eps_below _ _ Hlub eps) as (n&Hrange).
    exists n => n'. intros Hle.
    apply Heps. rewrite /ball//=/AbsRing_ball/abs/minus/plus/opp//=.
    rewrite Rabs_left1; last first.
    { destruct Hrange.
      apply (Rplus_le_reg_r x). ring_simplify.
      apply Hlub. eauto.
    }
    destruct Hrange.
    assert (sum_n a n <= sum_n a n').
    { apply sum_n_nonneg_terms_increasing; eauto. intros. apply Rle_ge. eauto. }
    destruct Hlub as [Hub Hlub].
    assert (sum_n a n' <= x); eauto.
    replace ((@sum_n (NormedModule.AbelianGroup R_AbsRing R_NormedModule) a n'))
            with ((@sum_n R_AbelianGroup a n')) by auto.
    nra.
  - apply Lim_seq_le_loc_const.
    * transitivity (a O); auto. 
      rewrite -(sum_O a). done.
    * exists O. auto.
Qed.

Lemma ex_series_is_lim_seq (f: nat → R):
  ex_series f → is_lim_seq (sum_n f) (Series f).
Proof.
  intros Hex. by eapply Series_correct.
Qed.
