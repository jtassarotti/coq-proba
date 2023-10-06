From stdpp Require Import tactics.
From discprob.basic Require Import base order nify.
Require Import Ranalysis5.
Require Import Reals Fourier FunctionalExtensionality.
From Coquelicot Require Export Rcomplements Rbar Series Lim_seq Hierarchy Markov Continuity ElemFct.
Require Import List.
Require Import Psatz Lia.


Local Notation "x ≤ y" := (Rle x y) (at level 70, no associativity).
Local Notation "x ≥ y" := (Rge x y) (at level 70, no associativity).


Lemma Rmult_eq_0_inv_r: ∀ r r1 r2 : R, (r ≠ 0 → r1 = r2) → r * r1 = r * r2.
Proof.
  intros r r1 r2; case (Req_dec r 0).
  - intros ->. by rewrite !Rmult_0_l.
  - intros Hneq Heq. rewrite Heq //.
Qed.

Lemma Rmult_eq_0_inv_l: ∀ r r1 r2 : R, (r ≠ 0 → r1 = r2) → r1 * r = r2 * r.
Proof.
  intros r r1 r2; case (Req_dec r 0).
  - intros ->. by rewrite !Rmult_0_r.
  - intros Hneq Heq. rewrite Heq //.
Qed.

Lemma Rmult_neq_0_compat: ∀ r1 r2 : R, r1 ≠ 0 → r2 ≠ 0 → r1 * r2 ≠ 0.
Proof. intros r1 r2 ?? [?|?]%Rmult_integral; congruence. Qed.

Lemma Rdiv_le_compat_contra: ∀ r1 r2 r3 r4 : R,
    0 ≤ r1 → 0 < r4 → r1 ≤ r2 → r4 ≤ r3 → r1 / r3 ≤ r2 / r4.
Proof.
  intros. rewrite /Rdiv. apply Rmult_le_compat; auto.
  rewrite -(Rmult_1_l (/ r3)). apply Rle_mult_inv_pos; fourier.
    by apply Rinv_le_contravar.
Qed.

Lemma Rmult_le_0_compat x y: 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
Proof.
  intros. rewrite -[a in a ≤ _](Rmult_0_l 0).
  apply Rmult_le_compat; eauto; try reflexivity.
Qed.


Lemma fold_right_plus_mult (l: list R) v :
  (fold_right Rplus 0 l) * v = fold_right Rplus 0 (map (λ x, x * v) l).
Proof.
  induction l => //=; first nra.
  ring_simplify. rewrite IHl. done.
Qed.

Lemma fold_right_map_Rmult_le {A} (l: list A) f f':
  (∀ x, In x l → 0 <= f x ∧ f x <= f' x) →
  fold_right Rmult 1 (map f l) <= fold_right Rmult 1 (map f' l).
Proof.
  intros Hin.
  cut (0 <= fold_right Rmult 1 (map f l) ∧
       fold_right Rmult 1 (map f l) <= fold_right Rmult 1 (map f' l)).
  { intros [? ?]; done. }
  induction l.
  - rewrite //=; intros; nra.
  - rewrite //=. destruct IHl.
    { intros a' Hin'. apply Hin. by right. }
    split.
    * apply Rmult_le_0_compat; eauto.
      edestruct (Hin a); eauto; first by left.
    * apply Rmult_le_compat; auto.
      ** edestruct (Hin a); eauto; first by left.
      ** edestruct (Hin a); eauto; first by left.
Qed.

Hint Resolve Rabs_pos Rle_ge.


Lemma Rabs_case r (P : R → Type):
  (0 <= r → P r) → (0 <= -r → P (-r)) → P (Rabs r).
Proof.
  intros Hcase1 Hcase2.
  destruct (Rle_dec 0 r) as [?|?%Rnot_le_gt].
  * rewrite Rabs_right //=; eauto; try nra.
  * rewrite Rabs_left1 //=.
    ** eapply Hcase2. apply Ropp_le_cancel.
       rewrite Ropp_0 Ropp_involutive. left. auto.
    ** left. auto.
Qed.

Lemma open_interval_open x y :
  open (open_interval x y).
Proof.
  rewrite /open => z [? ?].
  rewrite /locally.
  unshelve (eexists).
  { exists (Rmin (z - x) (y - z)). abstract (apply Rmin_pos; nra).  }
  intros z' => //=. rewrite /ball//=/AbsRing_ball//=/abs//=.
  apply Rmin_case_strong; apply Rabs_case;
    rewrite /open_interval/minus//=/plus//=/opp//=; intros; split; nra.
Qed.

Lemma disc_ball z Δ x:
  disc z Δ x ↔ ball z Δ x.
Proof. rewrite /disc/ball//=. Qed.

Lemma open_included_disc U z:
  open U → U z → ∃ delta : posreal, included (disc z delta) U.
Proof.
  intros Hopen Hz. edestruct Hopen as (delta&Hdelta); eauto.
  exists delta. intros ??. apply Hdelta; eauto.
Qed.

Lemma open_open_set U:
  open U → open_set U.
Proof. done. Qed.

Lemma disc_neighbourhood x (δ: posreal):
  neighbourhood (disc x δ) x.
Proof.
  rewrite /neighbourhood; exists δ. rewrite /included. done.
Qed.

Lemma ball_neighbourhood x (δ: R):
  δ > 0 →
  neighbourhood (ball x δ) x.
Proof.
  rewrite /neighbourhood. unshelve (eexists).
  { exists δ.  nra. }
  rewrite //=.
Qed.

Lemma pos_INR': ∀ n : nat, (0 < n)%nat → 0 < INR n.
Proof. intros n Hlt. replace 0 with (INR 0) by auto. by apply lt_INR.  Qed.

Lemma archimed_rat_dense1 eps r:
  0 < eps →
  0 <= r →
  ∃ n m, r < INR n / INR m < r + eps ∧ (0 < m)%nat.
Proof.
  intros Hpos1 Hpos2.
  edestruct (archimed_cor1 eps) as (m&Hm1&Hm2); auto.
  edestruct (archimed (r * (INR m))) as (Hup1&Hup2).
  assert (0 < INR m) by (apply pos_INR'; done).
  assert (0 <= r * INR m).
  { apply (pos_INR') in Hm2. rewrite /Rdiv.
    apply Rmult_le_pos; auto. nra.
  }
  assert (0 <= up (r * INR m))%Z.
  { apply le_IZR. nra. }
  exists (Z.to_nat (up (r * INR m))).
  exists m.
  split; first split; auto.
  *  rewrite INR_IZR_INZ.
     rewrite Z2Nat.id //=. apply (Rmult_lt_reg_r (INR m)); auto.
     rewrite /Rdiv Rmult_assoc. rewrite Rinv_l; last by nra.
     rewrite Rmult_1_r. done.
  *  rewrite INR_IZR_INZ.
     rewrite Z2Nat.id //=. apply (Rmult_lt_reg_r (INR m)); auto.
     rewrite /Rdiv Rmult_assoc. rewrite Rinv_l; last by nra.
     rewrite Rmult_1_r. rewrite Rmult_plus_distr_r.
     apply (Rle_lt_trans _ (r * INR m + 1)); first by nra.
     cut (1 < eps * INR m); first by nra.
     rewrite -(Rinv_l (INR m)); last by nra. apply Rmult_lt_compat_r; nra.
Qed.

Lemma archimed_rat_dense2 eps r:
  0 < eps →
  r < 0 →
  ∃ n m, r < - INR n / INR m < r + eps ∧ (0 < m)%nat.
Proof.
  intros Hpos Hneg.
  assert (∃ eps', 0 < eps' <= eps ∧ r + eps' < 0) as (eps'&Hr&?).
  { destruct (Rlt_dec eps (-r)) as [Hlt|Hnlt].
    { exists eps; split; auto; try nra. }
    apply Rnot_lt_ge in Hnlt.
    exists (-r / 2); split; nra.
  }
  cut (∃ n m, r < - INR n / INR m < r + eps' ∧ (0 < m)%nat).
  { intros (n&m&?&?). exists n, m; split; auto. nra. }
  set (r' := -r - eps').
  edestruct (archimed_rat_dense1 eps' (-r - eps')) as (n&m&?&?); try nra.
  exists n, m; split; auto; try nra.
Qed.

Lemma is_lim_seq_plus_inv un vn u v:
  is_lim_seq (λ n, un n + vn n) (u + v) →
  is_lim_seq (λ n, vn n) v →
  is_lim_seq (λ n, un n) u.
Proof.
  intros Hlim1 Hlim2.
  apply (is_lim_seq_scal_l _ (-1)) in Hlim2. rewrite //= in Hlim2.
  eapply is_lim_seq_plus' in Hlim1; eauto.
  replace (-1 * v + (u + v)) with u in Hlim1 by nra.
  eapply is_lim_seq_ext; last by apply Hlim1.
  intros. nra.
Qed.

Lemma is_lim_seq_opp_inv un u:
  is_lim_seq (λ n, - un n) (- u) →
  is_lim_seq (λ n, un n) u.
Proof.
  intros Hlim.
  apply (is_lim_seq_scal_l _ (-1)) in Hlim. rewrite //= in Hlim.
  replace (-1 * -u) with u in Hlim by nra.
  eapply is_lim_seq_ext; try eassumption.
  intros n; nra.
Qed.

Lemma Rmin_diff_eq x y:
  Rmin x y = (x + y) / 2 - Rabs(x - y) / 2.
Proof.
  apply Rmin_case_strong; apply Rabs_case; nra.
Qed.

Lemma Rmax_diff_eq x y:
  Rmax x y = (x + y) / 2 + Rabs(x - y) / 2.
Proof.
  apply Rmax_case_strong; apply Rabs_case; nra.
Qed.

Lemma continuous_Rmin_l x y: continuous (Rmin x) y.
Proof.
  eapply continuous_ext.
  { intros x'. rewrite Rmin_diff_eq; done. }
  apply: continuous_minus.
  * apply: continuous_scal.
    ** apply: continuous_plus.
       *** apply: continuous_const.
       *** apply: continuous_id.
    ** apply: continuous_const.
  * apply: continuous_scal.
    ** apply: continuous_comp.
       *** apply: continuous_minus.
           **** apply: continuous_const.
           **** apply: continuous_id.
       *** apply: continuous_abs.
    ** apply: continuous_const.
Qed.

Lemma continuous_Rmax_l x y: continuous (Rmax x) y.
Proof.
  eapply continuous_ext.
  { intros x'. rewrite Rmax_diff_eq; done. }
  apply: continuous_plus.
  * apply: continuous_scal.
    ** apply: continuous_plus.
       *** apply: continuous_const.
       *** apply: continuous_id.
    ** apply: continuous_const.
  * apply: continuous_scal.
    ** apply: continuous_comp.
       *** apply: continuous_minus.
           **** apply: continuous_const.
           **** apply: continuous_id.
       *** apply: continuous_abs.
    ** apply: continuous_const.
Qed.

Lemma archimed_pos r: 0 <= r → ∃ n, INR n <= r < INR (S n).
Proof.
  intros Hpos. exists (Z.to_nat (up r - 1)).
  cut (INR (Z.to_nat (up r - 1)) = IZR (up r)- 1).
  { rewrite S_INR => ->. specialize (archimed r). nra. }
  rewrite Z2Nat.inj_sub; last lia.
  rewrite minus_INR.
  * rewrite //=. f_equal.
    rewrite INR_IZR_INZ.  f_equal.
    apply Z2Nat.id.
    apply le_IZR. specialize (archimed r); nra.
  * apply Z2Nat.inj_le; try lia.
    ** apply le_IZR. specialize (archimed r); nra.
    ** apply le_IZR. specialize (archimed r). intros (Hgt&?).
       assert (0 < up r)%Z.
       { apply lt_IZR. nra. }
       apply IZR_le. lia.
Qed.

Lemma pow_INR n k: INR (n^k) = INR n^k.
Proof.
  induction k => //=. rewrite ?plus_INR mult_INR -IHk.
  replace (INR 0) with 0 by auto. nra.
Qed.

Lemma INR_diff_lt_1_eq n k: 0 <= INR n - INR k < 1 → n = k.
Proof.
  intros (?&Hdiff).
  assert (Hpos:INR k <= INR n) by nra.
  apply INR_le in Hpos.
  rewrite -minus_INR in Hdiff; auto.
  replace 1 with (INR 1) in Hdiff; auto.
  apply INR_lt in Hdiff.
  lia.
Qed.

Lemma Sup_seq_const k: Sup_seq (λ n, k) = k.
Proof.
  rewrite Rbar_sup_eq_lub.
  apply Lub.Rbar_is_lub_unique => //=.
  split.
  * intros ? (?&->) => //=. apply Rbar_le_refl.
  * intros ? Hub. apply Hub; exists O; eauto.
Qed.

Lemma Sup_seq_real (xn: nat → R): Rbar_lt m_infty (Sup_seq xn).
Proof.
  apply (Rbar_lt_trans _ (xn O - 1)); first done.
  apply Sup_seq_minor_lt. exists O => //=. nra.
Qed.

Lemma Sup_seq_real_p_infty (xn: nat → R):
  Sup_seq xn = p_infty ↔ ∀ k, ∃ n, k <= xn n.
Proof.
  split.
  - rewrite /Sup_seq. destruct (ex_sup_seq) as (v&Hsup) => //=.
    apply is_sup_seq_lub in Hsup. intros; subst.
    destruct Hsup as (Hub&Hlub).
    apply Classical_Pred_Type.not_all_not_ex => Hall.
    cut (Rbar_le p_infty k); first done.
    apply Hlub. intros ? (n&->). rewrite //=.
    specialize (Hall n). nra.
  - intros Hunbounded. specialize (Sup_seq_real xn).
    rewrite /Sup_seq. destruct (ex_sup_seq) as ([ | |]&His) => //=.
    exfalso. apply is_sup_seq_lub in His.
    destruct His as (Hub&?).
    destruct (Hunbounded (r+1)) as (n&Hle).
    feed pose proof (Hub (xn n)) as Hle'.
    { exists n. auto. }
    rewrite //= in Hle'. nra.
Qed.


Definition Rbar_max (x y: Rbar) : Rbar :=
  match x, y with
  | Finite x', Finite y' => Rmax x' y'
  | m_infty, _ => y
  | _, m_infty => x
  | p_infty, _ => p_infty
  | _, p_infty => p_infty
  end.

Lemma Rbar_max_l: ∀ x y : Rbar, Rbar_le x (Rbar_max x y).
Proof.
  destruct x, y => //=; try apply Rmax_l; reflexivity.
Qed.

Lemma Rbar_max_r: ∀ x y : Rbar, Rbar_le y (Rbar_max x y).
  destruct x, y => //=; try apply Rmax_r; reflexivity.
Qed.

Lemma Rbar_max_comm: ∀ x y : Rbar, Rbar_max x y = Rbar_max y x.
Proof. destruct x, y => //=; by rewrite Rmax_comm. Qed.

Lemma Rbar_max_case: ∀ (x y : Rbar) (P : Rbar → Type), P x → P y → P (Rbar_max x y).
Proof. destruct x, y => //=; by apply Rmax_case. Qed.

Lemma Rbar_max_case_strong:
  ∀ (x y : Rbar) (P : Rbar → Type),
  (Rbar_le y x → P x) → (Rbar_le x y → P y) → P (Rbar_max x y).
Proof. destruct x, y => //=; try apply Rmax_case_strong; eauto. Qed.

Lemma norm_Rabs r: norm r = Rabs r.
Proof.
  rewrite /norm//=/abs.
Qed.
