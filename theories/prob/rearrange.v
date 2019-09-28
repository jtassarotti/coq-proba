(*
   Here we prove that if a series converges absolutely, then every
   rearrangement of that series (1) converges absolutely, and (2)
   converges to the same value.  This is needed to show that the
   definition of expectation is sensible and matches alternate ways of
   defining it.
*)

From discprob.basic Require Import base order bigop_ext nify sval.
From discprob.prob Require Import countable.
Require Import Reals Fourier Omega Psatz ClassicalEpsilon.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq bigop fintype ssrnat choice.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.

Lemma sum_n_m_filter (a: nat → R) (P: pred nat) n m:
  sum_n_m (λ n, if P n then (Rabs (a n)) else 0) n m <= sum_n_m (Rabs \o a) n m.
Proof.
  apply sum_n_m_le => k. destruct (P k) => //=; try nra.
  apply Rabs_pos.
Qed.

Lemma foldl_max l:
  ∀ x, foldl max x l ≥ x.
Proof.
  induction l; rewrite //=; intros; try lia.
  specialize (IHl (Init.Nat.max x a)).
  etransitivity; eauto. apply Max.le_max_l.
Qed.

Lemma max_fun_range (σ: nat → nat) m:
  ∃ N, (∀ m', m' ≤ m → σ m' ≤ N) ∧ (∃ m0, m0 ≤ m ∧ σ m0 = N).
Proof.
  induction m.
  - exists (σ O). split.
    * by inversion 1.
    * exists O. split; auto.
  - destruct IHm as (N&?&Hachieve).
    exists (Init.Nat.max N (σ (S m))). split.
    * intros m'. inversion 1; subst.
      ** auto with *. 
      ** etransitivity; last apply Max.le_max_l; eauto.
    * apply (Max.max_case_strong).
      ** intros. destruct Hachieve as (m0&?&?). exists m0; split; subst; auto. 
      ** intros. exists (S m). split; auto.
Qed.

Section bijective.

Lemma bij_nat_cover (σ: nat → nat) (bij: bijective σ):
  ∀ n, ∃ m, ∀ m', m' ≥ m → 
  ∃ N, (∀ n', n' ≤ n → ∃ m'', m'' ≤ m' ∧ σ m'' = n') ∧ N ≥ n ∧ (∀ m'', m'' ≤ m' → σ m'' ≤ N).
Proof.
  destruct bij as [σinv Hcan1 Hcan2].
  induction n. 
  - exists (σinv O) => m' Hgem.
    edestruct (max_fun_range σ m') as (N&?&?).
    exists N; split. 
    * intros n'. inversion 1; subst. exists (σinv O); repeat split; auto.
    * split; auto with *.  
  - destruct IHn as (m&Hm). (* N&(IHm1&?&?)). *)
    exists (Init.Nat.max m (σinv (S n))) => m' Hgem.
    edestruct (max_fun_range σ (Init.Nat.max m' (σinv (S n)))) as (N'&Hbound&?).
    exists N'; repeat split.
    * intros n'. inversion 1; subst.
      ** exists (σinv (S n)). split; auto. 
         transitivity (Init.Nat.max m (σinv (S n))); first apply Max.le_max_r; eauto.
      ** destruct (Hm m') as (N&(IHm1&?&?)).
         { etransitivity; eauto; first apply Max.le_max_l. }
         destruct (IHm1 n') as (x&?&?); auto.
    * specialize (Hbound (σinv (S n))).
      rewrite Hcan2 in Hbound. apply Hbound. auto with *. 
    * intros m'' Hlem'. eapply Hbound. etransitivity; eauto. apply Max.le_max_l.
Qed.

Lemma sum_n_bij_sandwich (a: nat → R) (σ: nat → nat) (bij: bijective σ):
  ∀ n, ∃ m, ∀ m', m' ≥ m →
  ∃ n', n' ≥ n ∧ sum_n (Rabs \o a) n <= sum_n ((Rabs \o a) \o σ) m' <= sum_n (Rabs \o a) n'.
Proof.
  intros n; edestruct (bij_nat_cover σ bij n) as (m&Hm).
  exists m => m' Hgem. 
  edestruct Hm as (N&(Hhit&?&Hup)); eauto.
  exists N. repeat split; auto. 
  - rewrite ?sum_n_bigop //=.
    rewrite /index_enum.
    destruct bij as [σinv Hcan1 Hcan2].
    assert (Hupinv : ∀ n' : nat, n' ≤ n → σinv n' ≤ m').
    { 
      intros n'. move /Hhit => [m''] [Hle Heq].
      rewrite -Heq Hcan1. done.
    }
    set (σinv' := λ x: 'I_(S n), 
                  match x with
                    | Ordinal k Hle => 
                      Ordinal (proj2 (SSR_leq _ _) (le_n_S _ _ (Hupinv _ (proj1 (SSR_leq k n) Hle))))
                  end).
    apply (sum_reidx_map_le _ _ _ _ σinv').
    * intros (x&Hlex) ?. rewrite Hcan2. reflexivity.
    * intros; split; auto. rewrite -enumT mem_enum //=.
    * intros. apply Rle_ge, Rabs_pos. 
    * rewrite -enumT. apply enum_uniq.
    * rewrite -enumT. apply enum_uniq.
    * intros (x&?) (y&?) => //= _. inversion 1. apply ord_inj => //=.
      apply (bij_inj (Bijective Hcan2 Hcan1)). done.
  - rewrite ?sum_n_bigop //=.
    rewrite /index_enum.
    set (σ' := λ x: 'I_(S m'), 
                  match x with
                    | Ordinal k Hle => 
                      Ordinal (proj2 (SSR_leq _ _) (le_n_S _ _ (Hup _ (proj1 (SSR_leq k m') Hle))))
                  end).
    apply (sum_reidx_map_le _ _ _ _ σ').
    * intros (x&Hlex) ?. reflexivity.
    * intros; split; auto. rewrite -enumT mem_enum //=.
    * intros. apply Rle_ge, Rabs_pos. 
    * rewrite -enumT. apply enum_uniq.
    * rewrite -enumT. apply enum_uniq.
    * intros (x&?) (y&?) => //= _. inversion 1. apply ord_inj => //=.
      apply (bij_inj bij). done.
Qed.

Lemma sum_n_m_bij_diff_abs (a: nat → R) (σ: nat → nat) (bij: bijective σ):
  ∀ N, ∃ M, ∀ m, m ≥ M → 
  ∃ n, n ≥ N ∧ Rabs (sum_n (Rabs \o a \o σ) m - sum_n (Rabs \o a) N) <= sum_n_m (Rabs \o a) (S N) n.
Proof.
  intros N. 
  destruct (sum_n_bij_sandwich a σ bij N) as (M&HM).
  exists M => m HgeM.
  edestruct (HM m HgeM) as (N'&?&(?&?)); eauto.
  exists N'; split; auto.
  rewrite (sum_n_m_sum_n); last done.
  rewrite Rabs_right; last nra.
  rewrite /minus/plus/opp/=. nra.
Qed.

Lemma sum_n_m_bij_diff (a: nat → R) (σ: nat → nat) (bij: bijective σ):
  ∀ N, ∃ M, ∀ m, m ≥ M → 
  ∃ n, n ≥ N ∧ Rabs (sum_n (a \o σ) m - sum_n a N) <= sum_n_m (Rabs \o a) (S N) n.
Proof.
  intros n; edestruct (bij_nat_cover σ bij n) as (m&Hm).
  exists m => m' Hgem. 
  edestruct Hm as (N&(Hhit&?&Hup)); eauto.
  exists N. repeat split; auto. 
  transitivity (Rabs (\big[Rplus/0]_(S n <= i < S N | exC (λ m0, (leq m0 m') && (σ m0 == i))) (a i)));
    last first.
  { 
    rewrite sum_n_m_bigop. etransitivity; first apply Rabs_bigop_triang.
    rewrite //=. apply Rabs_bigop_filter. auto.
  }
  right. f_equal.
  assert (sum_n (a \o σ) m' =
          \big[Rplus/0]_(i < S N | exC (λ m0, (m0 <= m')%nat && (σ m0 == i))) a i) as ->.
  { 
    rewrite sum_n_bigop. 
    rewrite /index_enum.
    set (σ' := λ x: 'I_(S m'), 
                  match x with
                    | Ordinal k Hle => 
                      Ordinal (proj2 (SSR_leq _ _) (le_n_S _ _ (Hup _ (proj1 (SSR_leq k m') Hle))))
                  end).
    eapply (sum_reidx_map (Finite.enum (ordinal_finType m'.+1)) 
                          (Finite.enum (ordinal_finType N.+1)) 
                          (λ x, true) _ σ').
    * intros (x&Hlex) ? => //=. 
    * intros (m0&?); split; auto. apply (introT (exCP _)). 
      exists m0. apply /andP; split => //=. 
    * intros (n'&?) _. move /exCP => [m0]. move /andP => [Hle Heq].
      intros Hfalse. contradiction Hfalse. 
      assert (m0 < S m')%nat as Hlt.
      { nify.  omega. }
      exists (Ordinal Hlt). repeat split; eauto.
      apply ord_inj => //=. nify. done.
    * rewrite -enumT. apply enum_uniq.
    * rewrite -enumT. apply enum_uniq.
    * intros (x&?) (y&?)  _ => //=. inversion 1. apply ord_inj => //=.
      eapply bij_inj; eauto.
  }
  assert (sum_n a n =
          \big[Rplus/0]_(i < S n | exC (λ m0, (m0 <= m')%nat && (σ m0 == i))) a i) as ->.
  {
    rewrite sum_n_bigop.
    apply eq_bigl. intros (i&Hle). 
    symmetry. eapply (introT (exCP _)).
    edestruct (Hhit i) as (m''&?&?); first by (nify; lia).
    exists m''. apply /andP; split; nify; auto.
  }
  rewrite -(big_mkord (λ i, exC (λ m0, (m0 <= m')%nat && (σ m0 == i)))).
  assert (S n <= S N)%nat as Hsplit by (nify; lia).
  rewrite (big_cat_nat _ _ _ _ Hsplit) //=.
  rewrite big_mkord.
  assert (∀ a b, a + b - a = b) as -> by (intros; field).
  done.
Qed.

Lemma norm_dist_mid x y z: norm (x - y) <= norm (x - z) + norm (z - y).
Proof.
  replace (x - y) with ((x - z) + (z - y)) by field.
  etransitivity; last eapply norm_triangle.
  apply Rle_refl.
Qed.
Lemma series_rearrange (a: nat → R) (σ: nat → nat) (bij: bijective σ) (v: R): 
  is_series (λ n, Rabs (a n)) v →
  is_series (λ n, Rabs (a (σ n))) v ∧
  is_series (λ n, a (σ n)) (Series a).
Proof.
  intros Habsconv.
  assert (ex_series a) as (v'&Hconv) by (eapply ex_series_Rabs; eexists; eauto).
  assert(Hnorm: ∀ eps : posreal, ∃ N M, ∀ m, M ≤ m → 
         norm (sum_n (Rabs \o a) N - sum_n (Rabs \o a \o σ) m) < eps ∧
         norm (sum_n a N - sum_n (a \o σ) m) < eps ∧
         norm (sum_n (Rabs \o a) N - v) < eps ∧
         norm (sum_n a N - v') < eps).
  { 
    intros eps. 
    edestruct (Cauchy_ex_series (Rabs \o a)) as (N0&IHN). 
    { exists v; eauto. }
    assert (∃ N, ∀ N', N' ≥ N → norm (sum_n (Rabs \o a) N' - v) < eps) as (N1&HN1).
    { rewrite /is_series in Habsconv. 
      edestruct Habsconv as (x&Hball). eapply locally_ball.
      exists x. eapply Hball.
    }
    assert (∃ N, ∀ N', N' ≥ N → norm (sum_n a N' - v') < eps) as (N2&HN2).
    { rewrite /is_series in Hconv.
      edestruct Hconv as (x&Hball). eapply locally_ball.
      exists x. eapply Hball. 
    }
    set (N := max N0 (max N1 N2)).
    edestruct (sum_n_m_bij_diff_abs a σ bij N) as (M1&IHM1).
    edestruct (sum_n_m_bij_diff a σ bij N) as (M2&IHM2).
    exists N. exists (max M1 M2) => m Hle. 
    apply Nat.max_lub_iff in Hle as (?&?).
    rewrite /norm//=/abs//=; repeat split; auto. 
    - rewrite Rabs_minus_sym. edestruct (IHM1 m) as (n&?&Hle); auto. 
      eapply Rle_lt_trans; first eapply Hle.
      rewrite /norm//=/abs//= in IHN.
      eapply Rle_lt_trans; first apply Rle_abs. 
      assert (N0 <= N)%coq_nat.
      { rewrite /N. apply Max.le_max_l. }
      eapply IHN; auto. omega. 
    - rewrite Rabs_minus_sym. edestruct (IHM2 m) as (n&?&Hle); auto. 
      eapply Rle_lt_trans; first eapply Hle.
      rewrite /norm//=/abs//= in IHN.
      eapply Rle_lt_trans; first apply Rle_abs. 
      assert (N0 <= N)%coq_nat.
      { rewrite /N. apply Max.le_max_l. }
      eapply IHN; auto. omega. 
    - eapply HN1. 
      rewrite /N. etransitivity; first apply Max.le_max_r. apply Max.le_max_l.
    - eapply HN2. 
      rewrite /N. etransitivity; first apply Max.le_max_r. apply Max.le_max_r.
  }
  split.
  - rewrite /is_series. eapply filterlim_locally => eps.
    edestruct (Hnorm (pos_div_2 eps)) as (N&M&?HNM).
    exists M => m Hle.
    specialize (HNM m Hle) as (?&?&?&?).
    rewrite /ball//=/AbsRing_ball//=/abs/AbsRing.abs//=/minus//=/plus//=/opp//=.
    specialize (norm_dist_mid (sum_n (Rabs \o a \o σ) m) v (sum_n (Rabs \o a) N)).
    rewrite {1}/norm//={1}/Rminus.
    intros Hle'. eapply Rle_lt_trans; first eapply Hle'.
    destruct eps as (eps&?).
    replace (eps) with (eps/2 + eps/2); last by field.
    apply Rplus_lt_compat; eauto.
    rewrite /norm//=/abs//= Rabs_minus_sym. done. 
  - assert (Series a = v') as -> by (eapply is_series_unique; eauto). 
    rewrite /is_series. eapply filterlim_locally => eps.
    edestruct (Hnorm (pos_div_2 eps)) as (N&M&?HNM).
    exists M => m Hle.
    specialize (HNM m Hle) as (?&?&?&?).
    rewrite /ball//=/AbsRing_ball//=/abs/AbsRing.abs//=/minus//=/plus//=/opp//=.
    specialize (norm_dist_mid (sum_n (a \o σ) m) v' (sum_n a N)).
    rewrite {1}/norm//={1}/Rminus.
    intros Hle'. eapply Rle_lt_trans; first eapply Hle'.
    destruct eps as (eps&?).
    replace (eps) with (eps/2 + eps/2); last by field.
    apply Rplus_lt_compat; eauto.
    rewrite /norm//=/abs//= Rabs_minus_sym. done. 
Qed.

End bijective.

Section covering.

Variable (a: nat → R).
Variable (σ: nat → nat).  
Variable (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n').
Variable (COV: ∀ n, a n <> 0 → ∃ m, σ m = n).

Lemma inj_nat_cover:
  ∀ n, ∃ m, ∀ m', m' ≥ m → 
  ∃ N, (∀ n', n' ≤ n → (∃ m'', m'' ≤ m' ∧ σ m'' = n') ∨ a n' = 0) 
       ∧ N ≥ n ∧ (∀ m'', m'' ≤ m' → σ m'' ≤ N).
Proof.
  induction n. 
  - destruct (Req_dec (a O) 0) as [|Hneq].
    * exists O => m' Hge. 
      edestruct (max_fun_range σ m') as (N&?&?).
      exists N; split.
      ** intros n'. inversion 1. subst. auto.
      ** split; auto with *. 
    * edestruct (COV O Hneq) as (m&?). 
      exists m => m'. 
      edestruct (max_fun_range σ m') as (N&?&?).
      exists N; split.
      ** intros n'. inversion 1. subst. left. eauto.
      ** split; auto with *. 
  - destruct IHn as (m&Hm). 
    destruct (Req_dec (a (S n)) 0) as [|Hneq].
    * exists m => m' Hge. 
      edestruct Hm as (N&?&?&?); eauto.
      exists (S N); repeat split; auto; last omega.
      intros n'. inversion 1; subst; auto.
    * edestruct (COV (S n) Hneq) as (minv&Heq). 
    exists (Init.Nat.max m minv) => m' Hgem.
    edestruct (max_fun_range σ (Init.Nat.max m' minv)) as (N'&Hbound&?).
    exists N'; repeat split.
    ** intros n'. inversion 1; subst. left.
      *** exists minv. split; auto. 
         transitivity (Init.Nat.max m minv); first apply Max.le_max_r; eauto.
      *** destruct (Hm m') as (N&(IHm1&?&?)).
         { etransitivity; eauto; first apply Max.le_max_l. }
         eauto.
    ** specialize (Hbound minv).
       rewrite -Heq. eapply Hbound. apply Max.le_max_r. 
    ** intros m'' Hlem'. eapply Hbound. etransitivity; eauto. apply Max.le_max_l.
Qed.

Lemma sum_n_m_cover_diff:
  ∀ N, ∃ M, ∀ m, m ≥ M → 
  ∃ n, n ≥ N ∧ Rabs (sum_n (a \o σ) m - sum_n a N) <= sum_n_m (Rabs \o a) (S N) n.
Proof.
  intros n; edestruct (inj_nat_cover n) as (m&Hm).
  exists m => m' Hgem. 
  edestruct Hm as (N&(Hhit&?&Hup)); eauto.
  exists N. repeat split; auto. 
  transitivity (Rabs (\big[Rplus/0]_(S n <= i < S N | exC (λ m0, (leq m0 m') && (σ m0 == i))) (a i)));
    last first.
  { 
    rewrite sum_n_m_bigop. etransitivity; first apply Rabs_bigop_triang.
    rewrite //=. apply Rabs_bigop_filter. auto.
  }
  right. f_equal.
  assert (sum_n (a \o σ) m' =
          \big[Rplus/0]_(i < S N | exC (λ m0, (m0 <= m')%nat && (σ m0 == i))) a i) as ->.
  { 
    rewrite sum_n_bigop. 
    rewrite bigop_cond_non0 [a in _ = a]bigop_cond_non0.
    rewrite /index_enum.
    set (σ' := λ x: 'I_(S m'), 
                  match x with
                    | Ordinal k Hle => 
                      Ordinal (proj2 (SSR_leq _ _) (le_n_S _ _ (Hup _ (proj1 (SSR_leq k m') Hle))))
                  end).
    eapply (sum_reidx_map (Finite.enum (ordinal_finType m'.+1)) 
                          (Finite.enum (ordinal_finType N.+1)) 
                          _ _ σ').
    * intros (x&Hlex) ? => //=. 
    * intros (m0&?); split; auto. apply /andP; split; auto. apply (introT (exCP _)). 
      exists m0. apply /andP; split => //=. 
    * intros (n'&?) _. move /andP => [HexC ?]. move /exCP in HexC.
      destruct (HexC) as (m0&HexC'). move /andP in HexC'.  destruct (HexC') as (?&Heq).
      intros Hfalse. contradiction Hfalse. 
      assert (m0 < S m')%nat as Hlt.
      { nify.  omega. }
      exists (Ordinal Hlt). repeat split; auto.
      ** apply /andP; split; auto. rewrite //=. move /eqP in Heq. rewrite Heq. done. 
      ** apply ord_inj => //=. nify. done.
    * rewrite -enumT. apply enum_uniq.
    * rewrite -enumT. apply enum_uniq.
    * intros (x&?) (y&?) Hneq0 => //=. inversion 1. apply ord_inj => //=.
      eapply INJ; eauto. move /eqP. move /negP in Hneq0. auto.
  }
  assert (sum_n a n =
          \big[Rplus/0]_(i < S n | exC (λ m0, (m0 <= m')%nat && (σ m0 == i))) a i) as ->.
  {
    rewrite sum_n_bigop.
    rewrite bigop_cond_non0 [a in _ = a]bigop_cond_non0.
    eapply (sum_reidx_map _ _ _ _ id).
    * intros (x&Hlex) ? => //=. 
    * intros (n'&Hle) ? Hneq0; split; auto. apply /andP; split; auto. apply (introT (exCP _)). 
      edestruct (Hhit n') as [(m''&?&?)|].
      { clear -Hle. nify. omega. }
      ** exists m''. apply /andP; split; nify; try omega => //=. subst. done.
      ** exfalso. rewrite //= in Hneq0. move /eqP in Hneq0. auto. 
    * intros (n'&Hle) _. move /andP => [HexC ?]. move /exCP in HexC.
      destruct (HexC) as (m0&HexC'). move /andP in HexC'.  destruct (HexC') as (?&Heq).
      intros Hfalse. exfalso. eapply Hfalse. exists (Ordinal Hle). repeat split; auto.
    * rewrite /index_enum. rewrite -enumT. apply enum_uniq.
    * rewrite /index_enum. rewrite -enumT. apply enum_uniq.
    * intros (x&?) (y&?) => //=.
  }
  rewrite -(big_mkord (λ i, exC (λ m0, (m0 <= m')%nat && (σ m0 == i)))).
  assert (S n <= S N)%nat as Hsplit by (nify; lia).
  rewrite (big_cat_nat _ _ _ _ Hsplit) //=.
  rewrite big_mkord.
  assert (∀ a b, a + b - a = b) as -> by (intros; field).
  done.
Qed.

End covering.

Lemma series_rearrange_covering (a: nat → R) (σ: nat → nat) 
      (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n')
      (COV: ∀ n, a n <> 0 → ∃ m, σ m = n)
      (v: R): 
  is_series (λ n, Rabs (a n)) v →
  is_series (λ n, Rabs (a (σ n))) v ∧
  is_series (λ n, a (σ n)) (Series a).
Proof.
  intros Habsconv.
  assert (ex_series a) as (v'&Hconv) by (eapply ex_series_Rabs; eexists; eauto).
  assert(Hnorm: ∀ eps : posreal, ∃ N M, ∀ m, M ≤ m → 
         norm (sum_n (Rabs \o a) N - sum_n (Rabs \o a \o σ) m) < eps ∧
         norm (sum_n a N - sum_n (a \o σ) m) < eps ∧
         norm (sum_n (Rabs \o a) N - v) < eps ∧
         norm (sum_n a N - v') < eps).
  { 
    intros eps. 
    edestruct (Cauchy_ex_series (Rabs \o a)) as (N0&IHN). 
    { exists v; eauto. }
    assert (∃ N, ∀ N', N' ≥ N → norm (sum_n (Rabs \o a) N' - v) < eps) as (N1&HN1).
    { rewrite /is_series in Habsconv. 
      edestruct Habsconv as (x&Hball). eapply locally_ball.
      exists x. eapply Hball.
    }
    assert (∃ N, ∀ N', N' ≥ N → norm (sum_n a N' - v') < eps) as (N2&HN2).
    { rewrite /is_series in Hconv.
      edestruct Hconv as (x&Hball). eapply locally_ball.
      exists x. eapply Hball. 
    }
    set (N := max N0 (max N1 N2)).
    edestruct (sum_n_m_cover_diff (Rabs \o a) σ) as (M1&IHM1).
    {  rewrite //= => n n'. intros Hneq0. apply INJ; eauto. 
       intros Heq0. rewrite Heq0 Rabs_R0 in Hneq0. auto.
    }
    { 
      rewrite //= => n. intros Hneq0. eapply COV. 
       intros Heq0. rewrite Heq0 Rabs_R0 in Hneq0. auto.
    }
    edestruct (sum_n_m_cover_diff a σ INJ COV N) as (M2&IHM2).
    exists N. exists (max M1 M2) => m Hle. 
    apply Nat.max_lub_iff in Hle as (?&?).
    rewrite /norm//=/abs//=; repeat split; auto. 
    - rewrite Rabs_minus_sym. edestruct (IHM1 m) as (n&?&Hle); auto. 
      eapply Rle_lt_trans; first eapply Hle.
      rewrite /norm//=/abs//= in IHN.
      eapply Rle_lt_trans; first apply Rle_abs. 
      assert (N0 <= N)%coq_nat.
      { rewrite /N. apply Max.le_max_l. }
      eapply Rle_lt_trans; last apply (IHN (S N) n); auto; try omega.
      right. f_equal. apply sum_n_m_ext_loc; auto.
      intros => //=. rewrite //= Rabs_Rabsolu. done.
    - rewrite Rabs_minus_sym. edestruct (IHM2 m) as (n&?&Hle); auto. 
      eapply Rle_lt_trans; first eapply Hle.
      rewrite /norm//=/abs//= in IHN.
      eapply Rle_lt_trans; first apply Rle_abs. 
      assert (N0 <= N)%coq_nat.
      { rewrite /N. apply Max.le_max_l. }
      eapply IHN; auto. omega. 
    - eapply HN1. 
      rewrite /N. etransitivity; first apply Max.le_max_r. apply Max.le_max_l.
    - eapply HN2. 
      rewrite /N. etransitivity; first apply Max.le_max_r. apply Max.le_max_r.
  }
  split.
  - rewrite /is_series. eapply filterlim_locally => eps.
    edestruct (Hnorm (pos_div_2 eps)) as (N&M&?HNM).
    exists M => m Hle.
    specialize (HNM m Hle) as (?&?&?&?).
    rewrite /ball//=/AbsRing_ball//=/abs/AbsRing.abs//=/minus//=/plus//=/opp//=.
    specialize (norm_dist_mid (sum_n (Rabs \o a \o σ) m) v (sum_n (Rabs \o a) N)).
    rewrite {1}/norm//={1}/Rminus.
    intros Hle'. eapply Rle_lt_trans; first eapply Hle'.
    destruct eps as (eps&?).
    replace (eps) with (eps/2 + eps/2); last by field.
    apply Rplus_lt_compat; eauto.
    rewrite /norm//=/abs//= Rabs_minus_sym. done. 
  - assert (Series a = v') as -> by (eapply is_series_unique; eauto). 
    rewrite /is_series. eapply filterlim_locally => eps.
    edestruct (Hnorm (pos_div_2 eps)) as (N&M&?HNM).
    exists M => m Hle.
    specialize (HNM m Hle) as (?&?&?&?).
    rewrite /ball//=/AbsRing_ball//=/abs/AbsRing.abs//=/minus//=/plus//=/opp//=.
    specialize (norm_dist_mid (sum_n (a \o σ) m) v' (sum_n a N)).
    rewrite {1}/norm//={1}/Rminus.
    intros Hle'. eapply Rle_lt_trans; first eapply Hle'.
    destruct eps as (eps&?).
    replace (eps) with (eps/2 + eps/2); last by field.
    apply Rplus_lt_compat; eauto.
    rewrite /norm//=/abs//= Rabs_minus_sym. done. 
Qed.

Lemma series_rearrange_covering_pos (a: nat → R) (σ: nat → nat) 
      (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n')
      (COV: ∀ n, a n <> 0 → ∃ m, σ m = n)
      (POS: ∀ n, a n >= 0)
      (v: R): 
  is_series a v →
  is_series (λ n, a (σ n)) v.
Proof.
  intros. eapply (is_series_ext (λ n, Rabs (a (σ n)))).
  { intros n. rewrite Rabs_right; auto. }
  edestruct series_rearrange_covering as (His1&?); last eapply His1; eauto.
  eapply is_series_ext; eauto.
  { intros n. rewrite Rabs_right; auto. }
Qed.

Lemma Series_rearrange_covering (a: nat → R) (σ: nat → nat) 
      (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n')
      (COV: ∀ n, a n <> 0 → ∃ m, σ m = n):
  ex_series (λ n, Rabs (a n)) →
  Series a = Series (a \o σ). 
Proof.
  intros (v'&?).
  symmetry. apply is_series_unique. edestruct series_rearrange_covering; eauto.
Qed.

Lemma countable_series_rearrange_covering {Y X: countType}
      (a: X → R) (σ: Y → X)
      (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n')
      (COV: ∀ n, a n <> 0 → ∃ m, σ m = n)
      (v: R): 
  is_series (countable_sum (λ n, Rabs (a n))) v →
  is_series (countable_sum (λ n, Rabs (a (σ n)))) v ∧
  is_series (countable_sum (λ n, a (σ n))) (Series (countable_sum a)).
Proof.
  set (a' := λ n, match n with | O => 0 | S n' => countable_sum a n' end).
  set (σ' := λ n, match pickle_inv Y n with
                  | Some x =>
                    S (pickle (σ x))
                  | None => O
                  end).
  intros His. edestruct (series_rearrange_covering a' σ') as (Habs&?).
  { intros n n'. rewrite /σ'/a'/countable_sum/oapp//=.
    destruct (pickle_inv Y n) as [s|] eqn:Heqs.
    * rewrite pickleK_inv.
      destruct (pickle_inv Y n') as [s'|] eqn:Heqs'.
      ** intros ? HeqS. inversion HeqS as [Heq]. apply pickle_inj in Heq.
         assert (s = s').
         { eapply INJ; eauto. }
         subst. eapply pickle_inv_some_inj; eauto; congruence.
      ** intros Hneq0 Hpickle. inversion Hpickle.
    * nra.
  }
  { 
    intros n. rewrite /a'/countable_sum/σ'//=.
    destruct n as [|n]; first nra.
    destruct (pickle_inv X n) as [s|] eqn:Heqs.
    * rewrite //= => Hneq0.  edestruct (COV _ Hneq0) as (m&Heqm).
      exists (pickle m). rewrite pickleK_inv => //=. subst.
      f_equal.
      eapply pickle_inv_some_inv; eauto.
    * rewrite //=; nra.
  }
  {
    rewrite /a'.
    apply: is_series_decr_1.
    rewrite Rabs_R0 /opp//= Ropp_0/plus//= Rplus_0_r.
    eapply is_series_ext; last eassumption.
    intros n. rewrite /countable_sum//=. destruct pickle_inv => //=.
    by rewrite Rabs_R0.
  }
  split.
  * eapply is_series_ext; last eapply Habs.
    intros n. rewrite /a'/countable_sum/σ'//=.
    destruct (pickle_inv Y n) as [s|] eqn:Heqs.
    ** rewrite pickleK_inv //=.
    ** rewrite //= Rabs_R0 //=.
  * assert (Series a' = Series (countable_sum a)) as Heq.
    { rewrite /a'. by eapply Series_incr_1_aux. }
    rewrite -Heq.
    eapply is_series_ext; last eassumption.
    intros n. rewrite /a'/countable_sum/σ'//=.
    destruct (pickle_inv Y n) as [s|] eqn:Heqs.
    ** rewrite pickleK_inv //=.
    ** rewrite //=.
Qed.

Lemma countable_series_oapp {X: countType}
      (a: X → R) (v: R): 
  is_series (countable_sum (λ n, Rabs (oapp a R0 n))) v →
  is_series (countable_sum (λ n, Rabs (a n))) v ∧
  is_series (countable_sum (λ n, a n)) (Series (countable_sum (oapp a R0))).
Proof.
  intros. edestruct (countable_series_rearrange_covering (oapp a R0) Some) as (Habs&?).
  { rewrite //=. intros. congruence. }
  { rewrite //=. intros [|]; rewrite //=; (eauto || nra). }
  { eauto. } 
  split.
  * eapply is_series_ext; last eapply Habs.
    intros n. rewrite //=.
  * eapply is_series_ext; eauto.
Qed.

Lemma countable_series_oapp' {X: countType}
      (a: X → R) (v: R): 
  is_series (countable_sum (λ n, Rabs (a n))) v →
  is_series (countable_sum (λ n, Rabs (oapp a R0 n))) v ∧
  is_series (countable_sum (oapp a R0)) (Series (countable_sum a)).
Proof.
  intros His.
  set (a' := λ n, match n with | O => 0 | S n' => countable_sum a n' end).
  set (σ' := λ n, match pickle_inv (option_countType X) n with
                  | Some (Some x) =>
                    S (pickle x)
                  | _ => O
                  end).
  edestruct (series_rearrange_covering a' σ') as (Habs&?).
  { intros n n'. rewrite /σ'/a'/countable_sum/oapp//=.
    destruct (pickle_inv (option_countType X) n) as [[s|]|] eqn:Heqs.
    * rewrite pickleK_inv.
      destruct (pickle_inv (option_countType X) n') as [[s'|]|] eqn:Heqs'.
      ** intros ? HeqS. inversion HeqS as [Heq]. apply pickle_inj in Heq.
         subst. eapply pickle_inv_some_inj; eauto; congruence.
      ** intros Hneq0 Hpickle. inversion Hpickle.
      ** intros Hneq0 Hpickle. inversion Hpickle.
    * nra.
    * congruence.
  }
  { 
    intros n. rewrite /a'/countable_sum/σ'//=.
    destruct n as [|n]; first nra.
    destruct (pickle_inv X n) as [s|] eqn:Heqs => //=.
    * rewrite //= => Hneq0.
      exists (pickle (Some s)). rewrite pickleK_inv => //=. f_equal.
      eapply pickle_inv_some_inv; eauto.
  }
  {
    rewrite /a'.
    apply: is_series_decr_1.
    rewrite Rabs_R0 /opp//= Ropp_0/plus//= Rplus_0_r.
    eapply is_series_ext; last eassumption.
    intros n. rewrite /countable_sum//=. destruct pickle_inv => //=.
    by rewrite Rabs_R0.
  }
  split.
  * eapply is_series_ext; last eapply Habs.
    intros n. rewrite /a'/countable_sum/σ'//=.
    destruct (pickle_inv (option_countType X) n) as [[s|]|] eqn:Heqs.
    ** rewrite pickleK_inv //=.
    ** rewrite //= Rabs_R0 //=.
    ** rewrite //= Rabs_R0 //=.
  * assert (Series a' = Series (countable_sum a)) as Heq.
    { rewrite /a'. by eapply Series_incr_1_aux. }
    rewrite -Heq.
    eapply is_series_ext; last eassumption.
    intros n. rewrite /a'/countable_sum/σ'//=.
    destruct (pickle_inv (option_countType X) n) as [[s|]|] eqn:Heqs.
    ** rewrite pickleK_inv //=.
    ** rewrite //=.
    ** rewrite //=.
Qed.

Lemma countable_Series_oapp' {X: countType}
      (a: X → R):
  ex_series (countable_sum (λ n, Rabs (a n))) →
  Series (countable_sum a) = Series (countable_sum (oapp a R0)).
Proof.
  intros (v&Hex).
  edestruct (countable_series_oapp' a); eauto.
  symmetry. apply is_series_unique; eauto.
Qed.

Remark gt_support_conv {X: countType} (b: X → R): ∀ x, b x > 0 → support b.
Proof.
  intros x Hgt. exists x. destruct (Rgt_dec (b x) 0); auto.
Defined.

Lemma countable_series_rearrange_covering_match {X Y: countType}
      (a: X → R) (b: Y → R) (σ: support b → support a)
      (Hapos: ∀ x, a x >= 0) 
      (Hbpos: ∀ x, b x >= 0) 
      (INJ: ∀ n n', σ n = σ n' → n = n')
      (COV: ∀ n, ∃ m, σ m = n)
      (EQ: ∀ n, a (sval (σ n)) = b (sval n))
      (v: R): 
  is_series (countable_sum (λ n, a n)) v →
  is_series (countable_sum (λ n, b n)) v.
Proof.
  intros His.
  set (σ':=
         λ y, match Rgt_dec (b y) 0 with
              | left Hpf =>
                Some (sval (σ (gt_support_conv _ _ Hpf)))
              | _  => None
              end).
    cut (is_series (countable_sum (λ n, Rabs (oapp a R0 (σ' n)))) v).
    { intros Hext. eapply is_series_ext; last eapply Hext.
      intros n. rewrite /countable_sum/σ'//=.
      destruct pickle_inv as [s|] => //=.
      { destruct Rgt_dec => //=.
        * rewrite EQ //=; try nra. 
          rewrite Rabs_right; nra.
        * rewrite Rabs_R0. destruct (Hbpos s); nra.
      }
    }
  edestruct (countable_series_rearrange_covering (oapp a R0) σ').
  { rewrite /σ'. intros n n'. do 2 destruct Rgt_dec => //=. 
    intros Hneq0 Heq. inversion Heq as [Heq']. apply sval_inj_pi in Heq'. eapply INJ in Heq'.
    inversion Heq'. done.
  }
  { intros [s|] => //=. intros Hneq0.
    destruct (Hapos s) as [Hgt0|Heq0]; last nra.
    destruct (COV (gt_support_conv a s Hgt0)) as (y&Heqy).
    exists (sval y). rewrite /σ'.
    destruct Rgt_dec as [|Hngt]; last first.
    { destruct y as (y&Hgt). simpl in Hngt. exfalso. clear -Hngt Hgt. destruct Rgt_dec; auto. } 
    f_equal. transitivity (sval (σ y)).
    { do 2 f_equal. apply sval_inj_pred => //=. }
    rewrite Heqy => //=.
  }
  { edestruct (countable_series_oapp' a).
    { eapply is_series_ext; last eassumption.
      rewrite /countable_sum => n. destruct (pickle_inv X n) => //=.
      rewrite Rabs_right; eauto.
    }
    eauto.
  }
  eauto.
Qed.

Lemma countable_series_rearrange_covering_match_fun {X Y: countType}
      (a: X → R) (b: Y → R) (σ: {x : Y | b x ≠ 0} → { x : X | a x ≠ 0 })
   (*   (Hapos: ∀ x, a x >= 0) 
      (Hbpos: ∀ x, b x >= 0)  *)
      (INJ: ∀ n n', σ n = σ n' → n = n')
      (COV: ∀ n, ∃ m, σ m = n)
      (EQ: ∀ n, a (sval (σ n)) = b (sval n))
      (v: R): 
  is_series (countable_sum (λ n, Rabs (a n))) v →
  is_series (countable_sum (λ n, Rabs (b n))) v ∧
  is_series (countable_sum b) (Series (countable_sum a)).
Proof.
  intros His.
  set (σ':=
         λ y, match Req_EM_T (b y) 0 with
              | right Hpf =>
                Some (sval (σ (exist _ y Hpf)))
              | _  => None
              end).
  assert (Hext0: ∀ n : nat, countable_sum (λ n0 : Y, (oapp a R0 (σ' n0))) n
                           = countable_sum (λ n0 : Y, (b n0)) n).
  { 
      intros n. rewrite /countable_sum/σ'//=.
      destruct pickle_inv as [s|] => //=.
      { destruct Req_EM_T as [Heq0|Hneq0] => //=.
        rewrite //=. eapply EQ.
      }
  }
  cut (is_series (countable_sum (λ n, Rabs (oapp a R0 (σ' n)))) v ∧
       is_series (countable_sum (λ n, oapp a R0 (σ' n))) (Series (countable_sum a))).
  { intros (Hext_abs&Hext). split.
    * eapply is_series_ext; last eapply Hext_abs.
      intros n. rewrite ?countable_sum_Rabs. f_equal; eauto.
    * eapply is_series_ext; last eapply Hext.
      intros n. eauto.
  }
  edestruct (countable_series_rearrange_covering (oapp a R0) σ').
  { rewrite /σ'. intros n n'. do 2 destruct Req_EM_T => //=. 
    intros Hneq0 Heq. inversion Heq as [Heq']. apply sval_inj_pi in Heq'. eapply INJ in Heq'.
    inversion Heq'. done.
  }
  { intros [s|] => //=. intros Hneq0.
    destruct (COV (exist _ s Hneq0)) as (y&Heqy).
    exists (sval y). rewrite /σ'.
    destruct Req_EM_T as [Hngt|].
    { destruct y as (y&Hgt). simpl in Hngt. exfalso. clear -Hngt Hgt. congruence. }
    f_equal. transitivity (sval (σ y)).
    { do 2 f_equal. apply sval_inj_pi => //=. }
    rewrite Heqy => //=.
  }
  { edestruct (countable_series_oapp' a).
    { eapply is_series_ext; last eassumption.
      rewrite /countable_sum => n. destruct (pickle_inv X n) => //=.
    }
    eauto.
  }
  split; eauto.
  rewrite countable_Series_oapp'; eauto.
  eexists; eauto.
Qed.