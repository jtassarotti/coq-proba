(*
   So-called "summable" double series converge and can be rearranged and
   have the same value also if summed by columns or rows.

   This is used to consturuct the product distribution and also to show
   the equivalence of two defintions of expectation.
*)

From discprob.basic Require Import base order bigop_ext nify Series_Ext.
From discprob.prob Require Import countable rearrange.
From stdpp Require tactics.
Require Import Reals Fourier Lia Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq bigop fintype ssrnat choice.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.


Definition double_summable a :=
  ∃ (r: R), ∀ n, sum_n (λ j, sum_n (λ k, Rabs (a (j, k))) n) n <= r.

Lemma double_summable_mono_cond a:
  (∃ (r: R), ∃ N, ∀ n, n ≥ N → sum_n (λ j, sum_n (λ k, Rabs (a (j, k))) n) n <= r) →
  double_summable a.
Proof.
  intros (r&N&Hcond).
  exists r => n.
  destruct (le_ge_dec N n) as [Hle|Hge].
  - apply Hcond. lia.
  - transitivity (sum_n (λ j, sum_n (λ k, Rabs (a (j, k))) N) N).
    { clear Hcond.
      induction Hge; first reflexivity.
      etransitivity; first eapply IHHge.
      rewrite sum_Sn /plus//=.
      rewrite -[a in a <= _]Rplus_0_r.
      apply Rplus_le_compat.
      * rewrite ?sum_n_bigop.
        apply Rle_bigr => ??. apply sum_n_nonneg_terms_increasing; first lia.
        intros; apply Rle_ge, Rabs_pos.
      * apply sum_n_pos; eauto => ?.
        apply Rle_ge, Rabs_pos.
    }
    eauto.
Qed.

Lemma double_summable_ext a a':
  (∀ j k, Rabs (a (j, k)) = Rabs (a' (j, k))) →
  double_summable a → double_summable a'.
Proof.
  intros Hext (r&Hle).
  exists r => n. etransitivity; last (eapply (Hle n)).
  right.
  apply sum_n_ext => ?.
  apply sum_n_ext => ?.
  rewrite Hext. done.
Qed.

Lemma double_summable_abs a :
  double_summable a → double_summable (Rabs \o a).
Proof.
  apply double_summable_ext; eauto.
  intros. by rewrite Rabs_Rabsolu.
Qed.

Lemma double_summable_by_flip a:
  double_summable a →
  double_summable (λ xy, a (snd xy, fst xy)).
Proof.
  intros (r&Hle).
  exists r => n. rewrite sum_n_switch => //=.
Qed.

Lemma double_summable_flip a:
  double_summable (λ xy, a (snd xy, fst xy)) → double_summable a.
Proof.
  intros (r&Hle).
  exists r => n. rewrite sum_n_switch => //=.
Qed.

Lemma ex_series_rows_ds a:
  (∀ j, ex_series (λ k, Rabs (a (j, k)))) →
  ex_series (λ j, Series (λ k,  Rabs (a (j, k)))) →
  double_summable a.
Proof.
  intros Hrows Hex.
  destruct Hex as (r&Hseries).
  exists r => n.
  transitivity (sum_n (λ j, Series (λ k, Rabs (a (j, k)))) n).
  {  rewrite ?sum_n_bigop. apply Rle_bigr. intros (j&Hle) _.
     edestruct (Hrows j) as (v&Hrow). rewrite (is_series_unique _ _ Hrow).
     apply is_series_partial_pos; first (intros; apply Rle_ge, Rabs_pos); auto.
  }
  apply is_series_partial_pos; eauto.
  intros j. apply Rle_ge, Series_pos => k. apply Rle_ge, Rabs_pos.
Qed.

Lemma ex_series_columns_ds a:
  (∀ k, ex_series (λ j, Rabs (a (j, k)))) →
  ex_series (λ k, Series (λ j,  Rabs (a (j, k)))) →
  double_summable a.
Proof.
  intros. apply double_summable_flip. apply ex_series_rows_ds; eauto.
Qed.

Lemma ex_series_row a (DS: double_summable a) j:
  ex_series (λ k, Rabs (a (j, k))).
Proof.
  destruct DS as (M&HM).
  cut (∃ l: R, is_lim_seq (λ n, sum_n (λ k, Rabs (a (j, k))) n) l).
  { rewrite /ex_lim_seq/is_lim_seq/ex_series/is_series. rewrite //=.  }
  cut (∃ l: Rbar, is_lim_seq (λ n, sum_n (λ k, Rabs (a (j, k))) n) l).
  { intros (l&Hislim).
    assert (Rbar_le l M) as Hle.
    { eapply (is_lim_seq_le _ (λ n, M)); eauto; last by (apply is_lim_seq_const).
      intros n. etransitivity; last apply (HM (max j n)) => //=.
      rewrite ?sum_n_bigop.
      etransitivity; last first.
      { right. apply eq_bigr. intros; rewrite sum_n_bigop. done. }
      rewrite //=pair_big_dep//=/index_enum.
      refine (let σ' := (λ x, match x with
                                | Ordinal k Hle =>
                                  (@Ordinal (S (max j n)) j _, @ Ordinal (S (max j n)) k _)
                              end) : 'I_(S n) → 'I_(S (max j n)) * 'I_(S (max j n)) in _).
      Unshelve. all:swap 1 3.
      { abstract (intros; nify; lia). }
      { abstract (intros; nify; lia). }
      rewrite bigop_cond_non0 [a in _ <= a]bigop_cond_non0.
      eapply (sum_reidx_map_le _ _ _ _ σ').
      - intros (m&?) _. rewrite /σ' //=. right. repeat f_equal.
      - rewrite //=. intros (x&?) ? Hneq0; split; auto.
        rewrite -enumT mem_enum //=.
      - intros. apply Rle_ge, Rabs_pos.
      - rewrite -enumT. apply enum_uniq.
      - rewrite -enumT. apply: enum_uniq.
      - rewrite /σ'; intros (x&?) (y&?).
        rewrite //= => Hneq0. inversion 1. apply ord_inj => //=.
    }
    assert (Rbar_le 0 l) as Hge.
    {
      eapply (is_lim_seq_le (λ n, 0)); eauto; last by (apply is_lim_seq_const).
      intros n => /=. rewrite sum_n_bigop. apply Rle_big0 => ??. apply Rabs_pos.
    }
    destruct l as [l| |].
    * exists l. auto.
    * inversion Hle.
    * inversion Hge.
  }
  apply ex_lim_seq_incr.
  intros n. rewrite sum_Sn/plus//=. specialize (Rabs_pos (a (j, S n))). nra.
Qed.

Lemma ex_series_column a (DS: double_summable a) k:
  ex_series (λ j, Rabs (a (j, k))).
Proof.
  set (flip := λ (x : nat * nat), (snd x, fst x)).
  eapply ex_series_ext; last first.
  { eapply ex_series_row. apply double_summable_by_flip => //=. eapply DS. }
  intros n => //=.
Qed.

Module pre_converge.

Section covering1.

Variable (a: nat * nat → R).
Variable (σ: nat → nat * nat).

Variable (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n').
Variable (COV: ∀ n, a n <> 0 → ∃ m, σ m = n).

Lemma inj_nat_cover1:
  ∀ N, ∃ K, ∀ n, n ≤ N → (fst (σ n) ≤ K ∧ snd (σ n) ≤ K).
Proof.
  induction N.
  - exists (max (fst (σ O)) (snd (σ O))); intros n Hle; inversion Hle; split.
    * apply Max.le_max_l.
    * apply Max.le_max_r.
  - edestruct IHN as (K&HK).
    exists (max (max (fst (σ (S N))) (snd (σ (S N)))) K); intros n Hle; inversion Hle.
    * split.
      ** etransitivity; last apply Max.le_max_l. apply Max.le_max_l.
      ** etransitivity; last apply Max.le_max_l. apply Max.le_max_r.
    * split.
      ** etransitivity; last apply Max.le_max_r. edestruct HK; eauto.
      ** etransitivity; last apply Max.le_max_r. edestruct HK; eauto.
Qed.

Lemma inj_nat_cover2:
  ∀ K1 K2, ∃ N, ∀ l m, l ≤ K1 → m ≤ K2 →
 ( ∃ n, n ≤ N ∧ σ n = (l, m)) ∨ a (l, m) = 0.
Proof.
  induction K1.
  - induction K2.
    * destruct (Req_dec (a (O, O)) 0) as [|Hneq].
      ** exists O => l m. inversion 1; subst. inversion 1; subst.
         right. done.
      ** edestruct (COV _ Hneq) as (N&?).
         exists N => l m. inversion 1; subst. inversion 1; subst.
         left. exists N; split; auto.
    * destruct IHK2 as (N&HN).
      destruct (Req_dec (a (O, S K2)) 0) as [|Hneq].
      ** exists N => l m. inversion 1; subst. inversion 1; subst.
         *** right. done.
         *** eapply HN; auto.
      ** edestruct (COV _ Hneq) as (N'&?).
         exists (max N N') => l m. inversion 1; subst. inversion 1; subst.
         *** left. exists N'. split; auto. apply Max.le_max_r.
         *** edestruct (HN O m) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N; auto.
             apply Max.le_max_l.
  - induction K2.
    * destruct (IHK1 O) as (N&HN).
      destruct (Req_dec (a (S K1, O)) 0) as [|Hneq].
      ** exists N => l m. inversion 1; subst. inversion 1; subst.
         *** right. done.
         *** eapply HN; auto.
      ** edestruct (COV _ Hneq) as (N'&?).
         exists (max N N') => l m. inversion 1; subst; inversion 1; subst.
         *** left. exists N'. split; auto. apply Max.le_max_r.
         *** edestruct (HN l O) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N; auto.
             apply Max.le_max_l.
    * destruct (IHK1 (S K2)) as (N1&HN1).
      destruct IHK2 as (N2&HN2).
      destruct (Req_dec (a (S K1, S K2)) 0) as [|Hneq].
      ** exists (max N1 N2) => l m. inversion 1; subst; inversion 1; subst.
         *** right. done.
         *** edestruct (HN2 (S K1) m) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N2; auto.
             apply Max.le_max_r.
         *** edestruct (HN1 l (S K2)) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N1; auto.
             apply Max.le_max_l.
         *** edestruct (HN1 l m) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N1; auto.
             apply Max.le_max_l.
      ** edestruct (COV _ Hneq) as (N'&?).
         exists (max (max N1 N2) N') => l m. inversion 1; subst; inversion 1; subst.
         *** left.  exists N'; split; auto.
             apply Max.le_max_r.
         *** edestruct (HN2 (S K1) m) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N2; auto.
             etransitivity; first apply Max.le_max_r; apply Max.le_max_l.
         *** edestruct (HN1 l (S K2)) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N1; auto.
             etransitivity; first apply Max.le_max_l; apply Max.le_max_l.
         *** edestruct (HN1 l m) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N1; auto.
             etransitivity; first apply Max.le_max_l; apply Max.le_max_l.
Qed.

Lemma sum_n_m_cover_diff_double:
  ∀ N, ∃ K, ∀ l m, l ≥ K → m ≥ K →
  ∃ n, n ≥ N ∧ Rabs (sum_n (λ j, sum_n (λ k, a (j, k)) m) l - sum_n (a \o σ) N)
               <= sum_n_m (Rabs \o a \o σ) (S N) n.
Proof.
  intros N.
  edestruct (inj_nat_cover1 N) as (K&HK).
  exists K => l m Hl Hm.
  edestruct (inj_nat_cover2 l m) as (n&Hn).
  exists (max n N). repeat split.
  { intros; nify; lia. }
  transitivity (Rabs (\big[Rplus/0]_(S N <= i < S (Init.Nat.max n N) |
                                     ((σ i).1 <= l)%N && ((σ i).2 <= m)%N) (a (σ i))));
  last first.
  {
    rewrite sum_n_m_bigop. etransitivity; first apply Rabs_bigop_triang.
    rewrite //=. apply Rabs_bigop_filter. auto.
  }
  assert (sum_n (λ j, sum_n (λ k, a (j, k)) m) l =
          \big[Rplus/0]_(i < S (Init.Nat.max n N) |
                         leq (fst (σ i)) l && leq (snd (σ i)) m) a (σ i)) as Hleft.
  {
    etransitivity.
    { rewrite sum_n_bigop. eapply eq_bigr => ??. rewrite sum_n_bigop. done. }
      rewrite pair_big => //=. rewrite bigop_cond_non0 //=.
      rewrite /index_enum.
      symmetry.
      transitivity (\big[Rplus/0]_(i : {i : 'I_(S (max n N)) | leq (fst (σ i)) l &&
                                                            leq (snd (σ i)) m })
                     a (σ (sval i))).
      {
        rewrite bigop_cond_non0 [a in _ = a]bigop_cond_non0.
        symmetry; eapply (sum_reidx_map _ _ _ _ sval).
        - auto.
        - intros (i&Hpf) _ Hneq0; split.
          * rewrite -enumT mem_enum //.
          * rewrite //=. apply /andP; split; auto.
        - intros i _ Hbound Hfalse.
          move /andP in Hbound. destruct Hbound as (Hbound&Hneq0).
          move /andP in Hbound. destruct Hbound as (Hb1&Hb2).
          exfalso. apply Hfalse. rewrite //=.
          assert (is_true ((leq (σ i).1 l) && (leq (σ i).2 m))) as Hpf'.
          { rewrite //=; apply /andP; split; rewrite //= in Hb1 Hb2; destruct (σ n0); nify;
              lia. }
          exists (exist _ i Hpf'); repeat split.
            ** rewrite /index_enum //= -enumT mem_enum //=.
            ** rewrite //=.
        - rewrite /index_enum//= -enumT. apply enum_uniq.
        - rewrite /index_enum//= -enumT. apply enum_uniq.
        - intros (?&?) (?&?) ? Heq => //=.
          rewrite //= in Heq. subst. f_equal. apply bool_irrelevance.
      }
      refine (let σ' := (λ x, match x with
                              | exist o Hpf =>
                                (@Ordinal _ (fst (σ o)) _, @ Ordinal _ (snd (σ o)) _)
                              end) :
          { x: 'I_(S (max n N)) | leq (fst (σ x)) l && leq (snd (σ x)) m} → 'I_(S l) * 'I_(S m) in _).
      Unshelve. all:swap 1 3.
      { abstract (move: Hpf; move /andP => [? ?]; nify; lia). }
      { abstract (move: Hpf; move /andP => [? ?]; nify; lia). }
      rewrite [a in a = _]bigop_cond_non0.
      eapply (sum_reidx_map _ _ _ _ σ').
        - rewrite /σ'//=. intros (?&?) _ => //=. destruct (σ x) => //.
        - intros (i&Hpf) _ Hneq0; split.
          * rewrite -enumT mem_enum //.
          * rewrite //=. rewrite //= in Hneq0. destruct (σ i); auto.
        - rewrite //=. intros (l0, m0) _. rewrite //=. move /eqP. intros Hneq0 Hfalse.
          exfalso; apply Hfalse. edestruct (Hn l0 m0) as [(n0&Hle&Heq)|]; last by (exfalso; eauto).
          { clear. destruct l0 => //=. nify. lia. }
          { clear. destruct m0 => //=. nify. lia. }
          assert (Hpf1:  (n0 < S (max n N))%nat).
          { nify. specialize (Max.le_max_l n N); lia. }
          set (n0' := Ordinal Hpf1).
          assert (Hpf2: leq (fst (σ n0')) l && leq (snd (σ n0')) m).
          { apply /andP; rewrite Heq//=; destruct l0, m0 => //=; clear; split; nify. }
          exists (exist _ n0' Hpf2).
          repeat split => //=.
          * rewrite /index_enum//= -enumT mem_enum //.
          * rewrite Heq. apply /eqP. done.
          * rewrite /n0' //=; f_equal; apply ord_inj => //=; rewrite Heq; done.
        - rewrite /index_enum//= -enumT enum_uniq //.
        - rewrite /index_enum//= -enumT enum_uniq //.
        - rewrite /σ'//=. intros ?? Hneq0 Heq. cut (sval x = sval x').
          {  destruct x, x'. rewrite //=. intros; subst. f_equal. apply bool_irrelevance. }
          destruct x as ((?&?)&?), x' as ((?&?)&?) => //=.
          apply ord_inj. apply INJ => //=.
          ** apply /eqP; auto.
          ** rewrite //= in Heq. clear -Heq.
             inversion Heq as [[Heq1 Heq2]]. clear -Heq1 Heq2. destruct (σ m0), (σ m1); auto.
  }
  rewrite Hleft.
  assert (sum_n (a \o σ) N =
          \big[Rplus/0]_(i < S N |  ((σ i).1 <= l)%N && ((σ i).2 <= m)%N) a (σ i)) as Hright.
  {
    rewrite sum_n_bigop.
    rewrite bigop_cond_non0 [a in _ = a]bigop_cond_non0.
    eapply (sum_reidx_map _ _ _ _ id).
    * intros (x&Hlex) ? => //=.
    * intros (n'&Hle) ? Hneq0; split; auto. apply /andP; split; auto.
      rewrite //=. apply /andP; split.
      ** nify. transitivity K; auto. edestruct (HK n'); eauto. clear -Hle. nify. lia.
      ** nify. transitivity K; auto. edestruct (HK n'); eauto. clear -Hle. nify. lia.
    * intros i _. move /andP => [? Hneq0] => //= Hfalse.
      exfalso. apply Hfalse. exists i; split; auto.
      rewrite /index_enum -enumT mem_enum //.
    * rewrite /index_enum. rewrite -enumT. apply enum_uniq.
    * rewrite /index_enum. rewrite -enumT. apply enum_uniq.
    * intros (x&?) (y&?) => //=.
  }
  rewrite Hright.
  right.
  rewrite -(@big_mkord _ 0 Rplus (S (max n N)) (λ i, (leq (fst (σ i)) l) && (leq (snd (σ i)) m))
             (a \o σ)).
  assert (S N <= S (max n N))%nat as Hsplit by (nify; lia).
  rewrite (big_cat_nat _ _ _ _ Hsplit) //=.
  rewrite big_mkord.
  assert (∀ a b, a + b - a = b) as -> by (intros; field).
  done.
Qed.

Lemma is_lim_seq_sum_n (f: nat * nat → R) (h: nat → R) l:
  (∀ j, j ≤ l → is_lim_seq (λ m, sum_n (λ k, f (j, k)) m) (h j)) →
  is_lim_seq (λ m, sum_n (λ j, sum_n (λ k, f (j, k)) m) l) (sum_n h l).
Proof.
  intros Hh.
  induction l => //=.
  - intros. rewrite sum_O => //=. apply (is_lim_seq_ext (λ m, sum_n (λ k, f (O, k)) m)).
    * intros. rewrite sum_O. done.
    * by apply Hh.
  - rewrite sum_Sn.
    apply (is_lim_seq_ext (λ m, plus (sum_n (λ j, sum_n (λ k, f (j, k)) m) l)
                                     (sum_n (λ k, f (S l, k)) m))).
    * intros. by rewrite sum_Sn.
    * apply: is_lim_seq_plus; eauto.
      rewrite //=.
Qed.

Lemma is_lim_seq_fin_abs:
  ∀ (u : nat → R) (l : R), is_lim_seq u l → is_lim_seq (λ n : nat, Rabs (u n)) (Rabs l).
Proof.
  intros.
  assert (Rabs l = Rbar_abs l) as -> by auto.
  by apply (is_lim_seq_abs u (Finite l)).
Qed.

End covering1.

Section covering2.
Variable (a: nat * nat → R).
Variable (σ: nat → nat * nat).

Variable (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n').
Variable (COV: ∀ n, a n <> 0 → ∃ m, σ m = n).
Variable (EXS: ex_series (Rabs \o a \o σ)).

Lemma abs_inj: ∀ n n', Rabs (a (σ n)) <> 0 → σ n = σ n' → n = n'.
Proof.
  intros n n' Hneq0. apply INJ; auto.
  intros Heq. rewrite Heq Rabs_right in Hneq0; nra.
Qed.

Lemma abs_cov: ∀ n, Rabs (a n) <> 0 → ∃ m, σ m = n.
Proof.
  intros n Hneq0.
  eapply COV.
  intros Heq. rewrite Heq Rabs_right in Hneq0; nra.
Qed.

Lemma summable_implies_ds:
  double_summable a.
Proof.
  destruct (sum_n_m_cover_diff_double (λ x, Rabs (a x)) σ abs_inj abs_cov O) as (N&HN).
  apply double_summable_mono_cond.
  destruct EXS as (r&His).
  exists r, N. intros n Hge.
  destruct (HN n n) as (N'&Hge'&Hdiff); try lia.
  rewrite sum_O //= in Hdiff.
  setoid_rewrite <-Rabs_triang_inv in Hdiff.
  apply Rle_minus_l in Hdiff.
  rewrite Rplus_comm in Hdiff.
  rewrite /comp//= in Hdiff.

  replace (Rabs (Rabs (a (σ 0))) + sum_n_m (λ x : nat, Rabs (Rabs (a (σ x)))) 1 N')
          with (sum_n_m (λ x, Rabs (Rabs (a (σ x)))) 0 N') in Hdiff; last first.
  { rewrite (sum_Sn_m (λ x, Rabs (Rabs (a (σ x)))) 0 N') //=. }
  etransitivity.
  { eapply Rle_abs. }
  etransitivity; eauto.
  apply is_series_partial_pos.
  * intros; apply Rle_ge, Rabs_pos.
  * eapply is_series_ext; last eassumption.
    intros ? => //=. by rewrite Rabs_Rabsolu.
Qed.

Lemma series_double_covering:
  is_series (λ j, Series (λ k, a (j, k))) (Series (a \o σ)).
Proof.
  destruct (EXS) as (v&Habsconv).
  assert (ex_series (a \o σ)) as (v'&Hconv).
  { apply ex_series_Rabs.  eexists; eauto. }
  assert(Hnorm: ∀ eps : posreal, ∃ N K, ∀ l m, K ≤ l → K ≤ m →
         norm (sum_n (λ j, sum_n (λ k, a (j, k)) m) l - sum_n (a \o σ) N) < eps ∧
         norm (sum_n (a \o σ) N - v') < eps).
  {
    intros eps.

    edestruct (Cauchy_ex_series (Rabs \o a \o σ)) as (N0&IHN).
    { exists v; eauto. }
    assert (∃ N, ∀ N', N' ≥ N → norm (sum_n (a \o σ) N' - v') < eps) as (N2&HN2).
    { rewrite /is_series in Hconv.
      edestruct Hconv as (x&Hball). eapply locally_ball.
      exists x. eapply Hball.
    }
    set (N := max N0 N2).
    edestruct (sum_n_m_cover_diff_double _ _ INJ COV N) as (M&IHM2).
    exists N. exists M => m l Hm Hl.
    rewrite /norm//=/abs//=; repeat split; auto.
    - edestruct (IHM2 m l) as (n&?&Hle); auto.
      eapply Rle_lt_trans; first eapply Hle.
      rewrite /norm//=/abs//= in IHN.
      eapply Rle_lt_trans; first apply Rle_abs.
      assert (N0 <= N)%coq_nat.
      { rewrite /N. apply Max.le_max_l. }
      eapply IHN; auto. lia.
    - eapply HN2.
      rewrite /N. etransitivity; first apply Max.le_max_r. done.
  }
  assert(Hnorm': ∀ eps : posreal, ∃ N K, ∀ l, K ≤ l  →
         norm (sum_n (λ j, Series (λ k, a (j, k))) l - sum_n (a \o σ) N) < eps ∧
         norm (sum_n (a \o σ) N - v') < eps).
  {
    intros eps.
    edestruct (Hnorm (pos_div_2 eps)) as (N&K&Hdiff).
    exists N, K; split.
    - apply (Rle_lt_trans _ (pos_div_2 eps)); last by (destruct eps => //=; nra).
      transitivity (Lim_seq (λ k, norm (sum_n (λ j, sum_n (λ k, a (j, k)) k) l
                                        - sum_n (a \o σ) N))); last first.
      {
        eapply Rbar_le_fin; first by (destruct eps; rewrite //=; nra).
        rewrite -Lim_seq_const. apply Lim_seq_le_loc.
        exists K => m Hle. apply Rlt_le. eapply Hdiff; auto.
      }
      right. symmetry. apply Rbar_eq_fin.
      eapply is_lim_seq_unique.
      rewrite /norm//=/abs//=. apply is_lim_seq_fin_abs.
              eapply is_lim_seq_minus; [ | apply is_lim_seq_const | ].
       eapply (is_lim_seq_sum_n _ (λ j, Series (λ k, a (j, k)))).
       { intros ????.
         edestruct (Series_correct (λ k, a (j, k))) as (n&?).
         { apply ex_series_Rabs, ex_series_row, summable_implies_ds. }
         eauto. rewrite /filtermap. exists n. eauto.
       }
       rewrite //=.
    - edestruct Hdiff; eauto. transitivity (pos_div_2 eps); auto.
      destruct eps => //=; fourier.
  }
  assert (Series (a \o σ) = v') as -> by (eapply is_series_unique; eauto).
    rewrite /is_series. eapply filterlim_locally => eps.
    edestruct (Hnorm' (pos_div_2 eps)) as (N&M&?HNM).
    exists M => m Hle.
    specialize (HNM m Hle) as (?&?).
    rewrite /ball//=/AbsRing_ball//=/abs/AbsRing.abs//=/minus//=/plus//=/opp//=.
    specialize (norm_dist_mid (sum_n (λ j : nat, Series (λ k : nat, a (j, k))) m)
                              v' (sum_n (a \o σ) N)).
    rewrite {1}/norm//={1}/Rminus.
    intros Hle'. eapply Rle_lt_trans; first eapply Hle'.
    destruct eps as (eps&?).
    replace (eps) with (eps/2 + eps/2); last by field.
    apply Rplus_lt_compat; eauto.
Qed.

Lemma series_double_covering':
  is_series (a \o σ) (Series (λ j, Series (λ k, a (j, k)))).
Proof.
  specialize (is_series_unique _ _ (series_double_covering)) => ->.
  apply Series_correct, ex_series_Rabs, EXS.
Qed.

End covering2.
End pre_converge.

Section summable.

Variable (a: nat * nat → R).
Variable (σ: nat → nat * nat).

Variable (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n').
Variable (COV: ∀ n, a n <> 0 → ∃ m, σ m = n).

Variable (DS: double_summable a).

Lemma ex_series_ordering:
  ex_series (Rabs \o a \o σ).
Proof.
  destruct DS as (M&HM).
  cut (∃ l: R, is_lim_seq (λ n, sum_n (Rabs \o a \o σ) n) l).
  { rewrite /ex_lim_seq/is_lim_seq/ex_series/is_series. rewrite //=.  }
  cut (∃ l: Rbar, is_lim_seq (λ n, sum_n (Rabs \o a \o σ) n) l).
  { intros (l&Hislim).
    assert (Rbar_le l M) as Hle.
    { eapply (is_lim_seq_le _ (λ n, M)); eauto; last by (apply is_lim_seq_const).
      intros n. edestruct (pre_converge.inj_nat_cover1 σ n) as (K&HK).
      etransitivity; last apply (HM K) => //=.
      rewrite ?sum_n_bigop.
      etransitivity; last first.
      { right. apply eq_bigr. intros; rewrite sum_n_bigop. done. }
      rewrite //=pair_big_dep//=/index_enum.
      rewrite bigop_cond_non0 [a in _ <= a]bigop_cond_non0.
      set (σ' := λ x: 'I_(S n),
                      match x with
                        | Ordinal k Hle =>
                          let (pf1, pf2) := HK _ (le_S_n _ _ (proj1 (SSR_leq _ _) Hle)) in
                          (Ordinal (proj2 (SSR_leq _ _) (le_n_S _ _ pf1)),
                           Ordinal (proj2 (SSR_leq _ _) (le_n_S _ _ pf2)))
                      end).
      eapply (sum_reidx_map_le _ _ _ _ σ').
      - intros (m&?) _. rewrite /σ' //=. right. repeat f_equal.
        destruct (HK m _) => //=. destruct (σ m) => //=.
      - rewrite //=. intros (x&?) ? Hneq0; split; auto.
        * rewrite -enumT mem_enum //=.
        * move: Hneq0. rewrite /σ'. destruct (HK x _) => //=.
          destruct (σ x) => //=.
      - intros. apply Rle_ge, Rabs_pos.
      - rewrite -enumT. apply enum_uniq.
      - rewrite -enumT. apply: enum_uniq.
      - rewrite /σ'; intros (x&?) (y&?).
        destruct (HK x); destruct (HK y); rewrite //= => Hneq0. inversion 1. apply ord_inj => //=.
        eapply INJ; eauto.
        * move /eqP in Hneq0. intros Heq0. rewrite Heq0 in Hneq0.
          apply Hneq0. rewrite Rabs_R0. done.
        * destruct (σ x), (σ y); auto.
    }
    assert (Rbar_le 0 l) as Hge.
    {
      eapply (is_lim_seq_le (λ n, 0)); eauto; last by (apply is_lim_seq_const).
      intros n => /=. rewrite sum_n_bigop. apply Rle_big0 => ??. apply Rabs_pos.
    }
    destruct l as [l| |].
    * exists l. auto.
    * inversion Hle.
    * inversion Hge.
  }
  apply ex_lim_seq_incr.
  intros n. rewrite sum_Sn/plus//=. specialize (Rabs_pos (a (σ (S n)))). nra.
Qed.

Lemma series_double_covering:
  is_series (λ j, Series (λ k, a (j, k))) (Series (a \o σ)).
Proof.
  apply pre_converge.series_double_covering; eauto.
  apply ex_series_ordering.
Qed.

Lemma series_double_covering':
  is_series (a \o σ) (Series (λ j, Series (λ k, a (j, k)))).
Proof.
  specialize (is_series_unique _ _ (series_double_covering)) => ->.
  apply Series_correct, ex_series_Rabs, ex_series_ordering.
Qed.

End summable.

Lemma series_double_covering_Rabs a σ
      (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n')
      (COV: ∀ n, a n <> 0 → ∃ m, σ m = n)

      (DS: double_summable a):
  is_series (λ j, Series (λ k, Rabs (a (j, k)))) (Series (Rabs \o a \o σ)).
Proof.
  apply pre_converge.series_double_covering; eauto.
  - rewrite //=.  intros n n' Hneq0. eapply INJ; eauto. intros Heq0. rewrite Heq0 in Hneq0.
      rewrite Rabs_R0 in Hneq0. nra.
  - rewrite //=.  intros n Hneq0. eapply COV; eauto. intros Heq0. rewrite Heq0 in Hneq0.
      rewrite Rabs_R0 in Hneq0. nra.
  - apply ex_series_ordering.
    * intros. apply INJ; auto.
      intros HNEQ. apply H => //=. by rewrite HNEQ Rabs_R0.
    * by apply double_summable_abs.
Qed.

Lemma series_double_covering_Rabs' a σ
      (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n')
      (COV: ∀ n, a n <> 0 → ∃ m, σ m = n)

      (DS: double_summable a):

  is_series (Rabs \o a \o σ) (Series (λ j, Series (λ k, Rabs (a (j, k))))).
Proof.
  eapply series_double_covering'; eauto.
  - rewrite //=.  intros n n' Hneq0. eapply INJ; eauto. intros Heq0. rewrite Heq0 in Hneq0.
      rewrite Rabs_R0 in Hneq0. nra.
  - rewrite //=.  intros n Hneq0. eapply COV; eauto. intros Heq0. rewrite Heq0 in Hneq0.
      rewrite Rabs_R0 in Hneq0. nra.
  -  rewrite /double_summable//=. edestruct DS as (r&Hr).
     exists r. intros n. etransitivity; last (apply Hr).
     right. do 2 apply sum_n_ext => ?. rewrite Rabs_Rabsolu. done.
Qed.

Lemma sum_n_m_ext_const_zero: ∀ (G : AbelianGroup) (a : nat → G) (n m : nat),
    (∀ n, a n = zero) →
    sum_n_m a n m = zero.
Proof.
  intros G a n m Hz. rewrite (sum_n_m_ext _ (λ x, zero)) //.
  by rewrite sum_n_m_const_zero.
Qed.

Module double_swap.
Section double_swap.

Variable (a : nat * nat → R).
Variable (DS: double_summable a).

Definition σ := λ x, match @pickle_inv [countType of nat * nat] x with
            | Some (m, n) => (S m, S n)
            | None => (O, O)
            end.

Definition a' := λ mn, match mn with
                   | (S m', S n') => a (m', n')
                   | (_, _) => 0
                   end.

Lemma a_a'_Series_ext j: (λ j, Series (λ k, a (j, k))) j = (λ j, Series (λ k, a' (S j, S k))) j.
Proof. by apply Series_ext => //=. Qed.

Lemma a_a'_Series_ext_swap j:
  (λ k, Series (λ j, a (j, k))) j = (λ k, Series (λ j, a' (S j, S k))) j.
Proof. by apply Series_ext => //=. Qed.

Lemma a_a'_finite_sum n m:
  sum_n (λ j, sum_n (λ k, a (j, k)) m) n =
  sum_n (λ j, sum_n (λ k, a' (j, k)) (S m)) (S n).
Proof.
  symmetry. rewrite /sum_n.
  rewrite sum_Sn_m; last by (nify; lia).
  rewrite sum_n_m_ext_const_zero; last first.
  { intros [|] => //=.  }
  rewrite plus_zero_l.
  rewrite -sum_n_m_S.
  apply sum_n_m_ext.
  intros n'.
  rewrite sum_Sn_m; last by (nify; lia).
  rewrite plus_zero_l.
  rewrite -sum_n_m_S.
  done.
Qed.

Lemma a_a'_finite_sum_abs n m:
  sum_n (λ j, sum_n (λ k, Rabs (a (j, k))) m) n =
  sum_n (λ j, sum_n (λ k, Rabs (a' (j, k))) (S m)) (S n).
Proof.
  symmetry. rewrite /sum_n.
  rewrite sum_Sn_m; last by (nify; lia).
  rewrite sum_n_m_ext_const_zero; last first.
  { intros [|] => //=; rewrite Rabs_R0; done. }
  rewrite plus_zero_l.
  rewrite -sum_n_m_S.
  apply sum_n_m_ext.
  intros n'.
  rewrite sum_Sn_m; last by (nify; lia).
  rewrite Rabs_R0 plus_zero_l.
  rewrite -sum_n_m_S.
  done.
Qed.

Lemma ds_a': double_summable a'.
Proof.
  rewrite /double_summable. destruct DS as (r&HDS).
  exists r. intros n. destruct n.
  - rewrite ?sum_O => //=. rewrite Rabs_R0.
    etransitivity; last by (eapply (HDS O)).
    rewrite ?sum_O => //=. apply Rabs_pos.
  - rewrite -a_a'_finite_sum_abs. eauto.
Qed.

Lemma σ_inj:
  ∀ n n' : nat, a' (σ n) ≠ 0 → σ n = σ n' → n = n'.
Proof.
  intros n n'. rewrite /σ.
  specialize (@pickle_invK [countType of nat * nat] n).
  specialize (@pickle_invK [countType of nat * nat] n').
  destruct (pickle_inv) as [(?&?)|] => //=;
  destruct (pickle_inv) as [(?&?)|] => //=;
  intros <- ? ?. inversion 1. subst => //=.
Qed.

Lemma is_series_a'_σ_rows:
  is_series (λ j : nat, Series (λ k : nat, a' (j, k))) (Series (a' \o σ)).
Proof.
  eapply series_double_covering => //=.
  - apply σ_inj.
  - intros ([|m]&[|n]) ? => //=. exists (pickle (m, n)). rewrite /σ pickleK_inv.
    done.
  - apply ds_a'.
Qed.

Lemma is_series_a'_σ_columns:
  is_series (λ k : nat, Series (λ j : nat, a' (j, k))) (Series (a' \o σ)).
Proof.
  set (σflip := λ x, match @pickle_inv [countType of nat * nat] x with
                 | Some (m, n) => pickle (n, m)
                 | None =>  x
                 end).
  set (flip := λ (x : nat * nat), (snd x, fst x)).
  eapply (is_series_ext (λ k, Series (λ j: nat, (a' \o flip) (k, j)))).
  { intros n. apply Series_ext => //=. }
  cut (Series (a' \o σ) = Series ((a' \o flip) \o σ)).
  { intros ->. eapply series_double_covering => //=.
    - intros n n'. rewrite /σ.
      specialize (@pickle_invK [countType of nat * nat] n).
      specialize (@pickle_invK [countType of nat * nat] n').
    destruct (pickle_inv) as [(?&?)|] => //=;
    destruct (pickle_inv) as [(?&?)|] => //=;
    intros <- ? ?. inversion 1. subst => //=.
    - intros ([|m]&[|n]) ? => //=. exists (pickle (m, n)). rewrite /σ pickleK_inv.
    done.
    - apply double_summable_flip. eapply double_summable_ext; last by eapply ds_a'.
      rewrite //=.
  }
  assert (Series ((a' \o flip) \o σ) = Series ((a' \o σ) \o σflip)) as ->.
  {
    apply Series_ext => n. rewrite //=.
    rewrite /σflip/σ/a'.
    case_eq (@pickle_inv [countType of (nat * nat)] n).
    - intros (?&?) => //=. by rewrite pickleK_inv.
    - intros Hnone => //=.
      rewrite Hnone. done.
  }
  apply Series_rearrange_covering.
  - intros n n'. rewrite /σ/σflip/a' => //=.
    case_eq (@pickle_inv [countType of (nat * nat)] n).
    * intros (?&?) Heq. rewrite Heq => //=.
      rewrite pickleK_inv.
      case_eq (@pickle_inv [countType of (nat * nat)] n').
      ** intros (?&?) Heq'. rewrite Heq' => //=.
         intros ? Heqp.
         apply (f_equal (@pickle_inv [countType of (nat * nat)])) in Heqp.
         rewrite ?pickleK_inv in Heqp.
         inversion Heqp; subst.
         rewrite -Heq' in Heq.
         symmetry in Heq. eapply pickle_inv_some_inj in Heq; eauto.
      ** intros Hnone. rewrite Hnone => ? Hfalse. rewrite -Hfalse in Hnone.
         rewrite pickleK_inv in Hnone. congruence.
    * intros Hnone. rewrite ?Hnone.
      case_eq (@pickle_inv [countType of (nat * nat)] n').
      ** intros (?&?) Heq'. rewrite Heq' => //=.
      ** intros Hnone'. by rewrite Hnone' => ?? //=.
  - intros n. rewrite //=. rewrite /σ.
    case_eq (@pickle_inv [countType of (nat * nat)] n).
    * intros (m', n') Hinv ?. exists (pickle (n', m')).
      rewrite /σflip pickleK_inv.
      apply pickle_inv_some_inv; auto.
    * intros Hnone => //=.
  - apply ex_series_ordering.
    * apply σ_inj.
    * apply ds_a'.
Qed.

Lemma Series_a'_shift:
  (Series (λ n : nat, Series (λ j : nat, a' (j.+1, n.+1)))) =
  (Series (λ n : nat, Series (λ j : nat, a' (j, n)))).
Proof.
  symmetry. rewrite Series_incr_1; first rewrite Series_0.
  * rewrite Rplus_0_l. apply Series_ext.
    intros n'. rewrite Series_incr_1; first by (rewrite //=; nra).
    apply ex_series_Rabs. apply ex_series_column, ds_a'.
  * intros [|] => //=.
  * eexists; eapply is_series_a'_σ_columns.
Qed.

Lemma is_series_a'_shift v:
  is_series (λ j : nat, Series (λ n : nat, a' (j, n))) v →
  is_series (λ j : nat, Series (λ n : nat, a' (j.+1, n.+1))) v.
Proof.
  intros.
  apply (is_series_incr_1 (λ n, Series (λ k, a' (n, S k)))).
  rewrite (Series_0 (λ k, a' (O, S k))); last first.
  { destruct n => //=.  }
  rewrite plus_zero_r.
  eapply is_series_ext; last eauto.
  intros n. rewrite /=. rewrite Series_incr_1 => //=.
  * destruct n; nra.
  * apply ex_series_Rabs.
    apply (ex_series_row a'), ds_a'.
Qed.

Lemma ex_series_a'_shift:
  ex_series (λ j : nat, Series (λ n : nat, a' (j, n))) →
  ex_series (λ j : nat, Series (λ n : nat, a' (j.+1, n.+1))).
Proof.
  intros (v&?).
  exists v. eapply is_series_a'_shift.
  eauto.
Qed.

Lemma series_double_swap:
  is_series (λ j, Series (λ k, a (j, k))) (Series (λ k, Series (λ j, a (j, k)))).
Proof.
  eapply is_series_ext; first eapply a_a'_Series_ext.
  cut (is_series (λ j, Series (λ k, a' (j, k))) (Series (λ k : nat, Series (λ j : nat, a' (j, k)))));
    last first.
  {
    cut (Series (λ k, Series (λ j, a' (j, k))) = Series (a' \o σ)).
    { intros Heq. rewrite Heq. apply is_series_a'_σ_rows. }
    apply is_series_unique, is_series_a'_σ_columns.
  }
  intros Hseries.
  eapply is_series_ext.
  { symmetry.  apply a_a'_Series_ext. }
  erewrite (Series_ext); last first.
  { intros n. apply a_a'_Series_ext_swap. }
  rewrite Series_a'_shift. by apply is_series_a'_shift.
Qed.

End double_swap.
End double_swap.

Lemma series_double_swap a (DS: double_summable a):
  is_series (λ j, Series (λ k, a (j, k))) (Series (λ k, Series (λ j, a (j, k)))).
Proof. by apply double_swap.series_double_swap. Qed.

Lemma Series_double_swap a (DS: double_summable a):
  Series (λ j, Series (λ k, a (j, k))) =  (Series (λ k, Series (λ j, a (j, k)))).
Proof. apply is_series_unique. by apply series_double_swap. Qed.
