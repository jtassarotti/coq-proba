Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.basic Require Export base Series_Ext order bigop_ext sval Reals_ext.
From discprob.prob Require Import countable double rearrange.
From Coquelicot Require Export Rcomplements Rbar Series Lim_seq Hierarchy Markov.
From discprob.prob Require Import prob.

Section bind.
Variable (A : countType) (B: A → countType).
Variable (rI: R).
Variable (rb: R).
Variable (dist1: distrib A) (dist2: forall a, distrib (B a)).
Definition dep_prod_type := [countType of { a : A & B a } ].
Definition dep_prod_pmf (ab: dep_prod_type) := (dist1 (projT1 ab)) * (dist2 (projT1 ab) (projT2 ab)).

Section double.

Definition σprod :=
  λ n, match @pickle_inv [countType of dep_prod_type] n with
       | Some (existT a b) => (S (pickle a), S (pickle b))
       | None => (O, O)
       end.

Definition aprod :=
  λ mn, match mn with
        | (S m, S n) =>
          match (@pickle_inv A m) with
          | Some a =>
            match @pickle_inv (B a) n with
            |  Some b =>
                dep_prod_pmf (existT a b)
            | None => 0
            end
          | None => 0
          end
        | _ => 0
        end.


Lemma σprod_inj: ∀ n n', aprod (σprod n) <> 0 → σprod n = σprod n' → n = n'.
Proof.
  intros n n'. rewrite /σprod/aprod.
  case_eq (@pickle_inv [countType of dep_prod_type] n); last by nra.
  case_eq (@pickle_inv [countType of dep_prod_type] n'); last first.
  { intros Heq_none (a&b) Heq_some => //=. }
  intros (a'&b') Heq' (a&b) Heq Hneq0 => //=.
  inversion 1 as [[Hp1 Hp2]].
  assert (a = a').
  {
    apply (f_equal (@pickle_inv A)) in Hp1. rewrite ?pickleK_inv in Hp1.
    inversion Hp1; done.
  }
  subst.
  assert (b = b').
  {
    apply (f_equal (@pickle_inv (B a'))) in Hp2. rewrite ?pickleK_inv in Hp2.
    inversion Hp2; done.
  }
  subst.
  apply (f_equal (oapp (@pickle _) n)) in Heq.
  apply (f_equal (oapp (@pickle _) n')) in Heq'.
  rewrite ?pickle_invK //= in Heq Heq'. congruence.
Qed.

Lemma σprod_cov: ∀ n, aprod n <> 0 → ∃ m, σprod m = n.
Proof.
  intros (n1&n2).
  destruct n1, n2 => //=.
  rewrite /countable_sum.
  case_eq (@pickle_inv A n1) => //=; [].
  intros a Heq1.
  case_eq (@pickle_inv (B a) n2) => //=; [].
  intros b Heq2 => Hneq0.
  exists (@pickle [countType of dep_prod_type] (existT a b)).
  rewrite /σprod pickleK_inv. repeat f_equal.
  - apply (f_equal (oapp (@pickle _) n1)) in Heq1. rewrite pickle_invK //= in Heq1.
  - apply (f_equal (oapp (@pickle _) n2)) in Heq2. rewrite pickle_invK //= in Heq2.
Qed.

Lemma seriesC_partial_sum_bounded {X: countType} (h: X → R) r
      (Hseries: is_series (countable_sum h) r) (Hpos: ∀ x, h x >= 0) n:
         sum_n (countable_sum h) n <= r.
Proof.
  eapply is_lim_seq_incr_compare; eauto.
  { intros k. rewrite sum_Sn /plus//=. rewrite {3}/countable_sum//=.
    destruct (pickle_inv) as [a|] => //=; last nra.
    specialize (Hpos a). nra.
  }
Qed.

Section double1.
  (*
Variable (Hf_sum_bounded:
   ∀ i, val I i > 0 →
    ∃ (v: R), is_series (countable_sum (λ i', Rabs (h (ind (f (ind I i)) i')
                                               * val (f (ind I i)) i'))) v ∧
                                    v <= rb).
*)
Lemma aprod_double_summable: double_summable aprod.
Proof.
  exists 1 => n.
  destruct n.
  * rewrite ?sum_O //= Rabs_R0. nra.
  * transitivity
      (sum_n (λ j : nat, match j with
                         | O => 0
                         | S j => countable_sum (λ i, dist1 i) j
                         end) (S n)).
    { rewrite ?sum_n_bigop.
      rewrite -(big_mkord (λ x, true) (λ i, sum_n (λ k, Rabs (aprod (i, k))) (S n))).
      rewrite -(big_mkord (λ x, true)
                          (λ i, match i with
                                  O => 0
                                | S i => countable_sum (λ i, dist1 i) i
                                end)).
      apply Rle_bigr.

      intros i ?.
      rewrite //=. destruct i => //=.
      {
        rewrite ?sum_n_bigop.
        right.  rewrite Rabs_R0. rewrite big1 //=. }
      rewrite sum_nS /plus//=Rabs_R0 Rplus_0_l.
      rewrite /countable_sum//=.
      destruct (@pickle_inv (A) i) as [a|]; last first.
      { rewrite Rabs_R0. rewrite sum_n_const Rmult_0_r.
        rewrite /countable_sum//=.
        nra. }
      rewrite //=.
      transitivity (sum_n (λ n, dist1 a * countable_sum (λ i, dist2 a i) n) n).
      { right. apply sum_n_ext => k. rewrite /countable_sum//=.
        destruct pickle_inv => //=.
        * rewrite /dep_prod_pmf//= ?Rabs_mult. f_equal.
          ** apply Rabs_right, pmf_pos.
          ** apply Rabs_right, pmf_pos.
        * rewrite Rabs_R0; nra.
      }
      rewrite sum_n_mult_l /mult//=.
      destruct (pmf_pos dist1 a) as [Hgt|Heq0]; last first.
      { rewrite Heq0. nra. }
      transitivity (dist1 a * 1); last nra.
      apply Rmult_le_compat_l.
      { apply Rge_le, pmf_pos.  }
      eapply seriesC_partial_sum_bounded.
      * apply pmf_sum1.
      * intros; apply pmf_pos.
    }
    rewrite sum_nS /plus//= Rplus_0_l.
    eapply seriesC_partial_sum_bounded.
    { apply pmf_sum1. }
    { intros; apply pmf_pos. }
Qed.
End double1.

(* this is phrased in a funny way... *)
Section double2.

Lemma ex_series_prod_abs_row:
  ex_series (λ j, Series (λ k, Rabs (aprod (S j, S k)))).
Proof.
  rewrite -(ex_series_incr_1 (λ j, Series (λ k, Rabs (aprod (j, S k))))).
  eapply ex_series_ext; last first.
  { eexists;
      eapply (series_double_covering_Rabs _ _ σprod_inj σprod_cov aprod_double_summable); eauto. }
  intros n.
  rewrite [a in a = _]Series_incr_1; last first.
  {
    eapply ex_series_row, aprod_double_summable.
  }
  rewrite -[a in _ = a]Rplus_0_l; f_equal.
  rewrite //=. destruct n; auto using Rabs_R0.
Qed.

Lemma ex_series_prod_row:
  ex_series (λ j, Series (λ k, aprod (S j, S k))).
Proof.
  rewrite -(ex_series_incr_1 (λ j, Series (λ k, aprod (j, S k)))).
  eapply ex_series_ext; last first.
  { eexists;
      eapply (series_double_covering _ _ σprod_inj σprod_cov aprod_double_summable); eauto. }
  intros n.
  rewrite [a in a = _]Series_incr_1; last first.
  {
    eapply ex_series_Rabs. eapply ex_series_row, aprod_double_summable.
  }
  rewrite -[a in _ = a]Rplus_0_l; f_equal.
  rewrite //=. destruct n; auto.
Qed.

Lemma is_series_prod_row:
  is_series (countable_sum dep_prod_pmf)
            (Series (λ j, Series (λ k, aprod (S j, S k)))).
Proof.
  apply (is_series_ext (aprod \o σprod)).
  {
    intros n. rewrite /aprod/σprod/countable_sum/prod_pmf//=.
    destruct (pickle_inv _) as [s|] => //=.
    destruct s as (a0, b0) => //=.
    rewrite ?pickleK_inv //=.
  }
  eapply (is_series_chain _ _ _
                          (series_double_covering' _ _ σprod_inj σprod_cov aprod_double_summable)).
  cut (Series (λ j, Series (λ k, aprod (j, k))) =
      (Series (λ j : nat, Series (λ k : nat, aprod (S j, S k))))).
  {
    intros <-. apply Series_correct.
    eexists; eapply (series_double_covering _ _ σprod_inj σprod_cov aprod_double_summable); eauto.
  }
  rewrite Series_incr_1; last first.
  { eexists; eapply (series_double_covering _ _ σprod_inj σprod_cov aprod_double_summable); eauto. }
  rewrite {1}/aprod Series_0 // Rplus_0_l.
  apply Series_ext => n.
  rewrite Series_incr_1; last first.
  { apply ex_series_Rabs, ex_series_row, aprod_double_summable. }
  rewrite {1}/aprod Rplus_0_l => //=.
Qed.

Lemma Series_prod_row:
  Series (countable_sum (dep_prod_pmf)) =
  (Series (λ j, Series (λ k, aprod (S j, S k)))).
Proof.
  apply is_series_unique, is_series_prod_row.
Qed.

Lemma prod_series_ext:
  ∀ n : nat,
  (λ j : nat, Series (λ k : nat, aprod (S j, S k))) n =
  countable_sum
    (λ i : A,
     Series
       (countable_sum (λ i', dist2 i i')) *
     dist1 i) n.
Proof.
  intros n. rewrite /countable_sum//=/oapp.
  destruct (pickle_inv); last by apply Series_0.
  rewrite -Series_scal_r.
  eapply Series_ext => m.
  destruct pickle_inv => //=; last by nra.
  rewrite /dep_prod_pmf//=. nra.
Qed.

(*
Lemma prod_abs_series_ext:
  ∀ n : nat,
  (λ j : nat, Series (λ k : nat, Rabs (aprod (S j, S k)))) n =
  countable_sum
    (λ i : A,
     Series
       (countable_sum (λ i', Rabs (f (ind I i)) i')) *
     val I i) n.
Proof.
  intros n. rewrite /countable_sum//=/oapp.
  destruct (pickle_inv); last first.
  { setoid_rewrite Rabs_R0.
    by apply Series_0. }
  rewrite -Series_scal_r.
  eapply Series_ext => m.
  destruct pickle_inv => //=; last first.
  { rewrite Rabs_R0; nra. }
  rewrite /prod_pmf//= ?Rabs_mult ?Rabs_val. nra.
Qed.
*)

Lemma ex_series_pmf_abs_each_row i:
  ex_series (countable_sum (λ i', dist2 i i' * dist1 i)).
Proof.
  eapply (ex_series_ext (λ k, Rabs (aprod (S (pickle i), S k)))) ; last first.
  {
    rewrite -(ex_series_incr_1 (λ k, Rabs (aprod (S (pickle i), k)))).
    eapply (ex_series_row aprod), aprod_double_summable.
  }
  { intros n. rewrite //=. rewrite /countable_sum => //=.
    rewrite ?pickleK_inv. rewrite /oapp.
    destruct pickle_inv; rewrite /dep_prod_pmf //=.
    { rewrite Rabs_right; try nra.
      apply Rle_ge, Rmult_le_0_compat; apply Rge_le, pmf_pos. }
    { rewrite Rabs_R0 //. }
  }
Qed.

Lemma ex_series_pmf_abs_row:
   ex_series (countable_sum (λ i, Rabs (Series (countable_sum (λ i', dist2 i i'))) * dist1 i)).
Proof.
  apply: ex_series_le; last first.
  { apply ex_series_prod_abs_row. }
  intros n. rewrite norm_Rabs.
  rewrite Rabs_right; last first.
  { apply Rle_ge. rewrite /countable_sum/oapp.
    destruct pickle_inv; last reflexivity.
    apply Rmult_le_0_compat.
    * apply Rabs_pos.
    * apply Rge_le, pmf_pos.
  }
  rewrite /countable_sum//=/oapp.
  destruct (pickle_inv) as [i|]; last first.
  { rewrite Series_0; auto using Rabs_R0. nra. }
  replace (dist1 i) with (Rabs (dist1 i)); last by (auto using Rabs_right, pmf_pos).
   rewrite -Rabs_mult.
  rewrite -Series_scal_r.
  setoid_rewrite Series_Rabs.
  - right.
    eapply Series_ext => m.
    f_equal.
    destruct pickle_inv => //=; last by nra.
    rewrite /dep_prod_pmf//=. nra.
  - eapply ex_series_ext; last eapply (ex_series_pmf_abs_each_row i).
    intros n'. rewrite /countable_sum/oapp.
    destruct pickle_inv; last first.
    { rewrite Rmult_0_l Rabs_R0. done. }
    rewrite Rabs_right; try nra.
      apply Rle_ge, Rmult_le_0_compat; apply Rge_le, pmf_pos.
Qed.

Lemma ex_series_pmf_row:
   ex_series (countable_sum (λ i, (Series (countable_sum (λ i', dist2 i i'))) * dist1 i)).
Proof.
  eapply ex_series_ext; last first.
  { apply ex_series_prod_row. }
  { apply prod_series_ext. }
Qed.

Lemma prod_pmf_sum:
   is_series (countable_sum (dep_prod_pmf))
             (Series (countable_sum (λ i, (Series (countable_sum (λ i', dist2 i i'))) * dist1 i))).
Proof.
  intros.
  eapply (is_series_chain).
  { eapply is_series_prod_row. }
  apply Series_correct'; last first.
  { apply ex_series_prod_row. }
  { eapply Series_ext, prod_series_ext. }
Qed.

Lemma prod_pmf_pos_sum1 : is_series (countable_sum (dep_prod_pmf)) 1.
Proof.
  intros.
  eapply (is_series_chain).
  { eapply is_series_prod_row. }
  rewrite //=.
  eapply (is_series_ext (countable_sum (dist1))).
  { intros n.
    rewrite /countable_sum//=. destruct pickle_inv as [a|]; last first.
    { rewrite //=. by rewrite Series_0. }
    rewrite //=.
    rewrite -(Series_ext (λ k, dist1 a * countable_sum (λ i', dist2 a i') k)); last first.
    { intros m. rewrite /countable_sum. destruct (pickle_inv) => //=;
      rewrite /prod_pmf//=; nra. }
    rewrite Series_scal_l.
    destruct (pmf_pos dist1 a) as [Hgt|Heq0]; last first.
    { rewrite ?Heq0.  nra. }
    erewrite (is_series_unique _ 1); first nra.
    apply pmf_sum1.
  }
  apply pmf_sum1.
Qed.
End double2.


End double.

End bind.
