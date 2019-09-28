Require Export Reals Psatz Omega.
From discprob.prob Require Export prob countable stochastic_order markov double.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop seq.

(* TODO: can be generalized to consider case where the codomain of the rvar's are not all 
   the same *)
Definition independent {A} {B: eqType} {Ω: distrib A} (l: list (rvar Ω B)) :=
  ∀ lb, length lb = length l →
        pr Ω (λ a, fold_right andb true (map (λ Xb, (rvar_fun _ _ (fst Xb)) a == (snd Xb))
                                             (seq.zip l lb)))
        = fold_right Rmult 1 (map (λ Xb, pr_eq (fst Xb) (snd Xb)) (seq.zip l lb)).

Definition indep2 {A} {B1 B2: eqType} {Ω: distrib A}  (X: rvar Ω B1) (Y: rvar Ω B2) :=
  ∀ b1 b2, pr Ω (λ a, (X a == b1) && (Y a == b2)) =
           pr_eq X b1 * pr_eq Y b2.

Lemma indep2_pair_var {A} {B1 B2: eqType} {Ω: distrib A}  (X: rvar Ω B1) (Y: rvar Ω B2) :
  indep2 X Y →
  (∀ b1 b2, pr_eq (mkRvar Ω (λ a, (X a, Y a))) (b1, b2) =
           pr_eq X b1 * pr_eq Y b2).
Proof.
  rewrite /indep2. rewrite /pr_eq //=.
Qed.

Lemma zip_nil {S T: Type} (s: seq.seq T) : seq.zip (@nil S) s = nil.
Proof. destruct s => //=. Qed.

(*
Lemma independent_len {A} {B: eqType} {Ω: distrib A} (lX: list (rvar Ω B)) :
  (∀ lb, length lb = length lX →
         pr Ω (λ a, fold_right andb true (map (λ Xb, (rvar_fun _ _ (fst Xb)) a == (snd Xb))
                                              (seq.zip lX lb)))
         = fold_right Rmult 1 (map (λ Xb, pr_eq (fst Xb) (snd Xb)) (seq.zip lX lb))) →
  independent lX.
Proof.
  intros Hindep_len lb.
*)

Lemma independent_tl {A} {B: eqType} {Ω: distrib A} (X: rvar Ω B) (lX: list (rvar Ω B)):
  independent (X :: lX) → independent lX.
Proof.
  intros Hindep => bl.
  rewrite (pr_total_prob X).
  transitivity (Series (countable_sum (λ r : imgT X, pr_eq X (sval r) * 
      fold_right Rmult 1 (map (λ Xb : rvar Ω B * B, pr_eq Xb.1 Xb.2) (seq.zip lX bl))))).
  { apply Series_ext.
    intros n. rewrite /countable_sum; destruct (pickle_inv _) as [r|] => //=.
    rewrite (Hindep (sval r :: bl)) //=; f_equal; done.
  }
  rewrite SeriesC_scal_r.
  rewrite Series_pr_eq_over_range. nra.
Qed.

Lemma indep2_indendent {A} {B: eqType} {Ω: distrib A} (X Y: rvar Ω B) :
  indep2 X Y ↔ independent (X :: Y :: nil).
Proof.
  split.
  - intros Hindep2. rewrite /independent. intros lb.
    induction lb as [| b1 lb].
    { rewrite //=. }
    induction lb as [| b2 lb].
    { rewrite //=. } 
    rewrite //= zip_nil //=.
    intros Hlen.
    rewrite Rmult_1_r -Hindep2.
    apply pr_eq_pred => i. by rewrite /in_mem //= andbT.
  - intros Hindep. intros b1 b2. specialize (Hindep (b1 :: b2 :: nil)).
    rewrite //= Rmult_1_r in Hindep. rewrite -Hindep //.
    apply pr_eq_pred => i //=.
    by rewrite /in_mem //= andbT.
Qed.

Section joint_pr.

  Variable (A: countType).
  Variable (B1 B2: eqType).
  Variable (Ω: distrib A).
  Variable (X1 : rvar Ω B1).
  Variable (X2 : rvar Ω B2).
  Variable P: pred (B1).
  Variable Q: pred (B2).
  Variable (INDEP: indep2 X1 X2).

  Lemma imgT_pr1 ab:
    ab \in img (λ x : A, (X1 x, X2 x)) → (fst ab) \in img X1.
  Proof.
    rewrite /img//=. move /exCP => [x Heq].
    move /eqP in Heq. apply /exCP. exists x. apply /eqP. rewrite -Heq //=.
  Qed.

  Lemma imgT_pr2 ab:
    ab \in img (λ x : A, (X1 x, X2 x)) → (snd ab) \in img X2.
  Proof.
    rewrite /img//=. move /exCP => [x Heq].
    move /eqP in Heq. apply /exCP. exists x. apply /eqP. rewrite -Heq //=.
  Qed.

  Definition σprod : nat → nat * nat.
  Proof.
    intros n.
    destruct (pickle_inv [countType of (imgT (λ x, (X1 x, X2 x)))] n) as [ab|].
    - destruct ab as ((a,b)&Hpf).
      exact (S (@pickle [countType of imgT X1] (exist _ a (imgT_pr1 _ Hpf))),
             S (@pickle [countType of imgT X2] (exist _ b (imgT_pr2 _ Hpf)))).
    - exact (O, O).
  Defined.
        
  Definition aprod := 
    λ mn, match mn with
          | (S m, S n) => 
            match (pickle_inv [countType of (imgT X1)] m),
                  (pickle_inv [countType of (imgT X2)] n) with
            | Some a, Some b => 
              if P (sval a) && Q (sval b) then 
                pr_eq X1 (sval a) * pr_eq X2 (sval b)
              else
                0
            | _, _ => 0
          end
        | _ => 0
        end.

Lemma aprod_double_summable: double_summable aprod.
Proof.
  exists 1 => n. 
  rewrite /aprod.
  set (a' := (λ mn, 
              match mn with
              | (S m, S n) =>
                (countable_sum (λ a : imgT X1, if P (sval a) then pr_eq X1 (sval a) else 0)) m *
                (countable_sum (λ a : imgT X2, if Q (sval a) then pr_eq X2 (sval a) else 0)) n 
              | _ => 0
              end)). 
  transitivity (sum_n (λ j, sum_n (λ k, (a' (j, k))) n) n).
  { rewrite ?sum_n_bigop. rewrite /a'.
    eapply Rle_bigr. intros (i&?) ?. 
    rewrite ?sum_n_bigop. 
    eapply Rle_bigr. intros (j&?) ?. 
    destruct i, j => //=; rewrite ?Rabs_R0; try reflexivity.
    rewrite ?/countable_sum/prod_pmf.
    destruct pickle_inv, pickle_inv => //=; rewrite ?Rabs_R0 ?Rmult_0_l ?Rmult_0_r;
                                         try reflexivity; [].
    destruct (P _), (Q _) => //=; rewrite ?Rabs_R0 ?Rmult_0_r ?Rmult_0_l; try reflexivity.
    rewrite Rabs_mult ?Rabs_right; auto using pr_eq_ge_0. reflexivity.
  }
  rewrite /a'.
  destruct n.
  * rewrite ?sum_O //=. nra.
  * transitivity (sum_n (λ j, sum_n (λ k,
                countable_sum (λ a : imgT X1, if P (sval a) then pr_eq X1 (sval a) else 0) j *
                countable_sum (λ a : imgT X2, if Q (sval a) then pr_eq X2 (sval a) else 0) k) n) n).
    { 
      right.
      rewrite ?sum_n_bigop. 
      rewrite -(big_mkord (λ x, true) (λ i, sum_n (λ k, (a' (i, k))) (S n))).
      rewrite big_nat_recl; last done. 
      rewrite {1}/a' sum_n_const Rmult_0_r Rplus_0_l.

      transitivity (\big[Rplus/0]_(0 <= i < S n) \big[Rplus/0]_(0 <= i' < S n)
                     (λ k : nat, a' (S i, S k)) (i')).
      { eapply eq_bigr => i' ?.
        rewrite sum_n_bigop. 
        rewrite -(big_mkord (λ x, true) (λ i, (a' (_, i)))).
        rewrite big_nat_recl; last done. 
        rewrite {1}/a' Rplus_0_l.
        rewrite /a'//=.
      }
      rewrite big_mkord.
      apply eq_bigr => i ?.
      rewrite big_mkord.
      rewrite ?sum_n_bigop.
      apply eq_bigr => //=.
    }
    etransitivity.
    { right. eapply sum_n_ext => ?. rewrite sum_n_mult_l //=. }
    rewrite sum_n_mult_r.
    rewrite /mult //=.
    transitivity (1 * 1); last by nra.
    apply Rmult_le_compat.
    ** apply Rge_le, sum_n_partial_pos. intros n'.
       rewrite /countable_sum/oapp; destruct (pickle_inv _); try destruct (P _) => //=; try nra.
       apply pr_eq_ge_0.
    ** apply Rge_le, sum_n_partial_pos. intros n'.
       rewrite /countable_sum/oapp; destruct (pickle_inv _); try destruct (Q _) => //=; try nra.
       apply pr_eq_ge_0.
    ** apply pr_eq_sum_n_le_1.
    ** apply pr_eq_sum_n_le_1.
Qed.

Lemma σprod_inj: ∀ n n', aprod (σprod n) <> 0 → σprod n = σprod n' → n = n'.
Proof.
  intros n n'. rewrite /σprod/aprod.
  case_eq (pickle_inv [countType of imgT (λ x, (X1 x, X2 x))] n); last by nra.
  case_eq (pickle_inv [countType of imgT (λ x, (X1 x, X2 x))] n'); last first.
  { intros Heq_none ((a&b)&Hpf) Heq_some => //=. }
  intros ((a'&b')&Hpf') Heq' ((a&b)&Hpf) Heq Hneq0 => //=. 
  inversion 1 as [[Hp1 Hp2]].
  assert (a = a').
  { 
    apply (f_equal (pickle_inv [countType of imgT X1])) in Hp1. rewrite ?pickleK_inv in Hp1.
    inversion Hp1; done.
  }
  assert (b = b').
  { 
    apply (f_equal (pickle_inv [countType of imgT X2])) in Hp2. rewrite ?pickleK_inv in Hp2.
    inversion Hp2; done.
  }
  subst.
  apply (f_equal (oapp (@pickle _) n)) in Heq.
  apply (f_equal (oapp (@pickle _) n')) in Heq'.
  rewrite ?pickle_invK //= in Heq Heq'.
  rewrite Heq Heq'. f_equal.
  apply sval_inj_pred => //=.
Qed.

Lemma σprod_cov: ∀ n, aprod n <> 0 → ∃ m, σprod m = n.
Proof.
  intros (n1&n2).
  destruct n1, n2 => //=.
  rewrite /countable_sum.
  case_eq (pickle_inv [countType of imgT X1] n1); last first.
  { intros Heq. rewrite Heq => //=. }
  intros a Heq1. rewrite Heq1.
  case_eq (pickle_inv [countType of imgT X2] n2); last first.
  { intros Heq. rewrite Heq => //=. }
  intros b Heq2 => Hneq0.
  rewrite Heq2 in Hneq0.
  assert (Hgt0: pr_eq (mkRvar Ω (λ a, (X1 a, X2 a))) (sval a, sval b) > 0).
  { rewrite indep2_pair_var //.
    destruct (P _), (Q _); rewrite //= in Hneq0; try nra.
    specialize (pr_eq_ge_0 X1 (sval a)); intros [?|Heq0]; last first.
    { rewrite Heq0 in Hneq0. nra. }
    specialize (pr_eq_ge_0 X2 (sval b)); intros [?|Heq0'].
    * by apply Rmult_gt_0_compat.
    * rewrite Heq0' in Hneq0. nra.
  }
  apply pr_img in Hgt0.
  exists (@pickle [countType of (imgT (λ x, (X1 x, X2 x)))] (exist _ (sval a, sval b) Hgt0)).
  rewrite /σprod pickleK_inv. repeat f_equal.
  - apply (f_equal (oapp (@pickle _) n1)) in Heq1. rewrite pickle_invK //= in Heq1.
    rewrite Heq1. f_equal. apply sval_inj_pred => //=.
  - apply (f_equal (oapp (@pickle _) n2)) in Heq2. rewrite pickle_invK //= in Heq2.
    rewrite Heq2. f_equal. apply sval_inj_pred => //=.
Qed.

Lemma is_series_prod_row:
  is_series (countable_sum (λ ab : imgT (λ x, (X1 x, X2 x)),
                                   if P (fst (sval ab)) && Q (snd (sval ab)) then
                                    pr_eq X1 (fst (sval ab)) * pr_eq X2 (snd (sval ab))
                                  else
                                    0))
            (Series (λ j, Series (λ k, aprod (S j, S k)))).
Proof.
  apply (is_series_ext (aprod \o σprod)).
  { 
    intros n. rewrite /aprod/σprod/countable_sum/prod_pmf//=.
    destruct (pickle_inv _) as [s|] => //=.
    destruct s as ((a0, b0)&Hpf) => //=.
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
  Series (countable_sum (λ ab : imgT (λ x, (X1 x, X2 x)),
                                   if P (fst (sval ab)) && Q (snd (sval ab)) then
                                    pr_eq X1 (fst (sval ab)) * pr_eq X2 (snd (sval ab))
                                  else
                                    0)) =
  (Series (λ j, Series (λ k, aprod (S j, S k)))).
Proof.
  apply is_series_unique, is_series_prod_row.
Qed.

Lemma indep2_pred:
  pr Ω (λ a, P (X1 a) && Q (X2 a)) =
  pr Ω (λ a, P (X1 a)) * pr Ω (λ a, Q (X2 a)).
Proof.
  rewrite ?pr_pred_rvar.
  rewrite (pr_pred_rvar (mkRvar Ω (λ a, (X1 a, X2 a))) (λ ab, P (fst ab) && Q (snd ab))).
  transitivity ((Series (λ j, Series (λ k, aprod (S j, S k))))).
  { rewrite -Series_prod_row.  apply Series_ext => n.
    rewrite /countable_sum. destruct (pickle_inv _) as [[[a b] Heq]|] => //=.
    destruct (P _), (Q _) => //=.
    rewrite indep2_pair_var //.
  }
  etransitivity.
  {
    eapply Series_ext => n.
    rewrite /aprod.
    eapply (Series_ext _ (λ n', (match pickle_inv [countType of imgT X1] n with
                                 | Some a => if P (sval a) then (pr_eq X1 (sval a)) else 0
                                 | _ => 0
                             end) *
                            (match pickle_inv [countType of imgT X2] n' with
                                 | Some a => if Q (sval a) then (pr_eq X2 (sval a)) else 0
                                 | _ => 0
                             end))).
    intros n'.
    do 2 destruct pickle_inv => //=; try destruct (P _); try destruct (Q _); rewrite //=; nra.
  }
  rewrite -Series_scal_r.
  apply Series_ext => n.
  rewrite -Series_scal_l.
  apply Series_ext => n'.
  done.
Qed.
End joint_pr.

Section exp.
  Variable (A: countType).
  Variable (B1 B2: eqType).
  Variable (Ω: distrib A).
  Variable (X1 X2 : rrvar Ω).
  Variable (INDEP: indep2 X1 X2).
  Variable (EX1: ex_Ex X1).
  Variable (EX2: ex_Ex X2).

  Definition σprod_exp : nat → nat * nat.
  Proof.
    intros n.
    destruct (pickle_inv [countType of (imgT (λ x, (X1 x, X2 x)))] n) as [ab|].
    - destruct ab as ((a,b)&Hpf).
      exact (S (@pickle [countType of imgT X1] (exist _ a (imgT_pr1 _ _ _ _ _ _ _ Hpf))),
             S (@pickle [countType of imgT X2] (exist _ b (imgT_pr2 _ _ _ _ _ _ _ Hpf)))).
    - exact (O, O).
  Defined.
        
  Definition aprod_exp := 
    λ mn, match mn with
          | (S m, S n) => 
            match (pickle_inv [countType of (imgT X1)] m),
                  (pickle_inv [countType of (imgT X2)] n) with
            | Some a, Some b => 
                (sval a * pr_eq X1 (sval a)) * (sval b * pr_eq X2 (sval b))
            | _, _ => 0
          end
        | _ => 0
        end.

Lemma aprod_exp_double_summable: double_summable aprod_exp.
Proof.
  exists (Ex (rvar_comp X1 abs) * (Ex (rvar_comp X2 abs))) => n. 
  rewrite /aprod_exp.
  set (a' := (λ mn, 
              match mn with
              | (S m, S n) =>
                (countable_sum (λ a : imgT X1, Rabs (sval a) * pr_eq X1 (sval a))) m *
                (countable_sum (λ a : imgT X2, Rabs (sval a) * pr_eq X2 (sval a))) n
              | _ => 0
              end)). 
  transitivity (sum_n (λ j, sum_n (λ k, (a' (j, k))) n) n).
  { rewrite ?sum_n_bigop. rewrite /a'.
    eapply Rle_bigr. intros (i&?) ?. 
    rewrite ?sum_n_bigop. 
    eapply Rle_bigr. intros (j&?) ?. 
    destruct i, j => //=; rewrite ?Rabs_R0; try reflexivity.
    rewrite ?/countable_sum/prod_pmf.
    destruct pickle_inv, pickle_inv => //=; rewrite ?Rabs_R0 ?Rmult_0_l ?Rmult_0_r;
                                         try reflexivity; [].
    rewrite ?Rabs_mult -?Rmult_assoc.
    rewrite (Rabs_right (pr_eq _ _)); auto using pr_eq_ge_0.
    rewrite (Rabs_right (pr_eq _ _)); auto using pr_eq_ge_0.
    reflexivity.
  }
  rewrite /a'.
  destruct n.
  * rewrite ?sum_O //=; apply Rmult_le_0_compat; apply Ex_const_ge.
    ** by apply ex_Ex_comp_abs.
    ** intros => //=.
    ** by apply ex_Ex_comp_abs.
    ** intros => //=. 
  * transitivity (sum_n (λ j, sum_n (λ k,
                countable_sum (λ a : imgT X1, Rabs (sval a) * pr_eq X1 (sval a)) j *
                countable_sum (λ a : imgT X2, Rabs (sval a) * pr_eq X2 (sval a)) k) n) n).
    { 
      right.
      rewrite ?sum_n_bigop. 
      rewrite -(big_mkord (λ x, true) (λ i, sum_n (λ k, (a' (i, k))) (S n))).
      rewrite big_nat_recl; last done. 
      rewrite {1}/a' sum_n_const Rmult_0_r Rplus_0_l.

      transitivity (\big[Rplus/0]_(0 <= i < S n) \big[Rplus/0]_(0 <= i' < S n)
                     (λ k : nat, a' (S i, S k)) (i')).
      { eapply eq_bigr => i' ?.
        rewrite sum_n_bigop. 
        rewrite -(big_mkord (λ x, true) (λ i, (a' (_, i)))).
        rewrite big_nat_recl; last done. 
        rewrite {1}/a' Rplus_0_l.
        rewrite /a'//=.
      }
      rewrite big_mkord.
      apply eq_bigr => i ?.
      rewrite big_mkord.
      rewrite ?sum_n_bigop.
      apply eq_bigr => //=.
    }
    etransitivity.
    { right. eapply sum_n_ext => ?. rewrite sum_n_mult_l //=. }
    rewrite sum_n_mult_r.
    rewrite /mult //=.
    apply Rmult_le_compat.
    ** apply Rge_le, sum_n_partial_pos. intros n'.
       rewrite /countable_sum/oapp; destruct (pickle_inv _); try destruct (P _) => //=; try nra.
       apply Rle_ge, Rmult_le_0_compat.
       *** apply Rabs_pos. 
       *** apply Rge_le, pr_eq_ge_0.
    ** apply Rge_le, sum_n_partial_pos. intros n'.
       rewrite /countable_sum/oapp; destruct (pickle_inv _); try destruct (P _) => //=; try nra.
       apply Rle_ge, Rmult_le_0_compat.
       *** apply Rabs_pos. 
       *** apply Rge_le, pr_eq_ge_0.
    ** etransitivity; last apply Ex_sum_n_le_comp.
       { right.  apply sum_n_ext => n'. rewrite /countable_sum; destruct (pickle_inv _) => //=.
         rewrite /abs //=; field. }
       *** by apply ex_Ex_comp_abs.
       *** intros. rewrite /abs//=. apply Rle_ge, Rabs_pos.
    ** etransitivity; last apply Ex_sum_n_le_comp.
       { right.  apply sum_n_ext => n'. rewrite /countable_sum; destruct (pickle_inv _) => //=.
         rewrite /abs //=; field. }
       *** by apply ex_Ex_comp_abs.
       *** intros. rewrite /abs//=. apply Rle_ge, Rabs_pos.
Qed.

Lemma σprod_exp_inj: ∀ n n', aprod_exp (σprod_exp n) <> 0 → σprod_exp n = σprod_exp n' → n = n'.
Proof.
  intros n n'. rewrite /σprod_exp/aprod_exp.
  case_eq (pickle_inv [countType of imgT (λ x, (X1 x, X2 x))] n); last by nra.
  case_eq (pickle_inv [countType of imgT (λ x, (X1 x, X2 x))] n'); last first.
  { intros Heq_none ((a&b)&Hpf) Heq_some => //=. }
  intros ((a'&b')&Hpf') Heq' ((a&b)&Hpf) Heq Hneq0 => //=. 
  inversion 1 as [[Hp1 Hp2]].
  assert (a = a').
  { 
    apply (f_equal (pickle_inv [countType of imgT X1])) in Hp1. rewrite ?pickleK_inv in Hp1.
    inversion Hp1; done.
  }
  assert (b = b').
  { 
    apply (f_equal (pickle_inv [countType of imgT X2])) in Hp2. rewrite ?pickleK_inv in Hp2.
    inversion Hp2; done.
  }
  subst.
  apply (f_equal (oapp (@pickle _) n)) in Heq.
  apply (f_equal (oapp (@pickle _) n')) in Heq'.
  rewrite ?pickle_invK //= in Heq Heq'.
  rewrite Heq Heq'. f_equal.
  apply sval_inj_pred => //=.
Qed.

Lemma σprod_exp_cov: ∀ n, aprod_exp n <> 0 → ∃ m, σprod_exp m = n.
Proof.
  intros (n1&n2).
  destruct n1, n2 => //=.
  rewrite /countable_sum.
  case_eq (pickle_inv [countType of imgT X1] n1); last first.
  { intros Heq. rewrite Heq => //=. }
  intros a Heq1. rewrite Heq1.
  case_eq (pickle_inv [countType of imgT X2] n2); last first.
  { intros Heq. rewrite Heq => //=. }
  intros b Heq2 => Hneq0.
  rewrite Heq2 in Hneq0.
  assert (Hgt0: pr_eq (mkRvar Ω (λ a, (X1 a, X2 a))) (sval a, sval b) > 0).
  { rewrite indep2_pair_var //.
    specialize (pr_eq_ge_0 X1 (sval a)); intros [?|Heq0]; last first.
    { rewrite Heq0 in Hneq0. nra. }
    specialize (pr_eq_ge_0 X2 (sval b)); intros [?|Heq0'].
    * by apply Rmult_gt_0_compat.
    * rewrite Heq0' in Hneq0. nra.
  }
  apply pr_img in Hgt0.
  exists (@pickle [countType of (imgT (λ x, (X1 x, X2 x)))] (exist _ (sval a, sval b) Hgt0)).
  rewrite /σprod_exp pickleK_inv. repeat f_equal.
  - apply (f_equal (oapp (@pickle _) n1)) in Heq1. rewrite pickle_invK //= in Heq1.
    rewrite Heq1. f_equal. apply sval_inj_pred => //=.
  - apply (f_equal (oapp (@pickle _) n2)) in Heq2. rewrite pickle_invK //= in Heq2.
    rewrite Heq2. f_equal. apply sval_inj_pred => //=.
Qed.

Lemma is_series_prod_exp_row:
  is_series (countable_sum (λ ab : imgT (λ x, (X1 x, X2 x)),
                                   (pr_eq (mkRvar Ω (λ a, (X1 a, X2 a))) (sval ab)
                                          * (fst (sval ab) * snd (sval ab)))))
            (Series (λ j, Series (λ k, aprod_exp (S j, S k)))).
Proof.
  apply (is_series_ext (aprod_exp \o σprod_exp)).
  { 
    intros n. rewrite /aprod_exp/σprod_exp/countable_sum//=.
    destruct (pickle_inv _) as [s|] => //=.
    destruct s as ((a0, b0)&Hpf) => //=.
    rewrite ?pickleK_inv //=.
    rewrite indep2_pair_var //. field.
  }
  eapply (is_series_chain _ _ _
                          (series_double_covering' _ _ σprod_exp_inj σprod_exp_cov
                                                   aprod_exp_double_summable)).
  cut (Series (λ j, Series (λ k, aprod_exp (j, k))) =
      (Series (λ j : nat, Series (λ k : nat, aprod_exp (S j, S k))))).
  { 
    intros <-. apply Series_correct. 
    eexists; eapply (series_double_covering _ _ σprod_exp_inj σprod_exp_cov
                                            aprod_exp_double_summable); eauto.
  }
  rewrite Series_incr_1; last first.
  { eexists; eapply (series_double_covering _ _ σprod_exp_inj σprod_exp_cov
                                            aprod_exp_double_summable); eauto. }
  rewrite {1}/aprod_exp Series_0 // Rplus_0_l.
  apply Series_ext => n.
  rewrite Series_incr_1; last first.
  { apply ex_series_Rabs, ex_series_row, aprod_exp_double_summable. }
  rewrite {1}/aprod_exp Rplus_0_l => //=.
Qed.

Lemma is_series_prod_exp_row_abs:
  is_series (countable_sum (λ ab : imgT (λ x, (X1 x, X2 x)),
                                   (pr_eq (mkRvar Ω (λ a, (X1 a, X2 a))) (sval ab)
                                          * Rabs (fst (sval ab) * snd (sval ab)))))
            (Series (λ j, Series (λ k, Rabs (aprod_exp (S j, S k))))).
Proof.
  apply (is_series_ext (Rabs \o aprod_exp \o σprod_exp)).
  { 
    intros n. rewrite /aprod_exp/σprod_exp/countable_sum//=.
    destruct (pickle_inv _) as [s|] => //=; last by rewrite Rabs_R0.
    destruct s as ((a0, b0)&Hpf) => //=.
    rewrite ?pickleK_inv //=.
    rewrite indep2_pair_var //.
    rewrite ?Rabs_mult.
    rewrite (Rabs_right (pr_eq _ _)); auto using Rge_le, pr_eq_ge_0.
    rewrite (Rabs_right (pr_eq _ _)); auto using Rge_le, pr_eq_ge_0.
    field.
  }
  eapply (is_series_chain _ _ _
                          (series_double_covering_Rabs' _ _ σprod_exp_inj σprod_exp_cov
                                                   aprod_exp_double_summable)).
  cut (Series (λ j, Series (λ k, Rabs (aprod_exp (j, k)))) =
      (Series (λ j : nat, Series (λ k : nat, Rabs (aprod_exp (S j, S k)))))).
  { 
    intros <-. apply Series_correct. 
    eexists; eapply (series_double_covering_Rabs _ _ σprod_exp_inj σprod_exp_cov
                                            aprod_exp_double_summable); eauto.
  }
  rewrite Series_incr_1; last first.
  { eexists; eapply (series_double_covering_Rabs _ _ σprod_exp_inj σprod_exp_cov
                                            aprod_exp_double_summable); eauto. }
  rewrite {1}/aprod_exp Series_0 //; last by rewrite Rabs_R0.
  rewrite Rplus_0_l.
  apply Series_ext => n.
  rewrite Series_incr_1; last first.
  { apply ex_series_row, aprod_exp_double_summable. }
  rewrite {1}/aprod_exp Rabs_R0 Rplus_0_l => //=.
Qed.

Lemma Series_prod_exp_row:
  Series (countable_sum (λ ab : imgT (λ x, (X1 x, X2 x)),
                                   (pr_eq (mkRvar Ω (λ a, (X1 a, X2 a))) (sval ab)
                                          * (fst (sval ab) * snd (sval ab))))) =
  (Series (λ j, Series (λ k, aprod_exp (S j, S k)))).
Proof.
  apply is_series_unique, is_series_prod_exp_row.
Qed.

Lemma indep2_ex_Ex_prod :
  ex_Ex (mkRvar Ω (λ a, X1 a * X2 a)).
Proof.
  apply (ex_Ex_ext (rvar_comp (mkRvar Ω (λ a, (X1 a, X2 a))) (λ xy, fst xy * snd xy))); last by auto.
  apply ex_Ex_comp_by_alt.
  eexists. eapply is_series_prod_exp_row_abs.
Qed.

Lemma indep2_Ex_prod :
  Ex (mkRvar Ω (λ a, X1 a * X2 a)) = Ex X1 * Ex X2.
Proof.
  rewrite -(Ex_ext (rvar_comp (mkRvar Ω (λ a, (X1 a, X2 a))) (λ xy, fst xy * snd xy))); last by auto.
  - rewrite Ex_comp_by_alt; last by (eexists; eapply is_series_prod_exp_row_abs).
    rewrite Series_prod_exp_row.
    etransitivity.
    {
    eapply Series_ext => n.
    eapply (Series_ext _ (λ n', (match pickle_inv [countType of imgT X1] n with
                                 | Some a => pr_eq X1 (sval a) * (sval a)
                                 | _ => 0
                             end) *
                            (match pickle_inv [countType of imgT X2] n' with
                                 | Some a => pr_eq X2 (sval a) * (sval a)
                                 | _ => 0
                             end))).
    intros n'.
    rewrite /aprod_exp.
    do 2 destruct pickle_inv => //=; nra.
    }
    rewrite -Series_scal_r.
    apply Series_ext => n.
    rewrite -Series_scal_l.
    apply Series_ext => n'.
    done.
  - apply indep2_ex_Ex_prod.
Qed.
End exp.
 
Arguments indep2_pred {_ _ _ _}.
Arguments indep2_ex_Ex_prod {_ _}.
Arguments indep2_Ex_prod {_ _}.

Lemma indep2_fn {A} {B1 B2 C1 C2: eqType} {Ω: distrib A}  (X: rvar Ω B1) (Y: rvar Ω B2)
           (f1: B1 → C1) (f2: B2 → C2):
  indep2 X Y → indep2 (rvar_comp X f1) (rvar_comp Y f2).
Proof.
  intros Hindep b1 b2.
  rewrite (indep2_pred X Y (λ x, f1 x == b1) (λ x, f2 x == b2)) //.
Qed.


Lemma rvar_list_eq_foldr {A} {B: eqType} {Ω: distrib A}  (lX: list (rvar Ω B)) bl i:
  length bl = length lX →
  ((rvar_list lX) i == bl
  ↔ fold_right andb true (List.map (λ Xb : rvar Ω B * B, Xb.1 i == Xb.2) (zip lX bl))).
Proof.
  intros Hlen.
  split.
  - move /eqP => <-. 
    clear. induction lX => //=; apply /andP; split; auto. 
  - clear -Hlen. revert bl Hlen. induction lX => bl Hlen //=.
    * destruct bl => //=.
    * destruct bl as [|b bl] => //=.
      move /andP => [Heq Hrec]. move /eqP in Heq. rewrite Heq.
      apply /eqP. f_equal. 
      apply /eqP. apply IHlX; eauto.
Qed.

Lemma rvar_list_eq_short {A} {B: eqType} {Ω: distrib A}  (lX: list (rvar Ω B)) bl:
  length bl ≠ length lX →
  ∀ i, ((rvar_list lX) i == bl) = false.
Proof.
  intros Hlen => i.
  apply /eqP => Heq.
  apply (f_equal (@length B)) in Heq.
  rewrite /rvar_list //= in Heq. rewrite map_length in Heq.
  congruence.
Qed.

Lemma independent_rvar_list {A} {B: eqType} {Ω: distrib A}  (lX: list (rvar Ω B)) :
  independent lX →
  ∀ bl, length bl = length lX →
  pr_eq (rvar_list lX) bl = 
  fold_right Rmult 1 (map (λ Xb, pr_eq (fst Xb) (snd Xb)) (seq.zip lX bl)).
Proof.
  rewrite /independent. intros Hindep bl Hlen.
  rewrite -(Hindep bl) //.
  rewrite /pr_eq. apply pr_eq_pred' => i.
  by apply rvar_list_eq_foldr.
Qed.

Lemma independent_indep2_tl {A} {B: eqType} {Ω: distrib A}  (X: rvar Ω B) (lX: list (rvar Ω B)) :
  independent (X :: lX) →
  indep2 X (rvar_list lX).
Proof.
  intros Hindep. rewrite /indep2 => b bl.
  rewrite //= in Hindep.
  destruct (eq_nat_dec (length bl) (length lX)) as [Heq|Hneq].
  - rewrite independent_rvar_list //; eauto using independent_tl.
    specialize (Hindep (b :: bl)).
    rewrite //= in Hindep. rewrite -Hindep; last by (f_equal; done).
    apply pr_eq_pred' => i.
    destruct (X i == b); last done.
    rewrite andTb. by apply rvar_list_eq_foldr.
  - rewrite /pr_eq.
    rewrite (pr_eq_pred' Ω _ xpred0); last first.
    { intros i. rewrite rvar_list_eq_short // andbF //=. }
    rewrite [a in _ = _ * a](pr_eq_pred' Ω _ xpred0); last first.
    { intros i. rewrite rvar_list_eq_short // andbF //=. }
    rewrite pr_xpred0; field.
Qed.

Lemma independent_nil {A} {B} {Ω: distrib A} :
  @independent A B Ω [::].
Proof.
  intros b. destruct b => //= ?. apply pr_xpredT.
Qed.

Lemma independent_singleton {A} {B} {Ω: distrib A} X:
  @independent A B Ω [::X].
Proof.
  intros b.
  destruct b => //=.
  destruct b => //= _. rewrite Rmult_1_r;
  rewrite /pr_eq; apply pr_eq_pred => ?; by rewrite /in_mem //= andbT.
Qed.

Lemma indep2_independent_cons {A} {B: eqType} {Ω: distrib A}  (X: rvar Ω B) (lX: list (rvar Ω B)) :
  indep2 X (rvar_list lX) →
  independent lX →
  independent (X :: lX).
Proof.
  induction lX => //=.
  - intros; apply independent_singleton. 
  - intros Hindep2 Hindep_tl.
    intros lb. destruct lb => //=. destruct lb; first by done.
    intros Hlen.
    rewrite -independent_rvar_list //; last first.
    { rewrite //=. rewrite  //= in Hlen. omega. }
    rewrite -Hindep2.
    apply pr_eq_pred' => i.
    rewrite //= in Hlen.
    split; move /andP => [? ?]; apply /andP; split; auto;
                           apply rvar_list_eq_foldr => //=; omega.
Qed.

Lemma rvar_list_comp_ext {A} {B C: eqType} {Ω: distrib A} (lX: list (rvar Ω B)) (f: B → C) :
  (rvar_comp (rvar_list lX) (map f)) =1 (rvar_list (map (rvar_comp^~f) lX)).
Proof.
  induction lX => i //=.
  f_equal. specialize (IHlX i). rewrite //= in IHlX. 
Qed.

Lemma indep2_ext {A} {B C: eqType} {Ω: distrib A} (X X': rvar Ω B) (Y Y': rvar Ω C):
  X =1 X' →
  Y =1 Y' →
  indep2 X Y →
  indep2 X' Y'.
Proof.
  intros HextX HextY Hindep b c.
  specialize (Hindep b c).
  rewrite -(pr_eq_rvar_ext _ _ _ HextX).
  rewrite -(pr_eq_rvar_ext _ _ _ HextY).
  rewrite -Hindep. apply pr_eq_pred' => i. rewrite HextX HextY. done.
Qed.

Lemma indep_fn {A} {B C: eqType} {Ω: distrib A} (lX: list (rvar Ω B)) (f: B → C):
  independent lX → independent (map (rvar_comp^~ f) lX).
Proof.
  intros Hindep.
  induction lX as [| X l].
  - apply independent_nil.
  - rewrite map_cons. apply indep2_independent_cons.
    * eapply indep2_ext.
      ** intros i. reflexivity. 
      ** apply rvar_list_comp_ext.
      ** apply indep2_fn. by apply independent_indep2_tl.
    * apply IHl. eapply independent_tl; eauto.
Qed.

Lemma ex_Ex_indep_prod_list {A} {Ω: distrib A} (l: list (rrvar Ω)) :
  independent l →
  (∀ X, In X l → ex_Ex X) →
  ex_Ex (prod_list_rrvar l).
Proof.
  induction l as [| X l].
  - rewrite /prod_list_rrvar//= => ??; apply ex_Ex_const.
  - rewrite //= => Hindep Hex.
    eapply (ex_Ex_ext (mkRvar Ω (λ a, X a * prod_list_rrvar l a))).
    * apply indep2_ex_Ex_prod.
      ** rewrite prod_list_rrvar_alt.
         apply: (indep2_fn _ _ id (fold_right Rmult 1)).
         by apply independent_indep2_tl.
      ** apply Hex. by left.
      ** eapply IHl.
         *** eapply independent_tl; eauto.
         *** intros. eapply Hex. by right.
    * rewrite //=.
Qed.

Lemma Ex_indep_prod_list {A} {Ω: distrib A} (l: list (rrvar Ω)) :
  independent l →
  (∀ X, In X l → ex_Ex X) →
  Ex (prod_list_rrvar l) = fold_right Rmult 1 (map Ex l).
Proof.
  induction l as [| X l].
  - rewrite /prod_list_rrvar//= => ??; apply Ex_const.
  - rewrite //= => Hindep Hex.
    rewrite (Ex_ext _ (mkRvar Ω (λ a, X a * prod_list_rrvar l a))).
    * rewrite indep2_Ex_prod //.
      ** rewrite IHl //.
         *** eapply independent_tl; eauto.
         *** intros; eapply Hex; by right. 
      ** rewrite prod_list_rrvar_alt.
         apply: (indep2_fn _ _ id (fold_right Rmult 1)).
         by apply independent_indep2_tl.
      **  eapply Hex; by left.
      ** eapply ex_Ex_indep_prod_list; eauto.
         eapply independent_tl; eauto.
    * eapply ex_Ex_indep_prod_list; eauto.
    * rewrite //=.
Qed.