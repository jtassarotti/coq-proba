From discprob.basic Require Import base order nify seq_ext.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad monad_hoare counter.
From discprob.rec Require Import rec_convert counter_rec.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier Psatz Omega.

Definition h (n: nat) := 
  match n with
    | O => mret O
    | S O => mret O
    | S (S n') =>
      surv ← counter.binomial (S n');
      mret (sval surv)
  end.
Definition rsize (n: nat) := INR n.

Definition m x :=
  match (Rlt_dec x 2) with
  | left _ => 0
  | _ => x * (1 / 2)
  end.

Lemma Rplus_1_m x: x >= 2 → m (x + 1) = m x + (1 / 2).
Proof.
  rewrite /m. do 2 destruct (Rlt_dec) => //=; try nra. 
Qed.

Lemma Ex_h n:
  Ex (rvar_comp (rvar_of_ldist (h n)) rsize) <= m (rsize n).
Proof.
  induction n as [n IH] using (well_founded_induction lt_wf).
  destruct n as [| n]; last destruct n as [| n].
  - rewrite Ex_fin_comp. 
    rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ a)).
    rewrite img_rvar_of_ldist//=/img/undup//= !big_cons ?big_nil.
    rewrite pr_mret_simpl //= /m. destruct (Rlt_dec) => //; nra.
  - rewrite Ex_fin_comp. 
    rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ a)).
    rewrite img_rvar_of_ldist//=/img/undup//= !big_cons ?big_nil.
    rewrite pr_mret_simpl //= /m. destruct (Rlt_dec) => //; nra.
  - rewrite /h binomial_unfold. 
    rewrite -Ex_mbind_mret ?ldist_assoc.
    rewrite Ex_mbind_ldist2 ?big_cons ?big_nil Rplus_0_r /snd.
    rewrite pr_flip_true pr_flip_false.
    rewrite ?ldist_fmap_bind. simpl sval. 
    rewrite -ldist_assoc ldist_fmap_bind.
    rewrite -ldist_assoc ldist_fmap_bind.
    rewrite /rsize S_INR.
    rewrite (ldist_bind_ext (counter.binomial n) _ (λ x, mret (1 + INR (sval x)))); last first.
    { intros. rewrite S_INR. f_equal. rewrite Rplus_comm. done. }
    rewrite -(ldist_fmap_bind _ _ (λ n, mret (1 + n))).
    rewrite Ex_mbind_mret.
    rewrite Ex_fin_plus_l.
    destruct n as [| n].
    * rewrite binomial_unfold ldist_left_id /sval Ex_mret_simpl.
      replace (INR 0) with 0 by auto.
      replace (INR 1) with 1 by auto.
      rewrite /m. destruct Rlt_dec => //=; nra.
    * assert (S (S n) < S (S (S n)))%coq_nat as Hbound by auto. 
      specialize (IH (S (S n)) Hbound). rewrite /h in IH.
      rewrite Rplus_1_m; last first.
      { replace 2 with (INR 2) by auto. apply Rle_ge, le_INR. omega. }
      rewrite /rsize in IH.
      rewrite -Ex_mbind_mret in IH.
      rewrite ldist_fmap_bind in IH. rewrite Rmult_plus_distr_l Rplus_assoc Rmult_1_r.
      rewrite (Rplus_comm ( 1 / 2)).
      rewrite -Rmult_plus_distr_l.
      rewrite -(double (Ex _)). rewrite -Rmult_assoc. replace (1 /2 * 2) with 1 by nra.
      rewrite Rmult_1_l. apply Rplus_le_compat; auto. nra.
Qed.

Definition shift x :=
  match x with
    | O => 0
    | S n' => INR n'
  end.
Definition T := λ x, rvar_comp (rvar_of_ldist (approx_incrn x O)) shift.
  Definition a x := 
    match Rle_dec x 1 with
      | left _ => 0
      | _ =>
        match Rlt_dec x 2 with
        | left _ => (x - 1)
        | _ => 1
        end
    end.
Definition h' x := rvar_of_ldist (h x).

Lemma Trec: 
  ∀ x r, (λ x, true) x → pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h' x)) 
                ((pr_eq (h' x) (sval x')) * pr_gt (rvar_comp (T (sval x')) (λ x, x)) (r - a (rsize x))).
Proof.
  eapply eq_dist_unary_rec_gt; auto. 
  { rewrite /T. intros. eapply eq_dist_comp. apply eq_dist_approx_incrn_bulk. }
  intros n.
  induction n as [| n].
  - intros. rewrite approx_incr'_bulk_unfold -pr_gt_mbind_mret ldist_left_id pr_gt_mret_simpl. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' 0) x' *
      pr_gt (rvar_comp (rvar_comp (rvar_of_ldist (approx_incr'_bulk x')) shift) id)
            (r - a (rsize 0))))).
    rewrite img_rvar_of_ldist /h. 
    rewrite big_cons big_nil Rplus_0_r.
    rewrite /a/rsize/size. 
    replace (INR 0) with 0 by auto.
    destruct (Rlt_dec); last nra.
    rewrite /snd.
    rewrite rvar_comp_comp //=.
    rewrite -(pr_gt_mbind_mret (approx_incr'_bulk 0) (id \o shift)).
    rewrite pr_gt_mbind_ldist2 ?big_cons ?big_nil Rplus_0_r //=.
    rewrite !pr_mret_simpl !pr_gt_mret_simpl eq_refl /id //=. 
    destruct (Rle_dec); last nra.
    rewrite Rminus_0_r. destruct Rgt_dec => //=; nra.
  - intros. destruct n as [| n].
    {
    rewrite approx_incr'_bulk_unfold -?pr_gt_mbind_mret ldist_left_id pr_gt_mret_simpl. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' 0) x' *
      pr_gt (rvar_comp (rvar_comp (rvar_of_ldist (approx_incr'_bulk x')) shift) id)
            (r - a (rsize 1))))).
    rewrite img_rvar_of_ldist /h. 
    rewrite big_cons big_nil Rplus_0_r.
    rewrite /a/rsize/size. 
    replace (INR 1) with 1 by auto.
    destruct (Rle_dec); last nra.
    rewrite -(pr_gt_mbind_mret (approx_incr'_bulk 0) (id \o shift)).
    rewrite pr_gt_mbind_ldist2 ?big_cons ?big_nil Rplus_0_r.
    rewrite !pr_mret_simpl !pr_gt_mret_simpl eq_refl /id.
    rewrite //=. destruct (Rgt_dec) => //=; destruct (Rgt_dec) => //=; try nra.
    }
    rewrite approx_incr'_bulk_unfold.

    transitivity
  (pr_gt (rvar_comp (rvar_of_ldist
         (surv ← h (S (S n)); approx_incr'_bulk surv))
          (λ x, 1 + (shift x))) r); last first.
    {    
      rewrite /h'. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' _) x' *
      pr_gt (rvar_comp (rvar_comp (rvar_of_ldist (approx_incr'_bulk x')) shift) id)
            (r - a (rsize _))))).
    rewrite -pr_gt_mbind_mret ldist_assoc. rewrite pr_gt_mbind_ldist2.
    rewrite img_rvar_of_ldist. 
      * right.  eapply eq_bigr. intros k ?.
        f_equal. 
        rewrite pr_gt_mbind_mret. 
        rewrite rvar_comp_comp.
          rewrite {1}/pr_gt {1}[a in _ = a]/pr_gt.
          rewrite ?pr_gt_alt_comp /id. eapply eq_bigr => x ?.
          rewrite //=.
          eapply @if_sumbool_case_match. rewrite ?plus_INR ?Rmax_INR /rsize/a.
          specialize (S_INR n) => /= => ->. 
          destruct (Rlt_dec) as [Hlt0|Hnlt].
          { clear -Hlt0. specialize (pos_INR n). rewrite //=. intros.  exfalso; nra. }
          destruct (Rle_dec); first nra.
          nra.
    }
    rewrite /h.
    rewrite -?pr_gt_mbind_mret.
    rewrite ?ldist_assoc.
    eapply le_dist_ldist_bind_ext => a.
    eapply le_dist_ldist_bind_ext => pv.
    rewrite ldist_left_id.
    rewrite ldist_fmap_bind.
    intros k.
    eapply le_dist_ldist_bind_ext => n'; clear k.
    intros k. rewrite ?pr_gt_mret_simpl.
    do 2 destruct (Rgt_dec) => //=; try nra.
    assert (1 + shift n' >= shift (S n')).
    { clear. induction n'; first (rewrite //=; nra). 
      rewrite /shift S_INR. nra.
    }
    nra.
Qed.

Definition k := -/ ln(10/17).

Theorem bound x w:
    rsize x > 1 →  
    pr_gt (T x) ((k * ln (rsize x) + 1) + INR w)
       ≤ (10/17)^w.
Proof.
  specialize (counter_rec.recurrence_counter.counter_bound _ _ _ _ T h' (λ x, true)).
  rewrite /size/rsize => Hrec. eapply Hrec; clear.
  - auto.
  - intros l ?. rewrite //=.
    rewrite /counter_rec.recurrence_counter.size //= => Hgt. 
    cut (∀ n, INR (((rvar_of_ldist (h l) n))) <= INR l - 1); first by rewrite //=.
    intros n'. apply fun_to_mspec.
    rewrite /h.
    destruct l as [| l].
    { move: Hgt.  replace (INR 0) with 0 by auto. nra. } 
    destruct l as [| l].
    { move: Hgt.  replace (INR 0) with 0 by auto. replace (INR 1) with 1 by auto. nra. } 
    tbind (λ x, (sval x <= (S l))%coq_nat).
    { intros (x&?) _ => //=.  nify.  omega. }
    intros (pv&Hin) _. 
    apply mspec_mret.
    rewrite /sval. rewrite S_INR. ring_simplify.
    apply le_INR. nify; omega.
  - intros l. rewrite //=.
    rewrite /counter_rec.recurrence_counter.size //= => Hgt. 
    cut (∀ n, INR (((rvar_of_ldist (h l) n))) <= INR l); first by rewrite //=.
    intros n'. apply fun_to_mspec.
    rewrite /h.
    destruct l as [| l].
    { apply mspec_mret. reflexivity. }
    destruct l as [| l].
    { apply mspec_mret, le_INR. omega. }
    tbind (λ x, (sval x <= (S l))%coq_nat).
    { intros (x&?) _ => //=.  nify.  omega. }
    intros (pv&Hin) _. 
    apply mspec_mret.
    rewrite /sval. rewrite S_INR. 
    nify. apply le_INR in Hin. nra.
  - rewrite /quicksort_rec.recurrence_span2.size //=.
    intros l ? Hgt. rewrite //=.
    cut (∀ n, 0 <= INR (((rvar_of_ldist (h l) n)))); first by rewrite //=.
    intros n'. apply fun_to_mspec.
    intros ??. apply pos_INR. 
  - rewrite /counter_rec.recurrence_counter.size/counter_rec.recurrence_counter.rec_solution.d //=.
    intros x n Hle.
    replace 1 with (INR 1) in Hle by auto. apply INR_le in Hle.
    cut (shift ((rvar_of_ldist (approx_incrn x 0) n)) = 0); first by rewrite //=. 
    apply fun_to_mspec.
    destruct x; [| destruct x].
    * rewrite //=.
      apply mspec_mret => //=.
    * rewrite /approx_incrn. 
      rewrite ldist_left_id.
      rewrite /approx_incr.
      tbind (λ x, true).
      { rewrite //=. }
      intros b _.
      destruct b; apply mspec_mret => //=.
    * exfalso. omega.
  - intros. apply Trec; auto.
  - rewrite /counter_rec.recurrence_counter.size/counter_rec.recurrence_counter.rec_solution.d
            /counter_rec.recurrence_counter.rec_solution.m
            /counter_rec.recurrence_counter.count_factor.alpha.
    intros.
    etransitivity; first eapply Ex_h.
    rewrite /m/rsize/size/length. do 2 destruct Rlt_dec; try nra.
  - done.
Qed.

From Interval Require Import Interval_tactic.
Remark concrete_64_to_8bits:
  ∀ n, rsize n = 2^64 - 1 →
       pr_gt (rvar_comp (rvar_of_ldist (approx_incrn n O)) INR) (2^8 - 1)
        ≤ 1/(10^38).
Proof.
  intros n Hsize.
  transitivity (pr_gt (T n) 254).
  { rewrite /pr_gt /T ?pr_gt_alt_comp. right. apply eq_bigr.
    intros (i&?) => //= _.
    apply if_sumbool_case_match.
    rewrite /shift. destruct i.
    * replace (INR 0) with 0 by auto. nra.
    * rewrite S_INR. nra. 
  }
  transitivity (pr_gt (T n) ((k * ln (rsize n) + 1) + 169)).
  - apply Rge_le, pr_gt_contra.
    rewrite Hsize. rewrite /k. interval.
  - replace 169 with (INR 169); last first.
    { vm_compute. nra. } 
    etransitivity; first apply bound; auto; try nra. 
    interval.
Qed.


Remark concrete_64_to_7bits:
  ∀ n, rsize n = 2^64 - 1 →
       pr_gt (rvar_comp (rvar_of_ldist (approx_incrn n O)) INR) (2^7 - 1)
        ≤ 1/(10^9).
Proof.
  intros n Hsize.
  transitivity (pr_gt (T n) 126).
  { rewrite /pr_gt /T ?pr_gt_alt_comp. right. apply eq_bigr.
    intros (i&?) => //= _.
    apply if_sumbool_case_match.
    rewrite /shift. destruct i.
    * replace (INR 0) with 0 by auto. nra.
    * rewrite S_INR. nra. 
  }
  transitivity (pr_gt (T n) ((k * ln (rsize n) + 1) + 41)).
  - apply Rge_le, pr_gt_contra.
    rewrite Hsize. rewrite /k. interval.
  - replace 41 with (INR 41); last first.
    { vm_compute. nra. } 
    etransitivity; first apply bound; auto; try nra. 
    interval.
Qed.


Remark concrete_32_to_6bits:
  ∀ n, rsize n = 2^32 - 1 →
       pr_gt (rvar_comp (rvar_of_ldist (approx_incrn n O)) INR) (2^6 - 1)
        ≤ 5 * 1/10^5. 
Proof.
  intros n Hsize.
  transitivity (pr_gt (T n) 62).
  { rewrite /pr_gt /T ?pr_gt_alt_comp. right. apply eq_bigr.
    intros (i&?) => //= _.
    apply if_sumbool_case_match.
    rewrite /shift. destruct i.
    * replace (INR 0) with 0 by auto. nra.
    * rewrite S_INR. nra.
  }
  transitivity (pr_gt (T n) ((k * ln (rsize n) + 1) + 19)).
  - apply Rge_le, pr_gt_contra.
    rewrite Hsize. rewrite /k. interval.
  - replace 19 with (INR 19); last first.
    { vm_compute. nra. } 
    etransitivity; first apply bound; auto; try nra. 
    interval.
Qed.
