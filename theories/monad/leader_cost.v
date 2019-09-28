From discprob.basic Require Import base order nify seq_ext.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad monad_hoare counter leader.
From discprob.rec Require Import leader_rec.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier Psatz Omega.

Definition h (rp: nat * nat) := 
  match (fst rp) with
    | O => mret (O, snd rp)
    | S r' =>
      match (snd rp) with
      | O => mret (fst rp, O)
      | S O => mret (fst rp, O)
      | S (S n') =>
        surv ← counter.binomial (S (S n'));
        if sval surv == O then
            mret (r', S (S n'))
          else
            mret (r', sval surv)
      end
  end.
Definition rsize (n: nat * nat) :=
  match fst n with
    | O => 0
    | _ => INR (snd n)
  end.

Definition m x :=
  match (Rlt_dec x 2) with
  | left _ => 0
  | _ => x * (3 / 4)
  end.

Lemma Ex_h_aux n r:
  (Ex (rvar_of_ldist (x ← counter.binomial n; mret (rsize (r, (sval x))))) : R) <= 1/2 * INR n.
Proof.
  induction n. 
  - rewrite binomial_unfold ldist_left_id Ex_mret_simpl /rsize //=.
    destruct r => //=; nra.
  - rewrite binomial_unfold ldist_assoc Ex_mbind_ldist2 ?big_cons ?big_nil Rplus_0_r /snd.
    rewrite ?ldist_fmap_bind; simpl sval.
    rewrite pr_flip_true pr_flip_false.
    rewrite Ex_mbind_mret.
    etransitivity.
    { apply Rplus_le_compat_r. apply Rmult_le_compat_l; first nra.
      apply (Ex_fin_comp_mono _ _ (λ x, (1 + rsize (r, sval x)))).
      intros (x&?) => //=. rewrite /rsize.
      destruct r => //=; try nra.
      destruct x => //=; try nra.
    }
    rewrite -(rvar_comp_comp _ (λ x, rsize (r, sval x))).
    rewrite Ex_fin_plus_l. rewrite (Rplus_comm 1).
    rewrite -Ex_mbind_mret. rewrite S_INR.
    etransitivity.
    { apply Rplus_le_compat.
      * apply Rmult_le_compat_l; first nra. apply Rplus_le_compat_r; apply IHn.
      * apply Rmult_le_compat_l; first nra. apply IHn.
    }
    nra.
Qed.

Lemma Ex_h rp:
  Ex (rvar_comp (rvar_of_ldist (h rp)) rsize) <= m (rsize rp).
Proof.
  destruct rp as (r, p).
  revert r.
  induction p as [n IH] using (well_founded_induction lt_wf) => r.
  destruct r.
  { 
    rewrite Ex_fin_comp. 
    rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ a)).
    rewrite img_rvar_of_ldist//=/img/undup//= !big_cons ?big_nil.
    rewrite pr_mret_simpl //= /m eq_refl. 
    rewrite /rsize//=. destruct Rlt_dec; nra.
  }
  destruct n as [| n]; last destruct n as [| n].
  - rewrite Ex_fin_comp. 
    rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ a)).
    rewrite img_rvar_of_ldist//=/img/undup//= !big_cons ?big_nil.
    rewrite pr_mret_simpl //= /m eq_refl.
    rewrite /rsize//=. destruct (Rlt_dec) => //; nra.
  - rewrite Ex_fin_comp. 
    rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ a)).
    rewrite img_rvar_of_ldist//=/img/undup//= !big_cons ?big_nil.
    rewrite pr_mret_simpl //= /m eq_refl. 
    rewrite /rsize//=. destruct (Rlt_dec) => //; nra.
  - rewrite /h/fst/snd binomial_unfold.
    rewrite -Ex_mbind_mret ?ldist_assoc.
    rewrite Ex_mbind_ldist2 ?big_cons ?big_nil Rplus_0_r /snd.
    rewrite pr_flip_true pr_flip_false.
    rewrite ?ldist_fmap_bind. simpl sval. 
    rewrite -ldist_assoc ldist_fmap_bind. 
    destruct n as [| n].
    { 
      rewrite binomial_unfold ?ldist_assoc ?Ex_mbind_ldist2 ?big_cons ?big_nil Rplus_0_r /snd.
      rewrite ?pr_flip_true ?pr_flip_false.
      rewrite ?ldist_fmap_bind. simpl sval. 
      rewrite ?binomial_unfold ?ldist_assoc ?Ex_mbind_ldist2 ?big_cons ?big_nil Rplus_0_r /snd.
      rewrite ?ldist_left_id ?Ex_mret_simpl pr_mret_simpl.
      rewrite eq_refl //=.
      rewrite /rsize/m//=. destruct Rlt_dec => //=; first nra.
      destruct r; nra.
    }
    etransitivity.
    {
      apply Rplus_le_compat.
      * apply Rmult_le_compat_l; first nra. 
        etransitivity. 
        ** rewrite Ex_mbind_mret. apply (Ex_fin_comp_mono _ _ (λ x, (1 + rsize (r, sval x)))).
           intros (x&?) => //=. rewrite /rsize.
           destruct r => //=; try nra.
           destruct x => //=; try nra.
        ** rewrite -(rvar_comp_comp _ (λ x, rsize (r, sval x))).
           rewrite Ex_fin_plus_l. rewrite Rplus_comm.
           apply Rplus_le_compat_r. rewrite -Ex_mbind_mret. apply Ex_h_aux.
      * apply Rmult_le_compat_l; first nra.
        etransitivity. 
        ** rewrite (ldist_bind_ext _ (λ x, x' ← if sval x == 0%nat then mret (r, S (S (S n)))
                                                 else mret (r, sval x);
                                           mret (rsize x'))
                                     (λ x, x' ← mret (if sval x == 0%nat then (r, S (S (S n)))
                                                      else (r, sval x));
                                            mret (rsize x'))); last first.
           { intros. case: ifP; auto. }
           rewrite -ldist_assoc.
           rewrite ldist_fmap_bind.
           rewrite Ex_mbind_mret.
           apply (Ex_fin_comp_mono _ _ (λ x, (1 + rsize (if sval x == 0%nat then
                                                           (r, S (S n))
                                                         else
                                                           (r, sval x))))).
           { intros. rewrite /rsize; case: ifP => //=; destruct r; nra. }
        ** rewrite -(rvar_comp_comp _ _ (Rplus 1)).
           rewrite Ex_fin_plus_l. rewrite Rplus_comm. 
           apply Rplus_le_compat_r. rewrite -Ex_mbind_mret. 
           assert (S (S n) < S (S (S n)))%coq_nat as Hbound by auto.
           specialize (IH (S (S n)) Hbound (S r)).
           rewrite /h/fst/snd in IH.
           rewrite -(ldist_fmap_bind _ _ (λ x, mret (rsize x))) Ex_mbind_mret.
          rewrite -(ldist_bind_ext _ (λ x, if sval x == 0%nat then mret (r, (S (S n)))
                                           else mret (r, sval x))
                                     (λ x, mret (if sval x == 0%nat then (r, (S (S n)))
                                                      else (r, sval x)))); last first.
           { intros. case: ifP; auto. }
           apply IH.
    }
    rewrite ?S_INR /rsize/fst/snd ?S_INR.
    rewrite /m/rsize//=.
    specialize (pos_INR n).
    destruct (Rlt_dec) => //=; first nra. 
    destruct (Rlt_dec) => //=; first nra. 
    nra.
Qed.

Definition T := λ x, rvar_comp (rvar_of_ldist (leader_elect (fst x) (snd x))) 
                               (λ y, INR (fst x - fst y)).
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

Lemma if_mret {A: eqType} (P: bool) (a b: A):
  (if P then (mret a : ldist A) else mret b) = (mret (if P then a else b)).
Proof.
  destruct P; auto.
Qed.

Lemma Rmult_le_0_inv_r r r1 r2:
  r >= 0 → (r ≠ 0 → r1 <= r2) → r * r1 <= r * r2.
Proof.
  intros Hge Hcase. inversion Hge.
  - apply Rmult_le_compat_l; first nra. apply Hcase. nra.
  - subst. nra.
Qed.
  
Lemma Trec: 
  ∀ x r, (λ x, true) x → pr_gt (T x) r ≤ \big[Rplus/0]_(x' : imgT (h' x)) 
                ((pr_eq (h' x) (sval x')) * pr_gt (rvar_comp (T (sval x')) (λ x, x)) (r - a (rsize x))).
Proof.
  intros (rounds, n).
  intros. destruct rounds.
  { 
    rewrite /T -pr_gt_mbind_mret ldist_left_id pr_gt_mret_simpl. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' (O, n)) x' *
      pr_gt (rvar_comp (rvar_comp (rvar_of_ldist (leader_elect (fst x') (snd x')))
                                  (λ y, INR (fst x' - fst y))) (λ x, x))
            (r - a (rsize _))))).
    rewrite img_rvar_of_ldist /h'/h//=.
    rewrite big_cons big_nil Rplus_0_r//=.
    rewrite /a/rsize/size//=. 
    destruct (Rlt_dec); last nra.
    destruct (Rle_dec); last nra.
    rewrite rvar_comp_comp //=.
            rewrite //=.
    specialize (pr_gt_mbind_mret (mret (O, n)) (ssrfun.id \o (λ _ : nat * nat, 0)) (r - 0)).
    rewrite ldist_left_id.
    rewrite //= => <-.
    rewrite !pr_mret_simpl !pr_gt_mret_simpl eq_refl /id //= Rminus_0_r Rmult_1_l; nra.
  }
  induction n as [| n].
  - intros. rewrite /T.
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' (S rounds, O)) x' *
      pr_gt (rvar_comp (rvar_comp (rvar_of_ldist (leader_elect (fst x') (snd x'))) 
                                  (λ y, INR (fst x' - fst y))) ssrfun.id)
            (r - a (rsize (S rounds, O)))))).
    rewrite img_rvar_of_ldist /h. 
    rewrite big_cons big_nil Rplus_0_r.
    simpl fst.  simpl snd.
    rewrite /a/rsize/size.  simpl fst. rewrite /snd.
    replace (INR 0) with 0 by auto.
    destruct (Rlt_dec); last nra.
    destruct (Rle_dec); last nra.
    rewrite rvar_comp_comp //=.
    specialize (pr_gt_mbind_mret (mret (S rounds, O)) (ssrfun.id \o (λ y, INR (S rounds - fst y)))
                                 (r - 0)).
    rewrite ldist_left_id //= => <-.
    specialize (pr_gt_mbind_mret (mret (S rounds, O)) (λ y, INR (S rounds - fst y)) (r)).
    rewrite ldist_left_id //= => <-.
    rewrite !pr_mret_simpl !pr_gt_mret_simpl eq_refl /id //=. 
    rewrite Rminus_0_r.
    destruct (Rgt_dec);  nra.
  - intros. destruct n as [| n].
    {
      intros. rewrite /T.
      rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' (S rounds, S O)) x' *
      pr_gt (rvar_comp (rvar_comp (rvar_of_ldist (leader_elect (fst x') (snd x'))) 
                                  (λ y, INR (fst x' - fst y))) ssrfun.id)
            (r - a (rsize (S rounds, S O)))))).
    rewrite img_rvar_of_ldist /h. 
    rewrite big_cons big_nil Rplus_0_r.
    simpl fst.  simpl snd.
    rewrite /a/rsize/size.  simpl fst. rewrite /snd.
    replace (INR 1) with 1 by auto.
    destruct (Rlt_dec); last nra.
    destruct (Rle_dec); last nra.
    rewrite rvar_comp_comp //=.
    specialize (pr_gt_mbind_mret (mret (S rounds, O)) (ssrfun.id \o (λ y, INR (S rounds - fst y)))
                                 (r - 0)).
    rewrite ldist_left_id //= => <-.
    specialize (pr_gt_mbind_mret (mret (S rounds, S O)) (λ y, INR (S rounds - fst y)) (r)).
    rewrite ldist_left_id //= => <-.
    rewrite !pr_mret_simpl !pr_gt_mret_simpl eq_refl /id //=. 
    rewrite Rminus_0_r.
    destruct (Rgt_dec);  nra.
    }
    rewrite /T.
    transitivity
      (pr_gt (rvar_comp (rvar_of_ldist
         (surv ← h (S rounds, S (S n)); leader_elect (fst surv) (snd surv)))
          (λ x, 1 + (INR (rounds - fst x)))) r); last first.
    {    
      rewrite /T.
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' (S rounds, S (S n))) x' *
      pr_gt (rvar_comp (rvar_comp (rvar_of_ldist (leader_elect (fst x') (snd x'))) 
                       (λ y, INR (fst x' - fst y))) id)
            (r - a (rsize (S rounds, S (S n))))))).
    rewrite -pr_gt_mbind_mret ldist_assoc. rewrite pr_gt_mbind_ldist2.
    rewrite img_rvar_of_ldist. 
      * eapply Rle_bigr. intros k ?.
        apply Rmult_le_0_inv_r; first apply pr_eq_ge_0. 
        intros Hnon0.
        rewrite pr_gt_mbind_mret. 
        rewrite rvar_comp_comp. rewrite {1}/pr_gt {1}[a in _ <= a]/pr_gt.
        rewrite ?pr_gt_alt_comp /id. eapply Rle_bigr => x ?. rewrite //=.
        cut ((fst k >= rounds)%coq_nat).
        {
          intros Hlt. 
          destruct Rgt_dec as [Hc1|Hc1] => //=; try auto; try nra;
          destruct Rgt_dec as [Hc2|Hc2] => //=; try auto; try nra.
          ** exfalso. apply Hc2. rewrite /rsize/a.
             specialize (S_INR n) => /= => ->. 
             specialize (pos_INR n). destruct (Rlt_dec) as [Hlt0|Hnlt]; first nra.
             destruct (Rle_dec); first nra.
             intros. assert (INR (rounds - fst (sval x)) > r - 1). 
               { clear -Hc1. rewrite //= in Hc1. rewrite //=. nra. }
             eapply Rge_gt_trans; eauto.
             apply Rle_ge. apply le_INR. nify. clear -Hlt. destruct x => //=.
             destruct x, k => //=. simpl in Hlt. omega.
          ** apply Rge_le, pr_eq_ge_0.  
        }
        assert ( k \in img (h' (S rounds, S (S n)))) as Himg.
        { apply pr_img. edestruct (pr_eq_ge_0 (h' (S rounds, S (S n)))); eauto.
          congruence. }
        apply img_alt in Himg.
        destruct Himg as (i&<-).
        rewrite /h'. apply fun_to_mspec.
        rewrite /h/fst/snd. tbind (λ x, true).
        { rewrite //=. }
        intros ??. case: ifP => ?; apply mspec_mret; auto.
    }
    rewrite /h/fst/snd.
    rewrite -?pr_gt_mbind_mret.
    rewrite leader_elect_unfold.
    rewrite ldist_assoc.
    rewrite -?pr_gt_mbind_mret.
    rewrite ?ldist_assoc.
    eapply le_dist_ldist_bind_ext => a.
    eapply le_dist_ldist_bind_ext => pv k.
    rewrite (if_mret (sval pv == 0)%nat (rounds, S (S n)) (rounds, sval pv)).
    rewrite ldist_left_id //=.
    case: ifP.
    * intros. rewrite //=. apply: le_dist_ldist_bind_ext => n'; clear k.
                intros k. rewrite ?pr_gt_mret_simpl.
                destruct (Rgt_dec) as [Hc1|Hc1] => //=; try nra;
                destruct (Rgt_dec) as [Hc2|Hc2] => //=; try nra.
                exfalso. apply Hc2. eapply Rge_gt_trans; eauto.
                replace 1 with (INR 1) by auto. rewrite -plus_INR.
                apply Rle_ge, le_INR. nify. omega.
    * intros. rewrite //=. apply: le_dist_ldist_bind_ext => n'; clear k.
                intros k. rewrite ?pr_gt_mret_simpl.
                destruct (Rgt_dec) as [Hc1|Hc1] => //=; try nra;
                destruct (Rgt_dec) as [Hc2|Hc2] => //=; try nra.
                exfalso. apply Hc2. eapply Rge_gt_trans; eauto.
                replace 1 with (INR 1) by auto. rewrite -plus_INR.
                apply Rle_ge, le_INR. nify. omega.
Qed.

Definition k := -/ ln(3/4).

Theorem bound x w:
    rsize x > 1 →  
    pr_gt (T x) ((k * ln (rsize x) + 1) + INR w)
       ≤ (3/4)^w.
Proof.
  specialize (leader_rec.recurrence_leader.leader_bound _ _ _ _ T h' (λ x, true)).
  rewrite /size/rsize => Hrec. eapply Hrec; clear.
  - auto.
  - intros l ?. rewrite //=.
    rewrite /leader_rec.recurrence_leader.size/leader_rec.recurrence_leader.msr //= => Hgt. 
    cut (∀ n, INR (fst ((rvar_of_ldist (h l) n))) <= INR (fst l) - 1); first by rewrite //=.
    intros n'. apply fun_to_mspec.
    rewrite /h.
    destruct l as (r, p). rewrite /fst/snd.
    destruct r as [| r].
    { move: Hgt.  rewrite //=. nra. }
    move: Hgt. rewrite /fst/snd.
      destruct p.
      * replace (INR 0) with 0 by auto; nra.
      * rewrite S_INR. destruct p.
        ** replace (INR 0) with 0 by auto; nra.
        ** intros. tbind (λ x, true); first by auto.
           intros. case: ifP; intros; apply mspec_mret => //=;
           destruct r; rewrite ?S_INR //=; nra.
  - intros l. rewrite //=.
    cut (∀ n, recurrence_leader.size ((rvar_of_ldist (h l) n)) <=
              recurrence_leader.size (l)); first by rewrite //=.
    intros n'. apply fun_to_mspec.
    rewrite /h.
    destruct l as (r, p). rewrite /fst/snd.
    destruct r as [| r].
    { apply mspec_mret. reflexivity.  }
    destruct p as [| p].
    { apply mspec_mret. reflexivity. }
    destruct p as [| p].
    { apply mspec_mret. rewrite /recurrence_leader.size. rewrite //=. nra. }
    tbind (λ x, (sval x <= (S (S p)))%coq_nat).
    { intros (x&?) _ => //=.  nify.  omega. }
    intros (pv&Hin) _. 
    rewrite //=.
    case: ifP; intros; apply mspec_mret;
    rewrite /recurrence_leader.size;
    rewrite /sval; rewrite S_INR //=;
    destruct r, p; try nra;
    try specialize (pos_INR (S p)); try nra.
    * nify. apply le_INR in Hin. rewrite //= in Hin.
    * nify. apply le_INR in Hin. rewrite ?S_INR //= in Hin. rewrite ?S_INR. done.
  - intros l ? Hgt. rewrite //=.
    cut (∀ n, 0 <= recurrence_leader.size ((rvar_of_ldist (h l) n))); first by rewrite //=.
    intros n'. apply fun_to_mspec.
    intros (r&?) ?. rewrite /recurrence_leader.size => //=. destruct r; try nra. apply pos_INR. 
  - intros x n Hle. 
    rewrite /T.
    cut (INR (fst x - fst (rvar_of_ldist (leader_elect (fst x) (snd x)) n)) = 0);
      first by rewrite //=. 
    apply fun_to_mspec.
    destruct x as (r, p).
    destruct r as [| r].
    { rewrite leader_elect_unfold //. }
    destruct p; [| destruct p].
    rewrite //=. 
    * apply mspec_mret => //=. replace 0 with (INR 0) by auto. f_equal. nify. omega.
    * apply mspec_mret => //=. replace 0 with (INR 0) by auto. f_equal. nify. omega.
    * exfalso. move : Hle. 
      rewrite /leader_rec.recurrence_leader.size/leader_rec.recurrence_leader.rec_solution.d//=.
      destruct p; first nra.
      specialize (pos_INR (S p)). nra.
  - intros. apply Trec; auto.
  - rewrite /leader_rec.recurrence_leader.size/leader_rec.recurrence_leader.rec_solution.d
            /leader_rec.recurrence_leader.rec_solution.m
            /leader_rec.recurrence_leader.count_factor.alpha.
    intros.
    etransitivity; first eapply Ex_h.
    rewrite /m/rsize/size/length. do 2 destruct Rlt_dec; try nra.
  - done.
Qed.

From Interval Require Import Interval_tactic.
Remark concrete_512:
  ∀ n, pr_gt (rvar_comp (rvar_of_ldist (leader_elect (S n) 512)) (λ x, INR (S n - fst x))) (64)
        ≤ 1/(10^5).
Proof.
  intros n.
  transitivity (pr_gt (T (S n, 512%nat)) 64).
  { rewrite /T/fst/snd. reflexivity. } 
  transitivity (pr_gt (T (S n, 512%nat)) ((k * ln (rsize (S n, 512%nat)) + 1) + 41)).
  - apply Rge_le, pr_gt_contra.
    rewrite /k. rewrite /rsize/fst/snd.
    replace (INR 512) with 512; last first.
    { vm_compute. nra. }
    interval.
  - replace 41 with (INR 41); last first.
    { vm_compute. nra. } 
    etransitivity; first apply bound. 
    { rewrite /rsize//=. nra. }
    interval.
Qed.

Remark concrete_huge:
  ∀ players n, 
    INR players = 2^32 →
    pr_gt (rvar_comp (rvar_of_ldist (leader_elect (S n) players)) (λ x, INR (S n - fst x))) (128)
        ≤ 1/(10^6).
Proof.
  intros p n Hsize.
  transitivity (pr_gt (T (S n, p)) ((k * ln (rsize (S n, p)) + 1) + 49)).
  - apply Rge_le, pr_gt_contra.
    rewrite /k. rewrite /rsize/fst/snd.
    rewrite Hsize.
    interval.
  - replace 49 with (INR 49); last first.
    { vm_compute. nra. } 
    etransitivity; first apply bound. 
    { rewrite /rsize//=. nra. }
    interval.
Qed.