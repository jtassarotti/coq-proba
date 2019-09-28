From discprob.basic Require Import base order nify sval.
From discprob.prob Require Import prob countable finite stochastic_order uniform.
From discprob.monad Require Import monad monad_hoare.
From discprob.monad Require quicksort quicksort_cost.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From Coq Require Import Omega Psatz Program.Wf MSets.MSetInterface MSets.MSetGenTree Structures.OrdersEx.
Local Open Scope nat_scope.

(* TODO: should make unif generic over ``cost'' or not, so don't have to repeat this
   across other examples *)
Require Import Reals Fourier FunctionalExtensionality.
Program Definition unif n : ldist { x : nat | (leq x n) } :=
  mklDist [ seq (1/(INR (n.+1)), (exist _ (nat_of_ord i) _)) | i <- enum 'I_(n.+1) ] _ _.
Next Obligation. intros n (?&?); rewrite -ltnS. done. Qed.
Next Obligation. 
  intros ?.
  apply /allP => r.
  rewrite -map_comp //= (@eq_map _ _ _ (λ x, 1 / INR (S n))); last by done.
  rewrite (nat_of_ord_map_iota (S n) (λ x, 1 / INR (S n))).
  rewrite //=. induction (iota 1 n) => //=.
  - rewrite in_cons. move /orP => [Heq|Hin]; eauto.
    move /eqP in Heq. rewrite Heq. 
    destruct (Rle_dec) as [|Hn]; [ by auto | exfalso; apply Hn].
    left. apply Rdiv_lt_0_compat; first fourier.
    destruct n; first fourier.
    replace 0 with (INR O) by auto.
    cut (INR 0 < INR (S n)); intros; first by fourier.
    apply lt_INR. omega.
  - rewrite in_cons. move /orP => [Heq|Hin]; eauto.
    move /eqP in Heq. rewrite Heq. 
    destruct (Rle_dec 0 (1 / _)) as [|Hn]; [ by auto | exfalso; apply Hn].
    left. apply Rdiv_lt_0_compat; first fourier.
    destruct n; first by fourier.
    replace 0 with (INR O) by auto.
    cut (INR 0 < INR (S n)); intros; first by fourier.
    apply lt_INR; omega.
Qed.
Next Obligation.
  intros ?.
  rewrite -map_comp //= (@eq_map _ _ _ (λ x, 1 / INR (S n))); last by done.
  rewrite (nat_of_ord_map_iota (S n) (λ x, 1 / INR (S n))).
  cut (∀ o k, \big[Rplus/0]_(a<-[seq (1 / INR n.+1) | i <- iota k o]) a 
            = INR (o) / INR (n.+1)).
  { 
    intros Hcut. specialize (Hcut (n.+1) O). rewrite //= in Hcut.
    rewrite Hcut. apply /eqP => //=. field. 
    apply Rgt_not_eq.
    destruct n; first fourier.
    replace 0 with (INR O) by auto.
    cut (INR 0 < INR (S n)); first by intros; fourier.
    apply lt_INR; omega.
  }
  induction o => k.
  - rewrite big_nil. replace (INR 0) with 0 by auto. rewrite /Rdiv Rmult_0_l //. 
  - rewrite big_cons. rewrite (S_INR o).
    rewrite Rdiv_plus_distr IHo. ring. 
Qed.

Lemma unif_all n x (Hle: (x <= n)%nat):
  exist _ x Hle \in [seq i.2 | i <- outcomes (unif n)].
Proof.
  apply /mapP.
  set (a := exist _ x Hle).
  replace (a) with (1/INR (S n), a).2; last done.
  do 2 apply /mapP; eexists; eauto.
  rewrite /unif => //=.
  apply /mapP => //=.
  assert (Hlt: (x < S n)%nat) by auto.
  exists (Ordinal Hlt).
  - apply mem_enum. 
  - rewrite /a; repeat f_equal. apply bool_irrelevance.
Qed.


Lemma unif_pr n a : 
  a \in [seq i.2 | i <- outcomes (unif n)] → 
  pr_eq (rvar_of_ldist (unif n)) a = 1 / INR (S n).
Proof.
  intros Hin. rewrite pr_rvar_ldist /unif//=.
  rewrite big_map -big_filter //=.
  destruct a as (x&Hle) => //=.
  assert (Hlt: (x < S n)%nat) by auto.
  rewrite (bigD1_seq (Ordinal Hlt)) => //=.
  - rewrite -[a in _ = a]Rplus_0_r; f_equal.
    rewrite -big_filter -filter_predI big_filter. apply big_pred0.
    intros i => //=. apply negbTE. apply /andP => [] []. move /eqP => Heq.
    move /eqP => []. intros. subst. apply Heq.
    destruct i. f_equal. apply bool_irrelevance. 
  - rewrite mem_filter. apply /andP; split; auto. 
    * apply /eqP; f_equal; auto. f_equal. apply bool_irrelevance.
    * apply mem_enum. 
  - apply /filter_uniq/enum_uniq.
Qed.

Lemma unif_sval n n':
  n = n' →
  map sval (undup (map snd (unif n))) = map sval (undup (map snd (unif n'))).
Proof.
  intros Heq. rewrite /unif. subst. auto.
Qed.

Section perm.
Variable (A: eqType).
Program Definition draw_next (a : A) (l: list A) : ldist { x : A | x \in (a :: l) } :=
  idx ← unif (size l);
  mret (exist _ (nth a (a :: l) (sval idx)) _).
Next Obligation. intros a l (?&?); rewrite mem_nth //. Qed.


Definition rand_perm_list : list A → ldist (list A).
  refine(Fix (measure_wf lt_wf size) (fun _ => ldist (list A))
  (fun l rand_perm_list => 
     match l as l' return (l = l' → ldist (list A)) with
     | [::] => λ eq, mret [::]
     | [::a] => λ eq, mret [::a]
     | (a :: b :: l') => λ eq, 
                         p ← draw_next a (b :: l');
                         rest ← rand_perm_list (rem (sval p) (a :: b :: l')) _;
                         mret (sval p :: rest)
     end (Init.Logic.eq_refl))); rewrite /MR; auto.
  - abstract (destruct p as (x&Hin); rewrite size_rem //; subst; rewrite //=).
Defined.

Lemma rand_perm_list_unfold_aux l:
  rand_perm_list l =
  match l as l' return (l = l' → ldist (list A)) with
     | [::] => λ eq, mret [::]
     | [::a] => λ eq, mret [::a]
     | (a :: b :: l') => λ eq, 
                         p ← draw_next a (b :: l');
                         rest ← rand_perm_list (rem (sval p) (a :: b :: l'));
                         mret (sval p :: rest)
  end (Init.Logic.eq_refl).
Proof. rewrite /rand_perm_list quicksort.easy_fix_eq; done. Qed.

Lemma rand_perm_list_unfold l:
  rand_perm_list l =
  (match l with
    | [::] => mret [::]
    | [::a] => mret [::a]
    | (a :: l) => p ← draw_next a l;
                         rest ← rand_perm_list (rem (sval p) (a :: l));
                         mret (sval p :: rest)
  end).
Proof. rewrite rand_perm_list_unfold_aux. destruct l => //. destruct l => //. Qed.
End perm.

Arguments rand_perm_list {_}.
Arguments draw_next {_}.


Lemma draw_next_pr {A: eqType} (a': A) l a: 
  uniq (a' :: l) →
  sval a \in (a' :: l) →
  pr_eq (rvar_of_ldist (draw_next a' l)) a = 1 / INR (size (a' :: l)).
Proof.
  intros Huniq Hin. rewrite /draw_next.
  rewrite pr_mbind_ldist2.  
  assert (Hpf: (index (sval a) (a' :: l) <= size l)%nat).
  { rewrite -index_mem in Hin. rewrite //= in Hin. } 
  rewrite (@big_rem _ _ _ _ (undup (map snd (unif (size l)))) 
                    (exist _ (index (sval a) (a' :: l)) Hpf)); last first.
  { rewrite mem_undup. apply unif_all. }
    rewrite -[a in _ = a]Rplus_0_r. 
    rewrite rem_filter; last apply undup_uniq. 
    rewrite big_filter.
    rewrite big1; last first.
    { intros (n&Hle) Hn0. apply Rmult_eq_0_compat_l. 
      rewrite pr_mret_simpl //. destruct a. case: ifP; auto.
      intros Heq. move /eqP in Heq. inversion Heq as [[Heqx]].
      rewrite /sval in Hn0. cut (n = index x (a' :: l)).
      { intros Hidx. exfalso. move /negP in Hn0. apply Hn0.  
        apply /eqP. clear -Hidx. subst. f_equal. apply bool_irrelevance. } 
      symmetry. rewrite -Heqx. apply index_uniq; auto. }
    apply Rplus_eq_compat_r.
    rewrite pr_mret_simpl. case: ifP; last first. 
    { move /negP => Hfalse. exfalso; apply Hfalse. apply /eqP.
      destruct a as (a&Hin').
      apply sval_inj_pred. rewrite /sval.
      apply nth_index. auto.
    }
    intros. rewrite Rmult_1_r unif_pr; first done.
    apply unif_all.
Qed.

Lemma draw_next_all {A: eqType} (a: A) l x Hin:
  uniq (a :: l) →
  exist _ x Hin \in [seq i.2 | i <- outcomes (draw_next a l)].
Proof.
  intros Huniq.
  rewrite -mem_undup.
  rewrite -img_rvar_of_ldist'.
  apply pr_img. rewrite draw_next_pr //.
  apply Rlt_gt, Rdiv_lt_0_compat; first nra.
  specialize (pos_INR (size l)).
  rewrite S_INR. rewrite //=. rewrite -/size. nra.
Qed.
                     
Definition gen_perm (n: nat) := rand_perm_list (Finite.enum [finType of 'I_n]).

Lemma perm_eq_nil (A: eqType) (l: list A): perm_eq l [::] → l = [::].
Proof.
  move /perm_eq_size. destruct l => //=.
Qed.

Lemma perm_eq_singleton (A: eqType) (l: list A) (a: A): perm_eq l [::a] → l = [::a].
Proof.
  destruct l => //=.
  - rewrite perm_eq_sym. move /perm_eq_nil => //.
  - destruct l as [| b l] => //=. 
    * move /perm_eqP. intros Heq. specialize (Heq (pred1 a)).
      rewrite //= in Heq. f_equal.
      move: Heq. case: eqP; auto. rewrite eq_refl //=.
    * move /perm_eq_size => //=.
Qed.

Lemma perm_eq_rem {A: eqType} (l1 l2: list A) x:
  perm_eq l1 l2 → perm_eq (rem x l1) (rem x l2).
Proof.
  intros Heq.
  case_eq (x \in l1).
  - rewrite -(perm_cons x).
    intros Hin. eapply perm_eq_trans.
    * rewrite perm_eq_sym. apply perm_to_rem. done. 
    * eapply perm_eq_trans; first apply Heq. apply perm_to_rem.
      rewrite -(perm_eq_mem Heq) //.
  - intros Hnin. rewrite ?rem_id //.
    * rewrite -(perm_eq_mem Heq). apply /negP. rewrite Hnin. done.
    * apply /negP. rewrite Hnin. done.
Qed.

Lemma rand_perm_list_initial {A: eqType} (l1 l2 lt: seq A):
  perm_eq l1 l2 →
  pr_eq (rvar_of_ldist (rand_perm_list l1)) lt = 
  pr_eq (rvar_of_ldist (rand_perm_list l2)) lt.
Proof.
  remember (size l1) as k eqn:Heq.
  revert l1 l2 lt Heq.
  induction k as [k IH] using (well_founded_induction lt_wf) => l1 l2 lt Heq Hperm.
  destruct l1 as [| a1 l1]; last destruct l1 as [| b1 l1].
  - rewrite perm_eq_sym in Hperm; apply perm_eq_nil in Hperm; subst.
    done.
  - rewrite perm_eq_sym in Hperm; apply perm_eq_singleton in Hperm; subst. 
    done.
  - destruct l2 as [| a2 l2]; last destruct l2 as [| b2 l2].
    { apply perm_eq_nil in Hperm; subst. congruence. }
    { apply perm_eq_singleton in Hperm; subst. congruence. }
    rewrite ?rand_perm_list_unfold. 
    rewrite /draw_next. rewrite ?ldist_assoc.
    rewrite ?pr_mbind_ldist2.
    destruct (quicksort_cost.perm_eq_bij a1 _ _ Hperm) as (h&Hhspec&Hhsize&Hinv&Hinj).
    assert (Hbound: ∀ x, (x <= size (b1 :: l1))%nat → (h x <= size (b2 :: l2))%nat).
    { rewrite //= => x Hle. 
      apply (perm_eq_size) in Hperm.
      rewrite //= in Hperm.
      assert (h x < S (S (size l1)))%nat as Hsize'. 
      { apply Hhsize. rewrite //=. }
      nify. omega.
    }
    set (h' := λ x : {y : nat | (y <= (size (b1 :: l1)))%nat} ,
                     match x with
                      | exist n Hpf => (exist _ (h n) (Hbound n Hpf) :
                                          {x : nat | (x <= size (b2 :: l2))%nat})
                    end).
    eapply (sum_reidx_map _ _ _ _ h').
    * intros (n&Hle) Hin. f_equal.
      { rewrite ?unif_pr //; rewrite /h'; try apply unif_all.
        apply perm_eq_size in Hperm.  rewrite //= in Hperm. inversion Hperm as [Hsize].
        rewrite /size -/size Hsize. done. }
      rewrite 2!ldist_left_id /h'/sval.
      symmetry.
      rewrite (set_nth_default a1); last first. 
      { rewrite //=. by apply Hbound. }
      symmetry.
      eapply eq_dist_ldist_bind_congr.
      ** intros lt'. eapply IH; eauto.
         rewrite size_rem; subst => //=; nify; try omega.
         { apply /mem_nth => //=. }
         rewrite Hhspec; last by rewrite //=.
         apply perm_eq_rem; auto.
      ** intros a x. rewrite ?pr_mret_simpl Hhspec. eauto.
         rewrite //=.
    * intros a Hin _; split; auto. rewrite mem_undup. 
      destruct (h' a); apply unif_all.
    * intros (x&Hx) Hin _ Hfalse. exfalso. apply Hfalse.
      edestruct (Hinv x) as (x'&Hlt&?); eauto.
      { apply perm_eq_size in Hperm. clear -Hx Hperm. 
        rewrite //= in Hx, Hperm. nify. rewrite //=. omega. } 
      exists (exist _ x' Hlt); repeat split.
      ** rewrite mem_undup. apply unif_all.
      ** rewrite /h'//=; subst.
         f_equal => //=. apply bool_irrelevance. 
    * apply undup_uniq.
    * apply undup_uniq.
    * intros (x&?) (x'&?) _ Heqh'.
      rewrite /h' in Heqh'. inversion Heqh' as [Heqh]. eapply Hinj in Heqh; eauto.
      subst. f_equal. apply bool_irrelevance.
Qed.

(*
Lemma rand_perm_gen_then_draw {A: eqType} (a: A) (l: seq A):
  eq_dist (rvar_of_ldist (rand_perm_list l))
          (rvar_of_ldist (sigma ← gen_perm (size l);
                          mret ([seq (nth a l (nat_of_ord i)) | i <- sigma]))).
Proof.  
  remember (size l) as k eqn:Heq.
  revert l Heq.
  induction k as [k IH] using (well_founded_induction lt_wf) => l Heq => lt.
  destruct l as [| b1 l]; last destruct l as [| b2 l].
  - subst. rewrite /size/gen_perm.
    assert (Finite.enum [finType of 'I_0] = [::]) as ->.
    { destruct (Finite.enum _) as [| o l] => //=. inversion o. nify. omega. }
    rewrite ?rand_perm_list_unfold. 
    rewrite ldist_left_id. rewrite pr_mret_simpl; done.
  - rewrite rand_perm_list_unfold.
    rewrite /gen_perm. rewrite ?rand_perm_list_unfold.
    subst. specialize (size_enum_ord 1).
    rewrite enumT.
    destruct (Finite.enum) as [| o le]; first by done.
    destruct le; last by done.
    intros ?. rewrite ldist_left_id. rewrite ?pr_mret_simpl //=.
    assert (nat_of_ord o = O) as Hnat.
    { destruct o as (x&Hlt) => //=. clear -Hlt. rewrite //= in Hlt.  nify. omega. } 
    rewrite Hnat //=.
  - rewrite /gen_perm.
Abort.
*)

Lemma rand_perm_list_id {A: eqType} (l1: seq A):
  uniq l1 →
  pr_eq (rvar_of_ldist (rand_perm_list l1)) l1 = 1 / INR ((size l1)`!).
Proof. 
  remember (size l1) as k eqn:Heq.
  revert l1 Heq.
  induction k as [k IH] using (well_founded_induction lt_wf) => l1 Heq Huniq1.
  destruct l1 as [| a1 l1]; last destruct l1 as [| b1 l1].
  - rewrite rand_perm_list_unfold. subst. rewrite //=. rewrite pr_mret_simpl eq_refl.
    field.
  - rewrite rand_perm_list_unfold. subst. rewrite //=. rewrite pr_mret_simpl eq_refl.
    field.
  - rewrite ?rand_perm_list_unfold ?ldist_assoc ?pr_mbind_ldist2.
    assert (Hpf: (O <= size (b1 :: l1))%nat).
    { rewrite //=. }
    rewrite (@big_rem _ _ _ _ (undup (map snd (unif (size (b1 :: l1))))) (exist _ O Hpf)); last first.
    { rewrite mem_undup.  apply unif_all. }
    rewrite -[a in _ = a]Rplus_0_r. 
    rewrite rem_filter; last apply undup_uniq. 
    rewrite big_filter.
    rewrite big1; last first.
    { intros (n&Hle) Hn0. apply Rmult_eq_0_compat_l. 
      rewrite ldist_left_id /sval. rewrite ?pr_mbind_mret_inj0 //. intros rest. 
      destruct n; rewrite //= in Hn0.
      intros Heq'. 
      assert (nth a1 [:: a1, b1 & l1] (S n) == nth a1 [:: a1, b1 & l1] O) as Hidx.
      { rewrite //=. apply /eqP. inversion Heq' as [[Hhd Htl]]. rewrite Hhd. done.  }
      rewrite nth_uniq in Hidx; auto.
    }
    apply Rplus_eq_compat_r.
    subst. rewrite {1}factS. rewrite -/size.
    transitivity ((1/ INR (S (S (size l1)))) * (1 / INR ((S (size l1))`!))); last first.
    { symmetry. rewrite mult_INR ?S_INR. field. split. 
      * rewrite factS mult_INR ?S_INR. specialize (pos_INR (size l1)).
        intros. apply Rgt_not_eq. specialize (fact_gt0 (size l1)). intros Hgt0. nify. 
        apply lt_INR in Hgt0. replace (INR 0) with 0 in Hgt0; auto; nra.
      * specialize (pos_INR (size l1)). nra.
    }
    f_equal.
    * rewrite unif_pr; first by auto. apply unif_all.
    * rewrite ldist_left_id /sval. rewrite pr_mbind_mret_inj; last first.
      { intros a b; congruence. }
      rewrite /nth. rewrite {1}/rem //= eq_refl. apply IH; auto.
      rewrite cons_uniq in Huniq1. move /andP in Huniq1. intuition.
Qed.

Lemma pr_rand_perm_list {A: eqType} (l1 l2: seq A):
  uniq l1 →
  perm_eq l1 l2 →
  pr_eq (rvar_of_ldist (rand_perm_list l1)) l2 = 1 / INR ((size l1)`!).
Proof. 
  intros Huniq Hperm. 
  rewrite (rand_perm_list_initial l1 l2) //.
  rewrite rand_perm_list_id; last first.
  { rewrite -(perm_eq_uniq Hperm). done. }
  apply perm_eq_size in Hperm. rewrite Hperm. done.
Qed.

Lemma rand_perm_list_id' {A: eqType} (l1 l2: seq A):
  uniq l1 →
  uniq l2 →
  size l1 = size l2 →
  pr_eq (rvar_of_ldist (rand_perm_list l1)) l1 = 
  pr_eq (rvar_of_ldist (rand_perm_list l2)) l2.
Proof.
  intros Hu1 Hu2 Hsize. rewrite ?rand_perm_list_id // Hsize. done.
Qed.

Lemma rand_perm_list_correct {A: eqType} (l: list A):
  mspec (rand_perm_list l) (λ l': list A, perm_eq l l').
Proof.
 remember (size l) as k eqn: Heq.
 revert l Heq.
 induction k as [k IH] using (well_founded_induction lt_wf) => l Heq.
 destruct l as [| a l]; last destruct l as [| b l].
 - rewrite rand_perm_list_unfold. apply mspec_mret => //=.
 - rewrite rand_perm_list_unfold. apply mspec_mret => //=.
 - rewrite rand_perm_list_unfold.
   tbind (λ x, sval x \in a :: b :: l).
   { intros (?&?) => //. }
   intros (x&Hin) _.
   rewrite /sval. tbind (λ l', perm_eq (rem x [:: a, b & l]) l').
   { 
     eapply IH; eauto. subst. rewrite size_rem //=.
   }
   intros l' Hperm. 
   apply mspec_mret.
   eapply perm_eq_trans; first apply (perm_to_rem Hin); eauto.
   rewrite perm_cons. done.
Qed.

Lemma img_rand_perm_list {A: eqType} (l: list A):
  uniq l →
  img (rvar_of_ldist (rand_perm_list l)) =i perm_eq l.
Proof.  
  intros Huniq l'. rewrite img_rvar_of_ldist' mem_undup. 
  case_eq (l' \in (map snd (rand_perm_list l))).
  * intros Htrue. rewrite Htrue. 
    symmetry. apply rand_perm_list_correct. rewrite /output. auto.
  * intros Hnotin.
    case_eq (l' \in perm_eq l); rewrite //=.
    intros Hl'. exfalso.
    move /negP in Hnotin. apply Hnotin.
    rewrite -mem_undup. 
    rewrite -img_rvar_of_ldist'.
    apply pr_img. rewrite pr_rand_perm_list //.
    specialize (fact_gt0 (size l)). intros Hgt. nify. 
    apply lt_INR in Hgt. replace (INR 0) with 0 in Hgt by auto.
    apply Rlt_gt, Rdiv_lt_0_compat; nra.
Qed.

Lemma permutation_uniform {A: eqType} (l: list A):
  uniq l →
  uniform_on (rvar_of_ldist (rand_perm_list l)) (img (rvar_of_ldist (rand_perm_list l))).
Proof. 
  intros Huniq l1 l2 Hin1 Hin2.
  rewrite ?pr_rand_perm_list //. 
  - specialize (img_rand_perm_list l Huniq l2). rewrite /in_mem/mem//=. intros <-. auto.
  - specialize (img_rand_perm_list l Huniq l1). rewrite /in_mem/mem//=. intros <-. auto.
Qed.

Lemma INR_fact_gt0 n:
  0 < INR (n`!).
Proof.
  replace 0 with (INR 0) by auto. apply lt_INR. specialize (fact_gt0 n). intros. nify. done.
Qed.

Lemma filter_rem {A: eqType} (x: A) (s: seq A) (P: pred A):
  filter P (rem x s) = rem x (filter P s).
Proof.
  induction s => //=.
  case: ifP => //=.
  - case: ifP.
    * rewrite //=. intros ? ->. done.
    * rewrite //=; intros HP Heq. rewrite rem_id //. 
      apply /negP. rewrite mem_filter. move /andP. intros (HP'&?). 
      move /eqP in Heq. subst. move /negP in HP. apply HP. auto.
  - intros Hneq. case: ifP => //= HP. rewrite Hneq. f_equal.
    auto.
Qed.

(* TODO: there's a tremendous amount of redundancy and symmetry in the case work *)
Lemma pr_shuffle_then_split {A: eqType} (l: list A) (P Q: pred A) l1 l2 a0
  (Ha0: ∀ a, ((~~ P a) ∧ (~~ Q a)) ↔ a = a0)
  (HPQ: ∀ a, ~~ (P a && Q a)):
  uniq l →
  perm_eq (filter P l) l1 →
  perm_eq (filter Q l) l2 →
  pr_eq (rvar_of_ldist (lrand ← rand_perm_list l; mret (filter P lrand, filter Q lrand)))
        (l1, l2) = (1 / INR (size l1)`!) * (1 / INR (size l2)`!).
Proof. 
  remember (size l) as k eqn:Heq.
  revert l l1 l2 Heq.
  induction k as [k IH] using (well_founded_induction lt_wf) 
    => l l1 l2 Heq Huniq Hperm1 Hperm2.
  assert (Ha0Q: ~ Q a0).
  {
    intros HQ. 
    specialize (proj2 (Ha0 a0) Init.Logic.eq_refl); auto.
    intros (?&?). subst. apply /negP; eauto.
  }
  assert (Ha0P: ~ P a0).
  {
    intros HP. 
    specialize (proj2 (Ha0 a0) Init.Logic.eq_refl); auto.
    intros (?&_). subst. apply /negP; eauto.
  }
  assert (size l = size l1 + size l2 + (a0 \in l))%nat as Hsize_combine.
  { 
    apply perm_eq_size in Hperm1.
    apply perm_eq_size in Hperm2.
    rewrite -Hperm1.
    rewrite -Hperm2.
    rewrite ?size_filter.
    rewrite -count_predT -count_predUI.
    rewrite (@eq_in_count _ (predI P Q) pred0); last first.
    { intros a Hin => //=. apply /negP. specialize (HPQ a). move /negP in HPQ. auto. }
    rewrite count_pred0 addn0.
    rewrite -count_uniq_mem //.
    rewrite -count_predUI //=.
    rewrite (@eq_in_count _ (predI (predU P Q) (pred1 a0)) pred0); last first.
    { intros a Hin => //=. apply /andP.  intros (Hor&Heq').  
      move /eqP in Heq'. move /orP in Hor. destruct Hor; subst; auto. }
    rewrite count_pred0 addn0. apply eq_in_count.
    intros a Hin. rewrite //=. symmetry. apply /orP. 
    specialize (Ha0 a). 
    destruct (P a) => //=; auto; [].
    destruct (Q a) => //=; auto; [].
    right. apply /eqP. apply Ha0; auto.
  }
  destruct l as [| a1 l]; last destruct l as [| a2 l].
  - subst.
    rewrite ?rand_perm_list_unfold ?ldist_left_id ?pr_mret_simpl //=.
    rewrite //= in Hperm1 Hperm2.
    rewrite perm_eq_sym in Hperm1. apply perm_eq_nil in Hperm1.
    rewrite perm_eq_sym in Hperm2. apply perm_eq_nil in Hperm2.
    subst. rewrite eq_refl //=. field.
  - rewrite ?rand_perm_list_unfold ?ldist_left_id ?pr_mret_simpl //=.
    rewrite //= in Hperm1 Hperm2.
    move: Hperm1 Hperm2.
    case: (P a1);
    case: (Q a1); 
    intros Hperm1; rewrite perm_eq_sym in Hperm1;
    intros Hperm2; rewrite perm_eq_sym in Hperm2;
    try (apply perm_eq_nil in Hperm1);
    try (apply perm_eq_singleton in Hperm1);
    try (apply perm_eq_nil in Hperm2);
    try (apply perm_eq_singleton in Hperm2);
    subst; rewrite ?eq_refl //=; field.
  - rewrite ?rand_perm_list_unfold ldist_assoc.
    destruct l1 as [| a1_ l1]; destruct l2 as [| a2_ l2].
    * exfalso.  apply perm_eq_nil in Hperm1. apply perm_eq_nil in Hperm2. 
      { assert (a1 = a2).
        { transitivity a0. 
          ** apply Ha0; split.
             *** move: Hperm1. rewrite //=. case: ifP; auto; try congruence.
             *** move: Hperm2. rewrite //=. case: ifP; auto; try congruence.
          ** symmetry; apply Ha0; split.
             *** move: Hperm1. rewrite //=. repeat case: ifP; auto; try congruence.
             *** move: Hperm2. rewrite //=. repeat case: ifP; auto; try congruence.
        }
        subst. rewrite //= in Huniq. move /andP in Huniq. rewrite in_cons eq_refl //= in Huniq. 
        intuition.
      }
    * rewrite pr_mbind_ldist2.
      assert (Q a2_) as HQa2.
      {
        cut (is_true (a2_ \in (filter Q [:: a1, a2 & l]))). 
        { rewrite mem_filter. move /andP. intuition. }
        rewrite (perm_eq_mem Hperm2) in_cons eq_refl //.
      }
      assert (Hpf: a2_ \in (a1 :: a2 :: l)). 
      { apply perm_eq_mem in Hperm2.
        specialize (Hperm2 a2_). rewrite mem_filter in Hperm2.
        symmetry in Hperm2. rewrite in_cons eq_refl //= in Hperm2.
        symmetry in Hperm2. move /andP in Hperm2. destruct Hperm2; auto.
      }
      rewrite (@big_rem _ _ _ _ (undup _) (exist _ (a2_) Hpf)); last first.
      { rewrite mem_undup. apply draw_next_all. auto. }
      case_eq (a0 \in (a1 :: a2 :: l)).
      ** intros Hpf'.
      rewrite (@big_rem _ _ _ _ (rem _ (undup _)) (exist _ (a0) Hpf')); last first.
      { 
        rewrite rem_filter; last apply undup_uniq.
        rewrite mem_filter. apply /andP; split.
        - rewrite //=. apply /eqP => Heq'. inversion Heq' as [[Heq'']].
            subst. auto.
        - rewrite mem_undup. by apply draw_next_all.
      }
      rewrite (rem_filter (exist _ _ Hpf')); last first.
      { apply rem_uniq, undup_uniq. }
      rewrite (rem_filter (exist _ a2_ Hpf)); last first.
      { apply undup_uniq. }
      rewrite -filter_predI.
      rewrite big_filter.
      rewrite big1. 
      { rewrite ?draw_next_pr //. 
        rewrite /sval. rewrite ?ldist_fmap_bind. simpl filter.
        rewrite HQa2.
        assert ( P a2_ = false) as ->.
        { apply /negP. intros HP. specialize (HPQ a2_). move /negP in (HPQ).
          apply HPQ. apply /andP. intuition. }
        assert ( P a0 = false) as -> by (apply /negP; auto).
        assert ( Q a0 = false) as -> by (apply /negP; auto).
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (fst ls, a2_ :: snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (fst ls, a2_ :: snd ls)) ([::], l2)); last first.
        { intros (?&?) (?&?). rewrite //=. inversion 1. congruence. }
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (fst ls, snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (fst ls, snd ls)) ([::], l2)); last first.
        { intros (?&?) (?&?). rewrite //=. }
        rewrite (IH (size (rem a2_ [:: a1, a2 & l]))); eauto;
        try (rewrite size_rem //=); try (by apply rem_uniq);
        first (rewrite (IH (size (rem a0 [:: a1, a2 & l]))));
        try (rewrite size_rem //=); try by apply rem_uniq.
        **** simpl size. rewrite fact0. replace (INR 1) with 1 by auto. 
             rewrite ?S_INR ?factS mult_INR ?S_INR //=.
             rewrite Hpf' //= in Hsize_combine.
             assert (size l = size l2) as ->.
             { nify. omega. }
             field => //=.
             specialize (INR_fact_gt0 (size l2)); intros.
             specialize (pos_INR (size l2)); intros.
             repeat split; nra.
        **** subst. rewrite //=.
        **** rewrite filter_rem. replace [::] with (rem a0 [::]) by auto. 
             apply perm_eq_rem. done.
        **** rewrite filter_rem. replace (a2_ :: l2) with (rem a0 (a2_ :: l2)); first
             by apply perm_eq_rem.
             rewrite rem_id //. apply /negP.
             rewrite -(perm_eq_mem Hperm2) mem_filter. move /andP. intros (?&?); auto.
        **** subst. rewrite //=.
        **** rewrite filter_rem. replace [::] with (rem a2_ [::]) by auto. 
             apply perm_eq_rem. done.
        **** rewrite filter_rem. replace (l2) with (rem a2_ (a2_ :: l2)); first
             by apply perm_eq_rem.
             rewrite //= eq_refl. done.
      }
      intros (i&?) Hin. apply Rmult_eq_0_compat_l. 
      rewrite //= in Hin.
      rewrite ldist_fmap_bind. 
      apply pr_mbind_mret_inj0. intros lrest.
      intros Heq'. inversion Heq' as [[Heq1 Heq2]].
      case_eq (P i); first (intros HP; rewrite HP in Heq1; inversion Heq1).
      intros HnP.
      case_eq (Q i). 
      { intros HQ. rewrite HQ in Heq2. inversion Heq2. move /andP in Hin.
        destruct Hin as (_&Hin). move /negP in Hin. apply Hin. subst.
        apply /eqP; f_equal. apply bool_irrelevance. }
      intros HnQ.
      assert (i = a0).
      { apply Ha0. rewrite HnP HnQ //. }
      subst.
      move /andP in Hin. destruct Hin as (Hin&?). move /negP in Hin. apply Hin. subst.
      apply /eqP; f_equal. apply bool_irrelevance.
      ** intros Hpf'.
      rewrite (rem_filter (exist _ a2_ Hpf)); last first.
      { apply undup_uniq. }
      rewrite big_filter.
      rewrite big1. 
      { rewrite ?draw_next_pr //. 
        rewrite /sval. rewrite ?ldist_fmap_bind. simpl filter.
        rewrite HQa2.
        assert ( P a2_ = false) as ->.
        { apply /negP. intros HP. specialize (HPQ a2_). move /negP in (HPQ).
          apply HPQ. apply /andP. intuition. }
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (fst ls, a2_ :: snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (fst ls, a2_ :: snd ls)) ([::], l2)); last first.
        { intros (?&?) (?&?). rewrite //=. inversion 1. congruence. }
        rewrite (IH (size (rem a2_ [:: a1, a2 & l]))); eauto;
        try (rewrite size_rem //=); try (by apply rem_uniq).
        **** simpl size. rewrite fact0. replace (INR 1) with 1 by auto. 
             rewrite ?S_INR ?factS mult_INR ?S_INR //=.
             rewrite Hpf' //= in Hsize_combine.
             assert (S (size l) = size l2) as <-.
             { nify. omega. }
             rewrite factS mult_INR ?S_INR.
             field => //=.
             specialize (INR_fact_gt0 (size l)); intros.
             specialize (pos_INR (size l)); intros.
             repeat split; nra.
        **** subst. rewrite //=.
        **** rewrite filter_rem. replace [::] with (rem a2_ [::]) by auto. 
             apply perm_eq_rem. done.
        **** rewrite filter_rem. replace (l2) with (rem a2_ (a2_ :: l2)); first
             by apply perm_eq_rem.
             rewrite //= eq_refl. done.
      }
      intros (i&Hin') Hin. apply Rmult_eq_0_compat_l. 
      rewrite //= in Hin.
      rewrite ldist_fmap_bind. 
      apply pr_mbind_mret_inj0. intros lrest.
      intros Heq'. inversion Heq' as [[Heq1 Heq2]].
      case_eq (P i); first (intros HP; rewrite HP in Heq1; inversion Heq1).
      intros HnP.
      case_eq (Q i). 
      { intros HQ. rewrite HQ in Heq2. inversion Heq2. 
        move /negP in Hin. apply Hin. subst.
        apply /eqP; f_equal. apply bool_irrelevance. }
      intros HnQ.
      assert (i = a0).
      { apply Ha0. rewrite HnP HnQ //. }
      subst. clear -Hin' Hpf'. move /negP in Hpf'. apply Hpf'. 
      rewrite /in_mem. done.
    * rewrite pr_mbind_ldist2.
      assert (P a1_) as HPa2.
      {
        cut (is_true (a1_ \in (filter P [:: a1, a2 & l]))). 
        { rewrite mem_filter. move /andP. intuition. }
        rewrite (perm_eq_mem Hperm1) in_cons eq_refl //.
      }
      assert (Hpf: a1_ \in (a1 :: a2 :: l)). 
      { apply perm_eq_mem in Hperm1.
        specialize (Hperm1 a1_). rewrite mem_filter in Hperm1.
        symmetry in Hperm1. rewrite in_cons eq_refl //= in Hperm1.
        symmetry in Hperm1. move /andP in Hperm1. destruct Hperm1; auto.
      }
      rewrite (@big_rem _ _ _ _ (undup _) (exist _ (a1_) Hpf)); last first.
      { rewrite mem_undup. apply draw_next_all. auto. }
      case_eq (a0 \in (a1 :: a2 :: l)).
      ** intros Hpf'.
      rewrite (@big_rem _ _ _ _ (rem _ (undup _)) (exist _ (a0) Hpf')); last first.
      { 
        rewrite rem_filter; last apply undup_uniq.
        rewrite mem_filter. apply /andP; split.
        - rewrite //=. apply /eqP => Heq'. inversion Heq' as [[Heq'']].
            subst. auto.
        - rewrite mem_undup. by apply draw_next_all.
      }
      rewrite (rem_filter (exist _ _ Hpf')); last first.
      { apply rem_uniq, undup_uniq. }
      rewrite (rem_filter (exist _ a1_ Hpf)); last first.
      { apply undup_uniq. }
      rewrite -filter_predI.
      rewrite big_filter.
      rewrite big1. 
      { rewrite ?draw_next_pr //. 
        rewrite /sval. rewrite ?ldist_fmap_bind. simpl filter.
        rewrite HPa2.
        assert ( Q a1_ = false) as ->.
        { apply /negP. intros HP. specialize (HPQ a1_). move /negP in (HPQ).
          apply HPQ. apply /andP. intuition. }
        assert ( P a0 = false) as -> by (apply /negP; auto).
        assert ( Q a0 = false) as -> by (apply /negP; auto).
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (a1_ :: fst ls,  snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (a1_ :: fst ls,  snd ls)) (l1, [::])); last first.
        { intros (?&?) (?&?). rewrite //=. inversion 1. congruence. }
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (fst ls, snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (fst ls, snd ls)) (l1, [::])); last first.
        { intros (?&?) (?&?). rewrite //=. }
        rewrite (IH (size (rem a1_ [:: a1, a2 & l]))); eauto;
        try (rewrite size_rem //=); try (by apply rem_uniq);
        first (rewrite (IH (size (rem a0 [:: a1, a2 & l]))));
        try (rewrite size_rem //=); try by apply rem_uniq.
        **** simpl size. rewrite fact0. replace (INR 1) with 1 by auto. 
             rewrite ?S_INR ?factS mult_INR ?S_INR //=.
             rewrite Hpf' //= in Hsize_combine.
             assert (size l = size l1) as ->.
             { nify. omega. }
             field => //=.
             specialize (INR_fact_gt0 (size l1)); intros.
             specialize (pos_INR (size l1)); intros.
             repeat split; nra.
        **** subst. rewrite //=.
        **** rewrite filter_rem. replace (a1_ :: l1) with (rem a0 (a1_ :: l1)); first
             by apply perm_eq_rem.
             rewrite rem_id //. apply /negP.
             rewrite -(perm_eq_mem Hperm1) mem_filter. move /andP. intros (?&?); auto.
        **** rewrite filter_rem. replace [::] with (rem a0 [::]) by auto. 
             apply perm_eq_rem. done.
        **** subst. rewrite //=.
        **** rewrite filter_rem. replace (l1) with (rem a1_ (a1_ :: l1)); first
             by apply perm_eq_rem.
             rewrite //= eq_refl. done.
        **** rewrite filter_rem. replace [::] with (rem a1_ [::]) by auto. 
             apply perm_eq_rem. done.
      }
      intros (i&?) Hin. apply Rmult_eq_0_compat_l. 
      rewrite //= in Hin.
      rewrite ldist_fmap_bind. 
      apply pr_mbind_mret_inj0. intros lrest.
      intros Heq'. inversion Heq' as [[Heq1 Heq2]].
      case_eq (Q i); first (intros HQ; rewrite HQ in Heq2; inversion Heq2).
      intros HnQ.
      case_eq (P i). 
      { intros HP. rewrite HP in Heq1. inversion Heq1. move /andP in Hin.
        destruct Hin as (_&Hin). move /negP in Hin. apply Hin. subst.
        apply /eqP; f_equal. apply bool_irrelevance. }
      intros HnP.
      assert (i = a0).
      { apply Ha0. rewrite HnP HnQ //. }
      subst.
      move /andP in Hin. destruct Hin as (Hin&?). move /negP in Hin. apply Hin. subst.
      apply /eqP; f_equal. apply bool_irrelevance.
      ** intros Hpf'.
      rewrite (rem_filter (exist _ a1_ Hpf)); last first.
      { apply undup_uniq. }
      rewrite big_filter.
      rewrite big1. 
      { rewrite ?draw_next_pr //. 
        rewrite /sval. rewrite ?ldist_fmap_bind. simpl filter.
        rewrite HPa2.
        assert ( Q a1_ = false) as ->.
        { apply /negP. intros HP. specialize (HPQ a1_). move /negP in (HPQ).
          apply HPQ. apply /andP. intuition. }
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (a1_ :: fst ls,  snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (a1_ :: fst ls, snd ls)) (l1, [::])); last first.
        { intros (?&?) (?&?). rewrite //=. inversion 1. congruence. }
        rewrite (IH (size (rem a1_ [:: a1, a2 & l]))); eauto;
        try (rewrite size_rem //=); try (by apply rem_uniq).
        **** simpl size. rewrite fact0. replace (INR 1) with 1 by auto. 
             rewrite ?S_INR ?factS mult_INR ?S_INR //=.
             rewrite Hpf' //= in Hsize_combine.
             assert (S (size l) = size l1) as <-.
             { nify. omega. }
             rewrite factS mult_INR ?S_INR.
             field => //=.
             specialize (INR_fact_gt0 (size l)); intros.
             specialize (pos_INR (size l)); intros.
             repeat split; nra.
        **** subst. rewrite //=.
        **** rewrite filter_rem. replace (l1) with (rem a1_ (a1_ :: l1)); first
             by apply perm_eq_rem.
             rewrite //= eq_refl. done.
        **** rewrite filter_rem. replace [::] with (rem a1_ [::]) by auto. 
             apply perm_eq_rem. done.
      }
      intros (i&Hin') Hin. apply Rmult_eq_0_compat_l. 
      rewrite //= in Hin.
      rewrite ldist_fmap_bind. 
      apply pr_mbind_mret_inj0. intros lrest.
      intros Heq'. inversion Heq' as [[Heq1 Heq2]].
      case_eq (Q i); first (intros HQ; rewrite HQ in Heq2; inversion Heq2).
      intros HnQ.
      case_eq (P i). 
      { intros HP. rewrite HP in Heq1. inversion Heq1.
        move /negP in Hin. apply Hin. subst.
        apply /eqP; f_equal. apply bool_irrelevance. }
      intros HnP.
      assert (i = a0).
      { apply Ha0. rewrite HnP HnQ //. }
      subst. clear -Hin' Hpf'. move /negP in Hpf'. apply Hpf'. 
      rewrite /in_mem. done.
    * rewrite pr_mbind_ldist2.
      assert (P a1_) as HPa1.
      {
        cut (is_true (a1_ \in (filter P [:: a1, a2 & l]))). 
        { rewrite mem_filter. move /andP. intuition. }
        rewrite (perm_eq_mem Hperm1) in_cons eq_refl //.
      }
      assert (Q a2_) as HQa2.
      {
        cut (is_true (a2_ \in (filter Q [:: a1, a2 & l]))). 
        { rewrite mem_filter. move /andP. intuition. }
        rewrite (perm_eq_mem Hperm2) in_cons eq_refl //.
      }
      assert (Hpf1: a1_ \in (a1 :: a2 :: l)). 
      { apply perm_eq_mem in Hperm1.
        specialize (Hperm1 a1_). rewrite mem_filter in Hperm1.
        symmetry in Hperm1. rewrite in_cons eq_refl //= in Hperm1.
        symmetry in Hperm1. move /andP in Hperm1. destruct Hperm1; auto.
      }
      rewrite (@big_rem _ _ _ _ (undup _) (exist _ (a1_) Hpf1)); last first.
      { rewrite mem_undup. apply draw_next_all. auto. }
      assert (Hpf2: a2_ \in ((a1 :: a2 :: l))).
      { apply perm_eq_mem in Hperm2.
        specialize (Hperm2 a2_). rewrite mem_filter in Hperm2.
        symmetry in Hperm2. rewrite in_cons eq_refl //= in Hperm2.
        symmetry in Hperm2. move /andP in Hperm2. destruct Hperm2; auto.
      }
      rewrite (@big_rem _ _ _ _ (rem _ (undup _)) (exist _ (a2_) Hpf2)); last first.
      { rewrite rem_filter; last by apply undup_uniq. rewrite mem_filter mem_undup.
        apply /andP; split.
        * rewrite //=. apply /eqP. intros Heq'. inversion Heq'. subst.
          specialize (HPQ a1_). move /negP in HPQ. apply HPQ. apply /andP; split; auto.
        * apply draw_next_all; auto. 
      }
      case_eq (a0 \in (a1 :: a2 :: l)).
      ** intros Hpf'.
      rewrite (@big_rem _ _ _ _ (rem _ (rem _ (undup _))) (exist _ (a0) Hpf')); last first.
      { 
        rewrite ?rem_filter //; [| apply undup_uniq | apply filter_uniq, undup_uniq 
                                 | apply undup_uniq ].
        rewrite ?mem_filter. repeat (apply /andP; split).
        - rewrite //=. apply /eqP => Heq'. inversion Heq' as [[Heq'']].
            subst. auto.
        - rewrite //=. apply /eqP => Heq'. inversion Heq' as [[Heq'']].
            subst. auto.
        - rewrite mem_undup. by apply draw_next_all.
      }
      rewrite (rem_filter (exist _ _ Hpf')); last first.
      { apply rem_uniq, rem_uniq, undup_uniq. }
      rewrite (rem_filter (exist _ a1_ Hpf1)); last first.
      { apply undup_uniq. }
      rewrite (rem_filter (exist _ a2_ Hpf2)); last first.
      { apply filter_uniq, undup_uniq. }
      rewrite -?filter_predI.
      rewrite big_filter.
      rewrite big1. 
      { rewrite ?draw_next_pr //. 
        rewrite /sval. rewrite ?ldist_fmap_bind. simpl filter.
        rewrite HPa1 HQa2.
        assert ( Q a1_ = false) as HnQ1.
        { apply /negP. intros HP. specialize (HPQ a1_). move /negP in (HPQ).
          apply HPQ. apply /andP. intuition. }
        rewrite HnQ1.
        assert ( P a2_ = false) as HnP2.
        { apply /negP. intros HP. specialize (HPQ a2_). move /negP in (HPQ).
          apply HPQ. apply /andP. intuition. }
        rewrite HnP2.
        assert ( P a0 = false) as -> by (apply /negP; auto).
        assert ( Q a0 = false) as -> by (apply /negP; auto).
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (fst ls, snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (fst ls, snd ls)) (a1_ :: l1, a2_ ::l2)); last first.
        { intros (?&?) (?&?). rewrite //=. }
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (a1_ :: fst ls,  snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (a1_ :: fst ls,  snd ls)) (l1, a2_ :: l2)); last first.
        { intros (?&?) (?&?). rewrite //=. inversion 1. congruence. }
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (fst ls,  a2_ :: snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (fst ls,  a2_ :: snd ls)) (a1_ :: l1, l2)); last first.
        { intros (?&?) (?&?). rewrite //=. inversion 1. congruence. }
        rewrite (IH (size (rem a1_ [:: a1, a2 & l]))); eauto;
        try (rewrite size_rem //=); try (by apply rem_uniq);
        first rewrite (IH (size (rem a2_ [:: a1, a2 & l]))); eauto;
        try (rewrite size_rem //=); try (by apply rem_uniq);
        first (rewrite (IH (size (rem a0 [:: a1, a2 & l]))));
        try (rewrite size_rem //=); try by apply rem_uniq.
        **** simpl size. replace (INR 1) with 1 by auto. 
             rewrite ?S_INR ?factS mult_INR ?S_INR //=.
             rewrite Hpf' //= in Hsize_combine.
             assert (size l = size l1 + size l2 + 1)%nat as ->.
             { nify. omega. }
             rewrite ?S_INR ?factS ?plus_INR ?mult_INR ?S_INR //=.
             field => //=.
             specialize (INR_fact_gt0 (size l1)); intros.
             specialize (INR_fact_gt0 (size l2)); intros.
             specialize (pos_INR (size l1)); intros.
             specialize (pos_INR (size l2)); intros.
             repeat split; nra.
        **** subst. rewrite //=.
        **** rewrite filter_rem. replace (a1_ :: l1) with (rem a0 (a1_ :: l1)); first
             by apply perm_eq_rem.
             rewrite rem_id //. apply /negP.
             rewrite -(perm_eq_mem Hperm1) mem_filter. move /andP. intros (?&?); auto.
        **** rewrite filter_rem. replace (a2_ :: l2) with (rem a0 (a2_ :: l2)); first
             by apply perm_eq_rem. 
             rewrite rem_id //. apply /negP.
             rewrite -(perm_eq_mem Hperm2) mem_filter. move /andP. intros (?&?); auto.
        **** subst. rewrite //=.
        **** rewrite filter_rem. replace (a1_ :: l1) with (rem a2_ (a1_ :: l1)); first
             by apply perm_eq_rem.
             rewrite rem_id //. apply /negP.
             rewrite -(perm_eq_mem Hperm1) mem_filter. move /andP. intros (?&?); auto.
             move /negP in HnP2. auto.
        **** rewrite filter_rem. replace (l2) with (rem a2_ (a2_ :: l2)); first
             by apply perm_eq_rem.
             rewrite //= eq_refl. done.
        **** subst. rewrite //=. 
        **** rewrite filter_rem. replace (l1) with (rem a1_ (a1_ :: l1)); first
             by apply perm_eq_rem.
             rewrite //= eq_refl. done.
        **** rewrite filter_rem. replace (a2_ :: l2) with (rem a1_ (a2_ :: l2)); first
             by apply perm_eq_rem.
             rewrite rem_id //. apply /negP.
             rewrite -(perm_eq_mem Hperm2) mem_filter. move /andP. intros (?&?); auto.
             move /negP in HnQ1. auto.
      }
      intros (i&?) Hin. apply Rmult_eq_0_compat_l. 
      rewrite //= in Hin.
      rewrite ldist_fmap_bind. 
      apply pr_mbind_mret_inj0. intros lrest.
      intros Heq'. inversion Heq' as [[Heq1 Heq2]].
      case_eq (Q i). 
      { intros HQ. rewrite HQ in Heq2. inversion Heq2. move /andP in Hin.
        destruct Hin as (Hin&_). move /andP in Hin. destruct Hin as (_&Hin).
        move /negP in Hin. apply Hin. subst.
        apply /eqP; f_equal. apply bool_irrelevance. }
      intros HnQ.
      case_eq (P i). 
      { intros HP. rewrite HP in Heq1. inversion Heq1. move /andP in Hin.
        destruct Hin as (_&Hin). move /negP in Hin. apply Hin. subst.
        apply /eqP; f_equal. apply bool_irrelevance. }
      intros HnP.
      assert (i = a0).
      { apply Ha0. rewrite HnP HnQ //. }
      subst.
      move /andP in Hin. destruct Hin as (Hin&?). move /andP in Hin. 
      destruct Hin as (Hin&_). move /negP in Hin. apply Hin.
      apply /eqP; f_equal. apply bool_irrelevance.
      ** intros Hpf'.
      rewrite (rem_filter (exist _ a1_ Hpf1)); last first.
      { apply undup_uniq. }
      rewrite (rem_filter (exist _ a2_ Hpf2)); last first.
      { apply filter_uniq, undup_uniq. }
      rewrite -?filter_predI.
      rewrite big_filter.
      rewrite big1. 
      { rewrite ?draw_next_pr //. 
        rewrite /sval. rewrite ?ldist_fmap_bind. simpl filter.
        rewrite HPa1.
        rewrite HQa2.
        assert ( Q a1_ = false) as HnQ1.
        { apply /negP. intros HP. specialize (HPQ a1_). move /negP in (HPQ).
          apply HPQ. apply /andP. intuition. }
        rewrite HnQ1.
        assert ( P a2_ = false) as HnP2.
        { apply /negP. intros HP. specialize (HPQ a2_). move /negP in (HPQ).
          apply HPQ. apply /andP. intuition. }
        rewrite HnP2.
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (a1_ :: fst ls,  snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (a1_ :: fst ls,  snd ls)) (l1, a2_ :: l2)); last first.
        { intros (?&?) (?&?). rewrite //=. inversion 1. congruence. }
        rewrite -(ldist_fmap_bind _ (λ l, ([seq x <- l | P x],
                                           [seq x <- l | Q x])) 
                                  (λ ls, mret (fst ls,  a2_ :: snd ls))).
        rewrite (pr_mbind_mret_inj _ (λ ls, (fst ls,  a2_ :: snd ls)) (a1_ :: l1, l2)); last first.
        { intros (?&?) (?&?). rewrite //=. inversion 1. congruence. }
        rewrite (IH (size (rem a1_ [:: a1, a2 & l]))); eauto;
        try (rewrite size_rem //=); try (by apply rem_uniq);
        first rewrite (IH (size (rem a2_ [:: a1, a2 & l]))); eauto;
        try (rewrite size_rem //=); try by apply rem_uniq.
        **** simpl size. replace (INR 1) with 1 by auto. 
             rewrite ?S_INR ?factS mult_INR ?S_INR //=.
             rewrite Hpf' //= in Hsize_combine.
             assert (size l = size l1 + size l2)%nat as ->.
             { nify. omega. }
             rewrite ?S_INR ?factS ?plus_INR ?mult_INR ?S_INR //=.
             field => //=.
             specialize (INR_fact_gt0 (size l1)); intros.
             specialize (INR_fact_gt0 (size l2)); intros.
             specialize (pos_INR (size l1)); intros.
             specialize (pos_INR (size l2)); intros.
             repeat split; nra.
        **** subst. rewrite //=.
        **** rewrite filter_rem. replace (a1_ :: l1) with (rem a2_ (a1_ :: l1)); first
             by apply perm_eq_rem.
             rewrite rem_id //. apply /negP.
             rewrite -(perm_eq_mem Hperm1) mem_filter. move /andP. intros (?&?); auto.
             move /negP in HnP2. auto.
        **** rewrite filter_rem. replace (l2) with (rem a2_ (a2_ :: l2)); first
             by apply perm_eq_rem.
             rewrite //= eq_refl. done.
        **** subst. rewrite //=. 
        **** rewrite filter_rem. replace (l1) with (rem a1_ (a1_ :: l1)); first
             by apply perm_eq_rem.
             rewrite //= eq_refl. done.
        **** rewrite filter_rem. replace (a2_ :: l2) with (rem a1_ (a2_ :: l2)); first
             by apply perm_eq_rem.
             rewrite rem_id //. apply /negP.
             rewrite -(perm_eq_mem Hperm2) mem_filter. move /andP. intros (?&?); auto.
             move /negP in HnQ1. auto.
      }
      intros (i&Hin') Hin. apply Rmult_eq_0_compat_l. 
      rewrite //= in Hin.
      rewrite ldist_fmap_bind. 
      apply pr_mbind_mret_inj0. intros lrest.
      intros Heq'. inversion Heq' as [[Heq1 Heq2]].
      case_eq (Q i). 
      { intros HQ. rewrite HQ in Heq2. inversion Heq2. move /andP in Hin.
        destruct Hin as (Hin&_). move /negP in Hin. apply Hin. subst.
        apply /eqP; f_equal. apply bool_irrelevance. }
      intros HnQ.
      case_eq (P i). 
      { intros HP. rewrite HP in Heq1. inversion Heq1. move /andP in Hin.
        destruct Hin as (_&Hin). move /negP in Hin. apply Hin. subst.
        apply /eqP; f_equal. apply bool_irrelevance. }
      intros HnP.
      assert (i = a0).
      { apply Ha0. rewrite HnP HnQ //. }
      subst. clear -Hin' Hpf'. move /negP in Hpf'. apply Hpf'. 
      rewrite /in_mem. done.
Qed.

Local Open Scope nat_scope.
Lemma rand_perm_list_split l (x: nat): 
  uniq l →
      eq_dist (rvar_of_ldist (l' ← rand_perm_list l;
                                mret ([seq i <- l' | i < x], [seq i <- l' | x < i])))
              (rvar_of_ldist 
                 (l1 ← rand_perm_list [seq i <- l | i < x];
                  l2 ← rand_perm_list [seq i <- l | x < i];
                  mret (l1, l2))).
Proof.  
  intros Huniq.
  apply (mspec_range_eq_dist _ _ (λ ls, (perm_eq [seq i <- l | i < x]) (fst ls) &&
                                        (perm_eq [seq i <- l | x < i]) (snd ls))).
  { 
    eapply mspec_mbind; first apply rand_perm_list_correct. intros l' Hperm.
    apply mspec_mret => //=. apply /andP; split; apply quicksort_cost.perm_filter, Hperm.
  }
  {
    eapply mspec_mbind; first apply rand_perm_list_correct. intros l1 Hperm1.
    eapply mspec_mbind; first apply rand_perm_list_correct. intros l2 Hperm2.
    apply mspec_mret => //=. apply /andP; split;  try apply Hperm1; try apply Hperm2.
  }
  intros (l1&l2). move /andP. intros (Hperm1&Hperm2).
  rewrite (pr_shuffle_then_split _ _ _ _ _ x) //=.
  * intros. rewrite pr_eq_bind_pair.
    rewrite ?pr_rand_perm_list //. 
    ** apply perm_eq_size in Hperm1. rewrite Hperm1 //.
       apply perm_eq_size in Hperm2. rewrite Hperm2 //.
    ** by apply filter_uniq.
    ** by apply filter_uniq.
  * intros a; split.
    ** intros (Hnlt&Hngt).
       move /ltP in Hnlt.
       move /ltP in Hngt.
       omega.
    ** intros ->. split; apply /ltP; omega.
  * intros a. apply /andP. intros (Hlt1&Hlt2).
    move /ltP in Hlt1.
    move /ltP in Hlt2.
    omega.
Qed.
