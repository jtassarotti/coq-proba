From discprob.basic Require Import base order nify seq_ext.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad monad_hoare bst bst_correct permutation.
From discprob.monad Require Import max_triangle.
From discprob.rec Require Import rec_convert quicksort_rec.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From mathcomp Require Import path.
Require Import Reals Fourier Psatz Omega.

Definition h (l: seq nat) :=
  match l with
  | [::] => mret ([::], [::])
  | [::a] => mret ([::], [::])
  | a :: l => 
      p ← draw_next a l;
      mret ([seq i <- a :: l | i < sval p], [seq i <- a :: l | i > sval p])%nat
  end.

Definition rsize (l: seq nat) := INR (size l).

Definition m x :=
  match (Rlt_dec x (4/3)) with
  | left _ => 0
  | _ => x * (3 / 4)
  end.

Lemma uniq_unif n:
  uniq (outcomes (unif n)).
Proof.
  rewrite /unif//=.
  rewrite map_inj_uniq.
  - apply enum_uniq.
  - intros (?&?) (?&?). inversion 1; auto.
    subst; f_equal. apply bool_irrelevance.
Qed.

Lemma uniq_unif2 n:
  uniq ([seq i.2 | i <- outcomes (unif n)]).
Proof.
  rewrite /unif//=.
  rewrite map_inj_in_uniq.
  - apply uniq_unif.
  - intros (?&?) (?&?).
    move /mapP => [? ? Heq1]. inversion Heq1; subst.
    move /mapP => [? ? Heq2]. inversion Heq2; subst.
    rewrite //=. inversion 1. repeat f_equal. 
    apply val_inj => //=.
Qed.

Lemma Ex_max_partition_sum l: 
  Ex (rvar_comp (rvar_of_ldist (h l)) (λ x, Rmax (rsize (x.1)) (rsize (x.2)))) <=
  match (size l) with
     | O => 0
     | _ => \big[Rplus/0]_(i < size l) (/INR (size l) * (Rmax (INR i) (INR (size l - i - 1))))
  end.
Proof.
  destruct l as [| a l].
  - rewrite Ex_fin_comp.
    rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ (_ (fst a)) (_ (snd a)))).
    rewrite img_rvar_of_ldist//=/img/undup//= !big_cons ?big_nil.
    rewrite pr_mret_simpl //= /m/rsize//=.
    rewrite Rmax_left //; last (fourier). 
    rewrite /INR. ring_simplify. fourier. 
  - destruct l as [| b0 l0].
    { 
      rewrite Ex_fin_comp. 
      rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ (_ (fst a)) (_ (snd a)))).
      rewrite img_rvar_of_ldist//=/img/undup//= !big_cons ?big_nil.
      rewrite pr_mret_simpl //= /m/rsize//=.
      rewrite Rmax_left //; last (fourier). 
      replace (INR 0) with 0 by auto. ring_simplify. 
      apply Rle_big0 => i _ //=.
      destruct i as (i&Hlt) => //=. assert (i = O) as -> by (nify; omega). 
      replace (1 - 0 - 1)%nat with O by (nify; omega).
      replace (INR 0) with 0 by auto. rewrite Rmax_left; last fourier. 
      replace (INR 1) with 1 by auto. fourier.
    }
    remember (b0 :: l0) as l eqn:Heql0.

    replace (size (a :: l)) with (S (size l)) by auto. 
    rewrite -(Ex_mbind_mret (h (a :: l))).
    rewrite /h Heql0. rewrite -Heql0. clear l0 Heql0.

    rewrite ldist_assoc. rewrite ldist_assoc.
    rewrite Ex_mbind_ldist2.
    rewrite undup_id; last first.
    { apply uniq_unif2. } 
    edestruct (quicksort_cost.perm_eq_bij a) as (f&Hfspec&Hfsize&Hinv&Hinj).
    { rewrite perm_eq_sym. apply (perm_eqlE (perm_sort leq (a :: l))). }
    eapply sum_reidx_map_le with 
        (h := (λ (H : {x : nat | (x <= size l)%nat}), 
               let (x, i) := H in 
                (Ordinal (n:=(size l).+1) (m:=f x) (Hfsize x i)))).
    * intros (x, Hle) Hin. 
      rewrite unif_pr. rewrite /Rdiv Rmult_1_l. apply Rmult_le_compat_l. 
      ** left. apply Rinv_0_lt_compat. apply lt_0_INR. rewrite //=. omega. 
      ** rewrite -ldist_assoc. rewrite Ex_mbind_mret. 
         apply Ex_bound. 
         rewrite ?ldist_left_id.
         assert (Hlt: (x < size (a :: l))%nat) by auto.
         rewrite //= in Hlt.
         apply mspec_mret. rewrite /sval/nat_of_ord.
         remember (a :: l) as l0 eqn:Heql0.
         rewrite -Heql0.
         assert (Hsize: S (size l) = (size l0)) by (rewrite Heql0; auto).
         rewrite /rsize. 
         rewrite !Rmax_INR. apply le_INR. 
         apply Nat.max_le_compat; rewrite /fst/snd.
         *** apply /leP. rewrite Hfspec. 
             specialize (perm_eqlE (perm_sort leq l0)) => Hperm.
             rewrite //= -(perm_eq_size (quicksort_cost.perm_filter _ _ Hperm)).
             apply quicksort_cost.lower_split_size_sorted_nth; auto.
             **** apply sort_sorted => ??. apply leq_total.
             **** rewrite (perm_eq_size (perm_eqlE (perm_sort leq l0))) /=.
                  apply Hfsize. rewrite Heql0. done.
             **** rewrite Heql0 //=.
         *** apply /leP. rewrite Hfspec. 
             assert (Hsize': (size l).+1 = size l0) by rewrite Heql0 //.
             rewrite Hsize'. 
             specialize (perm_eqlE (perm_sort leq l0)) => Hperm.
             rewrite -(perm_eq_size (perm_eqlE (perm_sort leq l0))).
             rewrite -(perm_eq_size (quicksort_cost.perm_filter _ _ Hperm)).
             apply quicksort_cost.upper_split_size_sorted_nth; auto.
             **** apply sort_sorted => ??. apply leq_total.
             **** rewrite (perm_eq_size (perm_eqlE (perm_sort leq l0))) /=. 
                  apply Hfsize. rewrite Heql0. done.
             **** rewrite Heql0 //=.
      ** apply unif_all. 
    * intros (?&?) Hin; split; auto. 
      rewrite /index_enum. rewrite -enumT. rewrite mem_enum => //=.
    * intros b Hin _ Hfalse. contradiction Hfalse.
      destruct b as (m, Hle).
      destruct (Hinv m Hle) as (x'&Hle'&Heq).
      exists (exist _ x' Hle'); repeat split; auto.
      ** apply unif_all.
      ** apply ord_inj => //=.
    * apply uniq_unif2.  
    * rewrite /index_enum. rewrite -enumT. apply enum_uniq.
    * intros (?&?) (?&?) _ => //=. inversion 1; subst. apply /val_inj/Hinj => //=.
Qed.

Lemma Ex_max_partition l: 
  Ex (rvar_comp (rvar_of_ldist (h l)) (λ x, Rmax (rsize (x.1)) (rsize (x.2)))) <=
   m (rsize l).
Proof.
  eapply Rle_trans; [ apply Ex_max_partition_sum | apply quicksort_cost.sum_le_m ].
Qed.


Definition T := λ x, rvar_comp (rvar_of_ldist (add_list_random x Leaf)) (λ x, INR (height x)).
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

Lemma rand_tree_non_empty_non_leaf l:
  mspec (rand_tree_rec l) (λ t, l ≠ [::] → t ≠ Leaf).
Proof.
  destruct l; [| destruct l]; first congruence. 
  - rewrite rt_unfold. apply mspec_mret; congruence.
  - rewrite rt_unfold. do 3 (tbind (λ x, true) => //; intros). apply mspec_mret; congruence.
Qed.

Lemma filter_lt_gt_non_empty l x:
  (size l > 1)%nat →
  uniq l →
  [seq i <- l | (i < x)%nat] ≠ [::] ∨
  [seq i <- l | (x < i)%nat] ≠ [::].
Proof.
  intros Hsize Huniq.
  induction l as [| a l]; first by auto.
  induction l as [| b l]; first by auto.
  rewrite //=.
  repeat case: ifP;  try (left; congruence); try (right; congruence).
  move /ltP. intros Hlt1.
  move /ltP. intros Hlt2.
  move /ltP. intros Hlt3.
  move /ltP. intros Hlt4.
  assert (a = x).
  { omega. }
  assert (b = x).
  { omega. }
  subst. rewrite //= in Huniq. exfalso. move /andP in Huniq.
  destruct Huniq as (Hfalse&?). move /negP in Hfalse. apply Hfalse.
  by rewrite in_cons eq_refl.
Qed.

Lemma huniq l n:
  uniq l → uniq (fst ((h' l) n)) ∧ uniq (snd ((h' l) n)).
Proof.
  intros Huniq. rewrite //=.  
  cut (∀ n, uniq ((fst (rvar_of_ldist (h l) n))) ∧
          uniq ((snd (rvar_of_ldist (h l) n)))); first by rewrite //=.
  intros n'. apply fun_to_mspec.
  rewrite /h.
  destruct l as [| a l].
  { apply mspec_mret => //=. }
  destruct l as [| b l0].
  { apply mspec_mret => //=. }
  remember (b::l0) as l eqn:Heql0.
  clear b l0 Heql0.
  tbind (λ x, true). 
  { intros (?&?) => //. }
  intros ??. 
  apply mspec_mret.
  split; apply filter_uniq => //.
Qed.

Lemma Trec: 
    ∀ x r, uniq x → pr_eq (T x) r = 
            \big[Rplus/0]_(x' : imgT (h' x)) 
                        (pr_eq (h' x) (sval x') * 
                         pr_eq (rvar_comp (rvar_pair (T (fst (sval x'))) (T (snd (sval x'))))
                                         (fun xy => Rmax (fst xy) (snd xy))) (r - a (rsize x))).
Proof.
  eapply eq_dist_rec; [ apply huniq | | ]; last first.
  { rewrite /T. intros. apply eq_dist_comp. eapply eq_dist_trans; first apply alr_rand_perm.
    apply eq_dist_sym, rt_gen_perm. done. }
  intros ls r.
  induction ls as [| a0 ls] => Huniq.
  - rewrite /T. rewrite -pr_mbind_mret. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' [::]) x' *
      pr_eq (rvar_comp
               (rvar_pair
                  (rvar_comp (rvar_of_ldist (rand_tree_rec x'.1)) (λ x, INR (height x)))
                  (rvar_comp (rvar_of_ldist (rand_tree_rec x'.2)) (λ x, INR (height x))))
               (λ xy : prod_eqType R_eqType R_eqType, Rmax xy.1 xy.2)) (r - a (rsize [::]))))).
    rewrite img_rvar_of_ldist /h. 
    rewrite big_cons big_nil Rplus_0_r.
    rewrite /a/rsize/size. 
    replace (INR 0) with 0 by auto.
    destruct (Rlt_dec); last nra.
    specialize (pr_rvar_ldist ((x ← rand_tree_rec [::]; mret (INR (height x))))) => -> //=.
    rewrite big_cons big_nil /=.
    rewrite {2}/pr_eq. rewrite pr_eq_alt_comp.
    destruct (Rle_dec); last nra.
    
    rewrite -(big_map _ (λ x, true) (λ v, if Rmax (fst v) (snd v) == r - 0 then
                                            pr_eq _ v
                                          else
                                            0)).
    rewrite (eq_big_perm _ (img_pair_rv _ _ _ _)).
    rewrite allpairs_comp.
    rewrite img_rvar_comp map_comp (map_comp height).
    specialize (img_rvar_of_ldist (rand_tree_rec [::])) => ->.
    rewrite ?big_cons ?big_nil ?Rplus_0_r //= ?Rminus_0_r.
    rewrite Rmax_left; last reflexivity.
    case: ifP; last by (intros; field).
    rewrite pr_mret_simpl //=. intros. ring_simplify. rewrite pr_eq_rvar_pair //=.
    rewrite /pr_eq pr_eq_alt_comp.
    rewrite -(big_map _ (λ x, true) (λ v, if INR (height (v)) == 0 then pr_eq _ v else 0)).
    rewrite -(big_map _ (λ x, true) (λ v, if INR (height (v)) == 0 then pr_eq _ v else 0)).
    specialize (img_rvar_of_ldist (rand_tree_rec [::])) => -> //=.
    rewrite ?big_cons ?big_nil //= eq_refl.
    rewrite pr_mret_simpl //=. field.
  - destruct ls as [| b0 ls0]. 
    { rewrite /T. rewrite -pr_mbind_mret. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' _) x' *
      pr_eq (rvar_comp
               (rvar_pair
                  (rvar_comp (rvar_of_ldist (rand_tree_rec x'.1)) (λ x, INR (height x)))
                  (rvar_comp (rvar_of_ldist (rand_tree_rec x'.2)) (λ x, INR (height x))))
               (λ xy : prod_eqType R_eqType R_eqType, Rmax xy.1 xy.2)) (r - a (rsize _))))).
    rewrite img_rvar_of_ldist /h. 
    rewrite big_cons big_nil Rplus_0_r.
    rewrite /a/rsize/size. 
    replace (INR 1) with 1 by auto.
    destruct (Rlt_dec); last nra.
    specialize (pr_rvar_ldist ((x ← rand_tree_rec [:: a0]; mret (INR (height x))))) => -> //=.
    rewrite big_cons big_nil /=.
    rewrite /h'/h.
    rewrite {2}/pr_eq. rewrite 1!pr_eq_alt_comp.
    rewrite ?big_cons ?big_nil ?Rplus_0_r ?Rminus_0_r.
    rewrite pr_mret_simpl. ring_simplify. 
    destruct (Rle_dec); last nra.
    rewrite /Rminus Ropp_0 Rplus_0_r.
    rewrite -(big_map _ (λ x, true) (λ v, if Rmax (fst v) (snd v) == r then
                                            pr_eq _ v
                                          else
                                            0)).
    rewrite (eq_big_perm _ (img_pair_rv _ _ _ _)). 
    rewrite allpairs_comp.
    rewrite img_rvar_comp map_comp (map_comp height).
    specialize (img_rvar_of_ldist (rand_tree_rec [::])) => -> //=.
    rewrite ?big_cons ?big_nil //=. replace (INR 0) with 0 by auto.
    rewrite ?Rplus_0_r.
    rewrite Rmax_left; last reflexivity.
    case: ifP; intros; last field.
    rewrite pr_eq_rvar_pair.
    f_equal.
    * rewrite /pr_eq pr_eq_alt_comp.
      rewrite -(big_map _ (λ x, true) (λ v, if INR (height (v)) == 0 then pr_eq _ v else 0)).
      specialize (img_rvar_of_ldist (rand_tree_rec [::])) => -> //=.
      rewrite ?big_cons ?big_nil //= eq_refl.
      rewrite pr_mret_simpl //=. field.
    }
    remember (b0 :: ls0) as ls eqn:Heql0.
   rewrite /T. 
    rewrite rt_unfold.
    transitivity
  (pr_eq (rvar_comp (rvar_of_ldist
         ('(ll, lu) ← h (a0 :: ls);
            lls ← rand_tree_rec ll;
            lus ← rand_tree_rec lu;
            mret (lls, lus)))
          (λ x, 1 + Rmax (INR (height (fst x))) (INR (height (snd x))))) r); last first.
    {    
      rewrite /h'. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' _) x' *
      pr_eq (rvar_comp
               (rvar_pair
                  (rvar_comp (rvar_of_ldist (rand_tree_rec x'.1)) (λ x, INR (height x)))
                  (rvar_comp (rvar_of_ldist (rand_tree_rec x'.2)) (λ x, INR (height x))))
               (λ xy : prod_eqType R_eqType R_eqType, Rmax xy.1 xy.2)) (r - a (rsize _))))).
    rewrite -pr_mbind_mret ldist_assoc. rewrite pr_mbind_ldist2.
    rewrite img_rvar_of_ldist. 
      *  eapply eq_bigr. intros (ll&lu) _.
        f_equal. 
        rewrite pr_mbind_mret. rewrite rvar_pair_comp //= rvar_comp_comp //=. 
        transitivity (pr_eq (rvar_comp (rvar_pair (rvar_of_ldist (rand_tree_rec ll))
                                                  (rvar_of_ldist (rand_tree_rec lu)))
                                       (λ x : tree * tree, 1 + Rmax (INR (height x.1))
                                                                    (INR (height x.2)))) r).
        { apply: eq_dist_comp. apply: eq_dist_bind_rvar_pair. }
          rewrite {1}/pr_eq {1}[a in _ = a]/pr_eq.
          rewrite ?pr_eq_alt_comp /=. eapply eq_bigr => x ?.
          apply if_case_match. rewrite ?plus_INR ?Rmax_INR /rsize//=/a//=.
          rewrite Heql0 //=. specialize (S_INR (size ls0)) => /= => ->. 
          destruct (Rlt_dec) as [Hlt0|Hnlt].
          { clear -Hlt0. specialize (pos_INR (size ls0)). rewrite //=. intros.  exfalso; nra. }
          destruct (Rle_dec); first nra.
          apply /eqP; apply /eqP. case: ifP; first by (move /eqP => ->; nra).
          move /eqP. intros. nra.
    }
    rewrite Heql0.
    rewrite /h.
    rewrite -?pr_mbind_mret.
    rewrite ?ldist_assoc.
    eapply eq_dist_ldist_bind_ext => ?.
    eapply eq_dist_ldist_bind_ext => pv.
    rewrite ldist_left_id.
    rewrite ?ldist_assoc.
    eapply mspec_eq_dist_ldist_bind_ext; first apply (rand_tree_non_empty_non_leaf); intros tl Htl.
    rewrite ?ldist_assoc.
    eapply mspec_eq_dist_ldist_bind_ext; first apply (rand_tree_non_empty_non_leaf); intros tr Htr.
    apply outcomes_eq_dist => //=.
    do 3 f_equal.
    destruct tl, tr; try (rewrite S_INR Rmax_INR; nra); [].
    exfalso. 
    edestruct (filter_lt_gt_non_empty [:: a0, b0 & ls0] (sval pv)).
    ** rewrite //=. 
    ** rewrite -Heql0. auto.
    ** eapply Htl => //=.
    ** eapply Htr => //=.
Qed.
Definition k := -/ ln(3/4).

Lemma partition_perm_eq' l:
  ∀ n, perm_eq ([seq i <- l | i < n] ++ [seq i <- l | i == n] ++ [seq i <- l | n < i])%nat l. 
Proof.
  induction l as [| a l] => n; first by (rewrite //=).
  rewrite //=. case (ltngtP a n) => Hcmp //=.
  - by rewrite perm_cons.
  - eapply (perm_eq_trans).
    { erewrite perm_cat2l. rewrite perm_catC cat_cons. erewrite perm_cons. done. }
    rewrite -cat_cons perm_catCA cat_cons perm_cons.
    rewrite -perm_catCA.
    eapply (perm_eq_trans); last apply (IHl n).
    rewrite perm_cat2l perm_catC //.
  - rewrite -cat_cons perm_catCA // cat_cons perm_cons.
    rewrite perm_catCA //.
Qed.


Theorem bound x w:
    uniq x →
    rsize x > 1 →  
    pr_gt (T x) ((k * ln (rsize x) + 1) + INR w)
       ≤ (rsize x) * (3/4)^w.
Proof.
  specialize (quicksort_rec.recurrence_span2.qs_span_bound _ _ _ _ T h' uniq).
  rewrite /size/rsize => Hrec. eapply Hrec; clear.
  - apply huniq.
  - intros l ?. rewrite //=.
    rewrite /quicksort_rec.recurrence_span2.size //=.
    cut (∀ n, INR (length (fst (rvar_of_ldist (h l) n))) + 
              INR (length (snd (rvar_of_ldist (h l) n))) <=
                   INR (length l)); first by rewrite //=.
    intros n'. apply fun_to_mspec.
    rewrite /h.
    destruct l as [| a l].
    { apply mspec_mret => //=. replace (INR 0) with 0 by auto. nra. } 
    destruct l as [| b l0].
    { apply mspec_mret => //=. replace (INR 0) with 0 by auto. replace (INR 1) with 1 by auto. nra. } 
    remember (b::l0) as l eqn:Heql0.
    clear b l0 Heql0.
    tbind (λ x, sval x \in a :: l).
    { intros (?&?) => //. }
    intros (pv&Hin) _. 
    remember (a :: l) as l0 eqn:Heql0.
    apply mspec_mret.
    rewrite //=.
    replace (length l0) with (size l0) by auto.
    assert (Hlt: (ssrnat.ltn O (size [seq i <- l0 | i == pv]))%nat).
    {  rewrite size_filter //=. rewrite -has_count has_pred1 Heql0 in_cons //=. }
    rewrite -plus_INR. apply le_INR. move /ltP in Hlt. 
    rewrite -?size_legacy.
    specialize (partition_perm_eq' l0 pv). move /perm_eq_size. rewrite ?size_cat. 
    intros Hsize. nify. rewrite //= in Hsize. rewrite //=. omega.
  - rewrite /quicksort_rec.recurrence_span2.size //=.
    intros l ? Hgt. rewrite //=.
    cut (∀ n, INR (length (fst ((rvar_of_ldist (h l) n)))) + 
              INR (length (snd ((rvar_of_ldist (h l) n)))) <=
                   INR (length l) - 1); first by rewrite //=.
    intros n'. apply fun_to_mspec.
    rewrite /h.
    destruct l as [| a l].
    { move : Hgt. rewrite //=. replace (INR 0) with 0 by auto. nra. } 
    destruct l as [| b l0].
    { move : Hgt. rewrite //=. replace (INR 1) with 1 by auto. nra. } 
    remember (b::l0) as l eqn:Heql0.
    clear b l0 Heql0.
    tbind (λ x, sval x \in a :: l).
    { intros (?&?) => //. }
    intros (pv&Hin) _. 
    remember (a :: l) as l0 eqn:Heql0.
    apply mspec_mret.
    rewrite //=.
    replace (length l0) with (size l0) by auto.
    assert (Hlt: (ssrnat.ltn O (size [seq i <- l0 | i == pv]))%nat).
    {  rewrite size_filter //=. rewrite -has_count has_pred1 Heql0 in_cons //=. }
      move /ltP in Hlt. 
    rewrite -?size_legacy.
    specialize (partition_perm_eq' l0 pv). move /perm_eq_size => <-. 
    rewrite ?size_cat ?plus_INR.
    specialize (pos_INR (size [seq i <- l0 | (i < pv)%nat])).
    specialize (pos_INR (size [seq i <- l0 | (pv < i)%nat])).
    rewrite //=. intros.
    assert (Hge1: 1 <= INR (size [seq i <- l0 | i == pv])).
    { replace 1 with (INR 1) by auto. apply le_INR. omega. } 
    rewrite //= in Hge1. nra.
  - rewrite /quicksort_rec.recurrence_span2.size/quicksort_rec.recurrence_span2.rec_solution.d //=.
    intros x n Hle.
    replace 1 with (INR 1) in Hle by auto. apply INR_le in Hle.
    cut (INR (height (rvar_of_ldist (add_list_random x Leaf) n)) = 0); first by rewrite //=. 
    apply fun_to_mspec.
    destruct x; [| destruct x].
    * rewrite alr_unfold.
      apply mspec_mret => //=.
    * rewrite alr_unfold.
      apply mspec_mret => //=.
    * rewrite //= in Hle. omega.
  - intros. eapply (rec_pr_rec_gt _ rsize _ _ _ _ T h' uniq (λ xy, Rmax (fst xy) (snd xy))); auto.
    intros. apply Trec; auto.
  - rewrite /quicksort_rec.recurrence_span2.size/quicksort_rec.recurrence_span2.rec_solution.d
            /quicksort_rec.recurrence_span2.rec_solution.m
            /quicksort_rec.recurrence_span2.qs_factor.alpha.
    etransitivity; first eapply Ex_max_partition.
    rewrite /m/rsize/size/length. do 2 destruct Rlt_dec; try nra.
Qed.

From Interval Require Import Interval_tactic.
Remark concrete:
  ∀ l, uniq l → rsize l = 10 ^ 10 →
       pr_gt (T l) 300 ≤ 1/(10^15).
Proof.
  intros l Huniq Hsize.
  transitivity (pr_gt (T l) ((k * ln (rsize l) + 1) + 208)).
  - apply Rge_le, pr_gt_contra.
    rewrite Hsize. rewrite /k. interval.
  - replace 208 with (INR 208); last first.
    { vm_compute. nra. } 
    etransitivity; first apply bound; auto; try nra. rewrite Hsize. interval.
Qed.