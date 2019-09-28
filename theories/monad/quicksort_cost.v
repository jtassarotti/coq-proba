From discprob.basic Require Import base order nify seq_ext.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad monad_cost_hoare monad_cost quicksort quicksort_correct.
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
      p ← draw_pivot a l;
      spl ← dist_ret _ (partition' (sval p) (a :: l));
      mret (lower (sval spl), upper (sval spl))
  end.
Definition rsize (l: seq nat) := INR (size l).

Definition m x :=
  match (Rlt_dec x (4/3)) with
  | left _ => 0
  | _ => x * (3/4)
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

Lemma unif_all n x (Hle: (x <= n)%nat):
  (O, exist _ x Hle) \in [seq i.2 | i <- outcomes (unif n)].
Proof.
  apply /mapP.
  set (a := exist _ x Hle).
  replace (O, a) with (1/INR (S n), (O, a)).2; last done.
  do 2 apply /mapP; eexists; eauto.
  rewrite /unif => //=.
  apply /mapP => //=.
  assert (Hlt: (x < S n)%nat) by auto.
  exists (Ordinal Hlt).
  - apply mem_enum. 
  - rewrite /a; repeat f_equal. apply bool_irrelevance.
Qed.

Lemma unif_all2 n x (Hle: (x <= n)%nat):
  exist _ x Hle \in [seq i.2.2 | i <- outcomes (unif n)].
Proof.
  apply /mapP.
  set (a := exist _ x Hle).
  replace (a) with (1/INR (S n), (O, a)).2.2; last done.
  do 2 apply /mapP; eexists; eauto.
  rewrite /unif => //=.
  apply /mapP => //=.
  assert (Hlt: (x < S n)%nat) by auto.
  exists (Ordinal Hlt).
  - apply mem_enum. 
  - rewrite /a; repeat f_equal. apply bool_irrelevance.
Qed.

Lemma unif_cost n a c : 
  (c, a) \in [seq i.2 | i <- outcomes (unif n)] → 
  c = O.
Proof.
  replace (c, a) with (1/INR (S n), (c, a)).2; last done.
  move /mapP => [[r' [c' a']] Hin]. 
  move: Hin. rewrite /unif//=.
  move /mapP => [[c'' a''] Hin] [] => ??? []. subst. done.
Qed.

Lemma unif_cost2 n: 
  [seq (O, (i.2.2)) | i <- unif n] = [seq i.2 | i <- unif n].
Proof.  
  apply eq_in_map.
  intros (r, (c, a)) Hin. 
  rewrite //=. f_equal; symmetry.
  eapply (unif_cost n a).
  apply /mapP; eauto.
Qed.

Lemma unif_cost3 n: 
  [seq (O, i) | i <- [seq i.2.2 | i <- unif n]] = [seq i.2 | i <- unif n].
Proof.  
  rewrite -map_comp -unif_cost2 => //=.
Qed.

Lemma unif_pr n a : 
  a \in [seq i.2 | i <- outcomes (unif n)] → 
  pr_eq (rvar_of_ldist (unif n)) a = 1 / INR (S n).
Proof.
  intros Hin. rewrite pr_rvar_ldist /unif//=.
  rewrite big_map -big_filter //=.
  destruct a as (c&(x&Hle)) => //=.
  assert (c = O); last subst.
  { eapply unif_cost. apply Hin. }
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

Lemma partition_split l pv:
  let x := partition' pv l in
  lower (sval x.2) = [ seq n <- l | ltn n pv] ∧
  middle (sval x.2) = [ seq n <- l | n == pv] ∧
  upper (sval x.2) = [ seq n <- l | ltn pv n].
Proof.
      induction l as [|a l]; first by rewrite //=.
      rewrite //=; case (ltngtP a pv) => //= ?;
      destruct (IHl) as (?&?&?); repeat split; auto; f_equal; done.
Qed.

Lemma sorted_nth_trans {A: eqType} (R: rel A) s (Ht: transitive R)
      (Hsorted : sorted R s) x0 a b:
  (a < b < size s)%nat -> 
  R (nth x0 s a) (nth x0 s b).
Proof.
  move /andP => [Hab Hbs]. revert s Ht Hsorted Hbs. nify. 
  induction Hab => s Ht Hsorted Hbs.
  - induction s.
    * rewrite //= in Hbs.
    * move /pathP in Hsorted => //=. apply Hsorted. rewrite //= in Hbs.
  - induction s.
    * rewrite //= in Hbs. 
    * rewrite //=. eapply Ht; last apply IHHab; eauto.
      move /pathP in Hsorted => //=. apply Hsorted. 
      ** nify. rewrite //= in Hbs. omega.
      ** rewrite //= in Hsorted. destruct s => //=. 
         move /andP in Hsorted. destruct Hsorted as (?&?); eauto.
Qed.

Lemma sorted_nth_trans_refl {A : eqType} T (s: seq A) (Hr: reflexive T) (Ht: transitive T) 
      (Hsorted : sorted T s) x0 a b:
  (a <= b < size s)%nat -> T (nth x0 s a) (nth x0 s b).
Proof.
  move /andP => [Hab Hbs].
  rewrite leq_eqVlt in Hab. move /orP in Hab. destruct Hab as [Heq|Hab].
  - move /eqP in Heq; subst; apply Hr.
  - apply sorted_nth_trans; auto. apply /andP; split => //.
Qed.

Lemma eq_filter_in (T: eqType) (a1 a2: T → bool) (l: seq T):
  (∀ i, i \in l → a1 i = a2 i) →
  filter a1 l = filter a2 l.
Proof.
  induction l => //=.
  intros Hin. rewrite Hin; last first.
  - rewrite in_cons eq_refl //.
  - rewrite IHl => //.
    intros i Hin'; apply Hin. by rewrite in_cons Hin' orbT.
Qed.

Lemma lower_split_sorted l1 l2 x:
  sorted leq (l1 ++ x :: l2) →
  ∃ lmid, ([seq n <- l1 ++ x :: l2 | n < x] ++ lmid = l1)%nat.
Proof.
  revert l2 x. induction l1 => l2 x Hsorted.
  - exists [::].
    rewrite cat0s cats0.
    etransitivity; first eapply eq_filter_in; last apply filter_pred0.
    intros i Hin => //=.
    rewrite //= in Hsorted.
    replace x with (nth O (x :: l2) 0) => //.
    rewrite -(nth_index O Hin). apply negbTE. rewrite -leqNgt.
    apply sorted_nth_trans_refl; auto.
    * by intros => ?.
    * rewrite /= => ?????. eapply leq_trans; eauto.
    * apply /andP; split; auto.  rewrite index_mem. done.
  - rewrite /=. case: ifP.
    * intros. edestruct IHl1 as (lmid&Heq).
      { eapply path_sorted. rewrite //= in Hsorted. eauto. }
      exists lmid => /=. f_equal; done.
    * move /negbT. rewrite -leqNgt => Hle. exists (a :: l1).
      rewrite -[a in _ = a]cat0s; f_equal => //.
      etransitivity; first eapply eq_filter_in; last apply filter_pred0.
      intros i Hin => //=.
      rewrite //= in Hsorted.
      apply negbTE. rewrite -leqNgt. apply (leq_trans Hle).
      replace a with (nth O (a :: l1 ++ x :: l2) 0) => //.
      assert (Hin': i \in a :: (l1 ++ x :: l2)).
      { rewrite in_cons Hin orbT //. }
      rewrite -(nth_index O Hin'). 
      apply sorted_nth_trans_refl; auto.
      ** by intros => ?.
      ** rewrite /= => ?????. eapply leq_trans; eauto.
      ** apply /andP; split; auto.  rewrite index_mem. done.
Qed.

Lemma lower_split_size_sorted l1 l2 x:
  sorted leq (l1 ++ x :: l2) →
  (size [seq n <- l1 ++ x :: l2 | n < x] <= size l1)%nat.
Proof.
  intros (lmid&Heq)%lower_split_sorted.
  rewrite -[a in (_ <= size a)%nat]Heq.
  rewrite size_cat. rewrite -plusE. apply /leP. destruct size; omega.
Qed.


Lemma lower_split_size_sorted_nth  l x a:
  sorted leq l →
  (x < size l →
  size [seq n <- l | n < nth a l x] <= x)%nat.
Proof.
  rewrite nth_legacy => Hsort Hlt.
  edestruct (@nth_split _ x l a) as (l1&l2&Heq&Hlen). 
  { rewrite -size_legacy. apply /ltP. auto. }
  rewrite {2}Heq.
  rewrite -{3}Hlen. apply lower_split_size_sorted. rewrite Heq in Hsort => //.
Qed.

Lemma sorted_cat_inv {A: eqType} (R: rel A) (HTrans: transitive R) (l1 l2: seq A):
  sorted R (l1 ++ l2) → sorted R l1 ∧ sorted R l2.
Proof. 
  intros HS; split; eapply subseq_sorted; try apply HS; auto.
  - rewrite -[a in subseq a _]cats0.
    apply cat_subseq; eauto using sub0seq.
  - rewrite -[a in subseq a _]cat0s.
    apply cat_subseq; eauto using sub0seq.
Qed.
  
Lemma upper_split_sorted l1 l2 x:
  sorted leq (l1 ++ x :: l2) →
  (∃ lmid, lmid ++ [seq n <- l1 ++ x :: l2 | x < n] = l2)%nat.
Proof.
  revert l1 x. induction l2 as [| a l2] using rev_ind => l1 x Hsorted.
  - exists [::].
    rewrite ?cat0s ?cats0.
    etransitivity; first eapply eq_filter_in; last apply filter_pred0.
    intros i Hin => //=.
    rewrite //= in Hsorted.
    replace x with (nth O (l1 ++ [:: x]) (size l1)); last first.
    { rewrite nth_cat ltnn subnn //. }
    rewrite -(nth_index O Hin). apply negbTE. rewrite -leqNgt.
    apply sorted_nth_trans_refl; auto.
    * by intros => ?.
    * rewrite /= => ?????. eapply leq_trans; eauto.
    * apply /andP; split; auto.
      ** rewrite -index_mem size_cat //= in Hin. rewrite -ltnS //. move: Hin. by nat_norm.
      ** rewrite size_cat //=. nat_norm => //.
  - edestruct (IHl2 l1 x) as (lmid&Heq).
    { 
      rewrite -cat_cons catA in Hsorted.
      apply sorted_cat_inv in Hsorted; first (destruct Hsorted; auto).
      intros ?????. eauto using leq_trans.
    }
    rewrite -cat_cons catA filter_cat.
    rewrite {2}/filter.
    case: ifP => Hlt.
    * exists lmid. rewrite catA Heq. done.
    * exists (lmid ++ [::a]). 
      rewrite cats0. rewrite -[a in _ = a]cats0. 
      cut ([seq n <- l1 ++ x :: l2 | x < n] = [::])%nat.
      { 
        intros Hnil. rewrite ?Hnil -Heq ?Hnil ?cats0 ?cat0s. done.
      }
    etransitivity; first eapply eq_filter_in; last apply filter_pred0.
    intros i Hin => //=.
    apply negbTE. rewrite -leqNgt. apply negbT in Hlt. rewrite -leqNgt in Hlt. 
    eapply leq_trans; last apply Hlt.
    replace a with (nth O (l1 ++ x :: (l2 ++ [:: a])) (size (l1 ++ x :: l2 ))); last first.
    { rewrite -cat_cons catA nth_cat ltnn subnn //. }
    assert (Hin': i \in l1 ++ x:: l2 ++ [:: a]).
    { rewrite -cat_cons catA. rewrite mem_cat Hin //. }
    rewrite -(nth_index O Hin'). 
    apply sorted_nth_trans_refl; auto.
    ** by intros => ?.
    ** rewrite /= => ?????. eapply leq_trans; eauto.
    ** apply /andP; split; auto.
      *** rewrite -index_mem ?size_cat //= ?size_cat in Hin'.
          move: Hin'.
          rewrite ?size_cat //= -?plusE. move /leP => Hle'. apply /leP. destruct (size l2); omega.
      *** repeat (rewrite ?size_cat //=). rewrite -?plusE. apply /ltP => //=. omega.
Qed.

Lemma upper_split_size_sorted l1 l2 x:
  sorted leq (l1 ++ x :: l2) →
  (size [seq n <- l1 ++ x :: l2 | x < n] <= size l2)%nat.
Proof.
  intros (lmid&Heq)%upper_split_sorted.
  rewrite -[a in (_ <= size a)%nat]Heq.
  rewrite size_cat. rewrite -plusE. apply /leP. destruct size; omega.
Qed.

Lemma upper_split_size_sorted_nth  l x a:
  sorted leq l →
  (x < size l →
  size [seq n <- l | nth a l x < n] <= size l - x - 1)%nat.
Proof.
  rewrite nth_legacy => Hsort Hlt.
  edestruct (@nth_split _ x l a) as (l1&l2&Heq&Hlen). 
  { rewrite -size_legacy. apply /ltP. auto. }
  rewrite {2}Heq.
  assert (Hlen': (length l2 <= length l - x - 1)%nat).
  { rewrite Heq app_length //=. rewrite -?plusE -?minusE. apply /leP. rewrite -Hlen //=. omega. }
  eapply leq_trans; last apply Hlen'.
  apply upper_split_size_sorted. rewrite Heq in Hsort => //.
Qed.

Lemma perm_filter {T: eqType} {P: pred T} (s t: seq T):
  perm_eq s t → perm_eq [seq i <- s | P i] [seq i <- t | P i].
Proof.
  move /perm_eqP => Hcount.
  apply /perm_eqP => P'. rewrite ?count_filter. apply Hcount.
Qed.

Lemma perm_eq_bij {A: eqType} (a: A) (l1 l2: seq A): 
  perm_eq l1 l2 →
  (∃ f : nat → nat,
           (∀ x, x < size l1 → nth a l1 x = nth a l2 (f x))%nat ∧
           (∀ x, x < size l1 → f x < size l1)%nat ∧
           (∀ x, x < size l1 → ∃ x', x' < size l1 ∧ f x' = x)%nat ∧
           (∀ x x', x < size l1 → x' < size l1 → f x = f x' → x = x')%nat).
Proof.
  intros Hperm.
  assert (Hsize: size l1 = size l2).
  { apply perm_eq_size => //. }
  move /perm_eq_iotaP in Hperm. specialize (Hperm a).
  destruct Hperm as [Is Hperm Heq].
  assert (HsizeIs: size Is = size l2) by (rewrite (perm_eq_size Hperm) size_iota //).
  exists (λ x, nth O Is x).
  repeat split.
  - intros x Hlt. 
    rewrite Heq => //=. erewrite nth_map; auto; rewrite HsizeIs; nify; omega.
  - intros x Hlt.
    assert (Hin: nth O Is x \in Is).
    { apply nth_lt_size. nify. omega. }
    apply perm_eq_mem in Hperm. specialize (Hperm (nth O Is x)). 
    rewrite Hperm mem_iota in Hin. move /andP in Hin. destruct Hin as (?&?).
    nify. omega.
  - intros x lt. exists (index x Is); split. 
    * rewrite Hsize -(size_iota O (size l2)) -(perm_eq_size Hperm) index_mem.
      rewrite (perm_eq_mem Hperm) mem_iota. apply /andP; split; nify; omega. 
    * apply nth_index. 
      rewrite (perm_eq_mem Hperm) mem_iota. apply /andP; split; nify; omega. 
  - intros x x' Hlt Hlt'. move /eqP. rewrite nth_uniq; first by move /eqP. 
    * rewrite HsizeIs; nify; omega.
    * rewrite HsizeIs; nify; omega.
    * rewrite (perm_eq_uniq Hperm). apply iota_uniq.
Qed.

Lemma Ex_max_partition_sum l: 
  Ex (rvar_comp (rvar_of_ldist (h l)) (λ x, Rmax (rsize (x.2.1)) (rsize (x.2.2)))) <=
  match (size l) with
     | O => 0
     | _ => \big[Rplus/0]_(i < size l) (/INR (size l) * (Rmax (INR i) (INR (size l - i - 1))))
  end.
Proof.
  destruct l as [| a l].
  - rewrite Ex_fin_comp.
    rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ (_ (fst (snd a))) (_ (snd (snd a))))).
    rewrite img_rvar_of_ldist//=/img/undup//= !big_cons ?big_nil.
    rewrite pr_mret_simpl //= /m/rsize//=.
    rewrite Rmax_left //; last (fourier). 
    rewrite /INR. ring_simplify. fourier. 
  - destruct l as [| b0 l0].
    { 
      rewrite Ex_fin_comp. 
      rewrite -(big_map _ (λ x, true) (λ a, pr_eq _ a * _ (_ (fst (snd a))) (_ (snd (snd a))))).
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
    rewrite -unif_cost3 big_map.
    edestruct (perm_eq_bij O) as (f&Hfspec&Hfsize&Hinv&Hinj).
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
         rewrite ldist_cost_bind_fold.
         rewrite ?ldist_left_id.
         assert (Hlt: (x < size (a :: l))%nat) by auto.
         rewrite //= in Hlt.
         eapply (@cspec_mspec _ _ (λ x0 : (seq nat * seq nat),
                                      Rmax (rsize x0.1) (rsize x0.2) 
                                      <= Rmax (INR (f (Ordinal (n:= S (size l)) Hle)))
                                              (INR (S (size l) - (f (Ordinal (n := S (size l)) Hle)) 
                                                    - 1)))).
         tbind (λ y, nth 0%nat (a :: l) x = sval y). 
         { apply mspec_mret => //=. }
         intros (pv&Hin') Heq.
         tbind (λ x, lower (sval x) = [ seq n <- (a :: l) | ltn n pv] ∧
                     middle (sval x) = [ seq n <- (a :: l) | n == pv] ∧
                     upper (sval x) = [ seq n <- (a :: l) | ltn pv n]).
         { apply mspec_mret. apply partition_split. }
         remember (a :: l) as l0 eqn:Heql0.
         assert (Hsize: S (size l) = (size l0)) by (rewrite Heql0; auto).
         intros (spl&Hin'') => //=. intros (Hl&Hm&Hu).
         apply mspec_mret => //=.
         rewrite /rsize. 
         rewrite ?Rmax_INR. apply le_INR. 
         rewrite Hl Hu.
         apply Nat.max_le_compat.
         *** rewrite //= in Heq. rewrite -Heq. 
             apply /leP. rewrite Hfspec. 
             specialize (perm_eqlE (perm_sort leq l0)) => Hperm.
             rewrite -(perm_eq_size (perm_filter _ _ Hperm)).
             apply lower_split_size_sorted_nth; auto.
             **** apply sort_sorted => ??. apply leq_total.
             **** rewrite (perm_eq_size (perm_eqlE (perm_sort leq l0))) /=.
                  apply Hfsize. rewrite Heql0. done.
             **** rewrite Heql0 //=.
         *** rewrite //= in Heq. rewrite -Heq. 
             apply /leP. rewrite Hfspec. 
             assert (Hsize': (size l).+1 = size l0) by rewrite Heql0 //.
             rewrite Hsize'. 
             specialize (perm_eqlE (perm_sort leq l0)) => Hperm.
             rewrite -(perm_eq_size (perm_eqlE (perm_sort leq l0))).
             rewrite -(perm_eq_size (perm_filter _ _ Hperm)).
             apply upper_split_size_sorted_nth; auto.
             **** apply sort_sorted => ??. apply leq_total.
             **** rewrite (perm_eq_size (perm_eqlE (perm_sort leq l0))) /=. 
                  apply Hfsize. rewrite Heql0. done.
             **** rewrite Heql0 //=.
      ** rewrite -unif_cost3 //. apply /mapP. eexists; eauto.
    * intros (?&?) Hin; split; auto. 
      rewrite /index_enum. rewrite -enumT. rewrite mem_enum => //=.
    * intros b Hin _ Hfalse. contradiction Hfalse.
      destruct b as (m, Hle).
      destruct (Hinv m Hle) as (x'&Hle'&Heq).
      exists (exist _ x' Hle'); repeat split; auto.
      ** apply unif_all2.
      ** apply ord_inj => //=.
    * eapply map_uniq with (f := λ x, (O, x)). rewrite unif_cost3. eapply uniq_unif2. 
    * rewrite /index_enum. rewrite -enumT. apply enum_uniq.
    * intros (?&?) (?&?) _ => //=. inversion 1; subst. apply /val_inj/Hinj => //=.
Qed.

Lemma INR_half k:
  (odd k → INR (k./2) = INR k / 2 - /2) ∧
  (~~ odd k → INR (k./2) = INR k / 2).
Proof.
  induction k.
  - rewrite //=; replace (INR 0) with 0 by auto. split; intros; try done. field. 
  - rewrite //=; split. 
    * intros. rewrite uphalf_half. destruct (odd k); rewrite //=. 
      rewrite ?S_INR ?plus_INR. destruct IHk as (_&IHk). rewrite IHk => //.
      replace (INR 0) with 0 by auto. destruct k => //=; field.
    * rewrite negbK => Hodd. 
      rewrite uphalf_half Hodd //=.
      specialize (S_INR). rewrite //= => ->. 
      specialize (S_INR). rewrite //= => ->. 
      destruct IHk as (IHk&_). rewrite IHk => //. replace (INR 1) with 1 by auto. field.
Qed.

Lemma INR_uphalf_half_odd k: odd k → INR (uphalf k * half k) = (INR k + 1) * (INR k - 1) / 4.
Proof.
  intros Hodd. rewrite uphalf_half Hodd //=. nify.
  rewrite mult_INR plus_INR.
  destruct (INR_half k) as (Hhalf&_).
  rewrite ?Hhalf //=.
  replace (INR 1) with 1 by auto. field.
Qed.

Lemma INR_uphalf_half_even k: ~~ odd k → INR (uphalf k * half k) = (INR k) * (INR k) / 4.
Proof.
  move /negbTE => Heven.
  rewrite uphalf_half Heven add0n //=. nify.
  rewrite mult_INR.
  destruct (INR_half k) as (_&Hhalf).
  rewrite ?Hhalf; last by (rewrite Heven).
  field.
Qed.

Lemma succ_product_even k:
  ~~ odd (S k * k).
Proof.
  rewrite odd_mul => //=. destruct (odd k) => //=.
Qed.

Lemma sum_le_m l:
  match (size l) with
     | O => 0
     | _ => \big[Rplus/0]_(i < size l) (/INR (size l) * (Rmax (INR i) (INR (size l - i - 1))))
  end ≤
  m (rsize l).
Proof.
  rewrite /rsize. 
  remember (size l) as k eqn:Heqk. clear Heqk l.
  induction k => //=.
  - rewrite /m. destruct (Rlt_dec) => //=; try fourier. 
  - rewrite -big_distrr => /=. 
    eapply Rle_trans.
    { 
      apply Rmult_le_compat_l.
      { left. apply Rinv_0_lt_compat. replace 0 with (INR 0) by auto. 
        apply (lt_INR 0 (S k)). omega. }
      { right. eapply eq_bigr => i /=. rewrite Rmax_INR => //.  }
    }
    rewrite big_INR.
    specialize (max_triangular_sum (S k)). rewrite big_mkord => ->. 
    rewrite bin2.
    destruct k.
    {  rewrite plus_INR mult_INR => //=. 
       replace (INR 0) with 0 by auto.
       replace (INR 1) with 1 by auto.
       rewrite /m//=. destruct (Rlt_dec) => //=; fourier. 
    }
    rewrite /m. rewrite S_INR. destruct (Rlt_dec).
    { rewrite ?S_INR. intros. exfalso.
      specialize (pos_INR k). intros. nra. }
    rewrite plus_INR. 
    destruct (INR_half ((S (S k)) * (S k))) as (_&Hhalf).
    rewrite Hhalf; last apply succ_product_even.
    case_eq (odd (S (S k))) => Hparity.
    * rewrite INR_uphalf_half_odd //. nify.
      rewrite mult_INR ?S_INR.
      specialize (pos_INR k) => Hpos.
      apply (Rmult_le_reg_l (INR k + 1 + 1 )); first by fourier.
      field_simplify; last first.
      { apply Rgt_not_eq. fourier. }
      nra.
    * rewrite INR_uphalf_half_even //; last by (rewrite Hparity). nify.
      rewrite mult_INR ?S_INR.
      specialize (pos_INR k) => Hpos.
      apply (Rmult_le_reg_l (INR k + 1 + 1 )); first by fourier.
      field_simplify; last first.
      { apply Rgt_not_eq. fourier. }
      nra.
Qed.

Lemma Ex_max_partition l: 
  Ex (rvar_comp (rvar_of_ldist (h l)) (λ x, Rmax (rsize (x.2.1)) (rsize (x.2.2)))) <=
   m (rsize l).
Proof.
  eapply Rle_trans; [ apply Ex_max_partition_sum | apply sum_le_m ].
Qed.

Definition T := λ x, rvar_comp (rvar_of_ldist (qs x)) (λ x, INR (fst x)).
Definition a x :=
    match (Rle_dec x 1) with
      | left _ => 0
      | _ => x
    end.
Definition h' x := rvar_comp (rvar_of_ldist (h x)) snd.

Lemma Trec: 
    ∀ x r,  pr_eq (T x) r = 
            \big[Rplus/0]_(x' : imgT (h' x)) 
                        (pr_eq (h' x) (sval x') * 
                         pr_eq (rvar_comp (rvar_pair (T (fst (sval x'))) (T (snd (sval x'))))
                                         (fun xy => (fst xy) + (snd xy))) (r - a (rsize x))).
Proof.
  intros ls r.
  induction ls as [| a0 ls].
  - rewrite /T. rewrite -pr_mbind_mret. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' [::]) x' *
      pr_eq (rvar_comp
               (rvar_pair
                  (rvar_comp (rvar_of_ldist (qs x'.1)) (λ x, INR x.1))
                  (rvar_comp (rvar_of_ldist (qs x'.2)) (λ x, INR x.1)))
               (λ xy : prod_eqType R_eqType R_eqType, xy.1 + xy.2)) (r - a (rsize [::]))))).
    rewrite img_rvar_comp map_comp.
    rewrite img_rvar_of_ldist /h. 
    rewrite big_cons big_nil Rplus_0_r.
    rewrite /a/rsize/size. 
    replace (INR 0) with 0 by auto.
    destruct (Rle_dec); last nra.
    specialize (pr_rvar_ldist ((x ← qs [::]; mret (INR x.1)))) => -> //=.
    rewrite big_cons big_nil /=.
    rewrite /pr_eq; rewrite 2!pr_eq_alt_comp.
    
    rewrite -(big_map _ (λ x, true) (λ v, if (snd v) == _ then
                                            pr_eq _ v
                                          else
                                            0)).

    rewrite -(big_map _ (λ x, true) (λ v, if (fst v) + (snd v) == r - 0 then
                                            pr_eq _ v
                                          else
                                            0)).
    rewrite (eq_big_perm _ (img_pair_rv _ _ _ _)).
    rewrite allpairs_comp.
    rewrite img_rvar_comp.
    rewrite map_comp //=.
    rewrite (map_comp fst).
    specialize (img_rvar_of_ldist (qs [::])) => ->.
    rewrite Rmult_1_r Rplus_0_r.
    specialize (img_rvar_of_ldist (h [::])) => ->.
    rewrite //= !big_cons !big_nil ?Rplus_0_r //= ?Rminus_0_r.
    rewrite [a in _ = _ * a]big_cons ?big_nil //= ?Rplus_0_r.
    case: ifP; last first.
    { intros; field.  }
    rewrite pr_mret_simpl //=. intros. ring_simplify. rewrite pr_eq_rvar_pair //=.
    rewrite /pr_eq pr_eq_alt_comp.
    rewrite -(big_map _ (λ x, true) (λ v, if INR (fst (v)) == 0 then pr_eq _ v else 0)).
    rewrite -(big_map _ (λ x, true) (λ v, if INR (fst (v)) == 0 then pr_eq _ v else 0)).
    specialize (img_rvar_of_ldist (qs [::])) => -> //=.
    rewrite ?big_cons ?big_nil //= eq_refl.
    rewrite pr_mret_simpl //=. field.
  - destruct ls as [| b0 ls0]. 
    { rewrite /T. rewrite -pr_mbind_mret. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' _) x' *
      pr_eq (rvar_comp
               (rvar_pair
                  (rvar_comp (rvar_of_ldist (qs x'.1)) (λ x, INR x.1))
                  (rvar_comp (rvar_of_ldist (qs x'.2)) (λ x, INR x.1)))
               (λ xy : prod_eqType R_eqType R_eqType, xy.1 + xy.2)) (r - a (rsize _))))).
    rewrite img_rvar_comp map_comp.
    rewrite img_rvar_of_ldist /h. 
    rewrite big_cons big_nil Rplus_0_r.
    rewrite /a/rsize/size. 
    replace (INR 1) with 1 by auto.
    destruct (Rle_dec); last nra.
    specialize (pr_rvar_ldist ((x ← qs [:: a0]; mret (INR x.1)))) => -> //=.
    rewrite big_cons big_nil /=.
    rewrite /h'/h.
    rewrite {1}/pr_eq. rewrite 1!pr_eq_alt_comp.
    rewrite -(big_map _ (λ x, true) (λ v, if (snd v) == _ then
                                            pr_eq _ v
                                          else
                                            0)).
    specialize (img_rvar_of_ldist (h [::a0])) => ->. rewrite /h.
    rewrite ?big_cons ?big_nil ?Rplus_0_r //= ?Rminus_0_r.
    rewrite pr_mret_simpl //=. ring_simplify. 
    rewrite {1}/pr_eq. rewrite 1!pr_eq_alt_comp.
    rewrite -(big_map _ (λ x, true) (λ v, if (fst v) + (snd v) == r then
                                            pr_eq _ v
                                          else
                                            0)).
    rewrite (eq_big_perm _ (img_pair_rv _ _ _ _)). 
    rewrite allpairs_comp.
    rewrite img_rvar_comp map_comp (map_comp fst).
    specialize (img_rvar_of_ldist (qs [::])) => -> //=.
    rewrite ?big_cons ?big_nil //=. replace (INR 0) with 0 by auto.
    rewrite ?Rplus_0_r.
    case: ifP; intros; last field.
    rewrite pr_eq_rvar_pair.
    f_equal.
    * rewrite /pr_eq pr_eq_alt_comp.
      rewrite -(big_map _ (λ x, true) (λ v, if INR (fst (v)) == 0 then pr_eq _ v else 0)).
      specialize (img_rvar_of_ldist (qs [::])) => -> //=.
      rewrite ?big_cons ?big_nil //= eq_refl.
      rewrite pr_mret_simpl //=. field.
    * rewrite /pr_eq pr_eq_alt_comp.
      rewrite -(big_map _ (λ x, true) (λ v, if INR (fst (v)) == 0 then pr_eq _ v else 0)).
      specialize (img_rvar_of_ldist (qs [::])) => -> //=.
      rewrite ?big_cons ?big_nil //= eq_refl.
      rewrite pr_mret_simpl //=. field.
    }
    remember (b0 :: ls0) as ls eqn:Heql0.
   rewrite /T. 
    rewrite qs_unfold.
    transitivity
  (pr_eq (rvar_comp (rvar_of_ldist
         ('(ll, lu) ← h (a0 :: ls);
            lls ← qs ll;
            lus ← qs lu;
            mret (lls, lus))) (λ x, INR (fst x)))  r); last first.
    {    
      rewrite /h'. 
    rewrite -(big_map _ (λ x, true) 
     (λ x',
     (pr_eq (h' _) x' *
      pr_eq (rvar_comp
               (rvar_pair
                  (rvar_comp (rvar_of_ldist (qs x'.1)) (λ x, INR x.1))
                  (rvar_comp (rvar_of_ldist (qs x'.2)) (λ x, INR x.1)))
               (λ xy : prod_eqType R_eqType R_eqType, xy.1 + xy.2)) (r - a (rsize _))))).

    rewrite img_rvar_comp map_comp.
    rewrite img_rvar_of_ldist.
      rewrite (cost_bind_const (size (a0 :: ls))).
      * rewrite -undup_map. rewrite -map_comp. 
        eapply eq_bigr. intros (ll&lu) _.
        f_equal. 
        specialize (ldist_cost_pair (qs ll) (qs lu) (λ a b, (a, b))
                                    (λ x, INR (x + size (a0 :: ls)))) => ->.
        rewrite !rvar_pair_comp !rvar_comp_comp.
          rewrite {1}/pr_eq {1}[a in _ = a]/pr_eq.
          rewrite ?pr_eq_alt_comp /=. eapply eq_bigr => x ?.
          apply if_case_match. rewrite ?plus_INR /rsize//=/a//=.
          rewrite Heql0 //=. specialize (S_INR (size ls0)) => /= => ->. 
          destruct (Rle_dec).
          {specialize (pos_INR (size ls0)). intros. nra. } 
          apply /eqP.
          apply /eqP. case: ifP; first by (move /eqP => ->; nra).
          move /eqP. intros. nra.
      * intros d'. rewrite map_comp. move /mapP. intros [? Hin Heq]. rewrite Heq. 
        cut (cspec (h (a0 :: ls )) (λ x, fst x = size (a0 :: ls))); first by auto.
        rewrite /h. rewrite Heql0. rewrite -Heql0.
        cbind (λ x, fst x = O). 
        { 
          rewrite /draw_pivot.
          cbind (λ x, fst x = O).
          { rewrite /cspec/coutput. destruct y as (c, a). 
            rewrite /fst. eapply unif_cost; auto. }
          intros (c0, pv) => /= ->.
          apply cspec_mret => //=.
        }
        intros (?, pv) ->.
        cbind (λ x, fst x = size (a0 :: ls)).
        { 
         eapply cspec_dist_ret.
         clear. rewrite /snd. destruct pv as (pv&?).  rewrite /sval. 
         remember (a0 :: ls) as l. clear.
         induction l as [| a l] => //=.
         destruct (ltngtP a pv) => //=; nify; rewrite /partition' /= in IHl; rewrite IHl; omega.
        }
        intros (c, spl) ->.
        apply cspec_mret => //=. nify. omega.
    }
    (* TODO TODO: a good deal of this could be automated *) 
    rewrite Heql0.
    rewrite /h.
    rewrite -?pr_mbind_mret.
    f_equal.
    apply outcomes_eq_dist.
    rewrite ?ldist_assoc.
    f_equal; eapply ldist_bind_ext.
    intros (?&?). 
    eapply ldist_bind_ext.
    intros (?&?). 
    rewrite ?ldist_assoc.
    eapply ldist_bind_ext.
    intros (?&?). 
    rewrite ?ldist_assoc.
    rewrite ?ldist_left_id ?ldist_right_id.
    rewrite ?ldist_assoc.
    eapply ldist_bind_ext.
    intros (?&?). 
    rewrite ?ldist_assoc.
    eapply ldist_bind_ext.
    intros (?&?). 
    rewrite ?ldist_left_id ?ldist_right_id.
    f_equal => //=. f_equal. nify. omega. 
Qed.

Definition k := -/ ln(3/4).

Theorem bound x w:
    rsize x > 1 →  
    pr_gt (T x) (rsize x * (k * ln (rsize x) + 1) + INR w * rsize x)
       ≤ (rsize x) * (3/4)^w.
Proof.
  specialize (quicksort_rec.recurrence_work3.qs_work_bound _ _ _ _ T h').
  rewrite /size/rsize => Hrec. eapply Hrec; clear.
  - intros x' n. rewrite //=. apply Rle_ge. apply pos_INR.
  - intros l ?. rewrite //=.
    rewrite /quicksort_rec.recurrence_work3.size //=.
    cut (∀ n, INR (length (fst (snd (rvar_of_ldist (h l) n)))) + 
              INR (length (snd (snd (rvar_of_ldist (h l) n)))) <=
                   INR (length l)); first by rewrite //=.
    intros n'. apply fun_to_cspec.
    rewrite /h.
    destruct l as [| a l].
    { apply cspec_mret => //=. replace (INR 0) with 0 by auto. nra. } 
    destruct l as [| b l0].
    { apply cspec_mret => //=. replace (INR 0) with 0 by auto. replace (INR 1) with 1 by auto. nra. } 
    remember (b::l0) as l eqn:Heql0.
    clear b l0 Heql0.
    eapply (cspec_mspec _ (λ x, INR (length (fst x)) + INR (length (snd x)) <= INR (length _))).
    tbind (λ x, sval x \in a :: l).
    { intros (?&?) => //. }
    intros (pv&Hin) _. 
    tbind (λ x, lower (sval x) = [ seq n <- (a :: l) | ltn n pv] ∧
                middle (sval x) = [ seq n <- (a :: l) | n == pv] ∧
                upper (sval x) = [ seq n <- (a :: l) | ltn pv n]).
    { remember (a :: l) as l0 eqn:Heql0.
      apply mspec_mret => //=. clear. induction l0 as [|a l]; first by rewrite //=.
      rewrite //=; case (ltngtP a pv) => //= ?;
      destruct (IHl) as (?&?&?); repeat split; auto; f_equal; done.
    }
    remember (a :: l) as l0 eqn:Heql0.
    intros (spl&Hin') => //= ?. apply mspec_mret.
    move /andP in Hin'.
    destruct Hin' as (pf1&pf2); move /implyP in pf2.
    replace (length l0) with (size l0) by auto.
    rewrite -(perm_eq_size pf1) //= ?size_cat -?plusE //.
    assert (Hlt: (lt O (size (middle spl)))) by
            ( apply /ltP; apply pf2 => //=; destruct p; eauto; subst; rewrite //=).
    rewrite -plus_INR. apply le_INR. rewrite //=.
    assert (length (lower spl) = size (lower spl)) as Heq by auto.
    rewrite Heq. clear Heq.
    assert (length (upper spl) = size (upper spl)) as Heq by auto.
    rewrite Heq. clear Heq.
    clear -Hlt. rewrite //=. omega. 
  - rewrite /quicksort_rec.recurrence_work3.size //=.
    intros l ? Hgt. rewrite //=.
    cut (∀ n, INR (length (fst (snd (rvar_of_ldist (h l) n)))) + 
              INR (length (snd (snd (rvar_of_ldist (h l) n)))) <=
                   INR (length l) - 1); first by rewrite //=.
    intros n'. apply fun_to_cspec.
    rewrite /h.
    destruct l as [| a l].
    { move : Hgt. rewrite //=. replace (INR 0) with 0 by auto. nra. } 
    destruct l as [| b l0].
    { move : Hgt. rewrite //=. replace (INR 1) with 1 by auto. nra. } 
    remember (b::l0) as l eqn:Heql0.
    clear b l0 Heql0.
    eapply (cspec_mspec _ (λ x, INR (length (fst x)) + INR (length (snd x)) <= INR (length _) - 1)).
    tbind (λ x, sval x \in a :: l).
    { intros (?&?) => //. }
    intros (pv&Hin) _. 
    tbind (λ x, lower (sval x) = [ seq n <- (a :: l) | ltn n pv] ∧
                middle (sval x) = [ seq n <- (a :: l) | n == pv] ∧
                upper (sval x) = [ seq n <- (a :: l) | ltn pv n]).
    { remember (a :: l) as l0 eqn:Heql0.
      apply mspec_mret => //=. clear. induction l0 as [|a l]; first by rewrite //=.
      rewrite //=; case (ltngtP a pv) => //= ?;
      destruct (IHl) as (?&?&?); repeat split; auto; f_equal; done.
    }
    remember (a :: l) as l0 eqn:Heql0.
    intros (spl&Hin') => //= ?. apply mspec_mret.
    move /andP in Hin'.
    destruct Hin' as (pf1&pf2); move /implyP in pf2.
    replace (length l0) with (size l0) by auto.
    rewrite -(perm_eq_size pf1) //= ?size_cat -?plusE //.
    assert (Hlt: (lt O (size (middle spl)))) by
            ( apply /ltP; apply pf2 => //=; destruct p; eauto; subst; rewrite //=).
    rewrite ?plus_INR.
    assert (length (lower spl) = size (lower spl)) as Heq by auto.
    rewrite Heq. clear Heq.
    assert (length (upper spl) = size (upper spl)) as Heq by auto.
    rewrite Heq. clear Heq.
    specialize (pos_INR (size (lower (spl)))).
    specialize (pos_INR (size (upper (spl)))).
    rewrite //=. intros.
    assert (Hge1: 1 <= INR (size (middle spl))).
    { replace 1 with (INR 1) by auto. apply le_INR. omega. } 
    rewrite //= in Hge1. nra.
  - rewrite /quicksort_rec.recurrence_work3.size/quicksort_rec.recurrence_work3.d //=.
    intros x n Hle.
    replace 1 with (INR 1) in Hle by auto. apply INR_le in Hle.
    cut (INR (fst (rvar_of_ldist (qs x) n)) = 0); first by rewrite //=. 
    apply fun_to_cspec.
    destruct x; [| destruct x].
    * rewrite qs_unfold.
      apply cspec_mret => //=.
    * rewrite qs_unfold.
      apply cspec_mret => //=.
    * rewrite //= in Hle. omega.
  - intros. eapply (rec_pr_rec_gt _ rsize _ _ _ _ T h' (λ x, true)); auto; intros; apply Trec.
  - intros x. rewrite /quicksort_rec.recurrence_work3.size/quicksort_rec.recurrence_work3.d //=.
    eapply Ex_max_partition.
Qed.

From Interval Require Import Interval_tactic.
Remark concrete:
  ∀ l, rsize l = 10 ^ 8 →
       pr_gt (T l) (10^8 * (8 * 1/(ln 2) * ln (10^8))) ≤ 1/(10^10).
Proof.
  intros l Hsize.
  transitivity (pr_gt (T l) (10^8 * (k * ln (rsize l) + 1) + 147 * 10^8)).
  - apply Rge_le, pr_gt_contra.
    rewrite Hsize. rewrite /k. interval.
  - replace 147 with (INR 147); last first.
    { vm_compute. nra. } 
    rewrite -Hsize.
    etransitivity; first apply bound; auto; try nra. rewrite Hsize. interval.
Qed.

Remark concrete2:
  ∀ l, rsize l = 10 ^ 7 →
       pr_gt (T l) (10^7 * (8 * 1/(ln 2) * ln (10^7))) ≤ 1/(10^9).
Proof.
  intros l Hsize.
  transitivity (pr_gt (T l) (10^7 * (k * ln (rsize l) + 1) + 129 * 10^7)).
  - apply Rge_le, pr_gt_contra.
    rewrite Hsize. rewrite /k. interval.
  - replace 129 with (INR 129); last first.
    { vm_compute. nra. } 
    rewrite -Hsize.
    etransitivity; first apply bound; auto; try nra. rewrite Hsize. interval.
Qed.