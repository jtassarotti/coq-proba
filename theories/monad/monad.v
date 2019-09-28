From discprob.basic Require Import base order nify.
From discprob.basic Require Export monad.
From discprob.prob Require Import prob countable finite stochastic_order.
Require Import Reals Fourier FunctionalExtensionality Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype finset finfun bigop.


Record ldist (A: Type) := mklDist { 
  outcomes :> list (R * A);
  nonneg : all  (λ r, Rle_dec 0 r) [seq r.1 | r <- outcomes];
  sum1 : \big[Rplus/0]_(a <- map fst outcomes) a == R1
 }.  

Arguments outcomes {_}.
Arguments sum1 {_}.
Arguments mklDist {_}.

Lemma ldist_irrel A (l1 l2: ldist A) : 
  outcomes l1 = outcomes l2 → l1 = l2.
Proof.
  destruct l1 as [l1 pf1a pf1b].
  destruct l2 as [l2 pf2a pf2b] => //.
  rewrite /outcomes => ?. subst.
  f_equal; auto; exact: bool_irrelevance.
Qed.

Global Instance dist_ret: stdpp.base.MRet ldist.
  refine (λ A x, mklDist [::(R1, x)] _ _).
Proof.
{ abstract (rewrite //= andb_true_r; destruct (Rle_dec) => //=; nra). }
{ abstract (rewrite //= big_cons big_nil; apply /eqP => //=; field). }
Defined.

Definition dist_bind_aux :=
  λ {A B} (f: A → ldist B),
  fix go (l: seq (R * A)) :=
    match l with
      [::] => [::]
    | (r, x) :: l => map (λ py, (r * py.1, py.2)%R) (f x) ++ go l
    end.

Lemma dist_bind_pf1 {A B} (f: A → ldist B) d:
  all [eta (Rle_dec 0)] [seq r.1 | r <- dist_bind_aux f (outcomes d)].
Proof.
  apply /allP => r.
  destruct d as (l, pf1, pf2).
  rewrite //=; clear pf2.
  induction l as [| a l] => //=.
  destruct a as (r'&x) => //=.
  rewrite map_cat mem_cat.
  move /orP => [Hin|Hin].
  - move /allP in pf1. specialize (pf1 r'). 
    destruct (f x) as [l' pf1' pf2'].
    rewrite //= in Hin; clear pf2'.
    induction l' as [|? l'] => //=. 
    rewrite //= in_cons in Hin.
    move /orP in Hin. destruct Hin as [Heq|Hin'].
    * move /eqP in Heq. rewrite Heq. destruct (Rle_dec 0 (_ * _)) as [|Hn] => //=; try nra.
      exfalso; apply Hn.
      apply Rmult_le_0_compat.
      ** cut (is_true (Rle_dec 0 r')); first by destruct (Rle_dec 0 r') => //=.
         apply pf1. rewrite in_cons. apply /orP; by left.
      ** cut (is_true (Rle_dec 0 (fst a))); first by destruct (Rle_dec 0 (fst a)) => //=.
         move /allP in pf1'. apply pf1'. rewrite in_cons. apply /orP; by left. 
    * eapply IHl'; eauto; intros.
      rewrite //= in pf1'. move /andP in pf1'. destruct pf1'. auto. 
  - eapply IHl; eauto.
      rewrite //= in pf1. move /andP in pf1. destruct pf1. auto. 
Qed.

Lemma dist_bind_pf2 {A B} (f: A → ldist B) d:
  \big[Rplus/0]_(a<-[seq i.1 | i <- dist_bind_aux f (outcomes d)]) a == 1.
Proof.
 intros. apply /eqP.  destruct d as (l, pf1, pf2). 
 rewrite //=; clear pf1.
 revert pf2.  move /eqP. replace 1 with R1 by auto. generalize R1 as t.
 induction l as [| a l] => t.
 - rewrite big_nil //= => ?.
 - destruct a as (r, x); rewrite //= big_cons => Hsum. 
   rewrite map_cat -map_comp big_cat //= big_map //= (IHl (t - r)%R).
   * rewrite -big_distrr //=. specialize (sum1 (f x)). move /eqP. rewrite big_map => ->. field.
   * rewrite -Hsum. ring_simplify. done. 
Qed.

Global Instance dist_bind: stdpp.base.MBind ldist :=
  λ A B f d, mklDist (dist_bind_aux f (outcomes d)) (dist_bind_pf1 f d) (dist_bind_pf2 f d).

Global Program Instance dist_join: stdpp.base.MJoin ldist :=
  λ A (lld: ldist (ldist A)), 
  let fix go (ls : seq (R * ldist A)) :=
  match ls with [::] => [::] | (r, l) :: ls => [seq (r * i.1, i.2) | i <- l] ++ go ls end in
  mklDist (go lld) _ _.
Next Obligation.
  rewrite //= => A lld.
  apply /allP => r.
  destruct lld as (l, pf1, pf2).
  rewrite //=; clear pf2.
  induction l as [| a l] => //=.
  destruct a as (r'&x) => //=.
  rewrite map_cat mem_cat.
  move /orP => [Hin|Hin].
  - assert (0 ≤ r').
    { cut (is_true (Rle_dec 0 r')); first by destruct (Rle_dec 0 r') => //=.
      move /allP in pf1. apply pf1. rewrite in_cons //= eq_refl //. }
    clear pf1.
    destruct x as (l', pf1', pf2').
    rewrite //= in Hin. clear pf2'. induction l' as [| ? l'].
    { rewrite in_nil in Hin; done. }
    rewrite //= in_cons in Hin.
    move /orP in Hin. destruct Hin as [Heq|Hin'].
    * move /eqP in Heq. rewrite Heq.
      destruct (Rle_dec 0 (_ * _)) as [|Hn] => //=.
      contradiction Hn; apply Rmult_le_0_compat.
      ** auto. 
      ** cut (is_true (Rle_dec 0 (fst a))); first by destruct (Rle_dec 0 (fst a)) => //=.
         move /allP in pf1'. apply pf1'. rewrite in_cons. apply /orP; by left. 
    * eapply IHl'; eauto; intros.
      rewrite //= in pf1'. move /andP in pf1'. destruct pf1'; done.
  - eapply IHl; eauto.
    rewrite //= in pf1. move /andP in pf1. destruct pf1; done.
Qed.
Next Obligation.
 destruct lld as (l, pf1, pf2). 
 apply /eqP.
 rewrite //=; clear pf1.
 revert pf2. move /eqP. generalize R1 as t.
 induction l as [| a l] => t.
 - intros. rewrite //=.
 - destruct a as (r, x); rewrite //= big_cons => Hsum. 
   rewrite map_cat -map_comp big_cat //= big_map //= (IHl (t - r)%R). 
   * rewrite -big_distrr //=. specialize (sum1 (x)). move /eqP. rewrite big_map => ->. field.
   * rewrite -Hsum; ring_simplify; done.
Qed.

Global Program Instance dist_fmap: stdpp.base.FMap ldist :=
  λ A B (f: A → B) (ld: ldist A), 
  let fix go (l : seq (R * A)) := match l with [::] => [::] | (r, x) :: l => (r, f x) :: go l end in
  mklDist (go ld) _ _.
Next Obligation.
  intros A B f ld.
 apply /allP => r.
 destruct ld as (l, pf1, pf2). 
 rewrite //=. clear pf2.
 induction l as [|a l] => //=.
 destruct a as (r', x) => //=.
 rewrite in_cons.
 move /orP => [Heq|Hin].
 - move /eqP in Heq. rewrite Heq.
   move /andP in pf1. apply pf1.
 - apply IHl, Hin. intros. rewrite //= in pf1. move /andP in pf1.
   destruct pf1; auto.
Qed.
Next Obligation.
 intros A B f ld.
 apply /eqP.
 destruct ld as (l, pf1, pf2). 
 rewrite //=; clear pf1.
 revert pf2. move /eqP. generalize R1 as t.
 induction l as [| a l] => t.
 - intros. rewrite //=.
 - destruct a as (r, x); rewrite //= big_cons => Hsum. 
   rewrite big_cons. rewrite (IHl (t - r)%R); first field.
   rewrite -Hsum; ring_simplify; done. 
Qed.

Lemma bind_join_fmap {A B} (m: ldist A) (g: A → ldist B): 
  outcomes (mbind g m) = outcomes (mjoin (fmap g m)).
Proof.
  rewrite /mbind/mjoin/fmap/dist_bind/dist_join/dist_fmap.
  destruct m as (lm, pf1m, pf2m) => //=.
  clear pf1m pf2m.
  induction lm as [|a l] => //.
  destruct a as (r, x) => //=; f_equal; done.
Qed.

Lemma in_ldist_bind {A B : eqType} (f: A → ldist B) r (x : B) (m: ldist A) :
  (r, x) \in outcomes (x ← m; f x) → 
   ∃ r'' r' y, (r'', x) \in outcomes (f y) 
               ∧ (r', y) \in outcomes m
               ∧ r = r' * r''.
Proof.
  rewrite /mbind/dist_bind//=.
  destruct m as (l, pf1, pf2) => //=.
  clear pf1 pf2.
  induction l as [|p l IH] => //.
  rewrite //=. destruct p as (r'&y) => //=.
  rewrite mem_cat. move /orP => [Hin1|Hintl]. 
  - move /mapP in Hin1. destruct Hin1 as [[r'' y'] Hin Heq].
    rewrite //= in Heq. inversion Heq; subst. 
    exists r'', r', y; repeat split; auto.
    rewrite in_cons eq_refl //.
  - destruct IH as (r1&r2&y'&?&?&?); auto.
    exists r1, r2, y'; repeat split; auto.
    rewrite in_cons. apply /orP; by right.
Qed.

Lemma in_ldist_bind2 {A B : eqType} (f: A → ldist B) r' r'' (x : B) y (m: ldist A) :
   (r'', x) \in outcomes (f y) →
   (r', y) \in outcomes m →
   (r' * r'', x) \in outcomes (m ≫= f).
Proof.
  rewrite /mbind/dist_bind//=.
  destruct m as (l, pf1, pf2) => //=.
  clear pf1 pf2.
  induction l as [|p l IH] => //.
  rewrite //= => Hin1 Hin2'. destruct p as (?&?) => //=.
  rewrite mem_cat.
  rewrite in_cons in Hin2'. move /orP in Hin2'. destruct Hin2' as [Heq|Htl]; apply /orP.
  - left. move /eqP in Heq. inversion Heq; subst.
    apply /mapP. exists (r'',  x); auto.
  - right. apply IH; eauto.
Qed.

Lemma nth_lt_size {A: eqType} (d: A) m l (Hsize: (m < size l)%N):
  nth d l m \in l.
Proof.
  apply /all_nthP => //.
  apply /allP => x Hin //=.
Qed.

(* Every ldist can be regarded as a random variable *)
Definition dist_of_ldist {A: eqType} (ld: ldist A) : distrib [finType of ordinal (size ld)].
  apply (@mkDistrib _ (λ n, (nth R0 (map fst ld) (nat_of_ord n)))).
  - destruct a as [m Hlt]; destruct ld as (l, pf1, pf2); rewrite //=. 
    rewrite //= in Hlt. move /allP in pf1. 
    apply Rle_ge.
    cut (is_true (Rle_dec 0 (nth 0 [seq (fst i) | i <- l] m)));
      first by (destruct (Rle_dec) => //=).
    apply /pf1/nth_lt_size. rewrite size_map //.
  - destruct ld as (l, pf1, pf2); rewrite //=. move /eqP in pf2.
    replace 1 with R1 by auto.
    rewrite -pf2 -sum_index_ordinal -SeriesF_big_op.
    apply SeriesF_is_seriesC.
Defined.

Definition ld_def {A} (ld: seq (R *A) ) (n: 'I_(size ld)) : A.
  induction ld as [|(r, x)].
  - destruct n as (n&Hlt). inversion Hlt.
  - exact x.
Qed.

Lemma sum_index_ordinal_Fpair {A: eqType} (l: seq (R * A)) F:
  \big[Rplus/0]_(a in 'I_(size l)) 
   F (nth 0 [seq i.1 | i <- l] a, nth (ld_def l a) [seq i.2 | i <- l] a) =
  \big[Rplus/0]_(a<- l) F a.
Proof.  
    induction l as [| a l].
    * rewrite //= big_nil big_ord0 //. 
    * transitivity (\big[Rplus/0%R]_(0<= a' < (size l).+1) 
                     F (nth 0 ([seq i.1 | i <- a :: l]) a', (nth (snd a) ([seq i.2 | i <- a :: l]) a'))).
      { rewrite big_mkord. apply eq_bigr => ??. rewrite (set_nth_default (snd a)); first done.
        rewrite size_map. auto. }
      rewrite //= big_cons big_ltn; last auto. 
      destruct a; f_equal; rewrite big_add1 //=. rewrite -IHl big_mkord. 
      apply eq_bigr => i H. rewrite (set_nth_default (ld_def l i)); first done.        
      rewrite size_map. done.
Qed.

Definition rvar_of_ldist {A: eqType} (ld: ldist A) : rvar (dist_of_ldist ld) A :=
  mkRvar (dist_of_ldist ld) (λ n, (nth (ld_def ld n) (map snd ld) (nat_of_ord n))).

(* There must be some nice way to do this... I really need to learn ssreflect better *)
Lemma setP_help {A: finType} (P: A -> bool) (i: A):
  (pred_of_set [set x | P x]) i = P i.
Proof.
  rewrite -in_set.
  transitivity (i \in [set x | P x]); first by rewrite in_set.
  rewrite in_set. done.
Qed.

Lemma pr_rvar_ldist {A: eqType} (ld: ldist A) r :
  pr_eq (rvar_of_ldist ld) r = \big[Rplus/0%R]_(a <- outcomes ld | snd a == r) fst a.
Proof. 
  rewrite /pr_eq/pr. 
  rewrite SeriesC_fin_big -big_mkcondr.
  rewrite /dist_of_ldist //=.
  apply (sum_index_ordinal_P _ _ (R0, r)) => //= i.
  rewrite (nth_map (nth (0, r) ld i)) //.
  rewrite (set_nth_default (0, r)) //. 
Qed.

Lemma pr_gt_rvar_ldist (ld: ldist R) r :
  pr_gt (rvar_of_ldist ld) r = \big[Rplus/0%R]_(a <- outcomes ld | Rgt_dec (snd a) r) fst a.
Proof. 
  rewrite /pr_gt/pr. 
  rewrite SeriesC_fin_big -big_mkcondr.
  rewrite /dist_of_ldist //=.
  apply (sum_index_ordinal_P _ _ (R0, r)) => //= i.
  rewrite (nth_map (nth (0, r) ld i)) //.
  rewrite (set_nth_default (0, r)) //. 
Qed.

Lemma sum_mjoin {B: eqType} (lld: ldist (ldist B)) P:
  \big[Rplus/0]_(a <- outcomes (mjoin lld) | P (snd a)) a.1 =
  \big[Rplus/0]_(ld <- lld) \big[Rplus/0]_(a <- ld.2 | P (snd a)) (ld.1 * a.1).
Proof.  
  destruct lld as (lld, pf1, pf2) => //=.
  clear pf1 pf2.
  induction lld as [|[r ld] lld] => //=.
  { rewrite ?big_nil //. }
  rewrite big_cons big_cat //=.
  f_equal; eauto.
  rewrite big_map //=. 
Qed.

Lemma sum_fmap {A B} (f: A → B) (ld: ldist A) F:
  \big[Rplus/0]_(x <- outcomes (f <$> ld)) (F (x.1) (x.2)) =
  \big[Rplus/0]_(x <- ld) (F (x.1) (f x.2)).
Proof.  
  destruct ld as (ld, pf1, pf2) => //=.
  clear pf1 pf2.
  induction ld as [|[r x] ld] => //=.
  { rewrite ?big_nil //. }
  rewrite ?big_cons //=.
  f_equal; eauto.
Qed.

Lemma nat_of_ord_map_iota {A} n (F: nat → A):
  [seq (F (nat_of_ord i)) | i <- enum 'I_n] = 
  [seq (F i) | i <- iota 0%N n].
Proof.    
    by rewrite -val_enum_ord map_comp.
Qed.

Lemma nat_of_ord_map_iota' {A} n (F: nat → A):
  [seq (F (nat_of_ord i)) | i <- Finite.enum [finType of 'I_n]] = 
  [seq (F i) | i <- iota 0%N n].
Proof.    
  rewrite -nat_of_ord_map_iota. f_equal. 
  rewrite -enumT//=.
Qed.

Lemma map_nth_iota {A: eqType} (l: seq A) a:
      [seq nth a l i | i <- iota 0 (size l)] = l.
Proof. 
  induction l => //=.
  replace 1%nat with (1 + 0)%nat by auto with *.
  rewrite iota_addl -map_comp; f_equal => //=.
Qed.

Lemma img_rvar_of_ldist {A: eqType} (h: ldist A):
  map sval (Finite.enum [finType of (imgT (rvar_of_ldist h))]) = undup [seq i.2 | i <- h].
Proof.  
  rewrite {1}[@Finite.enum]unlock //=. rewrite img_fin_enum_sval.
  assert (a: A).
  { destruct h as (l, pf1, pf2). destruct l.
    - rewrite big_nil in pf2. move /eqP in pf2. exfalso.
      rewrite //= in pf2. fourier.
    - exact (snd p).
  }
  f_equal.
  etransitivity.
  - apply (@eq_map _ _ _ (λ n, nth a [seq i.2 | i <- h] (nat_of_ord n))).
    { intro i. erewrite set_nth_default; auto. rewrite size_map. done. }
  - rewrite -enumT. rewrite (nat_of_ord_map_iota (size h) (λ n, nth a [seq (snd i) | i <- h] n)). 
  destruct h as (l, pf1, pf2) => //=; clear pf1 pf2.
  rewrite -(size_map snd l) map_nth_iota //.
Qed.


Lemma img_rvar_of_ldist' {A: eqType} (h: ldist A) a:
  a \in img (rvar_of_ldist h) = (a \in undup [seq (snd i) | i <- h]).
Proof.  
  apply (introTF (exCP _)); case: ifP.
  - rewrite mem_undup. move /mapP. intros [x Hin Heq]; subst.
    rewrite //=. 
    assert (index (snd x) (map snd h) < size h)%nat as Hsize.
    { rewrite -(size_map snd) index_mem. apply /mapP. eexists; eauto. }  
    exists (Ordinal Hsize) => //=.
    rewrite nth_index => //=. apply /mapP. eexists; eauto.
  - rewrite mem_undup => Hfalse. intros (x&Heq).
    move /negP in Hfalse. apply Hfalse. move /eqP in Heq.
    rewrite -Heq. rewrite //=. apply nth_lt_size. rewrite size_map. destruct x. auto.
Qed.

(* Lemmas for simplifying monadic expressions *)
Lemma pr_mbind_ldist1 {A B: eqType} (h: ldist A) (f: A → ldist B) (b: B) :
  pr_eq (rvar_of_ldist (mbind f h)) b = 
  \big[Rplus/0]_(a : imgT (rvar_of_ldist h)) 
   (pr_eq (rvar_of_ldist h) (sval a) * pr_eq (rvar_of_ldist (f (sval a))) b).
Proof.
  transitivity (Ex (rvar_comp (rvar_of_ldist h) (λ a, pr_eq (rvar_of_ldist (f a)) b))); last first.
  { rewrite Ex_fin_comp. eapply eq_bigr => ??. field. }  
  rewrite pr_rvar_ldist Ex_fin_pt.
  symmetry. etransitivity.
  { apply eq_bigr => ?? /=. rewrite !pr_rvar_ldist. done. } 
  rewrite bind_join_fmap.
  rewrite (sum_mjoin _ (λ x, x == b)).
  rewrite (sum_fmap f h (λ x y, \big[Rplus/0]_(a <- y | a.2 == b) (x * a.1))).
  rewrite /index_enum.
  rewrite //= (sum_index_ordinal_Fpair _ (λ xy, 
     \big[Rplus/0]_(a <- f (xy.2) | a.2 == b) a.1 * (xy.1))).
  eapply eq_bigr => x _.
  rewrite Rmult_comm.
  rewrite big_distrr //.
Qed.

Lemma pr_mbind_ldist2 {A B: eqType} (h: ldist A) (f: A → ldist B) (b: B) :
  pr_eq (rvar_of_ldist (mbind f h)) b = 
  \big[Rplus/0]_(a <- undup [seq i.2 | i <- h]) 
   (pr_eq (rvar_of_ldist h) a * pr_eq (rvar_of_ldist (f a)) b).
Proof.
  rewrite -img_rvar_of_ldist pr_mbind_ldist1 //.
  rewrite big_map //=.
Qed.

Lemma pr_mret_simpl {A: eqType} (x y: A):
  pr_eq (rvar_of_ldist (mret x)) y = if (x == y) then 1 else 0.
Proof.  
  rewrite pr_rvar_ldist big_cons big_nil //=. case: ifP => ?; field.
Qed.

Lemma pr_mbind_mret {A B: eqType} (h: ldist A) (f: A → B) (b: B) :
  pr_eq (rvar_of_ldist (mbind (λ x, mret (f x)) h)) b = 
  pr_eq (rvar_comp (rvar_of_ldist h) f) b.
Proof.
  rewrite pr_mbind_ldist1 //.
  symmetry. rewrite {1}/pr_eq pr_eq_alt_comp.
  eapply eq_bigr => a _.
  rewrite pr_mret_simpl.
  case: ifP => ?; rewrite //= ?Rmult_1_r ?Rmult_0_r; done.
Qed.

Lemma pr_mbind_mret_inj {A B: eqType} (h: ldist A) (f: A → B) (a: A) :
  injective f →
  pr_eq (rvar_of_ldist (mbind (λ x, mret (f x)) h)) (f a)= 
  pr_eq (rvar_of_ldist h) a.
Proof.
  intros Hinj.
  rewrite pr_mbind_mret //= {1}/pr_eq pr_eq_alt_comp.
  rewrite {2}/pr_eq pr_eq_alt.
  eapply eq_bigr => i _. symmetry.
  case: ifP; move /eqP.
  * intros Heq1. rewrite Heq1 eq_refl. done.
  * intros Hneq. case: ifP; auto. move /eqP. intros Heq. 
    apply Hinj in Heq. congruence.
Qed.

Lemma pr_mbind_mret_inj0 {A B: eqType} (h: ldist A) (f: A → B) (b: B) :
  (∀ a, f a ≠ b) →
  pr_eq (rvar_of_ldist (mbind (λ x, mret (f x)) h)) b = 0.
Proof.
  intros Hneq. rewrite pr_mbind_mret {1}/pr_eq pr_eq_alt_comp.
  apply big1 => i _. case: ifP; auto. move /eqP => Heq. exfalso. 
  apply (Hneq (sval i)); auto.
Qed.

Lemma pr_gt_mbind_ldist1 {A: eqType} (h: ldist A) (f: A → ldist R) (b: R) :
  pr_gt (rvar_of_ldist (mbind f h)) b = 
  \big[Rplus/0]_(a : imgT (rvar_of_ldist h)) 
   (pr_eq (rvar_of_ldist h) (sval a) * pr_gt (rvar_of_ldist (f (sval a))) b).
Proof.
  transitivity (Ex (rvar_comp (rvar_of_ldist h) (λ a, pr_gt (rvar_of_ldist (f a)) b))); last first.
  { rewrite Ex_fin_comp. eapply eq_bigr => ??. field. }  
  rewrite pr_gt_rvar_ldist Ex_fin_pt.
  symmetry. etransitivity.
  { apply eq_bigr => ?? /=. rewrite !pr_gt_rvar_ldist. done. } 
  rewrite bind_join_fmap.
  rewrite (sum_mjoin _ (λ x, Rgt_dec x b)).
  rewrite (sum_fmap f h (λ x y, \big[Rplus/0]_(a <- y | Rgt_dec a.2 b) (x * a.1))).
  rewrite /index_enum.
  rewrite //= (sum_index_ordinal_Fpair _ (λ xy, 
     \big[Rplus/0]_(a <- f (xy.2) | Rgt_dec a.2 b) a.1 * (xy.1))).
  eapply eq_bigr => x _.
  rewrite Rmult_comm.
  rewrite big_distrr //.
Qed.

Lemma pr_gt_mbind_ldist2 {A: eqType} (h: ldist A) (f: A → ldist R) (b: R) :
  pr_gt (rvar_of_ldist (mbind f h)) b = 
  \big[Rplus/0]_(a <- undup [seq i.2 | i <- h]) 
   (pr_eq (rvar_of_ldist h) a * pr_gt (rvar_of_ldist (f a)) b).
Proof.
  rewrite -img_rvar_of_ldist pr_gt_mbind_ldist1 //.
  rewrite big_map //=.
Qed.

Lemma pr_gt_mret_simpl (x y: R):
  pr_gt (rvar_of_ldist (mret x)) y = if (Rgt_dec x y) then 1 else 0.
Proof.  
  rewrite pr_gt_rvar_ldist big_cons big_nil //=.
  destruct Rgt_dec => //=; try fourier; try nra.
Qed.

Lemma pr_gt_mbind_mret {A: eqType} (h: ldist A) (f: A → R) (b: R) :
  pr_gt (rvar_of_ldist (mbind (λ x, mret (f x)) h)) b = 
  pr_gt (rvar_comp (rvar_of_ldist h) f) b.
Proof.
  rewrite pr_gt_mbind_ldist1 //.
  symmetry. rewrite {1}/pr_gt pr_gt_alt_comp.
  eapply eq_bigr => a _.
  rewrite pr_gt_mret_simpl.
  destruct Rgt_dec => //=; rewrite ?Rmult_1_r ?Rmult_0_r //=.
Qed.

Lemma Ex_mbind_ldist1 {A: eqType} (h: ldist A) (f: A → ldist R) :
  Ex (rvar_of_ldist (mbind f h)) = 
  \big[Rplus/0]_(a : imgT (rvar_of_ldist h)) 
   (pr_eq (rvar_of_ldist h) (sval a) * Ex (rvar_of_ldist (f (sval a)))).
Proof.
  rewrite /Ex. rewrite SeriesC_fin_big.
  f_equal; etransitivity.
  {eapply eq_bigr => x _. rewrite pr_mbind_ldist1. rewrite big_distrl //. }
  rewrite exchange_big.
  apply eq_bigr => x _.
  rewrite SeriesC_fin_big.
  rewrite big_distrr //=. 
  rewrite /index_enum//=.
  rewrite -(big_map sval (λ x, true) (λ i, _ * pr_eq _ i * i)).
  rewrite -(big_map sval (λ x, true) (λ i, _ * (pr_eq _ i * i))).
  rewrite img_rvar_of_ldist.
  rewrite (img_rvar_of_ldist (dist_bind _ _ f h)).
  eapply sum_reidx_map_sym with (h := id).
  - intros; rewrite //=. rewrite //=. rewrite Rmult_assoc. done. 
  - intros ? Hin' ? Hnin. rewrite (pr_img_nin (rvar_of_ldist (f (sval x)))); first by ring.
    rewrite img_rvar_of_ldist'. auto.
  - intros ? Hin' ? Hnin. exfalso. apply Hnin. 
    destruct x as (x&Hin). 
    rewrite //= in Hin'. rewrite img_rvar_of_ldist' in Hin.
    rewrite ?mem_undup in Hin Hin'.
    move /mapP in Hin.
    move /mapP in Hin'.
    destruct Hin as [(r'&x') Hin1 ?]; subst. 
    destruct Hin' as [(r''&y'') Hin2 ?]; subst. 
    specialize (in_ldist_bind2 f _ _ _ _ h Hin2 Hin1). 
    rewrite //= => Hin_comb.
    exists y''.  rewrite mem_undup; split; auto.
    apply /mapP; auto.
    exists (r' * r'', y''); auto. 
  - apply undup_uniq.
  - apply undup_uniq.
  - intros ??; done. 
Qed.

Lemma Ex_mbind_ldist2 {A: eqType} (h: ldist A) (f: A → ldist R) :
  Ex (rvar_of_ldist (mbind f h)) = 
  \big[Rplus/0]_(a <- undup [seq i.2 | i <- h]) (pr_eq (rvar_of_ldist h) a * Ex (rvar_of_ldist (f a))).
Proof.
  rewrite -img_rvar_of_ldist Ex_mbind_ldist1 //. 
  rewrite big_map //=.
Qed.

Lemma Ex_mret_simpl (x: R):
  Ex (rvar_of_ldist (mret x)) = x. 
Proof.  
  rewrite /Ex SeriesC_fin_big /index_enum.
  rewrite -(big_map sval (λ x, true) (λ i, pr_eq _ i * i)).
  rewrite img_rvar_of_ldist //= big_cons big_nil.
  rewrite pr_mret_simpl eq_refl. f_equal; field.
Qed.

Lemma Ex_mbind_mret {A: eqType} (h: ldist A) (f: A → R) :
  Ex (rvar_of_ldist (mbind (λ x, mret (f x)) h)) = 
  Ex (rvar_comp (rvar_of_ldist h) f).
Proof.
  rewrite Ex_mbind_ldist1 //.
  rewrite Ex_fin_comp.
  eapply eq_bigr => a _.
  rewrite Ex_mret_simpl.
  f_equal.
Qed.

Lemma outcomes_eq_dist {A: eqType} (r1 r2: ldist A) :
  outcomes r1 = outcomes r2 → 
  eq_dist (rvar_of_ldist r1) (rvar_of_ldist r2).
Proof.
  rewrite /eq_dist => Heq x.
  rewrite ?pr_rvar_ldist Heq. done.
Qed.

Lemma ldist_left_id {A B: eqType} (x: A) (f: A → ldist B):
  mbind f (mret x) = f x.
Proof.
  apply ldist_irrel => //=. rewrite cats0.
  rewrite (@eq_map _ _ _ id); first by apply map_id.
  intros (?&?) => //=; f_equal; auto; ring_simplify; done.
Qed.

Lemma ldist_right_id {A: eqType} (m: ldist A) :
  mbind mret m = m.
Proof.
  apply ldist_irrel => //=. induction (outcomes m) as [| a l] => //=. 
  destruct a as (?&?) => //=; f_equal; auto.
  rewrite Rmult_1_r. done.
Qed.

Lemma ldist_assoc {A B C: eqType} (m: ldist A) (f: A → ldist B) (g: B → ldist C) :
  mbind g (mbind f m) = mbind (λ x, mbind g (f x)) m.
Proof.
  apply ldist_irrel.
  destruct m as [m pf1 pf2] => //=.
  clear pf1 pf2.
  assert (Haux: ∀ A B (f: A → ldist B) l1 l2, dist_bind_aux f (l1 ++ l2) = 
                               dist_bind_aux  f l1 ++ dist_bind_aux f l2).
  { induction l1 as [| a l] => //=.
    intros. destruct a as (r&x).
    rewrite IHl catA. done.
  }
  induction m as [| a l]; first by rewrite //=.
  destruct a as (r&x). 
  rewrite //= Haux; eauto.
  f_equal; eauto.
  clear -Haux. induction (outcomes (f x)) as [| a' l'] => //=.
  destruct a' as (r'&x'). rewrite map_cat; f_equal; eauto.  
  rewrite -map_comp => //=.
  apply eq_map => c. 
  destruct c as (r''&x'') => //=.
  f_equal; auto; field. 
Qed.

Lemma ldist_bind_ext {A B: eqType} m (f g: A → ldist B):
  (∀ a, f a = g a) →
  mbind f m = mbind g m.
Proof.
  destruct m as [l pf1 pf2] => Hext //=. 
  rewrite /dist_bind. 
  apply ldist_irrel => //=.
  clear pf1 pf2. induction l as [| a l] => //=.
  destruct a as (r, x). by rewrite IHl Hext.
Qed.

Lemma ldist_fmap_bind {A B C: eqType} m (h: A → B) (f: B → ldist C):
  mbind f (x ← m; mret (h x)) = mbind (λ x, f (h x)) m.
Proof.
  rewrite ldist_assoc.
  apply ldist_bind_ext => a. rewrite ldist_left_id. done.
Qed.

Lemma eq_dist_ldist_bind_ext {A B: eqType} m (f g: A → ldist B):
  (∀ a, eq_dist (rvar_of_ldist (f a)) (rvar_of_ldist (g a))) →
  eq_dist (rvar_of_ldist (mbind f m)) (rvar_of_ldist (mbind g m)).
Proof.
  rewrite /eq_dist => Heq b. rewrite ?pr_mbind_ldist2. 
  eapply eq_bigr => a _. rewrite Heq. done.
Qed.

Lemma le_dist_ldist_bind_ext {A: eqType} m (f g: A → ldist R):
  (∀ a k, pr_gt (rvar_of_ldist (f a)) k <= pr_gt (rvar_of_ldist (g a)) k) →
  (∀ k, pr_gt (rvar_of_ldist (mbind f m)) k <= pr_gt (rvar_of_ldist (mbind g m)) k).
Proof.
  rewrite /eq_dist => Heq b. rewrite ?pr_gt_mbind_ldist2. 
  apply Rle_bigr => a _. apply Rmult_le_compat_l.
  * apply Rge_le, pr_eq_ge_0. 
  * done.
Qed.

Lemma eq_dist_ldist_bind_congr {A B: eqType} m m' (f g: A → ldist B):
  eq_dist (rvar_of_ldist m) (rvar_of_ldist m') →
  (∀ a, eq_dist (rvar_of_ldist (f a)) (rvar_of_ldist (g a))) →
  eq_dist (rvar_of_ldist (mbind f m)) (rvar_of_ldist (mbind g m')).
Proof.
  rewrite /eq_dist => Hdist Heq b. rewrite ?pr_mbind_ldist2. 
  rewrite bigop_cond_non0 [a in _ = a]bigop_cond_non0.
  eapply (sum_reidx_map _ _ _ _ id). 
  - intros. rewrite Hdist Heq. done.
  - rewrite //=; intros a Hin Hnon0. rewrite -?img_rvar_of_ldist'; split.
    * apply pr_img. rewrite -Hdist. move /eqP in Hnon0.
      edestruct (ge_pr_0 (rvar_dist (rvar_of_ldist m))) as [|Heq0]; first by eauto.
      rewrite /pr_eq//= in Hnon0. rewrite Heq0 in Hnon0. nra.
    * rewrite -Heq -Hdist. done.
  - rewrite //= => a Hin. rewrite -?img_rvar_of_ldist' => Hnon0 Hfalse.
    exfalso; apply Hfalse. exists a.
    rewrite Heq Hdist; split; auto.
    rewrite -?img_rvar_of_ldist'.
    apply pr_img. rewrite Hdist. move /eqP in Hnon0.
    edestruct (ge_pr_0 (rvar_dist (rvar_of_ldist m'))) as [|Heq0]; first by eauto.
    rewrite /pr_eq in Hnon0. rewrite Heq0 in Hnon0. nra.
  - apply undup_uniq.
  - apply undup_uniq.
  - done. 
Qed.

Lemma ldist_bind_swap {A B C: eqType} (m1: ldist A) (m2: ldist B) (f: A → B → ldist C):
  eq_dist (rvar_of_ldist (a ← m1;
                            b ← m2;
                            f a b))
          (rvar_of_ldist (b ← m2;
                            a ← m1;
                            f a b)).
Proof.
  intros c. 
  rewrite ?pr_mbind_ldist2.
  etransitivity.
  { eapply eq_bigr. intros. rewrite pr_mbind_ldist2. rewrite big_distrr //. }
  symmetry.
  etransitivity.
  { eapply eq_bigr. intros. rewrite pr_mbind_ldist2. rewrite big_distrr //. }
  rewrite exchange_big.
  do 2 (eapply eq_bigr => ??).
  rewrite //=. nra.
Qed.

Lemma pr_eq_bind_pair {A B: eqType} (m1: ldist A) (m2: ldist B) (a: A) (b: B):
  pr_eq (rvar_of_ldist (a ← m1; b ← m2; mret (a, b))) (a, b) = 
  pr_eq (rvar_of_ldist m1) a * pr_eq (rvar_of_ldist m2) b.
Proof.
  rewrite ?pr_mbind_ldist2.
  etransitivity.
  { eapply eq_bigr. intros a' _. 
    rewrite pr_mbind_ldist2. apply Rmult_eq_compat_l. 
    eapply eq_bigr. intros b' _.
    rewrite pr_mret_simpl. 
    transitivity (pr_eq (rvar_of_ldist (mret a')) a *
                     (pr_eq (rvar_of_ldist m2) b' * 
                      pr_eq (rvar_of_ldist (mret b')) b)); last done.
    rewrite ?pr_mret_simpl.
    case: ifP; move /eqP => Heq.
    - inversion Heq as [[Heqa Heqb]]. 
      subst. rewrite ?eq_refl. nra.
    - case: ifP; move /eqP => Heqa.
      { case: ifP; move /eqP => Heqb.
        * subst. congruence.
        * nra.
      }
      nra.
  }
  etransitivity.
  {
    eapply eq_bigr. intros. rewrite -big_distrr.
    rewrite -pr_mbind_ldist2. rewrite -Rmult_assoc. done.
  }
  rewrite -big_distrl. rewrite ldist_right_id //=; f_equal.
  specialize (pr_mbind_ldist2 m1 (λ x, mret x)) => //=. intros <-.
  (* For some reason I cannot just do the appropriate rewrite... *)
  assert (Hfinal: ∀ {A: eqType} (m1: ldist A) a,
             pr_eq (rvar_of_ldist (x ← m1; mret x)) a = pr_eq (rvar_of_ldist m1) a).
  { intros.  rewrite ldist_right_id. done. }
  eapply Hfinal.
Qed.

Lemma eq_dist_bind_rvar_pair {A B: eqType} (m1: ldist A) (m2: ldist B):
  eq_dist (rvar_of_ldist (a ← m1; b ← m2; mret (a, b)))
          (rvar_pair (rvar_of_ldist m1) (rvar_of_ldist m2)).
Proof.
  intros (a&b). rewrite pr_eq_bind_pair pr_eq_rvar_pair //.
Qed.

Program Definition bernoulli (p: R) (Hrange: (0 <= p <= 1)%R) : ldist bool :=
  mklDist [:: (p, true) ; (1 - p, false)%R] _ _.
Next Obligation.
  rewrite //=; intros p (?&?);
  repeat (apply /andP; split; auto); destruct (Rle_dec) => //. nra.
Qed.
Next Obligation.
  rewrite //=; intros p (?&?);
  rewrite ?big_cons ?big_nil; apply /eqP => //=; field.
Qed.

Lemma pr_bernoulli_true (p: R) (Hrange: 0 <= p <= 1):
  pr_eq (rvar_of_ldist (bernoulli p Hrange)) true = p.
Proof.
  rewrite pr_rvar_ldist //= ?big_cons ?big_nil //=. field.
Qed.

Lemma pr_bernoulli_false (p: R) (Hrange: 0 <= p <= 1):
  pr_eq (rvar_of_ldist (bernoulli p Hrange)) false = 1 - p.
Proof.
  rewrite pr_rvar_ldist //= ?big_cons ?big_nil //=. field.
Qed.

Module test.
 
  
  Program Definition test1 : ldist (bool * bool) :=
    x ← bernoulli (1/2) _ ;
    y ← bernoulli (1/2) _;
    mret (x, y).
  Next Obligation. split; fourier. Qed.
  Next Obligation. split; fourier. Qed.
   
  (* Eval compute in (outcomes test1). *)

  Definition von_neumann_coin (p: R) (Hrange: 0 <= p <= 1): ldist (option bool) :=
    x ← bernoulli p Hrange;
    y ← bernoulli p Hrange;
    match x, y with
      | true, false => mret (Some true)
      | false, true => mret (Some false)
      | _, _ => mret None
    end.

  Fixpoint von_neumann_repeat (p: R) (Hrange: 0 <= p <= 1) (n: nat): ldist (option bool) :=
    match n with 
      | 0 => mret None
      | S n' => 
        res ← von_neumann_coin p Hrange;
        match res with
          | None => von_neumann_repeat p Hrange n'
          | _ => mret res
        end
    end.
  
  Lemma range_three_fourths: 0 <= 3/4 <= 1. Proof. split; fourier. Qed.
  (* Eval compute in (outcomes (von_neumann_coin (3/4) range_three_fourths)). *)

  Lemma von_neumann_fair (p: R) (Hrange: 0 <= p <= 1) :
    pr_eq (rvar_of_ldist (von_neumann_coin p Hrange)) (Some true) = 
    pr_eq (rvar_of_ldist (von_neumann_coin p Hrange)) (Some false).
  Proof.
    rewrite ?pr_rvar_ldist //= ?big_cons ?big_nil //=. field.
  Qed.

  Lemma von_neumann_fail (p: R) (Hrange: 0 <= p <= 1) :
    pr_eq (rvar_of_ldist (von_neumann_coin p Hrange)) None = 
    1 - 2 * (p * (1 - p)).
  Proof.
    rewrite ?pr_rvar_ldist //= ?big_cons ?big_nil //=. field.
  Qed.

  (* These are not yet the most efficient ways to prove these; 
     mainly ``brute-force'' computation; see below for a way that uses
     facts about monadic operations and a simple 'coupling' argument *)
  Lemma von_neumann_repeat_fair (p: R) (Hrange: 0 <= p <= 1) n :
    pr_eq (rvar_of_ldist (von_neumann_repeat p Hrange n)) (Some true) = 
    pr_eq (rvar_of_ldist (von_neumann_repeat p Hrange n)) (Some false).
  Proof.
    induction n.
    - rewrite ?pr_rvar_ldist //= ?big_cons ?big_nil //=. 
    - rewrite ?pr_rvar_ldist //= ?big_cons ?big_nil //=. 
      rewrite ?big_cat //=. f_equal.
      * rewrite ?big_map //= -?big_distrr; f_equal.
        by rewrite ?pr_rvar_ldist in IHn.
      * rewrite ?cats0. 
        rewrite ?big_cons //=; f_equal; first field.
        rewrite ?big_map //= -?big_distrr; f_equal.
        by rewrite ?pr_rvar_ldist in IHn.
  Qed.

  Lemma von_neumann_repeat_fail n (p: R) (Hrange: 0 <= p <= 1) :
    pr_eq (rvar_of_ldist (von_neumann_repeat p Hrange n)) None = 
    (1 - 2 * (p * (1 - p)))^n.
  Proof.
    induction n.
    - rewrite ?pr_rvar_ldist //= ?big_cons ?big_nil //=. field.
    - rewrite ?pr_rvar_ldist //= ?big_cons ?big_nil //=. 
      rewrite ?cats0 ?big_cat //=.
      rewrite ?pr_rvar_ldist in IHn.
      rewrite ?big_map -?big_distrr //= IHn.
      rewrite ?big_cons //=.
      rewrite ?big_map //= -?big_distrr //= IHn.
      field.
  Qed.

  Lemma von_neumann_repeat_fair' (p: R) (Hrange: 0 <= p <= 1) n :
    pr_eq (rvar_of_ldist (von_neumann_repeat p Hrange n)) (Some true) = 
    pr_eq (rvar_of_ldist (von_neumann_repeat p Hrange n)) (Some false).
  Proof.
    induction n.
    - rewrite ?pr_rvar_ldist //= ?big_cons ?big_nil //=. 
    - rewrite !pr_mbind_ldist2.
      (* Coupling *)
      eapply (sum_reidx_surj2 _ _ _ _ _ _
                            (λ a, match a with | Some b => Some (negb b) | None => None end )).
      * destruct a => ?. 
        ** f_equal; destruct s; rewrite ?von_neumann_fair //=;
          rewrite (pr_rvar_ldist (dist_ret _ (Some true)));
          rewrite (pr_rvar_ldist (dist_ret _ (Some false)));
          rewrite //= ?big_cons ?big_nil //=; try field.
        ** f_equal. eauto.
      * intros [[|]|]; rewrite //=.
      * intros [[|]|]; rewrite //=.
      * apply undup_uniq. 
      * apply undup_uniq. 
      * intros [[|]|] [[|]|] => //=.
  Qed.
  
  Lemma von_neumann_repeat_fail' n (p: R) (Hrange: 0 <= p <= 1) :
    pr_eq (rvar_of_ldist (von_neumann_repeat p Hrange n)) None = 
    (1 - 2 * (p * (1 - p)))^n.
  Proof.
    induction n.
    - rewrite ?pr_rvar_ldist //= ?big_cons ?big_nil //=. field.
    - rewrite pr_mbind_ldist2.
      rewrite {1}/von_neumann_coin. 
      rewrite ?big_cons ?big_nil IHn //=. 
      rewrite von_neumann_fail //=.
      rewrite ?pr_mret_simpl //=; field.
  Qed.

End test.

