From discprob.basic Require Import base order nify monad.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Fourier Psatz Omega.
Require Import Arith.


Section cost.
Definition cost A := (nat * A)%type.
Definition ldist_cost A := ldist (cost A).

Local Open Scope stdpp_scope.
Local Open Scope nat_scope.

Global Instance cost_bind: stdpp.base.MBind cost :=
  λ A B (f: A → cost B) x,
  (x.1 + (f (x.2)).1, (f (x.2)).2).
Global Instance cost_ret: stdpp.base.MRet cost :=
  λ A x, (0, x).

Lemma cost_left_id {A B: eqType} (x: A) (f: A → cost B):
  mbind f (mret x) = f x.
Proof.
  rewrite /cost_bind//=; destruct (f x); f_equal => //=.
Qed.

Lemma cost_right_id {A: eqType} (m: cost A) :
  mbind mret m = m.
Proof.
  destruct m => //=. rewrite /cost_bind; f_equal => //=.
Qed.

Lemma cost_assoc {A B C: eqType} (m: cost A) (f: A → cost B) (g: B → cost C) :
  mbind g (mbind f m) = mbind (λ x, mbind g (f x)) m.
Proof.
  destruct m => //=. rewrite /cost_bind; f_equal => //=. nify; ring.
Qed.

Notation MBind := stdpp.base.MBind.
Global Instance ldist_cost_bind: MBind ldist_cost :=
  λ A B f x,
  '(c1, a) ← x;
  '(c2, b) ← f a;
  mret (c1 + c2, b).
Global Instance ldist_cost_ret: MRet ldist_cost :=
  λ A x, mret (0, x).

Lemma ldist_cost_bind_fold {A B} (f: A → ldist_cost B) (x: ldist_cost A):
  '(c1, a) ← x;
  '(c2, b) ← f a;
  mret (c1 + c2, b) = mbind f x.
Proof.
  symmetry. rewrite {1}/mbind/ldist_cost_bind. done.
Qed.

Lemma ldist_cost_left_id {A B: eqType} (x: A) (f: A → ldist_cost B):
  mbind f (mret x) = f x.
Proof.
  specialize (@ldist_left_id).
  rewrite /mbind/ldist_cost_bind/ldist_cost//= => ->.
  rewrite -[a in _ = a]ldist_right_id /mbind.
  apply ldist_bind_ext => a. 
  destruct a as (c, a) => //=.
Qed.

End cost.

Require Import Reals Fourier FunctionalExtensionality.

Lemma ldist_cost_right_id {A: eqType} (m: ldist_cost A) :
  mbind mret m = m.
Proof.
  rewrite /mbind/ldist_cost_bind. 
  apply ldist_irrel=>//=.
  destruct m as [l pf1 pf2] => //=; clear pf1 pf2.
  induction l => //=. destruct a as (r, x) => //=.
  destruct x as (c, a) => //=. 
  rewrite ?Rmult_1_r; repeat f_equal => //.
Qed.

Lemma ldist_cost_assoc {A B C: eqType} (m: ldist_cost A) 
      (f: A → ldist_cost B) (g: B → ldist_cost C) :
  mbind g (mbind f m) = mbind (λ x, mbind g (f x)) m.
Proof.
  rewrite /mbind/base.mbind/ldist_cost_bind. 
  rewrite !ldist_assoc.
  apply ldist_bind_ext => x.
  destruct x as (c, a). 
  rewrite !ldist_assoc.
  apply ldist_bind_ext => x.
  destruct x as (c', b).
  rewrite !ldist_assoc.
  rewrite ldist_left_id.
  apply ldist_bind_ext => x.
  destruct x as (c'', z).
  rewrite ldist_left_id.
  do 2 f_equal. rewrite addnA. done. 
Qed.

Lemma ldist_cost_bind_semi {B C} (m: ldist_cost B) (g: nat → C) c1:
  (x ← '(c2, b) ← m;
  mret (c1 + c2, b)%nat;
  mret (g (fst x))) = 
  x ← m;
  mret (g (fst x + c1)%nat).
Proof.
  apply ldist_irrel=>//=.
  destruct m as [l pf1 pf2] => //=; clear pf1 pf2.
  induction l => //=. destruct a as (r, x) => //=.
  destruct x as (c, a) => //=. 
  rewrite ?Rmult_1_r /=.
  f_equal; auto.
  f_equal; auto.
  f_equal; rewrite addnC //.
Qed.

Lemma ldist_cost_bind_drop {B C} (m: ldist_cost B) (h: B → ldist C) (g: nat → C):
  (x ← (x ← m; mret (h x)) ;
  mret (g (fst x))) = 
  x ← m;
  mret (g (fst x)%nat).
Proof.
  apply ldist_irrel=>//=.
  destruct m as [l pf1 pf2] => //=; clear pf1 pf2.
  induction l => //=. destruct a as (r, x) => //=.
  destruct x as (c, a) => //=. 
  rewrite ?Rmult_1_r /=.
  f_equal; auto.
  rewrite addn0.
  f_equal; auto.
Qed.

Lemma cost_bind_const {A B C: eqType} d (h: ldist_cost A) (f: A → ldist_cost B) (g: nat → C) (c: C):
  (∀ d', d' \in [seq i.2.1 | i <- outcomes h] → d' = d) →
  pr_eq (rvar_comp (rvar_of_ldist (mbind f h)) (λ x, g (fst x))) c = 
  \big[Rplus/0]_(a <- undup [seq i.2.2 | i <- h]) 
   (pr_eq (rvar_comp (rvar_of_ldist h) snd) a
    * pr_eq (rvar_comp (rvar_of_ldist (f a)) (λ x, g (fst x + d)%nat)) c).
Proof.
  intros Hconst.
  rewrite -pr_mbind_mret ldist_assoc.
  rewrite pr_mbind_ldist2. symmetry.
  eapply sum_reidx_surj1 with (h := λ x, (d, x)).
  - intros a0 Hin. symmetry.
    rewrite -(pr_mbind_mret (f a0)). 
    rewrite ldist_cost_bind_semi; f_equal.
    rewrite /pr_eq pr_eq_alt_comp. rewrite pr_eq_alt.
    (* rewrite img_rvar_of_ldist. *)
    rewrite -?big_mkcondr.
    apply eq_bigl.
    rewrite /=. intros x.
    destruct x as ((d'&a)&Hin') => //=.
    rewrite img_rvar_of_ldist' in Hin'.
    rewrite mem_undup in Hin'. move /mapP in Hin'. 
    destruct Hin' as [(r&d'''&a'') ? Heq]; subst.
    assert (d' = d) as ->.
    { apply Hconst. apply /mapP. eexists; eauto. rewrite //=. inversion Heq. congruence. }
    rewrite //=.
    cut ((d, a) == (d, a0) = (a == a0)).
    { intros  Heq'. rewrite Heq'. done. }
    (* There must be a better way to rewrite this automatically!!!! *)
    apply /pair_eqP. case: ifP. move /eqP. intros; congruence. 
    move /eqP. intros. inversion 1. congruence.
  - intros a0. rewrite !mem_undup.  move /mapP.
    intros [(r&d'&a) ? Heq] _.
    split; auto. apply /mapP. exists (r, (d', a)); auto.
    rewrite //=. f_equal; auto. symmetry; apply Hconst.
    apply /mapP. eexists; eauto. 
  - intros (d', a).  rewrite !mem_undup => Hin _.
    exists a. repeat split; auto.
    rewrite mem_undup. rewrite map_comp.
    apply /mapP. eexists; eauto.
    f_equal. symmetry; apply Hconst.
    rewrite map_comp. apply /mapP. eexists; eauto.
  - apply undup_uniq.
  - apply undup_uniq.
  - intros ??.  congruence. 
Qed.


Lemma ldist_cost_pair {B1 B2: eqType} {C D: eqType} (m1: ldist_cost B1) (m2: ldist_cost B2) 
      (h: B1 → B2 → D) (g: nat → C) (c: C):
  pr_eq (rvar_comp (rvar_of_ldist ((x ← m1; y ← m2; mret (h x y) : ldist_cost D)))
                   (λ x, g (fst x))) c =
  pr_eq (rvar_comp (rvar_pair (rvar_comp (rvar_of_ldist m1) fst) 
                              (rvar_comp (rvar_of_ldist m2) fst)) (λ xy, g (fst xy + snd xy)%nat)) c.
Proof.
  rewrite -pr_mbind_mret rvar_pair_comp rvar_comp_comp.
  rewrite ldist_assoc.
  rewrite pr_mbind_ldist2.
  symmetry.
  rewrite {1}/pr_eq pr_eq_alt_comp.
  etransitivity.
  { eapply eq_bigr => i _. rewrite pr_eq_rvar_pair. done. } 
  rewrite -(big_map _ (λ x, true) (λ i, if g (fst (fst i) + fst (snd i))%nat == c then
                                pr_eq _ (fst i) * pr_eq _ (snd i) 
                                 else 
                                   0)).
              
  rewrite /index_enum.
  rewrite (eq_big_perm _ (img_pair_rv _ _ _ _)).
  rewrite  big_Rplus_allpair'.
  rewrite -(big_map _ (λ x, true) (λ i, \big[Rplus/0]_(i' <- _) 
                                         (if (g (fst (fst (i, _)) + fst (snd (i, _))) == c)%nat
                                          then
                                            pr_eq _ (fst (i, _)) *
                                            pr_eq _ (snd (i, _))
                                          else
                                            0))). 
  rewrite img_rvar_of_ldist.
  apply eq_bigr => a _. 
  etransitivity.
  { eapply eq_bigr => i _. 
    rewrite -[a in (if (_ : bool) then _ else a) = _](Rmult_0_r (pr_eq (rvar_of_ldist m1) a)).
    rewrite Rmult_comm -(Rmult_comm 0) -Rmult_if_distrib Rmult_comm. done.
  }
  rewrite -big_distrr. apply Rmult_eq_compat_l.
  destruct a as (c', b).
  rewrite ldist_assoc.
  rewrite ldist_assoc.
  rewrite pr_mbind_ldist2.
  rewrite -(big_map _ (λ x, true) (λ i, (if (g (fst (fst (_, i)) + fst (snd (_, i))) == c)%nat
                                          then
                                            pr_eq _ (snd (_, i))
                                          else
                                            0))). 
  rewrite img_rvar_of_ldist.
  eapply eq_bigr => a' _.
    rewrite -[a in (if (_ : bool) then _ else a) = _](Rmult_0_r (pr_eq (rvar_of_ldist m2) a')).
    rewrite -[a in (if (_ : bool) then a else _) = _](Rmult_1_r (pr_eq (rvar_of_ldist m2) a')).
    rewrite Rmult_comm -(Rmult_comm 0) -Rmult_if_distrib Rmult_comm.
  apply Rmult_eq_compat_l.
  destruct a' as (c'', b2).
  rewrite ?ldist_left_id pr_mret_simpl /= addn0 //.
Qed.