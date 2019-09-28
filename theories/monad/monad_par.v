From discprob.basic Require Import base order nify monad.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Fourier Psatz Omega.
Require Import Arith.

Section parcost.
(*
Record cost (A: eqType) := mkCost {
    result : A;
    work : nat;
    span : nat
  }.
  
Definition cost A := (nat * nat * A)%type.
Definition ldist_cost A := ldist (cost A).

Definition result {A} (a: cost A) : A := snd a.
Definition work {A} (a: cost A) : nat := fst (fst a).
Definition span {A} (a: cost A) : nat := snd (fst a).

Arguments result {_} _ /.
Arguments work {_} _ /.
Arguments span {_} _ /.

Definition mkCost {A} (work: nat) (span: nat) (result: A) := (work, span, result).
*)

Record cost A := mkCost {
    work : nat;
    span : nat;
    result : A;
  }.
Definition ldist_cost A := ldist (cost A).

Global Arguments result {_} _.
Global Arguments work {_} _.
Global Arguments span {_} _.
Global Arguments mkCost {_}.

Definition cost_eq_bool {A: eqType} (a b : cost A) : bool :=
  (result a == result b) && (work a == work b) && (span a == span b).
Lemma eq_cost {A: eqType} : Equality.axiom (@cost_eq_bool A).
Proof.
move=> [l1 m1 u1] [l2 m2 u2].
apply: (iffP idP); rewrite /cost_eq_bool //=.
- move /andP => [Hand ?].
  move /andP in Hand. destruct Hand as (?&?).
  f_equal; apply /eqP; done.
- inversion 1; subst.
  apply /andP; split; auto.
  apply /andP; split; auto.
Qed.
  
Canonical cost_eqMixin A := EqMixin (@eq_cost A).
Canonical cost_eqType A := Eval hnf in EqType (cost _) (cost_eqMixin A).

Local Open Scope stdpp_scope.
Local Open Scope nat_scope.

Global Instance cost_bind: MBind cost :=
  λ A B (f: A → cost B) x,
  mkCost (work x + work (f (result x))) 
         (span x + span (f (result x)))
         (result (f (result x))).

Global Instance cost_ret: MRet cost :=
  λ A x, mkCost 0 0 x.

Lemma cost_left_id {A B: eqType} (x: A) (f: A → cost B):
  mbind f (mret x) = f x.
Proof.
  rewrite /cost_bind//=; destruct (f x); f_equal => //=.
Qed.

Lemma cost_right_id {A: eqType} (m: cost A) :
  mbind mret m = m.
Proof.
  destruct m => //=. rewrite /cost_bind//=; repeat f_equal => //=.
Qed.

Lemma cost_assoc {A B C: eqType} (m: cost A) (f: A → cost B) (g: B → cost C) :
  mbind g (mbind f m) = mbind (λ x, mbind g (f x)) m.
Proof.
  destruct m => //=. rewrite /cost_bind; f_equal => //=; nify; ring.
Qed.

Global Instance ldist_cost_bind: MBind ldist_cost :=
  λ A B f (x: ldist_cost A),
  a ← x;
  b ← f (result a);
  mret {| result := result b; work := work a + work b; span := span a + span b |}.
Global Instance ldist_cost_ret: MRet ldist_cost :=
  λ A x, mret {| result := x; work := 0; span := 0|}. 

Lemma ldist_cost_bind_fold {A B} (f: A → ldist_cost B) (x: ldist_cost A):
  (a ← x;
  b ← f (result a);
  mret {| result := result b; work := work a + work b; span := span a + span b |} )
       = mbind f x.
Proof.
  symmetry. rewrite {1}/mbind/ldist_cost_bind. done.
Qed.

Lemma ldist_cost_left_id {A B: eqType} (x: A) (f: A → ldist_cost B):
  mbind f (mret x) = f x.
Proof.
  rewrite /mbind/base.mbind/ldist_cost_bind. 
  rewrite ldist_left_id -[a in _ = a]ldist_right_id /mbind.
  apply ldist_bind_ext => a. 
  destruct a as [w s a] => //=.
Qed.

Definition rpar2 {A B} (x: ldist_cost A) (y: ldist_cost B) : ldist_cost (A * B) :=
  a ← x;
  b ← y;
  mret {| result := (result a, result b) ; work := work a + work b; span := max (span a) (span b) |}.

Definition rpar3 {A B C} x y z : ldist_cost (A * B * C) :=
  a ← x;
  b ← y;
  c ← z;
  mret {| result := (result a, result b, result c) ; 
          work := work a + work b + work c;
          span := max (span a) (max (span b) (span c)) |}.

Definition par2 {A B} (a: cost A) (b: cost B) : cost (A * B) :=
  {| result := (result a, result b) ; work := work a + work b; span := max (span a) (span b) |}.

Definition par3 {A B C} a b c : cost (A * B * C) :=
 {| result := (result a, result b, result c) ; 
          work := work a + work b + work c;
          span := max (span a) (max (span b) (span c)) |}.

Fixpoint redcost {A} (l: list (cost A)) : cost (list A) :=
  match l with
    | [::] => {| result := [::]; work := 0; span := 0 |}
    | a :: l => {| result := result a :: (result (redcost l));
                   work := work a + work (redcost l);
                   span := max (span a) (span (redcost l)) |}
  end.
  
(* This is simplified in that the mapping function f needs to be deterministic *)
Definition parmap {A B} (f: A → cost B) (x: list A): cost (list B) :=
  redcost (map f x).

(*
Lemma parmap_foldleft {A B} (f: A → cost B) (x: list A):
  parmap f x = fold_left (λ (b: cost (list B)) a, x ← f a;
                                 y ← b;
                                 mret (y ++ [::x])) x (cost_ret _ [::]).
Proof.
Abort.
*)


Definition parflatten {A} (ls: list (list A)) : cost (list A) :=
   {| result := flatten ls; work := 0; span := 0 |}.
(*
Definition parmap {A B} (f: A → cost B) (x: list A): ldist_cost (list B) :=
  dist_ret _ (redcost (map f x)).
Definition parflatten {A} (ls: list (list A)) : ldist_cost (list A) :=
  dist_ret _ {| result := flatten ls; work := 0; span := 0 |}.
*)

Definition parfilter {A} (P: A → cost bool) (xs: list A) : cost (list A) :=
  ys ← parmap (λ a : A, b ← P a ;
                     mret (match b with
                           | true => a :: [::]
                           | false => [::]
                           end : seq A)) xs;
  parflatten ys.

(*
Definition parmap {A B} (x: ldist_cost (list A)) (f: A → cost B) : ldist_cost (list B) :=
  al ← x;
  dist_ret _ (redcost (map f al)).
*)


End parcost.

Require Import Reals Fourier FunctionalExtensionality.

Lemma ldist_cost_right_id {A: eqType} (m: ldist_cost A) :
  mbind mret m = m.
Proof.
  rewrite /mbind/ldist_cost_bind. 
  apply ldist_irrel=>//=.
  destruct m as [l pf1 pf2] => //=; clear pf1 pf2.
  induction l => //=. destruct a as (r, x) => //=.
  destruct x as [w s a] => //=. 
  rewrite ?Rmult_1_r; repeat f_equal => //.
Qed.

Lemma ldist_cost_assoc {A B C: eqType} (m: ldist_cost A) 
      (f: A → ldist_cost B) (g: B → ldist_cost C) :
  mbind g (mbind f m) = mbind (λ x, mbind g (f x)) m.
Proof.
  rewrite /mbind/base.mbind/ldist_cost_bind. 
  rewrite !ldist_assoc.
  apply ldist_bind_ext => x.
  destruct x.
  rewrite !ldist_assoc.
  apply ldist_bind_ext => x.
  destruct x.
  rewrite !ldist_assoc.
  rewrite ldist_left_id.
  apply ldist_bind_ext => x.
  destruct x.
  rewrite ldist_left_id.
  rewrite //=. do 2 f_equal; rewrite addnA; done. 
Qed.

Lemma ldist_cost_bind_semi_work {B C} (m: ldist_cost B) (g: nat → C) w1 s1:
  (x ← b ← m;
  mret {| work := w1 + work b; span := s1 + span b; result := result b|};
  mret (g (work x))) = 
  x ← m;
  mret (g (work x + w1)%nat).
Proof.
  apply ldist_irrel=>//=.
  destruct m as [l pf1 pf2] => //=; clear pf1 pf2.
  induction l => //=. destruct a as (r, x) => //=.
  destruct x.
  rewrite ?Rmult_1_r /=.
  f_equal; auto.
  f_equal; auto.
  f_equal; rewrite addnC //.
Qed.

Lemma ldist_cost_bind_semi_span {B C} (m: ldist_cost B) (g: nat → C) w1 s1:
  (x ← b ← m;
  mret {| work := w1 + work b; span := s1 + span b; result := result b|};
  mret (g (span x))) = 
  x ← m;
  mret (g (span x + s1)%nat).
Proof.
  apply ldist_irrel=>//=.
  destruct m as [l pf1 pf2] => //=; clear pf1 pf2.
  induction l => //=. destruct a as (r, x) => //=.
  destruct x.
  rewrite ?Rmult_1_r /=.
  f_equal; auto.
  f_equal; auto.
  f_equal; rewrite addnC //.
Qed.

Lemma ldist_cost_bind_drop_work {B C} (m: ldist_cost B) (h: B → ldist C) (g: nat → C):
  (x ← (x ← m; mret (h x)) ;
  mret (g (work x))) = 
  x ← m;
  mret (g (work x)%nat).
Proof.
  apply ldist_irrel=>//=.
  destruct m as [l pf1 pf2] => //=; clear pf1 pf2.
  induction l => //=. destruct a as (r, x) => //=.
  rewrite ?Rmult_1_r /=.
  f_equal; auto.
  rewrite addn0.
  f_equal; auto.
Qed.

Lemma cost_bind_const {A B C: eqType} w0 s0 (h: ldist_cost A) (f: A → ldist_cost B) 
      (g: nat → C) (c: C):
  (∀ d', d' \in [seq (work i.2) | i <- outcomes h] → d' = w0) →
  (∀ d', d' \in [seq (span i.2) | i <- outcomes h] → d' = s0) →
  pr_eq (rvar_comp (rvar_of_ldist (mbind f h)) (λ x, g (span x))) c = 
  \big[Rplus/0]_(a <- undup [seq (result i.2) | i <- h]) 
   (pr_eq (rvar_comp (rvar_of_ldist h) result) a
    * pr_eq (rvar_comp (rvar_of_ldist (f a)) (λ x, g (span x + s0)%nat)) c).
Proof.
  intros Hconstw Hconsts.
  rewrite -pr_mbind_mret ldist_assoc.
  rewrite pr_mbind_ldist2. symmetry.
  eapply sum_reidx_surj1 with (h := λ x, {| work := w0; span := s0; result := x|}).
  - intros a0 Hin. symmetry.
    rewrite -(pr_mbind_mret (f a0)). 
    rewrite ldist_cost_bind_semi_span; f_equal.
    rewrite /pr_eq pr_eq_alt_comp. rewrite pr_eq_alt.
    rewrite -?big_mkcondr.
    apply eq_bigl.
    rewrite /=. intros x.
    destruct x as ([w' s' a]&Hin') => //=.
    rewrite img_rvar_of_ldist' in Hin'.
    rewrite mem_undup in Hin'. move /mapP in Hin'. 
    destruct Hin' as [(r&[w''' s''' a'']) ? Heq]; subst.
    assert (s' = s0) as ->.
    { apply Hconsts. apply /mapP. eexists; eauto. rewrite //=. inversion Heq. congruence. }
    assert (w' = w0) as ->.
    { apply Hconstw. apply /mapP. eexists; eauto. rewrite //=. inversion Heq. congruence. }
    apply /eq_cost. case: ifP.
    * move /eqP => ->; done.
    * move /eqP => Hneq. inversion 1. congruence.
  - intros a0. rewrite !mem_undup.  move /mapP.
    intros [(r&a) ? Heq] _.
    split; auto. apply /mapP. exists (r, a); auto.
    rewrite //=. f_equal; auto. 
    destruct a as [w s a]. rewrite //= in Heq.
    f_equal; auto.
    * symmetry. apply Hconstw. apply /mapP; eexists; eauto.
    * symmetry. apply Hconsts. apply /mapP; eexists; eauto.
  - intros [w s a].  rewrite !mem_undup => Hin _.
    exists a. repeat split; auto.
    rewrite mem_undup. rewrite map_comp.
    apply /mapP. eexists; eauto.
    f_equal. 
    * symmetry; apply Hconstw. rewrite map_comp. apply /mapP. eexists; eauto.
    * symmetry; apply Hconsts. rewrite map_comp. apply /mapP. eexists; eauto.
  - apply undup_uniq.
  - apply undup_uniq.
  - intros ??.  congruence. 
Qed.

Lemma ldist_cost_rpair_span {B1 B2: eqType} {C: eqType} (m1: ldist_cost B1) (m2: ldist_cost B2) 
      (g: nat → C) (c: C):
  pr_eq (rvar_comp (rvar_of_ldist (rpar2 m1 m2))
                   (λ x, g (span x))) c =
  pr_eq (rvar_comp (rvar_pair (rvar_comp (rvar_of_ldist m1) span) 
                              (rvar_comp (rvar_of_ldist m2) span))
                   (λ xy, g (max (fst xy) (snd xy))%nat)) c.
Proof.
  rewrite -pr_mbind_mret rvar_pair_comp rvar_comp_comp.
  rewrite ldist_assoc.
  rewrite pr_mbind_ldist2.
  symmetry.
  rewrite {1}/pr_eq pr_eq_alt_comp.
  etransitivity.
  { eapply eq_bigr => i _. rewrite pr_eq_rvar_pair. done. } 
  rewrite -(big_map _ (λ x, true) (λ i, if g (max (span (fst i)) (span (snd i)))%nat == c then
                                pr_eq _ (fst i) * pr_eq _ (snd i) 
                                 else 
                                   0)).
              
  rewrite /index_enum.
  rewrite (eq_big_perm _ (img_pair_rv _ _ _ _)).
  rewrite  big_Rplus_allpair'.
  rewrite -(big_map _ (λ x, true) (λ i, \big[Rplus/0]_(i' <- _) 
                                         (if (g (max (span (fst (i, _)))
                                                     (span (snd (i, _)))) == c)%nat
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
  rewrite ldist_assoc.
  rewrite pr_mbind_ldist2.
  rewrite -(big_map _ (λ x, true) (λ i, (if (g (max (span (fst (_, i))) (span (snd (_, i)))) == c)%nat
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
  rewrite ?ldist_left_id pr_mret_simpl //=.
Qed.

Module tests.

Local Open Scope nat_scope.
  
Definition incr (x: nat) : cost nat :=
  {| result := S x; work := 1; span := 1 |}.

Eval compute in (parmap incr (1 :: 2 :: 3 :: [::])).

Remark Hrange: (0 <= 1/2 <= 1)%R.
Proof. split; fourier. Qed. 

Program Definition foo  : ldist_cost (seq nat) :=
  x ← (y ← bernoulli (1/2) Hrange;
        mret {| result := y; work := 0; span := 0|});
  if (x : bool) then
    dist_ret _ (parmap incr (1 :: 2 :: 3 :: [::]))
  else
    a ← (dist_ret _ (parmap incr (1 :: 2 :: 3 :: [::])));
    dist_ret _ (parmap incr a).
Eval compute in (outcomes foo).

Program Definition foo'  : ldist_cost (seq nat) :=
  vs ← foo;
  dist_ret _ (parfilter (λ x, mret (x == 3)) vs).

Eval compute in (outcomes foo').

End tests.
