From discprob.basic Require Import base order nify sval.
From discprob.prob Require Import prob countable finite stochastic_order uniform.
From discprob.monad.finite Require quicksort quicksort_cost.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From Coq Require Import Omega Psatz Program.Wf MSets.MSetInterface MSets.MSetGenTree Structures.OrdersEx Reals.


From discprob.monad.finite Require Import monad permutation.

(* Samples an element uniformly from a list by drawing a position *)
Definition uniform_from_list {A} (a : A) (l: list A) : ldist A :=
  idx ← unif (size l);
  mret ((seq.nth a (a :: l) (sval idx))).

(* Clips p to lie between 0 and 1, to form a valid probability *)
Definition Rclip (p: R) : { x : R | 0 <= x <= 1}.
Proof. exists (Rmax (Rmin 0 p) 1). abstract (apply Rmax_case_strong; apply Rmin_case_strong; nra). Defined.

(* bernoulli requires a proof that its input prob be bounded; this is a wrapper that clips the probability *)
Definition bernoulli_clipped (p: R) : ldist bool :=
  let p' := Rclip p in
  bernoulli (sval p') (proj2_sig p').

Definition do_transition {A} (trans_prob: A -> A -> R) (other_states : list A) (current: A) : ldist A :=
  next ← uniform_from_list current other_states;
  b ← bernoulli_clipped (trans_prob current next);
  mret (if b then next else current).
