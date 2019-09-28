From discprob.basic Require Import base order nify.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad monad_hoare bst.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From Coq Require Import Omega Program.Wf MSets.MSetInterface MSets.MSetGenTree Structures.OrdersEx.
Local Open Scope nat_scope.

(* This shows that the result of "add list random" is equivalent to adding the elements
   of the list according to some permutation *)

Lemma alr_correct (l: list nat) (t: tree): 
  mspec (add_list_random l t) (λ t': tree, ∃ l', t' = add_list l' t ∧ perm_eq l l').
Proof.
 remember (size l) as k eqn: Heq.
 revert t l Heq.
 induction k as [k IH] using (well_founded_induction lt_wf) => t l Heq.
 destruct l as [| a l]; last destruct l as [| b l].
 - rewrite alr_unfold. apply mspec_mret. exists [::] => //=.
 - rewrite alr_unfold. apply mspec_mret. exists [::a] => //=.
 - rewrite alr_unfold.
   tbind (λ x, sval x \in a :: b :: l).
   { intros (?&?) => //. }
   intros (x&Hin) _.
   eapply (mspec_conseq). 
   { rewrite /sval. eapply (IH (size (rem x [:: a, b & l]))).
     * subst. rewrite size_rem //=. 
     * done.
   }
   intros t' (l'&Heq'&Hperm). 
   exists (x :: l'); split; auto.
   eapply perm_eq_trans; first apply (perm_to_rem Hin); eauto.
   rewrite perm_cons. done.
Qed.