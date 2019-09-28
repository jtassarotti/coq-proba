From discprob.basic Require Import base order nify.
From discprob.prob Require Import prob countable finite stochastic_order uniform.
From discprob.monad Require Import monad permutation.
From discprob.monad Require quicksort quicksort_cost counter.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From Coq Require Import Reals Fourier Psatz Program.Wf Omega.

Definition binomial := counter.binomial.
Fixpoint leader_elect (rounds: nat) (players: nat) : ldist (nat * nat) :=
  match rounds with
  | O => mret (O, players)
  | S rounds' =>
    match players with
      | O => mret (rounds, O)
      | 1 => mret (rounds, S O)
      | S (S _) => 
        (surv ← binomial players;
         (if sval surv == O then
            (* no one survived, so all current players repeat in next round *)
            leader_elect rounds' players
          else
            leader_elect rounds' (sval surv)))
    end
  end.

Lemma leader_elect_unfold (rounds: nat) (players: nat):
  leader_elect rounds players =
  match rounds with
  | O => mret (O, players)
  | S rounds' =>
    match players with
      | O => mret (rounds, O)
      | 1 => mret (rounds, S O)
      | S (S _) => 
        (surv ← binomial players;
         (if sval surv == O then
            leader_elect rounds' players
          else
            leader_elect rounds' (sval surv)))
    end
  end.
Proof. destruct rounds, players => //=. Qed.