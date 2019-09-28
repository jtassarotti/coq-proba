From discprob.basic Require Import base order nify.
From discprob.prob Require Import prob countable finite stochastic_order uniform.
From discprob.monad Require Import monad permutation.
From discprob.monad Require quicksort quicksort_cost.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From Coq Require Import Reals Fourier Psatz Program.Wf Omega.

Lemma range_half: 0 <= 1/2 <= 1.
Proof. nra. Qed.

Lemma range_half_pow c: 0 <= 1 / (2 ^ c) <= 1.
Proof.
  induction c; first by (rewrite //=; split; nra). 
  replace (1 /2 ^ (S c)) with (1/2 * 1/(2 ^ c)); last first.
  { rewrite //=. field. clear; induction c => //=; nra.  }
  nra.
Qed.

Definition flip := bernoulli (1/2) range_half.
Definition flipn k := bernoulli (1/(2^k)) (range_half_pow k).


Lemma bernoulli_powS c:
  eq_dist (rvar_of_ldist (bernoulli (1/(2 ^ (S c))) (range_half_pow (S c))))
          (rvar_of_ldist ( b1 ← bernoulli (1/2) range_half;
                           b2 ← bernoulli (1/(2 ^ c)) (range_half_pow c);
                           mret (b1 && b2))).
Proof.
  intros b. repeat (rewrite pr_mbind_ldist2 ?big_cons big_nil).
  rewrite ?pr_mret_simpl.
  destruct b => //=; rewrite ?pr_bernoulli_true ?pr_bernoulli_false;
  field; apply Rgt_not_eq; induction c => //=; nra.
Qed.

Lemma flipnS c:
  eq_dist (rvar_of_ldist (flipn (S c)))
          (rvar_of_ldist ( b1 ← flip; 
                           b2 ← flipn c;
                           mret (b1 && b2))).
Proof. rewrite /flipn/flip; apply bernoulli_powS. Qed.

Lemma pr_flip_true: pr_eq (rvar_of_ldist flip) true = 1/2.
Proof. rewrite /flip; apply pr_bernoulli_true. Qed.

Lemma pr_flip_false: pr_eq (rvar_of_ldist flip) false = 1/2.
Proof. rewrite /flip; rewrite pr_bernoulli_false; nra. Qed.

Lemma pr_flipn_true c:
  pr_eq (rvar_of_ldist (flipn c)) true = 1 / (2 ^ c).
Proof. rewrite /flipn; rewrite pr_bernoulli_true //. Qed. 

Lemma pr_flipn_false c:
  pr_eq (rvar_of_ldist (flipn c)) false = 1 - 1 / (2 ^ c).
Proof. rewrite /flipn; rewrite pr_bernoulli_false //. Qed. 

Lemma flip_unfold:
  flip = bernoulli (1/2) (range_half).
Proof.
  done.
Qed.
  

Opaque flip.
Opaque flipn.
Opaque dist_bind.
Opaque dist_ret.

Definition approx_incr (c: nat) : ldist nat :=
  b ← flipn c;
    mret (if (b : bool) then
            S c
          else
            c).
          
Fixpoint approx_incrn (n: nat) (c: nat) : ldist nat :=
  match n with
    | 0 => mret c
    | S n' => 
      c' ← approx_incrn n' c;
      approx_incr c'
  end.

Fixpoint approx_incr' (c: nat) : ldist nat :=
  match c with
    | O => mret (S O)
    | S c' => 
      b ← flip;
      if (b : bool) then
        result ← approx_incr' c';
        mret (S result)
      else
        mret c
  end.

Lemma approx_incr'_unfold (c: nat):
  approx_incr' c =
  match c with
    | O => mret (S O)
    | S c' => 
      b ← flip;
      if (b : bool) then
        result ← approx_incr' c';
        mret (S result)
      else
        mret c
  end.
Proof. destruct c; auto. Qed.

Lemma eq_dist_approx_incr_incr' c:
  eq_dist (rvar_of_ldist (approx_incr c))
          (rvar_of_ldist (approx_incr' c)).
Proof.
  induction c as [| c].
  - intros n.
    rewrite //=/approx_incr/approx_incr'//=.
    specialize (pr_mbind_ldist2 (flipn 0) (λ b, mret (if b then (S O) else O)) n).
    rewrite //= => ->. 
    rewrite ?big_cons big_nil.
    rewrite //= pr_bernoulli_true pr_bernoulli_false.
    field.
  - rewrite /approx_incr approx_incr'_unfold.
    eapply eq_dist_trans.
    { eapply (eq_dist_ldist_bind_congr _ _ _ _ (flipnS c)); done. }
    rewrite [a in eq_dist _ a]//=.
    rewrite ldist_assoc. 
     apply eq_dist_ldist_bind_ext.
    intros b. 
    destruct b; last first. 
    { rewrite /andb. rewrite ldist_fmap_bind.
      intros n. rewrite ?pr_mbind_ldist2 !big_cons !big_nil pr_bernoulli_true pr_bernoulli_false.
      rewrite //=. rewrite !pr_mret_simpl. 
        case: ifP; intros; nra.
    }
    rewrite /andb. rewrite !ldist_fmap_bind. simpl size. 
    intros. 
    eapply (eq_dist_trans _ _ 
                          (rvar_of_ldist 
                             (x ← (x ← flipn c; mret (if (x : bool) then S c else c));
                               mret (S x)))).
    { rewrite ldist_fmap_bind.  eapply eq_dist_ldist_bind_ext => x.
      destruct x => //=. }
    eapply eq_dist_ldist_bind_congr; last done.
    rewrite /approx_incr in IHc. intros x. 
    rewrite IHc. done. 
Qed.

Fixpoint binomial (n: nat) : ldist { x: nat | (x <= n)%nat}.
  refine(match n with
    | 0 => mret (exist _ O _)
    | S n' => 
      b ← flip;
      rest ← binomial n';
      if (b : bool) then
        mret (exist _ (S (sval rest)) _ )
      else
        mret (exist _ (sval rest) _)
  end); auto.
  - abstract (destruct rest => //=; nify; omega).
  - abstract (destruct rest => //=; nify; omega).
Defined.

Lemma binomial_unfold n:
  binomial n = 
  match n as n0 return (ldist {x : nat | (x <= n0)%nat}) with
  | 0%nat => mret (exist (λ x : nat, (x <= 0)%nat) 0%nat (leqnn 0))
  | n'.+1 =>
      b ← flip;
      rest ← binomial n';
      (if (b : bool)
       then mret (exist (λ x : nat, (x <= n'.+1)%nat) (sval rest).+1 (binomial_subproof n' rest))
       else mret (exist (λ x : nat, (x <= n'.+1)%nat) (sval rest) (binomial_subproof0 n' rest)))
  end.
Proof. rewrite {1}/binomial. destruct n => //=. Qed. 

Definition approx_incr'_bulk : nat → ldist (nat).
  refine(Fix lt_wf (fun _ => ldist (nat))
  (fun incrs approx_incrn' => 
  match incrs as incrs' return (incrs = incrs' → ldist (nat)) with
    | O => λ eq, mret O
    | (S O) => λ eq, mret (S O)
    | (S (S n')) => λ eq,
      surv ← binomial (S n');
      result ← approx_incrn' (sval surv) _;
      mret (S result)
  end (Init.Logic.eq_refl))); auto.
Proof.
  abstract (destruct surv as (x&i) => //=; subst => //=; nify; rewrite //= in i; omega). 
Defined.

Lemma approx_incr'_bulk_unfold_aux n:
  approx_incr'_bulk n =
  match n as n' return (n = n' → ldist (nat)) with
    | O => λ eq, mret O
    | (S O) => λ eq, mret (S O)
    | (S (S n')) => λ eq,
      surv ← binomial (S n');
      result ← approx_incr'_bulk (sval surv);
      mret (S result)
  end (Init.Logic.eq_refl). 
Proof. rewrite /approx_incr'_bulk quicksort.easy_fix_eq; done. Qed.

Lemma approx_incr'_bulk_unfold n:
  approx_incr'_bulk n =
  match n with
    | O => mret O
    | (S O) => mret (S O)
    | (S (S n')) =>
      surv ← binomial (S n');
      result ← approx_incr'_bulk (sval surv);
      mret (S result)
  end.
Proof. 
  rewrite approx_incr'_bulk_unfold_aux.
  destruct n as [| n] => //. destruct n as [|  n] => //. 
Qed.

Fixpoint approx_incrn'  (n: nat) (c: nat) :=
  match n with
    | 0 => mret c
    | S n' =>
      c' ← approx_incrn' n' c;
      approx_incr' c'
  end.

Lemma approx_incrn'_right k:
      eq_dist (rvar_of_ldist (approx_incr'_bulk (S k)))
              (rvar_of_ldist (x ← approx_incr'_bulk k; approx_incr' x)).
Proof. 
  induction k as [k IH] using (well_founded_induction lt_wf).
  destruct k as [| k]; last destruct k as [| k].
  - subst. rewrite ?approx_incr'_bulk_unfold ldist_left_id//=.
  - subst. rewrite ?approx_incr'_bulk_unfold ldist_left_id.
    rewrite /binomial/approx_incr'. rewrite ldist_assoc.
    apply eq_dist_ldist_bind_ext => b.
    rewrite ldist_assoc ldist_left_id.
    destruct b.  
    * rewrite /sval ldist_left_id. rewrite approx_incr'_bulk_unfold. done.
    * rewrite /sval ldist_left_id. rewrite approx_incr'_bulk_unfold ldist_left_id. done.
  - subst. rewrite approx_incr'_bulk_unfold binomial_unfold ldist_assoc. 
   rewrite approx_incr'_bulk_unfold => v.
   rewrite pr_mbind_ldist2. 
   rewrite {1}flip_unfold ?big_cons ?big_nil pr_flip_true pr_flip_false. rewrite /snd.
   rewrite ?ldist_fmap_bind/sval.
   symmetry.
   rewrite ldist_assoc.
   rewrite ?pr_mbind_ldist2.
   rewrite Rplus_0_r.
   rewrite -Rmult_plus_distr_l.
   rewrite -big_split. rewrite big_distrr.
   apply eq_bigr. intros (k'&Hsize) _.
   rewrite //= -Rmult_plus_distr_l -Rmult_assoc (Rmult_comm ( 1 / 2)).
   rewrite Rmult_assoc; f_equal.
   specialize (@ldist_fmap_bind).
   rewrite //=/base.mbind => ->.
   specialize (IH k').
   assert (Hinj: injective (succn)).
   { intros ??. congruence. } 
   assert (Hbound: ((k' < (S (S k))))%coq_nat).
   { rewrite //=.  rewrite //= in Hsize.  nify. omega. }
   specialize (IH Hbound).
   etransitivity.
   {
     eapply eq_dist_ldist_bind_ext => c.
     rewrite approx_incr'_unfold.
     done.
   }
   rewrite ldist_bind_swap pr_mbind_ldist2 ?big_cons ?big_nil Rplus_0_r.
   rewrite /snd pr_flip_true pr_flip_false.
   rewrite -Rmult_plus_distr_l.
   rewrite -ldist_assoc.
   f_equal.
   destruct v as [| v]. 
   * rewrite ?pr_mbind_mret_inj0 //.
   * rewrite ?pr_mbind_mret_inj //. rewrite IH. done.
Qed.

Lemma eq_dist_approx_incr'_bulk (k: nat):
  eq_dist (rvar_of_ldist (approx_incr'_bulk k))
          (rvar_of_ldist (approx_incrn' k O)).
Proof.
  induction k as [k IH] using (well_founded_induction lt_wf).
  destruct k as [| k]; last destruct k as [| k].
  - subst. rewrite approx_incr'_bulk_unfold/size/approx_incrn'//=.
  - subst. rewrite approx_incr'_bulk_unfold/size/approx_incrn'.
    rewrite ldist_left_id/approx_incr'. done.
  - subst. rewrite approx_incr'_bulk_unfold.
    rewrite /approx_incrn' -/approx_incrn'.
    apply eq_dist_sym.
    eapply eq_dist_trans.
    { eapply eq_dist_ldist_bind_congr. 
      - apply eq_dist_sym. apply (IH (S k)).
        rewrite //=.
      - done.
    }
    eapply eq_dist_trans.
    { eapply eq_dist_sym. apply: approx_incrn'_right.  }
    rewrite approx_incr'_bulk_unfold. done.
Qed.

Lemma eq_dist_approx_incrn_incrn' n c:
  eq_dist (rvar_of_ldist (approx_incrn n c))
          (rvar_of_ldist (approx_incrn' n c)).
Proof.
  induction n.
  - by done. 
  - rewrite //=. apply eq_dist_ldist_bind_congr. 
      * apply IHn. 
      * apply eq_dist_approx_incr_incr'.
Qed.

Lemma eq_dist_approx_incrn_bulk n:
  eq_dist (rvar_of_ldist (approx_incrn n O))
          (rvar_of_ldist (approx_incr'_bulk n)).
Proof.
  eapply eq_dist_trans.
  - eapply eq_dist_approx_incrn_incrn'. 
  - apply eq_dist_sym. apply eq_dist_approx_incr'_bulk.
Qed.