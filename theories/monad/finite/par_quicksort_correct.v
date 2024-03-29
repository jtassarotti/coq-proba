From discprob.basic Require Import base order.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad.finite Require Import monad monad_par par_quicksort monad_par_hoare.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From mathcomp Require Import path.
Require Import Lia Coq.Program.Wf Coq.Arith.Wf_nat.

Lemma perm_eq_cat {A: eqType} (l1a l1b l2a l2b: seq A) :
  perm_eq l1a l2a →
  perm_eq l1b l2b →
  perm_eq (l1a ++ l1b) (l2a ++ l2b).
Proof.
  move /permP => Hpa.
  move /permP => Hpb.
  apply /permP.
  intros x. rewrite ?count_cat. rewrite (Hpa x) (Hpb x). done.
Qed.

Lemma sorted_cat {A: eqType} (l1 l2: seq A) (R: rel A):
  sorted R l1 → sorted R l2 →
  (∀ n1 n2, n1 \in l1 → n2 \in l2 → R n1 n2) →
  sorted R (l1 ++ l2).
Proof.
  revert l2. induction l1 => //=.
  intros l2 HP Hsorted Hle.
  rewrite cat_path. apply /andP; split; auto.
  induction l2 => //=. apply /andP; split; auto.
  apply Hle.
  - apply mem_last.
  - rewrite in_cons eq_refl //.
Qed.

Lemma quicksort_correct (l: list nat): mspec (qs l) (λ l', (sorted leq l' && perm_eq l l'):Prop).
Proof.
  remember (size l) as k eqn:Heq.
  revert l Heq.
  induction k as [k IH] using (well_founded_induction lt_wf) => l Heq.
  destruct l as [| a l].
  - rewrite //= => b. rewrite mem_seq1. move /eqP => -> //=.
  - destruct l as [| b0 l0].
    { rewrite //= => b. rewrite mem_seq1. move /eqP => -> //=. }
    rewrite qs_unfold.
    remember (b0 :: l0) as l eqn:Hl0. clear l0 Hl0.
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
    intros (spl&Hin'). intros (Hl&Hm&Hu). rewrite //= in Hl, Hm, Hu.
    tbind (λ x, (sorted leq (fst x) && perm_eq (lower spl) (fst x)) ∧
                (sorted leq (snd x) && perm_eq (upper spl) (snd x))).
    { rewrite //=.
      eapply (mspec_rpar2 _ _ (λ x, (sorted leq x && perm_eq (lower spl) x))
                              (λ x, (sorted leq x && perm_eq (upper spl) x))).
      - eapply (IH (size (lower spl))); auto.
        rewrite Heq.
        move /andP in Hin'.
        destruct Hin' as (pf1&pf2); move /implyP in pf2.
        rewrite -(perm_size pf1) //= ?size_cat -?plusE //;
          assert (Hlt: (lt O (size (middle spl)))) by
            ( apply /ltP; apply pf2 => //=; destruct p; eauto; subst; rewrite //=).
        rewrite //= in Hlt. lia.
      - eapply (IH (size (upper spl))); auto.
        rewrite Heq.
        move /andP in Hin'.
        destruct Hin' as (pf1&pf2); move /implyP in pf2.
        rewrite -(perm_size pf1) //= ?size_cat -?plusE //;
          assert (Hlt: (lt O (size (middle spl)))) by
            ( apply /ltP; apply pf2 => //=; destruct p; eauto; subst; rewrite //=).
        rewrite //= in Hlt. lia.
    }
    intros (ll&lu) (Hll&Hlu).
    move /andP in Hll. destruct Hll as (Hllsorted&Hllperm).
    move /andP in Hlu. destruct Hlu as (Hlusorted&Hluperm).
    apply mspec_mret => //=. apply /andP; split.
    * apply sorted_cat; [| apply sorted_cat |]; auto.
      ** rewrite Hm. clear. induction l0 => //=.
         case: ifP; auto.
         move /eqP => ->. rewrite //=.
         clear IHl0.
         induction l0 => //=.
         case: ifP; auto. move /eqP => -> //=. rewrite leqnn IHl0 //.
      ** rewrite Hm => a' b'; rewrite mem_filter.
         move /andP => [Heqpv Hin1 Hin2]. move /eqP in Heqpv.
         move: Hin2.
         rewrite -(perm_mem Hluperm) Hu mem_filter.
         move /andP => [Hgtpv ?]. move /ltP in Hgtpv.
         rewrite Heqpv. apply /leP. lia.
      ** intros a' b'. rewrite -(perm_mem Hllperm) Hl mem_filter.
         move /andP => [Hgtpv ?]. move /ltP in Hgtpv.
         rewrite mem_cat. move /orP => [].
         *** rewrite Hm; rewrite mem_filter.
             move /andP => [Heqpv ?]. move /eqP in Heqpv.
             rewrite Heqpv. apply /leP. lia.
         *** rewrite -(perm_mem Hluperm) Hu mem_filter.
             move /andP => [Hltpv ?]. move /ltP in Hltpv.
             apply /leP. lia.
    * move /andP in Hin'. destruct Hin' as (Hperm&_).
      rewrite perm_sym in Hperm.
      rewrite (perm_trans Hperm) //.
      repeat apply perm_eq_cat; auto.
Qed.
