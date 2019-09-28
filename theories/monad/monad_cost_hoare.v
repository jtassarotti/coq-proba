From discprob.basic Require Import base order.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad monad_cost.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier Psatz Omega.

(* The following form of writing down a spec for the output of the monad comes
   from how Adam Chlipala does monadic reasoning in his PoplMark challenge solution;
   the idea is simple but it helps guide tactics to write things in this form *)

Definition output {A} (p: ldist_cost A) := [seq i.2.2 | i <- outcomes p].
Definition coutput {A} (p: ldist_cost A) := [seq i.2 | i <- outcomes p].

Definition mspec {A: eqType} (m: ldist_cost A) (P: A → Prop) :=
  ∀ y, y \in output m → P y.

Lemma mspec_mret {A: eqType} (x: A) (P: A → Prop):
  P x → mspec (mret x) P.
Proof.
  intros HP y. rewrite /mret/ldist_cost_ret/mret/dist_ret/output//= mem_seq1.
  move /eqP => -> //.
Qed.

Lemma output_mbind_in {A B: eqType} b (m: ldist_cost A) (f: A → ldist_cost B):
  (b \in output (x ← m; f x)) →
  ∃ r c a, ((r, (c, a)) \in outcomes m) ∧ (b \in output (f a)).
Proof.
  rewrite /mbind/ldist_cost_bind/output. 
  move /mapP => [[r [c b'] Hin]] => //= ->.
  eapply (in_ldist_bind _ r (c, b') m) in Hin as (r'&r''&(c', a)&Hin1&Hin2&Heq).
  exists r'', c', a; split; first done. 
  eapply (in_ldist_bind _ r' (c, b') (f a)) in Hin1 as (?&?&(?&?)&Hin3&Hin4&?).
  subst. rewrite //= mem_seq1 in Hin3. move /eqP in Hin3. inversion Hin3; subst.
  apply /mapP; eauto.
Qed.

Lemma mspec_mbind {A B: eqType} (f: A → ldist_cost B) m (P: A → Prop) (Q: B → Prop):
  mspec m P →
  (∀ a, P a → mspec (f a) Q) →
  mspec (mbind f m) Q.
Proof.
  intros Hinput Hbody b Hin.
  edestruct (output_mbind_in b m f) as (r&c&a&Hin'&Hout); eauto.
  eapply Hbody; eauto. apply Hinput; eauto.
  apply /mapP; eauto.
Qed.

Tactic Notation "tbind" open_constr(P) :=
  match goal with
  | [ |- mspec (mbind ?f ?m) ?Q ] =>
    intros; eapply (@mspec_mbind _ _ f m P); auto
  | [ |- mspec (base.mbind ?f ?m) ?Q ] =>
    intros; eapply (@mspec_mbind _ _ f m P); auto
  end.

Definition cspec {A: eqType} (m: ldist_cost A) (P: nat * A → Prop) :=
  ∀ y, y \in coutput m → P y.

Lemma cspec_mret {A: eqType} (x: A) (P: nat * A → Prop):
  P (O, x) → cspec (mret x) P.
Proof.
  intros HP y. rewrite /mret/ldist_cost_ret/mret/dist_ret/output//= mem_seq1.
  move /eqP => -> //.
Qed.

Lemma cspec_dist_ret {A: eqType} x (P: nat * A → Prop):
  P x → cspec (dist_ret _ x) P.
Proof.
  intros HP y. rewrite /mret/ldist_cost_ret/mret/dist_ret/output//= mem_seq1.
  move /eqP => -> //.
Qed.

Lemma fun_to_cspec {A: eqType} (m: ldist_cost A) (P: nat * A → Prop):
  cspec m P → (∀ x, P ((rvar_of_ldist m) x)).
Proof. 
  rewrite /cspec/coutput => Hspec /= x.
  apply /Hspec/mem_nth. rewrite size_map. inversion x. done.
Qed.

Lemma coutput_mbind_in {A B: eqType} b (m: ldist_cost A) (f: A → ldist_cost B):
  (b \in coutput (x ← m; f x)) →
  ∃ r c a, ((r, (c, a)) \in outcomes m) ∧ ((fst b - c)%nat, snd b) \in coutput (f a) 
                                         ∧ (fst b - c + c = fst b)%nat.
Proof.
  rewrite /mbind/ldist_cost_bind/output. 
  move /mapP => [[r [c b'] Hin]] => //= ->.
  eapply (in_ldist_bind _ r (c, b') m) in Hin as (r'&r''&(c', a)&Hin1&Hin2&Heq).
  eapply (in_ldist_bind _ r' (c, b') (f a)) in Hin1 as (?&?&(?&?)&Hin3&Hin4&?).
  subst. rewrite //= mem_seq1 in Hin3. move /eqP in Hin3. inversion Hin3; subst.
  exists r'', c', a; repeat split; first done. 
  - apply /mapP; eauto.
    eexists; eauto => //=; f_equal; auto with *. 
  - rewrite //=. rewrite -?plusE -?minusE. omega.
Qed.

Lemma cspec_mbind {A B: eqType} (f: A → ldist_cost B) m (P: nat * A → Prop) (Q: nat * B → Prop):
  cspec m P →
  (∀ a, P a → cspec (f (snd a)) (λ nb, Q ((fst a + fst nb)%nat, snd nb)))→
  cspec (mbind f m) Q.
Proof.
  intros Hinput Hbody nb Hin.
  edestruct (coutput_mbind_in nb m f) as (r&c&a&Hin'&Hout&Heq); eauto.
  destruct nb as (nb1&nb2). rewrite //= in Heq. rewrite -Heq. rewrite addnC. 
  replace c with (fst (c, a)); last done. specialize (Hbody (c, a)).
  rewrite /cspec//= in Hbody. rewrite //= in Hout. rewrite //=.
  assert (HP: P (c, a)).                                                   
  { apply Hinput. rewrite/ coutput. apply /mapP => //=. eauto. }
  eapply (Hbody HP ((nb1 - c)%nat, nb2)); auto.
Qed.

Lemma cspec_mspec {A: eqType} (m: ldist_cost A) (P: A → Prop):
  mspec m P → cspec m (λ x, P (snd x)).
Proof. 
  rewrite /mspec/cspec/coutput/output => Hin y.
  move /mapP => [[c x] Hin' Heq].
  subst. apply Hin. apply /mapP. eauto.
Qed.

Tactic Notation "cbind" open_constr(P) :=
  match goal with
  | [ |- cspec (mbind ?f ?m) ?Q ] =>
    intros; eapply (@cspec_mbind _ _ f m P); auto
  end.

Lemma Ex_bound {A : eqType} (X: ldist_cost A) f r: 
  cspec X (λ x, f x <= r) →
  Ex (rvar_comp (rvar_of_ldist X) f) <= r.    
Proof.
  intros Hcspec. rewrite Ex_fin_comp.
  eapply Rle_trans.
  { 
    eapply Rle_bigr => i _. 
    apply Rmult_le_compat_l; last apply Hcspec.
    - apply Rge_le, ge_pr_0.
    - destruct i as (?&?) => //=. rewrite /coutput -mem_undup -img_rvar_of_ldist' //.
  }
  rewrite -big_distrl //= (pr_sum_all (rvar_of_ldist X)) Rmult_1_l. fourier. 
Qed.