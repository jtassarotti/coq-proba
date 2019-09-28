From discprob.basic Require Import base order.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier Psatz Omega.

Definition output {A} (p: ldist A) := [seq i.2 | i <- outcomes p].

Definition mspec {A: eqType} (m: ldist A) (P: A → Prop) :=
  ∀ y, y \in output m → P y.

Lemma mspec_mret {A: eqType} (x: A) (P: A → Prop):
  P x → mspec (mret x) P.
Proof.
  intros HP y. rewrite /mret/dist_ret/output//= mem_seq1.
  move /eqP => -> //.
Qed.

Lemma mspec_conseq {A: eqType} (m: ldist A) (P Q: A → Prop):
  mspec m P → (∀ a, P a → Q a) → mspec m Q.
Proof.
  intros HP HPQ a Hin. apply HPQ; eauto.
Qed.


Lemma output_mbind_in {A B: eqType} b (m: ldist A) (f: A → ldist B):
  (b \in output (x ← m; f x)) →
  ∃ r a, ((r, a)) \in outcomes m ∧ (b \in output (f a)).
Proof.
  rewrite /mbind/output. 
  move /mapP => [[r b' Hin]] => //= ->.
  eapply (in_ldist_bind _ r b' m) in Hin as (r'&r''&c'&Hin1&Hin2&Heq).
  exists r'', c'; split; auto. apply /mapP; eauto.
Qed.

Lemma mspec_mbind {A B: eqType} (f: A → ldist B) m (P: A → Prop) (Q: B → Prop):
  mspec m P →
  (∀ a, P a → mspec (f a) Q) →
  mspec (mbind f m) Q.
Proof.
  intros Hinput Hbody b Hin.
  edestruct (output_mbind_in b m f) as (r&?&Hin'&Hout); eauto.
  eapply Hbody; eauto. apply Hinput; eauto.
  apply /mapP; eauto.
Qed.

Tactic Notation "tbind" open_constr(P) :=
  match goal with
  | [ |- mspec (mbind ?f ?m) ?Q ] =>
    intros; eapply (@mspec_mbind _ _ f m P); auto
  end.

Lemma fun_to_mspec {A: eqType} (m: ldist A) (P: A → Prop):
  mspec m P → (∀ x, P ((rvar_of_ldist m) x)).
Proof. 
  rewrite /mspec/output => Hspec /= x.
  apply /Hspec/mem_nth. rewrite size_map. inversion x. done.
Qed.

Lemma mspec_range_eq_dist {A: eqType} (m1 m2: ldist A) (P: pred A):
  mspec m1 P →
  mspec m2 P → 
  (∀ a, P a → pr_eq (rvar_of_ldist m1) a = pr_eq (rvar_of_ldist m2) a) →
  eq_dist (rvar_of_ldist m1) (rvar_of_ldist m2).
Proof.
  intros Hm1 Hm2 Hin_eq a.
  specialize (Hm1 a). rewrite //= in Hm1.
  specialize (Hm2 a). rewrite //= in Hm2.
  specialize (Hin_eq a).
  case_eq (P a).
  - intros HP. apply Hin_eq. auto.
  - intros HnP. transitivity 0; last symmetry.
    * apply pr_img_nin. intros Hin. move /negP in HnP. apply HnP.
      apply Hm1. by rewrite /output -mem_undup -img_rvar_of_ldist'.
    * apply pr_img_nin. intros Hin. move /negP in HnP. apply HnP.
      apply Hm2. by rewrite /output -mem_undup -img_rvar_of_ldist'.
Qed.

Lemma mspec_eq_dist_ldist_bind_ext {A B: eqType} m P (f g: A → ldist B):
  mspec m P →
  (∀ a, P a → eq_dist (rvar_of_ldist (f a)) (rvar_of_ldist (g a))) →
  eq_dist (rvar_of_ldist (mbind f m)) (rvar_of_ldist (mbind g m)).
Proof.
  intros Hspec.
  rewrite /eq_dist => Heq b. rewrite ?pr_mbind_ldist1. 
  eapply eq_bigr => a _. rewrite Heq; first done.
  apply Hspec. rewrite /output.
  rewrite -mem_undup -img_rvar_of_ldist'.
  destruct a as (x&Hin) => //=.
Qed.

Lemma Ex_bound {A : eqType} (X: ldist A) f r: 
  mspec X (λ x, f x <= r) →
  Ex (rvar_comp (rvar_of_ldist X) f) <= r.    
Proof.
  intros Hmspec. rewrite Ex_fin_comp.
  eapply Rle_trans.
  { 
    eapply Rle_bigr => i _. 
    apply Rmult_le_compat_l; last apply Hmspec.
    - apply Rge_le, ge_pr_0.
    - destruct i as (?&?) => //=. rewrite /output -mem_undup -img_rvar_of_ldist' //.
  }
  rewrite -big_distrl //= (pr_sum_all (rvar_of_ldist X)) Rmult_1_l. fourier. 
Qed.