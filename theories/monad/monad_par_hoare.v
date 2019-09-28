From discprob.basic Require Import base order nify.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad monad_par.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier Psatz Omega.

(* The following form of writing down a spec for the output of the monad comes
   from how Adam Chlipala does monadic reasoning in his PoplMark challenge solution;
   the idea is simple but it helps guide tactics to write things in this form *)

Definition output {A} (p: ldist_cost A) := [seq (result i.2) | i <- outcomes p].
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
  ∃ r a, ((r, a)) \in outcomes m ∧ (b \in output (f (result a))).
Proof.
  rewrite /mbind/ldist_cost_bind/output. 
  move /mapP => [[r b' Hin]] => //= ->.
  eapply (in_ldist_bind _ r b' m) in Hin as (r'&r''&c'&Hin1&Hin2&Heq).
  exists r'', c'; split; first done. 
  eapply (in_ldist_bind _ r' b' (f (result c'))) in Hin1 as (?&?&?&Hin3&Hin4&?).
  subst. rewrite //= mem_seq1 in Hin3. move /eqP in Hin3. inversion Hin3; subst.
  apply /mapP; eauto.
Qed.

Lemma mspec_mbind {A B: eqType} (f: A → ldist_cost B) m (P: A → Prop) (Q: B → Prop):
  mspec m P →
  (∀ a, P a → mspec (f a) Q) →
  mspec (mbind f m) Q.
Proof.
  intros Hinput Hbody b Hin.
  edestruct (output_mbind_in b m f) as (r&a&Hin'&Hout); eauto.
  eapply Hbody; eauto. apply Hinput; eauto.
  apply /mapP; eauto.
Qed.

Tactic Notation "tbind" open_constr(P) :=
  match goal with
  | [ |- mspec (mbind ?f ?m) ?Q ] =>
    intros; eapply (@mspec_mbind _ _ f m P); auto
  end.

Definition cspec {A: eqType} (m: ldist_cost A) (P: cost A → Prop) :=
  ∀ y, y \in coutput m → P y.

Lemma cspec_mret {A: eqType} (x: A) (P: cost A → Prop):
  P {| work := 0; span := 0; result := x|} → cspec (mret x) P.
Proof.
  intros HP y. rewrite /mret/ldist_cost_ret/mret/dist_ret/output//= mem_seq1.
  move /eqP => -> //.
Qed.

Lemma cspec_dist_ret {A: eqType} x (P: cost A → Prop):
  P x → cspec (dist_ret _ x) P.
Proof.
  intros HP y. rewrite /mret/ldist_cost_ret/mret/dist_ret/output//= mem_seq1.
  move /eqP => -> //.
Qed.

Lemma fun_to_cspec {A: eqType} (m: ldist_cost A) (P: cost A → Prop):
  cspec m P → (∀ x, P ((rvar_of_ldist m) x)).
Proof. 
  rewrite /cspec/coutput => Hspec /= x.
  apply /Hspec/mem_nth. rewrite size_map. inversion x. done.
Qed.

Lemma coutput_mbind_in {A B: eqType} b (m: ldist_cost A) (f: A → ldist_cost B):
  (b \in coutput (x ← m; f x)) →
  ∃ r a, ((r, a) \in outcomes m) ∧ 
         {| work := work b - work a;
            span := span b - span a;
            result := result b|} \in coutput (f (result a)) 
                          ∧ (work b - (work a) + (work a) = work b)%nat
                          ∧ (span b - (span a) + (span a) = span b)%nat.
Proof.
  rewrite /mbind/ldist_cost_bind/output. 
  move /mapP => [[r b' Hin]] => //= ->.
  eapply (in_ldist_bind _ r b' m) in Hin as (r'&r''&a&Hin1&Hin2&Heq).
  eapply (in_ldist_bind _ r' b' (f (result a))) in Hin1 as (?&?&?&Hin3&Hin4&?).
  subst. rewrite //= mem_seq1 in Hin3. move /eqP in Hin3. inversion Hin3; subst.
  exists r'', a; repeat split; first done. 
  - apply /mapP; eauto.
    eexists; eauto => //=; f_equal; auto with *. 
    destruct x1 as [w r s] => //=;  f_equal; nify; omega.
  - rewrite //=; nify; omega.
  - rewrite //=; nify; omega.
Qed.

Lemma cspec_mbind {A B: eqType} (f: A → ldist_cost B) m (P: cost A → Prop) (Q: cost B → Prop):
  cspec m P →
  (∀ a, P a → cspec (f (result a)) 
                    (λ nb, Q {| work := (work a + work nb)%nat;
                                span := (span a + span nb)%nat;
                                result :=  result nb|})) →
  cspec (mbind f m) Q.
Proof.
  intros Hinput Hbody nb Hin.
  edestruct (coutput_mbind_in nb m f) as (r&c&Hin'&Hout&Heq1&Heq2); eauto.
  destruct nb as [nbw nbs nbr]. rewrite //= in Heq1 Heq2. rewrite -Heq1 -Heq2. 
  rewrite addnC. 
  rewrite (addnC _ (span c)). 
  specialize (Hbody c).
  rewrite /cspec//= in Hbody. rewrite //= in Hout. rewrite //=.
  assert (HP: P c).                                                   
  { apply Hinput. rewrite/ coutput. apply /mapP => //=. eauto. }
  eapply (Hbody HP {| work := nbw - work c;
                      span := nbs - span c;
                      result := nbr|}); auto.
Qed.

Lemma cspec_mspec {A: eqType} (m: ldist_cost A) (P: A → Prop):
  mspec m P → cspec m (λ x, P (result x)).
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

Lemma mspec_rpar2 {A B: eqType} (m: ldist_cost A) (m': ldist_cost B) (P: A → Prop) (Q : B → Prop):
  mspec m P →
  mspec m' Q →
  mspec (rpar2 m m') (λ x, P (fst x) ∧ Q (snd x)).
Proof.
  intros Hspec1 Hspec2 b Hin.
  assert (fst b \in output m ∧ snd b \in output m') as (?&?).
  { destruct b as (b1&b2). 
    rewrite /output in Hin. move /mapP in Hin. destruct Hin as [rb Hin Heq]. 
    destruct rb as (r&b). rewrite /rpar2 in Hin. 
    eapply in_ldist_bind in Hin as (?&?&a1&Hin&?&Hmult).
    eapply in_ldist_bind in Hin as (?&?&a2&Hin&?&Hmult').
    rewrite //= in Hin.
    rewrite in_cons in Hin. rewrite in_nil in Hin. move /orP in Hin. 
    destruct Hin as [Hin|]; last done.
    move /eqP in Hin. inversion Hin; subst.
    rewrite //= in Heq. 
    rewrite /output; split => //=; inversion Heq; subst; apply /mapP; eauto.
  }
  split.
  - eapply Hspec1; eauto.
  - eapply Hspec2; eauto.
Qed.