(* Indexed Valuations from Varacca-Winskel *)
From discprob.basic Require Import base sval order monad bigop_ext.
From discprob.basic Require Export classic_proof_irrel.
From discprob.prob Require Export countable.
Require Import Reals Psatz.
Require ClassicalEpsilon.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice bigop.
Global Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.

(* To make the following development work so that bind is a congruence w.r.t
   the ival equivalence relation, I need to assume either:
    (a) We're only going to talk about indexed valuations on types with decidable equality
     or
    (b) Functional choice axiom. 

   Choice a still requires some annoying hacking to use properly, so I think for now
   I will go with b; I will do so by assuming ClassicalEpsilon, which is admittedly
   even stronger.

*)

Record ival X :=
  {
    idx : countType;
    ind: idx → X;
    val: idx → R;
    val_nonneg: ∀ i, val i >= 0;
  }.

Arguments idx {_} _.
Arguments ind {_} _.
Arguments val {_} _.
Arguments val_nonneg {_}.

Definition In_isupport {X: Type} (x: X) (I : ival X) :=
  ∃ i, ind I i = x ∧ val I i > 0.
Definition isupport {X} I := { x : X | ∃ i, ind I i = x ∧ val I i > 0 }. 

Definition eq_ival {X} (I1 I2: ival X) :=
  ∃ h1: (support (val I1) → support (val I2)), ∃ h2: (support (val I2) → support (val I1)),
    (∀ a, h2 (h1 a) = a) ∧
    (∀ b, h1 (h2 b) = b) ∧
    (∀ a, ind I2 (sval (h1 a)) = ind I1 (sval a)) ∧
    (∀ a, val I2 (sval (h1 a)) = val I1 (sval a)).

Definition eq_ival_nondep {X} (I1 I2: ival X) :=
  ∃ h1: (idx I1 → idx I2), ∃ h2: (idx I2 → idx I1),
    (∀ a, val I1 a > 0 → val I2 (h1 a) > 0) ∧
    (∀ b, val I2 b > 0 → val I1 (h2 b) > 0) ∧
    (∀ a, val I1 a > 0 → h2 (h1 a) = a) ∧
    (∀ b, val I2 b > 0 → h1 (h2 b) = b) ∧
    (∀ a, val I1 a > 0 → ind I2 ((h1 a)) = ind I1 (a)) ∧
    (∀ a, val I1 a > 0 → val I2 ((h1 a)) = val I1 (a)).

Definition eq_ival_inj_surj {X} (I1 I2: ival X) :=
  ∃ h1: (support (val I1) → support (val I2)),
    (∀ a b, h1 a = h1 b → a = b) ∧
    (∀ b, ∃ a, h1 a = b) ∧
    (∀ a, ind I2 (sval (h1 a)) = ind I1 (sval a)) ∧
    (∀ a, val I2 (sval (h1 a)) = val I1 (sval a)).

Definition eq_ival_nondep_inj_surj {X} (I1 I2: ival X) :=
  ∃ h1: (idx I1 → idx I2),
    (∀ a, val I1 a > 0 → val I2 (h1 a) > 0) ∧
    (∀ a b, val I1 a > 0 → val I1 b > 0 → h1 a = h1 b → a = b) ∧
    (∀ b, ∃ a, h1 a = b ∧ (val I2 b > 0 → val I1 a > 0)) ∧
    (∀ a, val I1 a > 0 → ind I2 ((h1 a)) = ind I1 (a)) ∧
    (∀ a, val I1 a > 0 → val I2 ((h1 a)) = val I1 (a)).

Definition eq_ival_nondep_inj_surj' {X} (I1 I2: ival X) :=
  ∃ h1: (idx I1 → idx I2),
    (∀ a b, val I1 a > 0 → val I1 b > 0 → h1 a = h1 b → a = b) ∧
    (∀ b, ∃ a, h1 a = b ∧ (val I2 b > 0 → val I1 a > 0)) ∧
    (∀ a, val I1 a > 0 → ind I2 ((h1 a)) = ind I1 (a)) ∧
    (∀ a, val I1 a > 0 → val I2 ((h1 a)) = val I1 (a)).

Lemma eq_ival_nondep_inj_surj'_helper {X} (I1 I2: ival X):
  eq_ival_nondep_inj_surj' I1 I2 →
  eq_ival_nondep_inj_surj I1 I2.
Proof.
  intros (h1&?&?&?&?).
  exists h1; repeat split; eauto. 
  intros. rewrite H2; eauto.
Qed.

Definition oval {X} (I: ival X) (oi: option (idx I)) : R :=
  match oi with
  | None => 0
  | Some i => val I i
  end.

Definition oind {X} (I: ival X) (oi: option (idx I)) : option X :=
  match oi with
  | None => None
  | Some i => Some (ind I i)
  end.

Definition eq_ival_nondep_option {X} (I1 I2: ival X) :=
  ∃ h1: (idx I1 → option (idx I2)), ∃ h2: (idx I2 → option (idx I1)),
    (∀ b, val I2 b > 0 → oval I1 (h2 b) > 0) ∧
    (∀ a, val I1 a > 0 →
          match h1 a with
          | None => False
          | Some b =>
            h2 b = Some a
          end) ∧
    (∀ b, val I2 b > 0 →
          match h2 b with
          | None => False
          | Some a =>
            h1 a = Some b
          end) ∧
    (∀ a, val I1 a > 0 → oind I2 ((h1 a)) = oind I1 (Some a)) ∧
    (∀ a, val I1 a > 0 → oval I2 ((h1 a)) = val I1 (a)).

Definition eq_ival_nondep_option_inj_surj {X} (I1 I2: ival X) :=
  ∃ h1: (idx I1 → option (idx I2)),
    (∀ a, val I1 a > 0 → oval I2 (h1 a) > 0) ∧
    (∀ a b, val I1 a > 0 → val I1 b > 0 → h1 a = h1 b → a = b) ∧
    (∀ b, ∃ a, h1 a = Some b ∧ (val I2 b > 0 → val I1 a > 0)) ∧
    (∀ a, val I1 a > 0 → oind I2 ((h1 a)) = oind I1 (Some a)) ∧
    (∀ a, val I1 a > 0 → oval I2 ((h1 a)) = val I1 (a)).

Lemma eq_ival_nondep_option_suffice {X} (I1 I2: ival X):
  eq_ival_nondep_option I1 I2 → eq_ival I1 I2.
Proof.
  intros (h1&h2&Hs&Hr1&Hr2&Hoi&Hov).
  assert (Hconv: ∀ x y, is_true (Rgt_dec x y) → x > y).
  { intros x y; destruct (Rgt_dec); done. }
  assert (Hconv': ∀ x y, x > y → is_true (Rgt_dec x y)).
  { intros x y; destruct (Rgt_dec); done. }
  eexists. Unshelve.
  all: swap 1 2.
  {
    intros (a&Hpf).
    specialize (Hr1 a).
    specialize (Hov a).
    destruct (h1 a) as [b|].
    - exists b. abstract (rewrite //= in Hov; rewrite Hov => //=; destruct (Rgt_dec); auto).
    - abstract (exfalso; apply Hr1; destruct Rgt_dec; auto).
  }
  rewrite //=.
  eexists. Unshelve.
  all: swap 1 2.
  { 
    intros (a&Hpf).
    specialize (Hr2 a).
    specialize (Hs a).
    destruct (h2 a) as [b|].
    - exists b. abstract (rewrite //= in Hs; repeat destruct Rgt_dec => //=; eauto).
    - exfalso. rewrite //= in Hs. repeat destruct Rgt_dec => //=.
  }
  repeat split; auto.
  - intros (a&Hpf) => //=.
    apply sval_inj_pred => //=.
    generalize (Hr1 a) as Hr1a.
    generalize (Hov a) as Hova.
    destruct (h1 a) as [b| ] => //=.
    * generalize (Hr2 b) as Hr2b.
      generalize (Hs b) as Hss.
      destruct (h2 b) as [a'| ]; rewrite //=.
      ** intros. cut (Some a' = Some a); first by (inversion 1). eapply Hr1a.
         destruct (Rgt_dec); auto.
      ** intros Hfalse ??. exfalso. rewrite //=. destruct Rgt_dec.
         cut (0 > 0); first by nra. apply Hfalse. 
         rewrite Hova; auto.
         auto.
    * intros. exfalso; apply Hr1a. destruct Rgt_dec; auto.
  - intros (b&Hpf) => //=.
    apply sval_inj_pred => //=.
    generalize (Hr2 b) as Hr2b.
    generalize (Hs b) as Hovb.
    destruct (h2 b) as [a| ]; rewrite //=.
    * generalize (Hr1 a) as Hr1a.
      generalize (Hov a) as Hova.
      destruct (h1 a) as [b'| ] => //=.
      ** intros. cut (Some b' = Some b); first by (inversion 1). eapply Hr2b.
         destruct (Rgt_dec); auto.
      ** intros Hfalse ??. exfalso. rewrite //=. destruct Rgt_dec => //=.
         
         apply Hr1a. apply Hovb. done.
    * intros. exfalso; apply Hr2b. destruct Rgt_dec; auto. 
  - intros (a&Hpf).
    generalize (Hr1 a) as Hr1a.
    generalize (Hov a) as Hova.
    generalize (Hoi a) as Hoia.
    destruct (h1 a) as [b |] => //=.
    * intros. destruct Rgt_dec as [Hgt|Hngt] => //=.
      specialize (Hoia Hgt). inversion Hoia; done.
    * intros. exfalso. apply Hr1a; auto. 
  - intros (a&Hpf).
    generalize (Hr1 a) as Hr1a.
    generalize (Hov a) as Hova.
    generalize (Hoi a) as Hoia.
    destruct (h1 a) as [b |] => //=.
    * intros. destruct Rgt_dec as [Hgt|Hngt] => //=.
      specialize (Hova Hgt). inversion Hova; done.
    * intros. exfalso. apply Hr1a; auto. 
Qed.

Lemma eq_ival_inj_surj_suffice {X} (I1 I2: ival X):
  eq_ival_inj_surj I1 I2 → eq_ival I1 I2.
Proof.
  intros (h1&Hinj&Hsurj&Hind&Hval).
  exists h1.
  eexists.
  Unshelve. all: swap 1 2.
  { intros b. specialize (Hsurj b).
    apply ClassicalEpsilon.constructive_indefinite_description in Hsurj as (a&Heq).
    exact a.
  }
  repeat split => //=.
  - intros a.  destruct ClassicalEpsilon.constructive_indefinite_description as (a'&heq).
    eapply Hinj; eauto.
  - intros b. destruct ClassicalEpsilon.constructive_indefinite_description as (a'&Heq).
    done.
Qed.


Lemma eq_ival_nondep_option_symm {X} (I1 I2: ival X) :
  eq_ival_nondep_option I1 I2 →
  ∃ h1: (idx I1 → option (idx I2)), ∃ h2: (idx I2 → option (idx I1)),
    (∀ b, val I2 b > 0 → oval I1 (h2 b) > 0) ∧
    (∀ b, val I1 b > 0 → oval I2 (h1 b) > 0) ∧
    (∀ a, val I1 a > 0 →
          match h1 a with
          | None => False
          | Some b =>
            h2 b = Some a
          end) ∧
    (∀ b, val I2 b > 0 →
          match h2 b with
          | None => False
          | Some a =>
            h1 a = Some b
          end) ∧
    (∀ a, val I1 a > 0 → oind I2 ((h1 a)) = oind I1 (Some a)) ∧
    (∀ a, val I1 a > 0 → oval I2 ((h1 a)) = val I1 (a)) ∧
    (∀ b, val I2 b > 0 → oind I1 ((h2 b)) = oind I2 (Some b)) ∧
    (∀ b, val I2 b > 0 → oval I1 ((h2 b)) = val I2 (b)).
Proof.
  intros (h1&h2&Hdom&Hlr&Hrl&Hind&Hval).
  exists h1, h2. repeat split; auto.
  - intros a Hgt. specialize (Hval a). rewrite Hval => //=.
  - intros b Hgt. specialize (Hrl b Hgt).
    specialize (Hdom b Hgt).
    destruct (h2 b) as [a|].
    * rewrite -Hrl -Hind //=.
    * rewrite //=.
  - intros b Hgt. specialize (Hrl b Hgt).
    specialize (Hdom b Hgt).
    destruct (h2 b) as [a|].
    * replace (val I2 b) with (oval I2 (Some b)); last by done.
      rewrite -Hrl //= -Hval //=.
    * rewrite //=.
Qed.


Lemma eq_ival_nondep_option_necc {X} (I1 I2: ival X):
  eq_ival I1 I2 → eq_ival_nondep_option I1 I2.
Proof.
  intros (h1&h2&Hlr&Hrl&Hi&Hv).
  assert (Hconv': ∀ x y, x > y → is_true (Rgt_dec x y)).
  { intros x y; destruct (Rgt_dec); done. }
  exists (λ x, match (Rgt_dec (val I1 x) 0) with
               | left Hpf => Some (sval (h1 (exist _ x (Hconv' _ _ Hpf))))
               | right _ => None
               end).
  exists (λ x, match (Rgt_dec (val I2 x) 0) with
               | left Hpf => Some (sval (h2 (exist _ x (Hconv' _ _ Hpf))))
               | right _ => None
               end).
  repeat split => //=.
  - intros b. destruct Rgt_dec => //=. destruct (h2 _) => //= .
    destruct Rgt_dec => //=.
  - intros a. destruct Rgt_dec => //=. destruct Rgt_dec as [?|n] => //=; intros Hgt.
    *  f_equal.
       transitivity (sval (exist (λ x, Rgt_dec (val I1 x) 0) a (Hconv' _ _ Hgt)));
                  last by done.
       f_equal. etransitivity; last apply Hlr.
       f_equal => //=. apply sval_inj_pred => //=. do 2 f_equal.
       apply sval_inj_pred. done.
    * intros. exfalso. apply n. rewrite Hv => //=.
  - intros b. destruct Rgt_dec => //=. destruct Rgt_dec as [?|n] => //=; intros Hgt.
    *  f_equal.
       transitivity (sval (exist (λ x, Rgt_dec (val I2 x) 0) b (Hconv' _ _ Hgt)));
                  last by done.
       f_equal. etransitivity; last apply Hrl.
       f_equal => //=. apply sval_inj_pred => //=. do 2 f_equal.
       apply sval_inj_pred. done.
    * intros. exfalso. apply n. rewrite -Hv Hrl => //=.
  - intros a Hgt; destruct Rgt_dec => //=. rewrite Hi; done.
  - intros a Hgt; destruct Rgt_dec => //=. rewrite Hv; done.
Qed.

Lemma eq_ival_nondep_option_inj_surj_suffice {X} (I1 I2: ival X):
  eq_ival_nondep_option_inj_surj I1 I2 → eq_ival I1 I2.
Proof.
  intros (h1&Hrange&Hinj&Hsurj&?&?).
  apply eq_ival_nondep_option_suffice.
  exists h1.
  eexists.
  Unshelve. all: swap 1 2.
  { intros b. specialize (Hsurj b).
    apply ClassicalEpsilon.constructive_indefinite_description in Hsurj as (a&Heq).
    exact (Some a).
  }
  repeat split => //=.
  - intros b ?. destruct ClassicalEpsilon.constructive_indefinite_description as (a'&Heq&Hgt).
    eauto.
  - intros a ?.
    specialize (Hrange a). rewrite //= in Hrange.
    case_eq (h1 a).
    * intros s Hh1.
      destruct ClassicalEpsilon.constructive_indefinite_description as (a'&Heq&Hgt).
      f_equal. eapply Hinj; eauto. 
      ** eapply Hgt. rewrite Hh1 //= in Hrange. apply Hrange; auto.  
      ** congruence.
    * intros Hneq. rewrite Hneq in Hrange. rewrite //= in Hrange.
      nra.
  - intros b ?. destruct ClassicalEpsilon.constructive_indefinite_description as (a'&Heq&Hgt).
    eauto.
Qed.

Lemma eq_ival_nondep_suffice {X} (I1 I2: ival X):
  eq_ival_nondep I1 I2 → eq_ival I1 I2.
Proof.
  intros (h1&h2&Hr1&Hr2&Hs1&Hs2&Hind&Hval).
  assert (Hconv: ∀ x y, is_true (Rgt_dec x y) → x > y).
  { intros x y; destruct (Rgt_dec); done. }
  assert (Hconv': ∀ x y, x > y → is_true (Rgt_dec x y)).
  { intros x y; destruct (Rgt_dec); done. }
  rewrite /eq_ival. 
  exists (λ x, match x with exist a Hpf => exist _ (h1 a) (Hconv' _ _ (Hr1 a (Hconv _ _ Hpf))) end).
  exists (λ x, match x with exist a Hpf => exist _ (h2 a) (Hconv' _ _ (Hr2 a (Hconv _ _ Hpf))) end).
  repeat split; auto.
  - destruct a as (x&i) => //=.
    apply sval_inj_pred => //=. auto.
  - destruct b as (x&i) => //=.
    apply sval_inj_pred => //=. auto.
  - intros (x&i) => //=. apply Hind. auto.
  - intros (x&i) => //=. apply Hval. auto.
Qed.

Lemma eq_ival_nondep_inj_surj_suffice {X} (I1 I2: ival X):
  eq_ival_nondep_inj_surj I1 I2 → eq_ival I1 I2.
Proof.
  intros (h1&Hrange&Hinj&Hsurj&?&?).
  apply eq_ival_nondep_suffice.
  exists h1.
  eexists.
  Unshelve. all: swap 1 2.
  { intros b. specialize (Hsurj b).
    apply ClassicalEpsilon.constructive_indefinite_description in Hsurj as (a&Heq).
    exact a.
  }
  repeat split => //=.
  - intros b ?. destruct ClassicalEpsilon.constructive_indefinite_description as (a'&Heq&Hgt).
    eauto.
  - intros a ?. destruct ClassicalEpsilon.constructive_indefinite_description as (a'&Heq&Hgt).
    eauto.
  - intros b ?. destruct ClassicalEpsilon.constructive_indefinite_description as (a'&Heq&Hgt).
    eauto.
Qed.

Lemma eq_ival_refl {X} (I: ival X): eq_ival I I.
Proof.
  exists (λ x, x).
  exists (λ x, x).
  repeat split; try done.
Qed.

Lemma eq_ival_quasi_refl {X} (it: countType) (i: it → X) v pf1 pf2:
  eq_ival {| idx := it; ind := i; val := v; val_nonneg := pf1 |}
          {| idx := it; ind := i; val := v; val_nonneg := pf2 |}.
Proof.
  exists (λ x, x).
  exists (λ x, x).
  repeat split; try done.
Qed.

Lemma eq_ival_sym {X} (I1 I2: ival X): eq_ival I1 I2 → eq_ival I2 I1.
Proof.
  intros (h1&h2&H12&H21&Hind&Hval).
  exists h2, h1. repeat split; try done.
  - intros (x&i) => //=. rewrite -Hind H21 //=. 
  - intros (x&i) => //=. rewrite -Hval H21 //=. 
Qed.


Lemma eq_ival_trans {X} (I1 I2 I3: ival X): eq_ival I1 I2 → eq_ival I2 I3 → eq_ival I1 I3.
Proof.
  intros (h1&h2&Hs1&Hs2&Hind12&Hval12).
  intros (h2'&h3&Hs2'&Hs3&Hind23&Hval23).
  exists (λ x, h2' (h1 x)).
  exists (λ x, h2 (h3 x)).
  repeat split; auto.
  * intros. rewrite Hs2'; auto.
  * intros. rewrite Hs2; auto.
  * intros. rewrite Hind23 Hind12 //. 
  * intros. rewrite Hval23 Hval12 //. 
Qed.

Definition iplus {X} (I1 I2: ival X) : ival X :=
  {| idx := [countType of idx I1 + idx I2];
     ind := (λ x, match x with | inl a => ind I1 a | inr b => ind I2 b end);
     val := (λ x, match x with | inl a => val I1 a | inr b => val I2 b end);
     val_nonneg := (λ x, match x with | inl a => val_nonneg I1 a | inr b => val_nonneg I2 b end);
  |}.

Definition iscale {X} (p: R) (I: ival X) : ival X.
  refine 
  {| idx := idx I;
     ind := ind I;
     val := (λ x, Rabs p * (val I x));
     val_nonneg := _
  |}.
  abstract (intros i; specialize (val_nonneg I i); specialize (Rabs_pos p); nra).
Defined.

(* TODO: move *)
(* TODO: should we just use { x :unit | false} as empty ? *)
Lemma eqeP : Equality.axiom (λ x y : Empty_set, true).
Proof. intros []. Qed.

Canonical empty_eqMixin := EqMixin eqeP.
Canonical empty_eqType := Eval hnf in EqType Empty_set empty_eqMixin.

Fact empty_choiceMixin: choiceMixin Empty_set.
Proof.
  exists (λ P n, None).
  - intros ?? [].
  - intros ? [[]].
  - intros ?? ? x. done. 
Qed.
Canonical empty_choiceType := Eval hnf in ChoiceType Empty_set empty_choiceMixin.

Definition empty_pickle (x: Empty_set) := Empty_set_rect (λ x, nat) x.
Definition empty_unpickle (n: nat) : option Empty_set := None.
Lemma empty_pickleK : pcancel empty_pickle empty_unpickle.
Proof. intros []. Qed.

Definition empty_countMixin := CountMixin (empty_pickleK).
Canonical empty_countType := Eval hnf in CountType Empty_set empty_countMixin.

Lemma empty_enumP : @Finite.axiom [eqType of Empty_set] [::].
Proof. intros []. Qed.
Definition empty_finMixin := Eval hnf in FinMixin empty_enumP.
Canonical empty_finType := Eval hnf in FinType Empty_set empty_finMixin.

Definition zero_ival {X: Type} :=
  {| idx := [countType of Empty_set];
     ind := λ x, Empty_set_rect (λ x, X) x;
     val := Empty_set_rect (λ x, R);
     val_nonneg := Empty_set_rect (λ x, Empty_set_rec (λ x, R) x >= 0)
  |}. 

Section ival_props.
Variable (X: Type).
Implicit Types I: ival X.

Lemma Rabs_val I i: Rabs (val I i) = val I i.
Proof.
  rewrite Rabs_right //=. apply val_nonneg; eauto.
Qed.
  
Definition support_plus1 {I1 I2}: support (val (iplus I1 I2)) → (support (val I1) + support (val I2)).
Proof.
  rewrite //=. intros ([a|b]&Hpf).
  - exact (inl (exist _ a Hpf)).
  - exact (inr (exist _ b Hpf)).
Defined.

Definition support_plus2 {I1 I2}: (support (val I1) + support (val I2)) → support (val (iplus I1 I2)).
Proof.
  rewrite //=. intros [(a&Hpf)|(b&Hpf)].
  - exists (inl a). done.
  - exists (inr b). done.
Defined.

Lemma iplus_eq_ival I1 I1' I2 I2':
  eq_ival I1 I1' →
  eq_ival I2 I2' →
  eq_ival (iplus I1 I2) (iplus I1' I2').
Proof.
  intros (h1&h1'&Hs1&Hs1'&Hind11'&Hval11').
  intros (h2&h2'&Hs2&Hs2'&Hind22'&Hval22').
  exists (λ x, support_plus2 (match (support_plus1 x) with
                              | inl x => inl (h1 x)
                              | inr x => inr (h2 x)
                              end)).
  exists (λ x, support_plus2 (match (support_plus1 x) with
                              | inl x => inl (h1' x)
                              | inr x => inr (h2' x)
                              end)).
  repeat split; intros ([a|b]&Hpf) => //=; intros; rewrite ?Hs1 ?Hs1' ?Hs2 ?Hs2' //=; auto.
  * specialize (Hs1 (exist _ a Hpf)).
    destruct (h1 _) => //=.
    destruct (h1' _) => //=.
    inversion Hs1; subst; f_equal. apply eqtype.bool_irrelevance.
  * specialize (Hs2 (exist _ b Hpf)).
    destruct (h2 _) => //=.
    destruct (h2' _) => //=.
    inversion Hs2; subst; f_equal. apply eqtype.bool_irrelevance.
  * specialize (Hs1' (exist _ a Hpf)).
    destruct (h1' _) => //=.
    destruct (h1 _) => //=.
    inversion Hs1'; subst; f_equal. apply eqtype.bool_irrelevance.
  * specialize (Hs2' (exist _ b Hpf)).
    destruct (h2' _) => //=.
    destruct (h2 _) => //=.
    inversion Hs2'; subst; f_equal. apply eqtype.bool_irrelevance.
  * specialize (Hind11' (exist _ a Hpf)). specialize (Hs1 (exist _ a Hpf)).
    destruct (h1 _) => //=.
  * specialize (Hind22' (exist _ b Hpf)). specialize (Hs2 (exist _ b Hpf)).
    destruct (h2 _) => //=.
  * specialize (Hval11' (exist _ a Hpf)). specialize (Hs1 (exist _ a Hpf)).
    destruct (h1 _) => //=.
  * specialize (Hval22' (exist _ b Hpf)). specialize (Hs2 (exist _ b Hpf)).
    destruct (h2 _) => //=.
Qed.

Definition support_scale1 (p: R) (Hgt: p <> 0) {I}: support (val (iscale p I)) → (support (val I)).
Proof.
  rewrite //=.
  intros (x&Hpf). exists x.
  abstract (specialize (Rabs_pos_lt p Hgt); intros;
            destruct (Rgt_dec (val I x) 0);
            destruct Rgt_dec; auto; nra).
Defined.

Definition support_scale2 (p: R) (Hgt: p <> 0) {I}: support (val I) → (support (val (iscale p I))).
Proof.
  rewrite //=.
  intros (x&Hpf). exists x.
  abstract (specialize (Rabs_pos_lt p Hgt); intros;
            destruct (Rgt_dec (val I x) 0);
            destruct Rgt_dec; auto; nra).
Defined.
          
Lemma iscale_0_l I:
  eq_ival (iscale 0 I) zero_ival.
Proof.
  assert (h: support (val (iscale 0 I)) → support (val (@zero_ival X))).
  { rewrite //=. intros (x&Hpf). rewrite //= in Hpf. exfalso.
    rewrite Rabs_R0 in Hpf.
    destruct (Rgt_dec _ _); auto; nra. }
  exists h.
  exists (λ (x: support (val (zero_ival))), Empty_set_rect (λ x, _) (proj1_sig x)).
  repeat split.
  - rewrite //=; intros (a&Hpf). exfalso. rewrite Rabs_R0 in Hpf.
    destruct Rgt_dec; auto; try nra.
  - intros ([]&Hpf).
  - rewrite //=; intros (a&Hpf). exfalso. rewrite Rabs_R0 in Hpf.
    destruct Rgt_dec; auto; try nra.
  - rewrite //=; intros (a&Hpf). exfalso. rewrite Rabs_R0 in Hpf.
    destruct Rgt_dec; auto; try nra.
Qed.
  
Lemma iscale_eq_ival p I1 I1':
  eq_ival I1 I1' →
  eq_ival (iscale p I1) (iscale p I1').
Proof.
  intros (h1&h1'&Hs1&Hs1'&Hind11'&Hval11').
  destruct (Req_dec p R0) as [Heq0|Hgt0]; last first.
  * exists (λ x, support_scale2 p Hgt0 (h1 (support_scale1 p Hgt0 x))).
    exists (λ x, support_scale2 p Hgt0 (h1' (support_scale1 p Hgt0 x))).
    repeat split; auto.
    ** intros a. rewrite //=. 
       specialize (Hs1 (support_scale1 p Hgt0 a)).
       destruct (h1 _) as (x&i) => //=.
       erewrite <-(eqtype.bool_irrelevance i _).
       rewrite Hs1 => //=.
       destruct a as (a&Hpf) => //=.
       f_equal; apply eqtype.bool_irrelevance.
    ** intros b. rewrite //=. 
       specialize (Hs1' (support_scale1 p Hgt0 b)).
       destruct (h1' _) as (x&i) => //=.
       erewrite <-(eqtype.bool_irrelevance i _).
       rewrite Hs1' => //=.
       destruct b as (b&Hpf) => //=.
       f_equal; apply eqtype.bool_irrelevance.
    ** intros a. rewrite //=. specialize (Hind11' (support_scale1 p Hgt0 a)).
       destruct (h1 _) as (x&i) => //=.
       rewrite //= in Hind11'.
       etransitivity; first eauto. f_equal.
       destruct a => //=.
    ** intros a. rewrite //=. specialize (Hval11' (support_scale1 p Hgt0 a)).
       destruct (h1 _) as (x&i) => //=.
       rewrite //= in Hind11'.
       etransitivity; first eauto. f_equal.
       destruct a => //=.
  * subst; eapply (eq_ival_trans _ (zero_ival)).
    **  apply iscale_0_l.
    **  apply eq_ival_sym. apply iscale_0_l.
Qed.

Global Instance eq_ival_Transitivite {X}: Transitive (@eq_ival X).
Proof. intros ???. apply eq_ival_trans. Qed.
Global Instance eq_ival_Reflexive {X}: Reflexive (@eq_ival X).
Proof. intros ?. apply eq_ival_refl. Qed.
Global Instance eq_ival_Symmetry {X}: Symmetric (@eq_ival X).
Proof. intros ??. apply eq_ival_sym. Qed.
Global Instance eq_ival_Equivalence {X}: Equivalence (@eq_ival X).
Proof. split; apply _. Qed. 

Global Instance iplus_proper : Proper (@eq_ival X ==> @eq_ival X ==> @eq_ival X) (@iplus X).
Proof. intros ?? ? ?? ?. apply @iplus_eq_ival; auto. Qed.

Global Instance iscale_proper : Proper (eq ==> @eq_ival X ==> @eq_ival X) (@iscale X).
Proof. intros ?? ? ?? ?; subst. apply @iscale_eq_ival; auto. Qed.

Lemma iplus_comm I1 I2: eq_ival (iplus I1 I2) (iplus I2 I1).
Proof.
  apply eq_ival_nondep_suffice.
  exists (λ x, match x with | inl x => inr x | inr x => inl x end).
  exists (λ x, match x with | inl x => inr x | inr x => inl x end).
  repeat split; auto; intros [?|?]; rewrite //=.
Qed.

Lemma iplus_assoc I1 I2 I3: eq_ival (iplus I1 (iplus I2 I3)) (iplus (iplus I1 I2) I3).
Proof.
  apply eq_ival_nondep_suffice.
  exists (λ x, match x with | inl x => inl (inl x) | inr (inl x) => inl (inr x) | inr (inr x) =>  inr x end).
  exists (λ x, match x with | inl (inl x) => inl x | inl (inr x) => inr (inl x) | inr x =>  inr (inr x) end).
  repeat split; auto;
    try (intros [?|[?|?]]; done);
    try (intros [[?|?]|?]; done).
Qed.

Lemma iplus_0 I: eq_ival (iplus I zero_ival) I.
Proof.
  apply eq_ival_nondep_suffice.
  exists (λ x : idx (iplus I zero_ival),
                match x with | inl x => x | inr x => Empty_set_rect (λ x, idx I) x end).
  exists inl.
  repeat split; auto.
  - intros [?|[]]. rewrite //=.
  - intros [?|[]]. rewrite //=.
  - intros [?|[]]. rewrite //=.
  - intros [?|[]]. rewrite //=.
Qed.

Ltac abs_simpl :=
  match goal with
  | [ H: context [ Rabs ?p ] |- _ ]  =>
    rewrite (Rabs_right p) in H; last by nra
  | [ |- context [ Rabs ?p ] ] =>
    rewrite (Rabs_right p); last by nra
  end.

Lemma iscale_1 I: eq_ival (iscale 1 I) I.
Proof.
  apply eq_ival_nondep_suffice.
  exists (λ x, x).
  exists (λ x, x).
  repeat split => //=; auto; intros;
  repeat abs_simpl; nra. 
Qed.

Lemma iscale_distrib p I1 I2:
  eq_ival (iscale p (iplus I1 I2)) (iplus (iscale p I1) (iscale p I2)).
Proof.
  destruct (Req_dec p 0) as [Heq0|Hgt0].
  { subst. etransitivity.
    * apply iscale_0_l.
    * setoid_rewrite iscale_0_l. setoid_rewrite iplus_0. reflexivity.
  }
  apply eq_ival_nondep_suffice.
  exists (λ x, x).
  exists (λ x, x).
  repeat split => //=; auto; intros [?|?]; nra.
Qed.

(*
Lemma iscale_distrib_le p q I:
  p >= 0 →
  q >= 0 →
  le_ival (iscale (p + q) I) (iplus (iscale p I) (iscale q I)).
Proof.
  intros [Hgtp0|Heqp0]; last first.
  intros [Hgtq0|Heqq0]; last first.
  unshelve (eexists).
  { intros ([i|i]&Hgt);
      exists i; abstract (rewrite //= ?Rabs_right in Hgt *; try nra;
                    repeat destruct Rgt_dec => //=; exfalso; nra).
  }
  repeat split.
  - intros (i&Hgt). 
    
  rewrite //=.
    assert (Rabs (p + q) > Rabs p).
    { rewrite Rabs_right. SearchAbout Rabs Rplus. rewrite  
    nra.



  destruct (Req_dec p 0) as [Heqp0|Hgtp0].
  destruct (Req_dec q 0) as [Heqq0|Hgtq0].

  unshelve (eexists).
  { intros ([i|i]&Hgt). exists i => //=.
    rewrite //= in Hgt. repeat destruct Rgt_dec => //=. exfalso.
    assert (Rabs (p + q) > Rabs p).
    { rewrite  
    nra.
    
  etransitivity.
    * apply iscale_0_l.
    * setoid_rewrite iscale_0_l. setoid_rewrite iplus_0. reflexivity.
  }
  apply eq_ival_nondep_suffice.
  exists (λ x, x).
  exists (λ x, x).
  repeat split => //=; auto; intros [?|?]; nra.
Qed.
*)

Lemma iscale_0_r p:
  eq_ival (iscale p (@zero_ival X)) (zero_ival).
Proof.
  apply eq_ival_nondep_suffice.
  exists (λ x, x).
  exists (λ x, x).
  repeat split; auto => //=.
Qed.

Lemma iscale_assoc p q I:
  eq_ival (iscale p (iscale q I)) (iscale (p * q) I). 
Proof.
  apply eq_ival_nondep_suffice.
  exists (λ x, x).
  exists (λ x, x).
  repeat split => //=; auto; rewrite Rabs_mult; intros; nra.
Qed.

End ival_props.

Global Instance ival_ret: MRet ival.
refine(λ A x, {| idx := [finType of unit]; ind := (λ _, x); val := (λ _, 1) |}).
{ abstract (intros; nra). }
Defined.

Global Instance ival_bind: MBind ival.
refine(
  λ A B f I,
  {| idx := [countType of { i: idx I & idx (f (ind I i)) }];
     ind := (λ ip, ind (f (ind I (projT1 ip))) (projT2 ip));
     val := (λ ip, val I (projT1 ip)
                   * val (f (ind I (projT1 ip))) (projT2 ip));
     val_nonneg := _
  |}).
{ abstract (intros (i1&i2); specialize (val_nonneg I i1);
            specialize (val_nonneg (f (ind I i1)) i2) => //=; nra). }
Defined.

Global Instance ival_join: MJoin ival :=
  λ A I,
  mbind (λ x, x) I.

Lemma ival_left_id {A B: Type} (x: A) (f: A → ival B):
  eq_ival (mbind f (mret x)) (f x).
Proof.
  rewrite /ival_bind//=.
  apply eq_ival_nondep_suffice.
  exists (λ x, projT2 x).
  exists (λ x, existT tt x).
  repeat split; rewrite //=.
  - intros (?&?) => //=. nra.
  - intros; nra.
  - intros ([]&?) => //=.
  - intros (?&?) => //=. nra.
Qed.

Lemma ival_right_id {A: Type} (m: ival A):
  eq_ival (mbind mret m) m.
Proof.
  apply eq_ival_nondep_suffice.
  exists (λ x, projT1 x).
  exists (λ x, existT x tt).
  repeat split; rewrite //=.
  - intros (?&?) => //=. nra.
  - intros; nra.
  - intros (?&[]) => //=.
  - intros (?&?) => //=. nra.
Qed.

Lemma ival_assoc_wit1 {A B C} (m: ival A) (f: A → ival B) (g: B → ival C) : idx (mbind g (mbind f m)) → idx (mbind (λ x, mbind g (f x)) m).
Proof.
  rewrite //=.
  intros [[i1 i2] i3].
  exact (existT i1 (existT i2 i3)).
Defined.


Lemma ival_assoc_wit2 {A B C} (m: ival A) (f: A → ival B) (g: B → ival C) : idx (mbind (λ x, mbind g (f x)) m) → idx (mbind g (mbind f m)).
Proof.
  rewrite //=.
  intros [i1 [i2 i3]].
  exact (existT (existT i1 i2) i3).
Defined.

Lemma ival_assoc {A B C} (m: ival A) (f: A → ival B) (g: B → ival C) :
  eq_ival (mbind g (mbind f m)) (mbind (λ x, mbind g (f x)) m).
Proof.
  apply eq_ival_nondep_suffice => //=.
  exists (ival_assoc_wit1 m f g).
  exists (ival_assoc_wit2 m f g).
  repeat split => //=.
  - intros [[? ?] ?] => //=.
    nra.
  - intros [? [? ?]] => //=.
    nra.
  - intros [[? ?] ?] => //=.
  - intros [? [? ?]] => //=.
  - intros [[? ?] ?] => //=.
  - intros [[? ?] ?] => //=.
    nra.
Qed.

Lemma val_bind_gt {X Y} (I1: ival X) (I2: ival Y):
  ∀ i1 i2, val I1 i1 * val I2 i2 > 0 → val I1 i1 > 0 ∧ val I2 i2 > 0.
Proof.
  intros. specialize (val_nonneg I1 i1).  specialize (val_nonneg I2 i2). nra.
Qed.

(* In some sense this is more natural but we either have to make P decidable or do some finessing *)
(*
Definition ival_equip {A} (m: ival A) (P: A → Prop) :
  ival {x : A | P x}.
Proof.
  refine {| idx := [finType of {x: idx m | P (ind m x)}]; val := (λ x, val m (sval x));
            val_nonneg := _;
            ind := _ |}.
  - intros (im&Hgt).
    exists (ind m im).
    apply HP.  exists im; split; auto. destruct Rgt_dec => //=.
  - intros. apply val_nonneg.
Defined.
*)

Definition ival_equip {A} (m: ival A) (P: A → Prop) :
  (∀ x, (∃ i, ind m i = x ∧ val m i > 0) → P x) →
  ival {x : A | P x}.
Proof.
  intros HP.
  refine {| idx := [countType of {x: idx m | Rgt_dec (val m x) 0}]; val := (λ x, val m (sval x));
            val_nonneg := _;
            ind := _ |}.
  - intros (im&Hgt).
    exists (ind m im).
    apply HP.  exists im; split; auto. destruct Rgt_dec => //=.
  - intros. apply val_nonneg.
Defined.

Definition eq_ival_equip {A} (m1 m2: ival A) P Hpf1 Hpf2:
  eq_ival m1 m2 → eq_ival (ival_equip m1 P Hpf1) (ival_equip m2 P Hpf2).
Proof.
  intros (h1&h2&Hh12&Hh21&Hind&Hval). 
  eexists.
  Unshelve. all: swap 1 2.
  { intros (im1&_).
    set (im2 := (h1 im1)).
    exists im2. {  destruct im2; auto. }
  }
  eexists.
  Unshelve. all: swap 1 2.
  { intros (im2&_).
    set (im1 := (h2 im2)).
    exists im1. {  destruct im1; auto. }
  }
  repeat split => //=.
  - intros ((?&?)&?) => //=. simpl in *.
    apply sval_inj_pred => //=.
  - intros ((?&?)&?) => //=. simpl in *.
    apply sval_inj_pred => //=.
  - intros (im1&?) => //=. simpl in *.
    specialize (Hind im1). destruct im1 as (im1&Hgt).
    destruct (h1 (exist _ im1 Hgt)) as (?&?) => //=.
    rewrite //=.
    apply subset_eq_compat. eapply Hind.
  - intros ((?&?)&?) => //=. eapply Hval.
Qed.

(*
Lemma ival_bind_P {A B} (m: ival A) (f: A → ival B) (P: A → Prop) f':
  ∀ Hpf: ∀ x, (∃ i, ind m i = x ∧ val m i > 0) → P x,
  (∀ x, f (sval x) = f' x) → 
  eq_ival (mbind f m) (mbind f' (ival_equip m _ Hpf)).
Proof. 
  intros Hpf Heq.
  eexists.
  Unshelve. all: swap 1 2.
  { intros ((im&ifm)&Hgt).
    assert (Hgt': Rgt_dec (val m im) 0).
    {
      abstract (destruct Rgt_dec as [r|n] => //=; destruct Rgt_dec => //=;
                simpl in r; specialize (val_nonneg (f (ind m im)) ifm); nra).
    }
    unshelve (eexists).
    { exists (exist _ im Hgt').
      rewrite -Heq //=.
    }
    abstract (
    rewrite //=; rewrite //= in Hgt;
    destruct Rgt_dec as [?|?] => //=;
    destruct Rgt_dec as [?|?] => //=;
    destruct Rgt_dec as [?|n] => //=;
    exfalso; apply n;
    eapply Rge_gt_trans; [ | by eauto];
    (right; f_equal; destruct (Heq _) => //=)).
  }
  eexists.
  Unshelve. all: swap 1 2.
  { 
    intros (((im&Hgt')&ifm)&Hgt). simpl in *.
    unshelve (eexists).
    { exists im. clear Hgt. rewrite -Heq in ifm. rewrite //=. }
    rewrite //=.
    abstract (
        rewrite //=; rewrite //= in Hgt;
    destruct Rgt_dec as [?|?] => //=;
    destruct Rgt_dec as [?|?] => //=;
    destruct Rgt_dec as [?|n] => //=;
    exfalso; apply n;
    eapply Rge_gt_trans; [ | by eauto];
    (right; f_equal; destruct (Heq _) => //=)).
  }
  repeat split => //=.
  - intros ((?&?)&?). apply sval_inj_pred => //=. f_equal.
    destruct (Heq _) => //=.
  - intros (((x&?)&s)&i0). simpl in *.
    apply sval_inj_pred => //=.
    destruct (Heq _).
    f_equal.
    generalize i0.
    clear 
    rewrite Heq in s.
    assert (i = ival_bind_P_subproof A B m f x s i0) as ->.
    { apply classical_proof_irrelevance. } 
    done.
  - intros ((?&?)&?). done.
  - intros ((?&?)&?). done.
Qed.
*)

  
Lemma ival_bind_P {A B} (m: ival A) (f: A → ival B) (P: A → Prop):
  ∀ Hpf: ∀ x, (∃ i, ind m i = x ∧ val m i > 0) → P x,
  eq_ival (mbind f m) (mbind (λ x : {a: A | P a}, f (sval x)) (ival_equip m _ Hpf)).
Proof. 
  eexists.
  Unshelve. all: swap 1 2.
  { intros ((im&ifm)&Hgt).
    assert (Hgt': Rgt_dec (val m im) 0).
    {
      abstract (destruct Rgt_dec as [r|n] => //=; destruct Rgt_dec => //=;
                simpl in r; specialize (val_nonneg (f (ind m im)) ifm); nra).
    }
    exists (existT (exist _ im Hgt') ifm).
    rewrite //=.
  }
  eexists.
  Unshelve. all: swap 1 2.
  { 
    intros (((im&Hgt')&ifm)&Hgt). simpl in *.
    exists (existT im ifm).
    rewrite //=.
  }
  repeat split => //=.
  - intros ((?&?)&?). done.
  - intros (((x&?)&s)&i0). simpl in *.
    apply sval_inj_pred => //=.
    assert (i = ival_bind_P_subproof A B m f x s i0) as ->.
    { apply classical_proof_irrelevance. } 
    done.
  - intros ((?&?)&?). done.
  - intros ((?&?)&?). done.
Qed.

Lemma ival_bind_congr {A B} (m1 m2: ival A) (f1 f2: A → ival B) :
  eq_ival m1 m2 →
  (∀ a, eq_ival (f1 a) (f2 a)) →
  eq_ival (mbind f1 m1) (mbind f2 m2).
Proof. 
  intros Hequiv.
  apply eq_ival_nondep_option_necc, eq_ival_nondep_option_symm in Hequiv
    as (h1&h2&?&?&Hlr&Hrl&Hind1&Hval1&Hind2&Hval2).
  intros Hequivf.
  assert (∃ h1 : forall a, idx (f1 a) → option (idx (f2 a)),
          ∃ h2 : forall a, idx (f2 a) → option (idx (f1 a)),
            (∀ a0 b, val (f2 a0) b > 0 → oval (f1 a0) (h2 a0 b) > 0) ∧
            (∀ a0 b, val (f1 a0) b > 0 → oval (f2 a0) (h1 a0 b) > 0) ∧
            (∀ a0 a, val (f1 a0) a > 0 →
                  match h1 a0 a with
                  | None => False
                  | Some b =>
                    h2 a0 b = Some a
                  end) ∧
            (∀ a0 b, val (f2 a0) b > 0 →
                  match h2 a0 b with
                  | None => False
                  | Some a =>
                    h1 a0 a = Some b
                  end) ∧
            (∀ a0 a, val (f1 a0) a > 0 → oind (f2 a0) ((h1 a0 a)) = oind (f1 a0) (Some a)) ∧
            (∀ a0 a, val (f1 a0) a > 0 → oval (f2 a0) ((h1 a0 a)) = val (f1 a0) (a)) ∧
            (∀ a0 a, val (f2 a0) a > 0 → oind (f1 a0) ((h2 a0 a)) = oind (f2 a0) (Some a)) ∧
            (∀ a0 a, val (f2 a0) a > 0 → oval (f1 a0) ((h2 a0 a)) = val (f2 a0) (a)))
         as (hf1&hf2&Hfdom1&Hfdom2&Hflr&Hfrl&Hfind1&Hfval1&Hfind2&Hfval2).
  {
    eexists.
    Unshelve.
    all: swap 1 2.
    { 
      intros a.
      specialize (Hequivf a).
      apply eq_ival_nondep_option_necc, eq_ival_nondep_option_symm,
      ClassicalEpsilon.constructive_indefinite_description in Hequivf
        as (hf1&Hrest). exact hf1.
    }
    eexists.
    Unshelve.
    all: swap 1 2.
    { 
      intros a.
      specialize (Hequivf a).
      apply eq_ival_nondep_option_necc, eq_ival_nondep_option_symm,
      ClassicalEpsilon.constructive_indefinite_description in Hequivf
        as (hf1&Hrest).
      apply ClassicalEpsilon.constructive_indefinite_description in Hrest
        as (hf2&Hrest). exact hf2.
    }
    repeat split; intros a0 ?;
      destruct (Hequivf a0) => //=;
      repeat destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?&?&?&?);
      firstorder.
  }
  apply eq_ival_nondep_option_suffice.
  eexists.
  Unshelve.
  all: swap 1 2.
  { 
    intros (im1&if1).
    destruct (Rgt_dec (val m1 im1) 0) as [Hgt|]; last by (exact None).
    specialize (Hind1 im1 Hgt).
    destruct (h1 im1) as [im1'|]; last by (exact None).
    destruct (hf1 _ if1) as [if1'|]; last by (exact None).
     refine (Some (existT im1' (eq_rect_r (λ x, idx (f2 x))  if1' _))).
     { abstract (rewrite //= in Hind1; inversion Hind1 as [Heq]; done). }
  }
  eexists.
  Unshelve.
  all: swap 1 2.
  { 
    intros (im2&if2).
    destruct (Rgt_dec (val m2 im2) 0) as [Hgt|]; last by (exact None).
    specialize (Hind2 im2 Hgt).
    destruct (h2 im2) as [im2'|]; last by (exact None).
    destruct (hf2 _ if2) as [if2'|]; last by (exact None).
     refine (Some (existT im2' (eq_rect_r (λ x, idx (f1 x))  if2' _))).
     { abstract (rewrite //= in Hind2; inversion Hind2 as [Heq]; done). }
  }
  repeat split => //=.
  - intros (im2&if2) Hgt => //=.
    repeat destruct Rgt_dec => //=; last first.
    { rewrite //= in Hgt. exfalso; apply n. specialize (val_nonneg (f2 (ind m2 im2)) if2). nra. }
    generalize (Hind2 im2) as Hind2x.
    generalize (Hval2 im2) as Hval2x.
    destruct (h2 im2) => //=; last first.
    { intros. rewrite {1}Hval2x; eauto. } 
    specialize (Hfval2 _ if2) => //=.
    destruct (hf2 _ if2) => //=; last first.
    { intros. rewrite //= in Hgt. rewrite //= in Hfval2.
      assert (val (f2 (ind m2 im2)) if2 > 0).
      { specialize (val_nonneg m2 im2). intros. nra. }
      rewrite {1}Hfval2; done.
    }
    intros ??.
    cut (∀ a b, a > 0 → b > 0 → a * b > 0); last by (intros; nra).
    intros split. apply split.
    * rewrite Hval2x; apply r.
    * set (Hpf := (ival_bind_congr_subproof0 A m1 m2 im2 s (Hind2x r))).
      apply (Rge_gt_trans _ (val (f1 (ind m2 im2)) s0)).
      {
        right.
        eapply (Logic.EqdepFacts.f_eq_dep_non_dep) with (f := λ p x, val (f1 p) x).
        apply Logic.EqdepFacts.eq_sigT_eq_dep.
        destruct Hpf. f_equal.
      }
      rewrite //= in Hgt.
      rewrite //= in Hfval2. rewrite Hfval2; auto; nra.
  - intros (im1&if1) Hgt => //=.
    repeat destruct Rgt_dec as [Hgtm|n]=> //=; last first.
    { rewrite //= in Hgt. exfalso; apply n. specialize (val_nonneg (f1 (ind m1 im1)) if1). nra. }
    generalize (Hind1 im1) as Hind1x.
    generalize (Hval1 im1) as Hval1x.
    generalize (Hlr im1) as Hrlx.
    destruct (h1 im1) as [im2|] => //=; [].
    generalize (Hflr _ if1) as Hfrlx.
    specialize (Hfval1 _ if1) => //=.
    destruct (hf1 _ if1) as [if2|] => //=; last first.
    { intros. rewrite //= in Hgt. rewrite //= in Hfval1.
      assert (val (f1 (ind m1 im1)) if1 > 0).
      { specialize (val_nonneg m1 im1). intros. nra. }
      cut (0 > 0); first nra.
      rewrite {1}Hfval1; done.
    }
    intros ????.
    generalize (Hind2 im2).
    generalize (Hval2 im2).
    destruct (h2 im2) => //=; last first.
    { intros Hzero. rewrite Hval1x; auto.  destruct Rgt_dec => //=.
      cut (0 > 0); first nra.
      rewrite {1}Hzero; rewrite Hval1x; done.
    }
    rewrite (Hval1x); auto; []. destruct Rgt_dec as [Hgtm1|] => //=; [].
    assert (Hgtf: val (f1 (ind m1 im1)) if1 > 0).
    {
      clear -Hgtm1 Hgt.
      specialize (val_nonneg (f1 (ind m1 im1)) if1). intros. rewrite //= in Hgt. nra.
    }
    specialize (Hfval2 _ if2) => //=.
    assert (Logic.EqdepFacts.eq_dep _ (λ Ty, option (idx (f1 Ty))) _
              (hf2 (ind m2 im2) (eq_rect_r (λ x : A, idx (f2 x)) if2
                                           (ival_bind_congr_subproof A m1 m2 im1 im2 (Hind1x Hgtm))))
              _ (hf2 (ind m1 im1) if2)) as Hdep.
    { 
      clear -Hind1x.
      rewrite /eq_rect_r.
      generalize (Hind1x Hgtm) => Heq. inversion Heq as [Heq'].
      symmetry in Heq'.
      rewrite /eq_rect_r.
      assert (Heq' = (Logic.eq_sym (ival_bind_congr_subproof A m1 m2 im1 im2 Heq))) as <-.
      { apply classical_proof_irrelevance.  }
      destruct Heq' => //=.
    }
    intros ? Hind1x'.
    destruct (hf2 (ind m2 im2)
                  (eq_rect_r (λ x : A, idx (f2 x)) if2 (ival_bind_congr_subproof A m1 m2 im1 im2
                                                                                 (Hind1x Hgtm))))
      as [if1'|]; last first.
    { 
      clear -Hfrlx Hgtf Hdep Hgtm Hind1x.
      specialize (Hind1x Hgtm).
      inversion Hind1x as [Heq].
      rewrite Heq in Hdep.
      rewrite Hfrlx // in Hdep.
      inversion Hdep.
    }
    f_equal. subst. 
    specialize (Hrlx Hgtm). inversion Hrlx. subst. f_equal.
    rewrite /eq_rect_r.
    specialize (Hind1x Hgtm). inversion Hind1x as [Heq].
    clear -Heq Hfrlx Hgtf Hdep.
    assert (Heq = (Logic.eq_sym (ival_bind_congr_subproof0 A m1 m2 im2 im1 (Hind1x' Hgtm1)))) as <-.
    { apply classical_proof_irrelevance.  }
    clear -Heq Hind1x' Hfrlx Hgtf Hdep. destruct Heq => //=.
    cut (Some if1' = Some if1); first by congruence.
    rewrite -Hfrlx; auto.
    apply eq_dep_eq in Hdep. auto.
  - intros (im2&if2) Hgt => //=.
    repeat destruct Rgt_dec as [Hgtm|n]=> //=; last first.
    { rewrite //= in Hgt. exfalso; apply n. specialize (val_nonneg (f2 (ind m2 im2)) if2). nra. }
    generalize (Hind2 im2) as Hind2x.
    generalize (Hval2 im2) as Hval2x.
    generalize (Hrl im2) as Hrlx.
    destruct (h2 im2) as [im1|] => //=; [].
    generalize (Hfrl _ if2) as Hfrlx.
    specialize (Hfval2 _ if2) => //=.
    destruct (hf2 _ if2) as [if1|] => //=; last first.
    { intros. rewrite //= in Hgt. rewrite //= in Hfval2.
      assert (val (f2 (ind m2 im2)) if2 > 0).
      { specialize (val_nonneg m2 im2). intros. nra. }
      cut (0 > 0); first nra.
      rewrite {1}Hfval2; done.
    }
    intros ????.
    generalize (Hind1 im1).
    generalize (Hval1 im1).
    destruct (h1 im1) => //=; last first.
    { intros Hzero. rewrite Hval2x; auto.  destruct Rgt_dec => //=.
      cut (0 > 0); first nra.
      rewrite {1}Hzero; rewrite Hval2x; done.
    }
    rewrite (Hval2x); auto; []. destruct Rgt_dec as [Hgtm1|] => //=; [].
    assert (Hgtf: val (f2 (ind m2 im2)) if2 > 0).
    {
      clear -Hgtm1 Hgt.
      specialize (val_nonneg (f2 (ind m2 im2)) if2). intros. rewrite //= in Hgt. nra.
    }
    specialize (Hfval1 _ if1) => //=.
    assert (Logic.EqdepFacts.eq_dep _ (λ Ty, option (idx (f2 Ty))) _
              (hf1 (ind m1 im1) (eq_rect_r (λ x : A, idx (f1 x)) if1
                                           (ival_bind_congr_subproof0 A m1 m2 im2 im1 (Hind2x Hgtm))))
              _ (hf1 (ind m2 im2) if1)) as Hdep.
    { 
      clear -Hind2x.
      rewrite /eq_rect_r.
      generalize (Hind2x Hgtm) => Heq. inversion Heq as [Heq'].
      symmetry in Heq'.
      rewrite /eq_rect_r.
      assert (Heq' = (Logic.eq_sym (ival_bind_congr_subproof0 A m1 m2 im2 im1 Heq))) as <-.
      { apply classical_proof_irrelevance.  }
      destruct Heq' => //=.
    }
    intros ? Hind2x'.
    destruct (hf1 (ind m1 im1)
                  (eq_rect_r (λ x : A, idx (f1 x)) if1 (ival_bind_congr_subproof0 A m1 m2 im2 im1
                                                                                 (Hind2x Hgtm))))
      as [if2'|]; last first.
    { 
      clear -Hfrlx Hgtf Hdep Hgtm Hind2x.
      specialize (Hind2x Hgtm).
      inversion Hind2x as [Heq].
      rewrite Heq in Hdep.
      rewrite Hfrlx // in Hdep.
      inversion Hdep.
    }
    f_equal. subst. 
    specialize (Hrlx Hgtm). inversion Hrlx. subst. f_equal.
    rewrite /eq_rect_r.
    specialize (Hind2x Hgtm). inversion Hind2x as [Heq].
    clear -Heq Hfrlx Hgtf Hdep.
    assert (Heq = (Logic.eq_sym (ival_bind_congr_subproof A m1 m2 im1 im2 (Hind2x' Hgtm1)))) as <-.
    { apply classical_proof_irrelevance.  }
    clear -Heq Hind2x' Hfrlx Hgtf Hdep. destruct Heq => //=.
    cut (Some if2' = Some if2); first by congruence.
    rewrite -Hfrlx; auto.
    apply eq_dep_eq in Hdep. auto.
  - intros (im1&if1) (Hgt1&Hgt2)%val_bind_gt.
    destruct Rgt_dec => //=.
    generalize (Hind1 im1) as Hind1x.
    generalize (Hval1 im1) as Hval1x.
    generalize (Hlr im1) as Hrlx.
    destruct (h1 im1) as [im2|] => //=; [].
    generalize (Hflr _ if1) as Hfrlx.
    specialize (Hfval1 _ if1) => //=.
    specialize (Hfind1 _ if1) => //=.
    destruct (hf1 _ if1) as [if2|] => //=; []. 
    intros. rewrite //=. etransitivity; last apply Hfind1 => //=.
    rewrite //=.
    f_equal.
    eapply Logic.EqdepFacts.f_eq_dep_non_dep with (f := λ p x, ind (f2 p) x).
    generalize (Hind1x r). intros Heq. inversion Heq as [Heq'].
    rewrite /eq_rect_r.
    symmetry in Heq'.
    assert (Heq' = (Logic.eq_sym (ival_bind_congr_subproof A m1 m2 im1 im2 Heq))) as <-.
    { apply classical_proof_irrelevance.  }
    destruct Heq' => //=.
  - intros (im1&if1) (Hgt1&Hgt2)%val_bind_gt.
    destruct Rgt_dec => //=.
    generalize (Hind1 im1) as Hind1x.
    generalize (Hval1 im1) as Hval1x.
    generalize (Hlr im1) as Hrlx.
    destruct (h1 im1) as [im2|] => //=; [].
    generalize (Hflr _ if1) as Hfrlx.
    specialize (Hfval1 _ if1) => //=.
    specialize (Hfind1 _ if1) => //=.
    destruct (hf1 _ if1) as [if2|] => //=; []. 
    intros. rewrite //=. f_equal; first by (apply Hval1x; auto).
    etransitivity; last apply Hfval1 => //=.
    rewrite //=.
    f_equal.
    eapply Logic.EqdepFacts.f_eq_dep_non_dep with (f := λ p x, val (f2 p) x).
    generalize (Hind1x r). intros Heq. inversion Heq as [Heq'].
    rewrite /eq_rect_r.
    symmetry in Heq'.
    assert (Heq' = (Logic.eq_sym (ival_bind_congr_subproof A m1 m2 im1 im2 Heq))) as <-.
    { apply classical_proof_irrelevance.  }
    destruct Heq' => //=.
Qed.

Global Instance ibind_proper {X Y}:
  Proper ((pointwise_relation _ (@eq_ival Y)) ==> @eq_ival X ==> @eq_ival Y) (@mbind ival _ X Y).
Proof. intros ?? ? ?? ?. apply ival_bind_congr; eauto. Qed.

Lemma ival_bind_pos_congr {A B} (m1 m2: ival A) (f1 f2: A → ival B) :
  eq_ival m1 m2 →
  (∀ a, (∃ i, ind m1 i = a ∧ val m1 i > 0) ∨
        (∃ i, ind m2 i = a ∧ val m2 i > 0) → eq_ival (f1 a) (f2 a)) →
  eq_ival (mbind f1 m1) (mbind f2 m2).
Proof.
  intros Heqm.
  intros Heqf.
  etransitivity.
  { eapply ival_bind_P with (P := λ a : A,
                              (∃ i, ind m1 i = a ∧ val m1 i > 0) ∨
                              (∃ i, ind m2 i = a ∧ val m2 i > 0)).
    Unshelve.
    intros x Hl. left. done.  }
  etransitivity; last first.
  { symmetry. eapply ival_bind_P with (P := λ a : A,
                              (∃ i, ind m1 i = a ∧ val m1 i > 0) ∨
                              (∃ i, ind m2 i = a ∧ val m2 i > 0)).
    Unshelve.
    intros x Hl. right. done.  }
  eapply ival_bind_congr.
  - apply eq_ival_equip; first done.
  - intros (a&Hpf). eauto.
Qed.

Lemma ival_bind_P' {A B} (m: ival A) (f: A → ival B) (P: A → Prop) f':
  ∀ Hpf: ∀ x, (∃ i, ind m i = x ∧ val m i > 0) → P x,
  (∀ x, eq_ival (f (sval x)) (f' x)) → 
  eq_ival (mbind f m) (mbind f' (ival_equip m _ Hpf)).
Proof. 
  intros Hpf Heq. etransitivity.
  eapply (ival_bind_P _ _ _ Hpf).
  eapply ival_bind_congr; first reflexivity.
  intros. rewrite Heq. reflexivity.
Qed.

Lemma ival_mjoin_congr {A} (m1 m2: ival (ival A)):
  eq_ival m1 m2 →
  eq_ival (mjoin m1) (mjoin m2).
Proof.
  intros Heq.
  rewrite /mjoin/base.mjoin/ival_join//=. setoid_rewrite Heq. reflexivity.
Qed.

Lemma coerce_supp {X} (h: X → R) (x: X) (Hpf: h x > 0) : support h.
Proof.
  exists x. abstract (destruct Rgt_dec; eauto).
Defined.

Lemma eq_zero_ival_supp {X} (I: ival X):
  eq_ival I zero_ival ↔ (∀ i, val I i > 0 → False).
Proof.
  split.
  - intros (h1&?) i Hgt0.
    destruct (h1 (coerce_supp _ i Hgt0)) as ([]&?).
  - intros Hfalse.
    symmetry.
    eexists.
    Unshelve. all: swap 1 2.
    { intros ([]&?). }
    eexists.
    Unshelve. all: swap 1 2.
    { intros (x&Hgt0). destruct Rgt_dec => //=. exfalso; eapply Hfalse; eauto. }
    repeat split => //=.
    * intros ([]&?). 
    * intros (?&Hgt). 
      exfalso. destruct Rgt_dec => //=. eapply Hfalse; eauto.
    * intros ([]&?). 
    * intros ([]&?). 
Qed.

Lemma zero_ival_fmap_inv {X Y: Type} (f: X → Y) (I: ival X):
  eq_ival (a ← I; mret (f a)) zero_ival →
  eq_ival I zero_ival.
Proof.
  rewrite ?eq_zero_ival_supp.
  intros Hzero i Hgt0.
  apply (Hzero (existT i tt)) => //=.
  nra.
Qed.

Lemma mjoin_zero_ival {X} :
  eq_ival (mjoin (@zero_ival (ival X))) zero_ival.
Proof.
  apply eq_zero_ival_supp.
  intros (?&?) => //=.
Qed.

Lemma ival_plus_bind {A B} (m1 m2: ival A) (f: A → ival B) :
  eq_ival (x ← iplus m1 m2; f x) (iplus (x ← m1; f x) (x ← m2; f x)).
Proof. 
    eexists. Unshelve. all: swap 1 2.
    { intros (([i1|i2]&ih)&Hgt).
      * exists (inl (existT i1 ih)).
        rewrite //=.
      * exists (inr (existT i2 ih)).
        rewrite //=.
    }
    eexists. Unshelve. all: swap 1 2.
    { intros ([(i1&ih)|(i2&ih)]&Hgt).
      * exists (existT (inl i1) ih).
        rewrite //=.
      * exists (existT (inr i2) ih).
        rewrite //=.
    }
    repeat split => //=.
    * intros (([i1|i2]&ih)&Hgt) => //=.
    * intros ([(i1&ih)|(i2&ih)]&Hgt) => //=.
    * intros (([i1|i2]&ih)&Hgt) => //=.
    * intros (([i1|i2]&ih)&Hgt) => //=.
Qed.

Lemma ival_zero_bind {A B} (f: A → ival B) :
  eq_ival (x ← zero_ival; f x) zero_ival.
Proof. 
    eexists. Unshelve. all: swap 1 2.
    { intros (([]&?)&?). }
    eexists. Unshelve. all: swap 1 2.
    { intros ([]&?). }
    repeat split => //=.
    * intros (([]&?)&?).
    * intros ([]&?). 
    * intros (([]&?)&?).
    * intros (([]&?)&?).
Qed.

Lemma ival_scale_bind {A B} r (m: ival A) (f: A → ival B) :
  eq_ival (x ← iscale r m; f x) (iscale r (x ← m; f x)). 
Proof. 
  destruct (Req_dec r 0) as [Heq0|Hneq0%Rabs_no_R0].
  { subst. setoid_rewrite iscale_0_l. apply ival_zero_bind. }
  specialize (Rabs_pos r) => Rpos.
    eexists. Unshelve. all: swap 1 2.
    { intros (x&Hgt); exists x.
      abstract (rewrite //=; rewrite //= in Hgt;
                repeat destruct Rgt_dec; auto;
                nra).
    }
    eexists. Unshelve. all: swap 1 2.
    { intros (x&Hgt); exists x.
      abstract (rewrite //=; rewrite //= in Hgt;
                repeat destruct Rgt_dec; auto;
                nra).
    }
    repeat split => //=.
    * intros (a&?) => //=. apply sval_inj_pred => //=.
    * intros (a&?) => //=. apply sval_inj_pred => //=.
    * intros (a&?) => //=.
    * intros (a&?) => //=. nra.
Qed.

Lemma ival_bind_mret_mret {A B C} (m: ival A) (f: A → B) (g : B → C) :
  eq_ival (x ← (x ← m; mret (f x)); mret (g x)) (x ← m; mret (g (f x))).
Proof.
  setoid_rewrite ival_assoc. eapply ival_bind_congr; first by reflexivity.
  intros a. setoid_rewrite ival_left_id; reflexivity.
Qed.

Definition idxOf {A} (I: ival A) : ival (idx I) :=
  {| idx := idx I; val := val I; ind := id; val_nonneg := val_nonneg I |}.

Lemma eq_ival_idxOf {A} (I: ival A) :
  eq_ival I (x ← idxOf I; mret (ind I x)).
Proof.
  symmetry.
  unshelve (eexists).
  { intros ((ii&[])&Hgt).
    exists ii. rewrite //= Rmult_1_r in Hgt. auto. }
  unshelve (eexists).
  { intros (ii&Hgt).
    exists (existT ii tt) => //=. by rewrite Rmult_1_r. }

  repeat split => //=.
  - intros ((ii&[])&Hgt) => //=.
    apply sval_inj_pred => //=.
  - intros (ii&Hgt) => //=.
    apply sval_inj_pred => //=.
  - intros ((ii&[])&Hgt) => //=.
  - intros ((ii&[])&Hgt) => //=. nra.
Qed.
    
Definition supp_idxOf {A} (I: ival A) : ival (support (val I)).
   refine (ival_equip (idxOf I) _ _).
   abstract (rewrite /idxOf//=; intros i (?&->&?); destruct Rgt_dec => //=).
Defined.

Lemma ival_bind_comm_aux {A1 A2} (I1: ival A1) (I2: ival A2) :
  eq_ival (x ← I1; y ← I2; mret (x, y)) (y ← I2; x ← I1; mret (x, y)).
Proof.
  unshelve (eexists).
  { intros ((i1&i2&[])&Hgt).
    exists (existT i2 (existT i1 tt)).
    { abstract (repeat destruct Rgt_dec => //=; simpl in *; nra). }
  }
  unshelve (eexists).
  { intros ((i1&i2&[])&Hgt).
    exists (existT i2 (existT i1 tt)).
    { abstract (repeat destruct Rgt_dec => //=; simpl in *; nra). }
  }
  repeat split => //=.
  - intros ((i1&i2&[])&Hgt).
    apply sval_inj_pred => //=.
  - intros ((i1&i2&[])&Hgt).
    apply sval_inj_pred => //=.
  - intros ((i1&i2&[])&Hgt) => //=.
  - intros ((i1&i2&[])&Hgt) => //=.
    nra.
Qed.

Lemma ival_bind_comm {A1 A2 A3} (I1: ival A1) (I2: ival A2) (f: A1 → A2 → ival A3):
  eq_ival (x ← I1; y ← I2; f x y) (y ← I2; x ← I1; f x y).
Proof.
  transitivity (xy ← (x ← I1; y ← I2; mret (x, y)); f (fst xy) (snd xy)).
  - setoid_rewrite ival_assoc.
    eapply ival_bind_congr; first by reflexivity.
    intros x.
    setoid_rewrite ival_assoc.
    eapply ival_bind_congr; first by reflexivity.
    intros y.
    setoid_rewrite ival_left_id; reflexivity.
  - setoid_rewrite ival_bind_comm_aux.
    setoid_rewrite ival_assoc.
    eapply ival_bind_congr; first by reflexivity.
    intros x.
    setoid_rewrite ival_assoc.
    eapply ival_bind_congr; first by reflexivity.
    intros y.
    setoid_rewrite ival_left_id; reflexivity.
Qed.

Definition ival_primitive {X} (I: ival X) : Prop :=
  (∀ i1 i2, ind I i1 = ind I i2 → i1 = i2). (* ∧ (∀ i, val I i > 0). *)

Lemma primitive_mret {X} (x: X):
  ival_primitive (mret x).
Proof. intros [] [] => //=. Qed.

Lemma primitive_scale {X} p (I: ival X):
  ival_primitive I → ival_primitive (iscale p I).
Proof. rewrite //=. Qed.

Lemma primitive_mbind_inj {X Y} (I: ival X) (f: X → Y):
  (∀ x y, f x = f y → x = y) →
  ival_primitive I → ival_primitive (mbind (λ x, mret (f x)) I).
Proof.
  rewrite /ival_primitive => Hinj Hprim [i1 []] [i2 []] => //=.
  intros Heq%Hinj. apply Hprim in Heq. subst => //=.
Qed.

Lemma primitive_plus {X} (I1 I2: ival X):
  ival_primitive I1 →
  ival_primitive I2 →
  ¬ (∃ i1 i2, ind I1 i1 = ind I2 i2) →
  ival_primitive (iplus I1 I2).
Proof.
  intros Hprim1 Hprim2 Hdisj ia ib.
  destruct ia, ib => //=.
  - intros Heq. f_equal. apply Hprim1; eauto.
  - intros Heq. exfalso; eapply Hdisj; eauto.
  - intros Heq. exfalso; eapply Hdisj; eauto.
  - intros Heq. f_equal. apply Hprim2; eauto.
Qed.

Lemma primitive_plus_mret {X} (x1 x2: X):
  x1 ≠ x2 →
  ival_primitive (iplus (mret x1) (mret x2)).
Proof. intros ? [[]|[]] [[]|[]] => //=; intros; try f_equal; try congruence. Qed.

Lemma eq_ival_primitive_fmap_bij {X Y} (I1 : ival X) (I2: ival Y) (h: X → Y) :
  ival_primitive I1 →
  ival_primitive I2 →
  (∀ v1, In_isupport v1 I1 → In_isupport (h v1) I2) →
  (∀ v1 v1', In_isupport v1 I1 →
             In_isupport v1' I1 →
             h v1 = h v1' → v1 = v1') →
  (∀ v2, In_isupport v2 I2 → ∃ v1, In_isupport v1 I1 ∧ h v1 = v2) →
  (∀ i1 i2, ind I2 i2 = h (ind I1 i1) → val I2 i2 = val I1 i1) →
  eq_ival (x ← I1; mret (h x)) I2.
Proof.
  intros Hind1 (* Hval1] *) Hind2 (* Hval2] *) Hrange Hinj Hsurj Hprob.
  apply eq_ival_inj_surj_suffice.
  unshelve (eexists).
  { intros ((i1&?)&Hgt).
    specialize (Hrange (ind I1 i1)).
    apply ClassicalEpsilon.constructive_indefinite_description in Hrange as (i'&?&?).
    { exists i'. abstract (repeat destruct Rgt_dec => //=; auto). }
    { exists i1; abstract (rewrite //= in Hgt; repeat destruct Rgt_dec => //=; split; auto; nra). }
  }
  repeat split => //=.
  - intros ((i1&[])&Hgt1) ((i2&[])&Hgt2) => //=.
    destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?).
    destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?).
    inversion 1; subst. apply sval_inj_pred => //=.  f_equal.
    apply (Hind1); eauto.
    apply Hinj; last (by congruence); eexists; split; eauto.
    { clear -Hgt1 Hgt2. rewrite //= in Hgt1 Hgt2. repeat destruct Rgt_dec => //=; auto. nra.  }
    { clear -Hgt1 Hgt2. rewrite //= in Hgt1 Hgt2. repeat destruct Rgt_dec => //=; auto. nra.  }
  - intros (i2&Hgt). 
    edestruct (Hsurj) as (v1&Hin&Heq).
    { exists i2; split; eauto.
      destruct Rgt_dec => //=.
    }
    destruct Hin as (i1&?&Hgt1).
    unshelve (eexists).
    { exists (existT i1 tt). rewrite //=. abstract (repeat destruct Rgt_dec => //=; nra). }
    rewrite //=.
    destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?).
    apply sval_inj_pred => //=. 
    apply Hind2. congruence.
  - intros ((i1&[])&Hgt) => //=.
    destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?) => //=.
  - intros ((i1&[])&Hgt) => //=.
    destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?) => //=.
    rewrite Rmult_1_r.
    eapply Hprob; auto.
Qed.

Definition idx_eq_ind {X} (I1: ival X) (x: X) : idx I1 → R :=
  λ i, if ClassicalEpsilon.excluded_middle_informative (ind I1 i = x) then val I1 i else 0.

From discprob.prob Require Import double rearrange.
From discprob.prob Require Import prob finite stochastic_order.
From discprob.prob Require Export countable.

Definition eq_ival_prob {X} (I1 I2: ival X) : Prop :=
  ∀ x, (ex_series (countable_sum (idx_eq_ind I1 x)) →
        is_series (countable_sum (idx_eq_ind I2 x)) (Series (countable_sum (idx_eq_ind I1 x)))) ∧
      (ex_series (countable_sum (idx_eq_ind I2 x)) →
       is_series (countable_sum (idx_eq_ind I1 x)) (Series (countable_sum (idx_eq_ind I2 x)))).

Lemma eq_ival_prob_refl {X} (I: ival X): eq_ival_prob I I.
Proof. intros x; split; eapply Series_correct. Qed.

Lemma eq_ival_prob_sym {X} (I1 I2: ival X): eq_ival_prob I1 I2 → eq_ival_prob I2 I1.
Proof. intros Heq x; split; specialize (Heq x) as (?&?); intuition. Qed.

Lemma eq_ival_prob_trans {X} (I1 I2 I3: ival X):
  eq_ival_prob I1 I2 → eq_ival_prob I2 I3 → eq_ival_prob I1 I3.
Proof.
  intros Heq1 Heq2 x; split;
    specialize (Heq1 x) as (Heq1a&Heq1b); specialize (Heq2 x) as (Heq2a&Heq2b).
  - intros Hex. generalize (Heq1a Hex) => Heq1a'. apply is_series_unique in Heq1a' as <-.
    eapply Heq2a. eexists; eauto.
  - intros Hex. generalize (Heq2b Hex) => Heq2b'. apply is_series_unique in Heq2b' as <-.
    eapply Heq1b. eexists; eauto.
Qed.

Global Instance eq_ival_prob_Transitivite {X}: Transitive (@eq_ival_prob X).
Proof. intros ???. apply eq_ival_prob_trans. Qed.
Global Instance eq_ival_prob_Reflexive {X}: Reflexive (@eq_ival_prob X).
Proof. intros ?. apply eq_ival_prob_refl. Qed.
Global Instance eq_ival_prob_Symmetry {X}: Symmetric (@eq_ival_prob X).
Proof. intros ??. apply eq_ival_prob_sym. Qed.
Global Instance eq_ival_prob_Equivalence {X}: Equivalence (@eq_ival_prob X).
Proof. split; apply _. Qed. 

Lemma seriesC_partial_sum_bounded {X: countType} (h: X → R) r
      (Hseries: is_series (countable_sum h) r) (Hpos: ∀ x, h x >= 0) n:
         sum_n (countable_sum h) n <= r.
Proof.
  eapply is_lim_seq_incr_compare; eauto.
  { intros k. rewrite sum_Sn /plus//=. rewrite {3}/countable_sum//=.
    destruct (pickle_inv) as [a|] => //=; last nra.
    specialize (Hpos a). nra.
  }
Qed.

Lemma val_partial_sum_bounded {X: Type} (I: ival X) rI
     (Hseries: is_series (countable_sum (val I)) rI)
      n: sum_n (countable_sum (val I)) n <= rI.
Proof. intros. eapply seriesC_partial_sum_bounded; eauto using val_nonneg. Qed.

Lemma eq_ival_series {A : Type} (X Y: ival A) v:
  eq_ival X Y →
  is_series (countable_sum (val X)) v →
  is_series (countable_sum (val Y)) v.
Proof.
  intros Heq Hseries.
  destruct Heq as (h1&h2&Hspec).
  eapply (countable_series_rearrange_covering_match _ _ h2); last eassumption.
  { apply val_nonneg. }
  { apply val_nonneg. }
  { intros. intuition. }
  { intros n. exists (h1 n). intuition. }
  { intuition. } 
Qed.

Lemma sval_comm_match {A: Type} (P: A → Prop) (Q: Prop) (fl: Q → sig P) (fr: ¬ Q → sig P)
      (Htest: {Q} + {¬Q}):
  sval match Htest with | left Hpf => fl Hpf | right Hnfp => fr Hnfp end =
  match Htest with | left Hpf => sval (fl Hpf) | right Hnfp => sval (fr Hnfp) end.
Proof.
  destruct Htest => //=.
Qed.

Lemma sumbool_match_left {A: Type} (Q: Prop) (fl: Q → A) (fr: ¬ Q → A)
      (Htest: {Q} + {¬Q}) (HQ: Q): 
  match Htest with | left Hpf => fl Hpf | right Hnfp => fr Hnfp end =
  fl HQ.
Proof.
  destruct Htest => //=.
  f_equal. apply classical_proof_irrelevance.
Qed.

Lemma eq_ival_series_fun {A : Type} (X Y: ival A) f v:
  eq_ival X Y →
  (∀ a , f a 0 = 0) →
  is_series (countable_sum (λ i, Rabs (f (ind X i) (val X i)))) v →
  is_series (countable_sum (λ i, Rabs (f (ind Y i) (val Y i)))) v ∧
  is_series (countable_sum (λ i, f (ind Y i) (val Y i)))
            (Series (countable_sum (λ i, f (ind X i) (val X i)))).
Proof.
  intros Heq Hzero Hseries.
  assert (Hzero_contra : ∀ Y y, f (ind Y y) (val Y y) ≠ 0 → val Y y > 0).
  { intros Z z Hnz. destruct (val_nonneg Z z) as [|Heq']; eauto. rewrite Heq' Hzero //= in Hnz. }
  destruct Heq as (h1&h2&Hspec1&Hspec2&Hspec3&Hspec4).
  unshelve (eapply (countable_series_rearrange_covering_match_fun _ _ _); last eapply Hseries).
  { intros (x&Hgt).
    destruct (Rgt_dec (val Y x) 0) as [Hgt0|Hnot0].
    { exists (sval (h2 (gt_support_conv _ _ Hgt0))).
      abstract (rewrite -Hspec3 -Hspec4 Hspec2 //=). }
    { abstract (exfalso; eapply Hnot0; eauto). }
  }
  { intros (y1&Hgt1_pred) (y2&Hgt2_pred) => //=.
    destruct (Rgt_dec (val Y y1) 0) as [Hgt1|Hngt1] => //=; last first.
    { 
      intros Hex. exfalso.
      eapply Hngt1. eapply Hzero_contra; eauto.
    }
    destruct (Rgt_dec (val Y y2) 0) as [Hgt2|Hngt2] => //=.
    * inversion 1 as [Heq]. apply sval_inj_pi => //=.
      apply sval_inj_pred in Heq.
      apply (f_equal h1) in Heq. rewrite ?Hspec2 in Heq.
      inversion Heq. auto.
    * intros Hex. exfalso.
      eapply Hngt2. eapply Hzero_contra; eauto.
  }
  { intros (x1&Hgt1). unshelve (eexists).
    { destruct (Rgt_dec (val X x1) 0) as [Hgt|Hgnt].
      { exists (sval (h1 (gt_support_conv _ _ Hgt))).
        abstract (rewrite Hspec3 Hspec4 //=). }
      { exfalso; eapply Hgnt; eauto. }
    }
    rewrite //=.
    destruct (Rgt_dec (val X x1) 0) as [Hgt|Hngt] => //=.
    * apply sval_inj_pi. rewrite sval_comm_match => //=.
      rewrite sumbool_match_left.
      { rewrite Hspec4 => //=. } 
      { intros ?. transitivity (sval (h2 (h1 (gt_support_conv (val X) x1 Hgt)))); last first.
        { rewrite Hspec1 => //=. }
        f_equal. f_equal. apply sval_inj_pred => //=. }
  }
  { 
    intros (x&Hgt) => //=.
    destruct (Rgt_dec (val Y x) 0) as [|Hngt].
    * rewrite //=. rewrite -Hspec4 -Hspec3 Hspec2 => //=.
    * exfalso; eapply Hngt; eauto.
  }
Qed.

Lemma eq_ival_series_pred {A : Type} (X Y: ival A) v P:
  eq_ival X Y →
  is_series (countable_sum (λ i, if P (ind X i) then val X i else 0)) v →
  is_series (countable_sum (λ i, if P (ind Y i) then val Y i else 0)) v.
Proof.
  intros Heq His.
  edestruct (eq_ival_series_fun X Y (λ x y, if P x then y else 0)); eauto; last first.
  { eapply is_series_unique in His. rewrite -His; eauto. }
  { rewrite //=. eapply is_series_ext; last eapply His.
    intros n. apply countable_sum_Proper => ? //=.
    rewrite Rabs_right //=. destruct (P _); eauto using val_nonneg. nra.
  }
  { rewrite //= => a. destruct (P a); eauto. }
Qed.

Lemma eq_ival_series_fun_pos {A : Type} (X Y: ival A) f:
  eq_ival X Y →
  (∀ a , f a 0 = 0) →
  (∀ a r, r >= 0 → f a r >= 0) →
  ex_series (countable_sum (λ i, f (ind X i) (val X i)))  →
  is_series (countable_sum (λ i, f (ind Y i) (val Y i)))
            (Series (countable_sum (λ i, f (ind X i) (val X i)))).
Proof.
  intros Heq Hzero Hge (v&His).
  edestruct (eq_ival_series_fun X Y f); eauto.
  { eapply is_seriesC_ext; last eassumption; intros a.
    rewrite Rabs_right; eauto. eapply Hge. apply val_nonneg. }
Qed.

Lemma eq_ival_to_eq_ival_prob_aux {X} (I1 I2: ival X):
  eq_ival I1 I2 →
  ∀ x, (ex_series (countable_sum (idx_eq_ind I1 x)) →
        is_series (countable_sum (idx_eq_ind I2 x)) (Series (countable_sum (idx_eq_ind I1 x)))).
Proof.
  intros Heq x Hex.
  set (f := (λ x' r, if ClassicalEpsilon.excluded_middle_informative (x' = x) then
                       r
                     else 
                       0)).
  eapply (eq_ival_series_fun_pos I1 I2 f); eauto.
  { rewrite /f; intros a; destruct ClassicalEpsilon.excluded_middle_informative; eauto. }
  { rewrite /f; intros a r ?; destruct ClassicalEpsilon.excluded_middle_informative => //=; nra. }
Qed.

Lemma eq_ival_to_eq_ival_prob {X} (I1 I2: ival X):
  eq_ival I1 I2 →
  eq_ival_prob I1 I2.
Proof.
  intros Heq x; split.
  - apply eq_ival_to_eq_ival_prob_aux; eauto.
  - apply eq_ival_to_eq_ival_prob_aux; symmetry; eauto.
Qed.

Global Instance eq_ival_prob_proper X:
  Proper (@eq_ival X ==> @eq_ival X ==> iff) (@eq_ival_prob X).
Proof.
  intros ?? ? ?? ?.
  split.
  * intros. etransitivity.
    ** eapply eq_ival_to_eq_ival_prob. symmetry; eauto.
    ** etransitivity.
       *** eauto. 
       *** eapply eq_ival_to_eq_ival_prob; eauto.
  * intros. etransitivity.
    ** eapply eq_ival_to_eq_ival_prob. eauto.
    ** etransitivity.
       *** eauto. 
       *** eapply eq_ival_to_eq_ival_prob; symmetry; eauto.
Qed.
