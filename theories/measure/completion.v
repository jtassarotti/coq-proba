Require Import Reals Psatz Omega Fourier.
From stdpp Require Import tactics list.
From discprob.basic Require Import seq_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.measure Require Export borel integral.
Require Import ClassicalEpsilon.

Definition complete {A: Type} {F: measurable_space A} (μ: measure A) :=
  ∀ U V, F V → μ V = 0 → le_prop U V → F U.

Lemma completion_union_proj {A: Type} {F: measurable_space A} (μ: measure A) Ps
      (Hin : ∀ i : nat, ∃ W V : A → Prop, F W ∧ F V ∧ le_prop W (Ps i)
                                          ∧ le_prop (Ps i) V ∧ μ (set_minus V W) = 0) :
  nat → ((A → Prop) * (A → Prop)).
Proof.
  intros i.
  specialize (Hin i).
  apply ClassicalEpsilon.constructive_indefinite_description in Hin as (Wi&Hrest).
  apply ClassicalEpsilon.constructive_indefinite_description in Hrest as (Vi&Hrest).
  exact (Wi, Vi).
Defined.

Lemma completion_closed_full {A: Type} {F: measurable_space A} (μ: measure A):
  ∃ W V : A → Prop,
    F W ∧ F V ∧ le_prop W (λ _ : A, True) ∧ le_prop (λ _ : A, True) V ∧ μ (set_minus V W) = 0.
Proof.
  exists (λ _, True), (λ _, True); split_and!; eauto; try reflexivity.
  rewrite -(measure_empty _ μ). apply measure_proper.
  intros z; split.
  * intros (?&?). exfalso; auto.
  * intros [].
Qed.

Lemma completion_closed_union {A: Type} {F: measurable_space A} (μ: measure A):
  ∀ Ps : nat → A → Prop,
    (∀ i : nat,
        ∃ W V : A → Prop, F W ∧ F V ∧ le_prop W (Ps i) ∧ le_prop (Ps i) V ∧ μ (set_minus V W) = 0)
    → ∃ W V : A → Prop,
      F W ∧ F V ∧ le_prop W (unionF Ps) ∧ le_prop (unionF Ps) V ∧ μ (set_minus V W) = 0.
Proof.
  intros Ps Hin.
  set (Ws := (unionF (λ i : nat, (completion_union_proj μ Ps Hin i).1))).
  set (Vs := (unionF (λ i : nat, (completion_union_proj μ Ps Hin i).2))).
  assert (F Ws).
  { apply sigma_closed_unions. rewrite /completion_union_proj.
    intros i; do 2 destruct constructive_indefinite_description.
    intuition. }
  assert (F Vs).
  { apply sigma_closed_unions. rewrite /completion_union_proj.
    intros i; do 2 destruct constructive_indefinite_description.
    intuition. }
  assert (F (set_minus Vs Ws)).
  { apply sigma_closed_set_minus; eauto. }
  assert (∀ i : nat,
             F (set_minus (completion_union_proj μ Ps Hin i).2 (completion_union_proj μ Ps Hin i).1)).
  {
    intros i. rewrite /completion_union_proj.
    do 2 destruct constructive_indefinite_description => //=.
    apply sigma_closed_set_minus; intuition.
  }

  exists Ws, Vs; split_and!; eauto.
  * rewrite /Ws. intros z. rewrite /completion_union_proj.
    intros (i&?).
    do 2 destruct constructive_indefinite_description.
    exists i. firstorder.
  * rewrite /Vs. intros z. rewrite /completion_union_proj.
    intros (i&?).
    exists i.
    do 2 destruct constructive_indefinite_description.
    firstorder.
  * apply Rle_antisym; last apply Rge_le; auto.
    transitivity (μ (unionF (λ i : nat, set_minus
                                          (completion_union_proj μ Ps Hin i).2
                                          (completion_union_proj μ Ps Hin i).1))).
    { apply measure_mono; eauto.
      intros z (Hin1&Hnin2).
      destruct Hin1 as (i&Hin1).
      exists i. assert (¬ (completion_union_proj μ Ps Hin i).1 z) as Hin2.
      { intros Hin'. eapply Hnin2; eauto. exists i; eauto. }
      rewrite /completion_union_proj in Hin1 Hin2 *.
      do 2 destruct constructive_indefinite_description => //=.
    }
    right. apply measure_countable_subadditivity0; eauto.
    intros. rewrite /completion_union_proj;
                  do 2 destruct constructive_indefinite_description => //=; intuition.
Qed.

Definition sigma_completion {A: Type} {F: measurable_space A} (μ: measure A) : sigma_algebra A.
Proof.
  refine {| sigma_sets := λ U, ∃ W V, F W ∧ F V ∧ le_prop W U ∧ le_prop U V
                                      ∧ μ (set_minus V W) = 0 |}.
  - abstract (intros U U' Heq; by setoid_rewrite Heq).
  - apply completion_closed_full.
  - abstract (intros P (W&V&?&?&?&?&Hz);
    exists (compl V), (compl W);
    split_and!; eauto;
    [ intros z Hfalse HP; apply Hfalse; eauto |
      intros z Hfalse HP; apply Hfalse; eauto |
      rewrite (set_minus_union_complement');
      rewrite (set_minus_union_complement') in Hz * => Hz;
      rewrite compl_involutive -Hz; apply measure_proper; by rewrite comm ]).
  - apply completion_closed_union.
Defined.

(*
Definition completion {A: Type} {F: sigma_algebra A} (μ: measure F): measure (sigma_completion μ).
Proof.
  refine {| measure_fun :=

*)
