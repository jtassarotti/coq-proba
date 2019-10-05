Require Import Reals Psatz Omega.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From discprob.measure Require Export sets sigma_algebra.
From stdpp Require Import tactics.


Record dynkin_class (A: Type) :=
  mkDynkin {
      dynkin_sets:> (A → Prop) → Prop;
      dynkin_proper : Proper (@eq_prop A ==> iff) dynkin_sets;
      dynkin_full : dynkin_sets (λ _, True);
      dynkin_closed_set_minus :
        ∀ P Q, dynkin_sets P → dynkin_sets Q → Q ⊆ P → dynkin_sets (set_minus P Q);
      dynkin_closed_unions :
        ∀ Ps : nat → (A → Prop), (∀ i, dynkin_sets (Ps i)) →
                                 (∀ i, Ps i ⊆ Ps (S i)) → dynkin_sets (unionF Ps)
    }.

Record pi_system (A: Type) :=
  mkPiSystem {
      pi_sets:> (A → Prop) → Prop;
      pi_proper : Proper (@eq_prop A ==> iff) pi_sets;
      pi_closed_pair_intersect P Q: pi_sets P → pi_sets Q → pi_sets (P ∩ Q)
    }.

Global Instance dynkin_class_proper {A: Type} X : Proper (@eq_prop A ==> iff) (@dynkin_sets A X).
Proof. apply dynkin_proper. Qed.

Definition intersection_dynkin {A: Type} (I: Type) (U: I → dynkin_class A) : dynkin_class A.
  refine {| dynkin_sets := λ x, ∀ i, (U i) x |}.
  - abstract (intros X X' Heq; split => H i; [ rewrite -Heq | rewrite Heq ]; auto).
  - abstract (intros; by apply dynkin_full).
  - abstract (intros; by apply dynkin_closed_set_minus).
  - abstract (intros; by apply dynkin_closed_unions).
Defined.

Definition minimal_dynkin {A: Type} (F: (A → Prop) → Prop) : dynkin_class A :=
  intersection_dynkin { F' : dynkin_class A | le_prop F F' } sval.

Lemma minimal_dynkin_ub {A: Type} (F : (A → Prop) → Prop) :
  le_prop F (minimal_dynkin F).
Proof.
  intros i HF (F'&Hle) => //=. by apply Hle.
Qed.

Lemma minimal_dynkin_lub {A: Type} (F : (A → Prop) → Prop) (F': dynkin_class A) :
  le_prop F F' → le_prop (minimal_dynkin F) F'.
Proof.
  intros Hle X. rewrite /minimal_dynkin/intersection_dynkin => //=.
  intros H. specialize (H (exist _ F' Hle)). apply H.
Qed.

Definition sigma_to_dynkin {A: Type} (F : sigma_algebra A) : dynkin_class A.
Proof.
  refine {| dynkin_sets := F |}; auto.
  intros. by apply sigma_closed_set_minus.
Defined.

Lemma mdp_closed_pair_intersections {A: Type} (pi: pi_system A) P1 P2 :
  minimal_dynkin pi P1 → minimal_dynkin pi P2 → minimal_dynkin pi (P1 ∩ P2).
Proof.
  intros Hin1 Hin2.
  set (D1 := λ U, ∀ V, pi V →  minimal_dynkin pi (U ∩ V)).
  assert (H1full: D1 (λ _, True)).
  { rewrite /D1 => V HV. apply minimal_dynkin_ub. eapply pi_proper; eauto.
    by rewrite left_id. }
  assert (H1closed: ∀ U V, D1 U → D1 V → V ⊆ U → D1 (set_minus U V)).
  { rewrite /D1 => U V HU HV Hsub V' HV'.
    assert (set_minus U V ∩ V' ≡ set_minus (U ∩ V') (V ∩ V')) as ->.
    { firstorder. }
    apply dynkin_closed_set_minus; eauto. firstorder.
  }
  assert (H1union:
        ∀ Ps : nat → (A → Prop), (∀ i, D1 (Ps i)) →
                                 (∀ i, Ps i ⊆ Ps (S i)) → D1 (unionF Ps)).
  { rewrite /D1 => Ps HPs Hmono V HV.
    assert (unionF Ps ∩ V ≡ unionF (λ n, Ps n ∩ V)) as ->.
    { firstorder. }
    apply dynkin_closed_unions; eauto.
    firstorder.
  }
  assert (H1proper: Proper (@eq_prop A ==> iff) D1).
  { rewrite /D1. intros ?? Heq. setoid_rewrite Heq. done. }
  set (D1' := mkDynkin _ D1 H1proper H1full H1closed H1union).
  assert (le_prop pi D1').
  { intros U HpU V HpV. apply minimal_dynkin_ub. apply pi_closed_pair_intersect; auto. }
  assert (Hle: le_prop (minimal_dynkin pi) D1').
  { apply minimal_dynkin_lub. auto. }

  set (D2 := λ U, ∀ V, (minimal_dynkin pi) V →  minimal_dynkin pi (U ∩ V)).
  assert (H2full: D2 (λ _, True)).
  { rewrite /D2 => V HV. eapply dynkin_proper; eauto.
    by rewrite left_id. }
  assert (H2closed: ∀ U V, D2 U → D2 V → V ⊆ U → D2 (set_minus U V)).
  { rewrite /D2 => U V HU HV Hsub V' HV'.
    assert (set_minus U V ∩ V' ≡ set_minus (U ∩ V') (V ∩ V')) as ->.
    { firstorder. }
    apply dynkin_closed_set_minus; eauto. firstorder.
  }
  assert (H2union:
        ∀ Ps : nat → (A → Prop), (∀ i, D2 (Ps i)) →
                                 (∀ i, Ps i ⊆ Ps (S i)) → D2 (unionF Ps)).
  { rewrite /D2 => Ps HPs Hmono V HV.
    assert (unionF Ps ∩ V ≡ unionF (λ n, Ps n ∩ V)) as ->.
    { firstorder. }
    apply dynkin_closed_unions; eauto.
    firstorder.
  }
  assert (H2proper: Proper (@eq_prop A ==> iff) D2).
  { rewrite /D2. intros ?? Heq. setoid_rewrite Heq. done. }
  set (D2' := mkDynkin _ D2 H2proper H2full H2closed H2union).
  assert (le_prop pi D2').
  { intros U HpU V HpV. apply Hle in HpV.
    rewrite /D1'//=/D1 in HpV.
    rewrite comm. apply HpV. auto.
  }
  assert (Hle2: le_prop (minimal_dynkin pi) D2').
  { apply minimal_dynkin_lub. auto. }

  apply Hle2 in Hin1. rewrite //=/D2 in Hin1. apply Hin1.
  done.
Qed.

Lemma dynkin_closed_complements {A: Type} (F: dynkin_class A) U :
  F U → F (compl U).
Proof.
  intros HF.
  assert (compl U ≡ set_minus (λ _, True) U) as -> by firstorder.
  apply dynkin_closed_set_minus; auto.
  - apply dynkin_full.
  - firstorder.
Qed.

Lemma mdp_closed_pair_union {A: Type} (pi: pi_system A) U V:
  minimal_dynkin pi U → minimal_dynkin pi V →
  minimal_dynkin pi (U ∪ V).
Proof.
  intros HU HV.
  rewrite -(compl_involutive (U ∪ V)).
  apply dynkin_closed_complements.
  rewrite compl_union. by apply mdp_closed_pair_intersections; apply dynkin_closed_complements.
Qed.

Lemma mdp_closed_finite_union {A: Type} (pi: pi_system A) Us j:
  (∀ i, minimal_dynkin pi (Us i)) →
  minimal_dynkin pi (λ x, (∃ i, (i <= j)%nat ∧ Us i x)).
Proof.
  induction j => Hin.
  - eapply dynkin_proper; last eapply (Hin O).
     intros x; split.
     * intros (i&Hle&HUs). inversion Hle; subst. eauto.
     * intros. exists O; split; eauto.
  - assert ((λ x, ∃ i : nat, (i <= S j)%nat ∧ Us i x) ≡
            (λ x, ∃ i, (i <= j)%nat ∧ Us i x) ∪ Us (S j)) as ->.
    { intros x; split.
      * intros (i&Hle&HUs). inversion Hle; subst; firstorder.
      * firstorder.
    }
    apply mdp_closed_pair_union; eauto.
Qed.

Lemma mdp_closed_unions {A: Type} (pi: pi_system A) (Us: nat → A → Prop):
  (∀ i, minimal_dynkin pi (Us i)) →
  minimal_dynkin pi (unionF Us).
Proof.
  intros HUs.
  set (Vs := λ j : nat, (λ x, ∃ i, (i <= j)%nat ∧ Us i x)).
  assert (unionF Us ≡ unionF Vs) as ->.
  { intros x. split.
    - intros (i&Hin). exists i. firstorder.
    - intros (i&Hin). destruct Hin as (j&Hle&Hj).
      exists j. auto.
  }
  apply dynkin_closed_unions.
  - intros. apply mdp_closed_finite_union. eauto.
  - intros i x (j&Hle&Hin). exists j. split; auto.
Qed.

Definition mdp_to_sigma {A: Type} (pi: pi_system A) : sigma_algebra A.
  refine {| sigma_sets := minimal_dynkin pi |}.
  - apply dynkin_full.
  - apply dynkin_closed_complements.
  - apply mdp_closed_unions.
Defined.

Lemma pi_sigma_equiv_dynkin {A: Type} (pi: pi_system A):
  eq_prop (minimal_sigma pi) (minimal_dynkin pi).
Proof.
  apply le_prop_antisym; last first.
  -  transitivity (sigma_to_dynkin (minimal_sigma pi)); last reflexivity.
     apply minimal_dynkin_lub.
     apply minimal_sigma_ub.
  - replace (dynkin_sets _ (minimal_dynkin pi)) with (sigma_sets _ (mdp_to_sigma pi)) by auto.
    apply minimal_sigma_lub.
    apply minimal_dynkin_ub.
Qed.

Definition is_pi_system {A: Type} F :=
      Proper (@eq_prop A ==> iff) F ∧
      (∀ P Q, F P → F Q → F (P ∩ Q)).

Lemma pi_of_is_pi_system {A: Type} F (His: @is_pi_system A F) : pi_system A.
Proof. refine {| pi_sets := F |}; destruct His; auto. Defined.

