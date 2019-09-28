Require Import ClassicalFacts Classical_Prop ProofIrrelevanceFacts.

Lemma classical_proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.
Proof. apply proof_irrelevance_cci. intros. apply Classical_Prop.classic. Qed.

Module PI. Definition proof_irrelevance := classical_proof_irrelevance. End PI.

Module PIT := ProofIrrelevanceTheory(PI).
Export PIT.