From mathcomp Require Export ssreflect.
From mathcomp Require eqtype.
From discprob.basic Require Export classic_proof_irrel.

Notation sval := eqtype.sval.

Lemma sval_inj_pred {A: Type} (P: A -> bool) (a b: {x : A | is_true (P x)}):
  proj1_sig a = proj1_sig b -> a = b.
Proof.
  destruct a, b. rewrite /proj1_sig. intros. subst; f_equal. eapply eqtype.bool_irrelevance.
Qed.

Lemma sval_inj_pi {A: Type} (P: A -> Prop) (a b: {x : A | P x}):
  proj1_sig a = proj1_sig b -> a = b.
Proof.
  destruct a, b. rewrite /proj1_sig. intros. subst; f_equal. apply classical_proof_irrelevance.
Qed.
