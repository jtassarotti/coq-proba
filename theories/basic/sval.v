From mathcomp Require Export ssreflect eqtype ssrbool.
From discprob.basic Require Export classic_proof_irrel.

Lemma sval_inj_pred {A: Type} (P: pred A) (a b: {x : A | P x}):
  sval a = sval b -> a = b.
Proof.  
  destruct a, b. rewrite /sval. intros. subst; f_equal. apply bool_irrelevance.
Qed.

Lemma sval_inj_pi {A: Type} (P: A -> Prop) (a b: {x : A | P x}):
  sval a = sval b -> a = b.
Proof.  
  destruct a, b. rewrite /sval. intros. subst; f_equal. apply classical_proof_irrelevance. 
Qed.