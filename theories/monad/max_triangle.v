From discprob.basic Require Import base order nify seq_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat bigop fintype binomial.
Require Import Coq.omega.Omega Coq.Program.Wf.

Lemma uphalf_le n m:
  n <= m →
  uphalf n <= uphalf m.
Proof.
  move /leP => Hle. induction Hle.
  - done. 
  - nify; etransitivity; first apply IHHle. clear. 
    induction m => //=; first omega.
    rewrite ?uphalf_half; destruct (odd m); nify; omega.
Qed.

Lemma half_double_lt m n: m < n./2 → (m.*2 < n).
Proof.
  assert (Hlt: 0 < 2) by auto.
  rewrite -(ltn_pmul2r Hlt) -{2}(odd_double_half n). rewrite -?muln2.
  destruct (odd n) => //= ?; nify; omega.
Qed.

Lemma uphalf_sum_edge_odd n: 
  odd n →
  \sum_(0 <= i < n) (if i + i < n.+1 then 1 else 0) =
  uphalf n.
Proof.  
  assert (0 = n ∨ 0 < n)%coq_nat as [Heq|Hgt0] by omega.
  { subst. rewrite ?big_geq => //=. }
  
  transitivity (\sum_(0 <= i < uphalf n) 1); last first.
  { rewrite sum_nat_const_nat. nify. omega. }
  
  symmetry; rewrite (big_nat_widen 0 _ n); last first.
  { rewrite -{2}(uphalf_double n). apply uphalf_le; nify; omega. }
  
  rewrite -big_mkcondr //=. eapply eq_bigl.
             intros k. rewrite addnn. apply /ltP; case: ifP.
  - intros Hlt. 
    assert (Hle': k.*2 <= n) by (nify; omega).
    apply half_leq in Hle'. nify.
    eapply le_lt_trans; eauto.
    rewrite //= uphalf_half. destruct (odd n) => //=.
  - move /negbT/ltP => Hlt Hlt'.
    apply Hlt. apply /ltP/half_double_lt. nify. done.
Qed.

Lemma uphalf_sum_edge_even n: 
  ~~ odd n →
  \sum_(0 <= i < n) (if i + i < n then 1 else 0) =
  uphalf n.
Proof.  
  intros Heven.
  assert (0 = n ∨ 0 < n)%coq_nat as [Heq|Hgt0] by omega.
  { subst. rewrite ?big_geq => //=. }
  
  transitivity (\sum_(0 <= i < uphalf n) 1); last first.
  { rewrite sum_nat_const_nat. nify. omega. }
  
  symmetry; rewrite (big_nat_widen 0 _ n); last first.
  { rewrite -{2}(uphalf_double n). apply uphalf_le; nify; omega. }
  
  rewrite -big_mkcondr //=. eapply eq_bigl.
  intros k. rewrite addnn. apply /ltP; case: ifP.
  - intros Hlt. 
    assert (Hle': k.*2 < n - 1). 
    { move /ltP in Hlt. inversion Hlt; last (nify; omega).
      subst. rewrite //= odd_double // in Heven. }
    assert (2 <= n).
    { nify.  destruct n; first omega. destruct n; rewrite //= in Heven; omega. }
  
    rewrite uphalf_half. destruct (odd n) => //=. 
    rewrite add0n.
    apply (le_lt_trans _ (n - 2)./2); last first.
    { assert (n = (S (S (n - 2)))) as Hsum by (nify; omega). 
      rewrite {2}Hsum => //=. }
    apply /leP.
    rewrite -(half_double k) half_leq => //. 
    nify; omega.
  - move /negbT/ltP => Hlt Hlt'.
    apply Hlt. apply /ltP/half_double_lt. rewrite uphalf_half in Hlt'.
    move: Hlt'. destruct (odd n) => //= ?. nify. omega. 
Qed.

Lemma odd_half_double_lt n: odd n → n./2 + n./2 < n.
Proof.
  intros Hodd. rewrite -{3}(half_double n) -addnn halfD Hodd => //=.
Qed.

Lemma lt_addnn: ∀ n i, odd n → i ≠ uphalf n → (i + i < n.+2) = (i + i < n.+1).
Proof.
  intros n i Hodd Hneq.
  apply /ltP; case: ifP.
  - intros; nify; omega. 
  - move /ltP. intros Hlt. assert (i + i >= S n) by (nify; omega).
    intros Hfalse.
    cut (i + i <> S n). 
    { intros. nify. omega. }
    intros Heq. apply Hneq. 
    rewrite addnn in Heq.
    apply (f_equal half) in Heq. rewrite /= in Heq.
    nify. done.
Qed.

Lemma uphalf_sum_rec n:
  odd n →
  \sum_(0 <= i < n.+1) (if i + i < n.+2 then 1 else 0) =
  \sum_(0 <= i < n.+1) (if i + i < n.+1 then 1 else 0) + 1.
Proof.
  rewrite ?big_mkord => Hodd.
  assert (Hlt: (n.+1)./2 < n.+1).
  { destruct n; first by rewrite //=. 
    nify. eapply (le_lt_trans _ (S n)); auto.
    rewrite -{2}(half_double (S n)).
    apply /leP.
    apply half_leq.
    nify. omega.
  } 
  rewrite (bigD1 (Ordinal Hlt)) //.
  rewrite //=. rewrite addnC; f_equal. 
  - rewrite big_mkcond //=. eapply eq_bigr. intros (i&Hlt') _.
    rewrite //=.
    case: ifP => Hneq; last first.
    { case: ifP; auto. intros Hcontra. move /eqP in Hneq.
      inversion Hneq; subst.
      rewrite ?uphalf_half in Hcontra. rewrite Hodd //= in Hcontra.
      rewrite -{3}(half_double n) -addnn halfD Hodd //= in Hcontra. 
      nify. omega.
    }
    rewrite lt_addnn => //. intros Heq. subst. move /eqP in Hneq.
    apply /Hneq/ord_inj => //=. 
  - case: ifP; auto.
    move /ltP. intros Hn. contradiction Hn.
    rewrite uphalf_half Hodd => //=. 
    specialize (odd_half_double_lt n Hodd) => ?. 
    nify. omega.
Qed.

Lemma uphalf_sum_half n:
  \sum_(0 <= i < n) (if i < n - i then 1 else 0) = uphalf n.
Proof.
  transitivity (\sum_(0 <= i < n) (if i + i < n then 1 else 0)).
  { rewrite ?big_mkord -?big_mkcond. apply eq_bigl. intros (i&Hlt) => //=.
    apply /ltP. case: ifP; move /ltP; rewrite -?plusE -?minusE => ?; omega. 
  }
  rewrite uphalf_half.
  elim: n => [|n IHn]; first by rewrite ?big_geq.
  rewrite //= uphalf_half -IHn.
  rewrite big_nat_recr //=. destruct n => //=.
  - rewrite ?big_geq //=.
  - case: ifP.
    { move /ltP. rewrite -?plusE. intros. exfalso. omega. }
    intros. rewrite addn0.
    case_eq (odd n); last first.
    * intros Heven. rewrite uphalf_sum_edge_odd => //=; last by (rewrite Heven => //).
      rewrite IHn //= uphalf_half !Heven /=. nify. omega.
    * intros Hodd. rewrite uphalf_sum_edge_even => //=; last by (rewrite Hodd => //).
      rewrite //= uphalf_half Hodd //= in IHn.
      rewrite uphalf_sum_rec //= IHn. nify; omega. 
Qed.

Lemma uphalf_sum_max n:
\sum_(0 <= i < n) Init.Nat.max i (n.+1 - i - 1) =
\sum_(0 <= i < n) Init.Nat.max i (n - i - 1) + uphalf n.
Proof.  
  transitivity (\sum_(0 <= i < n) (Init.Nat.max i (n - i - 1) + (if i < n - i then 1 else 0))). 
  { rewrite ?big_mkord.
    eapply eq_bigr. intros (i&Hlt) _ => /=.
    case: ifP => Hlt'. 
    - rewrite ?Max.max_r => //=; nify; omega.
    - apply negbT in Hlt'. rewrite -leqNgt in Hlt'. 
      rewrite ?Max.max_l => //=; nify; omega.
  }    
  rewrite big_split //=. f_equal.
  apply uphalf_sum_half.
Qed.

Lemma max_triangular_sum n : \sum_(0 <= i < n) max i (n - i - 1) = 'C(n, 2) + uphalf n * half n.
Proof.
  elim: n => [|n IHn]; first by rewrite big_geq. 
  rewrite big_nat_recr //= binS bin1 Max.max_l; last by (nify; omega). 
  rewrite uphalf_sum_max IHn. ring. 
Qed.