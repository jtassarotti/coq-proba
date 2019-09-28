From mathcomp Require Import ssreflect seq ssrbool eqtype.
From stdpp Require Import gmap pmap.
From discprob.basic Require Import seq_ext.

Lemma list_fmap_map {X Y} (f: X → Y) (l: list X):
  f <$> l = map f l.
Proof. rewrite //=. Qed.

Lemma NoDup_uniq {X: eqType} (l: list X):
  NoDup l ↔ seq.uniq l.
Proof.
  split.
  - induction 1 => //=.
    * apply /andP; split.
      ** apply /negP => Hin.
         rewrite mem_seq_legacy -elem_of_list_In in Hin *. 
         done.
      ** auto.
  - induction l => //=.
    * intros; econstructor.
    * move /andP. intros (Hnin&Huniq).
      econstructor; last by eauto.
      rewrite elem_of_list_In -mem_seq_legacy. move /negP in Hnin.
      auto.
Qed.