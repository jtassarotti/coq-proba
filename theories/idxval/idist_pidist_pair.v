Require Import Reals Psatz.
From stdpp Require Import tactics.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
From discprob.basic Require Import base sval order monad bigop_ext nify.
From discprob.idxval Require Import pival_dist pival ival_dist ival ival_pair subset_coupling pidist_singleton extrema.
From discprob.prob Require Import prob countable finite stochastic_order.

Record idist_pidist_couplingP {A1 A2} (I1: ivdist A1) (I2: pidist A2) (P: A1 → A2 → Prop) : Type :=
  mkIPCoupling { elem_coupling : ivdist A2;
                 elem_member : le_pidist (singleton elem_coupling) I2;
                 elem_coupled :> ival_couplingP I1 elem_coupling P }.

Arguments elem_coupling {_ _ _ _ _} _.

Definition lsupport {A1 A2 Is1 Is2 P} (Icouple: idist_pidist_couplingP Is1 Is2 P) (y: A2) :=
  { x : A1 |  ∃ i Hpf, ival.ind Icouple i = (exist _ (x, y) Hpf) ∧ ival.val Icouple i > 0 }.
Definition rsupport {A1 A2 Is1 Is2 P} (Icouple: idist_pidist_couplingP Is1 Is2 P) (x: A1) :=
  { y : A2 |  ∃ i Hpf, ival.ind Icouple i = (exist _ (x, y) Hpf) ∧ ival.val Icouple i > 0 }.
                 
Lemma ip_subset_singleton {A1 A2} (I1 : ivdist A1) (Is2: pidist A2) P:
  (∃ ic : idist_pidist_couplingP I1 Is2 P, True) ↔ subset_couplingP (singleton I1) Is2 P.
Proof.
  split.
  - intros ([I2 Imem Icouple]&_).
    apply In_pidist_le_singleton in Imem; rewrite /In_pidist in Imem.
    destruct Imem as (I2'&?&?).
    intros I Hin. rewrite /In/singleton//= in Hin.
    subst; exists I2'; split; auto.
    eexists; eauto.
    eapply ival_coupling_proper; eauto.
  - intros Hsub. destruct (Hsub I1) as (I2&Hin&Hcouple&_); first by done.
    eexists; auto.
    exists (lift_In_pidist I2 Hin); auto.
    apply In_pidist_le_singleton. rewrite /In_pidist.
    exists I2; split; auto.
Qed.

Lemma ip_coupling_eq {A} (Is1 : ivdist A) (Is2: pidist A)
      (Ic: idist_pidist_couplingP Is1 Is2 (λ x y, x = y)): In_pidist Is1 Is2. 
Proof.
  destruct Ic as [Ic Hp1 Hp2].
  apply In_pidist_le_singleton.
  etransitivity; last by eauto.
  cut (eq_ivd Is1 Ic). 
  { intros Heq. setoid_rewrite Heq; reflexivity.  }
  by apply ival_coupling_eq.
Qed.

Lemma ip_coupling_singleton {A} (I: ivdist A) :
  idist_pidist_couplingP I (singleton I) (λ x y, x = y).
Proof.
  exists I.
  - reflexivity.
  - apply ival_coupling_refl.
Qed.

Lemma ip_coupling_mret {A1 A2} (P: A1 → A2 → Prop) x y:
  P x y →
  idist_pidist_couplingP (mret x) (mret y) P.
Proof.
  intros HP. exists (mret y).
  { setoid_rewrite singleton_mret. reflexivity. }
  by apply ival_coupling_mret.
Qed.

Lemma ip_coupling_bind {A1 A2 B1 B2} (f1: A1 → ivdist B1) (f2: A2 → pidist B2)
      Is1 Is2 P Q (Ic: idist_pidist_couplingP Is1 Is2 P):
  (∀ x y, P x y → idist_pidist_couplingP (f1 x) (f2 y) Q) →
  idist_pidist_couplingP (mbind f1 Is1) (mbind f2 Is2) Q.
Proof.
  intros Hfc.
  destruct (ip_subset_singleton ((mbind f1 Is1)) (mbind f2 Is2) Q) as (_&Hc2).
  eapply ClassicalEpsilon.constructive_indefinite_description in Hc2 as (Hc&?);
    first by exact Hc.
  eapply subset_coupling_proper. 
  { setoid_rewrite singleton_bind. reflexivity. }
  { reflexivity. }
  eapply subset_coupling_bind; intros; apply ip_subset_singleton; eauto.
Qed.

Lemma ip_coupling_conseq {A1 A2} (P1 P2: A1 → A2 → Prop) (I: ivdist A1) (Is: pidist A2):
  (∀ x y, P1 x y → P2 x y) →
  idist_pidist_couplingP I Is P1 →
  idist_pidist_couplingP I Is P2.
Proof.
  intros HP [I' ? Ic].
  exists I'; eauto.
  eapply ival_coupling_conseq; eauto.
Qed.
  

Lemma ip_coupling_proper {A1 A2} (I1 I2 : ivdist A1) (Is1 Is2: pidist A2) P:
  eq_ival I1 I2 → 
  eq_pidist Is1 Is2 → 
  idist_pidist_couplingP I1 Is1 P → 
  idist_pidist_couplingP I2 Is2 P.
Proof.
  intros Heq Heqp [Ielem ? ?].
  exists Ielem.
  - etransitivity; first eauto.
    setoid_rewrite Heqp. reflexivity.
  - eapply ival_coupling_proper; eauto.
Qed.

Lemma ip_coupling_proper' {A1 A2} (I1 I2 : ivdist A1) (Is1 Is2: pidist A2) P:
  eq_ivd I1 I2 → 
  eq_pidist Is1 Is2 → 
  idist_pidist_couplingP I1 Is1 P → 
  idist_pidist_couplingP I2 Is2 P.
Proof.
  intros Heq Heqp [Ielem ? ?].
  exists Ielem.
  - etransitivity; first eauto.
    setoid_rewrite Heqp. reflexivity.
  - eapply ival_coupling_proper; eauto.
Qed.


Lemma ip_coupling_proper_mono {A1 A2} (I1 I2 : ivdist A1) (Is1 Is2: pidist A2) P:
  eq_ivd I1 I2 → 
  le_pidist Is1 Is2 → 
  idist_pidist_couplingP I1 Is1 P → 
  idist_pidist_couplingP I2 Is2 P.
Proof.
  intros Heq Heqp [Ielem ? ?].
  exists Ielem.
  - etransitivity; first eauto.
    setoid_rewrite Heqp. reflexivity.
  - eapply ival_coupling_proper; eauto.
Qed.

Lemma ip_coupling_support {X Y} I1 I2 (P: X → Y → Prop) :
  ∀ (Ic: idist_pidist_couplingP I1 I2 P),
  idist_pidist_couplingP I1 I2 (λ x y, ∃ Hpf: P x y,  In_isupport x I1 ∧ In_psupport y I2 ∧
                        In_isupport (exist _ (x, y) Hpf) Ic).
Proof.
  intros Ic.
  destruct Ic as [Ielem ? Ic].
  specialize (ival_coupling_support _ _ _ Ic) => Ic'.
  exists Ielem; auto.
  eapply ival_coupling_conseq; eauto.
  intros x y (Hpf&Hin1&Hin2&?); exists Hpf; repeat split; auto.
  eapply le_pidist_support_coerce_aux; eauto.
  apply In_psupport_alt. exists Ielem; split; done.
Qed.

Lemma ip_coupling_support_wit {X Y} I1 I2 (P: X → Y → Prop)
      (Ic: idist_pidist_couplingP I1 I2 P):
       { xy : X * Y | ∃ Hpf : P (fst xy) (snd xy),
           In_isupport (fst xy) I1 ∧ In_psupport (snd xy) I2 ∧ In_isupport (exist _ xy Hpf) Ic}.
Proof.
  destruct Ic as [Ielem ? Ic].
  specialize (ival_coupling_support_wit _ _ _ Ic) => wit.
  destruct wit as ((x&y)&Hpf).
  exists (x, y).
  destruct Hpf as (Hpf&Hin1&Hin2&Hin3).
  exists Hpf. intuition.
  eapply le_pidist_support_coerce_aux; eauto.
  apply In_psupport_alt. exists Ielem; split; done.
Qed.
  
Lemma ip_coupling_plus {A1 A2} p Hpf p' Hpf'
      (P : A1 → A2 → Prop) (Is1 Is1': ivdist A1) (Is2 Is2': pidist A2) :
  p = p' →
  idist_pidist_couplingP Is1 Is2 P →
  idist_pidist_couplingP Is1' Is2' P →
  idist_pidist_couplingP (ivdplus p Hpf Is1 Is1') (pidist_plus p' Hpf' Is2 Is2') P.
Proof.
  intros; subst.
  edestruct (ip_subset_singleton (ivdplus p' Hpf Is1 Is1')
                                 (pidist_plus p' Hpf' Is2 Is2')) as (?&Hc2).
  eapply ClassicalEpsilon.constructive_indefinite_description in Hc2 as (Hc&?);
    first exact Hc.

  eapply subset_coupling_proper. 
  { setoid_rewrite singleton_plus. reflexivity. }
  { reflexivity. }
  eapply subset_coupling_plus; eauto; apply ip_subset_singleton; eexists; eauto.
Qed.

Lemma ip_coupling_union_l {A1 A2} I Is Is' (P: A1 → A2 → Prop):
  idist_pidist_couplingP I Is P →
  idist_pidist_couplingP I (pidist_union Is Is') P.
Proof.
  intros [Iwit ? Ic].
  exists Iwit; eauto.
  by apply pidist_union_le_l.
Qed.
  
Lemma ip_coupling_union_r {A1 A2} I Is Is' (P: A1 → A2 → Prop):
  idist_pidist_couplingP I Is' P →
  idist_pidist_couplingP I (pidist_union Is Is') P.
Proof.
  intros [Iwit ? Ic].
  exists Iwit; eauto.
  by apply pidist_union_le_r.
Qed.

Lemma indef_disj (P1 P2: Prop): P1 ∨ P2 → {P1} + {P2}.
Proof.
    { intros Hcase.
      assert (∃ b, if (b: bool) then P1 else P2) as Hb.
      { destruct Hcase; [ exists true | exists false ]; eauto.  }
      eapply ClassicalEpsilon.constructive_indefinite_description in Hb.
      destruct Hb as ([|]&HP'); eauto.
    }
Qed.

Lemma ip_coupling_union_list {A1 A2} I Is Ishd Iss (P: A1 → A2 → Prop):
  idist_pidist_couplingP I Is P →
  (∃ Is', eq_pidist Is Is' ∧ List.In Is' (Ishd :: Iss)) →
  idist_pidist_couplingP I (fold_left pidist_union Iss Ishd) P.
Proof.
  revert Ishd Is.
  induction Iss as [| Ishd' Iss] => Ishd Is.
  - intros Ic Hin. rewrite //=.
    apply ClassicalEpsilon.constructive_indefinite_description in Hin.
    destruct Hin as (Is'&Hequiv&Hin).
    assert (Is' = Ishd).
    { destruct Hin as [|[]]; done. }
    subst. eapply ip_coupling_proper; eauto.
  - intros Ic Hin. rewrite //=. 
    rewrite //= in Hin.
    apply ClassicalEpsilon.constructive_indefinite_description in Hin.
    destruct Hin as (Is'&Hequiv&Hin).
    apply indef_disj in Hin as [Heq1|Htl].
    { subst. eapply IHIss.
      ** apply ip_coupling_union_l.  eauto.
      ** eexists; split; last by (left; eauto).
         setoid_rewrite Hequiv; reflexivity.
    }
    apply indef_disj in Htl as [Heq2|Htl].
    { subst. eapply IHIss.
      ** apply ip_coupling_union_r.  eauto.
      ** eexists; split; last by (left; eauto).
         setoid_rewrite Hequiv; reflexivity.
    }
    eapply IHIss; eauto.
    exists Is'; split; eauto.
    right. done.
Qed.

(* TODO: strengthen these to be bounded_fun_on as is done for the irrel couplings to match the presentation in the text *)
Lemma idist_coupling_eq_ex_Ex {A1 A2} f g (I: ivdist A1) (Is: pidist A2) :
  idist_pidist_couplingP I Is (λ x y, f x = g y) →
  bounded_fun g →
  ex_Ex_ival f I.
Proof.
  intros.
  assert (idist_pidist_couplingP (x ← I; mret (f x))
                                 (x ← Is; mret (g x))
                                 (λ x y, x = y)) as Ic'.
  { eapply ip_coupling_bind; eauto => ???.
    apply ip_coupling_mret; auto. }
                                    
  destruct Ic' as [I2 Hmem Ic'].
  apply ival_coupling_eq in Ic'.
  rewrite (ex_Ex_ival_fmap id f).
  setoid_rewrite Ic'.
  cut (ex_Ex_extrema id (x ← Is; mret (g x))).
  { intros Hex'. edestruct (Hmem I2) as (I2'&Heq'&?); first done.
    rewrite Heq'. eapply Hex'; eauto. }
  rewrite -ex_Ex_extrema_fmap. eauto.
  eapply ex_Ex_extrema_bounded_fun.
  eauto.
Qed.

Lemma idist_coupling_eq_Ex_min {A1 A2} f g (I: ivdist A1) (Is: pidist A2) :
  idist_pidist_couplingP I Is (λ x y, f x = g y) →
  bounded_fun g →
  Rbar_le (Ex_min g Is) (Ex_ival f I).
Proof.
  intros Hirrel Hb.
  feed pose proof (idist_coupling_eq_ex_Ex f g I Is) as Hex; eauto.
  assert (idist_pidist_couplingP (x ← I; mret (f x))
                                 (x ← Is; mret (g x))
                                 (λ x y, x = y)) as Ic'.
  { eapply ip_coupling_bind; eauto => ???.
    apply ip_coupling_mret; auto. }
                                    
  destruct Ic' as [I2 Hmem Ic'].
  apply ival_coupling_eq in Ic'.
  transitivity (Ex_min (λ x, id (g x)) Is); first reflexivity.
  rewrite (Ex_min_comp g id).
  - transitivity (Ex_ival (λ x, Ex_ival id (mret (f x))) I); last first.
    { apply Ex_ival_mono.
      * intros. rewrite Ex_ival_mret. reflexivity.
      * setoid_rewrite Ex_ival_mret; eauto.
      * eauto.
    }
    rewrite -Ex_ival_bind_post; last first.
    { rewrite -ex_Ex_ival_fmap. eauto. }
    transitivity (Ex_ival id I2); last first.
    { refl_right. f_equal. symmetry. eapply Ex_ival_proper; eauto.
      rewrite -ex_Ex_ival_fmap. eauto. }
    
    apply In_pidist_le_singleton in Hmem.
    destruct Hmem as (I2'&Heq22'&?).
    transitivity (Ex_ival id I2'); last first.
    { refl_right. f_equal. symmetry. eapply Ex_ival_proper; eauto.
      eapply ex_Ex_ival_proper; eauto.
      rewrite -ex_Ex_ival_fmap. eauto. }
    apply Ex_min_spec1'; auto.
    eapply ex_Ex_ival_proper; eauto.
    eapply ex_Ex_ival_proper; eauto.
    rewrite -ex_Ex_ival_fmap. eauto.
  - apply Ex_min_bounded_fun_finite; eauto.
  - apply ex_Ex_extrema_bounded_fun; eauto.
Qed.