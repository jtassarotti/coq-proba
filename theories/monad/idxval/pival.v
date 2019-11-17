(* Indexed Valuations from Varacca-Wynskel *)
From discprob.basic Require Import base sval order monad.
Require Import Reals Psatz.

Require ClassicalEpsilon.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
Global Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.
From discprob.monad.idxval Require Import ival.

(* Lifting to powersets for non-determinism *)
Hint Extern 0 (eq_ival _ _) => reflexivity.
Record pival (X: Type) := { choices :> ival X → Prop; nonempty : ∃ I, choices I }.
Arguments choices {_} _.
Arguments nonempty {_} _.

Definition In_psupport {X: Type} (x: X) (Is : pival X) :=
  ∃ I i, Is I ∧ ind I i = x ∧ val I i > 0.
Definition psupport {X : Type} (Is: pival X) :=
  { x: X | In_psupport x Is }.

Notation ISet := (λ X, ival X → Prop).


Definition pplus_aux {X} (Is1 Is2: ISet X) :=
  λ I', ∃ I1 I2, Is1 I1 ∧ Is2 I2 ∧ I' = (iplus I1 I2).

(*
Definition In {X} (I: ival X) (Is: ISet X) := Is I.
*)
Definition In {X} (x: X) (I: X → Prop) := I x.

Lemma pplus_aux_in {X} I1 I2 (Is1 Is2: ISet X) :
  In I1 Is1 → In I2 Is2 → In  (iplus I1 I2) (pplus_aux Is1 Is2).
Proof.
  revert I1 I2 Is2.
  intros. exists I1, I2; repeat split; auto.
Qed.

Definition pplus {X} (Is1 Is2: pival X) : pival X.
  refine {| choices := pplus_aux Is1 Is2; nonempty := _ |}.
  abstract (destruct Is1 as (?&(I1&Hin1)); destruct Is2 as (?&(I2&Hin2));
            exists (iplus I1 I2); apply pplus_aux_in; done).
Defined.

Lemma pplus_in {X} I1 I2 (Is1 Is2: pival X):
  In I1 Is1 → In I2 Is2 → In (iplus I1 I2) (pplus Is1 Is2).
Proof. apply pplus_aux_in. Qed.

Lemma pplus_in_inv {X} (Is1 Is2: pival X):
  ∀ I, In I (pplus Is1 Is2) → ∃ I1 I2, In I1 Is1 ∧ In I2 Is2 ∧ eq_ival I (iplus I1 I2).
Proof. intros I; rewrite /In //= /pplus_aux. intros (?&?&?&?&->). do 2 eexists; eauto. Qed.

Definition pscale_aux {X} (p: R) (Is: ISet X) : ISet X :=
  λ I, ∃ I', In I' Is ∧ I = (iscale p I').

Definition pscale {X} (p: R) (Is: pival X) : pival X.
  refine {| choices := pscale_aux p Is; nonempty := _ |}.
  abstract (destruct Is as (Is&(I&Hin)); exists (iscale p I); rewrite //=; exists I;
            split; auto; reflexivity).
Defined.

Lemma pscale_in {X} p I (Is: pival X):
  In I Is → In (iscale p I) (pscale p Is).
Proof. intros Hin. exists I; split; auto; reflexivity. Qed.

Lemma pscale_in_inv {X} p (Is: pival X):
  ∀ I, In I (pscale p Is) → ∃ I', In I' Is ∧ eq_ival I (iscale p I').
Proof. intros I; rewrite /pscale/pscale_aux//=. intros (?&?&->). eexists; eauto. Qed.

Definition punion {X} (Is1 Is2: pival X) : pival X.
  refine {| choices := λ I, Is1 I ∨ Is2 I; nonempty := _ |}.
  abstract (destruct Is1 as (?&(I1&Hin1)); destruct Is2 as (?&(I2&Hin2));
            exists (I1); left; auto).
Defined.

Lemma punion_in_inv {A} (I: ival A) (m1 m2: pival A):
  In I (punion m1 m2) → (In I m1 ∨ In I m2).
Proof. rewrite //=. Qed.

Lemma punion_in_l {A} (I: ival A) (m1 m2: pival A):
  In I m1 → In I (punion m1 m2).
Proof. rewrite //= => ?; by left. Qed.

Lemma punion_in_r {A} (I: ival A) (m1 m2: pival A):
  In I m2 → In I (punion m1 m2).
Proof. rewrite //= => ?; by right. Qed.

(* The intuition for this ordering is that Is1 <= Is2 if every distribution in Is1
   is also in Is2 *)
Definition le_pival {X} (Is1 Is2: pival X) :=
  (∀ I, In I Is1 → ∃ I', eq_ival I I' ∧ In I' Is2).

Lemma le_pival_refl {X} (Is: pival X) : le_pival Is Is.
Proof. intros I Hin; exists I; split; auto; reflexivity. Qed.

Lemma le_pival_trans {X} (Is1 Is2 Is3: pival X) :
  le_pival Is1 Is2 →
  le_pival Is2 Is3 →
  le_pival Is1 Is3.
Proof.
  intros Hs12a Hs23a.
  intros I Hin.
  edestruct (Hs12a I Hin) as (I'&Heq'&Hin').
  edestruct (Hs23a I' Hin') as (I''&Heq''&Hin'').
  exists I''; split; auto; etransitivity; eauto.
Qed.

Definition eq_pival {X} (Is1 Is2: pival X) :=
  le_pival Is1 Is2 ∧ le_pival Is2 Is1.

Lemma eq_pival_refl {X} (Is: pival X) : eq_pival Is Is.
Proof.
  split => I Hin; eapply le_pival_refl; eauto.
Qed.

Lemma eq_pival_sym {X} (Is1 Is2: pival X) : eq_pival Is1 Is2 → eq_pival Is2 Is1.
Proof.
  intros (?&?); split; auto.
Qed.

Lemma eq_pival_trans {X} (Is1 Is2 Is3: pival X) :
  eq_pival Is1 Is2 →
  eq_pival Is2 Is3 →
  eq_pival Is1 Is3.
Proof.
  intros (Hs12a&Hs12b) (Hs23a&Hs23b); split.
  - eapply le_pival_trans; eauto.
  - eapply le_pival_trans; eauto.
Qed.

Definition zero_pival {X: Type} : pival X.
  refine {| choices := (λ I, I = (@zero_ival X)); nonempty := _ |}.
  abstract (exists zero_ival; reflexivity).
Defined.

Section pival_props.
Variable (X: Type).
Implicit Types I: ival X.
Implicit Types Is: pival X.

Lemma pplus_le_pival Is1 Is1' Is2 Is2':
  le_pival Is1 Is1' →
  le_pival Is2 Is2' →
  le_pival (pplus Is1 Is2) (pplus Is1' Is2').
Proof.
  intros Hs1 Hs2 I Hin.
  apply pplus_in_inv in Hin as (I1&I2&Hin1&Hin2&Heq).
  subst.
  edestruct (Hs1 I1 Hin1) as (I1'&Heq1&?).
  edestruct (Hs2 I2 Hin2) as (I2'&Heq2&?).
  exists (iplus I1' I2').
  split.
  * setoid_rewrite <-Heq1. setoid_rewrite <-Heq2. done.
  * apply pplus_in; auto.
Qed.

Lemma pplus_eq_pival Is1 Is1' Is2 Is2':
  eq_pival Is1 Is1' →
  eq_pival Is2 Is2' →
  eq_pival (pplus Is1 Is2) (pplus Is1' Is2').
Proof.
  intros (Hs1a&Hs1b).
  intros (Hs2a&Hs2b).
  split; eauto using pplus_le_pival.
Qed.

Lemma pscale_0_l Is:
  eq_pival (pscale 0 Is) zero_pival.
Proof.
  split; rewrite /le_pival.
  - destruct Is as (Is&Hpf) => //=. clear Hpf.
    intros I [I' [Hin Heq]].
    subst. exists (zero_ival); split; auto. apply iscale_0_l.
    rewrite /In. reflexivity.
  - rewrite /In/zero_pival//=. intros I Heql; subst.
    destruct Is as (Is&(I'&Hin)).
    exists (iscale 0 I'); split; auto.
    * by rewrite iscale_0_l.
    * eexists; split; eauto.
Qed.

Lemma pscale_le_pival p Is Is':
  le_pival Is Is' →
  le_pival (pscale p Is) (pscale p Is').
Proof.
  intros Hs1.
  intros ? (I&Hin&Heq)%pscale_in_inv; subst.
  edestruct (Hs1 _ Hin) as (I'&Heq'&Hin').
  exists (iscale p I'); split.
  * setoid_rewrite Heq. setoid_rewrite Heq'. reflexivity.
  * by apply pscale_in.
Qed.

Lemma pscale_eq_pival p Is Is':
  eq_pival Is Is' →
  eq_pival (pscale p Is) (pscale p Is').
Proof.
  intros (Hs1&Hs2).
  split; eauto using pscale_le_pival.
Qed.

Lemma punion_le_pival Is1 Is1' Is2 Is2':
  le_pival Is1 Is1' →
  le_pival Is2 Is2' →
  le_pival (punion Is1 Is2) (punion Is1' Is2').
Proof.
  intros Hs1 Hs2 I Hin.
  apply punion_in_inv in Hin as [Hin|Hin].
  * edestruct Hs1 as (I'&Heq&Hin'); eauto.
    exists I'; split; auto. apply punion_in_l; done.
  * edestruct Hs2 as (I'&Heq&Hin'); eauto.
    exists I'; split; auto. apply punion_in_r; done.
Qed.

Lemma punion_eq_pival Is1 Is1' Is2 Is2':
  eq_pival Is1 Is1' →
  eq_pival Is2 Is2' →
  eq_pival (punion Is1 Is2) (punion Is1' Is2').
Proof.
  intros (Hs1a&Hs1b).
  intros (Hs2a&Hs2b).
  split; eauto using punion_le_pival.
Qed.

Global Instance eq_pival_Transitivite {Y}: Transitive (@eq_pival Y).
Proof. intros ???. apply eq_pival_trans. Qed.
Global Instance eq_pival_Reflexive {Y}: Reflexive (@eq_pival Y).
Proof. intros ?. apply eq_pival_refl. Qed.
Global Instance eq_pival_Symmetry {Y}: Symmetric (@eq_pival Y).
Proof. intros ??. apply eq_pival_sym. Qed.

Global Instance le_pival_Transitivite {Y}: Transitive (@le_pival Y).
Proof. intros ???. apply le_pival_trans. Qed.
Global Instance le_pival_Reflexive {Y}: Reflexive (@le_pival Y).
Proof. intros ?. apply le_pival_refl. Qed.

Global Instance le_pival_proper {Y}: Proper (@eq_pival Y ==> @eq_pival Y ==> iff) (@le_pival Y).
Proof.
  intros Is1 Is1' Heq1 Is2 Is2' Heq2; split => Hle;
  destruct Heq1 as (Hle1&Hle1'); destruct Heq2 as (Hle2&Hle2').
  -  etransitivity; first eauto. etransitivity; first eauto.
     done.
  -  etransitivity; first eauto. etransitivity; first eauto.
     done.
Qed.

Global Instance pplus_mono : Proper (@le_pival X ==> @le_pival X ==> @le_pival X) (@pplus X).
Proof. intros ?? ? ?? ?. apply @pplus_le_pival; auto. Qed.

Global Instance pplus_proper : Proper (@eq_pival X ==> @eq_pival X ==> @eq_pival X) (@pplus X).
Proof. intros ?? ? ?? ?. apply @pplus_eq_pival; auto. Qed.

Global Instance pscale_mono : Proper (eq ==> @le_pival X ==> @le_pival X) (@pscale X).
Proof. intros ?? ? ?? ?; subst. apply @pscale_le_pival; auto. Qed.

Global Instance pscale_proper : Proper (eq ==> @eq_pival X ==> @eq_pival X) (@pscale X).
Proof. intros ?? ? ?? ?; subst. apply @pscale_eq_pival; auto. Qed.

Global Instance punion_mono : Proper (@le_pival X ==> @le_pival X ==> @le_pival X) (@punion X).
Proof. intros ?? ? ?? ?. apply @punion_le_pival; auto. Qed.

Global Instance punion_proper : Proper (@eq_pival X ==> @eq_pival X ==> @eq_pival X) (@punion X).
Proof. intros ?? ? ?? ?. apply @punion_eq_pival; auto. Qed.

Lemma pplus_comm Is1 Is2: eq_pival (pplus Is1 Is2) (pplus Is2 Is1).
Proof.
  split.
  - intros I (I1&I2&?&?&Heq)%pplus_in_inv.
    subst. exists (iplus I2 I1); split; first by (setoid_rewrite Heq; apply iplus_comm).
    apply pplus_in; eauto.
  - intros I (I1&I2&?&?&Heq)%pplus_in_inv.
    subst. exists (iplus I2 I1); split; first by (setoid_rewrite Heq; apply iplus_comm).
    apply pplus_in; eauto.
Qed.

Lemma pplus_assoc Is1 Is2 Is3: eq_pival (pplus Is1 (pplus Is2 Is3)) (pplus (pplus Is1 Is2) Is3).
Proof.
  split.
  - intros I (I1&?&Hin1&Hin'&Heq)%pplus_in_inv.
    apply pplus_in_inv in Hin' as (I2&I3&?&?&Heq'); subst.
    exists (iplus (iplus I1 I2) I3); split.
    rewrite Heq Heq'; first by apply iplus_assoc.
    apply pplus_in; eauto.
    apply pplus_in; eauto.
  - intros I (?&I3&Hin'&Hin3&Heq)%pplus_in_inv.
    apply pplus_in_inv in Hin' as (I1&I2&?&?&Heq'); subst.
    exists (iplus I1 (iplus I2 I3)); split.
    rewrite Heq Heq'; first by apply eq_ival_sym, iplus_assoc.
    apply pplus_in; eauto.
    apply pplus_in; eauto.
Qed.

Lemma pplus_0 Is: eq_pival (pplus Is zero_pival) Is.
Proof.
  split.
  - intros I (I1&I2&?&Hin2&Heq)%pplus_in_inv.
    rewrite /In/zero_pival//= in Hin2.
    exists I1; split; auto; rewrite ?Heq Hin2; first by apply iplus_0.
  - intros I Hin. exists (iplus I zero_ival); split.
    * setoid_rewrite iplus_0. reflexivity.
    * apply pplus_in; auto => //=.
Qed.

Lemma pscale_0 Is: eq_pival (pscale 0 Is) zero_pival.
Proof.
  split.
  - intros I (I'&Hin&Heq)%pscale_in_inv.
    subst. exists zero_ival.  rewrite Heq iscale_0_l //.
  - intros I Hin. destruct Is as (Is&(I'&Hin')). exists (iscale 0 I'); split.
    * setoid_rewrite iscale_0_l. inversion Hin. subst; reflexivity.
    * apply pscale_in; auto.
Qed.

Lemma pscale_1 Is: eq_pival (pscale 1 Is) Is.
Proof.
  split.
  - intros I (I'&Hin&Heq)%pscale_in_inv.
    subst. exists I'; split; auto. rewrite Heq iscale_1 //; reflexivity.
  - intros I Hin. exists (iscale 1 I); split.
    * setoid_rewrite iscale_1.  reflexivity.
    * apply pscale_in; auto.
Qed.

Lemma pscale_distrib p Is1 Is2:
  eq_pival (pscale p (pplus Is1 Is2)) (pplus (pscale p Is1) (pscale p Is2)).
Proof.
  split.
  - intros I (I'&Hin&Heq)%pscale_in_inv.
    subst. apply pplus_in_inv in Hin as (I1&I2&?&?&Heq_plus); subst.
    exists (iplus (iscale p I1) (iscale p I2)); split.
    * rewrite Heq -iscale_distrib Heq_plus //.
    * apply pplus_in; apply pscale_in; done.
  - intros I (I1'&I2'&Hin1&Hin2&Heq)%pplus_in_inv.
    subst.
    apply pscale_in_inv in Hin1 as (I1&?&Heq1); subst.
    apply pscale_in_inv in Hin2 as (I2&?&Heq2); subst.
    exists (iscale p (iplus I1 I2)); split.
    * rewrite iscale_distrib Heq Heq1 Heq2 //.
    * apply pscale_in; apply pplus_in; done.
Qed.

Lemma pscale_assoc p q Is:
  eq_pival (pscale p (pscale q Is)) (pscale (p * q) Is).
Proof.
  split.
  - intros I (?&(I'&?&->)%pscale_in_inv&Heq)%pscale_in_inv; subst.
    exists (iscale (p * q) I'); split.
    * by rewrite -iscale_assoc Heq.
    * apply pscale_in; done.
  - intros I (I'&?&?)%pscale_in_inv; subst.
    exists (iscale p (iscale q I')); split; first (by rewrite iscale_assoc).
    do 2 apply pscale_in; done.
Qed.

Lemma punion_comm Is1 Is2: eq_pival (punion Is1 Is2) (punion Is2 Is1).
Proof.
  split; (intros I [|]; exists I; split; auto; [right|left]; done).
Qed.

Lemma punion_assoc Is1 Is2 Is3: eq_pival (punion Is1 (punion Is2 Is3)) (punion (punion Is1 Is2) Is3).
Proof.
  split.
  - intros I [|[|]]; exists I; split; auto; [left;left|left;right|right]; done.
  - intros I [[|]|]; exists I; split; auto; [left|right;left|right;right]; done.
Qed.

Lemma punion_le Is Is': le_pival Is (punion Is Is').
Proof.
  intros I Hin. exists I; split; first by reflexivity.
  by apply punion_in_l.
Qed.

Lemma punion_le_l Is Is1 Is2: le_pival Is Is1 → le_pival Is (punion Is1 Is2).
Proof.
  intros Hle. setoid_rewrite Hle. apply punion_le.
Qed.

Lemma punion_le_r Is Is1 Is2: le_pival Is Is2 → le_pival Is (punion Is1 Is2).
Proof.
  intros Hle. setoid_rewrite Hle. setoid_rewrite punion_comm. apply punion_le.
Qed.

Lemma punion_le_id Is1 Is2: le_pival Is1 Is2 → eq_pival (punion Is1 Is2) Is2.
Proof.
  intros Hle.
  split.
  - intros I. rewrite ?in_app_iff. intros [Hin|Hin].
    * eapply Hle; done.
    * exists I; split; eauto.
  - setoid_rewrite punion_comm. apply punion_le.
Qed.

Lemma punion_idemp Is: eq_pival (punion Is Is) Is.
Proof.
  apply punion_le_id; reflexivity.
Qed.

Lemma pscale_punion_distrib p Is1 Is2:
  eq_pival (pscale p (punion Is1 Is2)) (punion (pscale p Is1) (pscale p Is2)).
Proof.
  split.
  - intros I (I'&Hin&Heq)%pscale_in_inv; subst.
    exists (iscale p I'); split => //=.
    destruct Hin as [Hin1|Hin2]; [ left; by apply pscale_in | right; by apply pscale_in ].
  - intros I. rewrite ?in_app_iff.  intros [(I'&?&?)%pscale_in_inv|(I'&?&?)%pscale_in_inv]; subst.
    * exists (iscale p I'); split => //.
      apply pscale_in; by left.
    * exists (iscale p I'); split => //.
      apply pscale_in; by right.
Qed.

Lemma pplus_punion_distrib Is Is1 Is2:
  eq_pival (pplus Is (punion Is1 Is2)) (punion (pplus Is Is1) (pplus Is Is2)).
Proof.
  split.
  - intros ? (I&I12&Hin&Hin12&Heq)%pplus_in_inv; subst.
    destruct Hin12 as [|];  eexists; (split; first by eapply Heq).
      * left. apply pplus_in; done.
      * right. apply pplus_in; done.
  - intros I. rewrite ?in_app_iff.
    intros [(Hin&Hin1&?&?&?)%pplus_in_inv|(Hin&Hin2&?&?&?)%pplus_in_inv]; subst.
    * eexists; split; first by eassumption.
      apply pplus_in; auto. left; done.
    * eexists; split; first by eassumption.
      apply pplus_in; auto. right; done.
Qed.

End pival_props.

Definition Pred (X: Type) : Type := X → Prop.
Global Instance pset_ret: MRet (@Pred) := λ A x, (λ y : A, x = y).

Definition pset_bind_aux {A B} (f: A → Pred B) (l: Pred A) :=
  λ y, ∃ x, l x ∧ (f x) y.
Global Instance pset_bind: MBind (@Pred) :=
  λ A B f l, pset_bind_aux f l.

(*
Lemma pset_right_id {A: Type} (l: Pred A):
  (mbind mret l) = l.
Proof.
  rewrite //=. rewrite /base.mbind/pset_bind/pset_bind_aux. intros y.
  induction l; auto. rewrite //=. f_equal; auto.
Qed.

Lemma pset_left_id {A B: Type} (x: A) (f: A → list B):
  (mbind f (mret x)) = f x.
Proof.
  rewrite //=. rewrite app_nil_r. done.
Qed.

Fixpoint distrib_aux {I : eqType} {X} (l: Pred I) (f: I → Pred X) :=
  λ y, ∃ x,
  match l with
  | [::] => [::]
  | [::i] =>
    x ← f i;
    mret (λ _, x)
  | i :: l =>
    x ← (f i);
    h' ← distrib_aux l f;
    mret (λ i', if i' == i then x else h' i')
  end.

Lemma distrib_aux_unfold {I : eqType} {X} i i' (l: list I) (f: I → list X) :
  distrib_aux (i :: i' :: l) f =
    x ← (f i);
    h' ← distrib_aux (i' :: l) f;
    mret (λ i', if i' == i then x else h' i').
Proof. done. Qed.

Lemma distrib_aux_nonempty {I: eqType} {X} (l: list I) (f: I → list X):
  l <> [::] →
  (∀ i, f i <> [::]) → distrib_aux l f <> [::].
Proof.
  induction l as [| i l]; first done.
  induction l as [| i' l] => _ Hnonempty.
  - rewrite //=. specialize (Hnonempty i). destruct (f i) => //=.
  - rewrite distrib_aux_unfold.
    destruct (distrib_aux (i' :: l) f).
    { exfalso. apply IHl; eauto. }
    specialize (Hnonempty i); destruct (f i); first done.
    rewrite //=.
Qed.

Lemma in_map_exist {A B: Type} (f: A → B) l:
  (∃ x, In x l) → ∃ x, In x (map f l).
Proof.
  intros (x&Hin). exists (f x). apply in_map. done.
Qed.
*)


Lemma val_prod {X Y} (I1: ival X) (I2: ival Y) i1 i2:
  val I1 i1 * val I2 i2 >= 0.
Proof.
  specialize (val_nonneg I1 i1).
  specialize (val_nonneg I2 i2); intros; nra.
Qed.

Definition distrib_aux {X} (Ip : ival (pival X)) : (ival X) → Prop :=
  λ I, (∃ h : idx Ip → ival X, (∀ i, val Ip i > 0 → In (h i) (ind Ip i)) ∧
                               eq_ival I {| idx := [countType of {i : idx Ip & idx (h i)}];
                                            ind := λ i, ind (h (projT1 i)) (projT2 i);
                                            val := λ i, val Ip (projT1 i)
                                                        * val (h (projT1 i)) (projT2 i);
                                            val_nonneg := λ i, val_prod _ _ (projT1 i) (projT2 i) |}).


Lemma distrib_aux_nonempty {X} (Ip: ival (pival X)) : (∃ I, In I (distrib_aux Ip)).
Proof.
  assert (∃ h : idx Ip → ival X, (∀ i, val Ip i > 0 → In (h i) (ind Ip i))) as (h&Hspec).
  {
    unshelve (eexists).
    { intros i. set (Is := ind Ip i).
      generalize (nonempty Is) => H.
      apply ClassicalEpsilon.constructive_indefinite_description in H
        as (I&Hin). exact I.
    }
    intros i Hgt0. rewrite //=.
    destruct ClassicalEpsilon.constructive_indefinite_description; eauto.
  }
  unshelve (eexists).
  {
    refine {| idx := [countType of {i : idx Ip & idx (h i)}];
              ind := λ i, ind (h (projT1 i)) (projT2 i);
                     val := λ i, val Ip (projT1 i)
                                 * val (h (projT1 i)) (projT2 i);
                     val_nonneg := _ |}.
    * intros (?&?); apply val_prod.
  }
  rewrite //=. rewrite /distrib_aux/In. exists h.
  split; auto using eq_ival_quasi_refl.
Qed.

Definition distrib {X} (Ip : ival (pival X)) : pival X :=
  {| choices := distrib_aux Ip; nonempty := distrib_aux_nonempty Ip|}.

Lemma extension_support {I} {X} (h: I → ival X) (ind0: I → pival X) val0:
  (∀ i, val0 i > 0 → In (h i) (ind0 i)) →
  ∃ h', (∀ i, val0 i > 0 → h i = h' i) ∧
        (∀ i, In (h' i) (ind0 i)).
Proof.
  intros Hin.
  evar (h': I → ival X).
  Unshelve. all: swap 1 2.
  {
    intros i.
    destruct (Rgt_dec (val0 i) 0).
    -  exact (h i).
    - destruct (ind0 i) as (l&Hne).
      apply ClassicalEpsilon.constructive_indefinite_description in Hne as (I'&?).
      exact I'.
  }
  exists h'.
  split.
  -  intros. rewrite /h'. destruct Rgt_dec; auto. exfalso; auto.
  -  intros. rewrite /h'. destruct Rgt_dec; auto.
     destruct (ind0 i) as (choices&Hne).
     destruct ClassicalEpsilon.constructive_indefinite_description => //=.
Qed.

Lemma match_sumbool {A} (Hcase: {A} + {¬ A}) B (Hpf: A) (f: A → B) (f': (¬ A)→ B):
  (∀ x y : A, f x = f y) →
    match Hcase with
    | left Hl => (f Hl)
    | right Hr => (f' Hr)
    end = f Hpf.
Proof.
  intros Hunicity.
  destruct Hcase; eauto.
  f_equal. done.
Qed.

Global Instance pival_ret: MRet pival.
refine (λ A x, {| choices := λ I,
                  I = {| idx := [finType of unit]; ind := (λ _, x); val := (λ _, 1);
                  val_nonneg := _ |};
                  nonempty := _ |}).
Unshelve.
all: swap 1 2.
{ abstract (intros; nra). }
abstract (eexists; reflexivity).
Defined.

Definition pival_fmap_aux {A B: Type} (f: A → B) (Is: ival A → Prop) : ival B → Prop :=
  λ Ib, ∃ Ia, In Ia Is ∧ eq_ival Ib (a ← Ia; mret (f a)).

Global Instance pival_fmap: FMap pival.
refine (λ A B f Is,
        {| choices := pival_fmap_aux f Is;
           nonempty := _ |}).
abstract (destruct Is as (Is&(Iv0&Hpf));
          eexists; rewrite /pival_fmap_aux; exists Iv0; split => //=).
Defined.

(*
Global Instance pival_mjoin: MJoin pival.
refine (λ A Iss,
        {| choices := concat (map (λ x, choices (distrib x)) (choices Iss));
           nonempty := _ |}).
abstract(destruct Iss as (Iss&?&Hne);
         destruct Iss as [|? ?]; [inversion Hne|];
         rewrite map_cons; destruct (distrib i) as (Is1&I&Hne1);
         exists I; rewrite concat_cons; apply in_or_app; left; done).
Defined.
*)


Global Instance pival_mbind : MBind pival.
refine (λ A B f Iss,
        {| choices := λ I, ∃ I0, In I0 Iss ∧ In I (distrib (a ← I0; mret (f a))) ;
           nonempty := _ |}).
abstract (destruct Iss as (Iss&I0&Hin);
          case_eq (distrib (a ← I0; mret (f a))) => ? [I Hin'] Heq;
          exists I; exists I0; split => //; rewrite Heq => //=).
Defined.

Lemma pival_mbind_in {X Y} (Is: pival X) (f: X → pival Y):
  ∀ Ix (h: idx Ix → ival Y),
    In Ix Is →
    (∀ i, val Ix i > 0 → In (h i) (f (ind Ix i))) →
    ∃ Ib Hpf, eq_ival {| idx := [countType of {i : idx Ix & idx (h i)}];
                     ind := λ i, ind (h (projT1 i)) (projT2 i);
                     val := λ i, val Ix (projT1 i) * (val (h (projT1 i)) (projT2 i));
                     val_nonneg := Hpf |}
                  Ib ∧
          In Ib (@mbind pival _ _ _ f Is).
Proof.
  destruct Is as [Is Hne].
  intros Ix h Hin Hin2.
  eexists. unshelve eexists.
  { intros (?&?); eapply val_prod. }
  split; first by reflexivity.
  rewrite /In/distrib//=. eexists; split; eauto. rewrite /distrib_aux/In => //=.
  set (h' :=(λ i: [countType of {_ : idx Ix & unit }], h (projT1 i))).
  exists h'.
  rewrite /h'.
  split.
  - intros (?&[]) => //=. rewrite Rmult_1_r. rewrite /h' => //=. apply Hin2.
  - apply eq_ival_nondep_suffice.
    * exists (λ x, match x with
                   | existT x ih => @existT _ (λ i, idx (h (projT1 i)))
                                           (@existT _ (λ i, unit) x tt) ih
                  end).
      exists (λ x, match x with
                   | existT (existT x _) ih => @existT _ (λ i, idx (h i)) x ih
                  end).
      repeat split => //=.
      ** intros (?&?) => //=. nra.
      ** intros ((?&?)&?) => //=. nra.
      ** intros (?&?) => //=.
      ** intros ((?&?)&?) => //= ?.
         destruct u. done.
      ** intros (?&?) => //=.
      ** intros (?&?) => //=.  nra.
Qed.

Lemma pival_mbind_in_alt {X Y} (Is: pival X) (f: X → pival Y):
  ∀ Ix (h: idx Ix → ival Y),
    In Ix Is →
    (∀ i, val Ix i > 0 → ∃ I', eq_ival (h i) I' ∧ In I' (f (ind Ix i))) →
    ∃ Ib Hpf, eq_ival {| idx := [countType of {i : idx Ix & idx (h i)}];
                     ind := λ i, ind (h (projT1 i)) (projT2 i);
                     val := λ i, val Ix (projT1 i) * (val (h (projT1 i)) (projT2 i));
                     val_nonneg := Hpf |}
                  Ib ∧
          In Ib (@mbind pival _ _ _ f Is).
Proof.
  intros Ix h Hin Hin2.
  assert (∃ h' : idx Ix → ival Y, (∀ i, val Ix i > 0 → In (h' i) (f (ind Ix i))) ∧
                                  (∀ i, eq_ival (h i) (h' i))) as (h'&Hh'1&Hh'2).
  {
    eexists. Unshelve.
    all: swap 1 2.
    {
    intros i. destruct (Rgt_dec (val Ix i) 0) as [r|n].
    - specialize (Hin2 i r).
      apply ClassicalEpsilon.constructive_indefinite_description in Hin2
        as (I'&?&?). exact I'.
    - exact (h i).
    }
    split.
    - intros i Hgt.  destruct (Rgt_dec) => //=.
      destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?) => //=.
    - intros i.  destruct (Rgt_dec) => //=.
      destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?) => //=.
  }
  edestruct (pival_mbind_in Is f Ix h') as (Ib&Hpf&?&?); eauto.
  exists Ib.
  eexists. Unshelve.
  - split; eauto.  etransitivity; last eauto.
    transitivity (i ← idxOf Ix; h i); first by apply eq_ival_quasi_refl.
    transitivity (i ← idxOf Ix; h' i); last by apply eq_ival_quasi_refl.
    apply ival_bind_congr; first by reflexivity.
    eauto.
  - intros. specialize (val_nonneg Ix (projT1 i)). specialize (val_nonneg (h (projT1 i)) (projT2 i)).
    intros; nra.
Qed.

Lemma pival_mbind_in_alt2 {X Y} (Is: pival X) (f: X → pival Y):
  ∀ Ix (h: idx Ix → ival Y),
    (∃ Ix', eq_ival Ix' Ix ∧ In Ix' Is) →
    (∀ i, val Ix i > 0 → In (h i) (f (ind Ix i))) →
    ∃ Ib Hpf, eq_ival {| idx := [countType of {i : idx Ix & idx (h i)}];
                     ind := λ i, ind (h (projT1 i)) (projT2 i);
                     val := λ i, val Ix (projT1 i) * (val (h (projT1 i)) (projT2 i));
                     val_nonneg := Hpf |}
                  Ib ∧
          In Ib (@mbind pival _ _ _ f Is).
Proof.
  intros Ix h (Ix'&Heqxx'&Hin') Hin.
  apply eq_ival_nondep_option_necc in Heqxx' as (h1&h2&Hr&Hh12&Hh21&Hind&Hval).
  edestruct (pival_mbind_in Is f Ix' (λ ix', match h1 ix' with
                                                 | Some ix => h ix
                                                 | None => zero_ival
                                                 end)) as (Ib&Hpf&Heq&Hin''); auto.
  -  intros ix' Hgt.
     specialize (Hind ix' Hgt).
     specialize (Hval ix' Hgt).
     specialize (Hh12 ix' Hgt).
     rewrite //=.
     destruct (h1 ix') as [ix|].
     * rewrite //= in Hind Hval. inversion Hind as [Heq]. eapply Hin.
       nra.
     * rewrite //= in Hind.
  - exists Ib.
    assert (Hpf'': ∀ (i: {i : idx Ix & idx (h i)}),
               val Ix (projT1 i) * val (h (projT1 i)) (projT2 i) >= 0).
    { intros i.
      specialize (val_nonneg Ix (projT1 i)).
      specialize (val_nonneg (h (projT1 i)) (projT2 i)).
      nra.
    }
    exists Hpf''.
    split; auto.
    etransitivity; eauto => //=.
    transitivity (x ← idxOf Ix; h x); first apply eq_ival_quasi_refl.
    transitivity (x ← idxOf Ix; x' ← mret (Some x);
                  match x' with
                    Some x => h x
                  | None => zero_ival
                  end).
    { apply ival_bind_congr; first by reflexivity.
      intros ix. setoid_rewrite ival_left_id. reflexivity.
    }

    transitivity (x ← idxOf Ix';
                  match h1 x with
                  | Some x => h x
                  | None => zero_ival
                  end); last first.
    { eauto. }
    transitivity (ox ← (x ← idxOf Ix'; mret (h1 x));
                  match ox with
                  | Some x => h x
                  | None => zero_ival
                  end); last first.
    { setoid_rewrite ival_assoc.
      apply ival_bind_congr; first by reflexivity.
      intros ix'.
      setoid_rewrite ival_left_id. reflexivity.
    }

    setoid_rewrite <-ival_assoc.
    apply ival_bind_congr; last by (intros; reflexivity).

    eapply eq_ival_nondep_option_suffice.
    exists (λ x, match h2 (projT1 x) with
                 | Some x' => Some (existT x' tt)
                 | None => None
                 end).
    exists (λ x, match h1 (projT1 x) with
                 | Some x' => Some (existT x' tt)
                 | None => None
                 end).
    repeat split => //=.
    * intros (ix'&?).
      rewrite Rmult_1_r //= => Hgt.
      specialize (Hval _ Hgt).
      destruct (h1 ix') => //=.
      ** rewrite //= in Hval. rewrite Hval; nra.
      ** rewrite //= in Hval. nra.
    * intros (ix&[]).
      rewrite Rmult_1_r //= => Hgt.
      specialize (Hh21 ix Hgt).
      destruct (h2 ix) as [ix'|] => //=.
      rewrite Hh21 => //=.
    * intros (ix&[]).
      rewrite Rmult_1_r //= => Hgt.
      specialize (Hh12 ix Hgt).
      destruct (h1 ix) as [ix'|] => //=.
      rewrite Hh12 => //=.
    * intros (ix&[]) => //=.
      rewrite Rmult_1_r //= => Hgt.
      specialize (Hh21 ix Hgt).
      destruct (h2 ix) => //=. rewrite Hh21 //.
    * intros (ix&[]) => //=.
      rewrite Rmult_1_r //= => Hgt.
      specialize (Hr ix Hgt).
      specialize (Hh21 ix Hgt).
      destruct (h2 ix) as [ix'|] => //=.
      specialize (Hval ix'). rewrite //= in Hval. rewrite -Hval; auto.
      rewrite Hh21 //=; nra.
Qed.

Lemma pival_mbind_in_alt2_idxOf {X Y} (Is: pival X) (f: X → pival Y):
  ∀ Ix (h: idx Ix → ival Y),
    (∃ Ix', eq_ival Ix' Ix ∧ In Ix' Is) →
    (∀ i, val Ix i > 0 → In (h i) (f (ind Ix i))) →
    ∃ Ib, eq_ival (i ← idxOf Ix; h i) Ib ∧
          In Ib (@mbind pival _ _ _ f Is).
Proof.
  intros. edestruct @pival_mbind_in_alt2 as (Ib&?&?&?); eauto.
Qed.

Lemma projT1_inj_irrel {X: Type} (P: Type) (x1 x2: {x : X & P}):
  (∀ p1 p2 : P, p1 = p2) →
  projT1 x1 = projT1 x2 → x1 = x2.
Proof.
  destruct x1 as (?&?) => //=.
  destruct x2 as (?&?) => //=.
  intros Hirrel ->. f_equal. done.
Qed.

Lemma eq_dep_eq_rect1 (U U': Type) (P: U → Type) (p: U')  (Hpf: U = U') (x: P (eq_rect_r _ p Hpf)):
  Logic.EqdepFacts.eq_dep U' (λ i, P (eq_rect_r _ i Hpf)) p x
         (eq_rect _ _ (eq_rect_r _ p Hpf) _ Hpf)
         (eq_rect_r (λ x, P x) x (rew_opp_l _ Hpf (eq_rect_r _ p Hpf))).
Proof.
  destruct Hpf => //=.
Qed.

Lemma eq_dep_eq_rect_r1 (U U': Type) (P: U → Type) (p: U) (x: P p) (Hpf: U = U'):
  Logic.EqdepFacts.eq_dep U P p x
         (eq_rect_r _ (eq_rect _ _ p _ Hpf) Hpf)
         (eq_rect_r (λ x, P x) x (rew_opp_l _ Hpf p)).
Proof.
  destruct Hpf => //=.
Qed.

Lemma eq_dep_eq_rect2 (U U': finType) (P: U → Type) (p: U')  (Hpf: U = U') (x: P (eq_rect_r _ p Hpf)):
  Logic.EqdepFacts.eq_dep U' (λ i, P (eq_rect_r _ i Hpf)) p x
         (eq_rect _ _ (eq_rect_r _ p Hpf) _ Hpf)
         (eq_rect_r (λ x, P x) x (rew_opp_l _ Hpf (eq_rect_r _ p Hpf))).
Proof.
  destruct Hpf => //=.
Qed.

Lemma eq_dep_eq_rect_r2 (U U': finType) (P: U → Type) (p: U) (x: P p) (Hpf: U = U'):
  Logic.EqdepFacts.eq_dep U P p x
         (eq_rect_r _ (eq_rect _ _ p _ Hpf) Hpf)
         (eq_rect_r (λ x, P x) x (rew_opp_l _ Hpf p)).
Proof.
  destruct Hpf => //=.
Qed.

Lemma pival_mbind_in_inv {X Y} (Is: pival X) (f: X → pival Y) Ib:
  In Ib (@mbind pival _ _ _ f Is) →
  ∃ Ix h Hpf, In Ix Is ∧ (∀ i, val Ix i > 0 → In (h i) (f (ind Ix i))) ∧
              eq_ival {| idx := [countType of {i : idx Ix & idx (h i)}];
                         ind := λ i, ind (h (projT1 i)) (projT2 i);
                         val := λ i, val Ix (projT1 i) * (val (h (projT1 i)) (projT2 i));
                         val_nonneg := Hpf |} Ib.
Proof.
  destruct Is as [Is Hne] => //=. clear Hne => Hin.
  destruct Hin as (Ix&Hin&Hin_distrib).
  exists Ix. destruct Hin_distrib as (h&?Hinh&Heq).
  rewrite //= in h Hinh Heq.
  exists (λ i, h (existT i tt)).
  exists (λ i, val_prod _ _ _ _).
  repeat split; auto.
  { intros. eapply Hinh => //=. by rewrite Rmult_1_r. }
  rewrite Heq.
  apply eq_ival_nondep_suffice.
  unshelve (eexists).
  {  simpl. intros (x&s). exists (existT x tt). exact s. }
  unshelve (eexists).
  { simpl. intros ((x&[])&s). exact (existT x s). }
    repeat split; auto.
    - intros (?&?) => //=. by rewrite Rmult_1_r.
    - intros ((?&[])&?) => //=. by rewrite Rmult_1_r.
    - intros (?&?) => //=.
    - intros ((?&[])&?) => //=.
    - intros (?&?) => //=.
    - intros (?&?) => //=. by rewrite Rmult_1_r.
Qed.

Lemma pival_mbind_in_inv_idxOf {X Y} (Is: pival X) (f: X → pival Y) Ib:
  In Ib (@mbind pival _ _ _ f Is) →
  ∃ Ix h, In Ix Is ∧ (∀ i, val Ix i > 0 → In (h i) (f (ind Ix i))) ∧
              eq_ival (x ← idxOf Ix; h x) Ib.
Proof.
  intros. edestruct (pival_mbind_in_inv Is f Ib) as (Ix&Hpf&h&Hin&Hhspec&Heq); eauto.
Qed.

Lemma pival_left_id {A B: Type} (x: A) (f: A → pival B):
  eq_pival (mbind f (mret x)) (f x).
Proof.
  split.
  - intros I Hin. apply pival_mbind_in_inv in Hin as (Ix&h&?&Hin&Hin2&?).
    inversion Hin; subst.
    rewrite //= in Hin. subst. rewrite //= in Hin2.
    exists (h tt).
    split; last by (apply Hin2; nra).
    etransitivity.
    { symmetry; eauto.  }
    rewrite //=.
    apply eq_ival_nondep_suffice.
    exists (λ x, match x with
                 | existT tt y => y
                 end).
    exists (λ x, existT tt x).
    repeat split => //=.
    * intros ([]&?) => //=. nra.
    * intros; nra.
    * intros ([]&?) => //=.
    * intros ([]&?) => //=.
    * intros ([]&?) => //=.  nra.
  - intros I Hin. edestruct (pival_mbind_in (mret x) f (mret x) (λ x, I)) as (Ix&Hpf&?&?).
    * rewrite /mret/base.mret/ival_ret/pival_ret/In//=. f_equal; eapply classical_proof_irrelevance.
    * rewrite //=.
    *  exists Ix. split; auto.
       etransitivity; last eauto.
       apply eq_ival_nondep_suffice.
       ** exists (λ x, existT  tt x).
          exists (λ x, projT2 x).
          repeat split => //=.
          *** intros. nra.
          *** intros. nra.
          *** intros ([]&?) ?. rewrite //=.
          *** intros. nra.
Qed.


Lemma pival_right_id {A: Type} (m: pival A):
  eq_pival (mbind mret m) m.
Proof.
  split.
  - intros I Hin. apply pival_mbind_in_inv in Hin as (Ix&h&Hnonneg&Hin&Hin2&?).
    exists Ix. split; auto. etransitivity; first by (symmetry; eauto).
    rewrite //= in Hin2.
    apply eq_ival_nondep_option_suffice.
    unshelve (eexists).
    { intros (x&i). exact (Some x). }
    unshelve (eexists).
    {
      intros x. destruct (Rgt_dec (val Ix x) 0).
      * rewrite //=. apply Some. exists x.
        rewrite Hin2 //.
      * exact None.
    }
    repeat split => //=.
    * intros b Hgt. destruct Rgt_dec => //=.
      generalize (Hin2 b Hgt). intros Heq.
      assert (val (h b) = λ x, 1) as ->.
      { rewrite Heq. eauto.  }
      nra.
    * intros (b&i) Hgt. destruct Rgt_dec as [r|n] => //=.
      ** repeat f_equal.
         rewrite -[a in _ = a](rew_opp_l (λ x, idx x) (Hin2 b r) i).
         f_equal. destruct eq_rect => //=.
      ** rewrite //= in Hgt. specialize (val_nonneg (h b) i). nra.
    * intros b Hgt. destruct Rgt_dec => //=.
    * intros (i&x) => //=. intros.
      assert (Hgt0: val Ix i > 0).
      { abstract (specialize (val_nonneg (h i) x) => ?; nra). }
      specialize (Hin2 i Hgt0).
      assert (ind (h i) = λ _, ind Ix i) as ->.
      { rewrite Hin2. auto. }
      done.
    * intros (i&x) => //=. intros.
      assert (Hgt0: val Ix i > 0).
      { abstract (specialize (val_nonneg (h i) x) => ?; nra). }
      specialize (Hin2 i Hgt0).
      assert (val (h i) = λ _, 1) as ->.
      { rewrite Hin2. auto. }
      nra.
  - intros I Hin.
    set (h :=  λ (x: idx I), {|
                 idx := [finType of unit];
                 ind := λ _ : unit, ind I x;
                 val := λ _ : unit, 1;
                 val_nonneg := pival_ret_subproof |}).
    edestruct (pival_mbind_in m (λ x, mret x) I h) as (Ib&Hpf&Heq&?); first done.
    { rewrite /h//=. }
    exists Ib. split; auto.
    etransitivity; last eauto.
    apply eq_ival_nondep_suffice.
    exists (λ x, existT x tt).
    exists (λ x, projT1 x).
    repeat split => //=.
    * intros; nra.
    * intros (?&?); nra.
    * intros (?&[]) ?. f_equal.
    * intros; nra.
Qed.

Lemma idxOf_join {A B C} {I: ival A} {h: idx I → ival B} {I': ival B} (h': idx I' → ival C)
  (Heq: eq_ival (i ← idxOf I; h i) I'):
  (∀ x : idx I, idx (h x) → ival C).
Proof.
  apply eq_ival_nondep_option_necc in Heq.
  eapply ClassicalEpsilon.constructive_indefinite_description in Heq
    as (h1&Hrest).
  intros i ihm.
  destruct (h1 (existT i ihm)) as [ic|].
  ** exact (h' ic).
  ** exact zero_ival.
Defined.

Lemma idxOf_join_spec {A B C} {I: ival A} {h: idx I → ival B} {I': ival B} (h': idx I' → ival C)
      (Heq: eq_ival (i ← idxOf I; h i) I'):
  eq_ival (i ← idxOf I; i' ← idxOf (h i); idxOf_join h' Heq i i') (i ← idxOf I'; h' i).
Proof.
  rewrite /idxOf_join.
  destruct ClassicalEpsilon.constructive_indefinite_description
   as (h1&h2&Hrange&Hh12&Hh21&Hind&Hval).
  transitivity ((oi' ← (i ← idxOf I; i' ← idxOf (h i); mret (h1 (existT i i')));
                         match oi' with
                         | Some ic => h' ic
                         | None => zero_ival
                         end)).
  { setoid_rewrite ival_assoc.
    apply ival_bind_congr; first by reflexivity.
    intros ii.
    setoid_rewrite ival_assoc.
    apply ival_bind_congr; first by reflexivity.
    intros ihi.
    setoid_rewrite ival_left_id.
    reflexivity.
  }
  transitivity (oi ← (i ← idxOf I'; mret (Some i));
                match oi with
                | None => zero_ival
                | Some i => h' i
                end); last first.
  { setoid_rewrite ival_assoc.
    apply ival_bind_congr; first by reflexivity.
    intros ii'.
    setoid_rewrite ival_left_id.
    reflexivity.
  }
  apply ival_bind_congr; last by reflexivity.
  apply eq_ival_nondep_option_suffice.
  eexists.
  Unshelve. all: swap 1 2.
  {
    intros (ii&ih&[]).
    simpl in *.
    destruct (h1 (existT ii ih)) as [i'|].
    * exact (Some (existT i' tt)).
    * exact None.
  }
  eexists.
  Unshelve. all: swap 1 2.
  {
    intros (ii'&[]).
    simpl in *.
    destruct (h2 (ii')) as [(ii&ih)|].
    * exact (Some (existT ii (existT ih tt))).
    * exact None.
  }
  repeat split => //=.
  * intros (b&[]) => //=.
    rewrite Rmult_1_r => Hgt.
    specialize (Hrange _ Hgt).
    destruct (h2 b) as [(ii&ih)|] => //=.
    rewrite //= in Hrange. nra.
  * intros (ii&ih&[]) => //=.
    rewrite Rmult_1_r => Hgt.
    specialize (Hh12 (existT ii ih) Hgt).
    destruct (h1 _).
    ** rewrite Hh12; done.
    ** done.
  * intros (b&[]) => //=.
    rewrite Rmult_1_r => Hgt.
    specialize (Hh21 b Hgt).
    destruct (h2 _) as [(ii&ih)|] => //=; [].
    rewrite Hh21; done.
  * intros (ii&ih&[]) => //=.
    rewrite Rmult_1_r => Hgt.
    specialize (Hind (existT ii ih) Hgt).
    destruct (h1 _) => //=.
  * intros (ii&ih&[]) => //=.
    rewrite Rmult_1_r => Hgt.
    specialize (Hval (existT ii ih) Hgt).
    destruct (h1 _) => //=.
    rewrite //= in Hval. nra.
Qed.

Lemma idxOf_split1 {A B C} (Im: ival A) (f: A → pival B) (g: B → pival C) (hm: idx Im → ival C)
      (Hchoice: ∀ i, val Im i > 0 → In (hm i) ((x ← f (ind Im i); g x) : pival C)):
  idx Im → { Imf: ival B & (idx Imf → ival C) }.
Proof.
  intros im. specialize (Hchoice im).
  destruct (Rgt_dec (val Im im) 0) as [r|n].
  - specialize (Hchoice r).  apply pival_mbind_in_inv in Hchoice.
    apply ClassicalEpsilon.constructive_indefinite_description in Hchoice as (Ib&Hrest).
    apply ClassicalEpsilon.constructive_indefinite_description in Hrest as (h&Hrest).
    exists Ib. exact h.
  - exists zero_ival.
    intros [].
Defined.

Lemma pival_mbind_in_iff {X Y} (Is: pival X) (f: X → pival Y) Ib:
  (∃ Ib', eq_ival Ib Ib' ∧ In Ib' (@mbind pival _ _ _ f Is)) ↔
  ∃ Ix h, In Ix Is ∧ (∀ i, val Ix i > 0 → In (h i) (f (ind Ix i))) ∧
              eq_ival (x ← idxOf Ix; h x) Ib.
Proof.
  split.
  - intros (Ib'&Heq&Hin). edestruct (pival_mbind_in_inv_idxOf Is f Ib') as (Ix&h&?&?); eauto.
    exists Ix, h. repeat split; intuition. etransitivity; eauto. by symmetry.
  - intros (Ix&h&Hin&?&?).
    edestruct (pival_mbind_in_alt2_idxOf Is f Ix h) as (Ib'&?&?); eauto.
    exists Ib'; split; auto. etransitivity; try eassumption. by symmetry.
Qed.

Lemma pival_assoc {A B C} (m: pival A) (f: A → pival B) (g: B → pival C) :
  eq_pival (mbind g (mbind f m)) (mbind (λ x, mbind g (f x)) m).
Proof.
  split.
  - intros I Hin.
    apply pival_mbind_in_inv in Hin as (Imf&hmf&Hpf&Hin&Hchoice1&Heq1).
    apply pival_mbind_in_inv in Hin as (Im&hm&?&Hin&Hcoice2&Heq2).

    assert (eq_ival (i ← idxOf Im; hm i) Imf).
    { etransitivity; last eauto.
      rewrite //=/ival_bind//=.
      eapply eq_ival_quasi_refl.
    }
    assert (eq_ival (i ← idxOf Imf; hmf i) I).
    { etransitivity; last eauto.
      rewrite //=/ival_bind//=.
      eapply eq_ival_quasi_refl.
    }

    set (hfg := idxOf_join hmf Heq2).
    set (hmfg' := λ i, i' ← idxOf (hm i); idxOf_join hmf Heq2 i i').
    specialize (idxOf_join_spec hmf Heq2) => Heq_split.
    edestruct (pival_mbind_in_alt m (λ x, x ← f x; g x) Im hmfg') as (Ic&?&?&?); first by done.
    { intros.
      specialize (pival_mbind_in (f (ind Im i)) (λ x, g x) _ (hfg i)).
      intros Hret.
      eapply ClassicalEpsilon.constructive_indefinite_description in Hret as (Ic&?&?&?); eauto.
      intros ihm Hgt.
      rewrite /hfg/idxOf_join.
      destruct ClassicalEpsilon.constructive_indefinite_description as
          (h1&?&?&Hr&?&?Hind&Hval).
      specialize (Hind (existT i ihm)).
      specialize (Hval (existT i ihm)).
      specialize (Hr (existT i ihm)).
      case_eq (h1 (@existT _ ((λ i0 : idx Im, idx (hm (ind (idxOf Im) i0)))) i ihm)).
      * intros ? Heq.
        generalize (Hchoice1 s). rewrite //= Heq //= in Hind Hval.
        intros Hc1'.
        match type of (Hind) with
        | ?A -> ?B => cut A
        end.
        ** intros Hgt'. specialize (Hind Hgt'). inversion Hind as [Heq']. eapply Hc1'.
           rewrite Hval; nra.
        ** nra.
      * intros Hfalse. exfalso. rewrite Hfalse in Hr. apply Hr => //=.
        nra.
    }
    assert (HeqIc: eq_ival (i ← idxOf Im; hmfg' i) Ic).
    {
      etransitivity; last eauto.
      rewrite //=/ival_bind. apply eq_ival_quasi_refl.
    }
    exists Ic; split; auto.
    etransitivity; eauto.
    etransitivity; first by (symmetry; eauto).
    setoid_rewrite <-Heq_split.
    rewrite -HeqIc.
    rewrite /hmfg'. reflexivity.
  - intros I Hin.
    apply pival_mbind_in_inv in Hin as (Im&hmfg&Hpf&Hin&Hchoice1&Heq1).
    assert (eq_ival (i ← idxOf Im; hmfg i) I).
    { etransitivity; last eauto.
      rewrite //=/ival_bind//=.
      eapply eq_ival_quasi_refl.
    }

    set (hm := λ im, projT1 (idxOf_split1 Im f g hmfg Hchoice1 im)).
    set (hmf := λ im, projT2 (idxOf_split1 Im f g hmfg Hchoice1 im)).
    edestruct (pival_mbind_in m (λ x, f x) Im hm) as (Imf&Hpf'&Heq2&Hin2); auto.
    { intros. rewrite /hm/idxOf_split1.
      destruct (Rgt_dec _) => //=.
      destruct ClassicalEpsilon.constructive_indefinite_description as (Imf&?).
      destruct ClassicalEpsilon.constructive_indefinite_description as (?&?&?&?&?).
      rewrite //=.
    }
    edestruct (pival_mbind_in_alt2_idxOf (x ← m; f x) g (x ← idxOf Im; hm x)) as (I'&Heq&Hin').
    {
      Unshelve. all: swap 1 2.
      { intros (im&imh). apply (hmf im imh). }
      eexists; split; last eauto.
      symmetry; etransitivity; eauto.
    }
    { intros (im&ihm) => //=.
      move: im ihm. rewrite /hm/hmf.
      rewrite /idxOf_split1.
      intros ?? Hgt.
      destruct Rgt_dec.
      ** destruct ClassicalEpsilon.constructive_indefinite_description as (Imf'&?).
         destruct ClassicalEpsilon.constructive_indefinite_description as
             (h&?&?&Hin'&?).
         rewrite //=. rewrite //= in Hgt.
         eapply Hin'. nra.
      ** exfalso. rewrite //= in Hgt.
    }
    exists I'; split; auto.
    assert (eq_ival (x ← idxOf Im; x' ← idxOf (hm x); hmf x x') I').
    {
      etransitivity; last eauto.
      transitivity (x ← (x ← idxOf Im; x' ← idxOf (hm x); mret (existT x x'));
                    hmf (projT1 x) (projT2 x)).
      { setoid_rewrite ival_assoc.
        apply ival_bind_congr; first reflexivity.
        intros im.
        setoid_rewrite ival_assoc.
        apply ival_bind_congr; first reflexivity.
        intros ?.
        setoid_rewrite ival_left_id => //=.
      }
      eapply ival_bind_congr; last first.
      { intros (?&?) => //=. }
      clear.
      apply eq_ival_nondep_suffice.
      exists (λ x, existT (projT1 x) (projT1 (projT2 x))).
      exists (λ x, existT (projT1 x) (existT (projT2 x) tt)).
      repeat split => //=.
      - intros (?&?) => //=. nra.
      - intros (?&?) => //=. nra.
      - intros (?&(?&[])) => //=.
      - intros (?&?) => //=.
      - intros (?&(?&[])) => //=. nra.
    }
    etransitivity; last eauto.
    etransitivity; first by (symmetry; eauto).
    apply ival_bind_pos_congr; first by reflexivity.
    intros im Hdom. rewrite /hmf/hm.
    rewrite /idxOf_split1.
    destruct Rgt_dec as [|n]; last first.
    { destruct Hdom as [(im'&Hieq&Higt0)|(im'&Hieq&Higt0)];
      exfalso; subst; rewrite //= in n. }
      destruct H as (?&?). rewrite //= in H.
    destruct ClassicalEpsilon.constructive_indefinite_description as (Imf'&?).
    destruct ClassicalEpsilon.constructive_indefinite_description as (h&?&?&?&Heq').
    etransitivity; first by (symmetry; eauto).
    apply eq_ival_quasi_refl.
Qed.


(* Could be cleaned up by proving a lemma about pival equiv in the case where there's no re-ordering *)
Lemma pival_fmap_id {X} (x: pival X): eq_pival (fmap id x) x.
Proof.
  rewrite /fmap/pival_fmap.
  split; rewrite /le_pival.
  - rewrite //=. destruct x as (Is&?&?) => //=.
    clear -Is.
    inversion 1 as [? (Hin&Heq)].
    eexists; split; try apply Hin.
    rewrite Heq. apply ival_right_id.
  - rewrite //=. destruct x as (Is&?&?) => //=.
    clear -Is. intros I Hin.
    eexists; split; eauto. rewrite /In/pival_fmap_aux//=.
    eexists; split; first by eauto. symmetry. apply ival_right_id.
Qed.

Lemma pival_union_bind {A B} (m1 m2: pival A) (f: A → pival B) :
  eq_pival (x ← punion m1 m2; f x) (punion (x ← m1; f x) (x ← m2; f x)).
Proof.
  split; rewrite /le_pival.
  - intros I Hin.
    apply pival_mbind_in_inv in Hin as (Ix&h&Hpf&Hin&Hhspec&Heq).
    rewrite //= in Hin. destruct Hin as [Hin|Hin].
    * edestruct (pival_mbind_in m1 f Ix) as (I'&Hpf'&Heq'&Hin'); auto.
      eexists; split; last first.
      ** apply punion_in_l. eauto.
      ** etransitivity; last eauto.
         symmetry; etransitivity; last eauto.
         apply eq_ival_quasi_refl.
    * edestruct (pival_mbind_in m2 f Ix) as (I'&Hpf'&Heq'&Hin'); auto.
      eexists; split; last first.
      ** apply punion_in_r. eauto.
      ** etransitivity; last eauto.
         symmetry; etransitivity; last eauto.
         apply eq_ival_quasi_refl.
  - intros I [Hin|Hin]%punion_in_inv.
    * eapply pival_mbind_in_inv in Hin as (Ix&h&Hpf&Hin&Hhspec&Heq).
      edestruct (pival_mbind_in (punion m1 m2) f) as (I'&Hpf'&Heq'&Hin').
      ** apply punion_in_l. eauto.
      ** eauto.
      **  exists I'. split; auto.
          etransitivity; last eauto.
          etransitivity; first (symmetry; eauto).
          apply eq_ival_quasi_refl.
    * eapply pival_mbind_in_inv in Hin as (Ix&h&Hpf&Hin&Hhspec&Heq).
      edestruct (pival_mbind_in (punion m1 m2) f) as (I'&Hpf'&Heq'&Hin').
      ** apply punion_in_r. eauto.
      ** eauto.
      **  exists I'. split; auto.
          etransitivity; last eauto.
          etransitivity; first (symmetry; eauto).
          apply eq_ival_quasi_refl.
Qed.


Lemma pival_bind_congr_aux {A B} (m1 m2: pival A) (f1 f2: A → pival B) :
  le_pival m1 m2 →
  (∀ a, In_psupport a m1 → le_pival (f1 a) (f2 a)) →
  (∀ I : ival B, In I (choices (x ← m1; f1 x : pival B)) →
                 ∃ I' : ival B, eq_ival I I' ∧ In I' (choices (x ← m2; f2 x : pival B))).
Proof.
  intros Heqm Heqf.
  intros I Hin.
  apply pival_mbind_in_inv in Hin as (Im1&h&Hin&Hinm1&Hhspec&Heq).
  edestruct (Heqm) as (Im2&HeqIm12&Hinm2); eauto.
  symmetry in HeqIm12.
  apply eq_ival_nondep_option_necc in HeqIm12.
  destruct (HeqIm12)as (h1&h2&Hr&Hh12&Hh21&Hind&Hval).
  set (h' := λ im2,
             match h1 im2 with
             | None => zero_ival
             | Some im1 => h im1
             end).
  edestruct (pival_mbind_in_alt m2 f2 _ h') as (I'&?&?&?); eauto.
  {  intros i Hgt.  rewrite /h'.
     specialize (Hh12 _ Hgt).
     specialize (Hind _ Hgt).
     specialize (Hval _ Hgt).
     specialize (Heqf (ind Im2 i)) as Heqf1.
     destruct (h1 i) as [i'|] => //=.
     eapply Heqf1.
     { rewrite //= in Hind. exists Im1, i'. repeat split; auto.
       congruence. rewrite //= in Hval. nra. }
     rewrite //= in Hind.
     rewrite //= in Hval.
     inversion Hind.
     eapply Hhspec.
     rewrite Hval; eauto.
  }
  exists I'. split; eauto.
  etransitivity; first by (symmetry; eauto).
  etransitivity; last eauto.
  transitivity (i ← idxOf Im1; h i); first by (apply eq_ival_quasi_refl).
  transitivity (i ← idxOf Im2; h' i); last by (apply eq_ival_quasi_refl).
  transitivity (i ← (i ← idxOf Im1; mret (Some i));
                match i with
                | None => zero_ival
                | Some i => h i
                end).
  { setoid_rewrite ival_assoc. apply ival_bind_congr; first by reflexivity.
    intros a. setoid_rewrite ival_left_id; reflexivity. }
  rewrite /h'.
  transitivity (i ← (i ← idxOf Im2; mret (h1 i));
                match i with
                | None => zero_ival
                | Some i => h i
                end); last first.
  { setoid_rewrite ival_assoc.  apply ival_bind_congr; first by reflexivity.
    intros a. setoid_rewrite ival_left_id; try reflexivity. }
  apply ival_bind_congr; last by (intros [|]; reflexivity).
  symmetry.
  eapply eq_ival_nondep_option_suffice.
  exists (λ x, match h1 (projT1 x) with
               | None => None
               | Some x' => Some (existT x' tt)
               end).
  exists (λ x, match h2 (projT1 x) with
               | None => None
               | Some x' => Some (existT x' tt)
               end).
  repeat split => //=.
  *  intros (b&[]) => //=.
     specialize (Hr b).
     destruct (h2 b) => //=; rewrite //= in Hr; intros; nra.
  *  intros (b&[]) => //=.
     rewrite Rmult_1_r => Hgt.
     specialize (Hh12 _ Hgt).
     destruct (h1 b) => //=; rewrite //= in Hh12; intros; eauto.
     destruct (h2 _) => //=; rewrite //= in Hh12; intros; eauto.
     repeat f_equal. congruence.
  *  intros (b&[]) => //=.
     rewrite Rmult_1_r => Hgt.
     specialize (Hh21 _ Hgt).
     destruct (h2 _) => //=; rewrite //= in Hh21; intros; eauto.
     destruct (h1 _) => //=; rewrite //= in Hh21; intros; eauto.
     repeat f_equal. congruence.
  *  intros (b&[]) => //=.
     rewrite Rmult_1_r => Hgt.
     specialize (Hind _ Hgt).
     destruct (h1 ) => //=.
  *  intros (b&[]) => //=.
     rewrite Rmult_1_r => Hgt.
     specialize (Hval _ Hgt).
     destruct (h1 ) => //=.
     rewrite //= in Hval. nra.
Qed.

Lemma pival_bind_congr_le_supp {A B} (m1 m2: pival A) (f1 f2: A → pival B) :
  le_pival m1 m2 →
  (∀ a, In_psupport a m1 → le_pival (f1 a) (f2 a)) →
  le_pival (x ← m1; f1 x) (x ← m2; f2 x).
Proof.
  intros Hlem Hlef.
  rewrite /le_pival.
  apply pival_bind_congr_aux; eauto.
Qed.

Lemma pival_bind_congr_le {A B} (m1 m2: pival A) (f1 f2: A → pival B) :
  le_pival m1 m2 →
  (∀ a, le_pival (f1 a) (f2 a)) →
  le_pival (x ← m1; f1 x) (x ← m2; f2 x).
Proof.
  intros Hlem Hlef.
  rewrite /le_pival.
  apply pival_bind_congr_aux; eauto.
Qed.

Lemma pival_bind_congr {A B} (m1 m2: pival A) (f1 f2: A → pival B) :
  eq_pival m1 m2 →
  (∀ a, eq_pival (f1 a) (f2 a)) →
  eq_pival (x ← m1; f1 x) (x ← m2; f2 x).
Proof.
  intros Heqm Heqf; split.
  - apply pival_bind_congr_le.
    * destruct Heqm; auto.
    * intros a. destruct (Heqf a); auto.
  - apply pival_bind_congr_le.
    * destruct Heqm; auto.
    * intros a. destruct (Heqf a); auto.
Qed.

Global Instance pival_bind_mono X Y :
  Proper (pointwise_relation X (@le_pival Y) ==> @le_pival X ==> @le_pival Y) (pival_mbind X Y).
Proof. intros ?? ? ?? ?. apply @pival_bind_congr_le; auto. Qed.

Global Instance pival_bind_proper X Y :
  Proper (pointwise_relation X (@eq_pival Y) ==> @eq_pival X ==> @eq_pival Y) (pival_mbind X Y).
Proof. intros ?? ? ?? ?. apply @pival_bind_congr; auto. Qed.

Lemma pival_plus_bind {A B} (m1 m2: pival A) (f: A → pival B) :
  eq_pival (x ← pplus m1 m2; f x) (pplus (x ← m1; f x) (x ← m2; f x)).
Proof.
  split; rewrite /le_pival.
  - intros I Hin.
    apply pival_mbind_in_inv in Hin as (Ix&h&Hpf&Hin&Hhspec&Heq).
    destruct Hin as (I1&I2&Hin1&Hin2&Heqplus).
    subst.
    edestruct (pival_mbind_in m1 f I1 (λ x, h (inl x))) as (I1'&Hpf1'&Heq1'&Hin1'); auto.
    { intros i Hgt0. eapply Hhspec. rewrite //=. }
    edestruct (pival_mbind_in m2 f I2 (λ x, h (inr x))) as (I2'&Hpf2'&Heq2'&Hin2'); auto.
    { intros i Hgt0. eapply Hhspec. rewrite //=. }
    exists (iplus I1' I2'); split; auto; last first.
    { apply pplus_in; auto. }
    etransitivity; first by (symmetry; eauto).
    setoid_rewrite <-Heq1'.
    setoid_rewrite <-Heq2'.
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
  - intros I Hin.
    destruct Hin as (I1&I2&Hin1&Hin2&Heqplus).
    apply pival_mbind_in_inv in Hin1 as (Ix1&h1&Hpf1&Hin1&Hhspec1&Heq1).
    apply pival_mbind_in_inv in Hin2 as (Ix2&h2&Hpf2&Hin2&Hhspec2&Heq2).
    subst.
    edestruct (pival_mbind_in (pplus m1 m2) f (iplus Ix1 Ix2)
                              (λ x, match x with | inl x => h1 x | inr x => h2 x end))
              as (I'&Hpf'&Heq''&in'').
    { apply pplus_in; eauto. }
    { intros [i|i] => //=; eauto. }
    exists I'; split; auto.
    etransitivity; last by eauto.
    etransitivity; first (eapply iplus_proper; symmetry; eauto).
    rewrite //=.
    eexists. Unshelve. all: swap 1 2.
    { intros ([(i1&ih)|(i2&ih)]&Hgt).
      * exists (existT (inl i1) ih).
        rewrite //=.
      * exists (existT (inr i2) ih).
        rewrite //=.
    }
    eexists. Unshelve. all: swap 1 2.
    { intros (([i1|i2]&ih)&Hgt).
      * exists (inl (existT i1 ih)).
        rewrite //=.
      * exists (inr (existT i2 ih)).
        rewrite //=.
    }
    repeat split => //=.
    * intros ([(i1&ih)|(i2&ih)]&Hgt) => //=.
    * intros (([i1|i2]&ih)&Hgt) => //=.
    * intros ([(i1&ih)|(i2&ih)]&Hgt) => //=.
    * intros ([(i1&ih)|(i2&ih)]&Hgt) => //=.
Qed.

Lemma pival_zero_bind {A B} (f: A → pival B) :
  eq_pival (x ← zero_pival; f x) zero_pival.
Proof.
  split; rewrite /le_pival.
  - intros I Hin.
    apply pival_mbind_in_inv in Hin as (Ix&h&Hpf&Hin&Hhspec&Heq).
    rewrite /In/zero_pival//= in Hin. subst.
    exists (zero_ival); split => //=.
    etransitivity; first by (symmetry; eauto).
    eexists. Unshelve. all: swap 1 2.
    { rewrite //=. intros (([]&?)&?). }
    eexists. Unshelve. all: swap 1 2.
    { intros ([]&?). }
    repeat split => //=.
    * intros (([]&?)&?).
    * intros ([]&?).
    * intros (([]&?)&?).
    * intros (([]&?)&?).
  - intros I Hin.
    rewrite /In/zero_pival//= in Hin. subst.
    edestruct (pival_mbind_in zero_pival f zero_ival (λ x, Empty_set_rect (λ x, ival B) x)) as
              (I'&Hpf'&Heq'&Hin').
    { done. }
    { intros []. }
    eexists; split; last by eauto.
    etransitivity; last by eauto.
    symmetry.
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

Lemma pival_scale_bind {A B} r (m: pival A) (f: A → pival B) :
  eq_pival (x ← pscale r m; f x) (pscale r (x ← m; f x)).
Proof.
  destruct (Req_dec r 0) as [Heq0|Hneq0%Rabs_no_R0].
  { subst. setoid_rewrite pscale_0_l. apply pival_zero_bind. }
  specialize (Rabs_pos r) => Rpos.
  split; rewrite /le_pival.
  - intros I Hin.
    apply pival_mbind_in_inv in Hin as (Ix&h&Hpf&Hin&Hhspec&Heq).
    destruct Hin as (I1&Hin&Heqscale). subst.
    edestruct (pival_mbind_in m f I1 h) as (I'&Hpf'&Heq'&Hin'); auto.
    { intros i Hgt0. eapply Hhspec. rewrite //=. nra. }
    exists (iscale r I'); split; auto; last first.
    { apply pscale_in; auto. }
    etransitivity; first by (symmetry; eauto).
    setoid_rewrite <-Heq'.
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
  - intros I Hin.
    destruct Hin as (I1&Hin&Heqscale).
    apply pival_mbind_in_inv in Hin as (Ix&h&Hpf&Hin&Hhspec&Heq).
    subst.
    edestruct (pival_mbind_in (pscale r m) f (iscale r Ix) h) as (I'&Hpf'&Heq'&Hin').
    { apply pscale_in. done. }
    { rewrite //=. intros; eapply Hhspec. nra. }
    eexists; split; last by eauto.
    etransitivity; last by eauto.
    setoid_rewrite <-Heq.
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

Lemma pival_join {X: Type} (INH: X) {A: Type} (Iss: X → pival A) : pival A.
  unshelve econstructor.
  - exact (λ I, ∃ x, Iss x I).
  - abstract (destruct (Iss INH) as (?&(I&?)) eqn:Heq; exists I, INH; eauto;
              rewrite Heq; eauto).
Defined.

Lemma pival_join_ext {X A: Type} (INH INH': X) (Iss Iss': X → pival A):
  (∀ x : X, eq_pival (Iss x) (Iss' x)) →
  eq_pival (pival_join INH Iss) (pival_join INH' Iss').
Proof.
  intros Hequiv.
  split.
  - intros I Hin.
    destruct Hin as (x&Hin).
    destruct (Hequiv x) as (Hle1&Hle2).
    destruct (Hle1 _ Hin) as (I'&?).
    exists I'; intuition. eexists; eauto.
  - intros I Hin.
    destruct Hin as (x&Hin).
    destruct (Hequiv x) as (Hle1&Hle2).
    destruct (Hle2 _ Hin) as (I'&?).
    exists I'; intuition. eexists; eauto.
Qed.

Lemma pival_join_equiv {X A: Type} (INH: X) (Iss: X → pival A) (Is: pival A):
  (∀ x : X, eq_pival (Iss x) Is) →
  eq_pival (pival_join INH Iss) Is.
Proof.
  intros Hequiv.
  split.
  - intros I Hin.
    destruct Hin as (x&Hin).
    destruct (Hequiv x) as (Hle1&Hle2).
    destruct (Hle1 _ Hin) as (I'&?).
    exists I'; intuition.
  - intros I Hin.
    destruct (Hequiv INH) as (Hle1&Hle2).
    destruct (Hle2 _ Hin) as (I'&?).
    exists I'; intuition. eexists; eauto.
Qed.

Lemma pival_join_bind {X A B: Type} (INH: X) Iss (f: A → pival B) :
  eq_pival (a ← pival_join INH Iss; f a)
           (pival_join INH (λ x, a ← Iss x; f a)).
Proof.
  split.
  - intros I0 Hin.
    edestruct (pival_mbind_in_inv_idxOf (pival_join INH Iss) f) as (I&h&Hin'&Hhspec&Heq).
    { eauto. }
    destruct Hin' as (x&Hin').
    edestruct (pival_mbind_in_alt2_idxOf (Iss x) f) as (I'&?&?).
    { eexists; split; auto. apply Hin'. }
    { eauto. }
    exists I'; split; auto.
    { rewrite -Heq. auto. }
    exists x. eauto.
  - intros I0 (x&Hin).
    edestruct (pival_mbind_in_inv_idxOf (Iss x) f) as (I&h&Hin'&Hhspec&Heq).
    { eauto. }
    edestruct (pival_mbind_in_alt2_idxOf (pival_join INH Iss) f) as (I'&?&?).
    { exists I; split; first reflexivity.
      exists x; eauto. }
    { eauto.  }
    eexists; split; last eauto.
    rewrite -Heq; eauto.
Qed.

Definition le_pival_prob {X} (Is1 Is2: pival X) :=
  (∀ I, In I Is1 → ∃ I', eq_ival_prob I I' ∧ In I' Is2).

Lemma le_pival_prob_refl {X} (Is: pival X) : le_pival_prob Is Is.
Proof. intros I Hin; exists I; split; auto; reflexivity. Qed.

Lemma le_pival_prob_trans {X} (Is1 Is2 Is3: pival X) :
  le_pival_prob Is1 Is2 →
  le_pival_prob Is2 Is3 →
  le_pival_prob Is1 Is3.
Proof.
  intros Hs12a Hs23a.
  intros I Hin.
  edestruct (Hs12a I Hin) as (I'&Heq'&Hin').
  edestruct (Hs23a I' Hin') as (I''&Heq''&Hin'').
  exists I''; split; auto; etransitivity; eauto.
Qed.

Definition eq_pival_prob {X} (Is1 Is2: pival X) :=
  le_pival_prob Is1 Is2 ∧ le_pival_prob Is2 Is1.

Lemma eq_pival_prob_refl {X} (Is: pival X) : eq_pival_prob Is Is.
Proof.
  split => I Hin; eapply le_pival_prob_refl; eauto.
Qed.

Lemma eq_pival_prob_sym {X} (Is1 Is2: pival X) : eq_pival_prob Is1 Is2 → eq_pival_prob Is2 Is1.
Proof.
  intros (?&?); split; auto.
Qed.

Lemma eq_pival_prob_trans {X} (Is1 Is2 Is3: pival X) :
  eq_pival_prob Is1 Is2 →
  eq_pival_prob Is2 Is3 →
  eq_pival_prob Is1 Is3.
Proof.
  intros (Hs12a&Hs12b) (Hs23a&Hs23b); split.
  - eapply le_pival_prob_trans; eauto.
  - eapply le_pival_prob_trans; eauto.
Qed.

Lemma le_pival_to_le_pival_prob {X} (Is1 Is2: pival X):
  le_pival Is1 Is2 →
  le_pival_prob Is1 Is2.
Proof.
  intros Hle I Hin. edestruct (Hle I Hin) as (I'&Heq&Hin').
  exists I'. split; eauto using eq_ival_to_eq_ival_prob.
Qed.

Lemma eq_pival_to_eq_pival_prob {X} (Is1 Is2: pival X):
  eq_pival Is1 Is2 →
  eq_pival_prob Is1 Is2.
Proof. intros (?&?); split; eauto using le_pival_to_le_pival_prob. Qed.

Global Instance eq_pival_prob_Transitivite {X}: Transitive (@eq_pival_prob X).
Proof. intros ???. apply eq_pival_prob_trans. Qed.
Global Instance eq_pival_prob_Reflexive {X}: Reflexive (@eq_pival_prob X).
Proof. intros ?. apply eq_pival_prob_refl. Qed.
Global Instance eq_pival_prob_Symmetry {X}: Symmetric (@eq_pival_prob X).
Proof. intros ??. apply eq_pival_prob_sym. Qed.

Global Instance le_pival_prob_Transitivite {X}: Transitive (@le_pival_prob X).
Proof. intros ???. apply le_pival_prob_trans. Qed.
Global Instance le_pival_prob_Reflexive {X}: Reflexive (@le_pival_prob X).
Proof. intros ?. apply le_pival_prob_refl. Qed.

Global Instance le_pival_prob_proper {X}: Proper (@eq_pival_prob X ==> @eq_pival_prob X ==> iff) (@le_pival_prob X).
Proof.
  intros Is1 Is1' Heq1 Is2 Is2' Heq2; split => Hle;
  destruct Heq1 as (Hle1&Hle1'); destruct Heq2 as (Hle2&Hle2').
  -  etransitivity; first eauto. etransitivity; first eauto.
     done.
  -  etransitivity; first eauto. etransitivity; first eauto.
     done.
Qed.

Global Instance le_pival_prob_proper' {X}: Proper (@eq_pival X ==> @eq_pival X ==> iff) (@le_pival_prob X).
Proof.
  intros Is1 Is1' Heq1 Is2 Is2' Heq2.
  eapply le_pival_prob_proper; eauto using eq_pival_to_eq_pival_prob.
Qed.
