From discprob.basic Require Import base nify.
From mathcomp Require Import ssreflect seq ssrbool eqtype.
Import Lia Zify.

Lemma undup_map {A B: eqType} (l: seq A) (f: A → B):
  undup [seq f x | x <- l] = undup [seq f x | x <- undup l].
Proof.
  induction l as [| a l] => //=.
  symmetry. case: ifP.
  * intros Hin. apply (map_f f) in Hin.
    rewrite Hin. done.
  * intros Hnin. rewrite //=.
    case: ifP.
    ** intros Hin'.
       move /mapP in Hin'. destruct Hin' as [a' ? ?]; subst.
       case: ifP; auto.
       intros Hfalse. exfalso. move /mapP in Hfalse. apply Hfalse.
       exists a'.
       *** rewrite -mem_undup; done.
       *** auto.
    ** intros Hnin'.
       case: ifP; last by (intros; f_equal; eauto).
       intros Hfalse. move /mapP in Hnin'. exfalso. apply Hnin'.
       move /mapP in Hfalse. destruct Hfalse as [a' ? ?].
       exists a'.
       *** rewrite mem_undup; done.
       *** auto.
Qed.

Lemma nth_legacy {A: Type} (d: A) l x:
  nth d l x = List.nth x l d.
Proof.
  revert x; induction l => //=; destruct x => /= //.
Qed.

Lemma nth_error_nth1 {A: Type} (d: A) l x:
  x < length l →
  List.nth_error l x = Some (nth d l x).
Proof.
  revert l.
  induction x.
  - rewrite //=. destruct l; auto. rewrite //=. lia.
  - intros l Hlt0; destruct l.
      ** rewrite //= in Hlt0. lia.
      ** rewrite //=. eapply IHx. rewrite //= in Hlt0. lia.
Qed.

Lemma nth_error_nth2 {A: Type} (d: A) l x v:
  List.nth_error l x = Some v →
  nth d l x = v.
Proof.
  revert x.
  induction l => //=.
  - destruct x; rewrite //=.
  - destruct x; rewrite //=; first by inversion 1.
    eauto.
Qed.

Lemma size_legacy {A: Type} (l: list A):
  size l = length l.
Proof. induction l => //=. Qed.

Lemma map_legacy {A B: Type} (f: A → B) l:
  map f l = List.map f l.
Proof.
  induction l => //=.
Qed.

Lemma mem_seq_legacy {A: eqType} (x: A) (l: seq A):
  x \in l ↔ In x l.
Proof.
  split.
  - induction l.
    * inversion 1.
    * move /orP => [Heq|Htail].
      ** move /eqP in Heq. by left.
      ** right. auto.
  - induction l; inversion 1.
    * apply /orP; left; subst; auto.
    * apply /orP; right; subst; auto.
Qed.

Require Import Reals Psatz.

Local Open Scope R.
From discprob.basic Require Import base nify order.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.
Import List.

Lemma fold_left_Rmin_init l x:
  fold_left Rmin l x <= x.
Proof.
  revert x. induction l => //=; first reflexivity.
  intros x. etransitivity; first eapply IHl.
  apply Rmin_l.
Qed.

Lemma fold_left_Rmin_mono_init l x x':
  x <= x' →
  fold_left Rmin l x <= fold_left Rmin l x'.
Proof.
  revert x x'. induction l => //=.
  intros. eapply IHl.
  apply Rle_min_compat_r; auto.
Qed.

Lemma fold_left_Rmin_cons a l x:
  fold_left Rmin (a :: l) x <= fold_left Rmin l x.
Proof.
  revert a x. destruct l.
  - intros; apply Rmin_l.
  - intros => //=. apply fold_left_Rmin_mono_init.
    apply Rle_min_compat_r. apply Rmin_l.
Qed.

Lemma fold_left_ext {A B} (f f': A → B → A) l l' x x':
  (forall a b, f a b = f' a b) → l = l' → x = x' → fold_left f l x = fold_left f' l' x'.
Proof.
  revert x x' l'. induction l => //=.
  - intros.  subst => //=.
  - intros x x' [| a' l']; first by auto.
    intros => //=. eapply IHl; eauto; by congruence.
Qed.

Lemma fold_left_Rmin_glb l r x:
  (∀ r', In r' l → r <= r') → r <= x → r <= fold_left Rmin l x.
Proof.
  revert r x. induction l as [| a l] => //=.
  intros r x Hglb Hinit. eapply IHl.
  - intros. apply Hglb; eauto.
  - apply Rmin_glb; eauto.
Qed.

Lemma fold_left_Rmin_lb l x:
  (∀ r', In r' l → fold_left Rmin l x <= r').
Proof.
  revert x. induction l as [| a l] => //=.
  intros x r [Hhd|Htl].
  - subst. etransitivity; first eapply fold_left_Rmin_init. apply Rmin_r.
  - eapply IHl. auto.
Qed.

Lemma fold_left_Rmin_witness1 l x:
  (∃ r, In r l ∧ r = fold_left Rmin l x) ∨ ((∀ r, In r l → x < r) ∧ fold_left Rmin l x = x).
Proof.
  revert x. induction l as [| a l] => //=.
  - right. split; auto; intros ? [].
  - intros x. edestruct (IHl (Rmin x a)) as [(r&Hin&Heq)|Hlt].
    * left. exists r. split; auto.
    * destruct (Rlt_dec x a).
      ** right; split.
         *** intros ? [|]; eauto.
             **** subst. nra.
             **** eapply Rle_lt_trans; last eapply Hlt; eauto.
                  rewrite Rmin_left; nra.
         *** destruct Hlt as (?&->). rewrite Rmin_left; nra.
      ** left. move: Hlt. rewrite Rmin_right; last by nra => Hlt.
         intros. exists a; split; first by left.
         apply Rle_antisym.
         ***  apply fold_left_Rmin_glb; try nra. intros. left. apply Hlt; eauto.
         *** apply fold_left_Rmin_init.
Qed.

Lemma fold_left_Rmax_init l x:
  x <= fold_left Rmax l x.
Proof.
  revert x. induction l => //=; first reflexivity.
  intros x. etransitivity; last eapply IHl.
  apply Rmax_l.
Qed.

Lemma fold_left_Rmax_ub l x:
  (∀ r', In r' l → r' <= fold_left Rmax l x).
Proof.
  revert x. induction l as [| a l] => //=.
  intros x r [Hhd|Htl].
  - subst. etransitivity; last eapply fold_left_Rmax_init. apply Rmax_r.
  - eapply IHl. auto.
Qed.

Lemma fold_left_Rmax_mono_init l x x':
  x <= x' →
  fold_left Rmax l x <= fold_left Rmax l x'.
Proof.
  revert x x'. induction l => //=.
  intros. eapply IHl.
  apply Rle_max_compat_r; auto.
Qed.

Lemma fold_left_Rmax_cons a l x:
   fold_left Rmax l x <= fold_left Rmax (a :: l) x.
Proof.
  revert a x. destruct l.
  - intros; apply Rmax_l.
  - intros => //=. apply fold_left_Rmax_mono_init.
    apply Rle_max_compat_r. apply Rmax_l.
Qed.

Lemma fold_left_Rmax_lub l r x:
  (∀ r', In r' l → r' <= r) → x <= r → fold_left Rmax l x <= r.
Proof.
  revert r x. induction l as [| a l] => //=.
  intros r x Hglb Hinit. eapply IHl.
  - intros. apply Hglb; eauto.
  - apply Rmax_lub; eauto.
Qed.

Lemma fold_left_Rmax_witness1 l x:
  (∃ r, In r l ∧ r = fold_left Rmax l x) ∨ ((∀ r, In r l → r < x) ∧ fold_left Rmax l x = x).
Proof.
  revert x. induction l as [| a l] => //=.
  - right. split; auto; intros ? [].
  - intros x. edestruct (IHl (Rmax x a)) as [(r&Hin&Heq)|Hlt].
    * left. exists r. split; auto.
    * destruct (Rgt_dec x a).
      ** right; split.
         *** intros ? [|]; eauto.
             **** subst. nra.
             **** eapply Rge_gt_trans; last eapply Hlt; eauto.
                  rewrite Rmax_left; nra.
         *** destruct Hlt as (?&->). rewrite Rmax_left; nra.
      ** left. move: Hlt. rewrite Rmax_right; last by nra => Hlt.
         intros. exists a; split; first by left.
         apply Rle_antisym.
         *** apply fold_left_Rmax_init.
         *** apply fold_left_Rmax_lub; try nra. intros. left. apply Hlt; eauto.
Qed.


Lemma fold_left_Rmax_Rmin_map {A} (l: list A) (x: R) f:
   fold_left Rmax (map f l) x = - fold_left Rmin (map (λ x, - f x) l) (- x).
Proof.
  revert x.
  induction l => x //=.
  - nra.
  - assert (- Rmax x (f a) = Rmin (- x) (-f a)) as <-; last auto.
    apply Ropp_Rmax.
Qed.

Lemma allpairs_comp {A A' B B'} (f1: A → A') (f2: B → B') l1 l2:
  [seq (f1 x1, f2 x2) | x1 <- l1, x2 <- l2] =
  [seq (x1, x2) | x1 <- [seq f1 i | i <- l1], x2 <- [seq f2 i | i <- l2]].
Proof.
  revert f1 f2 l2; induction l1 => //= f1 f2 l2.
  rewrite IHl1. rewrite -map_comp.
  f_equal. rewrite map_comp //=.
Qed.

Lemma foldl_Rmin l:
  ∀ x, foldl Rmin x l <= x.
Proof.
  induction l; rewrite //=; intros; try nra.
  eapply Rle_trans; first eapply IHl.
  apply Rmin_l.
Qed.

Lemma NoDup_uniq {T: eqType} (l: list T) : NoDup l ↔ uniq l.
Proof.
  split.
  - induction 1 => //=. apply /andP; split; auto.
    apply /negP. rewrite mem_seq_legacy. auto.
  - induction l; first econstructor.
    move /andP => [? ?]. econstructor; last eauto.
    rewrite -mem_seq_legacy; by apply /negP.
Qed.

Lemma NoDup_map {T1 T2: Type} (f: T1 → T2) (l: list T1) :
  (∀ x y, f x = f y → x = y) →
  NoDup l → NoDup (map f l).
Proof.
  intros Hinj.
  induction 1; first constructor.
  rewrite //=. constructor; auto.
  intros (x'&Heq&Hin')%in_map_iff.
  apply Hinj in Heq. subst. done.
Qed.

Lemma NoDup_map_inv {T1 T2: Type} (f: T1 → T2) (l: list T1) :
  NoDup (map f l) → NoDup l.
Proof.
  induction l => //=;  first constructor.
  inversion 1 as [|?? Hnin]. subst.
  econstructor.
  { intros Hin. apply Hnin. eapply in_map_iff; eauto. }
  eauto.
Qed.

Local Open Scope Z.
Lemma fold_left_Zmax_init l x:
  x <= fold_left Z.max l x.
Proof.
  revert x. induction l => //=; first reflexivity.
  intros x. etransitivity; last eapply IHl.
  apply Z.le_max_l.
Qed.

Lemma fold_left_Zmax_ub l x:
  (∀ r', In r' l → r' <= fold_left Z.max l x).
Proof.
  revert x. induction l as [| a l] => //=.
  intros x r [Hhd|Htl].
  - subst. etransitivity; last eapply fold_left_Zmax_init. apply Z.le_max_r.
  - eapply IHl. auto.
Qed.

Lemma fold_left_Zmax_mono_init l x x':
  x <= x' →
  fold_left Z.max l x <= fold_left Z.max l x'.
Proof.
  revert x x'. induction l => //=.
  intros. eapply IHl.
  apply Z.max_le_compat_r; auto.
Qed.

Lemma fold_left_Zmax_cons a l x:
   fold_left Z.max l x <= fold_left Z.max (a :: l) x.
Proof.
  revert a x. destruct l.
  - intros; apply Z.le_max_l.
  - intros => //=. apply fold_left_Zmax_mono_init.
    apply Z.max_le_compat_r. apply Z.le_max_l.
Qed.

Lemma fold_left_Zle_max_lub l r x:
  (∀ r', In r' l → r' <= r) → x <= r → fold_left Z.max l x <= r.
Proof.
  revert r x. induction l as [| a l] => //=.
  intros r x Hglb Hinit. eapply IHl.
  - intros. apply Hglb; eauto.
  - apply Z.max_lub; eauto.
Qed.

Lemma fold_left_Zmax_witness1 l x:
  (∃ r, In r l ∧ r = fold_left Z.max l x) ∨ ((∀ r, In r l → r < x) ∧ fold_left Z.max l x = x).
Proof.
  revert x. induction l as [| a l] => //=.
  - right. split; auto; intros ? [].
  - intros x. edestruct (IHl (Z.max x a)) as [(r&Hin&Heq)|Hlt].
    * left. exists r. split; auto.
    * destruct (Z_gt_dec x a).
      ** right; split.
         *** intros ? [|]; eauto.
             **** subst. lia.
             **** eapply Z.lt_le_trans; first eapply Hlt; eauto.
                  rewrite Z.max_l; lia.
         *** destruct Hlt as (?&->). rewrite Z.max_l; lia.
      ** left. move: Hlt. rewrite Z.max_r; last by lia=> Hlt.
         intros. exists a; split; first by left.
         apply Zle_antisym.
         *** apply fold_left_Zmax_init.
         *** apply fold_left_Zle_max_lub; try lia. intros.
             destruct Hlt as (Hlt&?). cut (r' < a); first lia.
             apply Hlt; eauto.
Qed.

Local Open Scope positive.
Lemma fold_left_Pmax_init l x:
  x <= fold_left Pos.max l x.
Proof.
  revert x. induction l => //=; first reflexivity.
  intros x. etransitivity; last eapply IHl.
  apply Pos.le_max_l.
Qed.

Lemma fold_left_Pmax_ub l x:
  (∀ r', In r' l → r' <= fold_left Pos.max l x).
Proof.
  revert x. induction l as [| a l] => //=.
  intros x r [Hhd|Htl].
  - subst. etransitivity; last eapply fold_left_Pmax_init. apply Pos.le_max_r.
  - eapply IHl. auto.
Qed.

Lemma fold_left_Pmax_mono_init l x x':
  x <= x' →
  fold_left Pos.max l x <= fold_left Pos.max l x'.
Proof.
  revert x x'. induction l => //=.
  intros. eapply IHl.
  apply Pos.max_le_compat_r; auto.
Qed.

Lemma fold_left_Pmax_cons a l x:
   fold_left Pos.max l x <= fold_left Pos.max (a :: l) x.
Proof.
  revert a x. destruct l.
  - intros; apply Pos.le_max_l.
  - intros => //=. apply fold_left_Pmax_mono_init.
    apply Pos.max_le_compat_r. apply Pos.le_max_l.
Qed.

Lemma fold_left_Ple_max_lub l r x:
  (∀ r', In r' l → r' <= r) → x <= r → fold_left Pos.max l x <= r.
Proof.
  revert r x. induction l as [| a l] => //=.
  intros r x Hglb Hinit. eapply IHl.
  - intros. apply Hglb; eauto.
  - apply Pos.max_lub; eauto.
Qed.

Lemma fold_left_Pmax_witness1 l x:
  (∃ r, In r l ∧ r = fold_left Pos.max l x) ∨ ((∀ r, In r l → r < x) ∧ fold_left Pos.max l x = x).
Proof.
  revert x. induction l as [| a l] => //=.
  - right. split; auto; intros ? [].
  - intros x. edestruct (IHl (Pos.max x a)) as [(r&Hin&Heq)|Hlt].
    * left. exists r. split; auto.
    *
      assert (x > a ∨ ¬ (x > a)) as [Hgt|Hngt].
      { zify. lia. }
      ** right; split.
         *** intros ? [|]; eauto.
             **** subst. zify; lia.
             **** eapply Pos.lt_le_trans; first eapply Hlt; eauto.
                  rewrite Pos.max_l; zify; lia.
         *** destruct Hlt as (?&->). rewrite Pos.max_l; zify; lia.
      ** left. move: Hlt. rewrite Pos.max_r; last by (zify; lia) => Hlt.
         intros. exists a; split; first by left.
         apply Pos.le_antisym.
         *** apply fold_left_Pmax_init.
         *** apply fold_left_Ple_max_lub; try lia. intros.
             destruct Hlt as (Hlt&?). cut (r' < a); first (zify; lia).
             apply Hlt; eauto.
Qed.


Lemma NoDup_inj_in_map {T1 T2: Type} (f: T1 → T2) (l: list T1) :
  (∀ x y, In x l → In y l → f x = f y → x = y) →
  NoDup l → NoDup (map f l).
Proof.
  intros Hinj.
  induction 1; first constructor.
  rewrite //=. constructor; auto.
  intros (x'&Heq&Hin')%in_map_iff.
  apply Hinj in Heq; eauto; subst.
  - done.
  - by right.
  - by left.
  - eapply IHNoDup. intros. eapply Hinj; try (by right). eauto.
Qed.
