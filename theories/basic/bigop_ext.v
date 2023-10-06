From discprob.basic Require Import base nify order seq_ext.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop seq.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.
Require Import Reals Psatz Lia.

(* Coquelicot defines some of its own algebraic hierarchy and
   functions for indexed sums: sum_n_m. But, ssreflect has its own
   rather developed library for so-called "big-ops", which uses a
   different algebraic hierarchy. We now define a compatibility layer
   to connect the Coquelicot hierarchy for R to the one assumed by
   ssreflect. *)

Section RAddLaw.
Import Monoid.

Lemma Rplus_associative: associative  Rplus.
Proof. intros ???; apply: Hierarchy.plus_assoc. Qed.
Lemma Rplus_left_id: left_id R0 Rplus.
Proof. intros ?. apply: Hierarchy.plus_zero_l. Qed.
Lemma Rplus_right_id: right_id R0 Rplus.
Proof. intros ?. apply: Hierarchy.plus_zero_r. Qed.
Lemma Rplus_commutative: commutative Rplus.
Proof. intros ?. apply: Hierarchy.plus_comm. Qed.

Lemma Rplus_left_distributive: left_distributive Rmult Rplus.
Proof. intros ???. nra. Qed.
Lemma Rplus_right_distributive: right_distributive Rmult Rplus.
Proof. intros ???. nra. Qed.
Lemma Rmult_left_zero: left_zero 0 Rmult.
Proof. intros ?. nra. Qed.
Lemma Rmult_right_zero: right_zero 0 Rmult.
Proof. intros ?. nra. Qed.

Canonical Rplus_monoid := Law Rplus_associative Rplus_left_id Rplus_right_id.
Canonical Rplus_comoid := ComLaw Rplus_commutative.
Canonical Rplus_addoid := AddLaw Rplus_left_distributive Rplus_right_distributive.
Canonical Rmult_muloid := MulLaw Rmult_left_zero Rmult_right_zero.

End RAddLaw.

Section sum_reidx.
Local Open Scope R_scope.



Lemma inj_neq {X Y: eqType} (h: X -> Y) a b: injective h -> a != b -> h a != h b.
Proof.
  intros Hinj Hab. apply /negP. move/eqP. intros H%Hinj.
  move:Hab. rewrite H eq_refl. done.
Qed.

Lemma sum_reidx_map {A B: eqType} (p: seq A) (q: seq B) P Q (h : A -> B) (F: A -> R) (F': B -> R) :
  (forall a,  a \in p -> F a = F' (h a)) ->
  (forall a,  a \in p -> P a = true -> (h a) \in q /\ Q (h a) = true ) ->
  (forall b,  b \in q -> Q b -> ~ (exists a, a \in p /\ P a = true /\ h a = b) -> F' b = 0) ->
  uniq p -> uniq q -> (∀ x x', P x → h x = h x' → x = x') ->
  \big[Rplus/0]_(i <- p | P i) (F i) =
  \big[Rplus/0]_(i <- q | Q i) (F' i).
Proof.
  move: q.
  induction p;
  intros q HFF' HPQ Hnin0 Huniq Huniq' Hinj.
  - rewrite big_nil.
    clear Huniq Huniq'.
    induction q as [|b q].
    * rewrite big_nil. done.
    * rewrite big_cons.
      case: ifP => [?|?].
      ** rewrite -[a in a = _]Rplus_0_r. f_equal.
         *** rewrite Hnin0 //; first apply mem_head.
             intros (a'&?&?&?). done.
         *** eapply IHq; eauto.
             **** intros a'. rewrite in_nil. done.
             **** intros ?? HQ Hbad. eapply Hnin0; auto. rewrite in_cons. apply /orP. by right.
      ** eapply IHq; eauto.
         *** intros a'. rewrite in_nil. done.
         *** intros ?? HQ Hbad. eapply Hnin0; auto. rewrite in_cons. apply /orP. by right.
  - rewrite big_cons.
    case: ifP => [HP | HnP].
    * apply HPQ in HP as (?&Hin); auto using mem_head.
      rewrite (big_rem (h a)) //= Hin.
      f_equal.
      ** eauto using HFF', mem_head.
      ** eapply IHp; auto using rem_uniq.
         *** intros. apply HFF'.
             rewrite in_cons. apply /orP. by right.
         *** intros a' Hin' HP'.
             rewrite rem_filter //; split.
             **** rewrite mem_filter. apply /andP.
                  split.
                  ***** rewrite /predC1 //=.
                        apply /eqP => Heq. apply Hinj in Heq; eauto.
                        move:Huniq. rewrite cons_uniq.
                        move/andP. intros (Hnin'&?).
                        subst. move: Hnin'. move /negP. auto.
                   ***** eapply HPQ; eauto. rewrite in_cons. apply /orP. by right.
             **** eapply HPQ; eauto. rewrite in_cons. apply /orP. by right.
         *** intros b.  rewrite rem_filter // mem_filter /predC1 //=. move/andP=>[Hneq' ?] HQ Hneq.
             eapply Hnin0; auto.
             intros (a'&Hin'&HP'&Ha').
             eapply Hneq. exists a'. split; auto.
             move:Hin'. rewrite in_cons.
             move/orP=>[Heq|?].
             **** exfalso. rewrite -Ha' in Hneq'.
                  move:Hneq'. move/eqP. move:Heq. move/eqP. intros ->.  done.
             **** auto.
         *** move:Huniq. rewrite cons_uniq. move/andP. firstorder.
    * eapply IHp; auto.
      ** intros. apply HFF'.
         rewrite in_cons. apply /orP. by right.
      ** intros a' Hin' HP'.
         eapply HPQ; auto.
         rewrite in_cons. apply /orP. by right.
      ** intros ?? HQ Hnin'. eapply Hnin0; auto.
         intros (a'&Hin'&HP'&Ha'). eapply Hnin'.
         exists a'. split; auto.
         move:Hin'. rewrite in_cons. move/orP=>[Heq|?]; auto.
         exfalso. move:Heq. move/eqP. intros Heq. rewrite Heq in HP'. congruence.
      ** move:Huniq. rewrite cons_uniq. move/andP. firstorder.
Qed.

(* TODO: this is obviously rather redundant with above *)
Lemma sum_reidx_map_le {A B: eqType} (p: seq A) (q: seq B) P Q (h : A -> B) (F: A -> R) (F': B -> R) :
  (forall a,  a \in p -> F a <= F' (h a)) ->
  (forall a,  a \in p -> P a = true -> (h a) \in q /\ Q (h a) = true ) ->
  (forall b,  b \in q -> Q b -> ~ (exists a, a \in p /\ P a = true /\ h a = b) -> F' b >= 0) ->
  uniq p -> uniq q -> (∀ x x', P x → h x = h x' → x = x') ->
  \big[Rplus/0]_(i <- p | P i) (F i) <=
  \big[Rplus/0]_(i <- q | Q i) (F' i).
Proof.
  move: q.
  induction p;
  intros q HFF' HPQ Hnin0 Huniq Huniq' Hinj.
  - rewrite big_nil.
    clear Huniq Huniq'.
    induction q as [|b q].
    * rewrite big_nil. nra.
    * rewrite big_cons.
      case: ifP => [?|?].
      ** rewrite -[a in a <= _]Rplus_0_r. apply Rplus_le_compat.
         *** eapply Rge_le, Hnin0; auto; first apply mem_head.
             intros (a'&?&?&?). done.
         *** eapply IHq; eauto.
             **** intros a'. rewrite in_nil. done.
             **** intros ?? HQ Hbad. eapply Hnin0; auto. rewrite in_cons. apply /orP. by right.
      ** eapply IHq; eauto.
         *** intros a'. rewrite in_nil. done.
         *** intros ?? HQ Hbad. eapply Hnin0; auto. rewrite in_cons. apply /orP. by right.
  - rewrite big_cons.
    case: ifP => [HP | HnP].
    * apply HPQ in HP as (?&Hin); auto using mem_head.
      rewrite (big_rem (h a)) //= Hin.
      apply Rplus_le_compat.
      ** eauto using HFF', mem_head.
      ** eapply IHp; auto using rem_uniq.
         *** intros. apply HFF'.
             rewrite in_cons. apply /orP. by right.
         *** intros a' Hin' HP'.
             rewrite rem_filter //; split.
             **** rewrite mem_filter. apply /andP.
                  split.
                  ***** rewrite /predC1 //=.
                        apply /eqP => Heq. apply Hinj in Heq; eauto.
                        move:Huniq. rewrite cons_uniq.
                        move/andP. intros (Hnin'&?).
                        subst. move: Hnin'. move /negP. auto.
                  ***** eapply HPQ; eauto. rewrite in_cons. apply /orP. by right.
             **** eapply HPQ; eauto. rewrite in_cons. apply /orP. by right.
         *** intros b.  rewrite rem_filter // mem_filter /predC1 //=. move/andP=>[Hneq' ?] HQ Hneq.
             eapply Hnin0; auto.
             intros (a'&Hin'&HP'&Ha').
             eapply Hneq. exists a'. split; auto.
             move:Hin'. rewrite in_cons.
             move/orP=>[Heq|?].
             **** exfalso. rewrite -Ha' in Hneq'.
                  move:Hneq'. move/eqP. move:Heq. move/eqP. intros ->.  done.
             **** auto.
         *** move:Huniq. rewrite cons_uniq. move/andP. firstorder.
    * eapply IHp; auto.
      ** intros. apply HFF'.
         rewrite in_cons. apply /orP. by right.
      ** intros a' Hin' HP'.
         eapply HPQ; auto.
         rewrite in_cons. apply /orP. by right.
      ** intros ?? HQ Hnin'. eapply Hnin0; auto.
         intros (a'&Hin'&HP'&Ha'). eapply Hnin'.
         exists a'. split; auto.
         move:Hin'. rewrite in_cons. move/orP=>[Heq|?]; auto.
         exfalso. move:Heq. move/eqP. intros Heq. rewrite Heq in HP'. congruence.
      ** move:Huniq. rewrite cons_uniq. move/andP. firstorder.
Qed.

Variable A B : eqType.

Lemma sum_reidx_map_sym (p: seq A) (q: seq B) (P: A -> bool) Q (h : A -> B) (F: A -> R) (F': B -> R) :
  (forall a,  a \in p -> F a = F' (h a)) ->
  (forall a,  a \in p -> P a ->  (~ (h a \in q /\ Q (h a) = true)) -> F a = 0) ->
  (forall b,  b \in q -> Q b -> ~ (exists a, a \in p /\ P a = true /\ h a = b) -> F' b = 0) ->
  uniq p -> uniq q -> injective h ->
  \big[Rplus/0]_(i <- p | P i) (F i) =
  \big[Rplus/0]_(i <- q | Q i) (F' i).
Proof.
  intros HFF' Hnin0a Hnin0b Huniq Huniq' Hinj.
  transitivity (\big[Rplus/0]_(i <- p | P i && (h i \in q) && (Q (h i))) (F i)).
  { symmetry.
    eapply (sum_reidx_map _ _ (fun a => P a && (h a \in q) && Q (h a))
                              P (fun x => x)); auto.
    - intros a Hin. by do 2 move /andP => [].
    - intros a Hin HP Hfalse. apply Hnin0a; auto. intros (?&?). apply Hfalse.
      exists a; repeat split; auto.
      apply /andP; split; auto.
      apply /andP; split; auto.
  }
  eapply (sum_reidx_map _ _ _ _ h); auto.
  - intros a Hin. move /andP => []. move /andP => []. auto.
  - intros b Hin HQ Hfalse. apply Hnin0b; auto.
    intros (a&?&?&Heq). apply Hfalse; exists a; repeat split; auto.
    rewrite Heq. do 2 (apply /andP; split; auto).
Qed.

Lemma sum_reidx_surj1 (p: seq A) (q: seq B) P Q (h : A -> B) (F: A -> R) (F': B -> R) :
  (forall a,  a \in p -> F a = F' (h a)) ->
  (forall a,  a \in p -> P a = true -> (h a) \in q /\ Q (h a) = true ) ->
  (forall b,  b \in q -> Q b -> exists a, a \in p /\ P a = true /\ h a = b) ->
  uniq p -> uniq q -> injective h ->
  \big[Rplus/0]_(i <- p | P i) (F i) =
  \big[Rplus/0]_(i <- q | Q i) (F' i).
Proof.
  intros ?? Hsurj ???. eapply sum_reidx_map; eauto.
  intros ??? Hfalse. exfalso; apply Hfalse.
  apply Hsurj; auto.
Qed.

Lemma sum_reidx_surj2 (p: seq A) (q: seq B) P Q (h : A -> B) (F: A -> R) (F': B -> R) :
  (forall a,  a \in p -> F a = F' (h a)) ->
  (forall a,  a \in p -> P a = true -> (h a) \in q /\ Q (h a) = true ) ->
  (forall b,  b \in q -> Q b -> has (fun a => P a && (h a == b)) p) ->
  uniq p -> uniq q -> injective h ->
  \big[Rplus/0]_(i <- p | P i) (F i) =
  \big[Rplus/0]_(i <- q | Q i) (F' i).
Proof.
  intros ?? Hsurj ???. eapply sum_reidx_surj1; eauto.
  intros b Hinb HQ. specialize (Hsurj b Hinb HQ).
  move: Hsurj. move /hasP => [x ?]. move /andP => [HP Heq].
  exists x. repeat split; eauto. apply /eqP. done.
Qed.

End sum_reidx.

Lemma Rabs_bigop_triang {A} (f: A → R) (p: seq A) (P: pred A):
  Rabs (\big[Rplus/0]_(i <- p | P i) (f i)) <= \big[Rplus/0]_(i <- p | P i) (Rabs (f i)).
Proof.
  induction p.
  - rewrite ?big_nil Rabs_R0 //. reflexivity.
  - rewrite ?big_cons.
    case: ifP; eauto.
    etransitivity; first eapply Rabs_triang. nra.
Qed.

Lemma bigop_cond_non0 {A} (f: A → R) (p: seq A) P:
  \big[Rplus/0]_(i <- p | P i) (f i) =
  \big[Rplus/0]_(i <- p | P i && (f i != 0)) (f i).
Proof.
  induction p as [| a p].
  - rewrite ?big_nil //.
  - rewrite ?big_cons.
    case: (P a) => //=.
    case: ifP.
    * intros. f_equal; eauto.
    * move /eqP => ->. nra.
Qed.

Lemma Rabs_bigop_filter {A} (f: A → R) (p: seq A) (P Q: pred A):
  (∀ a, P a → Q a) →
  \big[Rplus/0]_(i <- p | P i) (Rabs (f i)) <= \big[Rplus/0]_(i <- p | Q i) (Rabs (f i)).
Proof.
  intros Hcond.
  induction p as [| a p].
  - rewrite ?big_nil //. reflexivity.
  - rewrite ?big_cons. specialize (Hcond a).
    move: Hcond. case: (P a).
    * intros ->; auto. nra.
    * case: (Q a).
      ** intros. specialize (Rabs_pos (f a)). nra.
      ** done.
Qed.

Lemma sum_n_bigop (f: nat → R) n:
  sum_n f n = \big[Rplus/0]_(i < S n) (f i).
Proof.
  induction n.
  - rewrite sum_O big_ord_recl big_ord0 /=. nra.
  - rewrite sum_Sn big_ord_recr IHn. rewrite /plus//=.
Qed.

Lemma sum_n_m_bigop (f: nat → R) n m:
  sum_n_m f n m = \big[Rplus/0]_(n <= i < S m) (f i).
Proof.
  revert n. induction m => n.
  - induction n => //=.
    * specialize (sum_O f). rewrite /sum_n => ->.
      rewrite big_mkord big_ord_recl big_ord0 //=. nra.
    * rewrite sum_n_m_zero; last by lia.
      rewrite big_geq; try (nify; lia). done.
  - destruct (le_dec n (S m)) as [Hle|Hgt].
    * rewrite sum_n_Sm //=.
      assert (ssrnat.leq (S m) (S (S m))) as Hrange by (nify; lia).
      rewrite (big_cat_nat _ _ _ _ Hrange); last by (nify; lia).
      rewrite IHm big_nat1 /plus//=.
    * rewrite sum_n_m_zero; last by lia.
      rewrite big_geq; try (nify; lia). done.
Qed.

Lemma Rle_bigr {A} (f1 f2: A → R) (p: seq A) (P: pred A):
  (∀ i, P i → f1 i <= f2 i) →
  (\big[Rplus/0]_(i <- p | P i) (f1 i)) <= \big[Rplus/0]_(i <- p | P i) f2 i.
Proof.
  intros Hle.
  induction p as [| a p].
  - rewrite ?big_nil //=. nra.
  - rewrite ?big_cons.
    case: ifP; eauto => HP.
    specialize (Hle a HP).
    nra.
Qed.

Lemma Rle_bigr' {A} (f1 f2: A → R) (p: seq A) (P Q: pred A):
  (∀ i, P i → (Q i) ∧ f1 i <= f2 i) →
  (∀ i, ¬ P i →  Q i → 0 <= f2 i) →
  (\big[Rplus/0]_(i <- p | P i) (f1 i)) <= \big[Rplus/0]_(i <- p | Q i) f2 i.
Proof.
  intros Hle Hpos.
  induction p as [| a p].
  - rewrite ?big_nil //=. nra.
  - rewrite ?big_cons.
    case: ifP; eauto => HP.
    * specialize (Hle a HP). destruct Hle as (->&?).
      nra.
    * case: ifP; eauto => HQ.
      move /negP in HP. specialize (Hpos a HP HQ). nra.
Qed.

Lemma Rle_big0 {A} (f: A → R) (p: seq A) (P: pred A):
  (∀ i, P i → 0 <= f i) →
  0 <= \big[Rplus/0]_(i <- p | P i) f i.
Proof.
  intros Hle.
  induction p as [| a p].
  - rewrite ?big_nil //=. nra.
  - rewrite ?big_cons.
    case: ifP; eauto => HP.
    specialize (Hle a HP).
    nra.
Qed.

Lemma Rle_big0_In {A} (f: A → R) (p: seq A) (P: pred A):
  (∀ i, P i → List.In i p → 0 <= f i) →
  0 <= \big[Rplus/0]_(i <- p | P i) f i.
Proof.
  intros Hle.
  induction p as [| a p].
  - rewrite ?big_nil //=. nra.
  - rewrite ?big_cons.
    case: ifP; eauto => HP.
    * replace 0 with (0 + 0) at 1 by nra.
      apply Rplus_le_compat.
      ** apply Hle; eauto; by left.
      ** eapply IHp. intros; eauto. apply Hle; eauto; by right.
    * eapply IHp. intros; eauto. apply Hle; eauto; by right.
Qed.

Lemma Rlt_big_inv {A: eqType} (f g: A → R) (p: seq A) (P: pred A):
  \big[Rplus/0]_(i <- p | P i) f i < \big[Rplus/0]_(i <- p | P i) g i →
  ∃ i, (i \in p) ∧ P i ∧ f i < g i.
Proof.
  intros Hle.
  induction p as [| a p].
  - rewrite ?big_nil in Hle. nra.
  - rewrite ?big_cons in Hle.
    move: Hle.
    case: ifP; eauto => HP.
    * intros; destruct (Rlt_dec (f a) (g a)).
      ** exists a. repeat split; auto. rewrite in_cons eq_refl. done.
      ** edestruct IHp as (?&?&?&?); first by nra.
         exists x. repeat split; auto. rewrite in_cons. apply /orP. by right.
    * intros; edestruct IHp as (?&?&?&?); first by nra.
         exists x. repeat split; auto. rewrite in_cons. apply /orP. by right.
Qed.


Lemma Rlt_bigr {A: eqType} (f1 f2: A → R) (p: seq A) (P: pred A):
  (∀ i, P i → f1 i <= f2 i) →
  (∃ i, (i \in p) ∧ P i ∧ f1 i < f2 i) →
  (\big[Rplus/0]_(i <- p | P i) (f1 i)) < \big[Rplus/0]_(i <- p | P i) f2 i.
Proof.
  intros Hle (i&Hin&HP&Hlt).
  induction p as [| a p].
  - rewrite in_nil in Hin. exfalso; auto.
  - rewrite in_cons in Hin. move /orP in Hin. destruct Hin as [Heq|Hin].
    * move /eqP in Heq; subst. rewrite ?big_cons HP.
      apply Rplus_lt_le_compat; first done.
      apply Rle_bigr; auto.
    * rewrite ?big_cons. case: ifP =>?; eauto.
      apply Rplus_le_lt_compat; eauto.
Qed.

Lemma Rlt_0_bigr {A: eqType} (f: A → R) (p: seq A) (P: pred A):
  (∀ i, P i → 0 <= f i) →
  (∃ i, (i \in p) ∧ P i ∧ 0 < f i) →
  0 < \big[Rplus/0]_(i <- p | P i) f i.
Proof.
  intros Hle (i&Hin&HP&Hlt).
  eapply Rle_lt_trans; last apply (Rlt_bigr (λ x, 0)); eauto.
  rewrite big1 => //=. reflexivity.
Qed.

Lemma Rlt_0_big_inv {A: eqType} (f: A → R) (p: seq A) (P: pred A):
  0 < \big[Rplus/0]_(i <- p | P i) f i →
  (∃ i, (i \in p) ∧ P i ∧ 0 < f i).
Proof.
  intros; eapply Rlt_big_inv.
  rewrite big1 => //=.
Qed.

Lemma big_INR {A: finType} F:
  (\big[Rplus/0]_(i : A) INR (F i) = INR (\sum_(i : A) (F i))).
Proof.
  elim: (index_enum _) => [| hd tl IH].
  - rewrite 2!big_nil => //=.
  - by rewrite 2!big_cons IH -plus_INR.
Qed.

Lemma Rmax_INR a b: Rmax (INR a) (INR b) = INR (max a b).
Proof.
  apply Rmax_case_strong; intros ?%INR_le; f_equal;
    [ rewrite Max.max_l // | rewrite Max.max_r //].
Qed.

From mathcomp Require Import ssrnat.

Lemma sum_index_ordinal_P_aux {A} (f: A → R) (l: seq A) r P P':
  (∀ i, (i < size l)%nat → P i = P' (nth r l i)) →
  \big[Rplus/0%R]_(a in 'I_(size l) | P a) nth 0 [seq (f i) | i <- l] a =
  \big[Rplus/0%R]_(a<-l | P' a) (f a).
Proof.
    revert r P P'.
    induction l as [| a l] => r P P' HP.
    - rewrite //= big_nil big_ord0 //.
    - transitivity (\big[Rplus/0%R]_(0<= a' < S (size l) | P a') nth 0 ([seq (f i)| i <- a :: l]) a').
      { by rewrite big_mkord. }
      rewrite big_mkcond [a in _ = a]big_mkcond //= big_cons big_mkcond big_ltn //=.
      f_equal.
      * specialize (HP 0%nat). rewrite HP //=.
      * rewrite big_add1 //=. rewrite -big_mkcond -big_mkcond -(IHl r (λ i, P (S i)) P').
        ** rewrite big_mkord. done.
        ** intros. rewrite (HP (S i)) //=.
Qed.

Lemma sum_index_ordinal_P {A} (f: A → R) (l: seq (A)) r (P: 'I_(size l) → bool) P':
  (∀ i, P i = P' (nth r l i)) →
  \big[Rplus/0%R]_(a in 'I_(size l) | P a) nth 0 [seq (f i) | i <- l] a =
  \big[Rplus/0%R]_(a<-l | P' a) (f a).
Proof.
  set (P'' := λ (n: nat),
              match lt_dec n (size l) with
                | left Pf => P (Ordinal ((introT ltP Pf)))
                | _ => true
              end).
  intros HP.
  rewrite -(sum_index_ordinal_P_aux f l r P''); last first.
  {
    intros i Hlt. rewrite /P'' //=. destruct lt_dec as [?|n] => //=.
    - eauto.
    - exfalso; apply n. apply /ltP. done.
  }
  rewrite /P'' //=.
  rewrite big_mkcond.
  rewrite big_mkcond [a in _ = a]big_mkcond.
  apply eq_bigr => i ?.
  destruct (lt_dec i (size l)) as [Hlt|Hn].
  - rewrite //=.
    assert (i = Ordinal (m := i) (introT ltP Hlt)) as <-.
    { apply ord_inj => //=. }
    done.
  - exfalso; apply Hn. apply /ltP/ltn_ord.
Qed.

Lemma sum_index_ordinal {A: eqType} f (l: seq A):
  \big[Rplus/0]_(a in 'I_(size l)) nth 0 [seq (f i) | i <- l] a =
  \big[Rplus/0]_(a<-[seq (f i) | i <- l]) a.
Proof.
    induction l as [| a l].
    * rewrite //= big_nil big_ord0 //.
    * transitivity (\big[Rplus/0%R]_(0<= a' < (size l).+1) nth 0 ([seq (f i) | i <- a :: l]) a').
      { by rewrite big_mkord. }
      rewrite //= big_cons big_ltn; last auto.
      f_equal; rewrite big_add1 //=. rewrite -IHl big_mkord. done.
Qed.

Lemma sum_index_ordinal_F {A: eqType} (l: seq (R * A)) F:
  \big[Rplus/0]_(a in 'I_(size l)) F (nth 0 [seq i.1 | i <- l] a) =
  \big[Rplus/0]_(a<-[seq i.1 | i <- l]) F a.
Proof.
    induction l as [| a l].
    * rewrite //= big_nil big_ord0 //.
    * transitivity (\big[Rplus/0%R]_(0<= a' < (size l).+1) F (nth 0 ([seq i.1 | i <- a :: l]) a')).
      { by rewrite big_mkord. }
      rewrite //= big_cons big_ltn; last auto.
      f_equal; rewrite big_add1 //=. rewrite -IHl big_mkord. done.
Qed.

Lemma big_Rplus_allpair {A B: Type} (l1: seq A) (l2: seq B) F:
  \big[Rplus/0]_(i <- [seq (x1, x2) | x1 <- l1, x2 <- l2]) F i =
  \big[Rplus/0]_(i1 <- l1) \big[Rplus/0]_(i2 <- l2) F (i1, i2).
Proof.
  revert l2. induction l1 => //=.
  - intros l2. rewrite ?big_nil. done.
  - intros l2. rewrite big_cat big_cons IHl1 big_map //.
Qed.

Lemma big_Rplus_allpair' {A B: eqType} P Q (l1: seq {x: A | P x}) (l2: seq {x: B | Q x}) F:
  \big[Rplus/0]_(i <- [seq (sval x1, sval x2) | x1 <- l1, x2 <- l2]) F i =
  \big[Rplus/0]_(i1 <- l1) \big[Rplus/0]_(i2 <- l2) F (sval i1, sval i2).
Proof.
  etransitivity; last first.
  { eapply eq_bigr => i ?. rewrite -(big_map _ (λ x, true) (λ x, F (sval i, x))). done. }
  rewrite -(big_map _ (λ x, true) (λ x, \big[Rplus/0]_(i <- _ ) F (x, i))).
  rewrite -big_Rplus_allpair.
  f_equal. apply (allpairs_comp sval sval l1 l2).
Qed.


Lemma big1_In: ∀ (R : Type) (idx : R) (op : Monoid.law idx) (I : Type) (l : list I)
         (P : pred I) (F : I → R) (Heq0: ∀ i : I, P i → List.In i l → F i = idx),
                                   \big[op/idx]_(i <- l | P i) F i = idx.
Proof.
  intros. induction l as [| a l] => //=.
  * rewrite big_nil.  auto.
  * rewrite big_cons IHl => //=.
    ** specialize (Heq0 a). destruct (P a); auto. rewrite Heq0 //=; destruct op => //=.
       by left.
    ** intros. eapply Heq0; auto; by right.
Qed.

Lemma eq_bigr_In: ∀ (R : Type) (idx : R) (op : Monoid.law idx) (I : Type) (l : list I)
         (P : pred I) (F F': I → R) (Heq: ∀ i : I, P i → List.In i l → F i = F' i),
                                   \big[op/idx]_(i <- l | P i) F i =
                                   \big[op/idx]_(i <- l | P i) F' i.
Proof.
  intros. induction l as [| a l] => //=.
  * rewrite ?big_nil.  auto.
  * rewrite ?big_cons IHl => //=; eauto.
    ** specialize (Heq a). destruct (P a); auto. rewrite Heq //=. by left.
    ** intros. eapply Heq; auto; by right.
Qed.

Lemma sum_nS {G: AbelianGroup} :
  ∀ (a : nat → G) (n : nat),
    sum_n a n.+1 = plus (a O) (sum_n (λ n, a (S n)) n).
Proof.
  rewrite /sum_n. intros.
  rewrite {1}sum_Sn_m //=; last by lia.
  f_equal.
  by rewrite sum_n_m_S.
Qed.
