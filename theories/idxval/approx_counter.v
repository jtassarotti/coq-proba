(* Model of the compare-and-swap concurrent approximate counter using
the "lazy" synchronization scheme *)

From discprob.basic Require Import base sval order monad bigop_ext nify.
Require Import Reals Psatz Omega.

Require ClassicalEpsilon.
Global Set Bullet Behavior "Strict Subproofs".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype finset finfun bigop.

Local Open Scope R_scope.
From discprob.prob Require Import prob countable finite stochastic_order.
Import List.
From discprob.idxval Require Import pival_dist.

Module counter.

  Require discprob.monad.counter.

  (*
  Definition flipn (n: nat) : pidist bool :=
    pidist_plus (1/2^n) (counter.range_half_pow n) (mret true) (mret false).
   *)

  Definition incr_flipn (n: nat) : pidist nat :=
    pidist_plus (1/2^n) (counter.range_half_pow n) (mret (S O)) (mret O).

  Fixpoint upto (n: nat) : pidist nat :=
    match n with
    | O => mret O
    | S n' => pidist_union (mret (S n')) (upto n')
    end.

  Fixpoint rep_upto_while {A B: Type} (f: A → B → A) (P: A → bool) (n: nat)
           (comp: pidist B) (init: A) :=
    match n with
    | 0 => mret init
    | S n' =>
      if P init then
        pidist_union (mret init) 
                     (b ← comp;
                      rep_upto_while f P n' comp (f init b))
      else
        mret init
    end.
    
  Definition rep_upto {A B: Type} (f: A → B → A) (n: nat) (comp: pidist B) (init: A) :=
    rep_upto_while f (λ x, true) n comp init.

  Definition rep_upto_count {A B: Type} (f: A → B → A) (n: nat) (comp: pidist B) (init: A) :=
    rep_upto (λ an b, (f (fst an) b, S (snd an))) n comp (init, O).

  Definition rep_upto_while_count {A B: Type} (f: A → B → A) P (n: nat) (comp: pidist B) (init: A) :=
    rep_upto_while (λ an b, (f (fst an) b, S (snd an))) (λ x, P (fst x)) n comp (init, O).

  Fixpoint rep_while {A B: Type} (f: A → B → A) (P: A → bool) (n: nat)
           (comp: pidist B) (init: A) :=
    match n with
    | 0 => mret init
    | S n' =>
      if P init then
                     (b ← comp;
                      rep_while f P n' comp (f init b))
      else
        mret init
    end.

  Definition rep {A B: Type} (f: A → B → A) (n: nat) (comp: pidist B) (init: A) :=
    rep_while f (λ x, true) n comp init.

  Definition rep_count {A B: Type} (f: A → B → A) (n: nat) (comp: pidist B) (init: A) :=
    rep (λ an b, (f (fst an) b, S (snd an))) n comp (init, O).

  Definition rep_while_count {A B: Type} (f: A → B → A) P (n: nat) (comp: pidist B) (init: A) :=
    rep_while (λ an b, (f (fst an) b, S (snd an))) (λ x, P (fst x)) n comp (init, O).


  Definition approx_estimate (n: nat) : R :=
    2^n - 1.

  Fixpoint approx (pt: nat) (n: nat) (k: nat) {struct n} : pidist R :=
    match n with
    | 0 => mret (approx_estimate k)
    | S n => i0 ← incr_flipn k;
             '(itotal, c) ← rep_upto_while_count (λ isum i, isum + i)%nat
                                                 (λ isum, (isum <= pt)%nat) 
                                                 n
                                                 (incr_flipn k)
                                                 i0;
               approx pt (n - c) (k + min 1 itotal)
    end.

  Fixpoint approx_worst (pt: nat) (n: nat) (k: nat) {struct n} : pidist R :=
    match n with
    | 0 => mret (approx_estimate k)
    | S n => i0 ← incr_flipn k;
             '(itotal, c) ← rep_while_count (λ isum i, isum + i)%nat
                                                 (λ isum, (isum <= pt)%nat) 
                                                 n
                                                 (incr_flipn k)
                                                 i0;
               approx_worst pt (n - c) (k + min 1 itotal)
    end.


  Lemma rep_upto_while_impl {A B} (f: A → B → A) g1 g2 k m a:
    (∀ a, g1 a ==> g2 a) →
    le_pidist (rep_upto_while f g1 k m a) (rep_upto_while f g2 k m a).
  Proof.
    intros Himpl.
    revert a.
    induction k => //= a.
    - reflexivity.
    - specialize (Himpl a). destruct (g1 a).
      * rewrite //= in Himpl. rewrite Himpl. 
        apply pidist_union_mono; first reflexivity.
        apply pidist_bind_congr_le; first reflexivity.
        eauto.
      * destruct (g2 a); last by reflexivity.
        apply pidist_union_le; reflexivity.
  Qed.
    
  Lemma approx_pt_S_le_pidist pt n k:
    le_pidist (approx pt n k) (approx pt.+1 n k).
  Proof.
    revert pt k.
    induction n as [n IH] using lt_wf_ind => pt k.
    destruct n as [| n].
    - rewrite //=. reflexivity.
    - rewrite //=. apply pidist_bind_congr_le; first reflexivity.
      intros i0.
      destruct n.
      * rewrite //=. reflexivity.
      * rewrite /rep_upto_while_count. rewrite //=.
        destruct (le_dec i0 (pt)).
        ** assert (i0 <= pt)%nat as ->.
           { auto with *. nify. done. }
           assert (i0 <= (S pt))%nat as ->.
           { auto with *. nify. omega. }
           eapply pidist_bind_congr_le.
           { apply pidist_union_mono; first reflexivity.
             apply pidist_bind_congr_le; first reflexivity.
             intros.
             apply rep_upto_while_impl. intros => //=.
             apply /implyP. intros. nify. omega.
           }
           intros (itotal&c). eapply IH. nify. omega.
        ** assert (i0 <= pt = false)%nat as ->.
           { apply /negP. intros Hn. nify.  omega. }
           case: ifP.
           *** intros.
               assert (i0 = (S pt))%nat.
               { nify.  omega. }
               subst.
               apply pidist_bind_congr_le.
               ****  apply pidist_union_le.
               **** intros (?&?). eapply IH.
                    nify. omega.
           *** intros. setoid_rewrite pidist_left_id.
               eapply IH. nify. omega.
  Qed.

  Lemma approx_pt_S_Ex pt n k:
    Ex_min (approx (S pt) n k) ≤ Ex_min (approx pt n k).
  Proof.
    apply Ex_min_le_pidist.
    apply approx_pt_S_le_pidist.
  Qed.

  Local Open Scope nat_scope.

  Lemma approx_worst_aux pt n k1 k2 c1 c2 m1 m2 i1 i2:
    (k1 <= k2)%coq_nat →
    (k1 + Init.Nat.min 1 i1 <= k2 + Init.Nat.min 1 i2)%coq_nat →
    (i1 > i2 → k1 + Init.Nat.min 1 i1 <= k2)%coq_nat →
    (m1 = n + c1)%coq_nat →
    (m2 = n + c2)%coq_nat →
    Ex_min
      (' (itotal, c)
         ← rep_while (λ (an : nat * nat) (b : nat), ((an.1 + b)%N, an.2.+1))
         (λ x : nat * nat, (x.1 <= pt)%N) n (incr_flipn k1) (i1, c1)%nat;
         approx_worst pt (m1 - c) (k1 + Init.Nat.min 1 itotal))
      ≤ Ex_min
      (' (itotal, c)
         ← rep_upto_while (λ (an : nat * nat) (b : nat), ((an.1 + b)%N, an.2.+1))
         (λ x : nat * nat, (x.1 <= pt)%N) n (incr_flipn k2) (i2, c2);
         approx pt (m2 - c) (k2 + Init.Nat.min 1 itotal)).
  Proof.
    revert pt k1 k2 c1 c2 m1 m2 i1 i2. 
    induction n as [n IH] using lt_wf_ind => pt k1 k2 c1 c2 m1 m2 i1 i2 Hlek Hle Hlei
                                               Hm1 Hm2.
    destruct n as [| n].
    - rewrite /rep_while/rep_upto_while.
      setoid_rewrite pidist_left_id => //=.
      intros. subst. rewrite ?subnn //=. rewrite ?Ex_min_mret //= /approx_estimate //=.
      rewrite ?addn0. rewrite /Rminus. apply Rplus_le_compat_r.
      apply Rle_pow; try nra. rewrite //= in Hle.
    - rewrite {1}/rep_while -{1}/rep_while.
      rewrite {1}/rep_upto_while -{1}/rep_upto_while.
      case: ifP => Hle_pt1;
      rewrite //= in Hle_pt1;
      case: ifP => Hle_pt2;
      rewrite //= in Hle_pt2.
      * apply Ex_min_bind_union.
        ** setoid_rewrite pidist_left_id.  
           simpl fst. simpl snd.
           subst.
           replace ((S n + c2)%coq_nat - c2)%nat with (S n); last by (nify; omega).
           rewrite /approx -/approx.
           assert (k1 <= k2 + Init.Nat.min 1 i2)%coq_nat as Hle' by (nify; omega).
           setoid_rewrite pidist_assoc.
           destruct Hle' as [| k2' Hle']. (* Might want inversion instead of destruct here *)
           *** eapply Ex_min_bind_congr; first by reflexivity.
               intros i.
               rewrite /rep_upto_while_count. 
               eapply IH; nify; try omega. 
               destruct i1; simpl in *; omega.
               destruct i1.
               **** rewrite //=.  omega.
               **** rewrite //= in Hle. omega.
           *** eapply Ex_min_pidist_plus_bind_le_l;
               eapply Ex_min_pidist_plus_bind_le_r;
               setoid_rewrite pidist_left_id;
               abstract (eapply IH; destruct i1; simpl in *; nify; omega).
        ** setoid_rewrite pidist_assoc.
           destruct Hlek as [| k2' Hlek].
           *** eapply Ex_min_bind_congr; first by reflexivity.
               intros i.
               rewrite /rep_upto_while_count. 
               abstract (eapply IH; nify; try omega; 
                         destruct i1; destruct i2; destruct i; simpl in *; try omega).
           *** eapply Ex_min_pidist_plus_bind_le_l;
               eapply Ex_min_pidist_plus_bind_le_r;
               setoid_rewrite pidist_left_id;
               eapply IH; try omega;
               destruct i1; destruct i2; simpl in *; nify; try omega.
      * setoid_rewrite pidist_left_id.
        rewrite Hm2.
        replace ((S n + c2)%coq_nat - c2) with (S ((n + c2)%coq_nat - c2)); last by (nify; omega).
        rewrite /approx -/approx.
        rewrite /rep_upto_while_count.
        setoid_rewrite pidist_assoc.
        replace ((n + c2)%coq_nat - c2) with n; last by (nify; omega).
        eapply Ex_min_pidist_plus_bind_le_l;
        setoid_rewrite pidist_left_id;
        eapply Ex_min_pidist_plus_bind_le_r;
        setoid_rewrite pidist_left_id;
        by (eapply IH; try omega;
          destruct i1; destruct i2; simpl in *; nify; try omega).
      * move /negP in Hle_pt1.
        apply Ex_min_bind_union.
        ** setoid_rewrite pidist_left_id.
           rewrite Hm1 Hm2. 
           replace ((S n + c1)%coq_nat - c1) with (S ((n + c1)%coq_nat - c1)); last by (nify; omega).
           replace ((S n + c2)%coq_nat - c2) with (S ((n + c2)%coq_nat - c2)); last by (nify; omega).
        rewrite /approx_worst -/approx_worst.
        rewrite /rep_while_count.
        rewrite /approx -/approx.
        rewrite /rep_upto_while_count.
        replace ((n + c1)%coq_nat - c1) with n; last by (nify; omega).
        replace ((n + c2)%coq_nat - c2) with n; last by (nify; omega).
        assert (k1 + min 1 i1 = k2 + Init.Nat.min 1 i2 ∨
                k1 + min 1 i1 < k2 + Init.Nat.min 1 i2) as [Heq|Hlt].
        { rewrite //=.
          destruct i1; destruct i2; rewrite //= in Hle; inversion Hle; nify; try omega; auto;
          try (left; nify; omega);
          try (right; nify; omega). }
           *** rewrite Heq. subst. eapply Ex_min_bind_congr; first by reflexivity.
               intros i.
               eapply IH; nify; try omega. 
           *** eapply Ex_min_pidist_plus_bind_le_l;
               eapply Ex_min_pidist_plus_bind_le_r;
               setoid_rewrite pidist_left_id;
               abstract (eapply IH; destruct i1; simpl in *; nify; omega).
        ** setoid_rewrite pidist_assoc.
           setoid_rewrite pidist_left_id.
           rewrite Hm1.
           replace ((S n + c1)%coq_nat - c1) with (S ((n + c1)%coq_nat - c1)); last by (nify; omega).
           rewrite /approx_worst -/approx_worst.
           rewrite /rep_while_count.
           replace ((n + c1)%coq_nat - c1) with n; last by (nify; omega).
           destruct Hlei.
           { nify; omega. }
           *** eapply Ex_min_bind_congr; first by reflexivity.
               intros i.
               eapply IH;
                 destruct i1; destruct i2; destruct i; rewrite //=; nify; try omega; auto.
           *** eapply Ex_min_pidist_plus_bind_le_l;
               eapply Ex_min_pidist_plus_bind_le_r;
               setoid_rewrite pidist_left_id;
               abstract (eapply IH; destruct i1; simpl in *; nify; omega).
      * setoid_rewrite pidist_left_id.
        rewrite Hm1 Hm2.
           replace ((S n + c1)%coq_nat - c1) with (S ((n + c1)%coq_nat - c1)); last by (nify; omega).
           replace ((S n + c2)%coq_nat - c2) with (S ((n + c2)%coq_nat - c2)); last by (nify; omega).
        rewrite /approx_worst -/approx_worst.
        rewrite /rep_while_count.
        rewrite /approx -/approx.
        rewrite /rep_upto_while_count.
        replace ((n + c1)%coq_nat - c1) with n; last by (nify; omega).
        replace ((n + c2)%coq_nat - c2) with n; last by (nify; omega).
        assert (k1 + min 1 i1 = k2 + Init.Nat.min 1 i2 ∨
                k1 + min 1 i1 < k2 + Init.Nat.min 1 i2) as [Heq|Hlt].
        { rewrite //=.
          destruct i1; destruct i2; rewrite //= in Hle; inversion Hle; nify; try omega; auto;
          try (left; nify; omega);
          try (right; nify; omega). }
           *** rewrite Heq. subst. eapply Ex_min_bind_congr; first by reflexivity.
               intros i.
               eapply IH; nify; try omega. 
           *** eapply Ex_min_pidist_plus_bind_le_l;
               eapply Ex_min_pidist_plus_bind_le_r;
               setoid_rewrite pidist_left_id;
               abstract (eapply IH; destruct i1; simpl in *; nify; omega).
  Qed.

  Lemma approx_worst_spec pt n k:
    Ex_min (approx_worst pt n k) ≤ Ex_min (approx pt n k).
  Proof.
    destruct n. 
    - rewrite //=.  reflexivity.
    - rewrite /approx_worst -/approx_worst.
      rewrite /rep_while_count.
      rewrite /approx -/approx.
      rewrite /rep_upto_while_count.
      eapply Ex_min_bind_congr; first by reflexivity. intros i.
      eapply approx_worst_aux; omega.
  Qed.


  Local Open Scope R.
      
  Fixpoint Ex_approx_worst c n k curr :=
    match n with
    | 0 => match curr with
          | 0 => approx_estimate k
          | _ => approx_estimate (S k)
          end
    | S n =>
      let (curr', k') :=
          match (c - S curr)%nat with
          | 0 => (0, S k)%nat
          | _ => (S curr, k)%nat
          end
      in
      (1 / 2^k) * Ex_approx_worst c n k' curr' +
      (1 - 1 / 2^k) * Ex_approx_worst c n k curr
    end.



  Lemma Ex_approx_worst_spec_aux pt n k:
    (1 <= pt)%coq_nat →
    (∀ i1 c1 m1, 
    (i1 <= pt)%coq_nat →
    (m1 = n + c1)%coq_nat →
    ( Ex_min (' (itotal, c)
         ← rep_while (λ (an : nat * nat) (b : nat), ((an.1 + b)%N, an.2.+1))
         (λ x : nat * nat, (x.1 <= pt)%N) n (incr_flipn k) (i1, c1)%nat;
               approx_worst pt (m1 - c) (k + Init.Nat.min 1 itotal)) =
      Ex_approx_worst (S pt) n k (min i1 pt))) ∧
    ( Ex_min (approx_worst pt n k) = Ex_approx_worst (S pt) n k 0).
  Proof.
    intros Hpt.
    revert k. 
    induction n as [n IH] using lt_wf_ind => k. 
    destruct n as [| n].
    - split.
      * intros i1 c1 m1 Hlt Heq.
        rewrite //=.  setoid_rewrite pidist_left_id. rewrite Heq.
        replace ((0 + c1)%coq_nat - c1)%nat with O by (nify; omega).
        rewrite //=. rewrite Ex_min_mret.
        rewrite /approx_estimate; destruct i1 => //=; rewrite ?addn0 ?addn1 //=.
        destruct pt; rewrite ?addn0 ?addn1 //=. omega.
      * rewrite //=. apply Ex_min_mret.
    - split.
      * intros i1 c1 m1 Hlt Heq.
      rewrite /rep_while -/rep_while. rewrite /Ex_approx_worst -/Ex_approx_worst.
      rewrite /fst.
      assert (i1 <= pt)%N as -> by (nify; omega).
      case_eq (S pt - S i1)%nat.
      { intros.
        assert (pt = i1) as -> by (nify; omega).
        destruct n.
        * rewrite //=.  setoid_rewrite pidist_assoc. setoid_rewrite pidist_left_id.
          rewrite Ex_min_pidist_plus_bind. setoid_rewrite pidist_left_id.
          replace (m1 - S c1)%nat with O by (nify; omega).
          rewrite //=. rewrite ?Ex_min_mret ?addn1 ?addn0 => //=.
          rewrite Min.min_idempotent.
          destruct i1; rewrite ?addn0 ?addn1; auto.
          rewrite subnn. done.
        * setoid_rewrite pidist_assoc.
          rewrite Ex_min_pidist_plus_bind. setoid_rewrite pidist_left_id.
          destruct (IH (S n)) with (k := k) as (IHl&_); first by auto.
          rewrite [a in _ + (_ * a) = _]IHl; try (rewrite //=; nify; omega).
          rewrite addn0.
          f_equal. f_equal.
          rewrite /rep_while -/rep_while. rewrite addn1.
          assert (S i1 <= i1 = false)%nat as ->.
          { apply /negP. nify. omega. }
          setoid_rewrite pidist_left_id.
          rewrite /snd.
          replace (m1 - S c1)%nat with (S n) by (nify; omega).
          specialize (IH (S n)).
          assert (Hltn: (S n < S (S n))%coq_nat) by auto.
          destruct (IH Hltn (k + min 1 (S i1))%nat) as (_&IHr);
            last (rewrite (IHr); clear IHr); eauto;
            try (rewrite //=; nify; omega).
          rewrite ?Min.min_idempotent ?subnn. 
          destruct i1.
          ** rewrite Min.min_idempotent. rewrite ?Min.min_r; last by omega.
          ** rewrite ?Min.min_l; last by omega. rewrite ?addn0; f_equal.
             f_equal. f_equal.
             *** rewrite //=. nify. omega.
      }
      intros diff Hdiff.
      setoid_rewrite pidist_assoc.
      rewrite Ex_min_pidist_plus_bind.
      setoid_rewrite pidist_left_id.
      rewrite Heq. replace (S n + c1)%coq_nat with (n + S c1)%coq_nat; last by (nify; omega).
      specialize (IH n).
      assert (n < S n)%coq_nat as Hltn. 
      { auto.  }
      destruct (IH Hltn k) as (IHl&_); last (rewrite [a in _ + (_ * a) = _](IHl _ (S c1)); clear IHl);
        try (rewrite //=; nify; omega);
      destruct (IH Hltn k) as (IHl&_); last (rewrite (IHl _ (S c1)); clear IHl);
        try (rewrite //=; nify; omega).
      rewrite addn1 addn0 //=.
      destruct pt as [| pt].
      { exfalso. nify. omega. }
      assert (i1 <= pt)%coq_nat.
      { nify.  omega. }
      rewrite ?(Min.min_l i1 (S pt)); last by auto.
      rewrite ?(Min.min_l i1 pt); last by auto.
      rewrite Hdiff; f_equal.
      * rewrite /approx_worst -/approx_worst.
        rewrite Ex_min_pidist_plus_bind.
        setoid_rewrite pidist_left_id.
        specialize (IH n).
        assert (n < S n)%coq_nat as Hltn by auto.
      destruct (IH Hltn k) as (IHl&_); last (rewrite [a in _ + (_ * a) = _](IHl _ O); clear IHl);
        try (rewrite //=; nify; omega).
      destruct (IH Hltn k) as (IHl&_); last (rewrite (IHl _ O); clear IHl);
        try (rewrite //=; nify; omega).
      rewrite //=. 
      rewrite subn1 //=. destruct pt; first by omega.
      done.
  Qed.

  Lemma Ex_approx_worst_spec_aux2 n k:
    (∀ i1 c1 m1, 
    (i1 = 0 ∨ i1 = 1)%nat →
    (m1 = n + c1)%coq_nat →
    ( Ex_min (' (itotal, c)
         ← rep_while (λ (an : nat * nat) (b : nat), ((an.1 + b)%N, an.2.+1))
         (λ x : nat * nat, (x.1 <= 0)%N) n (incr_flipn k) (i1, c1)%nat;
               approx_worst 0 (m1 - c) (k + Init.Nat.min 1 itotal)) =
      Ex_approx_worst 1 n (k + min 1 i1) 0)) ∧
    ( Ex_min (approx_worst 0 n k) = Ex_approx_worst 1 n k 0).
  Proof.
    revert k.
    induction n as [n IH] using lt_wf_ind => k.
    destruct n as [| n].
    - split.
      * intros i1 c1 m2 Hcase Heq.
        rewrite Heq. rewrite //=. setoid_rewrite pidist_left_id.
        rewrite subnn. rewrite //=. rewrite Ex_min_mret. destruct i1; auto.
      * rewrite //=. rewrite Ex_min_mret; done.
    - split.
      * intros ic1 c1 m2 Hcase Heq.
        rewrite Heq. rewrite //=. destruct Hcase as [?|?]; subst.
        ** rewrite //=. setoid_rewrite pidist_assoc.
           rewrite Ex_min_pidist_plus_bind. setoid_rewrite pidist_left_id.
           assert (n < S n)%coq_nat as Hltnn.
           { auto. }

           destruct (IH n Hltnn k) as (IHl&_).
           rewrite [a in _ + (_ * a) = _]IHl; try (rewrite //=; nify; omega); [].
           rewrite ?addn0.
           f_equal. f_equal.
           destruct (IH _ Hltnn k%nat) as (IHl'&IHr).
           replace ((S (n + c1)%coq_nat)) with (n + (S c1))%coq_nat; last by auto.
           rewrite IHl'  //=; auto. rewrite addn1. done.
        ** rewrite //=. setoid_rewrite pidist_left_id.
           replace (S (n + c1)%coq_nat - c1)%nat with (S n); last by (nify; omega).
           rewrite //=. rewrite Ex_min_pidist_plus_bind.
           setoid_rewrite pidist_left_id.
           assert (n < S n)%coq_nat as Hltnn.
           { auto. }
           destruct (IH n Hltnn (k + 1)%nat) as (IHl&_); rewrite IHl; try (rewrite //=; nify; omega).
           f_equal.
           {rewrite //= ?addn1. f_equal. }
           destruct (IH n Hltnn (k + 1))%nat as (IHl'&_); rewrite IHl'; try (rewrite //=; nify; omega).
           rewrite //= ?addn1 ?addn0. f_equal.
      * rewrite //=.
        assert (n < S n)%coq_nat as Hltnn.
        { auto. }
        rewrite Ex_min_pidist_plus_bind.
        setoid_rewrite pidist_left_id.
        destruct (IH n Hltnn k)%nat as (IHl'&_).
        rewrite ?IHl'; try (rewrite //=; nify; omega).
        rewrite //= ?addn1 ?addn0. done.
  Qed.

  Lemma Ex_approx_worst_spec pt n k:
    Ex_min (approx_worst pt n k) = Ex_approx_worst (S pt) n k 0.
  Proof.
    destruct pt as [| pt].
    - edestruct Ex_approx_worst_spec_aux2; eauto.
    - edestruct (Ex_approx_worst_spec_aux (S pt) n k); eauto.
      nify. omega.
  Qed.
    

  Remark simple_calculation: Ex_min (approx_worst 1 5 0) = 3.
  Proof.
    rewrite Ex_approx_worst_spec //= /approx_estimate.
    nra.
  Qed.

  Remark simple_calculation2: Ex_min (approx_worst 1 6 0) >= 3.
  Proof.
    rewrite Ex_approx_worst_spec //= /approx_estimate.
    field_simplify.
    nra.
  Qed.

  (*
  Remark simple_calculation3: 7 - Ex_min (approx_worst 1 7 0) <= (33/10).
  Proof.
    rewrite Ex_approx_worst_spec //= /approx_estimate.
    field_simplify.
    nra.
  Qed.

  Remark simple_calculation4: 10 - Ex_min (approx_worst 1 10 0) <= (409/100).
  Proof.
    rewrite Ex_approx_worst_spec //= /approx_estimate.
    Time field_simplify.
    nra.
  Qed.
   *)

 End counter.