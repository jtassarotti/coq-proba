From discprob.basic Require Import base order nify.
From discprob.prob Require Import prob countable finite stochastic_order uniform.
From discprob.monad Require Import monad permutation.
From discprob.monad Require quicksort quicksort_cost.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
From Coq Require Import Omega Psatz Program.Wf MSets.MSetInterface MSets.MSetGenTree Structures.OrdersEx.
Local Open Scope nat_scope.

(* The Coq standard library includes a generic implementation of
   binary search trees, parametrized by a generic "information" type
   that is stored in each node. This library is used in the
   implementation of Red-Black and AVL trees, in which the information
   stored is the color/height. Obviously, insertion cannot be
   generically defined, because these self-balancing trees do
   different things when inserting. However, the operations that do
   not build or alter the tree can be defined generically since they
   do not make use of the information field.

   Since we are going to analyze non-balancing binary search trees,
   we do not need to track any extra information, so we will just 
   instantiate this generic machinery taking the information type
   to be unit. *)

Module unit.
  Definition t := unit.
End unit.

Include MSetGenTree.Ops Nat_as_OT unit.
Include MSetGenTree.Props Nat_as_OT unit.

Scheme tree_rect := Induction for tree Sort Type.

(* The notion of tree equality in the MSetGenTree library is actually about equivalence as sets,
   not them being literally equal. So, to make trees into an eqType we need our own decidable
   equality routine *)
Fixpoint tree_eq_bool (t1 t2 : tree) : bool :=
  match t1, t2 with
    | Leaf, Leaf => true
    | Node _ t1l v1 t1r, Node _ t2l v2 t2r =>
      (v1 == v2) && (tree_eq_bool t1l t2l) && (tree_eq_bool t1r t2r)
    | _, _ => false
  end.
Lemma eq_tree : Equality.axiom tree_eq_bool.
Proof.
  move=> t1 t2.
  revert t2. induction t1 using tree_rect => t2.
  { apply: (iffP idP); rewrite /tree_eq_bool //=.
    - destruct t2; auto; try inversion 1.
    - destruct t2; auto; try inversion 1. }
  apply: (iffP idP); rewrite //=.
  - destruct t2; auto; try (inversion 1; done). 
    move /andP => [].
    move /andP => [].
    move /eqP => ?; subst.
    move /IHt1_1 => ->. move /IHt1_2 => ->; f_equal. destruct t, t0; done.
  - inversion 1; subst.
    apply /andP; split; auto.
    apply /andP; split; auto.
    * by apply /IHt1_1. 
    * by apply /IHt1_2. 
Qed.
Canonical tree_eqMixin := EqMixin (@eq_tree).
Canonical tree_eqType := Eval hnf in EqType tree (tree_eqMixin).


Fixpoint height (t: tree) :=
  match t with
    | Leaf => 0
    | Node _ Leaf v Leaf => 0
    | Node _ tl v tr => 
      S (max (height tl) (height tr))
  end.

Fixpoint add (x: nat) (t: tree) :=
  match t with
    | Leaf => Node tt Leaf x Leaf
    | Node _ tl v tr =>
      match (Nat.compare x v) with
        | Eq => t
        | Lt => Node tt (add x tl) v tr
        | Gt => Node tt tl v (add x tr)
      end
  end.

(* We prove the add function satisfies the same properties
   as the add functions for the AVL and RB trees. These proofs
   are not intended to be optimal! *)
Lemma add_spec': ∀ t x y,
    InT y (add x t) ↔ y = x ∨ InT y t.
Proof.
  induction t using tree_ind.
  - rewrite //= => x y; split. 
    * inversion 1; subst; auto.
    * destruct 1 as [|Hinl]; subst. 
      ** by econstructor.
      ** by inversion Hinl. 
  - rewrite //= => x y.
    specialize (Nat.compare_eq x t3).
    destruct (Nat.compare x t3).
    * intros -> => //; split; auto. 
      inversion 1; auto. subst. econstructor; done.
    * intros _. split.
      ** inversion 1; subst.
         *** right. econstructor; done.
         *** edestruct (proj1 (IHt1 x y)); eauto. right. 
             eapply (InLeft); eauto.
         *** right. eapply (InRight); eauto. 
      ** inversion 1 as [Heq|Hin].
         *** subst. apply InLeft; eapply IHt1; firstorder.
         *** inversion Hin; subst. 
             **** econstructor; eauto.
             **** apply InLeft. apply IHt1; firstorder.
             **** apply InRight. done.
    * intros _. split.
      ** inversion 1; subst.
         *** right. econstructor; done.
         *** right. eapply (InLeft); eauto. 
         *** edestruct (proj1 (IHt2 x y)); eauto. right. 
             eapply (InRight); eauto.
      ** inversion 1 as [Heq|Hin].
         *** subst. apply InRight; eapply IHt2; firstorder.
         *** inversion Hin; subst. 
             **** econstructor; eauto.
             **** apply InLeft. done. 
             **** apply InRight. apply IHt2; firstorder.
Qed.

Lemma add_spec: ∀ t x y `{Ok t},
    InT y (add x t) ↔ y = x ∨ InT y t.
Proof.
  intros; apply add_spec'.
Qed.

Instance add_ok t x `{HOk: Ok t} : Ok (add x t).
Proof.
  induction HOk as [|? v tl tr Hl Hok' Hr ? Hlt Hgt].
  - rewrite //=; econstructor; try (econstructor); eauto;
      rewrite /lt_tree/gt_tree//= => y; inversion 1.
  - rewrite //=. specialize (Nat.compare_spec x v) => Hspec.
    destruct (Nat.compare x v) => //=.
    * intros. econstructor; eauto.
    * intros. econstructor; eauto.
      intros y. rewrite add_spec'. intros [Heq|Hin]; subst. 
      ** inversion Hspec; done.
      ** apply Hlt; done.
    * intros. econstructor; eauto.
      intros y. rewrite add_spec'. intros [Heq|Hin]; subst. 
      ** inversion Hspec; done.
      ** apply Hgt; done.
Qed.

Module examples.
Definition t1 := (add 7 (add 3 (add 5 (add 2 Leaf)))).
(*
Eval compute in t1.
Eval compute in (height t1).
*)

Definition t2 := (add 9 (add 8 (add 7 (add 6 (add 5 (add 4 (add 3 (add 2 (add 1 Leaf))))))))).
(*
Eval compute in t2.
Eval compute in (height t2).
*)
End examples.

Fixpoint add_list (l: list nat) (t: tree) :=
  match l with
    | [::] => t
    | n :: l => add_list l (add n t)
  end.

Lemma add_list_rec x (l: list nat) (tl tr: tree) :
  add_list l (Node tt tl x tr) =
  Node tt (add_list [seq i <- l | i < x] tl) x (add_list [seq i <- l | i > x] tr).
Proof.  
  revert x tl tr.
  induction l as [| a l] => x tl tr.
  - rewrite //=.
  - rewrite //=.
    specialize (Nat.compare_spec a x) => Hspec.   
    destruct (a ?= x); inversion Hspec; subst.
    * case: ifP; first (intros; nify; exfalso; omega); auto.
    * do 2 (case: ifP; move /ltP); try (intros; omega); [].
      intros _ _. rewrite IHl; f_equal.
    * do 2 (case: ifP; move /ltP); try (intros; omega); [].
      intros _ _. rewrite IHl; f_equal.
Qed.

Lemma add_list_rec_empty a (l: list nat):
  add_list (a :: l) Leaf =
  Node tt (add_list [seq i <- l | i < a] Leaf) a (add_list [seq i <- l | i > a] Leaf).
Proof.  
  rewrite //= add_list_rec //.
Qed.

Definition add_list_random : list nat → tree → ldist tree.
  refine(Fix (measure_wf lt_wf size) (fun _ => tree → ldist tree)
  (fun l add_list_random => 
     λ t,
     match l as l' return (l = l' → ldist tree) with
     | [::] => λ eq, mret t
     | [::a] => λ eq, mret (add a t)
     | (a :: b :: l') => λ eq, 
                         p ← draw_next a (b :: l');
                         add_list_random (rem (sval p) (a :: b :: l')) _ (add (sval p) t)
     end (Init.Logic.eq_refl))); rewrite /MR; auto.
  - abstract (destruct p as (x&Hin); rewrite size_rem //; subst; rewrite //=).
Defined.

Lemma alr_unfold_aux l t:
  add_list_random l t =
  match l as l' return (l = l' → ldist tree) with
    | [::] => λ eq, mret t
    | [:: a] => λ eq, mret (add a t)
    | (a :: b :: l') => λ eq, 
      p ← draw_next a (b :: l');
      add_list_random (rem (sval p) (a :: b :: l')) (add (sval p) t)
  end (Init.Logic.eq_refl).
Proof. rewrite /add_list_random quicksort.easy_fix_eq; done. Qed.

Lemma alr_unfold l t:
  add_list_random l t =
  (match l with
    | [::] => mret t
    | [::a] => mret (add a t)
    | (a :: l) =>
      p ← draw_next a l;
      add_list_random (rem (sval p) (a :: l)) (add (sval p) t)
  end).
Proof. 
  rewrite alr_unfold_aux. destruct l => //. destruct l => //.
Qed.

Lemma size_filter_lt {A: eqType} (l: seq A) (P: pred A):
  (∃ i, i \in l ∧ ~ P i) → (size [seq i <- l | P i] < size l)%nat.
Proof.  
  induction l => //=.
  - intros (i&Hin&Hnot). rewrite in_nil in Hin. done.
  - intros Hin. case: ifP.
    * intros HP. rewrite //=.
      assert (size [seq i <- l | P i] < size l)%nat.
      { apply IHl. edestruct Hin as (i&Hin'&?).  exists i. split; auto. rewrite in_cons in Hin'.
        move /orP in Hin'. destruct Hin' as [Heq|?]; auto. move /eqP in Heq; subst; auto.
      } 
      nify. omega.
    * intros. rewrite size_filter. specialize (count_size P l). rewrite //=. 
Qed.

Lemma size_filter_le {A: eqType} (l: seq A) (P: pred A):
  (size [seq i <- l | P i] <= size l)%coq_nat.
Proof.  
  rewrite size_filter.
  specialize (count_size P l). intros; nify. rewrite //=.
Qed.

Lemma alr_rand_perm l t:
  eq_dist (rvar_of_ldist (add_list_random l t))
          (rvar_of_ldist (l' ← rand_perm_list l; mret (add_list l' t))).
Proof.
  remember (size l) as k eqn:Heq.
  revert l t Heq.
  induction k as [k IH] using (well_founded_induction lt_wf) => l t Heq.
  destruct l as [| a l]; last destruct l as [| b l].
  - apply outcomes_eq_dist => //=; repeat f_equal; nra.
  - rewrite alr_unfold; rewrite rand_perm_list_unfold.
    apply outcomes_eq_dist => //=; repeat f_equal; nra.
  - rewrite alr_unfold; rewrite rand_perm_list_unfold.
    rewrite (ldist_assoc (draw_next a (b :: l))).
    apply eq_dist_ldist_bind_ext. intros (x&Hin). rewrite /sval.
    rewrite (ldist_assoc (rand_perm_list _)). 
    eapply eq_dist_trans; first eapply IH; try eauto.
    { rewrite size_rem //; subst; rewrite //=. }
    apply eq_dist_ldist_bind_ext. intros l'. 
    rewrite ldist_left_id //=.
Qed.
  

(* Here we give a version that looks closer to the kind of recursion in quicksort,
   and which matches the format needed for the span2 lemma *)
Definition rand_tree_rec : list nat → ldist tree.
  refine(Fix (measure_wf lt_wf size) (fun _ => ldist tree)
  (fun l rand_tree_rec => 
     match l as l' return (l = l' → ldist tree) with
     | [::] => λ eq, mret Leaf
     | [::a] => λ eq, mret (Node tt Leaf a Leaf)
     | (a :: b :: l') => λ eq, 
                         p ← draw_next a (b :: l');

                         tl ← rand_tree_rec [seq i <- (a :: b :: l') | (i < sval p)%nat] _;
                         tr ← rand_tree_rec [seq i <- (a :: b :: l') | (i > sval p)%nat] _;
                         mret (Node tt tl (sval p) tr)
     end (Init.Logic.eq_refl))); rewrite /MR; auto.
  - abstract (apply /ltP; subst; apply size_filter_lt;
              exists (sval p); split; destruct p as (?&Hin); auto => //= ?; nify; omega).
  - abstract (apply /ltP; subst; apply size_filter_lt;
              exists (sval p); split; destruct p as (?&Hin); auto => //= ?; nify; omega).
Defined.

Lemma rt_unfold_aux l:
  rand_tree_rec l =
  match l as l' return (l = l' → ldist tree) with
     | [::] => λ eq, mret Leaf
     | [::a] => λ eq, mret (Node tt Leaf a Leaf)
     | (a :: b :: l') => λ eq, 
                         p ← draw_next a (b :: l');

                         tl ← rand_tree_rec [seq i <- (a :: b :: l') | (i < sval p)%nat];
                         tr ← rand_tree_rec [seq i <- (a :: b :: l') | (i > sval p)%nat];
                         mret (Node tt tl (sval p) tr)
  end (Init.Logic.eq_refl).
Proof. rewrite /rand_tree_rec quicksort.easy_fix_eq; done. Qed.

Lemma rt_unfold l:
  rand_tree_rec l =
  (match l with
    | [::] => mret Leaf
    | [::a] => mret (Node tt Leaf a Leaf)
    | (a :: l) =>
                         p ← draw_next a l;

                         tl ← rand_tree_rec [seq i <- (a :: l) | (i < sval p)%nat];
                         tr ← rand_tree_rec [seq i <- (a :: l) | (i > sval p)%nat];
                         mret (Node tt tl (sval p) tr)
  end).
Proof. 
  rewrite rt_unfold_aux. destruct l => //. destruct l => //.
Qed.

Lemma rt_gen_perm l:
  uniq l →
  eq_dist (rvar_of_ldist (rand_tree_rec l))
          (rvar_of_ldist (l' ← rand_perm_list l; mret (add_list l' Leaf))).
Proof.
  remember (size l) as k eqn:Heq.
  revert l Heq.
  induction k as [k IH] using (well_founded_induction lt_wf) => l Heq Huniq.
  destruct l as [| a l]; last destruct l as [| b l].
  - apply outcomes_eq_dist => //=; repeat f_equal; nra.
  - rewrite rt_unfold; rewrite rand_perm_list_unfold.
    apply outcomes_eq_dist => //=; repeat f_equal; nra.
  - rewrite rt_unfold; rewrite rand_perm_list_unfold.
    rewrite (ldist_assoc (draw_next a (b :: l))).
    apply eq_dist_ldist_bind_ext. intros (x&Hin). rewrite /sval.
    rewrite (ldist_fmap_bind).
    eapply eq_dist_trans; last first.
    { f_equal. eapply eq_dist_ldist_bind_ext => l'.
      rewrite add_list_rec_empty. apply eq_dist_refl.  }
    rewrite -(ldist_fmap_bind _ (λ l, ([seq i <- l | i < x], [seq i <- l | x < i ]))
                              (λ ls, mret (Node tt (add_list (fst ls) Leaf) x
                                                   (add_list (snd ls) Leaf)))).
    eapply eq_dist_trans; last first.
    { eapply eq_dist_ldist_bind_congr; last done.
      apply eq_dist_sym. by eapply rand_perm_list_split, rem_uniq. } 
    rewrite ?ldist_assoc.
    eapply eq_dist_trans; last first.
    { eapply eq_dist_ldist_bind_ext => x0.
      rewrite (ldist_fmap_bind _ (λ l2, (x0, l2))).
      rewrite /fst/snd.
      rewrite -(ldist_fmap_bind _ (λ l, add_list l Leaf)
                                 (λ ls, mret (Node tt (add_list x0 Leaf) x ls))).
      eapply eq_dist_ldist_bind_congr.
      eapply IH; eauto.
      * eapply le_lt_trans; first eapply size_filter_le.
        rewrite size_rem //. subst => //=.
      * by apply filter_uniq, rem_uniq.
      * done.
    }
    eapply eq_dist_trans; last first.
    { eapply ldist_bind_swap. }
    eapply eq_dist_trans; last first.
    { eapply eq_dist_ldist_bind_ext => tr.
      rewrite -(ldist_fmap_bind _ (λ l, add_list l Leaf)
                                 (λ tl, mret (Node tt tl x tr))).
      eapply eq_dist_ldist_bind_congr.
      eapply IH; eauto.
      * eapply le_lt_trans; first eapply size_filter_le.
        rewrite size_rem //. subst => //=.
      * by apply filter_uniq, rem_uniq.
      * done.
    }
    eapply eq_dist_trans; last apply ldist_bind_swap.
    rewrite ?filter_rem ?rem_id; first apply eq_dist_refl.
    * rewrite mem_filter. apply /andP. intros (?&?). nify. omega.
    * rewrite mem_filter. apply /andP. intros (?&?). nify. omega.
Qed.

Lemma alr_rt_perm l:
  uniq l →
  eq_dist (rvar_of_ldist (add_list_random l Leaf))
          (rvar_of_ldist (rand_tree_rec l)).
Proof.
  intros Huniq. eapply eq_dist_trans.
  - apply alr_rand_perm.
  - apply eq_dist_sym. apply rt_gen_perm.
  done.
Qed.