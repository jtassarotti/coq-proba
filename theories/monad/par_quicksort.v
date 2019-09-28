From discprob.basic Require Import base order nify.
From discprob.prob Require Import prob countable finite stochastic_order.
From discprob.monad Require Import monad monad_par.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Coq.omega.Omega Coq.Program.Wf.
Local Open Scope nat_scope.

Definition compare (x y: nat) (* : cost (compare_nat x y (x < y) (y < x) (x == y)) *) :=
  {| work := 1; span := 1; result := ltngtP x y |}.
Definition ltc (x y: nat) :=
  b ← compare x y ;
    mret (match b with
          | CompareNatLt _ => true
          | _ => false
          end).
Definition eqc (x y: nat) :=
  b ← compare x y ;
    mret (match b with
          | CompareNatEq _ => true
          | _ => false
          end).
Definition gtc (x y: nat) :=
  b ← compare x y ;
    mret (match b with
          | CompareNatGt _ => true
          | _ => false
          end).

Record splitting (A: Type) := mkSplit { lower : seq A; middle: seq A; upper : seq A}.
Arguments mkSplit {_}.
Arguments lower {_}.
Arguments middle {_}.
Arguments upper {_}.

Definition splitting_eq_bool {A: eqType} (a b : splitting A) : bool :=
  (lower a == lower b) && (middle a == middle b) && (upper a == upper b).
Lemma eq_spl {A: eqType} : Equality.axiom (@splitting_eq_bool A).
Proof.
move=> [l1 m1 u1] [l2 m2 u2].
apply: (iffP idP); rewrite /splitting_eq_bool //=.
- move /andP => [Hand ?].
  move /andP in Hand. destruct Hand as (?&?).
  f_equal; apply /eqP; done.
- inversion 1; subst.
  apply /andP; split; auto.
  apply /andP; split; auto.
Qed.

Canonical splitting_eqMixin A := EqMixin (@eq_spl A).
Canonical splitting_eqType A := Eval hnf in EqType (splitting _) (splitting_eqMixin A).

Definition partition (n: nat) (l: list nat) :=
  '(l1, l2, l3) ← par3 (parfilter (λ x, ltc x n) l)
                       (parfilter (λ x, eqc x n) l)
                       (parfilter (λ x, gtc x n) l);
  mret {| lower := l1; middle := l2; upper := l3 |}.

Lemma partition_perm_eq l:
  ∀ n, perm_eq (lower (result (partition n l)) ++ 
                 middle (result (partition n l)) ++
                 upper (result (partition n l))) l.
Proof.
  induction l => n; first by (rewrite /partition/par3//=).
  rewrite //=. case (ltngtP a n) => Hcmp //=.
  - rewrite perm_cons. specialize (IHl n). rewrite //= in IHl.
  - eapply (perm_eq_trans).
    { erewrite perm_cat2l. rewrite perm_catC cat_cons. erewrite perm_cons. done. }
    rewrite -cat_cons perm_catCA cat_cons perm_cons.
    rewrite -perm_catCA.
    eapply (perm_eq_trans); last apply (IHl n).
    rewrite perm_cat2l perm_catC //.
  - rewrite -cat_cons perm_catCA // cat_cons perm_cons.
    rewrite perm_catCA //.
    eapply IHl.
Qed.

Lemma partition_middle_size l:
  ∀ n, n \in l → 0 < size (middle (result (partition n l))).
Proof.
  induction l => //= n Hin.
  intros. case (ltngtP a n) => //=; intros Hcmp; apply IHl;
  move: Hin; rewrite in_cons; move /orP => [HeqP|] //; exfalso;
  move /eqP in HeqP; subst; rewrite ltnn in Hcmp; done.
Qed.

Lemma work_mret {A B} (m: cost A) (f: A → B): work (x ← m; mret (f x)) = work m.  
Proof. rewrite //=. Qed.

Lemma work_par2 {A B} (m: cost A) (m': cost B): work (par2 m m') = work m + work m'.
Proof. rewrite //=. Qed.

Lemma work_par3 {A B C} (m: cost A) (m': cost B) (m'': cost C):
  work (par3 m m' m'') = work m + work m' + work m''.
Proof. rewrite //=. Qed.

Lemma work_parfilter {A: eqType} (P: A → cost bool) (l: seq A) k:
  (∀ x, x \in l → work (P x) = k) →
  work (parfilter P l) = size l * k.
Proof.
  intros Hcost. induction l => //=. 
  rewrite /parfilter/parmap//= in IHl. rewrite -addnA IHl => //=. 
  rewrite Hcost => //=.
  - nify => //=. omega. 
  - rewrite in_cons eq_refl //.
  - intros ? Hin. eapply Hcost. rewrite in_cons. apply /orP; auto.
Qed.

Lemma span_mret {A B} (m: cost A) (f: A → B): span (x ← m; mret (f x)) = span m.  
Proof. rewrite //=. Qed.

Lemma span_par2 {A B} (m: cost A) (m': cost B): span (par2 m m') = max (span m) (span m').
Proof. rewrite //=. Qed.

Lemma span_par3 {A B C} (m: cost A) (m': cost B) (m'': cost C):
  span (par3 m m' m'') = max (span m) (max (span m') (span m'')).
Proof. rewrite //=. Qed.

Lemma span_parfilter {A: eqType} (P: A → cost bool) (l: seq A) k:
  (∀ x, x \in l → span (P x) = k) →
  span (parfilter P l) =
      match l with
      | [::] => 0
      | _ => k
      end.
Proof.
  intros Hcost. induction l => //=. 
  rewrite /parfilter/parmap//= in IHl.
  rewrite addn0 in IHl. rewrite IHl.
  - rewrite addn0 Hcost; last by (rewrite in_cons eq_refl //). 
    rewrite Max.max_l => //=.
    destruct l; nify; omega.
  - intros ? Hin. eapply Hcost. rewrite in_cons. apply /orP; auto.
Qed.

Definition partition' (n: nat) (l: list nat) : 
  cost { x : splitting nat | perm_eq (lower x ++ middle x ++ upper x) l &&
                             ((n \in l) ==> (0 < size (middle x)))}.
Proof.
  refine {| work := work (partition n l);
            span := span (partition n l);
            result := exist _ (result (partition n l)) _|}.
  apply /andP; split.
  - apply partition_perm_eq.
  - apply /implyP/partition_middle_size.
Defined.

Lemma partition_work l: ∀ n, work (partition n l) = 3 * (size l).
Proof.
  intros n.
  rewrite /partition. 
  rewrite (work_mret _ ( λ x, let '(l1, l2, l3) := x in {| lower := l1;
                                                           middle := l2;
                                                           upper := l3 |})).
  rewrite work_par3 ?(work_parfilter _ _ 1); first (rewrite //=; nify; omega).
  - rewrite /gtc => x ?; rewrite (work_mret) => //=.
  - rewrite /eqc => x ?; rewrite (work_mret) => //=.
  - rewrite /ltc => x ?; rewrite (work_mret) => //=.
Qed.

Lemma partition_span a l: ∀ n, span (partition n (a :: l)) = 1.
Proof.
  intros n. rewrite /partition. 
  rewrite (span_mret _ ( λ x, let '(l1, l2, l3) := x in {| lower := l1;
                                                           middle := l2;
                                                           upper := l3 |})).
  rewrite span_par3 ?(span_parfilter _ _ 1).
  - repeat rewrite Max.max_l; nify; omega.
  - rewrite /gtc => x ?; rewrite (span_mret) => //=.
  - rewrite /eqc => x ?; rewrite (span_mret) => //=.
  - rewrite /ltc => x ?; rewrite (span_mret) => //=.
Qed.

Require Import Reals Fourier FunctionalExtensionality.

Program Definition unif n : ldist_cost { x : nat | (leq x n) } :=
  mklDist [ seq (1/(INR (n.+1)),
                {| work := 0; 
                   span := 0;
                   result := exist _ (nat_of_ord i) _|}) | i <- enum 'I_(n.+1) ] _ _.
Next Obligation. intros n (?&?). rewrite -ltnS. done. Qed.
Next Obligation. 
  intros ?.
  apply /allP => r.
  rewrite -map_comp //= (@eq_map _ _ _ (λ x, 1 / INR (S n))); last by done.
  rewrite (nat_of_ord_map_iota (S n) (λ x, 1 / INR (S n))).
  rewrite //=. induction (iota 1 n) => //=.
  - rewrite in_cons. move /orP => [Heq|Hin]; eauto.
    move /eqP in Heq. rewrite Heq. 
    destruct (Rle_dec) as [|Hn]; [ by auto | exfalso; apply Hn].
    left. apply Rdiv_lt_0_compat; first fourier.
    destruct n; first fourier.
    replace 0 with (INR O) by auto.
    cut (INR 0 < INR (S n)); intros; first by fourier.
    apply lt_INR. omega.
  - rewrite in_cons. move /orP => [Heq|Hin]; eauto.
    move /eqP in Heq. rewrite Heq. 
    destruct (Rle_dec 0 (1 / _)) as [|Hn]; [ by auto | exfalso; apply Hn].
    left. apply Rdiv_lt_0_compat; first fourier.
    destruct n; first by fourier.
    replace 0 with (INR O) by auto.
    cut (INR 0 < INR (S n)); intros; first by fourier.
    apply lt_INR; omega.
Qed.
Next Obligation.
  intros n.
  rewrite -map_comp //= (@eq_map _ _ _ (λ x, 1 / INR (S n))); last by done.
  rewrite (nat_of_ord_map_iota (S n) (λ x, 1 / INR (S n))).
  cut (∀ o k, \big[Rplus/0]_(a<-[seq (1 / INR n.+1) | i <- iota k o]) a 
            = INR (o) / INR (n.+1)).
  { 
    intros Hcut. specialize (Hcut (n.+1) O). rewrite //= in Hcut.
    rewrite Hcut. apply /eqP => //=. field. 
    apply Rgt_not_eq.
    destruct n; first fourier.
    replace 0 with (INR O) by auto.
    cut (INR 0 < INR (S n)); first by intros; fourier.
    apply lt_INR; omega.
  }
  induction o => k.
  - rewrite big_nil. replace (INR 0) with 0 by auto. rewrite /Rdiv Rmult_0_l //. 
  - rewrite big_cons. rewrite (S_INR o).
    rewrite Rdiv_plus_distr IHo. ring. 
Qed.

Program Definition draw_pivot (a : nat) (l: list nat) : ldist_cost { x : nat | x \in (a :: l) } :=
  idx ← unif (size l);
  mret (exist _ (nth O (a :: l) (sval idx)) _).
Next Obligation. intros a l (?&?). rewrite mem_nth //. Qed.

Definition qs : list nat → ldist_cost (list nat).
  refine(Fix (measure_wf lt_wf size) (fun _ => ldist_cost (list nat))
  (fun l qs => 
  match l as l' return (l = l' → ldist_cost (list nat)) with
    | [::] => λ eq, mret ([::])
    | [::a] => λ eq, mret ([::a])
    | (a :: b :: l') => λ eq, 
      p ← draw_pivot a (b :: l');
      spl ← dist_ret _ (partition' (sval p) l);
      '(lls, lus) ← rpar2 (qs (lower (sval spl)) _) (qs (upper (sval spl)) _);
      mret (lls ++ (middle (sval spl)) ++ lus)
  end (Init.Logic.eq_refl))); rewrite /MR; auto.
  - abstract (destruct spl as (spl&pf) => //=; move /andP in pf; 
    destruct pf as (pf1&pf2); move /implyP in pf2;
    rewrite -(perm_eq_size pf1) //= ?size_cat -?plusE;
    assert (0 < size (middle spl))%coq_nat by
    ( apply /ltP; apply pf2 => //=; destruct p; eauto; subst; rewrite //=); omega).
  - abstract (destruct spl as (spl&pf) => //=; move /andP in pf; 
    destruct pf as (pf1&pf2); move /implyP in pf2;
    rewrite -(perm_eq_size pf1) //= ?size_cat -?plusE;
    assert (0 < size (middle spl))%coq_nat by
    ( apply /ltP; apply pf2 => //=; destruct p; eauto; subst; rewrite //=); omega).
Defined.

Lemma easy_fix_eq:
  ∀ (A : Type) (R : A → A → Prop) (Rwf : well_founded R) (P : A → Type)
    (F : ∀ x : A, (∀ y : A, R y x → P y) → P x),
    ∀ x : A, Fix Rwf P F x = F x (λ (y : A) (_ : R y x), Fix Rwf P F y).
Proof.
  intros. apply Init.Wf.Fix_eq.
  intros. assert (f = g) as ->; last done. 
  apply functional_extensionality_dep => ?.
  apply functional_extensionality_dep => ?. done.
Qed.

Lemma qs_unfold_aux l:
  qs l =
  match l as l' return (l = l' → ldist_cost (list nat)) with
    | [::] => λ eq, mret ([::])
    | [:: a] => λ eq, mret ([:: a])
    | (a :: b :: l') => λ eq, 
      p ← draw_pivot a (b :: l');
      spl ← dist_ret _ (partition' (sval p) l);
      '(lls, lus) ← rpar2 (qs (lower (sval spl))) (qs (upper (sval spl)));
      mret (lls ++ (middle (sval spl)) ++ lus)
  end (Init.Logic.eq_refl).
Proof. rewrite /qs easy_fix_eq; done. Qed.

Lemma qs_unfold l:
  qs l = 
  (match l as l
  with
    | [::] => mret ([::])
    | [::a] => mret ([::a])
    | (a :: l) =>
      p ← draw_pivot a l;
      spl ← dist_ret _ (partition' (sval p) (a :: l));
      '(lls, lus) ← rpar2 (qs (lower (sval spl))) (qs (upper (sval spl)));
      mret (lls ++ (middle (sval spl)) ++ lus)
  end).
Proof. 
  rewrite qs_unfold_aux. destruct l => //. destruct l => //.
Qed.