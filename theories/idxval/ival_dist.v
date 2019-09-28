(* Here we consider indexed valuations that can be interpreted as probability
   distributions; that is, those in which the sum of the weights is equal to 0 *)

From discprob.basic Require Import base sval order monad.
Require Import Reals Psatz.

Require ClassicalEpsilon.
From discprob.prob Require Import double rearrange.
From mathcomp Require Import ssrfun ssreflect eqtype ssrbool seq fintype choice.
Global Set Bullet Behavior "Strict Subproofs".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype finset finfun bigop.

Local Open Scope R_scope.
From discprob.idxval Require Import ival.
From discprob.prob Require Import prob finite stochastic_order.
From discprob.prob Require Export countable.

Record ivdist X :=
  { ivd_ival :> ival X;
    val_sum1: is_series (countable_sum (val ivd_ival)) 1
  }.

Lemma val_sum1_Series {X} (I: ivdist X): Series (countable_sum (val I)) = 1.
Proof.
  apply is_series_unique, val_sum1.
Qed.

Lemma val_partial_sum_pos {X: Type} (I: ivdist X) n: 0 <= sum_n (countable_sum (val I)) n.
Proof.
  apply Rge_le, sum_n_partial_pos. rewrite /countable_sum.
  intros k. destruct pickle_inv => //=; try nra.
  apply val_nonneg.
Qed.


Arguments ivd_ival {_}.
Arguments val_sum1 {_}.

Definition dist_of_ivdist {X} (ivd: ivdist X) : distrib (idx ivd).
  refine ( {| pmf := val ivd; pmf_pos := val_nonneg ivd; pmf_sum1 := val_sum1 _ |} ).
Defined.

Definition rvar_of_ivdist {X: eqType} (ivd: ivdist X) : rvar _ X :=
  mkRvar (dist_of_ivdist ivd) (ind ivd).

Definition eq_ivd {X} (I1 I2: ivdist X) :=
  eq_ival I1 I2.

Global Instance eq_ivd_Transitivite {X}: Transitive (@eq_ivd X).
Proof. intros ???. apply eq_ival_trans. Qed.
Global Instance eq_ivd_Reflexive {X}: Reflexive (@eq_ivd X).
Proof. intros ?. apply eq_ival_refl. Qed.
Global Instance eq_ivd_Symmetry {X}: Symmetric (@eq_ivd X).
Proof. intros ??. apply eq_ival_sym. Qed.
Global Instance eq_ivd_Equivalence {X}: Equivalence (@eq_ivd X).
Proof. split; apply _. Qed. 

Global Instance ivd_ret: MRet ivdist.
refine(λ A x, {| ivd_ival := mret x;
                 val_sum1 := _ |}).
{ rewrite //=. apply: is_seriesC_bump. exact tt. }
Defined.

Section bind.
Context {A B: Type}.
Variable (f: A → ival B).
Variable (h: B → R).
Variable (rI: R).
Variable (rb: R).
Variable (I: ival A).
Local Notation prod_type :=  {i : idx I & idx (f (ind I i))}.
Definition prod_pmf (ab: {i : idx I & idx (f (ind I i))})
  := (val I (projT1 ab)) * ((h (ind (f (ind I (projT1 ab))) (projT2 ab)))) *
                             val (f (ind I (projT1 ab))) (projT2 ab).

Section double.
Variable P: pred (A * B).

Definition σprod := 
  λ n, match pickle_inv [countType of prod_type] n with
       | Some (existT a b) => (S (pickle a), S (pickle b))
       | None => (O, O)
       end.

Definition aprod := 
  λ mn, match mn with
        | (S m, S n) => 
          match (pickle_inv (idx I) m) with
          | Some a =>
            match pickle_inv (idx (f (ind I a))) n with
            |  Some b => 
                prod_pmf (existT a b)
            | None => 0
            end
          | None => 0
          end
        | _ => 0
        end.


Lemma σprod_inj: ∀ n n', aprod (σprod n) <> 0 → σprod n = σprod n' → n = n'.
Proof.
  intros n n'. rewrite /σprod/aprod.
  case_eq (pickle_inv [countType of prod_type] n); last by nra.
  case_eq (pickle_inv [countType of prod_type] n'); last first.
  { intros Heq_none (a&b) Heq_some => //=. }
  intros (a'&b') Heq' (a&b) Heq Hneq0 => //=. 
  inversion 1 as [[Hp1 Hp2]].
  assert (a = a').
  { 
    apply (f_equal (pickle_inv (idx I))) in Hp1. rewrite ?pickleK_inv in Hp1.
    inversion Hp1; done.
  }
  subst.
  assert (b = b').
  { 
    apply (f_equal (pickle_inv (idx (f (ind I a'))))) in Hp2. rewrite ?pickleK_inv in Hp2.
    inversion Hp2; done.
  }
  subst.
  apply (f_equal (oapp (@pickle _) n)) in Heq.
  apply (f_equal (oapp (@pickle _) n')) in Heq'.
  rewrite ?pickle_invK //= in Heq Heq'. congruence.
Qed.

Lemma σprod_cov: ∀ n, aprod n <> 0 → ∃ m, σprod m = n.
Proof.
  intros (n1&n2).
  destruct n1, n2 => //=.
  rewrite /countable_sum.
  case_eq (pickle_inv (idx I) n1) => //=; [].
  intros a Heq1.
  case_eq (pickle_inv (idx (f (ind I a))) n2) => //=; [].
  intros b Heq2 => Hneq0.
  exists (@pickle [countType of prod_type] (existT a b)).
  rewrite /σprod pickleK_inv. repeat f_equal.
  - apply (f_equal (oapp (@pickle _) n1)) in Heq1. rewrite pickle_invK //= in Heq1.
  - apply (f_equal (oapp (@pickle _) n2)) in Heq2. rewrite pickle_invK //= in Heq2.
Qed.


Section double1.
Variable (HIval_sum1: is_series (countable_sum (val I)) rI).
Variable (Hf_sum_bounded:
   ∀ i, val I i > 0 →
    ∃ (v: R), is_series (countable_sum (λ i', Rabs (h (ind (f (ind I i)) i')
                                               * val (f (ind I i)) i'))) v ∧
                                    v <= rb).
Lemma aprod_double_summable: double_summable aprod.
Proof.
  exists (Rmax 1 (Rabs rb * Rabs rI)) => n. 
  destruct n.
  * rewrite ?sum_O //= Rabs_R0. apply Rmax_case_strong; nra.
  * transitivity
      (sum_n (λ j : nat, match j with
                         | O => 0
                         | S j => countable_sum (λ i, val I i * Rabs rb) j
                         end) (S n)).
    { rewrite ?sum_n_bigop.
      rewrite -(big_mkord (λ x, true) (λ i, sum_n (λ k, Rabs (aprod (i, k))) (S n))).
      rewrite -(big_mkord (λ x, true)
                          (λ i, match i with
                                  O => 0
                                | S i => countable_sum (λ i, val I i * Rabs rb) i
                                end)). 
      apply Rle_bigr.

      intros i ?.
      rewrite //=. destruct i => //=.
      {
        rewrite ?sum_n_bigop.
        right.  rewrite Rabs_R0. rewrite big1 //=. }
      rewrite sum_nS /plus//=Rabs_R0 Rplus_0_l.
      rewrite /countable_sum//=.
      destruct (pickle_inv (idx I) i) as [a|]; last first.
      { rewrite Rabs_R0. rewrite sum_n_const Rmult_0_r.
        rewrite /countable_sum//=.
        nra. }
      rewrite //=.
      transitivity (sum_n (λ n, val I a * countable_sum (λ i, Rabs (h (ind (f (ind I a)) i))
                                                              * val (f (ind I a)) i) n) n).
      { right. apply sum_n_ext => k. rewrite /countable_sum//=.
        destruct pickle_inv => //=.
        * rewrite /prod_pmf//= ?Rabs_mult Rmult_assoc; f_equal.
          ** apply Rabs_right, val_nonneg. 
          ** f_equal. apply Rabs_right, val_nonneg. 
        * rewrite Rabs_R0; nra.
      }
      rewrite sum_n_mult_l /mult//=.
      destruct (val_nonneg I a) as [Hgt|Heq0]; last first.
      { rewrite Heq0. nra. } 
      apply Rmult_le_compat_l.
      { apply Rge_le, val_nonneg.  }
      edestruct (Hf_sum_bounded a) as (r'&His&Hlt); auto.
      transitivity r'; last first.
      { transitivity rb; eauto. apply Rabs_case; nra. }
      eapply seriesC_partial_sum_bounded.
      * eapply is_seriesC_ext; last eassumption.
        intros => //=. rewrite Rabs_mult; f_equal. apply Rabs_right, val_nonneg.
      * intros x. specialize (val_nonneg (f (ind I a)) x). intros. apply Rabs_case; nra.
    }
    rewrite sum_nS /plus//= Rplus_0_l.
    transitivity (scal (Rabs rb) (sum_n (countable_sum (val I)) n)).
    { right. rewrite -sum_n_scal_l.
      apply sum_n_ext => k. rewrite /countable_sum//=. destruct (pickle_inv) => //=;
      rewrite /scal//=/mult//=; nra.
    }
    rewrite /scal//=/mult//=.
    etransitivity; last apply Rmax_r.
    apply Rmult_le_compat_l; first by (apply Rabs_case; nra).
    transitivity rI; last by (apply Rabs_case; nra).
    apply val_partial_sum_bounded; eauto.
Qed.
End double1.

(* this is phrased in a funny way... *)
Section double2.
Variable (DS: double_summable aprod).

Lemma ex_series_prod_abs_row:
  ex_series (λ j, Series (λ k, Rabs (aprod (S j, S k)))).
Proof.
  rewrite -(ex_series_incr_1 (λ j, Series (λ k, Rabs (aprod (j, k.+1))))).
  eapply ex_series_ext; last first.
  { eexists;
      eapply (series_double_covering_Rabs _ _ σprod_inj σprod_cov DS); eauto. }
  intros n. 
  rewrite [a in a = _]Series_incr_1; last first.
  {
    eapply ex_series_row, DS.
  }
  rewrite -[a in _ = a]Rplus_0_l; f_equal.
  rewrite //=. destruct n; auto using Rabs_R0.
Qed.

Lemma ex_series_prod_row:
  ex_series (λ j, Series (λ k, aprod (S j, S k))).
Proof.
  rewrite -(ex_series_incr_1 (λ j, Series (λ k, aprod (j, k.+1)))).
  eapply ex_series_ext; last first.
  { eexists;
      eapply (series_double_covering _ _ σprod_inj σprod_cov DS); eauto. }
  intros n. 
  rewrite [a in a = _]Series_incr_1; last first.
  {
    eapply ex_series_Rabs. eapply ex_series_row, DS.
  }
  rewrite -[a in _ = a]Rplus_0_l; f_equal.
  rewrite //=. destruct n; auto.
Qed.

Lemma is_series_prod_row:
  is_series (countable_sum prod_pmf)
            (Series (λ j, Series (λ k, aprod (S j, S k)))).
Proof.
  apply (is_series_ext (aprod \o σprod)).
  { 
    intros n. rewrite /aprod/σprod/countable_sum/prod_pmf//=.
    destruct (pickle_inv _) as [s|] => //=.
    destruct s as (a0, b0) => //=.
    rewrite ?pickleK_inv //=.
  }
  eapply (is_series_chain _ _ _
                          (series_double_covering' _ _ σprod_inj σprod_cov DS)).
  cut (Series (λ j, Series (λ k, aprod (j, k))) =
      (Series (λ j : nat, Series (λ k : nat, aprod (S j, S k))))).
  { 
    intros <-. apply Series_correct. 
    eexists; eapply (series_double_covering _ _ σprod_inj σprod_cov DS); eauto.
  }
  rewrite Series_incr_1; last first.
  { eexists; eapply (series_double_covering _ _ σprod_inj σprod_cov DS); eauto. }
  rewrite {1}/aprod Series_0 // Rplus_0_l.
  apply Series_ext => n.
  rewrite Series_incr_1; last first.
  { apply ex_series_Rabs, ex_series_row, DS. }
  rewrite {1}/aprod Rplus_0_l => //=.
Qed.

Lemma Series_prod_row:
  Series (countable_sum (prod_pmf)) =
  (Series (λ j, Series (λ k, aprod (S j, S k)))).
Proof.
  apply is_series_unique, is_series_prod_row.
Qed.

Lemma prod_series_ext:
  ∀ n : nat,
  (λ j : nat, Series (λ k : nat, aprod (j.+1, k.+1))) n =
  countable_sum
    (λ i : idx I,
     Series
       (countable_sum (λ i' : idx (f (ind I i)), h (ind (f (ind I i)) i') * val (f (ind I i)) i')) *
     val I i) n.
Proof.
  intros n. rewrite /countable_sum//=/oapp.
  destruct (pickle_inv); last by apply Series_0.
  rewrite -Series_scal_r.
  eapply Series_ext => m.
  destruct pickle_inv => //=; last by nra.
  rewrite /prod_pmf//=. nra.
Qed.

Lemma prod_abs_series_ext:
  ∀ n : nat,
  (λ j : nat, Series (λ k : nat, Rabs (aprod (j.+1, k.+1)))) n =
  countable_sum
    (λ i : idx I,
     Series
       (countable_sum (λ i' : idx (f (ind I i)), Rabs (h (ind (f (ind I i)) i')) * val (f (ind I i)) i')) *
     val I i) n.
Proof.
  intros n. rewrite /countable_sum//=/oapp.
  destruct (pickle_inv); last first.
  { setoid_rewrite Rabs_R0. 
    by apply Series_0. }
  rewrite -Series_scal_r.
  eapply Series_ext => m.
  destruct pickle_inv => //=; last first.
  { rewrite Rabs_R0; nra. }
  rewrite /prod_pmf//= ?Rabs_mult ?Rabs_val. nra.
Qed.

Lemma ex_series_pmf_abs_each_row i:
  ex_series (countable_sum (λ i', Rabs (h (ind (f (ind I i)) i')
                                  * val (f (ind I i)) i' * val I i))).
Proof.
  eapply (ex_series_ext (λ k, Rabs (aprod (S (pickle i), S k)))) ; last first.
  {
    rewrite -(ex_series_incr_1 (λ k, Rabs (aprod (S (pickle i), k)))).
    eapply (ex_series_row aprod), DS.
  }
  { intros n. rewrite //=. rewrite /countable_sum => //=.
    rewrite ?pickleK_inv. rewrite /oapp.
    destruct pickle_inv; rewrite /prod_pmf //=.
    { f_equal; nra. }
    { rewrite Rabs_R0 //. }
  }
Qed.

Lemma ex_series_pmf_abs_row:
   ex_series (countable_sum (λ i, Rabs (Series (countable_sum (λ i', h (ind (f (ind I i)) i')
                             * val (f (ind I i)) i'))) * val I i)).
Proof.
  apply: ex_series_le; last first.
  { apply ex_series_prod_abs_row. }
  intros n. rewrite norm_Rabs.
  rewrite Rabs_right; last first.
  { apply Rle_ge. rewrite /countable_sum/oapp.
    destruct pickle_inv; last reflexivity.
    apply Rmult_le_0_compat.
    * apply Rabs_pos.
    * apply Rge_le, val_nonneg.
  }
  rewrite /countable_sum//=/oapp.
  destruct (pickle_inv) as [i|]; last first.
  { rewrite Series_0; auto using Rabs_R0. nra. }
  replace (val I i) with (Rabs (val I i)); last by (auto using Rabs_right, val_nonneg).
   rewrite -Rabs_mult.
  rewrite -Series_scal_r.
  setoid_rewrite Series_Rabs.
  - right.
    eapply Series_ext => m.
    f_equal.
    destruct pickle_inv => //=; last by nra.
    rewrite /prod_pmf//=. nra.
  - eapply ex_series_ext; last eapply (ex_series_pmf_abs_each_row i).
    intros n'. rewrite /countable_sum/oapp.
    destruct pickle_inv; last first.
    { rewrite Rmult_0_l Rabs_R0. done. }
    done.
Qed.

Lemma ex_series_pmf_row:
   ex_series (countable_sum (λ i, (Series (countable_sum (λ i', h (ind (f (ind I i)) i')
                             * val (f (ind I i)) i'))) * val I i)).
Proof.
  eapply ex_series_ext; last first.
  { apply ex_series_prod_row. }
  { apply prod_series_ext. }
Qed.

Lemma prod_pmf_sum:
   is_series (countable_sum (prod_pmf))
             (Series (countable_sum (λ i, (Series (countable_sum (λ i', h (ind (f (ind I i)) i')
                                     * val (f (ind I i)) i'))) * val I i))).
Proof.
  intros.
  eapply (is_series_chain).
  { eapply is_series_prod_row. }
  apply Series_correct'; last first.
  { apply ex_series_prod_row. }
  { eapply Series_ext, prod_series_ext. }
Qed.

Lemma prod_pmf_pos_sum1
    (HIval_sum1: is_series (countable_sum (val I)) rI)
      (Hf_sum1:
   ∀ i, val I i > 0 →
    is_series (countable_sum (λ i', (h (ind (f (ind I i)) i'))
                                               * val (f (ind I i)) i')) 1):
   rI = 1 →
  is_series (countable_sum (prod_pmf)) 1.
Proof.
  intros.
  eapply (is_series_chain).
  { eapply is_series_prod_row. }
  rewrite //=.
  eapply (is_series_ext (countable_sum (val I))). 
  { intros n.
    rewrite /countable_sum//=. destruct pickle_inv as [a|]; last first.
    { rewrite //=. by rewrite Series_0. }
    rewrite //=.
    rewrite -(Series_ext (λ k, val I a * countable_sum (λ i',
                                                        (h (ind (f (ind I a)) i')) *
                                             val (f (ind I a)) i') k)); last first.
    { intros m. rewrite /countable_sum. destruct (pickle_inv) => //=;
      rewrite /prod_pmf//=; nra. }
    rewrite Series_scal_l.
    destruct (val_nonneg I a) as [Hgt|Heq0]; last first.
    { rewrite ?Heq0.  nra. }
    specialize (Hf_sum1 _ Hgt).
    apply is_series_unique in Hf_sum1. rewrite Hf_sum1 Rmult_1_r. done.
  }
  subst.
  eauto.
Qed.
End double2.


Section double3.
Variable (HEX: ex_series (countable_sum (λ c, Rabs (prod_pmf c)))).

Lemma prod_pmf_sum_inv_ds:
  double_summable aprod.
Proof.
  eapply pre_converge.summable_implies_ds; eauto.
  { apply σprod_inj. }
  { apply σprod_cov. }
  { eapply ex_series_ext; last eassumption. 
    intros n. rewrite /aprod/σprod/countable_sum/prod_pmf//=.
    destruct (pickle_inv _) as [s|] => //=.
    destruct s as (a0, b0) => //=.
    rewrite ?pickleK_inv //=.
    rewrite Rabs_R0. done.
  }
Qed.

Lemma prod_pmf_sum_inv:
  is_series (countable_sum (prod_pmf))
            (Series (countable_sum (λ i, (Series (countable_sum (λ i', h (ind (f (ind I i)) i')
                                     * val (f (ind I i)) i'))) * val I i))).
Proof.
  intros.
  eapply prod_pmf_sum, prod_pmf_sum_inv_ds.
Qed.
End double3.

Section double4.
Variable (HIval_sum1: is_series (countable_sum (val I)) rI).
Variable (Habs_each_row: ∀ i,
             val I i > 0 →
  ex_series (countable_sum (λ i', Rabs (h (ind (f (ind I i)) i')
                                  * val (f (ind I i)) i')))). (* * val I i)))). *)

Variable (Hex_series: 
            ex_series (countable_sum (λ i, (Series (countable_sum (λ i', h (ind (f (ind I i)) i')
                                     * val (f (ind I i)) i'))) * val I i))).
Variable (Hhpos: ∀ x, h x >= 0).

Lemma prod_pmf_sum_by_row_ds1:
  ∀ j : nat, ex_series (λ k : nat, Rabs (aprod (j, k))).
Proof.
  * intros j. destruct j.
    ** rewrite //=. setoid_rewrite Rabs_R0.
       eapply ex_series_eventually0. exists O; eauto.
    ** eapply ex_series_incr_1.
       rewrite /aprod. destruct (pickle_inv (idx I) j) as [s|]; last 
       (by setoid_rewrite Rabs_R0; eapply ex_series_eventually0; exists O; eauto).
       destruct (val_nonneg I s) as [Hgt|Heq0]; last first.
       { eapply (ex_series_ext (λ _, 0)).
         * intros n. rewrite /prod_pmf; destruct pickle_inv => //=.
           ** rewrite Heq0 ?Rmult_0_l Rabs_R0 //=.
           ** rewrite Rabs_R0 //=.
         * eapply ex_series_eventually0; exists O; eauto.
       }
       specialize (Habs_each_row s Hgt).
       apply (ex_seriesC_scal_l _ (val I s)) in Habs_each_row.
       eapply ex_series_ext; last eapply (Habs_each_row); eauto.
       intros n. rewrite /countable_sum.
       destruct pickle_inv => //=.
       *** rewrite /prod_pmf ?Rabs_mult ?Rabs_val //=.
           nra.
       *** rewrite Rabs_R0 //=.
Qed.

Lemma prod_pmf_sum_by_row_ds:
  double_summable aprod.
Proof.
  eapply ex_series_rows_ds.
  * apply prod_pmf_sum_by_row_ds1.
  * apply ex_series_incr_1.
    eapply ex_series_ext.
    { intros n.  rewrite Series_incr_1; last eapply prod_pmf_sum_by_row_ds1.
      rewrite {1}/aprod Rabs_R0 Rplus_0_l. done. }
    intros. setoid_rewrite prod_abs_series_ext.
    eapply ex_seriesC_ext; try eassumption.
    intros n => //=. f_equal.
    eapply SeriesC_ext.
    intros m => //=. f_equal.
    rewrite Rabs_right; eauto.
Qed.

Lemma prod_pmf_sum_by_row:
  is_series (countable_sum (prod_pmf))
            (Series (countable_sum (λ i, (Series (countable_sum (λ i', h (ind (f (ind I i)) i')
                                     * val (f (ind I i)) i'))) * val I i))).
Proof.
  intros.
  eapply prod_pmf_sum, prod_pmf_sum_by_row_ds.
Qed.
End double4.

End double.

End bind.

Lemma ivd_bind_sum1'
  {A : Type}
  {B : Type}
  (f : A → ival B)
  (I : ival A)
  (HIval_sum1: is_series (countable_sum (val I)) 1)
  (Hfval_sum1: ∀ i, val I i > 0 → is_series (countable_sum (val (f (ind I i)))) 1):
  is_series (countable_sum (val (ival_bind _ _ (λ x : A, f x) I))) R1.
Proof.
  rewrite //=.
  eapply is_seriesC_ext; last first.
  * eapply (@prod_pmf_pos_sum1 A B f (λ _, 1) 1 I); eauto using val_sum1.
    { unshelve (eapply aprod_double_summable; eauto).
      { exact 1.  }
      { intros. exists 1; split.
        ** eapply is_seriesC_ext; try eapply Hfval_sum1; eauto.
           intros n. rewrite Rmult_1_l Rabs_right; auto using val_nonneg, Rle_ge.
        ** nra.
      }
    }
    { intros; eapply is_seriesC_ext; try eapply Hfval_sum1; eauto. intros; field. }
  * intros n. rewrite /prod_pmf//=; field.
Qed.

Lemma ivd_bind_sum1
  {A : Type}
  {B : Type}
  (f : A → ivdist B)
  (I : ivdist A):
  is_series (countable_sum (val (ival_bind _ _ (λ x : A, f x) I))) R1.
Proof.
  rewrite //=. eapply (ivd_bind_sum1' (λ a, ivd_ival (f a)) I) => //=; eauto using val_sum1.
Qed.

Global Instance ivd_bind: MBind ivdist.
refine(λ A B f I, {| ivd_ival := mbind (λ x, ivd_ival (f x)) (ivd_ival I);
                     val_sum1 := ivd_bind_sum1 _ _ |}).
Defined.

Global Instance ivd_bind_proper X Y :
  Proper (pointwise_relation X (@eq_ivd Y) ==> @eq_ivd X ==> @eq_ivd Y) (ivd_bind X Y).
Proof. intros ?? ? ?? ?. eapply ibind_proper; eauto. Qed. 

Lemma ivd_assoc {A B C} (m: ivdist A) (f: A → ivdist B) (g: B → ivdist C) :
  eq_ivd (mbind g (mbind f m)) (mbind (λ x, mbind g (f x)) m).
Proof.
  rewrite /eq_ivd. setoid_rewrite ival_assoc. reflexivity.
Qed.

Lemma ivd_left_id {A B: Type} (x: A) (f: A → ivdist B):
  eq_ivd (mbind f (mret x)) (f x).
Proof.
  rewrite /eq_ivd. setoid_rewrite ival_left_id. reflexivity.
Qed.

Lemma ivd_right_id {A: Type} (m: ivdist A):
  eq_ivd (mbind mret m) m.
Proof.
  rewrite /eq_ivd. setoid_rewrite ival_right_id. reflexivity.
Qed.

Lemma ivd_bind_congr {A B} (m1 m2: ivdist A) (f1 f2: A → ivdist B) :
  eq_ivd m1 m2 →
  (∀ a, eq_ivd (f1 a) (f2 a)) →
  eq_ivd (x ← m1; f1 x) (x ← m2; f2 x).
Proof. 
  intros Hlem Hlef.
  rewrite /eq_ivd.
  apply ival_bind_congr; eauto.
Qed.

Lemma ivdplus_sum1 {X} (p: R) (Hrange: 0 <= p <= 1) (I1 I2: ivdist X) :
  is_series (countable_sum (val (iplus (iscale p I1) (iscale (1 - p) I2)))) R1.
Proof.
  assert (iequip:
            is_series (countable_sum (val (iplus (iscale p (mret true))
                                                 (iscale (1 - p) (mret false))))) 1).
  { 
    eapply Series_correct'.
    { rewrite SeriesC_SeriesF.
      rewrite SeriesF_big_op.
      rewrite /index_enum {1}[@Finite.enum]unlock //= /sum_enum //=.
      rewrite ?[@Finite.enum]unlock //= /sum_enum //=.
      rewrite ?big_cons ?big_nil => //=.
      rewrite ?Rabs_right; nra.
    }
    { eexists. eapply SeriesF_is_seriesC. }
  }
  eapply (eq_ival_series (ivd_ival (x ← {| ivd_ival := (iplus (iscale p (mret true))
                                                    (iscale (1 - p) (mret false)));
                                 val_sum1 := iequip |};
                                    if x then I1 else I2))).
  {
    transitivity (x ← iplus (iscale p (mret true)) (iscale (1 - p) (mret false));
                  if x then (ivd_ival I1) else (ivd_ival I2)).
    { rewrite //=. eapply ival_bind_congr.
      * apply eq_ival_quasi_refl.
      * intros [|]; reflexivity.
    }
    rewrite ival_plus_bind. apply iplus_proper.
   * rewrite ival_scale_bind ival_left_id. reflexivity.
   * rewrite ival_scale_bind ival_left_id. reflexivity.
  }
  eapply val_sum1.
Qed.

Definition ivdplus {X} (p: R) (Hrange: 0 <= p <= 1) (I1 I2: ivdist X) : ivdist X.
Proof.
  refine {| ivd_ival := iplus (iscale p I1) (iscale (1 - p) I2) |}.
  apply ivdplus_sum1; auto.
Defined.

Lemma ivdist_plus_proper:
  ∀ (X : Type) r Hpf Hpf' (I1 I1' I2 I2': ivdist X),
    eq_ivd I1 I1' →
    eq_ivd I2 I2' →
    eq_ivd (ivdplus r Hpf I1 I2) (ivdplus r Hpf' I1' I2').
Proof.
  intros X r Hpf Hpf' Is1 Is1' Is2 Is2' Hle1 Hle2.
  rewrite /eq_ivd/ivdplus//=.
  rewrite /eq_ivd in Hle1, Hle2.
  setoid_rewrite Hle1. setoid_rewrite Hle2.
  reflexivity.
Qed.

Global Instance ivdist_plus_proper_instance:
  ∀ (X : Type) r Hpf, Proper (@eq_ivd X ==> @eq_ivd X ==> @eq_ivd X) (ivdplus r Hpf).
Proof.
  intros X r Hpf Is1 Is1' Hle1 Is2 Is2' Hle2.
  apply ivdist_plus_proper; eauto.
Qed.

Lemma ivdplus_comm {X} (p: R) Hpf Hpf' (I1 I2: ivdist X) :
  eq_ivd (ivdplus p Hpf I1 I2) (ivdplus (1 - p) Hpf' I2 I1).
Proof.
  rewrite /eq_ivd/ivdplus//=.
  replace (1 - (1 - p)) with p by nra.
  apply iplus_comm.
Qed.

Lemma ivdplus_eq_ival {X} p Hpf (I1 I1' I2 I2': ivdist X):
  eq_ivd I1 I1' →
  eq_ivd I2 I2' →
  eq_ival (ivdplus p Hpf I1 I2) (ivdplus p Hpf I1' I2').
Proof.
  rewrite /eq_ivd/ivdplus => Heq1 Heq2 //=.
  setoid_rewrite Heq1.
  setoid_rewrite Heq2.
  reflexivity.
Qed.


Lemma ivd_plus_bind:
  ∀ (A B : Type) p Hpf (m1 m2 : ivdist A) (f : A → ivdist B),
    eq_ivd (x ← ivdplus p Hpf m1 m2; f x) (ivdplus p Hpf (x ← m1; f x) (x ← m2; f x)).
Proof.
  intros A B p Hpf m1 m2 f.
  rewrite /eq_ivd. rewrite /ivdplus/ivd_bind.
  setoid_rewrite ival_plus_bind.
  setoid_rewrite ival_scale_bind.
  reflexivity.
Qed.
  
(* TODO: finite distributions can be regarded as ivdists. *)

(*
Lemma pr_rvar_ivdist {A: eqType} (ivd: ivdist A) r :
  pr_eq (rvar_of_ivdist ivd) r = \big[Rplus/0%R]_(a | ind ivd a == r) val ivd a.
Proof. 
  rewrite /pr_eq/pr. 
  rewrite SeriesC_fin_big -big_mkcondr.
  rewrite /dist_of_ivdist //=.
Qed.
*)

Lemma eq_ivdist_Series {X} (I1 I2: ivdist X) P:
  eq_ival I1 I2 →
  Series (countable_sum (λ i, if P (ind I1 i) then val I1 i else 0)) =
  Series (countable_sum (λ i, if P (ind I2 i) then val I2 i else 0)).
Proof.
  intros Heq.
  eapply is_series_unique.
  eapply eq_ival_series_pred; first by (symmetry; eauto).
  apply Series_correct.
  apply ex_seriesC_filter_P.
  { apply val_nonneg. }
  { exists 1. apply val_sum1. }
Qed.

(*
Lemma eq_ival_sum {X} (I1 I2: ival X) P:
  eq_ival I1 I2 →
  \big[Rplus/0]_(i | P (ind I1 i)) (val I1 i) = 
  \big[Rplus/0]_(i | P (ind I2 i)) (val I2 i). 
Proof.
  intros Heq.
  transitivity (\big[Rplus/0]_(i : support (val I1) | P (ind I1 (sval i))) (val I1 (sval i))).
  - symmetry.  rewrite /index_enum. apply sum_reidx_map with (h := sval) => //=.
    * intros (a&Hgt) ?? => //=. rewrite -enumT mem_enum //=.
    * intros b _ HP Hneq. specialize (val_nonneg I1 b).
      destruct 1 as [Hgt|Heq0]; auto.
      exfalso. apply Hneq.
      exists (coerce_supp _ _ Hgt); repeat split; auto.
      rewrite -enumT mem_enum //=.
    * rewrite -enumT. apply enum_uniq.
    * rewrite -enumT. apply enum_uniq.
    * intros. by apply sval_inj_pred.
  - destruct Heq as (h1&h2&Hh12&Hh21&Hind&Hval).
    rewrite /index_enum. apply sum_reidx_map with (h := λ x, sval (h1 x)).
    * intros (a&Hgt) ? => //=. rewrite Hval. done.
    * intros (a&Hgt) ?? => //=. split; first by rewrite -enumT mem_enum //=.
      rewrite Hind. done.
    * intros b _ HP Hneq. specialize (val_nonneg I2 b).
      destruct 1 as [Hgt|Heq0]; auto.
      exfalso. apply Hneq.
      exists (h2 (coerce_supp _ _ Hgt)); repeat split; auto.
      ** rewrite -enumT mem_enum //=.
      ** rewrite -Hind Hh21. done.
      ** rewrite Hh21 //=.
    * rewrite -enumT. apply enum_uniq.
    * rewrite -enumT. apply enum_uniq.
    * intros x x' _ ?%sval_inj_pred.
      rewrite -(Hh12 x).
      rewrite -(Hh12 x').
      congruence.
Qed.
*)

Lemma eq_ivdist_eq_dist {A: eqType} (ivd1 ivd2: ivdist A):
  eq_ivd ivd1 ivd2 →
  eq_dist (rvar_of_ivdist ivd1) (rvar_of_ivdist ivd2).
Proof.
  intros Heq_ivd a.
  rewrite /pr_eq/pr//=.
  eapply (eq_ivdist_Series _ _ (λ x, x == a) Heq_ivd).
Qed.

(*
Lemma pr_gt_rvar_ivdist (ivd: ivdist R) r :
  pr_gt (rvar_of_ivdist ivd) r = \big[Rplus/0%R]_(a | Rgt_dec (ind ivd a) r) val ivd a.
Proof. 
  rewrite /pr_gt/pr. 
  rewrite SeriesC_fin_big -big_mkcondr.
  rewrite /dist_of_ivdist //=.
Qed.
*)

(*
Lemma pr_mbind_ivdist {A B: eqType} (h: ivdist A) (f: A → ivdist B) (b: B) :
  pr_eq (rvar_of_ivdist (mbind f h)) b = 
  \big[Rplus/0]_(a : imgT (rvar_of_ivdist h)) 
   (pr_eq (rvar_of_ivdist h) (sval a) * pr_eq (rvar_of_ivdist (f (sval a))) b).
Proof.
  transitivity (Ex (rvar_comp (rvar_of_ivdist h) (λ a, pr_eq (rvar_of_ivdist (f a)) b))); last first.
  { rewrite Ex_fin_comp. eapply eq_bigr => ??. field. }  
  rewrite pr_rvar_ivdist Ex_fin_pt.
  symmetry. etransitivity.
  { apply eq_bigr => ?? /=. rewrite !pr_rvar_ivdist. done. } 
  rewrite //=.
  symmetry.
  rewrite /index_enum {1}[@Finite.enum]unlock /tag_enum big_flatten.
  rewrite big_map //= big_seq_cond.
  eapply eq_big.
  { intros i => //=. rewrite -enumT mem_enum //=. }
  intros i. rewrite andb_true_r => Hin.
  rewrite big_map //=.
  rewrite -big_distrr //=. nra.
Qed.
*)

(*
Lemma img_rvar_of_ivdist {A: eqType} (h: ivdist A):
  map sval (Finite.enum [finType of (imgT (rvar_of_ivdist h))]) = undup [seq i.2 | i <- h].
Proof.  
  rewrite {1}[@Finite.enum]unlock //=. rewrite img_fin_enum_sval.
  assert (a: A).
  { destruct h as (l, pf1, pf2). destruct l.
    - rewrite big_nil in pf2. move /eqP in pf2. exfalso.
      rewrite //= in pf2. fourier.
    - exact (snd p).
  }
  f_equal.
  etransitivity.
  - apply (@eq_map _ _ _ (λ n, nth a [seq i.2 | i <- h] (nat_of_ord n))).
    { intro i. erewrite set_nth_default; auto. rewrite size_map. done. }
  - rewrite -enumT. rewrite (nat_of_ord_map_iota (size h) (λ n, nth a [seq (snd i) | i <- h] n)). 
  destruct h as (l, pf1, pf2) => //=; clear pf1 pf2.
  rewrite -(size_map snd l) map_nth_iota //.
Qed.
*)

(*
Lemma Ex_mbind_ivdist {A: eqType} (h: ivdist A) (f: A → ivdist R) :
  Ex (rvar_of_ivdist (mbind f h)) = 
  \big[Rplus/0]_(a : imgT (rvar_of_ivdist h)) 
   (pr_eq (rvar_of_ivdist h) (sval a) * Ex (rvar_of_ivdist (f (sval a)))).
Proof.
  rewrite /Ex SeriesC_fin_big.
  f_equal. etransitivity.
  { eapply eq_bigr => x _. rewrite pr_mbind_ivdist. rewrite big_distrl /=.
    eapply eq_bigr => ? _. rewrite /=. rewrite Rmult_assoc //. }
  rewrite exchange_big.
  apply eq_bigr => x _.
  rewrite SeriesC_fin_big //=.
  rewrite -big_distrr //=. 
  f_equal.
  rewrite /index_enum//=.
  rewrite -(big_map sval (λ x, true) (λ i, pr_eq _ i * i)).
  rewrite -(big_map sval (λ x, true) (λ i, pr_eq _ i * i)).
  rewrite bigop_cond_non0.
  rewrite [a in _ = a]bigop_cond_non0.
  rewrite -big_filter.
  rewrite -[a in _ = a]big_filter.
  eapply eq_big_perm.
  apply uniq_perm_eq.
  { apply filter_uniq. rewrite map_inj_in_uniq; last first.
    - intros ? ? => //=. intros. by apply sval_inj_pred.
    - rewrite  {1}[@Finite.enum]unlock //=. apply img_fin_uniq.
  }
  { 
    apply filter_uniq.
    rewrite map_inj_in_uniq; last first.
    { intros ? ? => //=. intros. by apply sval_inj_pred. }
    rewrite  {1}[@Finite.enum]unlock //=. apply img_fin_uniq.
  }
  destruct x as (x&Hinx).
  rewrite //=.
  rewrite img_alt in Hinx * => [[ih Heqx]].
  
  intros r0.
  rewrite ?mem_filter.
  apply andb_id2l. move /eqP => Hneq0.

  apply /mapP.
  case: ifP.
  - move /mapP.
    intros [r Hin]. subst.
    destruct r as (r&Hin').
    clear Hin. rewrite //=. rewrite //= in Hneq0. rewrite img_alt in Hin' *.
    intros (ifx&Heqr).
    eexists.
    { Unshelve. all: swap 1 2.
      { exists r. rewrite img_alt.
        exists (existT ih ifx).
        rewrite Heqr //.
      }
      rewrite //=.
      rewrite  {1}[@Finite.enum]unlock //=.
      apply img_fin_mem.
    }
    rewrite //=.
  - move /negP => Hfalse.
    exfalso. apply Hfalse.
    apply /mapP.
    assert (Hpr0: pr_eq (rvar_of_ivdist (f x)) r0 ≠ 0).
    { clear -Hneq0. intros Heq0. rewrite Heq0 in Hneq0. nra. }
    apply pr_img0 in Hpr0.
    rewrite  {1}[@Finite.enum]unlock //=.
    rewrite //= in Hpr0.
    exists (exist _ r0 Hpr0); auto.
    apply img_fin_mem. 
Qed.
*)


(*
Lemma pr_eq_ivdplus {A: eqType} p Hpf ( I1 I2: ivdist A) (a: A):
  pr_eq (rvar_of_ivdist (ivdplus p Hpf I1 I2)) a =
  p * pr_eq (rvar_of_ivdist I1) a + (1 - p) * pr_eq (rvar_of_ivdist I2) a.
Proof.
  rewrite ?pr_rvar_ivdist.
  rewrite /index_enum {1}[@Finite.enum]unlock /sum_enum big_cat ?big_map //= -?big_distrr //=.
  rewrite ?Rabs_right;  nra.
Qed.

Lemma Ex_ivdplus p Hpf (I1 I2: ivdist R):
  Ex (rvar_of_ivdist (ivdplus p Hpf I1 I2)) =
  p * Ex (rvar_of_ivdist I1) + (1 - p) * Ex (rvar_of_ivdist I2).
Proof.
  rewrite ?Ex_fin_pt.
  rewrite //=.
  rewrite /index_enum {1}[@Finite.enum]unlock /sum_enum big_cat ?big_map //= -?big_distrr //=.
  rewrite ?big_distrr => //=.
  f_equal.
  - eapply eq_bigr => ??. rewrite Rabs_right; nra.
  - eapply eq_bigr => ??. rewrite Rabs_right; nra.
Qed.

Lemma primitive_ivdplus {X} p HPf (I1 I2: ivdist X):
  ival_primitive I1 →
  ival_primitive I2 →
  ¬ (∃ i1 i2, ind I1 i1 = ind I2 i2) →
  ival_primitive (ivdplus p HPf I1 I2).
Proof.
  intros Hprim1 Hprim2 Hdisj ia ib.
  destruct ia, ib => //=.
  - intros Heq. f_equal. apply Hprim1; eauto.
  - intros Heq. exfalso; eapply Hdisj; eauto.
  - intros Heq. exfalso; eapply Hdisj; eauto.
  - intros Heq. f_equal. apply Hprim2; eauto.
Qed.
*)
  
Lemma primitive_ivdplus_mret {X} p HPf (x1 x2: X):
  x1 ≠ x2 →
  ival_primitive (ivdplus p HPf (mret x1) (mret x2)).
Proof. intros ? [[]|[]] [[]|[]] => //=; intros; try f_equal; try congruence. Qed.

Lemma ivd_support_idx {X} (I: ivdist X) : {i : idx I | val I i > 0 }.
Proof.
  destruct I as ([idx ind val]&Hval).
  revert Hval.
  assert (1 > 0) as Hgt by nra.
  revert Hgt.
  rewrite //=.
  rewrite /index_enum.
  generalize 1.
  intros r Hgt0 Hseries.
  cut (∃ i : idx, val i > 0).
  { intros ?%ClassicalEpsilon.constructive_indefinite_description. done. }

  apply Classical_Pred_Type.not_all_not_ex.
  intros Hnot_gt.
  assert (r = 0); last by nra.
  { cut (is_series (countable_sum val) 0).
    { intros Heq. transitivity (Series (countable_sum val)).
      * symmetry. apply is_series_unique; eauto.
      * apply is_series_unique; eauto.
    }
    apply is_seriesC_0. intros n.
    destruct (val_nonneg n); eauto. exfalso; eapply Hnot_gt; eauto.
  }
Qed.

Lemma ivd_isupport_inhabited {X} (I: ivdist X) : isupport I.
Proof.
  destruct (ivd_support_idx I) as (i&Hgt).
  exists (ind I i). eexists; eauto.
Qed.

Definition eq_ivd_prob {X} (I1 I2: ivdist X) :=
  eq_ival_prob I1 I2.

Global Instance eq_ivd_prob_Transitivite {X}: Transitive (@eq_ivd_prob X).
Proof. intros ???. apply eq_ival_prob_trans. Qed.
Global Instance eq_ivd_prob_Reflexive {X}: Reflexive (@eq_ivd_prob X).
Proof. intros ?. apply eq_ival_prob_refl. Qed.
Global Instance eq_ivd_prob_Symmetry {X}: Symmetric (@eq_ivd_prob X).
Proof. intros ??. apply eq_ival_prob_sym. Qed.
Global Instance eq_ivd_prob_Equivalence {X}: Equivalence (@eq_ivd_prob X).
Proof. split; apply _. Qed. 

Global Instance eq_ivd_prob_proper X:
  Proper (@eq_ivd X ==> @eq_ivd X ==> iff) (@eq_ivd_prob X).
Proof.
  intros ?? ? ?? ?.
  split.
  * intros. etransitivity.
    ** eapply eq_ival_to_eq_ival_prob. symmetry; eauto.
    ** etransitivity.
       *** eauto. 
       *** eapply eq_ival_to_eq_ival_prob; eauto.
  * intros. etransitivity.
    ** eapply eq_ival_to_eq_ival_prob. eauto.
    ** etransitivity.
       *** eauto. 
       *** eapply eq_ival_to_eq_ival_prob; symmetry; eauto.
Qed.

Lemma ex_series_ivdist_idx_eq_ind {X} (I1: ivdist X) (x: X):
  ex_series (countable_sum (idx_eq_ind I1 x)).
Proof.
  eapply ex_seriesC_le; last (eexists; eapply val_sum1).
  rewrite /idx_eq_ind => a. destruct ClassicalEpsilon.excluded_middle_informative => //=;
  split; eauto; eauto using Rge_le, val_nonneg; nra.
Qed.

Lemma eq_ivd_prob_alt {X} (I1 I2: ivdist X) :
  eq_ivd_prob I1 I2 ↔
  (∀ x, Series (countable_sum (idx_eq_ind I1 x)) = Series (countable_sum (idx_eq_ind I2 x))).
Proof.
  split.
  - intros Heq x. specialize (Heq x) as (Heqa&Heqb).
    apply is_series_unique; eapply Heqb; eauto using ex_series_ivdist_idx_eq_ind.
  - intros Heq x; split.
    * intros Hex. rewrite Heq. apply Series_correct; eauto using ex_series_ivdist_idx_eq_ind.
    * intros Hex. rewrite -Heq. apply Series_correct; eauto using ex_series_ivdist_idx_eq_ind.
Qed.

