Require Import Reals Psatz.
From discprob.basic Require Export base Series_Ext order bigop_ext sval Reals_ext.
From discprob.prob Require Import countable double rearrange.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From Coquelicot Require Export Rcomplements Rbar Series Lim_seq Hierarchy Markov.
(* Basic definitions for discrete probability theory *)

Ltac to_lim_seq :=
  match goal with
    | [ |- filterlim ?f eventually (locally ?n) ] => change (is_lim_seq f n)
    | [ |- real (Lim_seq ?u) = ?l ] => rewrite (is_lim_seq_unique u l); first done
  end.


Record distrib (A: countType) := mkDistrib {
  pmf :> A → R;
  pmf_pos : ∀ a, pmf a >= 0;
  pmf_sum1 : is_series (countable_sum pmf) 1
}.

Arguments pmf {_} _.
Arguments pmf_pos {_} _.
Arguments pmf_sum1 {_} _.

Lemma pmf_sum1_Series {A} (X: distrib A) : Series (countable_sum X) = 1.
Proof.
  apply is_series_unique, pmf_sum1.
Qed.

Lemma pmf_sum_sum_n {A} (X: distrib A) n : 
  sum_n (countable_sum X) n <= 1.
Proof.
  rewrite -(pmf_sum1_Series X).
  apply is_series_partial_pos; last (apply Series_correct; eexists; eapply pmf_sum1).
  intros n'. rewrite /countable_sum. destruct (pickle_inv) => //=; last nra. 
  apply pmf_pos.
Qed.

Definition pr {A: countType} (d: distrib A) (P: A → bool) :=
  Series (countable_sum (λ a, if P a then d a else 0)).

Hint Resolve pmf_pos pmf_sum1 : prob.

Lemma pr_ex_series {A: countType} (d: distrib A) (P: A → bool):
  ex_series (countable_sum (λ a : A, if P a then d a else 0)).
Proof.
  eapply is_seriesC_filter_pos; eauto with prob.
Qed.

Hint Resolve pr_ex_series : prob.

(* Naming here is funny because later we will define "pr_ge" for random variables *)
Lemma ge_pr_0 {A: countType} (d: distrib A) P:
  pr d P >= 0.
Proof.
  rewrite /pr. apply Rle_ge, (Rle_trans _ (Series (countable_sum (λ n:A, 0)))).
  - right. symmetry; apply is_series_unique, is_seriesC_0; done.
  - apply Series_le.
    * rewrite /countable_sum => n. destruct (pickle_inv) as [s|] => //=; try nra. 
      destruct (P s) => //=; specialize (pmf_pos d s); nra.
    * auto with prob. 
Qed.

Lemma pr_le_1 {A: countType} (d: distrib A) P:
  pr d P <= 1.
Proof.
  rewrite /pr. apply (Rle_trans _ (Series (countable_sum d))).
  (*
  - right. symmetry; apply is_series_unique, is_seriesC_0; done.
   *)
  - apply Series_le.
    * rewrite /countable_sum => n. destruct (pickle_inv) as [s|] => //=; try nra. 
      destruct (P s) => //=; specialize (pmf_pos d s); nra.
    * eexists; eapply pmf_sum1.
  - right. apply pmf_sum1_Series.
Qed.

Lemma pr_sum_n {A} (d: distrib A) (P: A → bool) n : 
  sum_n (countable_sum (λ a, if P a then d a else 0)) n <= 1.
Proof.
  etransitivity; last apply (pr_le_1 d P).
  apply is_series_partial_pos; last first. 
  {  rewrite /pr. apply Series_correct. auto with prob. } 
  intros n'. rewrite /countable_sum. destruct (pickle_inv) => //=; last nra. 
  destruct (P _); last nra.
  apply pmf_pos.
Qed.

Lemma pr_xpredT {A: countType} (d: distrib A):
  pr d xpredT = 1.
Proof.
  rewrite /pr. apply is_series_unique, pmf_sum1.
Qed.

Lemma pr_xpred0 {A: countType} (d: distrib A):
  pr d xpred0 = 0.
Proof.
  rewrite /pr. rewrite Series_0 => //= n. rewrite /countable_sum.
  destruct (pickle_inv _) => //=.
Qed.

Lemma pr_eq_pred {A: countType} (d: distrib A) P Q: 
  P =i Q →
  pr d P = pr d Q.
Proof.
  rewrite /pr => HPQ.
  apply Series_ext => n. rewrite /countable_sum; destruct (pickle_inv A n) => //=.
  specialize (HPQ s). rewrite /in_mem//= in HPQ. rewrite HPQ. 
  done.
Qed.

Lemma pr_eq_pred' {A: countType} (d: distrib A) (P Q: pred A): 
  (∀ i, P i ↔ Q i) →
  pr d P = pr d Q.
Proof.
  intros Hext. apply pr_eq_pred. intros i.
  rewrite /in_mem => //=. specialize (Hext i).
  destruct (P i), (Q i); auto with *.
  * destruct Hext as [-> ?]; auto.
  * destruct Hext as [? <-]; auto.
Qed.

Lemma pr_mono_pred {A: countType} (d: distrib A) (P Q: pred A): 
  (∀ i, P i → Q i) →
  pr d P <= pr d Q.
Proof.
  rewrite /pr => HPQ.
  apply Series_le; last auto with prob.
  intros n. rewrite /countable_sum; destruct (pickle_inv A n) => //=; last nra.
  specialize (HPQ s).
  case: (ifP (P s)) => HP;  specialize (pmf_pos d s).
  * rewrite HPQ //. split; nra.
  * case: ifP; split; nra.
Qed.

Lemma pr_union {A: countType} (d: distrib A) P Q:
  pr d (predU P Q) =
  pr d P + pr d Q - pr d (predI P Q).
Proof.
  rewrite /pr. symmetry; apply is_seriesC_filter_union.
  - auto with prob. 
  - apply Series_correct. auto with prob.
Qed.

Lemma pr_union_le {A: countType} (d: distrib A) P Q:
  pr d (predU P Q) <=
  pr d P + pr d Q.
Proof.
  rewrite pr_union. specialize (ge_pr_0 d (predI P Q)). nra.
Qed.

Lemma distrib_exists_support {A: countType} (d: distrib A) :
  ∃ a, d a > 0.
Proof.
  edestruct (Series_strict_pos_inv (countable_sum d)) as (x&Hgt).
  - intros n; rewrite /countable_sum. destruct pickle_inv => //=.
    * apply pmf_pos.
    * nra.
  - rewrite pmf_sum1_Series. nra.
  - rewrite /countable_sum in Hgt. destruct (pickle_inv _ x) as [a|].
    * exists a. done.
    * rewrite //= in Hgt; nra.
Qed.

Record rvar {A} (Ω: distrib A) (B: eqType) := mkRvar { rvar_fun :> A → B; }.


Arguments mkRvar {_} _ {_} _.

Definition rvar_const {A} {B : eqType} (Ω: distrib A) (b: B) :=
  mkRvar Ω (λ x, b).

(* Given two distributions, we can form a joint ``independent'' distribution *)

Section product.
Variable (A B: countType).
Variable (dist1: distrib A) (dist2: distrib B).
Definition prod_pmf (ab: A * B) := (dist1 (fst ab)) * (dist2 (snd ab)).

Lemma prod_pmf_pos ab: prod_pmf ab >= 0.
Proof.
  rewrite /prod_pmf. 
  specialize (pmf_pos dist1 (fst ab)).
  specialize (pmf_pos dist2 (snd ab)).
  nra.
Qed.

Lemma is_series_chain s1 s2 v: is_series s2 (Series s1) → is_series s1 v → is_series s2 v.
Proof.
  intros Hs2 Hs1. apply is_series_unique in Hs1. rewrite -Hs1. done.
Qed.

Section double.
Variable P: pred (A * B).

Definition σprod := 
  λ n, match pickle_inv [countType of (A * B)] n with
       | Some (a, b) => (S (pickle a), S (pickle b))
       | None => (O, O)
       end.

Definition aprod := 
  λ mn, match mn with
        | (S m, S n) => 
          match (pickle_inv A m), (pickle_inv B n) with
            | Some a, Some b => 
              if P (a, b) then 
                prod_pmf (a, b) 
              else
                0
            | _, _ => 0
          end
        | _ => 0
        end.

Lemma aprod_double_summable: double_summable aprod.
Proof.
  exists 1 => n. 
  set (a' := (λ mn, 
              match mn with
              | (S m, S n) => (countable_sum dist1 m) * 
                              (countable_sum dist2 n)
              | _ => 0
              end)). 
  transitivity (sum_n (λ j, sum_n (λ k, Rabs (a' (j, k))) n) n).
  { rewrite ?sum_n_bigop. rewrite /a'.
    eapply Rle_bigr. intros (i&?) ?. 
    rewrite ?sum_n_bigop. 
    eapply Rle_bigr. intros (j&?) ?. 
    destruct i, j => //=; try reflexivity.
    rewrite ?/countable_sum/prod_pmf.
    destruct pickle_inv, pickle_inv => //=; rewrite ?Rmult_0_l ?Rmult_0_r; try reflexivity; [].
    destruct P => //=; first reflexivity.
    rewrite Rabs_R0. apply Rabs_pos.
  }
  destruct n.
  * rewrite ?sum_O //= Rabs_R0. nra.
  * etransitivity. 
    { 
      rewrite sum_n_bigop. 
      rewrite -(big_mkord (λ x, true) (λ i, sum_n (λ k, Rabs (a' (i, k))) (S n))).
      rewrite big_nat_recl; last done. 
      rewrite {1}/a' Rabs_R0 sum_n_const Rmult_0_r Rplus_0_l.
      eapply Rle_bigr => ??. 
      rewrite sum_n_bigop. 
      rewrite -(big_mkord (λ x, true) (λ i, Rabs (a' (_, i)))).
      rewrite big_nat_recl; last done. 
      rewrite {1}/a' Rabs_R0 Rplus_0_l.
      rewrite /a'//=.
      etransitivity.
      { right. eapply eq_bigr => ??. rewrite Rabs_mult. 
        rewrite ?Rabs_right; first done.
        - rewrite /countable_sum.  destruct pickle_inv => //=; try nra; try apply pmf_pos.
        - rewrite /countable_sum.  destruct pickle_inv => //=; try nra; try apply pmf_pos.
      }
      rewrite -big_distrr.
      rewrite big_mkord -(sum_n_bigop (λ i, countable_sum _ i)). 
      etransitivity. 
      { 
        apply Rmult_le_compat_l.
        - rewrite /countable_sum; destruct pickle_inv => //=; try nra; try apply Rge_le, pmf_pos.
        - apply pmf_sum_sum_n. 
      }
      rewrite Rmult_1_r.
      reflexivity.
    }
    rewrite big_mkord -sum_n_bigop.
    apply pmf_sum_sum_n.
Qed.

Lemma σprod_inj: ∀ n n', aprod (σprod n) <> 0 → σprod n = σprod n' → n = n'.
Proof.
  intros n n'. rewrite /σprod/aprod.
  case_eq (pickle_inv [countType of A * B] n); last by nra.
  case_eq (pickle_inv [countType of A * B] n'); last first.
  { intros Heq_none (a&b) Heq_some => //=. }
  intros (a'&b') Heq' (a&b) Heq Hneq0 => //=. 
  inversion 1 as [[Hp1 Hp2]].
  assert (a = a').
  { 
    apply (f_equal (pickle_inv A)) in Hp1. rewrite ?pickleK_inv in Hp1.
    inversion Hp1; done.
  }
  assert (b = b').
  { 
    apply (f_equal (pickle_inv B)) in Hp2. rewrite ?pickleK_inv in Hp2.
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
  case_eq (pickle_inv A n1) => //=; [].
  intros a Heq1.
  case_eq (pickle_inv B n2) => //=; [].
  intros b Heq2 => Hneq0.
  exists (pickle (a, b)).
  rewrite /σprod pickleK_inv. repeat f_equal.
  - apply (f_equal (oapp (@pickle _) n1)) in Heq1. rewrite pickle_invK //= in Heq1.
  - apply (f_equal (oapp (@pickle _) n2)) in Heq2. rewrite pickle_invK //= in Heq2.
Qed.

Lemma is_series_prod_row:
  is_series (countable_sum (λ ab, if P ab then prod_pmf ab else 0))
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
                          (series_double_covering' _ _ σprod_inj σprod_cov aprod_double_summable)).
  cut (Series (λ j, Series (λ k, aprod (j, k))) =
      (Series (λ j : nat, Series (λ k : nat, aprod (S j, S k))))).
  { 
    intros <-. apply Series_correct. 
    eexists; eapply (series_double_covering _ _ σprod_inj σprod_cov aprod_double_summable); eauto.
  }
  rewrite Series_incr_1; last first.
  { eexists; eapply (series_double_covering _ _ σprod_inj σprod_cov aprod_double_summable); eauto. }
  rewrite {1}/aprod Series_0 // Rplus_0_l.
  apply Series_ext => n.
  rewrite Series_incr_1; last first.
  { apply ex_series_Rabs, ex_series_row, aprod_double_summable. }
  rewrite {1}/aprod Rplus_0_l => //=.
Qed.

Lemma Series_prod_row:
  Series (countable_sum (λ ab, if P ab then prod_pmf ab else 0)) =
  (Series (λ j, Series (λ k, aprod (S j, S k)))).
Proof.
  apply is_series_unique, is_series_prod_row.
Qed.

End double.

Lemma prod_pmf_pos_sum1:
  is_series (countable_sum (prod_pmf)) 1.
Proof.
  eapply (is_series_chain).
  { apply (is_series_prod_row xpredT). }
  rewrite //=.
  eapply (is_series_ext (countable_sum dist1)). 
  { intros n.
    rewrite -(Series_ext (λ k, countable_sum dist1 n * countable_sum dist2 k)); last first.
    { intros m. rewrite /countable_sum. destruct (pickle_inv), (pickle_inv) => //=; nra. }
    rewrite Series_scal_l pmf_sum1_Series Rmult_1_r. done.
  }
  apply pmf_sum1.
Qed.

Definition distrib_prod := mkDistrib _ prod_pmf prod_pmf_pos prod_pmf_pos_sum1.

End product.

Arguments distrib_prod {_ _}.
Arguments prod_pmf {_ _}.

Definition rrvar {A} (Ω : distrib A) := @rvar A Ω [eqType of R].

Definition pr_eq {A} {B: eqType} {Ω : distrib A} (X: rvar Ω B) (b: B) :=
  pr Ω (λ a, X a == b).
Definition pr_gt {A} {Ω: distrib A} (X: rrvar Ω) (b: R) :=
  pr Ω (λ a, Rgt_dec (X a) b).
Definition pr_ge {A} {Ω: distrib A} (X: rrvar Ω) (b: R) :=
  pr Ω (λ a, Rge_dec (X a) b).

Definition rvar_dist {A} {B} {Ω : distrib A} (X: rvar Ω B) := Ω.

Lemma pr_gt_contra {A} (Ω: distrib A) (X: rrvar Ω) (r1 r2: R):
  r1 <= r2 →
  pr_gt X r1 >= pr_gt X r2.
Proof.
  rewrite /pr_gt. intros Hle. apply Rle_ge, pr_mono_pred. 
  intros x. 
  destruct Rgt_dec as [Hgt1|Hngt1] => //=.
  destruct Rgt_dec as [Hgt2|Hngt2] => //=.
  rewrite //= in Hngt2 Hgt1. nra.
Qed.

Lemma pr_eq_rvar_ext {A} {B: eqType} {Ω: distrib A} (X X': rvar Ω B) (b: B):
  X =1 X' →
  pr_eq X b = pr_eq X' b.
Proof.
  intros Hext; rewrite /pr_eq. apply pr_eq_pred' => i; by rewrite (Hext i).
Qed.

Lemma pr_eq_ge_0 {A} {B: eqType} {Ω: distrib A} (X: rvar Ω B) (b: B) :
  pr_eq X b >= 0.
Proof. apply ge_pr_0. Qed.

Lemma pr_eq_le_1 {A} {B: eqType} {Ω: distrib A} (X: rvar Ω B) (b: B) :
  pr_eq X b <= 1.
Proof. apply pr_le_1.  Qed.

(* Expectation is only said to exist if the sum below converges
   absolutely; this implies that the order of the sum does not matter,
   and that it will be equivalent to a standard alternative way to
   define expectation *)

Section Ex.
Definition Ex {A} {Ω: distrib A} (X: rrvar Ω) : R :=
  Series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * (sval r)))).

Definition is_Ex {A} {Ω : distrib A} (X: rrvar Ω) (v: R) :=
  ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (sval r)))) ∧
  is_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * sval r))) v.

Definition ex_Ex {A} {Ω : distrib A} (X: rrvar Ω) :=
  ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (sval r)))).

Lemma Ex_correct {A} {Ω : distrib A} (X: rrvar Ω) :
  ex_Ex X → is_Ex X (Ex X).
Proof.
  intros Hex. split; first done.
  rewrite /Ex. eapply Series_correct, ex_series_Rabs, ex_series_ext; last by apply Hex.
  intros n. rewrite /countable_sum/oapp. destruct (pickle_inv _) as [s|].
  * specialize (pr_eq_ge_0 X (sval s)). intros.
    rewrite Rabs_mult; f_equal. rewrite Rabs_right //.
  * rewrite Rabs_R0. done.
Qed.

Lemma is_Ex_unique {A} {Ω: distrib A} (X: rrvar Ω) (v : R) :
  is_Ex X v → Ex X = v.
Proof. intros [Habs Hser]. by apply is_series_unique. Qed.

Lemma ex_Ex' {A} {Ω : distrib A} (X: rrvar Ω) :
  ex_Ex X →
  ex_series (Rabs \o countable_sum (λ r: imgT X, (pr_eq X (sval r) *  (sval r)))).
Proof.
  rewrite /ex_Ex => H.
  eapply (ex_series_ext); last apply H.
  intros n. rewrite //=/countable_sum; destruct (pickle_inv _ n) => //=.
  - rewrite Rabs_mult; f_equal. rewrite Rabs_right; last apply ge_pr_0. done.
  - rewrite Rabs_R0. done.
Qed.

Lemma ex_Ex_nonabs {A} {Ω : distrib A} (X: rrvar Ω) :
  ex_Ex X →
  ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) *  (sval r)))).
Proof. intros. by apply ex_series_Rabs, ex_Ex'. Qed.

Hint Resolve  ex_Ex' ex_Ex_nonabs.

Definition rvar_comp {A: countType} {B C: eqType} {Ω : distrib A} (X: rvar Ω B) (f: B → C)
  : rvar Ω C :=
  mkRvar (rvar_dist X) (f \o X).
  
Section Ex_pt_gen.
Variable (A: countType).
Variable (B: eqType).
Variable (Ω: distrib A).
Variable (X: rvar Ω B).
Variable (f: B → R).

Definition σpt : nat → nat * nat.
  refine (λ n, match pickle_inv [countType of A] n with
               | Some a => (S (@pickle [countType of imgT X] (exist _ (X a) _)),
                            S (pickle a))
               | None => (O, O)
               end).
  { rewrite /img//=. apply /exCP. exists a. by rewrite eq_refl. } 
Defined.

Definition apt := 
  λ mn, match mn with
        | (S m, S n) => 
          match (pickle_inv [countType of imgT X] m), (pickle_inv A n) with
            | Some v, Some a => (if (X a) == (sval v) then rvar_dist X a else 0) * f (sval v)
            | _, _ => 0
          end
        | _ => 0
        end.

Lemma Series_correct_ext a a':
  (∀ n, a n = a' n) → is_series a (Series a) → is_series a' (Series a').
Proof.
  intros. eapply is_series_ext; eauto. rewrite (Series_ext a' a) //.
Qed.

Lemma Series_correct' a v:
  Series a = v → ex_series a → is_series a v. 
Proof. by intros <- ?; apply Series_correct. Qed.

Lemma apt_double_summable_by_row
      (EX: ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (f (sval r))))))
  : double_summable apt.
Proof.
  apply ex_series_rows_ds.
  - intros j. destruct j.
    * rewrite /apt. exists 0. apply is_series_0 => ?. rewrite Rabs_R0. done.
    * rewrite ex_series_incr_1.
      rewrite /apt. destruct (pickle_inv _ j) as [v|]; last first.
      { exists 0. apply is_series_0 => ?. rewrite Rabs_R0. done. }
      apply (ex_series_ext (λ k, Rabs (f (sval v)) * (match pickle_inv A k with 
                                                 | Some a => (if X a == sval v then (rvar_dist X) a
                                                             else 0)
                                                 | None => 0
                                                 end))).
      { intros k. destruct (pickle_inv) as [s|] => //=. 
        ** case: ifP => _. rewrite Rabs_mult.
           *** rewrite (Rabs_right ((rvar_dist X) s)); last apply pmf_pos; rewrite //=; nra.
           *** rewrite Rmult_0_l Rabs_R0. nra.
        ** rewrite Rabs_R0; nra.
      }
      apply: ex_series_scal.
      apply pr_ex_series. 
  - rewrite ex_series_incr_1. 
    destruct EX. eapply ex_series_ext; last (eexists; eauto).
    intros k. rewrite /countable_sum/apt. destruct (pickle_inv _ k) as [v|] => //=; last first.
    { symmetry; apply Series_0; intros [|]; by rewrite Rabs_R0. }
    rewrite Series_incr_1_aux; last by apply Rabs_R0.
    rewrite -(Series_ext (λ k, Rabs (f (sval v)) * (match pickle_inv A k with 
                                                 | Some a => (if X a == sval v then (rvar_dist X) a
                                                             else 0)
                                                 | None => 0
                                                 end))).
    * rewrite Series_scal_l. rewrite /pr_eq/pr/countable_sum/oapp//= Rmult_comm. done.
    * { intros j. destruct (pickle_inv) as [s|] => //=. 
        ** case: ifP => _. rewrite Rabs_mult.
           *** rewrite (Rabs_right ((rvar_dist X) s)); last apply pmf_pos; rewrite //=; nra.
           *** rewrite Rmult_0_l Rabs_R0. nra.
        ** rewrite Rabs_R0; nra.
      }
Qed.


Lemma apt_double_summable_by_column
 (EX_pt: ex_series (countable_sum (λ a, Rabs (f (X a)) * (rvar_dist X) a))):
 double_summable apt.
Proof.
  assert (Himg: ∀ v, X v \in img X).
  { intros v. rewrite /img //=. apply /exCP. eexists. eauto. }
  assert (Hext: ∀ v x, (λ n : nat,
                      match pickle_inv [countType of imgT X] n with
                      | Some v0 => if X v == sval v0 then Rabs (f (sval v0)) else 0
                      | None => 0
                      end) x =
               (λ n : nat, match eq_nat_dec n (@pickle [countType of imgT X]
                                                       (exist _ (X v) (Himg v) : imgT X))
                           with
                           | left _ => Rabs (f (X v))
                           |  _ => 0
                           end) x).
  { intros v x. generalize (Himg v); clear Himg => Himg. destruct Nat.eq_dec as [e|n].
    * rewrite //= e. rewrite pickleK_inv.
      rewrite //= eq_refl. done.
    * specialize (pickle_invK [countType of imgT X] x) => //=.
      intros. destruct pickle_inv => //.
      case: ifP.
      ** move /eqP => Heq. 
         rewrite Heq in Himg n. rewrite //= in H.
         rewrite -H in n.
         exfalso. apply n. f_equal. apply sval.sval_inj_pred => //=.
      ** done.
  }
  apply ex_series_columns_ds.
  - intros j. destruct j.
    * rewrite /apt. exists 0. apply is_series_0 => n. destruct n; rewrite Rabs_R0; done.
    * rewrite ex_series_incr_1.
      rewrite /apt. destruct (pickle_inv _ j) as [v|]; last first.
      { exists 0. apply is_series_0 => n. destruct (pickle_inv _); rewrite Rabs_R0; done. }
      apply (ex_series_ext (λ k, rvar_dist X v * (match pickle_inv [countType of imgT X] k with 
                                                  | Some v0 => (if X v == sval v0 then
                                                                  Rabs (f (sval v0))
                                                                else 0)
                                                 | None => 0
                                                 end))).
      { intros k. destruct (pickle_inv) as [s|] => //=. 
        ** case: ifP => _. rewrite Rabs_mult.
           *** rewrite (Rabs_right ((rvar_dist X) v)); last apply pmf_pos; rewrite //=.
           *** rewrite Rmult_0_l Rabs_R0. nra.
        ** rewrite Rabs_R0; nra.
      }
      apply: ex_series_scal.
      eapply ex_series_ext; first (intros; symmetry; eapply Hext).
      eexists; eapply is_series_bump.
  - rewrite ex_series_incr_1. 
    destruct EX_pt. eapply ex_series_ext; last (eexists; eauto).
    intros k. rewrite /countable_sum/apt.
    rewrite /oapp//=. destruct (pickle_inv _ k) as [v|] => //=; last first.
    { symmetry; apply Series_0; intros [|]. rewrite Rabs_R0; done. destruct (pickle_inv _) => //=;
      rewrite Rabs_R0; done.
    }
    rewrite Series_incr_1_aux; last by apply Rabs_R0.
    rewrite -(Series_ext (λ k, rvar_dist X v * (match pickle_inv [countType of imgT X] k with 
                                                | Some v0 => (if X v == sval v0 then
                                                                Rabs (f (sval v0))
                                                             else 0)
                                                 | None => 0
                                                 end))).
    * rewrite Series_scal_l. rewrite /pr_eq/pr/countable_sum/oapp//= Rmult_comm.
      f_equal. symmetry; etransitivity.
      ** apply Series_ext. 
         intros; eapply Hext.
      ** apply Series_bump.
    * intros j. destruct (pickle_inv) as [s|] => //=. 
        ** case: ifP => _. rewrite Rabs_mult.
           *** rewrite (Rabs_right ((rvar_dist X) v)); last apply pmf_pos; rewrite //=; nra.
           *** rewrite Rmult_0_l Rabs_R0. nra.
        ** rewrite Rabs_R0; nra.
Qed.


Lemma σpt_inj: ∀ n n', apt (σpt n) <> 0 → σpt n = σpt n' → n = n'.
Proof.
  intros n n'. rewrite /σpt/apt.
  case_eq (pickle_inv [countType of A] n); last by nra.
  case_eq (pickle_inv [countType of A] n'); last first.
  { intros Heq_none a Heq_some => //=. }
  intros a' Heq' a Heq Hneq0 => //=. 
  inversion 1 as [[Hp1 Hp2]].
  assert (a = a').
  { 
    apply (f_equal (pickle_inv A)) in Hp2. rewrite ?pickleK_inv in Hp2.
    inversion Hp2; done.
  }
  subst.
  apply (f_equal (oapp (@pickle _) n)) in Heq.
  apply (f_equal (oapp (@pickle _) n')) in Heq'.
  rewrite ?pickle_invK //= in Heq Heq'. congruence.
Qed.

Lemma σpt_cov: ∀ n, apt n <> 0 → ∃ m, σpt m = n.
Proof.
  intros (n1&n2).
  destruct n1, n2 => //=.
  rewrite /countable_sum.
  case_eq (pickle_inv [countType of imgT X] n1) => //=; last first.
  { intros ->. congruence. }
  intros v Heq1. rewrite Heq1.
  case_eq (pickle_inv A n2) => //=; [].
  intros a Heq2 => Hneq0.
  exists (pickle a).
  rewrite /σpt pickleK_inv. repeat f_equal.
  - apply (f_equal (oapp (@pickle _) n1)) in Heq1. rewrite pickle_invK //= in Heq1.
    rewrite Heq1. f_equal => //=. move: Hneq0. case: ifP; last by nra.
    move /eqP => Heq ?. destruct v as (v&Hpf). rewrite //= in Heq. subst. 
    rewrite //=. f_equal. apply bool_irrelevance.
  - apply (f_equal (oapp (@pickle _) n2)) in Heq2. rewrite pickle_invK //= in Heq2.
Qed.

Lemma apt_row_rewrite j:
  Series (λ k : nat, apt (S j, S k)) = countable_sum (λ r : imgT X, pr_eq X (sval r) * f (sval r)) j.
Proof.
 rewrite /apt/countable_sum. 
 destruct (pickle_inv _ j) as [v|] => //=; last apply Series_0 => //=.
 rewrite -(Series_ext (λ k, f (sval v) * (match pickle_inv A k with 
                                             | Some a => (if X a == sval v then (rvar_dist X) a
                                                          else 0)
                                             | None => 0
                                             end))).
    * rewrite Series_scal_l. rewrite /pr_eq/pr/countable_sum/oapp//=. rewrite Rmult_comm; done.
    * intros ?.  destruct (pickle_inv) as [s|] => //=; try case: ifP => _; nra. 
Qed.

Lemma apt_row_rewrite_abs j:
  Series (λ k : nat, Rabs (apt (S j, S k)))
  = countable_sum (λ r : imgT X, pr_eq X (sval r) * Rabs (f (sval r))) j.
Proof.
 rewrite /apt/countable_sum. 
 destruct (pickle_inv _ j) as [v|] => //=; last apply Series_0 => //=.
 rewrite -(Series_ext (λ k, Rabs (f (sval v)) * (match pickle_inv A k with 
                                             | Some a => (if X a == sval v then (rvar_dist X) a
                                                          else 0)
                                             | None => 0
                                             end))).
    * rewrite Series_scal_l. rewrite /pr_eq/pr/countable_sum/oapp//=. rewrite Rmult_comm; done.
    * intros ?.  destruct (pickle_inv) as [s|] => //=; try case: ifP => _; try nra. 
      ** rewrite Rabs_mult. rewrite (Rabs_right ((rvar_dist X) s)); auto using pmf_pos.
         rewrite Rmult_comm. done.
      ** by rewrite ?Rmult_0_l ?Rmult_0_r Rabs_R0.
      ** by rewrite ?Rmult_0_l ?Rmult_0_r Rabs_R0.
    * by rewrite Rabs_R0.
Qed.

Lemma is_series_Ex_pt_f
  (EX: ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (f (sval r)))))): 
  is_series (countable_sum (λ a : A, f (X a) * (rvar_dist X) a))
    (Series (countable_sum (λ a : A, f (X a) * (rvar_dist X) a))).
Proof.
  intros.
  apply (Series_correct_ext (apt \o σpt)).
  {
    intros n. rewrite /apt/σpt/countable_sum//=. 
    destruct (pickle_inv _ n) as [a|] => //=.
    rewrite ?pickleK_inv //= eq_refl. nra.
  }
  apply Series_correct, ex_series_Rabs, ex_series_ordering;
    auto using σpt_inj, σpt_cov, apt_double_summable_by_row.
Qed.

Lemma is_series_Ex_pt_f_abs
  (EX: ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (f (sval r)))))): 
  is_series (countable_sum (λ a : A, Rabs (f (X a)) * (rvar_dist X) a))
    (Series (countable_sum (λ a : A, Rabs (f (X a)) * (rvar_dist X) a))).
Proof.
  intros.
  apply (Series_correct_ext (Rabs \o apt \o σpt)).
  {
    intros n. rewrite /apt/σpt/countable_sum//=. 
    destruct (pickle_inv _ n) as [a|] => //=.
    rewrite ?pickleK_inv //= eq_refl.
    rewrite Rabs_mult //=.
    * rewrite Rabs_right; auto using pmf_pos.
      nra.
    * by rewrite Rabs_R0.
  }
  apply Series_correct, ex_series_ordering;
    auto using σpt_inj, σpt_cov, apt_double_summable_by_row.
Qed.

Lemma is_series_Ex_pt_f'
  (EX: ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (f (sval r)))))): 
  is_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * f (sval r)))) 
            (Series (countable_sum (λ a, f (X a) * (rvar_dist X) a))).
Proof.  
  intros.
  eapply (is_series_ext (λ j, Series (λ k, apt (S j, k)))).
  { intros n. rewrite Series_incr_1_aux => //. apply apt_row_rewrite. }
  rewrite -(Series_ext (apt \o σpt)); last first.
  {
    intros n. rewrite /apt/σpt/countable_sum//=. 
    destruct (pickle_inv _ n) as [a|] => //=.
    rewrite ?pickleK_inv //= eq_refl. nra.
  }
  apply (is_series_incr_1 (λ j, Series (λ k, apt (j, k)))).
  rewrite {3}/apt. rewrite [a in is_series _ (plus _ a)]Series_0 // plus_zero_r.
  apply series_double_covering; auto using σpt_inj, σpt_cov, apt_double_summable_by_row.
Qed.

Lemma is_series_Ex_by_pt_f':
  ex_series (countable_sum (λ a, Rabs (f (X a)) * (rvar_dist X) a)) →
  is_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * f (sval r))))
            (Series (countable_sum (λ a, f (X a) * (rvar_dist X) a))).
Proof.
  intros.
  eapply (is_series_ext (λ j, Series (λ k, apt (S j, k)))).
  { intros n. rewrite Series_incr_1_aux => //. apply apt_row_rewrite. }
  rewrite -(Series_ext (apt \o σpt)); last first.
  {
    intros n. rewrite /apt/σpt/countable_sum//=. 
    destruct (pickle_inv _ n) as [a|] => //=.
    rewrite ?pickleK_inv //= eq_refl //=. nra.
  }
  apply (is_series_incr_1 (λ j, Series (λ k, apt (j, k)))).
  rewrite {3}/apt. rewrite [a in is_series _ (plus _ a)]Series_0 // plus_zero_r.
  apply series_double_covering; auto using σpt_inj, σpt_cov, apt_double_summable_by_column.
Qed.

Lemma is_series_Ex_abs_by_pt_f':
  ex_series (countable_sum (λ a, Rabs (f (X a)) * (rvar_dist X) a)) →
  is_series (countable_sum (λ r: imgT X, pr_eq X (sval r) * Rabs (f (sval r))))
            (Series (countable_sum (λ a, Rabs (f (X a)) * (rvar_dist X) a))).
Proof.
  intros.
  eapply (is_series_ext (λ j, Series (λ k, Rabs (apt (S j, k))))).
  { intros n. rewrite Series_incr_1_aux => //. apply apt_row_rewrite_abs.
    rewrite //= Rabs_R0 //.
  }
  rewrite -(Series_ext (Rabs \o apt \o σpt)); last first.
  {
    intros n. rewrite /apt/σpt/countable_sum//=. 
    destruct (pickle_inv _ n) as [a|] => //=.
    rewrite ?pickleK_inv //= eq_refl //=.
    rewrite Rabs_mult //=.
    * rewrite Rabs_right; auto using pmf_pos.
      nra.
    * by rewrite Rabs_R0.
  }
  apply (is_series_incr_1 (λ j, Series (λ k, Rabs (apt (j, k))))).
  rewrite {3}/apt.
  rewrite [a in is_series _ (plus _ a)]Series_0 ?Rabs_R0 // plus_zero_r.
  apply series_double_covering_Rabs; auto using σpt_inj, σpt_cov, apt_double_summable_by_column.
Qed.

Lemma is_series_Ex_by_pt_f:
  ex_series (countable_sum (λ a, Rabs (f (X a)) * (rvar_dist X) a)) →
  is_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * f (sval r))))
            (Series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * f (sval r))))).
Proof. intros. apply Series_correct. eexists; by apply is_series_Ex_by_pt_f'. Qed.

Lemma ex_Ex_pt_f
  (EX: ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (f (sval r)))))): 
  ex_series (countable_sum (λ a, f (X a) * (rvar_dist X) a)).
Proof. eexists; by apply is_series_Ex_pt_f. Qed.

Lemma ex_Ex_pt_f_abs
  (EX: ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (f (sval r)))))): 
  ex_series (countable_sum (λ a, Rabs (f (X a)) * (rvar_dist X) a)).
Proof. intros. eexists; by apply is_series_Ex_pt_f_abs. Qed.

Lemma Ex_pt_f
  (EX: ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (f (sval r)))))): 
  Series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * (f (sval r)))))
  = Series (countable_sum (λ a, f (X a) * (rvar_dist X) a)).
Proof.  
  intros. by apply is_series_unique, is_series_Ex_pt_f'.
Qed.

Lemma ex_Ex_by_pt_f:
  ex_series (countable_sum (λ a, Rabs (f (X a)) * (rvar_dist X) a)) →
  ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (f (sval r))))).
Proof. eexists. by apply is_series_Ex_abs_by_pt_f'. Qed.

Lemma Ex_pt_by_column_f:
  ex_series (countable_sum (λ a, Rabs (f (X a)) * (rvar_dist X) a)) →
  Series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * (f (sval r)))))
  = Series (countable_sum (λ a, f (X a) * (rvar_dist X) a)).
Proof.  
  intros. by apply is_series_unique, is_series_Ex_by_pt_f'.
Qed.

End Ex_pt_gen.

Section Ex_pt.
Variable (A: countType).
Variable (Ω: distrib A).
Variable (X: rrvar Ω).
Lemma is_series_Ex_pt:
  ex_Ex X →
  is_series (countable_sum (λ a : A, (X a) * (rvar_dist X) a))
    (Series (countable_sum (λ a : A, X a * (rvar_dist X) a))).
Proof. intros; apply is_series_Ex_pt_f with (f := id) => //=. Qed.

Lemma is_series_Ex_pt_abs:
  ex_Ex X →
  is_series (countable_sum (λ a : A, Rabs (X a) * (rvar_dist X) a))
    (Series (countable_sum (λ a : A, Rabs (X a) * (rvar_dist X) a))).
Proof. intros; apply is_series_Ex_pt_f_abs with (f := id) => //=. Qed.

Lemma is_series_Ex_pt':
  ex_Ex X →
  is_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * sval r))) 
            (Series (countable_sum (λ a, X a * (rvar_dist X) a))).
Proof. intros; apply is_series_Ex_pt_f' with (f := id) => //=. Qed.

Lemma is_series_Ex_by_pt':
  ex_series (countable_sum (λ a, Rabs (X a) * (rvar_dist X) a)) →
  is_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * sval r)))
            (Series (countable_sum (λ a, X a * (rvar_dist X) a))).
Proof. intros; apply is_series_Ex_by_pt_f' with (f := id) => //=. Qed.

Lemma is_series_Ex_abs_by_pt':
  ex_series (countable_sum (λ a, Rabs (X a) * (rvar_dist X) a)) →
  is_series (countable_sum (λ r: imgT X, pr_eq X (sval r) * Rabs (sval r)))
            (Series (countable_sum (λ a, Rabs (X a) * (rvar_dist X) a))).
Proof. intros; apply is_series_Ex_abs_by_pt_f' with (f := id) => //=. Qed.

Lemma is_series_Ex_by_pt:
  ex_series (countable_sum (λ a, Rabs (X a) * (rvar_dist X) a)) →
  is_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * sval r)))
            (Series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * sval r)))).
Proof. intros; apply is_series_Ex_by_pt_f with (f := id) => //=. Qed.

Lemma ex_Ex_pt:
  ex_Ex X →
  ex_series (countable_sum (λ a, X a * (rvar_dist X) a)).
Proof. intros; apply ex_Ex_pt_f with (f := id) => //=. Qed.

Lemma ex_Ex_pt_abs:
  ex_Ex X →
  ex_series (countable_sum (λ a, Rabs (X a) * (rvar_dist X) a)).
Proof. intros; apply ex_Ex_pt_f_abs with (f := id) => //=. Qed.

Lemma Ex_pt:
  ex_Ex X →
  Ex X = Series (countable_sum (λ a, X a * (rvar_dist X) a)).
Proof. intros; apply Ex_pt_f with (f := id) => //=. Qed.

Lemma ex_Ex_by_pt:
  ex_series (countable_sum (λ a, Rabs (X a) * (rvar_dist X) a)) →
  ex_Ex X.
Proof. intros; apply ex_Ex_by_pt_f with (f := id) => //=. Qed.

Lemma Ex_pt_by_column:
  ex_series (countable_sum (λ a, Rabs (X a) * (rvar_dist X) a)) →
  Ex X = Series (countable_sum (λ a, X a * (rvar_dist X) a)).
Proof. intros; apply Ex_pt_by_column_f with (f := id) => //=. Qed.
End Ex_pt.

Lemma ex_Ex_ext {A} {Ω: distrib A} (X Y: rrvar Ω) :
  ex_Ex X →
  (∀ a, X a = Y a) →
  ex_Ex Y.
Proof.
  intros HXpt%ex_Ex_pt_abs Hext.
  apply ex_Ex_by_pt.
  eapply ex_series_ext; last eapply HXpt.
  intros n. rewrite //=/countable_sum. destruct (pickle_inv _ n) => //=.
  rewrite Hext. done.
Qed.

(* Technically ex_Ex could be removed, but the proof is a bit more annoying *)
Lemma Ex_ext {A} {Ω: distrib A} (X Y: rrvar Ω) :
  ex_Ex X →
  (∀ a, X a = Y a) →
  Ex X = Ex Y.
Proof.
  intros Hex Hext.
  rewrite ?Ex_pt //; last eapply ex_Ex_ext; eauto.
  apply Series_ext.
  intros n. rewrite //=/countable_sum. destruct (pickle_inv _ n) => //=.
  rewrite Hext. done.
Qed.

Lemma Ex_ext_le {A} {Ω: distrib A} (X Y: rrvar Ω) :
  ex_Ex X →
  ex_Ex Y →
  (∀ a, X a <= Y a) →
  Ex X <= Ex Y.
Proof.
  intros HexX HexY Hle.
  rewrite ?Ex_pt //. apply Series_le'.
  * intros. rewrite /countable_sum; destruct pickle_inv => //=; last by reflexivity.
    rewrite /rvar_dist. apply Rmult_le_compat_r; auto.
    apply Rge_le, pmf_pos.
  * by apply ex_Ex_pt.
  * by apply ex_Ex_pt.
Qed.

End Ex.


Hint Resolve ex_Ex_pt.

Definition rvar_pair {A1 A2: countType} {B1 B2: eqType} {Ω1 : distrib A1} {Ω2 : distrib A2}
           (X: rvar Ω1 B1) (Y: rvar Ω2 B2) :=
  mkRvar (distrib_prod Ω1 Ω2) (λ a, (X (fst a), Y (snd a))).

Lemma pair_joint_pred {A1 A2: countType} (Ω1 : distrib A1) (Ω2 : distrib A2) P Q:
  pr (distrib_prod Ω1 Ω2) (λ x, P (fst x) && Q (snd x)) =
  pr Ω1 P * pr Ω2 Q.
Proof.
  rewrite /pr//=/prod_pmf//=.
  rewrite (Series_prod_row _ _ _ _ (λ x, P (fst x) && Q (snd x))) => //=.
  rewrite /prod_pmf.
  etransitivity.
  {
    eapply Series_ext => n.
    eapply (Series_ext _ (λ n', (match pickle_inv A1 n with
                                 | Some a => if P a then Ω1 a else 0
                                 | _ => 0
                             end) *
                            (match pickle_inv A2 n' with
                                 | Some a => if Q a then Ω2 a else 0
                                 | _ => 0
                             end))).
    intros n'.
    do 2 destruct pickle_inv => //=; try destruct (P _); try destruct (Q _); rewrite //=; nra.
  }
  rewrite -Series_scal_r.
  apply Series_ext => n.
  rewrite -Series_scal_l.
  apply Series_ext => n'.
  done.
Qed.

Lemma pair_marginal1 {A1 A2: countType} (Ω1 : distrib A1) (Ω2 : distrib A2) P :
  pr (distrib_prod Ω1 Ω2) (λ x, P (fst x)) =
  pr Ω1 P.
Proof.
  transitivity (pr (distrib_prod Ω1 Ω2) (λ x, P (fst x) && true)).
  - apply pr_eq_pred' => i. by rewrite andbT.
  - by rewrite (pair_joint_pred _ _ _ xpredT) pr_xpredT Rmult_1_r.
Qed.

Lemma pair_marginal2 {A1 A2: countType} {Ω1 : distrib A1} {Ω2 : distrib A2} P:
  pr (distrib_prod Ω1 Ω2) (λ x, P (snd x)) =
  pr Ω2 P.
Proof.
  transitivity (pr (distrib_prod Ω1 Ω2) (λ x, true && P (snd x))).
  - apply pr_eq_pred' => i. by rewrite andTb.
  - by rewrite (pair_joint_pred _ _ xpredT _) pr_xpredT Rmult_1_l.
Qed.

Lemma rvar_pair_marginal1 {A1 A2: countType} {B1 B2: eqType} {Ω1 : distrib A1} {Ω2 : distrib A2}
           (X: rvar Ω1 B1) (Y: rvar Ω2 B2) P :
  pr (rvar_dist (rvar_pair X Y)) (λ x, P (fst x)) =
  pr (rvar_dist X) P.
Proof. by apply pair_marginal1. Qed.

Lemma rvar_pair_marginal2 {A1 A2: countType} {B1 B2: eqType} {Ω1 : distrib A1} {Ω2 : distrib A2}
           (X: rvar Ω1 B1) (Y: rvar Ω2 B2) P :
  pr (rvar_dist (rvar_pair X Y)) (λ x, P (snd x)) =
  pr (rvar_dist Y) P.
Proof. by apply pair_marginal2. Qed.

Lemma rvar_comp_assoc {A: countType} {Ω: distrib A} {B C D: eqType}
      (T: rvar Ω B) (f: B → C) (g: C → D):
  rvar_comp (rvar_comp T f) g = rvar_comp T (g \o f).
Proof. rewrite //=. Qed.

Lemma rvar_comp_comp {A: countType} {Ω: distrib A} {B C D: eqType}
      (T: rvar Ω B) (f: B → C) (g: C → D):
  rvar_comp (rvar_comp T f) g = rvar_comp T (g \o f).
Proof. rewrite //=. Qed.

Module Ex_comp_pt.
Section Ex_comp_pt.
  
Variable (A: countType).
Variable (B: eqType).
Variable (Ω: distrib A).
Variable (X: rvar Ω B).
Variable (f: B → R).
Variable (EX: ex_Ex (rvar_comp X f)).

Definition σcomppt : nat → nat * nat.
  refine (λ n, match pickle_inv [countType of A] n with
               | Some a => (S (@pickle [countType of imgT X] (exist _ (X a) _)),
                            S (pickle a))
               | None => (O, O)
               end).
  { rewrite /img//=. apply /exCP. exists a. by rewrite eq_refl. } 
Defined.

Definition acomppt := 
  λ mn, match mn with
        | (S m, S n) => 
          match (pickle_inv [countType of imgT X] m), (pickle_inv A n) with
            | Some v, Some a => (if (X a) == (sval v) then rvar_dist X a else 0) * f (sval v)
            | _, _ => 0
          end
        | _ => 0
        end.


Lemma σcomppt_inj: ∀ n n', acomppt (σcomppt n) <> 0 → σcomppt n = σcomppt n' → n = n'.
Proof.
  intros n n'. rewrite /σcomppt/acomppt.
  case_eq (pickle_inv [countType of A] n); last by nra.
  case_eq (pickle_inv [countType of A] n'); last first.
  { intros Heq_none a Heq_some => //=. }
  intros a' Heq' a Heq Hneq0 => //=. 
  inversion 1 as [[Hp1 Hp2]].
  assert (a = a').
  { 
    apply (f_equal (pickle_inv A)) in Hp2. rewrite ?pickleK_inv in Hp2.
    inversion Hp2; done.
  }
  subst.
  apply (f_equal (oapp (@pickle _) n)) in Heq.
  apply (f_equal (oapp (@pickle _) n')) in Heq'.
  rewrite ?pickle_invK //= in Heq Heq'. congruence.
Qed.

Lemma σcomppt_cov: ∀ n, acomppt n <> 0 → ∃ m, σcomppt m = n.
Proof.
  intros (n1&n2).
  destruct n1, n2 => //=.
  rewrite /countable_sum.
  case_eq (pickle_inv [countType of imgT X] n1) => //=; last first.
  { intros ->. congruence. }
  intros v Heq1. rewrite Heq1.
  case_eq (pickle_inv A n2) => //=; [].
  intros a Heq2 => Hneq0.
  exists (pickle a).
  rewrite /σcomppt pickleK_inv. repeat f_equal.
  - apply (f_equal (oapp (@pickle _) n1)) in Heq1. rewrite pickle_invK //= in Heq1.
    rewrite Heq1. f_equal => //=. move: Hneq0. case: ifP; last by nra.
    move /eqP => Heq ?. destruct v as (v&Hpf). rewrite //= in Heq. subst. 
    rewrite //=. f_equal. apply bool_irrelevance.
  - apply (f_equal (oapp (@pickle _) n2)) in Heq2. rewrite pickle_invK //= in Heq2.
Qed.

Lemma acomppt_row_rewrite j:
  Series (λ k : nat, acomppt (S j, S k)) = countable_sum (λ r : imgT X, pr_eq X (sval r) * f (sval r)) j.
Proof.
 rewrite /acomppt/countable_sum. 
 destruct (pickle_inv _ j) as [v|] => //=; last apply Series_0 => //=.
 rewrite -(Series_ext (λ k, f (sval v) * (match pickle_inv A k with 
                                             | Some a => (if X a == sval v then (rvar_dist X) a
                                                          else 0)
                                             | None => 0
                                             end))).
    * rewrite Series_scal_l. rewrite /pr_eq/pr/countable_sum/oapp//= Rmult_comm; done.
    * intros ?.  destruct (pickle_inv) as [s|] => //=; try case: ifP => _; nra. 
Qed.

Lemma acomppt_row_rewrite_abs j:
  Series (λ k : nat, Rabs (acomppt (S j, S k)))
  = countable_sum (λ r : imgT X, pr_eq X (sval r) * Rabs (f (sval r))) j.
Proof.
 rewrite /acomppt/countable_sum. 
 destruct (pickle_inv _ j) as [v|] => //=; last apply Series_0 => //=.
 rewrite -(Series_ext (λ k, Rabs (f (sval v)) * (match pickle_inv A k with 
                                             | Some a => (if X a == sval v then (rvar_dist X) a
                                                          else 0)
                                             | None => 0
                                             end))).
    * rewrite Series_scal_l. rewrite /pr_eq/pr/countable_sum/oapp//= Rmult_comm; done.
    * intros ?.  destruct (pickle_inv) as [s|] => //=; try case: ifP => _.
      ** rewrite Rabs_mult Rmult_comm; f_equal.
         rewrite Rabs_right //=; auto using pmf_pos.
      ** by rewrite Rmult_0_r Rmult_0_l ?Rabs_R0.
      ** by rewrite Rmult_0_r ?Rabs_R0.
    * intros; apply Rabs_R0.
Qed.

Lemma is_series_Ex_comp_pt:
  is_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * f (sval r)))) 
            (Series (countable_sum (λ a, f (X a) * (rvar_dist X) a))).
Proof.  
  eapply (is_series_ext (λ j, Series (λ k, acomppt (S j, k)))).
  { intros n. rewrite Series_incr_1_aux => //. apply acomppt_row_rewrite. }
  rewrite -(Series_ext (acomppt \o σcomppt)); last first.
  {
    intros n. rewrite /acomppt/σcomppt/countable_sum//=. 
    destruct (pickle_inv _ n) as [a|] => //=.
    rewrite ?pickleK_inv //= eq_refl. nra.
  }
  apply (is_series_incr_1 (λ j, Series (λ k, acomppt (j, k)))).
  rewrite {3}/acomppt. rewrite [a in is_series _ (plus _ a)]Series_0 // plus_zero_r.
  apply series_double_covering; auto using σcomppt_inj, σcomppt_cov.
  rewrite /acomppt.
  apply apt_double_summable_by_column.
  apply (ex_Ex_pt_f_abs _ _ _ (rvar_comp X f) (id)).
  auto.
Qed.

Lemma is_series_Ex_comp_pt_abs:
  is_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (f (sval r))))) 
            (Series (countable_sum (λ a, Rabs (f (X a)) * (rvar_dist X) a))).
Proof.  
  eapply (is_series_ext (λ j, Series (λ k, Rabs (acomppt (S j, k))))).
  { intros n. rewrite Series_incr_1_aux ?Rabs_R0 => //=. by rewrite acomppt_row_rewrite_abs. }
  rewrite -(Series_ext (Rabs \o acomppt \o σcomppt)); last first.
  {
    intros n. rewrite /acomppt/σcomppt/countable_sum//=. 
    destruct (pickle_inv _ n) as [a|] => //=; last by rewrite Rabs_R0.
    rewrite ?pickleK_inv //= eq_refl ?Rabs_mult.
    rewrite (Rabs_right); last by apply pmf_pos.
    nra.
  }
  apply (is_series_incr_1 (λ j, Series (λ k, Rabs (acomppt (j, k))))).
  rewrite {3}/acomppt. rewrite [a in is_series _ (plus _ a)]Series_0 // ?Rabs_R0 // plus_zero_r.
  apply series_double_covering_Rabs; auto using σcomppt_inj, σcomppt_cov.
  rewrite /acomppt.
  apply apt_double_summable_by_column.
  apply (ex_Ex_pt_f_abs _ _ _ (rvar_comp X f) (id)).
  auto.
Qed.

Lemma ex_series_Ex_comp_pt:
  ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * f (sval r)))). 
Proof.  
  eexists; apply is_series_Ex_comp_pt.
Qed.

Lemma ex_series_Ex_comp_pt_abs:
  ex_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * Rabs (f (sval r))))). 
Proof.  
  eexists; apply is_series_Ex_comp_pt_abs.
Qed.

Lemma is_series_Ex_comp_pt' v:
  (Series (countable_sum (λ a, f (X a) * (rvar_dist X) a))) = v →
  is_series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * f (sval r)))) v.
Proof. by intros <-; apply is_series_Ex_comp_pt. Qed.

Lemma Ex_comp:
  Ex (rvar_comp X f) = Series (countable_sum (λ r: imgT X, (pr_eq X (sval r) * f (sval r)))).
Proof.  
  rewrite Ex_pt //=.  symmetry.
  apply is_series_unique. apply is_series_Ex_comp_pt.
Qed.
End Ex_comp_pt.
End Ex_comp_pt.

Lemma ex_Ex_comp_by_alt {A} {B} {Ω: distrib A} (X: rvar Ω B) f:
  ex_series (countable_sum (λ r : imgT X, pr_eq X (sval r) * Rabs (f (sval r)))) →
  ex_Ex (rvar_comp X f).
Proof.
  intros Hex.
  apply ex_Ex_by_pt.
  by apply ex_Ex_pt_f_abs in Hex.
Qed.

Lemma Ex_comp_by_alt {A} {B} {Ω: distrib A} (X: rvar Ω B) f:
  ex_series (countable_sum (λ r : imgT X, pr_eq X (sval r) * Rabs (f (sval r)))) →
  Ex (rvar_comp X f) = Series (countable_sum (λ r : imgT X, pr_eq X (sval r) * f (sval r))).
Proof. intros; by apply Ex_comp_pt.Ex_comp, ex_Ex_comp_by_alt. Qed.

Section Ex_sum.

Variable (A: countType).
Variable (Ω: distrib A).
Variable (X Y: rrvar Ω).
Variable (EX_X: ex_Ex X).
Variable (EX_Y: ex_Ex Y).

Lemma ex_Ex_sum :
  ex_Ex (mkRvar Ω (λ x, X x + Y x)).
Proof.
  apply ex_Ex_by_pt.
     unshelve (apply: (ex_series_le _ (countable_sum (λ a, (Rabs (X a) * Ω a)
                                                           + (Rabs (Y a) * Ω a))))).
     * intros n. rewrite /norm/countable_sum//=.
       destruct pickle_inv as [a|] => //=.
       ** rewrite /abs//=. specialize (pmf_pos Ω a) => Hge.
          specialize (Rabs_pos (X a + Y a)) => Hge'.
          rewrite Rabs_right; last first.
          { apply Rge_le in Hge. apply Rle_ge.
            apply Rmult_le_pos; auto. }
          rewrite -Rmult_plus_distr_r.
          apply Rmult_le_compat_r; first by nra.
          apply Rabs_triang.
       ** rewrite /abs//=. rewrite Rabs_right; nra.
     * eapply ex_series_ext. 
       { intros; symmetry; eapply countable_sum_plus. }
       unshelve (apply: ex_series_plus).
       ** by apply ex_Ex_pt_abs. 
       ** by apply ex_Ex_pt_abs. 
Qed.

Lemma Ex_sum :
  Ex (mkRvar Ω (λ x, X x + Y x)) = Ex X + Ex Y.
Proof.
  rewrite Ex_pt; last apply ex_Ex_sum.
  symmetry. rewrite Ex_pt; auto.
  rewrite Ex_pt; auto.
  rewrite -Series_plus //=; auto.
  - apply Series_ext.
    intros n => //=. rewrite /countable_sum //=.
    rewrite /oapp. destruct pickle_inv => //=; rewrite /rvar_dist; field.
Qed.

Lemma is_Ex_sum :
  is_Ex (mkRvar Ω (λ x, X x + Y x)) (Ex X + Ex Y).
Proof.
  rewrite -Ex_sum; apply Ex_correct, ex_Ex_sum.
Qed.

End Ex_sum.

Section Ex_prop.

Variable (A: countType).
Variable (Ω: distrib A).
Variable (X: rrvar Ω).
Variable (EX_X: ex_Ex X).

Lemma ex_Ex_const (x: R):
  ex_Ex (rvar_const Ω x).
Proof.
  apply ex_Ex_by_pt.
  eapply ex_series_ext.
  { intros. by rewrite /rvar_const /= countable_sum_scal_l. }
  unshelve (apply: ex_series_scal_l).
  eexists; eapply pmf_sum1.
Qed.

Hint Resolve ex_Ex_const.

Lemma Ex_const (x: R):
  Ex (rvar_const Ω x) = x.
Proof.
  rewrite Ex_pt //. 
  erewrite Series_ext; last first.
  { intros. by rewrite /rvar_const /= countable_sum_scal_l. }
  by rewrite Series_scal_l pmf_sum1_Series Rmult_1_r.
Qed.

Lemma is_Ex_const (x: R):
  is_Ex (rvar_const Ω x) x.
Proof. rewrite -{2}(Ex_const x). by apply Ex_correct. Qed.

Lemma Ex_const_ge c :
  (∀ a, c <= X a) →
  c <= Ex X.
Proof.
  intros Hle.
  rewrite -(Ex_const c).
  apply Ex_ext_le => //=.
Qed.

Lemma ex_Ex_plus_l (x: R):
  ex_Ex (rvar_comp X (Rplus x)).
Proof.
  apply (ex_Ex_ext (mkRvar Ω (λ a, X a + (rvar_const Ω x) a))).
  * by apply ex_Ex_sum.
  * rewrite //=. intros; field.
Qed.

Lemma Ex_plus_l (x: R):
  Ex (rvar_comp X (Rplus x)) = x + Ex X.
Proof. rewrite -{2}(Ex_const x) -Ex_sum //. Qed.

Lemma ex_Ex_plus_r (x: R):
  ex_Ex (rvar_comp X (λ y, y + x)).
Proof.
  apply (ex_Ex_ext (mkRvar Ω (λ a, (rvar_const Ω x) a + X a))).
  * by apply ex_Ex_sum.
  * rewrite //=. intros; field.
Qed.

Lemma ex_Ex_plus_r' (x: R):
  ex_Ex (mkRvar Ω (λ a, X a + x)).
Proof. apply ex_Ex_plus_r. Qed.

Lemma Ex_plus_r (x: R):
  Ex (rvar_comp X (λ y, y + x)) = Ex X + x.
Proof. rewrite -{2}(Ex_const x) -Ex_sum //. Qed.

Lemma ex_Ex_scal_l (c: R):
  ex_Ex (rvar_comp X (λ x, c * x)).
Proof.
  apply ex_Ex_by_pt => //=.
  apply (ex_series_ext (λ n, Rabs c * (countable_sum (λ a, Rabs (X a) * (rvar_dist X a))) n)).
  * intros n. rewrite /countable_sum/oapp. destruct pickle_inv; auto.
    ** rewrite Rabs_mult /rvar_dist//=. field.
    ** by rewrite Rmult_0_r.
  * unshelve (apply: ex_series_scal_l). by apply ex_Ex_pt_abs. 
Qed.

Lemma Ex_scal_l (c: R):
  Ex (rvar_comp X (λ x, c * x)) = c * Ex X.
Proof. 
  rewrite ?Ex_pt //; last apply ex_Ex_scal_l.
  rewrite -Series_scal_l. apply Series_ext.
  intros n. rewrite /countable_sum/oapp. destruct pickle_inv; auto.
    ** rewrite /rvar_dist//=. field.
    ** by rewrite Rmult_0_r.
Qed.

Lemma ex_Ex_scal_r (c: R):
  ex_Ex (rvar_comp X (λ x, x * c)).
Proof.
  eapply ex_Ex_ext; first eapply ex_Ex_scal_l.
  intros a => //=. apply Rmult_comm.
Qed.
  
Lemma Ex_scal_r (c: R):
  Ex (rvar_comp X (λ x, x * c)) = Ex X * c.
Proof.
  erewrite Ex_ext.
  * rewrite Rmult_comm. eapply Ex_scal_l. 
  * apply ex_Ex_scal_r.
  * intros a => //=. apply Rmult_comm.
Qed.

Lemma ex_Ex_sum_inv (Y: rrvar Ω):
  ex_Ex (mkRvar Ω (λ a, X a + Y a)) →
  ex_Ex Y.
Proof.
  intros Hex.
  eapply (ex_Ex_ext (mkRvar Ω (λ a, (X a + Y a) + (rvar_comp X (λ x, -1 * x) a)))).
  - apply (@ex_Ex_sum _ _ (mkRvar Ω (λ a, X a + Y a))); auto.
    apply ex_Ex_scal_l.
  - intros => //=. field.
Qed.

Lemma ex_Ex_le (Y: rrvar Ω) :
  (∀ i, Rabs (Y i) <= Rabs (X i)) → ex_Ex Y.
Proof.
  intros Hbound.
  apply ex_Ex_by_pt.
  rewrite /ex_Ex.
  apply: ex_series_le; last (eapply ex_Ex_pt_abs, EX_X).
  intros n. rewrite /norm//=/countable_sum; destruct (pickle_inv _) => //=.
  * rewrite /abs//=. rewrite Rabs_right /rvar_dist; first apply Rmult_le_compat_r.
    ** apply Rge_le, pmf_pos. 
    ** eauto.
    ** apply Rle_ge, Rmult_le_pos; auto using Rabs_pos, Rge_le, pmf_pos.
  * rewrite /abs//=. rewrite Rabs_R0; reflexivity.
Qed.

Lemma ex_Ex_comp_abs:
  ex_Ex (rvar_comp X Rabs).
Proof.
  apply ex_Ex_le => i //=. rewrite Rabs_Rabsolu; reflexivity.
Qed.

End Ex_prop.

Arguments Ex_sum {_ _}.

Definition id_rvar {A: countType} (Ω: distrib A) : rvar Ω A :=
  mkRvar Ω (λ a, a).
Definition indicator {A: countType} {B: eqType} {Ω : distrib A} (X: rvar Ω B) (P: B → bool) :=
  rvar_comp X (λ a, if P a then 1 else 0).

Lemma ex_Ex_indicator {A} {B: eqType} {Ω : distrib A} (X: rvar Ω B) P:
  ex_Ex (indicator X P).
Proof.
  apply ex_Ex_by_pt.
  unshelve (apply: (ex_series_le _ (countable_sum (λ a : A, if P (X a) then Ω a else 0)))).
  - intros n. rewrite /norm//=/abs//=/countable_sum/oapp//=.
    destruct pickle_inv as [s|].
    * destruct (P _).
      ** rewrite Rabs_mult ?Rabs_R1.
         specialize (pmf_pos Ω s). intros. rewrite /rvar_dist Rabs_right //=. 
         nra.
      ** rewrite Rabs_mult ?Rabs_R0 Rmult_0_l. reflexivity.
    * rewrite Rabs_R0; reflexivity.
  - apply pr_ex_series.
Qed.
       

Lemma Ex_indicator {A} {B: eqType} {Ω : distrib A} (X: rvar Ω B) P:
  Ex (indicator X P) = pr_eq (indicator X P) 1.
Proof.
  rewrite Ex_pt; last apply ex_Ex_indicator.
  rewrite /pr_eq/pr. apply Series_ext.
  intros n. rewrite /countable_sum/oapp/rvar_dist; destruct pickle_inv => //=.
  destruct (P (X s)); case: ifP; move /eqP; intros; try congruence; try nra.
Qed.

Lemma Ex_indicator_le_1 {A} {B : eqType} {Ω: distrib A} (X : rvar Ω B) P:
  Ex (indicator X P) <= 1.
Proof. rewrite Ex_indicator. apply pr_le_1. Qed.

Lemma ex_Ex_abs {A} {Ω: distrib A} (X: rrvar Ω) :
  ex_Ex X ↔ ex_Ex (rvar_comp X (λ x, Rabs x)).
Proof.
  rewrite /ex_Ex; split.
  * intros Hex%ex_Ex_pt_abs.
    apply ex_Ex_by_pt.
    eapply ex_series_ext; last eapply Hex.
    intros n. rewrite /countable_sum; destruct pickle_inv as [s|] => //=.
    by rewrite Rabs_Rabsolu.
  * intros Hex%ex_Ex_pt_abs.
    apply ex_Ex_by_pt.
    eapply ex_series_ext; last eapply Hex.
    intros n. rewrite /countable_sum; destruct pickle_inv as [s|] => //=.
    by rewrite Rabs_Rabsolu.
Qed.

Lemma ex_Ex_pow_nat_le {A} {Ω: distrib A} (X: rrvar Ω) (r s: nat) :
  (0 < r)%nat → (r <= s)%nat →
  ex_Ex (rvar_comp X (λ x, (Rabs x)^s)) →
  ex_Ex (rvar_comp X (λ x, (Rabs x)^r)).
Proof.
  intros Hgt0_r Hle Hex.
  apply ex_Ex_by_pt.
  apply: ex_series_le; last first.
  { apply ex_Ex_pt, ex_Ex_plus_l with (x := 1), Hex. }
  intros n. rewrite /norm//=/countable_sum/abs//=.
  destruct (pickle_inv) as [a|] => //=.
  * rewrite Rabs_mult ?Rabs_Rabsolu.
    rewrite (Rabs_right (rvar_dist _ _)); auto using pmf_pos.
    apply Rmult_le_compat_r.
    ** apply Rge_le, pmf_pos. 
    ** rewrite Rabs_right; last apply Rle_ge, pow_le, Rabs_pos.
       destruct (Rle_dec 1 (Rabs (X a))).
       *** transitivity (Rabs (X a) ^ s).
           **** apply Rle_pow; auto.
           **** left. rewrite Rplus_comm. apply Rlt_plus_1.
       *** transitivity 1.
           **** left. apply pow_lt_1_compat; auto.
                split.
                ***** apply Rabs_pos.
                ***** by apply Rnot_le_gt.
           **** rewrite RPow_abs. specialize (Rabs_pos (X a ^ s)).
                intros. clear -H. rewrite -[a in a <= _]Rplus_0_r. 
                apply Rplus_le_compat_l. done.
  * rewrite Rabs_R0; reflexivity.
Qed.

Definition Var {A} {Ω: distrib A} (X: rrvar Ω) :=
  Ex (rvar_comp X (λ x, (x - Ex X)^2)).

Definition ex_Var {A} {Ω: distrib A} (X: rrvar Ω) :=
  ex_Ex X ∧ ex_Ex (rvar_comp X (λ x, (x - Ex X)^2)).

Lemma ex_Ex_second_moment {A} {Ω: distrib A} (X: rrvar Ω):
  ex_Ex (rvar_comp X (pow^~ 2%nat)) →
  ex_Ex X.
Proof.
  intros.
  apply ex_Ex_abs. apply (ex_Ex_ext (rvar_comp X (λ x, (Rabs x)^1))); last first.
  { rewrite //= => ?. by apply Rmult_1_r. }
  eapply (ex_Ex_pow_nat_le) with (s := 2%nat); auto.
  eapply ex_Ex_ext; eauto.
  intros a. move: (pow2_abs (X a)) => //=.
Qed.

Lemma ex_Var_second_moment {A} {Ω: distrib A} (X: rrvar Ω) :
  ex_Var X ↔ ex_Ex (rvar_comp X (λ x, x^2)).
Proof.
  split.
  - intros [HexX HexDiff].
    eapply (@ex_Ex_sum_inv _ _ (mkRvar Ω (λ x, X x * (-2 * Ex X) + (Ex X)^2))).
    * unshelve (apply: (ex_Ex_plus_r _ _ (mkRvar Ω (λ x, X x * (-2 * Ex X))) _ ((Ex X)^2))).
        by apply ex_Ex_scal_r. 
    * eapply ex_Ex_ext; first eapply HexDiff.
      intros a => //=. field.
  - intros Hex.
    split.
    * by apply ex_Ex_second_moment.
    * eapply (ex_Ex_ext (mkRvar Ω (λ a, (X a)^2
              + (mkRvar Ω (λ a, ((-2) * Ex X * (X a) + (Ex X)^2))) a))).
      ** apply (ex_Ex_sum _ _ (mkRvar Ω (λ a, (X a)^2))); auto.
         apply (ex_Ex_plus_r' _ _ (mkRvar Ω (λ a, -2 * Ex X * X a))).
         by apply ex_Ex_scal_l, ex_Ex_second_moment.
      ** intros a => //=. field.
Qed.

Lemma ex_Var_first_moment {A} {Ω: distrib A} (X: rrvar Ω) :
  ex_Var X → ex_Ex X.
Proof.
  intros. apply ex_Ex_second_moment. rewrite -ex_Var_second_moment. done. 
Qed.

(*
Hint Resolve ex_Var_first_moment.
*)

Lemma Var_Ex_diff {A} {Ω: distrib A} (X: rrvar Ω) :
  ex_Var X →
  Var X = Ex (rvar_comp X (λ x, x^2)) - (Ex X)^2.
Proof.
  intros HexVar. 
  rewrite /Var. 
  transitivity (Ex (mkRvar Ω (λ a, (X a)^2 + ((-2) * Ex X * (X a) + (Ex X)^2)))).
  - apply Ex_ext; first by destruct HexVar; auto.
    intros a => //=. field.
  - rewrite (Ex_sum (mkRvar Ω (λ a, (X a)^2)) (mkRvar Ω (λ a, (-2 * Ex X * X a + Ex X ^2)))).
    * rewrite (Ex_plus_r _ _ (mkRvar Ω (λ a, -2 * Ex X * X a))  _ ((Ex X)^2)) //=.
      ** rewrite Ex_scal_l //=; auto using ex_Var_first_moment.
         rewrite /rvar_comp/comp //=. rewrite Rmult_1_r. rewrite /Rminus.
         f_equal. field. 
      ** by apply ex_Ex_scal_l; auto using ex_Var_first_moment.
    * by rewrite -ex_Var_second_moment.
    * apply (ex_Ex_plus_r' _ _ (mkRvar Ω (λ a, -2 * Ex X * X a))).
      apply ex_Ex_scal_l, ex_Ex_second_moment. rewrite -ex_Var_second_moment. done.
Qed.

Definition Cov {A} {Ω: distrib A} (X Y : rrvar Ω) :=
  Ex (mkRvar Ω (λ a, (X a - Ex X) * (Y a - Ex Y))).

Definition ex_Cov {A} {Ω: distrib A} (X Y: rrvar Ω) :=
  ex_Ex X ∧ ex_Ex Y ∧ ex_Ex (mkRvar Ω (λ a, (X a - Ex X) * (Y a - Ex Y))).

(*
Lemma ex_Cov_ex_diff {A} {Ω: distrib A} (X Y: rrvar Ω) :
  ex_Cov X Y → ex_Ex (mkRvar Ω (λ a, X a * Y a)) ∧ ex_Ex X ∧ ex_Ex Y.
Proof.
  intros Hcov.
  repeat split.
  *  

Lemma Cov_Ex_diff {A} {Ω: distrib A} (X Y: rrvar Ω) :
  ex_Cov X Y →
  Cov X Y = Ex (mkRvar Ω (λ a, X a * Y a)) - Ex X * Ex Y.
Proof.
  intros Hex.

*)

Lemma distrib_of_rvar_pmf_sum1 {A: countType} {Ω: distrib A} {B: eqType} (X: rvar Ω B):
  is_series (countable_sum (λ x : [countType of imgT X], pr_eq X (sval x))) 1.
Proof.
  eapply (is_series_ext (countable_sum (λ x : [countType of imgT X], pr_eq X (sval x) * 1))).
  { intros => //=. rewrite /countable_sum; destruct pickle_inv; rewrite //= ?Rmult_1_r //=. }
  apply (Ex_comp_pt.is_series_Ex_comp_pt' _ _ _ X (λ _, 1)).
  * apply (ex_Ex_ext (rvar_const _ 1)); auto using ex_Ex_const.
  * rewrite -{2}(pmf_sum1_Series Ω).
    apply Series_ext => n. rewrite /countable_sum; destruct pickle_inv => //=.
    rewrite /rvar_dist; field.
Qed.

Definition distrib_of_rvar {A: countType} {Ω: distrib A} {B: eqType} (X: rvar Ω B) :=
  mkDistrib [countType of imgT X] (λ x, pr_eq X (sval x)) (λ x, pr_eq_ge_0 X (sval x))
            (distrib_of_rvar_pmf_sum1 X).

Lemma pr_pred_rvar {A} {B: eqType} {Ω: distrib A} (X: rvar Ω B) P :
  pr Ω (λ a, P (X a)) =
  Series (countable_sum (λ a : imgT X, if P (sval a) then pr_eq X (sval a) else 0)).
Proof.
  transitivity (pr_eq (indicator X (λ x, P x)) 1).
  {
    rewrite /pr_eq/pr. apply Series_ext => n. rewrite /countable_sum; destruct pickle_inv => //=.
    destruct (P _ ) => //=; case: ifP => //=; move /eqP; nra.
  }
  rewrite -Ex_indicator Ex_comp_pt.Ex_comp.
  - apply Series_ext => n. rewrite /countable_sum; destruct pickle_inv; rewrite //=.
    destruct (P _); nra.
  - eapply ex_Ex_le; first apply (@ex_Ex_const _ Ω 1).
    intros i => //=; destruct (P (X i)) => //=; rewrite ?Rabs_R0 ?Rabs_R1; nra.
Qed.

Lemma Ex_sum_n_le {A} {Ω: distrib A} (X: rrvar Ω) n:
  ex_Ex X →
  (∀ a, pr_eq X a > 0 → a >= 0) →
  sum_n (countable_sum (λ a : imgT X, pr_eq X (sval a) * sval a)) n <= Ex X.
Proof.
  intros Hex Hpos.
  apply is_series_partial_pos.
  - intros n'.  rewrite /countable_sum; destruct (pickle_inv _) as [s|] => //=.
    * destruct (pr_eq_ge_0 X (sval s)) as [Hge|Heq0].
      ** specialize (Hpos _ Hge). apply Rle_ge, Rmult_le_pos; auto using Rge_le.
         by left. 
      ** rewrite Heq0 Rmult_0_l. by right.
    * by right.
  - destruct (Ex_correct X); auto.
Qed.

Lemma Ex_sum_n_le_comp {A} {B} {Ω: distrib A} (X: rvar Ω B) f n:
  ex_Ex (rvar_comp X f) →
  (∀ a, pr_eq X a > 0 → f a >= 0) →
  sum_n (countable_sum (λ a : imgT X, pr_eq X (sval a) * f (sval a))) n <= Ex (rvar_comp X f).
Proof.
  intros Hex Hpos.
  rewrite Ex_comp_pt.Ex_comp //.
  apply is_series_partial_pos.
  - intros n'.  rewrite /countable_sum; destruct (pickle_inv _) as [s|] => //=.
    * destruct (pr_eq_ge_0 X (sval s)) as [Hge|Heq0].
      ** specialize (Hpos _ Hge). apply Rle_ge, Rmult_le_pos; auto using Rge_le.
         by left. 
      ** rewrite Heq0 Rmult_0_l. by right.
    * by right.
  - apply Ex_comp_pt.is_series_Ex_comp_pt'; auto.
    rewrite -Ex_comp_pt.Ex_comp //.
    rewrite Ex_pt //.
Qed.

Lemma pr_eq_sum_n_le_1 {A} {B} {Ω: distrib A} (X: rvar Ω B) P n:
  sum_n (countable_sum (λ a : imgT X, if P (sval a) then pr_eq X (sval a) else 0)) n <= 1.
Proof.
  etransitivity; last apply (Ex_indicator_le_1 X (λ x, P x)).
  apply is_series_partial_pos; last first. 
  rewrite Ex_comp_pt.Ex_comp.
  * eapply is_series_ext; last first.
    ** apply Series_correct.
       eexists. apply (Ex_comp_pt.is_series_Ex_comp_pt _ _ _ _ (λ x, if P x then 1 else 0)).
       apply ex_Ex_indicator.
    ** intros n'. rewrite /countable_sum. destruct (pickle_inv _) => //=; destruct (P _); nra.
  * apply ex_Ex_indicator.
  * intros n'. rewrite /countable_sum. destruct (pickle_inv _) => //=; try destruct (P _); try nra.
    apply pr_eq_ge_0.
Qed.

Definition sum_list_rrvar {A} {Ω: distrib A} (l: list (rrvar Ω)) : rrvar Ω :=
  mkRvar Ω (λ a, fold_right Rplus 0 (map (λ X, (rvar_fun _ _ X) a) l)).

Definition prod_list_rrvar {A} {Ω: distrib A} (l: list (rrvar Ω)) : rrvar Ω :=
  mkRvar Ω (λ a, fold_right Rmult 1 (map (λ X, (rvar_fun _ _ X) a) l)).

From mathcomp Require Import seq. 

Definition rvar_list {A} {B: eqType} {Ω: distrib A} (lX: list (rvar Ω B))
  : (rvar Ω [eqType of seq B]) :=
  mkRvar Ω (λ a, map (λ f, (rvar_fun _ _ f) a) lX).

Lemma sum_list_rrvar_alt {A} {Ω: distrib A} (l: list (rrvar Ω)):
  sum_list_rrvar l = rvar_comp (rvar_list l) (fold_right Rplus 0).
Proof. rewrite //=. Qed.

Lemma prod_list_rrvar_alt {A} {Ω: distrib A} (l: list (rrvar Ω)):
  prod_list_rrvar l = rvar_comp (rvar_list l) (fold_right Rmult 1).
Proof. rewrite //=. Qed.

Lemma ex_Ex_sum_list {A} {Ω: distrib A} (l: list (rrvar Ω)) :
  (∀ X, In X l → ex_Ex X) →
  ex_Ex (sum_list_rrvar l).
Proof.
  induction l as [| X l].
  - rewrite /sum_list_rrvar//= => ?; apply ex_Ex_const.
  - rewrite //= => Hex.
    apply (ex_Ex_ext (mkRvar Ω (λ a, X a + sum_list_rrvar l a))); auto using ex_Ex_sum.
Qed.

Lemma Ex_sum_list {A} {Ω: distrib A} (l: list (rrvar Ω)) :
  (∀ X, In X l → ex_Ex X) →
  Ex (sum_list_rrvar l) = fold_right Rplus 0 (map Ex l).
Proof.
  induction l as [| X l].
  - rewrite /sum_list_rrvar //= => ?; apply Ex_const. 
  - rewrite //= => Hin.
    rewrite (Ex_ext _ (mkRvar Ω (λ a, X a + sum_list_rrvar l a))); auto using ex_Ex_sum.
    * rewrite Ex_sum //.
      ** rewrite IHl //. intros; eapply Hin; by right.
      ** apply Hin. by left.
      ** apply ex_Ex_sum_list. intros; eapply Hin; by right.
    * by apply ex_Ex_sum_list.
Qed.

Lemma rvar_exists_support {A: countType} {B: eqType} {Ω: distrib A} (X: rvar Ω B):
  ∃ a, pr_eq X a > 0.
Proof.
  edestruct (distrib_exists_support Ω) as (a&Hgt0).
  exists (X a). 
  rewrite /pr_eq.
  rewrite /pr.
  eapply Rlt_gt, (Series_strict_pos _ (pickle a)).
  - intros n. rewrite /countable_sum. destruct (pickle_inv) => //=; try case: ifP.
    * intros. apply pmf_pos.
    * nra.
    * nra.
  - by rewrite /countable_sum pickleK_inv //= eq_refl. 
  - destruct (pr_ex_series Ω (λ a', X a' == X a)) as (v&?).
    by exists v.
Qed.

Lemma is_series_pr_eq_over_range {A : countType} {B: eqType} {Ω: distrib A} (X: rvar Ω B):
  is_series (countable_sum (λ v : imgT X, pr_eq X (sval v))) 1.
Proof.
  rewrite -(Ex_const _ Ω 1).
  assert (ex_Ex (rvar_comp X (λ _ : B, 1))).
  { eapply ex_Ex_ext; first eapply (ex_Ex_const _ _ 1). done. }
  assert (Ex (rvar_const Ω 1) = Ex (rvar_comp X (λ _, 1))) as ->.
  { rewrite Ex_pt //=. }
  eapply (is_series_ext (countable_sum (λ v: imgT X, pr_eq X (sval v) * 1))).
  { intros n. rewrite /countable_sum; destruct (pickle_inv) => //=; nra. } 
  apply (Ex_comp_pt.is_series_Ex_comp_pt') with (f:= (λ _, 1)) => //=.
  rewrite Ex_pt //=.
Qed.
  
Lemma Series_pr_eq_over_range {A : countType} {B: eqType} {Ω: distrib A} (X: rvar Ω B):
  Series (countable_sum (λ v : imgT X, pr_eq X (sval v))) = 1.
Proof.
  apply is_series_unique, is_series_pr_eq_over_range. 
Qed.

Module total_prob.
Section total_prob.
  
Variable (A: countType).
Variable (B: eqType).
Variable (Ω: distrib A).
Variable (X: rvar Ω B).
Variable (P: pred A).

Definition atotal := 
  λ mn, match mn with
        | (m, n) => 
          match (pickle_inv [countType of imgT X] m), (pickle_inv A n) with
            | Some v, Some a => (if (X a == sval v) && P a then Ω a else 0)
            | _, _ => 0
          end
        end.

Lemma ex_total_column_abs v:
  ex_series
    (λ k : nat,
     Rabs
       match pickle_inv A k with
       | Some a => if (X a == v) && P a then Ω a else 0
       | None => 0
       end).
Proof.
  apply: (ex_series_le _ (countable_sum (λ a : A, if P a then Ω a else 0)));
    last by apply pr_ex_series.
  intros n. rewrite /norm //= /abs //=.
  rewrite /countable_sum. rewrite /pr_eq/pr //=.
  destruct (pickle_inv _) as [s|] => //=.
  * rewrite Rabs_Rabsolu.
    rewrite Rabs_right; auto.
    ** case: ifP.
       *** move /andP => [? ->]. reflexivity.
       *** intros; case: ifP; auto using Rge_le, pmf_pos; reflexivity.
    ** case: ifP => ?.
       *** apply pmf_pos.
       *** nra. 
  * rewrite ?Rabs_R0. reflexivity.
Qed.

Lemma atotal_double_summable_by_column:
 double_summable atotal.
Proof.
  assert (Himg: ∀ v, X v \in img X).
  { intros v. rewrite /img //=. apply /exCP. eexists. eauto. }
  apply ex_series_rows_ds.
  - intros j. 
    * rewrite /atotal. destruct (pickle_inv _ j) as [v|]; last first.
      { exists 0. apply is_series_0 => n. rewrite Rabs_R0; done. }
      apply ex_total_column_abs.
  - rewrite /atotal.
    apply: (ex_series_le _ (countable_sum (λ v : imgT X, pr_eq X (sval v)))).
    { 
      intros n. rewrite /norm //= /abs //=.
      rewrite /countable_sum. rewrite /pr_eq/pr //=.
      assert (Hge0: ∀ k (s : imgT X),
          (λ k0 : nat,
                  match pickle_inv A k0 with
                  | Some a => if (X a == sval s) && P a then Ω a else 0
                  | None => 0
                  end) k >= 0).
      { intros k s.  destruct pickle_inv; try case: ifP; auto using pmf_pos; nra. }
      destruct (pickle_inv _) as [s|] => //=.
      * rewrite Rabs_right.
        ** apply: Series_le. intros n'; split.
           *** apply Rabs_pos.
           *** rewrite /countable_sum//=.
               destruct (pickle_inv _) => //=; last (rewrite Rabs_R0; reflexivity).
               case: ifP.
               **** move /andP => [-> ?]. rewrite Rabs_right; first reflexivity.
                    apply pmf_pos.
               **** rewrite Rabs_R0. intros; case: ifP; auto using Rge_le, pmf_pos; reflexivity.
           *** apply pr_ex_series.
        ** apply Rle_ge, Series_pos; auto.
      * rewrite Series_0 // Rabs_R0; reflexivity. 
    }
    exists 1; apply is_series_pr_eq_over_range.
Qed.

Lemma atotal_row_rewrite j:
  Series (λ k : nat, atotal (j, k))
  = countable_sum (λ b : imgT X, pr Ω (λ a, (X a == sval b) && P a)) j.
Proof.
 rewrite /atotal/countable_sum. 
 destruct (pickle_inv _ j) as [v|] => //=; last apply Series_0 => //=.
Qed.

Lemma atotal_column_rewrite k:
  Series (λ j : nat, atotal (j, k))
  = countable_sum (λ a, if P a then Ω a else 0) k. 
Proof.
  assert (Himg: ∀ v, X v \in img X).
  { intros v. rewrite /img //=. apply /exCP. eexists. eauto. }
 rewrite /atotal/countable_sum. 
 destruct (pickle_inv A k) as [s|].
 - rewrite //=. destruct (P s).
   * rewrite -{2}(Series_bump (@pickle [countType of imgT X] (exist _ (X s) (Himg s))) (Ω s)). 
     apply Series_ext => n.
     destruct (Nat.eq_dec ) as [Heqn|Hneq].
     ** subst. rewrite pickleK_inv //= eq_refl //=.
     ** specialize (pickle_invK [countType of imgT X] n).
        destruct (pickle_inv) as [s'|] => //=. intros Heq'.
        case: ifP => //=.
        rewrite andbT. move /eqP => Heq. subst.
        exfalso; apply Hneq. f_equal. apply sval_inj_pred => //=.
   * apply Series_0 => n //=. destruct (pickle_inv) => //=. by rewrite andbF.
 - rewrite //=. apply Series_0 => n //=. destruct (pickle_inv) => //=.
Qed.

Lemma pr_total_prob:
  pr Ω P = Series (countable_sum (λ r: imgT X, pr Ω (λ a, (X a == sval r) && P a))).
Proof.
  rewrite /pr.
  symmetry. etransitivity.
  { apply Series_ext. intros. by rewrite -atotal_row_rewrite. }
  {
    rewrite Series_double_swap; auto using atotal_double_summable_by_column.
    apply Series_ext => k.
    apply atotal_column_rewrite.
  }
Qed.
End total_prob.
End total_prob.

  
Lemma pr_total_prob {A : countType} {B: eqType} {Ω: distrib A} (X: rvar Ω B) P:
  pr Ω P = Series (countable_sum (λ r: imgT X, pr Ω (λ a, (X a == sval r) && P a))).
Proof.
  apply total_prob.pr_total_prob.
Qed.


Lemma img_alt {A: countType} {B: eqType} (f: A → B) i: (i \in img f) ↔ ∃ x, f x = i.
Proof.
  split; rewrite /img/in_mem//=.
  - move /exCP => [x Heq]. move /eqP in Heq. exists x. done.
  - intros [x Heq]. apply /exCP. exists x. subst. done.
Qed.

Lemma img_alt' {A: finType} {B: eqType} (f: A → B) i: 
  (i \in undup [seq f i | i <- Finite.enum A]) ↔ ∃ x, f x = i.  
Proof.
  split.
  - rewrite mem_undup. move /mapP => [a ? ->]. eexists; eauto.
  - intros [x Heq]. rewrite mem_undup. apply /mapP. eexists; eauto.
Qed.

Lemma pr_img {A} {B} {Ω : distrib A} (X: rvar Ω B) i: pr_eq X i > 0 → i \in img X.
Proof.
  rewrite /pr_eq/pr img_alt.
  move/Rgt_not_eq => Hsum0. 
  destruct (elimNf (exCP (λ x, X x == i))) as (x&?).
  - rewrite /exC. destruct (LPO_countb) as [|Hnone] => //=.
    exfalso. apply Hsum0. apply is_series_unique, is_seriesC_0.
    intros a. case: ifP; auto. intros. exfalso. eapply Hnone; eauto.
  - exists x. by apply /eqP.
Qed.

Lemma pr_img0 {A} {B} {Ω : distrib A} (X: rvar Ω B) i : pr_eq X i <> 0 → i \in img X.
Proof.
  rewrite /pr_eq.
  intros. apply pr_img.
  edestruct (ge_pr_0 (rvar_dist X)) as [Hg0|Hg0]; eauto.
  rewrite //= in Hg0.
Qed.

Lemma pr_img_nin {A B} {Ω: distrib A} (X: rvar Ω B) i: ~ (i \in img X) → pr_eq X i = 0.
Proof.
  intros Hnin. rewrite /pr_eq. edestruct (ge_pr_0 Ω); last eauto.
  exfalso. apply Hnin, pr_img. rewrite /pr_eq. nra.
Qed.

Lemma pr_img_gt {A} {Ω: distrib A} (X: rrvar Ω) i: pr_gt X i > 0 → ∃ i', i' > i ∧ i' \in img X.
Proof.
  rewrite /pr_gt.
  move/Rgt_not_eq => Hsum0.
  destruct (elimNf (exCP (λ x, Rgt_dec (X x) i))) as (x&Hx).
  - rewrite /exC. destruct (LPO_countb) as [|Hnone] => //=.
    exfalso. apply Hsum0. apply is_series_unique, is_seriesC_0.
    intros a. case: ifP; auto. intros. exfalso. eapply Hnone; eauto.
  - exists (X x). destruct (Rgt_dec); last by (exfalso; auto). 
    split; auto. apply img_alt. eauto.
Qed.

Lemma pr_img_ge {A} {Ω: distrib A} (X: rrvar Ω) i: pr_ge X i > 0 → ∃ i', i' >= i ∧ i' \in img X.
Proof.
  rewrite /pr_ge.
  move/Rgt_not_eq => Hsum0.
  destruct (elimNf (exCP (λ x, Rge_dec (X x) i))) as (x&Hx).
  - rewrite /exC. destruct (LPO_countb) as [|Hnone] => //=.
    exfalso. apply Hsum0. apply is_series_unique, is_seriesC_0.
    intros a. case: ifP; auto. intros. exfalso. eapply Hnone; eauto.
  - exists (X x). destruct (Rge_dec); last by (exfalso; auto). 
    split; auto. apply img_alt. eauto.
Qed.

Lemma SeriesC_pred_sat_le {A: countType} (f : A → R) (x : A) (P: pred A) :
  (∀ x, f x >= 0) →
  P x →
  ex_series (countable_sum (λ a : A, if P a then f a else 0)) →
  f x <= Series (countable_sum (λ a : A, if P a then f a else 0)).
Proof.
  intros Hge0 HP Hex.
  rewrite -[a in _ <= a](is_seriesC_filter_split _
                                                 (λ v : A, if P v then f v else 0)
                                                 (λ v, x == v)); swap 1 3.
  { by apply Series_correct. }
  { intros n; case: ifP; eauto; nra. }
  transitivity (f x + 0); first by nra.
  apply Rplus_le_compat; last first.
  { apply Series_pos. intros n. rewrite /countable_sum.
    destruct (pickle_inv _) => //=; last by nra.
    case : ifP; eauto using Rle_ge, Rle_refl.
    case : ifP; eauto using Rle_ge, Rle_refl.
  }
  rewrite (Series_ext _ (countable_sum (λ n : A, if n == x then f x else 0))); last first.
  { intros; apply countable_sum_ext.
    intros a. case: ifP.
    * move /eqP; intros; subst. rewrite eq_refl. rewrite HP. done.
    * move /eqP; intros Hneq. case: ifP => //=. move /eqP. 
      congruence.
  }
  rewrite (SeriesC_bump); nra.
Qed.

Lemma if_case_match {A: Type} (b b': bool) (x y: A): 
  b == b' → (if b then x else y) = (if b' then x else y).
Proof. 
    by move /eqP => ->. 
Qed.

Lemma pr_eq_sum_list {A: countType} {B: eqType} {Ω: distrib A} (X : rvar Ω B) l:
    Series (countable_sum (λ n : img_countType X,
                                          if sval n \in l then pr_eq X (sval n) else 0))
             = \big[Rplus/0]_(i <- undup l) pr_eq X i.
Proof.
  induction l.
  - rewrite big_nil. apply Series_0 => //=.
    intros n; rewrite /countable_sum; destruct (pickle_inv _); done.
  - rewrite /undup -/undup. case: ifP.
    * intros.  rewrite -IHl.
       apply SeriesC_ext => n. apply if_case_match.
       rewrite /in_mem //=.
       rewrite orb_idl //=.
       move /eqP; intros; subst; done.
    * intros Hnot_in. rewrite big_cons -IHl.
       rewrite -[a in a = _](is_seriesC_filter_split _
                                                     (λ v : imgT X, if sval v \in a :: l then
                                                                 pr_eq X (sval v)
                                                               else 0)
                                                     (λ v, a == sval v)); swap 1 3.
       ** apply Series_correct. apply (ex_seriesC_filter_P).
         *** intros; apply pr_eq_ge_0. 
         *** exists 1. apply is_series_pr_eq_over_range.
       ** intros n. case: ifP; auto using Rle_ge, Rle_refl, pr_eq_ge_0.
       ** f_equal.
          *** symmetry.  
              {
                destruct (Req_dec (pr_eq X a) 0) as [Heq0|Hneq0].
                * rewrite Heq0.
                  rewrite Series_0 //. intros n. rewrite /countable_sum.
                  destruct (pickle_inv _ n) => //=.
                  case: ifP => //=. move /eqP => Heq. subst.
                  case: ifP => //= ?.
                * apply pr_img0 in Hneq0.
                  replace (pr_eq X a) with (pr_eq X (sval (exist (λ x, x \in img X) a Hneq0 : imgT X)));
                    last by done.
                  rewrite -[a in a = _](SeriesC_bump _
                             ((exist (λ x: B, x \in img X) a Hneq0) : imgT X)).
                  apply SeriesC_ext => x.
                  case: ifP.
                  ** move /eqP; intros; subst => //=.
                     rewrite eq_refl. rewrite in_cons //= eq_refl //=. 
                  ** move /eqP; intros Hneq.
                     case: ifP.
                     *** move /eqP.  intros Heq. 
                         exfalso. apply Hneq. apply sval_inj_pred => //=.
                     *** done.
              }
          *** apply SeriesC_ext => x.
              case: ifP.
              **** intros Hnot. rewrite in_cons. rewrite eq_sym (negbTE Hnot) orFb.
                   done.
              **** move /eqP => ?; subst. by rewrite Hnot_in.
Qed.

Lemma pr_eq_le_sum_list {A: countType} {B: eqType} {Ω: distrib A} (X: rvar Ω B)
      (l: list B) b :
  ¬ (b \in l) →
  pr_eq X b <= 1 - \big[Rplus/0]_(i <- undup l) (pr_eq X i).
Proof.
  intros Hinin.
  rewrite -(Series_pr_eq_over_range X).
  rewrite -[a in _ <= a - _](is_seriesC_filter_split _ (λ v : imgT X, pr_eq X (sval v))
                                                 (λ v, (sval v) \in l)); swap 1 3.
  - apply Series_correct. eexists; apply is_series_pr_eq_over_range. 
  - intros; apply pr_eq_ge_0. 
  - rewrite pr_eq_sum_list. ring_simplify. 
    destruct (Req_dec (pr_eq X b) 0) as [Heq0|Hneq0].
    * rewrite Heq0.
      apply Series_pos. intros n. rewrite /countable_sum.
      destruct (pickle_inv _ n) => //=; last by nra.
      case: ifP; auto using pr_eq_ge_0; nra.
    * apply pr_img0 in Hneq0.
      replace (pr_eq X b) with (pr_eq X (sval (exist (λ x, x \in img X) b Hneq0 : imgT X)));
      last by done.
      apply (@SeriesC_pred_sat_le) with (x := (exist _ b Hneq0) : img_countType X)
                                     (f := λ x, pr_eq X (sval x))
                                     (P := λ x, sval x \notin l).
      ** intros; apply pr_eq_ge_0. 
      ** rewrite //=. by apply /negP.
      ** apply (ex_seriesC_filter_P).
         *** intros; apply pr_eq_ge_0. 
         *** exists 1. apply is_series_pr_eq_over_range.
Qed.