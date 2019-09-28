From discprob.basic Require Import base order.
From discprob.prob Require Import prob countable finite.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier FunctionalExtensionality Psatz.
Require Import Coq.omega.Omega.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.
Global Set Bullet Behavior "Strict Subproofs".

Notation "x ≤ y" := (Rle x y) (at level 70, no associativity).
Notation "x ≥ y" := (Rge x y) (at level 70, no associativity).

Lemma Finite_inj x y: Finite x = Finite y → x = y.
Proof.
  inversion 1. done.
Qed.
Lemma big_cons_Rplus:
  ∀ (I : Type) 
  (i : I) (r : seq I) (P : pred I) (F : I → R)
  (x:=\big[Rplus/0]_(j <- r | P j) F j),
  \big[Rplus/0]_(j <- (i :: r) | P j) F j = (if P i then (F i) else 0) + x. 
Proof.
  intros. rewrite big_cons. case: ifP => //. by rewrite Rplus_0_l.
Qed.

Lemma Rlt_not_eq': ∀ r1 r2, r1 < r2 → r2 ≠ r1.
Proof. intros ??? Hfalse. symmetry in Hfalse. eapply Rlt_not_eq; last exact Hfalse. done. Qed.

Lemma if_sumbool_case_match {A: Type} P Q (b: {P} + {¬ P}) (b': {Q} + {¬ Q}) (x y: A): 
  (P ↔ Q) → (if b then x else y) = (if b' then x else y).
Proof. 
  intros HPQ; destruct b as [p|np], b' as [q|nq] => //=. 
  - contradiction nq. by rewrite -HPQ. 
  - contradiction np. by rewrite HPQ. 
Qed.


(* TODO: lots of redundancy and duplication here *)

Lemma pr_sum_restrict {A: finType} (Ω: distrib A) (X: rrvar Ω) l P: 
  \big[Rplus/0]_(i <- l | P i) pr_eq X i = 
  \big[Rplus/0]_(i <- l | P i && (Rgt_dec (pr_eq X i) 0)) pr_eq X i.
Proof.
  symmetry; induction l.
  * rewrite ?big_nil //=.
  * rewrite ?big_cons. 
    symmetry. case: ifP.
    **  intros HP. rewrite //=.
        case: ifP.
        *** intros. f_equal; eauto.
        *** rewrite /pr//=. destruct (Rgt_dec) as [|Hnt] => // _. apply Rnot_lt_ge in Hnt.
            rewrite -[a in _ = a]Rplus_0_l; f_equal; eauto.
            move: Hnt.
            rewrite /pr_eq.
            edestruct (ge_pr_0 Ω) as [Hge|]; eauto.
            intros. exfalso. rewrite //= in Hnt. rewrite //= in Hge. fourier.
    ** rewrite //=.
Qed.


Section pr_gt.

Definition pr_gt_indicator {A} {Ω: distrib A} (T: rrvar Ω) r :=
  indicator T (λ n, Rgt_dec n r).

Lemma pr_gt_to_indicator {A} {Ω: distrib A} (T: rrvar Ω) r:
  pr (rvar_dist T) (λ n, Rgt_dec (T n) r) = pr_eq (pr_gt_indicator T r) 1.
Proof.
  rewrite /pr_eq/pr. apply Series_ext => n. rewrite /countable_sum; destruct pickle_inv => //=.
  destruct Rgt_dec; rewrite /rvar_dist//=; eauto; case: ifP => //=; move /eqP; nra.
Qed.
  
Variable A: finType.
Variable Ω: distrib A.
Variable T: rrvar Ω.

Lemma pr_gt_alt r: pr (rvar_dist T) (λ a, Rgt_dec (T a) r)
                 = \big[Rplus/0]_(v : imgT T) if (Rgt_dec (sval v) r) then pr_eq T (sval v) else 0.
Proof.
  rewrite pr_gt_to_indicator /pr_gt_indicator. apply Finite_inj.
  rewrite -Ex_indicator/indicator//=. rewrite Ex_fin_comp => //=. rewrite /index_enum/id_rvar//=.
  f_equal; eapply eq_bigr => ?? => //=. case: ifP => ?; destruct Rgt_dec => //=; nra.
Qed.

(* There must be a better way to do this kind of splitting on sequences... *)
Lemma pr_gt_alt3 r: pr (rvar_dist T) (λ n, Rgt_dec (T n) r) = 
                    \big[Rplus/0]_(i <- filter (λ x, Rgt_dec (sval x) r) 
                                     (Finite.enum [finType of imgT T])) (pr_eq T (sval i)). 
Proof.
  rewrite pr_gt_alt.
  rewrite big_filter //=.
  symmetry.
  transitivity (\big[Rplus/0]_(i : imgT (A:=A) T | (λ i, true) i && (Rgt_dec (sval i) r))
                 if (Rgt_dec (sval i) r) then pr_eq T (sval i) else 0).
  { apply eq_bigr. rewrite //=.  intros ?; destruct Rgt_dec => //=; done. }
  assert (H0: 0 = (\big[Rplus/0]_(i : imgT (A:=A) T | (λ i, true) i && ~~ (Rgt_dec (sval i) r))
                 if (Rgt_dec (sval i) r) then pr_eq T (sval i) else 0)).
  { 
    symmetry; apply big1 => i.  move /negP. destruct (Rgt_dec) => //=.
  }
  rewrite -[a in a = _]Rplus_0_r [a in _ + a = _]H0 -bigID.
  rewrite //=.
Qed.
End pr_gt.

Lemma pr_gt_alt_comp {A: finType} {B: eqType} {Ω: distrib A} (T: rvar Ω B) (f: B → R) r: 
 pr (rvar_dist (rvar_comp T f)) (λ n, Rgt_dec ((rvar_comp T f) n) r)
                 = \big[Rplus/0]_(v : imgT T) if (Rgt_dec (f (sval v)) r) then pr_eq T (sval v) else 0.
Proof.
  rewrite pr_gt_to_indicator /pr_gt_indicator. apply Finite_inj.
  rewrite -Ex_indicator/indicator//=. rewrite rvar_comp_assoc.
  rewrite Ex_fin_comp => //=. rewrite /index_enum/id_rvar//=.
  f_equal; eapply eq_bigr => ??; case: ifP; destruct (Rgt_dec) => //=; nra.
Qed.

Section pr_ge.

Definition pr_ge_indicator {A} {Ω: distrib A} (T: rrvar Ω) r :=
  indicator T (λ n, Rge_dec n r).

Lemma pr_ge_to_indicator {A} {Ω: distrib A} (T: rrvar Ω) r:
  pr (rvar_dist T) (λ n, Rge_dec (T n) r) = pr_eq (pr_ge_indicator T r) 1.
Proof.
  rewrite /pr_eq/pr. apply Series_ext => n. rewrite /countable_sum; destruct pickle_inv => //=.
  destruct Rge_dec; rewrite /rvar_dist//=; eauto; case: ifP => //=; move /eqP; nra.
Qed.
  

Variable A: finType.
Variable Ω: distrib A.
Variable T: rrvar Ω.

Lemma pr_ge_alt r: pr (rvar_dist T) (λ a, Rge_dec (T a) r)
                 = \big[Rplus/0]_(v : imgT T) if (Rge_dec (sval v) r) then pr_eq T (sval v) else 0.
Proof.
  rewrite pr_ge_to_indicator /pr_ge_indicator. apply Finite_inj.
  rewrite -Ex_indicator/indicator//=. rewrite Ex_fin_comp => //=. rewrite /index_enum/id_rvar//=.
  f_equal; eapply eq_bigr => ??; case: ifP; destruct Rge_dec => //=; nra.
Qed.

(* There must be a better way to do this kind of splitting on sequences... *)
Lemma pr_ge_alt3 r: pr (rvar_dist T) (λ n, Rge_dec (T n) r) = 
                    \big[Rplus/0]_(i <- filter (λ x, Rge_dec (sval x) r) 
                                     (Finite.enum [finType of imgT T])) (pr_eq T (sval i)). 
Proof.
  rewrite pr_ge_alt.
  rewrite big_filter //=.
  symmetry.
  transitivity (\big[Rplus/0]_(i : imgT (A:=A) T | (λ i, true) i && (Rge_dec (sval i) r))
                 if (Rge_dec (sval i) r) then pr_eq T (sval i) else 0).
  { apply eq_bigr. rewrite //= => ?; destruct Rge_dec => //=. }
  assert (H0: 0 = (\big[Rplus/0]_(i : imgT (A:=A) T | (λ i, true) i && ~~ (Rge_dec (sval i) r))
                 if (Rge_dec (sval i) r) then pr_eq T (sval i) else 0)).
  { 
    symmetry; apply big1 => i.  move /negP. destruct (Rge_dec) => //=.
  }
  rewrite -[a in a = _]Rplus_0_r [a in _ + a = _]H0 -bigID.
  rewrite //=.
Qed.
End pr_ge.

Lemma pr_ge_alt_comp {A: finType} {B: eqType} {Ω: distrib A} (T: rvar Ω B) (f: B → R) r: 
 pr (rvar_dist (rvar_comp T f)) (λ n, Rge_dec ((rvar_comp T f) n) r)
                 = \big[Rplus/0]_(v : imgT T) if (Rge_dec (f (sval v)) r) then pr_eq T (sval v) else 0.
Proof.
  rewrite pr_ge_to_indicator /pr_ge_indicator. apply Finite_inj.
  rewrite -Ex_indicator/indicator//=. rewrite rvar_comp_assoc.
  rewrite Ex_fin_comp => //=. rewrite /index_enum/id_rvar//=.
  f_equal; eapply eq_bigr => ??; case: ifP; destruct Rge_dec => //=; nra.
Qed.

Section pr_eq.

Definition pr_eq_indicator {A} {B: eqType} {Ω: distrib A} (T: rvar Ω B) r :=
  indicator T (λ n, n == r).

Lemma pr_eq_to_indicator {A} {B} {Ω: distrib A} (T: rvar Ω B) r:
  pr (rvar_dist T) (λ n, (T n) == r) = pr_eq (pr_eq_indicator T r) 1.
Proof.
  rewrite /pr_eq/pr. apply Series_ext => n. rewrite /countable_sum; destruct pickle_inv => //=.
  case: ifP => ?; rewrite /rvar_dist//=; eauto; case: ifP => //=; move /eqP; nra.
Qed.

Variable A: finType.
Variable B: eqType.
Variable Ω: distrib A.
Variable T: rvar Ω B.

Lemma pr_eq_alt r: pr (rvar_dist T) (λ a, (T a) == r)
                 = \big[Rplus/0]_(v : imgT T) if (sval v == r) then pr_eq T (sval v) else 0.
Proof.
  rewrite pr_eq_to_indicator /pr_gt_indicator. apply Finite_inj.
  rewrite -Ex_indicator/indicator//=. rewrite Ex_fin_comp => //=. rewrite /index_enum/id_rvar//=.
  f_equal; eapply eq_bigr => ??; case: ifP; nra.
Qed.

End pr_eq.

Lemma pr_eq_alt_comp {A: finType} {B C: eqType} {Ω: distrib A} (T: rvar Ω B) (f: B → C) r: 
  pr (rvar_dist (rvar_comp T f)) (λ n, (rvar_comp T f) n == r)
  = \big[Rplus/0]_(v : imgT T) if (f (sval v) == r) then pr_eq T (sval v) else 0.
Proof.
  rewrite pr_eq_to_indicator /pr_eq_indicator. apply Finite_inj.
  rewrite -Ex_indicator/indicator//=. rewrite rvar_comp_assoc.
  rewrite Ex_fin_comp => //=. rewrite /index_enum/id_rvar//=.
  f_equal; eapply eq_bigr => ??; case: ifP; nra.
Qed.

Section convert.
Lemma pr_gt_to_geq_eps {A: finType} {Ω: distrib A} (X: rrvar Ω) (x eps: R):
  (eps > 0 ∧ ∀ y, y \in img X → y ≠ x → Rabs (x - y) ≥ eps) →
    pr_gt X x = pr_ge X (x + eps/2).
Proof.      
  intros (Hgt0&HX).
  rewrite /pr_ge /pr_gt !pr_ge_alt !pr_gt_alt.
  rewrite big_seq_cond. 
  rewrite [a in _ = a]big_seq_cond.
  apply eq_bigr. intros (y&?) Hin => //=. rewrite Bool.andb_true_r in Hin.
  destruct (Rgt_dec) as [Hgt|Hngt] => //=.
  - destruct (Rge_dec) as [Hge|Hnge]; first done.
    exfalso; eapply Rlt_not_ge; last eapply (HX y); eauto.
    * rewrite Rabs_minus_sym Rabs_right; nra.
    * apply Rgt_not_eq. done.
  - destruct (Rge_dec); last done. 
    exfalso; eapply Rlt_not_ge; last eapply (HX y); eauto.
    * rewrite Rabs_minus_sym Rabs_right; nra.
    * apply Rlt_not_eq. nra.
Qed.

Lemma pr_ge_to_gt_eps {A: finType} {Ω: distrib A} (X: rrvar Ω) (x eps: R):
  (eps > 0 ∧ ∀ y, y \in img X → y ≠ x → Rabs (x - y) ≥ eps) →
    pr_ge X x = pr_gt X (x - eps/2).
Proof.      
  intros (Hgt0&HX).
  rewrite /pr_ge /pr_gt ?pr_ge_alt ?pr_gt_alt.
  rewrite big_seq_cond. 
  rewrite [a in _ = a]big_seq_cond.
  apply eq_bigr. intros (y&?) Hin => //=. rewrite Bool.andb_true_r in Hin.
  destruct (Rge_dec).
  - destruct (Rgt_dec); first done. 
    exfalso; eapply Rlt_not_ge; last eapply (HX y); eauto.
    * rewrite Rabs_minus_sym Rabs_right; nra.
    * apply Rlt_not_eq. nra. 
  - destruct (Rgt_dec); last done.
    exfalso; eapply Rlt_not_ge; last eapply (HX y); eauto.
    * rewrite Rabs_minus_sym Rabs_left; nra.
    * apply Rlt_not_eq. nra.
Qed.

Lemma pr_ge_split_eps {A: finType} {Ω: distrib A} (X: rrvar Ω) (x eps: R):
  (eps > 0 ∧ ∀ y, y \in img X → y ≠ x → Rabs (x - y) ≥ eps) →
    pr_eq X x = pr_ge X (x - eps/2) - pr_ge X (x + eps/2).
Proof.
  intros (Hgt0&HX).
  rewrite /pr_ge ?pr_ge_alt.
  rewrite /Rminus.
  rewrite -[a in _ = _ + - a](Rmult_1_l) Ropp_mult_distr_l.
  rewrite big_distrr //=.
  rewrite -big_split //=.
  rewrite {1}/pr_eq ?pr_eq_alt.
  rewrite big_seq_cond. 
  rewrite [a in _ = a]big_seq_cond.
  apply eq_bigr. intros (y&?) Hin => //=. rewrite Bool.andb_true_r in Hin.
  case: ifP.
  - move /eqP => ->. 
    destruct (Rge_dec) as [Hle|Hle]; last nra.
    destruct (Rge_dec) as [Hle'|Hle']; first nra.
    rewrite Rmult_0_r Rplus_0_r //.
  - move /eqP => Hneq. 
    destruct (Rge_dec) as [Hle|Hle] => //=; try nra;
    destruct (Rge_dec) as [Hle'|Hle'] => //=; try nra.
    exfalso. 
    eapply Rlt_not_ge; last eapply (HX y); eauto.
    assert (y - x ≤ eps / 2) by nra.
    assert (x - y ≤ eps / 2) by fourier.
    destruct (Rle_dec 0 (x - y)) as [?|Hgt%Rnot_le_gt].
    ** rewrite Rabs_right; fourier.
    ** rewrite Rabs_minus_sym Rabs_right; fourier. 
Qed.

Lemma Rmin_dist_list (l: seq R) (x: R):
  ∃ eps, eps > 0 ∧ ∀ y, y \in l → y ≠ x → Rabs (x - y) >= eps.
Proof.                               
  exists (foldl (Rmin) 1 (map (λ y, Rabs (x - y)) (filter (predC1 x) l))).
  split.
  * assert (1 > 0) as Hgt0 by fourier.
    revert Hgt0; generalize 1.
    induction l.
    ** rewrite //=; fourier.
    ** rewrite //=. case: ifP.
       *** rewrite map_cons //=. 
           move /eqP => Hneq r Hgt.
           eapply IHl.
           apply Rmin_case => //.
           apply Rabs_pos_lt. intros Heq. 
           apply Hneq; symmetry; by apply Rminus_diag_uniq.
       *** intros; eauto.
  * intros y Hin Hneq.
    generalize 1. induction l.
    ** rewrite //=.
    ** rewrite in_cons in Hin.
       move /orP in Hin; destruct Hin as [Heqa|Hinl].
       *** move /eqP in Heqa.
           subst. move /eqP /negbTE in Hneq. rewrite //= Hneq /=.
           intros. apply Rle_ge.  eapply Rle_trans; first eapply seq_ext.foldl_Rmin.
           apply Rmin_r.
       *** rewrite //=. case: ifP; intros; eapply IHl; eauto.
Qed.


(* Because we are working with finite probability spaces, the following is true: *)

Lemma pr_ge_split2 {A B: finType} {Ω: distrib A} {Ω': distrib B} (X: rrvar Ω) (Y: rrvar Ω')
      (x: R): ∃ x1 x2, 
    pr_eq X x = pr_ge X x1 - pr_ge X x2 ∧
    pr_eq Y x = pr_ge Y x1 - pr_ge Y x2.
Proof.
  edestruct (Rmin_dist_list (map sval (Finite.enum [finType of imgT X])
                            ++ map sval (Finite.enum [finType of imgT Y])) x) as (eps&Hgt0&Hdist).
  exists (x - eps/2). exists (x + eps/2).
  split; eapply pr_ge_split_eps.
  - split; auto. intros. eapply Hdist; auto.
    rewrite mem_cat. apply /orP; left.
    rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval.
    by apply img_alt', img_alt.
  - split; auto. intros. eapply Hdist; auto.
    rewrite mem_cat. apply /orP; right. 
    rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval.
    by apply img_alt', img_alt.
Qed.

Lemma pr_gt_to_geq2 {A B: finType} {Ω: distrib A} {Ω': distrib B} (X: rrvar Ω) (Y: rrvar Ω')
      (x: R): ∃ x',
    pr_gt X x = pr_ge X x' ∧
    pr_gt Y x = pr_ge Y x'.
Proof.
  edestruct (Rmin_dist_list (map sval (Finite.enum [finType of imgT X])
                            ++ map sval (Finite.enum [finType of imgT Y])) x) as (eps&Hgt0&Hdist).
  exists (x + eps/2).
  split; eapply pr_gt_to_geq_eps.
  - split; auto. intros. eapply Hdist; auto.
    rewrite mem_cat. apply /orP; left.
    rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval.
    by apply img_alt', img_alt.
  - split; auto. intros. eapply Hdist; auto.
    rewrite mem_cat. apply /orP; right. 
    rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval.
    by apply img_alt', img_alt.
Qed.

Lemma pr_ge_to_gt2 {A B: finType} {Ω: distrib A} {Ω': distrib B} (X: rrvar Ω) (Y: rrvar Ω')
      (x: R): ∃ x',
    pr_ge X x = pr_gt X x' ∧
    pr_ge Y x = pr_gt Y x'.
Proof.
  edestruct (Rmin_dist_list (map sval (Finite.enum [finType of imgT X])
                            ++ map sval (Finite.enum [finType of imgT Y])) x) as (eps&Hgt0&Hdist).
  exists (x - eps/2).
  split; eapply pr_ge_to_gt_eps.
  - split; auto. intros. eapply Hdist; auto.
    rewrite mem_cat. apply /orP; left.
    rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval.
    by apply img_alt', img_alt.
  - split; auto. intros. eapply Hdist; auto.
    rewrite mem_cat. apply /orP; right. 
    rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval.
    by apply img_alt', img_alt.
Qed.
End convert.

Definition eq_dist {A B: countType} {C: eqType} {Ω1: distrib A} {Ω2: distrib B}
           (X: rvar Ω1 C) (Y: rvar Ω2 C) := ∀ x, pr_eq X x = pr_eq Y x.

Lemma eq_dist_ext {A: countType} {B: eqType} {Ω: distrib A} (X Y: rvar Ω B) :
  (∀ x: A, X x = Y x) →
  eq_dist X Y.
Proof.
  intros Hext v. rewrite /pr_eq. apply pr_eq_pred' => i; by rewrite Hext.
Qed.
  
Lemma eq_dist_refl {A: countType} {C: eqType} {Ω: distrib A} (X: rvar Ω C) :
  eq_dist X X.
Proof. rewrite /eq_dist => x; done. Qed.

Lemma eq_dist_sym {A B: countType} {C: eqType} {Ω: distrib A} {Ω': distrib B}
      (X: rvar Ω C) (Y: rvar Ω' C) :
  eq_dist X Y → eq_dist Y X.
Proof. rewrite /eq_dist => ??; done. Qed.

Lemma eq_dist_trans {A B C: countType} (D: eqType) {ΩA: distrib A} {ΩB: distrib B} {ΩC: distrib C}
      (X: rvar ΩA D) (Y: rvar ΩB D) (Z: rvar ΩC D) :
  eq_dist X Y → eq_dist Y Z → eq_dist X Z.
Proof. rewrite /eq_dist => Hxy Hyz x. etransitivity; eauto. Qed.

Global Instance eq_dist_Reflexive {A} {B} {Ω}: Reflexive (@eq_dist A A B Ω Ω).
Proof. intros ?. apply eq_dist_refl. Qed.

Lemma eq_dist_comp {A1 A2: finType} {B C: eqType} {Ω1: distrib A1} {Ω2: distrib A2}
      (X1: rvar Ω1 B) (X2: rvar Ω2 B) (f: B → C) :
  eq_dist X1 X2 → eq_dist (rvar_comp X1 f) (rvar_comp X2 f).
Proof.  
  intros Heq c. rewrite /pr_eq ?pr_eq_alt_comp. 
  rewrite -(big_map sval (λ x, true) (λ v, if f v == c then pr_eq X1 v else 0)). 
  rewrite -(big_map sval (λ x, true) (λ v, if f v == c then pr_eq X2 v else 0)). 
  rewrite bigop_cond_non0.
  eapply (sum_reidx_map _ _ _ _ (λ x, x)).
  - intros. by rewrite Heq. 
  - rewrite //=. intros a ?. case: ifP; last by (intros ?; move /eqP; nra). 
    intros _.  move /eqP. rewrite Heq => Hnon0.
    split; auto.
    assert (a \in img X2) as Hin.
    { apply pr_img. move: Hnon0. rewrite /pr_eq. edestruct (ge_pr_0 Ω2); eauto; nra. }
    destruct (proj1 (img_alt X2 a) Hin) as (x&Heq').
    subst. apply /mapP. 
    exists (exist _ (X2 x) Hin) => //=.
    rewrite /index_enum [Finite.enum]unlock //=. apply img_fin_mem.
  - intros b Hin _ Hfalse. 
    rewrite -Heq. apply /eqP.
    case_eq ((if f b == c then pr_eq X1 b else 0) == 0); auto.
    move /eqP => Hneq.
    exfalso; apply Hfalse. 
    exists b; split; auto.
    * move: Hneq. case: ifP; last (intros ?; nra). 
      move /eqP => _  Himg. 
      assert (b \in img X1) as Hin'.
      { apply pr_img. move: Himg. rewrite /pr_eq.  edestruct (ge_pr_0 Ω1); eauto; nra. }
      destruct (proj1 (img_alt X1 b) Hin') as (x&Heq').
      subst. apply /mapP. 
      exists (exist _ (X1 x) Hin') => //=.
      rewrite /index_enum [Finite.enum]unlock //=. apply img_fin_mem.
    * split; auto. rewrite /=. apply /eqP. done.
  - rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval. apply undup_uniq.
  - rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval. apply undup_uniq.
  - auto.
Qed.

Lemma big_mkcond_sumbool
     : ∀ (R : Type) (idx : R) (op : Monoid.law idx) (I : Type) (r : seq I) (Q S: I → Prop)
       (P : ∀ i, {Q i} + {S i}) (F : I → R),
       \big[op/idx]_(i <- r | is_left (P i)) F i = \big[op/idx]_(i <- r) (if P i then F i else idx).
Proof.
  intros. rewrite big_mkcond. apply eq_bigr => i ?. destruct (P i) => //=.
Qed.

Lemma eq_dist_pr_ge {A B: finType} {Ω: distrib A} {Ω': distrib B} (X: rrvar Ω)
      (Y: rrvar Ω'):
  eq_dist X Y ↔ (∀ x, pr_ge X x = pr_ge Y x).
Proof.
  rewrite /eq_dist; split.
  - intros Heqd x. rewrite /pr_ge. rewrite ?pr_ge_alt. 
    rewrite -?big_mkcond_sumbool.
    rewrite -!(big_map sval (λ y, Rge_dec y x)).
    rewrite //=.
    rewrite (pr_sum_restrict). 
    apply sum_reidx_map with (h := λ x, x); auto.
    * intros a Hin. move /andP => [Hge Hgt].
      destruct (Rgt_dec) => //=.
      split; auto.
      rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval. 
      apply img_alt', img_alt.
      apply pr_img. rewrite -Heqd. done.
    * intros ??? Hfalse. edestruct (pr_eq_ge_0 Y); eauto.
      exfalso; apply Hfalse.
      eexists. split; eauto.
      ** rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval. 
         apply img_alt', img_alt, pr_img. rewrite Heqd /pr. eauto.
      ** split; auto. apply /andP; split; auto.
         rewrite Heqd /pr. destruct (Rgt_dec) => //=.
    * rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval. apply undup_uniq.
    * rewrite /index_enum [Finite.enum]unlock //=. rewrite img_fin_enum_sval. apply undup_uniq.
  - intros Heqd x. 
    edestruct (pr_ge_split2 X Y x) as (x1&x2&HeqX&HeqY).
    rewrite HeqX HeqY ?Heqd. done.
Qed.

Lemma eq_dist_pr_gt {A B: finType} {Ω: distrib A} {Ω': distrib B}
      (X: rrvar Ω) (Y: rrvar Ω'): 
  eq_dist X Y ↔ (∀ x, pr_gt X x = pr_gt Y x).
Proof.
  rewrite eq_dist_pr_ge; split.
  - intros Heqd x. 
    edestruct (pr_gt_to_geq2 X Y x) as (x1&HeqX&HeqY).
    rewrite HeqX HeqY ?Heqd. done.
  - intros Heqd x. 
    edestruct (pr_ge_to_gt2 X Y x) as (x1&HeqX&HeqY).
    rewrite HeqX HeqY ?Heqd. done.
Qed.

Module eq_dist_Ex.
Section eq_dist_Ex.

  Variable (A1 A2: countType).
  Variable (B: eqType).
  Variable (Ω1: distrib A1).
  Variable (Ω2: distrib A2).
  Variable (X1: rvar Ω1 B).
  Variable (X2: rvar Ω2 B).
  Variable (f: B → R).

  Variable (EQDIST: eq_dist X1 X2).
  Variable (EX: ex_Ex (rvar_comp X1 f)).

  Definition a := countable_sum (λ r: imgT X1, pr_eq X1 (sval r) * f (sval r)).
  Definition a' :=
         λ n, match n with
              | O => 0
              | S n' => countable_sum (λ r : imgT X1, pr_eq X1 (sval r) * f (sval r)) n'
              end.
  Definition σ := λ n,
            match pickle_inv [countType of imgT X2] n with
            | None => O
            | Some yb =>
              match Rgt_dec (pr_eq X1 (sval yb)) 0 with
              | left Hpf => S (@pickle [countType of imgT X1] (exist _ (sval yb) (pr_img _ _ Hpf)))
              | _ => O
              end
            end.

  Lemma σinj: ∀ n n', a' (σ n) <> 0 → σ n = σ n' → n = n'.
  Proof.
    intros n n'.
    rewrite /σ.
    case_eq (pickle_inv [countType of imgT X2] n); rewrite //=.
    intros s Heqs.
    case_eq (pickle_inv [countType of imgT X2] n'); rewrite //=.
    - intros s' Heqs'. rewrite Heqs'.
      do 2 destruct (Rgt_dec) => //=.
      * intros ? Heq. inversion Heq as [Heq']. apply pickle_inj in Heq'.
        eapply pickle_inv_some_inj; eauto.
        rewrite Heqs Heqs'. f_equal. inversion Heq'.
        by apply sval_inj_pred.
    - intros Hnone. 
      destruct (Rgt_dec) => //=.
      rewrite Hnone.
      intros Heqa' Heq0. inversion Heq0.
  Qed.

  Lemma σcov: ∀ n, a' n <> 0 → ∃ m, σ m = n.
  Proof.
    intros n. rewrite /a'. destruct n => //=.
    rewrite /countable_sum.
    case_eq (pickle_inv (img_countType X1) n).
    - intros s Heq => //= Hneq0.
      rewrite EQDIST in Hneq0.
      assert (Hneq0': pr_eq X2 (sval s) <> 0).
      { intros Heq0. rewrite Heq0 Rmult_0_l //= in Hneq0. }
      exists (@pickle [countType of imgT X2] (exist _ (sval s) (pr_img0 _ _ Hneq0'))).
      rewrite /σ pickleK_inv //=.
      destruct (Rgt_dec) as [|Hngt].
      * f_equal. apply pickle_inv_some_inv. rewrite Heq.
        f_equal. apply sval_inj_pred => //=.
      * exfalso. rewrite EQDIST in Hngt. destruct (pr_eq_ge_0 X2 (sval s)); nra.
    - rewrite //=.
  Qed.

  Lemma ex_Ex_alt:
    ex_series (Rabs \o a').
  Proof.
    apply ex_series_incr_1 => //=.
    eapply (ex_series_ext); last by eapply (Ex_comp_pt.ex_series_Ex_comp_pt_abs _ _ _ X1 f).
    intros n. rewrite /countable_sum.
    destruct (pickle_inv) => //=.
    * rewrite Rabs_mult. symmetry. rewrite Rabs_right; last by apply pr_eq_ge_0.
      done.
    * by rewrite Rabs_R0.
  Qed.

  Lemma rearrange:
    ex_series (λ n, Rabs (a' (σ n))) ∧
    is_series (λ n, a' (σ n)) (Series a').
  Proof.
    destruct (ex_Ex_alt) as (v&Hisv).
    edestruct (rearrange.series_rearrange_covering a' σ).
    - apply σinj. 
    - apply σcov.
    - eauto.
    - split.
      ** exists v; eauto. 
      ** eauto.
  Qed.

  Lemma a'_equal_ex_X1:
    Ex (rvar_comp X1 f) = Series a'.
  Proof.
    rewrite /a'.
    rewrite Series_incr_1; last first.
    { apply ex_series_Rabs, ex_Ex_alt. }
    rewrite Rplus_0_l //.
    by apply Ex_comp_pt.Ex_comp.
  Qed.

  Lemma ex_Ex_eq_dist:
    ex_Ex (rvar_comp X2 f).
  Proof.
    apply ex_Ex_comp_by_alt.
    destruct rearrange as (Hex&_).
    eapply ex_series_ext; last eapply Hex. 
    intros n => //=.
    rewrite /a'/σ/countable_sum.
    destruct (pickle_inv) => //=; last by apply Rabs_R0.
    destruct Rgt_dec => //=.
    * rewrite pickleK_inv //= Rabs_mult.
      rewrite Rabs_right; last by nra.
      rewrite EQDIST //.
    * destruct (pr_eq_ge_0 X1 (sval s)) as [?|Heq0]; first by nra.
      rewrite -EQDIST Heq0 Rabs_R0; nra.
  Qed.

  Lemma Ex_eq_dist:
    Ex (rvar_comp X1 f) = Ex (rvar_comp X2 f).
  Proof.
    rewrite a'_equal_ex_X1.
    transitivity (Series (a' \o σ)).
    { symmetry.  apply is_series_unique. destruct rearrange; eauto. }
    rewrite Ex_comp_pt.Ex_comp; last apply ex_Ex_eq_dist.
    apply Series_ext.
    intros n => //=.
    rewrite /a'/σ/countable_sum.
    destruct (pickle_inv) => //=.
    destruct Rgt_dec => //=.
    - rewrite pickleK_inv //= EQDIST //.
    - destruct (pr_eq_ge_0 X1 (sval s)) as [?|Heq0]; first by nra.
      rewrite -EQDIST Heq0; nra.
  Qed.
End eq_dist_Ex.
End eq_dist_Ex.

Definition ex_Ex_eq_dist := eq_dist_Ex.ex_Ex_eq_dist.
Definition Ex_eq_dist := eq_dist_Ex.Ex_eq_dist.
Arguments ex_Ex_eq_dist {_ _ _ _ _}.
Arguments Ex_eq_dist {_ _ _ _ _}.

Lemma Ex_eq_dist_fin {A: finType} {B: countType}
      {Ω: distrib A} {Ω': distrib B} (X: rrvar Ω) (Y: rrvar Ω'):
  eq_dist X Y → Ex X = Ex Y.
Proof.
  intros. apply: (Ex_eq_dist _ _ id) => //=.
Qed.
