From discprob.basic Require Import base order.
From discprob.prob Require Import prob countable finite stochastic_order.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp Require Import tuple finfun bigop prime binomial finset.
Require Import Reals Fourier FunctionalExtensionality Psatz.
Require Import Coq.omega.Omega.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.
Global Set Bullet Behavior "Strict Subproofs".

Section rec_convert_unary.
Variable X: eqType.
Variable size: X → R.
Variable A A' B : X → finType.
Variable ΩT: ∀ x, distrib (A x). 
Variable ΩT': ∀ x, distrib (A' x). 
Variable Ωh: ∀ x, distrib (B x). 
Variable T: ∀ x: X, rrvar (ΩT x).
Variable T': ∀ x: X, rrvar (ΩT' x).
Variable h: ∀ x: X, rvar (Ωh x) X.
Variable P: X → Prop.
Variable hP: ∀ x n, P x → P  ((h x) n).
Variable G: R → R.
Variable a: R → R.

Lemma eq_dist_unary_rec_gt:
  (∀ z, P z → eq_dist (T' z) (T z)) →
  (∀ z r, P z → pr_gt (T z) r <= \big[Rplus/0]_(x' : imgT (h z)) 
                        (pr_eq (h z) (sval x') * pr_gt (rvar_comp (T (sval x')) G) (r - a (size z))))
                        →
  ∀ z r,
  P z →
  pr_gt (T' z) r <= \big[Rplus/0]_(x' : imgT (h z)) 
                        (pr_eq (h z) (sval x') * pr_gt (rvar_comp (T' (sval x')) G) (r - a (size z))).
Proof.
  intros Heq_dist Hrec z r HP. rewrite (proj1 (eq_dist_pr_gt _ _) (Heq_dist _ HP)).
  etransitivity; first apply Hrec; auto.
  right.
  apply eq_bigr => i ?. f_equal. 
  apply (proj1 (eq_dist_pr_gt (rvar_comp (T (sval i)) G)
                                 (rvar_comp (T' (sval i)) G))).
  apply: eq_dist_comp.
  intros r'.
  rewrite ?Heq_dist //.
  destruct i as (i&Hin). clear -HP Hin hP. rewrite /sval. apply img_alt in Hin.
  destruct Hin as (x&<-). by apply hP.
Qed.


Variable Trec:
  ∀ x r, P x → pr_eq (T x) r = \big[Rplus/0]_(x' : imgT (h x)) 
                        (pr_eq (h x) (sval x') * pr_eq (rvar_comp (T (sval x')) G)
                                                       (r - a (size x))).


Lemma img_Trec_unary b z x: 
  P z →
  pr_eq (rvar_comp (T x) G) b ≠ 0 →
  x \in img (h z) → 
  pr_eq (h z) x ≠ 0 →
  b + a (size z) \in img (T z).
Proof.
  intros HP Hneq0 Hin Hneq0'. apply pr_img.
  specialize (Rmult_neq_0_compat _ _ Hneq0 Hneq0'). intros.
  enough (Hneq: pr_eq (T z) (b + a (size z)) ≠ 0).
  { move:Hneq. rewrite /pr_eq.
    intros. edestruct (ge_pr_0 (rvar_dist (T z))) as [|Heq0]; first eauto.
    rewrite Heq0 in Hneq. congruence. }
  rewrite Trec; last done.
  intros Hfalse.
  symmetry in Hfalse.
  enough (Hfalse': ∀ x', x' \in img (h z) → pr_eq (h z) x' * 
                  (pr_eq (rvar_comp (T x') G)
                     (b + a (size z) - a (size z))) = 0).
  { specialize (Hfalse' x). move:Hfalse'.
    rewrite /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r.
    rewrite Rmult_comm. auto. 
  }
  intros x' Hin'. edestruct (Req_dec) as [Heq|Hneq]; first apply Heq. 
  exfalso. eapply Rlt_not_eq; last apply Hfalse.
  apply Rlt_0_bigr.
  - intros. replace 0 with (0 * 0) by nra. apply Rmult_le_compat; try nra.
    * apply Rge_le, ge_pr_0.
    * apply Rge_le, ge_pr_0.
  - exists (exist _ x' Hin'); repeat split; auto.
    rewrite //=.
    specialize (pr_eq_ge_0 (h z) x').
    specialize (pr_eq_ge_0 (rvar_comp (T x') G)
                           (b + a (size z) - a (size z))).
    clear -Hneq. rewrite //=. intros ??.  rewrite //= in Hneq. nra.
Qed.

Lemma eq_dist_unary_rec:
  (∀ z, P z → eq_dist (T' z) (T z)) →
  ∀ z r,
  P z →
  pr_eq (T' z) r = \big[Rplus/0]_(x' : imgT (h z)) 
                        (pr_eq (h z) (sval x') * pr_eq (rvar_comp (T' (sval x')) G) (r - a (size z))).
Proof.
  intros Heq_dist z r HP. rewrite Heq_dist // Trec //.
  apply eq_bigr => i ?. f_equal. 
  apply: eq_dist_comp.
  intros r'.
  rewrite ?Heq_dist //.
  destruct i as (i&Hin). clear -HP Hin hP. rewrite /sval. apply img_alt in Hin.
  destruct Hin as (x&<-). by apply hP.
Qed.

Lemma rec_pr_rec_gt_unary z r:
  P z →
  pr_gt (T z) r ≤ \big[Rplus/0]_(x' : imgT (h z))
                        (pr_eq (h z) (sval x') * 
                         pr_gt (rvar_comp (T (sval x')) G) (r - a (size z))).
Proof.
  rewrite /pr_gt pr_gt_alt3. 
  etransitivity.
  { right. eapply eq_bigr => ? _. by apply Trec. }
  rewrite //=.
  rewrite exchange_big //=.
  apply Rle_bigr => x'.
  rewrite -big_distrr //=. 
  set (Trec' := rvar_comp (T (sval x')) G); 
    rewrite -/Trec'.
  transitivity (pr_eq (h z) (sval x') *
                \big[Rplus/0]_(i : imgT (A:=A z) (T z) 
                              | (Rgt_dec (sval i) r) && (pr_eq Trec' ((sval i) - a (size z)) != 0)) 
                 pr_eq Trec' ((sval i) - a (size z))).
  {  
    right. symmetry.
    eapply Rmult_eq_0_inv_r => Hneq //=. rewrite /index_enum.
    apply (@sum_reidx_map  [finType of imgT (T z)] _ _ _ _ _ (λ x, x)); auto.
    - rewrite /id //=. intros ??. move/andP=>[? ?].
      split; auto. rewrite mem_filter. apply /andP.
      split; auto.
    - intros b Hin' HQ Hfalse. 
      case (Req_dec (pr_eq Trec' (sval b - a (size z))) 0); auto.
      intros Hneq0. exfalso. eapply Hfalse.
      exists b. rewrite mem_filter in Hin'. move /andP in Hin'. destruct Hin' as [-> ->].
      split; auto. rewrite //=. split; auto.
      move: Hneq0. move /eqP => -> //.
    - rewrite -enumT. apply enum_uniq. 
    - rewrite -enumT. apply filter_uniq => //=. apply: enum_uniq. 
  }
  transitivity (pr_eq (h z) (sval x') * pr_gt Trec' (r - a (size z))).
  {
    right. 
    eapply Rmult_eq_0_inv_r => Hneq.
    rewrite /pr_gt. rewrite pr_gt_alt3.
    rewrite -(big_map sval (λ x, (Rgt_dec x r) && (pr_eq _ (x - _) != 0))
                           (λ i, pr_eq Trec' (i - a (size z)))).
    rewrite -(big_map sval (λ x, true) (λ i, pr_eq Trec' i)).
    eapply (@sum_reidx_map _ _ _ _ _ _ (λ x, x - a (size z))); auto.
    - intros a0 ?. move/andP => [Hgt HPr]. split; last done.
      move:Hgt. intros Hlt'.
      rewrite -(filter_map sval (λ x, (Rgt_dec x (r - a (size z))) : bool)).
      rewrite mem_filter. apply /andP. split.
      ** rewrite //=. do 2 destruct (Rgt_dec) => //=; nra.
      ** apply /mapP.
           assert (Hpf: a0 - a (size z) \in img Trec').
           { apply pr_img. edestruct (ge_pr_0 (rvar_dist Trec')) as [Hgt|Heq]; first apply Hgt.
             move /eqP in HPr. rewrite /pr_eq in HPr. rewrite //= in Heq. }
           exists (exist _ (a0 - a (size z)) Hpf); last by done.
           rewrite [Finite.enum]unlock //=. apply img_fin_mem.
  - intros b. 
    rewrite -(filter_map sval (λ x, (Rgt_dec x (r - a (size z))) : bool)).
    rewrite mem_filter.  move /andP =>[Hgt Hin'] _ Hfalse.
    case (Req_dec (pr_eq Trec' b) 0); auto.
    intros Hneq'.
    exfalso; apply Hfalse. 
    exists (b + a (size z)).
    repeat split.
    * assert (b + a (size z) \in img (T z)) as Hin.
      { eapply img_Trec_unary; eauto. destruct x'; auto. }
      rewrite -mem_undup. rewrite img_alt'.
      exists (exist _ (b + a (size z)) Hin).
      rewrite //=.
    * apply /andP; split.
      ** do 2 destruct (Rgt_dec) => //=. nra.
      ** rewrite /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r. apply /eqP. done.
    * rewrite /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r. apply /eqP. done.
  - rewrite /index_enum//=. rewrite [Finite.enum]unlock //= img_fin_enum_sval_comp.
    apply undup_uniq.
  - rewrite -(filter_map sval (λ x, (Rgt_dec x (r - a (size z))) : bool)).
    apply filter_uniq. rewrite /index_enum//=. 
    rewrite [Finite.enum]unlock //= img_fin_enum_sval_comp.
    apply undup_uniq.
  - intros ??. intros. nra. 
  }
  apply Rmult_le_compat_l; first by apply Rge_le, ge_pr_0. 
  rewrite /Trec'//=. reflexivity.
Qed.

End rec_convert_unary.

Section rec_convert.
Variable X: eqType.
Variable size: X → R.
Variable A A' B : X → finType.
Variable ΩT: ∀ x, distrib (A x). 
Variable ΩT': ∀ x, distrib (A' x). 
Variable Ωh: ∀ x, distrib (B x). 
Variable T: ∀ x: X, rrvar (ΩT x).
Variable T': ∀ x: X, rrvar (ΩT' x).
Variable h: ∀ x: X, rvar (Ωh x) [eqType of X * X]%type.
Variable P: X → Prop.
Variable hP: ∀ x n, P x → P (fst ((h x) n)) ∧ P (snd ((h x) n)).
Variable G: R * R → R.
Variable a: R → R.

Lemma eq_dist_rec_gt:
  (∀ z, P z → eq_dist (T' z) (T z)) →
  (∀ z r, P z → pr_gt (T z) r <= \big[Rplus/0]_(x' : imgT (h z)) 
                        (pr_eq (h z) (sval x') * pr_gt (rvar_comp (rvar_pair (T (fst (sval x')))
                                                                          (T (snd (sval x'))))
                                       G) (r - a (size z)))) →
  ∀ z r,
  P z →
  pr_gt (T' z) r <= \big[Rplus/0]_(x' : imgT (h z)) 
                        (pr_eq (h z) (sval x') * pr_gt (rvar_comp (rvar_pair (T' (fst (sval x')))
                                                                          (T' (snd (sval x'))))
                                       G) (r - a (size z))).
Proof.
  intros Heq_dist Hrec z r HP. rewrite (proj1 (eq_dist_pr_gt _ _) (Heq_dist _ HP)).
  etransitivity; first apply Hrec; auto.
  right.
  apply eq_bigr => i ?. f_equal. 
  apply (proj1 (eq_dist_pr_gt (rvar_comp (rvar_pair (T (sval i).1) (T (sval i).2)) G)
                              (rvar_comp (rvar_pair (T' (sval i).1) (T' (sval i).2)) G))).
  apply: eq_dist_comp.
  intros (r1&r2).
  rewrite ?pr_eq_rvar_pair ?Heq_dist //.
  - destruct i as (i&Hin). clear -HP Hin hP. rewrite /sval. apply img_alt in Hin.
    destruct Hin as (x&<-). by apply hP.
  - destruct i as (i&Hin). clear -HP Hin hP. rewrite /sval. apply img_alt in Hin.
    destruct Hin as (x&<-). by apply hP.
Qed.

Variable Trec:
  ∀ x r, P x → pr_eq (T x) r = \big[Rplus/0]_(x' : imgT (h x)) 
                        (pr_eq (h x) (sval x') * pr_eq (rvar_comp (rvar_pair (T (fst (sval x')))
                                                                          (T (snd (sval x'))))
                                       G) (r - a (size x))).


Lemma img_Trec_work b z x: 
  P z →
  pr_eq (rvar_comp (rvar_pair (T x.1) (T x.2)) G) b ≠ 0 →
  x \in img (h z) → 
  pr_eq (h z) x ≠ 0 →
  b + a (size z) \in img (T z).
Proof.
  intros HP Hneq0 Hin Hneq0'. apply pr_img.
  specialize (Rmult_neq_0_compat _ _ Hneq0 Hneq0'). intros.
  enough (Hneq: pr_eq (T z) (b + a (size z)) ≠ 0).
  { move:Hneq. rewrite /pr_eq.
    intros. edestruct (ge_pr_0 (rvar_dist (T z))) as [|Heq0]; first eauto.
    rewrite Heq0 in Hneq. congruence. }
  rewrite Trec; last done.
  intros Hfalse.
  symmetry in Hfalse.
  enough (Hfalse': ∀ x', x' \in img (h z) → pr_eq (h z) x' * 
                  (pr_eq (rvar_comp (rvar_pair (T x'.1) (T x'.2)) G)
                     (b + a (size z) - a (size z))) = 0).
  { specialize (Hfalse' x). move:Hfalse'.
    rewrite /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r.
    rewrite Rmult_comm. auto. 
  }
  intros x' Hin'. edestruct (Req_dec) as [Heq|Hneq]; first apply Heq. 
  exfalso. eapply Rlt_not_eq; last apply Hfalse.
  apply Rlt_0_bigr.
  - intros. replace 0 with (0 * 0) by nra. apply Rmult_le_compat; try nra.
    * apply Rge_le, ge_pr_0.
    * apply Rge_le, ge_pr_0.
  - exists (exist _ x' Hin'); repeat split; auto.
    rewrite //=.
    specialize (pr_eq_ge_0 (h z) x').
    specialize (pr_eq_ge_0 (rvar_comp (rvar_pair (T (fst x')) (T (snd x'))) G)
                           (b + a (size z) - a (size z))).
    clear -Hneq. rewrite //=. intros ??.  rewrite //= in Hneq. nra.
Qed.

Lemma eq_dist_rec:
  (∀ z, P z → eq_dist (T' z) (T z)) →
  ∀ z r,
  P z →
  pr_eq (T' z) r = \big[Rplus/0]_(x' : imgT (h z)) 
                        (pr_eq (h z) (sval x') * pr_eq (rvar_comp (rvar_pair (T' (fst (sval x')))
                                                                          (T' (snd (sval x'))))
                                       G) (r - a (size z))).
Proof.
  intros Heq_dist z r HP. rewrite Heq_dist // Trec //.
  apply eq_bigr => i ?. f_equal. 
  apply: eq_dist_comp.
  intros (r1&r2).
  rewrite ?pr_eq_rvar_pair ?Heq_dist //.
  - destruct i as (i&Hin). clear -HP Hin hP. rewrite /sval. apply img_alt in Hin.
    destruct Hin as (x&<-). by apply hP.
  - destruct i as (i&Hin). clear -HP Hin hP. rewrite /sval. apply img_alt in Hin.
    destruct Hin as (x&<-). by apply hP.
Qed.

Lemma rec_pr_rec_gt z r:
  P z →
  pr_gt (T z) r ≤ \big[Rplus/0]_(x' : imgT (h z))
                        (pr_eq (h z) (sval x') * 
                         pr_gt (rvar_comp (rvar_pair (T (fst (sval x'))) (T (snd (sval x'))))
                                                     G) (r - a (size z))).
Proof.
  rewrite /pr_gt pr_gt_alt3. 
  etransitivity.
  { right. eapply eq_bigr => ? _. by apply Trec. }
  rewrite //=.
  rewrite exchange_big //=.
  apply Rle_bigr => x'.
  rewrite -big_distrr //=. 
  set (Trecpair := rvar_comp (rvar_pair (T (sval x').1) (T (sval x').2)) G); 
    rewrite -/Trecpair.
  transitivity (pr_eq (h z) (sval x') *
                \big[Rplus/0]_(i : imgT (A:=A z) (T z) 
                              | (Rgt_dec (sval i) r) && (pr_eq Trecpair ((sval i) - a (size z)) != 0)) 
                 pr_eq Trecpair ((sval i) - a (size z))).
  {  
    right. symmetry.
    eapply Rmult_eq_0_inv_r => Hneq //=. rewrite /index_enum.
    apply (@sum_reidx_map  [finType of imgT (T z)] _ _ _ _ _ (λ x, x)); auto.
    - rewrite /id //=. intros ??. move/andP=>[? ?].
      split; auto. rewrite mem_filter. apply /andP.
      split; auto.
    - intros b Hin' HQ Hfalse. 
      case (Req_dec (pr_eq Trecpair (sval b - a (size z))) 0); auto.
      intros Hneq0. exfalso. eapply Hfalse.
      exists b. rewrite mem_filter in Hin'. move /andP in Hin'. destruct Hin' as [-> ->].
      split; auto. rewrite //=. split; auto.
      move: Hneq0. move /eqP => -> //.
    - rewrite -enumT. apply enum_uniq. 
    - rewrite -enumT. apply filter_uniq => //=. apply: enum_uniq. 
  }
  transitivity (pr_eq (h z) (sval x') * pr_gt Trecpair (r - a (size z))).
  {
    right. 
    eapply Rmult_eq_0_inv_r => Hneq.
    rewrite /pr_gt. rewrite pr_gt_alt3.
    rewrite -(big_map sval (λ x, (Rgt_dec x r) && (pr_eq _ (x - _) != 0))
                           (λ i, pr_eq Trecpair (i - a (size z)))).
    rewrite -(big_map sval (λ x, true) (λ i, pr_eq Trecpair i)).
    eapply (@sum_reidx_map _ _ _ _ _ _ (λ x, x - a (size z))); auto.
    - intros a0 ?. move/andP => [Hgt HPr]. split; last done.
      move:Hgt. intros Hlt'.
      rewrite -(filter_map sval (λ x, (Rgt_dec x (r - a (size z))) : bool)).
      rewrite mem_filter. apply /andP. split.
      ** rewrite //=. do 2 destruct (Rgt_dec) => //=; nra.
      ** apply /mapP.
           assert (Hpf: a0 - a (size z) \in img Trecpair).
           { apply pr_img. edestruct (ge_pr_0 (rvar_dist Trecpair)) as [Hgt|Heq]; first apply Hgt.
             move /eqP in HPr. rewrite /pr_eq in HPr. rewrite //= in Heq. }
           exists (exist _ (a0 - a (size z)) Hpf); last by done.
           rewrite [Finite.enum]unlock //=. apply img_fin_mem.
  - intros b. 
    rewrite -(filter_map sval (λ x, (Rgt_dec x (r - a (size z))) : bool)).
    rewrite mem_filter.  move /andP =>[Hgt Hin'] _ Hfalse.
    case (Req_dec (pr_eq Trecpair b) 0); auto.
    intros Hneq'.
    exfalso; apply Hfalse. 
    exists (b + a (size z)).
    repeat split.
    * assert (b + a (size z) \in img (T z)) as Hin.
      { eapply img_Trec_work; eauto. destruct x'; auto. }
      rewrite -mem_undup. rewrite img_alt'.
      exists (exist _ (b + a (size z)) Hin).
      rewrite //=.
    * apply /andP; split.
      ** do 2 destruct (Rgt_dec) => //=. nra.
      ** rewrite /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r. apply /eqP. done.
    * rewrite /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r. apply /eqP. done.
  - rewrite /index_enum//=. rewrite [Finite.enum]unlock //= img_fin_enum_sval_comp.
    apply undup_uniq.
  - rewrite -(filter_map sval (λ x, (Rgt_dec x (r - a (size z))) : bool)).
    apply filter_uniq. rewrite /index_enum//=. 
    rewrite [Finite.enum]unlock //= img_fin_enum_sval_comp.
    apply undup_uniq.
  - intros ??. intros. nra. 
  }
  apply Rmult_le_compat_l; first by apply Rge_le, ge_pr_0. 
  rewrite /Trecpair//=. reflexivity.
Qed.

End rec_convert.