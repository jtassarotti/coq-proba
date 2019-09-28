Require Import Reals Fourier Omega Psatz.
From discprob.basic Require Import base.
From discprob.prob Require Import prob countable finite stochastic_order.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.

Lemma bool_pickle_inv: ∀ x, (x >= 2)%nat → pickle_inv ([countType of bool]) x = None.
Proof.
  intros x Hgt.
  destruct x; first omega.
  destruct x; first omega.
  rewrite /pickle_inv//=.
  case: ifP => //.
  destruct (ssrnat.odd x) => //=.
Qed.

Definition bern_dist (p: R) (Hrange: 0 <= p <= 1) : distrib [countType of bool]. 
Proof.
  refine (mkDistrib _ (λ b, if (b : bool) then p else (1 - p)) _ _).
  - intros [|]; nra. 
  - apply Series_correct'.
    rewrite SeriesC_fin_big //= /index_enum.
    rewrite {1}[@Finite.enum]unlock //= ?big_cons ?big_nil //=; field.
    (*
    apply SeriesF_is_seriesC. SearchAbout is_series. "big". series big. apply filterlim_ext with
        (λ n, sum_n (countable_sum (λ _ : [countType of bool], 1 / 2)) (min 1 n)). 
    * destruct x => //=.
      induction x => //=.
      rewrite [a in _ = a]sum_Sn => //=.
      rewrite IHx => //=.
      rewrite -[a in a = _ ]Rplus_0_r.
      rewrite /plus/=.
      f_equal.
      rewrite /countable_sum bool_pickle_inv => //=; omega.
     *)
    * eexists; eapply SeriesF_is_seriesC. 
Defined.

Lemma pr_bern_dist_true p H: pr (bern_dist p H) (λ x, x == true) = p.
Proof.
  rewrite /pr SeriesC_fin_big //= /index_enum.
  rewrite {1}[@Finite.enum]unlock //= ?big_cons ?big_nil //=; field.
Qed.

Lemma pr_bern_dist_false p H: pr (bern_dist p H) (λ x, x == false) = (1 - p).
Proof.
  rewrite /pr SeriesC_fin_big //= /index_enum.
  rewrite {1}[@Finite.enum]unlock //= ?big_cons ?big_nil //=; field.
Qed.

Definition bernoulli p H : rrvar (bern_dist p H) :=
  mkRvar _ (λ (b: bool), if b then 1 else 0).

Lemma pr_eq_bernoulli_1 p H: pr_eq (bernoulli p H) 1 = p.  
Proof.
  rewrite /pr_eq /pr SeriesC_fin_big //= /index_enum.
  rewrite {1}[@Finite.enum]unlock //= ?big_cons ?big_nil eq_refl //=.
  case: ifP; move /eqP => ?; try nra.
Qed.

Lemma pr_eq_bernoulli_0 p H: pr_eq (bernoulli p H) 0 = (1 - p).
Proof.
  rewrite /pr_eq /pr SeriesC_fin_big //= /index_enum.
  rewrite {1}[@Finite.enum]unlock //= ?big_cons ?big_nil eq_refl //=.
  case: ifP; move /eqP => ?; try nra.
Qed.

Lemma pr_eq_bernoulli_alt p H r: r ≠ 0 → r ≠ 1 → pr_eq (bernoulli p H) r = 0.
Proof.
  rewrite /pr_eq /pr SeriesC_fin_big //= /index_enum.
  rewrite {1}[@Finite.enum]unlock //= ?big_cons ?big_nil //=. 
  intros Hneq0 Hneq1.
  case: ifP; move /eqP => Hneq; try nra.
  case: ifP; move /eqP => Hneq'; try nra.
Qed.

Lemma Ex_bernoulli p H:
  Ex (bernoulli p H) = p.
Proof.
  rewrite Ex_fin_pt //= /index_enum {1}[@Finite.enum]unlock //= ?big_cons ?big_nil //=. 
  field.
Qed.

Lemma Var_bernoulli p H:
  Var (bernoulli p H) = p * (1 - p).
Proof.
  rewrite /Var Ex_fin_pt //= /index_enum {1}[@Finite.enum]unlock //= ?big_cons ?big_nil //=
          Ex_bernoulli.
  field.
Qed.

Lemma EGF_bernoulli p H t:
  Ex (rvar_comp (bernoulli p H) (λ x, exp (t * x))) =
  p * exp t + (1 - p).
Proof.
  rewrite Ex_fin_pt //= /index_enum {1}[@Finite.enum]unlock //= ?big_cons ?big_nil //=.
  rewrite Rmult_0_r Rplus_0_r Rmult_1_r exp_0; field.
Qed.

Lemma eq_dist_bernoulli {A: countType} {Ω: distrib A} (X: rrvar Ω) p Hrange:
  pr_eq X 1 = p →
  pr_eq X 0 = (1 - p) →
  eq_dist X (bernoulli p Hrange).
Proof.
  intros Heq1 Heq0.
  intros r.
  destruct (Req_dec r 0).
  - subst. by rewrite pr_eq_bernoulli_0 Heq0.
  - destruct (Req_dec r 1).
    * subst. by rewrite pr_eq_bernoulli_1.
    * rewrite pr_eq_bernoulli_alt //.
      destruct (pr_eq_ge_0 X r) as [Hge|Hnge] => //=.
      apply Rgt_not_le in Hge. exfalso; apply Hge.
      etransitivity; first apply (pr_eq_le_sum_list X (1 :: 0 :: nil)). 
      **  intros Hin%seq_ext.mem_seq_legacy.
          inversion Hin as [|[]]; subst; auto.
      ** assert (seq.undup (1 :: 0 :: nil) = (1 :: 0 :: nil)) as Heq.
         { rewrite //=. rewrite /in_mem //= orbF //=. case: ifP => //=.
             move /eqP; nra. }
         rewrite Heq ?big_cons ?big_nil. nra.
Qed.

Definition is_bernoulli {A: countType} {Ω: distrib A} (X : rrvar Ω) p : Prop :=
  pr_eq X 1 = p ∧ pr_eq X 0 = (1 - p).

Lemma is_bernoulli_range {A: countType} {Ω: distrib A} (X: rrvar Ω) p :
  is_bernoulli X p → 0 <= p <= 1.
Proof.
  intros [Heq1 Heq2].
  specialize (pr_eq_ge_0 X 0).
  specialize (pr_eq_ge_0 X 1).
  specialize (pr_eq_le_1 X 0).
  specialize (pr_eq_le_1 X 1).
  intros. split; nra.
Qed.

Section is_bernoulli_facts.

  Variable (A: countType).
  Variable (Ω: distrib A).
  Variable (X: rrvar Ω).
  Variable (p: R).
  Variable (Hbern: is_bernoulli X p).
  
  Lemma is_bernoulli_eq_dist':
    eq_dist X (bernoulli p (is_bernoulli_range _ _ Hbern)).
  Proof. destruct Hbern; by apply (eq_dist_bernoulli X p (is_bernoulli_range _ _ Hbern)). Qed.

  Lemma is_bernoulli_ex_Ex f:
    ex_Ex (rvar_comp X f).
  Proof.
    eapply ex_Ex_eq_dist.
    - apply eq_dist_sym, is_bernoulli_eq_dist'.
    - apply: ex_Ex_fin. 
  Qed.

  Lemma Ex_is_bernoulli:
    Ex X = p.
  Proof.
    rewrite -(Ex_bernoulli p) //.
    * eapply is_bernoulli_range; eauto.
    * symmetry. unshelve (apply: Ex_eq_dist_fin).
    apply eq_dist_sym, is_bernoulli_eq_dist'.
  Qed.

  Lemma Var_is_bernoulli:
    Var X = p * (1 - p).
  Proof.
    rewrite -(Var_bernoulli p).
    * eapply is_bernoulli_range; eauto.
    * symmetry.
    rewrite /Var. rewrite Ex_is_bernoulli Ex_bernoulli. apply Ex_eq_dist.
    - apply eq_dist_sym, is_bernoulli_eq_dist'.
    - apply: ex_Ex_fin.
  Qed.

  Lemma EGF_is_bernoulli t:
    Ex (rvar_comp X (λ x, exp (t * x))) = p * exp t + (1 - p).
  Proof.
    rewrite -(EGF_bernoulli p).
    * eapply is_bernoulli_range; eauto.
    * symmetry.
    apply Ex_eq_dist.
    - apply eq_dist_sym, is_bernoulli_eq_dist'.
    - apply: ex_Ex_fin.
  Qed.

  Lemma is_bernoulli_eq_dist Hpf:
    eq_dist X (bernoulli p Hpf).
  Proof. destruct Hbern; by apply (eq_dist_bernoulli X p Hpf). Qed.
    
End is_bernoulli_facts.

Arguments is_bernoulli_eq_dist {_ _}.
Arguments Ex_is_bernoulli {_ _}.
Arguments Var_is_bernoulli {_ _}.
Arguments EGF_is_bernoulli {_ _}.
