From discprob.basic Require Import base Series_Ext seq_ext nify.
From discprob.prob Require Import countable rearrange prob finite stochastic_order.
Require Import Reals Fourier Omega Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype bigop seq.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.

(* Some facts about uniform distributions on finite sample spaces *)

Section unif.
Variable A: finType.
Variable B: eqType.
Variable Ω: distrib A.

Definition uniform_on (X: rvar Ω B) (P: pred B) :=
  ∀ x y, P x → P y → pr_eq X x = pr_eq X y.

Definition uniform X := uniform_on X (λ x, x \in img X). 

End unif.

Arguments uniform_on {_ _ _} _ _.
Arguments uniform {_ _ _} _.

Lemma indicator_pred_img {A: finType} {B: eqType} {Ω: distrib A} (X: rvar Ω B) (P: pred B):
  (∀ x, x \in img X → P x) →
  pr_eq (indicator X P) 1 = 1.
Proof.  
  intros HP.
  apply Finite_inj. rewrite -Ex_indicator. rewrite Ex_fin_pt => //=.
  rewrite -{2}(pmf_sum1_Series Ω) SeriesC_fin_big //= => //=.
  f_equal. apply eq_bigr => i ?.
  case: ifP; rewrite /rvar_dist; first nra.
  move /negP. intros Hfalse. exfalso; apply Hfalse.
  apply HP. apply img_alt. eexists; eauto.
Qed.

Lemma uniform_pred_img {A: finType} {B: eqType} {Ω: distrib A} (X: rvar Ω B) (P: pred B):
  (∀ x, x \in img X → P x) →
  uniform_on X P →
  ∀ x, x \in img X → P x → pr_eq X x = 1 / (\big[Rplus/0]_(a : imgT X | P (sval a)) 1).
Proof.  
  intros HP Hunif x Hin Hx.
  eapply indicator_pred_img in HP.
  apply (f_equal Finite) in HP.  rewrite -Ex_indicator in HP.
  rewrite /indicator in HP. rewrite Ex_fin_comp in HP.
  assert (\big[Rplus/0]_(a : imgT X | P (sval a)) ((pr_eq X x) * 1) = 1) as Hsum.
  { apply Finite_inj in HP. rewrite -{2}HP. 
    symmetry. etransitivity.
    { eapply eq_bigr => i _. rewrite Rmult_comm Rmult_if_distrib Rmult_0_l Rmult_1_l. done. }
    rewrite -big_mkcondr => //=.
    { eapply eq_bigr => i Hi. rewrite Rmult_1_r. apply Hunif; auto. }
  }
  rewrite -big_distrr //= in Hsum.
  intros. rewrite -{1}Hsum //=. field. 
  apply Rgt_not_eq, Rlt_gt, Rlt_0_bigr.
  - intros (i&?) _. rewrite //=. fourier.
  - exists (exist _ x Hin); repeat split => //=; try nra.
    rewrite /index_enum {1}[@Finite.enum]unlock //=. apply img_fin_mem.
Qed.

(* Two distributions which are uniform_on the union of their img are equal *)
Lemma uniform_on_eq {A A': finType} {B: eqType} {Ω: distrib A} {Ω': distrib A'}
      (X: rvar Ω B) (Y: rvar Ω' B) (P: pred B):
  (∀ x, x \in img X ↔ P x) →
  (∀ x, x \in img Y ↔ P x) →
  uniform_on X P →
  uniform_on Y P →
  eq_dist X Y.
Proof.
  intros HXP HYP HunifX HunifY => x.
  case_eq (P x).
  - intros HP.
    rewrite ?(uniform_pred_img _ P) => //=.
    *  f_equal. rewrite /index_enum. 
       rewrite -(big_map sval P (λ x, 1)).
       rewrite -(big_map sval P (λ x, 1)).
       rewrite /index_enum {1}[@Finite.enum]unlock //=. 
       rewrite /index_enum {1}[@Finite.enum]unlock //=. 
       rewrite ?img_fin_enum_sval.
       apply (sum_reidx_map _ _ _ _ id); auto.
       ** intros b. rewrite mem_undup. move /mapP => [a Hin] Heq HP'; split; auto.
          rewrite img_alt'. apply img_alt. rewrite HYP. done.
       ** intros b. rewrite ?mem_undup. move /mapP => [a' Hin] Heq HP' Hfalse. 
          exfalso; apply Hfalse.
          exists b. repeat split; auto.
          rewrite img_alt'. apply img_alt. rewrite HXP. done.
       ** apply undup_uniq.
       ** apply undup_uniq.
    * apply HYP.
    * rewrite HYP. done.
    * apply HXP.
    * rewrite HXP. done.
  - intros Hfalse. transitivity 0.
    * apply pr_img_nin. rewrite HXP Hfalse //. 
    * symmetry; apply pr_img_nin. rewrite HYP Hfalse //. 
Qed.