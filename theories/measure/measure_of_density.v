Require Import Reals Psatz.
From discprob.basic Require Export Series_Ext.
From discprob.measure Require Export borel integral.
Local Open Scope R_scope.
Require Import ClassicalEpsilon SetoidList.


Section measure_of_dens.


Context `{F: measurable_space X}.
Context `(μ: measure X).
Context (f: X → R).
Context (fnonneg: ∀ x, 0 <= f x).
Context (fintegrable: ex_integral μ f).

Definition measure_of_density_fun : (X → Prop) → R :=
  λ U, Integral_over μ U f.

Instance measure_of_density_fun_Proper :
  Proper (eq_prop ==> eq) (measure_of_density_fun).
Proof.
  intros U V Heq. rewrite /measure_of_density_fun/Integral_over.
  eapply Integral_ext => x0. specialize (Heq x0).
  destruct (excluded_middle_informative (U x0)) as [|n];
  destruct (excluded_middle_informative (V x0)) as [|n']; eauto;
    exfalso.
  - eapply n'; eapply Heq; eauto.
  - eapply n; eapply Heq; eauto.
Qed.

Lemma measure_of_density_fun_nonneg :
  ∀ U, measure_of_density_fun U >= 0.
Proof.
  intros U.
  rewrite /measure_of_density_fun/Integral_over.
  apply Integral_ge0. intros x. specialize (fnonneg x).
  destruct (excluded_middle_informative (U x)); nra.
Qed.

Lemma measure_of_density_fun_emptyset:
  measure_of_density_fun empty_set = 0.
Proof.
  rewrite /measure_of_density_fun/Integral_over.
  etransitivity; [ eapply Integral_ext | eapply Integral_0 ].
  intros x.
  destruct (excluded_middle_informative (empty_set x)) as [[]|]; try nra.
Qed.

Lemma indicator_ext P Q:
  (P ↔ Q) →
  match excluded_middle_informative P with
    | left _ => 1
    | _ => 0
  end =
  match excluded_middle_informative Q with
    | left _ => 1
    | _ => 0
  end.
Proof.
  clear. intros HPQ.  do 2 destruct (excluded_middle_informative _); eauto; try exfalso; firstorder.
Qed.


Lemma sum_n_disjoint_indicator {A} Us n (x : A):
  disjointF Us →
  sum_n (λ m : nat,
               match excluded_middle_informative (Us m x) with
               | left _ => 1
               | _ => 0
               end) n =
  match excluded_middle_informative (∃ m, m ≤ n ∧ Us m x) with
    | left _ => 1
    | _ => 0
  end.
Proof.
  intros Hdisj. induction n.
  - rewrite sum_O. eapply indicator_ext.
    split.
    * intros ?. exists O; split; eauto.
    * intros (m&Hle&?). inversion Hle. subst. eauto.
  - rewrite sum_Sn /plus /=.
    rewrite IHn.
    destruct (excluded_middle_informative _) as [(m1&?&?)|n1];
    destruct (excluded_middle_informative _) as [e2|n2]; try nra.
    * exfalso.
      eapply (Hdisj m1 (S n)); last (split; eassumption). lia.
    * destruct (excluded_middle_informative _) as [e3|n3]; first nra.
      exfalso. eapply n3. exists m1; split; eauto.
    * destruct (excluded_middle_informative _) as [e3|n3]; first nra.
      exfalso. eapply n3. exists (S n); split; eauto.
    * destruct (excluded_middle_informative _) as [(m&Hle&?)|n3]; last nra.
      exfalso. inversion Hle; subst; eauto.
Qed.

Lemma sum_n_disjoint_indicator_le_1 {A} Us n (x : A):
  disjointF Us →
  sum_n (λ m : nat,
               match excluded_middle_informative (Us m x) with
               | left _ => 1
               | _ => 0
               end) n <= 1.
Proof.
  intros. rewrite sum_n_disjoint_indicator; auto. destruct (excluded_middle_informative _); nra.
Qed.

Lemma measure_of_density_fun_additivity :
  ∀ U : nat → X → Prop,
    (∀ i : nat, F (U i)) → disjointF U →
    is_series (λ n : nat, measure_of_density_fun (U n)) (measure_of_density_fun (unionF U)).
Proof.
  intros Us Hin Hdisj.
  edestruct (is_integral_levi_series_ae_ex μ
              (λ n x, f x * (match excluded_middle_informative (Us n x) with | left _ => 1 | _ => 0 end))).
  { eapply almost_everywhere_meas_True'. intros x.
    eapply ex_series_single_non_zero.
    intros i j Hneq0i Hneq0j.
    destruct (excluded_middle_informative (Us i x));
    destruct (excluded_middle_informative (Us j x)); try nra.
    destruct (decide (i = j)) as [|Hneq]; first eauto.
    specialize (Hdisj i j Hneq). exfalso. eapply Hdisj; split; eauto.
  }
  { intros n x; specialize (fnonneg x); destruct (excluded_middle_informative _); nra. }
  { intros n. edestruct (ex_integral_ex_integral_over μ (Us n) f) as (?&?&?); eauto.
    eexists; eauto. }
  { destruct fintegrable as (v&His). exists v.
    intros r (n&His'). eapply is_integral_mono; eauto.
    intros x => /=. rewrite sum_n_scal_l /scal/=/mult//=.
    specialize (sum_n_disjoint_indicator_le_1 Us n x Hdisj). specialize (fnonneg x). intros.
    rewrite -[a in _ <= a](Rmult_1_r).
    apply Rmult_le_compat_l; try nra. eauto.
  }
  assert (measure_of_density_fun (unionF Us) =
          (Integral μ (λ x : X, Series (λ n : nat, f x * (match excluded_middle_informative (Us n x) with
                                                            | left _ => 1
                                                            | _ => 0
                                                          end))))) as ->.
  {
    rewrite /measure_of_density_fun/Integral_over. eapply Integral_ext.
    intros x. rewrite Series_scal_l; f_equal.
    destruct (excluded_middle_informative (unionF Us x)) as [Hin_union|Hnin_union].
    * symmetry. destruct Hin_union as (n&?). rewrite (Series_single_non_zero _ n) //=.
      { destruct (excluded_middle_informative _); eauto; try exfalso; eauto. }
      intros j. destruct (excluded_middle_informative _) => ?; last nra.
      destruct (decide (n = j)) as [?|Hneq]; eauto.
      exfalso. eapply (Hdisj n j); eauto.
    * symmetry. rewrite Series_0 //.
      intros m. destruct (excluded_middle_informative _); try nra.
      exfalso. eapply Hnin_union; eauto. exists m. eauto.
  }
  eapply is_series_ext; try eassumption; eauto.
Qed.

Definition measure_of_density : measure X.
Proof.
  refine {| measure_fun := measure_of_density_fun |}.
  - apply measure_of_density_fun_nonneg.
  - apply measure_of_density_fun_emptyset.
  - apply measure_of_density_fun_additivity.
Defined.

End measure_of_dens.
