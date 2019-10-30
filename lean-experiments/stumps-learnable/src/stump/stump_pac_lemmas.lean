/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import .setup_properties
import .algorithm_properties

local attribute [instance] classical.prop_decidable

open set
open measure_theory
open well_founded

namespace stump

variables (μ: probability_measure ℍ) (target: ℍ) (n: ℕ)

lemma partition:
    ∀ θ, 
    θ > 0 → 
    {x : ℍ | ∀ (a: ℍ) (b: bool), (a,b) = label target x → ite b a 0 < θ}
    = - Icc θ target :=
begin
    introv h1,
    apply ext,
    intros,
    unfold Icc, unfold label, unfold rle,
    simp,
    split; intros,
    {
        simp at *, intros,
        by_contradiction, simp at a_2,
        have FOO:= a x tt _ _,
        {
            simp at FOO,
            have BAR: ¬ (θ ≤ x), simp, assumption,
            contradiction,
        },
        trivial,
        tidy,
    },
    {
        by_cases (b = tt),
        {
            rw h at *, simp, rw a_2, 
            by_contradiction, simp at a_4,
            have INEQ1 := a a_4,
            have INEQ2: ¬ (x > target), {simp,tidy,},
            contradiction,
        },
        {
            simp at h, rw h at *, simp at *,
            tidy,
        },
    },
end

lemma miss_prob:
    ∀ ε, ∀ θ: nnreal, θ > 0 → 
    μ (Icc θ target) ≥ ε →
    μ {x : ℍ | ∀ (a: ℍ) (b: bool), (a,b) = label target x → ite b a 0 < θ} ≤ 1 - ε:=
begin
    intros,
    rw partition,
    have STO := probability_measure.prob_comp μ (Icc θ target) _,
    have SWAP: μ (- Icc θ target) = 1 - μ (Icc θ target), 
    {
        exact lc_nnreal (μ (-Icc θ target)) (μ (Icc θ target)) STO,
    },
    rw SWAP,
    {
        apply nnreal_sub_trans,
        assumption,
    },
    {
        apply is_measurable_of_is_closed,
        apply is_closed_Icc,
    },
    assumption,
end

lemma all_missed: 
    ∀ ε: nnreal, 
    ∀ θ: nnreal, 
    μ (Ioc θ target) ≤ ε → 
    {S: vec ℍ n | error μ target (choose n (label_sample target n S)) > ε} ⊆ 
    {S: vec ℍ n |  ∀ (i: dfin (nat.succ n)), ∀ p = label target (kth_projn S i), (if p.snd then p.fst else 0) < θ} :=
begin
    intros,
    conv {
        congr, congr, funext, rw (error_interval_1 μ target (choose n (label_sample target n S)) (choose_property_1 target n S)), skip, skip, 
    },
    rw set_of_subset_set_of,
    intros,
    have QENI: not (μ (Ioc (choose n (label_sample target n a_1)) target) ≤ μ (Ioc θ target)),
    {
        simp,
        have BREAK_LEQ: μ (Ioc θ target) < ε ∨ μ (Ioc θ target) = ε,
        {
            exact lt_or_eq_of_le a,
        },
        cases BREAK_LEQ,
        transitivity ε; try {assumption,}, 
        rw BREAK_LEQ, assumption,
    },
    by_cases (p.snd = tt),
    {
        have PROP := choose_property_2 target n a_1 i p _ h, 
        {
            rw h, simp,
            have INEQ1 := error_mono_interval μ target _ _ PROP _,
            by_contradiction, simp at a_3,
            have INEQ2 := error_mono_interval μ target _ _ a_3 _,
            have INEQ: μ (Ioc (choose n (label_sample target n a_1)) target) ≤ μ (Ioc θ target),
            {
                transitivity (μ (Ioc p.fst target)); try {assumption},
            }, clear INEQ1 INEQ2,
            contradiction,
            apply choose_property_3; try {assumption},
            {
                dunfold label_sample,
                rw ← kth_projn_map_comm,
                assumption,
            },
            apply choose_property_1,
        },
        {
            dunfold label_sample,
            rw ← kth_projn_map_comm,
            assumption,
        },
    },
    {
        simp at h, rw h, simp,
        have INEQ1': 0 ≤ choose n (label_sample target n a_1), 
        {
            apply choose_property_4,
        },
        have INEQ1 := error_mono_interval μ target _ _ INEQ1' _, clear INEQ1',
        by_contradiction, simp at a_3,
        have GEN: θ ≤ 0,
        {
            exact le_of_eq a_3,
        },
        have INEQ2 := error_mono_interval μ target _ _ GEN _, clear GEN,
        have INEQ: μ (Ioc (choose n (label_sample target n a_1)) target) ≤ μ (Ioc θ target),
            {
                transitivity (μ (Ioc 0 target)); try {assumption},
            }, clear INEQ1 INEQ2,
        contradiction,
        tidy,
        apply choose_property_1,
    },
end

lemma always_succeed:
    ∀ ε: nnreal, ε > 0 → ∀ n: ℕ, 
    μ (Ioc 0 target) ≤ ε →  
    ∀ S: vec ℍ n, error μ target (choose n (label_sample target n S)) ≤ ε :=
begin
    intros, 
    transitivity (μ (Ioc 0 target)); try {assumption}, 
    have HypIN := choose_property_1 target n S, 
    have ERMONO := error_mono μ _ 0 (choose n (label_sample target n S)) _ HypIN, 
    rw ← error_max,
    assumption,
    tidy,
end

end stump