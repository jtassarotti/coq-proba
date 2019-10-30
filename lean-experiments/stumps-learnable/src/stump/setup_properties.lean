/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import .setup_definition
import ..lib.util

open set 
open measure_theory
open probability_measure

local attribute [instance] classical.prop_decidable

namespace stump

variables (μ: probability_measure ℍ) (target: ℍ) 

lemma label_correct:
    ∀ x, (label target x).snd = tt ↔ x ≤ target :=
begin
    intros,
    split; intro,
    {
        unfold label at a,
        simp at a,
        unfold rle at a,
        tidy,
    },
    {
        unfold label,
        simp,
        unfold rle,
        tidy,
    }
end

lemma error_interval_1:
    ∀ h, h ≤ target → error μ target h = μ (Ioc h target) :=
begin
    intros,
    unfold error,
    have SETEQ: error_set h target = Ioc h target,
    {
        unfold error_set,
        unfold Ioc,
        unfold label,
        unfold rle,
        rw ext_iff,
        intro, 
        simp at *,
        split; intro, 
        {
            rw not_eq_prop at a_1,
            cases a_1; simp at a_1; cases a_1,
            {
                finish,
            },
            {
                split,
                {
                    exact lt_of_le_of_lt a a_1_right
                },
                {
                    transitivity h; assumption,
                },
            },
        },
        {
            cases a_1,
            finish,
        },
    },
    exact congr_arg μ SETEQ,
end

lemma error_interval_2:
    ∀ h, h > target → error μ target h = μ (Ioc target h) :=
begin
    intros,
    unfold error,
    have SETEQ: error_set h target = Ioc target h,    
    {
        unfold error_set,
        unfold Ioc,
        unfold label,
        unfold rle,
        rw ext_iff,
        intro, 
        simp at *,
        split; intro, 
        {
            rw not_eq_prop at a_1,
            cases a_1; simp at a_1; cases a_1,
            {
                split,
                {
                    by_contradiction,
                    have FOO: target < x,
                    {
                        transitivity h; try {assumption},
                    },
                    contradiction,
                },
                {
                    transitivity target; try {assumption},
                    have FOO: target < h,
                    {
                        exact mem_Ioi.mp a,
                    },
                    exact le_of_lt a,
                },
            },
            {
                split,
                {
                    exact mem_Ioi.mp a_1_right,
                },
                {
                    assumption,
                },
            },
        },
        {
            cases a_1,
            finish,
        },
    },
    exact congr_arg μ SETEQ,
end

lemma error_mono:
    ∀ c₁, ∀ c₂, 
    c₁ ≤ c₂ → 
    c₂ ≤ target → 
    error μ target c₂ ≤ error μ target c₁ :=
begin
    intros,
    rw error_interval_1,
    rw error_interval_1,
    apply probability_measure.prob_mono,
    exact Ioc_subset_Ioc_left a,
    transitivity c₂; assumption, 
    assumption,
end

lemma error_mono_interval:
    ∀ c₁, ∀ c₂, 
    c₁ ≤ c₂ → 
    c₂ ≤ target → 
    μ (Ioc c₂ target) ≤ μ (Ioc c₁ target) :=
begin
    intros,
    rw ← error_interval_1; try {assumption},
    rw ← error_interval_1,
    apply error_mono; try {assumption},
    transitivity c₂; try {assumption},
end

lemma error_max:
    error μ target 0 = μ (Ioc 0 target) :=
begin
    apply error_interval_1,
    tidy,
end

end stump