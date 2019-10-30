/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import .algorithm_definition
import .setup_measurable

open set

namespace stump

variables (μ: probability_measure ℍ) (target: ℍ) (n: ℕ)

@[simp]
lemma label_sample_measurable: ∀ n: ℕ, measurable (label_sample target n) :=
begin
    intro,
    apply measurable_map,
    apply label_measurable,
end

@[simp]
lemma max_continuous: ∀ n, continuous (max n) :=
begin
    intros,
    induction n,
    {
        unfold max,
        apply continuous_id, 
    },
    {
        unfold max,
        simp,
        apply continuous_if; intros,
        {
            unfold rlt at H, simp at H,
            have FOO := @frontier_lt_subset_eq nnreal (vec nnreal (nat.succ n_n)) _ _ _ _ (λ x, max n_n x.snd) (λ x, x.fst) _ (continuous_fst),
            {
                simp at FOO,
                have BAR := mem_of_mem_of_subset H FOO, clear FOO,
                rw mem_set_of_eq at BAR,
                exact eq.symm BAR,
            },
            {
                apply continuous.comp,
                assumption,
                apply continuous_snd,
            },
        },
        {
            apply continuous.comp,
            apply continuous_fst,
            apply continuous_id,
        },
        {
            apply continuous.comp,
            assumption,
            apply continuous.comp,
            apply continuous_snd,
            apply continuous_id,
        },
    },
end

@[simp]
lemma max_is_measurable: is_measurable {v: vec ℍ (nat.succ n) | rlt (max n v.snd) (v.fst)} :=
begin
    dunfold vec,
    unfold rlt,
    simp,
    apply test''',
    {
        apply continuous.comp,
        apply max_continuous,
        apply continuous_snd,
    },
    {
        apply continuous_fst,
    },
end

@[simp]
lemma max_measurable: ∀ n, measurable (max n) :=
begin
    intro n,
    induction n,
    {
        unfold max,
        apply measurable_id,
    },
    {
        unfold max,
        apply measurable.if,
        unfold_coes, apply max_is_measurable,
        apply measurable_fst,
        apply measurable_id,
        apply measurable.comp,
        apply n_ih,
        apply measurable_snd,
        apply measurable_id,
    }
end

@[simp]
lemma choose_measurable: measurable (choose n) :=
begin
    unfold choose,
    apply measurable.comp,
    apply max_measurable,
    unfold filter,
    apply measurable_map,
    apply measurable.if,
    unfold_coes, 
    {
        have PROD: {a: ℍ × bool | a.snd = tt} = set.prod {x: ℍ | true} {b: bool | b = tt},
        {
            rw ext_iff, intros,
            rw mem_prod_eq,
            repeat {rw mem_set_of_eq},
            finish,
        },
        rw PROD,
        apply is_measurable_set_prod,
        {
            rw ← univ_def,
            exact is_measurable.univ,
        },
        fsplit,
    },
    apply measurable_fst,
    apply measurable_id,
    apply measurable_const,

end

@[simp]
lemma is_measurable_vec_1:
    ∀ ε, is_measurable {v: vec (ℍ × bool) n | error μ target (choose n v) > ε} :=
begin
    intros,
    have PREIM: {v: vec (ℍ × bool) n | error μ target (choose n v)  > ε} = (choose n) ⁻¹' {h: ℍ | error μ target h > ε},
    simp, 
    rw PREIM,
    apply measurable.preimage; try {simp},
end

@[simp]
lemma is_measurable_vec_2:
    ∀ ε, is_measurable {v: vec (ℍ × bool) n | error μ target (choose n v) ≤ ε} :=
begin
    intros,
    have PREIM: {v: vec (ℍ × bool) n | error μ target (choose n v) ≤ ε} = (choose n) ⁻¹' {h: ℍ | error μ target h ≤ ε},
    simp, 
    rw PREIM,
    apply measurable.preimage; try {simp},    
end

end stump