/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import .setup_definition .setup_properties

open set
open measure_theory
open probability_measure
open lattice

local attribute [instance] classical.prop_decidable

namespace stump

variables (μ: probability_measure ℍ) (target: ℍ) 

lemma is_meas_to_target:
    is_measurable {a: nnreal | a ≤ target} :=
begin
    apply is_measurable_of_is_closed,
    have TEST: Icc 0 target = {a: nnreal | a ≤ target}, {
        unfold Icc,
        rw ext_iff,
        intro, 
        simp at *,
    },
    rw ← TEST, 
    apply is_closed_Icc,
end

@[simp] 
lemma label_measurable: measurable (label target) := 
begin
    dunfold label,
    apply measurable.prod,
    apply measurable_id,
    unfold rle,
    unfold to_bool,
    apply measurable.if,
    apply is_meas_to_target,
    apply measurable_const,
    apply measurable_const,
end

lemma measurable_interval_function:
    ∀ f: nnreal → nnreal,
    (∀ x: nnreal, is_measurable (f ⁻¹' Iio x)) → 
    measurable f :=
begin
    intros,
    have FOO:= borel_eq_generate_Iio nnreal,
    unfold measurable, 
    unfold stump.meas_ℍ,
    rw FOO,  
    apply measurable_generate_from,
    intros,
    unfold range at H,
    rw mem_set_of_eq at H,
    cases H,
    unfold is_measurable,
    unfold is_measurable at a,
    unfold stump.meas_ℍ at a,
    rw FOO at a,
    rw ← H_h,
    apply a,
end

lemma measurable_lt :let f := λ x: nnreal, μ (Icc 0 x) in
∀ y : nnreal, 
(∃ θ : nnreal, {x : nnreal | f x < y} = Ico 0 θ)
∨ 
{x : nnreal | f x < y} = ∅ 
∨ 
(∃ θ : nnreal, {x : nnreal | f x < y} = Icc 0 θ)
∨ 
{x : nnreal | f x < y} = Ici 0
:=
begin
    intros f y, 
    let S := {x : ℍ | f x < y},
    have hm : monotone f, from assume a b hab, prob_mono _ (Icc_subset_Icc (by refl) hab),
    have hm' : ∀ {x y}, f x < f y → x < y, 
    { 
        by_contradiction, push_neg at a, 
        choose x₀ y₀ hxy using a,
        rcases hxy with ⟨hxy₁,hxy₂⟩,
        have : f y₀ ≤ f x₀, from hm hxy₂, 
        rw ←not_lt at this, exact this hxy₁,   
    },  
    by_cases (∃ u, f(u) ≥ y),
    swap, push_neg at h,
    have hS : S = Ici 0,
    {
        ext z, dsimp [S, Ici],
        fsplit, assume h₁, by_contra, simp at *, assumption,
        assume h₁, apply h,
    },
    right, right, right, assumption,
    let T := {x : ℍ | f x ≥ y},
    have Tne : T ≠ ∅, 
    {
        assume not, choose u hyp using h,
        have : u ∈ T, by assumption, finish, 
    },
    have Tbdbl : bdd_below T, from ⟨ 0 , assume y hy, zero_le _ ⟩, 
    let θ := Inf T, 
    have Sleθ : ∀ x ∈ S, x ≤ θ, 
    {
        assume s hs, refine le_cInf Tne _,
        assume b hb, dsimp [T,S] at hb hs,
        suffices : f s < f b, exact le_of_lt (hm' this),
        exact lt_of_lt_of_le hs hb, 
    },
    by_cases case : (f θ < y),
    have hS : S = Icc 0 θ, from set.ext (assume x, iff.intro (assume h₁, ⟨ by simp , Sleθ _ h₁⟩) (assume h₂, lt_of_le_of_lt (hm h₂.2) case)), 
    right, right, left, existsi θ, exact hS, 
    have hS : S = Ico 0 θ,
    {
        ext x, fsplit, 
        assume h₁, 
        suffices : x ≠ θ, dsimp [Ico], refine ⟨ by simp , lt_of_le_of_ne (Sleθ _ h₁) this ⟩, 
        assume not, 
        have : θ ∉ S, from case, rw not at h₁, exact this h₁,
        assume h₁, dsimp [S,Ico] at h₁ ⊢, 
        have : x ∉ T, assume not, have : θ ≤ x, from cInf_le Tbdbl not,
        replace h₁ := h₁.2, rw ←not_le at h₁, exact h₁ this,   
        simp at this, assumption,
    },
    left, existsi θ, exact hS,      
end

lemma measurable_Icc_0_x:
    measurable (λ x: nnreal, μ (Icc 0 x)) :=
begin
    apply measurable_interval_function,
    intros,
    unfold set.preimage,
    unfold Iio,
    conv {
        congr, congr, funext, rw mem_set_of_eq, skip,
    },
    have FOO := measurable_lt μ x,
    cases FOO,
    cases FOO,
    rw FOO_h,
    exact is_measurable_Ico,
    cases FOO,
    rw FOO,
    exact is_measurable.empty,
    cases FOO,
    cases FOO,
    rw FOO_h,
    apply is_measurable_of_is_closed,
    apply is_closed_Icc,
    rw FOO,
    have COMPL: (Ici (0: nnreal) = - Iio 0),
    {
        unfold Ici, unfold Iio, 
        rw ext_iff, intro,
        rw mem_set_of_eq,
        rw compl_set_of,
        rw mem_set_of_eq,
        split; intro,
        simp, 
        simp at a,
        tidy,
    },
    rw COMPL,
    apply is_measurable.compl,
    exact is_measurable_Iio,
end

noncomputable
def error1: nnreal → nnreal := λ h, μ (Icc 0 target) - μ (Icc 0 h)

noncomputable 
def error2: nnreal → nnreal := λ h, μ (Icc 0 h) - μ (Icc 0 target)

noncomputable 
def error_decomposed: nnreal → nnreal := λ h, ite (rle h target) (error1 μ target h) (error2 μ target h) 

lemma decompose_error:
    error μ target = error_decomposed μ target :=
begin
    funext,
    unfold error_decomposed,
    by_cases (rle h target = tt),
    {
        dedup,
        rw h_1, simp,
        unfold error1,
        rw error_interval_1,
        rw ← Icc_diff_Ioc 0 h target,
        have INCL: Icc 0 h ⊆ Icc 0 target, swap,
        {
            have FOO:= @measure_diff nnreal _ μ _ _ INCL _ _ _,
            unfold_coes,
            unfold_coes at FOO,
            rw FOO,
            rw ← ennreal.coe_eq_coe,
            rw to_nnreal_sub,
            exact to_measure_lt_top μ (Icc 0 target),
            exact to_measure_lt_top μ (Icc 0 h),
            apply is_measurable_of_is_closed,
            apply is_closed_Icc,
            apply is_measurable_of_is_closed,
            apply is_closed_Icc,
            exact probability_measure.to_measure_lt_top μ (Icc 0 h),
        },
        {
            have H: h ≤ target, 
            {
                unfold rle at h_1,
                tidy,
            },
            unfold Icc,
            rw subset_def, intros,
            rw mem_set_of_eq,
            rw mem_set_of_eq at a,
            cases a,
            split,
            assumption,
            transitivity h; assumption,
        },
        {
            tidy,
        },
        repeat {
            unfold rle at h_1,
            tidy,
        },
    },
    {
        dedup,
        simp at h_1, rw h_1, simp,
        unfold error2,
        rw error_interval_2,
        rw ← Icc_diff_Ioc 0 target h,
        have INCL: Icc 0 target ⊆ Icc 0 h, swap,
        {
            have FOO:= @measure_diff nnreal _ μ _ _ INCL _ _ _,
            unfold_coes,
            unfold_coes at FOO,
            rw FOO,
            rw ← ennreal.coe_eq_coe,
            rw to_nnreal_sub,
            exact to_measure_lt_top μ (Icc 0 h),
            exact to_measure_lt_top μ (Icc 0 target),
            apply is_measurable_of_is_closed,
            apply is_closed_Icc,
            apply is_measurable_of_is_closed,
            apply is_closed_Icc,
            exact probability_measure.to_measure_lt_top μ (Icc 0 target)
        },
        {
            have H: target < h, 
            {
                unfold rle at h_1,
                tidy,
            },
            unfold Icc,
            rw subset_def, intros,
            rw mem_set_of_eq,
            rw mem_set_of_eq at a,
            cases a,
            split,
            assumption,
            transitivity target; try {assumption},
            exact le_of_lt H,
        },
        {
            tidy,
        },
        {
            unfold rle at h_1, simp at h_1,
            exact le_of_lt h_1,
        },
        {
            unfold rle at h_1, simp at h_1,
            exact (gt_from_lt h target).mp h_1,
        },
    }, 
end

lemma error_measurable:
    measurable (error μ target) :=
begin
    rw decompose_error,
    unfold error_decomposed,
    apply measurable.if,
    {
        unfold rle, simp, apply is_meas_to_target,
    },
    {
        unfold error1,
        apply nnreal.measurable_sub,
        {
            apply measurable_const,
        },
        {
            apply measurable_Icc_0_x,
        },
    },
    {
        unfold error2,
        apply nnreal.measurable_sub,
        {
            apply measurable_Icc_0_x,   
        },
        {
            apply measurable_const,
        },
    },
end

@[simp]
lemma is_meas_gamma_1:
    ∀ ε, 
    is_measurable {h: ℍ | error μ target h > ε} :=
begin
    intro, 
    have COMPL: {h: ℍ | error μ target h > ε} = -{h: ℍ | error μ target h ≤ ε},
    {
        rw compl_set_of,
        simp,
    },
    rw COMPL,
    apply is_measurable.compl,
    have MLE := @measurable_le _ _ _ _ _ _ _ (λ h, error μ target h) (λ h, ε),
    apply MLE,
    apply error_measurable,
    apply measurable_const,
end

@[simp]
lemma is_meas_gamma_2:
    ∀ ε, 
    is_measurable {h: ℍ | error μ target h ≤ ε} :=
begin
    intros, 
    have COMPL: {h: ℍ | error μ target h ≤ ε} = -{h: ℍ | error μ target h > ε},
    {
        rw compl_set_of,
        simp,
    },
    rw COMPL,
    apply is_measurable.compl, 
    apply is_meas_gamma_1,
end

@[simp]
lemma is_meas_one: ∀ θ,
    θ > 0 → 
    is_measurable {x: ℍ |  ∀ p = label target x, (if p.snd then p.fst else 0) < θ} :=
begin
    introv T0, 
    convert_to (is_measurable {x: ℍ | (if (label target x).snd then (label target x).fst else 0) < θ}),
    {
        rw ext_iff, intro,
        repeat {rw mem_set_of_eq}, 
        split; intros,
        apply a, trivial,  
        rw H, assumption,      
    },
    unfold label, simp, unfold rle,
    rw ite_equals_union_interval θ T0 target,
    apply is_measurable.union,
    {
        exact is_measurable_Ico,
    },
    {
        rw Ioi_complement target,
        apply is_measurable.compl,
        apply is_measurable.union,
        exact is_measurable_Iio,
        rw ← (Ico_diff_Ioo_eq_singleton (by exact lt_add_one target)),
        apply is_measurable.diff,
        exact is_measurable_Ico,
        exact is_measurable_Ioo,
    },    
end

@[simp]
lemma is_meas_forall: ∀ θ, 
    θ > 0 → 
    ∀ n, is_measurable {S: vec ℍ n |  ∀ (i: dfin (nat.succ n)), ∀ p = label target (kth_projn S i), (if p.snd then p.fst else 0) < θ} :=
begin
    intros, 
    convert_to (is_measurable {S: vec ℍ n |  ∀ (i: dfin (nat.succ n)), (if (label target (kth_projn S i)).snd then (label target (kth_projn S i)).fst else 0) < θ}),
    {
        rw ext_iff, intro,
        repeat {rw mem_set_of_eq}, 
        split; intros,
        apply (a_1 i), trivial,  
        rw H, apply (a_1 i),         
    },
    have FOO:= is_measurable_simple_vec (λ x, (if (label target x).snd then (label target x).fst else 0) < θ),
    apply FOO,
    convert_to (is_measurable {x: ℍ |  ∀ p = label target x, (if p.snd then p.fst else 0) < θ}),
    {
        rw ext_iff, intro,
        repeat {rw mem_set_of_eq}, 
        split; intros,
        rw H, assumption, 
        apply a_1, trivial,  
    },
    apply is_meas_one; assumption,
end

end stump