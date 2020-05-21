/-
Copyright © 2020, Oracle and/or its affiliates. All rights reserved.
-/

import .relax

open set
open real

local attribute [instance] classical.prop_decidable

namespace relax

variables (μ: probability_measure ℍ)

noncomputable
def code_f (u: ℍ × ℍ): ℍ :=
    let u1 := u.fst in
    let u2 := u.snd in
    let μ := generate_uniform_variate_simple(0,1,u1) in
    μ

noncomputable
def code_g (u: ℍ × ℍ): ℕ :=
    let u1 := u.fst in
    let u2 := u.snd in
    let μ := generate_uniform_variate_simple(0,1,u1) in
    let X := generate_binomial_variate_simple(μ,u2) in
    X

noncomputable
def coin_flip_code_simple: ℍ × ℍ → ℍ × ℕ :=
    λ (u: ℍ × ℍ), (code_f u,code_g u)

@[simp]
lemma is_measurable_function: 
    measurable (λ (u: ℍ × ℍ), coin_flip_code_simple u) :=
begin
    unfold coin_flip_code_simple,
    unfold code_f, unfold code_g, 
    simp,
    apply measurable.prod; simp,
    {
        apply measurable.comp,
        apply uniform_measurable,
        apply measurable.prod; simp,
        apply measurable_const,
        apply measurable.prod; simp,
        apply measurable_const,
        apply measurable_fst,
        apply measurable_id,
    },
    {
        apply measurable.comp,
        apply binomial_measurable,
        apply measurable.prod; simp,
        apply measurable.comp,
        apply uniform_measurable,
        apply measurable.prod; simp,
        apply measurable_const,
        apply measurable.prod; simp,
        apply measurable_const,
        apply measurable_fst,
        apply measurable_id,
        apply measurable_snd,      
        apply measurable_id,  
    }
end

noncomputable
def coin_flip_model_simple: probability_measure (ℍ × ℕ) :=
    map coin_flip_code_simple (prod.prob_measure μ μ)

/- Event: the result of the coin flip is head -/
def A := {v: (ℍ × ℕ) | v.snd = 1}

@[simp]
lemma is_measurable_A: is_measurable A :=
begin
    unfold A,
    have prod: {v: (ℍ × ℕ) | v.snd = 1} = set.prod {x: ℍ | true} {n: ℕ | n = 1}, 
    {
        rw ext_iff, intro,
        rw mem_prod_eq,
        split, intro,
        split,
        rw mem_set_of_eq at *,
        trivial,
        rw mem_set_of_eq at *,
        exact a,
        intro,
        cases a,
        rw mem_set_of_eq at *,
        exact a_right,
    },
    rw prod, clear prod,
    apply is_measurable_set_prod,
    apply is_measurable.univ,
    trivial,
end

/- Event: the bias of the coin is t -/
def B(t: ℍ) := {v: (ℍ × ℕ) | v.fst = t}

@[simp]
lemma is_measurable_B: ∀ t, is_measurable (B t) :=
begin
    intro,
    unfold B,
    have prod: {v: (ℍ × ℕ) | v.fst = t} = set.prod {t} univ, 
    {
        rw ext_iff, intro,
        rw mem_prod_eq,
        split, intro,
        split,
        rw mem_set_of_eq at *,
        rw a, simp,
        rw mem_set_of_eq at *,
        trivial,
        intro,
        cases a,
        rw mem_set_of_eq at *,
        simp at a_left,
        exact a_left,
    },
    rw prod, clear prod,
    apply is_measurable_set_prod,  
    swap, apply is_measurable.univ,
    apply measure_theory.is_measurable_singleton,
end

@[simp]
lemma is_measurable_event: ∀ t, is_measurable (A ∩ (B t)) :=
begin
    intro,
    apply is_measurable.inter; simp,
end

@[simp]
lemma coin_flip_property_prep_1:
    ∀ t: ℍ,
    {v: ℍ × ℍ | generate_binomial_variate_simple(t,v.snd) = 1} =
    set.prod univ (E_bin t) :=
begin
    intro,
    rw ext_iff,
    intro,
    repeat {rw mem_set_of_eq},
    split; intros,
    {
        simp,
        exact a,
    },
    {
        simp at a,
        exact a,
    }
end

@[simp]
lemma coin_flip_property_prep_2:
    ∀ t: ℍ,
    {v: ℍ × ℍ | generate_uniform_variate_simple(0, 1, v.fst) = t} =
    (E_uni t).prod univ :=
begin
    intro,
    rw ext_iff,
    intro,
    repeat {rw mem_set_of_eq},
    split; intros,
    {
        simp,
        exact a,
    },
    {
        simp at a,
        exact a,
    }
end

@[simp]
lemma coin_flip_property_prep_6:
    ∀ t: ℍ, 
    set.prod univ (E_bin t) ∩ set.prod (E_uni t) univ
    = set.prod (E_uni t) (E_bin t) :=
begin
    intro,
    rw ext_iff, intros, 
    repeat {rw inter_def},
    rw mem_set_of_eq,
    repeat {rw mem_prod_eq},
    simp at *,
    split; intros; tautology,
end

lemma coin_flip_property_prep_5:
    ∀ t: ℍ,
    {v: ℍ × ℍ | generate_binomial_variate_simple((generate_uniform_variate_simple(0, 1, v.fst)), v.snd) = 1} ∩
    {v: ℍ × ℍ | generate_uniform_variate_simple(0, 1, v.fst) = t} =
    {v: ℍ × ℍ | generate_binomial_variate_simple(t, v.snd) = 1} ∩ 
    {v: ℍ × ℍ | generate_uniform_variate_simple(0, 1, v.fst) = t} :=
begin
    intro, 
    simp,
    rw inter_def, simp,
    rw ext_iff,
    intro,
    unfold E_uni, unfold E_bin,
    repeat {rw mem_set_of_eq},
    split; intros,
    {
        cases a,
        rw a_right at a_left,
        simp at *,
        tautology,
    },
    {
        simp at *,
        cases a,
        rw a_left,
        rw a_right,
        simp,
    }
end

/- Whatever the bias is, the probability of getting head given
that the bias is t is t -/
lemma coin_flip_property:
    ∀ t: ℍ, 
    cond_prob (coin_flip_model_simple μ) A (B t) = t :=
begin
    intros,
    unfold cond_prob,
    dunfold coin_flip_model_simple,
    rw map_apply; try {simp},
    unfold A, unfold B,
    simp,
    unfold coin_flip_code_simple,
    unfold code_f, unfold code_g,

    rw coin_flip_property_prep_5,
    rw coin_flip_property_prep_1,
    rw coin_flip_property_prep_2,
    rw coin_flip_property_prep_6, 

    rw prod.prob_measure_apply,
    rw prod.prob_measure_apply,
    rw generate_binomial_variate_simple_prop,
    rw generate_uniform_variate_simple_prop,
    
    have alg: 1 * μ univ = 1,
    simp, 
    rw alg, clear alg,
    rw mul_comm,
    show t * 1 * 1⁻¹ = t,
    rw mul_assoc, simp,  

    apply uniform_event_measurable,
    apply is_measurable.univ,
    apply uniform_event_measurable,
    apply binomial_event_measurable,
end

lemma pull_back:
    ∀ f:  ℍ × ℍ → ℍ × ℕ,
    ∀ γ: probability_measure (ℍ × ℕ),
    γ = map f (prod.prob_measure μ μ) →
    measurable f →
    ∀ g: ℍ × ℍ → ℍ,
    ∀ h: ℍ × ℍ → ℕ,
    f = (λ (x: ℍ × ℍ), (g x, h x)) →
    ∀ P: set (ℍ × ℕ),
    is_measurable (set_of P) →
    ∀ Q1: set ℍ,
    is_measurable Q1 →
    ∀ Q2: set ℍ,
    is_measurable Q2 →
    (f ⁻¹' P) = set.prod Q1 Q2 →
    γ P = μ Q1 * μ Q2 :=
begin
    intros,
    rw a,
    rw map_apply; try {simp},
    rw a_2 at *, 
    rw a_6,
    rw prod.prob_measure_apply,
    tidy,
end

def my_pull_back := pull_back μ coin_flip_code_simple (coin_flip_model_simple μ) (refl (map coin_flip_code_simple (prod.prob_measure μ μ))) is_measurable_function code_f code_g (refl coin_flip_code_simple)

lemma coin_flip_property_2:
    ∀ t: ℍ, 
    cond_prob (coin_flip_model_simple μ) A (B t) = t :=
begin
    intros,
    unfold cond_prob,

    rw my_pull_back μ (A ∩ (B t)) (is_measurable_event t) (E_uni t) _ (E_bin t) _,
    rw my_pull_back μ (B t) (is_measurable_B t) (E_uni t) _ univ _,
    rw generate_uniform_variate_simple_prop,
    rw generate_binomial_variate_simple_prop,

    simp,
    show t * 1⁻¹ = t,
    rw ← mul_one t,
    rw mul_assoc,
    simp,

    unfold coin_flip_code_simple, 
    unfold code_f,
    unfold code_g,
    unfold B,
    simp,
    
    simp,
    apply is_measurable.univ,

    unfold coin_flip_code_simple, 
    unfold code_f,
    unfold code_g,
    unfold A, unfold B,
    simp,   
    rw ← coin_flip_property_prep_2, 
    rw coin_flip_property_prep_5,
    simp,

    simp,
    simp,

end

#check my_pull_back

lemma event_left: 
    ∀ P: ℍ → Prop,
    {x: ℍ × ℕ | P x.fst} = set.prod {x: ℍ | P x} {n: ℕ | true} :=
begin
    intro,
    rw ext_iff,
    intro,
    repeat {rw mem_set_of_eq},
    split; intros,
    {
        simp,
        exact a,
    },
    {
        simp at a,
        exact a,
    }    
end


end relax
