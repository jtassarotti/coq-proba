/-
Copyright © 2020, Oracle and/or its affiliates. All rights reserved.
-/

import measure_theory.measurable_space
import measure_theory.borel_space
import measure_theory.integration
import topology.instances.nnreal
import ..lib.basic
import ..lib.util

open set nat

local attribute [instance] classical.prop_decidable

namespace relax

notation `ℍ` := nnreal

variables (μ: probability_measure ℍ) 

noncomputable
instance meas_2 (n1: ℕ) (n2: ℕ): measurable_space (vec ℍ n1 × vec ℍ n2) :=
begin
    apply_instance,
end

noncomputable
def prod_2 (n1: ℕ) (n2: ℕ): probability_measure (vec ℍ n1 × vec ℍ n2) :=
    prod.prob_measure (vec.prob_measure n1 μ) (vec.prob_measure n2 μ)

noncomputable
instance meas_3 (n1: ℕ) (n2: ℕ) (n3: ℕ): measurable_space (vec ℍ n1 × vec ℍ n2 × vec ℍ n3) :=
begin
    apply_instance,
end

noncomputable
def prod_3 (n1: ℕ) (n2: ℕ) (n3: ℕ): probability_measure (vec ℍ n1 × vec ℍ n2 × vec ℍ n3) :=
    let u1 := vec.prob_measure n1 μ  in
    let u2 := vec.prob_measure n2 μ  in
    let u3 := vec.prob_measure n3 μ  in
    let p1 := prod.prob_measure u2 u3 in
    let p2 := prod.prob_measure u1 p1 in
    p2

noncomputable
def get (u : ℍ × ℍ) (n: ℕ): ℍ :=
    if n = 1 then u.fst else u.snd

/-  Uniform distribution -/

axiom generate_uniform_variate_simple: ℝ × ℝ × ℍ → ℍ 

def E_uni (t: ℍ) := {v: ℍ | generate_uniform_variate_simple(0, 1, v) = t}

axiom generate_uniform_variate_simple_in:
    ∀ v: ℍ, ∀ a: ℍ, ∀ b: ℍ, 
    a ≤ generate_uniform_variate_simple(a, b, v) ∧ 
    generate_uniform_variate_simple(a, b, v) ≤ b

@[simp]
axiom uniform_measurable: measurable generate_uniform_variate_simple 

@[simp]
axiom uniform_event_measurable: ∀ t, is_measurable {v: ℍ | generate_uniform_variate_simple(0, 1, v) = t}

/- Binomial distribution -/

axiom generate_binomial_variate_simple: ℍ × ℍ → ℕ 

def E_bin (t: ℍ) := {v: ℍ | generate_binomial_variate_simple(t,v) = 1}

@[simp]
axiom binomial_measurable: measurable generate_binomial_variate_simple 

@[simp]
axiom binomial_event_measurable: ∀ t, is_measurable {v: ℍ | generate_binomial_variate_simple(t,v) = 1}

axiom generate_binomial_variate_simple_prop: 
    ∀ t, μ (E_bin t) = t 

axiom generate_binomial_variate_simple_prop_2: 
    ∀ r, ∀ a, ∀ b,
    a ≤ b → 
    generate_binomial_variate_simple(a,r) = 1 → 
    generate_binomial_variate_simple(b,r) = 1

end relax
