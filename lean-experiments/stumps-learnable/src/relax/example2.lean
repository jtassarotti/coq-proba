/-
Copyright © 2020, Oracle and/or its affiliates. All rights reserved.
-/

import .relax

local attribute [instance] classical.prop_decidable

open set

namespace relax

variables (μ: probability_measure ℍ)

noncomputable
def code_1 (u: ℍ): ℍ :=
	generate_uniform_variate_simple(0,1,u)

noncomputable
def μ1: probability_measure ℍ :=
    map code_1 μ

noncomputable
def code_2 (u: ℍ × ℍ): ℕ :=
	let u1 := u.fst in
    let u2 := u.snd in
	let theta := generate_uniform_variate_simple(0,1,u1) in
	generate_binomial_variate_simple(theta,u2)

noncomputable
def μ2: probability_measure ℕ :=
    map code_2 (prod.prob_measure μ μ)

noncomputable
def code_3 (u: ℍ × ℍ): ℍ :=
	let u1 := u.fst in
	let u2 := u.snd in 
	let theta := generate_uniform_variate_simple(0,1,u1) in
	generate_uniform_variate_simple(0.8 * theta,1,u2)

noncomputable
def μ3: probability_measure ℍ :=
    map code_3 (prod.prob_measure μ μ)

noncomputable
def code_4 (u: ℍ × ℍ × ℍ): ℕ :=
	let u1 := u.fst in
    let u2 := u.snd.fst in
	let u3 := u.snd.snd in
	let theta := generate_uniform_variate_simple(0,1,u1) in
	let phi := generate_uniform_variate_simple(0.8 * theta,1,u2) in
	generate_binomial_variate_simple(phi,u3)

noncomputable
def μ4: probability_measure ℕ :=
    map code_4 (prod.prob_measure μ (prod.prob_measure μ μ))

noncomputable
def code_5 (u: ℍ × ℍ): ℍ × ℕ :=
	let u1 := u.fst in
	let theta := code_1 u1 in
	let X := code_2 u in
	(theta,X)

noncomputable
def μ5: probability_measure (ℍ × ℕ) :=
    map code_5 (prod.prob_measure μ μ)

noncomputable
def code_6 (u: ℍ × ℍ × ℍ): ℍ × ℕ :=
	let u1 := u.fst in
    let u2 := u.snd.fst in
	let phi := code_3 (u1,u2) in
	let Y := code_4 u in
	(phi,Y)

noncomputable
def μ6: probability_measure (ℍ × ℕ) :=
    map code_6 (prod.prob_measure μ (prod.prob_measure μ μ))

noncomputable
def mod_code (u: ℍ × ℍ × ℍ): (ℍ × ℕ) × (ℍ × ℕ) :=
    let u1 := u.fst in
    let u2 := u.snd.fst in
    let u3 := u.snd.snd in
	let (theta,X) := code_5 (u1,u2) in
	let (phi,Y) := code_6 (u1,u3,u2) in
	((theta,X),(phi,Y))

@[simp]
lemma measurable_mod_code:measurable ( λ ( u: ℍ × ℍ × ℍ),mod_code u) := 
begin
	sorry,
end

noncomputable
def δ: probability_measure ((ℍ × ℕ) × (ℍ × ℕ)) :=
    map mod_code (prod.prob_measure μ (prod.prob_measure μ μ))

def B(t: ℍ) := {v: (ℍ × ℕ) × (ℍ × ℕ) | v.fst.fst = t}
def C(t: ℍ) (p: ℍ) := {v: (ℍ × ℕ) × (ℍ × ℕ) | v.fst.fst = t ∧ v.snd.fst = p}

def male_selected := {v: (ℍ × ℕ) × (ℍ × ℕ) | v.fst.snd = 1}

@[simp]
lemma male_selected_is_measurable: is_measurable male_selected :=
begin
	sorry,
end

def female_selected := {v: (ℍ × ℕ) × (ℍ × ℕ) | v.snd.snd = 1}

@[simp]
lemma female_selected_is_measurable: is_measurable female_selected :=
begin
	sorry,
end

lemma set_rw_1:
	∀ t: ℍ,
	set.prod {a: ℍ | generate_uniform_variate_simple(0,1,a) = t} (set.prod {a: ℍ | generate_binomial_variate_simple(4/5 * t,a) = 1} univ) 
	⊆  {a: ℍ × ℍ × ℍ | (mod_code a).snd.snd = 1 ∧ (mod_code a).fst.fst = t} :=  
begin
	intros,
	unfold set.prod,
	rw set_of_subset_set_of,
	repeat {rw mem_set_of_eq}, simp,

	intros,
	unfold mod_code, simp,
	unfold code_5, simp,
	unfold mod_code._match_2, 
	unfold code_6, simp,
	unfold mod_code._match_1,
	unfold code_1, unfold code_3, unfold code_4, simp,

	rw a_1 at *, simp,
	apply generate_binomial_variate_simple_prop_2 b.fst (4/5 *t),
	have uni_in:= generate_uniform_variate_simple_in b.snd (4/5 * t) 1,
	cases uni_in, assumption,
	assumption,
end

lemma set_rw_3:
	∀ t: ℍ, 
	{a: ℍ × ℍ × ℍ | (mod_code a).fst.fst = t} =
	set.prod {a: ℍ | generate_uniform_variate_simple(0,1,a) = t} (set.prod univ univ) :=
begin
	intros,
	rw ext_iff, intros,
	repeat {rw mem_set_of_eq}, simp,
	cases x,
	cases x_snd, simp,

	unfold mod_code, simp,
	unfold code_5, simp,
	unfold mod_code._match_2, 
	unfold code_6, simp,
	unfold mod_code._match_1, simp,
	dunfold code_1, 
	tautology,
end

lemma meas_rw_3:
	∀ t: ℍ, 
	(prod.prob_measure μ (prod.prob_measure μ μ)) {a: ℍ × ℍ × ℍ | (mod_code a).fst.fst = t} =
	1 :=
begin
	intros,
	rw set_rw_3,
	rw prod.prob_measure_apply,
	rw prod.prob_measure_apply,

	have t_rw:= generate_uniform_variate_simple_prop μ t,
	unfold E_uni at t_rw,
	rw t_rw at *, clear t_rw, simp at *,	

	/- Measure -/
	repeat {sorry},

end

lemma set_rw_4:
	∀ t: ℍ, 
	{a: ℍ × ℍ × ℍ | (mod_code a).fst.snd = 1 ∧ (mod_code a).fst.fst = t} =
	set.prod {a: ℍ | generate_uniform_variate_simple(0,1,a) = t} (set.prod {a: ℍ | generate_binomial_variate_simple(t,a) = 1} univ) :=
begin
	intros,
	rw ext_iff, intros,
	repeat {rw mem_set_of_eq}, simp,
	cases x,
	cases x_snd, simp,

	unfold mod_code, simp,
	unfold code_5, simp,
	unfold mod_code._match_2, 
	unfold code_6, simp,
	unfold mod_code._match_1, simp,
	unfold code_1, unfold code_2, simp,
	
	split; intros,
	{
		cases a,
		rw a_right at *, simp at *,
		assumption,
	},
	{
		cases a,
		rw a_left at *, simp at *,
		assumption,
	},
end

lemma principal:
	∀ t,
	4/5 * t ≤ cond_prob (δ μ) female_selected (B t) :=
begin
	intros,
	unfold cond_prob,

	rw inter_def,
	unfold female_selected, unfold B,
	simp,

	have foo:= set_rw_1 t,
	have bar:= probability_measure.prob_mono (prod.prob_measure μ (prod.prob_measure μ μ)) foo,
	clear foo,

	rw prod.prob_measure_apply at bar,
	rw prod.prob_measure_apply at bar,

	dunfold δ, 
	rw map_apply, simp,
	rw map_apply, simp,

	have t_rw:= generate_uniform_variate_simple_prop μ t,
	unfold E_uni at t_rw,
	rw t_rw at *, clear t_rw, simp at *,

	have bin_rw:= generate_binomial_variate_simple_prop μ (4/5 * t),
	unfold E_bin at bin_rw,
	rw bin_rw at *, clear bin_rw,

	rw meas_rw_3,

	repeat {sorry},

end

lemma maj:
	∀ t: ℍ, 
	cond_prob (δ μ) male_selected (B t) = t :=
begin
	intros,
	unfold cond_prob,

	rw inter_def,
	unfold male_selected, unfold B,
	simp,

	dunfold δ, 
	rw map_apply, simp,
	rw map_apply, simp,

	rw set_rw_3,
	rw prod.prob_measure_apply,
	rw prod.prob_measure_apply,

	rw set_rw_4,
	rw prod.prob_measure_apply,
	rw prod.prob_measure_apply,

	have t_rw:= generate_uniform_variate_simple_prop μ t,
	unfold E_uni at t_rw,
	rw t_rw at *, clear t_rw, simp at *,	

	have bin_rw:= generate_binomial_variate_simple_prop μ t,
	unfold E_bin at bin_rw,
	rw bin_rw at *, clear bin_rw,	

	/- Doable -/
	repeat {sorry},

end

theorem final:
	∀ t: ℍ, ∀ p: ℍ,
	0.8 * cond_prob (δ μ) male_selected (B t) ≤ cond_prob (δ μ) female_selected (B t) :=
begin
	intros,
	rw maj,
	apply principal,
end

end relax