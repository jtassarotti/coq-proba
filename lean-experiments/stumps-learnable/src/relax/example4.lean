/-
Copyright © 2020, Oracle and/or its affiliates. All rights reserved.
-/

import .relax

local attribute [instance] classical.prop_decidable

open set

namespace relax

variables (μ: probability_measure ℍ)

noncomputable
def maj_code (u: ℍ × ℍ): (ℍ × ℕ) :=
    let u1 := u.fst in
    let u2 := u.snd in
	let theta := generate_uniform_variate_simple(0,1,u1) in
	let X := generate_binomial_variate_simple(theta,u2) in
	(theta,X)

@[simp]
lemma measurable_maj_code: measurable ( λ (u: ℍ × ℍ),maj_code u) := 
begin
  unfold maj_code,
  simp,
  apply measurable.prod; simp,
  { 
    apply measurable.comp,
    { apply uniform_measurable },
    {
      apply measurable.prod; simp,
      { apply measurable_const },
      apply measurable.prod; simp,
      { apply measurable_const },
      apply measurable_fst,
      apply measurable_id,
    }
  },
  apply measurable.comp,
  { apply binomial_measurable, },
  apply measurable.prod; simp,
  { apply measurable.comp,
    { apply uniform_measurable },
    apply measurable.prod; simp,
    { apply measurable_const },
    apply measurable.prod; simp,
    { apply measurable_const },
    apply measurable_fst,
    apply measurable_id,
  },
  apply measurable_snd, apply measurable_id
end

noncomputable
def γ: probability_measure (ℍ × ℕ) :=
	map maj_code (prod.prob_measure μ μ)

def B_(t: ℍ) := {v: (ℍ × ℕ)| v.fst = t}
def male_selected_ := {v: (ℍ × ℕ)  | v.snd = 1}

lemma rw_gamma_1:
	∀ t: ℍ, 
	γ μ {a: ℍ × ℕ | a.fst = t} = 1 :=
begin
	intros,
	dunfold γ,
	rw map_apply, simp,
	unfold maj_code, simp,
	have set_rw: {a: ℍ × ℍ | generate_uniform_variate_simple(0,1,a.fst) = t} = set.prod {a: ℍ | generate_uniform_variate_simple(0,1,a) = t} univ,
	{
		rw ext_iff,
		intros,
		repeat {rw mem_set_of_eq}, simp,
	},
	rw set_rw, clear set_rw,
	rw prod.prob_measure_apply, simp,

	have t_rw:= generate_uniform_variate_simple_prop μ t,
	unfold E_uni at t_rw,
	rw t_rw at *, 

	/- Measures-/
        { sorry },
        { sorry },
        { apply measurable_maj_code },
	{ sorry },

end

lemma rw_gamma_2:
	∀ t: ℍ, 
	γ μ {a: ℍ × ℕ | a.snd = 1 ∧ a.fst = t} = t :=
begin
	intros,
	dunfold γ,
	rw map_apply, simp,
	have set_rw: {a: ℍ × ℍ | (maj_code a).snd = 1 ∧ (maj_code a).fst = t} = set.prod {a: ℍ | generate_uniform_variate_simple(0,1,a) = t} {a: ℍ | generate_binomial_variate_simple(t,a) = 1},
	{
		rw ext_iff,
		intros,
		repeat {rw mem_set_of_eq}, simp,
		cases x,
		unfold maj_code, simp,
	
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
	},
	rw set_rw, clear set_rw,
	rw prod.prob_measure_apply,

	have t_rw:= generate_uniform_variate_simple_prop μ t,
	unfold E_uni at t_rw,
	rw t_rw at *, simp,

	have bin_rw:= generate_binomial_variate_simple_prop μ t,
	unfold E_bin at bin_rw,
	rw bin_rw at *, 

	/- Measures-/
	repeat {sorry},
end

lemma inv_one : (1 : nnreal) ⁻¹ = (1: nnreal) := nnreal.eq $ inv_one
lemma div_one : ∀ (t: nnreal), t/(1 : nnreal) = t :=
begin assume t, by rw [nnreal.div_def, inv_one, mul_one] end

lemma maj_:
	∀ t: ℍ, 
	cond_prob (γ μ) male_selected_ (B_ t) = t :=
begin
	intros,
	unfold cond_prob,

	rw inter_def,
	unfold male_selected_, unfold B_,
	simp,

	rw rw_gamma_1,
	rw rw_gamma_2,
        rw div_one,
end


noncomputable
def code (u: (ℍ × ℕ) × ℍ × ℍ): (ℍ × ℕ) × (ℍ × ℕ) :=
    let theta := u.fst.fst in
    let X := u.fst.snd in
    let u3 := u.snd.fst in
	let u4 := u.snd.snd in
	let phi := generate_uniform_variate_simple(0.8 * theta,1,u3) in
	let Y := generate_binomial_variate_simple(phi,u4) in
	((theta,X),(phi,Y))

@[simp]
lemma measurable_code:measurable ( λ (u: (ℍ × ℕ) × ℍ × ℍ),code u) := 
begin
	sorry,
end

noncomputable
def δ: probability_measure ((ℍ × ℕ) × (ℍ × ℕ)) :=
    map code (prod.prob_measure (γ μ) (prod.prob_measure μ μ))

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

lemma rw_dive:
	∀ P: ℍ × ℕ → Prop,
	δ μ {v: (ℍ × ℕ) × (ℍ × ℕ) | P v.fst} = γ μ {v: ℍ × ℕ | P v} :=
begin
	intros,
	dunfold δ,
	dunfold γ,
	rw map_apply, simp,
	rw map_apply, simp, 
	unfold code, simp,

	have set_rw: {a: (ℍ × ℕ) × ℍ × ℍ | P a.fst} = set.prod {a: ℍ × ℕ | P a} (set.prod univ univ),
	{
		rw ext_iff,
		intros,
		repeat {rw mem_set_of_eq}, simp,
	},
	rw set_rw, simp, clear set_rw,
	rw prod.prob_measure_apply, simp,
	rw map_apply, simp,

	/-MEasure-/
	repeat {sorry},
end

lemma set_rw_1:
	∀ t: ℍ, 
	set.prod {a: ℍ × ℕ | a.fst = t} (set.prod univ {a: ℍ | generate_binomial_variate_simple(4/5 * t,a) = 1})
	⊆  {a: (ℍ × ℕ) × ℍ × ℍ | (code a).snd.snd = 1 ∧ (code a).fst.fst = t} :=  
begin
	intros,
	unfold set.prod,
	rw set_of_subset_set_of,
	repeat {rw mem_set_of_eq}, simp,

	intros,
	unfold code, simp,

	rw a_1 at *, simp,
	apply generate_binomial_variate_simple_prop_2 b_1.snd (4/5 *t),
	have uni_in:= generate_uniform_variate_simple_in b_1.fst (4/5 * t) 1,
	cases uni_in, assumption,
	assumption,
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
	have bar:= probability_measure.prob_mono (prod.prob_measure (γ μ) (prod.prob_measure μ μ)) foo,
	clear foo,

	rw prod.prob_measure_apply at bar,
	rw prod.prob_measure_apply at bar,

	have rw_1 := rw_dive μ (λ (v: ℍ × ℕ), v.fst = t),
	simp at rw_1,
	rw rw_1, clear rw_1,

	rw rw_gamma_1 μ t at *, simp at *,

	have bin_rw:= generate_binomial_variate_simple_prop μ (4/5 * t),
	unfold E_bin at bin_rw,
	rw bin_rw at *, clear bin_rw,

	dunfold δ, 
	rw map_apply, simp,

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

	have rw_1 := rw_dive μ (λ (v: ℍ × ℕ), v.fst = t),
	simp at rw_1,
	rw rw_1, clear rw_1,

	have rw_2 := rw_dive μ (λ (v: ℍ × ℕ), v.snd = 1 ∧ v.fst = t),
	simp at rw_2,
	rw rw_2, clear rw_2,

	have prop:= maj_ μ t,
	unfold cond_prob at prop,
	unfold male_selected_ at prop, unfold B_ at prop,
	rw inter_def at prop,
	simp at prop,
	assumption,
end

theorem final:
	∀ t: ℍ,
	(0.8:nnreal) * cond_prob (δ μ) male_selected (B t) ≤ cond_prob (δ μ) female_selected (B t) :=
begin
	intros,
	rw maj,
	apply principal,
end

theorem corr1:
	∀ t: ℍ,
	(0.8: nnreal) * δ μ (male_selected ∩ (B t)) ≤ δ μ (female_selected ∩ (B t)) :=
begin
	intros,
	rw cond_prob_rw,
	rw cond_prob_rw,
	rw ← mul_assoc,
	rw mul_le_mul_right,
	apply final,
	
	/- non zero basics -/
	repeat {sorry},
end

theorem corr2:
	(λ (t: ℍ), (0.8: nnreal) * δ μ (male_selected ∩ (B t))) ≤ (λ (t: ℍ), δ μ (female_selected ∩ (B t))) :=
begin
	intros,
	funext,
	intro, 
	simp,
	apply corr1,
end

open measure_theory measure_theory.measure measure_theory.simple_func

noncomputable
instance foo: measurable_space ℍ :=
begin
	apply_instance,
end

noncomputable
instance bar: measure_space ℍ :=
begin
	sorry,
end

lemma lintegral_mono ⦃f g : ℍ → nnreal⦄ (h : f ≤ g) : (lintegral (λ a: ℍ, f a)) ≤ (lintegral (λ a: ℍ, g a)) :=
begin
	sorry,
end

noncomputable
def start: measure_theory.measure ℍ :=
	map (λ (u: ℍ), generate_uniform_variate_simple(0,1,u)) μ

theorem corr3:
	(0.8: ennreal) * integral (start μ) (λ (t: ℍ), δ μ (male_selected ∩ (B t))) ≤ integral (start μ) (λ (t: ℍ),δ μ (female_selected ∩ (B t))) :=
begin
	dunfold integral,
	rw ← lintegral_const_mul,
	have foo:= @lintegral_mono (λ (t: ℍ), (0.8: nnreal) * δ μ (male_selected ∩ (B t))) (λ (t: ℍ),δ μ (female_selected ∩ (B t))) (corr2 μ), 
	simp at foo,

	unfold_coes at *,
	rw ennreal.coe_to_nnreal,
	dunfold ennreal.to_nnreal at foo,
	
	
	have coe: some((4/5):nnreal) = ((4/5):nnreal), 
	{
		unfold_coes,
	},
	rw ← coe,
	apply foo,

	/- Corceion hell -/
	sorry,
	sorry,

end

end relax
