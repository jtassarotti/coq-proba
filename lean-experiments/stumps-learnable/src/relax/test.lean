/-
Copyright © 2020, Oracle and/or its affiliates. All rights reserved.
-/

import .relax

local attribute [instance] classical.prop_decidable

namespace relax

variables (μ: probability_measure ℍ)

noncomputable
def coin_flip_code_simple (u: ℍ × ℍ × ℍ): ℍ × ℕ × ℕ :=
    let u1 := u.fst in
    let u2 := u.snd.fst in
    let u3 := u.snd.snd in
    let μ := generate_uniform_variate_simple(0,1,u1) in
    let X := generate_binomial_variate_simple(μ,u2) in
    let Y := generate_binomial_variate_simple(μ,u3) in
    (μ,X,Y)

noncomputable
def coin_flip_model_simple: probability_measure (ℍ × ℕ × ℕ) :=
    map coin_flip_code_simple (prod.prob_measure μ (prod.prob_measure μ μ))

lemma coin_flip_code_is_measurable: measurable ( λ ( u: nnreal × nnreal × nnreal),coin_flip_code_simple u) := 
begin
	unfold coin_flip_code_simple,
	apply measurable.prod; simp,
	{
		apply measurable.comp,
		apply uniform_measurable,
		apply measurable.prod; simp,
		{
			apply measurable_const,
		},
		{
			apply measurable.prod; simp,
			{
				apply measurable_const,
			},
			{
				apply measurable_fst,
				apply measurable_id,
			},
		},
	},
	{
		apply measurable.prod; simp,
		{
			apply measurable.comp,
			apply binomial_measurable,
			apply measurable.prod; simp,
			{
				apply measurable.comp,
				apply uniform_measurable,
				apply measurable.prod; simp,
				{
					apply measurable_const,
				},
				{
					apply measurable.prod; simp,
					{
						apply measurable_const,
					},
					{
						apply measurable_fst,
						apply measurable_id,
					},
				},
			},
			{
				apply measurable_fst,
				apply measurable_snd,
				apply measurable_id,
			},
		},
		{
			apply measurable.comp,
			apply binomial_measurable,
			apply measurable.prod; simp,
			{
				apply measurable.comp,
				apply uniform_measurable,
				apply measurable.prod; simp,
				{
					apply measurable_const,
				},
				{
					apply measurable.prod; simp,
					{
						apply measurable_const,
					},
					{
						apply measurable_fst,
						apply measurable_id,
					},
				},
			},
			{
				apply measurable_snd,
				apply measurable_snd,
				apply measurable_id,
			},
		},
	},
end




end relax