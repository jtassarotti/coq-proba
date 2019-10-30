/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import .setup_definition .setup_measurable 
import .algorithm_definition .algorithm_measurable 
import .sample_complexity
import .stump_pac_lemmas
import .to_epsilon

open set nat

local attribute [instance] classical.prop_decidable

namespace stump

variables (μ: probability_measure ℍ) (target: ℍ) (n: ℕ)

noncomputable
def denot: probability_measure ℍ :=
    let η := vec.prob_measure n μ  in 
    let ν := map (label_sample target n) η in  
    let γ := map (choose n) ν in
    γ

lemma pullback:
    ∀ P: nnreal → Prop, 
    is_measurable {h: ℍ | P(@error μ target h)} →
    is_measurable {S: vec (ℍ × bool) n | P(error μ target (choose n S))} → 
    (denot μ target n) {h: ℍ | P(@error μ target h)} = (vec.prob_measure n μ) {S: vec ℍ n | P(error μ target (choose n (label_sample target n S)))} :=
begin
    intros,
    dunfold denot,
    rw map_apply, 
    rw map_apply,
    repeat {simp},
    repeat {assumption},
end

theorem choose_PAC:
    ∀ ε: nnreal, ∀ δ: nnreal, ∀ n: ℕ, 
    ε > 0 → ε < 1 → δ > 0 → δ < 1 → (n: ℝ) > (complexity ε δ) →
    (denot μ target n) {h: ℍ | @error μ target h ≤ ε} ≥ 1 - δ :=
begin
    introv eps_0 eps_1 delta_0 delta_1 n_gt, 
    by_cases((μ (Ioc 0 target)) > ε),
    {
        rw ← probability_measure.neq_prob_set,
        rw pullback μ target n (λ x, x > ε) _ _; try {simp},
        transitivity ((1 - ε)^(n+1)),
        {
            have EPS := extend_to_epsilon_1 μ target ε eps_0 h, cases EPS with θ θ_prop, cases θ_prop, 
            have TZ: θ > 0, 
            {
                by_contradiction h_contra,
                simp at h_contra, rw h_contra at *,
                have CONTRA: ¬ (μ (Ioc 0 target) ≤ ε), simp, assumption,
                contradiction,
            },
            transitivity ((vec.prob_measure n μ) {S: vec ℍ n |  ∀ (i: dfin (nat.succ n)), ∀ p = label target (kth_projn S i), (if p.snd then p.fst else 0) < θ}),
            {
                apply probability_measure.prob_mono,
                refine all_missed _ _ _ _ _ θ_prop_right,
            },
            {
                have INDEP := @prob_independence ℍ _ n _ (λ x, ∀ p = label target x, (if p.snd then p.fst else 0) < θ) μ (is_meas_one target θ TZ) (is_meas_forall target θ TZ),
                rw INDEP, clear INDEP,
                simp,
                apply pow_preserves_order (n+1),
                refine miss_prob _ _ _ _ TZ θ_prop_left,
            },
        },
        {
            apply complexity_enough ε δ n; assumption,
        },
        exact le_of_lt delta_1,
        simp,
    },
    {
        simp at h,
        rw pullback μ target n (λ x, x ≤ ε) _ _; try {simp},
        have DC: (vec.prob_measure n μ) {S: vec ℍ n | error μ target (choose n (label_sample target n S)) ≤ ε} = 1,
        {
            have AS := always_succeed μ target ε eps_0 n h, 
            refine probability_measure.prob_trivial _ _ AS,
        },
        rw DC; try {assumption},
        apply super_dumb, assumption, 
    },
end

end stump