/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import data.set
import analysis.complex.exponential
import .attributed.dvector 
import lib.basic
import topology.constructions

local attribute [instance] classical.prop_decidable

open nnreal real ennreal set lattice
open topological_space 
open measure_theory

lemma lc_nnreal: 
    ∀ a: nnreal, ∀ b: nnreal, a + b = 1 → a = (1:nnreal) - b :=
assume a b h, h ▸ (nnreal.add_sub_cancel).symm

lemma super_dumb:
    ∀ δ: nnreal, δ > (0:nnreal) → (1:nnreal) - δ ≤ (1: nnreal) :=
assume h, by simp

lemma coe_pmeas:
    ∀ a: ennreal, ∀ b: ennreal, a ≤ (1:ennreal) → b ≤ (1: ennreal) → a ≤ b → ennreal.to_nnreal a ≤ ennreal.to_nnreal b :=
begin
    intros a b h₁ h₂ h₃, 
    rw [← coe_le_coe, coe_to_nnreal,coe_to_nnreal], 
    assumption,
    rw ←ennreal.lt_top_iff_ne_top, 
    exact lt_of_le_of_lt h₂ (ennreal.lt_top_iff_ne_top.2 one_ne_top),
    rw ←ennreal.lt_top_iff_ne_top, 
    exact lt_of_le_of_lt h₁ (ennreal.lt_top_iff_ne_top.2 one_ne_top),
end

lemma pow_preserves_order:
    ∀ n: ℕ, ∀ a: nnreal, ∀ b: nnreal, a ≤ b → a^n ≤ b^n :=
begin
    intros n a b h,
    induction n with k ih, 
    {by simp}, 
    {simp [pow_succ], exact mul_le_mul h ih (zero_le _) (zero_le _)}, 
end

lemma not_eq_prop:
    ∀ A: Prop, ∀ B: Prop, (¬ (A ↔ B)) ↔ ((¬ (A → B)) ∨ (¬ (B → A))) :=
begin
    intros, 
    split; intros,
    finish,
    finish,
end

lemma nnreal_sub_trans:
    ∀ a: nnreal, ∀ b: nnreal, 
    a ≥ b → 1 - a ≤ 1 - b :=
begin
    intros,
    rw nnreal.sub_le_iff_le_add,
    simp,
    by_cases (b ≤ 1),
    {
        have h: 1 + (a - b) = a + (1 - b),
        { 
            calc 1 + (a - b) = 1 + a - b : by rw [←nnreal.eq_iff,nnreal.coe_add, (nnreal.coe_sub _ _ a_1), ←add_sub_assoc, nnreal.coe_sub _, nnreal.coe_add];                        exact le_add_of_le_of_nonneg h (zero_le _)
                 ...         = a + 1 - b : by rw add_comm 
                 ...         = a + (1 - b) : by rw [←nnreal.eq_iff,nnreal.coe_add, (nnreal.coe_sub _ _ h), ←add_sub_assoc,nnreal.coe_sub _, nnreal.coe_add];exact le_add_of_le_of_nonneg a_1 (zero_le _),
                 
        },
        rw h.symm,
        cases b, cases a, dsimp at *, simp at *,
    },
    {
        simp at h,
        rw nnreal.sub_eq_zero, swap,
        exact le_of_lt h,
        simp,
        transitivity b,
        exact le_of_lt h,
        assumption,
    }
end

lemma prod_rw {α: Type} {β: Type}:
    ∀ P₁: α → Prop,
    ∀ P₂: β → Prop,
    { v : α × β | P₁ v.fst ∧ P₂ v.snd} = set.prod {x: α | P₁ x} {x: β | P₂ x} :=
begin
    intros,
    unfold set.prod, 
    rw ext_iff, intro,
    repeat {rw mem_set_of_eq}, 
end

lemma dfin_1_projn {α: Type}:
    ∀ P: α → Prop,
    ∀ x: vec α 0,
    (∀ (i: dfin 1), P (kth_projn x i)) ↔ P x :=
begin
    intros,
    split; intros,
    {
        simp at *,
        apply a,
        exact dfin.fz,
    },
    {
        simp at *, assumption,
    },
end

lemma dfin_1_projn' {α: Type}:
    ∀ P: α → Prop,
    { x: vec α 0 | ∀ (i: dfin 1), P (kth_projn x i)} = {x: α | P x} :=
begin
    intros,
    rw ext_iff, intro,
    repeat {rw mem_set_of_eq}, 
    rw dfin_1_projn,
    trivial,
end

lemma is_measurable_simple_vec {α: Type} [measurable_space α]:
    ∀ P: α → Prop,
    is_measurable {x: α | P x} →
    ∀ n, 
    is_measurable {v: vec α n | ∀ (i: dfin (nat.succ n)), P(kth_projn v i)} :=
begin
    intros,
    induction n; intros,
    {
        rw dfin_1_projn', assumption,
    },
    {
        dunfold vec,
        conv {
            congr, congr, funext, rw dfin_succ_prop_iff_fst_and_rst, skip,
        },
        have PROD := prod_rw (λ x, P x) (λ x, ∀ (i: dfin (nat.succ n_n)), P(kth_projn x i)), 
        simp at PROD,
        rw PROD, clear PROD,
        apply is_measurable_set_prod; try {assumption},
    },
end

/- Move these results back to where vec was defined (../to_mathlib.lean)-/
noncomputable
instance vec_topo: ∀ n: ℕ, topological_space (vec nnreal n) :=
begin
    intro,
    induction n,
    {
        dunfold vec,
        apply_instance,
    },
    {
        unfold vec,
        have PROD := @prod.topological_space nnreal (vec nnreal n_n) _ n_ih,
        assumption,
    },
end


instance vec_second_countable : ∀ n:ℕ, second_countable_topology (vec nnreal n) :=
begin
    intros n, 
    induction n with k ih,
    dsimp [vec], apply_instance,
    dsimp [vec], 
    haveI := second_countable_topology nnreal,
    apply_instance,
end

lemma vec.measurable_space_eq_borel (n : ℕ) : vec.measurable_space n = measure_theory.borel (vec nnreal n) :=
begin
    induction n with k ih, 
    refl,
    dsimp [vec], rw ←measure_theory.borel_prod, 
    rw prod.measurable_space, rw ←ih, refl,
end

lemma test''' :
    ∀ n: ℕ, 
    ∀ f: nnreal × vec nnreal n → nnreal,
    ∀ g: nnreal × vec nnreal n → nnreal,
    continuous f →
    continuous g →
    is_measurable {p: nnreal × (vec nnreal n) | f p < g p} :=
begin
    intros n f g hf hg,    
    convert measure_theory.is_measurable_of_is_open _,
    haveI := vec_second_countable n,
    swap, 
    change topological_space (vec nnreal (nat.succ n)), apply_instance,
    swap,
    exact is_open_lt hf hg, rw prod.measurable_space, 
    rw ←measure_theory.borel_prod, rw vec.measurable_space_eq_borel n, refl,
end

lemma to_nnreal_sub {r₁ r₂ : ennreal} (h₁ : r₁ < ⊤) (h₂ : r₂ < ⊤) :
  (r₁ - r₂).to_nnreal = r₁.to_nnreal - r₂.to_nnreal :=
by rw [← ennreal.coe_eq_coe, ennreal.coe_sub, ennreal.coe_to_nnreal (ne_top_of_lt h₂), ennreal.coe_to_nnreal (ne_top_of_lt h₁),
    ennreal.coe_to_nnreal ((lt_top_iff_ne_top.1 (lt_of_le_of_lt (sub_le_self _ _) h₁)))]

section to_borel_space

/- Move these back to borel_space.lean -/

variables {α : Type*} [linear_order α] [topological_space α] [ordered_topology α] {a b c : α}

lemma is_measurable_Ioc : is_measurable (Ioc a b) :=  (is_measurable_of_is_open (is_open_lt continuous_const continuous_id)).inter (is_measurable_of_is_closed (is_closed_le continuous_id continuous_const))

lemma is_measurable_Icc : is_measurable (Icc a b) := is_measurable_of_is_closed $ is_closed_Icc

lemma is_measurable_Ioi : is_measurable (Ioi a) := 
is_measurable_of_is_open $ is_open_lt continuous_const continuous_id


end to_borel_space

lemma Ioi_complement:
    ∀ x: nnreal, Ioi x = - (Iio x ∪ {x}) :=
begin
    intros,
    rw ext_iff, intro,
    unfold Ioi, unfold Iio, 
    simp,
    repeat {rw mem_set_of_eq}, 
    split; intro,
    {
        push_neg, split,
        {
            by_contradiction, simp at *,
            rw a_1 at a,
            have FOO: ¬ (x < x), simp, 
            contradiction,
        },
        {
            exact le_of_lt a,
        },
    },
    {
        push_neg at a,
        cases a,
        by_contradiction,
        have FOO: ¬ (x ≤ x_1), 
        {
            simp, simp at a, 
            exact lt_of_le_of_ne a a_left, 
        },
        contradiction,
    },
end

lemma Icc_diff_Ioc:
    ∀ a: nnreal, ∀ b: nnreal, ∀ c: nnreal,
    a ≤ b → b ≤ c → (Icc a c \ Icc a b) = Ioc b c :=
begin
    unfold Icc, unfold Ioc,
    introv H1 H2,
    rw ext_iff, intro,
    rw mem_diff,
    repeat {rw mem_set_of_eq at *,},
    split; intros,
    {
        cases a_1, cases a_1_left,
        finish,
    },
    {
        cases a_1,
        split,
        {
            split,
            {
                transitivity b,
                assumption,
                exact le_of_lt a_1_left,
            },
            {
                assumption,
            },
        },
        {
            simp, intro, assumption,
        },
    },
end

lemma mono_simple {μ: probability_measure nnreal}:
    ∀ a: nnreal, ∀ b: nnreal, a ≤ b → μ (Icc 0 a) ≤ μ (Icc 0 b) :=
begin
    intros,
    apply probability_measure.prob_mono,
    unfold Icc,
    rw subset_def, intros,
    rw mem_set_of_eq at *,
    cases a_2,
    split,
    assumption,
    transitivity a; assumption,
end

lemma log_le_log_nnreal:
    ∀ x: nnreal, ∀ y: nnreal, x > 0 → y > 0 → (x ≤ y ↔ log x ≤ log y) :=
begin
    intros,
    rw log_le_log,
    refl, assumption, assumption,
end

lemma log_pow_nnreal:
    ∀ x: nnreal, x > 0 → ∀ n: ℕ, log(x^n) = n * log(x) :=
begin
    intros,
    apply exp_injective,
    rw exp_nat_mul,
    rw exp_log,
    rw exp_log,
    assumption,
    exact pow_pos a n,
end

lemma pow_coe:
    ∀ a: nnreal, ∀ n: ℕ, a.val ^ n = (a ^ n).val :=
begin
    intros,
    induction n,
    simp, refl,
    have pow_nnreal: ∀ a: nnreal, ∀ n: ℕ, a ^ (nat.succ n) = a * a ^ n, intros, exact rfl,
    rw pow_nnreal,  
    have mul_coe: ∀ a: nnreal, ∀ b: nnreal, (a * b).val = a.val * b.val, intros, refl,
    rw mul_coe,
    rw ← n_ih,
    refl,
end

lemma sub_nnreal:
    ∀ a: nnreal, ∀ b: nnreal, a ≥ b → (a - b).val = a.val - b.val :=
begin
    intros a b h,
    change (↑(a-b) = ↑a - ↑b),
    rw nnreal.coe_sub _ _ h,
end

lemma ite_equals_union_interval:
    ∀ θ > 0, ∀ y: nnreal, {x: nnreal | ite (to_bool(x ≤ y)) x 0 < θ} = Ico 0 θ ∪ Ioi y :=
begin
    intros,
    unfold Ico, unfold Ioi,
    rw ext_iff, intro,
    rw mem_union,
    repeat {rw mem_set_of_eq}, 
    split; intro,
    {
        split_ifs at a,
        {
            left,
            split, tidy, 
        },
        {
            right, tidy,
        },
    },
    {
        cases a,
        {
            cases a,
            split_ifs; assumption,
        },
        {
            split_ifs,
            {
                by_contradiction,
                have GEQ: ¬ (y < x), 
                {
                    simp, simp at h, assumption,
                },
                contradiction,
            },
            {
                assumption,
            },
        },
    },    
end