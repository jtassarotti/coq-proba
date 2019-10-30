/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import topology.sequences
import .setup_definition

/-!
# `extend_to_epsilon`

This file proves a property of values of measures on intervals.

Given a (probability) measure μ on ℝ, for every ε > 0, given 
a real number t such that μ(0,t] > ε we exhibit a θ such 
that μ(0,t) > ε and μ(θ,t] ≤ ε. 

This is a largely technical lemma used in other parts of 
the stump proof. 

## Notations

This file uses the local notation `f ⟶ limit` for 
`tendsto f at_top (nhds limit)` for better readability of 
some proof states.

## Implementation notes

We prove this lemma for `μ` a  probability measure on the 
non-negative real numbers `nnreal`. Note, however that we do 
not use that `μ` is a probability measure anywhere,and this
theorem holds for an arbitrary measure on a conditionally
complete, linearly ordered topological space α with an 
orderable topology. 

## Tags

measure, intervals
-/


noncomputable theory 

local attribute [instance, priority 0] classical.prop_decidable

universe u 

open set lattice nnreal probability_measure filter nat measure_theory topological_space 


local notation f `⟶` limit := tendsto f at_top (nhds limit)

section stump 
variables (μ: probability_measure ℍ) (target: ℍ) (n: ℕ)

/-- `inc_seq_of x n` takes a sequence `x` and returns the
    `n`th maximum member. -/
noncomputable def inc_seq_of  (x : ℕ → nnreal) : ℕ → nnreal 
| 0 := x 0
| (nat.succ n) := max (x (nat.succ n)) (inc_seq_of n)


lemma inc_seq_increasing' (x : ℕ → nnreal) : ∀ n:ℕ, inc_seq_of x n ≤ inc_seq_of x (succ n) :=
begin
  intros n,
  induction n with k ih, 
  {simp [inc_seq_of], right, refl},
  {
    by_cases (inc_seq_of x k ≤ x (succ k)), 
    simp [inc_seq_of,h] at ih ⊢, cases ih,  
    right, refl, 
    simp [inc_seq_of,h] at ih ⊢, right,
    split, rw not_le at h, apply le_of_lt h, refl
  }  
end


lemma inc_seq_mono {x : ℕ → nnreal} : ∀ n m:ℕ, (n ≤ m) → inc_seq_of x n ≤ inc_seq_of x m :=
begin
  intros n m hnm,
  induction hnm with k, by refl, 
  {
    rw inc_seq_of,
    by_cases (inc_seq_of x k ≤ x (succ k)), 
    simp [h], refine le_trans hnm_ih h,
    simp [h], simp at h, right, assumption,
  }
end

lemma inc_seq_le_of_seq_le {x : ℕ → nnreal} {θ : nnreal} (hx : ∀ n, x n ≤ θ) : ∀ n, inc_seq_of x n ≤ θ :=
begin
    intros n , 
    induction n with k ih, by rw inc_seq_of;exact hx 0, 
    {
    rw inc_seq_of,  
    by_cases (inc_seq_of x k ≤ x (succ k)), 
    simp [h], exact hx _,
    simp [h], exact ⟨hx _, ih⟩,
    }  
end

lemma inc_seq_of_exists_index (x : ℕ → nnreal) : ∀ n : ℕ, ∃ k : ℕ, inc_seq_of x n = x k :=
begin 
    intros n,
    induction n with n₀ ih, by rw inc_seq_of; existsi 0; refl, 
    {
    rw inc_seq_of,
    by_cases (inc_seq_of x n₀ ≤ x (succ n₀)),
    simp [h], existsi (succ n₀), refl, 
    rw max, split_ifs, 
      exact ih, 
      existsi (succ n₀), refl,
    }
end

lemma inc_seq_of_exists_index' (x : ℕ → nnreal) : ∀ nₖ : ℕ, ∃ n : ℕ, (inc_seq_of x nₖ = x n) ∧ (n ≤ nₖ) :=
begin 
    intros n,
    induction n with n₀ ih, by rw inc_seq_of; existsi 0 ; exact ⟨rfl, by refl⟩, 
    {
    rw inc_seq_of,
    by_cases (inc_seq_of x n₀ ≤ x (succ n₀)),
      simp[h], existsi (succ n₀), exact ⟨rfl, by refl⟩, 
      rw max, split_ifs, choose k hk using ih,
      exact ⟨k, and.intro hk.left (le_succ_of_le hk.right)⟩,
      choose k hk using ih, existsi k, rw not_le at h_1, rw not_le at h, exfalso,
      have h₁ := lt_trans h h_1, have h₂ := lt_irrefl (x (succ n₀)), 
      exact h₂ h₁,
    }
end

lemma seq_le_inc_seq (x : ℕ → nnreal) : ∀ n, x n ≤ inc_seq_of x n :=
begin
    intros n,
    induction n with k ih, by refl,
    {
    rw inc_seq_of, 
    by_cases (inc_seq_of x k ≤ x (succ k)), 
      simp [h] ; refl,
      simp [h],left ; refl,
    },
end

/-- This theorem states that the sequence of maximums of a sequence
 (converging to a point greater than every member of the sequence) 
 also converges to the same limit. 
 The proof uses the sandwich theorem. -/
theorem tendsto_inc_seq_of_eq_tendsto (x : ℕ → nnreal) (θ : nnreal) (h : tendsto x at_top (nhds θ)) (hfs : ∀ n:ℕ, (x n) ≤ θ ): tendsto (inc_seq_of x) at_top (nhds θ) := 
begin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h (tendsto_const_nhds) _ _,
  rw mem_at_top_sets, dsimp, existsi 0, intros b _, exact (seq_le_inc_seq x b),
  rw mem_at_top_sets, dsimp, existsi 0, intros b _, exact inc_seq_le_of_seq_le hfs _,
end


lemma lim_le_of_seq_le {x : ℕ → ℍ} {θ y: nnreal} (lim : tendsto x at_top (nhds θ)) (hx : ∀ n, x n ≤ y) : θ ≤ y := 
begin
  refine le_of_tendsto at_top_ne_bot lim _,
  rw mem_at_top_sets, existsi 0, intros b _, exact hx _,
end

/-- Helper lemma for extend_to_epsilon proof. -/
lemma Ioc_eq_Union_IccB {θ target : nnreal} (h : θ < target):let y := λ n:ℕ, θ + (target - θ)/(n+1) in 
let B := λ n:ℕ, Icc (y n) target in
 Ioc (θ) target = ⋃ i:ℕ, B i :=
begin
  intros y B,
   have hB₁ : ∀ i, B i ⊆ B (succ i), 
   {
    assume i, dsimp [B],
    refine Icc_subset_Icc _ (by refl), dsimp [y], simp,
    rw nnreal.coe_le, rw nnreal.coe_div, rw nnreal.coe_div,
    rw (nnreal.coe_sub _ _ (le_of_lt h)), rw _root_.div_le_div_left, simp, exact zero_le_one,
    rwa [sub_pos,←nnreal.coe_lt], all_goals{simp}, 
    refine add_pos (zero_lt_one) (_), 
    repeat {exact add_pos_of_pos_of_nonneg (zero_lt_one) (by simp)},
  },
  ext z,
  rw mem_Union, dsimp [B,Ioc,Icc,y],
  fsplit, 
  assume H, 
  have pos₀ : 0 < target - θ, by rw [nnreal.coe_pos, nnreal.coe_sub _ _ (le_of_lt (lt_of_lt_of_le H.1 H.2)), sub_pos,←nnreal.coe_lt]; exact lt_of_lt_of_le H.1 H.2,
  let ε₀ := z - θ, 
  have pos₁ : (ε₀/(target - θ) : nnreal) > 0,
  {    
    rw nnreal.div_def, refine mul_pos _ _,
    simp [ε₀], 
    change (0 < z - θ), 
    rw [nnreal.coe_pos, nnreal.coe_sub, sub_pos,←nnreal.coe_lt], exact H.1, exact le_of_lt H.1,
    change (0 < (target - θ)⁻¹),
    rwa nnreal.inv_pos, 
  },
  have := nnreal.coe_pos.1 pos₁, replace := exists_nat_one_div_lt this,
  choose n hyp using this, existsi n, 
  refine ⟨ _ , H.2 ⟩,
  suffices : (target - θ)/(n+1) < ε₀,
  refine le_of_lt _, 
  convert (add_lt_add_left this θ),  
  rw [add_comm, sub_add_cancel_of_le (le_of_lt H.1)],
  rw nnreal.coe_div at hyp,
  simp [-add_comm] at hyp, rw nnreal.div_def,
  rw nnreal.coe_lt, rw nnreal.coe_mul,
  rw lt_div_iff at hyp, rw mul_comm, simpa [-add_comm], rwa ←nnreal.coe_pos,
  assume H', choose j hyp' using H', 
  refine ⟨ _ , hyp'.2 ⟩,
  replace hyp' := hyp'.1,
  suffices : 0 < (target - θ) / (↑j + 1) ,
  calc θ < θ + ((target - θ) / (↑j + 1)) : by rwa (lt_add_iff_pos_right _)
    ... ≤ z                             : hyp', 
  rw [nnreal.coe_pos, nnreal.coe_div], refine div_pos _ _,
  rwa [nnreal.coe_sub _ _ (le_of_lt h), sub_pos,←nnreal.coe_lt], simp, exact add_pos_of_pos_of_nonneg (zero_lt_one) (by simp)
end 

/-- Main theorem: given a (probability) measure μ on ℝ, 
for every ε > 0, given a real number t such that μ(0,t] > ε 
we exhibit a θ such that μ(0,t) > ε and μ(θ,t] ≤ ε. -/
theorem extend_to_epsilon_1:
∀ ε: nnreal, ε > 0 → 
μ (Ioc 0 target) > ε →
∃ θ: nnreal, μ (Icc θ target) ≥ ε ∧ μ (Ioc θ target) ≤ ε
 :=
begin
  intros ε h₁ h₂,
  let K :=  {x: ℍ | μ (Icc x target) ≥ ε},
  /- We hope to prove that the supremum of the above set is the required number. -/ 
  let θ :=  Sup K,
  existsi θ,
  /- The set K is non-empty since 0 ∈ K. -/
  have Kne : K ≠ ∅,  
  {
    assume not, have zeroK : (0:nnreal) ∈ K, 
    replace h₂ : μ (Ioc 0 target) ≥ ε, by exact le_of_lt h₂,
    simp [h₂], 
    suffices : μ (Icc 0 target) ≥ μ (Ioc 0 target), exact le_trans h₂ this, refine prob_mono _ _, rintros x ⟨hx₁,hx₂⟩, exact and.intro (le_of_lt hx₁) hx₂, finish,
  },
  /- The set K is bounded above as `target` is an upper-bound. -/
  have Kbdd : bdd_above K, 
  {
    existsi target, assume y yinK, dsimp at yinK,by_contradiction,  rw [Icc] at yinK,   
    suffices : μ {x : ℍ | y ≤ x ∧ x ≤ target} = 0, rw this at yinK, change (0 < ε) at h₁, rw ←not_le at h₁, exact h₁ yinK,
    suffices : {x : ℍ | y ≤ x ∧ x ≤ target} = ∅, rw this, exact prob_empty μ, 
    suffices : ∀ x : ℍ, ¬ (y ≤ x ∧ x ≤ target), simp [this],
    rintros _ ⟨hx₁,hx₂⟩, exact a (le_trans hx₁ hx₂)
  },
  /- Since K is non-empty and bounded above, it's supremum is contained in it's closure. -/
  have SupinClK : θ ∈ closure K, by exact cSup_mem_closure Kne Kbdd,
  /- Since the closure K is equal to the sequential closure, θ belongs to the sequential closure of K. -/
  have : θ ∈ sequential_closure K,
  {
    suffices : sequential_closure K = closure K, rwa this,  
    exact sequential_space.sequential_closure_eq_closure K,
  },
  /- Hence, there exists a sequence x in K converging to θ. -/
  have seq : ∃ x : ℕ → nnreal, (∀ n : ℕ, x n ∈ K) ∧ (tendsto x at_top (nhds θ)), by rw sequential_closure at this ; simpa [this], clear this,
  choose x hn using seq, rcases hn with ⟨h₁,lim⟩,
  /- Now, the interval [ θ , target ] is the infinite intersection of the intervals [ zₙ = max_{k ≤ n} xₖ , target]. Note that the maximums are ≤ θ since the sequence itself is ≤ θ. -/
  have Iccintereq : Icc θ target = (⋂ (n : ℕ), Icc (inc_seq_of x n) target),
  {
    ext y,
    rw mem_Inter, fsplit, 
    assume h i, dsimp [Icc] at h |-, rcases h with ⟨g₁,g₂⟩, 
    refine ⟨ _, g₂⟩, simp [θ] at g₁, rw cSup_le_iff Kbdd Kne at g₁, refine inc_seq_le_of_seq_le _ _, assume i, exact g₁ (x i) (h₁ i),
    assume h, dsimp [Icc] at h |-, 
    refine ⟨ _ , (h 0).2⟩, refine le_of_tendsto at_top_ne_bot lim _, rw mem_at_top_sets, dsimp, existsi 0, intros b _, exact le_trans (seq_le_inc_seq x b) ((h b).left),
  },
  /- Let s(n) denote the interval [zₙ , target]. -/
  let s := λ n, Icc (inc_seq_of x n) target,
  /- We have lim_{n → ∞} μ [zₙ, target] = μ ([θ, target]). Crucially, we use the fact that measures are continuous from above. -/
  have : tendsto (μ.to_measure ∘ s) at_top (nhds (μ.to_measure (⋂ (n : ℕ), s n))), 
  {
    refine tendsto_measure_Inter _ _ _,
    show ∀ (n : ℕ), is_measurable (s n), from assume n, is_measurable_of_is_closed is_closed_Icc,
    show ∀ (n m : ℕ), n ≤ m → s m ⊆ s n, from assume n m hnm, Icc_subset_Icc (inc_seq_mono _ _ hnm) (by refl),
    existsi 0, apply to_measure_lt_top,
  },
  /- From this the first conclusion follows, by using the fact that if aₙ⟶b and aₙ ≥ c then b ≥ c. -/
  have part₁ : μ (Icc θ target) ≥ ε,
  {
    rw ←Iccintereq at this,  
    change (ε ≤ μ (Icc θ target)),
    rw prob_apply, 
    rw ←ennreal.coe_le_coe, rw ennreal.coe_to_nnreal (to_measure_ne_top _ _),
    refine ge_of_tendsto (at_top_ne_bot) this _, clear this,
    rw mem_at_top_sets, dsimp, existsi 0, intros b hb, 
    dsimp [s], 
    have := inc_seq_of_exists_index x b,
    choose k₀ hk₀ using this, rw hk₀,
    replace h₁ := h₁ k₀,  
    rw ← coe_eq_to_measure, 
    rw ennreal.coe_le_coe, assumption,
    exact is_measurable_of_is_closed is_closed_Icc,
  }, 
  /- The remaining proof proceeds by casing on target ≤ θ.-/
  by_cases (target ≤ θ),
  /- If target ≤ θ then [θ,target] = ∅ and the conclusion follows. -/
  have Iocempty : Ioc θ target = ∅, from Ioc_eq_empty h, 
  exact ⟨part₁,by simp [Iocempty]⟩,
  /- If not, we define a sequence yₙ := {θ + (target - θ)/(n+1)}. -/ 
  simp at h,
  let y := λ n:ℕ, θ + (target - θ)/(n+1),
  /- Prove that θ < yₙ ≤ target. -/
  have hb : ∀ n, (θ < y n) ∧ (y n ≤ target), 
  {
    assume n, split, 
    dsimp [y], 
    suffices : 0 < target - θ,
    norm_num, rw nnreal.div_def, refine mul_pos this _, 
    apply nnreal.inv_pos.2, rw zero_lt_iff_ne_zero, simp,
    rw nnreal.coe_pos, rw nnreal.coe_sub, 
    rw sub_pos, rwa ←nnreal.coe_lt, exact le_of_lt h,
    dsimp [y],
    calc (θ + (target - θ) / (n + 1)) 
    = θ + (target - θ)*(n+1)⁻¹ :by rw ←nnreal.div_def
    ... ≤ θ + ((target - θ)*1) : by simp; exact mul_le_of_le_one_right (le_of_lt (by rwa [nnreal.coe_pos, nnreal.coe_sub, sub_pos,←nnreal.coe_lt];exact le_of_lt h)) (by rw [nnreal.inv_le,mul_one];repeat{simp})
    ... = θ + (target - θ)   : by rw mul_one
    ... = θ + target - θ : by rw [←nnreal.eq_iff,nnreal.coe_add, (nnreal.coe_sub _ _ (le_of_lt h))]; simp
    ... = target     : by rw nnreal.add_sub_cancel',
  },
  /- Prove that ∀ n, μ[yₙ, target] < ε. -/
  have ha : ∀ n, μ (Icc (y n) target) < ε,
  {
    by_contradiction, push_neg at a, choose n ha using a, 
    have yinK : (y n) ∈ K, from ha,
    have : y n ≤ θ, from le_cSup (Kbdd) yinK,
    exact (not_le.2 (hb n).left this),
  },
  let B := λ n:ℕ, Icc (y n) target,
  /- From a helper lemma above, we get that 
  (θ, target] = ⋃(n:ℕ),[yₙ,target]. -/
  have hB₂ : Ioc (θ) target = ⋃ i:ℕ, B i, from Ioc_eq_Union_IccB h,
  let s' := λ n, Icc (y n) target,
  /- Now we prove, using the fact that measures are continuous from below, that μ [yₙ, target] → μ (θ, target]. -/
  have : tendsto (μ.to_measure ∘ s') at_top (nhds (μ.to_measure (⋃ (n : ℕ), s' n))), 
  { 
    refine tendsto_measure_Union _ _,
    assume n, exact is_measurable_of_is_closed is_closed_Icc,
    unfold monotone, dsimp [s'],
    assume a b hab, refine Icc_subset_Icc _ (by refl),
    dsimp [y], rw add_le_add_iff_left,
    rw nnreal.div_def, rw nnreal.div_def, 
    refine mul_le_mul_of_nonneg_left _ (le_of_lt (by rwa [nnreal.coe_pos,nnreal.coe_sub _ _ (le_of_lt h), sub_pos,←nnreal.coe_lt])),
    rw nnreal.coe_le, simp, rw inv_le_inv _ _, simpa,
    repeat{exact add_pos_of_pos_of_nonneg (zero_lt_one) (by simp)},
  },
  /- Show the remaining conclusion. -/
  have part₂ : μ (Ioc θ target) ≤ ε,
  {
    rw ←hB₂ at this, rw [prob_apply, ←ennreal.coe_le_coe, ennreal.coe_to_nnreal (to_measure_ne_top _ _)],
    refine le_of_tendsto (at_top_ne_bot) this _, clear this,
    rw mem_at_top_sets, existsi 0, intros b hb, 
    dsimp [s'], 
    refine le_of_lt _ ,  
    rw ← coe_eq_to_measure, 
    rw ennreal.coe_lt_coe, exact (ha b),
    exact (is_measurable_of_is_open (is_open_lt continuous_const continuous_id)).inter (is_measurable_of_is_closed (is_closed_le continuous_id continuous_const)),
  }, 
  exact ⟨part₁,part₂⟩,
end

end stump 