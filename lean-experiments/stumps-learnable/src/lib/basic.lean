/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import lib.attributed.probability_theory
import lib.attributed.dvector lib.attributed.to_mathlib
import measure_theory.giry_monad
import measure_theory.measure_space
import data.complex.exponential

local attribute [instance] classical.prop_decidable

universes u v 

open nnreal measure_theory nat list measure_theory.measure to_integration probability_measure set dfin lattice ennreal

variables {α : Type u} {β : Type u} {γ : Type v}[measurable_space α]

infixl ` >>=ₐ `:55 := measure.bind 
infixl ` <$>ₐ `:55 := measure.map 

local notation `doₐ` binders ` ←ₐ ` m ` ; ` t:(scoped p, m >>=ₐ p) := t

local notation `ret` := measure.dirac  

lemma split_set {α β : Type u} (Pa : α → Prop) (Pb : β → Prop) : {m : α × β | Pa m.fst} = {x : α | Pa x}.prod univ := by ext1; cases x; dsimp at *; simp at *

instance has_zero_dfin {n} : has_zero $ dfin (n+1) := ⟨dfin.fz⟩

lemma vec.split_set {n : ℕ} (P : α → Prop) (μ : probability_measure α) :
{x : vec α (n+2)| P (kth_projn x 1)} = set.prod univ {x : vec α (n+1) | P (kth_projn x 0)} := 
begin
ext1, cases x, cases x_snd, dsimp at *, simp at *, refl,
end

lemma vec.prod_measure_univ' {n : ℕ} [nonempty α] [ne : ∀ n, nonempty (vec α n)](μ : probability_measure α) : (vec.prod_measure μ n : measure (vec α (n))) (univ) = 1
:=
by exact measure_univ _


noncomputable def vec.prob_measure (n : ℕ) [nonempty α] (μ : probability_measure α) : probability_measure (vec α n) :=
⟨ vec.prod_measure μ n , vec.prod_measure_univ' μ ⟩


lemma vec.prob_measure_apply (n : ℕ) [nonempty α] {μ : probability_measure α} {S : set (vec α n)} (hS : is_measurable S) : (vec.prob_measure n μ) S = ((vec.prod_measure μ n) S) := rfl

lemma measure_kth_projn' {n : ℕ} [nonempty α]  {P : α → Prop} (μ : probability_measure α) (hP : is_measurable {x : α | P x}) (hp' : is_measurable {x : vec α (n + 1) | P (kth_projn x 0)}) : 
(vec.prod_measure μ (n+2) : probability_measure (vec α (n+2))) {x : vec α (n + 2) | P (kth_projn x 1)} = μ {x : α | P x} := 
begin 
  rw vec.split_set _ μ,
  rw vec.prod_measure_eq, 
  rw prod.prob_measure_apply _ _ is_measurable.univ _, rw prob_univ,rw one_mul, 
  have h: {x : vec α (n + 1) | P (kth_projn x 0)} = {x : vec α (n + 1) | P (x.fst)}, {
    ext1, cases x, refl,
  },
  rw h, clear h,
  induction n with k ih, rw vec.prod_measure_eq,
  have h₁: {x : vec α (0 + 1) | P (x.fst)} = set.prod {x:α | P(x)} univ,by ext1; cases x; dsimp at *;simp at *,
  rw h₁, rw vec.prod_measure,rw prod.prob_measure_apply _ _ _ is_measurable.univ, rw prob_univ, rw mul_one, assumption,assumption, exact hP, 
  have h₂ : {x : vec α (succ k + 1) | P (x.fst)} = {x : vec α (k + 2) | P (x.fst)},by refl,
  rw h₂, clear h₂, 
  have h₃ : {x : vec α (k + 2) | P (x.fst)} = set.prod {x : α | P(x)} univ, {
    ext1, cases x, dsimp at *, simp at *,
  },
  rw h₃, rw vec.prod_measure_eq,rw prod.prob_measure_apply _ _ _ is_measurable.univ, rw prob_univ, rw mul_one, assumption, apply nonempty.vec, exact hP, assumption, apply nonempty.vec, assumption,
end


@[simp] lemma measure_kth_projn {n : ℕ} [nonempty α] {P : α → Prop} (μ : probability_measure α) (hP : is_measurable {x : α | P x}) (hp' : ∀ n i, is_measurable {x : vec α n | P (kth_projn x i)}) : ∀ (i : dfin (n+1)),
(vec.prod_measure μ n : probability_measure (vec α n)) {x : vec α n | P (kth_projn x i)} = μ {x : α | P x} :=
begin
  intros i,
  induction n with n b dk ih, rw vec.prod_measure,
  have g : {x : vec α 0 | P (kth_projn x i)} = {x | P x}, by tidy, rw g, refl, 
  have h: {x : vec α (n + 1) | P (kth_projn x fz)} = {x : vec α (n + 1) | P (x.fst)}, {
    ext1, cases x, refl,
  },
  cases i,
  rw h, clear h,
have h₃ : {x : vec α (n + 1) | P (x.fst)} = set.prod {x : α | P(x)} univ, {
    ext1, cases x, dsimp at *, simp at *,
  },
  rw h₃, rw vec.prod_measure_eq, rw prod.prob_measure_apply _ _ hP is_measurable.univ, rw prob_univ, rw mul_one, exact (nonempty.vec n), rw vec.prod_measure_eq,
  have h₄ : {x : vec α (succ n) | P (kth_projn x (fs i_a))} = set.prod univ {x : vec α n | P (kth_projn x i_a)}, {
    ext1, cases x, dsimp at *, simp at *,
  },
  rw h₄, rw prod.prob_measure_apply _ _ is_measurable.univ _, rw prob_univ, rw one_mul, rw b,
  assumption, exact (nonempty.vec n), 
  apply hp',
end


lemma dfin_succ_prop_iff_fst_and_rst {α : Type u} (P : α → Prop) {k : ℕ} (x : vec α (succ k)) : (∀ (i : dfin (succ k + 1)), P (kth_projn x i)) ↔ P (x.fst) ∧ ∀ (i : dfin (succ k)), P (kth_projn (x.snd) i) :=
begin
  fsplit, 
  intros h, split, have := h fz, have : kth_projn x 0 = x.fst, cases x, refl, rw ←this, assumption,
  intro i₀, cases x, have := h (fs i₀), rwa kth_projn at this, 
  intros g i₁, cases g with l r, cases i₁ with ifz ifs, have : kth_projn x fz = x.fst, cases x, refl, rw this, assumption,
  cases x, rw kth_projn, exact r i₁_a,  
end

 lemma independence {n : ℕ} [nonempty α] {P : α → Prop} (μ : probability_measure α) (hP : is_measurable {x : α | P x}) (hp' : ∀ n, is_measurable {x : vec α n | ∀ i, P (kth_projn x i)}) :  
 (vec.prod_measure μ n : probability_measure (vec α n)) {x : vec α n | ∀ (i : dfin (n + 1)), P (kth_projn x i)} = μ {x : α | P x} ^ (n+1) := 
 begin
  induction n with k ih, 
  simp only [nat.pow_zero, nat_zero_eq_zero],
  have g : {x : vec α 0 | ∀ i : dfin 1, P (kth_projn x i)} = {x | P x}, {
    ext1, dsimp at *, fsplit, intros a, exact (a fz), intros a i, assumption,
  },
  rw g, simp, refl, 
  have h₂ : {x : vec α (succ k) | ∀ (i : dfin (succ k + 1)), P (kth_projn x i)} = set.prod {x | P x} {x : vec α k | ∀ (i : dfin (succ k)), P (kth_projn x i)},{
    ext1, apply dfin_succ_prop_iff_fst_and_rst,
  },
  rw [h₂], 
  rw vec.prod_measure_eq, rw vec.prod_measure_apply _ _ hP (hp' k),rw ih,refl, 
end

@[simp] lemma prob_independence {n : ℕ} [nonempty α] {P : α → Prop} (μ : probability_measure α) (hP : is_measurable {x : α | P x}) (hp' : ∀ n, is_measurable {x : vec α n | ∀ i, P (kth_projn x i)}) :  
 (vec.prob_measure n μ : probability_measure (vec α n)) {x : vec α n | ∀ (i : dfin (succ n)), P (kth_projn x i)} = (μ {x : α | P x}) ^ (n+1) := 
 begin
  induction n with k ih, 
    simp only [nat.pow_zero, nat_zero_eq_zero], 
  have g : {x : vec α 0 | ∀ i : dfin 1, P (kth_projn x i)} = {x | P x}, {
    ext1, dsimp at *, fsplit, intros a, exact (a fz), intros a i, assumption,
  },
  rw g, rw vec.prob_measure, simp, refl, 
  have h₂ : {x : vec α (succ k) | ∀ (i : dfin (succ (succ k))), P (kth_projn x i)} = set.prod {x | P x} {x : vec α k | ∀ (i : dfin (succ k)), P (kth_projn x i)},{
    ext1, apply dfin_succ_prop_iff_fst_and_rst,
  },
  rw h₂,
  rw vec.prob_measure_apply _ _,
  rw [vec.prod_measure_eq], rw vec.prod_measure_apply _ _ hP, rw pow_succ', rw ←ih, rw mul_comm, rw vec.prob_measure_apply, exact hp' k, exact hp' k, exact is_measurable_set_prod hP (hp' k),
end

noncomputable def point_indicators {f h: α → bool} {n : ℕ} (hf : measurable f) (hh : measurable h) (i : dfin (succ n)) := χ ⟦{x : vec α n | h(kth_projn x i) ≠ f (kth_projn x i)}⟧ 

lemma integral_point_indicators {f h: α → bool} {n : ℕ} [ne : nonempty (vec α n)] (hf : measurable f) (hh : measurable h) (hA : ∀ n i, is_measurable ({x : vec α n | h(kth_projn x i) ≠ f (kth_projn x i)})) (μ : measure (vec α n)) :
∀ i : dfin (succ n), 
 (∫ χ ⟦{x : vec α n | h(kth_projn x i) ≠ f (kth_projn x i)}⟧ ðμ) = μ ({x : vec α n | h(kth_projn x i) ≠ f (kth_projn x i)}) := assume i, integral_char_fun μ (hA n i)


lemma finally {f h : α → bool} {n : ℕ} [nonempty α] (hf : measurable f) (hh : measurable h) (hA : ∀ n i, is_measurable ({x : vec α n | h(kth_projn x i) ≠ f (kth_projn x i)})) (hB : is_measurable {x : α | h x ≠ f x}) (μ : probability_measure α) : let η := (vec.prod_measure μ n).to_measure in 
∀ i, (∫ (χ ⟦{x : vec α n | h(kth_projn x i) ≠ f (kth_projn x i)}⟧) ðη) = μ.to_measure {x : α | h x ≠ f x} := 
begin
  intros η i₀, 
  rw [integral_point_indicators hf hh hA (vec.prod_measure μ n).to_measure i₀], rw ←coe_eq_to_measure, rw ←coe_eq_to_measure,
  rw measure_kth_projn μ hB, 
  intro n₀, apply hA, 
end


lemma integral_char_fun_finset_sum {f h : α → bool} {n : ℕ} [nonempty α] (hf : measurable f) (hh : measurable h) (hA : ∀ n i, is_measurable ({x : vec α n | h(kth_projn x i) ≠ f (kth_projn x i)})) (hB : is_measurable {x : α | h x ≠ f x}) (μ : probability_measure α) (m : finset(dfin (succ n))):
(∫finset.sum m (λ (i : dfin (succ n)), ⇑χ⟦{x : vec α n | h (kth_projn x i) ≠ f (kth_projn x i)}⟧)ð((vec.prod_measure μ n).to_measure)) = m.sum (λ i, ((vec.prod_measure μ n)) ({x : vec α n | h(kth_projn x i) ≠ f (kth_projn x i)})) := 
begin
  rw integral,
  refine finset.induction_on m _ _,
  { simp, erw lintegral_zero },
  { assume a s has ih, simp [has], erw [lintegral_add],
    erw simple_func.lintegral_eq_integral,unfold char_fun,
    erw simple_func.restrict_const_integral, dsimp, rw ←ih, rw one_mul, rw coe_eq_to_measure, refl, exact(hA n a), 
    exact measurable.comp (simple_func.measurable _) measurable_id,
    refine measurable.comp _ measurable_id, 
    refine finset.induction_on s _ _, 
      {simp, exact simple_func.measurable 0,},
      {intros a b c d, simp [c], apply measure_theory.measurable_add, exact simple_func.measurable _, exact d,}
  },
end


lemma integral_sum_dfin {f h : α → bool} {n : ℕ} [nonempty α] (hf : measurable f) (hh : measurable h) (hA : ∀ n i, is_measurable ({x : vec α n | h(kth_projn x i) ≠ f (kth_projn x i)})) (hB : is_measurable {x : α | h x ≠ f x}) (μ : probability_measure α) (m : finset(dfin (succ n))) : let η := (vec.prod_measure μ n) in 
(∫ m.sum (λ i, χ ⟦{x : vec α n | h(kth_projn x i) ≠ f (kth_projn x i)}⟧) ðη.to_measure )= m.sum (λ i, (μ.to_measure : measure α)  {x : α | h x ≠ f x}) := 
begin
  intros η,
  rw [integral_char_fun_finset_sum hf hh hA hB],   
  congr, funext, rw measure_kth_projn μ hB hA, rw coe_eq_to_measure,
end


lemma measure_sum_const {f h : α → bool} {n : ℕ} (hf : measurable f) (hh : measurable h) (m : finset (fin n)) (μ : probability_measure α) : 
m.sum (λ i, (μ : measure α)  {x : α | h x ≠ f x}) = (m.card : ℕ) * ((μ : measure α)  {x : α | h x ≠ f x}) :=
begin
  apply finset.induction_on m, simp,
  intros a b c d,
  simp [c], rw add_monoid.add_smul, rw [add_monoid.smul],  
  simp [monoid.pow], rw right_distrib, rw monoid.one_mul, rw ←d, 
  simp, 
end

namespace hoeffding
open complex real

noncomputable def exp_fun (f : α → ennreal) : α → ℝ := λ x, exp $ (f x).to_real 


local notation  `∫` f `𝒹`m := integral m.to_measure f 


lemma integral_char_rect [measurable_space α] [measurable_space β] [n₁ : nonempty α] [n₂ : nonempty β](μ : probability_measure α) (ν : probability_measure β)  {A : set α} {B : set β} (hA : is_measurable A) (hB : is_measurable B) :
(∫ χ ⟦ A.prod B ⟧ 𝒹(μ ⊗ₚ ν)) = (μ A) * (ν B) := 
begin
  haveI := (nonempty_prod.2 (and.intro n₁ n₂)),
  rw [integral_char_fun _ (is_measurable_set_prod hA hB),←coe_eq_to_measure, 
  (prod.prob_measure_apply _ _ hA hB)], simp, 
end


end hoeffding


