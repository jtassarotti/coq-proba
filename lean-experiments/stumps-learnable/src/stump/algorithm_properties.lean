/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import .algorithm_definition
import .setup_properties

namespace stump

variables (μ: probability_measure ℍ) (target: ℍ) (n: ℕ)

lemma label_sample_correct_2:
    ∀ n, ∀ v: vec ℍ n, ∀ i: dfin (nat.succ n), (kth_projn (label_sample target n v) i).snd = tt  ↔ (kth_projn (label_sample target n v) i).fst ≤ target :=
begin
    intros,
    dunfold label_sample,
    rw ← kth_projn_map_comm,
    apply label_correct,
end

lemma filter_prop_1:
    ∀ n, ∀ v: vec ℍ n, ∀ i: dfin (nat.succ n), 
    kth_projn (filter n (label_sample target n v)) i ≤ target :=
begin
    intros,
    unfold filter,
    rw ← kth_projn_map_comm,
    by_cases ((kth_projn (label_sample target n v) i).snd = tt),
    {
        rw h,
        simp,
        have LBLCO := label_sample_correct_2 target n v i,
        cases LBLCO,
        apply LBLCO_mp,
        assumption,
    },
    {
        simp at h,
        rw h,
        simp,
    }
end 

lemma max_prop_1:
    ∀ n, ∀ v: vec ℍ n, ∀ i: dfin (nat.succ n), kth_projn v i ≤ max n v :=
begin
    intro,
    induction n; intros,
    {
        unfold max,
        cases i,
        tidy,
    },
    {
        cases v,
        unfold max, simp,
        cases i,
        {
            simp,
            by_cases (rlt (max n_n v_snd) v_fst = tt),
            {
                rw h,
                simp,
            },
            {
                simp at h,
                rw h,
                simp,
                unfold rlt at h,
                cases v_fst, simp at *, assumption,
            },
        },
        {
            have IH := n_ih v_snd i_a,
            simp,
            by_cases (rlt (max n_n v_snd) v_fst = tt),
            {
                rw h, 
                simp, unfold rlt at h,
                transitivity (max n_n v_snd),
                assumption, cases v_fst, simp at *, apply le_of_lt, assumption,
            },
            {   
                simp at h,
                rw h,
                simp,
                assumption,
            }
        }
    }
end

lemma max_prop_2:
    ∀ n, ∀ v: vec ℍ n, ∃ i: dfin (nat.succ n), kth_projn v i = max n v :=
begin
    intro,
    induction n; intros,
    {
        unfold max,
        cases v,
        existsi dfin.fz,
        simp,
    },{
        cases v,
        unfold max, simp,
        by_cases (rlt (max n_n v_snd) v_fst = tt),
        {
            rw h, simp,
            existsi dfin.fz,    
            simp, 
        },
        {
            have IND := n_ih v_snd,
            cases IND, clear n_ih,
            simp at h,
            rw h,
            simp,
            rw ← IND_h,
            existsi dfin.fs IND_w,
            simp,
        }
    }
end

lemma choose_property_1: 
    ∀ n: ℕ, ∀ S: vec ℍ n, choose n (label_sample target n S) ≤ target :=
begin
    intros,
    unfold choose, 
    have MP := max_prop_2 n (filter n (label_sample target n S)),
    cases MP,
    have FP := filter_prop_1 target n S MP_w,
    rw ← MP_h,
    assumption,
end

lemma choose_property_2:
    ∀ n: ℕ, ∀ S: vec ℍ n, 
    ∀ i: dfin (nat.succ n), 
    ∀ p = kth_projn (label_sample target n S) i,
    p.snd = tt → 
    p.fst ≤ choose n (label_sample target n S)  :=
begin
    intros,
    unfold choose,
    have MP := max_prop_1 n (filter n (label_sample target n S)) i,
    unfold filter at MP,
    rw ← kth_projn_map_comm at MP,
    rw ← H at MP,
    rw a at MP,
    simp at MP,
    assumption,
end

lemma choose_property_3:
    ∀ n: ℕ, ∀ S: vec ℍ n, 
    ∀ i: dfin (nat.succ n), 
    ∀ p = kth_projn (label_sample target n S) i,
    p.snd = tt → 
    p.fst ≤ target  :=
begin
    intros,
    transitivity (choose n (label_sample target n S)),
    apply choose_property_2; try {assumption},
    apply choose_property_1,
end

lemma choose_property_4:
    ∀ n: ℕ, ∀ S: vec ℍ n, 
    0 ≤ choose n (label_sample target n S) :=
begin
    intro,
    induction n,
    {
        intros, simp,
    },
    {
        intros, finish,
    },
end

end stump