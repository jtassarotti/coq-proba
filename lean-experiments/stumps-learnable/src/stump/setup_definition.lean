/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import measure_theory.measurable_space
import measure_theory.borel_space
import topology.instances.nnreal
import ..lib.basic
import ..lib.util

namespace stump

notation `ℍ` := nnreal

noncomputable
instance meas_ℍ: measurable_space ℍ :=
begin
    apply_instance,
end

noncomputable
instance topo_ℍ: topological_space ℍ :=
begin
    apply_instance,
end

noncomputable
instance meas_lbl: measurable_space (ℍ × bool) :=
begin
    apply_instance,
end

variables (μ: probability_measure ℍ) (target: ℍ) 

noncomputable
def rlt (x: nnreal) (y: nnreal) : bool := x < y 

noncomputable
def rle (x: nnreal) (y: nnreal) : bool := x ≤ y 

noncomputable 
def label (target: ℍ): ℍ → ℍ × bool :=
    λ x: ℍ, (x,rle x target)

def error_set (h: ℍ) := {x: ℍ | label h x ≠ label target x}

noncomputable
def error := λ h, μ (error_set h target)  

end stump

