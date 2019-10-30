/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import .setup_definition

namespace stump

variables (target: ℍ) (n: ℕ)

noncomputable 
def label_sample := vec_map (label target)

def filter := vec_map (λ p: (ℍ × bool), if p.snd then p.fst else 0)

noncomputable
def max: Π n: ℕ, vec ℍ n → ℍ
| 0 := λ x: nnreal, x
| (nat.succ n) := λ p, let m := max n p.snd in if rlt m p.fst then p.fst else m 

noncomputable 
def choose (n: ℕ):vec (ℍ × bool) n → ℍ :=
    λ data: (vec (ℍ × bool) n), max n (filter n data) 

end stump