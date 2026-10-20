/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantOperators
import AdalyFormal.Balaban.SuTwoInner

set_option autoImplicit false
set_option maxRecDepth 4000

/-!
Slim-tree relocation (2026-10-16, coordinator authorisation (a), see
`compute/slim_tree_20261016/NOTES.md`): the declarations `norm_RMap`, `inner_suTwoWitness_self`, `norm_suTwoWitness_sq` below are copied VERBATIM from
`Balaban/FaithfulCoercivitySU2.lean` (same fully qualified name
`AdalyFormal.Balaban.FaithfulCoercivitySU2.norm_RMap`), so that a module needing only `norm_RMap`
need not import a module that contains `sorry`.
-/

namespace AdalyFormal.Balaban.FaithfulCoercivitySU2

open AdalyFormal.Balaban.SuTwoInner (inner_eq_trace)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitnessVal RMap)
open AdalyFormal.Balaban.SuTwoInner (inner_RMap)

/-- **`RMap` preserves norms** — a direct corollary of `SuTwoInner.inner_RMap` (`RMap` is
ALREADY proved an isometry there; this file derives the norm-level statement it needs). -/
theorem norm_RMap (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    ‖RMap g X‖ = ‖X‖ := by
  have h : (inner ℝ (RMap g X) (RMap g X) : ℝ) = inner ℝ X X := inner_RMap g X X
  have h1 : ‖RMap g X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]; exact h
  have hsq := congrArg Real.sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsq

/-- `⟪w,w⟫ = 1` for `w = suTwoWitness = i·diag(1,−1)`: `−(1/2)·Re tr(w²) = −(1/2)·(−2)`. This
NORMALIZATION (Bałaban's `𝔰𝔲(2)` inner product as `SuTwoInner.inner_eq_trace` ships it) is what
turns the abstract bounds of §2 into the numerals `baseG = 2`, `|κ| ≤ 1`. -/
theorem inner_suTwoWitness_self : (inner ℝ (suTwoWitness : SuTwo) suTwoWitness : ℝ) = 1 := by
  rw [inner_eq_trace]
  show -(1 / 2 : ℝ) * (Matrix.trace (suTwoWitnessVal * suTwoWitnessVal)).re = 1
  norm_num [suTwoWitnessVal, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply,
    Complex.ext_iff]

theorem norm_suTwoWitness_sq : ‖(suTwoWitness : SuTwo)‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq]; exact inner_suTwoWitness_self

end AdalyFormal.Balaban.FaithfulCoercivitySU2
