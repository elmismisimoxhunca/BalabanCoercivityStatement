import AdalyFormal.Balaban.CovariantOperators
import AdalyFormal.Balaban.SuTwoLogExpCore

/-!
# R2Coord -- explicit real coordinates `ℝ³ ≅ 𝔰𝔲(2)`

`toM2 (a,b,c) = [[ i a, b + i c ], [ −b + i c, −i a ]]`, `fromM2 X = (Im X₀₀, Re X₀₁, Im X₀₁)`.
Used to run all analysis (guards, subtypes) in an ordinary finite-dimensional real normed space
`X = Edge → ℝ³`, never in the `SuTwo`-subtype (whose normed structure clashes with the ambient
matrix norm; see ATTEMPTS C5).
-/
set_option autoImplicit false
namespace AdalyFormal.IngredientFamilyR2

open AdalyFormal.Balaban.CovariantOperators (suTwo mem_suTwo_iff SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2)

/-- `(a,b,c) ↦ [[i a, b + i c], [−b + i c, −i a]]`. -/
noncomputable def toM2 : (Fin 3 → ℝ) →ₗ[ℝ] M2 where
  toFun v := !![Complex.I * (v 0 : ℂ), (v 1 : ℂ) + Complex.I * (v 2 : ℂ);
                -(v 1 : ℂ) + Complex.I * (v 2 : ℂ), -(Complex.I * (v 0 : ℂ))]
  map_add' v w := by
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c v := by
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

/-- `X ↦ (Im X₀₀, Re X₀₁, Im X₀₁)`. -/
noncomputable def fromM2 : M2 →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun X := ![(X 0 0).im, (X 0 1).re, (X 0 1).im]
  map_add' X Y := by ext i; fin_cases i <;> simp
  map_smul' c X := by ext i; fin_cases i <;> simp

theorem fromM2_toM2 (v : Fin 3 → ℝ) : fromM2 (toM2 v) = v := by
  ext i; fin_cases i <;> simp [fromM2, toM2]

theorem toM2_mem (v : Fin 3 → ℝ) : toM2 v ∈ suTwo := by
  rw [mem_suTwo_iff]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [toM2, Matrix.conjTranspose_apply] <;> ring
  · simp [toM2, Matrix.trace_fin_two]

theorem toM2_fromM2 {X : M2} (hX : X ∈ suTwo) : toM2 (fromM2 X) = X := by
  rw [mem_suTwo_iff] at hX
  obtain ⟨h1, h2⟩ := hX
  have e00 := congrFun (congrFun h1 0) 0
  have e10 := congrFun (congrFun h1 1) 0
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at e00 e10
  rw [Matrix.trace_fin_two] at h2
  have r00 : (X 0 0).re = 0 := by
    have := congrArg Complex.re e00; simp at this; linarith
  have h11 : X 1 1 = -X 0 0 := by
    linear_combination h2
  have i10 : X 1 0 = -((X 0 1).re : ℂ) + Complex.I * ((X 0 1).im : ℂ) := by
    have hc : X 1 0 = -(starRingEnd ℂ) (X 0 1) := by
      have := e10; simp at this; linear_combination this
    rw [hc]
    apply Complex.ext <;> simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fromM2, toM2]
  · apply Complex.ext <;> simp [r00]
  · apply Complex.ext <;> simp
  · rw [i10]
  · rw [h11]; apply Complex.ext <;> simp [r00]

#print axioms toM2_fromM2
#print axioms toM2_mem
#print axioms fromM2_toM2

end AdalyFormal.IngredientFamilyR2
