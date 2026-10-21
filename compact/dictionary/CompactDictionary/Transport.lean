import CompactDictionary.Coordinates
import CompactDictionary.Padding

/-! Hilbert-operator transport, including total ring inverses and projections. -/
set_option autoImplicit false
namespace CompactDictionary
open scoped RealInnerProductSpace
noncomputable section

section Inverse
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Conjugacy reflects units, so this also transports the zero off-unit branch. -/
theorem inverse_conjugacy (e : E ≃L[ℝ] F) (A : E →L[ℝ] E) (B : F →L[ℝ] F)
    (h : ∀ x, e (A x) = B (e x)) (x : E) :
    e (Ring.inverse A x) = Ring.inverse B (e x) := by
  have he : e.conjContinuousAlgEquiv A = B := by
    ext y
    change e (A (e.symm y)) = B y
    simpa using h (e.symm y)
  have hi := inverse_ringEquiv e.conjContinuousAlgEquiv.toRingEquiv A
  rw [show e.conjContinuousAlgEquiv.toRingEquiv A = B from he] at hi
  have hx := congrArg (fun T : F →L[ℝ] F => T (e x)) hi
  change Ring.inverse B (e x) = e (Ring.inverse A (e.symm (e x))) at hx
  simpa only [e.symm_apply_apply] using hx.symm
end Inverse

section Hilbert
variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem adjoint_conjugacy (e : E ≃ₗᵢ[ℝ] F) (t : G ≃ₗᵢ[ℝ] H)
    (A : E →L[ℝ] G) (B : F →L[ℝ] H) (h : ∀ x, t (A x) = B (e x)) (y : G) :
    e (ContinuousLinearMap.adjoint A y) = ContinuousLinearMap.adjoint B (t y) := by
  apply ext_inner_left ℝ
  intro z
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [e.inner_map_map, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right, ← h, t.inner_map_map]

/-- Transport symmetric operators by their diagonal, without choosing a Riesz inverse. -/
theorem symmetric_conjugacy [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (A : E →L[ℝ] E) (B : F →L[ℝ] F)
    (hA : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hB : ∀ x y, ⟪B x, y⟫ = ⟪x, B y⟫)
    (hd : ∀ x, ⟪x, A x⟫ = ⟪e x, B (e x)⟫) (x : E) : e (A x) = B (e x) := by
  have hb : ∀ u v, ⟪u, A v⟫ = ⟪e u, B (e v)⟫ := by
    intro u v
    have h := hd (u + v)
    simp only [map_add, inner_add_left, inner_add_right] at h
    have ha : ⟪v, A u⟫ = ⟪u, A v⟫ := (real_inner_comm _ _).trans (hA u v)
    have hb : ⟪e v, B (e u)⟫ = ⟪e u, B (e v)⟫ := (real_inner_comm _ _).trans (hB _ _)
    rw [ha, hb, ← hd u, ← hd v] at h
    linarith
  apply ext_inner_left ℝ
  intro z
  obtain ⟨y, rfl⟩ := e.surjective z
  rw [e.inner_map_map, hb]

theorem projection_conjugacy (e : E ≃ₗᵢ[ℝ] F)
    (S : Submodule ℝ E) (T : Submodule ℝ F)
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]
    (h : ∀ x, e x ∈ T ↔ x ∈ S) (x : E) :
    e (S.starProjection x) = T.starProjection (e x) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (h _).mpr (Submodule.starProjection_apply_mem S x)
  · intro y hy
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← e.map_sub, e.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero x z ((h z).mp hy)
end Hilbert
end
end CompactDictionary
