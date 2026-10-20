import ZR3A3

/-!
# R3B -- the abstract identity behind `goodFam`'s form, and the coercivity `‖v‖² ≤ form v`.

For `G₁⁻¹ = 1 + Q*Q` (goodBase: `Δ_π = id`, `T = 0`, `a = 1`) and `S = Q G₁ Q*` invertible:
  `⟨v, S⁻¹ v⟩ = ‖x‖² + ‖Q x‖²`  where `x = G₁ Q* S⁻¹ v`, `Q x = v`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane3

open scoped RealInnerProductSpace

section core
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem Ginv_unit (Q : E →L[ℝ] F) :
    IsUnit ((1 : E →L[ℝ] E) + (ContinuousLinearMap.adjoint Q).comp Q) := by
  have hinj : Function.Injective ((1 : E →L[ℝ] E) + (ContinuousLinearMap.adjoint Q).comp Q) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : ⟪x, ((1 : E →L[ℝ] E) + (ContinuousLinearMap.adjoint Q).comp Q) x⟫ = 0 := by
      rw [hx, inner_zero_right]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.comp_apply, inner_add_right] at h1
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq] at h1
    have h2 : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖Q x‖]
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp h2)
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective
      (f := (show E →ₗ[ℝ] E from (1 : E →L[ℝ] E) + (ContinuousLinearMap.adjoint Q).comp Q))).mp hinj⟩

theorem form_core (Q : E →L[ℝ] F)
    (hS : IsUnit ((Q.comp (Ring.inverse ((1 : E →L[ℝ] E) + (ContinuousLinearMap.adjoint Q).comp Q))).comp
      (ContinuousLinearMap.adjoint Q))) (v : F) :
    ∃ x : E, Q x = v ∧
      ⟪v, Ring.inverse ((Q.comp (Ring.inverse ((1 : E →L[ℝ] E) +
        (ContinuousLinearMap.adjoint Q).comp Q))).comp (ContinuousLinearMap.adjoint Q)) v⟫
        = ‖x‖ ^ 2 + ‖v‖ ^ 2 := by
  set Ginv : E →L[ℝ] E := (1 : E →L[ℝ] E) + (ContinuousLinearMap.adjoint Q).comp Q with hGinv
  set S := (Q.comp (Ring.inverse Ginv)).comp (ContinuousLinearMap.adjoint Q) with hSdef
  obtain ⟨u, hu⟩ := Ginv_unit Q
  have hG1 : Ring.inverse Ginv = ↑u⁻¹ := by rw [← hGinv] at hu; rw [← hu, Ring.inverse_unit]
  have hr : ∀ y, Ginv (Ring.inverse Ginv y) = y := fun y => by
    have hu' : Ginv = ↑u := hu.symm
    rw [hG1, hu']; exact ContinuousLinearMap.ext_iff.mp u.mul_inv y
  set w := Ring.inverse S v with hw
  have hSw : S w = v := by
    have := Ring.mul_inverse_cancel S hS
    have h2 := ContinuousLinearMap.ext_iff.mp this v
    simpa [hw, ContinuousLinearMap.mul_def] using h2
  refine ⟨Ring.inverse Ginv (ContinuousLinearMap.adjoint Q w), ?_, ?_⟩
  · rw [← hSw]; rfl
  · set x := Ring.inverse Ginv (ContinuousLinearMap.adjoint Q w) with hx
    have hQx : Q x = v := by rw [← hSw]; rfl
    have hGx : Ginv x = ContinuousLinearMap.adjoint Q w := hr _
    have h1 : ⟪v, w⟫ = ⟪x, Ginv x⟫ := by
      rw [hGx, ← hQx, ContinuousLinearMap.adjoint_inner_right]
    rw [h1, hGinv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.comp_apply, inner_add_right]
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, hQx]

/-- the coercive consequence: if `‖Q x‖ ≤ ‖x‖` then `⟨v,S⁻¹v⟩ − ⟨v,v⟩ ≥ ‖v‖²` -/
theorem form_core_coercive (Q : E →L[ℝ] F) (hQ : ∀ x, ‖Q x‖ ≤ ‖x‖)
    (hS : IsUnit ((Q.comp (Ring.inverse ((1 : E →L[ℝ] E) + (ContinuousLinearMap.adjoint Q).comp Q))).comp
      (ContinuousLinearMap.adjoint Q))) (v : F) :
    ‖v‖ ^ 2 ≤ ⟪v, Ring.inverse ((Q.comp (Ring.inverse ((1 : E →L[ℝ] E) +
        (ContinuousLinearMap.adjoint Q).comp Q))).comp (ContinuousLinearMap.adjoint Q)) v⟫
        - ⟪v, v⟫ := by
  obtain ⟨x, hx, h⟩ := form_core Q hS v
  rw [h, real_inner_self_eq_norm_sq]
  have := hQ x
  rw [hx] at this
  nlinarith [norm_nonneg v, norm_nonneg x]

end core

#print axioms Ginv_unit
#print axioms form_core
#print axioms form_core_coercive

end AdalyFormal.StatementLane3
