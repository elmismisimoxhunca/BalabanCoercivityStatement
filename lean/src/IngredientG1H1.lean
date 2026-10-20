import Mathlib

/-!
# IngredientG1H1 -- `G`, `H`, `G₁`, `H₁` of CMP99b (3.122)-(3.129) from their printed laws

Printed (corpus/pages/CMP99b_p420.md, p421.md; render corpus/renders/CMP99b_p420-32.png, p421-33.png):
 (3.122) `G⁻¹ = Δ_π + D R D* + Q* a Q`;
 (3.126) `H B = G Q* (Q G Q*)⁻¹ B`;
 (3.128) `⟨A,G₁⁻¹A⟩ = ⟨A,Δ_π A⟩ − 2⟨H C_π^{(2)}(A), J⟩ + ‖R D* A‖² + a‖Q A‖²`;
 (3.129) `H₁ B = G₁ Q* (Q G₁ Q*)⁻¹ B`.
Note: (3.138) is NOT a recursion on a previous Δ_k; it is the Neumann series
`G₁ = G₀(I − (Δ'_π+Δ^{(2)}_π)G₀)⁻¹` (p.423) of the operator DEFINED by (3.128).

Generic over finite-dimensional real inner-product spaces `E` (fine bonds) and `F` (unit bonds).
`T` stands for `R D*` (so `D R D* = Tˢ T`).  The base data (Δ_π, T, Q, C_π^{(2)}, J, a) are inputs;
what is determined here is `G, H, G₁, H₁`.  No analytic estimate is claimed.
-/
set_option autoImplicit false
namespace AdalyFormal.IngredientFamily

open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Base data of (3.122)-(3.128). `Ts` is the adjoint of `T = R D*`. -/
structure BaseData (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  Dpi : E →L[ℝ] E
  T : E →L[ℝ] E
  Ts : E →L[ℝ] E
  Q : E →L[ℝ] F
  Qs : F →L[ℝ] E
  a : ℝ
  /-- `C^{(2)}`: the second-order averaging term, a function at unit bonds (`F`). -/
  C2 : E → F
  J : E
  T_adj : ∀ x y, ⟪T x, y⟫ = ⟪x, Ts y⟫
  Q_adj : ∀ x y, ⟪Q x, y⟫ = ⟪x, Qs y⟫

namespace BaseData
variable (D : BaseData E F)

/-- `G⁻¹` of (3.122). -/
noncomputable def Ginv : E →L[ℝ] E := D.Dpi + D.Ts.comp D.T + D.a • (D.Qs.comp D.Q)
noncomputable def G : E →L[ℝ] E := Ring.inverse D.Ginv
/-- `H` of (3.126). -/
noncomputable def H : F →L[ℝ] E :=
  (D.G.comp D.Qs).comp (Ring.inverse ((D.Q.comp D.G).comp D.Qs))

/-- The quadratic form on the right of (3.128). -/
noncomputable def K (A : E) : ℝ :=
  ⟪A, D.Dpi A⟫ - 2 * ⟪D.H (D.C2 A), D.J⟫ + ‖D.T A‖ ^ 2 + D.a * ‖D.Q A‖ ^ 2

/-- `G₁⁻¹` is the SYMMETRIC operator whose quadratic form is `K` (3.128). -/
structure IsG1inv (G1inv : E →L[ℝ] E) : Prop where
  symm : ∀ x y, ⟪G1inv x, y⟫ = ⟪x, G1inv y⟫
  form : ∀ A, ⟪A, G1inv A⟫ = D.K A

/-- Two symmetric operators with the same quadratic form coincide: the prover cannot choose `G₁`. -/
theorem symm_unique {S1 S2 : E →L[ℝ] E} (h1 : ∀ x y, ⟪S1 x, y⟫ = ⟪x, S1 y⟫)
    (h2 : ∀ x y, ⟪S2 x, y⟫ = ⟪x, S2 y⟫) (hf : ∀ A, ⟪A, S1 A⟫ = ⟪A, S2 A⟫) : S1 = S2 := by
  ext y
  set Dm : E →L[ℝ] E := S1 - S2 with hDm
  have hs : ∀ x y, ⟪Dm x, y⟫ = ⟪x, Dm y⟫ := fun x y => by
    simp only [hDm, ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, h1, h2]
  have hf0 : ∀ x, ⟪x, Dm x⟫ = 0 := fun x => by
    simp only [hDm, ContinuousLinearMap.sub_apply, inner_sub_right, hf, sub_self]
  have hpol : ∀ x y, ⟪x, Dm y⟫ = 0 := fun x y => by
    have h := hf0 (x + y)
    simp only [map_add, inner_add_left, inner_add_right, hf0] at h
    have := hs y x
    rw [real_inner_comm] at this
    linarith [real_inner_comm x (Dm y)]
  have : Dm y = 0 := by
    have := hpol (Dm y) y
    exact inner_self_eq_zero.mp this
  simpa [hDm, sub_eq_zero] using this

theorem G1inv_unique {A B : E →L[ℝ] E} (hA : D.IsG1inv A) (hB : D.IsG1inv B) : A = B :=
  symm_unique hA.symm hB.symm (fun x => by rw [hA.form, hB.form])

/-- `G₁` of (3.128). -/
noncomputable def G1 (_D : BaseData E F) (G1inv : E →L[ℝ] E) : E →L[ℝ] E := Ring.inverse G1inv
/-- `H₁` of (3.129). -/
noncomputable def H1 (G1inv : E →L[ℝ] E) : F →L[ℝ] E :=
  ((D.G1 G1inv).comp D.Qs).comp (Ring.inverse ((D.Q.comp (D.G1 G1inv)).comp D.Qs))

/-- FEASIBILITY of `H₁`: if `G₁⁻¹` is coercive (the smallness consequence of (3.130)-(3.138))
and `Q*` is injective, then `Q G₁ Q*` is invertible, so `H₁` is the genuine solution operator. -/
theorem QG1Qs_isUnit {G1inv : E →L[ℝ] E} (hG : D.IsG1inv G1inv) {c : ℝ} (hc : 0 < c)
    (hco : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, G1inv x⟫) (hQs : Function.Injective D.Qs) :
    IsUnit ((D.Q.comp (D.G1 G1inv)).comp D.Qs) := by
  have hinj : Function.Injective G1inv := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have := hco x
    rw [hx, inner_zero_right] at this
    have h0 : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
  have hbij : Function.Bijective G1inv :=
    (LinearMap.injective_iff_surjective (f := (G1inv : E →ₗ[ℝ] E))).mp hinj |> fun hs => ⟨hinj, hs⟩
  have hu : IsUnit G1inv := (ContinuousLinearMap.isUnit_iff_bijective).mpr hbij
  obtain ⟨u, hu'⟩ := hu
  have hG1 : D.G1 G1inv = ↑u⁻¹ := by
    rw [BaseData.G1, ← hu', Ring.inverse_unit]
  have hl : ∀ x, G1inv (D.G1 G1inv x) = x := fun x => by
    rw [hG1, ← hu']
    exact ContinuousLinearMap.ext_iff.mp u.mul_inv x
  have hsymG1 : ∀ x y, ⟪D.G1 G1inv x, y⟫ = ⟪x, D.G1 G1inv y⟫ := fun x y => by
    have := hG.symm (D.G1 G1inv x) (D.G1 G1inv y)
    rw [hl, hl] at this
    exact this.symm
  have hposG1 : ∀ x, x ≠ 0 → 0 < ⟪x, D.G1 G1inv x⟫ := fun x hx => by
    have hy : D.G1 G1inv x ≠ 0 := fun h => hx (by simpa [h] using (hl x).symm)
    have := hco (D.G1 G1inv x)
    rw [hl, real_inner_comm] at this
    have hpos : 0 < ‖D.G1 G1inv x‖ ^ 2 := by positivity
    nlinarith
  have hQinj : Function.Injective ((D.Q.comp (D.G1 G1inv)).comp D.Qs) := by
    rw [injective_iff_map_eq_zero]
    intro u hu0
    by_contra hne
    have hz : D.Qs u ≠ 0 := fun h => hne (hQs (by simpa using h))
    have h1 : ⟪u, ((D.Q.comp (D.G1 G1inv)).comp D.Qs) u⟫ = ⟪D.Qs u, D.G1 G1inv (D.Qs u)⟫ := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [real_inner_comm, D.Q_adj]
      exact hsymG1 _ _
    rw [hu0, inner_zero_right] at h1
    exact (ne_of_gt (hposG1 _ hz)) h1.symm
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hQinj, (LinearMap.injective_iff_surjective
      (f := (show F →ₗ[ℝ] F from (D.Q.comp (D.G1 G1inv)).comp D.Qs))).mp hQinj⟩

end BaseData

/-- L7 witness: the hypotheses of `QG1Qs_isUnit` are jointly satisfiable (E = F = ℝ, Δπ = id, rest 0/id). -/
noncomputable def toyData : BaseData ℝ ℝ where
  Dpi := 1
  T := 0
  Ts := 0
  Q := 1
  Qs := 1
  a := 0
  C2 := fun _ => 0
  J := 0
  T_adj := by intro x y; simp
  Q_adj := by intro x y; simp

theorem toy_isG1inv : toyData.IsG1inv (1 : ℝ →L[ℝ] ℝ) :=
  ⟨fun x y => by simp [real_inner_comm], fun A => by
    simp [BaseData.K, toyData]⟩

theorem toy_feasible : IsUnit ((toyData.Q.comp (toyData.G1 (1 : ℝ →L[ℝ] ℝ))).comp toyData.Qs) :=
  toyData.QG1Qs_isUnit toy_isG1inv (c := 1) one_pos
    (fun x => by simp [real_inner_self_eq_norm_sq]) (fun x y h => by simpa [toyData] using h)

#print axioms toy_feasible
#print axioms BaseData.G1inv_unique
#print axioms BaseData.QG1Qs_isUnit
#print axioms BaseData.H1
end AdalyFormal.IngredientFamily
