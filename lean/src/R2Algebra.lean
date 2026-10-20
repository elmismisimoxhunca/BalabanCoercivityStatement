import Mathlib

/-!
# R2Algebra -- generic Hilbert-space layer for the printed (3.122)-(3.129), (3.134)-(3.138)

Printed (corpus/renders/CMP99b_p420-32.png, p421-33.png; corpus/pages p422, p423):
 (3.122) `G⁻¹ = Δ_π + D R D* + Q* a Q`,   (3.126) `H B = G Q* (Q G Q*)⁻¹ B`,
 (3.128) `⟨A,G₁⁻¹A⟩ = ⟨A,Δ_π A⟩ − 2⟨H C_π^{(2)}(A), J⟩ + ‖R D* A‖² + a‖Q A‖²`,
 (3.129) `H₁ B = G₁ Q* (Q G₁ Q*)⁻¹ B`,   (3.134) `⟨A,Δ^{(2)}A⟩ = 2⟨H C^{(2)}(A),J⟩`,
 (3.138) `G₁ = G₀ (I − (Δ'_π+Δ^{(2)}_π) G₀)⁻¹ = Σ_n G₀((Δ'_π+Δ^{(2)}_π)G₀)^n`.

This generalises the r1 `IngredientFamily.BaseData` in ONE respect that matters: the gauge-fixing
term is `‖R D* A‖²` where `R D* A` is a function on SITES (R acts on `L²(Ω₀,𝔤)` of sites), so
`T = R D* : E → S` has a DIFFERENT target `S` from the bond space `E` (r1 typed `T : E →L E`).

Everything here is a theorem about abstract finite-dimensional real Hilbert spaces `E` (fine bonds),
`S` (sites), `F` (unit bonds); the concrete operators are assembled in `R2Ops.lean`.
-/
set_option autoImplicit false
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace

variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-! ## 1. A bilinear form determines a symmetric operator (Riesz) -/

/-- Operator representing a bilinear form: `⟪x, bilinOp β y⟫ = β x y`. -/
noncomputable def bilinOp (β : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => (InnerProductSpace.toDual ℝ E).symm
        (LinearMap.toContinuousLinearMap (β.flip y))
      map_add' := fun y z => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext x
        simp
      map_smul' := fun c y => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext x
        simp }

theorem inner_bilinOp (β : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) : ⟪x, bilinOp β y⟫ = β x y := by
  have h := (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E)
    (x := x) (y := LinearMap.toContinuousLinearMap (β.flip y)))
  simp only [bilinOp, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  rw [real_inner_comm, h]
  simp


/-! ## 2. Quadratic maps -/

/-- A map is a QUADRATIC map iff it is the diagonal of a bilinear map (a homogeneous polynomial of
degree 2).  This is the content of the printed "a quadratic polynomial in B". -/
def IsQuadMap {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (f : X → Y) : Prop :=
  ∃ β : X →ₗ[ℝ] X →ₗ[ℝ] Y, ∀ x, f x = β x x

theorem IsQuadMap.smul_sq {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    {f : X → Y} (h : IsQuadMap f) (c : ℝ) (x : X) : f (c • x) = c ^ 2 • f x := by
  obtain ⟨β, hβ⟩ := h
  rw [hβ, hβ]; simp [smul_smul, pow_two]

theorem IsQuadMap.comp_linear {X X' Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup X']
    [Module ℝ X'] [AddCommGroup Y] [Module ℝ Y] {f : X → Y} (h : IsQuadMap f) (l : X' →ₗ[ℝ] X) :
    IsQuadMap (f ∘ l) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨(β.compl₁₂ l l), fun x => ?_⟩
  simp [hβ]

theorem IsQuadMap.map_linear {X Y Y' : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y]
    [Module ℝ Y] [AddCommGroup Y'] [Module ℝ Y'] {f : X → Y} (h : IsQuadMap f) (l : Y →ₗ[ℝ] Y') :
    IsQuadMap (l ∘ f) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨LinearMap.compr₂ β l, fun x => ?_⟩
  simp [hβ]


/-- The symmetric operator of the symmetrisation of a bilinear form. -/
noncomputable def symmOp (β0 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →L[ℝ] E :=
  bilinOp ((1 / 2 : ℝ) • (β0 + β0.flip))

theorem symmOp_symm (β0 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) : ⟪symmOp β0 x, y⟫ = ⟪x, symmOp β0 y⟫ := by
  unfold symmOp
  rw [real_inner_comm y (bilinOp _ x), inner_bilinOp, inner_bilinOp]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
  ring

theorem inner_symmOp_diag (β0 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x : E) : ⟪x, symmOp β0 x⟫ = β0 x x := by
  unfold symmOp
  rw [inner_bilinOp]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
  ring

/-- Any bilinear form's DIAGONAL is the quadratic form of a SYMMETRIC operator. -/
theorem exists_symm_of_diag (β0 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    ∃ Sop : E →L[ℝ] E, (∀ x y, ⟪Sop x, y⟫ = ⟪x, Sop y⟫) ∧ ∀ x, ⟪x, Sop x⟫ = β0 x x :=
  ⟨symmOp β0, symmOp_symm β0, inner_symmOp_diag β0⟩

/-- Two symmetric operators with the same quadratic form coincide. -/
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

/-! ## 3. Base data and the printed operators -/

/-- Base data of (3.122)-(3.128).  `T = R D* : E → S` (sites), `Ts` its adjoint; `Q : E → F`,
`Qs` its adjoint; `C2 = C_π^{(2)}`; `J` the source. -/
structure BaseDataS (E S F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup S] [InnerProductSpace ℝ S] [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  Dpi : E →L[ℝ] E
  T : E →L[ℝ] S
  Ts : S →L[ℝ] E
  Q : E →L[ℝ] F
  Qs : F →L[ℝ] E
  /-- the mass operator `Q* a Q` of (3.16), given by its (symmetric) form. -/
  Mass : E →L[ℝ] E
  C2 : E → F
  J : E
  T_adj : ∀ x s, ⟪T x, s⟫ = ⟪x, Ts s⟫
  Q_adj : ∀ x y, ⟪Q x, y⟫ = ⟪x, Qs y⟫
  Mass_symm : ∀ x y, ⟪Mass x, y⟫ = ⟪x, Mass y⟫

namespace BaseDataS
variable (D : BaseDataS E S F)

/-- `G⁻¹ = Δ_π + D R D* + Q* a Q` (3.122); `D R D* = Ts ∘ T` since `R` is an orthogonal projection. -/
noncomputable def Ginv : E →L[ℝ] E := D.Dpi + D.Ts.comp D.T + D.Mass
/-- `G` (3.122)/(3.27). -/
noncomputable def G : E →L[ℝ] E := Ring.inverse D.Ginv
/-- `H = G Q* (Q G Q*)⁻¹` (3.126). -/
noncomputable def H : F →L[ℝ] E :=
  (D.G.comp D.Qs).comp (Ring.inverse ((D.Q.comp D.G).comp D.Qs))

/-- The right-hand side of (3.128). -/
noncomputable def K (A : E) : ℝ :=
  ⟪A, D.Dpi A⟫ - 2 * ⟪D.H (D.C2 A), D.J⟫ + ‖D.T A‖ ^ 2 + ⟪A, D.Mass A⟫

/-- `G₁⁻¹` is the SYMMETRIC operator whose quadratic form is `K` (3.128). -/
structure IsG1inv (G1inv : E →L[ℝ] E) : Prop where
  symm : ∀ x y, ⟪G1inv x, y⟫ = ⟪x, G1inv y⟫
  form : ∀ A, ⟪A, G1inv A⟫ = D.K A

/-- Laws the print forces on the base data (THEOREMS of the concrete assembly, not assumptions
there): `Δ_π` symmetric, `C^{(2)}_π` a quadratic polynomial. -/
structure Laws : Prop where
  Dpi_symm : ∀ x y, ⟪D.Dpi x, y⟫ = ⟪x, D.Dpi y⟫
  C2_quad : IsQuadMap D.C2

theorem inner_Ginv (A : E) :
    ⟪A, D.Ginv A⟫ = ⟪A, D.Dpi A⟫ + ‖D.T A‖ ^ 2 + ⟪A, D.Mass A⟫ := by
  simp only [Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, inner_add_right]
  rw [← D.T_adj, real_inner_self_eq_norm_sq]

/-- `K A = ⟨A, G⁻¹ A⟩ − 2⟨H C₂(A), J⟩`: (3.128) is (3.122) with the `Δ^{(2)}` correction. -/
theorem K_eq (A : E) : D.K A = ⟪A, D.Ginv A⟫ - 2 * ⟪D.H (D.C2 A), D.J⟫ := by
  rw [inner_Ginv, K]; ring

theorem Ginv_symm (hL : D.Laws) (x y : E) : ⟪D.Ginv x, y⟫ = ⟪x, D.Ginv y⟫ := by
  have h1 : ⟪D.Ts (D.T x), y⟫ = ⟪x, D.Ts (D.T y)⟫ := by
    rw [real_inner_comm y (D.Ts (D.T x)), ← D.T_adj y (D.T x), ← D.T_adj x (D.T y)]
    exact real_inner_comm _ _
  simp only [Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, inner_add_right, hL.Dpi_symm x y, h1, D.Mass_symm x y]

/-- EXISTENCE of `G₁⁻¹` (printed (3.128) defines `G₁⁻¹` as THE operator of this form): under the
structural laws `K` is the diagonal of a bilinear form, hence the form of a symmetric operator.
(r1 proved only uniqueness; with a non-quadratic `C2` the class is EMPTY, see `Controls`.) -/
theorem exists_G1inv (hL : D.Laws) : ∃ G1inv : E →L[ℝ] E, D.IsG1inv G1inv := by
  obtain ⟨β, hβ⟩ := hL.C2_quad
  let β0 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun x y => ⟪x, D.Dpi y⟫ - 2 * ⟪D.H (β x y), D.J⟫ + ⟪D.T x, D.T y⟫ + ⟪x, D.Mass y⟫)
    (fun x1 x2 y => by
      simp only [inner_add_left, map_add, LinearMap.add_apply, inner_add_right, mul_add]; ring)
    (fun c x y => by
      simp only [inner_smul_left, map_smul, LinearMap.smul_apply, inner_smul_right, mul_add]
      simp; ring)
    (fun x y1 y2 => by
      simp only [inner_add_left, map_add, LinearMap.add_apply, inner_add_right, mul_add]; ring)
    (fun c x y => by
      simp only [inner_smul_left, map_smul, LinearMap.smul_apply, inner_smul_right, mul_add]
      simp; ring)
  obtain ⟨Sop, hs, hf⟩ := exists_symm_of_diag β0
  refine ⟨Sop, ⟨hs, fun A => ?_⟩⟩
  rw [hf A]
  simp only [β0, LinearMap.mk₂_apply, K, hβ A, real_inner_self_eq_norm_sq]

theorem G1inv_unique {A B : E →L[ℝ] E} (hA : D.IsG1inv A) (hB : D.IsG1inv B) : A = B :=
  symm_unique hA.symm hB.symm (fun x => by rw [hA.form, hB.form])


/-! ## 4. `Δ^{(2)}` (3.134), its relation to `G₁⁻¹`, coercivity and invertibility of `Q G₁ Q*` -/

/-- The bilinear form behind (3.134): `2⟨H β(x,y), J⟩` for a bilinear `β` with `C2 x = β x x`. -/
noncomputable def delta2Bil (β : E →ₗ[ℝ] E →ₗ[ℝ] F) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => 2 * ⟪D.H (β x y), D.J⟫)
    (fun x1 x2 y => by simp only [map_add, LinearMap.add_apply, inner_add_left]; ring)
    (fun c x y => by simp [real_inner_smul_left]; ring)
    (fun x y1 y2 => by simp only [map_add, inner_add_left]; ring)
    (fun c x y => by simp [real_inner_smul_left]; ring)

/-- `Δ^{(2)}` of (3.134): the symmetric operator with `⟨A,Δ^{(2)}A⟩ = 2⟨H C₂(A), J⟩`. -/
noncomputable def Delta2 (hL : D.Laws) : E →L[ℝ] E := symmOp (D.delta2Bil hL.C2_quad.choose)

theorem Delta2_spec (hL : D.Laws) :
    (∀ x y, ⟪D.Delta2 hL x, y⟫ = ⟪x, D.Delta2 hL y⟫) ∧
      ∀ A, ⟪A, D.Delta2 hL A⟫ = 2 * ⟪D.H (D.C2 A), D.J⟫ := by
  refine ⟨symmOp_symm _, fun A => ?_⟩
  unfold Delta2
  rw [inner_symmOp_diag]
  simp [delta2Bil, hL.C2_quad.choose_spec A]

theorem isG1inv_sub (hL : D.Laws) : D.IsG1inv (D.Ginv - D.Delta2 hL) := by
  obtain ⟨hs2, hf2⟩ := D.Delta2_spec hL
  refine ⟨fun x y => ?_, fun A => ?_⟩
  · simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, D.Ginv_symm hL, hs2]
  · simp only [ContinuousLinearMap.sub_apply, inner_sub_right, hf2, D.K_eq]

/-- If `G⁻¹` is coercive with constant `c` and `‖Δ^{(2)}‖ ≤ ε < c`, then every `G₁⁻¹` is coercive
with constant `c − ε`.  `‖Δ^{(2)}‖ ≤ ε` IS the printed smallness (3.137) in operator-norm form. -/
theorem G1inv_coercive (hL : D.Laws) {G1inv : E →L[ℝ] E} (hG : D.IsG1inv G1inv) {c ε : ℝ}
    (hc : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, D.Ginv x⟫) (hε : ‖D.Delta2 hL‖ ≤ ε) :
    ∀ x, (c - ε) * ‖x‖ ^ 2 ≤ ⟪x, G1inv x⟫ := by
  intro x
  have hEq : G1inv = D.Ginv - D.Delta2 hL := D.G1inv_unique hG (D.isG1inv_sub hL)
  rw [hEq]
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right]
  have h1 := hc x
  have h2 : ⟪x, D.Delta2 hL x⟫ ≤ ε * ‖x‖ ^ 2 := by
    calc ⟪x, D.Delta2 hL x⟫ ≤ ‖x‖ * ‖D.Delta2 hL x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖D.Delta2 hL‖ * ‖x‖) := by
          gcongr; exact (D.Delta2 hL).le_opNorm x
      _ ≤ ‖x‖ * (ε * ‖x‖) := by gcongr
      _ = ε * ‖x‖ ^ 2 := by ring
  nlinarith

end BaseDataS

/-- GENERIC: for a symmetric coercive `M` and `Qs` injective with `⟪Q x,y⟫ = ⟪x,Qs y⟫`,
the operator `Q M⁻¹ Qs` is a unit. -/
theorem isUnit_Q_inv_Qs {M : E →L[ℝ] E} (hsym : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫) {c : ℝ} (hc : 0 < c)
    (hco : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, M x⟫) {Q : E →L[ℝ] F} {Qs : F →L[ℝ] E}
    (hQ : ∀ x y, ⟪Q x, y⟫ = ⟪x, Qs y⟫) (hQs : Function.Injective Qs) :
    IsUnit ((Q.comp (Ring.inverse M)).comp Qs) := by
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have := hco x
    rw [hx, inner_zero_right] at this
    have h0 : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
  have hbij : Function.Bijective M :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : E →ₗ[ℝ] E))).mp hinj⟩
  have hu : IsUnit M := (ContinuousLinearMap.isUnit_iff_bijective).mpr hbij
  obtain ⟨u, hu'⟩ := hu
  have hG1 : Ring.inverse M = ↑u⁻¹ := by rw [← hu', Ring.inverse_unit]
  have hl : ∀ x, M (Ring.inverse M x) = x := fun x => by
    rw [hG1, ← hu']
    exact ContinuousLinearMap.ext_iff.mp u.mul_inv x
  have hsymG1 : ∀ x y, ⟪Ring.inverse M x, y⟫ = ⟪x, Ring.inverse M y⟫ := fun x y => by
    have := hsym (Ring.inverse M x) (Ring.inverse M y)
    rw [hl, hl] at this
    exact this.symm
  have hposG1 : ∀ x, x ≠ 0 → 0 < ⟪x, Ring.inverse M x⟫ := fun x hx => by
    have hy : Ring.inverse M x ≠ 0 := fun h => hx (by simpa [h] using (hl x).symm)
    have := hco (Ring.inverse M x)
    rw [hl, real_inner_comm] at this
    have hpos : 0 < ‖Ring.inverse M x‖ ^ 2 := by positivity
    nlinarith
  have hQinj : Function.Injective ((Q.comp (Ring.inverse M)).comp Qs) := by
    rw [injective_iff_map_eq_zero]
    intro u hu0
    by_contra hne
    have hz : Qs u ≠ 0 := fun h => hne (hQs (by simpa using h))
    have h1 : ⟪u, ((Q.comp (Ring.inverse M)).comp Qs) u⟫
        = ⟪Qs u, Ring.inverse M (Qs u)⟫ := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [real_inner_comm, hQ]
      exact hsymG1 _ _
    rw [hu0, inner_zero_right] at h1
    exact (ne_of_gt (hposG1 _ hz)) h1.symm
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hQinj, (LinearMap.injective_iff_surjective
      (f := (show F →ₗ[ℝ] F from (Q.comp (Ring.inverse M)).comp Qs))).mp hQinj⟩

namespace BaseDataS
variable (D : BaseDataS E S F)

/-- `G₁` of (3.128) and `H₁` of (3.129). -/
noncomputable def G1 (_D : BaseDataS E S F) (G1inv : E →L[ℝ] E) : E →L[ℝ] E := Ring.inverse G1inv
noncomputable def H1 (G1inv : E →L[ℝ] E) : F →L[ℝ] E :=
  ((D.G1 G1inv).comp D.Qs).comp (Ring.inverse ((D.Q.comp (D.G1 G1inv)).comp D.Qs))

theorem QG1Qs_isUnit {G1inv : E →L[ℝ] E} (hG : D.IsG1inv G1inv) {c : ℝ} (hc : 0 < c)
    (hco : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, G1inv x⟫) (hQs : Function.Injective D.Qs) :
    IsUnit ((D.Q.comp (D.G1 G1inv)).comp D.Qs) :=
  isUnit_Q_inv_Qs hG.symm hc hco D.Q_adj hQs

/-- The unconditional-in-`U` chain: coercive `G⁻¹` and `‖Δ^{(2)}‖ < c` give an invertible
`Q G₁ Q*` (the print writes `(Q G₁ Q*)⁻¹`). -/
theorem QG1Qs_isUnit_of_small (hL : D.Laws) {G1inv : E →L[ℝ] E} (hG : D.IsG1inv G1inv)
    {c ε : ℝ} (hcε : ε < c) (hc : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, D.Ginv x⟫)
    (hε : ‖D.Delta2 hL‖ ≤ ε) (hQs : Function.Injective D.Qs) :
    IsUnit ((D.Q.comp (D.G1 G1inv)).comp D.Qs) :=
  D.QG1Qs_isUnit hG (sub_pos.mpr hcε) (D.G1inv_coercive hL hG hc hε) hQs

end BaseDataS

/-! ## 5. The Neumann series (3.130)/(3.138) -/

/-- `inverse (M − N) = Σ M⁻¹ (N M⁻¹)^n` whenever `M` is a unit and `‖N M⁻¹‖ < 1`:
the printed `G₁ = G₀ (I − (Δ'_π + Δ_π^{(2)}) G₀)⁻¹ = Σ_n G₀((Δ'_π+Δ_π^{(2)})G₀)^n` (3.138). -/
theorem inverse_sub_eq_tsum {M N : E →L[ℝ] E} (hM : IsUnit M)
    (hN : ‖N * Ring.inverse M‖ < 1) :
    Ring.inverse (M - N) = ∑' n : ℕ, Ring.inverse M * (N * Ring.inverse M) ^ n := by
  obtain ⟨u, rfl⟩ := hM
  have hMi : Ring.inverse (u : E →L[ℝ] E) = ↑u⁻¹ := Ring.inverse_unit u
  set X : E →L[ℝ] E := N * Ring.inverse (u : E →L[ℝ] E) with hX
  have hfac : (u : E →L[ℝ] E) - N = ↑(Units.oneSub X hN * u) := by
    rw [Units.val_mul, Units.val_oneSub, hX, hMi, sub_mul, one_mul, mul_assoc]
    have : (↑u⁻¹ : E →L[ℝ] E) * ↑u = 1 := u.inv_mul
    rw [this, mul_one]
  rw [hfac, Ring.inverse_unit, mul_inv_rev, Units.val_mul]
  have h2 : (↑(Units.oneSub X hN)⁻¹ : E →L[ℝ] E) = ∑' n : ℕ, X ^ n := by
    rw [← NormedRing.inverse_one_sub X hN, geom_series_eq_inverse X hN]
  rw [h2, ← hMi, (summable_geometric_of_norm_lt_one hN).tsum_mul_left]


/-! ## 6. Controls (must-fire AND must-not-fire) on `E = S = F = ℝ`

`toy C2 J`: `Δ_π = 0`, `T = 0`, `Q = Q* = 1`, `Mass = 1`, so `G⁻¹ = 1`, `G = 1`, `H = 1` and
`K A = −2 C2(A) J + A²`. -/

noncomputable def toy (C2 : ℝ → ℝ) (J : ℝ) : BaseDataS ℝ ℝ ℝ where
  Dpi := 0
  T := 0
  Ts := 0
  Q := 1
  Qs := 1
  Mass := 1
  C2 := C2
  J := J
  T_adj := by intro x s; simp
  Q_adj := by intro x y; simp
  Mass_symm := by intro x y; simp

theorem toy_Ginv (C2 : ℝ → ℝ) (J : ℝ) : (toy C2 J).Ginv = 1 := by
  ext x; simp [BaseDataS.Ginv, toy]

theorem toy_G (C2 : ℝ → ℝ) (J : ℝ) : (toy C2 J).G = 1 := by
  simp [BaseDataS.G, toy_Ginv]

theorem toy_H (C2 : ℝ → ℝ) (J : ℝ) : (toy C2 J).H = 1 := by
  unfold BaseDataS.H
  rw [toy_G]
  have h1 : (((1 : ℝ →L[ℝ] ℝ).comp (1 : ℝ →L[ℝ] ℝ)).comp (1 : ℝ →L[ℝ] ℝ)) = (1 : ℝ →L[ℝ] ℝ) := by ext; simp
  ext x
  simp only [toy, h1, Ring.inverse_one]

theorem toy_K (C2 : ℝ → ℝ) (J : ℝ) (A : ℝ) :
    (toy C2 J).K A = -2 * C2 A * J + A ^ 2 := by
  unfold BaseDataS.K
  rw [toy_H]
  simp [toy]
  ring

/-- MUST-NOT-FIRE: `C2 = x²`, `J = 1/4`: laws hold, `G₁⁻¹ = 1/2` exists, is coercive with
`c − ε = 1/2` (`‖Δ^{(2)}‖ = 1/2 < c = 1`), and `Q G₁ Q*` is a unit. -/
theorem toy_good_laws : (toy (fun x => x ^ 2) (1 / 4)).Laws := by
  refine ⟨fun x y => by simp [toy], ?_⟩
  refine ⟨LinearMap.mk₂ ℝ (fun x y => x * y) (by intros; ring) (by intros; simp; ring)
    (by intros; ring) (by intros; simp; ring), fun x => ?_⟩
  simp [toy, pow_two]

theorem toy_good_G1inv : (toy (fun x => x ^ 2) (1 / 4)).IsG1inv ((1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) := by
  refine ⟨fun x y => by simp [mul_comm, mul_left_comm], fun A => ?_⟩
  rw [toy_K]
  simp [real_inner_eq_re_inner]
  ring

theorem toy_good_unit : IsUnit (((toy (fun x => x ^ 2) (1 / 4)).Q.comp
    ((toy (fun x => x ^ 2) (1 / 4)).G1 ((1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)))).comp
    (toy (fun x => x ^ 2) (1 / 4)).Qs) := by
  refine (toy (fun x => x ^ 2) (1 / 4)).QG1Qs_isUnit toy_good_G1inv (c := 1 / 2) (by norm_num)
    (fun x => ?_) (fun x y h => by simpa [toy] using h)
  simp [real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖x‖]

/-- MUST-FIRE (non-quadratic `C2 = x³`): NO operator satisfies `IsG1inv`. -/
theorem toy_cubic_no_G1inv : ¬ ∃ G1inv : ℝ →L[ℝ] ℝ, (toy (fun x => x ^ 3) 1).IsG1inv G1inv := by
  rintro ⟨g, hg⟩
  have h1 := hg.form 1
  have h2 := hg.form 2
  rw [toy_K] at h1 h2
  have e1 : g 1 = g 1 * 1 := by ring
  have e2 : g 2 = 2 * g 1 := by
    have := g.map_smul (2 : ℝ) 1
    simpa using this
  simp at h1 h2
  nlinarith

theorem toy_cubic_not_laws : ¬ (toy (fun x => x ^ 3) 1).Laws := fun h => by
  obtain ⟨G1inv, hG⟩ := (toy (fun x => x ^ 3) 1).exists_G1inv h
  exact toy_cubic_no_G1inv ⟨G1inv, hG⟩

/-- MUST-FIRE (sign flip `+2⟨HC2,J⟩` instead of `−`): the printed operator `1/2` does NOT satisfy
the sign-flipped form `3/2`, and neither does `G⁻¹ = 1` (dropped `C2` term). -/
theorem toy_good_not_signflip : ¬ (toy (fun x => x ^ 2) (1 / 4)).IsG1inv ((3 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) := by
  intro h
  have := h.form 1
  rw [toy_K] at this
  simp at this
  try norm_num at this

theorem toy_good_not_dropC2 : ¬ (toy (fun x => x ^ 2) (1 / 4)).IsG1inv (1 : ℝ →L[ℝ] ℝ) := by
  intro h
  have := h.form 1
  rw [toy_K] at this
  simp at this
  try norm_num at this

/-- MUST-FIRE (coercivity fails when `Δ^{(2)}` is not small): `J = 1`, `C2 = x²` gives
`G₁⁻¹ = −1`, not coercive. -/
theorem toy_big_not_coercive : ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, c * ‖x‖ ^ 2 ≤
    ⟪x, ((-1 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) x⟫ := by
  rintro ⟨c, hc, h⟩
  have := h 1
  simp at this
  linarith


#print axioms bilinOp
#print axioms inner_bilinOp
#print axioms exists_symm_of_diag
#print axioms symm_unique
#print axioms BaseDataS.exists_G1inv
#print axioms BaseDataS.G1inv_unique
#print axioms BaseDataS.Delta2_spec
#print axioms BaseDataS.isG1inv_sub
#print axioms BaseDataS.G1inv_coercive
#print axioms isUnit_Q_inv_Qs
#print axioms BaseDataS.QG1Qs_isUnit
#print axioms BaseDataS.QG1Qs_isUnit_of_small
#print axioms inverse_sub_eq_tsum
#print axioms toy_good_laws
#print axioms toy_good_G1inv
#print axioms toy_good_unit
#print axioms toy_cubic_no_G1inv
#print axioms toy_cubic_not_laws
#print axioms toy_good_not_signflip
#print axioms toy_good_not_dropC2
#print axioms toy_big_not_coercive

end AdalyFormal.IngredientFamilyR2
