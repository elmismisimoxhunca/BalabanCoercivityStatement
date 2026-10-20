import ZXR2Ops3

/-!
# R2Ops4 -- laws of the assembled base data, printed identities, (3.22) minimiser, (3.138) series
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

/-- `Δ_π` symmetric and `C^{(2)}_π` a quadratic polynomial: both PROVED for the assembled data
(they are not fields of the structure). -/
theorem baseData_laws (G : TowerGeom L) (U : Cfg L) (a : ℝ) (S : BondSector G) (Jf : BondFnL2 L) :
    (baseData G U a S Jf).Laws := by
  refine ⟨fun x y => ?_, ?_⟩
  · show ⟪(pE G) ((DpiFull G U a) ((iE G) x)), y⟫ = ⟪x, (pE G) ((DpiFull G U a) ((iE G) y))⟫
    rw [pE_inner_left, pE_inner_right]
    exact DpiFull_symm G U a _ _
  · have h := S.C2_quad.comp_linear
      (((Wop G U a).comp (iE G) : ↥(bondSupp G) →L[ℝ] BondFnL2 L) : ↥(bondSupp G) →ₗ[ℝ] BondFnL2 L)
    exact h

/-- The printed `D R D*` of (3.122) restricted to `E₀`: `Ts ∘ T = P_{E₀} (D R D*) ι`. -/
theorem baseData_TsT (G : TowerGeom L) (U : Cfg L) (a : ℝ) (S : BondSector G) (Jf : BondFnL2 L) :
    (baseData G U a S Jf).Ts.comp (baseData G U a S Jf).T
      = (pE G).comp (((gradL2 U).comp ((Rproj G U).comp (gradAdj U))).comp (iE G)) := by
  show (ContinuousLinearMap.adjoint ((Tfull G U).comp (iE G))).comp ((Tfull G U).comp (iE G)) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint (Tfull G U)),
    Tfull_adj_comp]
  rfl

/-- (3.128), first line, with every term as printed. -/
theorem baseData_K (G : TowerGeom L) (U : Cfg L) (a : ℝ) (S : BondSector G) (Jf : BondFnL2 L)
    (A : ↥(bondSupp G)) :
    (baseData G U a S Jf).K A
      = ⟪iE G A, DpiFull G U a (iE G A)⟫
        - 2 * ⟪(baseData G U a S Jf).H (S.C2full (Wop G U a (iE G A))), pE G Jf⟫
        + ‖Rproj G U (gradAdj U (iE G A))‖ ^ 2
        + ∑ p : BIdx G, a * (G.ell : ℝ) ^ (p.1 : ℕ) * ‖S.Qfull (iE G A) p‖ ^ 2 := by
  unfold BaseDataS.K
  have h1 : ⟪A, (baseData G U a S Jf).Dpi A⟫ = ⟪iE G A, DpiFull G U a (iE G A)⟫ := by
    show ⟪A, (pE G) ((DpiFull G U a) ((iE G) A))⟫ = _
    rw [pE_inner_right]
  have h2 : ⟪A, (baseData G U a S Jf).Mass A⟫
      = ∑ p : BIdx G, a * (G.ell : ℝ) ^ (p.1 : ℕ) * ‖S.Qfull (iE G A) p‖ ^ 2 := by
    show ⟪A, (pE G) ((MassFull G a S) ((iE G) A))⟫ = _
    rw [pE_inner_right, inner_MassFull]
  rw [h1, h2]
  rfl

/-- (3.22): `R f = Δ_U λ₀` with `λ₀ ∈ N(Q')` a minimiser of `λ ↦ ‖f − Δ_U λ‖²` over `N(Q')`. -/
theorem Rproj_minimiser (G : TowerGeom L) (U : Cfg L) (f : SiteL2 L) :
    ∃ l0 ∈ NQp G U, Rproj G U f = lapDir G U l0 ∧
      ∀ l ∈ NQp G U, ‖f - lapDir G U l0‖ ≤ ‖f - lapDir G U l‖ := by
  have hmem : Rproj G U f ∈ RImage G U := Submodule.starProjection_apply_mem _ _
  obtain ⟨l0, hl0, hl0eq⟩ := Submodule.mem_map.mp hmem
  have hl0' : lapDir G U l0 = Rproj G U f := hl0eq
  refine ⟨l0, hl0, hl0'.symm, fun l hl => ?_⟩
  have hmem' : lapDir G U l ∈ RImage G U := Submodule.mem_map.mpr ⟨l, hl, rfl⟩
  have hperp : f - Rproj G U f ∈ (RImage G U)ᗮ := Submodule.sub_starProjection_mem_orthogonal f
  have hin : ⟪f - Rproj G U f, Rproj G U f - lapDir G U l⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (Submodule.sub_mem _ hmem hmem') hperp
  have hdec : f - lapDir G U l = (f - Rproj G U f) + (Rproj G U f - lapDir G U l) := by abel
  rw [hl0', hdec]
  have h := norm_add_sq_real (f - Rproj G U f) (Rproj G U f - lapDir G U l)
  rw [hin] at h
  have h2 : ‖f - Rproj G U f‖ ^ 2 ≤ ‖(f - Rproj G U f) + (Rproj G U f - lapDir G U l)‖ ^ 2 := by
    nlinarith [sq_nonneg ‖Rproj G U f - lapDir G U l‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

#print axioms baseData_laws
#print axioms baseData_TsT
#print axioms baseData_K
#print axioms Rproj_minimiser

end AdalyFormal.IngredientFamilyR2
