import ZXR2Wire4

/-!
# R2Close0a -- flat-background positivity ingredients for the `k = 0` closed instance
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaPrimeCLMNormalized deltaPrimeOpNormalized
  deltaPrimeOpNormalized_eq_half_smul deltaPrimeOp_trivialU deltaKCLMNormalized)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM inner_dstarDCLM_eq_dstarDQuadForm)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm_nonneg dstarDQuadForm)
open AdalyFormal.Balaban.DeltaPrime (trivialU)

variable {L : PeriodicLatticeExtent}

theorem flatCfg_eq_trivialU : (flatCfg : PeriodicLinkConfiguration SU2 L) = trivialU (L := L) := rfl

theorem deltaPrimeCLMNormalized_flat :
    deltaPrimeCLMNormalized (flatCfg : PeriodicLinkConfiguration SU2 L) = 0 := by
  rw [flatCfg_eq_trivialU]
  ext1 y
  show deltaPrimeOpNormalized (trivialU (L := L)) y = 0
  rw [deltaPrimeOpNormalized_eq_half_smul, deltaPrimeOp_trivialU]
  simp

/-- `Δ = D*D + Δ'` (plaquette-localised to `plaqIn Ω₀`, r6) is positive semidefinite at the flat background (`Δ' = 0`). -/
theorem Delta_flat_nonneg (G : TowerGeom L) (y : BondFnL2 L) :
    0 ≤ ⟪y, Delta G (flatCfg : PeriodicLinkConfiguration SU2 L) y⟫ := by
  unfold Delta
  rw [flatCfg_eq_trivialU]
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_flat_nonneg _ _

theorem DpiFull_flat_nonneg (G : TowerGeom L) (a : ℝ) (x : BondFnL2 L) :
    0 ≤ ⟪x, DpiFull G (flatCfg : PeriodicLinkConfiguration SU2 L) a x⟫ := by
  unfold DpiFull
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  exact Delta_flat_nonneg G _

theorem Jf_flat (P : IngrBParams) (hU : P.U = flatCfg) : P.Jf = 0 := by
  unfold IngrBParams.Jf
  rw [hU]
  refine PiLp.ext (fun b => ?_)
  show -(AdalyFormal.IngredientFamily.JSU2Loc 1 (plaqIn P.G.Om0) flatCfg b) = 0
  rw [flatCfg_eq_trivialU, AdalyFormal.IngredientFamily.JSU2Loc_trivial, neg_zero]

#print axioms Delta_flat_nonneg
#print axioms Jf_flat

end AdalyFormal.IngredientFamilyR2
