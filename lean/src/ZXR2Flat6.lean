import ZR2Flat5
import ZXR2Unit1
import ZIngredientQ1

/-!
# R2Flat6 -- `Q1jet` at the flat background IS the printed `q1SU2` (CMP96 (2.125))
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.IngredientFamilyR2

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)

variable {L : PeriodicLatticeExtent}

theorem RegBg_flat (s ell : ℕ) : RegBg s ell (flatCfg : PeriodicLinkConfiguration SU2 L) := by
  intro c x _
  have : loopVar s ell (flatCfg : PeriodicLinkConfiguration SU2 L) c x = 1 := by
    unfold loopVar AdalyFormal.Balaban.UbarTowerCov.gammaVarStrided
      AdalyFormal.Balaban.UbarTowerCov.coarseBondVar
    rw [hol_flat, hol_flat, hol_flat, hol_flat]; simp
  rw [this]
  exact one_mem_LogReg

theorem QlinStepX_flat_apply (s ell : ℕ) (a : XS L) (e : PeriodicLatticeEdge L) :
    QlinStepX s ell flatCfg a e = fromM2 (Dtot s ell e a) := by
  have hc : ∀ e', HasFDerivAt (fun b : XS L => fromM2 (su2Log (rawStep s ell flatCfg (expCfgX b) e')))
      (fromM2L.comp (Dtot s ell e')) 0 := by
    intro e'
    exact fromM2L.hasFDerivAt.comp (0 : XS L)
      ((hasD1_rawStep_flat s ell e').log (SG_rawStep s ell flatCfg (RegBg_flat s ell) e'))
      |>.congr_fderiv rfl
  have hpi : HasFDerivAt (qStepX s ell flatCfg)
      (ContinuousLinearMap.pi (fun e' => fromM2L.comp (Dtot s ell e'))) 0 :=
    hasFDerivAt_pi.mpr (fun e' => hc e')
  have : QlinStepX s ell flatCfg = ContinuousLinearMap.pi (fun e' => fromM2L.comp (Dtot s ell e')) :=
    hpi.fderiv
  rw [this]
  rfl


theorem bondL_suCoordF (B : Bond L → SuTwo) (b : PeriodicLatticeEdge L) :
    bondL b (suCoordF B) = ((B b : SuTwo) : M2) := by
  show toM2 (fromM2 ((B b : SuTwo) : M2)) = _
  exact toM2_fromM2 (B b).2

/-- THE FLAT CROSS-CHECK, in the statement-lane's carrier: at the trivial background the printed
unit-level `Q₁` obtained as `L⁻¹ · D(raw map of (63))(0)` is EXACTLY the closed formula
`ell⁻⁴ Σ_{x∈B(c₋)} Σ_{i<ell} B(x+ie_μ,μ)` of CMP96 (2.125) (`q1SU2`). -/
theorem Q1jet_flat (ell : ℕ) (hell : 0 < ell) (hdvd : ∀ μ, ell ∣ (L μ + 1))
    (B : Bond L → SuTwo) (c : CoarseBond L ell) :
    Q1jet ell flatCfg B c = AdalyFormal.IngredientFamily.q1SU2 ell B c := by
  have he : (c.1.1, c.2).1 ∈ CoarseLattice L ell := c.1.2
  have hD := Dtot_flat_eq_printed ell hell hdvd (c.1.1, c.2) he
  -- the SuTwo element `S`
  set S : SuTwo := ∑ x ∈ blockOf c.1.1 ell, Wt ell • ∑ i ∈ Finset.range ell,
      B (pathSite x c.2 i, c.2) with hS
  have hDS : Dtot 1 ell (c.1.1, c.2) (suCoordF B) = ((S : SuTwo) : M2) := by
    rw [hD]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hS,
      Submodule.coe_sum, Submodule.coe_smul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact bondL_suCoordF B _
  apply Subtype.ext
  show ((ell : ℝ)⁻¹) • toM2 (QlinStepL 1 ell flatCfg (suCoordF B) (c.1.1, c.2)) = _
  rw [QlinStepL_eq_of_reg 1 ell flatCfg (RegBg_flat 1 ell), QlinStepX_flat_apply, hDS, toM2_fromM2 S.2]
  show ((ell : ℝ)⁻¹) • ((S : SuTwo) : M2) = ((1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf c.1.1 ell,
    ∑ i ∈ Finset.range ell, B (pathSite x c.2 i, c.2) : SuTwo)
  rw [hS]
  simp only [Submodule.coe_smul, Submodule.coe_sum, smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  unfold Wt
  field_simp

#print axioms Q1jet_flat

end AdalyFormal.IngredientFamilyR2
