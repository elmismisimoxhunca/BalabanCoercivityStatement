import R2Raw2

/-!
# R2Raw3 -- smoothness calculus for SU(2)-valued maps built from path holonomies
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AdalyFormal.IngredientFamilyR2

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.SmoothLog (su2Exp_coe_of_mem_suTwo)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : PeriodicLatticeExtent}

/-- `G : E → SU(2)` has analytic coercion at `0`. -/
def SG (G : E → SU2) : Prop := ContDiffAt ℝ ⊤ (fun A => ((G A : SU2) : M2)) 0

theorem SG.const (g : SU2) : SG (fun _ : E => g) := contDiffAt_const

theorem SG.mul {G H : E → SU2} (hG : SG G) (hH : SG H) : SG (fun A => G A * H A) :=
  ContDiffAt.mul hG hH

/-- conjugate transpose as an `ℝ`-continuous-linear map on `M₂(ℂ)`. -/
noncomputable def conjTR : M2 →L[ℝ] M2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Xᴴ
      map_add' := fun X Y => Matrix.conjTranspose_add X Y
      map_smul' := fun r X => by simp [Matrix.conjTranspose_smul] }

theorem conjTR_apply (X : M2) : conjTR X = Xᴴ := rfl

theorem SG.inv {G : E → SU2} (hG : SG G) : SG (fun A => (G A)⁻¹) := by
  have h : (fun A => (((G A)⁻¹ : SU2) : M2)) = fun A => conjTR ((G A : SU2) : M2) := by
    funext A; rfl
  unfold SG; rw [h]
  exact conjTR.contDiff.contDiffAt.comp (0 : E) hG

theorem SG.mul_inv {G H : E → SU2} (hG : SG G) (hH : SG H) : SG (fun A => G A * (H A)⁻¹) :=
  hG.mul hH.inv

/-- path holonomies of a family of configurations are analytic when each link is. -/
theorem SG.hol (s : ℕ) (V : E → PeriodicLinkConfiguration SU2 L)
    (hV : ∀ b, SG (fun A => V A b)) (p : List (Fin 3)) :
    ∀ y, SG (fun A => coarsePathHolonomy s (V A) y p) := by
  induction p with
  | nil => intro y; exact SG.const 1
  | cons μ rest ih =>
      intro y
      exact (hV (y, μ)).mul (ih _)

/-- `exp ∘ S` for an su(2)-valued analytic `S` gives an analytic SU(2)-valued map (guard transparent). -/
theorem SG_su2Exp {S : E → M2} (hS : ContDiffAt ℝ ⊤ S 0) (hah : ∀ A, (S A)ᴴ = -S A)
    (htr : ∀ A, Matrix.trace (S A) = 0) : SG (fun A => su2Exp (S A)) := by
  have h : (fun A => ((su2Exp (S A) : SU2) : M2)) = fun A => NormedSpace.exp (S A) := by
    funext A; exact su2Exp_coe_of_mem_suTwo (hah A) (htr A)
  unfold SG; rw [h]
  exact (NormedSpace.exp_analytic (S 0)).contDiffAt.comp (0 : E) hS

theorem su2Exp_one_of_zero {S : E → M2} (h0 : S 0 = 0) : su2Exp (S 0) = 1 := by
  rw [h0]; exact su2Exp_zero

/-- ℚ-smul by `((ell:ℚ)^3)⁻¹` is the real scalar multiplication by the same number. -/
theorem qsmul_real (q : ℚ) (X : M2) : q • X = (q : ℝ) • X := (Rat.cast_smul_eq_qsmul ℝ q X).symm

end AdalyFormal.IngredientFamilyR2
