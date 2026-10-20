import R2Flat1

/-!
# R2Flat2 -- first-order calculus for SU(2)-valued maps with `G 0 = 1` (`HasD1`)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.IngredientFamilyR2

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.SmoothLog (su2Exp_coe_of_mem_suTwo exp_hasFDerivAt_zero fderiv_su2Log_comp
  su2Log_comp_contDiffAt)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `G : E → SU(2)` has value `1` at `0` and coercion differentiable at `0` with derivative `T`. -/
def HasD1 (G : E → SU2) (T : E →L[ℝ] M2) : Prop :=
  G 0 = 1 ∧ HasFDerivAt (fun a => ((G a : SU2) : M2)) T 0

theorem HasD1.const_one : HasD1 (fun _ : E => (1 : SU2)) 0 :=
  ⟨rfl, hasFDerivAt_const _ _⟩

theorem HasD1.mul {G H : E → SU2} {T U : E →L[ℝ] M2} (hG : HasD1 G T) (hH : HasD1 H U) :
    HasD1 (fun a => G a * H a) (T + U) := by
  refine ⟨by simp [hG.1, hH.1], ?_⟩
  have := hG.2.mul' hH.2
  refine this.congr_fderiv ?_
  ext h
  simp [hG.1, hH.1, add_comm]
  rfl

/-- the derivative of an SU(2)-valued map with `G 0 = 1` is anti-Hermitian. -/
theorem HasD1.antiHerm {G : E → SU2} {T : E →L[ℝ] M2} (hG : HasD1 G T) (h : E) :
    (T h)ᴴ = -T h := by
  have hc : HasFDerivAt (fun a => conjTR ((G a : SU2) : M2)) (conjTR.comp T) 0 :=
    conjTR.hasFDerivAt.comp (0 : E) hG.2 |>.congr_fderiv rfl
  have hprod := hG.2.mul' hc
  have hone : ((fun a => ((G a : SU2) : M2)) * (fun a => conjTR ((G a : SU2) : M2)))
      = fun _ => (1 : M2) := by
    funext a
    exact mul_star_self (G a)
  rw [hone] at hprod
  have huniq := hprod.unique (hasFDerivAt_const (1 : M2) (0 : E))
  have := congrArg (fun F : E →L[ℝ] M2 => F h) huniq
  have h2 : (T h)ᴴ + T h = 0 := by
    simp [hG.1, conjTR_apply, Matrix.conjTranspose_one, MulOpposite.op_one] at this
    exact this
  exact eq_neg_of_add_eq_zero_left h2

theorem HasD1.inv {G : E → SU2} {T : E →L[ℝ] M2} (hG : HasD1 G T) :
    HasD1 (fun a => (G a)⁻¹) (-T) := by
  refine ⟨by simp [hG.1], ?_⟩
  have hc : HasFDerivAt (fun a => conjTR ((G a : SU2) : M2)) (conjTR.comp T) 0 :=
    conjTR.hasFDerivAt.comp (0 : E) hG.2 |>.congr_fderiv rfl
  refine hc.congr_fderiv ?_
  ext1 h
  show (T h)ᴴ = -T h
  exact hG.antiHerm h


theorem hasD1_su2Exp {S : E → M2} {T : E →L[ℝ] M2} (hS : HasFDerivAt S T 0) (h0 : S 0 = 0)
    (hah : ∀ a, (S a)ᴴ = -S a) (htr : ∀ a, Matrix.trace (S a) = 0) :
    HasD1 (fun a => su2Exp (S a)) T := by
  refine ⟨by show su2Exp (S 0) = 1; rw [h0]; exact su2Exp_zero, ?_⟩
  have hc : (fun a => ((su2Exp (S a) : SU2) : M2)) = fun a => NormedSpace.exp (S a) := by
    funext a; exact su2Exp_coe_of_mem_suTwo (hah a) (htr a)
  rw [hc]
  have he : HasFDerivAt (NormedSpace.exp : M2 → M2)
      ((ContinuousLinearEquiv.refl ℝ M2 : M2 ≃L[ℝ] M2) : M2 →L[ℝ] M2) (S 0) := by
    rw [h0]; exact exp_hasFDerivAt_zero
  exact (he.comp (0 : E) hS).congr_fderiv (ContinuousLinearMap.id_comp _)

theorem HasD1.log {G : E → SU2} {T : E →L[ℝ] M2} (hG : HasD1 G T) (hSG : SG G) :
    HasFDerivAt (fun a => su2Log (G a)) T 0 := by
  have hd : DifferentiableAt ℝ (fun a => su2Log (G a)) 0 :=
    (su2Log_comp_contDiffAt G hSG hG.1).differentiableAt (by simp)
  have h1 := fderiv_su2Log_comp G hG.2.differentiableAt hG.1
  have h2 : fderiv ℝ (fun a => ((G a : SU2) : M2)) 0 = T := hG.2.fderiv
  have h3 : fderiv ℝ (fun a => su2Log (G a)) 0 = T := by rw [h1, h2]
  rw [← h3]
  exact hd.hasFDerivAt

#print axioms HasD1.log

end AdalyFormal.IngredientFamilyR2
