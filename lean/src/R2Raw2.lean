import R2Raw1
import SmoothLog
import SmoothLogJet2
import AdalyFormal.Balaban.CovariantOperators
import AdalyFormal.Balaban.SuTwoInner

/-!
# R2Raw2 -- smoothness of the raw one-step averaging at SU(2) (regular background)

`LogReg`: the open set of `g ∈ M₂(ℂ)` near which the principal `su2Log` on `SU(2)` coincides with the
analytic local inverse `Lg` of `exp` (`SmoothLog.su2Log_eq_Lg_eventually`).  A background is REGULAR
when every loop holonomy entering the printed (43)-average lies in `LogReg` (this is the content of
the smallness "`Mα₀` sufficiently small", p.428).
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AdalyFormal.IngredientFamilyR2

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.SmoothLog (Lg Lg_contDiffAt Lg_contDiffAt_of_le su2Log_eq_Lg_eventually
  su2Log_comp_eventuallyEq su2Log_comp_contDiffAt exp_mem_suTwo su2Exp_coe_of_mem_suTwo)

/-- Points where `su2Log` is locally the analytic function `Lg`. -/
def LogReg : Set M2 :=
  {g | ContDiffAt ℝ ⊤ Lg g ∧ ∀ᶠ g' in 𝓝 g, ∀ h : g' ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
    su2Log ⟨g', h⟩ = Lg g'}

theorem LogReg_mem_nhds_one : LogReg ∈ 𝓝 (1 : M2) := by
  have h1 : ∀ᶠ g in 𝓝 (1 : M2), ContDiffAt ℝ ⊤ Lg g :=
    Lg_contDiffAt.eventually (by simp)
  have h2 : ∀ᶠ g in 𝓝 (1 : M2), ∀ᶠ g' in 𝓝 g, ∀ h : g' ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      su2Log ⟨g', h⟩ = Lg g' := su2Log_eq_Lg_eventually.eventually_nhds
  exact (h1.and h2)

theorem one_mem_LogReg : (1 : M2) ∈ LogReg := mem_of_mem_nhds LogReg_mem_nhds_one

/-- `su2Log ∘ G` is smooth at `0` whenever `G` is smooth at `0` with `G 0` in `LogReg`. -/
theorem su2Log_comp_contDiffAt_reg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → SU2) {n : WithTop ℕ∞} (hn : n ≤ ⊤)
    (hG : ContDiffAt ℝ n (fun A => (G A : M2)) 0) (hG0 : ((G 0 : SU2) : M2) ∈ LogReg) :
    ContDiffAt ℝ n (fun A => su2Log (G A)) 0 := by
  have hL : ContDiffAt ℝ n Lg ((G 0 : SU2) : M2) := hG0.1.of_le hn
  have hc : ContDiffAt ℝ n (fun A => Lg (G A : M2)) 0 := hL.comp (0 : E) hG
  have hev : (fun A => su2Log (G A)) =ᶠ[𝓝 0] fun A => Lg (G A : M2) := by
    have ht : Tendsto (fun A => (G A : M2)) (𝓝 0) (𝓝 ((G 0 : SU2) : M2)) := hG.continuousAt.tendsto
    filter_upwards [ht.eventually hG0.2] with A hA
    exact hA (G A).2
  exact hc.congr_of_eventuallyEq hev

#print axioms LogReg_mem_nhds_one
#print axioms su2Log_comp_contDiffAt_reg

end AdalyFormal.IngredientFamilyR2
