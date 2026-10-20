import ZXR2Wire3
import ZXR2Flat6
import ZXR2Unit3

/-!
# R2Wire4 -- the flat instance: `hb` of `toIngr` holds at `U = 1` (so the hypothesis is satisfiable,
and `C`,`h` exist there), and `Q₁` equals the printed closed formula (2.125).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.IngredientFamilyR2

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 su2LogExp)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.StatementLane (scaleUp)

theorem Ubar_flat (ell : ℕ) {L : PeriodicLatticeExtent} (l : ℕ) :
    UbarTower su2LogExp ell (flatCfg : PeriodicLinkConfiguration SU2 L) l = flatCfg := by
  induction l with
  | zero => rfl
  | succ l ih =>
      rw [AdalyFormal.Balaban.UbarTowerCov.UbarTower_succ, ih]
      funext c
      exact avg_flat_eq_one _ ell c

theorem unitBg_flat (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) :
    unitBg ell k Lu hell (flatCfg : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) = flatCfg := rfl

theorem Q1_flat_eq (ell : ℕ) {L : PeriodicLatticeExtent} (hell : 0 < ell) (hdvd : ∀ μ, ell ∣ (L μ + 1)) :
    Q1jet ell (flatCfg : PeriodicLinkConfiguration SU2 L) = AdalyFormal.IngredientFamily.q1SU2 ell := by
  refine LinearMap.ext (fun B => ?_)
  funext c
  exact Q1jet_flat ell hell hdvd B c

namespace IngrBParams

/-- `hb` at the trivial background: `H₀ = ell⁻³ · id`. -/
theorem hb_flat (P : IngrBParams) (hU : P.U = flatCfg) (hdvd : ∀ μ, P.ell ∣ (P.Lu μ + 1)) :
    Function.Bijective (H0 P.Lam P.Q1) := by
  have h1 : P.unitBgU = flatCfg := by
    unfold unitBgU
    rw [show bgTower P.G P.U P.k = flatCfg by
      unfold bgTower; rw [hU]; exact Ubar_flat P.ell P.k]
    rfl
  have h2 : P.Q1 = AdalyFormal.IngredientFamily.q1SU2 P.ell := by
    unfold Q1; rw [h1]; exact Q1_flat_eq P.ell P.hell hdvd
  rw [h2]
  exact H0_q1SU2_bijective P.hell hdvd P.Lam

#print axioms hb_flat

/-- THE NAME ASKED FOR: `IngrB_genuine` — a structure of the type of `StatementLane.Ingr`, every field
built from the printed operators (hypotheses `hb`, `hunit` explicit, see `toIngr`). -/
noncomputable abbrev IngrB_genuine (P : IngrBParams) (hb : Function.Bijective (H0 P.Lam P.Q1))
    (hunit : IsUnit ((P.Qin.comp P.G1in).comp (ContinuousLinearMap.adjoint P.Qin))) :
    AdalyFormal.StatementLane.Ingr P.ell P.Lu (scaleUp P.ell P.k P.Lu) P.Lam :=
  P.toIngr hb hunit

/-- Flat, full-tower instance: `hb` is a THEOREM, `τ` is a bijection; what remains of `hunit` is the
printed chain (coercivity `c` of `G⁻¹`, `‖Δ^{(2)}‖ ≤ ε < c`, `Q*` injective): `unit_of_chain`. -/
theorem flat_full_instance (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (hdvd : ∀ μ, ell ∣ (Lu μ + 1)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) :
    let P : IngrBParams := ⟨ell, k, Lu, hell, fullTower ell k Lu, flatCfg, a, Lam⟩
    Function.Bijective (H0 P.Lam P.Q1) ∧ Function.Bijective P.tau :=
  ⟨hb_flat _ rfl hdvd, IngrBParams.tau_bijective _ (fullTower_fullSupp ell k Lu hell flatCfg a Lam)⟩

end IngrBParams

end AdalyFormal.IngredientFamilyR2
