import ZXR2Close0c

/-!
# R2Close0d -- THE CLOSED INSTANCE: `IngrB0 : StatementLane.Ingr ell Lu (scaleUp ell 0 Lu) Lam`,
every field built from the printed operators and BOTH hypotheses of `toIngr` proved
(`k = 0`, flat background, full tower, `a > 0`, `ell ∣ Lu μ + 1`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Ingr)

variable (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

theorem P0_hb (hdvd : ∀ μ, ell ∣ (Lu μ + 1)) :
    Function.Bijective (H0 (P0 ell Lu hell a Lam).Lam (P0 ell Lu hell a Lam).Q1) :=
  IngrBParams.hb_flat (P0 ell Lu hell a Lam) rfl hdvd

theorem P0_hunit (ha : 0 < a) :
    IsUnit (((P0 ell Lu hell a Lam).Qin.comp (P0 ell Lu hell a Lam).G1in).comp
      (ContinuousLinearMap.adjoint (P0 ell Lu hell a Lam).Qin)) := by
  have hτ : Function.Bijective (P0 ell Lu hell a Lam).tau :=
    IngrBParams.tau_bijective _ (fullTower_fullSupp ell 0 Lu hell flatCfg a Lam)
  refine IngrBParams.unit_of_chain (P0 ell Lu hell a Lam) hτ (c := a) (ε := 0) ha
    (fun x => P0_Ginv_coercive ell Lu hell a Lam x) ?_ (P0_Qs_injective ell Lu hell a Lam)
    (IngrBParams.eta_pos _)
  rw [P0_Delta2_zero]
  exact le_of_eq ContinuousLinearMap.opNorm_zero

/-- THE CLOSED `IngrB_genuine` at `k = 0`, flat background, full tower. -/
noncomputable def IngrB0 (hdvd : ∀ μ, ell ∣ (Lu μ + 1)) (ha : 0 < a) :
    Ingr ell Lu (scaleUp ell 0 Lu) Lam :=
  IngrBParams.IngrB_genuine (P0 ell Lu hell a Lam) (P0_hb ell Lu hell a Lam hdvd) (P0_hunit ell Lu hell a Lam ha)

#print axioms P0_hunit
#print axioms IngrB0

end AdalyFormal.IngredientFamilyR2
