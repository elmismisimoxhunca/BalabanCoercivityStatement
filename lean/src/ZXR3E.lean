import ZR3D2
import ZXR2Close0d

/-!
# R3E -- MUST-NOT-FIRE on the GENUINE object (ingredient lane r2: `DpiFull`, `Tfull`, `Rproj`):
both new laws hold for the printed operators, on every tower geometry `G` and `a`.
  * `genuine_Dpi_flat`  : flat `U`, `curl A = 0  ⇒  ⟨A, Δ_π A⟩ = 0`     (here `DpiFull = W* Δ W`, (3.119))
  * `genuine_T_ker`     : every `U`, `A ⊥ D_U(sites) ⇒ T A = 0` with `T = R D*`  (`Tfull`)
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane3

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2 hiding gradL2 gradL2_apply
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaPrimeCLMNormalized deltaKCLMNormalized)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM inner_dstarDCLM_eq_dstarDQuadForm)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp
  norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm)

variable {L : PeriodicLatticeExtent}

theorem curl_gradL2_flat (mu : SiteL2 L) :
    curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (AdalyFormal.IngredientFamilyR2.gradL2 flatCfg mu) = 0 := by
  have h : AdalyFormal.IngredientFamilyR2.gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) mu =
      WithLp.toLp 2 (gradValueCovariant (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (WithLp.ofLp mu)) := rfl
  rw [h, curlCovariantCLM_L2_toLp]
  have : curlValueCovariant (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
      (gradValueCovariant flatCfg (WithLp.ofLp mu)) = 0 := by
    funext p
    rw [curlValueCovariant_gradValueCovariant]
    simp [flatCfg, RMap_one]
  rw [this]; rfl

theorem Delta_flat_form (G : TowerGeom L) (y : BondFnL2 L) :
    ⟪y, Delta G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) y⟫ =
      ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn G.Om0)
        (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2
          (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) y)‖ ^ 2 := by
  unfold Delta
  rw [AdalyFormal.StatementLaneR6.inner_deltaKLocCLM]
  have h0 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (plaqIn G.Om0) y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU _ _ _
  rw [h0, add_zero, real_inner_self_eq_norm_sq]

theorem genuine_Dpi_flat (G : TowerGeom L) (a : ℝ) (A : BondFnL2 L)
    (hA : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A = 0) :
    ⟪A, DpiFull G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) a A⟫ = 0 := by
  have h0 : AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2
      (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
      (A - IngredientFamilyR2.gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
        (Gp G flatCfg a (Rproj G flatCfg (gradAdj flatCfg A)))) = 0 := by
    have h1 : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
      (A - IngredientFamilyR2.gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
        (Gp G flatCfg a (Rproj G flatCfg (gradAdj flatCfg A)))) = 0 := by
      rw [map_sub, hA, curl_gradL2_flat, sub_zero]
    exact h1
  rw [inner_DpiFull, Delta_flat_form, h0, map_zero, norm_zero]
  simp

theorem genuine_T_ker (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L)
    (hA : ∀ lam : SiteL2 L, ⟪A, AdalyFormal.IngredientFamilyR2.gradL2 U lam⟫ = 0) :
    Tfull G U A = 0 := by
  have h0 : gradAdj U A = 0 := by
    have h1 : ⟪gradAdj U A, gradAdj U A⟫ = ⟪A, AdalyFormal.IngredientFamilyR2.gradL2 U (gradAdj U A)⟫ :=
      ContinuousLinearMap.adjoint_inner_left _ _ _
    rw [hA] at h1
    exact inner_self_eq_zero.mp h1
  show (Rproj G U) (gradAdj U A) = 0
  rw [h0, map_zero]

/-- the same two facts are what `no_witness` consumes: the genuine operators satisfy its laws on the
constant field (non-vacuity of the antecedents on the genuine object) -/
theorem genuine_laws_on_const (G : TowerGeom L) (a : ℝ) (X : SuTwo) :
    ⟪constField L X, DpiFull G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) a (constField L X)⟫ = 0 ∧
    Tfull G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (constField L X) = 0 :=
  ⟨genuine_Dpi_flat G a _ (curl_const_trivial X),
   genuine_T_ker G _ _ (fun lam => const_orth_grad_trivial X lam)⟩

#print axioms genuine_Dpi_flat
#print axioms genuine_T_ker
#print axioms genuine_laws_on_const

end AdalyFormal.StatementLane3
