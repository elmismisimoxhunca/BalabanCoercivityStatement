import ZXR2Sector
import ZStatementP428

/-!
# R2Unit1 (r8: `Q1jet`, `C2tilde` use the LOCAL per-component jets of `ZLocJet`; bridges `Q1jet_eq_r7`, `C2tilde_eq_r7`) -- unit-lattice objects: `Q₁` (printed one-step linear part at the unit level), the
reparametrisation `C` of (3.157) and the corridor lift `h` of CMP109 p.267, `D̃⁽²⁾` (3.155).

All are built from the printed one-step raw map `V̿₁` (CMP98 (63)/(89), R2Raw1) at stride 1 on the
UNIT torus, with background the blocked fine background `Ū^k` read at the unit sites.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.IngredientFamilyR2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.StatementLane (scaleUp LamPrime IsDroppedIn)

variable {L : PeriodicLatticeExtent}

/-- coordinates on plain su(2)-valued function fields. -/
noncomputable def suCoordF : (Bond L → SuTwo) →ₗ[ℝ] XS L where
  toFun B := fun b => fromM2 ((B b : SuTwo) : M2)
  map_add' A B := by funext b; simp
  map_smul' c A := by funext b; simp

noncomputable def suCoordFInv : XS L →ₗ[ℝ] (Bond L → SuTwo) where
  toFun a := fun b => ⟨toM2 (a b), toM2_mem _⟩
  map_add' a a' := by funext b; apply Subtype.ext; simp
  map_smul' c a := by funext b; apply Subtype.ext; simp

theorem suCoordFInv_suCoordF (B : Bond L → SuTwo) : suCoordFInv (suCoordF B) = B := by
  funext b; apply Subtype.ext
  show toM2 (fromM2 ((B b : SuTwo) : M2)) = _
  exact toM2_fromM2 (B b).2

/-! ## 1. the unit torus inside the fine torus -/

/-- unit site `y` ↦ the fine site `ell^k · y` (the embedding of `LambdaOK`). -/
def embY (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (y : PeriodicLatticeSite Lu) : PeriodicLatticeSite (scaleUp ell k Lu) :=
  fun μ => ⟨ell ^ k * (y μ).val, by
    have hp : 0 < ell ^ k := pow_pos hell k
    have h1 := (y μ).isLt
    have : scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
      unfold scaleUp
      have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    rw [this]
    calc ell ^ k * (y μ).val < ell ^ k * (Lu μ + 1) := Nat.mul_lt_mul_of_pos_left h1 hp
      _ = (Lu μ + 1) * ell ^ k := mul_comm _ _⟩

theorem embY_val (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (y : PeriodicLatticeSite Lu) (μ : Fin 3) : ((embY ell k Lu hell y) μ).val = ell ^ k * (y μ).val := rfl

/-- the blocked background `Ū^k` read at the unit sites: a link configuration of the UNIT torus. -/
noncomputable def unitBg (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (Ubar : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) :
    PeriodicLinkConfiguration SU2 Lu :=
  fun e => Ubar (embY ell k Lu hell e.1, e.2)

/-! ## 2. `Q₁` and `C̃⁽²⁾` of the unit-level one-step raw map -/

/-- `Q₁`: the printed linear part `L Q(V₀)` of (122) at the unit level, divided by `L`, read at the
coarse bonds: `(Q₁B)(c) = L⁻¹ (D qStepX(0) B)_c`. -/
noncomputable def Q1jet (ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) :
    (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo) where
  toFun B := fun c => ((ell : ℝ)⁻¹) •
    (suCoordFInv (QlinStepL 1 ell V0 (suCoordF B))) (c.1.1, c.2)
  map_add' A B := by funext c; simp [smul_add]
  map_smul' r A := by
    funext c
    simp only [RingHom.id_apply, Pi.smul_apply, map_smul]
    exact smul_comm ((ell : ℝ)⁻¹) r _

/-- `C̃⁽²⁾(B)`: the second-order term of the unit-level raw map, at the coarse bonds. -/
noncomputable def C2tilde (ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (B : Bond L → SuTwo) :
    CoarseBond L ell → SuTwo := fun c =>
  (suCoordFInv (C2StepL 1 ell V0 (suCoordF B))) (c.1.1, c.2)

theorem C2tilde_smul (ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (r : ℝ) (B : Bond L → SuTwo) :
    C2tilde ell V0 (r • B) = r ^ 2 • C2tilde ell V0 B := by
  funext c
  unfold C2tilde
  rw [map_smul, C2StepL_smul]
  simp only [map_smul, Pi.smul_apply]

/-- r8 BRIDGE: on a regular unit background the repaired `Q₁` is the r7 one (`QlinStepX`, `fderiv` of the whole map). -/
theorem Q1jet_eq_r7 (ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg 1 ell V0) (B : Bond L → SuTwo)
    (c : CoarseBond L ell) :
    Q1jet ell V0 B c = ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepX 1 ell V0 (suCoordF B))) (c.1.1, c.2) := by
  show ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell V0 (suCoordF B))) (c.1.1, c.2) = _
  rw [QlinStepL_eq_of_reg 1 ell V0 hreg]

/-- r8 BRIDGE (second order) for `C̃⁽²⁾`. -/
theorem C2tilde_eq_r7 (ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg 1 ell V0) (B : Bond L → SuTwo)
    (c : CoarseBond L ell) :
    C2tilde ell V0 B c = (suCoordFInv (C2StepX 1 ell V0 (suCoordF B))) (c.1.1, c.2) := by
  show (suCoordFInv (C2StepL 1 ell V0 (suCoordF B))) (c.1.1, c.2) = _
  rw [C2StepL_eq_C2StepX 1 ell V0 hreg]

#print axioms C2tilde_smul
#print axioms Q1jet_eq_r7
#print axioms C2tilde_eq_r7

end AdalyFormal.IngredientFamilyR2
