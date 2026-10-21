import CompactDictionary.Charts
import CompactDictionary.Geometry

/-!
Group-valued paths and raw averaging. `gammaPath` agrees with the frozen path
on the nonwrapping boxes actually summed, not on arbitrary pairs of sites.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CompactDictionary
open BalabanCompact
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.TowerLawCov
open AdalyFormal.Balaban.UbarTowerCov
open scoped Matrix Classical

noncomputable section
variable {L : Extent}

theorem coarsePathEnd_eq (s : ℕ) (y : Site L) (p : List (Fin 3)) :
    coarsePathEnd s y p = coarsePathEndpoint s y p := by
  induction p generalizing y with
  | nil => rfl
  | cons μ p ih => simp only [coarsePathEnd, coarsePathEndpoint, coarseShift_eq, ih]

theorem coarseHol_eq (s : ℕ) (V : Cfg L) (y : Site L) (p : List (Fin 3)) :
    coarseHol s (matU V) y p = ((coarsePathHolonomy s V y p : SU2) : M2) := by
  induction p generalizing y with
  | nil => rfl
  | cons μ p ih => simp only [coarseHol, coarsePathHolonomy, coarseShift_eq, ih, coe_mul, matU]

theorem steps_eq (s : ℕ) (y x : Site L) (μ : Fin 3) (h : (y μ).val ≤ (x μ).val) :
    steps s y x μ = coarseCoordSteps s y x μ := by
  unfold steps coarseCoordSteps
  rw [Fin.sub_val_of_le h]

theorem gammaPath_eq (s : ℕ) (y x : Site L) (h : ∀ μ, (y μ).val ≤ (x μ).val) :
    gammaPath s y x = coarseGammaPath s y x := by
  unfold gammaPath coarseGammaPath coarseStraightSegment
  rw [steps_eq s y x 2 (h 2)]
  rw [steps_eq s (Function.update y 2 (x 2)) x 1 (by simpa using h 1)]
  rw [steps_eq s (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0
    (by simpa using h 0)]
  exact List.append_assoc _ _ _

theorem stepBlock_eq (y : Site L) (s ell : ℕ) :
    stepBlock y s ell = AdalyFormal.Balaban.QjComposite.stepBlockOf y s ell := by
  ext x
  simp [stepBlock, AdalyFormal.Balaban.QjComposite.stepBlockOf,
    inStepBlock, AdalyFormal.Balaban.QjComposite.inStepBlock]

theorem cPlus_eq (s ell : ℕ) (c : Bond L) : cPlus s ell c = cPlusS s ell c :=
  coarsePathEnd_eq s c.1 _

theorem bondVar_eq (s ell : ℕ) (V : Cfg L) (c : Bond L) :
    bondVar s ell (matU V) c = ((coarseBondVar s ell V c : SU2) : M2) := coarseHol_eq s V _ _

theorem gammaVar_eq (s ell : ℕ) (V : Cfg L) (c : Bond L) (x : Site L)
    (hx : x ∈ stepBlock c.1 s ell) :
    gammaVar s ell (matU V) c x = ((gammaVarStrided s ell V c x : SU2) : M2) := by
  have h : ∀ μ, (c.1 μ).val ≤ (x μ).val := by
    have hx' : inStepBlock c.1 s ell x := (Finset.mem_filter.mp hx).2
    exact fun μ => (hx' μ).1
  simp only [gammaVar, gammaVarStrided, gammaPath_eq s c.1 x h, coarseHol_eq,
    cPlus_eq, coe_mul, coe_inv]

/-- All logarithms in blocking are evaluated at genuine SU(2) matrices. -/
theorem blocked_eq (s ell : ℕ) (V : Cfg L) (c : Bond L) :
    blocked s ell (matU V) c = ((stridedBlockedGauge su2LogExp s ell V c : SU2) : M2) := by
  have hsum : toM (∑ x ∈ stepBlock c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ •
      suLogM (gammaVar s ell (matU V) c x * (bondVar s ell (matU V) c)ᴴ)) =
      ∑ x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell,
        ((ell : ℚ) ^ 3)⁻¹ • su2Log (loopVar s ell V c x) := by
    change toMLM _ = _
    rw [map_sum]
    rw [← stepBlock_eq]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [map_smul]
    change ((ell : ℝ) ^ 3)⁻¹ • toM (suLogM _) = _
    rw [gammaVar_eq s ell V c x hx, bondVar_eq, ← coe_inv, ← coe_mul,
      suLogM_coe, toM_suLog, AdalyFormal.IngredientFamilyR2.qsmul_real]
    simp only [Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, loopVar]
  unfold blocked stridedBlockedGauge
  rw [suExpM_eq, hsum, bondVar_eq]
  rfl

theorem ofMat_coe (g : SU2) : ofMat (g : M2) = g := by
  unfold ofMat
  rw [dif_pos g.property]

/-- No fallback identity is introduced in the background tower. -/
theorem bgStep_eq (s ell : ℕ) (V : Cfg L) :
    bgStep s ell V = stridedBlockedGauge su2LogExp s ell V := by
  funext c
  rw [bgStep, blocked_eq, ofMat_coe]

theorem bgTower_eq (ell : ℕ) (U : Cfg L) (j : ℕ) :
    bgTower ell U j = UbarTower su2LogExp ell U j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [bgTower, ih, bgStep_eq, UbarTower_succ]

theorem rProdAux_eq (s : ℕ) (V0 V1 : Cfg L) (h : SU2) (y : Site L) (p : List (Fin 3)) :
    BalabanCompact.rProdAux s (matU V0) (matU V1) (h : M2) y p =
      (AdalyFormal.IngredientFamilyR2.rProdAux s V0 V1 h y p : M2) := by
  induction p generalizing y h with
  | nil => rfl
  | cons μ p ih =>
    simp only [BalabanCompact.rProdAux, AdalyFormal.IngredientFamilyR2.rProdAux,
      coarseShift_eq, coe_mul, coe_inv, matU]
    rw [← coe_mul h (V0 (y, μ)), ih]

/-- The real and rational averaging weights are identical, also at `ell = 0`. -/
theorem toM_sBlock (s ell : ℕ) (V0 V1 : Cfg L) (y : Site L) :
    toM (BalabanCompact.sBlock s ell (matU V0) (matU V1) y) =
      AdalyFormal.IngredientFamilyR2.sBlock s ell V0 V1 y := by
  unfold BalabanCompact.sBlock AdalyFormal.IngredientFamilyR2.sBlock
  change toMLM _ = _
  rw [map_sum, ← stepBlock_eq]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_smul]
  change ((ell : ℝ) ^ 3)⁻¹ • toM (suLogM _) = _
  have h : ∀ μ, (y μ).val ≤ (x μ).val := fun μ => ((Finset.mem_filter.mp hx).2 μ).1
  rw [gammaPath_eq s y x h]
  rw [show (1 : M2) = ((1 : SU2) : M2) from rfl, rProdAux_eq, suLogM_coe, toM_suLog,
    AdalyFormal.IngredientFamilyR2.qsmul_real]
  simp only [Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, AdalyFormal.IngredientFamilyR2.rProd]

theorem rawStep_eq (s ell : ℕ) (V0 V1 : Cfg L) (c : Bond L) :
    BalabanCompact.rawStep s ell (matU V0) (matU V1) c =
      (AdalyFormal.IngredientFamilyR2.rawStep s ell V0 V1 c : M2) := by
  rw [BalabanCompact.rawStep, AdalyFormal.IngredientFamilyR2.rawStep_simp]
  have hn (v : Vec) : toM (-v) = -toM v := toMLM.map_neg v
  simp only [suExpM_eq, hn, toM_sBlock, cPlus_eq, coe_mul, coe_inv]
  rw [show (fun b => matU V1 b * matU V0 b) = matU (fun b => V1 b * V0 b) from rfl]
  rw [blocked_eq, blocked_eq]

/-- Raw coordinate field equivalence, distinct from the Hilbert field isometry. -/
def rawField (L : Extent) : (Bond L → Vec) ≃L[ℝ] AdalyFormal.IngredientFamilyR2.XS L :=
  ContinuousLinearEquiv.piCongrRight (fun _ => rawCoordsCL)

@[simp] theorem rawField_apply (a : Bond L → Vec) (b : Bond L) :
    rawField L a b = rawCoords (a b) := rfl

/-- Global componentwise conjugacy; no regularity or differentiability hypothesis. -/
theorem qStep_conjugacy (s ell : ℕ) (V0 : Cfg L) (a : Bond L → Vec) (c : Bond L) :
    rawCoords (qStep s ell V0 a c) =
      AdalyFormal.IngredientFamilyR2.qStepX s ell V0 (rawField L a) c := by
  have he : (fun b => suExpM (a b)) =
      matU (AdalyFormal.IngredientFamilyR2.expCfgX (rawField L a)) := by
    funext b
    simp only [matU, AdalyFormal.IngredientFamilyR2.expCfgX, rawField_apply,
      toM2_rawCoords, suExpM_eq]
  unfold qStep
  rw [show (fun b => (V0 b : M2)) = matU V0 from rfl, he, rawStep_eq, rawCoords_suLogM]
  rfl

/-- The fixed convention differentiates at the identity fluctuation, for every background. -/
theorem qStep_zero (s ell : ℕ) (V0 : Cfg L) : qStep s ell V0 (0 : Bond L → Vec) = 0 := by
  funext c
  apply rawCoords.injective
  rw [qStep_conjugacy]
  simp only [map_zero, AdalyFormal.IngredientFamilyR2.qStepX_zero, Pi.zero_apply]

end
end CompactDictionary
