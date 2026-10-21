import CompactDictionary.Delta

/-! Constraint-space reindexing and bond-sector jets. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CompactDictionary
open BalabanCompact
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open scoped Classical RealInnerProductSpace
noncomputable section
variable {L : Extent}

variable (G : AdalyFormal.IngredientFamilyR2.TowerGeom L)

theorem bondsLam_eq (j : ℕ) : bondsLam G.ell G.k G.Lam j = AdalyFormal.IngredientFamilyR2.bondsLam G j := by
  ext b
  simp only [bondsLam, AdalyFormal.IngredientFamilyR2.bondsLam, coarseShift_eq]
  rfl

/-- No lattice size or stratum is changed: only proofs of bond membership are repackaged. -/
def bIdxEquiv : BIdx G.ell G.k G.Lam ≃ AdalyFormal.IngredientFamilyR2.BIdx G where
  toFun p := ⟨p.1, ⟨p.2.1, (bondsLam_eq G p.1) ▸ p.2.2⟩⟩
  invFun p := ⟨p.1, ⟨p.2.1, (bondsLam_eq G p.1).symm ▸ p.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sectorPauli : FSp G.ell G.k G.Lam ≃ₗᵢ[ℝ] AdalyFormal.IngredientFamilyR2.FSp G :=
  (fieldPauli (BIdx G.ell G.k G.Lam)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ SuTwo (bIdxEquiv G))

@[simp] theorem sectorPauli_apply (f : FSp G.ell G.k G.Lam) (p : AdalyFormal.IngredientFamilyR2.BIdx G) :
    sectorPauli G f p = pauli (f ((bIdxEquiv G).symm p)) := rfl

theorem suCoord_fieldPauli (A : Field L) :
    AdalyFormal.IngredientFamilyR2.suCoord (fieldPauli (Bond L) A) = rawField L (ofField A) :=
  suCoordF_pauli (ofField A)

theorem suCoordInv_raw (A : Bond L → Vec) :
    AdalyFormal.IngredientFamilyR2.suCoordInv (rawField L A) = fieldPauli (Bond L) (toField A) := by
  apply PiLp.ext
  intro b
  exact congrFun (suCoordFInv_raw A) b

variable (U : Cfg L)

theorem QlinB_conjugacy (j : ℕ) (A : Field L) :
    fieldPauli (Bond L) (toField (QlinComp G.ell (bgTower G.ell U) j (ofField A))) =
      AdalyFormal.IngredientFamilyR2.QlinB G U j (fieldPauli (Bond L) A) := by
  rw [AdalyFormal.IngredientFamilyR2.QlinB_apply, suCoord_fieldPauli, ← bg_eq,
    ← QlinComp_conjugacy, suCoordInv_raw]

theorem D2B_conjugacy (j : ℕ) (A B : Field L) :
    fieldPauli (Bond L) (toField (D2CompLM G.ell (bgTower G.ell U) j (ofField A) (ofField B))) =
      AdalyFormal.IngredientFamilyR2.D2B G U j (fieldPauli (Bond L) A) (fieldPauli (Bond L) B) := by
  unfold AdalyFormal.IngredientFamilyR2.D2B
  rw [LinearMap.mk₂_apply, suCoord_fieldPauli, suCoord_fieldPauli, ← bg_eq,
    ← D2Comp_conjugacy, suCoordInv_raw]

theorem Qfull_conjugacy (A : Field L) :
    sectorPauli G (Qfull G.ell G.k (bgTower G.ell U) G.Lam A) =
      AdalyFormal.IngredientFamilyR2.QfullOf G U (fieldPauli (Bond L) A) := by
  apply PiLp.ext
  intro p
  change pauli ((((G.ell : ℝ) ^ p.1.val)⁻¹) •
    (QlinComp G.ell (bgTower G.ell U) p.1.val (ofField A)) p.2.1) =
    (((G.ell : ℝ) ^ p.1.val)⁻¹) • (AdalyFormal.IngredientFamilyR2.QlinB G U p.1 (fieldPauli (Bond L) A)) p.2.1
  rw [map_smul, ← QlinB_conjugacy]
  rfl

theorem C2bil_diag_conjugacy (A : Field L) :
    sectorPauli G (C2bil G.ell G.k (bgTower G.ell U) G.Lam A A) =
      AdalyFormal.IngredientFamilyR2.C2fullOf G U (fieldPauli (Bond L) A) := by
  apply PiLp.ext
  intro p
  change pauli ((((G.ell : ℝ) ^ p.1.val)⁻¹) • (1 / 2 : ℝ) •
    (D2CompLM G.ell (bgTower G.ell U) p.1.val (ofField A) (ofField A)) p.2.1) =
    (((G.ell : ℝ) ^ p.1.val)⁻¹) • ((1 / 2 : ℝ) •
      (AdalyFormal.IngredientFamilyR2.D2B G U p.1 (fieldPauli (Bond L) A) (fieldPauli (Bond L) A)) p.2.1)
  rw [map_smul, map_smul, ← D2B_conjugacy]
  rfl

theorem massDiag_conjugacy (a : ℝ) (f : FSp G.ell G.k G.Lam) :
    sectorPauli G (diagW G.ell G.k G.Lam (massW G.ell a) f) =
      AdalyFormal.IngredientFamilyR2.diagW G (AdalyFormal.IngredientFamilyR2.massW G a) (sectorPauli G f) := by
  apply PiLp.ext
  intro p
  change pauli ((a * (G.ell : ℝ) ^ p.1.val) • f ((bIdxEquiv G).symm p)) = _
  rw [map_smul]
  rfl

theorem MassFull_conjugacy (a : ℝ) (A : Field L) :
    fieldPauli (Bond L) (MassFull G.ell G.k (bgTower G.ell U) G.Lam a A) =
      AdalyFormal.IngredientFamilyR2.MassFull G a (AdalyFormal.IngredientFamilyR2.bondSectorOf G U)
        (fieldPauli (Bond L) A) := by
  unfold MassFull AdalyFormal.IngredientFamilyR2.MassFull
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_conjugacy (fieldPauli (Bond L)) (sectorPauli G) _ _ (Qfull_conjugacy G U),
    massDiag_conjugacy, Qfull_conjugacy]
  rfl

end
end CompactDictionary
