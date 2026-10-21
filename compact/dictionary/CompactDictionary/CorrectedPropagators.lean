import CompactDictionary.Propagators

/-! The unique symmetric G₁ inverse and its totalized padded covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
namespace CompactDictionary
open BalabanCompact
open scoped RealInnerProductSpace
noncomputable section
variable {L : Extent}
variable (G : AdalyFormal.IngredientFamilyR2.TowerGeom L) (U : Cfg L) (a : ℝ)
local notation "bg" => bgTower G.ell U
local notation "J" => fieldPauli (Bond L) (Jfield (plaqIn G.Om0) U)
local notation "D" => AdalyFormal.IngredientFamilyR2.baseData G U a
  (AdalyFormal.IngredientFamilyR2.bondSectorOf G U) J

theorem JF_includeE : JF G.Om0 U = includeE G (D).J :=
  (includeE_projectE G (Jfield (plaqIn G.Om0) U)).symm

theorem C2pi_conjugacy (x : Supported G) :
    sectorPauli G (C2bil G.ell G.k bg G.Lam
      (Wop G.ell G.k bg G.Om0 G.Lam U a (includeE G x))
      (Wop G.ell G.k bg G.Om0 G.Lam U a (includeE G x))) = (D).C2 x := by
  rw [C2bil_diag_conjugacy, Wop_conjugacy, fieldPauli_includeE]
  rfl

theorem betaK_diag_eq (x : Supported G) :
    betaK G.ell G.k bg G.Om0 G.Lam U a (includeE G x) (includeE G x) = (D).K x := by
  unfold betaK
  rw [LinearMap.mk₂_apply, bondMask_includeE]
  rw [← includeE_projectE G (Dpi _ _ _ _ _ _ _ _), Dpi_compress G U a J,
    ← includeE_projectE G (MassFull _ _ _ _ _ _), Mass_compress G U a J,
    HE_conjugacy G U a J, C2pi_conjugacy, JF_includeE G U a]
  simp only [includeE_inner]
  rw [← (fieldPauli (Site L)).inner_map_map, Tfull_conjugacy G U a J, projectE_includeE,
    real_inner_self_eq_norm_sq]
  rfl

/-- Restrict the compact symmetric form to the frozen supported carrier. -/
def correctedInverse : Supported G →L[ℝ] Supported G :=
  (projectE G).comp ((symmOp (betaK G.ell G.k bg G.Om0 G.Lam U a)).comp (includeE G))

theorem correctedInverse_spec : (D).IsG1inv (correctedInverse G U a) := by
  constructor
  · intro x y
    change ⟪projectE G (symmOp _ (includeE G x)), y⟫ = ⟪x, projectE G (symmOp _ (includeE G y))⟫
    rw [real_inner_comm y, projectE_inner, ← symmOp_symm, real_inner_comm, projectE_inner]
  · intro x
    change ⟪x, projectE G (symmOp _ (includeE G x))⟫ = _
    rw [projectE_inner, inner_symmOp_diag, betaK_diag_eq]

theorem correctedInverse_eq (A : Supported G →L[ℝ] Supported G) (hA : (D).IsG1inv A) :
    correctedInverse G U a = A :=
  (D).G1inv_unique (correctedInverse_spec G U a) hA

theorem corrected_pad (A : Supported G →L[ℝ] Supported G) (hA : (D).IsG1inv A) :
    bondMask G.Om0 ∘L symmOp (betaK G.ell G.k bg G.Om0 G.Lam U a) ∘L bondMask G.Om0 +
      (1 - bondMask G.Om0) = pad (includeE G) (projectE G) A := by
  rw [← correctedInverse_eq G U a A hA]
  ext1 x
  simp only [_root_.add_apply, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply, pad_apply, correctedInverse]
  rw [← includeE_projectE G x, ← includeE_projectE]

theorem G1_conjugacy (A : Supported G →L[ℝ] Supported G) (hA : (D).IsG1inv A) (x : Field L) :
    G1 G.ell G.k bg G.Om0 G.Lam U a x = includeE G ((D).G1 A (projectE G x)) := by
  unfold G1
  rw [corrected_pad G U a A hA, inverse_supported]
  rfl

theorem Nmat_conjugacy (A : Supported G →L[ℝ] Supported G) (hA : (D).IsG1inv A)
    (f : FSp G.ell G.k G.Lam) :
    sectorPauli G (Nmat G.ell G.k bg G.Om0 G.Lam U a f) =
      (((D).Q.comp ((D).G1 A)).comp (D).Qs) (sectorPauli G f) := by
  unfold Nmat
  simp only [ContinuousLinearMap.comp_apply]
  rw [Qe_conjugacy G U a J, G1_conjugacy G U a A hA, projectE_includeE,
    Qs_conjugacy G U a J, projectE_includeE]

theorem H1E_conjugacy (A : Supported G →L[ℝ] Supported G) (hA : (D).IsG1inv A)
    (f : FSp G.ell G.k G.Lam) :
    H1E G.ell G.k bg G.Om0 G.Lam U a f = includeE G ((D).H1 A (sectorPauli G f)) := by
  unfold H1E
  simp only [ContinuousLinearMap.comp_apply]
  rw [G1_conjugacy G U a A hA, Qs_conjugacy G U a J, projectE_includeE]
  have hi := inverse_conjugacy (sectorPauli G).toContinuousLinearEquiv _ _
    (Nmat_conjugacy G U a A hA) f
  change sectorPauli G (Ring.inverse (Nmat G.ell G.k bg G.Om0 G.Lam U a) f) =
    Ring.inverse (((D).Q.comp ((D).G1 A)).comp (D).Qs) (sectorPauli G f) at hi
  unfold Nmat at hi
  rw [hi]
  rfl

end
end CompactDictionary
