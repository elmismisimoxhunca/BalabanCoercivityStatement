import CompactDictionary.SiteOperators

/-! The localized normalized Δ operator, including all six commutators. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CompactDictionary
open BalabanCompact
open scoped RealInnerProductSpace Classical
noncomputable section
variable {L : Extent}

theorem curlBil_eq (P : Set (Plaq L)) (U : Cfg L) (A B : Field L) :
    curlBil P U A B = inner ℝ (fieldPauli (Bond L) A)
      (AdalyFormal.StatementLaneR6.dstarDLoc U P (fieldPauli (Bond L) B)) := by
  rw [AdalyFormal.StatementLaneR6.inner_dstarDLoc]
  change (∑ p ∈ plaqFin P, inner ℝ (curlM (matU U) (ofField A) p)
    (curlM (matU U) (ofField B) p)) = _
  rw [PiLp.inner_apply]
  simp only [plaqFin, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [AdalyFormal.StatementLaneR6.plaqMask_apply, AdalyFormal.StatementLaneR6.plaqMask_apply]
  split_ifs with hp
  · change inner ℝ (curlM (matU U) (ofField A) p) (curlM (matU U) (ofField B) p) =
      inner ℝ (AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U (fun b => pauli (A b)) p)
        (AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U (fun b => pauli (B b)) p)
    rw [← pauli_curlM, ← pauli_curlM, pauli.inner_map_map]
    rfl
  · simp

theorem primeBil_diag_eq (P : Set (Plaq L)) (U : Cfg L) (A : Field L) :
    primeBil P U A A = AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U P
      (fieldPauli (Bond L) A) (fieldPauli (Bond L) A) := by
  change (∑ p ∈ plaqFin P, deltaPrimeBilLM (matU U) p (ofField A) (ofField A)) =
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc U P
      (fun b => pauli (A b)) (fun b => pauli (A b))
  simp only [AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  rw [AdalyFormal.StatementLaneR6.deltaPrimeBilRawLoc_apply]
  simp only [deltaPrimeBilLM_self, deltaPrimeAt_eq, plaqFin, Finset.sum_filter,
    AdalyFormal.Balaban.DeltaPrimeOperator.bilPlaq_diag]
  have scalar (r : ℝ) : (1 / 2 : ℝ) * (1 / 2 * (r + r)) = 1 / 2 * r := by ring
  rw [scalar, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs
  · rfl
  · simp

theorem DeltaOp_conjugacy (P : Set (Plaq L)) (U : Cfg L) (A : Field L) :
    fieldPauli (Bond L) (DeltaOp P U A) =
      AdalyFormal.StatementLaneR6.deltaKLocCLM U P (fieldPauli (Bond L) A) := by
  apply symmetric_conjugacy (fieldPauli (Bond L)) (DeltaOp P U)
    (AdalyFormal.StatementLaneR6.deltaKLocCLM U P)
  · intro x y
    simp only [DeltaOp, _root_.add_apply, inner_add_left, inner_add_right, symmOp_symm]
  · exact AdalyFormal.StatementLaneR6.deltaKLocCLM_symm U P
  · intro x
    simp only [DeltaOp, _root_.add_apply, inner_add_right, inner_symmOp_diag,
      AdalyFormal.StatementLaneR6.inner_deltaKLocCLM]
    rw [curlBil_eq, AdalyFormal.StatementLaneR6.inner_dstarDLoc, primeBil_diag_eq]

theorem Dpi_conjugacy (G : AdalyFormal.IngredientFamilyR2.TowerGeom L) (U : Cfg L)
    (a : ℝ) (A : Field L) :
    fieldPauli (Bond L) (Dpi G.ell G.k (bgTower G.ell U) G.Om0 G.Lam U a A) =
      AdalyFormal.IngredientFamilyR2.DpiFull G U a (fieldPauli (Bond L) A) := by
  unfold Dpi AdalyFormal.IngredientFamilyR2.DpiFull
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_conjugacy (fieldPauli (Bond L)) (fieldPauli (Bond L)) _ _ (Wop_conjugacy G U a),
    DeltaOp_conjugacy, Wop_conjugacy, plaqIn_eq]
  rfl

end
end CompactDictionary
