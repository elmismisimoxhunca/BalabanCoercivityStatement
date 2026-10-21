import BalabanCompact.Ops
import R2Coord
import AdalyFormal.Balaban.RMapLipschitz

/-!
Private compact/frozen dictionary: the intrinsic Pauli isometry and the distinct
raw-coordinate equivalence. No coercivity theorem is imported or assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace CompactDictionary

open BalabanCompact
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo mem_suTwo_iff)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.IngredientFamilyR2 (toM2 fromM2 toM2_fromM2)
open scoped RealInnerProductSpace

noncomputable section

/-- Frozen raw coordinates are ordered `(iσ₃,iσ₂,iσ₁)`. -/
def rawCoords : Vec ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![v 2, v 1, v 0]
  invFun w := WithLp.toLp 2 ![w 2, w 1, w 0]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv w := by funext i; fin_cases i <;> rfl
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl

theorem toM2_rawCoords (v : Vec) : toM2 (rawCoords v) = toM v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toM2, rawCoords, toM, Fin.sum_univ_three, Emat, Complex.real_smul] <;> ring

theorem rawCoords_fromM (X : M2) : rawCoords (fromM X) = fromM2 X := by
  funext i
  fin_cases i <;> simp [rawCoords, fromM, fromM2, Complex.mul_re]

theorem toM_fromM {X : M2} (hX : X ∈ suTwo) : toM (fromM X) = X := by
  rw [← toM2_rawCoords, rawCoords_fromM, toM2_fromM2 hX]

theorem toM_mem (v : Vec) : toM v ∈ suTwo := by
  rw [mem_suTwo_iff]
  exact ⟨toM_skew v, toM_trace v⟩

def toMLM : Vec →ₗ[ℝ] M2 where
  toFun := toM
  map_add' := toM_add
  map_smul' := toM_smul

/-- The map into the frozen intrinsic Hilbert fibre, not the ambient matrix norm. -/
def pauliLinear : Vec ≃ₗ[ℝ] SuTwo where
  toFun v := ⟨toM v, toM_mem v⟩
  invFun X := fromM X
  left_inv := fromM_toM
  right_inv X := Subtype.ext (toM_fromM X.property)
  map_add' v w := Subtype.ext (toM_add v w)
  map_smul' c v := Subtype.ext (toM_smul c v)

@[simp] theorem pauliLinear_coe (v : Vec) : (pauliLinear v : M2) = toM v := rfl

theorem pauliLinear_norm_sq (v : Vec) : ‖pauliLinear v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_hsInner, hsInner_def]
  change -(1 / 2 : ℝ) * (Matrix.trace (toM v * toM v)).re = _
  rw [toM_sq]
  simp [Matrix.trace_smul, Complex.real_smul, -Complex.ofReal_pow]
  ring

/-- The trace-normalized Pauli map is exactly an isometry (no `√2`). -/
def pauli : Vec ≃ₗᵢ[ℝ] SuTwo where
  toLinearEquiv := pauliLinear
  norm_map' v := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (pauliLinear_norm_sq v)

@[simp] theorem pauli_coe (v : Vec) : (pauli v : M2) = toM v := rfl
@[simp] theorem pauli_symm_apply (X : SuTwo) : pauli.symm X = fromM X := rfl

/-- Ordinary raw-coordinate spaces have a different norm, so use a CLE here. -/
def rawCoordsCL : Vec ≃L[ℝ] (Fin 3 → ℝ) := rawCoords.toContinuousLinearEquiv

/-- The two class predicates use the same *matrix* Frobenius formula. -/
theorem frobSq_eq (X : M2) : BalabanCompact.frobSq X =
    AdalyFormal.Balaban.RMapLipschitz.frobSq X := rfl

theorem frobNorm_eq (X : M2) : BalabanCompact.frobNorm X =
    AdalyFormal.Balaban.RMapLipschitz.frobNorm X := rfl

theorem frobSq_toM (v : Vec) : BalabanCompact.frobSq (toM v) = 2 * ‖v‖ ^ 2 := by
  have h := AdalyFormal.Balaban.RMapLipschitz.norm_sq_eq_half_frobSq (pauli v)
  rw [pauli.norm_map, pauli_coe, ← frobSq_eq] at h
  linarith

theorem frobNorm_toM (v : Vec) : BalabanCompact.frobNorm (toM v) = Real.sqrt 2 * ‖v‖ := by
  rw [BalabanCompact.frobNorm, frobSq_toM, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_sq (norm_nonneg v)]

/-- Pointwise Hilbert isometry, usable for bonds, sites and constraint indices. -/
def fieldPauli (ι : Type*) [Fintype ι] :
    PiLp 2 (fun _ : ι => Vec) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : ι => SuTwo) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => pauli)

@[simp] theorem fieldPauli_apply {ι : Type*} [Fintype ι]
    (v : PiLp 2 (fun _ : ι => Vec)) (i : ι) : fieldPauli ι v i = pauli (v i) := rfl

end
end CompactDictionary
