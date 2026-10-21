import CompactDictionary.Corridor

/-!
Localized source and prime form. All six pairs are retained in the frozen
transported convention; the factor `1/2` is the trace normalization.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace CompactDictionary
open BalabanCompact
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_coe_apply curlValueCovariant)
open scoped Matrix Classical
noncomputable section
variable {L : Extent}

theorem pauli_conjM (U : SU2) (v : Vec) : pauli (conjM (U : M2) v) = RMap U (pauli v) := by
  apply Subtype.ext
  change toM (fromM _) = _
  rw [← pauli_coe v, ← RMap_coe_apply, toM_fromM (RMap U (pauli v)).property]

theorem pauli_curlM (U : Cfg L) (A : Bond L → Vec) (p : Plaq L) :
    pauli (curlM (matU U) A p) = curlValueCovariant U (fun b => pauli (A b)) p := by
  simp only [curlM, map_sub, map_add, matU, pauli_conjM, curlValueCovariant, shift_eq]

theorem reH_eq (U : Cfg L) (p : Plaq L) :
    reH (matU U) p = AdalyFormal.Balaban.DeltaPrime.reHolonomy U p := by
  unfold reH AdalyFormal.Balaban.DeltaPrime.reHolonomy
    AdalyFormal.Balaban.DeltaPrime.holonomyElemInv AdalyFormal.Balaban.DeltaPrime.holonomyElem
    AdalyFormal.Target.ClayStatement.periodicPlaquetteHolonomy
  simp only [coe_mul, coe_inv, matU, shift_eq]

theorem imH_eq (U : Cfg L) (p : Plaq L) :
    imH (matU U) p = AdalyFormal.Balaban.DeltaPrime.imHolonomy U p := by
  unfold imH AdalyFormal.Balaban.DeltaPrime.imHolonomy
    AdalyFormal.Balaban.DeltaPrime.holonomyElemInv AdalyFormal.Balaban.DeltaPrime.holonomyElem
    AdalyFormal.Target.ClayStatement.periodicPlaquetteHolonomy
  simp only [coe_mul, coe_inv, matU, shift_eq]

theorem mat_inv_eq (g : SU2) : (g : M2)⁻¹ = ((g⁻¹ : SU2) : M2) := by
  rw [coe_matrix_inv, coe_inv]

theorem Fnu_eq (P : Set (Plaq L)) (U : Cfg L) (ν μ : Fin 3) (y : Site L) :
    Fnu P U ν μ y = AdalyFormal.IngredientFamily.FnuMuLoc P U ν μ y := by
  simp only [Fnu, AdalyFormal.IngredientFamily.FnuMuLoc, imHol,
    AdalyFormal.Balaban.DeltaPrime.imHolonomy, AdalyFormal.Balaban.DeltaPrime.holonomyElemInv,
    AdalyFormal.Balaban.DeltaPrime.holonomyElem, mat_inv_eq]
  rfl

theorem dstarDir_eq (U : Cfg L) (ν : Fin 3) (G : Site L → M2) (x : Site L) :
    dstarDir U ν G x = AdalyFormal.Balaban.SourceJ.DstarDir U ν G x := by
  unfold dstarDir AdalyFormal.Balaban.SourceJ.DstarDir
  rw [AdalyFormal.Balaban.CovariantOperators.conjByAmbient_apply]
  simp only [mat_inv_eq, ← coe_inv, inv_inv, shiftBack_eq]

theorem Jmat_eq (P : Set (Plaq L)) (U : Cfg L) (x : Site L) (μ : Fin 3) :
    Jmat P U x μ = AdalyFormal.IngredientFamily.JfieldLoc P U x μ := by
  have hf : Fnu P U = AdalyFormal.IngredientFamily.FnuMuLoc P U := by
    funext ν μ y; exact Fnu_eq P U ν μ y
  simp only [Jmat, AdalyFormal.IngredientFamily.JfieldLoc, hf, dstarDir_eq]

/-- The headline uses `-JSU2Loc`, hence the matching `+i` source, not `-i`. -/
theorem pauli_Jvec (P : Set (Plaq L)) (U : Cfg L) (b : Bond L) :
    pauli (Jvec P U b) = -AdalyFormal.IngredientFamily.JSU2Loc 1 P U b := by
  have he : ((-AdalyFormal.IngredientFamily.JSU2Loc 1 P U b : SuTwo) : M2) =
      Complex.I • Jmat P U b.1 b.2 := by
    simp [AdalyFormal.IngredientFamily.JSU2Loc, Jmat_eq]
  apply Subtype.ext
  change toM (fromM (Complex.I • Jmat P U b.1 b.2)) = _
  rw [← he, toM_fromM (-AdalyFormal.IngredientFamily.JSU2Loc 1 P U b).property]

theorem Jfield_conjugacy (P : Set (Plaq L)) (U : Cfg L) :
    fieldPauli (Bond L) (Jfield P U) =
      WithLp.toLp 2 (fun b => -AdalyFormal.IngredientFamily.JSU2Loc 1 P U b) := by
  apply PiLp.ext
  intro b
  exact pauli_Jvec P U b

/-- The two `i` factors on edge inputs and the formula's leading `i` reverse
    the commutator. This identity applies separately to each of the six pairs. -/
theorem commutator_sign (X Y : M2) :
    Complex.I • ((Complex.I • X) * (Complex.I • Y) - (Complex.I • Y) * (Complex.I • X)) =
      (Complex.I • Y) * X - (Complex.I • X) * Y := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul, Complex.I_mul_I,
    neg_one_smul, smul_neg]
  abel

/-- One prime-form diagonal, all six pairs and both trace factors accounted for. -/
theorem deltaPrimeAt_eq (U : Cfg L) (A : Bond L → Vec) (p : Plaq L) :
    deltaPrimeAt (matU U) A p = (1 / 2 : ℝ) *
      (AdalyFormal.Balaban.DeltaPrime.deltaPrimeFirstTermTransported U (fun b => pauli (A b)) p +
       AdalyFormal.Balaban.DeltaPrime.deltaPrimeSecondTermTransported U (fun b => pauli (A b)) p) := by
  unfold deltaPrimeAt AdalyFormal.Balaban.DeltaPrime.deltaPrimeFirstTermTransported
    AdalyFormal.Balaban.DeltaPrime.deltaPrimeSecondTermTransported
    AdalyFormal.Balaban.DeltaPrime.commutatorMatrixSumTransported
  rw [← pauli_curlM, pauli_coe, reH_eq, imH_eq]
  simp only [smul_add, commutator_sign, AdalyFormal.Balaban.DeltaPrime.AprimeZW,
    AdalyFormal.Balaban.DeltaPrime.AprimeWX, AdalyFormal.Balaban.DeltaPrime.AprimeXY,
    AdalyFormal.Balaban.DeltaPrime.AprimeYZ, Submodule.coe_neg, RMap_coe_apply, pauli_coe,
    shift_eq, matU, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, ntr]
  ring

end
end CompactDictionary
