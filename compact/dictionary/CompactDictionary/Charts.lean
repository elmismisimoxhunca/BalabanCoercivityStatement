import CompactDictionary.Coordinates
import AdalyFormal.Balaban.Bch2

/-!
The total compact/frozen SU(2) chart dictionary. These statements include zero
radius and the negative-identity branch; no global `exp (log g) = g` is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace CompactDictionary

open BalabanCompact
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.RegularityGap (Yof real_smul_eq su2Log_eq_kappa_smul)
open AdalyFormal.Balaban.Bch2 (nu IsSu2)
open AdalyFormal.Balaban.CovariantOperators (suTwo mem_suTwo_iff)

noncomputable section

theorem nu_toM (v : Vec) : nu (toM v) = ‖v‖ := by
  rw [nu, ← frobSq_eq, frobSq_toM]
  simp [Real.sqrt_sq (norm_nonneg v)]

/-- The compact exponential is the frozen exponential, including at radius zero. -/
theorem suExpM_eq (v : Vec) : suExpM v = (su2Exp (toM v) : M2) := by
  rw [AdalyFormal.Balaban.Bch2.exp_form ⟨toM_skew v, toM_trace v⟩, nu_toM]
  by_cases hv : v = 0
  · subst v
    simp [suExpM, toM]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    simp [suExpM, Real.sinc_of_ne_zero hn, div_eq_mul_inv]

theorem suExpM_mem (v : Vec) : suExpM v ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [suExpM_eq]
  exact (su2Exp (toM v)).property

/-- The frozen exponential's fallback branch is unreachable on Pauli inputs. -/
theorem suExpM_eq_exp (v : Vec) : suExpM v = NormedSpace.exp (toM v) := by
  rw [suExpM_eq, su2Exp_of_mem
    (AdalyFormal.Balaban.ClassPropagationUbar.exp_mem_special (toM_skew v) (toM_trace v))]

theorem suAngle_eq (g : SU2) : suAngle g = su2Angle g := by
  simp [suAngle, su2Angle]

/-- Compare coordinates first: this avoids assuming a chart inverse off SU(2). -/
theorem suLog_eq_fromM (g : SU2) : suLog g = fromM (su2Log g) := by
  rw [su2Log_eq_kappa_smul, real_smul_eq, fromM_smul]
  unfold suLog
  rw [suAngle_eq]
  change (if su2Angle g = 0 ∨ Real.sin (su2Angle g) = 0 then 0
    else (su2Angle g / Real.sin (su2Angle g)) •
      fromM ((g : M2) - Real.cos (su2Angle g) • (1 : M2))) = _
  by_cases h : su2Angle g = 0 ∨ Real.sin (su2Angle g) = 0
  · rw [if_pos h]
    rcases h with h | h <;> simp [su2Kappa, h]
  · rw [if_neg h]
    simp only [su2Kappa, Yof, real_smul_eq]

/-- Totalized equality, including the branch cut and identity. -/
theorem toM_suLog (g : SU2) : toM (suLog g) = su2Log g := by
  rw [suLog_eq_fromM]
  apply toM_fromM
  rw [mem_suTwo_iff]
  exact ⟨su2Log_antiHermitian g, su2Log_traceless g⟩

theorem suLogM_coe (g : SU2) : suLogM (g : M2) = suLog g := rfl

theorem rawCoords_suLogM (g : SU2) : rawCoords (suLogM (g : M2)) =
    AdalyFormal.IngredientFamilyR2.fromM2 (su2Log g) := by
  rw [suLogM_coe, suLog_eq_fromM, rawCoords_fromM]

@[simp] theorem suLog_one : suLog (1 : SU2) = 0 := by
  rw [suLog_eq_fromM, su2Log_one]
  ext i; fin_cases i <;> simp [fromM]

@[simp] theorem suLog_negOne : suLog su2NegOne = 0 := by
  rw [suLog_eq_fromM, su2Log_center]
  ext i; fin_cases i <;> simp [fromM]

/-- Explicitly retain the cut's junk value: exponentiating it gives `1`, not `-1`. -/
theorem suExpM_suLog_negOne : suExpM (suLog su2NegOne) = (1 : M2) := by
  rw [suExpM_eq, toM_suLog, su2Log_center, su2Exp_zero, coe_one]

end
end CompactDictionary
