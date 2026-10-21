import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
Total inverse transport on a split supported space. No nontriviality, finite
 dimension or invertibility hypothesis is needed for the masked identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CompactDictionary

noncomputable section

/-- Ring equivalences reflect units; arbitrary ring homomorphisms need not. -/
theorem inverse_ringEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) (a : R) :
    Ring.inverse (e a) = e (Ring.inverse a) := by
  by_cases ha : IsUnit a
  · have hea : IsUnit (e a) := ha.map e.toMonoidHom
    have hmul : e a * e (Ring.inverse a) = 1 := by
      rw [← e.map_mul, Ring.mul_inverse_cancel a ha, e.map_one]
    calc Ring.inverse (e a) = Ring.inverse (e a) * 1 := (mul_one _).symm
      _ = Ring.inverse (e a) * (e a * e (Ring.inverse a)) := by rw [hmul]
      _ = e (Ring.inverse a) := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hea, one_mul]
  · have hea : ¬ IsUnit (e a) := fun h => ha (by simpa using h.map e.symm.toMonoidHom)
    rw [Ring.inverse_non_unit _ hea, Ring.inverse_non_unit _ ha, e.map_zero]

section Split
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (i : E →L[ℝ] H) (p : H →L[ℝ] E) (hpi : p.comp i = 1)

/-- Extend by identity on the complement of the supported space. -/
def pad (A : E →L[ℝ] E) : H →L[ℝ] H := i.comp (A.comp p) + (1 - i.comp p)

include hpi

theorem retract_apply (x : E) : p (i x) = x :=
  congrArg (fun f : E →L[ℝ] E => f x) hpi

omit hpi in
theorem pad_apply (A : E →L[ℝ] E) (x : H) : pad i p A x = i (A (p x)) + (x - i (p x)) := rfl

theorem pad_i (A : E →L[ℝ] E) (x : E) : pad i p A (i x) = i (A x) := by
  rw [pad_apply, retract_apply i p hpi, sub_self, add_zero]

theorem p_pad (A : E →L[ℝ] E) (x : H) : p (pad i p A x) = A (p x) := by
  rw [pad_apply, map_add, map_sub, retract_apply i p hpi, retract_apply i p hpi,
    sub_self, add_zero]

omit hpi in
theorem pad_one : pad i p (1 : E →L[ℝ] E) = 1 := by
  ext x
  simp only [pad_apply, one_apply_eq_self]
  abel

theorem pad_mul (A B : E →L[ℝ] E) : pad i p (A * B) = pad i p A * pad i p B := by
  ext x
  simp only [mul_apply_eq_comp, pad_apply, map_add, map_sub,
    retract_apply i p hpi]
  abel

/-- Reflect units by compressing a two-sided inverse. -/
theorem pad_isUnit_iff (A : E →L[ℝ] E) : IsUnit (pad i p A) ↔ IsUnit A := by
  constructor
  · rintro ⟨u, hu⟩
    let B : E →L[ℝ] E := p.comp ((↑u⁻¹ : H →L[ℝ] H).comp i)
    have hleft : A * B = 1 := by
      ext x
      change A (p ((↑u⁻¹ : H →L[ℝ] H) (i x))) = x
      rw [← p_pad i p hpi A, ← hu]
      change p (((u : H →L[ℝ] H) * ↑u⁻¹) (i x)) = x
      rw [Units.mul_inv]
      exact retract_apply i p hpi x
    have hright : B * A = 1 := by
      ext x
      change p ((↑u⁻¹ : H →L[ℝ] H) (i (A x))) = x
      rw [← pad_i i p hpi A, ← hu]
      change p (((↑u⁻¹ : H →L[ℝ] H) * ↑u) (i x)) = x
      rw [Units.inv_mul]
      exact retract_apply i p hpi x
    exact ⟨⟨A, B, hleft, hright⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨⟨pad i p ↑u, pad i p ↑u⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← pad_mul i p hpi, Units.mul_inv, pad_one]
    · rw [← pad_mul i p hpi, Units.inv_mul, pad_one]

/-- The unmasked block inverse is valid only in the unit branch. -/
theorem inverse_pad_of_isUnit (A : E →L[ℝ] E) (ha : IsUnit A) :
    Ring.inverse (pad i p A) = pad i p (Ring.inverse A) := by
  have hp := (pad_isUnit_iff i p hpi A).mpr ha
  have hmul : pad i p A * pad i p (Ring.inverse A) = 1 := by
    rw [← pad_mul i p hpi, Ring.mul_inverse_cancel A ha, pad_one]
  calc Ring.inverse (pad i p A) = Ring.inverse (pad i p A) * 1 := (mul_one _).symm
    _ = Ring.inverse (pad i p A) * (pad i p A * pad i p (Ring.inverse A)) := by rw [hmul]
    _ = pad i p (Ring.inverse A) := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hp, one_mul]

/-- Singular branches are zero on both spaces. The final mask cannot be dropped. -/
theorem inverse_pad_mask (A : E →L[ℝ] E) :
    (Ring.inverse (pad i p A)).comp (i.comp p) = i.comp ((Ring.inverse A).comp p) := by
  by_cases ha : IsUnit A
  · rw [inverse_pad_of_isUnit i p hpi A ha]
    ext x
    exact pad_i i p hpi (Ring.inverse A) (p x)
  · have hp : ¬ IsUnit (pad i p A) := fun h => ha ((pad_isUnit_iff i p hpi A).mp h)
    rw [Ring.inverse_non_unit _ hp, Ring.inverse_non_unit _ ha]
    simp

end Split
end
end CompactDictionary
