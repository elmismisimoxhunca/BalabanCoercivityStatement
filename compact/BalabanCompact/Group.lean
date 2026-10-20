import BalabanCompact.Basic

/-!
# `exp` lands in `SU(2)`

Closed form `cos ‖v‖ · 1 + sinc ‖v‖ · (i v·σ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace BalabanCompact

open Complex Matrix

private lemma skew0 : (Emat 0)ᴴ = -Emat 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Emat, Matrix.conjTranspose_apply]

private lemma skew1 : (Emat 1)ᴴ = -Emat 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Emat, Matrix.conjTranspose_apply]

private lemma skew2 : (Emat 2)ᴴ = -Emat 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Emat, Matrix.conjTranspose_apply]

private lemma tr0 : (Emat 0).trace = 0 := by simp [Emat, Matrix.trace_fin_two]
private lemma tr1 : (Emat 1).trace = 0 := by simp [Emat, Matrix.trace_fin_two]
private lemma tr2 : (Emat 2).trace = 0 := by simp [Emat, Matrix.trace_fin_two]

lemma toM_skew (v : Vec) : (toM v)ᴴ = -toM v := by
  simp [toM, Fin.sum_univ_three, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    star_trivial, skew0, skew1, skew2, smul_neg]
  abel

lemma toM_trace (v : Vec) : (toM v).trace = 0 := by
  unfold toM
  simp only [Matrix.trace_sum, Matrix.trace_smul]
  refine Finset.sum_eq_zero fun i _ => ?_
  fin_cases i <;> simp [tr0, tr1, tr2]

lemma fromM_toM (v : Vec) : fromM (toM v) = v := by
  ext i
  fin_cases i <;>
    simp [fromM, toM, Fin.sum_univ_three, Emat, Matrix.smul_apply, Matrix.add_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      mul_comm I, Complex.I_mul_I]

lemma Emat_mul (i j : Fin 3) :
    Emat i * Emat j =
      (if i = j then -1 else 0) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      + (if i = 0 ∧ j = 1 then -1 else if i = 1 ∧ j = 0 then 1 else 0) • Emat 2
      + (if i = 1 ∧ j = 2 then -1 else if i = 2 ∧ j = 1 then 1 else 0) • Emat 0
      + (if i = 2 ∧ j = 0 then -1 else if i = 0 ∧ j = 2 then 1 else 0) • Emat 1 := by
  fin_cases i <;> fin_cases j <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Emat, Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply]

lemma toM_sq (v : Vec) : toM v * toM v = -‖v‖ ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hnorm : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_three, pow_two]
  unfold toM
  simp only [Fin.sum_univ_three, add_mul, mul_add, smul_mul, mul_smul, smul_smul]
  simp only [Fin.isValue, Algebra.mul_smul_comm, Emat_mul, ↓reduceIte, Int.reduceNeg, neg_smul, one_smul,
    zero_ne_one, and_false, and_true, zero_smul, add_zero, Fin.reduceEq, and_self, smul_neg, one_ne_zero, zero_add]
  rw [hnorm, pow_two, pow_two, pow_two]
  module

lemma sinc_sq_mul (r : ℝ) : (Real.sinc r) ^ 2 * r ^ 2 = (Real.sin r) ^ 2 := by
  rcases eq_or_ne r 0 with h | h
  · rw [h, Real.sinc_zero, Real.sin_zero]; norm_num
  · rw [Real.sinc_of_ne_zero h]; field_simp [h]; try ring


end BalabanCompact
