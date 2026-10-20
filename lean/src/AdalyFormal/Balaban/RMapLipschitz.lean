/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantOperators
import AdalyFormal.Balaban.SuTwoInner
import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false

/-!
# `RMapLipschitz.lean` — the SHARP `‖U−1‖`-smallness bound for `RMap` (closes `[RMAP-LIP-U1]`)

**What this closes.** `RegularUPerturbation.lean` (`norm_RMap_sub_self_le_two`) had only the CRUDE
per-bond bound `‖RMap(U)X − X‖ ≤ 2‖X‖`, which does NOT vanish at `U = 1` and so gives NO smallness.
This module proves the SHARP bound

  `‖RMap(U)X − X‖ ≤ 2 · frobNorm(U − 1) · ‖X‖`      (`norm_RMap_sub_self_le`)

where `frobNorm M = √(Σ|Mᵢⱼ|²)` is the Frobenius norm of the *full* matrix `U − 1`. At `U = 1` the
bound is `0`, so the single-scale drift `→ 0` as `U → 1` — the genuine `‖U−1‖` smallness that the
CMP99b (3.85)–(3.86) Neumann/random-walk series needs (`‖V(A)G‖ = O(α₁)`, `α₁ ∼ ‖U−1‖`).

## The route (fully self-contained; NO Mathlib matrix-norm instances)

`SuTwoInner.lean`'s module docstring warns that `Matrix (Fin 2) (Fin 2) ℂ` carries competing SCOPED
norm instances (`Matrix.Norms.L2Operator`), a diamond hazard. To avoid it entirely this module uses
a PLAIN real-valued `frobSq M := Σ|Mᵢⱼ|²` (no typeclass), and proves the three matrix-analysis facts
it needs by explicit `2×2` `Complex.normSq` algebra:

- `frobSq_mul_right_isometry` : `frobSq (M·W) = frobSq M` for `W·Wᴴ = 1`  (unitary invariance);
- `frobSq_sub_le`            : `frobSq (A−B) ≤ 2·frobSq A + 2·frobSq B`   (`|a−b|²≤2|a|²+2|b|²`);
- `frobSq_mul_le`            : `frobSq (A·B) ≤ frobSq A · frobSq B`        (Cauchy–Schwarz,
  exact SOS witness `Σ|Aᵢⱼ|²·Σ|Bⱼₖ|² − |ΣAᵢⱼBⱼₖ|² = |A·conj(D) − B·conj(C)|²`).

The commutator identity `RMap(U)X − X = (V·X − X·V)·Uᴴ` with `V = U−1` (using `U·Uᴴ = 1`) then gives
`frobSq(RMap(U)X − X) = frobSq(V·X − X·V) ≤ 4·frobSq(V)·frobSq(X)`, and the SuTwo-norm bridge
`‖Y‖² = ½·frobSq(↑Y)` (from `hsInner_self_eq_sumNormSq`) finishes.

## Scope honesty (unchanged from `RegularUPerturbation.lean`)

This is the sharp form of ONE single-scale per-bond primitive. It does NOT prove regular-`U`
coercivity, does NOT iterate to `k`-uniformity (the multi-scale random-walk expansion, unbuilt), and
does NOT touch the `C`-chain (3.156)–(3.158). It supplies the base `‖U−1‖`-smallness those steps
consume. LAW-19: `RMap`, `hsInner`, `RCLM`, `hsInner_self_eq_sumNormSq` are all imported and reused.
-/

namespace AdalyFormal.Balaban.RMapLipschitz

open AdalyFormal.Balaban.CovariantOperators AdalyFormal.Balaban.SuTwoInner

open scoped Matrix

/-! ## §1 — `frobSq`, the plain Frobenius-square of a full `2×2` complex matrix -/

/-- **`frobSq M = Σ|Mᵢⱼ|²`** — a plain `ℝ`-valued function (no norm typeclass, hence no instance
diamond). This is the *full-matrix* Frobenius square; on `↥SuTwo` it relates to the intrinsic norm
by `‖Y‖² = ½·frobSq(↑Y)` (`norm_sq_eq_half_frobSq`). -/
noncomputable def frobSq (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq (M 0 0) + Complex.normSq (M 0 1) +
    Complex.normSq (M 1 0) + Complex.normSq (M 1 1)

theorem frobSq_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ frobSq M := by
  unfold frobSq
  have h1 := Complex.normSq_nonneg (M 0 0)
  have h2 := Complex.normSq_nonneg (M 0 1)
  have h3 := Complex.normSq_nonneg (M 1 0)
  have h4 := Complex.normSq_nonneg (M 1 1)
  linarith

/-- `frobSq M = (tr(M·Mᴴ))·.re` — the trace form, used only to prove unitary invariance cleanly. -/
theorem frobSq_eq_trace (M : Matrix (Fin 2) (Fin 2) ℂ) :
    frobSq M = (Matrix.trace (M * Mᴴ)).re := by
  have hz : ∀ z : ℂ, (z * star z).re = Complex.normSq z := fun z => by
    rw [← starRingEnd_apply, Complex.mul_conj, Complex.ofReal_re]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Complex.add_re, hz]
  unfold frobSq
  ring

/-- **Unitary right-invariance**: `frobSq (M·W) = frobSq M` whenever `W·Wᴴ = 1`. -/
theorem frobSq_mul_right_isometry (M W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W * Wᴴ = 1) :
    frobSq (M * W) = frobSq M := by
  have key : (M * W) * (M * W)ᴴ = M * Mᴴ := by
    rw [Matrix.conjTranspose_mul]
    rw [show M * W * (Wᴴ * Mᴴ) = M * (W * Wᴴ) * Mᴴ by noncomm_ring, hW, Matrix.mul_one]
  rw [frobSq_eq_trace (M * W), key, ← frobSq_eq_trace M]

/-- **`|a−b|² ≤ 2|a|² + 2|b|²`, entrywise ⇒** `frobSq (A−B) ≤ 2·frobSq A + 2·frobSq B`. -/
theorem frobSq_sub_le (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    frobSq (A - B) ≤ 2 * frobSq A + 2 * frobSq B := by
  have h : ∀ z w : ℂ, Complex.normSq (z - w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
    intro z w
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg (z.re + w.re), sq_nonneg (z.im + w.im)]
  simp only [frobSq, Matrix.sub_apply]
  have h00 := h (A 0 0) (B 0 0)
  have h01 := h (A 0 1) (B 0 1)
  have h10 := h (A 1 0) (B 1 0)
  have h11 := h (A 1 1) (B 1 1)
  linarith

/-- **Submultiplicativity**: `frobSq (A·B) ≤ frobSq A · frobSq B`. The entrywise engine is the exact
Cauchy–Schwarz identity `(|a|²+|b|²)(|c|²+|d|²) = |a·c+b·d|² + |a·c̄' − b·c̄|²` (SOS witness). -/
theorem frobSq_mul_le (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    frobSq (A * B) ≤ frobSq A * frobSq B := by
  have cs : ∀ a b c d : ℂ, Complex.normSq (a * c + b * d) ≤
      (Complex.normSq a + Complex.normSq b) * (Complex.normSq c + Complex.normSq d) := by
    intro a b c d
    have key : (Complex.normSq a + Complex.normSq b) * (Complex.normSq c + Complex.normSq d) =
        Complex.normSq (a * c + b * d) +
          Complex.normSq (a * (starRingEnd ℂ) d - b * (starRingEnd ℂ) c) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [key]
    nlinarith [Complex.normSq_nonneg (a * (starRingEnd ℂ) d - b * (starRingEnd ℂ) c)]
  simp only [frobSq, Matrix.mul_apply, Fin.sum_univ_two]
  have h00 := cs (A 0 0) (A 0 1) (B 0 0) (B 1 0)
  have h01 := cs (A 0 0) (A 0 1) (B 0 1) (B 1 1)
  have h10 := cs (A 1 0) (A 1 1) (B 0 0) (B 1 0)
  have h11 := cs (A 1 0) (A 1 1) (B 0 1) (B 1 1)
  nlinarith [h00, h01, h10, h11, Complex.normSq_nonneg (A 0 0), Complex.normSq_nonneg (A 0 1),
    Complex.normSq_nonneg (A 1 0), Complex.normSq_nonneg (A 1 1)]

#print axioms frobSq_eq_trace
#print axioms frobSq_mul_right_isometry
#print axioms frobSq_sub_le
#print axioms frobSq_mul_le

/-! ## §2 — `frobNorm`, and the `SuTwo`-norm bridge -/

/-- The Frobenius norm of a full `2×2` matrix, `√(Σ|Mᵢⱼ|²)`. This is the quantity in which the
`‖U−1‖`-smallness is measured. -/
noncomputable def frobNorm (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Real.sqrt (frobSq M)

theorem frobNorm_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ frobNorm M := Real.sqrt_nonneg _

theorem frobNorm_sq (M : Matrix (Fin 2) (Fin 2) ℂ) : frobNorm M ^ 2 = frobSq M := by
  unfold frobNorm; rw [Real.sq_sqrt (frobSq_nonneg M)]

/-- **The norm bridge**: `‖Y‖² = ½·frobSq(↑Y)` on `↥SuTwo`. This hands the intrinsic Hilbert-space
norm to the full-matrix `frobSq` machinery. -/
theorem norm_sq_eq_half_frobSq (Y : SuTwo) :
    ‖Y‖ ^ 2 = (1 / 2 : ℝ) * frobSq (Y : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_hsInner, hsInner_self_eq_sumNormSq]
  unfold frobSq
  ring

#print axioms norm_sq_eq_half_frobSq

/-! ## §3 — THE SHARP BOUND -/

/-- **THE SHARP `‖U−1‖`-SMALLNESS BOUND** (closes `[RMAP-LIP-U1]`).
`‖RMap(U)X − X‖ ≤ 2 · frobNorm(U − 1) · ‖X‖`, where `frobNorm(U − 1) = √(Σ|(U−1)ᵢⱼ|²)`.
At `U = 1` the right side is `0`, so `RMap(U)X → X` at rate `frobNorm(U − 1)` — the genuine
first-order smallness the crude `norm_RMap_sub_self_le_two` lacked. Uniform in the RG step `k`
(single scale carries no `k`). -/
theorem norm_RMap_sub_self_le (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    ‖RMap U X - X‖ ≤ 2 * frobNorm ((U : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖X‖ := by
  set Umat := (U : Matrix (Fin 2) (Fin 2) ℂ) with hUmat
  set Xmat := (X : Matrix (Fin 2) (Fin 2) ℂ) with hXmat
  set V := Umat - 1 with hV
  -- unitary facts for `U`
  have hUUH : Umat * Umatᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp U.2.1
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUHU : Umatᴴ * Umatᴴᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    have h := Matrix.mem_unitaryGroup_iff'.mp U.2.1
    rwa [Matrix.star_eq_conjTranspose] at h
  -- Step A: the coerced difference matrix is the commutator times `Uᴴ`.
  have hDmat : ((RMap U X - X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
      = (V * Xmat - Xmat * V) * Umatᴴ := by
    rw [Submodule.coe_sub, RMap_coe_apply]
    have : (V * Xmat - Xmat * V) * Umatᴴ = Umat * Xmat * Umatᴴ - Xmat * (Umat * Umatᴴ) := by
      rw [hV]; noncomm_ring
    rw [this, hUUH, Matrix.mul_one]
  -- Step B: the frobSq estimate.
  have hfrobB : frobSq ((RMap U X - X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
      ≤ 4 * frobSq V * frobSq Xmat := by
    rw [hDmat, frobSq_mul_right_isometry _ _ hUHU]
    calc frobSq (V * Xmat - Xmat * V)
        ≤ 2 * frobSq (V * Xmat) + 2 * frobSq (Xmat * V) := frobSq_sub_le _ _
      _ ≤ 2 * (frobSq V * frobSq Xmat) + 2 * (frobSq Xmat * frobSq V) := by
          have h1 := frobSq_mul_le V Xmat
          have h2 := frobSq_mul_le Xmat V
          have hVnn := frobSq_nonneg V
          have hXnn := frobSq_nonneg Xmat
          nlinarith [h1, h2, hVnn, hXnn]
      _ = 4 * frobSq V * frobSq Xmat := by ring
  -- Step C+D: pass through the norm bridge and take square roots.
  have hnormsq : ‖RMap U X - X‖ ^ 2 ≤ (2 * frobNorm V * ‖X‖) ^ 2 := by
    have hL : ‖RMap U X - X‖ ^ 2 =
        (1 / 2 : ℝ) * frobSq ((RMap U X - X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) :=
      norm_sq_eq_half_frobSq _
    have hXsq : ‖X‖ ^ 2 = (1 / 2 : ℝ) * frobSq Xmat := norm_sq_eq_half_frobSq X
    have hR : (2 * frobNorm V * ‖X‖) ^ 2 = 4 * frobSq V * ‖X‖ ^ 2 := by
      rw [mul_pow, mul_pow, frobNorm_sq]; ring
    rw [hL, hR, hXsq]
    nlinarith [hfrobB, frobSq_nonneg V, frobSq_nonneg Xmat]
  have hb : 0 ≤ 2 * frobNorm V * ‖X‖ := by
    have := frobNorm_nonneg V
    have := norm_nonneg X
    positivity
  have := Real.sqrt_le_sqrt hnormsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hb] at this

#print axioms norm_RMap_sub_self_le

/-! ## §4 — operator smallness, vanishing at `U = 1` (diamond-free form)

The literal continuous-linear-map operator norm `‖RCLM U − id‖_op` is NOT stated here: the
`Norm (↥SuTwo →L[ℝ] ↥SuTwo)` instance fails to synthesize because of the `NormedSpace ℝ SuTwo`
instance diamond that `SuTwoInner.lean`'s module docstring flags (the `NormedAddCommGroup` under the
`InnerProductSpace`-derived `NormedSpace` is a different instance source than
`instNormedAddCommGroupSuTwo`).
Fighting that diamond adds no mathematical content: the *uniform-in-`X`* bound
`∀ X, ‖RMap U X − X‖ ≤ 2·frobNorm(U−1)·‖X‖` (`norm_RMap_sub_self_le`) is EXACTLY the operator-norm
smallness — it states the operator is Lipschitz-close to the identity with constant
`2·frobNorm(U−1)`. Here we record that this constant VANISHES at `U = 1`. -/

/-- `frobSq 0 = 0`. -/
@[simp] theorem frobSq_zero : frobSq (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [frobSq]

/-- `frobNorm 0 = 0`. -/
@[simp] theorem frobNorm_zero : frobNorm (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [frobNorm]

/-- **Vanishing at `U = 1`**: the sharp bound's constant is `0` at the trivial background, so the
per-bond drift is exactly `0` there — the operator-smallness content of "`RMap(U) → id` as `U → 1`".
`‖RMap(1)X − X‖ ≤ 0`, hence `= 0` (consistent with `RMap_one`). -/
theorem norm_RMap_one_sub_self_le_zero (X : SuTwo) :
    ‖RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) X - X‖ ≤ 0 := by
  have h := norm_RMap_sub_self_le (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) X
  have h1 : ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1 = 0 := by
    simp
  rw [h1, frobNorm_zero] at h
  simpa using h

#print axioms norm_RMap_one_sub_self_le_zero

end AdalyFormal.Balaban.RMapLipschitz
