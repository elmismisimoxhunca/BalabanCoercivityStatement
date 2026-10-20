/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.SuTwoLogExpTorus

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# How far the `SU(2)` log/exp pair is HONEST — two residuals of `SuTwoLogExpTorus`, closed

`SuTwoLogExpTorus` proved `exp (log g) = g` only on the maximal torus, and left `κ(g) = θ/sin θ`
with Lean's junk value `0/0 = 0` at `g = ±1` without characterising where else it could be junk.
Both are closed here.

**§1 — `exp ∘ log = id` on every CONJUGATE of the principal-branch torus.** `su2Log` and `su2Exp`
are both `Ad`-equivariant (that is literally the content of the two `LogExpAd` laws), so the torus
computation propagates along conjugation for free. The resulting family
`{h · torus t · h⁻¹ : 0 ≤ t < π}` is conjugation-closed and is the whole of `SU(2)` minus the
centre element `−1`; **that last identification is NOT proved here.**

**§2 — `sin θ(g) = 0` happens ONLY at `g = ±1`.** Proved from the `SU(2)` entry relations
(`gᴴ = adjugate g` when `det g = 1`) plus `|g₀₀|² + |g₀₁|² = 1`: `tr g = 2` forces `g = 1` and
`tr g = −2` forces `g = −1`. So `κ` is the honest `θ/sin θ` everywhere except at the two central
elements, where the junk value multiplies `g − gᴴ = 0` and is therefore invisible.
-/

namespace AdalyFormal.Balaban.SuTwoLogExp

open Matrix
open AdalyFormal.Balaban.BlockedGauge

/-! ## §1. `exp ∘ log = id` on the conjugates of the principal branch -/

/-- **`exp (log g) = g` for every conjugate of a principal-branch torus element.**

Both maps are `Ad`-equivariant, so the torus computation of `SuTwoLogExpTorus` propagates. The
family is conjugation-closed and strictly larger than the torus. -/
theorem su2_exp_log_conjTorus (h : SU2) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < Real.pi) :
    su2Exp (su2Log (h * torus t * h⁻¹)) = h * torus t * h⁻¹ := by
  rw [su2_log_conj h (torus t), su2Log_torus h0 h1, su2_exp_ad h (psiR t), su2Exp_psiR]

/-- The same statement in the shape a consumer wants: `exp ∘ log` is the identity on the set
`conjPrincipal`. -/
def conjPrincipal (g : SU2) : Prop :=
  ∃ (h : SU2) (t : ℝ), 0 ≤ t ∧ t < Real.pi ∧ g = h * torus t * h⁻¹

theorem su2_exp_log_of_conjPrincipal {g : SU2} (hg : conjPrincipal g) : su2Exp (su2Log g) = g := by
  obtain ⟨h, t, h0, h1, rfl⟩ := hg
  exact su2_exp_log_conjTorus h h0 h1

/-- The family is not just the torus: it is closed under conjugation by construction, and it
contains the identity (`t = 0`). -/
theorem conjPrincipal_one : conjPrincipal 1 :=
  ⟨1, 0, le_refl 0, Real.pi_pos, by rw [torus_zero]; group⟩

theorem conjPrincipal_conj {g : SU2} (hg : conjPrincipal g) (k : SU2) :
    conjPrincipal (k * g * k⁻¹) := by
  obtain ⟨h, t, h0, h1, rfl⟩ := hg
  exact ⟨k * h, t, h0, h1, by group⟩

/-! ## §2. `SU(2)` entry relations, and where `sin θ` can vanish -/

/-- `gᴴ = adjugate g` for `g ∈ SU(2)` (`det g = 1`). -/
theorem su2_conjTranspose_eq_adjugate (g : SU2) :
    (g : M2)ᴴ = !![(g : M2) 1 1, -(g : M2) 0 1; -(g : M2) 1 0, (g : M2) 0 0] := by
  have hadj : (g : M2)ᴴ = Matrix.adjugate (g : M2) := by
    rw [← coe_matrix_inv, Matrix.inv_def, coe_det]
    simp
  rw [hadj, Matrix.adjugate_fin_two]

theorem su2_e11 (g : SU2) : (g : M2) 1 1 = star ((g : M2) 0 0) := by
  have := congrFun (congrFun (su2_conjTranspose_eq_adjugate g) 0) 0
  simpa [Matrix.conjTranspose_apply] using this.symm

theorem su2_e10 (g : SU2) : (g : M2) 1 0 = - star ((g : M2) 0 1) := by
  have := congrFun (congrFun (su2_conjTranspose_eq_adjugate g) 0) 1
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at this
  have h2 := congrArg star this
  rwa [star_star, star_neg] at h2

/-- `|g₀₀|² + |g₀₁|² = 1`. -/
theorem su2_normSq (g : SU2) :
    Complex.normSq ((g : M2) 0 0) + Complex.normSq ((g : M2) 0 1) = 1 := by
  have hdet : (g : M2) 0 0 * (g : M2) 1 1 - (g : M2) 0 1 * (g : M2) 1 0 = 1 := by
    have := coe_det g
    rwa [Matrix.det_fin_two] at this
  rw [su2_e11 g, su2_e10 g] at hdet
  have : (g : M2) 0 0 * star ((g : M2) 0 0) + (g : M2) 0 1 * star ((g : M2) 0 1) = 1 := by
    linear_combination hdet
  have hre := congrArg Complex.re this
  simpa [Complex.mul_conj, Complex.add_re, Complex.ofReal_re] using hre

/-- **`tr g = 2` forces `g = 1`.** -/
theorem su2_trace_two (g : SU2) (h : Matrix.trace (g : M2) = 2) : g = 1 := by
  have htr : (g : M2) 0 0 + (g : M2) 1 1 = 2 := by rwa [Matrix.trace_fin_two] at h
  rw [su2_e11 g] at htr
  have hre : ((g : M2) 0 0).re = 1 := by
    have h' := congrArg Complex.re htr
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at h'
    have h2 : Complex.re (2 : ℂ) = 2 := by norm_num
    rw [h2] at h'
    linarith
  have hns : Complex.normSq ((g : M2) 0 0) + Complex.normSq ((g : M2) 0 1) = 1 := su2_normSq g
  have hge : (1 : ℝ) ≤ Complex.normSq ((g : M2) 0 0) := by
    have : Complex.normSq ((g : M2) 0 0)
        = ((g : M2) 0 0).re ^ 2 + ((g : M2) 0 0).im ^ 2 := by
      simp [Complex.normSq_apply]; ring
    rw [this, hre]
    nlinarith [sq_nonneg ((g : M2) 0 0).im]
  have h01 : Complex.normSq ((g : M2) 0 1) = 0 := by
    have := Complex.normSq_nonneg ((g : M2) 0 1)
    linarith
  have he01 : (g : M2) 0 1 = 0 := by
    rwa [Complex.normSq_eq_zero] at h01
  have him : ((g : M2) 0 0).im = 0 := by
    have hsq : Complex.normSq ((g : M2) 0 0) = 1 := by linarith
    have : ((g : M2) 0 0).re ^ 2 + ((g : M2) 0 0).im ^ 2 = 1 := by
      rw [← hsq]; simp [Complex.normSq_apply]; ring
    rw [hre] at this
    nlinarith [sq_nonneg ((g : M2) 0 0).im]
  have he00 : (g : M2) 0 0 = 1 := by
    apply Complex.ext <;> simp [hre, him]
  apply Subtype.ext
  rw [coe_one]
  have key : ∀ i : Fin 2, ∀ j : Fin 2, (g : M2) i j = (1 : M2) i j := by
    simp only [Fin.forall_fin_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
      (by decide : (0 : Fin 2) ≠ 1), (by decide : (1 : Fin 2) ≠ 0)]
    refine ⟨⟨he00, he01⟩, ?_, ?_⟩
    · rw [su2_e10 g, he01]; simp
    · rw [su2_e11 g, he00]; simp
  exact Matrix.ext key

/-- **`tr g = −2` forces `g = −1`.** -/
theorem su2_trace_neg_two (g : SU2) (h : Matrix.trace (g : M2) = -2) : g = su2NegOne := by
  have hmem := su2NegOne.2
  have hg : Matrix.trace ((su2NegOne * g : SU2) : M2) = 2 := by
    rw [coe_mul, coe_su2NegOne]
    rw [show (-1 : M2) * (g : M2) = -(g : M2) by simp, Matrix.trace_neg, h]
    ring
  have := su2_trace_two (su2NegOne * g) hg
  have hinv : su2NegOne * su2NegOne = 1 := by
    apply Subtype.ext
    rw [coe_mul, coe_su2NegOne, coe_one]
    simp
  calc g = su2NegOne * (su2NegOne * g) := by rw [← mul_assoc, hinv, one_mul]
    _ = su2NegOne * 1 := by rw [this]
    _ = su2NegOne := mul_one _

/-- `θ(g) ∈ [0, π]`, from `Real.arccos`'s range. -/
theorem su2Angle_mem (g : SU2) : 0 ≤ su2Angle g ∧ su2Angle g ≤ Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- **`sin θ(g) = 0` only at the two central elements.** So `κ(g) = θ/sin θ` is Lean's junk
`0/0 = 0` exactly at `g = ±1`, where it multiplies `g − gᴴ = 0` and is invisible. -/
theorem sin_su2Angle_ne_zero (g : SU2) (h1 : g ≠ 1) (h2 : g ≠ su2NegOne) :
    Real.sin (su2Angle g) ≠ 0 := by
  obtain ⟨hlo, hhi⟩ := su2Angle_mem g
  rcases eq_or_lt_of_le hlo with hz | hpos
  · exfalso
    have harc : Real.arccos ((Matrix.trace (g : M2)).re / 2) = 0 := by
      rw [← su2Angle]; exact hz.symm
    have hx : 1 ≤ (Matrix.trace (g : M2)).re / 2 := Real.arccos_eq_zero.mp harc
    have hre : (Matrix.trace (g : M2)).re = 2 := by
      have hb : (Matrix.trace (g : M2)).re ≤ 2 := by
        have := su2_normSq g
        have hns : Complex.normSq ((g : M2) 0 0) ≤ 1 := by
          have := Complex.normSq_nonneg ((g : M2) 0 1); linarith [su2_normSq g]
        have hsq : ((g : M2) 0 0).re ^ 2 ≤ 1 := by
          have : Complex.normSq ((g : M2) 0 0)
              = ((g : M2) 0 0).re ^ 2 + ((g : M2) 0 0).im ^ 2 := by
            simp [Complex.normSq_apply]; ring
          nlinarith [sq_nonneg ((g : M2) 0 0).im]
        have htr2 : (Matrix.trace (g : M2)).re = 2 * ((g : M2) 0 0).re := by
          rw [Matrix.trace_fin_two, su2_e11 g]
          simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
          ring
        nlinarith [hsq]
      linarith
    have htr : Matrix.trace (g : M2) = 2 := by
      apply Complex.ext
      · simpa using hre
      · have := trace_star g
        have him : (Matrix.trace (g : M2)).im = 0 := by
          have h' := congrArg Complex.im this
          simp only [Complex.star_def, Complex.conj_im] at h'
          linarith
        simpa using him
    exact h1 (su2_trace_two g htr)
  rcases eq_or_lt_of_le hhi with hpi | hlt
  · exfalso
    have harc : Real.arccos ((Matrix.trace (g : M2)).re / 2) = Real.pi := by
      rw [← su2Angle]; exact hpi
    have hx : (Matrix.trace (g : M2)).re / 2 ≤ -1 := Real.arccos_eq_pi.mp harc
    have hb : -2 ≤ (Matrix.trace (g : M2)).re := by
      have hns : Complex.normSq ((g : M2) 0 0) ≤ 1 := by
        have := Complex.normSq_nonneg ((g : M2) 0 1); linarith [su2_normSq g]
      have hsq : ((g : M2) 0 0).re ^ 2 ≤ 1 := by
        have : Complex.normSq ((g : M2) 0 0)
            = ((g : M2) 0 0).re ^ 2 + ((g : M2) 0 0).im ^ 2 := by
          simp [Complex.normSq_apply]; ring
        nlinarith [sq_nonneg ((g : M2) 0 0).im]
      have htr2 : (Matrix.trace (g : M2)).re = 2 * ((g : M2) 0 0).re := by
        rw [Matrix.trace_fin_two, su2_e11 g]
        simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
        ring
      nlinarith [hsq]
    have hre : (Matrix.trace (g : M2)).re = -2 := by linarith
    have htr : Matrix.trace (g : M2) = -2 := by
      apply Complex.ext
      · simpa using hre
      · have := trace_star g
        have him : (Matrix.trace (g : M2)).im = 0 := by
          have h' := congrArg Complex.im this
          simp only [Complex.star_def, Complex.conj_im] at h'
          linarith
        simpa using him
    exact h2 (su2_trace_neg_two g htr)
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)

end AdalyFormal.Balaban.SuTwoLogExp
