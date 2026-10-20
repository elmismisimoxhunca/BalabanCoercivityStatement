/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.SuTwoLogExpCore

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# The maximal torus of `SU(2)`, `exp ∘ log = id` on it, and the CENTRE OBSTRUCTION

Three things live here.

**§2-§4.** The one-parameter subgroup `t ↦ diag(e^{it}, e^{-it})` of `SU(2)`, and the two facts
that make `SuTwoLogExpCore.su2LogExp` an HONEST log/exp pair rather than a decoration:
`su2Exp (t • J) = torus t` for every real `t` (Mathlib's matrix exponential, evaluated), and
`su2Log (torus t) = t • J` for `0 ≤ t < π` — so `exp ∘ log = id` and `log ∘ exp = id` on the whole
principal branch of the torus. Nothing here is a hypothesis; both are computed from Mathlib's
`NormedSpace.exp` and `Real.arccos`.

**§5.** `su2Log` really lands in `su(2)`: its values are **traceless and anti-Hermitian**, proved
for EVERY `g ∈ SU(2)` (not just on the torus). This is what makes §6 apply to our own instance.

**§6 — THE CENTRE OBSTRUCTION, a proved impossibility.** For ANY `P : LogExpAd SU(2) M₂(ℂ)` whose
`ad` is genuine conjugation and whose `log` is traceless at `−1`, the value `P.log (−1) = 0` is
**forced** — the two `LogExpAd` laws leave no freedom at the centre. Hence
`P.exp (P.log (−1)) = P.exp 0`, and if `P` is also normalised by `exp 0 = 1` then `exp ∘ log`
FAILS at `−1` for every such `P`.

This is the precise answer to "does the branch cut at `−1` obstruct `SU(2)`?": it does **not**
obstruct `LogExpAd` (which never assumes `exp ∘ log = id`), and it **provably does** obstruct any
strengthening of `LogExpAd` that adds `exp ∘ log = id` while keeping `log` su(2)-valued. The
structure as written is inhabitable at `SU(2)` precisely because it omits that law.
-/

namespace AdalyFormal.Balaban.SuTwoLogExp

open Matrix
open AdalyFormal.Balaban.BlockedGauge

/-! ## §1. A `2 × 2` diagonal toolkit (entrywise once, algebraic thereafter) -/

/-- `diag(a, b)` as an element of `M₂(ℂ)`. -/
def dg (a b : ℂ) : M2 := Matrix.diagonal ![a, b]

theorem dg_congr {a b c d : ℂ} (h0 : a = c) (h1 : b = d) : dg a b = dg c d := by
  rw [h0, h1]

theorem dg_smul (x a b : ℂ) : x • dg a b = dg (x * a) (x * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.diagonal]

theorem dg_conjTranspose (a b : ℂ) : (dg a b)ᴴ = dg (star a) (star b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.diagonal, Matrix.conjTranspose_apply]

theorem dg_sub (a b c d : ℂ) : dg a b - dg c d = dg (a - c) (b - d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.diagonal]

theorem dg_mul (a b c d : ℂ) : dg a b * dg c d = dg (a * c) (b * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem dg_one : dg 1 1 = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.diagonal, Matrix.one_apply]

theorem dg_det (a b : ℂ) : (dg a b).det = a * b := by
  rw [dg, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem dg_trace (a b : ℂ) : Matrix.trace (dg a b) = a + b := by
  rw [dg, Matrix.trace_diagonal, Fin.sum_univ_two]
  simp

theorem dg_00 (a b : ℂ) : dg a b 0 0 = a := by rw [dg, Matrix.diagonal_apply_eq]; rfl
theorem dg_11 (a b : ℂ) : dg a b 1 1 = b := by rw [dg, Matrix.diagonal_apply_eq]; rfl
theorem dg_01 (a b : ℂ) : dg a b 0 1 = 0 := by
  rw [dg, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1)]
theorem dg_10 (a b : ℂ) : dg a b 1 0 = 0 := by
  rw [dg, Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]

theorem dg_neg_one : dg (-1 : ℂ) (-1) = (-1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.diagonal, Matrix.one_apply]

/-! ## §2. Scalar identities for `e^{it}` -/

theorem cexp_pos_form (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) = Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I :=
  Complex.exp_mul_I _

theorem cexp_neg_form (t : ℝ) :
    Complex.exp (-((t : ℂ) * Complex.I))
      = Complex.cos (t : ℂ) - Complex.sin (t : ℂ) * Complex.I := by
  rw [show -((t : ℂ) * Complex.I) = (-(t : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  ring

theorem cexp_mul_one (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-((t : ℂ) * Complex.I)) = 1 := by
  rw [← Complex.exp_add]
  simp

theorem cexp_mul_one' (t : ℝ) :
    Complex.exp (-((t : ℂ) * Complex.I)) * Complex.exp ((t : ℂ) * Complex.I) = 1 := by
  rw [mul_comm]; exact cexp_mul_one t

theorem cexp_star (t : ℝ) :
    star (Complex.exp ((t : ℂ) * Complex.I)) = Complex.exp (-((t : ℂ) * Complex.I)) := by
  rw [show star (Complex.exp ((t : ℂ) * Complex.I))
      = Complex.exp (star ((t : ℂ) * Complex.I)) from (Complex.exp_conj _).symm]
  congr 1
  simp [Complex.ext_iff]

theorem cexp_star' (t : ℝ) :
    star (Complex.exp (-((t : ℂ) * Complex.I))) = Complex.exp ((t : ℂ) * Complex.I) := by
  rw [← cexp_star t, star_star]

theorem cexp_re (t : ℝ) : (Complex.exp ((t : ℂ) * Complex.I)).re = Real.cos t :=
  Complex.exp_ofReal_mul_I_re t

theorem cexp_neg_re (t : ℝ) : (Complex.exp (-((t : ℂ) * Complex.I))).re = Real.cos t := by
  rw [show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem cexp_sub (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (-((t : ℂ) * Complex.I))
      = ((2 * Real.sin t : ℝ) : ℂ) * Complex.I := by
  rw [cexp_pos_form, cexp_neg_form]
  push_cast
  rw [← Complex.ofReal_sin]
  push_cast
  ring

/-! ## §3. The maximal torus -/

/-- `diag(e^{it}, e^{-it})` as a raw matrix. -/
noncomputable def torusM (t : ℝ) : M2 :=
  dg (Complex.exp ((t : ℂ) * Complex.I)) (Complex.exp (-((t : ℂ) * Complex.I)))

theorem torusM_mem (t : ℝ) : torusM t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, torusM, Matrix.star_eq_conjTranspose, dg_conjTranspose,
      dg_mul, cexp_star, cexp_star', cexp_mul_one, cexp_mul_one']
    exact dg_one
  · rw [torusM, dg_det]
    exact cexp_mul_one t

/-- **The maximal torus of `SU(2)`.** -/
noncomputable def torus (t : ℝ) : SU2 := ⟨torusM t, torusM_mem t⟩

@[simp] theorem coe_torus (t : ℝ) : ((torus t : SU2) : M2) = torusM t := rfl

@[simp] theorem torus_zero : torus 0 = 1 := by
  apply Subtype.ext
  rw [coe_torus, coe_one, torusM]
  refine (dg_congr ?_ ?_).trans dg_one <;> simp

theorem torus_add (s t : ℝ) : torus (s + t) = torus s * torus t := by
  apply Subtype.ext
  rw [coe_torus, coe_mul, coe_torus, coe_torus, torusM, torusM, torusM, dg_mul]
  refine dg_congr ?_ ?_ <;> rw [← Complex.exp_add] <;> congr 1 <;> push_cast <;> ring

/-! ## §4. `J`, the generator, and the two directions of `exp`/`log` on the torus -/

/-- `J = diag(i, −i)`, the generator: `torus t = exp (t • J)`. -/
noncomputable def su2J : M2 := dg Complex.I (-Complex.I)

/-- `ψ(t) = t • J`, the su(2) element whose exponential is `torus t`. -/
noncomputable def psiR (t : ℝ) : M2 := ((t : ℝ) : ℂ) • su2J

theorem psiR_dg (t : ℝ) : psiR t = dg ((t : ℂ) * Complex.I) (-((t : ℂ) * Complex.I)) := by
  rw [psiR, su2J, dg_smul]
  refine dg_congr rfl ?_
  ring

/-- **`exp (t • J) = torus t`** — Mathlib's matrix exponential, evaluated, for EVERY real `t`.
No branch restriction: the exponential is globally defined. -/
theorem su2Exp_psiR (t : ℝ) : su2Exp (psiR t) = torus t := by
  have hexp : NormedSpace.exp (psiR t) = torusM t := by
    rw [psiR_dg, dg, Matrix.exp_diagonal, torusM, dg]
    congr 1
    funext i
    rw [Pi.exp_def]
    fin_cases i <;> simp [← Complex.exp_eq_exp_ℂ]
  have hmem : NormedSpace.exp (psiR t) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [hexp]; exact torusM_mem t
  apply Subtype.ext
  rw [su2Exp_of_mem hmem, hexp, coe_torus]

theorem su2Angle_torus {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ Real.pi) : su2Angle (torus t) = t := by
  rw [su2Angle, coe_torus, torusM, dg_trace]
  rw [show (Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-((t : ℂ) * Complex.I))).re
      = 2 * Real.cos t by rw [Complex.add_re, cexp_re, cexp_neg_re]; ring]
  rw [show 2 * Real.cos t / 2 = Real.cos t by ring]
  exact Real.arccos_cos h0 h1

theorem torusM_sub_conjTranspose (t : ℝ) :
    torusM t - (torusM t)ᴴ = ((2 * Real.sin t : ℝ) : ℂ) • su2J := by
  rw [torusM, dg_conjTranspose, cexp_star, cexp_star', dg_sub, su2J, dg_smul]
  refine dg_congr (cexp_sub t) ?_
  rw [show Complex.exp (-((t : ℂ) * Complex.I)) - Complex.exp ((t : ℂ) * Complex.I)
      = -(Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (-((t : ℂ) * Complex.I))) by ring,
    cexp_sub]
  ring

/-- **`log (torus t) = t • J` on the principal branch `0 ≤ t < π`.**

Together with `su2Exp_psiR` this gives `exp (log g) = g` for every `g` on the torus with
`0 ≤ t < π` — the honest inverse pair, computed, not assumed. -/
theorem su2Log_torus {t : ℝ} (h0 : 0 ≤ t) (h1 : t < Real.pi) : su2Log (torus t) = psiR t := by
  rcases eq_or_lt_of_le h0 with rfl | hpos
  · rw [torus_zero, su2Log_one, psiR]
    simp
  have hsin : Real.sin t ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos h1)
  have hang : su2Angle (torus t) = t := su2Angle_torus h0 (le_of_lt h1)
  have hkap : su2Kappa (torus t) = t / Real.sin t := by rw [su2Kappa, hang]
  rw [su2Log, hkap, coe_torus, torusM_sub_conjTranspose, smul_smul, psiR]
  congr 1
  have hsinC : Complex.sin (t : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_ne_zero.mpr hsin
  push_cast
  field_simp

/-! ## §5. `su2Log` lands in `su(2)`: traceless and anti-Hermitian -/

/-- For `g ∈ SU(2)` the trace is REAL. Proved from `gᴴ = adjugate g` (`det g = 1`), which forces
`g₁₁ = conj g₀₀`. -/
theorem trace_star (g : SU2) : star (Matrix.trace (g : M2)) = Matrix.trace (g : M2) := by
  have hadj : (g : M2)ᴴ = Matrix.adjugate (g : M2) := by
    rw [← coe_matrix_inv, Matrix.inv_def, coe_det]
    simp
  have hadj2 : (g : M2)ᴴ
      = !![(g : M2) 1 1, -(g : M2) 0 1; -(g : M2) 1 0, (g : M2) 0 0] := by
    rw [hadj, Matrix.adjugate_fin_two]
  have h00 : star ((g : M2) 0 0) = (g : M2) 1 1 := by
    have := congrFun (congrFun hadj2 0) 0
    simpa [Matrix.conjTranspose_apply] using this
  have h11 : star ((g : M2) 1 1) = (g : M2) 0 0 := by
    rw [← h00, star_star]
  rw [Matrix.trace_fin_two, star_add, h00, h11]
  ring

/-- **`su2Log g` is traceless for EVERY `g ∈ SU(2)`.** -/
theorem su2Log_traceless (g : SU2) : Matrix.trace (su2Log g) = 0 := by
  rw [su2Log, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose,
    trace_star g, sub_self, smul_zero]

/-- **`su2Log g` is anti-Hermitian for EVERY `g ∈ SU(2)`.** Traceless + anti-Hermitian is exactly
membership in `su(2)`, so `su2Log : SU(2) → su(2)`. -/
theorem su2Log_antiHermitian (g : SU2) : (su2Log g)ᴴ = - su2Log g := by
  have hc : star ((su2Kappa g : ℂ) / 2) = (su2Kappa g : ℂ) / 2 := by
    simp [Complex.star_def, map_div₀, Complex.conj_ofReal]
  rw [su2Log, Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, ← neg_sub ((g : M2)) ((g : M2)ᴴ), smul_neg]

/-! ## §6. THE CENTRE OBSTRUCTION -/

theorem negOne_mem : (-1 : M2) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [← dg_neg_one]
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, dg_conjTranspose, dg_mul]
    refine (dg_congr ?_ ?_).trans dg_one <;> simp
  · rw [dg_det]; norm_num

/-- The centre element `−1 ∈ SU(2)`. -/
def su2NegOne : SU2 := ⟨-1, negOne_mem⟩

@[simp] theorem coe_su2NegOne : ((su2NegOne : SU2) : M2) = -1 := rfl

/-- **`log (−1) = 0` directly**, with no appeal to `log_center_forced`: the closed form has
`(−1) − (−1)ᴴ = 0`, so `su2Kappa`'s junk value `0/0 = 0` at the centre multiplies zero and is
invisible. This is the lemma `SuTwoLogExpCore.su2Kappa`'s docstring points at. -/
@[simp] theorem su2Log_center : su2Log su2NegOne = 0 := by
  rw [su2Log, coe_su2NegOne, show ((-1 : M2))ᴴ = (-1 : M2) by simp]
  simp

theorem su2NegOne_ne_one : su2NegOne ≠ 1 := by
  intro h
  have h2 : ((-1 : M2)) = (1 : M2) := by rw [← coe_su2NegOne, h, coe_one]
  have h3 := congrFun (congrFun h2 0) 0
  norm_num [Matrix.one_apply] at h3

/-- `−1` is central: conjugation fixes it. -/
theorem conj_su2NegOne (g : SU2) : g * su2NegOne * g⁻¹ = su2NegOne := by
  apply Subtype.ext
  rw [coe_mul, coe_mul, coe_inv, coe_su2NegOne]
  rw [show (g : M2) * (-1) = -(g : M2) by simp]
  rw [show (-(g : M2)) * (g : M2)ᴴ = -((g : M2) * (g : M2)ᴴ) by simp]
  rw [mul_star_self]

/-- **A matrix fixed by conjugation by all of `SU(2)` is a scalar** — proved with two explicit
witnesses, `diag(i,−i)` and `[[0,1],[−1,0]]`. -/
theorem adInvariant_isScalar {A : M2} (h : ∀ g : SU2, (g : M2) * A * (g : M2)ᴴ = A) :
    A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1 := by
  have hcomm : ∀ g : SU2, A * (g : M2) = (g : M2) * A := by
    intro g
    have h1 := h g
    calc A * (g : M2) = ((g : M2) * A * (g : M2)ᴴ) * (g : M2) := by rw [h1]
      _ = (g : M2) * A * ((g : M2)ᴴ * (g : M2)) := by rw [Matrix.mul_assoc]
      _ = (g : M2) * A := by rw [star_mul_self, Matrix.mul_one]
  have hu1 : (dg Complex.I (-Complex.I)) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, dg_conjTranspose, dg_mul]
      refine (dg_congr ?_ ?_).trans dg_one <;> simp [Complex.ext_iff]
    · rw [dg_det]
      simp [Complex.ext_iff]
  have hu2 : (!![0, 1; -1, 0] : M2) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_apply, Matrix.one_apply]
    · rw [Matrix.det_fin_two_of]
      ring
  have e1 := hcomm ⟨_, hu1⟩
  have e2 := hcomm ⟨_, hu2⟩
  have g01 := congrFun (congrFun e1 0) 1
  have g10 := congrFun (congrFun e1 1) 0
  have g2 := congrFun (congrFun e2 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, dg_00, dg_01, dg_10, dg_11,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    mul_zero, zero_mul, zero_add, add_zero, mul_one, one_mul] at g01 g10 g2
  have hI : (2 * Complex.I) ≠ 0 := by simp [Complex.ext_iff]
  refine ⟨?_, ?_, ?_⟩
  · have h2 : (2 * Complex.I) * A 0 1 = 0 := by linear_combination -g01
    exact (mul_eq_zero.mp h2).resolve_left hI
  · have h2 : (2 * Complex.I) * A 1 0 = 0 := by linear_combination g10
    exact (mul_eq_zero.mp h2).resolve_left hI
  · linear_combination g2

/-- **THE CENTRE OBSTRUCTION.** For any `LogExpAd SU(2) M₂(ℂ)` whose `ad` is genuine conjugation
and whose `log` is traceless at `−1`, the value `log (−1)` is FORCED to be `0`.

The two `LogExpAd` laws leave no freedom: `−1` is central, so `log_conj` says `log (−1)` is
`Ad`-invariant; `Ad`-invariance forces a scalar; tracelessness forces the scalar to vanish. -/
theorem log_center_forced (P : LogExpAd SU2 M2) (had : ∀ g : SU2, P.ad g = adMap g)
    (htr : Matrix.trace (P.log su2NegOne) = 0) : P.log su2NegOne = 0 := by
  have hinv : ∀ g : SU2, (g : M2) * P.log su2NegOne * (g : M2)ᴴ = P.log su2NegOne := by
    intro g
    have := P.log_conj g su2NegOne
    rw [conj_su2NegOne g, had g, adMap_apply] at this
    exact this.symm
  obtain ⟨h01, h10, h00⟩ := adInvariant_isScalar hinv
  have htr2 : P.log su2NegOne 0 0 + P.log su2NegOne 1 1 = 0 := by
    rw [Matrix.trace_fin_two] at htr; exact htr
  have hz : P.log su2NegOne 0 0 = 0 := by linear_combination htr2 / 2 + h00 / 2
  have hz1 : P.log su2NegOne 1 1 = 0 := by linear_combination hz - h00
  have key : ∀ i : Fin 2, ∀ j : Fin 2, P.log su2NegOne i j = (0 : M2) i j := by
    simp only [Matrix.zero_apply, Fin.forall_fin_two]
    exact ⟨⟨hz, h01⟩, ⟨h10, hz1⟩⟩
  exact Matrix.ext key

/-- **Consequence: `exp ∘ log = id` is UNAVAILABLE at the centre, for every such `P`.**
So `LogExpAd`'s omission of `exp ∘ log = id` is not a convenience — adding it would make the
structure uninhabitable at `SU(2)` by any su(2)-valued logarithm. -/
theorem exp_log_fails_at_center (P : LogExpAd SU2 M2) (had : ∀ g : SU2, P.ad g = adMap g)
    (htr : Matrix.trace (P.log su2NegOne) = 0) (hexp0 : P.exp 0 = 1) :
    P.exp (P.log su2NegOne) ≠ su2NegOne := by
  rw [log_center_forced P had htr, hexp0]
  exact fun h => su2NegOne_ne_one h.symm

/-- Our own instance satisfies the hypotheses, so it exhibits the obstruction concretely. -/
theorem su2LogExp_exp_log_fails_at_center :
    su2LogExp.exp (su2LogExp.log su2NegOne) ≠ su2NegOne :=
  exp_log_fails_at_center su2LogExp (fun _ => rfl) (su2Log_traceless su2NegOne) su2Exp_zero

end AdalyFormal.Balaban.SuTwoLogExp
