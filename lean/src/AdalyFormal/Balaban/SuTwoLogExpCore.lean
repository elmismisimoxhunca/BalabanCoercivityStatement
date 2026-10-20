/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BlockedGaugeCore
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `LogExpAd` AT `SU(2)` — the instance the campaign's only group actually needs

`BlockedGaugeCore.LogExpAd G 𝔤` packages the `exp[i·]`/`(1/i)log` pair of CMP109 (0.4) with
exactly two laws (`log_conj`, `exp_ad`) and the requirement that each `Ad g` be a `ℚ`-linear
endomorphism of `𝔤`. Concrete inhabitants existed for `Multiplicative ℚ` and for a group algebra;
**none for `SU(2)`**.

This module supplies one, with

* `G := Matrix.specialUnitaryGroup (Fin 2) ℂ` — the campaign's gauge group;
* `𝔤 := Matrix (Fin 2) (Fin 2) ℂ` — the ambient matrix algebra;
* `exp := ` **Mathlib's matrix exponential** `NormedSpace.exp`, totalised into `SU(2)` by a guard
  (see `su2Exp` for the exact statement of the guard and what is and is not proved about it);
* `log := ` the **principal logarithm of `SU(2)`** in closed form,
  `log g = (θ(g) / sin θ(g) / 2) • (g − gᴴ)` with `θ(g) = arccos (tr g / 2)`;
* `ad g := ` genuine conjugation `A ↦ g A gᴴ`.

**NORMALIZATION, stated because a wrong docstring on `su2Log` cost a downstream lane real work
(corrected 2026-07-30).** The `LogExpAd` STRUCTURE is described above as (0.4)'s `exp[i·]`/`(1/i)log`
pair. **This instance realizes it in the other, equivalent normalization**: `exp` is plain
`NormedSpace.exp` and `log` is the plain `𝔰𝔲(2)`-valued (anti-Hermitian) logarithm, with no `i` on
either side. The two laws cannot tell them apart — `log_conj` is invariant under any rescaling of
`log`, and `exp_ad` under the matching rescaling of `exp` — so BOTH normalizations inhabit
`LogExpAd`, and the structure is blind to which one a given instance uses. The conversion is
`(0.4)'s (1/i) log g = −i · su2Log g`, and the two `i`s of (0.4) cancel in the composite
(`BlockingLinkEstimate`: `exp[i Σ w (1/i) log X] = exp[Σ w log X]`), which is why nothing downstream
broke — but anything that reads `log` as an ALGEBRA-VALUED FIELD must use `su2Log`'s normalization,
not (0.4)'s. See `su2Log`'s docstring in §4.

## `Module ℚ` is NOT an obstruction — measured, not argued

`LogExpAd` requires `[AddCommGroup 𝔤] [Module ℚ 𝔤]`. `su(2)` is a **real** vector space, so the
`ℚ` looked like a typing obstruction. It is not: `Module ℚ (Matrix (Fin 2) (Fin 2) ℂ)` synthesises
in this Mathlib pin (`Matrix.module` from `Module ℚ ℂ`, itself from `ℂ`'s `DivisionRing`+`CharZero`
structure). Every `ℝ`-vector space is a `ℚ`-vector space by restriction of scalars; the `ℚ` in
`LogExpAd` is a **weakening**, not a strengthening, and it is exactly right for (0.4) because every
weight appearing there (`|G(y,x)|⁻¹`, `L^{-d}`) is rational. `adMap g` below is `ℂ`-linear, hence a
fortiori `ℚ`-linear, and is built as a `ℚ`-linear map with no scalar-restriction gymnastics.

## The branch cut at `−1` is NOT an obstruction to the two laws — and that is a theorem

Matrix `log` on `SU(2)` is genuinely multivalued at the centre element `−1`. It does not obstruct
`log_conj`, because `−1` is CENTRAL: `log (g (−1) g⁻¹) = log (−1)` and `Ad g` must fix whatever
value is assigned. The closed form above assigns `log (−1) = 0` automatically (`(−1) − (−1)ᴴ = 0`),
with no case split.

What the branch cut DOES obstruct is `exp ∘ log = id`, and `SuTwoLogExpTorus` §6 turns that into a
proved impossibility: for ANY `LogExpAd SU(2) 𝔤` whose `ad` is conjugation and whose `log` lands in
the traceless matrices (as Bałaban's `(1/i) log` does), `log (−1) = 0` is FORCED. This is precisely
why `LogExpAd` deliberately does not assume `exp ∘ log = id`: assuming it would have made the
structure uninhabitable at `SU(2)` by an su(2)-valued logarithm.

**SHARPENED 2026-07-30 — the obstruction is at EXACTLY ONE POINT, and everywhere else `exp ∘ log`
IS the identity.** `Balaban.RegularityGap.su2_exp_log_of_ne_negOne` proves `su2Exp (su2Log g) = g`
for every `g ≠ −1` (route: `X = su2Log g` satisfies `X² = −θ²·1` by Cayley–Hamilton from unitarity,
so `ℝ[X] ≅ ℂ` and `exp` transports along `Complex.liftAux`). The tree previously had this only on
`SuTwoLogExpFaithful.conjPrincipal`, a predicate with no membership criterion; the `≠ −1` form is
checkable, and `RegularityGap.frobNorm_negOne_sub_one` (`‖(−1) − 1‖_F = 2√2`) discharges it from any
smallness threshold below `2√2`. Nothing above is retracted — the impossibility at `−1` stands, and
it is now known to be the ONLY failure.
-/

namespace AdalyFormal.Balaban.SuTwoLogExp

open Matrix
open AdalyFormal.Balaban.BlockedGauge

/-- The ambient matrix algebra; the `𝔤` of `LogExpAd`. -/
abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- The gauge group. -/
abbrev SU2 : Type := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-! ## §1. Coercion and unitarity plumbing -/

theorem coe_mul (g h : SU2) : ((g * h : SU2) : M2) = (g : M2) * (h : M2) := rfl

theorem coe_inv (g : SU2) : ((g⁻¹ : SU2) : M2) = (g : M2)ᴴ := rfl

theorem coe_one : ((1 : SU2) : M2) = 1 := rfl

theorem star_mul_self (g : SU2) : (g : M2)ᴴ * (g : M2) = 1 := by
  have h : (g : M2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := g.2.1
  rw [Matrix.mem_unitaryGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose] using h

theorem mul_star_self (g : SU2) : (g : M2) * (g : M2)ᴴ = 1 := by
  have h : (g : M2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := g.2.1
  rw [Matrix.mem_unitaryGroup_iff] at h
  simpa [Matrix.star_eq_conjTranspose] using h

theorem coe_det (g : SU2) : (g : M2).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2

theorem coe_isUnit (g : SU2) : IsUnit (g : M2) := by
  rw [Matrix.isUnit_iff_isUnit_det, coe_det]
  exact isUnit_one

/-- The MATRIX inverse of an `SU(2)` element is its conjugate transpose. -/
theorem coe_matrix_inv (g : SU2) : (g : M2)⁻¹ = (g : M2)ᴴ :=
  Matrix.inv_eq_left_inv (star_mul_self g)

/-- Conjugation by an `SU(2)` element preserves membership in `SU(2)`. -/
theorem conj_mem (g : SU2) {M : M2} (h : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (g : M2) * M * (g : M2)ᴴ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hginv : ((g : M2)ᴴ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [← coe_inv g]; exact (g⁻¹ : SU2).2
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ g.2 h) hginv

/-- …and reflects it. -/
theorem conj_mem_iff (g : SU2) (M : M2) :
    (g : M2) * M * (g : M2)ᴴ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ
      ↔ M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine ⟨fun h => ?_, fun h => conj_mem g h⟩
  have := conj_mem g⁻¹ h
  rw [coe_inv] at this
  have hrw : (g : M2)ᴴ * ((g : M2) * M * (g : M2)ᴴ) * ((g : M2)ᴴ)ᴴ = M := by
    rw [Matrix.conjTranspose_conjTranspose]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, star_mul_self, Matrix.one_mul,
      Matrix.mul_assoc, star_mul_self, Matrix.mul_one]
  rwa [hrw] at this

/-! ## §2. `Ad` — genuine conjugation, as a `ℚ`-linear endomorphism -/

/-- `Ad g : A ↦ g A gᴴ`. `ℂ`-linear, a fortiori `ℚ`-linear. -/
def adMap (g : SU2) : M2 →ₗ[ℚ] M2 where
  toFun A := (g : M2) * A * (g : M2)ᴴ
  map_add' A B := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' q A := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem adMap_apply (g : SU2) (A : M2) : adMap g A = (g : M2) * A * (g : M2)ᴴ := rfl

/-! ## §3. `exp` — Mathlib's matrix exponential, totalised into `SU(2)` -/

open Classical in
/-- **The exponential.** On any `A` whose matrix exponential lands in `SU(2)` this IS
`NormedSpace.exp A` — no closed-form substitute, no re-derivation. The `else` branch is a
TOTALISATION: `LogExpAd.exp` must be defined on all of `𝔤`, and `NormedSpace.exp A` is not in
`SU(2)` for general `A ∈ M₂(ℂ)`.

**Exactly what is and is not proved about the guard.** `su2Exp_of_mem` shows the guard is
transparent wherever it holds; `su2Exp_psiR` (in `SuTwoLogExpTorus`) discharges it on the whole
one-parameter family the separation witness uses. It is NOT proved here that the guard holds on all of `su(2)` — that needs
`det (exp A) = exp (tr A)`, which this Mathlib pin lists as an explicit TODO
(`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`, "## TODO"). Note the direction of the
resulting risk: a spuriously-triggered guard can only make `exp` MORE trivial, so it can never
manufacture the separation of `SuTwoLogExpWitness` — it could only suppress it. -/
noncomputable def su2Exp (A : M2) : SU2 :=
  if h : NormedSpace.exp A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ then ⟨NormedSpace.exp A, h⟩
  else 1

theorem su2Exp_of_mem {A : M2} (h : NormedSpace.exp A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((su2Exp A : SU2) : M2) = NormedSpace.exp A := by
  classical
  simp only [su2Exp, dif_pos h]

theorem su2Exp_of_not_mem {A : M2}
    (h : NormedSpace.exp A ∉ Matrix.specialUnitaryGroup (Fin 2) ℂ) : su2Exp A = 1 := by
  classical
  simp only [su2Exp, dif_neg h]

@[simp] theorem su2Exp_zero : su2Exp (0 : M2) = 1 := by
  classical
  have h : NormedSpace.exp (0 : M2) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [NormedSpace.exp_zero]; exact Submonoid.one_mem _
  apply Subtype.ext
  rw [su2Exp_of_mem h, NormedSpace.exp_zero, coe_one]

/-! ## §4. `log` — the principal logarithm of `SU(2)` in closed form -/

/-- `θ(g) = arccos (Re tr g / 2) ∈ [0, π]`: the rotation angle of `g`. -/
noncomputable def su2Angle (g : SU2) : ℝ := Real.arccos ((Matrix.trace (g : M2)).re / 2)

/-- `κ(g) = θ(g) / sin θ(g)`. At `g = ±1` the denominator vanishes and Lean's division returns `0`;
that junk value is harmless because it multiplies `g − gᴴ = 0` there
(`SuTwoLogExpTorus.su2Log_center`), and `SuTwoLogExpFaithful.sin_su2Angle_ne_zero` proves the
denominator vanishes at NO other group element. -/
noncomputable def su2Kappa (g : SU2) : ℝ := su2Angle g / Real.sin (su2Angle g)

/-- **THE ORDINARY PRINCIPAL LOGARITHM of `SU(2)` — `𝔰𝔲(2)`-valued, NOT `(1/i) log`.**

~~**`(1/i) log` of CMP109 (0.4), for `SU(2)`.**~~ **STRUCK 2026-07-30: this docstring was wrong
about its own object.** Two theorems in this tree settle it, and a third sentence in this very file
already said so:

* `SuTwoLogExpTorus.su2Log_antiHermitian` — `(su2Log g)ᴴ = −su2Log g`. Anti-Hermitian traceless IS
  `𝔰𝔲(2)`. Bałaban's `(1/i)log` is `−i` times this, hence HERMITIAN traceless — a different space.
* `Balaban.RegularityGap.su2_exp_log_of_ne_negOne` — `su2Exp (su2Log g) = g` for every `g ≠ −1`,
  with `su2Exp = NormedSpace.exp` and **no factor of `i` anywhere**. That is the defining property
  of an ordinary logarithm; `(1/i)log` satisfies `exp (i · X) = g` instead.
* `su2LogExp`'s own docstring, below in this file, already called it "the genuine principal
  logarithm", and `BlockingLinkEstimate`'s header already recorded that in CMP98 (43) "the `i` and
  `1/i` cancel exactly", i.e. `exp[i Σ w (1/i) log X] = exp[Σ w log X]`. Only this docstring
  disagreed with the rest of the tree.

The conversion is exact and one-sided: `(1/i) log g = −i · su2Log g`. The `LogExpAd` LAWS do not
distinguish the two normalizations (`log_conj` is invariant under any rescaling of `log`, and
`exp_ad` under the matching rescaling of `exp`), which is why the instance below is valid either
way and why the error survived — the structure cannot see it. **DENOTATION can**, which is the
whole point: a lane reading this docstring puts the `i` on the wrong side of the source's chart
`U^u = e^{iηA}`. `compute/regularity_gap/` hit exactly that and had to pin the denotation
explicitly — `RegularityGap.frobNorm_chartA_eq_srcA` proves `‖chartA‖_F = ‖A‖_F` for the source's
own `A`, and `RegularityGap.chart_equation` proves the chart conjunct really is `U^u = e^{iηA}` —
work that this docstring caused.

`log g = (κ(g)/2) • (g − gᴴ)`. For `g = exp A` with `A ∈ su(2)` of angle `r ∈ [0, π)` this returns
exactly `A`: `g − gᴴ = 2 (sin r / r) A` and `κ = r / sin r`. **That sentence was always the correct
reading** — returning `A` from `exp A` is what an ordinary log does; `(1/i)log` would return `−iA`.
The header above it was the only thing wrong. -/
noncomputable def su2Log (g : SU2) : M2 :=
  ((su2Kappa g : ℂ) / 2) • ((g : M2) - (g : M2)ᴴ)

@[simp] theorem su2Log_one : su2Log (1 : SU2) = 0 := by
  simp [su2Log]

/-! ## §5. The two laws -/

theorem trace_conj (g : SU2) (X : SU2) :
    Matrix.trace ((g : M2) * (X : M2) * (g : M2)ᴴ) = Matrix.trace (X : M2) := by
  rw [Matrix.trace_mul_comm ((g : M2) * (X : M2)) ((g : M2)ᴴ), ← Matrix.mul_assoc,
    star_mul_self, Matrix.one_mul]

theorem su2Angle_conj (g X : SU2) : su2Angle (g * X * g⁻¹) = su2Angle X := by
  simp only [su2Angle, coe_mul, coe_inv, trace_conj g X]

theorem su2Kappa_conj (g X : SU2) : su2Kappa (g * X * g⁻¹) = su2Kappa X := by
  simp only [su2Kappa, su2Angle_conj]

/-- **Law 1: `log (g X g⁻¹) = Ad(g) (log X)`.** -/
theorem su2_log_conj (g X : SU2) : su2Log (g * X * g⁻¹) = adMap g (su2Log X) := by
  have hct : (((g : M2) * (X : M2) * (g : M2)ᴴ))ᴴ = (g : M2) * (X : M2)ᴴ * (g : M2)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp only [su2Log, adMap_apply, coe_mul, coe_inv, su2Kappa_conj, hct]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

/-- **Law 2: `exp (Ad(g) A) = g (exp A) g⁻¹`.** -/
theorem su2_exp_ad (g : SU2) (A : M2) : su2Exp (adMap g A) = g * su2Exp A * g⁻¹ := by
  classical
  have hconj : NormedSpace.exp ((g : M2) * A * (g : M2)ᴴ)
      = (g : M2) * NormedSpace.exp A * (g : M2)ᴴ := by
    have := Matrix.exp_conj (g : M2) A (coe_isUnit g)
    rwa [coe_matrix_inv] at this
  by_cases hA : NormedSpace.exp A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ
  · have hAd : NormedSpace.exp (adMap g A) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      rw [adMap_apply, hconj]
      exact conj_mem g hA
    apply Subtype.ext
    rw [su2Exp_of_mem hAd, adMap_apply, hconj, coe_mul, coe_mul, coe_inv, su2Exp_of_mem hA]
  · have hAd : NormedSpace.exp (adMap g A) ∉ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      rw [adMap_apply, hconj]
      exact fun hc => hA ((conj_mem_iff g _).mp hc)
    rw [su2Exp_of_not_mem hAd, su2Exp_of_not_mem hA, mul_one, mul_inv_cancel]

/-- **THE `LogExpAd` INSTANCE AT `SU(2)`.**

`log`/`exp` are the genuine principal logarithm and Mathlib's matrix exponential; `ad` is genuine
conjugation. Contrast `BlockedGaugeWitness.trivialLogExp`, which satisfies the same two laws with
`log = 0`, `exp = 1`, `ad = 0` and makes `Ū(c) = U(c)`; `SuTwoLogExpWitness` proves that THIS
instance fails that control. -/
noncomputable def su2LogExp : LogExpAd SU2 M2 where
  log := su2Log
  exp := su2Exp
  ad := adMap
  log_conj := su2_log_conj
  exp_ad := su2_exp_ad

@[simp] theorem su2LogExp_log (g : SU2) : su2LogExp.log g = su2Log g := rfl
@[simp] theorem su2LogExp_exp (A : M2) : su2LogExp.exp A = su2Exp A := rfl
@[simp] theorem su2LogExp_ad (g : SU2) : su2LogExp.ad g = adMap g := rfl

/-- `ad` is NOT the degenerate zero map of `trivialLogExp`, and NOT the identity of `ratLogExp`:
conjugation by the diagonal element `diag(i, −i)` moves the off-diagonal matrix unit. Pinned, no
existential over free data (S91). -/
theorem adMap_ne_zero_ne_id :
    ∃ (g : SU2) (A : M2), adMap g A ≠ A ∧ adMap g A ≠ 0 := by
  have hu : (Matrix.diagonal ![Complex.I, -Complex.I] : M2)
      ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.one_apply, Complex.ext_iff]
  have hd : (Matrix.diagonal ![Complex.I, -Complex.I] : M2).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp [Complex.ext_iff]
  refine ⟨⟨Matrix.diagonal ![Complex.I, -Complex.I],
    Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hu, hd⟩⟩,
    Matrix.of ![![0, 1], ![0, 0]], ?_, ?_⟩
  · intro h
    have h2 := congrFun (congrFun h 0) 1
    norm_num [adMap_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
      Matrix.conjTranspose] at h2
  · intro h
    have h2 := congrFun (congrFun h 0) 1
    norm_num [adMap_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
      Matrix.conjTranspose] at h2

end AdalyFormal.Balaban.SuTwoLogExp
