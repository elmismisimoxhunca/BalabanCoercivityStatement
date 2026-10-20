/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BlockedGaugeGuardAlgebra

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[BLOCKED-SU2-ALGEBRA]` — CLOSED. `exp` maps `su(2)` into `SU(2)`, unconditionally.

~~# THE ONE NAMED RESIDUAL LEFT IN `[BLOCKED-SU2-ALGEBRA]` — ISOLATED SO IT CANNOT HIDE~~

⚠ **SUPERSEDED 2026-08-01/02 (su2algebra_glue lane). The `sorry` below is DISCHARGED.** The struck
text is retained verbatim (S75: a correction is complete only when nothing still asserts the old
claim) because it is the honest record of two routes that stalled and of the risk-direction that
was carried while the debt was open. Everything it says about routes A and B remains TRUE — those
two routes really do stop where it says. What is no longer true is the *conclusion* those
paragraphs were written to support, namely that the statement was open. A **third** route closes
it; see §Route C.

~~This module exists so that the residual is a **`sorry` with a name and a locator**, not a sentence
in a docstring. It is imported by nothing; `BlockedGaugeGuardAlgebra` and every guard module remain
`sorryAx`-free, and `#print axioms` on this module's ONE unproved declaration shows the debt.~~
This module now carries **no `sorry`**: `#print axioms exp_su2Alg_mem_special` reports the three
standard axioms only.

## The statement

> `exp_su2Alg_mem_special : ∀ A : su(2), NormedSpace.exp A ∈ specialUnitaryGroup (Fin 2) ℂ`

Discharging it removes the totalising `if … then … else 1` from `SuTwoLogExpCore.su2Exp` on the
whole algebra carrier: `su2Exp_ungated` below proves that reduction ~~UNCONDITIONALLY, from the
statement as a hypothesis, so the value of closing it is machine-checked even while it is open~~
from the statement as a hypothesis, and `su2Exp_su2Alg_coe` now states it **with no hypothesis at
all**, the hypothesis having been discharged.

## Route C — CAYLEY–HAMILTON + `Complex.liftAux`. THE PROOF.

Every `H : M₂(ℂ)` that is traceless and anti-Hermitian satisfies the characteristic equation

> `H · H = −(‖H‖_F² / 2) · 1`   (`alg_sq`)

with a scalar that is REAL and NONPOSITIVE — that is the whole content, and it is four
matrix-entry identities (`scalar_val`, `offdiag01`, `offdiag10`, `diag11`), each a one-line
consequence of `Aᴴ = −A` and `trace A = 0`. Hence for `r := √(‖H‖_F²/2) > 0` the matrix
`J := r⁻¹ · H` satisfies `J² = −1`, so `Complex.liftAux J` is an `ℝ`-algebra map `ℂ → M₂(ℂ)`
sending `i ↦ J`. It is continuous (finite-dimensional), so it commutes with `exp`, and

> `exp H = φ(exp(i r)) = cos r · 1 + (sin r / r) · H`   (`exp_closed`)

whence `det (exp H) = cos²r + sin²r = 1` (`comb_det`). Together with unitarity —
`BlockedGaugeGuardAlgebra.exp_su2Alg_mem_unitary`, already proved — that is membership in `SU(2)`.
The `r = 0` branch is `H = 0`, `exp 0 = 1`.

This is the same `Complex.liftAux` technique `Balaban.RegularityGap.su2_exp_log_of_ne_negOne`
already uses (LAW-19: reuse, do not rebuild). It avoids BOTH walls recorded below: it never needs
`det (exp A) = exp (trace A)` (Route A) and it never diagonalises (Route B), so no degenerate case
splits on the eigenvector arise.

**Provenance and duplication, stated.** The identical mathematics is proved in
`Balaban.ClassPropagationUbar` (§3, `exp_mem_special`); the proof is re-proved here locally, as
private lemmas, rather than imported. The two copies are deliberate and disclosed; the local ones
are `private` so no ambiguity can arise at any common consumer.

⚠ **MEASURED, correcting the dispatch premise:** importing `ClassPropagationUbar` here would NOT
create an import cycle. ~~NOTHING in the tree imports `BlockedGaugeGuardAlgebraExp`~~ (STALE
within minutes and CORRECTED 2026-08-02 per the Claude prosecution: the main loop's root wiring
imported this module at `formal/AdalyFormal/AdalyFormal.lean` three minutes after this file's
last edit — and the grep recipe below has a structural blind spot: it sweeps the NESTED source
tree `AdalyFormal/` and misses the root import file one level up. The recipe's scope must be the
package directory, not the nested tree.) At this file's edit time: zero hits for
an ANCHORED import line, `grep -rlE "^import AdalyFormal[.]Balaban[.]BlockedGaugeGuardAlgebraExp$"`
over `AdalyFormal/`. (An UNANCHORED `grep -rl` for that string returns ONE hit — this file — because
this very sentence quotes the module path; the recipe is anchored for that reason.) And
`ClassPropagationUbar`'s 193-module import closure does not contain this module (nor does
`BlockedBackground`'s). The reason the proof is duplicated rather than imported is ARCHITECTURAL,
not a cycle: this module's own import closure is 14 modules, and importing `ClassPropagationUbar`
would attach the entire 193-module Bałaban tower to a small guard file that sits below it.

⚠ **THE THREE REMAINING LINTER WARNINGS, ITEMISED — ONE IS LOAD-BEARING, DO NOT "CLEAN" IT.**
`lake env lean` on this file emits exactly three warnings, all inside the ported Route C block.
Each was tested by MUTATING A SCRATCH COPY and recompiling; the results are below, and one of them
corrects an earlier version of this very paragraph (S75, corrected in place). Sites are named by
DECLARATION and `have`, never by absolute line number — an earlier draft cited line numbers and any
edit above them silently invalidated the citation:

1. `unusedSimpArgs` on `← Complex.ofReal_pow` in `scalar_valL` — **LOAD-BEARING.**
   Removing it was TESTED: `exit 1`, `unsolved goals`. A `←` simp argument also removes the OTHER
   direction from the simp set, which is the effect actually being used; the linter does not model
   that, and its own hint text says so.
2. `unusedSimpArgs` on `Complex.cos_ofReal_re` in `exp_closedL`, at the `him` `have` — **a genuine no-op AT
   THE SITE THE COMPILER FLAGS.** ~~in `exp_closedL`'s `hre` — LOAD-BEARING, same test, same
   outcome.~~ **That was WRONG about which line, and therefore wrong about the verdict.** Measured:
   `exp_closedL` contains TWO textually identical `simp [Complex.cos_ofReal_re,
   Complex.sin_ofReal_re, Complex.sin_ofReal_im]` calls, one closing the `hre` `have` and one
   closing the `him` `have`. The compiler flags **only the `him` one**, and deleting
   `Complex.cos_ofReal_re` there compiles CLEAN (`exit 0`, warnings drop to 2). Deleting it from
   the UNFLAGGED `hre` call instead BREAKS the file (`exit 1`, `unsolved goals`). So the linter is
   right about the line it names and the load-bearing occurrence is the one it says nothing about —
   which is exactly why a location must be measured and not inferred from a sibling.
3. `unusedTactic` on one `push_cast` in `comb_detL` — **genuinely a no-op**
   (deletion tested: `exit 0`, warnings drop to 2).

Warnings 2 and 3 are removable and are RETAINED ANYWAY, deliberately: this block is a byte-faithful
port of `ClassPropagationUbar` §3 and keeping it so lets a reviewer diff the two proof scripts and
get zero deltas. No `set_option linter.*` bump is used to hide anything.

The Route B and §Controls blocks below were linted clean by DELETING their dead alternatives and
unused simp arguments rather than annotating them, so every warning in this file is accounted for
above.

## What is already proved, and what ~~is missing~~ WAS missing

* **Unitarity — PROVED.** `BlockedGaugeGuardAlgebra.exp_antiHerm_mem_unitary`:
  `Aᴴ = −A ⟹ (exp A)ᴴ = exp(Aᴴ) = exp(−A) = (exp A)⁻¹`.
* ~~**`det = 1` — MISSING.**~~ **`det = 1` — PROVED** (Route C, `comb_det` at `c = cos r`,
  `d = sin r / r`). `exp_su2Alg_mem_special_of_det` below shows this was indeed the ONLY gap:
  unitarity plus `det (exp A) = 1` gives the conclusion.

## Two routes attempted, and where each stops — evidence of resistance, not a label

⚠ Retained as the record of resistance, and now partly superseded: **Route A is still blocked**
(the Mathlib lemma it needs is still absent); **Route B is CLOSED** (§Route B below proves its
named lemma, so it is a second complete proof). Route C, which needs neither, is the proof of
record for `exp_su2Alg_mem_special`.

**Route A — the general identity.** `det (exp A) = exp (trace A)` would give it immediately, since
`trace A = 0` on this carrier. **That identity is not in this Mathlib pin.** It is listed verbatim
in the `## TODO` block of `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`:

> `* Show that `Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)``

So Route A is blocked by an ABSENT upstream lemma, not by a name I failed to find. Proving it in
general is a Jordan-form / continuity argument well beyond this lane.

**Route B — diagonalise in `2×2` and reuse this tree's own machinery.** Every `A ∈ su(2)` is
`Ad(g)(psiR t)` for some `g ∈ SU(2)`, `t ∈ ℝ`; then
`exp A = g · exp(psiR t) · gᴴ = g · torusM t · gᴴ ∈ SU(2)` by `SuTwoLogExpTorus.su2Exp_psiR` and
`SuTwoLogExpCore.conj_mem` — both already proved. Route B therefore reduces the residual to ONE
purely linear-algebraic lemma, stated here as `su2Alg_conj_psiR`:

> `∀ A : su(2), ∃ (g : SU2) (t : ℝ), (A : M₂(ℂ)) = g · psiR t · gᴴ`

~~Where Route B stops:~~ **Route B no longer stops anywhere — `su2Alg_conj_psiR` is PROVED below
(§Route B).** The header's own analysis is retained verbatim and was accurate about the
construction, and inaccurate about the case count:

> ~~Where Route B stops:~~ writing `A = [[i z, w], [−w̄, −i z]]` with `z : ℝ`, `w : ℂ`, the
> eigenvalues are `±i r` with `r = √(z² + |w|²)`, and the unitary diagonaliser is
> `g = (w, i(r−z)) / √(2r(r−z))` in its first column — which DEGENERATES exactly when `w = 0` and
> `r = z` (the already-diagonal case) and again at `r = 0`. ~~So Route B needs a three-way case
> split~~ plus `Real.sqrt`/`Complex.normSq` normalisation proofs for the unitarity of `g`. That is
> ordinary work, not a barrier; ~~it was not completed in this lane's budget and is recorded as
> such.~~

**Corrected, and this is what made it short:** the split is TWO-way, not three-way, and it is on
`w`, not on `r`. `w = 0` alone absorbs both listed degeneracies at once (and one the header's
`r = z` phrasing misses, namely `w = 0` with `z < 0`); and `w ≠ 0` gives `|w|² > 0`, hence
`r² > z²` with `r > 0`, hence `r > z` STRICTLY — so `√(2r(r−z))` is positive with no further
hypothesis and the normalisation never degenerates.

~~`su2Alg_conj_psiR` is deliberately NOT stated as an axiom or a second `sorry`: only the target is
left open, so the sorry count of this residual is exactly **one**.~~ The sorry count of this module
is now **zero**, and `su2Alg_conj_psiR` is a theorem rather than a hypothesis — so
`exp_su2Alg_mem_special_of_conj` composes into `exp_su2Alg_mem_special_routeB`, a complete SECOND
proof of the main statement by a route disjoint from Route C.

## ~~⚠ Direction of the risk while this is open~~ — the risk is retired

~~`su2Exp`'s `else` branch returns `1`. A spuriously triggered guard therefore makes `exp` MORE
trivial, never less: it can only SUPPRESS a separation, never manufacture one. Every non-degeneracy
result in the guard modules (`su2Guarded_value_ne_one`, `su2AlgGuarded_value_ne_one`) is therefore
safe against this residual, and every one of them routes through `su2Exp_psiR`, where the guard is
DISCHARGED rather than assumed.~~

The `else` branch is now proved never to fire on the algebra carrier (`su2Exp_su2Alg_coe`), so the
question of which direction a spurious trigger would bias is moot on `su(2)`. The paragraph is
retained struck because it remains the correct reading for the AMBIENT `M₂(ℂ)` domain of `su2Exp`,
where the guard genuinely can fire — and that is a THEOREM here, not a remark:
`exp_mem_special_needs_traceless` exhibits `H = (π/2)i·1` (anti-Hermitian, NOT traceless,
`det (exp H) = −1`), and `exp_mem_special_needs_antiHerm` exhibits `H = diag(1,−1)` (traceless,
NOT anti-Hermitian, `exp H` not unitary). Both kernel-checked in §Controls below.

## ⚠ FINDING, OUT OF WRITE SCOPE (LAW-4) — not repaired here

`BlockingLinkEstimate.blockedLink_sub_one_le` and its siblings carry a branch hypothesis
(`su2Log (su2Exp H) = H` — the `hbranch` family) that exists because the guard could not be shown
inert. That module is NOT in this lane's write scope and is NOT in this module's import closure
(this module is upstream of it), so the hypothesis is not dropped here and no claim is made that it
can be. `ClassPropagationUbar.frobNorm_su2Exp_sub_one_le_uncond` already carries the branch-free
form of that particular estimate, downstream.
-/

namespace AdalyFormal.Balaban.SuTwoLogExp

open Matrix
open AdalyFormal.Balaban.BlockedGauge

/-! ## Route C — the local, private re-proof

Everything in this section is `private`: it duplicates `ClassPropagationUbar` §3, which cannot be
imported here (it is downstream). No name below escapes this file. -/

section RouteC

variable {H : M2}

/-- Squared Frobenius norm of a `2×2` complex matrix. Local copy of
`RMapLipschitz.frobSq` (that module is not in this file's import closure). -/
private noncomputable def frobSqL (M : M2) : ℝ :=
  Complex.normSq (M 0 0) + Complex.normSq (M 0 1) +
    Complex.normSq (M 1 0) + Complex.normSq (M 1 1)

private theorem frobSqL_nonneg (M : M2) : 0 ≤ frobSqL M := by
  unfold frobSqL
  have h1 := Complex.normSq_nonneg (M 0 0)
  have h2 := Complex.normSq_nonneg (M 0 1)
  have h3 := Complex.normSq_nonneg (M 1 0)
  have h4 := Complex.normSq_nonneg (M 1 1)
  linarith

/-- Local copy of `AlphaAnalyticity.matrix_eq_zero_of_frobSq_zero`. -/
private theorem matrix_eq_zero_of_frobSqL_zero {M : M2} (h : frobSqL M = 0) : M = 0 := by
  unfold frobSqL at h
  have h00 := Complex.normSq_nonneg (M 0 0)
  have h01 := Complex.normSq_nonneg (M 0 1)
  have h10 := Complex.normSq_nonneg (M 1 0)
  have h11 := Complex.normSq_nonneg (M 1 1)
  have e00 : M 0 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e01 : M 0 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e10 : M 1 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e11 : M 1 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11

/-- `Hᴴ = −H` entrywise. -/
private theorem entry_starL (hah : Hᴴ = -H) (i j : Fin 2) : star (H j i) = - H i j := by
  have := congrFun (congrFun hah i) j
  simpa [Matrix.conjTranspose_apply] using this

/-- The diagonal of an anti-Hermitian matrix is purely imaginary. -/
private theorem e00reL (hah : Hᴴ = -H) : (H 0 0).re = 0 := by
  have h := entry_starL hah 0 0
  have := congrArg Complex.re h
  simp at this
  linarith

private theorem e11L (htr : Matrix.trace H = 0) : H 1 1 = - H 0 0 := by
  rw [Matrix.trace_fin_two] at htr
  linear_combination htr

private theorem e10L (hah : Hᴴ = -H) : H 1 0 = - (starRingEnd ℂ) (H 0 1) := by
  have h := entry_starL hah 0 1
  rw [Complex.star_def] at h
  have h2 := congrArg (starRingEnd ℂ) h
  simpa using h2

/-- The `00` entry is `i·Im(H₀₀)` — used by Route B (§Route B below), not by Route C. -/
private theorem e00L (hah : Hᴴ = -H) : H 0 0 = (((H 0 0).im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [e00reL hah]

/-- `frobSqL H = 2(b² + |w|²)` with `b = Im H₀₀`, `w = H₀₁`. -/
private theorem frobSqL_eq (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    frobSqL H = 2 * ((H 0 0).im ^ 2 + Complex.normSq (H 0 1)) := by
  have hre := e00reL hah
  have h11 := e11L htr
  have h10 := e10L hah
  unfold frobSqL
  rw [h11, h10]
  simp only [Complex.normSq_apply, Complex.neg_re, Complex.neg_im, Complex.conj_re,
    Complex.conj_im]
  rw [hre]
  ring

private theorem scalar_valL (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    H 0 0 * H 0 0 + H 0 1 * H 1 0 = ((-(frobSqL H / 2) : ℝ) : ℂ) := by
  have hre := e00reL hah
  have h10 := e10L hah
  rw [frobSqL_eq hah htr, h10]
  apply Complex.ext <;>
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, hre, ← Complex.ofReal_pow] <;>
      ring

private theorem offdiag01L (htr : Matrix.trace H = 0) : H 0 0 * H 0 1 + H 0 1 * H 1 1 = 0 := by
  rw [e11L htr]; ring

private theorem offdiag10L (htr : Matrix.trace H = 0) : H 1 0 * H 0 0 + H 1 1 * H 1 0 = 0 := by
  rw [e11L htr]; ring

private theorem diag11L (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    H 1 0 * H 0 1 + H 1 1 * H 1 1 = ((-(frobSqL H / 2) : ℝ) : ℂ) := by
  rw [e11L htr, ← scalar_valL hah htr]
  ring

/-- **CAYLEY–HAMILTON ON `su(2)`.** `H·H = −(frobSqL H / 2)·1`. The scalar is REAL and NONPOSITIVE,
which is what makes `r⁻¹·H` a complex structure. -/
private theorem alg_sqL (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    H * H = ((-(frobSqL H / 2) : ℝ) : ℂ) • (1 : M2) := by
  have k00 := scalar_valL hah htr
  have k01 := offdiag01L htr
  have k10 := offdiag10L htr
  have k11 := diag11L hah htr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Fin.isValue] <;>
    simp [k00, k01, k10, k11]

private theorem comb_detL (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) (c d : ℝ) :
    (c • (1 : M2) + d • H).det = ((c ^ 2 + d ^ 2 * (frobSqL H / 2) : ℝ) : ℂ) := by
  have h11 := e11L htr
  have hsc := scalar_valL hah htr
  have o01 : ((1 : M2) 0 1) = 0 := Matrix.one_apply_ne (by decide)
  have o10 : ((1 : M2) 1 0) = 0 := Matrix.one_apply_ne (by decide)
  have o00 : ((1 : M2) 0 0) = 1 := Matrix.one_apply_eq _
  have o11 : ((1 : M2) 1 1) = 1 := Matrix.one_apply_eq _
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, o00, o01, o10, o11, Complex.real_smul]
  rw [h11]
  have hexp : ((c ^ 2 + d ^ 2 * (frobSqL H / 2) : ℝ) : ℂ)
      = (c : ℂ) ^ 2 - (d : ℂ) ^ 2 * ((-(frobSqL H / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, ← hsc]
  push_cast
  ring

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Local copy of `RegularityGap.real_smul_eq`. -/
private theorem real_smul_eqL (r : ℝ) (A : M2) : ((r : ℝ) : ℂ) • A = r • A := by
  rw [← Complex.coe_algebraMap, algebraMap_smul]

/-- **THE CLOSED FORM.** `exp H = cos r · 1 + (sin r / r) · H` with `r = √(frobSqL H / 2)`. -/
private theorem exp_closedL (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) {r : ℝ} (hr : 0 < r)
    (hr2 : r ^ 2 = frobSqL H / 2) :
    NormedSpace.exp H = (Real.cos r) • (1 : M2) + (Real.sin r * r⁻¹) • H := by
  have hrne : r ≠ 0 := ne_of_gt hr
  set J : M2 := (r⁻¹ : ℝ) • H with hJdef
  have hHH : H * H = ((-(r ^ 2) : ℝ)) • (1 : M2) := by
    rw [alg_sqL hah htr, hr2, real_smul_eqL]
  have hJ : J * J = -1 := by
    rw [hJdef, smul_mul_assoc, mul_smul_comm, hHH, smul_smul, smul_smul]
    have : r⁻¹ * r⁻¹ * -(r ^ 2) = -1 := by field_simp
    rw [this, neg_one_smul]
  set phi : ℂ →ₐ[ℝ] M2 := Complex.liftAux J hJ with hphi
  have hcont : Continuous ((phi : ℂ →ₐ[ℝ] M2) : ℂ → M2) := by
    have hc2 : Continuous ((phi : ℂ →ₐ[ℝ] M2).toLinearMap : ℂ → M2) :=
      LinearMap.continuous_of_finiteDimensional _
    exact hc2
  have hphir : phi ((r : ℂ) * Complex.I) = H := by
    rw [hphi, Complex.liftAux_apply]
    have hre : ((r : ℂ) * Complex.I).re = 0 := by simp
    have him : ((r : ℂ) * Complex.I).im = r := by simp
    rw [hre, him, map_zero, zero_add, hJdef, smul_smul, mul_inv_cancel₀ hrne, one_smul]
  have hexp : NormedSpace.exp H = phi (Complex.exp ((r : ℂ) * Complex.I)) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.map_exp phi hcont, hphir]
    rfl
  rw [hexp, Complex.exp_mul_I, hphi, Complex.liftAux_apply]
  have hre : (Complex.cos (r : ℂ) + Complex.sin (r : ℂ) * Complex.I).re = Real.cos r := by
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  have him : (Complex.cos (r : ℂ) + Complex.sin (r : ℂ) * Complex.I).im = Real.sin r := by
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  rw [hre, him, Algebra.algebraMap_eq_smul_one, hJdef, smul_smul]

/-- **`exp` MAPS TRACELESS ANTI-HERMITIAN `2×2` MATRICES INTO `SU(2)`.** Unitarity is
`exp_antiHerm_mem_unitary` (already in this file's import closure, LAW-19); `det = 1` is
`cos²r + sin²r` read off the closed form. -/
private theorem exp_mem_specialL (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    NormedSpace.exp H ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨exp_antiHerm_mem_unitary hah, ?_⟩
  rcases eq_or_lt_of_le (frobSqL_nonneg H) with hz | hpos
  · have hH0 : H = 0 := matrix_eq_zero_of_frobSqL_zero hz.symm
    rw [hH0, NormedSpace.exp_zero, Matrix.det_one]
  · set r : ℝ := Real.sqrt (frobSqL H / 2) with hrdef
    have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
    have hr2 : r ^ 2 = frobSqL H / 2 := Real.sq_sqrt (by linarith)
    rw [exp_closedL hah htr hrpos hr2, comb_detL hah htr]
    have hone : Real.cos r ^ 2 + (Real.sin r * r⁻¹) ^ 2 * (frobSqL H / 2) = 1 := by
      rw [← hr2]
      have hrne : r ≠ 0 := ne_of_gt hrpos
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq r]
    rw [hone]
    norm_num

end RouteC

/-! ## The statement, discharged

`exp_su2Alg_mem_special` below is byte-identical to the statement that carried the `sorry`; only
its proof changed. It is stated OUTSIDE `section RouteC` so that its elaboration uses the tree's
default matrix instances, not the section-local `linftyOp` ones — the `exact` therefore also
certifies that the two elaborations agree. -/

/-- **`exp` maps `su(2)` into `SU(2)`.** Was `[BLOCKED-SU2-ALGEBRA]`; closed by Route C. -/
theorem exp_su2Alg_mem_special (A : ↥su2Alg) :
    NormedSpace.exp (A : M2) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  exp_mem_specialL A.2.2 A.2.1

/-- The same fact for a bare traceless anti-Hermitian matrix, without the carrier subtype.
Public because every downstream consumer that wants to drop a guard hypothesis needs THIS form;
the carrier form is a corollary. -/
theorem exp_antiHerm_traceless_mem_special {H : M2} (hah : Hᴴ = -H)
    (htr : Matrix.trace H = 0) :
    NormedSpace.exp H ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  exp_mem_specialL hah htr

/-- **The reduction, PROVED (no `sorry`): unitarity is already in hand, so `det = 1` is the ONLY
missing half.** Retained: it is what identified the gap, and it is still the cleanest statement of
why unitarity alone was not enough. -/
theorem exp_su2Alg_mem_special_of_det (A : ↥su2Alg)
    (hdet : (NormedSpace.exp (A : M2)).det = 1) :
    NormedSpace.exp (A : M2) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨exp_su2Alg_mem_unitary A, hdet⟩

/-- **The value of closing it, PROVED (no `sorry`): the totalising guard of `su2Exp` never fires on
the algebra carrier.** Stated with the residual as an explicit HYPOTHESIS ~~, so this theorem is
unconditional Lean even though its hypothesis is open~~. The hypothesis is now a theorem
(`exp_su2Alg_mem_special`); this form is retained unchanged, and `su2Exp_su2Alg_coe` below is the
hypothesis-free consequence. -/
theorem su2Exp_ungated
    (h : ∀ A : ↥su2Alg, NormedSpace.exp (A : M2) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (A : ↥su2Alg) : ((su2Exp (A : M2) : SU2) : M2) = NormedSpace.exp (A : M2) :=
  su2Exp_of_mem (h A)

/-- **THE PAYOFF, UNCONDITIONAL.** On the `su(2)` carrier, `su2Exp` IS `NormedSpace.exp`: the
totalising `else 1` branch is proved never to fire. This is `su2Exp_ungated` with its hypothesis
discharged. -/
theorem su2Exp_su2Alg_coe (A : ↥su2Alg) :
    ((su2Exp (A : M2) : SU2) : M2) = NormedSpace.exp (A : M2) :=
  su2Exp_ungated exp_su2Alg_mem_special A

/-- The same payoff for a bare traceless anti-Hermitian matrix. -/
theorem su2Exp_coe_of_antiHerm_traceless {H : M2} (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    ((su2Exp H : SU2) : M2) = NormedSpace.exp H :=
  su2Exp_of_mem (exp_antiHerm_traceless_mem_special hah htr)

/-- **ROUTE A's IDENTITY, RESTRICTED TO THIS CARRIER.** Mathlib's `## TODO` lemma
`det (exp A) = exp (trace A)` is absent in general (header, Route A) and this does NOT supply it:
on the traceless anti-Hermitian carrier both sides are `1`, so this is a RESTATEMENT of the
`det = 1` half of Route C, not new content and not a proof of the general identity. It is stated
only so that the header's Route A paragraph names a checkable declaration instead of nothing:
what is missing upstream is the identity for ARBITRARY `A`, where `exp (trace A) ≠ 1`. -/
theorem det_exp_eq_exp_trace_of_antiHerm_traceless {H : M2} (hah : Hᴴ = -H)
    (htr : Matrix.trace H = 0) :
    (NormedSpace.exp H).det = NormedSpace.exp (Matrix.trace H) := by
  rw [htr, NormedSpace.exp_zero]
  exact (Matrix.mem_specialUnitaryGroup_iff.mp (exp_antiHerm_traceless_mem_special hah htr)).2

/-! ## §Controls — BOTH hypotheses of `exp_antiHerm_traceless_mem_special` are load-bearing

Neither `hah` nor `htr` is decoration, and this file proves that rather than asserting it. Both
witnesses are kernel-checked here; the module previously only NAMED the `htr` witness in prose. -/

/-- `exp` of a diagonal matrix, entrywise. -/
private theorem exp_dg (a b : ℂ) :
    NormedSpace.exp (dg a b) = dg (Complex.exp a) (Complex.exp b) := by
  rw [dg, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.exp_def]
  fin_cases i <;> simp [← Complex.exp_eq_exp_ℂ]

private theorem cexp_pi_div_two :
    Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- **MUST-FIRE CONTROL: `htr` IS LOAD-BEARING.** Anti-Hermitian ALONE does not put `exp` into
`SU(2)`: at `H = (π/2)i·1` — anti-Hermitian, trace `= iπ ≠ 0` — one has `exp H = i·1` with
determinant `−1`. So the tracelessness clause of `exp_antiHerm_traceless_mem_special` is not
decoration, and the `su2Exp` guard genuinely CAN fire on the ambient `M₂(ℂ)` domain. -/
theorem exp_mem_special_needs_traceless :
    ∃ H : M2, Hᴴ = -H ∧ Matrix.trace H ≠ 0 ∧
      NormedSpace.exp H ∉ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine ⟨dg (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) (((Real.pi / 2 : ℝ) : ℂ) * Complex.I),
    ?_, ?_, ?_⟩
  · rw [dg_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg]
  · rw [dg, Matrix.trace_fin_two]
    simp only [Matrix.diagonal_apply_eq]
    simp [Complex.ext_iff, Real.pi_ne_zero]
  · intro hmem
    have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp hmem).2
    rw [exp_dg, dg_det, cexp_pi_div_two, Complex.I_mul_I] at hdet
    exact absurd hdet (by norm_num)

/-- **MUST-FIRE CONTROL: `hah` IS LOAD-BEARING.** Traceless ALONE does not put `exp` into `SU(2)`
either: at the Hermitian traceless `H = diag(1, −1)`, `exp H = diag(e, e⁻¹)` has determinant `1`
but is NOT unitary (`e·ē = e² ≠ 1`). So the failure modes of the two hypotheses are different —
`htr` controls the determinant, `hah` controls unitarity — and neither implies the other. -/
theorem exp_mem_special_needs_antiHerm :
    ∃ H : M2, Matrix.trace H = 0 ∧ Hᴴ ≠ -H ∧
      NormedSpace.exp H ∉ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine ⟨dg 1 (-1), ?_, ?_, ?_⟩
  · rw [dg, Matrix.trace_fin_two]
    simp
  · rw [dg_conjTranspose]
    intro hcon
    have h00 := congrFun (congrFun hcon 0) 0
    simp [dg] at h00
    exact absurd h00 (by norm_num)
  · intro hmem
    have huni := Matrix.mem_specialUnitaryGroup_iff.mp hmem |>.1
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, exp_dg, dg_conjTranspose,
      dg_mul] at huni
    have hone : Complex.exp 1 = ((Real.exp 1 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
    have h00 : Complex.exp 1 * star (Complex.exp 1) = 1 := by
      have h := congrFun (congrFun huni 0) 0
      simpa [dg] using h
    rw [hone] at h00
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul] at h00
    have hR : Real.exp 1 * Real.exp 1 = 1 := by exact_mod_cast h00
    nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_pos (1 : ℝ)]

/-! ## §Route B — the diagonalisation, ALSO PROVED

The module header recorded Route B as reduced to one linear-algebra lemma, `su2Alg_conj_psiR`,
"not completed in this lane's budget". ~~That lemma is deliberately NOT stated as an axiom or a
second `sorry`.~~ **It is now a theorem** (`su2Alg_conj_psiR` below), so the file states it and
proves it. The degeneracies the header names are handled by a TWO-way split, not the three-way one
it predicted:

* `w = 0` — `A` is already diagonal and `A = psiR z` with `g = 1`. This single branch absorbs BOTH
  degeneracies the header listed (`r = 0`, i.e. `A = 0`; and `r = z`, i.e. `w = 0` with `z ≥ 0`),
  and it also covers `w = 0` with `z < 0`, which the header's `r = z` phrasing misses.
* `w ≠ 0` — then `‖w‖² > 0` forces `r² > z²` with `r > 0`, hence `r > z` STRICTLY, so
  `N = √(2r(r−z))` is positive and the normalisation the header worried about never divides by
  zero. No case split on the sign of `z` is needed.

The construction is the header's own: first column `(w, i(r−z))/N`. It is written unnormalised as
`GC w s = !![w, is; is, w̄]` so that the two facts needed are single scalar identities —
`GC · GCᴴ = (‖w‖² + s²)·1` and `GC · psiR r · GCᴴ = 2r(r−z)·A` — and the normalisation enters
exactly once, as `N⁻² · 2r(r−z) = 1`.

**This yields a SECOND, INDEPENDENT proof of the main theorem** (`exp_su2Alg_mem_special_routeB`).
~~Routes B and C share only the three entry lemmas (`e00L`/`e10L`/`e11L`) and Mathlib~~ (CORRECTED
per the Claude prosecution, 2026-08-02, and RE-CORRECTED same day per the second-family gate's
cone map: `e00L` is Route-B-ONLY, but its own proof routes through `e00reL`, so `e00reL` is in
BOTH proof-term cones — the measured shared surface is the FOUR lemmas
`{e10L, e11L, entry_starL, e00reL}`, each a one-line consequence of `hah`/`htr`, and each
mutation-verified load-bearing for both routes where shared. That four-lemma set is the honest
limit of the independence claim): Route C goes through Cayley–Hamilton and
`Complex.liftAux`; Route B goes through an explicit unitary and `Matrix.exp_conj` +
`Matrix.exp_diagonal`. Neither uses the other. -/

/-- The UNNORMALISED diagonaliser: columns `(w, i·s)` and `(i·s, w̄)`. -/
private noncomputable def GC (w : ℂ) (s : ℝ) : M2 :=
  !![w, (s : ℂ) * Complex.I; (s : ℂ) * Complex.I, (starRingEnd ℂ) w]

/-- The traceless anti-Hermitian matrix with data `(z, w)`: `!![iz, w; −w̄, −iz]`. -/
private noncomputable def AE (w : ℂ) (z : ℝ) : M2 :=
  !![(z : ℂ) * Complex.I, w; -(starRingEnd ℂ) w, -((z : ℂ) * Complex.I)]

private theorem GC_mul_star (w : ℂ) (s : ℝ) :
    GC w s * (GC w s)ᴴ = ((Complex.normSq w + s ^ 2 : ℝ) : ℂ) • (1 : M2) := by
  have hmc : w * (starRingEnd ℂ) w = ((Complex.normSq w : ℝ) : ℂ) := Complex.mul_conj w
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GC, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
      | ring1
      | linear_combination hmc - (s : ℂ) ^ 2 * Complex.I_sq

private theorem GC_det (w : ℂ) (s : ℝ) :
    (GC w s).det = ((Complex.normSq w + s ^ 2 : ℝ) : ℂ) := by
  have hmc : w * (starRingEnd ℂ) w = ((Complex.normSq w : ℝ) : ℂ) := Complex.mul_conj w
  simp [GC, Matrix.det_fin_two]
  linear_combination hmc - (s : ℂ) ^ 2 * Complex.I_sq

private theorem GC_smul_star (w : ℂ) (s c : ℝ) :
    (((c : ℝ) : ℂ) • GC w s)ᴴ = ((c : ℝ) : ℂ) • (GC w s)ᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.smul_apply]

/-- `psiR t` as a matrix literal. -/
private theorem psiR_lit (t : ℝ) :
    psiR t = !![(t : ℂ) * Complex.I, 0; 0, -((t : ℂ) * Complex.I)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [psiR_dg, dg]

/-- **THE CONJUGATION IDENTITY**, unnormalised: `GC · psiR r · GCᴴ = 2r(r−z) · A`. -/
private theorem GC_conj (w : ℂ) (z r : ℝ) (hw : Complex.normSq w = r ^ 2 - z ^ 2) :
    GC w (r - z) * psiR r * (GC w (r - z))ᴴ = ((2 * r * (r - z) : ℝ) : ℂ) • AE w z := by
  have hmc : w * (starRingEnd ℂ) w = (r : ℂ) ^ 2 - (z : ℂ) ^ 2 := by
    rw [Complex.mul_conj, hw]; push_cast; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GC, AE, psiR_lit, Matrix.mul_apply, Fin.sum_univ_two] <;>
    try push_cast
  · linear_combination ((r : ℂ) * Complex.I) * hmc
      + ((r : ℂ) * ((r : ℂ) - (z : ℂ)) ^ 2 * Complex.I) * Complex.I_sq
  · linear_combination (-2 * (r : ℂ) * ((r : ℂ) - (z : ℂ)) * w) * Complex.I_sq
  · linear_combination (2 * (r : ℂ) * ((r : ℂ) - (z : ℂ)) * (starRingEnd ℂ) w) * Complex.I_sq
  · linear_combination (-(r : ℂ) * Complex.I) * hmc
      + (-(r : ℂ) * ((r : ℂ) - (z : ℂ)) ^ 2 * Complex.I) * Complex.I_sq

/-- Normal form of a traceless anti-Hermitian `2×2` matrix. -/
private theorem su2Alg_eq_AE {H : M2} (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    H = AE (H 0 1) ((H 0 0).im) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [AE] using e00L hah
  · simp [AE]
  · simpa [AE] using e10L hah
  · have h11 : H 1 1 = -((((H 0 0).im : ℝ) : ℂ) * Complex.I) := by
      rw [e11L htr]
      exact congrArg Neg.neg (e00L hah)
    simpa [AE] using h11

/-- **ROUTE B's NAMED LEMMA — PROVED.** Every element of `su(2)` is `Ad(g)` of a torus generator:
`A = g · psiR t · gᴴ` with `g ∈ SU(2)`, `t ∈ ℝ`. This is the statement the module header named and
left unbuilt. -/
theorem su2Alg_conj_psiR (A : ↥su2Alg) :
    ∃ (g : SU2) (t : ℝ), (A : M2) = (g : M2) * psiR t * (g : M2)ᴴ := by
  obtain ⟨htr, hah⟩ := A.2
  obtain ⟨w, z, hMAE⟩ : ∃ (w : ℂ) (z : ℝ), (A : M2) = AE w z :=
    ⟨_, _, su2Alg_eq_AE hah htr⟩
  by_cases hw0 : w = 0
  · -- DEGENERATE BRANCH: `A` is already diagonal, `A = psiR z`, so `g = 1` works.
    refine ⟨1, z, ?_⟩
    have h1 : ((1 : SU2) : M2) = 1 := coe_one
    rw [hMAE, h1, one_mul, Matrix.conjTranspose_one, mul_one, hw0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [AE, psiR_lit]
  · -- GENERIC BRANCH: `w ≠ 0` forces `r > z` STRICTLY, so `N = √(2r(r−z)) > 0`.
    have hnwpos : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
    have hsum : (0 : ℝ) ≤ z ^ 2 + Complex.normSq w := by positivity
    obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.sqrt (z ^ 2 + Complex.normSq w) := ⟨_, rfl⟩
    have hr2 : r ^ 2 = z ^ 2 + Complex.normSq w := by rw [hrdef]; exact Real.sq_sqrt hsum
    have hnw : Complex.normSq w = r ^ 2 - z ^ 2 := by linarith
    have hrpos : 0 < r := by
      rw [hrdef]; exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg z])
    have hzr : z < r := by
      by_contra hcon
      have hcon' : r ≤ z := not_lt.mp hcon
      nlinarith [mul_nonneg (sub_nonneg.mpr hcon') (by linarith : (0 : ℝ) ≤ r + z)]
    obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Real.sqrt (2 * r * (r - z)) := ⟨_, rfl⟩
    have hNpos : 0 < N := by rw [hNdef]; exact Real.sqrt_pos.mpr (by nlinarith)
    have hN2 : N ^ 2 = 2 * r * (r - z) := by rw [hNdef]; exact Real.sq_sqrt (by nlinarith)
    have hNne : N ≠ 0 := ne_of_gt hNpos
    obtain ⟨g0, hg0def⟩ : ∃ g0 : M2, g0 = ((N⁻¹ : ℝ) : ℂ) • GC w (r - z) := ⟨_, rfl⟩
    have hg0star : g0ᴴ = ((N⁻¹ : ℝ) : ℂ) • (GC w (r - z))ᴴ := by
      rw [hg0def]; exact GC_smul_star w (r - z) N⁻¹
    have hcN : ((N⁻¹ : ℝ) : ℂ) * ((N⁻¹ : ℝ) : ℂ) * ((2 * r * (r - z) : ℝ) : ℂ) = 1 := by
      have hreal : N⁻¹ * N⁻¹ * (2 * r * (r - z)) = 1 := by
        rw [← hN2]; field_simp
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hreal
    have hns : ((Complex.normSq w + (r - z) ^ 2 : ℝ) : ℂ) = ((2 * r * (r - z) : ℝ) : ℂ) := by
      have hreal : Complex.normSq w + (r - z) ^ 2 = 2 * r * (r - z) := by rw [hnw]; ring
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hreal
    have hunit : g0 * g0ᴴ = 1 := by
      rw [hg0star, hg0def, smul_mul_assoc, mul_smul_comm, GC_mul_star, smul_smul, smul_smul,
        hns, hcN, one_smul]
    have hdet : g0.det = 1 := by
      rw [hg0def, Matrix.det_smul, GC_det, hns, Fintype.card_fin, ← hcN]
      ring
    have hmem : g0 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, hdet⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      exact hunit
    refine ⟨⟨g0, hmem⟩, r, ?_⟩
    have hcoe : ((⟨g0, hmem⟩ : SU2) : M2) = g0 := rfl
    rw [hcoe, hg0star, hg0def, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      GC_conj w z r hnw, smul_smul, hcN, one_smul, hMAE]

/-- **S91 MUST-FIRE CONTROL for `su2Alg_conj_psiR`.** The existential is NOT free data: at the
concrete carrier element `!![0, 1; −1, 0] ∈ su(2)` the degenerate witness `g = 1` fails for EVERY
`t`, so the construction in the generic branch is load-bearing and the statement cannot be
satisfied by a content-free term. Kernel-checked. -/
theorem su2Alg_conj_psiR_control :
    (!![0, 1; -1, 0] : M2) ∈ su2Alg ∧
      ∀ t : ℝ, (!![0, 1; -1, 0] : M2) ≠ ((1 : SU2) : M2) * psiR t * ((1 : SU2) : M2)ᴴ := by
  constructor
  · refine mem_su2Alg.mpr ⟨?_, ?_⟩
    · simp [Matrix.trace_fin_two]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · intro t hcon
    have h01 := congrFun (congrFun hcon 0) 1
    rw [coe_one, one_mul, Matrix.conjTranspose_one, mul_one, psiR_lit] at h01
    simp at h01

/-- **Route B, PROVED (no `sorry`): the linear-algebra lemma named in the docstring really does
finish the job.** So the residual ~~is reduced to `su2Alg_conj_psiR` and nothing else~~ WAS reduced
to `su2Alg_conj_psiR`; Route C closed it without that lemma — and `su2Alg_conj_psiR` is now itself
a theorem, so this hypothesis is dischargeable and Route B is a complete second proof
(`exp_su2Alg_mem_special_routeB`). -/
theorem exp_su2Alg_mem_special_of_conj
    (h : ∀ A : ↥su2Alg, ∃ (g : SU2) (t : ℝ), (A : M2) = (g : M2) * psiR t * (g : M2)ᴴ)
    (A : ↥su2Alg) : NormedSpace.exp (A : M2) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  obtain ⟨g, t, hA⟩ := h A
  have hconj : NormedSpace.exp ((g : M2) * psiR t * (g : M2)ᴴ)
      = (g : M2) * NormedSpace.exp (psiR t) * (g : M2)ᴴ := by
    have := Matrix.exp_conj (g : M2) (psiR t) (coe_isUnit g)
    rwa [coe_matrix_inv] at this
  -- `SuTwoLogExpTorus.su2Exp_psiR` proves this as an internal `have` and does not export it;
  -- reproduced here rather than weakening the statement (that module is outside this write scope).
  have htorus : NormedSpace.exp (psiR t) = torusM t := by
    rw [psiR_dg, dg, Matrix.exp_diagonal, torusM, dg]
    congr 1
    funext i
    rw [Pi.exp_def]
    fin_cases i <;> simp [← Complex.exp_eq_exp_ℂ]
  rw [hA, hconj, htorus]
  exact conj_mem g (torusM_mem t)

/-- **THE SAME THEOREM, BY THE OTHER ROUTE.** Byte-identical statement to
`exp_su2Alg_mem_special`, proved through Route B (explicit diagonalisation + `Matrix.exp_conj` +
`Matrix.exp_diagonal`) instead of Route C (Cayley–Hamilton + `Complex.liftAux`). Shared surface,
re-corrected 2026-08-02 per the second-family cone map: `{e10L, e11L, entry_starL, e00reL}`
(`e00L` is B-only but proves itself via `e00reL`, putting the latter in both cones). A
de-correlated cross-check of the discharged residual, not an extra assumption. -/
theorem exp_su2Alg_mem_special_routeB (A : ↥su2Alg) :
    NormedSpace.exp (A : M2) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  exp_su2Alg_mem_special_of_conj su2Alg_conj_psiR A

/-! ## Axiom audit (in-file, so it cannot drift) -/

#print axioms exp_su2Alg_mem_special
#print axioms exp_antiHerm_traceless_mem_special
#print axioms exp_su2Alg_mem_special_of_det
#print axioms su2Exp_ungated
#print axioms su2Exp_su2Alg_coe
#print axioms su2Exp_coe_of_antiHerm_traceless
#print axioms exp_su2Alg_mem_special_of_conj
#print axioms su2Alg_conj_psiR
#print axioms su2Alg_conj_psiR_control
#print axioms exp_su2Alg_mem_special_routeB
#print axioms exp_mem_special_needs_traceless
#print axioms exp_mem_special_needs_antiHerm
#print axioms det_exp_eq_exp_trace_of_antiHerm_traceless

end AdalyFormal.Balaban.SuTwoLogExp
