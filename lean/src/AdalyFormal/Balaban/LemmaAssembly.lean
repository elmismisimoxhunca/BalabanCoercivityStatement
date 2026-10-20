/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.AlphaAnalyticity

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `LemmaAssembly.lean` — assembling the three legs against `TheLemma`, and measuring the three gaps

**⚠⚠ THIS MODULE'S OPERATOR IS NOT CMP99b (3.10). SUPERSEDED BY `LemmaAssemblyNormalized.lean`.**
*Main-loop banner added 2026-07-28 (S75 in place; no declaration here is changed or struck).*

Everything below is stated about `deltaKQuadFormCorrected`, which a **grade-3** finding (blind Sol +
blind Kimi, independently, then verified against this tree's own kernel theorems) established is
**neither (3.10) nor (3.156)**: it adds a `D*D` leg carrying Bałaban's `tr 1 = 1` normalization (via
`SuTwoInner.hsInner = −(1/2)·Re Tr`) to a `Δ′` leg built on **raw `Matrix.trace`**, so **this module's
`Δ′` is exactly TWICE the source's.** CMP99b p.392 — now in the corpus, three independent renders
agreeing symbol-for-symbol — states *"the trace is normalized, i.e., `tr 1 = 1`"* immediately before
(3.10), using that same `tr` in **both** legs.

**The faithful object is `NormalizationAudit.deltaKQuadFormNormalizedCorrected`, and the assembly has
been re-proved on it:** `LemmaAssemblyNormalized.deltaKNormalized_gaugeRegular_coercive`, **same**
coercivity constant `γ = 1/2000` at a **weaker** threshold (`5·10⁻⁷` against this module's `10⁻⁷`),
because the faithful `Δ′` is half. **Prefer that module.** Nothing here is wrong *about the object it
names* — the defect is denotational, which is why every proof gate passed it.

*(Historical note for anyone reading an audit: `compute/norm_propagation/AUDIT.md` names this module's
`deltaK_gaugeRegular_coercive` as the campaign's most dangerous declaration. That audit predates
`LemmaAssemblyNormalized.lean`, which did not exist at its HEAD; the faithful twins it hoped for now
exist and are checked.)*

This module does ONE job: take the three built legs of `GOAL_LEMMA.md` §4's `Mα₀`-analyticity route
and try to compose them into the lemma, reporting exactly where the composition succeeds and where it
does not. Nothing here is graded by its author.

**The legs consumed (all pre-existing, none rebuilt — LAW-19):**

* `(b2)` `AlphaAnalyticity.deltaJ_gaugeRegular_coercive` —
  `coercConst α₀ * bondEnergy A ≤ dstarDQuadForm U A` for every `GaugeRegular α₀` background, on
  `axial ∩ ker Q₂(U)`, torus `4 ≤ L μ`, `2 ∣ L μ + 1`.
* `(b3)` `AlphaAnalyticity.gamma0_uniform_over_family` — the same with both constants bound before
  the index type / lattice family / background family / field family.
* `(b1)` enters only through `(b2)`'s own import cone (`RegularUCoercivityFull`).

**THE THREE GAPS, as this module finds them.** Facts only; the verdicts are the gates'.

1. **THE TARGET `sorry` CANNOT BE FILLED — and this is not this module's finding.**
   `TheLemma.theLemma_C_star_Delta_k_C_uniform` is documented IN ITS OWN DOCSTRING (2026-07-28) as
   **FALSE AS WRITTEN**, kernel-checked, refutation at `compute/sorry_triage/probe_lemma_refutation.lean`.
   The mechanism is that `Mα₀thresh` is a caller-supplied argument constrained only by `0 < Mα₀thresh`,
   so a caller may pick a threshold so large that `IsRegular` is satisfied by every configuration.
   §1 below RE-DERIVES that vacuity independently, in three lines, from `RMap`'s isometry — and then
   proves the sharper statement that the vacuity threshold is EXACTLY the threshold below which the
   hypothesis starts excluding pure gauges (§1, `isRegular_dichotomy`). Consequently NO patch to that
   declaration is proposed: L5 forbids weakening a statement to close a `sorry`, and the statement is
   retained unrepaired by its owning lane. What IS proposed
   (`compute/lemma_assembly/PATCH_theLemma.md`) is a NEW, separately-named declaration whose
   threshold is EXISTENTIAL, which is Bałaban's own quantifier ("with `Mα₀` sufficiently small").
2. **THE OPERATOR.** The legs bound `dstarDQuadForm` (the `D*D` term of CMP99b (3.10)); the lemma's
   conclusion is `deltaKQuadFormCorrected = dstarDQuadForm + deltaPrimeQuadFormTransported`. §2/§3
   close that gap by an absorption bound on `Δ′` — the missing analytic step, built here.
3. **THE REGULARITY HYPOTHESIS.** `TheLemma.IsRegular` is a THIRD predicate, distinct from BOTH
   `frobSupBond U ≤ α₀` and `AlphaAnalyticity.GaugeRegular α₀ U`. §1 proves it is neither necessary
   nor sufficient for the source condition, in the sharp form.

`#print axioms` on every declaration below.
-/

namespace AdalyFormal.Balaban.LemmaAssembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AlphaAnalyticity
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-! ## §1 — GAP 3: `TheLemma.IsRegular` is not Bałaban's regularity condition, sharply

`IsRegular U t := ∀ b, ‖R(U b)·w − w‖ ≤ t` with `w = suTwoWitness` FIXED
(`CovariantOperators.suTwoWitness = SuTwoInner.pauliE3`, CMP99b's own `E₃`).

Two facts, both proved below, with the SAME constant `2‖w‖` on each side:

* **Above `2‖w‖` the predicate is EMPTY as a restriction**: `isRegular_vacuous_at_two_norm` — every
  configuration whatsoever satisfies it, because `R(g)` is an isometry.
* **Below `2‖w‖` the predicate EXCLUDES A PURE GAUGE**: `pureGauge_not_isRegular` — the spike gauge
  of the IDENTITY configuration by `witnessMElem` is `GaugeRegular 0` (gauge-equivalent to `U ≡ 1`,
  hence regular in the source's sense at EVERY `α₀ ≥ 0`, since CMP99b (3.35) quantifies `∃ u`), yet
  it fails `IsRegular` at every threshold `< 2‖w‖`.

`isRegular_dichotomy` packages the two: there is NO threshold at which `IsRegular` both restricts the
configuration space and respects the gauge orbit of the identity. -/

open AdalyFormal.Balaban.RegularUDomainWitness (witL5 frobSupBond_trivialU witA
  bondEnergy_witA_pos regularU_domain_nonvacuous)
open AdalyFormal.Balaban.RegularUDomainWitnessGeneralU (siteZero)

/-- `2‖suTwoWitness‖`, the number both halves of §1's dichotomy turn on. -/
noncomputable def isRegularCeil : ℝ := 2 * ‖suTwoWitness‖

theorem isRegularCeil_pos : 0 < isRegularCeil := by
  have h : 0 < ‖suTwoWitness‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
  unfold isRegularCeil; linarith

/-- The two `trivialU` definitions in this tree are the same function.

**LAW-19 FINDING (not mine to fix, LAW-4):** `CovariantHjMinimizer.trivialU` (line 393) and
`DeltaPrime.trivialU` (line 281) are two independent definitions of `fun _ => 1`, in two files, both
live and both consumed by downstream modules. They are definitionally equal — this `rfl` is the
proof — but they should be collapsed onto one. Reported, not touched: both files are outside this
lane's write scope. -/
theorem trivialU_defs_agree :
    AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L
      = AdalyFormal.Balaban.DeltaPrime.trivialU (L := L) := rfl

/-- `‖R(witnessMElem)·w − w‖ = 2‖w‖` — the maximal displacement, from
`CovariantOperators.RMap_witnessMElem : R(witnessMElem)·w = −w`. -/
theorem displacement_witnessMElem :
    ‖RMap witnessMElem suTwoWitness - suTwoWitness‖ = isRegularCeil := by
  have hval : RMap witnessMElem suTwoWitness - suTwoWitness = (-2 : ℝ) • suTwoWitness := by
    rw [RMap_witnessMElem]
    module
  rw [hval, norm_smul]
  unfold isRegularCeil
  simp

#print axioms isRegularCeil_pos
#print axioms trivialU_defs_agree
#print axioms displacement_witnessMElem
/-! ## §2 — GAP 2, PART 1: the Frobenius toolkit needed to absorb `Δ′`

The lemma's conclusion is stated on `deltaKQuadFormCorrected U A = dstarDQuadForm U A +
deltaPrimeQuadFormTransported U A` (`DeltaKFull.lean` §3), while the legs bound `dstarDQuadForm`
alone. Closing that gap needs a quantitative bound on `Δ′` in terms of the regularity parameter.
`RMapLipschitz` supplies `frobSq`, its submultiplicativity and its unitary right-invariance; the
handful of further facts below are the ones it lacks. Every one is elementary and proved here rather
than assumed. -/

open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaKFull (deltaKQuadFormCorrected)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq
  frobSq_eq_trace frobSq_mul_right_isometry frobSq_sub_le frobSq_mul_le norm_sq_eq_half_frobSq)

/-- `((g * h : SU(2)) : Matrix) = g * h`. -/
theorem su_coe_mul (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((g * h : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- `frobSq Mᴴ = frobSq M`. -/
theorem frobSq_conjTranspose (M : Matrix (Fin 2) (Fin 2) ℂ) : frobSq Mᴴ = frobSq M := by
  simp only [AdalyFormal.Balaban.RMapLipschitz.frobSq, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.normSq_conj]
  ring

/-- `frobSq (-M) = frobSq M`. -/
theorem frobSq_neg (M : Matrix (Fin 2) (Fin 2) ℂ) : frobSq (-M) = frobSq M := by
  simp only [AdalyFormal.Balaban.RMapLipschitz.frobSq, Matrix.neg_apply, Complex.normSq_neg]

/-- `frobSq (c • M) = |c|² · frobSq M`. -/
theorem frobSq_smul (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    frobSq (c • M) = Complex.normSq c * frobSq M := by
  simp only [AdalyFormal.Balaban.RMapLipschitz.frobSq, Matrix.smul_apply, smul_eq_mul,
    Complex.normSq_mul]
  ring

/-- `frobSq (A + B) ≤ 2·frobSq A + 2·frobSq B` — the weak (constant-`2`) triangle inequality, which
is all the absorption needs. Derived from `RMapLipschitz.frobSq_sub_le`, not reproved. -/
theorem frobSq_add_le (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    frobSq (A + B) ≤ 2 * frobSq A + 2 * frobSq B := by
  have h := frobSq_sub_le A (-B)
  rw [sub_neg_eq_add, frobSq_neg] at h
  exact h

/-- Unitary LEFT-invariance of `frobSq` (the tree had only right-invariance). -/
theorem frobSq_mul_left_isometry (W M : Matrix (Fin 2) (Fin 2) ℂ) (hW : Wᴴ * W = 1) :
    frobSq (W * M) = frobSq M := by
  have h1 : frobSq (W * M) = frobSq (Mᴴ * Wᴴ) := by
    rw [← frobSq_conjTranspose (W * M), Matrix.conjTranspose_mul]
  have h2 : frobSq (Mᴴ * Wᴴ) = frobSq Mᴴ := by
    refine frobSq_mul_right_isometry Mᴴ Wᴴ ?_
    rw [Matrix.conjTranspose_conjTranspose]
    exact hW
  rw [h1, h2, frobSq_conjTranspose]

/-- `frobNorm M = √(frobSq M)`, by definition — named so `rw` can use it. -/
theorem frobNorm_eq (M : Matrix (Fin 2) (Fin 2) ℂ) : frobNorm M = Real.sqrt (frobSq M) := rfl

/-- `frobNorm (A·B) ≤ frobNorm A · frobNorm B`. -/
theorem frobNorm_mul_le (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    frobNorm (A * B) ≤ frobNorm A * frobNorm B := by
  have h := frobSq_mul_le A B
  rw [frobNorm_eq, frobNorm_eq, frobNorm_eq, ← Real.sqrt_mul (frobSq_nonneg A)]
  exact Real.sqrt_le_sqrt h

/-- `frobNorm (A − B) ≤ √2·(frobNorm A + frobNorm B)`. -/
theorem frobNorm_sub_le_sqrt_two (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    frobNorm (A - B) ≤ Real.sqrt 2 * (frobNorm A + frobNorm B) := by
  have hA := frobNorm_sq A
  have hB := frobNorm_sq B
  have hA0 := frobNorm_nonneg A
  have hB0 := frobNorm_nonneg B
  have hkey : frobSq (A - B) ≤ (Real.sqrt 2 * (frobNorm A + frobNorm B)) ^ 2 := by
    have h1 := frobSq_sub_le A B
    have h2 : (Real.sqrt 2 * (frobNorm A + frobNorm B)) ^ 2
        = 2 * (frobNorm A + frobNorm B) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [h2]
    nlinarith [h1, hA, hB, mul_nonneg hA0 hB0]
  have hrhs : 0 ≤ Real.sqrt 2 * (frobNorm A + frobNorm B) := by positivity
  calc frobNorm (A - B) = Real.sqrt (frobSq (A - B)) := frobNorm_eq _
    _ ≤ Real.sqrt ((Real.sqrt 2 * (frobNorm A + frobNorm B)) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt 2 * (frobNorm A + frobNorm B) := Real.sqrt_sq hrhs

/-- `|tr M|² ≤ 2·frobSq M` for a `2×2` matrix (Cauchy–Schwarz on the diagonal). -/
theorem normSq_trace_le (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Complex.normSq (Matrix.trace M) ≤ 2 * frobSq M := by
  rw [Matrix.trace_fin_two]
  have hcs : ∀ z w : ℂ, Complex.normSq (z + w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
    intro z w
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]
  have h := hcs (M 0 0) (M 1 1)
  have h01 := Complex.normSq_nonneg (M 0 1)
  have h10 := Complex.normSq_nonneg (M 1 0)
  unfold AdalyFormal.Balaban.RMapLipschitz.frobSq
  linarith

/-- `|(tr M).re| ≤ √2 · frobNorm M`. -/
theorem abs_re_trace_le (M : Matrix (Fin 2) (Fin 2) ℂ) :
    |(Matrix.trace M).re| ≤ Real.sqrt 2 * frobNorm M := by
  have hsq : ((Matrix.trace M).re) ^ 2 ≤ 2 * frobSq M := by
    have h1 : ((Matrix.trace M).re) ^ 2 ≤ Complex.normSq (Matrix.trace M) := by
      rw [Complex.normSq_apply, pow_two]
      nlinarith [mul_self_nonneg (Matrix.trace M).im]
    linarith [normSq_trace_le M]
  calc |(Matrix.trace M).re| = Real.sqrt (((Matrix.trace M).re) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * frobSq M) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * frobNorm M := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), frobNorm_eq]

/-- `|(tr M).im| ≤ √2 · frobNorm M`. -/
theorem abs_im_trace_le (M : Matrix (Fin 2) (Fin 2) ℂ) :
    |(Matrix.trace M).im| ≤ Real.sqrt 2 * frobNorm M := by
  have hsq : ((Matrix.trace M).im) ^ 2 ≤ 2 * frobSq M := by
    have h1 : ((Matrix.trace M).im) ^ 2 ≤ Complex.normSq (Matrix.trace M) := by
      rw [Complex.normSq_apply, pow_two]
      nlinarith [mul_self_nonneg (Matrix.trace M).re]
    linarith [normSq_trace_le M]
  calc |(Matrix.trace M).im| = Real.sqrt (((Matrix.trace M).im) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * frobSq M) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * frobNorm M := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), frobNorm_eq]

/-- `frobSq (↑X) = 2‖X‖²` for `X : 𝔰𝔲(2)` — the bridge between the intrinsic Hilbert-space norm the
coercivity is stated in and the full-matrix `frobSq` the trace estimates run in. -/
theorem frobSq_coe_suTwo (X : SuTwo) : frobSq (X : Matrix (Fin 2) (Fin 2) ℂ) = 2 * ‖X‖ ^ 2 := by
  have h := norm_sq_eq_half_frobSq X
  linarith

/-- `frobNorm (↑X) = √2·‖X‖`. -/
theorem frobNorm_coe_suTwo (X : SuTwo) :
    frobNorm (X : Matrix (Fin 2) (Fin 2) ℂ) = Real.sqrt 2 * ‖X‖ := by
  have h : frobNorm (X : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 = (Real.sqrt 2 * ‖X‖) ^ 2 := by
    rw [frobNorm_sq, frobSq_coe_suTwo, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have h0 : 0 ≤ frobNorm (X : Matrix (Fin 2) (Fin 2) ℂ) := frobNorm_nonneg _
  have h1 : 0 ≤ Real.sqrt 2 * ‖X‖ := by positivity
  nlinarith [h, h0, h1]

#print axioms su_coe_mul
#print axioms frobSq_conjTranspose
#print axioms frobSq_neg
#print axioms frobSq_smul
#print axioms frobSq_add_le
#print axioms frobSq_mul_left_isometry
#print axioms frobNorm_eq
#print axioms frobNorm_mul_le
#print axioms frobNorm_sub_le_sqrt_two
#print axioms normSq_trace_le
#print axioms abs_re_trace_le
#print axioms abs_im_trace_le
#print axioms frobSq_coe_suTwo
#print axioms frobNorm_coe_suTwo

/-! ## §2b — the plaquette curvature is bounded by the regularity parameter, GAUGE-INVARIANTLY

`frobSq (U(∂p) − 1) ≤ 32·α²` when every bond is within `α` of `1` (telescoping, four factors), and
the quantity is INVARIANT under gauge transformations (the holonomy conjugates). The second fact is
what lets the `GaugeRegular` hypothesis — smallness in SOME gauge — control the curvature of `U`
itself, which is the object `Δ′` is built from. -/

/-- `frobSq (g⁻¹ − 1) = frobSq (g − 1)` for `g ∈ SU(2)`. -/
theorem frobSq_inv_sub_one (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobSq (((g⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      = frobSq ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  rw [AdalyFormal.Balaban.RegularUQChain.su_coe_inv]
  have h : ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ - 1 = ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  rw [h, frobSq_conjTranspose]

/-- The telescoping step: `frobSq (g·h − 1) ≤ 2·frobSq (g−1) + 2·frobSq (h−1)` for unitaries. -/
theorem frobSq_mul_sub_one_le (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobSq (((g * h : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      ≤ 2 * frobSq ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        + 2 * frobSq ((h : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  set G := (g : Matrix (Fin 2) (Fin 2) ℂ) with hG
  set H := (h : Matrix (Fin 2) (Fin 2) ℂ) with hH
  have hsplit : (G * H - 1) = (G - 1) * H + (H - 1) := by noncomm_ring
  have hHunit : H * Hᴴ = 1 := by
    have h1 := Matrix.mem_unitaryGroup_iff.mp h.2.1
    rwa [Matrix.star_eq_conjTranspose] at h1
  rw [su_coe_mul, ← hG, ← hH, hsplit]
  calc frobSq ((G - 1) * H + (H - 1))
      ≤ 2 * frobSq ((G - 1) * H) + 2 * frobSq (H - 1) := frobSq_add_le _ _
    _ = 2 * frobSq (G - 1) + 2 * frobSq (H - 1) := by
        rw [frobSq_mul_right_isometry (G - 1) H hHunit]

/-- **THE CURVATURE BOUND.** If every bond value is within `α` of `1` in Frobenius norm, then every
plaquette holonomy is within `√32·α` of `1`: `frobSq (U(∂p) − 1) ≤ 32·α²`. Four factors, telescoped
with the weak triangle inequality (the honest cost of not proving the sharp one: `22` would suffice,
`32` is used for round arithmetic). -/
theorem frobSq_holonomy_sub_one_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L, frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (p : PeriodicLatticePlaquette L) :
    frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 32 * α ^ 2 := by
  have hbond : ∀ b : Bond L, frobSq ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α ^ 2 := by
    intro b
    have h1 := hα b
    have h0 := frobNorm_nonneg ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    have := frobNorm_sq ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    nlinarith [h1, h0, this]
  set a := U (p.1, p.2.1.1) with ha
  set b := U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) with hb
  set c := (U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ with hc
  set d := (U (p.1, p.2.1.2))⁻¹ with hd
  have hH : holonomyElem U p = a * b * c * d := rfl
  have hfa : frobSq ((a : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α ^ 2 := hbond _
  have hfb : frobSq ((b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α ^ 2 := hbond _
  have hfc : frobSq ((c : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α ^ 2 := by
    rw [hc, frobSq_inv_sub_one]; exact hbond _
  have hfd : frobSq ((d : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α ^ 2 := by
    rw [hd, frobSq_inv_sub_one]; exact hbond _
  have h1 := frobSq_mul_sub_one_le a b
  have h2 := frobSq_mul_sub_one_le (a * b) c
  have h3 := frobSq_mul_sub_one_le (a * b * c) d
  rw [hH]
  linarith [sq_nonneg α]

#print axioms frobSq_inv_sub_one
#print axioms frobSq_mul_sub_one_le
#print axioms frobSq_holonomy_sub_one_le

/-- Shifts in two DISTINCT coordinate directions commute. (`AdalyFormal.Lattice.Witness` has this
lemma, but that module is NOT in this file's import cone — measured, not assumed — and importing a
whole module for one three-line fact would enlarge the closure; LAW-19 disclosure: this is a
deliberate re-proof, and the two should be collapsed if `Lattice.Witness` ever enters the cone.) -/
theorem shift_comm_local (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hne : μ ≠ ν) :
    periodicLatticeShift (periodicLatticeShift x μ) ν
      = periodicLatticeShift (periodicLatticeShift x ν) μ := by
  have h1 : (periodicLatticeShift x μ) ν = x ν := by
    rw [periodicLatticeShift, Function.update_of_ne hne.symm]
  have h2 : (periodicLatticeShift x ν) μ = x μ := by
    rw [periodicLatticeShift, Function.update_of_ne hne]
  show Function.update (periodicLatticeShift x μ) ν ((periodicLatticeShift x μ) ν + 1)
      = Function.update (periodicLatticeShift x ν) μ ((periodicLatticeShift x ν) μ + 1)
  rw [h1, h2]
  show Function.update (Function.update x μ (x μ + 1)) ν (x ν + 1)
      = Function.update (Function.update x ν (x ν + 1)) μ (x μ + 1)
  exact Function.update_comm hne _ _ x

#print axioms shift_comm_local

/-- **HOLONOMY GAUGE COVARIANCE**: `U^γ(∂p) = γ(x)·U(∂p)·γ(x)⁻¹`, `x = p.1` the plaquette's base
site. The one combinatorial ingredient is `periodicLatticeShift_comm` (the two directions of a
plaquette are distinct, `p.2.2`), exactly as in
`RegularityHolonomy.holonomyElem_periodicGaugeTransform_trivialU`, whose `trivialU`-specialization
this generalizes. -/
theorem holonomyElem_gauge (γ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyElem (periodicGaugeTransform γ U) p
      = γ p.1 * holonomyElem U p * (γ p.1)⁻¹ := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  unfold holonomyElem
  change periodicGaugeTransform γ U (p.1, p.2.1.1) *
      periodicGaugeTransform γ U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
      (periodicGaugeTransform γ U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ *
      (periodicGaugeTransform γ U (p.1, p.2.1.2))⁻¹
    = γ p.1 * (U (p.1, p.2.1.1) * U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
      (U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ * (U (p.1, p.2.1.2))⁻¹) * (γ p.1)⁻¹
  simp only [periodicGaugeTransform, mul_inv_rev]
  rw [← shift_comm_local p.1 hne]
  group

/-- The curvature deviation is a GAUGE INVARIANT — conjugation by a unitary preserves `frobSq` and
fixes `1`. -/
theorem frobSq_holonomy_gauge_invariant (γ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    frobSq ((holonomyElem (periodicGaugeTransform γ U) p : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      = frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  have hg : ((γ p.1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (γ p.1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    AdalyFormal.Balaban.RegularUQChain.su_conjTranspose_mul (γ p.1)
  have hginv : ((γ p.1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
      * (((γ p.1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact hg
  rw [holonomyElem_gauge]
  have hsplit : ((γ p.1 * holonomyElem U p * (γ p.1)⁻¹ :
        Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1
      = (γ p.1 : Matrix (Fin 2) (Fin 2) ℂ) *
          ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) *
          ((γ p.1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
    rw [su_coe_mul, su_coe_mul, AdalyFormal.Balaban.RegularUQChain.su_coe_inv]
    have hu : (γ p.1 : Matrix (Fin 2) (Fin 2) ℂ) * ((γ p.1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ = 1 := by
      have h1 := Matrix.mem_unitaryGroup_iff.mp (γ p.1).2.1
      rwa [Matrix.star_eq_conjTranspose] at h1
    have hstep : (γ p.1 : Matrix (Fin 2) (Fin 2) ℂ)
          * ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          * ((γ p.1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
        = (γ p.1 : Matrix (Fin 2) (Fin 2) ℂ) * (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ)
            * ((γ p.1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
          - (γ p.1 : Matrix (Fin 2) (Fin 2) ℂ) * ((γ p.1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
      noncomm_ring
    rw [hstep, hu]
  rw [hsplit, frobSq_mul_right_isometry _ _ hginv, frobSq_mul_left_isometry _ _ hg]

/-- **THE CURVATURE BOUND FOR A `GaugeRegular` BACKGROUND** — the form the assembly consumes: a
background that is `α₀`-small in SOME gauge has all its plaquette curvatures bounded, with no gauge
named and no smallness assumed of `U` itself. -/
theorem frobSq_holonomy_of_gaugeRegular {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (p : PeriodicLatticePlaquette L) :
    frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 32 * α₀ ^ 2 := by
  obtain ⟨γ, hγ⟩ := hreg
  have hbond : ∀ b : Bond L,
      frobNorm (((periodicGaugeTransform γ U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α₀ :=
    fun b => le_trans (frobNorm_le_frobSupBond (periodicGaugeTransform γ U) b) hγ
  have h := frobSq_holonomy_sub_one_le (periodicGaugeTransform γ U) α₀ hα₀ hbond p
  rwa [frobSq_holonomy_gauge_invariant] at h

#print axioms holonomyElem_gauge
#print axioms frobSq_holonomy_gauge_invariant
#print axioms frobSq_holonomy_of_gaugeRegular

/-! ## §2c — the PER-PLAQUETTE `Δ′` bound

`Δ′`'s two terms (CMP99b (3.10), `DeltaPrime.lean` §3) are
`tr((D_UA)(p)²·(Re U(∂p) − 1))` and `tr(Σ i[A′,A′]·Im U(∂p))`. Both carry a curvature factor, which
§2b bounds by the regularity parameter; what is left is to bound the `A`-dependence — quadratically,
in the curl energy for the first term and in the four incident bond energies for the second. -/

/-- `hsInner X X = ‖X‖²`. -/
theorem hsInner_self_eq_norm_sq (X : SuTwo) : hsInner X X = ‖X‖ ^ 2 := by
  rw [← inner_eq_hsInner, real_inner_self_eq_norm_sq]

/-- `dstarDQuadForm U A = Σ_p ‖(D_U A)(p)‖²` — the curl energy, in the form the per-plaquette
estimates sum into. -/
theorem dstarDQuadForm_eq_sum_norm_sq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    dstarDQuadForm U A = ∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant U A p‖ ^ 2 := by
  unfold dstarDQuadForm covPlaqInner
  exact Finset.sum_congr rfl (fun p _ => hsInner_self_eq_norm_sq _)

/-- `frobSq (Re U(∂p) − 1) ≤ frobSq (U(∂p) − 1)`. -/
theorem frobSq_reHolonomy_sub_one_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    frobSq (reHolonomy U p - 1) ≤ frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  set H := (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) with hH
  set Hi := (holonomyElemInv U p : Matrix (Fin 2) (Fin 2) ℂ) with hHi
  have hsplit : reHolonomy U p - 1 = (1 / 2 : ℂ) • ((H - 1) + (Hi - 1)) := by
    unfold reHolonomy
    rw [← hH, ← hHi]
    module
  have hinv : frobSq (Hi - 1) = frobSq (H - 1) := by
    rw [hHi, hH]
    exact frobSq_inv_sub_one (holonomyElem U p)
  rw [hsplit, frobSq_smul]
  have hadd := frobSq_add_le (H - 1) (Hi - 1)
  have hnorm : Complex.normSq ((1 : ℂ) / 2) = 1 / 4 := by
    have h12 : ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
    rw [h12, Complex.normSq_ofReal]
    norm_num
  rw [hnorm, hinv] at *
  nlinarith [hadd, frobSq_nonneg (H - 1)]

/-- `frobSq (Im U(∂p)) ≤ frobSq (U(∂p) − 1)`. -/
theorem frobSq_imHolonomy_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    frobSq (imHolonomy U p) ≤ frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  set H := (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) with hH
  set Hi := (holonomyElemInv U p : Matrix (Fin 2) (Fin 2) ℂ) with hHi
  have hsplit : imHolonomy U p = (1 / (2 * Complex.I) : ℂ) • ((H - 1) - (Hi - 1)) := by
    unfold imHolonomy
    rw [← hH, ← hHi]
    congr 1
    abel
  have hinv : frobSq (Hi - 1) = frobSq (H - 1) := by
    rw [hHi, hH]
    exact frobSq_inv_sub_one (holonomyElem U p)
  have hnorm : Complex.normSq (1 / (2 * Complex.I)) = 1 / 4 := by
    rw [map_div₀, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_one]
    norm_num [Complex.normSq_apply]
  rw [hsplit, frobSq_smul, hnorm]
  have hsub := frobSq_sub_le (H - 1) (Hi - 1)
  rw [hinv] at hsub
  nlinarith [hsub, frobSq_nonneg (H - 1)]

#print axioms hsInner_self_eq_norm_sq
#print axioms dstarDQuadForm_eq_sum_norm_sq
#print axioms frobSq_reHolonomy_sub_one_le
#print axioms frobSq_imHolonomy_le

/-- `frobNorm (U(∂p) − 1) ≤ 4√2·α` for an `α`-regular background (§2b, in `frobNorm` form). -/
theorem frobNorm_holonomy_sub_one_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (p : PeriodicLatticePlaquette L) :
    frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 4 * Real.sqrt 2 * α₀ := by
  have h := frobSq_holonomy_of_gaugeRegular hα₀ U hreg p
  have hrhs : (0 : ℝ) ≤ 4 * Real.sqrt 2 * α₀ := by positivity
  have hsq : (4 * Real.sqrt 2 * α₀) ^ 2 = 32 * α₀ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  calc frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      = Real.sqrt (frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1)) := frobNorm_eq _
    _ ≤ Real.sqrt ((4 * Real.sqrt 2 * α₀) ^ 2) := Real.sqrt_le_sqrt (by rw [hsq]; exact h)
    _ = 4 * Real.sqrt 2 * α₀ := Real.sqrt_sq hrhs

/-- **THE FIRST `Δ′` TERM, bounded.** `|tr((D_UA)(p)²(Re U(∂p) − 1))| ≤ 16·α₀·‖(D_UA)(p)‖²` — the
curvature factor supplies the `α₀`, and the rest is the curl energy at that plaquette, so this term
absorbs into `dstarDQuadForm` itself. -/
theorem abs_deltaPrimeFirstTerm_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    |deltaPrimeFirstTerm U A p| ≤ 16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 := by
  set K := (curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ) with hK
  set R := reHolonomy U p - 1 with hR
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hfK : frobNorm K = Real.sqrt 2 * ‖curlValueCovariant U A p‖ := frobNorm_coe_suTwo _
  -- the curvature factor
  have hRle : frobNorm R ≤ 4 * Real.sqrt 2 * α₀ := by
    have h1 : frobSq R ≤ frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) :=
      frobSq_reHolonomy_sub_one_le U p
    have h2 := frobNorm_holonomy_sub_one_le hα₀ U hreg p
    calc frobNorm R = Real.sqrt (frobSq R) := frobNorm_eq _
      _ ≤ Real.sqrt (frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1)) :=
          Real.sqrt_le_sqrt h1
      _ = frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := (frobNorm_eq _).symm
      _ ≤ 4 * Real.sqrt 2 * α₀ := h2
  have hK0 : 0 ≤ frobNorm K := frobNorm_nonneg _
  have hR0 : 0 ≤ frobNorm R := frobNorm_nonneg _
  have hn0 : 0 ≤ ‖curlValueCovariant U A p‖ := norm_nonneg _
  have hstep : |deltaPrimeFirstTerm U A p| ≤ Real.sqrt 2 * (frobNorm K * frobNorm K * frobNorm R) := by
    have e1 : |deltaPrimeFirstTerm U A p| ≤ Real.sqrt 2 * frobNorm (K * K * R) := by
      unfold deltaPrimeFirstTerm
      rw [← hK, ← hR]
      exact abs_re_trace_le _
    have e2 : frobNorm (K * K * R) ≤ frobNorm (K * K) * frobNorm R := frobNorm_mul_le _ _
    have e3 : frobNorm (K * K) ≤ frobNorm K * frobNorm K := frobNorm_mul_le _ _
    have e4 : frobNorm (K * K * R) ≤ frobNorm K * frobNorm K * frobNorm R := by
      calc frobNorm (K * K * R) ≤ frobNorm (K * K) * frobNorm R := e2
        _ ≤ frobNorm K * frobNorm K * frobNorm R :=
            mul_le_mul_of_nonneg_right e3 hR0
    calc |deltaPrimeFirstTerm U A p| ≤ Real.sqrt 2 * frobNorm (K * K * R) := e1
      _ ≤ Real.sqrt 2 * (frobNorm K * frobNorm K * frobNorm R) :=
          mul_le_mul_of_nonneg_left e4 (Real.sqrt_nonneg 2)
  refine hstep.trans ?_
  rw [hfK]
  have hfin : Real.sqrt 2 * (Real.sqrt 2 * ‖curlValueCovariant U A p‖
        * (Real.sqrt 2 * ‖curlValueCovariant U A p‖) * frobNorm R)
      = 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 * frobNorm R := by
    have h : Real.sqrt 2 * (Real.sqrt 2 * ‖curlValueCovariant U A p‖
          * (Real.sqrt 2 * ‖curlValueCovariant U A p‖) * frobNorm R)
        = (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt 2
          * (‖curlValueCovariant U A p‖ * ‖curlValueCovariant U A p‖) * frobNorm R := by ring
    rw [h, hs2, sq]
  rw [hfin]
  have hmul : 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 * frobNorm R
      ≤ 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 * (4 * Real.sqrt 2 * α₀) := by
    have hcoef : (0 : ℝ) ≤ 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hRle hcoef
  refine hmul.trans (le_of_eq ?_)
  have h : 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 * (4 * Real.sqrt 2 * α₀)
      = 8 * (Real.sqrt 2 * Real.sqrt 2) * α₀ * ‖curlValueCovariant U A p‖ ^ 2 := by ring
  rw [h, hs2]
  ring

#print axioms frobNorm_holonomy_sub_one_le
#print axioms abs_deltaPrimeFirstTerm_le

/-! ### §2c.2 — the SECOND `Δ′` term: the commutator sum against `Im U(∂p)`

`tr(Σ_{b₁≺b₂} i[A′(b₁),A′(b₂)]·Im U(∂p))`. The commutators are quadratic in the four incident bond
values, and `Im U(∂p)` carries the curvature. The bound is per-plaquette; the plaquette→bond
incidence count (§2d) turns it into `bondEnergy`. -/

/-- The four incident bond energies of a plaquette — the quantity the commutator term is quadratic
in. -/
noncomputable def plaqBondSq (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : ℝ :=
  ‖A (p.1, p.2.1.1)‖ ^ 2 + ‖A (p.1, p.2.1.2)‖ ^ 2
    + ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
    + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2

theorem plaqBondSq_nonneg (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    0 ≤ plaqBondSq A p := by
  unfold plaqBondSq; positivity

/-- `|Im tr((XY − YX)·M)| ≤ 4·‖X‖_F‖Y‖_F‖M‖_F`. -/
theorem abs_im_trace_comm_le (X Y M : Matrix (Fin 2) (Fin 2) ℂ) :
    |(Matrix.trace ((X * Y - Y * X) * M)).im|
      ≤ 4 * frobNorm X * frobNorm Y * frobNorm M := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hX0 := frobNorm_nonneg X
  have hY0 := frobNorm_nonneg Y
  have hM0 := frobNorm_nonneg M
  have e1 : |(Matrix.trace ((X * Y - Y * X) * M)).im|
      ≤ Real.sqrt 2 * frobNorm ((X * Y - Y * X) * M) := abs_im_trace_le _
  have e2 : frobNorm ((X * Y - Y * X) * M) ≤ frobNorm (X * Y - Y * X) * frobNorm M :=
    frobNorm_mul_le _ _
  have e3 : frobNorm (X * Y - Y * X) ≤ Real.sqrt 2 * (frobNorm (X * Y) + frobNorm (Y * X)) :=
    frobNorm_sub_le_sqrt_two _ _
  have e4 : frobNorm (X * Y) ≤ frobNorm X * frobNorm Y := frobNorm_mul_le _ _
  have e5 : frobNorm (Y * X) ≤ frobNorm Y * frobNorm X := frobNorm_mul_le _ _
  have e6 : frobNorm (X * Y - Y * X) ≤ Real.sqrt 2 * (2 * (frobNorm X * frobNorm Y)) := by
    refine e3.trans ?_
    have : frobNorm (X * Y) + frobNorm (Y * X) ≤ 2 * (frobNorm X * frobNorm Y) := by
      nlinarith [e4, e5]
    exact mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg 2)
  have e7 : frobNorm ((X * Y - Y * X) * M)
      ≤ Real.sqrt 2 * (2 * (frobNorm X * frobNorm Y)) * frobNorm M :=
    e2.trans (mul_le_mul_of_nonneg_right e6 hM0)
  have e8 : |(Matrix.trace ((X * Y - Y * X) * M)).im|
      ≤ Real.sqrt 2 * (Real.sqrt 2 * (2 * (frobNorm X * frobNorm Y)) * frobNorm M) :=
    e1.trans (mul_le_mul_of_nonneg_left e7 (Real.sqrt_nonneg 2))
  refine e8.trans (le_of_eq ?_)
  have h : Real.sqrt 2 * (Real.sqrt 2 * (2 * (frobNorm X * frobNorm Y)) * frobNorm M)
      = (Real.sqrt 2 * Real.sqrt 2) * (2 * (frobNorm X * frobNorm Y) * frobNorm M) := by ring
  rw [h, hs2]; ring

/-- The six-commutator sum, bounded term by term at the TRACE level (so no triangle inequality for
`frobNorm` of a six-term sum is needed). -/
theorem abs_im_trace_commSum_le (a1 a2 a3 a4 M S : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : S = (a1 * a2 - a2 * a1) + (a1 * a3 - a3 * a1) + (a1 * a4 - a4 * a1)
      + (a2 * a3 - a3 * a2) + (a2 * a4 - a4 * a2) + (a3 * a4 - a4 * a3)) :
    |(Matrix.trace (S * M)).im|
      ≤ 4 * frobNorm M * (frobNorm a1 * frobNorm a2 + frobNorm a1 * frobNorm a3
          + frobNorm a1 * frobNorm a4 + frobNorm a2 * frobNorm a3 + frobNorm a2 * frobNorm a4
          + frobNorm a3 * frobNorm a4) := by
  have hsplit : Matrix.trace (S * M)
      = Matrix.trace ((a1 * a2 - a2 * a1) * M) + Matrix.trace ((a1 * a3 - a3 * a1) * M)
        + Matrix.trace ((a1 * a4 - a4 * a1) * M) + Matrix.trace ((a2 * a3 - a3 * a2) * M)
        + Matrix.trace ((a2 * a4 - a4 * a2) * M) + Matrix.trace ((a3 * a4 - a4 * a3) * M) := by
    rw [hS]
    simp only [Matrix.add_mul, Matrix.trace_add]
  rw [hsplit]
  simp only [Complex.add_im]
  have b12 := abs_im_trace_comm_le a1 a2 M
  have b13 := abs_im_trace_comm_le a1 a3 M
  have b14 := abs_im_trace_comm_le a1 a4 M
  have b23 := abs_im_trace_comm_le a2 a3 M
  have b24 := abs_im_trace_comm_le a2 a4 M
  have b34 := abs_im_trace_comm_le a3 a4 M
  have habs : |(Matrix.trace ((a1 * a2 - a2 * a1) * M)).im
        + (Matrix.trace ((a1 * a3 - a3 * a1) * M)).im
        + (Matrix.trace ((a1 * a4 - a4 * a1) * M)).im
        + (Matrix.trace ((a2 * a3 - a3 * a2) * M)).im
        + (Matrix.trace ((a2 * a4 - a4 * a2) * M)).im
        + (Matrix.trace ((a3 * a4 - a4 * a3) * M)).im|
      ≤ |(Matrix.trace ((a1 * a2 - a2 * a1) * M)).im|
        + |(Matrix.trace ((a1 * a3 - a3 * a1) * M)).im|
        + |(Matrix.trace ((a1 * a4 - a4 * a1) * M)).im|
        + |(Matrix.trace ((a2 * a3 - a3 * a2) * M)).im|
        + |(Matrix.trace ((a2 * a4 - a4 * a2) * M)).im|
        + |(Matrix.trace ((a3 * a4 - a4 * a3) * M)).im| := by
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ?_ (le_refl _)
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ?_ (le_refl _)
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ?_ (le_refl _)
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ?_ (le_refl _)
    exact abs_add_le _ _
  refine habs.trans ?_
  linarith [b12, b13, b14, b23, b24, b34]

#print axioms plaqBondSq_nonneg
#print axioms abs_im_trace_comm_le
#print axioms abs_im_trace_commSum_le

/-- The four `A′` components have the norms of the four incident bond values (`RMap` is an isometry,
negation preserves the norm). -/
theorem norm_AprimeXY (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖AprimeXY A p‖ = ‖A (p.1, p.2.1.1)‖ := rfl

theorem norm_AprimeWX (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖AprimeWX A p‖ = ‖A (p.1, p.2.1.2)‖ := by
  unfold AprimeWX; rw [norm_neg]

theorem norm_AprimeYZ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖AprimeYZ U A p‖ = ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ := by
  unfold AprimeYZ; rw [norm_RMap]

theorem norm_AprimeZW (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖AprimeZW U A p‖ = ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ := by
  unfold AprimeZW; rw [norm_neg, norm_RMap]

/-- **THE SECOND `Δ′` TERM, bounded.** `|tr(Σi[A′,A′]·Im U(∂p))| ≤ 72·α₀·(incident bond energy)`.
The `72` is `12` (six ordered pairs, AM–GM'd onto the four squares) times the curvature bound
`4√2·α₀ ≤ 6·α₀`. -/
theorem abs_deltaPrimeSecondTerm_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    |deltaPrimeSecondTerm U A p| ≤ 72 * α₀ * plaqBondSq A p := by
  set M := imHolonomy U p with hM
  set a1 := (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) with ha1
  set a2 := (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) with ha2
  set a3 := (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) with ha3
  set a4 := (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) with ha4
  set S := ((a1 * a2 - a2 * a1) + (a1 * a3 - a3 * a1) + (a1 * a4 - a4 * a1)
      + (a2 * a3 - a3 * a2) + (a2 * a4 - a4 * a2) + (a3 * a4 - a4 * a3)) with hS
  -- (i) the `I •` factor turns the real part into (minus) the imaginary part
  have hcs : commutatorMatrixSum U A p = Complex.I • S := rfl
  have hre : deltaPrimeSecondTerm U A p = -(Matrix.trace (S * M)).im := by
    unfold deltaPrimeSecondTerm
    rw [← hM, hcs, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
      Complex.I_re, Complex.I_im]
    ring
  rw [hre, abs_neg]
  -- (ii) the six-term trace bound
  have hbound := abs_im_trace_commSum_le a1 a2 a3 a4 M S hS
  -- (iii) the Frobenius norms of the `A′` components, in terms of the bond values
  have hf : ∀ (X : SuTwo), frobNorm (X : Matrix (Fin 2) (Fin 2) ℂ) = Real.sqrt 2 * ‖X‖ :=
    frobNorm_coe_suTwo
  set x1 := ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ with hx1
  set x2 := ‖A (p.1, p.2.1.2)‖ with hx2
  set x3 := ‖A (p.1, p.2.1.1)‖ with hx3
  set x4 := ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ with hx4
  have hfa1 : frobNorm a1 = Real.sqrt 2 * x1 := by
    rw [ha1, hf, hx1, norm_AprimeZW]
  have hfa2 : frobNorm a2 = Real.sqrt 2 * x2 := by
    rw [ha2, hf, hx2, norm_AprimeWX]
  have hfa3 : frobNorm a3 = Real.sqrt 2 * x3 := by
    rw [ha3, hf, hx3, norm_AprimeXY]
  have hfa4 : frobNorm a4 = Real.sqrt 2 * x4 := by
    rw [ha4, hf, hx4, norm_AprimeYZ]
  -- (iv) the curvature factor
  have hMle : frobNorm M ≤ 6 * α₀ := by
    have h1 : frobSq M ≤ frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
      rw [hM]; exact frobSq_imHolonomy_le U p
    have h2 := frobNorm_holonomy_sub_one_le hα₀ U hreg p
    have h3 : frobNorm M ≤ 4 * Real.sqrt 2 * α₀ := by
      calc frobNorm M = Real.sqrt (frobSq M) := frobNorm_eq _
        _ ≤ Real.sqrt (frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1)) :=
            Real.sqrt_le_sqrt h1
        _ = frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := (frobNorm_eq _).symm
        _ ≤ 4 * Real.sqrt 2 * α₀ := h2
    have h4 : Real.sqrt 2 ≤ 3 / 2 := AdalyFormal.Balaban.AlphaAnalyticity.sqrt_two_le
    nlinarith [h3, h4, hα₀]
  have hM0 : 0 ≤ frobNorm M := frobNorm_nonneg _
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hx10 : 0 ≤ x1 := norm_nonneg _
  have hx20 : 0 ≤ x2 := norm_nonneg _
  have hx30 : 0 ≤ x3 := norm_nonneg _
  have hx40 : 0 ≤ x4 := norm_nonneg _
  -- (v) assemble: 4·‖M‖_F·(Σ_{i<j} 2 x_i x_j) ≤ 12·‖M‖_F·Σ x_i² ≤ 72·α₀·Σ x_i²
  have hpair : frobNorm a1 * frobNorm a2 + frobNorm a1 * frobNorm a3
        + frobNorm a1 * frobNorm a4 + frobNorm a2 * frobNorm a3 + frobNorm a2 * frobNorm a4
        + frobNorm a3 * frobNorm a4
      ≤ 3 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
    rw [hfa1, hfa2, hfa3, hfa4]
    have hexp : Real.sqrt 2 * x1 * (Real.sqrt 2 * x2) + Real.sqrt 2 * x1 * (Real.sqrt 2 * x3)
        + Real.sqrt 2 * x1 * (Real.sqrt 2 * x4) + Real.sqrt 2 * x2 * (Real.sqrt 2 * x3)
        + Real.sqrt 2 * x2 * (Real.sqrt 2 * x4) + Real.sqrt 2 * x3 * (Real.sqrt 2 * x4)
        = (Real.sqrt 2 * Real.sqrt 2) * (x1 * x2 + x1 * x3 + x1 * x4 + x2 * x3 + x2 * x4
            + x3 * x4) := by ring
    rw [hexp, hs2]
    nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x1 - x4),
      sq_nonneg (x2 - x3), sq_nonneg (x2 - x4), sq_nonneg (x3 - x4)]
  have hfin : 4 * frobNorm M * (frobNorm a1 * frobNorm a2 + frobNorm a1 * frobNorm a3
        + frobNorm a1 * frobNorm a4 + frobNorm a2 * frobNorm a3 + frobNorm a2 * frobNorm a4
        + frobNorm a3 * frobNorm a4)
      ≤ 72 * α₀ * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
    have hsum0 : 0 ≤ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 := by positivity
    have hstep1 : 4 * frobNorm M * (frobNorm a1 * frobNorm a2 + frobNorm a1 * frobNorm a3
          + frobNorm a1 * frobNorm a4 + frobNorm a2 * frobNorm a3 + frobNorm a2 * frobNorm a4
          + frobNorm a3 * frobNorm a4)
        ≤ 4 * frobNorm M * (3 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2)) := by
      have h40 : (0 : ℝ) ≤ 4 * frobNorm M := by linarith
      exact mul_le_mul_of_nonneg_left hpair h40
    refine hstep1.trans ?_
    nlinarith [hMle, hsum0, hM0]
  refine hbound.trans (hfin.trans (le_of_eq ?_))
  unfold plaqBondSq
  rw [← hx1, ← hx2, ← hx3, ← hx4]
  ring

#print axioms norm_AprimeXY
#print axioms norm_AprimeWX
#print axioms norm_AprimeYZ
#print axioms norm_AprimeZW
#print axioms abs_deltaPrimeSecondTerm_le

/-! ## §2d — the GLOBAL `Δ′` bound, and THE ASSEMBLY

Two new incidence reindexings (the two BASE bonds of a plaquette; the two NEIGHBOUR bonds already
have theirs in `RegularUPerturbation` §11, reused not rebuilt), then the summed `Δ′` bound, then the
composition with the legs. -/

open AdalyFormal.Balaban.RegularUPerturbation (sum_nbr1_sq_le sum_nbr2_sq_le sum_dir_proj1_le
  sum_dir_proj2_le)

/-- **Base-1 energy reindex.** `∑_p ‖A(x,μ)‖² ≤ 2·bondEnergy A` (incidence `≤ d−1 = 2`). -/
theorem sum_base1_sq_le (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖A (p.1, p.2.1.1)‖ ^ 2 ≤ 2 * bondEnergy A := by
  have key : ∑ p : PeriodicLatticePlaquette L, ‖A (p.1, p.2.1.1)‖ ^ 2
      = ∑ dir : PeriodicPlaquetteDirections, ∑ y : PeriodicLatticeSite L, ‖A (y, dir.1.1)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [key]
  have hslice : ∀ ρ : Fin 3, (0 : ℝ) ≤ ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2 :=
    fun ρ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbe : bondEnergy A = ∑ ρ : Fin 3, ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2 := by
    unfold bondEnergy; rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hbe]
  exact sum_dir_proj1_le (fun ρ => ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2) hslice

/-- **Base-2 energy reindex.** `∑_p ‖A(x,ν)‖² ≤ 2·bondEnergy A`. -/
theorem sum_base2_sq_le (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖A (p.1, p.2.1.2)‖ ^ 2 ≤ 2 * bondEnergy A := by
  have key : ∑ p : PeriodicLatticePlaquette L, ‖A (p.1, p.2.1.2)‖ ^ 2
      = ∑ dir : PeriodicPlaquetteDirections, ∑ y : PeriodicLatticeSite L, ‖A (y, dir.1.2)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [key]
  have hslice : ∀ ρ : Fin 3, (0 : ℝ) ≤ ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2 :=
    fun ρ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbe : bondEnergy A = ∑ ρ : Fin 3, ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2 := by
    unfold bondEnergy; rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hbe]
  exact sum_dir_proj2_le (fun ρ => ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2) hslice

/-- **THE INCIDENCE BOUND.** `∑_p (four incident bond energies) ≤ 8·bondEnergy A` — four incidence
counts of `2`, all `d`-only: no lattice size, no scale, no `k`. -/
theorem sum_plaqBondSq_le (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, plaqBondSq A p ≤ 8 * bondEnergy A := by
  have hsplit : ∑ p : PeriodicLatticePlaquette L, plaqBondSq A p
      = (∑ p : PeriodicLatticePlaquette L, ‖A (p.1, p.2.1.1)‖ ^ 2)
        + (∑ p : PeriodicLatticePlaquette L, ‖A (p.1, p.2.1.2)‖ ^ 2)
        + (∑ p : PeriodicLatticePlaquette L,
            ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2)
        + (∑ p : PeriodicLatticePlaquette L,
            ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
    unfold plaqBondSq
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit]
  linarith [sum_base1_sq_le A, sum_base2_sq_le A, sum_nbr1_sq_le A, sum_nbr2_sq_le A]

#print axioms sum_base1_sq_le
#print axioms sum_base2_sq_le
#print axioms sum_plaqBondSq_le

/-- **THE GLOBAL `Δ′` BOUND — the missing analytic step of gap 2.**
`|⟨A,Δ′(U)A⟩| ≤ 16·α₀·⟨A,D*D A⟩ + 576·α₀·‖A‖²_{L²(bonds)}` for every `GaugeRegular α₀` background.
Both constants are absolute: no lattice size, no scale, no `k`, no background. The first piece is
proportional to the curl energy itself (so it is absorbed multiplicatively), the second to the bond
energy (so it is absorbed against the coercivity constant). -/
theorem abs_deltaPrimeQuadForm_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo) :
    |deltaPrimeQuadForm U A| ≤ 16 * α₀ * dstarDQuadForm U A + 576 * α₀ * bondEnergy A := by
  have hterm : ∀ p : PeriodicLatticePlaquette L,
      |deltaPrimePlaqTerm U A p|
        ≤ 16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 + 72 * α₀ * plaqBondSq A p := by
    intro p
    have h1 := abs_deltaPrimeFirstTerm_le hα₀ U hreg A p
    have h2 := abs_deltaPrimeSecondTerm_le hα₀ U hreg A p
    unfold deltaPrimePlaqTerm
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hstep : |deltaPrimeQuadForm U A|
      ≤ ∑ p : PeriodicLatticePlaquette L,
          (16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 + 72 * α₀ * plaqBondSq A p) := by
    unfold deltaPrimeQuadForm
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => hterm p))
  refine hstep.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← dstarDQuadForm_eq_sum_norm_sq]
  have h8 := sum_plaqBondSq_le A
  have hcoef : (0 : ℝ) ≤ 72 * α₀ := by linarith
  nlinarith [h8, hcoef, bondEnergy_nonneg A]

/-- The transported convention has the same absolute value (`DeltaPrime`'s global sign flip). -/
theorem abs_deltaPrimeQuadFormTransported_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo) :
    |deltaPrimeQuadFormTransported U A|
      ≤ 16 * α₀ * dstarDQuadForm U A + 576 * α₀ * bondEnergy A := by
  rw [deltaPrimeQuadFormTransported_eq_neg, abs_neg]
  exact abs_deltaPrimeQuadForm_le hα₀ U hreg A

#print axioms abs_deltaPrimeQuadForm_le
#print axioms abs_deltaPrimeQuadFormTransported_le

/-! ## §3 — THE ASSEMBLED COERCIVITY of `Δ_k` (this tree's (3.10) form) over the REGULAR class

The threshold and the constant are explicit absolute rationals. `assemblyAlpha = 10⁻⁷` is what the
crude constants of §2 force: the `Δ′` bond-energy term costs `576·α₀`, which must stay below the
`U = 1` base `γ₀ = 1/1728 ≈ 5.79·10⁻⁴`. A sharper `Δ′` bound would buy back most of the seven
decimal places; nothing in the STRUCTURE of the argument depends on the size of the threshold. -/

/-- The regularity threshold at which the assembly closes. -/
noncomputable def assemblyAlpha : ℝ := 1 / 10000000

/-- The assembled coercivity constant. -/
noncomputable def assemblyGamma : ℝ := 1 / 2000

theorem assemblyAlpha_pos : 0 < assemblyAlpha := by unfold assemblyAlpha; norm_num

theorem assemblyGamma_pos : 0 < assemblyGamma := by unfold assemblyGamma; norm_num

/-- **THE ASSEMBLY.** For EVERY background regular in the gauge-invariant (3.35) sense at
`α₀ = 10⁻⁷`, on the admissible subspace `axial ∩ ker Q₂(U)`, the tree's corrected `Δ_k` quadratic
form (`DeltaKFull.deltaKQuadFormCorrected`, CMP99b (3.10)) is bounded below by
`assemblyGamma · ‖A‖²_{L²(bonds)}` with `assemblyGamma = 1/2000` — a single absolute rational,
independent of the lattice `L`, of the background `U`, of the field `A`, and of the RG step.

This is the composition of leg (b2) (`AlphaAnalyticity.deltaJ_gaugeRegular_coercive`, which bounds
the `D*D` term only) with §2d's `Δ′` absorption. What it is NOT: see this module's header —
`deltaKQuadFormCorrected` is CMP99b p.392 (3.10)'s NON-recursive `Δ^η`, not p.428 (3.156)'s
recursive `Δ_k`, and `ell` is fixed at `2` by the imported base. -/
theorem deltaK_gaugeRegular_coercive
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular assemblyAlpha U) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0) :
    assemblyGamma * bondEnergy A ≤ deltaKQuadFormCorrected U A := by
  have hα0 : (0 : ℝ) ≤ assemblyAlpha := le_of_lt assemblyAlpha_pos
  have hthr : 96 * assemblyAlpha ^ 2 ≤ gammaZeroLit := by
    rw [gammaZeroLit_eq]; unfold assemblyAlpha; norm_num
  -- leg (b2): the `D*D` term
  have hleg := deltaJ_gaugeRegular_coercive hL hdvd assemblyAlpha hα0 hthr U hreg A hadm hkerU
  -- the constant's linear degradation off the `U = 1` base
  have hlin : gammaZeroLit - assemblyAlpha ≤ coercConst assemblyAlpha :=
    coercConst_ge_linear hα0 (by unfold assemblyAlpha; norm_num)
  have hg : gammaZeroLit = 1 / 1728 := gammaZeroLit_eq
  -- §2d: the `Δ′` absorption
  have habs := abs_deltaPrimeQuadFormTransported_le hα0 U hreg A
  have hlow : -(16 * assemblyAlpha * dstarDQuadForm U A + 576 * assemblyAlpha * bondEnergy A)
      ≤ deltaPrimeQuadFormTransported U A := neg_le_of_abs_le habs
  have hbe : 0 ≤ bondEnergy A := bondEnergy_nonneg A
  have hds : 0 ≤ dstarDQuadForm U A := dstarDQuadForm_nonneg U A
  have hstar : (1 / 1728 - assemblyAlpha) * bondEnergy A ≤ dstarDQuadForm U A := by
    have h1 : (gammaZeroLit - assemblyAlpha) * bondEnergy A ≤ coercConst assemblyAlpha * bondEnergy A :=
      mul_le_mul_of_nonneg_right hlin hbe
    rw [hg] at h1
    linarith [hleg, h1]
  have hK : deltaKQuadFormCorrected U A
      = dstarDQuadForm U A + deltaPrimeQuadFormTransported U A := rfl
  rw [hK]
  unfold assemblyGamma
  unfold assemblyAlpha at hlow hstar
  norm_num at hlow hstar
  linarith [hlow, hstar, hbe, hds]

#print axioms assemblyAlpha_pos
#print axioms assemblyGamma_pos
#print axioms deltaK_gaugeRegular_coercive

/-! ### §3b — the `k`-uniform (family) form, matching leg (b3)'s shape

The constants are bound BEFORE the index type, the lattice family, the background family and the
field family — the syntactic form of "`γ₀` independent of `k` and `U`" at a single block size. -/

/-- The `k`/scale-uniform predicate for the `Δ_k` form (the analogue of
`AlphaAnalyticity.Gamma0ScaleUniform`, now on `deltaKQuadFormCorrected` rather than on the `D*D`
term alone). -/
def DeltaKScaleUniform (γ₀' α₀ : ℝ) : Prop :=
  0 < γ₀' ∧ 0 < α₀ ∧
    ∀ (K : Type) (k : K) (Lf : K → PeriodicLatticeExtent)
      (Uf : (j : K) → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (Lf j))
      (Af : (j : K) → Bond (Lf j) → SuTwo),
      (∀ μ : Fin 3, 4 ≤ Lf k μ) → (∀ μ : Fin 3, (2 : ℕ) ∣ (Lf k μ + 1)) →
      GaugeRegular α₀ (Uf k) →
      (∀ y : PeriodicLatticeSite (Lf k), y ∈ CoarseLattice (Lf k) 2 →
        ∀ x : PeriodicLatticeSite (Lf k), x ∈ blockOf y 2 →
        ∀ b ∈ staircasePath y x, Af k b = 0) →
      (∀ b : CoarseBond (Lf k) 2, lineCoarseRestrictCov (Uf k) 2 (Af k) b = 0) →
      γ₀' * bondEnergy (Af k) ≤ deltaKQuadFormCorrected (Uf k) (Af k)

/-- **THE ASSEMBLY, `k`-uniform form.** -/
theorem deltaK_uniform_over_family : DeltaKScaleUniform assemblyGamma assemblyAlpha := by
  refine ⟨assemblyGamma_pos, assemblyAlpha_pos, ?_⟩
  intro K k Lf Uf Af hL hdvd hreg hadm hker
  exact deltaK_gaugeRegular_coercive hL hdvd (Uf k) hreg (Af k) hadm hker

#print axioms deltaK_uniform_over_family

/-! ## §4 — THE EXISTENTIAL-THRESHOLD FORM (the repair of the refuted statement's actual defect)

`TheLemma.theLemma_C_star_Delta_k_C_uniform` is false as written because `Mα₀thresh` is a
CALLER-SUPPLIED argument: the caller picks it, and a large choice empties the regularity hypothesis
(§1, `isRegular_vacuous_at_two_norm`). Bałaban's own sentence is existential — *"with `Mα₀`
sufficiently small"*. Below, the threshold is produced by the THEOREM, not consumed from the caller,
and `γ₀` is still bound first. -/

/-- **The lemma's shape with the threshold EXISTENTIALLY quantified.** `γ₀` first, then the
threshold, then `∀ U` regular, then `∀ A` admissible. Both witnesses are absolute rationals
(`1/2000`, `10⁻⁷`). -/
theorem deltaK_lemma_existential_threshold
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ thr : ℝ, 0 < thr ∧
      ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
        GaugeRegular thr U →
        ∀ A : Bond L → SuTwo,
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0) →
          (∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0) →
          γ₀ * bondEnergy A ≤ deltaKQuadFormCorrected U A :=
  ⟨assemblyGamma, assemblyGamma_pos, assemblyAlpha, assemblyAlpha_pos,
    fun U hreg A hadm hker => deltaK_gaugeRegular_coercive hL hdvd U hreg A hadm hker⟩

#print axioms deltaK_lemma_existential_threshold

/-! ## §5 — THE `C`-REPARAMETRIZATION LAYER: the reduction, and what it still needs

Bałaban's conclusion is `γ₀‖B̃‖² ≤ ⟨CB̃, Δ_k(U)CB̃⟩` over the FREE coordinates `B̃`, not over the bond
energy. Three inputs are needed to convert §3 into that shape, and they are stated as explicit
hypotheses on the reparametrization rather than assumed inside the constant:

1. `hlow` — `C` is bounded BELOW uniformly over the background family (`‖B̃‖² ≤ Kc·‖CB̃‖²_{L²}`, one
   `Kc` for all `U`). For a SINGLE `C` this follows from injectivity plus finite-dimensionality
   (`TheLemma.theLemma_U1_known_case`'s own route, `LinearMap.exists_antilipschitzWith`). For a
   `U`-INDEXED family — which is what Bałaban's `C` is, since (3.157) solves `(QB)(c) = 0` and `Q` is
   `U`-dependent — the UNIFORMITY of `Kc` across the family is a genuine additional demand and is
   exactly where a hidden `U`-dependence of `γ₀` would enter.
2. `hax`/`hker` — the range of `C` lands in the admissible subspace `axial ∩ ker Q₂(U)`. Note the
   subspace MOVES with `U`; that is why the family is indexed by `U` here (a single `U`-independent
   `C` whose range lies in `ker Q₂(U)` for EVERY regular `U` would have to land in the intersection
   over the whole regular class, and whether that intersection is nonzero is NOT settled here —
   stated as an open question, not silently assumed either way).

The reduction itself is unconditional given those inputs. -/

/-- **THE `C`-LAYER REDUCTION.** From §3 plus a uniform lower bound on the reparametrization family,
the lemma's own shape: one `γ₀ = assemblyGamma / Kc`, bound BEFORE the background and the free
coordinate. -/
theorem assembled_lemma_via_reparam
    {Btilde : Type*} [NormedAddCommGroup Btilde] [InnerProductSpace ℝ Btilde]
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (Cf : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L →
      (Btilde →L[ℝ] AdalyFormal.Balaban.CovariantOperators.BondFnL2 L))
    (Kc : ℝ) (hKc : 0 < Kc)
    (hlow : ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
      GaugeRegular assemblyAlpha U → ∀ Bt : Btilde,
        ‖Bt‖ ^ 2 ≤ Kc * bondEnergy (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)))
    (hax : ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
      GaugeRegular assemblyAlpha U → ∀ Bt : Btilde,
        ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
          ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x,
            AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt) b = 0)
    (hker : ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
      GaugeRegular assemblyAlpha U → ∀ Bt : Btilde,
        ∀ b : CoarseBond L 2,
          lineCoarseRestrictCov U 2
            (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)) b = 0) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
        GaugeRegular assemblyAlpha U → ∀ Bt : Btilde,
          γ₀ * ‖Bt‖ ^ 2 ≤ deltaKQuadFormCorrected U
            (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)) := by
  refine ⟨assemblyGamma / Kc, div_pos assemblyGamma_pos hKc, ?_⟩
  intro U hreg Bt
  have h1 := deltaK_gaugeRegular_coercive hL hdvd U hreg
    (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)) (hax U hreg Bt) (hker U hreg Bt)
  have h2 := hlow U hreg Bt
  have hγ0 : 0 < assemblyGamma := assemblyGamma_pos
  have hstep : assemblyGamma / Kc * ‖Bt‖ ^ 2
      ≤ assemblyGamma / Kc * (Kc * bondEnergy
          (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt))) :=
    mul_le_mul_of_nonneg_left h2 (le_of_lt (div_pos hγ0 hKc))
  have heq : assemblyGamma / Kc * (Kc * bondEnergy
        (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)))
      = assemblyGamma * bondEnergy
        (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)) := by
    field_simp
  rw [heq] at hstep
  linarith [hstep, h1]

#print axioms assembled_lemma_via_reparam

/-! ## §6 — JUNK ATTACKS on §3's own statement

Run against the assembled theorem, not against its inputs. Each is a compiled theorem. -/

/-- `GaugeRegular` is monotone in the threshold (needed to feed `α₀ = 0` witnesses into the
assembly's `α₀ = 10⁻⁷` hypothesis). -/
theorem gaugeRegular_mono {α β : ℝ} (hab : α ≤ β)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (h : GaugeRegular α U) : GaugeRegular β U := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, le_trans hγ hab⟩

/-- **JUNK 1 — the zero field makes the assembled inequality `0 ≤ 0`.** Recorded explicitly, for
EVERY background (no regularity needed): the theorem has content only against a nonzero-energy
witness, which JUNK 2 supplies. -/
theorem assembly_trivial_at_zero_field
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    bondEnergy (0 : Bond L → SuTwo) = 0 ∧ deltaKQuadFormCorrected U 0 = 0 := by
  have hbe : bondEnergy (0 : Bond L → SuTwo) = 0 := by unfold bondEnergy; simp
  refine ⟨hbe, ?_⟩
  have hcurl : ∀ p : PeriodicLatticePlaquette L,
      curlValueCovariant U (0 : Bond L → SuTwo) p = 0 := by
    intro p; unfold curlValueCovariant; simp
  have hds : dstarDQuadForm U (0 : Bond L → SuTwo) = 0 := by
    rw [dstarDQuadForm_eq_sum_norm_sq]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [hcurl p, norm_zero]; norm_num
  have hdp : deltaPrimeQuadForm U (0 : Bond L → SuTwo) = 0 := by
    unfold deltaPrimeQuadForm
    refine Finset.sum_eq_zero (fun p _ => ?_)
    unfold deltaPrimePlaqTerm deltaPrimeFirstTerm deltaPrimeSecondTerm commutatorMatrixSum
      AprimeXY AprimeYZ AprimeZW AprimeWX
    rw [hcurl p]
    simp
  have hK : deltaKQuadFormCorrected U (0 : Bond L → SuTwo)
      = dstarDQuadForm U 0 + deltaPrimeQuadFormTransported U 0 := rfl
  rw [hK, hds, deltaPrimeQuadFormTransported_eq_neg, hdp]
  ring

/-- **JUNK 3 — the regularity hypothesis at the assembly threshold is a GENUINE restriction.**
Any background carrying a plaquette holonomy equal to `witnessMElem` (Frobenius distance `2` from
`1`, i.e. `frobSq = 4`) is NOT `GaugeRegular` at `10⁻⁷`: §2b's curvature bound forces
`4 ≤ 32·α₀²`, i.e. `α₀ ≥ 1/(2√2) ≈ 0.354`. So the assembled theorem is not quantifying over
everything. -/
theorem not_gaugeRegular_of_holonomy_witnessMElem
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (h : holonomyElem U p = witnessMElem) :
    ¬ GaugeRegular assemblyAlpha U := by
  intro hreg
  have hb := frobSq_holonomy_of_gaugeRegular (le_of_lt assemblyAlpha_pos) U hreg p
  rw [h] at hb
  have hval : frobSq ((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 4 := by
    simp [AdalyFormal.Balaban.RMapLipschitz.frobSq, witnessMElem, witnessM, Matrix.one_apply]
    norm_num [Complex.normSq_apply]
  rw [hval] at hb
  unfold assemblyAlpha at hb
  norm_num at hb

/-- **JUNK 4 — the threshold is LOAD-BEARING for this route, not decorative.** With §2d's constants
the assembled constant `(1 − 16α)(γ₀ − α) − 576α` is NEGATIVE already at `α = 10⁻³`: the `Δ′`
bond-energy term (`576α`) overwhelms the `U = 1` base `γ₀ = 1/1728`. So the seven decimal places in
`assemblyAlpha` are forced by the crude `Δ′` constants, and a sharper `Δ′` bound — not a different
structure — is what would buy them back. -/
theorem assembly_constant_negative_at_thousandth :
    (1 - 16 * (1 / 1000 : ℝ)) * (1 / 1728 - 1 / 1000) - 576 * (1 / 1000) < 0 := by
  norm_num

#print axioms gaugeRegular_mono
#print axioms assembly_trivial_at_zero_field
#print axioms not_gaugeRegular_of_holonomy_witnessMElem
#print axioms assembly_constant_negative_at_thousandth

/-! ## §7 — GAP 1 (BLOCK SIZE), determined rather than deferred

**The question.** Leg (b3) is uniform in the RG step at a FIXED block size `ell = 2`, because the
imported `U = 1` base is `ell = 2`. Does that suffice for the lemma as stated?

**What was measured (declaration statements read, not summaries):**

* `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` — the leg's input — has `2` hardcoded in
  FOUR places: `CoarseLattice L 2`, `blockOf y 2`, `CoarseBond L 2`/`lineCoarseRestrictCov U 2`, and
  the constant `(1/108)·(1/2⁴)`.
* Its own `U = 1` input, `SuTwoGeomU1.suTwoGeomAdditive_trivialU_of_admissible`, is likewise
  `SuTwoGeomAdditiveInequality 2 (trivialU L) ((1/108)·(1/2⁴))` — `ell = 2` in the STATEMENT.
* **But the SCALAR general-`ell` Lemma 2.4 already exists**:
  `Lemma24GeneralEll.lemma24_general_ell (hell2 : 2 ≤ ell) (hstrict) (hdvd) (B : Bond L → ℝ)
  (hB : B ∈ admissibleSubspaceInter L ell) : Lemma24ConclusionCorrected ell B` — general `ell`, with
  the CORRECTED `ell⁻⁵` exponent (the printed `ell⁻⁴` is proved unreachable for large `ell` by
  `BlockPoincareSharp.no_subcubic_block_poincare`).

**The determination.**

1. `ell = 2` DOES give `k`-uniformity for the RG tower whose block size is `2`: `k` enters the
   statement only through the lattice/background/field family, and §3b binds both constants before
   that family. There is no residual `k`-dependence to remove at fixed block size.
2. `ell = 2` does NOT give the lemma at any other block size, and Bałaban's `L` is a fixed parameter
   his construction elsewhere requires LARGE. So a lemma for a general-`L` tower needs the general-`ell`
   chain.
3. The general-`ell` obstruction is NOT the missing scalar base (it exists, item 3 above) and is NOT
   `RES-CERT-ELL3` (the `ell = 3` SOS certificate) either, since `lemma24_general_ell` is already
   general. **It is the `SCALAR → 𝔰𝔲(2)` vectorization step**: `SuTwoGeomU1` transports the scalar
   `(2.128)` to the `𝔰𝔲(2)`-valued additive inequality at `ell = 2` only, and the perturbation chain
   (`RegularUQChain`'s drift bound is already general-`ell`, `64/ell`) consumes that `ell = 2`
   statement. Generalizing the assembly is therefore a re-run of `SuTwoGeomU1` at general `ell` over
   `lemma24_general_ell`, with the constant becoming `(1/54)·ell⁻⁵`-shaped rather than
   `(1/108)·ell⁻⁴`. That file is outside this lane's write scope; the input it would need is named
   above by declaration, not by description.
4. Consequence for the assembled constant: at general `ell` the base degrades like `ell⁻⁵` while §2d's
   `Δ′` cost is `ell`-INDEPENDENT (`576·α₀`, four incidence counts of `2`, no block size anywhere), so
   the threshold would have to shrink like `ell⁻⁵` — the assembly closes at every `ell` but with an
   `ell`-dependent threshold. That is a statement about THIS route's constants, not about Bałaban's.

## §8 — WHAT THIS MODULE DOES NOT CLAIM (read with §3)

* `deltaKQuadFormCorrected` is `DeltaKFull`'s corrected CMP99b **p.392 (3.10)** form, `dstarDQuadForm
  + deltaPrimeQuadFormTransported`. It is **NOT** p.428 **(3.156)**'s recursive `Δ_k`, and no bridge
  between them exists in this tree (`TheLemma` §3's own caveat, unchanged).
* The `C`-layer (§5) is a REDUCTION with three explicit hypotheses, two of which (`hax`/`hker`) assert
  that the reparametrization lands in the `U`-dependent admissible subspace. Whether Bałaban's actual
  `C` (3.157) satisfies them is not settled here; §5's docstring states precisely why the family must
  be `U`-indexed and where a hidden `U`-dependence of `γ₀` could still enter (the uniformity of `Kc`).
* The regularity predicate used is `AlphaAnalyticity.GaugeRegular` — CMP99b (3.35)'s FIRST clause with
  its `∃ u` restored, at the GLOBAL-cube specialization. The cube decomposition (M5), the exponential
  chart, and (3.36) remain proxied exactly as `AlphaAnalyticity`'s header discloses.
* §1's dichotomy is about `TheLemma.IsRegular`. It says nothing about whether `GaugeRegular` is the
  right predicate — that is `AlphaAnalyticity`'s claim, and it is prosecuted there.
-/

end AdalyFormal.Balaban.LemmaAssembly
