/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
/-
# RETRACTION NOTICE — READ BEFORE ANY OTHER LINE IN THIS FILE (2026-07-30)

`compute/wideness_retraction/`, acting on `compute/sol_regularity/SOL_VERDICT.md` (a
de-correlated Sol-family prosecution, gpt-5.6-sol xhigh, of `compute/regularity_gap/` at commit
`e19d84eb`).

## WHAT THIS FILE ESTABLISHES

§1-§11 prove, and the prosecution could NOT refute, a complete conditional comparison between
`AlphaAnalyticity.GaugeRegular α` and a **tree-local coordinatewise predicate** — narrowness below
`2π·α < c·Lj⁻³`, a constructed one-excited-bond wideness witness above `4·c·Lj⁻¹ ≤ α`, the
gauge-invariant curvature floor that makes the witness survive every gauge, `η`-cancellation, the
exact `8π·(L^j)²` band and its `√2` sharpening. All of that stands.

§12-§14 (added by this lane) build the EXTERIOR operator `∂^{η*}∂^η`, prove its adjoint identity,
kernel-check that it differs from the coordinatewise stencil, define the printed cube class, and
re-run narrowness and wideness against a faithful predicate.

## WHAT THIS FILE DOES **NOT** ESTABLISH

**It does not settle the containment between `GaugeRegular` and printed CMP99b (3.35) ∧ (3.36).**
That question is **UNSETTLED, in both directions.** Anything in §1-§11 that reads as if it did is
retracted; the theorems are unchanged, their SUBJECT was misnamed.

## THE THREE CONVICTED DEFECTS, and what was done about each

1. **WRONG OPERATOR.** (3.36) bounds `∂^{η*}∂^ηA`, the lattice EXTERIOR derivative composed with
   its adjoint — `∂^η` maps `0`-forms to `1`-forms (CMP95 p.20, `A^λ = A − ∂^ηλ`), hence `1`-forms
   to `2`-forms, and `∂^{η*}` sums plaquette components over `ν`. What §1 defined (then called
   `lapA`) is a COORDINATEWISE forward second difference, one direction at a time. CMP99a p.99
   eq. (1.136) prints `|∂^{η*}∂^ηA|` and `|Δ^ηA|` as SEPARATE quantities in one display, so the
   source itself distinguishes the exterior operator from a Laplacian
   (image: `compute/wideness_retraction/renders/CMP99a_p99-25.png`).
   → `lapA` is renamed `coordLapA`; §12 builds `extD` / `extDStar` / `extDStarD` with the adjoint
   identity `extD_adjoint` PROVED; and `coordSecondDiff_ne_extDStarD` kernel-checks a `1`-form at
   which every coordinatewise second difference vanishes while `extDStarD` does not.
2. **THE PRINTED CUBE CLASS WAS DROPPED.** `cube : Finset (Bond L)` carried no tie to `j`, `Ω`,
   `Λ`, `B^j`, block geometry, size or nonemptiness, so the EMPTY `Finset` satisfies all four
   obligations vacuously at arbitrary `η, Lj, c`.
   → §13 defines `IsSourceCube` (a coordinate box with the printed side floor `10·Lj ≤ s` at
   `1 ≤ Lj`), and proves `empty_not_isSourceCube`, `singleton_not_isSourceCube`,
   `nonempty_of_isSourceCube`, `exists_isSourceCube`.
3. **THE "SOURCE CLASS ⊄ `GaugeRegular`" DIRECTION USED A SINGLETON CUBE**, also outside the
   printed class. → `region_witness` is renamed `proxyRegion_witness` and is NOT restated at a
   printed cube; see the RESIDUAL below. The WIDE direction, which turns only on the first clause,
   IS restated at a genuine printed cube:
   `exists_faithfulWideness_witness_onSourceCube`.

A fourth conviction is arithmetic: the `Mα₀` numbers quoted in `e19d84eb`'s commit message treat
the printed floor `O(1) ≥ 10` as the equality `O(1) = 10`. At `O(1) = 100` the implications invert
in both directions. Nothing in this FILE asserts those numbers — `narrow_condition_at_alphaEll` and
`wide_condition_at_alphaEll` are conditions on the product `c = O(1)Mα₀` and never split it — so
this file needs no repair on that count; `CoercUMainDesigned` §2a carries the correction of record.

## RENAMES (2026-07-30) — no statement, hypothesis, constant or proof was altered

A name saying "3536" must not denote something that is not (3.35)/(3.36).

| was | is now |
|---|---|
| `Src3536` | `CoordProxy3536` |
| `Src3536Log` | `CoordProxy3536Log` |
| `lapA`, `lapA_norm` | `coordLapA`, `coordLapA_norm` |
| `src3536_eta_free` | `coordProxy3536_eta_free` |
| `src3536Log_of_gaugeRegular*` | `coordProxy3536Log_of_gaugeRegular*` |
| `frobSupBond_lt_of_src3536Log` | `frobSupBond_lt_of_coordProxy3536Log` |
| `not_src3536Log_of_curvature` | `not_coordProxy3536Log_of_curvature` |
| `wideness_witness`, `exists_wideness_witness*` | `proxyWideness_witness`, `exists_proxyWideness_witness*` |
| `wideness_at_large_cube` | `proxyWideness_at_large_cube` |
| `region_witness` | `proxyRegion_witness` |
| `containment_dichotomy` | `proxyContainment_dichotomy` |

`CoordProxy3536` keeps the numerals deliberately: it names what it is a proxy FOR, and says it is
a proxy. The old names no longer resolve anywhere, so a stale citation fails loudly instead of
binding silently to a different meaning.

**FINDING, out of write scope (LAW-4).** `Balaban/AlphaAnalyticity.lean` cites three of the old
names in prose. Those citations are now phantom. The needed edit is mechanical:
`src3536_eta_free` -> `coordProxy3536_eta_free`,
`src3536Log_of_gaugeRegular_uncond` -> `coordProxy3536Log_of_gaugeRegular_uncond`,
`exists_wideness_witness` -> `exists_proxyWideness_witness`; and the sentence's claim that those
theorems concern (3.35)/(3.36) must be corrected to the proxy. That file is not in this lane's
write scope and was not edited.

## WHAT §12-§14c DO AND DO NOT BUY — the one-line version; §16 has the table

**Do:** the BENIGN containment `GaugeRegular α ⊆ (3.35)∧(3.36)` is re-proved against the EXTERIOR
operator, for EVERY cube, at the recounted threshold `12π·α < c·Lj⁻³`
(`src3536FaithfulLog_of_gaugeRegular`). Both the `Finset.univ` wideness construction and the
singleton region construction are replaced by constructions at boxes of a modelled cube class
(`exists_faithfulWideness_witness_onSourceCube`, `exists_faithfulRegion_witness_onSourceCube`).

**Do NOT:** settle the containment in the non-benign direction. `IsSourceCube` is a RELAXATION of
the printed class (it omits the domain-sequence clauses), and the two `∃`-witnesses each act at ONE
box, whereas the source's condition is `∀ □ of the class`. A one-box failure inside a SUPERSET does
not negate a `∀` over a SUBSET, and a one-box success does not establish it. §16 states this in
full, with what would settle it.

**So the operative status is unchanged by this repair: UNSETTLED, in the non-benign direction.**

---
---

LANDED 2026-07-30 from `compute/regularity_gap/scratch/RegularityGap.lean` (committed
`e19d84eb`) by the `compute/regularity_propagate/` lane.

**EXACT INVENTORY OF THE CHANGES TO THE LANDED CONTENT** — corrected after this lane's own nested
validator caught the first version of this note undercounting its own diff by one line, which is
the defect class this file exists to document. `git diff` of the landed region (everything up to
`#print axioms proxyContainment_dichotomy`) against `e19d84eb` is 3 hunks / 20 lines:

1. this header block and the copyright block above it (comment);
2. the namespace rename `AdalyFormal.RegularityGapScratch` → `AdalyFormal.Balaban.RegularityGap`;
3. **one added import, `Mathlib.Analysis.Convex.SpecificFunctions.Deriv`** — a real Lean line, not
   a comment. It is used only by §11 (`strictConcaveOn_sin_Icc`) and by nothing in the landed
   content.

**No statement, hypothesis, numeric constant or tactic of the landed content was touched.** That
narrower claim is what the reader should rely on; the earlier "these are the ONLY changes" phrasing
was not accurate and is not restored.

§10 and §11 are ADDITIONS BY THIS LANE, clearly marked as such at their headings. They add; they do
not modify. In particular `coordProxy3536Log_of_gaugeRegular` and `coordProxy3536Log_of_gaugeRegular_uncond` are
untouched, and §11's sharpened variants sit beside them rather than replacing them.

It is landed because `CoercUMainDesigned` §2a now cites its theorems by name, and a citation of a
scratch file is not a citation of the tree. `CoercUMainDesigned` imports this module, so it is
reachable from `Spine`. REACHABLE IS NOT CONSUMED: no proof term in `Spine.main` invokes any
declaration here, and adding the import left `#print axioms` on every `CoercUMainDesigned` (70
records) and `Spine` (96 records) declaration bit-identical, with `AlphaAnalyticity` (62) and
`CoercUMainRegular` (71) likewise unchanged and zero records lost tree-wide
(`compute/regularity_propagate/axioms_diff.txt`). That invariance is the evidence the §2a edit is
prose-only.

# Which class contains which: `GaugeRegular α` versus CMP99b (3.35) ∧ (3.36)?

`AlphaAnalyticity.GaugeRegular α₀ U := ∃ γ, frobSupBond (U^γ) ≤ α₀`, a single GLOBAL
Frobenius sup bound on the group elements, with a threshold `alphaEll ell = 10⁻⁵·ell⁻⁵`
that is a pure number.

CMP99b p.396, image-adjudicated (`corpus/pages/CMP99b_p396.md`, render
`corpus/renders/CMP99b_p396-08.png`, `verification_status: adjudicated`):

> for an arbitrary cube □ of the described above class, and for a configuration `U` there
> exists a gauge transformation `u` on □ such that `U^u = e^{iηA}`, and if the index of □ is
> `j`, then
>   `|A| < O(1)Mα₀(L^jη)⁻¹`,  `|∇^ηA| < O(1)Mα₀(L^jη)⁻²`   on □,
>   where `O(1)M` is a size of □ in `T_{L^{-j}}`;                        (3.35)
>   `|∂^{η*}∂^ηA| < O(1)Mα₀(L^jη)⁻³`   on □.                            (3.36)

(The trailing clause of (3.35) is restored here after a nested validator caught it being
dropped without an ellipsis. It fixes the CUBE SIZE, not the inequality: the cube is
`O(1)M` blocks of `T_{L^{-j}}` across, i.e. `O(1)ML^jη` in `T_η`, with `O(1) ≥ 10`. Nothing
below consumes the cube's size — `cube : Finset (Bond L)` is left unconstrained, and that
genericity is used SYMMETRICALLY: narrowness is proved for EVERY `cube`, and the region
witness picks the smallest nonempty one.)
> ... Here `O(1)` will mean a number ≥ 10. ... We will need `α₀` so small that `O(1)Mα₀` is
> still a sufficiently small number. Let us notice that these regularity conditions do not
> impose any constraints on `U` outside the domain `Ω₀`.

This file formalizes (3.35)/(3.36) WITH their scale parameters (`η`, `Lj = L^j`, and the
product `c = O(1)Mα₀`) and settles the comparison.

## What is proved here

* `coordProxy3536_eta_free` — **`η` CANCELS IDENTICALLY from all three clauses.** The predicate with
  `η` is equivalent to one with no `η` in it. Only `Lj` and `c = O(1)Mα₀` survive.
* `coordProxy3536Log_of_gaugeRegular` — **NARROWNESS holds below an explicit threshold**:
  `2π·α < c·Lj⁻³` ⟹ `GaugeRegular α ⊆ (3.35)∧(3.36)`. Modulo `hbranch` (§5).
* `proxyWideness_witness` — **WIDENESS holds above an explicit threshold, with a CONSTRUCTED
  witness**: if `4·c·Lj⁻¹ ≤ frobNorm (g − 1) ≤ α` then the single-excited-bond configuration
  `oneBondU b₀ g` is `GaugeRegular α` and satisfies NEITHER (3.35) NOR (3.36), in EVERY gauge.
* `proxyRegion_witness` — **(3.35)∧(3.36) ⊄ `GaugeRegular`, unconditionally in the constants**:
  the source's conditions are cube-local, `GaugeRegular` is global.

Together: the two classes are INCOMPARABLE, and which containment fails is decided by the
single dimensionless ratio `α·Lj³ / c`.

## Convention pin — see §1a for the CORRECTED version

~~`SuTwoLogExpCore.su2Log` is documented as "`(1/i) log` of CMP109 (0.4)". Hence the source's
chart `U^u = e^{iηA}` gives `A(b) = η⁻¹ · su2Log (U^u b)`, which is what `chartA` below is.~~
**STRUCK (S75, corrected in this lane).** `su2Log` is the ORDINARY anti-Hermitian matrix
logarithm, not `(1/i)log` — `su2Log_antiHermitian` and `su2Exp (su2Log g) = g` with
`su2Exp = NormedSpace.exp` both prove it, and the upstream docstring is wrong about its own
object. So the source's field is `A = (iη)⁻¹ · su2Log (U^u)` and `chartA = i·A`. **§1a proves
this changes nothing**: `frobNorm_chartA_eq_srcA` shows `‖chartA‖_F = ‖A‖_F` exactly, and
`chart_equation` shows the chart conjunct really is `U^u = e^{iηA}` for the source's `A`.

The chart equation is carried as an explicit conjunct (`su2Exp (su2Log (V b)) = V b`), never
assumed away — and it is exactly what makes the wideness direction provable, since it forces
`V b ≠ −1`.
-/
import AdalyFormal.Balaban.AlphaAnalyticity
import AdalyFormal.Balaban.BlockingLinkEstimate
import AdalyFormal.Balaban.NonFlatBackground
-- §11 only: `Real.strictConcaveOn_sin_Icc`, for the half-range Jordan inequality.
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

set_option autoImplicit false
set_option maxRecDepth 40000

namespace AdalyFormal.Balaban.RegularityGap

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.RMapLipschitz
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond
  frobSupBond_nonneg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeRegular gaugeRegular_of_frobSupBond_le)
open AdalyFormal.Balaban.BlockingLinkEstimate (frobNorm_add_le frobNorm_real_smul
  frobNorm_su2Log_le_pi_div_two frobNorm_sub_one_le_frobNorm_su2Log frobNorm_conj_sub_one
  frobNorm_sub_one_eq cos_su2Angle)
open AdalyFormal.Balaban.RegularUQChain (frobNorm_su_mul_sub_one_le frobNorm_su_inv_sub_one)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem)
open AdalyFormal.Balaban.NonFlatBackground (holonomyElem_periodicGaugeTransform)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — small `frobNorm` helpers (not present upstream in this shape) -/

theorem frobNorm_neg (M : M2) : frobNorm (-M) = frobNorm M := by
  have h : (-M) = (((-1 : ℝ) : ℂ)) • M := by
    push_cast; module
  rw [h, frobNorm_real_smul]
  norm_num

theorem frobNorm_sub_le (M N : M2) : frobNorm (M - N) ≤ frobNorm M + frobNorm N := by
  have h : M - N = M + (-N) := sub_eq_add_neg M N
  rw [h]
  exact le_trans (frobNorm_add_le _ _) (by rw [frobNorm_neg])

/-! ## §0b — THE BRANCH LEMMA (`exp ∘ log = id` off the single antipode)

The narrowness direction must EXHIBIT the source's chart `U^u = e^{iηA}`, so it needs
`su2Exp (su2Log g) = g`. The tree had this only on `conjPrincipal` (`g = h·torus t·h⁻¹`,
`0 ≤ t < π`), with no criterion for membership. It is proved here for every `g ≠ −1`, by the
route `X := su2Log g` satisfies `X² = −θ²·1` (Cayley–Hamilton from unitarity) and hence
`ℝ[X] ≅ ℂ`, so `exp` transports along `Complex.liftAux` (`NormedSpace.map_exp`). -/

section Branch

open scoped Matrix

/-- `g + gᴴ = (tr g) • 1` for `g ∈ SU(2)` (`gᴴ = adj g` and `adj g = (tr g)·1 − g` in 2×2). -/
theorem su2_add_conjTranspose (g : SU2) :
    (g : M2) + (g : M2)ᴴ = (Matrix.trace (g : M2)) • (1 : M2) := by
  rw [su2_conjTranspose_eq_adjugate g]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, Matrix.add_apply] <;> ring

/-- The trace of an `SU(2)` element is `2 cos θ`, as a COMPLEX number (its imaginary part
vanishes). -/
theorem su2_trace_eq (g : SU2) :
    Matrix.trace (g : M2) = ((2 * Real.cos (su2Angle g) : ℝ) : ℂ) := by
  have hs := congrArg Matrix.trace (su2_add_conjTranspose g)
  rw [Matrix.trace_add, Matrix.trace_conjTranspose, Matrix.trace_smul, Matrix.trace_one] at hs
  have hcard : (Fintype.card (Fin 2) : ℂ) = 2 := by simp
  rw [hcard, smul_eq_mul] at hs
  have hstar : star (Matrix.trace (g : M2)) = Matrix.trace (g : M2) := by linear_combination hs
  have him : (Matrix.trace (g : M2)).im = 0 := by
    have := Complex.conj_eq_iff_im.mp hstar
    exact this
  have hre := cos_su2Angle g
  apply Complex.ext
  · rw [Complex.ofReal_re, hre]; ring
  · rw [him, Complex.ofReal_im]

/-- Cayley–Hamilton at `det = 1`, obtained from unitarity: `g² = (2 cos θ)·g − 1`. -/
theorem su2_sq (g : SU2) :
    (g : M2) * (g : M2) = ((2 * Real.cos (su2Angle g) : ℝ) : ℂ) • (g : M2) - 1 := by
  have hgH : (g : M2)ᴴ = ((2 * Real.cos (su2Angle g) : ℝ) : ℂ) • (1 : M2) - (g : M2) := by
    have h := su2_add_conjTranspose g
    rw [su2_trace_eq g] at h
    rw [← h]; abel
  have hu : (g : M2) * (g : M2)ᴴ = 1 := mul_star_self g
  rw [hgH, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at hu
  rw [← hu]; abel

/-- `Y = g − (cos θ)·1`, the traceless part of `g`. -/
noncomputable def Yof (g : SU2) : M2 :=
  (g : M2) - ((Real.cos (su2Angle g) : ℝ) : ℂ) • (1 : M2)

theorem Y_sq (g : SU2) :
    Yof g * Yof g = ((-(Real.sin (su2Angle g)) ^ 2 : ℝ) : ℂ) • (1 : M2) := by
  set u : ℂ := ((Real.cos (su2Angle g) : ℝ) : ℂ) with hu
  have hsq := su2_sq g
  have ht : ((2 * Real.cos (su2Angle g) : ℝ) : ℂ) = 2 * u := by
    rw [hu]; push_cast; ring
  rw [ht] at hsq
  have key : ((g : M2) - u • (1 : M2)) * ((g : M2) - u • (1 : M2))
      = (g : M2) * (g : M2) - (2 * u) • (g : M2) + (u * u) • (1 : M2) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
    module
  have hpy : Real.cos (su2Angle g) ^ 2 + Real.sin (su2Angle g) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  have hscal : ((-(Real.sin (su2Angle g)) ^ 2 : ℝ) : ℂ) = u * u - 1 := by
    rw [hu]
    have : ((Real.cos (su2Angle g) : ℝ) : ℂ) * ((Real.cos (su2Angle g) : ℝ) : ℂ)
        = ((Real.cos (su2Angle g) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    congr 1
    nlinarith [hpy]
  rw [Yof, ← hu, key, hsq, hscal]
  module

/-- `su2Log g = κ · Y`. -/
theorem su2Log_eq_kappa_smul (g : SU2) :
    su2Log g = ((su2Kappa g : ℝ) : ℂ) • Yof g := by
  have hgH : (g : M2)ᴴ = ((2 * Real.cos (su2Angle g) : ℝ) : ℂ) • (1 : M2) - (g : M2) := by
    have h := su2_add_conjTranspose g
    rw [su2_trace_eq g] at h
    rw [← h]; abel
  have h2 : ((2 * Real.cos (su2Angle g) : ℝ) : ℂ) • (1 : M2)
      = (2 : ℂ) • (((Real.cos (su2Angle g) : ℝ) : ℂ) • (1 : M2)) := by
    rw [smul_smul]; congr 1; push_cast; ring
  rw [su2Log, hgH, Yof, h2]
  module

/-- **`X² = −θ²·1` for `X = su2Log g`.** -/
theorem su2Log_sq (g : SU2) (h1 : g ≠ 1) (h2 : g ≠ su2NegOne) :
    su2Log g * su2Log g = ((-(su2Angle g) ^ 2 : ℝ) : ℂ) • (1 : M2) := by
  have hsin : Real.sin (su2Angle g) ≠ 0 := sin_su2Angle_ne_zero g h1 h2
  have hk : su2Kappa g * Real.sin (su2Angle g) = su2Angle g := by
    rw [su2Kappa]; field_simp
  rw [su2Log_eq_kappa_smul g, Matrix.smul_mul, Matrix.mul_smul, Y_sq g, smul_smul, smul_smul]
  congr 1
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  linear_combination (-(su2Angle g) - su2Kappa g * Real.sin (su2Angle g)) * hk

/-! ## The exponential step -/

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem real_smul_eq (r : ℝ) (A : M2) : ((r : ℝ) : ℂ) • A = r • A := by
  rw [← Complex.coe_algebraMap, algebraMap_smul]

/-- **THE BRANCH LEMMA.** `su2Exp ∘ su2Log = id` on ALL of `SU(2)` except the single antipode
`−1`. This closes the only hypothesis of the narrowness theorem that was not part of the
comparison itself. -/
theorem su2_exp_log_of_ne_negOne (g : SU2) (h2 : g ≠ su2NegOne) : su2Exp (su2Log g) = g := by
  by_cases h1 : g = 1
  · subst h1; rw [su2Log_one, su2Exp_zero]
  have hsin : Real.sin (su2Angle g) ≠ 0 := sin_su2Angle_ne_zero g h1 h2
  have hθ0 : su2Angle g ≠ 0 := fun h => hsin (by rw [h, Real.sin_zero])
  set θ : ℝ := su2Angle g with hθ
  set J : M2 := (θ⁻¹ : ℝ) • su2Log g with hJdef
  have hJ : J * J = -1 := by
    rw [hJdef, smul_mul_assoc, mul_smul_comm, su2Log_sq g h1 h2, real_smul_eq, smul_smul,
      smul_smul]
    have hval : θ⁻¹ * θ⁻¹ * -su2Angle g ^ 2 = -1 := by rw [← hθ]; field_simp
    rw [hval, neg_one_smul]
  set φ : ℂ →ₐ[ℝ] M2 := Complex.liftAux J hJ with hφ
  have hcont : Continuous ((φ : ℂ →ₐ[ℝ] M2) : ℂ → M2) := by
    have hc2 : Continuous ((φ : ℂ →ₐ[ℝ] M2).toLinearMap : ℂ → M2) :=
      LinearMap.continuous_of_finiteDimensional _
    exact hc2
  have hφθ : φ ((θ : ℂ) * Complex.I) = su2Log g := by
    rw [hφ, Complex.liftAux_apply]
    have hre : ((θ : ℂ) * Complex.I).re = 0 := by simp
    have him : ((θ : ℂ) * Complex.I).im = θ := by simp
    rw [hre, him, map_zero, zero_add, hJdef, smul_smul]
    rw [mul_inv_cancel₀ hθ0, one_smul]
  have hexp : NormedSpace.exp (su2Log g) = φ (Complex.exp ((θ : ℂ) * Complex.I)) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.map_exp φ hcont, hφθ]
    rfl
  have hkap : Real.sin θ * θ⁻¹ * su2Kappa g = 1 := by
    rw [su2Kappa, ← hθ]; field_simp
  have hval : φ (Complex.exp ((θ : ℂ) * Complex.I)) = (g : M2) := by
    rw [hφ, Complex.exp_mul_I, Complex.liftAux_apply]
    have hre : (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I).re = Real.cos θ := by
      simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
        Complex.sin_ofReal_im]
    have him : (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I).im = Real.sin θ := by
      simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
        Complex.sin_ofReal_im]
    rw [hre, him, Algebra.algebraMap_eq_smul_one, hJdef, su2Log_eq_kappa_smul g, real_smul_eq,
      smul_smul, smul_smul, hkap, one_smul, Yof, ← hθ, real_smul_eq]
    abel
  have hmem : NormedSpace.exp (su2Log g) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [hexp, hval]; exact SetLike.coe_mem g
  apply Subtype.ext
  rw [su2Exp_of_mem hmem, hexp, hval]

/-- **`GaugeRegular`'s threshold discharges the branch condition.** `‖(−1) − 1‖_F = 2√2`, so any
`g` strictly closer than `2√2` to `1` is on the principal branch. -/
theorem frobNorm_negOne_sub_one : frobNorm ((su2NegOne : M2) - 1) = 2 * Real.sqrt 2 := by
  have hc : ((su2NegOne : SU2) : M2) - 1 = (((-2 : ℝ)) : ℂ) • (1 : M2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [su2NegOne, Matrix.one_apply] <;> norm_num
  have h1 : frobNorm (1 : M2) = Real.sqrt 2 := by
    rw [frobNorm]
    congr 1
    unfold AdalyFormal.Balaban.RMapLipschitz.frobSq
    norm_num [Matrix.one_apply]
  rw [hc, frobNorm_real_smul, h1]
  norm_num

theorem su2_exp_log_of_frobNorm_lt (g : SU2)
    (h : frobNorm ((g : M2) - 1) < 2 * Real.sqrt 2) : su2Exp (su2Log g) = g := by
  refine su2_exp_log_of_ne_negOne g ?_
  intro hg
  rw [hg, frobNorm_negOne_sub_one] at h
  exact lt_irrefl _ h

end Branch

/-! ## §1 — the chart field `A` and its two lattice derivatives -/

/-- The bond obtained from `b` by translating its base site one step in direction `ν`.
Same shift used by `AlphaAnalyticity.gaugeGradSupBond`. -/
def shiftBond (b : Bond L) (ν : Fin 3) : Bond L := (periodicLatticeShift b.1 ν, b.2)

/-- **`A(b) = η⁻¹ · (1/i) log V(b)`** — the source's chart field of a configuration `V`,
on the principal branch. Valid as *the* chart exactly where `su2Exp (su2Log (V b)) = V b`. -/
noncomputable def chartA (η : ℝ) (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) : M2 :=
  ((η⁻¹ : ℝ) : ℂ) • su2Log (V b)

/-- **`∇^η_ν A (b) = η⁻¹ (A(b+ην) − A(b))`** — the finite difference of (3.35)'s second clause. -/
noncomputable def gradA (η : ℝ) (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) (ν : Fin 3) :
    M2 :=
  ((η⁻¹ : ℝ) : ℂ) • (chartA η V (shiftBond b ν) - chartA η V b)

/-- **`∂^{η*}∂^η_ν A (b) = η⁻² (A(b+2ην) − 2A(b+ην) + A(b))`** — (3.36)'s second difference,
written in the forward form (it is the centered second difference based at `b + ην`). -/
noncomputable def coordLapA (η : ℝ) (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) (ν : Fin 3) :
    M2 :=
  (((η ^ 2)⁻¹ : ℝ) : ℂ) •
    (chartA η V (shiftBond (shiftBond b ν) ν) - ((2 : ℝ) : ℂ) • chartA η V (shiftBond b ν)
      + chartA η V b)

/-! ### §1a — DENOTATION PIN: `chartA` versus the source's `A`

`SuTwoLogExpCore.su2Log`'s docstring calls itself "`(1/i) log`", but `su2Log_antiHermitian`
proves `(su2Log g)ᴴ = −su2Log g` and `su2_exp_log_of_ne_negOne` (§0b) proves
`su2Exp (su2Log g) = g` with `su2Exp = NormedSpace.exp`. So `su2Log` is the ORDINARY
(anti-Hermitian) matrix logarithm, and the source's chart `U^u = e^{iηA}` gives
`A = (iη)⁻¹ · su2Log (U^u) = −i·η⁻¹·su2Log (U^u)`, i.e. `chartA = i·A`.

`srcA` below IS the source's `A`. `frobNorm` does not see the phase, so every bound proved on
`chartA` is literally a bound on `|A|`; and `chart_equation` shows the chart conjunct of
`CoordProxy3536` really is `U^u = e^{iηA}` for that `A`. -/

/-- **The source's own `A`**: `U^u = e^{iηA}` ⟺ `A = (iη)⁻¹ · log (U^u)`. -/
noncomputable def srcA (η : ℝ) (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) : M2 :=
  ((η⁻¹ : ℝ) : ℂ) • ((-Complex.I) • su2Log (V b))

theorem frobNorm_I_smul (M : M2) : frobNorm (Complex.I • M) = frobNorm M := by
  rw [frobNorm, frobNorm]
  congr 1
  unfold AdalyFormal.Balaban.RMapLipschitz.frobSq
  simp [Matrix.smul_apply, Complex.normSq_mul]

theorem frobNorm_negI_smul (M : M2) : frobNorm ((-Complex.I) • M) = frobNorm M := by
  rw [frobNorm, frobNorm]
  congr 1
  unfold AdalyFormal.Balaban.RMapLipschitz.frobSq
  simp [Matrix.smul_apply, Complex.normSq_mul]

/-- **The bounds this file proves on `chartA` ARE bounds on the source's `A`.** -/
theorem frobNorm_chartA_eq_srcA (η : ℝ) (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) :
    frobNorm (chartA η V b) = frobNorm (srcA η V b) := by
  rw [chartA, srcA, frobNorm_real_smul, frobNorm_real_smul, frobNorm_negI_smul]

/-- **The chart conjunct of `CoordProxy3536` IS `U^u = e^{iηA}` for the source's `A`.** -/
theorem chart_equation (η : ℝ) (hη : η ≠ 0) (V : PeriodicLinkConfiguration SU2 L) (b : Bond L)
    (h : su2Exp (su2Log (V b)) = V b) :
    V b = su2Exp (Complex.I • (((η : ℝ) : ℂ) • srcA η V b)) := by
  have hkey : Complex.I • (((η : ℝ) : ℂ) • srcA η V b) = su2Log (V b) := by
    rw [srcA, smul_smul, smul_smul, smul_smul]
    have hII : Complex.I * (-Complex.I) = 1 := by
      rw [mul_neg, Complex.I_mul_I, neg_neg]
    have hηη : ((η : ℝ) : ℂ) * ((η⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hη, Complex.ofReal_one]
    have hprod : Complex.I * ((η : ℝ) : ℂ) * ((η⁻¹ : ℝ) : ℂ) * (-Complex.I) = 1 := by
      calc Complex.I * ((η : ℝ) : ℂ) * ((η⁻¹ : ℝ) : ℂ) * (-Complex.I)
          = (((η : ℝ) : ℂ) * ((η⁻¹ : ℝ) : ℂ)) * (Complex.I * (-Complex.I)) := by ring
        _ = 1 := by rw [hηη, hII]; ring
    rw [hprod, one_smul]
  rw [hkey, h]

/-! ## §2 — CMP99b (3.35) ∧ (3.36), with all four source parameters explicit

`c` is the source's product `O(1)Mα₀` (the source pins `O(1) ≥ 10` and requires `O(1)Mα₀`
"sufficiently small"; it never gives it a number). `Lj` is `L^j`, the cube's scale factor.
`η` is the lattice spacing. `cube` is `□`. -/

/-- **CMP99b (3.35) ∧ (3.36) on the cube `cube`, at spacing `η` and cube index scale `Lj`,
with `c = O(1)Mα₀`.** Four conjuncts: the per-cube gauge `u` (here `γ`), the chart equation
`U^u = e^{iηA}`, and the three bounds. -/
def CoordProxy3536 (η Lj c : ℝ) (cube : Finset (Bond L))
    (U : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∃ γ : PeriodicLatticeSite L → SU2,
    (∀ b ∈ cube, su2Exp (su2Log (periodicGaugeTransform γ U b))
        = periodicGaugeTransform γ U b) ∧
    (∀ b ∈ cube, frobNorm (chartA η (periodicGaugeTransform γ U) b) < c * (Lj * η)⁻¹) ∧
    (∀ b ∈ cube, ∀ ν, frobNorm (gradA η (periodicGaugeTransform γ U) b ν)
        < c * ((Lj * η) ^ 2)⁻¹) ∧
    (∀ b ∈ cube, ∀ ν, frobNorm (coordLapA η (periodicGaugeTransform γ U) b ν)
        < c * ((Lj * η) ^ 3)⁻¹)

/-- **The same predicate with `η` eliminated.** Every clause is a bound on `su2Log` alone. -/
def CoordProxy3536Log (Lj c : ℝ) (cube : Finset (Bond L))
    (U : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∃ γ : PeriodicLatticeSite L → SU2,
    (∀ b ∈ cube, su2Exp (su2Log (periodicGaugeTransform γ U b))
        = periodicGaugeTransform γ U b) ∧
    (∀ b ∈ cube, frobNorm (su2Log (periodicGaugeTransform γ U b)) < c * Lj⁻¹) ∧
    (∀ b ∈ cube, ∀ ν, frobNorm (su2Log (periodicGaugeTransform γ U (shiftBond b ν))
        - su2Log (periodicGaugeTransform γ U b)) < c * (Lj ^ 2)⁻¹) ∧
    (∀ b ∈ cube, ∀ ν, frobNorm (su2Log (periodicGaugeTransform γ U
          (shiftBond (shiftBond b ν) ν))
        - ((2 : ℝ) : ℂ) • su2Log (periodicGaugeTransform γ U (shiftBond b ν))
        + su2Log (periodicGaugeTransform γ U b)) < c * (Lj ^ 3)⁻¹)

/-! ### §2a — THE `η`-CANCELLATION -/

private theorem chartA_norm (η : ℝ) (hη : 0 < η) (V : PeriodicLinkConfiguration SU2 L)
    (b : Bond L) : frobNorm (chartA η V b) = η⁻¹ * frobNorm (su2Log (V b)) := by
  rw [chartA, frobNorm_real_smul, abs_of_nonneg (le_of_lt (inv_pos.mpr hη))]

private theorem gradA_norm (η : ℝ) (hη : 0 < η) (V : PeriodicLinkConfiguration SU2 L)
    (b : Bond L) (ν : Fin 3) :
    frobNorm (gradA η V b ν)
      = (η⁻¹) ^ 2 * frobNorm (su2Log (V (shiftBond b ν)) - su2Log (V b)) := by
  have hsub : chartA η V (shiftBond b ν) - chartA η V b
      = ((η⁻¹ : ℝ) : ℂ) • (su2Log (V (shiftBond b ν)) - su2Log (V b)) := by
    rw [chartA, chartA, smul_sub]
  rw [gradA, hsub, ← smul_assoc, smul_eq_mul, ← Complex.ofReal_mul, frobNorm_real_smul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ η⁻¹ * η⁻¹)]
  ring

private theorem coordLapA_norm (η : ℝ) (hη : 0 < η) (V : PeriodicLinkConfiguration SU2 L)
    (b : Bond L) (ν : Fin 3) :
    frobNorm (coordLapA η V b ν)
      = (η⁻¹) ^ 3 * frobNorm (su2Log (V (shiftBond (shiftBond b ν) ν))
          - ((2 : ℝ) : ℂ) • su2Log (V (shiftBond b ν)) + su2Log (V b)) := by
  have hsub : chartA η V (shiftBond (shiftBond b ν) ν)
        - ((2 : ℝ) : ℂ) • chartA η V (shiftBond b ν) + chartA η V b
      = ((η⁻¹ : ℝ) : ℂ) • (su2Log (V (shiftBond (shiftBond b ν) ν))
          - ((2 : ℝ) : ℂ) • su2Log (V (shiftBond b ν)) + su2Log (V b)) := by
    rw [chartA, chartA, chartA, smul_add, smul_sub, smul_comm]
  have h2 : (((η ^ 2)⁻¹ : ℝ) : ℂ) * ((η⁻¹ : ℝ) : ℂ) = (((η⁻¹) ^ 3 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [coordLapA, hsub, ← smul_assoc, smul_eq_mul, h2, frobNorm_real_smul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (η⁻¹) ^ 3)]

/-- **THE `η`-CANCELLATION THEOREM.** For every positive lattice spacing `η`, CMP99b
(3.35)∧(3.36) is EQUIVALENT to a predicate in which `η` does not occur.

This is the first substantive finding of the lane: the comparison of the source's regularity
class with `GaugeRegular` does NOT depend on the lattice spacing. `η` enters the source's
three bounds through `(L^jη)⁻¹, (L^jη)⁻², (L^jη)⁻³` and enters `A, ∇^ηA, ∂^{η*}∂^ηA` through
exactly the matching powers `η⁻¹, η⁻², η⁻³`, and the two cancel clause by clause. -/
theorem coordProxy3536_eta_free (η Lj c : ℝ) (hη : 0 < η) (cube : Finset (Bond L))
    (U : PeriodicLinkConfiguration SU2 L) :
    CoordProxy3536 η Lj c cube U ↔ CoordProxy3536Log Lj c cube U := by
  have hpos : (0:ℝ) < η⁻¹ := inv_pos.mpr hη
  have key1 : ∀ (V : PeriodicLinkConfiguration SU2 L) (b : Bond L),
      (frobNorm (chartA η V b) < c * (Lj * η)⁻¹ ↔ frobNorm (su2Log (V b)) < c * Lj⁻¹) := by
    intro V b
    rw [chartA_norm η hη V b, mul_inv, ← mul_assoc]
    constructor
    · intro h; nlinarith [h]
    · intro h; nlinarith [h]
  have key2 : ∀ (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) (ν : Fin 3),
      (frobNorm (gradA η V b ν) < c * ((Lj * η) ^ 2)⁻¹ ↔
        frobNorm (su2Log (V (shiftBond b ν)) - su2Log (V b)) < c * (Lj ^ 2)⁻¹) := by
    intro V b ν
    rw [gradA_norm η hη V b ν]
    have he : ((Lj * η) ^ 2)⁻¹ = (Lj ^ 2)⁻¹ * (η⁻¹) ^ 2 := by
      rw [mul_pow, mul_inv, inv_pow]
    rw [he, ← mul_assoc]
    have hp : (0:ℝ) < (η⁻¹) ^ 2 := by positivity
    constructor
    · intro h; nlinarith [h]
    · intro h; nlinarith [h]
  have key3 : ∀ (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) (ν : Fin 3),
      (frobNorm (coordLapA η V b ν) < c * ((Lj * η) ^ 3)⁻¹ ↔
        frobNorm (su2Log (V (shiftBond (shiftBond b ν) ν))
          - ((2 : ℝ) : ℂ) • su2Log (V (shiftBond b ν)) + su2Log (V b)) < c * (Lj ^ 3)⁻¹) := by
    intro V b ν
    rw [coordLapA_norm η hη V b ν]
    have he : ((Lj * η) ^ 3)⁻¹ = (Lj ^ 3)⁻¹ * (η⁻¹) ^ 3 := by
      rw [mul_pow, mul_inv, inv_pow]
    rw [he, ← mul_assoc]
    have hp : (0:ℝ) < (η⁻¹) ^ 3 := by positivity
    constructor
    · intro h; nlinarith [h]
    · intro h; nlinarith [h]
  constructor
  · rintro ⟨γ, hch, h1, h2, h3⟩
    exact ⟨γ, hch, fun b hb => (key1 _ b).mp (h1 b hb),
      fun b hb ν => (key2 _ b ν).mp (h2 b hb ν), fun b hb ν => (key3 _ b ν).mp (h3 b hb ν)⟩
  · rintro ⟨γ, hch, h1, h2, h3⟩
    exact ⟨γ, hch, fun b hb => (key1 _ b).mpr (h1 b hb),
      fun b hb ν => (key2 _ b ν).mpr (h2 b hb ν), fun b hb ν => (key3 _ b ν).mpr (h3 b hb ν)⟩

/-! ## §3 — THE GAUGE-INVARIANT CURVATURE FLOOR

`GaugeRegular` says the bonds can be made small in SOME gauge. The plaquette holonomy is
gauge-covariant (`NonFlatBackground.holonomyElem_periodicGaugeTransform`) and `frobNorm (· − 1)`
is conjugation-invariant (`BlockingLinkEstimate.frobNorm_conj_sub_one`), so a curved `U` has a
FLOOR under the bond sup that no gauge can beat. This is what makes the wideness direction
provable without knowing which gauge an adversary picks. -/

/-- The plaquette holonomy is a four-factor word, so it is within `4·sup_b ‖V b − 1‖` of `1`. -/
theorem frobNorm_holonomy_le_four (V : PeriodicLinkConfiguration SU2 L)
    (p : PeriodicLatticePlaquette L) :
    frobNorm ((holonomyElem V p : M2) - 1) ≤ 4 * frobSupBond V := by
  set a := V (p.1, p.2.1.1) with ha
  set b := V (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) with hb
  set cc := V (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) with hc
  set d := V (p.1, p.2.1.2) with hd
  have hH : holonomyElem V p = a * b * cc⁻¹ * d⁻¹ := rfl
  have h1 := frobNorm_su_mul_sub_one_le (a * b * cc⁻¹) d⁻¹
  have h2 := frobNorm_su_mul_sub_one_le (a * b) cc⁻¹
  have h3 := frobNorm_su_mul_sub_one_le a b
  have hia : frobNorm ((cc⁻¹ : SU2) : M2) = 0 → True := fun _ => trivial
  rw [frobNorm_su_inv_sub_one cc] at h2
  rw [frobNorm_su_inv_sub_one d] at h1
  have ba := frobNorm_le_frobSupBond V (p.1, p.2.1.1)
  have bb := frobNorm_le_frobSupBond V (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
  have bc := frobNorm_le_frobSupBond V (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)
  have bd := frobNorm_le_frobSupBond V (p.1, p.2.1.2)
  rw [hH]
  linarith

/-- `frobNorm (U(∂p) − 1)` is GAUGE-INVARIANT. -/
theorem holonomy_frob_gauge_inv (U : PeriodicLinkConfiguration SU2 L)
    (γ : PeriodicLatticeSite L → SU2) (p : PeriodicLatticePlaquette L) :
    frobNorm ((holonomyElem (periodicGaugeTransform γ U) p : M2) - 1)
      = frobNorm ((holonomyElem U p : M2) - 1) := by
  rw [holonomyElem_periodicGaugeTransform, frobNorm_conj_sub_one]

/-- **THE CURVATURE FLOOR.** No gauge can push the bond sup below a quarter of the plaquette
curvature. -/
theorem curvature_floor (U : PeriodicLinkConfiguration SU2 L)
    (γ : PeriodicLatticeSite L → SU2) (p : PeriodicLatticePlaquette L) :
    frobNorm ((holonomyElem U p : M2) - 1) ≤ 4 * frobSupBond (periodicGaugeTransform γ U) := by
  rw [← holonomy_frob_gauge_inv U γ p]
  exact frobNorm_holonomy_le_four _ p

/-! ## §4 — WIDENESS: a `GaugeRegular` configuration OUTSIDE the source's class -/

/-- The chart equation excludes the branch point: if `exp (log g) = g` then `g ≠ −1`. -/
theorem ne_negOne_of_chart {g : SU2} (h : su2Exp (su2Log g) = g) : g ≠ su2NegOne := by
  intro hg
  rw [hg, su2Log_center, su2Exp_zero] at h
  exact su2NegOne_ne_one h.symm

/-- **(3.35)'s first clause, read back on the group.** On the cube, the chart equation plus the
`|A|` bound force the GROUP elements to be within `c·Lj⁻¹` of `1` — in the gauge the source's
existential produced. `η` has already cancelled. -/
theorem frobSupBond_lt_of_coordProxy3536Log {Lj c : ℝ} {U : PeriodicLinkConfiguration SU2 L}
    (h : CoordProxy3536Log Lj c (Finset.univ : Finset (Bond L)) U) :
    ∃ γ : PeriodicLatticeSite L → SU2,
      frobSupBond (periodicGaugeTransform γ U) < c * Lj⁻¹ := by
  obtain ⟨γ, hch, h1, -, -⟩ := h
  refine ⟨γ, ?_⟩
  rw [frobSupBond, Finset.sup'_lt_iff]
  intro b _
  have hne := ne_negOne_of_chart (hch b (Finset.mem_univ b))
  exact lt_of_le_of_lt (frobNorm_sub_one_le_frobNorm_su2Log _ hne) (h1 b (Finset.mem_univ b))

/-- **WIDENESS, generic form.** A configuration whose curvature at ONE plaquette is at least
`4·c·Lj⁻¹` is outside CMP99b's class — in every gauge, for every chart. -/
theorem not_coordProxy3536Log_of_curvature {Lj c : ℝ} {U : PeriodicLinkConfiguration SU2 L}
    (p : PeriodicLatticePlaquette L)
    (hbig : 4 * (c * Lj⁻¹) ≤ frobNorm ((holonomyElem U p : M2) - 1)) :
    ¬ CoordProxy3536Log Lj c (Finset.univ : Finset (Bond L)) U := by
  intro h
  obtain ⟨γ, hlt⟩ := frobSupBond_lt_of_coordProxy3536Log h
  have := curvature_floor U γ p
  linarith

/-! ### §4a — the explicit witness: ONE excited bond -/

open Classical in
/-- `U(b) = g` on the single bond `b₀`, `1` elsewhere. -/
noncomputable def oneBondU (b₀ : Bond L) (g : SU2) : PeriodicLinkConfiguration SU2 L :=
  fun b => if b = b₀ then g else 1

theorem oneBondU_apply_of_ne {b₀ b : Bond L} {g : SU2} (h : b ≠ b₀) :
    oneBondU b₀ g b = 1 := by
  classical
  simp only [oneBondU, if_neg h]

theorem oneBondU_self {b₀ : Bond L} {g : SU2} : oneBondU b₀ g b₀ = g := by
  classical
  simp only [oneBondU]
  simp

theorem frobSupBond_oneBondU (b₀ : Bond L) (g : SU2) :
    frobSupBond (oneBondU b₀ g) ≤ frobNorm ((g : M2) - 1) := by
  classical
  rw [frobSupBond]
  refine Finset.sup'_le _ _ ?_
  intro b _
  by_cases hb : b = b₀
  · subst hb; rw [oneBondU_self]
  · rw [oneBondU_apply_of_ne hb, OneMemClass.coe_one, sub_self, frobNorm_zero]
    exact frobNorm_nonneg _

/-- The excited bond sits on the plaquette `p` in the `μ` direction, and the other three bonds
of `p` are untouched, so the plaquette holonomy IS `g`. -/
theorem holonomy_oneBondU (p : PeriodicLatticePlaquette L) (g : SU2)
    (hshift : periodicLatticeShift p.1 p.2.1.2 ≠ p.1) :
    holonomyElem (oneBondU (p.1, p.2.1.1) g) p = g := by
  classical
  have hμν : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  have e1 : ((periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : Bond L) ≠ (p.1, p.2.1.1) := by
    intro hc; exact hμν (congrArg Prod.snd hc).symm
  have e2 : ((periodicLatticeShift p.1 p.2.1.2, p.2.1.1) : Bond L) ≠ (p.1, p.2.1.1) := by
    intro hc; exact hshift (congrArg Prod.fst hc)
  have e3 : ((p.1, p.2.1.2) : Bond L) ≠ (p.1, p.2.1.1) := by
    intro hc; exact hμν (congrArg Prod.snd hc).symm
  show oneBondU (p.1, p.2.1.1) g (p.1, p.2.1.1)
      * oneBondU (p.1, p.2.1.1) g (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      * (oneBondU (p.1, p.2.1.1) g (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹
      * (oneBondU (p.1, p.2.1.1) g (p.1, p.2.1.2))⁻¹ = g
  rw [oneBondU_self, oneBondU_apply_of_ne e1, oneBondU_apply_of_ne e2,
    oneBondU_apply_of_ne e3]
  group

/-- **THE WIDENESS WITNESS.** For every `g ∈ SU(2)` and every plaquette `p` with a genuine
second direction, `oneBondU g` is `GaugeRegular` at `α = ‖g − 1‖_F` and is OUTSIDE
CMP99b (3.35)∧(3.36) as soon as `4·c·Lj⁻¹ ≤ ‖g − 1‖_F`.

So `GaugeRegular α ⊄ (3.35)∧(3.36)` whenever `4·c·Lj⁻¹ ≤ α ≤ 2√2`. -/
theorem proxyWideness_witness (Lj c α : ℝ) (p : PeriodicLatticePlaquette L) (g : SU2)
    (hshift : periodicLatticeShift p.1 p.2.1.2 ≠ p.1)
    (hle : frobNorm ((g : M2) - 1) ≤ α)
    (hbig : 4 * (c * Lj⁻¹) ≤ frobNorm ((g : M2) - 1)) :
    GaugeRegular α (oneBondU (p.1, p.2.1.1) g) ∧
      ¬ CoordProxy3536Log Lj c (Finset.univ : Finset (Bond L)) (oneBondU (p.1, p.2.1.1) g) := by
  constructor
  · exact gaugeRegular_of_frobSupBond_le
      (le_trans (frobSupBond_oneBondU (p.1, p.2.1.1) g) hle)
  · refine not_coordProxy3536Log_of_curvature p ?_
    rw [holonomy_oneBondU p g hshift]
    exact hbig

/-! ## §5 — THE OTHER DIRECTION: the source's class is NOT inside `GaugeRegular`

The source's own sentence: *"these regularity conditions do not impose any constraints on `U`
outside the domain `Ω₀`."* Formalized: a cube on which `U ≡ 1` satisfies (3.35)∧(3.36) at every
positive `c`, while a single excited bond OUTSIDE that cube destroys `GaugeRegular`.

The cube is NONEMPTY (a genuine bond), and every bond the three clauses look at from it —
`b₁`, `b₁ + ν`, `b₁ + 2ν` for all `ν` — carries the same DIRECTION component as `b₁`, so a
`b₀` of a different direction is never seen. -/

theorem proxyRegion_witness (Lj c α : ℝ) (hLj : 0 < Lj) (hc : 0 < c)
    (p : PeriodicLatticePlaquette L) (b₁ : Bond L) (g : SU2)
    (hshift : periodicLatticeShift p.1 p.2.1.2 ≠ p.1)
    (hdir : b₁.2 ≠ p.2.1.1)
    (hα : 4 * α < frobNorm ((g : M2) - 1)) :
    CoordProxy3536Log Lj c {b₁} (oneBondU (p.1, p.2.1.1) g) ∧
      ¬ GaugeRegular α (oneBondU (p.1, p.2.1.1) g) := by
  classical
  set b₀ : Bond L := (p.1, p.2.1.1) with hb₀
  set U := oneBondU b₀ g with hU
  have hone : ∀ b : Bond L, b.2 = b₁.2 → U b = 1 := by
    intro b hbd
    refine oneBondU_apply_of_ne ?_
    intro hc'
    exact hdir (hbd ▸ congrArg Prod.snd hc')
  have hshiftdir : ∀ (b : Bond L) (ν : Fin 3), (shiftBond b ν).2 = b.2 := fun _ _ => rfl
  constructor
  · refine ⟨fun _ => 1, ?_, ?_, ?_, ?_⟩
    · intro b hb
      rw [AdalyFormal.Balaban.AlphaAnalyticity.gaugeTransform_one]
      rw [Finset.mem_singleton] at hb
      subst hb
      rw [hone b rfl, su2Log_one, su2Exp_zero]
    · intro b hb
      rw [AdalyFormal.Balaban.AlphaAnalyticity.gaugeTransform_one]
      rw [Finset.mem_singleton] at hb
      subst hb
      rw [hone b rfl, su2Log_one, frobNorm_zero]
      positivity
    · intro b hb ν
      rw [AdalyFormal.Balaban.AlphaAnalyticity.gaugeTransform_one]
      rw [Finset.mem_singleton] at hb
      subst hb
      rw [hone _ (hshiftdir b ν), hone b rfl, su2Log_one, sub_self, frobNorm_zero]
      positivity
    · intro b hb ν
      rw [AdalyFormal.Balaban.AlphaAnalyticity.gaugeTransform_one]
      rw [Finset.mem_singleton] at hb
      subst hb
      rw [hone _ ((hshiftdir (shiftBond b ν) ν).trans (hshiftdir b ν)),
        hone _ (hshiftdir b ν), hone b rfl, su2Log_one]
      rw [smul_zero, sub_zero, add_zero, frobNorm_zero]
      positivity
  · rintro ⟨γ, hγ⟩
    have hfloor := curvature_floor U γ p
    rw [hU, hb₀, holonomy_oneBondU p g hshift] at hfloor
    linarith

/-! ## §6 — NARROWNESS: `GaugeRegular α` IS inside the source's class below an explicit threshold

The withdrawn claim in `CoercUMainDesigned` §2a said the containment "turns on a comparison of
thresholds that cannot even be stated in this tree", naming `η, L^j, M, α₀`. §2a's `η` is gone
(`coordProxy3536_eta_free`). What is left is the single inequality `2π·α < c·Lj⁻³` with
`c = O(1)Mα₀`.

The `2π` is composed, not tuned: `π/2` is CMP98 (25) (`frobNorm_su2Log_le_pi_div_two`), and the
factors `1, 2, 4` are the numbers of `log` terms in `A`, `∇^ηA`, `∂^{η*}∂^ηA` respectively —
`4·(π/2) = 2π` is the binding one, from (3.36). -/

/-- **NARROWNESS.** `hbranch` is the ONLY hypothesis not about the comparison itself: it says
group elements within `α` of `1` lie on the principal branch. See §7. -/
theorem coordProxy3536Log_of_gaugeRegular (Lj c α : ℝ) (U : PeriodicLinkConfiguration SU2 L)
    (hLj : 1 ≤ Lj) (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hthr : 2 * Real.pi * α < c * (Lj ^ 3)⁻¹)
    (hbranch : ∀ h : SU2, frobNorm ((h : M2) - 1) ≤ α → su2Exp (su2Log h) = h)
    (hreg : GaugeRegular α U) (cube : Finset (Bond L)) :
    CoordProxy3536Log Lj c cube U := by
  obtain ⟨γ, hsup⟩ := hreg
  set V := periodicGaugeTransform γ U with hV
  have hb : ∀ b : Bond L, frobNorm ((V b : M2) - 1) ≤ α := fun b =>
    le_trans (frobNorm_le_frobSupBond V b) hsup
  have hlog : ∀ b : Bond L, frobNorm (su2Log (V b)) ≤ Real.pi / 2 * α := by
    intro b
    refine le_trans (frobNorm_su2Log_le_pi_div_two (V b)) ?_
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    nlinarith [hb b, frobNorm_nonneg ((V b : M2) - 1)]
  -- the three thresholds, ordered by `Lj ≥ 1`
  have hLj0 : (0:ℝ) < Lj := lt_of_lt_of_le zero_lt_one hLj
  have h31 : c * (Lj ^ 3)⁻¹ ≤ c * Lj⁻¹ := by
    have hi : (Lj ^ 3)⁻¹ ≤ Lj⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hLj0
        (by nlinarith [mul_nonneg (mul_nonneg hLj0.le hLj0.le) (sub_nonneg.mpr hLj)])
    exact mul_le_mul_of_nonneg_left hi hc
  have h32 : c * (Lj ^ 3)⁻¹ ≤ c * (Lj ^ 2)⁻¹ := by
    have hi : (Lj ^ 3)⁻¹ ≤ (Lj ^ 2)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity)
        (by nlinarith [mul_nonneg (mul_nonneg hLj0.le hLj0.le) (sub_nonneg.mpr hLj)])
    exact mul_le_mul_of_nonneg_left hi hc
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · exact fun b _ => hbranch (V b) (hb b)
  · intro b _
    have := hlog b
    nlinarith [hthr, h31]
  · intro b _ ν
    have h1 := hlog (shiftBond b ν)
    have h2 := hlog b
    have := frobNorm_sub_le (su2Log (V (shiftBond b ν))) (su2Log (V b))
    nlinarith [hthr, h32]
  · intro b _ ν
    have hA := hlog (shiftBond (shiftBond b ν) ν)
    have hB := hlog (shiftBond b ν)
    have hC := hlog b
    have hsmul : frobNorm (((2:ℝ) : ℂ) • su2Log (V (shiftBond b ν)))
        = 2 * frobNorm (su2Log (V (shiftBond b ν))) := by
      rw [frobNorm_real_smul]; norm_num
    have t1 := frobNorm_sub_le (su2Log (V (shiftBond (shiftBond b ν) ν)))
      (((2:ℝ) : ℂ) • su2Log (V (shiftBond b ν)))
    have t2 := frobNorm_add_le
      (su2Log (V (shiftBond (shiftBond b ν) ν)) - ((2:ℝ) : ℂ) • su2Log (V (shiftBond b ν)))
      (su2Log (V b))
    rw [hsmul] at t1
    nlinarith [hthr]

/-- **NARROWNESS, UNCONDITIONAL.** The branch hypothesis is discharged by §0b: `α < 2√2` is
exactly "the class `GaugeRegular α` is a proper subclass" (every `SU(2)` element is within
`2√2 = ‖(−1) − 1‖_F` of `1`, so `GaugeRegular (2√2)` is EVERY configuration).

So: **if `2π·α < c·Lj⁻³` then `GaugeRegular α ⊆ (3.35)∧(3.36)`** — the benign direction, with a
stated, checkable side condition and no residual hypothesis. -/
theorem coordProxy3536Log_of_gaugeRegular_uncond (Lj c α : ℝ) (U : PeriodicLinkConfiguration SU2 L)
    (hLj : 1 ≤ Lj) (hα : 0 ≤ α) (hc : 0 ≤ c) (hα2 : α < 2 * Real.sqrt 2)
    (hthr : 2 * Real.pi * α < c * (Lj ^ 3)⁻¹)
    (hreg : GaugeRegular α U) (cube : Finset (Bond L)) :
    CoordProxy3536Log Lj c cube U :=
  coordProxy3536Log_of_gaugeRegular Lj c α U hLj hα hc hthr
    (fun h hh => su2_exp_log_of_frobNorm_lt h (lt_of_le_of_lt hh hα2)) hreg cube

/-! ## §9 — THE TWO SIDE CONDITIONS AT THE TREE'S OWN NUMBERS

`alphaEll ell = (1/100000)·(1/ell⁵)` (`GeneralEllAssembly.lean:479`), and the tree's cube is the
block of side `ell`, so `Lj = ell`. Both regime conditions are then pure-number comparisons
against the source's `c = O(1)Mα₀`, which CMP99b never gives a value (it says only
`O(1) ≥ 10` and "`O(1)Mα₀` sufficiently small"). -/

/-- The NARROW side condition at `α = 10⁻⁵·ell⁻⁵`, `Lj = ell`, in lowest terms. -/
theorem narrow_condition_at_alphaEll (e c : ℝ) (he : 0 < e) :
    (2 * Real.pi * ((1 / 100000) * (1 / e ^ 5)) < c * (e ^ 3)⁻¹) ↔
      (2 * Real.pi * (1 / 100000) < c * e ^ 2) := by
  have hne : e ≠ 0 := ne_of_gt he
  have key : 2 * Real.pi * ((1 / 100000) * (1 / e ^ 5))
      = (2 * Real.pi * (1 / 100000)) * (e ^ 5)⁻¹ := by field_simp
  have key2 : c * (e ^ 3)⁻¹ = (c * e ^ 2) * (e ^ 5)⁻¹ := by field_simp
  have hp : (0:ℝ) < (e ^ 5)⁻¹ := by positivity
  rw [key, key2]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact absurd h (not_lt.mpr (mul_le_mul_of_nonneg_right hcon (le_of_lt hp)))
  · intro h
    exact mul_lt_mul_of_pos_right h hp

/-- The WIDE side condition at `α = 10⁻⁵·ell⁻⁵`, `Lj = ell`, in lowest terms. -/
theorem wide_condition_at_alphaEll (e c a : ℝ) (he : 0 < e) :
    (4 * (c * e⁻¹) ≤ a ∧ a ≤ (1 / 100000) * (1 / e ^ 5)) →
      4 * c ≤ (1 / 100000) * (1 / e ^ 4) := by
  rintro ⟨h1, h2⟩
  have h5 : (0:ℝ) < e ^ 5 := by positivity
  have hcomb : 4 * (c * e⁻¹) ≤ (1 / 100000) * (1 / e ^ 5) := le_trans h1 h2
  have := mul_le_mul_of_nonneg_right hcomb (le_of_lt he)
  field_simp at this ⊢
  nlinarith [this, he, h5]

#print axioms frobNorm_neg
#print axioms frobNorm_sub_le
#print axioms real_smul_eq
#print axioms su2Log_eq_kappa_smul
#print axioms chartA_norm
#print axioms gradA_norm
#print axioms coordLapA_norm
#print axioms oneBondU_apply_of_ne
#print axioms oneBondU_self
#print axioms su2_add_conjTranspose
#print axioms su2_trace_eq
#print axioms su2_sq
#print axioms Y_sq
#print axioms su2Log_sq
#print axioms su2_exp_log_of_ne_negOne
#print axioms frobNorm_negOne_sub_one
#print axioms su2_exp_log_of_frobNorm_lt
#print axioms coordProxy3536Log_of_gaugeRegular_uncond
#print axioms narrow_condition_at_alphaEll
#print axioms wide_condition_at_alphaEll

/-- **WIDENESS IS UNAVOIDABLE AT LARGE CUBE SCALE, for EVERY positive `c = O(1)Mα₀`.**

The source's threshold on a cube of index `j` is `∝ Lj⁻¹` (and `Lj⁻³` for (3.36)); it SHRINKS as
the cube grows. `GaugeRegular`'s threshold `alphaEll ell` carries no cube index at all. So for
any fixed `c > 0` and any fixed nonflat `g`, every cube scale `Lj ≥ 4c/‖g−1‖_F` puts the witness
inside `GaugeRegular` and outside CMP99b's class. No smallness assumption on `c` is used. -/
theorem proxyWideness_at_large_cube (c Lj : ℝ) (p : PeriodicLatticePlaquette L) (g : SU2)
    (hshift : periodicLatticeShift p.1 p.2.1.2 ≠ p.1)
    (hg : 0 < frobNorm ((g : M2) - 1)) (hLj : 0 < Lj)
    (hbig : 4 * c / frobNorm ((g : M2) - 1) ≤ Lj) :
    GaugeRegular (frobNorm ((g : M2) - 1)) (oneBondU (p.1, p.2.1.1) g) ∧
      ¬ CoordProxy3536Log Lj c (Finset.univ : Finset (Bond L)) (oneBondU (p.1, p.2.1.1) g) := by
  refine proxyWideness_witness Lj c (frobNorm ((g : M2) - 1)) p g hshift le_rfl ?_
  rw [div_le_iff₀ hg] at hbig
  rw [mul_comm c Lj⁻¹, ← mul_assoc]
  rw [show (4 : ℝ) * Lj⁻¹ * c = (4 * c) / Lj by field_simp]
  rw [div_le_iff₀ hLj]
  linarith

#print axioms proxyWideness_at_large_cube

/-! ## §7 — THE DICHOTOMY, and the exact residual

Put §4 and §6 together. With `α` the tree's threshold and `c = O(1)Mα₀` the source's:

* `2π·α < c·Lj⁻³`  ⟹  `GaugeRegular α ⊆ (3.35)∧(3.36)`   (`coordProxy3536Log_of_gaugeRegular`)
* `4·c·Lj⁻¹ ≤ α`   ⟹  `GaugeRegular α ⊄ (3.35)∧(3.36)`, with a constructed witness
                                                          (`proxyWideness_witness`)
* and `(3.35)∧(3.36) ⊄ GaugeRegular` in BOTH regimes                (`proxyRegion_witness`)

so the classes are never equal, and which containment holds is decided by `α·Lj³/c`. -/

/-- **THE DICHOTOMY, in one statement.** Both regimes are realized; the source's own
constants decide which. -/
theorem proxyContainment_dichotomy (Lj c α : ℝ) (p : PeriodicLatticePlaquette L) (g : SU2)
    (hLj : 1 ≤ Lj) (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hshift : periodicLatticeShift p.1 p.2.1.2 ≠ p.1)
    (hbranch : ∀ h : SU2, frobNorm ((h : M2) - 1) ≤ α → su2Exp (su2Log h) = h) :
    (2 * Real.pi * α < c * (Lj ^ 3)⁻¹ →
        ∀ U : PeriodicLinkConfiguration SU2 L, GaugeRegular α U →
          CoordProxy3536Log Lj c (Finset.univ : Finset (Bond L)) U) ∧
    (frobNorm ((g : M2) - 1) ≤ α → 4 * (c * Lj⁻¹) ≤ frobNorm ((g : M2) - 1) →
        GaugeRegular α (oneBondU (p.1, p.2.1.1) g) ∧
        ¬ CoordProxy3536Log Lj c (Finset.univ : Finset (Bond L)) (oneBondU (p.1, p.2.1.1) g)) := by
  refine ⟨fun hthr U hreg =>
      coordProxy3536Log_of_gaugeRegular Lj c α U hLj hα hc hthr hbranch hreg _, ?_⟩
  intro hle hbig
  exact proxyWideness_witness Lj c α p g hshift hle hbig

/-! ## §8 — axiom audit -/

#print axioms frobNorm_I_smul
#print axioms frobNorm_negI_smul
#print axioms frobNorm_chartA_eq_srcA
#print axioms chart_equation
#print axioms coordProxy3536_eta_free
#print axioms frobNorm_holonomy_le_four
#print axioms holonomy_frob_gauge_inv
#print axioms curvature_floor
#print axioms ne_negOne_of_chart
#print axioms frobSupBond_lt_of_coordProxy3536Log
#print axioms not_coordProxy3536Log_of_curvature
#print axioms holonomy_oneBondU
#print axioms frobSupBond_oneBondU
#print axioms proxyWideness_witness
#print axioms proxyRegion_witness
#print axioms coordProxy3536Log_of_gaugeRegular
#print axioms proxyContainment_dichotomy

/-! ## §10 — THE WIDENESS WITNESS IS INHABITED (added 2026-07-30, `compute/regularity_propagate/`)

**NEW IN THIS LANE, not part of the landed file.** `proxyWideness_witness` and `proxyWideness_at_large_cube`
take the group element `g` as a HYPOTHESIS. Nothing above proves that the band
`[4·c·Lj⁻¹, α]` they require actually contains a realizable `‖g − 1‖_F` — so, read strictly, the
landed wideness statements were conditional on an unbuilt object. That is the
"do-not-take-`∃`-as-a-hypothesis" defect, and this section closes it rather than naming it:
`exists_su2_frobNorm_sub_one_eq` CONSTRUCTS the element, on the maximal torus, and
`exists_proxyWideness_witness` turns the whole wideness direction into an unconditional `∃ U`.

The construction reuses what the tree already had (LAW-19): `BlockingLinkEstimate`'s
`frobNorm_sub_one_eq` (`‖g − 1‖_F = 2√2·sin(θ(g)/2)`), `SuTwoLogExpTorus`'s `torus`/`su2Angle_torus`
and `AlphaAnalyticity`'s `shift_ne_self`. Nothing here is new machinery. -/

/-- **EVERY value in `[0, 2√2]` is realized as `‖g − 1‖_F` by an actual `g ∈ SU(2)`** — namely
`torus (2·arcsin (a/(2√2)))` on the maximal torus. `2√2 = ‖(−1) − 1‖_F` is the exact top of the
range (`frobNorm_negOne_sub_one`), so this is surjectivity onto the full range, not onto a
convenient sub-interval. -/
theorem exists_su2_frobNorm_sub_one_eq (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 2 * Real.sqrt 2) :
    ∃ g : SU2, frobNorm ((g : M2) - 1) = a := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (0 : ℝ) < 2 * Real.sqrt 2 := by linarith
  set x : ℝ := a / (2 * Real.sqrt 2) with hx
  have hx0 : 0 ≤ x := div_nonneg h0 (le_of_lt hden)
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hden]; exact h1
  have hxm1 : (-1 : ℝ) ≤ x := by linarith
  set t : ℝ := 2 * Real.arcsin x with ht
  have ht0 : 0 ≤ t := by
    rw [ht]; have := Real.arcsin_nonneg.mpr hx0; linarith
  have htpi : t ≤ Real.pi := by
    rw [ht]; have := Real.arcsin_le_pi_div_two x; linarith
  refine ⟨torus t, ?_⟩
  rw [frobNorm_sub_one_eq, su2Angle_torus ht0 htpi]
  have hhalf : t / 2 = Real.arcsin x := by rw [ht]; ring
  rw [hhalf, Real.sin_arcsin hxm1 hx1, hx]
  field_simp

/-- **WIDENESS AS AN UNCONDITIONAL EXISTENCE STATEMENT.** No `g` is assumed: for any threshold `α`
in the realizable range that clears the curvature floor `4·c·Lj⁻¹`, a configuration EXISTS which is
`GaugeRegular α` and which CMP99b (3.35)∧(3.36) rejects in every gauge.

The only lattice hypothesis is `1 ≤ L 1` — the direction-`1` extent must admit a genuine shift, or
there is no plaquette to carry curvature. That is the honest degenerate point, stated rather than
assumed away. -/
theorem exists_proxyWideness_witness (Lj c α : ℝ) (hL1 : 1 ≤ L 1) (hα0 : 0 ≤ α)
    (hα2 : α ≤ 2 * Real.sqrt 2) (hband : 4 * (c * Lj⁻¹) ≤ α) :
    ∃ U : PeriodicLinkConfiguration SU2 L,
      GaugeRegular α U ∧ ¬ CoordProxy3536Log Lj c (Finset.univ : Finset (Bond L)) U := by
  obtain ⟨g, hg⟩ := exists_su2_frobNorm_sub_one_eq α hα0 hα2
  refine ⟨oneBondU (((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) : Bond L) g, ?_⟩
  have hshift : periodicLatticeShift
      ((((fun _ => 0 : PeriodicLatticeSite L),
        (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) :
          PeriodicLatticePlaquette L).1)
      ((((fun _ => 0 : PeriodicLatticeSite L),
        (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) :
          PeriodicLatticePlaquette L).2.1.2)
      ≠ (((fun _ => 0 : PeriodicLatticeSite L),
        (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) :
          PeriodicLatticePlaquette L).1 :=
    AdalyFormal.Balaban.AlphaAnalyticity.shift_ne_self _ _ hL1
  exact proxyWideness_witness Lj c α
    (((fun _ => 0 : PeriodicLatticeSite L),
      (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) : PeriodicLatticePlaquette L)
    g hshift (le_of_eq hg) (hg ▸ hband)

/-- **THE WIDENESS REGIME IS INHABITED AT THE TREE'S OWN THRESHOLD.**
`α = 10⁻⁵·ell⁻⁵` (`GeneralEllAssembly.alphaEll`, transcribed as a literal here to avoid an import),
`Lj = ell`. The side condition is exactly `wide_condition_at_alphaEll`'s, now shown SUFFICIENT for a
witness to exist and not merely necessary for the band to be non-empty.

At `ell = 2` this reads `4c ≤ 1/1600000`, i.e. `c = O(1)Mα₀ ≤ 1.5625·10⁻⁷`. CMP99b never gives
`O(1)Mα₀` a value — it requires only that it be "sufficiently small" — and SMALLER `c` is exactly
this regime. -/
theorem exists_proxyWideness_witness_at_alphaEll (e c : ℝ) (he : 1 ≤ e) (hc : 0 ≤ c) (hL1 : 1 ≤ L 1)
    (hsmall : 4 * c ≤ (1 / 100000) * (1 / e ^ 4)) :
    ∃ U : PeriodicLinkConfiguration SU2 L,
      GaugeRegular ((1 / 100000) * (1 / e ^ 5)) U ∧
        ¬ CoordProxy3536Log e c (Finset.univ : Finset (Bond L)) U := by
  have he0 : (0 : ℝ) < e := lt_of_lt_of_le zero_lt_one he
  have h5 : (0 : ℝ) < e ^ 5 := by positivity
  have hα0 : (0 : ℝ) ≤ (1 / 100000) * (1 / e ^ 5) := by positivity
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hα2 : (1 / 100000) * (1 / e ^ 5) ≤ 2 * Real.sqrt 2 := by
    have he5 : (1 : ℝ) ≤ e ^ 5 := one_le_pow₀ he
    have : (1 / 100000) * (1 / e ^ 5) ≤ (1 / 100000 : ℝ) := by
      rw [mul_one_div, div_le_iff₀ h5]; nlinarith
    linarith
  refine exists_proxyWideness_witness e c _ hL1 hα0 hα2 ?_
  have h4 : (0 : ℝ) < e ^ 4 := by positivity
  rw [mul_comm c e⁻¹, ← mul_assoc, show (4 : ℝ) * e⁻¹ * c = (4 * c) / e by field_simp,
    div_le_iff₀ he0]
  have hkey : (1 / 100000) * (1 / e ^ 5) * e = (1 / 100000) * (1 / e ^ 4) := by
    field_simp
  rw [hkey]
  exact hsmall

#print axioms exists_su2_frobNorm_sub_one_eq
#print axioms exists_proxyWideness_witness
#print axioms exists_proxyWideness_witness_at_alphaEll

/-! ## §11 — THE BAND: how much of it is OUR SLACK (added 2026-07-30, `compute/regularity_propagate/`)

§7 leaves an undetermined band of `8π·(L^j)²` between the two thresholds. **It is not closable here,
and the reason is a statement about the wide side, not an absence of effort.** Closing it needs the
OPTIMAL `GaugeRegular α` configuration violating (3.35) — a minimization of the curvature-to-bond-sup
ratio over ALL configurations. The wide constant `4` does not come from such an optimum: it is the
four-bond count of one plaquette applied to ONE chosen witness (`oneBondU`), i.e. an upper bound on
what that witness achieves, and no theorem in reach says the witness is best possible. That is a
genuine open optimization, not a mechanical gap.

**What IS reachable is the narrow side, and it is improvable by exactly `√2`.** §6's `2π` is
`4 · (π/2)` and the `π/2` is `BlockingLinkEstimate.frobNorm_su2Log_le_pi_div_two`, which is SHARP
ONLY AT THE ANTIPODE: the exact ratio is `‖log g‖_F/‖g − 1‖_F = (θ/2)/sin(θ/2)`, equal to `1` in the
limit `θ → 0` and reaching `π/2` only at `θ = π`. `GaugeRegular α` confines `g` near `1`, so the
antipodal value is never the operative one. Below, at `θ ≤ π/2` (equivalently `‖g − 1‖_F ≤ 2`), the
constant is `π/(2√2) ≈ 1.1107`, the narrow threshold becomes `√2·π·α`, and the band shrinks from
`8π·(L^j)² ≈ 25.13·(L^j)²` to `4√2·π·(L^j)² ≈ 17.77·(L^j)²` — 71.1 instead of 100.5 at `ell = 2`.

**This does not move the answer and is not offered as if it did.** It measures how much of the band
is slack in OUR bound (a factor `√2`) versus how much is a real gap between the two phenomena (the
remaining `4√2π·(L^j)²`), which is the honest thing to know about a residual before anyone tries to
close it. -/

/-- **`sin x ≥ (2√2/π)·x` on `[0, π/4]`** — the Jordan inequality on the half-range, from concavity
of `sin`. Mathlib's `Real.mul_le_sin` supplies only the `[0, π/2]` constant `2/π ≈ 0.6366`; the
constant here is `2√2/π ≈ 0.9003`. -/
theorem sin_ge_of_le_pi_div_four {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 4) :
    (2 * Real.sqrt 2 / Real.pi) * x ≤ Real.sin x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  have ht0 : (0 : ℝ) ≤ 4 * x / Real.pi := by positivity
  have ht1 : 4 * x / Real.pi ≤ 1 := by rw [div_le_one hpi]; linarith
  have hconc := (strictConcaveOn_sin_Icc).concaveOn
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_refl _, le_of_lt hpi⟩
  have h4mem : Real.pi / 4 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by positivity, by linarith⟩
  have hkey := hconc.2 h0mem h4mem
    (by linarith : (0 : ℝ) ≤ 1 - 4 * x / Real.pi) ht0 (by ring)
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, Real.sin_zero,
    Real.sin_pi_div_four] at hkey
  have harg : (1 - 4 * x / Real.pi) * 0 + 4 * x / Real.pi * (Real.pi / 4) = x := by
    rw [mul_zero, zero_add]; field_simp; try ring
  rw [harg] at hkey
  have hlhs : (1 - 4 * x / Real.pi) * 0 + 4 * x / Real.pi * (Real.sqrt 2 / 2)
      = 2 * Real.sqrt 2 / Real.pi * x := by
    rw [mul_zero, zero_add]; field_simp; try ring
  linarith [hkey, hlhs.le, hlhs.ge]

/-- **THE SHARPENED CHART BOUND.** For `g` within `2` of `1` — equivalently, of rotation angle at
most `π/2` — `‖log g‖_F ≤ (π/(2√2))·‖g − 1‖_F`, a factor `√2` better than
`BlockingLinkEstimate.frobNorm_su2Log_le_pi_div_two`. Both are instances of `(θ/2)/sin(θ/2)`
evaluated at the top of the admitted angle range; the landed bound evaluates it at `θ = π`, this one
at `θ = π/2`. -/
theorem frobNorm_su2Log_le_sharp (g : SU2) (h : frobNorm ((g : M2) - 1) ≤ 2) :
    frobNorm (su2Log g) ≤ (Real.pi / (2 * Real.sqrt 2)) * frobNorm ((g : M2) - 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set θ : ℝ := su2Angle g with hθ
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθpi : θ ≤ Real.pi := Real.arccos_le_pi _
  have hval : frobNorm ((g : M2) - 1) = 2 * Real.sqrt 2 * Real.sin (θ / 2) :=
    frobNorm_sub_one_eq g
  -- the angle is at most `π/2`
  have hhalf0 : 0 ≤ θ / 2 := by linarith
  have hhalfpi2 : θ / 2 ≤ Real.pi / 2 := by linarith
  have hsinle : Real.sin (θ / 2) ≤ Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]
    rw [hval] at h
    nlinarith [h, hs2, hsq]
  have hqtr : θ / 2 ≤ Real.pi / 4 := by
    by_contra hcon
    push_neg at hcon
    have hm := Real.strictMonoOn_sin
      (show Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith, by linarith⟩)
      (show θ / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith, by linarith⟩) hcon
    linarith
  -- Jordan on the half-range
  have hjor := sin_ge_of_le_pi_div_four hhalf0 hqtr
  have hlog : frobNorm (su2Log g) ≤ Real.sqrt 2 * θ :=
    AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_su2Log_le g
  -- `‖g − 1‖ = 2√2·sin(θ/2) ≥ 2√2·(2√2/π)·(θ/2) = 4θ/π`
  have hlow : 4 / Real.pi * θ ≤ frobNorm ((g : M2) - 1) := by
    rw [hval]
    have := mul_le_mul_of_nonneg_left hjor (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 2)
    calc 4 / Real.pi * θ
        = 2 * Real.sqrt 2 * (2 * Real.sqrt 2 / Real.pi * (θ / 2)) := by
          field_simp; nlinarith [hsq]
      _ ≤ 2 * Real.sqrt 2 * Real.sin (θ / 2) := this
  -- combine
  have hK : (0 : ℝ) < Real.pi / (2 * Real.sqrt 2) := by positivity
  have hstep : Real.sqrt 2 * θ ≤ Real.pi / (2 * Real.sqrt 2) * frobNorm ((g : M2) - 1) := by
    have := mul_le_mul_of_nonneg_left hlow (le_of_lt hK)
    calc Real.sqrt 2 * θ
        = Real.pi / (2 * Real.sqrt 2) * (4 / Real.pi * θ) := by
          field_simp; nlinarith [hsq]
      _ ≤ Real.pi / (2 * Real.sqrt 2) * frobNorm ((g : M2) - 1) := this
  linarith

/-- **NARROWNESS, GENERALIZED OVER THE CHART CONSTANT `K`** — which exhibits where §6's `2π` comes
from. The threshold is `4·K·α`, and the `4` is `1 + 2 + 1`, the coefficient count of the SECOND
DIFFERENCE in (3.36); `K` is whatever bounds `‖log g‖_F` by `K·‖g − 1‖_F` on the admitted range.
§6 is the `K = π/2` instance; `coordProxy3536Log_of_gaugeRegular_sharp` is the `K = π/(2√2)` instance. -/
theorem coordProxy3536Log_of_gaugeRegular_gen (Lj c α K : ℝ) (U : PeriodicLinkConfiguration SU2 L)
    (hLj : 1 ≤ Lj) (hα : 0 ≤ α) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hchart : ∀ h : SU2, frobNorm ((h : M2) - 1) ≤ α → frobNorm (su2Log h) ≤ K * α)
    (hthr : 4 * K * α < c * (Lj ^ 3)⁻¹)
    (hbranch : ∀ h : SU2, frobNorm ((h : M2) - 1) ≤ α → su2Exp (su2Log h) = h)
    (hreg : GaugeRegular α U) (cube : Finset (Bond L)) :
    CoordProxy3536Log Lj c cube U := by
  obtain ⟨γ, hsup⟩ := hreg
  set V := periodicGaugeTransform γ U with hV
  have hb : ∀ b : Bond L, frobNorm ((V b : M2) - 1) ≤ α := fun b =>
    le_trans (frobNorm_le_frobSupBond V b) hsup
  have hlog : ∀ b : Bond L, frobNorm (su2Log (V b)) ≤ K * α := fun b => hchart (V b) (hb b)
  have hKα : 0 ≤ K * α := mul_nonneg hK hα
  have hLj0 : (0 : ℝ) < Lj := lt_of_lt_of_le zero_lt_one hLj
  have h31 : c * (Lj ^ 3)⁻¹ ≤ c * Lj⁻¹ := by
    have hi : (Lj ^ 3)⁻¹ ≤ Lj⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hLj0
        (by nlinarith [mul_nonneg (mul_nonneg hLj0.le hLj0.le) (sub_nonneg.mpr hLj)])
    exact mul_le_mul_of_nonneg_left hi hc
  have h32 : c * (Lj ^ 3)⁻¹ ≤ c * (Lj ^ 2)⁻¹ := by
    have hi : (Lj ^ 3)⁻¹ ≤ (Lj ^ 2)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity)
        (by nlinarith [mul_nonneg (mul_nonneg hLj0.le hLj0.le) (sub_nonneg.mpr hLj)])
    exact mul_le_mul_of_nonneg_left hi hc
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · exact fun b _ => hbranch (V b) (hb b)
  · intro b _
    have := hlog b
    linarith
  · intro b _ ν
    have h1 := hlog (shiftBond b ν)
    have h2 := hlog b
    have := frobNorm_sub_le (su2Log (V (shiftBond b ν))) (su2Log (V b))
    linarith
  · intro b _ ν
    have hA := hlog (shiftBond (shiftBond b ν) ν)
    have hB := hlog (shiftBond b ν)
    have hC := hlog b
    have hsmul : frobNorm (((2 : ℝ) : ℂ) • su2Log (V (shiftBond b ν)))
        = 2 * frobNorm (su2Log (V (shiftBond b ν))) := by
      rw [frobNorm_real_smul]; norm_num
    have t1 := frobNorm_sub_le (su2Log (V (shiftBond (shiftBond b ν) ν)))
      (((2 : ℝ) : ℂ) • su2Log (V (shiftBond b ν)))
    have t2 := frobNorm_add_le
      (su2Log (V (shiftBond (shiftBond b ν) ν)) - ((2 : ℝ) : ℂ) • su2Log (V (shiftBond b ν)))
      (su2Log (V b))
    rw [hsmul] at t1
    linarith

/-- **THE LANDED §6 THEOREM IS THE `K = π/2` INSTANCE** — a consistency check on the generalization,
not a new result: `4·(π/2) = 2π`. -/
theorem coordProxy3536Log_of_gaugeRegular_gen_recovers_landed (Lj c α : ℝ)
    (U : PeriodicLinkConfiguration SU2 L)
    (hLj : 1 ≤ Lj) (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hthr : 2 * Real.pi * α < c * (Lj ^ 3)⁻¹)
    (hbranch : ∀ h : SU2, frobNorm ((h : M2) - 1) ≤ α → su2Exp (su2Log h) = h)
    (hreg : GaugeRegular α U) (cube : Finset (Bond L)) :
    CoordProxy3536Log Lj c cube U := by
  refine coordProxy3536Log_of_gaugeRegular_gen Lj c α (Real.pi / 2) U hLj hα hc
    (by positivity) (fun h hh => ?_) (by linarith [hthr]) hbranch hreg cube
  refine le_trans (frobNorm_su2Log_le_pi_div_two h) ?_
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [hh, frobNorm_nonneg ((h : M2) - 1)]

/-- **NARROWNESS AT THE SHARPENED CONSTANT.** `√2·π·α < c·(L^j)⁻³` suffices, in place of §6's
`2π·α`, whenever `α ≤ 2`. The branch hypothesis is discharged for free: `α ≤ 2 < 2√2`. -/
theorem coordProxy3536Log_of_gaugeRegular_sharp (Lj c α : ℝ) (U : PeriodicLinkConfiguration SU2 L)
    (hLj : 1 ≤ Lj) (hα : 0 ≤ α) (hc : 0 ≤ c) (hα2 : α ≤ 2)
    (hthr : Real.sqrt 2 * Real.pi * α < c * (Lj ^ 3)⁻¹)
    (hreg : GaugeRegular α U) (cube : Finset (Bond L)) :
    CoordProxy3536Log Lj c cube U := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2lt : (1 : ℝ) < Real.sqrt 2 := by nlinarith [hsq, hs2]
  have h2lt : (2 : ℝ) < 2 * Real.sqrt 2 := by linarith
  have h4K : 4 * (Real.pi / (2 * Real.sqrt 2)) = Real.sqrt 2 * Real.pi := by
    field_simp; nlinarith [hsq]
  refine coordProxy3536Log_of_gaugeRegular_gen Lj c α (Real.pi / (2 * Real.sqrt 2)) U hLj hα hc
    (by positivity) (fun h hh => ?_) (by rw [h4K]; exact hthr) (fun h hh => ?_) hreg cube
  · exact le_trans (frobNorm_su2Log_le_sharp h (le_trans hh hα2))
      (mul_le_mul_of_nonneg_left hh (by positivity))
  · exact su2_exp_log_of_frobNorm_lt h (lt_of_le_of_lt (le_trans hh hα2) h2lt)

#print axioms sin_ge_of_le_pi_div_four
#print axioms frobNorm_su2Log_le_sharp
#print axioms coordProxy3536Log_of_gaugeRegular_gen
#print axioms coordProxy3536Log_of_gaugeRegular_gen_recovers_landed
#print axioms coordProxy3536Log_of_gaugeRegular_sharp


/-! ## §12-§14 — ADDED 2026-07-30 by `compute/wideness_retraction/` (the RETRACTION lane).

These sections exist because a de-correlated Sol-family prosecution
(`compute/sol_regularity/SOL_VERDICT.md`) convicted the source-fidelity claim of §1-§11 on three
DEFINITION defects. They repair the definition; they do not alter one statement, hypothesis,
constant or proof of §1-§11, which are retained in full under renamed (honest) identifiers. -/

open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack
  periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift periodicLatticeShiftEquiv)
open AdalyFormal.Balaban.AdmissibleSubspace (inBlock blockOf mem_blockOf)
open AdalyFormal.Balaban.AlphaAnalyticity (shift_ne_self)
open scoped Matrix

/-! ## §12 — THE FAITHFUL (3.36) OPERATOR -/

/-- Backward shift of a bond's base site. -/
def shiftBondBack (b : Bond L) (ν : Fin 3) : Bond L := (periodicLatticeShiftBack b.1 ν, b.2)

/-- `(∂^η A)_{μν}(x)`. -/
noncomputable def extD (η : ℝ) (A : Bond L → M2) (x : PeriodicLatticeSite L) (μ ν : Fin 3) : M2 :=
  ((η⁻¹ : ℝ) : ℂ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)
    - A (periodicLatticeShift x ν, μ) + A (x, μ))

theorem extD_antisymm (η : ℝ) (A : Bond L → M2) (x : PeriodicLatticeSite L) (μ ν : Fin 3) :
    extD η A x μ ν = - extD η A x ν μ := by
  unfold extD
  rw [← smul_neg]
  congr 1
  abel

theorem extD_self (η : ℝ) (A : Bond L → M2) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    extD η A x μ μ = 0 := by
  unfold extD
  have h : A (periodicLatticeShift x μ, μ) - A (x, μ) - A (periodicLatticeShift x μ, μ)
      + A (x, μ) = 0 := by abel
  rw [h, smul_zero]

/-- `(∂^{η*}F)_μ(x) = Σ_ν η⁻¹ (F_{μν}(x) − F_{μν}(x−ην))`. -/
noncomputable def extDStar (η : ℝ)
    (F : PeriodicLatticeSite L → Fin 3 → Fin 3 → M2) (b : Bond L) : M2 :=
  ∑ ν : Fin 3, ((η⁻¹ : ℝ) : ℂ) • (F b.1 b.2 ν - F (periodicLatticeShiftBack b.1 ν) b.2 ν)

/-- **`∂^{η*}∂^η A`**, the operator (3.36) bounds. -/
noncomputable def extDStarD (η : ℝ) (A : Bond L → M2) (b : Bond L) : M2 :=
  extDStar η (fun x μ ν => extD η A x μ ν) b

/-! ### the pairing and the adjoint identity -/

/-- The `ℂ`-bilinear entrywise pairing `⟪M, N⟫ = Σ_{ij} M_{ij} N_{ij} = tr (M Nᵀ)`. -/
def pairM (M N : M2) : ℂ := Matrix.trace (M * Nᵀ)

theorem pairM_sub_left (M N P : M2) : pairM (M - N) P = pairM M P - pairM N P := by
  simp [pairM, Matrix.sub_mul, Matrix.trace_sub]

theorem pairM_add_left (M N P : M2) : pairM (M + N) P = pairM M P + pairM N P := by
  simp [pairM, Matrix.add_mul, Matrix.trace_add]

theorem pairM_smul_left (r : ℂ) (M P : M2) : pairM (r • M) P = r * pairM M P := by
  simp [pairM, Matrix.trace_smul, smul_eq_mul]

theorem pairM_sub_right (M N P : M2) : pairM M (N - P) = pairM M N - pairM M P := by
  simp [pairM, Matrix.mul_sub, Matrix.trace_sub]

theorem pairM_neg_right (M N : M2) : pairM M (-N) = - pairM M N := by
  simp [pairM]

theorem pairM_smul_right (r : ℂ) (M P : M2) : pairM M (r • P) = r * pairM M P := by
  simp [pairM, Matrix.trace_smul, smul_eq_mul]

theorem pairM_sum_right (M : M2) (f : Fin 3 → M2) :
    pairM M (∑ ν : Fin 3, f ν) = ∑ ν : Fin 3, pairM M (f ν) := by
  unfold pairM
  rw [Matrix.transpose_sum, Matrix.mul_sum, Matrix.trace_sum]

/-- Reindexing a site sum along the forward shift. -/
theorem sum_shift (μ : Fin 3) (f : PeriodicLatticeSite L → ℂ) :
    ∑ x : PeriodicLatticeSite L, f (periodicLatticeShift x μ)
      = ∑ x : PeriodicLatticeSite L, f x :=
  Fintype.sum_equiv (periodicLatticeShiftEquiv μ) _ _ (fun _ => rfl)

/-- **THE ADJOINT IDENTITY.** For every antisymmetric `2`-form `F`,
`⟪∂^η A, F⟫₂ = 2·⟪A, ∂^{η*}F⟫₁`, the `⟪·,·⟫₂` sum running over ORDERED direction pairs (hence the
counted factor `2 = |{(μ,ν),(ν,μ)}|`). This is what entitles `extDStar` to the name "adjoint"; it
is proved, not asserted. -/
theorem extD_adjoint (η : ℝ) (A : Bond L → M2)
    (F : PeriodicLatticeSite L → Fin 3 → Fin 3 → M2)
    (hF : ∀ x μ ν, F x μ ν = - F x ν μ) :
    (∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, pairM (extD η A x μ ν) (F x μ ν))
      = 2 * ∑ b : Bond L, pairM (A b) (extDStar η F b) := by
  classical
  set c : ℂ := ((η⁻¹ : ℝ) : ℂ) with hcdef
  set P : PeriodicLatticeSite L → Fin 3 → Fin 3 → ℂ :=
    fun x μ ν => c * pairM (A (periodicLatticeShift x μ, ν)) (F x μ ν)
      - c * pairM (A (x, ν)) (F x μ ν) with hPdef
  -- (1) the summand splits as `P x μ ν + P x ν μ`.
  have h1 : ∀ (x : PeriodicLatticeSite L) (μ ν : Fin 3),
      pairM (extD η A x μ ν) (F x μ ν) = P x μ ν + P x ν μ := by
    intro x μ ν
    have hswap : F x ν μ = - F x μ ν := hF x ν μ
    simp only [hPdef, extD, pairM_smul_left, pairM_add_left, pairM_sub_left, hswap,
      pairM_neg_right, hcdef]
    ring
  -- (2) the double sum of `P x ν μ` equals that of `P x μ ν`.
  have h2 : ∀ x : PeriodicLatticeSite L,
      (∑ μ : Fin 3, ∑ ν : Fin 3, P x ν μ) = ∑ μ : Fin 3, ∑ ν : Fin 3, P x μ ν :=
    fun x => Finset.sum_comm
  -- (3) so the whole triple sum is `2 * ∑ P`.
  have h3 : (∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
        pairM (extD η A x μ ν) (F x μ ν))
      = 2 * ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, P x μ ν := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : (∑ μ : Fin 3, ∑ ν : Fin 3, pairM (extD η A x μ ν) (F x μ ν))
        = (∑ μ : Fin 3, ∑ ν : Fin 3, P x μ ν) + (∑ μ : Fin 3, ∑ ν : Fin 3, P x ν μ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ν _ => h1 x μ ν
    rw [this, h2 x]
    ring
  -- (4) the reindexed inner sum, for fixed `μ ν`.
  have h4 : ∀ μ ν : Fin 3,
      (∑ x : PeriodicLatticeSite L, P x μ ν)
        = ∑ x : PeriodicLatticeSite L,
            pairM (A (x, ν)) (c • (F (periodicLatticeShiftBack x μ) μ ν - F x μ ν)) := by
    intro μ ν
    have hre : (∑ x : PeriodicLatticeSite L,
          c * pairM (A (periodicLatticeShift x μ, ν)) (F x μ ν))
        = ∑ x : PeriodicLatticeSite L,
            c * pairM (A (x, ν)) (F (periodicLatticeShiftBack x μ) μ ν) := by
      have := sum_shift (L := L) μ
        (fun x => c * pairM (A (x, ν)) (F (periodicLatticeShiftBack x μ) μ ν))
      rw [← this]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [periodicLatticeShiftBack_shift]
    simp only [hPdef]
    rw [Finset.sum_sub_distrib, hre, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [pairM_smul_right, pairM_sub_right]
    ring
  -- (5) assemble.
  have h5 : (∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, P x μ ν)
      = ∑ b : Bond L, pairM (A b) (extDStar η F b) := by
    have e1 : (∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, P x μ ν)
        = ∑ x : PeriodicLatticeSite L, ∑ ν : Fin 3, ∑ μ : Fin 3,
            pairM (A (x, ν)) (c • (F (periodicLatticeShiftBack x μ) μ ν - F x μ ν)) := by
      calc (∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, P x μ ν)
          = ∑ μ : Fin 3, ∑ x : PeriodicLatticeSite L, ∑ ν : Fin 3, P x μ ν := Finset.sum_comm
        _ = ∑ μ : Fin 3, ∑ ν : Fin 3, ∑ x : PeriodicLatticeSite L, P x μ ν :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ μ : Fin 3, ∑ ν : Fin 3, ∑ x : PeriodicLatticeSite L,
              pairM (A (x, ν)) (c • (F (periodicLatticeShiftBack x μ) μ ν - F x μ ν)) :=
            Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => h4 μ ν
        _ = ∑ μ : Fin 3, ∑ x : PeriodicLatticeSite L, ∑ ν : Fin 3,
              pairM (A (x, ν)) (c • (F (periodicLatticeShiftBack x μ) μ ν - F x μ ν)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
              pairM (A (x, ν)) (c • (F (periodicLatticeShiftBack x μ) μ ν - F x μ ν)) :=
            Finset.sum_comm
        _ = ∑ x : PeriodicLatticeSite L, ∑ ν : Fin 3, ∑ μ : Fin 3,
              pairM (A (x, ν)) (c • (F (periodicLatticeShiftBack x μ) μ ν - F x μ ν)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [e1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [← pairM_sum_right]
    congr 1
    unfold extDStar
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hs1 : F x ν μ = - F x μ ν := hF x ν μ
    have hs2 : F (periodicLatticeShiftBack x μ) ν μ
        = - F (periodicLatticeShiftBack x μ) μ ν := hF (periodicLatticeShiftBack x μ) ν μ
    simp only [hs1, hs2, hcdef]
    congr 1
    abel
  rw [h3, h5]

/-! ### §12a — the two operators are DIFFERENT -/

/-- The convicted stencil, at the level of a general `M2`-valued bond field: `coordLapA` is exactly
`(η²)⁻¹` times this, so any statement proved here is about the operator the file actually used. -/
noncomputable def coordSecondDiff (A : Bond L → M2) (b : Bond L) (ν : Fin 3) : M2 :=
  A (shiftBond (shiftBond b ν) ν) - ((2 : ℝ) : ℂ) • A (shiftBond b ν) + A b

theorem coordLapA_eq_stencil (η : ℝ) (V : PeriodicLinkConfiguration SU2 L) (b : Bond L)
    (ν : Fin 3) :
    coordLapA η V b ν = (((η ^ 2)⁻¹ : ℝ) : ℂ) • coordSecondDiff (chartA η V) b ν := rfl

/-- The separating lattice: side `4` in each direction. -/
def sepLat : PeriodicLatticeExtent := fun _ => 3

/-- Its origin. -/
def sepSite : PeriodicLatticeSite sepLat := fun _ => 0

/-- A one-form supported on the single bond `(origin, direction 1)`. -/
noncomputable def sepA : Bond sepLat → M2 := fun b => if b = (sepSite, 1) then 1 else 0

/-- The bond at which the two operators are evaluated: `(origin, direction 0)`. -/
def sepBond : Bond sepLat := (sepSite, 0)

theorem sepA_of_dir_ne {b : Bond sepLat} (h : b.2 ≠ 1) : sepA b = 0 := by
  classical
  simp only [sepA]
  rw [if_neg]
  intro hc
  exact h (congrArg Prod.snd hc)

theorem sepA_of_site_ne {b : Bond sepLat} (h : b.1 ≠ sepSite) : sepA b = 0 := by
  classical
  simp only [sepA]
  rw [if_neg]
  intro hc
  exact h (congrArg Prod.fst hc)

theorem shiftBond_snd (b : Bond L) (ν : Fin 3) : (shiftBond b ν).2 = b.2 := rfl

/-- Every coordinatewise second difference of `sepA` VANISHES at `sepBond`. -/
theorem sep_coordSecondDiff_zero (ν : Fin 3) : coordSecondDiff sepA sepBond ν = 0 := by
  have h0 : ∀ b : Bond sepLat, b.2 = (0 : Fin 3) → sepA b = 0 := by
    intro b hb
    exact sepA_of_dir_ne (by rw [hb]; decide)
  have e1 : sepA (shiftBond (shiftBond sepBond ν) ν) = 0 := h0 _ rfl
  have e2 : sepA (shiftBond sepBond ν) = 0 := h0 _ rfl
  have e3 : sepA sepBond = 0 := h0 _ rfl
  simp [coordSecondDiff, e1, e2, e3]


/-! ### shift facts the separating example needs -/

theorem shiftBack_ne_self (x : PeriodicLatticeSite L) (ν : Fin 3) (h : 1 ≤ L ν) :
    periodicLatticeShiftBack x ν ≠ x := by
  intro heq
  have hx : periodicLatticeShift x ν = x := by
    have := periodicLatticeShift_shiftBack x ν
    rwa [heq] at this
  exact shift_ne_self x ν h hx

/-- Shifting FORWARD in a direction `μ` cannot undo a BACKWARD shift in a different direction. -/
theorem shift_shiftBack_ne_self (x : PeriodicLatticeSite L) (μ ν : Fin 3) (hμν : μ ≠ ν)
    (h : 1 ≤ L ν) : periodicLatticeShift (periodicLatticeShiftBack x ν) μ ≠ x := by
  intro heq
  have hc : x ν - 1 = x ν := by
    have := congrFun heq ν
    rwa [periodicLatticeShift, Function.update_of_ne (Ne.symm hμν),
      periodicLatticeShiftBack, Function.update_self] at this
  have h1 : (1 : Fin (L ν + 1)) = 0 := by
    have h2 := congrArg (fun z : Fin (L ν + 1) => x ν - z) hc
    simp at h2
    have h3 := congrArg (fun z : Fin (L ν + 1) => z - x ν + 1) hc
    simpa using h3
  have hval : (1 : Fin (L ν + 1)).val = (0 : Fin (L ν + 1)).val := congrArg Fin.val h1
  rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (show 1 < L ν + 1 by omega)] at hval
  omega

/-! ### §12b — THE SEPARATION, kernel checked -/

theorem extD_sepA_dirZero (x : PeriodicLatticeSite sepLat) (ν : Fin 3) :
    extD 1 sepA x 0 ν = sepA (periodicLatticeShift x 0, ν) - sepA (x, ν) := by
  have hne01 : (0 : Fin 3) ≠ 1 := by decide
  have hz1 : sepA (periodicLatticeShift x ν, 0) = 0 := sepA_of_dir_ne hne01
  have hz2 : sepA (x, (0 : Fin 3)) = 0 := sepA_of_dir_ne hne01
  simp [extD, hz1, hz2]

theorem sep_extDStarD_ne_zero : extDStarD 1 sepA sepBond ≠ 0 := by
  classical
  have hL : ∀ μ : Fin 3, 1 ≤ sepLat μ := fun _ => by unfold sepLat; omega
  have hA : periodicLatticeShift sepSite 0 ≠ sepSite := shift_ne_self sepSite 0 (hL 0)
  have hB : periodicLatticeShiftBack sepSite 1 ≠ sepSite := shiftBack_ne_self sepSite 1 (hL 1)
  have hC : periodicLatticeShift (periodicLatticeShiftBack sepSite 1) 0 ≠ sepSite :=
    shift_shiftBack_ne_self sepSite 0 1 (by decide) (hL 1)
  -- the six `extD` values
  have hne01 : (0 : Fin 3) ≠ 1 := by decide
  have hne21 : (2 : Fin 3) ≠ 1 := by decide
  have v00 : extD 1 sepA sepSite 0 0 = 0 := by
    rw [extD_sepA_dirZero]
    rw [sepA_of_dir_ne (b := (periodicLatticeShift sepSite 0, (0 : Fin 3))) hne01,
      sepA_of_dir_ne (b := (sepSite, (0 : Fin 3))) hne01]
    abel
  have v01 : extD 1 sepA sepSite 0 1 = -1 := by
    rw [extD_sepA_dirZero]
    rw [sepA_of_site_ne (b := (periodicLatticeShift sepSite 0, (1 : Fin 3))) hA]
    have : sepA (sepSite, (1 : Fin 3)) = 1 := by simp [sepA]
    rw [this]
    abel
  have v02 : extD 1 sepA sepSite 0 2 = 0 := by
    rw [extD_sepA_dirZero]
    rw [sepA_of_dir_ne (b := (periodicLatticeShift sepSite 0, (2 : Fin 3))) hne21,
      sepA_of_dir_ne (b := (sepSite, (2 : Fin 3))) hne21]
    abel
  have w00 : extD 1 sepA (periodicLatticeShiftBack sepSite 0) 0 0 = 0 := by
    rw [extD_sepA_dirZero]
    rw [sepA_of_dir_ne
        (b := (periodicLatticeShift (periodicLatticeShiftBack sepSite 0) 0, (0 : Fin 3))) hne01,
      sepA_of_dir_ne (b := (periodicLatticeShiftBack sepSite 0, (0 : Fin 3))) hne01]
    abel
  have w01 : extD 1 sepA (periodicLatticeShiftBack sepSite 1) 0 1 = 0 := by
    rw [extD_sepA_dirZero]
    rw [sepA_of_site_ne
        (b := (periodicLatticeShift (periodicLatticeShiftBack sepSite 1) 0, (1 : Fin 3))) hC,
      sepA_of_site_ne (b := (periodicLatticeShiftBack sepSite 1, (1 : Fin 3))) hB]
    abel
  have w02 : extD 1 sepA (periodicLatticeShiftBack sepSite 2) 0 2 = 0 := by
    rw [extD_sepA_dirZero]
    rw [sepA_of_dir_ne
        (b := (periodicLatticeShift (periodicLatticeShiftBack sepSite 2) 0, (2 : Fin 3))) hne21,
      sepA_of_dir_ne (b := (periodicLatticeShiftBack sepSite 2, (2 : Fin 3))) hne21]
    abel
  have hval : extDStarD 1 sepA sepBond = -1 := by
    unfold extDStarD extDStar
    rw [Fin.sum_univ_three]
    show ((((1:ℝ))⁻¹ : ℝ) : ℂ) • (extD 1 sepA sepBond.1 sepBond.2 0
        - extD 1 sepA (periodicLatticeShiftBack sepBond.1 0) sepBond.2 0)
      + ((((1:ℝ))⁻¹ : ℝ) : ℂ) • (extD 1 sepA sepBond.1 sepBond.2 1
        - extD 1 sepA (periodicLatticeShiftBack sepBond.1 1) sepBond.2 1)
      + ((((1:ℝ))⁻¹ : ℝ) : ℂ) • (extD 1 sepA sepBond.1 sepBond.2 2
        - extD 1 sepA (periodicLatticeShiftBack sepBond.1 2) sepBond.2 2) = -1
    have hb1 : sepBond.1 = sepSite := rfl
    have hb2 : sepBond.2 = (0 : Fin 3) := rfl
    rw [hb1, hb2, v00, v01, v02, w00, w01, w02]
    simp
  rw [hval]
  simp

/-- **THE Q1 DEFECT, KERNEL CHECKED.** There is a `1`-form on which EVERY coordinatewise second
difference vanishes at a bond while the exterior `∂^{η*}∂^η` does not. The two operators are
therefore different operators, not different conventions for one operator. -/
theorem coordSecondDiff_ne_extDStarD :
    ∃ (A : Bond sepLat → M2) (b : Bond sepLat),
      (∀ ν : Fin 3, coordSecondDiff A b ν = 0) ∧ extDStarD 1 A b ≠ 0 :=
  ⟨sepA, sepBond, sep_coordSecondDiff_zero, sep_extDStarD_ne_zero⟩


/-! ## §13 — THE PRINTED CUBE CLASS -/

open AdalyFormal.Balaban.AdmissibleSubspace (inBlock blockOf mem_blockOf)

/-- The bonds whose base site lies in the coordinate box of side `s` based at `y`.

**THIS IS THE BASE-SITE SET, AND IT IS NOT THE CARRIER THE PRINTED BOUNDS RANGE OVER.** Added
2026-08-05 (`compute/formal_batch/`); the declaration itself is UNCHANGED, so every existing
importer is unaffected.

Two facts a consumer needs, both established elsewhere in this file:

1. **CARRIER.** `compute/carrier_adjudication/ADJUDICATION.md` (ledger
   `CARRIER-RULED-INTERNAL-BONDS`) adjudicates *"on `□`"* in (3.35)/(3.36) as the INTERNAL bonds —
   both endpoints in the box — because p.396 builds `A` from *"a gauge transformation `u` on `□`"*
   and p.395's `U^u(x,x') = u(x)U(x,x')u^{-1}(x')` needs `u` at both endpoints. The faithful
   constructor is **`interiorCubeBondsF`** (§17a). At a fitted side-`10` box the two sets differ by
   `300` bonds out of `3000` (`carrier_gap_at_ten`).
2. **TRUNCATION.** This set is defined by `inBlock`, a NON-WRAPPING half-open interval intersected
   with the finite extent, and `IsSourceCube` does not require that interval to FIT. At the corner
   of a small lattice a nominal side-`10` box silently truncates, so the SAME three-bond set can be
   `IsSourceCube` at two different nominal sides. Every exact count in §17a therefore carries the
   fit clause `∀ μ, (y μ).val + s ≤ L μ + 1` as an explicit hypothesis
   (`sourceCubeBonds_card_of_fit`, `interiorCubeBondsF_card`), and without it both counts are false.

`sourceCubeBonds` is retained because §12-§14c are stated over it and because it is the set whose
count the disclosure arithmetic subtracts from. -/
def sourceCubeBonds (y : PeriodicLatticeSite L) (s : ℕ) : Finset (Bond L) :=
  Finset.univ.filter (fun b : Bond L => inBlock y s b.1)

theorem mem_sourceCubeBonds {y : PeriodicLatticeSite L} {s : ℕ} {b : Bond L} :
    b ∈ sourceCubeBonds y s ↔ inBlock y s b.1 := by
  classical
  simp [sourceCubeBonds]

/-- **CMP99b p.396's cube class**, at the level of structure the page fixes: `□` is a coordinate
box which is a union of big blocks, of size `O(1)M L^j` with `O(1) ≥ 10` and
~~`M ≥ 1`~~ — **STRUCK, corrected 2026-08-05 (`compute/formal_batch/`, S75), and retained struck:**
`M ≥ M_1` with `M_1` UNSPECIFIED. `compute/cube_convention/ADJUDICATION.md` (ledger
`CUBE-CONVENTION-BOX-FORCED-AT-P408`) rules that `M ≥ 1` is not printed on the read pages: the
source's only inequality on `M` is Theorem 3.1's `M ≥ M_1` with `M_1` left unspecified (CMP96
p.232, *"`M` sufficiently large"*), so citing a bare `M ≥ 1` UNDERSTATES the source hypothesis.
Nothing in this definition consumes any floor on `M` — `IsSourceCube` never mentions `M` — so the
correction is to the READING, not to the object; §17's `DomainTower` carries the floor it actually
uses as the explicit typed field `hM : 2 ≤ M`, disclosed there as strictly weaker than `M ≥ M_1`.
At a scale `L^j ≥ 1`. The two clauses that matter adversarially are the SIDE FLOOR `10·Lj ≤ s` and
`1 ≤ Lj`; together they force `10 ≤ s`, which is what kills the empty and singleton attacks. -/
def IsSourceCube (Lj : ℝ) (cube : Finset (Bond L)) : Prop :=
  ∃ (y : PeriodicLatticeSite L) (s : ℕ),
    cube = sourceCubeBonds y s ∧ (1 : ℝ) ≤ Lj ∧ (10 : ℝ) * Lj ≤ (s : ℝ)

theorem ten_le_of_isSourceCube {Lj : ℝ} {cube : Finset (Bond L)} (h : IsSourceCube Lj cube) :
    ∃ (y : PeriodicLatticeSite L) (s : ℕ), cube = sourceCubeBonds y s ∧ 10 ≤ s := by
  obtain ⟨y, s, hc, hLj, hs⟩ := h
  refine ⟨y, s, hc, ?_⟩
  have : (10 : ℝ) ≤ (s : ℝ) := le_trans (by nlinarith) hs
  exact_mod_cast this

theorem mem_sourceCubeBonds_base {y : PeriodicLatticeSite L} {s : ℕ} (hs : 1 ≤ s)
    (d : Fin 3) : ((y, d) : Bond L) ∈ sourceCubeBonds y s := by
  rw [mem_sourceCubeBonds]
  intro μ
  have hfst : ((y, d) : Bond L).1 = y := rfl
  rw [hfst]
  exact ⟨le_rfl, by omega⟩

/-- **A source cube is NONEMPTY** — the empty-`Finset` collapse is blocked by the class itself. -/
theorem nonempty_of_isSourceCube {Lj : ℝ} {cube : Finset (Bond L)} (h : IsSourceCube Lj cube) :
    cube.Nonempty := by
  obtain ⟨y, s, hc, hs⟩ := ten_le_of_isSourceCube h
  exact ⟨(y, 0), by rw [hc]; exact mem_sourceCubeBonds_base (by omega) 0⟩

/-- **THE EMPTY `Finset` IS NOT A SOURCE CUBE.** -/
theorem empty_not_isSourceCube (Lj : ℝ) :
    ¬ IsSourceCube Lj (∅ : Finset (Bond L)) := by
  intro h
  obtain ⟨b, hb⟩ := nonempty_of_isSourceCube h
  exact absurd hb (Finset.notMem_empty b)

/-- **NO SINGLETON IS A SOURCE CUBE.** A source cube contains at least the three bonds based at
its own corner, one per direction. -/
theorem singleton_not_isSourceCube (Lj : ℝ) (b : Bond L) :
    ¬ IsSourceCube Lj ({b} : Finset (Bond L)) := by
  intro h
  obtain ⟨y, s, hc, hs⟩ := ten_le_of_isSourceCube h
  have h0 : ((y, 0) : Bond L) ∈ ({b} : Finset (Bond L)) := by
    rw [hc]; exact mem_sourceCubeBonds_base (by omega) 0
  have h1 : ((y, 1) : Bond L) ∈ ({b} : Finset (Bond L)) := by
    rw [hc]; exact mem_sourceCubeBonds_base (by omega) 1
  rw [Finset.mem_singleton] at h0 h1
  have : ((y, 0) : Bond L) = ((y, 1) : Bond L) := h0.trans h1.symm
  have hd : (0 : Fin 3) = 1 := congrArg Prod.snd this
  exact absurd hd (by decide)

/-- A lattice with room for a printed cube AND a margin: side `16` in each direction. The cube is
based at coordinate `1` and has side `10`, so its sites are `1..10`; a single forward shift reaches
`11` and a single backward shift reaches `0`, both without wrapping, and coordinates `12..15` are
left over for an excitation the cube's clauses cannot see (§14c). -/
def bigLat : PeriodicLatticeExtent := fun _ => 15

/-- **SOURCE CUBES EXIST.** Non-vacuity of the class, at `Lj = 1`, side `10`, on `bigLat`. -/
theorem exists_isSourceCube :
    ∃ cube : Finset (Bond bigLat), IsSourceCube 1 cube ∧ cube.Nonempty := by
  set y0 : PeriodicLatticeSite bigLat := fun _ => 0 with hy0
  refine ⟨sourceCubeBonds y0 10, ⟨y0, 10, rfl, le_rfl, by norm_num⟩, ?_⟩
  exact ⟨(y0, 0), mem_sourceCubeBonds_base (by omega) 0⟩


/-! ## §14 — THE FAITHFUL PREDICATE -/

/-- `log U(b)` as a `1`-form. `chartA η V = η⁻¹ • logField V`, definitionally. -/
noncomputable def logField (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) : M2 :=
  su2Log (V b)

theorem chartA_eq_smul_logField (η : ℝ) (V : PeriodicLinkConfiguration SU2 L) :
    chartA η V = fun b => ((η⁻¹ : ℝ) : ℂ) • logField V b := rfl

/-! ### homogeneity of the exterior operator -/

theorem extD_smul (η : ℝ) (r : ℂ) (A : Bond L → M2) (x : PeriodicLatticeSite L) (μ ν : Fin 3) :
    extD η (fun b => r • A b) x μ ν = r • extD η A x μ ν := by
  unfold extD
  have h : (r • A (periodicLatticeShift x μ, ν) - r • A (x, ν)
      - r • A (periodicLatticeShift x ν, μ) + r • A (x, μ))
      = r • (A (periodicLatticeShift x μ, ν) - A (x, ν)
        - A (periodicLatticeShift x ν, μ) + A (x, μ)) := by
    simp [smul_sub, smul_add]
  rw [h, smul_comm]

theorem extDStar_smul (η : ℝ) (r : ℂ)
    (F : PeriodicLatticeSite L → Fin 3 → Fin 3 → M2) (b : Bond L) :
    extDStar η (fun x μ ν => r • F x μ ν) b = r • extDStar η F b := by
  unfold extDStar
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← smul_sub, smul_comm]

theorem extD_eta (η : ℝ) (A : Bond L → M2) (x : PeriodicLatticeSite L) (μ ν : Fin 3) :
    extD η A x μ ν = ((η⁻¹ : ℝ) : ℂ) • extD 1 A x μ ν := by
  unfold extD; simp

theorem extDStar_eta (η : ℝ) (F : PeriodicLatticeSite L → Fin 3 → Fin 3 → M2) (b : Bond L) :
    extDStar η F b = ((η⁻¹ : ℝ) : ℂ) • extDStar 1 F b := by
  unfold extDStar
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp

theorem extDStarD_smul (η : ℝ) (r : ℂ) (A : Bond L → M2) (b : Bond L) :
    extDStarD η (fun b' => r • A b') b = r • extDStarD η A b := by
  unfold extDStarD
  rw [show (fun (x : PeriodicLatticeSite L) (μ ν : Fin 3) =>
        extD η (fun b' => r • A b') x μ ν)
      = (fun (x : PeriodicLatticeSite L) (μ ν : Fin 3) => r • extD η A x μ ν) from
    funext fun x => funext fun μ => funext fun ν => extD_smul η r A x μ ν]
  exact extDStar_smul η r _ b

theorem extDStarD_eta (η : ℝ) (A : Bond L → M2) (b : Bond L) :
    extDStarD η A b = ((((η⁻¹) ^ 2 : ℝ)) : ℂ) • extDStarD 1 A b := by
  unfold extDStarD
  rw [show (fun (x : PeriodicLatticeSite L) (μ ν : Fin 3) => extD η A x μ ν)
      = (fun (x : PeriodicLatticeSite L) (μ ν : Fin 3) => ((η⁻¹ : ℝ) : ℂ) • extD 1 A x μ ν) from
    funext fun x => funext fun μ => funext fun ν => extD_eta η A x μ ν]
  rw [extDStar_smul, extDStar_eta, smul_smul, ← Complex.ofReal_mul]
  congr 2
  ring

theorem extDStarD_chartA (η : ℝ) (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) :
    extDStarD η (chartA η V) b = ((((η⁻¹) ^ 3 : ℝ)) : ℂ) • extDStarD 1 (logField V) b := by
  rw [chartA_eq_smul_logField, extDStarD_smul, extDStarD_eta, smul_smul, ← Complex.ofReal_mul]
  congr 2
  ring

private theorem extDStarD_chartA_norm (η : ℝ) (hη : 0 < η)
    (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) :
    frobNorm (extDStarD η (chartA η V) b)
      = (η⁻¹) ^ 3 * frobNorm (extDStarD 1 (logField V) b) := by
  rw [extDStarD_chartA, frobNorm_real_smul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (η⁻¹) ^ 3)]

/-! ### the faithful predicate itself -/

/-- **CMP99b (3.35) ∧ (3.36), FAITHFULLY.** Three repairs against `CoordProxy3536`:
the fourth clause is the EXTERIOR `∂^{η*}∂^η` (`extDStarD`), not a coordinatewise second
difference; it carries no `∀ ν`, because `∂^{η*}∂^ηA` is already a `1`-form (one value per bond);
and the cube is meant to be quantified inside the printed class `IsSourceCube`. -/
def Src3536Faithful (η Lj c : ℝ) (cube : Finset (Bond L))
    (U : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∃ γ : PeriodicLatticeSite L → SU2,
    (∀ b ∈ cube, su2Exp (su2Log (periodicGaugeTransform γ U b))
        = periodicGaugeTransform γ U b) ∧
    (∀ b ∈ cube, frobNorm (chartA η (periodicGaugeTransform γ U) b) < c * (Lj * η)⁻¹) ∧
    (∀ b ∈ cube, ∀ ν, frobNorm (gradA η (periodicGaugeTransform γ U) b ν)
        < c * ((Lj * η) ^ 2)⁻¹) ∧
    (∀ b ∈ cube, frobNorm (extDStarD η (chartA η (periodicGaugeTransform γ U)) b)
        < c * ((Lj * η) ^ 3)⁻¹)

/-- The same with `η` eliminated. -/
def Src3536FaithfulLog (Lj c : ℝ) (cube : Finset (Bond L))
    (U : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∃ γ : PeriodicLatticeSite L → SU2,
    (∀ b ∈ cube, su2Exp (su2Log (periodicGaugeTransform γ U b))
        = periodicGaugeTransform γ U b) ∧
    (∀ b ∈ cube, frobNorm (su2Log (periodicGaugeTransform γ U b)) < c * Lj⁻¹) ∧
    (∀ b ∈ cube, ∀ ν, frobNorm (su2Log (periodicGaugeTransform γ U (shiftBond b ν))
        - su2Log (periodicGaugeTransform γ U b)) < c * (Lj ^ 2)⁻¹) ∧
    (∀ b ∈ cube, frobNorm (extDStarD 1 (logField (periodicGaugeTransform γ U)) b)
        < c * (Lj ^ 3)⁻¹)

/-- **`η` CANCELS FROM THE FAITHFUL PREDICATE TOO.** The exterior stencil carries the same two
powers of `η⁻¹` the coordinatewise one did, so the cancellation is not an artifact of the
substituted operator. -/
theorem src3536Faithful_eta_free (η Lj c : ℝ) (hη : 0 < η) (cube : Finset (Bond L))
    (U : PeriodicLinkConfiguration SU2 L) :
    Src3536Faithful η Lj c cube U ↔ Src3536FaithfulLog Lj c cube U := by
  have hpos : (0:ℝ) < η⁻¹ := inv_pos.mpr hη
  have key1 : ∀ (V : PeriodicLinkConfiguration SU2 L) (b : Bond L),
      (frobNorm (chartA η V b) < c * (Lj * η)⁻¹ ↔ frobNorm (su2Log (V b)) < c * Lj⁻¹) := by
    intro V b
    rw [chartA_norm η hη V b, mul_inv, ← mul_assoc]
    constructor
    · intro h; nlinarith [h]
    · intro h; nlinarith [h]
  have key2 : ∀ (V : PeriodicLinkConfiguration SU2 L) (b : Bond L) (ν : Fin 3),
      (frobNorm (gradA η V b ν) < c * ((Lj * η) ^ 2)⁻¹ ↔
        frobNorm (su2Log (V (shiftBond b ν)) - su2Log (V b)) < c * (Lj ^ 2)⁻¹) := by
    intro V b ν
    rw [gradA_norm η hη V b ν]
    have he : ((Lj * η) ^ 2)⁻¹ = (Lj ^ 2)⁻¹ * (η⁻¹) ^ 2 := by rw [mul_pow, mul_inv, inv_pow]
    rw [he, ← mul_assoc]
    have hp : (0:ℝ) < (η⁻¹) ^ 2 := by positivity
    constructor
    · intro h; nlinarith [h]
    · intro h; nlinarith [h]
  have key4 : ∀ (V : PeriodicLinkConfiguration SU2 L) (b : Bond L),
      (frobNorm (extDStarD η (chartA η V) b) < c * ((Lj * η) ^ 3)⁻¹ ↔
        frobNorm (extDStarD 1 (logField V) b) < c * (Lj ^ 3)⁻¹) := by
    intro V b
    rw [extDStarD_chartA_norm η hη V b]
    have he : ((Lj * η) ^ 3)⁻¹ = (Lj ^ 3)⁻¹ * (η⁻¹) ^ 3 := by rw [mul_pow, mul_inv, inv_pow]
    rw [he, ← mul_assoc]
    have hp : (0:ℝ) < (η⁻¹) ^ 3 := by positivity
    constructor
    · intro h; nlinarith [h]
    · intro h; nlinarith [h]
  constructor
  · rintro ⟨γ, hch, h1, h2, h3⟩
    exact ⟨γ, hch, fun b hb => (key1 _ b).mp (h1 b hb),
      fun b hb ν => (key2 _ b ν).mp (h2 b hb ν), fun b hb => (key4 _ b).mp (h3 b hb)⟩
  · rintro ⟨γ, hch, h1, h2, h3⟩
    exact ⟨γ, hch, fun b hb => (key1 _ b).mpr (h1 b hb),
      fun b hb ν => (key2 _ b ν).mpr (h2 b hb ν), fun b hb => (key4 _ b).mpr (h3 b hb)⟩


/-! ### §14a — NARROWNESS AGAINST THE FAITHFUL PREDICATE, with the constant COUNTED

`24 = 3 · 2 · 4`: three directions `ν` in the `∂^{η*}` sum, two terms in each backward
difference, four terms in each `∂^η` plaquette component. Composed with CMP98 (25)'s `π/2`
(`frobNorm_su2Log_le_pi_div_two`) the binding threshold is `24·(π/2) = 12π`, SIX TIMES the
proxy's `2π`. Nothing is tuned; the count is read off the definition. -/

theorem frobNorm_extD_one_le (A : Bond L → M2) (K : ℝ) (hK : ∀ b, frobNorm (A b) ≤ K)
    (x : PeriodicLatticeSite L) (μ ν : Fin 3) : frobNorm (extD 1 A x μ ν) ≤ 4 * K := by
  have h : extD 1 A x μ ν = A (periodicLatticeShift x μ, ν) - A (x, ν)
      - A (periodicLatticeShift x ν, μ) + A (x, μ) := by simp [extD]
  rw [h]
  have t1 := frobNorm_add_le (A (periodicLatticeShift x μ, ν) - A (x, ν)
    - A (periodicLatticeShift x ν, μ)) (A (x, μ))
  have t2 := frobNorm_sub_le (A (periodicLatticeShift x μ, ν) - A (x, ν))
    (A (periodicLatticeShift x ν, μ))
  have t3 := frobNorm_sub_le (A (periodicLatticeShift x μ, ν)) (A (x, ν))
  linarith [hK (periodicLatticeShift x μ, ν), hK (x, ν),
    hK (periodicLatticeShift x ν, μ), hK (x, μ)]

theorem frobNorm_extDStarD_one_le (A : Bond L → M2) (K : ℝ) (hK : ∀ b, frobNorm (A b) ≤ K)
    (b : Bond L) : frobNorm (extDStarD 1 A b) ≤ 24 * K := by
  have hexp : extDStarD 1 A b
      = (extD 1 A b.1 b.2 0 - extD 1 A (periodicLatticeShiftBack b.1 0) b.2 0)
      + (extD 1 A b.1 b.2 1 - extD 1 A (periodicLatticeShiftBack b.1 1) b.2 1)
      + (extD 1 A b.1 b.2 2 - extD 1 A (periodicLatticeShiftBack b.1 2) b.2 2) := by
    unfold extDStarD extDStar
    rw [Fin.sum_univ_three]
    simp
  rw [hexp]
  have e0 := frobNorm_extD_one_le A K hK b.1 b.2 0
  have e1 := frobNorm_extD_one_le A K hK b.1 b.2 1
  have e2 := frobNorm_extD_one_le A K hK b.1 b.2 2
  have f0 := frobNorm_extD_one_le A K hK (periodicLatticeShiftBack b.1 0) b.2 0
  have f1 := frobNorm_extD_one_le A K hK (periodicLatticeShiftBack b.1 1) b.2 1
  have f2 := frobNorm_extD_one_le A K hK (periodicLatticeShiftBack b.1 2) b.2 2
  have s0 := frobNorm_sub_le (extD 1 A b.1 b.2 0) (extD 1 A (periodicLatticeShiftBack b.1 0) b.2 0)
  have s1 := frobNorm_sub_le (extD 1 A b.1 b.2 1) (extD 1 A (periodicLatticeShiftBack b.1 1) b.2 1)
  have s2 := frobNorm_sub_le (extD 1 A b.1 b.2 2) (extD 1 A (periodicLatticeShiftBack b.1 2) b.2 2)
  have t1 := frobNorm_add_le
    ((extD 1 A b.1 b.2 0 - extD 1 A (periodicLatticeShiftBack b.1 0) b.2 0)
      + (extD 1 A b.1 b.2 1 - extD 1 A (periodicLatticeShiftBack b.1 1) b.2 1))
    (extD 1 A b.1 b.2 2 - extD 1 A (periodicLatticeShiftBack b.1 2) b.2 2)
  have t2 := frobNorm_add_le
    (extD 1 A b.1 b.2 0 - extD 1 A (periodicLatticeShiftBack b.1 0) b.2 0)
    (extD 1 A b.1 b.2 1 - extD 1 A (periodicLatticeShiftBack b.1 1) b.2 1)
  linarith

/-- **NARROWNESS, FAITHFUL VERSION.** Same shape as the proxy's, with the operator repaired and
the constant recounted: the threshold is `12π·α < c·Lj⁻³`, not `2π·α < c·Lj⁻³`. -/
theorem src3536FaithfulLog_of_gaugeRegular (Lj c α : ℝ) (U : PeriodicLinkConfiguration SU2 L)
    (hLj : 1 ≤ Lj) (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hthr : 12 * Real.pi * α < c * (Lj ^ 3)⁻¹)
    (hbranch : ∀ h : SU2, frobNorm ((h : M2) - 1) ≤ α → su2Exp (su2Log h) = h)
    (hreg : GaugeRegular α U) (cube : Finset (Bond L)) :
    Src3536FaithfulLog Lj c cube U := by
  obtain ⟨γ, hsup⟩ := hreg
  set V := periodicGaugeTransform γ U with hV
  have hb : ∀ b : Bond L, frobNorm ((V b : M2) - 1) ≤ α := fun b =>
    le_trans (frobNorm_le_frobSupBond V b) hsup
  have hlog : ∀ b : Bond L, frobNorm (su2Log (V b)) ≤ Real.pi / 2 * α := by
    intro b
    refine le_trans (frobNorm_su2Log_le_pi_div_two (V b)) ?_
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    nlinarith [hb b, frobNorm_nonneg ((V b : M2) - 1)]
  have hLj0 : (0:ℝ) < Lj := lt_of_lt_of_le zero_lt_one hLj
  have h31 : c * (Lj ^ 3)⁻¹ ≤ c * Lj⁻¹ := by
    have hi : (Lj ^ 3)⁻¹ ≤ Lj⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hLj0
        (by nlinarith [mul_nonneg (mul_nonneg hLj0.le hLj0.le) (sub_nonneg.mpr hLj)])
    exact mul_le_mul_of_nonneg_left hi hc
  have h32 : c * (Lj ^ 3)⁻¹ ≤ c * (Lj ^ 2)⁻¹ := by
    have hi : (Lj ^ 3)⁻¹ ≤ (Lj ^ 2)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity)
        (by nlinarith [mul_nonneg (mul_nonneg hLj0.le hLj0.le) (sub_nonneg.mpr hLj)])
    exact mul_le_mul_of_nonneg_left hi hc
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · exact fun b _ => hbranch (V b) (hb b)
  · intro b _
    have := hlog b
    nlinarith [hthr, h31]
  · intro b _ ν
    have h1 := hlog (shiftBond b ν)
    have h2 := hlog b
    have := frobNorm_sub_le (su2Log (V (shiftBond b ν))) (su2Log (V b))
    nlinarith [hthr, h32]
  · intro b _
    have hK : ∀ b' : Bond L, frobNorm (logField V b') ≤ Real.pi / 2 * α := hlog
    have := frobNorm_extDStarD_one_le (logField V) (Real.pi / 2 * α) hK b
    nlinarith [hthr]

/-! ### §14b — WIDENESS AT A CUBE OF THE PRINTED CLASS

The wide direction is the one the cube defect did NOT damage, because it turns only on the first
clause, which the proxy and the faithful predicate share. Restated here at a cube containing the
four bonds of one plaquette — no `Finset.univ`, no singleton. -/

theorem frobNorm_holonomy_le_of_bonds (V : PeriodicLinkConfiguration SU2 L)
    (p : PeriodicLatticePlaquette L) (K : ℝ)
    (h0 : frobNorm ((V (p.1, p.2.1.1) : M2) - 1) ≤ K)
    (h1 : frobNorm ((V (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : M2) - 1) ≤ K)
    (h2 : frobNorm ((V (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) : M2) - 1) ≤ K)
    (h3 : frobNorm ((V (p.1, p.2.1.2) : M2) - 1) ≤ K) :
    frobNorm ((holonomyElem V p : M2) - 1) ≤ 4 * K := by
  set a := V (p.1, p.2.1.1) with ha
  set bb := V (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) with hbb
  set cc := V (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) with hcc
  set d := V (p.1, p.2.1.2) with hd
  have hH : holonomyElem V p = a * bb * cc⁻¹ * d⁻¹ := rfl
  have t1 := frobNorm_su_mul_sub_one_le (a * bb * cc⁻¹) d⁻¹
  have t2 := frobNorm_su_mul_sub_one_le (a * bb) cc⁻¹
  have t3 := frobNorm_su_mul_sub_one_le a bb
  rw [frobNorm_su_inv_sub_one cc] at t2
  rw [frobNorm_su_inv_sub_one d] at t1
  rw [hH]
  linarith

/-- **WIDENESS AGAINST THE FAITHFUL PREDICATE, AT AN ARBITRARY CUBE CARRYING ONE PLAQUETTE.** -/
theorem not_src3536FaithfulLog_of_curvature_cube {Lj c : ℝ}
    {U : PeriodicLinkConfiguration SU2 L} (p : PeriodicLatticePlaquette L)
    (cube : Finset (Bond L))
    (hb0 : ((p.1, p.2.1.1) : Bond L) ∈ cube)
    (hb1 : ((periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : Bond L) ∈ cube)
    (hb2 : ((periodicLatticeShift p.1 p.2.1.2, p.2.1.1) : Bond L) ∈ cube)
    (hb3 : ((p.1, p.2.1.2) : Bond L) ∈ cube)
    (hbig : 4 * (c * Lj⁻¹) ≤ frobNorm ((holonomyElem U p : M2) - 1)) :
    ¬ Src3536FaithfulLog Lj c cube U := by
  rintro ⟨γ, hch, h1, -, -⟩
  set V := periodicGaugeTransform γ U with hV
  have hbnd : ∀ b ∈ cube, frobNorm ((V b : M2) - 1) < c * Lj⁻¹ := by
    intro b hb
    have hne := ne_negOne_of_chart (hch b hb)
    exact lt_of_le_of_lt (frobNorm_sub_one_le_frobNorm_su2Log _ hne) (h1 b hb)
  -- one strict bound covering all four bonds
  set K : ℝ := max (max (frobNorm ((V (p.1, p.2.1.1) : M2) - 1))
      (frobNorm ((V (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : M2) - 1)))
    (max (frobNorm ((V (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) : M2) - 1))
      (frobNorm ((V (p.1, p.2.1.2) : M2) - 1))) with hKdef
  have hKlt : K < c * Lj⁻¹ := by
    rw [hKdef]
    simp only [max_lt_iff]
    exact ⟨⟨hbnd _ hb0, hbnd _ hb1⟩, ⟨hbnd _ hb2, hbnd _ hb3⟩⟩
  have hfour := frobNorm_holonomy_le_of_bonds V p K
    (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_left (le_max_right _ _))
    (le_max_of_le_right (le_max_left _ _)) (le_max_of_le_right (le_max_right _ _))
  rw [holonomy_frob_gauge_inv U γ p] at hfour
  linarith


/-- The corner of the concrete printed cube: coordinate `1`, not `0`, so that the backward shifts
`∂^{η*}` performs from inside the cube stay inside `[0, 31]` without wrapping. -/
def bigOrigin : PeriodicLatticeSite bigLat := fun _ => 1

/-- A concrete cube of the printed class on `bigLat`: the box of side `10` at the origin. -/
def bigCube : Finset (Bond bigLat) := sourceCubeBonds bigOrigin 10

theorem bigCube_isSourceCube : IsSourceCube 1 bigCube :=
  ⟨bigOrigin, 10, rfl, le_rfl, by norm_num⟩

theorem bigOrigin_val (μ : Fin 3) : (bigOrigin μ).val = 1 := rfl

theorem mem_bigCube_of_origin (d : Fin 3) : ((bigOrigin, d) : Bond bigLat) ∈ bigCube := by
  rw [bigCube, mem_sourceCubeBonds]
  intro μ
  have hfst : ((bigOrigin, d) : Bond bigLat).1 = bigOrigin := rfl
  rw [hfst, bigOrigin_val]
  omega

theorem mem_bigCube_of_shift (μ0 d : Fin 3) :
    ((periodicLatticeShift bigOrigin μ0, d) : Bond bigLat) ∈ bigCube := by
  rw [bigCube, mem_sourceCubeBonds]
  intro μ
  have hfst : ((periodicLatticeShift bigOrigin μ0, d) : Bond bigLat).1
      = periodicLatticeShift bigOrigin μ0 := rfl
  rw [hfst, bigOrigin_val]
  have hx : 1 ≤ ((periodicLatticeShift bigOrigin μ0) μ).val ∧
      ((periodicLatticeShift bigOrigin μ0) μ).val ≤ 2 := by
    by_cases h : μ = μ0
    · subst h
      show 1 ≤ (Function.update bigOrigin μ (bigOrigin μ + 1) μ).val ∧
        (Function.update bigOrigin μ (bigOrigin μ + 1) μ).val ≤ 2
      rw [Function.update_self]
      show 1 ≤ ((1 : Fin (bigLat μ + 1)) + 1).val ∧ ((1 : Fin (bigLat μ + 1)) + 1).val ≤ 2
      unfold bigLat
      decide
    · show 1 ≤ (Function.update bigOrigin μ0 (bigOrigin μ0 + 1) μ).val ∧
        (Function.update bigOrigin μ0 (bigOrigin μ0 + 1) μ).val ≤ 2
      rw [Function.update_of_ne h, bigOrigin_val]
      omega
  omega

/-- **THE WIDE WITNESS, ON A CUBE OF THE PRINTED CLASS, UNCONDITIONALLY.** No cube is assumed and
no group element is assumed: the cube is a genuine `IsSourceCube` (side `10 ≥ 10·Lj` at `Lj = 1`,
on the side-`16` lattice `bigLat`), and `g` is built by `exists_su2_frobNorm_sub_one_eq`.

This is the one direction the conviction's cube defect did NOT damage; it is restated here at a
cube that is actually in the class, so that the restatement is checkable rather than asserted. -/
theorem exists_faithfulWideness_witness_onSourceCube (c α : ℝ) (hα0 : 0 ≤ α)
    (hα2 : α ≤ 2 * Real.sqrt 2) (hband : 4 * c ≤ α) :
    ∃ (cube : Finset (Bond bigLat)) (U : PeriodicLinkConfiguration SU2 bigLat),
      IsSourceCube 1 cube ∧ GaugeRegular α U ∧ ¬ Src3536FaithfulLog 1 c cube U := by
  classical
  set p : PeriodicLatticePlaquette bigLat :=
    (bigOrigin, (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) with hp
  obtain ⟨g, hg⟩ := exists_su2_frobNorm_sub_one_eq α hα0 hα2
  have hp1 : p.1 = bigOrigin := rfl
  have hpμ : p.2.1.1 = (0 : Fin 3) := rfl
  have hpν : p.2.1.2 = (1 : Fin 3) := rfl
  refine ⟨bigCube, oneBondU (p.1, p.2.1.1) g, bigCube_isSourceCube, ?_, ?_⟩
  · exact gaugeRegular_of_frobSupBond_le
      (le_of_le_of_eq (frobSupBond_oneBondU (p.1, p.2.1.1) g) hg)
  · have hshift : periodicLatticeShift p.1 p.2.1.2 ≠ p.1 :=
      shift_ne_self bigOrigin 1 (by unfold bigLat; omega)
    have hhol : holonomyElem (oneBondU (p.1, p.2.1.1) g) p = g := holonomy_oneBondU p g hshift
    refine not_src3536FaithfulLog_of_curvature_cube p bigCube ?_ ?_ ?_ ?_ ?_
    · rw [hp1, hpμ]; exact mem_bigCube_of_origin 0
    · rw [hp1, hpμ, hpν]; exact mem_bigCube_of_shift 0 1
    · rw [hp1, hpμ, hpν]; exact mem_bigCube_of_shift 1 0
    · rw [hp1, hpν]; exact mem_bigCube_of_origin 1
    · rw [hhol, hg]
      simpa using hband


/-! ## §14c — THE REGION WITNESS AT A CUBE OF THE PRINTED CLASS -/

/-- The excited site: coordinate `13` in every direction. The clauses of `Src3536FaithfulLog` on
`bigCube` read only sites with every coordinate `≤ 11`, so they never see it. -/
def farSite : PeriodicLatticeSite bigLat := fun _ => 13

def farBond : Bond bigLat := (farSite, 0)

/-- Sites the cube's own clauses can read. -/
def Band11 (x : PeriodicLatticeSite bigLat) : Prop := ∀ μ : Fin 3, (x μ).val ≤ 11

/-- Sites one forward shift away from `Band11`. -/
def Band10 (x : PeriodicLatticeSite bigLat) : Prop := ∀ μ : Fin 3, (x μ).val ≤ 10

/-- The cube's own sites: coordinates `1..10`. -/
def InCube (x : PeriodicLatticeSite bigLat) : Prop :=
  ∀ μ : Fin 3, 1 ≤ (x μ).val ∧ (x μ).val ≤ 10

theorem inCube_of_mem_bigCube {b : Bond bigLat} (hb : b ∈ bigCube) : InCube b.1 := by
  rw [bigCube, mem_sourceCubeBonds] at hb
  intro μ
  have := hb μ
  rw [bigOrigin_val] at this
  omega

/-- `(a + 1).val = a.val + 1` on `Fin 16` below the top. -/
theorem val_add_one_of_le {μ : Fin 3} {a : Fin (bigLat μ + 1)} (h : a.val ≤ 10) :
    (a + 1).val = a.val + 1 := by
  have hlt : a < Fin.last (bigLat μ) := by
    rw [Fin.lt_def]
    show a.val < (Fin.last (bigLat μ)).val
    rw [Fin.val_last]
    unfold bigLat
    omega
  exact Fin.val_add_one_of_lt hlt

theorem val_sub_one_of_pos {μ : Fin 3} {a : Fin (bigLat μ + 1)} (h : 1 ≤ a.val) :
    (a - 1).val = a.val - 1 := by
  have hne : a ≠ 0 := by
    intro hc
    rw [hc] at h
    simp at h
  rw [Fin.coe_sub_one, if_neg hne]

theorem band11_of_band10 {x : PeriodicLatticeSite bigLat} (h : Band10 x) : Band11 x :=
  fun μ => by have := h μ; omega

theorem band10_of_inCube {x : PeriodicLatticeSite bigLat} (h : InCube x) : Band10 x :=
  fun μ => (h μ).2

theorem band11_shift_of_band10 {x : PeriodicLatticeSite bigLat} (h : Band10 x) (μ0 : Fin 3) :
    Band11 (periodicLatticeShift x μ0) := by
  intro μ
  by_cases hμ : μ = μ0
  · subst hμ
    show (Function.update x μ (x μ + 1) μ).val ≤ 11
    rw [Function.update_self, val_add_one_of_le (h μ)]
    have := h μ; omega
  · show (Function.update x μ0 (x μ0 + 1) μ).val ≤ 11
    rw [Function.update_of_ne hμ]
    have := h μ; omega

theorem band10_shiftBack_of_inCube {x : PeriodicLatticeSite bigLat} (h : InCube x) (μ0 : Fin 3) :
    Band10 (periodicLatticeShiftBack x μ0) := by
  intro μ
  by_cases hμ : μ = μ0
  · subst hμ
    show (Function.update x μ (x μ - 1) μ).val ≤ 10
    rw [Function.update_self, val_sub_one_of_pos (h μ).1]
    have := h μ; omega
  · show (Function.update x μ0 (x μ0 - 1) μ).val ≤ 10
    rw [Function.update_of_ne hμ]
    exact (h μ).2

theorem not_band11_farSite : ¬ Band11 farSite := by
  intro h
  have h0 : (farSite 0).val ≤ 11 := h 0
  have hv : (farSite 0).val = 13 := rfl
  omega

theorem ne_farBond_of_band11 {x : PeriodicLatticeSite bigLat} (h : Band11 x) (d : Fin 3) :
    ((x, d) : Bond bigLat) ≠ farBond := by
  intro hc
  have hx : x = farSite := congrArg Prod.fst hc
  rw [hx] at h
  exact not_band11_farSite h


/-- **THE REGION CONFIGURATION**: `1` everywhere except the single far bond, where it is `−1`. -/
noncomputable def regionU : PeriodicLinkConfiguration SU2 bigLat := oneBondU farBond su2NegOne

theorem regionU_eq_one_of_band11 {x : PeriodicLatticeSite bigLat} (h : Band11 x) (d : Fin 3) :
    regionU ((x, d) : Bond bigLat) = 1 :=
  oneBondU_apply_of_ne (ne_farBond_of_band11 h d)

theorem logField_regionU_of_band11 {x : PeriodicLatticeSite bigLat} (h : Band11 x) (d : Fin 3) :
    logField regionU ((x, d) : Bond bigLat) = 0 := by
  unfold logField
  rw [regionU_eq_one_of_band11 h d, su2Log_one]

theorem extD_regionU_zero {x : PeriodicLatticeSite bigLat} (hx : Band10 x) (μ ν : Fin 3) :
    extD 1 (logField regionU) x μ ν = 0 := by
  unfold extD
  rw [logField_regionU_of_band11 (band11_shift_of_band10 hx μ) ν,
    logField_regionU_of_band11 (band11_of_band10 hx) ν,
    logField_regionU_of_band11 (band11_shift_of_band10 hx ν) μ,
    logField_regionU_of_band11 (band11_of_band10 hx) μ]
  simp

theorem extDStarD_regionU_zero {b : Bond bigLat} (hb : InCube b.1) :
    extDStarD 1 (logField regionU) b = 0 := by
  unfold extDStarD extDStar
  refine Finset.sum_eq_zero fun ν _ => ?_
  simp only []
  rw [extD_regionU_zero (band10_of_inCube hb) b.2 ν,
    extD_regionU_zero (band10_shiftBack_of_inCube hb ν) b.2 ν]
  simp

/-- **THE REGION WITNESS, AT A CUBE OF THE PRINTED CLASS.** The source's own sentence
*"these regularity conditions do not impose any constraints on `U` outside the domain `Ω₀`"*,
formalized without a singleton: `bigCube` is a genuine `IsSourceCube` of side `10`, the
configuration satisfies the faithful (3.35)∧(3.36) on it at EVERY positive `c`, and it fails
`GaugeRegular α` because a plaquette four cells away carries the maximal curvature `2√2`.

This closes the leg the singleton cube left open, and it needed the exterior operator to be
built first: `∂^{η*}` reaches BACKWARD out of the cube, which is why `bigCube` is based at
coordinate `1` rather than `0`. -/
theorem exists_faithfulRegion_witness_onSourceCube (c α : ℝ) (hc : 0 < c)
    (hα : 4 * α < 2 * Real.sqrt 2) :
    ∃ (cube : Finset (Bond bigLat)) (U : PeriodicLinkConfiguration SU2 bigLat),
      IsSourceCube 1 cube ∧ Src3536FaithfulLog 1 c cube U ∧ ¬ GaugeRegular α U := by
  have hgt : periodicGaugeTransform (fun _ => (1 : SU2)) regionU = regionU :=
    AdalyFormal.Balaban.AlphaAnalyticity.gaugeTransform_one regionU
  refine ⟨bigCube, regionU, bigCube_isSourceCube, ?_, ?_⟩
  · refine ⟨fun _ => 1, ?_, ?_, ?_, ?_⟩
    · intro b hb
      rw [hgt]
      have h1 : regionU b = 1 :=
        regionU_eq_one_of_band11
          (band11_of_band10 (band10_of_inCube (inCube_of_mem_bigCube hb))) b.2
      rw [h1, su2Log_one, su2Exp_zero]
    · intro b hb
      rw [hgt]
      have h1 : regionU b = 1 :=
        regionU_eq_one_of_band11
          (band11_of_band10 (band10_of_inCube (inCube_of_mem_bigCube hb))) b.2
      rw [h1, su2Log_one, frobNorm_zero]
      simpa using hc
    · intro b hb ν
      rw [hgt]
      have hcube := inCube_of_mem_bigCube hb
      have h1 : regionU b = 1 :=
        regionU_eq_one_of_band11 (band11_of_band10 (band10_of_inCube hcube)) b.2
      have h2 : regionU (shiftBond b ν) = 1 :=
        regionU_eq_one_of_band11 (band11_shift_of_band10 (band10_of_inCube hcube) ν) b.2
      rw [h1, h2, su2Log_one, sub_self, frobNorm_zero]
      simpa using hc
    · intro b hb
      rw [hgt, extDStarD_regionU_zero (inCube_of_mem_bigCube hb), frobNorm_zero]
      simpa using hc
  · rintro ⟨γ, hγ⟩
    have hshift : periodicLatticeShift
        (((farSite, (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) :
          PeriodicLatticePlaquette bigLat)).1
        (((farSite, (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) :
          PeriodicLatticePlaquette bigLat)).2.1.2
        ≠ (((farSite, (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) :
          PeriodicLatticePlaquette bigLat)).1 :=
      shift_ne_self farSite 1 (by unfold bigLat; omega)
    have hhol : holonomyElem regionU
        ((farSite, (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) :
          PeriodicLatticePlaquette bigLat) = su2NegOne :=
      holonomy_oneBondU _ su2NegOne hshift
    have hfloor := curvature_floor regionU γ
      ((farSite, (⟨(0, 1), by decide⟩ : PeriodicPlaquetteDirections)) :
        PeriodicLatticePlaquette bigLat)
    rw [hhol, frobNorm_negOne_sub_one] at hfloor
    linarith


/-! ## §14d — THE `∀`-OVER-THE-CLASS FORM, which is the shape the source's sentence has

p.396 says *"for an arbitrary cube `□` of the described above class ... there exists a gauge
transformation `u` on `□`"*. The quantifier order is `∀ □ ∈ class, ∃ u`, and the `∀` is what the
per-cube predicates above leave to the consumer. Supplying it here is not cosmetic: it is what
removes the EMPTY-CUBE COLLAPSE, because `∅` is not in the class (`empty_not_isSourceCube`), and
what makes the wide witness negate a statement rather than an instance. -/

/-- **The source's condition in its printed quantifier shape.** -/
def Src3536FaithfulAll (η Lj c : ℝ) (U : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ cube : Finset (Bond L), IsSourceCube Lj cube → Src3536Faithful η Lj c cube U

/-- The same, `η`-free. -/
def Src3536FaithfulAllLog (Lj c : ℝ) (U : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ cube : Finset (Bond L), IsSourceCube Lj cube → Src3536FaithfulLog Lj c cube U

theorem src3536FaithfulAll_eta_free (η Lj c : ℝ) (hη : 0 < η)
    (U : PeriodicLinkConfiguration SU2 L) :
    Src3536FaithfulAll η Lj c U ↔ Src3536FaithfulAllLog Lj c U := by
  constructor
  · intro h cube hcube
    exact (src3536Faithful_eta_free η Lj c hη cube U).mp (h cube hcube)
  · intro h cube hcube
    exact (src3536Faithful_eta_free η Lj c hη cube U).mpr (h cube hcube)

/-- **NARROWNESS IN THE `∀`-FORM.** Immediate from the per-cube theorem, and it is the form a
consumer should cite: `12π·α < c·Lj⁻³ ⟹ GaugeRegular α ⊆ (the class, quantified as printed)`. -/
theorem src3536FaithfulAllLog_of_gaugeRegular (Lj c α : ℝ) (U : PeriodicLinkConfiguration SU2 L)
    (hLj : 1 ≤ Lj) (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hthr : 12 * Real.pi * α < c * (Lj ^ 3)⁻¹)
    (hbranch : ∀ h : SU2, frobNorm ((h : M2) - 1) ≤ α → su2Exp (su2Log h) = h)
    (hreg : GaugeRegular α U) :
    Src3536FaithfulAllLog Lj c U :=
  fun cube _ => src3536FaithfulLog_of_gaugeRegular Lj c α U hLj hα hc hthr hbranch hreg cube

/-- **THE EMPTY-CUBE COLLAPSE IS GONE FROM THE `∀`-FORM.** `Src3536FaithfulLog Lj c ∅ U` holds for
every `U` (all four obligations are vacuous), so the per-cube predicate is degenerate at `∅`. The
`∀`-form is not: `∅` is not in the class, and the class is nonempty, so the statement has real
content at a real cube. Both facts are theorems, not remarks. -/
theorem src3536FaithfulLog_empty_collapse (Lj c : ℝ) (U : PeriodicLinkConfiguration SU2 L) :
    Src3536FaithfulLog Lj c (∅ : Finset (Bond L)) U :=
  ⟨fun _ => 1, fun b hb => absurd hb (Finset.notMem_empty b),
    fun b hb => absurd hb (Finset.notMem_empty b),
    fun b hb => absurd hb (Finset.notMem_empty b),
    fun b hb => absurd hb (Finset.notMem_empty b)⟩

/-- **THE WIDE WITNESS NEGATES THE `∀`-FORM**, which is what a witness has to do. -/
theorem not_src3536FaithfulAllLog_wideness (c α : ℝ) (hα0 : 0 ≤ α)
    (hα2 : α ≤ 2 * Real.sqrt 2) (hband : 4 * c ≤ α) :
    ∃ U : PeriodicLinkConfiguration SU2 bigLat,
      GaugeRegular α U ∧ ¬ Src3536FaithfulAllLog 1 c U := by
  obtain ⟨cube, U, hcube, hreg, hnot⟩ :=
    exists_faithfulWideness_witness_onSourceCube c α hα0 hα2 hband
  exact ⟨U, hreg, fun hall => hnot (hall cube hcube)⟩

#print axioms src3536FaithfulAll_eta_free
#print axioms src3536FaithfulAllLog_of_gaugeRegular
#print axioms src3536FaithfulLog_empty_collapse
#print axioms not_src3536FaithfulAllLog_wideness

/-! ## §15b — MUST-NOT-FIRE CONTROLS

A gate that cannot fail is not a gate. Two of the repairs above are load-bearing, and each is
paired here with a kernel-checked statement showing what breaks if it is removed. -/

/-- **CONTROL for `coordSecondDiff_ne_extDStarD`.** The separation statement is FALSE if the SAME
operator is put on both sides: no `A` has all its coordinatewise second differences zero at `b`
while one of them is nonzero. So the separation is carried by the two operators being DIFFERENT and
by nothing else — it is not an artifact of the shape of the statement. -/
theorem coordSecondDiff_separation_control :
    ¬ ∃ (A : Bond sepLat → M2) (b : Bond sepLat),
      (∀ ν : Fin 3, coordSecondDiff A b ν = 0) ∧ coordSecondDiff A b 0 ≠ 0 := by
  rintro ⟨A, b, h0, hne⟩
  exact hne (h0 0)

/-- **CONTROL for the side floor in `IsSourceCube`.** At side `0` the box carries NO bonds. So a
cube class without the floor `10·Lj ≤ s` would admit `∅`, and `empty_not_isSourceCube` would be
false: the floor is exactly what blocks the collapse, and dropping it is observable. -/
theorem sourceCubeBonds_zero_eq_empty (y : PeriodicLatticeSite L) :
    sourceCubeBonds y 0 = (∅ : Finset (Bond L)) := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro b hb
  rw [mem_sourceCubeBonds] at hb
  have := hb 0
  omega

/-- The other half of the same control: at side `1` the box is NONEMPTY, so the emptiness above is
about the side, not about `sourceCubeBonds` being degenerate. -/
theorem sourceCubeBonds_one_nonempty (y : PeriodicLatticeSite L) :
    (sourceCubeBonds y 1).Nonempty :=
  ⟨(y, 0), mem_sourceCubeBonds_base le_rfl 0⟩

#print axioms coordSecondDiff_separation_control
#print axioms sourceCubeBonds_zero_eq_empty
#print axioms sourceCubeBonds_one_nonempty

/-! ## §16 — SCOPE OF §12-§14c, STATED BEFORE THE PROSECUTOR ASKS

**`IsSourceCube` is a RELAXATION of the printed class, not the printed class.** It carries what
p.396 fixes about the SHAPE and the SIZE of `□` — a coordinate box, side `s` with `10·Lj ≤ s` at
`1 ≤ Lj`, from *"`O(1)M` is a size of `□` in `T_{L^{-j}}`"* together with *"`O(1)` will mean a
number `≥ 10`"* and ~~`M ≥ 1`~~ — **STRUCK 2026-08-05, retained struck (S75):** the source's only
printed inequality on `M` is Theorem 3.1's `M ≥ M_1`, `M_1` UNSPECIFIED (*"sufficiently large"*,
CMP96 p.232); a bare `M ≥ 1` UNDERSTATES it (`compute/cube_convention/ADJUDICATION.md`, ledger
`CUBE-CONVENTION-BOX-FORCED-AT-P408`). It does **not** carry the four clauses that further RESTRICT
the class: the unique index `j`; membership in `B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1})`; nonempty intersection
with `B^j(Λ_j)`; and the exact size `O(1)ML^jη` rather than a floor. Those need the domain sequence
(`Balaban/DomainSequence.lean` has `LambdaKDomain`; it is not imported here).

**UPDATED 2026-08-05 (`compute/formal_batch/`).** ~~"Those need the domain sequence … not imported
here"~~ is no longer the whole story, and the sentence is kept above only as the record of what §16
said when it was written. **§17 of THIS FILE now builds that domain-sequence layer** on this very
carrier — `DomainTower` (`{Ω_j}`, (2.1)'s nesting, (2.2)'s coarse alignment), its derived `Λ_j` and
shells `B^j(Λ_j)`, and `PrintedOmegaData`, which carries p.396's THREE clauses at the printed index
together with the printed three-clause uniqueness. What §16 says about `IsSourceCube` ITSELF is
unchanged and still true: `IsSourceCube` is the relaxation, §12-§14c are stated against it, and
§17's class (`PrintedCube` + `PrintedOmegaData.Class`) is a SEPARATE, additive object that no
§12-§14c theorem consumes. The non-benign direction remains UNSETTLED.

So the intended set relation is `printed class ⊆ IsSourceCube`, strictly. **That makes the three
results asymmetric, and the asymmetry is the whole scope statement:**

| result | quantifier over cubes | does it settle a containment against the SOURCE? |
|---|---|---|
| `src3536FaithfulLog_of_gaugeRegular` / `src3536FaithfulAllLog_of_gaugeRegular` | proved for **EVERY** `cube`, hence for the `∀`-form | **YES.** A superset quantifier covers every printed cube. `12π·α < c·Lj⁻³ ⟹ GaugeRegular α ⊆ (3.35)∧(3.36)`, now with the exterior operator. This is the benign direction and it is repaired. |
| `exists_faithfulWideness_witness_onSourceCube`, `not_src3536FaithfulAllLog_wideness` | fails the conditions at **ONE** `IsSourceCube` box, hence negates the `∀`-form over `IsSourceCube` | **NO.** The source's `∀` runs over the PRINTED class, a SUBSET; failing at one box of a superset does not negate a `∀` over the subset, because that box need not be printed. |
| `exists_faithfulRegion_witness_onSourceCube` | satisfies the conditions at **ONE** `IsSourceCube` box | **NO.** Membership in the source's class needs the conditions at EVERY printed cube; `regionU` fails them at boxes near `farSite`. |

**On the empty-cube collapse.** `src3536FaithfulLog_empty_collapse` proves that the PER-CUBE
predicate is still degenerate at `cube = ∅` — inherited from the source's own per-cube phrasing, and
stated rather than hidden. The `∀`-form `Src3536FaithfulAllLog` is not degenerate there:
`empty_not_isSourceCube` keeps `∅` out of the class and `exists_isSourceCube` keeps the class
inhabited. **A consumer should cite the `∀`-form.** The per-cube predicates are retained because the
witnesses and the narrow theorem are naturally stated at a cube.

**Therefore §12-§14c do NOT re-establish "the classes are incomparable".** They establish the
benign containment against a faithful operator, and they replace two singleton/`univ` constructions
with constructions at boxes of the modelled class — which is strictly more than was there, and
strictly less than a settlement. **The non-benign direction is UNSETTLED.**

What would settle it: carry the domain-sequence clauses into `IsSourceCube` (so that the modelled
class is contained in, not containing, the printed one) for the wide direction; and for the region
direction, a `∀`-quantified membership statement, i.e. a configuration satisfying the conditions on
every printed cube while admitting no single global gauge — an obstruction, not a construction.

Two further stated limits, neither hidden:
* both witnesses are at `Lj = 1` on the concrete lattice `bigLat` (side `16`), because the box side
  must be at least `10·Lj` and must leave a margin for `∂^{η*}`'s backward reach. Nothing in
  `not_src3536FaithfulLog_of_curvature_cube` or `src3536FaithfulLog_of_gaugeRegular` is specialized
  to `Lj = 1`; only the two `∃`-witnesses are.
* `24 = 3·2·4` is an UPPER bound on the term count of `extDStarD`, not the sharp one: the `ν = μ`
  summand vanishes (`extD_self`), so `16` is attainable. `24` is used because it is read directly
  off the definition without a case split. A larger constant makes the narrow threshold HARDER to
  meet, so this is the conservative direction for a `⊆` claim. -/

/-! ## §15 — axiom audit for §12-§14 -/

#print axioms extD_antisymm
#print axioms extD_self
#print axioms pairM_sub_left
#print axioms pairM_add_left
#print axioms pairM_smul_left
#print axioms pairM_sub_right
#print axioms pairM_neg_right
#print axioms pairM_smul_right
#print axioms pairM_sum_right
#print axioms sum_shift
#print axioms extD_adjoint
#print axioms coordLapA_eq_stencil
#print axioms sepA_of_dir_ne
#print axioms sepA_of_site_ne
#print axioms shiftBond_snd
#print axioms sep_coordSecondDiff_zero
#print axioms shiftBack_ne_self
#print axioms shift_shiftBack_ne_self
#print axioms extD_sepA_dirZero
#print axioms sep_extDStarD_ne_zero
#print axioms coordSecondDiff_ne_extDStarD
#print axioms mem_sourceCubeBonds
#print axioms ten_le_of_isSourceCube
#print axioms mem_sourceCubeBonds_base
#print axioms nonempty_of_isSourceCube
#print axioms empty_not_isSourceCube
#print axioms singleton_not_isSourceCube
#print axioms exists_isSourceCube
#print axioms chartA_eq_smul_logField
#print axioms extD_smul
#print axioms extDStar_smul
#print axioms extD_eta
#print axioms extDStar_eta
#print axioms extDStarD_smul
#print axioms extDStarD_eta
#print axioms extDStarD_chartA
#print axioms src3536Faithful_eta_free
#print axioms frobNorm_extD_one_le
#print axioms frobNorm_extDStarD_one_le
#print axioms src3536FaithfulLog_of_gaugeRegular
#print axioms frobNorm_holonomy_le_of_bonds
#print axioms not_src3536FaithfulLog_of_curvature_cube
#print axioms bigCube_isSourceCube
#print axioms bigOrigin_val
#print axioms mem_bigCube_of_origin
#print axioms mem_bigCube_of_shift
#print axioms exists_faithfulWideness_witness_onSourceCube
#print axioms inCube_of_mem_bigCube
#print axioms val_add_one_of_le
#print axioms val_sub_one_of_pos
#print axioms band11_of_band10
#print axioms band10_of_inCube
#print axioms band11_shift_of_band10
#print axioms band10_shiftBack_of_inCube
#print axioms not_band11_farSite
#print axioms ne_farBond_of_band11
#print axioms regionU_eq_one_of_band11
#print axioms logField_regionU_of_band11
#print axioms extD_regionU_zero
#print axioms extDStarD_regionU_zero
#print axioms exists_faithfulRegion_witness_onSourceCube


/-! §17 needs two further names from `AdmissibleSubspace` that §0-§16 do not open. -/
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)

/-! ## §17 — THE Ω-DATA LAYER: p.396's DOMAIN SEQUENCE, ITS CUBE CLASS, AND THE PRINTED INDEX

`corpus/pages/CMP99b_p396.md` (`verification_status: adjudicated`; render
`corpus/renders/CMP99b_p396-08.png`, sha256
`d0f0d665232fc871e005f2e721ea338e96c1a52763e151c3966bf7fcb47568ec`), the sentence that INTRODUCES
the class, VERBATIM and complete:

> *"Now we will introduce the regularity conditions for gauge field configurations `U`.  They
> depend on the sequence of domains `{Ω_j}`.  At first let us introduce a class of cubes.  For each
> cube `□` of this class there exists a unique index `j`, `0 ≤ j ≤ k`, such that
> `□ ⊂ B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1})`, `□ ∩ B^j(Λ_j) ≠ ∅`, and `□` is a union of several big blocks
> of the lattice `T_{L^{-j}}`, which implies that its size in the lattice `T_η` is `O(1) M L^j η`.
> Here `O(1)` will mean a number `≥ 10`.  The set `Λ_0` in the above condition means
> `Λ_0 = Ω_0 ∖ Ω_1`, where `Ω_0 = {`a union of big blocks of the lattice `T_1`, such that their
> distances to `Ω_1` are `≤ RM}`."*

THE SENTENCE HAS **THREE** PROPERTIES AND ONE UNIQUENESS SCOPE.  Read off the printed text, at the
index `j`:

* **(P1)** `□ ⊂ B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1})`;
* **(P2)** `□ ∩ B^j(Λ_j) ≠ ∅`;
* **(P3)** `□` is a union of several big blocks of `T_{L^{-j}}`;

and the index is unique **among the `j ∈ [0,k]` satisfying ALL THREE** — the printed quantifier is
*"there exists a unique index `j`, `0 ≤ j ≤ k`, such that (P1), (P2), and (P3)"*, one `such that`
governing the three conjuncts.

`Λ_j` and `B^j` are CMP96 (2.3)/(2.2), re-quoted at
`Balaban/DomainSequence.lean`'s header from `compute/domain_sequence_spec/renders/CMP96_p224-02.png`
(sha256 `f9aa9408ae14fd5f564f22b7989efeb51b38ab4a628ebb3256abea5f29fbe877`), VERBATIM:

> *"`Ω_1 ⊃ Ω_2 ⊃ … ⊃ Ω_k, Ω_j ⊂ T_η, j = 1,2,…,k,`* **(2.1)**, *which satisfy:*
> *`Ω_j = B^j(Ω_j^{(j)})`, `Ω_j^{(j)} ⊂ T_{L^jη}^{(j)}` "and it is a sum of big blocks", …* **(2.2)**.
> *`Λ_j = Ω_j^{(j)} ∖ Ω_{j+1}^{(j)}, j=1,…,k−1, Λ_k = Ω_k^{(k)}, Λ_0 = Ω_1^c`* **(2.3)**.
> *`Ω_1 = ⋃_{j=1}^k B^j(Λ_j), T = ⋃_{j=0}^k B^j(Λ_j)`, where `B^0(Λ_0) = Λ_0`.* **(2.4)**"

### WHAT THIS SECTION ADDS, AND WHAT IT DELIBERATELY DOES NOT

**ADDS.**  The domain-sequence layer §16 named as missing: `DomainTower` (the `{Ω_j}` sequence with
(2.1)'s nesting and (2.2)'s coarse-alignment, carried at the `PeriodicLatticeSite` carrier),
its derived `Lam` = (2.3)'s `Λ_j` and `Shell` = `B^j(Λ_j)`, and `PrintedOmegaData` — the cube class
with (P1),(P2),(P3) AT the printed index and the printed THREE-clause uniqueness.

**DOES NOT.**  No RG-flow instance is attempted: nothing here derives `{Ω_j}` from a renormalization
step, and the structure is DATA a caller supplies, exactly as `{Ω_j}` is data in the source.  Two
instances are supplied — one degenerate (constant index, the honest measurement of what a free
parameter buys) and one non-degenerate (two genuinely nested domains, a two-valued index map, both
cubes' printed indices PROVED unique).
-/

/-! ### §17a — THE INTERIOR CARRIER: THE FIT-CARRYING CONSTRUCTOR AND ITS COUNT

**WHY THIS EXISTS (the truncation root).**  `sourceCubeBonds y s` filters on
`AdmissibleSubspace.inBlock`, a NON-WRAPPING half-open coordinate interval `[y_μ, y_μ + s)`
intersected with the finite extent, and `IsSourceCube` never requires that interval to FIT.  On a
lattice of side `8` the corner site `7` at nominal side `10` therefore TRUNCATES to a single site,
so a three-bond set is `IsSourceCube` at nominal side `10` AND at nominal side `20`
(`compute/sol_wire3/scratch/BoundaryBondProbe.lean`, axiom-clean; disclosed in
`compute/curved_leg_wire/CurvedLegWire.lean` §2b).  The fit clause is what makes any count exact.

**AND THE CARRIER RULING.**  `compute/carrier_adjudication/ADJUDICATION.md`
(ledger `CARRIER-RULED-INTERNAL-BONDS`) adjudicates which bonds *"on `□`"* ranges over in
(3.35)/(3.36): **INTERNAL** — both endpoints in the box — because p.396 constructs `A` through
*"a gauge transformation `u` on `□`"* with `U^u = e^{iηA}`, and p.395's own formula
`U^u(x,x') = u(x)U(x,x')u^{-1}(x')` needs `u` at BOTH endpoints.  `interiorCubeBondsF` below is that
carrier; it is definitionally the same body as `CurvedLegWire.interiorCubeBonds`, which is where the
convention was first built and where the count lemmas ported below were first proved (credit: the
wire lane; `formal/` cannot import `compute/`, so they are ported, not re-invented).

`sourceCubeBonds` is NOT removed and NOT changed: it is the BASE-SITE set, an implementation object
with an exact count of its own, and every existing importer keeps the identical declaration.
-/

/-- **THE FAITHFUL CUBE CARRIER** — the bonds with BOTH endpoints in the coordinate box.
Definitionally `(sourceCubeBonds y s).filter (both endpoints in the box)`; the same body as
`CurvedLegWire.interiorCubeBonds`, ported here so the root module carries the adjudicated carrier.
The trailing `F` records that this is the FIT-carrying/faithful constructor of §17, distinguishing
it from the base-site `sourceCubeBonds` above, which is retained unchanged. -/
def interiorCubeBondsF (y : PeriodicLatticeSite L) (s : ℕ) : Finset (Bond L) :=
  (sourceCubeBonds y s).filter (fun b => inBlock y s (periodicLatticeShift b.1 b.2))

theorem mem_interiorCubeBondsF {y : PeriodicLatticeSite L} {s : ℕ} {b : Bond L} :
    b ∈ interiorCubeBondsF y s ↔
      inBlock y s b.1 ∧ inBlock y s (periodicLatticeShift b.1 b.2) := by
  classical
  simp [interiorCubeBondsF, mem_sourceCubeBonds]

/-- The interior carrier sits inside the base-site one. -/
theorem interiorCubeBondsF_subset (y : PeriodicLatticeSite L) (s : ℕ) :
    interiorCubeBondsF y s ⊆ sourceCubeBonds y s :=
  Finset.filter_subset _ _

/-- One coordinate direction: a half-open interval that FITS has exactly `s` sites. -/
theorem coord_interval_card {n : ℕ} (a s : ℕ) (h : a + s ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun z => a ≤ z.val ∧ z.val < a + s)).card = s := by
  classical
  have himg :
      ((Finset.univ : Finset (Fin n)).filter (fun z => a ≤ z.val ∧ z.val < a + s)).image Fin.val
        = Finset.Ico a (a + s) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨m, by omega⟩, ⟨h1, h2⟩, rfl⟩
  have hc := Finset.card_image_of_injective
    ((Finset.univ : Finset (Fin n)).filter (fun z => a ≤ z.val ∧ z.val < a + s))
    (Fin.val_injective (n := n))
  rw [himg, Nat.card_Ico] at hc
  omega

/-- **p.408's SIZE-TO-CELL-COUNT RELATION, AS A THEOREM (`d = 3`).**  A FITTED box of side `s`
contains exactly `s³` sites — the printed *"union of `(2+2n)^d` big blocks"* relation at the level
of CELLS, which is the level p.408 actually prints
(`corpus/pages/CMP99b_p408.md`, adjudicated; ledger `CUBE-CONVENTION-BOX-FORCED-AT-P408`).
Without the fit clause this is FALSE. -/
theorem block_card_of_fit (y : PeriodicLatticeSite L) (s : ℕ)
    (hfit : ∀ μ : Fin 3, (y μ).val + s ≤ L μ + 1) :
    ((Finset.univ : Finset (PeriodicLatticeSite L)).filter (inBlock y s)).card = s ^ 3 := by
  classical
  have hset : ((Finset.univ : Finset (PeriodicLatticeSite L)).filter (inBlock y s))
      = Fintype.piFinset (fun μ : Fin 3 =>
          (Finset.univ : Finset (Fin (L μ + 1))).filter
            (fun z => (y μ).val ≤ z.val ∧ z.val < (y μ).val + s)) := by
    ext x
    simp [Fintype.mem_piFinset, inBlock]
  rw [hset, Fintype.card_piFinset]
  have hfac : ∀ μ : Fin 3,
      ((Finset.univ : Finset (Fin (L μ + 1))).filter
        (fun z => (y μ).val ≤ z.val ∧ z.val < (y μ).val + s)).card = s :=
    fun μ => coord_interval_card _ _ (hfit μ)
  rw [Finset.prod_congr rfl (fun μ _ => hfac μ)]
  simp [Finset.prod_const]

/-- **THE BASE-SITE CARRIER'S EXACT SIZE — OURS, NOT p.408's.**  p.408 counts BIG BLOCKS; it never
defines a bond carrier and never prints the factor `3`.  What is claimed: `sourceCubeBonds` is
defined by the base-site convention, so a FITTED box of side `s` carries exactly `3·s³` of them —
`s³` cells (that part is p.408's, `block_card_of_fit`) times three positive directions (that part
is this tree's convention). -/
theorem sourceCubeBonds_card_of_fit (y : PeriodicLatticeSite L) (s : ℕ)
    (hfit : ∀ μ : Fin 3, (y μ).val + s ≤ L μ + 1) :
    (sourceCubeBonds y s).card = 3 * s ^ 3 := by
  classical
  have h1 : sourceCubeBonds y s
      = ((Finset.univ : Finset (PeriodicLatticeSite L)).filter (inBlock y s))
          ×ˢ (Finset.univ : Finset (Fin 3)) := by
    ext b
    simp [sourceCubeBonds, Finset.mem_product]
  rw [h1, Finset.card_product, block_card_of_fit y s hfit]
  simp [Finset.card_univ]
  ring

/-- One coordinate direction, for the endpoint-closed set: a base coordinate in `[a, a+s)` whose
successor is still in `[a, a+s)` must lie in `[a, a+s−1)`, which has `s − 1` values.  `hprop` says
the box does not wrap around the whole direction — without it the box IS the whole direction, the
successor is always inside, and the count would be `s`, not `s − 1`. -/
theorem coord_interval_succ_card {n : ℕ} (a s : ℕ) (hfit : a + s ≤ n + 1) (hprop : s < n + 1) :
    ((Finset.univ : Finset (Fin (n + 1))).filter
        (fun z => (a ≤ z.val ∧ z.val < a + s)
          ∧ (a ≤ ((z + 1 : Fin (n + 1))).val
              ∧ ((z + 1 : Fin (n + 1))).val < a + s))).card = s - 1 := by
  classical
  have hset :
      ((Finset.univ : Finset (Fin (n + 1))).filter
        (fun z => (a ≤ z.val ∧ z.val < a + s)
          ∧ (a ≤ ((z + 1 : Fin (n + 1))).val
              ∧ ((z + 1 : Fin (n + 1))).val < a + s)))
        = ((Finset.univ : Finset (Fin (n + 1))).filter
            (fun z => a ≤ z.val ∧ z.val < a + (s - 1))) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hz : z = Fin.last n
    · subst hz
      rw [Fin.val_add_one, if_pos rfl, Fin.val_last]
      omega
    · rw [Fin.val_add_one, if_neg hz]
      omega
  rw [hset]
  exact coord_interval_card a (s - 1) (by omega)

/-- **THE INTERIOR CARRIER'S EXACT SIZE.**  Under the fit, and with the box a PROPER sub-box of
every direction, exactly `3·s²·(s−1)` of the base-site bonds have both endpoints in the box.  At
`s = 10` this is `2700`, against `3·10³ = 3000` base-site bonds — the `300`-bond gap the carrier
adjudication turns on. -/
theorem interiorCubeBondsF_card (y : PeriodicLatticeSite L) (s : ℕ)
    (hfit : ∀ μ : Fin 3, (y μ).val + s ≤ L μ + 1) (hprop : ∀ μ : Fin 3, s < L μ + 1) :
    (interiorCubeBondsF y s).card = 3 * (s ^ 2 * (s - 1)) := by
  classical
  have hinj : ∀ d : Fin 3,
      Function.Injective (fun x : PeriodicLatticeSite L => ((x, d) : Bond L)) :=
    fun d a b hab => congrArg Prod.fst hab
  have hbi : interiorCubeBondsF y s
      = (Finset.univ : Finset (Fin 3)).biUnion (fun d =>
          ((Finset.univ : Finset (PeriodicLatticeSite L)).filter
              (fun x => inBlock y s x ∧ inBlock y s (periodicLatticeShift x d))).image
            (fun x => ((x, d) : Bond L))) := by
    ext b
    constructor
    · intro hb
      rw [mem_interiorCubeBondsF] at hb
      refine Finset.mem_biUnion.mpr ⟨b.2, Finset.mem_univ _, ?_⟩
      exact Finset.mem_image.mpr ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.1, hb.2⟩, rfl⟩
    · intro hb
      obtain ⟨d, -, hd⟩ := Finset.mem_biUnion.mp hb
      obtain ⟨x, hx, hxb⟩ := Finset.mem_image.mp hd
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hx
      rw [← hxb, mem_interiorCubeBondsF]
      exact ⟨h1, h2⟩
  rw [hbi, Finset.card_biUnion]
  · have hcard : ∀ d : Fin 3,
        (((Finset.univ : Finset (PeriodicLatticeSite L)).filter
            (fun x => inBlock y s x ∧ inBlock y s (periodicLatticeShift x d))).image
          (fun x => ((x, d) : Bond L))).card = s ^ 2 * (s - 1) := by
      intro d
      rw [Finset.card_image_of_injective _ (hinj d)]
      have hset : ((Finset.univ : Finset (PeriodicLatticeSite L)).filter
            (fun x => inBlock y s x ∧ inBlock y s (periodicLatticeShift x d)))
          = Fintype.piFinset (fun μ : Fin 3 =>
              (Finset.univ : Finset (Fin (L μ + 1))).filter
                (fun z => ((y μ).val ≤ z.val ∧ z.val < (y μ).val + s)
                  ∧ (μ = d → ((y μ).val ≤ ((z + 1 : Fin (L μ + 1))).val
                        ∧ ((z + 1 : Fin (L μ + 1))).val < (y μ).val + s)))) := by
        ext x
        simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩ μ
          refine ⟨h1 μ, fun hμ => ?_⟩
          subst hμ
          have h2μ := h2 μ
          simpa only [periodicLatticeShift, Function.update_self] using h2μ
        · intro h
          refine ⟨fun μ => (h μ).1, fun μ => ?_⟩
          by_cases hμ : μ = d
          · subst hμ
            simpa only [periodicLatticeShift, Function.update_self] using (h μ).2 rfl
          · simpa only [periodicLatticeShift, Function.update_of_ne hμ] using (h μ).1
      rw [hset, Fintype.card_piFinset]
      have hprod : ∀ μ : Fin 3,
          ((Finset.univ : Finset (Fin (L μ + 1))).filter
            (fun z => ((y μ).val ≤ z.val ∧ z.val < (y μ).val + s)
              ∧ (μ = d → ((y μ).val ≤ ((z + 1 : Fin (L μ + 1))).val
                    ∧ ((z + 1 : Fin (L μ + 1))).val < (y μ).val + s)))).card
          = if μ = d then s - 1 else s := by
        intro μ
        by_cases hμ : μ = d
        · subst hμ
          rw [if_pos rfl]
          rw [show ((Finset.univ : Finset (Fin (L μ + 1))).filter
                (fun z => ((y μ).val ≤ z.val ∧ z.val < (y μ).val + s)
                  ∧ (μ = μ → ((y μ).val ≤ ((z + 1 : Fin (L μ + 1))).val
                        ∧ ((z + 1 : Fin (L μ + 1))).val < (y μ).val + s))))
              = ((Finset.univ : Finset (Fin (L μ + 1))).filter
                (fun z => ((y μ).val ≤ z.val ∧ z.val < (y μ).val + s)
                  ∧ ((y μ).val ≤ ((z + 1 : Fin (L μ + 1))).val
                      ∧ ((z + 1 : Fin (L μ + 1))).val < (y μ).val + s))) from by
            ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, forall_const]]
          exact coord_interval_succ_card _ _ (hfit μ) (hprop μ)
        · rw [if_neg hμ]
          rw [show ((Finset.univ : Finset (Fin (L μ + 1))).filter
                (fun z => ((y μ).val ≤ z.val ∧ z.val < (y μ).val + s)
                  ∧ (μ = d → ((y μ).val ≤ ((z + 1 : Fin (L μ + 1))).val
                        ∧ ((z + 1 : Fin (L μ + 1))).val < (y μ).val + s))))
              = ((Finset.univ : Finset (Fin (L μ + 1))).filter
                (fun z => (y μ).val ≤ z.val ∧ z.val < (y μ).val + s)) from by
            ext z
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hμ, false_implies,
              and_true]]
          exact coord_interval_card _ _ (hfit μ)
      rw [Finset.prod_congr rfl (fun μ _ => hprod μ),
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ d), if_pos rfl,
        Finset.prod_congr rfl (fun μ hμ => if_neg (Finset.ne_of_mem_erase hμ)),
        Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ d), Finset.card_univ,
        Fintype.card_fin]
      show (s - 1) * s ^ 2 = s ^ 2 * (s - 1)
      exact Nat.mul_comm _ _
    rw [Finset.sum_congr rfl (fun d _ => hcard d), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_filter]
    rintro z ⟨x, -, hx⟩ ⟨x', -, hx'⟩
    exact hab ((congrArg Prod.snd hx).trans (congrArg Prod.snd hx').symm)

/-- **THE CARRIER GAP, AS NUMBERS.**  `s = 10`: `3000` base-site bonds, `2700` endpoint-closed,
`300` leaving the box. -/
theorem carrier_gap_at_ten (y : PeriodicLatticeSite L)
    (hfit : ∀ μ : Fin 3, (y μ).val + 10 ≤ L μ + 1) (hprop : ∀ μ : Fin 3, 10 < L μ + 1) :
    (sourceCubeBonds y 10).card = 3000
      ∧ (interiorCubeBondsF y 10).card = 2700
      ∧ (sourceCubeBonds y 10).card - (interiorCubeBondsF y 10).card = 300 := by
  refine ⟨by rw [sourceCubeBonds_card_of_fit y 10 hfit]; norm_num, ?_, ?_⟩
  · rw [interiorCubeBondsF_card y 10 hfit hprop]; norm_num
  · rw [sourceCubeBonds_card_of_fit y 10 hfit, interiorCubeBondsF_card y 10 hfit hprop]
    norm_num

/-! ### §17b — THE PRINTED CUBE AS THE BOX DATA p.408 FORCES -/

/-- **A CUBE OF p.396's CLASS, AS DATA.**  `compute/cube_convention/ADJUDICATION.md` (ledger
`CUBE-CONVENTION-BOX-FORCED-AT-P408`) rules the shape BOX-FORCED from p.408's own
size-to-block-count identity (*"a cube of the size `(2+2n)ML^jη` … hence a union of `(2+2n)^d` big
blocks"*): side `t` in block units ⟺ `t^d` blocks holds for every `n`, and only an axis-aligned
coordinate box satisfies it.  The `fit` field is the non-truncation clause §17a exists for. -/
structure PrintedCube (L : PeriodicLatticeExtent) where
  /-- the box's base corner -/
  base : PeriodicLatticeSite L
  /-- the box's side, in lattice units -/
  side : ℕ
  /-- the box does not run off the finite lattice -/
  fit : ∀ μ : Fin 3, (base μ).val + side ≤ L μ + 1

namespace PrintedCube

/-- `□` as a SITE set — the region the printed containment clauses (P1)/(P2) are about. -/
def region (C : PrintedCube L) : Finset (PeriodicLatticeSite L) := blockOf C.base C.side

/-- `□` as a BOND set, at the adjudicated INTERNAL carrier. -/
def bonds (C : PrintedCube L) : Finset (Bond L) := interiorCubeBondsF C.base C.side

theorem mem_region {C : PrintedCube L} {x : PeriodicLatticeSite L} :
    x ∈ C.region ↔ ∀ μ : Fin 3, (C.base μ).val ≤ (x μ).val ∧ (x μ).val < (C.base μ).val + C.side :=
  mem_blockOf

theorem mem_bonds {C : PrintedCube L} {b : Bond L} :
    b ∈ C.bonds ↔ inBlock C.base C.side b.1 ∧ inBlock C.base C.side (periodicLatticeShift b.1 b.2) :=
  mem_interiorCubeBondsF

theorem base_mem_region_of_mem_bonds {C : PrintedCube L} {b : Bond L} (hb : b ∈ C.bonds) :
    b.1 ∈ C.region :=
  mem_blockOf.mpr (mem_bonds.mp hb).1

theorem head_mem_region_of_mem_bonds {C : PrintedCube L} {b : Bond L} (hb : b ∈ C.bonds) :
    periodicLatticeShift b.1 b.2 ∈ C.region :=
  mem_blockOf.mpr (mem_bonds.mp hb).2

end PrintedCube

/-- The `μ`-coordinate of a forward shift, when the shift does not wrap. -/
theorem shift_val_self {x : PeriodicLatticeSite L} {μ : Fin 3} (h : (x μ).val + 1 < L μ + 1) :
    ((periodicLatticeShift x μ) μ).val = (x μ).val + 1 := by
  have hne : x μ ≠ Fin.last (L μ) := by
    intro hlast
    rw [hlast, Fin.val_last] at h
    omega
  simp only [periodicLatticeShift, Function.update_self]
  rw [Fin.val_add_one, if_neg hne]

/-- The other coordinates of a forward shift are untouched. -/
theorem shift_val_of_ne {x : PeriodicLatticeSite L} {μ ν : Fin 3} (h : ν ≠ μ) :
    ((periodicLatticeShift x μ) ν).val = (x ν).val := by
  simp only [periodicLatticeShift, Function.update_of_ne h]

/-- **`B^ell(S)`, THE BLOW-UP OF A LEVEL-`ell` SET** — CMP96 (2.2)/(2.4)'s `B^j`, the union of the
level-`ell` big blocks based at the points of `S`.

**LAW-19 DISCLOSURE — reuse was ATTEMPTED and is BLOCKED, with the block MEASURED.**
`Balaban/DomainSequence.lean` already carries this map as `bigBlockUnion S ell = S.biUnion (fun y =>
blockOf y ell)`, on this very carrier, and that is what this section tried first.  It cannot be used
here: `Finset.biUnion` carries a `DecidableEq (PeriodicLatticeSite L)` obligation which, at a
CONCRETE extent, makes the elaborator diverge — `compute/formal_batch/dev/Probe4.lean` (three
declarations, identical shape) compiles `CoarseLattice` membership and the filter form below at
`fun _ => 15`, and hits `maximum recursion depth` on the `biUnion` form alone.  The `Finset.filter`
form is extensionally the same set (`mem_blowUp` has the same statement as
`DomainSequence.mem_bigBlockUnion`) and elaborates.  The `biUnion` form remains correct where it is
used — every existing use in `DomainSequence` is at an ABSTRACT extent or on a small witness — so
this is a note about THIS section's concrete instances, not a defect report against that module. -/
def blowUp (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) : Finset (PeriodicLatticeSite L) :=
  Finset.univ.filter (fun x => ∃ y ∈ S, inBlock y ell x)

theorem mem_blowUp {S : Finset (PeriodicLatticeSite L)} {ell : ℕ} {x : PeriodicLatticeSite L} :
    x ∈ blowUp S ell ↔ ∃ y ∈ S, inBlock y ell x := by
  classical
  simp [blowUp]

/-! ### §17c — THE DOMAIN TOWER `{Ω_j}`, ITS `Λ_j`, AND THE SHELLS `B^j(Λ_j)` -/

/-- The side of a big block of `T_{L^{-j}}` in `T_η` units: `M·L^j`.  `M` is the source's big-block
size and `L` its RG factor. -/
def blockSide (M Lb j : ℕ) : ℕ := M * Lb ^ j

theorem blockSide_zero (M Lb : ℕ) : blockSide M Lb 0 = M := by simp [blockSide]

theorem blockSide_succ (M Lb j : ℕ) : blockSide M Lb (j + 1) = blockSide M Lb j * Lb := by
  simp only [blockSide, pow_succ]
  ring

theorem blockSide_dvd_succ (M Lb j : ℕ) : blockSide M Lb j ∣ blockSide M Lb (j + 1) :=
  ⟨Lb, blockSide_succ M Lb j⟩

theorem blockSide_dvd_of_le {M Lb : ℕ} {i j : ℕ} (h : i ≤ j) :
    blockSide M Lb i ∣ blockSide M Lb j := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨Lb ^ t, by simp only [blockSide, pow_add]; ring⟩

theorem blockSide_pos {M Lb : ℕ} (hM : 1 ≤ M) (hLb : 1 ≤ Lb) (j : ℕ) : 0 < blockSide M Lb j :=
  Nat.mul_pos hM (Nat.one_le_pow j Lb hLb)

/-- The corner of the level-`ell` block containing `x` — the same construction as
`SG_Geom.floorTo` (`Ofine P p S = {x : floorTo P p x ∈ S}` is that module's `B^p`), ported to the
`PeriodicLatticeSite` carrier because the two carriers differ (`SG_Geom` sites are
`Fin P.d → ZMod P.N`, these are `(μ : Fin 3) → Fin (L μ + 1)`) and `formal/` has no translation
layer between them. -/
def coarseCorner (ell : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun μ => ⟨(x μ).val / ell * ell, lt_of_le_of_lt (Nat.div_mul_le_self _ _) (x μ).isLt⟩

theorem coarseCorner_val (ell : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((coarseCorner ell x) μ).val = (x μ).val / ell * ell := rfl

theorem coarseCorner_mem_coarseLattice {ell : ℕ} (hell : 0 < ell) (x : PeriodicLatticeSite L) :
    coarseCorner ell x ∈ CoarseLattice L ell := by
  refine mem_CoarseLattice.mpr (fun μ => ?_)
  rw [coarseCorner_val]
  exact Nat.mul_mod_left _ _

theorem inBlock_coarseCorner {ell : ℕ} (hell : 0 < ell) (x : PeriodicLatticeSite L) :
    inBlock (coarseCorner ell x) ell x := by
  intro μ
  refine ⟨by rw [coarseCorner_val]; exact Nat.div_mul_le_self _ _, ?_⟩
  rw [coarseCorner_val]
  have hdm := Nat.div_add_mod (x μ).val ell
  have hlt := Nat.mod_lt (x μ).val hell
  calc (x μ).val = ell * ((x μ).val / ell) + (x μ).val % ell := hdm.symm
    _ < ell * ((x μ).val / ell) + ell := by omega
    _ = (x μ).val / ell * ell + ell := by rw [Nat.mul_comm]

/-- A multiple of `ell` that is `≤ x` is `≤` the level-`ell` corner of `x`. -/
theorem le_coarseCorner_of_dvd {ell a b : ℕ} (hell : 0 < ell) (ha : ell ∣ a) (hab : a ≤ b) :
    a ≤ b / ell * ell := by
  obtain ⟨m, rfl⟩ := ha
  have : m ≤ b / ell := Nat.le_div_iff_mul_le hell |>.mpr (by rw [Nat.mul_comm]; exact hab)
  calc ell * m = m * ell := Nat.mul_comm _ _
    _ ≤ b / ell * ell := Nat.mul_le_mul_right _ this

/-- **THE DOMAIN SEQUENCE `{Ω_j}` (CMP96 (2.1)-(2.2), CMP99b p.396's *"sequence of domains"*).**

`Oc j` is `Ω_j^{(j)}`, the level-`j` representation; the fine domain is `Ω_j = B^j(Ω_j^{(j)})`,
which is (2.2)'s first clause and is DERIVED here (`Omega`), not carried twice.  `hnest` is (2.1)
stated on the fine domains as printed; `hcoarse` is (2.2)'s `Ω_j^{(j)} ⊂ T^{(j)}_{L^jη}` — the
level-`j` representation is a set of block corners.  `hstop` records that the sequence is finite:
p.396 uses indices `0 ≤ j ≤ k` and `Λ_{j+1}` at `j = k`, so the tower carries `j = 0,…,k+1`.

**THE `M` FLOOR IS `hM : 2 ≤ M`, AND IT IS CONSUMED.**  `compute/cube_convention/ADJUDICATION.md`
rules that a bare `M ≥ 1` UNDERSTATES the source: the printed hypothesis is Theorem 3.1's
`M ≥ M_1` with `M_1` unspecified (*"sufficiently large"*, CMP96 p.232).  `2 ≤ M` is therefore
strictly WEAKER than the source's hypothesis — every configuration the source admits satisfies it —
and it is not decoration: `blockCorner_mem_region` below FAILS at `M = 1`, because a big block of
side `1` has no interior bond, and with it the bond-level projection of (P2) fails. -/
structure DomainTower (L : PeriodicLatticeExtent) (k M Lb : ℕ) where
  /-- `Ω_j^{(j)}`, the level-`j` representation of `Ω_j` -/
  Oc : ℕ → Finset (PeriodicLatticeSite L)
  /-- big blocks have at least two sites per side; see the structure docstring -/
  hM : 2 ≤ M
  /-- the RG factor is at least `1` -/
  hLb : 1 ≤ Lb
  /-- **(2.2)**: `Ω_j^{(j)} ⊂ T^{(j)}_{L^jη}` — a set of level-`j` block corners -/
  hcoarse : ∀ j, Oc j ⊆ CoarseLattice L (blockSide M Lb j)
  /-- **(2.1)**: `Ω_1 ⊃ Ω_2 ⊃ …`, stated on the fine domains `Ω_j = B^j(Ω_j^{(j)})` as printed -/
  hnest : ∀ j, blowUp (Oc (j + 1)) (blockSide M Lb (j + 1))
            ⊆ blowUp (Oc j) (blockSide M Lb j)
  /-- the tower is finite: p.396 ranges over `0 ≤ j ≤ k` and reaches `Λ_{j+1}` at `j = k` -/
  hstop : ∀ j, k + 1 < j → Oc j = ∅

namespace DomainTower

variable {k M Lb : ℕ} (D : DomainTower L k M Lb)

/-- **`Ω_j = B^j(Ω_j^{(j)})`**, (2.2)'s first clause, derived. -/
def Omega (j : ℕ) : Finset (PeriodicLatticeSite L) :=
  blowUp (D.Oc j) (blockSide M Lb j)

/-- **`Λ_j = Ω_j^{(j)} ∖ Ω_{j+1}`**, (2.3) / p.396's *"`Λ_0 = Ω_0 ∖ Ω_1`"*. -/
def Lam (j : ℕ) : Finset (PeriodicLatticeSite L) :=
  (D.Oc j).filter (fun y => y ∉ D.Omega (j + 1))

/-- **`B^j(Λ_j)`**, the shell the printed clauses (P1)/(P2) are stated with. -/
def Shell (j : ℕ) : Finset (PeriodicLatticeSite L) :=
  blowUp (D.Lam j) (blockSide M Lb j)

theorem mem_Omega {j : ℕ} {x : PeriodicLatticeSite L} :
    x ∈ D.Omega j ↔ ∃ y ∈ D.Oc j, inBlock y (blockSide M Lb j) x := mem_blowUp

theorem mem_Lam {j : ℕ} {y : PeriodicLatticeSite L} :
    y ∈ D.Lam j ↔ y ∈ D.Oc j ∧ y ∉ D.Omega (j + 1) := by simp [Lam]

theorem mem_Shell {j : ℕ} {x : PeriodicLatticeSite L} :
    x ∈ D.Shell j ↔ ∃ y ∈ D.Lam j, inBlock y (blockSide M Lb j) x := mem_blowUp

theorem lam_subset_oc (j : ℕ) : D.Lam j ⊆ D.Oc j := Finset.filter_subset _ _

theorem shell_subset_omega (j : ℕ) : D.Shell j ⊆ D.Omega j := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := D.mem_Shell.mp hx
  exact D.mem_Omega.mpr ⟨y, D.lam_subset_oc j hy, hxy⟩

theorem omega_antitone {i j : ℕ} (h : i ≤ j) : D.Omega j ⊆ D.Omega i := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction t with
  | zero => simp
  | succ n ih =>
    intro x hx
    have hx' : x ∈ D.Omega ((i + n) + 1) := by
      have hidx : i + (n + 1) = (i + n) + 1 := by omega
      rwa [hidx] at hx
    exact ih (D.hnest (i + n) hx')

/-- **THE SHELLS ARE PAIRWISE DISJOINT — CMP96 (2.4)'s partition, as a theorem.**

`T = ⋃_{j=0}^k B^j(Λ_j)` is printed as a decomposition; that the pieces do not overlap is what
makes an index READABLE off a point, and it is exactly what the tower's own fields force: a point of
`B^j(Λ_j)` with `j ≥ i+1` lies in `Ω_j ⊆ Ω_{i+1}` by (2.1), while a point of `B^i(Λ_i)` has its
level-`i` corner OUTSIDE `Ω_{i+1}` by (2.3) — and `Ω_{i+1}` is a union of level-`(i+1)` blocks, each
of which is a union of level-`i` blocks, so it cannot contain the point without containing its
level-`i` corner.

This is the load-bearing geometric fact of §17: `two_clause_rigid` below is proved FROM it. -/
theorem shell_disjoint {i j : ℕ} (hij : i < j) {x : PeriodicLatticeSite L}
    (hi : x ∈ D.Shell i) (hj : x ∈ D.Shell j) : False := by
  obtain ⟨y, hy, hxy⟩ := D.mem_Shell.mp hi
  have hyLam := D.mem_Lam.mp hy
  -- `x ∈ Ω_j ⊆ Ω_{i+1}`
  have hxOmega : x ∈ D.Omega (i + 1) :=
    D.omega_antitone (by omega) (D.shell_subset_omega j hj)
  obtain ⟨w, hw, hwx⟩ := D.mem_Omega.mp hxOmega
  -- `y`, the level-`i` corner of `x`, is in the same level-`(i+1)` block as `x`
  have hbi : 0 < blockSide M Lb i := blockSide_pos (by have := D.hM; omega) D.hLb i
  have hycoarse := mem_CoarseLattice.mp (D.hcoarse i (hyLam.1))
  have hwcoarse := mem_CoarseLattice.mp (D.hcoarse (i + 1) hw)
  have hdvd : blockSide M Lb i ∣ blockSide M Lb (i + 1) := blockSide_dvd_succ M Lb i
  have hyin : inBlock w (blockSide M Lb (i + 1)) y := by
    intro μ
    have hxμ := hwx μ
    have hyμ := hxy μ
    refine ⟨?_, by omega⟩
    -- `w_μ` is a multiple of `blockSide i`, `≤ x_μ`, and `y_μ` is the largest such
    obtain ⟨a, ha⟩ : blockSide M Lb i ∣ (w μ).val :=
      dvd_trans hdvd (Nat.dvd_of_mod_eq_zero (hwcoarse μ))
    obtain ⟨b, hb⟩ : blockSide M Lb i ∣ (y μ).val := Nat.dvd_of_mod_eq_zero (hycoarse μ)
    have hexp : blockSide M Lb i * (b + 1) = blockSide M Lb i * b + blockSide M Lb i := by ring
    have hab : a < b + 1 := by
      by_contra hcon
      push_neg at hcon
      have hmul : blockSide M Lb i * (b + 1) ≤ blockSide M Lb i * a :=
        Nat.mul_le_mul_left _ hcon
      omega
    have hle : blockSide M Lb i * a ≤ blockSide M Lb i * b := Nat.mul_le_mul_left _ (by omega)
    omega
  exact hyLam.2 (D.mem_Omega.mpr ⟨w, hw, hyin⟩)

theorem shell_disjoint' {i j : ℕ} (hij : i ≠ j) {x : PeriodicLatticeSite L}
    (hi : x ∈ D.Shell i) (hj : x ∈ D.Shell j) : False := by
  rcases Nat.lt_or_ge i j with h | h
  · exact D.shell_disjoint h hi hj
  · exact D.shell_disjoint (by omega) hj hi

end DomainTower

/-! ### §17d — THE PRINTED CUBE CLASS AND THE PRINTED INDEX -/

/-- **(P3), p.396: *"`□` is a union of several big blocks of the lattice `T_{L^{-j}}`"*.**  A box is
a union of level-`j` big blocks exactly when its corner is level-`j` aligned and its side is a
positive multiple of the level-`j` block side. -/
def IsBlockUnionAt (M Lb j : ℕ) (C : PrintedCube L) : Prop :=
  (∀ μ : Fin 3, (C.base μ).val % blockSide M Lb j = 0)
    ∧ blockSide M Lb j ∣ C.side
    ∧ 0 < C.side

/-- **(P3) TRANSFERS DOWNWARD IN THE INDEX.**  A union of level-`j` big blocks is a union of
level-`i` ones for `i ≤ j`, because `blockSide i ∣ blockSide j`.  This is why the printed
three-clause uniqueness has real content only against LARGER indices, and it is used in
`two_clause_rigid`'s companion discussion. -/
theorem isBlockUnionAt_of_le {M Lb i j : ℕ} (hij : i ≤ j) {C : PrintedCube L}
    (h : IsBlockUnionAt M Lb j C) : IsBlockUnionAt M Lb i C := by
  obtain ⟨halign, hdvd, hpos⟩ := h
  have hd : blockSide M Lb i ∣ blockSide M Lb j := blockSide_dvd_of_le hij
  refine ⟨fun μ => ?_, dvd_trans hd hdvd, hpos⟩
  obtain ⟨c, hc⟩ : blockSide M Lb i ∣ (C.base μ).val :=
    dvd_trans hd (Nat.dvd_of_mod_eq_zero (halign μ))
  rw [hc]
  exact Nat.mul_mod_right _ _

/-- **p.396's CUBE CLASS AND ITS INDEX — the full printed sentence, as a structure.**

Fields `contained`, `meets`, `bigblock` are (P1), (P2), (P3) AT the printed index; `unique` is the
printed uniqueness — *"there exists a unique index `j`, `0 ≤ j ≤ k`, such that"* the THREE
properties — so its hypothesis carries all three conjuncts.  `floor` is *"its size in the lattice
`T_η` is `O(1) M L^j η`.  Here `O(1)` will mean a number `≥ 10`."*

**SCOPE NOTE, OWED AND DISCHARGED (`WIRE-ROUND4-DELTAS-CLOSED-BOTH-FAMILIES`, Kimi's one owed
sentence).**  `CurvedLegWire.OmegaData.unique` tests uniqueness among the indices satisfying only
(P1) and (P2) — two of the three printed properties — which is an UNSTATED STRENGTHENING of the
printed scope.  This structure carries the printed three-clause scope, and `two_clause_rigid` PROVES
the wire's stronger scope from it: the strengthening is real as a STATEMENT and vacuous as an
ASSUMPTION, once the domain sequence is present. -/
structure PrintedOmegaData (L : PeriodicLatticeExtent) (k M Lb : ℕ) where
  /-- the domain sequence `{Ω_j}` the conditions *"depend on"* -/
  D : DomainTower L k M Lb
  /-- *"a class of cubes"* -/
  Class : PrintedCube L → Prop
  /-- *"there exists a unique index `j`"* — the printed index map -/
  idx : PrintedCube L → ℕ
  /-- *"`0 ≤ j ≤ k`"* -/
  idx_le : ∀ C, Class C → idx C ≤ k
  /-- **(P1)** *"`□ ⊂ B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1})`"* -/
  contained : ∀ C, Class C → C.region ⊆ D.Shell (idx C) ∪ D.Shell (idx C + 1)
  /-- **(P2)** *"`□ ∩ B^j(Λ_j) ≠ ∅`"* -/
  meets : ∀ C, Class C → (C.region ∩ D.Shell (idx C)).Nonempty
  /-- **(P3)** *"`□` is a union of several big blocks of the lattice `T_{L^{-j}}`"* -/
  bigblock : ∀ C, Class C → IsBlockUnionAt M Lb (idx C) C
  /-- *"its size … is `O(1) M L^j η`.  Here `O(1)` will mean a number `≥ 10`"* -/
  floor : ∀ C, Class C → 10 * blockSide M Lb (idx C) ≤ C.side
  /-- **THE PRINTED UNIQUENESS**, at its printed scope: among the `j ∈ [0,k]` satisfying ALL THREE -/
  unique : ∀ C, Class C → ∀ j : ℕ, j ≤ k →
    C.region ⊆ D.Shell j ∪ D.Shell (j + 1) →
    (C.region ∩ D.Shell j).Nonempty →
    IsBlockUnionAt M Lb j C →
    j = idx C

namespace PrintedOmegaData

variable {k M Lb : ℕ} (P : PrintedOmegaData L k M Lb)

/-- **(P3) IS LOAD-BEARING FOR THE BOND-LEVEL READING OF (P2): the block corner of a shell point of
the cube is ITSELF in the cube, and carries a cube bond.**

Given a site `x` of `□` lying in `B^{idx}(Λ_{idx})`, its level-`idx` corner `y` is in `Λ_{idx}`
(hence in the shell), lies in `□` because `□` is a union of level-`idx` blocks (P3), and has its
forward neighbour in `□` because a big block has at least `2` sites per side (`hM`).  So `(y, 0)` is
a bond OF the cube based at a shell point.

At `M = 1` this fails: the block is a single site, `y` can be the far corner of `□`, and no cube
bond is based in the shell. -/
theorem blockCorner_mem_region {C : PrintedCube L} (hC : P.Class C)
    {x : PeriodicLatticeSite L} (hx : x ∈ C.region) (hxs : x ∈ P.D.Shell (P.idx C)) :
    ∃ y : PeriodicLatticeSite L,
      y ∈ C.region ∧ y ∈ P.D.Shell (P.idx C) ∧ ((y, 0) : Bond L) ∈ C.bonds := by
  classical
  have hbjpos : 0 < blockSide M Lb (P.idx C) :=
    blockSide_pos (by have := P.D.hM; omega) P.D.hLb (P.idx C)
  have hbj2 : 2 ≤ blockSide M Lb (P.idx C) := by
    have h1 : (2 : ℕ) ≤ M := P.D.hM
    have hp : 1 ≤ Lb ^ (P.idx C) := Nat.one_le_pow _ _ P.D.hLb
    have h2 : M * 1 ≤ M * Lb ^ (P.idx C) := Nat.mul_le_mul_left _ hp
    simp only [blockSide]
    omega
  obtain ⟨y, hyLam, hyx⟩ := P.D.mem_Shell.mp hxs
  obtain ⟨halign, hdvd, hpos⟩ := P.bigblock C hC
  have hycoarse := mem_CoarseLattice.mp (P.D.hcoarse (P.idx C) (P.D.lam_subset_oc (P.idx C) hyLam))
  have hxregion := PrintedCube.mem_region.mp hx
  -- `y`, the level-`idx` corner of the shell point `x`, lies in the box: both `base` and `y` are
  -- level-`idx` aligned, and `base ≤ x < y + blockSide` forces `base ≤ y`.
  have hyregion : y ∈ C.region := by
    refine PrintedCube.mem_region.mpr (fun μ => ?_)
    have h1 := (hxregion μ).1
    have h2 := (hxregion μ).2
    have h3 := (hyx μ).1
    have h4 := (hyx μ).2
    obtain ⟨a, ha⟩ : blockSide M Lb (P.idx C) ∣ (C.base μ).val :=
      Nat.dvd_of_mod_eq_zero (halign μ)
    obtain ⟨b, hb⟩ : blockSide M Lb (P.idx C) ∣ (y μ).val :=
      Nat.dvd_of_mod_eq_zero (hycoarse μ)
    have hab : a ≤ b := by
      by_contra hcon
      push_neg at hcon
      have hmul : blockSide M Lb (P.idx C) * (b + 1) ≤ blockSide M Lb (P.idx C) * a :=
        Nat.mul_le_mul_left _ (by omega)
      have hexp : blockSide M Lb (P.idx C) * (b + 1)
          = blockSide M Lb (P.idx C) * b + blockSide M Lb (P.idx C) := by ring
      omega
    have hle : blockSide M Lb (P.idx C) * a ≤ blockSide M Lb (P.idx C) * b :=
      Nat.mul_le_mul_left _ hab
    exact ⟨by omega, by omega⟩
  have hyregionμ := PrintedCube.mem_region.mp hyregion
  -- the forward neighbour of `y` in direction `0` is still in the box: the box is a union of
  -- level-`idx` blocks (P3) and a block has at least two sites per side (`2 ≤ M`).
  have hy0next : (y 0).val + 1 < (C.base 0).val + C.side := by
    obtain ⟨a, ha⟩ : blockSide M Lb (P.idx C) ∣ (C.base 0).val :=
      Nat.dvd_of_mod_eq_zero (halign 0)
    obtain ⟨b, hb⟩ : blockSide M Lb (P.idx C) ∣ (y 0).val :=
      Nat.dvd_of_mod_eq_zero (hycoarse 0)
    obtain ⟨c, hc⟩ : blockSide M Lb (P.idx C) ∣ C.side := hdvd
    have h1 := (hyregionμ 0).1
    have h2 := (hyregionμ 0).2
    have hexpac : blockSide M Lb (P.idx C) * (a + c)
        = blockSide M Lb (P.idx C) * a + blockSide M Lb (P.idx C) * c := by ring
    have hbc : b < a + c := by
      by_contra hcon
      push_neg at hcon
      have hmul : blockSide M Lb (P.idx C) * (a + c) ≤ blockSide M Lb (P.idx C) * b :=
        Nat.mul_le_mul_left _ hcon
      omega
    have hmul2 : blockSide M Lb (P.idx C) * (b + 1) ≤ blockSide M Lb (P.idx C) * (a + c) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexpb : blockSide M Lb (P.idx C) * (b + 1)
        = blockSide M Lb (P.idx C) * b + blockSide M Lb (P.idx C) := by ring
    omega
  have hshiftin : inBlock C.base C.side (periodicLatticeShift y 0) := by
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      have hlt : (y 0).val + 1 < L 0 + 1 := by
        have hfit0 := C.fit 0
        omega
      rw [shift_val_self hlt]
      exact ⟨by have := (hyregionμ 0).1; omega, hy0next⟩
    · rw [shift_val_of_ne hμ]
      exact hyregionμ μ
  refine ⟨y, hyregion, ?_, ?_⟩
  · exact P.D.mem_Shell.mpr ⟨y, hyLam, fun μ => ⟨le_rfl, by omega⟩⟩
  · exact PrintedCube.mem_bonds.mpr ⟨fun μ => hyregionμ μ, hshiftin⟩

/-- **THE WIRE'S UNIQUENESS SCOPE IS A THEOREM, NOT AN EXTRA ASSUMPTION.**

`CurvedLegWire.OmegaData.unique` drops the big-block conjunct (P3) from the printed uniqueness
scope, and reads the containment clauses at the BOND level, where the far corner of the box carries
no bond.  Both weakenings are absorbed here: on a class cube, the two containment clauses alone —
read only away from the far corner — already force the printed index.

The proof is `shell_disjoint`, twice.  If `j` satisfies both clauses then the cube's `Shell (idx C)`
point (which exists by (P2), and can be taken to be a block corner, hence bond-carrying and not the
far corner, by `blockCorner_mem_region`) lies in `Shell j ∪ Shell (j+1)`, forcing `idx C ∈ {j, j+1}`;
and the cube's `Shell j` point lies in `Shell (idx C) ∪ Shell (idx C + 1)`, forcing
`j ∈ {idx C, idx C + 1}`.  Only `j = idx C` survives. -/
theorem two_clause_rigid {C : PrintedCube L} (hC : P.Class C) (j : ℕ)
    (hcont : ∀ x ∈ C.region, (∃ μ : Fin 3, ((x, μ) : Bond L) ∈ C.bonds) →
      x ∈ P.D.Shell j ∪ P.D.Shell (j + 1))
    (hmeet : (C.region ∩ P.D.Shell j).Nonempty) :
    j = P.idx C := by
  classical
  obtain ⟨x0, hx0⟩ := P.meets C hC
  have hx0r : x0 ∈ C.region := (Finset.mem_inter.mp hx0).1
  have hx0s : x0 ∈ P.D.Shell (P.idx C) := (Finset.mem_inter.mp hx0).2
  obtain ⟨y, hyr, hys, hyb⟩ := P.blockCorner_mem_region hC hx0r hx0s
  have hy2 : y ∈ P.D.Shell j ∪ P.D.Shell (j + 1) := hcont y hyr ⟨0, hyb⟩
  -- first: `idx C ∈ {j, j+1}`
  have h1 : P.idx C = j ∨ P.idx C = j + 1 := by
    rcases Finset.mem_union.mp hy2 with h | h
    · by_contra hcon
      push_neg at hcon
      exact P.D.shell_disjoint' (by omega) hys h
    · by_contra hcon
      push_neg at hcon
      exact P.D.shell_disjoint' (by omega) hys h
  -- second: `j ∈ {idx C, idx C + 1}`
  obtain ⟨z, hz⟩ := hmeet
  have hzr : z ∈ C.region := (Finset.mem_inter.mp hz).1
  have hzs : z ∈ P.D.Shell j := (Finset.mem_inter.mp hz).2
  have hz2 : z ∈ P.D.Shell (P.idx C) ∪ P.D.Shell (P.idx C + 1) := P.contained C hC hzr
  have h2 : j = P.idx C ∨ j = P.idx C + 1 := by
    rcases Finset.mem_union.mp hz2 with h | h
    · by_contra hcon
      push_neg at hcon
      exact P.D.shell_disjoint' (by omega) hzs h
    · by_contra hcon
      push_neg at hcon
      exact P.D.shell_disjoint' (by omega) hzs h
  omega

end PrintedOmegaData

/-! ### §17e — THE PROJECTION TO THE WIRE'S BOND-LEVEL SHAPE -/

/-- **`CurvedLegWire.OmegaData`, FIELD FOR FIELD.**

The wire's structure is `OmegaData (D3 : Door3Setup) (Lscale : ℝ)` with
`Bdom : ℕ → Finset (Bond D3.L)`, `idx : Finset (Bond D3.L) → ℕ`, and the four clauses
`idx_le`, `contained`, `meets`, `unique`, each quantified over the cubes of its class
`fun cube => ∃ j, SourceCubeAt D3 Lscale cube j`.  `WireOmegaShape L k Cls` is that structure with
the three wire-local parameters abstracted: `L := D3.L`, `k := D3.k`, and `Cls` the class predicate.
`formal/` cannot import `compute/`, so the correspondence is by SHAPE, and the shape is literal —
instantiating the wire's `OmegaData` from a `WireOmegaShape` is
`⟨W.Bdom, W.idx, W.idx_le, W.contained, W.meets, W.unique⟩`.

The `Bdom` this section supplies is the BASE-SITE reading of a domain: `b ∈ Bdom j` iff the base
site of `b` lies in `B^j(Λ_j)`.  That reading is NOT the (3.35)/(3.36) carrier ruling
(`CARRIER-RULED-INTERNAL-BONDS`, which is about the bonds the printed BOUNDS range over, a
different construct); it is how a DOMAIN — a site set — is read as a bond set, and it is chosen
because it is the reading under which the wire's `contained` and `unique` clauses correspond to
p.396's site-level clauses in BOTH directions. -/
structure WireOmegaShape (L : PeriodicLatticeExtent) (k : ℕ) (Cls : Finset (Bond L) → Prop) where
  /-- the RG domain sequence, read as bond sets -/
  Bdom : ℕ → Finset (Bond L)
  /-- the printed index of a cube -/
  idx : Finset (Bond L) → ℕ
  /-- p.396's printed range `0 ≤ j ≤ k` -/
  idx_le : ∀ cube : Finset (Bond L), Cls cube → idx cube ≤ k
  /-- p.396: `□ ⊂ B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1})` -/
  contained : ∀ cube : Finset (Bond L), Cls cube →
    ∀ b ∈ cube, b ∈ Bdom (idx cube) ∨ b ∈ Bdom (idx cube + 1)
  /-- p.396: `□ ∩ B^j(Λ_j) ≠ ∅` -/
  meets : ∀ cube : Finset (Bond L), Cls cube → ∃ b ∈ cube, b ∈ Bdom (idx cube)
  /-- the wire's uniqueness scope: unique among the `j ≤ k` with the two containment clauses -/
  unique : ∀ cube : Finset (Bond L), Cls cube → ∀ j : ℕ, j ≤ k →
    (∀ b ∈ cube, b ∈ Bdom j ∨ b ∈ Bdom (j + 1)) →
    (∃ b ∈ cube, b ∈ Bdom j) → j = idx cube

/-- A site set read as a bond set by the BASE-SITE rule. -/
def bondsBased (S : Finset (PeriodicLatticeSite L)) : Finset (Bond L) :=
  Finset.univ.filter (fun b : Bond L => b.1 ∈ S)

theorem mem_bondsBased {S : Finset (PeriodicLatticeSite L)} {b : Bond L} :
    b ∈ bondsBased S ↔ b.1 ∈ S := by simp [bondsBased]

namespace PrintedOmegaData

variable {k M Lb : ℕ} (P : PrintedOmegaData L k M Lb)

/-- The class, transported to bond sets. -/
def ClsOf (cube : Finset (Bond L)) : Prop := ∃ C : PrintedCube L, P.Class C ∧ cube = C.bonds

open Classical in
/-- The printed index, transported to bond sets. -/
noncomputable def idxOf (cube : Finset (Bond L)) : ℕ :=
  if h : ∃ C : PrintedCube L, P.Class C ∧ cube = C.bonds then P.idx h.choose else 0

theorem idxOf_spec {cube : Finset (Bond L)} (h : P.ClsOf cube) :
    ∃ C : PrintedCube L, P.Class C ∧ cube = C.bonds ∧ P.idxOf cube = P.idx C := by
  classical
  have h' : ∃ C : PrintedCube L, P.Class C ∧ cube = C.bonds := h
  refine ⟨h'.choose, h'.choose_spec.1, h'.choose_spec.2, ?_⟩
  rw [idxOf, dif_pos h']

/-- **THE PROJECTION — the wire's structure, built from the printed one, UNCONDITIONALLY.**

Every field is discharged: `contained` from (P1) plus "a cube bond's base is a cube site";
`meets` from (P2) plus `blockCorner_mem_region` (which is where (P3) and `2 ≤ M` are consumed); and
`unique`, the wire's STRENGTHENED scope, from `two_clause_rigid`, i.e. from the shell disjointness
that CMP96 (2.4) prints and the tower's own fields force.

No side hypothesis is taken.  In particular no well-definedness assumption on `idxOf` is needed:
every clause is proved at the representative `idxOf` itself selects. -/
noncomputable def toWireShape : WireOmegaShape L k P.ClsOf where
  Bdom := fun j => bondsBased (P.D.Shell j)
  idx := P.idxOf
  idx_le := by
    intro cube hcube
    obtain ⟨C, hC, -, hidx⟩ := P.idxOf_spec hcube
    rw [hidx]
    exact P.idx_le C hC
  contained := by
    intro cube hcube b hb
    obtain ⟨C, hC, hcb, hidx⟩ := P.idxOf_spec hcube
    subst hcb
    rw [hidx]
    have hbr : b.1 ∈ C.region := PrintedCube.base_mem_region_of_mem_bonds hb
    rcases Finset.mem_union.mp (P.contained C hC hbr) with h | h
    · exact Or.inl (mem_bondsBased.mpr h)
    · exact Or.inr (mem_bondsBased.mpr h)
  meets := by
    intro cube hcube
    obtain ⟨C, hC, hcb, hidx⟩ := P.idxOf_spec hcube
    subst hcb
    rw [hidx]
    obtain ⟨x0, hx0⟩ := P.meets C hC
    obtain ⟨y, -, hys, hyb⟩ := P.blockCorner_mem_region hC
      (Finset.mem_inter.mp hx0).1 (Finset.mem_inter.mp hx0).2
    exact ⟨(y, 0), hyb, mem_bondsBased.mpr hys⟩
  unique := by
    intro cube hcube j hjk hcont hmeet
    obtain ⟨C, hC, hcb, hidx⟩ := P.idxOf_spec hcube
    subst hcb
    rw [hidx]
    refine P.two_clause_rigid hC j (fun x hx hxb => ?_) ?_
    · obtain ⟨μ, hμ⟩ := hxb
      have := hcont ((x, μ) : Bond L) hμ
      rcases this with h | h
      · exact Finset.mem_union_left _ (mem_bondsBased.mp h)
      · exact Finset.mem_union_right _ (mem_bondsBased.mp h)
    · obtain ⟨b, hb, hbs⟩ := hmeet
      exact ⟨b.1, Finset.mem_inter.mpr
        ⟨PrintedCube.base_mem_region_of_mem_bonds hb, mem_bondsBased.mp hbs⟩⟩

end PrintedOmegaData

/-! ### §17f — INSTANCES: THE DEGENERATE ONE, AND A NON-DEGENERATE ONE WITH A TWO-VALUED INDEX -/

/-- **`B^ell(T^{(ell)}) = T`** — every site lies in the level-`ell` block based at its own corner. -/
theorem mem_blowUp_coarseLattice {ell : ℕ} (hell : 0 < ell) (x : PeriodicLatticeSite L) :
    x ∈ blowUp (CoarseLattice L ell) ell :=
  mem_blowUp.mpr ⟨coarseCorner ell x, coarseCorner_mem_coarseLattice hell x,
    inBlock_coarseCorner hell x⟩

theorem blowUp_empty (ell : ℕ) :
    blowUp (∅ : Finset (PeriodicLatticeSite L)) ell = ∅ := by
  simp [blowUp]

/-- The degenerate tower: `Ω_0^{(0)}` is ALL level-`0` block corners and every later domain is
empty.  `Ω_0 = T`, `Ω_j = ∅` for `j ≥ 1`, so (2.1)'s nesting is trivially satisfied. -/
def degenerateTower (L : PeriodicLatticeExtent) (k M Lb : ℕ) (hM : 2 ≤ M) (hLb : 1 ≤ Lb) :
    DomainTower L k M Lb where
  Oc := fun j => match j with
    | 0 => CoarseLattice L (blockSide M Lb 0)
    | _ + 1 => ∅
  hM := hM
  hLb := hLb
  hcoarse := by
    intro j
    match j with
    | 0 => exact Finset.Subset.refl _
    | _ + 1 => exact Finset.empty_subset _
  hnest := by
    intro j x hx
    have hx' : x ∈ blowUp (∅ : Finset (PeriodicLatticeSite L))
        (blockSide M Lb (j + 1)) := hx
    rw [blowUp_empty] at hx'
    exact absurd hx' (Finset.notMem_empty x)
  hstop := by
    intro j hj
    match j with
    | 0 => omega
    | _ + 1 => rfl

theorem degenerate_shell_zero {k M Lb : ℕ} (hM : 2 ≤ M) (hLb : 1 ≤ Lb)
    (x : PeriodicLatticeSite L) : x ∈ (degenerateTower L k M Lb hM hLb).Shell 0 := by
  have hpos : 0 < blockSide M Lb 0 := blockSide_pos (by omega) hLb 0
  refine (degenerateTower L k M Lb hM hLb).mem_Shell.mpr
    ⟨coarseCorner (blockSide M Lb 0) x, ?_, inBlock_coarseCorner hpos x⟩
  refine (degenerateTower L k M Lb hM hLb).mem_Lam.mpr
    ⟨coarseCorner_mem_coarseLattice hpos x, ?_⟩
  intro hcon
  obtain ⟨w, hw, -⟩ := (degenerateTower L k M Lb hM hLb).mem_Omega.mp hcon
  have hw' : w ∈ (∅ : Finset (PeriodicLatticeSite L)) := hw
  exact absurd hw' (Finset.notMem_empty w)

theorem degenerate_shell_pos {k M Lb : ℕ} (hM : 2 ≤ M) (hLb : 1 ≤ Lb) {j : ℕ} (hj : j ≠ 0)
    (x : PeriodicLatticeSite L) : x ∉ (degenerateTower L k M Lb hM hLb).Shell j := by
  intro hx
  obtain ⟨y, hy, -⟩ := (degenerateTower L k M Lb hM hLb).mem_Shell.mp hx
  have hy' := (degenerateTower L k M Lb hM hLb).mem_Lam.mp hy
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hy'' : y ∈ (∅ : Finset (PeriodicLatticeSite L)) := hy'.1
  exact absurd hy'' (Finset.notMem_empty y)

/-- **THE DEGENERATE `PrintedOmegaData` — the honest measurement of a FREE `{Ω_j}` parameter.**

Mirrors `CurvedLegWire.omegaDataDegenerate` at the faithful structure: the index map is the
CONSTANT `0`, at every `k`.  A caller who is merely handed the obligation to supply a
`PrintedOmegaData` can supply THIS one and buy nothing — the printed per-cube scale collapses to a
single scale, exactly as `regularUPrinted_at_degenerate_iff` measures on the wire's side.  The
structure constrains `{Ω_j}` to be SELF-CONSISTENT; it cannot, on its own, constrain it to be THE
sequence the RG flow produces.  `omegaWitness` below is the contrast: a tower with two genuinely
nested domains at which the index map takes TWO values. -/
def printedOmegaDegenerate (L : PeriodicLatticeExtent) (k M Lb : ℕ) (hM : 2 ≤ M) (hLb : 1 ≤ Lb) :
    PrintedOmegaData L k M Lb where
  D := degenerateTower L k M Lb hM hLb
  Class := fun C => IsBlockUnionAt M Lb 0 C ∧ 10 * blockSide M Lb 0 ≤ C.side
  idx := fun _ => 0
  idx_le := fun _ _ => Nat.zero_le _
  contained := by
    intro C _ x _
    exact Finset.mem_union_left _ (degenerate_shell_zero hM hLb x)
  meets := by
    intro C hC
    refine ⟨C.base, Finset.mem_inter.mpr ⟨?_, degenerate_shell_zero hM hLb _⟩⟩
    exact PrintedCube.mem_region.mpr (fun μ => ⟨le_rfl, by have := hC.1.2.2; omega⟩)
  bigblock := fun _ hC => hC.1
  floor := fun _ hC => hC.2
  unique := by
    intro C _ j _ _ hmeet _
    by_contra hj
    obtain ⟨z, hz⟩ := hmeet
    exact degenerate_shell_pos hM hLb hj z (Finset.mem_inter.mp hz).2

/-! #### The non-degenerate witness

`M = 2`, `L = 2`, `k = 1`, so big blocks have side `2` at level `0` and side `4` at level `1`.
`Ω_1` is the `4`-aligned box `[0,48)³` and `Ω_0 = T`, two GENUINELY nested domains (`Ω_1 ⊊ Ω_0`).
The shells are then `B^1(Λ_1) = [0,48)³` and `B^0(Λ_0) = ([0,48)³)ᶜ`, and the class carries one cube
in each: `cubeOne = [0,40)³` at printed index `1` (side `40 = 10·4`, the printed floor at level `1`)
and `cubeTwo = [48,68)³` at printed index `0` (side `20 = 10·2`).  **The index map is NOT
constant**, which is exactly what the wire's `regularUPrinted_at_degenerate_iff` identifies as the
whole content of the printed target.

**WHY THE EXTENT IS A PARAMETER AND NOT A NUMERAL — a MEASURED tooling limit, disclosed.**  The
first version of this witness fixed `L := fun _ => 95` (`96` sites per direction, the smallest that
holds `[48,68)³`).  It does not elaborate: at a CONCRETE extent, unifying a `Finset
(PeriodicLatticeSite (fun _ => 95))` against a lemma's `Finset (PeriodicLatticeSite ?L)` diverges
(`maximum recursion depth` / `whnf` heartbeat exhaustion), and the divergence is reproducible on a
three-declaration probe with no content of ours in it
(`compute/formal_batch/dev/Probe3.lean`, `Probe4.lean`).  The witness is therefore stated for EVERY
extent with at least `68` sites per direction — which is STRICTLY STRONGER than one numeral — and
`exists_witnessExtent` below exhibits such an extent, so the hypothesis is not empty.  Nothing
mathematical is weakened: `∀ L, hL → P L` together with `∃ L, hL` gives `∃ L, P L`, and
`exists_printedOmegaData_idx_two_valued` states exactly that. -/

/-- The witness needs `68` sites per direction: `cubeTwo` is `[48,68)³`. -/
def WitnessExtent (L : PeriodicLatticeExtent) : Prop := ∀ μ : Fin 3, 68 ≤ L μ + 1

/-- The hypothesis is not empty: `96` sites per direction. -/
theorem exists_witnessExtent : ∃ L : PeriodicLatticeExtent, WitnessExtent L :=
  ⟨fun _ => 95, fun _ => by show (68 : ℕ) ≤ 95 + 1; omega⟩

/-- `Ω_j^{(j)}` for the witness: all `2`-aligned sites at level `0`; the `4`-aligned sites of
`[0,48)³` at level `1`; nothing above. -/
def witnessOc (L : PeriodicLatticeExtent) : ℕ → Finset (PeriodicLatticeSite L)
  | 0 => CoarseLattice L 2
  | 1 => (CoarseLattice L 4).filter (fun y => ∀ μ : Fin 3, (y μ).val < 48)
  | _ + 2 => ∅

theorem two_pos : (0 : ℕ) < 2 := by norm_num

theorem four_pos : (0 : ℕ) < 4 := by norm_num

theorem bs0 : blockSide 2 2 0 = 2 := by norm_num [blockSide]
theorem bs1 : blockSide 2 2 1 = 4 := by norm_num [blockSide]

theorem witnessOc_zero (L : PeriodicLatticeExtent) : witnessOc L 0 = CoarseLattice L 2 := rfl
theorem witnessOc_one (L : PeriodicLatticeExtent) :
    witnessOc L 1 = (CoarseLattice L 4).filter (fun y => ∀ μ : Fin 3, (y μ).val < 48) := rfl
theorem witnessOc_succ_succ (L : PeriodicLatticeExtent) (n : ℕ) : witnessOc L (n + 2) = ∅ := rfl

def witnessTower (L : PeriodicLatticeExtent) : DomainTower L 1 2 2 where
  Oc := witnessOc L
  hM := by norm_num
  hLb := by norm_num
  hcoarse := by
    intro j
    match j with
    | 0 => rw [bs0, witnessOc_zero]
    | 1 => rw [bs1, witnessOc_one]; exact Finset.filter_subset _ _
    | n + 2 => rw [witnessOc_succ_succ]; exact Finset.empty_subset _
  hnest := by
    intro j
    match j with
    | 0 =>
      intro x _
      rw [bs0, witnessOc_zero]
      exact mem_blowUp_coarseLattice two_pos x
    | 1 =>
      intro x hx
      rw [show (1 : ℕ) + 1 = 2 from rfl, witnessOc_succ_succ L 0, blowUp_empty] at hx
      exact absurd hx (Finset.notMem_empty x)
    | n + 2 =>
      intro x hx
      rw [show n + 2 + 1 = (n + 1) + 2 from by omega, witnessOc_succ_succ,
        blowUp_empty] at hx
      exact absurd hx (Finset.notMem_empty x)
  hstop := by
    intro j hj
    match j with
    | 0 => exact absurd hj (by omega)
    | 1 => exact absurd hj (by omega)
    | n + 2 => exact witnessOc_succ_succ L n

theorem witnessTower_Omega_one (L : PeriodicLatticeExtent) (x : PeriodicLatticeSite L) :
    x ∈ (witnessTower L).Omega 1 ↔ ∀ μ : Fin 3, (x μ).val < 48 := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (witnessTower L).mem_Omega.mp hx
    rw [show (witnessTower L).Oc 1 = witnessOc L 1 from rfl, witnessOc_one] at hy
    obtain ⟨hy4, hylt⟩ := Finset.mem_filter.mp hy
    intro μ
    have h1 := (hyx μ).2
    have h2 := hylt μ
    have h3 := (mem_CoarseLattice.mp hy4) μ
    rw [bs1] at h1
    omega
  · intro hx
    refine (witnessTower L).mem_Omega.mpr ⟨coarseCorner 4 x, ?_, ?_⟩
    · rw [show (witnessTower L).Oc 1 = witnessOc L 1 from rfl, witnessOc_one]
      refine Finset.mem_filter.mpr ⟨coarseCorner_mem_coarseLattice four_pos x, fun μ => ?_⟩
      rw [coarseCorner_val]
      have := hx μ
      omega
    · rw [bs1]
      exact inBlock_coarseCorner four_pos x

theorem witnessTower_Lam_one (L : PeriodicLatticeExtent) :
    (witnessTower L).Lam 1 = witnessOc L 1 := by
  ext y
  rw [DomainTower.mem_Lam]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro hcon
  obtain ⟨w, hw, -⟩ := (witnessTower L).mem_Omega.mp hcon
  rw [show (witnessTower L).Oc (1 + 1) = witnessOc L 2 from rfl, witnessOc_succ_succ] at hw
  exact absurd hw (Finset.notMem_empty w)

theorem witnessTower_Shell_one (L : PeriodicLatticeExtent) (x : PeriodicLatticeSite L) :
    x ∈ (witnessTower L).Shell 1 ↔ ∀ μ : Fin 3, (x μ).val < 48 := by
  rw [DomainTower.mem_Shell, witnessTower_Lam_one, ← witnessTower_Omega_one L x,
    DomainTower.mem_Omega, show (witnessTower L).Oc 1 = witnessOc L 1 from rfl]

theorem witnessTower_Shell_zero (L : PeriodicLatticeExtent) (x : PeriodicLatticeSite L) :
    x ∈ (witnessTower L).Shell 0 ↔ ∃ μ : Fin 3, 48 ≤ (x μ).val := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (witnessTower L).mem_Shell.mp hx
    have hy' := (witnessTower L).mem_Lam.mp hy
    have hnot : ¬ (∀ μ : Fin 3, (y μ).val < 48) := fun hcon =>
      hy'.2 ((witnessTower_Omega_one L y).mpr hcon)
    push_neg at hnot
    obtain ⟨μ, hμ⟩ := hnot
    exact ⟨μ, le_trans hμ (hyx μ).1⟩
  · rintro ⟨μ0, hμ0⟩
    refine (witnessTower L).mem_Shell.mpr ⟨coarseCorner 2 x, ?_, ?_⟩
    · refine (witnessTower L).mem_Lam.mpr ⟨?_, ?_⟩
      · rw [show (witnessTower L).Oc 0 = witnessOc L 0 from rfl, witnessOc_zero]
        exact coarseCorner_mem_coarseLattice two_pos x
      · intro hcon
        have hlt := (witnessTower_Omega_one L _).mp hcon μ0
        rw [coarseCorner_val] at hlt
        omega
    · rw [bs0]
      exact inBlock_coarseCorner two_pos x

/-- `[0,40)³` — side `40 = 10·(M L¹) = 10·4`, the printed floor at level `1`. -/
def cubeOne (L : PeriodicLatticeExtent) (hL : WitnessExtent L) : PrintedCube L where
  base := fun μ => ⟨0, by have := hL μ; omega⟩
  side := 40
  fit := by intro μ; have := hL μ; simpa using by omega

/-- `[48,68)³` — side `20 = 10·(M L⁰) = 10·2`, the printed floor at level `0`, disjoint from
`Ω_1 = [0,48)³`. -/
def cubeTwo (L : PeriodicLatticeExtent) (hL : WitnessExtent L) : PrintedCube L where
  base := fun μ => ⟨48, by have := hL μ; omega⟩
  side := 20
  fit := by intro μ; have := hL μ; simpa using by omega

theorem cubeOne_base_val (L : PeriodicLatticeExtent) (hL : WitnessExtent L) (μ : Fin 3) :
    ((cubeOne L hL).base μ).val = 0 := rfl
theorem cubeOne_side (L : PeriodicLatticeExtent) (hL : WitnessExtent L) :
    (cubeOne L hL).side = 40 := rfl
theorem cubeTwo_base_val (L : PeriodicLatticeExtent) (hL : WitnessExtent L) (μ : Fin 3) :
    ((cubeTwo L hL).base μ).val = 48 := rfl
theorem cubeTwo_side (L : PeriodicLatticeExtent) (hL : WitnessExtent L) :
    (cubeTwo L hL).side = 20 := rfl

theorem cubeTwo_ne_cubeOne (L : PeriodicLatticeExtent) (hL : WitnessExtent L) :
    cubeTwo L hL ≠ cubeOne L hL := by
  intro h
  have hs : (cubeTwo L hL).side = (cubeOne L hL).side := congrArg PrintedCube.side h
  rw [cubeOne_side, cubeTwo_side] at hs
  omega

open Classical in
/-- **THE NON-DEGENERATE `PrintedOmegaData`.**  Two genuinely nested domains, one class cube at
printed index `1` and one at printed index `0`, each index PROVED unique by the printed
three-clause scope. -/
noncomputable def witnessOmega (L : PeriodicLatticeExtent) (hL : WitnessExtent L) :
    PrintedOmegaData L 1 2 2 where
  D := witnessTower L
  Class := fun C => C = cubeOne L hL ∨ C = cubeTwo L hL
  idx := fun C => if C = cubeOne L hL then 1 else 0
  idx_le := by
    intro C hC
    rcases hC with rfl | rfl
    · rw [if_pos rfl]
    · rw [if_neg (cubeTwo_ne_cubeOne L hL)]; omega
  contained := by
    intro C hC x hx
    rcases hC with rfl | rfl
    · rw [if_pos rfl]
      refine Finset.mem_union_left _ ((witnessTower_Shell_one L x).mpr (fun μ => ?_))
      have hx' := (PrintedCube.mem_region.mp hx) μ
      rw [cubeOne_base_val, cubeOne_side] at hx'
      omega
    · rw [if_neg (cubeTwo_ne_cubeOne L hL)]
      refine Finset.mem_union_left _ ((witnessTower_Shell_zero L x).mpr ⟨0, ?_⟩)
      have hx' := (PrintedCube.mem_region.mp hx) 0
      rw [cubeTwo_base_val] at hx'
      omega
  meets := by
    intro C hC
    rcases hC with rfl | rfl
    · rw [if_pos rfl]
      refine ⟨(cubeOne L hL).base, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · refine PrintedCube.mem_region.mpr (fun μ => ⟨le_rfl, ?_⟩)
        rw [cubeOne_base_val, cubeOne_side]
        omega
      · refine (witnessTower_Shell_one L _).mpr (fun μ => ?_)
        rw [cubeOne_base_val]
        omega
    · rw [if_neg (cubeTwo_ne_cubeOne L hL)]
      refine ⟨(cubeTwo L hL).base, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · refine PrintedCube.mem_region.mpr (fun μ => ⟨le_rfl, ?_⟩)
        rw [cubeTwo_base_val, cubeTwo_side]
        omega
      · refine (witnessTower_Shell_zero L _).mpr ⟨0, ?_⟩
        rw [cubeTwo_base_val]
  bigblock := by
    intro C hC
    rcases hC with rfl | rfl
    · rw [if_pos rfl]
      refine ⟨fun μ => ?_, ?_, ?_⟩
      · rw [bs1, cubeOne_base_val]
      · rw [bs1, cubeOne_side]; exact ⟨10, rfl⟩
      · rw [cubeOne_side]; omega
    · rw [if_neg (cubeTwo_ne_cubeOne L hL)]
      refine ⟨fun μ => ?_, ?_, ?_⟩
      · rw [bs0, cubeTwo_base_val]
      · rw [bs0, cubeTwo_side]; exact ⟨10, rfl⟩
      · rw [cubeTwo_side]; omega
  floor := by
    intro C hC
    rcases hC with rfl | rfl
    · rw [if_pos rfl, bs1, cubeOne_side]
    · rw [if_neg (cubeTwo_ne_cubeOne L hL), bs0, cubeTwo_side]
  unique := by
    intro C hC j hjk _ hmeet _
    rcases hC with rfl | rfl
    · rw [if_pos rfl]
      obtain ⟨z, hz⟩ := hmeet
      have hzr := PrintedCube.mem_region.mp (Finset.mem_inter.mp hz).1
      have hzs := (Finset.mem_inter.mp hz).2
      interval_cases j
      · exfalso
        obtain ⟨μ, hμ⟩ := (witnessTower_Shell_zero L z).mp hzs
        have hzμ := hzr μ
        rw [cubeOne_base_val, cubeOne_side] at hzμ
        omega
      · rfl
    · rw [if_neg (cubeTwo_ne_cubeOne L hL)]
      obtain ⟨z, hz⟩ := hmeet
      have hzr := PrintedCube.mem_region.mp (Finset.mem_inter.mp hz).1
      have hzs := (Finset.mem_inter.mp hz).2
      interval_cases j
      · rfl
      · exfalso
        have h48 := (witnessTower_Shell_one L z).mp hzs 0
        have hz0 := hzr 0
        rw [cubeTwo_base_val] at hz0
        omega

open Classical in
/-- **THE INDEX MAP OF THE WITNESS TAKES TWO VALUES.** -/
theorem witnessOmega_idx_two_valued (L : PeriodicLatticeExtent) (hL : WitnessExtent L) :
    (witnessOmega L hL).idx (cubeOne L hL) = 1
      ∧ (witnessOmega L hL).idx (cubeTwo L hL) = 0 := by
  constructor
  · show (if cubeOne L hL = cubeOne L hL then 1 else 0) = 1
    rw [if_pos rfl]
  · show (if cubeTwo L hL = cubeOne L hL then 1 else 0) = 0
    rw [if_neg (cubeTwo_ne_cubeOne L hL)]

/-- The two class cubes carry DIFFERENT bond sets — the corner bond of `cubeOne` is not a bond of
`cubeTwo`.  This is what makes the transported index map two-valued as well. -/
theorem cubeOne_bonds_ne_cubeTwo_bonds (L : PeriodicLatticeExtent) (hL : WitnessExtent L) :
    (cubeOne L hL).bonds ≠ (cubeTwo L hL).bonds := by
  intro h
  have hb : (((cubeOne L hL).base, 0) : Bond L) ∈ (cubeOne L hL).bonds := by
    refine PrintedCube.mem_bonds.mpr ⟨?_, ?_⟩
    · show inBlock (cubeOne L hL).base (cubeOne L hL).side (cubeOne L hL).base
      intro μ
      rw [cubeOne_base_val, cubeOne_side]
      omega
    · show inBlock (cubeOne L hL).base (cubeOne L hL).side
        (periodicLatticeShift (cubeOne L hL).base 0)
      intro μ
      by_cases hμ : μ = 0
      · subst hμ
        rw [shift_val_self (by rw [cubeOne_base_val]; have := hL 0; omega),
          cubeOne_base_val, cubeOne_side]
        omega
      · rw [shift_val_of_ne hμ]
        exact ⟨le_rfl, by rw [cubeOne_base_val, cubeOne_side]; omega⟩
  rw [h] at hb
  have hbase := (PrintedCube.mem_bonds.mp hb).1 0
  rw [cubeTwo_base_val] at hbase
  have h0 : (((cubeOne L hL).base, (0 : Fin 3)) : Bond L).1 0 = (cubeOne L hL).base 0 := rfl
  rw [h0, cubeOne_base_val] at hbase
  omega

open Classical in
/-- **THE PROJECTED WIRE-SHAPE INDEX IS TWO-VALUED TOO** — so the `OmegaData` the wire's
`RegularUPrinted` is stated over is, at this instance, NOT the degenerate constant-index one, and
the printed per-cube scale `L^{idx □}` genuinely varies over the class. -/
theorem witnessOmega_wire_idx_two_valued (L : PeriodicLatticeExtent) (hL : WitnessExtent L) :
    (witnessOmega L hL).toWireShape.idx (cubeOne L hL).bonds = 1
      ∧ (witnessOmega L hL).toWireShape.idx (cubeTwo L hL).bonds = 0 := by
  constructor
  · obtain ⟨C, hC, hbonds, hidx⟩ :=
      (witnessOmega L hL).idxOf_spec ⟨cubeOne L hL, Or.inl rfl, rfl⟩
    have hC1 : C = cubeOne L hL := by
      rcases hC with rfl | rfl
      · rfl
      · exact absurd hbonds (cubeOne_bonds_ne_cubeTwo_bonds L hL)
    show (witnessOmega L hL).idxOf (cubeOne L hL).bonds = 1
    rw [hidx, hC1]
    exact (witnessOmega_idx_two_valued L hL).1
  · obtain ⟨C, hC, hbonds, hidx⟩ :=
      (witnessOmega L hL).idxOf_spec ⟨cubeTwo L hL, Or.inr rfl, rfl⟩
    have hC2 : C = cubeTwo L hL := by
      rcases hC with rfl | rfl
      · exact absurd hbonds.symm (cubeOne_bonds_ne_cubeTwo_bonds L hL)
      · rfl
    show (witnessOmega L hL).idxOf (cubeTwo L hL).bonds = 0
    rw [hidx, hC2]
    exact (witnessOmega_idx_two_valued L hL).2

/-- **NON-VACUITY, IN ONE STATEMENT.**  There IS an extent, and on it a `PrintedOmegaData` whose
printed index map takes two different values on the class — so `PrintedOmegaData` is inhabited by
something the degenerate constant-index instance is not. -/
theorem exists_printedOmegaData_idx_two_valued :
    ∃ (L : PeriodicLatticeExtent) (P : PrintedOmegaData L 1 2 2)
      (C₁ C₂ : PrintedCube L), P.Class C₁ ∧ P.Class C₂ ∧ P.idx C₁ = 1 ∧ P.idx C₂ = 0 := by
  obtain ⟨L, hL⟩ := exists_witnessExtent
  exact ⟨L, witnessOmega L hL, cubeOne L hL, cubeTwo L hL, Or.inl rfl, Or.inr rfl,
    (witnessOmega_idx_two_valued L hL).1, (witnessOmega_idx_two_valued L hL).2⟩

/-! ### §17g — axiom audit for §17 -/

#print axioms interiorCubeBondsF_card
#print axioms carrier_gap_at_ten
#print axioms DomainTower.shell_disjoint
#print axioms PrintedOmegaData.blockCorner_mem_region
#print axioms PrintedOmegaData.two_clause_rigid
#print axioms PrintedOmegaData.toWireShape
#print axioms printedOmegaDegenerate
#print axioms witnessTower_Shell_zero
#print axioms witnessTower_Shell_one
#print axioms witnessOmega
#print axioms witnessOmega_idx_two_valued
#print axioms cubeOne_bonds_ne_cubeTwo_bonds
#print axioms witnessOmega_wire_idx_two_valued
#print axioms exists_printedOmegaData_idx_two_valued

end AdalyFormal.Balaban.RegularityGap
