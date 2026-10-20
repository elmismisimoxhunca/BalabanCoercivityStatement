/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantHjFaithful
import AdalyFormal.Balaban.CovU1Reduction

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[U1-LEADING-COERC]` — the `U=1` base case of the leading-term coercivity: a REFUTATION + the
explicit `C`-reduction step

**Dispatch.** CHARACTERIZE then BUILD the `U=1` base case of the leading-term inequality
`deltaJ ≥ γ'‖·‖²_coarse` the su(2) `C*Δ_kC` coercivity reduces to, i.e.
`CovariantHjFaithful.FaithfulCovCoercivityTarget witnessEll levels (trivialU)`, by connecting it to
Balaban's proved Lemma 2.4 / CMP96 (2.128).

## CHARACTERIZATION (the `C`-reduction, source-pinned) — the target is FALSE, so no reduction exists

The dispatch's characterize question — *is `deltaJ(trivialU) ≥ γ'‖B‖²` a consequence of (2.128), or
does it need the full (3.157)-(3.158) `C`-reduction?* — has a **negative answer**: the U=1 base case
of the target is **FALSE as written** (`∀ A0`), so no TRUE hypothesis (Balaban's Lemma 2.4 included)
can imply it.

**Root cause (source-pinned).**
* The Lean `deltaJQuadFormCovFaithful` is the pure MINIMIZED CURL energy `‖D_U H_j B‖²`. It VANISHES
  on the curl-kernel — in particular on CONSTANT bond fields (`CovU1Reduction.flatCurlValue_const_eq
  _zero`: `curl(trivialU)(const v)=0`), which have NONZERO faithful coarse average
  (`LineIntegralCovariant.lineCoarseRestrictCov_const_witness`: `Q₁(trivialU)(const v)=v`).
* Balaban's coercive object (CMP99b (3.156), adjudicated `corpus/pages/CMP99b_p428.md`) is
  `⟨B,Δ_kB⟩ = ⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩`. `(QG₁Q*)⁻¹` is POSITIVE-DEFINITE because it
  is the Schur complement of the FULL fluctuation action (curl **+** averaging mass `aQ*Q` **+**
  `Δ⁽²⁾`), NOT curl alone — which is exactly why CMP96 (2.128) keeps the coarse term
  `ell·‖Q₁B‖²` ADDITIVELY: `ell‖Q₁B‖² + ‖curl B‖² ≥ c‖B‖²` (`BlockPoincareLemma24.Lemma24Conclusion`,
  the Lean transcription of (2.128)). The curl alone does not control constants; the additive coarse
  term does.
* Balaban's Lemma 2.4 / `C*Δ_kC ≥ γ₀` (p.428) is moreover considered on the FLUCTUATION subspace
  `{B : …, Q₁B=0}` (p.428 verbatim: *"This form is considered on the subspace {B : …, Q₁B=0}. We can
  parametrize this subspace … B = C B̃"*), where the coarse term drops and it bounds the FINE norm.
  The target needs a bound against the COARSE norm on the FULL space — a different object, related to
  Balaban's only through the FULL covariance `(QG₁Q*)⁻¹`, whose positive-definiteness the pure-curl
  Lean proxy `deltaJ` DROPS.
* Balaban's own (2.128)/Lemma 2.4 in this tree (`GeomGlobal.lemma24_unconditional_U1_ell2`) is stated
  on `admissibleSubspaceInter` (the axial/staircase gauge), which EXCLUDES exactly the
  constant/harmonic curl-kernel modes. The faithful target carries NO such restriction (`∀ A0`), so
  it is strictly STRONGER than anything Balaban proves — and false.

**Corrected (reducible) targets** (named, NOT built here): restrict `∀ A0` to an
`admissibleSubspaceInter`-analogue (axial gauge, excluding curl-kernel coarse modes); OR bound the
SUM `ell‖Q₁A0‖² + deltaJ(A0)` (the genuine (2.128) LHS); OR carry the mass term `⟨B,(QG₁Q*)⁻¹B⟩`
rather than the pure-curl proxy. These, and the outright refutation of the k-UNIFORM target, are
assembled downstream in `CoercivityTargetsCorrected.lean`.

**GRADE-2 CLARIFICATION (2026-07-26, `compute/sol_deltak_readjudicate/SOL_VERDICT.md`).** The
averaging mass in (3.156) `Δ_k` CANCELS exactly against the leading Schur mass, so at `U=1`
`Δ_k = deltaJ` (pure minimized curl; `DeltaKSuTwoAssembly.deltaK_at_U1_eq_deltaJ`). Thus `deltaJ` is
NOT merely a "proxy" for `Δ_k` — it IS `Δ_k` at `U=1`. The §5 refutation below is therefore a
refutation of the unrestricted coercivity of `Δ_k` ITSELF, not of a proxy; the pre-cancellation
`(QG₁Q*)⁻¹` (= `deltaJ + a‖B‖²`) is a distinct object that is never the coercive target.

## What is built (all kernel-checked, `#print axioms` at each brick)

1. §1 `deltaJQuadFormCovFaithful_eq_zero_of_curl_zero` — `U`-general: a curl-free field has zero
   minimized curl energy.
2. §2 `curlCovariantLM_trivialU_const_eq_zero` / `deltaJQuadFormCovFaithful_trivialU_const_eq_zero`
   — a constant field is curl-free at `U=1`, so `deltaJ(trivialU)(const)=0`.
3. §3 `covCoarseBondInner_Q_trivialU_const_witness_pos` — the faithful coarse norm of `Q₁(const)` is
   STRICTLY POSITIVE on the witness (true block average `= v ≠ 0`).
4. §4 `compatibleExtent_witness` — `CompatibleExtent witnessL witnessEll`.
5. §5 **`faithfulCovCoercivityTarget_trivialU_witness_false`** — THE REFUTATION.
6. §6 `GaugeFixedCurlCoercivity` + `faithfulCovCoercivity_of_gaugeFixedCurlCoercivity` — the explicit
   `C`-reduction step: the target (on gauge-fixed inputs) reduces to the gauge-fixed curl-vs-coarse
   coercivity `γ₀‖Q₁A‖² ≤ ‖curl A‖²`. Non-circular (hypothesis is over ALL gauge-fixed `A`, and uses
   the RAW curl energy, not the minimized `deltaJ`). Localizes the obstruction to the curl-kernel
   modes with nonzero coarse average (constants) — exactly what Balaban's axial-gauge
   `admissibleSubspaceInter` excludes.

## Honesty / scope
* **ISLAND.** Nothing here is wired to any consumed spine declaration. This is a REFUTATION of a bare
  `def : Prop` target plus a reduction lemma; NO coercivity is proved (none is true as stated).
* **`U=1` ONLY.** The regular-`U` case (open frontier) is untouched.
* Does NOT touch `GeomGlobal`/`Ell2RefBlock` (parallel `Href` lane), read-only reuse elsewhere.
-/

namespace AdalyFormal.Balaban.U1LeadingCoercivity

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.KernelSubspace
  AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.Balaban.LineIntegralCovariant
  AdalyFormal.Balaban.CovariantHjFaithful
  AdalyFormal.Balaban.CovU1Reduction
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — a curl-free field has zero minimized curl energy (`U`-general) -/

/-- The faithful closest-point projection fixes `0`. -/
theorem curlImageCovProjFaithful_zero (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection] :
    curlImageCovProjFaithful ell levels U 0 = 0 := by
  unfold curlImageCovProjFaithful
  simp only [map_zero]

/-- **`curl A0 = 0 ⇒ deltaJ = 0`** — if the covariant curl of the particular solution vanishes, its
Balaban harmonic extension has zero curl (the closest-point correction of `0` is `0`), so the
minimized curl energy `deltaJQuadFormCovFaithful = ‖D_U H_j‖²` is `0`. Holds for EVERY `U`. -/
theorem deltaJQuadFormCovFaithful_eq_zero_of_curl_zero (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (h : curlCovariantLM U A0 = 0) :
    deltaJQuadFormCovFaithful ell levels U A0 = 0 := by
  have hcurl : curlCovariantLM U (hjExtensionCovFaithful ell levels U A0) = 0 := by
    rw [curlCov_hjExtensionCovFaithful]
    unfold hjCorrectionTargetCovFaithful
    rw [h, curlImageCovProjFaithful_zero, sub_zero]
  unfold deltaJQuadFormCovFaithful
  rw [hcurl]
  have hz : hsInner (0 : SuTwo) (0 : SuTwo) = 0 := by
    rw [← hsInnerLeftLM_apply]; exact map_zero _
  unfold covPlaqInner
  simp only [Pi.zero_apply, hz, Finset.sum_const_zero]

#print axioms curlImageCovProjFaithful_zero
#print axioms deltaJQuadFormCovFaithful_eq_zero_of_curl_zero

/-! ## §2 — a CONSTANT field is curl-free at `U=1`, hence `deltaJ(trivialU)(const) = 0` -/

/-- **`curl(trivialU)(const v) = 0`** — the `U=1` covariant curl is the flat curl
(`CovU1Reduction.curlCovariantLM_trivialU_eq_flatCurlLM`), and the flat curl of a constant is
`v+v−v−v = 0` (`CovU1Reduction.flatCurlValue_const_eq_zero`). -/
theorem curlCovariantLM_trivialU_const_eq_zero (v : SuTwo) :
    curlCovariantLM (trivialU L) (fun _ : Bond L => v) = 0 := by
  rw [curlCovariantLM_trivialU_eq_flatCurlLM]
  show flatCurlValue (fun _ : Bond L => v) = 0
  exact flatCurlValue_const_eq_zero v

/-- **`deltaJQuadFormCovFaithful (trivialU) (const v) = 0`** for EVERY `v` — the constant field is
curl-free at `U=1`, so its minimized curl energy is `0` (mirrors, on the FAITHFUL/covariant carrier,
`CovU1Reduction.deltaJQuadFormCov_ell1_trivialU_const_eq_zero`, now at ANY `ell`/`levels`). -/
theorem deltaJQuadFormCovFaithful_trivialU_const_eq_zero (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels (trivialU L)).HasOrthogonalProjection]
    (v : SuTwo) :
    deltaJQuadFormCovFaithful ell levels (trivialU L) (fun _ : Bond L => v) = 0 :=
  deltaJQuadFormCovFaithful_eq_zero_of_curl_zero ell levels (trivialU L) _
    (curlCovariantLM_trivialU_const_eq_zero v)

#print axioms curlCovariantLM_trivialU_const_eq_zero
#print axioms deltaJQuadFormCovFaithful_trivialU_const_eq_zero

/-! ## §3 — the faithful coarse norm of `Q₁(const)` is STRICTLY POSITIVE on the witness -/

/-- **`Q₁(trivialU)(const suTwoWitness) ≠ 0`** on the witness lattice — the faithful covariant `Q` is
a TRUE block average, `lineCoarseRestrictCov (trivialU) witnessEll (const v) (targetCoarseBond) = v`
(`LineIntegralCovariant.lineCoarseRestrictCov_const_witness`), and `suTwoWitness ≠ 0`. -/
theorem Q_trivialU_const_witness_ne_zero :
    lineCoarseRestrictCovLM (trivialU witnessL) witnessEll (fun _ : Bond witnessL => suTwoWitness)
      ≠ 0 := by
  intro h
  have hc := congrFun h (⟨witnessY, witnessY_coarse⟩, 0)
  rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_const_witness, Pi.zero_apply] at hc
  exact suTwoWitness_ne_zero hc

/-- **The faithful coarse norm of `Q₁(const suTwoWitness)` is strictly positive** — positive-DEFINITE
`covCoarseBondInner` (`CovariantHjFaithful.covCoarseBondInner_pos_of_ne`) at a nonzero coarse field. -/
theorem covCoarseBondInner_Q_trivialU_const_witness_pos :
    0 < covCoarseBondInner
        (lineCoarseRestrictCovLM (trivialU witnessL) witnessEll (fun _ : Bond witnessL => suTwoWitness))
        (lineCoarseRestrictCovLM (trivialU witnessL) witnessEll (fun _ : Bond witnessL => suTwoWitness)) :=
  covCoarseBondInner_pos_of_ne Q_trivialU_const_witness_ne_zero

#print axioms Q_trivialU_const_witness_ne_zero
#print axioms covCoarseBondInner_Q_trivialU_const_witness_pos

/-! ## §4 — `CompatibleExtent witnessL witnessEll` -/

/-- **`CompatibleExtent witnessL witnessEll`** — `0 < 2` and `2 ∣ (3+1) = 2∣4` (`witnessL ≡ 3`,
`witnessEll = 2`). So the refutation below FIRES the target's antecedent (it is not vacuous). -/
theorem compatibleExtent_witness : CompatibleExtent witnessL witnessEll := by
  refine ⟨by norm_num [witnessEll], fun μ => ?_⟩
  show (witnessEll : ℕ) ∣ (witnessL μ + 1)
  norm_num [witnessEll, witnessL]

#print axioms compatibleExtent_witness

/-! ## §5 — THE REFUTATION: the `U=1` base case of the leading-term coercivity is FALSE -/

/-- **THE `U=1` BASE CASE OF THE LEADING-TERM COERCIVITY IS FALSE.** There is NO `γ₀ > 0` with
`γ₀·covCoarseBondInner (Q₁A0) (Q₁A0) ≤ deltaJQuadFormCovFaithful witnessEll [] (trivialU) A0` for all
`A0`: the CONSTANT field `A0 ≡ suTwoWitness` makes the RHS `0` (curl-free at `U=1`) while the LHS is
strictly positive (`Q₁(const) = suTwoWitness ≠ 0`, true block average). Hence
`FaithfulCovCoercivityTarget witnessEll [] (trivialU witnessL)` does NOT hold — and since Balaban's
Lemma 2.4 / (2.128) is TRUE, NO reduction `[Lemma 2.4] ⟹ target` can exist. See the module docstring
for the source-pinned root cause (pure-curl `deltaJ` drops the mass/covariance that makes Balaban's
`(QG₁Q*)⁻¹` positive-definite; (2.128) is stated on the axial-gauge `admissibleSubspaceInter`, which
excludes the curl-kernel constant modes). -/
theorem faithfulCovCoercivityTarget_trivialU_witness_false :
    ¬ FaithfulCovCoercivityTarget witnessEll ([] : List (KernelSubspace.Level witnessL))
        (trivialU witnessL) := by
  unfold FaithfulCovCoercivityTarget
  intro htarget
  obtain ⟨γ₀, hγ, hbound⟩ := htarget compatibleExtent_witness
  have hle := hbound (fun _ : Bond witnessL => suTwoWitness)
  rw [deltaJQuadFormCovFaithful_trivialU_const_eq_zero witnessEll
    ([] : List (KernelSubspace.Level witnessL)) suTwoWitness] at hle
  have hpos := covCoarseBondInner_Q_trivialU_const_witness_pos
  nlinarith [mul_pos hγ hpos]

#print axioms faithfulCovCoercivityTarget_trivialU_witness_false

/-! ## §6 — the explicit `C`-reduction step: which coercivity WOULD suffice (and where it fails) -/

/-- **`GaugeFixedCurlCoercivity` — the gauge-fixed curl-vs-coarse coercivity.** For every GAUGE-FIXED
field `A` (`RcovLM U levels (D_U^* A) = 0`), the RAW curl energy `‖D_U A‖²` dominates `γ₀` times the
coarse-field `L²` norm `‖Q₁A‖²`. This is the honest Schur-reduced form of the coarse coercivity the
target needs — genuinely DIFFERENT from the target (it quantifies over ALL gauge-fixed `A`, using the
raw curl energy, not the minimized `deltaJ` of a single harmonic extension). `def : Prop` only. -/
def GaugeFixedCurlCoercivity (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (γ₀ : ℝ) : Prop :=
  ∀ A : Bond L → SuTwo, RcovLM U levels (gradCovariantAdjointLM U A) = 0 →
    γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A) (lineCoarseRestrictCovLM U ell A)
      ≤ covPlaqInner (curlCovariantLM U A) (curlCovariantLM U A)

/-- The harmonic extension preserves the coarse field: `Q₁(H_j A0) = Q₁ A0` (the correction lies in
`ker Q₁`, first clause of `gaugeConstraintSubspaceCovFaithful`). -/
theorem lineCoarseRestrict_hjExtensionCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    lineCoarseRestrictCovLM U ell (hjExtensionCovFaithful ell levels U A0) =
      lineCoarseRestrictCovLM U ell A0 := by
  unfold hjExtensionCovFaithful
  rw [map_add,
    (mem_gaugeConstraintSubspaceCovFaithful.mp (hjCorrectionCovFaithful_mem ell levels U A0)).1,
    add_zero]

/-- The harmonic extension preserves gauge-fixedness: if `A0` is gauge-fixed so is `H_j A0` (the
correction is gauge-fixed too, second clause of `gaugeConstraintSubspaceCovFaithful`). -/
theorem gaugeFixed_hjExtensionCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo)
    (h : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    RcovLM U levels (gradCovariantAdjointLM U (hjExtensionCovFaithful ell levels U A0)) = 0 := by
  unfold hjExtensionCovFaithful
  rw [map_add, map_add, h,
    (mem_gaugeConstraintSubspaceCovFaithful.mp (hjCorrectionCovFaithful_mem ell levels U A0)).2,
    add_zero]

/-- **THE `C`-REDUCTION STEP, PROVED.** Given the gauge-fixed curl-vs-coarse coercivity
`GaugeFixedCurlCoercivity … γ₀`, the leading-term target inequality
`γ₀‖Q₁A0‖² ≤ deltaJQuadFormCovFaithful A0` holds for every GAUGE-FIXED `A0`. Mechanism: apply the
hypothesis to the harmonic extension `H_j A0` (still gauge-fixed, same coarse field), and use
`deltaJ = ‖D_U H_j A0‖²` by definition. This is the explicit `C`-reduction the dispatch asked to make
precise — it exhibits EXACTLY the coercivity that would suffice.

**Where it fails, localized.** The refutation §5 shows the target is false via the CONSTANT field
`A0 ≡ suTwoWitness` — a curl-kernel mode (`curl(trivialU)(const)=0`) with nonzero coarse average.
Should that constant be gauge-fixed (i.e. `RcovLM U levels (D_U^*(const)) = 0`, which depends on
`levels` — at `levels=[]` the kernel subspace is `⊤`, so `RcovLM []` projects onto the FULL Laplacian
range and gauge-fixedness of the constant is NOT automatic, hence NOT asserted here), this reduction
forces `¬ GaugeFixedCurlCoercivity`. In every case the obstruction is the SAME class — curl-kernel
modes with nonzero coarse average — which is precisely what Balaban's axial-gauge
`admissibleSubspaceInter` (the domain of (2.128)/Lemma 2.4) EXCLUDES. NON-CIRCULAR: the hypothesis is
over ALL gauge-fixed `A`, using the raw curl energy, not the per-extension minimized `deltaJ`. -/
theorem faithfulCovCoercivity_of_gaugeFixedCurlCoercivity (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (γ₀ : ℝ) (hGF : GaugeFixedCurlCoercivity ell levels U γ₀)
    (A0 : Bond L → SuTwo) (hA0 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0)
      ≤ deltaJQuadFormCovFaithful ell levels U A0 := by
  have key := hGF (hjExtensionCovFaithful ell levels U A0)
    (gaugeFixed_hjExtensionCovFaithful ell levels U A0 hA0)
  rw [lineCoarseRestrict_hjExtensionCovFaithful] at key
  unfold deltaJQuadFormCovFaithful
  exact key

#print axioms lineCoarseRestrict_hjExtensionCovFaithful
#print axioms gaugeFixed_hjExtensionCovFaithful
#print axioms faithfulCovCoercivity_of_gaugeFixedCurlCoercivity

end AdalyFormal.Balaban.U1LeadingCoercivity
