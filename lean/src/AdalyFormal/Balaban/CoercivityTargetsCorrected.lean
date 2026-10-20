/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CStarDeltaKCCompose
import AdalyFormal.Balaban.U1LeadingCoercivity

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[COERC-TARGETS-CORRECTED]` — the grade-2 re-adjudication of the su(2) coercivity targets

**Owner-ordered correction (2026-07-26).** A grade-2 re-adjudication (Sol page-image read
`compute/sol_deltak_readjudicate/SOL_VERDICT.md` + the Lean refutation
`U1LeadingCoercivity.faithfulCovCoercivityTarget_trivialU_witness_false`) established:

1. **`Δ_k = deltaJ` at `U=1`.** CMP99b (3.128) gives the leading Schur complement
   `⟨B,(QG₁Q*)⁻¹B⟩ = min_{QA=B}[curl] + a‖B‖²`, and (3.156) `Δ_k = (QG₁Q*)⁻¹ − a⟨B,B⟩` subtracts the
   SAME averaging mass, so it CANCELS: `Δ_k = min_{QA=B}[curl]`. At `U=1`, `J=0` and `Δ'=0` (p.392),
   so `Δ_k = deltaJ` (pure minimized curl, `DeltaKSuTwoAssembly.deltaK_at_U1_eq_deltaJ`). The
   mass-subtracted `deltaKSuTwoForm a` (a≠0) is therefore NOT `Δ_k`.

2. **Balaban's coercivity is DOMAIN-RESTRICTED.** `C*Δ_kC ≥ γ₀` (CMP99b p.428) is stated on the
   supported, axial-gauge, `Q₁B=0` fluctuation subspace, reparametrized by free bonds `B̃` (`B=CB̃`);
   it bounds the FREE-bond norm, NEVER all fields (SOL_VERDICT.md Q3). The unrestricted `∀ A0` bound
   `γ₀‖Q₁A0‖² ≤ deltaJ` is FALSE: the constant field at `U=1` is curl-free (`deltaJ=0`) with nonzero
   coarse average (`‖Q₁(const)‖²>0`).

3. **The correct `U=1` coercive object is CMP96 (2.128)** on the axial-gauge domain:
   `L^{d-2}·Σ_c|Q₁B|² + Σ_p|∂₁B|² ≥ (1/(12d²))·L^{d-1}‖B‖²` — the coarse-average term ESSENTIAL. In
   this tree that is the SCALAR `GeomGlobal.GeomInequality`/`GeomGlobal.Lemma24Conclusion` on
   `admissibleSubspaceInter` (the axial/staircase gauge), an Href-lane `sorry` we do NOT touch.

## What this module does (all kernel-checked, `#print axioms` at each brick; no `sorry`/`axiom`)

* §1 **Refutations of the unrestricted targets** — the `∀ A0` (all-field) targets are FALSE, not
  open. `faithfulCovCoercivityTargetUniform_false`, `deltaKSuTwoCoercivityTarget_witness_false`
  (`0 ≤ a`), `deltaKSuTwoCoercivityTargetUniform_false` (`0 ≤ a`). Each reuses the constant-field
  witness (LAW-19).
* §2 **The corrected DOMAIN-RESTRICTED target** `FaithfulCovCoercivityTargetGaugeFixed` (gauge-fixed
  inputs only) and its PROVED reduction to `U1LeadingCoercivity.GaugeFixedCurlCoercivity` (the su(2)
  curl-vs-coarse coercivity) via the existing `faithfulCovCoercivity_of_gaugeFixedCurlCoercivity`.
* §3 **The named link to CMP96 (2.128)** — `SuTwoGeomAdditiveInequality`, the su(2) analogue of the
  scalar `GeomGlobal.GeomInequality`/`Lemma24Conclusion` (curl PLUS the essential coarse-average term
  controlling the fine field), stated as a `def : Prop` and connected in prose to the Href-blocked
  scalar object on `admissibleSubspaceInter`. NOT proved here.

## Honesty / scope

* **ISLAND.** Nothing here is wired to `coerc_u_main` or any consumed spine declaration.
* **The corrected target is a `def : Prop`, NOT asserted true.** Its reduction to
  `GaugeFixedCurlCoercivity` is proved; whether that su(2) curl-vs-coarse coercivity HOLDS is the open
  content, and matches CMP96 (2.128) on the AXIAL gauge. The mere gauge-fixed restriction is the
  reduction target of the existing proved lemma; the FULLY faithful Balaban domain additionally
  imposes the axial condition (2.121) (`admissibleSubspaceInter`), which provably excludes the
  curl-kernel constant modes that refute the unrestricted target (a raw constant fails (2.121)).
* **Carrier note.** `GeomGlobal.GeomInequality` is over `Bond L → ℝ`; the su(2) objects are over
  `Bond L → SuTwo`. The §3 link is the su(2) analogue by name, NOT a cross-carrier proof — the scalar
  (2.128) itself is the Href-lane `sorry` (`GeomGlobal.geomInequality_of_admissible_ell2`).
-/

namespace AdalyFormal.Balaban.CoercivityTargetsCorrected

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.KernelSubspace
  AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.Balaban.LineIntegralCovariant
  AdalyFormal.Balaban.CovariantHjFaithful
  AdalyFormal.Balaban.DeltaKSuTwoAssembly
  AdalyFormal.Balaban.U1LeadingCoercivity
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — REFUTATIONS of the unrestricted (`∀ A0`) coercivity targets -/

/-- **THE k-UNIFORM FAITHFUL TARGET IS FALSE.** `FaithfulCovCoercivityTargetUniform` fixes ONE
`γ₀ > 0` for all `(L, ell, levels, U)`; its witness member `FaithfulCovCoercivityTarget witnessEll []
(trivialU witnessL)` is refuted by `faithfulCovCoercivityTarget_trivialU_witness_false` (constant
field at `U=1`). `RegularBackground` is the `True` placeholder, so it does not shield `trivialU`. -/
theorem faithfulCovCoercivityTargetUniform_false : ¬ FaithfulCovCoercivityTargetUniform := by
  rintro ⟨γ₀, hγ, h⟩
  apply faithfulCovCoercivityTarget_trivialU_witness_false
  intro _hcompat
  exact ⟨γ₀, hγ,
    h witnessL witnessEll ([] : List (KernelSubspace.Level witnessL)) (trivialU witnessL)
      compatibleExtent_witness trivial⟩

#print axioms faithfulCovCoercivityTargetUniform_false

/-- **THE UNRESTRICTED `deltaKSuTwoForm` TARGET IS FALSE at the witness (`0 ≤ a`).** The constant
field `A0 ≡ suTwoWitness` at `U=1` has `deltaJ = 0` (curl-free) and coarse norm `m > 0`, so
`deltaKSuTwoForm a … (const) = 0 − a·m = −a·m ≤ 0 < γ₀·m` for `γ₀ > 0`, `a ≥ 0` — no such `γ₀`
exists. (For `a > 0` it is strictly more negative than the `a=0` leading refutation.) -/
theorem deltaKSuTwoCoercivityTarget_witness_false (a : ℝ) (ha : 0 ≤ a) :
    ¬ DeltaKSuTwoCoercivityTarget a witnessEll ([] : List (KernelSubspace.Level witnessL))
        (trivialU witnessL) := by
  intro htarget
  obtain ⟨γ₀, hγ, hbound⟩ := htarget compatibleExtent_witness
  have hle := hbound (fun _ : Bond witnessL => suTwoWitness)
  rw [DeltaKSuTwoAssembly.deltaKSuTwoForm,
    deltaJQuadFormCovFaithful_trivialU_const_eq_zero witnessEll
      ([] : List (KernelSubspace.Level witnessL)) suTwoWitness] at hle
  have hpos := covCoarseBondInner_Q_trivialU_const_witness_pos
  nlinarith [mul_pos hγ hpos, mul_nonneg ha (le_of_lt hpos)]

#print axioms deltaKSuTwoCoercivityTarget_witness_false

/-- **THE k-UNIFORM `deltaKSuTwoForm` TARGET IS FALSE (`0 ≤ a`).** Its witness member is the target
refuted just above. -/
theorem deltaKSuTwoCoercivityTargetUniform_false (a : ℝ) (ha : 0 ≤ a) :
    ¬ DeltaKSuTwoCoercivityTargetUniform a := by
  rintro ⟨γ₀, hγ, h⟩
  apply deltaKSuTwoCoercivityTarget_witness_false a ha
  intro _hcompat
  exact ⟨γ₀, hγ,
    h witnessL witnessEll ([] : List (KernelSubspace.Level witnessL)) (trivialU witnessL)
      compatibleExtent_witness trivial⟩

#print axioms deltaKSuTwoCoercivityTargetUniform_false

/-! ## §2 — the CORRECTED domain-restricted target and its reduction to (2.128)-on-fluctuation -/

/-- **THE CORRECTED (DOMAIN-RESTRICTED) COERCIVITY TARGET — `def : Prop`, NOT asserted.** The
faithful `⟨B,Δ_k B⟩ ≥ γ₀‖Q₁·‖²` bound, quantified ONLY over GAUGE-FIXED inputs
(`RcovLM U levels (D_U^* A0) = 0`), on the COMPATIBLE domain — matching Balaban's actual claim
(`C*Δ_kC ≥ γ₀` is on the gauge-fixed / `Q₁B=0` fluctuation subspace, NOT all fields). This is exactly
the conclusion shape of the PROVED reduction `faithfulCovCoercivity_of_gaugeFixedCurlCoercivity`, so
it reduces to the su(2) curl-vs-coarse coercivity `GaugeFixedCurlCoercivity` (§2 theorem).

Unlike the unrestricted `FaithfulCovCoercivityTarget` (REFUTED, §1), the constant-field counterexample
is NOT automatically in scope: the constant is excluded from Balaban's FULL domain by the axial
condition (2.121). (Whether the mere gauge-fixed condition alone already excludes it at `levels=[]` is
NOT established — see `U1LeadingCoercivity.faithfulCovCoercivity_of_gaugeFixedCurlCoercivity`'s
docstring; the axial refinement `admissibleSubspaceInter` is the provably-sufficient domain.) -/
def FaithfulCovCoercivityTargetGaugeFixed (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection] : Prop :=
  CompatibleExtent L ell →
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ A0 : Bond L → SuTwo,
      RcovLM U levels (gradCovariantAdjointLM U A0) = 0 →
        γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0)
          ≤ deltaJQuadFormCovFaithful ell levels U A0

/-- **THE CORRECTED TARGET REDUCES TO `GaugeFixedCurlCoercivity`, PROVED.** Given the su(2)
gauge-fixed curl-vs-coarse coercivity `∃ γ₀ > 0, GaugeFixedCurlCoercivity ell levels U γ₀` (the raw
curl energy `‖D_U A‖²` dominates `γ₀‖Q₁A‖²` on every gauge-fixed `A`), the corrected domain-restricted
target holds — a direct wrapping of the existing `faithfulCovCoercivity_of_gaugeFixedCurlCoercivity`.
This is the honest `C*Δ_kC`-coercivity ⟸ (2.128) unification: the correct target follows from the
su(2) curl-vs-coarse coercivity, the analogue of CMP96 (2.128) on the axial gauge (§3). -/
theorem faithfulCovCoercivityTargetGaugeFixed_of_gaugeFixedCurlCoercivity (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (h : ∃ γ₀ : ℝ, 0 < γ₀ ∧ GaugeFixedCurlCoercivity ell levels U γ₀) :
    FaithfulCovCoercivityTargetGaugeFixed ell levels U := by
  intro _hcompat
  obtain ⟨γ₀, hγ, hGF⟩ := h
  exact ⟨γ₀, hγ, fun A0 hA0 =>
    faithfulCovCoercivity_of_gaugeFixedCurlCoercivity ell levels U γ₀ hGF A0 hA0⟩

#print axioms faithfulCovCoercivityTargetGaugeFixed_of_gaugeFixedCurlCoercivity

/-! ## §3 — the named link to CMP96 (2.128) / `GeomGlobal.GeomInequality` -/

/-- **THE su(2) (2.128)-ANALOGUE — `def : Prop`, the named link.** The su(2) form of CMP96 (2.128):
the coarse-average term `ell·Σ_c‖Q₁A0(c)‖²` PLUS the fine curl energy `Σ_p‖curl A0(p)‖²` controls the
fine bond norm `‖A0‖²`, with a size-independent constant. This mirrors the SCALAR
`GeomGlobal.Lemma24Conclusion` (`ell·coarseQEnergy + totalCurlEnergy ≥ (1/108)(1/ell⁴)·bondNormSq`)
and `GeomGlobal.GeomInequality`, both stated on the axial gauge `admissibleSubspaceInter` (the
Href-lane `sorry` `GeomGlobal.geomInequality_of_admissible_ell2`, NOT touched here).

**Why this is the correct object, and why the coarse term is essential.** A curl-kernel mode (e.g. a
constant at `U=1`) has `curl A0 = 0` but `Q₁A0 ≠ 0`; the coarse-average term detects it, the curl term
does not. Dropping it gives the unrestricted `γ₀‖Q₁A0‖² ≤ curl` bound — REFUTED (§1). Balaban keeps
the coarse term additively (2.128) OR removes the mode by `Q₁B=0` + axial gauge (the fluctuation
subspace of `GaugeFixedCurlCoercivity`). `c : ℝ` is the constant slot (Balaban's `1/(12d²)·L^{d-1}`
in (2.128)); value NOT asserted. NOT proved here — this NAMES the su(2) mechanism `GaugeFixedCurlCoercivity`
is the fluctuation-restriction of. -/
def SuTwoGeomAdditiveInequality (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : ℝ) (A0 : Bond L → SuTwo) : Prop :=
  (ell : ℝ) * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0)
      + covPlaqInner (curlCovariantLM U A0) (curlCovariantLM U A0)
    ≥ c * covBondInner A0 A0

end AdalyFormal.Balaban.CoercivityTargetsCorrected
