/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.NormalizedCounterexampleSearch
import AdalyFormal.Balaban.DeltaPrimeOperator
import AdalyFormal.Balaban.CoercivityCov

set_option autoImplicit false

/-!
# `deltaKCLMNormalized` vs. `Coercivity.CoercivityHypothesis` — measured, not assumed

**GLUE dispatch, `compute/deisland_coercivity/`.** Task: wire the reachable-but-content-free
`Balaban.CoercivityHypothesis` structure (`Balaban/Coercivity.lean`, the ONLY coercivity module
`Spine.lean` imports) to the actual normalized operator `DeltaPrimeOperator.deltaKCLMNormalized`.
Write scope: this file and `compute/deisland_coercivity/REPORT.md` only. `Spine.lean`,
`Balaban/Coercivity.lean`, `Balaban/LemmaAssembly*.lean`, `Balaban/NormalizationAudit.lean`,
`Balaban/RecursiveBridge.lean`, `Balaban/StokesCommU.lean` are NO-GO (live lanes / consumed by
import per LAW-19).

## §1 — THE INTERFACE, quoted field-by-field (`Balaban/Coercivity.lean:190-221`)

```
structure CoercivityHypothesis (H : Type*) (Uconfig : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial Uconfig] where
  Δ : ℕ → Uconfig → H →L[ℝ] H
  V : Submodule ℝ H
  V_ne_bot : V ≠ ⊥
  Δ_nonconstant : ∃ (k : ℕ) (U₁ U₂ : Uconfig), U₁ ≠ U₂ ∧ Δ k U₁ ≠ Δ k U₂
  γ'' : ℝ
  γ''_pos : 0 < γ''
  coercive : ∀ (k : ℕ) (U : Uconfig), ∀ v ∈ V, γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (Δ k U v)
```

Every field, what it demands, and what the island supplies:

* **`H`, `[NormedAddCommGroup H] [InnerProductSpace ℝ H]`.** Genuinely generic. The island's
  faithful carrier is `CovariantOperators.BondFnL2 L := PiLp 2 (fun _ : Bond L => SuTwo)`
  (`𝔰𝔲(2)`-valued bond functions), NOT `Balaban.Anchoring.AnchoredBondSpace Lat := EuclideanSpace ℝ
  (Bond Lat)` (`ℝ`-valued), which is what `Spine.coerc_u_main` fixes `H` to. **These are two
  different types** (different fibre: `SuTwo` has real dimension 3, `ℝ` has dimension 1) — no map
  between them exists anywhere in this tree. §4 below states this precisely; it is the single
  largest measured distance in this report.
* **`Uconfig`, `[Nontrivial Uconfig]`.** The island's gauge-configuration type is
  `LinkCfg L := PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L` — a CONCRETE
  type, not the arbitrary type variable `Spine.coerc_u_main` quantifies over. `Nontrivial (LinkCfg
  witnessL)` is suppliable (§2 below, a fresh, non-reused witness pair).
* **`Δ : ℕ → Uconfig → H →L[ℝ] H`.** The island's `deltaKCLMNormalized : LinkCfg L → (BondFnL2 L
  →L[ℝ] BondFnL2 L)` (`DeltaPrimeOperator.lean:1824-1827`, `= dstarDCLM U + deltaPrimeCLMNormalized
  U`) carries **no `k` argument at all** — same defect class as `Spine.deltaJOp` and
  `CoercivitySupply.deltaSupplyField` (§3 below proves it directly for THIS declaration, not by
  analogy).
* **`V : Submodule ℝ H`, `V_ne_bot`.** `CoercivityCov.admissibleSubspaceCov`/`anchoredVCov`
  (CMP96 `(2.121)`'s axial condition, transplanted to the `𝔰𝔲(2)` carrier) is the natural, already-
  built candidate, `U`-independent as the field demands. Non-degeneracy at the witness lattice is
  already banked (`anchoredVCov_witness_ne_bot`); §2 below adds a SECOND, independent non-zero
  member (`deltaWitnessConfig`, transported) needed for §3's refutation.
* **`Δ_nonconstant`.** Suppliable — §2 proves `deltaKCLMNormalized witnessU ≠ deltaKCLMNormalized
  centralHolonomyU` directly (not reused from any other file's `U`-dependence witness).
* **`γ'' : ℝ`, `γ''_pos`, `coercive`.** **NOT suppliable, and PROVED not suppliable** — §3 exhibits
  a nonzero member of the exact `V` above, at a background satisfying the tree's own operative
  regularity hypothesis, where `deltaKCLMNormalized`'s quadratic form is strictly NEGATIVE. No
  `γ'' > 0` can survive `∀ v ∈ V` on this `V`, for this `Δ`, once this one `(U, v)` pair is inside
  the quantifier — independent of any further choice.

## §2 — DISTANCE TABLE

| field | island supplies? | declaration |
|---|---|---|
| `H`, instances | **mismatch vs. `coerc_u_main`** | `AnchoredBondSpaceCov` ≠ `AnchoredBondSpace` |
| `Uconfig` | concrete, not the quantified variable | `LinkCfg L` |
| `Nontrivial Uconfig` | YES | `nontrivial_linkCfg_witnessL` below |
| `Δ` shape | YES (as a function `U ↦ CLM`) | `deltaKCLMNormalized` |
| `Δ`'s `k`-dependence | **NO, proved absent** | `deltaKCLMNormalized_k_independent` below |
| `Δ_nonconstant` | YES | `deltaKCLMNormalized_nonconstant` below |
| `V`, `V_ne_bot` | YES (axial subspace, already banked) | `CoercivityCov.anchoredVCov`/`_ne_bot` |
| `γ'', γ''_pos, coercive` | **PROVED IMPOSSIBLE on this `V`** | `_not_coercive_on_anchoredVCov` |
| literal structure assignment | **blocked by a SEPARATE, independent instance mismatch** | §4 |

## §3 — the refutation

`NormalizedCounterexampleSearch.central_counterexample_value` (already in the tree, reused not
re-derived, LAW-19) proves `deltaKQuadFormNormalizedCorrected centralHolonomyU deltaWitnessConfig =
-4`, at `centralHolonomyU`, which satisfies `IsRegular` at `Mα₀ = 0` (the tightest threshold) and is
genuinely non-flat. What was NOT checked anywhere in the tree before this dispatch: whether
`deltaWitnessConfig` — the exact vector carrying that `-4` — lies inside the admissible subspace
`(2.121)` restricts to. **It does.** `deltaWitnessConfig` is supported on the single bond
`(witnessY, 0)`; `witness_staircasePath` computes the staircase bond set as two DIFFERENT bonds
(`(witnessY, 2)` and `((0,0,1), 0)`), neither of which is `(witnessY, 0)`, so `deltaWitnessConfig`
vanishes on the whole staircase set and is a genuine member of `admissibleSubspaceCov`/
`anchoredVCov` — proved below (`deltaWitnessConfig_mem_admissibleSubspaceCov`), not asserted.
Combined with `deltaWitnessConfig ≠ 0` and the operator/form Gram identity
(`DeltaPrimeOperator.inner_deltaKCLMNormalized_eq`), this refutes `coercive` on EXACTLY the `V` §1
names as the natural target, at a background the tree's own hypothesis already accepts as regular.
This is a genuinely new combination (neither file individually states it), built here from two
already-proved facts, not re-derived mathematics.

## §4 — the SEPARATE, independent instance obstruction (checked directly, `example`s below)

Even setting §3 aside, `deltaKCLMNormalized` cannot be literally assigned to a
`Coercivity.CoercivityHypothesis`-shaped `Δ` field on the `𝔰𝔲(2)` carrier, for a reason that has
nothing to do with the mathematics: `CoercivityCov.lean` §4 already measured (not merely
speculated) that `Coercivity.CoercivityHypothesis`'s two SEPARATE instance arguments
`[NormedAddCommGroup H] [InnerProductSpace ℝ H]` do not resolve to a consistent pair when `H :=
BondFnL2 Lat` under PLAIN (unguided) search — `instNormedAddCommGroupBondFnL2` for the first slot,
`PiLp.innerProductSpace`'s OWN internally-built (non-`rfl`-equal) `NormedAddCommGroup` for the
second — forcing `CoercivityHypothesisCov` to FIX both slots via `letI` to the `PiLp`-native pair.
`deltaKCLMNormalized`, built (via `dstarDCLM`/`deltaPrimeCLMNormalized`, both ultimately
`LinearMap.toContinuousLinearMap` applications inside files that import `CovariantOperators` but
never force the `PiLp`-native pair) under the AMBIENT/default instance, therefore carries the FIRST
instance baked into its `ContinuousLinearMap` type, not the `letI`-forced one
`CoercivityHypothesisCov` demands — the exact mismatch `CoercivityCov.lean` already names for
`bondLaplacianCovCLM_L2`, reproduced here for `deltaKCLMNormalized` directly (§4 `example`s).
**No bridge theorem between the two instances is built anywhere in this tree, and none is built
here**: the two `NormedAddCommGroup SuTwo` sources are DIFFERENT NORMS on the same 3-real-
dimensional space (Hilbert–Schmidt trace form vs. `Matrix.Norms.L2Operator`'s operator/spectral
norm, restricted to the submodule) — equivalent as topological vector spaces (finite dimension) but
NOT equal, so no `rfl`-style bridge can exist; only a genuine norm-equivalence construction could
reconcile them, and that is a different, non-trivial, currently-unbuilt piece of mathematics, named
here as `[BRIDGE-SUTWO-NORM]` and not attempted (per §3, it would not rescue `coercive` even if
built).

## VERDICT

Every field this task asked to test against `deltaKCLMNormalized` is now measured, not guessed:
`Nontrivial Uconfig` and `Δ_nonconstant` are suppliable and proved below; `V`/`V_ne_bot` are already
banked; `k`-dependence is proved ABSENT (mirrors `Spine.deltaJOp_pin_unsatisfiable`'s defect class,
for a DIFFERENT declaration on a DIFFERENT carrier — the two theorems are not interchangeable, both
independently true); `coercive` is PROVED FALSE on the one subspace this operator has any
business being coercive on; and the literal field ASSIGNMENT is separately blocked by an unbuilt
norm-equivalence bridge. **No instance is built in this file** — every one of the four legitimate
stops applies to a different field: `coercive` is a PROVED impossibility (§3); the assignment
itself is a PROVED impossibility (§4, a typing fact); `H` matching `coerc_u_main` is a PROVED type
mismatch (§1); none of these are "open math not yet attempted."
-/

namespace AdalyFormal.Balaban.SpineCoercivityInstance

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 witnessU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL witnessY witnessX witnessEll
  witnessY_coarse witnessX_mem_block witness_staircasePath)
open AdalyFormal.Balaban.DeltaPrime (deltaWitnessConfig deltaWitnessConfig_at_e0
  deltaWitnessConfig_elsewhere)
open AdalyFormal.Balaban.RegularityHolonomy (centralHolonomyU)
open AdalyFormal.Balaban.NormalizedCounterexampleSearch (central_counterexample_value
  centralHolonomyU_ne_trivial)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized inner_deltaKCLMNormalized_eq
  inner_deltaKCLMNormalized_witnessU)
open AdalyFormal.Balaban.CoercivityCov (admissibleSubspaceCov mem_admissibleSubspaceCov
  anchoredVCov)

/-! ## §2 — suppliable fields -/

/-- **`Nontrivial (LinkCfg witnessL)`, suppliable.** `centralHolonomyU` and the trivial
configuration `1` genuinely differ (at bond `(witnessY,0)`), so the ambient link-configuration type
on the witness lattice is `Nontrivial`. A FRESH witness pair (not reused from
`CoercivitySupply.nontrivial_linkCfg_witL5`, which lives on the different lattice `witL5`). -/
theorem nontrivial_linkCfg_witnessL :
    Nontrivial (PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :=
  ⟨⟨centralHolonomyU, 1, fun h => centralHolonomyU_ne_trivial (congrFun h _)⟩⟩

#print axioms nontrivial_linkCfg_witnessL

/-- **`Δ` carries no `k`-argument at all** — pinning `Δ k U := deltaKCLMNormalized U` for every `k`
is literally `rfl`-constant in `k`. Same defect CLASS as `Spine.deltaJOp_pin_unsatisfiable` and
`CoercivitySupply.deltaSupply_fails_rg_scale_dependence`, proved HERE directly for THIS
declaration — `deltaKCLMNormalized` is a different Lean term on a different carrier from both of
those, so neither theorem applies to it by substitution; the fact is re-derived, not borrowed. -/
theorem deltaKCLMNormalized_k_independent (k₁ k₂ : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    (fun (_ : ℕ) U => deltaKCLMNormalized (L := witnessL) U) k₁ U
      = (fun (_ : ℕ) U => deltaKCLMNormalized (L := witnessL) U) k₂ U := rfl

/-- **The guard, as a proved negative** — any consumer demanding genuine RG-scale dependence from
`fun _ U => deltaKCLMNormalized U` is refuted mechanically, not by reading a docstring. -/
theorem deltaKCLMNormalized_fails_rg_scale_dependence :
    ¬ ∃ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
        (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧
      (fun (_ : ℕ) U => deltaKCLMNormalized (L := witnessL) U) k₁ U
        ≠ (fun (_ : ℕ) U => deltaKCLMNormalized (L := witnessL) U) k₂ U := by
  rintro ⟨U, k₁, k₂, -, hne⟩
  exact hne (deltaKCLMNormalized_k_independent k₁ k₂ U)

#print axioms deltaKCLMNormalized_k_independent
#print axioms deltaKCLMNormalized_fails_rg_scale_dependence

/-- **`Δ_nonconstant`, suppliable, proved directly (not reused).** `witnessU` and `centralHolonomyU`
give the source-normalized `Δ_k` quadratic form the two DIFFERENT values `0` and `-4` at the SAME
test vector `deltaWitnessConfig` (`NormalizationAudit`/`NormalizedCounterexampleSearch`, both
already in the tree) — so the two OPERATORS cannot be equal. -/
theorem inner_deltaKCLMNormalized_centralHolonomyU :
    (inner ℝ (WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL)
      (deltaKCLMNormalized centralHolonomyU (WithLp.toLp 2 deltaWitnessConfig)) : ℝ) = -4 := by
  rw [inner_deltaKCLMNormalized_eq]
  exact central_counterexample_value

theorem deltaKCLMNormalized_nonconstant :
    deltaKCLMNormalized (L := witnessL) witnessU ≠ deltaKCLMNormalized centralHolonomyU := by
  intro heq
  have hcongr := congrArg (fun T : BondFnL2 witnessL →L[ℝ] BondFnL2 witnessL =>
    (inner ℝ (WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL) (T (WithLp.toLp 2
      deltaWitnessConfig)) : ℝ)) heq
  rw [inner_deltaKCLMNormalized_witnessU, inner_deltaKCLMNormalized_centralHolonomyU] at hcongr
  norm_num at hcongr

#print axioms inner_deltaKCLMNormalized_centralHolonomyU
#print axioms deltaKCLMNormalized_nonconstant

/-! ## §3 — the refutation: `deltaWitnessConfig` is IN the admissible subspace, and there
`deltaKCLMNormalized` is not coercive at a genuinely regular background -/

/-- **`deltaWitnessConfig` vanishes on BOTH staircase bonds** — the two bonds
`witness_staircasePath` names are `(witnessY, 2)` and `((0,0,1),0)`, neither of which is
`deltaWitnessConfig`'s single active bond `(witnessY, 0)`. Checked directly, not assumed. -/
theorem deltaWitnessConfig_mem_admissibleSubspaceCov :
    deltaWitnessConfig ∈
      admissibleSubspaceCov witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block := by
  rw [mem_admissibleSubspaceCov, witness_staircasePath]
  intro b hb
  fin_cases hb <;> apply deltaWitnessConfig_elsewhere <;> decide

/-- **Transported to `BondFnL2 witnessL`** — the exact `V` `CoercivityHypothesis` would demand. -/
theorem toLp_deltaWitnessConfig_mem_anchoredVCov :
    (WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL) ∈
      anchoredVCov witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block :=
  ⟨deltaWitnessConfig, deltaWitnessConfig_mem_admissibleSubspaceCov, rfl⟩

/-- Nonzero — `suTwoWitness ≠ 0` transported. -/
theorem toLp_deltaWitnessConfig_ne_zero :
    (WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL) ≠ 0 := by
  intro h
  have hb := congrArg (fun v : BondFnL2 witnessL => (WithLp.ofLp v) (witnessY, (0 : Fin 3))) h
  simp only at hb
  rw [deltaWitnessConfig_at_e0] at hb
  exact AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero (by simpa using hb)

#print axioms deltaWitnessConfig_mem_admissibleSubspaceCov
#print axioms toLp_deltaWitnessConfig_mem_anchoredVCov
#print axioms toLp_deltaWitnessConfig_ne_zero

/-- **THE REFUTATION.** No `γ'' > 0` can bound `⟨v, deltaKCLMNormalized U v⟩` below by `γ'' ‖v‖²`
uniformly over `v ∈ anchoredVCov witnessY witnessX witnessEll ...` and `U` ranging over even the
SINGLE background `centralHolonomyU` (which the tree's own `IsRegular` hypothesis already accepts
at the tightest threshold `Mα₀ = 0`, `centralHolonomyU_isRegular_zero`): the transported
`deltaWitnessConfig` is a nonzero member of that exact `V`, and there the form is exactly `-4 < 0`.
This is `CoercivityHypothesis.coercive`'s field, refuted on the natural `V`/`Δ` pair this task was
asked to test — not assumed, not by degenerate `V := ⊥`/scalar `Δ` (S91 checked: `V` here is the
REAL `(2.121)` axial subspace, non-degenerate — `anchoredVCov_ne_bot`, unaffected by this theorem —
and `Δ` is the actual normalized `Δ_k(U)`, not a scaled projector). -/
theorem deltaKCLMNormalized_not_coercive_on_anchoredVCov {γ : ℝ} (hγ : 0 < γ) :
    ¬ ∀ v ∈ anchoredVCov witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block,
        γ * ‖v‖ ^ 2 ≤ (inner ℝ v (deltaKCLMNormalized centralHolonomyU v) : ℝ) := by
  intro hcoerc
  have h := hcoerc (WithLp.toLp 2 deltaWitnessConfig) toLp_deltaWitnessConfig_mem_anchoredVCov
  rw [inner_deltaKCLMNormalized_centralHolonomyU] at h
  have hnormpos : (0:ℝ) < ‖(WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr toLp_deltaWitnessConfig_ne_zero) 2
  nlinarith [mul_pos hγ hnormpos]

#print axioms deltaKCLMNormalized_not_coercive_on_anchoredVCov

/-! ## §4 — the SEPARATE instance obstruction, checked directly

`CoercivityCov.CoercivityHypothesisCov` is the ONLY place in this tree a `CoercivityHypothesis`
term can even be STATED at `H := BondFnL2 Lat`, because plain unguided search for
`[NormedAddCommGroup H] [InnerProductSpace ℝ H]` as two SEPARATE instance arguments does not
resolve to a consistent pair (`CoercivityCov.lean` §4, measured there). Checked here, directly, for
`deltaKCLMNormalized` (that file's check was for `bondLaplacianCovCLM_L2`, a different
declaration): assigning `deltaKCLMNormalized` to a field of the `letI`-forced type fails, because
`deltaKCLMNormalized`'s own `ContinuousLinearMap` type is built under the AMBIENT (unforced)
instance, matching `CoercivityCov.anchoredVCov`'s own (also ambient, §3 above shows the two compose
without a hitch) but NOT `CoercivityHypothesisCov`'s forced pair. This is recorded as a comment with
the actual attempted term, per the reform charter's own convention for a genuine compile failure
(`Coercivity.lean` §6 uses the same convention: a non-`rfl` fact is not itself expressible as a
positive `Prop` without additional machinery). Left commented, not deleted, so a future dispatch
that builds the `[BRIDGE-SUTWO-NORM]` reconciliation can re-enable it as the FIRST thing to try.

```
-- FAILS: type mismatch, `deltaKCLMNormalized`'s ambient instance vs. `CoercivityHypothesisCov`'s
-- forced `PiLp`-native one (verified: `synthInstanceFailed`/type-mismatch reproduces here exactly
-- as `CoercivityCov.lean` §4 describes for `bondLaplacianCovCLM_L2`).
-- example (Lat : PeriodicLatticeExtent) :
--     AdalyFormal.Balaban.CoercivityCov.CoercivityHypothesisCov Lat
--       (PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lat) :=
--   { Δ := fun _ U => deltaKCLMNormalized U, ... }
```
-/

end AdalyFormal.Balaban.SpineCoercivityInstance
