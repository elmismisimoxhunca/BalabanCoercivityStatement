/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Coercivity
import AdalyFormal.Balaban.LemmaAssemblyNormalized
import AdalyFormal.Balaban.SpineCoercivityInstance
import AdalyFormal.Balaban.RegularUCurvedWitness
import AdalyFormal.Balaban.IslandBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

/-!
# `CoercivityRegular.lean` — `CoercivityHypothesis` with the BACKGROUND DOMAIN repaired

Additive module. `Balaban/Coercivity.lean` is NOT edited; nothing in `Spine.lean`'s closure moves.

## §0 — the defect this repairs (established elsewhere, consumed here, not re-derived)

`Balaban.CoercivityHypothesis.coercive` reads

```
coercive : ∀ (k : ℕ) (U : Uconfig), ∀ v ∈ V, γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (Δ k U v)
```

— an unrestricted `∀ U`, with no regularity field anywhere in the structure. That demand is FALSE
for the real operator: `SpineCoercivityInstance.deltaKCLMNormalized_not_coercive_on_anchoredVCov`
proves no `γ'' > 0` bounds `deltaKCLMNormalized` below on the real `(2.121)` axial subspace
`CoercivityCov.anchoredVCov`, because the normalized form is `−4` at
`DeltaPrime.deltaWitnessConfig` under `RegularityHolonomy.centralHolonomyU`.

The proved coercivity `LemmaAssemblyNormalized.deltaKNormalized_gaugeRegular_coercive` is not in
conflict: it is stated for `AlphaAnalyticity.GaugeRegular normAlpha U` with
`normAlpha = 5·10⁻⁷`, and `centralHolonomyU` is nowhere near that class (§3 proves it,
gauge-invariantly). Different hypothesis classes. The structure has no field to carry Bałaban's
CMP99b (3.35) restriction, so it demands something false.

## §0b — what is in this file

* **§1** `CoercivityHypothesisRegular`: the same structure with a `Reg : Uconfig → Prop` field, the
  subspace made a `U`-indexed FAMILY (forced — Bałaban's subspace is `ker Q_k(U)`, §7), every
  original anti-vacuity guard kept verbatim, and one NEW guard (`Reg_nonconstant`) that exists
  precisely to stop the repair from being cheated by shrinking `Reg` to a point.
* **§2** the degenerate-binder battery, run as theorems, in both directions.
* **§3** the MUST-FIRE control: `¬ GaugeRegular normAlpha centralHolonomyU` (gauge-invariantly,
  via the plaquette curvature), together with the theorem that ANY regularity predicate admitting
  `centralHolonomyU` still cannot support `coercive` for the real operator. That pair is what
  proves the repair did work rather than merely moved the words around.
* **§4** the regular class at `normAlpha = 5·10⁻⁷` CONTAINS A GENUINELY CURVED BACKGROUND —
  constructed, not assumed, and not the flat one.
* **§5–§6** the single-active-bond machinery needed to prove `Δ` genuinely varies over the
  REGULAR class (not merely over all `U`), on the lattice the coercivity theorem admits.
* **§7** the instance: a `CoercivityHypothesisRegular` whose `Δ` IS
  `DeltaPrimeOperator.deltaKCLMNormalized` and whose `coercive` field is discharged by
  `deltaKNormalized_gaugeRegular_coercive`.

## §0c — MUTATION RECORD (OPS-3), 6 run, 6 FIRED, 0 survivors; baseline `M0` (verbatim copy) compiles

Each mutant is the whole file with ONE line changed, compiled standalone by `lake env lean`; each
was diffed against the source before running (exactly 2 changed lines per mutant), so a no-op
`sed` cannot masquerade as a survivor.

| id | mutation | errors | fires at |
|----|----------|--------|----------|
| `M0` | none (verbatim copy) | **0** | — (the control that the harness can pass) |
| `M1` | instance `Reg := fun _ => True` (the repair DELETED) | 4 | `Reg_nonconstant`, **`coercive`**, `instanceReg_excludes_central_on_witL5` |
| `M2` | instance `γ'' := 1` (numerically false) | 4 | `γ''_pos` is fine, **`coercive`** fails, `realInstance_gamma` fails |
| `M3` | instance `V := fun _ => ⊤` (domain widened past `axial ∩ ker Q₂(U)`) | 2 | `V_ne_bot` path, **`coercive`** |
| `M4` | `curvedT := 1/100` (above the `normAlpha` threshold) | 1 | `frobSupBond_curvedRegularU_le` (`linarith` refutation) |
| `M5` | `curvedRegularU := trivialU witL5` (curvature removed) | 8 | the whole §4 apparatus incl. `curvedRegularU_curved`, `regular_class_contains_curved`, `regular_class_not_all_flat` |
| `M6` | `Reg_nonconstant`'s two backgrounds made EQUAL | 1 | `Reg_nonconstant` |

**Disclosed limit:** `M6` fails by `isDefEq` heartbeat exhaustion rather than a clean type
mismatch — that proves the two backgrounds are not definitionally interchangeable in that position,
which is WEAKER than a proof that the mutated statement is false. `M1`–`M5` fail by clean type
mismatch or `linarith` refutation on statements that are genuinely false.

**The vacuity control for §3** is not a mutant but a theorem already in the tree:
`NormalizedCounterexampleSearch.centralHolonomyU_isRegular_zero` proves the PRE-REPAIR predicate
`IsRegular` ACCEPTS `centralHolonomyU` at the tightest threshold. So §3's exclusion is not a check
that fires on everything: the predicate it replaced fires on nothing here.

## §0d — RESIDUAL CREATED BY THIS WORK, AND WHY IT IS NOT CLOSED HERE

The `ContinuousLinearMap` bundling (§8). Nine routes attempted and tabulated with their exact
break points; the root cause is localised BY MEASUREMENT to `SuTwo`'s own instance declarations
(`instTopologicalSpaceSubtype` vs `SuTwoInner.instNormedAddCommGroupSuTwo`), with a must-not-fire
control showing the same `PiLp` diamond is `rfl` at a plain `ℝ` fibre
(`pilp_topology_diamond_is_rfl_at_real_fibre`). Closing it requires editing
`Balaban/CovariantOperators.lean` / `Balaban/SuTwoInner.lean`, which is a WRITE-SCOPE COLLISION for
this dispatch, not a mathematical obstacle. The exact repair a future dispatch should try: make
`SuTwo`'s `UniformSpace`/`TopologicalSpace` instances derive from
`SuTwoInner.instNormedAddCommGroupSuTwo` (or build that `NormedAddCommGroup` from the subtype
uniformity via `replaceUniformity`) so the two paths coincide definitionally.

`#print axioms` on every declaration.
-/

namespace AdalyFormal.Balaban.CoercivityRegular

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one RMap_coe_apply
  curlValueCovariant suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice staircasePath witnessL
  witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond frobSupBond_nonneg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeRegular gaugeRegular_of_frobSupBond_le
  gaugeRegular_gauge_invariant)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem)
open AdalyFormal.Balaban.LemmaAssembly (frobSq_holonomy_of_gaugeRegular)
open AdalyFormal.Balaban.LemmaAssemblyNormalized (normAlpha normGamma normAlpha_pos normGamma_pos
  deltaKNormalized_gaugeRegular_coercive)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized inner_deltaKCLMNormalized_eq)
open AdalyFormal.Balaban.CoercivityCov (anchoredVCov)
open AdalyFormal.Balaban.RegularityHolonomy (centralHolonomyU)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5 witL5_four_le witL5_two_dvd)
open AdalyFormal.Balaban.RegularUDomainWitnessGeneralU (siteZero genWitness genWitness_axial
  genWitness_mem_kerQ genWitness_ne_zero genWitness_at_freeBond)
open AdalyFormal.Balaban.RegularUCurvedWitness (bondU bondU_at bondU_off frobSupBond_bondU
  curvedBond curvedPlaq curvedFamilyU curvedFamilyU_curvature_ne_one frobSupBond_curvedFamilyU_le
  witL5_pos holonomy_singleBond_base_plaquette holonomy_singleBond_trichotomy shift_ne_self dir01)
open AdalyFormal.Balaban.IslandBridge (norm_sq_bondFnL2)
open scoped Matrix

/-! ## §1 — THE REPAIRED STRUCTURE

Field-by-field against `Balaban.CoercivityHypothesis` (`Balaban/Coercivity.lean:190-221`):

| original field | here | status |
|---|---|---|
| `[Nontrivial Uconfig]` | `[Nontrivial Uconfig]` | **KEPT VERBATIM** (instance argument) |
| `Δ : ℕ → Uconfig → H →L[ℝ] H` | identical | **KEPT VERBATIM** |
| `V : Submodule ℝ H` | `V : Uconfig → Submodule ℝ H` | **INDEXED** (§7: forced by `ker Q_k(U)`) |
| `V_ne_bot : V ≠ ⊥` | `V_ne_bot : ∀ U, Reg U → V U ≠ ⊥` | **KEPT**, relativised to the domain |
| `Δ_nonconstant` | identical, unrelativised | **KEPT VERBATIM** |
| `γ'' : ℝ` | identical | **KEPT VERBATIM** |
| `γ''_pos : 0 < γ''` | identical | **KEPT VERBATIM** |
| `coercive` | `∀ k U, Reg U → ∀ v ∈ V U, …` | **DOMAIN RESTRICTED** — the repair |
| — | `Reg : Uconfig → Prop` | **NEW** |
| — | `Reg_nonconstant` | **NEW GUARD ON THE REPAIR ITSELF** |

Two design points a prosecutor will go at first, stated before they are asked:

**(a) Why `V` became a family.** The proved coercivity `deltaKNormalized_gaugeRegular_coercive`
holds on `axial ∩ ker Q₂(U)`, and `ker Q₂(U)` genuinely depends on `U`
(`lineCoarseRestrictCov U 2`). A `U`-INDEPENDENT `V` would force the structure to demand a bound
on a subspace on which nothing in this tree proves one; keeping `V` constant while restricting only
`Reg` would have made §7's instance impossible for a reason that has nothing to do with regularity.
`V_ne_bot` is relativised to `Reg` for the same reason it is a field at all: outside the regular
class the structure asserts nothing, so a non-degeneracy demand there would be an extra,
unmotivated hypothesis rather than a guard.

**(b) Why `Reg_nonconstant` is needed.** Restricting a `∀` can empty it. `Reg := fun _ => False`
makes `coercive` vacuous; `Reg := fun U => U = U₀` makes it a one-point claim, at which
"uniformity in `U`" — the entire content of `[LEM-COERC-U]` — evaporates. `Reg_nonconstant`
demands two DISTINCT regular backgrounds at which `Δ` genuinely DIFFERS, so the restricted
quantifier still ranges over a set on which the operator moves. It is strictly stronger than
`Δ_nonconstant` (§2, `Δ_nonconstant_of_Reg_nonconstant`); `Δ_nonconstant` is kept anyway, verbatim,
so that "every guard the original has" is literally true field-for-field and not merely
"implied". -/

/-- **`CoercivityHypothesisRegular`** — `Balaban.CoercivityHypothesis` with the background domain
of `coercive` cut down to a carried regularity predicate, and with a guard on that predicate. -/
structure CoercivityHypothesisRegular (H : Type*) (Uconfig : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial Uconfig] where
  /-- The operator family. **Unchanged from `CoercivityHypothesis`** (a `ContinuousLinearMap`, so
  the R3 `Migration.L8c` composition property is inherited unchanged). -/
  Δ : ℕ → Uconfig → H →L[ℝ] H
  /-- **NEW — the regularity predicate.** The field `CoercivityHypothesis` lacks. The intended
  instantiation is `AlphaAnalyticity.GaugeRegular α₀`, which is CMP99b (3.35)'s first clause with
  its `∃ u` restored, hence gauge-INVARIANT (`gaugeRegular_gauge_invariant`). It is deliberately
  NOT `TheLemma.IsRegular`: `LemmaAssembly.isRegular_dichotomy` proves that predicate unusable at
  every threshold. -/
  Reg : Uconfig → Prop
  /-- The distinguished subspace, now a `U`-INDEXED family (§1(a)): Bałaban's subspace is
  `axial ∩ ker Q_k(U)` and the kernel moves with the background. -/
  V : Uconfig → Submodule ℝ H
  /-- **KEPT** (R3's own guard, relativised to the domain the structure speaks about). -/
  V_ne_bot : ∀ U : Uconfig, Reg U → V U ≠ ⊥
  /-- **KEPT VERBATIM** from `CoercivityHypothesis`. -/
  Δ_nonconstant : ∃ (k : ℕ) (U₁ U₂ : Uconfig), U₁ ≠ U₂ ∧ Δ k U₁ ≠ Δ k U₂
  /-- **NEW — the guard on the repair.** Two DISTINCT backgrounds inside `Reg` at which `Δ`
  genuinely differs. Blocks the cheat where the domain restriction is made true by making the
  domain trivial (§2).

  **⚠ SCOPE OF THIS GUARD — MEASURED BY A BLIND SECOND-FAMILY GATE, 2026-07-28. READ BEFORE CITING IT.**
  It proves **LABEL variation and OPERATOR variation. It does NOT prove gauge-orbit variation, and it
  does NOT prove curvature.** Compiled counterexample: at `Reg := GaugeRegular 0` the pair
  `trivialU` / `centerU` satisfies every conjunct — both regular at threshold `0`, distinct as
  configurations, inducing distinct positive operators — **yet they are GAUGE-EQUIVALENT and both
  FLAT**, and the gate compiled the transform between them.

  So this field alone is not evidence that an instance describes anything physically non-flat. It is
  exactly its conditional name and no more — the same lesson as the `Fin 0` carrier defeating three
  purpose-built anti-degeneracy theorems elsewhere in this tree on the same day, because their own
  premises were uninhabited there.

  **This does NOT weaken the concrete instance below.** `realCoercivityHypothesisRegularLM` uses
  `Reg := GaugeRegular normAlpha` with a pair containing `curvedRegularU`, whose nontrivial holonomy
  is proved to survive EVERY gauge transform (`regular_class_contains_curved`,
  `curvedRegularU_not_gaugeTransform_of_flat`). The curvature is carried by a SEPARATE theorem about
  the concrete class, not by this field.

  **To close the gap at the structure level**, add an orbit-level field — nontrivial holonomy at some
  plaquette, or non-membership in the flat orbit — rather than only `U₁ ≠ U₂ ∧ Δ U₁ ≠ Δ U₂`.
  Deliberately NOT done here: it would change the structure while consumers are being built against
  it, and the concrete instance already carries the stronger fact. Recorded so nobody reads this field
  as more than it is. -/
  Reg_nonconstant : ∃ (k : ℕ) (U₁ U₂ : Uconfig),
    Reg U₁ ∧ Reg U₂ ∧ U₁ ≠ U₂ ∧ Δ k U₁ ≠ Δ k U₂
  /-- **KEPT VERBATIM.** -/
  γ'' : ℝ
  /-- **KEPT VERBATIM.** -/
  γ''_pos : 0 < γ''
  /-- **THE REPAIR.** `CoercivityHypothesis.coercive` with `Reg U` inserted. -/
  coercive : ∀ (k : ℕ) (U : Uconfig), Reg U → ∀ v ∈ V U,
    γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (Δ k U v)

/-! ## §2 — THE DEGENERATE-BINDER BATTERY, AND THE RELATION TO THE ORIGINAL -/

section Abstract

variable {H Uconfig : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial Uconfig]

/-- `Reg_nonconstant` is strictly stronger than `Δ_nonconstant`: the redundancy of keeping both is
deliberate, and this is the proof that nothing was lost by keeping the weaker one too. -/
theorem Δ_nonconstant_of_Reg_nonconstant (h : CoercivityHypothesisRegular H Uconfig) :
    ∃ (k : ℕ) (U₁ U₂ : Uconfig), U₁ ≠ U₂ ∧ h.Δ k U₁ ≠ h.Δ k U₂ := by
  obtain ⟨k, U₁, U₂, _, _, hne, hΔ⟩ := h.Reg_nonconstant
  exact ⟨k, U₁, U₂, hne, hΔ⟩

/-- **DEGENERATE BINDER 1 — `Reg` cannot be empty.** -/
theorem reg_nonempty (h : CoercivityHypothesisRegular H Uconfig) : ∃ U : Uconfig, h.Reg U := by
  obtain ⟨_, U₁, _, h1, _, _, _⟩ := h.Reg_nonconstant
  exact ⟨U₁, h1⟩

/-- **DEGENERATE BINDER 2 — `Reg` cannot be a single point.** This is the specific cheat the
domain restriction invites: make `coercive` true by making the domain a point. -/
theorem reg_not_singleton (h : CoercivityHypothesisRegular H Uconfig) (U₀ : Uconfig) :
    ¬ ∀ U : Uconfig, h.Reg U → U = U₀ := by
  intro hsing
  obtain ⟨_, U₁, U₂, h1, h2, hne, _⟩ := h.Reg_nonconstant
  exact hne ((hsing U₁ h1).trans (hsing U₂ h2).symm)

/-- **DEGENERATE BINDER 3 — `Δ` cannot be constant on the REGULAR class.** Even a `Δ` that varies
somewhere but is constant where the claim is made is refuted. -/
theorem delta_not_constant_on_reg (h : CoercivityHypothesisRegular H Uconfig) :
    ¬ ∀ (k : ℕ) (U₁ U₂ : Uconfig), h.Reg U₁ → h.Reg U₂ → h.Δ k U₁ = h.Δ k U₂ := by
  intro hconst
  obtain ⟨k, U₁, U₂, h1, h2, _, hΔ⟩ := h.Reg_nonconstant
  exact hΔ (hconst k U₁ U₂ h1 h2)

/-- **DEGENERATE BINDER 4 — `Δ` cannot be the zero operator.** The exact exploit
(`Coercivity.lean` §2's `botZeroCoercivityAnyU`, `Δ := 0`, `V := ⊥`) that convicted the R2 shape. -/
theorem delta_ne_zero (h : CoercivityHypothesisRegular H Uconfig) :
    ∃ (k : ℕ) (U : Uconfig), h.Δ k U ≠ 0 := by
  obtain ⟨k, U₁, U₂, _, hΔ⟩ := h.Δ_nonconstant
  by_cases h1 : h.Δ k U₁ = 0
  · exact ⟨k, U₂, fun h2 => hΔ (h1.trans h2.symm)⟩
  · exact ⟨k, U₁, h1⟩

/-- **DEGENERATE BINDER 5 — the subspace is nonzero where the claim is made**, with a NAMED nonzero
element extracted, not merely `V U ≠ ⊥`. -/
theorem exists_ne_zero_mem_V (h : CoercivityHypothesisRegular H Uconfig)
    {U : Uconfig} (hU : h.Reg U) : ∃ v ∈ h.V U, v ≠ 0 := by
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h.V_ne_bot U hU)
  exact ⟨v, hv, hne⟩

/-- **DEGENERATE BINDER 6 — `γ'' = 0` is excluded**, and the bound it gives at the named nonzero
element of `V U` is a STRICTLY positive number, not `0 ≤ 0`. -/
theorem coercive_strict_at_some_point (h : CoercivityHypothesisRegular H Uconfig)
    {U : Uconfig} (hU : h.Reg U) (k : ℕ) :
    ∃ v ∈ h.V U, 0 < h.γ'' * ‖v‖ ^ 2 ∧
      h.γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (h.Δ k U v) := by
  obtain ⟨v, hv, hne⟩ := exists_ne_zero_mem_V h hU
  refine ⟨v, hv, ?_, h.coercive k U hU v hv⟩
  have hv2 : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  exact mul_pos h.γ''_pos hv2

/-- **DEGENERATE BINDER 7 — `Uconfig := PUnit` does not even typecheck.** Kept verbatim from the
original shape's own guard: `[Nontrivial Uconfig]` is an instance argument of the structure. -/
theorem punit_not_nontrivial : ¬ Nontrivial PUnit := by
  intro h
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  exact hab (Subsingleton.elim a b)

/-- **THE REPAIR IS A RELAXATION, PROVED.** Every `CoercivityHypothesis` yields a
`CoercivityHypothesisRegular` with `Reg = fun _ => True` and the constant subspace family. So the
new demand is WEAKER: nothing that satisfied the old shape is excluded. Combined with §3 (the real
operator satisfies the new one and PROVABLY not the old one) this makes the weakening strict and
necessary, rather than a cosmetic re-shuffle. -/
def ofUnrestrictedDomain (h : AdalyFormal.Balaban.CoercivityHypothesis H Uconfig) :
    CoercivityHypothesisRegular H Uconfig where
  Δ := h.Δ
  Reg := fun _ => True
  V := fun _ => h.V
  V_ne_bot := fun _ _ => h.V_ne_bot
  Δ_nonconstant := h.Δ_nonconstant
  Reg_nonconstant := by
    obtain ⟨k, U₁, U₂, hne, hΔ⟩ := h.Δ_nonconstant
    exact ⟨k, U₁, U₂, trivial, trivial, hne, hΔ⟩
  γ'' := h.γ''
  γ''_pos := h.γ''_pos
  coercive := fun k U _ v hv => h.coercive k U v hv

end Abstract

/-! ## §3 — THE MUST-FIRE CONTROL: the counterexample background is EXCLUDED, and would not be
without the field

Two halves, both needed. Half (i) says the regularity field genuinely throws `centralHolonomyU`
out, and does so GAUGE-INVARIANTLY (via the plaquette curvature, so no choice of gauge rescues
it). Half (ii) says that ANY predicate that lets `centralHolonomyU` back in is still refuted for
the real operator — so the exclusion is not decoration: it is the only thing standing between the
structure and a false demand.

Note the `α₀ = 0` degeneracy explicitly, because that is exactly how the OLD predicate was
cheated: `NormalizedCounterexampleSearch.centralHolonomyU_isRegular_zero` proves `IsRegular`
ACCEPTS `centralHolonomyU` at the tightest threshold `Mα₀ = 0` (`Ad(−1) = id`). `GaugeRegular 0`
REJECTS it (`gaugeRegular_zero_excludes_central` below). That contrast is the reason the field is
`GaugeRegular` and not `IsRegular`. -/

/-- `‖(−1) − 1‖²_F = ‖diag(−2,−2)‖²_F = 8`. -/
theorem frobSq_negOne_sub_one :
    frobSq ((AdalyFormal.Balaban.DeltaKFull.negOneElem : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 8 := by
  have hcoe : ((AdalyFormal.Balaban.DeltaKFull.negOneElem :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl
  rw [hcoe]
  unfold frobSq
  norm_num [Matrix.one_apply, Complex.normSq_apply]

/-- **MUST-FIRE (i).** `GaugeRegular α₀` REJECTS `centralHolonomyU` at every `α₀ < 1/2`. The
argument is gauge-invariant by construction: it runs through the plaquette curvature bound
`LemmaAssembly.frobSq_holonomy_of_gaugeRegular`, which consumes only `∃ γ, …`, so no choice of
gauge can rescue the configuration. -/
theorem gaugeRegular_excludes_central {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hsmall : α₀ < 1 / 2) :
    ¬ GaugeRegular α₀ centralHolonomyU := by
  intro hreg
  have h := frobSq_holonomy_of_gaugeRegular hα₀ centralHolonomyU hreg
    AdalyFormal.Balaban.CovariantOperators.witnessPlaquette
  rw [AdalyFormal.Balaban.RegularityHolonomy.holonomy_centralHolonomyU_witnessPlaquette,
    frobSq_negOne_sub_one] at h
  nlinarith

/-- **The `α₀ = 0` degenerate binder, run.** Contrast with
`NormalizedCounterexampleSearch.centralHolonomyU_isRegular_zero`, which proves the OLD predicate
`IsRegular` ACCEPTS this background at `Mα₀ = 0`. -/
theorem gaugeRegular_zero_excludes_central : ¬ GaugeRegular (0 : ℝ) centralHolonomyU :=
  gaugeRegular_excludes_central le_rfl (by norm_num)

/-- **At the operative threshold.** `normAlpha = 5·10⁻⁷`. -/
theorem gaugeRegular_normAlpha_excludes_central : ¬ GaugeRegular normAlpha centralHolonomyU :=
  gaugeRegular_excludes_central (le_of_lt normAlpha_pos)
    (by unfold normAlpha; norm_num)

/-- **MUST-FIRE (ii) — the control that proves the field is LOAD-BEARING, not decorative.** For
EVERY predicate `Reg` that admits `centralHolonomyU`, the repaired `coercive` field is still
UNSATISFIABLE at `Δ := deltaKCLMNormalized`, `V := anchoredVCov` — for every `γ > 0`. So a repair
whose regularity field failed to exclude that one background would have repaired nothing. Taken
with `gaugeRegular_normAlpha_excludes_central`, this is the exact mutation test: put
`centralHolonomyU` back into the domain and the structure becomes uninhabitable at the real
operator. -/
theorem no_regular_class_admitting_central
    (Reg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL → Prop)
    (hmem : Reg centralHolonomyU) {γ : ℝ} (hγ : 0 < γ) :
    ¬ ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL), Reg U →
        ∀ v ∈ anchoredVCov witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block,
          γ * ‖v‖ ^ 2 ≤ (inner ℝ v (deltaKCLMNormalized U v) : ℝ) := by
  intro hall
  exact AdalyFormal.Balaban.SpineCoercivityInstance.deltaKCLMNormalized_not_coercive_on_anchoredVCov
    hγ (hall centralHolonomyU hmem)

/-- **The same statement in the form that names the repair**: the UNRESTRICTED domain (`Reg` = the
always-true predicate, i.e. exactly `CoercivityHypothesis.coercive`'s own quantifier) is refuted. -/
theorem unrestricted_domain_refuted_for_real_operator {γ : ℝ} (hγ : 0 < γ) :
    ¬ ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL),
        ∀ v ∈ anchoredVCov witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block,
          γ * ‖v‖ ^ 2 ≤ (inner ℝ v (deltaKCLMNormalized U v) : ℝ) :=
  fun hall => no_regular_class_admitting_central (fun _ => True) trivial hγ
    (fun U _ => hall U)

#print axioms frobSq_negOne_sub_one
#print axioms gaugeRegular_excludes_central
#print axioms gaugeRegular_zero_excludes_central
#print axioms gaugeRegular_normAlpha_excludes_central
#print axioms no_regular_class_admitting_central
#print axioms unrestricted_domain_refuted_for_real_operator

/-! ## §4 — THE REGULAR CLASS AT `5·10⁻⁷` CONTAINS A GENUINELY CURVED BACKGROUND

The question the dispatch flags as open: restricting the domain can EMPTY it, and a coercivity
claim restricted to a class containing only flat configurations is vacuous in the way that matters.
The tree's previously exhibited curved regular witness (`RegularUCurvedWitness.curvedU`) has
`frobSupBond ≈ 7.07·10⁻⁴` and does not reach `normAlpha = 5·10⁻⁷`.

**ANSWER: CONSTRUCTED, not impossible.** The one-parameter family
`RegularUCurvedWitness.curvedFamilyU t` (the rational rotation `rotElem t` on the single bond
`curvedBond`, `1` elsewhere) has `frobSupBond ≤ 2√2·|t|`, so it enters `GaugeRegular normAlpha` for
all small `t`, while its holonomy at `curvedPlaq` is `rotElem t ≠ 1` for every `t ≠ 0` — curvature
that survives EVERY gauge transformation. Taking `t = 10⁻⁷` gives `2√2·10⁻⁷ ≈ 2.83·10⁻⁷ ≤
5·10⁻⁷ = normAlpha`, with room to spare (the exact requirement is `2√2 ≤ 5`, i.e. `8 ≤ 25`).

This is a REUSE, not a new construction (LAW-19): the family, its curvature theorem and its
`frobSupBond` bound are already in the tree; what was missing — and is supplied here — is the
arithmetic that places a member of it under the NORMALIZED threshold, plus the gauge-invariant
statement that the resulting regular class is not a set of flat configurations. -/

/-- The parameter. `10⁻⁷`, a rational. -/
noncomputable def curvedT : ℝ := 1 / 10000000

theorem curvedT_pos : 0 < curvedT := by unfold curvedT; norm_num

theorem curvedT_ne_zero : curvedT ≠ 0 := ne_of_gt curvedT_pos

/-- **The curved background that IS regular at the normalized threshold.** -/
noncomputable def curvedRegularU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5 :=
  curvedFamilyU curvedT

/-- **The exact arithmetic the §4 threshold turns on, as its own named declaration** (nested-
validator finding: it was previously validated only inside another theorem's tactic block).
`2√2 ≤ 5`, i.e. `8 ≤ 25`. -/
theorem two_sqrt_two_le_five : 2 * Real.sqrt 2 ≤ 5 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- `α₁(curvedRegularU) ≤ 2√2·10⁻⁷ ≤ 5·10⁻⁷ = normAlpha`. Exact rational arithmetic: the
requirement is `2√2 ≤ 5`, i.e. `8 ≤ 25` (`two_sqrt_two_le_five`). -/
theorem frobSupBond_curvedRegularU_le : frobSupBond curvedRegularU ≤ normAlpha := by
  have h := frobSupBond_curvedFamilyU_le curvedT
  have habs : |curvedT| = curvedT := abs_of_pos curvedT_pos
  rw [habs] at h
  refine le_trans h ?_
  have h52 := two_sqrt_two_le_five
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold curvedT normAlpha
  nlinarith

/-- **The regularity, at the normalized threshold.** -/
theorem curvedRegularU_gaugeRegular : GaugeRegular normAlpha curvedRegularU :=
  gaugeRegular_of_frobSupBond_le frobSupBond_curvedRegularU_le

/-- **The curvature.** `holonomyElem curvedRegularU curvedPlaq = rotElem 10⁻⁷ ≠ 1`. -/
theorem curvedRegularU_curved :
    holonomyElem curvedRegularU curvedPlaq ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  curvedFamilyU_curvature_ne_one curvedT_ne_zero

/-- **The GAUGE-INVARIANT separation** — `curvedRegularU` is not the gauge transform, by ANY `γ`,
of ANY configuration flat at `curvedPlaq`. So its curvature is not an artefact of the gauge in
which the `frobSupBond` bound was measured; the same configuration is simultaneously
`normAlpha`-regular in the gauge-invariant sense and provably outside every flat gauge orbit. -/
theorem curvedRegularU_not_gaugeTransform_of_flat
    (γ : PeriodicLatticeSite witL5 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5)
    (hV : holonomyElem V curvedPlaq = 1) :
    curvedRegularU ≠ periodicGaugeTransform γ V := by
  intro h
  apply curvedRegularU_curved
  rw [h, AdalyFormal.Balaban.NonFlatBackground.holonomyElem_periodicGaugeTransform_eq_one_iff]
  exact hV

/-- **THE HEADLINE OF §4, as an existential over the regular class itself.** The
`GaugeRegular normAlpha` class at the lattice the coercivity theorem admits (`witL5`, `4 ≤ 5`,
`2 ∣ 6`) contains a configuration with nonzero field strength. The restricted domain is therefore
NOT the flat point (nor a set of pure gauges), and `deltaKNormalized_gaugeRegular_coercive` says
something at a curved background. -/
theorem regular_class_contains_curved :
    ∃ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5,
      GaugeRegular normAlpha U ∧
        ∃ p : PeriodicLatticePlaquette witL5,
          holonomyElem U p ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨curvedRegularU, curvedRegularU_gaugeRegular, curvedPlaq, curvedRegularU_curved⟩

/-- **The negative alternative is FALSE, stated as its own theorem** (the dispatch asked for
whichever of the two is true; this is the refutation of the other). It is NOT the case that every
`normAlpha`-regular background is flat. -/
theorem regular_class_not_all_flat :
    ¬ ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5,
        GaugeRegular normAlpha U →
          ∀ p : PeriodicLatticePlaquette witL5,
            holonomyElem U p = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  intro hall
  exact curvedRegularU_curved (hall curvedRegularU curvedRegularU_gaugeRegular curvedPlaq)

/-- **MUST-NOT-FIRE control on §4** — the curvature clause is not free: the FLAT background
`trivialU witL5` is also `normAlpha`-regular, and it satisfies the flatness the curved witness
denies. So `regular_class_contains_curved` is a statement about the class being STRICTLY larger
than the flat point, not a tautology about regularity. -/
theorem trivialU_gaugeRegular_and_flat :
    GaugeRegular normAlpha (trivialU witL5) ∧
      ∀ p : PeriodicLatticePlaquette witL5,
        holonomyElem (trivialU witL5) p = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨gaugeRegular_of_frobSupBond_le ?_, fun p =>
    AdalyFormal.Balaban.DeltaPrime.holonomyElem_trivialU p⟩
  have h : frobSupBond (trivialU witL5) = 0 := by
    unfold frobSupBond
    refine le_antisymm (Finset.sup'_le _ _ (fun b _ => ?_)) ?_
    · have : ((trivialU witL5 b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl
      rw [this, sub_self, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
    · exact frobSupBond_nonneg (trivialU witL5)
  rw [h]
  exact le_of_lt normAlpha_pos

#print axioms curvedT
#print axioms curvedT_pos
#print axioms curvedT_ne_zero
#print axioms curvedRegularU
#print axioms two_sqrt_two_le_five
#print axioms frobSupBond_curvedRegularU_le
#print axioms curvedRegularU_gaugeRegular
#print axioms curvedRegularU_curved
#print axioms curvedRegularU_not_gaugeTransform_of_flat
#print axioms regular_class_contains_curved
#print axioms regular_class_not_all_flat
#print axioms trivialU_gaugeRegular_and_flat

/-! ## §5 — SINGLE-ACTIVE-BOND FIELDS: the machinery `Reg_nonconstant` needs

`Reg_nonconstant` demands two DISTINCT backgrounds INSIDE the regular class at which `Δ` genuinely
differs. `SpineCoercivityInstance.deltaKCLMNormalized_nonconstant` supplies a distinguishing pair
on `witnessL` — but `witnessL μ = 3` fails `deltaKNormalized_gaugeRegular_coercive`'s own
`hL : 4 ≤ L μ`, and one of its two backgrounds (`centralHolonomyU`) is precisely the one §3 throws
OUT of the regular class. So neither that theorem nor its pair transfers: the separation has to be
re-done on `witL5`, between two backgrounds BOTH regular at `normAlpha`.

The pair used is `trivialU witL5` (flat, regular) and `curvedRegularU` (curved, regular, §4). The
test field is a single-active-bond field, for which every quantity below is computable in closed
form on ANY extent:

* `dstarDQuadForm U (spikeWitness b₀)` is **independent of `U`** — at each plaquette at most one of
  the four `A′` terms survives, and each is `±R(g)·suTwoWitness` with `R(g)` an isometry, so the
  norm is `‖suTwoWitness‖` or `0` according to whether the plaquette touches `b₀`, a condition that
  does not mention `U` at all.
* `deltaPrimeSecondTerm U (spikeWitness b₀) p = 0` for the same reason — at most one `A′` is
  nonzero, so all six commutators have a zero factor.
* `deltaPrimeFirstTerm U (spikeWitness b₀) p` is `0` off `b₀`'s plaquettes and
  `2 − Re tr U(∂p) = defectOfElem(U(∂p))/2 ≥ 0` on them, because `suTwoWitness² = −1` and
  conjugation preserves that.

So the whole `U`-dependence of `deltaKQuadFormNormalizedCorrected U (spikeWitness b₀)` sits in
`Δ′`, with a definite SIGN, and the two backgrounds are separated by it. -/

section Spike

variable {L : PeriodicLatticeExtent}

open AdalyFormal.Balaban.DeltaPrime (AprimeXY AprimeYZ AprimeZW AprimeWX commutatorMatrixSum
  reHolonomy holonomyElemInv deltaPrimeFirstTerm deltaPrimeSecondTerm deltaPrimePlaqTerm
  deltaPrimeQuadForm deltaPrimeQuadForm_vanishes_at_trivial
  commutatorMatrixSum_eq_zero_of_a1a2a4_zero commutatorMatrixSum_eq_zero_of_a2a3a4_zero)
open AdalyFormal.Balaban.NonFlatBackground (defectOfElem defectOfElem_nonneg defectOfElem_inv
  defectOfElem_one defectOfElem_rotElem rotElem)
open AdalyFormal.Balaban.NormalizedCounterexampleSearch (trace_inv_re_eq_trace_re)
open AdalyFormal.Balaban.NormalizationAudit (deltaPrimeQuadFormNormalizedTransported
  deltaPrimeQuadFormNormalizedTransported_eq_half_transported)
open AdalyFormal.Balaban.DeltaPrime (deltaPrimeQuadFormTransported_eq_neg)

/-- The single-active-bond FIELD carrying `suTwoWitness`, extent-generic. -/
noncomputable def spikeWitness (b₀ : Bond L) : Bond L → SuTwo :=
  fun b => if b = b₀ then suTwoWitness else 0

theorem spikeWitness_at (b₀ : Bond L) : spikeWitness b₀ b₀ = suTwoWitness := by
  rw [spikeWitness, if_pos rfl]

theorem spikeWitness_off (b₀ : Bond L) {b : Bond L} (h : b ≠ b₀) : spikeWitness b₀ b = 0 := by
  rw [spikeWitness, if_neg h]

/-- **LAW-19 consolidation, not a third copy.** `DeltaPrime.deltaWitnessConfig` IS this family at
`b₀ = (witnessY, 0)` — `rfl`. -/
theorem deltaWitnessConfig_eq_spikeWitness :
    AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig
      = spikeWitness (witnessY, (0 : Fin 3)) := rfl

/-- `p`'s boundary contains `b₀`. Manifestly `U`-independent — that is the whole point. -/
def Touches (b₀ : Bond L) (p : PeriodicLatticePlaquette L) : Prop :=
  (p.1, p.2.1.1) = b₀ ∨ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = b₀ ∨
    (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = b₀ ∨ (p.1, p.2.1.2) = b₀

/-- `R(g)` squares a `−1`-squaring element to `−1` again: `(gSg^H)² = gS²g^H = −gg^H = −1`. -/
theorem rmap_suTwoWitness_sq (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((RMap g suTwoWitness : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((RMap g suTwoWitness : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
      = -1 := by
  have hu : (g : Matrix (Fin 2) (Fin 2) ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ = 1 := by
    have h1 := Matrix.mem_unitaryGroup_iff.mp g.2.1
    rwa [Matrix.star_eq_conjTranspose] at h1
  have hu' : ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have h1 := Matrix.mem_unitaryGroup_iff'.mp g.2.1
    rwa [Matrix.star_eq_conjTranspose] at h1
  rw [RMap_coe_apply]
  calc (g : Matrix (Fin 2) (Fin 2) ℂ) * (suTwoWitness : Matrix (Fin 2) (Fin 2) ℂ) *
          ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * (suTwoWitness : Matrix (Fin 2) (Fin 2) ℂ) *
          ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ)
      = (g : Matrix (Fin 2) (Fin 2) ℂ) * (suTwoWitness : Matrix (Fin 2) (Fin 2) ℂ) *
          (((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (g : Matrix (Fin 2) (Fin 2) ℂ)) *
          (suTwoWitness : Matrix (Fin 2) (Fin 2) ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
        noncomm_ring
    _ = (g : Matrix (Fin 2) (Fin 2) ℂ) *
          ((suTwoWitness : Matrix (Fin 2) (Fin 2) ℂ) *
            (suTwoWitness : Matrix (Fin 2) (Fin 2) ℂ)) *
          ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by rw [hu']; noncomm_ring
    _ = -1 := by
        rw [AdalyFormal.Balaban.DeltaPrime.suTwoWitness_coe_sq]
        rw [show (g : Matrix (Fin 2) (Fin 2) ℂ) * (-1 : Matrix (Fin 2) (Fin 2) ℂ) *
          ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
            = -((g : Matrix (Fin 2) (Fin 2) ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) by
          noncomm_ring]
        rw [hu]

/-- `‖R(g)·suTwoWitness‖ = ‖suTwoWitness‖`. -/
theorem norm_rmap_suTwoWitness (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ‖(RMap g suTwoWitness : SuTwo)‖ = ‖(suTwoWitness : SuTwo)‖ :=
  (AdalyFormal.Balaban.SuTwoInner.RIsometry g).norm_map suTwoWitness

/-- **The four bonds of a plaquette are pairwise distinct** on a nondegenerate extent. -/
theorem plaq_bonds_distinct (hnd : ∀ μ : Fin 3, 0 < L μ) (p : PeriodicLatticePlaquette L) :
    (p.1, p.2.1.1) ≠ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∧
    (p.1, p.2.1.1) ≠ (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∧
    (p.1, p.2.1.1) ≠ (p.1, p.2.1.2) ∧
    (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ≠ (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∧
    (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ≠ (p.1, p.2.1.2) ∧
    (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ≠ (p.1, p.2.1.2) := by
  have hmn : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  refine ⟨fun hc => hmn (congrArg Prod.snd hc), fun hc => ?_, fun hc => hmn (congrArg Prod.snd hc),
    fun hc => hmn (congrArg Prod.snd hc).symm, fun hc => ?_,
    fun hc => hmn (congrArg Prod.snd hc)⟩
  · exact shift_ne_self p.1 p.2.1.2 (hnd _) (congrArg Prod.fst hc).symm
  · exact shift_ne_self p.1 p.2.1.1 (hnd _) (congrArg Prod.fst hc)

/-- Off `b₀`'s plaquettes the covariant curl of the spike field vanishes — every one of the four
`A′` terms reads the field at a bond that is not `b₀`. -/
theorem spike_curl_of_not_touches
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (p : PeriodicLatticePlaquette L) (h : ¬ Touches b₀ p) :
    curlValueCovariant U (spikeWitness b₀) p = 0 := by
  unfold Touches at h
  push_neg at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold curlValueCovariant
  rw [spikeWitness_off b₀ h1, spikeWitness_off b₀ h2, spikeWitness_off b₀ h3,
    spikeWitness_off b₀ h4]
  simp

/-- On `b₀`'s plaquettes the covariant curl is `±R(g)·suTwoWitness` for an explicit `g` read off
the background — the ONLY place `U` enters, and it enters through an isometry. -/
theorem spike_curl_of_touches
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) (p : PeriodicLatticePlaquette L) (h : Touches b₀ p) :
    ∃ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      curlValueCovariant U (spikeWitness b₀) p = (RMap g suTwoWitness : SuTwo) ∨
        curlValueCovariant U (spikeWitness b₀) p = -(RMap g suTwoWitness : SuTwo) := by
  obtain ⟨d12, d13, d14, d23, d24, d34⟩ := plaq_bonds_distinct hnd p
  unfold curlValueCovariant
  rcases h with h1 | h2 | h3 | h4
  · refine ⟨1, Or.inl ?_⟩
    subst h1
    rw [spikeWitness_at, spikeWitness_off _ d12.symm, spikeWitness_off _ d13.symm,
      spikeWitness_off _ d14.symm, RMap_one]
    simp
  · refine ⟨U (p.1, p.2.1.1), Or.inl ?_⟩
    subst h2
    rw [spikeWitness_at, spikeWitness_off _ d12, spikeWitness_off _ d23.symm,
      spikeWitness_off _ d24.symm]
    simp
  · refine ⟨U (p.1, p.2.1.2), Or.inr ?_⟩
    subst h3
    rw [spikeWitness_at, spikeWitness_off _ d13, spikeWitness_off _ d23,
      spikeWitness_off _ d34.symm]
    simp
  · refine ⟨1, Or.inr ?_⟩
    subst h4
    rw [spikeWitness_at, spikeWitness_off _ d14, spikeWitness_off _ d24,
      spikeWitness_off _ d34, RMap_one]
    simp

/-- `‖curl‖ = ‖suTwoWitness‖` on `b₀`'s plaquettes — **independent of `U`**. -/
theorem norm_spike_curl_of_touches
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) (p : PeriodicLatticePlaquette L) (h : Touches b₀ p) :
    ‖curlValueCovariant U (spikeWitness b₀) p‖ = ‖(suTwoWitness : SuTwo)‖ := by
  obtain ⟨g, hg | hg⟩ := spike_curl_of_touches U b₀ hnd p h
  · rw [hg, norm_rmap_suTwoWitness]
  · rw [hg, norm_neg, norm_rmap_suTwoWitness]

/-- The curl SQUARES to `−1` on `b₀`'s plaquettes, whatever the background. -/
theorem spike_curl_sq_of_touches
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) (p : PeriodicLatticePlaquette L) (h : Touches b₀ p) :
    ((curlValueCovariant U (spikeWitness b₀) p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((curlValueCovariant U (spikeWitness b₀) p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
      = -1 := by
  obtain ⟨g, hg | hg⟩ := spike_curl_of_touches U b₀ hnd p h
  · rw [hg, rmap_suTwoWitness_sq]
  · rw [hg]
    have hneg : ((-(RMap g suTwoWitness : SuTwo) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) =
        -((RMap g suTwoWitness : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
    rw [hneg, neg_mul_neg, rmap_suTwoWitness_sq]

#print axioms spikeWitness
#print axioms spikeWitness_at
#print axioms spikeWitness_off
#print axioms Touches
#print axioms deltaWitnessConfig_eq_spikeWitness
#print axioms rmap_suTwoWitness_sq
#print axioms norm_rmap_suTwoWitness
#print axioms plaq_bonds_distinct
#print axioms spike_curl_of_not_touches
#print axioms spike_curl_of_touches
#print axioms norm_spike_curl_of_touches
#print axioms spike_curl_sq_of_touches

/-! ### §5b — the two `Δ′` sub-terms at a spike field -/

/-- `Re tr(Re U(∂p)) = Re tr(U(∂p))` — extent-generic, `U`-generic. (The tree's
`NormalizedCounterexampleSearch.reHolonomy_trace_re_eq` says this only for `singleBondU` on
`witnessL` and only under a two-case holonomy hypothesis; the fact needs neither.) -/
theorem trace_reHolonomy_re
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Matrix.trace (reHolonomy U p)).re =
      (Matrix.trace ((holonomyElem U p : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold reHolonomy holonomyElemInv
  rw [Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, Complex.mul_re, Complex.add_re,
    Complex.add_im, trace_inv_re_eq_trace_re]
  have h1 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  have h2 : (1 / 2 : ℂ).im = 0 := by norm_num
  rw [h1, h2]
  ring

/-- **The commutator sum vanishes for a spike field** — at every plaquette at most one of the four
`A′` values is nonzero, so each of the six commutators has a zero factor. -/
theorem spike_commutatorMatrixSum_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) (p : PeriodicLatticePlaquette L) :
    commutatorMatrixSum U (spikeWitness b₀) p = 0 := by
  obtain ⟨d12, d13, d14, d23, d24, d34⟩ := plaq_bonds_distinct hnd p
  unfold commutatorMatrixSum AprimeZW AprimeWX AprimeXY AprimeYZ
  by_cases h : Touches b₀ p
  · rcases h with h1 | h2 | h3 | h4
    · subst h1
      rw [spikeWitness_off _ d12.symm, spikeWitness_off _ d13.symm, spikeWitness_off _ d14.symm]
      simp
    · subst h2
      rw [spikeWitness_off _ d12, spikeWitness_off _ d23.symm, spikeWitness_off _ d24.symm]
      simp
    · subst h3
      rw [spikeWitness_off _ d13, spikeWitness_off _ d23, spikeWitness_off _ d34.symm]
      simp
    · subst h4
      rw [spikeWitness_off _ d14, spikeWitness_off _ d24, spikeWitness_off _ d34]
      simp
  · unfold Touches at h
    push_neg at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [spikeWitness_off b₀ h1, spikeWitness_off b₀ h2, spikeWitness_off b₀ h3,
      spikeWitness_off b₀ h4]
    simp

/-- The SECOND `Δ′` term is identically `0` at a spike field. -/
theorem spike_deltaPrimeSecondTerm_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) (p : PeriodicLatticePlaquette L) :
    deltaPrimeSecondTerm U (spikeWitness b₀) p = 0 := by
  unfold deltaPrimeSecondTerm
  rw [spike_commutatorMatrixSum_eq_zero U b₀ hnd p]
  simp

/-- The FIRST `Δ′` term off `b₀`'s plaquettes is `0`. -/
theorem spike_deltaPrimeFirstTerm_of_not_touches
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (p : PeriodicLatticePlaquette L) (h : ¬ Touches b₀ p) :
    deltaPrimeFirstTerm U (spikeWitness b₀) p = 0 := by
  unfold deltaPrimeFirstTerm
  rw [spike_curl_of_not_touches U b₀ p h]
  simp

/-- **The FIRST `Δ′` term ON `b₀`'s plaquettes is EXACTLY half the holonomy defect.**
`tr(C²(Re U(∂p) − 1)) = tr(−(Re U(∂p) − 1)) = 2 − Re tr U(∂p) = defectOfElem(U(∂p))/2 ≥ 0`. -/
theorem spike_deltaPrimeFirstTerm_of_touches
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) (p : PeriodicLatticePlaquette L) (h : Touches b₀ p) :
    deltaPrimeFirstTerm U (spikeWitness b₀) p = defectOfElem (holonomyElem U p) / 2 := by
  unfold deltaPrimeFirstTerm defectOfElem
  rw [spike_curl_sq_of_touches U b₀ hnd p h]
  rw [show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (reHolonomy U p - 1)
      = -(reHolonomy U p) + 1 by noncomm_ring]
  rw [Matrix.trace_add, Matrix.trace_neg]
  simp only [Complex.add_re, Complex.neg_re]
  rw [trace_reHolonomy_re]
  rw [show (Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ)).re = (2 : ℝ) by
    simp [Matrix.trace_fin_two, Matrix.one_apply]]
  ring

/-- Every per-plaquette `Δ′` summand at a spike field is NONNEGATIVE. -/
theorem spike_deltaPrimePlaqTerm_nonneg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) (p : PeriodicLatticePlaquette L) :
    0 ≤ deltaPrimePlaqTerm U (spikeWitness b₀) p := by
  unfold deltaPrimePlaqTerm
  rw [spike_deltaPrimeSecondTerm_eq_zero U b₀ hnd p, add_zero]
  by_cases h : Touches b₀ p
  · rw [spike_deltaPrimeFirstTerm_of_touches U b₀ hnd p h]
    have := defectOfElem_nonneg (holonomyElem U p)
    linarith
  · rw [spike_deltaPrimeFirstTerm_of_not_touches U b₀ p h]

/-- The full `Δ′` quadratic form at a spike field is `≥` any single plaquette's summand. -/
theorem spike_deltaPrimeQuadForm_ge
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) (p₀ : PeriodicLatticePlaquette L) :
    deltaPrimePlaqTerm U (spikeWitness b₀) p₀ ≤ deltaPrimeQuadForm U (spikeWitness b₀) := by
  unfold deltaPrimeQuadForm
  exact Finset.single_le_sum
    (f := fun p : PeriodicLatticePlaquette L => deltaPrimePlaqTerm U (spikeWitness b₀) p)
    (fun q _ => spike_deltaPrimePlaqTerm_nonneg U b₀ hnd q) (Finset.mem_univ p₀)

/-- **`D_U^*D_U` DOES NOT SEE THE BACKGROUND at a spike field** — the leading term is literally the
same real number at every `U`, because the only `U`-dependence is an isometry acting on the single
surviving `A′`. This is what isolates the whole background dependence into `Δ′`. -/
theorem spike_dstarDQuadForm_indep
    (U U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b₀ : Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) :
    dstarDQuadForm U (spikeWitness b₀) = dstarDQuadForm U' (spikeWitness b₀) := by
  rw [AdalyFormal.Balaban.LemmaAssembly.dstarDQuadForm_eq_sum_norm_sq,
    AdalyFormal.Balaban.LemmaAssembly.dstarDQuadForm_eq_sum_norm_sq]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : Touches b₀ p
  · rw [norm_spike_curl_of_touches U b₀ hnd p h, norm_spike_curl_of_touches U' b₀ hnd p h]
  · rw [spike_curl_of_not_touches U b₀ p h, spike_curl_of_not_touches U' b₀ p h]

#print axioms trace_reHolonomy_re
#print axioms spike_commutatorMatrixSum_eq_zero
#print axioms spike_deltaPrimeSecondTerm_eq_zero
#print axioms spike_deltaPrimeFirstTerm_of_not_touches
#print axioms spike_deltaPrimeFirstTerm_of_touches
#print axioms spike_deltaPrimePlaqTerm_nonneg
#print axioms spike_deltaPrimeQuadForm_ge
#print axioms spike_dstarDQuadForm_indep

/-! ## §6 — `Δ` SEPARATES TWO BACKGROUNDS THAT ARE *BOTH* REGULAR AT `normAlpha`

This is what `Reg_nonconstant` demands and what `SpineCoercivityInstance`'s pair cannot give: its
two backgrounds live on `witnessL` (`4 ≤ 3` fails) and one of them (`centralHolonomyU`) is exactly
the configuration §3 EXPELS from the regular class. Here both members of the pair —
`trivialU witL5` and `curvedRegularU` — are `GaugeRegular normAlpha`. -/

/-- The holonomy of the curved regular background at its own base plaquette. -/
theorem holonomy_curvedRegularU_curvedPlaq :
    holonomyElem curvedRegularU curvedPlaq = rotElem curvedT :=
  holonomy_singleBond_base_plaquette (curvedFamilyU curvedT) curvedBond.1 dir01 (rotElem curvedT)
    (bondU_at curvedBond _) (fun _ hb => bondU_off curvedBond _ hb) (by decide)

/-- The base plaquette does touch the active bond. -/
theorem touches_curvedBond_curvedPlaq : Touches curvedBond curvedPlaq := Or.inl rfl

/-- **`Δ′` is STRICTLY POSITIVE at the curved regular background**, on the spike field supported at
the bond carrying the curvature. Value at the base plaquette: `defectOfElem(rotElem t)/2 =
4t²/(1+t²) > 0`, and every other plaquette contributes `≥ 0`. -/
theorem deltaPrimeQuadForm_curvedRegularU_pos :
    0 < deltaPrimeQuadForm curvedRegularU (spikeWitness curvedBond) := by
  have hbase : deltaPrimePlaqTerm curvedRegularU (spikeWitness curvedBond) curvedPlaq
      = defectOfElem (rotElem curvedT) / 2 := by
    unfold deltaPrimePlaqTerm
    rw [spike_deltaPrimeSecondTerm_eq_zero curvedRegularU curvedBond witL5_pos curvedPlaq, add_zero,
      spike_deltaPrimeFirstTerm_of_touches curvedRegularU curvedBond witL5_pos curvedPlaq
        touches_curvedBond_curvedPlaq, holonomy_curvedRegularU_curvedPlaq]
  have hpos : 0 < defectOfElem (rotElem curvedT) / 2 := by
    rw [defectOfElem_rotElem]
    have ht : 0 < curvedT := curvedT_pos
    have hd : (0 : ℝ) < 1 + curvedT ^ 2 := by positivity
    have : 0 < 8 * curvedT ^ 2 / (1 + curvedT ^ 2) := by positivity
    linarith
  have hle := spike_deltaPrimeQuadForm_ge curvedRegularU curvedBond witL5_pos curvedPlaq
  rw [hbase] at hle
  linarith

/-- `Δ′` vanishes identically at the FLAT background (the tree's own general lemma, reused). -/
theorem deltaPrimeQuadForm_trivialU_witL5 :
    deltaPrimeQuadForm (trivialU witL5) (spikeWitness curvedBond) = 0 :=
  deltaPrimeQuadForm_vanishes_at_trivial (spikeWitness curvedBond)

/-- The normalized assembly, unfolded to `D*D − ½Δ′`, general in `U`/`A`. -/
theorem deltaKQuadFormNormalizedCorrected_eq_sub
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaKQuadFormNormalizedCorrected U A
      = dstarDQuadForm U A - (1 / 2 : ℝ) * deltaPrimeQuadForm U A := by
  show dstarDQuadForm U A + deltaPrimeQuadFormNormalizedTransported U A = _
  rw [deltaPrimeQuadFormNormalizedTransported_eq_half_transported,
    deltaPrimeQuadFormTransported_eq_neg]
  ring

/-- **THE SEPARATION, at the level of the quadratic form.** Both backgrounds are
`GaugeRegular normAlpha`; the normalized `Δ_k` form takes DIFFERENT values on the same admissible
test field. All the difference sits in `Δ′`, with a definite sign. -/
theorem deltaKQuadForm_separates_regular_pair :
    deltaKQuadFormNormalizedCorrected curvedRegularU (spikeWitness curvedBond)
      < deltaKQuadFormNormalizedCorrected (trivialU witL5) (spikeWitness curvedBond) := by
  rw [deltaKQuadFormNormalizedCorrected_eq_sub, deltaKQuadFormNormalizedCorrected_eq_sub,
    deltaPrimeQuadForm_trivialU_witL5,
    spike_dstarDQuadForm_indep curvedRegularU (trivialU witL5) curvedBond witL5_pos]
  have := deltaPrimeQuadForm_curvedRegularU_pos
  linarith

/-- **`Δ` GENUINELY VARIES OVER THE REGULAR CLASS.** The two operators differ. -/
theorem deltaKCLMNormalized_ne_on_regular_pair :
    deltaKCLMNormalized (L := witL5) (trivialU witL5) ≠ deltaKCLMNormalized curvedRegularU := by
  intro heq
  have hcongr := congrArg (fun T : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5 =>
    (inner ℝ (WithLp.toLp 2 (spikeWitness curvedBond) : BondFnL2 witL5)
      (T (WithLp.toLp 2 (spikeWitness curvedBond))) : ℝ)) heq
  rw [inner_deltaKCLMNormalized_eq, inner_deltaKCLMNormalized_eq] at hcongr
  have hlt := deltaKQuadForm_separates_regular_pair
  rw [← hcongr] at hlt
  exact lt_irrefl _ hlt

/-- The two backgrounds are distinct configurations (needed for the `U₁ ≠ U₂` clause). -/
theorem trivialU_ne_curvedRegularU : (trivialU witL5) ≠ curvedRegularU := by
  intro h
  have hb := congrFun h curvedBond
  rw [show curvedRegularU curvedBond = rotElem curvedT from bondU_at curvedBond _] at hb
  exact AdalyFormal.Balaban.NonFlatBackground.rotElem_ne_one curvedT_ne_zero hb.symm

#print axioms holonomy_curvedRegularU_curvedPlaq
#print axioms touches_curvedBond_curvedPlaq
#print axioms deltaPrimeQuadForm_curvedRegularU_pos
#print axioms deltaPrimeQuadForm_trivialU_witL5
#print axioms deltaKQuadFormNormalizedCorrected_eq_sub
#print axioms deltaKQuadForm_separates_regular_pair
#print axioms deltaKCLMNormalized_ne_on_regular_pair
#print axioms trivialU_ne_curvedRegularU

end Spike

/-! ## §7 — THE INSTANCE: the real operator inhabits the repaired structure

`H := BondFnL2 witL5` (the `𝔰𝔲(2)`-valued bond `L²` space, the faithful carrier), `Uconfig :=`
the link configurations on `witL5`, `Δ := fun _ U => deltaKCLMNormalized U` (the actual
source-normalized `Δ_k`), `Reg := GaugeRegular normAlpha`, `γ'' := normGamma = 1/2000`,
`V U := axial ∩ ker Q₂(U)`, transported to `BondFnL2` along the linear equivalence
`BondSU2Space.bondFnL2Equiv`.

**Two disclosures a prosecutor is entitled to before reading the term.**

1. **`Δ` carries no genuine `k`-dependence.** `deltaKCLMNormalized` has no `k` argument, so
   `fun _ U => deltaKCLMNormalized U` is `rfl`-constant in `k`
   (`SpineCoercivityInstance.deltaKCLMNormalized_k_independent`, already in the tree — reproduced
   below as `instanceDelta_k_independent` for THIS instance's own `Δ` field so the disclosure is a
   theorem here, not a cross-reference). The structure's fields do not demand `k`-dependence, and
   this instance does not supply it. Nothing below claims RG-scale uniformity.
2. **`H` is NOT `Spine.coerc_u_main`'s carrier.** That lemma fixes
   `H := EuclideanSpace ℝ (Bond Lat)` (fibre dimension 1); this instance lives on `BondFnL2`
   (fibre dimension 3). `IslandBridge.no_linearEquiv_euclid_bondFnL2` proves no linear equivalence
   between them exists. This instance therefore does NOT close `[LEM-COERC-U]` on Spine's carrier;
   it inhabits the repaired STRUCTURE at the operator's own carrier.

**What is NOT an obstruction, measured rather than assumed.** `SpineCoercivityInstance` §4 records
that `CoercivityCov.CoercivityHypothesisCov` cannot take `deltaKCLMNormalized` in its `Δ` field
because that `abbrev` `letI`-forces a `PiLp`-native instance pair that is not the ambient one.
Measured here directly: with `CoercivityCov` imported, ORDINARY instance search at
`H := BondFnL2 witL5` resolves to `CoercivityCov.instNormedAddCommGroupBondFnL2Cov` /
`instInnerProductSpaceBondFnL2Cov` (both are global `instance`s), and `deltaKCLMNormalized U`
DOES elaborate at the resulting `BondFnL2 witL5 →L[ℝ] BondFnL2 witL5`
(`instanceDelta_typechecks` below is that check, as a theorem). So the §4 obstruction is specific
to the `letI`-forced `abbrev`, not to the carrier; `[BRIDGE-SUTWO-NORM]` is not needed for this
structure and is not claimed closed. -/

section RealInstance

variable {L : PeriodicLatticeExtent}

open AdalyFormal.Balaban.BondSU2Space (bondFnL2Equiv)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCovLM lineCoarseRestrictCovLM_apply)

/-- The axial-gauge condition of CMP96 `(2.121)`, over ALL block pairs at once (the coercivity
theorem's own `hadm` hypothesis), as a submodule of bare bond fields. -/
noncomputable def axialBare (L : PeriodicLatticeExtent) : Submodule ℝ (Bond L → SuTwo) where
  carrier := {A | ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
    ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0}
  add_mem' := by
    intro A B hA hB y hy x hx b hb
    show A b + B b = 0
    rw [hA y hy x hx b hb, hB y hy x hx b hb, add_zero]
  zero_mem' := by intro y _ x _ b _; rfl
  smul_mem' := by
    intro c A hA y hy x hx b hb
    show c • A b = 0
    rw [hA y hy x hx b hb, smul_zero]

/-- `axial ∩ ker Q₂(U)` — EXACTLY the domain of `deltaKNormalized_gaugeRegular_coercive`. -/
noncomputable def admKerBare
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Submodule ℝ (Bond L → SuTwo) :=
  axialBare L ⊓ LinearMap.ker (lineCoarseRestrictCovLM U 2)

theorem mem_admKerBare
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {A : Bond L → SuTwo}
    (hax : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0)
    (hker : ∀ c : CoarseBond L 2, lineCoarseRestrictCov U 2 A c = 0) :
    A ∈ admKerBare U :=
  ⟨hax, by
    show lineCoarseRestrictCovLM U 2 A = 0
    exact funext (fun c => hker c)⟩

theorem admKerBare_axial
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {A : Bond L → SuTwo} (h : A ∈ admKerBare U) :
    ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0 := h.1

theorem admKerBare_ker
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {A : Bond L → SuTwo} (h : A ∈ admKerBare U) :
    ∀ c : CoarseBond L 2, lineCoarseRestrictCov U 2 A c = 0 := by
  intro c
  have h2 : lineCoarseRestrictCovLM U 2 A = 0 := h.2
  exact congrFun h2 c

/-- The same subspace, transported to `BondFnL2 L` along the linear EQUIVALENCE
`BondSU2Space.bondFnL2Equiv` — the same construction `CoercivityCov.anchoredVCov` uses, so it is
the same subspace re-typed, not a reconstruction. -/
noncomputable def VReg (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Submodule ℝ (BondFnL2 L) :=
  Submodule.map (bondFnL2Equiv L).symm.toLinearMap (admKerBare U)

theorem toLp_mem_VReg
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {A : Bond L → SuTwo} (h : A ∈ admKerBare U) :
    (WithLp.toLp 2 A : BondFnL2 L) ∈ VReg U :=
  ⟨A, h, rfl⟩

theorem exists_of_mem_VReg
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {v : BondFnL2 L} (h : v ∈ VReg U) :
    ∃ A : Bond L → SuTwo, A ∈ admKerBare U ∧ (WithLp.toLp 2 A : BondFnL2 L) = v := by
  obtain ⟨A, hA, hv⟩ := h
  exact ⟨A, hA, hv⟩

/-- `V U ≠ ⊥` at EVERY background — witnessed by `genWitness U`, which is axial, in `ker Q₂(U)`,
and nonzero, for every `U` (`RegularUDomainWitnessGeneralU`, reused). -/
theorem VReg_ne_bot (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    VReg U ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨(WithLp.toLp 2 (genWitness U) : BondFnL2 L),
    toLp_mem_VReg (mem_admKerBare (genWitness_axial hdvd U) (genWitness_mem_kerQ hdvd U)), ?_⟩
  intro hzero
  apply genWitness_ne_zero hdvd U
  have := congrArg (fun v : BondFnL2 L => (bondFnL2Equiv L) v) hzero
  simpa using this

#print axioms axialBare
#print axioms admKerBare
#print axioms mem_admKerBare
#print axioms admKerBare_axial
#print axioms admKerBare_ker
#print axioms VReg
#print axioms toLp_mem_VReg
#print axioms exists_of_mem_VReg
#print axioms VReg_ne_bot

/-! ### §7b — the coercivity, on the carrier, from `deltaKNormalized_gaugeRegular_coercive` -/

/-- **`CoercivityHypothesisRegular.coercive`'s exact statement, proved for the real operator.** -/
theorem deltaKCLMNormalized_coercive_on_VReg
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular normAlpha U) (v : BondFnL2 L) (hv : v ∈ VReg U) :
    normGamma * ‖v‖ ^ 2 ≤ (inner ℝ v (deltaKCLMNormalized U v) : ℝ) := by
  obtain ⟨A, hA, hvA⟩ := exists_of_mem_VReg hv
  subst hvA
  rw [norm_sq_bondFnL2, inner_deltaKCLMNormalized_eq]
  exact deltaKNormalized_gaugeRegular_coercive hL hdvd U hreg A
    (admKerBare_axial hA) (admKerBare_ker hA)

#print axioms deltaKCLMNormalized_coercive_on_VReg

end RealInstance


/-! ## §8 — THE CARRIER OBSTRUCTION, MEASURED (and the tree's recorded diagnosis CORRECTED)

`SpineCoercivityInstance` §4 and `CoercivityCov` §4 record that `deltaKCLMNormalized` cannot be
assigned to a `CoercivityHypothesis`-shaped `Δ` field at `H := BondFnL2 Lat`, and attribute it to
the two `NormedAddCommGroup` candidates being **"DIFFERENT NORMS on the same 3-real-dimensional
space (Hilbert–Schmidt trace form vs. `Matrix.Norms.L2Operator`'s operator/spectral norm)"**, from
which they conclude *"no `rfl`-style bridge can exist"*.

**Measured here; that diagnosis is wrong, and the true one is narrower.** With `CoercivityCov`
imported, ordinary instance search at `H := BondFnL2 witL5` gives
`CoercivityCov.instNormedAddCommGroupBondFnL2Cov` (`= PiLp.normedAddCommGroup`) and
`instInnerProductSpaceBondFnL2Cov`. Against `deltaKCLMNormalized`'s own instance path:

* the **`AddCommMonoid`** components are `rfl`-equal (`addCommMonoid_diamond_is_rfl` below);
* the **`Module ℝ`** components are `rfl`-equal (`module_diamond_is_rfl` below);
* the **`TopologicalSpace`** components are **NOT** `rfl`-equal — `PiLp.topologicalSpace`
  (`= TopologicalSpace.induced WithLp.ofLp Pi.topologicalSpace`, the product topology transported
  through the fibres' OWN registered topologies) versus the metric topology derived from
  `PiLp.normedAddCommGroup`. Erasing `PiLp.topologicalSpace` from search only moves the failure one
  layer down, to `PiLp.uniformSpace` versus `PseudoMetricSpace.toUniformSpace`.

So there is no norm disagreement to reconcile and `[BRIDGE-SUTWO-NORM]` as described is not the
blocker. The blocker is a TOPOLOGY/UNIFORMITY instance path on the FIBRE `SuTwo` propagated through
`PiLp`, and it is a property of `Balaban/CovariantOperators.lean`'s carrier declarations, outside
this file's write scope. **CORRECTED IN PLACE (nested-validator flag, S75) — the following universal claim OVERSHOT and
is struck; the retained wording is what the file actually establishes.** ~~Its consequence is exact
and applies verbatim to `Balaban.CoercivityHypothesis` itself: no `ContinuousLinearMap`-valued
field over an abstract `[NormedAddCommGroup H]` can receive `deltaKCLMNormalized` at
`H := BondFnL2 L`.~~ **What IS established:** the `ContinuousLinearMap` TYPE carries the topology
as an argument; the topology `deltaKCLMNormalized`'s type carries and the topology an abstract
`[NormedAddCommGroup H]` field-type produces are DIFFERENT TERMS that Lean does not identify at
default transparency (fast `rfl` failure, and `>7 min` without completion at `2·10⁷` heartbeats);
and the nine routes tabulated below each broke at the point named. That is evidence of resistance,
not a proved impossibility — no theorem in this file rules out a route nobody has tried, and the
obvious untried one (repairing the fibre-level `SuTwo` topology/uniformity instance path in
`Balaban/CovariantOperators.lean`) is outside this file's write scope.

Routes ATTEMPTED and where each broke (OPS-1: evidence of resistance, not a label):

| route | breaks at |
|---|---|
| `Δ := fun _ U => deltaKCLMNormalized U` | type mismatch, topology component |
| same, via `by exact` (default-transparency defeq) | `whnf` heartbeat exhaustion at `2·10⁷`, >7 min, no completion |
| `LinearMap.toContinuousLinearMap (deltaKCLMNormalized U).toLinearMap` | synthesized `PiLp.topologicalSpace` ≠ inferred metric topology |
| same, with `letI` pinning `TopologicalSpace` to the metric one | the `.toLinearMap` projection then mismatches instead |
| `⟨deltaLM U, LinearMap.continuous_of_finiteDimensional _⟩` | anonymous constructor re-synthesizes the topology args |
| `refine ⟨⟨deltaLM U, ?_⟩⟩` in tactic mode | same |
| `{ toLinearMap := …, cont := by apply … }` structure notation | same |
| `attribute [-instance] PiLp.topologicalSpace` | failure moves to `PiLp.uniformSpace` |
| a separate `Continuous (Δ …)` FIELD, `by apply LinearMap.continuous_of_finiteDimensional` | `apply` "failed to assign synthesized instance" — the lemma insists on the `PiLp` topology |

**What is NOT blocked, and is therefore what §9 lands.** The `Module` diamond being `rfl` means the
UNDERLYING LINEAR MAP transfers with no friction. `deltaKCLMNormalized U`'s linear map is the SAME
FUNCTION (`deltaLM_apply` is `rfl`), the coercivity statement never mentions continuity, and the
`𝔰𝔲(2)` carrier is finite-dimensional so nothing mathematical is lost — only the BUNDLING. §9
therefore states the linear-map form of the structure and instantiates it with the real operator.
That deviation from `CoercivityHypothesis`'s R3 `ContinuousLinearMap` field is DISCLOSED, is the
only one, and is forced by the measurement above, not chosen. -/

section Obstruction

open AdalyFormal.Balaban.CoercivityCov (instNormedAddCommGroupBondFnL2Cov
  instInnerProductSpaceBondFnL2Cov)

/-- The `AddCommMonoid` halves of the diamond ARE `rfl`-equal. -/
theorem addCommMonoid_diamond_is_rfl :
    (WithLp.instAddCommGroup 2 ((_ : Bond witL5) → SuTwo)).toAddCommMonoid
      = (instNormedAddCommGroupBondFnL2Cov witL5).toAddCommMonoid := rfl

/-- The `Module ℝ` halves of the diamond ARE `rfl`-equal. This is the component the linear-map
form needs, and it is why §9 lands. -/
theorem module_diamond_is_rfl :
    (WithLp.instModule 2 ℝ ((_ : Bond witL5) → SuTwo))
      = (instInnerProductSpaceBondFnL2Cov witL5).toModule := rfl

/-- **MUST-NOT-FIRE CONTROL, and the localisation of the defect.** At a PLAIN fibre (`ℝ`) the very
same `PiLp` topology diamond IS `rfl`. So the obstruction is not a `PiLp` fact and not a "two
different norms" fact — it is specific to the FIBRE `SuTwo`, whose ambient `TopologicalSpace`
instance is `instTopologicalSpaceSubtype` (the induced subtype topology from the ambient matrix
space) while its `NormedAddCommGroup` is `SuTwoInner.instNormedAddCommGroupSuTwo`; those two
instance paths are independent and are not `rfl`-equal, and `PiLp` faithfully propagates the
mismatch. Repairing it means editing `SuTwo`'s instance declarations
(`Balaban/CovariantOperators.lean` / `Balaban/SuTwoInner.lean`) — outside this file's write
scope. -/
theorem pilp_topology_diamond_is_rfl_at_real_fibre :
    (PiLp.topologicalSpace 2 fun _ : Fin 3 => ℝ)
      = (PiLp.normedAddCommGroup (p := 2)
          (α := fun _ : Fin 3 => ℝ)).toUniformSpace.toTopologicalSpace := rfl

#print axioms addCommMonoid_diamond_is_rfl
#print axioms module_diamond_is_rfl
#print axioms pilp_topology_diamond_is_rfl_at_real_fibre

end Obstruction

/-! ## §9 — THE LINEAR-MAP FORM, AND THE INSTANCE AT THE REAL OPERATOR -/

/-- **`CoercivityHypothesisRegularLM`** — `CoercivityHypothesisRegular` with the operator field
UNBUNDLED to a `LinearMap`. Every other field is character-for-character the same. The change is
forced by §8's measurement and is the ONLY deviation from `Balaban.CoercivityHypothesis`'s field
list apart from the two the repair is about (`Reg`, `Reg_nonconstant`) and the `U`-indexing of
`V`. -/
structure CoercivityHypothesisRegularLM (H : Type*) (Uconfig : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial Uconfig] where
  /-- The operator family, as a `LinearMap` (§8). -/
  Δ : ℕ → Uconfig → H →ₗ[ℝ] H
  /-- The regularity predicate — the repair. -/
  Reg : Uconfig → Prop
  /-- The `U`-indexed distinguished subspace. -/
  V : Uconfig → Submodule ℝ H
  /-- KEPT. -/
  V_ne_bot : ∀ U : Uconfig, Reg U → V U ≠ ⊥
  /-- KEPT VERBATIM. -/
  Δ_nonconstant : ∃ (k : ℕ) (U₁ U₂ : Uconfig), U₁ ≠ U₂ ∧ Δ k U₁ ≠ Δ k U₂
  /-- The guard on the repair. -/
  Reg_nonconstant : ∃ (k : ℕ) (U₁ U₂ : Uconfig),
    Reg U₁ ∧ Reg U₂ ∧ U₁ ≠ U₂ ∧ Δ k U₁ ≠ Δ k U₂
  /-- KEPT VERBATIM. -/
  γ'' : ℝ
  /-- KEPT VERBATIM. -/
  γ''_pos : 0 < γ''
  /-- The repaired coercivity. -/
  coercive : ∀ (k : ℕ) (U : Uconfig), Reg U → ∀ v ∈ V U,
    γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (Δ k U v)

section AbstractLM

variable {H Uconfig : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial Uconfig]

/-- **The `ContinuousLinearMap` form is STRICTLY STRONGER**: forgetting continuity is a map, so
`CoercivityHypothesisRegularLM` is a genuine weakening and every theorem below applies a fortiori
to the bundled form whenever the bundled form exists. -/
def CoercivityHypothesisRegular.toLM (h : CoercivityHypothesisRegular H Uconfig) :
    CoercivityHypothesisRegularLM H Uconfig where
  Δ := fun k U => (h.Δ k U).toLinearMap
  Reg := h.Reg
  V := h.V
  V_ne_bot := h.V_ne_bot
  Δ_nonconstant := by
    obtain ⟨k, U₁, U₂, hne, hΔ⟩ := h.Δ_nonconstant
    exact ⟨k, U₁, U₂, hne, fun hc => hΔ (ContinuousLinearMap.coe_injective hc)⟩
  Reg_nonconstant := by
    obtain ⟨k, U₁, U₂, h1, h2, hne, hΔ⟩ := h.Reg_nonconstant
    exact ⟨k, U₁, U₂, h1, h2, hne, fun hc => hΔ (ContinuousLinearMap.coe_injective hc)⟩
  γ'' := h.γ''
  γ''_pos := h.γ''_pos
  coercive := h.coercive

/-- The whole §2 battery, restated for the linear-map form (same proofs; nothing in §2 used
continuity). -/
theorem regLM_nonempty (h : CoercivityHypothesisRegularLM H Uconfig) : ∃ U : Uconfig, h.Reg U := by
  obtain ⟨_, U₁, _, h1, _, _, _⟩ := h.Reg_nonconstant
  exact ⟨U₁, h1⟩

theorem regLM_not_singleton (h : CoercivityHypothesisRegularLM H Uconfig) (U₀ : Uconfig) :
    ¬ ∀ U : Uconfig, h.Reg U → U = U₀ := by
  intro hsing
  obtain ⟨_, U₁, U₂, h1, h2, hne, _⟩ := h.Reg_nonconstant
  exact hne ((hsing U₁ h1).trans (hsing U₂ h2).symm)

theorem deltaLM_not_constant_on_reg (h : CoercivityHypothesisRegularLM H Uconfig) :
    ¬ ∀ (k : ℕ) (U₁ U₂ : Uconfig), h.Reg U₁ → h.Reg U₂ → h.Δ k U₁ = h.Δ k U₂ := by
  intro hconst
  obtain ⟨k, U₁, U₂, h1, h2, _, hΔ⟩ := h.Reg_nonconstant
  exact hΔ (hconst k U₁ U₂ h1 h2)

theorem deltaLM_ne_zero (h : CoercivityHypothesisRegularLM H Uconfig) :
    ∃ (k : ℕ) (U : Uconfig), h.Δ k U ≠ 0 := by
  obtain ⟨k, U₁, U₂, _, hΔ⟩ := h.Δ_nonconstant
  by_cases h1 : h.Δ k U₁ = 0
  · exact ⟨k, U₂, fun h2 => hΔ (h1.trans h2.symm)⟩
  · exact ⟨k, U₁, h1⟩

theorem existsLM_ne_zero_mem_V (h : CoercivityHypothesisRegularLM H Uconfig)
    {U : Uconfig} (hU : h.Reg U) : ∃ v ∈ h.V U, v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot (h.V_ne_bot U hU)

theorem coerciveLM_strict_at_some_point (h : CoercivityHypothesisRegularLM H Uconfig)
    {U : Uconfig} (hU : h.Reg U) (k : ℕ) :
    ∃ v ∈ h.V U, 0 < h.γ'' * ‖v‖ ^ 2 ∧ h.γ'' * ‖v‖ ^ 2 ≤ inner ℝ v (h.Δ k U v) := by
  obtain ⟨v, hv, hne⟩ := existsLM_ne_zero_mem_V h hU
  refine ⟨v, hv, ?_, h.coercive k U hU v hv⟩
  exact mul_pos h.γ''_pos (pow_pos (norm_pos_iff.mpr hne) 2)

end AbstractLM

#print axioms CoercivityHypothesisRegularLM
#print axioms CoercivityHypothesisRegular.toLM
#print axioms regLM_nonempty
#print axioms regLM_not_singleton
#print axioms deltaLM_not_constant_on_reg
#print axioms deltaLM_ne_zero
#print axioms existsLM_ne_zero_mem_V
#print axioms coerciveLM_strict_at_some_point

/-! ### §9b — the term -/

/-- `Nontrivial` for the concrete configuration type, from §6's own separated pair.
(`CoercivitySupply.nontrivial_linkCfg_witL5` states the same fact from a different pair; it is not
imported here, so the fact is re-established from a witness this file needed anyway.) -/
instance nontrivial_linkCfg_witL5 :
    Nontrivial (PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5) :=
  ⟨⟨trivialU witL5, curvedRegularU, trivialU_ne_curvedRegularU⟩⟩

/-- **The real operator's underlying linear map.** Not a new operator: `deltaLM_apply` is `rfl`. -/
noncomputable def deltaLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5) :
    BondFnL2 witL5 →ₗ[ℝ] BondFnL2 witL5 :=
  (deltaKCLMNormalized U).toLinearMap

theorem deltaLM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5)
    (v : BondFnL2 witL5) : deltaLM U v = deltaKCLMNormalized U v := rfl

theorem deltaLM_ne_on_regular_pair :
    deltaLM (trivialU witL5) ≠ deltaLM curvedRegularU := by
  intro h
  exact deltaKCLMNormalized_ne_on_regular_pair (ContinuousLinearMap.coe_injective h)

/-- **THE INSTANCE.** `Δ` is the real `deltaKCLMNormalized` (as its underlying linear map, the same
function by `rfl`); `Reg` is `GaugeRegular 5·10⁻⁷`; `V U` is `axial ∩ ker Q₂(U)`; `γ''` is
`1/2000`; `coercive` is discharged by `LemmaAssemblyNormalized.deltaKNormalized_gaugeRegular_
coercive`; `Reg_nonconstant` is discharged by §6's pair, both members `normAlpha`-regular, one flat
and one genuinely curved. -/
noncomputable def realCoercivityHypothesisRegularLM :
    CoercivityHypothesisRegularLM (BondFnL2 witL5)
      (PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5) where
  Δ := fun _ U => deltaLM U
  Reg := fun U => GaugeRegular normAlpha U
  V := fun U => VReg U
  V_ne_bot := fun U _ => VReg_ne_bot witL5_two_dvd U
  Δ_nonconstant := ⟨0, trivialU witL5, curvedRegularU, trivialU_ne_curvedRegularU,
    deltaLM_ne_on_regular_pair⟩
  Reg_nonconstant := ⟨0, trivialU witL5, curvedRegularU, trivialU_gaugeRegular_and_flat.1,
    curvedRegularU_gaugeRegular, trivialU_ne_curvedRegularU, deltaLM_ne_on_regular_pair⟩
  γ'' := normGamma
  γ''_pos := normGamma_pos
  coercive := fun _ U hreg v hv =>
    deltaKCLMNormalized_coercive_on_VReg witL5_four_le witL5_two_dvd U hreg v hv

/-- Existential form. The `∃` is over NOTHING free (S91): every component is a `def` or a named
theorem above. -/
theorem exists_realCoercivityHypothesisRegularLM :
    Nonempty (CoercivityHypothesisRegularLM (BondFnL2 witL5)
      (PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5)) :=
  ⟨realCoercivityHypothesisRegularLM⟩

/-- **DISCLOSURE — the instance's `Δ` is `rfl`-constant in `k`.** `deltaKCLMNormalized` has no `k`
argument. No RG-scale uniformity is claimed anywhere in this file. -/
theorem instanceDelta_k_independent (k₁ k₂ : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5) :
    realCoercivityHypothesisRegularLM.Δ k₁ U = realCoercivityHypothesisRegularLM.Δ k₂ U := rfl

/-- The instance's `Δ` field IS the real operator, pointwise, by `rfl`. -/
theorem instanceDelta_is_real (k : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5)
    (v : BondFnL2 witL5) :
    realCoercivityHypothesisRegularLM.Δ k U v = deltaKCLMNormalized U v := rfl

/-- The instance's constant is the real one, not a free parameter. -/
theorem realInstance_gamma : realCoercivityHypothesisRegularLM.γ'' = 1 / 2000 := rfl

/-- The instance's regularity predicate EXCLUDES the counterexample background's analogue: at the
instance's own lattice, a central single-bond configuration is thrown out, exactly as
`centralHolonomyU` is on `witnessL` (§3). -/
theorem instanceReg_excludes_central_on_witL5 :
    ¬ realCoercivityHypothesisRegularLM.Reg
        (bondU curvedBond AdalyFormal.Balaban.DeltaKFull.negOneElem) := by
  intro hreg
  have h := frobSq_holonomy_of_gaugeRegular (le_of_lt normAlpha_pos)
    (bondU curvedBond AdalyFormal.Balaban.DeltaKFull.negOneElem) hreg curvedPlaq
  rw [show holonomyElem (bondU curvedBond AdalyFormal.Balaban.DeltaKFull.negOneElem) curvedPlaq
      = AdalyFormal.Balaban.DeltaKFull.negOneElem from
    holonomy_singleBond_base_plaquette _ curvedBond.1 dir01 _ (bondU_at curvedBond _)
      (fun _ hb => bondU_off curvedBond _ hb) (by decide),
    frobSq_negOne_sub_one] at h
  rw [show normAlpha = 1 / 2000000 from rfl] at h
  norm_num at h

#print axioms nontrivial_linkCfg_witL5
#print axioms deltaLM
#print axioms deltaLM_apply
#print axioms deltaLM_ne_on_regular_pair
#print axioms realCoercivityHypothesisRegularLM
#print axioms exists_realCoercivityHypothesisRegularLM
#print axioms instanceDelta_k_independent
#print axioms instanceDelta_is_real
#print axioms realInstance_gamma
#print axioms instanceReg_excludes_central_on_witL5

#print axioms CoercivityHypothesisRegular
#print axioms Δ_nonconstant_of_Reg_nonconstant
#print axioms reg_nonempty
#print axioms reg_not_singleton
#print axioms delta_not_constant_on_reg
#print axioms delta_ne_zero
#print axioms exists_ne_zero_mem_V
#print axioms coercive_strict_at_some_point
#print axioms punit_not_nontrivial
#print axioms ofUnrestrictedDomain

end AdalyFormal.Balaban.CoercivityRegular
