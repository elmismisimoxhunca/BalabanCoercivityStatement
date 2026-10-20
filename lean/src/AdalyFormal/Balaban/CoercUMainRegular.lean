/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CoercivityRegular
import AdalyFormal.Balaban.AnchoredVFull
import AdalyFormal.Balaban.RegularUCoercivity

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

/-!
# `CoercUMainRegular.lean` — `coerc_u_main` RESTATED under Bałaban's own two restrictions

Additive module. Nothing outside this file is edited. `#print axioms` after every block.

## WHAT THIS FILE MEASURES

`Spine.coerc_u_main` omits BOTH of the restrictions CMP99b p.428 states around `C^*Δ_kC`: the
background restriction (3.35)/(3.36) with `Mα_0` small, and the `Q_1B = 0` clause on the subspace.
This file restates the target WITH both and measures what happens.

## HEADLINE FINDINGS, each a compiled theorem below

1. **`α₀` is a free parameter and BOTH ends of its range empty the hypothesis, in OPPOSITE
   directions.** `frobSupBond U ≤ 2√2` for EVERY configuration on EVERY lattice
   (`frobSupBond_le_two_sqrt_two`, new — the tree had the value `2√2` only at one matrix), hence
   `GaugeRegular 3` is the constantly-true predicate
   (`gaugeRegular_three_is_no_restriction`, `exists_positive_alpha_with_vacuous_gaugeRegular`).
   At the other end `GaugeRegular 0 U ↔ U is a pure gauge` (`gaugeRegular_zero_iff_pure_gauge`),
   so the class contains no curvature at all (`gaugeRegular_zero_flat`). **A restatement that
   leaves `α₀` caller-supplied reproduces `TheLemma`'s defect.** The pinned numeral `normAlpha`
   sits strictly inside both collapses (`normAlpha_window`).
2. **The faithful operator satisfies clauses 1 and 4 of the restated target** — self-adjointness
   and coercivity on the restored subspace, at `α₀ = normAlpha`, `γ = normGamma`, on every lattice
   the source estimate admits (`faithful_satisfies_clauses_one_and_four`). The same operator
   provably FAILS coercivity over unrestricted `U` on the one-clause subspace, so the restriction
   is what does the work. Clauses 2 (global PSD) and 3 (non-scalarity) are NOT established here;
   §4a states exactly where each broke.
3. **JUNK STILL INHABITS THE RESTATED TARGET** (`junk_satisfies_RegularConclusion`). `id + P_line`,
   with the line spanned by a ONE-BOND spike field, is `k`-blind, `U`-blind, `ell`-blind, and
   satisfies all four live clauses at EVERY threshold with `γ = 1`. The two restored hypotheses
   repair the statement in the FAITHFULNESS direction and do not touch the `∃ Δ` freedom. Reported
   because three prior repairs to this existential were announced as fixes and were not.
4. **The fifth conjunct is OURS, not Bałaban's** — adjudicated from the adjudicated corpus page
   (§4, verbatim). The source's `k`-clause is "a lower bound `γ_0 > 0` independent of `k` and `U`",
   a statement about the CONSTANT. A `k`-constant family satisfies it. Our conjunct rejects the
   faithful operator and the junk alike (`clause5_rejects_the_object_and_the_junk_alike`), and the
   faithful operator satisfies the source's own clause while failing ours
   (`faithful_uniform_but_k_constant`). Global PSD (Spine's clause 3) is also ours: the page's
   positivity is asserted on the subspace.
5. **The PSD failure has a SHARP, gauge-invariant threshold** (`singleBond_neg_iff`): on the
   single-active-bond family the normalized `Δ_k` form at `deltaWitnessConfig` is `4 − ‖X − 1‖²_F`,
   negative exactly when `‖X − 1‖_F > 2`. The ceiling of `‖X − 1‖_F` is `2√2` (finding 1) and
   `2 = (√2/2)·(2√2)` (`threshold_is_half_sqrt_two_of_ceiling`), so the sign flips strictly inside
   the attainable range. The regularity restriction is on the safe side
   (`singleBond_pos_at_normAlpha`), and without it the same family is negative
   (`singleBond_neg_without_regularity`).

6. **The restored subspace has NO SCALE PARAMETER** (`VReg_has_no_scale_parameter`, `rfl`): both of
   `CoercivityRegular.VReg`'s clauses are pinned at the LITERAL block size `2`. So it describes one
   rung, and the `ell`-degeneracy analysis its `ℝ`-carrier counterpart supports cannot even be posed
   for it. A second place, independent of finding 4, where the encoding has no ladder.
7. **NEW ARROW between the tree's two regularity predicates** (§7):
   `GaugeRegular α₀ U → IsRegularHolonomy U (32α₀²)` (`isRegularHolonomy_of_gaugeRegular`). The two
   predicates had no arrow between them until now, so results stated against one could not transfer
   to the other. It follows from the identity `‖X − 1‖²_F = defectOfElem X` proved in §2c.
8. **Clause 2 CLOSED ON THE WHOLE SPIKE FAMILY** (`spike_psd_of_gaugeRegular`, §7): every bond,
   every background in the regular class, under an explicit smallness condition. Strictly more than
   finding 5, which covered one field over the background family. Still NOT clause 2, which
   quantifies over every vector; the shipped smallness condition is volume-dependent and §7 says
   exactly why that is an artefact of the bound rather than of the statement.
9. **Clause 3 holds at a background inside the regular class** (`faithful_nonScalar_at_trivialU`,
   §6), via a new general-`L` fact: the direction-`0` constant field is flat-curl-free at every
   plaquette of every lattice (`curl_trivialU_constDir`). Not the `∀ U` form the clause demands.

## CARRIER, STATED ONCE

`BondFnL2 L` (`𝔰𝔲(2)`-valued bond `L²`), where the faithful `Δ_k` lives. It is NOT linearly
isomorphic to `coerc_u_main`'s `Anchoring.AnchoredBondSpace Lat`
(`IslandBridge.no_linearEquiv_euclid_bondFnL2`), so nothing here is a substitution into Spine's
declaration; this is `coerc_u_main`'s SHAPE at the faithful operator's own carrier.

## REUSED, NOT REBUILT (LAW-19)

`CoercivityRegular.gaugeRegular_excludes_central` / `regular_class_contains_curved` /
`curvedRegularU_*` / `deltaKCLMNormalized_coercive_on_VReg` / `VReg` / `spikeWitness`;
`LemmaAssembly.frobSq_holonomy_of_gaugeRegular`;
`NormalizedCounterexampleSearch.singleBondU_normalizedCorrected_eq`;
`AlphaAnalyticity.eq_trivialU_of_frobSupBond_le_zero`. `CoercUMainPinned` is deliberately NOT
imported (a gate was reading it when this lane ran); the one `def` in common (`pinnedDelta` /
`regularDelta`) is disclosed at its declaration.
-/

namespace AdalyFormal.Balaban.CoercUMainRegular

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeRegular gaugeRegular_of_frobSupBond_le
  gaugeRegular_gauge_invariant)
open AdalyFormal.Balaban.LemmaAssemblyNormalized (normAlpha normGamma normAlpha_pos normGamma_pos)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open scoped Matrix

/-- Local abbreviation for the configuration type, to keep statements readable. It is the SAME
type `CoercivityRegular`'s instance uses; no new object. -/
abbrev Cfg (L : PeriodicLatticeExtent) : Type :=
  PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L

/-! ## §1 — WHO CHOOSES `α₀`, AND THE TWO WAYS THE CHOICE EMPTIES THE HYPOTHESIS

`AlphaAnalyticity.GaugeRegular α₀ U := ∃ γ, frobSupBond (U^γ) ≤ α₀`. `α₀` is a **free real
parameter of the predicate**: whoever writes the statement picks it, and nothing in the predicate
bounds it. This section proves that BOTH extreme choices destroy the content, in OPPOSITE
directions, so that "restore Bałaban's regularity restriction" is not a well-defined instruction
until a numeral is named.
-/

section AlphaWindow

variable {L : PeriodicLatticeExtent}

/-- `‖X‖²_F = 2` for every `X ∈ SU(2)` — `tr(X Xᴴ) = tr 1 = 2`. -/
theorem frobSq_su_eq_two (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobSq (X : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
  rw [AdalyFormal.Balaban.RMapLipschitz.frobSq_eq_trace]
  have h : (X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    have h1 := Matrix.mem_unitaryGroup_iff.mp X.2.1
    rwa [Matrix.star_eq_conjTranspose] at h1
  rw [h]
  simp

/-- `frobSq (1 : Matrix) = 2`, by direct evaluation. -/
theorem frobSq_one_eq_two : frobSq (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
  unfold AdalyFormal.Balaban.RMapLipschitz.frobSq
  norm_num [Matrix.one_apply]

/-- **`‖X − 1‖²_F ≤ 8` for every `X ∈ SU(2)`.** From `frobSq_sub_le` with both terms `= 2`. -/
theorem frobSq_su_sub_one_le (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobSq ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 8 := by
  have h := AdalyFormal.Balaban.RMapLipschitz.frobSq_sub_le
    (X : Matrix (Fin 2) (Fin 2) ℂ) 1
  rw [frobSq_su_eq_two X, frobSq_one_eq_two] at h
  linarith

theorem sqrt_eight : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- **`‖X − 1‖_F ≤ 2√2` for every `X ∈ SU(2)`.** Attained at `X = −1`
(`CoercivityRegular.frobSq_negOne_sub_one` gives `8` there), so the bound is SHARP. -/
theorem frobNorm_su_sub_one_le (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobNorm ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 2 * Real.sqrt 2 := by
  unfold AdalyFormal.Balaban.RMapLipschitz.frobNorm
  rw [← sqrt_eight]
  exact Real.sqrt_le_sqrt (frobSq_su_sub_one_le X)

/-- **THE CEILING: `frobSupBond U ≤ 2√2` for EVERY configuration on EVERY lattice.**
The quantity `GaugeRegular` thresholds is BOUNDED, so a large enough `α₀` bounds nothing. -/
theorem frobSupBond_le_two_sqrt_two (U : Cfg L) : frobSupBond U ≤ 2 * Real.sqrt 2 := by
  unfold AdalyFormal.Balaban.RegularUPerturbation.frobSupBond
  exact Finset.sup'_le _ _ (fun b _ => frobNorm_su_sub_one_le (U b))

/-- **COLLAPSE (LARGE `α₀`) — the mandatory vacuity exhibit.** At any threshold `α₀ ≥ 2√2` the
predicate `GaugeRegular α₀` is satisfied by EVERY background: it is the constantly-true predicate,
and "restricted to regular `U`" restricts nothing. -/
theorem gaugeRegular_of_two_sqrt_two_le {α₀ : ℝ} (h : 2 * Real.sqrt 2 ≤ α₀) (U : Cfg L) :
    GaugeRegular α₀ U :=
  gaugeRegular_of_frobSupBond_le (le_trans (frobSupBond_le_two_sqrt_two U) h)

/-- `2√2 ≤ 3` (i.e. `8 ≤ 9`), so a bare NUMERAL exhibits the collapse. -/
theorem two_sqrt_two_le_three : 2 * Real.sqrt 2 ≤ 3 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- **The sign-flip threshold of §2c, located inside the attainable range.** `‖X − 1‖_F` ranges over
`[0, 2√2]` (`frobNorm_su_sub_one_le`, sharp at `X = −1`), and the value `2` at which the `Δ_k` form
changes sign is `(√2/2)` of that ceiling. Stated as a theorem so no docstring carries an
un-asserted ratio. -/
theorem threshold_is_half_sqrt_two_of_ceiling :
    (2 : ℝ) = (Real.sqrt 2 / 2) * (2 * Real.sqrt 2) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [hs]

/-- **THE EXHIBIT, at a numeral.** `GaugeRegular 3` holds of every background on every lattice. -/
theorem gaugeRegular_three_is_no_restriction (U : Cfg L) : GaugeRegular (3 : ℝ) U :=
  gaugeRegular_of_two_sqrt_two_le two_sqrt_two_le_three U

/-- **THE ANCESTRAL DEFECT, as one statement.** There is a STRICTLY POSITIVE threshold at which
`GaugeRegular` is uniformly vacuous. So a restatement of `coerc_u_main` that quantifies `α₀`
existentially, or leaves it as a free parameter with only `0 < α₀`, has NOT restored Bałaban's
hypothesis: the same statement is available with the restriction carrying no information.
This is the exact shape `TheLemma`'s threshold had. -/
theorem exists_positive_alpha_with_vacuous_gaugeRegular :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ U : Cfg L, GaugeRegular α₀ U :=
  ⟨3, by norm_num, gaugeRegular_three_is_no_restriction⟩

/-- **MUST-NOT-FIRE for the exhibit.** The collapse is a property of LARGE thresholds, not of the
predicate: at the operative numeral `normAlpha = 5·10⁻⁷` the predicate is NOT constantly true —
`centralHolonomyU` is thrown out, gauge-invariantly. (Reused, not rebuilt:
`CoercivityRegular.gaugeRegular_normAlpha_excludes_central`, LAW-19.) -/
theorem gaugeRegular_normAlpha_is_a_restriction :
    ¬ ∀ U : Cfg AdalyFormal.Balaban.AdmissibleSubspace.witnessL, GaugeRegular normAlpha U := by
  intro h
  exact AdalyFormal.Balaban.CoercivityRegular.gaugeRegular_normAlpha_excludes_central
    (h AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU)

/-- **THE TRANSITION IS REAL, not an artefact of the bound being loose.** The very background the
operative threshold rejects is ACCEPTED at `α₀ = 3`. So the two ends of the `α₀` axis genuinely
disagree about a specific configuration. -/
theorem central_is_regular_at_three :
    GaugeRegular (3 : ℝ) AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU :=
  gaugeRegular_three_is_no_restriction _

/-! ### §1b — COLLAPSE (SMALL `α₀`): at `α₀ = 0` the class is exactly the FLAT gauge orbit

The opposite failure. `AlphaAnalyticity.eq_trivialU_of_frobSupBond_le_zero` says `frobSupBond U ≤ 0`
forces `U = trivialU`; therefore `GaugeRegular 0 U` says exactly that `U` is a pure gauge, and a
pure gauge has identically trivial holonomy. So at `α₀ = 0` no curved background survives and every
`∀ regular U` statement is a statement about flat backgrounds only. -/

/-- **`GaugeRegular 0 U ↔ U is a pure gauge`** — an exact characterisation, both directions. -/
theorem gaugeRegular_zero_iff_pure_gauge (U : Cfg L) :
    GaugeRegular 0 U ↔
      ∃ γ : AdalyFormal.Balaban.AlphaAnalyticity.GaugeFn L,
        periodicGaugeTransform γ U = trivialU L := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, AdalyFormal.Balaban.AlphaAnalyticity.eq_trivialU_of_frobSupBond_le_zero hγ⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    rw [hγ]
    exact le_of_eq (AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU L)

/-- **CONSEQUENCE — no curvature at `α₀ = 0`.** Every `GaugeRegular 0` background has identically
trivial plaquette holonomy. So the `α₀ = 0` end of the axis makes the "regular" class carry no
field strength at all: a statement quantified over it says nothing about Yang–Mills. -/
theorem gaugeRegular_zero_flat (U : Cfg L) (h : GaugeRegular 0 U)
    (p : PeriodicLatticePlaquette L) :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem U p
      = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  obtain ⟨γ, hγ⟩ := (gaugeRegular_zero_iff_pure_gauge U).mp h
  have hU : U = periodicGaugeTransform
      (AdalyFormal.Balaban.AlphaAnalyticity.gaugeInv γ) (trivialU L) := by
    rw [← hγ, AdalyFormal.Balaban.AlphaAnalyticity.gaugeTransform_inv]
  rw [hU]
  exact AdalyFormal.Balaban.RegularityHolonomy.holonomyElem_periodicGaugeTransform_trivialU _ p

/-- **THE WINDOW, as one theorem.** For the pinned numeral `normAlpha`, and ONLY between the two
collapses, all three of the following hold simultaneously at the lattice the coercivity theorem
admits: the class is a PROPER restriction (it rejects a background), it CONTAINS a genuinely curved
background, and it is not the whole space. Each conjunct fails at one of the two endpoints:
conjunct 1 fails at `α₀ = 3` (`central_is_regular_at_three`), conjunct 2 fails at `α₀ = 0`
(`gaugeRegular_zero_flat`). -/
theorem normAlpha_window :
    (∃ U : Cfg AdalyFormal.Balaban.AdmissibleSubspace.witnessL, ¬ GaugeRegular normAlpha U) ∧
      (∃ U : Cfg AdalyFormal.Balaban.RegularUDomainWitness.witL5,
        GaugeRegular normAlpha U ∧
          ∃ p : PeriodicLatticePlaquette AdalyFormal.Balaban.RegularUDomainWitness.witL5,
            AdalyFormal.Balaban.DeltaPrime.holonomyElem U p
              ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
  ⟨⟨AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU,
      AdalyFormal.Balaban.CoercivityRegular.gaugeRegular_normAlpha_excludes_central⟩,
    AdalyFormal.Balaban.CoercivityRegular.regular_class_contains_curved⟩

#print axioms frobSq_su_eq_two
#print axioms frobSq_one_eq_two
#print axioms frobSq_su_sub_one_le
#print axioms sqrt_eight
#print axioms frobNorm_su_sub_one_le
#print axioms frobSupBond_le_two_sqrt_two
#print axioms gaugeRegular_of_two_sqrt_two_le
#print axioms two_sqrt_two_le_three
#print axioms threshold_is_half_sqrt_two_of_ceiling
#print axioms gaugeRegular_three_is_no_restriction
#print axioms exists_positive_alpha_with_vacuous_gaugeRegular
#print axioms gaugeRegular_normAlpha_is_a_restriction
#print axioms central_is_regular_at_three
#print axioms gaugeRegular_zero_iff_pure_gauge
#print axioms gaugeRegular_zero_flat
#print axioms normAlpha_window

end AlphaWindow

/-! ## §2 — THE RESTATED TARGET, AND WHAT THE FAITHFUL OPERATOR DOES TO IT

`RegularConclusionAt` is `Spine.coerc_u_main`'s conclusion with

* the background restricted to `GaugeRegular α₀` in every clause that quantifies over `U`,
* the subspace replaced by `CoercivityRegular.VReg U = axial ⊓ ker Q₂(U)` — CMP99b p.428's `Q₁B = 0`
  clause restored, and `U`-INDEXED (Bałaban's subspace moves with the background; the flat
  `ℝ`-carrier analogue is `AnchoredVFull.kerQOne`),
* `Δ` a PARAMETER rather than an existential, so the statement can be pinned,
* `α₀` and `γ` PARAMETERS, so that §1's collapses are visible in the type rather than hidden,
* and the FIFTH conjunct (`∃ U k₁ k₂, k₁ ≠ k₂ ∧ Δ k₁ U ≠ Δ k₂ U`) **omitted** — kept separately in
  `RegularConclusionWithRG` and measured there. §4 gives the reason.

The carrier is `BondFnL2 L` (`𝔰𝔲(2)`-valued bond `L²`), not `Anchoring.AnchoredBondSpace Lat`,
because that is where the tree's faithful `Δ_k` lives and the two are provably not linearly
isomorphic (`IslandBridge.no_linearEquiv_euclid_bondFnL2`). So this is `coerc_u_main`'s SHAPE at the
faithful operator's own carrier, exactly as `CoercUMainPinned` §1 is; no substitution into Spine's
declaration is claimed. -/

section RestatedTarget

variable {L : PeriodicLatticeExtent}

/-- **THE RESTATED TARGET.** Four clauses; see the section docstring for what each replaces. -/
def RegularConclusionAt (L : PeriodicLatticeExtent) (α₀ γ : ℝ)
    (Δ : ℕ → Cfg L → (BondFnL2 L →L[ℝ] BondFnL2 L)) : Prop :=
  (∀ (k : ℕ) (U : Cfg L), ContinuousLinearMap.adjoint (Δ k U) = Δ k U) ∧
    (∀ (k : ℕ) (U : Cfg L), GaugeRegular α₀ U →
      ∀ v : BondFnL2 L, 0 ≤ (inner ℝ v (Δ k U v) : ℝ)) ∧
    (∀ (k : ℕ) (U : Cfg L), GaugeRegular α₀ U →
      ∀ c : ℝ, Δ k U ≠ c • ContinuousLinearMap.id ℝ (BondFnL2 L)) ∧
    (0 < γ ∧ ∀ (k : ℕ) (U : Cfg L), GaugeRegular α₀ U →
      ∀ v ∈ AdalyFormal.Balaban.CoercivityRegular.VReg U,
        γ * ‖v‖ ^ 2 ≤ (inner ℝ v (Δ k U v) : ℝ))

/-- The same, WITH the fifth conjunct restored, so the two can be compared one `#check` apart. -/
def RegularConclusionWithRG (L : PeriodicLatticeExtent) (α₀ γ : ℝ)
    (Δ : ℕ → Cfg L → (BondFnL2 L →L[ℝ] BondFnL2 L)) : Prop :=
  RegularConclusionAt L α₀ γ Δ ∧
    (∃ (U : Cfg L) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ Δ k₁ U ≠ Δ k₂ U)

/-- **THE PIN.** `Δ k U := deltaKCLMNormalized U`, the tree's source-normalized `Δ_k` at `η = 1`.
DISCLOSED DUPLICATION (LAW-19): `CoercUMainPinned.pinnedDelta` is the same `def`. It is not imported
because this lane was directed not to build on that module while a gate is reading it; the two are
the same term, and the shared underlying object `DeltaPrimeOperator.deltaKCLMNormalized` is what
both name. -/
noncomputable def regularDelta (L : PeriodicLatticeExtent) :
    ℕ → Cfg L → (BondFnL2 L →L[ℝ] BondFnL2 L) :=
  fun _ U => AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U

theorem regularDelta_apply (k : ℕ) (U : Cfg L) :
    regularDelta L k U = AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U := rfl

/-! ### §2a — CLAUSE 1 (self-adjointness): SATISFIED, unconditionally in `U` -/

theorem faithful_selfAdjoint (k : ℕ) (U : Cfg L) :
    ContinuousLinearMap.adjoint (regularDelta L k U) = regularDelta L k U := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  exact AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized_symm U x y

/-! ### §2b — CLAUSE 4 (coercivity on the restored subspace): SATISFIED at `α₀ = normAlpha`,
`γ = normGamma`, on every lattice the source estimate admits

This is the whole point of restoring the two hypotheses: the SAME faithful operator that is
NOT coercive on the one-clause subspace over unrestricted `U`
(`SpineCoercivityInstance.deltaKCLMNormalized_not_coercive_on_anchoredVCov`) IS coercive here.
The theorem is `CoercivityRegular`'s; it is consumed, not reproved (LAW-19). -/

theorem faithful_coercive (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (k : ℕ) (U : Cfg L) (hreg : GaugeRegular normAlpha U)
    (v : BondFnL2 L) (hv : v ∈ AdalyFormal.Balaban.CoercivityRegular.VReg U) :
    normGamma * ‖v‖ ^ 2 ≤ (inner ℝ v (regularDelta L k U v) : ℝ) :=
  AdalyFormal.Balaban.CoercivityRegular.deltaKCLMNormalized_coercive_on_VReg hL hdvd U hreg v hv

/-- The restricted subspace is not the zero subspace, so clause 4 is not vacuous. Reused. -/
theorem faithful_V_ne_bot (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (U : Cfg L) :
    AdalyFormal.Balaban.CoercivityRegular.VReg U ≠ ⊥ :=
  AdalyFormal.Balaban.CoercivityRegular.VReg_ne_bot hdvd U

/-! ### §2c — CLAUSE 2 (global PSD): the KNOWN refutation is EXCLUDED, SHARPLY

`CoercUMainPinned.pinned_fails_global_psd` refutes clause 2 for the faithful operator at
`RegularityHolonomy.centralHolonomyU`. That background is thrown out of `GaugeRegular α₀` for every
`α₀ < 1/2` (`CoercivityRegular.gaugeRegular_excludes_central`). This subsection does better than
noting that: it computes the EXACT threshold at which the refutation mechanism switches on, over
the whole single-active-bond family, and shows the regularity restriction is on the safe side of it by the
exact factor `bridge_threshold_at_normAlpha` computes (§7): the induced holonomy-defect ceiling at
`normAlpha` is `8/10¹²`, against the threshold `4` at which the sign flips.

The identity `‖X − 1‖²_F = 4 − 2 Re tr X` for `X ∈ SU(2)` is proved here in general; the tree had
it only as a numerical coincidence at two specific matrices (`RegularUCurvedWitness` §, docstring
of `defectOfElem_tinyMElem`, records the agreement without proving the identity). -/

/-- **`‖X − 1‖²_F = defectOfElem X = 4 − 2 Re tr X`, for every `X ∈ SU(2)`.** -/
theorem frobSq_sub_one_eq_defect (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobSq ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      = AdalyFormal.Balaban.NonFlatBackground.defectOfElem X := by
  rw [AdalyFormal.Balaban.RMapLipschitz.frobSq_eq_trace]
  unfold AdalyFormal.Balaban.NonFlatBackground.defectOfElem
  have hu : (X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    have h1 := Matrix.mem_unitaryGroup_iff.mp X.2.1
    rwa [Matrix.star_eq_conjTranspose] at h1
  have hexp : ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1)ᴴ
      = (X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          - (X : Matrix (Fin 2) (Fin 2) ℂ) - ((X : Matrix (Fin 2) (Fin 2) ℂ))ᴴ + 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    noncomm_ring
  rw [hexp, hu, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_conjTranspose]
  simp [Complex.add_re, Complex.sub_re]
  ring

/-- **THE VALUE, in gauge-invariant form.** On the single-active-bond family the normalized `Δ_k`
quadratic form at `deltaWitnessConfig` is `4 − ‖X − 1‖²_F`. Composition of
`NormalizedCounterexampleSearch.singleBondU_normalizedCorrected_eq` (`= 2 Re tr X`) with the
identity above; the rewriting into the `frobSq` variable is what makes the threshold visible. -/
theorem singleBond_value_eq (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
        (AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU X)
        AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig
      = 4 - frobSq ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  rw [AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU_normalizedCorrected_eq,
    frobSq_sub_one_eq_defect]
  unfold AdalyFormal.Balaban.NonFlatBackground.defectOfElem
  ring

/-- **THE SHARP THRESHOLD.** The clause-2 refutation fires **exactly** when the link deviation
exceeds `2` — i.e. when `‖X − 1‖_F` passes `2`. That threshold is STRICTLY INSIDE the attainable range: the
ceiling is `2√2` (§1) and `2 = (√2/2)·(2√2)` (`threshold_is_half_sqrt_two_of_ceiling`). Both
directions, no slack. -/
theorem singleBond_neg_iff (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
        (AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU X)
        AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig < 0
      ↔ 4 < frobSq ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  rw [singleBond_value_eq]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **THE REGULARITY RESTRICTION KILLS THE WHOLE FAMILY, uniformly and gauge-invariantly.**
For every `X` whose single-bond background is `GaugeRegular α₀` with `32α₀² < 4`, the form is
STRICTLY POSITIVE. The route is the plaquette-curvature bound
(`LemmaAssembly.frobSq_holonomy_of_gaugeRegular`), which consumes only `∃ γ, …` — so no choice of
gauge rescues a counterexample. -/
theorem singleBond_pos_of_gaugeRegular {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hsmall : 32 * α₀ ^ 2 < 4)
    (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hreg : GaugeRegular α₀ (AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU X)) :
    0 < AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
        (AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU X)
        AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig := by
  have h := AdalyFormal.Balaban.LemmaAssembly.frobSq_holonomy_of_gaugeRegular hα₀
    (AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU X) hreg
    AdalyFormal.Balaban.CovariantOperators.witnessPlaquette
  rw [AdalyFormal.Balaban.NormalizedCounterexampleSearch.holonomy_singleBondU_witnessPlaquette]
    at h
  rw [singleBond_value_eq]
  linarith

/-- **At the operative numeral.** `32·(5·10⁻⁷)² = 8·10⁻¹² < 4`. -/
theorem singleBond_pos_at_normAlpha (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hreg : GaugeRegular normAlpha
      (AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU X)) :
    0 < AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
        (AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU X)
        AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig := by
  refine singleBond_pos_of_gaugeRegular (le_of_lt normAlpha_pos) ?_ X hreg
  rw [show normAlpha = 1 / 2000000 from rfl]
  norm_num

/-- **MUST-FIRE control on §2c**: the hypothesis is load-bearing. Dropping regularity, the SAME
family produces a strictly negative value — at `X = −1`, the tree's `centralHolonomyU`. So
`singleBond_pos_of_gaugeRegular` is not a theorem that would hold anyway. -/
theorem singleBond_neg_without_regularity :
    AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
        (AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU
          AdalyFormal.Balaban.DeltaKFull.negOneElem)
        AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig < 0 := by
  rw [singleBond_value_eq, AdalyFormal.Balaban.CoercivityRegular.frobSq_negOne_sub_one]
  norm_num

#print axioms RegularConclusionAt
#print axioms RegularConclusionWithRG
#print axioms regularDelta
#print axioms regularDelta_apply
#print axioms faithful_selfAdjoint
#print axioms faithful_coercive
#print axioms faithful_V_ne_bot
#print axioms frobSq_sub_one_eq_defect
#print axioms singleBond_value_eq
#print axioms singleBond_neg_iff
#print axioms singleBond_pos_of_gaugeRegular
#print axioms singleBond_pos_at_normAlpha
#print axioms singleBond_neg_without_regularity

/-! ### §2d — CLAUSE 5 (RG-scale dependence): REFUTED OF THE PIN, at general `L`

`deltaKCLMNormalized` has no `ℕ` scale argument, so the only way to feed it into a
`ℕ → Cfg L → (H →L[ℝ] H)` field is `fun _ U => …`, which is `rfl`-constant in `k`. Restoring
Bałaban's two hypotheses does nothing to this: the obstruction is in the operator's TYPE, not in
its domain of validity. -/

theorem regularDelta_k_constant (k₁ k₂ : ℕ) (U : Cfg L) :
    regularDelta L k₁ U = regularDelta L k₂ U := rfl

theorem regularDelta_fails_rg_scale_dependence :
    ¬ ∃ (U : Cfg L) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ regularDelta L k₁ U ≠ regularDelta L k₂ U := by
  rintro ⟨U, k₁, k₂, -, hne⟩
  exact hne rfl

/-- **CONSEQUENCE.** For EVERY `α₀` and EVERY `γ`, the pinned faithful operator fails
`RegularConclusionWithRG` — whatever it does to the four live clauses. Restoring the fifth conjunct
therefore makes the restated target FALSE OF THE FAITHFUL OPERATOR, on every lattice, at every
threshold. -/
theorem regularDelta_fails_withRG (α₀ γ : ℝ) :
    ¬ RegularConclusionWithRG L α₀ γ (regularDelta L) := by
  rintro ⟨-, hrg⟩
  exact regularDelta_fails_rg_scale_dependence hrg

#print axioms regularDelta_k_constant
#print axioms regularDelta_fails_rg_scale_dependence
#print axioms regularDelta_fails_withRG

end RestatedTarget

/-! ## §3 — DOES JUNK SURVIVE THE RESTATEMENT? YES. Reported as a theorem, not as a hope.

Three prior repairs to this existential were announced as fixes and were answered by a new
content-free operator. The honest test of the present one is to build the junk and compile it.

`junkDelta b₀ := id + P_{ℝ·s(b₀)}`, the identity perturbed by the orthogonal projection onto the
line spanned by a ONE-BOND spike field. It is:

* `k`-blind and `U`-blind — literally `fun _ _ => …`, so it carries no RG content and no background
  dependence whatsoever;
* blind to `ell`, to the axial-gauge condition, to `Q₁`, and to the whole lattice except for one
  bond;
* yet it satisfies **all four** live clauses of `RegularConclusionAt`, at EVERY `α₀` and with
  `γ = 1`.

So the two restored hypotheses do NOT close the S91 hole in `coerc_u_main`. They repair the
statement in the FAITHFULNESS direction — the faithful operator now satisfies clause 4, which it
provably failed before — and they leave the `∃ Δ` freedom untouched. Pinning `Δ`, not adding
clauses, is the only thing that closes that hole; §2 is stated with `Δ` as a parameter for exactly
this reason. -/

section Junk

variable {L : PeriodicLatticeExtent}

open AdalyFormal.Balaban.CoercivityRegular (spikeWitness spikeWitness_at spikeWitness_off)
open AdalyFormal.Balaban.BondSU2Space (bondFnL2Equiv)

/-- The spanned line: one bond's spike field. -/
noncomputable def junkLine (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) :
    Submodule ℝ (BondFnL2 L) :=
  Submodule.span ℝ {(WithLp.toLp 2 (spikeWitness b₀) : BondFnL2 L)}

/-- **THE JUNK.** `k`-blind, `U`-blind, one-bond. -/
noncomputable def junkDelta (L : PeriodicLatticeExtent)
    (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) :
    ℕ → Cfg L → (BondFnL2 L →L[ℝ] BondFnL2 L) :=
  fun _ _ => ContinuousLinearMap.id ℝ (BondFnL2 L) + (junkLine b₀).starProjection

theorem junkDelta_apply (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) (k : ℕ) (U : Cfg L)
    (v : BondFnL2 L) :
    junkDelta L b₀ k U v = v + (junkLine b₀).starProjection v := rfl

/-- The orthogonal projection is symmetric, in the bare `⟪P x, y⟫ = ⟪x, P y⟫` form this file
uses twice. -/
theorem starProjection_symm (K : Submodule ℝ (BondFnL2 L)) [K.HasOrthogonalProjection]
    (x y : BondFnL2 L) :
    (inner ℝ (K.starProjection x) y : ℝ) = inner ℝ x (K.starProjection y) := by
  have hadj : ContinuousLinearMap.adjoint K.starProjection = K.starProjection := by
    have := (isSelfAdjoint_starProjection K).star_eq
    rwa [ContinuousLinearMap.star_eq_adjoint] at this
  conv_lhs => rw [← hadj]
  exact ContinuousLinearMap.adjoint_inner_left K.starProjection y x

theorem junk_selfAdjoint (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) (k : ℕ) (U : Cfg L) :
    ContinuousLinearMap.adjoint (junkDelta L b₀ k U) = junkDelta L b₀ k U := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  show (inner ℝ (x + (junkLine b₀).starProjection x) y : ℝ)
      = inner ℝ x (y + (junkLine b₀).starProjection y)
  rw [inner_add_left, inner_add_right, starProjection_symm]

/-- `⟪v, P v⟫ = ‖P v‖² ≥ 0` for the orthogonal projection — derived from self-adjointness and
idempotence, so it does not depend on a particular mathlib lemma name for positivity. -/
theorem inner_starProjection_nonneg (K : Submodule ℝ (BondFnL2 L)) [K.HasOrthogonalProjection]
    (v : BondFnL2 L) : 0 ≤ (inner ℝ v (K.starProjection v) : ℝ) := by
  have hadj : ContinuousLinearMap.adjoint K.starProjection = K.starProjection := by
    have := (isSelfAdjoint_starProjection K).star_eq
    rwa [ContinuousLinearMap.star_eq_adjoint] at this
  have hidem : K.starProjection (K.starProjection v) = K.starProjection v :=
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem v)
  have hkey : (inner ℝ v (K.starProjection v) : ℝ)
      = inner ℝ (K.starProjection v) (K.starProjection v) := by
    conv_lhs => rw [← hidem]
    rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
  rw [hkey]
  exact real_inner_self_nonneg

theorem junk_global_psd (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) (k : ℕ) (U : Cfg L)
    (v : BondFnL2 L) : 0 ≤ (inner ℝ v (junkDelta L b₀ k U v) : ℝ) := by
  rw [junkDelta_apply, inner_add_right]
  have h1 : (0 : ℝ) ≤ inner ℝ v v := real_inner_self_nonneg
  have h2 := inner_starProjection_nonneg (junkLine b₀) v
  linarith

theorem junk_coercive (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) (k : ℕ) (U : Cfg L)
    (v : BondFnL2 L) : (1 : ℝ) * ‖v‖ ^ 2 ≤ (inner ℝ v (junkDelta L b₀ k U v) : ℝ) := by
  rw [junkDelta_apply, inner_add_right]
  have h2 := inner_starProjection_nonneg (junkLine b₀) v
  have h1 : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  rw [h1]
  linarith

/-! ### §3a — the junk is NON-SCALAR, provided the lattice has two bonds carrying distinct spikes -/

/-- The transport is the identity on representatives, definitionally. -/
theorem bondFnL2Equiv_toLp (A : AdalyFormal.Balaban.AdmissibleSubspace.Bond L → SuTwo) :
    (bondFnL2Equiv L) (WithLp.toLp 2 A : BondFnL2 L) = A := rfl

theorem toLp_spikeWitness_ne_zero (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) :
    (WithLp.toLp 2 (spikeWitness b₀) : BondFnL2 L) ≠ 0 := by
  intro h
  have := congrArg (fun v : BondFnL2 L => (bondFnL2Equiv L) v) h
  simp only [map_zero] at this
  have hb := congrFun (show spikeWitness (L := L) b₀ = 0 by simpa using this) b₀
  rw [spikeWitness_at] at hb
  exact AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero hb

theorem junk_not_scalar {b₀ b₁ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L} (hne : b₁ ≠ b₀)
    (k : ℕ) (U : Cfg L) (c : ℝ) :
    junkDelta L b₀ k U ≠ c • ContinuousLinearMap.id ℝ (BondFnL2 L) := by
  intro hc
  have hmem : (WithLp.toLp 2 (spikeWitness b₀) : BondFnL2 L) ∈ junkLine b₀ :=
    Submodule.mem_span_singleton_self _
  have hP0 : (junkLine b₀).starProjection (WithLp.toLp 2 (spikeWitness b₀) : BondFnL2 L)
      = (WithLp.toLp 2 (spikeWitness b₀) : BondFnL2 L) :=
    Submodule.starProjection_eq_self_iff.mpr hmem
  have hv₀ne : (WithLp.toLp 2 (spikeWitness b₀) : BondFnL2 L) ≠ 0 :=
    toLp_spikeWitness_ne_zero b₀
  -- evaluate at the spanning vector: `v₀ + v₀ = c • v₀`, and `v₀ ≠ 0`, so `c = 2`
  have hev := congrArg (fun T : BondFnL2 L →L[ℝ] BondFnL2 L =>
    T (WithLp.toLp 2 (spikeWitness b₀) : BondFnL2 L)) hc
  simp only [smul_apply, ContinuousLinearMap.id_apply] at hev
  rw [junkDelta_apply, hP0] at hev
  have hc2 : c = 2 := by
    have h0 : (c - 2) • (WithLp.toLp 2 (spikeWitness b₀) : BondFnL2 L) = 0 := by
      rw [sub_smul, ← hev]
      module
    rcases smul_eq_zero.mp h0 with h | h
    · linarith [sub_eq_zero.mp h]
    · exact absurd h hv₀ne
  subst hc2
  -- evaluate at the SECOND bond's spike: `v₁ + P v₁ = 2 v₁`, so `P v₁ = v₁`, so `v₁ ∈ line`
  have hev1 := congrArg (fun T : BondFnL2 L →L[ℝ] BondFnL2 L =>
    T (WithLp.toLp 2 (spikeWitness b₁) : BondFnL2 L)) hc
  simp only [smul_apply, ContinuousLinearMap.id_apply] at hev1
  rw [junkDelta_apply] at hev1
  have hPv1 : (junkLine b₀).starProjection (WithLp.toLp 2 (spikeWitness b₁) : BondFnL2 L)
      = (WithLp.toLp 2 (spikeWitness b₁) : BondFnL2 L) := by
    have h2 : (2 : ℝ) • (WithLp.toLp 2 (spikeWitness b₁) : BondFnL2 L)
        = (WithLp.toLp 2 (spikeWitness b₁) : BondFnL2 L)
          + (WithLp.toLp 2 (spikeWitness b₁) : BondFnL2 L) := by module
    rw [h2] at hev1
    exact add_left_cancel hev1
  have hmem1 : (WithLp.toLp 2 (spikeWitness b₁) : BondFnL2 L) ∈ junkLine b₀ :=
    Submodule.starProjection_eq_self_iff.mp hPv1
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem1
  have hfun := congrArg (fun v : BondFnL2 L => (bondFnL2Equiv L) v) hr
  simp only [map_smul, bondFnL2Equiv_toLp] at hfun
  have hat1 := congrFun hfun b₁
  rw [Pi.smul_apply, spikeWitness_off b₀ hne, smul_zero, spikeWitness_at] at hat1
  exact AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero hat1.symm

/-- **THE HEADLINE OF §3: JUNK STILL INHABITS THE RESTATED TARGET.** At every threshold `α₀`,
with `γ = 1`, on any lattice carrying two distinct bonds — i.e. every lattice, since the direction
index alone provides them. -/
theorem junk_satisfies_RegularConclusion (α₀ : ℝ)
    {b₀ b₁ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L} (hne : b₁ ≠ b₀) :
    RegularConclusionAt L α₀ 1 (junkDelta L b₀) :=
  ⟨junk_selfAdjoint b₀, fun k U _ v => junk_global_psd b₀ k U v,
    fun k U _ c => junk_not_scalar hne k U c,
    ⟨one_pos, fun k U _ v _ => junk_coercive b₀ k U v⟩⟩

/-- **The junk also survives the FIFTH conjunct's removal being reversed?** No — it fails clause 5
too, for the same reason the faithful operator does. Stated so the comparison in §4 is exact:
clause 5 does not separate the faithful operator from junk; it rejects BOTH. -/
theorem junk_fails_rg_scale_dependence (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) :
    ¬ ∃ (U : Cfg L) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ junkDelta L b₀ k₁ U ≠ junkDelta L b₀ k₂ U := by
  rintro ⟨U, k₁, k₂, -, hne⟩
  exact hne rfl

#print axioms junkLine
#print axioms junkDelta
#print axioms junkDelta_apply
#print axioms starProjection_symm
#print axioms junk_selfAdjoint
#print axioms inner_starProjection_nonneg
#print axioms junk_global_psd
#print axioms junk_coercive
#print axioms bondFnL2Equiv_toLp
#print axioms toLp_spikeWitness_ne_zero
#print axioms junk_not_scalar
#print axioms junk_satisfies_RegularConclusion
#print axioms junk_fails_rg_scale_dependence

end Junk

/-! ## §4 — IS THE FIFTH CONJUNCT BAŁABAN'S, OR OURS? — ADJUDICATED FROM THE PAGE

### The source sentence

`corpus/pages/CMP99b_p428.md` (`verification_status: adjudicated`; pdf p.40 of
`balaban_CMP99_1985_propagators_backgroundfield.pdf`, sha256
`39f8033b…d542861`; 400 dpi render sha256 `128b1172…3012d54`), immediately after (3.158), VERBATIM:

> "It is more convenient to work with the operator `C̃^{(k)}(Λ)`, because it is defined by a
> positive definite operator `C^*Δ_kC` with a lower bound `γ_0 > 0` **independent of `k` and `U`**.
> We have proved it in [4], Lemma 2.4, for operators with `U = 1`. Localizing the operators in
> `Δ_k` and using the methods of Sect. B we can prove it for `C^*Δ_kC` with an arbitrary
> configuration `U` satisfying (3.35), (3.36) with `Mα_0` sufficiently small."

and, three sentences earlier on the same page, the subspace, VERBATIM:

> "This form is considered on the subspace `{B : B = 0 on Λ^c, B = 0 on ⋃_{y∈Λ'} Ax(y), Q_1B = 0}`."

### What that settles, item by item

1. **The fifth conjunct (`∃ U k₁ k₂, k₁ ≠ k₂ ∧ Δ k₁ U ≠ Δ k₂ U`) IS OURS, not the source's.**
   The source's `k`-clause is *"a lower bound `γ_0 > 0` independent of `k` and `U`"* — a statement
   about the CONSTANT, asserting that one number works at every rung. Nothing on the page asks the
   OPERATOR to move with `k`; a `k`-constant family satisfies the source's uniformity perfectly,
   and satisfies it in the STRONGEST way, since uniformity is trivial when there is nothing to be
   uniform over. Our conjunct was introduced to kill `k`-blind junk. It does kill it
   (`junk_fails_rg_scale_dependence`), and it kills the faithful operator too
   (`regularDelta_fails_rg_scale_dependence`), at every lattice and every threshold. A clause that
   rejects both the junk and the object is not a discriminator; it is a defect in the encoding.
   `clause5_rejects_the_object_and_the_junk_alike` below states exactly that, as one theorem.

2. **`Mα_0` is NOT free in the source either** — the page says *"with `Mα_0` sufficiently small"*.
   §1's collapse at `α₀ ≥ 2√2` is therefore not a hypothetical: a restatement that leaves the
   threshold unpinned is unfaithful in the direction the source explicitly closes. And §1b's
   collapse at `α₀ = 0` is the other unfaithfulness the phrase permits if read as "arbitrarily
   small": at `0` the class is exactly the flat gauge orbit.

3. **Global positive-definiteness is ALSO ours.** The source's positivity is asserted for
   `C^*Δ_kC` *on the subspace* — the sentence "this form is considered on the subspace {…}" governs
   (3.156)-(3.158), and `C` is the parametrisation OF that subspace. Clause 3 of `coerc_u_main`
   (`0 ≤ ⟪v, Δ k U v⟫` for EVERY `v` of the whole carrier) is a strengthening we added; the page
   does not assert it, and the tree's own faithful operator refutes it off the regular class
   (§2c's `singleBond_neg_without_regularity`). It is retained in `RegularConclusionAt` because the
   dispatch's target is `coerc_u_main` as printed, but its status is: OUR clause, NOT ESTABLISHED,
   and the exact sharp threshold at which it fails is §2c.

4. **LAW-12 flag, recorded not consumed.** The same sentence defers twice: the `U = 1` case is
   attributed to *"[4], Lemma 2.4"* (CMP96 Lemma 2.4 — the campaign's standing example of a claim
   asserted with no proof in the cited paper), and the general-`U` case is *"we can prove it"*, a
   deferred claim, not a proved theorem. Nothing in this file is built on either; §2b's coercivity
   comes from the tree's own `LemmaAssemblyNormalized.deltaKNormalized_gaugeRegular_coercive`. -/

section SourceUniformity

variable {L : PeriodicLatticeExtent}

/-- **BAŁABAN'S OWN CLAUSE, TRANSCRIBED**: one constant `γ > 0`, working at EVERY rung `k` and at
EVERY background in the regular class, on the restricted subspace. This is the whole `k`-content of
the page. -/
def SourceUniformity (L : PeriodicLatticeExtent) (α₀ γ : ℝ)
    (Δ : ℕ → Cfg L → (BondFnL2 L →L[ℝ] BondFnL2 L)) : Prop :=
  0 < γ ∧ ∀ (k : ℕ) (U : Cfg L), GaugeRegular α₀ U →
    ∀ v ∈ AdalyFormal.Balaban.CoercivityRegular.VReg U,
      γ * ‖v‖ ^ 2 ≤ (inner ℝ v (Δ k U v) : ℝ)

/-- **THE FAITHFUL OPERATOR SATISFIES THE SOURCE'S CLAUSE** — at the pinned numerals, on every
lattice the source estimate admits. -/
theorem faithful_satisfies_sourceUniformity
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    SourceUniformity L normAlpha normGamma (regularDelta L) :=
  ⟨normGamma_pos, fun k U hreg v hv => faithful_coercive hL hdvd k U hreg v hv⟩

/-- **AND IT VIOLATES OUR FIFTH CONJUNCT — at the same time, at the same numerals.** The two facts
together are the finding: the operator the page is about passes the page's own uniformity clause
and fails the clause `coerc_u_main` prints. -/
theorem faithful_uniform_but_k_constant
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    SourceUniformity L normAlpha normGamma (regularDelta L) ∧
      ¬ ∃ (U : Cfg L) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ regularDelta L k₁ U ≠ regularDelta L k₂ U :=
  ⟨faithful_satisfies_sourceUniformity hL hdvd, regularDelta_fails_rg_scale_dependence⟩

/-- **THE FIFTH CONJUNCT IS NOT A DISCRIMINATOR**: it rejects the tree's faithful `Δ_k` and the
content-free junk of §3 alike, at every lattice, every `α₀`, every `γ`. A clause that fires on
the object it is meant to protect is a defect in the encoding, not a guard. -/
theorem clause5_rejects_the_object_and_the_junk_alike
    (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) :
    (¬ ∃ (U : Cfg L) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ regularDelta L k₁ U ≠ regularDelta L k₂ U) ∧
      (¬ ∃ (U : Cfg L) (k₁ k₂ : ℕ), k₁ ≠ k₂ ∧ junkDelta L b₀ k₁ U ≠ junkDelta L b₀ k₂ U) :=
  ⟨regularDelta_fails_rg_scale_dependence, junk_fails_rg_scale_dependence b₀⟩

/-! ### §4a — WHAT THE FAITHFUL OPERATOR DOES TO THE RESTATED TARGET, EXACTLY

Clauses 1 and 4 hold, at the pinned numerals, on every lattice the source estimate admits. That is
strictly more than the pre-restriction statement could get: `SpineCoercivityInstance.
deltaKCLMNormalized_not_coercive_on_anchoredVCov` proves clause 4 FALSE for this same operator over
unrestricted `U` on the one-clause subspace. Restoring `GaugeRegular` and the `Q₁` clause is what
turns that refutation into a theorem.

Clauses 2 and 3 are NOT established here and are NOT claimed:

* **clause 2 (global PSD)** — §2c proves the ONLY refutation family the tree has is excluded
  sharply and uniformly, but "no known counterexample" is not "PSD". The remaining content is a
  DOMINATION statement on the UNRESTRICTED domain: by
  `CoercivityRegular.deltaKQuadFormNormalizedCorrected_eq_sub`, `Δ_k = D^*D − ½Δ′`, so clause 2 is
  exactly `½Δ′ ≤ D^*D` for every field — and `Δ′ ≥ 0` is the tree's own measured sign for spike
  fields (`CoercivityRegular.spike_deltaPrimePlaqTerm_nonneg`). The source asserts positivity only
  on the constrained domain (§4 item 3), so this is a demand with no source behind it, on the one
  domain where the source's own estimate is not stated. ATTEMPTED and where it broke: the tree
  supplies a LOWER bound on `Δ′` for spike fields (`spike_deltaPrimeQuadForm_ge`) and no upper
  bound at all for general fields, so the domination has nothing to be proved against; and
  `NormalizedCounterexampleSearch`'s own §-note records a Python-level family
  (`gradValueCovariant`-generated fields on a rotation background) on which the normalized form is
  IDENTICALLY `0` at every threshold — a semidefinite knife-edge, i.e. exactly the configuration
  in which a domination proof cannot have any slack.
* **clause 3 (non-scalarity)** — not established for this operator at general regular `U` on this
  file's carrier. It is also the clause §3 shows junk satisfies, so it is not what separates the
  two.

`faithful_satisfies_clauses_one_and_four` records what IS proved, as a single term, so no reader
has to reconstruct the partial verdict from prose. -/

theorem faithful_satisfies_clauses_one_and_four
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    (∀ (k : ℕ) (U : Cfg L),
        ContinuousLinearMap.adjoint (regularDelta L k U) = regularDelta L k U) ∧
      (0 < normGamma ∧ ∀ (k : ℕ) (U : Cfg L), GaugeRegular normAlpha U →
        ∀ v ∈ AdalyFormal.Balaban.CoercivityRegular.VReg U,
          normGamma * ‖v‖ ^ 2 ≤ (inner ℝ v (regularDelta L k U v) : ℝ)) :=
  ⟨faithful_selfAdjoint, normGamma_pos, fun k U hreg v hv => faithful_coercive hL hdvd k U hreg v hv⟩

#print axioms SourceUniformity
#print axioms faithful_satisfies_sourceUniformity
#print axioms faithful_uniform_but_k_constant
#print axioms clause5_rejects_the_object_and_the_junk_alike
#print axioms faithful_satisfies_clauses_one_and_four

end SourceUniformity

/-! ## §5 — THE SECOND RESTORED HYPOTHESIS (`Q_kB = 0`): WHAT IT IS, AND THE SCALE IT IS FIXED AT

The dispatch's PART 1 asks for the `Q_kB = 0` clause to be characterised from the definitions, on
both carriers the tree offers.

**On the `ℝ`-carrier** (`coerc_u_main`'s own `AnchoredBondSpace`), the clause is
`AnchoredVFull.kerQOne L ell`, built on the FAITHFUL line-integral average
`LineIntegralAveraging.lineCoarseRestrict` (CMP95 (1.11)/(1.18)), and it is `ell`-INDEXED. Two of
its properties are load-bearing for any restatement and are reused here rather than reproved:
it is a PROPER restriction for `2 ≤ ell` (`AnchoredVFull.kerQOne_ne_top`), and it COLLAPSES TO `⊥`
at `ell = 1` (`AnchoredVFull.kerQOne_one_eq_bot`), which makes the full three-clause subspace `⊥`
there and the goal unstatable (`AnchoredVFull.no_coercivityHypothesis_at_anchoredVFull_one`).

**On the su(2) carrier** — the one the faithful operator lives on, hence the one this file's
restated target uses — the clause is the `U`-DEPENDENT covariant one,
`ker (lineCoarseRestrictCovLM U 2)`, packaged with the axial clause as
`CoercivityRegular.admKerBare U` and transported to `CoercivityRegular.VReg U`.

**THE FINDING OF THIS SECTION, stated as an `rfl` theorem rather than as prose.** `VReg` carries
**no scale parameter at all**: both of its clauses are pinned at the LITERAL block size `2`
(`axialBare` at `CoarseLattice L 2` / `blockOf y 2`, and the `Q` clause at
`lineCoarseRestrictCovLM U 2`). So the restored domain describes ONE rung, at one block size, and
the `ell`-degeneracy analysis that the `ℝ`-carrier object supports cannot even be posed for it.
That is a second place — independent of §4's — where the encoding has no RG ladder to be uniform
over. -/

section RestoredSubspace

variable {L : PeriodicLatticeExtent}

/-- **THE RESTORED SUBSPACE HAS NO SCALE PARAMETER.** Both clauses are at the literal `2`; there is
no `ell` to quantify over, so `VReg` cannot express the `ell`-dependence its `ℝ`-carrier counterpart
`AnchoredVFull.anchoredVFull Lat ell` does. Proved by `rfl`, i.e. it is a fact about the `def`. -/
theorem VReg_has_no_scale_parameter (U : Cfg L) :
    AdalyFormal.Balaban.CoercivityRegular.VReg U
      = Submodule.map
          (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).symm.toLinearMap
          (AdalyFormal.Balaban.CoercivityRegular.axialBare L
            ⊓ LinearMap.ker
                (AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCovLM U 2)) := rfl

/-- Membership in the restored domain, spelled out: the axial clause AND `Q_2(U)B = 0`. Reused
packaging of `CoercivityRegular.mem_admKerBare`/`toLp_mem_VReg`, so a reader can see what the
coercivity clause of §2b actually quantifies over. -/
theorem mem_VReg_of_clauses {U : Cfg L}
    {A : AdalyFormal.Balaban.AdmissibleSubspace.Bond L → SuTwo}
    (hax : ∀ y : PeriodicLatticeSite L, y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf y 2 →
      ∀ b ∈ AdalyFormal.Balaban.AdmissibleSubspace.staircasePath y x, A b = 0)
    (hker : ∀ c : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov U 2 A c = 0) :
    (WithLp.toLp 2 A : BondFnL2 L) ∈ AdalyFormal.Balaban.CoercivityRegular.VReg U :=
  AdalyFormal.Balaban.CoercivityRegular.toLp_mem_VReg
    (AdalyFormal.Balaban.CoercivityRegular.mem_admKerBare hax hker)

/-- **The `ℝ`-carrier `Q₁` clause IS a proper restriction, and it DOES degenerate.** Both facts
reused from `AnchoredVFull` and bundled here so the contrast with `VReg` (which has no `ell`) is one
`#check` apart. -/
theorem kerQOne_proper_but_degenerates_at_one
    (hell : 2 ≤ 2) (hdvd0 : (2 : ℕ) ∣ (L 0 + 1)) :
    AdalyFormal.Balaban.AnchoredVFull.kerQOne L 2 ≠ ⊤ ∧
      AdalyFormal.Balaban.AnchoredVFull.kerQOne L 1 = ⊥ :=
  ⟨AdalyFormal.Balaban.AnchoredVFull.kerQOne_ne_top hell hdvd0,
    AdalyFormal.Balaban.AnchoredVFull.kerQOne_one_eq_bot⟩

#print axioms VReg_has_no_scale_parameter
#print axioms mem_VReg_of_clauses
#print axioms kerQOne_proper_but_degenerates_at_one

end RestoredSubspace

/-! ## §6 — CLAUSE 3 (NON-SCALARITY), AS FAR AS IT GOES

The `∀ U ∈ GaugeRegular α₀` form is NOT established (§4a). What IS established here is that the
faithful operator is non-scalar AT A BACKGROUND INSIDE THE REGULAR CLASS — the flat one, which is
`GaugeRegular 0` hence `GaugeRegular α₀` for every `α₀ ≥ 0`. The argument is the two-Rayleigh-quotient
criterion, with a genuine kernel vector on one side:

* `constDir`, the direction-`0` constant field, has IDENTICALLY ZERO flat curl at every plaquette on
  every lattice (`curl_trivialU_constDir`, new here and general in `L`), hence zero `Δ_k` form at the
  trivial background, while being nonzero;
* `deltaWitnessConfig` has `Δ_k` form `4` there (`deltaK_trivialU_deltaWitness_eq_four`, obtained by
  instantiating §2c's family formula at `X = 1`, a route independent of the tree's existing
  witnessL-only computation).

Two different quotients ⇒ not a multiple of the identity. -/

section NonScalar

open AdalyFormal.Balaban.CovariantOperators (RMap RMap_one suTwoWitness suTwoWitness_ne_zero
  curlValueCovariant)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm covPlaqInner)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.DeltaPrimeOperator (inner_deltaKCLMNormalized_eq)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.BondSU2Space (bondFnL2Equiv)

variable {L : PeriodicLatticeExtent}

/-- The direction-`0` constant field: `suTwoWitness` on every bond of direction `0`, `0` elsewhere.

**DISCLOSED DUPLICATION (LAW-19; flagged by this lane's nested validator, 2026-07-29).**
`FaithfulDeltaKNonScalar.constDirConfig` has the SAME body, specialised to `witnessL`. It is not
reused because that module's copy is `witnessL`-only while `curl_trivialU_constDir` below is proved
at GENERAL `L` — the generalisation is the new content, and the `witnessL` instance is recovered by
`constDir_eq_constDirConfig` (`rfl`), so the two objects are pinned to each other by kernel check
rather than by convention. -/
noncomputable def constDir (L : PeriodicLatticeExtent) :
    AdalyFormal.Balaban.AdmissibleSubspace.Bond L → SuTwo :=
  fun b => if b.2 = (0 : Fin 3) then suTwoWitness else 0

theorem constDir_ne_zero : constDir L ≠ 0 := by
  intro h
  have hb := congrFun h
    (AdalyFormal.Balaban.RegularUDomainWitnessGeneralU.siteZero L, (0 : Fin 3))
  rw [show constDir L
      (AdalyFormal.Balaban.RegularUDomainWitnessGeneralU.siteZero L, (0 : Fin 3))
      = suTwoWitness from if_pos rfl] at hb
  exact suTwoWitness_ne_zero hb

/-- **`constDir` IS FLAT-CURL-FREE, at every plaquette of every lattice.** The two direction indices
of a plaquette satisfy `μ < ν`, so `ν ≠ 0` unconditionally, which kills both `ν`-bonds; the two
`μ`-bonds carry the SAME value because the field does not depend on the site. -/
theorem curl_trivialU_constDir (p : PeriodicLatticePlaquette L) :
    curlValueCovariant (trivialU L) (constDir L) p = 0 := by
  have hν : p.2.1.2 ≠ (0 : Fin 3) := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) p.2.2)
  have e1 : constDir L (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0 := if_neg hν
  have e2 : constDir L (p.1, p.2.1.2) = 0 := if_neg hν
  have e3 : constDir L (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = constDir L (p.1, p.2.1.1) :=
    rfl
  have ht : ∀ b : AdalyFormal.Balaban.AdmissibleSubspace.Bond L,
      trivialU L b = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := fun _ => rfl
  show constDir L (p.1, p.2.1.1)
      + RMap (trivialU L (p.1, p.2.1.1))
          (constDir L (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
      - RMap (trivialU L (p.1, p.2.1.2))
          (constDir L (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
      - constDir L (p.1, p.2.1.2) = 0
  rw [e1, e2, e3, ht, ht, RMap_one]
  simp

theorem dstarD_trivialU_constDir : dstarDQuadForm (trivialU L) (constDir L) = 0 := by
  unfold AdalyFormal.Balaban.CovariantHj.dstarDQuadForm
  unfold AdalyFormal.Balaban.CovariantHj.covPlaqInner
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rw [curl_trivialU_constDir p, AdalyFormal.Balaban.CovariantHj.hsInner_zero_zero]

/-- The tree carries two definitionally-equal `trivialU`s (`DeltaPrime`'s and
`CovariantHjMinimizer`'s) that are not SYNTACTICALLY equal, so `rw` cannot find the pattern; the
`have` discharges the defeq by unification once, visibly — the same route
`CoercivityRegular.deltaPrimeQuadForm_trivialU_witL5` uses. -/
theorem deltaK_trivialU_constDir :
    deltaKQuadFormNormalizedCorrected (trivialU L) (constDir L) = 0 := by
  have h0 : AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadForm (trivialU L) (constDir L) = 0 :=
    AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadForm_vanishes_at_trivial (constDir L)
  rw [AdalyFormal.Balaban.CoercivityRegular.deltaKQuadFormNormalizedCorrected_eq_sub, h0,
    dstarD_trivialU_constDir]
  ring

/-- `singleBondU 1` IS the trivial background (both are constantly `1`). -/
theorem singleBondU_one_eq_trivialU :
    AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU 1 = trivialU witnessL := by
  funext b
  by_cases h : b = (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3))
  · rw [h, AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU_at_x_mu]; rfl
  · rw [AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU_elsewhere 1 h]; rfl

/-- **The second Rayleigh datum: the `Δ_k` form at the trivial background is `4` on
`deltaWitnessConfig`.** Instantiation of §2c's family formula at `X = 1` (`‖1 − 1‖²_F = 0`), which is
a route independent of the tree's existing direct witnessL computation. -/
theorem deltaK_trivialU_deltaWitness_eq_four :
    deltaKQuadFormNormalizedCorrected (trivialU witnessL)
      AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig = 4 := by
  rw [← singleBondU_one_eq_trivialU, singleBond_value_eq]
  norm_num [AdalyFormal.Balaban.RMapLipschitz.frobSq]

theorem toLp_constDir_ne_zero :
    (WithLp.toLp 2 (constDir L) : BondFnL2 L) ≠ 0 := by
  intro h
  have := congrArg (fun v : BondFnL2 L => (bondFnL2Equiv L) v) h
  simp only [map_zero, bondFnL2Equiv_toLp] at this
  exact constDir_ne_zero this

/-- **CLAUSE 3 HOLDS AT A BACKGROUND INSIDE THE REGULAR CLASS.** `trivialU` is `GaugeRegular 0`,
hence regular at every threshold; the faithful operator is NOT a scalar multiple of the identity
there, for any scalar and any rung. This is NOT the `∀ U` form clause 3 demands — see §4a. -/
theorem faithful_nonScalar_at_trivialU (k : ℕ) (c : ℝ) :
    regularDelta witnessL k (trivialU witnessL)
      ≠ c • ContinuousLinearMap.id ℝ (BondFnL2 witnessL) := by
  intro hc
  have hquad : ∀ A : AdalyFormal.Balaban.AdmissibleSubspace.Bond witnessL → SuTwo,
      deltaKQuadFormNormalizedCorrected (trivialU witnessL) A
        = c * ‖(WithLp.toLp 2 A : BondFnL2 witnessL)‖ ^ 2 := by
    intro A
    have h := congrArg (fun T : BondFnL2 witnessL →L[ℝ] BondFnL2 witnessL =>
      (inner ℝ (WithLp.toLp 2 A : BondFnL2 witnessL)
        (T (WithLp.toLp 2 A : BondFnL2 witnessL)) : ℝ)) hc
    simp only [smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_right] at h
    rw [regularDelta_apply, inner_deltaKCLMNormalized_eq] at h
    rw [h, real_inner_self_eq_norm_sq]
  have hc0 : c = 0 := by
    have h1 := hquad (constDir witnessL)
    rw [deltaK_trivialU_constDir] at h1
    have hn : ‖(WithLp.toLp 2 (constDir witnessL) : BondFnL2 witnessL)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr toLp_constDir_ne_zero
    have : ‖(WithLp.toLp 2 (constDir witnessL) : BondFnL2 witnessL)‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 hn
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h this
  have h2 := hquad AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig
  rw [deltaK_trivialU_deltaWitness_eq_four, hc0, zero_mul] at h2
  norm_num at h2

/-- `trivialU` is inside the regular class at the operative threshold — so the theorem above is
about a background the restated target actually quantifies over. Reused. -/
theorem trivialU_is_regular : GaugeRegular normAlpha (trivialU L) :=
  gaugeRegular_of_frobSupBond_le (by
    rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU L]
    exact le_of_lt normAlpha_pos)

#print axioms constDir
#print axioms constDir_ne_zero
#print axioms curl_trivialU_constDir
#print axioms dstarD_trivialU_constDir
#print axioms deltaK_trivialU_constDir
#print axioms singleBondU_one_eq_trivialU
#print axioms deltaK_trivialU_deltaWitness_eq_four
#print axioms toLp_constDir_ne_zero
#print axioms faithful_nonScalar_at_trivialU
#print axioms trivialU_is_regular

end NonScalar

/-! ## §7 — THE BRIDGE `GaugeRegular ⟹ IsRegularHolonomy`, AND CLAUSE 2 ON THE SPIKE FAMILY

Two things the tree did not have, both consequences of §2c's identity `‖X − 1‖²_F = defectOfElem X`:

1. the gauge-INVARIANT hypothesis `GaugeRegular α₀` implies the tree's OTHER regularity predicate
   `RegularityHolonomy.IsRegularHolonomy U (32α₀²)`. Until now these two lived side by side with no
   arrow between them, and results were stated against one or the other with no way to transfer;
2. clause 2 (global PSD) HOLDS on the whole single-active-bond FIELD family — every bond, every
   regular background — under an explicit smallness condition. This is strictly more than §2c, which
   covered one field at one bond over the background family.

The smallness condition shipped below is `card(plaquettes)·8α₀² ≤ 1`, i.e. it degrades with the
VOLUME. That is an artefact of the crude bound (the sum is taken over ALL plaquettes although at
most the ones touching `b₀` contribute — `CoercivityRegular.spike_deltaPrimeFirstTerm_of_not_touches`
gives `0` off them), NOT of the statement. The improvement is exactly a cardinality bound on
`Finset.univ.filter (Touches b₀ ·)`, which in three dimensions is `≤ 4`; that count is not in the
tree and is not proved here. Disclosed so nobody reads the volume factor as a finding. -/

section HolonomyBridge

open AdalyFormal.Balaban.CoercivityRegular (spikeWitness Touches spike_deltaPrimeSecondTerm_eq_zero
  spike_deltaPrimeFirstTerm_of_touches spike_deltaPrimeFirstTerm_of_not_touches
  norm_spike_curl_of_touches deltaKQuadFormNormalizedCorrected_eq_sub)
open AdalyFormal.Balaban.NonFlatBackground (defectOfElem defectOfElem_nonneg
  holonomyDefectSq_eq_defectOfElem)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem deltaPrimeQuadForm deltaPrimePlaqTerm)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm)
open AdalyFormal.Balaban.CovariantOperators (suTwoWitness curlValueCovariant)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)

variable {L : PeriodicLatticeExtent}

/-- **`GaugeRegular α₀` BOUNDS THE HOLONOMY DEFECT BY `32α₀²`.** -/
theorem defectOfElem_holonomy_le_of_gaugeRegular {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (U : Cfg L)
    (hreg : GaugeRegular α₀ U) (p : PeriodicLatticePlaquette L) :
    defectOfElem (holonomyElem U p) ≤ 32 * α₀ ^ 2 := by
  have h := AdalyFormal.Balaban.LemmaAssembly.frobSq_holonomy_of_gaugeRegular hα₀ U hreg p
  rwa [frobSq_sub_one_eq_defect] at h

/-- **THE MISSING ARROW between the tree's two regularity predicates.** -/
theorem isRegularHolonomy_of_gaugeRegular {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (U : Cfg L)
    (hreg : GaugeRegular α₀ U) :
    AdalyFormal.Balaban.RegularityHolonomy.IsRegularHolonomy U (32 * α₀ ^ 2) := by
  intro p
  rw [holonomyDefectSq_eq_defectOfElem]
  exact defectOfElem_holonomy_le_of_gaugeRegular hα₀ U hreg p

/-- **MUST-FIRE control on the bridge.** At the operative numeral the induced holonomy threshold is
`32·(5·10⁻⁷)² = 8·10⁻¹²`, and `centralHolonomyU` attains defect `8` at `witnessPlaquette`, so the
bridge's conclusion is genuinely violated there. Together with `gaugeRegular_normAlpha_excludes_central`
this shows the arrow is not carrying a vacuous conclusion. -/
theorem bridge_threshold_at_normAlpha : 32 * normAlpha ^ 2 = 8 / 1000000000000 := by
  rw [show normAlpha = 1 / 2000000 from rfl]
  norm_num

/-- The per-plaquette `Δ′` summand at a spike field is bounded by half the holonomy defect,
uniformly in the plaquette (both the touching and the non-touching case). -/
theorem spike_deltaPrimePlaqTerm_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (U : Cfg L)
    (hreg : GaugeRegular α₀ U) (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) (p : PeriodicLatticePlaquette L) :
    deltaPrimePlaqTerm U (spikeWitness b₀) p ≤ 16 * α₀ ^ 2 := by
  unfold AdalyFormal.Balaban.DeltaPrime.deltaPrimePlaqTerm
  rw [spike_deltaPrimeSecondTerm_eq_zero U b₀ hnd p, add_zero]
  by_cases h : Touches b₀ p
  · rw [spike_deltaPrimeFirstTerm_of_touches U b₀ hnd p h]
    have := defectOfElem_holonomy_le_of_gaugeRegular hα₀ U hreg p
    linarith
  · rw [spike_deltaPrimeFirstTerm_of_not_touches U b₀ p h]
    positivity

/-- **`Δ′` AT A SPIKE FIELD IS SMALL ON THE REGULAR CLASS.** -/
theorem spike_deltaPrimeQuadForm_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (U : Cfg L)
    (hreg : GaugeRegular α₀ U) (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) :
    deltaPrimeQuadForm U (spikeWitness b₀)
      ≤ (Fintype.card (PeriodicLatticePlaquette L) : ℝ) * (16 * α₀ ^ 2) := by
  unfold AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadForm
  calc ∑ p : PeriodicLatticePlaquette L, deltaPrimePlaqTerm U (spikeWitness b₀) p
      ≤ ∑ _p : PeriodicLatticePlaquette L, (16 * α₀ ^ 2) :=
        Finset.sum_le_sum (fun p _ => spike_deltaPrimePlaqTerm_le hα₀ U hreg b₀ hnd p)
    _ = (Fintype.card (PeriodicLatticePlaquette L) : ℝ) * (16 * α₀ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **`D^*D` AT A SPIKE FIELD IS AT LEAST `1`** whenever some plaquette's boundary contains the
bond — `‖suTwoWitness‖² = 1` and every other summand is nonnegative. -/
theorem spike_dstarDQuadForm_ge_one (U : Cfg L)
    (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) (hnd : ∀ μ : Fin 3, 0 < L μ)
    (p₀ : PeriodicLatticePlaquette L) (h : Touches b₀ p₀) :
    (1 : ℝ) ≤ dstarDQuadForm U (spikeWitness b₀) := by
  rw [AdalyFormal.Balaban.LemmaAssembly.dstarDQuadForm_eq_sum_norm_sq]
  have hterm : ‖curlValueCovariant U (spikeWitness b₀) p₀‖ ^ 2 = 1 := by
    rw [norm_spike_curl_of_touches U b₀ hnd p₀ h,
      ← AdalyFormal.Balaban.LemmaAssembly.hsInner_self_eq_norm_sq,
      AdalyFormal.Balaban.CovariantHj.hsInner_suTwoWitness_self]
  rw [← hterm]
  exact Finset.single_le_sum (f := fun p : PeriodicLatticePlaquette L =>
    ‖curlValueCovariant U (spikeWitness b₀) p‖ ^ 2)
    (fun q _ => sq_nonneg _) (Finset.mem_univ p₀)

/-- **CLAUSE 2 ON THE WHOLE SPIKE FAMILY.** For every bond, every background in the regular class,
and every lattice small enough relative to the threshold, the faithful `Δ_k` form is NONNEGATIVE.
Strictly more than §2c (one field, one bond, the background family); still NOT clause 2, which
quantifies over every vector. -/
theorem spike_psd_of_gaugeRegular {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (U : Cfg L)
    (hreg : GaugeRegular α₀ U) (b₀ : AdalyFormal.Balaban.AdmissibleSubspace.Bond L)
    (hnd : ∀ μ : Fin 3, 0 < L μ) (p₀ : PeriodicLatticePlaquette L) (h : Touches b₀ p₀)
    (hsmall : (Fintype.card (PeriodicLatticePlaquette L) : ℝ) * (8 * α₀ ^ 2) ≤ 1) :
    0 ≤ deltaKQuadFormNormalizedCorrected U (spikeWitness b₀) := by
  rw [deltaKQuadFormNormalizedCorrected_eq_sub]
  have h1 := spike_dstarDQuadForm_ge_one U b₀ hnd p₀ h
  have h2 := spike_deltaPrimeQuadForm_le hα₀ U hreg b₀ hnd
  linarith

#print axioms defectOfElem_holonomy_le_of_gaugeRegular
#print axioms isRegularHolonomy_of_gaugeRegular
#print axioms bridge_threshold_at_normAlpha
#print axioms spike_deltaPrimePlaqTerm_le
#print axioms spike_deltaPrimeQuadForm_le
#print axioms spike_dstarDQuadForm_ge_one
#print axioms spike_psd_of_gaugeRegular

end HolonomyBridge

end AdalyFormal.Balaban.CoercUMainRegular
