/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.FaithfulMinimality
import AdalyFormal.Balaban.ThirdLevelWitness
import AdalyFormal.Balaban.NormalizationAudit
import AdalyFormal.Balaban.RegularUGamma0
import AdalyFormal.Balaban.MinSwap

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `Δ_k` WITH A UNIT-LEVEL ARGUMENT — the fine level genuinely integrated out

## What this module is

### INVENTORY — CORRECTED after two de-correlated prosecutions

~~"Every `Δ`-shaped quadratic form in this tree takes a **fine** bond field."~~
**STRUCK: FALSE AS STATED.** Both prosecution passes convicted this sentence, and a shape query
(`compute/duplicate_census/concept_index.py --root formal/AdalyFormal/AdalyFormal
--like CoarseBond`, filtered to `RESULT(Real)`) found one further object that neither pass
named. Retained struck so the overclaim is on the record. The accurate inventory, in three groups:

*(a) Fine-argument `Δ`-shaped forms — the original list, correct as far as it goes:*

* `CovariantHjFaithful.deltaJQuadFormCovFaithful ell levels U A0` — `A0 : Bond L → SuTwo`;
* `CStarLevelCorrected.deltaKCorr S levels U B` — `B : Bond L → SuTwo` (the `LevelSplit` separates
  the two BLOCK SIDES, but the argument type stays fine);
* `NormalizationAudit.deltaKQuadFormNormalizedCorrected U A` — `A : Bond L → SuTwo`.

*(b) `Δ`-shaped forms over a GENERIC carrier, omitted by the struck claim:*

* `DeltaKAssembly.deltaKForm D bc Qext J B : ℝ` with `B : K`, an abstract inner-product carrier —
  and it is the one object in the tree that carries CMP99b (3.156)'s `−2⟪H₁D̃⁽²⁾B, J⟫` term;
* `DeltaKRecursive.deltaKQuadForm F k B : ℝ` with `B : H`, likewise abstract, and `k`-indexed.

Neither takes a fine bond field; both were missed because the original inventory was a grep over
`Bond L → SuTwo` and a generic carrier does not match that string.

*(c) Real-valued forms that ALREADY take a `CoarseBond L ell → SuTwo`, omitted by the struck claim:*

* `RegularUGamma0.coarseCurlEnergySuTwo hdvd B` — the coarse-curl `L²` energy at the flat coarse
  background (found by the Claude pass);
* `CoarseCurlCovariant.coarseCurlEnergyCov hdvd V B` — the same at a coarse background `V`
  (found by the shape query only; neither prosecution named it);
* `CovariantHjFaithful.covCoarseBondInner B B` — the coarse `L²` inner product on the diagonal.

*(d) THE ABSTRACT FIBRE-INFIMUM PATTERN ITSELF, which already exists in this tree:*

* `MinSwap.fibre S Q B := {A | A ∈ S ∧ Q A = B}` and
  `MinSwap.schur q S Q B := sInf (q '' MinSwap.fibre S Q B)`, generic over the carriers, carrying
  the same `sInf ∅ = 0` hazard note this module carries.
  **Neither prosecution pass named this and neither did the original inventory**; it was found by a
  shape query over result type `ℝ` with an abstract-carrier final argument, i.e. by a search that
  could not match this module's own vocabulary (§READ-FIRST rule 6).

**Consequence, stated plainly: NEITHER the argument type NOR the construction pattern is new here.**
~~"Its argument type is `CoarseBond L ell → SuTwo`. That is the whole point."~~ **STRUCK** — three
objects in group (c) already have that argument type, and group (d) already has the fibre-infimum
construction in the abstract. `deltaKUnit_eq_minSwap_schur` (§2) proves the identification
outright: `deltaKUnit` IS `MinSwap.schur` instantiated at `q =` the covariant curl energy,
`S =` the gauge-fixed fine fields, `Q = Q_ell^{cov}`.

**What this module actually supplies** is therefore neither the type nor the pattern but the
CONCRETE COVARIANT INSTANTIATION and the theorems that only exist at that instantiation: the coset
structure of the fibre, the factoring `Δ_J = deltaKUnit ∘ Q_ell` (`deltaKUnit_factors_through_Q`),
the Pythagoras comparison with the collapsed p.392 form, and the concrete non-vacuity and strictness
witnesses. The abstract template can state none of those, and the objects in group (c) — all direct
coarse-lattice expressions with no fine level in them at all — are not this object.

### What it is FOR

CMP99b (3.156) prints `⟨B, Δ_k B⟩` with `B` the **unit-lattice** field on both sides, `Δ_k` the
Schur complement over the fibre `{A : QA = B}` — so its argument is a unit-level object and the
fine level is already integrated out. `CStarLevelCorrected.lean` says so in its own words, verbatim:

> "The final repair is a genuine third level — a finer bond space with `Q : finer → Bond L`,
> `Δ_k`'s Schur fibre taken there, and `C`'s constraint left where it is, on `Bond L`. That
> construction is NOT built here."

**This module supplies a fibre-minimised unit-argument form of exactly that shape** — and nothing
more. With `Bond L → SuTwo` in the role of the finer bond space and
`Q_ell = lineCoarseRestrictCovLM U ell : (Bond L → SuTwo) → (CoarseBond L ell → SuTwo)` in the role
of `Q`, the form

  `deltaKUnit ell levels U : (CoarseBond L ell → SuTwo) → ℝ`

is the infimum of the fine curl energy over the faithful fibre above a **unit-level** field.
It is NOT CMP99b (3.156)'s operator: the `J` term is absent, the printed three-clause domain on `B`
is absent, and there is no `k`-indexed family. See "What is NOT claimed" immediately below — that
list is the operative scope, and the sentence above must be read against it.

## What is NOT claimed (read before quoting)

* **This does NOT close the denotation-dictionary row `delta_k_unit_p428_3156`.** Whether this
  object is the one CMP99b means is an adjudication against the source pages, not a build; the
  `MISMATCH` verdict stands until prosecuted.
* **No RG ladder.** `k`-indexing is a separate axis and nothing here produces a `Δ_k` tower. The
  standing NO-RG-LADDER finding is untouched.
* **No `Q_j` composite** is used: the module is parametric in the block side `ell`.
* **`J = 0`** — the `−2⟨H₁D̃⁽²⁾(B),J⟩` term of (3.156) is absent, the same standing residual as
  `DeltaKSuTwoAssembly` §3.
* **No coercivity.** The witnesses below are non-vacuity anchors, not bounds.

## What IS proved

1. **§1** `unitFibre` and its COSET structure: above a unit-level `B` the fibre is exactly an affine
   translate of `gaugeConstraintSubspaceCovFaithful` (`unitFibre_eq_coset`). "The fine data that is
   integrated out" is precisely `V`, as a theorem.
2. **§2** `deltaKUnit`, the unit-level form, together with
   `deltaKUnit_factors_through_Q` — the fine-level `Δ_J` FACTORS through `Q_ell`, which is the exact
   content of "the fine level is integrated out". Well-definedness on unit data is inherited from
   `FaithfulMinimality.deltaJ_isLeast_fibreEnergies` (NOT re-proved — LAW-19).
3. **§3** the DOMAIN: `liftableUnitFields`, a submodule of unit-level fields, and a NAMED lift
   `unitLift` (no existential is registered: the witness is a construction, not an `∃`).
   The empty-fibre hazard is made LOUD by `deltaKUnit_eq_zero_of_no_lift`.
3b. **§3c** the word "FORM" is EARNED, not asserted: `deltaKUnit_zero_eq_zero` (unconditional),
   `deltaKUnit_smul` (the quadratic scaling law `Q(cB) = c²Q(B)`), `deltaKUnit_parallelogram`
   (the parallelogram law on `liftableUnitFields`), `deltaKUnitPolar` + `deltaKUnitPolar_diag`
   (the polarization identity reproduces the form on the diagonal), bundled as
   `deltaKUnit_is_quadratic_form`.
3c. **§3d** the `ell = 0` COLLAPSE, proved: `deltaKUnit_ell0_eq_zero` — at block side `0` the form
   is IDENTICALLY ZERO on every unit-level field, for every `levels` and every `U`, because
   `Q_0 ≡ 0`. `coarseWitness0_ne_zero` shows this is a genuine collapse of the operator, not an
   empty-type artefact. See "Degenerate block sides" below.
3d. **§3e** the `levels`-MONOTONICITY of the infimum, with the nonemptiness hypothesis EXPLICIT:
   `deltaKUnit_oneLevelUniv_le_of_lift`, `deltaKUnit_pos_of_pos_oneLevelUniv`, and the dichotomy
   `deltaKUnit_pos_or_unitFibre_empty`. This replaces a prose argument that was invalid as written.
3e. **§7b** that hypothesis DISCHARGED at a concrete field:
   `NilLevelTarget.loopField` is divergence-free at the trivial background, so it lies in the fibre
   for EVERY `levels` (`loopField_mem_unitFibre`) and the unit-level form is strictly positive there
   at every `levels`, live `R` included (`deltaKUnit_loopField_pos_at_every_levels`).
4. **§4** NON-VACUITY at a NON-DEGENERATE level: on `witL7`, `ell = 2`, `U = 1`, the unit-level
   field `B7unit = Q₂ B7` is NONZERO, has a lift, and `0 < deltaKUnit … B7unit`. Its fibre contains
   TWO DISTINCT fine lifts with the SAME value — the integration-out is not over a point.
5. **§5** the fine level CARRIES ENERGY THAT IS STRICTLY REMOVED: `B7'` lies in the fibre above the
   ZERO unit field, `deltaKUnit … 0 = 0` (now a special case of the UNCONDITIONAL
   `deltaKUnit_zero_eq_zero` of §3c, which holds at every `ell`, `levels` and `U`), and
   `0 < dstarDQuadForm (trivialU witL7) B7'`. So the minimisation is not a no-op at `ell = 2`.
6. **§6** COMPARISON WITH THE COLLAPSED FORM, exactly: the fine curl energy splits as
   `dstarDQuadForm U A0 = deltaKUnit ell levels U (Q_ell A0) + (Schur defect)` (Pythagoras), the
   collapsed normalized form adds one further named term, at `ell = 1` the unit form collapses back
   onto `dstarDQuadForm` EXACTLY (so the level distinction is INVISIBLE at `ell = 1`), and §5
   exhibits a field where the Schur defect is STRICTLY positive at `ell = 2`.
7. **§6b** THE TWO FORMS GENUINELY DIFFER, and NEITHER DOMINATES THE OTHER — two kernel-checked
   strict inequalities pointing in OPPOSITE directions (`no_ordering_between_collapsed_and_unit`).

## THE ORDERING, stated correctly (this replaces a false word)

~~"`deltaKQuadFormNormalizedCorrected` … exceeds the unit-level form by TWO named terms."~~
**STRUCK: "exceeds" is FALSE**, and the two displayed terms are NOT a nonnegative distance.
`collapsed_eq_deltaKUnit_add_two_terms` is an EQUALITY with a signed remainder:

  `collapsed = deltaKUnit + ⟪P,P⟫ + Δ′`,  with `⟪P,P⟫ ≥ 0` but **`Δ′` of INDEFINITE SIGN**.

Both orderings actually occur, and both are theorems in §6b:

* `deltaKUnit_lt_collapsed_at_B7'` — `ell = 2`, `witL7`, `U = trivialU`, `A0 = B7'`:
  `deltaKUnit = 0 < collapsed` (there `Δ′ = 0` and the Schur defect carries everything);
* `collapsed_lt_deltaKUnit_at_deltaWitness` — `ell = 1`, `witnessL`, `U = witnessU`,
  `A0 = deltaWitnessConfig`: `collapsed = 0 < 4 = deltaKUnit`. Here `Δ′` is NEGATIVE and cancels
  the whole of `dstarDQuadForm`.

So the identity is a DECOMPOSITION, not a gap in either direction, and no consumer may read it as
one. (The `-4`-vs-`0` normalization history behind the second witness is `NormalizationAudit`'s.)

## Honest scope

* Everything is the FAITHFUL covariant `Q` (`lineCoarseRestrictCovLM`, CMP95 (1.18) / CMP98 (125)),
  whose "true block average" reading holds on COMPATIBLE full blocks; the algebraic content below
  (coset structure, factoring, Pythagoras) is linear-algebraic and holds for all `ell`, and the
  concrete witnesses live on `witL7`, where `2 ∣ 8` and `4 ∣ 8` both hold.
* **DEGENERATE BLOCK SIDES — BOTH of them, and both proved, not narrated.** The general identities
  carry no `0 < ell` hypothesis, so they admit two block sides on which they say nothing:
  * `ell = 0`: `Q_0 ≡ 0` (`MinSwap.lineCoarseRestrictCovLM_ell_zero`) while `CoarseBond L 0` is
    NONEMPTY, so every fine field has zero unit shadow and `deltaKUnit 0 levels U B = 0` for EVERY
    `B`, `levels`, `U` (`deltaKUnit_ell0_eq_zero`). The headline identity then holds for arbitrary
    `A0` and `U` with its unit term identically `0` — `collapsed_ell0_carries_no_unit_content`
    states exactly that, so the vacuity is a theorem and cannot be met by surprise. This was
    UNDISCLOSED in the first version of this module and is the reason for this paragraph.
  * `ell = 1`: `Q_1` is the identity/reindexing, `V = ⊥`, and `deltaKUnit` collapses onto
    `dstarDQuadForm` (`deltaKUnit_ell1_eq_dstarD`).
  Every non-degenerate witness in §4/§5/§5b is therefore at `ell = 2`.
* `levels = oneLevelUniv` at the witnesses makes the `R`-clause vacuous
  (`RcovLM_oneLevelUniv_eq_zero`).
  ~~"with a live `R` the fibre is smaller and the infimum only rises, so §4's positivity persists"~~
  **STRUCK: INVALID AS STATED.** Subset-monotonicity of `sInf` needs the SMALLER set to be
  nonempty, and `sInf ∅ = 0` in `ℝ` — the exact hazard this module proves in
  `deltaKUnit_eq_zero_of_no_lift`. Without nonemptiness the infimum can DROP to `0`, i.e.
  positivity can be DESTROYED rather than preserved. §3e now proves the repaired statements:
  `deltaKUnit_oneLevelUniv_le_of_lift` (monotonicity, with a lift supplied),
  `deltaKUnit_pos_of_pos_oneLevelUniv` (positivity persists, same hypothesis), and
  `deltaKUnit_pos_or_unitFibre_empty` (the dichotomy: persists, or the fibre is empty and the
  value is the `sInf ∅` artefact).
  **§7b then DISCHARGES the hypothesis at a concrete field:** `NilLevelTarget.loopField m` is
  divergence-free at the trivial background, so by linearity `R` annihilates its gauge term for
  EVERY `levels`, and `deltaKUnit_loopField_pos_at_every_levels` gives strict positivity of the
  unit-level form at every `levels` — live `R` included. What is STILL not known is §4's own
  witness: that positivity is at `ell = 1`, the degenerate block side, and nothing shows `B7` has a
  divergence-free representative, so `0 < deltaKUnit 2 levels (trivialU witL7) B7unit` at a live
  `levels` remains unsettled. `deltaKUnit_loopField_pos_of_oneLevelUniv_pos` reduces the `ell ≥ 2`
  question for the LOOP to one `oneLevelUniv` fact.
  ~~"§5's `= 0` half is `oneLevelUniv`-scoped."~~ **STRUCK, SUPERSEDED AND STRENGTHENED:**
  `deltaKUnit_zero_eq_zero` proves `deltaKUnit ell levels U 0 = 0` for EVERY `ell`, `levels` and
  `U` unconditionally, so `deltaKUnit_zero_witL7` is now a special case and that half of §5 is not
  `oneLevelUniv`-scoped at all.
* `U = trivialU` at the witnesses. §1, §2, §3, §3c, §3d, §3e and §6 are general in `U`.
-/

namespace AdalyFormal.Balaban.DeltaKUnitLevel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU oneLevelUniv RcovLM
  RcovLM_oneLevelUniv_eq_zero deltaKernelImageCovH gradCovariantAdjointLM covPlaqInner_add_left
  covPlaqInner_add_right covPlaqInner_sub_right plaqFnEquiv)
open AdalyFormal.Balaban.MinSwap (lineCoarseRestrictCovLM_ell_zero const_coarse_ne_zero)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected
  deltaPrimeQuadFormNormalizedTransported
  deltaPrimeQuadFormNormalizedTransported_eq_half_transported
  deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero
  dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four)
open AdalyFormal.Balaban.DeltaPrime (deltaWitnessConfig deltaPrimeQuadFormTransported
  deltaPrimeQuadFormTransported_vanishes_at_trivial)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.CStarLevelCorrected (LevelSplit deltaKCorr covPlaqInner_zero_right
  covPlaqInner_self_pos_of_ne)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo stokesU stokesPhi stokesPhi_apply
  stokes_factoring hsInner_smul_right)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.ThirdLevelWitness (dipole dipole_apply_plus coarseCurlSuTwo_apply
  witL7 witL7_two_dvd hlt01 hsInner_witness_pos split24 B7 B7' s7Z s7P s7M y70
  Q_dipole_apply_dir Q_dipole_apply_offdir one_ne_zero_fin3 B7'_kerQ2 B7'_ne_zero pathSiteBack
  B7_not_kerQ2 third_level_positivity)
open AdalyFormal.Balaban.FaithfulMinimality (fibreEnergies deltaJ_isLeast_fibreEnergies
  deltaJ_eq_of_same_fibre)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE UNIT-LEVEL FIBRE, and its coset structure

`unitFibre ell levels U B` is the set of FINE fields lying above the UNIT-level field `B`, subject
to the same two clauses that define `gaugeConstraintSubspaceCovFaithful`: the faithful covariant
block average `Q_ell` hits `B`, and the `R∂*_U` gauge clause holds.

The coset theorem is the precise sense in which "the fine level is integrated out": the fine data
invisible to `B` is EXACTLY the subspace `V = gaugeConstraintSubspaceCovFaithful`. -/

/-- **The faithful fibre above a UNIT-level field `B`.** Note the type of `B`:
`CoarseBond L ell → SuTwo`, not `Bond L → SuTwo`. -/
def unitFibre (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L ell → SuTwo) : Set (Bond L → SuTwo) :=
  {A | lineCoarseRestrictCovLM U ell A = B ∧
    RcovLM U levels (gradCovariantAdjointLM U A) = 0}

theorem mem_unitFibre {ell : ℕ} {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {B : CoarseBond L ell → SuTwo} {A : Bond L → SuTwo} :
    A ∈ unitFibre ell levels U B ↔
      lineCoarseRestrictCovLM U ell A = B ∧
        RcovLM U levels (gradCovariantAdjointLM U A) = 0 := Iff.rfl

#print axioms mem_unitFibre

/-- The difference of two fine lifts of the SAME unit-level field lies in `V`. -/
theorem sub_mem_V_of_mem_unitFibre {ell : ℕ} {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} {A0 A1 : Bond L → SuTwo}
    (h0 : A0 ∈ unitFibre ell levels U B) (h1 : A1 ∈ unitFibre ell levels U B) :
    A1 - A0 ∈ gaugeConstraintSubspaceCovFaithful ell levels U := by
  rw [mem_gaugeConstraintSubspaceCovFaithful]
  exact ⟨by rw [map_sub, h1.1, h0.1, sub_self],
    by rw [map_sub, map_sub, h1.2, h0.2, sub_self]⟩

/-- Translating a fine lift by an element of `V` stays in the same fibre. -/
theorem add_mem_unitFibre_of_mem_V {ell : ℕ} {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} {A0 v : Bond L → SuTwo}
    (h0 : A0 ∈ unitFibre ell levels U B)
    (hv : v ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    A0 + v ∈ unitFibre ell levels U B := by
  obtain ⟨hv1, hv2⟩ := mem_gaugeConstraintSubspaceCovFaithful.mp hv
  exact ⟨by rw [map_add, hv1, add_zero, h0.1], by rw [map_add, map_add, hv2, add_zero, h0.2]⟩

/-- **THE COSET CHARACTERIZATION.** Given ONE fine lift `A0`, a fine field lies above `B` exactly
when it differs from `A0` by an element of `V`. -/
theorem mem_unitFibre_iff_sub_mem_V {ell : ℕ} {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} {A0 A : Bond L → SuTwo}
    (h0 : A0 ∈ unitFibre ell levels U B) :
    A ∈ unitFibre ell levels U B ↔
      A - A0 ∈ gaugeConstraintSubspaceCovFaithful ell levels U := by
  constructor
  · intro hA
    exact sub_mem_V_of_mem_unitFibre h0 hA
  · intro hA
    have hmem := add_mem_unitFibre_of_mem_V h0 hA
    have hEq : A0 + (A - A0) = A := by abel
    rwa [hEq] at hmem

/-- **THE COSET THEOREM.** The fibre above `B` is exactly `A0 + V`. So the fine information that the
unit-level field `B` does not see is precisely `gaugeConstraintSubspaceCovFaithful ell levels U`,
and nothing else. -/
theorem unitFibre_eq_coset {ell : ℕ} {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} {A0 : Bond L → SuTwo}
    (h0 : A0 ∈ unitFibre ell levels U B) :
    unitFibre ell levels U B =
      {A : Bond L → SuTwo | A - A0 ∈ gaugeConstraintSubspaceCovFaithful ell levels U} :=
  Set.ext fun _ => by
    rw [Set.mem_setOf_eq]
    exact mem_unitFibre_iff_sub_mem_V h0

#print axioms sub_mem_V_of_mem_unitFibre
#print axioms add_mem_unitFibre_of_mem_V
#print axioms mem_unitFibre_iff_sub_mem_V
#print axioms unitFibre_eq_coset

/-- `fibreEnergies` is exactly the image of the fibre under the fine curl energy — the bridge
between `FaithfulMinimality`'s set of reals and §1's set of fields. -/
theorem fibreEnergies_eq_image (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L ell → SuTwo) :
    fibreEnergies ell levels U B =
      (fun A => covPlaqInner (curlCovariantLM U A) (curlCovariantLM U A)) ''
        unitFibre ell levels U B := by
  ext r
  constructor
  · rintro ⟨A, h1, h2, rfl⟩
    exact ⟨A, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨A, ⟨h1, h2⟩, rfl⟩
    exact ⟨A, h1, h2, rfl⟩

#print axioms fibreEnergies_eq_image

/-! ## §2 — `deltaKUnit`: THE FORM WHOSE ARGUMENT IS A UNIT-LEVEL FIELD

The definition is the infimum of the fine curl energy over the fibre. `FaithfulMinimality` already
proves the infimum is ATTAINED (`deltaJ_isLeast_fibreEnergies`) and independent of the lift
(`deltaJ_eq_of_same_fibre`); neither is re-proved here (LAW-19). What is new is the OBJECT: a real
number attached to a `CoarseBond L ell → SuTwo`. -/

/-- **`⟨B, Δ_k B⟩` WITH `B` A UNIT-LEVEL FIELD.** The infimum of the fine curl energy
`‖D_U A‖²` over the faithful fibre `{A : Q_ell A = B, R∂*_U A = 0}`.

The argument type is `CoarseBond L ell → SuTwo`: the fine level is integrated out by the infimum,
not carried. Compare `deltaJQuadFormCovFaithful`, `deltaKCorr` and
`deltaKQuadFormNormalizedCorrected`, all of which take a `Bond L → SuTwo`.

**Hazard, made loud in `deltaKUnit_eq_zero_of_no_lift`:** `sInf ∅ = 0` in `ℝ`, so on a unit-level
field with NO fine lift this returns `0`. Every substantive statement below is therefore guarded by
an explicit lift (`unitFibre` membership) or by `liftableUnitFields` membership. -/
noncomputable def deltaKUnit (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L ell → SuTwo) : ℝ :=
  sInf (fibreEnergies ell levels U B)

/-- **WELL-DEFINEDNESS ON UNIT DATA.** The value equals `Δ_J` at ANY fine lift — so two fine lifts
of the same unit-level field give the same number, and the number is a function of `B` alone. -/
theorem deltaKUnit_eq_deltaJ_of_mem {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (B : CoarseBond L ell → SuTwo)
    (h0 : A0 ∈ unitFibre ell levels U B) :
    deltaKUnit ell levels U B = deltaJQuadFormCovFaithful ell levels U A0 :=
  (deltaJ_isLeast_fibreEnergies levels U A0 B h0.1 h0.2).csInf_eq

/-- The value is ATTAINED and is a lower bound: `IsLeast`, at the unit level. -/
theorem deltaKUnit_isLeast {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (B : CoarseBond L ell → SuTwo)
    (h0 : A0 ∈ unitFibre ell levels U B) :
    IsLeast (fibreEnergies ell levels U B) (deltaKUnit ell levels U B) := by
  rw [deltaKUnit_eq_deltaJ_of_mem levels U A0 B h0]
  exact deltaJ_isLeast_fibreEnergies levels U A0 B h0.1 h0.2

/-- **THE FACTORIZATION — the exact content of "the fine level is integrated out".** For a
gauge-fixed fine field `A0`, the FINE-level form `Δ_J(A0)` equals the UNIT-level form evaluated at
`A0`'s block average. So `Δ_J` factors through `Q_ell`: it depends on `A0` only through
`Q_ell A0`. -/
theorem deltaKUnit_factors_through_Q {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    deltaKUnit ell levels U (lineCoarseRestrictCovLM U ell A0)
      = deltaJQuadFormCovFaithful ell levels U A0 :=
  deltaKUnit_eq_deltaJ_of_mem levels U A0 _ ⟨rfl, h2⟩

/-- The unit-level form is a lower bound for the fine curl energy at EVERY lift. -/
theorem deltaKUnit_le_fine_energy {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 A1 : Bond L → SuTwo) (B : CoarseBond L ell → SuTwo)
    (h0 : A0 ∈ unitFibre ell levels U B) (h1 : A1 ∈ unitFibre ell levels U B) :
    deltaKUnit ell levels U B ≤ covPlaqInner (curlCovariantLM U A1) (curlCovariantLM U A1) :=
  (deltaKUnit_isLeast levels U A0 B h0).2 ⟨A1, h1.1, h1.2, rfl⟩

theorem deltaKUnit_nonneg {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (B : CoarseBond L ell → SuTwo)
    (h0 : A0 ∈ unitFibre ell levels U B) :
    0 ≤ deltaKUnit ell levels U B := by
  rw [deltaKUnit_eq_deltaJ_of_mem levels U A0 B h0]
  exact deltaJQuadFormCovFaithful_nonneg ell levels U A0

/-- **`deltaKUnit` IS `MinSwap.schur` AT THE COVARIANT DATA.** The ABSTRACT "infimum of the fine
energy over the fibre" already exists in this tree, generic over the carriers:
`MinSwap.schur q S Q B := sInf (q '' MinSwap.fibre S Q B)`, together with
`MinSwap.fibre S Q B := {A | A ∈ S ∧ Q A = B}` and the same `sInf ∅ = 0` hazard note. Neither
prosecution pass named it and neither did this module's original inventory; a shape query over
result type `ℝ` with an abstract-carrier final argument found it.

This theorem is the exact bridge. `deltaKUnit` is therefore NOT a new construction pattern — it is
the INSTANTIATION of the existing pattern at `q =` the covariant curl energy, `S =` the gauge-fixed
fine fields, `Q = Q_ell^{cov}`. What this module supplies over `MinSwap` is the concrete covariant
data and the theorems that need it (coset structure, factoring through `Q_ell`, the Pythagoras
comparison, the concrete witnesses) — none of which the abstract template can state.

Consumers may now transport `MinSwap`'s general Schur lemmas onto `deltaKUnit` through this
equation. `fibreEnergies_bddBelow` (§3e) duplicates, on the `fibreEnergies` spelling,
`MinSwap.bddBelow_image_of_nonneg`, which says the same thing on the `q '' fibre` spelling; the two
are connected by this bridge, and the duplication is disclosed rather than silent. -/
theorem deltaKUnit_eq_minSwap_schur (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L ell → SuTwo) :
    deltaKUnit ell levels U B
      = AdalyFormal.Balaban.MinSwap.schur
          (fun A : Bond L → SuTwo => covPlaqInner (curlCovariantLM U A) (curlCovariantLM U A))
          {A : Bond L → SuTwo | RcovLM U levels (gradCovariantAdjointLM U A) = 0}
          (lineCoarseRestrictCovLM U ell) B := by
  unfold deltaKUnit AdalyFormal.Balaban.MinSwap.schur
  congr 1
  ext r
  constructor
  · rintro ⟨A, h1, h2, rfl⟩
    exact ⟨A, ⟨h2, h1⟩, rfl⟩
  · rintro ⟨A, ⟨h2, h1⟩, rfl⟩
    exact ⟨A, h1, h2, rfl⟩

#print axioms deltaKUnit_eq_deltaJ_of_mem
#print axioms deltaKUnit_isLeast
#print axioms deltaKUnit_factors_through_Q
#print axioms deltaKUnit_le_fine_energy
#print axioms deltaKUnit_nonneg
#print axioms deltaKUnit_eq_minSwap_schur

/-! ## §3 — THE DOMAIN: which unit-level fields have a fine lift, and the loud empty-fibre hazard

The dispatch's measured hazard: the Landau fibre was found EMPTY over some coarse fields at `U = 1`
(rank 80 of 88 in a numerical probe). Fibre-nonemptiness is background-dependent and is NOT assumed
anywhere here. `liftableUnitFields` names the exact set on which the form has content, and it is a
SUBMODULE (the image of a kernel under a linear map), so the domain is a linear object rather than
an ad-hoc collection. -/

/-- The gauge-fixed fine fields — the kernel of `R^{cov}(U) ∘ ∂*_U`. -/
noncomputable def gaugeFixedFine (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    Submodule ℝ (Bond L → SuTwo) :=
  LinearMap.ker ((RcovLM U levels).comp (gradCovariantAdjointLM U))

theorem mem_gaugeFixedFine {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {A : Bond L → SuTwo} :
    A ∈ gaugeFixedFine levels U ↔ RcovLM U levels (gradCovariantAdjointLM U A) = 0 := Iff.rfl

/-- **THE DOMAIN OF THE UNIT-LEVEL FORM**, as a submodule of unit-level fields: the image of the
gauge-fixed fine fields under the faithful covariant block average. -/
noncomputable def liftableUnitFields (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    Submodule ℝ (CoarseBond L ell → SuTwo) :=
  Submodule.map (lineCoarseRestrictCovLM U ell) (gaugeFixedFine levels U)

theorem mem_liftableUnitFields_of_mem_unitFibre {ell : ℕ}
    {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} {A0 : Bond L → SuTwo}
    (h0 : A0 ∈ unitFibre ell levels U B) :
    B ∈ liftableUnitFields ell levels U :=
  Submodule.mem_map.mpr ⟨A0, h0.2, h0.1⟩

/-- **A NAMED LIFT.** Rather than register an `∃`-concluding declaration (S91: an existential over
free data is the defect that has killed three statements in this project), the witness is a
CONSTRUCTION: `unitLift` picks a fine lift out of the `liftableUnitFields` membership proof, and
`unitLift_mem_unitFibre` certifies it. No statement in this module concludes in `∃`/`Nonempty`. -/
noncomputable def unitLift {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} (hB : B ∈ liftableUnitFields ell levels U) :
    Bond L → SuTwo :=
  (Submodule.mem_map.mp hB).choose

theorem unitLift_mem_unitFibre {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} (hB : B ∈ liftableUnitFields ell levels U) :
    unitLift levels U hB ∈ unitFibre ell levels U B :=
  ⟨(Submodule.mem_map.mp hB).choose_spec.2, (Submodule.mem_map.mp hB).choose_spec.1⟩

/-- On its domain the form is attained and nonnegative — with no lift supplied by the caller. -/
theorem deltaKUnit_isLeast_of_liftable {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} (hB : B ∈ liftableUnitFields ell levels U) :
    IsLeast (fibreEnergies ell levels U B) (deltaKUnit ell levels U B) :=
  deltaKUnit_isLeast levels U _ B (unitLift_mem_unitFibre levels U hB)

theorem deltaKUnit_nonneg_of_liftable {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} (hB : B ∈ liftableUnitFields ell levels U) :
    0 ≤ deltaKUnit ell levels U B :=
  deltaKUnit_nonneg levels U _ B (unitLift_mem_unitFibre levels U hB)

/-- **THE EMPTY-FIBRE HAZARD, MADE LOUD.** `sInf ∅ = 0`, so off the domain the form silently reads
`0` — indistinguishable from a genuine zero. Stated as a theorem so no consumer can meet it by
surprise: a `deltaKUnit … B = 0` is evidence of nothing unless `B ∈ liftableUnitFields`. -/
theorem deltaKUnit_eq_zero_of_no_lift {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L ell → SuTwo)
    (h : fibreEnergies ell levels U B = (∅ : Set ℝ)) :
    deltaKUnit ell levels U B = 0 := by
  unfold deltaKUnit
  rw [h]
  exact Real.sInf_empty

/-! ### §3b — AT `ell = 1` THE FORM IS TOTAL: the emptiness hazard is DECIDED, safely

At block side `1` the faithful covariant block average is the IDENTITY for EVERY background —
`RegularUGamma0.lineCoarseRestrictCov_one_eq_self`, because the `ell = 1` transport path
`Γ_{y,y} ++ straightSegment y y μ` is empty and its holonomy is `1`. So the lift is the same data
re-indexed: `unitLiftOne`, a NAMED construction. At `levels = oneLevelUniv` the gauge clause is
vacuous, hence `liftableUnitFields 1 (oneLevelUniv L) U = ⊤`: EVERY unit-level field has a fine
lift and `deltaKUnit_eq_zero_of_no_lift` can never fire.

~~An earlier draft proved this by injectivity
(`CovariantHjFaithful.lineCoarseRestrictCovLM_one_eq_zero_imp`) plus equality of finite dimensions,
defining `coarseBondOneEquiv` / `bondOneLinearEquiv` / `finrank_bond_eq_finrank_coarseBond_one`.~~
**SUPERSEDED and DELETED (LAW-19): those three declarations duplicated
`RegularUGamma0.coarseBond_one_bijective` and `RegularUGamma0.lineCoarseRestrictCov_one_eq_self`,
which were already in the tree.** Retained struck so the duplication is on the record.

**Scope, stated as a limit and not as a claim.** At `ell ≥ 2` no such statement is made here.
`Q_ell` then maps a larger space onto a smaller one and which unit-level fields are hit is NOT
settled by this module; what IS established is one concrete non-vacuity point, `B7unit ≠ 0` in
`liftableUnitFields 2 …` (§4). -/

/-- **THE NAMED `ell = 1` LIFT.** At block side `1` the faithful covariant block average is the
IDENTITY for every background (`RegularUGamma0.lineCoarseRestrictCov_one_eq_self` — reused, not
re-proved: the `ell = 1` transport path `Γ_{y,y} ++ straightSegment y y μ` is empty, so its
holonomy is `1`). The lift is therefore the same data re-indexed. -/
def unitLiftOne {L : PeriodicLatticeExtent} (B : CoarseBond L 1 → SuTwo) : Bond L → SuTwo :=
  fun b => B (⟨b.1, AdalyFormal.Balaban.CovariantHjMinimizer.mem_CoarseLattice_one b.1⟩, b.2)

theorem lineCoarseRestrictCovLM_one_unitLiftOne
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L 1 → SuTwo) :
    lineCoarseRestrictCovLM U 1 (unitLiftOne B) = B := by
  funext c
  rw [lineCoarseRestrictCovLM_apply,
    AdalyFormal.Balaban.RegularUGamma0.lineCoarseRestrictCov_one_eq_self]
  rfl

/-- **`Q_1(U)` IS SURJECTIVE**, with the preimage the NAMED `unitLiftOne` rather than a choice. -/
theorem lineCoarseRestrictCovLM_one_surjective
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Function.Surjective (lineCoarseRestrictCovLM U 1) :=
  fun B => ⟨unitLiftOne B, lineCoarseRestrictCovLM_one_unitLiftOne U B⟩

/-- At `levels = oneLevelUniv` the gauge clause is vacuous, so every fine field is gauge-fixed. -/
theorem gaugeFixedFine_oneLevelUniv_eq_top (L : PeriodicLatticeExtent)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    gaugeFixedFine (oneLevelUniv L) U = ⊤ :=
  Submodule.eq_top_iff'.mpr (fun A => RcovLM_oneLevelUniv_eq_zero U (gradCovariantAdjointLM U A))

/-- With the gauge clause vacuous, the domain is exactly the range of the block average. -/
theorem liftableUnitFields_oneLevelUniv_eq_range (ell : ℕ) (L : PeriodicLatticeExtent)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    liftableUnitFields ell (oneLevelUniv L) U
      = LinearMap.range (lineCoarseRestrictCovLM U ell) := by
  unfold liftableUnitFields
  rw [gaugeFixedFine_oneLevelUniv_eq_top, Submodule.map_top]

/-- **THE FORM IS TOTAL AT `ell = 1`.** Every unit-level field has a fine lift, so the `sInf ∅`
artefact of `deltaKUnit_eq_zero_of_no_lift` cannot occur at block side `1`, for ANY background. -/
theorem liftableUnitFields_ell1_oneLevelUniv_eq_top (L : PeriodicLatticeExtent)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    liftableUnitFields 1 (oneLevelUniv L) U = ⊤ :=
  Submodule.eq_top_iff'.mpr (fun B => Submodule.mem_map.mpr
    ⟨unitLiftOne B, RcovLM_oneLevelUniv_eq_zero U _,
      lineCoarseRestrictCovLM_one_unitLiftOne U B⟩)

/-- The named `ell = 1` lift genuinely lies in the fibre — the non-emptiness statement with no
existential in its conclusion. -/
theorem unitLiftOne_mem_unitFibre (L : PeriodicLatticeExtent)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection]
    (B : CoarseBond L 1 → SuTwo) :
    unitLiftOne B ∈ unitFibre 1 (oneLevelUniv L) U B :=
  ⟨lineCoarseRestrictCovLM_one_unitLiftOne U B, RcovLM_oneLevelUniv_eq_zero U _⟩

#print axioms lineCoarseRestrictCovLM_one_unitLiftOne
#print axioms lineCoarseRestrictCovLM_one_surjective
#print axioms unitLiftOne_mem_unitFibre
#print axioms gaugeFixedFine_oneLevelUniv_eq_top
#print axioms liftableUnitFields_oneLevelUniv_eq_range
#print axioms liftableUnitFields_ell1_oneLevelUniv_eq_top

#print axioms mem_gaugeFixedFine
#print axioms mem_liftableUnitFields_of_mem_unitFibre
#print axioms unitLift_mem_unitFibre
#print axioms deltaKUnit_isLeast_of_liftable
#print axioms deltaKUnit_nonneg_of_liftable
#print axioms deltaKUnit_eq_zero_of_no_lift

/-! ## §3c — "FORM" IS EARNED: the quadratic-form laws, PROVED

A prosecution convicted the word "form": `deltaKUnit` is a real-valued function and nothing in the
first version of this module gave it a scaling law, a parallelogram law, or a polarization. This
section supplies all three. Two of them (`deltaKUnit_zero_eq_zero`, `deltaKUnit_smul`'s `c = 0`
branch) are unconditional; the parallelogram and polarization are stated on `liftableUnitFields`,
which is where the form has content at all (§3).

The mechanism throughout is that `A ↦ c • A` and `A ↦ A ± A'` map fibres to fibres — `Q_ell`, `∂*_U`
and `R^{cov}` are all linear — and the fine curl energy is a genuine quadratic form on the fine
level. The `sInf` then transports the law, PROVIDED the fibre is nonempty; that proviso is exactly
the `liftableUnitFields` hypothesis and is never left implicit.

`covPlaqInner_smul_left` / `_smul_right` / `_sub_left` did not exist anywhere in the tree
(searched: only `covPlaqInner_add_left`, `_add_right`, `_sub_right`, `_zero_right` are present), so
they are proved here from `hsInner_smul_left` / `hsInner_smul_right` / `covPlaqInner_symm`. -/

theorem covPlaqInner_smul_left (c : ℝ) (A B : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner (c • A) B = c * covPlaqInner A B := by
  unfold covPlaqInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Pi.smul_apply, hsInner_smul_left]

theorem covPlaqInner_smul_right (c : ℝ) (A B : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner A (c • B) = c * covPlaqInner A B := by
  rw [covPlaqInner_symm A (c • B), covPlaqInner_smul_left, covPlaqInner_symm B A]

theorem covPlaqInner_smul_self (c : ℝ) (A : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner (c • A) (c • A) = c ^ 2 * covPlaqInner A A := by
  rw [covPlaqInner_smul_left, covPlaqInner_smul_right]
  ring

theorem covPlaqInner_sub_left (A B C : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner (A - B) C = covPlaqInner A C - covPlaqInner B C := by
  rw [covPlaqInner_symm (A - B) C, covPlaqInner_sub_right, covPlaqInner_symm C A,
    covPlaqInner_symm C B]

#print axioms covPlaqInner_smul_left
#print axioms covPlaqInner_smul_right
#print axioms covPlaqInner_smul_self
#print axioms covPlaqInner_sub_left

/-- **`Δ_k(0) = 0`, UNCONDITIONALLY.** The zero fine field is always a lift of the zero unit-level
field (`Q_ell` and `R∂*_U` are linear) and its curl energy is `0`, while every fibre energy is
`≥ 0`. So this is a GENUINE attained zero at every `ell`, `levels`, `U` — not the `sInf ∅`
artefact. No orthogonal-projection instance is used. -/
theorem deltaKUnit_zero_eq_zero (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    deltaKUnit ell levels U (0 : CoarseBond L ell → SuTwo) = 0 := by
  have hmem : (0 : ℝ) ∈ fibreEnergies ell levels U (0 : CoarseBond L ell → SuTwo) :=
    ⟨0, map_zero _, by simp only [map_zero], by
      simp only [map_zero]
      rw [covPlaqInner_zero_right]⟩
  have hlb : ∀ r ∈ fibreEnergies ell levels U (0 : CoarseBond L ell → SuTwo), (0 : ℝ) ≤ r := by
    rintro r ⟨A, -, -, rfl⟩
    exact covPlaqInner_self_nonneg _
  exact IsLeast.csInf_eq
    (⟨hmem, hlb⟩ : IsLeast (fibreEnergies ell levels U (0 : CoarseBond L ell → SuTwo)) (0 : ℝ))

/-- **THE QUADRATIC SCALING LAW.** `Δ_k(cB) = c²·Δ_k(B)` on the domain, for EVERY real `c`
(including `c = 0`, where both sides are `0`). This is the first of the three facts that make
"form" a theorem rather than a word: a merely-nonnegative function of `B` need not scale at all. -/
theorem deltaKUnit_smul {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (c : ℝ) {B : CoarseBond L ell → SuTwo} (hB : B ∈ liftableUnitFields ell levels U) :
    deltaKUnit ell levels U (c • B) = c ^ 2 * deltaKUnit ell levels U B := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, deltaKUnit_zero_eq_zero]
    ring
  · have hleast := deltaKUnit_isLeast_of_liftable levels U hB
    obtain ⟨A, hAQ, hAR, hAval⟩ := hleast.1
    have hmem : c ^ 2 * deltaKUnit ell levels U B ∈ fibreEnergies ell levels U (c • B) := by
      refine ⟨c • A, ?_, ?_, ?_⟩
      · rw [map_smul, hAQ]
      · rw [map_smul, map_smul, hAR, smul_zero]
      · rw [map_smul, covPlaqInner_smul_self, hAval]
    have hlb : ∀ r ∈ fibreEnergies ell levels U (c • B),
        c ^ 2 * deltaKUnit ell levels U B ≤ r := by
      rintro r ⟨A', hA'Q, hA'R, rfl⟩
      have hin1 : lineCoarseRestrictCovLM U ell (c⁻¹ • A') = B := by
        rw [map_smul, hA'Q, smul_smul, inv_mul_cancel₀ hc, one_smul]
      have hin2 : RcovLM U levels (gradCovariantAdjointLM U (c⁻¹ • A')) = 0 := by
        rw [map_smul, map_smul, hA'R, smul_zero]
      have hle := hleast.2 ⟨c⁻¹ • A', hin1, hin2, rfl⟩
      rw [map_smul, covPlaqInner_smul_self] at hle
      have hcpos : (0 : ℝ) < c ^ 2 := by positivity
      have hcc : c ^ 2 * (c⁻¹) ^ 2 = 1 := by
        field_simp
      calc c ^ 2 * deltaKUnit ell levels U B
          ≤ c ^ 2 * ((c⁻¹) ^ 2 *
              covPlaqInner (curlCovariantLM U A') (curlCovariantLM U A')) :=
            mul_le_mul_of_nonneg_left hle (le_of_lt hcpos)
        _ = covPlaqInner (curlCovariantLM U A') (curlCovariantLM U A') := by
            rw [← mul_assoc, hcc, one_mul]
    exact IsLeast.csInf_eq (⟨hmem, hlb⟩ : IsLeast (fibreEnergies ell levels U (c • B)) _)

#print axioms deltaKUnit_zero_eq_zero
#print axioms deltaKUnit_smul

/-- The closest-point projection onto `W^{cov}_faithful` is ADDITIVE. It is built from
`Submodule.starProjection` (a continuous linear map) conjugated by the linear equivalence
`plaqFnEquiv`, so this is `map_add` three times; no such lemma existed in `CovariantHjFaithful`. -/
theorem curlImageCovProjFaithful_add (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (X Y : PeriodicLatticePlaquette L → SuTwo) :
    curlImageCovProjFaithful ell levels U (X + Y)
      = curlImageCovProjFaithful ell levels U X + curlImageCovProjFaithful ell levels U Y := by
  unfold curlImageCovProjFaithful
  simp only [map_add]

theorem curlImageCovProjFaithful_sub (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (X Y : PeriodicLatticePlaquette L → SuTwo) :
    curlImageCovProjFaithful ell levels U (X - Y)
      = curlImageCovProjFaithful ell levels U X - curlImageCovProjFaithful ell levels U Y := by
  unfold curlImageCovProjFaithful
  simp only [map_sub]

theorem hjCorrectionTargetCovFaithful_add (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A1 A2 : Bond L → SuTwo) :
    hjCorrectionTargetCovFaithful ell levels U (A1 + A2)
      = hjCorrectionTargetCovFaithful ell levels U A1
        + hjCorrectionTargetCovFaithful ell levels U A2 := by
  unfold hjCorrectionTargetCovFaithful
  rw [map_add, curlImageCovProjFaithful_add]
  abel

theorem hjCorrectionTargetCovFaithful_sub (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A1 A2 : Bond L → SuTwo) :
    hjCorrectionTargetCovFaithful ell levels U (A1 - A2)
      = hjCorrectionTargetCovFaithful ell levels U A1
        - hjCorrectionTargetCovFaithful ell levels U A2 := by
  unfold hjCorrectionTargetCovFaithful
  rw [map_sub, curlImageCovProjFaithful_sub]
  abel

/-- `Δ_J` is the squared norm of the correction target — the same identity the §6 Pythagoras proof
uses inline, extracted so the quadratic laws can be read off it. -/
theorem deltaJ_eq_covPlaqInner_target (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    deltaJQuadFormCovFaithful ell levels U A0
      = covPlaqInner (hjCorrectionTargetCovFaithful ell levels U A0)
          (hjCorrectionTargetCovFaithful ell levels U A0) := by
  unfold deltaJQuadFormCovFaithful
  rw [curlCov_hjExtensionCovFaithful]

/-- **THE PARALLELOGRAM LAW AT THE FINE LEVEL.** -/
theorem deltaJ_parallelogram (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A1 A2 : Bond L → SuTwo) :
    deltaJQuadFormCovFaithful ell levels U (A1 + A2)
        + deltaJQuadFormCovFaithful ell levels U (A1 - A2)
      = 2 * deltaJQuadFormCovFaithful ell levels U A1
        + 2 * deltaJQuadFormCovFaithful ell levels U A2 := by
  rw [deltaJ_eq_covPlaqInner_target ell levels U (A1 + A2),
    deltaJ_eq_covPlaqInner_target ell levels U (A1 - A2),
    deltaJ_eq_covPlaqInner_target ell levels U A1,
    deltaJ_eq_covPlaqInner_target ell levels U A2,
    hjCorrectionTargetCovFaithful_add, hjCorrectionTargetCovFaithful_sub,
    covPlaqInner_add_left, covPlaqInner_add_right, covPlaqInner_add_right,
    covPlaqInner_sub_left, covPlaqInner_sub_right, covPlaqInner_sub_right]
  ring

/-- **THE PARALLELOGRAM LAW AT THE UNIT LEVEL**, on `liftableUnitFields`. Together with
`deltaKUnit_smul` and `deltaKUnit_zero_eq_zero` this is what makes `deltaKUnit` a QUADRATIC FORM on
its domain and not merely a nonnegative function of `B`. -/
theorem deltaKUnit_parallelogram {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    {B1 B2 : CoarseBond L ell → SuTwo}
    (h1 : B1 ∈ liftableUnitFields ell levels U)
    (h2 : B2 ∈ liftableUnitFields ell levels U) :
    deltaKUnit ell levels U (B1 + B2) + deltaKUnit ell levels U (B1 - B2)
      = 2 * deltaKUnit ell levels U B1 + 2 * deltaKUnit ell levels U B2 := by
  obtain ⟨A1, hA1g, hA1q⟩ := Submodule.mem_map.mp h1
  obtain ⟨A2, hA2g, hA2q⟩ := Submodule.mem_map.mp h2
  have g1 : RcovLM U levels (gradCovariantAdjointLM U A1) = 0 := mem_gaugeFixedFine.mp hA1g
  have g2 : RcovLM U levels (gradCovariantAdjointLM U A2) = 0 := mem_gaugeFixedFine.mp hA2g
  have e1 : deltaKUnit ell levels U B1 = deltaJQuadFormCovFaithful ell levels U A1 :=
    deltaKUnit_eq_deltaJ_of_mem levels U A1 B1 ⟨hA1q, g1⟩
  have e2 : deltaKUnit ell levels U B2 = deltaJQuadFormCovFaithful ell levels U A2 :=
    deltaKUnit_eq_deltaJ_of_mem levels U A2 B2 ⟨hA2q, g2⟩
  have ep : deltaKUnit ell levels U (B1 + B2)
      = deltaJQuadFormCovFaithful ell levels U (A1 + A2) :=
    deltaKUnit_eq_deltaJ_of_mem levels U (A1 + A2) (B1 + B2)
      ⟨by rw [map_add, hA1q, hA2q], by rw [map_add, map_add, g1, g2, add_zero]⟩
  have em : deltaKUnit ell levels U (B1 - B2)
      = deltaJQuadFormCovFaithful ell levels U (A1 - A2) :=
    deltaKUnit_eq_deltaJ_of_mem levels U (A1 - A2) (B1 - B2)
      ⟨by rw [map_sub, hA1q, hA2q], by rw [map_sub, map_sub, g1, g2, sub_zero]⟩
  rw [e1, e2, ep, em]
  exact deltaJ_parallelogram ell levels U A1 A2

/-- **THE POLARIZATION of the unit-level form.** -/
noncomputable def deltaKUnitPolar (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B1 B2 : CoarseBond L ell → SuTwo) : ℝ :=
  (deltaKUnit ell levels U (B1 + B2) - deltaKUnit ell levels U (B1 - B2)) / 4

/-- **THE POLARIZATION IDENTITY REPRODUCES THE FORM ON THE DIAGONAL.** -/
theorem deltaKUnitPolar_diag {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} (hB : B ∈ liftableUnitFields ell levels U) :
    deltaKUnitPolar ell levels U B B = deltaKUnit ell levels U B := by
  unfold deltaKUnitPolar
  rw [sub_self, deltaKUnit_zero_eq_zero,
    show B + B = (2 : ℝ) • B from (two_smul ℝ B).symm,
    deltaKUnit_smul levels U 2 hB]
  norm_num

/-- **§3c ASSEMBLED — the word "form" is now a theorem.** Vanishing at `0`, the quadratic scaling
law, the parallelogram law and the polarization identity, all on `liftableUnitFields`. -/
theorem deltaKUnit_is_quadratic_form {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (c : ℝ) {B1 B2 : CoarseBond L ell → SuTwo}
    (h1 : B1 ∈ liftableUnitFields ell levels U)
    (h2 : B2 ∈ liftableUnitFields ell levels U) :
    deltaKUnit ell levels U (0 : CoarseBond L ell → SuTwo) = 0
  ∧ deltaKUnit ell levels U (c • B1) = c ^ 2 * deltaKUnit ell levels U B1
  ∧ deltaKUnit ell levels U (B1 + B2) + deltaKUnit ell levels U (B1 - B2)
      = 2 * deltaKUnit ell levels U B1 + 2 * deltaKUnit ell levels U B2
  ∧ deltaKUnitPolar ell levels U B1 B1 = deltaKUnit ell levels U B1 :=
  ⟨deltaKUnit_zero_eq_zero ell levels U, deltaKUnit_smul levels U c h1,
    deltaKUnit_parallelogram levels U h1 h2, deltaKUnitPolar_diag levels U h1⟩

#print axioms curlImageCovProjFaithful_add
#print axioms curlImageCovProjFaithful_sub
#print axioms hjCorrectionTargetCovFaithful_add
#print axioms hjCorrectionTargetCovFaithful_sub
#print axioms deltaJ_eq_covPlaqInner_target
#print axioms deltaJ_parallelogram
#print axioms deltaKUnit_parallelogram
#print axioms deltaKUnitPolar
#print axioms deltaKUnitPolar_diag
#print axioms deltaKUnit_is_quadratic_form

/-! ## §3d — THE `ell = 0` COLLAPSE, PROVED (the undisclosed degenerate block side)

The first version of this module discussed the `ell = 1` degeneracy repeatedly and never mentioned
`ell = 0`. A de-correlated prosecution pass compiled the collapse and convicted the omission. It is
now a theorem.

At block side `0` the faithful covariant block average carries the normalization `1/(0:ℝ)^4 = 0`, so
`Q_0` ANNIHILATES EVERY FINE FIELD (`MinSwap.lineCoarseRestrictCovLM_ell_zero`, reused — LAW-19;
importing `MinSwap` for it takes this island's import closure from 88 modules to 108 — MinSwap
itself plus 19 of its dependencies — which is the measured price of not re-proving it here).
Consequences, all proved below:

* the fibre above any NONZERO unit-level field is EMPTY, so `deltaKUnit` there is the `sInf ∅ = 0`
  artefact `deltaKUnit_eq_zero_of_no_lift` warns about;
* the fibre above `0` is nonempty, and the value there is a genuine `0`;
* hence `deltaKUnit 0 levels U B = 0` for EVERY `B`, `levels`, `U` — the form is IDENTICALLY ZERO.

`CoarseBond L 0` is NOT empty, so this is a collapse of the OPERATOR and not an artefact of an empty
index type: `coarseWitness0_ne_zero` exhibits a nonzero unit-level field at `ell = 0` on `witL7`. -/

theorem unitFibre_ell0_eq_empty_of_ne_zero (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {B : CoarseBond L 0 → SuTwo} (hB : B ≠ 0) :
    unitFibre 0 levels U B = (∅ : Set (Bond L → SuTwo)) := by
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA
  exact hB (hA.1.symm.trans (lineCoarseRestrictCovLM_ell_zero U A))

theorem fibreEnergies_ell0_eq_empty_of_ne_zero (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {B : CoarseBond L 0 → SuTwo} (hB : B ≠ 0) :
    fibreEnergies 0 levels U B = (∅ : Set ℝ) := by
  rw [fibreEnergies_eq_image, unitFibre_ell0_eq_empty_of_ne_zero levels U hB, Set.image_empty]

/-- **THE `ell = 0` COLLAPSE.** The unit-level form is IDENTICALLY `0` at block side `0`, for every
unit-level field, every `levels`, every background. Above `0` this is a genuine attained minimum;
above every other `B` it is the empty-infimum artefact. Either way the form carries NO information
about the fine field, so every statement in this module that is quantified over `ell` says nothing
at `ell = 0`. -/
theorem deltaKUnit_ell0_eq_zero (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L 0 → SuTwo) :
    deltaKUnit 0 levels U B = 0 := by
  by_cases hB : B = 0
  · subst hB
    exact deltaKUnit_zero_eq_zero 0 levels U
  · exact deltaKUnit_eq_zero_of_no_lift levels U B
      (fibreEnergies_ell0_eq_empty_of_ne_zero levels U hB)

/-- A NONZERO unit-level field at block side `0`, so that `deltaKUnit_ell0_eq_zero` is a genuine
collapse of `Q_0` and not the vacuous statement that `CoarseBond L 0 → SuTwo` has only one element.
Reuses `MinSwap.const_coarse_ne_zero` (LAW-19). -/
noncomputable def coarseWitness0 : CoarseBond witL7 0 → SuTwo := fun _ => suTwoWitness

theorem coarseWitness0_ne_zero : coarseWitness0 ≠ 0 :=
  const_coarse_ne_zero suTwoWitness_ne_zero

/-- **§3d ASSEMBLED.** A NONZERO unit-level field at `ell = 0` whose form value is `0`. -/
theorem deltaKUnit_ell0_collapse_is_not_vacuous :
    coarseWitness0 ≠ 0
  ∧ deltaKUnit 0 (oneLevelUniv witL7) (trivialU witL7) coarseWitness0 = 0
  ∧ unitFibre 0 (oneLevelUniv witL7) (trivialU witL7) coarseWitness0
      = (∅ : Set (Bond witL7 → SuTwo)) :=
  ⟨coarseWitness0_ne_zero,
    deltaKUnit_ell0_eq_zero (oneLevelUniv witL7) (trivialU witL7) coarseWitness0,
    unitFibre_ell0_eq_empty_of_ne_zero (oneLevelUniv witL7) (trivialU witL7)
      coarseWitness0_ne_zero⟩

#print axioms unitFibre_ell0_eq_empty_of_ne_zero
#print axioms fibreEnergies_ell0_eq_empty_of_ne_zero
#print axioms deltaKUnit_ell0_eq_zero
#print axioms coarseWitness0
#print axioms coarseWitness0_ne_zero
#print axioms deltaKUnit_ell0_collapse_is_not_vacuous

/-! ## §3e — MONOTONICITY IN `levels`: the live-`R` argument, repaired into theorems

The first version of this module argued in prose that with a live `R` the fibre is smaller, "so the
infimum only rises, so §4's positivity persists". **That argument is invalid as stated**, and a
de-correlated prosecution pass convicted it. Subset-monotonicity of `sInf` requires the SMALLER set
to be NONEMPTY; with `sInf ∅ = 0` (this module's own `deltaKUnit_eq_zero_of_no_lift`) a smaller,
EMPTY fibre makes the value DROP to `0`, destroying positivity rather than preserving it.

Repaired here into three statements, with the missing hypothesis carried explicitly:

* `deltaKUnit_oneLevelUniv_le_of_lift` — monotonicity, given a lift in the smaller fibre;
* `deltaKUnit_pos_of_pos_oneLevelUniv` — positivity persists, same hypothesis;
* `deltaKUnit_pos_or_unitFibre_empty` — the dichotomy, with NO hypothesis: either positivity
  persists or the live-`R` fibre is empty and the value is the artefact.

**OPEN, stated plainly.** No concrete `levels` with a live `R` and a nonempty fibre above `B7unit`
is exhibited in this module, so §4's positivity is not known to persist at any specific live `R`.
The hypothesis of the first two theorems is dischargeable in principle (it is a membership, not an
existential over free data) but nothing here discharges it. Reading
`deltaKUnit_pos_of_pos_oneLevelUniv` as "positivity persists" without supplying `h0` is precisely
the convicted move. -/

theorem fibreEnergies_bddBelow (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L ell → SuTwo) : BddBelow (fibreEnergies ell levels U B) := by
  refine ⟨0, ?_⟩
  rintro r ⟨A, -, -, rfl⟩
  exact covPlaqInner_self_nonneg _

/-- Every fibre sits inside the `oneLevelUniv` fibre: the two differ only in the gauge clause, and
at `oneLevelUniv` that clause is vacuous. -/
theorem unitFibre_subset_oneLevelUniv {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection]
    (B : CoarseBond L ell → SuTwo) :
    unitFibre ell levels U B ⊆ unitFibre ell (oneLevelUniv L) U B :=
  fun _ hA => ⟨hA.1, RcovLM_oneLevelUniv_eq_zero U _⟩

theorem fibreEnergies_subset_oneLevelUniv {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection]
    (B : CoarseBond L ell → SuTwo) :
    fibreEnergies ell levels U B ⊆ fibreEnergies ell (oneLevelUniv L) U B := by
  rw [fibreEnergies_eq_image, fibreEnergies_eq_image]
  exact Set.image_mono (unitFibre_subset_oneLevelUniv levels U B)

/-- **THE INFIMUM ONLY RISES — with the nonemptiness hypothesis EXPLICIT.** A lift `A0` in the
`levels`-fibre is exactly what the struck prose argument silently assumed. -/
theorem deltaKUnit_oneLevelUniv_le_of_lift {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} {A0 : Bond L → SuTwo}
    (h0 : A0 ∈ unitFibre ell levels U B) :
    deltaKUnit ell (oneLevelUniv L) U B ≤ deltaKUnit ell levels U B := by
  unfold deltaKUnit
  exact csInf_le_csInf (fibreEnergies_bddBelow ell (oneLevelUniv L) U B)
    ⟨covPlaqInner (curlCovariantLM U A0) (curlCovariantLM U A0), A0, h0.1, h0.2, rfl⟩
    (fibreEnergies_subset_oneLevelUniv levels U B)

/-- **POSITIVITY PERSISTS TO A LIVE `R`** — the struck claim, now a theorem, with the hypothesis it
needs written into its statement. -/
theorem deltaKUnit_pos_of_pos_oneLevelUniv {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection]
    {B : CoarseBond L ell → SuTwo} {A0 : Bond L → SuTwo}
    (h0 : A0 ∈ unitFibre ell levels U B)
    (hpos : 0 < deltaKUnit ell (oneLevelUniv L) U B) :
    0 < deltaKUnit ell levels U B :=
  lt_of_lt_of_le hpos (deltaKUnit_oneLevelUniv_le_of_lift levels U h0)

/-- **THE DICHOTOMY, WITH NO EXTRA HYPOTHESIS.** Given `oneLevelUniv`-positivity at `B`, EITHER the
positivity persists at `levels`, OR the `levels`-fibre above `B` is EMPTY — in which case
`deltaKUnit … B` is the `sInf ∅ = 0` artefact and is evidence of nothing. There is no third case,
and the struck prose asserted the first branch while ignoring the second. -/
theorem deltaKUnit_pos_or_unitFibre_empty {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection]
    (B : CoarseBond L ell → SuTwo)
    (hpos : 0 < deltaKUnit ell (oneLevelUniv L) U B) :
    0 < deltaKUnit ell levels U B ∨ unitFibre ell levels U B = (∅ : Set (Bond L → SuTwo)) := by
  rcases Set.eq_empty_or_nonempty (unitFibre ell levels U B) with h | ⟨A0, hA0⟩
  · exact Or.inr h
  · exact Or.inl (deltaKUnit_pos_of_pos_oneLevelUniv levels U hA0 hpos)

#print axioms fibreEnergies_bddBelow
#print axioms unitFibre_subset_oneLevelUniv
#print axioms fibreEnergies_subset_oneLevelUniv
#print axioms deltaKUnit_oneLevelUniv_le_of_lift
#print axioms deltaKUnit_pos_of_pos_oneLevelUniv
#print axioms deltaKUnit_pos_or_unitFibre_empty

/-! ## §4 — NON-VACUITY AT A NON-DEGENERATE LEVEL (`witL7`, `ell = 2`, `U = 1`)

`ell = 1` is a degenerate test point: there `V = ⊥`, `Q_1` is injective, and the unit form is
literally `dstarDQuadForm` transported along a bijection (§6). Every statement in this section is at
`ell = 2`, where `V ≠ ⊥` (`ThirdLevelWitness.V2_witL7_ne_bot`) and the Schur mechanism acts. -/

/-- The UNIT-LEVEL field `B7unit = Q₂ B7`. Its type is `CoarseBond witL7 2 → SuTwo`. -/
noncomputable def B7unit : CoarseBond witL7 2 → SuTwo :=
  lineCoarseRestrictCovLM (trivialU witL7) 2 B7

/-- `B7` is a fine lift of `B7unit`. -/
theorem B7_mem_unitFibre :
    B7 ∈ unitFibre 2 (oneLevelUniv witL7) (trivialU witL7) B7unit :=
  ⟨rfl, RcovLM_oneLevelUniv_eq_zero (trivialU witL7) _⟩

/-- The unit-level field is NONZERO — so the witness is not the trivial `B = 0` instance. -/
theorem B7unit_ne_zero : B7unit ≠ 0 := B7_not_kerQ2

theorem B7unit_mem_liftableUnitFields :
    B7unit ∈ liftableUnitFields 2 (oneLevelUniv witL7) (trivialU witL7) :=
  mem_liftableUnitFields_of_mem_unitFibre B7_mem_unitFibre

/-- **THE NON-VACUITY OF THE UNIT-LEVEL FORM**: at a NONZERO unit-level field with a fine lift, the
form is STRICTLY POSITIVE. Transported from `ThirdLevelWitness.third_level_positivity` through
`deltaKUnit_eq_deltaJ_of_mem`; the value is not an empty infimum. -/
theorem deltaKUnit_B7unit_pos :
    0 < deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit := by
  rw [deltaKUnit_eq_deltaJ_of_mem (oneLevelUniv witL7) (trivialU witL7) B7 B7unit
    B7_mem_unitFibre]
  exact third_level_positivity

/-- A SECOND, DISTINCT fine lift of the SAME unit-level field: `B7 + B7'`, with `B7' ∈ V(2)`. -/
theorem B7_add_B7'_mem_unitFibre :
    B7 + B7' ∈ unitFibre 2 (oneLevelUniv witL7) (trivialU witL7) B7unit :=
  ⟨by rw [map_add, B7'_kerQ2, add_zero]; rfl, RcovLM_oneLevelUniv_eq_zero (trivialU witL7) _⟩

theorem B7_ne_B7_add_B7' : B7 ≠ B7 + B7' := by
  intro h
  refine B7'_ne_zero ?_
  have h1 : B7 + B7' = B7 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h1

/-- **THE INTEGRATION-OUT IS NOT OVER A POINT.** Two DISTINCT fine fields lie above the same
unit-level field `B7unit`, and `Δ_J` takes the same value at both. The fine data really is
integrated out, at a level where `V ≠ ⊥`. (The equality is `deltaJ_eq_of_same_fibre`, imported —
what is new is that it is exhibited at an explicit pair of distinct lifts.) -/
theorem two_distinct_lifts_same_value :
    B7 ∈ unitFibre 2 (oneLevelUniv witL7) (trivialU witL7) B7unit
  ∧ B7 + B7' ∈ unitFibre 2 (oneLevelUniv witL7) (trivialU witL7) B7unit
  ∧ B7 ≠ B7 + B7'
  ∧ deltaJQuadFormCovFaithful 2 (oneLevelUniv witL7) (trivialU witL7) B7
      = deltaJQuadFormCovFaithful 2 (oneLevelUniv witL7) (trivialU witL7) (B7 + B7') :=
  ⟨B7_mem_unitFibre, B7_add_B7'_mem_unitFibre, B7_ne_B7_add_B7',
    deltaJ_eq_of_same_fibre (oneLevelUniv witL7) (trivialU witL7) B7 (B7 + B7') B7unit
      B7_mem_unitFibre.1 B7_mem_unitFibre.2
      B7_add_B7'_mem_unitFibre.1 B7_add_B7'_mem_unitFibre.2⟩

/-- **§4 ASSEMBLED.** A nonzero unit-level field, in the domain, with strictly positive unit-level
form, and at least two distinct fine lifts. Every object named; no existential over free data. -/
theorem unit_level_form_nonvacuous :
    B7unit ≠ 0
  ∧ B7unit ∈ liftableUnitFields 2 (oneLevelUniv witL7) (trivialU witL7)
  ∧ 0 < deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit
  ∧ B7 ≠ B7 + B7' :=
  ⟨B7unit_ne_zero, B7unit_mem_liftableUnitFields, deltaKUnit_B7unit_pos, B7_ne_B7_add_B7'⟩

/-- **§3c's QUADRATIC-FORM LAWS ARE NOT VACUOUS.** The laws of §3c are stated on
`liftableUnitFields`, so the first question to ask them is whether that domain contains anything
where the form is not `0`. It does, at the non-degenerate block side: `B7unit` is NONZERO, lies in
the domain, has STRICTLY POSITIVE form value, and the scaling law is exercised there at every real
`c`. Without this, "a quadratic form on `liftableUnitFields`" could have been a statement about a
domain on which the form vanishes identically. -/
theorem quadratic_form_laws_nonvacuous_at_B7unit (c : ℝ) :
    B7unit ≠ 0
  ∧ B7unit ∈ liftableUnitFields 2 (oneLevelUniv witL7) (trivialU witL7)
  ∧ 0 < deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit
  ∧ deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) (c • B7unit)
      = c ^ 2 * deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit :=
  ⟨B7unit_ne_zero, B7unit_mem_liftableUnitFields, deltaKUnit_B7unit_pos,
    deltaKUnit_smul (oneLevelUniv witL7) (trivialU witL7) c B7unit_mem_liftableUnitFields⟩

#print axioms B7_mem_unitFibre
#print axioms B7unit_ne_zero
#print axioms B7unit_mem_liftableUnitFields
#print axioms deltaKUnit_B7unit_pos
#print axioms two_distinct_lifts_same_value
#print axioms unit_level_form_nonvacuous
#print axioms quadratic_form_laws_nonvacuous_at_B7unit

/-! ## §5 — THE FINE LEVEL CARRIES ENERGY THAT IS STRICTLY REMOVED

A form defined by minimisation is only interesting if the minimisation does something. Here it
removes ALL of a strictly positive energy: `B7'` lies above the ZERO unit-level field, the unit form
there is `0`, and `B7'`'s own fine curl energy is `> 0`.

The positivity of `‖D_1 B7'‖²` is obtained WITHOUT a direct plaquette computation: pair the curl
against the `ell = 1` Stokes vector and use the already-proved factoring identity
`⟪stokesU, D_1 v⟫ = stokesPhi (Q_1 v)` (`ThirdLevelStokes.stokes_factoring`). At `ell = 1` the block
is a singleton, so `Q_1 B7'` is the dipole itself and its coarse curl at the origin plaquette is
`2•w ≠ 0`. -/

theorem witL7_one_dvd : ∀ μ : Fin 3, (1 : ℕ) ∣ (witL7 μ + 1) := fun _ => one_dvd _

theorem y70_coarse1 : y70 ∈ CoarseLattice witL7 1 := by
  rw [mem_CoarseLattice]; decide

theorem y70_shift0_coarse1 : coarseShift y70 1 0 ∈ CoarseLattice witL7 1 := by
  rw [mem_CoarseLattice]; decide

theorem y70_shift1_coarse1 : coarseShift y70 1 1 ∈ CoarseLattice witL7 1 := by
  rw [mem_CoarseLattice]; decide

/-- `Q₁ B7'` at the origin direction-`0` coarse bond: **`w`**. At `ell = 1` the block is the
singleton `{y}`, so the block average is the field value itself. -/
theorem Q1_B7'_origin :
    lineCoarseRestrictCovLM (trivialU witL7) 1 B7' ((⟨y70, y70_coarse1⟩, 0) : CoarseBond witL7 1)
      = suTwoWitness := by
  have hZ0 : inBlock y70 1 (pathSiteBack s7Z 0 0) := by decide
  have hP0 : ¬ inBlock y70 1 (pathSiteBack s7P 0 0) := by decide
  rw [show B7' = dipole s7Z s7P 0 suTwoWitness from rfl, Q_dipole_apply_dir]
  rw [Finset.sum_range_one, Finset.sum_range_one]
  rw [if_pos (mem_blockOf.mpr hZ0), if_neg (fun h => hP0 (mem_blockOf.mp h))]
  rw [smul_smul]
  norm_num

/-- `Q₁ B7'` at the direction-`0` coarse bond one step up in direction `1` — the bond
`coarseCurlSuTwo` reads with a minus sign: **`−w`**. -/
theorem Q1_B7'_shifted (hmem : coarseShift y70 1 1 ∈ CoarseLattice witL7 1) :
    lineCoarseRestrictCovLM (trivialU witL7) 1 B7'
        ((⟨coarseShift y70 1 1, hmem⟩, 0) : CoarseBond witL7 1)
      = -suTwoWitness := by
  have hZ0 : ¬ inBlock (coarseShift y70 1 1) 1 (pathSiteBack s7Z 0 0) := by decide
  have hP0 : inBlock (coarseShift y70 1 1) 1 (pathSiteBack s7P 0 0) := by decide
  rw [show B7' = dipole s7Z s7P 0 suTwoWitness from rfl, Q_dipole_apply_dir]
  rw [Finset.sum_range_one, Finset.sum_range_one]
  rw [if_neg (fun h => hZ0 (mem_blockOf.mp h)), if_pos (mem_blockOf.mpr hP0)]
  rw [smul_smul]
  norm_num

/-- **The coarse curl of `Q₁ B7'` at the origin plaquette is `2 • w`.** Four-term combination:
`w + 0 − (−w) − 0`. -/
theorem coarseCurl_Q1_B7' :
    coarseCurlSuTwo witL7_one_dvd (lineCoarseRestrictCovLM (trivialU witL7) 1 B7')
        ((⟨y70, y70_coarse1⟩, ⟨(0, 1), hlt01⟩) :
          AdalyFormal.Balaban.CoarseCurl.CoarsePlaquette witL7 1)
      = (2 : ℝ) • suTwoWitness := by
  rw [coarseCurlSuTwo_apply witL7_one_dvd _ y70_coarse1 hlt01 y70_shift0_coarse1
    y70_shift1_coarse1]
  rw [Q1_B7'_origin, Q1_B7'_shifted y70_shift1_coarse1,
    show lineCoarseRestrictCovLM (trivialU witL7) 1 B7'
        ((⟨coarseShift y70 1 0, y70_shift0_coarse1⟩, 1) : CoarseBond witL7 1) = 0 from
      Q_dipole_apply_offdir 1 s7Z s7P 0 suTwoWitness _ one_ne_zero_fin3,
    show lineCoarseRestrictCovLM (trivialU witL7) 1 B7'
        ((⟨y70, y70_coarse1⟩, 1) : CoarseBond witL7 1) = 0 from
      Q_dipole_apply_offdir 1 s7Z s7P 0 suTwoWitness _ one_ne_zero_fin3]
  rw [add_zero, sub_neg_eq_add, sub_zero, two_smul]

theorem stokesPhi_Q1_B7'_pos :
    0 < stokesPhi 1 witL7_one_dvd y70_coarse1 hlt01 suTwoWitness
        (lineCoarseRestrictCovLM (trivialU witL7) 1 B7') := by
  rw [stokesPhi_apply, coarseCurl_Q1_B7', hsInner_smul_right]
  simp only [Nat.cast_one, one_pow, one_mul]
  have h := hsInner_witness_pos
  linarith

/-- **The flat curl of `B7'` is NONZERO** — it pairs nontrivially with the `ell = 1` Stokes
vector. -/
theorem curl_B7'_ne_zero : curlCovariantLM (trivialU witL7) B7' ≠ 0 := by
  intro h
  have hf := stokes_factoring (L := witL7) (ell := 1) one_pos witL7_one_dvd y70_coarse1 hlt01
    suTwoWitness B7'
  rw [h, covPlaqInner_zero_right] at hf
  have hp := stokesPhi_Q1_B7'_pos
  linarith

/-- `B7'` has strictly positive fine curl energy at `U = 1`. -/
theorem dstarD_B7'_pos : 0 < dstarDQuadForm (trivialU witL7) B7' :=
  covPlaqInner_self_pos_of_ne curl_B7'_ne_zero

/-- `B7'` lies above the ZERO unit-level field at `ell = 2` (`Q₂ B7' = 0`). -/
theorem B7'_mem_unitFibre_zero :
    B7' ∈ unitFibre 2 (oneLevelUniv witL7) (trivialU witL7) 0 :=
  ⟨B7'_kerQ2, RcovLM_oneLevelUniv_eq_zero (trivialU witL7) _⟩

/-- The unit-level form at the ZERO unit field is `0` — and this is a GENUINE zero (the fibre is
nonempty, `B7'` is in it), not the `sInf ∅` artefact of `deltaKUnit_eq_zero_of_no_lift`.

**SUPERSEDED IN GENERALITY (kept: it is the form §5/§6b consume).** `deltaKUnit_zero_eq_zero` (§3c)
proves this for EVERY `ell`, `levels` and `U`, with no witness field and no projection instance,
so the `witL7`/`ell = 2`/`trivialU` scoping here is not a limitation of the fact. -/
theorem deltaKUnit_zero_witL7 :
    deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) 0 = 0 := by
  rw [deltaKUnit_eq_deltaJ_of_mem (oneLevelUniv witL7) (trivialU witL7) B7' 0
    B7'_mem_unitFibre_zero]
  exact deltaJQuadFormCovFaithful_eq_zero_of_mem_V 2 (oneLevelUniv witL7) (trivialU witL7) B7'
    (mem_gaugeConstraintSubspaceCovFaithful.mpr
      ⟨B7'_kerQ2, RcovLM_oneLevelUniv_eq_zero (trivialU witL7) _⟩)

/-- **THE MINIMISATION IS NOT A NO-OP.** `B7'` sits in the fibre above the zero unit-level field;
the unit-level form there is `0`; and `B7'`'s own fine curl energy is STRICTLY POSITIVE. So passing
from the fine field to its unit-level image removes a strictly positive amount of energy at
`ell = 2` — the level separation has quantitative content, not just a type change. -/
theorem strict_energy_removal :
    B7' ∈ unitFibre 2 (oneLevelUniv witL7) (trivialU witL7) 0
  ∧ deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) 0 = 0
  ∧ 0 < dstarDQuadForm (trivialU witL7) B7' :=
  ⟨B7'_mem_unitFibre_zero, deltaKUnit_zero_witL7, dstarD_B7'_pos⟩

/-! ### §5b — THE REMOVAL IS STRICT AT A NONZERO UNIT-LEVEL FIELD TOO

§5's witness sits above `B = 0`. Above the NONZERO `B7unit` no single lift is known to have
strictly larger energy than the minimum, and computing the cross term `⟪D B7, D B7'⟫` directly is
expensive. It is not needed: the fine energy is a strictly convex quadratic along the fibre
direction `B7'`, so it CANNOT be constant on three collinear lifts. The second-difference identity
below is exactly that convexity, and `dstarD_B7'_pos` is its strict-positivity input. -/

/-- **THE SECOND-DIFFERENCE (parallelogram) IDENTITY** for the fine curl energy along a direction
`v`: `E(A) + E(A + 2v) = 2E(A + v) + 2E(v)`. Pure bilinearity of `covPlaqInner` and linearity of the
covariant curl; general in `L`, `U`, `A`, `v`. -/
theorem energy_second_difference
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A v : Bond L → SuTwo) :
    dstarDQuadForm U A + dstarDQuadForm U (A + v + v)
      = 2 * dstarDQuadForm U (A + v) + 2 * dstarDQuadForm U v := by
  have hd : ∀ W : Bond L → SuTwo,
      dstarDQuadForm U W = covPlaqInner (curlCovariantLM U W) (curlCovariantLM U W) :=
    fun _ => rfl
  rw [hd A, hd (A + v + v), hd (A + v), hd v]
  simp only [map_add, covPlaqInner_add_left, covPlaqInner_add_right]
  rw [covPlaqInner_symm (curlCovariantLM U v) (curlCovariantLM U A)]
  ring

/-- A THIRD lift of `B7unit`, collinear with the first two: `B7 + 2·B7'`. -/
theorem B7_add_two_B7'_mem_unitFibre :
    B7 + B7' + B7' ∈ unitFibre 2 (oneLevelUniv witL7) (trivialU witL7) B7unit :=
  ⟨by rw [map_add, map_add, B7'_kerQ2, add_zero, add_zero]; rfl,
    RcovLM_oneLevelUniv_eq_zero _ _⟩

/-- **STRICT REMOVAL ABOVE A NONZERO UNIT-LEVEL FIELD.** At least one of the three named lifts of
`B7unit` has fine curl energy STRICTLY above the unit-level form. So the minimisation does real work
above `B7unit ≠ 0`, not only above `0`. Which lift is strict is NOT determined here and is not
claimed. -/
theorem removal_strict_at_B7unit :
    deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit
        < dstarDQuadForm (trivialU witL7) B7
  ∨ deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit
        < dstarDQuadForm (trivialU witL7) (B7 + B7')
  ∨ deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit
        < dstarDQuadForm (trivialU witL7) (B7 + B7' + B7') := by
  by_contra hcon
  have h0 : dstarDQuadForm (trivialU witL7) B7
      ≤ deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit :=
    not_lt.mp (fun h => hcon (Or.inl h))
  have h1 : dstarDQuadForm (trivialU witL7) (B7 + B7')
      ≤ deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit :=
    not_lt.mp (fun h => hcon (Or.inr (Or.inl h)))
  have h2 : dstarDQuadForm (trivialU witL7) (B7 + B7' + B7')
      ≤ deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit :=
    not_lt.mp (fun h => hcon (Or.inr (Or.inr h)))
  have le0 : deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit
      ≤ dstarDQuadForm (trivialU witL7) B7 :=
    deltaKUnit_le_fine_energy (oneLevelUniv witL7) (trivialU witL7) B7 B7 B7unit
      B7_mem_unitFibre B7_mem_unitFibre
  have le1 : deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit
      ≤ dstarDQuadForm (trivialU witL7) (B7 + B7') :=
    deltaKUnit_le_fine_energy (oneLevelUniv witL7) (trivialU witL7) B7 (B7 + B7') B7unit
      B7_mem_unitFibre B7_add_B7'_mem_unitFibre
  have le2 : deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7) B7unit
      ≤ dstarDQuadForm (trivialU witL7) (B7 + B7' + B7') :=
    deltaKUnit_le_fine_energy (oneLevelUniv witL7) (trivialU witL7) B7 (B7 + B7' + B7') B7unit
      B7_mem_unitFibre B7_add_two_B7'_mem_unitFibre
  have hid := energy_second_difference (trivialU witL7) B7 B7'
  have hpos := dstarD_B7'_pos
  linarith

#print axioms energy_second_difference
#print axioms B7_add_two_B7'_mem_unitFibre
#print axioms removal_strict_at_B7unit

#print axioms Q1_B7'_origin
#print axioms Q1_B7'_shifted
#print axioms coarseCurl_Q1_B7'
#print axioms stokesPhi_Q1_B7'_pos
#print axioms curl_B7'_ne_zero
#print axioms dstarD_B7'_pos
#print axioms deltaKUnit_zero_witL7
#print axioms strict_energy_removal

/-! ## §6 — COMPARISON WITH THE COLLAPSED FORM, EXACTLY

The dispatch asked for one of two answers: the unit-level form agrees with
`NormalizationAudit.deltaKQuadFormNormalizedCorrected`, or it differs and the difference is
exhibited.

~~"It differs, and the difference is an exact identity with two named terms."~~
**STRUCK AS A PROMISE OF A DECLARATION THAT DID NOT EXIST.** A prosecution pass observed correctly
that no declaration in this module stated the two forms are unequal: the headline
`collapsed_eq_deltaKUnit_add_two_terms` is an EQUALITY WITH TWO CORRECTION TERMS, and
`schurDefect_pos_witL7` proves one of those terms positive at one flat witness — neither says the
two whole forms differ. The promised declaration is now shipped, in §6b:
`deltaKUnit_lt_collapsed_at_B7'` (hence `deltaKUnit_ne_collapsed_at_B7'`), at `ell = 2` on `witL7`
at the trivial background, where `Δ′` vanishes identically and the Schur defect carries the whole
difference. §6b also ships the OPPOSITE strict inequality at a different witness, which is why the
word "exceeds" has been struck from the headline docstring below. -/

/-- **PYTHAGORAS AT THE UNIT LEVEL.** For a gauge-fixed fine field `A0`, the fine curl energy splits
exactly into the unit-level form at `A0`'s block average plus the SCHUR DEFECT — the squared norm of
the component of `D_U A0` lying in `D_U(V)`, i.e. exactly the energy the minimisation removes. -/
theorem fine_energy_eq_deltaKUnit_add_schurDefect {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    dstarDQuadForm U A0
      = deltaKUnit ell levels U (lineCoarseRestrictCovLM U ell A0)
        + covPlaqInner (curlImageCovProjFaithful ell levels U (curlCovariantLM U A0))
            (curlImageCovProjFaithful ell levels U (curlCovariantLM U A0)) := by
  rw [deltaKUnit_factors_through_Q levels U A0 h2]
  set P := curlImageCovProjFaithful ell levels U (curlCovariantLM U A0) with hP_def
  set p := hjCorrectionTargetCovFaithful ell levels U A0 with hp_def
  have hsplit : curlCovariantLM U A0 = p + P := by
    rw [hp_def, hP_def]
    unfold hjCorrectionTargetCovFaithful
    abel
  have hPmem : P ∈ curlImageCovFaithful ell levels U :=
    curlImageCovProjFaithful_mem ell levels U (curlCovariantLM U A0)
  have hPp : covPlaqInner P p = 0 :=
    hjCorrectionTargetCovFaithful_orthogonal ell levels U A0 hPmem
  have hpP : covPlaqInner p P = 0 := by rw [covPlaqInner_symm]; exact hPp
  have hdelta : deltaJQuadFormCovFaithful ell levels U A0 = covPlaqInner p p := by
    rw [hp_def]
    unfold deltaJQuadFormCovFaithful
    rw [curlCov_hjExtensionCovFaithful]
  rw [hdelta]
  change covPlaqInner (curlCovariantLM U A0) (curlCovariantLM U A0) = _
  rw [hsplit, covPlaqInner_add_left, covPlaqInner_add_right, covPlaqInner_add_right, hpP, hPp]
  ring

/-- The unit-level form never exceeds the fine curl energy of any gauge-fixed lift — the
`[CSTAR-SCHUR-GAP]` ordering, now stated with the unit-level argument.

**DO NOT GENERALISE THIS TO THE COLLAPSED FORM.** The ordering holds against `dstarDQuadForm`
because the only correction term is the nonnegative Schur defect. It is FALSE against
`deltaKQuadFormNormalizedCorrected`, which adds the sign-indefinite `Δ′` on top:
`collapsed_lt_deltaKUnit_at_deltaWitness` (§6b) exhibits `collapsed = 0 < 4 = deltaKUnit`. The two
"never exceeds" readings differ by exactly one term and exactly one of them is a theorem. -/
theorem deltaKUnit_le_dstarD {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    deltaKUnit ell levels U (lineCoarseRestrictCovLM U ell A0) ≤ dstarDQuadForm U A0 := by
  rw [fine_energy_eq_deltaKUnit_add_schurDefect (ell := ell) levels U A0 h2]
  have := covPlaqInner_self_nonneg
    (curlImageCovProjFaithful ell levels U (curlCovariantLM U A0))
  linarith

/-- **THE EXACT COMPARISON WITH THE COLLAPSED FORM.** `deltaKQuadFormNormalizedCorrected` (this
tree's source-normalized p.392 object, argument a FINE field) DECOMPOSES as the unit-level form plus
TWO named terms: the Schur defect removed by the fibre minimisation, and the `Δ′` summand, which has
no counterpart in the curl-relative Schur complement at all.

~~"…exceeds the unit-level form by TWO named terms."~~ **STRUCK: "exceeds" IS FALSE**, and this
docstring is the place the error was introduced. `⟪P,P⟫ ≥ 0` but **`Δ′` is SIGN-INDEFINITE**, so the
right-hand side is not `deltaKUnit` plus a nonnegative distance, and the identity below orders the
two forms in NEITHER direction. Both orderings are realised at legal witnesses, and both are
theorems in §6b: `deltaKUnit_lt_collapsed_at_B7'` (`deltaKUnit = 0 < collapsed`) and
`collapsed_lt_deltaKUnit_at_deltaWitness` (`collapsed = 0 < 4 = deltaKUnit`, where `Δ′` is negative
and cancels `dstarDQuadForm` entirely). Any consumer reading this identity as a one-sided gap is
reading it wrong; `no_ordering_between_collapsed_and_unit` is the statement that forbids it.

**At `ell = 0` this identity has NO unit-level content**: `deltaKUnit 0 levels U (Q_0 A0) = 0` for
arbitrary `A0` and `U` (§3d), so it degenerates to `collapsed = ⟪P,P⟫ + Δ′` — see
`collapsed_ell0_carries_no_unit_content` immediately below.

This is what the denotation-dictionary `MISMATCH` costs, as an identity rather than a narrative. -/
theorem collapsed_eq_deltaKUnit_add_two_terms {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected U A0
      = deltaKUnit ell levels U (lineCoarseRestrictCovLM U ell A0)
        + covPlaqInner (curlImageCovProjFaithful ell levels U (curlCovariantLM U A0))
            (curlImageCovProjFaithful ell levels U (curlCovariantLM U A0))
        + AdalyFormal.Balaban.NormalizationAudit.deltaPrimeQuadFormNormalizedTransported U A0 := by
  unfold AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
  rw [fine_energy_eq_deltaKUnit_add_schurDefect (ell := ell) levels U A0 h2]

/-- **AT `ell = 0` THE HEADLINE CARRIES NO UNIT-LEVEL CONTENT.** `Q_0 ≡ 0` (§3d), so the unit term
of the identity above is `0` for ARBITRARY `A0` and ARBITRARY `U`, and the identity degenerates into
a statement about the fine level alone: `collapsed = ⟪P,P⟫ + Δ′`. This is the collapse a
de-correlated prosecution pass compiled and convicted as undisclosed; it is now a theorem, so the
headline can no longer be read as measuring anything at block side `0`. -/
theorem collapsed_ell0_carries_no_unit_content
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 0 levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    deltaKUnit 0 levels U (lineCoarseRestrictCovLM U 0 A0) = 0
  ∧ AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected U A0
      = covPlaqInner (curlImageCovProjFaithful 0 levels U (curlCovariantLM U A0))
          (curlImageCovProjFaithful 0 levels U (curlCovariantLM U A0))
        + AdalyFormal.Balaban.NormalizationAudit.deltaPrimeQuadFormNormalizedTransported U A0 := by
  refine ⟨deltaKUnit_ell0_eq_zero levels U _, ?_⟩
  rw [collapsed_eq_deltaKUnit_add_two_terms (ell := 0) levels U A0 h2,
    deltaKUnit_ell0_eq_zero levels U _, zero_add]

/-- **AT `ell = 1` THE DISTINCTION IS INVISIBLE.** The unit-level form collapses EXACTLY onto
`dstarDQuadForm` — `V = ⊥`, the Schur defect is `0`, and the level separation has no content. This
is why §4 and §5 are stated at `ell = 2` and why a witness at `ell = 1` would prove nothing about
the repair (the class-5 degenerate-test-point failure mode). -/
theorem deltaKUnit_ell1_eq_dstarD (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    deltaKUnit 1 levels U (lineCoarseRestrictCovLM U 1 A0) = dstarDQuadForm U A0 := by
  rw [deltaKUnit_factors_through_Q levels U A0 h2]
  exact deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm levels U A0

/-- **THE SCHUR DEFECT IS STRICTLY POSITIVE AT `ell = 2`** — so §6's identity is not an identity
between equal things. At `B7'`: the unit-level form is `0`, the fine energy is `> 0`, hence the
defect term carries all of it. -/
theorem schurDefect_pos_witL7 :
    0 < covPlaqInner
        (curlImageCovProjFaithful 2 (oneLevelUniv witL7) (trivialU witL7)
          (curlCovariantLM (trivialU witL7) B7'))
        (curlImageCovProjFaithful 2 (oneLevelUniv witL7) (trivialU witL7)
          (curlCovariantLM (trivialU witL7) B7')) := by
  have hid := fine_energy_eq_deltaKUnit_add_schurDefect (ell := 2) (oneLevelUniv witL7)
    (trivialU witL7) B7' (RcovLM_oneLevelUniv_eq_zero (trivialU witL7) _)
  rw [show lineCoarseRestrictCovLM (trivialU witL7) 2 B7' = 0 from B7'_kerQ2,
    deltaKUnit_zero_witL7] at hid
  have := dstarD_B7'_pos
  linarith

#print axioms fine_energy_eq_deltaKUnit_add_schurDefect
#print axioms deltaKUnit_le_dstarD
#print axioms collapsed_eq_deltaKUnit_add_two_terms
#print axioms collapsed_ell0_carries_no_unit_content
#print axioms deltaKUnit_ell1_eq_dstarD
#print axioms schurDefect_pos_witL7

/-! ## §6b — THE TWO FORMS GENUINELY DIFFER, AND NEITHER DOMINATES THE OTHER

§6 promised a declaration saying the two forms differ and did not ship one. It ships here — and the
same two witnesses kill the word "exceeds" at the same time, because they order the two forms in
OPPOSITE directions.

* At `ell = 2`, `witL7`, `U = trivialU`, `A0 = B7'`: `Δ′` vanishes identically at the trivial
  background, `Q₂ B7' = 0`, `deltaKUnit … 0 = 0`, and the Schur defect is strictly positive
  (`schurDefect_pos_witL7`). Hence `deltaKUnit = 0 < collapsed`. This is the DIFFERENCE theorem.
* At `ell = 1`, `witnessL`, `U = witnessU`, `A0 = deltaWitnessConfig`: the collapsed normalized form
  is exactly `0` (`NormalizationAudit`'s headline) while `deltaKUnit` collapses onto
  `dstarDQuadForm = 4` (§6's `ell = 1` theorem). Hence `collapsed = 0 < 4 = deltaKUnit`: the
  collapsed form is STRICTLY SMALLER. The `Δ′` term is `−4` there and cancels `D*D` entirely.

Both are legal instances of the headline's hypotheses (`h2` holds by `RcovLM_oneLevelUniv_eq_zero`),
so no ordering claim about `collapsed` versus `deltaKUnit` can be made from the headline identity —
only the decomposition itself. -/

/-- `Δ′` (consistently normalized, transported) vanishes IDENTICALLY at the trivial background, for
EVERY fine field: `DeltaPrime.deltaPrimeQuadFormTransported_vanishes_at_trivial` carried through
`NormalizationAudit.deltaPrimeQuadFormNormalizedTransported_eq_half_transported` (both reused —
LAW-19). The tree carries two `trivialU` declarations, `DeltaPrime.trivialU` and
`CovariantHjMinimizer.trivialU`; both are `fun _ => 1` and the unification below is definitional. -/
theorem deltaPrimeNormalizedTransported_trivialU_eq_zero (A : Bond L → SuTwo) :
    AdalyFormal.Balaban.NormalizationAudit.deltaPrimeQuadFormNormalizedTransported
        (trivialU L) A = 0 := by
  have h : deltaPrimeQuadFormTransported (trivialU L) A = 0 :=
    deltaPrimeQuadFormTransported_vanishes_at_trivial A
  rw [deltaPrimeQuadFormNormalizedTransported_eq_half_transported, h]
  ring

/-- **THE DIFFERENCE THEOREM — the declaration §6 promised and did not ship.** At `ell = 2` on
`witL7` at the trivial background the unit-level form and the collapsed normalized form are NOT
equal: the unit-level form is `0` and the collapsed form is the (strictly positive) Schur defect. -/
theorem deltaKUnit_lt_collapsed_at_B7' :
    deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7)
        (lineCoarseRestrictCovLM (trivialU witL7) 2 B7')
      < AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
          (trivialU witL7) B7' := by
  have hid := collapsed_eq_deltaKUnit_add_two_terms (ell := 2) (oneLevelUniv witL7)
    (trivialU witL7) B7' (RcovLM_oneLevelUniv_eq_zero (trivialU witL7) _)
  rw [deltaPrimeNormalizedTransported_trivialU_eq_zero,
    show lineCoarseRestrictCovLM (trivialU witL7) 2 B7' = 0 from B7'_kerQ2,
    deltaKUnit_zero_witL7, zero_add, add_zero] at hid
  rw [show lineCoarseRestrictCovLM (trivialU witL7) 2 B7' = 0 from B7'_kerQ2,
    deltaKUnit_zero_witL7, hid]
  exact schurDefect_pos_witL7

theorem deltaKUnit_ne_collapsed_at_B7' :
    deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7)
        (lineCoarseRestrictCovLM (trivialU witL7) 2 B7')
      ≠ AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
          (trivialU witL7) B7' :=
  ne_of_lt deltaKUnit_lt_collapsed_at_B7'

/-- **"EXCEEDS" IS FALSE, PROVED.** At a legal instance of the headline's hypotheses the COLLAPSED
form is STRICTLY SMALLER than the unit-level form: `0 < 4`. The `Δ′` summand is `−4` here
(`NormalizationAudit`'s own computation) and cancels the whole of `dstarDQuadForm`, so the two
"correction terms" of the headline identity are not a nonnegative distance in any sense. -/
theorem collapsed_lt_deltaKUnit_at_deltaWitness :
    AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
        witnessU deltaWitnessConfig
      < deltaKUnit 1 (oneLevelUniv AdmissibleSubspace.witnessL) witnessU
          (lineCoarseRestrictCovLM witnessU 1
            deltaWitnessConfig) := by
  rw [deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero,
    deltaKUnit_ell1_eq_dstarD (oneLevelUniv AdmissibleSubspace.witnessL) witnessU
      deltaWitnessConfig
      (RcovLM_oneLevelUniv_eq_zero witnessU _),
    dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four]
  norm_num

/-- **§6b ASSEMBLED — NEITHER FORM DOMINATES THE OTHER.** Two strict inequalities, at two legal
witnesses, pointing in OPPOSITE directions. This is the statement that forbids reading
`collapsed_eq_deltaKUnit_add_two_terms` as a gap, in either direction, and it is the reason the word
"exceeds" is struck from that theorem's docstring. -/
theorem no_ordering_between_collapsed_and_unit :
    deltaKUnit 2 (oneLevelUniv witL7) (trivialU witL7)
        (lineCoarseRestrictCovLM (trivialU witL7) 2 B7')
      < AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
          (trivialU witL7) B7'
  ∧ AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
        witnessU deltaWitnessConfig
      < deltaKUnit 1 (oneLevelUniv AdmissibleSubspace.witnessL) witnessU
          (lineCoarseRestrictCovLM witnessU 1
            deltaWitnessConfig) :=
  ⟨deltaKUnit_lt_collapsed_at_B7', collapsed_lt_deltaKUnit_at_deltaWitness⟩

#print axioms deltaPrimeNormalizedTransported_trivialU_eq_zero
#print axioms deltaKUnit_lt_collapsed_at_B7'
#print axioms deltaKUnit_ne_collapsed_at_B7'
#print axioms collapsed_lt_deltaKUnit_at_deltaWitness
#print axioms no_ordering_between_collapsed_and_unit

/-! ## §7 — THE UNIT-LEVEL FORM IS GENUINELY BACKGROUND-DEPENDENT, AT FIXED UNIT DATA

A form that turned out to be secretly `U`-independent would be a defect, so this is checked and not
assumed. At `ell = 1` the faithful block average is the IDENTITY for every background
(`RegularUGamma0.lineCoarseRestrictCov_one_eq_self` — the `ell = 1` transport path is empty, so its
holonomy is `1`), hence ONE AND THE SAME unit-level field is the image of `myWitnessConfig` under
both backgrounds, and the form still takes two different values. This is a SAME-`B` statement, not
the weaker "two different arguments give two different values".

**READ THIS BEFORE CITING §7.** The witness sits at `ell = 1`, which §6 proves is the DEGENERATE
level: there `V = ⊥` and `deltaKUnit` collapses onto `dstarDQuadForm` exactly, so the Schur
mechanism is not exercised at all. What §7 establishes is therefore precisely this and no more:
**the unit-level form is not `U`-blind.** It does NOT show that the MINIMISATION is `U`-dependent —
that would need a witness at `ell ≥ 2`, and none is given here. The two facts are complementary:
§4/§5/§5b exercise the Schur mechanism at `ell = 2` but at one fixed background; §7 moves the
background but at the degenerate level.

Placed after §6 because it consumes `deltaKUnit_ell1_eq_dstarD`. -/

/-- The unit-level field `Q_1 myWitnessConfig` — the same field for every background at
`ell = 1`. -/
noncomputable def witnessUnitB : CoarseBond AdmissibleSubspace.witnessL 1 → SuTwo :=
  lineCoarseRestrictCovLM myTrivialU 1 myWitnessConfig

theorem witnessUnitB_eq_under_witnessU :
    lineCoarseRestrictCovLM witnessU 1 myWitnessConfig = witnessUnitB := by
  funext c
  rw [lineCoarseRestrictCovLM_apply,
    AdalyFormal.Balaban.RegularUGamma0.lineCoarseRestrictCov_one_eq_self]
  change _ = lineCoarseRestrictCovLM myTrivialU 1 myWitnessConfig c
  rw [lineCoarseRestrictCovLM_apply,
    AdalyFormal.Balaban.RegularUGamma0.lineCoarseRestrictCov_one_eq_self]

/-- **THE UNIT-LEVEL FORM IS GENUINELY `U`-DEPENDENT.** Same unit-level field `witnessUnitB`, two
backgrounds, two different values — transferred from `dstarDQuadForm_genuinely_U_dependent` (`0` vs
`4`) through the `ell = 1` collapse. -/
theorem deltaKUnit_genuinely_U_dependent :
    deltaKUnit 1 (oneLevelUniv AdmissibleSubspace.witnessL) myTrivialU witnessUnitB
      ≠ deltaKUnit 1 (oneLevelUniv AdmissibleSubspace.witnessL) witnessU witnessUnitB := by
  have h1 : deltaKUnit 1 (oneLevelUniv AdmissibleSubspace.witnessL) myTrivialU witnessUnitB
      = dstarDQuadForm myTrivialU myWitnessConfig :=
    deltaKUnit_ell1_eq_dstarD (oneLevelUniv AdmissibleSubspace.witnessL) myTrivialU
      myWitnessConfig (RcovLM_oneLevelUniv_eq_zero myTrivialU _)
  have h2 : deltaKUnit 1 (oneLevelUniv AdmissibleSubspace.witnessL) witnessU witnessUnitB
      = dstarDQuadForm witnessU myWitnessConfig := by
    rw [← witnessUnitB_eq_under_witnessU]
    exact deltaKUnit_ell1_eq_dstarD (oneLevelUniv AdmissibleSubspace.witnessL) witnessU
      myWitnessConfig (RcovLM_oneLevelUniv_eq_zero witnessU _)
  rw [h1, h2]
  exact dstarDQuadForm_genuinely_U_dependent

#print axioms witnessUnitB_eq_under_witnessU
#print axioms deltaKUnit_genuinely_U_dependent

/-! ## §7b — A CONCRETE FIBRE THAT IS NONEMPTY AT **EVERY** `levels`, LIVE `R` INCLUDED

§3e proved the live-`R` monotonicity/persistence statements but left their hypothesis
undischarged, and the first draft of this repair recorded "no concrete live-`R` nonempty fibre is
exhibited" as open. **It is not open; it is discharged here**, and the object needed was already in
the tree.

`NilLevelTarget.loopField m` — the four-bond loop around one plaquette of `wExt m` — is
DIVERGENCE-FREE at the trivial background: `gradCovariantAdjointLM (trivialU (wExt m))
(loopField m) = 0` (`NilLevelTarget.loopField_div_eq_zero`, reused — LAW-19). Since
`RcovLM U levels` is linear, it annihilates `0` for **every** `levels` whatsoever. Hence the loop
lies in the fibre above its own unit shadow at every block side and every `levels` — no matter how
live `R` is — and `deltaKUnit_eq_zero_of_no_lift`'s emptiness branch is ruled out there
unconditionally.

At `ell = 1` the value is then pinned exactly, and is STRICTLY POSITIVE at every `levels`, because
`TransverseClass.loopField_dstarD_pos` gives `0 < dstarDQuadForm (trivialU (wExt m)) (loopField m)`
(reused — LAW-19).

**What this does and does not settle, stated exactly.** It settles that positivity of the unit-level
form CAN survive an arbitrary `levels` — the struck prose's conclusion is realised at a concrete,
named field, with no hypothesis left dangling. It does NOT settle §4's own witness: `ell = 1` is the
degenerate block side (`deltaKUnit_ell1_eq_dstarD`), and whether
`0 < deltaKUnit 2 levels (trivialU witL7) B7unit` at a live `levels` is still not known, because
nothing here shows `B7` has a divergence-free representative in its fibre.
`deltaKUnit_loopField_pos_of_oneLevelUniv_pos` reduces the `ell ≥ 2` question for the LOOP to a
single `oneLevelUniv` positivity fact, with the emptiness branch already eliminated. -/

/-- **THE LOOP LIES IN THE FIBRE AT EVERY `levels` AND EVERY BLOCK SIDE.** The gauge clause is
discharged by linearity from `loopField_div_eq_zero`, so `levels` is completely unconstrained —
this is the concrete live-`R` fibre member §3e's hypothesis asks for. -/
theorem loopField_mem_unitFibre (m ell : ℕ)
    (levels : List (KernelSubspace.Level (AdalyFormal.Balaban.WitnessInequality.wExt m))) :
    AdalyFormal.Balaban.NilLevelTarget.loopField m
      ∈ unitFibre ell levels (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
          (lineCoarseRestrictCovLM (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m)) ell
            (AdalyFormal.Balaban.NilLevelTarget.loopField m)) :=
  ⟨rfl, by rw [AdalyFormal.Balaban.NilLevelTarget.loopField_div_eq_zero, map_zero]⟩

/-- At the degenerate block side the value is pinned exactly, for EVERY `levels`. -/
theorem deltaKUnit_loopField_ell1_eq_dstarD (m : ℕ)
    (levels : List (KernelSubspace.Level (AdalyFormal.Balaban.WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
      levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels
      (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))).HasOrthogonalProjection] :
    deltaKUnit 1 levels (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
        (lineCoarseRestrictCovLM (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m)) 1
          (AdalyFormal.Balaban.NilLevelTarget.loopField m))
      = dstarDQuadForm (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
          (AdalyFormal.Balaban.NilLevelTarget.loopField m) :=
  deltaKUnit_ell1_eq_dstarD levels (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
    (AdalyFormal.Balaban.NilLevelTarget.loopField m)
    (by rw [AdalyFormal.Balaban.NilLevelTarget.loopField_div_eq_zero, map_zero])

/-- **POSITIVITY OF THE UNIT-LEVEL FORM AT EVERY `levels`, LIVE `R` INCLUDED.** A concrete named
unit-level field whose form value is strictly positive no matter which `levels` (hence which `R`) is
imposed. At the degenerate block side `ell = 1`; see the section docstring for what is and is not
settled by this. -/
theorem deltaKUnit_loopField_pos_at_every_levels (m : ℕ)
    (levels : List (KernelSubspace.Level (AdalyFormal.Balaban.WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
      levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels
      (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))).HasOrthogonalProjection] :
    0 < deltaKUnit 1 levels (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
      (lineCoarseRestrictCovLM (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m)) 1
        (AdalyFormal.Balaban.NilLevelTarget.loopField m)) := by
  rw [deltaKUnit_loopField_ell1_eq_dstarD m levels]
  exact AdalyFormal.Balaban.TransverseClass.loopField_dstarD_pos m

/-- **THE `ell ≥ 2` QUESTION FOR THE LOOP, REDUCED.** Because the fibre is nonempty at every
`levels`, the emptiness branch of `deltaKUnit_pos_or_unitFibre_empty` is eliminated at the loop, and
live-`R` positivity at ANY block side follows from the single `oneLevelUniv` fact. -/
theorem deltaKUnit_loopField_pos_of_oneLevelUniv_pos (m ell : ℕ)
    (levels : List (KernelSubspace.Level (AdalyFormal.Balaban.WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
      (oneLevelUniv (AdalyFormal.Balaban.WitnessInequality.wExt m))).HasOrthogonalProjection]
    (hpos : 0 < deltaKUnit ell (oneLevelUniv (AdalyFormal.Balaban.WitnessInequality.wExt m))
      (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
      (lineCoarseRestrictCovLM (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m)) ell
        (AdalyFormal.Balaban.NilLevelTarget.loopField m))) :
    0 < deltaKUnit ell levels (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
      (lineCoarseRestrictCovLM (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m)) ell
        (AdalyFormal.Balaban.NilLevelTarget.loopField m)) :=
  deltaKUnit_pos_of_pos_oneLevelUniv levels
    (trivialU (AdalyFormal.Balaban.WitnessInequality.wExt m))
    (loopField_mem_unitFibre m ell levels) hpos

#print axioms loopField_mem_unitFibre
#print axioms deltaKUnit_loopField_ell1_eq_dstarD
#print axioms deltaKUnit_loopField_pos_at_every_levels
#print axioms deltaKUnit_loopField_pos_of_oneLevelUniv_pos

/-! ## §8 — AXIOM CHECK ON EVERY REMAINING DECLARATION

The sections above check each theorem as it lands. This block covers the `def`s and the auxiliary
lemmas that did not carry their own check, so that EVERY declaration in the module — 102 of them
after the 2026-07-30 prosecution repair (was 62) — has a `#print axioms` report. Expected
everywhere: `[propext, Classical.choice, Quot.sound]`, with the single exception `witL7_one_dvd`,
which reports the strictly smaller `[propext]`. -/

#print axioms unitFibre
#print axioms deltaKUnit
#print axioms gaugeFixedFine
#print axioms liftableUnitFields
#print axioms unitLift
#print axioms unitLiftOne
#print axioms B7unit
#print axioms witnessUnitB
#print axioms B7_add_B7'_mem_unitFibre
#print axioms B7_ne_B7_add_B7'
#print axioms witL7_one_dvd
#print axioms y70_coarse1
#print axioms y70_shift0_coarse1
#print axioms y70_shift1_coarse1
#print axioms B7'_mem_unitFibre_zero

end AdalyFormal.Balaban.DeltaKUnitLevel
