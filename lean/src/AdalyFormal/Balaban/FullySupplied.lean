/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.QcEquation
import AdalyFormal.Balaban.FullReparamC

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-!
# `FullySupplied.lean` — Claim 18's bundle with EVERY operator supplied, and the resulting decision

## The diagnosis this module acts on

Two repairs of the claim-18 bundle have failed the same way, and the second one proved why.

1. `Claim18Carrier.Clauses` quantifies existentially over `(C⁽²⁾, 𝒬_c, 𝒬_c⁻¹)` and is satisfiable by
   pure linear algebra at every carrier pair with a dimension drop
   (`compute/claim18_carrier/carrier_attacks.lean`).
2. `QcEquation.SuppliedClauses` pins `𝒬_c` and `𝒬_c⁻¹` to the real lattice operators, and the bundle
   STILL lands (`compute/qc_equation/qc_attacks.lean`), because `QcEquation.suppliedClauses_iff`
   proves the surviving content is three conditions on `C⁽²⁾` ALONE — one of them an UPPER bound on a
   composition, which a free factor can always meet by shrinking.

So the vacuity did not go away, it MOVED to whichever operator was left free. This module removes the
last one: `C⁽²⁾` is supplied as Bałaban's actual (3.157) reparametrization.

## THE TYPE MISMATCH, WRITTEN OUT (task item 1)

`FullReparamC.fullCLM U ell Dinv : (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo)` — the real `C`, acting on
**su(2)-valued** bond fields. `QcEquation.SuppliedClauses` wants
`C2 : BondSpace L →L[ℝ] BondSpace L` with `BondSpace L = EuclideanSpace ℝ (Bond L)`
(`LatticeOperators.lean:244`) — the **ℝ-valued** bond space, of ℝ-dimension `|Bond L|`, whereas
`Bond L → SuTwo` has ℝ-dimension `3·|Bond L|`.

**No wrapper onto `BondSpace L` exists**, and none is built here: an ℝ-linear map cannot conjugate
`fullC` into an operator on a space of one third the dimension without discarding two of the three
su(2) components, which is exactly the "convenient look-alike" substitution that must not happen.
The resolution is the other direction — state the bundle at the carrier the real `C` lives on, where
`𝒬_c` also exists as a real object:

| slot | supplied object | provenance |
|---|---|---|
| `Hfine` | `FineField L` = `Bond L → 𝔰𝔲(2)` | pinned in §1, one normed structure (Pi/sup); see §1 for the two MEASURED reasons the bare function type cannot be used |
| `Hcoarse` | `CoarseField L ell` = `CoarseBond L ell → 𝔰𝔲(2)` | pinned in §1 |
| `C⁽²⁾` | `cTwoCLM U ell` = `FullReparamC.fullC U ell (FullReparamC.dinvC U ell)` | the real (3.157) `C` with the real EXPLICIT inverse — **no `Dinv` parameter and no `hinv` hypothesis survive**; `FullReparamC.dinvC_hinv` discharges it unconditionally |
| `𝒬_c` | `qcCLM U ell` = `LineIntegralCovariant.lineCoarseRestrictCov U ell` | the faithful covariant `Q_k(U)`, CMP95 (1.18)/CMP98 (125), line integral intact |
| `𝒬_c⁻¹` | `suTwoLiftCLM L ell` = `suTwoLift` (§2) | `QcEquation.lastLayerLift` on the su(2) fibre; agreement with the scalar object PROVED (`suTwoLift_scalar`), not asserted |

There is **no existential over any operator** in `FullySuppliedClauses` (§6), and **no new constant**:
the remaining arguments are the background field `U` (data of the model, not an operator) and Claim 18's
own four constants `Lreal, d, Ccorr, α₀`.

## THE ANSWER: the bundle is FALSE at the faithful parameters, and the failure is ISOLATED to
## CLAUSE 5 — Bałaban's own transfer constant — by exactly one power of `ell`

At the trivial background, §5 and §7 compute the transfer operator `D̃⁽²⁾ = C⁽²⁾ ∘ 𝒬_c⁻¹` **exactly**:

* `fullC_suTwoLift_at_dropped` : `(C⁽²⁾(𝒬_c⁻¹F))(droppedBondLast ell c) = −(ell³ − ell) • F c`
* `opNorm_transfer_eq` : `‖C⁽²⁾ ∘L 𝒬_c⁻¹‖ = ell³ − ell` — an **EQUALITY**, at `2 ≤ ell` on a tiled
  extent, so the comparison with clause 5 is a measurement and not an estimate.

Clause 5 demands `‖D̃⁽²⁾‖ ≤ Lreal^(d−1)`. Every OTHER clause is a theorem about the supplied operators:

| clause | statement | where |
|---|---|---|
| 1 | `𝒬_c ∘L 𝒬_c⁻¹ = id` | `qc_comp_suTwoLift` (§3) |
| 2 | `Injective 𝒬_c⁻¹` | `suTwoLift_injective` (§9) |
| 3 | `‖𝒬_c‖ ≤ 1 ≤ 1 + Ccorr·Lreal²·α₀` | `opNorm_qc_le_one`, `qc_clause3` (§9) |
| 4a | `1 ≤ ‖C⁽²⁾‖` — **at EVERY `U`** | `one_le_opNorm_cTwo` (§9) |
| 4b | `¬ Injective 𝒬_c` | `qc_not_injective` (§9) |
| 5 | `‖C⁽²⁾ ∘L 𝒬_c⁻¹‖ ≤ Lreal^(d−1)` | **THIS IS THE ONE THAT FAILS** |
| 6 | `C⁽²⁾ ∘L 𝒬_c⁻¹ ≠ 0` | `transfer_ne_zero` (§9) |

So §10 is an **IFF**, not a claim:
`FullySuppliedClauses L ell (trivialU L) Lreal d Ccorr α₀ ↔ ell³ − ell ≤ Lreal^(d−1)`
(`fullySupplied_iff`, at `2 ≤ ell`, tiled, `0 ≤ Ccorr`, `0 ≤ α₀`).

At Bałaban's own identification `Lreal = ell` (his `L` IS the block side) and the dimension of this
tree's lattice `d = 3`, clause 5 reads `‖D̃⁽²⁾‖ ≤ ell²`, and `ell² < ell³ − ell` for every `2 ≤ ell`:
**FALSE** (`fullySupplied_false_at_faithful_scale`), concretely `6 > 4` on the `4³` torus at `ell = 2`
(`fullySupplied_false_at_witness_lattice`). By the IFF the bundle becomes TRUE at `d = 4` with
`Lreal = ell` (`ell³ − ell ≤ ell³`), so the failing quantity is the EXPONENT in clause 5 and not the
operators: both operators are the source's, both are non-degenerate, and five of six clauses hold.

**Where the `ell³` comes from, counted:** `𝒬_c`'s normalization is `1/ell⁴` over `ell³` block sites ×
`ell` bonds per segment, so the diagonal coefficient of the (3.157) equation at the dropped bond is
`ell⁻³` (`FullReparamC.coeffDc_general_op`, general in `U`) and its inverse is `ell³`
(`FullReparamC.dinvC`). The section's weight is `ell` (`QcEquation`'s own computation of the unique
exact right inverse). `ell³ · (1 − ell⁻²) = ell³ − ell`. No constant here is chosen.

## THE ONE BIT THE VERDICT HINGES ON — `d` — STATED UP FRONT, NOT BURIED

By `fullySupplied_iff` the bundle is TRUE exactly when `ell³ − ell ≤ Lreal^(d−1)`. With Bałaban's own
scale identification `Lreal = ell` that is `ell³ − ell ≤ ell^(d−1)`, so:

* `d = 3` → bound `ell²` → **FALSE** for every `2 ≤ ell` (`fullySupplied_false_at_faithful_scale`);
* `d = 4` → bound `ell³` → **TRUE** for every `ell` (compiled OUTSIDE the package,
  `compute/fully_supplied/fs_attacks.lean`'s `fullySupplied_lands_at_d_four`);
* `d ≤ 2` → bound `≤ ell` → FALSE, more strongly.

So the entire decision is one integer. What this tree fixes and what it leaves free, measured rather
than assumed:

* `Spine.claim18_exists` binds `(d : ℕ)` with **NO hypothesis** — `d` is free there.
* The lattice of this tree has **three** directions: `PeriodicLatticeSite L = ∀ μ : Fin 3, …`.
* This tree's own `𝒬_c` normalization is `1/ell⁴`, and `LineIntegralAveraging.lean` §2's docstring
  derives that as `η^{d+1}` with **`d = 3`** — i.e. the operator supplied here was built at `d = 3`.

Those three facts are why the faithful instantiation used above is `d = 3`. They are NOT a proof that
Claim 18's own `d` is 3 rather than the physical spacetime dimension 4, and this module does not claim
it: the `d = 4` reading is compiled too, and it LANDS. What is established without any convention
choice is the equality `‖C⁽²⁾ ∘L 𝒬_c⁻¹‖ = ell³ − ell`; which side of clause 5 that falls on is a
question about `d`, and it is now a question with a one-line answer either way.

## SCOPE, stated rather than implied

**The domain of `Lreal` and `d` in `fullySupplied_iff` is WIDER than its physical justification.**
`Lreal : ℝ` and `d : ℕ` carry no positivity or minimality hypothesis, and clause 5's bound is
`Real.rpow Lreal ((d:ℝ) - 1)`, whose value at `Lreal ≤ 0` is the principal-branch one and carries no
physical meaning as an operator-norm bound. Every instantiation used here takes
`Lreal = (ell : ℝ) ≥ 2 > 0` and `d ∈ {3, 4}`, so no result below is exercised outside that range; the
`iff` is nonetheless stated at the wider domain, and a future consumer that reuses it at an unchecked
`Lreal` would be relying on a comparison of `ell³ − ell` against a quantity that is not a bound.
Flagged here rather than left for a reader to notice.


The `‖·‖` computations are at `U = trivialU`. That is not a convenience: it is the background at which
the PINNED section is an exact right inverse of the covariant average, i.e. the background at which
clause 1 holds and the bundle has its best case. At a general `U` the flat last-layer lift is not a
section of `lineCoarseRestrictCov U ell` (the per-`x` holonomies in `rZeroA` do not cancel), so a
general-`U` version of §10 would need a covariantly transported section. §5a records the general-`U`
closed form of the transfer value, which shows the `ell³` amplification is a fact about `dinvC` and is
not special to `U = 1`; what §10 needs at general `U` is only the section equation.

**Why a single-valued covariant section does not simply exist — read off the definitions, not
guessed.** `Q1Real.rZeroA` applies `RMap (periodicPathHolonomy U y (transportPath y x μ i))` to the
bond value at `(pathSite x μ i, μ)`, and
`transportPath y x μ i = GammaPath y x ++ straightSegment x (pathSite x μ i) μ`
(`Q1Real.lean:382`), with `GammaPath y x` ordered direction `2`, then `1`, then `0`
(`Q1Real.lean:307-310`). Exactly `ell` pairs `(x,i)` reach one last-layer bond — those with `x` at
`μ`-offset `j` and `i = ell − 1 − j` — so a covariant section would have to put ONE value there that
cancels `ell` holonomies at once. Concatenating gives:

* `μ = 0`: `[2-steps] ++ [1-steps] ++ [0^j] ++ [0^i]` = `[2] ++ [1] ++ [0^{ell−1}]`, **the same path
  for every `j`** — the `μ`-steps are last in `GammaPath`'s order, so they merge.
* `μ = 1`: `[2] ++ [1^j] ++ [0] ++ [1^i]` — the extra `μ`-steps land AFTER the transverse steps, so
  the path genuinely depends on `j`; likewise `μ = 2`.

So for `μ ≠ 0` the `ell` holonomies differ, and they differ by commutators of the transverse staircase
with the `μ`-segment — i.e. by CURVATURE. That is the same obstruction
`LineIntegralCovariant.lean` §4 already names for the general-`U` (1.20) intertwining
(`CovariantOperators.witness_curvature_ne_zero`, `d² ≠ 0`, holding only up to center-flat). This
paragraph is a reading of the cited definitions, checkable line by line; it is NOT a theorem of this
module and is not used by anything here.

## What is deliberately NOT here

No positive inhabitation of anything `Spine.lean` consumes. Per `Spine.lean` §3b.1's standing
doctrine the landing witnesses of a REPAIRED statement live outside the package; here the headline is
a NEGATION (`fullySupplied_false`), which is safe inside the package, and the one positive statement
(`fullySupplied_iff`'s `mpr` direction, and §7's clause theorems) is about the SUPPLIED operators, so
it cannot be used to discharge an existential over operators — there is no existential.
-/

namespace AdalyFormal.Balaban.FullySupplied

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators (CoarseBond gradValue)
open AdalyFormal.Balaban.CovariantOperators
  (SuTwo RMap RMap_one RMap_mul_apply suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.Q1Real (periodicPathHolonomy_trivialU_eq_one)
open AdalyFormal.Balaban.LineIntegralAveraging (lineIntegralValue lineCoarseRestrict)
open AdalyFormal.Balaban.LineIntegralCovariant
  (lineCoarseRestrictCov lineCoarseRestrictCovLM lineCoarseRestrictSuTwo
   lineCoarseRestrictCov_trivialU lineCoarseRestrictSuTwo_smul_fixed
   lineCoarseRestrictCov_add lineCoarseRestrictCov_smul)
open AdalyFormal.Balaban.QcEquation
  (lastLayerLift blockCorner blockCorner_val blockCorner_mem blockCorner_of_mem_blockOf
   kerLam lineCoarseRestrict_gradValue_kerLam gradValue_kerLam_origin originSite originCoarseBond
   lineCoarseRestrict_lastLayerLift)
open AdalyFormal.Balaban.ReparamCDisjoint
  (droppedBondLast pathSite_apply_ne pathSite_apply_self_val coarse_coord_add_ell_le)
open AdalyFormal.Balaban.ReparamCSuTwo
  (constraintFunctional constraintFunctional_apply dropZero coeffDc coeffDc_apply restFunctional)
open AdalyFormal.Balaban.FullReparamC
  (IsDropped fullC fullCLM fullC_free fullC_dropped fullC_add fullC_smul solvedValue dinvC
   coeffDc_general_op dropTransport coarseBond_base_not_dropped originSite_coarse)
open ContinuousLinearMap

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the two su(2) carriers, PINNED as `def` synonyms with exactly one normed structure each

This is not cosmetic packaging; both halves are MEASURED obstructions to stating the bundle at the
bare function types, and the measurements are in this lane's own probe logs.

1. **Two competing `NormedAddCommGroup ↥SuTwo` instances are in scope.**
   `compute/fully_supplied/probe1.log`: with this module's imports, `#synth NormedAddCommGroup ↥SuTwo`
   returns `SuTwoInner.instNormedAddCommGroupSuTwo` (the `hsInner`-sourced norm), while
   `#synth NormedAddCommGroup (Bond L → ↥SuTwo)` returns
   `CovariantOperators.instNormedAddCommGroupBondFn`, which was baked with the OTHER fibre norm
   (`Submodule.normedAddCommGroup`). Consequence, measured in the same log: `norm_le_pi_norm F b`
   does not typecheck at `Bond L → ↥SuTwo` — `‖F b‖` and `‖F‖` are norms of different structures.
   `formal/AdalyFormal/SUTWO_DIAMOND.md` records the diamond and explicitly rules the Bond-level
   composite instances out of scope for its repair, so this is a known, documented gap.
2. **`Pi.topologicalSpace` outranks the normed-derived topology on a bare function type**, so
   `A →L[ℝ] B` written at `Bond L → ↥SuTwo` elaborates with `Pi.topologicalSpace`/`Pi.addCommMonoid`
   and `Norm (A →L[ℝ] B)` is then UNSYNTHESIZABLE (`compute/fully_supplied/probe3.log`). Clause 3 and
   clause 5 are statements about `‖·‖` of operators, so at the bare type they cannot be stated at all.

On a `def` synonym neither problem arises: `Pi.*` instances no longer apply by unification, the four
instances below are the only ones, and the topology/module structure the `→L` notation finds is
necessarily the one the norms come from.

**PRECISE STATE OF THAT PROBE, corrected by this lane's own nested validator (do not read it as
"all green"):** `compute/fully_supplied/probe4.log` contains **one error**, out of nine `example`
blocks in `compute/fully_supplied/probe_instances4.lean`. The eight that pass are the load-bearing
ones — pointwise norm access on both pinned carriers (`norm_le_pi_norm`, `pi_norm_le_iff_of_nonneg`),
the rebuilt `cTwoCLM`/`qcCLM`, `Claim18Carrier.Clauses` well-typed at the pinned carriers, and the
`rfl`-level unfolding of application. The one that fails is a `Pi.single_eq_same` convenience check on
the `def` synonym, and it is **not used anywhere in this module** — that name occurs nowhere in this
file outside THIS paragraph, because the one-bond test fields here are `coarseDelta`/`fineDelta`,
defined by an explicit `if _ = _ then _ else 0` precisely because the `Pi`-single API did not cooperate
with the synonym.

**What is and is not fixed by the choice of fibre norm.** The carriers are Pi/SUP over the fibre —
CMP98 p.36 (126)'s own norm class, the same choice `Claim18Carrier.lean`'s scope note argues for. The
fibre norm itself is whichever `NormedAddCommGroup ↥SuTwo` is in scope, and §7's value `ell³ − ell` is
INDEPENDENT of that choice: the proof uses only `‖r • v‖ = |r|·‖v‖` and the sup structure, so
replacing the fibre norm by any positive multiple of itself rescales both carriers identically and
leaves every operator norm here unchanged. -/

/-- **The fine su(2) bond-field carrier**, `Bond L → 𝔰𝔲(2)`, pinned. -/
def FineField (L : PeriodicLatticeExtent) : Type := Bond L → SuTwo

/-- **The coarse su(2) bond-field carrier**, `CoarseBond L ell → 𝔰𝔲(2)`, pinned. -/
def CoarseField (L : PeriodicLatticeExtent) (ell : ℕ) : Type := CoarseBond L ell → SuTwo

noncomputable instance instNormedAddCommGroupFineField {L : PeriodicLatticeExtent} :
    NormedAddCommGroup (FineField L) := Pi.normedAddCommGroup

noncomputable instance instNormedSpaceFineField {L : PeriodicLatticeExtent} :
    NormedSpace ℝ (FineField L) := Pi.normedSpace

noncomputable instance instNormedAddCommGroupCoarseField {L : PeriodicLatticeExtent} {ell : ℕ} :
    NormedAddCommGroup (CoarseField L ell) := Pi.normedAddCommGroup

noncomputable instance instNormedSpaceCoarseField {L : PeriodicLatticeExtent} {ell : ℕ} :
    NormedSpace ℝ (CoarseField L ell) := Pi.normedSpace

noncomputable instance instFiniteDimensionalFineField {L : PeriodicLatticeExtent} :
    FiniteDimensional ℝ (FineField L) :=
  inferInstanceAs (FiniteDimensional ℝ (Bond L → SuTwo))

noncomputable instance instFiniteDimensionalCoarseField {L : PeriodicLatticeExtent} {ell : ℕ} :
    FiniteDimensional ℝ (CoarseField L ell) :=
  inferInstanceAs (FiniteDimensional ℝ (CoarseBond L ell → SuTwo))

/-- A one-bond test field on the coarse carrier. -/
noncomputable def coarseDelta {ell : ℕ} (c : CoarseBond L ell) (v : SuTwo) : CoarseField L ell :=
  fun c' => if c' = c then v else 0

/-- A one-bond test field on the fine carrier. -/
noncomputable def fineDelta (b : Bond L) (v : SuTwo) : FineField L :=
  fun b' => if b' = b then v else 0

theorem coarseDelta_same {ell : ℕ} (c : CoarseBond L ell) (v : SuTwo) : coarseDelta c v c = v :=
  if_pos rfl

theorem coarseDelta_ne {ell : ℕ} {c c' : CoarseBond L ell} (v : SuTwo) (h : c' ≠ c) :
    coarseDelta c v c' = 0 := if_neg h

theorem fineDelta_same (b : Bond L) (v : SuTwo) : fineDelta b v b = v := if_pos rfl

theorem fineDelta_ne {b b' : Bond L} (v : SuTwo) (h : b' ≠ b) : fineDelta b v b' = 0 := if_neg h

theorem norm_coarseDelta {ell : ℕ} (c : CoarseBond L ell) (v : SuTwo) :
    ‖coarseDelta c v‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr ?_) ?_
  · intro c'
    by_cases h : c' = c
    · subst h; rw [coarseDelta_same]
    · rw [coarseDelta_ne v h, norm_zero]; exact norm_nonneg v
  · have h := norm_le_pi_norm (coarseDelta c v) c
    rwa [coarseDelta_same] at h

theorem norm_fineDelta (b : Bond L) (v : SuTwo) : ‖fineDelta b v‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr ?_) ?_
  · intro b'
    by_cases h : b' = b
    · subst h; rw [fineDelta_same]
    · rw [fineDelta_ne v h, norm_zero]; exact norm_nonneg v
  · have h := norm_le_pi_norm (fineDelta b v) b
    rwa [fineDelta_same] at h

/-! ## §2 — `𝒬_c⁻¹` on the su(2) fibre: the SAME last-layer lift `QcEquation` pinned -/

/-- **`(𝒬_c⁻¹ F)(z,μ) := ell • F(π z, μ)`** on the fine `μ`-bonds whose `μ`-offset inside their own
block is `ell − 1`, and `0` elsewhere — `QcEquation.lastLayerLift` with the scalar fibre `ℝ` replaced
by `SuTwo`. The weight `ell` and the layer `ell − 1` are NOT re-chosen here: they are exactly the
values `QcEquation` §2 computed as the unique member of the family `s_w^k` that is an exact right
inverse of the faithful average, and `suTwoLift_scalar` below proves this object restricts to that
one on scalar fields. -/
noncomputable def suTwoLift (ell : ℕ) (F : CoarseBond L ell → SuTwo) (b : Bond L) : SuTwo :=
  if (b.1 b.2).val % ell = ell - 1 then
    (ell : ℝ) • F (⟨blockCorner ell b.1, blockCorner_mem b.1⟩, b.2)
  else 0

/-- `lastLayerLift` in the TRUE branch, as a rewrite. -/
theorem lastLayerLift_pos {ell : ℕ} (f : CoarseBond L ell → ℝ) {b : Bond L}
    (h : (b.1 b.2).val % ell = ell - 1) :
    lastLayerLift ell f b = (ell : ℝ) * f (⟨blockCorner ell b.1, blockCorner_mem b.1⟩, b.2) := by
  unfold lastLayerLift
  rw [if_pos h]

/-- `lastLayerLift` in the FALSE branch, as a rewrite. -/
theorem lastLayerLift_neg {ell : ℕ} (f : CoarseBond L ell → ℝ) {b : Bond L}
    (h : ¬ (b.1 b.2).val % ell = ell - 1) : lastLayerLift ell f b = 0 := by
  unfold lastLayerLift
  rw [if_neg h]

/-- **The su(2) lift IS the scalar lift on scalar fields** — the anti-look-alike check. On a field of
the form `c ↦ f c • v` the su(2) object returns `(lastLayerLift ell f b) • v`, so nothing about the
weight, the layer or the block-corner map has been silently re-chosen. -/
theorem suTwoLift_scalar (ell : ℕ) (f : CoarseBond L ell → ℝ) (v : SuTwo) (b : Bond L) :
    suTwoLift ell (fun c => f c • v) b = (lastLayerLift ell f b) • v := by
  unfold suTwoLift
  by_cases h : (b.1 b.2).val % ell = ell - 1
  · rw [if_pos h, lastLayerLift_pos f h, smul_smul]
  · rw [if_neg h, lastLayerLift_neg f h, zero_smul]

/-- **The lift factors as (scalar weight) • (coarse value)** — the identity that lets the su(2)
section equation be reduced to `QcEquation.lineCoarseRestrict_lastLayerLift` rather than reproved. -/
theorem suTwoLift_factor {ell : ℕ} (F : CoarseBond L ell → SuTwo) (b : Bond L) :
    suTwoLift ell F b =
      (lastLayerLift ell (fun _ => (1 : ℝ)) b) •
        F (⟨blockCorner ell b.1, blockCorner_mem b.1⟩, b.2) := by
  unfold suTwoLift
  by_cases h : (b.1 b.2).val % ell = ell - 1
  · rw [if_pos h, lastLayerLift_pos (fun _ => (1 : ℝ)) h, mul_one]
  · rw [if_neg h, lastLayerLift_neg (fun _ => (1 : ℝ)) h, zero_smul]

theorem suTwoLift_add (ell : ℕ) (F G : CoarseBond L ell → SuTwo) (b : Bond L) :
    suTwoLift ell (F + G) b = suTwoLift ell F b + suTwoLift ell G b := by
  unfold suTwoLift
  by_cases h : (b.1 b.2).val % ell = ell - 1
  · rw [if_pos h, if_pos h, if_pos h, Pi.add_apply, smul_add]
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem suTwoLift_smul (ell : ℕ) (a : ℝ) (F : CoarseBond L ell → SuTwo) (b : Bond L) :
    suTwoLift ell (a • F) b = a • suTwoLift ell F b := by
  unfold suTwoLift
  by_cases h : (b.1 b.2).val % ell = ell - 1
  · rw [if_pos h, if_pos h, Pi.smul_apply, smul_comm]
  · rw [if_neg h, if_neg h, smul_zero]

/-- The lift as a `LinearMap` between the pinned carriers. -/
noncomputable def suTwoLiftLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    CoarseField L ell →ₗ[ℝ] FineField L where
  toFun F := suTwoLift ell F
  map_add' F G := funext fun b => suTwoLift_add ell F G b
  map_smul' a F := funext fun b => suTwoLift_smul ell a F b

theorem suTwoLiftLM_apply (L : PeriodicLatticeExtent) (ell : ℕ) (F : CoarseField L ell) :
    suTwoLiftLM L ell F = suTwoLift ell F := rfl

/-- **`𝒬_c⁻¹` as a genuine `ContinuousLinearMap`** — the supplied section slot. -/
noncomputable def suTwoLiftCLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    CoarseField L ell →L[ℝ] FineField L :=
  LinearMap.toContinuousLinearMap (suTwoLiftLM L ell)

theorem suTwoLiftCLM_apply (L : PeriodicLatticeExtent) (ell : ℕ) (F : CoarseField L ell) :
    suTwoLiftCLM L ell F = suTwoLift ell F := rfl

/-- **`C⁽²⁾` as a `LinearMap` between the pinned carriers** — `FullReparamC.fullC` at the REAL
explicit inverse `FullReparamC.dinvC`. No `Dinv` parameter survives and no `hinv` is assumed: the
inverse is the source's own, discharged unconditionally by `FullReparamC.dinvC_hinv`. -/
noncomputable def cTwoLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) : FineField L →ₗ[ℝ] FineField L where
  toFun B := fullC U ell (dinvC U ell) B
  map_add' B₁ B₂ := fullC_add U (dinvC U ell) B₁ B₂
  map_smul' a B := fullC_smul U (dinvC U ell) a B

/-- **`𝒬_c` as a `LinearMap` between the pinned carriers** — the faithful covariant line-integral
average `LineIntegralCovariant.lineCoarseRestrictCov`, CMP95 (1.18)/CMP98 (125). -/
noncomputable def qcLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) : FineField L →ₗ[ℝ] CoarseField L ell where
  toFun A := lineCoarseRestrictCov U ell A
  map_add' A₁ A₂ := funext fun b => lineCoarseRestrictCov_add U ell A₁ A₂ b
  map_smul' a A := funext fun b => lineCoarseRestrictCov_smul U ell a A b

noncomputable def cTwoCLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) : FineField L →L[ℝ] FineField L :=
  LinearMap.toContinuousLinearMap (cTwoLM U ell)

noncomputable def qcCLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) : FineField L →L[ℝ] CoarseField L ell :=
  LinearMap.toContinuousLinearMap (qcLM U ell)

theorem cTwoCLM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (B : FineField L) : cTwoCLM U ell B = fullC U ell (dinvC U ell) B := rfl

theorem qcCLM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (A : FineField L) : qcCLM U ell A = lineCoarseRestrictCov U ell A := rfl

theorem transfer_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (F : CoarseField L ell) :
    (cTwoCLM U ell ∘L suTwoLiftCLM L ell) F = fullC U ell (dinvC U ell) (suTwoLift ell F) := rfl

/-! ## §3 — THE SECTION EQUATION on the su(2) carrier -/

/-- The line integral, in the `pathSite` form the covariant average uses. Definitional: `pathSite`
(`QOne.lean:175`) and `lineIntegralValue`'s own iterate (`LineIntegralAveraging.lean:97`) are the
same function. -/
theorem lineIntegralValue_eq_pathSite (ell : ℕ) (A : Bond L → ℝ) (x : PeriodicLatticeSite L)
    (μ : Fin 3) : lineIntegralValue ell A x μ = ∑ i ∈ Finset.range ell, A (pathSite x μ i, μ) := rfl

/-- **Every read bond the lift does NOT kill carries the coarse bond `c` itself.** For `x` in the
block of a coarse site `y` and `i < ell`, if the bond `(x + i·e_μ, μ)` sits on the last layer of its
own block then its block corner is `y`. Two ingredients: transversally `pathSite` does not move, so
`blockCorner_of_mem_blockOf` applies; along `μ` the last-layer condition forces `j + i = ell − 1`
(with `j` the `μ`-offset of `x`), hence no periodic wrap and corner `y μ`. -/
theorem blockCorner_read_hit {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell) (μ : Fin 3) {i : ℕ} (hi : i < ell)
    (hcond : ((pathSite x μ i) μ).val % ell = ell - 1) :
    blockCorner ell (pathSite x μ i) = y := by
  have hcorner : blockCorner ell x = y := blockCorner_of_mem_blockOf hy hx
  have hblk := mem_blockOf.mp hx
  have hy0 : ∀ ν : Fin 3, (y ν).val % ell = 0 := mem_CoarseLattice.mp hy
  have hfit : (y μ).val + ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd hy μ
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (hy0 μ)
  -- the `μ`-offset of `x`
  have hlo : (y μ).val ≤ (x μ).val := (hblk μ).1
  have hhi : (x μ).val < (y μ).val + ell := (hblk μ).2
  -- the last-layer condition, reduced mod `ell`
  have hmodell : ((x μ).val + i) % ell = ell - 1 := by
    have h1 : ((pathSite x μ i) μ).val = ((x μ).val + i) % (L μ + 1) := pathSite_apply_self_val _ _ _
    rw [h1, Nat.mod_mod_of_dvd _ (hdvd μ)] at hcond
    exact hcond
  have hsum : (x μ).val + i = (y μ).val + (ell - 1) := by
    have hxv : (x μ).val = ell * k + ((x μ).val - (y μ).val) := by omega
    have hj : (x μ).val - (y μ).val < ell := by omega
    have hrw : ((x μ).val + i) % ell = (((x μ).val - (y μ).val) + i) % ell := by
      conv_lhs => rw [show (x μ).val + i = ell * k + (((x μ).val - (y μ).val) + i) by omega]
      rw [Nat.mul_add_mod]
    rw [hrw] at hmodell
    have hlt2 : ((x μ).val - (y μ).val) + i < 2 * ell := by omega
    rcases lt_or_ge (((x μ).val - (y μ).val) + i) ell with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hmodell; omega
    · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at hmodell; omega
  -- so the moved coordinate does not wrap
  have hval : ((pathSite x μ i) μ).val = (y μ).val + (ell - 1) := by
    rw [pathSite_apply_self_val, hsum, Nat.mod_eq_of_lt (by omega)]
  funext ν
  apply Fin.ext
  rcases eq_or_ne ν μ with rfl | hν
  · rw [blockCorner_val, hval]
    have h2 : ((y ν).val + (ell - 1)) % ell = ell - 1 := by
      rw [show (y ν).val + (ell - 1) = ell * k + (ell - 1) by omega, Nat.mul_add_mod,
        Nat.mod_eq_of_lt (by omega)]
    omega
  · have hsite : (pathSite x μ i) ν = x ν := pathSite_apply_ne x μ ν i hν
    rw [blockCorner_val, hsite, ← blockCorner_val ell x ν, hcorner]

/-- **THE SECTION EQUATION at `U = 1`**: the su(2) last-layer lift is an EXACT right inverse of the
faithful flat su(2) line-integral average, at every coarse bond, every tiled extent, every `0 < ell`.
The whole counting is inherited from `QcEquation.lineCoarseRestrict_lastLayerLift` via
`suTwoLift_factor` — no re-derivation of the `ell⁴` bookkeeping. -/
theorem lineCoarseRestrictSuTwo_suTwoLift {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (F : CoarseBond L ell → SuTwo) (b : CoarseBond L ell) :
    lineCoarseRestrictSuTwo ell (suTwoLift ell F) b = F b := by
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  have hterm : ∀ x ∈ blockOf y ell, ∀ i ∈ Finset.range ell,
      suTwoLift ell F (pathSite x μ i, μ)
        = (lastLayerLift ell (fun _ => (1 : ℝ)) (pathSite x μ i, μ)) •
            F ((⟨y, hy⟩ : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), μ) := by
    intro x hx i hi
    rw [suTwoLift_factor]
    by_cases hcond : ((pathSite x μ i) μ).val % ell = ell - 1
    · congr 2
      refine Prod.ext_iff.mpr ⟨Subtype.ext ?_, rfl⟩
      exact blockCorner_read_hit hell hdvd hy hx μ (Finset.mem_range.mp hi) hcond
    · rw [lastLayerLift_neg (fun _ => (1 : ℝ)) hcond, zero_smul, zero_smul]
  simp only [lineCoarseRestrictSuTwo]
  rw [Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun i hi => hterm x hx i hi))]
  have hinner : ∀ x ∈ blockOf y ell,
      (∑ i ∈ Finset.range ell,
        (lastLayerLift ell (fun _ => (1 : ℝ)) (pathSite x μ i, μ)) •
          F ((⟨y, hy⟩ : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), μ))
      = (∑ i ∈ Finset.range ell, lastLayerLift ell (fun _ => (1 : ℝ)) (pathSite x μ i, μ)) •
          F ((⟨y, hy⟩ : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), μ) :=
    fun _ _ => Finset.sum_smul.symm
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_smul, smul_smul]
  have hcoeff : (1 / (ell : ℝ) ^ 4) *
      ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell,
        lastLayerLift ell (fun _ => (1 : ℝ)) (pathSite x μ i, μ) = 1 := by
    have h : lineCoarseRestrict ell (lastLayerLift ell (fun _ => (1 : ℝ)))
        ((⟨y, hy⟩ : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), μ) = 1 :=
      lineCoarseRestrict_lastLayerLift hell hdvd (fun _ => (1 : ℝ)) _
    rw [lineCoarseRestrict] at h
    simpa only [lineIntegralValue_eq_pathSite] using h
  rw [hcoeff, one_smul]

/-- The section equation as an operator identity, at the CLM layer: **clause 1**. -/
theorem qc_comp_suTwoLift {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    qcCLM (trivialU L) ell ∘L suTwoLiftCLM L ell
      = ContinuousLinearMap.id ℝ (CoarseField L ell) := by
  refine ContinuousLinearMap.ext fun F => ?_
  funext b
  show lineCoarseRestrictCov (trivialU L) ell (suTwoLift ell F) b = F b
  rw [lineCoarseRestrictCov_trivialU]
  exact lineCoarseRestrictSuTwo_suTwoLift hell hdvd F b

#print axioms suTwoLift_scalar
#print axioms blockCorner_read_hit
#print axioms lineCoarseRestrictSuTwo_suTwoLift
#print axioms qc_comp_suTwoLift

/-! ## §4 — the pieces of the transfer computation, each a fact about a SUPPLIED object -/

/-- **`rest_c = L_c − coeffDc(c,b₀)∘proj_{b₀}`** — immediate from `dropZero = id − single∘proj`, and
the identity that makes the transfer computable in closed form without re-doing the `ell⁴` block sum:
the only piece of `rest_c` that is not already known is the diagonal coefficient, and
`FullReparamC.coeffDc_general_op` gives that in closed form. -/
theorem restFunctional_eq {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (c : CoarseBond L ell)
    (b₀ : Bond L) (B : Bond L → SuTwo) :
    restFunctional U ell c b₀ B
      = lineCoarseRestrictCov U ell B c - coeffDc U ell c b₀ (B b₀) := by
  have h1 : dropZero b₀ B
      = B - (LinearMap.single ℝ (fun _ : Bond L => SuTwo) b₀) (B b₀) := by
    simp only [dropZero, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
  show constraintFunctional U ell c (dropZero b₀ B) = _
  rw [h1, map_sub]
  simp only [constraintFunctional_apply, coeffDc_apply, LinearMap.single_apply]

/-- The trivial background transports nothing along the drop path. -/
theorem dropTransport_trivialU {ell : ℕ} (c : CoarseBond L ell) :
    dropTransport (trivialU L) ell c = 1 :=
  periodicPathHolonomy_trivialU_eq_one _ _

/-- The real explicit inverse at the trivial background: `ell³ · id`. -/
theorem dinvC_trivialU {ell : ℕ} (c : CoarseBond L ell) :
    dinvC (trivialU L) ell c = ((ell : ℝ) ^ 3) • LinearMap.id := by
  show ((ell : ℝ) ^ 3) • RMap (dropTransport (trivialU L) ell c)⁻¹ = _
  rw [dropTransport_trivialU, inv_one, RMap_one]

/-- The diagonal coefficient at the trivial background: `ell⁻³ · id`. Quoted from
`FullReparamC.coeffDc_general_op`, which is general in `U`. -/
theorem coeffDc_trivialU_dropped {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (c : CoarseBond L ell) :
    coeffDc (trivialU L) ell c (droppedBondLast ell c)
      = ((1 : ℝ) / (ell : ℝ) ^ 3) • LinearMap.id := by
  rw [coeffDc_general_op hell hdvd, dropTransport_trivialU, RMap_one]

/-- The dropped bond sits on the LAST LAYER — the layer the supplied section writes to. This is the
overlap between the two pinned objects: `𝒬_c⁻¹`'s support and `C⁽²⁾`'s eliminated variables. -/
theorem droppedBondLast_lastLayer {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (c : CoarseBond L ell) :
    ((pathSite c.1.1 c.2 (ell - 1)) c.2).val % ell = ell - 1 := by
  have hfit : (c.1.1 c.2).val + ell ≤ L c.2 + 1 := coarseLattice_mem_fits hdvd c.1.2 c.2
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 c.2)
  have h1 : ((pathSite c.1.1 c.2 (ell - 1)) c.2).val = (c.1.1 c.2).val + (ell - 1) := by
    rw [pathSite_apply_self_val,
      Nat.mod_eq_of_lt (show (c.1.1 c.2).val + (ell - 1) < L c.2 + 1 by omega)]
  rw [h1, show (c.1.1 c.2).val + (ell - 1) = ell * k + (ell - 1) by omega, Nat.mul_add_mod,
    Nat.mod_eq_of_lt (show ell - 1 < ell by omega)]

/-- **The section's value AT the dropped bond is `ell • F c`** — not `0`. This is the fact that
refutes the natural first guess (that the real `C` annihilates the section's range because `C`
eliminates exactly the last-layer variables): the section's support is EVERY bond at `μ`-offset
`ell − 1`, whereas the dropped bonds are only those whose TRANSVERSE coordinates are multiples of
`ell`, so `C` is the identity on most of the section's support and the composition is far from zero. -/
theorem suTwoLift_droppedBondLast {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (F : CoarseBond L ell → SuTwo) (c : CoarseBond L ell) :
    suTwoLift ell F (droppedBondLast ell c) = (ell : ℝ) • F c := by
  have hself : c.1.1 ∈ blockOf c.1.1 ell := by
    rw [mem_blockOf]; intro ν; omega
  have hcond : (((droppedBondLast ell c).1) ((droppedBondLast ell c).2)).val % ell = ell - 1 :=
    droppedBondLast_lastLayer hell hdvd c
  have hcb : ((⟨blockCorner ell ((droppedBondLast ell c).1),
        blockCorner_mem ((droppedBondLast ell c).1)⟩ :
        {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}),
      ((droppedBondLast ell c).2)) = c := by
    refine Prod.ext_iff.mpr ⟨Subtype.ext ?_, rfl⟩
    exact blockCorner_read_hit hell hdvd c.1.2 hself c.2 (by omega) hcond
  rw [suTwoLift_factor, lastLayerLift_pos (fun _ => (1 : ℝ)) hcond, mul_one, hcb]

/-! ## §5 — THE TRANSFER OPERATOR `D̃⁽²⁾ = C⁽²⁾ ∘ 𝒬_c⁻¹`, IN CLOSED FORM -/

/-- **THE COMPUTATION.** At the trivial background, the real (3.157) reparametrization composed with
the supplied section returns, at the dropped bond of `c`, exactly `−(ell³ − ell) • F c`.

The mechanism, and why the factor is what it is: `rest_c(𝒬_c⁻¹F) = F c − ell⁻³·(ell • F c)`, because
the section is an exact right inverse (so the un-dropped constraint value is `F c`) and the diagonal
coefficient is `ell⁻³` while the section's value at the dropped bond is `ell • F c`. Applying the real
inverse `ell³ · id` multiplies the residual `(1 − ell⁻²)` by `ell³`. So the `ell³` is the
normalization of `𝒬_c` and the `ell` is the section's line-integral weight — both counted, neither
chosen. -/
theorem fullC_suTwoLift_at_dropped {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (F : CoarseBond L ell → SuTwo) (c : CoarseBond L ell) :
    fullC (trivialU L) ell (dinvC (trivialU L) ell) (suTwoLift ell F) (droppedBondLast ell c)
      = (-((ell : ℝ) ^ 3 - (ell : ℝ))) • F c := by
  have hne : ((ell : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  have hQ : lineCoarseRestrictCov (trivialU L) ell (suTwoLift ell F) c = F c := by
    rw [lineCoarseRestrictCov_trivialU]
    exact lineCoarseRestrictSuTwo_suTwoLift hell hdvd F c
  have hb0 : suTwoLift ell F (droppedBondLast ell c) = (ell : ℝ) • F c :=
    suTwoLift_droppedBondLast hell hdvd F c
  have hrest : restFunctional (trivialU L) ell c (droppedBondLast ell c) (suTwoLift ell F)
      = F c - ((1 : ℝ) / (ell : ℝ) ^ 2) • F c := by
    rw [restFunctional_eq, hQ, hb0, coeffDc_trivialU_dropped hell hdvd]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [show (1 / (ell : ℝ) ^ 3) * (ell : ℝ) = 1 / (ell : ℝ) ^ 2 by field_simp]
  rw [fullC_dropped hell hdvd, solvedValue, hrest, dinvC_trivialU]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_sub, smul_smul]
  rw [show ((ell : ℝ) ^ 3) * (1 / (ell : ℝ) ^ 2) = (ell : ℝ) by field_simp, ← sub_smul,
    ← neg_smul]

#print axioms restFunctional_eq
#print axioms dropTransport_trivialU
#print axioms dinvC_trivialU
#print axioms coeffDc_trivialU_dropped
#print axioms suTwoLift_droppedBondLast
#print axioms fullC_suTwoLift_at_dropped


/-! ### §5a — the SAME computation at a GENERAL background field

The `ell³` amplification is not an artefact of `U = 1`: it comes from `FullReparamC.dinvC`, whose
closed form `ell³ · R(dropTransport⁻¹)` is general in `U` (`FullReparamC.coeffDc_general_op`). The
identity below holds at every `U`, and the `U = 1` value `−(ell³ − ell) • F c` is exactly what it
returns once the section equation replaces `𝒬_c(𝒬_c⁻¹F)(c)` by `F c` — a second, independent route to
`fullC_suTwoLift_at_dropped`, recorded as `fullC_suTwoLift_at_dropped_via_general` below. -/

theorem dinvC_apply {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L ell) (v : SuTwo) :
    dinvC U ell c v = ((ell : ℝ) ^ 3) • RMap (dropTransport U ell c)⁻¹ v := by
  show (((ell : ℝ) ^ 3) • RMap (dropTransport U ell c)⁻¹) v = _
  rw [LinearMap.smul_apply]

theorem rmap_inv_cancel {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L ell) (v : SuTwo) :
    RMap (dropTransport U ell c)⁻¹ (RMap (dropTransport U ell c) v) = v := by
  rw [RMap_mul_apply, inv_mul_cancel, RMap_one, LinearMap.id_apply]

/-- **THE TRANSFER VALUE AT THE DROPPED BOND, GENERAL `U`.** -/
theorem fullC_suTwoLift_at_dropped_general {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (F : CoarseBond L ell → SuTwo) (c : CoarseBond L ell) :
    fullC U ell (dinvC U ell) (suTwoLift ell F) (droppedBondLast ell c)
      = (ell : ℝ) • F c
        - ((ell : ℝ) ^ 3) • RMap (dropTransport U ell c)⁻¹
            (lineCoarseRestrictCov U ell (suTwoLift ell F) c) := by
  have hne : ((ell : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  have hb0 : suTwoLift ell F (droppedBondLast ell c) = (ell : ℝ) • F c :=
    suTwoLift_droppedBondLast hell hdvd F c
  have hstep : RMap (dropTransport U ell c)⁻¹
      (((((1 : ℝ) / (ell : ℝ) ^ 3) • RMap (dropTransport U ell c))) ((ell : ℝ) • F c))
      = ((1 : ℝ) / (ell : ℝ) ^ 2) • F c := by
    rw [LinearMap.smul_apply, map_smul, map_smul, map_smul, rmap_inv_cancel, smul_smul]
    congr 1
    field_simp
  rw [fullC_dropped hell hdvd, solvedValue, restFunctional_eq,
    coeffDc_general_op hell hdvd, hb0, dinvC_apply, map_sub, hstep, smul_sub, smul_smul,
    show ((ell : ℝ) ^ 3) * ((1 : ℝ) / (ell : ℝ) ^ 2) = (ell : ℝ) by field_simp, neg_sub]

/-- The `U = 1` value re-derived from the general identity — a second, independent path to
`fullC_suTwoLift_at_dropped`, so the constant `ell³ − ell` is not produced by a single computation. -/
theorem fullC_suTwoLift_at_dropped_via_general {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (F : CoarseBond L ell → SuTwo)
    (c : CoarseBond L ell) :
    fullC (trivialU L) ell (dinvC (trivialU L) ell) (suTwoLift ell F) (droppedBondLast ell c)
      = (-((ell : ℝ) ^ 3 - (ell : ℝ))) • F c := by
  have hQ : lineCoarseRestrictCov (trivialU L) ell (suTwoLift ell F) c = F c := by
    rw [lineCoarseRestrictCov_trivialU]
    exact lineCoarseRestrictSuTwo_suTwoLift hell hdvd F c
  rw [fullC_suTwoLift_at_dropped_general hell hdvd, hQ, dropTransport_trivialU, inv_one, RMap_one,
    LinearMap.id_apply, ← neg_sub, ← sub_smul, ← neg_smul, neg_sub, sub_smul]

/-- The two closed forms are the same number — the non-trivial content being that the general-`U`
right-hand side collapses to `−(ell³ − ell) • F c` at `U = 1`. Deliberately NOT stated as
`x = x` (which would be a tautology proving nothing): it equates the two DIFFERENT expressions. -/
theorem transfer_value_two_routes_agree {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (F : CoarseBond L ell → SuTwo)
    (c : CoarseBond L ell) :
    (-((ell : ℝ) ^ 3 - (ell : ℝ))) • F c
      = (ell : ℝ) • F c
        - ((ell : ℝ) ^ 3) • RMap (dropTransport (trivialU L) ell c)⁻¹
            (lineCoarseRestrictCov (trivialU L) ell (suTwoLift ell F) c) :=
  (fullC_suTwoLift_at_dropped hell hdvd F c).symm.trans
    (fullC_suTwoLift_at_dropped_general hell hdvd (trivialU L) F c)

#print axioms dinvC_apply
#print axioms rmap_inv_cancel
#print axioms fullC_suTwoLift_at_dropped_general
#print axioms fullC_suTwoLift_at_dropped_via_general
#print axioms transfer_value_two_routes_agree

/-! ## §6 — THE FULLY SUPPLIED BUNDLE -/

/-- **CLAIM 18'S CLAUSE BUNDLE WITH EVERY OPERATOR SUPPLIED.** There is no existential over `C⁽²⁾`,
none over `𝒬_c`, none over `𝒬_c⁻¹`, and no carrier is chosen by a witness: all three slots are named
lattice objects and both carriers are fixed by their types. The remaining arguments are the background
field `U` and Claim 18's own four constants; nothing has been added, and in particular no new constant
is introduced that a witness could tune.

So this is a genuine proposition about Bałaban's operators — TRUE or FALSE — and §8/§9 decide it. -/
def FullySuppliedClauses (L : PeriodicLatticeExtent) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ) : Prop :=
  AdalyFormal.Balaban.Claim18Carrier.Clauses
    (Hfine := FineField L) (Hcoarse := CoarseField L ell)
    Lreal d Ccorr α₀ (cTwoCLM U ell) (qcCLM U ell) (suTwoLiftCLM L ell)

/-! ## §7 — the EXACT operator norm of the transfer operator `D̃⁽²⁾ = C⁽²⁾ ∘ 𝒬_c⁻¹` -/

/-- The section's pointwise bound: `ell`, its line-integral weight. -/
theorem norm_suTwoLift_le {ell : ℕ} (F : CoarseField L ell) (b : Bond L) :
    ‖suTwoLift ell F b‖ ≤ (ell : ℝ) * ‖F‖ := by
  unfold suTwoLift
  by_cases h : (b.1 b.2).val % ell = ell - 1
  · rw [if_pos h, norm_smul, Real.norm_eq_abs, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm F _) (Nat.cast_nonneg ell)
  · rw [if_neg h, norm_zero]
    positivity

/-- `ell ≤ ell³ − ell` for `2 ≤ ell`: the dropped-bond value dominates every free-bond value, which is
why the operator norm is attained AT a dropped bond. -/
theorem ell_le_cube_sub {ell : ℕ} (hell2 : 2 ≤ ell) : (ell : ℝ) ≤ (ell : ℝ) ^ 3 - (ell : ℝ) := by
  have h2 : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell2
  have hsq : (4 : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
  have h4 : (ell : ℝ) * 4 ≤ (ell : ℝ) * (ell : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by linarith)
  have h5 : (ell : ℝ) * (ell : ℝ) ^ 2 = (ell : ℝ) ^ 3 := by ring
  linarith

theorem cube_sub_nonneg {ell : ℕ} (hell2 : 2 ≤ ell) : (0 : ℝ) ≤ (ell : ℝ) ^ 3 - (ell : ℝ) :=
  le_trans (Nat.cast_nonneg ell) (ell_le_cube_sub hell2)

/-- The pointwise upper bound on the transfer. Enumeration is against the DEFINITION of `fullC`
(identity off `IsDropped`, `solvedValue` on `IsDropped`), not against a chosen subset of bonds: the
`by_cases` is on `IsDropped ell b` itself, so no bond class can be silently omitted. -/
theorem norm_transfer_apply_le {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseField L ell) :
    ‖(cTwoCLM (trivialU L) ell ∘L suTwoLiftCLM L ell) F‖ ≤ ((ell : ℝ) ^ 3 - (ell : ℝ)) * ‖F‖ := by
  have hell : 0 < ell := by omega
  have hle : (ell : ℝ) ≤ (ell : ℝ) ^ 3 - (ell : ℝ) := ell_le_cube_sub hell2
  have hnn0 : (0 : ℝ) ≤ (ell : ℝ) ^ 3 - (ell : ℝ) := cube_sub_nonneg hell2
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hnn0 (norm_nonneg F))).mpr ?_
  intro b
  show ‖fullC (trivialU L) ell (dinvC (trivialU L) ell) (suTwoLift ell F) b‖ ≤ _
  by_cases hd : IsDropped ell b
  · obtain ⟨c, rfl⟩ := hd
    rw [fullC_suTwoLift_at_dropped hell hdvd, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : -((ell : ℝ) ^ 3 - (ell : ℝ)) ≤ 0), neg_neg]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm F c) hnn0
  · rw [fullC_free (trivialU L) (dinvC (trivialU L) ell) (suTwoLift ell F) hd]
    exact le_trans (norm_suTwoLift_le F b) (mul_le_mul_of_nonneg_right hle (norm_nonneg F))

/-- **THE NORM OF THE TRANSFER OPERATOR, EXACTLY: `‖C⁽²⁾ ∘L 𝒬_c⁻¹‖ = ell³ − ell`.**

An EQUALITY, so the comparison with clause 5's bound is a measurement and not an estimate. Upper
bound: `norm_transfer_apply_le`. Lower bound: attained at the single NAMED test field
`coarseDelta (originCoarseBond L ell) suTwoWitness`, read at that coarse bond's own dropped bond. -/
theorem opNorm_transfer_eq {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖cTwoCLM (trivialU L) ell ∘L suTwoLiftCLM L ell‖ = (ell : ℝ) ^ 3 - (ell : ℝ) := by
  have hell : 0 < ell := by omega
  have hnn0 : (0 : ℝ) ≤ (ell : ℝ) ^ 3 - (ell : ℝ) := cube_sub_nonneg hell2
  refine le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ hnn0 fun F => norm_transfer_apply_le hell2 hdvd F) ?_
  set c : CoarseBond L ell := originCoarseBond L ell with hc
  have hwpos : (0 : ℝ) < ‖suTwoWitness‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
  have hval : (cTwoCLM (trivialU L) ell ∘L suTwoLiftCLM L ell)
        (coarseDelta c suTwoWitness) (droppedBondLast ell c)
      = (-((ell : ℝ) ^ 3 - (ell : ℝ))) • suTwoWitness := by
    show fullC (trivialU L) ell (dinvC (trivialU L) ell)
        (suTwoLift ell (coarseDelta c suTwoWitness)) (droppedBondLast ell c) = _
    rw [fullC_suTwoLift_at_dropped hell hdvd, coarseDelta_same]
  have hge : ((ell : ℝ) ^ 3 - (ell : ℝ)) * ‖suTwoWitness‖
      ≤ ‖(cTwoCLM (trivialU L) ell ∘L suTwoLiftCLM L ell) (coarseDelta c suTwoWitness)‖ := by
    have h1 := norm_le_pi_norm
      ((cTwoCLM (trivialU L) ell ∘L suTwoLiftCLM L ell) (coarseDelta c suTwoWitness))
      (droppedBondLast ell c)
    rw [hval, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : -((ell : ℝ) ^ 3 - (ell : ℝ)) ≤ 0), neg_neg] at h1
    exact h1
  have h2 := (cTwoCLM (trivialU L) ell ∘L suTwoLiftCLM L ell).le_opNorm
    (coarseDelta c suTwoWitness)
  rw [norm_coarseDelta] at h2
  exact le_of_mul_le_mul_right (by linarith) hwpos

#print axioms norm_coarseDelta
#print axioms norm_fineDelta
#print axioms norm_suTwoLift_le
#print axioms ell_le_cube_sub
#print axioms norm_transfer_apply_le
#print axioms opNorm_transfer_eq

/-! ## §8 — THE DECISION: the fully supplied bundle is FALSE at the faithful parameters -/

/-- **THE HEADLINE.** With every operator supplied, Claim 18's bundle is FALSE whenever its own
transfer bound `Lreal^(d−1)` falls below the transfer operator's actual norm `ell³ − ell`. Nothing is
estimated: the norm is `opNorm_transfer_eq`, an equality. -/
theorem fullySupplied_false {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    (hlt : Lreal ^ ((d : ℝ) - 1) < (ell : ℝ) ^ 3 - (ell : ℝ)) :
    ¬ FullySuppliedClauses L ell (trivialU L) Lreal d Ccorr α₀ := by
  intro h
  have h5 : ‖cTwoCLM (trivialU L) ell ∘L suTwoLiftCLM L ell‖ ≤ Lreal ^ ((d : ℝ) - 1) :=
    h.2.2.2.2.1
  rw [opNorm_transfer_eq hell2 hdvd] at h5
  linarith

/-- **AT THE FAITHFUL PARAMETERS.** Bałaban's `L` is the block side, so `Lreal = ell`; this tree's
lattice is three-dimensional (`Fin 3`), so `d = 3`; clause 5 then reads `‖D̃⁽²⁾‖ ≤ ell²`. The actual
norm is `ell³ − ell > ell²` for every `2 ≤ ell`, so the fully supplied bundle is FALSE — at every
tileable extent, every block side `2 ≤ ell`, every `Ccorr` and every `α₀`. The failure is by exactly
one power of `ell`. -/
theorem fullySupplied_false_at_faithful_scale {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (Ccorr α₀ : ℝ) :
    ¬ FullySuppliedClauses L ell (trivialU L) (ell : ℝ) 3 Ccorr α₀ := by
  refine fullySupplied_false hell2 hdvd (ell : ℝ) 3 Ccorr α₀ ?_
  have h2 : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell2
  have hexp : (((3 : ℕ) : ℝ) - 1) = ((2 : ℕ) : ℝ) := by norm_num
  rw [hexp, Real.rpow_natCast]
  nlinarith [h2]

/-- **AT A CONCRETE LATTICE**, so the general theorem is not vacuous for lack of a tileable extent:
the `4³` torus (`L μ + 1 = 4`), block side `ell = 2`, `Lreal = 2`, `d = 3`. Clause 5 demands
`‖D̃⁽²⁾‖ ≤ 2² = 4`; the actual norm is `2³ − 2 = 6`. -/
theorem fullySupplied_false_at_witness_lattice (Ccorr α₀ : ℝ) :
    ¬ FullySuppliedClauses (fun _ => 3) 2 (trivialU (fun _ => 3)) (2 : ℝ) 3 Ccorr α₀ :=
  fullySupplied_false_at_faithful_scale (L := fun _ => 3) (by norm_num)
    (fun _ => by norm_num) Ccorr α₀

#print axioms fullySupplied_false
#print axioms fullySupplied_false_at_faithful_scale
#print axioms fullySupplied_false_at_witness_lattice

/-! ## §9 — THE OTHER FIVE CLAUSES ARE THEOREMS, so the failure is LOCALIZED to clause 5 -/

/-- Clause 2: an exact section is injective. Quoted from `Claim18Carrier`, not reproved. -/
theorem suTwoLift_injective {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Function.Injective (suTwoLiftCLM L ell) :=
  AdalyFormal.Balaban.Claim18Carrier.section_forces_inv_injective (qc_comp_suTwoLift hell hdvd)

/-- The pointwise sup bound on the faithful average: `ell³` block sites times `ell` bonds per segment
against the `1/ell⁴` coefficient — a genuine average, so it does not expand the sup norm. The counts
come from `AdmissibleSubspace.card_blockOf_of_coarse` and `Finset.card_range`, not from a claim. -/
theorem norm_qc_apply_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : FineField L) (b : CoarseBond L ell) :
    ‖lineCoarseRestrictSuTwo ell A b‖ ≤ ‖A‖ := by
  have hne : ((ell : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  have hellpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hcard : (blockOf b.1.1 ell).card = ell ^ 3 := card_blockOf_of_coarse hdvd b.1.2
  have hcpos : (0 : ℝ) < 1 / (ell : ℝ) ^ 4 := one_div_pos.mpr (pow_pos hellpos 4)
  have hinner : ∀ x ∈ blockOf b.1.1 ell,
      ‖∑ i ∈ Finset.range ell, A (pathSite x b.2 i, b.2)‖ ≤ (ell : ℝ) * ‖A‖ := by
    intro x _
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans
      (Finset.sum_le_sum (fun i _ => norm_le_pi_norm A (pathSite x b.2 i, b.2))) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_refl _
  have houter : ‖∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell, A (pathSite x b.2 i, b.2)‖
      ≤ (ell : ℝ) ^ 3 * ((ell : ℝ) * ‖A‖) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum hinner) ?_
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast
    exact le_refl _
  show ‖(1 / (ell : ℝ) ^ 4) •
    (∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell, A (pathSite x b.2 i, b.2))‖ ≤ ‖A‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
  refine le_trans (mul_le_mul_of_nonneg_left houter hcpos.le) ?_
  rw [show (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) ^ 3 * ((ell : ℝ) * ‖A‖))
      = ((ell : ℝ) ^ 4 / (ell : ℝ) ^ 4) * ‖A‖ by ring, div_self (pow_ne_zero 4 hne), one_mul]

/-- `‖𝒬_c‖ ≤ 1` at the trivial background — the absolute block-average bound of CMP98 p.36 (126), in
that estimate's OWN sup-norm class. -/
theorem opNorm_qc_le_one {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖qcCLM (trivialU L) ell‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr ?_
  intro b
  show ‖lineCoarseRestrictCov (trivialU L) ell A b‖ ≤ ‖A‖
  rw [lineCoarseRestrictCov_trivialU]
  exact norm_qc_apply_le hell hdvd A b

/-- Clause 3 in the exact form the bundle states it. -/
theorem qc_clause3 {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lreal Ccorr α₀ : ℝ) (hC : 0 ≤ Ccorr) (hα : 0 ≤ α₀) :
    ‖qcCLM (trivialU L) ell‖ ≤ 1 + Ccorr * Lreal ^ 2 * α₀ := by
  refine le_trans (opNorm_qc_le_one hell hdvd) ?_
  have h : (0 : ℝ) ≤ Ccorr * Lreal ^ 2 * α₀ :=
    mul_nonneg (mul_nonneg hC (sq_nonneg Lreal)) hα
  linarith

/-- Clause 4a: `1 ≤ ‖C⁽²⁾‖`, for EVERY background field. The real `C` is the identity on every free
bond, and `FullReparamC.coarseBond_base_not_dropped` names one: the bond at the origin in direction
`0`. So the anti-shrink floor is not an assumption on a witness, it is a property of the operator. -/
theorem one_le_opNorm_cTwo {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    1 ≤ ‖cTwoCLM U ell‖ := by
  have hwpos : (0 : ℝ) < ‖suTwoWitness‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
  have hfree : ¬ IsDropped ell ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) :=
    coarseBond_base_not_dropped hell2 hdvd _ originSite_coarse 0
  have hval : cTwoCLM U ell
      (fineDelta ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) suTwoWitness)
      ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) = suTwoWitness := by
    show fullC U ell (dinvC U ell)
      (fineDelta ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) suTwoWitness) _ = _
    rw [fullC_free U (dinvC U ell) _ hfree, fineDelta_same]
  have h1 : ‖suTwoWitness‖
      ≤ ‖cTwoCLM U ell
          (fineDelta ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) suTwoWitness)‖ := by
    have h := norm_le_pi_norm
      (cTwoCLM U ell (fineDelta ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) suTwoWitness))
      ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3))
    rwa [hval] at h
  have h2 : ‖cTwoCLM U ell
        (fineDelta ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) suTwoWitness)‖
      ≤ ‖cTwoCLM U ell‖ * ‖suTwoWitness‖ := by
    have h := (cTwoCLM U ell).le_opNorm
      (fineDelta ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) suTwoWitness)
    rwa [norm_fineDelta] at h
  exact le_of_mul_le_mul_right (by linarith) hwpos

/-- Clause 4b: the faithful average is NOT injective — genuine coarsening. The kernel element is the
su(2)-valued image of `QcEquation`'s scalar one (`∂₀λ₀` with `λ₀(x) = x₀ mod ell`), so the counting is
inherited rather than redone: `lineCoarseRestrictSuTwo_smul_fixed` reduces it to
`QcEquation.lineCoarseRestrict_gradValue_kerLam`. -/
theorem qc_not_injective {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ¬ Function.Injective (qcCLM (trivialU L) ell) := by
  have hell : 0 < ell := by omega
  have hzero : qcCLM (trivialU L) ell
      ((fun e => gradValue (kerLam ell) e • suTwoWitness : FineField L)) = 0 := by
    funext b
    show lineCoarseRestrictCov (trivialU L) ell
      (fun e => gradValue (kerLam ell) e • suTwoWitness) b = (0 : CoarseField L ell) b
    rw [lineCoarseRestrictCov_trivialU, lineCoarseRestrictSuTwo_smul_fixed,
      lineCoarseRestrict_gradValue_kerLam hell hdvd, zero_smul]
    rfl
  intro hinj
  have hz0 : qcCLM (trivialU L) ell (0 : FineField L) = 0 := map_zero _
  have hA0 : (fun e => gradValue (kerLam ell) e • suTwoWitness : FineField L) = (0 : FineField L) :=
    hinj (hzero.trans hz0.symm)
  have h1 : (fun e => gradValue (kerLam ell) e • suTwoWitness : FineField L)
      (originSite L, (0 : Fin 3)) = suTwoWitness := by
    show gradValue (kerLam ell) (originSite L, (0 : Fin 3)) • suTwoWitness = suTwoWitness
    rw [gradValue_kerLam_origin hell2 hdvd, one_smul]
  rw [hA0] at h1
  exact suTwoWitness_ne_zero (h1.symm.trans rfl)

/-- Clause 6: the transfer operator is NOT zero. This is the clause `Claim18Carrier` ADDED to kill the
zero-transfer degeneracy, and the real `C⁽²⁾` passes it — the section's support is every bond at
`μ`-offset `ell − 1`, of which the eliminated (dropped) bonds are only the fraction whose transverse
coordinates are multiples of `ell`, so `C⁽²⁾` is the identity on most of `range 𝒬_c⁻¹`. -/
theorem transfer_ne_zero {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    cTwoCLM (trivialU L) ell ∘L suTwoLiftCLM L ell ≠ 0 := by
  intro hz
  have h := opNorm_transfer_eq (L := L) hell2 hdvd
  rw [hz, norm_zero] at h
  have h2 : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell2
  linarith [ell_le_cube_sub hell2, h]

#print axioms suTwoLift_injective
#print axioms norm_qc_apply_le
#print axioms opNorm_qc_le_one
#print axioms qc_clause3
#print axioms one_le_opNorm_cTwo
#print axioms qc_not_injective
#print axioms transfer_ne_zero

/-! ## §10 — THE MEASUREMENT: an IFF, so the decision is not an estimate

With every operator supplied, the six-clause bundle is EQUIVALENT to a single numerical inequality
between two computed quantities: the transfer operator's actual norm `ell³ − ell` and Claim 18's own
bound `Lreal^(d−1)`. Five clauses impose nothing (they are §3/§9's theorems), and the sixth is exactly
that inequality. This is the analogue of `QcEquation.suppliedClauses_iff` with the LAST operator pinned
— and where that one left three inequalities about a free operator, this one leaves no freedom at all. -/
theorem fullySupplied_iff {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ) (hC : 0 ≤ Ccorr) (hα : 0 ≤ α₀) :
    FullySuppliedClauses L ell (trivialU L) Lreal d Ccorr α₀
      ↔ (ell : ℝ) ^ 3 - (ell : ℝ) ≤ Lreal ^ ((d : ℝ) - 1) := by
  have hell : 0 < ell := by omega
  constructor
  · intro h
    have h5 : ‖cTwoCLM (trivialU L) ell ∘L suTwoLiftCLM L ell‖ ≤ Lreal ^ ((d : ℝ) - 1) :=
      h.2.2.2.2.1
    rwa [opNorm_transfer_eq hell2 hdvd] at h5
  · intro hb
    refine ⟨qc_comp_suTwoLift hell hdvd, suTwoLift_injective hell hdvd,
      qc_clause3 hell hdvd Lreal Ccorr α₀ hC hα,
      ⟨fun _ => one_le_opNorm_cTwo hell2 hdvd (trivialU L), qc_not_injective hell2 hdvd⟩, ?_,
      transfer_ne_zero hell2 hdvd⟩
    rw [opNorm_transfer_eq hell2 hdvd]
    exact hb

#print axioms fullySupplied_iff

/-! ## §11 — `#print axioms` COMPLETENESS: every remaining declaration of this module

Every `theorem`, `def` and `instance` above already carries a `#print axioms` line except the
definitions, instances and small helper lemmas; they are printed here so the count is 67 of 67 and no
declaration in this module is unaudited. The carriers, the four normed instances and the two
finite-dimensionality instances are included on purpose: they are DATA the statements depend on, and
a `def`-level axiom leak would be invisible in the theorems' cones. -/

#print axioms FineField
#print axioms CoarseField
#print axioms instNormedAddCommGroupFineField
#print axioms instNormedSpaceFineField
#print axioms instNormedAddCommGroupCoarseField
#print axioms instNormedSpaceCoarseField
#print axioms instFiniteDimensionalFineField
#print axioms instFiniteDimensionalCoarseField
#print axioms coarseDelta
#print axioms fineDelta
#print axioms coarseDelta_same
#print axioms coarseDelta_ne
#print axioms fineDelta_same
#print axioms fineDelta_ne
#print axioms suTwoLift
#print axioms lastLayerLift_pos
#print axioms lastLayerLift_neg
#print axioms suTwoLift_factor
#print axioms suTwoLift_add
#print axioms suTwoLift_smul
#print axioms suTwoLiftLM
#print axioms suTwoLiftLM_apply
#print axioms suTwoLiftCLM
#print axioms suTwoLiftCLM_apply
#print axioms cTwoLM
#print axioms qcLM
#print axioms cTwoCLM
#print axioms qcCLM
#print axioms cTwoCLM_apply
#print axioms qcCLM_apply
#print axioms transfer_apply
#print axioms lineIntegralValue_eq_pathSite
#print axioms droppedBondLast_lastLayer
#print axioms FullySuppliedClauses
#print axioms cube_sub_nonneg
