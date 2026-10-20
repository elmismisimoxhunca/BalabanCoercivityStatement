/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CoarseRestrictTransported
import AdalyFormal.Balaban.Cmp98GammaPrimary

set_option autoImplicit false

/-!
# `QjComposite` — the COMPOSITE averaging `Q'_j`, CMP99b (3.19) FIRST line

**One operator, and nothing more.** This module builds the `j`-fold composition of transported site
averagings along an ABSTRACT background tower, together with its linearity, its reduction at `j = 1`
to the tree's existing one-step operator, its exact `Ad`-covariance, its locality on the box
`B^j(y)`, and its identification (at `j = 2`, explicitly) with CMP98 p.29's tower transport
`U(Γ^{(j)}_{y,x})`.

It builds no `Δ_k`, no RG ladder, and no coercivity statement. It does not close the denotation
dictionary's `Δ_k` MISMATCH row; it supplies one of the objects that row names as missing.

## The source, quoted, and WHICH line is built

CMP99b (3.19) has two lines. The corpus page is `corpus/pages/CMP99b_p393.md`
(`verification_status: single-read`), and the load-bearing reading was taken from the 400 dpi image
`corpus/renders/CMP99b_p393-05.png` (LAW-11), as recorded in
`CoarseRestrictTransported.lean`'s own header:

> `(Q'_j(U)λ)(y) = (Q'(Ū^{j-1})·····Q'(Ū)Q'(U)λ)(y) = Σ_{x∈B^j(y)} L^{-jd} R(U(Γ^{(j)}_{y,x})) λ(x)`

**This module builds the FIRST equality's left-hand structure — the composite.** It does NOT build
the second (`direct`) form, and it does not assert that the two agree; see §8.

### The ORDER is read off the display, not guessed

The printed product is `Q'(Ū^{j-1})·····Q'(Ū)Q'(U)`, acting on `λ` on the RIGHT. Operator products
compose right-to-left, so the FINE-level factor `Q'(U)` acts FIRST and the COARSEST factor
`Q'(Ū^{j-1})` acts LAST. Hence `Qcomposite bg ell (j+1) = (level-j step) ∘ Qcomposite bg ell j`
(`Qcomposite_succ`), with `bg 0 = U` the fine background. The same orientation is independently
fixed by CMP98 printed p.29's unnumbered display (quoted in `Cmp98GammaPrimary.lean`'s header),
whose transport `Ū₀^{j-1}(Γ_{x_j,x_{j-1}})·…·U₀(Γ_{x_1,x})` puts the coarsest factor LEFTMOST — and
§6 below proves our composite's transport is exactly that element at `j = 2`.

## The background tower is a PARAMETER — and WHICH source object it is meant to be

**There are two different barred objects in CMP98 and they must not be confused.** Corpus page
`corpus/pages/CMP98_p31.md` (`verification_status: single-read`, render
`corpus/renders/CMP98_p31-15.png`) records a DOUBLE-overline object `Ū̄₁^j` at (90)–(91), explicitly
flagged there as *"NOT literally `Ū^j`"* and distinct from the SINGLE-overline `Ū^k` of eq. (43).

The disambiguation is printed on the same page, and it is decisive. VERBATIM from
`corpus/pages/CMP98_p31.md`, the prose introducing (89):

> "the new `k`-th order averaging operation defined by the last expression in (88) is a composition
> of `k` averaging operations defined by (63) with properly chosen configurations `V₀`. More
> precisely, for a `j`-th factor in this composition, we take `V₀ = Ū₀^{j-1}`."

and immediately after (89):

> "We define inductively a sequence of averaging operations of `j`-th order composing `j` operations
> defined above for `V₀ = U₀, Ū₀, …, Ū₀^{j-1}` correspondingly."

So, in CMP98's own composite:

* the **backgrounds of the successive factors** are the SINGLE-bar tower `U₀, Ū₀, Ū₀², …, Ū₀^{j-1}`,
  i.e. the iterated order-`l` average of the *background* configuration `U₀`, whose defining formula
  is CMP98 eq. (43) on `corpus/pages/CMP98_p24.md` (`verification_status: adjudicated`);
* the **DOUBLE-bar `Ū̄₁^j`** of (90)–(91) is the *output* of the composite operation applied to the
  configuration `U₁` — the thing being averaged, NOT the background parameter.

**This module's `bg : ℕ → PeriodicLinkConfiguration (SU(2)) L` is intended to denote the SINGLE-bar
background tower, `bg l ≐ Ū₀^l`, with `bg 0 = U₀`** — the sequence CMP99b (3.19) writes as
`U, Ū, …, Ū^{j-1}`. **That identification is NOT PROVED HERE and is not claimed** — `bg` is and
remains a parameter of this module. (A tower satisfying the law §5 assumes IS built, one module
downstream, by `UbarTowerCov.UbarTower`; see item 1 and item 5 of "What is NOT claimed".) Two gaps
stand between the parameter and the source object, both stated rather than papered:

1. ~~The level-`l` tower `Ū₀^l` is not constructed anywhere in this tree — eq. (43) is a `log`/`exp`
   block average which nothing here builds —~~ so `bg` is genuinely free data, and every theorem
   below holds for EVERY tower, including towers that are not blocked averages of anything.
   **The inner struck clause was FALSE (S75, 2026-07-30)** and is retained only so the correction is
   visible: two declarations DO build a `log`/`exp` block average. `BlockedGauge.blockedGauge`
   (`BlockedGaugeCore.lean:538`) builds **CMP109 (0.4)** on the concrete lattice, and
   `BlockingLinkEstimate.blockedLink` (`:420`) builds **CMP98 (43)**'s formula in an abstract
   `(Finset ι, weights w, loops W, Uc)` form carrying the *estimate* rather than the lattice
   geometry. Neither is `Ū₀^l` for `l ≥ 2`.
   **THE OUTER CLAUSE IS NOW ALSO STRUCK (S75, same day, second correction).** The level-`l` tower
   `Ū₀^l` **is** constructed in this tree: `UbarTowerCov.UbarTower` in
   `Balaban/UbarTowerCovariance.lean`, which imports this module. Its contour family is a stated
   CHOICE (`TowerLawCov.coarseGammaPath`; CMP98 (14) defers `Γ_{c_-,x}` to "paper [2]"), so it is
   one faithful transcription of (43), not the unique one. What survives unchanged is the operative
   claim of this item: `bg` is free data *here*, because the module that constructs the tower is
   downstream of this one and cannot be imported by it.
2. CMP98's (88)–(92) is the **BOND/link sector** (a configuration at bonds of `Ω`, output at bonds of
   `Ω^{(k)}`), whereas CMP99b (3.19)'s `Q'_j` acts on a **SITE** field `λ` valued in `𝔰𝔲(2)`. The
   background sequence is transported across that sector boundary by NOTATION ONLY: (3.19) prints
   single bars in ascending order, matching the single-bar tower. No proof of the cross-sector
   identification is offered here.

**CMP98 eq. (63) is not needed by this construction, so its absence from the corpus is not a stop
for this module.** (63) defines the base one-step averaging of the BOND sector — the operation (89)
re-notates and (90) seeds. The one-step operator composed here is the SITE-sector `Q'` of CMP99b
(3.19) itself, already re-derived in `CoarseRestrictTransported` from (3.19) plus CMP98 p.24's
contour. A build of `Ū₀^l`, or of the double-bar bond-sector composite, WOULD need (63), and that
would be a hard stop.

~~Before parameterising, the tree was searched for an existing supplier (LAW-19):
`grep -rn "stride\|Ubar\|UBar\|barU"` over `formal/AdalyFormal/AdalyFormal` returns **no
blocked-background link field** anywhere.~~
**STRUCK 2026-07-30 (S75). THAT ABSENCE CLAIM IS FALSE, and the search is why.** The tree DOES
carry a blocked-background link field: `Balaban/BlockedGaugeCore.lean:630`
`BlockedGauge.blockedGaugeAsConfig P ell U : PeriodicLinkConfiguration G L`, CMP109 (0.4). The
grep above could not return it — that file names the object `blockedGauge`, and writes the bar in
**Unicode** (`Ū`), so no ASCII spelling of "Ubar" appears in it. This is the incident that added
**§READ-FIRST rule 6** to `compute/BUILD_STANDARDS.md`: *search by the CONCEPT — the type
signature, the operator's shape, the source equation number — and always run at least one search
that cannot match your own vocabulary.* Three such searches (raw-Unicode glyph; a sweep over every
declaration whose STATEMENT contains a gauge-transform token; a grep on source equation numbers)
are recorded in `compute/blockedgauge_ident/BGIdent.lean`. The surviving content of this paragraph
— that none of the objects listed below is the level-`l` tower `Ū₀^l` — is unaffected and stands;
what was wrong was the blanket absence claim. See item 5 of "What is NOT claimed" for what the
existing object is and why it still does not supply this file's `bg`.
`Balaban/BlockedGaugeAverage.lean` has `Ubar : G` — a single GROUP element characterised by the
Federbush condition `Σ log(U_j Ū⁻¹) = 0`, not a link configuration on a coarse lattice.
`Balaban/Averaging.lean` has `Ubar : FineConfig → CoarseConfig` inside the *definition of the
property* `GaugeCovariant`, with both config types abstract and no instance built.
`Balaban/BackgroundAveraging.lean` averages an `𝔰𝔲(2)`-valued BOND field (`qPrimeSuTwo`), not a
group-valued background. `Balaban/Cmp98GammaPrimary.lean` takes the tower as a parameter
`Ubar : ℕ → PeriodicLinkConfiguration …` exactly as here.

So the tower is taken as `bg : ℕ → PeriodicLinkConfiguration (SU(2)) L`, matching
`Cmp98Gamma.stepVar`'s own parameter convention, with `bg 0` the fine background. Nothing in this
file asserts that any particular `bg` is a blocked average of anything, and the name `bg` is
deliberately neutral: it wears neither bar.

## Which lattice each factor lives on: the STRIDED block, and why it is not optional

In the source, the level-`l` factor averages a field living on the level-`l` lattice (spacing
`ell^l`) over the `ell^d` level-`l` sites inside one level-`(l+1)` block. All fields in this tree
live on the single fine site space, so the level-`l` factor must average over the **strided** set
`{x : x_μ = y_μ + ell^l · i_μ, 0 ≤ i_μ < ell}` — `stepBlockOf y (ell^l) ell` in §1.

This is forced, and the naive alternative is WRONG: composing the tree's contiguous `blockOf … ell`
with itself sums over `y + m + n` with `0 ≤ m, n < ell`, i.e. a SMEARED box of side `2ell − 1` with
multiplicities, not the box `B²(y)` of side `ell²`. With the stride, the base-`ell` digit expansion
`x = y + Σ_l ell^l i_l` makes each point of `B^j(y)` reachable, and §6's locality theorem
(`Qcomposite_local`) proves the composite reads `λ` only on `blockOf y (ell^j)` — the source's
`B^j(y)`.

`stepBlockOf y 1 ell = blockOf y ell` (`stepBlockOf_one`), so the level-`0` factor is literally the
tree's existing operator; that is the content of `stepAverage_one` / `Qcomposite_one`.

## Reuse (LAW-19): four existing objects, no rebuilds

* `CoarseRestrictTransported.coarseRestrictSiteCovariantU` — the one-step transported averaging.
  **Not rebuilt**: `Qcomposite_one` proves the `j = 1` composite IS it.
* `TowerLawCov.coarsePathHolonomy` / `coarseGammaPath` / `coarsePathEndpoint` — the STRIDED
  holonomy, the strided staircase contour (same descending coordinate order `2,1,0` as the
  adjudicated `AdmissibleSubspace.staircasePath`), and its endpoint. **Not rebuilt.** §2 proves that
  at stride `1` this holonomy equals `CoarseRestrictTransported.staircaseTransport` — so the two
  contour encodings in the tree are the SAME object, not rivals.
* `Cmp98Gamma.stepVar` / `gammaVar` — the tree's tower-transport object. **Not rebuilt**: §7 proves
  our composite's transport is definitionally `stepVar`, and expands `j = 2` against `gammaVar`.
  §7 also states plainly that this is an INTERNAL identification, and that `gammaVar`'s own source
  attribution is currently unsettled (see "What is NOT claimed", item 1).
* `AdmissibleSubspace.blockOf` / `card_blockOf`'s bijection technique — the `ell^3` count is
  re-proved for the strided block by the same `Fin 3 → Fin ell` bijection, generalised.

## Hypotheses that travel

`blockOf` and `stepBlockOf` SILENTLY TRUNCATE at the torus boundary. Every cardinality/normalization
statement therefore carries a fitting hypothesis, and §1c proves it LOAD-BEARING rather than
decorative (`card_stepBlockOf_truncates` gives the actual count `8` and
`card_stepBlockOf_truncates_ne` gives `≠ ell^3 = 27`, on a concrete `(y, s, ell)` on `witnessL`), in
the same discipline as
`MinSwapWitness.sum_blockOf_coord_truncates` and `CoarseRestrictTransported.staircaseEndpoint_truncates`.

Term-by-term identities (linearity, covariance, the `U = 1` reduction, the `j = 2` expansion) carry
no such hypothesis and do not pretend to.

## What is NOT claimed

1. **No `Γ^{(j)}`, and its defining locus in CMP98 is currently UNSETTLED.** `Cmp98GammaPrimary.lean`
   attributes the object to an unnumbered display on CMP98 printed p.29, read from a single 300 dpi
   render (`compute/cmp98_gamma_o1/renders/CMP98_pdf13-13.png`) that is **not** a corpus page and has
   had no second read. Two later corpus measurements bear on it and neither confirms it:
   `corpus/pages/CMP98_p33.md` (`single-read`) shows (101)–(108) is a telescoping PROOF continuing
   from p.31's (92), whose `Γ`s are ordinary two-point contours used as arguments — **`Γ^{(j)}` is
   not defined there**; and `corpus/pages/CMP99b_p401.md` cites CMP98 **(52),(53)** for the
   telescoping it needs. The defining locus is estimated at CMP98 printed pp.26–29 and is **outside
   the corpus**. This file therefore uses `Cmp98Gamma.gammaVar` as an INTERNAL tree object (§6 is a
   Lean-level identification) and asserts nothing about which CMP98 equation it re-derives. No bond
   set is invented here.
2. **The composite is NOT claimed equal to the direct form** `Σ_{x∈B^j(y)} L^{-jd} R(U(Γ^{(j)}_{y,x}))λ(x)`
   as a single sum over `B^j(y)`. §7 proves the transport of each CHAIN `y = x_j, …, x_0 = x` is
   `gammaVar`; collapsing the nested chain sums into one sum over `B^j(y)` additionally needs the
   uniqueness of the ancestor chain, which is not proved here. §6's locality theorem is the honest
   partial statement: the composite depends on `λ` only through `B^j(y)`.
3. **The operator is FAMILY-DEPENDENT; covariance is FAMILY-INDEPENDENT.** Exactly as in
   `CoarseRestrictTransported`'s header: replacing the staircase family by another with the same
   endpoints multiplies each summand by `Ad` of a loop holonomy, which is `≠ 1` at curved
   backgrounds — so `Qcomposite` itself depends on the contour family, at every level. §5's
   covariance proof uses only that each level's contour is a connected strided chain from the anchor
   to the summand site, never WHICH chain, so covariance holds for any fixed family. Nothing here is
   stated uniformly over unrestricted backgrounds.
4. **No claim about `Δ_k`, no RG ladder, no coercivity, no `γ₀`, no CMP99b p.428.** This file closes
   no denotation-dictionary row.
5. **The tower's own gauge covariance is a DEFINITION *in this module*; it is a THEOREM one module
   downstream.** §4 transforms the tower by `coarseGaugeTransform (ell^l) γ (bg l)` — the formula
   CMP98 p.19 (11) asserts for the true blocked background. ~~Because `Ū^l` is not ingested, that
   `Ū^l(U^γ) = (Ū^l U)^{γ}` is not proved here and is not claimed.~~

   **STRUCK 2026-07-30 (S75), retained so the correction is visible. THE LAW IS NOW PROVED IN-TREE**
   — in `Balaban/UbarTowerCovariance.lean`, which imports this module:

   * `UbarTowerCov.stridedBlockedGauge` transcribes CMP98 (15) = (42) = (43) at a general stride;
   * `UbarTowerCov.UbarTower` iterates it at stride `ell^l`, which is (43)'s own recursion;
   * `UbarTowerCov.UbarTower_gauge` proves
     `UbarTower P ell (U^γ) l = coarseGaugeTransform (ell^l) γ (UbarTower P ell U l)` — the exact
     law disclaimed above, in THIS module's `coarseGaugeTransform`, unconditional in
     `ell, l, γ, U, P`, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`;
   * `UbarTowerCov.tower_feeds_Qcomposite` feeds that tower to §5's `Qcomposite_gaugeTransform`
     with the definitional transformation law replaced by the proved one, so §5's assumption is
     DISCHARGED for this tower and no assumption is left standing there.

   **What remains true of THIS module, and why the sentence above was struck rather than deleted.**
   `bg` is a parameter here and stays one: the discharge necessarily lives DOWNSTREAM (the proving
   module imports this one, so this one cannot import it), and every theorem below therefore still
   holds for EVERY tower, including towers that are not blocked averages of anything. What changed
   is that the tree now exhibits at least one `bg` for which the assumed law is a theorem, so §5 is
   no longer known only to be non-vacuous by fiat.

   **The object proved about is the CMP98 (43) SINGLE-BAR tower `Ū^l`, and it is NOT
   `BlockedGauge.blockedGauge`.** `blockedGauge` is **CMP109 (0.4)**, settled as a DIFFERENT object;
   do not read `UbarTower_gauge` as a statement about it. The two source differences below are the
   reason, and `UbarTowerCovariance.lean` turns each into a decidable fact about this tree's own
   encodings: `contourFamily_card_ge_two` with its control `contourFamily_card_axis`, and
   `blockOf_ne_stepBlockOf` with `card_blockOf_four = 64` against `card_stepBlockOf_two_two = 8`.

   **AMENDED 2026-07-30 — the tree also has five ANALOGOUS theorems, and the reason none of THEM
   transfers is a SOURCE difference, not a type or notation difference.**

   *What the tree already proves.* `BlockedGaugeCore.lean:586`
   `blockedGauge_gauge : blockedGauge P ell (U^γ) c = coarseGaugeTransform ell γ (blockedGauge P ell U) c`
   (plus `centeredBlockedGauge_gauge`, `su2_centeredBlockedGauge_gauge`,
   `su2_blockedGauge_gauge_concrete`, `contourAverage_gauge`). And the two apparent gaps to §5 are
   both ZERO, checked by the kernel in `compute/blockedgauge_ident/BGIdent.lean`:
   `BlockedGauge.CoarseBond L → G` **IS** `PeriodicLinkConfiguration G L` (`rfl`, no axioms), and
   `BlockedGauge.coarseGaugeTransform` **IS** the `coarseGaugeTransform` of §5 below
   (`coarseGaugeTransform_eq`, via `coarseShift y m μ = shiftBy y μ m`). Note that §5's
   `coarseGaugeTransform` (defined in §5 of this file) is therefore a LAW-19 DUPLICATE of
   `BlockedGaugeCore.lean:545`.

   *Why it still does not transfer — two independent source differences.* `blockedGauge` is
   **CMP109 (0.4)**; this file's `bg l` denotes **CMP98 (43)**'s `Ū^l`.
   * (0.4) averages the loop logarithm over the contour FAMILIES `G(c_-,x) × G(c_+,x')` with
     weights `1/|G|`; CMP98 (15)=(42)=(43) uses ONE contour
     `Γ_{c,x} = Γ_{c_-,x} ∪ [x,x(c)] ∪ Γ_{x(c),c_+}`. Bałaban draws that distinction himself, in
     the paragraph directly beneath (0.4) on CMP109 printed p.253 (read at 400 dpi on
     `corpus/renders/CMP109_p253-05.png`, sha256 `5462ae7f…`): *"A natural idea … would be to use
     variables obtained by averaging the contour variables `{U(Γ)}_{Γ∈G(y,x)}`, rather than to use
     one contour variable `U(Γ_{y,x})`."*
   * (0.4) is pinned to `c ∈ T^{(1)}` — the FIRST level. CMP98 (43) re-bases every level:
     `Ū^{k+1}` is the blocking of `Ū^k` *"where the contours `Γ_{c,x}` are defined on the lattice
     `Ω^{(k)}`"* (printed p.24, `corpus/pages/CMP98_p24.md`, `adjudicated`), i.e. at spacing
     `ell^k`. `blockedGauge P ell` uses FINE-unit `contourFamily`/`straightSeg`/`blockOf` at every
     `ell` — a fact `BlockedGaugeCore.blockedGaugeAsConfig`'s own docstring already states.

   *Provenance of the downstream proof.* The construction was first kernel-checked as an exhibit at
   `compute/blockedgauge_ident/` (`BGIdent.lean` + `QjBridge.lean`, commit `12cb000a`), where it had
   to re-declare thirteen of this module's declarations verbatim because a file under `compute/` has
   no package context. ~~Landing the construction in `formal/` is separate work and was outside the
   lane's write scope; until it lands, `bg` here remains free data and item 5's first paragraph is
   the operative statement for THIS file.~~ **STRUCK 2026-07-30 (S75): it landed**, as
   `Balaban/UbarTowerCovariance.lean`, and every one of those re-declarations collapsed into the
   import — the three `rfl` transcription bridges the exhibit carried are gone because there is now
   nothing to bridge. `bg` remaining free data in THIS file is still true and is now a scoping fact
   about the import direction, not a statement about what is proved (see item 5 above).
-/

namespace AdalyFormal.Balaban.QjComposite

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf inBlock CoarseLattice
  corner1 corner2 witnessL witnessY witnessEll)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one RMap_mul_apply suTwoWitness
  suTwoWitness_ne_zero witnessMElem RMap_witnessMElem witnessU witnessU_at_x_mu)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU coarseRestrictSiteCovariant
  RMap_apply_inv_cancel)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath
  coarseCoordSteps coarseStraightSegment coarsePathHolonomy_trivialU coarseGammaPath_self)
open AdalyFormal.Balaban.CoarseRestrictTransported (axisBonds pathTransport staircaseBonds
  staircaseTransport pathSite_of_le pathSite_leg2 pathSite_leg1 pathSite_leg0
  coarseRestrictSiteCovariantU coarseRestrictSiteCovariantU_add coarseRestrictSiteCovariantU_smul
  RMap_inv_apply_cancel corner1_apply_one corner2_apply_zero
  coarseRestrictSiteCovariantU_trivialU_eq sepU sepLam sepLam_flat_value
  sepLam_transported_ne_zero axisBonds_succ pathTransport_append pathTransport_singleton)
open AdalyFormal.Balaban.Cmp98Gamma (gammaVarOf gammaVarOf_zero gammaVarOf_succ stepVar gammaVar)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the STRIDED block `B_s(y)`

The level-`l` factor of the composite averages over the level-`l` sites of one level-`(l+1)` block:
coordinatewise `x_μ = y_μ + s·i_μ` with `0 ≤ i_μ < ell` and `s = ell^l`. Stated as a coordinate
condition so that `s = 1` reduces to `AdmissibleSubspace.inBlock` on the nose. -/

/-- **`x ∈ B_s(y)`** — `x` lies in the `s`-strided box of `ell` steps per axis based at `y`. The
three conjuncts are: forward orientation, box width `s·ell`, and landing on the stride sublattice. -/
abbrev inStepBlock (y : PeriodicLatticeSite L) (s ell : ℕ) (x : PeriodicLatticeSite L) : Prop :=
  ∀ μ : Fin 3, (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + s * ell ∧
    s ∣ ((x μ).val - (y μ).val)

/-- `B_s(y)` as a `Finset`. -/
def stepBlockOf (y : PeriodicLatticeSite L) (s ell : ℕ) : Finset (PeriodicLatticeSite L) :=
  Finset.univ.filter (inStepBlock y s ell)

theorem mem_stepBlockOf {y x : PeriodicLatticeSite L} {s ell : ℕ} :
    x ∈ stepBlockOf y s ell ↔ inStepBlock y s ell x := by
  simp [stepBlockOf]

/-- **At stride `1` the strided block IS the tree's block.** So the level-`0` factor of the
composite is literally the existing one-step operator — this is what makes `Qcomposite_one` a
reduction rather than a coincidence. -/
theorem stepBlockOf_one (y : PeriodicLatticeSite L) (ell : ℕ) :
    stepBlockOf y 1 ell = blockOf y ell := by
  ext x
  constructor
  · intro hx
    rw [mem_blockOf]
    intro μ
    have h := mem_stepBlockOf.mp hx μ
    exact ⟨h.1, by omega⟩
  · intro hx
    rw [mem_stepBlockOf]
    intro μ
    have h := mem_blockOf.mp hx μ
    exact ⟨h.1, by omega, one_dvd _⟩

/-- The anchor is always in its own strided block. -/
theorem self_mem_stepBlockOf (y : PeriodicLatticeSite L) {s ell : ℕ} (hell : 0 < ell)
    (hs : 0 < s) : y ∈ stepBlockOf y s ell := by
  rw [mem_stepBlockOf]
  intro μ
  refine ⟨le_refl _, ?_, by simp⟩
  have : 1 ≤ s * ell := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-! ### §1b — the count, and the fitting hypothesis it needs -/

/-- **`|B_s(y)| = ell^3`**, given that the strided box fits inside the periodic extent. Same
bijection technique as `AdmissibleSubspace.card_blockOf` (LAW-19), generalised to stride `s`: the
index map is `f ↦ (μ ↦ y_μ + s·f_μ)` on `Fin 3 → Fin ell`. -/
theorem card_stepBlockOf (y : PeriodicLatticeSite L) (s ell : ℕ) (hs : 0 < s)
    (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1) :
    (stepBlockOf y s ell).card = ell ^ 3 := by
  have key : ∀ (μ : Fin 3) (i : ℕ), i < ell → (y μ).val + s * i < L μ + 1 := by
    intro μ i hi
    have h1 : s * (i + 1) ≤ s * ell := Nat.mul_le_mul_left s hi
    have h2 := hfit μ
    have : s * i + s ≤ s * ell := by rw [Nat.mul_add, Nat.mul_one] at h1; omega
    omega
  have hbij : stepBlockOf y s ell = Finset.image
      (fun f : Fin 3 → Fin ell => (fun μ : Fin 3 => (⟨(y μ).val + s * (f μ).val,
        key μ (f μ).val (f μ).isLt⟩ : Fin (L μ + 1)))) Finset.univ := by
    ext x
    simp only [mem_stepBlockOf, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hx
      refine ⟨fun μ => ⟨((x μ).val - (y μ).val) / s, ?_⟩, ?_⟩
      · have h := hx μ
        have hlt : (x μ).val - (y μ).val < ell * s := by
          have := h.2.1; rw [Nat.mul_comm] at this ⊢; omega
        exact (Nat.div_lt_iff_lt_mul hs).mpr hlt
      · funext μ
        have h := hx μ
        apply Fin.ext
        show (y μ).val + s * (((x μ).val - (y μ).val) / s) = (x μ).val
        rw [Nat.mul_div_cancel' h.2.2]
        omega
    · rintro ⟨f, rfl⟩
      intro μ
      refine ⟨by simp, ?_, ?_⟩
      · show (y μ).val + s * (f μ).val < (y μ).val + s * ell
        have : s * (f μ).val < s * ell := by
          have h1 : s * ((f μ).val + 1) ≤ s * ell := Nat.mul_le_mul_left s (f μ).isLt
          rw [Nat.mul_add, Nat.mul_one] at h1
          omega
        omega
      · show s ∣ ((y μ).val + s * (f μ).val - (y μ).val)
        rw [Nat.add_sub_cancel_left]
        exact dvd_mul_right s _
  rw [hbij, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fun]
  · simp
  · intro f g hfg
    funext μ
    have h := congrFun hfg μ
    apply Fin.ext
    have heq : (y μ).val + s * (f μ).val = (y μ).val + s * (g μ).val := congrArg Fin.val h
    exact Nat.eq_of_mul_eq_mul_left hs (by omega)

/-! ### §1c — the fitting hypothesis is LOAD-BEARING

`witnessL = (3,3,3)` (so each coordinate ranges over `Fin 4`). At `y = 0`, `s = 2`, `ell = 3` the
strided box would need width `s·ell = 6 > 4`: it wraps, and the count collapses from `27` to `8`.
Dropping `hfit` from `card_stepBlockOf` therefore makes it FALSE, and every normalization statement
below that divides by `ell^3` would be dividing by the wrong number. -/

/-- The concrete counterexample: `|B_2(0)|` with `ell = 3` on `witnessL` is `8`, not `3^3 = 27`. -/
theorem card_stepBlockOf_truncates :
    (stepBlockOf witnessY 2 3).card = 8 := by decide

theorem card_stepBlockOf_truncates_ne :
    (stepBlockOf witnessY 2 3).card ≠ 3 ^ 3 := by decide

/-- The same instance shows the fitting hypothesis genuinely fails there. -/
theorem witnessY_not_fit : ¬ (∀ μ : Fin 3, (witnessY μ).val + 2 * 3 ≤ witnessL μ + 1) := by decide

/-! ### §1d — the strided block sits inside the box `B^{j+1}(y)`

`stepBlockOf y (ell^j) ell ⊆ blockOf y (ell^(j+1))`, and each summand's own `ell^j`-box also sits
inside it. These two inclusions are what §6's locality theorem runs on. -/

theorem stepBlockOf_subset_blockOf {y : PeriodicLatticeSite L} {s ell : ℕ} :
    stepBlockOf y s ell ⊆ blockOf y (s * ell) := by
  intro x hx
  rw [mem_blockOf]
  intro μ
  have h := mem_stepBlockOf.mp hx μ
  exact ⟨h.1, h.2.1⟩

theorem blockOf_subset_of_mem_stepBlockOf {y x : PeriodicLatticeSite L} {s ell : ℕ}
    (hx : x ∈ stepBlockOf y s ell) :
    blockOf x s ⊆ blockOf y (s * ell) := by
  intro z hz
  rw [mem_blockOf] at hz ⊢
  intro μ
  have hxm := mem_stepBlockOf.mp hx μ
  have hzm := hz μ
  -- `x_μ ≤ y_μ + s·(ell−1)` since `x_μ − y_μ` is a multiple of `s` strictly below `s·ell`
  obtain ⟨q, hq⟩ := hxm.2.2
  have hxy : (x μ).val = (y μ).val + s * q := by omega
  have hqlt : q < ell := by
    by_contra hcon
    have : s * ell ≤ s * q := Nat.mul_le_mul_left s (Nat.le_of_not_lt hcon)
    omega
  have hstep : s * q + s ≤ s * ell := by
    have h1 : s * (q + 1) ≤ s * ell := Nat.mul_le_mul_left s hqlt
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega
  exact ⟨by omega, by omega⟩

/-- `B(y)` at side `1` is the single point `y` — the `j = 0` base case of locality. -/
theorem blockOf_one_eq_singleton (y : PeriodicLatticeSite L) : blockOf y 1 = {y} := by
  ext x
  rw [mem_blockOf, Finset.mem_singleton]
  constructor
  · intro hx
    funext μ
    apply Fin.ext
    have := hx μ
    omega
  · rintro rfl
    intro μ
    omega

#print axioms inStepBlock
#print axioms stepBlockOf
/-! ### §1e — THE DEGENERATE VALUES OF `ell`, MADE EXPLICIT

Every general theorem below quantifies over `ell` with no lower bound, and at `ell ∈ {0, 1}` those
theorems are TRUE BUT CONTENT-FREE. Leaving that unstated is exactly the "a free parameter decides
the statement" hazard, so the two collapses are PROVED here rather than left for a reader to notice:

* `ell = 0`: every strided block is empty and the composite is identically `0` from `j = 1` on
  (`Qcomposite_ell_zero`), so e.g. covariance degenerates to `0 = Ad(γ)0`.
* `ell = 1`: every strided block is the singleton `{y}`, the contour is empty, and the composite is
  the IDENTITY at every `j` (`Qcomposite_ell_one`), so covariance degenerates to `Ad(γ)λ = Ad(γ)λ`.

The content therefore lives at `ell ≥ 2`, and §8b exhibits a genuine separation there (at `ell = 2`,
on the tree's own witness lattice) — so no general theorem below is vacuous, only its `ell ≤ 1`
instances are. No statement is weakened to avoid this; the hypotheses stay as general as they are
true. -/

theorem not_mem_stepBlockOf_ell_zero (y x : PeriodicLatticeSite L) (s : ℕ) :
    x ∉ stepBlockOf y s 0 := by
  intro hx
  have h := mem_stepBlockOf.mp hx 0
  have h1 := h.1
  have h2 := h.2.1
  rw [Nat.mul_zero] at h2
  omega

/-- At `ell = 1` the strided block is a single point, whatever the stride. -/
theorem stepBlockOf_one_one (y : PeriodicLatticeSite L) : stepBlockOf y 1 1 = {y} := by
  ext x
  rw [mem_stepBlockOf, Finset.mem_singleton]
  constructor
  · intro hx
    funext μ
    apply Fin.ext
    have h := hx μ
    have h1 := h.1
    have h2 := h.2.1
    omega
  · rintro rfl
    intro μ
    exact ⟨le_refl _, by omega, by simp⟩

#print axioms not_mem_stepBlockOf_ell_zero
#print axioms stepBlockOf_one_one

#print axioms mem_stepBlockOf
#print axioms stepBlockOf_one
#print axioms self_mem_stepBlockOf
#print axioms card_stepBlockOf
#print axioms card_stepBlockOf_truncates
#print axioms card_stepBlockOf_truncates_ne
#print axioms witnessY_not_fit
#print axioms stepBlockOf_subset_blockOf
#print axioms blockOf_subset_of_mem_stepBlockOf
#print axioms blockOf_one_eq_singleton

/-! ## §2 — the stride-`1` bridge: `coarsePathHolonomy 1 = staircaseTransport`

The tree carries TWO encodings of the axial staircase transport: `TowerLawCov.coarsePathHolonomy`
(a list of DIRECTIONS, stepping by `ell` fine sites) and `CoarseRestrictTransported.pathTransport`
along `staircaseBonds` (a list of BONDS, stepping by one). They use the same descending coordinate
order `2, 1, 0` and the same corner sites. This section proves they agree at stride `1`, so this
module introduces no third convention, and `Qcomposite_one` lands on the tree's existing operator
rather than on a look-alike. -/

theorem coarseShift_one (y : PeriodicLatticeSite L) (μ : Fin 3) :
    coarseShift y 1 μ = pathSite y μ 1 := rfl

/-- `pathSite` composes: walking `a` then `b` steps is walking `b + a` steps. -/
theorem pathSite_add (y : PeriodicLatticeSite L) (μ : Fin 3) (a b : ℕ) :
    pathSite (pathSite y μ a) μ b = pathSite y μ (b + a) := by
  show (fun z => periodicLatticeShift z μ)^[b] ((fun z => periodicLatticeShift z μ)^[a] y) = _
  rw [← Function.iterate_add_apply]
  rfl

theorem coarsePathHolonomy_nil {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L) :
    coarsePathHolonomy s V y [] = 1 := rfl

theorem coarsePathHolonomy_cons {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (rest : List (Fin 3)) :
    coarsePathHolonomy s V y (μ :: rest)
      = V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) rest := rfl

theorem coarsePathEndpoint_cons (s : ℕ) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (rest : List (Fin 3)) :
    coarsePathEndpoint s y (μ :: rest) = coarsePathEndpoint s (coarseShift y s μ) rest := rfl

theorem coarsePathEndpoint_append (s : ℕ) (y : PeriodicLatticeSite L) (p q : List (Fin 3)) :
    coarsePathEndpoint s y (p ++ q)
      = coarsePathEndpoint s (coarsePathEndpoint s y p) q := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih => rw [List.cons_append, coarsePathEndpoint_cons, coarsePathEndpoint_cons, ih]

theorem coarsePathHolonomy_append {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L) (p q : List (Fin 3)) :
    coarsePathHolonomy s V y (p ++ q)
      = coarsePathHolonomy s V y p * coarsePathHolonomy s V (coarsePathEndpoint s y p) q := by
  induction p generalizing y with
  | nil =>
      rw [List.nil_append]
      show _ = 1 * _
      rw [one_mul]
      rfl
  | cons μ rest ih =>
      rw [List.cons_append, coarsePathHolonomy_cons, coarsePathHolonomy_cons, ih,
        coarsePathEndpoint_cons, mul_assoc]

/-- **The strided path endpoint, in closed form**: `n` unit-steps of length `s` in direction `μ`
land on `pathSite y μ (s·n)`. -/
theorem coarsePathEndpoint_replicate (s : ℕ) (y : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    coarsePathEndpoint s y (List.replicate n μ) = pathSite y μ (s * n) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, coarsePathEndpoint_cons]
      show coarsePathEndpoint s (pathSite y μ s) (List.replicate n μ) = _
      rw [ih, pathSite_add, Nat.mul_succ]

/-- **A single axial leg agrees**, at stride `1`, between the two encodings. Both are grown from the
FAR end (`List.replicate_succ'` against `CoarseRestrictTransported.axisBonds_succ`), so the induction
never has to reassociate a noncommutative product. -/
theorem coarsePathHolonomy_one_replicate {G : Type*} [Group G]
    (V : PeriodicLinkConfiguration G L) (base : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    coarsePathHolonomy 1 V base (List.replicate n μ) = pathTransport V (axisBonds base μ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ', coarsePathHolonomy_append, ih, coarsePathEndpoint_replicate,
        Nat.one_mul, axisBonds_succ, pathTransport_append, pathTransport_singleton]
      show _ * (V (pathSite base μ n, μ) * 1) = _
      rw [mul_one]

/-- The strided step-count at stride `1` is the plain coordinate difference, under forward
orientation (`Fin` subtraction is exact there). -/
theorem coarseCoordSteps_one {y x : PeriodicLatticeSite L} (μ : Fin 3)
    (h : (y μ).val ≤ (x μ).val) :
    coarseCoordSteps 1 y x μ = (x μ).val - (y μ).val := by
  unfold coarseCoordSteps
  rw [Nat.div_one, Fin.sub_val_of_le (Fin.le_def.mpr h)]

/-- **`coarseGammaPath` at stride `1`, unfolded** into the three replicate legs with the tree's
corner sites. -/
theorem coarseGammaPath_one_eq {y x : PeriodicLatticeSite L}
    (h : ∀ μ : Fin 3, (y μ).val ≤ (x μ).val) :
    coarseGammaPath 1 y x = List.replicate ((x 2).val - (y 2).val) 2 ++
      (List.replicate ((x 1).val - (y 1).val) 1 ++
        List.replicate ((x 0).val - (y 0).val) 0) := by
  unfold coarseGammaPath coarseStraightSegment
  have h1 : coarseCoordSteps 1 y x 2 = (x 2).val - (y 2).val := coarseCoordSteps_one 2 (h 2)
  have hc1 : (Function.update y 2 (x 2) : PeriodicLatticeSite L) 1 = y 1 := corner1_apply_one y x
  have h2 : coarseCoordSteps 1 (Function.update y 2 (x 2)) x 1 = (x 1).val - (y 1).val := by
    have hh := coarseCoordSteps_one (y := (Function.update y 2 (x 2) : PeriodicLatticeSite L))
      (x := x) 1 (by rw [hc1]; exact h 1)
    rw [hh, hc1]
  have hc2 : (Function.update (Function.update y 2 (x 2)) 1 (x 1) : PeriodicLatticeSite L) 0
      = y 0 := corner2_apply_zero y x
  have h3 : coarseCoordSteps 1 (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0
      = (x 0).val - (y 0).val := by
    have hh := coarseCoordSteps_one
      (y := (Function.update (Function.update y 2 (x 2)) 1 (x 1) : PeriodicLatticeSite L))
      (x := x) 0 (by rw [hc2]; exact h 0)
    rw [hh, hc2]
  rw [h1, h2, h3]

/-- **THE STRIDE-`1` BRIDGE.** The strided holonomy along `coarseGammaPath` at stride `1` IS
`CoarseRestrictTransported.staircaseTransport`. Both encodings of the CMP98 p.24 axial staircase
denote the same group element. -/
theorem coarsePathHolonomy_one_eq_staircaseTransport {G : Type*} [Group G]
    (V : PeriodicLinkConfiguration G L) {y x : PeriodicLatticeSite L}
    (h : ∀ μ : Fin 3, (y μ).val ≤ (x μ).val) :
    coarsePathHolonomy 1 V y (coarseGammaPath 1 y x) = staircaseTransport V y x := by
  rw [coarseGammaPath_one_eq h, coarsePathHolonomy_append, coarsePathHolonomy_append,
    coarsePathHolonomy_one_replicate, coarsePathHolonomy_one_replicate,
    coarsePathHolonomy_one_replicate, coarsePathEndpoint_replicate, coarsePathEndpoint_replicate,
    one_mul, one_mul, pathSite_leg2 (h 2), pathSite_leg1 (h 1)]
  show _ = pathTransport V (staircaseBonds y x)
  unfold staircaseBonds
  rw [pathTransport, pathTransport, pathTransport, pathTransport, List.append_assoc,
    List.map_append, List.map_append, List.prod_append, List.prod_append]

#print axioms coarsePathEndpoint_append
#print axioms coarsePathHolonomy_append
#print axioms coarsePathEndpoint_replicate
#print axioms coarsePathHolonomy_one_replicate
#print axioms coarseGammaPath_one_eq
#print axioms coarsePathHolonomy_one_eq_staircaseTransport

#print axioms coarseShift_one
#print axioms pathSite_add
#print axioms coarsePathHolonomy_nil
#print axioms coarsePathHolonomy_cons
#print axioms coarsePathEndpoint_cons
#print axioms coarseCoordSteps_one

/-! ## §3 — the level-`l` FACTOR `Q'(V)` at stride `s`

One factor of the composite: the `U`-dependent block average of a site field, over the STRIDED block,
with the strided staircase transport in each summand. At `s = 1` it IS
`CoarseRestrictTransported.coarseRestrictSiteCovariantU` (`stepAverage_one`). -/

/-- **`(Q'_s(V)λ)(y) := ell^{-3} • Σ_{x ∈ B_s(y)} R(V(Γ^s_{y,x})) λ(x)`** — the level factor. -/
noncomputable def stepAverage (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) : SuTwo :=
  (1 / (ell : ℝ) ^ 3) • ∑ x ∈ stepBlockOf y s ell,
    RMap (coarsePathHolonomy s V y (coarseGammaPath s y x)) (lam x)

theorem stepAverage_add (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam1 lam2 : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    stepAverage s V ell (lam1 + lam2) y = stepAverage s V ell lam1 y + stepAverage s V ell lam2 y := by
  simp only [stepAverage, Pi.add_apply, map_add]
  rw [← smul_add, ← Finset.sum_add_distrib]

theorem stepAverage_smul (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) (c : ℝ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    stepAverage s V ell (c • lam) y = c • stepAverage s V ell lam y := by
  simp only [stepAverage, Pi.smul_apply, map_smul]
  rw [smul_comm, ← Finset.smul_sum]

/-- **The level-`0` factor IS the tree's existing one-step operator.** Not a look-alike: the block
coincides (`stepBlockOf_one`) and the transport coincides (§2's bridge). -/
theorem stepAverage_one
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    stepAverage 1 V ell lam y = coarseRestrictSiteCovariantU V ell lam y := by
  unfold stepAverage coarseRestrictSiteCovariantU
  rw [stepBlockOf_one]
  exact congrArg (fun z => (1 / (ell : ℝ) ^ 3) • z)
    (Finset.sum_congr rfl (fun x hx => by
      rw [coarsePathHolonomy_one_eq_staircaseTransport V (fun μ => (mem_blockOf.mp hx μ).1)]))

/-- At the trivial background every transport is `1`, and the factor is the flat strided average. -/
theorem stepAverage_trivialU (s ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo)
    (y : PeriodicLatticeSite L) :
    stepAverage s (trivialU L) ell lam y
      = (1 / (ell : ℝ) ^ 3) • ∑ x ∈ stepBlockOf y s ell, lam x := by
  unfold stepAverage
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [coarsePathHolonomy_trivialU, RMap_one]
  rfl

/-- **The normalization is a genuine `ell^{-d}` average.** On the covariantly constant mode — the
field whose value at `x` is the back-transport of a fixed `v` — the factor returns `v` exactly. A
different exponent, or a dropped fitting hypothesis (§1c), breaks this. -/
theorem stepAverage_covariantly_constant
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {s ell : ℕ}
    (hs : 0 < s) (hell : 0 < ell) {y : PeriodicLatticeSite L}
    (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1) (v : SuTwo) :
    stepAverage s V ell
        (fun x => RMap ((coarsePathHolonomy s V y (coarseGammaPath s y x))⁻¹) v) y = v := by
  unfold stepAverage
  have hterm : ∀ x ∈ stepBlockOf y s ell,
      RMap (coarsePathHolonomy s V y (coarseGammaPath s y x))
        (RMap ((coarsePathHolonomy s V y (coarseGammaPath s y x))⁻¹) v) = v :=
    fun x _ => RMap_apply_inv_cancel _ v
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_stepBlockOf y s ell hs hfit]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hne : ((ell : ℝ)) ^ 3 ≠ 0 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  push_cast
  rw [one_div, inv_mul_cancel₀ hne, one_smul]

#print axioms stepAverage
#print axioms stepAverage_add
#print axioms stepAverage_smul
#print axioms stepAverage_one
#print axioms stepAverage_trivialU
#print axioms stepAverage_covariantly_constant

/-! ## §4 — `Q'_j`: the COMPOSITE

`Q'_j(U) = Q'(Ū^{j-1})·····Q'(Ū)Q'(U)` — the fine factor acts FIRST (rightmost), the coarsest LAST.
The level-`l` factor uses background `bg l` at stride `ell^l`. -/

/-- **The composite averaging, CMP99b (3.19) first line.** `bg 0` is the fine background. -/
noncomputable def Qcomposite
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) :
    ℕ → (PeriodicLatticeSite L → SuTwo) → (PeriodicLatticeSite L → SuTwo)
  | 0 => fun lam => lam
  | (j + 1) => fun lam => stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam)

/-- `Q'_0 = id`: the empty product of averagings. -/
theorem Qcomposite_zero
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) : Qcomposite bg ell 0 lam = lam := rfl

/-- **THE COMPOSITION LAW, in the orientation (3.19) forces**: the NEW factor is the COARSEST one
and is applied LAST, on the outside. -/
theorem Qcomposite_succ
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell j : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) :
    Qcomposite bg ell (j + 1) lam
      = stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam) := rfl

/-- **`Q'_1 = Q'(U)`** — the `j = 1` composite is exactly the tree's existing one-step transported
averaging at the fine background `bg 0`. -/
theorem Qcomposite_one
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) :
    Qcomposite bg ell 1 lam = coarseRestrictSiteCovariantU (bg 0) ell lam := by
  funext y
  show stepAverage (ell ^ 0) (bg 0) ell lam y = _
  rw [pow_zero, stepAverage_one]

/-! ### §4a — LINEARITY, by induction on the number of factors -/

theorem Qcomposite_add
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell j : ℕ)
    (lam1 lam2 : PeriodicLatticeSite L → SuTwo) :
    Qcomposite bg ell j (lam1 + lam2) = Qcomposite bg ell j lam1 + Qcomposite bg ell j lam2 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      funext y
      show stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j (lam1 + lam2)) y = _
      rw [ih]
      exact stepAverage_add _ _ _ _ _ _

theorem Qcomposite_smul
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell j : ℕ)
    (c : ℝ) (lam : PeriodicLatticeSite L → SuTwo) :
    Qcomposite bg ell j (c • lam) = c • Qcomposite bg ell j lam := by
  induction j with
  | zero => rfl
  | succ j ih =>
      funext y
      show stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j (c • lam)) y = _
      rw [ih]
      exact stepAverage_smul _ _ _ _ _ _

/-- The composite as a genuine `LinearMap`. -/
noncomputable def QcompositeLM
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell j : ℕ) :
    (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo) where
  toFun lam := Qcomposite bg ell j lam
  map_add' := Qcomposite_add bg ell j
  map_smul' c lam := Qcomposite_smul bg ell j c lam

theorem QcompositeLM_apply
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell j : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) :
    QcompositeLM bg ell j lam = Qcomposite bg ell j lam := rfl

#print axioms Qcomposite
#print axioms QcompositeLM
/-! ### §4b — the two degenerate towers of §1e, now at the level of the composite -/

/-- At `ell = 0` the composite ANNIHILATES everything from `j = 1` on. -/
theorem stepAverage_ell_zero (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    stepAverage s V 0 lam y = 0 := by
  unfold stepAverage
  rw [Finset.sum_eq_zero (fun x hx => absurd hx (not_mem_stepBlockOf_ell_zero y x s)), smul_zero]

theorem Qcomposite_ell_zero
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (j : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    Qcomposite bg 0 (j + 1) lam y = 0 := by
  show stepAverage (0 ^ j) (bg j) 0 (Qcomposite bg 0 j lam) y = 0
  exact stepAverage_ell_zero _ _ _ _

/-- At `ell = 1` the composite is the IDENTITY at every `j`. -/
theorem Qcomposite_ell_one
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (j : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) :
    Qcomposite bg 1 j lam = lam := by
  induction j with
  | zero => rfl
  | succ j ih =>
      funext y
      show stepAverage (1 ^ j) (bg j) 1 (Qcomposite bg 1 j lam) y = lam y
      rw [ih, one_pow]
      unfold stepAverage
      rw [stepBlockOf_one_one, Finset.sum_singleton, coarseGammaPath_self, coarsePathHolonomy_nil,
        RMap_one]
      simp

#print axioms stepAverage_ell_zero
#print axioms Qcomposite_ell_zero
#print axioms Qcomposite_ell_one

#print axioms Qcomposite_zero
#print axioms Qcomposite_succ
#print axioms Qcomposite_one
#print axioms Qcomposite_add
#print axioms Qcomposite_smul
#print axioms QcompositeLM_apply

/-! ## §5 — EXACT `Ad`-COVARIANCE OF THE COMPOSITE

The property the flat operator provably lacks, and the reason the composite is worth having. It is
inherited from the level factors: each factor's transport is `Ad`-equivariant along its own strided
contour, and the conjugations at the intermediate anchors cancel in pairs when the factors are
composed. Exact — no error term, no regularity, no divisibility. -/

/-- The gauge transform of a STRIDED background: the second gauge factor sits at the far end of the
STRIDED bond, not the fine neighbour. At `s = 1` it is the tree's `periodicGaugeTransform`. -/
def coarseGaugeTransform {G : Type*} [Group G] (s : ℕ) (γ : PeriodicLatticeSite L → G)
    (V : PeriodicLinkConfiguration G L) : PeriodicLinkConfiguration G L :=
  fun e => γ e.1 * V e * (γ (coarseShift e.1 s e.2))⁻¹

theorem coarseGaugeTransform_one {G : Type*} [Group G] (γ : PeriodicLatticeSite L → G)
    (V : PeriodicLinkConfiguration G L) :
    coarseGaugeTransform 1 γ V = periodicGaugeTransform γ V := rfl

/-- **The strided transporter is `Ad`-equivariant**: conjugation at the two ENDS of the path, all
intermediate factors telescoping away. Uses only that the path is a connected strided chain — never
which chain (family-independence of covariance). -/
theorem coarsePathHolonomy_coarseGaugeTransform {G : Type*} [Group G] (s : ℕ)
    (γ : PeriodicLatticeSite L → G) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    coarsePathHolonomy s (coarseGaugeTransform s γ V) y p
      = γ y * coarsePathHolonomy s V y p * (γ (coarsePathEndpoint s y p))⁻¹ := by
  induction p generalizing y with
  | nil =>
      show (1 : G) = γ y * 1 * (γ y)⁻¹
      group
  | cons μ rest ih =>
      rw [coarsePathHolonomy_cons, coarsePathHolonomy_cons, ih, coarsePathEndpoint_cons]
      simp only [coarseGaugeTransform]
      group

/-- `s · (number of strided steps) = coordinate difference`, when the difference is a multiple of the
stride. This is where the `s ∣ …` conjunct of `inStepBlock` does its work. -/
theorem mul_coarseCoordSteps {s : ℕ} {y x : PeriodicLatticeSite L} (μ : Fin 3)
    (hle : (y μ).val ≤ (x μ).val) (hdvd : s ∣ ((x μ).val - (y μ).val)) :
    s * coarseCoordSteps s y x μ = (x μ).val - (y μ).val := by
  unfold coarseCoordSteps
  rw [Fin.sub_val_of_le (Fin.le_def.mpr hle)]
  exact Nat.mul_div_cancel' hdvd

/-- **The strided staircase CLOSES at `x`** — under exactly the orientation-plus-divisibility
condition `inStepBlock` supplies. Drop either conjunct and the path lands somewhere else. -/
theorem coarsePathEndpoint_coarseGammaPath {s : ℕ} {y x : PeriodicLatticeSite L}
    (h : ∀ μ : Fin 3, (y μ).val ≤ (x μ).val ∧ s ∣ ((x μ).val - (y μ).val)) :
    coarsePathEndpoint s y (coarseGammaPath s y x) = x := by
  unfold coarseGammaPath coarseStraightSegment
  rw [coarsePathEndpoint_append, coarsePathEndpoint_append, coarsePathEndpoint_replicate,
    coarsePathEndpoint_replicate, coarsePathEndpoint_replicate]
  have h1 : s * coarseCoordSteps s y x 2 = (x 2).val - (y 2).val :=
    mul_coarseCoordSteps 2 (h 2).1 (h 2).2
  have hc1 : (Function.update y 2 (x 2) : PeriodicLatticeSite L) 1 = y 1 := corner1_apply_one y x
  have h2 : s * coarseCoordSteps s (Function.update y 2 (x 2)) x 1 = (x 1).val - (y 1).val := by
    have hh := mul_coarseCoordSteps (s := s)
      (y := (Function.update y 2 (x 2) : PeriodicLatticeSite L)) (x := x) 1
      (by rw [hc1]; exact (h 1).1) (by rw [hc1]; exact (h 1).2)
    rw [hh, hc1]
  have hc2 : (Function.update (Function.update y 2 (x 2)) 1 (x 1) : PeriodicLatticeSite L) 0
      = y 0 := corner2_apply_zero y x
  have h3 : s * coarseCoordSteps s (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0
      = (x 0).val - (y 0).val := by
    have hh := mul_coarseCoordSteps (s := s)
      (y := (Function.update (Function.update y 2 (x 2)) 1 (x 1) : PeriodicLatticeSite L))
      (x := x) 0 (by rw [hc2]; exact (h 0).1) (by rw [hc2]; exact (h 0).2)
    rw [hh, hc2]
  rw [h1, pathSite_leg2 (h 2).1, h2, pathSite_leg1 (h 1).1, h3, pathSite_leg0 (h 0).1]

/-- **One FACTOR is exactly `Ad`-covariant.** No error term, no curvature condition, no restriction
on the background. -/
theorem stepAverage_gaugeTransform (s : ℕ)
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    stepAverage s (coarseGaugeTransform s γ V) ell (fun x => RMap (γ x) (lam x)) y
      = RMap (γ y) (stepAverage s V ell lam y) := by
  have hsum : ∀ x ∈ stepBlockOf y s ell,
      RMap (coarsePathHolonomy s (coarseGaugeTransform s γ V) y (coarseGammaPath s y x))
          (RMap (γ x) (lam x))
        = RMap (γ y) (RMap (coarsePathHolonomy s V y (coarseGammaPath s y x)) (lam x)) := by
    intro x hx
    have hx' := mem_stepBlockOf.mp hx
    have hcancel : (γ y * coarsePathHolonomy s V y (coarseGammaPath s y x) * (γ x)⁻¹) * γ x
        = γ y * coarsePathHolonomy s V y (coarseGammaPath s y x) := by group
    rw [coarsePathHolonomy_coarseGaugeTransform,
      coarsePathEndpoint_coarseGammaPath (fun μ => ⟨(hx' μ).1, (hx' μ).2.2⟩),
      RMap_mul_apply, RMap_mul_apply, hcancel]
  unfold stepAverage
  rw [map_smul, map_sum, Finset.sum_congr rfl hsum]

/-- **THE COVARIANCE THEOREM FOR THE COMPOSITE.** `Q'_j` at the gauge-transformed tower, applied to
the gauge-transformed field, equals `Ad(γ(y))` of `Q'_j` at the original data — EXACTLY, at every
`j`, every `ell`, every anchor, every tower, every `γ`, with no hypothesis whatsoever.

The tower's transformation law is the DEFINITION `bg l ↦ coarseGaugeTransform (ell^l) γ (bg l)`,
i.e. the level-`l` background transforms by the same `γ` read at level-`l` spacing; this is the
formula CMP98 p.19 (11) asserts for the true blocked background, and it is NOT proved here ~~(the
blocked background is not built — see the header)~~.

**SUPERSEDED IN PART, 2026-07-30 (S75).** The parenthetical is false and is retained struck: the
blocked background IS built, one module downstream, as `UbarTowerCov.UbarTower`
(`Balaban/UbarTowerCovariance.lean`), and the law is PROVED there as
`UbarTowerCov.UbarTower_gauge`. "NOT proved HERE" remains exact — the proof cannot live in this
file, since the module carrying it imports this one. `UbarTowerCov.tower_feeds_Qcomposite` is this
theorem with that assumption discharged. -/
theorem Qcomposite_gaugeTransform
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (j : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) :
    Qcomposite (fun l => coarseGaugeTransform (ell ^ l) γ (bg l)) ell j
        (fun x => RMap (γ x) (lam x))
      = fun y => RMap (γ y) (Qcomposite bg ell j lam y) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      funext y
      show stepAverage (ell ^ j) (coarseGaugeTransform (ell ^ j) γ (bg j)) ell
          (Qcomposite (fun l => coarseGaugeTransform (ell ^ l) γ (bg l)) ell j
            (fun x => RMap (γ x) (lam x))) y
        = RMap (γ y) (stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam) y)
      rw [ih]
      exact stepAverage_gaugeTransform _ _ _ _ _ _

#print axioms coarseGaugeTransform
#print axioms coarseGaugeTransform_one
#print axioms coarsePathHolonomy_coarseGaugeTransform
#print axioms mul_coarseCoordSteps
#print axioms coarsePathEndpoint_coarseGammaPath
#print axioms stepAverage_gaugeTransform
#print axioms Qcomposite_gaugeTransform

/-! ## §6 — LOCALITY: the composite reads `λ` only on `B^j(y)`

The honest partial form of (3.19)'s second line. We do NOT prove the composite equals a single sum
over `B^j(y)`; we prove its DOMAIN OF DEPENDENCE is exactly that box — which is the property the
source's own locality remark (CMP98 p.31, *"these averages have the same locality properties … `(Ū^k)_c`
depends on the variables `U_b` for `b ⊂ B^k(c₋) ∪ B^k(c₊)`"*) asserts for the background tower, here
proved for the site-field composite. -/

theorem Qcomposite_local
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell j : ℕ)
    {lam lam' : PeriodicLatticeSite L → SuTwo} {y : PeriodicLatticeSite L}
    (h : ∀ x ∈ blockOf y (ell ^ j), lam x = lam' x) :
    Qcomposite bg ell j lam y = Qcomposite bg ell j lam' y := by
  induction j generalizing y with
  | zero =>
      have hy : y ∈ blockOf y (ell ^ 0) := by
        rw [pow_zero, blockOf_one_eq_singleton]
        exact Finset.mem_singleton_self y
      exact h y hy
  | succ j ih =>
      show stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam) y
        = stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam') y
      unfold stepAverage
      refine congrArg (fun z => (1 / (ell : ℝ) ^ 3) • z)
        (Finset.sum_congr rfl (fun x hx => ?_))
      have hsub : blockOf x (ell ^ j) ⊆ blockOf y (ell ^ j * ell) :=
        blockOf_subset_of_mem_stepBlockOf hx
      have hx' : Qcomposite bg ell j lam x = Qcomposite bg ell j lam' x := by
        refine ih (fun z hz => h z ?_)
        rw [pow_succ]
        exact hsub hz
      rw [hx']

#print axioms Qcomposite_local

/-! ## §7 — THE TRANSPORT IS THE TOWER PRODUCT

Each factor's transport is, definitionally, the level-`l` factor `Cmp98Gamma.stepVar` of the tree's
tower-transport object; and at `j = 2` the composite expands into the nested chain sum with the FULL
product `Cmp98Gamma.gammaVar` in each summand.

**Scope.** This is an identification with an object already in this tree. `Cmp98Gamma.gammaVar`'s own
attribution to a particular CMP98 equation is currently unsettled (header, "What is NOT claimed",
item 1), so nothing here is a claim about which printed formula is being re-derived. -/

/-- The ancestor chain `x = x₀, x₁, x₂ = y` of CMP99b p.401's *"`x_l ∈ B(x_{l+1})`"*, at `j = 2`. -/
def ancOf (y x₁ x₀ : PeriodicLatticeSite L) : ℕ → PeriodicLatticeSite L :=
  fun l => if l = 0 then x₀ else if l = 1 then x₁ else y

theorem ancOf_zero (y x₁ x₀ : PeriodicLatticeSite L) : ancOf y x₁ x₀ 0 = x₀ := rfl
theorem ancOf_one (y x₁ x₀ : PeriodicLatticeSite L) : ancOf y x₁ x₀ 1 = x₁ := rfl
theorem ancOf_two (y x₁ x₀ : PeriodicLatticeSite L) : ancOf y x₁ x₀ 2 = y := rfl

/-- **The level-`l` factor's transport IS `Cmp98Gamma.stepVar`** — definitionally, no re-encoding. -/
theorem stepVar_eq_holonomy (ell : ℕ)
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (anc : ℕ → PeriodicLatticeSite L) (l : ℕ) :
    stepVar ell bg anc l
      = coarsePathHolonomy (ell ^ l) (bg l) (anc (l + 1))
          (coarseGammaPath (ell ^ l) (anc (l + 1)) (anc l)) := rfl

/-- **`Q'_2` expanded**: a nested sum over the ancestor chain `y = x₂, x₁, x₀ = x`, with the ORDERED
tower product `gammaVar` as the transport of each chain. This is CMP99b (3.19)'s content at `j = 2`
in chain form; it is NOT the single sum over `B²(y)` (see the header). -/
theorem Qcomposite_two_expand
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    Qcomposite bg ell 2 lam y
      = (1 / (ell : ℝ) ^ 3) • ∑ x₁ ∈ stepBlockOf y (ell ^ 1) ell,
          (1 / (ell : ℝ) ^ 3) • ∑ x₀ ∈ stepBlockOf x₁ (ell ^ 0) ell,
            RMap (gammaVar ell bg (ancOf y x₁ x₀) 2) (lam x₀) := by
  show stepAverage (ell ^ 1) (bg 1) ell (Qcomposite bg ell 1 lam) y = _
  unfold stepAverage
  refine congrArg (fun z => (1 / (ell : ℝ) ^ 3) • z)
    (Finset.sum_congr rfl (fun x₁ _ => ?_))
  show RMap (coarsePathHolonomy (ell ^ 1) (bg 1) y (coarseGammaPath (ell ^ 1) y x₁))
      (stepAverage (ell ^ 0) (bg 0) ell lam x₁) = _
  unfold stepAverage
  rw [map_smul, map_sum]
  refine congrArg (fun z => (1 / (ell : ℝ) ^ 3) • z)
    (Finset.sum_congr rfl (fun x₀ _ => ?_))
  rw [RMap_mul_apply]
  show RMap _ (lam x₀) = RMap (gammaVarOf (stepVar ell bg (ancOf y x₁ x₀)) 2) (lam x₀)
  rw [gammaVarOf_succ, gammaVarOf_succ, gammaVarOf_zero, mul_one, stepVar_eq_holonomy,
    stepVar_eq_holonomy, ancOf_zero, ancOf_one, ancOf_two, pow_zero]

#print axioms ancOf
#print axioms ancOf_zero
#print axioms ancOf_one
#print axioms ancOf_two
#print axioms stepVar_eq_holonomy
#print axioms Qcomposite_two_expand

/-! ## §8 — CONTROLS

Must-not-fire (the composite degenerates to the flat operator at the trivial tower) and must-fire
(the composite genuinely depends on the tower). -/

/-- Must-not-fire: at the trivial tower the `j = 1` composite is the tree's FLAT block average. -/
theorem Qcomposite_trivial_tower_one (ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) :
    Qcomposite (fun _ => trivialU L) ell 1 lam = coarseRestrictSiteCovariant ell lam := by
  rw [Qcomposite_one, coarseRestrictSiteCovariantU_trivialU_eq]

/-- Must-fire: the composite is NOT the flat operator. On the tree's own separation witness the
`j = 1` composite at the curved background `sepU` is nonzero while at the trivial tower it is zero,
so the background genuinely enters. -/
theorem Qcomposite_background_dependent :
    Qcomposite (fun _ => sepU) witnessEll 1 sepLam witnessY
      ≠ Qcomposite (fun _ => trivialU witnessL) witnessEll 1 sepLam witnessY := by
  have h1 : Qcomposite (fun _ => sepU) witnessEll 1 sepLam witnessY
      = coarseRestrictSiteCovariantU sepU witnessEll sepLam witnessY := by
    rw [Qcomposite_one]
  have h2 : Qcomposite (fun _ => trivialU witnessL) witnessEll 1 sepLam witnessY = 0 := by
    rw [Qcomposite_trivial_tower_one]
    exact sepLam_flat_value
  rw [h1, h2]
  exact sepLam_transported_ne_zero

/-! ### §8b — the LEVEL-`1` background genuinely enters

The controls above only exercise `bg 0`, which the tree already had. The real question for a
COMPOSITE is whether the higher levels of the tower do any work — a `Q'_2` that ignored `bg 1` would
be a relabelled `Q'_1`. Two towers agreeing at level `0` and differing at level `1` are exhibited
here, on the tree's own `witnessL` (extent `(3,3,3)`, i.e. `Fin 4` per axis), at `ell = 2`, and shown
to give DIFFERENT values on a single-site field.

The mechanism is exactly the strided block: the level-`1` factor averages over the STRIDE-`2` block
of `witnessY`, whose member `zTwo = (2,0,0)` is reached by a coarse contour of length one — a single
level-`1` link, `bg 1 (witnessY, 0)`. The chain `witnessY = x₂ ← x₁ = zTwo ← x₀ = zTwo` is the unique
one contributing. -/

/-- The stride-`2` neighbour of the origin along coordinate `0`. -/
def zTwo : PeriodicLatticeSite witnessL := Function.update witnessY 0 ⟨2, by decide⟩

/-- A single-site field supported at `zTwo`. -/
noncomputable def deltaTwo : PeriodicLatticeSite witnessL → SuTwo :=
  fun x => if x = zTwo then suTwoWitness else 0

/-- A tower that is trivial everywhere EXCEPT at level `1`. Two instances of it with different `V`
therefore agree at level `0` — so any difference they produce is level-`1` information. -/
noncomputable def towerAtOne
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL :=
  fun l => if l = 1 then V else trivialU witnessL

theorem zTwo_mem_stepBlock : zTwo ∈ stepBlockOf witnessY 2 2 := by decide

theorem zTwo_mem_own_block : zTwo ∈ blockOf zTwo 2 := by decide

/-- The chain is UNIQUE: no other stride-`2` anchor of `witnessY`'s level-`1` block contains
`zTwo` in its own fine block. -/
theorem stepBlock_unique_ancestor (x₁ : PeriodicLatticeSite witnessL)
    (hx : x₁ ∈ stepBlockOf witnessY 2 2) (hne : x₁ ≠ zTwo) : zTwo ∉ blockOf x₁ 2 := by
  revert x₁; decide

/-- The coarse contour from the origin to `zTwo` at stride `2` is ONE coarse link in direction `0`. -/
theorem coarseGammaPath_zTwo : coarseGammaPath 2 witnessY zTwo = [0] := by decide

/-- **The value of `Q'_2` on the single-site field**, at an arbitrary level-`1` background. Only
`V (witnessY, 0)` survives — a LEVEL-`1` link variable, which no `Q'_1` can see. -/
theorem Qcomposite_two_deltaTwo_value
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    Qcomposite (towerAtOne V) 2 2 deltaTwo witnessY
      = (1 / (2 : ℝ) ^ 3) • RMap (V (witnessY, 0)) ((1 / (2 : ℝ) ^ 3) • suTwoWitness) := by
  have hb1 : (towerAtOne V) 1 = V := by unfold towerAtOne; simp
  have hb0 : (towerAtOne V) 0 = trivialU witnessL := by unfold towerAtOne; simp
  have hQ1 : ∀ x₁ : PeriodicLatticeSite witnessL,
      Qcomposite (towerAtOne V) 2 1 deltaTwo x₁
        = (1 / (2 : ℝ) ^ 3) • (if zTwo ∈ blockOf x₁ 2 then suTwoWitness else 0) := by
    intro x₁
    rw [Qcomposite_one, hb0, coarseRestrictSiteCovariantU_trivialU_eq]
    unfold coarseRestrictSiteCovariant deltaTwo
    rw [Finset.sum_ite_eq' (blockOf x₁ 2) zTwo (fun _ => suTwoWitness)]
    norm_num
  have hhol : coarsePathHolonomy 2 V witnessY (coarseGammaPath 2 witnessY zTwo)
      = V (witnessY, 0) := by
    rw [coarseGammaPath_zTwo, coarsePathHolonomy_cons, coarsePathHolonomy_nil, mul_one]
  have hvanish : ∀ x₁ ∈ stepBlockOf witnessY 2 2, x₁ ≠ zTwo →
      RMap (coarsePathHolonomy 2 V witnessY (coarseGammaPath 2 witnessY x₁))
        (Qcomposite (towerAtOne V) 2 1 deltaTwo x₁) = 0 := by
    intro x₁ hx₁ hne
    rw [hQ1 x₁, if_neg (stepBlock_unique_ancestor x₁ hx₁ hne), smul_zero, map_zero]
  show stepAverage (2 ^ 1) ((towerAtOne V) 1) 2
      (Qcomposite (towerAtOne V) 2 1 deltaTwo) witnessY = _
  rw [hb1, pow_one]
  unfold stepAverage
  rw [Finset.sum_eq_single zTwo hvanish (fun hcon => absurd zTwo_mem_stepBlock hcon), hhol,
    hQ1 zTwo, if_pos zTwo_mem_own_block]
  norm_num

/-- **MUST-FIRE: `Q'_2` reads the level-`1` background.** The two towers agree at level `0` (both
trivial) and differ only at level `1`, and the composite separates them. So this is a genuinely
`2`-step object, not the one-step operator under a new name. -/
theorem Qcomposite_two_level_one_dependent :
    Qcomposite (towerAtOne witnessU) 2 2 deltaTwo witnessY
      ≠ Qcomposite (towerAtOne (trivialU witnessL)) 2 2 deltaTwo witnessY := by
  rw [Qcomposite_two_deltaTwo_value, Qcomposite_two_deltaTwo_value, witnessU_at_x_mu,
    show (trivialU witnessL) (witnessY, (0 : Fin 3)) = 1 from rfl, RMap_one]
  intro hcon
  have hc : (1 / (2 : ℝ) ^ 3) ≠ 0 := by norm_num
  rw [map_smul, RMap_witnessMElem] at hcon
  have h1 := smul_right_injective SuTwo hc hcon
  have h2 := smul_right_injective SuTwo hc h1
  have hsum2 : (2 : ℝ) • suTwoWitness = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h2]
    exact neg_add_cancel _
  rcases smul_eq_zero.mp hsum2 with h | h
  · norm_num at h
  · exact suTwoWitness_ne_zero h

#print axioms Qcomposite_trivial_tower_one
#print axioms Qcomposite_background_dependent
#print axioms zTwo
#print axioms deltaTwo
#print axioms towerAtOne
#print axioms zTwo_mem_stepBlock
#print axioms zTwo_mem_own_block
#print axioms stepBlock_unique_ancestor
#print axioms coarseGammaPath_zTwo
#print axioms Qcomposite_two_deltaTwo_value
#print axioms Qcomposite_two_level_one_dependent

/-! ## §9 — WHAT THIS MODULE ESTABLISHED, AND WHAT IT DID NOT

Established, kernel-checked, no `sorry` and no new axiom:

* `stepBlockOf` / `card_stepBlockOf` — the strided block and its `ell^3` count, with the fitting
  hypothesis proved load-bearing by the PAIR `card_stepBlockOf_truncates` (count `= 8`) and
  `card_stepBlockOf_truncates_ne` (count `≠ 3^3`); neither theorem alone states `8 ≠ 27`.
* `coarsePathHolonomy_one_eq_staircaseTransport` — the tree's two staircase encodings agree at
  stride `1`. No third convention is introduced here.
* `stepAverage` — the level factor; linear, reducing at stride `1` to the tree's existing
  `coarseRestrictSiteCovariantU`, flat at the trivial background, and reproducing the covariantly
  constant mode exactly (so the `ell^{-3}` normalization is checked, not assumed).
* `Qcomposite` — the composite, with `Qcomposite_succ` the composition law in the orientation
  (3.19) forces, `Qcomposite_one` the reduction to the one-step operator, and
  `Qcomposite_add`/`Qcomposite_smul`/`QcompositeLM` its linearity.
* `Qcomposite_gaugeTransform` — EXACT `Ad`-covariance of the composite at every `j`, no hypotheses.
* `Qcomposite_local` — the composite reads `λ` only on `blockOf y (ell^j)`, the source's `B^j(y)`.
* `Qcomposite_two_expand` — at `j = 2`, the nested chain sum with the ordered tower product
  `Cmp98Gamma.gammaVar` as each chain's transport.
* Controls: must-not-fire at the trivial tower (`Qcomposite_trivial_tower_one`), must-fire on the
  level-`0` background (`Qcomposite_background_dependent`) AND on the level-`1` background
  (`Qcomposite_two_level_one_dependent`).
* Degeneracy disclosure, proved rather than asserted: `Qcomposite_ell_zero` (`ell = 0` ⇒ the
  composite is `0` from `j = 1` on) and `Qcomposite_ell_one` (`ell = 1` ⇒ the composite is the
  identity at every `j`). Every general-`ell` theorem above is therefore CONTENT-FREE at `ell ≤ 1`
  and carries its content at `ell ≥ 2`, where the `ell = 2` separation of §8b is exhibited. This is
  stated, not repaired: no hypothesis was added to any theorem, because each is true as stated.

NOT established, and not claimed anywhere above:

* that `bg` is Bałaban's `Ū₀^l` ~~(nothing here builds a blocked average; see the header)~~ —
  **parenthetical STRUCK 2026-07-30 (S75), retained visible**: a blocked average IS built, one
  module downstream, as `UbarTowerCov.UbarTower`, and `UbarTowerCov.UbarTower_gauge` proves the
  covariance law item 5 of the header disclaimed. What is still not established HERE is the
  identification of this module's PARAMETER `bg` with it — that identification is made downstream,
  by instantiation, in `UbarTowerCov.tower_feeds_Qcomposite`;
* that the composite equals the DIRECT form as a single sum over `B^j(y)` — only the locality
  statement and the `j = 2` chain expansion are proved;
* any statement about `Δ_k`, an RG ladder, coercivity, `γ₀`, or CMP99b p.428. No denotation
  dictionary row is closed by this module.
* contour-family independence of the OPERATOR — it is family-dependent at every level; only the
  COVARIANCE is family-independent, and the proof of `coarsePathHolonomy_coarseGaugeTransform`
  shows exactly why (it never uses which chain).

A residual this module creates and does NOT close: `Qcomposite_two_expand` is proved at `j = 2`
only. Extending it to general `j` needs a `Finset`-indexed family of ancestor chains, which is a
representation choice (a dependent `Finset` of chain functions) rather than new mathematics; the
`j`-uniform structural content — that each factor's transport is `Cmp98Gamma.stepVar l` — is already
proved at all `j` by `stepVar_eq_holonomy` together with `Qcomposite_succ`. -/

end AdalyFormal.Balaban.QjComposite
