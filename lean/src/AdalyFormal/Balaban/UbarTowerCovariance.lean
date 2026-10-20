/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.QjComposite
import AdalyFormal.Balaban.U1AnchorPoincare

set_option autoImplicit false
set_option maxRecDepth 4000

/-!
# `Ū^l` — CMP98 (43)'s SINGLE-BAR background tower, and its gauge covariance

This module builds CMP98 eq. (15) = (42) = (43) at a general stride, iterates it by (43)'s own
recursion into the single-bar tower `Ū^l`, and PROVES the covariance law

  `Ū^l(U^γ) = coarseGaugeTransform (ell^l) γ (Ū^l U)`   (`UbarTower_gauge`)

for every `l`, `ell`, `γ`, `U` and every `LogExpAd P`, with **no hypotheses**. That law is the one
`QjComposite.lean`'s header item 5 previously recorded as *"not proved here and is not claimed"*;
`tower_feeds_Qcomposite` (§10) discharges `QjComposite`'s §5 assumption with it, so `Qcomposite`'s
covariance is available at a tower that is a blocked average rather than at free data.

## Provenance and what this module is NOT

The mathematics was built and kernel-checked as an exhibit at `compute/blockedgauge_ident/`
(`BGIdent.lean` + `QjBridge.lean`, commit `12cb000a`); this module is that construction LANDED into
the package, with the exhibit's re-declarations of `QjComposite` plumbing collapsed into the import
(see "Reuse" below). No statement was weakened in the move.

**`stridedBlockedGauge` is NOT `BlockedGauge.blockedGauge`, and neither is claimed to be the
other.** `blockedGauge` is **CMP109 (0.4)**; this file's object is **CMP98 (15)=(42)=(43)**. They
were settled as different objects, and §9 turns each of the two source differences into a decidable
fact about this tree's own encodings rather than leaving it as a reading:

* **(0.4) averages over the contour FAMILY** `G(c_-,x) × G(c_+,x')` with weights `1/|G|`; CMP98
  (15) takes the logarithm of ONE contour variable `Γ_{c,x} = Γ_{c_-,x} ∪ [x,x(c)] ∪ Γ_{x(c),c_+}`.
  Bałaban draws the distinction himself directly beneath (0.4) on CMP109 printed p.253 (read at
  400 dpi on `corpus/renders/CMP109_p253-05.png`): *"A natural idea … would be to use variables
  obtained by averaging the contour variables `{U(Γ)}_{Γ∈G(y,x)}`, rather than to use one contour
  variable `U(Γ_{y,x})`."* Mechanised as `contourFamily_card_ge_two` (≥ 2 contours at a
  two-coordinate displacement) with its own non-cherry-picking control `contourFamily_card_axis`
  (= 1 contour along an axis, where the two formulas do coincide).
* **(0.4) is pinned to the FIRST level** `c ∈ T^{(1)}` and `blockedGauge P ell` uses FINE-unit
  `contourFamily`/`straightSeg`/`blockOf` at every `ell`; CMP98 (43) RE-BASES every level —
  `Ū^{k+1}` is the one-step blocking of `Ū^k` *"where the contours `Γ_{c,x}` are defined on the
  lattice `Ω^{(k)}`"* (printed p.24, `corpus/pages/CMP98_p24.md`, `verification_status:
  adjudicated`), i.e. at spacing `ell^k`. Mechanised as `blockOf_ne_stepBlockOf`, with the counts
  `card_blockOf_four = 64` against `card_stepBlockOf_two_two = 8`.

Three further things this file does not claim:

1. **The contour family is a CHOICE.** CMP98 (14) defers `Γ_{c_-,x}` to "paper [2]"; this file uses
   `TowerLawCov.coarseGammaPath` (CMP95 (1.7)'s descending-`2,1,0` staircase, as pinned in
   `TowerLawCovariant.lean`). Covariance is family-INDEPENDENT — the proof uses only that each leg
   is a connected strided chain — but the OBJECT is family-dependent.
2. **Degeneracy is not addressed.** `LogExpAd` has degenerate inhabitants making `Ū = U`; see
   `BlockedGaugeCore`'s header and `BlockedGaugeGuard.lean`. Covariance alone certifies nothing
   about non-degeneracy — exactly as for `blockedGauge_gauge`.
3. **No claim that the composite `Q'_j` equals the direct form.**
   `TowerLawCov.tower_law_cov_refuted`
   (`TowerLawCovariant.lean:1323`) REFUTES the covariant tower law for the AVERAGING operator at a
   curved background, for every `V` — and `TowerLawCov.tower_law_cov_refuted_at_blockedGauge`
   (`:1363`) instantiates that refutation at `blockedGaugeAsConfig` itself. That is a different
   statement from the background covariance proved here, and nothing here weakens it.

## Reuse (LAW-19) — what the landing DELETED

The exhibit could not import `QjComposite` (a file under `compute/` has no package context), so it
re-declared thirteen of that module's declarations verbatim and carried three `rfl` transcription
checks. Landing collapses all of them into the import; the following are now USED from
`QjComposite`, not redefined here: `coarseGaugeTransform`, `coarseGaugeTransform_one`,
`coarsePathHolonomy_coarseGaugeTransform`, `coarsePathHolonomy_cons`, `coarsePathEndpoint_cons`,
`coarsePathEndpoint_append`, `coarsePathEndpoint_replicate`, `mul_coarseCoordSteps`,
`coarsePathEndpoint_coarseGammaPath`, `inStepBlock`, `stepBlockOf`, `mem_stepBlockOf`,
`self_mem_stepBlockOf`. Two more duplications the exhibit carried are also gone: its
`coarseShift_comm` is deleted in favour of `U1AnchorPoincare.coarseShift_comm_gen`, which states it
in the same unrestricted form (`Weitzenbock.pathSite_comm` sits underneath both), and its three
lattice witnesses `wL`/`wY`/`wX` are replaced by
`AdmissibleSubspace.witnessL`/`witnessY`/`witnessX`, which are literally the same sites.

**A fourth duplication was introduced by this landing and then removed**: the single-axis witness of
§9 was first declared here as a new `axisWitness`, on the stated ground that the tree had no such
site. It has one — `QOne.site1` — and the deletion is recorded at §9 rather than silently, because
the failure mode is the one this header warns about: the shape index cannot separate two sites of
type `PeriodicLatticeSite witnessL`, and the grep that finds it is not the spelling the author had
in mind.

Searched by SHAPE, not by name (`compute/duplicate_census/concept_index.py --like`), before
declaring anything: `LogExpAd` (56 hits — `blockedGauge`, `centeredBlockedGauge`,
`blockedGaugeAsConfig`, `blockedGaugeMap`, `innerAvg`, none the level-`l` tower) and
`Nat ARROW PeriodicLinkConfiguration` (161 hits, same conclusion).
`BlockingLinkEstimate.blockedLink` is (43)'s formula in an abstract
`(Finset ι, weights, loops, Uc)` form carrying the *estimate*, with no lattice geometry and no
level recursion; it is not this object either.
-/

namespace AdalyFormal.Balaban.UbarTowerCov

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.BlockedGauge (CoarseBond cPlus shiftBy LogExpAd blockedGauge
  contourFamily contourSteps)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf witnessL witnessY witnessX)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.TowerLawCov (coarsePathEndpoint coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf self_mem_stepBlockOf
  coarseGaugeTransform coarseGaugeTransform_one coarsePathHolonomy_coarseGaugeTransform
  coarsePathEndpoint_cons coarsePathEndpoint_replicate coarsePathEndpoint_coarseGammaPath
  Qcomposite Qcomposite_gaugeTransform)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the TYPE question: `blockedGauge`'s carrier IS a link configuration -/

/-- `BlockedGauge.CoarseBond L` IS `PeriodicLatticeEdge L`. -/
theorem coarseBond_eq_edge (L : PeriodicLatticeExtent) :
    CoarseBond L = PeriodicLatticeEdge L := rfl

/-- Hence `CoarseBond L → G` IS `PeriodicLinkConfiguration G L`: the two carriers of a background
configuration in this tree are the same type, not merely isomorphic. -/
theorem coarseBondFun_eq_linkConfig (G : Type) [Group G] (L : PeriodicLatticeExtent) :
    (CoarseBond L → G) = PeriodicLinkConfiguration G L := rfl

/-- The type identity is USABLE, not just true: a `blockedGauge` value typechecks where a
`PeriodicLinkConfiguration` is demanded, with no coercion. -/
theorem blockedGauge_typechecks_as_config {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : LogExpAd G 𝔤) (ell : ℕ) (U : PeriodicLinkConfiguration G L) :
    (blockedGauge P ell U : PeriodicLinkConfiguration G L) = blockedGauge P ell U := rfl

/-! ## §2 — the two forward shifts are the same map -/

/-- `coarseShift` (an `ell`-fold `periodicLatticeShift`) and `shiftBy` (the endpoint of a
`straightSeg`) are the SAME function. Note the argument ORDER differs: `coarseShift y m μ` vs
`shiftBy y μ m`. -/
theorem coarseShift_eq_shiftBy (y : PeriodicLatticeSite L) (m : ℕ) (μ : Fin 3) :
    coarseShift y m μ = shiftBy y μ m := by
  induction m generalizing y with
  | zero => rfl
  | succ n ih =>
      show (fun z => periodicLatticeShift z μ)^[n + 1] y = _
      rw [Function.iterate_succ_apply]
      rw [show ((fun z : PeriodicLatticeSite L => periodicLatticeShift z μ)^[n]
            (periodicLatticeShift y μ)) = coarseShift (periodicLatticeShift y μ) n μ from rfl]
      rw [ih (periodicLatticeShift y μ)]
      rfl

/-! ## §3 — the two `coarseGaugeTransform`s are the same function -/

/-- **The two coarse gauge actions in this tree are EQUAL.**

`BlockedGauge.coarseGaugeTransform ell γ V c = γ c.1 * V c * (γ (cPlus ell c))⁻¹` (far end
`cPlus ell c = shiftBy c.1 c.2 ell`) and `QjComposite.coarseGaugeTransform s γ V e = γ e.1 * V e *
(γ (coarseShift e.1 s e.2))⁻¹` (far end `coarseShift e.1 s e.2`) are the same map, by §2. So the
conclusion of `BlockedGaugeCore.blockedGauge_gauge` is already stated in `QjComposite`'s
vocabulary, and `UbarTower_gauge`/`UbarTower_gauge'` below make no choice of vocabulary. -/
theorem coarseGaugeTransform_eq {G : Type*} [Group G] (s : ℕ) (γ : PeriodicLatticeSite L → G)
    (V : PeriodicLinkConfiguration G L) :
    AdalyFormal.Balaban.BlockedGauge.coarseGaugeTransform s γ V = coarseGaugeTransform s γ V := by
  funext e
  show γ e.1 * V e * (γ (cPlus s e))⁻¹ = γ e.1 * V e * (γ (coarseShift e.1 s e.2))⁻¹
  rw [coarseShift_eq_shiftBy]
  rfl

/-! ## §4 — strided endpoints commute

The two lemmas this construction needs that `QjComposite` does not already carry. The underlying
geometry — that two strided shifts commute with NO restriction on the two directions — is already
in the tree twice, as `Weitzenbock.pathSite_comm` and, in this file's own `coarseShift` vocabulary,
as `U1AnchorPoincare.coarseShift_comm_gen`. The latter is used directly (LAW-19); the exhibit's
one-line re-statement of it is deleted, which is the only reason this module imports
`U1AnchorPoincare`. Note the tree's OTHER `coarseShift_comm`s (`Lemma24GeneralEll`,
`LineIntegralAveraging`) all carry a `μ ≠ ν` hypothesis and would not serve here. -/

theorem coarsePathEndpoint_coarseShift (s t : ℕ) (ν : Fin 3) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) :
    coarsePathEndpoint s (coarseShift y t ν) p = coarseShift (coarsePathEndpoint s y p) t ν := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih =>
      rw [coarsePathEndpoint_cons, coarsePathEndpoint_cons,
        AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen, ih]

/-- **Two strided paths from the same base commute**: `endpoint(endpoint(y,q),p) =
endpoint(endpoint(y,p),q)`. This is what makes the level-`l` loop of (15) CLOSE without any extra
hypothesis: the translate of `Γ_{c_-,x}` based at `c_+` lands exactly on `x(c)`. -/
theorem coarsePathEndpoint_comm (s : ℕ) (y : PeriodicLatticeSite L) (p q : List (Fin 3)) :
    coarsePathEndpoint s (coarsePathEndpoint s y q) p
      = coarsePathEndpoint s (coarsePathEndpoint s y p) q := by
  induction q generalizing y with
  | nil => rfl
  | cons ν rest ih =>
      rw [coarsePathEndpoint_cons, ih, coarsePathEndpoint_coarseShift,
        coarsePathEndpoint_cons]

/-! ## §5 — CMP98 (15) = (42) = (43), AT STRIDE `s` -/

variable {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]

/-- `c_+` for a bond `c` of `Ω^{(l+1)}` whose level-`l` spacing is `s`: `ell` strided steps in
direction `c.2`, i.e. `c_- + s·ell·e_{c.2}`. -/
def cPlusS (s ell : ℕ) (c : PeriodicLatticeEdge L) : PeriodicLatticeSite L :=
  coarsePathEndpoint s c.1 (List.replicate ell c.2)

theorem cPlusS_eq (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    cPlusS s ell c = coarseShift c.1 (s * ell) c.2 :=
  coarsePathEndpoint_replicate s c.1 c.2 ell

/-- **`V(c)`** — the level-`(l+1)` bond variable of `c`, read off the level-`l` field `V` as the
product of the `ell` successive level-`l` links along `c`. -/
def coarseBondVar (s ell : ℕ) (V : PeriodicLinkConfiguration G L)
    (c : PeriodicLatticeEdge L) : G :=
  coarsePathHolonomy s V c.1 (List.replicate ell c.2)

/-- **`V(Γ_{c,x})`** — CMP98 (14)'s contour `Γ_{c_-,x} ∪ [x,x(c)] ∪ Γ_{x(c),c_+}`, at stride `s`:
the staircase `c_- → x`, then the `ell` strided steps `x → x(c)`, then the REVERSE of the SAME
staircase based at `c_+` (which is `Γ_{c_+,x(c)}`, since `x(c) − c_+ = x − c_-`). -/
def gammaVarStrided (s ell : ℕ) (V : PeriodicLinkConfiguration G L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) : G :=
  coarsePathHolonomy s V c.1 (coarseGammaPath s c.1 x)
    * coarsePathHolonomy s V x (List.replicate ell c.2)
    * (coarsePathHolonomy s V (cPlusS s ell c) (coarseGammaPath s c.1 x))⁻¹

/-- **`W_x = V(Γ_{c,x})·V(c)⁻¹`** — the closed loop at `c_-` whose logarithm (15) averages. -/
def loopVar (s ell : ℕ) (V : PeriodicLinkConfiguration G L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) : G :=
  gammaVarStrided s ell V c x * (coarseBondVar s ell V c)⁻¹

/-- **CMP98 (15) = (42) = (43), TRANSCRIBED AT STRIDE `s`.**

`Ū_c = exp[ Σ_{x ∈ B_s(c_-)} ell^{-3} · log (V(Γ_{c,x}) V(c)^{-1}) ] · V(c)`

The `i` and `1/i` of the printed formula cancel and are absorbed into `P.exp` / `P.log`, exactly as
in `BlockedGaugeCore.blockedGauge`. The weight `ell^{-3}` is `L^{-d}` at `d = 3`. -/
noncomputable def stridedBlockedGauge (P : LogExpAd G 𝔤) (s ell : ℕ)
    (V : PeriodicLinkConfiguration G L) (c : PeriodicLatticeEdge L) : G :=
  P.exp (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell V c x))
    * coarseBondVar s ell V c

/-! ## §6 — covariance of the strided blocking -/

theorem coarseBondVar_gauge (s ell : ℕ) (γ : PeriodicLatticeSite L → G)
    (V : PeriodicLinkConfiguration G L) (c : PeriodicLatticeEdge L) :
    coarseBondVar s ell (coarseGaugeTransform s γ V) c
      = γ c.1 * coarseBondVar s ell V c * (γ (cPlusS s ell c))⁻¹ := by
  unfold coarseBondVar cPlusS
  rw [coarsePathHolonomy_coarseGaugeTransform]

/-- **The contour variable transforms at its two ENDS.** The loop closure is where
`coarsePathEndpoint_comm` does its work: the third leg's endpoint is `x(c)` on the nose. -/
theorem gammaVarStrided_gauge (s ell : ℕ) (γ : PeriodicLatticeSite L → G)
    (V : PeriodicLinkConfiguration G L) (c : PeriodicLatticeEdge L)
    {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf c.1 s ell) :
    gammaVarStrided s ell (coarseGaugeTransform s γ V) c x
      = γ c.1 * gammaVarStrided s ell V c x * (γ (cPlusS s ell c))⁻¹ := by
  have hx' := mem_stepBlockOf.mp hx
  have h1 : coarsePathEndpoint s c.1 (coarseGammaPath s c.1 x) = x :=
    coarsePathEndpoint_coarseGammaPath (fun μ => ⟨(hx' μ).1, (hx' μ).2.2⟩)
  have h3 : coarsePathEndpoint s (cPlusS s ell c) (coarseGammaPath s c.1 x)
      = coarsePathEndpoint s x (List.replicate ell c.2) := by
    unfold cPlusS
    rw [coarsePathEndpoint_comm, h1]
  unfold gammaVarStrided
  rw [coarsePathHolonomy_coarseGaugeTransform, coarsePathHolonomy_coarseGaugeTransform,
    coarsePathHolonomy_coarseGaugeTransform, h1, h3]
  group

/-- **`W_x` is CONJUGATED by `γ(c_-)`** — a closed loop based at `c_-`, for every `x` in the block.
This is the mechanism CMP98 p.24 states in prose ("the matrices … are unitarily equivalent"). -/
theorem loopVar_gauge (s ell : ℕ) (γ : PeriodicLatticeSite L → G)
    (V : PeriodicLinkConfiguration G L) (c : PeriodicLatticeEdge L)
    {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf c.1 s ell) :
    loopVar s ell (coarseGaugeTransform s γ V) c x
      = γ c.1 * loopVar s ell V c x * (γ c.1)⁻¹ := by
  unfold loopVar
  rw [gammaVarStrided_gauge s ell γ V c hx, coarseBondVar_gauge]
  group

/-- **THE STRIDED BLOCKING IS GAUGE-COVARIANT.**

`Ū(V^γ)(c) = γ(c_-) Ū(V)(c) γ(c_+)⁻¹`, where the INPUT `V` is gauge-transformed at its own level
(`stride s`) and the OUTPUT at the next level (`stride s·ell`).

**No hypotheses at all** — no `0 < ell`, no divisibility, no `CoarseLattice` membership. Contrast
`BlockedGaugeCore.blockedGauge_gauge`, which needs `0 < ell`, `ell ∣ (L c.2 + 1)` and
`c.1 ∈ CoarseLattice L ell`: those are forced there by `contourFamily`'s endpoint conditions, and
they disappear here because every leg is a `coarseGammaPath` whose closure is supplied by the
summation index `x ∈ stepBlockOf` and by `coarsePathEndpoint_comm`. -/
theorem stridedBlockedGauge_gauge (P : LogExpAd G 𝔤) (s ell : ℕ)
    (γ : PeriodicLatticeSite L → G) (V : PeriodicLinkConfiguration G L)
    (c : PeriodicLatticeEdge L) :
    stridedBlockedGauge P s ell (coarseGaugeTransform s γ V) c
      = coarseGaugeTransform (s * ell) γ (stridedBlockedGauge P s ell V) c := by
  have hterm : ∀ x ∈ stepBlockOf c.1 s ell,
      ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell (coarseGaugeTransform s γ V) c x)
        = P.ad (γ c.1) (((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell V c x)) := by
    intro x hx
    rw [loopVar_gauge s ell γ V c hx, P.log_conj, map_smul]
  show P.exp _ * _ = γ c.1 * (P.exp _ * _) * (γ (coarseShift c.1 (s * ell) c.2))⁻¹
  rw [Finset.sum_congr rfl hterm, ← map_sum, P.exp_ad, coarseBondVar_gauge, cPlusS_eq]
  group

/-! ## §7 — the TOWER `Ū^l`, and the law -/

/-- **CMP98 (43)'s recursion.** `Ū^0 = U`; `Ū^{l+1}` is the one-step blocking of `Ū^l` with the
contours defined on `Ω^{(l)}` — i.e. at stride `ell^l`, which is exactly (43)'s
*"where the contours `Γ_{c,x}` are defined on the lattice `Ω^{(k)}`"*. -/
noncomputable def UbarTower (P : LogExpAd G 𝔤) (ell : ℕ)
    (U : PeriodicLinkConfiguration G L) : ℕ → PeriodicLinkConfiguration G L
  | 0 => U
  | l + 1 => stridedBlockedGauge P (ell ^ l) ell (UbarTower P ell U l)

@[simp] theorem UbarTower_zero (P : LogExpAd G 𝔤) (ell : ℕ)
    (U : PeriodicLinkConfiguration G L) : UbarTower P ell U 0 = U := rfl

@[simp] theorem UbarTower_succ (P : LogExpAd G 𝔤) (ell : ℕ)
    (U : PeriodicLinkConfiguration G L) (l : ℕ) :
    UbarTower P ell U (l + 1) = stridedBlockedGauge P (ell ^ l) ell (UbarTower P ell U l) := rfl

/-- **`Ū^l(U^γ) = (Ū^l U)^γ` — CMP98 p.19 (11) FOR THE TOWER, PROVED.**

This is the statement `QjComposite.lean`'s header item 5 recorded as not proved and not claimed,
for the tower built by (43)'s own recursion, with the level-`l` gauge action being exactly the one
`QjComposite.Qcomposite_gaugeTransform` assumes (`QjComposite.coarseGaugeTransform (ell^l) γ`).

Unconditional in `ell`, `l`, `γ`, `U` and `P`. -/
theorem UbarTower_gauge (P : LogExpAd G 𝔤) (ell : ℕ) (γ : PeriodicLatticeSite L → G)
    (U : PeriodicLinkConfiguration G L) (l : ℕ) :
    UbarTower P ell (periodicGaugeTransform γ U) l
      = coarseGaugeTransform (ell ^ l) γ (UbarTower P ell U l) := by
  induction l with
  | zero => rw [UbarTower_zero, UbarTower_zero, pow_zero, coarseGaugeTransform_one]
  | succ l ih =>
      rw [UbarTower_succ, UbarTower_succ, ih]
      funext c
      rw [stridedBlockedGauge_gauge, pow_succ]

/-- The same law written with `BlockedGaugeCore`'s `coarseGaugeTransform` — the two are equal (§3),
so no choice of vocabulary is being made. -/
theorem UbarTower_gauge' (P : LogExpAd G 𝔤) (ell : ℕ) (γ : PeriodicLatticeSite L → G)
    (U : PeriodicLinkConfiguration G L) (l : ℕ) :
    UbarTower P ell (periodicGaugeTransform γ U) l
      = AdalyFormal.Balaban.BlockedGauge.coarseGaugeTransform (ell ^ l) γ
          (UbarTower P ell U l) := by
  rw [coarseGaugeTransform_eq]
  exact UbarTower_gauge P ell γ U l

/-! ## §8 — CONTROLS

The covariance theorem is proved with NO hypotheses, so the standard "which hypothesis is
load-bearing" mutation is not available. What IS available is the mechanism: the theorem fails the
moment the two strides are DE-SYNCHRONISED. -/

/-- **The stride is load-bearing.** The output gauge action is at stride `s·ell`, and it is pinned
by `cPlusS`, not chosen. Recorded as a term so a reader can see the exponent is derived, not
asserted. -/
theorem output_stride_is_s_mul_ell (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    cPlusS s ell c = coarseShift c.1 (s * ell) c.2 := cPlusS_eq s ell c

/-- **The tower's level-`l` stride is `ell^l`, derived from the recursion.** Level `l+1` is built by
blocking level `l` at stride `ell^l`, so its own bonds have stride `ell^l · ell = ell^{l+1}`. -/
theorem tower_stride (ell l : ℕ) (c : PeriodicLatticeEdge L) :
    cPlusS (ell ^ l) ell c = coarseShift c.1 (ell ^ (l + 1)) c.2 := by
  rw [cPlusS_eq, pow_succ]

/-- **The `l = 1` rung is a genuine one-step blocking at stride 1**, i.e. CMP98 (42) itself. -/
theorem UbarTower_one (P : LogExpAd G 𝔤) (ell : ℕ) (U : PeriodicLinkConfiguration G L) :
    UbarTower P ell U 1 = stridedBlockedGauge P 1 ell U := by
  rw [UbarTower_succ, UbarTower_zero, pow_zero]

/-- **Not vacuous: the block is nonempty** whenever `0 < ell` and `0 < s`, so the exponent of (15)
is a sum over a nonempty index set. Witness `y` itself, from `QjComposite.self_mem_stepBlockOf`. -/
theorem stepBlockOf_nonempty (y : PeriodicLatticeSite L) {s ell : ℕ} (hell : 0 < ell)
    (hs : 0 < s) : (stepBlockOf y s ell).Nonempty :=
  ⟨y, self_mem_stepBlockOf y hell hs⟩

/-- The same at every level of the tower; the second positivity hypothesis is DERIVED
(`pow_pos hell l`), not assumed. -/
theorem tower_block_nonempty (y : PeriodicLatticeSite L) {ell : ℕ} (hell : 0 < ell) (l : ℕ) :
    (stepBlockOf y (ell ^ l) ell).Nonempty :=
  stepBlockOf_nonempty y hell (pow_pos hell l)

/-! ### §8b — THE DEGENERATE VALUES OF `ell`, AT THE LEVEL OF THE BLOCKING ITSELF

Every theorem above quantifies over `ell` with **no lower bound**, so at `ell ∈ {0,1}` each of them
is TRUE BUT CONTENT-FREE. `QjComposite`'s §1e makes that explicit for the composite; the same
disclosure is owed here for the blocking, because `stridedBlockedGauge_gauge` has no hypotheses at
all and a reader could take its generality for strength. The two collapses are PROVED, not left to
be noticed:

* **`ell = 0` is the severe one.** The block is EMPTY, so the exponent sum is `0` and the bond
  product is the empty product: `stridedBlockedGauge P s 0 V c = P.exp 0` — a constant **independent
  of `V` and of `c`**. The "blocking" discards its input entirely. `stridedBlockedGauge_gauge` at
  `ell = 0` therefore says nothing about the lattice; it reduces exactly to the centrality of
  `P.exp 0`, which is forced by the `exp_ad` axiom alone (`exp_zero_conj`) and involves no contour,
  no block and no gauge field.
* **`ell = 1`** collapses the block to the singleton `{y}` at every POSITIVE stride
  (`stepBlockOf_ell_one`, which generalises `QjComposite.stepBlockOf_one_one` from `s = 1` to all
  `0 < s`). The contour `Γ_{c,x}` is then the bond itself, the loop `W_x` is trivial, and the
  blocking is the bare link times the fixed constant `P.exp (P.log 1)`
  (`stridedBlockedGauge_ell_one`).
* **`s = 0` is a THIRD collapse, in the STRIDE rather than in `ell`**, and it was found by the
  kernel while these were being proved, not by inspection: `stepBlockOf_ell_one` is FALSE as first
  written without `0 < s`. At stride `0` the block is empty for every `ell`
  (`stepBlockOf_stride_zero`). `UbarTower` never reaches it except through `ell = 0` (its strides
  are `ell^l`), but `stridedBlockedGauge` and `stridedBlockedGauge_gauge` are stated at free `s`.

The content therefore lives at `ell ≥ 2` and `s ≥ 1`, which is where §9's separation witnesses sit.
No statement above was weakened to avoid this; the hypotheses stay as general as they are true, and
the one hypothesis added here (`0 < s` on `stepBlockOf_ell_one`) was added because the statement
without it is false, not to make a proof go through. -/

theorem stepBlockOf_ell_zero (y : PeriodicLatticeSite L) (s : ℕ) :
    stepBlockOf y s 0 = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  exact AdalyFormal.Balaban.QjComposite.not_mem_stepBlockOf_ell_zero y x s

/-- **A THIRD degeneracy, found while proving the other two, and it is the stride not `ell`.** At
stride `0` the block is empty for EVERY `ell`, so `stridedBlockedGauge P 0 ell` also discards its
input. The tower never hits this except through `ell = 0` (its strides are `ell^l`), but
`stridedBlockedGauge` and `stridedBlockedGauge_gauge` are stated at free `s`, so it is disclosed
here rather than left implicit. -/
theorem stepBlockOf_stride_zero (y : PeriodicLatticeSite L) (ell : ℕ) :
    stepBlockOf y 0 ell = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have h := mem_stepBlockOf.mp hx 0
  have h1 := h.1
  have h2 := h.2.1
  rw [Nat.zero_mul] at h2
  omega

/-- **`P.exp 0` is central** — forced by the `exp_ad` axiom alone, with no lattice input. This is
all that `stridedBlockedGauge_gauge` says at `ell = 0`. -/
theorem exp_zero_conj (P : LogExpAd G 𝔤) (g : G) : g * P.exp 0 * g⁻¹ = P.exp 0 := by
  have h := P.exp_ad g 0
  rw [map_zero] at h
  exact h.symm

/-- **At `ell = 0` the blocking discards its input.** The value does not mention `V` or `c`. -/
theorem stridedBlockedGauge_ell_zero (P : LogExpAd G 𝔤) (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (c : PeriodicLatticeEdge L) :
    stridedBlockedGauge P s 0 V c = P.exp 0 := by
  show P.exp (∑ x ∈ stepBlockOf c.1 s 0, _) * coarseBondVar s 0 V c = _
  rw [stepBlockOf_ell_zero, Finset.sum_empty]
  show P.exp 0 * (1 : G) = P.exp 0
  rw [mul_one]

/-- At `ell = 1` the strided block is the singleton `{y}`, at every POSITIVE stride.

**`0 < s` is load-bearing and was found by the kernel, not by inspection.** Without it the statement
is FALSE at `s = 0`, where the block is `∅ ≠ {y}` (`stepBlockOf_stride_zero`). Note also that this
generalises `QjComposite.stepBlockOf_one_one` (which fixes `s = 1`) — at general `s` the collapse is
NOT an `omega` consequence of the box condition alone: it needs the `s ∣ (x_μ − y_μ)` conjunct of
`inStepBlock`, via `Nat.eq_zero_of_dvd_of_lt`. -/
theorem stepBlockOf_ell_one (y : PeriodicLatticeSite L) {s : ℕ} (hs : 0 < s) :
    stepBlockOf y s 1 = {y} := by
  ext x
  rw [mem_stepBlockOf, Finset.mem_singleton]
  constructor
  · intro hx
    funext μ
    apply Fin.ext
    have h := hx μ
    have hlt : (x μ).val - (y μ).val < s := by
      have := h.2.1
      omega
    have hzero : (x μ).val - (y μ).val = 0 := Nat.eq_zero_of_dvd_of_lt h.2.2 hlt
    have h1 := h.1
    omega
  · rintro rfl
    intro μ
    exact ⟨le_refl _, by omega, by simp⟩

/-- The staircase from a site to ITSELF is the empty path, at every stride. -/
theorem coarseGammaPath_self (s : ℕ) (y : PeriodicLatticeSite L) :
    coarseGammaPath s y y = [] := by
  simp [coarseGammaPath, AdalyFormal.Balaban.TowerLawCov.coarseStraightSegment,
    AdalyFormal.Balaban.TowerLawCov.coarseCoordSteps]

/-- **At `ell = 1` the blocking is the bare link times a fixed constant.** The loop `W_x` is
trivial, so no contour and no block geometry survives. -/
theorem stridedBlockedGauge_ell_one (P : LogExpAd G 𝔤) {s : ℕ} (hs : 0 < s)
    (V : PeriodicLinkConfiguration G L) (c : PeriodicLatticeEdge L) :
    stridedBlockedGauge P s 1 V c = P.exp (P.log 1) * V c := by
  have hloop : loopVar s 1 V c c.1 = 1 := by
    show gammaVarStrided s 1 V c c.1 * (coarseBondVar s 1 V c)⁻¹ = 1
    show (coarsePathHolonomy s V c.1 (coarseGammaPath s c.1 c.1)
        * coarsePathHolonomy s V c.1 (List.replicate 1 c.2)
        * (coarsePathHolonomy s V (cPlusS s 1 c) (coarseGammaPath s c.1 c.1))⁻¹)
      * (coarsePathHolonomy s V c.1 (List.replicate 1 c.2))⁻¹ = 1
    rw [coarseGammaPath_self]
    show (1 * coarsePathHolonomy s V c.1 (List.replicate 1 c.2) * (1 : G)⁻¹)
      * (coarsePathHolonomy s V c.1 (List.replicate 1 c.2))⁻¹ = 1
    group
  unfold stridedBlockedGauge
  rw [stepBlockOf_ell_one _ hs, Finset.sum_singleton, hloop]
  norm_num
  show V (c.1, c.2) * 1 = V c
  rw [mul_one]

/-- The tower inherits the `ell = 0` collapse at every level from `1` on. -/
theorem UbarTower_ell_zero (P : LogExpAd G 𝔤) (U : PeriodicLinkConfiguration G L) (l : ℕ) :
    UbarTower P 0 U (l + 1) = fun _ => P.exp 0 := by
  rw [UbarTower_succ]
  funext c
  exact stridedBlockedGauge_ell_zero P (0 ^ l) _ c

/-! ## §9 — THE TWO SOURCE DIFFERENCES, AS KERNEL-CHECKED FACTS ABOUT THIS TREE

The header argues from the printed pages that (0.4) and (15)/(42)/(43) are different formulas. §9
turns each difference into a decidable statement about the tree's OWN encodings, so neither rests
on a reading. The lattice is `AdmissibleSubspace.witnessL = fun _ => 3` (sites `Fin 4` per axis,
`4³ = 64` sites), anchor `witnessY = 0`, and `witnessX` — the tree's own site differing from
`witnessY` in coordinates `0` and `2` but not `1`. -/

/-- The `π = id` contour through `witnessX`: one step in direction `0`, then one in direction
`2`. -/
theorem contourSteps_id :
    contourSteps 1 witnessY witnessX = [((0 : Fin 3), true), ((2 : Fin 3), true)] := by decide

/-- The `π = (0 2)` contour: the SAME two legs in the OTHER order. -/
theorem contourSteps_swap :
    contourSteps (Equiv.swap 0 2) witnessY witnessX
      = [((2 : Fin 3), true), ((0 : Fin 3), true)] := by decide

/-- **DIFFERENCE 1, MADE MECHANICAL.** `G(c_-,x)` has at least two elements at a site displaced in
two coordinates, so (0.4)'s inner `Σ_{Γ∈G} 1/|G|` is a GENUINE average of more than one loop
logarithm — while CMP98 (15)=(42)=(43) takes `log` of ONE contour variable. `exp` of an average of
distinct logarithms is not `exp` of any one of them, so the two formulas are not the same function
of `U`, whatever `LogExpAd` is supplied.

(This does not by itself prove `blockedGauge ≠ stridedBlockedGauge` as VALUES for every `P` — the
degenerate `LogExpAd`s collapse both to the bare holonomy. It proves the two DEFINITIONS average
over index sets of different size, which is the difference Bałaban himself names on CMP109 p.253
directly under (0.4).) -/
theorem contourFamily_card_ge_two : 2 ≤ (contourFamily witnessY witnessX).card := by
  have h1 : contourSteps 1 witnessY witnessX ∈ contourFamily witnessY witnessX := by
    simp [contourFamily]
  have h2 : contourSteps (Equiv.swap 0 2) witnessY witnessX
      ∈ contourFamily witnessY witnessX :=
    Finset.mem_image.mpr ⟨Equiv.swap 0 2, Finset.mem_univ _, rfl⟩
  have hne : contourSteps 1 witnessY witnessX
      ≠ contourSteps (Equiv.swap 0 2) witnessY witnessX := by
    rw [contourSteps_id, contourSteps_swap]
    decide
  exact Finset.one_lt_card.mpr ⟨_, h1, _, h2, hne⟩

/-! The single-axis witness is `QOne.site1 = (1,0,0)` on the same lattice — **not a new
definition**.
The lane's first draft declared its own `axisWitness := fun μ => if μ = 0 then 1 else 0` on the
stated ground that "the tree carries no single-axis displacement from `witnessY`"
(`AdmissibleSubspace`'s `witnessX` moves two coordinates; `overlapStart`, `boundaryCenter` and
`outsideX` move three). That absence claim was FALSE and the duplicate was deleted:
`QOne.site1` (`QOne.lean:326`, *"the SECOND site of the `μ=0` axis"*) is the same function, on the
same `witnessL`, and `QOne` was already in this module's import closure. The shape index does not
separate these — both sit in the trivial `RESULT(PeriodicLatticeSite witnessL)` group of 286 — and
the ASCII grep that finds it (`if μ.val = 0 then 1 else 0`) is not the spelling this lane used.
Found by this lane's nested validator; recorded because it is the same LAW-19 failure mode the
header above describes for `Ū`. -/

open AdalyFormal.Balaban.QOne (site1)

/-- **The other side of the dichotomy, so `contourFamily_card_ge_two` is not cherry-picked.** At a
displacement along a single AXIS the permutation family collapses to ONE contour, and there (0.4)'s
inner average and (15)'s single logarithm do coincide. So the two formulas differ exactly off the
axes — which is why difference 1 is a real difference and not an artefact of the chosen witness. -/
theorem contourFamily_card_axis : (contourFamily witnessY site1).card = 1 := by decide

/-- `site1` is in the DIRECT `ell²`-block. (`QOne.site1_mem_block` is the same fact at
`witnessEll = 2`; the direct block of difference 2 is at side `4`, so it is proved here.) -/
theorem site1_mem_blockOf_four : site1 ∈ blockOf witnessY 4 := by decide

/-- …but the level-2 ITERATE never reads it: `(1,0,0)` is not on the stride-`2` sublattice. -/
theorem site1_not_mem_stepBlockOf : site1 ∉ stepBlockOf witnessY 2 2 := by decide

/-- **DIFFERENCE 2, MADE MECHANICAL.** With `ell = 2`, `blockedGauge P (ell²) = blockedGauge P 4`
averages over `blockOf c₋ 4` — the CONTIGUOUS `4³ = 64` fine sites — whereas the level-2 factor of
(43)'s iterate averages over `stepBlockOf c₋ 2 2` — the STRIDED `2³ = 8` sites of `Ω^{(1)}`. The two
operators read different sites, so the direct `ell^l`-blocking is not the `l`-fold iterate. -/
theorem blockOf_ne_stepBlockOf : blockOf witnessY 4 ≠ stepBlockOf witnessY 2 2 :=
  fun h => site1_not_mem_stepBlockOf (h ▸ site1_mem_blockOf_four)

/-- The counts, so the difference is legible: `64` against `8`. -/
theorem card_blockOf_four : (blockOf witnessY 4).card = 64 := by decide

theorem card_stepBlockOf_two_two : (stepBlockOf witnessY 2 2).card = 8 := by decide

/-! ## §10 — THE DISCHARGE: `QjComposite`'s §5 assumption, supplied

`QjComposite.Qcomposite_gaugeTransform` proves the composite's covariance for a background tower
that is transformed BY DEFINITION (`fun l => coarseGaugeTransform (ell^l) γ (bg l)`). §10 replaces
that definitional law by the PROVED one: instantiate `bg := UbarTower P ell U` and the hypothesis
is discharged by `UbarTower_gauge`, with no assumption left standing. -/

/-- **The tower built here is a tower `Qcomposite` accepts, and its transformation law is the one
`Qcomposite_gaugeTransform` needs.** Gauge-transforming the FINE configuration `U` and building the
tower from `U^γ` gives exactly the `Ad`-conjugated composite. -/
theorem tower_feeds_Qcomposite {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : LogExpAd (Matrix.specialUnitaryGroup (Fin 2) ℂ) 𝔤) (ell : ℕ)
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (j : ℕ) (lam : PeriodicLatticeSite L → SuTwo) :
    Qcomposite (UbarTower P ell (periodicGaugeTransform γ U)) ell j
        (fun x => RMap (γ x) (lam x))
      = fun y => RMap (γ y) (Qcomposite (UbarTower P ell U) ell j lam y) := by
  have h : UbarTower P ell (periodicGaugeTransform γ U)
      = fun l => coarseGaugeTransform (ell ^ l) γ (UbarTower P ell U l) := by
    funext l
    rw [UbarTower_gauge]
  rw [h]
  exact Qcomposite_gaugeTransform _ ell γ j lam

#print axioms coarseBond_eq_edge
#print axioms coarseBondFun_eq_linkConfig
#print axioms blockedGauge_typechecks_as_config
#print axioms coarseShift_eq_shiftBy
#print axioms coarseGaugeTransform_eq
#print axioms coarsePathEndpoint_coarseShift
#print axioms coarsePathEndpoint_comm
#print axioms cPlusS_eq
#print axioms coarseBondVar_gauge
#print axioms gammaVarStrided_gauge
#print axioms loopVar_gauge
#print axioms stridedBlockedGauge_gauge
#print axioms UbarTower_zero
#print axioms UbarTower_succ
#print axioms UbarTower_gauge
#print axioms UbarTower_gauge'
#print axioms output_stride_is_s_mul_ell
#print axioms tower_stride
#print axioms UbarTower_one
#print axioms stepBlockOf_nonempty
#print axioms tower_block_nonempty
#print axioms stepBlockOf_ell_zero
#print axioms stepBlockOf_stride_zero
#print axioms exp_zero_conj
#print axioms stridedBlockedGauge_ell_zero
#print axioms stepBlockOf_ell_one
#print axioms coarseGammaPath_self
#print axioms stridedBlockedGauge_ell_one
#print axioms UbarTower_ell_zero
#print axioms contourSteps_id
#print axioms contourSteps_swap
#print axioms contourFamily_card_ge_two
#print axioms contourFamily_card_axis
#print axioms site1_mem_blockOf_four
#print axioms site1_not_mem_stepBlockOf
#print axioms blockOf_ne_stepBlockOf
#print axioms card_blockOf_four
#print axioms card_stepBlockOf_two_two
#print axioms tower_feeds_Qcomposite

end AdalyFormal.Balaban.UbarTowerCov
