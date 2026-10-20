/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantHjMinimizer
import AdalyFormal.Balaban.ReparamCDisjoint
import AdalyFormal.Balaban.CovarianceG1
import AdalyFormal.Lattice.Witness

set_option autoImplicit false

/-!
# `CoarseRestrictTransported` — the TRANSPORT-WEIGHTED site averaging `Q'(U)`

**What this module builds, and nothing more.** ONE missing operator: the `U`-dependent,
transport-weighted site averaging that CMP99b (3.19) writes, together with the kernel subspace it
defines, its exact gauge covariance, and a proof that its kernel genuinely DIFFERS from the flat
kernel already in the tree. It builds no RG ladder, and it closes no coercivity target: this file
contains no statement about `γ₀`, about CMP99b p.428, or about any `Δ_k` tower. Its consumers are
not retrofitted — `CovariantHjMinimizer.kernelSubspaceCov` and everything above it is left exactly
as it stands, and the two objects are compared here rather than one replacing the other.

## The defect this repairs (source-pinned)

`CovariantHjMinimizer.coarseRestrictSiteCovariant ell lam y = (1/ell³) • Σ_{x ∈ blockOf y ell} lam x`
takes **no `U` argument at all**, and `kernelSubspaceCov` therefore has no `U` argument either. The
source's operator does. CMP99b (3.19), page `corpus/pages/CMP99b_p393.md` (`verification_status:
single-read`, so the load-bearing reading was taken from the 400dpi image
`corpus/renders/CMP99b_p393-05.png` — LAW-11), VERBATIM:

> `(Q'_j(U)λ)(y) = Σ_{x∈B^j(y)} L^{-jd} R(U(Γ^{(j)}_{y,x})) λ(x)`

Every summand carries `R(U(Γ_{y,x}))`, the adjoint action of the background parallel transporter
from the block anchor `y` to the fine site `x`.

## The contour `Γ_{y,x}`, and WHICH page defines it

The contour family is pinned in the source, at ADJUDICATED corpus grade, and the definition is NOT
on the page that uses it:

* `corpus/pages/CMP98_p24.md` (`verification_status: adjudicated`), VERBATIM: "let us introduce
  locally the axial gauge with the initial point `y`. This means that we take the contours
  `Γ_{y,x} = [y,(y₁,…,y_{d−1},x_d)] ∪ … ∪ [y₁,x₂,…,x_d), x]`" — the bracket mismatch is the source's
  own and is preserved here, not silently repaired. This is the COORDINATE-ORDERED AXIAL STAIRCASE:
  the LAST coordinate is adjusted FIRST, coordinate `1` LAST.
* `corpus/pages/CMP98_p19.md` (`verification_status: adjudicated`), (14)–(15): the contour
  concatenation `Γ_{c₋,x} ∪ [x,x(c)] ∪ Γ_{x(c),c₊}`, and the group average with transports
  `U(Γ_{c,x})U(c)⁻¹`.

On this tree's `d = 3`, 0-indexed carrier, "paper coordinate `d` first, paper coordinate `1` last"
is "Lean coordinate `2` first, Lean coordinate `0` last" — which is EXACTLY the order
`AdmissibleSubspace.corner1`/`corner2`/`staircasePath` already encode (that module's §3 derives the
same order independently from CMP96 printed p.244's telescoping). **This file therefore does not
introduce a second contour convention**: it adds the ORDERED (`List`-valued) refinement of the
already-adjudicated `staircasePath`, because a `Finset` of bonds cannot carry a noncommutative
ordered product, and it PROVES the two agree as bond sets (`staircaseBonds_toFinset_eq_staircasePath`,
§2c) rather than asserting it in prose.

## Orientation: no inverses — VERIFIED, not assumed

The transport is a product of FORWARD link variables only (`axisBonds` emits `(z, μ)`, never an
inverse). That is only correct because for `x ∈ blockOf y ell` every coordinate offset satisfies
`0 ≤ (x μ).val - (y μ).val` (`AdmissibleSubspace.inBlock`'s own first conjunct), so each of the three
axial legs sweeps UPWARD. This file does not take that on faith:

* `staircaseEndpoint_of_le` proves the forward product's endpoint IS `x` under that hypothesis;
* `staircaseEndpoint_truncates` exhibits a concrete `(y, x)` pair with `x` OUTSIDE the block where
  the endpoint is NOT `x` — `ℕ` subtraction silently truncates the leg length to `0`, so the
  hypothesis is load-bearing, not decorative (same discipline as
  `MinSwapWitness.sum_blockOf_coord_truncates`).

## What is NOT claimed: the operator is FAMILY-DEPENDENT, and covariance is FAMILY-INDEPENDENT

Two statements, both required, neither implying the other:

1. **`Q'(U)` is NOT contour-independent.** Replacing `Γ_{y,x}` by another contour `Γ'_{y,x}` with the
   same endpoints multiplies the `x`-summand by `Ad` of the loop holonomy `U(Γ' ∪ (−Γ))`, which is
   `≠ 1` at curved `U`. Over the source's REGULAR backgrounds the difference is controlled by the
   curvature of loops inside one block, so a bound for one family transfers to another with a
   degraded constant; over UNRESTRICTED `U` loop holonomies are `O(1)` and **nothing transfers
   between families** — any unrestricted-`U` statement about this operator is FAMILY-RELATIVE and
   must pin the family in its own statement. Nothing in this file is stated uniformly over
   unrestricted `U`.
2. **Covariance IS family-independent.** `staircaseTransport_gaugeTransform` /
   `coarseRestrictSiteCovariantU_gaugeTransform` below prove exact `Ad`-covariance, and their proof
   uses only that the chosen path is a connected chain from `y` to `x` — it never uses which chain.
   The choice of family selects WHICH covariant subspace `N(Q'(U))` is, not WHETHER it is covariant.

## Relation to `CovarianceG1.QMap` — DISCLOSED OVERLAP, and its named residual CLOSED

`Balaban/CovarianceG1.lean` already builds the same ARITHMETIC SHAPE: `QMap Qd μ y = Σ_{x ∈ Qd.B y}
((Qd.L)^Qd.d)⁻¹ • Qd.Rconj y x (μ x)`, over ABSTRACT `Site`/`Center`/`𝔤`, with the conjugation family
`Rconj` as a FREE STRUCTURE FIELD. That file's own §1b names the missing piece exactly: "`Rconj y x
:= RMap (holonomy along Γ_{y,x})` ... **This bridge is not built in this file** — doing so needs the
periodic-lattice contour object `Γ_{y,x}` ..., which is a separate, currently-unlocated
construction."

This file supplies that contour object, and rather than leaving a second same-shaped operator in the
tree undisclosed, it CLOSES that residual from this side (§7): `transportedQData` instantiates
`CovarianceG1.QData` with `Rconj y x := RMap (staircaseTransport U y x)`, and
`QMap_transportedQData` proves `QMap (transportedQData U ell hdvd) lam c =
coarseRestrictSiteCovariantU U ell lam c.1` — so the abstract operator and the concrete one are the
SAME object at the SU(2) periodic lattice, not two rival definitions. `CovarianceG1.lean` is NOT
edited (its own header: "NAMES DELIBERATELY NOT CHANGED — several lanes touch this file family");
the instantiation lives here, where it is additive.

Two facts fall out of the bridge worth recording. (i) `BlockGeometry.card_block : ∀ y, (B y).card =
L ^ d` is a PROOF FIELD, so the abstract framework cannot be instantiated at all without the
truncation guard — `transportedQData` is forced to carry `∀ μ, ell ∣ (L μ + 1)` and to take its
centers in `AdmissibleSubspace.AlignedCoarseCenter`, discharging `card_block` via
`alignedCoarseCenter_card`. (ii) The weight matches: `CovarianceG1`'s own banner establishes that the
GAUGE/SITE sector's weight is `L^{-d}` (CMP95 (1.20)) and the BOND sector's is `L^{-(d+1)}` (CMP95
(1.18)). This file is the GAUGE/SITE sector — `lam : Site → 𝔰𝔲(2)`, output site-indexed — so `1/ell³`
= `L^{-d}` at `d = 3` is the correct weight here, and no bond-sector consumer may instantiate it.

## Normalization

`(1/ell³)` denotes the source's `L^{-jd}` average only when the block is a full `ell³` box.
`blockOf` SILENTLY TRUNCATES at the torus boundary (`MinSwapWitness.badCorner_block_card`: a card-1
"block" for `ell = 2`), so the normalization statement here
(`coarseRestrictSiteCovariantU_covariantly_constant`) carries `0 < ell`, `∀ μ, ell ∣ (L μ + 1)` and
`y ∈ CoarseLattice L ell`, discharged through `AdmissibleSubspace.card_blockOf_of_coarse` (LAW-19).
Statements that are term-by-term identities (covariance, the `U = 1` reduction, the separation
witness) need no such hypothesis and do not carry one.
-/

namespace AdalyFormal.Balaban.CoarseRestrictTransported

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf inBlock CoarseLattice
  corner1 corner2 update0_corner2_eq staircasePath axisSegment mem_axisSegment
  card_blockOf_of_coarse witnessL witnessY witnessEll witnessY_coarse)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_apply_ne pathSite_apply_self_val)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one RMap_mul_apply suTwoWitness
  suTwoWitness_ne_zero witnessMElem RMap_witnessMElem)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU coarseRestrictSiteCovariant
  coarseRestrictSiteCovariant_add coarseRestrictSiteCovariant_smul kernelSubspaceCov
  mem_kernelSubspaceCov RMap_apply_inv_cancel siteLaplacianCovLM siteFnEquiv)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `pathSite` under a no-wrap hypothesis: the closed form the staircase needs

`QOne.pathSite x μ i` (LAW-19 reuse: `Nat.iterate` of `periodicLatticeShift`, with
`ReparamCDisjoint.pathSite_apply_ne`/`pathSite_apply_self_val` already proved) is the `i`-th site
along the forward axis. The one lemma missing from the tree is the NO-WRAP inversion: walking
`t.val - (base μ).val` forward steps from `base` lands exactly on the site whose `μ`-coordinate is
`t`, PROVIDED `(base μ).val ≤ t.val`. -/

/-- **No-wrap inversion for `pathSite`.** Walking `t.val - (base μ).val` forward steps in direction
`μ` reaches `Function.update base μ t` whenever `(base μ).val ≤ t.val`. The hypothesis is what rules
out both `ℕ`-subtraction truncation and torus wraparound (`t.isLt` supplies the latter). -/
theorem pathSite_of_le (base : PeriodicLatticeSite L) (μ : Fin 3) (t : Fin (L μ + 1))
    (h : (base μ).val ≤ t.val) :
    pathSite base μ (t.val - (base μ).val) = Function.update base μ t := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    rw [Function.update_self]
    apply Fin.ext
    rw [pathSite_apply_self_val]
    have hsum : (base ν).val + (t.val - (base ν).val) = t.val := by omega
    rw [hsum, Nat.mod_eq_of_lt t.isLt]
  · rw [pathSite_apply_ne _ _ _ _ hν, Function.update_of_ne hν]

#print axioms pathSite_of_le

/-! ## §2 — the ORDERED axial staircase and its transport

`AdmissibleSubspace.staircasePath : Finset (Bond L)` is the adjudicated contour, but a `Finset`
carries no order, and the transporter `U(Γ_{y,x})` is a NONCOMMUTATIVE ordered product. So the
staircase is refit here as a `List (Bond L)`, in the source's traversal order, and §2c proves the
underlying bond SET is `staircasePath y x` unchanged. -/

/-- The ordered list of forward bonds of one axial leg: `n` steps in direction `μ` starting at
`base`. Leftmost entry is the step LEAVING `base`. -/
def axisBonds (base : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) : List (Bond L) :=
  (List.range n).map (fun i => (pathSite base μ i, μ))

/-- **`U(Γ) := ∏_{b ∈ Γ} U(b)`, ordered, leftmost = first step.** With this tree's own convention
`(D_Uλ)(b) = R(U(b))λ(b₊) − λ(b₋)` (`CovariantOperators.gradValueCovariant`), `U(b)` carries the
fibre at `b₊` to the fibre at `b₋`; hence the product taken in traversal order from `y` carries the
fibre at the FAR endpoint to the fibre at `y`, which is the slot `R(U(Γ_{y,x}))λ(x)` needs. -/
def pathTransport {G : Type*} [Group G] (U : PeriodicLinkConfiguration G L)
    (bs : List (Bond L)) : G :=
  (bs.map U).prod

theorem pathTransport_nil {G : Type*} [Group G] (U : PeriodicLinkConfiguration G L) :
    pathTransport U ([] : List (Bond L)) = 1 := rfl

theorem pathTransport_append {G : Type*} [Group G] (U : PeriodicLinkConfiguration G L)
    (bs cs : List (Bond L)) :
    pathTransport U (bs ++ cs) = pathTransport U bs * pathTransport U cs := by
  unfold pathTransport
  rw [List.map_append, List.prod_append]

/-- **`Γ_{y,x}`, ORDERED — CMP98 p.24 (adjudicated).** Leg 1 sweeps coordinate `2` from `y` to
`corner1 y x`; leg 2 sweeps coordinate `1` to `corner2 y x`; leg 3 sweeps coordinate `0` to `x`.
Leg lengths are the `ℕ` coordinate offsets, so this list is the source's contour exactly when those
offsets are the true (nonnegative) offsets — see `staircaseEndpoint_truncates` for what happens
otherwise. -/
def staircaseBonds (y x : PeriodicLatticeSite L) : List (Bond L) :=
  axisBonds y 2 ((x 2).val - (y 2).val) ++
    axisBonds (corner1 y x) 1 ((x 1).val - (y 1).val) ++
      axisBonds (corner2 y x) 0 ((x 0).val - (y 0).val)

/-- **`U(Γ_{y,x})`**, the ordered product of `U` along the axial staircase. Forward links only: no
inverses appear anywhere in this definition. -/
def staircaseTransport {G : Type*} [Group G] (U : PeriodicLinkConfiguration G L)
    (y x : PeriodicLatticeSite L) : G :=
  pathTransport U (staircaseBonds y x)

/-- The endpoint the ordered staircase actually reaches, computed from the same data the transport
uses (so a mismatch with `x` is a mismatch of the TRANSPORT, not of a separate bookkeeping object). -/
def staircaseEndpoint (y x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  pathSite (corner2 y x) 0 ((x 0).val - (y 0).val)

/-! ### §2a — the leg endpoints, under the in-block orientation hypothesis -/

theorem corner1_apply_one (y x : PeriodicLatticeSite L) : (corner1 y x) 1 = y 1 := by
  unfold corner1
  exact Function.update_of_ne (by decide) _ _

theorem corner1_apply_zero (y x : PeriodicLatticeSite L) : (corner1 y x) 0 = y 0 := by
  unfold corner1
  exact Function.update_of_ne (by decide) _ _

theorem corner2_apply_zero (y x : PeriodicLatticeSite L) : (corner2 y x) 0 = y 0 := by
  unfold corner2
  rw [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1), corner1_apply_zero]

/-- Leg 1 lands on `corner1 y x`. -/
theorem pathSite_leg2 {y x : PeriodicLatticeSite L} (h : (y 2).val ≤ (x 2).val) :
    pathSite y 2 ((x 2).val - (y 2).val) = corner1 y x :=
  pathSite_of_le y 2 (x 2) h

/-- Leg 2 lands on `corner2 y x`. -/
theorem pathSite_leg1 {y x : PeriodicLatticeSite L} (h : (y 1).val ≤ (x 1).val) :
    pathSite (corner1 y x) 1 ((x 1).val - (y 1).val) = corner2 y x := by
  have hb : ((corner1 y x) 1).val = (y 1).val := by rw [corner1_apply_one]
  have := pathSite_of_le (corner1 y x) 1 (x 1) (by rw [hb]; exact h)
  rw [hb] at this
  rw [this]
  rfl

/-- Leg 3 lands on `x` itself — the staircase CLOSES. -/
theorem pathSite_leg0 {y x : PeriodicLatticeSite L} (h : (y 0).val ≤ (x 0).val) :
    pathSite (corner2 y x) 0 ((x 0).val - (y 0).val) = x := by
  have hb : ((corner2 y x) 0).val = (y 0).val := by rw [corner2_apply_zero]
  have := pathSite_of_le (corner2 y x) 0 (x 0) (by rw [hb]; exact h)
  rw [hb] at this
  rw [this, update0_corner2_eq]

/-- **The forward-only product really does connect `y` to `x`** — under the coordinatewise
orientation hypothesis that `x ∈ blockOf y ell` supplies. This is the verification that "no inverses
are needed": the three legs are all traversed in the POSITIVE direction and still reach `x`. -/
theorem staircaseEndpoint_of_le {y x : PeriodicLatticeSite L}
    (h : ∀ μ : Fin 3, (y μ).val ≤ (x μ).val) : staircaseEndpoint y x = x :=
  pathSite_leg0 (h 0)

theorem staircaseEndpoint_of_mem_block {y x : PeriodicLatticeSite L} {ell : ℕ}
    (hx : x ∈ blockOf y ell) : staircaseEndpoint y x = x :=
  staircaseEndpoint_of_le (fun μ => (mem_blockOf.mp hx μ).1)

/-! ### §2b — the orientation hypothesis is LOAD-BEARING, not decoration -/

/-- A coarse anchor with a strictly positive coordinate on the witness lattice. -/
def offBlockAnchor : PeriodicLatticeSite witnessL := Function.update witnessY 0 1

/-- **`ℕ` subtraction TRUNCATES the leg length, so the forward staircase does NOT reach a site
lying BELOW the anchor.** `offBlockAnchor = (1,0,0)`, `witnessY = (0,0,0)`: coordinate `0` of the
target is SMALLER than the anchor's, the leg length truncates to `0`, and the endpoint stays at
`(1,0,0) ≠ (0,0,0)`. So `staircaseEndpoint_of_le`'s hypothesis (and hence every in-block hypothesis
downstream) is genuinely required: dropping it would leave `staircaseTransport` silently transporting
along a path that does not end where the summand's `λ(x)` lives. -/
theorem staircaseEndpoint_truncates :
    staircaseEndpoint offBlockAnchor witnessY ≠ witnessY := by decide

/-- The same fact stated as the block-membership failure it corresponds to. -/
theorem witnessY_not_mem_offBlockAnchor_block :
    witnessY ∉ blockOf offBlockAnchor witnessEll := by decide

#print axioms pathSite_leg2
#print axioms pathSite_leg1
#print axioms pathSite_leg0
#print axioms staircaseEndpoint_of_le
#print axioms staircaseEndpoint_of_mem_block
#print axioms staircaseEndpoint_truncates
#print axioms witnessY_not_mem_offBlockAnchor_block

/-! ### §2c — the ordered list carries the ADJUDICATED bond set `staircasePath y x` -/

/-- One axial leg's bond LIST has exactly the bond set of the corresponding `axisSegment`, under the
no-wrap hypothesis.

**S91 note.** The membership characterization of `axisBonds` is INLINED here rather than stated as
its own `↔ ∃ i < n, …` lemma: an `∃`-shaped conclusion would enlarge the project's S91 existential
surface for no gain, and the standing preference is to ELIMINATE an existential rather than register
one. `List.mem_map`/`List.mem_range` supply it directly. -/
theorem axisBonds_toFinset_eq_axisSegment (base : PeriodicLatticeSite L) (μ : Fin 3)
    (t : Fin (L μ + 1)) (h : (base μ).val ≤ t.val) :
    (axisBonds base μ (t.val - (base μ).val)).toFinset =
      axisSegment base μ (base μ).val t.val := by
  ext b
  rw [List.mem_toFinset, mem_axisSegment]
  unfold axisBonds
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨rfl, fun ν hν => pathSite_apply_ne _ _ _ _ hν, ?_, ?_⟩
    · rw [pathSite_apply_self_val, Nat.mod_eq_of_lt (by omega : (base μ).val + i < L μ + 1)]
      omega
    · rw [pathSite_apply_self_val, Nat.mod_eq_of_lt (by omega : (base μ).val + i < L μ + 1)]
      omega
  · rintro ⟨hdir, hoth, hlo, hhi⟩
    refine ⟨(b.1 μ).val - (base μ).val, by omega, ?_⟩
    have hb1 : pathSite base μ ((b.1 μ).val - (base μ).val) = b.1 := by
      rw [pathSite_of_le base μ (b.1 μ) hlo]
      funext ν
      by_cases hν : ν = μ
      · subst hν; rw [Function.update_self]
      · rw [Function.update_of_ne hν, (hoth ν hν).symm]
    rw [hb1, ← hdir]

/-- **The ordered staircase's bond set IS `AdmissibleSubspace.staircasePath y x`** — so this file
introduces no second contour convention: it orders the adjudicated one. Proved under the in-block
orientation hypothesis, which is exactly where `min`/`max` in `staircasePath` collapse to
`y`/`x`. -/
theorem staircaseBonds_toFinset_eq_staircasePath {y x : PeriodicLatticeSite L}
    (h : ∀ μ : Fin 3, (y μ).val ≤ (x μ).val) :
    (staircaseBonds y x).toFinset = staircasePath y x := by
  unfold staircaseBonds staircasePath
  rw [List.toFinset_append, List.toFinset_append]
  have h2 : (axisBonds y 2 ((x 2).val - (y 2).val)).toFinset =
      axisSegment y 2 (min (y 2).val (x 2).val) (max (y 2).val (x 2).val) := by
    rw [min_eq_left (h 2), max_eq_right (h 2)]
    exact axisBonds_toFinset_eq_axisSegment y 2 (x 2) (h 2)
  have h1 : (axisBonds (corner1 y x) 1 ((x 1).val - (y 1).val)).toFinset =
      axisSegment (corner1 y x) 1 (min (y 1).val (x 1).val) (max (y 1).val (x 1).val) := by
    rw [min_eq_left (h 1), max_eq_right (h 1)]
    have hb : ((corner1 y x) 1).val = (y 1).val := by rw [corner1_apply_one]
    have := axisBonds_toFinset_eq_axisSegment (corner1 y x) 1 (x 1) (by rw [hb]; exact h 1)
    rw [hb] at this
    exact this
  have h0 : (axisBonds (corner2 y x) 0 ((x 0).val - (y 0).val)).toFinset =
      axisSegment (corner2 y x) 0 (min (y 0).val (x 0).val) (max (y 0).val (x 0).val) := by
    rw [min_eq_left (h 0), max_eq_right (h 0)]
    have hb : ((corner2 y x) 0).val = (y 0).val := by rw [corner2_apply_zero]
    have := axisBonds_toFinset_eq_axisSegment (corner2 y x) 0 (x 0) (by rw [hb]; exact h 0)
    rw [hb] at this
    exact this
  rw [h2, h1, h0]

-- NOTE: there is deliberately NO `#print axioms mem_axisBonds` here. That declaration was removed
-- (its `∃`-shaped statement was inlined into the theorem above, see the S91 note). An earlier draft
-- left the `#print axioms` line behind, which produced an `error(lean.unknownIdentifier)` that FIVE
-- consecutive builds reported as clean, because the grep pattern in use (`': error:'`) does not match
-- Lean 4.31's KINDED diagnostics (`error(lean.unknownIdentifier):`). Use `': error'` without the
-- trailing colon. Caught by the nested validator, not by this lane's own audit.
#print axioms axisBonds_toFinset_eq_axisSegment
#print axioms staircaseBonds_toFinset_eq_staircasePath

/-! ### §2d — `Γ_{y,y}` is trivial, and the trivial background transports nothing -/

theorem staircaseBonds_self (y : PeriodicLatticeSite L) : staircaseBonds y y = [] := by
  unfold staircaseBonds axisBonds
  simp

theorem staircaseTransport_self {G : Type*} [Group G] (U : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) : staircaseTransport U y y = 1 := by
  unfold staircaseTransport
  rw [staircaseBonds_self]
  rfl

theorem pathTransport_one {G : Type*} [Group G] (bs : List (Bond L)) :
    pathTransport (fun _ => (1 : G)) bs = 1 := by
  unfold pathTransport
  apply List.prod_eq_one
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨b, -, hb⟩ := hg
  exact hb.symm

theorem staircaseTransport_trivialU (y x : PeriodicLatticeSite L) :
    staircaseTransport (trivialU L) y x = 1 := by
  unfold staircaseTransport trivialU
  exact pathTransport_one _

#print axioms staircaseBonds_self
#print axioms staircaseTransport_self
#print axioms staircaseTransport_trivialU

/-! ## §3 — `Q'(U)`: the transport-weighted site averaging, CMP99b (3.19) -/

/-- **`(Q'(U)λ)(y) := (1/ell³) • Σ_{x ∈ blockOf y ell} R(U(Γ_{y,x})) λ(x)`**, CMP99b (3.19) at one
level, with `Γ_{y,x}` the adjudicated axial staircase (§2). Reuses `CovariantOperators.RMap` — the
adjoint action `R(U)X = UXU⁻¹` — rather than rebuilding it (LAW-19). Setting every transport to `1`
recovers `CovariantHjMinimizer.coarseRestrictSiteCovariant` exactly (§3b). -/
noncomputable def coarseRestrictSiteCovariantU
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) : SuTwo :=
  (1 / (ell : ℝ) ^ 3) • ∑ x ∈ blockOf y ell, RMap (staircaseTransport U y x) (lam x)

/-! ### §3a — LINEARITY in `lam`: the load-bearing structural fact

Each summand is `RMap g` — a fixed `SuTwo →ₗ[ℝ] SuTwo` once `U` is fixed — applied to `lam x`, so
the whole operator is a finite `ℝ`-linear combination of linear images. This is what makes the
`Submodule` proofs of `kernelSubspaceCov` port verbatim (§4). -/

theorem coarseRestrictSiteCovariantU_add
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam1 lam2 : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    coarseRestrictSiteCovariantU U ell (lam1 + lam2) y =
      coarseRestrictSiteCovariantU U ell lam1 y + coarseRestrictSiteCovariantU U ell lam2 y := by
  simp only [coarseRestrictSiteCovariantU, Pi.add_apply, map_add]
  rw [← smul_add, ← Finset.sum_add_distrib]

theorem coarseRestrictSiteCovariantU_smul
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) (c : ℝ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    coarseRestrictSiteCovariantU U ell (c • lam) y =
      c • coarseRestrictSiteCovariantU U ell lam y := by
  simp only [coarseRestrictSiteCovariantU, Pi.smul_apply, map_smul]
  rw [smul_comm, ← Finset.smul_sum]

/-- `Q'(U)` as a genuine `LinearMap` — the object §4's `Submodule` carrier is built from. -/
noncomputable def coarseRestrictSiteCovariantULM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) :
    (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo) where
  toFun lam := coarseRestrictSiteCovariantU U ell lam
  map_add' lam1 lam2 := funext fun y => coarseRestrictSiteCovariantU_add U ell lam1 lam2 y
  map_smul' c lam := funext fun y => coarseRestrictSiteCovariantU_smul U ell c lam y

theorem coarseRestrictSiteCovariantULM_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) :
    coarseRestrictSiteCovariantULM U ell lam = coarseRestrictSiteCovariantU U ell lam := rfl

#print axioms coarseRestrictSiteCovariantU_add
#print axioms coarseRestrictSiteCovariantU_smul
#print axioms coarseRestrictSiteCovariantULM_apply

/-! ### §3b — reduction at `U = 1`: a genuine GENERALISATION, not a rival object -/

/-- **`Q'(1) = Q'_flat`.** At the trivial background every transport is `1` and `R(1) = id`, so the
new operator is literally the tree's existing flat one — the compatibility check that makes this a
generalisation rather than a competing definition. -/
theorem coarseRestrictSiteCovariantU_trivialU (ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo)
    (y : PeriodicLatticeSite L) :
    coarseRestrictSiteCovariantU (trivialU L) ell lam y = coarseRestrictSiteCovariant ell lam y := by
  unfold coarseRestrictSiteCovariantU coarseRestrictSiteCovariant
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [staircaseTransport_trivialU, RMap_one]
  rfl

/-- The same, as an equality of operators (the form a consumer rewriting `Q'(1)` wants). -/
theorem coarseRestrictSiteCovariantU_trivialU_eq (ell : ℕ) :
    coarseRestrictSiteCovariantU (trivialU L) ell = coarseRestrictSiteCovariant (L := L) ell := by
  funext lam y
  exact coarseRestrictSiteCovariantU_trivialU ell lam y

#print axioms coarseRestrictSiteCovariantU_trivialU
#print axioms coarseRestrictSiteCovariantU_trivialU_eq

/-! ## §3c — the normalization is a genuine `L^{-d}` AVERAGE, and the guard it needs

`(1/ell³)` denotes CMP99b (3.19)'s `L^{-jd}` only if the block really has `ell³` sites. On the
COVARIANTLY CONSTANT mode — the field whose value at `x` is the back-transport of a fixed `v` to
`x`, i.e. exactly the mode `Q'(U)` should reproduce — the operator returns `v` on the nose. A garbage
exponent (`ell²`, `ell⁴`) makes this fail, and so does dropping the divisibility guard
(`MinSwapWitness.badCorner_block_card`: `blockOf` returns a ONE-site "block" at `ell = 2` on a
non-dividing extent). -/

theorem RMap_inv_apply_cancel (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (Y : SuTwo) :
    RMap U⁻¹ (RMap U Y) = Y := by
  have h := RMap_apply_inv_cancel U⁻¹ Y
  rwa [inv_inv] at h

theorem RMap_eq_zero_iff (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (Y : SuTwo) :
    RMap U Y = 0 ↔ Y = 0 := by
  constructor
  · intro h
    have := RMap_inv_apply_cancel U Y
    rw [h, map_zero] at this
    exact this.symm
  · intro h; rw [h, map_zero]

/-- **`Q'(U)` reproduces the covariantly constant mode exactly** — the normalization certificate.
Carries `0 < ell`, `∀ μ, ell ∣ (L μ + 1)` and `y ∈ CoarseLattice L ell`, discharged through
`AdmissibleSubspace.card_blockOf_of_coarse` (LAW-19). -/
theorem coarseRestrictSiteCovariantU_covariantly_constant
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (hell : 0 < ell) (hdvd : ∀ μ, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (v : SuTwo) :
    coarseRestrictSiteCovariantU U ell
        (fun x => RMap ((staircaseTransport U y x)⁻¹) v) y = v := by
  unfold coarseRestrictSiteCovariantU
  have hterm : ∀ x ∈ blockOf y ell,
      RMap (staircaseTransport U y x) (RMap ((staircaseTransport U y x)⁻¹) v) = v :=
    fun x _ => RMap_apply_inv_cancel _ v
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_blockOf_of_coarse hdvd hy]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [one_div, inv_mul_cancel₀ (by positivity), one_smul]

#print axioms RMap_inv_apply_cancel
#print axioms RMap_eq_zero_iff
#print axioms coarseRestrictSiteCovariantU_covariantly_constant

/-! ## §4 — EXACT `Ad`-COVARIANCE: `Q'(U^γ)∘Ad(γ) = Ad(γ)∘Q'(U)`

This is CMP98 p.19's defining condition (11) for the averaging, and CMP98 p.24's own proof mechanism
("`U^u(Γ_{c,x})U^u(c)⁻¹ = u(c₋)U(Γ_{c,x})U(c)⁻¹u⁻¹(c₋)`") — the conjugations telescope along the
contour and collapse at its initial point. Proved here for EVERY extent, EVERY `ell`, EVERY anchor
`y`, EVERY background `U` and EVERY gauge function `γ`, with NO regularity or divisibility
hypothesis, because it is a term-by-term identity.

**Family-independence, and its limit.** The proof below uses only that the contour is a connected
chain of forward bonds from `y` to `x`; it never uses WHICH chain. So covariance holds for any fixed
contour family — but the OPERATOR does not: two families differ by loop holonomies (see this file's
header). Covariance is family-independent; `Q'(U)` itself is family-dependent. -/

theorem pathTransport_singleton {G : Type*} [Group G] (U : PeriodicLinkConfiguration G L)
    (b : Bond L) : pathTransport U [b] = U b := by
  unfold pathTransport
  simp

theorem axisBonds_succ (base : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    axisBonds base μ (n + 1) = axisBonds base μ n ++ [(pathSite base μ n, μ)] := by
  unfold axisBonds
  rw [List.range_succ, List.map_append]
  rfl

/-- **One axial leg's transport under a gauge transform**: conjugation at the two endpoints, all the
intermediate factors cancelling telescopically. -/
theorem pathTransport_axisBonds_gaugeTransform {G : Type*} [Group G]
    (γ : PeriodicLatticeSite L → G) (U : PeriodicLinkConfiguration G L)
    (base : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    pathTransport (periodicGaugeTransform γ U) (axisBonds base μ n) =
      γ base * pathTransport U (axisBonds base μ n) * (γ (pathSite base μ n))⁻¹ := by
  induction n with
  | zero =>
      unfold axisBonds
      simp [pathTransport, pathSite_zero]
  | succ n ih =>
      rw [axisBonds_succ, pathTransport_append, pathTransport_append, ih,
        pathTransport_singleton, pathTransport_singleton, periodicGaugeTransform,
        ← pathSite_succ]
      group

/-- **`U^γ(Γ_{y,x}) = γ(y) · U(Γ_{y,x}) · γ(x)⁻¹`** — the transporter is `Ad`-EQUIVARIANT along the
staircase. The hypothesis is the same coordinatewise orientation `x ∈ blockOf y ell` supplies. -/
theorem staircaseTransport_gaugeTransform {G : Type*} [Group G]
    (γ : PeriodicLatticeSite L → G) (U : PeriodicLinkConfiguration G L)
    {y x : PeriodicLatticeSite L} (h : ∀ μ : Fin 3, (y μ).val ≤ (x μ).val) :
    staircaseTransport (periodicGaugeTransform γ U) y x =
      γ y * staircaseTransport U y x * (γ x)⁻¹ := by
  unfold staircaseTransport staircaseBonds
  rw [pathTransport_append, pathTransport_append, pathTransport_append, pathTransport_append,
    pathTransport_axisBonds_gaugeTransform, pathTransport_axisBonds_gaugeTransform,
    pathTransport_axisBonds_gaugeTransform, pathSite_leg2 (h 2), pathSite_leg1 (h 1),
    pathSite_leg0 (h 0)]
  group

theorem staircaseTransport_gaugeTransform_of_mem_block {G : Type*} [Group G]
    (γ : PeriodicLatticeSite L → G) (U : PeriodicLinkConfiguration G L)
    {y x : PeriodicLatticeSite L} {ell : ℕ} (hx : x ∈ blockOf y ell) :
    staircaseTransport (periodicGaugeTransform γ U) y x =
      γ y * staircaseTransport U y x * (γ x)⁻¹ :=
  staircaseTransport_gaugeTransform γ U (fun μ => (mem_blockOf.mp hx μ).1)

/-- **THE COVARIANCE THEOREM.** `Q'(U^γ)(Ad(γ)λ)(y) = Ad(γ(y))((Q'(U)λ)(y))`, exactly — no error
term, no curvature condition, no restriction on `U`. This is the property CMP98 (11) imposes and
that the FLAT operator fails (§4b). -/
theorem coarseRestrictSiteCovariantU_gaugeTransform
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    coarseRestrictSiteCovariantU (periodicGaugeTransform γ U) ell
        (fun x => RMap (γ x) (lam x)) y =
      RMap (γ y) (coarseRestrictSiteCovariantU U ell lam y) := by
  have hsum : ∀ x ∈ blockOf y ell,
      RMap (staircaseTransport (periodicGaugeTransform γ U) y x) (RMap (γ x) (lam x)) =
        RMap (γ y) (RMap (staircaseTransport U y x) (lam x)) := by
    intro x hx
    rw [staircaseTransport_gaugeTransform_of_mem_block γ U hx, ← RMap_mul_apply, ← RMap_mul_apply,
      RMap_inv_apply_cancel]
  unfold coarseRestrictSiteCovariantU
  rw [map_smul, map_sum, Finset.sum_congr rfl hsum]

#print axioms pathTransport_singleton
#print axioms axisBonds_succ
#print axioms pathTransport_axisBonds_gaugeTransform
#print axioms staircaseTransport_gaugeTransform
#print axioms staircaseTransport_gaugeTransform_of_mem_block
#print axioms coarseRestrictSiteCovariantU_gaugeTransform

/-! ## §5 — `N(Q'(U))`: the transported kernel subspace

Fable's structural claim, now MEASURED rather than asserted: because `Q'(U)` is still `ℝ`-linear in
`lam` (§3a), the three `Submodule` obligations of `CovariantHjMinimizer.kernelSubspaceCov` discharge
by the SAME three rewrites, with `coarseRestrictSiteCovariant_add`/`_smul` replaced by their
transported twins. The bodies below are that port, unchanged in shape. -/

/-- **`N(Q'(U)) := {λ : Q'(U)λ = 0 on every level}`** — the `U`-DEPENDENT kernel subspace, the object
CMP99b (3.21)'s `N(Q')` actually is. Structural port of `CovariantHjMinimizer.kernelSubspaceCov`,
reusing the same `KernelSubspace.Level` free-data packaging (LAW-19). -/
noncomputable def kernelSubspaceCovU
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) : Submodule ℝ (PeriodicLatticeSite L → SuTwo) where
  carrier := {lam | ∀ lvl ∈ levels, ∀ y ∈ lvl.2, coarseRestrictSiteCovariantU U lvl.1 lam y = 0}
  zero_mem' := by
    intro lvl _ y _
    simp [coarseRestrictSiteCovariantU]
  add_mem' := by
    intro lam1 lam2 h1 h2 lvl hlvl y hy
    rw [coarseRestrictSiteCovariantU_add, h1 lvl hlvl y hy, h2 lvl hlvl y hy, add_zero]
  smul_mem' := by
    intro c lam h lvl hlvl y hy
    rw [coarseRestrictSiteCovariantU_smul, h lvl hlvl y hy, smul_zero]

theorem mem_kernelSubspaceCovU
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {levels : List (KernelSubspace.Level L)} {lam : PeriodicLatticeSite L → SuTwo} :
    lam ∈ kernelSubspaceCovU U levels ↔
      ∀ lvl ∈ levels, ∀ y ∈ lvl.2, coarseRestrictSiteCovariantU U lvl.1 lam y = 0 := Iff.rfl

/-- Transported into `SiteFnL2 L`, mirroring `CovariantHjMinimizer.kernelSubspaceCovH` (LAW-19). -/
noncomputable def kernelSubspaceCovUH
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) :
    Submodule ℝ (CovariantHjMinimizer.SiteFnL2 L) :=
  (kernelSubspaceCovU U levels).map (siteFnEquiv L).symm.toLinearMap

/-- **`Δ₀^{cov}(U)(N(Q'(U)))`** — the image `R(U)` projects onto, now with `U` in BOTH factors, as
CMP99b (3.21) `R = Δ_U^η N(Q')` has it. Port of `CovariantHjMinimizer.deltaKernelImageCov`. -/
noncomputable def deltaKernelImageCovU
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) : Submodule ℝ (PeriodicLatticeSite L → SuTwo) :=
  Submodule.map (siteLaplacianCovLM U) (kernelSubspaceCovU U levels)

noncomputable def deltaKernelImageCovUH
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) :
    Submodule ℝ (CovariantHjMinimizer.SiteFnL2 L) :=
  (deltaKernelImageCovU U levels).map (siteFnEquiv L).symm.toLinearMap

/-- **`N(Q'(1)) = N(Q'_flat)`** — at the trivial background the transported kernel IS the tree's
existing flat kernel subspace, as a `Submodule` equality. -/
theorem kernelSubspaceCovU_trivialU (levels : List (KernelSubspace.Level L)) :
    kernelSubspaceCovU (trivialU L) levels = kernelSubspaceCov levels := by
  apply SetLike.ext
  intro lam
  rw [mem_kernelSubspaceCovU, mem_kernelSubspaceCov]
  constructor
  · intro h lvl hlvl y hy
    rw [← coarseRestrictSiteCovariantU_trivialU]
    exact h lvl hlvl y hy
  · intro h lvl hlvl y hy
    rw [coarseRestrictSiteCovariantU_trivialU]
    exact h lvl hlvl y hy

/-- **THE KERNEL IS `Ad`-COVARIANT — `N(Q'(U^γ)) = Ad(γ)·N(Q'(U))`**, in membership form. This is
the source's family-independent property: whichever contour family is fixed, the kernel is covariant.
Immediate from §4's exact covariance plus injectivity of `RMap`. -/
theorem mem_kernelSubspaceCovU_gaugeTransform
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) (lam : PeriodicLatticeSite L → SuTwo) :
    (fun x => RMap (γ x) (lam x)) ∈ kernelSubspaceCovU (periodicGaugeTransform γ U) levels ↔
      lam ∈ kernelSubspaceCovU U levels := by
  rw [mem_kernelSubspaceCovU, mem_kernelSubspaceCovU]
  constructor
  · intro h lvl hlvl y hy
    have := h lvl hlvl y hy
    rw [coarseRestrictSiteCovariantU_gaugeTransform] at this
    exact (RMap_eq_zero_iff _ _).mp this
  · intro h lvl hlvl y hy
    rw [coarseRestrictSiteCovariantU_gaugeTransform, h lvl hlvl y hy, map_zero]

#print axioms mem_kernelSubspaceCovU
#print axioms kernelSubspaceCovU_trivialU
#print axioms mem_kernelSubspaceCovU_gaugeTransform

/-! ## §6 — THE SEPARATION: the two kernels genuinely differ at nontrivial `U`, AT ZERO CURVATURE

The exhibit is `λ` supported at two sites of ONE block with `λ(x₂) = −λ(x₁)`: the FLAT sum vanishes,
while the transported sum is `(Ad(g₁) − Ad(g₂))λ(x₁) ≠ 0`.

**Regime.** The background used is `sepU := periodicGaugeTransform sepGamma (trivialU)`, a PURE
GAUGE, whose plaquette holonomy is IDENTICALLY `1` (`sepU_holonomy_eq_one`) — zero curvature, hence
inside CMP98 (52)'s regular-background condition `|U(∂p) − 1| < α₀η²` for every `α₀ > 0`. This is
deliberately NOT `CovariantHjMinimizer.adWitnessU`, whose single non-identity link gives `O(1)`
plaquette curvature and therefore sits outside the regime the source promises anything in.
`sepU ≠ trivialU` is proved (`sepU_ne_trivialU`), so the separation is not read off a degenerate
point. -/

/-- A general two-site collapse for block sums: reusable, and the technique
`CovariantHjMinimizer.coarseRestrictCovariant_gradValueCovariant_witnessLam` uses inline (LAW-19,
factored out here rather than repeated four times below). -/
theorem block_sum_pair {y a b : PeriodicLatticeSite L} {ell : ℕ}
    (f : PeriodicLatticeSite L → SuTwo) (ha : a ∈ blockOf y ell) (hb : b ∈ blockOf y ell)
    (hab : a ≠ b) (hoff : ∀ x ∈ blockOf y ell, x ≠ a → x ≠ b → f x = 0) :
    ∑ x ∈ blockOf y ell, f x = f a + f b := by
  classical
  have hSsub : ({a, b} : Finset (PeriodicLatticeSite L)) ⊆ blockOf y ell := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · rw [hz]; exact ha
    · rw [hz]; exact hb
  rw [← Finset.sum_sdiff hSsub]
  have hzero : ∀ x ∈ blockOf y ell \ ({a, b} : Finset (PeriodicLatticeSite L)), f x = 0 := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hoff x hx.1 hx.2.1 hx.2.2
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_add, Finset.sum_pair hab]

#print axioms block_sum_pair

/-- The second support site: `witnessY + e₀`, inside `blockOf witnessY witnessEll`. -/
def sepSiteB : PeriodicLatticeSite witnessL := periodicLatticeShift witnessY 0

theorem sepSiteB_ne_witnessY : sepSiteB ≠ witnessY := by decide

theorem witnessY_mem_sepBlock : witnessY ∈ blockOf witnessY witnessEll := by decide

theorem sepSiteB_mem_sepBlock : sepSiteB ∈ blockOf witnessY witnessEll := by decide

/-- `λ = w` at `witnessY`, `−w` at `sepSiteB`, `0` elsewhere: the FLAT block sum cancels exactly. -/
noncomputable def sepLam : PeriodicLatticeSite witnessL → SuTwo :=
  fun x => if x = witnessY then suTwoWitness else if x = sepSiteB then -suTwoWitness else 0

theorem sepLam_witnessY : sepLam witnessY = suTwoWitness := by
  unfold sepLam; rw [if_pos rfl]

theorem sepLam_sepSiteB : sepLam sepSiteB = -suTwoWitness := by
  unfold sepLam; rw [if_neg sepSiteB_ne_witnessY, if_pos rfl]

theorem sepLam_off {x : PeriodicLatticeSite witnessL} (h1 : x ≠ witnessY) (h2 : x ≠ sepSiteB) :
    sepLam x = 0 := by
  unfold sepLam; rw [if_neg h1, if_neg h2]

/-- The gauge function: `witnessMElem` at `sepSiteB`, `1` elsewhere. -/
noncomputable def sepGamma : PeriodicLatticeSite witnessL → Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  fun x => if x = sepSiteB then witnessMElem else 1

theorem sepGamma_witnessY : sepGamma witnessY = 1 := by
  unfold sepGamma; rw [if_neg (Ne.symm sepSiteB_ne_witnessY)]

theorem sepGamma_sepSiteB : sepGamma sepSiteB = witnessMElem := by
  unfold sepGamma; rw [if_pos rfl]

/-- **The separating background: a PURE GAUGE, zero curvature.** -/
noncomputable def sepU : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL :=
  periodicGaugeTransform sepGamma (trivialU witnessL)

/-- `sepU` has IDENTICALLY trivial plaquette holonomy — it is inside the source's regular regime for
every threshold, unlike `CovariantHjMinimizer.adWitnessU`. -/
theorem sepU_holonomy_eq_one (p : PeriodicLatticePlaquette witnessL) :
    periodicPlaquetteHolonomy sepU p = 1 := by
  unfold sepU
  rw [AdalyFormal.Lattice.Witness.periodicPlaquetteHolonomy_gaugeTransform]
  have htriv : periodicPlaquetteHolonomy (trivialU witnessL) p = 1 := by
    simp [periodicPlaquetteHolonomy, trivialU]
  rw [htriv, mul_one, mul_inv_cancel]

theorem witnessMElem_ne_one : witnessMElem ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  intro h
  have hR := RMap_witnessMElem
  rw [h, RMap_one, LinearMap.id_apply] at hR
  have h2 : suTwoWitness + suTwoWitness = 0 := by
    nth_rewrite 1 [hR]
    exact neg_add_cancel _
  rw [← two_smul ℝ suTwoWitness] at h2
  rcases smul_eq_zero.mp h2 with hc | hw
  · exact absurd hc (by norm_num)
  · exact suTwoWitness_ne_zero hw

/-- `sepU` is genuinely a DIFFERENT background from the trivial one: the separation below is not read
off a degenerate point. -/
theorem sepU_ne_trivialU : sepU ≠ trivialU witnessL := by
  intro h
  have hval : sepU (witnessY, (0 : Fin 3)) = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
    rw [h]; rfl
  unfold sepU periodicGaugeTransform trivialU at hval
  rw [sepGamma_witnessY] at hval
  simp only [one_mul, mul_one] at hval
  have : sepGamma sepSiteB = 1 := by
    rw [show sepSiteB = periodicLatticeShift witnessY 0 from rfl, inv_eq_one.mp hval]
  rw [sepGamma_sepSiteB] at this
  exact witnessMElem_ne_one this

theorem RMap_witnessMElem_inv : RMap witnessMElem⁻¹ suTwoWitness = -suTwoWitness := by
  have h := RMap_inv_apply_cancel witnessMElem suTwoWitness
  rw [RMap_witnessMElem, map_neg] at h
  exact neg_eq_iff_eq_neg.mp h

/-- The transport from `witnessY` to any block site, at `sepU`: `γ(y)·1·γ(x)⁻¹ = γ(x)⁻¹`. -/
theorem staircaseTransport_sepU {x : PeriodicLatticeSite witnessL}
    (hx : x ∈ blockOf witnessY witnessEll) :
    staircaseTransport sepU witnessY x = (sepGamma x)⁻¹ := by
  unfold sepU
  rw [staircaseTransport_gaugeTransform_of_mem_block sepGamma _ hx, staircaseTransport_trivialU,
    sepGamma_witnessY, one_mul, one_mul]

#print axioms sepSiteB_ne_witnessY
#print axioms witnessY_mem_sepBlock
#print axioms sepSiteB_mem_sepBlock
#print axioms sepU_holonomy_eq_one
#print axioms witnessMElem_ne_one
#print axioms sepU_ne_trivialU
#print axioms RMap_witnessMElem_inv
#print axioms staircaseTransport_sepU

/-! ### §6a — the two values: FLAT is `0`, TRANSPORTED is `(1/4)•w` -/

/-- The FLAT operator annihilates `sepLam`. -/
theorem sepLam_flat_value : coarseRestrictSiteCovariant witnessEll sepLam witnessY = 0 := by
  unfold coarseRestrictSiteCovariant
  rw [block_sum_pair sepLam witnessY_mem_sepBlock sepSiteB_mem_sepBlock
    (Ne.symm sepSiteB_ne_witnessY) (fun x _ h1 h2 => sepLam_off h1 h2)]
  rw [sepLam_witnessY, sepLam_sepSiteB, add_neg_cancel, smul_zero]

/-- The TRANSPORTED operator does not: the two `Ad`-transports differ, so the cancellation fails and
the value is `(1/ell³)•(w + w)`. -/
theorem sepLam_transported_value :
    coarseRestrictSiteCovariantU sepU witnessEll sepLam witnessY =
      (1 / (witnessEll : ℝ) ^ 3) • (suTwoWitness + suTwoWitness) := by
  unfold coarseRestrictSiteCovariantU
  congr 1
  rw [block_sum_pair (fun x => RMap (staircaseTransport sepU witnessY x) (sepLam x))
    witnessY_mem_sepBlock sepSiteB_mem_sepBlock (Ne.symm sepSiteB_ne_witnessY)
    (fun x _ h1 h2 => by rw [sepLam_off h1 h2, map_zero])]
  rw [staircaseTransport_self, RMap_one, LinearMap.id_apply, sepLam_witnessY,
    staircaseTransport_sepU sepSiteB_mem_sepBlock, sepGamma_sepSiteB, sepLam_sepSiteB, map_neg,
    RMap_witnessMElem_inv, neg_neg]

theorem sepLam_transported_ne_zero :
    coarseRestrictSiteCovariantU sepU witnessEll sepLam witnessY ≠ 0 := by
  rw [sepLam_transported_value, ← two_smul ℝ suTwoWitness, smul_smul]
  refine smul_ne_zero ?_ suTwoWitness_ne_zero
  unfold witnessEll
  norm_num

#print axioms sepLam_flat_value
#print axioms sepLam_transported_value
#print axioms sepLam_transported_ne_zero

/-! ### §6b — the kernels, separated as `Submodule`s -/

/-- One level: `ell = 2`, coarse set `{witnessY}`. -/
def sepLevels : List (KernelSubspace.Level witnessL) := [(witnessEll, {witnessY})]

theorem sepLam_mem_flat_kernel : sepLam ∈ kernelSubspaceCov sepLevels := by
  rw [mem_kernelSubspaceCov]
  intro lvl hlvl y hy
  simp only [sepLevels, List.mem_singleton] at hlvl
  subst hlvl
  simp only [Finset.mem_singleton] at hy
  subst hy
  exact sepLam_flat_value

theorem sepLam_not_mem_transported_kernel : sepLam ∉ kernelSubspaceCovU sepU sepLevels := by
  intro h
  refine sepLam_transported_ne_zero (h (witnessEll, {witnessY}) ?_ witnessY ?_)
  · simp [sepLevels]
  · simp

/-- **THE SEPARATION THEOREM.** At the pure-gauge (zero-curvature) background `sepU`, the transported
kernel subspace is NOT the flat one. So `CovariantHjMinimizer.kernelSubspaceCov` is a bound on a
DIFFERENT slice than CMP99b (3.21)'s `N(Q')`, and the `U`-dependence of the source's kernel is real,
not a notational flourish. -/
theorem kernelSubspaceCovU_ne_kernelSubspaceCov :
    kernelSubspaceCovU sepU sepLevels ≠ kernelSubspaceCov sepLevels := by
  intro h
  apply sepLam_not_mem_transported_kernel
  rw [h]
  exact sepLam_mem_flat_kernel

/-- The same fact as genuine `U`-DEPENDENCE of the transported kernel: `N(Q'(sepU)) ≠ N(Q'(1))`. -/
theorem kernelSubspaceCovU_sepU_ne_trivialU :
    kernelSubspaceCovU sepU sepLevels ≠ kernelSubspaceCovU (trivialU witnessL) sepLevels := by
  rw [kernelSubspaceCovU_trivialU]
  exact kernelSubspaceCovU_ne_kernelSubspaceCov

/-- The flat kernel is not CONTAINED in the transported one. -/
theorem flat_kernel_not_le_transported :
    ¬ (kernelSubspaceCov sepLevels ≤ kernelSubspaceCovU sepU sepLevels) := by
  intro hle
  exact sepLam_not_mem_transported_kernel (hle sepLam_mem_flat_kernel)

/-! ### §6c — and the containment fails in BOTH directions: the two subspaces are incomparable

`sepLam2 = w` at BOTH sites: the TRANSPORTED sum cancels (the two `Ad`-transports differ by exactly
the sign) while the FLAT sum doubles. So neither kernel contains the other; one is not a refinement
of the other. -/

noncomputable def sepLam2 : PeriodicLatticeSite witnessL → SuTwo :=
  fun x => if x = witnessY then suTwoWitness else if x = sepSiteB then suTwoWitness else 0

theorem sepLam2_witnessY : sepLam2 witnessY = suTwoWitness := by
  unfold sepLam2; rw [if_pos rfl]

theorem sepLam2_sepSiteB : sepLam2 sepSiteB = suTwoWitness := by
  unfold sepLam2; rw [if_neg sepSiteB_ne_witnessY, if_pos rfl]

theorem sepLam2_off {x : PeriodicLatticeSite witnessL} (h1 : x ≠ witnessY) (h2 : x ≠ sepSiteB) :
    sepLam2 x = 0 := by
  unfold sepLam2; rw [if_neg h1, if_neg h2]

theorem sepLam2_transported_value :
    coarseRestrictSiteCovariantU sepU witnessEll sepLam2 witnessY = 0 := by
  unfold coarseRestrictSiteCovariantU
  rw [block_sum_pair (fun x => RMap (staircaseTransport sepU witnessY x) (sepLam2 x))
    witnessY_mem_sepBlock sepSiteB_mem_sepBlock (Ne.symm sepSiteB_ne_witnessY)
    (fun x _ h1 h2 => by rw [sepLam2_off h1 h2, map_zero])]
  rw [staircaseTransport_self, RMap_one, LinearMap.id_apply, sepLam2_witnessY,
    staircaseTransport_sepU sepSiteB_mem_sepBlock, sepGamma_sepSiteB, sepLam2_sepSiteB,
    RMap_witnessMElem_inv, add_neg_cancel, smul_zero]

theorem sepLam2_flat_value :
    coarseRestrictSiteCovariant witnessEll sepLam2 witnessY =
      (1 / (witnessEll : ℝ) ^ 3) • (suTwoWitness + suTwoWitness) := by
  unfold coarseRestrictSiteCovariant
  rw [block_sum_pair sepLam2 witnessY_mem_sepBlock sepSiteB_mem_sepBlock
    (Ne.symm sepSiteB_ne_witnessY) (fun x _ h1 h2 => sepLam2_off h1 h2)]
  rw [sepLam2_witnessY, sepLam2_sepSiteB]

theorem sepLam2_flat_ne_zero :
    coarseRestrictSiteCovariant witnessEll sepLam2 witnessY ≠ 0 := by
  rw [sepLam2_flat_value, ← two_smul ℝ suTwoWitness, smul_smul]
  refine smul_ne_zero ?_ suTwoWitness_ne_zero
  unfold witnessEll
  norm_num

theorem sepLam2_mem_transported_kernel : sepLam2 ∈ kernelSubspaceCovU sepU sepLevels := by
  rw [mem_kernelSubspaceCovU]
  intro lvl hlvl y hy
  simp only [sepLevels, List.mem_singleton] at hlvl
  subst hlvl
  simp only [Finset.mem_singleton] at hy
  subst hy
  exact sepLam2_transported_value

theorem sepLam2_not_mem_flat_kernel : sepLam2 ∉ kernelSubspaceCov sepLevels := by
  intro h
  refine sepLam2_flat_ne_zero (h (witnessEll, {witnessY}) ?_ witnessY ?_)
  · simp [sepLevels]
  · simp

/-- **The transported kernel is not contained in the flat one either** — with
`flat_kernel_not_le_transported`, the two subspaces are INCOMPARABLE at this zero-curvature
background. -/
theorem transported_kernel_not_le_flat :
    ¬ (kernelSubspaceCovU sepU sepLevels ≤ kernelSubspaceCov sepLevels) := by
  intro hle
  exact sepLam2_not_mem_flat_kernel (hle sepLam2_mem_transported_kernel)

#print axioms sepLam_mem_flat_kernel
#print axioms sepLam_not_mem_transported_kernel
#print axioms kernelSubspaceCovU_ne_kernelSubspaceCov
#print axioms kernelSubspaceCovU_sepU_ne_trivialU
#print axioms flat_kernel_not_le_transported
#print axioms sepLam2_transported_value
#print axioms sepLam2_flat_value
#print axioms sepLam2_mem_transported_kernel
#print axioms sepLam2_not_mem_flat_kernel
#print axioms transported_kernel_not_le_flat

/-! ### §6d — the same separation stated as COVARIANCE-TRACKING: the transported operator tracks the
`Ad`-gauge action on the SAME data where the flat operator does not

Same `γ`, same `λ`, same ZERO-CURVATURE background. `Q'(U^γ)` maps `Ad(γ)λ` to
`Ad(γ(y))(Q'(1)λ)(y) = 0`; the flat operator sends `Ad(γ)λ` to a NONZERO value while
`Ad(γ(witnessY))` of its own output is `0`. This is the regime-clean replacement for
`CovariantHjMinimizer.coarseRestrictCovariant_ad_action_witness`, whose background has `O(1)`
plaquette curvature. -/

theorem sepU_transported_tracks :
    coarseRestrictSiteCovariantU sepU witnessEll (fun x => RMap (sepGamma x) (sepLam x)) witnessY =
      RMap (sepGamma witnessY) (coarseRestrictSiteCovariant witnessEll sepLam witnessY) := by
  unfold sepU
  rw [coarseRestrictSiteCovariantU_gaugeTransform, coarseRestrictSiteCovariantU_trivialU]

theorem sepU_transported_tracks_zero :
    coarseRestrictSiteCovariantU sepU witnessEll (fun x => RMap (sepGamma x) (sepLam x)) witnessY
      = 0 := by
  rw [sepU_transported_tracks, sepLam_flat_value, map_zero]

/-- **The FLAT operator fails the same tracking identity, at ZERO curvature.** -/
theorem coarseRestrictSiteCovariant_not_ad_covariant :
    coarseRestrictSiteCovariant witnessEll (fun x => RMap (sepGamma x) (sepLam x)) witnessY ≠
      RMap (sepGamma witnessY) (coarseRestrictSiteCovariant witnessEll sepLam witnessY) := by
  rw [sepLam_flat_value, map_zero]
  unfold coarseRestrictSiteCovariant
  rw [block_sum_pair (fun x => RMap (sepGamma x) (sepLam x)) witnessY_mem_sepBlock
    sepSiteB_mem_sepBlock (Ne.symm sepSiteB_ne_witnessY)
    (fun x _ h1 h2 => by rw [sepLam_off h1 h2, map_zero])]
  rw [sepGamma_witnessY, RMap_one, LinearMap.id_apply, sepLam_witnessY, sepGamma_sepSiteB,
    sepLam_sepSiteB, map_neg, RMap_witnessMElem, neg_neg, ← two_smul ℝ suTwoWitness, smul_smul]
  refine smul_ne_zero ?_ suTwoWitness_ne_zero
  unfold witnessEll
  norm_num

#print axioms sepU_transported_tracks
#print axioms sepU_transported_tracks_zero
#print axioms coarseRestrictSiteCovariant_not_ad_covariant

/-! ## §7 — CLOSING `CovarianceG1.lean` §1b's NAMED RESIDUAL from this side (LAW-19, no edit there)

`CovarianceG1.QData`'s `Rconj` field is instantiated here to the concrete staircase transport, and
`QMap` of that instance is proved EQUAL to `coarseRestrictSiteCovariantU`. Note what the abstract
framework forces: `BlockGeometry.card_block` is a PROOF field, so the instance cannot be formed
without the divisibility guard and aligned centers. -/

open AdalyFormal.Balaban.AdmissibleSubspace (AlignedCoarseCenter alignedCoarseCenter_card)
open AdalyFormal.Balaban.CovarianceG1 (QData QMap)

/-- **`Rconj y x := R(U(Γ_{y,x}))`** — the instantiation `CovarianceG1.lean` §1b named as unbuilt. -/
noncomputable def transportedQData
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) :
    QData (PeriodicLatticeSite L) (AlignedCoarseCenter L ell hdvd) SuTwo where
  B := fun c => blockOf c.1 ell
  L := ell
  d := 3
  card_block := fun c => alignedCoarseCenter_card c
  Rconj := fun c x => RMap (staircaseTransport U c.1 x)

/-- **The abstract `Q'` and the concrete `Q'(U)` are the SAME OBJECT** at the SU(2) periodic lattice
— so this file leaves no undisclosed duplicate operator in the tree. -/
theorem QMap_transportedQData
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) (lam : PeriodicLatticeSite L → SuTwo)
    (c : AlignedCoarseCenter L ell hdvd) :
    QMap (transportedQData U ell hdvd) lam c = coarseRestrictSiteCovariantU U ell lam c.1 := by
  unfold QMap coarseRestrictSiteCovariantU transportedQData
  rw [one_div, Finset.smul_sum]

#print axioms transportedQData
#print axioms QMap_transportedQData

/-! ## §8 — FAMILY-DEPENDENCE, as theorems rather than as header prose

The header asserts two things about the choice of contour family. Neither is left as prose here.

**(a) At ZERO curvature the transport depends only on the ENDPOINTS.**
`staircaseTransport_pureGauge` below evaluates to `γ(y)·γ(x)⁻¹` — a expression in which no contour
appears at all. Any family with the same telescoping property therefore gives the SAME operator at a
pure-gauge background, which is why the separation exhibit of §6 (whose contour has length ONE, so
it cannot discriminate order) is nonetheless legitimate: at zero curvature there is nothing to
discriminate.

**(b) At CURVED backgrounds the transport genuinely DIFFERS between families.**
`staircaseTransport_ne_foilStaircaseTransport` exhibits one site — the diagonal `(1,1,0)`, whose
staircase has TWO legs in different directions — and one background where the CMP98-p.24 order gives
`witnessMElem` and the foil order `(0,1,2)` gives `1`. So no downstream statement may treat the
operator as contour-independent, and any unrestricted-`U` claim about it must pin the family in its
own statement.

**Disclosed regime.** `curvedU` has NONZERO plaquette curvature (`curvedU_holonomy_ne_one`), so this
exhibit sits OUTSIDE CMP98 (52)'s regular-background condition — deliberately, since (a) proves the
difference is invisible at zero curvature. That is the honest content of "contour choice is
quantitative over regular `U`, structural over unrestricted `U`", and it is why (b) needs curvature
and could not have been exhibited inside the regular regime. -/

/-- At a pure-gauge background the staircase transport is `γ(y)·γ(x)⁻¹`: ENDPOINTS ONLY, no contour
data on the right-hand side. -/
theorem staircaseTransport_pureGauge
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    {y x : PeriodicLatticeSite L} (h : ∀ μ : Fin 3, (y μ).val ≤ (x μ).val) :
    staircaseTransport (periodicGaugeTransform γ (trivialU L)) y x = γ y * (γ x)⁻¹ := by
  rw [staircaseTransport_gaugeTransform γ (trivialU L) h, staircaseTransport_trivialU, mul_one]

/-- The DIAGONAL site `(1,1,0)`: its staircase has two legs, in directions `1` and `0`, so the
coordinate ORDER is visible in the transport (unlike §6's single-leg site). -/
def diagSite : PeriodicLatticeSite witnessL :=
  periodicLatticeShift (periodicLatticeShift witnessY 0) 1

/-- `(0,1,0)`: the corner the CMP98-p.24 order passes through. -/
def diagCorner : PeriodicLatticeSite witnessL := periodicLatticeShift witnessY 1

theorem diagSite_mem_block : diagSite ∈ blockOf witnessY witnessEll := by decide

/-- The FOIL contour family: `AdmissibleSubspace.foilStaircasePath`'s order (`0,1,2` from `y`), which
that module proves is NOT the source's. Ordered here the same way `staircaseBonds` orders the true
one, purely so the two can be compared. -/
def foilStaircaseBonds (y x : PeriodicLatticeSite L) : List (Bond L) :=
  axisBonds y 0 ((x 0).val - (y 0).val) ++
    axisBonds (AdmissibleSubspace.foilCorner1 y x) 1 ((x 1).val - (y 1).val) ++
      axisBonds (AdmissibleSubspace.foilCorner2 y x) 2 ((x 2).val - (y 2).val)

def foilStaircaseTransport {G : Type*} [Group G] (U : PeriodicLinkConfiguration G L)
    (y x : PeriodicLatticeSite L) : G :=
  pathTransport U (foilStaircaseBonds y x)

theorem staircaseBonds_diagSite :
    staircaseBonds witnessY diagSite = [(witnessY, 1), (diagCorner, 0)] := by decide

theorem foilStaircaseBonds_diagSite :
    foilStaircaseBonds witnessY diagSite = [(witnessY, 0), (sepSiteB, 1)] := by decide

/-- A background with ONE non-identity link, at `(witnessY, 1)`. Curved (below), and deliberately so:
at zero curvature the two families cannot differ. -/
noncomputable def curvedU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL :=
  fun e => if e = (witnessY, (1 : Fin 3)) then witnessMElem else 1

/-- The plaquette at `witnessY` in the `(0,1)` plane. -/
def curvedPlaq : PeriodicLatticePlaquette witnessL := (witnessY, ⟨(0, 1), by decide⟩)

theorem curvedU_holonomy_ne_one : periodicPlaquetteHolonomy curvedU curvedPlaq ≠ 1 := by
  have h0 : curvedU (witnessY, (0 : Fin 3)) = 1 := by
    unfold curvedU; rw [if_neg (by decide)]
  have h1 : curvedU (witnessY, (1 : Fin 3)) = witnessMElem := by
    unfold curvedU; rw [if_pos rfl]
  have h2 : curvedU (sepSiteB, (1 : Fin 3)) = 1 := by
    unfold curvedU; rw [if_neg (by decide)]
  have h3 : curvedU (diagCorner, (0 : Fin 3)) = 1 := by
    unfold curvedU; rw [if_neg (by decide)]
  show curvedU (witnessY, (0 : Fin 3)) * curvedU (periodicLatticeShift witnessY 0, (1 : Fin 3)) *
      (curvedU (periodicLatticeShift witnessY 1, (0 : Fin 3)))⁻¹ *
      (curvedU (witnessY, (1 : Fin 3)))⁻¹ ≠ 1
  rw [show periodicLatticeShift witnessY 0 = sepSiteB from rfl,
    show periodicLatticeShift witnessY 1 = diagCorner from rfl, h0, h1, h2, h3]
  simp only [one_mul, inv_one, mul_one]
  rw [inv_ne_one]
  exact witnessMElem_ne_one

theorem staircaseTransport_curvedU_diag :
    staircaseTransport curvedU witnessY diagSite = witnessMElem := by
  unfold staircaseTransport
  rw [staircaseBonds_diagSite]
  unfold pathTransport
  have h1 : curvedU (witnessY, (1 : Fin 3)) = witnessMElem := by
    unfold curvedU; rw [if_pos rfl]
  have h3 : curvedU (diagCorner, (0 : Fin 3)) = 1 := by
    unfold curvedU; rw [if_neg (by decide)]
  simp [h1, h3]

theorem foilStaircaseTransport_curvedU_diag :
    foilStaircaseTransport curvedU witnessY diagSite = 1 := by
  unfold foilStaircaseTransport
  rw [foilStaircaseBonds_diagSite]
  unfold pathTransport
  have h0 : curvedU (witnessY, (0 : Fin 3)) = 1 := by
    unfold curvedU; rw [if_neg (by decide)]
  have h2 : curvedU (sepSiteB, (1 : Fin 3)) = 1 := by
    unfold curvedU; rw [if_neg (by decide)]
  simp [h0, h2]

/-- **THE FAMILY-DEPENDENCE THEOREM.** The source's coordinate order and the foil order give
DIFFERENT transporters between the SAME two endpoints at a curved background — so `Q'(U)` is
contour-family-dependent, exactly as this file's header states and never denies. -/
theorem staircaseTransport_ne_foilStaircaseTransport :
    staircaseTransport curvedU witnessY diagSite ≠
      foilStaircaseTransport curvedU witnessY diagSite := by
  rw [staircaseTransport_curvedU_diag, foilStaircaseTransport_curvedU_diag]
  exact witnessMElem_ne_one

#print axioms staircaseTransport_pureGauge
#print axioms diagSite_mem_block
#print axioms staircaseBonds_diagSite
#print axioms foilStaircaseBonds_diagSite
#print axioms curvedU_holonomy_ne_one
#print axioms staircaseTransport_curvedU_diag
#print axioms foilStaircaseTransport_curvedU_diag
#print axioms staircaseTransport_ne_foilStaircaseTransport

/-! ## §9 —  COVERAGE: every remaining declaration of this file, including every
`def`, so the audit surface is the whole file and not just its headline theorems. -/

#print axioms axisBonds
#print axioms coarseRestrictSiteCovariantU
#print axioms coarseRestrictSiteCovariantULM
#print axioms corner1_apply_one
#print axioms corner1_apply_zero
#print axioms corner2_apply_zero
#print axioms curvedPlaq
#print axioms curvedU
#print axioms deltaKernelImageCovU
#print axioms deltaKernelImageCovUH
#print axioms diagCorner
#print axioms diagSite
#print axioms foilStaircaseBonds
#print axioms foilStaircaseTransport
#print axioms kernelSubspaceCovU
#print axioms kernelSubspaceCovUH
#print axioms offBlockAnchor
#print axioms pathTransport
#print axioms pathTransport_append
#print axioms pathTransport_nil
#print axioms pathTransport_one
#print axioms sepGamma
#print axioms sepGamma_sepSiteB
#print axioms sepGamma_witnessY
#print axioms sepLam
#print axioms sepLam2
#print axioms sepLam2_flat_ne_zero
#print axioms sepLam2_off
#print axioms sepLam2_sepSiteB
#print axioms sepLam2_witnessY
#print axioms sepLam_off
#print axioms sepLam_sepSiteB
#print axioms sepLam_witnessY
#print axioms sepLevels
#print axioms sepSiteB
#print axioms sepU
#print axioms staircaseBonds
#print axioms staircaseEndpoint
#print axioms staircaseTransport

/-! ## §10 — the PROJECTION layer also rebuilds: `R(U)` on the TRANSPORTED image

Fable's claim was that `RcovLM` and everything above it "rebuild verbatim" once the operator is
still linear. §5 measured that for the `Submodule` layer. This section measures it for the layer that
actually needed a Hilbert-space fact — the orthogonal projection — by porting
`CovariantHjMinimizer`'s `RcovFun`/`RcovLM`/§8c onto `deltaKernelImageCovUH`. The claim HOLDS: the
same four proofs go through with the transported submodule substituted.

**One improvement over the object ported from.** `CovariantHjMinimizer.RcovFun` carries
`[(deltaKernelImageCovH U levels).HasOrthogonalProjection]` as an instance BRACKET, with its §8d
recording that the bracket is always dischargeable by `#synth`. Here the instance is DISCHARGED, not
carried: `deltaKernelImageCovUH_hasOrthogonalProjection` proves it by `infer_instance` for every `U`
and `levels`, and the definitions below take no instance argument at all. An always-dischargeable
hypothesis left in a signature is precisely the shape of residual that passes every gate while
nobody discharges it. -/

/-- The `HasOrthogonalProjection` instance is DISCHARGED, for every `U` and `levels`: `SiteFnL2 L` is
finite-dimensional, so Mathlib's own instance chain supplies it. No bracket travels downstream. -/
theorem deltaKernelImageCovUH_hasOrthogonalProjection
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) :
    (deltaKernelImageCovUH U levels).HasOrthogonalProjection := by infer_instance

theorem mem_deltaKernelImageCovUH
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) {v : CovariantHjMinimizer.SiteFnL2 L} :
    v ∈ deltaKernelImageCovUH U levels ↔ siteFnEquiv L v ∈ deltaKernelImageCovU U levels := by
  unfold deltaKernelImageCovUH
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨lam, hlam, hEq⟩
    have heq2 : (siteFnEquiv L).symm lam = v := hEq
    rw [← heq2]; simpa using hlam
  · intro hv
    exact ⟨siteFnEquiv L v, hv, by simp⟩

/-- **`R(U)` on the transported image**, as a bare function — same construction as
`CovariantHjMinimizer.RcovFun`, with `deltaKernelImageCovH` replaced by `deltaKernelImageCovUH`. -/
noncomputable def RcovUFun
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) :
    (PeriodicLatticeSite L → SuTwo) → (PeriodicLatticeSite L → SuTwo) :=
  fun lam =>
    siteFnEquiv L ((deltaKernelImageCovUH U levels).starProjection ((siteFnEquiv L).symm lam))

noncomputable def RcovULM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) :
    (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo) where
  toFun := RcovUFun U levels
  map_add' a b := by
    unfold RcovUFun
    rw [map_add, map_add, map_add]
  map_smul' c a := by
    unfold RcovUFun
    rw [map_smul, map_smul, map_smul, RingHom.id_apply]

theorem RcovUFun_mem
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) (lam : PeriodicLatticeSite L → SuTwo) :
    RcovUFun U levels lam ∈ deltaKernelImageCovU U levels := by
  unfold RcovUFun
  exact (mem_deltaKernelImageCovUH U levels).mp (Submodule.starProjection_apply_mem _ _)

theorem RcovUFun_idem
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) (lam : PeriodicLatticeSite L → SuTwo) :
    RcovUFun U levels (RcovUFun U levels lam) = RcovUFun U levels lam := by
  unfold RcovUFun
  rw [CovariantHjMinimizer.siteFnEquiv_symm_apply, WithLp.toLp_ofLp]
  congr 1
  exact congrFun (congrArg DFunLike.coe (Submodule.isIdempotentElem_starProjection
    (deltaKernelImageCovUH U levels))) _

theorem RcovUFun_fixes
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) {lam : PeriodicLatticeSite L → SuTwo}
    (h : lam ∈ deltaKernelImageCovU U levels) : RcovUFun U levels lam = lam := by
  unfold RcovUFun
  have hmem : (siteFnEquiv L).symm lam ∈ deltaKernelImageCovUH U levels := by
    rw [mem_deltaKernelImageCovUH]
    simpa using h
  rw [Submodule.starProjection_eq_self_iff.mpr hmem]
  simp

theorem RcovUFun_selfAdjoint
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) (lam1 lam2 : PeriodicLatticeSite L → SuTwo) :
    CovariantHjMinimizer.covSiteInner (RcovUFun U levels lam1) lam2 =
      CovariantHjMinimizer.covSiteInner lam1 (RcovUFun U levels lam2) := by
  unfold RcovUFun
  rw [← CovariantHjMinimizer.inner_siteFnL2_eq_covSiteInner,
    ← CovariantHjMinimizer.inner_siteFnL2_eq_covSiteInner]
  rw [CovariantHjMinimizer.siteFnEquiv_symm_apply, CovariantHjMinimizer.siteFnEquiv_symm_apply,
    WithLp.toLp_ofLp, WithLp.toLp_ofLp]
  exact Submodule.starProjection_isSymmetric (deltaKernelImageCovUH U levels) _ _

#print axioms deltaKernelImageCovUH_hasOrthogonalProjection
#print axioms mem_deltaKernelImageCovUH
#print axioms RcovUFun
#print axioms RcovULM
#print axioms RcovUFun_mem
#print axioms RcovUFun_idem
#print axioms RcovUFun_fixes
#print axioms RcovUFun_selfAdjoint

/-! ## §11 — A NEGATIVE RESULT THIS LANE OWES: at `sepLevels` the kernel separation does NOT reach
the subspace `R(U)` projects onto

§6 proves the two KERNELS are incomparable. A reader could take that to mean the whole chain above
them separates too. It does not, and the honest thing is to prove that here rather than let it be
found later.

**The mechanism.** `Δ₀^{cov}(U) = D_U^*D_U` kills the pure-gauge zero modes `x ↦ Ad(γ(x))c`
(`gradValueCovariant_pureGaugeZeroMode`), a THREE-real-dimensional family (one `c ∈ 𝔰𝔲(2)`), and at a
level structure with a SINGLE coarse site the constraint `Q'λ(y) = 0` is exactly THREE real
conditions. Both `Q'(sepU)` and `Q'_flat` map that zero-mode family ONTO `𝔰𝔲(2)`
(`coarseRestrictSiteCovariantU_zeroMode`, `coarseRestrictSiteCovariant_zeroMode` — the second needs
the explicit inverse of `c ↦ (7c + Ad(M)c)/8`, supplied via `Ad(M)² = id`). So every `λ` can be
corrected by a `Δ`-invisible zero mode into either kernel, and

  `deltaKernelImageCovU sepU sepLevels = deltaKernelImageCov sepU sepLevels = Δ₀^{cov}(sepU)(⊤)`,

both being the FULL range. `R(U)` built on either is therefore the SAME projection at this witness.

**What this does and does not say.** It does NOT weaken §6: the kernels genuinely differ, and CMP99b
(3.21)'s `N(Q')` genuinely is the transported one, so building on the flat kernel is still building on
the wrong object. What it says is that a ONE-COARSE-SITE level structure cannot exhibit the
consequence — the constraint's codimension is exactly absorbed by `Δ`'s zero modes. Any downstream
claim that the transported kernel CHANGES `R(U)` must therefore be made at a level structure with
more constraints than `Δ` has zero modes, and this file does not supply such a witness. That is a
statement about the WITNESS, proved, not a limitation of the operator. -/

/-- Subtraction form of linearity for the transported operator (the image argument below corrects
`lam` by a zero mode, i.e. subtracts). -/
theorem coarseRestrictSiteCovariantU_sub
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (lam1 lam2 : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    coarseRestrictSiteCovariantU U ell (lam1 - lam2) y =
      coarseRestrictSiteCovariantU U ell lam1 y - coarseRestrictSiteCovariantU U ell lam2 y := by
  simp only [coarseRestrictSiteCovariantU, Pi.sub_apply, map_sub]
  rw [← smul_sub, ← Finset.sum_sub_distrib]

/-- The same for the FLAT operator (`CovariantHjMinimizer` exports `_add`/`_smul` but not `_sub`). -/
theorem coarseRestrictSiteCovariant_sub (ell : ℕ)
    (lam1 lam2 : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    coarseRestrictSiteCovariant ell (lam1 - lam2) y =
      coarseRestrictSiteCovariant ell lam1 y - coarseRestrictSiteCovariant ell lam2 y := by
  simp only [coarseRestrictSiteCovariant, Pi.sub_apply]
  rw [← smul_sub, ← Finset.sum_sub_distrib]

#print axioms coarseRestrictSiteCovariantU_sub
#print axioms coarseRestrictSiteCovariant_sub

/-- `Ad(M)² = id` on `𝔰𝔲(2)`: `M² = −1` and conjugation by `−1` is trivial. -/
theorem RMap_witnessMElem_involutive (X : SuTwo) :
    RMap witnessMElem (RMap witnessMElem X) = X := by
  rw [RMap_mul_apply]
  apply Subtype.ext
  rw [CovariantOperators.RMap_coe_apply]
  have hmm : ((witnessMElem * witnessMElem : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    show CovariantOperators.witnessM * CovariantOperators.witnessM = -1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CovariantOperators.witnessM, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hmm]
  simp

/-- **The pure-gauge zero mode.** `x ↦ Ad(γ(x))c` is annihilated by `D_U` at `U = U^γ` from the
trivial background — for every extent, every `γ`, every `c`. -/
theorem gradValueCovariant_pureGaugeZeroMode
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (c : SuTwo) :
    CovariantOperators.gradValueCovariant (periodicGaugeTransform γ (trivialU L))
      (fun x => RMap (γ x) c) = 0 := by
  funext b
  simp only [CovariantOperators.gradValueCovariant, periodicGaugeTransform, trivialU, mul_one,
    Pi.zero_apply]
  rw [← RMap_mul_apply, RMap_inv_apply_cancel]
  exact sub_self _

theorem siteLaplacianCovLM_pureGaugeZeroMode
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (c : SuTwo) :
    siteLaplacianCovLM (periodicGaugeTransform γ (trivialU L)) (fun x => RMap (γ x) c) = 0 := by
  unfold siteLaplacianCovLM
  rw [LinearMap.comp_apply]
  have h : CovariantOperators.gradCovariantLM (periodicGaugeTransform γ (trivialU L))
      (fun x => RMap (γ x) c) = 0 := gradValueCovariant_pureGaugeZeroMode γ c
  rw [h, map_zero]

/-- `blockOf witnessY witnessEll` has exactly `8` sites — the divisibility guard discharged at the
witness (`2 ∣ 4` in every direction). -/
theorem card_sepBlock : (blockOf witnessY witnessEll).card = 8 := by
  have h := card_blockOf_of_coarse (L := witnessL) (ell := witnessEll) (by decide) witnessY_coarse
  rw [h]
  unfold witnessEll
  norm_num

/-- **`Q'(sepU)` maps the zero-mode family ONTO `𝔰𝔲(2)`**: the transported average of
`x ↦ Ad(γ(x))c` at the anchor is `c` itself, because each transport exactly undoes the gauge factor. -/
theorem coarseRestrictSiteCovariantU_zeroMode (c : SuTwo) :
    coarseRestrictSiteCovariantU sepU witnessEll (fun x => RMap (sepGamma x) c) witnessY = c := by
  unfold coarseRestrictSiteCovariantU
  have hterm : ∀ x ∈ blockOf witnessY witnessEll,
      RMap (staircaseTransport sepU witnessY x) (RMap (sepGamma x) c) = c := by
    intro x hx
    rw [staircaseTransport_sepU hx, RMap_inv_apply_cancel]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_sepBlock]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  unfold witnessEll
  norm_num

/-- **`Q'_flat` also maps the zero-mode family onto `𝔰𝔲(2)`** — but through the nontrivial map
`c ↦ (7c + Ad(M)c)/8`, whose inverse `b ↦ (7b − Ad(M)b)/6` is exhibited here (it is an inverse because
`Ad(M)² = id`). Stated in the SURJECTIVITY form the image argument needs: the given `b` is hit. -/
theorem coarseRestrictSiteCovariant_zeroMode (b : SuTwo) :
    coarseRestrictSiteCovariant witnessEll
        (fun x => RMap (sepGamma x) ((6 : ℝ)⁻¹ • ((7 : ℝ) • b - RMap witnessMElem b))) witnessY
      = b := by
  set c : SuTwo := (6 : ℝ)⁻¹ • ((7 : ℝ) • b - RMap witnessMElem b) with hc
  unfold coarseRestrictSiteCovariant
  have hsplit : ∑ x ∈ blockOf witnessY witnessEll, RMap (sepGamma x) c =
      (7 : ℕ) • c + RMap witnessMElem c := by
    have hsub : ({sepSiteB} : Finset (PeriodicLatticeSite witnessL)) ⊆
        blockOf witnessY witnessEll := by
      intro z hz
      rw [Finset.mem_singleton] at hz
      rw [hz]; exact sepSiteB_mem_sepBlock
    rw [← Finset.sum_sdiff hsub]
    have hconst : ∀ x ∈ blockOf witnessY witnessEll \ ({sepSiteB} : Finset _),
        RMap (sepGamma x) c = c := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
      unfold sepGamma
      rw [if_neg hx.2, RMap_one, LinearMap.id_apply]
    have hcard : (blockOf witnessY witnessEll \
        ({sepSiteB} : Finset (PeriodicLatticeSite witnessL))).card = 7 := by decide
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, Finset.sum_singleton,
      sepGamma_sepSiteB]
  rw [hsplit]
  have hinv : (7 : ℕ) • c + RMap witnessMElem c = (8 : ℝ) • b := by
    rw [hc, map_smul, map_sub, map_smul, RMap_witnessMElem_involutive,
      ← Nat.cast_smul_eq_nsmul ℝ]
    push_cast
    module
  rw [hinv, smul_smul]
  unfold witnessEll
  norm_num

#print axioms RMap_witnessMElem_involutive
#print axioms gradValueCovariant_pureGaugeZeroMode
#print axioms siteLaplacianCovLM_pureGaugeZeroMode
#print axioms card_sepBlock
#print axioms coarseRestrictSiteCovariantU_zeroMode
#print axioms coarseRestrictSiteCovariant_zeroMode

/-- **The transported image is the FULL range of `Δ₀^{cov}(sepU)`** — the constraint imposes nothing
on it at this level structure. -/
theorem deltaKernelImageCovU_sepU_eq_top_image :
    deltaKernelImageCovU sepU sepLevels = Submodule.map (siteLaplacianCovLM sepU) ⊤ := by
  apply le_antisymm
  · exact Submodule.map_mono le_top
  · rw [Submodule.map_le_iff_le_comap]
    intro lam _
    rw [Submodule.mem_comap]
    set c : SuTwo := coarseRestrictSiteCovariantU sepU witnessEll lam witnessY with hc
    set k : PeriodicLatticeSite witnessL → SuTwo := fun x => RMap (sepGamma x) c with hk
    refine ⟨lam - k, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_kernelSubspaceCovU]
      intro lvl hlvl y hy
      simp only [sepLevels, List.mem_singleton] at hlvl
      subst hlvl
      simp only [Finset.mem_singleton] at hy
      subst hy
      rw [coarseRestrictSiteCovariantU_sub, hk, coarseRestrictSiteCovariantU_zeroMode, ← hc,
        sub_self]
    · have hkzero : siteLaplacianCovLM sepU k = 0 := by
        rw [hk]
        exact siteLaplacianCovLM_pureGaugeZeroMode sepGamma c
      rw [map_sub, hkzero, sub_zero]

/-- **The FLAT image is the same full range** — via the inverted zero-mode map. -/
theorem deltaKernelImageCov_sepU_eq_top_image :
    CovariantHjMinimizer.deltaKernelImageCov sepU sepLevels =
      Submodule.map (siteLaplacianCovLM sepU) ⊤ := by
  apply le_antisymm
  · exact Submodule.map_mono le_top
  · rw [Submodule.map_le_iff_le_comap]
    intro lam _
    rw [Submodule.mem_comap]
    set b : SuTwo := coarseRestrictSiteCovariant witnessEll lam witnessY with hb
    set k : PeriodicLatticeSite witnessL → SuTwo :=
      fun x => RMap (sepGamma x) ((6 : ℝ)⁻¹ • ((7 : ℝ) • b - RMap witnessMElem b)) with hk
    refine ⟨lam - k, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_kernelSubspaceCov]
      intro lvl hlvl y hy
      simp only [sepLevels, List.mem_singleton] at hlvl
      subst hlvl
      simp only [Finset.mem_singleton] at hy
      subst hy
      rw [coarseRestrictSiteCovariant_sub, hk, coarseRestrictSiteCovariant_zeroMode, ← hb,
        sub_self]
    · have hkzero : siteLaplacianCovLM sepU k = 0 := by
        rw [hk]
        exact siteLaplacianCovLM_pureGaugeZeroMode sepGamma _
      rw [map_sub, hkzero, sub_zero]

/-- **THE NEGATIVE RESULT.** The two `Δ`-images COINCIDE, even though the two kernels are
incomparable (§6). So `R(U)` cannot see the kernel separation at `sepLevels`: exhibiting a consequence
for `R(U)` needs a level structure imposing more constraints than `Δ₀^{cov}` has zero modes, and this
file does not supply one. Disclosed here, proved, rather than left to be discovered downstream. -/
theorem deltaKernelImage_sepU_coincide :
    deltaKernelImageCovU sepU sepLevels = CovariantHjMinimizer.deltaKernelImageCov sepU sepLevels := by
  rw [deltaKernelImageCovU_sepU_eq_top_image, deltaKernelImageCov_sepU_eq_top_image]

#print axioms deltaKernelImageCovU_sepU_eq_top_image
#print axioms deltaKernelImageCov_sepU_eq_top_image
#print axioms deltaKernelImage_sepU_coincide
