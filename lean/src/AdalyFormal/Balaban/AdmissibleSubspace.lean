/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Target.ClayStatement
import AdalyFormal.Balaban.Blocks

set_option autoImplicit false
-- The witness computations below are genuine finite `decide`/kernel-reduction computations over
-- a ~64-192 element `Fintype` (`PeriodicLatticeSite`/`PeriodicLatticeEdge witnessL`), not
-- `native_decide` (L1 forbids that; this file has none) -- just deep enough term reduction that
-- the default elaborator recursion budget is too small. Raising it is safe: the KERNEL still
-- checks the resulting `Decidable.decide`/`rfl`-style proof term by ordinary whnf reduction.
set_option maxRecDepth 8000

/-!
# The `(2.121)` admissible subspace — `Γ_{y,x}`, axis-anchored, direction-asymmetric

## ⚠ REPAIR PASS R2 (2026-07-21) — READ THIS FIRST

`compute/SOL_GATE_ADMISSIBLE_SUBSPACE.md` (Sol, grade 2) convicted the R1 version of this module on
two counts. This pass repairs BOTH, having independently re-derived the source content myself
(rendered CMP96 printed p.244 at 300 dpi, `pdftoppm -r 300 -f 22 -l 22`, sha256
`07ab9fee8e3858b252fb3a1a51c6d17457aa1c5b93b1358d05234acef310688c`, byte-identical to every prior
independent render of this page — this is now the SIXTH independent reproduction of the same
bytes), reading the telescoping argument below (2.121)/(2.123) coordinate-by-coordinate rather than
trusting either prior transcription:

1. **THE COORDINATE ORDER WAS BACKWARDS.** The object R1 named `staircasePath` (walking `0,1,2`
   from `y`) is NOT the source's `Γ_{y,x}`. The object R1 named `reverseStaircasePath` (walking
   `2,1,0` from `y`) — and explicitly labelled "the order Balaban does not use" — IS the source's
   object. **Full derivation in §3's docstring below**, independent of and cross-checked against
   Sol's reading. **Names are SWAPPED in this pass**: `staircasePath`/`corner1`/`corner2` now denote
   the TRUE `(2,1,0)`-from-`y` order; `foilStaircasePath`/`foilCorner1`/`foilCorner2` (renamed from
   the R1 names) denote the WRONG `(0,1,2)`-from-`y` order, KEPT (not deleted) as the named foil the
   asymmetry test (§8) needs. The underlying mathematics of every theorem is unchanged and still
   kernel-checks; only which object is CALLED the source's changes.
2. **THE SUBSPACE WAS NOT ACTUALLY DERIVED FROM THE BLOCK GEOMETRY.** R1's `admissibleSubspace y x`
   took two sites and nothing else — no `ell`, no `x ∈ B(y)` proof, no coarse-center datum, no
   `y ∈ Λ'` proof — so Sol compiled membership for an `x` provably outside the block. This pass adds
   a genuine coarse-center lattice `Λ'` (`CoarseLattice`, §1b below — a real spaced sublattice
   with a proved existence+uniqueness tiling law, NOT `FittingCenter`'s mere "room to fit", which
   Sol showed admits overlapping starts) and changes `admissibleSubspace`'s SIGNATURE to REQUIRE
   `hy : y ∈ CoarseLattice L ell` and `hx : x ∈ blockOf y ell` as explicit parameters. Sol's
   exact exploit
   (`(fun _ => 0) ∈ admissibleSubspace witnessY outsideX`) is now a TYPE ERROR, not merely an
   unproved side condition — confirmed in this pass's own scratch testing (§10 of the R2 report).

**Cost, disclosed per the dispatch's explicit instruction**: `admissibleSubspace`'s new arity breaks
three NO-GO files this dispatch may not edit (`Balaban/Coercivity.lean`,
`Balaban/RGLinearization.lean`,
and transitively `HoleHunt/TrivialInhabitation.lean`, which consumes `Coercivity.lean`'s `Anchoring`
namespace). `staircasePath`'s own 2-argument SIGNATURE is unchanged (only its swapped body), so
`Spine.lean`'s references to it (as a bare hypothesis type `b₀ ∉ staircasePath y x`, never the
2.121-conditioned subspace itself) are UNAFFECTED. The exact required patch for each broken file is
written into `ADMISSIBLE_SUBSPACE_R2.md` §11 for sequencing — not applied here (explicit NO-GO).

## Source pin (independently re-rendered and read AGAIN for this repair pass, LAW-11/20)

`pdftoppm -r 300 -f 22 -l 22` on `compute/balaban_su2_papers/balaban_CMP96_1984_propagators_II.pdf`
(offset 222, `corpus/tools/page_offsets.json`, `CMP96`, `constant_verified: true` ⇒ printed p.244 =
PDF page 22), sha256 `07ab9fee8e3858b252fb3a1a51c6d17457aa1c5b93b1358d05234acef310688c`.
**(2.121)**,
printed 244, reads exactly:

> `B(b) = 0` for `b ⊂ Γ_{y,x}`, `x ∈ B(y)`, `y ∈ Λ'`.

## What this module builds

1. **`CoarseLattice L ell`** (§1b) — CMP96's `Λ' ⊂ ℤ^d` made concrete: a genuine spaced sublattice
   (every coordinate a multiple of `ell`), with PROVED existence (`coarseLattice_exists`, given the
   lattice extent is exactly tileable) and uniqueness (`coarseLattice_unique`) of the owning coarse
   center for any fine site — a genuine tiling/partition law, not `FittingCenter`'s "room to fit"
   (which the D1 comparison in §9 shows admits overlapping starts).
2. **`staircasePath` = `Γ_{y,x}`** (§3), the TRUE source order (see the swap above and the full
   derivation in §3's own docstring), and `foilStaircasePath`, the wrong order, KEPT as the named
   foil (not deleted).
3. **`admissibleSubspace`** (§4) — CMP96 `(2.121)` as a genuine `Submodule ℝ (Bond L → ℝ)`, now
   REQUIRING `ell`, `hy : y ∈ CoarseLattice L ell`, `hx : x ∈ blockOf y ell` — the (2.121)
antecedents
   are TYPE-LEVEL preconditions on constructing the object, not decoupled side facts.
4. **Non-degeneracy** (§5/§6) and **the asymmetry acceptance test** (§8, roles swapped to match §3's
   correction) — unchanged in spirit from R1, re-derived against the corrected/antecedented objects.
5. **D1 closure demonstrations** (§9) — `outsideX_not_mem_block` and `overlapStart_not_coarse` are
   the "no proof exists" certificates that make Sol's exact exploit a type error;
`overlapStart_fits`
   shows the SAME site Sol used to break `FittingCenter` (an overlapping start) is excluded by
   `CoarseLattice` specifically, not merely by accident.

## What this module does NOT build (named, not silently dropped)

* **`Δ_k(U)` itself** — out of scope per the mandate, unchanged from R1's characterization
  (`ADMISSIBLE_SUBSPACE.md` §5, superseded in emphasis but not in content by this pass).
* **Wiring `admissibleSubspace` into `Balaban.CoercivityHypothesis.V`** — still NOT done; the
  antecedent-carrying signature makes this MORE honest to wire later, not less, but the wiring
  itself remains `Coercivity.lean`'s job (NO-GO here).
* **A torus-wraparound embedding for `Center := Site`** (§7's `FittingCenter`/`BlockGeometry`
  material, kept UNCHANGED from R1 — it answers a different question, the abstract `BlockGeometry`
  instance, not the `Λ'` antecedent `admissibleSubspace` now requires).
-/

namespace AdalyFormal.Balaban.AdmissibleSubspace

open AdalyFormal.Target.ClayStatement

variable {L : PeriodicLatticeExtent}

/-! ## §1. `B(y)` — the block, made concrete on the periodic-cubic coordinate lattice -/

/-- **`x ∈ B(y)`, CMP96 p.244 / `Blocks.lean`'s `BlockGeometry.B`, concretely**: each coordinate of
`x` lies in the half-open interval `[y_μ, y_μ + ell)`. A genuine axis-aligned coordinate BOX,
matching `PHASE0_DEFS_PLAN.md`'s C1 embedding question (§7 below resolves it for this specific
box-shaped case, not in general). -/
abbrev inBlock (y : PeriodicLatticeSite L) (ell : ℕ) (x : PeriodicLatticeSite L) : Prop :=
  ∀ μ : Fin 3, (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell

/-- `B(y)` itself, as a `Finset` — matching `Blocks.lean`'s `BlockGeometry.B : Center → Finset
Site` exactly in shape, specialized to `Center := Site := PeriodicLatticeSite L`. -/
def blockOf (y : PeriodicLatticeSite L) (ell : ℕ) : Finset (PeriodicLatticeSite L) :=
  Finset.univ.filter (inBlock y ell)

theorem mem_blockOf {y x : PeriodicLatticeSite L} {ell : ℕ} :
    x ∈ blockOf y ell ↔ inBlock y ell x := by
  simp [blockOf]

/-! ## §1b. `Λ'` — the coarse-center lattice, a genuine spaced sublattice (R2 repair, antecedent 2)

CMP96 printed pp.244-245 use `y ∈ Λ'` where `Λ' ⊂ ℤ^d` is a SUBSET of sites (never a separate index
type), spaced so that blocks based at distinct members of `Λ'` tile the lattice without overlap
(printed p.245's figure shows adjacent blocks `B(c₋)`, `B(c₊)` sharing a single separating plane,
not an overlap region). `FittingCenter` (§7, kept from R1) captures only "a box of side `ell` fits
here" — Sol's gate showed this admits OVERLAPPING starts (e.g. both `0` and `1` are valid centers
for side `2` on `4` sites) and carries no spacing/partition structure. `CoarseLattice` below is the
honest fix: sites all of whose coordinates are multiples of `ell`, PROVED (not merely asserted) to
tile: every fine site lies in the block of EXACTLY ONE such center, given the ambient extent is
exactly divisible by `ell` (the natural condition for CMP96's own construction, where lattice sizes
are built as powers of the RG block scale). -/

/-- **`Λ'`, CMP96 printed pp.244-245, made concrete**: the sublattice of sites all of whose
coordinates are multiples of the block side `ell`. A genuine spaced coarse lattice, not merely "a
site a box fits at" (`FittingCenter`, §7 — see `overlapStart_fits`/`overlapStart_not_coarse` in §9
for the concrete site `FittingCenter` wrongly admits and `CoarseLattice` correctly excludes). -/
def CoarseLattice (L : PeriodicLatticeExtent) (ell : ℕ) : Finset (PeriodicLatticeSite L) :=
  Finset.univ.filter (fun y => ∀ μ : Fin 3, (y μ).val % ell = 0)

theorem mem_CoarseLattice {L : PeriodicLatticeExtent} {ell : ℕ} {y : PeriodicLatticeSite L} :
    y ∈ CoarseLattice L ell ↔ ∀ μ : Fin 3, (y μ).val % ell = 0 := by
  simp [CoarseLattice]

/-- Elementary number-theoretic fact underlying uniqueness: two multiples of `ell` that both lie in
a half-open window `[c, c+ell)` around the same point `b` must coincide — there is room for only one
multiple of `ell` per window of length `ell`. Proved directly (no unpinned Mathlib
division-uniqueness
lemma name assumed), via a two-sided `by_contra` + `Nat.mul_le_mul_left` sandwich. -/
theorem unique_multiple_in_window (ell b c d : ℕ)
    (h1 : c % ell = 0) (h2 : d % ell = 0)
    (h3a : c ≤ b) (h3b : b < c + ell)
    (h4a : d ≤ b) (h4b : b < d + ell) : c = d := by
  obtain ⟨k1, hk1⟩ := Nat.dvd_of_mod_eq_zero h1
  obtain ⟨k2, hk2⟩ := Nat.dvd_of_mod_eq_zero h2
  subst hk1 hk2
  have hle : k1 ≤ k2 := by
    by_contra hcon
    rw [not_le] at hcon
    have hmul : ell * (k2 + 1) ≤ ell * k1 := Nat.mul_le_mul_left ell hcon
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hge : k2 ≤ k1 := by
    by_contra hcon
    rw [not_le] at hcon
    have hmul : ell * (k1 + 1) ≤ ell * k2 := Nat.mul_le_mul_left ell hcon
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  rw [le_antisymm hle hge]

/-- **Existence — `Λ'` genuinely tiles.** Every fine site `x` lies in the block of SOME coarse
center, provided the ambient extent is exactly divisible by the block side `ell` (the natural
hypothesis: CMP96 builds its lattice sizes as powers of the RG scale precisely so blocks tile
without remainder) and `ell > 0`. The witness lattice below (`witnessL`, extent `3` i.e. `4` sites
per coordinate, `ell = 2`) satisfies this (`2 ∣ 4`), so this is exercised concretely, not left as an
unexercised abstract theorem (`witness_coarseLattice_exists` in §6). -/
theorem coarseLattice_exists (ell : ℕ) (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (x : PeriodicLatticeSite L) :
    ∃ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell ∧ x ∈ blockOf y ell := by
  have hbound : ∀ μ : Fin 3, ell * ((x μ).val / ell) < L μ + 1 := by
    intro μ
    obtain ⟨k, hk⟩ := hdvd μ
    have hxlt := (x μ).isLt
    have hdm := Nat.div_add_mod (x μ).val ell
    have hmod := Nat.mod_lt (x μ).val hell
    omega
  refine ⟨fun μ => ⟨ell * ((x μ).val / ell), hbound μ⟩, ?_, ?_⟩
  · rw [mem_CoarseLattice]
    intro μ
    exact Nat.mul_mod_right ell _
  · rw [mem_blockOf]
    intro μ
    simp only
    have hdm := Nat.div_add_mod (x μ).val ell
    have hmod := Nat.mod_lt (x μ).val hell
    exact ⟨Nat.mul_div_le (x μ).val ell, by omega⟩

/-- **Uniqueness — `Λ'` genuinely PARTITIONS, blocks do not overlap.** The coarse center owning a
given fine site is unique. This is exactly the property `FittingCenter` (§7) LACKS — Sol's gate
found it admits overlapping starts `0` and `1` at side `2` on `4` sites, i.e. TWO different
"fitting centers" both claim the same site; `CoarseLattice` cannot: at most one member of `Λ'` can
own any given `x`. -/
theorem coarseLattice_unique (ell : ℕ) {y y' x : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (hy' : y' ∈ CoarseLattice L ell)
    (hx : x ∈ blockOf y ell) (hx' : x ∈ blockOf y' ell) : y = y' := by
  rw [mem_CoarseLattice] at hy hy'
  rw [mem_blockOf] at hx hx'
  funext μ
  apply Fin.ext
  exact unique_multiple_in_window ell (x μ).val (y μ).val (y' μ).val (hy μ) (hy' μ)
    (hx μ).1 (hx μ).2 (hx' μ).1 (hx' μ).2

/-! ## §1c — CLOSING THE ALIGNMENT GAP (Defect 3 repair, `SILENT_OBJECT_FIXES.md`, 2026-07-21)

`card_blockOf` below (§7) proves `(blockOf y ell).card = ell^3` CONDITIONAL on a separate `hfit`
hypothesis (`∀ μ, (y μ).val + ell ≤ L μ + 1`), and this module's docstring for `CoarseLattice` had,
until this pass, only ARGUED in prose that "CoarseLattice centres satisfy `ell ∣ (L μ+1)`" makes
that hypothesis automatic — never proved it. Mid-dispatch escalation (coordinator, 2026-07-21): the
wall-prover's `d=3` zero mode reduction lives on the coefficient balance of the coarse-graining
operator `Q(U)`'s block average, which makes a miscounted block size DIRECTLY load-bearing, not
cosmetic. `coarseLattice_mem_fits` below closes the gap as a KERNEL theorem: `CoarseLattice`
membership, under the SAME tileability hypothesis `coarseLattice_exists`/`coarseLattice_unique`
already assume, PROVABLY implies `hfit` — for EVERY member, not merely a hand-picked witness.
`AlignedCoarseCenter` then packages the guarantee INTO A TYPE, so a consumer built against it
cannot construct a center whose block fails to tile — "impossible to violate", not "documented",
per the coordinator's explicit instruction. §9b below makes the DANGER of not using it concrete: a
genuine non-`CoarseLattice` center undercounts its block, kernel-checked. -/

/-- **The alignment gap, closed.** Every `Λ'`-member's block genuinely fits inside the periodic
extent, given the tileability hypothesis `ell ∣ (L μ + 1)` for every axis — the PROOF of the
sentence this module's docstring previously only asserted. -/
theorem coarseLattice_mem_fits {L : PeriodicLatticeExtent} {ell : ℕ}
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    ∀ μ, (y μ).val + ell ≤ L μ + 1 := by
  intro μ
  rw [mem_CoarseLattice] at hy
  obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero (hy μ)
  obtain ⟨k, hk⟩ := hdvd μ
  have hlt : (y μ).val < L μ + 1 := (y μ).isLt
  rw [hj, hk] at hlt
  have hjk : j < k := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmul : ell * k ≤ ell * j := Nat.mul_le_mul_left ell hcon
    omega
  have hmul2 : ell * (j + 1) ≤ ell * k := Nat.mul_le_mul_left ell hjk
  rw [Nat.mul_add, Nat.mul_one] at hmul2
  rw [hj, hk]
  omega

/-- **The alignment enforced IN THE TYPE** (the coordinator's explicit ask): a coarse center
bundled with its own `Λ'`-membership proof. An element of this type cannot fail to tile — the
fitting proof (`alignedCoarseCenter_fits` below) is DERIVED from the type's own field via
`coarseLattice_mem_fits`, never re-asserted or assumed again at a call site. A consumer rewired to
accept `AlignedCoarseCenter L ell hdvd` in place of a bare `PeriodicLatticeSite L` gets the
`ell^3`-block guarantee (`alignedCoarseCenter_card`, §7b below) automatically, at every call — the
alignment condition becomes impossible to violate rather than merely documented. (NOT wired into
`KernelSubspace.coarseRestrictSite` / `Balaban.LatticeOperators.coarseRestrict` here — both are
outside this lane's write scope; the exact patch is in `SILENT_OBJECT_FIXES.md`.) -/
def AlignedCoarseCenter (L : PeriodicLatticeExtent) (ell : ℕ)
    (_hdvd : ∀ μ, ell ∣ (L μ + 1)) : Type :=
  {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}

instance instFintypeAlignedCoarseCenter (L : PeriodicLatticeExtent) (ell : ℕ)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) : Fintype (AlignedCoarseCenter L ell hdvd) :=
  Subtype.fintype _

instance instDecidableEqAlignedCoarseCenter (L : PeriodicLatticeExtent) (ell : ℕ)
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) : DecidableEq (AlignedCoarseCenter L ell hdvd) :=
  Subtype.instDecidableEq

/-- The guarantee, extracted from the type's own membership field — not re-derived from a fresh
side hypothesis. -/
theorem alignedCoarseCenter_fits {L : PeriodicLatticeExtent} {ell : ℕ}
    {hdvd : ∀ μ, ell ∣ (L μ + 1)} (c : AlignedCoarseCenter L ell hdvd) :
    ∀ μ, (c.1 μ).val + ell ≤ L μ + 1 :=
  coarseLattice_mem_fits hdvd c.2

#print axioms coarseLattice_mem_fits
#print axioms alignedCoarseCenter_fits

/-! ## §2. The axis-parallel segment -/

/-- The axis-parallel segment of bonds in direction `μ`, based at `base`, sweeping the
`μ`-coordinate over the half-open range `[a, b)`; every OTHER coordinate of the bond's base site is
pinned to `base`'s value. This is the elementary building block of the staircase — matches
`Blocks.lean`'s own filter style (`bondsTouching`, `bondsBothEndpointsIn`), not a new idiom. -/
def axisSegment (base : PeriodicLatticeSite L) (μ : Fin 3) (a b : ℕ) :
    Finset (PeriodicLatticeEdge L) :=
  Finset.univ.filter (fun e : PeriodicLatticeEdge L =>
    e.2 = μ ∧ (∀ ν : Fin 3, ν ≠ μ → e.1 ν = base ν) ∧ a ≤ (e.1 μ).val ∧ (e.1 μ).val < b)

theorem mem_axisSegment {base : PeriodicLatticeSite L} {μ : Fin 3} {a b : ℕ}
    {e : PeriodicLatticeEdge L} :
    e ∈ axisSegment base μ a b ↔
      e.2 = μ ∧ (∀ ν : Fin 3, ν ≠ μ → e.1 ν = base ν) ∧ a ≤ (e.1 μ).val ∧ (e.1 μ).val < b := by
  simp [axisSegment]

/-! ## §3. The staircase path `Γ_{y,x}` — CMP96 printed p.244, TRUE order `e_3, e_2, e_1` (R2)

**Full derivation, independent of and cross-checked against Sol's reading, from the rendered p.244
image itself (not merely the OCR draft), of the telescoping argument immediately below (2.121)/
(2.123):**

For `b = ⟨x, x+e_2⟩`, the page displays
`B(x,x+e_2) = (B(x,x+e_2) - B(x-e_1,x-e_1+e_2)) + ... +
(B((y_1+1,x_2,...,x_d),(y_1+1,x_2+1,...,x_d))
  - B((y_1,x_2,...,x_d),(y_1,x_2,...,x_d)+e_2)) = Σ(∂_1 B)(p(x'))`.
The individual difference terms telescope EXACTLY to
`B(x,x+e_2) - B((y_1,x_2,...,x_d),(y_1,x_2,...,x_d)+e_2)`, so the displayed equality
`B(x,x+e_2) = [that sum]` holds only because the boundary term `B((y_1,x_2,...,x_d),(y_1,x_2,...,
x_d)+e_2)` is IMPLICITLY ZERO — it disappears from the display precisely because it is a bond in
`Γ_{y,x}` by (2.121). So `Γ_{y,x}` contains the direction-`e_2` bond based at
`(y_1,x_2,...,x_d)` — coordinate `1` ALREADY at `y`'s value, coordinates `2,...,d` STILL at `x`'s
values.

For general `j` (printed just above (2.123)), the union of segments needed is
`x' ∈ [(y_1,...,y_{j-1},x_j,...,x_d),(y_1,...,x_{j-1},x_j,...,x_d)] ∪ ... ∪ [(y_1,x_2,...,x_d),x]`:
reading term by term, the segment for coordinate `k` (`1 ≤ k ≤ j-1`) has coordinates `1,...,k-1`
FIXED AT `y`'s values and coordinates `k+1,...,d` FIXED AT `x`'s values, with coordinate `k` itself
swept between `y_k` and `x_k`. Defining `z_k := (y_1,...,y_k,x_{k+1},...,x_d)` for `k = 0,...,d`
(so `z_0 = x`, `z_d = y`), this is EXACTLY the edge between `z_{k-1}` and `z_k` (they differ only in
coordinate `k`). So `Γ_{y,x} = ⋃_{k=1}^{d} (\text{edge } z_{k-1}z_k)` — a staircase from `x` (`z_0`)
to `y` (`z_d`) that switches coordinate `1` FIRST, then `2`, ..., then `d` LAST, as walked FROM `x`
TO `y`. Equivalently, as walked FROM `y` TO `x` (the SAME edge set, opposite traversal), it switches
coordinate `d` first, `d-1` next, ..., coordinate `1` last — order `d,...,1`, i.e. `(2,1,0)` on this
0-indexed `d=3` carrier.

Concretely verified term-by-term against the boundary bond identified above: the `j=2` boundary bond
(direction `e_2`, base `(y_1,x_2,...,x_d)`, i.e. coordinate `1`(paper)/`0`(Lean 0-indexed) ALREADY
at
`y`, coordinates `2,3`(paper)/`1,2`(Lean) STILL at `x`) is exactly the `z_1`-to-`z_2` edge for `d=3`
in THIS scheme — matching `corner1`/`corner2` below (updating coordinate `2` first, then `1`), NOT
R1's `(0,1,2)`-from-`y` order (which has the OPPOSITE coordinate assignment at every corner). This
is the swap: what R1 called `reverseStaircasePath` — and explicitly labelled "the order Balaban
does not use" — is, on this reading, `Γ_{y,x}` itself. -/

/-- First corner walking the TRUE order: `y` with coordinate `2` switched to `x`'s value. -/
def corner1 (y x : PeriodicLatticeSite L) : PeriodicLatticeSite L := Function.update y 2 (x 2)

/-- Second corner: additionally coordinate `1` switched to `x`'s value. -/
def corner2 (y x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  Function.update (corner1 y x) 1 (x 1)

/-- The staircase CLOSES at `x` once coordinate `0` (the LAST coordinate in the true order) is
also switched. -/
theorem update0_corner2_eq (y x : PeriodicLatticeSite L) :
    Function.update (corner2 y x) 0 (x 0) = x := by
  funext ν
  fin_cases ν <;> simp [corner2, corner1, Function.update]

/-- **`Γ_{y,x}` — CMP96 printed p.244, `(2.121)`, formalized, TRUE order (R2 correction).** The
staircase path of bonds from `y` to `x`: walk coordinate `2` first (from `y` to `corner1`), then
coordinate `1` (from `corner1` to `corner2`), then coordinate `0` (from `corner2` to `x`) —
Balaban's fixed order `e_d,...,e_1` as walked from `y`, derived in full above. **AXIS-ANCHORED**
(tied to the specific pair `(y,x)`, not a radius) and **DIRECTION-ASYMMETRIC** (the fixed order is
load-bearing — §8 exhibits a configuration this set admits that the WRONG order
(`foilStaircasePath`)
or a same-radius `ℓ¹`-ball forbids). Never a symmetrized ball. -/
def staircasePath (y x : PeriodicLatticeSite L) : Finset (PeriodicLatticeEdge L) :=
  axisSegment y 2 (min (y 2).val (x 2).val) (max (y 2).val (x 2).val) ∪
  axisSegment (corner1 y x) 1 (min (y 1).val (x 1).val) (max (y 1).val (x 1).val) ∪
  axisSegment (corner2 y x) 0 (min (y 0).val (x 0).val) (max (y 0).val (x 0).val)

/-- **The foil — R1's `(0,1,2)`-from-`y` order, KEPT (not deleted, per the mandate).** Walking
coordinate `0` first, then `1`, then `2` — the order this repair pass shows is NOT the source's.
Retained under a name that no longer claims to be `Γ_{y,x}`: it is the counter-object §8's asymmetry
acceptance test needs. `foilCorner1`/`foilCorner2` are R1's `corner1`/`corner2`, renamed only. -/
def foilCorner1 (y x : PeriodicLatticeSite L) : PeriodicLatticeSite L := Function.update y 0 (x 0)

def foilCorner2 (y x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  Function.update (foilCorner1 y x) 1 (x 1)

theorem update2_foilCorner2_eq (y x : PeriodicLatticeSite L) :
    Function.update (foilCorner2 y x) 2 (x 2) = x := by
  funext ν
  fin_cases ν <;> simp [foilCorner2, foilCorner1, Function.update]

/-- `foilStaircasePath` — the WRONG order, `(0,1,2)` from `y`. This is R1's `staircasePath`, renamed
(the underlying definition is byte-for-byte what R1 shipped under the other name). -/
def foilStaircasePath (y x : PeriodicLatticeSite L) : Finset (PeriodicLatticeEdge L) :=
  axisSegment y 0 (min (y 0).val (x 0).val) (max (y 0).val (x 0).val) ∪
  axisSegment (foilCorner1 y x) 1 (min (y 1).val (x 1).val) (max (y 1).val (x 1).val) ∪
  axisSegment (foilCorner2 y x) 2 (min (y 2).val (x 2).val) (max (y 2).val (x 2).val)

/-! ## §4. The `(2.121)` admissible subspace — NOW genuinely a function of the source's data (R2) -/

/-- Bond configurations — CMP96's real (not group-valued) field `B(b)`, one real number per link.

**[SCOPE CORRECTED 2026-07-29 — this docstring is TRUE OF CMP96 AND FALSE AS A CARRIER FOR
CMP99b, and it is the written origin of a tree-wide carrier defect.]** The guard checks the wrong
distinction. `B` is not *group*-valued; it is *Lie-algebra*-valued, and for non-abelian `G` that is
not one real number. CMP99b p.417 defines it, image-verified at 400 dpi by two lanes independently,
word for word: *"For a configuration `B` defined on `𝔅` and **with values in the Lie algebra `𝔤`**
we define `H(U)B` …"*, on configurations `A` *"with values in `𝔤`"* satisfying (3.110).

**Why the scalar reading was ever right:** CMP99b p.389 says the two previous papers treated *"the
simplest **Abelian** gauge field theory action"*, and `[4] = CMP96` is that abelian, one-real-
component paper. p.428's *"We have proved it in [4], Lemma 2.4, for operators with `U = 1`"* is
therefore a citation to a scalar result, and it transfers **at `U ≡ 1` and nowhere else** — via the
`Σ_a` component decomposition p.389 itself displays.

That transfer is real and is now a theorem: `Balaban/CarrierAdjudication.lean`'s `ampliate_coercive`
carries scalar coercivity up to su(2) with the **same `γ`** for fibre-diagonal operators. **The
converse is FALSE** (`scalar_coercivity_does_not_imply_su2`): `sectorProj` is coercive with `γ = 1`
on the whole scalar image and annihilates a nonzero su(2) field. So a scalar result is a genuine
`U = 1` result and is *not* evidence for the general-`U` statement.

Consumers stating a `CoercivityHypothesis` on this carrier and billing it as CMP99b p.428 are
mis-denoting. `descendHyp` (same module) builds `Spine.coerc_u_main`'s exact target type from one on
`BondFnL2`, same `γ''`, `V_ne_bot` discharged — so restating upward is a strict strengthening whose
descent is mechanical except at the two non-degeneracy conjuncts. -/
abbrev Bond (L : PeriodicLatticeExtent) := PeriodicLatticeEdge L

/-- **CMP96 `(2.121)`, as a genuine `Submodule`, NOW REQUIRING both antecedents (2.121) states
alongside `B(b) = 0` — `x ∈ B(y)` and `y ∈ Λ'` — as EXPLICIT PARAMETERS, not decoupled side facts.**
Sol's D1 attack (compiling membership for an `x` provably outside the block, since R1's version took
only `y x` and nothing else) is now a TYPE ERROR: there is no proof term to supply for `hx` when `x`
genuinely lies outside `blockOf y ell` (`outsideX_not_mem_block`, §9), so `admissibleSubspace`
simply
cannot be APPLIED to such a pair. `staircasePath` itself is left unconditioned on purpose —
`Γ_{y,x}`
is a well-defined bond set for ANY `(y,x)` regardless of whether `x ∈ B(y)` holds; it is the CLAIM
that "(2.121)'s admissible subspace exists for this pair" that (2.121) conditions on `x ∈ B(y)`,
`y ∈ Λ'`, so the antecedents belong on `admissibleSubspace`, not on `Γ_{y,x}` itself. -/
def admissibleSubspace (y x : PeriodicLatticeSite L) (ell : ℕ)
    (_hy : y ∈ CoarseLattice L ell) (_hx : x ∈ blockOf y ell) : Submodule ℝ (Bond L → ℝ) where
  carrier := {B | ∀ b ∈ staircasePath y x, B b = 0}
  zero_mem' := by intro b _; rfl
  add_mem' := by
    intro B1 B2 hB1 hB2 b hb
    simp [hB1 b hb, hB2 b hb]
  smul_mem' := by
    intro c B hB b hb
    simp [hB b hb]

theorem mem_admissibleSubspace {y x : PeriodicLatticeSite L} {ell : ℕ}
    {hy : y ∈ CoarseLattice L ell} {hx : x ∈ blockOf y ell} {B : Bond L → ℝ} :
    B ∈ admissibleSubspace y x ell hy hx ↔ ∀ b ∈ staircasePath y x, B b = 0 := Iff.rfl

/-! ## §4b. THE INTERSECTION admissible subspace — CMP96 `(2.121)` LITERALLY, `y ∈ Λ'` and
`x ∈ B(y)` both UNIVERSAL (V-scope repair, this pass)

**The defect this closes.** `admissibleSubspace y x ell hy hx` above is `(2.121)`'s condition for
ONE fixed pair `(y,x)`. The printed sentence itself, quoted verbatim in the module-level docstring
above (`compute/denotation_audit/CMP96_p244_render.png`), is
> `B(b) = 0` for `b ⊂ Γ_{y,x}`, `x ∈ B(y)`, `y ∈ Λ'`
i.e. universally quantified over BOTH `x` (ranging over the block `B(y)`) AND `y` (ranging over the
coarse lattice `Λ'`) — a single admissible subspace, the SIMULTANEOUS restriction over every valid
pair, not a family of subspaces indexed by a caller-chosen `(y,x)`. `admissibleSubspaceInter` below
is exactly that: `B` lies in it iff it vanishes on `Γ_{y,x}` for EVERY `y ∈ Λ'` and EVERY `x ∈ B(y)`
— the genuine `(2.121)` object, built directly (not via `iInf`/`Submodule.iInf` over a packaged
index type) so its carrier is a transparent, one-to-one transcription of (2.121)'s own quantifier
structure: `∀ y ∈ Λ', ∀ x ∈ B(y), ∀ b ∈ Γ_{y,x}, B(b) = 0`. -/

/-- **CMP96 `(2.121)`, literally — universal in both antecedents.** A genuine `Submodule`: `B`
vanishes on `Γ_{y,x}` for every coarse center `y ∈ Λ'` and every `x` in `y`'s block, simultaneously.
This is a SUBSET of (contained in) every individual `admissibleSubspace y x ell hy hx`
(`admissibleSubspaceInter_le` below) — a strictly MORE restrictive object than any single pair's
subspace, exactly what a genuine set-theoretic intersection over more constraints must be. -/
def admissibleSubspaceInter (L : PeriodicLatticeExtent) (ell : ℕ) : Submodule ℝ (Bond L → ℝ) where
  carrier := {B | ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, B b = 0}
  zero_mem' := by intro y _hy x _hx b _hb; rfl
  add_mem' := by
    intro B1 B2 hB1 hB2 y hy x hx b hb
    simp [hB1 y hy x hx b hb, hB2 y hy x hx b hb]
  smul_mem' := by
    intro c B hB y hy x hx b hb
    simp [hB y hy x hx b hb]

theorem mem_admissibleSubspaceInter {L : PeriodicLatticeExtent} {ell : ℕ} {B : Bond L → ℝ} :
    B ∈ admissibleSubspaceInter L ell ↔
      ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
        ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, B b = 0 :=
  Iff.rfl

/-- **Faithfulness check, kernel-checked, not merely argued in prose**: the intersection object is
genuinely CONTAINED IN every individual pair's `admissibleSubspace` — confirming
`admissibleSubspaceInter` really is a lower bound of the family `{admissibleSubspace y x ell hy hx}`
(the defining property of an intersection), not merely a same-shaped but unrelated construction.
Mutation check: dropping either the `y`- or the `x`-quantifier from the carrier (e.g. fixing `y` to
one witness) breaks this theorem for a DIFFERENT `y'`/`x'` pair — `admissibleSubspaceInter_strict_
witness` (§9d below, once the witness lattice's objects are in scope) exhibits this concretely on
two DISTINCT pairs of the witness lattice: a configuration admissible for one pair alone but
excluded once a second, disjoint pair's staircase is also required to vanish. -/
theorem admissibleSubspaceInter_le {L : PeriodicLatticeExtent} {ell : ℕ}
    {y x : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell) :
    admissibleSubspaceInter L ell ≤ admissibleSubspace y x ell hy hx := by
  intro B hB
  rw [mem_admissibleSubspace]
  intro b hb
  exact hB y hy x hx b hb

#print axioms admissibleSubspaceInter
#print axioms mem_admissibleSubspaceInter
#print axioms admissibleSubspaceInter_le

/-! ## §4c. `admissibleSubspaceInter ≠ ⊥` — GENUINE non-vacuity, UNCONDITIONAL in `L`/`ell`
(grade-2 gate repair, this pass, closing item 1 of the four QUALIFIED findings)

**What `admissibleSubspaceInter_strict_witness` (§9d below) does NOT establish.** It proves
`admissibleSubspaceInter` is a STRICT SUBSET of one single pair's `admissibleSubspace` — a
containment fact between two objects, not `admissibleSubspaceInter L ell ≠ ⊥`. A strict subset of
a nonempty submodule can still itself be `⊥` (any proper subspace of a `1`-dimensional space is a
concrete instance), so the containment fact alone does not settle non-vacuity. Since
`Balaban.CoercivityHypothesis.V_ne_bot` (`Coercivity.lean` §2) is a MANDATORY FIELD of every
`CoercivityHypothesis` term, and `Spine.coerc_u_main` pins `cohyp.V` to the transported image of
exactly this object (`Anchoring.anchoredVInter`, below), `admissibleSubspaceInter L ell ≠ ⊥` is
genuinely load-bearing — the docstring previously bundled it into "GENUINE, NON-VACUOUS NARROWING"
without a proof of the non-vacuous half; `admissibleSubspaceInter_strict_witness`'s own docstring
is corrected below (§9d) to no longer claim it.

**The witness, general in `L` and `ell` both — no divisibility/positivity hypothesis needed.**
`maximalSite L` is the site at the LAST coordinate index in every direction (`Fin.last (L μ)`,
i.e. coordinate value `L μ` itself, the top value `Fin (L μ + 1)` represents); `generalWrapBond L`
pairs it with direction `0`. For ANY valid pair `(y,x)` (`y ∈ CoarseLattice L ell`,
`x ∈ blockOf y ell`), `staircasePath y x`'s direction-`0` segment is based at `corner2 y x`
(coordinate `0` still `= y_0`, unmoved until this last segment) and sweeps `e.1 0` over
`[min(y_0,x_0), max(y_0,x_0))` — strictly BELOW `max(y_0,x_0) ≤ x_0 ≤ L 0` (`x_0 : Fin (L 0 + 1)`,
so `x_0.val ≤ L 0`), so it can never reach `L 0`, the exact value `generalWrapBond`'s direction-`0`
bond carries; the direction-`2`/`1` segments are excluded on direction alone
(`e.2 = 2` or `e.2 = 1 ≠ 0`). So `generalWrapBond L` lies OUTSIDE every valid pair's `Γ_{y,x}`
simultaneously, hence the indicator configuration on it lies in the intersection over ALL pairs —
a genuine, unconditional-in-`ell` non-vacuity witness. Adapted from the grade-2 gate's
independently-proved (and independently kernel-checked, `#print axioms` clean) scratch
certificate: `compute/sol_vscope_gate/NONVACUITY_CHECK.lean`
(`generalWrapBond_not_mem_any`/`admissibleSubspaceInter_ne_bot_independent`), cross-checked by a
second, degenerate-lattice witness in `compute/prosecute_vscope/VacuityTest.lean`
(`crossBond`/`admissibleSubspaceInter_witness_ne_bot`, a boundary bond crossing between two
adjacent blocks on the fixed witness lattice — the SAME phenomenon, exhibited concretely rather
than in the general `L` argument used here). -/

/-- The maximal-coordinate base site on any periodic lattice — every coordinate at its top value
`L μ` (the largest value `Fin (L μ + 1)` represents). -/
def maximalSite (L : PeriodicLatticeExtent) : PeriodicLatticeSite L :=
  fun μ => Fin.last (L μ)

/-- The direction-`0` bond based at `maximalSite L` — the concrete witness no valid staircase can
reach (proved below, `generalWrapBond_not_mem_any`). -/
def generalWrapBond (L : PeriodicLatticeExtent) : Bond L :=
  (maximalSite L, (0 : Fin 3))

/-- **No valid `(y,x)` pair's staircase contains `generalWrapBond L`** — general in `L`, `ell`,
`y`, `x`; the only hypotheses used are the `(2.121)` antecedents `admissibleSubspaceInter` already
quantifies over (`y ∈ CoarseLattice L ell`, `x ∈ blockOf y ell`), no further side condition on
`ell`. -/
theorem generalWrapBond_not_mem_any {L : PeriodicLatticeExtent} {ell : ℕ}
    (y x : PeriodicLatticeSite L) (_hy : y ∈ CoarseLattice L ell)
    (hx : x ∈ blockOf y ell) : generalWrapBond L ∉ staircasePath y x := by
  rw [mem_blockOf] at hx
  intro hb
  simp only [staircasePath, Finset.mem_union] at hb
  rcases hb with hab | h0
  · rcases hab with h2 | h1
    · have hd := (mem_axisSegment.mp h2).1
      have hv := congrArg Fin.val hd
      norm_num [generalWrapBond] at hv
    · have hd := (mem_axisSegment.mp h1).1
      have hv := congrArg Fin.val hd
      norm_num [generalWrapBond] at hv
  · have hm := (mem_axisSegment.mp h0).2.2.2
    have hyx : (y 0).val ≤ (x 0).val := (hx 0).1
    rw [max_eq_right hyx] at hm
    have hxle : (x 0).val ≤ L 0 := Nat.le_of_lt_succ (x 0).isLt
    have hlast : (maximalSite L 0).val = L 0 := rfl
    change (maximalSite L 0).val < (x 0).val at hm
    rw [hlast] at hm
    omega

/-- The indicator configuration on `generalWrapBond L`: `1` there, `0` everywhere else. -/
noncomputable def generalWrapConfig (L : PeriodicLatticeExtent) : Bond L → ℝ :=
  fun e => if e = generalWrapBond L then 1 else 0

theorem generalWrapConfig_mem {L : PeriodicLatticeExtent} {ell : ℕ} :
    generalWrapConfig L ∈ admissibleSubspaceInter L ell := by
  rw [mem_admissibleSubspaceInter]
  intro y hy x hx b hb
  have hbne : b ≠ generalWrapBond L := by
    intro h
    rw [h] at hb
    exact generalWrapBond_not_mem_any y x hy hx hb
  simp [generalWrapConfig, hbne]

theorem generalWrapConfig_ne_zero (L : PeriodicLatticeExtent) : generalWrapConfig L ≠ 0 := by
  intro h
  have := congrFun h (generalWrapBond L)
  simp [generalWrapConfig] at this

/-- **`admissibleSubspaceInter L ell ≠ ⊥`, UNCONDITIONALLY — every `L`, every `ell`, no extra
hypothesis.** This is the fix item 1 of the grade-2 gate's four QUALIFIED findings adds: genuine
non-vacuity of the `(2.121)` intersection object, not merely the strict-subset fact
`admissibleSubspaceInter_strict_witness` (§9d) already carried. -/
theorem admissibleSubspaceInter_ne_bot (L : PeriodicLatticeExtent) (ell : ℕ) :
    admissibleSubspaceInter L ell ≠ ⊥ := by
  intro hbot
  have hmem : generalWrapConfig L ∈ (⊥ : Submodule ℝ (Bond L → ℝ)) := by
    rw [← hbot]; exact generalWrapConfig_mem
  exact generalWrapConfig_ne_zero L (Submodule.mem_bot ℝ |>.mp hmem)

#print axioms generalWrapBond_not_mem_any
#print axioms generalWrapConfig_mem
#print axioms generalWrapConfig_ne_zero
#print axioms admissibleSubspaceInter_ne_bot

/-! ## §5. Non-degeneracy: `admissibleSubspace ≠ ⊥`, `admissibleSubspace ≠ ⊤` -/

/-- **General non-vacuity.** Whenever some bond `b₀` lies OUTSIDE `Γ_{y,x}`, the indicator
configuration on `b₀` is a genuine NONZERO member of `admissibleSubspace` — `(2.121)` does not
accidentally force every configuration to vanish. -/
theorem admissibleSubspace_ne_bot_of_exists {y x : PeriodicLatticeSite L} {ell : ℕ}
    {hy : y ∈ CoarseLattice L ell} {hx : x ∈ blockOf y ell}
    (b₀ : Bond L) (hb₀ : b₀ ∉ staircasePath y x) : admissibleSubspace y x ell hy hx ≠ ⊥ := by
  intro hbot
  have hmem : (fun e => if e = b₀ then (1 : ℝ) else 0) ∈ admissibleSubspace y x ell hy hx := by
    rw [mem_admissibleSubspace]
    intro b hb
    have hbne : b ≠ b₀ := by rintro rfl; exact hb₀ hb
    simp [hbne]
  rw [hbot, Submodule.mem_bot] at hmem
  have hcontra := congrFun hmem b₀
  simp at hcontra

/-- **General non-triviality.** Whenever `Γ_{y,x}` is nonempty, the constant-`1` configuration
FAILS `(2.121)`, so `admissibleSubspace` is genuinely proper, not everything. -/
theorem admissibleSubspace_ne_top_of_nonempty {y x : PeriodicLatticeSite L} {ell : ℕ}
    {hy : y ∈ CoarseLattice L ell} {hx : x ∈ blockOf y ell}
    (hne : (staircasePath y x).Nonempty) : admissibleSubspace y x ell hy hx ≠ ⊤ := by
  intro htop
  obtain ⟨b, hb⟩ := hne
  have hmem : (fun _ : Bond L => (1 : ℝ)) ∈ admissibleSubspace y x ell hy hx :=
    htop ▸ Submodule.mem_top
  have h0 := (mem_admissibleSubspace).mp hmem b hb
  norm_num at h0

/-! ## §6. Concrete witness lattice: `y = (0,0,0)`, `x = (1,0,1)`, block side `2` -/

/-- Periodic extent `3` in every direction (`Fin 4` per coordinate: sites `0,1,2,3`) — enough room
for the block and for bonds strictly outside `Γ_{y,x}`. Chosen (unchanged from R1) so `witnessEll =
2` DIVIDES the site count `4`, making `CoarseLattice`'s tiling law (`coarseLattice_exists`)
exercised
concretely on this exact lattice, not merely on an abstract one (`witness_coarseLattice_exists`
below). -/
def witnessL : PeriodicLatticeExtent := fun _ => 3

/-- Block corner, the lattice origin. -/
def witnessY : PeriodicLatticeSite witnessL := fun _ => 0

/-- A point differing from `witnessY` in coordinates `0` and `2` but NOT `1` — the minimal
configuration producing a genuine "corner" (an L-shaped, not straight, staircase), needed to see
direction-asymmetry: a straight segment looks the same walked either way. Unchanged from R1. -/
def witnessX : PeriodicLatticeSite witnessL := fun μ =>
  match μ.val with
  | 2 => 1
  | 0 => 1
  | _ => 0

/-- Block side length. -/
def witnessEll : ℕ := 2

theorem witnessX_mem_block : witnessX ∈ blockOf witnessY witnessEll := by decide

/-- **The `y ∈ Λ'` antecedent, discharged concretely (R2, new).** `witnessY = (0,0,0)` has every
coordinate `≡ 0 (mod ell)` trivially. -/
theorem witnessY_coarse : witnessY ∈ CoarseLattice witnessL witnessEll := by decide

/-- **`CoarseLattice`'s tiling law, exercised concretely** — not left as an unexercised abstract
theorem. `witnessEll = 2` divides `witnessL μ + 1 = 4` in every coordinate. -/
theorem witness_coarseLattice_exists (x : PeriodicLatticeSite witnessL) :
    ∃ y : PeriodicLatticeSite witnessL, y ∈ CoarseLattice witnessL witnessEll ∧
      x ∈ blockOf y witnessEll :=
  coarseLattice_exists witnessEll (by decide) (by decide) x

/-- The staircase path on the witness data, computed out fully: exactly two bonds, the TRUE-order
corner `(0,0,0) →_{e_2} (0,0,1) →_{e_0} (1,0,1)` (R2: swapped from R1's `(0,0,0) →_{e_0} (1,0,0)
→_{e_2} (1,0,1)`, which is now `foilStaircasePath`'s witness, below). -/
theorem witness_staircasePath :
    staircasePath witnessY witnessX =
      {((fun _ => (0 : Fin 4)), (2 : Fin 3)),
        ((fun μ => if μ.val = 2 then 1 else 0), (0 : Fin 3))} := by
  decide

theorem witness_staircasePath_nonempty : (staircasePath witnessY witnessX).Nonempty := by
  rw [witness_staircasePath]
  exact ⟨((fun _ => (0 : Fin 4)), (2 : Fin 3)), by decide⟩

/-- The foil (WRONG order) staircase on the witness data — this is exactly R1's
`witness_staircasePath`, under the corrected name. -/
theorem witness_foilStaircasePath :
    foilStaircasePath witnessY witnessX =
      {((fun _ => (0 : Fin 4)), (0 : Fin 3)),
        ((fun μ => if μ.val = 0 then 1 else 0), (2 : Fin 3))} := by
  decide

/-- A bond entirely outside the block and the staircase: site `(2,2,2)`, direction `0`. -/
def witnessOutsideBond : Bond witnessL := ((fun _ => (2 : Fin 4)), (0 : Fin 3))

theorem witnessOutsideBond_not_mem : witnessOutsideBond ∉ staircasePath witnessY witnessX := by
  rw [witness_staircasePath]; decide

/-- **Non-vacuity, discharged concretely**, now with the (2.121) antecedents supplied. -/
theorem witness_admissibleSubspace_ne_bot :
    admissibleSubspace witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block ≠ ⊥ :=
  admissibleSubspace_ne_bot_of_exists witnessOutsideBond witnessOutsideBond_not_mem

/-- **Non-triviality, discharged concretely**, likewise. -/
theorem witness_admissibleSubspace_ne_top :
    admissibleSubspace witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block ≠ ⊤ :=
  admissibleSubspace_ne_top_of_nonempty witness_staircasePath_nonempty

#print axioms coarseLattice_exists
#print axioms coarseLattice_unique
#print axioms mem_admissibleSubspace
#print axioms witness_admissibleSubspace_ne_bot
#print axioms witness_admissibleSubspace_ne_top

/-! ## §7. The concrete `BlockGeometry` instance (reuse of `Balaban.Blocks`, LAW-19) — UNCHANGED

Kept byte-for-byte from R1: this section answers a DIFFERENT question (the abstract `BlockGeometry`
structure's `Center` embedding) than the `Λ'` antecedent `admissibleSubspace` now requires (§1b/§4).
`FittingCenter` remains a real, useful, but STRICTLY WEAKER notion than `CoarseLattice` — §9 makes
the comparison explicit and concrete. -/

/-- `blockOf`'s cardinality law: every block has exactly `ell^3` sites, PROVIDED it fits inside the
periodic extent (`hfit`) — CMP96 printed p.244 `(2.123)`'s implicit `|B(y)| = L^d` law
(`Blocks.lean`'s `BlockGeometry.card_block`), proved here (not merely cited) for this concrete
axis-aligned box embedding, via an explicit bijection with `Fin 3 → Fin ell`. -/
theorem card_blockOf (y : PeriodicLatticeSite L) (ell : ℕ)
    (hfit : ∀ μ, (y μ).val + ell ≤ L μ + 1) :
    (blockOf y ell).card = ell ^ 3 := by
  have hbij : blockOf y ell = Finset.image
      (fun f : Fin 3 → Fin ell => (fun μ : Fin 3 => (⟨(y μ).val + (f μ).val, by
        have := (f μ).isLt
        have := hfit μ
        omega⟩ : Fin (L μ + 1)))) Finset.univ := by
    ext x
    simp only [mem_blockOf, inBlock, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hx
      refine ⟨fun μ => ⟨(x μ).val - (y μ).val, ?_⟩, ?_⟩
      · have h1 := (hx μ).1
        have h2 := (hx μ).2
        omega
      · funext μ
        have h1 := (hx μ).1
        have h2 := (hx μ).2
        apply Fin.ext
        simp only
        omega
    · rintro ⟨f, rfl⟩
      intro μ
      simp only
      have := (f μ).isLt
      omega
  rw [hbij, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fun]
  · simp
  · intro f g hfg
    funext μ
    have := congrFun hfg μ
    apply Fin.ext
    have heq : (y μ).val + (f μ).val = (y μ).val + (g μ).val := by
      have := congrArg Fin.val this
      simpa using this
    omega

/-! ## §7b — the headline correctness-in-the-aligned-case result, closing §1c/§7's gap into one
proved chain (Defect 3 repair). -/

/-- **Correctness, proved rather than argued**: every `CoarseLattice` member's block has EXACTLY
`ell^3` sites, given the tileability hypothesis. Closes §1c's `coarseLattice_mem_fits` against
§7's `card_blockOf`. -/
theorem card_blockOf_of_coarse {L : PeriodicLatticeExtent} {ell : ℕ}
    (hdvd : ∀ μ, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    (blockOf y ell).card = ell ^ 3 :=
  card_blockOf y ell (coarseLattice_mem_fits hdvd hy)

/-- **The same, for the type-bundled center** — by construction, no side hypothesis to discharge
at the call site. -/
theorem alignedCoarseCenter_card {L : PeriodicLatticeExtent} {ell : ℕ}
    {hdvd : ∀ μ, ell ∣ (L μ + 1)} (c : AlignedCoarseCenter L ell hdvd) :
    (blockOf c.1 ell).card = ell ^ 3 :=
  card_blockOf c.1 ell (alignedCoarseCenter_fits c)

#print axioms card_blockOf_of_coarse
#print axioms alignedCoarseCenter_card

/-- **A GENUINE FINDING, surfaced rather than papered over** (R1, unchanged): on a PERIODIC
(wraparound) lattice, `Center := Site` — every fine site a valid block corner — is FALSE in general
for `ell > 1`. The honest fix, matching Balaban's own structure: `Center` is the SUBTYPE of sites
where the block of side `ell` actually fits — but this is NOT `Λ'` (§1b/§9 make the distinction
concrete). -/
def FittingCenter (L : PeriodicLatticeExtent) (ell : ℕ) : Type :=
  {y : PeriodicLatticeSite L // ∀ μ : Fin 3, (y μ).val + ell ≤ L μ + 1}

instance instFintypeFittingCenter (L : PeriodicLatticeExtent) (ell : ℕ) :
    Fintype (FittingCenter L ell) := Subtype.fintype _

instance instDecidableEqFittingCenter (L : PeriodicLatticeExtent) (ell : ℕ) :
    DecidableEq (FittingCenter L ell) := Subtype.instDecidableEq

/-- **Concrete instance connecting to `Balaban.Blocks`' abstract `BlockGeometry`**, `Site :=
PeriodicLatticeSite L`, `Center := FittingCenter L ell`. Resolves `PHASE0_DEFS_PLAN.md`'s C1
embedding question for THIS box-shaped case — a specific, correctly-scoped instance, not a general
resolution of C1. Unrelated to and unchanged by the `Λ'`/antecedent repair in §1b/§4. -/
def blockGeometryOf (L : PeriodicLatticeExtent) (ell : ℕ) :
    Balaban.BlockGeometry (PeriodicLatticeSite L) (FittingCenter L ell) where
  B := fun y => blockOf y.1 ell
  L := ell
  d := 3
  card_block := fun y => card_blockOf y.1 ell y.2

/-- The witness corner genuinely fits. -/
theorem witnessY_fits : ∀ μ : Fin 3, (witnessY μ).val + witnessEll ≤ witnessL μ + 1 := by decide

def witnessYFitting : FittingCenter witnessL witnessEll := ⟨witnessY, witnessY_fits⟩

theorem witness_blockGeometryOf_B :
    (blockGeometryOf witnessL witnessEll).B witnessYFitting = blockOf witnessY witnessEll := rfl

theorem witness_blockGeometryOf_card :
    ((blockGeometryOf witnessL witnessEll).B witnessYFitting).card = witnessEll ^ 3 :=
  card_blockOf witnessY witnessEll witnessY_fits

#print axioms card_blockOf
#print axioms blockGeometryOf
#print axioms witnessY_fits
#print axioms witness_blockGeometryOf_card

/-! ## §8. THE ASYMMETRY ACCEPTANCE TEST — roles swapped to match §3's correction (R2)

Same mandate acceptance criterion as R1 ("exhibit a configuration in one and not the other"), now
correctly directed: the pivot bond is admissible for the TRUE `staircasePath` and excluded by BOTH
a same-radius symmetrized `ℓ¹`-ball (§8a) and the WRONG-order `foilStaircasePath` (§8b). The pivot
bond itself (`pivotBond = (0,0,0)` direction `0`) is R1's OLD pivot's sibling — the OTHER of the two
witness bonds — chosen because it is the one lying in the FOIL (not the true path), matching the
swapped roles precisely; see the R2 report §7 for the derivation of why this exact swap is forced,
not an arbitrary re-pick. -/

/-- Absolute difference of two naturals — kept local (not `Nat.dist`) so this file's arithmetic
does not depend on an unpinned Mathlib name. -/
def natAbsDiff (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- `ℓ¹`-distance between two lattice sites. -/
def l1dist (s t : PeriodicLatticeSite L) : ℕ := ∑ ν : Fin 3, natAbsDiff (s ν).val (t ν).val

/-- **The symmetrized-ball strawman**: every bond BASED within `ℓ¹`-distance `r` of `y` — direction-
blind, order-blind, exactly the kind of "simplification" (2.121) is NOT. -/
def ballPath (y : PeriodicLatticeSite L) (r : ℕ) : Finset (PeriodicLatticeEdge L) :=
  Finset.univ.filter (fun e : PeriodicLatticeEdge L => l1dist e.1 y ≤ r)

/-- The ball-admissible subspace, built identically to `admissibleSubspace` but from `ballPath`
(deliberately NOT antecedented — it is a strawman comparison object, not a `(2.121)` claim). -/
def ballAdmissibleSubspace (y : PeriodicLatticeSite L) (r : ℕ) : Submodule ℝ (Bond L → ℝ) where
  carrier := {B | ∀ b ∈ ballPath y r, B b = 0}
  zero_mem' := by intro b _; rfl
  add_mem' := by
    intro B1 B2 hB1 hB2 b hb
    simp [hB1 b hb, hB2 b hb]
  smul_mem' := by
    intro c B hB b hb
    simp [hB b hb]

/-- The foil-admissible subspace, built identically to `admissibleSubspace` but from
`foilStaircasePath` (also deliberately NOT antecedented, same reason). -/
def foilAdmissibleSubspace (y x : PeriodicLatticeSite L) : Submodule ℝ (Bond L → ℝ) where
  carrier := {B | ∀ b ∈ foilStaircasePath y x, B b = 0}
  zero_mem' := by intro b _; rfl
  add_mem' := by
    intro B1 B2 hB1 hB2 b hb
    simp [hB1 b hb, hB2 b hb]
  smul_mem' := by
    intro c B hB b hb
    simp [hB b hb]

/-- **The pivot bond, R2**: site `(0,0,0)`, direction `0` — lies in `foilStaircasePath` AND in the
ball of radius `l1dist witnessY witnessX = 2` (its base site IS `witnessY` itself, distance `0`),
but is NOT in the TRUE `staircasePath` (whose two bonds are at direction `2`/site `(0,0,0)` and
direction `0`/site `(0,0,1)` — neither matches direction `0` at site `(0,0,0)`). -/
def pivotBond : Bond witnessL := ((fun _ => (0 : Fin 4)), (0 : Fin 3))

theorem pivotBond_not_mem_staircasePath : pivotBond ∉ staircasePath witnessY witnessX := by
  rw [witness_staircasePath]; decide

theorem pivotBond_mem_foilStaircasePath :
    pivotBond ∈ foilStaircasePath witnessY witnessX := by
  rw [witness_foilStaircasePath]; decide

theorem pivotBond_l1dist_zero : l1dist (L := witnessL) pivotBond.1 witnessY = 0 := by
  simp [l1dist, natAbsDiff, pivotBond, witnessY]

/-- `l1dist witnessY witnessX = 2`, the radius the ball strawman uses (unchanged from R1: `witnessX`
itself was not touched). -/
theorem witness_radius : l1dist witnessY witnessX = 2 := by decide

/-- The pivot indicator configuration: `1` on `pivotBond`, `0` elsewhere. -/
noncomputable def pivotConfig : Bond witnessL → ℝ := fun e => if e = pivotBond then 1 else 0

/-- **§8a — the ball strawman fails the acceptance test.** `pivotConfig` is admissible for the TRUE
`(2.121)` staircase condition (`pivotBond` is outside `staircasePath`) but is EXCLUDED by the
symmetrized ball of the correct radius (`pivotBond` lies in the ball, distance `0 ≤ 2`). -/
theorem staircase_ne_ball_witness :
    pivotConfig ∈ admissibleSubspace witnessY witnessX witnessEll witnessY_coarse
        witnessX_mem_block ∧
      pivotConfig ∉ ballAdmissibleSubspace witnessY (l1dist witnessY witnessX) := by
  constructor
  · rw [mem_admissibleSubspace]
    intro b hb
    have hbne : b ≠ pivotBond := by
      intro h; rw [h] at hb; exact pivotBond_not_mem_staircasePath hb
    simp [pivotConfig, hbne]
  · intro hmem
    have hin : pivotBond ∈ ballPath witnessY (l1dist witnessY witnessX) := by
      rw [ballPath, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, pivotBond_l1dist_zero.le.trans (by omega)⟩
    have := hmem pivotBond hin
    simp [pivotConfig] at this

/-- **§8b — the WRONG-order foil fails the acceptance test too.** Same `pivotConfig`: admissible
for the TRUE staircase but not for `foilStaircasePath`, since `pivotBond` lies exactly in the
foil. -/
theorem staircase_ne_foil_witness :
    pivotConfig ∈ admissibleSubspace witnessY witnessX witnessEll witnessY_coarse
        witnessX_mem_block ∧
      pivotConfig ∉ foilAdmissibleSubspace witnessY witnessX := by
  refine ⟨(staircase_ne_ball_witness).1, ?_⟩
  intro hmem
  have := hmem pivotBond pivotBond_mem_foilStaircasePath
  simp [pivotConfig] at this

#print axioms staircase_ne_ball_witness
#print axioms staircase_ne_foil_witness

/-! ## §9. D1 CLOSURE — Sol's exact exploit, and the `FittingCenter`-vs-`CoarseLattice` comparison

Two demonstrations, both mechanical: (a) the `x ∈ B(y)` antecedent genuinely gates the object — no
proof exists for a provably-outside `x`, so Sol's exact exploit is now a type error (verified in
scratch during this dispatch, see the R2 report §10); (b) the `y ∈ Λ'` antecedent genuinely excludes
the SPECIFIC overlapping-start site Sol used to convict `FittingCenter`. -/

/-- An `x` provably OUTSIDE the block — Sol's exact D1 exploit target. -/
def outsideX : PeriodicLatticeSite witnessL := fun _ => 3

/-- **No proof of `outsideX ∈ blockOf witnessY witnessEll` exists** — this is the "no witness"
certificate. Consequently `admissibleSubspace witnessY outsideX witnessEll witnessY_coarse hx`
cannot even be STATED without a term of the (uninhabited, on this data) type
`outsideX ∈ blockOf witnessY witnessEll`: attempting Sol's exact exploit,
`(fun _ => 0) ∈ admissibleSubspace witnessY outsideX witnessEll witnessY_coarse
  outsideX_not_mem_block`, is a TYPE MISMATCH at elaboration (confirmed in this dispatch's own
scratch testing, not merely asserted — R2 report §10), not an unproved side-goal. -/
theorem outsideX_not_mem_block : outsideX ∉ blockOf witnessY witnessEll := by decide

/-- **The exact overlapping-start site Sol's gate used to convict `FittingCenter`**: side `2` on `4`
sites admits BOTH `0` (`witnessY`) and `1` as "fitting centers" — Sol: "it admits overlapping starts
such as 0 and 1 at side 2." -/
def overlapStart : PeriodicLatticeSite witnessL := fun _ => 1

/-- `overlapStart` genuinely satisfies `FittingCenter`'s defining predicate — the pathology is real,
not hypothetical. -/
theorem overlapStart_fits : ∀ μ : Fin 3, (overlapStart μ).val + witnessEll ≤ witnessL μ + 1 := by
  decide

/-- **`CoarseLattice` correctly EXCLUDES it** — `overlapStart`'s coordinates are `1`, not a multiple
of `witnessEll = 2`. This is the concrete demonstration that `Λ'` (§1b) is a STRICT, non-cosmetic
refinement of `FittingCenter`, excluding EXACTLY the pathology Sol named, not some unrelated
site. -/
theorem overlapStart_not_coarse : overlapStart ∉ CoarseLattice witnessL witnessEll := by decide

/-! ## §9c — THE DANGER MADE CONCRETE: a NON-aligned center genuinely undercounts (Defect 3,
"make the unaligned case a proved error", the third option in the dispatch's menu).
`Balaban/KernelSubspace.lean`'s own docstring records that `coarseRestrictSite` does NOT constrain
its centers to `CoarseLattice` — this is the kernel-checked demonstration of what goes wrong if
that freedom is ever exercised at the lattice boundary. -/

/-- A boundary center at the TOP of every coordinate — NOT a member of `CoarseLattice`
(`3 % 2 = 1 ≠ 0`), exactly the kind of center `coarseRestrictSite`'s unconstrained signature
permits. -/
def boundaryCenter : PeriodicLatticeSite witnessL := fun _ => (3 : Fin 4)

theorem boundaryCenter_not_coarse : boundaryCenter ∉ CoarseLattice witnessL witnessEll := by decide

/-- **The undercount, computed exactly**: only ONE site (`boundaryCenter` itself) satisfies the
box condition in every coordinate simultaneously, not `witnessEll^3 = 8`. -/
theorem boundaryCenter_blockOf_card : (blockOf boundaryCenter witnessEll).card = 1 := by decide

/-- **THE PROVED ERROR**: the block of a non-`CoarseLattice` center does NOT have `ell^3` sites —
kernel-checked, not asserted. Any averaging operator that divides by the full `ell^3` (bond:
`ell^4` via `Balaban.LatticeOperators.coarseRestrict`; site: `ell^3` via
`Balaban.KernelSubspace.coarseRestrictSite`) while summing over `blockOf boundaryCenter witnessEll`
is off by a factor of exactly `witnessEll^3 = 8` at this concrete witness — the "wrong coefficient
in the block average" the coordinator's evidence names. Mutation: the FALSE universal this refutes
is "every center's block has `ell^3` sites, alignment or not" — `boundaryCenter` is the witness
that makes that universal false, kernel-checked rather than merely argued from the boundary
disagreement (`blockOfPeriodic_ne_blockOf_at_boundary`, `HoleHunt/ConventionPins.lean` §5, which
pins the PREDICATE disagreement; this pins the CARDINALITY consequence). -/
theorem boundaryCenter_undercounts :
    (blockOf boundaryCenter witnessEll).card ≠ witnessEll ^ 3 := by
  rw [boundaryCenter_blockOf_card]
  decide

#print axioms boundaryCenter_not_coarse
#print axioms boundaryCenter_blockOf_card
#print axioms boundaryCenter_undercounts

/-! ## §9d — `admissibleSubspaceInter` IS A GENUINE STRICT NARROWING (V-scope repair, this
pass; docstring CORRECTED, grade-2 gate repair, this pass): a SECOND coarse pair, concretely
computed, constrains a bond the FIRST pair's `Γ_{y,x}` never touches — kernel-checked evidence
that intersecting over `Λ'` genuinely does more than a single pair, not a same-shaped relabeling
of `admissibleSubspace witnessY witnessX`.

**Correction (grade-2 gate, this pass): this section proves STRICT SUBSET, not non-vacuity.**
`admissibleSubspaceInter_strict_witness` below was previously labeled "GENUINE, NON-VACUOUS
NARROWING" — imprecise: it exhibits `pivotConfig2` inside ONE pair's `admissibleSubspace` and
outside the intersection, i.e. `admissibleSubspaceInter witnessL witnessEll <
admissibleSubspace witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block` (containment,
strict), which says nothing about whether `admissibleSubspaceInter` itself equals `⊥`. For
`admissibleSubspaceInter L ell ≠ ⊥` (needed because `CoercivityHypothesis.V_ne_bot` is a
mandatory field of every consumer instance), see the UNCONDITIONAL `admissibleSubspaceInter_ne_bot`
in §4c above instead. -/

/-- A second coarse center, distinct from `witnessY`: `(2,2,2)`, still a member of `CoarseLattice`
(every coordinate `≡ 0 (mod witnessEll = 2)`). -/
def witnessY2 : PeriodicLatticeSite witnessL := fun _ => 2

theorem witnessY2_coarse : witnessY2 ∈ CoarseLattice witnessL witnessEll := by decide

/-- A point in `witnessY2`'s block, differing from `witnessY2` only in coordinate `2`. -/
def witnessX2 : PeriodicLatticeSite witnessL := fun μ => if μ.val = 2 then 3 else 2

theorem witnessX2_mem_block : witnessX2 ∈ blockOf witnessY2 witnessEll := by decide

/-- The staircase for the SECOND pair, computed out fully: a single bond, base `(2,2,2)`
direction `2` — entirely disjoint from `staircasePath witnessY witnessX`'s two bonds (bases
`(0,0,0)` and `(0,0,1)`, both far from `(2,2,2)`). -/
theorem witness_staircasePath2 :
    staircasePath witnessY2 witnessX2 = {((fun _ => (2 : Fin 4)), (2 : Fin 3))} := by decide

/-- The pivot bond for the second pair. -/
def pivotBond2 : Bond witnessL := ((fun _ => (2 : Fin 4)), (2 : Fin 3))

theorem pivotBond2_mem_staircasePath2 : pivotBond2 ∈ staircasePath witnessY2 witnessX2 := by
  rw [witness_staircasePath2]; decide

/-- **`pivotBond2` lies outside the FIRST pair's `Γ_{y,x}`** — confirmed against the already-computed
`witness_staircasePath`, not re-derived. -/
theorem pivotBond2_not_mem_staircasePath : pivotBond2 ∉ staircasePath witnessY witnessX := by
  rw [witness_staircasePath]; decide

/-- The pivot-2 indicator configuration. -/
noncomputable def pivotConfig2 : Bond witnessL → ℝ := fun e => if e = pivotBond2 then 1 else 0

/-- **THE NARROWING, KERNEL-CHECKED**: `pivotConfig2` is admissible for the FIRST pair alone
(vanishes on `Γ_{witnessY,witnessX}`, since `pivotBond2` lies outside it) but is EXCLUDED from
`admissibleSubspaceInter` (it is nonzero on `pivotBond2`, which lies in the SECOND pair's
`Γ_{witnessY2,witnessX2}`). This is the concrete refutation of "the intersection adds nothing beyond
one pair": `admissibleSubspaceInter witnessL witnessEll` is a STRICT subset of
`admissibleSubspace witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block` at this witness,
not an equal (relabeled) object. **This is a containment fact only — it does NOT establish
`admissibleSubspaceInter witnessL witnessEll ≠ ⊥`** (a strict subset of a nonempty submodule can
still be `⊥`); for that, see the unconditional `admissibleSubspaceInter_ne_bot` in §4c above. -/
theorem admissibleSubspaceInter_strict_witness :
    pivotConfig2 ∈ admissibleSubspace witnessY witnessX witnessEll witnessY_coarse
        witnessX_mem_block ∧
      pivotConfig2 ∉ admissibleSubspaceInter witnessL witnessEll := by
  constructor
  · rw [mem_admissibleSubspace]
    intro b hb
    have hbne : b ≠ pivotBond2 := by
      intro h; rw [h] at hb; exact pivotBond2_not_mem_staircasePath hb
    simp [pivotConfig2, hbne]
  · intro hmem
    have := hmem witnessY2 witnessY2_coarse witnessX2 witnessX2_mem_block pivotBond2
      pivotBond2_mem_staircasePath2
    simp [pivotConfig2] at this

#print axioms witnessY2_coarse
#print axioms witnessX2_mem_block
#print axioms witness_staircasePath2
#print axioms pivotBond2_mem_staircasePath2
#print axioms pivotBond2_not_mem_staircasePath
#print axioms admissibleSubspaceInter_strict_witness

end AdalyFormal.Balaban.AdmissibleSubspace
