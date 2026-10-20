/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic

/-!
# Balaban's block geometry — `B(y)`, bonds `B(c)`, and Λ-bonds

Phase-0 REFORM_PROGRAM definitions layer (`REFORM_PROGRAM.md`, `PHASE0_DEFS_PLAN.md` item A1/B1).
Stands alone: no import of `Target.ClayStatement` (that wiring is `Spine.lean`'s job).

## Source pins

* **`B(c_-)`, the block of sites averaged over** — `corpus/pages/CMP98_p19.md`
  (`verification_status: adjudicated`), eq. (14)-(15): both averaging formulas sum over
  `x ∈ B(c_-)`, a finite block of sites attached to a coarse point `c_-`. Neither adjudicated
  CMP98 page states `B`'s cardinality or exact combinatorial embedding explicitly.
* **The cardinality law `|B(y)| = L^d`** — read directly off the rendered page image
  `compute/balaban_su2_papers/balaban_CMP96_1984_propagators_II.pdf`, PDF page 22 = printed page
  244 (`corpus/tools/page_offsets.json`: paper `CMP96`, offset 222, `constant_verified: true`),
  independently re-rendered and read for this module (image-verified per LAW-11/20; NOT yet filed
  under `corpus/pages/` — see `BALABAN_DEFS_REPORT.md` for the promotion recommendation to the
  corpus lane). The page's `(2.123)` displays `Σ_{b⊂B(y)} |B(b)|² ≦ d L^d Σ_{p⊂B(y)} |(∂₁B)(p)|²`,
  and the surrounding argument sums `d L^d`-many bond terms against `L^d`-many plaquettes inside
  one block — `B(y)` is a `d`-dimensional `L`-block, `|B(y)| = L^d`. This is exactly
  `PHASE0_DEFS_PLAN.md` item **B1**'s recommended groundwork law, now pinned to the page rather
  than merely proposed.
* **`B(c)` for a coarse BOND `c` — bonds with BOTH endpoints block-constrained** — same page,
  printed 244: *"bonds `b ∈ B(c) = {b : b_ ∈ B(c_-), b_+ ∈ B(c_+)}` for some `c ∈ Λ'`. Let
  `c = ⟨y, y+Le_μ⟩`..."* — `c` here is a **coarse bond** (an edge of the block lattice) with two
  endpoint block-centers `c_-, c_+`; `B(c)` is the set of FINE bonds whose tail lies in the
  `c_-`-block AND whose head lies in the `c_+`-block. **BOTH endpoints constrained** — this is
  `bondsBetweenBlocks` below.
* **`Λ`-bonds (Lemma 2.4) — AT LEAST ONE endpoint** — printed 245: *"Let a set `Λ ⊂ Z^d` be a sum
  of blocks, `Λ = B(Λ')`. We denote by `Λ` also a set of bonds `b` such that **at least one** of
  the end-points `b_-, b_+` belongs to `Λ`."* This is a DIFFERENT, strictly weaker membership
  condition than `bondsBetweenBlocks` above, for a different index object (a general block union
  `Λ`, not a single coarse bond `c`). **Both definitions are transcribed verbatim from the same
  two-page span and never conflated** — S83 ("enumerate against the definition, not the
  construction") names exactly this at-least-one-vs-both confusion as a convicted defect pattern
  elsewhere in the campaign; `bondsTouching_ne_bondsBothEndpointsIn_witness` in
  `Balaban/Probes.lean` is the standing regression guard.

## Scope (L7 / REFORM_PROGRAM Phase 0)

Definitions only. The exact geometric embedding of `B : Center → Finset Site` into `ℤ^d` (how a
block-center `y` determines its cube of sites) is `PHASE0_DEFS_PLAN.md`'s **C1**, explicitly
flagged there as unresolved pending a fuller source read — this module does NOT commit to a
specific embedding. It axiomatizes the one property that IS pinned (`|B(c)| = L^d`) and builds the
bond-geometry definitions on top of an abstract `B`, exactly matching the plan's B1 recommendation
("a concrete `B : Site → Finset Site` satisfying a stated cardinality/geometry law"). A full
partition/disjointness law (blocks tile the lattice) is standard for any genuine block
decomposition but is NOT separately page-pinned here; it is not assumed below — `card_block` is
the only structural axiom, deliberately minimal.
-/

namespace AdalyFormal.Balaban

/-- **Block geometry**, `PHASE0_DEFS_PLAN.md` item B1.

A finite fine lattice `Site`, a finite coarse index `Center`, a block assignment `B : Center →
Finset Site` (`B(y)` on `corpus/pages/CMP98_p19.md` eq. (14)-(15)), and the one law pinned by the
page-image read of CMP96 printed p.244 `(2.123)`: every block has exactly `L^d` sites, for the
paper's own `L` (RG block scale) and `d` (lattice dimension). -/
structure BlockGeometry (Site Center : Type*) [Fintype Site] [DecidableEq Site]
    [Fintype Center] [DecidableEq Center] where
  /-- `B(y)`: the block of fine sites attached to a coarse point `y`. -/
  B : Center → Finset Site
  /-- RG block side length. -/
  L : ℕ
  /-- Lattice dimension. -/
  d : ℕ
  /-- CMP96 printed p.244, `(2.123)`'s implicit block size: `|B(y)| = L^d`. -/
  card_block : ∀ y, (B y).card = L ^ d

variable {Site Center : Type*} [Fintype Site] [DecidableEq Site]
  [Fintype Center] [DecidableEq Center]

/-- **`B(c)` for a coarse bond `c = (c_-, c_+)`** — CMP96 printed p.244: `{b : b_ ∈ B(c_-), b_+ ∈
B(c_+)}`. BOTH endpoints constrained; `c` here is a pair of adjacent block-centers, not a general
set. Represented as an ordered pair `(cMinus, cPlus) : Center × Center`; the fine bond set is the
literal product `B(cMinus) ×ˢ B(cPlus)`. -/
def bondsBetweenBlocks (geo : BlockGeometry Site Center) (cMinus cPlus : Center) :
    Finset (Site × Site) :=
  geo.B cMinus ×ˢ geo.B cPlus

/-- The block-union `Λ = B(Λ')` for a set of coarse centers `Λ'` — CMP96 printed p.245, Lemma 2.4's
opening clause "`Λ ⊂ Z^d` be a sum of blocks, `Λ = B(Λ')`". -/
def blockUnion (geo : BlockGeometry Site Center) (Λ' : Finset Center) : Finset Site :=
  Λ'.biUnion geo.B

/-- **Λ-bonds (Lemma 2.4)** — CMP96 printed p.245: "a set of bonds `b` such that **at least one**
of the end-points `b_-, b_+` belongs to `Λ`", filtered out of an ambient fine-bond set `allBonds`
(the paper's own ambient bond set of the fine lattice, supplied here rather than constructed, since
the fine-lattice link geometry is `Spine.lean`'s wiring job, not this standalone module's). -/
def bondsTouching (Λ : Finset Site) (allBonds : Finset (Site × Site)) :
    Finset (Site × Site) :=
  allBonds.filter (fun b => b.1 ∈ Λ ∨ b.2 ∈ Λ)

/-- The DEGENERATE (both-endpoints) reading of the SAME Λ, kept only so
`Balaban/Probes.lean` can prove it is a genuinely different, strictly smaller set than
`bondsTouching` — the exact "at-least-one vs both" conflation S83 warns against. Not used anywhere
else in this file. -/
def bondsBothEndpointsIn (Λ : Finset Site) (allBonds : Finset (Site × Site)) :
    Finset (Site × Site) :=
  allBonds.filter (fun b => b.1 ∈ Λ ∧ b.2 ∈ Λ)

omit [Fintype Site] in
/-- `bondsBothEndpointsIn` is always a subset of `bondsTouching` on the same data — the "both"
reading can never see more bonds than the "at-least-one" reading. Elementary, but pins the
direction of the S83 weakening so `Probes.lean`'s non-vacuity witness is checking the right
inequality. -/
theorem bondsBothEndpointsIn_subset_bondsTouching (Λ : Finset Site)
    (allBonds : Finset (Site × Site)) :
    bondsBothEndpointsIn Λ allBonds ⊆ bondsTouching Λ allBonds := by
  intro b hb
  simp only [bondsBothEndpointsIn, Finset.mem_filter] at hb
  simp only [bondsTouching, Finset.mem_filter]
  exact ⟨hb.1, Or.inl hb.2.1⟩

end AdalyFormal.Balaban
