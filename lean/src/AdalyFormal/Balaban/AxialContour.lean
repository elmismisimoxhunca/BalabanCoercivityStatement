/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.AdmissibleSubspace

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `Ax(y)` — the blockwise axial-gauge contour bond set, CMP95 `(1.10)`

## Fidelity check (lead requirement of this dispatch) — done FIRST, at the DEFINING page

`compute/kimi_omega_gate/VERDICT.md` (Kimi second-family gate) found: **"Ax(y): CONFIRMED same
object"** — same staircase contours `Γ_{y,x}` (CMP95 `(1.7)`), same linear zero-condition, and an
explicit provenance chain CMP96 `(2.121)`/`(2.152)-(2.154)` → CMP99b's `(3.156)` region (via
`"[4] (2.154-2.155)"` on CMP99b printed p.428). It flagged that the reuse candidate
`AdmissibleSubspace.lean`'s `staircasePath` "needs a dedicated fidelity check against CMP95's
original convention, since that file's own R1→R2 history shows this coordinate-order is
error-prone." That check is done here, against the page that DEFINES `Γ_{y,x}` (CMP95 `(1.7)`),
not the page that USES it (CMP96 p.244, which is what `AdmissibleSubspace.lean`'s own R2 repair
pass actually re-derived from — see its docstring, "BUILD DISCIPLINE" rule 1 of this dispatch:
read the page that defines, not the page that uses).

**Source, rendered and read directly (LAW-11), independent second pass:**
`pdftoppm -r 300 -f 2 -l 4 -png compute/balaban_su2_papers/balaban_CMP95_1984_propagators_I.pdf`
(offset 16 per `corpus/tools/page_offsets.json`'s `constant_verified: true` entry for
`balaban_CMP95_1984_propagators_I`, `evidence_sample` includes `[18,2],[19,3],[20,4]` — printed
page `p` = pdf page `p - 16`). Printed pp. 18-19 headers read "18"/"T. Balaban" and
"Propagators for Lattice Gauge Theories. I"/"19" in the image. sha256 of the two renders used:
`9da7b05b423be0d97302a53aff0da0a4b2d22e07f5e9f4855879fd5fb828e145` (p.18, pdf page 2) and
`6642f04cf5484919591c3157c83a3062c3dca7da9d954347de140e15f9f67199` (p.19, pdf page 3) —
byte-identical to `renders/p18cmp95-02.png` and `renders/cmp95_p1920-03.png` already on disk from
an earlier, independent lane (reproducibility, S-class dual-run discipline).

**(1.6), printed p.18** (verbatim, image-read):
`B(y) = {x ∈ T_1 : y_μ ≦ x_μ < y_μ + L, μ = 1,...,d}, y ∈ T_L^{(1)}.`
Matches `AdmissibleSubspace.lean`'s `blockOf`/`inBlock` exactly (half-open coordinate box), modulo
the outer quantifier `y ∈ T_L^{(1)}` — CMP95's `T_L^{(1)} = T_1 ∩ Lℤ^d` (stated in prose
immediately above (1.6)) is EXACTLY `AdmissibleSubspace.lean`'s `CoarseLattice L ell` with `ell :=
L` (sites all of whose coordinates are multiples of the block scale) — reused below as `T_L^{(1)}`'s
formal referent, not redefined.

**(1.7), printed p.18** (verbatim, image-read):
`Γ_{y,x} = [y,(y_1,...,y_{d-1},x_d)] ∪ ... ∪ [(y_1,...,y_μ,x_{μ+1},...,x_d),
  (y_1,...,x_μ,x_{μ+1},...,x_d)] ∪ ... ∪ [(y_1,x_2,...,x_d),x],`
`where [x_1,x_2] is a line segment connecting points x_1,x_2.`
Read term by term: the FIRST segment (leaving `y`) has left endpoint `y` and right endpoint
`(y_1,...,y_{d-1},x_d)` — coordinate `d` (the LAST coordinate) switches from `y_d` to `x_d`, all
others still at `y`. The GENERIC term for a coordinate `μ` has left endpoint
`(y_1,...,y_μ,x_{μ+1},...,x_d)` (coords `1..μ` at `y`, `μ+1..d` at `x`) and right endpoint
`(y_1,...,x_μ,x_{μ+1},...,x_d)` (coords `1..μ-1` at `y`, `μ..d` at `x`) — coordinate `μ` switches.
The LAST displayed term `[(y_1,x_2,...,x_d),x]` matches this generic pattern at `μ = 1` (coord `1`
at `y`, coords `2..d` at `x`, switching to all-`x`). So, walking `Γ_{y,x}` FROM `y` TO `x`, the
coordinate switch order is **`d, d-1, ..., 1`** — the LAST coordinate first, the FIRST coordinate
last. On this file's `d = 3`, `0`-indexed `Fin 3` carrier, that is **switch order `2, 1, 0`** from
`y`.

**Cross-check against the reuse candidate**: `AdmissibleSubspace.lean`'s `staircasePath`
docstring states its own independently re-derived order (from CMP96 p.244's telescoping argument,
a USING page) as *"walk coordinate `2` first (from `y` to `corner1`), then coordinate `1`
..., then coordinate `0` last"* — **identical** to the order just derived here directly from
CMP95's own DEFINING equation `(1.7)`. Two independent derivations, from two different pages (one
a definition, one a use), by two different repair passes, agree exactly on the coordinate order.
**Verdict: `staircasePath` is REUSED, not rebuilt** — CMP95 `(1.7)` fidelity is CONFIRMED at the
defining page, not merely inherited from the CMP96-page derivation. No divergence found.

**(1.10), printed p.19** (verbatim, image-read):
`δ_Ax(A) = ∏_{y ∈ T_L^{(1)}} ∏_{x ∈ B(y), x ≠ y} δ(A(Γ_{y,x})),`
introduced by the prose immediately above it: *"we remove it by introducing Axial (Ax) gauge
fixing conditions `A(Γ_{y,x}) = 0`, `x ∈ B(y)`, `x ≠ y`, `y ∈ T_L^{(1)}`."*

**A specialization this build states plainly, not silently.** CMP95's own `(1.10)` is, LITERALLY,
a family of ONE linear condition per pair `(y,x)` — the SUM `A(Γ_{y,x}) = Σ_{b ⊂ Γ_{y,x}} A(b)`
vanishes, not each individual bond of `Γ_{y,x}` separately. The INDIVIDUAL-bond-zero form —
`B(b) = 0` for every `b ⊂ Γ_{y,x}` — is what CMP96's `(2.121)` (printed p.244, already the pin for
`AdmissibleSubspace.lean`'s `admissibleSubspace`) states directly, and it is this
individual-bond form that CMP99b's `(3.156)` subspace consumes (per the omega gate's citation:
`"...B = 0 on ∪_{y∈Λ'} Ax(y)..."`, parametrized "in the same way as in [4] (2.154-2.155)").

These two forms are NOT definitionally the same proposition, but they ARE provably equivalent for
the staircase geometry, by a telescoping/differencing argument: because `(1.10)`'s SUM condition
holds for **every** `x ∈ B(y)` simultaneously (not one at a time), and neighboring staircases
`Γ_{y,x}`, `Γ_{y,x'}` for `x, x'` differing in one coordinate share all but their final segment,
differencing consecutive sum-conditions along one swept coordinate recovers each individual bond
value on that segment — exactly the mechanism `AdmissibleSubspace.lean`'s own docstring exhibits
for the CMP96 p.244 telescoping identity (its `§3`, the `j`-indexed argument). Worked by hand for
`d = 2` in this dispatch's own scratch work (not shipped as a Lean theorem here — see
`AXIAL_CONTOUR.md` §"Named residual" for the full worked argument and exactly where a general-`d`
Lean formalization would go): fixing `x_2` and varying `x_1` over the block width recovers the
horizontal bonds at height `x_2` by differencing; fixing `x_1 = y_1` and varying `x_2` recovers
the vertical trunk bonds. **This file builds the CMP96/CMP99b individual-bond-zero form directly**
(matching what the `(3.156)` subspace actually consumes, per the omega gate's confirmed-same-object
finding), and states — rather than silently assumes — that this is the STRONGER of the two
provably-equivalent readings of "the Ax gauge fixing condition", named as `AXIAL_CONTOUR.md`'s
residual R1.

## What this module builds

1. **`Ax y ell`** (`§1`) — the bond set `⋃_{x ∈ B(y), x ≠ y} Γ_{y,x}`, CMP95 `(1.10)`'s contour
   union rooted at a single `y`, built from `AdmissibleSubspace.lean`'s `staircasePath`/`blockOf`
   by REUSE (import only — `AdmissibleSubspace.lean` is not edited by this file, per the dispatch's
   explicit NO-GO).
2. **`AxLocus y ell`** (`§2`) — the `Submodule ℝ (Bond L → ℝ)` of configurations vanishing on
   `Ax y ell` — the single-block clause.
3. **`AxUnionLocus S ell`** (`§3`) — the same clause for a whole `Finset` `S` of centers `y`,
   generalizing both CMP95's own `(1.10)` (`S := CoarseLattice L ell`, i.e. `S = T_L^{(1)}`,
   EVERY coarse site) and CMP96 `(2.121)`/CMP99b `(3.156)`'s restricted use (`S := Λ'`, a proper
   sub-`Finset` of the coarse lattice) as the SAME construction at different `S` — this is the
   object "ready to be one of the three intersected clauses of the `(3.156)` subspace."
4. **Non-vacuity** (`§4`) — a concrete `Ax(y)` on the witness lattice (reusing
   `AdmissibleSubspace.lean`'s `witnessL`/`witnessY`/`witnessEll`), a nonzero field vanishing on
   it, and a field not vanishing on it, so `AxLocus`/`AxUnionLocus` are proper (`≠ ⊥`, `≠ ⊤`)
   subspaces, not degenerate.
5. **Degeneracies** (`§5`) — `ell = 1` (blocks are singletons, `Ax y 1 = ∅`, `AxLocus y 1 = ⊤`,
   proved in general, not just on the witness) and `y` at a periodic-extent corner (reusing
   `AdmissibleSubspace.lean`'s `boundaryCenter`/`boundaryCenter_blockOf_card`: the SAME emptiness
   conclusion, `Ax boundaryCenter witnessEll = ∅`, for a DIFFERENT reason — boundary truncation of
   `blockOf`, not `ell = 1`).

## What this module does NOT build (named, not silently dropped)

* **The full `(3.156)` subspace** — only its second (`Ax`) clause; `Λ` (first clause) and `Q₁`
  (third clause, and per the omega gate NOT the same object as CMP95's abelian `Q₁` once `U ≠ 1`)
  are explicitly out of scope for this dispatch.
* **The CMP95 `(1.10)` sum-condition itself as a Lean object** — only its individually-provably-
  equivalent, CMP96/CMP99b-consumed reformulation. The equivalence is argued by hand (above and in
  `AXIAL_CONTOUR.md`), not machine-checked in this file; named as residual R1, not silently
  identified.
* **`δ_Ax(A)` as a measure-theoretic Dirac delta / density** — this file builds the SET
  `Ax y ell` and its zero-LOCUS as an algebraic `Submodule`, matching what `AdmissibleSubspace.lean`
  already does for a single pair and what the `(3.156)` subspace's clause needs; it does not build
  a measure or a gauge-fixing Jacobian.
-/

namespace AdalyFormal.Balaban.AxialContour

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace

variable {L : PeriodicLatticeExtent}

/-! ## §1. `Ax(y)` — the axial-gauge contour bond set rooted at `y`, CMP95 `(1.10)` -/

/-- **`Ax(y)`, CMP95 `(1.10)`'s contour union, made concrete.** The union, over every `x` in the
block `B(y)` other than `y` itself, of the staircase contour `Γ_{y,x}` — REUSING
`AdmissibleSubspace.lean`'s `staircasePath` (already fidelity-checked against CMP95 `(1.7)` above)
and `blockOf` (CMP95 `(1.6)`) by import, not redefinition. `x ≠ y` matches `(1.10)`'s own
quantifier exactly (`Finset.erase`, not a separate filter, so it is visibly the SAME set `B(y)`
`(1.6)` minus the single point `y`, no silent widening or narrowing). -/
def Ax (y : PeriodicLatticeSite L) (ell : ℕ) : Finset (Bond L) :=
  (blockOf y ell |>.erase y).biUnion (staircasePath y)

theorem mem_Ax {y : PeriodicLatticeSite L} {ell : ℕ} {b : Bond L} :
    b ∈ Ax y ell ↔ ∃ x ∈ blockOf y ell, x ≠ y ∧ b ∈ staircasePath y x := by
  unfold Ax
  simp only [Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hxne, hxmem⟩, hb⟩
    exact ⟨x, hxmem, hxne, hb⟩
  · rintro ⟨x, hxmem, hxne, hb⟩
    exact ⟨x, ⟨hxne, hxmem⟩, hb⟩

/-! ## §2. `AxLocus y ell` — "`B = 0` on `Ax(y)`", the single-block clause, as a genuine
`Submodule` -/

/-- **The zero locus of `Ax(y)`**, matching `AdmissibleSubspace.lean`'s `admissibleSubspace`
construction verbatim in shape (same three-field `Submodule` proof pattern), applied to the
UNION bond set `Ax y ell` rather than a single `Γ_{y,x}`. -/
def AxLocus (y : PeriodicLatticeSite L) (ell : ℕ) : Submodule ℝ (Bond L → ℝ) where
  carrier := {B | ∀ b ∈ Ax y ell, B b = 0}
  zero_mem' := by intro b _; rfl
  add_mem' := by
    intro B1 B2 hB1 hB2 b hb
    simp [hB1 b hb, hB2 b hb]
  smul_mem' := by
    intro c B hB b hb
    simp [hB b hb]

theorem mem_AxLocus {y : PeriodicLatticeSite L} {ell : ℕ} {B : Bond L → ℝ} :
    B ∈ AxLocus y ell ↔ ∀ b ∈ Ax y ell, B b = 0 := Iff.rfl

/-! ## §3. `AxUnionLocus S ell` — "`B = 0` on `∪_{y ∈ S} Ax(y)`", the general clause

Generalizes over the CENTER SET `S`, so the SAME construction instantiates both CMP95's own
`(1.10)` (all of `T_L^{(1)}`, i.e. `S := CoarseLattice L ell`) and CMP96 `(2.121)`/CMP99b
`(3.156)`'s restricted `Λ'` (any `S : Finset (PeriodicLatticeSite L)`, in particular a PROPER
sub-`Finset` of `CoarseLattice L ell`) without redefining anything per choice of `S`. -/

/-- **The `(3.156)`-ready second clause**: `B = 0` on `⋃_{y ∈ S} Ax(y)`, for an arbitrary `Finset`
`S` of centers. Built directly (not as an infimum of `AxLocus`es) so its carrier is literally the
zero-locus of the UNION bond set, matching how CMP99b's `"B = 0 on ∪_{y∈Λ'} Ax(y)"` is phrased —
`axUnionLocus_eq_iInf` below proves this coincides with the naive "vanish on every `AxLocus`
separately" reading, so both phrasings of the source sentence pick out the same object. -/
def AxUnionLocus (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) : Submodule ℝ (Bond L → ℝ) where
  carrier := {B | ∀ y ∈ S, ∀ b ∈ Ax y ell, B b = 0}
  zero_mem' := by intro y _ b _; rfl
  add_mem' := by
    intro B1 B2 hB1 hB2 y hy b hb
    simp [hB1 y hy b hb, hB2 y hy b hb]
  smul_mem' := by
    intro c B hB y hy b hb
    simp [hB y hy b hb]

theorem mem_AxUnionLocus {S : Finset (PeriodicLatticeSite L)} {ell : ℕ} {B : Bond L → ℝ} :
    B ∈ AxUnionLocus S ell ↔ ∀ y ∈ S, ∀ b ∈ Ax y ell, B b = 0 := Iff.rfl

/-- **The two readings of "`B = 0` on `∪_{y∈S} Ax(y)`" agree**: vanishing jointly on the union
(`AxUnionLocus`, as phrased in the source) is the same condition as vanishing on every single
`AxLocus y ell` for `y ∈ S` (the `iInf` reading) — a genuine `Submodule` equality, not merely a
set-membership `Iff`. -/
theorem axUnionLocus_eq_iInf (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) :
    AxUnionLocus S ell = ⨅ y ∈ S, AxLocus y ell := by
  apply le_antisymm
  · intro B hB
    simp only [Submodule.mem_iInf]
    intro y hy b hb
    exact hB y hy b hb
  · intro B hB y hy b hb
    simp only [Submodule.mem_iInf] at hB
    exact hB y hy b hb

/-- **CMP95's own `(1.10)` recovered as the `S := CoarseLattice L ell` instance** — "every `y ∈
T_L^{(1)}`", the unrestricted single-scale axial gauge condition, no `Λ'` restriction. Named
explicitly rather than left implicit, since the `(3.156)` subspace instead uses a restricted `S`. -/
abbrev cmp95AxLocus (L : PeriodicLatticeExtent) (ell : ℕ) : Submodule ℝ (Bond L → ℝ) :=
  AxUnionLocus (CoarseLattice L ell) ell

/-! ## §4. Non-vacuity — concrete `Ax(y)` on the witness lattice, and both a vanishing and a
non-vanishing field, so `AxLocus`/`AxUnionLocus` are genuinely PROPER subspaces -/

/-- **`Ax(witnessY)` computed out exactly** (block side `2` on the `4`-site-per-axis witness
lattice reused from `AdmissibleSubspace.lean`): the union, over the `7` nonzero-offset corners of
the `2×2×2` block, of their staircases. **Computed exactly (not guessed): `7 = ell^3 - 1` bonds**,
not `21 = 7×3` (the naive "each of `7` corners contributes up to `3` fresh bonds" upper bound) —
the staircase geometry forces massive sharing. Worked out by hand and cross-checked against the
kernel computation (`#eval` probe, this dispatch's scratch work): the `7` bonds split as
`1` "trunk" bond in direction `2` at `(0,0,0)` (shared by every `x` with `x_2 = 1`, regardless of
`x_0, x_1`), `2` "branch" bonds in direction `1` (at `(0,0,0)` and `(0,0,1)`, one per value the
already-switched coordinate `2` can take), and `4` "leaf" bonds in direction `0` (at `(0,x_1,x_2)`
for each of the `4` values `(x_1,x_2) ∈ {0,1}^2`) — `1 + 2 + 4 = 7`, a genuine spanning TREE of
the `8`-point block rooted at `y`, not a symmetric or redundant covering. Computed by `decide`
over the finite carrier, not asserted. -/
theorem witness_Ax_card : (Ax witnessY witnessEll).card = 7 := by decide

theorem witness_Ax_nonempty : (Ax witnessY witnessEll).Nonempty := by
  rw [← Finset.card_pos, witness_Ax_card]; decide

/-- The "trunk" bond of `Ax(witnessY)` named explicitly (type-ascribed to `Bond witnessL`, so the
membership rewrite below unifies syntactically through the `Bond` abbreviation rather than against
the raw product type Lean would otherwise infer for an anonymous pair literal). -/
def axWitnessTrunkBond : Bond witnessL := ((fun _ => (0 : Fin 4)), (2 : Fin 3))

/-- One concrete bond genuinely IN `Ax(witnessY)`: the trunk bond just named, obtained as
`staircasePath witnessY witnessX`'s first segment (base `witnessY` itself, direction `2`).
Reused directly from `AdmissibleSubspace.lean`'s own computed witness staircase. -/
theorem witnessBond0_mem_Ax : axWitnessTrunkBond ∈ Ax witnessY witnessEll := by
  rw [mem_Ax]
  exact ⟨witnessX, witnessX_mem_block, by decide, by rw [witness_staircasePath]; decide⟩

/-- **A field NOT vanishing on `Ax(witnessY)`**: the indicator of the bond just exhibited is a
genuine member of `Bond L → ℝ` failing `AxLocus`'s condition — `AxLocus witnessY witnessEll ≠ ⊤`. -/
theorem witness_AxLocus_ne_top : AxLocus witnessY witnessEll ≠ ⊤ := by
  intro htop
  have hmem : (fun _ : Bond witnessL => (1 : ℝ)) ∈ AxLocus witnessY witnessEll :=
    htop ▸ Submodule.mem_top
  have h0 := (mem_AxLocus).mp hmem _ witnessBond0_mem_Ax
  norm_num at h0

/-- **A nonzero field VANISHING on `Ax(witnessY)`**: the indicator of a bond genuinely outside the
`7`-bond set (reusing `AdmissibleSubspace.lean`'s `witnessOutsideBond`, `(2,2,2)` direction `0`,
which lies outside the `2×2×2` block entirely and so outside every staircase it could feed into) —
`AxLocus witnessY witnessEll ≠ ⊥`. -/
theorem witnessOutsideBond_not_mem_Ax :
    witnessOutsideBond ∉ Ax witnessY witnessEll := by decide

theorem witness_AxLocus_ne_bot : AxLocus witnessY witnessEll ≠ ⊥ := by
  intro hbot
  have hmem : (fun e => if e = witnessOutsideBond then (1 : ℝ) else 0) ∈
      AxLocus witnessY witnessEll := by
    rw [mem_AxLocus]
    intro b hb
    have hbne : b ≠ witnessOutsideBond := by
      rintro rfl; exact witnessOutsideBond_not_mem_Ax hb
    simp [hbne]
  rw [hbot, Submodule.mem_bot] at hmem
  have hcontra := congrFun hmem witnessOutsideBond
  simp at hcontra

/-- **The `S`-level (`AxUnionLocus`) properness, `S := {witnessY}`** — a genuine, non-degenerate
single-center instance of the general clause, transported directly from the `AxLocus` witnesses
via `axUnionLocus_eq_iInf`. -/
theorem witness_AxUnionLocus_ne_top : AxUnionLocus {witnessY} witnessEll ≠ ⊤ := by
  rw [axUnionLocus_eq_iInf]
  simp only [Finset.mem_singleton, iInf_iInf_eq_left]
  exact witness_AxLocus_ne_top

theorem witness_AxUnionLocus_ne_bot : AxUnionLocus {witnessY} witnessEll ≠ ⊥ := by
  rw [axUnionLocus_eq_iInf]
  simp only [Finset.mem_singleton, iInf_iInf_eq_left]
  exact witness_AxLocus_ne_bot

#print axioms mem_Ax
#print axioms axUnionLocus_eq_iInf
#print axioms witness_Ax_card
#print axioms witness_Ax_nonempty
#print axioms witness_AxLocus_ne_top
#print axioms witness_AxLocus_ne_bot
#print axioms witness_AxUnionLocus_ne_top
#print axioms witness_AxUnionLocus_ne_bot

/-! ## §5. Degeneracies — `ell = 1` (singleton blocks) and `y` at a periodic-extent corner

Both required by the dispatch. Genuinely different MECHANISMS producing the same conclusion
(`Ax y ell = ∅`), documented as such rather than conflated. -/

/-- **`ell = 1` closes the block to a single point.** `inBlock y 1 x` forces
`y_μ ≤ x_μ < y_μ + 1`, i.e. `x_μ = y_μ`, for every `μ` — so `blockOf y 1 = {y}` exactly, for ANY
`y`, general `L`. The elementary fact underlying the degeneracy below. -/
theorem blockOf_one (y : PeriodicLatticeSite L) : blockOf y 1 = {y} := by
  ext x
  rw [mem_blockOf, Finset.mem_singleton]
  constructor
  · intro hx
    funext μ
    apply Fin.ext
    have h1 := (hx μ).1
    have h2 := (hx μ).2
    omega
  · rintro rfl
    intro μ
    omega

/-- **`Ax(y)` at `ell = 1` is empty, in GENERAL (not merely on the witness).** With the block a
singleton `{y}`, erasing `y` itself leaves nothing to union staircases over — there is no `x ≠ y`
in the block, so no gauge condition to impose. This is the honest formal reading of the source's
own degenerate case (CMP96 p.223's prose explicitly "admits the case when some domains ... equal
`T_η`", i.e. degenerate block structure is inside the construction's own scope, not an artifact of
this Lean encoding — see the omega gate's Claim 1 finding, quoted in `AdmissibleSubspace.lean`). -/
theorem Ax_one (y : PeriodicLatticeSite L) : Ax y 1 = ∅ := by
  unfold Ax
  rw [blockOf_one, Finset.erase_singleton]
  simp

/-- Consequently the single-block clause imposes NO constraint at `ell = 1`: every field
vanishes on the empty bond set, vacuously — `AxLocus y 1 = ⊤`, proved (not merely observed) via
`Ax_one`. -/
theorem AxLocus_one (y : PeriodicLatticeSite L) : AxLocus y 1 = ⊤ := by
  ext B
  simp only [Submodule.mem_top, iff_true, mem_AxLocus, Ax_one]
  intro b hb
  exact absurd hb (Finset.notMem_empty b)

/-- **`y` at a periodic-extent corner — the SECOND, DIFFERENT degeneracy mechanism.** Reusing
`AdmissibleSubspace.lean`'s `boundaryCenter` (`(3,3,3)` on the `4`-site-per-axis witness lattice,
NOT a `CoarseLattice` member, and already proved there to have `(blockOf boundaryCenter
witnessEll).card = 1`, i.e. `blockOf boundaryCenter witnessEll = {boundaryCenter}` — the box
`[3,3+2)` is truncated by the periodic extent's hard `Fin 4` bound to the single point `3`, not
wrapped). Since the block again collapses to the singleton `{boundaryCenter}`, `Ax(boundaryCenter)`
is empty for EXACTLY the same set-theoretic reason as `ell = 1` (erasing the center from a
singleton block leaves nothing) but the CAUSE is boundary truncation of `blockOf`, not a small
`ell` — `ell = witnessEll = 2` here, genuinely `> 1`. -/
theorem boundaryCenter_blockOf_eq_singleton :
    blockOf boundaryCenter witnessEll = {boundaryCenter} := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [mem_blockOf] at hx
    rw [Finset.mem_singleton]
    funext μ
    apply Fin.ext
    have h1 := (hx μ).1
    have h2 := (hx μ).2
    have hb : (boundaryCenter μ).val = 3 := rfl
    have hL : witnessL μ = 3 := rfl
    have hxlt := (x μ).isLt
    omega
  · rw [boundaryCenter_blockOf_card, Finset.card_singleton]

theorem Ax_boundaryCenter_eq_empty : Ax boundaryCenter witnessEll = ∅ := by
  unfold Ax
  rw [boundaryCenter_blockOf_eq_singleton, Finset.erase_singleton]
  simp

theorem AxLocus_boundaryCenter_eq_top : AxLocus boundaryCenter witnessEll = ⊤ := by
  ext B
  simp only [Submodule.mem_top, iff_true, mem_AxLocus, Ax_boundaryCenter_eq_empty]
  intro b hb
  exact absurd hb (Finset.notMem_empty b)

/-- **Mutation control (S82-style): the emptiness is NOT a tautology of the construction — it
genuinely depends on `ell`/the center.** At `ell = witnessEll = 2` and `y = witnessY` (an ALIGNED,
non-corner center), `Ax y ell` is the `7`-element set of `§4`, not empty. So `Ax_one` and
`Ax_boundaryCenter_eq_empty` are reporting a real degeneracy of THEIR specific inputs, not a bug
that empties `Ax` unconditionally — exhibited by directly contrasting cardinalities `0 ≠ 7`. -/
theorem Ax_degenerate_ne_generic :
    (Ax boundaryCenter witnessEll).card ≠ (Ax witnessY witnessEll).card := by
  rw [Ax_boundaryCenter_eq_empty, witness_Ax_card]
  simp

#print axioms blockOf_one
#print axioms Ax_one
#print axioms AxLocus_one
#print axioms boundaryCenter_blockOf_eq_singleton
#print axioms Ax_boundaryCenter_eq_empty
#print axioms AxLocus_boundaryCenter_eq_top
#print axioms Ax_degenerate_ne_generic

end AdalyFormal.Balaban.AxialContour
