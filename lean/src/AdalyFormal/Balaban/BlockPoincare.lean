/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CoarseCurl
import AdalyFormal.Balaban.PoincareBridge
import AdalyFormal.Migration.BlockPoincare

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# CMP96 `(2.123)` — the per-block Poincaré, concretely, on the FINE `Bond`/`PeriodicLatticePlaquette`
geometry (U=1 real-valued sector)

## Source pin (LAW-11: rendered page, read directly, not the OCR text layer)

`compute/denotation_audit/CMP96_p244_render.png` (`pdftoppm -r 300` on
`balaban_CMP96_1984_propagators_II.pdf`, offset 222, printed p.244; SAME byte-identical render
`AdmissibleSubspace.lean`'s own R2 pass pinned, sha256
`07ab9fee8e3858b252fb3a1a51c6d17457aa1c5b93b1358d05234acef310688c`). The target display,
**(2.123)**:

> `Σ_{b⊂B(y)} |B(b)|² ≦ dL^d Σ_{p⊂B(y)} |(∂₁B)(p)|²`

for `B` satisfying **(2.121)** (`B(b)=0` for `b⊂Γ_{y,x}`, `x∈B(y)`, `y∈Λ'`), proved on the page by
an elementary staircase telescoping (through the FIRST `j-1` coordinates of a bond's direction-`j`
displacement) followed by Cauchy-Schwarz, then summed over bonds/directions with the worst-case
count `(d-1)(L-1)²L^{d-2}` for the last direction, giving the combined constant `dL^d`.

## What this file is, precisely

This is the CONCRETE, `d=3` (`Fin 3`, this tree's own ambient dimension throughout
`AdmissibleSubspace`/`LatticeOperators`) instantiation of the residuals
`[RES-SPINE-TH2-TELESCOPE]`/`[RES-SPINE-TH2-COUNT]` (`Spine.lean` §"Theorem 2", named against
`Migration/BlockPoincare.lean`'s abstract `block_poincare_core_indexed`) — for the U=1 (real-valued,
abelian) sector specifically, where `Migration/BlockPoincare.lean` §1.5 item 2's missing
`SU(2)`-adjoint-isometry ingredient is NOT needed at all: `B : Bond L → ℝ` is already real-valued,
so the telescoping identity's "triangle inequality" step is the ordinary real one
(`|Σxᵢ| ≤ Σ|xᵢ|`), with no group action to control. What genuinely remains missing and is built here
is `[RES-SPINE-TH2-TELESCOPE]`'s OTHER half — "fine bonds/plaquettes inside one block and a
tree-bond classification, which `Balaban/Blocks.lean` does NOT supply" — using this tree's ALREADY-
BUILT concrete objects instead (`AdmissibleSubspace.blockOf`/`staircasePath`/`CoarseLattice`,
`LatticeOperators.curlValue`/`Bond`, `Target.ClayStatement.PeriodicLatticePlaquette`), plus
`[RES-SPINE-TH2-COUNT]`, the concrete `K·M ≤ d·L^d` counting fact for this geometry.

## Status, disclosed precisely (do not oversell)

* **§1 (`bondInBlock`/`plaqInBlock`) — the concrete "fine bonds/plaquettes inside one block" data
  `Migration/BlockPoincare.lean` §1.5 item 1 names as missing.**
* **§2 (the direction-`0` triviality lemma `dir0_bond_eq_zero` and the reusable
  `noWrap_of_bondInBlock` helper) — PROVED, sorry-free, general in `y`.** A genuinely new fact not
  otherwise in this tree: EVERY direction-`0` (Lean 0-index; CMP96's own `e_1`) bond with both
  endpoints in a block is forced to `0` by `(2.121)` DIRECTLY (no telescoping needed) — the reason
  the page's own sum only ever discusses directions `2,…,d`.
* **§3 (`z0`/`zK`, `z0_bond1_eq_zero`, `dir1_step_eq_curl`, `dir1_bondSq_le`) — PROVED, sorry-free,
  in FULL GENERALITY (no separate boundary case needed).** The page's own displayed per-bond bound
  `|B(x,x+e_2)|² ≤ |x_1-y_1|·Σ|(∂₁B)(p(x'))|²`, faithfully reproduced as
  `(B b)² ≤ (ell-1)·Σ_{k<n} (curlValue B (zK y x k,(0,1)))²` for `n = x_0-y_0`. **Correction to an
  earlier working hypothesis this docstring carried**: the boundary case ("`x`'s coordinate `1` at
  the very top of the block") does NOT need an adjacent-block admissibility instance — `bondInBlock
  b`'s OWN hypothesis (both endpoints of `b` in the SAME block) already forces every auxiliary bond
  the telescoping touches to stay strictly inside `blockOf y ell`, so a single `y` suffices
  throughout. `nextBlock_mem_coarseLattice` is kept (harmless, general, and reusable) even though
  §3 turned out not to need it.
* **§4 (direction-`2` telescoping) — [SUPERSEDED: now BUILT, sorry-free]** as `dir2_bondSq_le` /
  `dir2_bond_eq_sum` (walks A `zK` + B `wK`, path length `≤ 2(ell-1)`). ~~NOT ATTEMPTED, named
  precisely.~~ (Original note retained below for the recipe, but the lemma now exists.) CMP96's own
  "general `j`" formula (p.244, above (2.123)) telescopes a direction-`2` (Lean; CMP96's `e_3`) bond
  through BOTH
  preceding coordinates `0` and `1` (path length ≤ `2(ell-1)`, not `ell-1`) — the SAME construction
  as §3 (walk one coordinate to `y`'s value, invoke §2's triviality lemma to cancel the curl's
  cross-terms, telescope, Cauchy-Schwarz), but with TWO nested walks instead of one, hence a
  genuinely bigger (not harder in kind) proof. `zK`/`z0` generalize readily to a
  `zKK y x k1 k2`-shaped two-coordinate walk; the per-bond bound would read
  `(B b)² ≤ (2(ell-1))·Σ|(curlValue in the (0,2) or (1,2) plane)|²` depending on which of the two
  preceding coordinates the last step crosses. Not attempted for time; the recipe above is the exact
  missing lemma, not a vague pointer.
* **§5/§6, the AGGREGATION — [SUPERSEDED: now CLOSED, sorry-free, as `block_poincare` in §6].**
  `Σ_{b⊂B(y)}|B(b)|² ≤ 3·ell³·Σ_{p⊂B(y)}|(∂₁B)(p)|²`, `[RES-SPINE-TH2-COUNT]`, is proved by
  instantiating `Migration.BlockPoincare.block_poincare_core'` on this lattice with `K = 2·ell`,
  `M = ell²`, `hK`/`hM`/`hTri` all discharged (see §6). **CORRECTION to this note's earlier count**:
  the honest multiplicity bound is `M ≤ ell²`, NOT ~~`M ≤ ell-1`~~ — the earlier `ell-1` was FALSE
  for `(1,2)`-plane plaquettes, since `wK y x k` does not depend on `x_0`/`x_1`, so up to `ell·(ell-1)`
  distinct dir-`2` bonds share ONE `(1,2)`-plaquette; the injection `b ↦ (b.1 0, b.1 1)` gives the
  correct `M ≤ ell²` (coord-`2`/direction recovered from `p` via `steps_recover`). `K·M ≤ 2·ell³ ≤
  3·ell³` (`blockPoincareConst_bound`). The full plaquette subtype was NOT needed — indicator-form
  `bAbs`/`pAbs` over the full `Bond L`/`PeriodicLatticePlaquette L` Fintypes make the full-type sum
  equal the block sum, avoiding subtype packaging. The abstract-`∀y` `block_poincare_core_indexed`
  interface does NOT fit (no per-`y` side conditions); the single-block `block_poincare_core'` does.
* **§6 — the composition toward `(2.122)`/`coerc_u_main`'s three-term bound is NOT built here**
  (out of scope for this file — a separate, harder step needing (2.127) too, per
  `CMP96Lemma24Farkas.lean`'s own scope note). Stated, not proved: once §4/§5 close (2.123) itself
  (`Σ_{b⊂B(y)}|B(b)|² ≤ 3ell³·Σ_{p⊂B(y)}|(∂₁B)(p)|²`, summed over `y ∈ CoarseLattice L ell`), the
  NEXT step toward `(2.122)`'s `γ₀''‖B‖²` lower bound is CMP96's OWN move immediately after
  (2.123), printed p.245: combine (2.123) with the grade-3 curl-relative bound
  `U1CurlCoercivity.lean`'s `γ₀‖∂₁'B‖² ≤ ⟨B,Δ_jB⟩` is a DIFFERENT (coarse-curl) quantity, not the
  fine `Σ_p|(∂₁B)(p)|²` (2.123) bounds — the two must be reconciled via `LatticeOperators.
  coarseRestrict`'s own averaging before they compose, which `CoarseCurl.lean` §6 already proves
  does NOT commute cleanly with the fine curl (`coarseCurl_coarseRestrict_ne_coarsePlaquetteRestrict
  _curl_witness`). So the honest composition path is: (2.123) [this file, partial] + (2.127)
  [CMP96Lemma24Farkas.lean's own opaque-real Farkas step, ALSO not yet derived from a genuine `B`]
  ⟹ Lemma 2.4/(2.128)'s `L^{d-2}Σ_c|(Q₁B)(c)|² + Σ_p|(∂₁B)(p)|² ≥ (1/(12d²))L^{-d-1}‖B‖²` — a
  DIFFERENT bound from (2.122)'s `γ₀''‖B‖²` target, using `Q₁B` (coarse-restricted `B`) rather than
  `∂₁'B` (coarse curl of coarse-restricted `B`). Composing THIS chain toward `coerc_u_main.coercive`
  therefore still needs the missing link the `PoincareRangeC.lean` §4 residual already names
  (a genuine Poincaré/spectral-gap inequality on `CoarseBondSpace`) — (2.123) is one necessary
  ingredient of that chain, not a bypass of it.
-/

namespace AdalyFormal.Balaban.BlockPoincare

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators

variable {L : PeriodicLatticeExtent}

/-! ## §1. `bondInBlock`/`plaqInBlock` — the fine bond/plaquette geometry `Blocks.lean` lacks
(`Migration/BlockPoincare.lean` §1.5 item 1, closed for this concrete lattice) -/

/-- **A fine bond, entirely contained in the block `B(y)`**: both endpoints (base site and its
forward shift) lie in `blockOf y ell`. -/
abbrev bondInBlock (y : PeriodicLatticeSite L) (ell : ℕ) (b : Bond L) : Prop :=
  b.1 ∈ blockOf y ell ∧ periodicLatticeShift b.1 b.2 ∈ blockOf y ell

/-- The `Finset` of bonds contained in `B(y)` — `{b ⊂ B(y)}`, CMP96 (2.123)'s own summation set. -/
def bondsInBlock (y : PeriodicLatticeSite L) (ell : ℕ) : Finset (Bond L) :=
  Finset.univ.filter (bondInBlock y ell)

theorem mem_bondsInBlock {y : PeriodicLatticeSite L} {ell : ℕ} {b : Bond L} :
    b ∈ bondsInBlock y ell ↔ bondInBlock y ell b := by
  simp [bondsInBlock]

/-- **A fine plaquette, entirely contained in the block `B(y)`**: all four corners lie in
`blockOf y ell`. Matches the four sites `curlValue` actually reads
(`p.1`, `shift_μ p.1`, `shift_ν p.1`, `shift_μ(shift_ν p.1)`). -/
abbrev plaqInBlock (y : PeriodicLatticeSite L) (ell : ℕ) (p : PeriodicLatticePlaquette L) : Prop :=
  p.1 ∈ blockOf y ell ∧
  periodicLatticeShift p.1 p.2.1.1 ∈ blockOf y ell ∧
  periodicLatticeShift p.1 p.2.1.2 ∈ blockOf y ell ∧
  periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ blockOf y ell

/-- The `Finset` of plaquettes contained in `B(y)` — `{p ⊂ B(y)}`. -/
def plaqsInBlock (y : PeriodicLatticeSite L) (ell : ℕ) : Finset (PeriodicLatticePlaquette L) :=
  Finset.univ.filter (plaqInBlock y ell)

theorem mem_plaqsInBlock {y : PeriodicLatticeSite L} {ell : ℕ} {p : PeriodicLatticePlaquette L} :
    p ∈ plaqsInBlock y ell ↔ plaqInBlock y ell p := by
  simp [plaqsInBlock]

/-! ## §2. THE DIRECTION-`0` TRIVIALITY LEMMA — every direction-`0` (Lean; CMP96's `e_1`) bond in
a block is forced to `0` by `(2.121)` DIRECTLY, no telescoping needed.

This is exactly why the source's own sum (displayed on p.244, immediately below (2.122)) only ever
discusses directions `2,…,d`: direction `1`'s bonds contribute IDENTICALLY ZERO, not merely a
bounded amount.

**hstrict is genuinely needed and disclosed**: without SOME hypothesis excluding the degenerate
"single block wraps into itself" case (`ell = L μ + 1`, `y μ = 0`), a bond's forward shift can
WRAP AROUND the torus back to `y`'s own corner, and the staircase segment used to force it to zero
becomes empty. `hstrict : ∀ μ, ell < L μ + 1` (more than one block per axis — Bałaban's own
RG-hierarchy regime, `ell ≪ L`) rules this out; a genuinely single-block lattice is outside CMP96's
own intended use of `(2.123)` (the whole point of the lemma is comparing a fine block to its coarser
neighbours). -/

/-- Every `CoarseLattice` member's forward shift (in ANY one direction) is again a `CoarseLattice`
member, using ONLY the tileability hypothesis already required elsewhere in this tree — this is
`CoarseCurl.coarseShift_mem_coarseLattice` specialized to a SINGLE fine step composed `ell` times
starting one step in; concretely it is the `y'' := y + ell•e_μ` "next block over" construction,
built directly here (not via `coarseShift`, which iterates a DIFFERENT number of times) via the
`ell`-fold-shift fact `AdmissibleSubspace.coarseShift_mem_coarseLattice` already supplies verbatim. -/
theorem nextBlock_mem_coarseLattice {L : PeriodicLatticeExtent} {ell : ℕ}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    AdalyFormal.Balaban.CoarseCurl.coarseShift y ell μ ∈ CoarseLattice L ell :=
  AdalyFormal.Balaban.CoarseCurl.coarseShift_mem_coarseLattice hdvd hy μ

/-- The forward shift by one step in direction `μ` never changes any OTHER coordinate — the single
elementary fact `dir0_bond_eq_zero`'s coordinate bookkeeping rests on. -/
theorem periodicLatticeShift_coord_ne {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    {μ ν : Fin 3} (hν : ν ≠ μ) : (periodicLatticeShift x μ) ν = x ν :=
  Function.update_of_ne hν _ _

/-- **THE GENERAL NO-WRAP LEMMA.** Whenever a bond `(x,μ)` has BOTH endpoints inside the SAME
block `blockOf y ell`, its forward step never wraps around the periodic torus — PROVIDED `ell < L
μ + 1` (more than one block along axis `μ`, `hstrict`). Reusable across every direction's own
telescoping construction (this file's own general form of the wraparound-exclusion argument
`dir0_bond_eq_zero` uses internally, factored out once here rather than re-derived per direction). -/
theorem noWrap_of_bondInBlock {L : PeriodicLatticeExtent} {ell : ℕ} {μ : Fin 3}
    (hstrict : ell < L μ + 1) {y x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell)
    (hshift : periodicLatticeShift x μ ∈ blockOf y ell) : (x μ).val + 1 < L μ + 1 := by
  by_contra hcon
  push_neg at hcon
  have hxtop : (x μ).val = L μ := by have := (x μ).isLt; omega
  have hxge : (y μ).val ≤ (x μ).val := (mem_blockOf.mp hx) μ |>.1
  rcases Nat.eq_zero_or_pos (L μ) with hLmu | hLmu
  · -- degenerate one-point axis: `hstrict : ell < L μ + 1 = 1`, so `ell = 0`, contradicting
    -- `x`'s own membership bound `(x μ).val < (y μ).val + ell` at `(x μ).val = L μ = 0`.
    have hxlt : (x μ).val < (y μ).val + ell := (mem_blockOf.mp hx) μ |>.2
    omega
  · have hv1 : (1 : Fin (L μ + 1)).val = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    have hva : (x μ + (1 : Fin (L μ + 1))).val
        = if L μ + 1 ≤ (x μ).val + (1 : Fin (L μ + 1)).val
          then (x μ).val + (1 : Fin (L μ + 1)).val - (L μ + 1)
          else (x μ).val + (1 : Fin (L μ + 1)).val := Fin.val_add_eq_ite _ _
    rw [hv1] at hva
    have hshiftval : (periodicLatticeShift x μ) μ = x μ + 1 := Function.update_self _ _ _
    have hwrap : ((periodicLatticeShift x μ) μ).val = 0 := by
      rw [hshiftval, hva, if_pos (by omega)]
      omega
    have hshiftge : (y μ).val ≤ ((periodicLatticeShift x μ) μ).val :=
      (mem_blockOf.mp hshift) μ |>.1
    rw [hwrap] at hshiftge
    have hy0 : (y μ).val = 0 := le_antisymm hshiftge (Nat.zero_le _)
    have hxlt : (x μ).val < (y μ).val + ell := (mem_blockOf.mp hx) μ |>.2
    omega

#print axioms noWrap_of_bondInBlock

/-- **The direction-`0` triviality lemma.** For `B` admissible for EVERY block simultaneously
(`admissibleSubspaceInter`), every direction-`0` bond with both endpoints in `blockOf y ell`
vanishes. Proved by exhibiting `b` as the LAST segment of `staircasePath y x'` for
`x' := periodicLatticeShift b.1 0` (which lies in `blockOf y ell` by hypothesis). `hstrict`
(`ell < L 0 + 1`, more than one block along axis `0`) rules out the degenerate wraparound case where
`x'`'s forward shift would land back at `y`'s own corner. -/
theorem dir0_bond_eq_zero {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict : ell < L 0 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (b : Bond L) (hb2 : b.2 = 0) (hbb : bondInBlock y ell b) :
    B b = 0 := by
  obtain ⟨hb1, hb1'⟩ := hbb
  set x' := periodicLatticeShift b.1 (0 : Fin 3) with hx'_def
  have hx'mem : x' ∈ blockOf y ell := by rw [hx'_def, ← hb2]; exact hb1'
  have hb1lt : (b.1 0).val < (y 0).val + ell := (mem_blockOf.mp hb1) 0 |>.2
  have hb1ge : (y 0).val ≤ (b.1 0).val := (mem_blockOf.mp hb1) 0 |>.1
  have hx'0lt : (x' 0).val < (y 0).val + ell := (mem_blockOf.mp hx'mem) 0 |>.2
  have hx'0ge : (y 0).val ≤ (x' 0).val := (mem_blockOf.mp hx'mem) 0 |>.1
  -- The single elementary Fin-arithmetic fact everything below rests on: `x' 0`'s value is EITHER
  -- `(b.1 0).val + 1` (no wrap) OR `0` (wraps, only when `(b.1 0).val = L 0` exactly). `L 0 = 0`
  -- is handled separately (degenerate one-point axis: `x' 0`'s bound alone forces `.val = 0`),
  -- since `omega` cannot reason about `%`/`Fin.val_add` when the modulus `L 0 + 1` is a variable —
  -- splitting on `L 0 = 0` turns `(1 : Fin (L 0 + 1)).val` into a LITERAL `0` or `1`, which it can.
  have hx'eq : x' 0 = b.1 0 + 1 := by rw [hx'_def]; exact Function.update_self _ _ _
  rcases Nat.eq_zero_or_pos (L 0) with hL0 | hL0
  · -- degenerate one-point axis: every `Fin (L 0 + 1) = Fin 1` value has `.val = 0`.
    have hx'wrap : (x' 0).val = 0 := by have := (x' 0).isLt; omega
    rw [hx'wrap] at hx'0ge
    have hy0 : (y 0).val = 0 := le_antisymm hx'0ge (Nat.zero_le _)
    have hb1v0 : (b.1 0).val = 0 := by have := (b.1 0).isLt; omega
    rw [hy0] at hb1lt
    -- `hstrict : ell < L 0 + 1 = 1`, i.e. `ell = 0`; then `hb1lt : (b.1 0).val < 0 + 0`, absurd.
    have hell0 : ell = 0 := by omega
    omega
  · have hv1 : (1 : Fin (L 0 + 1)).val = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    have hva : (b.1 0 + (1 : Fin (L 0 + 1))).val
        = if L 0 + 1 ≤ (b.1 0).val + (1 : Fin (L 0 + 1)).val
          then (b.1 0).val + (1 : Fin (L 0 + 1)).val - (L 0 + 1)
          else (b.1 0).val + (1 : Fin (L 0 + 1)).val := Fin.val_add_eq_ite _ _
    rw [hv1] at hva
    have hx'val : (x' 0).val
        = if L 0 + 1 ≤ (b.1 0).val + 1 then (b.1 0).val + 1 - (L 0 + 1) else (b.1 0).val + 1 := by
      rw [hx'eq]; exact hva
    have hnowrap : (b.1 0).val + 1 < L 0 + 1 := by
      by_contra hcon
      push_neg at hcon
      have hx'wrap : (x' 0).val = 0 := by
        rw [hx'val, if_pos (by omega : L 0 + 1 ≤ (b.1 0).val + 1)]
        have := (b.1 0).isLt
        omega
      rw [hx'wrap] at hx'0ge
      have hy0 : (y 0).val = 0 := le_antisymm hx'0ge (Nat.zero_le _)
      rw [hy0] at hb1lt
      omega
    have hshiftval : (x' 0).val = (b.1 0).val + 1 := by
      rw [hx'val, if_neg (by omega : ¬ L 0 + 1 ≤ (b.1 0).val + 1)]
    have hx'ν : ∀ ν : Fin 3, ν ≠ 0 → x' ν = b.1 ν := fun ν hν =>
      periodicLatticeShift_coord_ne b.1 hν
    have hstair : b ∈ staircasePath y x' := by
      unfold staircasePath
      apply Finset.mem_union_right
      rw [mem_axisSegment]
      refine ⟨hb2, ?_, ?_, ?_⟩
      · intro ν hν
        have hval2 : ν.val = 1 ∨ ν.val = 2 := by
          have h0 : ν.val ≠ 0 := fun h => hν (Fin.ext h)
          have := ν.isLt
          omega
        rcases hval2 with h1 | h2
        · have hνeq : ν = 1 := Fin.ext h1
          subst hνeq
          show (corner2 y x') 1 = b.1 1
          unfold corner2
          rw [Function.update_self]
          exact (hx'ν 1 (by decide)).symm
        · have hνeq : ν = 2 := Fin.ext h2
          subst hνeq
          show (corner2 y x') 2 = b.1 2
          unfold corner2 corner1
          rw [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1), Function.update_self]
          exact (hx'ν 2 (by decide)).symm
      · have hx'gt : (y 0).val < (x' 0).val := by omega
        have hminy : min (y 0).val (x' 0).val = (y 0).val := min_eq_left (le_of_lt hx'gt)
        rw [hminy]; exact hb1ge
      · have hx'gt : (y 0).val < (x' 0).val := by omega
        have hmaxy : max (y 0).val (x' 0).val = (x' 0).val := max_eq_right (le_of_lt hx'gt)
        rw [hmaxy]; omega
    exact (mem_admissibleSubspaceInter.mp hB) y hy x' hx'mem b hstair

#print axioms dir0_bond_eq_zero

/-! ## §3. THE DIRECTION-`1` (Lean; CMP96's `e_2`) TELESCOPING BOUND — the page's own worked
example, p.244: `|B(x,x+e_2)|² ≤ |x_1-y_1| Σ|(∂₁B)(p(x'))|²`, PROVED for THIS concrete geometry.

The construction: for `b = (x,1) ∈ bondsInBlock y ell`, walk `x`'s coordinate `0` DOWN to `y`'s own
value one fine step at a time (`zK y x k`, `k = 0,…,n`, `n := x_0 - y_0`), landing on `x` at `k = n`
and on `z₀ := (y_0,x_1,x_2)` at `k=0`. `z₀`'s own direction-`1` bond is forced to `0` DIRECTLY by
`(2.121)` (a single admissibility application, no telescoping); each step
`B(zK(k+1),1) - B(zK(k),1)` equals `curlValue B (zK(k),⟨0,1⟩)` EXACTLY, because the curl's other two
terms — direction-`0` bonds at `zK(k)` and at `shift₁(zK(k))` — both vanish by §2's
`dir0_bond_eq_zero` (both stay inside `blockOf y ell`, using `bondInBlock b`'s OWN hypothesis, not
an adjacent block — the boundary case that would need an adjacent block is excluded ALREADY by `b`
having both endpoints in the block). Summing the telescoping identity and applying Cauchy-Schwarz
(`sq_sum_le_card_mul_sum_sq`) gives the bound. -/

/-- `z₀` — `x` with coordinate `0` reset to `y`'s value; the starting corner of the walk. -/
def z0 (y x : PeriodicLatticeSite L) : PeriodicLatticeSite L := Function.update x 0 (y 0)

theorem z0_coord0 (y x : PeriodicLatticeSite L) : (z0 y x) 0 = y 0 := Function.update_self _ _ _

theorem z0_coord_ne (y x : PeriodicLatticeSite L) {ν : Fin 3} (hν : ν ≠ 0) :
    (z0 y x) ν = x ν := Function.update_of_ne hν _ _

/-- The walk itself: `x`'s coordinate `0` shifted `k` fine steps forward from `y`'s value — the
`k`-fold iterate of the fine shift, reusing `CoarseCurl.coarseShift` verbatim (LAW-19: it is
already exactly `(fun z ↦ periodicLatticeShift z μ)^[k] z0`, with the iteration count a free `ℕ`
parameter, not tied to the block side). -/
def zK (y x : PeriodicLatticeSite L) (k : ℕ) : PeriodicLatticeSite L :=
  AdalyFormal.Balaban.CoarseCurl.coarseShift (z0 y x) k 0

theorem zK_zero (y x : PeriodicLatticeSite L) : zK y x 0 = z0 y x := by
  unfold zK AdalyFormal.Balaban.CoarseCurl.coarseShift
  exact Function.iterate_zero_apply _ _

theorem zK_succ (y x : PeriodicLatticeSite L) (k : ℕ) :
    zK y x (k + 1) = periodicLatticeShift (zK y x k) 0 := by
  unfold zK AdalyFormal.Balaban.CoarseCurl.coarseShift
  exact Function.iterate_succ_apply' _ _ _

theorem zK_coord0 (y x : PeriodicLatticeSite L) (k : ℕ) :
    (zK y x k 0).val = ((y 0).val + k) % (L 0 + 1) := by
  have h := AdalyFormal.Balaban.CoarseCurl.coarseShift_val_eq (z0 y x) k 0
  rw [z0_coord0] at h
  exact h

theorem zK_coord_ne (y x : PeriodicLatticeSite L) (k : ℕ) {ν : Fin 3} (hν : ν ≠ 0) :
    (zK y x k) ν = x ν := by
  have h := AdalyFormal.Balaban.CoarseCurl.coarseShift_apply_ne (z0 y x) k 0 ν hν
  rw [z0_coord_ne y x hν] at h
  exact h

/-- **The walk closes at `x` when `k = n := x_0 - y_0`** (Nat subtraction, safe since `x_0 ≥ y_0`
inside a block). -/
theorem zK_walkLength (y x : PeriodicLatticeSite L) (hge : (y 0).val ≤ (x 0).val)
    (hlt : (x 0).val < L 0 + 1) : zK y x ((x 0).val - (y 0).val) = x := by
  funext ν
  by_cases hν : ν = 0
  · subst hν
    apply Fin.ext
    rw [zK_coord0]
    have : (y 0).val + ((x 0).val - (y 0).val) = (x 0).val := by omega
    rw [this, Nat.mod_eq_of_lt hlt]
  · rw [zK_coord_ne y x _ hν]

/-- **`zK`'s coordinate `0` is EXACTLY `y_0 + k` (no wraparound), for any `k` not exceeding the
walk's own total length `x_0 - y_0`.** The precise, non-modular value the membership lemmas below
need. -/
theorem zK_coord0_eq_of_le (y x : PeriodicLatticeSite L) {k : ℕ}
    (hk : k ≤ (x 0).val - (y 0).val) (hxlt : (x 0).val < L 0 + 1) :
    (zK y x k 0).val = (y 0).val + k := by
  rw [zK_coord0]
  exact Nat.mod_eq_of_lt (by omega)

/-- **The base case: `z₀`'s own direction-`1` bond is forced to `0` DIRECTLY** — a single
admissibility application at `x''' := shift₁(x)` (NOT `shift₁(z₀)`: the staircase's middle
segment, based at `corner1 y x'''`, has coordinate `0` FIXED AT `y`'s value regardless of `x'''`,
matching `z₀`'s own coordinate-`0` value automatically). Uses `bondInBlock b`'s own hypothesis
(`shift₁(x) ∈ blockOf y ell`) directly as the membership witness for `x'''`. -/
theorem z0_bond1_eq_zero {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict1 : ell < L 1 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift1 : periodicLatticeShift x 1 ∈ blockOf y ell) :
    B (z0 y x, (1 : Fin 3)) = 0 := by
  set x''' := periodicLatticeShift x (1 : Fin 3) with hx'''_def
  have hnowrap : (x 1).val + 1 < L 1 + 1 := noWrap_of_bondInBlock hstrict1 hx hshift1
  have hx'''1 : (x''' 1).val = (x 1).val + 1 :=
    AdalyFormal.Balaban.PoincareBridge.shift_val_self x 1 hnowrap
  have hx'''2 : x''' 2 = x 2 := periodicLatticeShift_coord_ne x (by decide)
  have hx1ge : (y 1).val ≤ (x 1).val := (mem_blockOf.mp hx) 1 |>.1
  have hstair : (z0 y x, (1 : Fin 3)) ∈ staircasePath y x''' := by
    unfold staircasePath
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [mem_axisSegment]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro ν hν
      by_cases hν0 : ν = 0
      · subst hν0
        show (z0 y x) 0 = (corner1 y x''') 0
        rw [z0_coord0]
        unfold corner1
        exact (Function.update_of_ne (by decide) _ _).symm
      · have hν2 : ν = 2 := by
          have := ν.isLt
          have h0 : ν.val ≠ 0 := fun h => hν0 (Fin.ext h)
          have h1 : ν.val ≠ 1 := fun h => hν (Fin.ext h)
          apply Fin.ext; omega
        subst hν2
        show (z0 y x) 2 = (corner1 y x''') 2
        rw [z0_coord_ne y x (by decide)]
        unfold corner1
        rw [Function.update_self, hx'''2]
    · show min (y 1).val (x''' 1).val ≤ ((z0 y x) 1).val
      rw [z0_coord_ne y x (by decide)]
      have hmin : min (y 1).val (x''' 1).val = (y 1).val := by
        apply min_eq_left; omega
      rw [hmin]; exact hx1ge
    · show ((z0 y x) 1).val < max (y 1).val (x''' 1).val
      rw [z0_coord_ne y x (by decide)]
      have hmax : max (y 1).val (x''' 1).val = (x''' 1).val := by
        apply max_eq_right; omega
      rw [hmax]; omega
  exact (mem_admissibleSubspaceInter.mp hB) y hy x''' hshift1 (z0 y x, 1) hstair

#print axioms z0_bond1_eq_zero

/-! ## §3b. The telescoping step and the assembled per-bond bound -/

/-- `zK y x k` lies in the block, for every `k` up to the walk's own length. -/
theorem zK_mem_blockOf {L : PeriodicLatticeExtent} {ell : ℕ} (y x : PeriodicLatticeSite L)
    (hx : x ∈ blockOf y ell) {k : ℕ} (hk : k ≤ (x 0).val - (y 0).val) :
    zK y x k ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    have hxge := (mem_blockOf.mp hx) 0 |>.1
    have hxlt := (mem_blockOf.mp hx) 0 |>.2
    have hxisLt := (x 0).isLt
    have hval := zK_coord0_eq_of_le y x hk (by omega)
    rw [hval]
    exact ⟨by omega, by omega⟩
  · rw [zK_coord_ne y x k hμ]
    exact mem_blockOf.mp hx μ

/-- `shift₁(zK y x k)` lies in the block, for every `k` up to the walk's own length — coordinate
`1` computed via `noWrap_of_bondInBlock`/`shift_val_self` at `x` itself (`zK`'s own coordinate `1`
equals `x`'s). -/
theorem shift1_zK_mem_blockOf {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict1 : ell < L 1 + 1)
    (y x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift1 : periodicLatticeShift x 1 ∈ blockOf y ell) {k : ℕ}
    (hk : k ≤ (x 0).val - (y 0).val) :
    periodicLatticeShift (zK y x k) 1 ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro μ
  by_cases hμ : μ = 1
  · subst hμ
    have hzk1 : zK y x k 1 = x 1 := zK_coord_ne y x k (by decide)
    have hnowrap : (x 1).val + 1 < L 1 + 1 := noWrap_of_bondInBlock hstrict1 hx hshift1
    have hnowrap' : (zK y x k 1).val + 1 < L 1 + 1 := by rw [hzk1]; exact hnowrap
    have hval : ((periodicLatticeShift (zK y x k) 1) 1).val = (zK y x k 1).val + 1 :=
      AdalyFormal.Balaban.PoincareBridge.shift_val_self (zK y x k) 1 hnowrap'
    have hshiftval : ((periodicLatticeShift x (1 : Fin 3)) 1).val = (x 1).val + 1 :=
      AdalyFormal.Balaban.PoincareBridge.shift_val_self x 1 hnowrap
    have hmemx1 := mem_blockOf.mp hshift1 1
    rw [hshiftval] at hmemx1
    rw [hval, hzk1]
    exact hmemx1
  · by_cases hμ0 : μ = 0
    · subst hμ0
      rw [periodicLatticeShift_coord_ne (zK y x k) (by decide : (0 : Fin 3) ≠ 1)]
      exact mem_blockOf.mp (zK_mem_blockOf y x hx hk) 0
    · have hμ2 : μ = 2 := by
        have := μ.isLt
        have h0 : μ.val ≠ 0 := fun h => hμ0 (Fin.ext h)
        have h1 : μ.val ≠ 1 := fun h => hμ (Fin.ext h)
        apply Fin.ext; omega
      subst hμ2
      rw [periodicLatticeShift_coord_ne (zK y x k) (by decide : (2 : Fin 3) ≠ 1)]
      exact mem_blockOf.mp (zK_mem_blockOf y x hx hk) 2

/-- `shift₀(shift₁(zK y x k))` lies in the block, for `k` STRICTLY below the walk's own length
(the two-step-forward point). -/
theorem shift0_shift1_zK_mem_blockOf {L : PeriodicLatticeExtent} {ell : ℕ}
    (hstrict1 : ell < L 1 + 1) (y x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift1 : periodicLatticeShift x 1 ∈ blockOf y ell) {k : ℕ}
    (hk1 : k + 1 ≤ (x 0).val - (y 0).val) :
    periodicLatticeShift (periodicLatticeShift (zK y x k) 1) 0 ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    have hshift1coord0 : (periodicLatticeShift (zK y x k) 1) 0 = zK y x k 0 :=
      periodicLatticeShift_coord_ne (zK y x k) (by decide : (0 : Fin 3) ≠ 1)
    have hk_le : k ≤ (x 0).val - (y 0).val := by omega
    have hxisLt := (x 0).isLt
    have hval0 : (zK y x k 0).val = (y 0).val + k := zK_coord0_eq_of_le y x hk_le (by omega)
    have hxge := (mem_blockOf.mp hx) 0 |>.1
    have hxlt := (mem_blockOf.mp hx) 0 |>.2
    have hnowrap0 : ((periodicLatticeShift (zK y x k) 1) 0).val + 1 < L 0 + 1 := by
      rw [hshift1coord0, hval0]; omega
    have hval := AdalyFormal.Balaban.PoincareBridge.shift_val_self
      (periodicLatticeShift (zK y x k) 1) 0 hnowrap0
    rw [hval, hshift1coord0, hval0]
    exact ⟨by omega, by omega⟩
  · rw [periodicLatticeShift_coord_ne (periodicLatticeShift (zK y x k) 1) hμ]
    exact mem_blockOf.mp (shift1_zK_mem_blockOf hstrict1 y x hx hshift1 (by omega)) μ

/-- **THE TELESCOPING STEP** — the curl at `zK y x k`, in the `(0,1)`-plane, equals EXACTLY the
consecutive difference of the direction-`1` bond values, because the curl's other two terms
(direction-`0` bonds at `zK y x k` and at `shift₁(zK y x k)`) both vanish by `dir0_bond_eq_zero`. -/
theorem dir1_step_eq_curl {L : PeriodicLatticeExtent} {ell : ℕ}
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift1 : periodicLatticeShift x 1 ∈ blockOf y ell) {k : ℕ}
    (hk1 : k + 1 ≤ (x 0).val - (y 0).val) :
    curlValue B (zK y x k, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩)
      = B (zK y x (k + 1), (1 : Fin 3)) - B (zK y x k, (1 : Fin 3)) := by
  have hk : k ≤ (x 0).val - (y 0).val := by omega
  have hzk_mem : zK y x k ∈ blockOf y ell := zK_mem_blockOf y x hx hk
  have hzk1_mem : zK y x (k + 1) ∈ blockOf y ell := zK_mem_blockOf y x hx hk1
  have hterm1 : B (zK y x k, (0 : Fin 3)) = 0 := by
    apply dir0_bond_eq_zero hstrict0 B hB y hy (zK y x k, 0) rfl
    refine ⟨hzk_mem, ?_⟩
    show periodicLatticeShift (zK y x k) 0 ∈ blockOf y ell
    rw [← zK_succ]; exact hzk1_mem
  have hterm2 : B (periodicLatticeShift (zK y x k) 1, (0 : Fin 3)) = 0 := by
    apply dir0_bond_eq_zero hstrict0 B hB y hy (periodicLatticeShift (zK y x k) 1, 0) rfl
    exact ⟨shift1_zK_mem_blockOf hstrict1 y x hx hshift1 hk,
      shift0_shift1_zK_mem_blockOf hstrict1 y x hx hshift1 hk1⟩
  unfold curlValue
  show B (zK y x k, (0 : Fin 3)) + B (periodicLatticeShift (zK y x k) 0, (1 : Fin 3))
      - B (periodicLatticeShift (zK y x k) 1, (0 : Fin 3)) - B (zK y x k, (1 : Fin 3))
    = B (zK y x (k + 1), (1 : Fin 3)) - B (zK y x k, (1 : Fin 3))
  rw [hterm1, hterm2, zK_succ]
  ring

/-- Elementary telescoping: the sum of consecutive differences collapses to the endpoints. -/
theorem telescope_sum (φ : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (φ (k + 1) - φ k) = φ n - φ 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- **THE ASSEMBLED PER-BOND BOUND — CMP96 p.244's own displayed inequality
`|B(x,x+e_2)|² ≤ |x_1-y_1|Σ|(∂₁B)(p(x'))|²`, faithfully reproduced.** For every direction-`1` bond
`b` with both endpoints in `blockOf y ell`, the square of its value is bounded by `(ell-1)` times
the sum of squared curls along the telescoping path — the genuine geometric content of `(2.123)`,
for this one direction. -/
theorem dir1_bondSq_le {L : PeriodicLatticeExtent} {ell : ℕ}
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (b : Bond L) (hb2 : b.2 = 1) (hbb : bondInBlock y ell b) :
    (B b) ^ 2 ≤ ((ell : ℝ) - 1) *
      ∑ k ∈ Finset.range ((b.1 0).val - (y 0).val),
        (curlValue B (zK y b.1 k, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩)) ^ 2 := by
  obtain ⟨hx, hshift1'⟩ := hbb
  have hshift1 : periodicLatticeShift b.1 1 ∈ blockOf y ell := by rw [← hb2]; exact hshift1'
  set n := (b.1 0).val - (y 0).val with hn_def
  have hxge : (y 0).val ≤ (b.1 0).val := (mem_blockOf.mp hx) 0 |>.1
  have hxlt : (b.1 0).val < (y 0).val + ell := (mem_blockOf.mp hx) 0 |>.2
  have hxisLt := (b.1 0).isLt
  have hnlt : n < ell := by omega
  set φ : ℕ → ℝ := fun k => B (zK y b.1 k, (1 : Fin 3)) with hφ_def
  have hsum_eq : ∑ k ∈ Finset.range n, curlValue B (zK y b.1 k, ⟨(0, 1), by decide⟩)
      = φ n - φ 0 := by
    rw [← telescope_sum φ n]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact dir1_step_eq_curl hstrict0 hstrict1 B hB y hy b.1 hx hshift1 (by omega)
  have hφ0 : φ 0 = 0 := by
    show B (zK y b.1 0, (1 : Fin 3)) = 0
    rw [zK_zero]
    exact z0_bond1_eq_zero hstrict1 B hB y hy b.1 hx hshift1
  have hφn : φ n = B b := by
    show B (zK y b.1 n, (1 : Fin 3)) = B b
    rw [hn_def, zK_walkLength y b.1 hxge (by omega)]
    exact congrArg B (Prod.ext rfl hb2.symm)
  have hBb_eq : B b = ∑ k ∈ Finset.range n, curlValue B (zK y b.1 k, ⟨(0, 1), by decide⟩) := by
    rw [hsum_eq, hφ0, hφn]; ring
  rw [hBb_eq]
  set g : ℕ → ℝ := fun k => curlValue B (zK y b.1 k, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩)
    with hg_def
  have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.range n) (f := g)
  simp only [Finset.card_range] at hCS
  have hSnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range n, (g k) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hnR : (n : ℝ) ≤ (ell : ℝ) - 1 := by
    have h1 : n + 1 ≤ ell := hnlt
    have hcast : ((n : ℝ) + 1) ≤ (ell : ℝ) := by exact_mod_cast h1
    linarith
  calc (∑ k ∈ Finset.range n, g k) ^ 2
      ≤ (n : ℝ) * ∑ k ∈ Finset.range n, (g k) ^ 2 := hCS
    _ ≤ ((ell : ℝ) - 1) * ∑ k ∈ Finset.range n, (g k) ^ 2 :=
        mul_le_mul_of_nonneg_right hnR hSnn

#print axioms dir1_bondSq_le

/-! ## §4. THE DIRECTION-`2` (Lean; CMP96's `e_3`, `j = 3`) TELESCOPING BOUND — the page's own
"arbitrary `j`" formula (p.244, above (2.123)) at `j = d = 3`, PROVED for this concrete geometry.

CMP96 p.244 states, for `b = ⟨x, x+e_j⟩`, `2 ≤ j ≤ d`:
`|B(x,x+e_j)|² ≤ (|x_1-y_1|+…+|x_{j-1}-y_{j-1}|) Σ|(∂₁B)(p(x'))|²`, the plaquettes `p(x')` parallel
to `(e_{j-1},e_j),…,(e_1,e_j)`. For `d = 3`, `j = 3` (Lean direction `2`) this is TWO nested
telescoping walks: FIRST along axis `0` (source `e_1`) from `x` down to `(y_0,x_1,x_2)` — giving
`(0,2)`-plane [source `(e_1,e_3)`] plaquettes; THEN along axis `1` (source `e_2`) from `(y_0,x_1,x_2)`
down to `(y_0,y_1,x_2)` — giving `(1,2)`-plane [source `(e_2,e_3)`] plaquettes; ending at
`w₀ := (y_0,y_1,x_2)`, whose direction-`2` bond is forced to `0` by `(2.121)`. The path-length
factor is `|x_0-y_0| + |x_1-y_1| ≤ 2(ell-1)`, matching the source's `|x_1-y_1|+|x_2-y_2|`.

Walk A (axis `0`) reuses `zK` verbatim (it is bond-direction-agnostic); the direction-`0` bonds in
its `(0,2)`-curls vanish by §2's `dir0_bond_eq_zero`, EXACTLY as in §3. Walk B (axis `1`) needs the
new `wK` walk below; the direction-`1` bonds in its `(1,2)`-curls vanish NOT by a triviality lemma
but by a direct `(2.121)` admissibility application on `Γ_{y,z₀}` (the same mechanism as
`z0_bond1_eq_zero`), because a direction-`1` bond based at coordinate `0 = y_0` is the middle segment
of the staircase to `z₀`. -/

/-- `w₀` — `z₀` with coordinate `1` further reset to `y`'s value: the point `(y_0, y_1, x_2)`, the
common endpoint of the two nested walks. Its direction-`2` bond is `(2.123)`'s zero boundary term. -/
def w0 (y x : PeriodicLatticeSite L) : PeriodicLatticeSite L := Function.update (z0 y x) 1 (y 1)

theorem w0_coord0 (y x : PeriodicLatticeSite L) : (w0 y x) 0 = y 0 := by
  unfold w0; rw [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1), z0_coord0]

theorem w0_coord1 (y x : PeriodicLatticeSite L) : (w0 y x) 1 = y 1 := Function.update_self _ _ _

theorem w0_coord2 (y x : PeriodicLatticeSite L) : (w0 y x) 2 = x 2 := by
  unfold w0
  rw [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1), z0_coord_ne y x (by decide)]

/-- Walk B: `w₀`'s coordinate `1` shifted `k` fine steps forward — the axis-`1` analogue of `zK`,
reusing `CoarseCurl.coarseShift` verbatim (LAW-19). -/
def wK (y x : PeriodicLatticeSite L) (k : ℕ) : PeriodicLatticeSite L :=
  AdalyFormal.Balaban.CoarseCurl.coarseShift (w0 y x) k 1

theorem wK_zero (y x : PeriodicLatticeSite L) : wK y x 0 = w0 y x := by
  unfold wK AdalyFormal.Balaban.CoarseCurl.coarseShift
  exact Function.iterate_zero_apply _ _

theorem wK_succ (y x : PeriodicLatticeSite L) (k : ℕ) :
    wK y x (k + 1) = periodicLatticeShift (wK y x k) 1 := by
  unfold wK AdalyFormal.Balaban.CoarseCurl.coarseShift
  exact Function.iterate_succ_apply' _ _ _

theorem wK_coord1 (y x : PeriodicLatticeSite L) (k : ℕ) :
    (wK y x k 1).val = ((y 1).val + k) % (L 1 + 1) := by
  have h := AdalyFormal.Balaban.CoarseCurl.coarseShift_val_eq (w0 y x) k 1
  rw [w0_coord1] at h
  exact h

theorem wK_coord_ne (y x : PeriodicLatticeSite L) (k : ℕ) {ν : Fin 3} (hν : ν ≠ 1) :
    (wK y x k) ν = (w0 y x) ν :=
  AdalyFormal.Balaban.CoarseCurl.coarseShift_apply_ne (w0 y x) k 1 ν hν

theorem wK_coord0 (y x : PeriodicLatticeSite L) (k : ℕ) : (wK y x k) 0 = y 0 := by
  rw [wK_coord_ne y x k (by decide : (0 : Fin 3) ≠ 1), w0_coord0]

theorem wK_coord2 (y x : PeriodicLatticeSite L) (k : ℕ) : (wK y x k) 2 = x 2 := by
  rw [wK_coord_ne y x k (by decide : (2 : Fin 3) ≠ 1), w0_coord2]

theorem wK_coord1_eq_of_le (y x : PeriodicLatticeSite L) {k : ℕ}
    (hk : k ≤ (x 1).val - (y 1).val) (hxlt : (x 1).val < L 1 + 1) :
    (wK y x k 1).val = (y 1).val + k := by
  rw [wK_coord1]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Walk B closes at `z₀` when `k = n_B := x_1 - y_1`.** -/
theorem wK_walkLength (y x : PeriodicLatticeSite L) (hge : (y 1).val ≤ (x 1).val)
    (hlt : (x 1).val < L 1 + 1) : wK y x ((x 1).val - (y 1).val) = z0 y x := by
  funext ν
  by_cases hν : ν = 1
  · subst hν
    apply Fin.ext
    rw [wK_coord1, show (z0 y x) 1 = x 1 from z0_coord_ne y x (by decide)]
    have : (y 1).val + ((x 1).val - (y 1).val) = (x 1).val := by omega
    rw [this, Nat.mod_eq_of_lt hlt]
  · rw [wK_coord_ne y x _ hν]
    show (w0 y x) ν = (z0 y x) ν
    unfold w0
    exact Function.update_of_ne hν _ _

/-! ### §4a. Walk-A membership lemmas (direction-`2` shift), mirroring §3b for the `(0,2)` plane -/

theorem shift2_zK_mem_blockOf {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict2 : ell < L 2 + 1)
    (y x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift2 : periodicLatticeShift x 2 ∈ blockOf y ell) {k : ℕ}
    (hk : k ≤ (x 0).val - (y 0).val) :
    periodicLatticeShift (zK y x k) 2 ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro μ
  by_cases hμ : μ = 2
  · subst hμ
    have hzk2 : zK y x k 2 = x 2 := zK_coord_ne y x k (by decide)
    have hnowrap : (x 2).val + 1 < L 2 + 1 := noWrap_of_bondInBlock hstrict2 hx hshift2
    have hnowrap' : (zK y x k 2).val + 1 < L 2 + 1 := by rw [hzk2]; exact hnowrap
    have hval : ((periodicLatticeShift (zK y x k) 2) 2).val = (zK y x k 2).val + 1 :=
      AdalyFormal.Balaban.PoincareBridge.shift_val_self (zK y x k) 2 hnowrap'
    have hshiftval : ((periodicLatticeShift x (2 : Fin 3)) 2).val = (x 2).val + 1 :=
      AdalyFormal.Balaban.PoincareBridge.shift_val_self x 2 hnowrap
    have hmemx2 := mem_blockOf.mp hshift2 2
    rw [hshiftval] at hmemx2
    rw [hval, hzk2]
    exact hmemx2
  · by_cases hμ0 : μ = 0
    · subst hμ0
      rw [periodicLatticeShift_coord_ne (zK y x k) (by decide : (0 : Fin 3) ≠ 2)]
      exact mem_blockOf.mp (zK_mem_blockOf y x hx hk) 0
    · have hμ1 : μ = 1 := by
        have := μ.isLt
        have h0 : μ.val ≠ 0 := fun h => hμ0 (Fin.ext h)
        have h2 : μ.val ≠ 2 := fun h => hμ (Fin.ext h)
        apply Fin.ext; omega
      subst hμ1
      rw [periodicLatticeShift_coord_ne (zK y x k) (by decide : (1 : Fin 3) ≠ 2)]
      exact mem_blockOf.mp (zK_mem_blockOf y x hx hk) 1

theorem shift0_shift2_zK_mem_blockOf {L : PeriodicLatticeExtent} {ell : ℕ}
    (hstrict2 : ell < L 2 + 1) (y x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift2 : periodicLatticeShift x 2 ∈ blockOf y ell) {k : ℕ}
    (hk1 : k + 1 ≤ (x 0).val - (y 0).val) :
    periodicLatticeShift (periodicLatticeShift (zK y x k) 2) 0 ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    have hshift2coord0 : (periodicLatticeShift (zK y x k) 2) 0 = zK y x k 0 :=
      periodicLatticeShift_coord_ne (zK y x k) (by decide : (0 : Fin 3) ≠ 2)
    have hk_le : k ≤ (x 0).val - (y 0).val := by omega
    have hxisLt := (x 0).isLt
    have hval0 : (zK y x k 0).val = (y 0).val + k := zK_coord0_eq_of_le y x hk_le (by omega)
    have hxge := (mem_blockOf.mp hx) 0 |>.1
    have hxlt := (mem_blockOf.mp hx) 0 |>.2
    have hnowrap0 : ((periodicLatticeShift (zK y x k) 2) 0).val + 1 < L 0 + 1 := by
      rw [hshift2coord0, hval0]; omega
    have hval := AdalyFormal.Balaban.PoincareBridge.shift_val_self
      (periodicLatticeShift (zK y x k) 2) 0 hnowrap0
    rw [hval, hshift2coord0, hval0]
    exact ⟨by omega, by omega⟩
  · rw [periodicLatticeShift_coord_ne (periodicLatticeShift (zK y x k) 2) hμ]
    exact mem_blockOf.mp (shift2_zK_mem_blockOf hstrict2 y x hx hshift2 (by omega)) μ

/-- **Walk-A telescoping step (`(0,2)` plane).** The `(0,2)`-curl at `zK y x k` equals the
consecutive difference of direction-`2` bond values, the two direction-`0` cross-terms vanishing by
`dir0_bond_eq_zero`. -/
theorem dir2_stepA_eq_curl {L : PeriodicLatticeExtent} {ell : ℕ}
    (hstrict0 : ell < L 0 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift2 : periodicLatticeShift x 2 ∈ blockOf y ell) {k : ℕ}
    (hk1 : k + 1 ≤ (x 0).val - (y 0).val) :
    curlValue B (zK y x k, ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩)
      = B (zK y x (k + 1), (2 : Fin 3)) - B (zK y x k, (2 : Fin 3)) := by
  have hk : k ≤ (x 0).val - (y 0).val := by omega
  have hzk_mem : zK y x k ∈ blockOf y ell := zK_mem_blockOf y x hx hk
  have hzk1_mem : zK y x (k + 1) ∈ blockOf y ell := zK_mem_blockOf y x hx hk1
  have hterm1 : B (zK y x k, (0 : Fin 3)) = 0 := by
    apply dir0_bond_eq_zero hstrict0 B hB y hy (zK y x k, 0) rfl
    refine ⟨hzk_mem, ?_⟩
    show periodicLatticeShift (zK y x k) 0 ∈ blockOf y ell
    rw [← zK_succ]; exact hzk1_mem
  have hterm2 : B (periodicLatticeShift (zK y x k) 2, (0 : Fin 3)) = 0 := by
    apply dir0_bond_eq_zero hstrict0 B hB y hy (periodicLatticeShift (zK y x k) 2, 0) rfl
    exact ⟨shift2_zK_mem_blockOf hstrict2 y x hx hshift2 hk,
      shift0_shift2_zK_mem_blockOf hstrict2 y x hx hshift2 hk1⟩
  unfold curlValue
  show B (zK y x k, (0 : Fin 3)) + B (periodicLatticeShift (zK y x k) 0, (2 : Fin 3))
      - B (periodicLatticeShift (zK y x k) 2, (0 : Fin 3)) - B (zK y x k, (2 : Fin 3))
    = B (zK y x (k + 1), (2 : Fin 3)) - B (zK y x k, (2 : Fin 3))
  rw [hterm1, hterm2, zK_succ]
  ring

/-! ### §4b. Walk-B vanishing lemmas — direction-`1` bonds at coordinate-`0 = y_0` vanish by
`(2.121)` (staircase middle segment), and the endpoint direction-`2` bond `B(w₀,2)` vanishes by
`(2.121)` (staircase first segment). -/

/-- `z₀` lies in the block (coordinate `0` reset to `y`'s value; the other two are `x`'s). -/
theorem z0_mem_blockOf {L : PeriodicLatticeExtent} {ell : ℕ} (y x : PeriodicLatticeSite L)
    (hx : x ∈ blockOf y ell) : z0 y x ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro μ
  by_cases hμ0 : μ = 0
  · subst hμ0
    rw [z0_coord0]
    have hell : 0 < ell := by have h := (mem_blockOf.mp hx) 0; omega
    exact ⟨le_refl _, by omega⟩
  · rw [z0_coord_ne y x hμ0]
    exact mem_blockOf.mp hx μ

/-- **`B(wK y x k, 1) = 0`** for `k < n_B` — the direction-`1` bond at `(y_0, y_1+k, x_2)` is the
middle (axis-`1`) segment of `Γ_{y, z₀}`, so `(2.121)` kills it. -/
theorem wK_bond1_eq_zero {L : PeriodicLatticeExtent} {ell : ℕ}
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell) {k : ℕ}
    (hk : k < (x 1).val - (y 1).val) :
    B (wK y x k, (1 : Fin 3)) = 0 := by
  have hxge1 := (mem_blockOf.mp hx) 1 |>.1
  have hz0mem : z0 y x ∈ blockOf y ell := z0_mem_blockOf y x hx
  have hz01 : (z0 y x) 1 = x 1 := z0_coord_ne y x (by decide : (1 : Fin 3) ≠ 0)
  have hwkval : (wK y x k 1).val = (y 1).val + k := wK_coord1_eq_of_le y x (le_of_lt hk) (x 1).isLt
  have hstair : (wK y x k, (1 : Fin 3)) ∈ staircasePath y (z0 y x) := by
    unfold staircasePath
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [mem_axisSegment]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro ν hν
      by_cases hν0 : ν = 0
      · subst hν0
        show (wK y x k) 0 = (corner1 y (z0 y x)) 0
        rw [wK_coord0]
        unfold corner1
        exact (Function.update_of_ne (by decide) _ _).symm
      · have hν2 : ν = 2 := by
          have := ν.isLt
          have h0 : ν.val ≠ 0 := fun h => hν0 (Fin.ext h)
          have h1 : ν.val ≠ 1 := fun h => hν (Fin.ext h)
          apply Fin.ext; omega
        subst hν2
        show (wK y x k) 2 = (corner1 y (z0 y x)) 2
        rw [wK_coord2]
        unfold corner1
        rw [Function.update_self]
        exact (z0_coord_ne y x (by decide : (2 : Fin 3) ≠ 0)).symm
    · show min (y 1).val ((z0 y x) 1).val ≤ (wK y x k 1).val
      rw [hz01]
      have hmin : min (y 1).val (x 1).val = (y 1).val := min_eq_left hxge1
      rw [hmin, hwkval]; omega
    · show (wK y x k 1).val < max (y 1).val ((z0 y x) 1).val
      rw [hz01]
      have hmax : max (y 1).val (x 1).val = (x 1).val := max_eq_right hxge1
      rw [hmax, hwkval]; omega
  exact (mem_admissibleSubspaceInter.mp hB) y hy (z0 y x) hz0mem (wK y x k, 1) hstair

/-- **`B(shift₂(wK y x k), 1) = 0`** for `k < n_B` — the direction-`1` bond at
`(y_0, y_1+k, x_2+1)` is the middle segment of `Γ_{y, shift₂ z₀}`. -/
theorem shift2_wK_bond1_eq_zero {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict2 : ell < L 2 + 1)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift2 : periodicLatticeShift x 2 ∈ blockOf y ell)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell) {k : ℕ}
    (hk : k < (x 1).val - (y 1).val) :
    B (periodicLatticeShift (wK y x k) 2, (1 : Fin 3)) = 0 := by
  have hxge1 := (mem_blockOf.mp hx) 1 |>.1
  have hnowrap2 : (x 2).val + 1 < L 2 + 1 := noWrap_of_bondInBlock hstrict2 hx hshift2
  set x' := periodicLatticeShift (z0 y x) 2 with hx'def
  have hz0_2 : (z0 y x) 2 = x 2 := z0_coord_ne y x (by decide : (2 : Fin 3) ≠ 0)
  have hnowrap2' : ((z0 y x) 2).val + 1 < L 2 + 1 := by rw [hz0_2]; exact hnowrap2
  have hx'2val : (x' 2).val = (x 2).val + 1 := by
    rw [hx'def, AdalyFormal.Balaban.PoincareBridge.shift_val_self (z0 y x) 2 hnowrap2', hz0_2]
  have hx'1 : x' 1 = x 1 := by
    rw [hx'def, periodicLatticeShift_coord_ne (z0 y x) (by decide : (1 : Fin 3) ≠ 2),
        z0_coord_ne y x (by decide : (1 : Fin 3) ≠ 0)]
  have hx'0 : x' 0 = y 0 := by
    rw [hx'def, periodicLatticeShift_coord_ne (z0 y x) (by decide : (0 : Fin 3) ≠ 2), z0_coord0]
  have hx'mem : x' ∈ blockOf y ell := by
    rw [mem_blockOf]
    intro μ
    by_cases hμ0 : μ = 0
    · subst hμ0
      rw [hx'0]
      have hell : 0 < ell := by have h := (mem_blockOf.mp hx) 0; omega
      exact ⟨le_refl _, by omega⟩
    · by_cases hμ1 : μ = 1
      · subst hμ1
        rw [hx'1]; exact mem_blockOf.mp hx 1
      · have hμ2 : μ = 2 := by
          have := μ.isLt
          have h0 : μ.val ≠ 0 := fun h => hμ0 (Fin.ext h)
          have h1 : μ.val ≠ 1 := fun h => hμ1 (Fin.ext h)
          apply Fin.ext; omega
        subst hμ2
        rw [hx'2val]
        have hmemx2 := mem_blockOf.mp hshift2 2
        have hshiftval := AdalyFormal.Balaban.PoincareBridge.shift_val_self x 2 hnowrap2
        rw [hshiftval] at hmemx2
        exact hmemx2
  set e := periodicLatticeShift (wK y x k) 2 with hedef
  have hwk2 : (wK y x k) 2 = x 2 := wK_coord2 y x k
  have hnw : ((wK y x k) 2).val + 1 < L 2 + 1 := by rw [hwk2]; exact hnowrap2
  have he2 : (e 2).val = (x 2).val + 1 := by
    rw [hedef, AdalyFormal.Balaban.PoincareBridge.shift_val_self (wK y x k) 2 hnw, hwk2]
  have he0 : e 0 = y 0 := by
    rw [hedef, periodicLatticeShift_coord_ne (wK y x k) (by decide : (0 : Fin 3) ≠ 2), wK_coord0]
  have he1val : (e 1).val = (y 1).val + k := by
    have hstep : e 1 = wK y x k 1 := by
      rw [hedef, periodicLatticeShift_coord_ne (wK y x k) (by decide : (1 : Fin 3) ≠ 2)]
    rw [hstep]
    exact wK_coord1_eq_of_le y x (le_of_lt hk) (x 1).isLt
  have hstair : (e, (1 : Fin 3)) ∈ staircasePath y x' := by
    unfold staircasePath
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [mem_axisSegment]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro ν hν
      by_cases hν0 : ν = 0
      · subst hν0
        show e 0 = (corner1 y x') 0
        rw [he0]
        unfold corner1
        exact (Function.update_of_ne (by decide) _ _).symm
      · have hν2 : ν = 2 := by
          have := ν.isLt
          have h0 : ν.val ≠ 0 := fun h => hν0 (Fin.ext h)
          have h1 : ν.val ≠ 1 := fun h => hν (Fin.ext h)
          apply Fin.ext; omega
        subst hν2
        show e 2 = (corner1 y x') 2
        apply Fin.ext
        rw [he2]
        unfold corner1
        rw [Function.update_self, hx'2val]
    · show min (y 1).val (x' 1).val ≤ (e 1).val
      rw [hx'1]
      have hmin : min (y 1).val (x 1).val = (y 1).val := min_eq_left hxge1
      rw [hmin, he1val]; omega
    · show (e 1).val < max (y 1).val (x' 1).val
      rw [hx'1]
      have hmax : max (y 1).val (x 1).val = (x 1).val := max_eq_right hxge1
      rw [hmax, he1val]; omega
  exact (mem_admissibleSubspaceInter.mp hB) y hy x' hx'mem (e, 1) hstair

/-- **`B(w₀ y x, 2) = 0`** — the direction-`2` bond at `(y_0, y_1, x_2)` is the first (axis-`2`)
segment of `Γ_{y, shift₂ x}`, the zero boundary term of `(2.123)`'s telescoping. -/
theorem w0_bond2_eq_zero {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict2 : ell < L 2 + 1)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift2 : periodicLatticeShift x 2 ∈ blockOf y ell)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell) :
    B (w0 y x, (2 : Fin 3)) = 0 := by
  have hnowrap2 : (x 2).val + 1 < L 2 + 1 := noWrap_of_bondInBlock hstrict2 hx hshift2
  have hxge2 := (mem_blockOf.mp hx) 2 |>.1
  set x'' := periodicLatticeShift x 2 with hx''def
  have hx''2 : (x'' 2).val = (x 2).val + 1 := by
    rw [hx''def]; exact AdalyFormal.Balaban.PoincareBridge.shift_val_self x 2 hnowrap2
  have hw02 : (w0 y x) 2 = x 2 := w0_coord2 y x
  have hstair : (w0 y x, (2 : Fin 3)) ∈ staircasePath y x'' := by
    unfold staircasePath
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [mem_axisSegment]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro ν hν
      by_cases hν0 : ν = 0
      · subst hν0
        show (w0 y x) 0 = y 0
        exact w0_coord0 y x
      · have hν1 : ν = 1 := by
          have := ν.isLt
          have h0 : ν.val ≠ 0 := fun h => hν0 (Fin.ext h)
          have h2 : ν.val ≠ 2 := fun h => hν (Fin.ext h)
          apply Fin.ext; omega
        subst hν1
        show (w0 y x) 1 = y 1
        exact w0_coord1 y x
    · show min (y 2).val (x'' 2).val ≤ (w0 y x 2).val
      rw [hx''2]
      have hmin : min (y 2).val ((x 2).val + 1) = (y 2).val := by apply min_eq_left; omega
      rw [hmin, hw02]; exact hxge2
    · show (w0 y x 2).val < max (y 2).val (x'' 2).val
      rw [hx''2]
      have hmax : max (y 2).val ((x 2).val + 1) = (x 2).val + 1 := by apply max_eq_right; omega
      rw [hmax, hw02]; omega
  exact (mem_admissibleSubspaceInter.mp hB) y hy x'' hshift2 (w0 y x, 2) hstair

/-- **Walk-B telescoping step (`(1,2)` plane).** The `(1,2)`-curl at `wK y x k` equals the
consecutive difference of direction-`2` bond values, the two direction-`1` cross-terms vanishing by
`wK_bond1_eq_zero` / `shift2_wK_bond1_eq_zero`. -/
theorem dir2_stepB_eq_curl {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift2 : periodicLatticeShift x 2 ∈ blockOf y ell) {k : ℕ}
    (hk1 : k + 1 ≤ (x 1).val - (y 1).val) :
    curlValue B (wK y x k, ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩)
      = B (wK y x (k + 1), (2 : Fin 3)) - B (wK y x k, (2 : Fin 3)) := by
  have hk : k < (x 1).val - (y 1).val := by omega
  have hterm1 : B (wK y x k, (1 : Fin 3)) = 0 := wK_bond1_eq_zero y hy x hx B hB hk
  have hterm2 : B (periodicLatticeShift (wK y x k) 2, (1 : Fin 3)) = 0 :=
    shift2_wK_bond1_eq_zero hstrict2 y hy x hx hshift2 B hB hk
  unfold curlValue
  show B (wK y x k, (1 : Fin 3)) + B (periodicLatticeShift (wK y x k) 1, (2 : Fin 3))
      - B (periodicLatticeShift (wK y x k) 2, (1 : Fin 3)) - B (wK y x k, (2 : Fin 3))
    = B (wK y x (k + 1), (2 : Fin 3)) - B (wK y x k, (2 : Fin 3))
  rw [hterm1, hterm2, wK_succ]
  ring

/-- **THE ASSEMBLED DIRECTION-`2` PER-BOND BOUND — CMP96 p.244's "arbitrary `j`" inequality at
`j = d = 3`.** For every direction-`2` bond `b` with both endpoints in `blockOf y ell`,
`(B b)² ≤ 2(ell-1)·(Σ_{k<n_A}|(0,2)-curl|² + Σ_{k<n_B}|(1,2)-curl|²)`, where the two path segments
walk axis `0` (length `n_A = x_0-y_0`) then axis `1` (length `n_B = x_1-y_1`), each `≤ ell-1`. The
constant `2(ell-1)` is block-size-only (the source's path-length factor `|x_1-y_1|+|x_2-y_2|`). -/
theorem dir2_bondSq_le {L : PeriodicLatticeExtent} {ell : ℕ}
    (hstrict0 : ell < L 0 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (b : Bond L) (hb2 : b.2 = 2) (hbb : bondInBlock y ell b) :
    (B b) ^ 2 ≤ (2 * ((ell : ℝ) - 1)) *
      (∑ k ∈ Finset.range ((b.1 0).val - (y 0).val),
          (curlValue B (zK y b.1 k, ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩)) ^ 2
       + ∑ k ∈ Finset.range ((b.1 1).val - (y 1).val),
          (curlValue B (wK y b.1 k, ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩)) ^ 2) := by
  obtain ⟨hx, hshift2'⟩ := hbb
  have hshift2 : periodicLatticeShift b.1 2 ∈ blockOf y ell := by rw [← hb2]; exact hshift2'
  have hx0ge := (mem_blockOf.mp hx) 0 |>.1
  have hx0lt := (mem_blockOf.mp hx) 0 |>.2
  have hx1ge := (mem_blockOf.mp hx) 1 |>.1
  have hx1lt := (mem_blockOf.mp hx) 1 |>.2
  have hx0isLt := (b.1 0).isLt
  have hx1isLt := (b.1 1).isLt
  set nA := (b.1 0).val - (y 0).val with hnA
  set nB := (b.1 1).val - (y 1).val with hnB
  have hnAlt : nA < ell := by omega
  have hnBlt : nB < ell := by omega
  -- Walk A telescoping: B(b) - B(z₀,2) = Σ_A curl(0,2)
  set φA : ℕ → ℝ := fun k => B (zK y b.1 k, (2 : Fin 3)) with hφA
  have hsumA : ∑ k ∈ Finset.range nA, curlValue B (zK y b.1 k, ⟨(0, 2), by decide⟩)
      = φA nA - φA 0 := by
    rw [← telescope_sum φA nA]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact dir2_stepA_eq_curl hstrict0 hstrict2 B hB y hy b.1 hx hshift2 (by omega)
  have hφA0 : φA 0 = B (z0 y b.1, (2 : Fin 3)) := by
    show B (zK y b.1 0, (2 : Fin 3)) = _; rw [zK_zero]
  have hφAn : φA nA = B b := by
    show B (zK y b.1 nA, (2 : Fin 3)) = B b
    rw [hnA, zK_walkLength y b.1 hx0ge (by omega)]
    exact congrArg B (Prod.ext rfl hb2.symm)
  -- Walk B telescoping: B(z₀,2) - B(w₀,2) = Σ_B curl(1,2)
  set φB : ℕ → ℝ := fun k => B (wK y b.1 k, (2 : Fin 3)) with hφB
  have hsumB : ∑ k ∈ Finset.range nB, curlValue B (wK y b.1 k, ⟨(1, 2), by decide⟩)
      = φB nB - φB 0 := by
    rw [← telescope_sum φB nB]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact dir2_stepB_eq_curl hstrict2 B hB y hy b.1 hx hshift2 (by omega)
  have hφB0 : φB 0 = 0 := by
    show B (wK y b.1 0, (2 : Fin 3)) = 0
    rw [wK_zero]; exact w0_bond2_eq_zero hstrict2 y hy b.1 hx hshift2 B hB
  have hφBn : φB nB = B (z0 y b.1, (2 : Fin 3)) := by
    show B (wK y b.1 nB, (2 : Fin 3)) = _
    rw [hnB, wK_walkLength y b.1 hx1ge (by omega)]
  -- Combine: B(b) = S_A + S_B
  set gA : ℕ → ℝ := fun k => curlValue B (zK y b.1 k, ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩)
    with hgA
  set gB : ℕ → ℝ := fun k => curlValue B (wK y b.1 k, ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩)
    with hgB
  set SA := ∑ k ∈ Finset.range nA, gA k with hSA
  set SB := ∑ k ∈ Finset.range nB, gB k with hSB
  have hBb : B b = SA + SB := by
    have hA : SA = B b - B (z0 y b.1, (2 : Fin 3)) := by rw [hsumA, hφA0, hφAn]
    have hBsum : SB = B (z0 y b.1, (2 : Fin 3)) := by rw [hsumB, hφB0, hφBn]; ring
    rw [hA, hBsum]; ring
  -- Cauchy-Schwarz on each segment
  have hCSA := sq_sum_le_card_mul_sum_sq (s := Finset.range nA) (f := gA)
  have hCSB := sq_sum_le_card_mul_sum_sq (s := Finset.range nB) (f := gB)
  simp only [Finset.card_range] at hCSA hCSB
  set TA := ∑ k ∈ Finset.range nA, (gA k) ^ 2 with hTA
  set TB := ∑ k ∈ Finset.range nB, (gB k) ^ 2 with hTB
  have hTAnn : (0 : ℝ) ≤ TA := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hTBnn : (0 : ℝ) ≤ TB := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hnAR : (nA : ℝ) ≤ (ell : ℝ) - 1 := by
    have h1 : nA + 1 ≤ ell := hnAlt
    have : ((nA : ℝ) + 1) ≤ (ell : ℝ) := by exact_mod_cast h1
    linarith
  have hnBR : (nB : ℝ) ≤ (ell : ℝ) - 1 := by
    have h1 : nB + 1 ≤ ell := hnBlt
    have : ((nB : ℝ) + 1) ≤ (ell : ℝ) := by exact_mod_cast h1
    linarith
  have hSA2 : SA ^ 2 ≤ ((ell : ℝ) - 1) * TA :=
    le_trans hCSA (mul_le_mul_of_nonneg_right hnAR hTAnn)
  have hSB2 : SB ^ 2 ≤ ((ell : ℝ) - 1) * TB :=
    le_trans hCSB (mul_le_mul_of_nonneg_right hnBR hTBnn)
  have hexp : (SA + SB) ^ 2 ≤ 2 * SA ^ 2 + 2 * SB ^ 2 := by nlinarith [sq_nonneg (SA - SB)]
  rw [hBb]
  calc (SA + SB) ^ 2 ≤ 2 * SA ^ 2 + 2 * SB ^ 2 := hexp
    _ ≤ 2 * (((ell : ℝ) - 1) * TA) + 2 * (((ell : ℝ) - 1) * TB) := by linarith [hSA2, hSB2]
    _ = (2 * ((ell : ℝ) - 1)) * (TA + TB) := by ring

#print axioms dir2_bondSq_le

/-! ## §5. Toward the AGGREGATION `(2.123)` — reusable ingredients + the precisely-named residual.

The headline `∑_{b⊂B(y)}|B(b)|² ≤ dL^d ∑_{p⊂B(y)}|(∂₁B)(p)|²` (constant `3·ell³` at `d=3`, `L=ell`)
is Bałaban's `Σ_b Σ_j` sum of the per-bond bounds `dir1_bondSq_le`/`dir2_bondSq_le` (dir-`0` bonds
vanish, §2), reorganized by the double-counting `Σ_b Σ_{p∈path(b)} = Σ_p mult(p)·(…)`. This section
supplies the SIGNED telescoping identities (the un-squared `hTri` input the abstract combinatorial
core `Migration.BlockPoincare.block_poincare_core_indexed` consumes) and pins the constant; the one
remaining item — the concrete multiplicity bound — is named precisely at the end. -/

/-- **Direction-`1` signed telescoping identity** (the un-squared form of `dir1_bondSq_le`, exposing
`hTri`): `B(b) = Σ_{k<n_A} (0,1)-curl` along the axis-`0` walk. Then `|B b| ≤ Σ|curl|` by the
triangle inequality — exactly `block_poincare_core'`'s `hTri` for a direction-`1` bond. -/
theorem dir1_bond_eq_sum {L : PeriodicLatticeExtent} {ell : ℕ}
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (b : Bond L) (hb2 : b.2 = 1) (hbb : bondInBlock y ell b) :
    B b = ∑ k ∈ Finset.range ((b.1 0).val - (y 0).val),
        curlValue B (zK y b.1 k, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩) := by
  obtain ⟨hx, hshift1'⟩ := hbb
  have hshift1 : periodicLatticeShift b.1 1 ∈ blockOf y ell := by rw [← hb2]; exact hshift1'
  set n := (b.1 0).val - (y 0).val with hn_def
  have hxge := (mem_blockOf.mp hx) 0 |>.1
  have hxlt := (mem_blockOf.mp hx) 0 |>.2
  have hxisLt := (b.1 0).isLt
  set φ : ℕ → ℝ := fun k => B (zK y b.1 k, (1 : Fin 3)) with hφ_def
  have hsum_eq : ∑ k ∈ Finset.range n, curlValue B (zK y b.1 k, ⟨(0, 1), by decide⟩) = φ n - φ 0 := by
    rw [← telescope_sum φ n]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact dir1_step_eq_curl hstrict0 hstrict1 B hB y hy b.1 hx hshift1 (by omega)
  have hφ0 : φ 0 = 0 := by
    show B (zK y b.1 0, (1 : Fin 3)) = 0
    rw [zK_zero]; exact z0_bond1_eq_zero hstrict1 B hB y hy b.1 hx hshift1
  have hφn : φ n = B b := by
    show B (zK y b.1 n, (1 : Fin 3)) = B b
    rw [hn_def, zK_walkLength y b.1 hxge (by omega)]
    exact congrArg B (Prod.ext rfl hb2.symm)
  rw [hsum_eq, hφ0, hφn]; ring

/-- **Direction-`2` signed telescoping identity** (the un-squared form of `dir2_bondSq_le`):
`B(b) = Σ_{k<n_A} (0,2)-curl + Σ_{k<n_B} (1,2)-curl`. Triangle inequality then gives the `hTri`
input for a direction-`2` bond. -/
theorem dir2_bond_eq_sum {L : PeriodicLatticeExtent} {ell : ℕ}
    (hstrict0 : ell < L 0 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (b : Bond L) (hb2 : b.2 = 2) (hbb : bondInBlock y ell b) :
    B b = (∑ k ∈ Finset.range ((b.1 0).val - (y 0).val),
          curlValue B (zK y b.1 k, ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩))
        + (∑ k ∈ Finset.range ((b.1 1).val - (y 1).val),
          curlValue B (wK y b.1 k, ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩)) := by
  obtain ⟨hx, hshift2'⟩ := hbb
  have hshift2 : periodicLatticeShift b.1 2 ∈ blockOf y ell := by rw [← hb2]; exact hshift2'
  have hx0ge := (mem_blockOf.mp hx) 0 |>.1
  have hx0lt := (mem_blockOf.mp hx) 0 |>.2
  have hx1ge := (mem_blockOf.mp hx) 1 |>.1
  have hx1lt := (mem_blockOf.mp hx) 1 |>.2
  have hx0isLt := (b.1 0).isLt
  have hx1isLt := (b.1 1).isLt
  set nA := (b.1 0).val - (y 0).val with hnA
  set nB := (b.1 1).val - (y 1).val with hnB
  set φA : ℕ → ℝ := fun k => B (zK y b.1 k, (2 : Fin 3)) with hφA
  have hsumA : ∑ k ∈ Finset.range nA, curlValue B (zK y b.1 k, ⟨(0, 2), by decide⟩)
      = φA nA - φA 0 := by
    rw [← telescope_sum φA nA]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact dir2_stepA_eq_curl hstrict0 hstrict2 B hB y hy b.1 hx hshift2 (by omega)
  have hφA0 : φA 0 = B (z0 y b.1, (2 : Fin 3)) := by
    show B (zK y b.1 0, (2 : Fin 3)) = _; rw [zK_zero]
  have hφAn : φA nA = B b := by
    show B (zK y b.1 nA, (2 : Fin 3)) = B b
    rw [hnA, zK_walkLength y b.1 hx0ge (by omega)]
    exact congrArg B (Prod.ext rfl hb2.symm)
  set φB : ℕ → ℝ := fun k => B (wK y b.1 k, (2 : Fin 3)) with hφB
  have hsumB : ∑ k ∈ Finset.range nB, curlValue B (wK y b.1 k, ⟨(1, 2), by decide⟩)
      = φB nB - φB 0 := by
    rw [← telescope_sum φB nB]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact dir2_stepB_eq_curl hstrict2 B hB y hy b.1 hx hshift2 (by omega)
  have hφB0 : φB 0 = 0 := by
    show B (wK y b.1 0, (2 : Fin 3)) = 0
    rw [wK_zero]; exact w0_bond2_eq_zero hstrict2 y hy b.1 hx hshift2 B hB
  have hφBn : φB nB = B (z0 y b.1, (2 : Fin 3)) := by
    show B (wK y b.1 nB, (2 : Fin 3)) = _
    rw [hnB, wK_walkLength y b.1 hx1ge (by omega)]
  rw [hsumA, hsumB, hφA0, hφAn, hφB0, hφBn]; ring

/-- **The aggregation constant is block-size-only.** With per-bond telescoping-path length
`K ≤ 2·ell` (dir-`2` bonds, the longest: `n_A + n_B ≤ 2(ell-1)`) and per-plaquette multiplicity
`M ≤ ell²` (the `(1,2)`-plane plaquettes, whose bonds are free in coordinate `0`: `ell` choices,
times `≤ ell-1` in coordinate `1`), the abstract core's constant `K·M ≤ 2·ell³ ≤ 3·ell³ = d·L^d`
(`d = 3`, `L = ell`). NO ambient-lattice-extent (`L μ`) factor appears — the hallmark of a correct
`(2.123)` aggregation. -/
theorem blockPoincareConst_bound (ell : ℕ) : (2 * ell) * (ell * ell) ≤ 3 * ell ^ 3 := by
  have h : (2 * ell) * (ell * ell) = 2 * ell ^ 3 := by ring
  rw [h]
  have : 2 * ell ^ 3 ≤ 3 * ell ^ 3 := by omega
  exact this

#print axioms dir1_bond_eq_sum
#print axioms dir2_bond_eq_sum
#print axioms blockPoincareConst_bound

/-!
## §5b. [SUPERSEDED — CLOSED IN §6] roadmap for `[RES-SPINE-TH2-COUNT]`, now realized as
`block_poincare`. The plan below is accurate EXCEPT: (i) §6 uses indicator-form `bAbs`/`pAbs` over
the FULL `Bond L`/`PeriodicLatticePlaquette L` Fintypes with the single-block
`block_poincare_core'`, NOT subtypes + `block_poincare_core_indexed` (whose `∀y`-uniform interface
does not fit — no per-`y` side conditions); (ii) the injection targets `range ell ×ˢ range ell`
(sizes `[0,ell)`), same `ell²` bound. Retained as the derivation record.

Everything the headline `(2.123)` needs EXCEPT one concrete counting fact is now in place:

* the per-bond geometric content — `dir0_bond_eq_zero` (dir-`0` bonds vanish), `dir1_bond_eq_sum`,
  `dir2_bond_eq_sum` (the signed telescoping identities) — from which the un-squared triangle bound
  `|B(b)| ≤ Σ_{p ∈ path(b)} |curlValue B p|` (the core's `hTri`) is immediate via
  `Finset.abs_sum_le_sum_abs`;
* the abstract combinatorial double-counting core
  `Migration.BlockPoincare.block_poincare_core_indexed` (sorry-free): given `hK`, `hM`, `hTri` it
  delivers `Σ_b (B b)² ≤ K·M·Σ_p (curl p)²`;
* the constant arithmetic `blockPoincareConst_bound` (`K·M ≤ 3·ell³`, above), verifying
  volume-independence.

**The single remaining residual — the concrete `steps`/`K`/`M` instantiation of the core for this
lattice.** To fire `block_poincare_core_indexed` one must supply, with
`Center := PeriodicLatticeSite L`, `Bondy y := {b // bondInBlock y ell b}`,
`Plaqy y := {p // plaqInBlock y ell p}`:

1. `steps y : Bondy y → Finset (Plaqy y)` — for a dir-`1` bond, the `(0,1)`-plaquettes
   `⟨(zK y b.1 k, ⟨(0,1),_⟩), _⟩` (`k < n_A`); for a dir-`2` bond, the `(0,2)`-plaquettes
   (`k < n_A`) together with the `(1,2)`-plaquettes `⟨(wK y b.1 k, ⟨(1,2),_⟩), _⟩` (`k < n_B`);
   for a dir-`0` bond, `∅`. **Each plaquette's `plaqInBlock` proof is already available** from this
   file's corner-membership lemmas (`zK_mem_blockOf`, `shift1_zK_mem_blockOf`,
   `shift0_shift1_zK_mem_blockOf`, `shift2_zK_mem_blockOf`, `shift0_shift2_zK_mem_blockOf`, plus the
   analogous `wK` corner lemmas — `wK`'s four corners are `wK k`, `wK (k+1)`, `shift₂(wK k)`,
   `shift₂(wK (k+1))`, whose block membership follows the SAME pattern as the `zK` ones but were
   not separately packaged this pass).
2. `hK : (steps y b).card ≤ 2*ell` — immediate from `n_A, n_B ≤ ell-1` and `Finset.card_image_le`.
3. `hM : plaqMultiplicity (steps y) p ≤ ell*ell` — **the load-bearing counting fact.** For a fixed
   plaquette `p`, the map `b ↦ (b.1 0, b.1 1)` is INJECTIVE on `{b | p ∈ steps y b}`: from
   `p ∈ steps y b` one reads off `b.1 2 = p.1 2` (all three planes) and `b.2` (`= 1` iff
   `p.2=(0,1)`, else `2`), so `b.1` is recovered from `(b.1 0, b.1 1)` and `p`; the image lies in
   the block grid `[y_0,y_0+ell)×[y_1,y_1+ell)` of size `ell²` (`Finset.card_le_card_of_injOn`).
   This is `[RES-SPINE-TH2-COUNT]` in fully concrete form.
4. `hTri` — the abs-of-signed-sum bound noted above, from `dir1_bond_eq_sum`/`dir2_bond_eq_sum`.

Then `block_poincare_core_indexed steps bondAbs plaqAbs (2*ell) (ell*ell) hK hM _ _ hTri`,
composed with `blockPoincareConst_bound` and `sq_abs`, yields exactly
`∑_{b∈bondsInBlock y ell} (B b)² ≤ 3·ell³·∑_{p∈plaqsInBlock y ell} (curlValue B p)²`.

**Status: BUILT (§6), sorry-free**, as `steps` / `steps_hK` / `steps_hM` / `steps_hTri` /
`block_poincare`, axioms `[propext, Classical.choice, Quot.sound]`. Item 3's per-plane coordinate
read-off (`steps_recover`) was indeed the one intricate step. -/

/-! ## §6. THE BLOCK-WIDE AGGREGATION `(2.123)` — `block_poincare`, closing `[RES-SPINE-TH2-COUNT]`.

This section instantiates the sorry-free abstract combinatorial core
`Migration.BlockPoincare.block_poincare_core'` (the double-counting + Cauchy–Schwarz body of
Bałaban's printed proof) on THIS concrete lattice, discharging the concrete forms of `hTri`
(the telescoping/triangle bound, from §5's `dir1_bond_eq_sum`/`dir2_bond_eq_sum`) and the
multiplicity count `hM ≤ ell²`, `hK ≤ 2·ell` (`[RES-SPINE-TH2-COUNT]`). The `∀ y`-uniform
`block_poincare_core_indexed` interface does NOT fit here (its `hK/hM/hTri` carry no per-`y` side
conditions, whereas the concrete per-bond bound needs `y ∈ CoarseLattice` and the block-fits
condition `hstrict`); the single-block `block_poincare_core'` fits and is consumed. -/

/-- **Walk-B (axis-`1`) membership**: `wK y x k ∈ B(y)` for `k ≤ n_B` (its coord-`0` is `y_0`,
coord-`1` is `y_1+k < y_1+ell`, coord-`2` is `x_2`). -/
theorem wK_mem_blockOf {L : PeriodicLatticeExtent} {ell : ℕ} (y x : PeriodicLatticeSite L)
    (hx : x ∈ blockOf y ell) {k : ℕ} (hk : k ≤ (x 1).val - (y 1).val) :
    wK y x k ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro μ
  have hell : 0 < ell := by have h := (mem_blockOf.mp hx) 0; omega
  by_cases hμ0 : μ = 0
  · subst hμ0
    rw [wK_coord0]
    exact ⟨le_refl _, by omega⟩
  · by_cases hμ1 : μ = 1
    · subst hμ1
      have hx1ge := (mem_blockOf.mp hx) 1 |>.1
      have hx1lt := (mem_blockOf.mp hx) 1 |>.2
      have hval := wK_coord1_eq_of_le y x hk (x 1).isLt
      rw [hval]
      exact ⟨by omega, by omega⟩
    · have hμ2 : μ = 2 := by
        have := μ.isLt
        have h0 : μ.val ≠ 0 := fun h => hμ0 (Fin.ext h)
        have h1 : μ.val ≠ 1 := fun h => hμ1 (Fin.ext h)
        apply Fin.ext; omega
      subst hμ2
      rw [wK_coord2]
      exact mem_blockOf.mp hx 2

/-- **`shift₂(wK y x k) ∈ B(y)`** for `k ≤ n_B` (coord-`2` becomes `x_2+1`, in block by `hshift2`). -/
theorem shift2_wK_mem_blockOf {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict2 : ell < L 2 + 1)
    (y x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift2 : periodicLatticeShift x 2 ∈ blockOf y ell) {k : ℕ}
    (hk : k ≤ (x 1).val - (y 1).val) :
    periodicLatticeShift (wK y x k) 2 ∈ blockOf y ell := by
  rw [mem_blockOf]
  intro μ
  by_cases hμ2 : μ = 2
  · subst hμ2
    have hwk2 : (wK y x k) 2 = x 2 := wK_coord2 y x k
    have hnowrap : (x 2).val + 1 < L 2 + 1 := noWrap_of_bondInBlock hstrict2 hx hshift2
    have hnowrap' : ((wK y x k) 2).val + 1 < L 2 + 1 := by rw [hwk2]; exact hnowrap
    have hval : ((periodicLatticeShift (wK y x k) 2) 2).val = ((wK y x k) 2).val + 1 :=
      AdalyFormal.Balaban.PoincareBridge.shift_val_self (wK y x k) 2 hnowrap'
    have hshiftval : ((periodicLatticeShift x (2 : Fin 3)) 2).val = (x 2).val + 1 :=
      AdalyFormal.Balaban.PoincareBridge.shift_val_self x 2 hnowrap
    have hmemx2 := mem_blockOf.mp hshift2 2
    rw [hshiftval] at hmemx2
    rw [hval, hwk2]
    exact hmemx2
  · rw [periodicLatticeShift_coord_ne (wK y x k) hμ2]
    exact mem_blockOf.mp (wK_mem_blockOf y x hx hk) μ

/-- **Plane-`(0,1)` plaquette membership** (dir-`1` bond): all four corners of
`(zK y x k, ⟨(0,1),_⟩)` lie in `B(y)`, for `k+1 ≤ n_A`. -/
theorem plaq01_mem {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict1 : ell < L 1 + 1)
    (y x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift1 : periodicLatticeShift x 1 ∈ blockOf y ell) {k : ℕ}
    (hk1 : k + 1 ≤ (x 0).val - (y 0).val) :
    plaqInBlock y ell (zK y x k, (⟨((0:Fin 3),(1:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)) := by
  have hk : k ≤ (x 0).val - (y 0).val := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zK_mem_blockOf y x hx hk
  · show periodicLatticeShift (zK y x k) 0 ∈ blockOf y ell
    rw [← zK_succ]; exact zK_mem_blockOf y x hx hk1
  · show periodicLatticeShift (zK y x k) 1 ∈ blockOf y ell
    exact shift1_zK_mem_blockOf hstrict1 y x hx hshift1 hk
  · show periodicLatticeShift (periodicLatticeShift (zK y x k) 0) 1 ∈ blockOf y ell
    rw [← zK_succ]; exact shift1_zK_mem_blockOf hstrict1 y x hx hshift1 hk1

/-- **Plane-`(0,2)` plaquette membership** (dir-`2` bond, walk A), `k+1 ≤ n_A`. -/
theorem plaq02_mem {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict2 : ell < L 2 + 1)
    (y x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift2 : periodicLatticeShift x 2 ∈ blockOf y ell) {k : ℕ}
    (hk1 : k + 1 ≤ (x 0).val - (y 0).val) :
    plaqInBlock y ell (zK y x k, (⟨((0:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)) := by
  have hk : k ≤ (x 0).val - (y 0).val := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zK_mem_blockOf y x hx hk
  · show periodicLatticeShift (zK y x k) 0 ∈ blockOf y ell
    rw [← zK_succ]; exact zK_mem_blockOf y x hx hk1
  · show periodicLatticeShift (zK y x k) 2 ∈ blockOf y ell
    exact shift2_zK_mem_blockOf hstrict2 y x hx hshift2 hk
  · show periodicLatticeShift (periodicLatticeShift (zK y x k) 0) 2 ∈ blockOf y ell
    rw [← zK_succ]; exact shift2_zK_mem_blockOf hstrict2 y x hx hshift2 hk1

/-- **Plane-`(1,2)` plaquette membership** (dir-`2` bond, walk B), `k+1 ≤ n_B`. -/
theorem plaq12_mem {L : PeriodicLatticeExtent} {ell : ℕ} (hstrict2 : ell < L 2 + 1)
    (y x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell)
    (hshift2 : periodicLatticeShift x 2 ∈ blockOf y ell) {k : ℕ}
    (hk1 : k + 1 ≤ (x 1).val - (y 1).val) :
    plaqInBlock y ell (wK y x k, (⟨((1:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)) := by
  have hk : k ≤ (x 1).val - (y 1).val := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact wK_mem_blockOf y x hx hk
  · show periodicLatticeShift (wK y x k) 1 ∈ blockOf y ell
    rw [← wK_succ]; exact wK_mem_blockOf y x hx hk1
  · show periodicLatticeShift (wK y x k) 2 ∈ blockOf y ell
    exact shift2_wK_mem_blockOf hstrict2 y x hx hshift2 hk
  · show periodicLatticeShift (periodicLatticeShift (wK y x k) 1) 2 ∈ blockOf y ell
    rw [← wK_succ]; exact shift2_wK_mem_blockOf hstrict2 y x hx hshift2 hk1

/-- **The telescoping plaquette path of a bond `b` inside `B(y)`.** dir-`1`: the `(0,1)`-plaquettes
along the axis-`0` walk; dir-`2`: the `(0,2)`-plaquettes (walk A) ∪ the `(1,2)`-plaquettes (walk B);
dir-`0` / out-of-block: `∅`. -/
def steps (y : PeriodicLatticeSite L) (ell : ℕ) (b : Bond L) :
    Finset (PeriodicLatticePlaquette L) :=
  if bondInBlock y ell b then
    if b.2 = 1 then
      (Finset.range ((b.1 0).val - (y 0).val)).image
        (fun k => (zK y b.1 k, (⟨((0:Fin 3),(1:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)))
    else if b.2 = 2 then
      (Finset.range ((b.1 0).val - (y 0).val)).image
          (fun k => (zK y b.1 k, (⟨((0:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)))
      ∪ (Finset.range ((b.1 1).val - (y 1).val)).image
          (fun k => (wK y b.1 k, (⟨((1:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)))
    else ∅
  else ∅

/-- A plaquette can lie on a bond's telescoping path only if the bond is inside `B(y)`. -/
theorem steps_bondInBlock {L : PeriodicLatticeExtent} {ell : ℕ} {y : PeriodicLatticeSite L}
    {b : Bond L} {p : PeriodicLatticePlaquette L} (hp : p ∈ steps y ell b) :
    bondInBlock y ell b := by
  by_contra hc
  unfold steps at hp
  rw [if_neg hc] at hp
  exact absurd hp (Finset.notMem_empty p)

/-- **The read-off (the "one genuinely intricate step" of `[RES-SPINE-TH2-COUNT]`).** From
`p ∈ steps y ell b` one recovers the bond's base coordinate-`2` (`b.1 2 = p.1 2`, all three planes
preserve coord-`2`) and its direction (`= 1` iff `p` is a `(0,1)`-plaquette, else `= 2`) — both as
functions of `p` ALONE. This forces injectivity of `b ↦ (b.1 0, b.1 1)` on the multiplicity set. -/
theorem steps_recover {L : PeriodicLatticeExtent} {ell : ℕ} {y : PeriodicLatticeSite L}
    {b : Bond L} {p : PeriodicLatticePlaquette L} (hp : p ∈ steps y ell b) :
    b.1 2 = p.1 2 ∧
      b.2 = (if p.2 = (⟨((0:Fin 3),(1:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)
        then (1 : Fin 3) else 2) := by
  have hbb := steps_bondInBlock hp
  unfold steps at hp
  rw [if_pos hbb] at hp
  by_cases h1 : b.2 = 1
  · rw [if_pos h1] at hp
    rw [Finset.mem_image] at hp
    obtain ⟨k, _, hpk⟩ := hp
    subst hpk
    refine ⟨?_, ?_⟩
    · show b.1 2 = (zK y b.1 k) 2
      rw [zK_coord_ne y b.1 k (by decide : (2:Fin 3) ≠ 0)]
    · rw [if_pos rfl]; exact h1
  · rw [if_neg h1] at hp
    by_cases h2 : b.2 = 2
    · rw [if_pos h2] at hp
      rw [Finset.mem_union] at hp
      rcases hp with hA | hB
      · rw [Finset.mem_image] at hA
        obtain ⟨k, _, hpk⟩ := hA
        subst hpk
        refine ⟨?_, ?_⟩
        · show b.1 2 = (zK y b.1 k) 2
          rw [zK_coord_ne y b.1 k (by decide : (2:Fin 3) ≠ 0)]
        · have hne : (⟨((0:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)
              ≠ ⟨((0:Fin 3),(1:Fin 3)), by decide⟩ := by decide
          rw [if_neg hne]; exact h2
      · rw [Finset.mem_image] at hB
        obtain ⟨k, _, hpk⟩ := hB
        subst hpk
        refine ⟨?_, ?_⟩
        · show b.1 2 = (wK y b.1 k) 2
          rw [wK_coord2 y b.1 k]
        · have hne : (⟨((1:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)
              ≠ ⟨((0:Fin 3),(1:Fin 3)), by decide⟩ := by decide
          rw [if_neg hne]; exact h2
    · rw [if_neg h2] at hp
      exact absurd hp (Finset.notMem_empty p)

/-- **`hK`**: every bond's telescoping path has length `≤ 2·ell` (`n_A + n_B ≤ 2(ell-1)`). -/
theorem steps_hK {L : PeriodicLatticeExtent} {ell : ℕ} (y : PeriodicLatticeSite L) (b : Bond L) :
    (steps y ell b).card ≤ 2 * ell := by
  unfold steps
  by_cases hbb : bondInBlock y ell b
  · rw [if_pos hbb]
    obtain ⟨hx, _⟩ := hbb
    have hx0ge := (mem_blockOf.mp hx) 0 |>.1
    have hx0lt := (mem_blockOf.mp hx) 0 |>.2
    have hx1ge := (mem_blockOf.mp hx) 1 |>.1
    have hx1lt := (mem_blockOf.mp hx) 1 |>.2
    by_cases h1 : b.2 = 1
    · rw [if_pos h1]
      refine le_trans Finset.card_image_le ?_
      rw [Finset.card_range]; omega
    · by_cases h2 : b.2 = 2
      · rw [if_neg h1, if_pos h2]
        refine le_trans (Finset.card_union_le _ _) ?_
        refine le_trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le) ?_
        rw [Finset.card_range, Finset.card_range]; omega
      · rw [if_neg h1, if_neg h2]; simp
  · rw [if_neg hbb]; simp

/-- **`hM`**: every plaquette is visited by `≤ ell²` bonds' paths. The injection
`b ↦ ((b.1 0).val - y_0, (b.1 1).val - y_1)` into `range ell ×ˢ range ell` is injective on the
multiplicity set (coord-`2` and direction recovered from `p` via `steps_recover`). This is the tight
`(1,2)`-plane count Bałaban's argument produces — a naive `ell-1` would be FALSE, since `wK` does not
depend on `x_0`/`x_1`, so `ell·(ell-1)` bonds can share one `(1,2)`-plaquette. -/
theorem steps_hM {L : PeriodicLatticeExtent} {ell : ℕ} (y : PeriodicLatticeSite L)
    (p : PeriodicLatticePlaquette L) :
    AdalyFormal.Migration.BlockPoincare.plaqMultiplicity (steps y ell) p ≤ ell * ell := by
  unfold AdalyFormal.Migration.BlockPoincare.plaqMultiplicity
  have hcard : (Finset.range ell ×ˢ Finset.range ell).card = ell * ell := by
    rw [Finset.card_product, Finset.card_range]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun b : Bond L => ((b.1 0).val - (y 0).val, (b.1 1).val - (y 1).val))
  · intro b hb
    have hp : p ∈ steps y ell b := (Finset.mem_filter.mp hb).2
    obtain ⟨hx, _⟩ := steps_bondInBlock hp
    have h0ge := (mem_blockOf.mp hx) 0 |>.1
    have h0lt := (mem_blockOf.mp hx) 0 |>.2
    have h1ge := (mem_blockOf.mp hx) 1 |>.1
    have h1lt := (mem_blockOf.mp hx) 1 |>.2
    show ((b.1 0).val - (y 0).val, (b.1 1).val - (y 1).val)
      ∈ Finset.range ell ×ˢ Finset.range ell
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · intro b hb b' hb' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hb hb'
    have hp := hb.2
    have hp' := hb'.2
    obtain ⟨hx, _⟩ := steps_bondInBlock hp
    obtain ⟨hx', _⟩ := steps_bondInBlock hp'
    obtain ⟨hc2, hdir⟩ := steps_recover hp
    obtain ⟨hc2', hdir'⟩ := steps_recover hp'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨he0, he1⟩ := heq
    have hb0ge := (mem_blockOf.mp hx) 0 |>.1
    have hb1ge := (mem_blockOf.mp hx) 1 |>.1
    have hb0ge' := (mem_blockOf.mp hx') 0 |>.1
    have hb1ge' := (mem_blockOf.mp hx') 1 |>.1
    have hval0 : (b.1 0).val = (b'.1 0).val := by omega
    have hval1 : (b.1 1).val = (b'.1 1).val := by omega
    have hc2'' : b.1 2 = b'.1 2 := hc2.trans hc2'.symm
    have hsite : b.1 = b'.1 := by
      funext μ
      by_cases hμ0 : μ = 0
      · subst hμ0; exact Fin.ext hval0
      · by_cases hμ1 : μ = 1
        · subst hμ1; exact Fin.ext hval1
        · have hμ2 : μ = 2 := by
            have := μ.isLt
            have h0 : μ.val ≠ 0 := fun h => hμ0 (Fin.ext h)
            have h1 : μ.val ≠ 1 := fun h => hμ1 (Fin.ext h)
            apply Fin.ext; omega
          subst hμ2; exact hc2''
    exact Prod.ext hsite (hdir.trans hdir'.symm)

/-- Block-restricted bond magnitude (indicator form, so the full-`Bond L` sum equals the block sum). -/
def bAbs (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (b : Bond L) : ℝ :=
  if bondInBlock y ell b then |B b| else 0

/-- Block-restricted curl magnitude. -/
def pAbs (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ)
    (p : PeriodicLatticePlaquette L) : ℝ :=
  if plaqInBlock y ell p then |curlValue B p| else 0

theorem bondAbs_sq_sum {L : PeriodicLatticeExtent} (B : Bond L → ℝ)
    (y : PeriodicLatticeSite L) (ell : ℕ) :
    ∑ b : Bond L, (bAbs B y ell b) ^ 2 = ∑ b ∈ bondsInBlock y ell, (B b) ^ 2 := by
  have hbi : bondsInBlock y ell = Finset.univ.filter (bondInBlock y ell) := rfl
  rw [hbi, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  unfold bAbs
  by_cases hc : bondInBlock y ell b
  · rw [if_pos hc, if_pos hc, sq_abs]
  · rw [if_neg hc, if_neg hc]; ring

theorem plaqAbs_sq_sum {L : PeriodicLatticeExtent} (B : Bond L → ℝ)
    (y : PeriodicLatticeSite L) (ell : ℕ) :
    ∑ p : PeriodicLatticePlaquette L, (pAbs B y ell p) ^ 2
      = ∑ p ∈ plaqsInBlock y ell, (curlValue B p) ^ 2 := by
  have hpi : plaqsInBlock y ell = Finset.univ.filter (plaqInBlock y ell) := rfl
  rw [hpi, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  unfold pAbs
  by_cases hc : plaqInBlock y ell p
  · rw [if_pos hc, if_pos hc, sq_abs]
  · rw [if_neg hc, if_neg hc]; ring

/-- **`hTri`**: `|B b| ≤ Σ_{p ∈ path(b)} |curlValue B p|`, the triangle inequality on §5's signed
telescoping identities (`dir1_bond_eq_sum`/`dir2_bond_eq_sum`); dir-`0` bonds vanish (`dir0_bond_eq_zero`). -/
theorem steps_hTri {L : PeriodicLatticeExtent} {ell : ℕ}
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell) (b : Bond L) :
    bAbs B y ell b ≤ ∑ p ∈ steps y ell b, pAbs B y ell p := by
  unfold bAbs
  by_cases hbb : bondInBlock y ell b
  · rw [if_pos hbb]
    obtain ⟨hx, hshiftb⟩ := hbb
    by_cases h1 : b.2 = 1
    · have hshift1 : periodicLatticeShift b.1 1 ∈ blockOf y ell := by rw [← h1]; exact hshiftb
      have hsteps : steps y ell b = (Finset.range ((b.1 0).val - (y 0).val)).image
          (fun k => (zK y b.1 k,
            (⟨((0:Fin 3),(1:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections))) := by
        unfold steps; rw [if_pos ⟨hx, hshiftb⟩, if_pos h1]
      rw [hsteps]
      have hinj : ∀ k1 ∈ Finset.range ((b.1 0).val - (y 0).val),
          ∀ k2 ∈ Finset.range ((b.1 0).val - (y 0).val),
          (zK y b.1 k1, (⟨((0:Fin 3),(1:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections))
            = (zK y b.1 k2, ⟨((0:Fin 3),(1:Fin 3)), by decide⟩) → k1 = k2 := by
        intro k1 hk1 k2 hk2 heq
        rw [Finset.mem_range] at hk1 hk2
        have hsite : zK y b.1 k1 = zK y b.1 k2 := (Prod.mk.injEq _ _ _ _).mp heq |>.1
        have e1 : (zK y b.1 k1 0).val = (y 0).val + k1 :=
          zK_coord0_eq_of_le y b.1 (by omega) (b.1 0).isLt
        have e2 : (zK y b.1 k2 0).val = (y 0).val + k2 :=
          zK_coord0_eq_of_le y b.1 (by omega) (b.1 0).isLt
        have e3 : (zK y b.1 k1 0).val = (zK y b.1 k2 0).val := by rw [hsite]
        omega
      rw [Finset.sum_image hinj]
      have hconv : ∑ k ∈ Finset.range ((b.1 0).val - (y 0).val),
            pAbs B y ell (zK y b.1 k,
              (⟨((0:Fin 3),(1:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections))
          = ∑ k ∈ Finset.range ((b.1 0).val - (y 0).val),
            |curlValue B (zK y b.1 k, ⟨((0:Fin 3),(1:Fin 3)), by decide⟩)| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        unfold pAbs
        rw [if_pos (plaq01_mem hstrict1 y b.1 hx hshift1 (by omega))]
      rw [hconv, dir1_bond_eq_sum hstrict0 hstrict1 B hB y hy b h1 ⟨hx, hshiftb⟩]
      exact Finset.abs_sum_le_sum_abs _ _
    · by_cases h2 : b.2 = 2
      · have hshift2 : periodicLatticeShift b.1 2 ∈ blockOf y ell := by rw [← h2]; exact hshiftb
        have hsteps : steps y ell b =
            (Finset.range ((b.1 0).val - (y 0).val)).image
                (fun k => (zK y b.1 k,
                  (⟨((0:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)))
            ∪ (Finset.range ((b.1 1).val - (y 1).val)).image
                (fun k => (wK y b.1 k,
                  (⟨((1:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections))) := by
          unfold steps; rw [if_pos ⟨hx, hshiftb⟩, if_neg h1, if_pos h2]
        rw [hsteps]
        have hdisj : Disjoint
            ((Finset.range ((b.1 0).val - (y 0).val)).image
                (fun k => (zK y b.1 k,
                  (⟨((0:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections))))
            ((Finset.range ((b.1 1).val - (y 1).val)).image
                (fun k => (wK y b.1 k,
                  (⟨((1:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections)))) := by
          rw [Finset.disjoint_left]
          intro q hqA hqB
          rw [Finset.mem_image] at hqA hqB
          obtain ⟨k, _, hk⟩ := hqA
          obtain ⟨k', _, hk'⟩ := hqB
          rw [← hk] at hk'
          exact absurd ((Prod.mk.injEq _ _ _ _).mp hk').2 (by decide)
        rw [Finset.sum_union hdisj]
        have hinjA : ∀ k1 ∈ Finset.range ((b.1 0).val - (y 0).val),
            ∀ k2 ∈ Finset.range ((b.1 0).val - (y 0).val),
            (zK y b.1 k1, (⟨((0:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections))
              = (zK y b.1 k2, ⟨((0:Fin 3),(2:Fin 3)), by decide⟩) → k1 = k2 := by
          intro k1 hk1 k2 hk2 heq
          rw [Finset.mem_range] at hk1 hk2
          have hsite : zK y b.1 k1 = zK y b.1 k2 := (Prod.mk.injEq _ _ _ _).mp heq |>.1
          have e1 : (zK y b.1 k1 0).val = (y 0).val + k1 :=
            zK_coord0_eq_of_le y b.1 (by omega) (b.1 0).isLt
          have e2 : (zK y b.1 k2 0).val = (y 0).val + k2 :=
            zK_coord0_eq_of_le y b.1 (by omega) (b.1 0).isLt
          have e3 : (zK y b.1 k1 0).val = (zK y b.1 k2 0).val := by rw [hsite]
          omega
        have hinjB : ∀ k1 ∈ Finset.range ((b.1 1).val - (y 1).val),
            ∀ k2 ∈ Finset.range ((b.1 1).val - (y 1).val),
            (wK y b.1 k1, (⟨((1:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections))
              = (wK y b.1 k2, ⟨((1:Fin 3),(2:Fin 3)), by decide⟩) → k1 = k2 := by
          intro k1 hk1 k2 hk2 heq
          rw [Finset.mem_range] at hk1 hk2
          have hsite : wK y b.1 k1 = wK y b.1 k2 := (Prod.mk.injEq _ _ _ _).mp heq |>.1
          have e1 : (wK y b.1 k1 1).val = (y 1).val + k1 :=
            wK_coord1_eq_of_le y b.1 (by omega) (b.1 1).isLt
          have e2 : (wK y b.1 k2 1).val = (y 1).val + k2 :=
            wK_coord1_eq_of_le y b.1 (by omega) (b.1 1).isLt
          have e3 : (wK y b.1 k1 1).val = (wK y b.1 k2 1).val := by rw [hsite]
          omega
        rw [Finset.sum_image hinjA, Finset.sum_image hinjB]
        have hconvA : ∑ k ∈ Finset.range ((b.1 0).val - (y 0).val),
              pAbs B y ell (zK y b.1 k,
                (⟨((0:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections))
            = ∑ k ∈ Finset.range ((b.1 0).val - (y 0).val),
              |curlValue B (zK y b.1 k, ⟨((0:Fin 3),(2:Fin 3)), by decide⟩)| := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          unfold pAbs
          rw [if_pos (plaq02_mem hstrict2 y b.1 hx hshift2 (by omega))]
        have hconvB : ∑ k ∈ Finset.range ((b.1 1).val - (y 1).val),
              pAbs B y ell (wK y b.1 k,
                (⟨((1:Fin 3),(2:Fin 3)), by decide⟩ : PeriodicPlaquetteDirections))
            = ∑ k ∈ Finset.range ((b.1 1).val - (y 1).val),
              |curlValue B (wK y b.1 k, ⟨((1:Fin 3),(2:Fin 3)), by decide⟩)| := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          unfold pAbs
          rw [if_pos (plaq12_mem hstrict2 y b.1 hx hshift2 (by omega))]
        rw [hconvA, hconvB, dir2_bond_eq_sum hstrict0 hstrict2 B hB y hy b h2 ⟨hx, hshiftb⟩]
        exact le_trans (abs_add_le _ _)
          (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
      · have hb0 : b.2 = 0 := by
          have := b.2.isLt
          have h0 : b.2.val ≠ 1 := fun h => h1 (Fin.ext h)
          have h0' : b.2.val ≠ 2 := fun h => h2 (Fin.ext h)
          apply Fin.ext; omega
        have hBb : B b = 0 := dir0_bond_eq_zero hstrict0 B hB y hy b hb0 ⟨hx, hshiftb⟩
        have hsteps : steps y ell b = ∅ := by
          unfold steps; rw [if_pos ⟨hx, hshiftb⟩, if_neg h1, if_neg h2]
        rw [hsteps, hBb]; simp
  · rw [if_neg hbb]
    have hsteps : steps y ell b = ∅ := by unfold steps; rw [if_neg hbb]
    rw [hsteps]; simp

/-! ### The headline: CMP96 `(2.123)` block-wide, constant `3·ell³` (block-size-only). -/

/-- **CMP96 `(2.123)`, the block-wide headline** (U=1 real-valued sector, `d=3`, `L=ell`):
`Σ_{b⊂B(y)} |B(b)|² ≤ 3·ell³ · Σ_{p⊂B(y)} |(∂₁B)(p)|²` for `B` admissible for every block
(`admissibleSubspaceInter`), on any coarse-lattice center `y`. The constant `3·ell³ = d·L^d` is
VOLUME-INDEPENDENT (no ambient `L μ` factor). Instantiates
`Migration.BlockPoincare.block_poincare_core'` (its correctness is now load-bearing for this
concrete theorem). Ingredient 1 of the 3-piece fine chain `[(2.123)+(2.128)+(2.118)]`; does NOT
discharge `coerc_u_main`.

## Scope of the hypotheses, stated precisely (do NOT read this as an unconditional torus-(2.123))

* **`hstrict0/1/2` (`ell < L μ + 1` on each axis) is a LOAD-BEARING no-wrap hypothesis, not mere
  book-keeping.** It is a genuine restriction NOT stated beside (2.123) in the source. Without it —
  e.g. a single-block torus `ell = L μ + 1` — a direction-`0` bond can wrap around the periodic
  torus back into the block; there is then an admissible, curl-free `B` supported on such a wrap
  "sheet" with `LHS > 0` while `RHS = 0`, which REFUTES the inequality. So the theorem is not an
  unconditional periodic-torus (2.123); `hstrict` is the exact hypothesis excluding that wrap sheet
  (the `noWrap_of_bondInBlock` failure mode, §2). Bałaban's own RG-hierarchy regime (`ell ≪ L`,
  more than one block per axis) satisfies it.
* **The hypotheses are DELIBERATELY GENERAL and admit DEGENERATE / TRUNCATED blocks, for which the
  inequality holds TRIVIALLY.** `hstrict + y ∈ CoarseLattice L ell` does NOT pin a full-cardinality
  `ell³` block: `ell = 0` makes both sums empty (`0 ≤ 0`); and when `ell ∤ (L μ + 1)`, a coarse
  center near the far corner (e.g. side-`5` axis, `ell = 2`, center coordinate `4`) has `blockOf`
  boundary-truncated below `ell³` sites — the inequality still holds there, trivially. The theorem
  is thus MORE GENERAL than "full interior block"; these degenerate cases are kept in scope on
  purpose (the theorem is neither narrowed nor weakened to exclude them).
* **The intended / load-bearing regime is a FULL INTERIOR block, where the inequality is
  NON-VACUOUS.** `block_poincare_nonvacuous` (§7) exhibits this in-tree: a nonzero admissible
  `innerConfig` on `witnessL`/`witnessY`/`witnessEll` (`ell = 2`, full block) for which
  `0 < LHS ≤ 3·ell³·RHS` with `0 < RHS` — a genuine positive-≤-positive instance, not `0 ≤ 0`.
* **A source-exact restatement of (2.123)** would additionally assume `0 < ell` and a full-fit
  condition (`ell ∣ (L μ + 1)`, or equivalently `(y μ).val + ell ≤ L μ + 1` for an interior block).
  These are intentionally NOT added as hypotheses here — the theorem is stated in its more general,
  still-true form; this note documents precisely what the hypotheses do and do not pin. -/
theorem block_poincare {L : PeriodicLatticeExtent} {ell : ℕ}
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell) :
    ∑ b ∈ bondsInBlock y ell, (B b) ^ 2
      ≤ 3 * (ell : ℝ) ^ 3 * ∑ p ∈ plaqsInBlock y ell, (curlValue B p) ^ 2 := by
  have hcore := AdalyFormal.Migration.BlockPoincare.block_poincare_core'
    (steps y ell) (bAbs B y ell) (pAbs B y ell) (2 * ell) (ell * ell)
    (steps_hK y) (steps_hM y)
    (fun b => by unfold bAbs; split <;> [exact abs_nonneg _; exact le_refl 0])
    (fun p => by unfold pAbs; split <;> [exact abs_nonneg _; exact le_refl 0])
    (steps_hTri hstrict0 hstrict1 hstrict2 B hB y hy)
  rw [bondAbs_sq_sum, plaqAbs_sq_sum] at hcore
  have hpnn : (0 : ℝ) ≤ ∑ p ∈ plaqsInBlock y ell, (curlValue B p) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hconst : ((2 * ell : ℕ) : ℝ) * ((ell * ell : ℕ) : ℝ) ≤ 3 * (ell : ℝ) ^ 3 := by
    have h : ((2 * ell : ℕ) : ℝ) * ((ell * ell : ℕ) : ℝ) = 2 * (ell : ℝ) ^ 3 := by push_cast; ring
    rw [h]; nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) ell) 3]
  exact le_trans hcore (mul_le_mul_of_nonneg_right hconst hpnn)

#print axioms steps_recover
#print axioms steps_hK
#print axioms steps_hM
#print axioms steps_hTri
#print axioms block_poincare

/-! ## §7. IN-TREE NON-VACUITY WITNESS for `block_poincare` (folded from the prosecution exhibit
`compute/prosecute_2123/NonVacuity.lean`).

`block_poincare` is quantified over ALL admissible `B`; on its own it exhibits no single instance
where BOTH sides are strictly positive — an all-zero `B`, or a degenerate `ell = 0` block, satisfies
it as `0 ≤ 0`. This section closes that gap CONCRETELY and in-file: a nonzero `innerConfig`,
genuinely in `admissibleSubspaceInter witnessL witnessEll`, carrying a direction-`1` bond STRICTLY
INSIDE the full interior block `blockOf witnessY witnessEll` (side `ell = 2` on the witness torus).
`block_poincare_nonvacuous` applies the headline to it and reads off `0 < LHS ≤ 3·ell³·RHS` with
`0 < RHS` — a genuine positive-≤-positive instance, not `0 ≤ 0`.

The witness bond is direction-`1` (Lean index), base `(1,0,0)`, whose forward shift is `(1,1,0)`;
both endpoints have every coordinate in `{0,1} ⊂ blockOf witnessY 2`, so it is strictly inside the
block, yet it is NOT the direction-`0`/`z₀`-forced-zero class (its base coordinate `0` is `1 ≠ 0 =
(witnessY 0).val`), so it is not directly annihilated by (2.121) at `y = witnessY`. -/

section NonVacuityWitness
-- Matches the raised recursion budget the standalone exhibit
-- `compute/prosecute_2123/NonVacuity.lean` used for its brute-force `decide`s (and their linters).
set_option maxRecDepth 4000

/-- A direction-`1` (Lean idx) bond, base `(1,0,0)`, fully inside `blockOf witnessY witnessEll`. -/
def innerBond : Bond witnessL :=
  ((fun μ => if μ.val = 0 then (1 : Fin 4) else (0 : Fin 4)), (1 : Fin 3))

theorem innerBond_in_block : bondInBlock witnessY witnessEll innerBond := by
  unfold bondInBlock innerBond
  decide

/-- The indicator configuration supported on `innerBond` alone. -/
noncomputable def innerConfig : Bond witnessL → ℝ := fun e => if e = innerBond then 1 else 0

theorem innerConfig_ne_zero : innerConfig ≠ 0 := by
  intro h
  have : innerConfig innerBond = (0 : Bond witnessL → ℝ) innerBond := by rw [h]
  simp [innerConfig] at this

/-- `innerBond` survives EVERY `(y,x)` staircase constraint globally — brute-force `decide`, the
fact that lets `innerConfig` sit in `admissibleSubspaceInter`. -/
theorem innerBond_not_mem_any_staircase :
    ∀ y x : PeriodicLatticeSite witnessL,
      y ∈ CoarseLattice witnessL witnessEll → x ∈ blockOf y witnessEll →
      innerBond ∉ staircasePath y x := by
  decide

theorem innerConfig_mem_inter :
    innerConfig ∈ admissibleSubspaceInter witnessL witnessEll := by
  rw [mem_admissibleSubspaceInter]
  intro y hy x hx b hb
  simp only [innerConfig]
  rw [if_neg]
  intro heq
  subst heq
  exact innerBond_not_mem_any_staircase y x hy hx hb

/-- The LHS block-bond sum for `innerConfig` is strictly nonzero (`innerBond` contributes `1`). -/
theorem lhs_nonzero :
    ∑ b ∈ bondsInBlock witnessY witnessEll, (innerConfig b) ^ 2 ≠ 0 := by
  have hmem : innerBond ∈ bondsInBlock witnessY witnessEll := by
    rw [mem_bondsInBlock]; exact innerBond_in_block
  have hval : innerConfig innerBond = 1 := by simp [innerConfig]
  have : (0:ℝ) < ∑ b ∈ bondsInBlock witnessY witnessEll, (innerConfig b) ^ 2 := by
    apply Finset.sum_pos'
    · intro i _; positivity
    · exact ⟨innerBond, hmem, by rw [hval]; norm_num⟩
  linarith

/-- **The capstone: `block_poincare` is NON-VACUOUS in-tree.** Applying the headline to the concrete
admissible `innerConfig` on the full interior block `blockOf witnessY witnessEll` (`ell = 2`) yields
a `0 < LHS ≤ 3·ell³·RHS` instance in which BOTH sides are strictly positive — the inequality is a
genuine positive-≤-positive statement here, not the trivial `0 ≤ 0`. The strict positivity of the
RHS is FORCED by the headline itself: a strictly positive LHS with a nonnegative constant cannot be
bounded by a zero RHS. -/
theorem block_poincare_nonvacuous :
    (0 : ℝ) < ∑ b ∈ bondsInBlock witnessY witnessEll, (innerConfig b) ^ 2 ∧
      ∑ b ∈ bondsInBlock witnessY witnessEll, (innerConfig b) ^ 2
        ≤ 3 * (witnessEll : ℝ) ^ 3
            * ∑ p ∈ plaqsInBlock witnessY witnessEll, (curlValue innerConfig p) ^ 2 ∧
      (0 : ℝ) < ∑ p ∈ plaqsInBlock witnessY witnessEll, (curlValue innerConfig p) ^ 2 := by
  have hlhs_pos : (0 : ℝ) < ∑ b ∈ bondsInBlock witnessY witnessEll, (innerConfig b) ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Ne.symm lhs_nonzero)
  have hbp := block_poincare (L := witnessL) (ell := witnessEll)
    (by decide) (by decide) (by decide) innerConfig innerConfig_mem_inter witnessY witnessY_coarse
  refine ⟨hlhs_pos, hbp, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hrhs0 : ∑ p ∈ plaqsInBlock witnessY witnessEll, (curlValue innerConfig p) ^ 2 = 0 :=
    le_antisymm hcon (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [hrhs0, mul_zero] at hbp
  linarith

#print axioms innerBond_in_block
#print axioms innerConfig_ne_zero
#print axioms innerBond_not_mem_any_staircase
#print axioms innerConfig_mem_inter
#print axioms lhs_nonzero
#print axioms block_poincare_nonvacuous

end NonVacuityWitness

end AdalyFormal.Balaban.BlockPoincare
