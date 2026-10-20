/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Blocks
import Mathlib.Tactic.IntervalCases

/-!
# The scale tower `Ω^(0), Ω^(1), …, Ω^(K)`

Phase-0 REFORM_PROGRAM definitions layer, `PHASE0_DEFS_PLAN.md` item **A2**. Stands alone: no
import of `Target.ClayStatement`.

## Source pin

`corpus/pages/CMP98_p24.md` (`verification_status: adjudicated`), the sentence introducing eq.
(43): *"and if `k`-th order averaging `Ū^k` is defined at bonds of `Ω^(k)`, then [eq. (43) defines
`Ū^{k+1}` on `Ω^(k+1)`]"* — the iteration is over a finite (or, in the paper, unboundedly
extensible) TOWER of lattices `Ω^(0) ⊃ Ω^(1) ⊃ …`, each level's block map coarsening the previous
level's sites into the next level's centers. `PHASE0_DEFS_PLAN.md`'s **C1** flags the exact
embedding of this tower into `ℤ^d` as still open (needs a fuller `CMP98`/`CMP109` read); this
module therefore builds the tower as an ABSTRACT sequence of `BlockGeometry`-shaped coarsening
steps, deferring the concrete embedding exactly as the plan recommends for A2 ("needs A1 first").

## Scope

One object: a finite tower of `K` coarsening steps, each satisfying `Blocks.lean`'s pinned
cardinality law `|B(y)| = L^d`, with the SAME `L, d` at every step (Balaban's `L` and `d` are fixed
constants of the whole construction, not step-dependent — no page pins a step-dependent `L`, and
eq. (43) reuses the same block map shape at every order). No theorem about the tower beyond the
witness computation below (closing sorrys about the tower's own properties, e.g. that iterating
`averageAt` along it defines a well-formed order-`k` average, is `IteratedAveraging.lean` /
Phase-1 `Spine.lean` work, not this file's).
-/

namespace AdalyFormal.Balaban

/-- **Scale ladder**: `K` nested RG coarsening steps `Level (j+1) → Finset (Level j)` for
`j = 0, …, K-1`, each satisfying `Blocks.lean`'s block-cardinality law `|B_j(c)| = L^d` with a
COMMON `L, d` across all levels (CMP98 p.24's `L` is a fixed construction parameter, not indexed by
`k`). `Level 0` is the finest lattice `Ω^(0)`; `Level K` is the coarsest level actually specified.
`Level` is total on `ℕ` (not merely `Fin (K+1)`) purely so the structure typechecks without
dependent `Fin`-indexed families; only `j < K` carries any axiom, so levels `> K` carry no content
and may be filled with anything of the right shape (see the witness below, which reuses a
1-element placeholder past its own `K`). -/
structure ScaleLadder where
  /-- The site/center type at RG level `j`; `Level 0` is the finest lattice `Ω^(0)`. -/
  Level : ℕ → Type
  /-- Every level is finite. -/
  levelFintype : ∀ j, Fintype (Level j)
  /-- Every level has decidable equality (needed for `Finset`-valued blocks). -/
  levelDecEq : ∀ j, DecidableEq (Level j)
  /-- Common RG block side length across all specified levels. -/
  L : ℕ
  /-- Common lattice dimension across all specified levels. -/
  d : ℕ
  /-- Number of coarsening steps actually specified by this ladder (CMP98 eq. (43) iterates this
  indefinitely in the source; a Lean witness must fix a fold depth). -/
  K : ℕ
  /-- The order-`j+1` block map `Ω^(j+1) → Finset (Ω^(j))`, for each specified step `j < K`. -/
  block : (j : ℕ) → j < K → Level (j + 1) → Finset (Level j)
  /-- Every specified step satisfies `Blocks.lean`'s pinned cardinality law. -/
  card_block : ∀ j (h : j < K) (c : Level (j + 1)), haveI := levelFintype j;
    haveI := levelDecEq j; (block j h c).card = L ^ d

attribute [instance] ScaleLadder.levelFintype ScaleLadder.levelDecEq

/-- Step `j`'s data repackaged as a `BlockGeometry (Level j) (Level (j+1))`, when `j < K` — this
is exactly `Blocks.lean`'s object, one per rung of the tower. -/
def ScaleLadder.geometryAt (ladder : ScaleLadder) (j : ℕ) (h : j < ladder.K) :
    BlockGeometry (ladder.Level j) (ladder.Level (j + 1)) where
  B := ladder.block j h
  L := ladder.L
  d := ladder.d
  card_block := ladder.card_block j h

/-! ## L7 witness: a 2-step, `L=2, d=1` tower

Reuses `Blocks.lean`'s own witness geometry (see `Balaban/Probes.lean` for the shared numeric
data): `Ω^(0) = Fin 4` (four fine sites), `Ω^(1) = Fin 2` (two blocks of two sites each,
`|B_0(y)| = 2 = 2^1`), `Ω^(2) = Fin 1` (one top block of the two level-1 "sites",
`|B_1(y)| = 2 = 2^1`). Levels beyond `K = 2` are filled with `Fin 1` placeholders carrying no
axiom (`j ≥ K` is never constrained by `card_block`). -/

abbrev witnessLevel : ℕ → Type := fun j =>
  match j with
  | 0 => Fin 4
  | 1 => Fin 2
  | _ => Fin 1

instance : ∀ j, Fintype (witnessLevel j)
  | 0 => inferInstanceAs (Fintype (Fin 4))
  | 1 => inferInstanceAs (Fintype (Fin 2))
  | _ + 2 => inferInstanceAs (Fintype (Fin 1))

instance : ∀ j, DecidableEq (witnessLevel j)
  | 0 => inferInstanceAs (DecidableEq (Fin 4))
  | 1 => inferInstanceAs (DecidableEq (Fin 2))
  | _ + 2 => inferInstanceAs (DecidableEq (Fin 1))

def witnessBlock0 : Fin 2 → Finset (Fin 4)
  | 0 => {0, 1}
  | 1 => {2, 3}

def witnessBlock1 : Fin 1 → Finset (Fin 2)
  | 0 => {0, 1}

/-- Total block function on `ℕ` (structural match, no dependence on the `j < K` proof) so that
`card_block`'s per-case goals reduce definitionally instead of being blocked behind a
`j < K`-indexed `dite`/`Eq.ndrec`. Levels `≥ 2` are unconstrained by `card_block` (never reached
under `h : j < K = 2`), so the empty placeholder is harmless. -/
def witnessBlockFn : (j : ℕ) → witnessLevel (j + 1) → Finset (witnessLevel j)
  | 0 => witnessBlock0
  | 1 => witnessBlock1
  | _ + 2 => fun _ => ∅

/-- The 2-step `L=2, d=1` witness tower: a nontrivial model of `ScaleLadder` computed in-kernel. -/
def witnessScaleLadder : ScaleLadder where
  Level := witnessLevel
  levelFintype := inferInstance
  levelDecEq := inferInstance
  L := 2
  d := 1
  K := 2
  block j _ := witnessBlockFn j
  card_block j h := by
    match j, h with
    | 0, _ => decide
    | 1, _ => decide

/-- The witness tower's step-0 block sizes match the pinned law by direct computation. -/
example : (witnessBlock0 0).card = 2 ^ 1 := by decide

/-- The witness tower's step-1 block size matches the pinned law by direct computation. -/
example : (witnessBlock1 0).card = 2 ^ 1 := by decide

end AdalyFormal.Balaban
