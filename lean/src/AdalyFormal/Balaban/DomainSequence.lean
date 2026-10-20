/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Target.ClayStatement
import AdalyFormal.Balaban.AdmissibleSubspace

set_option autoImplicit false
set_option maxRecDepth 4000

/-!
# `Λ_k` — a single coarsest-scale big-block domain, CMP96 (2.1)-(2.4)

## Source pin (image-verified for THIS module, LAW-11/20, not merely inherited)

`compute/balaban_su2_papers/balaban_CMP96_1984_propagators_II.pdf`, printed p.224
(`corpus/tools/page_offsets.json`, `CMP96`, offset 222, `constant_verified: true`). Rendered by a
prior lane at `compute/domain_sequence_spec/renders/CMP96_p224-02.png`
(`sha256 f9aa9408ae14fd5f564f22b7989efeb51b38ab4a628ebb3256abea5f29fbe877`, re-confirmed present on
disk and RE-READ directly by this module's author, not taken on the prior lane's transcription
alone — the printed header "224 / T. Bałaban" is visible in the image). **(2.1)-(2.4)**, verbatim:

> `Ω_1 ⊃ Ω_2 ⊃ … ⊃ Ω_k, Ω_j ⊂ T_η, j = 1,2,…,k,` **(2.1)**, which satisfy: `Ω_j = B^j(Ω_j^{(j)})`,
> `Ω_j^{(j)} ⊂ T_{L^jη}^{(j)}` "and it is a sum of big blocks", `(L^jη)^{-1} dist(Ω_j^c, Ω_{j+1}) >
> RM`, "`M` is a size of big blocks and `R` is a big positive integer which will be fixed later."
> **(2.2)**. `Λ_j = Ω_j^{(j)} ∖ Ω_{j+1}^{(j)}, j=1,…,k−1, Λ_k = Ω_k^{(k)}, Λ_0 = Ω_1^c` **(2.3)**.
> `Ω_1 = ⋃_{j=1}^k B^j(Λ_j), T = ⋃_{j=0}^k B^j(Λ_j)`, where `B^0(Λ_0) = Λ_0`. **(2.4)**.
> "Let us notice that we admit the case when some domains `Ω_j` are equal to `T_η`, for example
> `Ω_j = T_η` for `j=1,2,…,l, l≤k`."

Confirmed by direct re-read: the gauge field `A` first appears only in (2.5), AFTER these
definitions, in the separate variational problem — `U`/`A` never appears in (2.1)-(2.4) or their
surrounding prose, directly OR via a domain-of-validity restriction. Two independent prior passes
(`compute/domain_sequence_spec/OMEGA_SPEC.md`, `compute/kimi_omega_gate/VERDICT.md`, a
de-correlated second-family gate) reached the same reading; this module's own direct re-read of the
rendered page (above) is a THIRD independent confirmation, not a citation of either.

## What this module builds: `Λ_k`, single fixed scale, honestly scoped

Per the dispatch and per `OMEGA_SPEC.md` §5 / `VERDICT.md` Claim 3: stating CMP99b's one-shell
problem `(3.155)-(3.156)` (`corpus/pages/CMP99b_p427.md`, `CMP99b_p428.md`, both
`verification_status: adjudicated`) needs `Λ ⊂ Λ_k = Ω_k^{(k)}` with the margin `dist(Λ, Λ_k^c) >
RM` — a SINGLE instance of (2.2)'s free-choice-plus-margin rule, specialized to `j = k`, NOT the
full recursive tower `Ω_1 ⊃ … ⊃ Ω_k` across every level `j = 1,…,k`. This module builds exactly
that single instance, on ONE fixed periodic lattice (no multiscale rescaling tower `T_{L^jη}^{(j)}`
— `PHASE0_DEFS_PLAN.md` item **C1**, the `ScaleLadder ↔ PeriodicLatticeSite` reconciliation, is a
separately-flagged, larger, cross-cutting task and is correctly bypassed here, per `OMEGA_SPEC.md`
§5 step 2's own recommendation). This is a genuine, disclosed SPECIALIZATION (single scale, not the
full `{Ω_j}` sequence), not an opaque stand-in: every object below is built from actual (2.1)-(2.4)
content (nesting, "sum of big blocks", the `RM` margin), and `U` appears in NO type or definition
in this file.

**What is deliberately NOT built here** (named, not silently dropped): the multiscale blow-up maps
`B^j` across levels `j = 1,…,k` (only the single-level block union `B(y)` — CMP96's `B^j` restricted
to one level — is needed and built, via `AdmissibleSubspace.blockOf`, reused per LAW-19); the
indexing shift CMP99b makes to the SAME construction (`Ω_0` prepended, per
`compute/kimi_omega_gate/VERDICT.md` F3) — irrelevant to `Λ_k = Ω_k^{(k)}` itself, since `Λ_k`'s
definition is unchanged by that shift, but flagged here so a later consumer does not silently
assume CMP96's own `Λ_0 = Ω_1^c` indexing applies verbatim to a CMP99b-context sequence; and `Ax(y)`,
`Q_1`, and the `U`-dependent operator data `(G_1, H_1, D̃⁽²⁾, J, a, Q)` that `(3.156)` ALSO needs
(per `VERDICT.md` Claims 2-3's caveat) — out of scope for this dispatch, which is
`Λ_k` only.

## The `L`/`M` naming collision (flagged by `compute/kimi_omega_gate/VERDICT.md`), and how this file
avoids it

`Balaban/Blocks.lean`'s `BlockGeometry` structure has a field named `L` (documented there as "RG
block side length") whose INTENDED VALUE, were it instantiated for this construction, would be
CMP96's `M` ("a size of big blocks", (2.2)) — a DIFFERENT constant from CMP96's own `L` (the
rescaling ratio between coarsening levels, never separately tracked in this single-scale module).
**This module does NOT instantiate `BlockGeometry` at all** — it builds `Λ_k` directly via
`Finset.biUnion` over `AdmissibleSubspace.blockOf` (already reusable at the needed shape, LAW-19),
sidestepping the collision entirely rather than assigning a mismatched value to a misleadingly-named
field. The constants used below are named `bigBlockSizeK` / `bigBlockSizeInner` (CMP96's `M`,
applied per-domain — CMP99b p.408 already factors a single nominal `M` into composite per-domain
constants such as `M = K·R₀·M₀`, so per-domain block sizes are already the source's own practice,
not a modeling liberty taken here) and `marginBound` (CMP96's `R·M` as a single product, since only
the product enters the margin condition (2.2) — `R` and `M` are not separately re-derived as fields
of the bound itself).

## Periodic-aware distance — closing the gap `compute/kimi_omega_gate/VERDICT.md` names explicitly

`AdmissibleSubspace.l1dist` (`AdmissibleSubspace.lean:661`) is `∑ ν, natAbsDiff (s ν).val (t ν).val`
— a **coordinate-wise raw `ℓ¹` distance with NO wraparound**. Since `PeriodicLatticeSite` is
explicitly a torus (`Fin (L μ + 1)` per coordinate, periodic by construction — see
`periodicLatticeShift`, `Target/ClayStatement.lean`), a margin condition "near the torus boundary"
computed with `l1dist` can be WRONG: two sites can be `l1dist`-far apart yet adjacent on the torus.
`periodicSiteDist` below is the wraparound-corrected replacement, and §6's mutation theorem exhibits
a concrete pair where the two disagree about whether a margin bound is satisfied — this is not a
cosmetic difference, it changes which verdict the margin CHECK returns (S82/OPS-3 discipline).
-/

namespace AdalyFormal.Balaban.DomainSequence

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (natAbsDiff l1dist blockOf mem_blockOf inBlock)

variable {Lat : PeriodicLatticeExtent}

/-! ## §1. A periodic-aware distance on `PeriodicLatticeSite` -/

/-- Periodic (wraparound) distance on a single coordinate axis of extent `n+1` (i.e. the cycle
`ℤ/(n+1)ℤ`, matching `Fin (n+1)`): the shorter of the two arcs between `a` and `b`. -/
def periodicCoordDist (n : ℕ) (a b : Fin (n + 1)) : ℕ :=
  min (natAbsDiff a.val b.val) (n + 1 - natAbsDiff a.val b.val)

/-- Periodic (wraparound-corrected) `ℓ¹`-distance between two lattice sites — the object
`AdmissibleSubspace.l1dist` does NOT provide (see the module docstring). Config-independent: no
`U` appears anywhere in the definition. -/
def periodicSiteDist (s t : PeriodicLatticeSite Lat) : ℕ :=
  ∑ ν : Fin 3, periodicCoordDist (Lat ν) (s ν) (t ν)

@[simp] theorem periodicCoordDist_self (n : ℕ) (a : Fin (n + 1)) :
    periodicCoordDist n a a = 0 := by
  unfold periodicCoordDist natAbsDiff
  omega

@[simp] theorem periodicSiteDist_self (s : PeriodicLatticeSite Lat) :
    periodicSiteDist s s = 0 := by
  unfold periodicSiteDist
  simp

theorem periodicCoordDist_comm (n : ℕ) (a b : Fin (n + 1)) :
    periodicCoordDist n a b = periodicCoordDist n b a := by
  unfold periodicCoordDist natAbsDiff
  omega

theorem periodicSiteDist_comm (s t : PeriodicLatticeSite Lat) :
    periodicSiteDist s t = periodicSiteDist t s := by
  unfold periodicSiteDist
  exact Finset.sum_congr rfl (fun ν _ => periodicCoordDist_comm _ (s ν) (t ν))

/-- `periodicSiteDist` is never bigger than the naive (non-periodic) `l1dist` — the periodic
correction can only shorten a distance, never lengthen it, since it is a `min` against the naive
value. A basic sanity fact used by `l1dist_ne_periodicSiteDist` below to show the two genuinely
diverge (a strict `<` occurs there, not merely this `≤`). -/
theorem periodicSiteDist_le_l1dist (s t : PeriodicLatticeSite Lat) :
    periodicSiteDist s t ≤ l1dist s t := by
  unfold periodicSiteDist l1dist
  apply Finset.sum_le_sum
  intro ν _
  unfold periodicCoordDist
  exact min_le_left _ _

/-! ## §2. Big blocks and `Λ_k` (CMP96 (2.2)-(2.4), single fixed scale, reusing
`AdmissibleSubspace.blockOf`) -/

/-- `B(y)`, CMP96's single-level block map, reused verbatim from `AdmissibleSubspace.blockOf`
(LAW-19) under a name matching this module's own "big block" vocabulary. -/
def bigBlock (y : PeriodicLatticeSite Lat) (M : ℕ) : Finset (PeriodicLatticeSite Lat) :=
  blockOf y M

theorem mem_bigBlock {y x : PeriodicLatticeSite Lat} {M : ℕ} :
    x ∈ bigBlock y M ↔ inBlock y M x :=
  mem_blockOf

/-- `B^j(Λ')`, CMP96 (2.2)/(2.4)'s block-union / blow-up map, restricted to ONE level (the
multiscale composition across `j = 1,…,k` is out of scope, see the module docstring) — a domain
"which is a sum of big blocks" (2.2) built from a FREELY CHOSEN finite set of block centers. -/
def bigBlockUnion (centers : Finset (PeriodicLatticeSite Lat)) (M : ℕ) :
    Finset (PeriodicLatticeSite Lat) :=
  centers.biUnion (fun y => bigBlock y M)

theorem mem_bigBlockUnion {centers : Finset (PeriodicLatticeSite Lat)} {M : ℕ}
    {x : PeriodicLatticeSite Lat} :
    x ∈ bigBlockUnion centers M ↔ ∃ y ∈ centers, inBlock y M x := by
  unfold bigBlockUnion
  simp [mem_bigBlock]

/-- A genuine, non-degenerate union: `bigBlockUnion` over TWO distinct centers really does union
two blocks, not silently collapse to one — exercising the `biUnion` machinery (2.4) actually needs
for "a sum of big blocks", not merely the single-center case §4/§5 use for their tractable margin
proof. -/
theorem bigBlockUnion_pair (c1 c2 : PeriodicLatticeSite Lat) (M : ℕ) :
    bigBlockUnion ({c1, c2} : Finset (PeriodicLatticeSite Lat)) M
      = bigBlock c1 M ∪ bigBlock c2 M := by
  unfold bigBlockUnion
  simp

/-! ## §3. The margin condition, CMP96 (2.2)'s `(L^jη)^{-1} dist(Ω_j^c, Ω_{j+1}) > RM`, specialized
to `Λ ⊂ Λ_k` (CMP99b p.427's own re-use of the same rule, one step past level `k`) -/

/-- **The margin condition**: every point of `Lambda` is strictly more than `bound` (periodic)
lattice steps from every point OUTSIDE `LambdaK`. Phrased as a bound on ALL pairs rather than as
`bound < <the actual pointwise infimum>` — equivalent for finite sets (the infimum, if the sets
involved are nonempty, is attained by some pair, so the two phrasings are interchangeable), and
avoids threading a separate nonemptiness/infimum-existence argument through every use site. `U`
never appears. -/
def MarginCondition (Lambda LambdaK : Finset (PeriodicLatticeSite Lat)) (bound : ℕ) : Prop :=
  ∀ x ∈ Lambda, ∀ y : PeriodicLatticeSite Lat, y ∉ LambdaK → bound < periodicSiteDist x y

/-! ## §4. `Λ_k` bundled with the nested `Λ` and the margin hypothesis -/

/-- A single instance of CMP96 (2.1)-(2.4)'s free-choice-plus-margin rule, specialized to `Λ ⊂ Λ_k
= Ω_k^{(k)}` (CMP99b p.427). Data: two big-block sizes (§ above, on the `L`/`M` collision), and two
finite sets of block CENTERS — `centersK` builds `Λ_k` (CMP96's `Ω_k^{(k)}`, "a sum of big
blocks"), `centersInner` builds `Λ` (CMP99b p.427's further-nested domain). Config-independent:
`U` occurs nowhere in this structure. -/
structure LambdaKDomain (Lat : PeriodicLatticeExtent) where
  /-- CMP96 (2.2)'s `M`, as applied to `Λ_k`'s own defining blocks. -/
  bigBlockSizeK : ℕ
  /-- CMP96 (2.2)'s `M`, as applied to `Λ`'s defining blocks (may differ — see the module
  docstring on why per-domain block sizes are already the source's own practice). -/
  bigBlockSizeInner : ℕ
  /-- `R·M` of CMP96 (2.2), tracked as a single product (only the product enters the margin
  condition). -/
  marginBound : ℕ
  /-- The freely-chosen block centers building `Λ_k = Ω_k^{(k)}`. -/
  centersK : Finset (PeriodicLatticeSite Lat)
  /-- The freely-chosen block centers building `Λ` (CMP99b p.427: "`Λ` is a union of big
  blocks"). -/
  centersInner : Finset (PeriodicLatticeSite Lat)

namespace LambdaKDomain

variable (o : LambdaKDomain Lat)

/-- `Λ_k = Ω_k^{(k)}`, CMP96 (2.3), built from `o.centersK`. -/
def LambdaK : Finset (PeriodicLatticeSite Lat) := bigBlockUnion o.centersK o.bigBlockSizeK

/-- `Λ`, CMP99b p.427's further-nested domain, built from `o.centersInner`. -/
def Lambda : Finset (PeriodicLatticeSite Lat) := bigBlockUnion o.centersInner o.bigBlockSizeInner

/-- **The (2.2)/(p.427) validity condition**: `Λ ⊂ Λ_k` (nesting) and the `RM` margin between `Λ`
and `Λ_k`'s complement. Both conjuncts are genuinely checkable Props over the concrete data above
— NOT vacuously true (§6 exhibits both a satisfying instance and a violating mutation for each
conjunct). -/
def IsValid : Prop :=
  o.Lambda ⊆ o.LambdaK ∧ MarginCondition o.Lambda o.LambdaK o.marginBound

end LambdaKDomain

/-! ## §5. Non-vacuity: a concrete `LambdaKDomain` satisfying `IsValid`, with a genuine (not
degenerate-empty) `Lambda`

Single-block centers (`bigBlockUnion_pair` above already exercises the genuine multi-center union
case separately, so the margin arithmetic below is kept to the tractable single-block case).
Lattice side `41` (`Lat := fun _ => 40`), outer block `[10,30)` per axis (`bigBlockSizeK = 20`,
center `10`), inner block `[16,24)` per axis (`bigBlockSizeInner = 8`, center `16`), margin bound
`6`. The margin arithmetic below (§5b) shows every axis alone already forces `periodicSiteDist ≥ 7
> 6`, with plenty of room to spare — not a knife-edge coincidence. -/

/-- The witness lattice: side-length-`41` cube in all three directions (generous room; §6's
wraparound mutation deliberately uses a MUCH smaller lattice to make the wraparound shortcut
large relative to the block sizes). -/
def witnessLat : PeriodicLatticeExtent := fun _ => 40

@[simp] theorem witnessLat_eq (μ : Fin 3) : witnessLat μ = 40 := rfl

/-- The outer block's center, `(10,10,10)`. -/
def witnessCenterK : PeriodicLatticeSite witnessLat := fun _ => 10

@[simp] theorem witnessCenterK_val (μ : Fin 3) : (witnessCenterK μ).val = 10 := rfl

/-- The inner block's center, `(16,16,16)`. -/
def witnessCenterI : PeriodicLatticeSite witnessLat := fun _ => 16

@[simp] theorem witnessCenterI_val (μ : Fin 3) : (witnessCenterI μ).val = 16 := rfl

/-- The witness instance: `centersK`/`centersInner` are SINGLETON center sets (a single big
block each) — the minimal but fully genuine case of (2.2)'s "sum of big blocks" (a sum of one
term). `bigBlockUnion_pair` above separately shows the multi-center case is not vacuous either. -/
def witnessDomain : LambdaKDomain witnessLat where
  bigBlockSizeK := 20
  bigBlockSizeInner := 8
  marginBound := 6
  centersK := {witnessCenterK}
  centersInner := {witnessCenterI}

/-- §5a: `LambdaK` genuinely equals the single block `bigBlock witnessCenterK 20` — the `biUnion`
over a singleton reduces correctly (a basic sanity check that the definitions compose as
intended, not a load-bearing theorem in its own right). -/
theorem witnessDomain_LambdaK :
    (witnessDomain).LambdaK = bigBlock witnessCenterK 20 := by
  unfold LambdaKDomain.LambdaK witnessDomain bigBlockUnion
  simp

theorem witnessDomain_Lambda :
    (witnessDomain).Lambda = bigBlock witnessCenterI 8 := by
  unfold LambdaKDomain.Lambda witnessDomain bigBlockUnion
  simp

/-- §5b: nesting. Every axis of `witnessCenterI 8`'s block (`[16,24)`) lies inside
`witnessCenterK 20`'s block (`[10,30)`). -/
theorem witnessDomain_nested : (witnessDomain).Lambda ⊆ (witnessDomain).LambdaK := by
  rw [witnessDomain_LambdaK, witnessDomain_Lambda]
  intro x hx
  rw [mem_bigBlock, inBlock] at hx ⊢
  intro μ
  have h := hx μ
  simp only [witnessCenterI_val, witnessCenterK_val] at h ⊢
  omega

set_option maxHeartbeats 1000000 in
-- reason for change: the `Finset.single_le_sum` unification step over `PeriodicLatticeSite
-- witnessLat` (a `Fin 3 → Fin 41` Pi-type Fintype) exceeds the default heartbeat budget; the
-- proof itself is a fixed finite computation, not a runaway search.
/-- §5c: the margin condition holds with `marginBound = 6`, and every axis ALONE already forces
strictly more than that (the sum over all three non-negative axis-contributions can only be
larger), so this is not a knife-edge numeric coincidence. -/
theorem witnessDomain_margin :
    MarginCondition (witnessDomain).Lambda (witnessDomain).LambdaK (witnessDomain).marginBound := by
  rw [witnessDomain_LambdaK, witnessDomain_Lambda]
  intro x hx y hy
  rw [mem_bigBlock, inBlock] at hx
  have hy' : ¬ inBlock witnessCenterK 20 y := fun h => hy (mem_bigBlock.mpr h)
  rw [inBlock] at hy'
  push Not at hy'
  obtain ⟨μ0, hμ0⟩ := hy'
  have hx0 := hx μ0
  simp only [witnessCenterK_val, witnessCenterI_val] at hμ0 hx0
  have hterm : periodicCoordDist (witnessLat μ0) (x μ0) (y μ0) > 6 := by
    simp only [witnessLat_eq]
    unfold periodicCoordDist natAbsDiff
    omega
  have hsum : periodicCoordDist (witnessLat μ0) (x μ0) (y μ0) ≤ periodicSiteDist x y := by
    unfold periodicSiteDist
    exact Finset.single_le_sum (f := fun ν => periodicCoordDist (witnessLat ν) (x ν) (y ν))
      (fun ν _ => Nat.zero_le _) (Finset.mem_univ μ0)
  change (witnessDomain).marginBound < periodicSiteDist x y
  have hb : (witnessDomain).marginBound = 6 := rfl
  omega

/-- `Lambda` is genuinely nonempty (not a vacuous domain — the centers are in their own blocks). -/
theorem witnessDomain_Lambda_nonempty : (witnessDomain).Lambda.Nonempty := by
  rw [witnessDomain_Lambda]
  refine ⟨witnessCenterI, ?_⟩
  rw [mem_bigBlock, inBlock]
  intro μ
  simp only [witnessCenterI_val]
  omega

/-- **Non-vacuity, assembled**: a concrete `LambdaKDomain` with `IsValid` (genuine nesting +
genuine margin) and a nonempty `Lambda` — `Λ_k` is not an opaque or vacuous stand-in. -/
theorem domainSequence_nonvacuous :
    ∃ o : LambdaKDomain witnessLat, o.IsValid ∧ o.Lambda.Nonempty :=
  ⟨witnessDomain, ⟨witnessDomain_nested, witnessDomain_margin⟩, witnessDomain_Lambda_nonempty⟩

/-! ## §6. Falsifiability — periodicity matters (S82/OPS-3), the nesting/margin conjuncts are
genuinely checkable, and named degeneracies

Three mutation-style theorems, each a concrete PROOF (not a description) that the corresponding
check can and does fail. -/

/-- **§6a — periodicity is load-bearing, not cosmetic.** A concrete pair `(x,y)` on a SMALL torus
(`Lat := fun _ => 9`, side `10`) where the NAIVE (non-periodic) `l1dist` says `9` — comfortably
clearing any bound up to `8` — while the TRUE (periodic) `periodicSiteDist` says `1`: a margin
bound of, say, `4` would be WRONGLY certified satisfied by `l1dist` and CORRECTLY detected as
violated by `periodicSiteDist`. This is the exact gap `compute/kimi_omega_gate/VERDICT.md` names:
`AdmissibleSubspace.l1dist` alone cannot be used for CMP96 (2.2)'s margin condition on a torus. -/
def wrapLat : PeriodicLatticeExtent := fun _ => 9

@[simp] theorem wrapLat_eq (μ : Fin 3) : wrapLat μ = 9 := rfl

/-- `(0,0,0)`. -/
def wrapX : PeriodicLatticeSite wrapLat := fun _ => 0

/-- `(9,0,0)` — differs from `wrapX` ONLY on axis `0`, so the naive `l1dist` (which sums all
three axes) is exactly the single-axis gap `9`, not `27`. -/
def wrapY : PeriodicLatticeSite wrapLat := Function.update wrapX 0 9

theorem wrap_l1dist : l1dist wrapX wrapY = 9 := by decide

theorem wrap_periodicSiteDist : periodicSiteDist wrapX wrapY = 1 := by decide

/-- The divergence, stated as the actual falsifiability fact: at bound `4`, the naive metric
CERTIFIES the margin (`4 < l1dist`) while the periodic metric REFUTES it
(`¬ (4 < periodicSiteDist)`) — same pair, same bound, opposite verdicts. -/
theorem l1dist_ne_periodicSiteDist_verdict :
    (4 < l1dist wrapX wrapY) ∧ ¬ (4 < periodicSiteDist wrapX wrapY) := by
  rw [wrap_l1dist, wrap_periodicSiteDist]
  omega

/-- **§6b — the margin condition is falsifiable, not vacuously true for any bound.** Reusing
§5's genuine `witnessDomain` geometry but with a MUTATED (too-large) `marginBound = 8`: the exact
same `(x,y)` pair from §5c's proof (the axis-`μ0` boundary pair) now VIOLATES the margin, since
the true minimal gap is `7`, not `≥ 9`. Exhibits a violating pair directly (not merely "the
theorem no longer proves"), matching the OPS-3 "make it fail" standard. -/
theorem margin_condition_fails_at_mutated_bound :
    ¬ MarginCondition (witnessDomain).Lambda (witnessDomain).LambdaK 8 := by
  intro hbad
  rw [witnessDomain_LambdaK, witnessDomain_Lambda] at hbad
  -- the boundary point x = (16,16,16) (the inner block's own center) and y = (9,16,16)
  -- (just outside the outer block on axis 0: 9 < 10) realize the minimal gap of 7.
  set x : PeriodicLatticeSite witnessLat := witnessCenterI with hxdef
  set y : PeriodicLatticeSite witnessLat := Function.update witnessCenterI 0 (9 : Fin 41)
    with hydef
  have hxmem : x ∈ bigBlock witnessCenterI 8 := by
    rw [hxdef, mem_bigBlock]; decide
  have hynotmem : y ∉ bigBlock witnessCenterK 20 := by
    rw [hydef, mem_bigBlock]; decide
  have h := hbad x hxmem y hynotmem
  have hval : periodicSiteDist x y = 7 := by
    rw [hxdef, hydef]; decide
  omega

/-- **§6c — nesting is falsifiable too.** With `bigBlockSizeInner` mutated so the inner block
sticks OUT of the outer block on axis `0` (center unchanged at `16`, size grown to `30`, giving
`[16,46)`, capped at the lattice's own extent `[16,41)`), `Λ ⊄ Λ_k`: the point `witnessCenterI`
itself, shifted to have coordinate `35` on axis `0` (inside `[16,41)` but NOT inside the outer
block's `[10,30)`), lies in the mutated `Lambda` but not in `LambdaK`. -/
theorem nesting_fails_at_mutated_blockSize :
    ¬ (bigBlockUnion ({witnessCenterI} : Finset (PeriodicLatticeSite witnessLat)) 30 ⊆
        bigBlock witnessCenterK 20) := by
  intro hsub
  have hxmem : (Function.update witnessCenterI 0 (35 : Fin 41)) ∈
      bigBlockUnion ({witnessCenterI} : Finset (PeriodicLatticeSite witnessLat)) 30 := by
    rw [mem_bigBlockUnion]
    refine ⟨witnessCenterI, Finset.mem_singleton_self _, ?_⟩
    decide
  have hmem := hsub hxmem
  rw [mem_bigBlock] at hmem
  have h0 : ¬ inBlock witnessCenterK 20 (Function.update witnessCenterI 0 (35 : Fin 41)) := by
    decide
  exact h0 hmem

/-- **§6d — degenerate small lattices cap the achievable margin.** On the smallest nontrivial
torus (`Lat := fun _ => 1`, side `2`), NO pair of sites is ever more than `3` apart under
`periodicSiteDist` — so a `MarginCondition` with `marginBound ≥ 3` can never be satisfied by ANY
nonempty `Lambda`/`LambdaK^c` pair on this lattice, regardless of how the domains are chosen.
Answers the dispatch's named degeneracy ("small lattices where the margin can't be met")
concretely, not merely by assertion. -/
def tinyLat : PeriodicLatticeExtent := fun _ => 1

theorem tiny_periodicSiteDist_le_three (s t : PeriodicLatticeSite tinyLat) :
    periodicSiteDist s t ≤ 3 := by
  have h : ∀ ν : Fin 3, periodicCoordDist (tinyLat ν) (s ν) (t ν) ≤ 1 := by
    intro ν
    have hs := (s ν).isLt
    have ht := (t ν).isLt
    simp only [tinyLat] at hs ht
    unfold periodicCoordDist natAbsDiff
    simp only [tinyLat]
    omega
  unfold periodicSiteDist
  calc ∑ ν : Fin 3, periodicCoordDist (tinyLat ν) (s ν) (t ν)
      ≤ ∑ _ν : Fin 3, (1 : ℕ) := Finset.sum_le_sum (fun ν _ => h ν)
    _ = 3 := by simp

/-- Consequence: on `tinyLat`, no `MarginCondition` with `bound ≥ 3` can hold for a nonempty
`Lambda` and a nonempty complement of `LambdaK` — margin is capped by lattice size, not just by
parameter choice. -/
theorem tiny_no_margin_ge_three (Lambda LambdaK : Finset (PeriodicLatticeSite tinyLat))
    (bound : ℕ) (hbound : 3 ≤ bound) (x : PeriodicLatticeSite tinyLat) (hx : x ∈ Lambda)
    (y : PeriodicLatticeSite tinyLat) (hy : y ∉ LambdaK) :
    ¬ MarginCondition Lambda LambdaK bound := by
  intro hmargin
  have h := hmargin x hx y hy
  have h2 := tiny_periodicSiteDist_le_three x y
  omega

/-- **`ell = 1` degeneracy**: a big block of size `1` is exactly its own center — the definitions
above do not silently misbehave at this boundary case. -/
theorem bigBlock_one (y : PeriodicLatticeSite Lat) :
    bigBlock y 1 = {y} := by
  unfold bigBlock blockOf
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, inBlock]
  constructor
  · intro h
    funext μ
    have := h μ
    omega
  · intro h
    subst h
    intro μ
    omega

end AdalyFormal.Balaban.DomainSequence

#print axioms AdalyFormal.Balaban.DomainSequence.domainSequence_nonvacuous
#print axioms AdalyFormal.Balaban.DomainSequence.l1dist_ne_periodicSiteDist_verdict
#print axioms AdalyFormal.Balaban.DomainSequence.margin_condition_fails_at_mutated_bound
#print axioms AdalyFormal.Balaban.DomainSequence.nesting_fails_at_mutated_blockSize
#print axioms AdalyFormal.Balaban.DomainSequence.tiny_no_margin_ge_three
#print axioms AdalyFormal.Balaban.DomainSequence.bigBlock_one
#print axioms AdalyFormal.Balaban.DomainSequence.bigBlockUnion_pair
