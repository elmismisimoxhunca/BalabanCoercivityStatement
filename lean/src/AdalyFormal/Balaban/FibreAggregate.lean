/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.FibreCoercivity

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3200000

/-!
# `FibreAggregate.lean` — the per-bond fibre bound, SUMMED, with no volume factor

Lane record: `compute/fibre_aggregate/PROGRESS.md`.

## The gap this closes

`FibreCoercivity.bond_energy_bound` proves, for every SINGLE bond `b`,

`‖A b‖² ≤ 69088 · (P_Ax(A) + curlEnergy A)` on `{Q A = 0}`,

with an absolute constant. Summing that over bonds costs `Fintype.card (Bond L)` — the volume —
which is what `FibreCoercivity.bondEnergy_le_with_volume_factor` records and refuses to call a
coercivity constant. Its docstring names the missing piece:

> Removing the factor requires a bond ↦ (block, local index) reindexing together with a
> multiplicity count bounding how many blocks' local estimates a single plaquette or contour
> enters

This module supplies both, and concludes

`aggregate_fibre_bound : bondEnergy A ≤ 3316224 · (P_Ax(A) + curlEnergy A)`

equivalently `γ_agg · bondEnergy A ≤ ⟨A, Δ_k A⟩ + P_Ax(A)` with `γ_agg = 1/3316224`, on
`{Q A = 0}`, at block side `ell = 2`, flat background, at every periodic extent with
`2 ∣ (L μ + 1)`. **`γ_agg` does not depend on `L`** — `aggregate_two_extents` exhibits the same
numeral at two different extents.

## Why the volume appeared, and where it goes

`FibreCoercivity.intra_block_energy_bound` reads

`‖A (addOff y e, μ)‖² ≤ 352 · (pAxBlock A 2 y + curlEnergy A)`.

The gauge-fixing side `pAxBlock A 2 y` is ALREADY block-local. Only `curlEnergy A`
(`∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖²`) is global — and every plaquette that
proof actually invokes is BASED at a site of `blockOf y 2`. So the global curl energy can be
replaced by `curlBlock A y` (§1), and the whole chain re-runs with the SAME constants
(352, 2820, 11280, 23264, 69088 — §4). Not one constant is refitted here; each is inherited from
the counted chain in `FibreCoercivity` §5c.

One localization is genuinely two-block, not one-block. A direction-`μ` bond whose `μ`-coordinate
is ODD straddles `B(y)` and `B(y + 2e_μ)`, so any plaquette containing it does too:
`inter_step_bound`'s `A (periodicLatticeShift (addOff y u) μ, ν)` sits in the neighbour block when
`u μ = 1`. That is the geometry, not a defect of the argument, and it is why the budget is
`pairG A y μ = localG A y + localG A (cnbr y μ)`. TWO is bounded by geometry; it does not grow
with `L`. `cc_shift_addOff_zero` / `cc_shift_addOff_one` prove that NOTHING reaches further.

## The multiplicity count, stated plainly

* `sum_over_blocks` (§2): side-`2` blocks based at `CoarseLattice L 2` PARTITION the sites — each
  site lies in exactly one, none dropped, none doubled (`mem_blockOf_iff_cc` is an iff, and both
  directions are used). Hence `∑_y localG A y = P_Ax + curlEnergy` EXACTLY (`sum_localG`), an
  identity with no slack.
* Each bond is charged to the block of its BASE SITE. A block carries `≤ 8` sites
  (`card_blockOf_two_le`) and there are `3` directions, so `∑_b localG A (cc b.1) ≤ 24 · G` (§5).
* The neighbour term contributes the same `24 · G`, because `x ↦ periodicLatticeShift x μ` is a
  BIJECTION of the site set (`sum_shift_site`) — this is the reindexing half the source module
  said was already available.
* Total multiplicity `48`. `γ_agg = 1/(69088 · 48) = 1/3316224` (`multiplicity_arithmetic`).

**Where this differs from the `SplitBaseCase` Schur pattern, stated so it is not over-read.** That
pattern is `ℓ⁵`-Cauchy–Schwarz over a window TIMES an `ℓ²` multiplicity. Only the MULTIPLICITY half
is used here, and no Cauchy–Schwarz enters at all: `FibreCoercivity`'s per-bond estimate is already
an `L²`-pointwise bound `‖A b‖² ≤ C · (budget)`, so summing it needs a count and nothing else.
Anyone reading `48` as a Cauchy–Schwarz constant is reading it wrong; it is a pure count.

## Scope, stated so nobody over-reads it

Inherited verbatim from `FibreCoercivity`, and none of it is weakened here: `ell = 2` only; flat
background (`trivialU`) only; `2 ∣ (L μ + 1)` carried explicitly as the `blockOf`-truncation guard;
`𝔰𝔲(2)`-valued bond fields; `Q` is the tree's own `lineCoarseRestrictCov`. `3316224` is an upper
bound and is certainly not optimal — the claim is that it is POSITIVE and `L`-FREE, which is the
property the volume factor destroys and an RG argument needs.
-/

namespace AdalyFormal.Balaban.FibreAggregate

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.AxialCoercivity
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.FibreCoercivity

variable {L : PeriodicLatticeExtent}

/-! ## §1. The BLOCK-LOCAL right-hand side

`curlBlock A y` is the curl energy carried by the plaquettes BASED at a site of `B(y)`. The base
site is the honest assignment: `PeriodicLatticePlaquette L = Site × Directions`, so summing
`curlBlock` over the coarse lattice reproduces `curlEnergy` EXACTLY (`sum_curlBlock`), with no
double counting to absorb. -/

/-- The block-local curl energy: `∑_{x ∈ B(y)} ∑_{(μ<ν)} ‖(dA)(x, μ, ν)‖²`. -/
noncomputable def curlBlock (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) : ℝ :=
  ∑ x ∈ blockOf y 2, ∑ d : PeriodicPlaquetteDirections, ‖flatCurlValue A (x, d)‖ ^ 2

theorem curlBlock_nonneg (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) :
    0 ≤ curlBlock A y :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- A plaquette based INSIDE the block is controlled by the block's own curl energy. This is the
one replacement that removes the volume: `FibreCoercivity`'s chain only ever invokes
`norm_sq_flatCurl_le` at plaquettes based in `B(y)`. -/
theorem norm_sq_flatCurl_le_curlBlock (A : Bond L → SuTwo) {y x : PeriodicLatticeSite L}
    (hx : x ∈ blockOf y 2) (d : PeriodicPlaquetteDirections) :
    ‖flatCurlValue A (x, d)‖ ^ 2 ≤ curlBlock A y := by
  have h1 : ‖flatCurlValue A (x, d)‖ ^ 2
      ≤ ∑ d' : PeriodicPlaquetteDirections, ‖flatCurlValue A (x, d')‖ ^ 2 :=
    Finset.single_le_sum (f := fun d' : PeriodicPlaquetteDirections =>
      ‖flatCurlValue A (x, d')‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ d)
  have h2 : (∑ d' : PeriodicPlaquetteDirections, ‖flatCurlValue A (x, d')‖ ^ 2)
      ≤ curlBlock A y :=
    Finset.single_le_sum (f := fun z : PeriodicLatticeSite L =>
        ∑ d' : PeriodicPlaquetteDirections, ‖flatCurlValue A (z, d')‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hx
  linarith

/-- **The block-local budget.** `pAxBlock` is `AxialCoercivity`'s own single-block gauge-fixing
energy (reused, not redefined); `curlBlock` is §1's block-local curl energy. -/
noncomputable def localG (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) : ℝ :=
  pAxBlock A 2 y + curlBlock A y

theorem localG_nonneg (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) : 0 ≤ localG A y := by
  have h1 := pAxBlock_nonneg A 2 y
  have h2 := curlBlock_nonneg A y
  unfold localG
  linarith

theorem curlBlock_le_localG (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) :
    curlBlock A y ≤ localG A y := by
  have h1 := pAxBlock_nonneg A 2 y
  unfold localG
  linarith

#print axioms curlBlock
#print axioms curlBlock_nonneg
#print axioms norm_sq_flatCurl_le_curlBlock
#print axioms localG
#print axioms localG_nonneg
#print axioms curlBlock_le_localG

/-! ## §2. THE PARTITION — side-`2` blocks tile the sites, exactly once each

This is the "bond ↦ (block, local index) reindexing" as a THEOREM, not a remark. `cc x` is
`FibreCoercivity`'s coarse-centre map (reused); the content is that for a coarse `y`, membership in
`B(y)` is EQUIVALENT to `cc x = y`, so the blocks are the fibres of `cc` — no site dropped (`cc x`
is always coarse, `cc_mem`), no site doubled (the fibres of a function are disjoint). -/

/-- **`B(y)` is exactly the fibre of `cc` over a coarse `y`.** Both directions are needed: `←` says
no site is dropped, `→` says no site is claimed by two blocks. -/
theorem mem_blockOf_iff_cc {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (x : PeriodicLatticeSite L) : x ∈ blockOf y 2 ↔ cc x = y := by
  constructor
  · intro hx
    funext ν
    apply Fin.ext
    rw [cc_val]
    have h1 := mem_blockOf.1 hx ν
    have h2 := hy ν
    omega
  · intro hx
    refine mem_blockOf.2 (fun ν => ?_)
    have h : (cc x ν).val = (y ν).val := by rw [hx]
    rw [cc_val] at h
    omega

/-- The coarse centre of an in-block offset site is the block's own centre. -/
theorem cc_addOff (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) {u : Fin 3 → ℕ} (hu : ∀ ν, u ν ≤ 1) :
    cc (addOff y u) = y :=
  (mem_blockOf_iff_cc hy _).1 (mem_blockOf_addOff hdvd hy hu)

/-- **THE TILING, as a summation identity.** Summing any site function over each coarse block and
then over the coarse lattice returns the plain sum over sites — no multiplicity, no loss. -/
theorem sum_over_blocks (f : PeriodicLatticeSite L → ℝ) :
    ∑ y ∈ CoarseLattice L 2, ∑ x ∈ blockOf y 2, f x = ∑ x : PeriodicLatticeSite L, f x := by
  classical
  have hmaps : ∀ x ∈ (Finset.univ : Finset (PeriodicLatticeSite L)), cc x ∈ CoarseLattice L 2 :=
    fun x _ => cc_mem x
  have hfib : ∀ y ∈ CoarseLattice L 2,
      (∑ x ∈ blockOf y 2, f x)
        = ∑ x ∈ Finset.univ.filter (fun x : PeriodicLatticeSite L => cc x = y), f x := by
    intro y hy
    have hy2 : ∀ μ : Fin 3, (y μ).val % 2 = 0 := mem_CoarseLattice.1 hy
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_blockOf_iff_cc hy2 x
  calc ∑ y ∈ CoarseLattice L 2, ∑ x ∈ blockOf y 2, f x
      = ∑ y ∈ CoarseLattice L 2,
          ∑ x ∈ Finset.univ.filter (fun x : PeriodicLatticeSite L => cc x = y), f x :=
        Finset.sum_congr rfl hfib
    _ = ∑ x : PeriodicLatticeSite L, f x := Finset.sum_fiberwise_of_maps_to hmaps f

/-- **THE BOND PARTITION.** Charging each bond to the block holding its BASE SITE is a genuine
partition of the bond set: summing any bond function over (coarse centre, base site in that block,
direction) returns the plain sum over bonds. No bond dropped, no bond double-assigned — this is the
`bond ↦ (block, local index)` reindexing, as an identity. -/
theorem sum_over_block_bonds (f : Bond L → ℝ) :
    ∑ y ∈ CoarseLattice L 2, ∑ x ∈ blockOf y 2, ∑ μ : Fin 3, f (x, μ)
      = ∑ b : Bond L, f b := by
  rw [sum_over_blocks (fun x : PeriodicLatticeSite L => ∑ μ : Fin 3, f (x, μ))]
  exact (Fintype.sum_prod_type f).symm

/-- The block-local curl energies sum EXACTLY to the global one. -/
theorem sum_curlBlock (A : Bond L → SuTwo) :
    ∑ y ∈ CoarseLattice L 2, curlBlock A y = curlEnergy A := by
  have h := sum_over_blocks
    (fun x : PeriodicLatticeSite L =>
      ∑ d : PeriodicPlaquetteDirections, ‖flatCurlValue A (x, d)‖ ^ 2)
  calc ∑ y ∈ CoarseLattice L 2, curlBlock A y
      = ∑ y ∈ CoarseLattice L 2, ∑ x ∈ blockOf y 2,
          ∑ d : PeriodicPlaquetteDirections, ‖flatCurlValue A (x, d)‖ ^ 2 := rfl
    _ = ∑ x : PeriodicLatticeSite L,
          ∑ d : PeriodicPlaquetteDirections, ‖flatCurlValue A (x, d)‖ ^ 2 := h
    _ = ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2 :=
        (Fintype.sum_prod_type (fun p : PeriodicLatticePlaquette L => ‖flatCurlValue A p‖ ^ 2)).symm
    _ = curlEnergy A := rfl

/-- **The block budgets sum EXACTLY to the global right-hand side.** This is the identity that makes
the multiplicity count meaningful: there is no hidden inflation on the way from blocks to the
global `P_Ax + curlEnergy`. -/
theorem sum_localG (A : Bond L → SuTwo) :
    ∑ y ∈ CoarseLattice L 2, localG A y = pAx A (CoarseLattice L 2) 2 + curlEnergy A := by
  unfold localG
  rw [Finset.sum_add_distrib, sum_curlBlock]
  rfl

/-- Every block budget is dominated by the global one. -/
theorem localG_le_global (A : Bond L → SuTwo) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L 2) :
    localG A y ≤ pAx A (CoarseLattice L 2) 2 + curlEnergy A := by
  rw [← sum_localG A]
  exact Finset.single_le_sum (f := fun z => localG A z) (fun z _ => localG_nonneg A z) hy

#print axioms mem_blockOf_iff_cc
#print axioms cc_addOff
#print axioms sum_over_blocks
#print axioms sum_over_block_bonds
#print axioms sum_curlBlock
#print axioms sum_localG
#print axioms localG_le_global

/-! ## §3. BLOCK CARDINALITY AND THE NEIGHBOUR CENTRE -/

/-- A half-open coordinate window of width `2` holds at most `2` lattice coordinates. -/
theorem card_window_le_two (n a : ℕ) :
    (Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < a + 2)).card ≤ 2 := by
  classical
  have h : (Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < a + 2)).card
      ≤ (Finset.range 2).card := by
    refine Finset.card_le_card_of_injOn (fun i => i.val - a) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine Finset.mem_range.2 ?_
      show i.val - a < 2
      omega
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      have hij' : (i : Fin n).val - a = (j : Fin n).val - a := hij
      exact Fin.ext (by omega)
  simpa using h

/-- **A side-`2` block carries at most `8` sites.** No hypothesis: at a truncated corner the block
is smaller, which only helps the aggregate bound.

REUSE DISCLOSURE (LAW-19): `BlockedGaugeCore.card_blockOf` already proves the sharp
`card (blockOf y ell) = ell ^ 3` at general `ell`, but under `0 < ell`, `ell ∣ (L μ + 1)` AND
`y ∈ Λ'`, and that module is NOT in `FibreCoercivity`'s import closure (measured: 165 modules,
`BlockedGaugeCore` absent). This narrow version is stated UNCONDITIONALLY, which is what the
aggregate needs, and avoids pulling in an extra import subtree. -/
theorem card_blockOf_two_le (y : PeriodicLatticeSite L) : (blockOf y 2).card ≤ 8 := by
  classical
  rw [blockOf_eq_piFinset, Fintype.card_piFinset]
  have hle : ∀ μ : Fin 3,
      (Finset.univ.filter (fun i : Fin (L μ + 1) =>
        (y μ).val ≤ i.val ∧ i.val < (y μ).val + 2)).card ≤ 2 :=
    fun μ => card_window_le_two (L μ + 1) (y μ).val
  calc (∏ μ : Fin 3, (Finset.univ.filter (fun i : Fin (L μ + 1) =>
          (y μ).val ≤ i.val ∧ i.val < (y μ).val + 2)).card)
      ≤ ∏ _μ : Fin 3, 2 := Finset.prod_le_prod' (fun μ _ => hle μ)
    _ = 8 := by decide

/-- The bonds charged to one block: at most `3 · 8 = 24`. Backs the `24` of the multiplicity
count with a compiled statement rather than prose. -/
theorem block_bond_count_le (y : PeriodicLatticeSite L) : (blockOf y 2).card * 3 ≤ 24 := by
  have h := card_blockOf_two_le y
  omega

/-- The multiplicity arithmetic, checked rather than asserted:
`48 = 2 · 3 · 8` (two blocks per bond, three directions, eight sites per block) and
`3316224 = 69088 · 48`. -/
theorem multiplicity_arithmetic : (48 : ℕ) = 2 * 3 * 8 ∧ (3316224 : ℕ) = 69088 * 48 := by
  constructor <;> norm_num

/-- **The `μ`-neighbour coarse centre**, `y + 2e_μ`. The direction-`μ` bonds with odd
`μ`-coordinate straddle `B(y)` and `B(cnbr y μ)`; §3's two lemmas prove nothing in this module
reaches further. -/
def cnbr (y : PeriodicLatticeSite L) (μ : Fin 3) : PeriodicLatticeSite L :=
  cc (periodicLatticeShift (periodicLatticeShift y μ) μ)

theorem cnbr_val_ne {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (μ : Fin 3) {ν : Fin 3} (hν : ν ≠ μ) : (cnbr y μ ν).val = (y ν).val := by
  have h1 : (periodicLatticeShift (periodicLatticeShift y μ) μ) ν = y ν := by
    rw [shiftNe (periodicLatticeShift y μ) hν, shiftNe y hν]
  show ((periodicLatticeShift (periodicLatticeShift y μ) μ) ν).val
      - ((periodicLatticeShift (periodicLatticeShift y μ) μ) ν).val % 2 = _
  rw [h1]
  have := hy ν
  omega

theorem cnbr_val_self (y : PeriodicLatticeSite L) (μ : Fin 3) :
    (cnbr y μ μ).val
      = ((y μ).val + 2) % (L μ + 1) - ((y μ).val + 2) % (L μ + 1) % 2 := by
  have h1 : ((periodicLatticeShift (periodicLatticeShift y μ) μ) μ).val
      = ((y μ).val + 2) % (L μ + 1) := by
    rw [shiftMod, shiftMod, Nat.mod_add_mod]
  show ((periodicLatticeShift (periodicLatticeShift y μ) μ) μ).val
      - ((periodicLatticeShift (periodicLatticeShift y μ) μ) μ).val % 2 = _
  rw [h1]

/-- The `μ`-coordinate of a shifted in-block site, honestly modulo the extent. -/
theorem shift_addOff_val_self (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    {u : Fin 3 → ℕ} (hu : ∀ ν, u ν ≤ 1) (μ : Fin 3) :
    ((periodicLatticeShift (addOff y u) μ) μ).val = ((y μ).val + u μ + 1) % (L μ + 1) := by
  rw [shiftMod, addOff_val y u μ (addOff_bound hdvd hy hu μ)]

/-- If `u μ = 0`, shifting along `μ` STAYS in `B(y)`. -/
theorem cc_shift_addOff_zero (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    {u : Fin 3 → ℕ} (hu : ∀ ν, u ν ≤ 1) (μ : Fin 3) (h0 : u μ = 0) :
    cc (periodicLatticeShift (addOff y u) μ) = y := by
  funext ν
  apply Fin.ext
  rw [cc_val]
  by_cases hν : ν = μ
  · subst hν
    rw [shift_addOff_val_self hdvd hy hu ν, h0]
    have hroom := coarse_room hdvd hy ν
    have hmod : ((y ν).val + 0 + 1) % (L ν + 1) = (y ν).val + 1 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    have := hy ν
    omega
  · rw [shiftNe (addOff y u) hν, addOff_val y u ν (addOff_bound hdvd hy hu ν)]
    have h1 := hy ν
    have h2 := hu ν
    omega

/-- If `u μ = 1`, shifting along `μ` lands in the `μ`-NEIGHBOUR block — and in no other. -/
theorem cc_shift_addOff_one (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    {u : Fin 3 → ℕ} (hu : ∀ ν, u ν ≤ 1) (μ : Fin 3) (h1 : u μ = 1) :
    cc (periodicLatticeShift (addOff y u) μ) = cnbr y μ := by
  funext ν
  apply Fin.ext
  by_cases hν : ν = μ
  · subst hν
    have harg : (y ν).val + 1 + 1 = (y ν).val + 2 := by omega
    rw [cc_val, shift_addOff_val_self hdvd hy hu ν, h1, harg, cnbr_val_self y ν]
  · rw [cc_val, shiftNe (addOff y u) hν, addOff_val y u ν (addOff_bound hdvd hy hu ν),
      cnbr_val_ne hy μ hν]
    have ha := hy ν
    have hb := hu ν
    omega

#print axioms card_window_le_two
#print axioms card_blockOf_two_le
#print axioms block_bond_count_le
#print axioms multiplicity_arithmetic
#print axioms cnbr
#print axioms cnbr_val_ne
#print axioms cnbr_val_self
#print axioms shift_addOff_val_self
#print axioms cc_shift_addOff_zero
#print axioms cc_shift_addOff_one

/-! ## §4. THE LOCALIZED CHAIN — `FibreCoercivity` §5c with a block-local right-hand side

Every constant here is the one `FibreCoercivity` §5c counted; none is refitted. The ONLY change is
that the global `pAx A (CoarseLattice L 2) 2 + curlEnergy A` is replaced by the block budget
`localG A y` (intra) or the two-block budget `pairG A y μ` (inter). -/

/-- **The two-block budget.** `y` and its `μ`-neighbour, and nothing else. -/
noncomputable def pairG (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) (μ : Fin 3) : ℝ :=
  localG A y + localG A (cnbr y μ)

theorem pairG_nonneg (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    0 ≤ pairG A y μ := by
  have h1 := localG_nonneg A y
  have h2 := localG_nonneg A (cnbr y μ)
  unfold pairG
  linarith

theorem localG_le_pairG (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    localG A y ≤ pairG A y μ := by
  have h2 := localG_nonneg A (cnbr y μ)
  unfold pairG
  linarith

theorem localG_cnbr_le_pairG (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    localG A (cnbr y μ) ≤ pairG A y μ := by
  have h1 := localG_nonneg A y
  unfold pairG
  linarith

/-- **The budget closes over the geometry**: a site reached by one `μ`-shift out of `B(y)` still
lies in `B(y)` or in `B(cnbr y μ)`. This is the statement that the multiplicity is `2` and not
`|Λ|`. -/
theorem localG_cc_shift_le_pairG (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    {u : Fin 3 → ℕ} (hu : ∀ ν, u ν ≤ 1) (μ : Fin 3) :
    localG A (cc (periodicLatticeShift (addOff y u) μ)) ≤ pairG A y μ := by
  rcases (show u μ = 0 ∨ u μ = 1 by have := hu μ; omega) with h | h
  · rw [cc_shift_addOff_zero hdvd hy hu μ h]
    exact localG_le_pairG A y μ
  · rw [cc_shift_addOff_one hdvd hy hu μ h]
    exact localG_cnbr_le_pairG A y μ

/-- **THE LOCALIZED QUANTITATIVE STAGE ONE.** `FibreCoercivity.intra_block_energy_bound` with
`curlEnergy A` replaced by `curlBlock A y`. Same constant `352`, same five-step nesting; the only
change is that every plaquette invoked is recognized as BASED IN `B(y)`. -/
theorem intra_block_energy_bound_local (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo) {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (e : Fin 3 → ℕ) (he : ∀ ν, e ν ≤ 1) (μ : Fin 3) (heμ : e μ = 0) :
    ‖A (addOff y e, μ)‖ ^ 2 ≤ 352 * localG A y := by
  have hPy : (0 : ℝ) ≤ pAxBlock A 2 y := pAxBlock_nonneg A 2 y
  have hCc : (0 : ℝ) ≤ curlBlock A y := curlBlock_nonneg A y
  show ‖A (addOff y e, μ)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y)
  have hz0 : addOff y (off3 0 0 0) = y := addOff_zero y
  have hmem : ∀ u : Fin 3 → ℕ, (∀ ν, u ν ≤ 1) → addOff y u ∈ blockOf y 2 :=
    fun u hu => mem_blockOf_addOff hdvd hy hu
  have hI : ∀ r s t : ℕ, r ≤ 1 → s ≤ 1 → t ≤ 1 →
      ‖pathIntegral A y (addOff y (off3 r s t))‖ ^ 2 ≤ pAxBlock A 2 y :=
    fun r s t hr hs ht =>
      norm_sq_pathIntegral_le_pAxBlock A 2 (mem_blockOf_addOff hdvd hy (off3_le r s t hr hs ht))
  have E : ∀ r s t : ℕ, r ≤ 1 → s ≤ 1 → t ≤ 1 →
      pathIntegral A y (addOff y (off3 r s t))
        = (if t = 1 then A (y, 2) else 0)
          + (if s = 1 then A (addOff y (off3 0 0 t), 1) else 0)
          + (if r = 1 then A (addOff y (off3 0 s t), 0) else 0) :=
    fun r s t hr hs ht => pathIntegral_off3 hdvd A hy r s t hr hs ht
  have b1 : ‖A (addOff y (off3 0 0 0), 2)‖ ^ 2 ≤ pAxBlock A 2 y := by
    have h := E 0 0 1 (by omega) (by omega) (by omega)
    norm_num at h
    rw [hz0, ← h]
    exact hI 0 0 1 (by omega) (by omega) (by omega)
  have b2 : ‖A (addOff y (off3 0 0 0), 1)‖ ^ 2 ≤ pAxBlock A 2 y := by
    have h := E 0 1 0 (by omega) (by omega) (by omega)
    norm_num at h
    rw [← h]
    exact hI 0 1 0 (by omega) (by omega) (by omega)
  have b4 : ‖A (addOff y (off3 0 0 0), 0)‖ ^ 2 ≤ pAxBlock A 2 y := by
    have h := E 1 0 0 (by omega) (by omega) (by omega)
    norm_num at h
    rw [← h]
    exact hI 1 0 0 (by omega) (by omega) (by omega)
  have b3 : ‖A (addOff y (off3 0 0 1), 1)‖ ^ 2 ≤ 8 * pAxBlock A 2 y := by
    have h := E 0 1 1 (by omega) (by omega) (by omega)
    norm_num at h
    have hsol : A (addOff y (off3 0 0 1), 1)
        = pathIntegral A y (addOff y (off3 0 1 1)) + (-A (addOff y (off3 0 0 0), 2)) + 0 + 0 := by
      rw [hz0, h]; abel
    have hb := sq_four (pathIntegral A y (addOff y (off3 0 1 1)))
      (-A (addOff y (off3 0 0 0), 2)) 0 0
    rw [← hsol] at hb
    have h1 := hI 0 1 1 (by omega) (by omega) (by omega)
    rw [norm_neg] at hb
    simp only [norm_zero] at hb
    nlinarith [hb, h1, b1]
  have b5 : ‖A (addOff y (off3 0 1 0), 0)‖ ^ 2 ≤ 8 * pAxBlock A 2 y := by
    have h := E 1 1 0 (by omega) (by omega) (by omega)
    norm_num at h
    have hsol : A (addOff y (off3 0 1 0), 0)
        = pathIntegral A y (addOff y (off3 1 1 0)) + (-A (addOff y (off3 0 0 0), 1)) + 0 + 0 := by
      rw [h]; abel
    have hb := sq_four (pathIntegral A y (addOff y (off3 1 1 0)))
      (-A (addOff y (off3 0 0 0), 1)) 0 0
    rw [← hsol] at hb
    have h1 := hI 1 1 0 (by omega) (by omega) (by omega)
    rw [norm_neg] at hb
    simp only [norm_zero] at hb
    nlinarith [hb, h1, b2]
  have b6 : ‖A (addOff y (off3 0 0 1), 0)‖ ^ 2 ≤ 8 * pAxBlock A 2 y := by
    have h := E 1 0 1 (by omega) (by omega) (by omega)
    norm_num at h
    have hsol : A (addOff y (off3 0 0 1), 0)
        = pathIntegral A y (addOff y (off3 1 0 1)) + (-A (addOff y (off3 0 0 0), 2)) + 0 + 0 := by
      rw [hz0, h]; abel
    have hb := sq_four (pathIntegral A y (addOff y (off3 1 0 1)))
      (-A (addOff y (off3 0 0 0), 2)) 0 0
    rw [← hsol] at hb
    have h1 := hI 1 0 1 (by omega) (by omega) (by omega)
    rw [norm_neg] at hb
    simp only [norm_zero] at hb
    nlinarith [hb, h1, b1]
  have b7 : ‖A (addOff y (off3 0 1 1), 0)‖ ^ 2 ≤ 40 * pAxBlock A 2 y := by
    have h := E 1 1 1 (by omega) (by omega) (by omega)
    norm_num at h
    have hsol : A (addOff y (off3 0 1 1), 0)
        = pathIntegral A y (addOff y (off3 1 1 1)) + (-A (addOff y (off3 0 0 0), 2))
          + (-A (addOff y (off3 0 0 1), 1)) + 0 := by
      rw [hz0, h]; abel
    have hb := sq_four (pathIntegral A y (addOff y (off3 1 1 1)))
      (-A (addOff y (off3 0 0 0), 2)) (-A (addOff y (off3 0 0 1), 1)) 0
    rw [← hsol] at hb
    have h1 := hI 1 1 1 (by omega) (by omega) (by omega)
    rw [norm_neg, norm_neg] at hb
    simp only [norm_zero] at hb
    nlinarith [hb, h1, b1, b3]
  have SH : ∀ (u v : Fin 3 → ℕ) (m : Fin 3), (∀ ν, u ν ≤ 1) → (∀ ν, v ν ≤ 1) →
      v m = u m + 1 → (∀ ν, ν ≠ m → v ν = u ν) →
      periodicLatticeShift (addOff y u) m = addOff y v :=
    fun u v m hu hv h1 h2 => shift_addOff hdvd hy u v m hu hv h1 h2
  have n1 : ‖A (addOff y (off3 1 0 0), 1)‖ ^ 2
      ≤ 4 * (curlBlock A y + pAxBlock A 2 y + 8 * pAxBlock A 2 y + pAxBlock A 2 y) := by
    have hs := curl_solve A (addOff y (off3 0 0 0)) 0 1 (by decide)
    rw [SH (off3 0 0 0) (off3 1 0 0) 0 (by decide) (by decide) (by decide) (by decide),
      SH (off3 0 0 0) (off3 0 1 0) 1 (by decide) (by decide) (by decide) (by decide)] at hs
    have hb := sq_four (flatCurlValue A (addOff y (off3 0 0 0), ⟨((0 : Fin 3), (1 : Fin 3)),
        by decide⟩)) (-A (addOff y (off3 0 0 0), 0)) (A (addOff y (off3 0 1 0), 0))
      (A (addOff y (off3 0 0 0), 1))
    rw [← hs, norm_neg] at hb
    have hF := norm_sq_flatCurl_le_curlBlock A (hmem (off3 0 0 0) (by decide))
      ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩
    nlinarith [hb, hF, b4, b5, b2]
  have n3 : ‖A (addOff y (off3 1 0 0), 2)‖ ^ 2
      ≤ 4 * (curlBlock A y + pAxBlock A 2 y + 8 * pAxBlock A 2 y + pAxBlock A 2 y) := by
    have hs := curl_solve A (addOff y (off3 0 0 0)) 0 2 (by decide)
    rw [SH (off3 0 0 0) (off3 1 0 0) 0 (by decide) (by decide) (by decide) (by decide),
      SH (off3 0 0 0) (off3 0 0 1) 2 (by decide) (by decide) (by decide) (by decide)] at hs
    have hb := sq_four (flatCurlValue A (addOff y (off3 0 0 0), ⟨((0 : Fin 3), (2 : Fin 3)),
        by decide⟩)) (-A (addOff y (off3 0 0 0), 0)) (A (addOff y (off3 0 0 1), 0))
      (A (addOff y (off3 0 0 0), 2))
    rw [← hs, norm_neg] at hb
    have hF := norm_sq_flatCurl_le_curlBlock A (hmem (off3 0 0 0) (by decide))
      ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩
    nlinarith [hb, hF, b4, b6, b1]
  have n4 : ‖A (addOff y (off3 0 1 0), 2)‖ ^ 2
      ≤ 4 * (curlBlock A y + pAxBlock A 2 y + 8 * pAxBlock A 2 y + pAxBlock A 2 y) := by
    have hs := curl_solve A (addOff y (off3 0 0 0)) 1 2 (by decide)
    rw [SH (off3 0 0 0) (off3 0 1 0) 1 (by decide) (by decide) (by decide) (by decide),
      SH (off3 0 0 0) (off3 0 0 1) 2 (by decide) (by decide) (by decide) (by decide)] at hs
    have hb := sq_four (flatCurlValue A (addOff y (off3 0 0 0), ⟨((1 : Fin 3), (2 : Fin 3)),
        by decide⟩)) (-A (addOff y (off3 0 0 0), 1)) (A (addOff y (off3 0 0 1), 1))
      (A (addOff y (off3 0 0 0), 2))
    rw [← hs, norm_neg] at hb
    have hF := norm_sq_flatCurl_le_curlBlock A (hmem (off3 0 0 0) (by decide))
      ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩
    nlinarith [hb, hF, b2, b3, b1]
  have n2 : ‖A (addOff y (off3 1 0 1), 1)‖ ^ 2
      ≤ 4 * (curlBlock A y + 8 * pAxBlock A 2 y + 40 * pAxBlock A 2 y + 8 * pAxBlock A 2 y) := by
    have hs := curl_solve A (addOff y (off3 0 0 1)) 0 1 (by decide)
    rw [SH (off3 0 0 1) (off3 1 0 1) 0 (by decide) (by decide) (by decide) (by decide),
      SH (off3 0 0 1) (off3 0 1 1) 1 (by decide) (by decide) (by decide) (by decide)] at hs
    have hb := sq_four (flatCurlValue A (addOff y (off3 0 0 1), ⟨((0 : Fin 3), (1 : Fin 3)),
        by decide⟩)) (-A (addOff y (off3 0 0 1), 0)) (A (addOff y (off3 0 1 1), 0))
      (A (addOff y (off3 0 0 1), 1))
    rw [← hs, norm_neg] at hb
    have hF := norm_sq_flatCurl_le_curlBlock A (hmem (off3 0 0 1) (by decide))
      ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩
    nlinarith [hb, hF, b6, b7, b3]
  have n5 : ‖A (addOff y (off3 1 1 0), 2)‖ ^ 2
      ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    have hs := curl_solve A (addOff y (off3 0 1 0)) 0 2 (by decide)
    rw [SH (off3 0 1 0) (off3 1 1 0) 0 (by decide) (by decide) (by decide) (by decide),
      SH (off3 0 1 0) (off3 0 1 1) 2 (by decide) (by decide) (by decide) (by decide)] at hs
    have hb := sq_four (flatCurlValue A (addOff y (off3 0 1 0), ⟨((0 : Fin 3), (2 : Fin 3)),
        by decide⟩)) (-A (addOff y (off3 0 1 0), 0)) (A (addOff y (off3 0 1 1), 0))
      (A (addOff y (off3 0 1 0), 2))
    rw [← hs, norm_neg] at hb
    have hF := norm_sq_flatCurl_le_curlBlock A (hmem (off3 0 1 0) (by decide))
      ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩
    nlinarith [hb, hF, b5, b7, n4]
  have hb1 : ‖A (addOff y (off3 0 0 0), 2)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hb2 : ‖A (addOff y (off3 0 0 0), 1)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hb3 : ‖A (addOff y (off3 0 0 1), 1)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hb4 : ‖A (addOff y (off3 0 0 0), 0)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hb5 : ‖A (addOff y (off3 0 1 0), 0)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hb6 : ‖A (addOff y (off3 0 0 1), 0)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hb7 : ‖A (addOff y (off3 0 1 1), 0)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hn1 : ‖A (addOff y (off3 1 0 0), 1)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hn2 : ‖A (addOff y (off3 1 0 1), 1)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hn3 : ‖A (addOff y (off3 1 0 0), 2)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hn4 : ‖A (addOff y (off3 0 1 0), 2)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlBlock A y) := by
    linarith
  have hc0 : e 0 ≤ 1 := he 0
  have hc1 : e 1 ≤ 1 := he 1
  have hc2 : e 2 ≤ 1 := he 2
  rw [eq_off3 e]
  rcases fin3_cases μ with rfl | rfl | rfl
  · rw [show e 0 = 0 from heμ]
    rcases (show e 1 = 0 ∨ e 1 = 1 by omega) with h1 | h1 <;>
      rcases (show e 2 = 0 ∨ e 2 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact hb4
    · exact hb6
    · exact hb5
    · exact hb7
  · rw [show e 1 = 0 from heμ]
    rcases (show e 0 = 0 ∨ e 0 = 1 by omega) with h1 | h1 <;>
      rcases (show e 2 = 0 ∨ e 2 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact hb2
    · exact hb3
    · exact hn1
    · exact hn2
  · rw [show e 2 = 0 from heμ]
    rcases (show e 0 = 0 ∨ e 0 = 1 by omega) with h1 | h1 <;>
      rcases (show e 1 = 0 ∨ e 1 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact hb1
    · exact hn4
    · exact hn3
    · exact n5

/-- **The localized stage one, POINTWISE.** Every bond with even direction-coordinate, charged to
its OWN block and nothing else. -/
theorem intra_bond_local (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (z : PeriodicLatticeSite L) (μ : Fin 3) (hz : (z μ).val % 2 = 0) :
    ‖A (z, μ)‖ ^ 2 ≤ 352 * localG A (cc z) := by
  have hy : ∀ ν : Fin 3, ((cc z) ν).val % 2 = 0 := fun ν => cc_even z ν
  have hze : z = addOff (cc z) (fun ν => (z ν).val % 2) := by
    refine addOff_of_val (cc z) z _ (fun ν => ?_)
    show (z ν).val = (cc z ν).val + (z ν).val % 2
    rw [cc_val]; omega
  have key := intra_block_energy_bound_local hdvd A hy (fun ν => (z ν).val % 2)
    (fun ν => by omega) μ hz
  rwa [← hze] at key

#print axioms pairG
#print axioms pairG_nonneg
#print axioms localG_le_pairG
#print axioms localG_cnbr_le_pairG
#print axioms localG_cc_shift_le_pairG
#print axioms intra_block_energy_bound_local
#print axioms intra_bond_local

/-- **The localized transverse step**, `FibreCoercivity.inter_step_bound` on the two-block budget.
Constant `2820 = 4·(1 + 352 + 352)` unchanged. -/
theorem inter_step_local (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (u v : Fin 3 → ℕ) (hu : ∀ ν, u ν ≤ 1) (hv : ∀ ν, v ν ≤ 1) (μ ν : Fin 3) (hne : ν ≠ μ)
    (hzero : u ν = 0) (hone : v ν = u ν + 1) (hrest : ∀ ρ, ρ ≠ ν → v ρ = u ρ) :
    ‖A (addOff y v, μ) - A (addOff y u, μ)‖ ^ 2 ≤ 2820 * pairG A y μ := by
  have hG : (0 : ℝ) ≤ pairG A y μ := pairG_nonneg A y μ
  have hshift : periodicLatticeShift (addOff y u) ν = addOff y v :=
    shift_addOff hdvd hy u v ν hu hv hone hrest
  have hpar : (addOff y u ν).val % 2 = 0 := by rw [addOff_parity hdvd hy hu ν, hzero]
  have hI1 : ‖A (addOff y u, ν)‖ ^ 2 ≤ 352 * pairG A y μ := by
    have h := intra_bond_local hdvd A (addOff y u) ν hpar
    rw [cc_addOff hdvd hy hu] at h
    have h2 := localG_le_pairG A y μ
    linarith
  have hI2 : ‖A (periodicLatticeShift (addOff y u) μ, ν)‖ ^ 2 ≤ 352 * pairG A y μ := by
    have h := intra_bond_local hdvd A (periodicLatticeShift (addOff y u) μ) ν (by
      rw [shiftNe (addOff y u) hne]; exact hpar)
    have h2 := localG_cc_shift_le_pairG hdvd A hy hu μ
    linarith
  have hFB : ∀ d : PeriodicPlaquetteDirections,
      ‖flatCurlValue A (addOff y u, d)‖ ^ 2 ≤ pairG A y μ := by
    intro d
    have h := norm_sq_flatCurl_le_curlBlock A (mem_blockOf_addOff hdvd hy hu) d
    have h2 := curlBlock_le_localG A y
    have h3 := localG_le_pairG A y μ
    linarith
  rcases lt_trichotomy μ ν with h | h | h
  · have hF := hFB ⟨(μ, ν), h⟩
    have hsol : A (addOff y v, μ) - A (addOff y u, μ)
        = A (periodicLatticeShift (addOff y u) μ, ν) + (-A (addOff y u, ν))
          + (-flatCurlValue A (addOff y u, ⟨(μ, ν), h⟩)) + 0 := by
      have hc : flatCurlValue A (addOff y u, ⟨(μ, ν), h⟩)
          = A (addOff y u, μ) + A (periodicLatticeShift (addOff y u) μ, ν)
            - A (periodicLatticeShift (addOff y u) ν, μ) - A (addOff y u, ν) := rfl
      rw [hc, ← hshift]
      abel
    have hb := sq_four (A (periodicLatticeShift (addOff y u) μ, ν)) (-A (addOff y u, ν))
      (-flatCurlValue A (addOff y u, ⟨(μ, ν), h⟩)) 0
    rw [← hsol, norm_neg, norm_neg] at hb
    simp only [norm_zero] at hb
    nlinarith [hb, hF, hI1, hI2]
  · exact absurd h.symm hne
  · have hF := hFB ⟨(ν, μ), h⟩
    have hsol : A (addOff y v, μ) - A (addOff y u, μ)
        = flatCurlValue A (addOff y u, ⟨(ν, μ), h⟩) + (-A (addOff y u, ν))
          + A (periodicLatticeShift (addOff y u) μ, ν) + 0 := by
      have hc : flatCurlValue A (addOff y u, ⟨(ν, μ), h⟩)
          = A (addOff y u, ν) + A (periodicLatticeShift (addOff y u) ν, μ)
            - A (periodicLatticeShift (addOff y u) μ, ν) - A (addOff y u, μ) := rfl
      rw [hc, ← hshift]
      abel
    have hb := sq_four (flatCurlValue A (addOff y u, ⟨(ν, μ), h⟩)) (-A (addOff y u, ν))
      (A (periodicLatticeShift (addOff y u) μ, ν)) 0
    rw [← hsol, norm_neg] at hb
    simp only [norm_zero] at hb
    nlinarith [hb, hF, hI1, hI2]

/-- **The localized stage two**, `FibreCoercivity.inter_dev_bound` on the two-block budget.
Constant `11280 = 4·2820` unchanged. -/
theorem inter_dev_local (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (e : Fin 3 → ℕ) (he : ∀ ν, e ν ≤ 1) (μ : Fin 3) (heμ : e μ = 1) :
    ‖A (addOff y e, μ) - A (periodicLatticeShift y μ, μ)‖ ^ 2 ≤ 11280 * pairG A y μ := by
  have hG : (0 : ℝ) ≤ pairG A y μ := pairG_nonneg A y μ
  have S := fun (u v : Fin 3 → ℕ) (hu : ∀ ν, u ν ≤ 1) (hv : ∀ ν, v ν ≤ 1)
      (m n : Fin 3) (hne : n ≠ m) (h0 : u n = 0) (h1 : v n = u n + 1)
      (hr : ∀ ρ, ρ ≠ n → v ρ = u ρ) =>
    inter_step_local hdvd A hy u v hu hv m n hne h0 h1 hr
  have two : ∀ a b c : SuTwo, ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
    intro a b c
    have h : a - c = (a - b) + (b - c) := by abel
    rw [h]
    exact sq_two _ _
  have zero_case : ∀ a : SuTwo, ‖a - a‖ ^ 2 ≤ 11280 * pairG A y μ := by
    intro a
    rw [sub_self, norm_zero]
    nlinarith
  have hb0 : e 0 ≤ 1 := he 0
  have hb1 : e 1 ≤ 1 := he 1
  have hb2 : e 2 ≤ 1 := he 2
  rw [eq_off3 e]
  rcases fin3_cases μ with rfl | rfl | rfl
  · rw [shift_eq_addOff0 hdvd hy, show e 0 = 1 from heμ]
    have k01 := S (off3 1 0 0) (off3 1 0 1) (by decide) (by decide) 0 2
      (by decide) (by decide) (by decide) (by decide)
    have k10 := S (off3 1 0 0) (off3 1 1 0) (by decide) (by decide) 0 1
      (by decide) (by decide) (by decide) (by decide)
    have k11 := S (off3 1 1 0) (off3 1 1 1) (by decide) (by decide) 0 2
      (by decide) (by decide) (by decide) (by decide)
    rcases (show e 1 = 0 ∨ e 1 = 1 by omega) with h1 | h1 <;>
      rcases (show e 2 = 0 ∨ e 2 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact zero_case _
    · nlinarith [k01]
    · nlinarith [k10]
    · nlinarith [two (A (addOff y (off3 1 1 1), (0 : Fin 3)))
        (A (addOff y (off3 1 1 0), (0 : Fin 3))) (A (addOff y (off3 1 0 0), (0 : Fin 3))),
        k11, k10]
  · rw [shift_eq_addOff1 hdvd hy, show e 1 = 1 from heμ]
    have k01 := S (off3 0 1 0) (off3 0 1 1) (by decide) (by decide) 1 2
      (by decide) (by decide) (by decide) (by decide)
    have k10 := S (off3 0 1 0) (off3 1 1 0) (by decide) (by decide) 1 0
      (by decide) (by decide) (by decide) (by decide)
    have k11 := S (off3 1 1 0) (off3 1 1 1) (by decide) (by decide) 1 2
      (by decide) (by decide) (by decide) (by decide)
    rcases (show e 0 = 0 ∨ e 0 = 1 by omega) with h1 | h1 <;>
      rcases (show e 2 = 0 ∨ e 2 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact zero_case _
    · nlinarith [k01]
    · nlinarith [k10]
    · nlinarith [two (A (addOff y (off3 1 1 1), (1 : Fin 3)))
        (A (addOff y (off3 1 1 0), (1 : Fin 3))) (A (addOff y (off3 0 1 0), (1 : Fin 3))),
        k11, k10]
  · rw [shift_eq_addOff2 hdvd hy, show e 2 = 1 from heμ]
    have k01 := S (off3 0 0 1) (off3 0 1 1) (by decide) (by decide) 2 1
      (by decide) (by decide) (by decide) (by decide)
    have k10 := S (off3 0 0 1) (off3 1 0 1) (by decide) (by decide) 2 0
      (by decide) (by decide) (by decide) (by decide)
    have k11 := S (off3 1 0 1) (off3 1 1 1) (by decide) (by decide) 2 1
      (by decide) (by decide) (by decide) (by decide)
    rcases (show e 0 = 0 ∨ e 0 = 1 by omega) with h1 | h1 <;>
      rcases (show e 1 = 0 ∨ e 1 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact zero_case _
    · nlinarith [k01]
    · nlinarith [k10]
    · nlinarith [two (A (addOff y (off3 1 1 1), (2 : Fin 3)))
        (A (addOff y (off3 1 0 1), (2 : Fin 3))) (A (addOff y (off3 0 0 1), (2 : Fin 3))),
        k11, k10]

/-- **The localized `Q`-summand deviation.** Constant `23264 = 2·352 + 2·11280` unchanged. -/
theorem block_summand_dev_local (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (e : Fin 3 → ℕ) (he : ∀ ν, e ν ≤ 1) (μ : Fin 3) :
    ‖(A (addOff y e, μ) + A (periodicLatticeShift (addOff y e) μ, μ))
        - A (periodicLatticeShift y μ, μ)‖ ^ 2
      ≤ 23264 * pairG A y μ := by
  have hG : (0 : ℝ) ≤ pairG A y μ := pairG_nonneg A y μ
  have hpar : (addOff y e μ).val % 2 = e μ % 2 := addOff_parity hdvd hy he μ
  set e' : Fin 3 → ℕ := fun ν => if ν = μ then 1 else e ν with he'def
  have he' : ∀ ν, e' ν ≤ 1 := by
    intro ν
    simp only [he'def]
    split_ifs with hh
    · omega
    · exact he ν
  rcases (show e μ = 0 ∨ e μ = 1 by have := he μ; omega) with h0 | h1
  · have hA : ‖A (addOff y e, μ)‖ ^ 2 ≤ 352 * pairG A y μ := by
      have h := intra_bond_local hdvd A (addOff y e) μ (by rw [hpar, h0])
      rw [cc_addOff hdvd hy he] at h
      have h2 := localG_le_pairG A y μ
      linarith
    have hsh : periodicLatticeShift (addOff y e) μ = addOff y e' :=
      shift_addOff hdvd hy e e' μ he he' (by simp only [he'def, if_pos rfl, h0])
        (fun ν hν => by simp only [he'def, if_neg hν])
    have hA' : ‖A (periodicLatticeShift (addOff y e) μ, μ)
        - A (periodicLatticeShift y μ, μ)‖ ^ 2 ≤ 11280 * pairG A y μ := by
      rw [hsh]
      exact inter_dev_local hdvd A hy e' he' μ (by simp only [he'def, if_pos rfl])
    have heq : (A (addOff y e, μ) + A (periodicLatticeShift (addOff y e) μ, μ))
          - A (periodicLatticeShift y μ, μ)
        = A (addOff y e, μ)
          + (A (periodicLatticeShift (addOff y e) μ, μ) - A (periodicLatticeShift y μ, μ)) := by
      abel
    rw [heq]
    have hb := sq_two (A (addOff y e, μ))
      (A (periodicLatticeShift (addOff y e) μ, μ) - A (periodicLatticeShift y μ, μ))
    nlinarith [hb, hA, hA']
  · have hA : ‖A (addOff y e, μ) - A (periodicLatticeShift y μ, μ)‖ ^ 2
        ≤ 11280 * pairG A y μ :=
      inter_dev_local hdvd A hy e he μ h1
    have hA' : ‖A (periodicLatticeShift (addOff y e) μ, μ)‖ ^ 2 ≤ 352 * pairG A y μ := by
      have h := intra_bond_local hdvd A (periodicLatticeShift (addOff y e) μ) μ (by
        rw [shift_parity hdvd (addOff y e) μ]
        have hq := hpar
        have hr := h1
        omega)
      have h2 := localG_cc_shift_le_pairG hdvd A hy he μ
      linarith
    have heq : (A (addOff y e, μ) + A (periodicLatticeShift (addOff y e) μ, μ))
          - A (periodicLatticeShift y μ, μ)
        = (A (addOff y e, μ) - A (periodicLatticeShift y μ, μ))
          + A (periodicLatticeShift (addOff y e) μ, μ) := by
      abel
    rw [heq]
    have hb := sq_two (A (addOff y e, μ) - A (periodicLatticeShift y μ, μ))
      (A (periodicLatticeShift (addOff y e) μ, μ))
    nlinarith [hb, hA, hA']

/-- **The localized stage three.** `Q A = 0` bounds the block's reference inter-block bond by the
TWO-BLOCK budget. The average is still taken through a maximum over the block, so no square root
and no Cauchy–Schwarz enters. -/
theorem Q_inter_local (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    {y : PeriodicLatticeSite L} (hyc : y ∈ CoarseLattice L 2) (μ : Fin 3) :
    ‖A (periodicLatticeShift y μ, μ)‖ ^ 2 ≤ 23264 * pairG A y μ := by
  have hy : ∀ ν : Fin 3, (y ν).val % 2 = 0 := mem_CoarseLattice.1 hyc
  have hG : (0 : ℝ) ≤ pairG A y μ := pairG_nonneg A y μ
  have h := hQ (⟨y, hyc⟩, μ)
  rw [lineCoarse_trivial_two A y hyc μ] at h
  have hsum : (∑ x ∈ blockOf y 2, (A (x, μ) + A (periodicLatticeShift x μ, μ))) = 0 := by
    rcases smul_eq_zero.1 h with hc0 | hs
    · exact absurd hc0 (by norm_num)
    · exact hs
  have hdev : ∀ x ∈ blockOf y 2,
      ‖(A (x, μ) + A (periodicLatticeShift x μ, μ)) - A (periodicLatticeShift y μ, μ)‖ ^ 2
        ≤ 23264 * pairG A y μ := by
    intro x hx
    obtain ⟨hxe, hle⟩ := mem_block_offset hx
    have key := block_summand_dev_local hdvd A hy (fun ν => (x ν).val - (y ν).val) hle μ
    rwa [← hxe] at key
  have hnem : (blockOf y 2).Nonempty := ⟨y, mem_blockOf.2 (fun ν => by omega)⟩
  obtain ⟨x0, hx0, hmax⟩ := Finset.exists_max_image (blockOf y 2)
    (fun x => ‖(A (x, μ) + A (periodicLatticeShift x μ, μ))
      - A (periodicLatticeShift y μ, μ)‖) hnem
  have hM0 : (0 : ℝ) ≤ ‖(A (x0, μ) + A (periodicLatticeShift x0 μ, μ))
      - A (periodicLatticeShift y μ, μ)‖ := norm_nonneg _
  have hrw : (∑ x ∈ blockOf y 2,
        ((A (x, μ) + A (periodicLatticeShift x μ, μ)) - A (periodicLatticeShift y μ, μ)))
      = -((blockOf y 2).card • A (periodicLatticeShift y μ, μ)) := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const]
    abel
  have hn : ‖(∑ x ∈ blockOf y 2,
        ((A (x, μ) + A (periodicLatticeShift x μ, μ)) - A (periodicLatticeShift y μ, μ)))‖
      ≤ ∑ x ∈ blockOf y 2,
        ‖(A (x, μ) + A (periodicLatticeShift x μ, μ)) - A (periodicLatticeShift y μ, μ)‖ :=
    norm_sum_le _ _
  have hle2 : (∑ x ∈ blockOf y 2,
        ‖(A (x, μ) + A (periodicLatticeShift x μ, μ)) - A (periodicLatticeShift y μ, μ)‖)
      ≤ (blockOf y 2).card • ‖(A (x0, μ) + A (periodicLatticeShift x0 μ, μ))
        - A (periodicLatticeShift y μ, μ)‖ :=
    Finset.sum_le_card_nsmul _ _ _ (fun x hx => hmax x hx)
  rw [hrw, norm_neg] at hn
  have hns : ‖((blockOf y 2).card • A (periodicLatticeShift y μ, μ))‖
      = ((blockOf y 2).card : ℝ) * ‖A (periodicLatticeShift y μ, μ)‖ := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((blockOf y 2).card : ℝ))]
  rw [hns] at hn
  rw [nsmul_eq_mul] at hle2
  have hcard : (0 : ℝ) < ((blockOf y 2).card : ℝ) := by
    have hpos := Finset.card_pos.2 hnem
    exact_mod_cast hpos
  have hcle : ‖A (periodicLatticeShift y μ, μ)‖
      ≤ ‖(A (x0, μ) + A (periodicLatticeShift x0 μ, μ)) - A (periodicLatticeShift y μ, μ)‖ :=
    le_of_mul_le_mul_left (by linarith) hcard
  have hMsq := hdev x0 hx0
  nlinarith [hcle, hM0, norm_nonneg (A (periodicLatticeShift y μ, μ)), hMsq]

/-- **THE PER-BOND LOCAL BOUND.** Every bond's energy is controlled by the budget of the block
holding its BASE SITE together with the budget of the block holding the site one step along the
bond — two blocks, never more. Same constant `69088` as the global
`FibreCoercivity.bond_energy_bound`. -/
theorem bond_energy_local (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    (b : Bond L) :
    ‖A b‖ ^ 2
      ≤ 69088 * (localG A (cc b.1) + localG A (cc (periodicLatticeShift b.1 b.2))) := by
  obtain ⟨z, μ⟩ := b
  have hg1 : (0 : ℝ) ≤ localG A (cc z) := localG_nonneg A (cc z)
  have hg2 : (0 : ℝ) ≤ localG A (cc (periodicLatticeShift z μ)) :=
    localG_nonneg A (cc (periodicLatticeShift z μ))
  by_cases hz : (z μ).val % 2 = 0
  · have h := intra_bond_local hdvd A z μ hz
    show ‖A (z, μ)‖ ^ 2 ≤ _
    nlinarith [h]
  · have hz1 : (z μ).val % 2 = 1 := by omega
    have hy : ∀ ν : Fin 3, ((cc z) ν).val % 2 = 0 := fun ν => cc_even z ν
    have hle : ∀ ν, ((fun w => (z w).val % 2) : Fin 3 → ℕ) ν ≤ 1 := by
      intro ν
      show (z ν).val % 2 ≤ 1
      omega
    have hze : z = addOff (cc z) (fun ν => (z ν).val % 2) := by
      refine addOff_of_val (cc z) z _ (fun ν => ?_)
      show (z ν).val = (cc z ν).val + (z ν).val % 2
      rw [cc_val]; omega
    have hnbr : cc (periodicLatticeShift z μ) = cnbr (cc z) μ := by
      conv_lhs => rw [hze]
      exact cc_shift_addOff_one hdvd hy hle μ (by simpa using hz1)
    have hpairEq : localG A (cc z) + localG A (cc (periodicLatticeShift z μ))
        = pairG A (cc z) μ := by
      rw [hnbr]
      rfl
    have hdev : ‖A (z, μ) - A (periodicLatticeShift (cc z) μ, μ)‖ ^ 2
        ≤ 11280 * pairG A (cc z) μ := by
      have key := inter_dev_local hdvd A hy (fun ν => (z ν).val % 2) hle μ (by simpa using hz1)
      rwa [← hze] at key
    have href := Q_inter_local hdvd A hQ (cc_mem z) μ
    have hsplit : A (z, μ)
        = (A (z, μ) - A (periodicLatticeShift (cc z) μ, μ))
          + A (periodicLatticeShift (cc z) μ, μ) := by abel
    have hb := sq_two (A (z, μ) - A (periodicLatticeShift (cc z) μ, μ))
      (A (periodicLatticeShift (cc z) μ, μ))
    rw [← hsplit] at hb
    show ‖A (z, μ)‖ ^ 2 ≤ 69088 * (localG A (cc z) + localG A (cc (periodicLatticeShift z μ)))
    rw [hpairEq]
    nlinarith [hb, hdev, href]

#print axioms inter_step_local
#print axioms inter_dev_local
#print axioms block_summand_dev_local
#print axioms Q_inter_local
#print axioms bond_energy_local

/-! ## §5. THE AGGREGATE — the multiplicity count, and the theorem -/

/-- **The reindexing.** `x ↦ x + e_μ` is a bijection of the site set, so a sum over sites of any
function of the SHIFTED site equals the sum of the function itself. This is the half of the count
the source module said was already available; `periodicLatticeShift_injective` is reused
(`CoarseCurl`), not re-proved. -/
theorem sum_shift_site (μ : Fin 3) (g : PeriodicLatticeSite L → ℝ) :
    ∑ x : PeriodicLatticeSite L, g (periodicLatticeShift x μ)
      = ∑ x : PeriodicLatticeSite L, g x := by
  have hinj : Function.Injective (fun x : PeriodicLatticeSite L => periodicLatticeShift x μ) :=
    AdalyFormal.Balaban.CoarseCurl.periodicLatticeShift_injective μ
  have hbij : Function.Bijective (fun x : PeriodicLatticeSite L => periodicLatticeShift x μ) :=
    Finite.injective_iff_bijective.1 hinj
  exact Fintype.sum_bijective _ hbij (fun x => g (periodicLatticeShift x μ)) g (fun _ => rfl)

/-- **The site-multiplicity count.** Charging every site to its own block costs at most the block
cardinality `8`, and nothing more — because the blocks TILE (§2). -/
theorem sum_localG_cc_le (A : Bond L → SuTwo) :
    ∑ x : PeriodicLatticeSite L, localG A (cc x)
      ≤ 8 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
  have h2 : ∀ y ∈ CoarseLattice L 2,
      (∑ x ∈ blockOf y 2, localG A (cc x)) ≤ 8 * localG A y := by
    intro y hy
    have hy2 : ∀ μ : Fin 3, (y μ).val % 2 = 0 := mem_CoarseLattice.1 hy
    have hcong : (∑ x ∈ blockOf y 2, localG A (cc x))
        = ∑ _x ∈ blockOf y 2, localG A y :=
      Finset.sum_congr rfl (fun x hx => by rw [(mem_blockOf_iff_cc hy2 x).1 hx])
    rw [hcong, Finset.sum_const, nsmul_eq_mul]
    have hc : ((blockOf y 2).card : ℝ) ≤ 8 := by exact_mod_cast card_blockOf_two_le y
    nlinarith [localG_nonneg A y, hc]
  calc ∑ x : PeriodicLatticeSite L, localG A (cc x)
      = ∑ y ∈ CoarseLattice L 2, ∑ x ∈ blockOf y 2, localG A (cc x) :=
        (sum_over_blocks (fun x => localG A (cc x))).symm
    _ ≤ ∑ y ∈ CoarseLattice L 2, 8 * localG A y := Finset.sum_le_sum h2
    _ = 8 * ∑ y ∈ CoarseLattice L 2, localG A y := by rw [Finset.mul_sum]
    _ = 8 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by rw [sum_localG]

/-- **THE AGGREGATE `L²` BOUND.** On `{Q A = 0}`, at block side `ell = 2`, flat background, every
periodic extent with `2 ∣ (L μ + 1)`:

`bondEnergy A ≤ 3316224 · (P_Ax(A) + curlEnergy A)`.

`3316224 = 69088 · 48` and the `48 = 2 · 3 · 8` is COUNTED: two blocks per bond (§4), three bond
directions, eight sites per block (§3). No factor depends on `L`. -/
theorem aggregate_fibre_bound (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0) :
    bondEnergy A ≤ 3316224 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
  set S := ∑ x : PeriodicLatticeSite L, localG A (cc x) with hSdef
  have hstep : (∑ b : Bond L, ‖A b‖ ^ 2)
      ≤ ∑ b : Bond L,
          69088 * (localG A (cc b.1) + localG A (cc (periodicLatticeShift b.1 b.2))) :=
    Finset.sum_le_sum (fun b _ => bond_energy_local hdvd A hQ b)
  have hdouble : (∑ b : Bond L,
        (localG A (cc b.1) + localG A (cc (periodicLatticeShift b.1 b.2)))) = 6 * S := by
    have e1 : (∑ b : Bond L,
          (localG A (cc b.1) + localG A (cc (periodicLatticeShift b.1 b.2))))
        = ∑ z : PeriodicLatticeSite L, ∑ μ : Fin 3,
            (localG A (cc z) + localG A (cc (periodicLatticeShift z μ))) :=
      Fintype.sum_prod_type _
    have e2 : ∀ z : PeriodicLatticeSite L,
        (∑ _μ : Fin 3, (localG A (cc z) + localG A (cc (periodicLatticeShift z _μ))))
          = 3 * localG A (cc z)
            + ∑ μ : Fin 3, localG A (cc (periodicLatticeShift z μ)) := by
      intro z
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      norm_num
    have e4 : (∑ z : PeriodicLatticeSite L,
          ∑ μ : Fin 3, localG A (cc (periodicLatticeShift z μ))) = 3 * S := by
      rw [Finset.sum_comm]
      have h5 : ∀ μ : Fin 3,
          (∑ z : PeriodicLatticeSite L, localG A (cc (periodicLatticeShift z μ))) = S :=
        fun μ => sum_shift_site μ (fun w => localG A (cc w))
      rw [Finset.sum_congr rfl (fun μ _ => h5 μ), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num
    rw [e1, Finset.sum_congr rfl (fun z _ => e2 z), Finset.sum_add_distrib, ← Finset.mul_sum, e4,
      ← hSdef]
    ring
  have hSle : S ≤ 8 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := sum_localG_cc_le A
  have hfin : bondEnergy A ≤ 69088 * (6 * S) := by
    show (∑ b : Bond L, ‖A b‖ ^ 2) ≤ 69088 * (6 * S)
    calc (∑ b : Bond L, ‖A b‖ ^ 2)
        ≤ ∑ b : Bond L,
            69088 * (localG A (cc b.1) + localG A (cc (periodicLatticeShift b.1 b.2))) := hstep
      _ = 69088 * ∑ b : Bond L,
            (localG A (cc b.1) + localG A (cc (periodicLatticeShift b.1 b.2))) :=
          (Finset.mul_sum _ _ _).symm
      _ = 69088 * (6 * S) := by rw [hdouble]
  linarith

#print axioms sum_shift_site
#print axioms sum_localG_cc_le
#print axioms aggregate_fibre_bound

/-! ## §6. THE COMPOSITION INTERFACE — `γ · bondEnergy ≤ ⟨A, Δ_k A⟩ + P_Ax`

`FibreCoercivity.deltaK_trivialU_eq_curlEnergy` (reused, not re-derived) identifies the campaign's
own `Δ_k` at the flat background with `curlEnergy`. So §5's inequality IS the bridge demand, with
`γ_agg = 1/3316224`. -/

/-- **THE AGGREGATE BOUND IN THE CONSUMER'S SHAPE.** `γ · bondEnergy A ≤ ⟨A, Δ_k A⟩ + P_Ax(A)` on
`{Q A = 0}`, with `γ = 1/3316224 > 0` and NO dependence on the lattice extent. -/
theorem aggregate_fibre_bound_deltaK (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0) :
    (1 / 3316224 : ℝ) * bondEnergy A
      ≤ deltaKQuadFormNormalizedCorrected (trivialU L) A + pAx A (CoarseLattice L 2) 2 := by
  have h := aggregate_fibre_bound hdvd A hQ
  rw [deltaK_trivialU_eq_curlEnergy]
  linarith

/-- `γ_agg` is a positive rational, stated so it cannot be read as an unspecified constant. -/
theorem gamma_agg_pos : (0 : ℝ) < 1 / 3316224 := by norm_num

theorem gamma_agg_value : (1 / 3316224 : ℝ) = 1 / (69088 * 48) := by norm_num

/-- `γ_agg` under a name, so a consumer can wire the CONSTANT rather than the numeral. It is a
plain `def` with a `rfl`-value, not an opaque parameter and not an existential — there is no data
here for a prover to choose. -/
noncomputable def gammaAgg : ℝ := 1 / 3316224

theorem gammaAgg_eq : gammaAgg = 1 / 3316224 := rfl

theorem gammaAgg_pos : 0 < gammaAgg := by
  rw [gammaAgg_eq]
  norm_num

/-- **THE WIRE.** `γ · bondEnergy A ≤ ⟨A, Δ_k A⟩ + P_Ax(A)` on `{Q A = 0}`, with the constant
named. Identical content to `aggregate_fibre_bound_deltaK`; this is the shape a composition lane
consumes as a hypothesis. -/
theorem aggregate_fibre_bound_gamma (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0) :
    gammaAgg * bondEnergy A
      ≤ deltaKQuadFormNormalizedCorrected (trivialU L) A + pAx A (CoarseLattice L 2) 2 := by
  rw [gammaAgg_eq]
  exact aggregate_fibre_bound_deltaK hdvd A hQ

#print axioms aggregate_fibre_bound_deltaK
#print axioms gamma_agg_pos
#print axioms gamma_agg_value
#print axioms gammaAgg
#print axioms gammaAgg_eq
#print axioms gammaAgg_pos
#print axioms aggregate_fibre_bound_gamma

/-! ## §7. CONTROLS — must-fire, must-not-fire, `L`-freeness, rescaling -/

section Controls

open AdalyFormal.Balaban.RegularUDomainWitness (witL5)

/-- A field with one nonzero bond has strictly positive `L²` energy. -/
theorem bondEnergy_pos (A : Bond L → SuTwo) {b0 : Bond L} (h : A b0 ≠ 0) : 0 < bondEnergy A := by
  have hpos : (0 : ℝ) < ‖A b0‖ ^ 2 := pow_pos (norm_pos_iff.2 h) 2
  have hle : ‖A b0‖ ^ 2 ≤ ∑ b : Bond L, ‖A b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b : Bond L => ‖A b‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b0)
  show (0 : ℝ) < ∑ b : Bond L, ‖A b‖ ^ 2
  linarith

/-- **MUST-FIRE AND MUST-NOT-FIRE, ON ONE FIELD.** At the closed alternating mode `altMode w`
(`w ≠ 0`), which SATISFIES the `Q A = 0` hypothesis:

* the constraint set is not `{0}` — `altMode w` is a nonzero member of it;
* the LEFT side `γ · bondEnergy` is STRICTLY POSITIVE, so the inequality is not a statement about
  zeros (must-fire);
* the RIGHT side is FINITE and STRICTLY POSITIVE (must-not-fire: the bound is not the trivial
  `0 ≤ ∞` or `x ≤ 0`);
* and the inequality itself holds there. -/
theorem aggregate_nonvacuous (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo) (hw : w ≠ 0) :
    (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
        lineCoarseRestrictCov (trivialU L) 2 (altMode w) b = 0)
      ∧ (altMode (L := L) w ≠ fun _ => 0)
      ∧ 0 < (1 / 3316224 : ℝ) * bondEnergy (altMode (L := L) w)
      ∧ 0 < deltaKQuadFormNormalizedCorrected (trivialU L) (altMode (L := L) w)
            + pAx (altMode (L := L) w) (CoarseLattice L 2) 2
      ∧ (1 / 3316224 : ℝ) * bondEnergy (altMode (L := L) w)
          ≤ deltaKQuadFormNormalizedCorrected (trivialU L) (altMode (L := L) w)
            + pAx (altMode (L := L) w) (CoarseLattice L 2) 2 := by
  have hbnz : altMode (L := L) w ((zeroSite L), (0 : Fin 3)) ≠ 0 := by
    rw [altMode_eq w (b := (((zeroSite L), (0 : Fin 3)) : Bond L)) rfl]
    have hpar : par (zeroSite L) = 1 := by unfold par; rw [if_pos (zeroSite_even 0)]
    rw [hpar, one_smul]
    exact hw
  have hE : 0 < bondEnergy (altMode (L := L) w) := bondEnergy_pos _ hbnz
  have hDz : deltaKQuadFormNormalizedCorrected (trivialU L) (altMode (L := L) w) = 0 :=
    (closedFlat_iff_deltaK_zero (altMode (L := L) w)).1 (altMode_closed w)
  have hPnn : (0 : ℝ) ≤ pAx (altMode (L := L) w) (CoarseLattice L 2) 2 :=
    pAx_nonneg _ _ 2
  have hPne : pAx (altMode (L := L) w) (CoarseLattice L 2) 2 ≠ 0 := altMode_pAx_ne hdvd w hw
  refine ⟨altMode_Q hdvd w, altMode_field_ne w hw, by linarith, ?_,
    aggregate_fibre_bound_deltaK hdvd _ (altMode_Q hdvd w)⟩
  rw [hDz]
  exact lt_of_le_of_ne hPnn (Ne.symm hPne) |>.trans_le (le_of_eq (by ring))

/-- The extent `4³`, an even extent DIFFERENT from the campaign's `6³` witness. -/
def witL3 : PeriodicLatticeExtent := fun _ => 3

theorem hdvd_witL3 : ∀ μ : Fin 3, (2 : ℕ) ∣ (witL3 μ + 1) := by decide

theorem hdvd_witL5' : ∀ μ : Fin 3, (2 : ℕ) ∣ (witL5 μ + 1) := hdvd_witL5

/-- The bond count at the `4³` extent — the constant `bondEnergy_le_with_volume_factor` would
carry there. Proved, not asserted in prose. -/
theorem card_bond_witL3 : Fintype.card (Bond witL3) = 192 := by decide

/-- The bond count at the `6³` extent. `648 ≠ 192`: the volume factor is NOT the same number at the
two extents in `aggregate_two_extents`, and `3316224` is. -/
theorem card_bond_witL5 : Fintype.card (Bond witL5) = 648 := by decide

theorem card_bond_differs : Fintype.card (Bond witL3) ≠ Fintype.card (Bond witL5) := by
  rw [card_bond_witL3, card_bond_witL5]
  decide

/-- **`γ_agg` IS `L`-FREE — exhibited, not asserted.** The SAME numeral `1/3316224` works at the
`4³` extent and at the `6³` extent. A volume-dependent constant could not do this:
`bondEnergy_le_with_volume_factor`'s constant is `Fintype.card (Bond L)`, and
`card_bond_differs` proves that number is NOT the same on these two lines (`192` vs `648`). -/
theorem aggregate_two_extents :
    (∀ (A : Bond witL3 → SuTwo),
        (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL3 2,
          lineCoarseRestrictCov (trivialU witL3) 2 A b = 0) →
        (1 / 3316224 : ℝ) * bondEnergy A
          ≤ deltaKQuadFormNormalizedCorrected (trivialU witL3) A
            + pAx A (CoarseLattice witL3 2) 2)
      ∧ (∀ (A : Bond witL5 → SuTwo),
        (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2,
          lineCoarseRestrictCov (trivialU witL5) 2 A b = 0) →
        (1 / 3316224 : ℝ) * bondEnergy A
          ≤ deltaKQuadFormNormalizedCorrected (trivialU witL5) A
            + pAx A (CoarseLattice witL5 2) 2) :=
  ⟨fun A hQ => aggregate_fibre_bound_deltaK hdvd_witL3 A hQ,
   fun A hQ => aggregate_fibre_bound_deltaK hdvd_witL5' A hQ⟩

/-- The campaign's own alternating witness IS this module's `altMode`, at the `6³` extent and the
`𝔰𝔲(2)` generator `rotGen`. `BridgeRestricted.altC` and `FibreCoercivity.par` have literally the
same body, so the two fields are the same function — which is what lets `AxialCoercivity`'s EXACT
numeric evaluations be read as evaluations of the field this module's controls use. -/
theorem axisField_eq_altMode :
    AdalyFormal.Balaban.BridgeRestricted.axisField (0 : Fin 3)
        AdalyFormal.Balaban.BridgeRestricted.altC AdalyFormal.Balaban.BridgeRestricted.rotGen
      = altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen := by
  funext b
  show (if b.2 = (0 : Fin 3)
      then (AdalyFormal.Balaban.BridgeRestricted.altC b.1)
        • AdalyFormal.Balaban.BridgeRestricted.rotGen else 0)
    = (if b.2 = (0 : Fin 3)
      then (par b.1) • AdalyFormal.Balaban.BridgeRestricted.rotGen else 0)
  rfl

/-- **BOTH SIDES, AS EXPLICIT NUMBERS, AT A NAMED NONZERO FIELD.** At the `6³` extent and the
closed alternating mode:

* `bondEnergy = 216‖rotGen‖²` (`AxialCoercivity.bondEnergy_altField`, reused),
* `⟨A, Δ_k A⟩ + P_Ax(A) = 108‖rotGen‖²` (`Δ_k` vanishes: the mode is closed; `P_Ax` is
  `AxialCoercivity.pAx_altField`, reused),
* `‖rotGen‖² > 0`,
* and the aggregate bound reads `216/3316224 · ‖rotGen‖² ≤ 108‖rotGen‖²`, which holds.

So the inequality is not a statement about zeros on either side, and the two sides are actual
computed numbers rather than existentially quantified quantities. -/
theorem aggregate_numeric_at_alternating :
    bondEnergy (altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)
        = 216 * ‖AdalyFormal.Balaban.BridgeRestricted.rotGen‖ ^ 2
      ∧ deltaKQuadFormNormalizedCorrected (trivialU witL5)
            (altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)
          + pAx (altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)
              (CoarseLattice witL5 2) 2
        = 108 * ‖AdalyFormal.Balaban.BridgeRestricted.rotGen‖ ^ 2
      ∧ 0 < ‖AdalyFormal.Balaban.BridgeRestricted.rotGen‖ ^ 2
      ∧ (1 / 3316224 : ℝ) * (216 * ‖AdalyFormal.Balaban.BridgeRestricted.rotGen‖ ^ 2)
          ≤ 108 * ‖AdalyFormal.Balaban.BridgeRestricted.rotGen‖ ^ 2 := by
  have hpos : 0 < ‖AdalyFormal.Balaban.BridgeRestricted.rotGen‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 AdalyFormal.Balaban.BridgeRestricted.rotGen_ne_zero) 2
  have hB : bondEnergy (altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)
      = 216 * ‖AdalyFormal.Balaban.BridgeRestricted.rotGen‖ ^ 2 := by
    rw [← axisField_eq_altMode]
    exact bondEnergy_altField
  have hDz : deltaKQuadFormNormalizedCorrected (trivialU witL5)
      (altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen) = 0 :=
    (closedFlat_iff_deltaK_zero _).1 (altMode_closed _)
  have hP : pAx (altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)
      (CoarseLattice witL5 2) 2
      = 108 * ‖AdalyFormal.Balaban.BridgeRestricted.rotGen‖ ^ 2 := by
    rw [← axisField_eq_altMode]
    exact pAx_altField
  exact ⟨hB, by rw [hDz, hP, zero_add], hpos, by nlinarith [hpos]⟩

/-- **RESCALE CONTROL.** Both sides of the aggregate bound are homogeneous of degree `2` in `A`, so
no choice of overall normalization can make it true or false; in particular `γ_agg` is not an
artefact of a normalization convention. -/
theorem aggregate_is_homogeneous (A : Bond L → SuTwo) (t : ℝ) :
    bondEnergy (fun b => t • A b) = t ^ 2 * bondEnergy A
      ∧ curlEnergy (fun b => t • A b) = t ^ 2 * curlEnergy A
      ∧ pAx (fun b => t • A b) (CoarseLattice L 2) 2 = t ^ 2 * pAx A (CoarseLattice L 2) 2 := by
  refine ⟨?_, (quantitative_bound_is_homogeneous A t ((zeroSite L), (0 : Fin 3))
      (CoarseLattice L 2) 2).2.1, pAx_smul A (CoarseLattice L 2) 2 t⟩
  show (∑ b : Bond L, ‖t • A b‖ ^ 2) = t ^ 2 * ∑ b : Bond L, ‖A b‖ ^ 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- **THE AGGREGATE IMPLIES THE TRIPLE-KERNEL TRIVIALITY**, so the constant `3316224` is not hiding
a vacuity: setting the right-hand side to `0` returns `A = 0`. Proved by running the AGGREGATE
bound at the hypotheses of `triple_kernel_trivial`, not by re-invoking it — a genuine cross-check
of the aggregated chain against the qualitative one. -/
theorem aggregate_implies_qualitative (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo) (hc : closedFlat A)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    (hP : pAx A (CoarseLattice L 2) 2 = 0) :
    A = fun _ => 0 := by
  have hCz : curlEnergy A = 0 := by
    unfold curlEnergy
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [hc p, norm_zero]
    norm_num
  have h := aggregate_fibre_bound hdvd A hQ
  rw [hP, hCz] at h
  have hzero : bondEnergy A ≤ 0 := by linarith
  funext b
  have hle : ‖A b‖ ^ 2 ≤ ∑ c : Bond L, ‖A c‖ ^ 2 :=
    Finset.single_le_sum (f := fun c : Bond L => ‖A c‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b)
  have hb : ‖A b‖ ^ 2 ≤ 0 := le_trans hle hzero
  have h1 : ‖A b‖ = 0 := by nlinarith [norm_nonneg (A b), hb]
  exact norm_eq_zero.1 h1

end Controls

#print axioms bondEnergy_pos
#print axioms aggregate_nonvacuous
#print axioms witL3
#print axioms hdvd_witL3
#print axioms hdvd_witL5'
#print axioms card_bond_witL3
#print axioms card_bond_witL5
#print axioms card_bond_differs
#print axioms aggregate_two_extents
#print axioms axisField_eq_altMode
#print axioms aggregate_numeric_at_alternating
#print axioms aggregate_is_homogeneous
#print axioms aggregate_implies_qualitative

end AdalyFormal.Balaban.FibreAggregate
