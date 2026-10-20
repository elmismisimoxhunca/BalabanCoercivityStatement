/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RegularUCoercivityFull

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[REGU-DOMAIN-NONVAC]` — the domain of `deltaJ_regularU_coercive_on_kerQU` is NOT `{0}`

**The residual this closes.** `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` quantifies
over all su(2) fields `A` satisfying simultaneously

* `hadm` — the su(2) **axial gauge**: `A b = 0` for every `b ∈ Γ_{y,x}`, every `y ∈ Λ'`, every
  `x ∈ B(y)` (CMP96 (2.121), `AdmissibleSubspace.staircasePath`), and
* `hkerU` — membership in `ker Q₁(U)`: `lineCoarseRestrictCov U 2 A b = 0` for every coarse
  bond `b`.

Prosecutor `PROS-REGULARU-COERC-FULL` (grade-1, 2026-07-25) found NO witness anywhere in the tree
that this intersection contains a nonzero field, and no proof that it is `{0}` — i.e. the theorem
might have been VACUOUS. This module settles it: **the intersection is genuinely nonzero**, by an
EXPLICIT kernel-checked witness at `U = trivialU` (a legitimate instance of the `∀ U` theorem, whose
smallness hypotheses `hthr`/`hsmall` hold there because `frobSupBond (trivialU) = 0`).

## The witness (stated concretely, no existential over free data)

* **Lattice** `witL5 : PeriodicLatticeExtent := fun _ => 5` — six sites `0..5` per axis. It
  satisfies BOTH standing hypotheses of the target theorem: `4 ≤ witL5 μ` (`4 ≤ 5`) and
  `2 ∣ witL5 μ + 1` (`2 ∣ 6`), so every block of side `ell = 2` is a genuine full `2³` block
  (no `blockOf` truncation — the torus artifact recorded in `MEMORY.md`).
* **The field** `witA := witChi • suTwoWitness`, where `witChi` is the `±1` indicator of the two
  DIRECTION-`0` bonds based at `sPlus = (5,5,5)` and `sMinus = (5,4,5)`:
  `witA (sPlus,0) = w`, `witA (sMinus,0) = -w`, `witA = 0` on all other bonds
  (`w = suTwoWitness = i·diag(1,-1)`).

## Why it works (the two mechanisms, both proved below, not asserted)

1. **Axial gauge.** `§1`'s `dir0_top_not_mem_staircase` generalizes
   `AdmissibleSubspace.generalWrapBond_not_mem_any`: ANY direction-`0` bond whose base site has
   coordinate `0` equal to the TOP value `L 0` lies off `Γ_{y,x}` for every valid `(y,x)`. Reason:
   the direction-`0` segment of `Γ_{y,x}` is `axisSegment (corner2 y x) 0 (min y₀ x₀) (max y₀ x₀)`,
   whose members satisfy `(e.1 0).val < max y₀ x₀ = x₀ ≤ L 0` STRICTLY; the direction-`2`/`1`
   segments are excluded on direction alone. Both `sPlus` and `sMinus` have coordinate `0` equal to
   `5 = witL5 0`, so BOTH bonds are off every staircase — the axial gauge is satisfied vacuously on
   the support of `witA`.
2. **`ker Q₁(1)` by exact ± cancellation.** At `U = 1`,
   `lineCoarseRestrictCov (trivialU) 2 A b = (1/2⁴) • Σ_{x ∈ B(b₋)} Σ_{i<2} A(pathSite x b₂ i, b₂)`
   (`lineCoarseRestrictCov_trivialU` ⟶ `lineCoarseRestrictSuTwo`). A direction-`0` bond is read only
   by direction-`0` coarse bonds, and each of the FOUR sites that can produce `sPlus` or `sMinus`
   along a length-`2` segment — `sPlus = (5,5,5)`, `sMinus = (5,4,5)` at `i = 0`, and their backward
   shifts `tPlus = (4,5,5)`, `tMinus = (4,4,5)` at `i = 1` — has ALL THREE coordinates in `{4,5}`.
   On a `Λ'`-aligned coarse centre (`ell = 2`, all coordinates even) that pins the owning block to
   the SINGLE centre `cCenter = (4,4,4)` (`§3`'s `mem_blockOf_iff_center`). So each coarse sum sees
   the `+w` and the `−w` contribution together, or neither: every coarse sum vanishes EXACTLY.

## What is established (three PROVED properties + the payoff)

* `witA_axial` — `witA` satisfies the su(2) axial gauge on `witL5`, `ell = 2`.
* `witA_mem_kerQ1` — `∀ b : CoarseBond witL5 2`,
  `lineCoarseRestrictCov (trivialU witL5) 2 witA b = 0`.
* `witA_ne_zero` — `witA ≠ 0`.
* `regularU_domain_nonvacuous` — the three bundled: `[REGU-DOMAIN-NONVAC]` RESOLVED, the domain
  is `≠ {0}`.
* `bondEnergy_witA_pos` — `0 < bondEnergy witA`, so the coercivity inequality at `witA` has a
  STRICTLY POSITIVE left-hand side: not merely non-vacuous but non-trivial.
* `deltaJ_coercive_at_witA` — the target theorem INSTANTIATED at this witness,
  `γ₀ · bondEnergy witA ≤ deltaJ(1) witA` with `γ₀ = (1/108)(1/2⁴)`.
* `witASingle_value` / `witASingle_not_mem_kerQ1` — **control A**: delete the `−` bond and
  `ker Q₁(1)` FAILS, with the exact value `(1/8)·w`. The coarse sums genuinely READ these bonds
  (multiplicity `2`), so `witA_mem_kerQ1` is not a degenerate pass.
* `dir0_bond_on_staircase` / `witALow_not_axial` — **control B**: move the support off the top
  coordinate and the axial gauge FAILS; the gauge really constrains direction-`0` bonds.

## Honest scope (§LEAN-D / no-success-lie)

* The witness is at `U = trivialU`. That is a legitimate instance of the `∀ U` theorem and it
  defeats vacuity of the theorem AS STATED (`∀ U, ∀ A, P U A → Q U A` is vacuous only if the
  hypothesis set is empty for EVERY `U`; here it is nonempty for `U = 1`). It does NOT prove the
  domain is nonzero for every fixed non-trivial `U` — that is a strictly stronger, separate claim,
  and it is NAMED here as `[REGU-DOMAIN-NONVAC-GENERALU]`, with the evidence of resistance recorded
  in `§7` below (attempted in this pass, not closed).
* L1-L3 clean: no incomplete proofs, no compiler-trusted decision procedure, no new axiom, no
  unchecked-implementation attributes. Every `decide` here is an ordinary KERNEL decision over a
  `Fin 3`/`Fin 6`-sized finite proposition.
* Read-only reuse (LAW-19): `AdmissibleSubspace`, `LineIntegralCovariant`, `QOne`,
  `CovariantHjMinimizer`, `RegularUPerturbation`, `RegularUCoercivityFull`. Nothing rebuilt.
-/

namespace AdalyFormal.Balaban.RegularUDomainWitness

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.RegularUCoercivityFull
open AdalyFormal.Balaban.CovariantHjMinimizer
  (trivialU periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

/-! ## §1 — the general geometric mechanism: TOP-coordinate direction-`0` bonds are off EVERY
staircase

`AdmissibleSubspace.generalWrapBond_not_mem_any` proves this for the ONE bond based at
`maximalSite L` (every coordinate at the top). Its proof, read line by line, uses ONLY coordinate
`0` of the base site; the other coordinates are never touched. This section extracts exactly that
strength, which is what a ± CANCELLING PAIR needs (the two bonds must differ in a transverse
coordinate, so `maximalSite` alone cannot supply both). -/

/-- **Any direction-`0` bond whose base site sits at the TOP coordinate-`0` value `L 0` lies off
`Γ_{y,x}` for every `(2.121)`-valid pair.** Generalizes `generalWrapBond_not_mem_any` (which is the
special case `z = maximalSite L`) by dropping every constraint on coordinates `1`, `2`. The only
hypothesis used besides `hz` is `x ∈ blockOf y ell`, i.e. `(2.121)`'s own antecedent. -/
theorem dir0_top_not_mem_staircase {L : PeriodicLatticeExtent} {ell : ℕ}
    (z : PeriodicLatticeSite L) (hz : (z 0).val = L 0)
    {y x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell) :
    ((z, (0 : Fin 3)) : Bond L) ∉ staircasePath y x := by
  rw [mem_blockOf] at hx
  intro hb
  simp only [staircasePath, Finset.mem_union] at hb
  rcases hb with hab | h0
  · rcases hab with h2 | h1
    · have hd := (mem_axisSegment.mp h2).1
      have hv := congrArg Fin.val hd
      norm_num at hv
    · have hd := (mem_axisSegment.mp h1).1
      have hv := congrArg Fin.val hd
      norm_num at hv
  · have hm := (mem_axisSegment.mp h0).2.2.2
    have hyx : (y 0).val ≤ (x 0).val := (hx 0).1
    rw [max_eq_right hyx] at hm
    have hxle : (x 0).val ≤ L 0 := Nat.le_of_lt_succ (x 0).isLt
    change (z 0).val < (x 0).val at hm
    rw [hz] at hm
    omega

/-- **The general shift-preimage law**, the reindexing fact the `i = 1` half of every length-`2`
segment sum needs. Pure `Equiv` bookkeeping on `CovariantHjMinimizer`'s already-proved inverse pair
(LAW-19: `periodicLatticeShiftEquiv` exists; this is its `Iff` face). -/
theorem shift_eq_iff_shiftBack {L : PeriodicLatticeExtent} (x z : PeriodicLatticeSite L)
    (μ : Fin 3) : periodicLatticeShift x μ = z ↔ x = periodicLatticeShiftBack z μ := by
  constructor
  · rintro rfl; rw [periodicLatticeShiftBack_shift]
  · rintro rfl; rw [periodicLatticeShift_shiftBack]

/-! ## §2 — the witness lattice and the two cancelling bonds -/

/-- **The witness lattice**: extent `5` in every direction, i.e. six sites `0,…,5` per axis. Chosen
to satisfy BOTH standing hypotheses of `deltaJ_regularU_coercive_on_kerQU` — `4 ≤ L μ` and
`2 ∣ L μ + 1` (`2 ∣ 6`) — so blocks of side `2` are FULL `2³` blocks and `blockOf` does not
truncate. -/
def witL5 : PeriodicLatticeExtent := fun _ => 5

theorem witL5_four_le : ∀ μ : Fin 3, 4 ≤ witL5 μ := by decide

theorem witL5_two_dvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (witL5 μ + 1) := by decide

/-- `(5,5,5)` — the top corner. -/
def sPlus : PeriodicLatticeSite witL5 := fun _ => 5

/-- `(5,4,5)` — the top corner with the TRANSVERSE coordinate `1` lowered by one. Same
coordinate-`0` value `5`, so it enjoys the SAME axial-gauge exclusion (§1); same owning block, so it
cancels `sPlus` in every coarse sum (§3/§4). -/
def sMinus : PeriodicLatticeSite witL5 := fun ν => if ν = 1 then 4 else 5

/-- The `+` bond: direction `0`, based at `sPlus`. -/
def bPlus : Bond witL5 := (sPlus, 0)

/-- The `−` bond: direction `0`, based at `sMinus`. -/
def bMinus : Bond witL5 := (sMinus, 0)

theorem bPlus_ne_bMinus : bPlus ≠ bMinus := by decide

/-- `(4,5,5)` — the backward `e₀`-shift of `sPlus`, the site that reaches `bPlus` at `i = 1`. -/
def tPlus : PeriodicLatticeSite witL5 := periodicLatticeShiftBack sPlus 0

/-- `(4,4,5)` — the backward `e₀`-shift of `sMinus`. -/
def tMinus : PeriodicLatticeSite witL5 := periodicLatticeShiftBack sMinus 0

/-- **The scalar `±1` profile**: `+1` on `bPlus`, `−1` on `bMinus`, `0` elsewhere. -/
noncomputable def witChi : Bond witL5 → ℝ :=
  fun e => (if e = bPlus then (1 : ℝ) else 0) - (if e = bMinus then (1 : ℝ) else 0)

/-- **THE WITNESS FIELD** `witA = witChi • suTwoWitness` — the explicit su(2) bond field claimed to
live in `axial-gauge ∩ ker Q₁(1)` and to be nonzero. -/
noncomputable def witA : Bond witL5 → SuTwo := fun e => witChi e • suTwoWitness

theorem witA_bPlus : witA bPlus = suTwoWitness := by
  have h : witChi bPlus = 1 := by
    simp [witChi, bPlus_ne_bMinus]
  rw [witA, h, one_smul]

/-- **Property (3): `witA ≠ 0`.** -/
theorem witA_ne_zero : witA ≠ 0 := by
  intro h
  have hb : witA bPlus = 0 := by rw [h]; rfl
  rw [witA_bPlus] at hb
  exact suTwoWitness_ne_zero hb

/-! ## §3 — the block-alignment mechanism: on a `Λ'`-aligned centre, all four relevant sites are
owned by the SAME block `B((4,4,4))` -/

/-- The unique coarse centre owning every site with all coordinates in `{4,5}`. -/
def cCenter : PeriodicLatticeSite witL5 := fun _ => 4

/-- **The alignment lemma.** For a `Λ'`-aligned coarse centre `y` (all coordinates even, `ell = 2`),
a site whose every coordinate lies in `{4,5}` belongs to `B(y)` IF AND ONLY IF `y = (4,4,4)`. This
is where evenness of the coarse centre is load-bearing: without `hy` the site `(5,5,5)` would also
sit in `B((5,5,5))`, and the cancellation below would fail. -/
theorem mem_blockOf_iff_center {w : PeriodicLatticeSite witL5}
    (hw : ∀ ν : Fin 3, (w ν).val = 4 ∨ (w ν).val = 5)
    {y : PeriodicLatticeSite witL5} (hy : y ∈ CoarseLattice witL5 2) :
    w ∈ blockOf y 2 ↔ y = cCenter := by
  rw [mem_CoarseLattice] at hy
  rw [mem_blockOf]
  constructor
  · intro h
    funext ν
    apply Fin.ext
    have h1 := (h ν).1
    have h2 := (h ν).2
    have h3 := hy ν
    have h4 := hw ν
    have hc : (cCenter ν).val = 4 := rfl
    omega
  · rintro rfl
    intro ν
    have h4 := hw ν
    have hc : (cCenter ν).val = 4 := rfl
    omega

theorem sPlus_coords : ∀ ν : Fin 3, (sPlus ν).val = 4 ∨ (sPlus ν).val = 5 := by decide

theorem sMinus_coords : ∀ ν : Fin 3, (sMinus ν).val = 4 ∨ (sMinus ν).val = 5 := by decide

theorem tPlus_coords : ∀ ν : Fin 3, (tPlus ν).val = 4 ∨ (tPlus ν).val = 5 := by decide

theorem tMinus_coords : ∀ ν : Fin 3, (tMinus ν).val = 4 ∨ (tMinus ν).val = 5 := by decide

/-! ## §4 — every coarse block-segment sum of `witChi` vanishes -/

/-- **The `ell = 2` block-segment sum, split into its `i = 0` and `i = 1` halves.** Reused by §4
and by §6b's controls (LAW-19: built once). -/
theorem blockSegSum_split (y : PeriodicLatticeSite witL5) (μ : Fin 3) (f : Bond witL5 → ℝ) :
    (∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, f (pathSite x μ i, μ))
      = (∑ x ∈ blockOf y 2, f (x, μ)) + (∑ x ∈ blockOf y 2, f (periodicLatticeShift x μ, μ)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rfl

/-- **The cancellation, in full.** For every `Λ'`-aligned coarse centre `y` and every direction `μ`,
the `Q₁(1)` block-segment sum of `witChi` is EXACTLY zero.

Two cases. `μ ≠ 0`: `witChi` is supported on direction-`0` bonds only, so every summand is `0`.
`μ = 0`: the `i = 0` half contributes `[sPlus ∈ B(y)] − [sMinus ∈ B(y)]` and the `i = 1` half
contributes `[tPlus ∈ B(y)] − [tMinus ∈ B(y)]`; by §3 all four memberships are equivalent to
`y = (4,4,4)`, so both halves vanish identically. -/
theorem witChi_blockSum_zero (y : PeriodicLatticeSite witL5) (hy : y ∈ CoarseLattice witL5 2)
    (μ : Fin 3) :
    (∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, witChi (pathSite x μ i, μ)) = 0 := by
  rw [blockSegSum_split]
  by_cases hμ : μ = 0
  · subst hμ
    have hA : (∑ x ∈ blockOf y 2, witChi (x, (0 : Fin 3))) = 0 := by
      have hx : ∀ x : PeriodicLatticeSite witL5, witChi (x, (0 : Fin 3))
          = (if x = sPlus then (1 : ℝ) else 0) - (if x = sMinus then (1 : ℝ) else 0) := by
        intro x
        simp only [witChi, bPlus, bMinus, Prod.mk.injEq, and_true]
      simp only [hx, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        mem_blockOf_iff_center sPlus_coords hy, mem_blockOf_iff_center sMinus_coords hy, sub_self]
    have hB : (∑ x ∈ blockOf y 2,
        witChi (periodicLatticeShift x (0 : Fin 3), (0 : Fin 3))) = 0 := by
      have e1 : ∀ x : PeriodicLatticeSite witL5,
          ((periodicLatticeShift x (0 : Fin 3), (0 : Fin 3)) = bPlus) ↔ (x = tPlus) := by
        intro x
        rw [bPlus, Prod.mk.injEq]
        constructor
        · rintro ⟨h, -⟩
          exact (shift_eq_iff_shiftBack x sPlus 0).mp h
        · intro h
          exact ⟨(shift_eq_iff_shiftBack x sPlus 0).mpr h, rfl⟩
      have e2 : ∀ x : PeriodicLatticeSite witL5,
          ((periodicLatticeShift x (0 : Fin 3), (0 : Fin 3)) = bMinus) ↔ (x = tMinus) := by
        intro x
        rw [bMinus, Prod.mk.injEq]
        constructor
        · rintro ⟨h, -⟩
          exact (shift_eq_iff_shiftBack x sMinus 0).mp h
        · intro h
          exact ⟨(shift_eq_iff_shiftBack x sMinus 0).mpr h, rfl⟩
      have hx : ∀ x : PeriodicLatticeSite witL5,
          witChi (periodicLatticeShift x (0 : Fin 3), (0 : Fin 3))
            = (if x = tPlus then (1 : ℝ) else 0) - (if x = tMinus then (1 : ℝ) else 0) := by
        intro x
        rw [witChi]
        congr 1
        · exact if_congr (e1 x) rfl rfl
        · exact if_congr (e2 x) rfl rfl
      simp only [hx, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        mem_blockOf_iff_center tPlus_coords hy, mem_blockOf_iff_center tMinus_coords hy, sub_self]
    rw [hA, hB, add_zero]
  · -- `witChi` is supported on DIRECTION-`0` bonds only, so at `μ ≠ 0` every summand vanishes
    -- (this single fact covers BOTH halves: the `i = 1` summand is `witChi (shift x μ, μ)`, an
    -- instance of the same `∀ x` statement at the shifted site).
    have hA : ∀ x : PeriodicLatticeSite witL5, witChi (x, μ) = 0 := by
      intro x
      simp only [witChi, bPlus, bMinus, Prod.mk.injEq, hμ, and_false, if_false, sub_zero]
    simp only [hA, Finset.sum_const_zero, add_zero]

/-! ## §5 — THE THREE PROPERTIES -/

/-- **Property (1): the su(2) AXIAL GAUGE.** `witA` vanishes on `Γ_{y,x}` for every coarse centre
`y ∈ Λ'` and every `x ∈ B(y)` — exactly `deltaJ_regularU_coercive_on_kerQU`'s `hadm`. Both bonds in
`witA`'s support sit at coordinate-`0` value `5 = witL5 0`, so §1 excludes them from every
staircase. -/
theorem witA_axial : ∀ y : PeriodicLatticeSite witL5, y ∈ CoarseLattice witL5 2 →
    ∀ x : PeriodicLatticeSite witL5, x ∈ blockOf y 2 →
      ∀ b ∈ staircasePath y x, witA b = 0 := by
  intro y _hy x hx b hb
  have h1 : b ≠ bPlus := by
    rintro rfl
    exact dir0_top_not_mem_staircase (ell := 2) sPlus (by decide) hx hb
  have h2 : b ≠ bMinus := by
    rintro rfl
    exact dir0_top_not_mem_staircase (ell := 2) sMinus (by decide) hx hb
  have hchi : witChi b = 0 := by
    simp only [witChi, if_neg h1, if_neg h2, sub_zero]
  rw [witA, hchi, zero_smul]

/-- **Property (2): `witA ∈ ker Q₁(1)`.** Every coarse-bond value of the faithful covariant
line-integral `Q₁` at the trivial background vanishes — the exact ± cancellation of §4. -/
theorem witA_mem_kerQ1 : ∀ b : CoarseBond witL5 2,
    lineCoarseRestrictCov (trivialU witL5) 2 witA b = 0 := by
  intro b
  rw [lineCoarseRestrictCov_trivialU]
  unfold lineCoarseRestrictSuTwo
  have hz : (∑ x ∈ blockOf b.1.1 2, ∑ i ∈ Finset.range 2, witA (pathSite x b.2 i, b.2)) = 0 := by
    have hchi : ∀ (x : PeriodicLatticeSite witL5) (i : ℕ),
        witA (pathSite x b.2 i, b.2) = witChi (pathSite x b.2 i, b.2) • suTwoWitness :=
      fun _ _ => rfl
    simp only [hchi, ← Finset.sum_smul]
    rw [witChi_blockSum_zero b.1.1 b.1.2 b.2, zero_smul]
  rw [hz, smul_zero]

/-- **`[REGU-DOMAIN-NONVAC]` RESOLVED — the domain is NOT `{0}`.** The intersection
`axial-gauge ∩ ker Q₁(trivialU)` on the compatible torus `witL5` (`4 ≤ L μ`, `2 ∣ L μ + 1`) contains
the explicit NONZERO field `witA`. Hence
`RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` is NOT vacuous. -/
theorem regularU_domain_nonvacuous :
    (∀ y : PeriodicLatticeSite witL5, y ∈ CoarseLattice witL5 2 →
        ∀ x : PeriodicLatticeSite witL5, x ∈ blockOf y 2 →
          ∀ b ∈ staircasePath y x, witA b = 0) ∧
      (∀ b : CoarseBond witL5 2, lineCoarseRestrictCov (trivialU witL5) 2 witA b = 0) ∧
      witA ≠ 0 :=
  ⟨witA_axial, witA_mem_kerQ1, witA_ne_zero⟩

#print axioms dir0_top_not_mem_staircase
#print axioms witChi_blockSum_zero
#print axioms witA_axial
#print axioms witA_mem_kerQ1
#print axioms witA_ne_zero
#print axioms regularU_domain_nonvacuous

/-! ## §6 — the payoff: the target theorem INSTANTIATED, with a strictly positive left-hand side

Non-vacuity of the domain would still leave the coercivity statement CONTENTLESS at the witness if
`bondEnergy witA = 0` (the inequality would read `0 ≤ deltaJ`). It does not: `bondEnergy witA > 0`,
so the instantiated inequality genuinely lower-bounds `deltaJ(1) witA` by a positive multiple of a
positive energy. -/

/-- `frobSupBond (trivialU L) = 0` — the trivial background is at zero distance from `1` in the
`sup_b` Frobenius sense, so the target theorem's smallness hypotheses hold TRIVIALLY there. -/
theorem frobSupBond_trivialU (L : PeriodicLatticeExtent) : frobSupBond (trivialU L) = 0 := by
  unfold frobSupBond
  have hconst : ∀ b : Bond L,
      RMapLipschitz.frobNorm (((trivialU L) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0 := by
    intro b
    rw [show ((trivialU L) b : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl, sub_self,
      RMapLipschitz.frobNorm_zero]
  simp only [hconst]
  exact Finset.sup'_const _ _

/-- **The witness carries strictly positive bond energy** — the instantiated coercivity inequality
is not the trivial `0 ≤ deltaJ`. -/
theorem bondEnergy_witA_pos : 0 < bondEnergy witA := by
  have hle : ‖witA bPlus‖ ^ 2 ≤ ∑ b : Bond witL5, ‖witA b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b : Bond witL5 => ‖witA b‖ ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ bPlus)
  have hpos : (0 : ℝ) < ‖witA bPlus‖ ^ 2 := by
    have hne : witA bPlus ≠ 0 := by rw [witA_bPlus]; exact suTwoWitness_ne_zero
    have : (0 : ℝ) < ‖witA bPlus‖ := norm_pos_iff.mpr hne
    positivity
  unfold bondEnergy
  linarith

/-- **`deltaJ_regularU_coercive_on_kerQU`, INSTANTIATED at the witness.** With
`α₁ = frobSupBond (trivialU) = 0` the two smallness hypotheses are trivial and the constant
collapses to `γ₀ = (1/108)(1/2⁴)`:

  `γ₀ · bondEnergy witA ≤ deltaJ(1) witA`,   `0 < bondEnergy witA`.

A non-vacuous, non-trivial instance of the headline regular-`U` coercivity. -/
theorem deltaJ_coercive_at_witA :
    (1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4) * bondEnergy witA
      ≤ dstarDQuadForm (trivialU witL5) witA := by
  have hα : frobSupBond (trivialU witL5) = 0 := frobSupBond_trivialU witL5
  have hγ0 : (0 : ℝ) ≤ (1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by norm_num
  have hthr : 64 * frobSupBond (trivialU witL5) ^ 2
      ≤ (1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by
    rw [hα]; norm_num
  have hsmall : 0 ≤ Real.sqrt ((1 / 108 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 4)
        - 64 * frobSupBond (trivialU witL5) ^ 2)
      - 4 * Real.sqrt 2 * frobSupBond (trivialU witL5) := by
    rw [hα]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero]
    positivity
  have key := deltaJ_regularU_coercive_on_kerQU witL5_four_le witL5_two_dvd (trivialU witL5)
    witA witA_axial witA_mem_kerQ1 hthr hsmall
  rw [hα] at key
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero] at key
  rwa [Real.sq_sqrt hγ0] at key

#print axioms frobSupBond_trivialU
#print axioms bondEnergy_witA_pos
#print axioms deltaJ_coercive_at_witA

/-! ## §6b — FALSIFIABILITY CONTROLS: both mechanisms are LOAD-BEARING, neither passes degenerately

The single most dangerous way `witA_mem_kerQ1` could be worthless is the **degenerate test point**
(MEMORY class 5): if NO coarse block-segment sum ever reads the two bonds in `witA`'s support, then
`witA_mem_kerQ1` holds for a reason that has nothing to do with the ± cancellation, and the same
proof would certify any field supported there — including one that is not really in the kernel of
the intended operator. §6b rules that out by MAKING THE CHECK FAIL on a controlled mutation.

* **Control A (drop the `−` bond).** `witASingle` is `witA` with the cancelling partner deleted. It
  still satisfies the axial gauge (`witASingle_axial` — same §1 mechanism), but it is NOT in
  `ker Q₁(1)`: at the coarse bond based at `(4,4,4)` in direction `0` it evaluates to
  `(1/8)·suTwoWitness ≠ 0` (`witASingle_value`, an exact value, not just `≠ 0`). So the coarse sums
  DO read `bPlus`, with multiplicity exactly `2` (`= 16 · 1/8`), and the `−w` bond is doing real
  work. `witA_mem_kerQ1` is not vacuous.
* **Control B (move the support off the top coordinate).** `witALow` is the direction-`0` indicator
  at the ORIGIN. It FAILS the axial gauge (`witALow_not_axial`), because the direction-`0` bond at
  the origin genuinely lies on `Γ_{(0,0,0),(1,0,0)}` (`dir0_bond_on_staircase`). So the axial gauge
  is a real constraint on direction-`0` bonds and `witA_axial` is not passing because the staircase
  set is empty — the TOP-coordinate placement of `witA`'s support is load-bearing.

Together: `witASingle` passes gauge/fails kernel, `witALow` fails gauge, `witA` passes both. Each
hypothesis of the target theorem is separately falsifiable at this witness. -/

theorem cCenter_coarse : cCenter ∈ CoarseLattice witL5 2 := by
  rw [mem_CoarseLattice]; decide

/-- The coarse bond based at `(4,4,4)` in direction `0` — the one that reads both witness bonds. -/
def cBond : CoarseBond witL5 2 := (⟨cCenter, cCenter_coarse⟩, 0)

/-- **CONTROL A**: `witA` with the cancelling `−` bond DELETED. -/
noncomputable def witASingle : Bond witL5 → SuTwo :=
  fun e => (if e = bPlus then (1 : ℝ) else 0) • suTwoWitness

/-- Control A still satisfies the axial gauge — so the gauge is NOT what separates it from
`witA`. -/
theorem witASingle_axial : ∀ y : PeriodicLatticeSite witL5, y ∈ CoarseLattice witL5 2 →
    ∀ x : PeriodicLatticeSite witL5, x ∈ blockOf y 2 →
      ∀ b ∈ staircasePath y x, witASingle b = 0 := by
  intro y _hy x hx b hb
  have h1 : b ≠ bPlus := by
    rintro rfl
    exact dir0_top_not_mem_staircase (ell := 2) sPlus (by decide) hx hb
  rw [witASingle, if_neg h1, zero_smul]

/-- **CONTROL A, the exact value**: dropping the `−` bond leaves a NONZERO coarse value
`(1/8)·suTwoWitness` at `cBond`. The `1/8 = 2/2⁴` records that the coarse sum reads `bPlus` with
multiplicity exactly `2` (once at `i = 0` from `sPlus`, once at `i = 1` from `tPlus`) — the
quantitative proof that the block-segment sum is not blind to this bond. -/
theorem witASingle_value :
    lineCoarseRestrictCov (trivialU witL5) 2 witASingle cBond = (1 / 8 : ℝ) • suTwoWitness := by
  rw [lineCoarseRestrictCov_trivialU]
  unfold lineCoarseRestrictSuTwo
  have hchi : ∀ (x : PeriodicLatticeSite witL5) (i : ℕ),
      witASingle (pathSite x cBond.2 i, cBond.2)
        = (if (pathSite x cBond.2 i, cBond.2) = bPlus then (1 : ℝ) else 0) • suTwoWitness :=
    fun _ _ => rfl
  simp only [hchi, ← Finset.sum_smul]
  have hsum : (∑ x ∈ blockOf cBond.1.1 2, ∑ i ∈ Finset.range 2,
      (if (pathSite x cBond.2 i, cBond.2) = bPlus then (1 : ℝ) else 0)) = 2 := by
    -- `cBond.1.1` is `cCenter` and `cBond.2` is `0` by definition of `cBond`.
    change (∑ x ∈ blockOf cCenter 2, ∑ i ∈ Finset.range 2,
      (if (pathSite x (0 : Fin 3) i, (0 : Fin 3)) = bPlus then (1 : ℝ) else 0)) = 2
    -- `blockSegSum_split` is applied with `f` given EXPLICITLY: the summand
    -- `if (pathSite x 0 i, 0) = bPlus …` is not a higher-order pattern, so unification
    -- cannot recover `f` on its own.
    have hsplit : (∑ x ∈ blockOf cCenter 2, ∑ i ∈ Finset.range 2,
          (if (pathSite x (0 : Fin 3) i, (0 : Fin 3)) = bPlus then (1 : ℝ) else 0))
        = (∑ x ∈ blockOf cCenter 2,
            (if ((x : PeriodicLatticeSite witL5), (0 : Fin 3)) = bPlus then (1 : ℝ) else 0))
          + (∑ x ∈ blockOf cCenter 2,
              (if (periodicLatticeShift x (0 : Fin 3), (0 : Fin 3)) = bPlus then (1 : ℝ) else 0)) :=
      blockSegSum_split cCenter 0 (fun e => if e = bPlus then (1 : ℝ) else 0)
    rw [hsplit]
    have h1 : ∀ x : PeriodicLatticeSite witL5, ((x, (0 : Fin 3)) = bPlus) ↔ (x = sPlus) := by
      intro x
      rw [bPlus, Prod.mk.injEq]
      exact and_iff_left rfl
    have h2 : ∀ x : PeriodicLatticeSite witL5,
        ((periodicLatticeShift x (0 : Fin 3), (0 : Fin 3)) = bPlus) ↔ (x = tPlus) := by
      intro x
      rw [bPlus, Prod.mk.injEq]
      constructor
      · rintro ⟨h, -⟩
        exact (shift_eq_iff_shiftBack x sPlus 0).mp h
      · intro h
        exact ⟨(shift_eq_iff_shiftBack x sPlus 0).mpr h, rfl⟩
    -- each half is rewritten SEPARATELY: a single `simp only` lets simp's own `Prod`/`sum_boole`
    -- lemmas pre-empt `h2` and collapse the second sum to a `Finset.card` before it can fire.
    have hs1 : (∑ x ∈ blockOf cCenter 2,
        (if ((x : PeriodicLatticeSite witL5), (0 : Fin 3)) = bPlus then (1 : ℝ) else 0)) = 1 := by
      have hr : ∀ x : PeriodicLatticeSite witL5,
          (if ((x : PeriodicLatticeSite witL5), (0 : Fin 3)) = bPlus then (1 : ℝ) else 0)
            = (if x = sPlus then (1 : ℝ) else 0) := fun x => if_congr (h1 x) rfl rfl
      simp only [hr, Finset.sum_ite_eq']
      rw [if_pos]
      exact (mem_blockOf_iff_center sPlus_coords cCenter_coarse).mpr rfl
    have hs2 : (∑ x ∈ blockOf cCenter 2,
        (if (periodicLatticeShift x (0 : Fin 3), (0 : Fin 3)) = bPlus then (1 : ℝ) else 0))
          = 1 := by
      have hr : ∀ x : PeriodicLatticeSite witL5,
          (if (periodicLatticeShift x (0 : Fin 3), (0 : Fin 3)) = bPlus then (1 : ℝ) else 0)
            = (if x = tPlus then (1 : ℝ) else 0) := fun x => if_congr (h2 x) rfl rfl
      simp only [hr, Finset.sum_ite_eq']
      rw [if_pos]
      exact (mem_blockOf_iff_center tPlus_coords cCenter_coarse).mpr rfl
    rw [hs1, hs2]
    norm_num
  rw [hsum, smul_smul]
  congr 1
  norm_num

/-- **CONTROL A fires**: with the `−` bond removed, `ker Q₁(1)` membership FAILS. -/
theorem witASingle_not_mem_kerQ1 :
    lineCoarseRestrictCov (trivialU witL5) 2 witASingle cBond ≠ 0 := by
  rw [witASingle_value]
  intro h
  rcases smul_eq_zero.mp h with h' | h'
  · norm_num at h'
  · exact suTwoWitness_ne_zero h'

/-- Origin of the witness lattice, a `Λ'` member. -/
def yZero : PeriodicLatticeSite witL5 := fun _ => 0

/-- `(1,0,0)` — a point of `B((0,0,0))` whose staircase to the origin is a single direction-`0`
bond. -/
def xOne : PeriodicLatticeSite witL5 := fun ν => if ν = 0 then 1 else 0

theorem yZero_coarse : yZero ∈ CoarseLattice witL5 2 := by
  rw [mem_CoarseLattice]; decide

theorem xOne_mem_block : xOne ∈ blockOf yZero 2 := by
  rw [mem_blockOf]; decide

/-- **The axial gauge really does constrain direction-`0` bonds** — the direction-`0` bond at the
origin lies ON `Γ_{(0,0,0),(1,0,0)}`. Without this, `witA_axial` could be passing merely because no
direction-`0` bond is ever constrained. -/
theorem dir0_bond_on_staircase :
    ((yZero, (0 : Fin 3)) : Bond witL5) ∈ staircasePath yZero xOne := by
  rw [staircasePath]
  refine Finset.mem_union_right _ ?_
  rw [mem_axisSegment]
  decide

/-- **CONTROL B**: the direction-`0` indicator at the ORIGIN (support off the top coordinate). -/
noncomputable def witALow : Bond witL5 → SuTwo :=
  fun e => (if e = ((yZero, (0 : Fin 3)) : Bond witL5) then (1 : ℝ) else 0) • suTwoWitness

/-- **CONTROL B fires**: moving the support off the top coordinate BREAKS the axial gauge. -/
theorem witALow_not_axial :
    ¬ (∀ y : PeriodicLatticeSite witL5, y ∈ CoarseLattice witL5 2 →
        ∀ x : PeriodicLatticeSite witL5, x ∈ blockOf y 2 →
          ∀ b ∈ staircasePath y x, witALow b = 0) := by
  intro h
  have hv := h yZero yZero_coarse xOne xOne_mem_block ((yZero, (0 : Fin 3)) : Bond witL5)
    dir0_bond_on_staircase
  rw [witALow, if_pos rfl, one_smul] at hv
  exact suTwoWitness_ne_zero hv

#print axioms witASingle_axial
#print axioms witASingle_value
#print axioms witASingle_not_mem_kerQ1
#print axioms dir0_bond_on_staircase
#print axioms witALow_not_axial

/-! ## §7 — `[REGU-DOMAIN-NONVAC-GENERALU]`: evidence of resistance (OPS-1), NOT a bare label

The residual closed above is the one the prosecutor named: the theorem's domain is non-empty, so the
theorem is not vacuous. The strictly stronger question — *is the domain nonzero for EVERY fixed `U`
satisfying `hthr`/`hsmall`?* — was attempted in this pass and is NOT closed. What was tried and
exactly where it breaks:

1. **Transport the `U = 1` witness.** The axial-gauge half transports verbatim: §1 is
   `U`-independent, so `witA` satisfies `hadm` for every `U`. The `ker Q₁(U)` half does NOT:
   `lineCoarseRestrictCov U 2 witA b = (1/2⁴) • Σ_x (rZeroA U … )`, and at `U ≠ 1` the two
   contributions `+w` and `−w` are transported by DIFFERENT holonomies
   (`R(V₀(Γ_{c₋,x} ∪ [x,b₋]))` depends on `x`, `Q1Real.rZeroA`), so `Ad(g₁)w − Ad(g₂)w ≠ 0` in
   general. The cancellation is a `U = 1` phenomenon, not a geometric one. **This is exactly the
   defect that killed the two candidate witnesses the prosecutor examined**, and it kills the naive
   transport too.
2. **Dimension counting instead of an explicit witness.** `ker Q₁(U)` is the kernel of the linear
   map `lineCoarseRestrictCovLM U 2` from `Bond witL5 → SuTwo` (real dimension `3 · 3 · 6³ = 1944`)
   to `CoarseBond witL5 2 → SuTwo` (real dimension `3 · 3 · 3³ = 243`), so `dim ker ≥ 1701` for
   `U`; the axial gauge imposes `3` linear conditions per bond of `⋃_{y,x} Γ_{y,x}`, so it would
   suffice that `|⋃_{y,x} Γ_{y,x}| < 567`. **Where it breaks:** this needs the EXACT cardinality of
   the staircase union (a `Finset.card` over `27 × 8` heavily overlapping pairs), plus
   `Submodule.finrank` machinery — `finrank (Bond → SuTwo)`, `finrank_le_of_surjective`-style rank
   bounds, and a `finrank` lower bound for an intersection — none of which exists in this tree for
   these carriers. It is a genuine multi-lemma build with a combinatorial cardinality computation at
   its head, not a corollary of anything present. It is also strictly weaker than what the campaign
   ultimately wants (an explicit `C`-image witness), which is why it was not pursued past scoping.
3. **A `U`-independent zero-set argument.** If some bond family is read by NO coarse segment, the
   `ker Q₁(U)` condition on it is vacuous for every `U`. **Where it breaks:** on the compatible
   torus (`2 ∣ L μ + 1`) the blocks TILE, so every fine bond `(z, μ)` is read at `i = 0` by the
   coarse bond based at the unique block owning `z`. The "unread bond" route is provably empty
   here — it can only exist on an INCOMPATIBLE extent, which the target theorem's `hdvd` forbids.

So the general-`U` non-vacuity reduces to a named, precise missing primitive: **a rank/dimension
bound for `lineCoarseRestrictCovLM U 2` restricted to the axial-gauge subspace, uniform in `U`** —
equivalently, the surjectivity (or corank bound) of `Q₁(U)` on the `(2.121)` subspace. That is the
`C`-reparametrization content (`reparamCSuTwo`: `C B̃ ∈ ker Q₁(U)` by construction) the module
docstring of `RegularUCoercivityFull` already points at, and it is a separate build. -/

end AdalyFormal.Balaban.RegularUDomainWitness
