/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.ReparamCSuTwo

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `ReparamCDisjoint` — GAP 2 of `compute/cstar_roadmap/ROADMAP.md`: the coarse-bond constraints
DECOUPLE, but only for the CORRECTED dropped bond

**The question** (`ROADMAP.md` §GAP 2): `ReparamCSuTwo.reparamCSuTwo` solves the single constraint
`(Q₁(U)(C B̃))(c₀) = 0` by adjusting one dropped fine bond. The target `ker Q₁(U)` needs the
constraint at EVERY coarse bond. Does the constraint functional `L_c(B) := (Q₁(U)B)(c)` read
another coarse bond's dropped bond? If not, the full `C` is a commuting composition of the
single-constraint maps (mechanical); if so, it is a genuine simultaneous linear solve.

## The read-set

`LineIntegralCovariant.lineCoarseRestrictCov U ell B c` is
`(1/ell⁴) • Σ_{x ∈ blockOf c.1.1 ell} Q1Real.rZeroA U c.1.1 x B c.2 ell`, and `rZeroA` is
`Σ_{i ∈ range ell} RMap(transport) (B (pathSite x c.2 i, c.2))`. So `L_c` reads exactly the bonds

    ReadsBond ell c b  ↔  ∃ x ∈ blockOf c.1.1 ell, ∃ i < ell, (pathSite x c.2 i, c.2) = b

(§1), and `lineCoarseRestrictCov_congr` (§2) is the operational form: `L_c` depends on `B` ONLY
through its restriction to that set.

Relative to `y = c.1.1`, a read bond's base site has transverse offsets in `[0, ell)` and
`c.2`-offset `j + i ∈ [0, 2ell-2]` with `j, i ∈ [0, ell)`. **The segment overhang is real**: for
`ell ≥ 2` the value `ell` lies in `[0, 2ell-2]`, so the read-set reaches the NEXT coarse site
`y + ell·e_μ` — the base site of the neighbouring block.

## The verdict, in two theorems

* `droppedBondLast_not_reads` (§4) — with the dropped bond taken to be the **last** fine bond of the
  long bond `c` whose base lies in `B(c)`,

      droppedBondLast ell c := (pathSite c.1.1 c.2 (ell - 1), c.2)

  the constraints **DECOUPLE**: `c ≠ c' → ¬ ReadsBond ell c (droppedBondLast ell c')`, for every
  extent `L` with `0 < ell` and `∀ μ, ell ∣ L μ + 1`. `constraint_indep_of_other_droppedBond` (§5)
  is the operational corollary: changing `B` at another coarse bond's dropped bond does not move
  `L_c` at all.
* `droppedBond_couples_witness` (§6) — with `ReparamCSuTwo.droppedBond ell c = (c.1.1, c.2)`, the
  bond at the coarse site itself (`c.2`-offset `0`, which the previous coarse bond's overhang
  reaches, since `ell ≤ 2ell - 2` for `ell ≥ 2`), the constraints **COUPLE**: an explicit pair
  `cA ≠ cB` on `witnessL` with `ReadsBond witnessEll cA (droppedBond witnessEll cB)`.

§6 is not decoration: it is the **mutation proof** that §4 is non-vacuous and that the offset
`ell - 1` is load-bearing. Replacing `ell - 1` by `0` in `droppedBondLast` makes §4 FALSE, and §6 is
the counterexample, kernel-checked, in this file. Together with `droppedBondLast_reads_self` (§3 —
`L_c` DOES read its own dropped bond, so the constraint is not vacuous either) these bracket the
statement from both sides.

## Consequence for the assembly (stated, not built here)

With `droppedBondLast`, the full reparametrization is the composition over coarse bonds of the
per-`c` single-constraint maps, and §5 says the composition order is irrelevant and each step
preserves the previously-solved constraints. The remaining per-`c` ingredient is the invertibility
of the diagonal coefficient; at `ell = 2` the two contributing terms are `(x,i) = (y, 1)` and
`(y + e_μ, 0)` (`readers_ell2`, §5d — these are the ONLY two), both with transport holonomy
`U_μ(y)` (`transport_terms_eq`, §5d), giving `2 • RMap (U_μ(y))` — invertible with no numerical
computation.

~~That last identification is NOT proved here (it needs `GammaPath y (y + e_μ) = [(μ,true)]`);
see `compute/cstar_roadmap/GAP2_DECOUPLING.md` residual R2.~~ **SUPERSEDED in the same pass**: §5d
now proves `gammaPath_shift` and both statements above. What is still NOT built here is the
purely definitional step of extracting "the coefficient of `B(b₀)`" from `rZeroA`'s sum as a
`LinearMap` and inverting it — that is `ReparamCSuTwo`'s `coeffDc` plumbing, retargeted; no
mathematical content remains in it. **`gammaPath_shift` carries the side condition `0 < L μ`**,
which `0 < ell` alone does NOT supply (it follows from `ell ∣ L μ + 1` with `ell ≥ 2`).

**Scope.** Nothing here changes `ReparamCSuTwo.droppedBond`; retargeting it (and everything
downstream, including the scope line of `ReparamCJoint.witnessMain_joint_kernel_nonzero`, whose
`∀ U` singularity is a property of the OLD choice, not of `Q₁`) is residual R4 of the same file.
-/

namespace AdalyFormal.Balaban.ReparamCDisjoint

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice
  mem_CoarseLattice unique_multiple_in_window witnessL witnessEll witnessY witnessY_coarse)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.Q1Real (nsmul_one_val rZeroA)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.ReparamCSuTwo (droppedBond)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — the closed form of `pathSite` (proved, not assumed) -/

/-- `pathSite x μ i` moves only coordinate `μ`, by `i` forward steps. `QOne.pathSite` is defined as
a `Nat.iterate` of `periodicLatticeShift`; this is the closed form as a THEOREM. -/
theorem pathSite_eq (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    pathSite x μ i = Function.update x μ (x μ + i • (1 : Fin (L μ + 1))) := by
  induction i with
  | zero => simp [pathSite_zero]
  | succ i ih =>
      rw [pathSite_succ, ih]
      simp only [periodicLatticeShift, Function.update_self, Function.update_idem]
      congr 1
      rw [succ_nsmul, ← add_assoc]

/-- Transverse coordinates are untouched. -/
theorem pathSite_apply_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (i : ℕ) (h : ν ≠ μ) :
    pathSite x μ i ν = x ν := by
  rw [pathSite_eq]; exact Function.update_of_ne h _ _

/-- The moved coordinate, as a `Nat` value: forward by `i`, modulo the periodic extent. -/
theorem pathSite_apply_self_val (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    ((pathSite x μ i) μ).val = ((x μ).val + i) % (L μ + 1) := by
  rw [pathSite_eq, Function.update_self, Fin.val_add, nsmul_one_val]
  exact Nat.ModEq.add_left _ (Nat.mod_modEq i (L μ + 1))

#print axioms pathSite_eq
#print axioms pathSite_apply_ne
#print axioms pathSite_apply_self_val

/-! ## §1 — the read-set of the constraint functional `L_c` -/

/-- **`b` is READ by the constraint at coarse bond `c`** — `b` occurs as an argument of `B` in the
double sum defining `lineCoarseRestrictCov U ell B c`. Transcribed from that definition's own
index sets (`blockOf c.1.1 ell` for `x`, `Finset.range ell` for `i`) and its own argument
`(pathSite x c.2 i, c.2)`; §2 proves the transcription is faithful. -/
def ReadsBond (ell : ℕ) (c : CoarseBond L ell) (b : Bond L) : Prop :=
  ∃ x ∈ blockOf c.1.1 ell, ∃ i ∈ Finset.range ell, (pathSite x c.2 i, c.2) = b

/-! ## §2 — LOCALITY: `L_c` depends on `B` only through the read-set -/

/-- **The faithfulness of §1**: two bond fields agreeing on everything `c` reads give the same
value of the constraint functional. This is what makes "does not read" operational. -/
theorem lineCoarseRestrictCov_congr
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (B₁ B₂ : Bond L → SuTwo) (c : CoarseBond L ell)
    (h : ∀ b, ReadsBond ell c b → B₁ b = B₂ b) :
    lineCoarseRestrictCov U ell B₁ c = lineCoarseRestrictCov U ell B₂ c := by
  simp only [lineCoarseRestrictCov]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  simp only [rZeroA]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h _ ⟨x, hx, i, hi, rfl⟩]

#print axioms lineCoarseRestrictCov_congr

/-! ## §3 — the CORRECTED dropped bond, and the fact that its own constraint reads it -/

/-- **The corrected dropped bond**: the LAST fine bond of the long bond `c` whose base site still
lies in `B(c)` — `c.2`-offset `ell - 1` from the coarse site, rather than `ReparamCSuTwo`'s offset
`0`. -/
def droppedBondLast (ell : ℕ) (c : CoarseBond L ell) : Bond L :=
  (pathSite c.1.1 c.2 (ell - 1), c.2)

/-- Non-vacuity from below: `L_c` DOES read its own dropped bond (so the single constraint can
determine it). Take `x = c.1.1`, `i = ell - 1`. -/
theorem droppedBondLast_reads_self {ell : ℕ} (hell : 0 < ell) (c : CoarseBond L ell) :
    ReadsBond ell c (droppedBondLast ell c) :=
  ⟨c.1.1, by rw [mem_blockOf]; intro ν; omega, ell - 1, Finset.mem_range.mpr (by omega), rfl⟩

#print axioms droppedBondLast_reads_self

/-! ## §4 — THE DISJOINTNESS THEOREM: distinct coarse bonds do not read each other's dropped bond -/

/-- Auxiliary: a `CoarseLattice` coordinate plus a full block fits inside the periodic extent.
Uses only `ell ∣ L μ + 1` and `ell ∣ t`. -/
theorem coarse_coord_add_ell_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (μ : Fin 3)
    (t : ℕ) (ht : t % ell = 0) (htn : t < L μ + 1) : t + ell ≤ L μ + 1 := by
  obtain ⟨p, hp⟩ := Nat.dvd_of_mod_eq_zero ht
  obtain ⟨q, hq⟩ := hdvd μ
  rw [hq, hp] at htn ⊢
  have hpq : p < q := lt_of_mul_lt_mul_left htn (Nat.zero_le ell)
  calc ell * p + ell = ell * (p + 1) := by ring
    _ ≤ ell * q := Nat.mul_le_mul_left ell hpq

/-- **GAP 2, DECIDED: the constraints DECOUPLE at the corrected dropped bond.**

For `0 < ell` and an extent tiled by blocks (`∀ μ, ell ∣ L μ + 1`), the constraint functional at a
coarse bond `c` never reads the dropped bond of a DIFFERENT coarse bond `c'`.

Proof: a read bond of `c` has direction `c.2` and base site with transverse offsets in `[0, ell)`
and `c.2`-offset `j + i ∈ [0, 2ell-2]` from `c.1.1`; `droppedBondLast ell c'` has direction `c'.2`
and base site at offset exactly `ell - 1` from the coarse site `c'.1.1`. Matching forces
`c.2 = c'.2` and then, coordinate by coordinate, `c'.1.1 = c.1.1` — the transverse coordinates by
`unique_multiple_in_window` (only one multiple of `ell` per window of length `ell`), and the
`c.2`-coordinate because `b + ell - 1 = u + i` with `a ≤ u < a + ell` and `i < ell` sandwiches
`b` strictly within `ell` of `a`, while the periodic-wraparound branch `u + i = b + ell - 1 + n` is
arithmetically impossible (it would need `n ≤ n - 1`). -/
theorem droppedBondLast_not_reads {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (c c' : CoarseBond L ell) (hne : c ≠ c') :
    ¬ ReadsBond ell c (droppedBondLast ell c') := by
  rintro ⟨x, hx, i, hi, heq⟩
  rw [Finset.mem_range] at hi
  rw [mem_blockOf] at hx
  have hy : ∀ ν : Fin 3, (c.1.1 ν).val % ell = 0 := mem_CoarseLattice.mp c.1.2
  have hy' : ∀ ν : Fin 3, (c'.1.1 ν).val % ell = 0 := mem_CoarseLattice.mp c'.1.2
  -- split the bond equality
  simp only [droppedBondLast, Prod.mk.injEq] at heq
  obtain ⟨hsite, hdir⟩ := heq
  rw [← hdir] at hsite
  set μ : Fin 3 := c.2 with hμ
  -- transverse coordinates
  have htrans : ∀ ν : Fin 3, ν ≠ μ → (c.1.1 ν).val = (c'.1.1 ν).val := by
    intro ν hν
    have hxy : x ν = c'.1.1 ν := by
      have h1 := congrFun hsite ν
      rwa [pathSite_apply_ne _ _ _ _ hν, pathSite_apply_ne _ _ _ _ hν] at h1
    have hxyv : (x ν).val = (c'.1.1 ν).val := congrArg Fin.val hxy
    exact unique_multiple_in_window ell (x ν).val (c.1.1 ν).val (c'.1.1 ν).val (hy ν) (hy' ν)
      (hx ν).1 (hx ν).2 (le_of_eq hxyv.symm) (by omega)
  -- the moved coordinate
  have hval : ((x μ).val + i) % (L μ + 1) = ((c'.1.1 μ).val + (ell - 1)) % (L μ + 1) := by
    have h1 := congrArg (fun z : PeriodicLatticeSite L => (z μ).val) hsite
    rwa [pathSite_apply_self_val, pathSite_apply_self_val] at h1
  have hA : (c.1.1 μ).val + ell ≤ L μ + 1 :=
    coarse_coord_add_ell_le hdvd μ _ (hy μ) (c.1.1 μ).isLt
  have hB : (c'.1.1 μ).val + ell ≤ L μ + 1 :=
    coarse_coord_add_ell_le hdvd μ _ (hy' μ) (c'.1.1 μ).isLt
  have hxlt : (x μ).val < L μ + 1 := (x μ).isLt
  have hxlo : (c.1.1 μ).val ≤ (x μ).val := (hx μ).1
  have hxhi : (x μ).val < (c.1.1 μ).val + ell := (hx μ).2
  -- the right-hand side needs no reduction: `b + (ell-1) < L μ + 1`
  rw [Nat.mod_eq_of_lt (show (c'.1.1 μ).val + (ell - 1) < L μ + 1 by omega)] at hval
  have hmain : (c.1.1 μ).val = (c'.1.1 μ).val := by
    rcases lt_or_ge ((x μ).val + i) (L μ + 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hval
      rcases le_total (c.1.1 μ).val (c'.1.1 μ).val with hle | hle
      · exact unique_multiple_in_window ell (c'.1.1 μ).val (c.1.1 μ).val (c'.1.1 μ).val
          (hy μ) (hy' μ) hle (by omega) (le_refl _) (by omega)
      · exact unique_multiple_in_window ell (c.1.1 μ).val (c.1.1 μ).val (c'.1.1 μ).val
          (hy μ) (hy' μ) (le_refl _) (by omega) hle (by omega)
    · exfalso
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt (show (x μ).val + i - (L μ + 1) < L μ + 1 by omega)] at hval
      omega
  -- assemble: the coarse sites agree, the directions agree, so `c = c'`
  refine hne (Prod.ext_iff.mpr ⟨Subtype.ext ?_, hdir⟩)
  funext ν
  apply Fin.ext
  rcases eq_or_ne ν μ with rfl | hν
  · exact hmain
  · exact htrans ν hν

#print axioms coarse_coord_add_ell_le
#print axioms droppedBondLast_not_reads

/-! ## §5 — the operational corollary: adjusting another dropped bond does not move `L_c` -/

/-- **Decoupling, in the form the assembly needs.** Overwriting `B` at the dropped bond of a
DIFFERENT coarse bond `c'` leaves the constraint at `c` numerically unchanged. Hence the per-`c`
single-constraint solves commute and compose into a full `C` without a simultaneous linear solve. -/
theorem constraint_indep_of_other_droppedBond {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c c' : CoarseBond L ell) (hne : c ≠ c') (B : Bond L → SuTwo) (v : SuTwo) :
    lineCoarseRestrictCov U ell (Function.update B (droppedBondLast ell c') v) c
      = lineCoarseRestrictCov U ell B c := by
  refine lineCoarseRestrictCov_congr U ell _ _ c ?_
  intro b hb
  have hbne : b ≠ droppedBondLast ell c' := by
    rintro rfl
    exact droppedBondLast_not_reads hell hdvd c c' hne hb
  exact Function.update_of_ne hbne _ _

#print axioms constraint_indep_of_other_droppedBond

/-! ## §5b — GAP 1's `hb₀`: the corrected dropped bond lies on NO axial staircase

`ROADMAP.md` §GAP 1 flags `hb₀` ("is the dropped bond off the staircases?") as unchecked. For
`ReparamCSuTwo.droppedBond` the answer is NO — `(y, μ)` is the whole of `staircasePath y (y + e_μ)`
when `y + e_μ ∈ blockOf y ell`, so the old dropped bond is already forced to `0` by the axial gauge
and is not a free variable at all. For `droppedBondLast` the answer is YES, proved here, for EVERY
coarse centre `y'` and every `x ∈ blockOf y' ell` — so the axial gauge and the `Q₁` elimination
touch disjoint variables, which is what (3.157)'s `Λ̃ = Λ \ (⋃Ax(y) ∪ ⋃ B(c)∩c)` presupposes. -/

/-- Reusable (checked by grep first, LAW-19: no such lemma existed): every bond of an
`axisSegment` occurring in a staircase has its BASE SITE inside the block, provided the segment's
own base site does. -/
theorem axisSegment_base_mem_block {ell : ℕ} {y x base : PeriodicLatticeSite L} {d : Fin 3}
    (hx : ∀ ν : Fin 3, (y ν).val ≤ (x ν).val ∧ (x ν).val < (y ν).val + ell)
    (hbase : ∀ ν : Fin 3, (y ν).val ≤ (base ν).val ∧ (base ν).val < (y ν).val + ell)
    {e : Bond L}
    (he : e ∈ AdmissibleSubspace.axisSegment base d
            (min (y d).val (x d).val) (max (y d).val (x d).val)) :
    ∀ ν : Fin 3, (y ν).val ≤ (e.1 ν).val ∧ (e.1 ν).val < (y ν).val + ell := by
  obtain ⟨_, htr, hlo, hhi⟩ := AdmissibleSubspace.mem_axisSegment.mp he
  intro ν
  rcases eq_or_ne ν d with rfl | hν
  · have := hx ν; omega
  · rw [htr ν hν]; exact hbase ν

/-- Reusable: the base site of every bond of `staircasePath y x` lies in `blockOf y ell`
(the staircase never leaves the block it is drawn in). -/
theorem staircasePath_base_mem_block {ell : ℕ} {y x : PeriodicLatticeSite L}
    (hx : x ∈ blockOf y ell) {e : Bond L}
    (he : e ∈ AdmissibleSubspace.staircasePath y x) : e.1 ∈ blockOf y ell := by
  rw [mem_blockOf] at hx ⊢
  simp only [AdmissibleSubspace.staircasePath, Finset.mem_union] at he
  rcases he with (h2 | h1) | h0
  · exact axisSegment_base_mem_block hx (fun ν => by have := hx ν; omega) h2
  · refine axisSegment_base_mem_block hx (fun ν => ?_) h1
    rcases eq_or_ne ν 2 with rfl | h
    · simpa only [AdmissibleSubspace.corner1, Function.update_self] using hx 2
    · simp only [AdmissibleSubspace.corner1, Function.update_of_ne h]
      have := hx ν; omega
  · refine axisSegment_base_mem_block hx (fun ν => ?_) h0
    rcases eq_or_ne ν 1 with rfl | h1'
    · simpa only [AdmissibleSubspace.corner2, Function.update_self] using hx 1
    · simp only [AdmissibleSubspace.corner2, Function.update_of_ne h1']
      rcases eq_or_ne ν 2 with rfl | h2'
      · simpa only [AdmissibleSubspace.corner1, Function.update_self] using hx 2
      · simp only [AdmissibleSubspace.corner1, Function.update_of_ne h2']
        have := hx ν; omega

/-- The corrected dropped bond's base site lies in its OWN block (and, by tiling, in no other). -/
theorem droppedBondLast_base_mem_block {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (c : CoarseBond L ell) :
    (droppedBondLast ell c).1 ∈ blockOf c.1.1 ell := by
  have hfit : (c.1.1 c.2).val + ell ≤ L c.2 + 1 :=
    coarse_coord_add_ell_le hdvd c.2 _ (mem_CoarseLattice.mp c.1.2 c.2) (c.1.1 c.2).isLt
  rw [mem_blockOf]
  intro ν
  rcases eq_or_ne ν c.2 with rfl | hν
  · simp only [droppedBondLast]
    rw [pathSite_apply_self_val, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [droppedBondLast]
    rw [pathSite_apply_ne _ _ _ _ hν]
    omega

/-- **GAP 1's `hb₀`, CLOSED for the corrected dropped bond.** For every coarse centre `y'` and every
`x ∈ blockOf y' ell`, `droppedBondLast ell c` is not on the axial staircase `Γ_{y',x}`.

Two cases. If `y' ≠ c.1.1`: the bond's base lies in `blockOf c.1.1 ell`
(`droppedBondLast_base_mem_block`) while every staircase bond's base lies in `blockOf y' ell`
(`staircasePath_base_mem_block`), and blocks of distinct coarse centres are disjoint
(`AdmissibleSubspace.coarseLattice_unique`). If `y' = c.1.1`: the staircase's direction-`c.2`
segment stops strictly below `(x c.2).val ≤ (c.1.1 c.2).val + ell - 1`, which is exactly the bond's
own `c.2`-coordinate — the bond is the one step that leaves the block. -/
theorem droppedBondLast_not_mem_staircase {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (c : CoarseBond L ell)
    (y' : PeriodicLatticeSite L) (hy' : y' ∈ CoarseLattice L ell)
    (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y' ell) :
    droppedBondLast ell c ∉ AdmissibleSubspace.staircasePath y' x := by
  intro he
  have hfit : (c.1.1 c.2).val + ell ≤ L c.2 + 1 :=
    coarse_coord_add_ell_le hdvd c.2 _ (mem_CoarseLattice.mp c.1.2 c.2) (c.1.1 c.2).isLt
  have hbase : ((droppedBondLast ell c).1 c.2).val = (c.1.1 c.2).val + (ell - 1) := by
    simp only [droppedBondLast]
    rw [pathSite_apply_self_val]
    exact Nat.mod_eq_of_lt (by omega)
  -- the two blocks coincide, by tiling
  have hsame : c.1.1 = y' :=
    AdmissibleSubspace.coarseLattice_unique ell c.1.2 hy'
      (droppedBondLast_base_mem_block hell hdvd c) (staircasePath_base_mem_block hx he)
  subst hsame
  rw [mem_blockOf] at hx
  -- direction-`c.2` segment: the bond's `c.2`-coordinate is at or past the segment's top
  have key : ∀ (d : Fin 3) (base : PeriodicLatticeSite L),
      droppedBondLast ell c ∈ AdmissibleSubspace.axisSegment base d
        (min (c.1.1 d).val (x d).val) (max (c.1.1 d).val (x d).val) → False := by
    intro d base hmem
    obtain ⟨hd, _, _, hhi⟩ := AdmissibleSubspace.mem_axisSegment.mp hmem
    have hd' : c.2 = d := hd
    subst hd'
    have h1 := (hx c.2).1
    have h2 := (hx c.2).2
    rw [hbase] at hhi
    omega
  simp only [AdmissibleSubspace.staircasePath, Finset.mem_union] at he
  rcases he with (h2 | h1) | h0
  · exact key 2 _ h2
  · exact key 1 _ h1
  · exact key 0 _ h0

#print axioms axisSegment_base_mem_block
#print axioms staircasePath_base_mem_block
#print axioms droppedBondLast_base_mem_block
#print axioms droppedBondLast_not_mem_staircase

/-! ## §5d — the two transport factors reaching the corrected dropped bond at `ell = 2` coincide

At `ell = 2` exactly two `(x,i)` pairs of `lineCoarseRestrictCov`'s double sum land on
`droppedBondLast 2 c = (y + e_μ, μ)` — namely `(y, 1)` and `(y + e_μ, 0)` (`readers_ell2` below).
This section proves their two transport holonomies are the SAME group element `U_μ(y)`, so the
diagonal coefficient of the single-`c` constraint is `2 • RMap (U_μ(y))` — invertible, with no
numerical `coeffDc` computation. -/

/-- No forward `μ`-step in a direction with more than one site: `coordSteps y (y+e_μ) μ = 1`.
**The `0 < L μ` hypothesis is load-bearing**: on a one-site direction `(1 : Fin 1).val = 0` and the
contour degenerates to `[]`. -/
theorem coordSteps_shift_self (y : PeriodicLatticeSite L) (μ : Fin 3) (hL : 0 < L μ) :
    Q1Real.coordSteps y (periodicLatticeShift y μ) μ = 1 := by
  simp only [Q1Real.coordSteps, periodicLatticeShift, Function.update_self, add_sub_cancel_left]
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)

theorem coordSteps_shift_ne (y : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    Q1Real.coordSteps y (periodicLatticeShift y μ) ν = 0 := by
  simp only [Q1Real.coordSteps, periodicLatticeShift, Function.update_of_ne h, sub_self,
    Fin.val_zero]

/-- Each of `GammaPath`'s three legs, uniformly. -/
theorem leg_eq (y : PeriodicLatticeSite L) (μ d : Fin 3) (hL : 0 < L μ)
    (base : PeriodicLatticeSite L) (hb : base d = y d) :
    Q1Real.straightSegment base (periodicLatticeShift y μ) d
      = if d = μ then [(d, true)] else [] := by
  have hc : Q1Real.coordSteps base (periodicLatticeShift y μ) d
      = Q1Real.coordSteps y (periodicLatticeShift y μ) d := by
    simp only [Q1Real.coordSteps, hb]
  simp only [Q1Real.straightSegment, hc]
  rcases eq_or_ne d μ with rfl | h
  · rw [coordSteps_shift_self y d hL, if_pos rfl, List.replicate_one]
  · rw [coordSteps_shift_ne y μ d h, if_neg h, List.replicate_zero]

/-- **`Γ_{y, y+e_μ}` is the single `μ`-step** — the coarse-to-block contour to the immediate
neighbour does not detour. Needs `0 < L μ`. -/
theorem gammaPath_shift (y : PeriodicLatticeSite L) (μ : Fin 3) (hL : 0 < L μ) :
    Q1Real.GammaPath y (periodicLatticeShift y μ) = [(μ, true)] := by
  have hb1 : (Function.update y 2 ((periodicLatticeShift y μ) 2)) 1 = y 1 :=
    Function.update_of_ne (by decide) _ _
  have hb0 : (Function.update (Function.update y 2 ((periodicLatticeShift y μ) 2)) 1
      ((periodicLatticeShift y μ) 1)) 0 = y 0 := by
    rw [Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
      Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)]
  unfold Q1Real.GammaPath
  rw [leg_eq y μ 2 hL y rfl, leg_eq y μ 1 hL _ hb1, leg_eq y μ 0 hL _ hb0]
  have hμ : μ = 0 ∨ μ = 1 ∨ μ = 2 := by
    rcases μ with ⟨v, hv⟩
    match v, hv with
    | 0, _ => exact Or.inl rfl
    | 1, _ => exact Or.inr (Or.inl rfl)
    | 2, _ => exact Or.inr (Or.inr rfl)
  rcases hμ with rfl | rfl | rfl <;> decide

theorem holonomy_singleStep
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicPathHolonomy U y [(μ, true)] = U (y, μ) := by
  simp [periodicPathHolonomy]

/-- **The two transport factors coincide.** Term `(x,i) = (y, 1)` carries
`Γ_{y,y} ++ [y, y+e_μ] = [(μ,true)]`; term `(x,i) = (y+e_μ, 0)` carries
`Γ_{y,y+e_μ} ++ [] = [(μ,true)]`. Both holonomies are `U_μ(y)`. -/
theorem transport_terms_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) (hL : 0 < L μ) :
    periodicPathHolonomy U y (Q1Real.transportPath y y μ 1) = U (y, μ) ∧
    periodicPathHolonomy U y
      (Q1Real.transportPath y (periodicLatticeShift y μ) μ 0) = U (y, μ) := by
  constructor
  · have hg : Q1Real.GammaPath y y = [] := Q1Real.GammaPath_self y
    have hs : Q1Real.straightSegment y (pathSite y μ 1) μ = [(μ, true)] := by
      simp only [Q1Real.straightSegment, pathSite_succ, pathSite_zero]
      rw [coordSteps_shift_self y μ hL, List.replicate_one]
    simp only [Q1Real.transportPath, hg, hs, List.nil_append]
    exact holonomy_singleStep U y μ
  · have hs : Q1Real.straightSegment (periodicLatticeShift y μ)
        (pathSite (periodicLatticeShift y μ) μ 0) μ = [] := by
      rw [pathSite_zero]; exact Q1Real.straightSegment_self _ _
    simp only [Q1Real.transportPath, hs, List.append_nil, gammaPath_shift y μ hL]
    exact holonomy_singleStep U y μ

/-- **The multiplicity, exactly: at `ell = 2` only `(y,1)` and `(y+e_μ,0)` reach the dropped
bond.** Together with `transport_terms_eq` this pins the diagonal coefficient to
`2 • RMap (U_μ(y))`. -/
theorem readers_ell2 (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (c : CoarseBond L 2)
    (x : PeriodicLatticeSite L) (i : ℕ) (hx : x ∈ blockOf c.1.1 2) (hi : i < 2)
    (heq : (pathSite x c.2 i, c.2) = droppedBondLast 2 c) :
    (x = c.1.1 ∧ i = 1) ∨ (x = periodicLatticeShift c.1.1 c.2 ∧ i = 0) := by
  rw [mem_blockOf] at hx
  have hfit : (c.1.1 c.2).val + 2 ≤ L c.2 + 1 :=
    coarse_coord_add_ell_le hdvd c.2 _ (mem_CoarseLattice.mp c.1.2 c.2) (c.1.1 c.2).isLt
  simp only [droppedBondLast, Prod.mk.injEq] at heq
  obtain ⟨hsite, -⟩ := heq
  -- transverse coordinates of `x` agree with the coarse site
  have htr : ∀ ν : Fin 3, ν ≠ c.2 → x ν = c.1.1 ν := by
    intro ν hν
    have h1 := congrFun hsite ν
    rwa [pathSite_apply_ne _ _ _ _ hν, pathSite_apply_ne _ _ _ _ hν] at h1
  -- the moved coordinate
  have hval : ((x c.2).val + i) % (L c.2 + 1) = ((c.1.1 c.2).val + 1) % (L c.2 + 1) := by
    have h1 := congrArg (fun z : PeriodicLatticeSite L => (z c.2).val) hsite
    rwa [pathSite_apply_self_val, pathSite_apply_self_val] at h1
  rw [Nat.mod_eq_of_lt (show (c.1.1 c.2).val + 1 < L c.2 + 1 by omega)] at hval
  have hlo := (hx c.2).1
  have hhi := (hx c.2).2
  have hxlt : (x c.2).val < L c.2 + 1 := (x c.2).isLt
  have hsum : (x c.2).val + i = (c.1.1 c.2).val + 1 := by
    rcases lt_or_ge ((x c.2).val + i) (L c.2 + 1) with hlt | hge
    · rwa [Nat.mod_eq_of_lt hlt] at hval
    · exfalso
      rw [Nat.mod_eq_sub_mod hge,
        Nat.mod_eq_of_lt (show (x c.2).val + i - (L c.2 + 1) < L c.2 + 1 by omega)] at hval
      omega
  -- `(u, i)` is `(a, 1)` or `(a+1, 0)`
  rcases (show i = 1 ∨ i = 0 by omega) with rfl | rfl
  · left
    refine ⟨?_, rfl⟩
    funext ν
    rcases eq_or_ne ν c.2 with rfl | hν
    · exact Fin.ext (by omega)
    · exact htr ν hν
  · right
    refine ⟨?_, rfl⟩
    funext ν
    rcases eq_or_ne ν c.2 with rfl | hν
    · apply Fin.ext
      have h1 : ((c.1.1 c.2) + 1 : Fin (L c.2 + 1)).val = (c.1.1 c.2).val + 1 := by
        rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < L c.2 + 1 by omega),
          Nat.mod_eq_of_lt (show (c.1.1 c.2).val + 1 < L c.2 + 1 by omega)]
      simp only [periodicLatticeShift, Function.update_self]
      rw [h1]
      omega
    · rw [htr ν hν, periodicLatticeShift, Function.update_of_ne hν]

#print axioms coordSteps_shift_self
#print axioms gammaPath_shift
#print axioms holonomy_singleStep
#print axioms transport_terms_eq
#print axioms readers_ell2

/-! ## §6 — MUTATION PROOF: the OLD dropped bond (offset `0`) DOES couple

`ReparamCSuTwo.droppedBond ell c = (c.1.1, c.2)` sits at `c.2`-offset `0`, which the PREVIOUS
coarse bond's overhang reaches (`ell ≤ 2ell - 2` for `ell ≥ 2`). Concretely on `witnessL`
(`fun _ => 3`, i.e. `4` sites per direction) at `witnessEll = 2`: the coarse bond at the origin in
direction `0` reads the bond `((2,0,0), 0)`, which is the dropped bond of the coarse bond at
`(2,0,0)` in direction `0`. Witness inside the read-set: `x = (1,0,0)`, `i = 1`.

This is the mutation that makes §4 falsifiable: substituting `0` for `ell - 1` in
`droppedBondLast` turns `droppedBondLast_not_reads` into a FALSE statement, refuted by
`droppedBond_couples_witness` below. -/

/-- The coarse site `(2,0,0)` on `witnessL`. -/
def yB : PeriodicLatticeSite witnessL := fun ν => if ν = 0 then 2 else 0

theorem yB_coarse : yB ∈ CoarseLattice witnessL witnessEll := by decide

/-- The coarse bond at the origin, direction `0`. -/
def cA : CoarseBond witnessL witnessEll := (⟨witnessY, witnessY_coarse⟩, 0)

/-- The coarse bond at `(2,0,0)`, direction `0` — the `μ`-neighbour of `cA`. -/
def cB : CoarseBond witnessL witnessEll := (⟨yB, yB_coarse⟩, 0)

theorem cA_ne_cB : cA ≠ cB := by
  intro h
  exact absurd (congrArg (fun p : CoarseBond witnessL witnessEll => (p.1.1) 0) h) (by decide)

/-- The interior site `(1,0,0)` — the last site of `blockOf witnessY 2` in direction `0`. -/
def xMid : PeriodicLatticeSite witnessL := fun ν => if ν = 0 then 1 else 0

theorem xMid_mem_block : xMid ∈ blockOf witnessY witnessEll := by
  rw [mem_blockOf]; decide

/-- **THE COUPLING, kernel-checked**: `cA ≠ cB` yet the constraint at `cA` reads the OLD dropped
bond of `cB`. So with `ReparamCSuTwo.droppedBond` the coarse-bond constraints do NOT decouple. -/
theorem droppedBond_couples_witness :
    ReadsBond witnessEll cA (droppedBond witnessEll cB) :=
  ⟨xMid, xMid_mem_block, 1, Finset.mem_range.mpr (by decide), by decide⟩

#print axioms yB_coarse
#print axioms cA_ne_cB
#print axioms xMid_mem_block
#print axioms droppedBond_couples_witness

/-- Packaged: the analogue of `droppedBondLast_not_reads` for `ReparamCSuTwo.droppedBond` is FALSE.
Stated as an explicit refutation so the mutation is a theorem, not a remark. -/
theorem droppedBond_not_decoupled :
    ¬ (∀ (c c' : CoarseBond witnessL witnessEll), c ≠ c' →
        ¬ ReadsBond witnessEll c (droppedBond witnessEll c')) :=
  fun h => h cA cB cA_ne_cB droppedBond_couples_witness

#print axioms droppedBond_not_decoupled

/-! ## §7 — SECOND MUTATION: the OLD dropped bond IS on an axial staircase

`ReparamCSuTwo.droppedBond witnessEll cA = (witnessY, 0)` lies on `staircasePath witnessY xMid` with
`xMid = (1,0,0) ∈ blockOf witnessY 2` (the direction-`0` leg of `Γ_{y,x}` is
`axisSegment (corner2 y x) 0 [0, 1)`, whose single member is exactly `(witnessY, 0)`). So the OLD
dropped bond is already forced to `0` by the axial gauge — it cannot be the variable the `Q₁`
constraint solves for. This is the second, independent reason the old choice is wrong, and the
mutation witness showing §5b is non-vacuous: substituting `droppedBond` for `droppedBondLast` in
`droppedBondLast_not_mem_staircase` makes it FALSE. -/
theorem droppedBond_mem_staircase_witness :
    droppedBond witnessEll cA ∈ AdmissibleSubspace.staircasePath witnessY xMid := by
  simp only [AdmissibleSubspace.staircasePath, Finset.mem_union]
  right
  rw [AdmissibleSubspace.mem_axisSegment]
  exact ⟨rfl, by decide, by decide, by decide⟩

/-- Packaged refutation: the analogue of `droppedBondLast_not_mem_staircase` for
`ReparamCSuTwo.droppedBond` is FALSE. -/
theorem droppedBond_not_off_staircases :
    ¬ (∀ (c : CoarseBond witnessL witnessEll) (y' : PeriodicLatticeSite witnessL),
        y' ∈ CoarseLattice witnessL witnessEll →
        ∀ x : PeriodicLatticeSite witnessL, x ∈ blockOf y' witnessEll →
          droppedBond witnessEll c ∉ AdmissibleSubspace.staircasePath y' x) :=
  fun h => h cA witnessY witnessY_coarse xMid xMid_mem_block droppedBond_mem_staircase_witness

#print axioms droppedBond_mem_staircase_witness
#print axioms droppedBond_not_off_staircases

end AdalyFormal.Balaban.ReparamCDisjoint
