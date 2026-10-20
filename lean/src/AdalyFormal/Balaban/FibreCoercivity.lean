/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.AxialCoercivity
import AdalyFormal.Balaban.CovU1Reduction
import AdalyFormal.Balaban.LineIntegralCovariant
import AdalyFormal.Balaban.LemmaAssembly
import AdalyFormal.Balaban.DeltaKUnitLevel

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

/-!
# `FibreCoercivity.lean` — the TRIPLE KERNEL of CMP95 printed p.19, DECIDED

Lane record: `compute/fibre_coercivity/PROGRESS.md`.

## The question

CMP95 printed p.19 asserts, with no printed proof, that the quadratic form `⟨∂A, ∂A⟩` is positive
on the subspace cut out by `QA = 0` and `A(Γ_{y,x}) = 0`. The FIRST thing that claim needs is that
the three conditions have only the zero field in common: a quantitative bound over a nonzero kernel
would be theater.

**THE QUESTION.** At a SINGLE level, block side `ell = 2`, flat background: is

`ker(d) ∩ ker(Q_2) ∩ ker(P_Ax) = {0}` ?

**THE ANSWER PROVED HERE: YES**, at every periodic extent with `2 ∣ (L μ + 1)` — not just at the
`6³` witness. `triple_kernel_trivial` is the theorem. Its conclusion is an equation on a
universally quantified field (`A = 0`), so there is no existential for a degenerate instance to
satisfy.

## What the three clauses are

* `closedFlat A` — the fine curl vanishes on every plaquette (`CovU1Reduction.flatCurlValue`, the
  `U = 1` reduction of CMP99b `(3.4)`'s covariant curl). REUSED, not redefined.
* `lineCoarseRestrictCov (trivialU L) 2 A b = 0` for every coarse bond — the tree's OWN `Q`
  (`LineIntegralCovariant`), at the flat background. REUSED, not redefined.
* `pAx A (CoarseLattice L 2) 2 = 0` — the tree's OWN axial gauge-fixing form (`AxialCoercivity`,
  CMP95 `(1.10)` at unit weight). REUSED, not redefined. Its zero locus is exactly
  `∀ y x, A(Γ_{y,x}) = 0` (`AxialCoercivity.pAx_eq_zero_iff`), so using the quadratic form and
  using the source's delta constraint are the same hypothesis, not a weakening.

## Each clause is load-bearing (§5)

Three fields, each satisfying exactly TWO of the three clauses and each PROVED NONZERO:

| field | closed | `Q` | `P_Ax` |
|---|---|---|---|
| `altMode` (direction `0`, alternating in `x₀`) | `0` | `0` | `≠ 0` |
| `blockMode` (direction `0`, odd-`x₀` indicator) | `0` | `≠ 0` | `0` |
| `oddAltMode` (direction `1`, alternating in `x₁`, odd-`x₀` slices) | `≠ 0` | `0` | `0` |

The first two are general-extent forms of `BridgeRestricted.altC` / `AxialCoercivity.blockC`; the
third is new here and is what shows the CURL clause is not redundant.

## The proof, in three stages

Write `A_μ(x)` for `A (x, μ)`. Call a bond `(z, μ)` **intra-block** when `(z μ).val` is even — then
both endpoints lie in one side-`2` block.

* **§2 — closed + `P_Ax = 0` ⟹ every intra-block bond vanishes** (`intra_block_vanishes`).
  Seven of a block's twelve intra-block bonds are its `(1.7)` spanning tree and fall out of the
  contour integrals ALONE, no curl: the `(1.7)` order makes the system triangular,
  `A(Γ_{y, y+re₀+se₁+te₂}) = t·A₂(y) + s·A₁(y+te₂) + r·A₀(y+se₁+te₂)`. The other five each follow
  from ONE plaquette whose other three bonds are already known (the last at a second level of
  nesting).
* **§3 — closed + §2 ⟹ inter-block bonds are constant across a block**
  (`inter_block_shift`, `inter_block_const`). For `(z μ).val` odd and `(z ν).val` even, the `(μ,ν)`
  plaquette at `z` has both direction-`ν` bonds intra-block, hence zero, so
  `A_μ(z) = A_μ(z + e_ν)`.
* **§4 — `Q = 0` + §2 + §3 ⟹ the inter-block bonds vanish** (`Q_kills_inter_block`). In
  `2⁴·Q_μ(y) = ∑_{x∈B(y)} (A_μ(x) + A_μ(x+e_μ))` each summand contributes exactly ONE bond that §2
  does not already kill, and §3 says all of them equal `A_μ(y+e_μ)`. So the sum is
  `|B(y)| · A_μ(y+e_μ)` and `Q = 0` kills it.

Stage §4 never uses closedness on the odd–odd plaquettes: the coarse `1`-form surviving §2/§3 is
annihilated by `Q` outright, with no coarse Hodge argument. That is why the theorem holds at every
even extent rather than only where coarse cohomology is controlled.

## Scope, stated so nobody over-reads it

* **`ell = 2` only.** The scratchpad probe `compute/fibre_coercivity/triple_kernel.py` reports a
  zero triple kernel at `ell ∈ {2,3,4}` and at four extents, but that instrument signs nothing
  (REFORM CHARTER: python explores; the kernel is the evidence). Only `ell = 2` is PROVED here.
* **Flat background only.** `closedFlat` is the `U = 1` curl and the `Q` clause is at `trivialU`.
  `pAx` is background-independent already (its contours carry no transport); the other two are not.
* **This is the QUALITATIVE half of p.19** — positive DEFINITENESS on the subspace. It is not yet
  `≥ c · bondEnergy` with an explicit `c`. §6 states exactly what is owed.
* `ell = 1` is degenerate: `pAx ≡ 0` there (`AxialCoercivity.pAx_ell_one`), so nothing at `ell = 1`
  is evidence about the gauge-fixing clause. Recorded in place as `ell1_pAx_vacuous`.
-/

namespace AdalyFormal.Balaban.FibreCoercivity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.AxialCoercivity
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue flatCurlValue_smul)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.Q1Real (rZeroA rZeroA_trivialU)
open AdalyFormal.Balaban.QOne (pathSite)

variable {L : PeriodicLatticeExtent}

/-! ## §0. Site arithmetic — offsets, shifts, parity

Everything is stated at a GENERAL periodic extent subject to `2 ∣ (L μ + 1)`: the side-`2` blocks
tile the torus exactly when the extent is even in every direction. That hypothesis is the
`blockOf`-truncation guard, carried explicitly rather than assumed away. -/

/-- Case analysis on `Fin 3` that leaves NUMERALS in the goal (`fin_cases` leaves
`(fun i ↦ i) ⟨0, _⟩`, against which the `off3` simp lemmas do not fire). -/
theorem fin3_cases (ν : Fin 3) : ν = 0 ∨ ν = 1 ∨ ν = 2 := by revert ν; decide

/-- The three ordered plaquette direction pairs, enumerated. -/
theorem plaq_dirs (d : {p : Fin 3 × Fin 3 // p.1 < p.2}) :
    (d.1.1 = 0 ∧ d.1.2 = 1) ∨ (d.1.1 = 0 ∧ d.1.2 = 2) ∨ (d.1.1 = 1 ∧ d.1.2 = 2) := by
  revert d; decide

/-- The even part of a coordinate, as a site: `cc z` is the CENTRE of the unique side-`2` block
containing `z`. -/
def cc (z : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun μ => ⟨(z μ).val - (z μ).val % 2, by have := (z μ).isLt; omega⟩

theorem cc_val (z : PeriodicLatticeSite L) (μ : Fin 3) :
    (cc z μ).val = (z μ).val - (z μ).val % 2 := rfl

theorem cc_even (z : PeriodicLatticeSite L) (μ : Fin 3) : (cc z μ).val % 2 = 0 := by
  rw [cc_val]; omega

theorem cc_mem (z : PeriodicLatticeSite L) : cc z ∈ CoarseLattice L 2 :=
  mem_CoarseLattice.2 (fun μ => cc_even z μ)

/-- A site displaced from `y` by a coordinate-wise offset, reduced modulo the extent. Total, with
the honest val identity available under the no-wrap bound. -/
def addOff (y : PeriodicLatticeSite L) (e : Fin 3 → ℕ) : PeriodicLatticeSite L :=
  fun μ => ⟨((y μ).val + e μ) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem addOff_val (y : PeriodicLatticeSite L) (e : Fin 3 → ℕ) (μ : Fin 3)
    (h : (y μ).val + e μ < L μ + 1) : (addOff y e μ).val = (y μ).val + e μ :=
  Nat.mod_eq_of_lt h

/-- The concrete three-component offset: `off3 r s t` is `r` in direction `0`, `s` in direction
`1`, `t` in direction `2`. -/
def off3 (r s t : ℕ) : Fin 3 → ℕ := fun ν => if ν = 0 then r else if ν = 1 then s else t

theorem off3_zero (r s t : ℕ) : off3 r s t 0 = r := rfl

theorem off3_one (r s t : ℕ) : off3 r s t 1 = s := rfl

theorem off3_two (r s t : ℕ) : off3 r s t 2 = t := rfl

theorem off3_le (r s t : ℕ) (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) (ν : Fin 3) :
    off3 r s t ν ≤ 1 := by
  rcases fin3_cases ν with rfl | rfl | rfl
  · rw [off3_zero]; exact hr
  · rw [off3_one]; exact hs
  · rw [off3_two]; exact ht

theorem eq_off3 (e : Fin 3 → ℕ) : e = off3 (e 0) (e 1) (e 2) := by
  funext ν
  rcases fin3_cases ν with rfl | rfl | rfl
  · rw [off3_zero]
  · rw [off3_one]
  · rw [off3_two]

theorem off3_000 (ν : Fin 3) : off3 0 0 0 ν = 0 := by
  rcases fin3_cases ν with rfl | rfl | rfl <;> rfl

theorem addOff_zero (y : PeriodicLatticeSite L) : addOff y (off3 0 0 0) = y := by
  funext ν
  apply Fin.ext
  rw [addOff_val y _ ν (by rw [off3_000]; simpa using (y ν).isLt), off3_000]
  omega

theorem addOff_congr (y : PeriodicLatticeSite L) {e e' : Fin 3 → ℕ} (h : ∀ ν, e ν = e' ν) :
    addOff y e = addOff y e' := by
  funext ν
  apply Fin.ext
  show ((y ν).val + e ν) % (L ν + 1) = ((y ν).val + e' ν) % (L ν + 1)
  rw [h ν]

/-- Recognizing a site as an offset of another, from the coordinate values. -/
theorem addOff_of_val (y z : PeriodicLatticeSite L) (e : Fin 3 → ℕ)
    (h : ∀ ν, (z ν).val = (y ν).val + e ν) : z = addOff y e := by
  funext ν
  apply Fin.ext
  rw [addOff_val y e ν (by rw [← h ν]; exact (z ν).isLt), ← h ν]

theorem shiftNe (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hne : ν ≠ μ) :
    (periodicLatticeShift x μ) ν = x ν :=
  Function.update_of_ne hne _ _

theorem shiftSelf (x : PeriodicLatticeSite L) (μ : Fin 3) (h : (x μ).val + 1 < L μ + 1) :
    ((periodicLatticeShift x μ) μ).val = (x μ).val + 1 := by
  show ((Function.update x μ (x μ + 1)) μ).val = _
  rw [Function.update_self]
  exact Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; omega)

/-- The shift's coordinate value, INCLUDING the wrap-around case. -/
theorem shiftMod (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((periodicLatticeShift x μ) μ).val = ((x μ).val + 1) % (L μ + 1) := by
  by_cases h : (x μ).val + 1 < L μ + 1
  · rw [shiftSelf x μ h, Nat.mod_eq_of_lt h]
  · have hx := (x μ).isLt
    have he : (x μ).val = L μ := by omega
    show ((Function.update x μ (x μ + 1)) μ).val = _
    rw [Function.update_self]
    have hlast : x μ = Fin.last (L μ) := Fin.ext (by rw [Fin.val_last]; exact he)
    rw [hlast, Fin.last_add_one]
    simp [he]

/-- **Wrap-around preserves parity**, because the extent is even. This is what lets every statement
below be about `(z μ).val % 2` with no boundary case. -/
theorem shift_parity (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (x : PeriodicLatticeSite L)
    (μ : Fin 3) : ((periodicLatticeShift x μ) μ).val % 2 = ((x μ).val + 1) % 2 := by
  rw [shiftMod, Nat.mod_mod_of_dvd _ (hdvd μ)]

/-- A coarse centre has room for a full block: its coordinate is even and the extent is even, so it
is not the last site in any direction. The `blockOf`-truncation guard. -/
theorem coarse_room (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) (μ : Fin 3) : (y μ).val + 1 < L μ + 1 := by
  obtain ⟨k, hk⟩ := hdvd μ
  have h1 := hy μ
  have h2 := (y μ).isLt
  omega

theorem addOff_bound (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) {e : Fin 3 → ℕ} (he : ∀ ν, e ν ≤ 1) (ν : Fin 3) :
    (y ν).val + e ν < L ν + 1 := by
  have h1 := coarse_room hdvd hy ν
  have h2 := he ν
  omega

/-- Shifting an offset site increments that offset, as long as both stay inside the block. -/
theorem shift_addOff (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) (e e' : Fin 3 → ℕ) (μ : Fin 3)
    (he : ∀ ν, e ν ≤ 1) (he' : ∀ ν, e' ν ≤ 1)
    (hμ : e' μ = e μ + 1) (hν : ∀ ν, ν ≠ μ → e' ν = e ν) :
    periodicLatticeShift (addOff y e) μ = addOff y e' := by
  funext ν
  by_cases h : ν = μ
  · subst h
    apply Fin.ext
    have hb := addOff_bound hdvd hy he ν
    have hb' := addOff_bound hdvd hy he' ν
    rw [shiftSelf _ _ (by rw [addOff_val y e ν hb]; omega), addOff_val y e ν hb,
      addOff_val y e' ν hb', hμ]
    omega
  · rw [shiftNe _ h]
    apply Fin.ext
    show ((y ν).val + e ν) % (L ν + 1) = ((y ν).val + e' ν) % (L ν + 1)
    rw [hν ν h]

/-- The parity of an offset coordinate at a coarse centre. -/
theorem addOff_parity (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) {e : Fin 3 → ℕ} (he : ∀ ν, e ν ≤ 1) (ν : Fin 3) :
    (addOff y e ν).val % 2 = e ν % 2 := by
  rw [addOff_val y e ν (addOff_bound hdvd hy he ν)]
  have h := hy ν
  omega

/-- Every site of `B(y)` for a coarse `y` is an offset of `y` by `0`s and `1`s. -/
theorem mem_block_offset {y x : PeriodicLatticeSite L} (hx : x ∈ blockOf y 2) :
    x = addOff y (fun ν => (x ν).val - (y ν).val) ∧ ∀ ν, (x ν).val - (y ν).val ≤ 1 := by
  have hb := mem_blockOf.1 hx
  refine ⟨addOff_of_val y x _ (fun ν => ?_), fun ν => ?_⟩
  · have := hb ν; omega
  · have := hb ν; omega

theorem mem_blockOf_addOff (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) {e : Fin 3 → ℕ} (he : ∀ ν, e ν ≤ 1) :
    addOff y e ∈ blockOf y 2 := by
  refine mem_blockOf.2 (fun ν => ?_)
  rw [addOff_val y e ν (addOff_bound hdvd hy he ν)]
  have := he ν
  omega

theorem shift_eq_addOff0 (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) :
    periodicLatticeShift y 0 = addOff y (off3 1 0 0) := by
  have h := shift_addOff hdvd hy (off3 0 0 0) (off3 1 0 0) 0
    (by decide) (by decide) (by decide) (by decide)
  rwa [addOff_zero] at h

theorem shift_eq_addOff1 (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) :
    periodicLatticeShift y 1 = addOff y (off3 0 1 0) := by
  have h := shift_addOff hdvd hy (off3 0 0 0) (off3 0 1 0) 1
    (by decide) (by decide) (by decide) (by decide)
  rwa [addOff_zero] at h

theorem shift_eq_addOff2 (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) :
    periodicLatticeShift y 2 = addOff y (off3 0 0 1) := by
  have h := shift_addOff hdvd hy (off3 0 0 0) (off3 0 0 1) 2
    (by decide) (by decide) (by decide) (by decide)
  rwa [addOff_zero] at h

#print axioms fin3_cases
#print axioms plaq_dirs
#print axioms cc
#print axioms cc_mem
#print axioms addOff
#print axioms off3
#print axioms eq_off3
#print axioms addOff_zero
#print axioms addOff_congr
#print axioms addOff_of_val
#print axioms shiftMod
#print axioms shift_parity
#print axioms coarse_room
#print axioms shift_addOff
#print axioms addOff_parity
#print axioms mem_block_offset
#print axioms mem_blockOf_addOff
#print axioms shift_eq_addOff0
#print axioms shift_eq_addOff1
#print axioms shift_eq_addOff2

/-! ## §1. The closedness clause and the explicit contour integral -/

/-- **The fine closedness clause**, `d A = 0`, at the flat background. -/
def closedFlat (A : Bond L → SuTwo) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, flatCurlValue A p = 0

/-- The plaquette relation in the form used below. -/
theorem curl_rel {A : Bond L → SuTwo} (hc : closedFlat A) (z : PeriodicLatticeSite L)
    (μ ν : Fin 3) (h : μ < ν) :
    A (z, μ) + A (periodicLatticeShift z μ, ν) - A (periodicLatticeShift z ν, μ) - A (z, ν) = 0 :=
  hc (z, ⟨(μ, ν), h⟩)

/-- `Γ_{y,x}` splits into its three axis runs, and the contour integral splits with it. The runs
carry three DIFFERENT bond directions, which is the disjointness. -/
theorem pathIntegral_split (A : Bond L → SuTwo) (y x : PeriodicLatticeSite L) :
    pathIntegral A y x
      = (∑ b ∈ axisSegment y 2 (min (y 2).val (x 2).val) (max (y 2).val (x 2).val), A b)
        + (∑ b ∈ axisSegment (corner1 y x) 1 (min (y 1).val (x 1).val)
            (max (y 1).val (x 1).val), A b)
        + (∑ b ∈ axisSegment (corner2 y x) 0 (min (y 0).val (x 0).val)
            (max (y 0).val (x 0).val), A b) := by
  have hdir : ∀ (base : PeriodicLatticeSite L) (μ : Fin 3) (a b : ℕ) (e : Bond L),
      e ∈ axisSegment base μ a b → e.2 = μ := fun _ _ _ _ _ h => (mem_axisSegment.1 h).1
  have hd21 : Disjoint (axisSegment y 2 (min (y 2).val (x 2).val) (max (y 2).val (x 2).val))
      (axisSegment (corner1 y x) 1 (min (y 1).val (x 1).val) (max (y 1).val (x 1).val)) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    exact absurd ((hdir _ _ _ _ _ h1).symm.trans (hdir _ _ _ _ _ h2)) (by decide)
  have hd0 : Disjoint
      ((axisSegment y 2 (min (y 2).val (x 2).val) (max (y 2).val (x 2).val))
        ∪ (axisSegment (corner1 y x) 1 (min (y 1).val (x 1).val) (max (y 1).val (x 1).val)))
      (axisSegment (corner2 y x) 0 (min (y 0).val (x 0).val) (max (y 0).val (x 0).val)) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    have h0 := hdir _ _ _ _ _ h2
    rcases Finset.mem_union.1 h1 with h | h
    · exact absurd ((hdir _ _ _ _ _ h).symm.trans h0) (by decide)
    · exact absurd ((hdir _ _ _ _ _ h).symm.trans h0) (by decide)
  unfold pathIntegral staircasePath
  rw [Finset.sum_union hd0, Finset.sum_union hd21]

theorem corner1_addOff (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) (r s t : ℕ)
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) :
    corner1 y (addOff y (off3 r s t)) = addOff y (off3 0 0 t) := by
  have hb := addOff_bound hdvd hy (off3_le r s t hr hs ht)
  have hb0 := addOff_bound hdvd hy (off3_le 0 0 t (by omega) (by omega) ht)
  funext ν
  apply Fin.ext
  show (Function.update y 2 (addOff y (off3 r s t) 2) ν).val = _
  by_cases h : ν = 2
  · subst h
    rw [Function.update_self, addOff_val y _ 2 (hb 2), addOff_val y _ 2 (hb0 2), off3_two, off3_two]
  · rw [Function.update_of_ne h, addOff_val y _ ν (hb0 ν)]
    have hz : off3 0 0 t ν = 0 := by
      rcases fin3_cases ν with rfl | rfl | rfl
      · rfl
      · rfl
      · exact absurd rfl h
    omega

theorem corner2_addOff (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) (r s t : ℕ)
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) :
    corner2 y (addOff y (off3 r s t)) = addOff y (off3 0 s t) := by
  have hb := addOff_bound hdvd hy (off3_le r s t hr hs ht)
  have hbs := addOff_bound hdvd hy (off3_le 0 s t (by omega) hs ht)
  have hb0 := addOff_bound hdvd hy (off3_le 0 0 t (by omega) (by omega) ht)
  show Function.update (corner1 y (addOff y (off3 r s t))) 1 (addOff y (off3 r s t) 1) = _
  rw [corner1_addOff hdvd hy r s t hr hs ht]
  funext ν
  apply Fin.ext
  by_cases h : ν = 1
  · subst h
    rw [Function.update_self, addOff_val y _ 1 (hb 1), addOff_val y _ 1 (hbs 1), off3_one, off3_one]
  · rw [Function.update_of_ne h, addOff_val y _ ν (hb0 ν), addOff_val y _ ν (hbs ν)]
    have he : off3 0 0 t ν = off3 0 s t ν := by
      rcases fin3_cases ν with rfl | rfl | rfl
      · rfl
      · exact absurd rfl h
      · rfl
    omega

/-- **THE CONTOUR INTEGRAL AT BLOCK SCALE `2`, EXPLICITLY.** The `(1.7)` order (coordinate `2`
first, then `1`, then `0`) makes the seven-equation system TRIANGULAR: each new contour adds at
most one bond to the previous ones. -/
theorem pathIntegral_off3 (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) (r s t : ℕ)
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) :
    pathIntegral A y (addOff y (off3 r s t))
      = (if t = 1 then A (y, 2) else 0)
        + (if s = 1 then A (addOff y (off3 0 0 t), 1) else 0)
        + (if r = 1 then A (addOff y (off3 0 s t), 0) else 0) := by
  have hb := addOff_bound hdvd hy (off3_le r s t hr hs ht)
  have hb0 := addOff_bound hdvd hy (off3_le 0 0 t (by omega) (by omega) ht)
  have hbs := addOff_bound hdvd hy (off3_le 0 s t (by omega) hs ht)
  have hv0 : (addOff y (off3 r s t) 0).val = (y 0).val + r := by
    rw [addOff_val y _ 0 (hb 0), off3_zero]
  have hv1 : (addOff y (off3 r s t) 1).val = (y 1).val + s := by
    rw [addOff_val y _ 1 (hb 1), off3_one]
  have hv2 : (addOff y (off3 r s t) 2).val = (y 2).val + t := by
    rw [addOff_val y _ 2 (hb 2), off3_two]
  have hbase1 : (addOff y (off3 0 0 t) 1).val = (y 1).val := by
    rw [addOff_val y _ 1 (hb0 1), off3_one]; omega
  have hbase0 : (addOff y (off3 0 s t) 0).val = (y 0).val := by
    rw [addOff_val y _ 0 (hbs 0), off3_zero]; omega
  rw [pathIntegral_split, corner1_addOff hdvd hy r s t hr hs ht,
    corner2_addOff hdvd hy r s t hr hs ht]
  have e2 : (∑ b ∈ axisSegment y 2 (min (y 2).val (addOff y (off3 r s t) 2).val)
      (max (y 2).val (addOff y (off3 r s t) 2).val), A b) = if t = 1 then A (y, 2) else 0 := by
    rw [show min (y 2).val (addOff y (off3 r s t) 2).val = (y 2).val by omega]
    rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
    · rw [show max (y 2).val (addOff y (off3 r s 0) 2).val = (y 2).val by omega,
        axisSegment_self_empty]
      simp
    · rw [show max (y 2).val (addOff y (off3 r s 1) 2).val = (y 2).val + 1 by omega,
        axisSegment_succ_singleton]
      simp
  have e1 : (∑ b ∈ axisSegment (addOff y (off3 0 0 t)) 1
      (min (y 1).val (addOff y (off3 r s t) 1).val)
      (max (y 1).val (addOff y (off3 r s t) 1).val), A b)
      = if s = 1 then A (addOff y (off3 0 0 t), 1) else 0 := by
    rw [show min (y 1).val (addOff y (off3 r s t) 1).val = (addOff y (off3 0 0 t) 1).val by omega]
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [show max (y 1).val (addOff y (off3 r 0 t) 1).val
        = (addOff y (off3 0 0 t) 1).val by omega, axisSegment_self_empty]
      simp
    · rw [show max (y 1).val (addOff y (off3 r 1 t) 1).val
        = (addOff y (off3 0 0 t) 1).val + 1 by omega, axisSegment_succ_singleton]
      simp
  have e0 : (∑ b ∈ axisSegment (addOff y (off3 0 s t)) 0
      (min (y 0).val (addOff y (off3 r s t) 0).val)
      (max (y 0).val (addOff y (off3 r s t) 0).val), A b)
      = if r = 1 then A (addOff y (off3 0 s t), 0) else 0 := by
    rw [show min (y 0).val (addOff y (off3 r s t) 0).val = (addOff y (off3 0 s t) 0).val by omega]
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · rw [show max (y 0).val (addOff y (off3 0 s t) 0).val
        = (addOff y (off3 0 s t) 0).val by omega, axisSegment_self_empty]
      simp
    · rw [show max (y 0).val (addOff y (off3 1 s t) 0).val
        = (addOff y (off3 0 s t) 0).val + 1 by omega, axisSegment_succ_singleton]
      simp
  rw [e2, e1, e0]

#print axioms closedFlat
#print axioms curl_rel
#print axioms pathIntegral_split
#print axioms corner1_addOff
#print axioms corner2_addOff
#print axioms pathIntegral_off3

/-! ## §2. STAGE ONE — closed + `P_Ax = 0` kills every INTRA-BLOCK bond -/

/-- The seven `(1.7)` tree bonds of a block, from the contour integrals ALONE — **no curl is used
here**. This is the half of CMP95 p.19's positivity that the gauge fixing supplies unaided. -/
theorem tree_bonds_vanish (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (hI : ∀ r s t : ℕ, r ≤ 1 → s ≤ 1 → t ≤ 1 →
      pathIntegral A y (addOff y (off3 r s t)) = 0) :
    A (addOff y (off3 0 0 0), 2) = 0 ∧ A (addOff y (off3 0 0 0), 1) = 0
      ∧ A (addOff y (off3 0 0 1), 1) = 0 ∧ A (addOff y (off3 0 0 0), 0) = 0
      ∧ A (addOff y (off3 0 1 0), 0) = 0 ∧ A (addOff y (off3 0 0 1), 0) = 0
      ∧ A (addOff y (off3 0 1 1), 0) = 0 := by
  have P : ∀ r s t : ℕ, r ≤ 1 → s ≤ 1 → t ≤ 1 →
      (if t = 1 then A (y, 2) else 0)
        + (if s = 1 then A (addOff y (off3 0 0 t), 1) else 0)
        + (if r = 1 then A (addOff y (off3 0 s t), 0) else 0) = 0 :=
    fun r s t hr hs ht =>
      (pathIntegral_off3 hdvd A hy r s t hr hs ht).symm.trans (hI r s t hr hs ht)
  have hz : addOff y (off3 0 0 0) = y := addOff_zero y
  have T1 : A (y, 2) = 0 := by
    have h := P 0 0 1 (by omega) (by omega) (by omega); simpa using h
  have T2 : A (addOff y (off3 0 0 0), 1) = 0 := by
    have h := P 0 1 0 (by omega) (by omega) (by omega); simpa using h
  have T3 : A (addOff y (off3 0 0 1), 1) = 0 := by
    have h := P 0 1 1 (by omega) (by omega) (by omega)
    simp only [if_pos rfl, if_neg (by omega : ¬(0 = 1))] at h
    rw [T1] at h; simpa using h
  have T4 : A (addOff y (off3 0 0 0), 0) = 0 := by
    have h := P 1 0 0 (by omega) (by omega) (by omega); simpa using h
  have T5 : A (addOff y (off3 0 1 0), 0) = 0 := by
    have h := P 1 1 0 (by omega) (by omega) (by omega)
    simp only [if_pos rfl, if_neg (by omega : ¬(0 = 1))] at h
    rw [T2] at h; simpa using h
  have T6 : A (addOff y (off3 0 0 1), 0) = 0 := by
    have h := P 1 0 1 (by omega) (by omega) (by omega)
    simp only [if_pos rfl, if_neg (by omega : ¬(0 = 1))] at h
    rw [T1] at h; simpa using h
  have T7 : A (addOff y (off3 0 1 1), 0) = 0 := by
    have h := P 1 1 1 (by omega) (by omega) (by omega)
    simp only [if_pos rfl] at h
    rw [T1, T3] at h; simpa using h
  exact ⟨by rw [hz]; exact T1, T2, T3, T4, T5, T6, T7⟩

/-- The remaining five intra-block bonds, one plaquette each (the last at a second level of
nesting). -/
theorem nontree_bonds_vanish (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hc : closedFlat A) {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (hI : ∀ r s t : ℕ, r ≤ 1 → s ≤ 1 → t ≤ 1 →
      pathIntegral A y (addOff y (off3 r s t)) = 0) :
    A (addOff y (off3 1 0 0), 1) = 0 ∧ A (addOff y (off3 1 0 1), 1) = 0
      ∧ A (addOff y (off3 1 0 0), 2) = 0 ∧ A (addOff y (off3 0 1 0), 2) = 0
      ∧ A (addOff y (off3 1 1 0), 2) = 0 := by
  obtain ⟨T1, T2, T3, T4, T5, T6, T7⟩ := tree_bonds_vanish hdvd A hy hI
  have hz : addOff y (off3 0 0 0) = y := addOff_zero y
  have hT1 : A (addOff y (off3 0 0 0), 2) = 0 := T1
  have N1 : A (addOff y (off3 1 0 0), 1) = 0 := by
    have h := curl_rel hc (addOff y (off3 0 0 0)) 0 1 (by decide)
    rw [shift_addOff hdvd hy (off3 0 0 0) (off3 1 0 0) 0
        (by decide) (by decide) (by decide) (by decide),
      shift_addOff hdvd hy (off3 0 0 0) (off3 0 1 0) 1
        (by decide) (by decide) (by decide) (by decide),
      T4, T5, T2] at h
    simpa using h
  have N2 : A (addOff y (off3 1 0 1), 1) = 0 := by
    have h := curl_rel hc (addOff y (off3 0 0 1)) 0 1 (by decide)
    rw [shift_addOff hdvd hy (off3 0 0 1) (off3 1 0 1) 0
        (by decide) (by decide) (by decide) (by decide),
      shift_addOff hdvd hy (off3 0 0 1) (off3 0 1 1) 1
        (by decide) (by decide) (by decide) (by decide),
      T6, T7, T3] at h
    simpa using h
  have N3 : A (addOff y (off3 1 0 0), 2) = 0 := by
    have h := curl_rel hc (addOff y (off3 0 0 0)) 0 2 (by decide)
    rw [shift_addOff hdvd hy (off3 0 0 0) (off3 1 0 0) 0
        (by decide) (by decide) (by decide) (by decide),
      shift_addOff hdvd hy (off3 0 0 0) (off3 0 0 1) 2
        (by decide) (by decide) (by decide) (by decide),
      T4, T6, hT1] at h
    simpa using h
  have N4 : A (addOff y (off3 0 1 0), 2) = 0 := by
    have h := curl_rel hc (addOff y (off3 0 0 0)) 1 2 (by decide)
    rw [shift_addOff hdvd hy (off3 0 0 0) (off3 0 1 0) 1
        (by decide) (by decide) (by decide) (by decide),
      shift_addOff hdvd hy (off3 0 0 0) (off3 0 0 1) 2
        (by decide) (by decide) (by decide) (by decide),
      T2, T3, hT1] at h
    simpa using h
  have N5 : A (addOff y (off3 1 1 0), 2) = 0 := by
    have h := curl_rel hc (addOff y (off3 0 1 0)) 0 2 (by decide)
    rw [shift_addOff hdvd hy (off3 0 1 0) (off3 1 1 0) 0
        (by decide) (by decide) (by decide) (by decide),
      shift_addOff hdvd hy (off3 0 1 0) (off3 0 1 1) 2
        (by decide) (by decide) (by decide) (by decide),
      T5, T7, N4] at h
    simpa using h
  exact ⟨N1, N2, N3, N4, N5⟩

/-- **STAGE ONE, POINTWISE.** Closed plus the `(1.10)` gauge condition kills every bond whose
direction-coordinate is EVEN — every bond with both endpoints in a single side-`2` block. -/
theorem intra_block_vanishes (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hc : closedFlat A) (hP : pAx A (CoarseLattice L 2) 2 = 0)
    (z : PeriodicLatticeSite L) (μ : Fin 3) (hz : (z μ).val % 2 = 0) :
    A (z, μ) = 0 := by
  set y := cc z with hydef
  have hy : ∀ ν : Fin 3, (y ν).val % 2 = 0 := fun ν => cc_even z ν
  have hyc : y ∈ CoarseLattice L 2 := cc_mem z
  have hI : ∀ r s t : ℕ, r ≤ 1 → s ≤ 1 → t ≤ 1 →
      pathIntegral A y (addOff y (off3 r s t)) = 0 := by
    intro r s t hr hs ht
    by_cases hxy : addOff y (off3 r s t) = y
    · rw [hxy]
      unfold pathIntegral
      rw [staircasePath_self, Finset.sum_empty]
    · exact (pAx_eq_zero_iff A (CoarseLattice L 2) 2).1 hP y hyc _
        (Finset.mem_erase.2 ⟨hxy, mem_blockOf_addOff hdvd hy (off3_le r s t hr hs ht)⟩)
  obtain ⟨T1, T2, T3, T4, T5, T6, T7⟩ := tree_bonds_vanish hdvd A hy hI
  obtain ⟨N1, N2, N3, N4, N5⟩ := nontree_bonds_vanish hdvd A hc hy hI
  have hT1 : A (addOff y (off3 0 0 0), 2) = 0 := T1
  set e : Fin 3 → ℕ := fun ν => (z ν).val % 2 with hedef
  have hze : z = addOff y e := by
    refine addOff_of_val y z e (fun ν => ?_)
    show (z ν).val = (cc z ν).val + (z ν).val % 2
    rw [cc_val]
    omega
  have hb0 : e 0 ≤ 1 := by simp only [hedef]; omega
  have hb1 : e 1 ≤ 1 := by simp only [hedef]; omega
  have hb2 : e 2 ≤ 1 := by simp only [hedef]; omega
  have hsplit : e = off3 (e 0) (e 1) (e 2) := eq_off3 e
  rw [hze, hsplit]
  rcases fin3_cases μ with rfl | rfl | rfl
  · rw [show e 0 = 0 from hz]
    rcases (show e 1 = 0 ∨ e 1 = 1 by omega) with h1 | h1 <;>
      rcases (show e 2 = 0 ∨ e 2 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact T4
    · exact T6
    · exact T5
    · exact T7
  · rw [show e 1 = 0 from hz]
    rcases (show e 0 = 0 ∨ e 0 = 1 by omega) with h1 | h1 <;>
      rcases (show e 2 = 0 ∨ e 2 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact T2
    · exact T3
    · exact N1
    · exact N2
  · rw [show e 2 = 0 from hz]
    rcases (show e 0 = 0 ∨ e 0 = 1 by omega) with h1 | h1 <;>
      rcases (show e 1 = 0 ∨ e 1 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact hT1
    · exact N4
    · exact N3
    · exact N5

#print axioms tree_bonds_vanish
#print axioms nontree_bonds_vanish
#print axioms intra_block_vanishes

/-! ## §3. STAGE TWO — the surviving INTER-BLOCK bonds are constant across a block -/

/-- **One transverse step does not change an inter-block bond.** The `(μ,ν)` plaquette at `z` has
BOTH of its direction-`ν` bonds intra-block (their `ν`-coordinate is `z ν`, even), so §2 kills them
and the plaquette relation degenerates to `A_μ(z) = A_μ(z + e_ν)`. -/
theorem inter_block_shift (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hc : closedFlat A) (hP : pAx A (CoarseLattice L 2) 2 = 0)
    (z : PeriodicLatticeSite L) (μ ν : Fin 3) (hne : ν ≠ μ) (hzν : (z ν).val % 2 = 0) :
    A (z, μ) = A (periodicLatticeShift z ν, μ) := by
  have hkill : A (z, ν) = 0 := intra_block_vanishes hdvd A hc hP z ν hzν
  have hkill' : A (periodicLatticeShift z μ, ν) = 0 := by
    refine intra_block_vanishes hdvd A hc hP _ ν ?_
    rw [shiftNe z hne]; exact hzν
  rcases lt_trichotomy μ ν with h | h | h
  · have hrel := curl_rel hc z μ ν h
    rw [hkill, hkill'] at hrel
    have hd : A (z, μ) - A (periodicLatticeShift z ν, μ) = 0 := by rw [← hrel]; abel
    exact sub_eq_zero.1 hd
  · exact absurd h.symm hne
  · have hrel := curl_rel hc z ν μ h
    rw [hkill, hkill'] at hrel
    have hd : A (periodicLatticeShift z ν, μ) - A (z, μ) = 0 := by rw [← hrel]; abel
    exact (sub_eq_zero.1 hd).symm

/-- One transverse step, in the `addOff` bookkeeping. -/
theorem inter_step (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hc : closedFlat A) (hP : pAx A (CoarseLattice L 2) 2 = 0)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (e e' : Fin 3 → ℕ) (he : ∀ ν, e ν ≤ 1) (he' : ∀ ν, e' ν ≤ 1)
    (μ ν : Fin 3) (hne : ν ≠ μ) (hzero : e ν = 0) (hone : e' ν = e ν + 1)
    (hrest : ∀ ρ, ρ ≠ ν → e' ρ = e ρ) :
    A (addOff y e', μ) = A (addOff y e, μ) := by
  have hshift : periodicLatticeShift (addOff y e) ν = addOff y e' :=
    shift_addOff hdvd hy e e' ν he he' hone hrest
  have hpar : (addOff y e ν).val % 2 = 0 := by
    rw [addOff_parity hdvd hy he ν, hzero]
  have hstep := inter_block_shift hdvd A hc hP (addOff y e) μ ν hne hpar
  rw [hshift] at hstep
  exact hstep.symm

/-- **STAGE TWO.** Every inter-block bond in direction `μ` inside the block of the coarse centre
`y` equals the one based at `y + e_μ`. -/
theorem inter_block_const (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hc : closedFlat A) (hP : pAx A (CoarseLattice L 2) 2 = 0)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (e : Fin 3 → ℕ) (he : ∀ ν, e ν ≤ 1) (μ : Fin 3) (heμ : e μ = 1) :
    A (addOff y e, μ) = A (periodicLatticeShift y μ, μ) := by
  have S := fun (u v : Fin 3 → ℕ) (hu : ∀ ν, u ν ≤ 1) (hv : ∀ ν, v ν ≤ 1)
      (m n : Fin 3) (hne : n ≠ m) (h0 : u n = 0) (h1 : v n = u n + 1)
      (hr : ∀ ρ, ρ ≠ n → v ρ = u ρ) =>
    inter_step hdvd A hc hP hy u v hu hv m n hne h0 h1 hr
  have hb0 : e 0 ≤ 1 := he 0
  have hb1 : e 1 ≤ 1 := he 1
  have hb2 : e 2 ≤ 1 := he 2
  have hsplit : e = off3 (e 0) (e 1) (e 2) := eq_off3 e
  rw [hsplit]
  rcases fin3_cases μ with rfl | rfl | rfl
  · rw [shift_eq_addOff0 hdvd hy, show e 0 = 1 from heμ]
    -- direction 0: reduce the transverse offsets `(s,t)` to `(0,0)`
    have k11 : A (addOff y (off3 1 1 1), 0) = A (addOff y (off3 1 1 0), 0) :=
      S (off3 1 1 0) (off3 1 1 1) (by decide) (by decide) 0 2
        (by decide) (by decide) (by decide) (by decide)
    have k01 : A (addOff y (off3 1 0 1), 0) = A (addOff y (off3 1 0 0), 0) :=
      S (off3 1 0 0) (off3 1 0 1) (by decide) (by decide) 0 2
        (by decide) (by decide) (by decide) (by decide)
    have k10 : A (addOff y (off3 1 1 0), 0) = A (addOff y (off3 1 0 0), 0) :=
      S (off3 1 0 0) (off3 1 1 0) (by decide) (by decide) 0 1
        (by decide) (by decide) (by decide) (by decide)
    rcases (show e 1 = 0 ∨ e 1 = 1 by omega) with h1 | h1 <;>
      rcases (show e 2 = 0 ∨ e 2 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact k01
    · exact k10
    · exact k11.trans k10
  · rw [shift_eq_addOff1 hdvd hy, show e 1 = 1 from heμ]
    have k11 : A (addOff y (off3 1 1 1), 1) = A (addOff y (off3 1 1 0), 1) :=
      S (off3 1 1 0) (off3 1 1 1) (by decide) (by decide) 1 2
        (by decide) (by decide) (by decide) (by decide)
    have k01 : A (addOff y (off3 0 1 1), 1) = A (addOff y (off3 0 1 0), 1) :=
      S (off3 0 1 0) (off3 0 1 1) (by decide) (by decide) 1 2
        (by decide) (by decide) (by decide) (by decide)
    have k10 : A (addOff y (off3 1 1 0), 1) = A (addOff y (off3 0 1 0), 1) :=
      S (off3 0 1 0) (off3 1 1 0) (by decide) (by decide) 1 0
        (by decide) (by decide) (by decide) (by decide)
    rcases (show e 0 = 0 ∨ e 0 = 1 by omega) with h1 | h1 <;>
      rcases (show e 2 = 0 ∨ e 2 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact k01
    · exact k10
    · exact k11.trans k10
  · rw [shift_eq_addOff2 hdvd hy, show e 2 = 1 from heμ]
    have k11 : A (addOff y (off3 1 1 1), 2) = A (addOff y (off3 1 0 1), 2) :=
      S (off3 1 0 1) (off3 1 1 1) (by decide) (by decide) 2 1
        (by decide) (by decide) (by decide) (by decide)
    have k01 : A (addOff y (off3 0 1 1), 2) = A (addOff y (off3 0 0 1), 2) :=
      S (off3 0 0 1) (off3 0 1 1) (by decide) (by decide) 2 1
        (by decide) (by decide) (by decide) (by decide)
    have k10 : A (addOff y (off3 1 0 1), 2) = A (addOff y (off3 0 0 1), 2) :=
      S (off3 0 0 1) (off3 1 0 1) (by decide) (by decide) 2 0
        (by decide) (by decide) (by decide) (by decide)
    rcases (show e 0 = 0 ∨ e 0 = 1 by omega) with h1 | h1 <;>
      rcases (show e 1 = 0 ∨ e 1 = 1 by omega) with h2 | h2 <;> rw [h1, h2]
    · exact k01
    · exact k10
    · exact k11.trans k10

#print axioms inter_block_shift
#print axioms inter_step
#print axioms inter_block_const

/-! ## §4. STAGE THREE — `Q` kills the inter-block bonds -/

/-- `Q` at the flat background and block side `2`, in bare form: `ell⁻⁴` times the block sum of the
two-bond line integrals. `rZeroA_trivialU` is the tree's own reduction; nothing is redefined. -/
theorem lineCoarse_trivial_two (A : Bond L → SuTwo) (y : PeriodicLatticeSite L)
    (hyc : y ∈ CoarseLattice L 2) (μ : Fin 3) :
    lineCoarseRestrictCov (trivialU L) 2 A (⟨y, hyc⟩, μ)
      = (1 / ((2 : ℕ) : ℝ) ^ 4)
        • ∑ x ∈ blockOf y 2, (A (x, μ) + A (periodicLatticeShift x μ, μ)) := by
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf y 2, rZeroA (trivialU L) y x A μ 2 = _
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [rZeroA_trivialU]
  have p0 : pathSite x μ 0 = x := rfl
  have p1 : pathSite x μ 1 = periodicLatticeShift x μ := rfl
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, zero_add]

/-- **STAGE THREE.** With §2 and §3 in hand, `Q A = 0` forces the block's inter-block bond to
vanish: each of the `|B(y)|` summands of `2⁴·Q_μ(y)` contributes exactly one surviving bond, and
they are all the same one. -/
theorem Q_kills_inter_block (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hc : closedFlat A) (hP : pAx A (CoarseLattice L 2) 2 = 0)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    {y : PeriodicLatticeSite L} (hyc : y ∈ CoarseLattice L 2) (μ : Fin 3) :
    A (periodicLatticeShift y μ, μ) = 0 := by
  have hy : ∀ ν : Fin 3, (y ν).val % 2 = 0 := mem_CoarseLattice.1 hyc
  have h := hQ (⟨y, hyc⟩, μ)
  rw [lineCoarse_trivial_two A y hyc μ] at h
  have hsum : (∑ x ∈ blockOf y 2, (A (x, μ) + A (periodicLatticeShift x μ, μ))) = 0 := by
    rcases smul_eq_zero.1 h with hc0 | hs
    · exact absurd hc0 (by norm_num)
    · exact hs
  -- every summand is the SAME bond value
  have hterm : ∀ x ∈ blockOf y 2,
      A (x, μ) + A (periodicLatticeShift x μ, μ) = A (periodicLatticeShift y μ, μ) := by
    intro x hx
    obtain ⟨hxe, hle⟩ := mem_block_offset hx
    set e : Fin 3 → ℕ := fun ν => (x ν).val - (y ν).val with hedef
    have hpar : (x μ).val % 2 = e μ % 2 := by
      rw [hxe]; exact addOff_parity hdvd hy hle μ
    set e' : Fin 3 → ℕ := fun ν => if ν = μ then 1 else e ν with he'def
    have hemu : e μ = (x μ).val - (y μ).val := rfl
    rcases (show e μ = 0 ∨ e μ = 1 by rw [hemu]; have := hle μ; omega) with h0 | h1
    · -- the bond at `x` is intra-block; the shifted one is the block's inter-block bond
      have hA : A (x, μ) = 0 := by
        refine intra_block_vanishes hdvd A hc hP x μ ?_
        rw [hpar, h0]
      have hsh : periodicLatticeShift x μ = addOff y e' := by
        rw [hxe]
        refine shift_addOff hdvd hy e e' μ hle (fun ν => ?_) ?_ (fun ν hν => ?_)
        · simp only [he'def]; split_ifs with hh
          · omega
          · exact hle ν
        · simp only [he'def, if_pos rfl, h0]
        · simp only [he'def, if_neg hν]
      rw [hA, zero_add, hsh]
      exact inter_block_const hdvd A hc hP hy e' (fun ν => by
        simp only [he'def]; split_ifs with hh
        · omega
        · exact hle ν) μ (by simp only [he'def, if_pos rfl])
    · -- the bond at `x` IS the inter-block bond; the shifted one is intra-block
      have hA : A (x, μ) = A (periodicLatticeShift y μ, μ) := by
        rw [hxe]
        exact inter_block_const hdvd A hc hP hy e hle μ h1
      have hA' : A (periodicLatticeShift x μ, μ) = 0 := by
        refine intra_block_vanishes hdvd A hc hP _ μ ?_
        rw [shift_parity hdvd x μ]
        have hp := hpar
        have hq := h1
        omega
      rw [hA, hA', add_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const] at hsum
  have hcard : (blockOf y 2).card ≠ 0 := by
    refine Finset.card_ne_zero_of_mem (a := y) (mem_blockOf.2 (fun ν => ?_))
    omega
  have hcast : (((blockOf y 2).card : ℝ)) • A (periodicLatticeShift y μ, μ) = 0 := by
    rw [Nat.cast_smul_eq_nsmul ℝ]
    exact hsum
  rcases smul_eq_zero.1 hcast with hz | hz
  · exact absurd (Nat.cast_eq_zero.1 hz) hcard
  · exact hz

#print axioms lineCoarse_trivial_two
#print axioms Q_kills_inter_block

/-! ## §5. THE THEOREM -/

/-- **THE TRIPLE KERNEL IS ZERO.** At every periodic extent with `2 ∣ (L μ + 1)`, at block side
`ell = 2` and the flat background, a bond field that is
* CLOSED (`closedFlat`: the fine curl vanishes on every plaquette),
* COARSE-AVERAGE-FREE (`Q A = 0` at every coarse bond, `Q` being the tree's own
  `lineCoarseRestrictCov`), and
* AXIAL-GAUGE-FIXED (`pAx A = 0`, equivalently CMP95 `(1.10)`'s `A(Γ_{y,x}) = 0` for every coarse
  `y` and every `x ∈ B(y)`)

is IDENTICALLY ZERO. This is the qualitative half of CMP95 printed p.19's unproved positivity
claim, at a single level. -/
theorem triple_kernel_trivial (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hc : closedFlat A)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    (hP : pAx A (CoarseLattice L 2) 2 = 0) :
    A = fun _ => 0 := by
  funext b
  obtain ⟨z, μ⟩ := b
  by_cases hz : (z μ).val % 2 = 0
  · exact intra_block_vanishes hdvd A hc hP z μ hz
  · have hz1 : (z μ).val % 2 = 1 := by omega
    set y := cc z with hydef
    have hy : ∀ ν : Fin 3, (y ν).val % 2 = 0 := fun ν => cc_even z ν
    have hyc : y ∈ CoarseLattice L 2 := cc_mem z
    set e : Fin 3 → ℕ := fun ν => (z ν).val % 2 with hedef
    have hze : z = addOff y e := by
      refine addOff_of_val y z e (fun ν => ?_)
      show (z ν).val = (cc z ν).val + (z ν).val % 2
      rw [cc_val]; omega
    have hle : ∀ ν, e ν ≤ 1 := fun ν => by simp only [hedef]; omega
    rw [hze]
    rw [inter_block_const hdvd A hc hP hy e hle μ (by simp only [hedef]; exact hz1)]
    exact Q_kills_inter_block hdvd A hc hP hQ hyc μ

/-- The same statement in "the three conditions have only `0` in common" form. -/
theorem triple_kernel_eq_zero (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (h : closedFlat A
      ∧ (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
          lineCoarseRestrictCov (trivialU L) 2 A b = 0)
      ∧ pAx A (CoarseLattice L 2) 2 = 0) :
    ∀ b : Bond L, A b = 0 :=
  fun b => congrFun (triple_kernel_trivial hdvd A h.1 h.2.1 h.2.2) b

#print axioms triple_kernel_trivial
#print axioms triple_kernel_eq_zero

/-! ## §5b. EACH CLAUSE IS LOAD-BEARING — three witnesses, each nonzero, each missing one clause

The theorem would be worthless if one of its three hypotheses already implied the conclusion. This
section exhibits, at every extent with `2 ∣ (L μ + 1)` and for every nonzero `w : 𝔰𝔲(2)`, three
fields that are PROVED NONZERO and satisfy exactly two of the three clauses each. -/

section Controls

theorem d10 : (1 : Fin 3) ≠ 0 := by decide
theorem d20 : (2 : Fin 3) ≠ 0 := by decide
theorem d01 : (0 : Fin 3) ≠ 1 := by decide
theorem d21 : (2 : Fin 3) ≠ 1 := by decide

/-- The all-`0` site. Built from a raw `Fin` literal so `(zeroSite μ).val = 0` is `rfl`. -/
def zeroSite (L : PeriodicLatticeExtent) : PeriodicLatticeSite L := fun _ => ⟨0, Nat.succ_pos _⟩

theorem zeroSite_val (μ : Fin 3) : ((zeroSite L) μ).val = 0 := rfl

theorem zeroSite_coarse : (zeroSite L) ∈ CoarseLattice L 2 :=
  mem_CoarseLattice.2 (fun _ => rfl)

theorem zeroSite_even (μ : Fin 3) : ((zeroSite L) μ).val % 2 = 0 := rfl

/-- The `±1` alternation in coordinate `0`. -/
def par (z : PeriodicLatticeSite L) : ℝ := if (z 0).val % 2 = 0 then 1 else -1

theorem par_ne (z : PeriodicLatticeSite L) {ν : Fin 3} (h : ν ≠ 0) :
    par (periodicLatticeShift z ν) = par z := by
  unfold par
  rw [shiftNe z (Ne.symm h)]

theorem par_shift0 (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (z : PeriodicLatticeSite L) :
    par (periodicLatticeShift z 0) = -par z := by
  unfold par
  rw [shift_parity hdvd z 0]
  rcases (show (z 0).val % 2 = 0 ∨ (z 0).val % 2 = 1 by omega) with h | h
  · rw [if_neg (by omega : ¬(((z 0).val + 1) % 2 = 0)), if_pos h]
  · rw [if_pos (by omega : ((z 0).val + 1) % 2 = 0), if_neg (by omega : ¬((z 0).val % 2 = 0))]
    norm_num

/-- **CONTROL 1** — the closed, coarse-average-free ALTERNATING mode. The general-extent form of
`BridgeRestricted.altC` paired with a fibre vector. Only `P_Ax` sees it. -/
noncomputable def altMode (w : SuTwo) : Bond L → SuTwo :=
  fun b => if b.2 = 0 then (par b.1) • w else 0

theorem altMode_ne (w : SuTwo) {b : Bond L} (h : b.2 ≠ 0) : altMode w b = 0 := if_neg h

theorem altMode_eq (w : SuTwo) {b : Bond L} (h : b.2 = 0) : altMode w b = (par b.1) • w := if_pos h

/-- **CONTROL 2** — the closed, gauge-fixed BLOCK-GRADIENT mode. The general-extent form of
`AxialCoercivity.blockC`. Only `Q` sees it. -/
noncomputable def blockMode (w : SuTwo) : Bond L → SuTwo :=
  fun b => if b.2 = 0 ∧ (b.1 0).val % 2 = 1 then w else 0

theorem blockMode_ne (w : SuTwo) {b : Bond L} (h : b.2 ≠ 0) : blockMode w b = 0 :=
  if_neg (fun hh => h hh.1)

theorem blockMode_even (w : SuTwo) {b : Bond L} (h : (b.1 0).val % 2 = 0) : blockMode w b = 0 :=
  if_neg (fun hh => by omega)

theorem blockMode_odd (w : SuTwo) {b : Bond L} (h0 : b.2 = 0) (h : (b.1 0).val % 2 = 1) :
    blockMode w b = w := if_pos ⟨h0, h⟩

/-- The `±1` alternation in coordinate `1`. -/
def par1 (z : PeriodicLatticeSite L) : ℝ := if (z 1).val % 2 = 0 then 1 else -1

theorem par1_shift1 (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (z : PeriodicLatticeSite L) :
    par1 (periodicLatticeShift z 1) = -par1 z := by
  unfold par1
  rw [shift_parity hdvd z 1]
  rcases (show (z 1).val % 2 = 0 ∨ (z 1).val % 2 = 1 by omega) with h | h
  · rw [if_neg (by omega : ¬(((z 1).val + 1) % 2 = 0)), if_pos h]
  · rw [if_pos (by omega : ((z 1).val + 1) % 2 = 0), if_neg (by omega : ¬((z 1).val % 2 = 0))]
    norm_num

/-- **CONTROL 3** — the gauge-fixed, coarse-average-free ODD-SLICE TRANSVERSE mode. Direction `1`,
alternating in `x₁`, supported on the ODD coordinate-`0` slices — exactly the region
`AxialCoercivity.pAx_eq_zero_of_support_off_coarse` proves `(1.10)` is blind to. It is NOT closed,
which is what shows the curl clause is not redundant. New in this module. -/
noncomputable def oddAltMode (w : SuTwo) : Bond L → SuTwo :=
  fun b => if b.2 = 1 ∧ (b.1 0).val % 2 = 1 then (par1 b.1) • w else 0

theorem oddAltMode_ne (w : SuTwo) {b : Bond L} (h : b.2 ≠ 1) : oddAltMode w b = 0 :=
  if_neg (fun hh => h hh.1)

theorem oddAltMode_even (w : SuTwo) {b : Bond L} (h : (b.1 0).val % 2 = 0) :
    oddAltMode w b = 0 := if_neg (fun hh => by omega)

theorem oddAltMode_eq (w : SuTwo) {b : Bond L} (h1 : b.2 = 1) (h : (b.1 0).val % 2 = 1) :
    oddAltMode w b = (par1 b.1) • w := if_pos ⟨h1, h⟩

/-! ### Control 1: `altMode` is closed, `Q`-free, and `P_Ax`-VISIBLE -/

theorem altMode_closed (w : SuTwo) : closedFlat (altMode (L := L) w) := by
  rintro ⟨z, d⟩
  show altMode w (z, d.1.1) + altMode w (periodicLatticeShift z d.1.1, d.1.2)
      - altMode w (periodicLatticeShift z d.1.2, d.1.1) - altMode w (z, d.1.2) = 0
  rcases plaq_dirs d with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · rw [altMode_ne w (b := ((periodicLatticeShift z 0, (1 : Fin 3)) : Bond L)) d10,
      altMode_ne w (b := ((z, (1 : Fin 3)) : Bond L)) d10,
      altMode_eq w (b := ((z, (0 : Fin 3)) : Bond L)) rfl,
      altMode_eq w (b := ((periodicLatticeShift z 1, (0 : Fin 3)) : Bond L)) rfl,
      par_ne z d10]
    abel
  · rw [altMode_ne w (b := ((periodicLatticeShift z 0, (2 : Fin 3)) : Bond L)) d20,
      altMode_ne w (b := ((z, (2 : Fin 3)) : Bond L)) d20,
      altMode_eq w (b := ((z, (0 : Fin 3)) : Bond L)) rfl,
      altMode_eq w (b := ((periodicLatticeShift z 2, (0 : Fin 3)) : Bond L)) rfl,
      par_ne z d20]
    abel
  · rw [altMode_ne w (b := ((z, (1 : Fin 3)) : Bond L)) d10,
      altMode_ne w (b := ((periodicLatticeShift z 1, (2 : Fin 3)) : Bond L)) d20,
      altMode_ne w (b := ((periodicLatticeShift z 2, (1 : Fin 3)) : Bond L)) d10,
      altMode_ne w (b := ((z, (2 : Fin 3)) : Bond L)) d20]
    abel

theorem altMode_Q (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo)
    (b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2) :
    lineCoarseRestrictCov (trivialU L) 2 (altMode w) b = 0 := by
  obtain ⟨⟨y, hyc⟩, μ⟩ := b
  rw [lineCoarse_trivial_two (altMode w) y hyc μ]
  have hz : (∑ x ∈ blockOf y 2,
      (altMode w (x, μ) + altMode w (periodicLatticeShift x μ, μ))) = 0 := by
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hμ : μ = 0
    · subst hμ
      rw [altMode_eq w (b := ((x, (0 : Fin 3)) : Bond L)) rfl,
        altMode_eq w (b := ((periodicLatticeShift x 0, (0 : Fin 3)) : Bond L)) rfl,
        par_shift0 hdvd x, neg_smul]
      abel
    · rw [altMode_ne w (b := ((x, μ) : Bond L)) hμ,
        altMode_ne w (b := ((periodicLatticeShift x μ, μ) : Bond L)) hμ]
      abel
  rw [hz, smul_zero]

theorem altMode_pAx_ne (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo) (hw : w ≠ 0) :
    pAx (altMode (L := L) w) (CoarseLattice L 2) 2 ≠ 0 := by
  intro hcon
  have hy : ∀ μ : Fin 3, ((zeroSite L) μ).val % 2 = 0 := fun μ => zeroSite_even μ
  have hx : addOff (zeroSite L) (off3 1 0 0) ∈ (blockOf (zeroSite L) 2).erase (zeroSite L) := by
    refine Finset.mem_erase.2 ⟨?_, mem_blockOf_addOff hdvd hy (by decide)⟩
    intro hcon2
    have hv := congrArg (fun z : PeriodicLatticeSite L => (z 0).val) hcon2
    rw [addOff_val (zeroSite L) (off3 1 0 0) 0 (by rw [zeroSite_val]; exact coarse_room hdvd hy 0)]
      at hv
    simp only [zeroSite_val, off3_zero] at hv
    omega
  have hI := (pAx_eq_zero_iff (altMode (L := L) w) (CoarseLattice L 2) 2).1 hcon
    (zeroSite L) zeroSite_coarse _ hx
  rw [pathIntegral_off3 hdvd (altMode (L := L) w) hy 1 0 0 (by omega) (by omega) (by omega)] at hI
  rw [addOff_zero] at hI
  norm_num at hI
  rw [altMode_eq w (b := (((zeroSite L), (0 : Fin 3)) : Bond L)) rfl] at hI
  have hpar : par (zeroSite L) = 1 := by unfold par; rw [if_pos (zeroSite_even 0)]
  rw [hpar, one_smul] at hI
  exact hw hI

theorem altMode_field_ne (w : SuTwo) (hw : w ≠ 0) : altMode (L := L) w ≠ fun _ => 0 := by
  intro hcon
  have h := congrFun hcon ((zeroSite L), (0 : Fin 3))
  rw [altMode_eq w (b := (((zeroSite L), (0 : Fin 3)) : Bond L)) rfl] at h
  have hpar : par (zeroSite L) = 1 := by unfold par; rw [if_pos (zeroSite_even 0)]
  rw [hpar, one_smul] at h
  exact hw h

/-! ### Control 2: `blockMode` is closed, `P_Ax`-free, and `Q`-VISIBLE -/

theorem blockMode_closed (w : SuTwo) : closedFlat (blockMode (L := L) w) := by
  rintro ⟨z, d⟩
  show blockMode w (z, d.1.1) + blockMode w (periodicLatticeShift z d.1.1, d.1.2)
      - blockMode w (periodicLatticeShift z d.1.2, d.1.1) - blockMode w (z, d.1.2) = 0
  have key : ∀ ν : Fin 3, ν ≠ 0 →
      blockMode (L := L) w (z, (0 : Fin 3))
        - blockMode (L := L) w (periodicLatticeShift z ν, (0 : Fin 3)) = 0 := by
    intro ν hν
    have hcoord : ((periodicLatticeShift z ν) 0).val = (z 0).val := by
      rw [shiftNe z (Ne.symm hν)]
    by_cases hp : (z 0).val % 2 = 1
    · rw [blockMode_odd w (b := ((z, (0 : Fin 3)) : Bond L)) rfl hp,
        blockMode_odd w (b := ((periodicLatticeShift z ν, (0 : Fin 3)) : Bond L)) rfl
          (by show ((periodicLatticeShift z ν) 0).val % 2 = 1; rw [hcoord]; exact hp)]
      abel
    · rw [blockMode_even w (b := ((z, (0 : Fin 3)) : Bond L))
          (by show (z 0).val % 2 = 0; omega),
        blockMode_even w (b := ((periodicLatticeShift z ν, (0 : Fin 3)) : Bond L))
          (by show ((periodicLatticeShift z ν) 0).val % 2 = 0; rw [hcoord]; omega)]
      abel
  rcases plaq_dirs d with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · rw [blockMode_ne w (b := ((periodicLatticeShift z 0, (1 : Fin 3)) : Bond L)) d10,
      blockMode_ne w (b := ((z, (1 : Fin 3)) : Bond L)) d10, add_zero, sub_zero]
    exact key 1 d10
  · rw [blockMode_ne w (b := ((periodicLatticeShift z 0, (2 : Fin 3)) : Bond L)) d20,
      blockMode_ne w (b := ((z, (2 : Fin 3)) : Bond L)) d20, add_zero, sub_zero]
    exact key 2 d20
  · rw [blockMode_ne w (b := ((z, (1 : Fin 3)) : Bond L)) d10,
      blockMode_ne w (b := ((periodicLatticeShift z 1, (2 : Fin 3)) : Bond L)) d20,
      blockMode_ne w (b := ((periodicLatticeShift z 2, (1 : Fin 3)) : Bond L)) d10,
      blockMode_ne w (b := ((z, (2 : Fin 3)) : Bond L)) d20]
    abel

theorem blockMode_pAx (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo) :
    pAx (blockMode (L := L) w) (CoarseLattice L 2) 2 = 0 := by
  rw [pAx_eq_zero_iff]
  intro y hyc x hx
  have hy : ∀ μ : Fin 3, (y μ).val % 2 = 0 := mem_CoarseLattice.1 hyc
  obtain ⟨hxe, hle⟩ := mem_block_offset (Finset.mem_erase.1 hx).2
  rw [hxe, eq_off3 (fun ν => (x ν).val - (y ν).val),
    pathIntegral_off3 hdvd (blockMode (L := L) w) hy _ _ _ (hle 0) (hle 1) (hle 2),
    blockMode_ne w (b := ((y, (2 : Fin 3)) : Bond L)) d20,
    blockMode_ne w (b := ((addOff y (off3 0 0 ((x 2).val - (y 2).val)), (1 : Fin 3)) : Bond L)) d10,
    blockMode_even w (b := ((addOff y (off3 0 ((x 1).val - (y 1).val)
        ((x 2).val - (y 2).val)), (0 : Fin 3)) : Bond L))
      (by
        show (addOff y (off3 0 ((x 1).val - (y 1).val) ((x 2).val - (y 2).val)) 0).val % 2 = 0
        rw [addOff_parity hdvd hy (off3_le 0 _ _ (by omega) (hle 1) (hle 2)) 0, off3_zero])]
  simp

theorem blockMode_Q_ne (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo) (hw : w ≠ 0) :
    ¬ (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
        lineCoarseRestrictCov (trivialU L) 2 (blockMode w) b = 0) := by
  intro hcon
  have h := hcon (⟨zeroSite L, zeroSite_coarse⟩, 0)
  rw [lineCoarse_trivial_two (blockMode w) (zeroSite L) zeroSite_coarse 0] at h
  have hterm : ∀ x ∈ blockOf (zeroSite L) 2,
      blockMode (L := L) w (x, 0) + blockMode (L := L) w (periodicLatticeShift x 0, 0) = w := by
    intro x _
    have hsh := shift_parity hdvd x 0
    by_cases hp : (x 0).val % 2 = 1
    · rw [blockMode_odd w (b := ((x, (0 : Fin 3)) : Bond L)) rfl hp,
        blockMode_even w (b := ((periodicLatticeShift x 0, (0 : Fin 3)) : Bond L))
          (by show ((periodicLatticeShift x 0) 0).val % 2 = 0; rw [hsh]; omega)]
      abel
    · rw [blockMode_even w (b := ((x, (0 : Fin 3)) : Bond L))
          (by show (x 0).val % 2 = 0; omega),
        blockMode_odd w (b := ((periodicLatticeShift x 0, (0 : Fin 3)) : Bond L)) rfl
          (by show ((periodicLatticeShift x 0) 0).val % 2 = 1; rw [hsh]; omega)]
      abel
  rw [Finset.sum_congr rfl hterm, Finset.sum_const] at h
  have hcard : (blockOf (zeroSite L) 2).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (a := zeroSite L) (mem_blockOf.2 (fun ν => by omega))
  have hcast : ((1 / ((2 : ℕ) : ℝ) ^ 4) * (((blockOf (zeroSite L) 2).card : ℝ))) • w = 0 := by
    rw [mul_smul, Nat.cast_smul_eq_nsmul ℝ]
    exact h
  rcases smul_eq_zero.1 hcast with hz | hz
  · rcases mul_eq_zero.1 hz with h1 | h1
    · norm_num at h1
    · exact hcard (Nat.cast_eq_zero.1 h1)
  · exact hw hz

theorem blockMode_field_ne (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo) (hw : w ≠ 0) :
    blockMode (L := L) w ≠ fun _ => 0 := by
  intro hcon
  have hodd : ((periodicLatticeShift (zeroSite L) 0) 0).val % 2 = 1 := by
    rw [shift_parity hdvd (zeroSite L) 0, zeroSite_val]
  have h := congrFun hcon ((periodicLatticeShift (zeroSite L) 0), (0 : Fin 3))
  rw [blockMode_odd w (b := ((periodicLatticeShift (zeroSite L) 0, (0 : Fin 3)) : Bond L))
    rfl hodd] at h
  exact hw h

/-! ### Control 3: `oddAltMode` is `P_Ax`-free, `Q`-free, and NOT CLOSED -/

theorem oddAltMode_pAx (w : SuTwo) :
    pAx (oddAltMode (L := L) w) (CoarseLattice L 2) 2 = 0 := by
  refine pAx_eq_zero_of_support_off_coarse (oddAltMode (L := L) w) 2 (fun b hb => ?_)
  by_cases hcase : b.2 = 1 ∧ (b.1 0).val % 2 = 1
  · exact ⟨by rw [hcase.1]; exact d10, by rw [hcase.2]; omega⟩
  · exact absurd (if_neg hcase) hb

theorem oddAltMode_Q (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo)
    (b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2) :
    lineCoarseRestrictCov (trivialU L) 2 (oddAltMode w) b = 0 := by
  obtain ⟨⟨y, hyc⟩, μ⟩ := b
  rw [lineCoarse_trivial_two (oddAltMode w) y hyc μ]
  have hz : (∑ x ∈ blockOf y 2,
      (oddAltMode w (x, μ) + oddAltMode w (periodicLatticeShift x μ, μ))) = 0 := by
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hμ : μ = 1
    · subst hμ
      have hcoord : ((periodicLatticeShift x 1) 0).val = (x 0).val := by
        rw [shiftNe x d01]
      by_cases hp : (x 0).val % 2 = 1
      · rw [oddAltMode_eq w (b := ((x, (1 : Fin 3)) : Bond L)) rfl hp,
          oddAltMode_eq w (b := ((periodicLatticeShift x 1, (1 : Fin 3)) : Bond L)) rfl
            (by show ((periodicLatticeShift x 1) 0).val % 2 = 1; rw [hcoord]; exact hp),
          par1_shift1 hdvd x, neg_smul]
        abel
      · rw [oddAltMode_even w (b := ((x, (1 : Fin 3)) : Bond L))
            (by show (x 0).val % 2 = 0; omega),
          oddAltMode_even w (b := ((periodicLatticeShift x 1, (1 : Fin 3)) : Bond L))
            (by show ((periodicLatticeShift x 1) 0).val % 2 = 0; rw [hcoord]; omega)]
        abel
    · rw [oddAltMode_ne w (b := ((x, μ) : Bond L)) hμ,
        oddAltMode_ne w (b := ((periodicLatticeShift x μ, μ) : Bond L)) hμ]
      abel
  rw [hz, smul_zero]

theorem oddAltMode_not_closed (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo) (hw : w ≠ 0) :
    ¬ closedFlat (oddAltMode (L := L) w) := by
  intro hcon
  have hodd : ((periodicLatticeShift (zeroSite L) 0) 0).val % 2 = 1 := by
    rw [shift_parity hdvd (zeroSite L) 0, zeroSite_val]
  have hpar1 : par1 (periodicLatticeShift (zeroSite L) (0 : Fin 3)) = 1 := by
    unfold par1
    rw [if_pos (show ((periodicLatticeShift (zeroSite L) 0) 1).val % 2 = 0 by
      rw [shiftNe (zeroSite L) d10, zeroSite_val])]
  have hexp : oddAltMode (L := L) w ((zeroSite L), (0 : Fin 3))
      + oddAltMode (L := L) w (periodicLatticeShift (zeroSite L) 0, (1 : Fin 3))
      - oddAltMode (L := L) w (periodicLatticeShift (zeroSite L) 1, (0 : Fin 3))
      - oddAltMode (L := L) w ((zeroSite L), (1 : Fin 3)) = 0 :=
    hcon ((zeroSite L), ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩)
  rw [oddAltMode_ne w (b := (((zeroSite L), (0 : Fin 3)) : Bond L)) d01,
    oddAltMode_ne w (b := ((periodicLatticeShift (zeroSite L) 1, (0 : Fin 3)) : Bond L)) d01,
    oddAltMode_even w (b := (((zeroSite L), (1 : Fin 3)) : Bond L)) (zeroSite_even 0),
    oddAltMode_eq w (b := ((periodicLatticeShift (zeroSite L) 0, (1 : Fin 3)) : Bond L)) rfl hodd,
    hpar1, one_smul] at hexp
  simp only [zero_add, sub_zero] at hexp
  exact hw hexp

theorem oddAltMode_field_ne (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo) (hw : w ≠ 0) :
    oddAltMode (L := L) w ≠ fun _ => 0 := by
  intro hcon
  have hodd : ((periodicLatticeShift (zeroSite L) 0) 0).val % 2 = 1 := by
    rw [shift_parity hdvd (zeroSite L) 0, zeroSite_val]
  have hpar1 : par1 (periodicLatticeShift (zeroSite L) (0 : Fin 3)) = 1 := by
    unfold par1
    rw [if_pos (show ((periodicLatticeShift (zeroSite L) 0) 1).val % 2 = 0 by
      rw [shiftNe (zeroSite L) d10, zeroSite_val])]
  have h := congrFun hcon ((periodicLatticeShift (zeroSite L) 0), (1 : Fin 3))
  rw [oddAltMode_eq w (b := ((periodicLatticeShift (zeroSite L) 0, (1 : Fin 3)) : Bond L))
    rfl hodd, hpar1, one_smul] at h
  exact hw h

/-- **NO CLAUSE OF `triple_kernel_trivial` CAN BE DROPPED.** For every nonzero `w : 𝔰𝔲(2)` and
every extent with `2 ∣ (L μ + 1)`, the three exhibited fields are nonzero and each satisfies
exactly two of the three hypotheses. -/
theorem clauses_are_load_bearing (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo)
    (hw : w ≠ 0) :
    ((altMode (L := L) w ≠ fun _ => 0) ∧ closedFlat (altMode (L := L) w)
        ∧ (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
            lineCoarseRestrictCov (trivialU L) 2 (altMode w) b = 0)
        ∧ pAx (altMode (L := L) w) (CoarseLattice L 2) 2 ≠ 0)
      ∧ ((blockMode (L := L) w ≠ fun _ => 0) ∧ closedFlat (blockMode (L := L) w)
        ∧ pAx (blockMode (L := L) w) (CoarseLattice L 2) 2 = 0
        ∧ ¬ (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
            lineCoarseRestrictCov (trivialU L) 2 (blockMode w) b = 0))
      ∧ ((oddAltMode (L := L) w ≠ fun _ => 0)
        ∧ (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
            lineCoarseRestrictCov (trivialU L) 2 (oddAltMode w) b = 0)
        ∧ pAx (oddAltMode (L := L) w) (CoarseLattice L 2) 2 = 0
        ∧ ¬ closedFlat (oddAltMode (L := L) w)) :=
  ⟨⟨altMode_field_ne w hw, altMode_closed w, altMode_Q hdvd w, altMode_pAx_ne hdvd w hw⟩,
   ⟨blockMode_field_ne hdvd w hw, blockMode_closed w, blockMode_pAx hdvd w,
     blockMode_Q_ne hdvd w hw⟩,
   ⟨oddAltMode_field_ne hdvd w hw, oddAltMode_Q hdvd w, oddAltMode_pAx w,
     oddAltMode_not_closed hdvd w hw⟩⟩

/-- The controls are NOT VACUOUS: `𝔰𝔲(2)` has a nonzero element, so `clauses_are_load_bearing`
fires at a genuine `w`. `rotGen` is the tree's own witness (`BridgeRestricted`), reused. -/
theorem clauses_are_load_bearing_at_rotGen (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    (AdalyFormal.Balaban.BridgeRestricted.rotGen ≠ 0)
      ∧ ((altMode (L := L) AdalyFormal.Balaban.BridgeRestricted.rotGen ≠ fun _ => 0)
        ∧ closedFlat (altMode (L := L) AdalyFormal.Balaban.BridgeRestricted.rotGen)
        ∧ pAx (altMode (L := L) AdalyFormal.Balaban.BridgeRestricted.rotGen)
            (CoarseLattice L 2) 2 ≠ 0) :=
  ⟨AdalyFormal.Balaban.BridgeRestricted.rotGen_ne_zero,
    altMode_field_ne _ AdalyFormal.Balaban.BridgeRestricted.rotGen_ne_zero,
    altMode_closed _,
    altMode_pAx_ne hdvd _ AdalyFormal.Balaban.BridgeRestricted.rotGen_ne_zero⟩

end Controls

#print axioms zeroSite
#print axioms par
#print axioms altMode
#print axioms blockMode
#print axioms oddAltMode
#print axioms altMode_closed
#print axioms altMode_Q
#print axioms altMode_pAx_ne
#print axioms altMode_field_ne
#print axioms blockMode_closed
#print axioms blockMode_pAx
#print axioms blockMode_Q_ne
#print axioms blockMode_field_ne
#print axioms oddAltMode_pAx
#print axioms oddAltMode_Q
#print axioms oddAltMode_not_closed
#print axioms oddAltMode_field_ne
#print axioms clauses_are_load_bearing
#print axioms clauses_are_load_bearing_at_rotGen

/-! ## §5c. THE QUANTITATIVE HALF — every INTRA-BLOCK bond, with an explicit constant

§2 says the intra-block bonds VANISH when `pAx = 0` and the curl vanishes. This section is the
quantitative form of the same chain: with NOTHING assumed about `A`, every intra-block bond's energy
is bounded by the block's OWN gauge-fixing energy plus the curl energy, with an ABSOLUTE constant —
no volume factor, no dependence on `L`.

`352` is a counted constant, not a fitted one: it is what `sq_four` (`‖a+b+c+d‖² ≤ 4(…)`) produces
after the five-step nesting of §2, and the derivation of each intermediate bound is written out in
the proof. Both sides are homogeneous of degree `2` in `A`, so the statement is invariant under
`A ↦ tA` — rescaling cannot make it true or false. -/

section Quantitative

/-- The fine curl energy `∑_p ‖(dA)(p)‖²`. -/
noncomputable def curlEnergy (A : Bond L → SuTwo) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2

theorem curlEnergy_nonneg (A : Bond L → SuTwo) : 0 ≤ curlEnergy A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem norm_sq_flatCurl_le (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖flatCurlValue A p‖ ^ 2 ≤ curlEnergy A :=
  Finset.single_le_sum (f := fun q => ‖flatCurlValue A q‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ p)

theorem sq_two (a b : SuTwo) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a + b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem sq_four (a b c d : SuTwo) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h1 : a + b + c + d = (a + b) + (c + d) := by abel
  rw [h1]
  have h2 := sq_two (a + b) (c + d)
  have h3 := sq_two a b
  have h4 := sq_two c d
  linarith

/-- The curl identity solved for the `(shift z μ, ν)` bond. -/
theorem curl_solve (A : Bond L → SuTwo) (z : PeriodicLatticeSite L) (μ ν : Fin 3) (h : μ < ν) :
    A (periodicLatticeShift z μ, ν)
      = flatCurlValue A (z, ⟨(μ, ν), h⟩) + (-A (z, μ)) + A (periodicLatticeShift z ν, μ)
        + A (z, ν) := by
  have hc : flatCurlValue A (z, ⟨(μ, ν), h⟩)
      = A (z, μ) + A (periodicLatticeShift z μ, ν)
        - A (periodicLatticeShift z ν, μ) - A (z, ν) := rfl
  rw [hc]
  abel

/-- **THE QUANTITATIVE STAGE ONE.** For an ARBITRARY bond field (no closedness, no gauge condition,
no background), every bond with both endpoints in the side-`2` block `B(y)` of a coarse centre `y`
satisfies `‖A b‖² ≤ 352 · (P_Ax-energy of THAT block + total curl energy)`. -/
theorem intra_block_energy_bound (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (e : Fin 3 → ℕ) (he : ∀ ν, e ν ≤ 1) (μ : Fin 3) (heμ : e μ = 0) :
    ‖A (addOff y e, μ)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
  have hPy : (0 : ℝ) ≤ pAxBlock A 2 y := pAxBlock_nonneg A 2 y
  have hCc : (0 : ℝ) ≤ curlEnergy A := curlEnergy_nonneg A
  have hz0 : addOff y (off3 0 0 0) = y := addOff_zero y
  -- the seven contour integrals, each bounded by the block's own gauge-fixing energy
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
  -- b1 : A(y,2)
  have b1 : ‖A (addOff y (off3 0 0 0), 2)‖ ^ 2 ≤ pAxBlock A 2 y := by
    have h := E 0 0 1 (by omega) (by omega) (by omega)
    norm_num at h
    rw [hz0, ← h]
    exact hI 0 0 1 (by omega) (by omega) (by omega)
  -- b2 : A(y,1)
  have b2 : ‖A (addOff y (off3 0 0 0), 1)‖ ^ 2 ≤ pAxBlock A 2 y := by
    have h := E 0 1 0 (by omega) (by omega) (by omega)
    norm_num at h
    rw [← h]
    exact hI 0 1 0 (by omega) (by omega) (by omega)
  -- b4 : A(y,0)
  have b4 : ‖A (addOff y (off3 0 0 0), 0)‖ ^ 2 ≤ pAxBlock A 2 y := by
    have h := E 1 0 0 (by omega) (by omega) (by omega)
    norm_num at h
    rw [← h]
    exact hI 1 0 0 (by omega) (by omega) (by omega)
  -- b3 : A(y+e₂,1) = I(0,1,1) − A(y,2)
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
  -- b5 : A(y+e₁,0) = I(1,1,0) − A(y,1)
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
  -- b6 : A(y+e₂,0) = I(1,0,1) − A(y,2)
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
  -- b7 : A(y+e₁+e₂,0) = I(1,1,1) − A(y,2) − A(y+e₂,1)
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
  -- the five plaquette-driven bonds
  have SH : ∀ (u v : Fin 3 → ℕ) (m : Fin 3), (∀ ν, u ν ≤ 1) → (∀ ν, v ν ≤ 1) →
      v m = u m + 1 → (∀ ν, ν ≠ m → v ν = u ν) →
      periodicLatticeShift (addOff y u) m = addOff y v :=
    fun u v m hu hv h1 h2 => shift_addOff hdvd hy u v m hu hv h1 h2
  have n1 : ‖A (addOff y (off3 1 0 0), 1)‖ ^ 2
      ≤ 4 * (curlEnergy A + pAxBlock A 2 y + 8 * pAxBlock A 2 y + pAxBlock A 2 y) := by
    have hs := curl_solve A (addOff y (off3 0 0 0)) 0 1 (by decide)
    rw [SH (off3 0 0 0) (off3 1 0 0) 0 (by decide) (by decide) (by decide) (by decide),
      SH (off3 0 0 0) (off3 0 1 0) 1 (by decide) (by decide) (by decide) (by decide)] at hs
    have hb := sq_four (flatCurlValue A (addOff y (off3 0 0 0), ⟨((0 : Fin 3), (1 : Fin 3)),
        by decide⟩)) (-A (addOff y (off3 0 0 0), 0)) (A (addOff y (off3 0 1 0), 0))
      (A (addOff y (off3 0 0 0), 1))
    rw [← hs, norm_neg] at hb
    have hF := norm_sq_flatCurl_le A (addOff y (off3 0 0 0), ⟨((0 : Fin 3), (1 : Fin 3)),
      by decide⟩)
    nlinarith [hb, hF, b4, b5, b2]
  have n3 : ‖A (addOff y (off3 1 0 0), 2)‖ ^ 2
      ≤ 4 * (curlEnergy A + pAxBlock A 2 y + 8 * pAxBlock A 2 y + pAxBlock A 2 y) := by
    have hs := curl_solve A (addOff y (off3 0 0 0)) 0 2 (by decide)
    rw [SH (off3 0 0 0) (off3 1 0 0) 0 (by decide) (by decide) (by decide) (by decide),
      SH (off3 0 0 0) (off3 0 0 1) 2 (by decide) (by decide) (by decide) (by decide)] at hs
    have hb := sq_four (flatCurlValue A (addOff y (off3 0 0 0), ⟨((0 : Fin 3), (2 : Fin 3)),
        by decide⟩)) (-A (addOff y (off3 0 0 0), 0)) (A (addOff y (off3 0 0 1), 0))
      (A (addOff y (off3 0 0 0), 2))
    rw [← hs, norm_neg] at hb
    have hF := norm_sq_flatCurl_le A (addOff y (off3 0 0 0), ⟨((0 : Fin 3), (2 : Fin 3)),
      by decide⟩)
    nlinarith [hb, hF, b4, b6, b1]
  have n4 : ‖A (addOff y (off3 0 1 0), 2)‖ ^ 2
      ≤ 4 * (curlEnergy A + pAxBlock A 2 y + 8 * pAxBlock A 2 y + pAxBlock A 2 y) := by
    have hs := curl_solve A (addOff y (off3 0 0 0)) 1 2 (by decide)
    rw [SH (off3 0 0 0) (off3 0 1 0) 1 (by decide) (by decide) (by decide) (by decide),
      SH (off3 0 0 0) (off3 0 0 1) 2 (by decide) (by decide) (by decide) (by decide)] at hs
    have hb := sq_four (flatCurlValue A (addOff y (off3 0 0 0), ⟨((1 : Fin 3), (2 : Fin 3)),
        by decide⟩)) (-A (addOff y (off3 0 0 0), 1)) (A (addOff y (off3 0 0 1), 1))
      (A (addOff y (off3 0 0 0), 2))
    rw [← hs, norm_neg] at hb
    have hF := norm_sq_flatCurl_le A (addOff y (off3 0 0 0), ⟨((1 : Fin 3), (2 : Fin 3)),
      by decide⟩)
    nlinarith [hb, hF, b2, b3, b1]
  have n2 : ‖A (addOff y (off3 1 0 1), 1)‖ ^ 2
      ≤ 4 * (curlEnergy A + 8 * pAxBlock A 2 y + 40 * pAxBlock A 2 y + 8 * pAxBlock A 2 y) := by
    have hs := curl_solve A (addOff y (off3 0 0 1)) 0 1 (by decide)
    rw [SH (off3 0 0 1) (off3 1 0 1) 0 (by decide) (by decide) (by decide) (by decide),
      SH (off3 0 0 1) (off3 0 1 1) 1 (by decide) (by decide) (by decide) (by decide)] at hs
    have hb := sq_four (flatCurlValue A (addOff y (off3 0 0 1), ⟨((0 : Fin 3), (1 : Fin 3)),
        by decide⟩)) (-A (addOff y (off3 0 0 1), 0)) (A (addOff y (off3 0 1 1), 0))
      (A (addOff y (off3 0 0 1), 1))
    rw [← hs, norm_neg] at hb
    have hF := norm_sq_flatCurl_le A (addOff y (off3 0 0 1), ⟨((0 : Fin 3), (1 : Fin 3)),
      by decide⟩)
    nlinarith [hb, hF, b6, b7, b3]
  have n5 : ‖A (addOff y (off3 1 1 0), 2)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    have hs := curl_solve A (addOff y (off3 0 1 0)) 0 2 (by decide)
    rw [SH (off3 0 1 0) (off3 1 1 0) 0 (by decide) (by decide) (by decide) (by decide),
      SH (off3 0 1 0) (off3 0 1 1) 2 (by decide) (by decide) (by decide) (by decide)] at hs
    have hb := sq_four (flatCurlValue A (addOff y (off3 0 1 0), ⟨((0 : Fin 3), (2 : Fin 3)),
        by decide⟩)) (-A (addOff y (off3 0 1 0), 0)) (A (addOff y (off3 0 1 1), 0))
      (A (addOff y (off3 0 1 0), 2))
    rw [← hs, norm_neg] at hb
    have hF := norm_sq_flatCurl_le A (addOff y (off3 0 1 0), ⟨((0 : Fin 3), (2 : Fin 3)),
      by decide⟩)
    nlinarith [hb, hF, b5, b7, n4]
  -- weaken every bound to the uniform constant
  have hb1 : ‖A (addOff y (off3 0 0 0), 2)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    linarith
  have hb2 : ‖A (addOff y (off3 0 0 0), 1)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    linarith
  have hb3 : ‖A (addOff y (off3 0 0 1), 1)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    linarith
  have hb4 : ‖A (addOff y (off3 0 0 0), 0)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    linarith
  have hb5 : ‖A (addOff y (off3 0 1 0), 0)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    linarith
  have hb6 : ‖A (addOff y (off3 0 0 1), 0)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    linarith
  have hb7 : ‖A (addOff y (off3 0 1 1), 0)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    linarith
  have hn1 : ‖A (addOff y (off3 1 0 0), 1)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    linarith
  have hn2 : ‖A (addOff y (off3 1 0 1), 1)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    linarith
  have hn3 : ‖A (addOff y (off3 1 0 0), 2)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
    linarith
  have hn4 : ‖A (addOff y (off3 0 1 0), 2)‖ ^ 2 ≤ 352 * (pAxBlock A 2 y + curlEnergy A) := by
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

/-- **THE QUANTITATIVE STAGE ONE, POINTWISE.** Every bond whose direction-coordinate is even.
No hypothesis on `A` at all. -/
theorem intra_bond_energy_bound (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (z : PeriodicLatticeSite L) (μ : Fin 3) (hz : (z μ).val % 2 = 0) :
    ‖A (z, μ)‖ ^ 2 ≤ 352 * (pAxBlock A 2 (cc z) + curlEnergy A) := by
  have hy : ∀ ν : Fin 3, ((cc z) ν).val % 2 = 0 := fun ν => cc_even z ν
  have hze : z = addOff (cc z) (fun ν => (z ν).val % 2) := by
    refine addOff_of_val (cc z) z _ (fun ν => ?_)
    show (z ν).val = (cc z ν).val + (z ν).val % 2
    rw [cc_val]; omega
  have key := intra_block_energy_bound hdvd A hy (fun ν => (z ν).val % 2)
    (fun ν => by omega) μ hz
  rwa [← hze] at key

/-- The same with the GLOBAL gauge-fixing energy on the right (the form a consumer states). -/
theorem intra_bond_energy_bound_global (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo) (z : PeriodicLatticeSite L) (μ : Fin 3) (hz : (z μ).val % 2 = 0) :
    ‖A (z, μ)‖ ^ 2 ≤ 352 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
  have h1 := intra_bond_energy_bound hdvd A z μ hz
  have h2 : pAxBlock A 2 (cc z) ≤ pAx A (CoarseLattice L 2) 2 :=
    pAxBlock_le_pAx A (CoarseLattice L 2) 2 (cc_mem z)
  linarith

/-- **MUST-FIRE for the quantitative bound.** It is not a statement about zeros: at the alternating
mode, an intra-block bond carries `‖w‖² > 0` on the LEFT, so the inequality is constraining a
genuinely nonzero quantity. (`altMode`'s own contours have `pAx > 0`, `altMode_pAx_ne`.) -/
theorem intra_bond_energy_bound_nonvacuous (w : SuTwo) (hw : w ≠ 0) :
    0 < ‖altMode (L := L) w ((zeroSite L), (0 : Fin 3))‖ ^ 2 := by
  rw [altMode_eq w (b := (((zeroSite L), (0 : Fin 3)) : Bond L)) rfl]
  have hpar : par (zeroSite L) = 1 := by unfold par; rw [if_pos (zeroSite_even 0)]
  rw [hpar, one_smul]
  exact pow_pos (norm_pos_iff.2 hw) 2

/-- **RESCALE CONTROL.** Both sides of `intra_bond_energy_bound` are homogeneous of degree `2`, so
no choice of overall normalization of `A` can make the bound true or false: multiplying `A` by `t`
multiplies both sides by `t²`. Stated for `pAx`; `curlEnergy` and `‖A b‖²` scale the same way by
`flatCurlValue_smul` and `norm_smul`. -/
theorem quantitative_bound_is_homogeneous (A : Bond L → SuTwo) (t : ℝ) (b : Bond L)
    (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) :
    ‖(fun c => t • A c) b‖ ^ 2 = t ^ 2 * ‖A b‖ ^ 2
      ∧ curlEnergy (fun c => t • A c) = t ^ 2 * curlEnergy A
      ∧ pAx (fun c => t • A c) S ell = t ^ 2 * pAx A S ell := by
  refine ⟨?_, ?_, pAx_smul A S ell t⟩
  · show ‖t • A b‖ ^ 2 = _
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  · unfold curlEnergy
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hsm : flatCurlValue (fun c => t • A c) p = t • flatCurlValue A p := by
      have := flatCurlValue_smul (L := L) t A
      exact congrFun this p
    rw [hsm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]


/-! ### §5c.2 — the INTER-BLOCK half: `Q = 0` closes the quantitative chain

`G := pAx A (CoarseLattice L 2) 2 + curlEnergy A` is the right-hand side throughout. Every constant
below is COUNTED from the previous one through `sq_two` / `sq_four`, never fitted:

`352` (intra, §5c.1) → `2820 = 4·(1 + 352 + 352)` (one transverse step) → `11280 = 4·2820`
(at most two steps) → `23264 = 2·352 + 2·11280` (a `Q`-summand's deviation) → `69088 = 2·23264 +
2·11280` (an arbitrary bond). The `Q`-average is taken with a MAXIMUM over the block, not
Cauchy–Schwarz, so no square root enters. -/

/-- One transverse step, quantitatively: the two direction-`ν` bonds of the plaquette are
intra-block, so §5c.1 controls them and the step costs one curl. -/
theorem inter_step_bound (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (u v : Fin 3 → ℕ) (hu : ∀ ν, u ν ≤ 1) (hv : ∀ ν, v ν ≤ 1) (μ ν : Fin 3) (hne : ν ≠ μ)
    (hzero : u ν = 0) (hone : v ν = u ν + 1) (hrest : ∀ ρ, ρ ≠ ν → v ρ = u ρ) :
    ‖A (addOff y v, μ) - A (addOff y u, μ)‖ ^ 2
      ≤ 2820 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
  have hP : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 := pAx_nonneg A _ 2
  have hC : (0 : ℝ) ≤ curlEnergy A := curlEnergy_nonneg A
  have hshift : periodicLatticeShift (addOff y u) ν = addOff y v :=
    shift_addOff hdvd hy u v ν hu hv hone hrest
  have hpar : (addOff y u ν).val % 2 = 0 := by rw [addOff_parity hdvd hy hu ν, hzero]
  have hI1 : ‖A (addOff y u, ν)‖ ^ 2 ≤ 352 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) :=
    intra_bond_energy_bound_global hdvd A _ ν hpar
  have hI2 : ‖A (periodicLatticeShift (addOff y u) μ, ν)‖ ^ 2
      ≤ 352 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
    refine intra_bond_energy_bound_global hdvd A _ ν ?_
    rw [shiftNe (addOff y u) hne]
    exact hpar
  rcases lt_trichotomy μ ν with h | h | h
  · have hF := norm_sq_flatCurl_le A (addOff y u, ⟨(μ, ν), h⟩)
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
  · have hF := norm_sq_flatCurl_le A (addOff y u, ⟨(ν, μ), h⟩)
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

/-- **Quantitative STAGE TWO.** An inter-block bond differs from the block's reference bond
`A(y + e_μ, μ)` by at most two transverse steps. -/
theorem inter_dev_bound (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (e : Fin 3 → ℕ) (he : ∀ ν, e ν ≤ 1) (μ : Fin 3) (heμ : e μ = 1) :
    ‖A (addOff y e, μ) - A (periodicLatticeShift y μ, μ)‖ ^ 2
      ≤ 11280 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
  have hP : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 := pAx_nonneg A _ 2
  have hC : (0 : ℝ) ≤ curlEnergy A := curlEnergy_nonneg A
  have S := fun (u v : Fin 3 → ℕ) (hu : ∀ ν, u ν ≤ 1) (hv : ∀ ν, v ν ≤ 1)
      (m n : Fin 3) (hne : n ≠ m) (h0 : u n = 0) (h1 : v n = u n + 1)
      (hr : ∀ ρ, ρ ≠ n → v ρ = u ρ) =>
    inter_step_bound hdvd A hy u v hu hv m n hne h0 h1 hr
  have two : ∀ a b c : SuTwo,
      ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
    intro a b c
    have h : a - c = (a - b) + (b - c) := by abel
    rw [h]
    exact sq_two _ _
  have zero_case : ∀ a : SuTwo,
      ‖a - a‖ ^ 2 ≤ 11280 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
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

/-- The deviation of a single `Q`-summand from the block's reference bond. Stated with an ABSTRACT
offset `e` (never with a site `x` that the offset itself mentions — rewriting `x = addOff y (…x…)`
in place substitutes inside the offset and corrupts the statement). -/
theorem block_summand_dev (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0)
    (e : Fin 3 → ℕ) (he : ∀ ν, e ν ≤ 1) (μ : Fin 3) :
    ‖(A (addOff y e, μ) + A (periodicLatticeShift (addOff y e) μ, μ))
        - A (periodicLatticeShift y μ, μ)‖ ^ 2
      ≤ 23264 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
  have hP : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 := pAx_nonneg A _ 2
  have hC : (0 : ℝ) ≤ curlEnergy A := curlEnergy_nonneg A
  have hpar : (addOff y e μ).val % 2 = e μ % 2 := addOff_parity hdvd hy he μ
  set e' : Fin 3 → ℕ := fun ν => if ν = μ then 1 else e ν with he'def
  have he' : ∀ ν, e' ν ≤ 1 := by
    intro ν
    simp only [he'def]
    split_ifs with hh
    · omega
    · exact he ν
  rcases (show e μ = 0 ∨ e μ = 1 by have := he μ; omega) with h0 | h1
  · have hA : ‖A (addOff y e, μ)‖ ^ 2 ≤ 352 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) :=
      intra_bond_energy_bound_global hdvd A _ μ (by rw [hpar, h0])
    have hsh : periodicLatticeShift (addOff y e) μ = addOff y e' :=
      shift_addOff hdvd hy e e' μ he he' (by simp only [he'def, if_pos rfl, h0])
        (fun ν hν => by simp only [he'def, if_neg hν])
    have hA' : ‖A (periodicLatticeShift (addOff y e) μ, μ)
        - A (periodicLatticeShift y μ, μ)‖ ^ 2
        ≤ 11280 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
      rw [hsh]
      exact inter_dev_bound hdvd A hy e' he' μ (by simp only [he'def, if_pos rfl])
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
        ≤ 11280 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) :=
      inter_dev_bound hdvd A hy e he μ h1
    have hA' : ‖A (periodicLatticeShift (addOff y e) μ, μ)‖ ^ 2
        ≤ 352 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
      refine intra_bond_energy_bound_global hdvd A _ μ ?_
      rw [shift_parity hdvd (addOff y e) μ]
      have hq := hpar
      have hr := h1
      omega
    have heq : (A (addOff y e, μ) + A (periodicLatticeShift (addOff y e) μ, μ))
          - A (periodicLatticeShift y μ, μ)
        = (A (addOff y e, μ) - A (periodicLatticeShift y μ, μ))
          + A (periodicLatticeShift (addOff y e) μ, μ) := by
      abel
    rw [heq]
    have hb := sq_two (A (addOff y e, μ) - A (periodicLatticeShift y μ, μ))
      (A (periodicLatticeShift (addOff y e) μ, μ))
    nlinarith [hb, hA, hA']

/-- **Quantitative STAGE THREE.** `Q A = 0` bounds the block's reference inter-block bond. The
average is taken through a MAXIMUM over the block (`Finset.exists_max_image`), so neither a square
root nor a Cauchy–Schwarz inequality is needed. -/
theorem Q_inter_bound (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    {y : PeriodicLatticeSite L} (hyc : y ∈ CoarseLattice L 2) (μ : Fin 3) :
    ‖A (periodicLatticeShift y μ, μ)‖ ^ 2
      ≤ 23264 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
  have hy : ∀ ν : Fin 3, (y ν).val % 2 = 0 := mem_CoarseLattice.1 hyc
  have hP : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 := pAx_nonneg A _ 2
  have hC : (0 : ℝ) ≤ curlEnergy A := curlEnergy_nonneg A
  have h := hQ (⟨y, hyc⟩, μ)
  rw [lineCoarse_trivial_two A y hyc μ] at h
  have hsum : (∑ x ∈ blockOf y 2, (A (x, μ) + A (periodicLatticeShift x μ, μ))) = 0 := by
    rcases smul_eq_zero.1 h with hc0 | hs
    · exact absurd hc0 (by norm_num)
    · exact hs
  have hdev : ∀ x ∈ blockOf y 2,
      ‖(A (x, μ) + A (periodicLatticeShift x μ, μ)) - A (periodicLatticeShift y μ, μ)‖ ^ 2
        ≤ 23264 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
    intro x hx
    obtain ⟨hxe, hle⟩ := mem_block_offset hx
    have key := block_summand_dev hdvd A hy (fun ν => (x ν).val - (y ν).val) hle μ
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

/-- **THE QUANTITATIVE THEOREM.** On the coarse-average-free subspace, at every extent with
`2 ∣ (L μ + 1)`, block side `ell = 2`, flat background, EVERY bond's energy is bounded by the
gauge-fixing energy plus the curl energy, with an ABSOLUTE constant — no volume factor and no
dependence on `L`. This is the quantitative form of `triple_kernel_trivial`: setting the right-hand
side to `0` recovers `A = 0`. -/
theorem bond_energy_bound (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    (b : Bond L) :
    ‖A b‖ ^ 2 ≤ 69088 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
  obtain ⟨z, μ⟩ := b
  have hP : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 := pAx_nonneg A _ 2
  have hC : (0 : ℝ) ≤ curlEnergy A := curlEnergy_nonneg A
  by_cases hz : (z μ).val % 2 = 0
  · have h := intra_bond_energy_bound_global hdvd A z μ hz
    nlinarith [h]
  · have hz1 : (z μ).val % 2 = 1 := by omega
    have hy : ∀ ν : Fin 3, ((cc z) ν).val % 2 = 0 := fun ν => cc_even z ν
    have hze : z = addOff (cc z) (fun ν => (z ν).val % 2) := by
      refine addOff_of_val (cc z) z _ (fun ν => ?_)
      show (z ν).val = (cc z ν).val + (z ν).val % 2
      rw [cc_val]; omega
    have hdev : ‖A (z, μ) - A (periodicLatticeShift (cc z) μ, μ)‖ ^ 2
        ≤ 11280 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
      have key := inter_dev_bound hdvd A hy (fun ν => (z ν).val % 2)
        (fun ν => by omega) μ hz1
      rwa [← hze] at key
    have href := Q_inter_bound hdvd A hQ (cc_mem z) μ
    have hsplit : A (z, μ)
        = (A (z, μ) - A (periodicLatticeShift (cc z) μ, μ))
          + A (periodicLatticeShift (cc z) μ, μ) := by abel
    have hb := sq_two (A (z, μ) - A (periodicLatticeShift (cc z) μ, μ))
      (A (periodicLatticeShift (cc z) μ, μ))
    rw [← hsplit] at hb
    nlinarith [hb, hdev, href]

/-- **THE QUANTITATIVE THEOREM IMPLIES THE QUALITATIVE ONE** — the two are consistent, and the
`69088` is not hiding a vacuity: putting the right-hand side to zero returns `A = 0`. Proved by
running `bond_energy_bound` at the hypotheses of `triple_kernel_trivial`, NOT by re-invoking
`triple_kernel_trivial`, so this is a genuine cross-check of the two chains against each other. -/
theorem quantitative_implies_qualitative (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
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
  funext b
  have h := bond_energy_bound hdvd A hQ b
  rw [hP, hCz] at h
  have h0 : ‖A b‖ ^ 2 ≤ 0 := by linarith
  have h1 : ‖A b‖ = 0 := by nlinarith [norm_nonneg (A b), h0]
  exact norm_eq_zero.1 h1

end Quantitative

#print axioms curlEnergy
#print axioms norm_sq_flatCurl_le
#print axioms sq_two
#print axioms sq_four
#print axioms curl_solve
#print axioms intra_block_energy_bound
#print axioms intra_bond_energy_bound
#print axioms intra_bond_energy_bound_global
#print axioms intra_bond_energy_bound_nonvacuous
#print axioms quantitative_bound_is_homogeneous
#print axioms inter_step_bound
#print axioms inter_dev_bound
#print axioms block_summand_dev
#print axioms Q_inter_bound
#print axioms bond_energy_bound
#print axioms quantitative_implies_qualitative

/-! ## §5d. THE HYPOTHESIS `2 ∣ (L μ + 1)` IS DISCHARGEABLE — the theorem at `witL5`

A theorem whose extent hypothesis no extent satisfies would be vacuous. `witL5 = fun _ => 5` is the
campaign's own `6³` witness geometry (`RegularUDomainWitness`), and `2 ∣ 6`, so both headline
theorems fire there with NO hypothesis on the extent at all. -/

section Witness

open AdalyFormal.Balaban.RegularUDomainWitness (witL5)

theorem hdvd_witL5 : ∀ μ : Fin 3, (2 : ℕ) ∣ (witL5 μ + 1) := by decide

/-- **The triple kernel is zero at `witL5`** — the extent hypothesis discharged, so this statement
has no side condition left. -/
theorem triple_kernel_trivial_witL5 (A : Bond witL5 → SuTwo) (hc : closedFlat A)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2,
      lineCoarseRestrictCov (trivialU witL5) 2 A b = 0)
    (hP : pAx A (CoarseLattice witL5 2) 2 = 0) :
    A = fun _ => 0 :=
  triple_kernel_trivial hdvd_witL5 A hc hQ hP

/-- **The quantitative bound at `witL5`**, extent hypothesis discharged. -/
theorem bond_energy_bound_witL5 (A : Bond witL5 → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2,
      lineCoarseRestrictCov (trivialU witL5) 2 A b = 0) (b : Bond witL5) :
    ‖A b‖ ^ 2 ≤ 69088 * (pAx A (CoarseLattice witL5 2) 2 + curlEnergy A) :=
  bond_energy_bound hdvd_witL5 A hQ b

/-- **The drop-one controls at `witL5`, at a concretely nonzero fibre vector** — so the
non-redundancy of the three clauses is a statement with no undischarged hypothesis either. -/
theorem clauses_are_load_bearing_witL5 :
    ((altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen ≠ fun _ => 0)
        ∧ closedFlat (altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)
        ∧ (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2,
            lineCoarseRestrictCov (trivialU witL5) 2
              (altMode AdalyFormal.Balaban.BridgeRestricted.rotGen) b = 0)
        ∧ pAx (altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)
            (CoarseLattice witL5 2) 2 ≠ 0)
      ∧ ((blockMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen ≠ fun _ => 0)
        ∧ closedFlat (blockMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)
        ∧ pAx (blockMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)
            (CoarseLattice witL5 2) 2 = 0
        ∧ ¬ (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2,
            lineCoarseRestrictCov (trivialU witL5) 2
              (blockMode AdalyFormal.Balaban.BridgeRestricted.rotGen) b = 0))
      ∧ ((oddAltMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen ≠ fun _ => 0)
        ∧ (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2,
            lineCoarseRestrictCov (trivialU witL5) 2
              (oddAltMode AdalyFormal.Balaban.BridgeRestricted.rotGen) b = 0)
        ∧ pAx (oddAltMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)
            (CoarseLattice witL5 2) 2 = 0
        ∧ ¬ closedFlat (oddAltMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen)) :=
  clauses_are_load_bearing hdvd_witL5 AdalyFormal.Balaban.BridgeRestricted.rotGen
    AdalyFormal.Balaban.BridgeRestricted.rotGen_ne_zero

end Witness

#print axioms hdvd_witL5
#print axioms triple_kernel_trivial_witL5
#print axioms bond_energy_bound_witL5
#print axioms clauses_are_load_bearing_witL5

/-! ## §5e. THE COMPOSITION INTERFACE — the same statements in the campaign's own `Δ_k`

Everything above is phrased with `curlEnergy`, this module's own `∑_p ‖(dA)(p)‖²`. The campaign's
operator is `NormalizationAudit.deltaKQuadFormNormalizedCorrected`. At the FLAT background the two
coincide EXACTLY — `Δ′` vanishes there (`DeltaKUnitLevel.deltaPrimeNormalizedTransported_trivialU_eq_zero`,
reused not re-derived) and `d*d` is the curl energy (`LemmaAssembly.dstarDQuadForm_eq_sum_norm_sq`,
likewise). So §5c's bound is literally CMP95 p.19's `⟨A, Δ_k A⟩ + P_Ax(A) ≥ c·(energy)` on the
subspace `QA = 0`, with `c = 1/69088`. -/

section DeltaKBridge

open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm)
open AdalyFormal.Balaban.LemmaAssembly (dstarDQuadForm_eq_sum_norm_sq)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.CovU1Reduction (curlValueCovariant_trivialU_local)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- **`Δ_k` AT THE FLAT BACKGROUND IS THE CURL ENERGY.** Not a normalization convention chosen
here: both halves are the tree's own theorems. -/
theorem deltaK_trivialU_eq_curlEnergy (A : Bond L → SuTwo) :
    deltaKQuadFormNormalizedCorrected (trivialU L) A = curlEnergy A := by
  show dstarDQuadForm (trivialU L) A
      + AdalyFormal.Balaban.NormalizationAudit.deltaPrimeQuadFormNormalizedTransported
        (trivialU L) A = _
  rw [AdalyFormal.Balaban.DeltaKUnitLevel.deltaPrimeNormalizedTransported_trivialU_eq_zero A,
    add_zero, dstarDQuadForm_eq_sum_norm_sq]
  unfold curlEnergy
  exact Finset.sum_congr rfl (fun p _ => by rw [curlValueCovariant_trivialU_local A p])

/-- `Δ_k = 0` at the flat background is exactly closedness — it is a sum of squares. -/
theorem closedFlat_iff_deltaK_zero (A : Bond L → SuTwo) :
    closedFlat A ↔ deltaKQuadFormNormalizedCorrected (trivialU L) A = 0 := by
  rw [deltaK_trivialU_eq_curlEnergy]
  constructor
  · intro hc
    unfold curlEnergy
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [hc p, norm_zero]
    norm_num
  · intro h p
    have h1 : ‖flatCurlValue A p‖ ^ 2 = 0 := by
      have hle := norm_sq_flatCurl_le A p
      have hnn := sq_nonneg (‖flatCurlValue A p‖)
      rw [h] at hle
      linarith
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1)

/-- **CMP95 printed p.19, IN THE CAMPAIGN'S OWN OPERATOR — the qualitative half.** -/
theorem triple_kernel_trivial_deltaK (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo)
    (hD : deltaKQuadFormNormalizedCorrected (trivialU L) A = 0)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    (hP : pAx A (CoarseLattice L 2) 2 = 0) :
    A = fun _ => 0 :=
  triple_kernel_trivial hdvd A ((closedFlat_iff_deltaK_zero A).2 hD) hQ hP

/-- **CMP95 printed p.19, IN THE CAMPAIGN'S OWN OPERATOR — the quantitative half.**
`⟨A, Δ_k A⟩ + P_Ax(A) ≥ (1/69088)·‖A b‖²` for every bond, on `{QA = 0}`, at every even extent, with
NO volume factor. Setting the left side to `0` returns the qualitative half. -/
theorem bond_energy_bound_deltaK (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    (b : Bond L) :
    ‖A b‖ ^ 2
      ≤ 69088 * (deltaKQuadFormNormalizedCorrected (trivialU L) A
        + pAx A (CoarseLattice L 2) 2) := by
  rw [deltaK_trivialU_eq_curlEnergy]
  have h := bond_energy_bound hdvd A hQ b
  linarith

/-- **The `L²` form, WITH ITS VOLUME FACTOR STATED IN THE NAME.** Summing the per-bond bound over
the `Fintype.card (Bond L)` bonds is legitimate but costs a factor that GROWS WITH THE VOLUME, so
this is NOT a coercivity constant in Bałaban's sense and must not be cited as one. It is recorded
only so that the gap between what is proved and what an RG argument needs is explicit rather than
implied. Removing the factor requires a bond ↦ (block, local index) reindexing together with a
multiplicity count bounding how many blocks' local estimates a single plaquette or contour enters —
see `compute/fibre_coercivity/PROGRESS.md` §"What is NOT proved". -/
theorem bondEnergy_le_with_volume_factor (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0) :
    bondEnergy A
      ≤ (Fintype.card (Bond L) : ℝ)
        * (69088 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A)) := by
  show (∑ b : Bond L, ‖A b‖ ^ 2) ≤ _
  have hstep : (∑ b : Bond L, ‖A b‖ ^ 2)
      ≤ ∑ _b : Bond L, (69088 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A)) :=
    Finset.sum_le_sum (fun b _ => bond_energy_bound hdvd A hQ b)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstep
  exact hstep

end DeltaKBridge

#print axioms deltaK_trivialU_eq_curlEnergy
#print axioms closedFlat_iff_deltaK_zero
#print axioms triple_kernel_trivial_deltaK
#print axioms bond_energy_bound_deltaK
#print axioms bondEnergy_le_with_volume_factor

/-! ## §6. `ell = 1` — the degenerate case, recorded in place -/

/-- **At `ell = 1` the gauge-fixing clause is VACUOUS**: `B(y) = {y}`, so `(1.10)`'s inner product
is empty and `pAx ≡ 0` for EVERY field. Nothing proved at `ell = 1` is evidence about the
gauge-fixing term. Reused from `AxialCoercivity`, not re-derived. -/
theorem ell1_pAx_vacuous (A : Bond L → SuTwo) (S : Finset (PeriodicLatticeSite L)) :
    pAx A S 1 = 0 :=
  pAx_ell_one A S

#print axioms ell1_pAx_vacuous

end AdalyFormal.Balaban.FibreCoercivity
