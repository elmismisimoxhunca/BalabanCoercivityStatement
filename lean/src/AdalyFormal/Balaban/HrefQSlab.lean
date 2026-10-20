import AdalyFormal.Balaban.QSlabExpand
import AdalyFormal.Balaban.HrefBlk
import AdalyFormal.Balaban.EnergyEval
import AdalyFormal.Balaban.SparseGram

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! # `HrefQSlab` — the Q line-form free-cell reindex (`[Q-reindex]`, piece of `hQS`).

The three line-integral energies `lineCoarseRestrict 2 C (⟨prevSite μ,_⟩, μ)` expressed exactly on
the admissible subspace as scalar multiples of `freecoord`-covectors, matching `SparseGram.qsCertSparse`'s
three Q squares.  Ground truth: `compute/href_qslab/covector_spec.py` (self-hash f9ede09c0767eb83,
exact ℚ, size-uniform N∈{6,8}):

* `line_0 = (1/8)·(C₆₄+C₆₇+C₇₁+C₇₄)`.

The construction: unfold `lineCoarseRestrict` to `(1/16)·∑_{x∈block(prevSite μ)} lineIntegralValue`,
enumerate the 8 block sites via `QSlabExpand.blockOf_fits_eq_image`, expand each `lineIntegralValue`
to its two bonds, identify each free bond via `HrefBlk.freeCellBond_eq_of_coords` and drop each
staircase-pinned bond via `BlockPoincare.dir0_bond_eq_zero` (μ=0). -/

namespace HrefQSlab

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.Lemma24Assembly
open RatSOSEval
open BlockFaithful QSlabExpand FreeCellFrame Ell2RefBlock HrefBlk

variable {L : PeriodicLatticeExtent}

/-- `lineIntegralValue` at `ell = 2` is the sum of the base bond and its `+e_μ` shift. -/
theorem lineIntegralValue_two (C : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    lineIntegralValue 2 C x μ = C (x, μ) + C (periodicLatticeShift x μ, μ) := by
  simp [lineIntegralValue, Finset.sum_range_succ]

/-- The reference block `B(prevSite 0)` fits (no wrap on the block enumeration): its `+2` upper
corner is `≤ L μ + 1` on every axis. -/
theorem prevSite0_fits (hL : ∀ μ, 4 ≤ L μ) :
    ∀ μ : Fin 3, ((prevSite (0 : Fin 3) : PeriodicLatticeSite L) μ).val + 2 ≤ L μ + 1 := by
  intro μ
  by_cases h : μ = 0
  · subst h; rw [prevSite_self]; have := hL 0; omega
  · rw [prevSite_ne 0 μ h]; have := hL μ; simp; omega

/-- The `+e_0` shift, off-axis coordinates unchanged. -/
theorem shift0_coord_ne (s : PeriodicLatticeSite L) {ν : Fin 3} (hν : ν ≠ 0) :
    (periodicLatticeShift s 0 ν) = s ν := Function.update_of_ne hν _ _

/-- The `+e_0` shift, on-axis value is `(s₀+1) mod (L₀+1)`. -/
theorem shift0_coord0_val (s : PeriodicLatticeSite L) :
    (periodicLatticeShift s 0 0).val = ((s 0).val + 1) % (L 0 + 1) := by
  rw [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- Case-split helper: a `Fin 3` that is neither `0` nor `1` is `2`. -/
theorem fin3_two {μ : Fin 3} (h0 : μ ≠ 0) (h1 : μ ≠ 1) : μ = 2 := by
  have e0 : μ.val ≠ 0 := fun h => h0 (Fin.ext h)
  have e1 : μ.val ≠ 1 := fun h => h1 (Fin.ext h)
  have := μ.isLt; exact Fin.ext (by omega)

/-! ## Pin / free-bond identifiers for direction-`0` bonds (μ = 0). -/

/-- A direction-`0` bond based at coord₀ `= L₀-1` (with in-`{0,1}` transverse coords) is
staircase-pinned in `B(prevSite 0)` — it vanishes on the admissible subspace. -/
theorem pinPrev0 (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) (s : PeriodicLatticeSite L)
    (hc0 : (s 0).val = L 0 - 1) (hc1 : (s 1).val < 2) (hc2 : (s 2).val < 2) :
    C (s, (0 : Fin 3)) = 0 := by
  have hL0 := hL 0
  have hmem1 : s ∈ blockOf (prevSite (0 : Fin 3) : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro μ
    by_cases h0 : μ = 0
    · subst h0; rw [prevSite_self]; omega
    · by_cases h1 : μ = 1
      · subst h1; rw [prevSite_ne 0 1 (by decide)]; simp only [Fin.val_zero]; omega
      · have h2 := fin3_two h0 h1; subst h2; rw [prevSite_ne 0 2 (by decide)]; simp only [Fin.val_zero]; omega
  have hmem2 : periodicLatticeShift s 0 ∈ blockOf (prevSite (0 : Fin 3) : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro μ
    by_cases h0 : μ = 0
    · subst h0; rw [prevSite_self, shift0_coord0_val, hc0]
      have : (L 0 - 1 + 1) % (L 0 + 1) = L 0 := by
        rw [show L 0 - 1 + 1 = L 0 by omega, Nat.mod_eq_of_lt (by omega)]
      rw [this]; omega
    · by_cases h1 : μ = 1
      · subst h1; rw [shift0_coord_ne s (by decide), prevSite_ne 0 1 (by decide)]
        simp only [Fin.val_zero]; omega
      · have h2 := fin3_two h0 h1; subst h2; rw [shift0_coord_ne s (by decide), prevSite_ne 0 2 (by decide)]
        simp only [Fin.val_zero]; omega
  exact dir0_bond_eq_zero (by omega) C hC (prevSite 0) (prevSite_mem 0 hdvd) (s, 0) rfl
    ⟨hmem1, hmem2⟩

/-- A direction-`0` bond based at coord₀ `= 0` (with in-`{0,1}` transverse coords) is
staircase-pinned in `B(0)` — it vanishes on the admissible subspace. -/
theorem pinOrig0 (hL : ∀ μ, 4 ≤ L μ) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) (s : PeriodicLatticeSite L)
    (hc0 : (s 0).val = 0) (hc1 : (s 1).val < 2) (hc2 : (s 2).val < 2) :
    C (s, (0 : Fin 3)) = 0 := by
  have hL0 := hL 0
  have hmem1 : s ∈ blockOf (0 : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro μ
    by_cases h0 : μ = 0
    · subst h0; show (0 : ℕ) ≤ (s 0).val ∧ (s 0).val < 0 + 2; omega
    · by_cases h1 : μ = 1
      · subst h1; show (0 : ℕ) ≤ (s 1).val ∧ (s 1).val < 0 + 2; omega
      · have h2 := fin3_two h0 h1; subst h2; show (0 : ℕ) ≤ (s 2).val ∧ (s 2).val < 0 + 2; omega
  have hmem2 : periodicLatticeShift s 0 ∈ blockOf (0 : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro μ
    by_cases h0 : μ = 0
    · subst h0; rw [shift0_coord0_val, hc0]
      have : (0 + 1) % (L 0 + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [this]; show (0 : ℕ) ≤ 1 ∧ 1 < 0 + 2; omega
    · by_cases h1 : μ = 1
      · subst h1; rw [shift0_coord_ne s (by decide)]; show (0:ℕ) ≤ (s 1).val ∧ (s 1).val < 0+2; omega
      · have h2 := fin3_two h0 h1; subst h2; rw [shift0_coord_ne s (by decide)]; show (0:ℕ) ≤ (s 2).val ∧ (s 2).val < 0+2; omega
  exact dir0_bond_eq_zero (by omega) C hC (0 : PeriodicLatticeSite L)
    (BlockFaithful.origin_mem_coarse 2) (s, 0) rfl ⟨hmem1, hmem2⟩

/-- A direction-`0` bond whose site matches free-cell coordinate `idx`'s reference site equals
`freeCellBond … idx`. -/
theorem freeIdent0 (hL : ∀ μ, 4 ≤ L μ) (C : Bond L → ℝ) (idx : Fin 80) (s : PeriodicLatticeSite L)
    (q0 : (refSite L hL idx 0).val = (s 0).val) (q1 : (refSite L hL idx 1).val = (s 1).val)
    (q2 : (refSite L hL idx 2).val = (s 2).val) (hd : freeDir idx = 0) :
    C (s, (0 : Fin 3)) = C (freeCellBond L hL idx) := by
  rw [freeCellBond_eq_of_coords hL idx s 0 q0 q1 q2 hd]

/-- Injectivity of the block-fitting site enumeration. -/
theorem siteFn_inj (hL : ∀ μ, 4 ≤ L μ) :
    ∀ f ∈ (Finset.univ : Finset (Fin 3 → Fin 2)), ∀ g ∈ (Finset.univ : Finset (Fin 3 → Fin 2)),
      (fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + (f μ).val, by
        have := (f μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1)))
      = (fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + (g μ).val, by
        have := (g μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))) → f = g := by
  intro f _ g _ h
  funext μ
  have := congrFun h μ
  have hv : ((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + (f μ).val
      = ((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + (g μ).val := congrArg Fin.val this
  exact Fin.ext (by omega)

theorem line0_blocksum (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) :
    (∑ x ∈ blockOf (prevSite (0 : Fin 3) : PeriodicLatticeSite L) 2, lineIntegralValue 2 C x 0)
      = 2 * (C (freeCellBond L hL 64) + C (freeCellBond L hL 67)
             + C (freeCellBond L hL 71) + C (freeCellBond L hL 74)) := by
  rw [blockOf_fits_eq_image (prevSite 0) 2 (prevSite0_fits hL), Finset.sum_image (siteFn_inj hL)]
  rw [show (Finset.univ : Finset (Fin 3 → Fin 2)) =
      { ![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1], ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1] } from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [lineIntegralValue_two]
  have b1_000 : C ((fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![0,0,0] : Fin 3 → Fin 2) μ).val, by have := ((![0,0,0] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))), (0 : Fin 3)) = 0 := by
    apply pinPrev0 hL hdvd C hC
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b2_000 : C (periodicLatticeShift (fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![0,0,0] : Fin 3 → Fin 2) μ).val, by have := ((![0,0,0] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))) 0, (0 : Fin 3)) = C (freeCellBond L hL 64) := by
    apply freeIdent0 hL C 64 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 64 0 4 (by decide), (coordNat_vals (L:=L) 0).2.2]
      rw [shift0_coord0_val]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
    · rw [refSite_val hL 64 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 64 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b1_001 : C ((fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![0,0,1] : Fin 3 → Fin 2) μ).val, by have := ((![0,0,1] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))), (0 : Fin 3)) = 0 := by
    apply pinPrev0 hL hdvd C hC
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b2_001 : C (periodicLatticeShift (fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![0,0,1] : Fin 3 → Fin 2) μ).val, by have := ((![0,0,1] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))) 0, (0 : Fin 3)) = C (freeCellBond L hL 67) := by
    apply freeIdent0 hL C 67 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 67 0 4 (by decide), (coordNat_vals (L:=L) 0).2.2]
      rw [shift0_coord0_val]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
    · rw [refSite_val hL 67 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 67 2 1 (by decide), (coordNat_vals (L:=L) 2).2.1]
      rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b1_010 : C ((fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![0,1,0] : Fin 3 → Fin 2) μ).val, by have := ((![0,1,0] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))), (0 : Fin 3)) = 0 := by
    apply pinPrev0 hL hdvd C hC
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b2_010 : C (periodicLatticeShift (fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![0,1,0] : Fin 3 → Fin 2) μ).val, by have := ((![0,1,0] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))) 0, (0 : Fin 3)) = C (freeCellBond L hL 71) := by
    apply freeIdent0 hL C 71 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 71 0 4 (by decide), (coordNat_vals (L:=L) 0).2.2]
      rw [shift0_coord0_val]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
    · rw [refSite_val hL 71 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 71 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b1_011 : C ((fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![0,1,1] : Fin 3 → Fin 2) μ).val, by have := ((![0,1,1] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))), (0 : Fin 3)) = 0 := by
    apply pinPrev0 hL hdvd C hC
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b2_011 : C (periodicLatticeShift (fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![0,1,1] : Fin 3 → Fin 2) μ).val, by have := ((![0,1,1] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))) 0, (0 : Fin 3)) = C (freeCellBond L hL 74) := by
    apply freeIdent0 hL C 74 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 74 0 4 (by decide), (coordNat_vals (L:=L) 0).2.2]
      rw [shift0_coord0_val]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
    · rw [refSite_val hL 74 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 74 2 1 (by decide), (coordNat_vals (L:=L) 2).2.1]
      rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b1_100 : C ((fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![1,0,0] : Fin 3 → Fin 2) μ).val, by have := ((![1,0,0] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))), (0 : Fin 3)) = C (freeCellBond L hL 64) := by
    apply freeIdent0 hL C 64 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 64 0 4 (by decide), (coordNat_vals (L:=L) 0).2.2]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 64 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 64 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b2_100 : C (periodicLatticeShift (fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![1,0,0] : Fin 3 → Fin 2) μ).val, by have := ((![1,0,0] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))) 0, (0 : Fin 3)) = 0 := by
    apply pinOrig0 hL C hC
    · rw [shift0_coord0_val]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
    · rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b1_101 : C ((fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![1,0,1] : Fin 3 → Fin 2) μ).val, by have := ((![1,0,1] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))), (0 : Fin 3)) = C (freeCellBond L hL 67) := by
    apply freeIdent0 hL C 67 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 67 0 4 (by decide), (coordNat_vals (L:=L) 0).2.2]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 67 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 67 2 1 (by decide), (coordNat_vals (L:=L) 2).2.1]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b2_101 : C (periodicLatticeShift (fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![1,0,1] : Fin 3 → Fin 2) μ).val, by have := ((![1,0,1] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))) 0, (0 : Fin 3)) = 0 := by
    apply pinOrig0 hL C hC
    · rw [shift0_coord0_val]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
    · rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b1_110 : C ((fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![1,1,0] : Fin 3 → Fin 2) μ).val, by have := ((![1,1,0] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))), (0 : Fin 3)) = C (freeCellBond L hL 71) := by
    apply freeIdent0 hL C 71 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 71 0 4 (by decide), (coordNat_vals (L:=L) 0).2.2]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 71 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 71 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b2_110 : C (periodicLatticeShift (fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![1,1,0] : Fin 3 → Fin 2) μ).val, by have := ((![1,1,0] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))) 0, (0 : Fin 3)) = 0 := by
    apply pinOrig0 hL C hC
    · rw [shift0_coord0_val]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
    · rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b1_111 : C ((fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![1,1,1] : Fin 3 → Fin 2) μ).val, by have := ((![1,1,1] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))), (0 : Fin 3)) = C (freeCellBond L hL 74) := by
    apply freeIdent0 hL C 74 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 74 0 4 (by decide), (coordNat_vals (L:=L) 0).2.2]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 74 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [refSite_val hL 74 2 1 (by decide), (coordNat_vals (L:=L) 2).2.1]
      simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  have b2_111 : C (periodicLatticeShift (fun μ : Fin 3 => (⟨((prevSite (0:Fin 3) : PeriodicLatticeSite L) μ).val + ((![1,1,1] : Fin 3 → Fin 2) μ).val, by have := ((![1,1,1] : Fin 3 → Fin 2) μ).isLt; have := prevSite0_fits hL μ; omega⟩ : Fin (L μ + 1))) 0, (0 : Fin 3)) = 0 := by
    apply pinOrig0 hL C hC
    · rw [shift0_coord0_val]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
    · rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
    · rw [shift0_coord_ne _ (by decide)]; simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 0; omega)
  rw [b1_000, b2_000, b1_001, b2_001, b1_010, b2_010, b1_011, b2_011, b1_100, b2_100, b1_101, b2_101, b1_110, b2_110, b1_111, b2_111]
  ring

/-- **The `μ = 0` line-form free-cell reindex (`[Q-reindex]`, PROVED, no `sorry`).** On the admissible
subspace, the coarse `Q`-energy line integral at `prevSite 0` equals `(1/8)` times the sum of `C` on
its four free-cell top-face bonds `{64,67,71,74}` — matching `SparseGram.qsCertSparse`'s first Q square
(coefficient `4`, since `256·(1/8)² = 4`).  Ground truth `compute/href_qslab/covector_spec.py`. -/
theorem line_reindex0 (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) :
    lineCoarseRestrict 2 C (⟨prevSite 0, prevSite_mem 0 hdvd⟩, 0)
      = (1 / 8) * (freecoord L hL C 64 + freecoord L hL C 67
                   + freecoord L hL C 71 + freecoord L hL C 74) := by
  simp only [freecoord_apply]
  rw [lineCoarseRestrict, line0_blocksum hL hdvd C hC]
  push_cast
  ring


/-! ## Shared infrastructure for the `μ = 1, 2` line-form free-cell reindexes.
Generalizes the `μ = 0` template's helpers to arbitrary `κ`, and adds the direction-`1`/`2` pin
wrappers over `BlockPoincare.z0_bond1_eq_zero` / `w0_bond2_eq_zero`. -/

/-- `prevSite κ`'s block fits (no wrap) for every axis: `+2` upper corner `≤ L ν + 1`. -/
theorem prevSite_fits (hL : ∀ μ, 4 ≤ L μ) (κ : Fin 3) :
    ∀ ν : Fin 3, ((prevSite κ : PeriodicLatticeSite L) ν).val + 2 ≤ L ν + 1 := by
  intro ν
  by_cases h : ν = κ
  · rw [h, prevSite_self]; have := hL κ; omega
  · rw [prevSite_ne κ ν h]; have := hL ν; simp; omega

/-- `coordNat`'s code-`3` value is `L ν - 1`. -/
theorem coordNat3 (ν : Fin 3) : coordNat L ν 3 = L ν - 1 := by simp [coordNat]

/-- The `+e_1` shift, off-axis coordinates unchanged. -/
theorem shift1_coord_ne (s : PeriodicLatticeSite L) {ν : Fin 3} (hν : ν ≠ 1) :
    (periodicLatticeShift s 1 ν) = s ν := Function.update_of_ne hν _ _

/-- The `+e_1` shift, on-axis value is `(s₁+1) mod (L₁+1)`. -/
theorem shift1_coord1_val (s : PeriodicLatticeSite L) :
    (periodicLatticeShift s 1 1).val = ((s 1).val + 1) % (L 1 + 1) := by
  rw [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- The `+e_2` shift, off-axis coordinates unchanged. -/
theorem shift2_coord_ne (s : PeriodicLatticeSite L) {ν : Fin 3} (hν : ν ≠ 2) :
    (periodicLatticeShift s 2 ν) = s ν := Function.update_of_ne hν _ _

/-- The `+e_2` shift, on-axis value is `(s₂+1) mod (L₂+1)`. -/
theorem shift2_coord2_val (s : PeriodicLatticeSite L) :
    (periodicLatticeShift s 2 2).val = ((s 2).val + 1) % (L 2 + 1) := by
  rw [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- Injectivity of the block-fitting site enumeration for `prevSite κ`. -/
theorem siteFn_inj_mu (hL : ∀ μ, 4 ≤ L μ) (κ : Fin 3) :
    ∀ f ∈ (Finset.univ : Finset (Fin 3 → Fin 2)), ∀ g ∈ (Finset.univ : Finset (Fin 3 → Fin 2)),
      (fun ν : Fin 3 => (⟨((prevSite κ : PeriodicLatticeSite L) ν).val + (f ν).val, by
        have := (f ν).isLt; have := prevSite_fits hL κ ν; omega⟩ : Fin (L ν + 1)))
      = (fun ν : Fin 3 => (⟨((prevSite κ : PeriodicLatticeSite L) ν).val + (g ν).val, by
        have := (g ν).isLt; have := prevSite_fits hL κ ν; omega⟩ : Fin (L ν + 1))) → f = g := by
  intro f _ g _ h
  funext ν
  have := congrFun h ν
  have hv : ((prevSite κ : PeriodicLatticeSite L) ν).val + (f ν).val
      = ((prevSite κ : PeriodicLatticeSite L) ν).val + (g ν).val := congrArg Fin.val this
  exact Fin.ext (by omega)

/-- Generic direction-`1` pin: a dir-`1` bond at a site whose coord `0 = y₀`, both endpoints in
`B(y)`, vanishes on the admissible subspace (`z0 y s = s`, then `z0_bond1_eq_zero`). -/
theorem pinDir1 (hL : ∀ μ, 4 ≤ L μ) (C : Bond L → ℝ) (hC : C ∈ admissibleSubspaceInter L 2)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L 2) (s : PeriodicLatticeSite L)
    (h0 : s 0 = y 0) (hm : s ∈ blockOf y 2) (hms : periodicLatticeShift s 1 ∈ blockOf y 2) :
    C (s, (1 : Fin 3)) = 0 := by
  have hz : z0 y s = s := by unfold z0; rw [← h0]; exact Function.update_eq_self 0 s
  rw [← hz]
  exact z0_bond1_eq_zero (by have := hL 1; omega) C hC y hy s hm hms

/-- Generic direction-`2` pin: a dir-`2` bond at a site whose coords `0 = y₀, 1 = y₁`, both
endpoints in `B(y)`, vanishes on the admissible subspace (`w0 y s = s`, then `w0_bond2_eq_zero`). -/
theorem pinDir2 (hL : ∀ μ, 4 ≤ L μ) (C : Bond L → ℝ) (hC : C ∈ admissibleSubspaceInter L 2)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L 2) (s : PeriodicLatticeSite L)
    (h0 : s 0 = y 0) (h1 : s 1 = y 1) (hm : s ∈ blockOf y 2)
    (hms : periodicLatticeShift s 2 ∈ blockOf y 2) :
    C (s, (2 : Fin 3)) = 0 := by
  have hz : z0 y s = s := by unfold z0; rw [← h0]; exact Function.update_eq_self 0 s
  have hw : w0 y s = s := by unfold w0; rw [hz, ← h1]; exact Function.update_eq_self 1 s
  rw [← hw]
  exact w0_bond2_eq_zero (by have := hL 2; omega) y hy s hm hms C hC

/-- dir-`1` pin in `B(prevSite 1)` (coord₁ `= L₁-1`, coord₀ `= 0`). -/
theorem pinPrev1 (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) (s : PeriodicLatticeSite L)
    (hc0 : (s 0).val = 0) (hc1 : (s 1).val = L 1 - 1) (hc2 : (s 2).val < 2) :
    C (s, (1 : Fin 3)) = 0 := by
  have hL1 := hL 1
  have h0 : s 0 = (prevSite 1 : PeriodicLatticeSite L) 0 := by
    rw [prevSite_ne 1 0 (by decide)]; exact Fin.ext (by simpa using hc0)
  have hm : s ∈ blockOf (prevSite 1 : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro ν
    by_cases k0 : ν = 0
    · subst k0; rw [prevSite_ne 1 0 (by decide)]; simp only [Fin.val_zero]; omega
    · by_cases k1 : ν = 1
      · subst k1; rw [prevSite_self]; omega
      · have k2 := fin3_two k0 k1; subst k2; rw [prevSite_ne 1 2 (by decide)]; simp only [Fin.val_zero]; omega
  have hms : periodicLatticeShift s 1 ∈ blockOf (prevSite 1 : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro ν
    by_cases k0 : ν = 0
    · subst k0; rw [prevSite_ne 1 0 (by decide), shift1_coord_ne s (by decide)]; simp only [Fin.val_zero]; omega
    · by_cases k1 : ν = 1
      · subst k1; rw [prevSite_self, shift1_coord1_val, hc1]
        rw [show L 1 - 1 + 1 = L 1 by omega, Nat.mod_eq_of_lt (by omega)]; omega
      · have k2 := fin3_two k0 k1; subst k2; rw [prevSite_ne 1 2 (by decide), shift1_coord_ne s (by decide)]; simp only [Fin.val_zero]; omega
  exact pinDir1 hL C hC (prevSite 1) (prevSite_mem 1 hdvd) s h0 hm hms

/-- dir-`1` pin in `B(0)` (the wrapped coord₁ `= 0`, coord₀ `= 0`). -/
theorem pinOrig1 (hL : ∀ μ, 4 ≤ L μ) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) (s : PeriodicLatticeSite L)
    (hc0 : (s 0).val = 0) (hc1 : (s 1).val = 0) (hc2 : (s 2).val < 2) :
    C (s, (1 : Fin 3)) = 0 := by
  have hL1 := hL 1
  have h0 : s 0 = (0 : PeriodicLatticeSite L) 0 := Fin.ext (by simpa using hc0)
  have hm : s ∈ blockOf (0 : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro ν
    by_cases k0 : ν = 0
    · subst k0; show (0 : ℕ) ≤ (s 0).val ∧ (s 0).val < 0 + 2; omega
    · by_cases k1 : ν = 1
      · subst k1; show (0 : ℕ) ≤ (s 1).val ∧ (s 1).val < 0 + 2; omega
      · have k2 := fin3_two k0 k1; subst k2; show (0 : ℕ) ≤ (s 2).val ∧ (s 2).val < 0 + 2; omega
  have hms : periodicLatticeShift s 1 ∈ blockOf (0 : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro ν
    by_cases k0 : ν = 0
    · subst k0; rw [shift1_coord_ne s (by decide)]; show (0 : ℕ) ≤ (s 0).val ∧ (s 0).val < 0 + 2; omega
    · by_cases k1 : ν = 1
      · subst k1; rw [shift1_coord1_val, hc1]
        have h1e : (0 + 1) % (L 1 + 1) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1e]; show (0 : ℕ) ≤ 1 ∧ 1 < 0 + 2; omega
      · have k2 := fin3_two k0 k1; subst k2; rw [shift1_coord_ne s (by decide)]; show (0 : ℕ) ≤ (s 2).val ∧ (s 2).val < 0 + 2; omega
  exact pinDir1 hL C hC (0 : PeriodicLatticeSite L) (BlockFaithful.origin_mem_coarse 2) s h0 hm hms

/-- dir-`2` pin in `B(prevSite 2)` (coord₂ `= L₂-1`, coords `0,1 = 0`). -/
theorem pinPrev2 (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) (s : PeriodicLatticeSite L)
    (hc0 : (s 0).val = 0) (hc1 : (s 1).val = 0) (hc2 : (s 2).val = L 2 - 1) :
    C (s, (2 : Fin 3)) = 0 := by
  have hL2 := hL 2
  have h0 : s 0 = (prevSite 2 : PeriodicLatticeSite L) 0 := by
    rw [prevSite_ne 2 0 (by decide)]; exact Fin.ext (by simpa using hc0)
  have h1 : s 1 = (prevSite 2 : PeriodicLatticeSite L) 1 := by
    rw [prevSite_ne 2 1 (by decide)]; exact Fin.ext (by simpa using hc1)
  have hm : s ∈ blockOf (prevSite 2 : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro ν
    by_cases k0 : ν = 0
    · subst k0; rw [prevSite_ne 2 0 (by decide)]; simp only [Fin.val_zero]; omega
    · by_cases k1 : ν = 1
      · subst k1; rw [prevSite_ne 2 1 (by decide)]; simp only [Fin.val_zero]; omega
      · have k2 := fin3_two k0 k1; subst k2; rw [prevSite_self]; omega
  have hms : periodicLatticeShift s 2 ∈ blockOf (prevSite 2 : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro ν
    by_cases k0 : ν = 0
    · subst k0; rw [prevSite_ne 2 0 (by decide), shift2_coord_ne s (by decide)]; simp only [Fin.val_zero]; omega
    · by_cases k1 : ν = 1
      · subst k1; rw [prevSite_ne 2 1 (by decide), shift2_coord_ne s (by decide)]; simp only [Fin.val_zero]; omega
      · have k2 := fin3_two k0 k1; subst k2; rw [prevSite_self, shift2_coord2_val, hc2]
        rw [show L 2 - 1 + 1 = L 2 by omega, Nat.mod_eq_of_lt (by omega)]; omega
  exact pinDir2 hL C hC (prevSite 2) (prevSite_mem 2 hdvd) s h0 h1 hm hms

/-- dir-`2` pin in `B(0)` (the wrapped coord₂ `= 0`, coords `0,1 = 0`). -/
theorem pinOrig2 (hL : ∀ μ, 4 ≤ L μ) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) (s : PeriodicLatticeSite L)
    (hc0 : (s 0).val = 0) (hc1 : (s 1).val = 0) (hc2 : (s 2).val = 0) :
    C (s, (2 : Fin 3)) = 0 := by
  have hL2 := hL 2
  have h0 : s 0 = (0 : PeriodicLatticeSite L) 0 := Fin.ext (by simpa using hc0)
  have h1 : s 1 = (0 : PeriodicLatticeSite L) 1 := Fin.ext (by simpa using hc1)
  have hm : s ∈ blockOf (0 : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro ν
    by_cases k0 : ν = 0
    · subst k0; show (0 : ℕ) ≤ (s 0).val ∧ (s 0).val < 0 + 2; omega
    · by_cases k1 : ν = 1
      · subst k1; show (0 : ℕ) ≤ (s 1).val ∧ (s 1).val < 0 + 2; omega
      · have k2 := fin3_two k0 k1; subst k2; show (0 : ℕ) ≤ (s 2).val ∧ (s 2).val < 0 + 2; omega
  have hms : periodicLatticeShift s 2 ∈ blockOf (0 : PeriodicLatticeSite L) 2 := by
    rw [mem_blockOf]; intro ν
    by_cases k0 : ν = 0
    · subst k0; rw [shift2_coord_ne s (by decide)]; show (0 : ℕ) ≤ (s 0).val ∧ (s 0).val < 0 + 2; omega
    · by_cases k1 : ν = 1
      · subst k1; rw [shift2_coord_ne s (by decide)]; show (0 : ℕ) ≤ (s 1).val ∧ (s 1).val < 0 + 2; omega
      · have k2 := fin3_two k0 k1; subst k2; rw [shift2_coord2_val, hc2]
        have h2e : (0 + 1) % (L 2 + 1) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h2e]; show (0 : ℕ) ≤ 1 ∧ 1 < 0 + 2; omega
  exact pinDir2 hL C hC (0 : PeriodicLatticeSite L) (BlockFaithful.origin_mem_coarse 2) s h0 h1 hm hms

/-- A direction-`1` bond whose site matches free-cell coord `idx`'s reference site equals
`freeCellBond … idx`. -/
theorem freeIdent1 (hL : ∀ μ, 4 ≤ L μ) (C : Bond L → ℝ) (idx : Fin 80) (s : PeriodicLatticeSite L)
    (q0 : (refSite L hL idx 0).val = (s 0).val) (q1 : (refSite L hL idx 1).val = (s 1).val)
    (q2 : (refSite L hL idx 2).val = (s 2).val) (hd : freeDir idx = 1) :
    C (s, (1 : Fin 3)) = C (freeCellBond L hL idx) := by
  rw [freeCellBond_eq_of_coords hL idx s 1 q0 q1 q2 hd]

/-- A direction-`2` bond whose site matches free-cell coord `idx`'s reference site equals
`freeCellBond … idx`. -/
theorem freeIdent2 (hL : ∀ μ, 4 ≤ L μ) (C : Bond L → ℝ) (idx : Fin 80) (s : PeriodicLatticeSite L)
    (q0 : (refSite L hL idx 0).val = (s 0).val) (q1 : (refSite L hL idx 1).val = (s 1).val)
    (q2 : (refSite L hL idx 2).val = (s 2).val) (hd : freeDir idx = 2) :
    C (s, (2 : Fin 3)) = C (freeCellBond L hL idx) := by
  rw [freeCellBond_eq_of_coords hL idx s 2 q0 q1 q2 hd]


theorem line2_blocksum (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) :
    (∑ x ∈ blockOf (prevSite (2 : Fin 3) : PeriodicLatticeSite L) 2, lineIntegralValue 2 C x 2)
      = 2 * C (freeCellBond L hL 1) + C (freeCellBond L hL 3) + C (freeCellBond L hL 7) + 2 * C (freeCellBond L hL 9) + C (freeCellBond L hL 19) + C (freeCellBond L hL 25) + 2 * C (freeCellBond L hL 28) + C (freeCellBond L hL 31) + C (freeCellBond L hL 34) + 2 * C (freeCellBond L hL 37) := by
  rw [blockOf_fits_eq_image (prevSite 2) 2 (prevSite_fits hL 2), Finset.sum_image (siteFn_inj_mu hL 2)]
  rw [show (Finset.univ : Finset (Fin 3 → Fin 2)) =
      { ![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1], ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1] } from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [lineIntegralValue_two]
  have b1_000 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = 0 := by
    apply pinPrev2 hL hdvd C hC
    · simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
  have b2_000 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (2 : Fin 3)) = C (freeCellBond L hL 1) := by
    apply freeIdent2 hL C 1 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 1 0 0 (by decide), (coordNat_vals (L:=L) 0).1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 1 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 1 2 4 (by decide), (coordNat_vals (L:=L) 2).2.2]
      rw [shift2_coord2_val]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
  have b1_001 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 1) := by
    apply freeIdent2 hL C 1 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 1 0 0 (by decide), (coordNat_vals (L:=L) 0).1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 1 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 1 2 4 (by decide), (coordNat_vals (L:=L) 2).2.2]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
  have b2_001 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (2 : Fin 3)) = 0 := by
    apply pinOrig2 hL C hC
    · rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [shift2_coord2_val]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
  have b1_010 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 7) := by
    apply freeIdent2 hL C 7 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 7 0 0 (by decide), (coordNat_vals (L:=L) 0).1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 7 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 7 2 3 (by decide), coordNat3 2]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
  have b2_010 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (2 : Fin 3)) = C (freeCellBond L hL 9) := by
    apply freeIdent2 hL C 9 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 9 0 0 (by decide), (coordNat_vals (L:=L) 0).1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 9 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 9 2 4 (by decide), (coordNat_vals (L:=L) 2).2.2]
      rw [shift2_coord2_val]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
  have b1_011 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 9) := by
    apply freeIdent2 hL C 9 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 9 0 0 (by decide), (coordNat_vals (L:=L) 0).1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 9 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 9 2 4 (by decide), (coordNat_vals (L:=L) 2).2.2]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
  have b2_011 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (2 : Fin 3)) = C (freeCellBond L hL 3) := by
    apply freeIdent2 hL C 3 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 3 0 0 (by decide), (coordNat_vals (L:=L) 0).1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 3 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 3 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      rw [shift2_coord2_val]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
  have b1_100 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 25) := by
    apply freeIdent2 hL C 25 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 25 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 25 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 25 2 3 (by decide), coordNat3 2]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
  have b2_100 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (2 : Fin 3)) = C (freeCellBond L hL 28) := by
    apply freeIdent2 hL C 28 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 28 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 28 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 28 2 4 (by decide), (coordNat_vals (L:=L) 2).2.2]
      rw [shift2_coord2_val]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
  have b1_101 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 28) := by
    apply freeIdent2 hL C 28 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 28 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 28 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 28 2 4 (by decide), (coordNat_vals (L:=L) 2).2.2]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
  have b2_101 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (2 : Fin 3)) = C (freeCellBond L hL 19) := by
    apply freeIdent2 hL C 19 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 19 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 19 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 19 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      rw [shift2_coord2_val]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
  have b1_110 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 34) := by
    apply freeIdent2 hL C 34 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 34 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 34 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 34 2 3 (by decide), coordNat3 2]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
  have b2_110 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (2 : Fin 3)) = C (freeCellBond L hL 37) := by
    apply freeIdent2 hL C 37 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 37 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 37 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 37 2 4 (by decide), (coordNat_vals (L:=L) 2).2.2]
      rw [shift2_coord2_val]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
  have b1_111 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 37) := by
    apply freeIdent2 hL C 37 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 37 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 37 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 37 2 4 (by decide), (coordNat_vals (L:=L) 2).2.2]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
  have b2_111 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (2 : Fin 3)) = C (freeCellBond L hL 31) := by
    apply freeIdent2 hL C 31 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 31 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 31 1 1 (by decide), (coordNat_vals (L:=L) 1).2.1]
      rw [shift2_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 2; omega)
    · rw [refSite_val hL 31 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      rw [shift2_coord2_val]
      simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
  rw [b1_000, b2_000, b1_001, b2_001, b1_010, b2_010, b1_011, b2_011, b1_100, b2_100, b1_101, b2_101, b1_110, b2_110, b1_111, b2_111]
  ring

theorem line_reindex2 (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) :
    lineCoarseRestrict 2 C (⟨prevSite 2, prevSite_mem 2 hdvd⟩, 2)
      = (1 / 8) * (freecoord L hL C 1 + freecoord L hL C 9 + freecoord L hL C 28 + freecoord L hL C 37) + (1 / 16) * (freecoord L hL C 3 + freecoord L hL C 7 + freecoord L hL C 19 + freecoord L hL C 25 + freecoord L hL C 31 + freecoord L hL C 34) := by
  simp only [freecoord_apply]
  rw [lineCoarseRestrict, line2_blocksum hL hdvd C hC]
  push_cast
  ring

theorem line1_blocksum (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) :
    (∑ x ∈ blockOf (prevSite (1 : Fin 3) : PeriodicLatticeSite L) 2, lineIntegralValue 2 C x 1)
      = 2 * C (freeCellBond L hL 12) + 2 * C (freeCellBond L hL 14) + 2 * C (freeCellBond L hL 48) + 2 * C (freeCellBond L hL 51) + C (freeCellBond L hL 18) + C (freeCellBond L hL 21) + C (freeCellBond L hL 41) + C (freeCellBond L hL 44) := by
  rw [blockOf_fits_eq_image (prevSite 1) 2 (prevSite_fits hL 1), Finset.sum_image (siteFn_inj_mu hL 1)]
  rw [show (Finset.univ : Finset (Fin 3 → Fin 2)) =
      { ![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1], ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1] } from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [lineIntegralValue_two]
  have b1_000 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = 0 := by
    apply pinPrev1 hL hdvd C hC
    · simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b2_000 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (1 : Fin 3)) = C (freeCellBond L hL 12) := by
    apply freeIdent1 hL C 12 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 12 0 0 (by decide), (coordNat_vals (L:=L) 0).1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 12 1 4 (by decide), (coordNat_vals (L:=L) 1).2.2]
      rw [shift1_coord1_val]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
    · rw [refSite_val hL 12 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b1_001 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = 0 := by
    apply pinPrev1 hL hdvd C hC
    · simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b2_001 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (1 : Fin 3)) = C (freeCellBond L hL 14) := by
    apply freeIdent1 hL C 14 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 14 0 0 (by decide), (coordNat_vals (L:=L) 0).1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 14 1 4 (by decide), (coordNat_vals (L:=L) 1).2.2]
      rw [shift1_coord1_val]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
    · rw [refSite_val hL 14 2 1 (by decide), (coordNat_vals (L:=L) 2).2.1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b1_010 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 12) := by
    apply freeIdent1 hL C 12 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 12 0 0 (by decide), (coordNat_vals (L:=L) 0).1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 12 1 4 (by decide), (coordNat_vals (L:=L) 1).2.2]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 12 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b2_010 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (1 : Fin 3)) = 0 := by
    apply pinOrig1 hL C hC
    · rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [shift1_coord1_val]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
    · rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b1_011 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 14) := by
    apply freeIdent1 hL C 14 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 14 0 0 (by decide), (coordNat_vals (L:=L) 0).1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 14 1 4 (by decide), (coordNat_vals (L:=L) 1).2.2]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 14 2 1 (by decide), (coordNat_vals (L:=L) 2).2.1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b2_011 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (1 : Fin 3)) = 0 := by
    apply pinOrig1 hL C hC
    · rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [shift1_coord1_val]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
    · rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b1_100 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 41) := by
    apply freeIdent1 hL C 41 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 41 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 41 1 3 (by decide), coordNat3 1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 41 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b2_100 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (1 : Fin 3)) = C (freeCellBond L hL 48) := by
    apply freeIdent1 hL C 48 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 48 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 48 1 4 (by decide), (coordNat_vals (L:=L) 1).2.2]
      rw [shift1_coord1_val]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
    · rw [refSite_val hL 48 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b1_101 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 44) := by
    apply freeIdent1 hL C 44 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 44 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 44 1 3 (by decide), coordNat3 1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 44 2 1 (by decide), (coordNat_vals (L:=L) 2).2.1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b2_101 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (1 : Fin 3)) = C (freeCellBond L hL 51) := by
    apply freeIdent1 hL C 51 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 51 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 51 1 4 (by decide), (coordNat_vals (L:=L) 1).2.2]
      rw [shift1_coord1_val]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
    · rw [refSite_val hL 51 2 1 (by decide), (coordNat_vals (L:=L) 2).2.1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b1_110 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 48) := by
    apply freeIdent1 hL C 48 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 48 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 48 1 4 (by decide), (coordNat_vals (L:=L) 1).2.2]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 48 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b2_110 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (1 : Fin 3)) = C (freeCellBond L hL 18) := by
    apply freeIdent1 hL C 18 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 18 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 18 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      rw [shift1_coord1_val]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
    · rw [refSite_val hL 18 2 0 (by decide), (coordNat_vals (L:=L) 2).1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b1_111 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 51) := by
    apply freeIdent1 hL C 51 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 51 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 51 1 4 (by decide), (coordNat_vals (L:=L) 1).2.2]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 51 2 1 (by decide), (coordNat_vals (L:=L) 2).2.1]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  have b2_111 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (1 : Fin 3)) = C (freeCellBond L hL 21) := by
    apply freeIdent1 hL C 21 _ ?_ ?_ ?_ (by decide)
    · rw [refSite_val hL 21 0 1 (by decide), (coordNat_vals (L:=L) 0).2.1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
    · rw [refSite_val hL 21 1 0 (by decide), (coordNat_vals (L:=L) 1).1]
      rw [shift1_coord1_val]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
      rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
    · rw [refSite_val hL 21 2 1 (by decide), (coordNat_vals (L:=L) 2).2.1]
      rw [shift1_coord_ne _ (by decide)]
      simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero] <;> first | rfl | omega | (have := hL 1; omega)
  rw [b1_000, b2_000, b1_001, b2_001, b1_010, b2_010, b1_011, b2_011, b1_100, b2_100, b1_101, b2_101, b1_110, b2_110, b1_111, b2_111]
  ring

theorem line_reindex1 (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) :
    lineCoarseRestrict 2 C (⟨prevSite 1, prevSite_mem 1 hdvd⟩, 1)
      = (1 / 8) * (freecoord L hL C 12 + freecoord L hL C 14 + freecoord L hL C 48 + freecoord L hL C 51) + (1 / 16) * (freecoord L hL C 18 + freecoord L hL C 21 + freecoord L hL C 41 + freecoord L hL C 44) := by
  simp only [freecoord_apply]
  rw [lineCoarseRestrict, line1_blocksum hL hdvd C hC]
  push_cast
  ring


#print axioms line0_blocksum
#print axioms line_reindex0
#print axioms line2_blocksum
#print axioms line_reindex2
#print axioms line1_blocksum
#print axioms line_reindex1


/-! ## Slab-reindex, step 1: the `slabPlaqs` enumeration.

`slabPlaqs (⟨prevSite κ,_⟩, κ)` factors as `blockOf (prevSite κ) 2 ×ˢ {the two direction pairs
containing κ}`.  Ground truth `compute/href_qslab/curl_breakdown.py` (self-hash eccafad5c0810309):
16 plaquettes per κ = 8 block sites × 2 direction pairs. -/

/-- The three plaquette direction pairs `(0,1),(0,2),(1,2)`. -/
def pdir01 : PeriodicPlaquetteDirections := ⟨(0, 1), by decide⟩
def pdir02 : PeriodicPlaquetteDirections := ⟨(0, 2), by decide⟩
def pdir12 : PeriodicPlaquetteDirections := ⟨(1, 2), by decide⟩

/-- `coordNat` code-value helpers (simp-usable). -/
theorem coordNat0 (ν : Fin 3) : coordNat L ν 0 = 0 := (coordNat_vals ν).1
theorem coordNat1 (ν : Fin 3) : coordNat L ν 1 = 1 := (coordNat_vals ν).2.1
theorem coordNat2 (ν : Fin 3) : coordNat L ν 2 = 2 := by simp [coordNat]
theorem coordNat4 (ν : Fin 3) : coordNat L ν 4 = L ν := (coordNat_vals ν).2.2

/-- Generic direction-`0` pin: a dir-`0` bond with both endpoints in a common coarse block vanishes
on the admissible subspace. -/
theorem pinDir0 (hL : ∀ μ, 4 ≤ L μ) (C : Bond L → ℝ) (hC : C ∈ admissibleSubspaceInter L 2)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L 2) (s : PeriodicLatticeSite L)
    (hm : s ∈ blockOf y 2) (hms : periodicLatticeShift s 0 ∈ blockOf y 2) :
    C (s, (0 : Fin 3)) = 0 :=
  dir0_bond_eq_zero (by have := hL 0; omega) C hC y hy (s, 0) rfl ⟨hm, hms⟩

/-- A coarse block origin built from three coordinate codes (`coordFin` per axis). -/
def codeOriginSite (hL : ∀ μ, 4 ≤ L μ) (c : Fin 3 → Fin 5) : PeriodicLatticeSite L :=
  fun ν => coordFin L ν (hL ν) (c ν)

theorem codeOriginSite_val (hL : ∀ μ, 4 ≤ L μ) (c : Fin 3 → Fin 5) (ν : Fin 3) :
    (codeOriginSite hL c ν).val = coordNat L ν (c ν) := rfl

/-- A `codeOriginSite` is coarse if each of its `coordNat` values is even. -/
theorem codeOriginSite_coarse (hL : ∀ μ, 4 ≤ L μ) (c : Fin 3 → Fin 5)
    (hc : ∀ ν, (coordNat L ν (c ν)) % 2 = 0) :
    codeOriginSite hL c ∈ CoarseLattice L 2 := by
  rw [mem_CoarseLattice]; intro ν; rw [codeOriginSite_val]; exact hc ν

/-- Coarse-block origin from three explicit codes, given per-axis evenness. -/
theorem codeOriginSite_coarse3 (hL : ∀ μ, 4 ≤ L μ) (c0 c1 c2 : Fin 5)
    (h0 : (coordNat L 0 c0) % 2 = 0) (h1 : (coordNat L 1 c1) % 2 = 0)
    (h2 : (coordNat L 2 c2) % 2 = 0) :
    codeOriginSite hL ![c0, c1, c2] ∈ CoarseLattice L 2 := by
  apply codeOriginSite_coarse hL
  intro ν; fin_cases ν
  · exact h0
  · exact h1
  · exact h2

/-- Block membership into a `codeOriginSite` block from per-axis coordinate bounds. -/
theorem mem_block_codeOrigin (hL : ∀ μ, 4 ≤ L μ) (c0 c1 c2 : Fin 5) (s : PeriodicLatticeSite L)
    (h0 : (coordNat L 0 c0) ≤ (s 0).val ∧ (s 0).val < (coordNat L 0 c0) + 2)
    (h1 : (coordNat L 1 c1) ≤ (s 1).val ∧ (s 1).val < (coordNat L 1 c1) + 2)
    (h2 : (coordNat L 2 c2) ≤ (s 2).val ∧ (s 2).val < (coordNat L 2 c2) + 2) :
    s ∈ blockOf (codeOriginSite hL ![c0, c1, c2]) 2 := by
  rw [mem_blockOf]; intro ν; rw [codeOriginSite_val]; fin_cases ν
  · exact h0
  · exact h1
  · exact h2

/-- **`slabPlaqs` at `prevSite κ` factors (PROVED).** The plaquettes credited by the coarse bond
`(⟨prevSite κ,_⟩, κ)` are exactly `block(prevSite κ) ×ˢ {directions containing κ}`.  The direction
finset `D` is supplied concretely (`decide`d) per axis. -/
theorem slabPlaqs_prevSite (κ : Fin 3) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (D : Finset PeriodicPlaquetteDirections)
    (hD : (Finset.univ.filter
        (fun d : PeriodicPlaquetteDirections => κ = (d.1).1 ∨ κ = (d.1).2)) = D) :
    slabPlaqs (⟨prevSite κ, prevSite_mem κ hdvd⟩, κ)
      = blockOf (prevSite κ : PeriodicLatticeSite L) 2 ×ˢ D := by
  ext p
  simp only [slabPlaqs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, ← hD]
  tauto







/-! ## Slab-reindex, step 2: the mu=0 curl block (generated by gen_curls.py). -/

theorem slabsum0 (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) :
    (∑ p ∈ slabPlaqs (⟨prevSite (0 : Fin 3), prevSite_mem 0 hdvd⟩, 0), (curlValue C p) ^ 2)
      = (freecoord L hL C 65)^2 + (freecoord L hL C 66)^2 + (freecoord L hL C 68)^2 + (freecoord L hL C 69 - freecoord L hL C 59)^2 + (freecoord L hL C 72 - freecoord L hL C 60)^2 + (freecoord L hL C 73 - freecoord L hL C 61)^2 + (freecoord L hL C 75 - freecoord L hL C 62)^2 + (freecoord L hL C 76 - freecoord L hL C 63)^2 + (freecoord L hL C 64 - freecoord L hL C 71 - freecoord L hL C 65)^2 + (freecoord L hL C 64 - freecoord L hL C 67 - freecoord L hL C 66)^2 + (freecoord L hL C 67 - freecoord L hL C 74 - freecoord L hL C 68)^2 + (freecoord L hL C 67 + freecoord L hL C 0 - freecoord L hL C 70 - freecoord L hL C 69)^2 + (freecoord L hL C 71 + freecoord L hL C 2 - freecoord L hL C 78 - freecoord L hL C 72)^2 + (freecoord L hL C 71 + freecoord L hL C 3 - freecoord L hL C 74 - freecoord L hL C 73)^2 + (freecoord L hL C 74 + freecoord L hL C 4 - freecoord L hL C 79 - freecoord L hL C 75)^2 + (freecoord L hL C 74 + freecoord L hL C 5 - freecoord L hL C 77 - freecoord L hL C 76)^2 := by
  rw [slabPlaqs_prevSite 0 hdvd {pdir01, pdir02} (by decide)]
  rw [Finset.sum_product]
  rw [blockOf_fits_eq_image (prevSite 0) 2 (prevSite_fits hL 0), Finset.sum_image (siteFn_inj_mu hL 0)]
  rw [show (Finset.univ : Finset (Fin 3 → Fin 2)) =
      { ![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1], ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1] } from by decide]
  simp only [Finset.sum_pair (by decide : pdir01 ≠ pdir02)]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  have cv000_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 65) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c000_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c000_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 65) := by
      apply freeIdent1 hL C 65 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 65 0 4 (by decide), coordNat4 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 65 1 0 (by decide), coordNat0 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 65 2 0 (by decide), coordNat0 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c000_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c000_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat3]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    rw [c000_01_0, c000_01_1, c000_01_2, c000_01_3]
    try ring
  have cv000_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 66) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c000_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c000_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 66) := by
      apply freeIdent2 hL C 66 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 66 0 4 (by decide), coordNat4 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 66 1 0 (by decide), coordNat0 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 66 2 0 (by decide), coordNat0 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c000_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
    have c000_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = 0 := by
      apply pinDir2 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat3]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]) <;> (try rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]) <;> (try rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))])
          all_goals omega
    rw [c000_02_0, c000_02_1, c000_02_2, c000_02_3]
    try ring
  have cv001_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 68) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c001_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c001_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 68) := by
      apply freeIdent1 hL C 68 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 68 0 4 (by decide), coordNat4 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 68 1 0 (by decide), coordNat0 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 68 2 1 (by decide), coordNat1 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c001_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c001_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat3]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    rw [c001_01_0, c001_01_1, c001_01_2, c001_01_3]
    try ring
  have cv001_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 69 - freecoord L hL C 59) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c001_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c001_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 69) := by
      apply freeIdent2 hL C 69 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 69 0 4 (by decide), coordNat4 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 69 1 0 (by decide), coordNat0 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 69 2 1 (by decide), coordNat1 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c001_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,2])
        (codeOriginSite_coarse3 hL 3 0 2 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 2
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 2
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
    have c001_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 59) := by
      apply freeIdent2 hL C 59 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 59 0 3 (by decide), coordNat3 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 59 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 59 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c001_02_0, c001_02_1, c001_02_2, c001_02_3]
    try ring
  have cv010_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 72 - freecoord L hL C 60) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c010_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c010_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 72) := by
      apply freeIdent1 hL C 72 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 72 0 4 (by decide), coordNat4 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 72 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 72 2 0 (by decide), coordNat0 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c010_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,2,0])
        (codeOriginSite_coarse3 hL 3 2 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 2 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 2 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c010_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 60) := by
      apply freeIdent1 hL C 60 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 60 0 3 (by decide), coordNat3 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 60 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 60 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c010_01_0, c010_01_1, c010_01_2, c010_01_3]
    try ring
  have cv010_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 73 - freecoord L hL C 61) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c010_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c010_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 73) := by
      apply freeIdent2 hL C 73 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 73 0 4 (by decide), coordNat4 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 73 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 73 2 0 (by decide), coordNat0 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c010_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
    have c010_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 61) := by
      apply freeIdent2 hL C 61 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 61 0 3 (by decide), coordNat3 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 61 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 61 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c010_02_0, c010_02_1, c010_02_2, c010_02_3]
    try ring
  have cv011_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 75 - freecoord L hL C 62) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c011_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c011_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 75) := by
      apply freeIdent1 hL C 75 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 75 0 4 (by decide), coordNat4 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 75 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 75 2 1 (by decide), coordNat1 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c011_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,2,0])
        (codeOriginSite_coarse3 hL 3 2 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 2 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 2 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c011_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 62) := by
      apply freeIdent1 hL C 62 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 62 0 3 (by decide), coordNat3 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 62 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 62 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c011_01_0, c011_01_1, c011_01_2, c011_01_3]
    try ring
  have cv011_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 76 - freecoord L hL C 63) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c011_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,0])
        (codeOriginSite_coarse3 hL 3 0 0 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c011_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 76) := by
      apply freeIdent2 hL C 76 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 76 0 4 (by decide), coordNat4 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 76 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 76 2 1 (by decide), coordNat1 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c011_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![3,0,2])
        (codeOriginSite_coarse3 hL 3 0 2 (by rw [coordNat3]; have := hdvd 0; omega) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 3 0 2
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
      · apply mem_block_codeOrigin hL 3 0 2
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord0_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
    have c011_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 63) := by
      apply freeIdent2 hL C 63 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 63 0 3 (by decide), coordNat3 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 63 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 63 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c011_02_0, c011_02_1, c011_02_2, c011_02_3]
    try ring
  have cv100_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 64 - freecoord L hL C 71 - freecoord L hL C 65) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c100_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 64) := by
      apply freeIdent0 hL C 64 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 64 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 64 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 64 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c100_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,0,0])
        (codeOriginSite_coarse3 hL 0 0 0 (by simp [coordNat]) (by simp [coordNat]) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c100_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = C (freeCellBond L hL 71) := by
      apply freeIdent0 hL C 71 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 71 0 4 (by decide), coordNat4 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 71 1 1 (by decide), coordNat1 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 71 2 0 (by decide), coordNat0 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c100_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 65) := by
      apply freeIdent1 hL C 65 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 65 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 65 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 65 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c100_01_0, c100_01_1, c100_01_2, c100_01_3]
    try ring
  have cv100_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 64 - freecoord L hL C 67 - freecoord L hL C 66) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c100_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 64) := by
      apply freeIdent0 hL C 64 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 64 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 64 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 64 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c100_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = 0 := by
      apply pinDir2 hL C hC (codeOriginSite hL ![0,0,0])
        (codeOriginSite_coarse3 hL 0 0 0 (by simp [coordNat]) (by simp [coordNat]) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
        all_goals omega
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord2_val]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]) <;> (try rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]) <;> (try rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))])
          all_goals omega
    have c100_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = C (freeCellBond L hL 67) := by
      apply freeIdent0 hL C 67 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 67 0 4 (by decide), coordNat4 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 67 1 0 (by decide), coordNat0 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 67 2 1 (by decide), coordNat1 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c100_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 66) := by
      apply freeIdent2 hL C 66 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 66 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 66 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 66 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c100_02_0, c100_02_1, c100_02_2, c100_02_3]
    try ring
  have cv101_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 67 - freecoord L hL C 74 - freecoord L hL C 68) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c101_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 67) := by
      apply freeIdent0 hL C 67 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 67 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 67 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 67 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,0,0])
        (codeOriginSite_coarse3 hL 0 0 0 (by simp [coordNat]) (by simp [coordNat]) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c101_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = C (freeCellBond L hL 74) := by
      apply freeIdent0 hL C 74 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 0 4 (by decide), coordNat4 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 1 1 (by decide), coordNat1 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 2 1 (by decide), coordNat1 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 68) := by
      apply freeIdent1 hL C 68 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 68 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 68 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 68 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c101_01_0, c101_01_1, c101_01_2, c101_01_3]
    try ring
  have cv101_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 67 + freecoord L hL C 0 - freecoord L hL C 70 - freecoord L hL C 69) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c101_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 67) := by
      apply freeIdent0 hL C 67 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 67 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 67 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 67 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 0) := by
      apply freeIdent2 hL C 0 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 0 0 0 (by decide), coordNat0 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 0 1 0 (by decide), coordNat0 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 0 2 1 (by decide), coordNat1 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = C (freeCellBond L hL 70) := by
      apply freeIdent0 hL C 70 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 70 0 4 (by decide), coordNat4 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 70 1 0 (by decide), coordNat0 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 70 2 2 (by decide), coordNat2 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c101_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 69) := by
      apply freeIdent2 hL C 69 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 69 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 69 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 69 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c101_02_0, c101_02_1, c101_02_2, c101_02_3]
    try ring
  have cv110_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 71 + freecoord L hL C 2 - freecoord L hL C 78 - freecoord L hL C 72) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c110_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 71) := by
      apply freeIdent0 hL C 71 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 71 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 71 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 71 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 2) := by
      apply freeIdent1 hL C 2 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 2 0 0 (by decide), coordNat0 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 2 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 2 2 0 (by decide), coordNat0 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = C (freeCellBond L hL 78) := by
      apply freeIdent0 hL C 78 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 78 0 4 (by decide), coordNat4 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 78 1 2 (by decide), coordNat2 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 78 2 0 (by decide), coordNat0 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 72) := by
      apply freeIdent1 hL C 72 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 72 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 72 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 72 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c110_01_0, c110_01_1, c110_01_2, c110_01_3]
    try ring
  have cv110_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 71 + freecoord L hL C 3 - freecoord L hL C 74 - freecoord L hL C 73) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c110_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 71) := by
      apply freeIdent0 hL C 71 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 71 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 71 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 71 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 3) := by
      apply freeIdent2 hL C 3 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 3 0 0 (by decide), coordNat0 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 3 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 3 2 0 (by decide), coordNat0 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = C (freeCellBond L hL 74) := by
      apply freeIdent0 hL C 74 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 0 4 (by decide), coordNat4 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 1 1 (by decide), coordNat1 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 2 1 (by decide), coordNat1 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c110_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 73) := by
      apply freeIdent2 hL C 73 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 73 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 73 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 73 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c110_02_0, c110_02_1, c110_02_2, c110_02_3]
    try ring
  have cv111_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 74 + freecoord L hL C 4 - freecoord L hL C 79 - freecoord L hL C 75) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c111_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 74) := by
      apply freeIdent0 hL C 74 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 4) := by
      apply freeIdent1 hL C 4 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 4 0 0 (by decide), coordNat0 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 4 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 4 2 1 (by decide), coordNat1 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = C (freeCellBond L hL 79) := by
      apply freeIdent0 hL C 79 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 79 0 4 (by decide), coordNat4 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 79 1 2 (by decide), coordNat2 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 79 2 1 (by decide), coordNat1 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 75) := by
      apply freeIdent1 hL C 75 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 75 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 75 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 75 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c111_01_0, c111_01_1, c111_01_2, c111_01_3]
    try ring
  have cv111_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 74 + freecoord L hL C 5 - freecoord L hL C 77 - freecoord L hL C 76) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c111_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 74) := by
      apply freeIdent0 hL C 74 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 74 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 5) := by
      apply freeIdent2 hL C 5 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 5 0 0 (by decide), coordNat0 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 5 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 5 2 1 (by decide), coordNat1 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = C (freeCellBond L hL 77) := by
      apply freeIdent0 hL C 77 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 77 0 4 (by decide), coordNat4 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 77 1 1 (by decide), coordNat1 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 77 2 2 (by decide), coordNat2 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c111_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (0:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (0:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 76) := by
      apply freeIdent2 hL C 76 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 76 0 4 (by decide), coordNat4 0]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 76 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 76 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 0 1 (by decide), prevSite_ne 0 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c111_02_0, c111_02_1, c111_02_2, c111_02_3]
    try ring
  rw [cv000_01, cv000_02, cv001_01, cv001_02, cv010_01, cv010_02, cv011_01, cv011_02, cv100_01, cv100_02, cv101_01, cv101_02, cv110_01, cv110_02, cv111_01, cv111_02]
  try ring


#print axioms slabsum0

/-! ## Slab-reindex: the mu=1 curl block. -/

theorem slabsum1 (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) :
    (∑ p ∈ slabPlaqs (⟨prevSite (1 : Fin 3), prevSite_mem 1 hdvd⟩, 1), (curlValue C p) ^ 2)
      = (freecoord L hL C 41)^2 + (freecoord L hL C 13)^2 + (freecoord L hL C 44)^2 + (freecoord L hL C 15 - freecoord L hL C 11)^2 + (freecoord L hL C 48 - freecoord L hL C 12)^2 + (freecoord L hL C 12 - freecoord L hL C 14 - freecoord L hL C 13)^2 + (freecoord L hL C 51 - freecoord L hL C 14)^2 + (freecoord L hL C 14 + freecoord L hL C 0 - freecoord L hL C 16 - freecoord L hL C 15)^2 + (freecoord L hL C 40 - freecoord L hL C 47 - freecoord L hL C 41)^2 + (freecoord L hL C 41 + freecoord L hL C 49 - freecoord L hL C 44 - freecoord L hL C 42)^2 + (freecoord L hL C 43 - freecoord L hL C 50 - freecoord L hL C 44)^2 + (freecoord L hL C 44 + freecoord L hL C 52 - freecoord L hL C 46 - freecoord L hL C 45)^2 + (freecoord L hL C 47 + freecoord L hL C 57 - freecoord L hL C 17 - freecoord L hL C 48)^2 + (freecoord L hL C 48 + freecoord L hL C 19 - freecoord L hL C 51 - freecoord L hL C 49)^2 + (freecoord L hL C 50 + freecoord L hL C 58 - freecoord L hL C 20 - freecoord L hL C 51)^2 + (freecoord L hL C 51 + freecoord L hL C 22 - freecoord L hL C 53 - freecoord L hL C 52)^2 := by
  rw [slabPlaqs_prevSite 1 hdvd {pdir01, pdir12} (by decide)]
  rw [Finset.sum_product]
  rw [blockOf_fits_eq_image (prevSite 1) 2 (prevSite_fits hL 1), Finset.sum_image (siteFn_inj_mu hL 1)]
  rw [show (Finset.univ : Finset (Fin 3 → Fin 2)) =
      { ![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1], ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1] } from by decide]
  simp only [Finset.sum_pair (by decide : pdir01 ≠ pdir12)]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  have cv000_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 41) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c000_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c000_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 41) := by
      apply freeIdent1 hL C 41 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 41 0 1 (by decide), coordNat1 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 41 1 3 (by decide), coordNat3 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 41 2 0 (by decide), coordNat0 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c000_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c000_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    rw [c000_01_0, c000_01_1, c000_01_2, c000_01_3]
    try ring
  have cv000_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 13) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c000_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c000_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 13) := by
      apply freeIdent2 hL C 13 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 13 0 0 (by decide), coordNat0 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 13 1 4 (by decide), coordNat4 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 13 2 0 (by decide), coordNat0 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c000_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord1_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
    have c000_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = 0 := by
      apply pinDir2 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat3]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]) <;> (try rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]) <;> (try rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))])
          all_goals omega
    rw [c000_12_0, c000_12_1, c000_12_2, c000_12_3]
    try ring
  have cv001_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 44) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c001_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c001_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 44) := by
      apply freeIdent1 hL C 44 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 0 1 (by decide), coordNat1 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 1 3 (by decide), coordNat3 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 2 1 (by decide), coordNat1 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c001_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c001_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    rw [c001_01_0, c001_01_1, c001_01_2, c001_01_3]
    try ring
  have cv001_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 15 - freecoord L hL C 11) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c001_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c001_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 15) := by
      apply freeIdent2 hL C 15 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 15 0 0 (by decide), coordNat0 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 15 1 4 (by decide), coordNat4 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 15 2 1 (by decide), coordNat1 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c001_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,3,2])
        (codeOriginSite_coarse3 hL 0 3 2 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 3 2
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 2
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord1_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
    have c001_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 11) := by
      apply freeIdent2 hL C 11 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 11 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 11 1 3 (by decide), coordNat3 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 11 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c001_12_0, c001_12_1, c001_12_2, c001_12_3]
    try ring
  have cv010_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 48 - freecoord L hL C 12) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c010_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c010_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 48) := by
      apply freeIdent1 hL C 48 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 48 0 1 (by decide), coordNat1 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 48 1 4 (by decide), coordNat4 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 48 2 0 (by decide), coordNat0 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c010_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,0,0])
        (codeOriginSite_coarse3 hL 0 0 0 (by simp [coordNat]) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c010_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 12) := by
      apply freeIdent1 hL C 12 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 12 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 12 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 12 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c010_01_0, c010_01_1, c010_01_2, c010_01_3]
    try ring
  have cv010_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 12 - freecoord L hL C 14 - freecoord L hL C 13) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c010_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 12) := by
      apply freeIdent1 hL C 12 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 12 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 12 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 12 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c010_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = 0 := by
      apply pinDir2 hL C hC (codeOriginSite hL ![0,0,0])
        (codeOriginSite_coarse3 hL 0 0 0 (by simp [coordNat]) (by simp [coordNat]) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord2_val]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]) <;> (try rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]) <;> (try rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))])
          all_goals omega
    have c010_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 14) := by
      apply freeIdent1 hL C 14 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 14 0 0 (by decide), coordNat0 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 14 1 4 (by decide), coordNat4 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 14 2 1 (by decide), coordNat1 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c010_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 13) := by
      apply freeIdent2 hL C 13 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 13 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 13 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 13 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c010_12_0, c010_12_1, c010_12_2, c010_12_3]
    try ring
  have cv011_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 51 - freecoord L hL C 14) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c011_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,3,0])
        (codeOriginSite_coarse3 hL 0 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c011_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 51) := by
      apply freeIdent1 hL C 51 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 0 1 (by decide), coordNat1 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 1 4 (by decide), coordNat4 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 2 1 (by decide), coordNat1 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c011_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,0,0])
        (codeOriginSite_coarse3 hL 0 0 0 (by simp [coordNat]) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c011_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 14) := by
      apply freeIdent1 hL C 14 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 14 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 14 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 14 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c011_01_0, c011_01_1, c011_01_2, c011_01_3]
    try ring
  have cv011_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 14 + freecoord L hL C 0 - freecoord L hL C 16 - freecoord L hL C 15) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c011_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 14) := by
      apply freeIdent1 hL C 14 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 14 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 14 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 14 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c011_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 0) := by
      apply freeIdent2 hL C 0 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 0 0 0 (by decide), coordNat0 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 0 1 0 (by decide), coordNat0 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 0 2 1 (by decide), coordNat1 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c011_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 16) := by
      apply freeIdent1 hL C 16 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 16 0 0 (by decide), coordNat0 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 16 1 4 (by decide), coordNat4 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 16 2 2 (by decide), coordNat2 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c011_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 15) := by
      apply freeIdent2 hL C 15 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 15 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 15 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 15 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c011_12_0, c011_12_1, c011_12_2, c011_12_3]
    try ring
  have cv100_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 40 - freecoord L hL C 47 - freecoord L hL C 41) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c100_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 40) := by
      apply freeIdent0 hL C 40 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 40 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 40 1 3 (by decide), coordNat3 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 40 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c100_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![2,3,0])
        (codeOriginSite_coarse3 hL 2 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat2]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · apply mem_block_codeOrigin hL 2 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 2 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord1_val]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c100_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = C (freeCellBond L hL 47) := by
      apply freeIdent0 hL C 47 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 47 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 47 1 4 (by decide), coordNat4 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 47 2 0 (by decide), coordNat0 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c100_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 41) := by
      apply freeIdent1 hL C 41 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 41 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 41 1 3 (by decide), coordNat3 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 41 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c100_01_0, c100_01_1, c100_01_2, c100_01_3]
    try ring
  have cv100_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 41 + freecoord L hL C 49 - freecoord L hL C 44 - freecoord L hL C 42) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c100_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 41) := by
      apply freeIdent1 hL C 41 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 41 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 41 1 3 (by decide), coordNat3 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 41 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c100_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 49) := by
      apply freeIdent2 hL C 49 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 49 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 49 1 4 (by decide), coordNat4 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 49 2 0 (by decide), coordNat0 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c100_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 44) := by
      apply freeIdent1 hL C 44 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 1 3 (by decide), coordNat3 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 2 1 (by decide), coordNat1 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c100_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 42) := by
      apply freeIdent2 hL C 42 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 42 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 42 1 3 (by decide), coordNat3 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 42 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c100_12_0, c100_12_1, c100_12_2, c100_12_3]
    try ring
  have cv101_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 43 - freecoord L hL C 50 - freecoord L hL C 44) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c101_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 43) := by
      apply freeIdent0 hL C 43 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 43 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 43 1 3 (by decide), coordNat3 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 43 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![2,3,0])
        (codeOriginSite_coarse3 hL 2 3 0 (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 1; omega) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat2]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · apply mem_block_codeOrigin hL 2 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 2 3 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord1_val]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c101_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = C (freeCellBond L hL 50) := by
      apply freeIdent0 hL C 50 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 50 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 50 1 4 (by decide), coordNat4 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 50 2 1 (by decide), coordNat1 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 44) := by
      apply freeIdent1 hL C 44 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 1 3 (by decide), coordNat3 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c101_01_0, c101_01_1, c101_01_2, c101_01_3]
    try ring
  have cv101_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 44 + freecoord L hL C 52 - freecoord L hL C 46 - freecoord L hL C 45) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c101_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 44) := by
      apply freeIdent1 hL C 44 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 1 3 (by decide), coordNat3 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 44 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 52) := by
      apply freeIdent2 hL C 52 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 52 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 52 1 4 (by decide), coordNat4 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 52 2 1 (by decide), coordNat1 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 46) := by
      apply freeIdent1 hL C 46 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 46 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 46 1 3 (by decide), coordNat3 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 46 2 2 (by decide), coordNat2 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c101_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 45) := by
      apply freeIdent2 hL C 45 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 45 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 45 1 3 (by decide), coordNat3 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 45 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c101_12_0, c101_12_1, c101_12_2, c101_12_3]
    try ring
  have cv110_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 47 + freecoord L hL C 57 - freecoord L hL C 17 - freecoord L hL C 48) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c110_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 47) := by
      apply freeIdent0 hL C 47 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 47 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 47 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 47 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 57) := by
      apply freeIdent1 hL C 57 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 57 0 2 (by decide), coordNat2 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 57 1 4 (by decide), coordNat4 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 57 2 0 (by decide), coordNat0 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = C (freeCellBond L hL 17) := by
      apply freeIdent0 hL C 17 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 17 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 17 1 0 (by decide), coordNat0 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 17 2 0 (by decide), coordNat0 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 48) := by
      apply freeIdent1 hL C 48 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 48 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 48 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 48 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c110_01_0, c110_01_1, c110_01_2, c110_01_3]
    try ring
  have cv110_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 48 + freecoord L hL C 19 - freecoord L hL C 51 - freecoord L hL C 49) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c110_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 48) := by
      apply freeIdent1 hL C 48 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 48 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 48 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 48 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 19) := by
      apply freeIdent2 hL C 19 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 19 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 19 1 0 (by decide), coordNat0 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 19 2 0 (by decide), coordNat0 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 51) := by
      apply freeIdent1 hL C 51 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 1 4 (by decide), coordNat4 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 2 1 (by decide), coordNat1 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c110_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 49) := by
      apply freeIdent2 hL C 49 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 49 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 49 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 49 2 0 (by decide), coordNat0 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c110_12_0, c110_12_1, c110_12_2, c110_12_3]
    try ring
  have cv111_01 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir01) = (freecoord L hL C 50 + freecoord L hL C 58 - freecoord L hL C 20 - freecoord L hL C 51) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir01]
    have c111_01_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 50) := by
      apply freeIdent0 hL C 50 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 50 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 50 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 50 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_01_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (1 : Fin 3)) = C (freeCellBond L hL 58) := by
      apply freeIdent1 hL C 58 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 58 0 2 (by decide), coordNat2 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 58 1 4 (by decide), coordNat4 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 58 2 1 (by decide), coordNat1 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_01_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (0 : Fin 3)) = C (freeCellBond L hL 20) := by
      apply freeIdent0 hL C 20 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 20 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 20 1 0 (by decide), coordNat0 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 20 2 1 (by decide), coordNat1 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_01_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 51) := by
      apply freeIdent1 hL C 51 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c111_01_0, c111_01_1, c111_01_2, c111_01_3]
    try ring
  have cv111_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 51 + freecoord L hL C 22 - freecoord L hL C 53 - freecoord L hL C 52) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c111_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 51) := by
      apply freeIdent1 hL C 51 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 51 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 22) := by
      apply freeIdent2 hL C 22 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 22 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 22 1 0 (by decide), coordNat0 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 22 2 1 (by decide), coordNat1 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 53) := by
      apply freeIdent1 hL C 53 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 53 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 53 1 4 (by decide), coordNat4 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 53 2 2 (by decide), coordNat2 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c111_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (1:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (1:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 52) := by
      apply freeIdent2 hL C 52 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 52 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 52 1 4 (by decide), coordNat4 1]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 52 2 1 (by decide), coordNat1 2]
        simp only [prevSite_self, prevSite_ne 1 0 (by decide), prevSite_ne 1 2 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c111_12_0, c111_12_1, c111_12_2, c111_12_3]
    try ring
  rw [cv000_01, cv000_12, cv001_01, cv001_12, cv010_01, cv010_12, cv011_01, cv011_12, cv100_01, cv100_12, cv101_01, cv101_12, cv110_01, cv110_12, cv111_01, cv111_12]
  try ring


#print axioms slabsum1

/-! ## Slab-reindex: the mu=2 curl block. -/

theorem slabsum2 (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) :
    (∑ p ∈ slabPlaqs (⟨prevSite (2 : Fin 3), prevSite_mem 2 hdvd⟩, 2), (curlValue C p) ^ 2)
      = (freecoord L hL C 25)^2 + (freecoord L hL C 7)^2 + (freecoord L hL C 28 - freecoord L hL C 1)^2 + (freecoord L hL C 9 - freecoord L hL C 1)^2 + (freecoord L hL C 34 - freecoord L hL C 7)^2 + (freecoord L hL C 6 - freecoord L hL C 8 - freecoord L hL C 7)^2 + (freecoord L hL C 37 - freecoord L hL C 9)^2 + (freecoord L hL C 8 + freecoord L hL C 10 - freecoord L hL C 2 - freecoord L hL C 9)^2 + (freecoord L hL C 23 - freecoord L hL C 26 - freecoord L hL C 25)^2 + (freecoord L hL C 24 + freecoord L hL C 34 - freecoord L hL C 27 - freecoord L hL C 25)^2 + (freecoord L hL C 26 + freecoord L hL C 54 - freecoord L hL C 17 - freecoord L hL C 28)^2 + (freecoord L hL C 27 + freecoord L hL C 37 - freecoord L hL C 18 - freecoord L hL C 28)^2 + (freecoord L hL C 32 + freecoord L hL C 55 - freecoord L hL C 35 - freecoord L hL C 34)^2 + (freecoord L hL C 33 + freecoord L hL C 38 - freecoord L hL C 36 - freecoord L hL C 34)^2 + (freecoord L hL C 35 + freecoord L hL C 56 - freecoord L hL C 29 - freecoord L hL C 37)^2 + (freecoord L hL C 36 + freecoord L hL C 39 - freecoord L hL C 30 - freecoord L hL C 37)^2 := by
  rw [slabPlaqs_prevSite 2 hdvd {pdir02, pdir12} (by decide)]
  rw [Finset.sum_product]
  rw [blockOf_fits_eq_image (prevSite 2) 2 (prevSite_fits hL 2), Finset.sum_image (siteFn_inj_mu hL 2)]
  rw [show (Finset.univ : Finset (Fin 3 → Fin 2)) =
      { ![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1], ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1] } from by decide]
  simp only [Finset.sum_pair (by decide : pdir02 ≠ pdir12)]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  have cv000_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 25) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c000_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c000_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 25) := by
      apply freeIdent2 hL C 25 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 25 0 1 (by decide), coordNat1 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 25 1 0 (by decide), coordNat0 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 25 2 3 (by decide), coordNat3 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c000_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
    have c000_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = 0 := by
      apply pinDir2 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]) <;> (try rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]) <;> (try rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))])
          all_goals omega
    rw [c000_02_0, c000_02_1, c000_02_2, c000_02_3]
    try ring
  have cv000_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 7) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c000_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c000_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 7) := by
      apply freeIdent2 hL C 7 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 7 0 0 (by decide), coordNat0 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 7 1 1 (by decide), coordNat1 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 7 2 3 (by decide), coordNat3 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c000_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
    have c000_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = 0 := by
      apply pinDir2 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]) <;> (try rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]) <;> (try rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))])
          all_goals omega
    rw [c000_12_0, c000_12_1, c000_12_2, c000_12_3]
    try ring
  have cv001_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 28 - freecoord L hL C 1) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c001_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c001_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 28) := by
      apply freeIdent2 hL C 28 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 28 0 1 (by decide), coordNat1 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 28 1 0 (by decide), coordNat0 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 28 2 4 (by decide), coordNat4 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c001_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,0,0])
        (codeOriginSite_coarse3 hL 0 0 0 (by simp [coordNat]) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
          all_goals omega
    have c001_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 1) := by
      apply freeIdent2 hL C 1 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 1 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 1 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 1 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c001_02_0, c001_02_1, c001_02_2, c001_02_3]
    try ring
  have cv001_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 9 - freecoord L hL C 1) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c001_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c001_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 9) := by
      apply freeIdent2 hL C 9 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 9 0 0 (by decide), coordNat0 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 9 1 1 (by decide), coordNat1 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 9 2 4 (by decide), coordNat4 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c001_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = 0 := by
      apply pinDir1 hL C hC (codeOriginSite hL ![0,0,0])
        (codeOriginSite_coarse3 hL 0 0 0 (by simp [coordNat]) (by simp [coordNat]) (by simp [coordNat]))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord1_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]) <;> (try rw [show L 1 - 1 + 1 + 1 = L 1 + 1 by (have := hL 1; omega), Nat.mod_self]) <;> (try rw [show L 1 - 1 + 1 = L 1 by (have := hL 1; omega), Nat.mod_eq_of_lt (by (have := hL 1; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
          all_goals omega
    have c001_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 1) := by
      apply freeIdent2 hL C 1 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 1 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 1 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 1 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c001_12_0, c001_12_1, c001_12_2, c001_12_3]
    try ring
  have cv010_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 34 - freecoord L hL C 7) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c010_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c010_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 34) := by
      apply freeIdent2 hL C 34 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 0 1 (by decide), coordNat1 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 2 3 (by decide), coordNat3 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c010_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
          all_goals omega
    have c010_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 7) := by
      apply freeIdent2 hL C 7 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 7 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 7 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 7 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c010_02_0, c010_02_1, c010_02_2, c010_02_3]
    try ring
  have cv010_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 6 - freecoord L hL C 8 - freecoord L hL C 7) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c010_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 6) := by
      apply freeIdent1 hL C 6 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 6 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 6 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 6 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c010_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = 0 := by
      apply pinDir2 hL C hC (codeOriginSite hL ![0,2,3])
        (codeOriginSite_coarse3 hL 0 2 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat2]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · apply mem_block_codeOrigin hL 0 2 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 2 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift2_coord_ne _ (by decide)]
          rw [shift1_coord1_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord2_val]
          rw [shift1_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]) <;> (try rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]) <;> (try rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))])
          all_goals omega
    have c010_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 8) := by
      apply freeIdent1 hL C 8 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 8 0 0 (by decide), coordNat0 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 8 1 1 (by decide), coordNat1 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 8 2 4 (by decide), coordNat4 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c010_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 7) := by
      apply freeIdent2 hL C 7 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 7 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 7 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 7 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c010_12_0, c010_12_1, c010_12_2, c010_12_3]
    try ring
  have cv011_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 37 - freecoord L hL C 9) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c011_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,0,3])
        (codeOriginSite_coarse3 hL 0 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
    have c011_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 37) := by
      apply freeIdent2 hL C 37 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 0 1 (by decide), coordNat1 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 2 4 (by decide), coordNat4 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c011_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = 0 := by
      apply pinDir0 hL C hC (codeOriginSite hL ![0,0,0])
        (codeOriginSite_coarse3 hL 0 0 0 (by simp [coordNat]) (by simp [coordNat]) (by simp [coordNat]))
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
          all_goals omega
      · apply mem_block_codeOrigin hL 0 0 0
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord0_val]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]) <;> (try rw [show L 0 - 1 + 1 + 1 = L 0 + 1 by (have := hL 0; omega), Nat.mod_self]) <;> (try rw [show L 0 - 1 + 1 = L 0 by (have := hL 0; omega), Nat.mod_eq_of_lt (by (have := hL 0; omega))])
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          rw [shift2_coord2_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
          all_goals omega
    have c011_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 9) := by
      apply freeIdent2 hL C 9 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 9 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 9 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 9 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c011_02_0, c011_02_1, c011_02_2, c011_02_3]
    try ring
  have cv011_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 8 + freecoord L hL C 10 - freecoord L hL C 2 - freecoord L hL C 9) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c011_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 8) := by
      apply freeIdent1 hL C 8 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 8 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 8 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 8 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c011_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 10) := by
      apply freeIdent2 hL C 10 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 10 0 0 (by decide), coordNat0 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 10 1 2 (by decide), coordNat2 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 10 2 4 (by decide), coordNat4 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c011_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 2) := by
      apply freeIdent1 hL C 2 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 2 0 0 (by decide), coordNat0 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 2 1 1 (by decide), coordNat1 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 2 2 0 (by decide), coordNat0 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
        all_goals omega
    have c011_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![0,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![0,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 9) := by
      apply freeIdent2 hL C 9 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 9 0 0 (by decide), coordNat0 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 9 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 9 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c011_12_0, c011_12_1, c011_12_2, c011_12_3]
    try ring
  have cv100_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 23 - freecoord L hL C 26 - freecoord L hL C 25) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c100_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 23) := by
      apply freeIdent0 hL C 23 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 23 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 23 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 23 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c100_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = 0 := by
      apply pinDir2 hL C hC (codeOriginSite hL ![2,0,3])
        (codeOriginSite_coarse3 hL 2 0 3 (by simp [coordNat]) (by simp [coordNat]) (by rw [coordNat3]; have := hdvd 2; omega))
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat2]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · apply Fin.ext
        have := hL 0; have := hL 1; have := hL 2
        rw [codeOriginSite_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, coordNat0]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · apply mem_block_codeOrigin hL 2 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
      · apply mem_block_codeOrigin hL 2 0 3
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat2]
          rw [shift2_coord_ne _ (by decide)]
          rw [shift0_coord0_val]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat0]
          rw [shift2_coord_ne _ (by decide)]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          all_goals omega
        · have := hL 0; have := hL 1; have := hL 2
          simp only [coordNat3]
          rw [shift2_coord2_val]
          rw [shift0_coord_ne _ (by decide)]
          simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
          (try rw [Nat.mod_eq_of_lt (by (have := hL 2; omega))]) <;> (try rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]) <;> (try rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))])
          all_goals omega
    have c100_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = C (freeCellBond L hL 26) := by
      apply freeIdent0 hL C 26 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 26 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 26 1 0 (by decide), coordNat0 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 26 2 4 (by decide), coordNat4 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c100_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 25) := by
      apply freeIdent2 hL C 25 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 25 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 25 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 25 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c100_02_0, c100_02_1, c100_02_2, c100_02_3]
    try ring
  have cv100_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 24 + freecoord L hL C 34 - freecoord L hL C 27 - freecoord L hL C 25) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c100_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 24) := by
      apply freeIdent1 hL C 24 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 24 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 24 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 24 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c100_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 34) := by
      apply freeIdent2 hL C 34 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 1 1 (by decide), coordNat1 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 2 3 (by decide), coordNat3 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c100_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 27) := by
      apply freeIdent1 hL C 27 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 27 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 27 1 0 (by decide), coordNat0 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 27 2 4 (by decide), coordNat4 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c100_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 25) := by
      apply freeIdent2 hL C 25 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 25 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 25 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 25 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c100_12_0, c100_12_1, c100_12_2, c100_12_3]
    try ring
  have cv101_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 26 + freecoord L hL C 54 - freecoord L hL C 17 - freecoord L hL C 28) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c101_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 26) := by
      apply freeIdent0 hL C 26 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 26 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 26 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 26 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 54) := by
      apply freeIdent2 hL C 54 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 54 0 2 (by decide), coordNat2 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 54 1 0 (by decide), coordNat0 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 54 2 4 (by decide), coordNat4 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = C (freeCellBond L hL 17) := by
      apply freeIdent0 hL C 17 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 17 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 17 1 0 (by decide), coordNat0 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 17 2 0 (by decide), coordNat0 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
        all_goals omega
    have c101_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 28) := by
      apply freeIdent2 hL C 28 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 28 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 28 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 28 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c101_02_0, c101_02_1, c101_02_2, c101_02_3]
    try ring
  have cv101_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 27 + freecoord L hL C 37 - freecoord L hL C 18 - freecoord L hL C 28) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c101_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 27) := by
      apply freeIdent1 hL C 27 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 27 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 27 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 27 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 37) := by
      apply freeIdent2 hL C 37 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 1 1 (by decide), coordNat1 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 2 4 (by decide), coordNat4 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c101_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 18) := by
      apply freeIdent1 hL C 18 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 18 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 18 1 0 (by decide), coordNat0 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 18 2 0 (by decide), coordNat0 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
        all_goals omega
    have c101_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,0,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,0,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 28) := by
      apply freeIdent2 hL C 28 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 28 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 28 1 0 (by decide), coordNat0 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 28 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c101_12_0, c101_12_1, c101_12_2, c101_12_3]
    try ring
  have cv110_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 32 + freecoord L hL C 55 - freecoord L hL C 35 - freecoord L hL C 34) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c110_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 32) := by
      apply freeIdent0 hL C 32 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 32 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 32 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 32 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 55) := by
      apply freeIdent2 hL C 55 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 55 0 2 (by decide), coordNat2 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 55 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 55 2 3 (by decide), coordNat3 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = C (freeCellBond L hL 35) := by
      apply freeIdent0 hL C 35 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 35 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 35 1 1 (by decide), coordNat1 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 35 2 4 (by decide), coordNat4 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c110_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 34) := by
      apply freeIdent2 hL C 34 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c110_02_0, c110_02_1, c110_02_2, c110_02_3]
    try ring
  have cv110_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 33 + freecoord L hL C 38 - freecoord L hL C 36 - freecoord L hL C 34) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c110_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 33) := by
      apply freeIdent1 hL C 33 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 33 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 33 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 33 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 38) := by
      apply freeIdent2 hL C 38 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 38 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 38 1 2 (by decide), coordNat2 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 38 2 3 (by decide), coordNat3 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c110_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 36) := by
      apply freeIdent1 hL C 36 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 36 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 36 1 1 (by decide), coordNat1 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 36 2 4 (by decide), coordNat4 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 2 - 1 + 1 = L 2 by (have := hL 2; omega), Nat.mod_eq_of_lt (by (have := hL 2; omega))]
        all_goals omega
    have c110_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,0] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,0] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 34) := by
      apply freeIdent2 hL C 34 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 34 2 3 (by decide), coordNat3 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c110_12_0, c110_12_1, c110_12_2, c110_12_3]
    try ring
  have cv111_02 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir02) = (freecoord L hL C 35 + freecoord L hL C 56 - freecoord L hL C 29 - freecoord L hL C 37) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir02]
    have c111_02_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (0 : Fin 3)) = C (freeCellBond L hL 35) := by
      apply freeIdent0 hL C 35 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 35 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 35 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 35 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_02_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 0, (2 : Fin 3)) = C (freeCellBond L hL 56) := by
      apply freeIdent2 hL C 56 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 56 0 2 (by decide), coordNat2 0]
        rw [shift0_coord0_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 0; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 56 1 1 (by decide), coordNat1 1]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 56 2 4 (by decide), coordNat4 2]
        rw [shift0_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_02_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (0 : Fin 3)) = C (freeCellBond L hL 29) := by
      apply freeIdent0 hL C 29 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 29 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 29 1 1 (by decide), coordNat1 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 29 2 0 (by decide), coordNat0 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
        all_goals omega
    have c111_02_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 37) := by
      apply freeIdent2 hL C 37 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c111_02_0, c111_02_1, c111_02_2, c111_02_3]
    try ring
  have cv111_12 : curlValue C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), pdir12) = (freecoord L hL C 36 + freecoord L hL C 39 - freecoord L hL C 30 - freecoord L hL C 37) := by
    simp only [freecoord_apply]
    simp only [curlValue, pdir12]
    have c111_12_0 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (1 : Fin 3)) = C (freeCellBond L hL 36) := by
      apply freeIdent1 hL C 36 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 36 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 36 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 36 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_12_1 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 1, (2 : Fin 3)) = C (freeCellBond L hL 39) := by
      apply freeIdent2 hL C 39 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 39 0 1 (by decide), coordNat1 0]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 39 1 2 (by decide), coordNat2 1]
        rw [shift1_coord1_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [Nat.mod_eq_of_lt (by (have := hL 1; omega))]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 39 2 4 (by decide), coordNat4 2]
        rw [shift1_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    have c111_12_2 : C (periodicLatticeShift (fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))) 2, (1 : Fin 3)) = C (freeCellBond L hL 30) := by
      apply freeIdent1 hL C 30 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 30 0 1 (by decide), coordNat1 0]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 30 1 1 (by decide), coordNat1 1]
        rw [shift2_coord_ne _ (by decide)]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 30 2 0 (by decide), coordNat0 2]
        rw [shift2_coord2_val]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        rw [show L 2 - 1 + 1 + 1 = L 2 + 1 by (have := hL 2; omega), Nat.mod_self]
        all_goals omega
    have c111_12_3 : C ((fun ν : Fin 3 => (⟨((prevSite (2:Fin 3):PeriodicLatticeSite L) ν).val + ((![1,1,1] : Fin 3 → Fin 2) ν).val, by have := ((![1,1,1] : Fin 3 → Fin 2) ν).isLt; have := prevSite_fits hL (2:Fin 3) ν; omega⟩ : Fin (L ν + 1))), (2 : Fin 3)) = C (freeCellBond L hL 37) := by
      apply freeIdent2 hL C 37 _ ?_ ?_ ?_ (by decide)
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 0 1 (by decide), coordNat1 0]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 1 1 (by decide), coordNat1 1]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
      · have := hL 0; have := hL 1; have := hL 2
        rw [refSite_val hL 37 2 4 (by decide), coordNat4 2]
        simp only [prevSite_self, prevSite_ne 2 0 (by decide), prevSite_ne 2 1 (by decide), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.add_zero]
        all_goals omega
    rw [c111_12_0, c111_12_1, c111_12_2, c111_12_3]
    try ring
  rw [cv000_02, cv000_12, cv001_02, cv001_12, cv010_02, cv010_12, cv011_02, cv011_12, cv100_02, cv100_12, cv101_02, cv101_12, cv110_02, cv110_12, cv111_02, cv111_12]
  try ring


#print axioms slabsum2

/-! ## Slab-reindex, step 3: `hQS` ASSEMBLED (PROVED, no `sorry`, axiom-clean).

The two off-diagonal energies (`∑_μ line²`, `∑_μ ∑_p curl²`) expressed on the admissible subspace
via `SparseGram.qsCertSparse`.  Combines the three `line_reindex` (Q half) and the three `slabsum`
(Slab half) with the pure covector arithmetic identity `(1/128)·sosQuadValue qsCert x = 256·∑line² +
32·∑curl²` (unfolded `sosQuadValue`, `ring`).  Ground truth `compute/href_qslab/covector_spec.py`. -/
theorem hQS_proved (hL : ∀ μ, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (C : Bond L → ℝ) (hC : C ∈ admissibleSubspaceInter L 2) :
    ((2 : ℕ) : ℝ) * (∑ μ : Fin 3,
          (lineCoarseRestrict 2 C (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ)) ^ 2)
      + (1 / ((2 : ℕ) : ℝ) ^ 2) * (∑ μ : Fin 3,
          ∑ p ∈ slabPlaqs (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ), (curlValue C p) ^ 2)
      = (1 / 128) * sosQuadValue (SparseGram.qsCertSparse.map castSparse) (freecoord L hL C) := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three,
      line_reindex0 hL hdvd C hC, line_reindex1 hL hdvd C hC, line_reindex2 hL hdvd C hC,
      slabsum0 hL hdvd C hC, slabsum1 hL hdvd C hC, slabsum2 hL hdvd C hC]
  simp only [sosQuadValue, SparseGram.qsCertSparse, List.map_cons, List.map_nil, castSparse,
    scovEval, List.sum_cons, List.sum_nil]
  push_cast
  ring

#print axioms hQS_proved

end HrefQSlab
