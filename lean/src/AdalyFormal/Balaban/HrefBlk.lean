import AdalyFormal.Balaban.Ell2RefBlock

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! # `HrefBlk` — the Blk diagonal energy evaluated onto its 5 free-cell coordinates.

This module closes the last DIAGONAL piece of the reference-block SOS identity `Href`
(`Ell2RefBlock.geomInequality_of_admissible_ell2_of_refBlockSOS`): the in-block bond energy
`∑_{b⊂B(0)} C(b)²`, on the admissible subspace, evaluated onto its 5 free-cell coordinates
`blkIds = {3,18,19,21,31}` (companion to `Ell2RefBlock.topFace_total_freecoord`, which does the same
for the 12 Top coordinates).

`EnergyEval.inBlock_energy_full_drop` (PROVED) already drops the 7 staircase-pinned in-block bonds,
leaving `∑_{b : ¬pinned} C(b)²` over the 5 free in-block bonds.  Here we identify those 5 filtered
bonds with the free-cell enumeration `freeCellBond` at `blkIds` and reindex, so the Blk energy is a
concrete `∑_{i∈blkIds} (freecoord C i)²`.

## The 5 free in-block bonds (`compute/href_identity/verify_blk.py`, `PYTHONHASHSEED=0`).

The 12 in-block-`0` bonds (base coord in `{0,1}³`, base coord along the bond direction `= 0` so the
`+dir` endpoint stays in the block) split into 7 staircase-pinned (`EnergyEval.pinnedInBlock0`, which
carry no free-cell coordinate) and 5 free.  The 5 free are exactly the `codeList` entries with all
site codes in `{0,1}` and unpinned direction:
`idx 3 = ((0,1,0),dir 2)`, `18 = ((1,0,0),dir 1)`, `19 = ((1,0,0),dir 2)`, `21 = ((1,0,1),dir 1)`,
`31 = ((1,1,0),dir 2)`.

## What is PROVED here (no `sorry`, axiom-clean — `#print axioms` below).

* `blkIds` — the 5 free-cell coordinates carrying the backward Blk energy.
* `blk_total_freecoord` — **the Blk diagonal energy through `freecoord` (PROVED, no `sorry`).**  On the
  admissible subspace, `∑_{b⊂B(0)} C(b)² = ∑_{i∈blkIds} (freecoord C i)²`.  This LOCKS the Blk piece of
  `Href` into the same `freecoord` framework the Top piece already sits in.

## HONEST SCOPE — what this does NOT close.

This is one of the FOUR energies of `Href`; it does NOT discharge `Href` (still open: the Q and Slab
OFF-diagonal expansions, and the final SOS reflection).  It is the last diagonal brick, banked for
reuse by a future full-`Href` build; it does not by itself change
`GeomGlobal.geomInequality_of_admissible_ell2`'s `sorry`. -/

namespace HrefBlk

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.BlockPoincare
open FreeCellFrame
open QSlabExpand
open Ell2RefBlock

variable {L : PeriodicLatticeExtent}

/-- The 5 free-cell coordinates carrying the backward Blk energy (the free in-block-`0` bonds). -/
def blkIds : Finset (Fin 80) := {3, 18, 19, 21, 31}

/-- Bond reconstruction: a free-cell index whose `refSite` matches `x` coordinate-by-coordinate and
whose `freeDir` matches `d` has `freeCellBond … = (x, d)`. -/
theorem freeCellBond_eq_of_coords (hL : ∀ μ, 4 ≤ L μ) (i : Fin 80) (x : PeriodicLatticeSite L)
    (d : Fin 3) (q0 : (refSite L hL i 0).val = (x 0).val) (q1 : (refSite L hL i 1).val = (x 1).val)
    (q2 : (refSite L hL i 2).val = (x 2).val) (qd : freeDir i = d) :
    freeCellBond L hL i = (x, d) := by
  have hs : refSite L hL i = x := by funext ν; fin_cases ν <;> apply Fin.ext <;> assumption
  show (refSite L hL i, freeDir i) = (x, d)
  rw [hs, qd]

/-- **Filter membership of a `blkIds` free-cell bond from its coordinate data (PROVED, no `sorry`).**
Given the direction `d`, that every `refSite` coordinate is in `{0,1}`, that the base-direction
coordinate is `0`, and unpinnedness, the bond is an unpinned in-block-`0` bond. -/
theorem blkBond_mem (hL : ∀ μ, 4 ≤ L μ) (j : Fin 80) (d : Fin 3)
    (hd : freeDir j = d)
    (hv0 : (refSite L hL j 0).val = 0 ∨ (refSite L hL j 0).val = 1)
    (hv1 : (refSite L hL j 1).val = 0 ∨ (refSite L hL j 1).val = 1)
    (hv2 : (refSite L hL j 2).val = 0 ∨ (refSite L hL j 2).val = 1)
    (hdz : (refSite L hL j d).val = 0)
    (hnp : ¬ EnergyEval.pinnedInBlock0 (freeCellBond L hL j)) :
    bondInBlock (0 : PeriodicLatticeSite L) 2 (freeCellBond L hL j)
      ∧ ¬ EnergyEval.pinnedInBlock0 (freeCellBond L hL j) := by
  have hv : ∀ ν, (refSite L hL j ν).val = 0 ∨ (refSite L hL j ν).val = 1 := by
    intro ν; fin_cases ν <;> first | exact hv0 | exact hv1 | exact hv2
  refine ⟨⟨?_, ?_⟩, hnp⟩
  · rw [mem_blockOf]; intro ν
    refine ⟨Nat.zero_le _, ?_⟩
    show (refSite L hL j ν).val < 2
    rcases hv ν with h | h <;> omega
  · rw [mem_blockOf]; intro ν
    refine ⟨Nat.zero_le _, ?_⟩
    show (periodicLatticeShift (refSite L hL j) (freeDir j) ν).val < 2
    rw [hd]
    by_cases hν : ν = d
    · subst hν
      rw [periodicLatticeShift, Function.update_self, Fin.val_add, hdz]
      have h1v : (1 : Fin (L ν + 1)).val = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by have := hL ν; omega)
      have hlt : (0 : ℕ) + 1 < L ν + 1 := by have := hL ν; omega
      rw [h1v, Nat.mod_eq_of_lt hlt]
      omega
    · rw [periodicLatticeShift, Function.update_of_ne hν]
      rcases hv ν with h | h <;> omega

/-- **The filtered free in-block bonds ARE the `blkIds` free-cell bonds (PROVED, no `sorry`).** -/
theorem filter_eq_image (hL : ∀ μ, 4 ≤ L μ) :
    (bondsInBlock (0 : PeriodicLatticeSite L) 2).filter (fun b => ¬ EnergyEval.pinnedInBlock0 b)
      = Finset.image (freeCellBond L hL) blkIds := by
  have cn0 : ∀ ν : Fin 3, coordNat L ν 0 = 0 := fun ν => (coordNat_vals ν).1
  have cn1 : ∀ ν : Fin 3, coordNat L ν 1 = 1 := fun ν => (coordNat_vals ν).2.1
  have R : ∀ (i : Fin 80) (ν : Fin 3) (c : Fin 5), axisCode (freeCode i) ν = c →
      (refSite L hL i ν).val = coordNat L ν c := fun i ν c hc => refSite_val hL i ν c hc
  ext b
  rw [Finset.mem_filter, mem_bondsInBlock, Finset.mem_image]
  constructor
  · rintro ⟨⟨hb1, hbs⟩, hpin⟩
    rw [mem_blockOf] at hb1
    -- coords of b.1 are in {0,1}
    have hcoord : ∀ ν : Fin 3, (b.1 ν).val = 0 ∨ (b.1 ν).val = 1 := by
      intro ν
      have h2 : (b.1 ν).val < 2 := (hb1 ν).2
      omega
    -- the shift along b.2 keeps the base-dir coordinate `= 0`
    have hshift_dd : (periodicLatticeShift b.1 b.2 b.2).val = ((b.1 b.2).val + 1) % (L b.2 + 1) := by
      have h1v : (1 : Fin (L b.2 + 1)).val = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by have := hL b.2; omega)
      rw [periodicLatticeShift, Function.update_self, Fin.val_add, h1v]
    have hddz : (b.1 b.2).val = 0 := by
      have h2 : (periodicLatticeShift b.1 b.2 b.2).val < 2 := ((mem_blockOf.mp hbs) b.2).2
      rw [hshift_dd] at h2
      have hlt : (b.1 b.2).val < 2 := by rcases hcoord b.2 with h | h <;> omega
      have hL2 := hL b.2
      have hnw : ((b.1 b.2).val + 1) % (L b.2 + 1) = (b.1 b.2).val + 1 := by
        apply Nat.mod_eq_of_lt; omega
      rw [hnw] at h2; omega
    -- reconstruct the index by casing on the direction and the free coordinates
    have hb2 : b.2 = 0 ∨ b.2 = 1 ∨ b.2 = 2 := by
      have h := b.2.isLt
      have hv : b.2.val = 0 ∨ b.2.val = 1 ∨ b.2.val = 2 := by omega
      rcases hv with hv | hv | hv
      · exact Or.inl (Fin.ext (by simp [hv]))
      · exact Or.inr (Or.inl (Fin.ext (by simp [hv])))
      · exact Or.inr (Or.inr (Fin.ext (by simp [hv])))
    -- helper to build the witness from a concrete index
    have mkw : ∀ (i : Fin 80), (refSite L hL i 0).val = (b.1 0).val →
        (refSite L hL i 1).val = (b.1 1).val → (refSite L hL i 2).val = (b.1 2).val →
        freeDir i = b.2 → i ∈ blkIds → ∃ a ∈ blkIds, freeCellBond L hL a = b := by
      intro i q0 q1 q2 qd hi
      exact ⟨i, hi, freeCellBond_eq_of_coords hL i b.1 b.2 q0 q1 q2 qd⟩
    rcases hb2 with h2 | h2 | h2
    · -- direction 0: always pinned, contradiction
      exact absurd (Or.inl h2) hpin
    · -- direction 1: (b.1 0).val = 1 (unpinned), (b.1 1).val = 0 (base-dir), (b.1 2).val ∈ {0,1}
      have hb1dir : (b.1 1).val = 0 := by rw [← h2]; exact hddz
      have hx0 : (b.1 0).val = 1 := by
        rcases hcoord 0 with h | h
        · exact absurd (Or.inr (Or.inl ⟨h2, h⟩)) hpin
        · exact h
      rcases hcoord 2 with hx2 | hx2
      · -- (1,0,0) dir 1 = idx 18
        refine mkw 18 ?_ ?_ ?_ ?_ (by decide)
        · rw [R 18 0 1 (by decide), cn1, hx0]
        · rw [R 18 1 0 (by decide), cn0, hb1dir]
        · rw [R 18 2 0 (by decide), cn0, hx2]
        · show freeDir 18 = b.2; rw [h2]; decide
      · -- (1,0,1) dir 1 = idx 21
        refine mkw 21 ?_ ?_ ?_ ?_ (by decide)
        · rw [R 21 0 1 (by decide), cn1, hx0]
        · rw [R 21 1 0 (by decide), cn0, hb1dir]
        · rw [R 21 2 1 (by decide), cn1, hx2]
        · show freeDir 21 = b.2; rw [h2]; decide
    · -- direction 2: (b.1 2).val = 0 (base-dir), NOT (x0=0 ∧ x1=0)
      have hb1dir : (b.1 2).val = 0 := by rw [← h2]; exact hddz
      have hnot00 : ¬ ((b.1 0).val = 0 ∧ (b.1 1).val = 0) := fun ⟨e0, e1⟩ =>
        hpin (Or.inr (Or.inr ⟨h2, e0, e1⟩))
      rcases hcoord 0 with hx0 | hx0
      · -- x0 = 0, so x1 = 1 (else pinned): (0,1,0) dir 2 = idx 3
        have hx1 : (b.1 1).val = 1 := by
          rcases hcoord 1 with h | h
          · exact absurd ⟨hx0, h⟩ hnot00
          · exact h
        refine mkw 3 ?_ ?_ ?_ ?_ (by decide)
        · rw [R 3 0 0 (by decide), cn0, hx0]
        · rw [R 3 1 1 (by decide), cn1, hx1]
        · rw [R 3 2 0 (by decide), cn0, hb1dir]
        · show freeDir 3 = b.2; rw [h2]; decide
      · -- x0 = 1
        rcases hcoord 1 with hx1 | hx1
        · -- (1,0,0) dir 2 = idx 19
          refine mkw 19 ?_ ?_ ?_ ?_ (by decide)
          · rw [R 19 0 1 (by decide), cn1, hx0]
          · rw [R 19 1 0 (by decide), cn0, hx1]
          · rw [R 19 2 0 (by decide), cn0, hb1dir]
          · show freeDir 19 = b.2; rw [h2]; decide
        · -- (1,1,0) dir 2 = idx 31
          refine mkw 31 ?_ ?_ ?_ ?_ (by decide)
          · rw [R 31 0 1 (by decide), cn1, hx0]
          · rw [R 31 1 1 (by decide), cn1, hx1]
          · rw [R 31 2 0 (by decide), cn0, hb1dir]
          · show freeDir 31 = b.2; rw [h2]; decide
  · rintro ⟨i, hi, rfl⟩
    -- each blkIds free-cell bond is in-block-0 and unpinned (five explicit indices)
    fin_cases hi
    · -- idx 3, dir 2, site (0,1,0)
      have e0 : (refSite L hL 3 0).val = 0 := by rw [R 3 0 0 (by decide), cn0]
      have e1 : (refSite L hL 3 1).val = 1 := by rw [R 3 1 1 (by decide), cn1]
      have e2 : (refSite L hL 3 2).val = 0 := by rw [R 3 2 0 (by decide), cn0]
      refine blkBond_mem hL 3 2 (by decide) (Or.inl e0) (Or.inr e1) (Or.inl e2) e2 ?_
      intro hp; unfold EnergyEval.pinnedInBlock0 at hp
      rcases hp with h | ⟨h, _⟩ | ⟨_, _, h1⟩
      · change freeDir 3 = 0 at h; exact absurd h (by decide)
      · change freeDir 3 = 1 at h; exact absurd h (by decide)
      · have hc : ((freeCellBond L hL 3).1 1).val = 1 := e1
        omega
    · -- idx 18, dir 1, site (1,0,0)
      have e0 : (refSite L hL 18 0).val = 1 := by rw [R 18 0 1 (by decide), cn1]
      have e1 : (refSite L hL 18 1).val = 0 := by rw [R 18 1 0 (by decide), cn0]
      have e2 : (refSite L hL 18 2).val = 0 := by rw [R 18 2 0 (by decide), cn0]
      refine blkBond_mem hL 18 1 (by decide) (Or.inr e0) (Or.inl e1) (Or.inl e2) e1 ?_
      intro hp; unfold EnergyEval.pinnedInBlock0 at hp
      rcases hp with h | ⟨_, h0⟩ | ⟨h, _, _⟩
      · change freeDir 18 = 0 at h; exact absurd h (by decide)
      · have hc : ((freeCellBond L hL 18).1 0).val = 1 := e0
        omega
      · change freeDir 18 = 2 at h; exact absurd h (by decide)
    · -- idx 19, dir 2, site (1,0,0)
      have e0 : (refSite L hL 19 0).val = 1 := by rw [R 19 0 1 (by decide), cn1]
      have e1 : (refSite L hL 19 1).val = 0 := by rw [R 19 1 0 (by decide), cn0]
      have e2 : (refSite L hL 19 2).val = 0 := by rw [R 19 2 0 (by decide), cn0]
      refine blkBond_mem hL 19 2 (by decide) (Or.inr e0) (Or.inl e1) (Or.inl e2) e2 ?_
      intro hp; unfold EnergyEval.pinnedInBlock0 at hp
      rcases hp with h | ⟨h, _⟩ | ⟨_, h0, _⟩
      · change freeDir 19 = 0 at h; exact absurd h (by decide)
      · change freeDir 19 = 1 at h; exact absurd h (by decide)
      · have hc : ((freeCellBond L hL 19).1 0).val = 1 := e0
        omega
    · -- idx 21, dir 1, site (1,0,1)
      have e0 : (refSite L hL 21 0).val = 1 := by rw [R 21 0 1 (by decide), cn1]
      have e1 : (refSite L hL 21 1).val = 0 := by rw [R 21 1 0 (by decide), cn0]
      have e2 : (refSite L hL 21 2).val = 1 := by rw [R 21 2 1 (by decide), cn1]
      refine blkBond_mem hL 21 1 (by decide) (Or.inr e0) (Or.inl e1) (Or.inr e2) e1 ?_
      intro hp; unfold EnergyEval.pinnedInBlock0 at hp
      rcases hp with h | ⟨_, h0⟩ | ⟨h, _, _⟩
      · change freeDir 21 = 0 at h; exact absurd h (by decide)
      · have hc : ((freeCellBond L hL 21).1 0).val = 1 := e0
        omega
      · change freeDir 21 = 2 at h; exact absurd h (by decide)
    · -- idx 31, dir 2, site (1,1,0)
      have e0 : (refSite L hL 31 0).val = 1 := by rw [R 31 0 1 (by decide), cn1]
      have e1 : (refSite L hL 31 1).val = 1 := by rw [R 31 1 1 (by decide), cn1]
      have e2 : (refSite L hL 31 2).val = 0 := by rw [R 31 2 0 (by decide), cn0]
      refine blkBond_mem hL 31 2 (by decide) (Or.inr e0) (Or.inr e1) (Or.inl e2) e2 ?_
      intro hp; unfold EnergyEval.pinnedInBlock0 at hp
      rcases hp with h | ⟨h, _⟩ | ⟨_, h0, _⟩
      · change freeDir 31 = 0 at h; exact absurd h (by decide)
      · change freeDir 31 = 1 at h; exact absurd h (by decide)
      · have hc : ((freeCellBond L hL 31).1 0).val = 1 := e0
        omega

/-- **The Blk diagonal energy through `freecoord` (PROVED, no `sorry`).** On the admissible subspace,
the in-block bond energy of the reference block `0` equals the sum of `freecoord`-squares on the 5 free
in-block coordinates `blkIds`.  Companion to `Ell2RefBlock.topFace_total_freecoord`. -/
theorem blk_total_freecoord (hL : ∀ μ, 4 ≤ L μ) (C : Bond L → ℝ)
    (hC : C ∈ admissibleSubspaceInter L 2) :
    (∑ b ∈ bondsInBlock (0 : PeriodicLatticeSite L) 2, (C b) ^ 2)
      = ∑ i ∈ blkIds, (freecoord L hL C i) ^ 2 := by
  have hstrict : ∀ μ : Fin 3, (2 : ℕ) < L μ + 1 := fun μ => by have := hL μ; omega
  simp only [freecoord_apply]
  rw [EnergyEval.inBlock_energy_full_drop hstrict C hC, filter_eq_image hL,
    Finset.sum_image (fun i _ j _ h => freeCellBond_injective hL h)]

#print axioms blk_total_freecoord

end HrefBlk
