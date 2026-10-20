import AdalyFormal.Balaban.BlockFaithful

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # `EnergyEval` — per-energy evaluation of the reference-block backward form, piece (ii-rest) of
`[RES-GEOM-REINDEX]`.

`BlockFaithful.localGeomBackward_refBlock_explicit` (PROVED, axiom-clean) rewrites
`LocalGeomBackward 2 hdvd B (refBlock L 2)` as the explicit four-energy form at the pinned sites
`prevSite μ` (previous block) and the origin:

  `2·∑_μ (Q₁B)(prevSite μ,μ)² + ¼·∑_μ ∑_{p∈slab(prevSite μ,μ)} curl² − (1/24)·∑_μ topFace(prevSite μ,μ)
    + (3/2)·∑_{b⊂B(0)} B(b)²`.

Piece (ii) is the identity of THIS form with the reference Gram `⟨v(B), T v(B)⟩` on the 80 free-cell
coordinates (`compute/backward_cert/cert_backward.json`, verified residual 0, 200/200).

## The measured per-energy structure (`compute/energy_eval/per_energy_split.py`, exact ℚ, N∈{6,8}).

The four energies split into TWO classes (size-uniform N∈{6,8}, faithful sum residual 0, controls
in `controls.py` all move the residual):

| energy | scale | free coords | pinned bonds | off-diagonal? |
|--------|-------|-------------|--------------|---------------|
| `topFaceEnergy`  (Top) | −1/24 | 12 | 0  | **NO** (diagonal — individual-bond squares) |
| `bondsInBlock`   (Blk) | +3/2  | 5  | 7  | **NO** (diagonal — individual-bond squares) |
| `coarseQEnergy`  (Q)   | +2    | 22 | 14 | **YES** — 158 off-diagonal entries |
| `slabCurlEnergy` (Slab)| +1/4  | 78 | 36 | **YES** — 312 off-diagonal entries |

So **all 470 off-diagonal (cross-)terms of `T` live in the two energies Q and Slab** — the squares of
the line-integral and curl LINEAR FORMS with torus-wrap at `prevSite μ`.  Top and Blk are pure
diagonal sums of individual-bond squares and are the exemplar-tractable pieces; the admissibility
subspace drops their staircase-pinned bonds (Blk: 7 pinned; Top: 0 pinned).

## What is PROVED here (no `sorry`, axiom-clean).

* `inBlock_energy_dir0_drop` — the Blk-energy DIR-0 admissibility drop: on `admissibleSubspaceInter`,
  the in-block bond energy `∑_{b⊂B(0)} B(b)²` equals its restriction to the direction-`≠0` bonds,
  because every direction-`0` in-block bond vanishes (reusing `BlockPoincare.dir0_bond_eq_zero`, the
  proved "last staircase segment" lemma — LAW-19).  All 4 direction-`0` in-block bonds of block `0`
  are staircase-pinned (`compute/energy_eval/`), so this drop is exactly the dir-`0` slice of Blk's
  7-bond admissibility drop.

* `pinnedInBlock0` / `inBlock_energy_full_drop` — the COMPLETE Blk-energy admissibility drop: the
  in-block bond energy of block `0` equals its restriction to the 5 STAIRCASE-UNPINNED (free) bonds,
  all 7 pinned bonds vanishing.  The pinned predicate — dir-`0`, OR dir-`1` at coordinate-`0` `= 0`,
  OR dir-`2` at coordinates `0,1` both `= 0` — is EXACTLY the 7 staircase-pinned in-block bonds
  (`compute/energy_eval/per_energy_split.py`, verified all 12, size-uniform), and each class vanishes
  by the matching proved corner lemma: `dir0_bond_eq_zero`, `z0_bond1_eq_zero`, `w0_bond2_eq_zero`
  (LAW-19; `z0 0 b.1 = b.1` / `w0 0 b.1 = b.1` at these coordinates, so the corner lemmas apply with
  `x := b.1` — no bond enumeration needed).  This is the Blk energy fully evaluated onto its free
  coordinates — the diagonal `(3/2)·∑_{5 free}` contribution to `T`.

## The NAMED residual for a full piece (ii).

Full (ii) — `LocalGeomBackward 2 hdvd B 0 = ⟨v(B), T v(B)⟩` — additionally needs:
(a) the Top diagonal enumeration into its 12 free coords (wrap arithmetic at `prevSite μ`, 0 pinned)
    — **NOW PROVED, axiom-clean, in `QSlabExpand.topFace_total`** (downstream of this module):
    `∑_μ topFaceEnergy B (prevSite μ) 2 μ = ∑_{i∈topIds} B(freeCellBond i)²`, the 12 = 4+4+4 free
    coordinates `{1,9,12,14,28,37,48,51,64,67,71,74}`, via the reusable fitting-block enumeration
    `QSlabExpand.blockOf_fits_eq_image`;
(b) **the genuine wall — the Q and Slab OFF-DIAGONAL expansions**: the squares of
    `lineCoarseRestrict`/`curlValue` linear forms into the 470 cross-term coefficients of `T`, with
    the `prevSite μ` torus-wrap.  This is the multi-hundred-line convention-sensitive construction the
    module docstrings of `BackwardCert`/`FreeCellFrame`/`GeomGlobal` name; the per-energy split above
    localizes it precisely to these two energies (Q: 158, Slab: 312 off-diagonal entries). -/

namespace EnergyEval

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.BlockPoincare

variable {L : PeriodicLatticeExtent}

/-- **The Blk-energy direction-`0` admissibility drop (PROVED, no `sorry`).** On the intersection
admissible subspace, the in-block bond energy of the reference block `0` restricts to its
direction-`≠0` bonds: every direction-`0` bond with both endpoints in `blockOf 0 2` vanishes
(`BlockPoincare.dir0_bond_eq_zero`).  This is the exemplar-following admissibility drop for the
diagonal Blk energy, on its direction-`0` slice (all 4 dir-`0` in-block bonds are staircase-pinned,
`compute/energy_eval/per_energy_split.py`). -/
theorem inBlock_energy_dir0_drop (hstrict0 : (2 : ℕ) < L 0 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2) :
    (∑ b ∈ bondsInBlock (0 : PeriodicLatticeSite L) 2, (B b) ^ 2)
      = ∑ b ∈ (bondsInBlock (0 : PeriodicLatticeSite L) 2).filter (fun b => b.2 ≠ 0), (B b) ^ 2 := by
  conv_lhs =>
    rw [← Finset.sum_filter_add_sum_filter_not
        (bondsInBlock (0 : PeriodicLatticeSite L) 2) (fun b => b.2 ≠ 0) (fun b => (B b) ^ 2)]
  have hzero : (∑ b ∈ (bondsInBlock (0 : PeriodicLatticeSite L) 2).filter
        (fun b => ¬ b.2 ≠ 0), (B b) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_filter] at hb
    have hb2 : b.2 = 0 := by simpa using hb.2
    have hbb : bondInBlock (0 : PeriodicLatticeSite L) 2 b := mem_bondsInBlock.mp hb.1
    rw [dir0_bond_eq_zero hstrict0 B hB (0 : PeriodicLatticeSite L)
      (BlockFaithful.origin_mem_coarse 2) b hb2 hbb]
    ring
  rw [hzero, add_zero]

#print axioms inBlock_energy_dir0_drop

/-! ## §2. The COMPLETE Blk-energy admissibility drop (all 7 pinned bonds). -/

/-- **The staircase-pinned in-block bonds of the reference block `0`.** A bond `b ⊂ B(0)` is pinned
iff it is a direction-`0` bond, OR a direction-`1` bond based at coordinate-`0` `= 0`, OR a
direction-`2` bond based at coordinates `0` and `1` both `= 0`.  This predicate is EXACTLY the 7
staircase-pinned in-block bonds (`compute/energy_eval/per_energy_split.py`, checked against all 12,
size-uniform `N∈{6,8}`); its complement is the 5 free coords `{3,18,19,21,31}`. -/
def pinnedInBlock0 (b : Bond L) : Prop :=
  b.2 = 0 ∨ (b.2 = 1 ∧ (b.1 0).val = 0) ∨ (b.2 = 2 ∧ (b.1 0).val = 0 ∧ (b.1 1).val = 0)

instance (b : Bond L) : Decidable (pinnedInBlock0 b) := by unfold pinnedInBlock0; infer_instance

/-- Every pinned in-block bond of block `0` vanishes on the admissible subspace — dir-`0` by
`dir0_bond_eq_zero`, dir-`1`@`x₀=0` by `z0_bond1_eq_zero` (with `x := b.1`, since `z0 0 b.1 = b.1`),
dir-`2`@`x₀=x₁=0` by `w0_bond2_eq_zero` (with `x := b.1`, since `w0 0 b.1 = b.1`). -/
theorem pinned_inBlock0_eq_zero (hstrict : ∀ μ : Fin 3, (2 : ℕ) < L μ + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2)
    {b : Bond L} (hbb : bondInBlock (0 : PeriodicLatticeSite L) 2 b)
    (hpin : pinnedInBlock0 b) : B b = 0 := by
  obtain ⟨hb1mem, hshiftmem⟩ := hbb
  rcases hpin with h0 | ⟨hb2, hc0⟩ | ⟨hb2, hc0, hc1⟩
  · -- direction 0
    exact dir0_bond_eq_zero (hstrict 0) B hB (0 : PeriodicLatticeSite L)
      (BlockFaithful.origin_mem_coarse 2) b h0 ⟨hb1mem, hshiftmem⟩
  · -- direction 1, base coordinate 0 = 0  ⇒  z0 0 b.1 = b.1
    have hb10 : b.1 0 = 0 := Fin.ext (by rw [hc0]; rfl)
    have hz0 : z0 (0 : PeriodicLatticeSite L) b.1 = b.1 := by
      funext ν
      by_cases hν : ν = 0
      · subst hν; rw [z0_coord0]; exact hb10.symm
      · rw [z0_coord_ne _ _ hν]
    have hshift1 : periodicLatticeShift b.1 (1 : Fin 3) ∈ blockOf (0 : PeriodicLatticeSite L) 2 :=
      hb2 ▸ hshiftmem
    have hz := z0_bond1_eq_zero (hstrict 1) B hB (0 : PeriodicLatticeSite L)
      (BlockFaithful.origin_mem_coarse 2) b.1 hb1mem hshift1
    rw [hz0] at hz
    have hbe : b = (b.1, (1 : Fin 3)) := Prod.ext rfl hb2
    rw [hbe]; exact hz
  · -- direction 2, base coordinates 0,1 both = 0  ⇒  w0 0 b.1 = b.1
    have hb10 : b.1 0 = 0 := Fin.ext (by rw [hc0]; rfl)
    have hb11 : b.1 1 = 0 := Fin.ext (by rw [hc1]; rfl)
    have hw0 : w0 (0 : PeriodicLatticeSite L) b.1 = b.1 := by
      funext ν
      by_cases h0 : ν = 0
      · subst h0; rw [w0_coord0]; exact hb10.symm
      · by_cases h1 : ν = 1
        · subst h1; rw [w0_coord1]; exact hb11.symm
        · have h2 : ν = 2 := by
            have e0 : ν.val ≠ 0 := fun h => h0 (Fin.ext h)
            have e1 : ν.val ≠ 1 := fun h => h1 (Fin.ext h)
            have := ν.isLt; apply Fin.ext; omega
          subst h2; rw [w0_coord2]
    have hshift2 : periodicLatticeShift b.1 (2 : Fin 3) ∈ blockOf (0 : PeriodicLatticeSite L) 2 :=
      hb2 ▸ hshiftmem
    have hz := w0_bond2_eq_zero (hstrict 2) (0 : PeriodicLatticeSite L)
      (BlockFaithful.origin_mem_coarse 2) b.1 hb1mem hshift2 B hB
    rw [hw0] at hz
    have hbe : b = (b.1, (2 : Fin 3)) := Prod.ext rfl hb2
    rw [hbe]; exact hz

/-- **THE COMPLETE Blk-energy admissibility drop (PROVED, no `sorry`).** On the intersection
admissible subspace, the in-block bond energy of the reference block `0` equals its restriction to
the 5 staircase-unpinned (free) in-block bonds — all 7 pinned bonds vanish (`pinned_inBlock0_eq_zero`,
reusing the three proved corner-vanishing lemmas, LAW-19).  This is the diagonal Blk energy fully
evaluated onto its free coordinates: the `(3/2)·∑_{5 free} B(b)²` contribution to the reference Gram
`T`. -/
theorem inBlock_energy_full_drop (hstrict : ∀ μ : Fin 3, (2 : ℕ) < L μ + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2) :
    (∑ b ∈ bondsInBlock (0 : PeriodicLatticeSite L) 2, (B b) ^ 2)
      = ∑ b ∈ (bondsInBlock (0 : PeriodicLatticeSite L) 2).filter
          (fun b => ¬ pinnedInBlock0 b), (B b) ^ 2 := by
  conv_lhs =>
    rw [← Finset.sum_filter_add_sum_filter_not
        (bondsInBlock (0 : PeriodicLatticeSite L) 2) (fun b => pinnedInBlock0 b)
        (fun b => (B b) ^ 2)]
  have hzero : (∑ b ∈ (bondsInBlock (0 : PeriodicLatticeSite L) 2).filter
        (fun b => pinnedInBlock0 b), (B b) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_filter] at hb
    have hbb : bondInBlock (0 : PeriodicLatticeSite L) 2 b := mem_bondsInBlock.mp hb.1
    rw [pinned_inBlock0_eq_zero hstrict B hB hbb hb.2]; ring
  rw [hzero, zero_add]

#print axioms pinned_inBlock0_eq_zero
#print axioms inBlock_energy_full_drop

end EnergyEval
