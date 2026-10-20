import AdalyFormal.Balaban.EnergyEval

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! # `QSlabExpand` — the reference-block `ell=2` (2.128) last-mile expansions.

This module attacks the localized wall of piece (ii) of `[RES-GEOM-REINDEX]`: the free-cell
evaluation of the four reference-block energies of
`BlockFaithful.localGeomBackward_refBlock_explicit`
(`2·Q₀ + ¼·Slab₀ − (1/24)·Top₀ + (3/2)·Blk₀`) into the 80 free-cell bond coordinates and the
match to the certificate Gram `T`.

`EnergyEval.inBlock_energy_full_drop` (PROVED elsewhere) handles Blk.  Here:

* §1 — `blockOf_fits_eq_image`: the reusable enumeration of a *fitting* block as an explicit
  `Finset.image` over `Fin 3 → Fin ell` (LAW-19: extracted, not re-derived, from the `hbij`
  already proved inside `AdmissibleSubspace.card_blockOf`).  This is the single lemma that unblocks
  the symbolic-in-`L` Finset enumeration of ALL FOUR energies.
* §2 — the Top diagonal energy `∑_μ topFaceEnergy B (prevSite μ) 2 μ` evaluated onto its 12 free-cell
  coordinates (0 pinned), the tractable diagonal piece the wall triage flagged.

Numerical characterization: `compute/qslab/qslab_expand.py` (exact ℚ, `PYTHONHASHSEED=0`,
size-uniform N∈{6,8}, dual-run byte-identical): Q₀ = 3 line-integral forms (158 off-diagonal free
entries), Slab₀ = 48 curl forms (312 off-diagonal), `2·Q₀ + ¼·Slab₀` supplies EVERY off-diagonal
entry of `T` (residual 0, off-support 0), mutation controls all break it. -/

namespace QSlabExpand

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace

variable {L : PeriodicLatticeExtent}

/-! ## §1. The reusable fitting-block enumeration. -/

/-- **A fitting block as an explicit image (PROVED, no `sorry`).** When the block `B(y)` fits inside
the periodic extent on every axis (`hfit`), it equals the image of `Fin 3 → Fin ell` (the `ell³`
per-axis offset choices) under `f ↦ (μ ↦ y_μ + f_μ)`.  This is exactly the `hbij` step proved inside
`AdmissibleSubspace.card_blockOf`, extracted as a standalone lemma (LAW-19) so the four reference-
block energies can be enumerated symbolically in `L`. -/
theorem blockOf_fits_eq_image (y : PeriodicLatticeSite L) (ell : ℕ)
    (hfit : ∀ μ, (y μ).val + ell ≤ L μ + 1) :
    blockOf y ell = Finset.image
      (fun f : Fin 3 → Fin ell => (fun μ : Fin 3 => (⟨(y μ).val + (f μ).val, by
        have := (f μ).isLt; have := hfit μ; omega⟩ : Fin (L μ + 1)))) Finset.univ := by
  ext x
  simp only [mem_blockOf, inBlock, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    refine ⟨fun μ => ⟨(x μ).val - (y μ).val, ?_⟩, ?_⟩
    · have h1 := (hx μ).1
      have h2 := (hx μ).2
      omega
    · funext μ
      have h1 := (hx μ).1
      have h2 := (hx μ).2
      apply Fin.ext
      simp only
      omega
  · rintro ⟨f, rfl⟩
    intro μ
    simp only
    have := (f μ).isLt
    omega

#print axioms blockOf_fits_eq_image

/-! ## §2. The Top diagonal energy onto its 12 free-cell coordinates.

`∑_μ topFaceEnergy B (prevSite μ) 2 μ` is the sum, over the three backward top-faces, of the
longitudinal bond squares.  Each top face is 4 sites (the far μ-layer of the fitting 2-block at
`prevSite μ`), all of whose bonds `(x,μ)` are FREE (0 pinned).  The 12 free-cell indices are (numeric
characterization `compute/energy_eval/per_energy_split.py`, `mat_Top`/`crossSectionTop`, exact ℚ,
size-uniform N∈{6,8}; NOT `compute/qslab/qslab_expand.py`, which characterizes only the Q/Slab
OFF-diagonal energies):
`μ=0 → {64,67,71,74}` (dir 0, coord₀ = L₀), `μ=1 → {12,14,48,51}` (dir 1, coord₁ = L₁),
`μ=2 → {1,9,28,37}` (dir 2, coord₂ = L₂). -/

open GeomScratch
open AdalyFormal.Balaban.CrossSectionField
open BlockFaithful
open FreeCellFrame

/-- The 12 free-cell coordinates carrying the backward Top energy (dir-`μ` block, coord-`μ` `= L μ`). -/
def topIds : Finset (Fin 80) := {1, 9, 12, 14, 28, 37, 48, 51, 64, 67, 71, 74}

/-- The 4 top-face free-cell coordinates for direction `0` (coord₀ `= L₀`, dir `0`). -/
def topIds0 : Finset (Fin 80) := {64, 67, 71, 74}

/-- Every direction-`0` top-face free-cell coordinate has `freeDir = 0` (one `decide` over the
finset; reused so no per-use `fin_cases`/`decide` blows up the kernel on the 80-entry `codeList`). -/
theorem topIds0_freeDir : ∀ i ∈ topIds0, freeDir i = 0 := by decide

/-- `refSite`'s `ν`-coordinate value is the tabulated `coordNat` of its axis-`ν` code (PROVED). -/
theorem refSite_val (hL : ∀ μ, 4 ≤ L μ) (i : Fin 80) (ν : Fin 3) (c : Fin 5)
    (hc : axisCode (freeCode i) ν = c) : (refSite L hL i ν).val = coordNat L ν c := by
  show (coordFin L ν (hL ν) (axisCode (freeCode i) ν)).val = coordNat L ν c
  rw [hc]; rfl

/-- The three `coordNat` values used by the free-cell bonds, evaluated symbolically (PROVED). -/
theorem coordNat_vals (ν : Fin 3) :
    coordNat L ν 0 = 0 ∧ coordNat L ν 1 = 1 ∧ coordNat L ν 4 = L ν := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [coordNat]

/-- **Top diagonal energy, direction `0` (PROVED, no `sorry`).** The backward top-face energy in
direction `0` equals the sum of the squares of `B` on its 4 free-cell bonds `{64,67,71,74}`
(coord₀ `= L₀`, dir `0`). -/
theorem topFace_dir0 (hL : ∀ μ, 4 ≤ L μ) (B : Bond L → ℝ) :
    topFaceEnergy B (prevSite (0 : Fin 3)) 2 0
      = ∑ i ∈ topIds0, (B (freeCellBond L hL i)) ^ 2 := by
  have cn0 : ∀ ν : Fin 3, coordNat L ν 0 = 0 := fun ν => (coordNat_vals ν).1
  have cn1 : ∀ ν : Fin 3, coordNat L ν 1 = 1 := fun ν => (coordNat_vals ν).2.1
  have cn4 : ∀ ν : Fin 3, coordNat L ν 4 = L ν := fun ν => (coordNat_vals ν).2.2
  have hcs : crossSectionTop (prevSite (0 : Fin 3)) 2 0
      = Finset.image (refSite L hL) topIds0 := by
    ext x
    rw [mem_crossSectionTop, mem_blockOf]
    simp only [topIds0, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hblk, hc⟩
      have h0 : (x 0).val = L 0 := by
        have hp := prevSite_self (0 : Fin 3) (L := L)
        simp only [hp] at hc; have := hL 0; omega
      have hb1 := hblk 1; have hb2 := hblk 2
      rw [prevSite_ne 0 1 (by decide)] at hb1
      rw [prevSite_ne 0 2 (by decide)] at hb2
      simp only [Fin.val_zero, Nat.zero_add] at hb1 hb2
      obtain ⟨_, hb1r⟩ := hb1; obtain ⟨_, hb2r⟩ := hb2
      have hx1 : (x 1).val = 0 ∨ (x 1).val = 1 := by omega
      have hx2 : (x 2).val = 0 ∨ (x 2).val = 1 := by omega
      have mk : ∀ (i : Fin 80), (refSite L hL i 0).val = (x 0).val →
          (refSite L hL i 1).val = (x 1).val → (refSite L hL i 2).val = (x 2).val →
          refSite L hL i = x := by
        intro i q0 q1 q2; funext ν; fin_cases ν <;> apply Fin.ext <;> assumption
      have e0 : ∀ i : Fin 80, axisCode (freeCode i) 0 = 4 → (refSite L hL i 0).val = (x 0).val :=
        fun i h => by rw [refSite_val hL i 0 4 h, coordNat_vals (L := L) 0 |>.2.2, h0]
      rcases hx1 with hx1 | hx1 <;> rcases hx2 with hx2 | hx2
      · exact ⟨64, by tauto, mk 64 (e0 64 (by decide))
          (by rw [refSite_val hL 64 1 0 (by decide), cn0, hx1])
          (by rw [refSite_val hL 64 2 0 (by decide), cn0, hx2])⟩
      · exact ⟨67, by tauto, mk 67 (e0 67 (by decide))
          (by rw [refSite_val hL 67 1 0 (by decide), cn0, hx1])
          (by rw [refSite_val hL 67 2 1 (by decide), cn1, hx2])⟩
      · exact ⟨71, by tauto, mk 71 (e0 71 (by decide))
          (by rw [refSite_val hL 71 1 1 (by decide), cn1, hx1])
          (by rw [refSite_val hL 71 2 0 (by decide), cn0, hx2])⟩
      · exact ⟨74, by tauto, mk 74 (e0 74 (by decide))
          (by rw [refSite_val hL 74 1 1 (by decide), cn1, hx1])
          (by rw [refSite_val hL 74 2 1 (by decide), cn1, hx2])⟩
    · rintro ⟨i, hi, rfl⟩
      -- membership of each concrete refSite in the cross-section, coordinate by coordinate
      have memh : ∀ (j : Fin 80), axisCode (freeCode j) 0 = 4 →
          (axisCode (freeCode j) 1 = 0 ∨ axisCode (freeCode j) 1 = 1) →
          (axisCode (freeCode j) 2 = 0 ∨ axisCode (freeCode j) 2 = 1) →
          (∀ ν, ((prevSite (0:Fin 3) : PeriodicLatticeSite L) ν).val ≤ (refSite L hL j ν).val ∧
              (refSite L hL j ν).val < ((prevSite (0:Fin 3) : PeriodicLatticeSite L) ν).val + 2) ∧
            (refSite L hL j 0).val = ((prevSite (0:Fin 3) : PeriodicLatticeSite L) 0).val + (2 - 1) := by
        intro j a0 a1 a2
        have hL0 := hL 0
        refine ⟨fun ν => ?_, ?_⟩
        · by_cases hz : ν = 0
          · subst hz; rw [prevSite_self, refSite_val hL j 0 4 a0, cn4]; omega
          · by_cases ho : ν = 1
            · subst ho; rw [prevSite_ne 0 1 (by decide)]
              rcases a1 with a | a <;> rw [refSite_val hL j 1 _ a] <;>
                simp only [cn0, cn1, Fin.val_zero] <;> omega
            · have ht : ν = 2 := by
                have e0 : ν.val ≠ 0 := fun h => hz (Fin.ext h)
                have e1 : ν.val ≠ 1 := fun h => ho (Fin.ext h)
                have := ν.isLt; apply Fin.ext; omega
              subst ht; rw [prevSite_ne 0 2 (by decide)]
              rcases a2 with a | a <;> rw [refSite_val hL j 2 _ a] <;>
                simp only [cn0, cn1, Fin.val_zero] <;> omega
        · rw [prevSite_self, refSite_val hL j 0 4 a0, cn4]; omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        exact memh _ (by decide) (by decide) (by decide)
  rw [show topFaceEnergy B (prevSite (0:Fin 3)) 2 0
        = ∑ x ∈ crossSectionTop (prevSite (0:Fin 3)) 2 0, (B (x, (0:Fin 3))) ^ 2 from rfl, hcs,
      Finset.sum_image ?_]
  · apply Finset.sum_congr rfl
    intro i hi
    have hd : freeDir i = 0 := topIds0_freeDir i hi
    show (B (refSite L hL i, (0:Fin 3))) ^ 2 = (B (freeCellBond L hL i)) ^ 2
    rw [freeCellBond, hd]
  · -- injectivity of `refSite` on `topIds0`, via `freeCode_injective` (LAW-19), avoiding a
    -- 16-case `decide` (which blows up the kernel on the 80-entry `codeList`).
    intro i hi j hj h
    have hdi : freeDir i = 0 := topIds0_freeDir i hi
    have hdj : freeDir j = 0 := topIds0_freeDir j hj
    apply freeCode_injective
    have c0 : (freeCode i).1 = (freeCode j).1 := by
      simpa [axisCode] using coordFin_injective 0 (hL 0) (congrFun h 0)
    have c1 : (freeCode i).2.1 = (freeCode j).2.1 := by
      simpa [axisCode] using coordFin_injective 1 (hL 1) (congrFun h 1)
    have c2 : (freeCode i).2.2.1 = (freeCode j).2.2.1 := by
      simpa [axisCode] using coordFin_injective 2 (hL 2) (congrFun h 2)
    have cd : (freeCode i).2.2.2 = (freeCode j).2.2.2 := by
      have : freeDir i = freeDir j := by rw [hdi, hdj]
      simpa [freeDir] using this
    exact Prod.ext c0 (Prod.ext c1 (Prod.ext c2 cd))

#print axioms topFace_dir0

/-- The 4 top-face free-cell coordinates for direction `1` (coord₁ `= L₁`, dir `1`). -/
def topIds1 : Finset (Fin 80) := {12, 14, 48, 51}

theorem topIds1_freeDir : ∀ i ∈ topIds1, freeDir i = 1 := by decide

/-- **Top diagonal energy, direction `1` (PROVED, no `sorry`).** -/
theorem topFace_dir1 (hL : ∀ μ, 4 ≤ L μ) (B : Bond L → ℝ) :
    topFaceEnergy B (prevSite (1 : Fin 3)) 2 1
      = ∑ i ∈ topIds1, (B (freeCellBond L hL i)) ^ 2 := by
  have cn0 : ∀ ν : Fin 3, coordNat L ν 0 = 0 := fun ν => (coordNat_vals ν).1
  have cn1 : ∀ ν : Fin 3, coordNat L ν 1 = 1 := fun ν => (coordNat_vals ν).2.1
  have cn4 : ∀ ν : Fin 3, coordNat L ν 4 = L ν := fun ν => (coordNat_vals ν).2.2
  have hcs : crossSectionTop (prevSite (1 : Fin 3)) 2 1
      = Finset.image (refSite L hL) topIds1 := by
    ext x
    rw [mem_crossSectionTop, mem_blockOf]
    simp only [topIds1, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hblk, hc⟩
      have h1 : (x 1).val = L 1 := by
        have hp := prevSite_self (1 : Fin 3) (L := L)
        simp only [hp] at hc; have := hL 1; omega
      have hb0 := hblk 0; have hb2 := hblk 2
      rw [prevSite_ne 1 0 (by decide)] at hb0
      rw [prevSite_ne 1 2 (by decide)] at hb2
      simp only [Fin.val_zero, Nat.zero_add] at hb0 hb2
      obtain ⟨_, hb0r⟩ := hb0; obtain ⟨_, hb2r⟩ := hb2
      have hx0 : (x 0).val = 0 ∨ (x 0).val = 1 := by omega
      have hx2 : (x 2).val = 0 ∨ (x 2).val = 1 := by omega
      have mk : ∀ (i : Fin 80), (refSite L hL i 0).val = (x 0).val →
          (refSite L hL i 1).val = (x 1).val → (refSite L hL i 2).val = (x 2).val →
          refSite L hL i = x := by
        intro i q0 q1 q2; funext ν; fin_cases ν <;> apply Fin.ext <;> assumption
      have eL : ∀ i : Fin 80, axisCode (freeCode i) 1 = 4 → (refSite L hL i 1).val = (x 1).val :=
        fun i h => by rw [refSite_val hL i 1 4 h, coordNat_vals (L := L) 1 |>.2.2, h1]
      rcases hx0 with hx0 | hx0 <;> rcases hx2 with hx2 | hx2
      · exact ⟨12, by tauto, mk 12
          (by rw [refSite_val hL 12 0 0 (by decide), cn0, hx0]) (eL 12 (by decide))
          (by rw [refSite_val hL 12 2 0 (by decide), cn0, hx2])⟩
      · exact ⟨14, by tauto, mk 14
          (by rw [refSite_val hL 14 0 0 (by decide), cn0, hx0]) (eL 14 (by decide))
          (by rw [refSite_val hL 14 2 1 (by decide), cn1, hx2])⟩
      · exact ⟨48, by tauto, mk 48
          (by rw [refSite_val hL 48 0 1 (by decide), cn1, hx0]) (eL 48 (by decide))
          (by rw [refSite_val hL 48 2 0 (by decide), cn0, hx2])⟩
      · exact ⟨51, by tauto, mk 51
          (by rw [refSite_val hL 51 0 1 (by decide), cn1, hx0]) (eL 51 (by decide))
          (by rw [refSite_val hL 51 2 1 (by decide), cn1, hx2])⟩
    · rintro ⟨i, hi, rfl⟩
      have memh : ∀ (j : Fin 80), axisCode (freeCode j) 1 = 4 →
          (axisCode (freeCode j) 0 = 0 ∨ axisCode (freeCode j) 0 = 1) →
          (axisCode (freeCode j) 2 = 0 ∨ axisCode (freeCode j) 2 = 1) →
          (∀ ν, ((prevSite (1:Fin 3) : PeriodicLatticeSite L) ν).val ≤ (refSite L hL j ν).val ∧
              (refSite L hL j ν).val < ((prevSite (1:Fin 3) : PeriodicLatticeSite L) ν).val + 2) ∧
            (refSite L hL j 1).val = ((prevSite (1:Fin 3) : PeriodicLatticeSite L) 1).val + (2 - 1) := by
        intro j aL a0 a2
        have hL1 := hL 1
        refine ⟨fun ν => ?_, ?_⟩
        · by_cases hz : ν = 1
          · subst hz; rw [prevSite_self, refSite_val hL j 1 4 aL, cn4]; omega
          · by_cases ho : ν = 0
            · subst ho; rw [prevSite_ne 1 0 (by decide)]
              rcases a0 with a | a <;> rw [refSite_val hL j 0 _ a] <;>
                simp only [cn0, cn1, Fin.val_zero] <;> omega
            · have ht : ν = 2 := by
                have e0 : ν.val ≠ 1 := fun h => hz (Fin.ext h)
                have e1 : ν.val ≠ 0 := fun h => ho (Fin.ext h)
                have := ν.isLt; apply Fin.ext; omega
              subst ht; rw [prevSite_ne 1 2 (by decide)]
              rcases a2 with a | a <;> rw [refSite_val hL j 2 _ a] <;>
                simp only [cn0, cn1, Fin.val_zero] <;> omega
        · rw [prevSite_self, refSite_val hL j 1 4 aL, cn4]; omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        exact memh _ (by decide) (by decide) (by decide)
  rw [show topFaceEnergy B (prevSite (1:Fin 3)) 2 1
        = ∑ x ∈ crossSectionTop (prevSite (1:Fin 3)) 2 1, (B (x, (1:Fin 3))) ^ 2 from rfl, hcs,
      Finset.sum_image ?_]
  · apply Finset.sum_congr rfl
    intro i hi
    have hd : freeDir i = 1 := topIds1_freeDir i hi
    show (B (refSite L hL i, (1:Fin 3))) ^ 2 = (B (freeCellBond L hL i)) ^ 2
    rw [freeCellBond, hd]
  · intro i hi j hj h
    have hdi : freeDir i = 1 := topIds1_freeDir i hi
    have hdj : freeDir j = 1 := topIds1_freeDir j hj
    apply freeCode_injective
    have c0 : (freeCode i).1 = (freeCode j).1 := by
      simpa [axisCode] using coordFin_injective 0 (hL 0) (congrFun h 0)
    have c1 : (freeCode i).2.1 = (freeCode j).2.1 := by
      simpa [axisCode] using coordFin_injective 1 (hL 1) (congrFun h 1)
    have c2 : (freeCode i).2.2.1 = (freeCode j).2.2.1 := by
      simpa [axisCode] using coordFin_injective 2 (hL 2) (congrFun h 2)
    have cd : (freeCode i).2.2.2 = (freeCode j).2.2.2 := by
      have : freeDir i = freeDir j := by rw [hdi, hdj]
      simpa [freeDir] using this
    exact Prod.ext c0 (Prod.ext c1 (Prod.ext c2 cd))

#print axioms topFace_dir1

/-- The 4 top-face free-cell coordinates for direction `2` (coord₂ `= L₂`, dir `2`). -/
def topIds2 : Finset (Fin 80) := {1, 9, 28, 37}

theorem topIds2_freeDir : ∀ i ∈ topIds2, freeDir i = 2 := by decide

/-- **Top diagonal energy, direction `2` (PROVED, no `sorry`).** -/
theorem topFace_dir2 (hL : ∀ μ, 4 ≤ L μ) (B : Bond L → ℝ) :
    topFaceEnergy B (prevSite (2 : Fin 3)) 2 2
      = ∑ i ∈ topIds2, (B (freeCellBond L hL i)) ^ 2 := by
  have cn0 : ∀ ν : Fin 3, coordNat L ν 0 = 0 := fun ν => (coordNat_vals ν).1
  have cn1 : ∀ ν : Fin 3, coordNat L ν 1 = 1 := fun ν => (coordNat_vals ν).2.1
  have cn4 : ∀ ν : Fin 3, coordNat L ν 4 = L ν := fun ν => (coordNat_vals ν).2.2
  have hcs : crossSectionTop (prevSite (2 : Fin 3)) 2 2
      = Finset.image (refSite L hL) topIds2 := by
    ext x
    rw [mem_crossSectionTop, mem_blockOf]
    simp only [topIds2, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hblk, hc⟩
      have h2 : (x 2).val = L 2 := by
        have hp := prevSite_self (2 : Fin 3) (L := L)
        simp only [hp] at hc; have := hL 2; omega
      have hb0 := hblk 0; have hb1 := hblk 1
      rw [prevSite_ne 2 0 (by decide)] at hb0
      rw [prevSite_ne 2 1 (by decide)] at hb1
      simp only [Fin.val_zero, Nat.zero_add] at hb0 hb1
      obtain ⟨_, hb0r⟩ := hb0; obtain ⟨_, hb1r⟩ := hb1
      have hx0 : (x 0).val = 0 ∨ (x 0).val = 1 := by omega
      have hx1 : (x 1).val = 0 ∨ (x 1).val = 1 := by omega
      have mk : ∀ (i : Fin 80), (refSite L hL i 0).val = (x 0).val →
          (refSite L hL i 1).val = (x 1).val → (refSite L hL i 2).val = (x 2).val →
          refSite L hL i = x := by
        intro i q0 q1 q2; funext ν; fin_cases ν <;> apply Fin.ext <;> assumption
      have eL : ∀ i : Fin 80, axisCode (freeCode i) 2 = 4 → (refSite L hL i 2).val = (x 2).val :=
        fun i h => by rw [refSite_val hL i 2 4 h, coordNat_vals (L := L) 2 |>.2.2, h2]
      rcases hx0 with hx0 | hx0 <;> rcases hx1 with hx1 | hx1
      · exact ⟨1, by tauto, mk 1
          (by rw [refSite_val hL 1 0 0 (by decide), cn0, hx0])
          (by rw [refSite_val hL 1 1 0 (by decide), cn0, hx1]) (eL 1 (by decide))⟩
      · exact ⟨9, by tauto, mk 9
          (by rw [refSite_val hL 9 0 0 (by decide), cn0, hx0])
          (by rw [refSite_val hL 9 1 1 (by decide), cn1, hx1]) (eL 9 (by decide))⟩
      · exact ⟨28, by tauto, mk 28
          (by rw [refSite_val hL 28 0 1 (by decide), cn1, hx0])
          (by rw [refSite_val hL 28 1 0 (by decide), cn0, hx1]) (eL 28 (by decide))⟩
      · exact ⟨37, by tauto, mk 37
          (by rw [refSite_val hL 37 0 1 (by decide), cn1, hx0])
          (by rw [refSite_val hL 37 1 1 (by decide), cn1, hx1]) (eL 37 (by decide))⟩
    · rintro ⟨i, hi, rfl⟩
      have memh : ∀ (j : Fin 80), axisCode (freeCode j) 2 = 4 →
          (axisCode (freeCode j) 0 = 0 ∨ axisCode (freeCode j) 0 = 1) →
          (axisCode (freeCode j) 1 = 0 ∨ axisCode (freeCode j) 1 = 1) →
          (∀ ν, ((prevSite (2:Fin 3) : PeriodicLatticeSite L) ν).val ≤ (refSite L hL j ν).val ∧
              (refSite L hL j ν).val < ((prevSite (2:Fin 3) : PeriodicLatticeSite L) ν).val + 2) ∧
            (refSite L hL j 2).val = ((prevSite (2:Fin 3) : PeriodicLatticeSite L) 2).val + (2 - 1) := by
        intro j aL a0 a1
        have hL2 := hL 2
        refine ⟨fun ν => ?_, ?_⟩
        · by_cases hz : ν = 2
          · subst hz; rw [prevSite_self, refSite_val hL j 2 4 aL, cn4]; omega
          · by_cases ho : ν = 0
            · subst ho; rw [prevSite_ne 2 0 (by decide)]
              rcases a0 with a | a <;> rw [refSite_val hL j 0 _ a] <;>
                simp only [cn0, cn1, Fin.val_zero] <;> omega
            · have ht : ν = 1 := by
                have e0 : ν.val ≠ 2 := fun h => hz (Fin.ext h)
                have e1 : ν.val ≠ 0 := fun h => ho (Fin.ext h)
                have := ν.isLt; apply Fin.ext; omega
              subst ht; rw [prevSite_ne 2 1 (by decide)]
              rcases a1 with a | a <;> rw [refSite_val hL j 1 _ a] <;>
                simp only [cn0, cn1, Fin.val_zero] <;> omega
        · rw [prevSite_self, refSite_val hL j 2 4 aL, cn4]; omega
      rcases hi with rfl | rfl | rfl | rfl <;>
        exact memh _ (by decide) (by decide) (by decide)
  rw [show topFaceEnergy B (prevSite (2:Fin 3)) 2 2
        = ∑ x ∈ crossSectionTop (prevSite (2:Fin 3)) 2 2, (B (x, (2:Fin 3))) ^ 2 from rfl, hcs,
      Finset.sum_image ?_]
  · apply Finset.sum_congr rfl
    intro i hi
    have hd : freeDir i = 2 := topIds2_freeDir i hi
    show (B (refSite L hL i, (2:Fin 3))) ^ 2 = (B (freeCellBond L hL i)) ^ 2
    rw [freeCellBond, hd]
  · intro i hi j hj h
    have hdi : freeDir i = 2 := topIds2_freeDir i hi
    have hdj : freeDir j = 2 := topIds2_freeDir j hj
    apply freeCode_injective
    have c0 : (freeCode i).1 = (freeCode j).1 := by
      simpa [axisCode] using coordFin_injective 0 (hL 0) (congrFun h 0)
    have c1 : (freeCode i).2.1 = (freeCode j).2.1 := by
      simpa [axisCode] using coordFin_injective 1 (hL 1) (congrFun h 1)
    have c2 : (freeCode i).2.2.1 = (freeCode j).2.2.1 := by
      simpa [axisCode] using coordFin_injective 2 (hL 2) (congrFun h 2)
    have cd : (freeCode i).2.2.2 = (freeCode j).2.2.2 := by
      have : freeDir i = freeDir j := by rw [hdi, hdj]
      simpa [freeDir] using this
    exact Prod.ext c0 (Prod.ext c1 (Prod.ext c2 cd))

#print axioms topFace_dir2

/-- **THE FULL Top diagonal energy onto its 12 free-cell coordinates (PROVED, no `sorry`).** The sum
over the three backward top-faces of the longitudinal bond energy equals the sum of `B`-squares on
the 12 free-cell coordinates `topIds = topIds0 ∪ topIds1 ∪ topIds2` (all free, 0 pinned). This is Top's
exact `−(1/24)·∑ᵢ B(freeCellBond i)²` diagonal contribution to the reference Gram `T`
(numeric characterization `compute/energy_eval/per_energy_split.py`, `mat_Top`; the Top energy is
diagonal, so it needs no cross-term expansion — unlike the Q and Slab walls, whose off-diagonal
characterization is `compute/qslab/qslab_expand.py`). -/
theorem topFace_total (hL : ∀ μ, 4 ≤ L μ) (B : Bond L → ℝ) :
    (∑ μ : Fin 3, topFaceEnergy B (prevSite μ) 2 μ)
      = ∑ i ∈ topIds, (B (freeCellBond L hL i)) ^ 2 := by
  rw [Fin.sum_univ_three, topFace_dir0 hL B, topFace_dir1 hL B, topFace_dir2 hL B,
      show topIds = topIds0 ∪ topIds1 ∪ topIds2 from by decide,
      Finset.sum_union (by decide), Finset.sum_union (by decide)]

#print axioms topFace_total

end QSlabExpand
