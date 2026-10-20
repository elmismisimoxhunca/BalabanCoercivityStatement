import AdalyFormal.Balaban.Ell2Discharge
import AdalyFormal.Balaban.QSlabExpand

set_option autoImplicit false
set_option maxHeartbeats 400000

/-! # `Ell2RefBlock` — `freecoord` and the reference-block sharpening of the `ell=2` `(geom)` residual.

This module executes the two structural prerequisites the prior `[RES-GEOM-REINDEX]` attempts had left
implicit, and SHARPENS the standing residual of `GeomGlobal.geomInequality_of_admissible_ell2` from the
whole-lattice `Hreindex` (`∀ z, ∃ c fc, LocalGeomBackward … z = c · sosQuadValue …`) down to a SINGLE
reference-block identity plus a translation-transport statement — the exact `(ii)`/`(iv)` split the
`EnergyEval`/`FreeCellFrame`/`BackwardTCert` docstrings name.

## What is DEFINED / PROVED here (no `sorry`, axiom-clean — `#print axioms` below).

* `freecoord` — **the free-cell coordinate extraction** `(Bond L → ℝ) → (Fin 80 → ℝ)`,
  `freecoord L hL B i := B (freeCellBond L hL i)`, a thin wrapper over the PROVED (injective,
  `FreeCellFrame.freeCellBond_injective`) free-cell bond enumeration.  This is the object the
  `Hreindex` identity is stated in terms of; the whole backward positivity certificate
  `BackwardTCert.backCertSparse` acts on `freecoord L hL B`.
* `topFace_total_freecoord` — the PROVED Top diagonal energy (`QSlabExpand.topFace_total`) re-expressed
  through `freecoord`, LOCKING the encoding: the free-cell coordinate framework really is the one the
  proved reference-block energy evaluations feed.
* `geomInequality_of_admissible_ell2_of_refBlockSOS` — **THE REFERENCE-BLOCK REDUCTION (PROVED, no
  `sorry`).**  From (a) the reference-block SOS identity `Href` — for EVERY admissible field the
  reference block's backward form equals a nonnegative multiple of the proved 56-square certificate's
  SOS value at `freecoord` — and (b) a per-block admissible transport `Htrans` onto the reference block,
  the `ell = 2` `(geom)` inequality `GeomInequality 2 B` follows.  Positivity is entirely outsourced to
  the axiom-clean `BackwardTCert.backTSparse_nonneg` (via the proved
  `Ell2Discharge.geomInequality_of_admissible_ell2_of_backwardReindex`); the sole open content is the
  pure IDENTITY `Href` at the single reference block, and the transport `Htrans`.

## HONEST SCOPE — what this does and does NOT close (§LEAN-D / no-success-lie).

This does **NOT** discharge `GeomGlobal.geomInequality_of_admissible_ell2`'s `sorry`.  It reduces it to
the two named residuals, both explicit Lean statements carried as HYPOTHESES (never a `sorry`):

* **`Href`** — the reference-block matrix identity `[RES-GEOM-REINDEX]` piece (ii).  Its content splits,
  per `EnergyEval`'s measured per-energy table, into:
    - Top (`−1/24`, 12 free coords, diagonal): **PROVED** — `QSlabExpand.topFace_total` /
      `topFace_total_freecoord` here.
    - Blk (`+3/2`, 5 free coords, diagonal): drop **PROVED** — `EnergyEval.inBlock_energy_full_drop`
      (still needs the `filter`-to-`freeCellBond` reindexing of the 5 free in-block bonds).
    - Q  (`+2`,  158 off-diagonal cross-terms): **the genuine wall** — the free-cell expansion of the
      squared `lineCoarseRestrict` line-integral forms at `prevSite μ` (torus-wrap).
    - Slab (`+1/4`, 312 off-diagonal cross-terms): **the genuine wall** — the free-cell expansion of the
      squared `curlValue` forms over `slabPlaqs (prevSite μ, μ)`.
    - the SOS reflection `sosQuadValue (backCertSparse.map castSparse) = W · (Gram T of the above)`
      (`[RES-CERT-KERNEL-REFLECT]`, MEASURED feasible, wiring pending).
  So `Href` is exactly the two off-diagonal walls (Q, Slab) plus the diagonal pieces (Top proved, Blk
  proved-drop) plus the SOS reflection — a multi-hundred-line, convention-sensitive construction, NOT
  built.  It is NAMED, not faked.
* **`Htrans`** — the translation transport `[RES-GEOM-REINDEX]` piece (iv): every coarse block `z`'s
  backward form equals the reference block's backward form of an admissible pullback of `B`.  The model
  is `CoarseShiftCovariance.coarseRestrict_shift_intertwine` (proved, for the operator `coarseRestrict`);
  the three energies of `LocalGeomBackward` (`lineCoarseRestrict`, `slabPlaqs`+`curlValue`,
  `topFaceEnergy`) each need their own such intertwining lemma — NOT built.

The `hL : ∀ μ, 4 ≤ L μ` accepted torus hypothesis (owner 2026-07-25) enters through `freeCellBond` /
`freecoord` (≥ 4 sites per direction, no wraparound collision) and subsumes the backward route's
`hstrict : 2 < L μ + 1`. -/

namespace Ell2RefBlock

open RatSOSEval
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open GeomGlobal
open BackwardCert
open Ell2Discharge
open FreeCellFrame
open BlockFaithful
open GeomScratch

variable {L : PeriodicLatticeExtent}

/-- **The free-cell coordinate extraction** `(Bond L → ℝ) → (Fin 80 → ℝ)`: coordinate `i` is the value
of `B` on the `i`-th free-cell bond `FreeCellFrame.freeCellBond L hL i` (the reference-block, staircase-
unpinned bond enumeration, PROVED injective).  This is the object on which the backward positivity
certificate `BackwardTCert.backCertSparse` acts; the `Hreindex` identity is `LocalGeomBackward … =
c · sosQuadValue (backCertSparse.map castSparse) (freecoord L hL B)`. -/
def freecoord (L : PeriodicLatticeExtent) (hL : ∀ μ, 4 ≤ L μ) (B : Bond L → ℝ) : Fin 80 → ℝ :=
  fun i => B (freeCellBond L hL i)

@[simp] theorem freecoord_apply (hL : ∀ μ, 4 ≤ L μ) (B : Bond L → ℝ) (i : Fin 80) :
    freecoord L hL B i = B (freeCellBond L hL i) := rfl

/-- **The Top diagonal energy through `freecoord` (PROVED, no `sorry`).** `QSlabExpand.topFace_total`
re-expressed in the `freecoord` framework: the sum over the three backward top-faces of the longitudinal
bond energy is the sum of `freecoord`-squares on the 12 free-cell Top coordinates.  This LOCKS that
`freecoord` is the coordinate object the proved reference-block energy evaluations feed. -/
theorem topFace_total_freecoord (hL : ∀ μ, 4 ≤ L μ) (B : Bond L → ℝ) :
    (∑ μ : Fin 3, topFaceEnergy B (prevSite μ) 2 μ)
      = ∑ i ∈ QSlabExpand.topIds, (freecoord L hL B i) ^ 2 := by
  rw [QSlabExpand.topFace_total hL B]
  rfl

/-- **THE REFERENCE-BLOCK REDUCTION (PROVED, no `sorry`).** From the reference-block SOS identity `Href`
(for every admissible field, the reference block's backward form equals a nonnegative multiple of the
proved 56-square certificate's SOS value at its `freecoord`) and the per-block admissible transport
`Htrans` (every block's backward form is the reference block's backward form of an admissible pullback),
the `ell = 2` `(geom)` inequality `GeomInequality 2 B` follows.

Positivity is entirely carried by the axiom-clean `BackwardTCert.backTSparse_nonneg` through the proved
`Ell2Discharge.geomInequality_of_admissible_ell2_of_backwardReindex`; the sole open content is the pure
IDENTITY `Href` at the SINGLE reference block plus the transport `Htrans` — `[RES-GEOM-REINDEX]` pieces
(ii) and (iv).  This SHARPENS the standing whole-lattice `Hreindex` residual (an existential quantified
over EVERY coarse block) to one reference-block identity and one transport statement. -/
theorem geomInequality_of_admissible_ell2_of_refBlockSOS
    (hL : ∀ μ : Fin 3, 4 ≤ L μ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2)
    (Href : ∀ (C : Bond L → ℝ), C ∈ admissibleSubspaceInter L 2 →
        ∃ c : ℝ, 0 ≤ c ∧
          LocalGeomBackward 2 hdvd C (refBlock L 2)
            = c * sosQuadValue (BackwardTCert.backCertSparse.map castSparse) (freecoord L hL C))
    (Htrans : ∀ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 2},
        ∃ (C : Bond L → ℝ), C ∈ admissibleSubspaceInter L 2 ∧
          LocalGeomBackward 2 hdvd B z = LocalGeomBackward 2 hdvd C (refBlock L 2)) :
    GeomInequality 2 B := by
  have hstrict : ∀ μ : Fin 3, (2 : ℕ) < L μ + 1 := fun μ => by have := hL μ; omega
  refine geomInequality_of_admissible_ell2_of_backwardReindex hdvd hstrict B hB ?_
  intro z
  obtain ⟨C, hC, hzC⟩ := Htrans z
  obtain ⟨c, hc, hCref⟩ := Href C hC
  exact ⟨c, freecoord L hL C, hc, by rw [hzC, hCref]⟩

#print axioms freecoord
#print axioms topFace_total_freecoord
#print axioms geomInequality_of_admissible_ell2_of_refBlockSOS

end Ell2RefBlock
