import AdalyFormal.Balaban.EnergyIntertwine
import AdalyFormal.Balaban.HrefBlk
import AdalyFormal.Balaban.SparseGram
import AdalyFormal.Balaban.BackwardTCert
import AdalyFormal.Balaban.HrefRefl
import AdalyFormal.Balaban.HrefQSlab

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # `HrefReduction` — the reference-block SOS identity `Href` reduced to its TWO precise walls,
with the two PROVED diagonal energies banked in.

`Ell2RefBlock.geomInequality_of_admissible_ell2_of_refBlockSOS` reduces the `ell = 2` `(geom)`
inequality to the monolithic reference-block SOS identity `Href` (plus the now-discharged `Htrans`).
This module opens `Href` up one level, using `BlockFaithful.localGeomBackward_refBlock_explicit`
(the explicit four-energy form) together with the TWO already-proved DIAGONAL bricks:

* `Ell2RefBlock.topFace_total_freecoord` — Top `= ∑_{i∈topIds} (freecoord C i)²`, and
* `HrefBlk.blk_total_freecoord`         — Blk `= ∑_{i∈blkIds} (freecoord C i)²`.

Substituting these, `Href` follows from EXACTLY the two remaining OFF-diagonal / reflection walls,
each carried as a precisely-typed HYPOTHESIS (never a `sorry`):

* **`hQS`** — the **Q+Slab reindex** `[RES-GEOM-REINDEX] (ii-offdiag)`.  On the admissible subspace,
    `2·(∑_μ line²) + ¼·(∑_μ ∑_p curl²) = (1/128)·sosQuadValue qsCertSparse (freecoord C)`,
  i.e. the two off-diagonal energies expressed via the **SMALL-INTEGER** `SparseGram.qsCertSparse`
  (coefficients ≤ 32, covector entries ≤ 3).  Verified residual 0, exact ℚ, size-uniform N∈{6,8}:
  `compute/href_identity/sparse_reflect_analysis.py` [`Gram(qsCert) = 256·G_Q + 32·G_Slab`] and the
  prior `compute/qslab/qslab_expand.py` / `compute/qslab_energy/decisive.py`.  This is the genuine
  torus-geometry wall (free-cell expansion of `lineCoarseRestrict`/`curlValue` at `prevSite μ`, with
  the `+e_μ` torus wrap); the ARITHMETIC is small-integer, the difficulty is the geometry.

* **`hrefl`** — the **SOS-basis reflection** `[RES-CERT-KERNEL-REFLECT]`.  A pure free-coordinate
  identity `sosQuadValue backCertSparse x = W · M(x)` where
    `M(x) = (1/128)·sosQuadValue qsCertSparse x − (1/24)·∑topIds x² + (3/2)·∑blkIds x²`
  is the `LocalGeomBackward0` quadratic form.  Verified residual 0
  (`sparse_reflect_analysis.py` (3): `Gram(backCert) = W·T`).  MEASURED to be the intrinsically
  HARD wall: `backCertSparse` is a DIFFERENT SOS basis than the energy forms (only 20/56 squares
  share a support with an energy form — `sparse_reflect_analysis.py` (5)), so the sparse
  "match covector sets" shortcut does NOT apply; and the integers are intrinsically huge — even the
  minimal rational LDL of `T` has ≥ 10-digit pivots / 27-digit integer weights
  (`sparse_reflect_analysis.py` (4)), so NO small-integer T-cert exists.  This is exactly why the
  naive dense `∀ a b, gram backCertI a b = T a b` timed out > 500 s (`compute/tcert/gram_probe.out`,
  EXIT 124, WALL 500.78 s); its sound kernel reflection needs the `RatSOSEval.STree` balanced-tree
  wiring (`compute/tcert/backcert_gram_kernel_check.lean` checks the ARITHMETIC in 3.63 s but is not
  yet wired through `RatSOSEval.gram`).

## HONEST SCOPE — what this does and does NOT close (§LEAN-D / no-success-lie).

⚠ **S75, 2026-07-28: the sentence below is SUPERSEDED, retained struck.**  There is no longer any
`sorry` in `GeomGlobal` to discharge: the two stubs were DELETED from `GeomGlobal.lean` and
re-declared, proved, into the same namespace by the leaf `AdalyFormal.Balaban.GeomBaseClosed` (which
imports this module).  `GeomGlobal.geomInequality_of_admissible_ell2` now has axiom cone
`{propext, Classical.choice, Quot.sound}`.  What the sentence below says about THIS theorem
(`href_of_QSlab_refl` reduces `Href` to `hQS ∧ hrefl` and does not itself close them) is still true.

~~This does **NOT** discharge `GeomGlobal.geomInequality_of_admissible_ell2`'s `sorry`.~~  It BANKS the
two diagonal energies into the `Href` reduction (they were islands) and reduces `Href` to `hQS ∧
hrefl` — the two walls precisely typed.  Both hypotheses are numerically VERIFIED true (residual 0,
above), so they are the correct next targets, not artefacts.  `#print axioms` on the reduction below
is `{propext, Classical.choice, Quot.sound}` — no `sorryAx`. -/

namespace AdalyFormal.Balaban.HrefReduction

open Finset
open RatSOSEval
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.Lemma24Assembly
open AdalyFormal.Balaban.CrossSectionField
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.BlockPoincareLemma24
open GeomScratch
open BackwardCert
open BlockFaithful
open Ell2RefBlock
open HrefBlk
open QSlabExpand

variable {L : PeriodicLatticeExtent}

/-- **`Href` FROM THE TWO WALLS (PROVED, no `sorry`, axiom-clean).**  The reference-block SOS identity
`Href` (the residual of `Ell2RefBlock.geomInequality_of_admissible_ell2_of_refBlockSOS`) follows from
the Q+Slab reindex `hQS` and the SOS-basis reflection `hrefl`, with the two diagonal energies (Top,
Blk) supplied by the already-proved bricks `topFace_total_freecoord` / `blk_total_freecoord`.

`hQS` and `hrefl` are the two named remaining walls, each numerically verified residual 0
(`compute/href_identity/sparse_reflect_analysis.py`).  The witness is `c = 1/W ≥ 0`. -/
theorem href_of_QSlab_refl
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (W : ℝ) (hW : 0 < W)
    (hQS : ∀ (C : Bond L → ℝ), C ∈ admissibleSubspaceInter L 2 →
        ((2 : ℕ) : ℝ) * (∑ μ : Fin 3,
              (lineCoarseRestrict 2 C (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ)) ^ 2)
          + (1 / ((2 : ℕ) : ℝ) ^ 2) * (∑ μ : Fin 3,
              ∑ p ∈ slabPlaqs (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ), (curlValue C p) ^ 2)
          = (1 / 128) * sosQuadValue (SparseGram.qsCertSparse.map castSparse) (freecoord L hL C))
    (hrefl : ∀ x : Fin 80 → ℝ,
        sosQuadValue (BackwardTCert.backCertSparse.map castSparse) x
          = W * ((1 / 128) * sosQuadValue (SparseGram.qsCertSparse.map castSparse) x
                  - (1 / 3) * (1 / ((2 : ℕ) : ℝ) ^ 3) * (∑ i ∈ topIds, (x i) ^ 2)
                  + 6 * (1 / ((2 : ℕ) : ℝ) ^ 2) * (∑ i ∈ blkIds, (x i) ^ 2))) :
    ∀ (C : Bond L → ℝ), C ∈ admissibleSubspaceInter L 2 →
      ∃ c : ℝ, 0 ≤ c ∧
        LocalGeomBackward 2 hdvd C (refBlock L 2)
          = c * sosQuadValue (BackwardTCert.backCertSparse.map castSparse) (freecoord L hL C) := by
  intro C hC
  have hWne : W ≠ 0 := ne_of_gt hW
  refine ⟨1 / W, one_div_nonneg.mpr hW.le, ?_⟩
  rw [localGeomBackward_refBlock_explicit hdvd C,
    topFace_total_freecoord hL C, blk_total_freecoord hL C hC, hQS C hC,
    hrefl (freecoord L hL C)]
  field_simp

#print axioms href_of_QSlab_refl

/-- **The `ell = 2` `(geom)` inequality FROM THE TWO WALLS (PROVED, no `sorry`, axiom-clean).**
Chains `href_of_QSlab_refl` through the capstone
`EnergyIntertwine.geomInequality_of_admissible_ell2_of_Href` (which has already discharged the
translation transport `Htrans`).  So `GeomInequality 2 B` now follows from EXACTLY the two named
walls `hQS` (Q+Slab reindex, small-integer) and `hrefl` (SOS-basis reflection, huge-integer) — the
diagonal energies and the transport are all banked.  This is the sharpest current statement of what
the `ell = 2` U=1 Bałaban Lemma 2.4 milestone rests on. -/
theorem geomInequality_of_admissible_ell2_of_QSlab_refl
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2)
    (W : ℝ) (hW : 0 < W)
    (hQS : ∀ (C : Bond L → ℝ), C ∈ admissibleSubspaceInter L 2 →
        ((2 : ℕ) : ℝ) * (∑ μ : Fin 3,
              (lineCoarseRestrict 2 C (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ)) ^ 2)
          + (1 / ((2 : ℕ) : ℝ) ^ 2) * (∑ μ : Fin 3,
              ∑ p ∈ slabPlaqs (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ), (curlValue C p) ^ 2)
          = (1 / 128) * sosQuadValue (SparseGram.qsCertSparse.map castSparse) (freecoord L hL C))
    (hrefl : ∀ x : Fin 80 → ℝ,
        sosQuadValue (BackwardTCert.backCertSparse.map castSparse) x
          = W * ((1 / 128) * sosQuadValue (SparseGram.qsCertSparse.map castSparse) x
                  - (1 / 3) * (1 / ((2 : ℕ) : ℝ) ^ 3) * (∑ i ∈ topIds, (x i) ^ 2)
                  + 6 * (1 / ((2 : ℕ) : ℝ) ^ 2) * (∑ i ∈ blkIds, (x i) ^ 2))) :
    GeomGlobal.GeomInequality 2 B :=
  EnergyIntertwine.geomInequality_of_admissible_ell2_of_Href hL hdvd B hB
    (href_of_QSlab_refl hL hdvd W hW hQS hrefl)

#print axioms geomInequality_of_admissible_ell2_of_QSlab_refl

/-- **The `ell = 2` `(geom)` inequality FROM THE Q+Slab REINDEX ALONE — `hrefl` now PROVED.**
The SOS-basis reflection wall `hrefl` is discharged by `HrefRefl.hrefl_proved` (axiom-clean; the
entrywise reflection identity `384·gram_bc = W·(3·gram_qs − 16·Dtop + 576·Dblk)` checked by a strict
kernel `rfl` over the real `RatSOSEval.gram` of the real certificates, `~326 s`, no `native_decide`),
at the explicit scale `W = HrefRefl.Wint > 0` (`HrefRefl.Wpos`).  So `GeomInequality 2 B` now follows
from EXACTLY the single remaining wall `hQS` — the Q+Slab reindex `[RES-GEOM-REINDEX] (ii-offdiag)`, a
separate lane's target.  This is the sharpest current statement of the `ell = 2` U=1 Bałaban Lemma 2.4
milestone: it rests on `hQS` alone (the diagonal energies, the transport, and the reflection are all
banked). -/
theorem geomInequality_of_admissible_ell2_of_QSlab
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2)
    (hQS : ∀ (C : Bond L → ℝ), C ∈ admissibleSubspaceInter L 2 →
        ((2 : ℕ) : ℝ) * (∑ μ : Fin 3,
              (lineCoarseRestrict 2 C (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ)) ^ 2)
          + (1 / ((2 : ℕ) : ℝ) ^ 2) * (∑ μ : Fin 3,
              ∑ p ∈ slabPlaqs (⟨prevSite μ, prevSite_mem μ hdvd⟩, μ), (curlValue C p) ^ 2)
          = (1 / 128) * sosQuadValue (SparseGram.qsCertSparse.map castSparse) (freecoord L hL C)) :
    GeomGlobal.GeomInequality 2 B :=
  geomInequality_of_admissible_ell2_of_QSlab_refl hL hdvd B hB
    ((HrefRefl.Wint : ℝ)) HrefRefl.Wpos hQS HrefRefl.hrefl_proved

#print axioms geomInequality_of_admissible_ell2_of_QSlab

/-! ## THE MILESTONE — `hQS` now PROVED, so `(geom)` and Lemma 2.4 are UNCONDITIONAL at U=1, ell=2.

`HrefQSlab.hQS_proved` (axiom-clean) discharges the last wall `hQS` (the Q+Slab reindex).  Chaining it
through `geomInequality_of_admissible_ell2_of_QSlab` (whose `hrefl` is already `HrefRefl.hrefl_proved`)
gives `GeomInequality 2 B` UNCONDITIONALLY, and then `GeomGlobal.lemma24_unconditional_of_geom` gives
`Lemma24Conclusion 2 B` — the first fully unconditional U=1, ell=2 Bałaban Lemma 2.4 (accepted torus
scope `hL : ∀ μ, 4 ≤ L μ`, `hdvd : ∀ μ, 2 ∣ L μ + 1`).  NO `sorry`, `#print axioms` = {propext,
Classical.choice, Quot.sound}.

NOTE (import direction) — ⚠ **S75, 2026-07-28: CORRECTED. The old note is struck below; the word
"unremovable" was wrong.**  The cycle is real (verified by enumerating every simple import path:
exactly two, both ending on the edge `GeomOperatorSOS → GeomGlobal`), but it forced only that the
CLOSED PROOF cannot be written inside `GeomGlobal.lean` — it never forced the `sorry` to STAY there.
The two stubs have been DELETED from `GeomGlobal.lean` and re-declared, proved, into the same
`GeomGlobal` namespace by the leaf module `AdalyFormal.Balaban.GeomBaseClosed`, which imports THIS
module and so sees both sides.  `GeomGlobal.geomInequality_of_admissible_ell2` and
`GeomGlobal.lemma24_unconditional_U1_ell2` therefore still resolve, now with axiom cone
`{propext, Classical.choice, Quot.sound}`.  Statement identity was machine-checked against the stubs
before deletion (`compute/geom_cycle/CONTROLS.log`, two must-fail controls firing).  The `_uncond`
theorems below remain the hypothesis-minimal forms and the ones to consume in new code.

~~NOTE (import direction): `GeomGlobal.geomInequality_of_admissible_ell2` keeps its `sorry` — it is
STRUCTURALLY unremovable here because `HrefReduction` (this module) already depends on `GeomGlobal`
(via `EnergyIntertwine`), so `GeomGlobal` cannot import the reduction chain without a cycle.  The
unconditional result therefore lives HERE (the module that can see both the reduction and the closed
`hQS`); `GeomGlobal`'s stub is SUPERSEDED by `lemma24_unconditional_U1_ell2_uncond` below.~~ -/
theorem geomInequality_of_admissible_ell2_uncond
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2) :
    GeomGlobal.GeomInequality 2 B :=
  geomInequality_of_admissible_ell2_of_QSlab hL hdvd B hB
    (fun C hC => HrefQSlab.hQS_proved hL hdvd C hC)

#print axioms geomInequality_of_admissible_ell2_uncond

/-- **`Lemma24Conclusion` at U=1, `ell = 2`, FULLY UNCONDITIONAL (PROVED, no `sorry`, axiom-clean).**
The `ell = 2` U=1 Bałaban Lemma 2.4 milestone: for admissible `B` on any torus with `4 ≤ L μ` and
`2 ∣ L μ + 1`, `Lemma24Conclusion 2 B` holds unconditionally.  `hstrict` is derived from `hL`. -/
theorem lemma24_unconditional_U1_ell2_uncond
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2) :
    Lemma24Conclusion 2 B :=
  GeomGlobal.lemma24_unconditional_of_geom (le_refl 2)
    (by have := hL 0; omega) (by have := hL 1; omega) (by have := hL 2; omega)
    hdvd B hB (geomInequality_of_admissible_ell2_uncond hL hdvd B hB)

#print axioms lemma24_unconditional_U1_ell2_uncond

end AdalyFormal.Balaban.HrefReduction
