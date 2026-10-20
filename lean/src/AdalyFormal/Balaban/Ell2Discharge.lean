import AdalyFormal.Balaban.BackwardCert
import AdalyFormal.Balaban.BackwardTCert

set_option autoImplicit false
set_option maxHeartbeats 400000

/-! # `Ell2Discharge` — the FINAL composition brick for the `ell = 2` U=1 `(geom)` residual.

This module assembles the whole backward-route chain into ONE reduction that discharges
`GeomGlobal.geomInequality_of_admissible_ell2`'s positivity content down to a single PURE ALGEBRAIC
IDENTITY (no inequality left).  Every positivity fact on the path is a PROVED, axiom-clean brick:

* `BackwardCert.geomInequality_of_backwardBlockNonneg`  — `GeomInequality 2 B ⟵ ∀ z, 0 ≤ LocalGeomBackward 2 hdvd B z`.
* `BackwardTCert.backTSparse_nonneg`  — `0 ≤ sosQuadValue (backCertSparse.map castSparse) fc` (the genuine
  56-square T-cert, term-by-term `sq_nonneg`, gram-free, `W > 0`).

## What is PROVED here (no `sorry`, axiom-clean — `#print axioms` below).

`geomInequality_of_admissible_ell2_of_backwardReindex`: **from the per-block backward REINDEX IDENTITY
alone** — for every coarse block `z` there is a nonnegative constant `c` (morally `1/W`, `W` the
per-square integer scale of `backCertSparse`) and a free-cell coordinate assignment `fc : Fin 80 → ℝ`
(morally `freecoord B`) with

    `LocalGeomBackward 2 hdvd B z = c · sosQuadValue (backCertSparse.map castSparse) fc`

— the `(geom)` inequality `GeomInequality 2 B` follows.  Positivity is fully outsourced to the proved
`backTSparse_nonneg`; the ONLY remaining obligation `Hreindex` is a pure IDENTITY tying each per-block
energy to the concrete certificate's SOS value.  This SHARPENS the standing residual from "prove
`∀ z, 0 ≤ LocalGeomBackward`" (an inequality) to "prove `∀ z, LocalGeomBackward = c·(certificate SOS
value)`" (an equality), with the certificate and its positivity already in the kernel.

## HONEST SCOPE — what this does and does NOT close (§LEAN-D / no-success-lie).

This does **NOT** discharge `GeomGlobal.geomInequality_of_admissible_ell2`'s `sorry`.  It converts the
open positivity into the open identity `Hreindex`, which is exactly `[RES-GEOM-REINDEX]` piece (ii)
(the symbolic-`L` free-cell expansion of `lineCoarseRestrict`/`slabPlaqs`+`curlValue`/`topFaceEnergy`/
`bondsInBlock` on the admissible subspace) plus its transport to every block `z` (piece iv).  That
identity is a multi-hundred-line combinatorial construction over four nested `Finset`-sum energy
operators plus the staircase-gauge vanishing, NOT built — and no shift-intertwining lemma yet exists
for three of the four energies (only `CoarseShiftCovariance.coarseRestrict_shift_intertwine`, for
`coarseRestrict`).  So `Hreindex` is a HYPOTHESIS here, honestly named, not a proved fact.

**Statement-scope FINDING (routed to statement-prosecution, not silently fixed).**  The backward route
needs `hstrict : ∀ μ, 2 < L μ + 1` (via `GeomScratch.sum_topFace_eq_Sbet`, used inside
`geomForm_eq_sum_localGeomBackward`).  `GeomGlobal.geomInequality_of_admissible_ell2` as currently
stated takes ONLY `hdvd`, no `hstrict`; for a degenerate lattice (`L μ + 1 = 2`, one block per axis)
`hstrict` fails, so that exact signature is not dischargeable by this route.  This brick therefore
takes `hstrict` explicitly; adding `hstrict` to the `GeomGlobal` statement would be a hypothesis
STRENGTHENING and must be adjudicated, not done under cover of closing a `sorry`.

**ADJUDICATION (2026-07-25, source-pinned, IMAGE-verified).**  Bałaban CMP96 Lemma 2.4 (printed p.245,
eq (2.128); page image `compute/ell2_discharge/render/cmp96_p245-23.png`, PDF page 23, `page_offsets`
offset 222) is stated on the INFINITE lattice `Z^d` for an ARBITRARY sum of blocks `Λ = B(Λ')` with
`B = 0` outside `Λ` (compact support).  It carries NO per-axis block-count minimum and NO periodicity,
hence NO `hstrict` analogue: a `Λ` one block thick in a direction is covered (the neighbour blocks
`c₋ = y`, `c₊ = y + L eμ` are empty there, `B = 0`).  So `hstrict` is NOT a faithful transcription of a
Bałaban hypothesis — it is a TORUS-formalization artifact (the backward-reindex telescoping degenerates
when a direction has exactly one coarse block, `prevμ z = z`, `L μ + 1 = 2`).  **VERDICT: DO NOT narrow
`GeomGlobal.geomInequality_of_admissible_ell2`.**  The backward route genuinely does not cover the
`L μ + 1 = 2` torus corner; that `sorry` STAYS.  Full coverage needs a SEPARATE degenerate-direction
argument for that finite corner (or matching the formalization to Bałaban's `Z^d`/compact-support
setting, where the corner does not arise).  This brick remains an honest hstrict-CONDITIONAL reduction:
even a fully-proved `Hreindex` closes only the `hstrict`-conditional statement, NOT the `hdvd`-only
`GeomGlobal` signature. -/

namespace Ell2Discharge

open RatSOSEval
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open GeomGlobal
open BackwardCert

variable {L : PeriodicLatticeExtent}

/-- **THE FINAL COMPOSITION (PROVED, no `sorry`).**  From the per-block backward reindex identity
`Hreindex` — each per-block form equals a nonnegative multiple of the proved 56-square certificate's
SOS value — the `ell = 2` `(geom)` inequality `GeomInequality 2 B` follows.  Positivity is entirely
carried by the axiom-clean `BackwardTCert.backTSparse_nonneg`; the sole open content is the identity
`Hreindex` (`[RES-GEOM-REINDEX]` piece (ii)+(iv), NOT proved here — see the module docstring). -/
theorem geomInequality_of_admissible_ell2_of_backwardReindex
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (hstrict : ∀ μ : Fin 3, (2 : ℕ) < L μ + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L 2)
    (Hreindex : ∀ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 2},
        ∃ (c : ℝ) (fc : Fin 80 → ℝ), 0 ≤ c ∧
          LocalGeomBackward 2 hdvd B z
            = c * sosQuadValue (BackwardTCert.backCertSparse.map castSparse) fc) :
    GeomInequality 2 B := by
  apply geomInequality_of_backwardBlockNonneg (by norm_num) hdvd hstrict B
  intro z
  obtain ⟨c, fc, hc, hz⟩ := Hreindex z
  rw [hz]
  exact mul_nonneg hc (BackwardTCert.backTSparse_nonneg fc)

#print axioms geomInequality_of_admissible_ell2_of_backwardReindex

end Ell2Discharge
