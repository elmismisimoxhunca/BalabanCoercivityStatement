import AdalyFormal.Balaban.BackwardCert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

/-! # `FreeCellFrame` — the symbolic free-cell bond enumeration (piece (i) of `[RES-GEOM-REINDEX]`).

This module builds the **translation-invariant free-cell bond indexing** the backward per-block
positivity certificate needs: a symbolic-in-`L` map `freeCellBond : Fin 80 → Bond L` whose image is
exactly the 80 free (staircase-unpinned) bonds on which `BackwardCert.LocalGeomBackward 2 hdvd B z`
is supported, for the reference block `z = 0`, and its injectivity (a genuine indexing).

## What is characterized NUMERICALLY (CHARACTERIZE-FIRST, `compute/freecell_frame/`).

Independent, Lean-faithful re-derivation (`faithful_recheck.py`, NOT importing the cert's own
`characterize.py`), exact ℚ, `PYTHONHASHSEED=0`, dual-run byte-identical:

* **(i) Enumeration.** The support of `LocalGeomBackward 2 hdvd B 0` (minus the staircase-pinned
  bonds, which vanish on the admissible subspace) is EXACTLY 80 bonds, matching the certificate's
  `free_coord_to_bond` map (`compute/backward_cert/cert_backward.json`) set-for-set.  Every site
  coordinate of every free bond is one of `{0, 1, 2, L μ - 1, L μ}` — hence symbolic in `L` (values
  `4, 5` on the `N = 6` sample are `L μ - 1, L μ`; value `3` never occurs).  The `L μ - 1, L μ`
  coordinates are the wrapped **previous block** `prevμ 0` that `LocalGeomBackward` credits to block
  `0`.
* **(ii) Matrix-faithfulness (numeric).**  On 200 random admissible `B`,
  `LocalGeomBackward 2 hdvd B 0 = ∑_{a,b} T a b · B(bond_a) · B(bond_b)` EXACTLY (0 mismatches),
  with `T` the certificate Gram; non-vacuous (200/200 nonzero); no negative value.  Matrix residual
  `max |LocalGeomBackward₀(free) − T| = 0`; off-support (non-pinned) `= 0`.  Mutation controls
  (double a `d_k`, drop a square, flip the top-face sign in the Lean form) each drive the residual
  off zero — the check is non-vacuous (OPS-3).
* **(iii) `T ⪰ 0`.**  `T = ∑_{k<56} d_k v_k v_kᵀ`, exact reconstruction residual 0, PSD rank 56,
  min LDLᵀ pivot `35/627 > 0`.
* **(iv) Transport.**  For EVERY coarse block `z` (origin, interior, torus-wrap tested),
  `LocalGeomBackward 2 hdvd B z` restricted to its `z`-shifted free coordinates equals the SAME `T`,
  residual 0 — translation-invariance, so transport of the reference-block positivity is valid.

So the target is confirmed real: the **Lean** `LocalGeomBackward` matches the certificate `T`
exactly (the task's "does the Lean per-block energy equal `T`?" — answer: YES, residual 0).

## What is PROVED here (no `sorry`, axiom-clean).

* `coordFin` / `coordFin_injective` — the symbolic coordinate map `Fin 5 → Fin (L μ + 1)` sending
  codes `0,1,2,3,4` to `0,1,2,L μ - 1,L μ`, injective when `4 ≤ L μ`.
* `freeCode` / `freeCode_injective` — the 80-entry code table (`codeList`, `Nodup` by `decide`).
* `freeCellBond` / `freeCellBond_injective` — the free-cell bond enumeration and its injectivity
  (a genuine indexing) for any `L` with `4 ≤ L μ` on every axis.

## The remaining obligations to discharge `GeomGlobal.geomInequality_of_admissible_ell2` (NAMED).

This module supplies piece (i).  A kernel discharge of `∀ z, 0 ≤ LocalGeomBackward 2 hdvd B z`
(which `BackwardCert.geomInequality_of_backwardBlockNonneg` reduces the residual to) still needs:

* **(ii-Lean) matrix-faithfulness identity** `LocalGeomBackward 2 hdvd B 0
  = ∑_{a,b} T a b · B(freeCellBond … a) · B(freeCellBond … b)` on admissible `B` — the symbolic
  evaluation of the four `Finset.univ.filter` energies (`lineCoarseRestrict`/`slabPlaqs`/
  `topFaceEnergy`/`bondsInBlock`) into the 80 free-cell coordinates.  The load-bearing obstruction:
  `LocalGeomBackward` credits block `0` the content of the coarse bonds at `prevμ 0 =
  (coarseShiftEquiv 2 μ hdvd).symm 0`, a `Classical.choice`-opaque `Equiv` inverse; pinning it to
  the explicit site `Function.update 0 μ ⟨L μ - 1, _⟩` needs `(coarseShiftEquiv …).symm 0 = ⟨…⟩` via
  `Equiv.symm_apply_eq` + `coarseShift ⟨…⟩ 2 μ = 0` (the `(L μ - 1) + 2 ≡ 0` wrap).  Numerically
  residual 0 (above); the symbolic `Finset`-`ext` evaluations are the multi-hundred-line body.
* **(iii-Lean) `T ⪰ 0`** via `RatSOSEval.quadForm_nonneg_of_intGram` fed the 56 integer-scaled
  squares — blocked only on the `∀ a b, gram sqsI a b = T a b` kernel wiring
  (`[RES-CERT-KERNEL-REFLECT]`, MEASURED feasible, `compute/rat_sos_eval/FEASIBILITY.md`).
* **(iv-Lean) transport** of the reference-block identity to every `z` via
  `CoarseShiftCovariance` (numerically confirmed translation-invariant above). -/

namespace FreeCellFrame

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace

variable {L : PeriodicLatticeExtent}

/-! ## §1. The symbolic coordinate map `Fin 5 → Fin (L μ + 1)`. -/

/-- The five symbolic coordinate values a free-cell bond's site can take on axis `μ`:
codes `0,1,2,3,4` ↦ `0,1,2, L μ - 1, L μ`.  (`3, 4` are the wrapped previous-block coordinates.) -/
def coordNat (L : PeriodicLatticeExtent) (μ : Fin 3) (code : Fin 5) : ℕ :=
  ![0, 1, 2, L μ - 1, L μ] code

theorem coordNat_lt (μ : Fin 3) (hμ : 4 ≤ L μ) (code : Fin 5) : coordNat L μ code < L μ + 1 := by
  fin_cases code <;> simp [coordNat] <;> omega

/-- The symbolic coordinate value as a genuine `Fin (L μ + 1)` element (needs `4 ≤ L μ` so the five
values are in range). -/
def coordFin (L : PeriodicLatticeExtent) (μ : Fin 3) (hμ : 4 ≤ L μ) (code : Fin 5) :
    Fin (L μ + 1) :=
  ⟨coordNat L μ code, coordNat_lt μ hμ code⟩

/-- The five coordinate values are DISTINCT when `4 ≤ L μ` — hence `coordFin` is injective. -/
theorem coordFin_injective (μ : Fin 3) (hμ : 4 ≤ L μ) :
    Function.Injective (coordFin L μ hμ) := by
  intro a b hab
  have hval : coordNat L μ a = coordNat L μ b := congrArg Fin.val hab
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (exfalso; simp [coordNat] at hval <;> omega)

/-! ## §2. The 80-entry code table and `freeCode`. -/

/-- The 80 free-cell bonds as `(axis-0 code, axis-1 code, axis-2 code, direction)`, extracted from
`compute/backward_cert/cert_backward.json` (`free_coord_to_bond`, coordinate values recoded
`0,1,2,4,5 ↦ 0,1,2,3,4`). -/
def codeList : List (Fin 5 × Fin 5 × Fin 5 × Fin 3) := [
    (0, 0, 1, 2), (0, 0, 4, 2), (0, 1, 0, 1), (0, 1, 0, 2),
    (0, 1, 1, 1), (0, 1, 1, 2), (0, 1, 3, 1), (0, 1, 3, 2),
    (0, 1, 4, 1), (0, 1, 4, 2), (0, 2, 4, 2), (0, 3, 1, 2),
    (0, 4, 0, 1), (0, 4, 0, 2), (0, 4, 1, 1), (0, 4, 1, 2),
    (0, 4, 2, 1), (1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 0, 2),
    (1, 0, 1, 0), (1, 0, 1, 1), (1, 0, 1, 2), (1, 0, 3, 0),
    (1, 0, 3, 1), (1, 0, 3, 2), (1, 0, 4, 0), (1, 0, 4, 1),
    (1, 0, 4, 2), (1, 1, 0, 0), (1, 1, 0, 1), (1, 1, 0, 2),
    (1, 1, 3, 0), (1, 1, 3, 1), (1, 1, 3, 2), (1, 1, 4, 0),
    (1, 1, 4, 1), (1, 1, 4, 2), (1, 2, 3, 2), (1, 2, 4, 2),
    (1, 3, 0, 0), (1, 3, 0, 1), (1, 3, 0, 2), (1, 3, 1, 0),
    (1, 3, 1, 1), (1, 3, 1, 2), (1, 3, 2, 1), (1, 4, 0, 0),
    (1, 4, 0, 1), (1, 4, 0, 2), (1, 4, 1, 0), (1, 4, 1, 1),
    (1, 4, 1, 2), (1, 4, 2, 1), (2, 0, 4, 2), (2, 1, 3, 2),
    (2, 1, 4, 2), (2, 4, 0, 1), (2, 4, 1, 1), (3, 0, 1, 2),
    (3, 1, 0, 1), (3, 1, 0, 2), (3, 1, 1, 1), (3, 1, 1, 2),
    (4, 0, 0, 0), (4, 0, 0, 1), (4, 0, 0, 2), (4, 0, 1, 0),
    (4, 0, 1, 1), (4, 0, 1, 2), (4, 0, 2, 0), (4, 1, 0, 0),
    (4, 1, 0, 1), (4, 1, 0, 2), (4, 1, 1, 0), (4, 1, 1, 1),
    (4, 1, 1, 2), (4, 1, 2, 0), (4, 2, 0, 0), (4, 2, 1, 0),
]

theorem codeList_length : codeList.length = 80 := by rfl

theorem codeList_nodup : codeList.Nodup := by decide

/-- The code 4-tuple of free-cell coordinate `i`. -/
def freeCode (i : Fin 80) : Fin 5 × Fin 5 × Fin 5 × Fin 3 :=
  codeList.get (Fin.cast codeList_length.symm i)

theorem freeCode_injective : Function.Injective freeCode := by
  intro i j h
  have hg : codeList.get (Fin.cast codeList_length.symm i)
      = codeList.get (Fin.cast codeList_length.symm j) := h
  have hcast := (List.nodup_iff_injective_get.mp codeList_nodup) hg
  have : i.val = j.val := by
    have := congrArg Fin.val hcast
    simpa using this
  exact Fin.ext this

/-! ## §3. The free-cell bond enumeration and its injectivity. -/

/-- The axis-`μ` code of a code 4-tuple (as a `Fin 3 → Fin 5` vector, so it reduces cleanly). -/
def axisCode (t : Fin 5 × Fin 5 × Fin 5 × Fin 3) : Fin 3 → Fin 5 :=
  ![t.1, t.2.1, t.2.2.1]

/-- The reference-block (`z = 0`) site of free-cell coordinate `i`, symbolic in `L`. -/
def refSite (L : PeriodicLatticeExtent) (hL : ∀ μ, 4 ≤ L μ) (i : Fin 80) :
    PeriodicLatticeSite L :=
  fun μ => coordFin L μ (hL μ) (axisCode (freeCode i) μ)

/-- The direction of free-cell coordinate `i`. -/
def freeDir (i : Fin 80) : Fin 3 := (freeCode i).2.2.2

/-- **The free-cell bond enumeration** `Fin 80 → Bond L` (reference block `z = 0`), symbolic in
`L`. -/
def freeCellBond (L : PeriodicLatticeExtent) (hL : ∀ μ, 4 ≤ L μ) (i : Fin 80) : Bond L :=
  (refSite L hL i, freeDir i)

/-- **A GENUINE INDEXING (PROVED, no `sorry`).** The free-cell bond enumeration is injective for any
`L` with `4 ≤ L μ` on every axis. -/
theorem freeCellBond_injective (hL : ∀ μ, 4 ≤ L μ) :
    Function.Injective (freeCellBond L hL) := by
  intro i j h
  simp only [freeCellBond, Prod.mk.injEq] at h
  obtain ⟨hs, hd⟩ := h
  -- codes agree on all three axes (from the site equality via coordFin injectivity)
  have hc : ∀ μ, axisCode (freeCode i) μ = axisCode (freeCode j) μ := by
    intro μ
    exact coordFin_injective μ (hL μ) (congrFun hs μ)
  have h0 : (freeCode i).1 = (freeCode j).1 := by simpa [axisCode] using hc 0
  have h1 : (freeCode i).2.1 = (freeCode j).2.1 := by simpa [axisCode] using hc 1
  have h2 : (freeCode i).2.2.1 = (freeCode j).2.2.1 := by simpa [axisCode] using hc 2
  have hd' : (freeCode i).2.2.2 = (freeCode j).2.2.2 := hd
  apply freeCode_injective
  exact Prod.ext_iff.mpr ⟨h0, Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h2, hd'⟩⟩⟩

#print axioms freeCellBond_injective

end FreeCellFrame
