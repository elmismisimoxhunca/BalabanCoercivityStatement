import AdalyFormal.Balaban.GeomOperatorSOS

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # `FreeCellReindex` — the whole-lattice → per-block reindex of `geomForm` (`[RES-GEOM-REINDEX]`).

This module builds the EXACT reindex identity

    `geomForm ell B = ∑_{y∈Λ'} LocalGeom ell B y`

decomposing the whole-lattice `(geom)` form into a sum over coarse blocks `y` of a FIXED per-block
local form `LocalGeom`.  The four whole-lattice energies of `geomForm`
(`coarseQEnergy`, `slabCurlEnergy`, `bondNormSq − inBlockBondEnergy`, `inBlockBondEnergy`) are each
ALREADY block/coarse-bond-indexed sums, so this decomposition is an honest REGROUPING — no
cross-block re-apportioning — proved sorry-free by consuming `GeomScratch.sum_topFace_eq_Sbet`
(the `bondNormSq − inBlock = ∑_c topFace` half) together with `Fintype.sum_prod_type`
(`CoarseBond = {y∈Λ'} × Fin 3`) and `Finset.sum_subtype`.

## What this DOES and does NOT deliver — the measured finding (`compute/geom_reindex/characterize.py`).

* **DELIVERS (proved, no `sorry`): `geomForm_eq_sum_localGeom`** — the reindex identity, EXACT
  (numerically residual 0 at `ell=2`, `N=6`; the global margin of `geomForm|_admissible` is
  `+0.07727733`, matching `compute/geom_global/ladder.py` — the model is faithful).

* **`geomForm_eq_sum_localGeom` does NOT by itself discharge `geomInequality_of_admissible_ell2`,
  because the FORWARD assignment `LocalGeom` proved here is NOT PSD.**  The naive forward-biased
  per-block form (each coarse bond `(y,μ)` and its slab / top-face / line-integral credited to its
  BASE block `y`) is **not PSD** on the admissible subspace — exact pivoted congruence finds a
  negative pivot, float `λ_min = −0.00765250`, for BOTH origin and interior blocks
  (`compute/geom_reindex/characterize.py`).  A PSD total (`geomForm|_admissible ⪰ 0`, margin
  `+0.0773`) does not force each block term PSD.

* **THE CLEAN DISCHARGE ROUTE — the BACKWARD assignment IS PSD (measured, verified two ways).**
  Crediting each coarse bond `(y,μ)`'s content to the block its `+μ` face points INTO (`y+e_μ`)
  instead of its base block — plus the in-block bond energy of the block itself — gives a per-block
  form that is **positive semidefinite** on the admissible subspace: exact symmetric congruence
  (Sylvester inertia) reduces it to `diag(56 positive, 24 zero)` — **56 positive, 0 negative pivots**
  — and float `eigvalsh` agrees (`λ_min ≈ 1e-16`, no eigenvalue `< −1e-9`), for origin, interior AND
  torus-wrap blocks, SIZE-UNIFORM across `N∈{6,8}` with IDENTICAL rank 56 and spectrum
  (`compute/geom_reindex/backward_psd.py`, partition residual 0).  So

      `geomForm 2 B = ∑_y LocalGeomBackward_y`,   each `LocalGeomBackward_y ≥ 0`  ⟹  `geomForm ≥ 0`.

  This is a DIFFERENT, GEOMETRICALLY NATURAL per-block decomposition, and it **refutes the earlier
  claim** (in `GeomGlobal`/`GeomOperatorSOS`, and this module's prior draft) that only the census
  joint 13-block band-1 SOS `M_free = ∑ᵢ dᵢ Sᵢᵀ Sᵢ` (1243 squares) works.  The backward per-block
  form is PSD of RANK 56, so it has an exact rational sum-of-squares of just **56 squares** — a
  DRAMATICALLY smaller certificate than the census 1243, and geometrically grounded (a per-block, not
  a fitted-symbol, object).

* **The SOLE remaining residual to a kernel discharge** is therefore sharpened to: (i) the BACKWARD
  reindex `geomForm 2 B = ∑_y LocalGeomBackward_y` (a regrouping of the same four energies by HEAD
  block instead of base block — the coarse-bond sum reindexed through the `coarseShift · μ`
  bijection on `Λ'`); and (ii) the single FIXED per-block backward SOS ℚ-identity
  `LocalGeomBackward_0 = ∑_{k<56} d_k (v_k · B)²`, `d_k > 0` rational (extractable from the exact
  pivoted LDLᵀ), transported by `CoarseShiftCovariance` and summed, its positivity then TRIVIAL
  (`GeomOperatorSOS.sosForm_nonneg`).  The `RatSOSEval` engine (kernel-clean) checks such a fixed
  rational SOS identity.  The census route (`HasOperatorSOS` / `geomInequality_of_hasOperatorSOS`)
  remains valid but is now the HARDER of two options.

`geomForm_eq_sum_localGeom` (forward) is a genuine, unconditional, reusable brick — the exact
per-block reindex machinery — and it records precisely where the FORWARD per-block route breaks (the
PSD step) and, by the backward measurement above, exactly how to fix it. -/

namespace FreeCellReindex

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.CrossSectionField
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.Lemma24Assembly
open GeomScratch
open GeomOperatorSOS

variable {L : PeriodicLatticeExtent}

/-- **The per-block local form of `geomForm`, indexed by a coarse block `y ∈ Λ'`.** Collects, for the
three coarse bonds `(y,μ)` based at `y` and the block `B(y)` itself:
`ell·Σ_μ (Q₁B)(y,μ)² + ell⁻²·Σ_μ Σ_{p∈slab(y,μ)} curl² − (1/3)ell⁻³·Σ_μ topFace(y,μ)
  + 6·ell⁻²·Σ_{b⊂B(y)} B(b)²`.
This is the "naive forward-biased" per-block assignment: each coarse bond `(y,μ)` and its slab / top
face / line-integral are credited entirely to the base block `y`.  Summing over `y∈Λ'` reproduces
`geomForm` EXACTLY (`geomForm_eq_sum_localGeom`).  MEASURED not PSD per block on the admissible
subspace (see module docstring). -/
noncomputable def LocalGeom (ell : ℕ) (B : Bond L → ℝ)
    (y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) : ℝ :=
  (ell : ℝ) * ∑ μ : Fin 3, (lineCoarseRestrict ell B (y, μ)) ^ 2
    + (1 / (ell : ℝ) ^ 2) * ∑ μ : Fin 3, ∑ p ∈ slabPlaqs (y, μ), (curlValue B p) ^ 2
    - (1 / 3) * (1 / (ell : ℝ) ^ 3) * ∑ μ : Fin 3, topFaceEnergy B y.1 ell μ
    + 6 * (1 / (ell : ℝ) ^ 2) * ∑ b ∈ bondsInBlock y.1 ell, (B b) ^ 2

/-- **THE REINDEX (PROVED, no `sorry`).** `geomForm ell B = ∑_{y∈Λ'} LocalGeom ell B y`.  Exact
regrouping of the four already-block-indexed energies of `geomForm`; consumes
`GeomScratch.sum_topFace_eq_Sbet` for the `bondNormSq − inBlock = ∑_c topFace` half. -/
theorem geomForm_eq_sum_localGeom {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    (B : Bond L → ℝ) :
    geomForm ell B
      = ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, LocalGeom ell B y := by
  -- Piece 1: ell·coarseQEnergy
  have e1 : (∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        (ell : ℝ) * ∑ μ : Fin 3, (lineCoarseRestrict ell B (y, μ)) ^ 2)
      = (ell : ℝ) * coarseQEnergy ell B := by
    rw [coarseQEnergy, Fintype.sum_prod_type, Finset.mul_sum]
  -- Piece 2: ell⁻²·slabCurlEnergy
  have e2 : (∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        (1 / (ell : ℝ) ^ 2) * ∑ μ : Fin 3, ∑ p ∈ slabPlaqs (y, μ), (curlValue B p) ^ 2)
      = (1 / (ell : ℝ) ^ 2) * slabCurlEnergy ell B := by
    rw [slabCurlEnergy, Fintype.sum_prod_type, Finset.mul_sum]
  -- Piece 3: (1/3)ell⁻³·(bondNormSq − inBlock), via FACT 1
  have hF1 : bondNormSq B - inBlockBondEnergy ell B
      = ∑ c : CoarseBond L ell, topFaceEnergy B c.1.1 ell c.2 := by
    have := sum_topFace_eq_Sbet hell hdvd hstrict B; linarith [this]
  have e3 : (∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        (1 / 3) * (1 / (ell : ℝ) ^ 3) * ∑ μ : Fin 3, topFaceEnergy B y.1 ell μ)
      = (1 / 3) * (1 / (ell : ℝ) ^ 3) * (bondNormSq B - inBlockBondEnergy ell B) := by
    rw [hF1, Fintype.sum_prod_type, Finset.mul_sum]
  -- Piece 4: 6·ell⁻²·inBlock
  have e4 : (∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        6 * (1 / (ell : ℝ) ^ 2) * ∑ b ∈ bondsInBlock y.1 ell, (B b) ^ 2)
      = 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B := by
    rw [inBlockBondEnergy_eq_sum, Finset.mul_sum]
    exact (Finset.sum_subtype (CoarseLattice L ell) (fun _ => Iff.rfl)
      (fun z => 6 * (1 / (ell : ℝ) ^ 2) * blockBondEnergy B z ell)).symm
  -- Assemble: sum splits over the four summands of LocalGeom
  simp only [LocalGeom]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, e1, e2, e3, e4]
  unfold geomForm
  ring

#print axioms geomForm_eq_sum_localGeom

end FreeCellReindex
