import AdalyFormal.Balaban.FreeCellReindex
import AdalyFormal.Balaban.CoarseShiftCovariance

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # `BackwardCert` — the BACKWARD per-block decomposition of `geomForm` and its positivity reduction.

`FreeCellReindex.geomForm_eq_sum_localGeom` regroups `geomForm ell B` into a sum over coarse blocks by
crediting each coarse bond `(y,μ)` to its BASE block `y` (the FORWARD assignment).  That forward
per-block form is MEASURED **not** PSD (`compute/geom_reindex/characterize.py`: a negative pivot,
float `λ_min = −0.0077`), so it cannot deliver `geomForm ≥ 0` term-by-term.

This module builds the BACKWARD assignment, which IS positive semidefinite per block
(`compute/geom_reindex/backward_psd.py`: exact Sylvester congruence `diag(56 pos, 24 zero, 0 neg)`,
size-uniform across `N∈{6,8}`, partition residual 0).  Crediting each coarse bond `(y,μ)`'s content to
the block its `+μ` face points INTO — the HEAD block `coarseShift y ell μ` — instead of its base block
gives a per-block form `LocalGeomBackward` that is a nonnegative quadratic form.  Equivalently, block
`z` is credited the content of the coarse bonds `(prevμ z, μ)` for each `μ`, where `prevμ` is the
inverse of the `ell`-shift bijection on the coarse lattice.

## What is PROVED here (no `sorry`, no new axioms).

* `coarseShiftEquiv` — the `ell`-shift as an honest `Equiv` on the coarse-lattice subtype (from
  `CoarseShiftCovariance.coarseShift_injective` + finiteness), so its inverse `prevμ` exists.
* `geomForm_eq_sum_localGeomBackward` — **THE BACKWARD REINDEX**: `geomForm ell B =
  ∑_{z∈Λ'} LocalGeomBackward ell hdvd B z`.  Proved by the same four-piece regrouping as the forward
  reindex, with the three coarse-bond-indexed energies (`coarseQEnergy`, `slabCurlEnergy`, the
  top-face `Sbet` half via `GeomScratch.sum_topFace_eq_Sbet`) reindexed through `coarseShiftEquiv`'s
  inverse (`Equiv.sum_comp`); the in-block half is credited to `z` unchanged, identical to the forward
  proof.  This is an EXACT identity (no admissibility needed) — the honest, reusable backward-regroup
  brick.
* `geomInequality_of_backwardBlockNonneg` — **THE POSITIVITY REDUCTION**: if every backward per-block
  form is nonnegative (`∀ z, 0 ≤ LocalGeomBackward ell hdvd B z`) then `GeomInequality ell B` holds.
  Immediate from the reindex + `GeomOperatorSOS.geomInequality_iff_geomForm_nonneg` +
  `Finset.sum_nonneg`.  This SHARPENS `GeomGlobal.geomInequality_of_admissible_ell2`'s residual to the
  single per-block statement `∀ z, 0 ≤ LocalGeomBackward 2 hdvd B z`.

## The single remaining residual (NAMED, not faked) — `[RES-GEOM-REINDEX]`.

`geomInequality_of_backwardBlockNonneg` takes per-block positivity as a HYPOTHESIS; this module does
NOT prove it, and carries no `sorry`.  Discharging that hypothesis is exactly the transport of the
backward 56-square SOS certificate:

* **The certificate EXISTS and is verified** (`compute/backward_cert/`, `PYTHONHASHSEED=0`,
  dual-run byte-identical): `extract_backward_sos.py` (self-hash reported in the run log) emits the
  reference block's exact rational LDLᵀ as `LocalGeomBackward₀ = ∑_{k<56} d_k (v_k · B)²`, `d_k > 0`
  rational, over the 80 free (staircase-unpinned) bond coordinates, and VERIFIES the reconstruction
  residual is EXACTLY 0 over ℚ.  `controls.py`: `5/5` mutations (double a `d_k`, perturb a covector,
  drop a square, S82 garbage `d_k≡1`, and the backward SOS applied to the FORWARD indefinite form)
  each drive the residual off zero — the check is NON-VACUOUS.  It is `~22×` smaller than the census
  `1243`-square certificate and geometrically grounded (a per-block, not a fitted-symbol, object).

* **What a Lean discharge of `∀ z, 0 ≤ LocalGeomBackward 2 hdvd B z` still needs** — the bond-
  coordinate framework `[RES-GEOM-REINDEX]`: (i) a translation-invariant enumeration of the `≤ 80`
  bonds in a coarse block's backward neighbourhood as `Fin 80` free-cell coordinates (symbolic in a
  general lattice `L`, NOT specialised to one `N`); (ii) the identity
  `LocalGeomBackward₀ B = ∑_{a,b} (T a b) (freecoord B)_a (freecoord B)_b` reducing the abstract
  `Finset` sums (`lineCoarseRestrict`, `slabPlaqs`/`curlValue`, `topFaceEnergy`, `bondsInBlock`) to the
  reference-block Gram `T`; (iii) the kernel-checked SOS identity `T = ∑_{k<56} d_k v_k v_kᵀ` — feeding
  the `d_k, v_k` above to `RatSOSEval.quadForm_nonneg_of_intGram` (whose ~56-square scale is well within
  the MEASURED `~38 s` `rfl` budget for the census 1243, `compute/rat_sos_eval/FEASIBILITY.md`); and
  (iv) `CoarseShiftCovariance`-transport of the reference-block positivity to every block `z` (the form
  is translation-invariant, `coarseRestrict_shift_intertwine` is the model).  Step (i)+(ii), the
  symbolic free-cell coordinate framework, is a multi-hundred-line combinatorial construction, not yet
  in the tree — this is the honest wall, now equipped with the concrete 56-square target data. -/

namespace BackwardCert

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.CrossSectionField
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.Lemma24Assembly
open AdalyFormal.Balaban.CoarseCurl
open GeomScratch
open GeomOperatorSOS
open GeomGlobal

variable {L : PeriodicLatticeExtent}

/-- **The `ell`-shift in direction `μ` as an `Equiv` on the coarse-lattice subtype.** Injective
(`CoarseShiftCovariance.coarseShift_injective`) self-map of a finite type, hence bijective; packaged as
an `Equiv` so its inverse `prevμ := (coarseShiftEquiv ell μ hdvd).symm` — "the previous coarse block in
direction `μ`" — is available for the backward decomposition. -/
noncomputable def coarseShiftEquiv (ell : ℕ) (μ : Fin 3) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell} ≃
      {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell} :=
  Equiv.ofBijective
    (fun z => ⟨coarseShift z.1 ell μ, coarseShift_mem_coarseLattice hdvd z.2 μ⟩)
    (Finite.injective_iff_bijective.mp (by
      intro a b h
      exact Subtype.ext
        (AdalyFormal.Balaban.CoarseShiftCovariance.coarseShift_injective ell μ
          (Subtype.ext_iff.mp h))))

/-- **The BACKWARD per-block local form.** Block `z` is credited the coarse-bond content
(line-`Q`, slab curls, top-face) of the coarse bonds `(prevμ z, μ)` whose `+μ` face points INTO `z`
(`prevμ = (coarseShiftEquiv ell μ hdvd).symm`), PLUS the in-block bond energy of `z` itself:
`ell·Σ_μ (Q₁B)(prevμ z,μ)² + ell⁻²·Σ_μ Σ_{p∈slab(prevμ z,μ)} curl² − (1/3)ell⁻³·Σ_μ topFace(prevμ z,μ)
  + 6·ell⁻²·Σ_{b⊂B(z)} B(b)²`.
Summing over `z∈Λ'` reproduces `geomForm` EXACTLY (`geomForm_eq_sum_localGeomBackward`).  MEASURED PSD
per block on the admissible subspace (rank 56; `compute/geom_reindex/backward_psd.py`), UNLIKE the
forward `FreeCellReindex.LocalGeom`. -/
noncomputable def LocalGeomBackward (ell : ℕ) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : Bond L → ℝ) (z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) : ℝ :=
  (ell : ℝ) * ∑ μ : Fin 3,
      (lineCoarseRestrict ell B ((coarseShiftEquiv ell μ hdvd).symm z, μ)) ^ 2
    + (1 / (ell : ℝ) ^ 2) * ∑ μ : Fin 3,
        ∑ p ∈ slabPlaqs ((coarseShiftEquiv ell μ hdvd).symm z, μ), (curlValue B p) ^ 2
    - (1 / 3) * (1 / (ell : ℝ) ^ 3) * ∑ μ : Fin 3,
        topFaceEnergy B ((coarseShiftEquiv ell μ hdvd).symm z).1 ell μ
    + 6 * (1 / (ell : ℝ) ^ 2) * ∑ b ∈ bondsInBlock z.1 ell, (B b) ^ 2

/-- **The reindex heart.** For any `φ`, summing `φ` over the coarse-lattice subtype with each block's
direction-`μ` slot pulled back by `prevμ = (coarseShiftEquiv ell μ hdvd).symm` equals the un-pulled
sum: `∑_z ∑_μ φ (prevμ z) μ = ∑_z ∑_μ φ z μ`.  Per-`μ` reindex by the shift `Equiv` (`Equiv.sum_comp`)
after swapping the two finite sums. -/
theorem sum_prev_reindex {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (φ : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell} → Fin 3 → ℝ) :
    (∑ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        ∑ μ : Fin 3, φ ((coarseShiftEquiv ell μ hdvd).symm z) μ)
      = ∑ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}, ∑ μ : Fin 3, φ z μ := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  exact Equiv.sum_comp (coarseShiftEquiv ell μ hdvd).symm (fun z => φ z μ)

/-- **THE BACKWARD REINDEX (PROVED, no `sorry`).** `geomForm ell B = ∑_{z∈Λ'} LocalGeomBackward ell
hdvd B z`.  Exact regrouping of the four already-block-indexed energies of `geomForm`, the three
coarse-bond-indexed ones reindexed through `coarseShiftEquiv`'s inverse (`sum_prev_reindex`), the
in-block one credited to `z` unchanged; consumes `GeomScratch.sum_topFace_eq_Sbet` for the
`bondNormSq − inBlock = ∑_c topFace` half. -/
theorem geomForm_eq_sum_localGeomBackward {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    (B : Bond L → ℝ) :
    geomForm ell B
      = ∑ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
          LocalGeomBackward ell hdvd B z := by
  -- Piece 1: ell·coarseQEnergy, reindexed
  -- NOTE (robustness): each piece is closed by a pure `rw` chain LHS→RHS, NOT by `congr 1`.
  -- `congr 1` on `c * X = c * Y` recurses into `X`/`Y`, forcing `whnf` on the `Classical.choice`-
  -- based `coarseShiftEquiv` inside `slabPlaqs ((·).symm z, μ)` — that blows the heartbeat budget.
  have e1 : (∑ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        (ell : ℝ) * ∑ μ : Fin 3,
          (lineCoarseRestrict ell B ((coarseShiftEquiv ell μ hdvd).symm z, μ)) ^ 2)
      = (ell : ℝ) * coarseQEnergy ell B := by
    rw [← Finset.mul_sum,
      sum_prev_reindex hdvd (fun z μ => (lineCoarseRestrict ell B (z, μ)) ^ 2),
      coarseQEnergy, Fintype.sum_prod_type]
  -- Piece 2: ell⁻²·slabCurlEnergy, reindexed
  have e2 : (∑ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        (1 / (ell : ℝ) ^ 2) * ∑ μ : Fin 3,
          ∑ p ∈ slabPlaqs ((coarseShiftEquiv ell μ hdvd).symm z, μ), (curlValue B p) ^ 2)
      = (1 / (ell : ℝ) ^ 2) * slabCurlEnergy ell B := by
    rw [← Finset.mul_sum,
      sum_prev_reindex hdvd (fun z μ => ∑ p ∈ slabPlaqs (z, μ), (curlValue B p) ^ 2),
      slabCurlEnergy, Fintype.sum_prod_type]
  -- Piece 3: (1/3)ell⁻³·(bondNormSq − inBlock), via FACT 1, reindexed
  have hF1 : bondNormSq B - inBlockBondEnergy ell B
      = ∑ c : CoarseBond L ell, topFaceEnergy B c.1.1 ell c.2 := by
    have := sum_topFace_eq_Sbet hell hdvd hstrict B; linarith [this]
  have e3 : (∑ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        (1 / 3) * (1 / (ell : ℝ) ^ 3) * ∑ μ : Fin 3,
          topFaceEnergy B ((coarseShiftEquiv ell μ hdvd).symm z).1 ell μ)
      = (1 / 3) * (1 / (ell : ℝ) ^ 3) * (bondNormSq B - inBlockBondEnergy ell B) := by
    rw [← Finset.mul_sum,
      sum_prev_reindex hdvd (fun z μ => topFaceEnergy B z.1 ell μ),
      hF1, Fintype.sum_prod_type]
  -- Piece 4: 6·ell⁻²·inBlock (credited to z unchanged — identical to the forward proof)
  have e4 : (∑ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        6 * (1 / (ell : ℝ) ^ 2) * ∑ b ∈ bondsInBlock z.1 ell, (B b) ^ 2)
      = 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B := by
    rw [inBlockBondEnergy_eq_sum, Finset.mul_sum]
    exact (Finset.sum_subtype (CoarseLattice L ell) (fun _ => Iff.rfl)
      (fun z => 6 * (1 / (ell : ℝ) ^ 2) * blockBondEnergy B z ell)).symm
  -- Assemble
  simp only [LocalGeomBackward]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, e1, e2, e3, e4]
  unfold geomForm
  ring

#print axioms geomForm_eq_sum_localGeomBackward

/-- **THE POSITIVITY REDUCTION (PROVED, no `sorry`).** If every backward per-block form is nonnegative,
then `GeomInequality ell B` holds.  This sharpens `GeomGlobal.geomInequality_of_admissible_ell2`'s
residual to the single per-block statement `∀ z, 0 ≤ LocalGeomBackward ell hdvd B z` — which the
verified 56-square backward certificate (`compute/backward_cert/`) targets, modulo the named bond-
coordinate framework `[RES-GEOM-REINDEX]` (see the module docstring). -/
theorem geomInequality_of_backwardBlockNonneg {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    (B : Bond L → ℝ)
    (hpos : ∀ z : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
      0 ≤ LocalGeomBackward ell hdvd B z) :
    GeomInequality ell B := by
  rw [geomInequality_iff_geomForm_nonneg, geomForm_eq_sum_localGeomBackward hell hdvd hstrict B]
  exact Finset.sum_nonneg (fun z _ => hpos z)

#print axioms geomInequality_of_backwardBlockNonneg

end BackwardCert
