/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantHjMinimizer
import AdalyFormal.Balaban.LineIntegralCovariant

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[FAITHFUL-COV-HJ]` — the covariant `H_j` machinery RE-BASED onto the FAITHFUL covariant `Q`

**Task.** `CovariantHjMinimizer.deltaJQuadFormCov` builds a genuinely `U`-dependent, curl-relative
covariant Schur complement `‖D_U H_j^{cov} B‖²`, but its interpolation/gauge constraint pins the
particular solution through the CONVICTED single-bond, `U`-independent restriction
`coarseRestrictCovariantLM L ell` (proved in `LineIntegralCovariant.lean` §2 to DROP the line
integral: it returns `(1/2)•v` on a constant field where the true block average returns `v`). This
module rebuilds the SAME machinery over the FAITHFUL covariant line-integral `Q`,
`LineIntegralCovariant.lineCoarseRestrictCovLM U ell` (grade-2 source-faithful: CMP95 (1.18)
block average of CMP98 p.28's per-bond path-dependent transport `R_{0,c₋}`, at the (125)
`η^{d+1}=1/ell⁴` normalization).

**The whole defect lives at ONE operator.** Grepping `CovariantHjMinimizer.lean`,
`coarseRestrictCovariantLM L ell` appears ONLY in the first gauge-constraint clause
(`gaugeConstraintSubspaceCov`, `IsBalabanExtensionCov.interpolates`, the `h1` hypothesis of
`hjExtensionCov_isBalabanExtensionCov`). Every other ingredient — `RcovLM` (the site projection,
built on the `U`-independent SITE average `coarseRestrictSiteCovariant`, UNCHANGED), the adjoint
`gradCovariantAdjointLM U`, the curl `curlCovariantLM U`, `deltaKernelImageCovH`, the closest-point
projection onto the curl image — is independent of the coarse BOND restriction and is reused
verbatim (LAW-19). So the re-basing is: replace `coarseRestrictCovariantLM L ell A' = 0/= B` by
`lineCoarseRestrictCovLM U ell A' = 0/= B` in the constraint, and re-thread the (unchanged)
correction/minimization chain over the new gauge-tangent subspace.

## What is proved here (all kernel-checked, `#print axioms` at each brick)

1. §1 `gaugeConstraintSubspaceCovFaithful` — the covariant gauge-tangent subspace with the FAITHFUL
   first clause `lineCoarseRestrictCovLM U ell A' = 0` (second clause `RcovLM (D_U^* A') = 0`
   unchanged).
2. §2 the correction/projection chain (`curlImageCovFaithful`, its `PlaqFnL2` transport, the bare
   closest-point projection `curlImageCovProjFaithful`, `hjCorrectionCovFaithful`,
   `hjExtensionCovFaithful`) — the exact analogues of `CovariantHjMinimizer.lean` §10–§12.
3. §3 `IsBalabanExtensionCovFaithful` + `hjExtensionCovFaithful_isBalabanExtensionCov`, whose
   `interpolates` clause and `h1` hypothesis now read `lineCoarseRestrictCovLM U ell A0 = B` — the
   FAITHFUL (1.18)-covariant interpolation constraint. Same honest hypothesis shape as
   `HjMinimizer`/`CovariantHjMinimizer` (a particular solution that already interpolates and is
    gauge-fixed); the harder existence-of-`A0` content is the SAME inherited residual, NOT
    discharged.
4. §4 `deltaJQuadFormCovFaithful` (STILL curl-relative: `covPlaqInner (D_U H) (D_U H) = ‖D_U H‖²`,
   NOT bare `‖v‖²` — the bare form is proved FALSE in `CovU1Reduction.lean`), `_nonneg`, and
   `_genuinely_U_dependent` (via faithful-`Q` injectivity at `ell=1`, transferring
   `dstarDQuadForm_genuinely_U_dependent`).
5. §5 the OPEN curl-relative coercivity TARGET, stated as a `def : Prop` (NOT proved, no `sorry`),
   carrying the compatibility hypothesis `0 < ell ∧ ∀ μ, ell ∣ L μ + 1` (the torus-artifact lesson:
   on incompatible extents the faithful block truncates and any coercivity constant degrades).

## Honesty / scope

* **This is an ISLAND.** Nothing here is wired to `coerc_u_main` or to any consumed spine
  declaration; the general-`U` intertwining is NOT claimed (it fails by the curvature obstruction,
  `LineIntegralCovariant.lean` §4b), the coercivity is NOT claimed proved, and the existence of a
  particular solution `A0` for arbitrary `B` is the SAME unbuilt residual as upstream.
* **Compatibility.** The faithful "true average" reading of `lineCoarseRestrictCovLM` holds only on
  COMPATIBLE full blocks (`LineIntegralCovariant.lean` §1 grade-2 Sol caveat). The extension/nonneg/
   U-dependence bricks below are purely algebraic (linearity of the operators) and hold for ALL
   `ell`;
   they do NOT assert faithfulness. The ONE place faithfulness is load-bearing — the coercivity
   target
  (§5) — carries `CompatibleExtent L ell` explicitly. At the `ell=1` U-dependence witness,
  `CompatibleExtent L 1` holds automatically (`1 ∣ n`).
-/

namespace AdalyFormal.Balaban.CovariantHjFaithful

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.KernelSubspace
  AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.Balaban.LineIntegralCovariant
  AdalyFormal.Balaban.Q1Real
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `V^{cov}_faithful(U)`: the gauge-tangent subspace with the FAITHFUL first clause -/

/-- **`V^{cov}_faithful(U) := {A' : Q_k(U)A' = 0, R^{cov}(U)(D_U^*A') = 0}`** — the covariant
gauge-tangent subspace, with the coarse-restriction clause now the FAITHFUL covariant line-integral
`lineCoarseRestrictCovLM U ell` (CMP95 (1.18)/CMP98 (125)) in place of the convicted single-bond
`coarseRestrictCovariantLM`. The second (`R`, site-projection) clause is UNCHANGED. -/
noncomputable def gaugeConstraintSubspaceCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    Submodule ℝ (Bond L → SuTwo) where
  carrier := {A' | lineCoarseRestrictCovLM U ell A' = 0 ∧
    RcovLM U levels (gradCovariantAdjointLM U A') = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · rw [map_add, ha1, hb1, add_zero]
    · rw [map_add, map_add, ha2, hb2, add_zero]
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · rw [map_smul, ha1, smul_zero]
    · rw [map_smul, map_smul, ha2, smul_zero]

theorem mem_gaugeConstraintSubspaceCovFaithful {ell : ℕ}
    {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {A' : Bond L → SuTwo} :
    A' ∈ gaugeConstraintSubspaceCovFaithful ell levels U ↔
      lineCoarseRestrictCovLM U ell A' = 0 ∧
        RcovLM U levels (gradCovariantAdjointLM U A') = 0 := Iff.rfl

#print axioms mem_gaugeConstraintSubspaceCovFaithful

/-- **`W^{cov}_faithful(U) := D_U(V^{cov}_faithful(U))`**, the curl-image of the faithful
gauge-tangent subspace. -/
noncomputable def curlImageCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    Submodule ℝ (PeriodicLatticePlaquette L → SuTwo) :=
  Submodule.map (curlCovariantLM U) (gaugeConstraintSubspaceCovFaithful ell levels U)

theorem mem_curlImageCovFaithful_iff {ell : ℕ}
    {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {y : PeriodicLatticePlaquette L → SuTwo} :
    y ∈ curlImageCovFaithful ell levels U ↔
      ∃ v ∈ gaugeConstraintSubspaceCovFaithful ell levels U, curlCovariantLM U v = y := by
  unfold curlImageCovFaithful
  exact Submodule.mem_map

theorem curl_mem_curlImageCovFaithful_of_mem {ell : ℕ}
    {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {v : Bond L → SuTwo} (hv : v ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    curlCovariantLM U v ∈ curlImageCovFaithful ell levels U :=
  mem_curlImageCovFaithful_iff.mpr ⟨v, hv, rfl⟩

#print axioms mem_curlImageCovFaithful_iff
#print axioms curl_mem_curlImageCovFaithful_of_mem

/-! ## §2 — the closest-point projection onto `W^{cov}_faithful(U)`, and `H_j^{cov}_faithful`,
mirroring `CovariantHjMinimizer.lean` §10–§12 EXACTLY (bare-function route through the FRESH
`PlaqFnL2 L` type, reused from that file — LAW-19). -/

/-- `curlImageCovFaithful`, transported into `PlaqFnL2 L`. -/
noncomputable def curlImageCovHFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    Submodule ℝ (PlaqFnL2 L) :=
  (curlImageCovFaithful ell levels U).map (plaqFnEquiv L).symm.toLinearMap

theorem mem_curlImageCovHFaithful {ell : ℕ}
    {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {v : PlaqFnL2 L} :
    v ∈ curlImageCovHFaithful ell levels U ↔
      plaqFnEquiv L v ∈ curlImageCovFaithful ell levels U := by
  unfold curlImageCovHFaithful
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hEq⟩
    have heq2 : (plaqFnEquiv L).symm y = v := hEq
    rw [← heq2]
    simpa using hy
  · intro hv
    exact ⟨plaqFnEquiv L v, hv, by simp⟩

#print axioms mem_curlImageCovHFaithful

/-- **`W^{cov}_faithful(U)`'s closest-point projection, as a bare function.** -/
noncomputable def curlImageCovProjFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection] :
    (PeriodicLatticePlaquette L → SuTwo) → (PeriodicLatticePlaquette L → SuTwo) :=
  fun A =>
    plaqFnEquiv L ((curlImageCovHFaithful ell levels U).starProjection ((plaqFnEquiv L).symm A))

/-- Range: `curlImageCovProjFaithful` lands in `curlImageCovFaithful`. -/
theorem curlImageCovProjFaithful_mem (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A : PeriodicLatticePlaquette L → SuTwo) :
    curlImageCovProjFaithful ell levels U A ∈ curlImageCovFaithful ell levels U := by
  unfold curlImageCovProjFaithful
  exact mem_curlImageCovHFaithful.mp (Submodule.starProjection_apply_mem _ _)

/-- Fixes points already in `curlImageCovFaithful`. -/
theorem curlImageCovProjFaithful_fixes (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    {A : PeriodicLatticePlaquette L → SuTwo} (h : A ∈ curlImageCovFaithful ell levels U) :
    curlImageCovProjFaithful ell levels U A = A := by
  unfold curlImageCovProjFaithful
  have hmem : (plaqFnEquiv L).symm A ∈ curlImageCovHFaithful ell levels U := by
    rw [mem_curlImageCovHFaithful]
    simpa using h
  rw [Submodule.starProjection_eq_self_iff.mpr hmem]
  simp

/-- **Self-adjoint w.r.t. the BARE pairing `covPlaqInner`.** -/
theorem curlImageCovProjFaithful_selfAdjoint (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A1 A2 : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner (curlImageCovProjFaithful ell levels U A1) A2 =
      covPlaqInner A1 (curlImageCovProjFaithful ell levels U A2) := by
  unfold curlImageCovProjFaithful
  rw [← inner_plaqFnL2_eq_covPlaqInner, ← inner_plaqFnL2_eq_covPlaqInner]
  rw [plaqFnEquiv_symm_apply, plaqFnEquiv_symm_apply, WithLp.toLp_ofLp, WithLp.toLp_ofLp]
  exact Submodule.starProjection_isSymmetric (curlImageCovHFaithful ell levels U) _ _

#print axioms curlImageCovProjFaithful_mem
#print axioms curlImageCovProjFaithful_fixes
#print axioms curlImageCovProjFaithful_selfAdjoint

/-- The correction target: `D_U A0 - W^{cov}_faithful(U).proj(D_U A0)`, chosen so the result lands
in `W^{cov}_faithful(U)ᗮ`. -/
noncomputable def hjCorrectionTargetCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : PeriodicLatticePlaquette L → SuTwo :=
  curlCovariantLM U A0 - curlImageCovProjFaithful ell levels U (curlCovariantLM U A0)

/-- **The correction target is `covPlaqInner`-orthogonal to `curlImageCovFaithful`.** -/
theorem hjCorrectionTargetCovFaithful_orthogonal (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) {A' : PeriodicLatticePlaquette L → SuTwo}
    (hA' : A' ∈ curlImageCovFaithful ell levels U) :
    covPlaqInner A' (hjCorrectionTargetCovFaithful ell levels U A0) = 0 := by
  unfold hjCorrectionTargetCovFaithful
  rw [covPlaqInner_sub_right]
  have hstep : covPlaqInner A' (curlImageCovProjFaithful ell levels U (curlCovariantLM U A0)) =
      covPlaqInner (curlImageCovProjFaithful ell levels U A') (curlCovariantLM U A0) :=
    (curlImageCovProjFaithful_selfAdjoint ell levels U A' (curlCovariantLM U A0)).symm
  rw [hstep, curlImageCovProjFaithful_fixes ell levels U hA', sub_self]

#print axioms hjCorrectionTargetCovFaithful_orthogonal

theorem negCurlImageCovProjFaithful_mem_curlImageCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    -(curlImageCovProjFaithful ell levels U (curlCovariantLM U A0)) ∈
      curlImageCovFaithful ell levels U :=
  Submodule.neg_mem _ (curlImageCovProjFaithful_mem ell levels U (curlCovariantLM U A0))

/-- **`hjCorrectionCovFaithful` — a chosen `v ∈ V^{cov}_faithful(U)`** with
`D_U v = -W^{cov}_faithful(U).proj(D_U A0)`. -/
noncomputable def hjCorrectionCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : Bond L → SuTwo :=
  (mem_curlImageCovFaithful_iff.mp
    (negCurlImageCovProjFaithful_mem_curlImageCovFaithful ell levels U A0)).choose

theorem hjCorrectionCovFaithful_mem (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    hjCorrectionCovFaithful ell levels U A0 ∈ gaugeConstraintSubspaceCovFaithful ell levels U :=
  (mem_curlImageCovFaithful_iff.mp
    (negCurlImageCovProjFaithful_mem_curlImageCovFaithful ell levels U A0)).choose_spec.1

theorem hjCorrectionCovFaithful_curl (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    curlCovariantLM U (hjCorrectionCovFaithful ell levels U A0) =
      -(curlImageCovProjFaithful ell levels U (curlCovariantLM U A0)) :=
  (mem_curlImageCovFaithful_iff.mp
    (negCurlImageCovProjFaithful_mem_curlImageCovFaithful ell levels U A0)).choose_spec.2

#print axioms negCurlImageCovProjFaithful_mem_curlImageCovFaithful
#print axioms hjCorrectionCovFaithful_mem
#print axioms hjCorrectionCovFaithful_curl

/-- **`H_j^{cov}_faithful`, built from a particular solution `A0`.** -/
noncomputable def hjExtensionCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : Bond L → SuTwo :=
  A0 + hjCorrectionCovFaithful ell levels U A0

theorem curlCov_hjExtensionCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    curlCovariantLM U (hjExtensionCovFaithful ell levels U A0) =
      hjCorrectionTargetCovFaithful ell levels U A0 := by
  unfold hjExtensionCovFaithful hjCorrectionTargetCovFaithful
  rw [map_add, hjCorrectionCovFaithful_curl]
  abel

#print axioms curlCov_hjExtensionCovFaithful

/-! ## §3 — `IsBalabanExtensionCovFaithful` + the main extension theorem, with the FAITHFUL
interpolation constraint `lineCoarseRestrictCovLM U ell A = B`. -/

structure IsBalabanExtensionCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (B : CoarseBond L ell → SuTwo) (A : Bond L → SuTwo) : Prop where
  interpolates : lineCoarseRestrictCovLM U ell A = B
  gaugeFixed : RcovLM U levels (gradCovariantAdjointLM U A) = 0
  orthogonal : ∀ A' ∈ gaugeConstraintSubspaceCovFaithful ell levels U,
    covPlaqInner (curlCovariantLM U A') (curlCovariantLM U A) = 0

#print axioms IsBalabanExtensionCovFaithful.mk

/-- **THE MAIN THEOREM: `hjExtensionCovFaithful` satisfies `IsBalabanExtensionCovFaithful`**, GIVEN
a particular solution `A0` already interpolating `B` (through the FAITHFUL covariant `Q`) and
gauge-fixed — the SAME honest hypothesis shape as `CovariantHjMinimizer.
hjExtensionCov_isBalabanExtensionCov`, now with `h1 : lineCoarseRestrictCovLM U ell A0 = B`. The
existence of such an `A0` for arbitrary `B` is the SAME inherited residual, NOT discharged. -/
theorem hjExtensionCovFaithful_isBalabanExtensionCov (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (B : CoarseBond L ell → SuTwo)
    (h1 : lineCoarseRestrictCovLM U ell A0 = B)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    IsBalabanExtensionCovFaithful ell levels U B (hjExtensionCovFaithful ell levels U A0) := by
  obtain ⟨hVQ, hVR⟩ :=
    mem_gaugeConstraintSubspaceCovFaithful.mp (hjCorrectionCovFaithful_mem ell levels U A0)
  refine ⟨?_, ?_, ?_⟩
  · unfold hjExtensionCovFaithful
    simp only [map_add, hVQ, h1, add_zero]
  · unfold hjExtensionCovFaithful
    simp only [map_add, hVR, h2, add_zero]
  · intro A' hA'
    rw [curlCov_hjExtensionCovFaithful]
    exact hjCorrectionTargetCovFaithful_orthogonal ell levels U A0
      (curl_mem_curlImageCovFaithful_of_mem hA')

#print axioms hjExtensionCovFaithful_isBalabanExtensionCov

/-! ## §4 — `Δ_j^{cov}_faithful(U)`: the curl-relative Schur complement, and its nonnegativity /
genuine `U`-dependence — MATCHING the shapes proved for the single-bond `deltaJQuadFormCov`. -/

/-- **`⟨B, Δ_j^{cov}_faithful(U)B⟩ := ‖D_U H_j^{cov}_faithful(U)B‖²_{L²}`** — the covariant Schur
complement, CURL-RELATIVE (`covPlaqInner (D_U H) (D_U H)`), re-based onto the FAITHFUL covariant `Q`
through `hjExtensionCovFaithful`. NOT bare `‖v‖²` (which `CovU1Reduction.lean` proves is FALSE on the
curl-free kernel).

**[CSTAR-LEVEL-MISMATCH] — LEVEL INDEX OF `A0`, RECORDED (denotation-dictionary finding, not
re-litigated here).** `A0 : Bond L → SuTwo` is a field on this tree's SINGLE fine/unit bond level.
The source objects this form stands in for are UNIT-lattice (`Λ`) quadratic forms with the fine
level already integrated out: `compute/denotation_dict/DENOTATION_DICT.tsv` row
`delta_k_unit_p428_3156` (CMP99b p.428 (3.156) `Δ_k`, `src_level = tgt_level = unit (Lambda)`,
sector `bond`) and row `delta96_j_unit_2118` (CMP96 p.243 (2.118) `Δ_j`, likewise unit→unit). The
dictionary's `MISMATCH` verdict on `delta_k_unit_p428_3156` names exactly this file's
`deltaJQuadFormCovFaithful` as the carrier of the collapse (its `V` is `ker` of the same `Q_1`).
The typed separation that makes the collapse UNSTATEABLE already exists and is NOT used here:
`AdalyFormal.Balaban.CStarLevelCorrected.LevelSplit` (with
`AdalyFormal.Balaban.CStarLevelCorrected.LevelSplit.ne : S.fibre ≠ S.constr`). Nothing in this
declaration or its proofs is changed by this note; it is a disclosure of the level index, so that
consumers do not read `A0` as a fine-level field over an already-unit-level `Δ`. -/
noncomputable def deltaJQuadFormCovFaithful (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : ℝ :=
  covPlaqInner (curlCovariantLM U (hjExtensionCovFaithful ell levels U A0))
    (curlCovariantLM U (hjExtensionCovFaithful ell levels U A0))

theorem deltaJQuadFormCovFaithful_nonneg (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : 0 ≤ deltaJQuadFormCovFaithful ell levels U A0 :=
  covPlaqInner_self_nonneg _

#print axioms deltaJQuadFormCovFaithful_nonneg

/-! ### §4a — the `U`-dependence witness: at `ell=1` the FAITHFUL `Q_1(U)` is INJECTIVE (a block of
side 1 is a singleton and the covariant transport `R(g)` is invertible), so
`V^{cov}_faithful(U) = ⊥`, the correction step is a NO-OP, and `deltaJQuadFormCovFaithful` reduces
EXACTLY to `dstarDQuadForm` — transferring `dstarDQuadForm_genuinely_U_dependent` verbatim.
`CompatibleExtent L 1` holds automatically (`1 ∣ n`), so this witness lives ON the faithful domain. -/

/-- **`Q_1(U)` (the FAITHFUL covariant restriction) is injective** — at `ell=1`, `blockOf y 1 = {y}`
(`KernelSubspace.blockOf_one_eq_singleton`) collapses the block average to a single covariant
transport `R(g)·A'(y,μ)`, and `R(g)` is invertible (`RMap_apply_inv_cancel`), so `Q_1(U)A' = 0`
forces `A' = 0`. This is the faithful analogue of
`CovariantHjMinimizer.coarseRestrictCovariantLM_one_eq_zero_imp`. -/
theorem lineCoarseRestrictCovLM_one_eq_zero_imp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {A' : Bond L → SuTwo} (h : lineCoarseRestrictCovLM U 1 A' = 0) : A' = 0 := by
  funext e
  obtain ⟨y, μ⟩ := e
  have hy : y ∈ AdmissibleSubspace.CoarseLattice L 1 :=
    CovariantHjMinimizer.mem_CoarseLattice_one y
  have hcongr := congrFun h (⟨⟨y, hy⟩, μ⟩)
  simp only [lineCoarseRestrictCovLM, lineCoarseRestrictCov, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply] at hcongr
  rw [KernelSubspace.blockOf_one_eq_singleton, Finset.sum_singleton, rZeroA, Finset.sum_range_one,
    pathSite_zero] at hcongr
  set g := periodicPathHolonomy U y (transportPath y y μ 0) with hg_def
  rw [smul_eq_zero] at hcongr
  rcases hcongr with hc | hg
  · exact absurd hc (by norm_num)
  · have hinv := CovariantHjMinimizer.RMap_apply_inv_cancel g⁻¹ (A' (y, μ))
    rw [inv_inv] at hinv
    calc A' (y, μ) = RMap g⁻¹ (RMap g (A' (y, μ))) := hinv.symm
      _ = RMap g⁻¹ 0 := by rw [hg]
      _ = 0 := map_zero _

#print axioms lineCoarseRestrictCovLM_one_eq_zero_imp

/-- **`V^{cov}_faithful(U) = ⊥` at `ell=1`, for ANY `levels`/`U`** — the first (faithful `Q_1`)
clause forces `A' = 0` regardless of the second. -/
theorem gaugeConstraintSubspaceCovFaithful_ell1_eq_bot
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    gaugeConstraintSubspaceCovFaithful 1 levels U = ⊥ := by
  ext A'
  rw [Submodule.mem_bot, mem_gaugeConstraintSubspaceCovFaithful]
  constructor
  · rintro ⟨h1, _⟩
    exact lineCoarseRestrictCovLM_one_eq_zero_imp U h1
  · rintro rfl
    exact ⟨map_zero _, by rw [map_zero, map_zero]⟩

theorem curlImageCovFaithful_ell1_eq_bot
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    curlImageCovFaithful 1 levels U = ⊥ := by
  unfold curlImageCovFaithful
  rw [gaugeConstraintSubspaceCovFaithful_ell1_eq_bot]
  exact Submodule.map_bot _

theorem curlImageCovHFaithful_ell1_eq_bot
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    curlImageCovHFaithful 1 levels U = ⊥ := by
  unfold curlImageCovHFaithful
  rw [curlImageCovFaithful_ell1_eq_bot]
  exact Submodule.map_bot _

#print axioms gaugeConstraintSubspaceCovFaithful_ell1_eq_bot

/-- **`curlImageCovProjFaithful ≡ 0` at `ell=1`** — projecting onto the trivial subspace. -/
theorem curlImageCovProjFaithful_ell1_eq_zero
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels U).HasOrthogonalProjection]
    (A : PeriodicLatticePlaquette L → SuTwo) :
    curlImageCovProjFaithful 1 levels U A = 0 := by
  unfold curlImageCovProjFaithful
  have hmem : (curlImageCovHFaithful 1 levels U).starProjection ((plaqFnEquiv L).symm A) ∈
      curlImageCovHFaithful 1 levels U := Submodule.starProjection_apply_mem _ _
  have hzero : (curlImageCovHFaithful 1 levels U).starProjection ((plaqFnEquiv L).symm A) = 0 := by
    have hbot := curlImageCovHFaithful_ell1_eq_bot (L := L) (levels := levels) (U := U)
    rw [Submodule.eq_bot_iff] at hbot
    exact hbot _ hmem
  rw [hzero, map_zero]

theorem hjCorrectionTargetCovFaithful_ell1_eq_curl
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    hjCorrectionTargetCovFaithful 1 levels U A0 = curlCovariantLM U A0 := by
  unfold hjCorrectionTargetCovFaithful
  rw [curlImageCovProjFaithful_ell1_eq_zero]
  abel

/-- **THE REDUCTION**: at `ell=1`, `deltaJQuadFormCovFaithful` equals `dstarDQuadForm` EXACTLY. -/
theorem deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    deltaJQuadFormCovFaithful 1 levels U A0 = CovariantHj.dstarDQuadForm U A0 := by
  unfold deltaJQuadFormCovFaithful CovariantHj.dstarDQuadForm
  rw [curlCov_hjExtensionCovFaithful, hjCorrectionTargetCovFaithful_ell1_eq_curl]
  rfl

#print axioms deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm

/-- **THE HEADLINE `U`-DEPENDENCE**: two backgrounds `myTrivialU ≠ witnessU`, same underlying bond
field `myWitnessConfig`, same `(ell, levels) = (1, [])` FAITHFUL-`Q` covariant `H_j` construction,
DIFFERENT `Δ_j^{cov}_faithful(U)` values (`0` vs `4`, transferred from
`dstarDQuadForm_genuinely_U_dependent`) — MATCHING the shape of the single-bond
`CovariantHjMinimizer.deltaJQuadFormCov_genuinely_U_dependent`, now over the faithful `Q`. -/
theorem deltaJQuadFormCovFaithful_genuinely_U_dependent :
    deltaJQuadFormCovFaithful 1 ([] : List (KernelSubspace.Level AdmissibleSubspace.witnessL))
        myTrivialU myWitnessConfig ≠
      deltaJQuadFormCovFaithful 1 ([] : List (KernelSubspace.Level AdmissibleSubspace.witnessL))
        witnessU myWitnessConfig := by
  rw [deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm,
    deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm]
  exact dstarDQuadForm_genuinely_U_dependent

#print axioms deltaJQuadFormCovFaithful_genuinely_U_dependent

/-! ## §5 — the coercivity TARGET as a `def : Prop` (no `sorry`/`axiom`) — **REFUTED as written**;
the corrected domain-restricted target lives downstream in `CoercivityTargetsCorrected.lean`.

**GRADE-2 RE-ADJUDICATION (2026-07-26, `compute/sol_deltak_readjudicate/SOL_VERDICT.md` + a Lean
refutation).** Two successive corrections, the SECOND of which refutes even the first:

1. `PROS-COVREBASE-01` (prior): the ORIGINAL target lower-bounded `deltaJ` by the INPUT curl energy
   `dstarDQuadForm U A0`. FALSE: on `A0 ∈ gaugeConstraintSubspaceCovFaithful`, `deltaJ A0 = 0` yet
   `dstarDQuadForm U A0` can be positive. The RHS was changed to the COARSE field norm
   `covCoarseBondInner B B`, `B = Q_k(U)A0` (§5b `faithfulCovCoercivity_shell_holds_on_V` shows the
   `A0 ∈ V` counterexample no longer applies, since there `B=0`).

2. **This correction: the coarse-RHS form `FaithfulCovCoercivityTarget` (below, `∀ A0`) is STILL
   FALSE, not open.** Balaban's `C*Δ_kC ≥ γ₀` (CMP99b p.428) is NOT an all-field bound: it is stated
   on the supported, axial-gauge, `Q₁B=0` fluctuation subspace, reparametrized by free bonds
   (SOL_VERDICT.md Q3). The all-`A0` bound `γ₀‖Q₁A0‖² ≤ deltaJ` is refuted by the CONSTANT field at
   `U=1`: `deltaJ(const)=0` (curl-free) while `‖Q₁(const)‖²>0` (true block average), and the constant
   is a curl-kernel mode with nonzero coarse average — NOT excluded by the mere `V`-restriction.
   Proved in `U1LeadingCoercivity.faithfulCovCoercivityTarget_trivialU_witness_false`; the uniform
   form is refuted outright in `CoercivityTargetsCorrected.faithfulCovCoercivityTargetUniform_false`.
   The domain-restricted (gauge-fixed, then axial) CORRECTED target — the one that reduces to
   `GaugeFixedCurlCoercivity`/(2.128) on `admissibleSubspaceInter` — is in `CoercivityTargetsCorrected`.

The §5b lemmas (`_shell_holds_on_V`, `_eq_zero_of_mem_V`) are RETAINED: they are true (`0 ≤ 0` on
`V`) and are consumed downstream, but they establish non-falsity only ON `V`, NOT on the constant
field, so they do NOT rescue the `∀ A0` target. -/

/-! ### §5a — the faithful COARSE-field `L²` norm, the coarse analogue of `CovariantHj.covBondInner`,
with the SAME `hsInner` SU(2) convention. This is the RHS the corrected target bounds below. -/

/-- **The faithful coarse-field `L²` inner product** on `CoarseBond L ell → 𝔰𝔲(2)` — the coarse
analogue of `CovariantHj.covBondInner` (which sums `hsInner` over `Bond L`), summing the SAME
`SuTwoInner.hsInner` over `CoarseBond L ell`. `covCoarseBondInner B B = ‖B‖²_{L²(coarse)}`. -/
noncomputable def covCoarseBondInner {ell : ℕ} (B B' : CoarseBond L ell → SuTwo) : ℝ :=
  ∑ c : CoarseBond L ell, hsInner (B c) (B' c)

theorem covCoarseBondInner_self_nonneg {ell : ℕ} (B : CoarseBond L ell → SuTwo) :
    0 ≤ covCoarseBondInner B B := by
  unfold covCoarseBondInner
  exact Finset.sum_nonneg (fun c _ => hsInner_self_nonneg (B c))

/-- **The coarse-field norm is strictly positive on a NONZERO coarse field** — so the corrected
target's RHS is genuinely non-vacuous (a real norm, not the constantly-zero form). Mirrors
`ProbeShellVacuity.covPlaqInner_self_pos_of_ne_zero`: `hsInner` is positive-DEFINITE
(`hsInner_self_eq_zero`), not merely PSD. -/
theorem covCoarseBondInner_pos_of_ne {ell : ℕ} {B : CoarseBond L ell → SuTwo} (hB : B ≠ 0) :
    0 < covCoarseBondInner B B := by
  unfold covCoarseBondInner
  apply Finset.sum_pos'
  · exact fun c _ => hsInner_self_nonneg (B c)
  · obtain ⟨c, hc⟩ := Function.ne_iff.mp hB
    exact ⟨c, Finset.mem_univ c, by
      rcases lt_or_eq_of_le (hsInner_self_nonneg (B c)) with h | h
      · exact h
      · exact absurd (hsInner_self_eq_zero h.symm) hc⟩

#print axioms covCoarseBondInner_self_nonneg
#print axioms covCoarseBondInner_pos_of_ne

/-- **The source-admissible domain** (`LineIntegralCovariant.lean` §1 grade-2 Sol caveat): the
faithful covariant `Q` is a TRUE block average only on COMPATIBLE full blocks. Off this domain
`blockOf` truncates and any coercivity constant degrades — hence the coercivity target carries it. -/
def CompatibleExtent (L : PeriodicLatticeExtent) (ell : ℕ) : Prop :=
  0 < ell ∧ ∀ μ, ell ∣ (L μ + 1)

/-- **PLACEHOLDER for Balaban's regular-background (small-field) condition** on `U`. Currently
`True`, so the stated targets are the STRONG, regularity-FREE form (they must hold for ALL `U`);
replacing this with Balaban's actual small-field/regularity predicate can only WEAKEN the hypothesis
burden (fewer backgrounds to cover), never strengthen the claim. Named as a `def` so the uniform
target below carries the antecedent slot explicitly rather than in prose. NOT the real condition. -/
def RegularBackground
    {L : PeriodicLatticeExtent}
    (_U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop := True

/-- **THE UNRESTRICTED (`∀ A0`) COARSE-RHS TARGET — REFUTED as written (NOT open).** Would bound the
minimized covariant curl energy `deltaJQuadFormCovFaithful A0 = ‖D_U H_j^{cov}(A0)‖²` below by a
fixed fraction of the COARSE FIELD `B = lineCoarseRestrictCovLM U ell A0`'s own `L²` norm
`covCoarseBondInner B B`, for EVERY `A0` on the COMPATIBLE domain.

**REFUTED (grade-2, see §5 header):** the constant field at `U=1` has `deltaJ = 0` (curl-free) and
`‖Q₁(const)‖² > 0` (true block average), so no `γ₀ > 0` exists — see
`U1LeadingCoercivity.faithfulCovCoercivityTarget_trivialU_witness_false` (the witness member
`FaithfulCovCoercivityTarget witnessEll [] (trivialU witnessL)` is FALSE). The coarse-RHS correction
of `PROS-COVREBASE-01` only removed the `A0 ∈ V` counterexample (there `B=0`), NOT the constant
curl-kernel mode (which has `B≠0`). Balaban's actual `C*Δ_kC ≥ γ₀` is on the axial-gauge, `Q₁B=0`
fluctuation subspace, NOT all `A0` (SOL_VERDICT.md Q3).

`def : Prop` only — NOT asserted, NO proof, NOT wired. Retained to carry its refutation. The CORRECT
domain-restricted target (gauge-fixed inputs, reducing to `GaugeFixedCurlCoercivity`/(2.128) on the
axial-gauge `admissibleSubspaceInter`) is in `CoercivityTargetsCorrected.lean`. -/
def FaithfulCovCoercivityTarget (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection] : Prop :=
  CompatibleExtent L ell →
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ A0 : Bond L → SuTwo,
      γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0)
        ≤ deltaJQuadFormCovFaithful ell levels U A0

/-- **THE k-UNIFORM UNRESTRICTED TARGET — REFUTED as written (NOT open).** `∃ γ₀ > 0` quantified
OUTSIDE `L, ell, levels, U`. Its witness member is `FaithfulCovCoercivityTarget witnessEll []
(trivialU witnessL)`, which is FALSE (constant field, `U=1`), so this uniform form is outright
refuted: `CoercivityTargetsCorrected.faithfulCovCoercivityTargetUniform_false`. The `RegularBackground`
placeholder is `True`, so it does not shield `trivialU`.

`def : Prop` only — NOT asserted, NO proof, NOT wired. Retained to carry its refutation. This is NOT
the genuine open content; the domain-restricted CORRECTED target (gauge-fixed → axial gauge, reducing
to (2.128)) is in `CoercivityTargetsCorrected.lean`. -/
def FaithfulCovCoercivityTargetUniform : Prop :=
  ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (L : PeriodicLatticeExtent) (ell : ℕ) (levels : List (KernelSubspace.Level L))
      (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
      [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
      [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection],
      CompatibleExtent L ell → RegularBackground U → ∀ A0 : Bond L → SuTwo,
        γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0)
          ≤ deltaJQuadFormCovFaithful ell levels U A0

/-! ### §5b — NON-FALSITY of the corrected shell: the discipline-#5 counterexample is CURED.
On `A0 ∈ gaugeConstraintSubspaceCovFaithful` BOTH sides vanish, so the corrected inequality holds
(`0 ≤ 0`) for ANY `γ₀` — no `0 < 0` contradiction can be assembled. The prior (convicted) target
was refuted at exactly these `A0` because its RHS was the INPUT curl energy, nonzero there. -/

/-- **Probe-1 re-derived in-module**: for ANY `A0 ∈ gaugeConstraintSubspaceCovFaithful` the
minimized Schur complement is IDENTICALLY ZERO. Assembled from the §2/§4 bricks exactly as the
prosecutor's `ProbeShellVacuity.deltaJQuadFormCovFaithful_eq_zero_of_mem_V`. -/
theorem deltaJQuadFormCovFaithful_eq_zero_of_mem_V (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (hA0 : A0 ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    deltaJQuadFormCovFaithful ell levels U A0 = 0 := by
  have hmem : curlCovariantLM U A0 ∈ curlImageCovFaithful ell levels U :=
    curl_mem_curlImageCovFaithful_of_mem hA0
  have hfix := curlImageCovProjFaithful_fixes ell levels U hmem
  unfold deltaJQuadFormCovFaithful
  rw [curlCov_hjExtensionCovFaithful]
  show covPlaqInner (hjCorrectionTargetCovFaithful ell levels U A0)
    (hjCorrectionTargetCovFaithful ell levels U A0) = 0
  unfold hjCorrectionTargetCovFaithful
  rw [hfix, sub_self]
  have hz : hsInner (0 : SuTwo) (0 : SuTwo) = 0 := by
    rw [← hsInnerLeftLM_apply]
    exact map_zero _
  unfold covPlaqInner
  simp only [Pi.zero_apply, hz, Finset.sum_const_zero]

/-- On `A0 ∈ gaugeConstraintSubspaceCovFaithful`, the coarse field `B = Q_k(U)A0 = 0` (first clause
of the subspace), so the corrected RHS-norm `covCoarseBondInner B B` vanishes. This is why the
correction cures discipline #5: the SAME `A0` that made the OLD RHS (`dstarDQuadForm U A0`) nonzero
makes the NEW RHS-norm zero. -/
theorem covCoarseBondInner_restrict_eq_zero_of_mem_V (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (hA0 : A0 ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0) = 0 := by
  have hB : lineCoarseRestrictCovLM U ell A0 = 0 :=
    (mem_gaugeConstraintSubspaceCovFaithful.mp hA0).1
  rw [hB]
  have hz : hsInner (0 : SuTwo) (0 : SuTwo) = 0 := by
    rw [← hsInnerLeftLM_apply]
    exact map_zero _
  unfold covCoarseBondInner
  simp only [Pi.zero_apply, hz, Finset.sum_const_zero]

/-- **THE CURE, machine-checked**: on `A0 ∈ gaugeConstraintSubspaceCovFaithful`, for ANY `γ₀`, the
CORRECTED shell inequality
`γ₀ · covCoarseBondInner B B ≤ deltaJQuadFormCovFaithful A0` holds — both sides are `0`, so it reads
`0 ≤ 0`. Contrast the CONVICTED target, refuted at exactly these `A0`
(`ProbeShellVacuity.FaithfulCovCoercivityTarget_false_of_nonzero_curl_in_V`) because its RHS was the
input curl energy `dstarDQuadForm U A0`, strictly positive there. No `0 < 0` contradiction survives
the correction. -/
theorem faithfulCovCoercivity_shell_holds_on_V (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (γ₀ : ℝ) (A0 : Bond L → SuTwo)
    (hA0 : A0 ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0)
      ≤ deltaJQuadFormCovFaithful ell levels U A0 := by
  rw [covCoarseBondInner_restrict_eq_zero_of_mem_V ell levels U A0 hA0,
    deltaJQuadFormCovFaithful_eq_zero_of_mem_V ell levels U A0 hA0]
  simp

#print axioms deltaJQuadFormCovFaithful_eq_zero_of_mem_V
#print axioms covCoarseBondInner_restrict_eq_zero_of_mem_V
#print axioms faithfulCovCoercivity_shell_holds_on_V

end AdalyFormal.Balaban.CovariantHjFaithful
