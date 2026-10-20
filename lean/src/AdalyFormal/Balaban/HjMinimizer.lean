/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.KernelSubspace
import AdalyFormal.Balaban.LineIntegralAveraging

set_option autoImplicit false

/-!
# `H_j`, the harmonic-extension operator, and `Δ_j`, its Schur-complement action —
CMP95 Sect. D (pp. 26-29), CMP96 pp. 223-224, 242-243

**Task** (see the dispatch mandate): build `H_j` as the minimizer/harmonic-extension operator it
literally is, reusing `LatticeOperators`, `CovariantOperators`, `KernelSubspace`,
`AdmissibleSubspace`, `SuTwoInner` (LAW-19), then `Δ_j` as the Schur complement
`⟨B,Δ_jB⟩ := ‖∂H_jB‖²`.

## Source pins (LAW-11: rendered mathpix pages read directly; images not yet independently
re-rendered at 300dpi by this lane — see the "What is NOT independently image-verified" note below)

* **CMP96 printed p.223** (`balaban_CMP96_1984_propagators_II`, `corpus/mathpix/.../normalized/
  p223.md`): "Let us begin with a generalization of the variational problem considered in **Sect. D
  of [4]** and leading to the operator `H_k`." — `[4]` = CMP95 ("Propagators... I"). This is the
  FIRST concrete confirmation, independent of any prior lane's guess, that `H_k`/`H_j`'s DEFINITION
  lives in CMP95, not CMP96 — exactly the "definition sits in paper I" pattern the dispatch warned
  about, now traced to its actual page.
* **CMP95 printed p.26, heading "D. Operators `H_k` and a Calculation of the Actions"**
  (`corpus/mathpix/balaban_CMP95_1984_propagators_I/normalized/p26.md`): the integral (1.47),
  "With this integral an operator of fundamental importance is connected. It is defined on
  configurations `B` on the lattice `T_1^(k)` and its value on such a configuration is equal to a
  configuration `A` on `T_η` **minimizing the form `(1/2)⟨∂A,∂A⟩` under the conditions `Q_kA=B`,
  `R∂*A=0`**." — THE defining variational characterization.
* **CMP95 printed p.29** (`.../p29.md`), immediately after the closed-form momentum-space formula
  (1.60)/(1.63): "Using (1.60), or better (1.63), we can verify all the properties of `H_kB`:
  **`Q_kH_kB=B`, `R∂*H_kB=0`, `H_kB` is a minimum of `(1/2)⟨∂A,∂A⟩` on the hyperplane
  `{A:Q_kA=B,R∂*A=0}`, which means that `⟨∂A',∂H_kB⟩=0` on the subspace
  `{A':Q_kA'=0,R∂*A'=0}`.**" This THREE-property characterization (interpolation, gauge-fixing,
  orthogonality) is `IsBalabanExtension` below, quoted essentially verbatim.
* **CMP95 printed p.29, eq. (1.65)**: "The action `Δ_k` is thus defined by `⟨B,Δ_kB⟩=⟨∂H_kB,∂H_kB⟩`."
  — THE Schur-complement definition, built below as `deltaJQuadForm`.
* **CMP95 printed p.25, eq. (1.38)/(1.44) and surrounding prose**: "The projection operator `R` has
  a clear meaning. It **is an orthogonal projection on the linear subspace `ΔN(Q_k')`** of
  `L²(T_η)`" — this is `R`'s DEFINITION (the closed-form matrix formula (1.38)/(1.44) is Bałaban's
  own EXPLICIT REALIZATION of this same abstract fact, not a second definition). Built below as
  `RProj`, using mathlib's general Hilbert-space orthogonal-projection machinery directly on this
  "clear meaning" reading, sidestepping the Fourier-domain derivation entirely (a legitimate
  simplification: the closed form and the abstract projection are provably the SAME operator by
  Bałaban's own text, and this file builds the operator via its defining property, not via
  reproducing four pages of momentum-space algebra).
* **CMP96 printed p.243, eq. (2.116)-(2.118)** (`.../p243.md`, already read by a prior lane and
  re-confirmed here): "In the last integral above we make the translation `A→A+H_jB`. The operator
  `H_j` may be different from the operator defined in Sect. D of [4]... but we will prove later
  that they are equal." — CMP96's own multiscale `H_j` generalizes CMP95's single-scale `H_k` via
  the IDENTICAL variational characterization (now over the multiscale block geometry `Q_j` built in
  `LatticeOperators.coarseRestrictCLM`), and eq. (2.117)-(2.118) confirms
  `exp[-½‖∂H_jB‖²] ↔ ⟨B,Δ_jB⟩` with bounds `γ_0‖∂_1B‖² ≤ ⟨B,Δ_jB⟩ ≤ γ_1‖∂_1B‖²` (2.118) — the
  QUANTITATIVE bound, named as a residual below (§6), distinct from the definitional content built
  here.

## What is NOT independently image-verified by THIS lane

The mathpix pages above are `verification_status: machine-draft` (LAW-11 correction: not yet
dual-read/adjudicated `corpus/pages/`). This lane read the machine-draft transcription directly
(not a prior lane's paraphrase) and cross-checked the THREE-property characterization against BOTH
CMP95 p.29's explicit restatement and CMP96 p.243's own re-derivation (2.116)-(2.117), which agree
on the defining content (interpolation + gauge-fixing + minimality) — a load-bearing, disputed
reading would still need a 300dpi image render, which this lane did not additionally perform (time
budget; the OCR-confidence on the load-bearing sentences quoted above is `conf≥0.74` throughout,
the low end being a whole-paragraph line, not the specific quoted clauses).

## What this module builds

1. **`deltaKernelImage`/`RProj`** (§1) — `R`, CMP95 (1.38)/(1.44)/p.25's "clear meaning": the
   orthogonal projection onto `Δ₀(N(Q'))`, built via mathlib's `Submodule.starProjection` (a
   finite-dimensional submodule is automatically `CompleteSpace`, hence automatically
   `HasOrthogonalProjection` — no Poincaré hypothesis needed for `R` ITSELF, unlike
   `KernelSubspace`'s `Δ₀`-positivity theorems, which needed Poincaré for a DIFFERENT purpose,
   injectivity/invertibility of `Δ₀` on `N(Q')`).
2. **`gaugeConstraintSubspace`/`curlImage`** (§2) — the linear subspace
   `V := ker(Q_j) ⊓ ker(R∘∂₀*) ⊂ BondSpace L` (CMP95 p.29's `{A':Q_kA'=0,R∂*A'=0}`) and its image
   `W := ∂₁(V) ⊂ PlaquetteSpace L`.
3. **`IsBalabanExtension`** (§3) — the THREE-property `Prop`-valued structure quoted above, verbatim
   from CMP95 p.29.
4. **`hjExtension`** (§4) — `H_j`, built from ANY particular solution `A0` (interpolates + gauge-
   fixed but not yet minimal) by adding a correction `v ∈ V` chosen so that `∂₁(A0+v)` lands in
   `Wᗮ` (the orthogonal-projection closest-point construction) — **UNCONDITIONAL EXISTENCE, no
   Poincaré/coercivity hypothesis needed**, because the correction step is a finite-dimensional
   closest-point problem, always solvable. `hjExtension_isBalabanExtension` proves the built object
   satisfies all three CMP95 p.29 properties.
5. **`deltaJQuadForm`** (§5) — `Δ_j`, CMP95 (1.65)/CMP96 (2.116): `⟨B,Δ_jB⟩ := ‖∂₁H_jB‖²`, together
   with **`deltaJQuadForm_indep_of_particular_solution`**: the value is **provably independent of
   which particular solution `A0` was used** to build `H_j` — the genuine "Schur complement is a
   well-defined function of `B` alone" content, not merely asserted.
6. **§S91/§S92 minimality attack** (§7) — **CORRECTED (S75-style, in place) after the nested
   `verifier`'s audit found this item's ORIGINAL text overclaimed a CONCRETE witness §7 does not
   contain.** What §7 ACTUALLY builds is `hjExtension_isMinimal`: a GENERAL, unconditional
   Pythagorean-decomposition theorem proving that ANY `A1` satisfying `interpolates`/`gaugeFixed`
   (dropping ONLY `orthogonal`) has `‖∂₁A1‖² ≥ deltaJQuadForm ell levels A0`, with
   `hjExtension_achieves_own_minimum` confirming `hjExtension` itself attains that bound — i.e. the
   orthogonality clause is proved load-bearing FOR MINIMALITY IN GENERAL, a STRONGER guarantee than
   a single concrete non-orthogonal witness would give, but genuinely NOT a witness-based check. NO
   concrete witness (numeric or otherwise) exhibiting a non-orthogonal-but-interpolating `A` is
   built anywhere in this file — see the residual list below, both for that and for the DIFFERENT,
   previously-unflagged gap the verifier's audit surfaced (existence of a particular solution).

## What this module does NOT build — named residuals, not silently dropped

* **EXISTENCE of a particular solution `A0`** (i.e. `∃ A0, coarseRestrictCLM L ell A0 = B ∧
  RProj levels ((gradCLM L).adjoint A0) = 0`, for a GIVEN `B`): this is an UNPROVEN, silently-carried
  HYPOTHESIS threading through `hjExtension_isBalabanExtension`, `hjExtension_isMinimal`, and
  `deltaJQuadForm_indep_of_particular_solution` — **flagged by the nested `verifier`'s audit as
  missing from this list in an earlier draft** (this row is the fix). Nothing in this file proves
  such an `A0` exists for a given `B`; every theorem is stated "GIVEN `A0` with these two
  properties," never "for every `B`, such an `A0` exists." Establishing existence needs surjectivity
  of `(coarseRestrictCLM L ell, RProj levels ∘ (gradCLM L).adjoint)` onto the relevant target space
  — genuinely separate content, not attempted here.
* **A CONCRETE witness for the §7 minimality attack**: `hjExtension_isMinimal` is general and
  unconditional (see item 6 above), but no SPECIFIC non-orthogonal `A1` on the shared witness
  lattice is exhibited with its `‖∂₁A1‖²` computed by hand and shown strictly larger than
  `deltaJQuadForm`. The module's earlier draft (before this correction) claimed such a witness
  existed in §7; it does not — see the file's tail section ("Named residual: a FULLY CONCRETE
  numeric witness…") for the closest attempted concrete computation and exactly what blocked it.
* **UNIQUENESS of `H_jB` as a BOND configuration** (as opposed to uniqueness of `∂₁H_jB`, which
  IS proved via the orthogonal-projection argument): this needs `V ∩ ker(∂₁) = ⊥`, i.e. that `R`'s
  gauge-fixing condition eliminates ALL residual pure-gauge freedom inside the constraint set — the
  genuinely hard content Bałaban's closed-form derivation (CMP95 pp.22-28, the `Δ_a`/`G`
  Lagrange-multiplier computation) exists to establish, and which rests on `Δ₀`'s invertibility on
  `N(Q')`, i.e. **the same named mesh-uniform discrete Poincaré hypothesis `KernelSubspace.
  positive_of_poincare` already carries** (CMP89 (2.26)/(2.27), uncited in CMP89 itself). NOT
  attempted here: it would require reproducing the Lagrange-multiplier elimination (CMP95 eqs.
  1.48-1.60) to show the gauge-tangent space `V` intersects `ker(∂₁)` trivially, genuinely new work
  beyond a routine consequence of what `KernelSubspace` already proved.
* **The quantitative bound (1.67)/(2.118)**: `γ_0‖∂_1B‖² ≤ ⟨B,Δ_jB⟩ ≤ γ_1‖∂_1B‖²` — NOT proved here.
  `deltaJQuadForm ≥ 0` is immediate (§5, a norm-squared), but the TWO-SIDED bound with dimension-only
  constants needs the same closed-form momentum-space computation (CMP95 eqs. 1.66-1.67) this module
  deliberately avoids reproducing (see the module's own design choice, above). Named residual for a
  follow-up lane; **NOT required for `hjExtension`/`deltaJQuadForm` to be well-defined**, only for
  the source's stated quantitative equivalence with `‖∂_1B‖²`.
* **`Δ_a`, `G`** (CMP95 §E, p.29-30): the "resolvent" operators Bałaban builds as an alternative,
  Fourier-friendly representation of `H_k`. Genuinely NOT needed for THIS module's variational
  construction (the orthogonal-projection route bypasses them entirely) — named because the dispatch
  mandate's blocked chain lists them, and this module's route makes them dispensable for `H_j`/`Δ_j`
  specifically, not because they were built.
* **The multiscale domain geometry** (`Ω_j`, `Λ_j` as nested regions of a single lattice, CMP96
  Sect. A pp.223-224): unchanged NO-GO from `KernelSubspace`, `ScaleLadder.lean`'s own scope. This
  module's `ell`/`levels` parameters carry the SAME free-`Finset`-as-data simplification
  `KernelSubspace` already disclosed, not a new one.
-/

/-! ## SUBSTRATE-WIRING CORRECTION (2026-07-24), S75-style, in place

**`gaugeConstraintSubspace`/`IsBalabanExtension`/`hjExtension`/`deltaJQuadForm` (§2-§7 below) NOW
USE THE FAITHFUL `Q_k`** — `LineIntegralAveraging.lineCoarseRestrictCLM` (CMP95 (1.11)/(1.18),
the block-averaged LINE INTEGRAL) — in place of `LatticeOperators.coarseRestrictCLM` (the
single-bond port CMP95 (1.67)'s own kernel-checked refutation, `U1AnchorRefutation.lean`, shows is
FALSE for every `γ₀,γ₁`). This is a FORCED repair, not a preference: the prior encoding made
`BalabanFreeCoercivity` unprovable for ANY constants (a pure-gauge witness has zero
harmonic-extension energy but nonzero single-bond coarse curl); the faithful `Q_k` kills exactly
that witness class (gradients telescope to gradients, `LineIntegralAveraging` §3-§4). Kimi's
third-gate verdict (`compute/kimi_u1lower_gate/KIMI_VERDICT.md` §J2(c)) confirms §1-§7's own
proofs use ONLY continuous-linear-map linearity and submodule structure — none of them is
specific to `coarseRestrictCLM`'s single-bond formula — so they transfer verbatim under this
rename. **§8 below (surjectivity of the coarse-restriction operator, `GaugeCorrectionComplete`)
is DELIBERATELY LEFT REFERRING TO THE OLD `coarseRestrictCLM`** — its own existence machinery
(`coarseLiftValue`'s single-bond lift) does NOT transfer to the faithful double-sum operator (the
neighbour coarse center's bond receives multiplicity `ell−1` under the lift, verified in Kimi's
own numerics, `checks.py` check C9) — this is GAP-1, named `[FAITHFUL-Q-SURJECTIVE]`: surjectivity
of `lineCoarseRestrictCLM`, and the consequent restatement of `GaugeCorrectionComplete` over
`ker(lineCoarseRestrictCLM)`, are NOT proved anywhere in this tree. **This gap does NOT block the
lower half of `BalabanFreeCoercivity`** (`U1Anchor.lean`, now closed below it): that statement
quantifies over a GIVEN `A0` with `B := lineCoarseRestrictCLM L ell A0`, so `interpolates` holds by
`rfl` — no existence/surjectivity theorem is consumed by the closure. §8's theorems below remain
valid, sorry-free facts ABOUT THE OLD OPERATOR; they are simply no longer the existence machinery
`hjExtension_isBalabanExtension`'s hypothesis needs post-swap (that hypothesis is now discharged
per-instance by the caller, as `U1Anchor.BalabanFreeCoercivity`'s own `_hgauge` field already
does) — disclosed here rather than silently left to look like it still closes the gap. -/

namespace AdalyFormal.Balaban.HjMinimizer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.KernelSubspace
open AdalyFormal.Balaban.LineIntegralAveraging

variable {L : PeriodicLatticeExtent}

/-! ## §1. `R` — the orthogonal projection onto `Δ₀(N(Q'))` (CMP95 p.25, eq. 1.38/1.44) -/

/-- **`Δ₀(N(Q'))`, CMP95 p.25's `ΔN(Q_k')`** — the image of the kernel subspace under the site
Laplacian `Δ₀ = siteLaplacianCLM`. A finite-dimensional submodule of `SiteSpace L`. -/
noncomputable def deltaKernelImage {L : PeriodicLatticeExtent} (levels : List (Level L)) :
    Submodule ℝ (SiteSpace L) :=
  Submodule.map (siteLaplacianCLM L).toLinearMap (kernelSubspaceH levels)

/-- **`R`, CMP95 p.25's "clear meaning": the orthogonal projection onto `ΔN(Q_k')`.**
Built via mathlib's `Submodule.starProjection`, which requires
`(deltaKernelImage levels).HasOrthogonalProjection` — automatic here because
`deltaKernelImage levels` is a submodule of the FINITE-DIMENSIONAL space `SiteSpace L`, hence
itself finite-dimensional, hence `CompleteSpace`, hence `HasOrthogonalProjection`
(`Submodule.HasOrthogonalProjection.ofCompleteSpace`), all resolved by typeclass search — no
Poincaré hypothesis needed for `R` ITSELF. -/
noncomputable def RProj {L : PeriodicLatticeExtent} (levels : List (Level L)) :
    SiteSpace L →L[ℝ] SiteSpace L :=
  (deltaKernelImage levels).starProjection

/-- **`R` lands inside `Δ₀(N(Q'))`** — the defining property of a projection onto a subspace,
needed repeatedly below. -/
theorem RProj_apply_mem {L : PeriodicLatticeExtent} (levels : List (Level L))
    (v : SiteSpace L) : RProj levels v ∈ deltaKernelImage levels :=
  Submodule.starProjection_apply_mem _ v

#print axioms RProj_apply_mem

/-! ## §2. The gauge-tangent subspace `V := ker(Q_j) ⊓ ker(R∘∂₀*)` and its curl-image `W` -/

/-- **`V := {A' : Q_jA'=0, R∂*A'=0}`, CMP95 p.29's constraint subspace** — a genuine linear
`Submodule` of `BondSpace L` (an intersection of two linear conditions, since `Q_j`, `R`, `∂₀*` are
all continuous LINEAR maps). **Built as an explicit `carrier` submodule** (mirroring
`KernelSubspace.kernelSubspace`'s own pattern, LAW-19), not via `LinearMap.ker` — sidesteps the
`ContinuousLinearMap.toLinearMap` coercion friction entirely, so membership unfolds by `Iff.rfl`. -/
noncomputable def gaugeConstraintSubspace {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (Level L)) : Submodule ℝ (BondSpace L) where
  carrier := {A' | lineCoarseRestrictCLM L ell A' = 0 ∧ RProj levels ((gradCLM L).adjoint A') = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · simp only [map_add, ha1, hb1, add_zero]
    · simp only [map_add, ha2, hb2, add_zero]
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · simp only [map_smul, ha1, smul_zero]
    · simp only [map_smul, ha2, smul_zero]

theorem mem_gaugeConstraintSubspace {L : PeriodicLatticeExtent} {ell : ℕ}
    {levels : List (Level L)} {A' : BondSpace L} :
    A' ∈ gaugeConstraintSubspace ell levels ↔
      lineCoarseRestrictCLM L ell A' = 0 ∧ RProj levels ((gradCLM L).adjoint A') = 0 := Iff.rfl

#print axioms mem_gaugeConstraintSubspace

/-- **`W := ∂₁(V)`, the curl-image of the gauge-tangent subspace** — a submodule of
`PlaquetteSpace L`. -/
noncomputable def curlImage {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L)) :
    Submodule ℝ (PlaquetteSpace L) :=
  Submodule.map (curlCLM L).toLinearMap (gaugeConstraintSubspace ell levels)

/-- **Bridging `curlImage`'s membership to the underlying `Submodule.map` existential**, needed
because `curlImage` is a plain `def` and `Submodule.mem_map` does not unify through it without an
explicit `unfold`. -/
theorem mem_curlImage_iff {L : PeriodicLatticeExtent} {ell : ℕ} {levels : List (Level L)}
    {y : PlaquetteSpace L} :
    y ∈ curlImage ell levels ↔ ∃ v ∈ gaugeConstraintSubspace ell levels, curlCLM L v = y := by
  unfold curlImage
  exact Submodule.mem_map

/-- **The forward direction of `mem_curlImage_iff`, as a standalone helper** — `curlCLM L v ∈ W`
whenever `v ∈ V`, the fact needed repeatedly below in place of the non-unifying
`Submodule.mem_map_of_mem`. -/
theorem curlCLM_mem_curlImage_of_mem {L : PeriodicLatticeExtent} {ell : ℕ}
    {levels : List (Level L)} {v : BondSpace L} (hv : v ∈ gaugeConstraintSubspace ell levels) :
    curlCLM L v ∈ curlImage ell levels :=
  mem_curlImage_iff.mpr ⟨v, hv, rfl⟩

#print axioms mem_curlImage_iff
#print axioms curlCLM_mem_curlImage_of_mem

/-! ## §3. `IsBalabanExtension` — the THREE-property characterization, CMP95 p.29 verbatim -/

/-- **`IsBalabanExtension ell levels B A`: `A` is a Bałaban harmonic extension of `B`.**
Verbatim from CMP95 p.29: "`Q_kH_kB=B`, `R∂*H_kB=0`, `H_kB` is a minimum of `(1/2)⟨∂A,∂A⟩` on the
hyperplane `{A:Q_kA=B,R∂*A=0}`, which means that `⟨∂A',∂H_kB⟩=0` on the subspace
`{A':Q_kA'=0,R∂*A'=0}`." The third field is stated in exactly this "means" form (the orthogonality
characterization of minimality), not re-derived from a separate minimization predicate. -/
structure IsBalabanExtension {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L))
    (B : CoarseBondSpace L ell) (A : BondSpace L) : Prop where
  interpolates : lineCoarseRestrictCLM L ell A = B
  gaugeFixed : RProj levels ((gradCLM L).adjoint A) = 0
  orthogonal : ∀ A' ∈ gaugeConstraintSubspace ell levels,
    (inner ℝ (curlCLM L A') (curlCLM L A) : ℝ) = 0

#print axioms IsBalabanExtension.mk

/-! ## §4. `H_j` — built from a particular solution, unconditional existence -/

/-- **The target correction in `PlaquetteSpace L`**: `-W.starProjection(∂₁A0)`, chosen so that
`∂₁A0 + (this target)` lands in `Wᗮ` (`sub_starProjection_mem_orthogonal`, applied to `∂₁A0`). -/
noncomputable def hjCorrectionTarget {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (Level L)) (A0 : BondSpace L) : PlaquetteSpace L :=
  curlCLM L A0 - (curlImage ell levels).starProjection (curlCLM L A0)

/-- **The correction target lies in `Wᗮ`** — the defining orthogonality fact of the closest-point
construction (`sub_starProjection_mem_orthogonal`, mathlib). -/
theorem hjCorrectionTarget_mem_orthogonal {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (Level L)) (A0 : BondSpace L) :
    hjCorrectionTarget ell levels A0 ∈ (curlImage ell levels)ᗮ := by
  unfold hjCorrectionTarget
  exact Submodule.sub_starProjection_mem_orthogonal (curlCLM L A0)

/-- **The NEGATIVE of the star-projection lies in `W`** (submodules are closed under negation and
`starProjection_apply_mem` lands in `W`) — this is what makes `v ∈ V` with `∂₁v = -W.starProjection
(∂₁A0)` EXIST: `-W.starProjection(∂₁A0) ∈ W = ∂₁(V)` by definition of `curlImage`. -/
theorem negStarProjection_mem_curlImage {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (Level L)) (A0 : BondSpace L) :
    -(curlImage ell levels).starProjection (curlCLM L A0) ∈ curlImage ell levels :=
  Submodule.neg_mem _ (Submodule.starProjection_apply_mem _ _)

/-- **`hjCorrection` — a chosen `v ∈ V` with `∂₁v = -W.starProjection(∂₁A0)`**, extracted from
`mem_curlImage_iff` (which unfolds `curlImage`'s membership to exactly this existential) via
`Classical.choose`. -/
noncomputable def hjCorrection {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L))
    (A0 : BondSpace L) : BondSpace L :=
  (mem_curlImage_iff.mp (negStarProjection_mem_curlImage ell levels A0)).choose

theorem hjCorrection_mem {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L))
    (A0 : BondSpace L) : hjCorrection ell levels A0 ∈ gaugeConstraintSubspace ell levels :=
  (mem_curlImage_iff.mp (negStarProjection_mem_curlImage ell levels A0)).choose_spec.1

theorem hjCorrection_curl {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L))
    (A0 : BondSpace L) :
    curlCLM L (hjCorrection ell levels A0) =
      -(curlImage ell levels).starProjection (curlCLM L A0) :=
  (mem_curlImage_iff.mp (negStarProjection_mem_curlImage ell levels A0)).choose_spec.2

#print axioms hjCorrection_mem
#print axioms hjCorrection_curl

/-- **`H_j` — the harmonic extension, built from a particular solution `A0`.** Unconditional:
requires no hypothesis on `A0` to be WELL-DEFINED as a term (it is `A0` plus a correction that
always exists, §4's whole point); `A0` itself satisfying `interpolates`/`gaugeFixed` is what makes
the RESULT satisfy `IsBalabanExtension` (`hjExtension_isBalabanExtension` below). -/
noncomputable def hjExtension {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L))
    (A0 : BondSpace L) : BondSpace L :=
  A0 + hjCorrection ell levels A0

/-- **`∂₁(H_jA0) = hjCorrectionTarget ell levels A0`** — the curl of the built extension is exactly
the `Wᗮ`-component of `∂₁A0`, independent of any hypothesis on `A0`. -/
theorem curlCLM_hjExtension {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L))
    (A0 : BondSpace L) :
    curlCLM L (hjExtension ell levels A0) = hjCorrectionTarget ell levels A0 := by
  unfold hjExtension hjCorrectionTarget
  rw [map_add, hjCorrection_curl]
  abel

#print axioms curlCLM_hjExtension

/-- **THE MAIN THEOREM: `hjExtension` satisfies `IsBalabanExtension`**, GIVEN that the particular
solution `A0` already interpolates `B` and is gauge-fixed. This is the honest hypothesis this
construction needs — NOT a Poincaré/coercivity assumption, but literally "a particular solution of
the two LINEAR constraints exists for THIS `A0`, THIS `B`" (`A0` and `B` are already related by
`h1`/`h2`, so THIS hypothesis is trivially instantiable by taking `B := coarseRestrictCLM L ell A0`
whenever `RProj levels ((gradCLM L).adjoint A0) = 0` already holds for some `A0`). The SEPARATE,
harder content — "for an ARBITRARY given `B`, some such `A0` exists" — is named as an explicit
residual in the module docstring ("EXISTENCE of a particular solution `A0`"), NOT checked by §7
(CORRECTED: an earlier draft of this comment wrongly pointed to §7 for that check; §7 is about
minimality among solutions that already exist, a different question). -/
theorem hjExtension_isBalabanExtension {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (Level L)) (A0 : BondSpace L) (B : CoarseBondSpace L ell)
    (h1 : lineCoarseRestrictCLM L ell A0 = B) (h2 : RProj levels ((gradCLM L).adjoint A0) = 0) :
    IsBalabanExtension ell levels B (hjExtension ell levels A0) := by
  obtain ⟨hVQ, hVR⟩ := mem_gaugeConstraintSubspace.mp (hjCorrection_mem ell levels A0)
  refine ⟨?_, ?_, ?_⟩
  · unfold hjExtension
    simp only [map_add, hVQ, h1, add_zero]
  · unfold hjExtension
    simp only [map_add, hVR, h2, add_zero]
  · intro A' hA'
    rw [curlCLM_hjExtension]
    have hmem : curlCLM L A' ∈ curlImage ell levels := curlCLM_mem_curlImage_of_mem hA'
    have h := (Submodule.mem_orthogonal' (curlImage ell levels)
      (hjCorrectionTarget ell levels A0)).mp
      (hjCorrectionTarget_mem_orthogonal ell levels A0) (curlCLM L A') hmem
    rwa [real_inner_comm] at h

#print axioms hjExtension_isBalabanExtension

/-! ## §5. `Δ_j` — the Schur complement `⟨B,Δ_jB⟩ := ‖∂₁H_jB‖²`, CMP95 (1.65)/CMP96 (2.116) -/

/-- **`Δ_j`'s quadratic form, CMP95 eq. (1.65)/CMP96 eq. (2.117)**: `⟨B,Δ_jB⟩ := ‖∂₁H_jB‖²`,
computed from any particular solution `A0` via `hjExtension`. -/
noncomputable def deltaJQuadForm {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L))
    (A0 : BondSpace L) : ℝ :=
  ‖curlCLM L (hjExtension ell levels A0)‖ ^ 2

theorem deltaJQuadForm_nonneg {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L))
    (A0 : BondSpace L) : 0 ≤ deltaJQuadForm ell levels A0 := by
  unfold deltaJQuadForm; positivity

#print axioms deltaJQuadForm_nonneg

/-- **`hjCorrectionTarget` is INVARIANT under adding a `V`-element to `A0`** — the algebraic core
of well-definedness: for `v ∈ V`, `∂₁v ∈ W`, so `W.starProjection` fixes it
(`starProjection_eq_self_iff`), and the target's linear/affine structure absorbs it exactly. -/
theorem hjCorrectionTarget_add_of_mem {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (Level L)) (A0 v : BondSpace L) (hv : v ∈ gaugeConstraintSubspace ell levels) :
    hjCorrectionTarget ell levels (A0 + v) = hjCorrectionTarget ell levels A0 := by
  unfold hjCorrectionTarget
  have hWv : curlCLM L v ∈ curlImage ell levels := curlCLM_mem_curlImage_of_mem hv
  have hfix : (curlImage ell levels).starProjection (curlCLM L v) = curlCLM L v :=
    Submodule.starProjection_eq_self_iff.mpr hWv
  rw [map_add, map_add, hfix]
  abel

#print axioms hjCorrectionTarget_add_of_mem

/-- **`deltaJQuadForm` is independent of the choice of particular solution `A0`** — the genuine
"the Schur complement is a well-defined function of `B` alone" content: any two particular
solutions of the SAME `B`'s linear constraints differ by an element of `V = gaugeConstraintSubspace`
(both `Q_j` and `RProj∘∂₀*` are LINEAR, so the difference of two zeros-of-the-same-affine-condition
lies in the kernel intersection), and `hjCorrectionTarget_add_of_mem` shows the built extension's
curl is unchanged by any such shift. -/
theorem deltaJQuadForm_indep_of_particular_solution {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (Level L)) (A0 A0' : BondSpace L) (B : CoarseBondSpace L ell)
    (h1 : lineCoarseRestrictCLM L ell A0 = B) (h2 : RProj levels ((gradCLM L).adjoint A0) = 0)
    (h1' : lineCoarseRestrictCLM L ell A0' = B) (h2' : RProj levels ((gradCLM L).adjoint A0') = 0) :
    deltaJQuadForm ell levels A0 = deltaJQuadForm ell levels A0' := by
  have hVmem : A0' - A0 ∈ gaugeConstraintSubspace ell levels := by
    rw [mem_gaugeConstraintSubspace]
    refine ⟨?_, ?_⟩
    · simp only [map_sub, h1', h1, sub_self]
    · simp only [map_sub, h2', h2, sub_self]
  have hkey : hjCorrectionTarget ell levels A0' = hjCorrectionTarget ell levels A0 := by
    have heq : A0 + (A0' - A0) = A0' := by abel
    have hstep := hjCorrectionTarget_add_of_mem ell levels A0 (A0' - A0) hVmem
    rw [heq] at hstep
    exact hstep
  unfold deltaJQuadForm
  rw [curlCLM_hjExtension, curlCLM_hjExtension, hkey]

#print axioms deltaJQuadForm_indep_of_particular_solution

/-! ## §6. Named residual: the quantitative bound (1.67)/(2.118) — NOT built here

**Deliberately NOT formalized as a `Prop`, unlike the rest of this file's residuals.** CMP95
(1.67)/CMP96 (2.118) states `γ_0‖∂_1B‖² ≤ ⟨B,Δ_jB⟩ ≤ γ_1‖∂_1B‖²` where `∂_1B` is the CURL TAKEN ON
THE COARSE/UNIT LATTICE that `B : CoarseBondSpace L ell` itself lives on — a genuinely DIFFERENT
operator from this file's `curlCLM L : BondSpace L →L[ℝ] PlaquetteSpace L` (the FINE-lattice curl).
No coarse-lattice plaquette structure / coarse curl is built anywhere in this tree yet. An earlier
draft of this section stated the bound using `‖curlCLM L A0‖` (the FINE curl of a particular
solution) as a stand-in — **this is dimensionally/conceptually the WRONG object** (comparing a
fine-lattice quantity to what the source states as a coarse-lattice one), so it was REMOVED rather
than shipped as a plausible-looking but incorrect residual `Prop` (a wrong statement is worse than
a named prose gap, per the project's definition-rigging discipline). **The residual, correctly
named**: build a coarse curl `∂_1' : CoarseBondSpace L ell →L[ℝ] (coarse plaquette space)` (does not
exist in this tree), then state and prove the two-sided bound against `‖∂_1'B‖²`. NOT required for
`hjExtension`/`deltaJQuadForm` to be well-defined (§4-§5 are complete and unconditional modulo the
particular-solution hypothesis) — only for the source's stated quantitative equivalence. -/

/-! ## §7. `hjExtension` is genuinely MINIMAL — the S91-style "junk witness is provably worse"
guarantee, built as a GENERAL theorem (not a single concrete counterexample) -/

/-- **THE MINIMALITY THEOREM**: for ANY OTHER particular solution `A1` of the SAME two linear
constraints (`interpolates B`, `gaugeFixed`), `‖∂₁A1‖² ≥ deltaJQuadForm ell levels A0` — i.e. the
value `hjExtension` achieves is the GENUINE INFIMUM among ALL candidates satisfying the two linear
conditions alone, not merely A PARTICULAR value. This is the precise, general form of the S91
attack the mandate demands: it is NOT enough to exhibit one concrete `A1` with strictly larger
norm (a spot check); this proves EVERY competitor is no better, by the Pythagorean decomposition
`curlCLM A1 = p + q` with `p ⊥ q`, `p = hjCorrectionTarget` (independent of `A1`, `deltaJQuadForm`'s
own value) and `q ∈ curlImage ell levels` (the residual freedom `A1` has beyond `hjExtension`). -/
theorem hjExtension_isMinimal {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L))
    (A0 A1 : BondSpace L) (B : CoarseBondSpace L ell)
    (h1 : lineCoarseRestrictCLM L ell A0 = B) (h2 : RProj levels ((gradCLM L).adjoint A0) = 0)
    (h1' : lineCoarseRestrictCLM L ell A1 = B) (h2' : RProj levels ((gradCLM L).adjoint A1) = 0) :
    deltaJQuadForm ell levels A0 ≤ ‖curlCLM L A1‖ ^ 2 := by
  have hVmem : A1 - A0 ∈ gaugeConstraintSubspace ell levels := by
    rw [mem_gaugeConstraintSubspace]
    refine ⟨?_, ?_⟩
    · simp only [map_sub, h1', h1, sub_self]
    · simp only [map_sub, h2', h2, sub_self]
  set p := hjCorrectionTarget ell levels A0 with hp_def
  set q := curlCLM L A1 - p with hq_def
  have hsplit_A1 : curlCLM L A1 = curlCLM L A0 + curlCLM L (A1 - A0) := by
    rw [← map_add]
    congr 1
    abel
  have hwmem : curlCLM L (A1 - A0) ∈ curlImage ell levels := curlCLM_mem_curlImage_of_mem hVmem
  have hqeq : q = curlCLM L (A1 - A0) + (curlImage ell levels).starProjection (curlCLM L A0) := by
    rw [hq_def, hp_def]
    unfold hjCorrectionTarget
    rw [hsplit_A1]
    abel
  have hqmem : q ∈ curlImage ell levels := by
    rw [hqeq]
    exact Submodule.add_mem _ hwmem (Submodule.starProjection_apply_mem _ _)
  have hporth : p ∈ (curlImage ell levels)ᗮ := hjCorrectionTarget_mem_orthogonal ell levels A0
  have hinner : (inner ℝ p q : ℝ) = 0 :=
    (Submodule.mem_orthogonal' (curlImage ell levels) p).mp hporth q hqmem
  have hsplit : curlCLM L A1 = p + q := by rw [hq_def]; abel
  have hpyth : ‖curlCLM L A1‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    rw [hsplit, norm_add_sq_real, hinner]; ring
  have hdelta : deltaJQuadForm ell levels A0 = ‖p‖ ^ 2 := by
    unfold deltaJQuadForm; rw [curlCLM_hjExtension]
  rw [hpyth, hdelta]
  nlinarith [sq_nonneg ‖q‖, norm_nonneg q]

#print axioms hjExtension_isMinimal

/-- **Corollary, stated in the `IsBalabanExtension`-facing form**: `hjExtension`'s OWN curl-norm
equals `deltaJQuadForm` by definition — confirming `deltaJQuadForm`/`hjExtension` are not merely
"a solution" but genuinely THE minimum among ALL competitors (`hjExtension_isMinimal`), matching
CMP95 p.29's own claim ("`H_kB` is A MINIMUM," not merely "a critical point"). -/
theorem hjExtension_achieves_own_minimum {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (Level L)) (A0 : BondSpace L) :
    ‖curlCLM L (hjExtension ell levels A0)‖ ^ 2 = deltaJQuadForm ell levels A0 := by
  unfold deltaJQuadForm; rfl

#print axioms hjExtension_achieves_own_minimum

/-! ## §8. EXISTENCE of a particular solution `A0` — the dangerous residual, addressed

**Dispatch target** (this pass): the module docstring's own residual, "EXISTENCE of a particular
solution `A0`" — `∀ B, ∃ A0, coarseRestrictCLM L ell A0 = B ∧
RProj levels ((gradCLM L).adjoint A0) = 0`. Split, per the dispatch's own instruction, into the two
genuinely separate facts:

* **(a) SURJECTIVITY of `coarseRestrictCLM`, §8a below — PROVED, UNCONDITIONALLY, by an EXPLICIT
  construction** (`coarseRestrictCLM_surjective`): given `B`, define `A0` to carry ALL of `B`'s mass
  at the SINGLE fine bond based at each coarse center itself (`coarseLiftValue`: `(y,μ) ↦
  ell⁴·B(y,μ)` when `y ∈ CoarseLattice`, `0` elsewhere — the `ell⁴` exactly inverts
  `coarseRestrict`'s own `1/ell⁴` normalization, §"What this module builds" item 6's R2
  correction). `coarseLattice_unique` (`AdmissibleSubspace.lean`, LAW-19 reuse, hypothesis-free)
  proves NO OTHER coarse center's block can also contain the point `y`, so every other block member
  contributes `0` to the average and `Finset.sum_eq_single` collapses it back to exactly `B(y,μ)`.
  Needs ONLY `ell > 0` (for self-membership `y ∈ blockOf y ell`) —
  `coarseLattice_exists`'s tiling divisibility hypothesis is NOT required, since this construction
  never needs every fine site COVERED by a block, only that distinct coarse centers' blocks cannot
  both claim the same point.
* **(b) The gauge-fixing correction, §8b-§8d below — REDUCED, not closed, to one named
  Submodule-equality hypothesis, with the reduction itself PROVED as a general, hypothesis-light
  lemma.** `exists_particular_iff_ker_sup_ker_eq_top` (§8b): for ANY surjective `T1` and ANY `T2`
  (arbitrary linear maps between real vector spaces, no continuity/finite-dimensionality needed),
  `(∀ y1, ∃ x, T1 x=y1 ∧ T2 x=0) ↔ LinearMap.ker T1 ⊔ LinearMap.ker T2 = ⊤`. Applied to
  `T1 := coarseRestrictCLM L ell` (surjective by (a)) and
  `T2 := RProj levels ∘ (gradCLM L).adjoint`, the ENTIRE existence question reduces to ONE
  Submodule equality, named `GaugeCorrectionComplete` (§8c) in the SAME house style as
  `KernelSubspace.positive_of_poincare`'s `hbound` — an explicit, checkable hypothesis threaded
  through ONE theorem, not silently assumed inside every downstream one. **Evidence this
  hypothesis is genuinely hard, not a formality** (prose reasoning, NOT a claimed/proved Lean
  fact — no theorem below asserts it): by standard finite-dimensional adjoint duality,
  `(ker T)ᗮ = range(T*)` for finite-dim `T`, so `GaugeCorrectionComplete` is equivalent to
  `range((coarseRestrictCLM)*) ∩ range(∂₀∘RProj) = {0}` — i.e. that no nonzero "coarse-lift" bond
  field (constant per direction within each block — literally `(coarseRestrictCLM)*`'s own range,
  by the SAME averaging-adjoint computation `coarseLiftValue` above realizes concretely for a
  single block) coincides with a nonzero PURE-GAUGE field `∂₀λ` arising from `λ ∈ Δ₀(N(Q'))`.
  This is EXACTLY the kind of fact Bałaban's own Lagrange-multiplier `Δ_a`/`G` construction
  (CMP95 §E, pp.29-30 — named in THIS
  file's OWN "What this module does NOT build" list as "genuinely NOT needed for THIS module's
  variational construction... bypasses them entirely") exists to supply: solving the constrained
  system `{Q_kA=B, R∂*A=0}` for a GIVEN `B` is precisely what `H_k`'s closed-form momentum-space
  formula (CMP95 (1.60)/(1.63), same "NOT built" list) computes. **This SHARPENS, not merely
  repeats, the module's own docstring**: `Δ_a`/`G` are not merely "dispensable for DEFINING
  `H_j`/`Δ_j`" (still true, unchanged) — on the evidence above they are the missing primitive for
  proving `H_j`/`Δ_j` are DEFINED AT EVERY `B`, a genuinely different claim. **NOT shown to be the
  SAME hypothesis as `KernelSubspace.positive_of_poincare`** (that is `Δ₀`'s POSITIVITY on
  `N(Q')`; `GaugeCorrectionComplete` is a statement about the intersection of two specific
  subspaces of `BondSpace L`) — related in spirit (both trace to CMP95's Lagrange-multiplier
  elimination, pp.22-28) but NOT proved here to be logically equivalent or mutually reducible.
* **(c) A genuinely UNCONDITIONAL special case, §8d**: when `deltaKernelImage levels = ⊥`
  (`RProj` is then PROVABLY the zero map, `RProj_eq_zero_of_deltaKernelImage_eq_bot`), the
  gauge-fixing condition is vacuous for every `A`, `GaugeCorrectionComplete` holds trivially, and
  full existence
  follows WITHOUT any named hypothesis (`particularSolution_exists_of_deltaKernelImage_eq_bot`).

**What this section does NOT claim**: `GaugeCorrectionComplete` itself is NOT proved for a general
`levels` (only reduced to, and shown equivalent to, the target existence property, plus proved in
the degenerate `deltaKernelImage = ⊥` corner case). No falsifying instance is exhibited either —
the missing primitive (`Δ_a`/`G`'s Lagrange-multiplier inversion) is not yet built anywhere in this
tree, matching this file's own pre-existing NO-GO on those operators, so neither a proof nor a
concrete refutation of `GaugeCorrectionComplete` for generic `levels` is attempted here. -/

/-! ### §8a. Surjectivity of `coarseRestrictCLM` — UNCONDITIONAL, explicit construction -/

/-- **The explicit block-delta lift of `Bf : CoarseBond L ell → ℝ`**: all of `Bf(y,μ)`'s mass is
placed on the SINGLE fine bond `(y,μ)` based at the coarse center `y` itself (scaled by `ell⁴` to
invert `coarseRestrict`'s own `1/ell⁴` normalization), `0` on every fine bond not based at a coarse
center. -/
noncomputable def coarseLiftValue {L : PeriodicLatticeExtent} (ell : ℕ)
    (Bf : CoarseBond L ell → ℝ) (b : Bond L) : ℝ :=
  if h : b.1 ∈ AdmissibleSubspace.CoarseLattice L ell then
    (ell : ℝ) ^ 4 * Bf (⟨b.1, h⟩, b.2)
  else 0

/-- **The lift genuinely inverts `coarseRestrict`**: averaging `coarseLiftValue ell Bf` back over
any block reproduces `Bf` exactly at that coarse bond. The ONLY nonzero contributor to the block sum
is the block's OWN coarse center `y`: `coarseLattice_unique` (`AdmissibleSubspace.lean`, LAW-19)
rules out any OTHER coarse-lattice member `x ≠ y` also owning a point (namely itself) inside
`blockOf y ell` — if such an `x` were in `CoarseLattice`, uniqueness would force `x = y`,
contradicting `x ≠ y`; otherwise the `if` in `coarseLiftValue` gives `0` directly. -/
theorem coarseRestrict_coarseLiftValue {L : PeriodicLatticeExtent} (ell : ℕ) (hell : 0 < ell)
    (Bf : CoarseBond L ell → ℝ) (c : CoarseBond L ell) :
    coarseRestrict ell (coarseLiftValue ell Bf) c = Bf c := by
  obtain ⟨⟨y, hy⟩, μ⟩ := c
  have hself : y ∈ AdmissibleSubspace.blockOf y ell := by
    rw [AdmissibleSubspace.mem_blockOf]
    intro ν
    exact ⟨le_refl _, by omega⟩
  have hsum : (∑ x ∈ AdmissibleSubspace.blockOf y ell, coarseLiftValue ell Bf (x, μ)) =
      coarseLiftValue ell Bf (y, μ) := by
    apply Finset.sum_eq_single
    · intro x hx hxy
      by_cases hxc : x ∈ AdmissibleSubspace.CoarseLattice L ell
      · exfalso
        have hxself : x ∈ AdmissibleSubspace.blockOf x ell := by
          rw [AdmissibleSubspace.mem_blockOf]
          intro ν
          exact ⟨le_refl _, by omega⟩
        exact hxy (AdmissibleSubspace.coarseLattice_unique ell hxc hy hxself hx)
      · simp only [coarseLiftValue, dif_neg hxc]
    · intro h
      exact absurd hself h
  simp only [coarseRestrict]
  rw [hsum]
  simp only [coarseLiftValue, dif_pos hy]
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  field_simp

#print axioms coarseRestrict_coarseLiftValue

/- **`coarseRestrictCLM_apply` RELOCATED (substrate-wiring lane, 2026-07-24)** to
`LatticeOperators.lean` (right next to `coarseRestrictCLM`'s own definition, alongside
`gradCLM_apply`/`curlCLM_apply`) — it used nothing from this file, and `U1CommutingSquare.lean`
needed direct access to it once `CoarseCurl.lean`'s (vestigial) import of `HjMinimizer` was
removed to break an import cycle (`HjMinimizer → LineIntegralAveraging → CoarseShiftCovariance →
CoarseCurl → HjMinimizer`, now `→ LatticeOperators`, acyclic). Every call site below
(`open AdalyFormal.Balaban.LatticeOperators` is already in effect) resolves unqualified to
`LatticeOperators.coarseRestrictCLM_apply` unchanged. -/

/-- **THE SURJECTIVITY THEOREM, UNCONDITIONAL**: `coarseRestrictCLM L ell` hits every `B`. Needs
only `ell > 0`; no tiling-divisibility hypothesis. -/
theorem coarseRestrictCLM_surjective (L : PeriodicLatticeExtent) (ell : ℕ) (hell : 0 < ell) :
    Function.Surjective (coarseRestrictCLM L ell) := by
  intro B
  refine ⟨(bondEquiv L).symm (coarseLiftValue ell (coarseBondEquiv L ell B)), ?_⟩
  apply (coarseBondEquiv L ell).injective
  rw [coarseRestrictCLM_apply]
  simp only [LinearEquiv.apply_symm_apply]
  funext c
  exact coarseRestrict_coarseLiftValue ell hell (coarseBondEquiv L ell B) c

#print axioms coarseRestrictCLM_surjective

/-! ### §8b. A general, hypothesis-light reduction: `(∀ y1, ∃ x, T1 x=y1 ∧ T2 x=0)` ⟺ a
Submodule-sum equality. Pure linear algebra, no finite-dimensionality/continuity/inner-product
structure used — genuinely reusable anywhere else in this tree the same shape of question arises. -/

section GeneralReduction

variable {X Y1 Y2 : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y1] [Module ℝ Y1]
  [AddCommGroup Y2] [Module ℝ Y2]

/-- **(⇐) direction**: if the two kernels together span everything, the correction always exists.
Given `B`, pick ANY preimage `a` of `B` under the surjective `T1`, then split `a = k1+k2` along the
kernel decomposition (`Submodule.mem_sup`); `k2` is the desired correction. -/
theorem exists_particular_of_ker_sup_ker_eq_top (T1 : X →ₗ[ℝ] Y1) (T2 : X →ₗ[ℝ] Y2)
    (hT1 : Function.Surjective T1) (hsup : LinearMap.ker T1 ⊔ LinearMap.ker T2 = ⊤) :
    ∀ y1 : Y1, ∃ x : X, T1 x = y1 ∧ T2 x = 0 := by
  intro y1
  obtain ⟨a, ha⟩ := hT1 y1
  have hmem : a ∈ LinearMap.ker T1 ⊔ LinearMap.ker T2 := hsup ▸ Submodule.mem_top
  obtain ⟨k1, hk1, k2, hk2, hk⟩ := Submodule.mem_sup.mp hmem
  refine ⟨k2, ?_, LinearMap.mem_ker.mp hk2⟩
  have hsplit : T1 a = T1 k1 + T1 k2 := by rw [← hk, map_add]
  rw [LinearMap.mem_ker.mp hk1, zero_add] at hsplit
  rw [← hsplit, ha]

/-- **(⇒) direction**: if the correction always exists, the two kernels must together span
everything (no surjectivity hypothesis needed here — the existence property alone forces it,
since it already implies `T1` is surjective by dropping the second conjunct). -/
theorem ker_sup_ker_eq_top_of_exists_particular (T1 : X →ₗ[ℝ] Y1) (T2 : X →ₗ[ℝ] Y2)
    (hex : ∀ y1 : Y1, ∃ x : X, T1 x = y1 ∧ T2 x = 0) :
    LinearMap.ker T1 ⊔ LinearMap.ker T2 = ⊤ := by
  refine le_antisymm le_top ?_
  intro a _
  obtain ⟨x, hx1, hx2⟩ := hex (T1 a)
  have hmem1 : a - x ∈ LinearMap.ker T1 := by
    rw [LinearMap.mem_ker, map_sub, hx1, sub_self]
  have hmem2 : x ∈ LinearMap.ker T2 := LinearMap.mem_ker.mpr hx2
  have heq : a = (a - x) + x := by abel
  rw [heq]
  exact Submodule.mem_sup.mpr ⟨a - x, hmem1, x, hmem2, rfl⟩

/-- **The full equivalence**, given `T1` surjective. -/
theorem exists_particular_iff_ker_sup_ker_eq_top (T1 : X →ₗ[ℝ] Y1) (T2 : X →ₗ[ℝ] Y2)
    (hT1 : Function.Surjective T1) :
    (∀ y1 : Y1, ∃ x : X, T1 x = y1 ∧ T2 x = 0) ↔ LinearMap.ker T1 ⊔ LinearMap.ker T2 = ⊤ :=
  ⟨ker_sup_ker_eq_top_of_exists_particular T1 T2,
    exists_particular_of_ker_sup_ker_eq_top T1 T2 hT1⟩

#print axioms exists_particular_of_ker_sup_ker_eq_top
#print axioms ker_sup_ker_eq_top_of_exists_particular
#print axioms exists_particular_iff_ker_sup_ker_eq_top

end GeneralReduction

/-! ### §8c. Applying the reduction: `GaugeCorrectionComplete`, the ONE remaining named condition -/

/-- **The precise remaining condition** for `∀ B, ∃ A0` (both properties) to hold, GIVEN
`coarseRestrictCLM`'s already-UNCONDITIONAL surjectivity (§8a). Named in the same house style as
`KernelSubspace.positive_of_poincare`'s `hbound`: an explicit, checkable hypothesis, carried openly,
never silently assumed. -/
def GaugeCorrectionComplete {L : PeriodicLatticeExtent} (ell : ℕ) (levels : List (Level L)) :
    Prop :=
  LinearMap.ker (coarseRestrictCLM L ell).toLinearMap ⊔
    LinearMap.ker (((RProj levels).comp (gradCLM L).adjoint).toLinearMap) = ⊤

/-- **THE closure theorem, conditional on `GaugeCorrectionComplete`** — combines §8a's unconditional
surjectivity with §8b's general reduction. This is the SHARPEST form of the module's own named
residual "EXISTENCE of a particular solution `A0`": no longer an unproven blanket assumption
threading silently through every downstream theorem's hypotheses, but a SINGLE, clearly named,
checkable linear-algebra condition, stated exactly once. -/
theorem particularSolution_exists_of_gaugeCorrectionComplete {L : PeriodicLatticeExtent}
    (ell : ℕ) (hell : 0 < ell) (levels : List (Level L))
    (hgcc : GaugeCorrectionComplete ell levels) :
    ∀ B : CoarseBondSpace L ell, ∃ A0 : BondSpace L,
      coarseRestrictCLM L ell A0 = B ∧ RProj levels ((gradCLM L).adjoint A0) = 0 := by
  intro B
  obtain ⟨A0, h1, h2⟩ := exists_particular_of_ker_sup_ker_eq_top
    (coarseRestrictCLM L ell).toLinearMap (((RProj levels).comp (gradCLM L).adjoint).toLinearMap)
    (coarseRestrictCLM_surjective L ell hell) hgcc B
  exact ⟨A0, h1, h2⟩

/-- **The reverse direction, for completeness**: `GaugeCorrectionComplete` is not merely SUFFICIENT
but EXACTLY EQUIVALENT (given only `ell > 0`, via `coarseRestrictCLM_surjective`) to the existence
property the module needs — confirms nothing was lost narrowing to this one named hypothesis. -/
theorem gaugeCorrectionComplete_of_particularSolution_exists {L : PeriodicLatticeExtent}
    (ell : ℕ) (levels : List (Level L))
    (hex : ∀ B : CoarseBondSpace L ell, ∃ A0 : BondSpace L,
      coarseRestrictCLM L ell A0 = B ∧ RProj levels ((gradCLM L).adjoint A0) = 0) :
    GaugeCorrectionComplete ell levels :=
  ker_sup_ker_eq_top_of_exists_particular (coarseRestrictCLM L ell).toLinearMap
    (((RProj levels).comp (gradCLM L).adjoint).toLinearMap) hex

#print axioms particularSolution_exists_of_gaugeCorrectionComplete
#print axioms gaugeCorrectionComplete_of_particularSolution_exists

/-! ### §8d. A genuinely UNCONDITIONAL special case: `deltaKernelImage levels = ⊥` -/

/-- **`RProj` is the zero map whenever its target image is trivial** — immediate from
`RProj_apply_mem` (§1): `RProj levels v` always lands in `deltaKernelImage levels`, so if that
submodule is `⊥`, `RProj levels v = 0` for every `v`. -/
theorem RProj_eq_zero_of_deltaKernelImage_eq_bot {L : PeriodicLatticeExtent}
    (levels : List (Level L)) (h : deltaKernelImage levels = ⊥) :
    RProj levels = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hmem := RProj_apply_mem levels v
  rw [h, Submodule.mem_bot] at hmem
  simpa using hmem

/-- **`GaugeCorrectionComplete` holds UNCONDITIONALLY when `deltaKernelImage levels = ⊥`**: `T2`
becomes the zero map, whose kernel is already `⊤`, so the sum with anything is `⊤`. -/
theorem gaugeCorrectionComplete_of_deltaKernelImage_eq_bot {L : PeriodicLatticeExtent}
    (ell : ℕ) (levels : List (Level L)) (h : deltaKernelImage levels = ⊥) :
    GaugeCorrectionComplete ell levels := by
  unfold GaugeCorrectionComplete
  have hz : ((RProj levels).comp (gradCLM L).adjoint).toLinearMap = 0 := by
    ext v
    simp [RProj_eq_zero_of_deltaKernelImage_eq_bot levels h]
  rw [hz, LinearMap.ker_zero]
  exact sup_top_eq _

/-- **The fully UNCONDITIONAL corollary**: in the `deltaKernelImage levels = ⊥` case, existence of
`A0` holds outright, with NO named hypothesis at all beyond `ell > 0`. -/
theorem particularSolution_exists_of_deltaKernelImage_eq_bot {L : PeriodicLatticeExtent}
    (ell : ℕ) (hell : 0 < ell) (levels : List (Level L)) (h : deltaKernelImage levels = ⊥) :
    ∀ B : CoarseBondSpace L ell, ∃ A0 : BondSpace L,
      coarseRestrictCLM L ell A0 = B ∧ RProj levels ((gradCLM L).adjoint A0) = 0 :=
  particularSolution_exists_of_gaugeCorrectionComplete ell hell levels
    (gaugeCorrectionComplete_of_deltaKernelImage_eq_bot ell levels h)

#print axioms RProj_eq_zero_of_deltaKernelImage_eq_bot
#print axioms gaugeCorrectionComplete_of_deltaKernelImage_eq_bot
#print axioms particularSolution_exists_of_deltaKernelImage_eq_bot

/-! ## Named residual: a FULLY CONCRETE numeric witness on the shared witness lattice

`hjExtension_isMinimal` (general, unconditional) already proves no competitor beats
`hjExtension`'s value — a STRONGER guarantee than a single concrete spot-check would give. A
genuinely CONCRETE instantiation (`gaugeConstraintSubspace ell levels ≠ ⊥` on
`AdmissibleSubspace.witnessL`, with an EXPLICIT nonzero `v` and its curl computed by hand) was
attempted and NOT completed in this pass: it requires `ker(coarseRestrictCLM)` membership at
EVERY coarse bond (not merely the one hosting the witness's support), which needs the
block-DISJOINTNESS uniqueness lemmas already in `AdmissibleSubspace`
(`coarseLattice_unique`/`unique_multiple_in_window`) to rule out the witness's two nonzero fine
bonds leaking into a DIFFERENT coarse center's block-average — genuinely more work than a
`Finset.sum_eq_single`-style argument, and not attempted here (named, not silently dropped). The
sub-computation THAT WOULD BE NEEDED was partly worked out by hand in this lane's scratch work: a
config `+1` at `(kernelWitnessSiteA,0)`, `-1` at `(kernelWitnessSiteB,0)` (both
`KernelSubspace`-proved members of `blockOf witnessY witnessEll`) has ZERO block-average at
`(witnessY,0)` (by the SAME cancellation `KernelSubspace.kernelWitnessLam_block_sum_eq_zero` uses)
and NONZERO curl on `LatticeOperators.d4Plaquette` (`= 1`, since `shift_1(witnessY) =
kernelWitnessSiteB` collapses one of `curlValue`'s four terms to exactly the witness's own `-1`
value) — the arithmetic is done, only the disjointness-across-other-coarse-bonds step remains. -/

end AdalyFormal.Balaban.HjMinimizer
