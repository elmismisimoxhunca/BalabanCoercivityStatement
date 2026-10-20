/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantHjFaithful

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[DELTAK-SU2-ASSEMBLY]` — the CMP99b (3.156) `Δ_k` quadratic form, su(2) carrier, ZERO SOURCE

**GRADE-2 CORRECTION (2026-07-26, `compute/sol_deltak_readjudicate/SOL_VERDICT.md`, Sol page-image
read of CMP99b (3.128)/(3.156)/(3.155) + a Lean refutation).** The (3.156) `Δ_k` is
`⟨B,Δ_kB⟩ = ⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩`, and by (3.128)
`⟨A,G₁⁻¹A⟩ = ⟨A,Δ_π A⟩ − 2⟨HC,J⟩ + ‖RD*A‖² + a‖QA‖²` the leading Schur complement is
`⟨B,(QG₁Q*)⁻¹B⟩ = min_{QA=B}[curl part] + a‖B‖²` — it CARRIES the averaging mass `+a‖B‖²`. So the
`−a⟨B,B⟩` in (3.156) CANCELS IT EXACTLY: `Δ_k = min_{QA=B}[curl part]` (pure minimized curl, mass
gone). At `U=1` the source `J=0` and `Δ'=0` (p.392), so `Δ_k = deltaJ` (the pure minimized covariant
curl energy, `CovariantHjFaithful.deltaJQuadFormCovFaithful`).

**Consequence — the object `deltaKSuTwoForm a` below is MIS-NAMED for `a≠0`.** In this module
`deltaJQuadFormCovFaithful` is the MINIMIZED CURL `min curl` (= `Δ_k` at `U=1`), NOT the leading term
`⟨B,(QG₁Q*)⁻¹B⟩` (which is `deltaJ + a‖B‖²`). Hence `deltaKSuTwoForm a = deltaJ − a‖B‖²` is
`Δ_k − a‖B‖²`, i.e. `Δ_k` with the mass subtracted a SECOND, spurious time — it is NOT the (3.156)
`Δ_k` for `a≠0`. The FAITHFUL (3.156) `Δ_k` at `U=1` is `deltaKSuTwoForm 0 = deltaJQuadFormCovFaithful`
(§1 `deltaK_at_U1_eq_deltaJ`). The `deltaKSuTwoForm a` family is RETAINED (not deleted) as an
algebraic object `deltaJ − a‖B‖²`, but honestly RELABELED: it is NOT `Δ_k`.

## The two pieces (LAW-19 — reuse, do not rebuild)

* **`deltaJQuadFormCovFaithful` = `min curl` = `Δ_k` at `U=1`.** Commit `e9c0e8ee` verdict **(B)** and
  `compute/cstar_deltak_c_su2/DELTA_PI_ADJUDICATED.md` of CMP99b (3.118)–(3.120): on the gauge slice
  `{RD*A = 0}` every `Δ'_π` correction of (3.120) carries a `G'RD*A` factor and vanishes, so
  `Δ_π = bare Δ = D_U*D_U` there. The Schur minimum `min_{QA=B}` of the bare covariant curl is
  `‖D_U H_j^{cov}(A0)‖²` = `deltaJQuadFormCovFaithful`. Per SOL_VERDICT.md this minimized-curl object
  is exactly `Δ_k` at `U=1` (the mass has already cancelled), NOT the pre-cancellation leading term.
* **Mass term** `a⟨B,B⟩` with `B = Q_1(U)A0 = lineCoarseRestrictCovLM U ell A0`, `⟨B,B⟩` the coarse
  `L²` norm `CovariantHjFaithful.covCoarseBondInner B B`. Subtracting it from `deltaJ` (already
  mass-free) does NOT produce `Δ_k`; it produces the spurious `deltaJ − a‖B‖²`. `a : ℝ` is carried
  as a free parameter (value NOT asserted). The `a=0` slice `deltaKSuTwoForm 0 = deltaJ` is the one
  faithful to (3.156) at `U=1`.

## The source term is a NAMED RESIDUAL

`2⟨H₁D̃⁽²⁾(B),J⟩` needs the second-order covariant kernel `C⁽²⁾ = H₁D̃⁽²⁾` and the source `J` on
su(2) — NEITHER is built. At `J = 0` this term is `0`, and `deltaKSuTwoForm` is exactly `⟨B,Δ_kB⟩`
there. §3 carries a `src : ℝ` SLOT (`deltaKSuTwoFormWithSource`) that NAMES `⟨H₁D̃⁽²⁾(B),J⟩` as a
real number without building the operator, and proves that `src = 0` recovers `deltaKSuTwoForm`.
Building `H₁D̃⁽²⁾` / `J` on su(2) is the residual this module deliberately leaves open.

## What is proved here (all kernel-checked; `#print axioms` at each brick)

1. §1 `deltaKSuTwoForm a ell levels U A0` — the algebraic object `deltaJ − a·covCoarseBondInner B B`
   (NOT the (3.156) `Δ_k` for `a≠0`; see the grade-2 correction above);
   `deltaKSuTwoForm_zero_eq_deltaJ` and `deltaK_at_U1_eq_deltaJ` (the `a=0` slice IS the faithful
   (3.156) `Δ_k` at `U=1`, equal to `deltaJ`).
2. §2 the algebraic properties: vanishing at `A0=0`, vanishing on the whole gauge kernel `V`
   (BOTH terms vanish there — this is why the mass subtraction does not create a counterexample on
   `V`), the `a=0` `U`-dependence witness (transferred from `deltaJ`), and the **non-negativity-FAILS
   brick** `deltaKSuTwoForm_neg_of_curlfree_masspos` (wherever the leading curl energy vanishes but
   the coarse field is nonzero and `a>0`, the form is STRICTLY NEGATIVE).
3. §3 the source SLOT `deltaKSuTwoFormWithSource` and `_at_zero_source`, naming the residual.
4. §4 the coercivity TARGETs (`def : Prop`, NOT proved, no `sorry`) — now **marked REFUTED as
   written**: the unrestricted `∀ A0` shell is FALSE (`U1LeadingCoercivity.
   faithfulCovCoercivityTarget_trivialU_witness_false` refutes the `a=0` member; `a≥0` is strictly
   worse), and the outright refutations of `DeltaKSuTwoCoercivityTarget`/`…Uniform` live downstream in
   `CoercivityTargetsCorrected.lean`. The domain-restricted (gauge-fixed) CORRECTED target and its
   reduction to `GaugeFixedCurlCoercivity`/(2.128) also live in `CoercivityTargetsCorrected.lean`. The
   algebraic **bridge** `deltaKSuTwoCoercivity_iff_shifted` (`γ₀·‖B‖² ≤ deltaJ − a‖B‖²` ↔
   `(γ₀+a)·‖B‖² ≤ deltaJ`) is retained: it shows the spurious `deltaKSuTwoForm a` coercivity is EXACTLY
   the (refuted) leading `deltaJ` coercivity with a shifted constant — i.e. subtracting the mass makes
   the target STRICTLY HARDER, never a repair.

## Honesty / scope

* **This is an ISLAND.** Nothing here is wired to `coerc_u_main` or any consumed spine declaration.
* **`deltaKSuTwoForm a` (a≠0) is NOT `Δ_k`.** Per the grade-2 correction, the faithful (3.156) `Δ_k`
  at `U=1` is `deltaKSuTwoForm 0 = deltaJ`. The `a≠0` family is a retained algebraic object only.
* **NOT non-negative.** With the `−a⟨B,B⟩` subtraction `deltaKSuTwoForm` need NOT be `≥ 0`; §2 proves
  a strictly-negative regime explicitly. We assert NO coercivity, NO wiring. Every coercivity target
  here is REFUTED as written (§4).
* **Zero source only.** The full (3.156) form at `J≠0` carries `−2⟨H₁D̃⁽²⁾(B),J⟩`; that operator is
  UNBUILT (§3 residual).
* **Compatibility (`CompatibleExtent`).** `covCoarseBondInner B B` equals the true `‖B‖²` only on
  COMPATIBLE full blocks (`LineIntegralCovariant.lean` §1 grade-2 caveat; torus `blockOf` truncation
  lesson). The §2 algebraic bricks (reduction, vanishing, negativity) are purely algebraic and hold
  for ALL `ell`; they assert NO faithfulness. The ONE place faithfulness is load-bearing — the
  coercivity target (§4) — carries `CompatibleExtent L ell` explicitly.
-/

namespace AdalyFormal.Balaban.DeltaKSuTwoAssembly

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.KernelSubspace
  AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.Balaban.LineIntegralCovariant
  AdalyFormal.Balaban.Q1Real
  AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the algebraic form `deltaJ − a‖B‖²`, and the faithful `Δ_k = deltaJ` identity at `U=1` -/

/-- **The algebraic object `deltaJ − a·⟨B,B⟩`, su(2) carrier — NOT the (3.156) `Δ_k` for `a≠0`.**
`deltaJQuadFormCovFaithful` is the MINIMIZED covariant curl `min curl` (`= Δ_k` at `U=1`, mass
already cancelled — see the grade-2 correction, `SOL_VERDICT.md`), and the mass term is
`a·covCoarseBondInner B B`, `B = Q_1(U)A0 = lineCoarseRestrictCovLM U ell A0`. Because the (3.156)
`Δ_k` mass CANCELS against the leading Schur mass, subtracting `a‖B‖²` from the already-mass-free
`deltaJ` does NOT give `Δ_k`; it gives the spurious `Δ_k − a‖B‖²`. **The faithful (3.156) `Δ_k` at
`U=1` is the `a=0` slice `deltaKSuTwoForm 0 = deltaJ`** (`deltaK_at_U1_eq_deltaJ`). `a : ℝ` free
(value NOT asserted). NOT claimed nonneg — the `−a` makes it indefinite (§2).

**[CSTAR-LEVEL-MISMATCH] — LEVEL INDEX OF `A0`, RECORDED (denotation-dictionary finding, not
re-litigated here).** `A0 : Bond L → SuTwo` is a field on this tree's SINGLE fine/unit bond level.
CMP99b p.428 (3.156)'s `Δ_k` is a UNIT-lattice (`Λ`) form with the fine level already integrated
out — `compute/denotation_dict/DENOTATION_DICT.tsv` row `delta_k_unit_p428_3156`
(`src_level = tgt_level = unit (Lambda)`, sector `bond`), whose dictionary verdict is `MISMATCH`
and whose note names THIS declaration ("`deltaKSuTwoForm`'s argument is `A0 : Bond L -> SuTwo`, a
field on the tree's SINGLE fine/unit level") together with its ingredient
`CovariantHjFaithful.deltaJQuadFormCovFaithful`. The CMP96 counterpart is row `delta96_j_unit_2118`
((2.118) `Δ_j`, unit→unit). The typed separation that makes the collapse unstateable is
`AdalyFormal.Balaban.CStarLevelCorrected.LevelSplit` (`LevelSplit.ne`); it is NOT used here.
Nothing in this declaration or its proofs is changed by this note. -/
noncomputable def deltaKSuTwoForm (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : ℝ :=
  deltaJQuadFormCovFaithful ell levels U A0
    - a * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0)

/-- **Mass-free reduction**: at `a=0` `deltaKSuTwoForm` is EXACTLY `deltaJQuadFormCovFaithful` — the
faithful (3.156) `Δ_k` at `U=1` (see `deltaK_at_U1_eq_deltaJ`; the mass has cancelled). -/
theorem deltaKSuTwoForm_zero_eq_deltaJ (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    deltaKSuTwoForm 0 ell levels U A0 = deltaJQuadFormCovFaithful ell levels U A0 := by
  unfold deltaKSuTwoForm
  ring

#print axioms deltaKSuTwoForm_zero_eq_deltaJ

/-- **THE FAITHFUL (3.156) `Δ_k` AT `U=1` IS `deltaJ`.** By `SOL_VERDICT.md`: (3.128) gives the
leading Schur complement `⟨B,(QG₁Q*)⁻¹B⟩ = min_{QA=B}[curl] + a‖B‖²` and (3.156) subtracts exactly
`a⟨B,B⟩`, so the averaging mass cancels and `Δ_k = min_{QA=B}[curl]`; at `U=1` the source `J=0` and
`Δ'=0` (p.392), leaving `Δ_k = deltaJ` (pure minimized covariant curl). In this module that is the
`a=0` slice: `deltaKSuTwoForm 0 ell levels U A0 = deltaJQuadFormCovFaithful ell levels U A0`. This is
the CORRECTED identification — for `a≠0`, `deltaKSuTwoForm a ≠ Δ_k` (it double-subtracts the mass).

**Type-vs-semantics disclosure.** The kernel-checked CONTENT here is the `a=0` algebra
`deltaKSuTwoForm 0 = deltaJ`, which holds for a GENERIC `U` (the type carries no `U=1` binder; the
proof is `deltaKSuTwoForm_zero_eq_deltaJ`). The "at `U=1` this `= Δ_k`" claim is the EXTERNAL Sol
page-image adjudication (mass cancellation + `J=0`, `Δ'=0`); it is NOT itself kernel-checkable because
Balaban's `Δ_k` has no Lean definition in this tree. Cite the docstring, not the name alone. -/
theorem deltaK_at_U1_eq_deltaJ (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    deltaKSuTwoForm 0 ell levels U A0 = deltaJQuadFormCovFaithful ell levels U A0 :=
  deltaKSuTwoForm_zero_eq_deltaJ ell levels U A0

#print axioms deltaK_at_U1_eq_deltaJ

/-! ## §2 — algebraic properties (purely algebraic; hold for ALL `ell`, assert NO faithfulness) -/

/-- **Vanishing on the gauge kernel `V`.** For `A0 ∈ gaugeConstraintSubspaceCovFaithful` BOTH the
leading term (`deltaJQuadFormCovFaithful_eq_zero_of_mem_V`) and the coarse field
`B = Q_k(U)A0 = 0` (`covCoarseBondInner_restrict_eq_zero_of_mem_V`) vanish, so
`deltaKSuTwoForm a ... A0 = 0` for EVERY `a`. This is exactly why the mass subtraction does not
manufacture a coercivity counterexample on `V` (the discipline-#5 point): the SAME `A0` that would
have made a curl-energy RHS nonzero makes both `Δ_k` terms zero. -/
theorem deltaKSuTwoForm_eq_zero_of_mem_V (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (hA0 : A0 ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    deltaKSuTwoForm a ell levels U A0 = 0 := by
  unfold deltaKSuTwoForm
  rw [deltaJQuadFormCovFaithful_eq_zero_of_mem_V ell levels U A0 hA0,
    covCoarseBondInner_restrict_eq_zero_of_mem_V ell levels U A0 hA0]
  ring

/-- **Vanishing at the zero field** (`0 ∈ V`). -/
theorem deltaKSuTwoForm_zero_field (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection] :
    deltaKSuTwoForm a ell levels U (0 : Bond L → SuTwo) = 0 :=
  deltaKSuTwoForm_eq_zero_of_mem_V a ell levels U 0 (Submodule.zero_mem _)

#print axioms deltaKSuTwoForm_eq_zero_of_mem_V
#print axioms deltaKSuTwoForm_zero_field

/-- **NON-NEGATIVITY FAILS — the honest brick.** Wherever the leading curl energy vanishes
(`deltaJ = 0`) but the coarse field is nonzero (`⟨B,B⟩ > 0`) with a positive mass `a > 0`, the
(3.156) `Δ_k` form is STRICTLY NEGATIVE. This is why `deltaKSuTwoForm` is NOT claimed `≥ 0`: the
`−a⟨B,B⟩` subtraction makes it genuinely indefinite. (At `ell=1` `Q_1(U)` is injective so `V=⊥`;
any `A0≠0` there has `⟨B,B⟩>0`, and any curl-free such `A0` realizes this negative regime.) -/
theorem deltaKSuTwoForm_neg_of_curlfree_masspos (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo)
    (hderiv : deltaJQuadFormCovFaithful ell levels U A0 = 0)
    (hmass : 0 < covCoarseBondInner (lineCoarseRestrictCovLM U ell A0)
      (lineCoarseRestrictCovLM U ell A0))
    (ha : 0 < a) :
    deltaKSuTwoForm a ell levels U A0 < 0 := by
  unfold deltaKSuTwoForm
  rw [hderiv]
  have : 0 < a * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0)
      (lineCoarseRestrictCovLM U ell A0) := mul_pos ha hmass
  linarith

#print axioms deltaKSuTwoForm_neg_of_curlfree_masspos

/-- **`a=0` `U`-dependence witness.** At `a=0` the form is `deltaJQuadFormCovFaithful` (= the faithful
`Δ_k` at `U=1`), so it inherits the headline `U`-dependence of `deltaJQuadFormCovFaithful` (values
`0` vs `4` at the fixed
`(ell,levels,U,A0)` witnesses; `deltaJQuadFormCovFaithful_genuinely_U_dependent`). The `Δ_k` form is
genuinely `U`-dependent, not a `U`-constant. -/
theorem deltaKSuTwoForm_zero_mass_genuinely_U_dependent :
    deltaKSuTwoForm 0 1 ([] : List (KernelSubspace.Level AdmissibleSubspace.witnessL))
        myTrivialU myWitnessConfig ≠
      deltaKSuTwoForm 0 1 ([] : List (KernelSubspace.Level AdmissibleSubspace.witnessL))
        witnessU myWitnessConfig := by
  rw [deltaKSuTwoForm_zero_eq_deltaJ, deltaKSuTwoForm_zero_eq_deltaJ]
  exact deltaJQuadFormCovFaithful_genuinely_U_dependent

#print axioms deltaKSuTwoForm_zero_mass_genuinely_U_dependent

/-! ## §3 — the NAMED source residual `−2⟨H₁D̃⁽²⁾(B),J⟩` (the `J≠0` re-entry) -/

/-- **The full (3.156) form with the source slot NAMED.** `src : ℝ` stands for the scalar
`⟨H₁D̃⁽²⁾(B), J⟩` — the operator `H₁D̃⁽²⁾ = C⁽²⁾` and the su(2) source `J` are NOT built (residual);
we carry only the resulting real number so the assembly's shape is explicit:
`⟨B,Δ_kB⟩ = deltaKSuTwoForm − 2·src`. This does NOT construct the source term; it names where it
enters. -/
noncomputable def deltaKSuTwoFormWithSource (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (src : ℝ) : ℝ :=
  deltaKSuTwoForm a ell levels U A0 - 2 * src

/-- **At zero source `J=0` (`src=0`) the full form is exactly `deltaKSuTwoForm`.** At `J=0` the source
term `−2⟨H₁D̃⁽²⁾,J⟩` vanishes; the faithful (3.156) `Δ_k` at `U=1` is then the `a=0` slice
`deltaKSuTwoForm 0 = deltaJ` (the mass having cancelled — grade-2 correction). -/
theorem deltaKSuTwoFormWithSource_at_zero_source (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    deltaKSuTwoFormWithSource a ell levels U A0 0 = deltaKSuTwoForm a ell levels U A0 := by
  unfold deltaKSuTwoFormWithSource
  ring

#print axioms deltaKSuTwoFormWithSource_at_zero_source

/-! ## §4 — the coercivity TARGETs (`def : Prop`, no `sorry`/`axiom`) — **REFUTED as written** -/

/-- **THE UNRESTRICTED `deltaKSuTwoForm` COERCIVITY TARGET — REFUTED as written (not open).** Bounds
the spurious `deltaKSuTwoForm a = deltaJ − a‖B‖²` below by `γ₀‖B‖²` over ALL `A0`. By
`deltaKSuTwoCoercivity_iff_shifted` this is EXACTLY the leading `deltaJ ≥ (γ₀+a)‖B‖²`, i.e.
`FaithfulCovCoercivityTarget` at the shifted constant — which is FALSE for the constant field at `U=1`
(`U1LeadingCoercivity.faithfulCovCoercivityTarget_trivialU_witness_false`: `deltaJ(const)=0` while
`‖Q₁(const)‖²>0`); the `−a‖B‖²` (`a≥0`) only makes it worse. The outright refutation of this `def` at
the witness is `CoercivityTargetsCorrected.deltaKSuTwoCoercivityTarget_witness_false`. `def : Prop`
only: NOT asserted, NO proof, NOT wired. The CORRECT object is the domain-restricted target in
`CoercivityTargetsCorrected.lean`. -/
def DeltaKSuTwoCoercivityTarget (a : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection] : Prop :=
  CompatibleExtent L ell →
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ A0 : Bond L → SuTwo,
      γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0)
        ≤ deltaKSuTwoForm a ell levels U A0

/-- **THE k-UNIFORM `deltaKSuTwoForm` COERCIVITY TARGET — REFUTED as written (`0 ≤ a`).** `∃ γ₀ > 0`
quantified OUTSIDE `L, ell, levels, U`. Its witness member (`witnessL, witnessEll, [], trivialU`) is
`DeltaKSuTwoCoercivityTarget a witnessEll [] trivialU`, refuted above; hence the uniform form is
outright FALSE for `0 ≤ a` (`CoercivityTargetsCorrected.deltaKSuTwoCoercivityTargetUniform_false`).
Bare `def : Prop`: NOT asserted, NO proof, NOT wired. Retained only to carry its refutation; it is
NOT the genuine open content (that is the domain-restricted target in the corrected module). -/
def DeltaKSuTwoCoercivityTargetUniform (a : ℝ) : Prop :=
  ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (L : PeriodicLatticeExtent) (ell : ℕ) (levels : List (KernelSubspace.Level L))
      (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
      [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
      [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection],
      CompatibleExtent L ell → RegularBackground U → ∀ A0 : Bond L → SuTwo,
        γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0)
          ≤ deltaKSuTwoForm a ell levels U A0

/-- **THE BRIDGE — the mass subtraction is a CONSTANT SHIFT that makes the target HARDER.** For any
`γ₀`, the inequality `γ₀·‖B‖² ≤ deltaKSuTwoForm a = deltaJ − a‖B‖²` is EQUIVALENT to
`(γ₀+a)·‖B‖² ≤ deltaJ`. So the spurious `deltaKSuTwoForm a` coercivity at `γ₀` is exactly the
LEADING (`deltaJ`) coercivity at the LARGER constant `γ₀+a` — subtracting the mass RAISES the
required constant, it never repairs the (refuted) leading target. This is precisely why
`deltaKSuTwoForm a` is not the correct coercive object: the faithful `Δ_k` is `deltaJ` (`a=0`).
Purely algebraic; holds for all `ell`, all `A0`. -/
theorem deltaKSuTwoCoercivity_iff_shifted (a γ₀ : ℝ) (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0) (lineCoarseRestrictCovLM U ell A0)
        ≤ deltaKSuTwoForm a ell levels U A0
      ↔ (γ₀ + a) * covCoarseBondInner (lineCoarseRestrictCovLM U ell A0)
          (lineCoarseRestrictCovLM U ell A0)
        ≤ deltaJQuadFormCovFaithful ell levels U A0 := by
  unfold deltaKSuTwoForm
  rw [add_mul]
  constructor <;> intro h <;> linarith

#print axioms deltaKSuTwoCoercivity_iff_shifted

end AdalyFormal.Balaban.DeltaKSuTwoAssembly
