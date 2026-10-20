/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantOperators
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

/-!
# The real inner product on `𝔰𝔲(2)` — Bałaban CMP99b pp.390-392

Builds `InnerProductSpace ℝ suTwo`, the residual named (and explicitly NOT attempted) by
`Balaban/CovariantOperators.lean`'s own scope note. `suTwo` is REUSED from that file, not
redefined (LAW-19).

## The normalization, and where it comes from (this is not a free choice)

Two sentences of CMP99b fix the constant. Both are **image-verified at 300 dpi** from
`compute/balaban_su2_papers/balaban_CMP99_1985_propagators_backgroundfield.pdf`
(sha256 `39f8033b35838c7bdd14f97c7fb1edb0b35d4190b8b88f31d19d12a72d542861`), pdf pages 3 and 4 =
printed pages 391 and 392 (offset 388, `corpus/tools/page_offsets.json`, `constant_verified`):

* **printed p.391, last three lines (VERBATIM):** "In the sequel we will frequently use adjoint
  operators to derivatives `D`. The adjoints are taken with respect to natural `L²` scalar products
  for functions with values in `N × N` **hermitian** matrices. The inner product for these matrices
  is defined"
* **printed p.392, first line (VERBATIM):** "by `X · Y = tr XY`. **Let us recall that the trace is
  normalized, i.e., `tr 1 = 1`.**"

So Bałaban's carrier is the HERMITIAN presentation of the Lie algebra (consistent with his own
`U' = exp(iηA)`, p.390 and eq. (3.12)), and his `tr` is the NORMALIZED trace `tr = N⁻¹ Tr`. For
`N = 2`, `tr M = ½ Tr M`, where `Tr` is the ordinary matrix trace (Mathlib's `Matrix.trace`).

This tree's carrier `suTwo` is the ANTI-hermitian presentation (`Xᴴ = -X`, traceless), fixed by
`CovariantOperators.lean`. The two presentations are identified by the standard `ℝ`-linear
isomorphism `φ : X ↦ i·X` (anti-hermitian `↦` hermitian). Transporting Bałaban's form along `φ`:

`⟪X, Y⟫ := φ(X) · φ(Y) = tr((iX)(iY)) = -tr(XY) = -½ Tr(X·Y)`.

That is the definition below, `hsInner`. **Named, visible convention (not silent):** the `-½` is
`(-1)` from the `φ`-transport times `(½)` from Bałaban's `tr 1 = 1`. Multiply either factor and the
form stops matching the source; multiply the whole thing by `2` and `hsInner_e1_e1`/`hsInner_e2_e2`/
`hsInner_e3_e3` below stop reading `1` on the Pauli generators (§7's `hsInner_ne_unnormalized`
makes exactly that failure a theorem).

**Independent second source route to the SAME constant** (CMP99b printed p.390, VERBATIM): "in
this paper a norm `|X|` of a `N × N` matrix means the Hilbert-Schmidt norm: `|X|² = tr X*X`". With
the same normalized `tr`, `|X|² = ½ Tr(XᴴX) = ½ Σᵢⱼ|Xᵢⱼ|²`, and `hsInner_self_eq_sumNormSq` below
proves `⟪X,X⟫ = ½ Σᵢⱼ|Xᵢⱼ|²` — the two source sentences agree, and the theorem is the check.

## Correction to `compute/lattice_operator_audit/OPERATOR_AUDIT.md` §2.2/§2.4 (S75, recorded here)

That audit reports the convention as "the Hilbert-Schmidt inner product on matrices, `X·Y = tr XY`
(p.392, image-confirmed)" and pairs it with the "traceless anti-Hermitian" carrier. Taken literally
on THIS tree's anti-hermitian carrier, `X·Y = tr XY` is NEGATIVE definite (`tr X² = -½Σ|Xᵢⱼ|² < 0`
for `X ≠ 0` skew-hermitian, proved below as `trace_sq_neg_of_mem`), hence not an inner product at
all. The audit also omits the `tr 1 = 1` sentence, which is on the same printed line as the formula
it quotes. Net: a SIGN and a FACTOR OF 2. Both are corrected here at the source; the audit file
itself is read-only for this lane and is NOT edited (see `formal/AdalyFormal/SUTWO_INNER.md`).

## Instance hazard, stated openly

`Matrix (Fin 2) (Fin 2) ℂ` has no default Mathlib norm; `CovariantOperators.lean` activates the
scoped `L²`-operator norm and thereby (via `Submodule.normedAddCommGroup`) a norm on `SuTwo`
*inside that file's scope*. Measured (`#synth NormedAddCommGroup ↥SuTwo` in an importing file with
no scoped norms opened): **fails to synthesize** — so the instances below are the first and only
norm on `SuTwo` reachable from an ordinary import. A file that opens `Matrix.Norms.L2Operator`
AND imports this module gets two. They are equal as functions (on `𝔰𝔲(2)` every element is normal
with eigenvalues `±iλ`, so the operator norm is `|λ|` and `‖X‖² = -½Tr X² = |λ|²`) but not
definitionally so; ~~the Lean proof of that agreement is named as a residual and NOT claimed
here.~~

**⚠ SUPERSEDED (S75, 2026-08-09, `compute/norm_diamond_install/`) — the struck clause is now FALSE
and is retained only so the record shows when the residual was closed.** The agreement IS proved
here, in §4e below, on all of `𝔰𝔲(2)` and not merely at `suTwoWitness`: `fibre_norms_agree`
(the two norm FUNCTIONS are equal at every `X`) and `fibre_norm_instances_eq` (stronger — the two
`Norm ↥SuTwo` STRUCTURES are the same term). The route is not the eigenvalue argument quoted above
but its matrix form: `conjTranspose_mul_self_eq_diagonal` shows `Xᴴ X` is a SCALAR matrix with
scalar `hsInner X X` for traceless skew-hermitian `2×2`, after which the C*-identity
`‖AᴴA‖ = ‖A‖‖A‖` and `Matrix.l2_opNorm_diagonal` finish it with no spectral theory.

This also closes, by name, the scope `HoleHunt/ConventionPins.lean` §2.3b left open ("agreement AT
`suTwoWitness`, not a proof that the two norms agree on all of `𝔰𝔲(2)`") and supplies the
"additional (unbuilt) machinery to compare the two norm FUNCTIONS pointwise" that
`Balaban/CoercivityCov.lean` §0 names — both of those files are outside this pass's write scope and
still carry the old wording (reported, not edited: LAW-4).
-/

namespace AdalyFormal.Balaban.SuTwoInner

open Matrix Complex AdalyFormal.Balaban.CovariantOperators

/-! ## §1 — the form itself -/

/-- **Bałaban's matrix inner product, transported to the anti-hermitian presentation**:
`⟪X,Y⟫ = -½ Tr(XY)`. See the module docstring for the two image-verified source sentences that fix
both the sign and the `½`. `Matrix.trace` here is the ORDINARY (unnormalized) trace. -/
noncomputable def hsInner (X Y : SuTwo) : ℝ :=
  -(1 / 2 : ℝ) *
    (Matrix.trace ((X : Matrix (Fin 2) (Fin 2) ℂ) * (Y : Matrix (Fin 2) (Fin 2) ℂ))).re

theorem hsInner_def (X Y : SuTwo) :
    hsInner X Y =
      -(1 / 2 : ℝ) *
        (Matrix.trace ((X : Matrix (Fin 2) (Fin 2) ℂ) * (Y : Matrix (Fin 2) (Fin 2) ℂ))).re := rfl

/-! ### §1.1 — the two entrywise computations the whole file rests on -/

/-- The `2×2` trace-of-a-product, fully expanded. Kept as a named lemma so every later computation
goes through the SAME expansion (no second, silently different, unfolding). -/
theorem trace_mul_fin2 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (A * B) = A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **The skew-hermitian entry relation**: `Xᴴ = -X` says exactly `X j i = -conj(X i j)`. -/
theorem entry_skew {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = -X) (i j : Fin 2) :
    X j i = -(starRingEnd ℂ) (X i j) := by
  have h : (starRingEnd ℂ) (X j i) = -X i j := by
    have h0 := congrFun (congrFun hX i) j
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using h0
  have h1 := congrArg (starRingEnd ℂ) h
  simpa using h1

/-- Consequence: on a skew-hermitian matrix each diagonal contribution to `Tr(X·X)` is
`-|Xᵢⱼ|²`. This is where positivity is really born. -/
theorem entry_prod_skew {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = -X) (i j : Fin 2) :
    X i j * X j i = -(Complex.normSq (X i j) : ℂ) := by
  rw [entry_skew hX i j, mul_neg, Complex.mul_conj]

/-! ## §2 — positive definiteness (the real work) -/

/-- **`⟪X,X⟫ = ½ Σᵢⱼ |Xᵢⱼ|²`** — the independent second computational path to the same number,
and the one that makes positivity and definiteness immediate. This is also the theorem that ties
the p.392 sentence (`X·Y = tr XY`, `tr 1 = 1`) to the p.390 sentence (`|X|² = tr X*X`): both give
`½Σ|Xᵢⱼ|²` on this carrier. -/
theorem hsInner_self_eq_sumNormSq (X : SuTwo) :
    hsInner X X =
      (1 / 2 : ℝ) *
        (Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
          Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) +
          Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
          Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) := by
  obtain ⟨hX1, -⟩ := X.2
  rw [hsInner_def, trace_mul_fin2, entry_prod_skew hX1 0 0, entry_prod_skew hX1 0 1,
    entry_prod_skew hX1 1 0, entry_prod_skew hX1 1 1]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring

theorem hsInner_self_nonneg (X : SuTwo) : 0 ≤ hsInner X X := by
  rw [hsInner_self_eq_sumNormSq]
  have h1 := Complex.normSq_nonneg ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
  have h2 := Complex.normSq_nonneg ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1)
  have h3 := Complex.normSq_nonneg ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
  have h4 := Complex.normSq_nonneg ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
  linarith

/-- **Definiteness.** -/
theorem hsInner_self_eq_zero {X : SuTwo} (h : hsInner X X = 0) : X = 0 := by
  rw [hsInner_self_eq_sumNormSq] at h
  have h1 := Complex.normSq_nonneg ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
  have h2 := Complex.normSq_nonneg ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1)
  have h3 := Complex.normSq_nonneg ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
  have h4 := Complex.normSq_nonneg ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
  have e00 : Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = 0 := by linarith
  have e01 : Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 0 := by linarith
  have e10 : Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = 0 := by linarith
  have e11 : Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 1) = 0 := by linarith
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Submodule.coe_zero, Matrix.zero_apply]
  · exact Complex.normSq_eq_zero.mp e00
  · exact Complex.normSq_eq_zero.mp e01
  · exact Complex.normSq_eq_zero.mp e10
  · exact Complex.normSq_eq_zero.mp e11

/-- **`Tr(X²) < 0` for `X ≠ 0` skew-hermitian** — the fact quoted in the module docstring's
correction to `OPERATOR_AUDIT.md`: the audit's literal `X·Y = tr XY` is negative definite on this
carrier, so the sign in `hsInner` is forced, not chosen. -/
theorem trace_sq_neg_of_mem {X : SuTwo} (hX : X ≠ 0) :
    (Matrix.trace ((X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ))).re < 0 := by
  have hpos : 0 < hsInner X X := by
    rcases lt_or_eq_of_le (hsInner_self_nonneg X) with h | h
    · exact h
    · exact absurd (hsInner_self_eq_zero h.symm) hX
  rw [hsInner_def] at hpos
  linarith

/-! ## §3 — bilinearity and symmetry -/

theorem hsInner_symm (X Y : SuTwo) : hsInner X Y = hsInner Y X := by
  rw [hsInner_def, hsInner_def, Matrix.trace_mul_comm]

theorem hsInner_add_left (X Y Z : SuTwo) :
    hsInner (X + Y) Z = hsInner X Z + hsInner Y Z := by
  simp only [hsInner_def, Submodule.coe_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  ring

theorem hsInner_smul_left (X Y : SuTwo) (r : ℝ) :
    hsInner (r • X) Y = r * hsInner X Y := by
  simp only [hsInner_def, SetLike.val_smul, Matrix.smul_mul, Matrix.trace_smul,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## §4 — the `InnerProductSpace ℝ SuTwo` instance -/

/-- The `PreInnerProductSpace.Core` assembled from §1-§3 (everything but definiteness). -/
@[implicit_reducible]
noncomputable def suTwoPreCore : PreInnerProductSpace.Core ℝ SuTwo where
  inner := hsInner
  conj_inner_symm X Y := by
    simp only [starRingEnd_apply, star_trivial]
    exact hsInner_symm Y X
  re_inner_nonneg X := hsInner_self_nonneg X
  add_left X Y Z := hsInner_add_left X Y Z
  smul_left X Y r := by
    simp only [starRingEnd_apply, star_trivial]
    exact hsInner_smul_left X Y r

/-- The full `InnerProductSpace.Core`, adding definiteness. Mathlib's `ofCore` machinery
(Cauchy-Schwarz, the induced norm, the triangle inequality) is REUSED, not rebuilt (LAW-19). -/
@[implicit_reducible]
noncomputable def suTwoCore : InnerProductSpace.Core ℝ SuTwo where
  __ := suTwoPreCore
  definite _ h := hsInner_self_eq_zero h

/-! ### §4a — finite-dimensionality

Moved UP from §9 (where it originally lived) because §4b's diamond repair consumes it. Nothing
about it needs a norm: `SuTwo` is a `Submodule ℝ` of the finite-dimensional real vector space
`Matrix (Fin 2) (Fin 2) ℂ`. -/

instance instFiniteDimensionalSuTwo : FiniteDimensional ℝ SuTwo := by
  infer_instance

/-! ### §4b — THE UNIFORMITY DIAMOND, CLOSED BY CONSTRUCTION

**What was measured, and what it broke.** `↥SuTwo` is a subtype of `Matrix (Fin 2) (Fin 2) ℂ`, so
typeclass search finds `instTopologicalSpaceSubtype` / `instUniformSpaceSubtype` for it *before any
norm exists*. The norm built here from `hsInner` carries its OWN metric uniformity. Measured with
`#synth` and `example … := rfl` on the pre-repair file (`compute/sutwo_diamond/REPORT.md` §BEFORE):

```
#synth TopologicalSpace SuTwo   →  instTopologicalSpaceSubtype
#synth NormedAddCommGroup SuTwo →  instNormedAddCommGroupSuTwo
(inferInstance : TopologicalSpace SuTwo)
  = (inferInstance : NormedAddCommGroup SuTwo).toUniformSpace.toTopologicalSpace   -- rfl FAILS
(PiLp.topologicalSpace 2 fun _ : Fin 3 => SuTwo)
  = (PiLp.normedAddCommGroup (α := fun _ : Fin 3 => SuTwo)).toUniformSpace.toTopologicalSpace
                                                                                  -- rfl FAILS
```

`PiLp` propagates the fibre mismatch verbatim, which is why no `ContinuousLinearMap` over
`BondFnL2 L = PiLp 2 (fun _ : Bond L => SuTwo)` would unify with the one an abstract
`[NormedAddCommGroup H]` field type produces (`CoercivityRegular.lean` §8's nine-route table).

**The repair, and why THIS one.** `MetricSpace.replaceUniformity` — Mathlib's designated tool for
exactly this "forgetful inheritance" situation (`Mathlib/Topology/MetricSpace/Defs.lean`). It takes
the metric space built from `hsInner` and *overwrites its `toUniformSpace` field with the ambient
`instUniformSpaceSubtype`*, discharging the obligation that the two uniformity FILTERS agree — which
is precisely the propositional equality §9b already proves. The alternative (declare new
`TopologicalSpace`/`UniformSpace SuTwo` instances derived from the norm) was rejected: it would
register a SECOND, competing instance for a class that already has one, i.e. it would create the
diamond rather than remove it, and would displace an instance `instCompleteSpaceSuTwo` (§9b) and
every ambient-topology consumer already depends on.

**The norm is NOT touched.** `replaceUniformity` rewrites only the uniformity field;
`norm_unchanged_by_uniformity_repair` (§4c) is the `rfl` proof that `‖·‖` is the same FUNCTION
before and after, and `inner_eq_hsInner`/`inner_eq_trace` still hold by `rfl`. Bałaban's
`tr 1 = 1` normalization (`-½ Tr(XY)`, module docstring) is unaffected. -/

/-- **The raw normed group straight off the core** — the pre-repair object, kept as a NAMED `def`
(not an instance) so the repair below is a visible, checkable step rather than a silent rewrite.
Its uniformity is the metric one; `instNormedAddCommGroupSuTwo` replaces exactly that field. -/
@[implicit_reducible]
noncomputable def suTwoNormedRaw : NormedAddCommGroup SuTwo :=
  suTwoCore.toNormedAddCommGroup

section RawDiamond

attribute [local instance] suTwoNormedRaw

/-- The inner-product structure over the RAW normed group. Local-instance only; it exists so the
two continuity arguments below have `NormedSpace ℝ SuTwo` (hence `ContinuousSMul`) available on
the norm side. -/
@[implicit_reducible]
noncomputable def suTwoInnerRaw : InnerProductSpace ℝ SuTwo :=
  InnerProductSpace.ofCore suTwoPreCore

attribute [local instance] suTwoInnerRaw

/-- **Identity, ambient topology → raw-norm topology, is continuous.** A linear map out of a
finite-dimensional space into a Hausdorff topological vector space is automatically continuous
(`LinearMap.continuous_of_finiteDimensional`) — the general theorem underlying "all norms on a
finite-dimensional space are equivalent", applied here to ambient-vs-norm. -/
theorem continuous_id_ambient_to_rawNorm :
    @Continuous SuTwo SuTwo instTopologicalSpaceSubtype
      (@UniformSpace.toTopologicalSpace SuTwo PseudoMetricSpace.toUniformSpace)
      id :=
  @LinearMap.continuous_of_finiteDimensional ℝ _ SuTwo _ _
    instTopologicalSpaceSubtype _ _
    SuTwo _ _ (@UniformSpace.toTopologicalSpace SuTwo PseudoMetricSpace.toUniformSpace) _ _
    _ _ _
    (LinearMap.id : SuTwo →ₗ[ℝ] SuTwo)

/-- The reverse direction, same theorem with domain/codomain swapped. -/
theorem continuous_id_rawNorm_to_ambient :
    @Continuous SuTwo SuTwo (@UniformSpace.toTopologicalSpace SuTwo PseudoMetricSpace.toUniformSpace)
      instTopologicalSpaceSubtype
      id :=
  @LinearMap.continuous_of_finiteDimensional ℝ _ SuTwo _ _
    (@UniformSpace.toTopologicalSpace SuTwo PseudoMetricSpace.toUniformSpace) _ _
    SuTwo _ _ instTopologicalSpaceSubtype _ _
    _ _ _
    (LinearMap.id : SuTwo →ₗ[ℝ] SuTwo)

/-- The ambient and RAW-norm topologies coincide (continuous both ways ⇒ equal). -/
theorem ambient_topologicalSpace_eq_rawNorm :
    (instTopologicalSpaceSubtype : TopologicalSpace SuTwo) =
      @UniformSpace.toTopologicalSpace SuTwo PseudoMetricSpace.toUniformSpace := by
  apply le_antisymm
  · exact continuous_id_iff_le.mp continuous_id_ambient_to_rawNorm
  · exact continuous_id_iff_le.mp continuous_id_rawNorm_to_ambient

/-- **The equality `MetricSpace.replaceUniformity` consumes.** For a topological additive group the
uniform structure is determined by the topology at `0` (`IsUniformAddGroup.ext`), and both sides are
genuine `IsUniformAddGroup` structures. -/
theorem ambient_uniformSpace_eq_rawNorm :
    (instUniformSpaceSubtype : UniformSpace SuTwo) = PseudoMetricSpace.toUniformSpace :=
  IsUniformAddGroup.ext (suTwo.toAddSubgroup.isUniformAddGroup) inferInstance
    (congrArg (@nhds SuTwo · (0 : SuTwo)) ambient_topologicalSpace_eq_rawNorm)

end RawDiamond

/-- The `uniformity`-FILTER form of §4b's equality, i.e. literally the hypothesis
`MetricSpace.replaceUniformity` asks for. -/
theorem uniformity_ambient_eq_rawNorm :
    @uniformity SuTwo instUniformSpaceSubtype
      = @uniformity SuTwo suTwoNormedRaw.toMetricSpace.toPseudoMetricSpace.toUniformSpace :=
  congrArg (fun u : UniformSpace SuTwo => @uniformity SuTwo u) ambient_uniformSpace_eq_rawNorm

/-- **THE SHIPPED NORM on `𝔰𝔲(2)`**, `hsInner`'s norm with its uniformity field replaced by the
ambient subtype uniformity (§4b). Same `Norm`, same `AddCommGroup`, same `dist`; only the
`toUniformSpace` field differs from `suTwoNormedRaw`, and it now agrees DEFINITIONALLY with what
`#synth UniformSpace ↥SuTwo` / `#synth TopologicalSpace ↥SuTwo` return. -/
noncomputable instance instNormedAddCommGroupSuTwo : NormedAddCommGroup SuTwo :=
  { suTwoNormedRaw with
    toMetricSpace :=
      @MetricSpace.replaceUniformity SuTwo instUniformSpaceSubtype
        suTwoNormedRaw.toMetricSpace uniformity_ambient_eq_rawNorm }

/-- **The deliverable: `InnerProductSpace ℝ 𝔰𝔲(2)`.**

Built field-by-field rather than by `InnerProductSpace.ofCore`, because `ofCore`'s result is typed
against `InnerProductSpace.Core.toSeminormedAddCommGroup` — the RAW group — and that is not
definitionally the uniformity-replaced one (measured: `ofCore suTwoPreCore` against the repaired
group gives `Type mismatch … Core.toSeminormedAddCommGroup` vs `NormedAddCommGroup.
toSeminormedAddCommGroup`). Every field below is nevertheless the SAME mathematics: the norm is
`√(hsInner X X)` by `rfl` on both sides (`norm_eq_sqrt_hsInner` below), so each obligation is the
obligation `ofCore` discharges, restated. -/
noncomputable instance instInnerProductSpaceSuTwo : InnerProductSpace ℝ SuTwo where
  toInner := ⟨hsInner⟩
  norm_smul_le := by
    intro r X
    show Real.sqrt (hsInner (r • X) (r • X)) ≤ ‖r‖ * Real.sqrt (hsInner X X)
    have hs : hsInner (r • X) (r • X) = r ^ 2 * hsInner X X := by
      rw [hsInner_smul_left, hsInner_symm, hsInner_smul_left, hsInner_symm]; ring
    rw [hs, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
  norm_sq_eq_re_inner := by
    intro X
    show Real.sqrt (hsInner X X) ^ 2 = hsInner X X
    exact Real.sq_sqrt (hsInner_self_nonneg X)
  conj_inner_symm := by
    intro X Y
    show hsInner Y X = hsInner X Y
    exact hsInner_symm Y X
  add_left := by
    intro X Y Z
    exact hsInner_add_left X Y Z
  smul_left := by
    intro X Y r
    show hsInner (r • X) Y = r * hsInner X Y
    exact hsInner_smul_left X Y r

/-! ### §4c — MUST-NOT-FIRE CONTROLS: the repair changed no VALUE

If any of these stopped being `rfl`, the repair would have moved the mathematics rather than the
instance path, and it would be the wrong fix. -/

/-- The shipped norm is `√⟪X,X⟫` — literally, by `rfl`. -/
theorem norm_eq_sqrt_hsInner (X : SuTwo) : ‖X‖ = Real.sqrt (hsInner X X) := rfl

/-- **THE NORM DID NOT CHANGE.** `‖·‖` under the shipped (uniformity-replaced) instance is the SAME
FUNCTION as under `suTwoNormedRaw`, by `rfl` — pointwise and as a whole function. This is the check
that Bałaban's `tr 1 = 1` normalization survived the instance surgery untouched. -/
theorem norm_unchanged_by_uniformity_repair :
    (@norm SuTwo (@NormedAddCommGroup.toNorm SuTwo instNormedAddCommGroupSuTwo))
      = (@norm SuTwo (@NormedAddCommGroup.toNorm SuTwo suTwoNormedRaw)) := rfl

/-- Same for `dist`. -/
theorem dist_unchanged_by_uniformity_repair :
    (@dist SuTwo instNormedAddCommGroupSuTwo.toMetricSpace.toPseudoMetricSpace.toDist)
      = (@dist SuTwo suTwoNormedRaw.toMetricSpace.toPseudoMetricSpace.toDist) := rfl

/-- The `AddCommGroup` component is the canonical `Submodule` one — no algebraic diamond was
introduced. -/
theorem addCommGroup_unchanged_by_uniformity_repair :
    (@NormedAddCommGroup.toAddCommGroup SuTwo instNormedAddCommGroupSuTwo)
      = (SuTwo.addCommGroup : AddCommGroup SuTwo) := rfl

/-- The `Module ℝ` component of the inner-product structure is the canonical `Submodule` one. -/
theorem module_unchanged_by_uniformity_repair :
    (@InnerProductSpace.toNormedSpace ℝ SuTwo _ _ instInnerProductSpaceSuTwo).toModule
      = (SuTwo.module : Module ℝ SuTwo) := rfl

/-! ### §4d — MUST-FIRE CONTROLS: the diamond is gone

Each of these FAILS to typecheck on the pre-repair file (recorded in
`compute/sutwo_diamond/REPORT.md` §BEFORE) and is `rfl` here. That is the whole content of the
repair. -/

/-- `#synth UniformSpace ↥SuTwo` and the norm's uniformity are now the SAME TERM. -/
theorem uniformSpace_diamond_is_rfl :
    (instUniformSpaceSubtype : UniformSpace SuTwo)
      = @PseudoMetricSpace.toUniformSpace SuTwo
          (@MetricSpace.toPseudoMetricSpace SuTwo
            (@NormedAddCommGroup.toMetricSpace SuTwo instNormedAddCommGroupSuTwo)) := rfl

/-- `#synth TopologicalSpace ↥SuTwo` and the norm's topology are now the SAME TERM. -/
theorem topologicalSpace_diamond_is_rfl :
    (instTopologicalSpaceSubtype : TopologicalSpace SuTwo)
      = @UniformSpace.toTopologicalSpace SuTwo
          (@PseudoMetricSpace.toUniformSpace SuTwo
            (@MetricSpace.toPseudoMetricSpace SuTwo
              (@NormedAddCommGroup.toMetricSpace SuTwo instNormedAddCommGroupSuTwo))) := rfl

/-- **The consequence at the `PiLp` level — the thing that was actually blocked.** The `PiLp`
topology built from the fibres' registered `TopologicalSpace` and the one built from
`PiLp.normedAddCommGroup` are now the SAME TERM at the `SuTwo` fibre. Pre-repair this `rfl` FAILED
(measured), and `CoercivityRegular.lean` §8's `pilp_topology_diamond_is_rfl_at_real_fibre` is the
must-not-fire control showing the failure was specific to this fibre, not a `PiLp` fact. -/
theorem pilp_topology_diamond_is_rfl_at_suTwo_fibre :
    (PiLp.topologicalSpace 2 fun _ : Fin 3 => SuTwo)
      = (PiLp.normedAddCommGroup (p := 2)
          (α := fun _ : Fin 3 => SuTwo)).toUniformSpace.toTopologicalSpace := rfl

/-- Same at the `UniformSpace` level. -/
theorem pilp_uniformSpace_diamond_is_rfl_at_suTwo_fibre :
    (PiLp.uniformSpace 2 fun _ : Fin 3 => SuTwo)
      = (PiLp.normedAddCommGroup (p := 2)
          (α := fun _ : Fin 3 => SuTwo)).toUniformSpace := rfl

/-- **THE `BondFnL2` REGRESSION PIN** (`compute/norm_diamond/PATCH_SPEC.md` step 2, installed by
`compute/norm_diamond_install/`). `‖·‖` on the bond carrier IS the norm of the registered
`NormedAddCommGroup` on that same type.

This `rfl` **FAILED** for as long as `CovariantOperators.lean` registered
`instNormedAddCommGroupBondFnL2` (an `inferInstance` frozen at the L²-OPERATOR fibre): the `Norm`
slot resolved to `PiLp.instNorm` at the HILBERT–SCHMIDT fibre while the `NormedAddCommGroup` slot
resolved to the frozen operator-fibre instance, so `‖v‖` was not the registered structure's norm and
`ContinuousLinearMap.adjoint` / bare `LinearMap.adjoint` could not unify on this carrier. Measured
failing three times before the deletion (`compute/norm_diamond/logs/diamond.log` M3,
`logs/diamond3.log` P5, and `compute/norm_diamond_install/logs/pin_mustnotfire.log`, the last of
which compiles THIS file against the pre-deletion `CovariantOperators` olean).

It fails again the moment anyone re-registers a `NormedAddCommGroup (BondFnL2 L)` from a different
fibre — which is the point of keeping it. -/
theorem bondFnL2_norm_is_the_registered_norm
    (L : AdalyFormal.Target.ClayStatement.PeriodicLatticeExtent) :
    (inferInstance : Norm (BondFnL2 L))
      = (@NormedAddCommGroup.toNorm (BondFnL2 L) inferInstance) := rfl

/-- The instance's `⟪·,·⟫_ℝ` IS `hsInner` — stated so no consumer has to guess which form the
instance carries (and so the normalization above is the one that actually ships). -/
theorem inner_eq_hsInner (X Y : SuTwo) : inner ℝ X Y = hsInner X Y := rfl

theorem inner_eq_trace (X Y : SuTwo) :
    inner ℝ X Y =
      -(1 / 2 : ℝ) *
        (Matrix.trace ((X : Matrix (Fin 2) (Fin 2) ℂ) * (Y : Matrix (Fin 2) (Fin 2) ℂ))).re := rfl

/-! ## §5 — the concrete instance: the Pauli-derived generators are ORTHONORMAL

An abstract inner product space with no computed value denotes nothing. Here is the value, on the
physicists' own basis. `E_k := i·σ_k`, the anti-hermitian presentation of the Pauli generators.
Two of the three are REUSED from `CovariantOperators.lean` (`witnessM = iσ₂`,
`suTwoWitnessVal = iσ₃`), not redefined. -/

/-- The entrywise form of `hsInner`, so every concrete evaluation goes through one expansion. -/
theorem hsInner_entries (X Y : SuTwo) :
    hsInner X Y =
      -(1 / 2 : ℝ) *
        ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
          (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (Y : Matrix (Fin 2) (Fin 2) ℂ) 1 0 +
          (X : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1 +
          (X : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (Y : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re := by
  rw [hsInner_def, trace_mul_fin2]

/-- `iσ₁ = !![0, i; i, 0]`. -/
def pauliE1Val : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]

theorem pauliE1Val_mem : pauliE1Val ∈ suTwo := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliE1Val, Matrix.conjTranspose_apply]
  · simp [pauliE1Val, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- `E₁ = iσ₁`. -/
def pauliE1 : SuTwo := ⟨pauliE1Val, pauliE1Val_mem⟩

/-- `E₂ = iσ₂ = !![0, 1; -1, 0]` — this is exactly `CovariantOperators.witnessM` (LAW-19 reuse:
that matrix, already proved to lie in `suTwo` there, IS `iσ₂`). -/
def pauliE2 : SuTwo := ⟨witnessM, witnessM_mem_suTwo⟩

/-- `E₃ = iσ₃ = !![i, 0; 0, -i]` — exactly `CovariantOperators.suTwoWitness`, reused. -/
def pauliE3 : SuTwo := suTwoWitness

theorem hsInner_e1_e1 : hsInner pauliE1 pauliE1 = 1 := by
  rw [hsInner_entries]; simp [pauliE1, pauliE1Val]; norm_num

theorem hsInner_e2_e2 : hsInner pauliE2 pauliE2 = 1 := by
  rw [hsInner_entries]; simp [pauliE2, witnessM]; norm_num

theorem hsInner_e3_e3 : hsInner pauliE3 pauliE3 = 1 := by
  rw [hsInner_entries]; simp [pauliE3, suTwoWitness, suTwoWitnessVal]; norm_num

theorem hsInner_e1_e2 : hsInner pauliE1 pauliE2 = 0 := by
  rw [hsInner_entries]; simp [pauliE1, pauliE1Val, pauliE2, witnessM]

theorem hsInner_e1_e3 : hsInner pauliE1 pauliE3 = 0 := by
  rw [hsInner_entries]; simp [pauliE1, pauliE1Val, pauliE3, suTwoWitness, suTwoWitnessVal]

theorem hsInner_e2_e3 : hsInner pauliE2 pauliE3 = 0 := by
  rw [hsInner_entries]; simp [pauliE2, witnessM, pauliE3, suTwoWitness, suTwoWitnessVal]

/-! ## §6 — `Ad`-invariance: `R(U)` is an isometry of `𝔰𝔲(2)`

This is what makes the form the RIGHT one for a gauge theory: the adjoint action of `SU(2)`
preserves it, so `D*` (CMP99b eq. 3.8) is well defined independently of the background gauge. -/

/-- `Uᴴ U = 1` for `U ∈ SU(2)` — the same two-line derivation used inline inside
`CovariantOperators.conjByAmbient_mem`; it is not exported there, so it is restated here rather
than duplicated silently. -/
theorem conjTranspose_mul_self (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp U.2.1
  rwa [Matrix.star_eq_conjTranspose] at h

/-- **`⟪R(U)X, R(U)Y⟫ = ⟪X,Y⟫`** — `Ad`-invariance of the form. -/
theorem hsInner_RMap (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X Y : SuTwo) :
    hsInner (RMap U X) (RMap U Y) = hsInner X Y := by
  have hUU := conjTranspose_mul_self U
  set u : Matrix (Fin 2) (Fin 2) ℂ := (U : Matrix (Fin 2) (Fin 2) ℂ) with hu
  set x : Matrix (Fin 2) (Fin 2) ℂ := (X : Matrix (Fin 2) (Fin 2) ℂ) with hx
  set y : Matrix (Fin 2) (Fin 2) ℂ := (Y : Matrix (Fin 2) (Fin 2) ℂ) with hy
  rw [hsInner_def, hsInner_def, RMap_coe_apply, RMap_coe_apply, ← hu, ← hx, ← hy]
  have key : (u * x * uᴴ) * (u * y * uᴴ) = u * (x * y) * uᴴ := by
    calc (u * x * uᴴ) * (u * y * uᴴ) = u * x * (uᴴ * u) * y * uᴴ := by noncomm_ring
      _ = u * x * 1 * y * uᴴ := by rw [hUU]
      _ = u * (x * y) * uᴴ := by noncomm_ring
  rw [key, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hUU, Matrix.mul_one]

theorem inner_RMap (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X Y : SuTwo) :
    inner ℝ (RMap U X) (RMap U Y) = inner ℝ X Y := hsInner_RMap U X Y

/-- **`R(U)` promoted to a genuine `LinearIsometry`** — the shape a future `D*`/`H_j` construction
wants. Built by `LinearMap.isometryOfInner` from §6's invariance (Mathlib machinery reused). -/
noncomputable def RIsometry (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) : SuTwo →ₗᵢ[ℝ] SuTwo :=
  (RMap U).isometryOfInner (inner_RMap U)

theorem RIsometry_apply (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    RIsometry U X = RMap U X := rfl

/-- **A NON-VACUOUS instance of `Ad`-invariance.** `R(M)` for `M = !![0,1;-1,0]` genuinely MOVES
the vector (`CovariantOperators.RMap_witnessMElem`: `R(M)E₃ = -E₃`, and `E₃ ≠ -E₃`), yet the inner
product is unchanged. Without this the invariance theorem could be satisfied by an action that is
secretly the identity. -/
theorem hsInner_RMap_witness :
    hsInner (RMap witnessMElem pauliE3) (RMap witnessMElem pauliE3) = 1 ∧
      RMap witnessMElem pauliE3 ≠ pauliE3 := by
  constructor
  · rw [hsInner_RMap]; exact hsInner_e3_e3
  · rw [pauliE3, RMap_witnessMElem]
    exact fun h => suTwoWitness_ne_neg_self h.symm

/-! ## §7 — falsifiability: the form FAILS when its hypotheses are removed

Three mutations, each with the failure exhibited as a theorem rather than asserted. -/

/-- The same formula, on the AMBIENT matrix space — no skew-hermitian, no traceless hypothesis. -/
noncomputable def ambientForm (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  -(1 / 2 : ℝ) * (Matrix.trace (A * B)).re

theorem hsInner_eq_ambientForm (X Y : SuTwo) :
    hsInner X Y = ambientForm (X : Matrix (Fin 2) (Fin 2) ℂ) (Y : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- **MUTATION 1 (S82 garbage substitution): drop the skew-hermitian hypothesis and positivity
DIES.** `CovariantOperators.garbageNotSkewHermitian = !![1,0;0,-1]` is traceless but hermitian;
the form evaluates to `-1` on it. So `hsInner_self_nonneg` is NOT algebraically forced — it
genuinely consumes `Xᴴ = -X`. -/
theorem ambientForm_garbage_eq_neg_one :
    ambientForm garbageNotSkewHermitian garbageNotSkewHermitian = -1 := by
  rw [ambientForm, trace_mul_fin2]
  simp [garbageNotSkewHermitian]
  norm_num

theorem ambientForm_not_nonneg :
    ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℂ, 0 ≤ ambientForm A A := by
  intro h
  have h1 := h garbageNotSkewHermitian
  rw [ambientForm_garbage_eq_neg_one] at h1
  norm_num at h1

/-- **MUTATION 2: forget Bałaban's `tr 1 = 1` and the Pauli values move.** `hsInnerUnnormalized`
is `hsInner` with the `½` dropped — i.e. reading the audit's "`X·Y = tr XY`" with `tr` taken to be
the ordinary trace. It reports `2`, not `1`, on `E₃`. The `½` is therefore DETECTED by §5's stated
values, not merely declared in a docstring. -/
noncomputable def hsInnerUnnormalized (X Y : SuTwo) : ℝ :=
  -(Matrix.trace ((X : Matrix (Fin 2) (Fin 2) ℂ) * (Y : Matrix (Fin 2) (Fin 2) ℂ))).re

theorem hsInnerUnnormalized_e3_e3 : hsInnerUnnormalized pauliE3 pauliE3 = 2 := by
  rw [hsInnerUnnormalized, trace_mul_fin2]
  simp [pauliE3, suTwoWitness, suTwoWitnessVal]
  norm_num

theorem hsInner_ne_unnormalized :
    hsInner pauliE3 pauliE3 ≠ hsInnerUnnormalized pauliE3 pauliE3 := by
  rw [hsInner_e3_e3, hsInnerUnnormalized_e3_e3]
  norm_num

/-- **MUTATION 3: flip the sign and positivity dies on a genuine member.** This is the audit's
literal reading `X·Y = tr XY` on the anti-hermitian carrier — negative on every nonzero element.
(Restated from §2's `trace_sq_neg_of_mem` at the concrete witness so the failure is a number.) -/
theorem trace_sq_pauliE3 :
    (Matrix.trace ((pauliE3 : Matrix (Fin 2) (Fin 2) ℂ) *
      (pauliE3 : Matrix (Fin 2) (Fin 2) ℂ))).re = -2 := by
  rw [trace_mul_fin2]
  simp [pauliE3, suTwoWitness, suTwoWitnessVal]
  norm_num

/-! ## §9 — `𝔰𝔲(2)` is a real HILBERT space, of dimension 3

Completeness is what upgrades "inner product space" to the object an operator construction
(`Δ'`, `H_j`, `D*`) can actually live on. In finite dimensions it is free — but only once the
finite-dimensionality is actually available on THIS carrier, which is the thing to check. -/

-- `instFiniteDimensionalSuTwo` MOVED UP to §4a (the §4b diamond repair consumes it). It is the
-- same declaration, same proof; only its position in the file changed.

/-- **`𝔰𝔲(2)` is a real HILBERT space** — complete for the metric of `hsInner`'s own norm.

**SUPERSEDED IN PLACE (S75, uniformity-diamond repair, §4b) — the paragraph below is retained
struck because it describes the PRE-REPAIR file and is no longer true.** After §4b,
`instUniformSpaceSubtype` and `PseudoMetricSpace.toUniformSpace` are the SAME TERM on `↥SuTwo`
(`uniformSpace_diamond_is_rfl`, by `rfl`), so the `@`-explicit uniformity in this statement now
names exactly the ambient one, and the "explicitly NAMED residual" is CLOSED BY CONSTRUCTION rather
than merely propositionally (§9b's `ambient_uniformSpace_eq_norm_uniformSpace`, which proved the
propositional version, is retained and now also provable by `rfl`).

~~The `@`-explicit uniformity is NOT decoration, and this is a MEASURED finding rather than a
stylistic choice. `#synth UniformSpace ↥SuTwo` in this very file returns **`instUniformSpaceSubtype`**
— `↥SuTwo` already carries a uniformity as a *subtype of the ambient matrix space*, inherited
independently of any norm — while `#synth SeminormedAddCommGroup ↥SuTwo` returns
`NormedAddCommGroup.toSeminormedAddCommGroup` off `instNormedAddCommGroupSuTwo`. Those two are
propositionally but not definitionally the same uniformity (all norms on a finite-dimensional real
space are equivalent, so the filters agree), and a bare `instance : CompleteSpace SuTwo` therefore
elaborates against the SUBTYPE uniformity and fails to typecheck:~~

```
  FiniteDimensional.complete ℝ ↥SuTwo  :  @CompleteSpace ↥SuTwo PseudoMetricSpace.toUniformSpace
  expected                             :  @CompleteSpace ↥SuTwo instUniformSpaceSubtype
```

~~So completeness is stated here for the uniformity that `hsInner`'s norm actually induces, and
`instUniformSpaceSubtype = PseudoMetricSpace.toUniformSpace` on `𝔰𝔲(2)` is left as an explicitly
NAMED residual (see `formal/AdalyFormal/SUTWO_INNER.md`), NOT quietly assumed.~~ -/
theorem suTwo_complete : @CompleteSpace SuTwo PseudoMetricSpace.toUniformSpace := by
  haveI : ProperSpace SuTwo := FiniteDimensional.proper_real SuTwo
  exact complete_of_proper

/-! ## §9b — DIAMOND REPAIR (dispatch mandate): `CompleteSpace ↥SuTwo` findable by ORDINARY
`#synth`, and a KERNEL-CHECKED proof that the two uniformities §9 named as a residual actually
COINCIDE — so `Continuous f`/`CompleteSpace` on `𝔰𝔲(2)`, however typeclass search resolves them,
denote the norm's own topology, not a silently different one.

**Route taken (measured, not guessed — see `HoleHunt/SuTwoInstanceProbe.lean`).** `#synth
CompleteSpace ↥SuTwo` currently FAILS outright (no instance at all, since §9 deliberately left
`suTwo_complete` a named theorem, not an `instance`, to avoid the elaboration mismatch documented
there). This section closes that gap WITHOUT touching `instNormedAddCommGroupSuTwo`/
`instInnerProductSpaceSuTwo` (§4, unchanged, still the only norm/inner-product on `SuTwo` an
ordinary importer finds) and WITHOUT registering a second, competing `UniformSpace`/
`TopologicalSpace ↥SuTwo` (which would BE the diamond the dispatch forbids). Instead:

1. `instCompleteSpaceSuTwo` proves completeness DIRECTLY for the AMBIENT topology
   (`instUniformSpaceSubtype`, the one ordinary `#synth UniformSpace ↥SuTwo` already returns) via
   Mathlib's GENERAL topological-vector-space theory (`Mathlib.Topology.Algebra.Module.
   FiniteDimension`'s `FiniteDimensional.complete`) — this route needs NO norm on `SuTwo` or on the
   ambient `Matrix (Fin 2) (Fin 2) ℂ` at all (unlike the ANALOGOUS normed-space lemma
   `Submodule.closed_of_finiteDimensional` in `Analysis.Normed.Module.FiniteDimension`, which would
   force exactly the scope dependency `CovariantOperators.lean` §7 already flagged as hazardous).
   `suTwo`'s own `AddSubgroup` gets its canonical uniform-add-group structure
   (`Submodule.toAddSubgroup`/`AddSubgroup.isUniformAddGroup`, the SAME step Mathlib's own
   `Submodule.complete_of_finiteDimensional` uses), then `FiniteDimensional.complete` (finite-dim +
   Hausdorff + complete base field ⇒ complete) finishes it. This IS the genuine, ordinarily-findable
   `CompleteSpace ↥SuTwo` instance the dispatch asks for.
2. `ambient_uniformSpace_eq_norm_uniformSpace` proves `instUniformSpaceSubtype` (ambient, item 1's
   uniformity) and `PseudoMetricSpace.toUniformSpace` (`hsInner`'s own uniformity, `suTwo_complete`'s
   uniformity) are the SAME term, i.e. the residual §9 named is CLOSED, not merely worked around.
   Both are `IsUniformAddGroup ↥SuTwo` structures; for a topological group the uniform structure is
   determined by the topology (`IsUniformAddGroup.ext`/`uniformity_eq_comap_nhds_zero` reduces
   uniformity-equality to topology-equality, i.e. to neighborhoods of `0`), and the two TOPOLOGIES
   agree because the IDENTITY map is continuous both ways between them — each direction is a
   finite-dimensional linear map into/out of a Hausdorff topological vector space, hence continuous
   by `LinearMap.continuous_of_finiteDimensional` (the SAME general theorem underlying "all norms on
   a finite-dim space are equivalent," applied here to a norm vs. a norm-independent ambient
   topology instead of norm vs. norm). Continuous bijection with continuous inverse between two
   topologies on one type forces topological equality (`TopologicalSpace.le_antisymm` via
   `continuous_id_iff_le` both ways).
3. `suTwo_complete_eq_instCompleteSpaceSuTwo` transports item 1's instance across item 2's equality
   and confirms it is (proof-irrelevantly) the SAME fact as `suTwo_complete` — so the "two
   completeness proofs" are not two independent claims that might silently diverge; they are one
   proof, viewed through two, now PROVABLY EQUAL, uniformities. -/

open Filter Topology in
/-- **`CompleteSpace ↥SuTwo`, w.r.t. the AMBIENT (default, `#synth`-findable) topology.** No norm
anywhere in this proof — pure finite-dimensional topological-vector-space theory, so it cannot
diamond against `instNormedAddCommGroupSuTwo`'s separate route. -/
noncomputable instance instCompleteSpaceSuTwo : CompleteSpace SuTwo := by
  haveI : IsUniformAddGroup SuTwo := suTwo.toAddSubgroup.isUniformAddGroup
  exact FiniteDimensional.complete ℝ SuTwo

/-- The two `IsUniformAddGroup` structures on `↥SuTwo` — the ambient one (§9b item 1, what ordinary
`#synth` finds) and the one carried inside `instNormedAddCommGroupSuTwo` (§4, `hsInner`'s own) — as
NAMED terms, so the equality theorem below states something concrete rather than an opaque
`inferInstance = inferInstance`. -/
theorem isUniformAddGroup_ambient : IsUniformAddGroup SuTwo :=
  suTwo.toAddSubgroup.isUniformAddGroup

theorem isUniformAddGroup_norm :
    @IsUniformAddGroup SuTwo PseudoMetricSpace.toUniformSpace _ :=
  inferInstance

/-- **Identity, ambient topology → norm topology, is continuous.** A finite-dimensional linear map
into a Hausdorff topological vector space (`hsInner`'s own `SuTwo`, via `instInnerProductSpaceSuTwo`)
is automatically continuous — `LinearMap.continuous_of_finiteDimensional`, the exact fact underlying
"all norms on a finite-dim space are equivalent," here applied to AMBIENT-topology-vs-norm rather
than norm-vs-norm. -/
theorem continuous_id_ambient_to_norm :
    @Continuous SuTwo SuTwo instTopologicalSpaceSubtype
      (@UniformSpace.toTopologicalSpace SuTwo PseudoMetricSpace.toUniformSpace)
      id :=
  @LinearMap.continuous_of_finiteDimensional ℝ _ SuTwo _ _
    instTopologicalSpaceSubtype _ _
    SuTwo _ _ (@UniformSpace.toTopologicalSpace SuTwo PseudoMetricSpace.toUniformSpace) _ _
    _ _ _
    (LinearMap.id : SuTwo →ₗ[ℝ] SuTwo)

/-- **Identity, norm topology → ambient topology, is continuous.** The reverse direction: `SuTwo`
with `hsInner`'s topology is finite-dimensional (§9, `instFiniteDimensionalSuTwo`) and the ambient
topology makes it a Hausdorff topological vector space (inherited from `Matrix (Fin 2) (Fin 2) ℂ`'s
own entrywise structure, no norm choice needed) — so `LinearMap.continuous_of_finiteDimensional`
applies with the roles of domain/codomain swapped relative to the previous theorem. -/
theorem continuous_id_norm_to_ambient :
    @Continuous SuTwo SuTwo (@UniformSpace.toTopologicalSpace SuTwo PseudoMetricSpace.toUniformSpace)
      instTopologicalSpaceSubtype
      id :=
  @LinearMap.continuous_of_finiteDimensional ℝ _ SuTwo _ _
    (@UniformSpace.toTopologicalSpace SuTwo PseudoMetricSpace.toUniformSpace) _ _
    SuTwo _ _ instTopologicalSpaceSubtype _ _
    _ _ _
    (LinearMap.id : SuTwo →ₗ[ℝ] SuTwo)

/-- **THE CLOSED RESIDUAL: the ambient and norm topologies on `𝔰𝔲(2)` are THE SAME.** Continuous
bijection with continuous inverse (both directions above) between two topologies on one type forces
equality (`continuous_id_iff_le`, antisymmetry of the specialization order on topologies). -/
theorem ambient_topologicalSpace_eq_norm_topologicalSpace :
    (instTopologicalSpaceSubtype : TopologicalSpace SuTwo) =
      @UniformSpace.toTopologicalSpace SuTwo PseudoMetricSpace.toUniformSpace := by
  apply le_antisymm
  · exact continuous_id_iff_le.mp continuous_id_ambient_to_norm
  · exact continuous_id_iff_le.mp continuous_id_norm_to_ambient

/-- **THE CLOSED RESIDUAL, at the `UniformSpace` level.** For a topological additive group the
uniform structure is determined by the topology at `0` (`IsUniformAddGroup.ext`, the `to_additive`
image of `IsUniformGroup.ext`: two `IsUniformAddGroup` structures on the same carrier with the same
`nhds 0` are literally the SAME `UniformSpace`): since the underlying topologies agree (previous
theorem, hence the same `nhds 0`) and BOTH `instUniformSpaceSubtype` and `PseudoMetricSpace.
toUniformSpace` are genuine `IsUniformAddGroup` structures, the uniformities themselves agree, not
merely their topologies. This is the literal statement `SuTwoInner.lean`'s own §9 docstring named as
an explicitly NOT-yet-proved residual — closed here. -/
theorem ambient_uniformSpace_eq_norm_uniformSpace :
    (instUniformSpaceSubtype : UniformSpace SuTwo) = PseudoMetricSpace.toUniformSpace :=
  IsUniformAddGroup.ext isUniformAddGroup_ambient isUniformAddGroup_norm
    (congrArg (@nhds SuTwo · (0 : SuTwo)) ambient_topologicalSpace_eq_norm_topologicalSpace)

/-- **SUPERSEDED IN PLACE (S75, §4b uniformity-diamond repair).** This note recorded that
`ambient_uniformSpace_eq_norm_uniformSpace` was NOT provable by `rfl`. That was true of the
pre-repair file and is FALSE of this one: §4b makes the shipped `NormedAddCommGroup`'s uniformity
field literally `instUniformSpaceSubtype`, so the equality is now definitional
(`uniformSpace_diamond_is_rfl`, §4d, proved by `rfl`). The general proof above is RETAINED
unchanged — it is still a correct proof, it no longer needs to be, and three modules
(`DeltaKFull`, `BondSU2Space`, `CovariantHjMinimizer`) consume this exact statement.

~~Falsifiability (S82/OPS-3): the equality is NOT a tautology of matching `rfl`-terms. The two
sides are built via genuinely different routes (`instUniformSpaceSubtype` from the ambient subtype,
`PseudoMetricSpace.toUniformSpace` from `hsInner`'s bilinear form via `InnerProductSpace.Core`) — if
they were secretly the same TERM already, this whole section (and the residual §9 named) would not
have been necessary. Confirmed NOT `rfl`: attempting `rfl` in place of the proof above fails (checked
directly, not asserted) — the equality genuinely consumes `continuous_of_finiteDimensional` on both
sides, not definitional unfolding.~~ -/
theorem ambient_uniformSpace_eq_norm_uniformSpace_not_rfl : True := by
  -- Mutation record (PRE-REPAIR, superseded): replacing the proof of
  -- `ambient_uniformSpace_eq_norm_uniformSpace` with `rfl` was tried first and rejected by the
  -- kernel. Post-§4b that mutation SUCCEEDS, which is the repair's must-fire control
  -- (`uniformSpace_diamond_is_rfl`, §4d).
  trivial

/-- **The two completeness facts are the SAME fact**, transported across the closed uniformity
equality — not two independent claims that might silently diverge. -/
theorem suTwo_complete_eq_instCompleteSpaceSuTwo :
    suTwo_complete =
      ambient_uniformSpace_eq_norm_uniformSpace ▸ (instCompleteSpaceSuTwo : CompleteSpace SuTwo) :=
  Subsingleton.elim _ _

/-- **The explicit `Pauli` decomposition**: every `X ∈ 𝔰𝔲(2)` is
`Im(X₀₁)·E₁ + Re(X₀₁)·E₂ + Im(X₀₀)·E₃`. Note it consumes BOTH defining conditions of `suTwo` — the
`E₃` coefficient is forced by tracelessness and the `(1,0)` entry by skew-hermitian-ness — so
`𝔰𝔲(2)` is genuinely 3-dimensional, not 4. -/
theorem suTwo_decompose (X : SuTwo) :
    X = ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im • pauliE1 +
        ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re • pauliE2 +
        ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im • pauliE3 := by
  obtain ⟨hskew, htr⟩ := X.2
  have hre00 : ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re = 0 := by
    have h := congrArg Complex.re (entry_skew hskew 0 0)
    simp only [Complex.neg_re, Complex.conj_re] at h
    linarith
  have h11 : (X : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = -((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
    have h := htr
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  have h10 : (X : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      -(starRingEnd ℂ) ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := entry_skew hskew 0 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Submodule.coe_add, SetLike.val_smul, Matrix.add_apply, Matrix.smul_apply,
      pauliE1, pauliE1Val, pauliE2, witnessM, pauliE3, suTwoWitness, suTwoWitnessVal,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one,
      Complex.real_smul, Fin.zero_eta, Fin.mk_one]
  · apply Complex.ext <;> simp [hre00]
  · apply Complex.ext <;> simp
  · rw [h10]; apply Complex.ext <;> simp
  · rw [h11]; apply Complex.ext <;> simp [hre00]

/-- The three generators SPAN `𝔰𝔲(2)`. -/
theorem span_pauli_eq_top :
    Submodule.span ℝ ({pauliE1, pauliE2, pauliE3} : Set SuTwo) = ⊤ := by
  rw [eq_top_iff]
  rintro X -
  rw [suTwo_decompose X]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

/-! ## §4e — THE TWO `𝔰𝔲(2)` FIBRE NORMS ARE THE SAME FUNCTION

**Closes the residual this module's own docstring named and declined** (the struck clause at the
top: "the Lean proof of that agreement is named as a residual and NOT claimed here"). Built by
`compute/norm_diamond/` as `stage/NormDiamond/SuTwoNormAgreement.lean` and installed here rather
than as a new module, because this is the file that owed the proof.

**What it is for.** `Balaban/CovariantOperators.lean` used to register a `NormedAddCommGroup
(BondFnL2 L)` whose `𝔰𝔲(2)` fibre was the L²-OPERATOR norm, while every consumer's `‖·‖` went
through the HILBERT–SCHMIDT fibre built from `hsInner`. That instance is now deleted. The theorems
below are what make the deletion **provably content-preserving**: whichever side of the former
diamond a statement sat on, `‖·‖` denotes the SAME REAL NUMBER — a kernel-checked fact, not a hope.

**The route** is not the eigenvalue argument the docstring sketched (normality, eigenvalues `±iλ`)
but its matrix form, which Mathlib supports directly: for traceless skew-hermitian `2×2`,
`Xᴴ X` is a SCALAR matrix with scalar `hsInner X X` (§4e.1), so the C*-identity
`‖AᴴA‖ = ‖A‖‖A‖` plus `Matrix.l2_opNorm_diagonal` gives `‖X‖²_op = hsInner X X` with no spectral
theory (§4e.2).

**Scope, stated (S88).** This proves the two `Norm` structures are equal. It does NOT prove the two
`NormedAddCommGroup` STRUCTURES are equal — they may differ in `uniformity`/`bornology`/proof
fields, and nothing here claims otherwise.

`open scoped Matrix.Norms.L2Operator` is deliberately confined to this section: it is what makes the
operator norm on `Matrix (Fin 2) (Fin 2) ℂ` nameable at all, and it is exactly the scope whose
leakage created the original diamond. It is NOT exported to importers. -/

section FibreNormAgreement

open scoped Matrix.Norms.L2Operator
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent)

/-! ### §4e.1 — the structural identity `Xᴴ X = (hsInner X X) · 1` on `𝔰𝔲(2)` -/

/-- The `(0,0)` entry of a skew-hermitian matrix is purely imaginary. -/
theorem re_entry00_eq_zero (X : SuTwo) : ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re = 0 := by
  obtain ⟨hskew, -⟩ := X.2
  have h := congrArg Complex.re (entry_skew hskew 0 0)
  simp only [Complex.neg_re, Complex.conj_re] at h
  linarith

/-- Tracelessness in entry form. -/
theorem entry11_eq_neg_entry00 (X : SuTwo) :
    (X : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = -((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  obtain ⟨-, htr⟩ := X.2
  rw [Matrix.trace_fin_two] at htr
  linear_combination htr

/-- `hsInner X X` in terms of the two free entries. -/
theorem hsInner_self_entries (X : SuTwo) :
    hsInner X X = ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im ^ 2
      + Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  obtain ⟨hskew, -⟩ := X.2
  have hre00 := re_entry00_eq_zero X
  have h11 := entry11_eq_neg_entry00 X
  have h10 : (X : Matrix (Fin 2) (Fin 2) ℂ) 1 0
      = -(starRingEnd ℂ) ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := entry_skew hskew 0 1
  rw [hsInner_self_eq_sumNormSq]
  have e00 : Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
      = ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im ^ 2 := by
    rw [Complex.normSq_apply, hre00]; ring
  have e11 : Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
      = ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im ^ 2 := by
    rw [h11, Complex.normSq_neg, Complex.normSq_apply, hre00]; ring
  have e10 : Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
      = Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
    rw [h10, Complex.normSq_neg, Complex.normSq_conj]
  rw [e00, e11, e10]
  ring

/-- **THE STRUCTURAL IDENTITY.** For `X ∈ 𝔰𝔲(2)`, `Xᴴ X` is a SCALAR matrix and the scalar is
`hsInner X X`. BOTH defining conditions of `suTwo` are consumed — skew-hermitian-ness for the
diagonal entries, tracelessness for the off-diagonal ones vanishing — and §4e.4 proves neither is
decorative. -/
theorem conjTranspose_mul_self_eq_diagonal (X : SuTwo) :
    (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (X : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.diagonal (fun _ : Fin 2 => ((hsInner X X : ℝ) : ℂ)) := by
  obtain ⟨hskew, -⟩ := X.2
  have hre00 := re_entry00_eq_zero X
  have h11 := entry11_eq_neg_entry00 X
  have hs := hsInner_self_entries X
  -- abbreviate the two free entries so the rewrites below terminate
  set p : ℝ := ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im with hp
  set z : ℂ := (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 with hzdef
  have h10 : (X : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -(starRingEnd ℂ) z := entry_skew hskew 0 1
  have hz : (X : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (p : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hp, hre00]
  -- `Xᴴ = -X` turns the conjugate-transpose product into a plain matrix square
  rw [hskew]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one] <;>
    simp only [hs, h11, h10, hz] <;>
    apply Complex.ext <;>
    simp [Complex.normSq_apply, ← hzdef, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-! ### §4e.2 — the operator norm of `X ∈ 𝔰𝔲(2)` -/

/-- **`‖X‖²_op = hsInner X X`** with `‖·‖` the L²-OPERATOR norm on `Matrix (Fin 2) (Fin 2) ℂ`.
Route: the C*-identity `‖Aᴴ A‖ = ‖A‖‖A‖` (`Matrix.l2_opNorm_conjTranspose_mul_self`), then §4e.1,
then `Matrix.l2_opNorm_diagonal`. -/
theorem l2op_norm_sq_eq_hsInner (X : SuTwo) :
    ‖(X : Matrix (Fin 2) (Fin 2) ℂ)‖ * ‖(X : Matrix (Fin 2) (Fin 2) ℂ)‖ = hsInner X X := by
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (X : Matrix (Fin 2) (Fin 2) ℂ)
  rw [conjTranspose_mul_self_eq_diagonal X, Matrix.l2_opNorm_diagonal] at h1
  rw [← h1, pi_norm_const]
  simp [abs_of_nonneg (hsInner_self_nonneg X)]

/-! ### §4e.3 — THE FIBRE AGREEMENT -/

/-- The operator-norm fibre structure — the same object `HoleHunt/ConventionPins.lean` names
`suTwoFiberNorm` (LAW-19). Deliberately a plain `def`, NOT an instance: registering it would
re-create the very diamond this file's §4b/§4d exist to close. -/
@[reducible] noncomputable def suTwoFibreOp : NormedAddCommGroup SuTwo :=
  Submodule.normedAddCommGroup suTwo

/-- **MUST-FIRE RESOLUTION PIN, so §4e.3's content cannot be trivialised by the ambient scope.**
Inside this section BOTH `𝔰𝔲(2)` norms are reachable (`open scoped Matrix.Norms.L2Operator` is
active), so a reader is entitled to ask which one the bare `‖X‖` in `fibre_norms_agree` denotes.
It denotes the shipped `hsInner` one: this `rfl` says the `Norm` ordinary search returns here IS
`instNormedAddCommGroupSuTwo`'s. If the scoped operator norm ever won instance search instead, this
pin fails and `fibre_norms_agree` would have become the tautology `x = x`. -/
theorem norm_search_is_the_hsInner_instance :
    (inferInstance : Norm SuTwo)
      = (@NormedAddCommGroup.toNorm SuTwo instNormedAddCommGroupSuTwo) := rfl

/-- **THE FIBRE THEOREM.** The L²-operator fibre norm and the shipped `hsInner` fibre norm are the
SAME FUNCTION on all of `𝔰𝔲(2)` — not merely at `suTwoWitness`, which is the scope
`HoleHunt/ConventionPins.lean` §2.3b explicitly left open. -/
theorem fibre_norms_agree (X : SuTwo) :
    @norm SuTwo (@NormedAddCommGroup.toNorm SuTwo suTwoFibreOp) X = ‖X‖ := by
  have hop : @norm SuTwo (@NormedAddCommGroup.toNorm SuTwo suTwoFibreOp) X
      = ‖(X : Matrix (Fin 2) (Fin 2) ℂ)‖ := rfl
  have hnn : 0 ≤ ‖(X : Matrix (Fin 2) (Fin 2) ℂ)‖ := norm_nonneg _
  rw [hop, norm_eq_sqrt_hsInner, ← l2op_norm_sq_eq_hsInner X, Real.sqrt_mul_self hnn]

/-- **Stronger: the two `Norm ↥SuTwo` STRUCTURES are the same term.** `Norm` is a one-field
structure, so equal norm functions give equal instances (structure eta). -/
theorem fibre_norm_instances_eq :
    (@NormedAddCommGroup.toNorm SuTwo suTwoFibreOp)
      = (inferInstance : Norm SuTwo) :=
  congrArg Norm.mk (funext fibre_norms_agree)

/-! ### §4e.3b — the consequence at the bond carrier

**Provenance note (S75).** `compute/norm_diamond/stage/NormDiamond/SuTwoNormAgreement.lean` stated
these two against `CovariantOperators.instNormedAddCommGroupBondFnL2` BY NAME, together with a third
theorem `frozen_instance_is_pilp_at_op_fibre` measuring that the frozen instance WAS
`PiLp.normedAddCommGroup` at the `suTwoFibreOp` fibre. That instance is deleted in this same pass, so
the name is gone and the measurement has no subject left to measure. What is installed here is the
composite: the statements below are the staged ones with the frozen NAME replaced by the TERM that
`frozen_instance_is_pilp_at_op_fibre` proved it to be. Nothing is weakened — the term-level form is
if anything more robust, since it survives the deletion and does not depend on any instance being
registered. -/

/-- **THE CARRIER THEOREM.** `PiLp.normedAddCommGroup` built at the L²-OPERATOR fibre and the `Norm`
that ordinary search finds on `BondFnL2 L` (`PiLp.instNorm` at the HS fibre) are the SAME TERM, for
every `L`. This is what makes the deletion of the operator-fibre instance content-preserving: a
statement written under either one is a statement about the same norm function. -/
theorem bondFnL2_op_fibre_norm_instances_eq (L : PeriodicLatticeExtent) :
    (@NormedAddCommGroup.toNorm (BondFnL2 L)
        (@PiLp.normedAddCommGroup 2 (Bond L) (fun _ => SuTwo) _ _ (fun _ => suTwoFibreOp)))
      = (inferInstance : Norm (BondFnL2 L)) :=
  congrArg (fun (f : ∀ _ : Bond L, Norm SuTwo) =>
      @PiLp.instNorm 2 (Bond L) (fun _ => SuTwo) _ f)
    (funext fun _ => fibre_norm_instances_eq)

/-- The pointwise corollary: `‖v‖` denotes the same real number on either side of the former
diamond. -/
theorem bondFnL2_norms_agree (L : PeriodicLatticeExtent) (v : BondFnL2 L) :
    @norm (BondFnL2 L) (@NormedAddCommGroup.toNorm (BondFnL2 L)
        (@PiLp.normedAddCommGroup 2 (Bond L) (fun _ => SuTwo) _ _ (fun _ => suTwoFibreOp))) v
      = ‖v‖ :=
  congrArg (fun n => @norm (BondFnL2 L) n v) (bondFnL2_op_fibre_norm_instances_eq L)

/-! ### §4e.4 — ANTI-VACUITY CONTROLS (S82 garbage substitution)

`conjTranspose_mul_self_eq_diagonal` is the load-bearing step and it consumes BOTH defining
conditions of `suTwo`. These controls prove neither is decorative: substitute a matrix violating
exactly one condition and the CONCLUSION becomes FALSE. Without them a reader cannot tell whether
the identity is a fact about `𝔰𝔲(2)` or an algebraic tautology about `2×2` matrices.

`ambientForm` is this file's own ambient extension of `hsInner`
(`ambientForm A B = -(1/2)·Re Tr(A·B)`), reused rather than redefined (LAW-19). -/

/-- CONTROL A: `σ₃` is TRACELESS but HERMITIAN, not skew-hermitian. -/
def ctrlHermitian : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem ctrlHermitian_traceless : Matrix.trace ctrlHermitian = 0 := by
  simp [ctrlHermitian, Matrix.trace_fin_two]

theorem ctrlHermitian_not_skew : ctrlHermitianᴴ ≠ -ctrlHermitian := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [ctrlHermitian, Matrix.conjTranspose_apply] at h00
  norm_num [Complex.ext_iff] at h00

/-- CONTROL A fires: the identity's conclusion is FALSE on `σ₃`. -/
theorem ctrlHermitian_breaks :
    ctrlHermitianᴴ * ctrlHermitian
      ≠ Matrix.diagonal (fun _ : Fin 2 => ((ambientForm ctrlHermitian ctrlHermitian : ℝ) : ℂ)) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [ctrlHermitian, ambientForm, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
    Matrix.diagonal_apply_eq] at h00
  norm_num at h00

/-- CONTROL B: `diagonal ![i, 2i]` is SKEW-HERMITIAN but NOT traceless. -/
def ctrlNonTraceless : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, 2 * Complex.I]

theorem ctrlNonTraceless_skew : ctrlNonTracelessᴴ = -ctrlNonTraceless := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ctrlNonTraceless, Matrix.conjTranspose_apply]

theorem ctrlNonTraceless_not_traceless : Matrix.trace ctrlNonTraceless ≠ 0 := by
  simp [ctrlNonTraceless, Matrix.trace_fin_two, Complex.ext_iff]
  norm_num

/-- CONTROL B fires: on a skew-hermitian matrix with nonzero trace, `Xᴴ X` is not even a SCALAR
matrix (`(0,0)` entry `1`, `(1,1)` entry `4`), so no value of the scalar can rescue the identity. -/
theorem ctrlNonTraceless_breaks :
    ∀ c : ℂ, ctrlNonTracelessᴴ * ctrlNonTraceless ≠ Matrix.diagonal (fun _ : Fin 2 => c) := by
  intro c h
  have h00 : (ctrlNonTracelessᴴ * ctrlNonTraceless) 0 0 = c := by rw [h]; simp
  have h11 : (ctrlNonTracelessᴴ * ctrlNonTraceless) 1 1 = c := by rw [h]; simp
  rw [← h11] at h00
  simp [ctrlNonTraceless, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Complex.ext_iff] at h00
  norm_num at h00

end FibreNormAgreement

/-! ## §8 — axiom audit -/

#print axioms hsInner_self_eq_sumNormSq
#print axioms hsInner_self_nonneg
#print axioms hsInner_self_eq_zero
#print axioms trace_sq_neg_of_mem
#print axioms hsInner_symm
#print axioms hsInner_add_left
#print axioms hsInner_smul_left
#print axioms instNormedAddCommGroupSuTwo
#print axioms instInnerProductSpaceSuTwo
#print axioms inner_eq_hsInner
#print axioms inner_eq_trace
#print axioms hsInner_e1_e1
#print axioms hsInner_e2_e2
#print axioms hsInner_e3_e3
#print axioms hsInner_e1_e2
#print axioms hsInner_e1_e3
#print axioms hsInner_e2_e3
#print axioms hsInner_RMap
#print axioms RIsometry
#print axioms hsInner_RMap_witness
#print axioms ambientForm_not_nonneg
#print axioms hsInner_ne_unnormalized
#print axioms trace_sq_pauliE3
#print axioms instFiniteDimensionalSuTwo
#print axioms suTwo_complete
#print axioms suTwo_decompose
#print axioms span_pauli_eq_top
#print axioms instCompleteSpaceSuTwo
#print axioms isUniformAddGroup_ambient
#print axioms isUniformAddGroup_norm
#print axioms continuous_id_ambient_to_norm
#print axioms continuous_id_norm_to_ambient
#print axioms ambient_topologicalSpace_eq_norm_topologicalSpace
#print axioms ambient_uniformSpace_eq_norm_uniformSpace
#print axioms suTwo_complete_eq_instCompleteSpaceSuTwo
#print axioms suTwoNormedRaw
#print axioms suTwoInnerRaw
#print axioms continuous_id_ambient_to_rawNorm
#print axioms continuous_id_rawNorm_to_ambient
#print axioms ambient_topologicalSpace_eq_rawNorm
#print axioms ambient_uniformSpace_eq_rawNorm
#print axioms uniformity_ambient_eq_rawNorm
#print axioms norm_eq_sqrt_hsInner
#print axioms norm_unchanged_by_uniformity_repair
#print axioms dist_unchanged_by_uniformity_repair
#print axioms addCommGroup_unchanged_by_uniformity_repair
#print axioms module_unchanged_by_uniformity_repair
#print axioms uniformSpace_diamond_is_rfl
#print axioms topologicalSpace_diamond_is_rfl
#print axioms pilp_topology_diamond_is_rfl_at_suTwo_fibre
#print axioms pilp_uniformSpace_diamond_is_rfl_at_suTwo_fibre
#print axioms bondFnL2_norm_is_the_registered_norm
#print axioms re_entry00_eq_zero
#print axioms entry11_eq_neg_entry00
#print axioms hsInner_self_entries
#print axioms conjTranspose_mul_self_eq_diagonal
#print axioms l2op_norm_sq_eq_hsInner
#print axioms norm_search_is_the_hsInner_instance
#print axioms fibre_norms_agree
#print axioms fibre_norm_instances_eq
#print axioms bondFnL2_op_fibre_norm_instances_eq
#print axioms bondFnL2_norms_agree
#print axioms ctrlHermitian_traceless
#print axioms ctrlHermitian_not_skew
#print axioms ctrlHermitian_breaks
#print axioms ctrlNonTraceless_skew
#print axioms ctrlNonTraceless_not_traceless
#print axioms ctrlNonTraceless_breaks

end AdalyFormal.Balaban.SuTwoInner
