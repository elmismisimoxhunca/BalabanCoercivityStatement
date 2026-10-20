/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BondSU2Space
import AdalyFormal.Balaban.DeltaPrime

set_option autoImplicit false

/-!
# Assembling CMP99b `Δ_k(U)` on `BondFnL2 L` — what joins, what does NOT, and why

**Dispatch target**: join `Balaban/BondSU2Space.lean`'s `bondLaplacianCovCLM_L2` and
`Balaban/DeltaPrime.lean`'s `deltaPrimeQuadForm`/`deltaQuadForm` into a single
`H →L[ℝ] H`, `H := BondFnL2 L`, matching `Coercivity.lean`'s `Δ : ℕ → Uconfig → H →L[ℝ] H` field
shape and CMP99b eq. (3.10).

**HEADLINE FINDING, settled by direct construction, not assumed**: the two halves named in the
dispatch do **not** join as instructed. `bondLaplacianCovCLM_L2` is **not** the `D*D`/`DD*` piece of
CMP99b (3.10) — it is built from the wrong `D` (§1 below, a genuine object-identity error this file
corrects rather than propagates). The CORRECT `D*D` piece is built here from scratch (§4-§5), on the
right carrier, with its quadratic form proved (not asserted) to equal `CovariantHj.dstarDQuadForm`.
Promoting it (or `Δ′`) to a genuine SELF-ADJOINT `ContinuousLinearMap` hits a SECOND, previously
undocumented wall (§6) — `ContinuousLinearMap.adjoint`/`InnerProductSpace.toDual`-based Riesz
routes fail on the SAME ambient-vs-norm-topology instance diamond `PILP_BRIDGE.md` found for bundled
`∘L`/`∘ₗ` composition, extended here to bundled *application*, not just composition. §7 names the
two precise combinatorial lemmas (in the PROVEN style of `CovariantHjMinimizer.lean` §5's
`gradCovariantAdjointValue`) that would close it, and §8 proves the ASSEMBLY LOGIC is sound
conditional on them — the strongest honest output available in this dispatch's budget, per
`problem/PROBLEM.md`'s disposition on named, precisely-characterized residuals.

## §0 — SIGN VERDICT: SETTLED, not parameterized

CMP99b printed p.392 (image-verified at 300dpi, `compute/carrier_audit/renders/CMP99b_p392-04.png`,
header "392 / T. Balaban", re-confirmed directly in this dispatch, not merely cited from
`CARRIER.md`), eq. (3.10), VERBATIM:

> `⟨A,ΔA⟩ = ⟨A,D*DA⟩ + ⟨A,Δ'A⟩`

— a **PLUS** sign between the two terms. This settles the ASSEMBLY sign
(`DeltaPrime.deltaQuadForm_eq`'s own `dstarDQuadForm U A + deltaPrimeQuadForm U A` shape is the
right ASSEMBLY structure).

What is **not** settled by the assembly sign alone is which of `DeltaPrime.lean`'s two proved-to-
differ-by-sign readings of `Δ′` (`deltaPrimeQuadForm` "untransported" vs `deltaPrimeQuadFormTransported`,
`deltaPrimeQuadFormTransported_eq_neg` proving they are negatives of each other, `8` vs `-8` at the
witness) is the one that reproduces Bałaban's own numeral. **This IS settled here, by a short,
independently-checkable derivation from facts ALREADY IN THIS TREE** (no new page render needed
beyond the re-confirmation above, since `SuTwoInner.lean`'s own docstring already carries the
image-verified quotes used):

1. `SuTwoInner.lean`'s own docstring (image-verified, p.391-392): Bałaban's carrier is HERMITIAN
   (`U'=exp(iηA)`), ours (`SuTwo`) is ANTI-Hermitian, related by `φ:X↦iX`, and `hsInner` is
   **DERIVED** there as `hsInner X Y := φ(X)·φ(Y) = tr((iX)(iY)) = -tr(XY) = -½Tr(XY)` (the final
   `-½` factor is Bałaban's own trace normalization, `tr = ½Tr` for `N=2`, immaterial to the SIGN
   question this section asks — elided above only where the derivation chain is re-quoted, not
   where the actual `def hsInner` itself is cited) — i.e. `hsInner` **already bakes in** the
   `φ`-transport relative to Bałaban's own raw-trace pairing `X·Y=tr XY`.
2. `dstarDQuadForm U A := covPlaqInner (curl U A) (curl U A)` is built **entirely from `hsInner`**
   (via `covPlaqInner`/`covBondInner`, `CovariantHj.lean` §1). Since `curlValueCovariant` is an
   `ℝ`-linear (in fact `ℂ`-linear, since `RMap`/negation/subtraction all commute with `i`-scaling)
   combination of its argument, `curl(φ(X)) = φ(curl(X)) = i·curl(X)` for any bond field `X`.
   Substituting Bałaban's `A := φ(X) = iX` into his own `⟨A,D*DA⟩ = Σ_p tr((D^1A)(p)·(D^1A)(p))`
   (raw Hermitian pairing, p.391's `X·Y=trXY`) gives `Σ_p tr(i·curl(X)(p)·i·curl(X)(p)) =
   -Σ_p tr(curl(X)(p)²)`. Meanwhile `dstarDQuadForm(X) = Σ_p hsInner(curl(X)(p),curl(X)(p)) =
   Σ_p (-tr(curl(X)(p)²))` (definition 1 above, at `Y=X`). **These are the SAME expression** — the
   `φ`-transport built into `hsInner` ALREADY reproduces Bałaban's `⟨A,D*DA⟩` exactly, with **no
   further sign correction needed** — matching `DeltaPrime.lean`'s own module-docstring disclosure
   that `dstarDQuadForm`/`curlValueCovariant` needed "no φ-transport correction" beyond what `hsInner`
   already supplies.
3. **`Δ′`'s two terms (`deltaPrimeFirstTerm`/`deltaPrimeSecondTerm`) are built from RAW
   `Matrix.trace`, NOT from `hsInner`** (`DeltaPrime.lean` §3, direct inspection: `Matrix.trace
   (curl(A)(p) * curl(A)(p) * (reHolonomy U p - 1))`, no `hsInner`/`covPlaqInner`/`covBondInner`
   anywhere in either term's definition). So they do **NOT** automatically inherit `hsInner`'s
   built-in `φ`-correction — substituting `A := φ(X) = iX` into Bałaban's own raw-trace formula
   `tr((D^1A)(p))²(ReU(∂p)-1)` gives `tr((i·curl(X)(p))²)(...) = -tr(curl(X)(p)²)(...)`, i.e. the
   **NEGATIVE** of `deltaPrimeFirstTerm(X,p) := tr(curl(X)(p)²)(...)` **AS DIRECTLY WRITTEN in this
   tree** (no extra sign there). The SAME argument applies term-by-term to `deltaPrimeSecondTerm`
   (also a raw, unwrapped trace against `commutatorMatrixSum`).

**Conclusion, DERIVED not guessed**: because `dstarDQuadForm` picks up its needed `φ`-correction
"for free" through `hsInner`, while `deltaPrimeFirstTerm`/`deltaPrimeSecondTerm` do NOT (raw
traces), the CORRECT reading of CMP99b (3.10) in THIS tree's conventions is

`⟨A,ΔA⟩_correct(X) = dstarDQuadForm U X + deltaPrimeQuadFormTransported U X`

i.e. the **TRANSPORTED** reading of `Δ′`, NOT `DeltaPrime.lean`'s own committed
(`deltaQuadForm := dstarDQuadForm + deltaPrimeQuadForm`, untransported) definition. This is a
genuine correction to that file's committed convention (named here, `DeltaPrime.lean` is out of
this file's write scope and is NOT edited) — `DeltaPrime.lean`'s own docstring already anticipated
exactly this resolution path ("that determination needs the SAME question resolved for
`curlValueCovariant` itself"), and this section is that resolution.

This is stated below as `deltaKQuadFormCorrected` (§3) and used throughout.
-/

namespace AdalyFormal.Balaban.DeltaKFull

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.Balaban.BondSU2Space AdalyFormal.Balaban.DeltaPrime

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE D-OPERATOR MISMATCH: `bondLaplacianCovCLM_L2` is NOT CMP99b (3.10)'s `D*D`/`DD*`

Read directly, not assumed: `BondSU2Space.bondLaplacianCovLM U := (gradCovariantLM U).comp
(gradCovariantAdjointLM U)`, built ENTIRELY from `gradCovariantLM`/`gradCovariantAdjointLM` —
`CovariantOperators.lean`'s SITE↔BOND covariant gradient family (`gradValueCovariant : (Site→SuTwo)
→ (Bond→SuTwo)`, a discrete `∂₀`) and its explicit adjoint.

`CovariantHj.dstarDQuadForm U A := covPlaqInner (curlValueCovariant U A) (curlValueCovariant U A)`
— CMP99b (3.10)'s ACTUAL `⟨A,D*DA⟩` term — is built from `curlValueCovariant : (Bond→SuTwo) →
(Plaquette→SuTwo)` (`CovariantOperators.lean`'s BOND↔PLAQUETTE covariant curl, a discrete `∂₁`,
matching `DeltaPrime.lean`'s own identification `(D_U^1A)(p) = curlValueCovariant U A p`,
`sum_Aprime_eq_curl`).

These are two **different linear maps on different domain/codomain pairs**
(`Site→Bond`/`Bond→Site` vs `Bond→Plaquette`/`Plaquette→Bond`). `BondSU2Space.lean`'s own §6
disclosed `bondLaplacianCovLM` as "a NAMED SIMPLIFICATION relative to CMP99b's actual `Δ_k(U)` — the
`D*D`/`DD*` piece alone" — that disclosure is imprecise: it is not a simplification of the D*D/DD*
piece, it is a genuinely DIFFERENT bond-level Laplacian (the "other side" of the SITE-BOND gradient
family, `CovariantHjMinimizer.siteLaplacianCovLM`'s bond-indexed sibling), unrelated to
`dstarDQuadForm` by any Gram identity. Confirmed directly: `bondLaplacianCovLM`'s own proved Gram
identity (`BondSU2Space.covBondInner_bondLaplacianCovLM_eq_covSiteInner`) reduces to
`covSiteInner (gradCovariantAdjointValue U A) (gradCovariantAdjointValue U A)` — a sum over SITES of
the covariant DIVERGENCE's norm — never to `covPlaqInner (curlValueCovariant ...) (...)`, a sum over
PLAQUETTES of the covariant CURL's norm. **Combining `bondLaplacianCovCLM_L2 + [Δ′ operator]` as the
dispatch's brief literally instructed would NOT reproduce `dstarDQuadForm + Δ′` — it would silently
assemble the wrong first term.** This file does not make that error; §4-§5 build the correct one.

(No theorem is stated here beyond this documented finding — the two operators live in genuinely
different Lean types (`(Bond→SuTwo)→(Bond→SuTwo)` vs the `(Bond→SuTwo)→(Plaquette→SuTwo)`-derived
`(Bond→SuTwo)→(Bond→SuTwo)`), so "prove they disagree" is not even the right kind of statement;
the mismatch is a DENOTATION error, not a numerical one, and is recorded here precisely for that
reason — `problem/PROBLEM.md`'s "the failure mode is the wrong object" pattern.)

## §2 — corrected `U`-dependence witness criterion (Sol/coordinator correction, addressed directly)

The centre of `SU(2)` is `{±I}`, and `Ad(±I) = id` — a "background far from the identity" is
INSUFFICIENT; the correct criterion is `Ad(U) ≠ id`. Checked here, not assumed, for the shared
witness element `witnessMElem` that `adWitnessU` (`BondSU2Space.lean`), `witnessU`
(`CovariantOperators.lean`/`DeltaPrime.lean`), and this file all reuse (LAW-19): -/

/-- **`Ad(witnessMElem) ≠ id`**, proved from `RMap_witnessMElem` (`RMap witnessMElem suTwoWitness =
-suTwoWitness`, ALREADY banked, `CovariantOperators.lean`) plus `suTwoWitness_ne_zero` — if
`RMap witnessMElem` fixed every vector it would fix `suTwoWitness`, forcing `suTwoWitness =
-suTwoWitness`, i.e. `2 • suTwoWitness = 0`, contradicting non-vanishing. This is the CORRECT
criterion (`Ad(U) ≠ id`, not "far from `1`" as a group element): `witnessMElem` could a priori have
been `-1 ∈ SU(2)` (maximally far from `1` as a group element, `Ad(-1)=id`) — it is not; every witness
in this tree built on `witnessMElem`/`adWitnessU`/`witnessU` therefore DOES exercise a genuinely
non-central conjugation action, not merely a group element far from `1`. -/
theorem RMap_witnessMElem_ne_id : RMap witnessMElem ≠ LinearMap.id := by
  intro hcontra
  have h : RMap witnessMElem suTwoWitness = suTwoWitness := by
    rw [hcontra]; rfl
  rw [RMap_witnessMElem] at h
  apply suTwoWitness_ne_zero
  have h2 : (2 : ℝ) • suTwoWitness = 0 := by
    linear_combination (norm := module) (-1 : ℝ) • h
  rcases smul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

#print axioms RMap_witnessMElem_ne_id

/-- **`witnessMElem` is not `±1`** (an independent, purely algebraic confirmation of §2's point,
checked directly on the concrete `2×2` matrix rather than inferred): `witnessM = !![0,1;-1,0]` has
zero diagonal, so it cannot equal `1` (diagonal `1`) or `-1` (diagonal `-1`) — ruling out the ONLY
two central elements of `SU(2)` by direct entry inspection, independent of the `RMap`-based argument
above (a second, algebraically distinct route to the same non-centrality conclusion). -/
theorem witnessMElem_ne_one : witnessMElem ≠ 1 := by
  intro hcontra
  have h : (witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    congrArg (Subtype.val) hcontra
  have := congrFun (congrFun h 0) 0
  simp [witnessMElem, witnessM] at this

/-- `-1 ∈ SU(2)` (the OTHER central element), packaged as a group element directly (the ambient
`Matrix.specialUnitaryGroup` carries no `Neg` instance of its own — it is a multiplicative subgroup,
not additive — so this is built by hand from the underlying matrix `-1` and its membership proof,
rather than via subtype-level `Neg` notation). -/
def negOneElem : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨-1, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨by
    rw [Matrix.mem_unitaryGroup_iff, star_neg, star_one, neg_mul_neg, one_mul], by
    rw [Matrix.det_neg, Matrix.det_one]; simp⟩⟩

theorem witnessMElem_ne_negOneElem : witnessMElem ≠ negOneElem := by
  intro hcontra
  have h : (witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) = (negOneElem : Matrix (Fin 2) (Fin 2) ℂ) :=
    congrArg (Subtype.val) hcontra
  have := congrFun (congrFun h 0) 0
  simp [witnessMElem, witnessM, negOneElem] at this

#print axioms witnessMElem_ne_one
#print axioms negOneElem
#print axioms witnessMElem_ne_negOneElem

/-! ## §3 — the CORRECTED `Δ_k(U)` quadratic form: `dstarDQuadForm + deltaPrimeQuadFormTransported`

Per §0's derivation. Stated once, by name, so every downstream theorem in this file refers to the
SAME corrected target rather than re-deriving the sign each time. -/

/-- **The corrected CMP99b (3.10) quadratic form**, in this tree's conventions (§0). -/
noncomputable def deltaKQuadFormCorrected
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  dstarDQuadForm U A + deltaPrimeQuadFormTransported U A

theorem deltaKQuadFormCorrected_eq_deltaQuadForm_sub_two_deltaPrime
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaKQuadFormCorrected U A = deltaQuadForm U A - 2 * deltaPrimeQuadForm U A := by
  unfold deltaKQuadFormCorrected
  rw [deltaPrimeQuadFormTransported_eq_neg, deltaQuadForm_eq]
  ring

#print axioms deltaKQuadFormCorrected_eq_deltaQuadForm_sub_two_deltaPrime

/-- **Sanity check**: the correction is NOT vacuous — `deltaKQuadFormCorrected` and
`DeltaPrime.deltaQuadForm` genuinely DISAGREE on the witness config (`8` vs `-8` contribution from
the `Δ′` piece, `deltaPrimeQuadForm_conventions_differ_at_witnessU`, already banked), confirming
this file's correction is substantive, not a relabelling. -/
theorem deltaKQuadFormCorrected_ne_deltaQuadForm_at_witness :
    deltaKQuadFormCorrected witnessU deltaWitnessConfig ≠ deltaQuadForm witnessU deltaWitnessConfig := by
  rw [deltaKQuadFormCorrected_eq_deltaQuadForm_sub_two_deltaPrime,
    deltaPrimeQuadForm_witnessU_deltaWitnessConfig_eq]
  intro hcon
  have : (16 : ℝ) = 0 := by linarith [hcon]
  norm_num at this

#print axioms deltaKQuadFormCorrected_ne_deltaQuadForm_at_witness

/-! ## §4 — the `PlaqFnL2 L` topology closure (LAW-19: mirrors `BondSU2Space.lean` §1's ALREADY-
PROVED technique for `BondFnL2 L`, one index type over — `CovariantHjMinimizer.lean`'s own §8e
explicitly named `IsTopologicalAddGroup (SiteFnL2 L)`/(by the same construction) `PlaqFnL2 L` as
NOT yet closed; this closes it for `PlaqFnL2`, in this file, without editing either upstream file). -/

theorem plaqL2UniformSpace_bridge {L : PeriodicLatticeExtent} :
    (inferInstance : UniformSpace (PlaqFnL2 L)) =
      @PseudoMetricSpace.toUniformSpace (PlaqFnL2 L) inferInstance := by
  have h1 : (inferInstance : UniformSpace (PlaqFnL2 L)) =
      @PiLp.uniformSpace 2 (PeriodicLatticePlaquette L)
        (fun _ => SuTwo) (fun _ => instUniformSpaceSubtype) := rfl
  have h2 : (@PseudoMetricSpace.toUniformSpace (PlaqFnL2 L) inferInstance) =
      @PiLp.uniformSpace 2 (PeriodicLatticePlaquette L)
        (fun _ => SuTwo) (fun _ => PseudoMetricSpace.toUniformSpace) := rfl
  -- REPAIRED 2026-07-28 (`compute/sutwo_diamond`; out-of-scope one-line fix, DISCLOSED). The
  -- previous script was `rw [h1, h2]; congr 1; funext _; exact
  -- ambient_uniformSpace_eq_norm_uniformSpace`. After `SuTwoInner.lean` §4b closes the FIBRE
  -- diamond BY CONSTRUCTION (`uniformSpace_diamond_is_rfl`), `rw [h1, h2]` already closes the goal
  -- and every following tactic failed with "No goals to be solved". Rewritten as a pure TERM
  -- proof: identical content, and it compiles in both the pre- and post-repair worlds.
  have key : @PiLp.uniformSpace 2 (PeriodicLatticePlaquette L) (fun _ => SuTwo)
        (fun _ => instUniformSpaceSubtype)
      = @PiLp.uniformSpace 2 (PeriodicLatticePlaquette L) (fun _ => SuTwo)
        (fun _ => PseudoMetricSpace.toUniformSpace) :=
    congrArg
      (fun u : UniformSpace SuTwo =>
        @PiLp.uniformSpace 2 (PeriodicLatticePlaquette L) (fun _ => SuTwo) (fun _ => u))
      ambient_uniformSpace_eq_norm_uniformSpace
  exact h1.trans (key.trans h2.symm)

theorem plaqL2TopologicalSpace_bridge {L : PeriodicLatticeExtent} :
    (inferInstance : TopologicalSpace (PlaqFnL2 L)) =
      @UniformSpace.toTopologicalSpace (PlaqFnL2 L)
        (@PseudoMetricSpace.toUniformSpace (PlaqFnL2 L) inferInstance) :=
  congrArg (@UniformSpace.toTopologicalSpace (PlaqFnL2 L)) plaqL2UniformSpace_bridge

theorem plaqL2IsTopAddGroup_of_eq {t : TopologicalSpace (PlaqFnL2 L)}
    (ht : t = (@PseudoMetricSpace.toUniformSpace (PlaqFnL2 L) inferInstance).toTopologicalSpace) :
    @IsTopologicalAddGroup (PlaqFnL2 L) t _ := by
  subst ht
  infer_instance

theorem plaqL2ContinuousSMul_of_eq {t : TopologicalSpace (PlaqFnL2 L)}
    (ht : t = (@PseudoMetricSpace.toUniformSpace (PlaqFnL2 L) inferInstance).toTopologicalSpace) :
    @ContinuousSMul ℝ (PlaqFnL2 L) _ _ t := by
  subst ht
  infer_instance

noncomputable instance instIsTopAddGroupPlaqFnL2 : IsTopologicalAddGroup (PlaqFnL2 L) :=
  plaqL2IsTopAddGroup_of_eq plaqL2TopologicalSpace_bridge

noncomputable instance instContinuousSMulPlaqFnL2 : ContinuousSMul ℝ (PlaqFnL2 L) :=
  plaqL2ContinuousSMul_of_eq plaqL2TopologicalSpace_bridge

#print axioms plaqL2UniformSpace_bridge
#print axioms plaqL2TopologicalSpace_bridge
#print axioms plaqL2IsTopAddGroup_of_eq
#print axioms plaqL2ContinuousSMul_of_eq
#print axioms instIsTopAddGroupPlaqFnL2
#print axioms instContinuousSMulPlaqFnL2

/-! ## §5 — THE CORRECT `D_U^1 : BondFnL2 L →L[ℝ] PlaqFnL2 L`, and its Gram identity

Mirrors `BondSU2Space.lean` §3's bare-function-then-promote technique exactly (LAW-19), but for
`curlCovariantLM`/`curlValueCovariant` (BOND↔PLAQUETTE) rather than the SITE↔BOND gradient family —
this is the object §1 shows was missing. `curlCovariantLM` itself is REUSED, not rebuilt
(`CovariantOperators.lean`, already a bare `LinearMap`). -/

/-- **`D_U^1`, carried to `BondFnL2 L →ₗ[ℝ] PlaqFnL2 L`** — ordinary (non-bundled) composition
through the two `WithLp.linearEquiv`s, needing only `Module ℝ`, exactly as `BondSU2Space.lean`'s own
`bondLaplacianCovLM_L2` is built. -/
noncomputable def curlCovariantLM_L2 {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →ₗ[ℝ] PlaqFnL2 L :=
  (plaqFnEquiv L).symm.toLinearMap ∘ₗ (curlCovariantLM U) ∘ₗ (bondFnL2Equiv L).toLinearMap

/-- **THE MISSING OBJECT from §1**: `D_U^1 : BondFnL2 L →L[ℝ] PlaqFnL2 L`, a genuine
`ContinuousLinearMap` on the RIGHT carrier pair — this typechecks only because §4's `PlaqFnL2`
closure and `BondSU2Space.lean` §1's `BondFnL2` closure are BOTH in scope. -/
noncomputable def curlCovariantCLM_L2 {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] PlaqFnL2 L :=
  LinearMap.toContinuousLinearMap (curlCovariantLM_L2 U)

theorem curlCovariantCLM_L2_toLp {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    curlCovariantCLM_L2 U (WithLp.toLp 2 A) = WithLp.toLp 2 (curlValueCovariant U A) := by
  show (plaqFnEquiv L).symm (curlCovariantLM U ((bondFnL2Equiv L) (WithLp.toLp 2 A))) = _
  congr 1

/-- **`dstarDQuadForm` IS `‖D_U^1 · ‖²` on the correct carrier** — the Gram identity CMP99b (3.10)'s
`⟨A,D*DA⟩` term is DEFINED to be (`CovariantHj.lean`'s own comment: "built via the standard Gram
identity ... rather than constructing `D*` as an operator"), now PROVED on `BondFnL2 L`/`PlaqFnL2 L`
rather than merely asserted about the bare type. This is achieved WITHOUT needing an adjoint
operator (§6 explains why that route is blocked); the norm itself suffices for this identity. -/
theorem norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo) :
    ‖curlCovariantCLM_L2 U (WithLp.toLp 2 A)‖ ^ 2 = dstarDQuadForm U A := by
  have hns := real_inner_self_eq_norm_sq (curlCovariantCLM_L2 U (WithLp.toLp 2 A))
  rw [← hns, curlCovariantCLM_L2_toLp, inner_plaqFnL2_eq_covPlaqInner]
  rfl

#print axioms curlCovariantLM_L2
#print axioms curlCovariantCLM_L2
#print axioms curlCovariantCLM_L2_toLp
#print axioms norm_sq_curlCovariantCLM_L2_eq_dstarDQuadForm

/-! ## §5b — NON-DEGENERACY: `curlCovariantCLM_L2` is genuinely `U`-dependent, reusing the
ALREADY-BANKED witness `CovariantHj.curl_triv_at_witnessPlaquette`/`curl_witnessU_at_witnessPlaquette`
(LAW-19 — no new witness invented), at `witnessMElem`, which §2 confirms is NON-CENTRAL
(`Ad(witnessMElem) ≠ id`), satisfying the corrected criterion. -/

theorem curlValueCovariant_myTrivialU_ne_witnessU_at_witnessPlaquette :
    curlValueCovariant myTrivialU myWitnessConfig witnessPlaquette ≠
      curlValueCovariant witnessU myWitnessConfig witnessPlaquette := by
  rw [curl_triv_at_witnessPlaquette, curl_witnessU_at_witnessPlaquette]
  intro hcon
  apply suTwoWitness_ne_zero
  have h2 : (2 : ℝ) • suTwoWitness = 0 := by
    linear_combination (norm := module) (1 : ℝ) • hcon
  rcases smul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

/-- **THE HEADLINE NON-VACUITY WITNESS for `curlCovariantCLM_L2`**: it genuinely differs across two
configurations of the background, at a witness whose non-identity link (`witnessMElem`) is
NON-CENTRAL (§2), not merely far from `1` as a group element. -/
theorem curlCovariantCLM_L2_genuinely_U_dependent :
    curlCovariantCLM_L2 (L := AdmissibleSubspace.witnessL) myTrivialU
        (WithLp.toLp 2 myWitnessConfig) ≠
      curlCovariantCLM_L2 witnessU (WithLp.toLp 2 myWitnessConfig) := by
  rw [curlCovariantCLM_L2_toLp, curlCovariantCLM_L2_toLp]
  intro hcon
  apply curlValueCovariant_myTrivialU_ne_witnessU_at_witnessPlaquette
  have h := congrArg (plaqFnEquiv AdmissibleSubspace.witnessL) hcon
  rw [plaqFnEquiv_toLp, plaqFnEquiv_toLp] at h
  exact congrFun h witnessPlaquette

#print axioms curlValueCovariant_myTrivialU_ne_witnessU_at_witnessPlaquette
#print axioms curlCovariantCLM_L2_genuinely_U_dependent

/-! ## §6 — THE WALL: `.adjoint`/Riesz-representation routes to promote `D*D`/`Δ′` to genuine
OPERATORS (not just quadratic forms) hit the SAME ambient-vs-norm-topology diamond `PILP_BRIDGE.md`
found for bundled `∘L`/`∘ₗ` composition — extended here to bundled APPLICATION, a strictly stronger
(and previously undocumented) failure mode. Reproduced directly below, not merely asserted:

1. `(curlCovariantCLM_L2 U).adjoint` **fails to even ELABORATE** (not merely fails to `.comp`):
   `ContinuousLinearMap.adjoint`'s defining section (`Mathlib.Analysis.InnerProductSpace.Adjoint`)
   fixes `variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]` and derives `E`'s topology
   INTERNALLY from those instances (i.e. from `PiLp.normedAddCommGroup`'s own
   `PseudoMetricSpace.toUniformSpace.toTopologicalSpace`), NOT from whatever `TopologicalSpace E`
   ambient search finds independently (`PiLp.topologicalSpace`, the Pi-style one, built compositionally
   from each fiber's AMBIENT `TopologicalSpace SuTwo` — the subtype-of-`Matrix` one, per
   `SuTwoInner.lean`'s own diamond). `curlCovariantCLM_L2 U`, built via `LinearMap.toContinuousLinearMap`
   under the AMBIENT topology (the only route `BondSU2Space.lean` §1's bridge makes available), has
   `PiLp.topologicalSpace` baked into ITS type. Applying `.adjoint` to it produces the error
   (reproduced directly, `lake env lean` on a scratch probe, this dispatch):
   `synthesized type class instance is not definitionally equal to expression inferred by typing rules,
   synthesized PiLp.topologicalSpace 2 fun x => ↥SuTwo, inferred
   PseudoMetricSpace.toUniformSpace.toTopologicalSpace` — at the very call site, before any `.comp`.
2. The SAME failure reproduces for `innerSL`-based Riesz-representation composition (the
   `InnerProductSpace.toDual` family): `(innerSL ℝ) A ∘SL curlCovariantCLM_L2 U` fails identically
   ("Application type mismatch... expected `?m.33 →SL[?m.30] BondFnL2 L`... has type `BondFnL2 L →L[ℝ]
   PlaqFnL2 L`"), confirming this is NOT specific to `.adjoint`'s particular definition but to EVERY
   Mathlib construction that consumes a bundled `E →L[𝕜] F` under the InnerProductSpace-derived
   topology rather than producing one under it.
3. `PILP_BRIDGE.md`'s own diagnosis ("a propositional bridge does not make two
   syntactically-different-but-propositionally-equal instance terms `rfl`/defeq to each other; `rw`/
   `▸` need the mismatched instance to appear syntactically in the goal, which it does not once a
   bundled structure's type has already been fixed") explains WHY §4's bridge (which only proves
   PROPOSITIONAL equality) cannot rescue this: the mismatch here is not even reachable by `rw`/`▸`
   inside a tactic block, since it is an ELABORATION-time unification failure on `.adjoint`'s own
   ARGUMENT, before any goal exists to rewrite.

**Consequently**: the only route this tree has EVER successfully used to promote a covariant
adjoint-like object to a genuine LinearMap (`CovariantHjMinimizer.lean` §5's
`gradCovariantAdjointValue`, `BondSU2Space.lean` §3's bare-function composition) is EXPLICIT,
HANDWRITTEN combinatorial construction on the BARE type, entirely avoiding `ContinuousLinearMap.adjoint`/
`InnerProductSpace.toDual`. §7 names the two such constructions this assembly needs. -/

/-! ## §7 — THE TWO NAMED, LOAD-BEARING RESIDUAL LEMMAS

Both follow the PROVEN technique of `CovariantHjMinimizer.lean` §5 (`gradCovariantAdjointValue`,
`covBondInner_gradValueCovariant_eq_covSiteInner`) — bare `Finset.sum` construction plus an explicit
Gram-identity proof by index-reindexing, NEVER `ContinuousLinearMap.adjoint`/`toDual` (§6). Neither
is attempted to completion in this dispatch's budget; each is stated here as the PRECISE target a
follow-up construction must hit, which is itself the deliverable (`problem/PROBLEM.md`'s
"named-missing-primitive" disposition).

**Residual 1 — `curlCovariantAdjointValue`, the explicit combinatorial adjoint of the covariant
curl.** Needed signature and defining property (NOT proved here):

```
noncomputable def curlCovariantAdjointValue
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (F : PeriodicLatticePlaquette L → SuTwo) (b : Bond L) : SuTwo := ...
theorem covPlaqInner_curlValueCovariant_eq_covBondInner
    (U : ...) (A : Bond L → SuTwo) (F : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner (curlValueCovariant U A) F = covBondInner A (curlCovariantAdjointValue U F) := ...
```

Scope of the combinatorics needed (measured directly from `curlValueCovariant`'s own four
`AprimeXY`/`AprimeYZ`/`AprimeZW`/`AprimeWX` sub-terms, `DeltaPrime.lean` §2): each bond `(x,τ)`
appears in exactly `2(d-1) = 4` plaquettes in `d=3` (2 for each of the other two directions `ν≠τ`,
in one of two roles depending on whether `τ` is the smaller or larger of the pair) — MORE case
branches than `gradCovariantAdjointValue`'s single-role (inflow/outflow) sum over `μ`, since the
curl has FOUR roles (`XY`/`YZ`/`ZW`/`WX`) rather than two, each requiring its own reindexing
bijection and `RMap`-inverse bookkeeping. This is a genuinely new, comparable-in-size construction
to `CovariantHjMinimizer.lean` §5 itself, not a small gap.

**Residual 2 — the `Δ′` operator.** `deltaPrimeQuadFormTransported` is a genuine quadratic form
(its two components are, respectively, the square of an `ℝ`-linear functional of `A` and a
bilinear-in-pairs commutator sum, both built from `ℝ`-linear pieces `AprimeXY`/`AprimeYZ`/`AprimeZW`/
`AprimeWX`). Its associated SYMMETRIC BILINEAR FORM can be built directly (NOT via subtraction-based
polarization, which would need re-proving the parallelogram identity) by the explicit symmetrization
`bilin(A,B,p) := (1/2)(mixed(A,B,p) + mixed(B,A,p))` where `mixed` substitutes `A` for the "left"
factor and `B` for the "right" factor in each product PRIOR to symmetrization — a construction that
is mechanical but was not attempted to completion here (comparable in size to `DeltaPrime.lean`
itself, ~1000 lines, given the 6-term commutator sum). Its Riesz-style representation as a vector
must ALSO avoid `InnerProductSpace.toDual` (§6) — the finite-dimensional analogue (representing a
bilinear form on `Bond L → SuTwo` via `covBondInner` and the FINITE basis `{(b,e_i)}` the tree
already has, `SuTwoInner.lean`'s `e1`/`e2`/`e3`) is the correct bare-type-only route, not attempted
here either.

## §8 — THE ASSEMBLY LOGIC, proved conditional on the two residuals (honest, non-circular)

The content below is a genuine but SMALL fact (bilinearity of the inner product, not the hard
mathematics named in §7) — stated explicitly, not padded, so a reader does not mistake it for having
closed §7. -/

/-- **Assembly is sound**: GIVEN any two operators `T1 T2 : BondFnL2 L →L[ℝ] BondFnL2 L` whose
quadratic forms (against the bare-type inner product, transported via `WithLp.toLp`) reproduce
`dstarDQuadForm`/`deltaPrimeQuadFormTransported` respectively — i.e. §7's Residual 1/2, PROMOTED to
`BondFnL2 L` the same way §5 promotes the curl — their SUM's quadratic form reproduces
`deltaKQuadFormCorrected`, §0's settled target. This is the ENTIRE content the dispatch's
`deltaKFullCLM := bondLaplacianCovCLM_L2 U + deltaPrimeCLM U` step needed, made precise and correct
(with the RIGHT `T1`, not `bondLaplacianCovCLM_L2`, per §1). -/
theorem deltaKFullCLM_assembly_sound {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (T1 T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hT1 : ∀ A : Bond L → SuTwo,
      (inner ℝ (WithLp.toLp 2 A) (T1 (WithLp.toLp 2 A)) : ℝ) = dstarDQuadForm U A)
    (hT2 : ∀ A : Bond L → SuTwo,
      (inner ℝ (WithLp.toLp 2 A) (T2 (WithLp.toLp 2 A)) : ℝ) = deltaPrimeQuadFormTransported U A)
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A) ((T1 + T2) (WithLp.toLp 2 A)) : ℝ) = deltaKQuadFormCorrected U A := by
  unfold deltaKQuadFormCorrected
  rw [add_apply, inner_add_right, hT1, hT2]

#print axioms deltaKFullCLM_assembly_sound

/-! ## §9 — residuals named precisely, again, in one place (mechanical propagation target)

1. **§7 Residual 1** (`curlCovariantAdjointValue` + its Gram identity) — the explicit combinatorial
   adjoint of the covariant curl. NOT attempted to completion.
2. **§7 Residual 2** (the `Δ′` operator, via bilinear-form symmetrization + bare-basis Riesz
   representation, NOT `InnerProductSpace.toDual`). NOT attempted to completion.
3. **§1's finding should propagate**: any consumer that currently treats `bondLaplacianCovCLM_L2`
   as "the `D*D`/`DD*` piece of `Δ_k(U)`" (its own docstring's characterization) is citing the wrong
   object for that role — it remains a valid, `U`-dependent, nonnegative, self-adjoint (w.r.t.
   `covBondInner`) operator in its own right, just not CMP99b (3.10)'s `D*D`.
4. `deltaKFullCLM` itself (the dispatch's literal named deliverable) is **not** constructed as an
   unconditional `H →L[ℝ] H` term in this file — §8's theorem is the closest honest substitute
   (sound assembly LOGIC, conditional on the two named residuals). Once Residual 1/Residual 2 land,
   `deltaKFullCLM U := T1 U + T2 U` and `deltaKFullCLM_assembly_sound` specialize immediately to the
   unconditional statement, with NO further mathematical content needed — the join step itself is
   trivial once its two ingredients exist; the ingredients are what is hard.
-/

end AdalyFormal.Balaban.DeltaKFull
