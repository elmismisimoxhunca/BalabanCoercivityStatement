/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CStarDeltaKCOperator
import AdalyFormal.Balaban.DeltaPrime
import AdalyFormal.Balaban.DeltaKU
-- §N (normalization repair) consumes `NormalizationAudit`'s already-kernel-checked
-- `deltaPrimeQuadFormNormalizedTransported_eq_half_transported` rather than re-deriving it (LAW-19).
import AdalyFormal.Balaban.NormalizationAudit

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-
================================================================================================
 CONVICTION BANNER — filed 2026-07-26, de-correlated Sol prosecution
 `compute/sol_deltaprime/SOL_PROSECUTION_DELTAPRIME.md` — verdict CONVICTED on source fidelity
================================================================================================
TWO convictions, both answered in §N of this file.

(1) FACTOR-2 SOURCE-FIDELITY DEFECT.  CMP99b printed p.392, same page as (3.10), same convention:
    "Let us recall that the trace is normalized, i.e., `tr 1 = 1`."  For `N = 2`, source
    `tr = (1/2)·Tr`; Mathlib's `Matrix.trace` is `Tr` with `Tr 1 = 2`.  `traceForm` (§2 below) and
    both `DeltaPrime.deltaPrime*Transported` terms use RAW `Matrix.trace`.  Since
    `CovariantHj.dstarDQuadForm` is built entirely from `SuTwoInner.hsInner = -(1/2)·Tr`, the `D*D`
    half ALREADY carries the source normalization, so the RELATIVE coefficient of `Δ_k = D*D + Δ′`
    is wrong by 2.  Sol's compiled witness: this file's `Δ′` at `witnessU`/`deltaWitnessConfig` is
    `-8`; the source-normalized value is `-4`; proved unequal.
    ⇒ `inner_cStarDeltaKC_unconditional` and `bondAdjoint_cStarDeltaKC_unconditional` AS ORIGINALLY
      STATED (§7) are identities about `D*D + 2·Δ′_source`, NOT about source-normalized `Δ_k`.
      They are RETAINED (true of the raw object, and their names are cited elsewhere) but are
      SUPERSEDED for source-fidelity purposes by the `…Normalized…` theorems of §N.

(2) FORCED-ASSERTION DEFECT.  `deltaPrimeBil := symm(raw) = (1/2)•(raw + raw.flip)` is symmetric
    for EVERY raw bilinear form — Sol compiled this for an arbitrary form, for `0`, and for
    arbitrary nonzero garbage.  So `deltaPrimeBil_symm`, `deltaPrimeBilL2_symm`,
    `bondAdjoint_deltaPrimeOp`, `inner_deltaPrimeOp_symm`, `inner_deltaPrimeCLM_symm`,
    `deltaKCLM_symm`, `bondAdjoint_cStarDeltaKC_unconditional` (7 declarations) are S82-FORCED
    consistency facts and are NOT evidence that the source expansion was transcribed correctly.
    The builder record's sentence "No assertion in the module is algebraically forced in the S82
    sense" (`compute/deltaprime_operator/RECORD.md:68-71`) is CONVICTED and is corrected in §N.
    Sol's sharp point, recorded so it is not re-answered wrongly: "16/16 mutations killed" does NOT
    answer this, because mutation M12 died of INCOHERENCE (it changed the operator while leaving
    surrounding restatements aimed at the old form), and a COHERENT zero-form substitution stays
    self-adjoint.  §N supplies non-forced source checks that survive a COHERENT substitution.

(3) `η` SCOPE.  CMP99b's printed (3.10) carries the weight `η^d η^{-2}`; the Lean types here have
    no `η` binder and no such weight.  Every "(3.10)" billing in this file therefore means the
    `η = 1` (unit-spacing) SPECIALIZATION of (3.10).  Stated inline at each billing site in §N.

INTENDED REPAIR, and the option taken: **OPTION (b)** — the raw `traceForm`/`bilPlaq`/
`deltaPrimeBilRaw`/`deltaPrimeBil`/`deltaPrimeOp`/`deltaPrimeCLM` layer is KEPT BIT-FOR-BIT (no
existing declaration changes meaning), and §N adds a NORMALIZED wrapper layer
(`deltaPrimeBilNormalized`, `deltaPrimeBilL2Normalized`, `deltaPrimeOpNormalized`,
`deltaPrimeCLMNormalized`, `deltaKCLMNormalized`) whose diagonal is
`NormalizationAudit.deltaPrimeQuadFormNormalizedTransported`, together with re-proved
`inner_cStarDeltaKC_normalized_unconditional` / `bondAdjoint_cStarDeltaKC_normalized_unconditional`.
Option (a) — inserting `1/2` into `traceForm` — was REJECTED because `traceForm` is a generic
`ℝ`-bilinear trace pairing also used to state `bilPlaq_atoms` and every `*_diag` `rfl`-pin against
`DeltaPrime.lean`'s RAW terms; changing it would silently redefine those pins and make them assert
something the imported `DeltaPrime.lean` does not say.
================================================================================================
-/

/-!
# `Δ′` AS AN OPERATOR — the last open input to `C*Δ_kC` — `[DELTAPRIME-OPERATOR]`

## §0 — WHAT THIS MODULE IS

`Balaban/CStarDeltaKCOperator.lean` §10-§11 assembles `C*Δ_kC` as a genuine operator **conditional on
exactly one typed input**:

    T2  : BondFnL2 L →L[ℝ] BondFnL2 L
    hT2 : ∀ A, ⟪toLp A, T2 (toLp A)⟫ = DeltaPrime.deltaPrimeQuadFormTransported U A

This module **supplies it**, and therefore makes `CStarDeltaKCOperator.inner_cStarDeltaKCCLM_eq`
UNCONDITIONAL (§7). The construction is: write `Δ′`'s quadratic form out as a *bilinear* form on the
bare carrier `Bond L → SuTwo`, term by term against `DeltaPrime.lean`'s own definitions
(§1-§4); symmetrize it (§4); transport it to `BondFnL2 L` (§5); and push it through
`CStarDeltaKCOperator.bilinToOperatorBond`, which turns any bilinear form on that carrier into an
operator and any SYMMETRIC one into a self-adjoint operator (§6).

`Δ′`'s form is not a norm-square, so no adjoint produces it; the whole content is the explicit
bilinear expansion. `bilinToOperatorBond` (the Riesz half) is REUSED, not rebuilt (LAW-19).

## §0a — TERM-BY-TERM CORRESPONDENCE (§S class 58: nothing dropped, and the map is stated)

`DeltaPrime.deltaPrimeQuadFormTransported U A = ∑ p, (deltaPrimeFirstTermTransported U A p +
deltaPrimeSecondTermTransported U A p)`. Verbatim from `DeltaPrime.lean`, the two summands are

    deltaPrimeFirstTermTransported U A p =
      (Matrix.trace ((I • ↑(curlValueCovariant U A p)) * (I • ↑(curlValueCovariant U A p))
        * (reHolonomy U p - 1))).re
    deltaPrimeSecondTermTransported U A p =
      (Matrix.trace (commutatorMatrixSumTransported U A p * imHolonomy U p)).re
    commutatorMatrixSumTransported U A p =
      I • ((a₁a₂ - a₂a₁) + (a₁a₃ - a₃a₁) + (a₁a₄ - a₄a₁)
            + (a₂a₃ - a₃a₂) + (a₂a₄ - a₄a₂) + (a₃a₄ - a₄a₃))
      with  a₁ = I • ↑(AprimeZW U A p),  a₂ = I • ↑(AprimeWX A p),
            a₃ = I • ↑(AprimeXY A p),    a₄ = I • ↑(AprimeYZ U A p)

and the correspondence with this module is:

| `DeltaPrime` object | here | pinned by |
|---|---|---|
| `↑(AprimeZW U A p)` | `a1LM U p` | `a1LM_apply` (`rfl`) |
| `↑(AprimeWX A p)` | `a2LM p` | `a2LM_apply` (`rfl`) |
| `↑(AprimeXY A p)` | `a3LM p` | `a3LM_apply` (`rfl`) |
| `↑(AprimeYZ U A p)` | `a4LM U p` | `a4LM_apply` (`rfl`) |
| `I • ↑(Aprime…)` (the `aᵢ`) | `b1LM`-`b4LM` | `bᵢLM` definitions |
| `↑(curlValueCovariant U A p)` | `curlMatLM U p` | `curlMatLM_apply` (`rfl`) |
| first term | `firstBilPlaq U p` | `firstBilPlaq_diag` (`rfl`) |
| each of the SIX brackets `(aᵢaⱼ - aⱼaᵢ)`, `i<j`, traced against `imHolonomy U p` | `pairBil U p bᵢ bⱼ` (six summands of `secondBilPlaq`) | `secondBilPlaq_diag` |
| `∑ p` over ALL plaquettes | `∑ p` in `deltaPrimeBilRaw` | `deltaPrimeBilRaw_diag` |

The `≺`-order and hence the six pairs are `DeltaPrime.lean`'s own (`a₁ = A′(z,w) ≺ a₂ = A′(w,x) ≺
a₃ = A′(x,y) ≺ a₄ = A′(y,z)`, read there off CMP99b printed p.390). Six pairs, each contributing
BOTH matrix orderings, so `secondBilPlaq` has exactly `12` elementary trace atoms and `bilPlaq`
exactly `13` — the same count as the source expression. §9 exhibits a background/field pair at which
the commutator half is NONZERO, so its presence is not merely asserted.

## §0b — WHAT IS DIAGONAL-ONLY, AND WHAT IS NOT (disclosure carried forward)

The sandwich lane's finding, restated because it is load-bearing here: **`hT2` constrains only the
DIAGONAL** `⟪A, T2 A⟫`, so it fixes `Δ′`'s quadratic FORM and NOT the operator — `T2 + S` satisfies
it for any skew `S`. Consequently:

* **DIAGONAL-ONLY conclusions** (they say nothing about a skew part, and would survive replacing
  `deltaPrimeCLM U` by `deltaPrimeCLM U + S`): `inner_deltaPrimeCLM_eq` (= `hT2` itself),
  `inner_deltaKCLM_eq`, `inner_cStarDeltaKCCLM_unconditional`, `deltaPrimeOp_ne_zero_at_witnessU`.
* **NOT diagonal-only**: the symmetry of the bilinear form (`deltaPrimeBil_symm`) and the
  self-adjointness it yields (`bondAdjoint_deltaPrimeOp`, `deltaKCLM_symm`,
  `bondAdjoint_cStarDeltaKC_unconditional`). Symmetry is PROVED here from the construction
  (`deltaPrimeBil` is `½(raw + raw.flip)` by definition), never assumed — and it is exactly the
  `hsym` hypothesis that `CStarDeltaKCOperator.bondAdjoint_cStarDeltaKC` needs, i.e. the hypothesis
  that pins `T2` uniquely. So this module supplies the uniqueness-pinning datum as well as `hT2`.
  **[S75 CORRECTION, conviction banner (2) — added, nothing struck, because every sentence above is
  literally true and none of it was the defect.** What was wrong was the EVIDENTIARY reading. All
  SEVEN of `deltaPrimeBil_symm`, `deltaPrimeBilL2_symm`, `bondAdjoint_deltaPrimeOp`,
  `inner_deltaPrimeOp_symm`, `inner_deltaPrimeCLM_symm`, `deltaKCLM_symm`,
  `bondAdjoint_cStarDeltaKC_unconditional` are **S82-ALGEBRAICALLY FORCED**: `½(raw + raw.flip)` is
  symmetric for EVERY raw bilinear form, so Sol compiled the identical conclusions for the zero form
  and for arbitrary nonzero garbage. "NOT diagonal-only" is TRUE and "independently source-tested" is
  FALSE, and the two must not be read as the same claim. §N.7 supplies checks that DO fail under a
  COHERENT substitution of a different bilinear form.**]**
* `deltaPrimeOp_trivialU` (`Δ′`'s operator VANISHES at the flat background) is *stronger* than a
  diagonal statement and is derived from the diagonal by polarization, which is legitimate only
  BECAUSE the form is symmetric — the derivation is spelled out and cites the symmetry.

## §0c — NO COERCIVITY CLAIM, AND THE CONE

No coercivity, positivity, or lower bound of any kind is stated for `C*Δ_kC` here.
`CStarDeltaKCOperator` §7(a) records that the naive such target is *proved false*
(`[CSTAR-LEVEL-MISMATCH]`) and that `[CSTAR-SCHUR-GAP]`'s ordering runs the wrong way; nothing below
touches either. `Δ_k`'s positive semidefiniteness is NOT proved and NOT assumed: §8 exhibits a
background at which `Δ′`'s own diagonal is NEGATIVE (`-8`), so `inner_cStarDeltaKC_nonneg`'s
hypothesis is not available and is not invoked.

**Cone**: this module imports only `CStarDeltaKCOperator` (→ `FullReparamC`, `DeltaKFull`) and
`DeltaPrime`. It does NOT import `DeltaKSuTwoAssembly` (whose `deltaJ − a‖B‖²` double-subtracts the
averaging mass), `CStarDeltaKCCompose`, `CStarDeltaKCCoercive`, or `CStarLevelCorrected`, and neither
does anything it imports; measured, `compute/deltaprime_operator/cone.txt`. It also uses the
TRANSPORTED `Δ′` throughout — never `deltaPrimeQuadForm`/`deltaQuadForm`, whose sign
`DeltaPrime.deltaPrimeQuadFormTransported_eq_neg` proves is opposite.
-/

namespace AdalyFormal.Balaban.DeltaPrimeOperator

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant suTwo
  curlCovariantLM suTwoWitness suTwoWitnessVal witnessM witnessMElem witnessU witnessPlaquette
  RMap_one RMap_witnessMElem witnessU_at_x_mu witnessU_at_x_nu)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL witnessY)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHj (myWitnessPlaquette2 plaquette_snd_dir_ne_zero
  eq_witnessPlaquette_or_myWitnessPlaquette2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (bilinToOperatorBond inner_bilinToOperatorBond
  bondAdjoint bondAdjoint_bilinToOperatorBond bondAdjoint_eq_self_iff dstarDCLM
  inner_dstarDLM_symm dstarDLM cStarDeltaKC cStarDeltaKCCLM inner_cStarDeltaKCCLM_eq
  inner_cStarDeltaKC_eq bondAdjoint_cStarDeltaKC reparamCL2 curlAdjoint inner_curlAdjoint_right
  curlCovariantLM_L2_toLp inner_dstarDCLM_eq_dstarDQuadForm inner_cStarMC_self reparamCL2_apply
  cStarMC)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm)
open AdalyFormal.Balaban.NormalizationAudit (deltaPrimeQuadFormNormalizedTransported
  deltaPrimeQuadFormNormalizedTransported_eq_half_transported deltaKQuadFormNormalizedCorrected
  deltaKQuadFormNormalizedCorrected_eq dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four
  deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero)
open AdalyFormal.Balaban.DeltaKU (curlCovariantAdjointValue deltaKUOp deltaKUOp_apply
  covPlaqInner_curlValueCovariant_eq_covBondInner)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — ELEMENTARY ℝ-LINEAR MAPS INTO `Matrix (Fin 2) (Fin 2) ℂ`

`SuTwo` is an ℝ-submodule of `Matrix (Fin 2) (Fin 2) ℂ`, so `Submodule.subtype suTwo` is an
ℝ-linear map into the matrices; composing it with a projection (and, where the source formula has
one, with `RMap`) bundles each of `Δ′`'s constituent *linear-in-`A`* matrix reads. Bundling is what
makes the bilinearity of the whole expression a `by`-free consequence of the module structure on
`→ₗ` instead of a hand proof per term.
-/

/-- `A ↦ ↑(A b)` — bond evaluation, into the matrices. -/
noncomputable def bondMatLM (b : Bond L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Submodule.subtype suTwo) ∘ₗ (LinearMap.proj b : (Bond L → SuTwo) →ₗ[ℝ] SuTwo)

theorem bondMatLM_apply (b : Bond L) (A : Bond L → SuTwo) :
    bondMatLM b A = ((A b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- `A ↦ ↑(R(V)(A b))` — the transported bond read appearing in `AprimeYZ`/`AprimeZW`. -/
noncomputable def bondMatRLM (V : Matrix.specialUnitaryGroup (Fin 2) ℂ) (b : Bond L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Submodule.subtype suTwo) ∘ₗ (RMap V) ∘ₗ (LinearMap.proj b : (Bond L → SuTwo) →ₗ[ℝ] SuTwo)

theorem bondMatRLM_apply (V : Matrix.specialUnitaryGroup (Fin 2) ℂ) (b : Bond L)
    (A : Bond L → SuTwo) :
    bondMatRLM V b A = ((RMap V (A b) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- `A ↦ ↑((D_U A)(p))` — the covariant curl at one plaquette, into the matrices.
`curlCovariantLM` is REUSED from `CovariantOperators.lean` (LAW-19), so the linearity of the curl is
not re-proved here. -/
noncomputable def curlMatLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Submodule.subtype suTwo) ∘ₗ
    (LinearMap.proj p : (PeriodicLatticePlaquette L → SuTwo) →ₗ[ℝ] SuTwo) ∘ₗ
      (curlCovariantLM U)

theorem curlMatLM_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    curlMatLM U p A = ((curlValueCovariant U A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- `M ↦ Complex.I • M`, as an ℝ-linear map. This is the `φ`-transport factor
`DeltaPrime.lean` §11 applies at the MATRIX level (because `i·(anti-Hermitian)` leaves `SuTwo`);
it is ℝ-linear, not ℂ-linear-in-disguise, which is why it composes with the maps above. -/
noncomputable def smulILM : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun M := Complex.I • M
  map_add' _ _ := smul_add _ _ _
  map_smul' c M := smul_comm (Complex.I) c M

theorem smulILM_apply (M : Matrix (Fin 2) (Fin 2) ℂ) : smulILM M = Complex.I • M := rfl

/-- **THE ELEMENTARY BILINEAR ATOM** `(A,B) ↦ Re tr(f A · g B · M)`, for a FIXED matrix `M` and two
bundled linear reads `f`, `g`. Every term of `Δ′`'s bilinear form is one of these or the `flip` of
one, so bilinearity is established once here and never again. -/
noncomputable def traceForm (M : Matrix (Fin 2) (Fin 2) ℂ)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun A B => (Matrix.trace (f A * g B * M)).re)
    (fun _ _ _ => by simp [Matrix.add_mul])
    (fun _ _ _ => by
      simp only [map_smul, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul])
    (fun _ _ _ => by simp [Matrix.mul_add, Matrix.add_mul])
    (fun _ _ _ => by
      simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re,
        smul_eq_mul])

theorem traceForm_apply (M : Matrix (Fin 2) (Fin 2) ℂ)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo) :
    traceForm M f g A B = (Matrix.trace (f A * g B * M)).re := rfl

#print axioms bondMatLM
#print axioms bondMatLM_apply
#print axioms bondMatRLM
#print axioms bondMatRLM_apply
#print axioms curlMatLM
#print axioms curlMatLM_apply
#print axioms smulILM
#print axioms smulILM_apply
#print axioms traceForm
#print axioms traceForm_apply

/-! ## §2 — THE FOUR `A′` COMPONENTS, PINNED TO `DeltaPrime`'s OWN DEFINITIONS BY `rfl`

Indices follow `DeltaPrime.lean`'s `≺`-order verbatim: `a₁ = A′(z,w)` (`AprimeZW`),
`a₂ = A′(w,x)` (`AprimeWX`), `a₃ = A′(x,y)` (`AprimeXY`), `a₄ = A′(y,z)` (`AprimeYZ`). The two
negations are the source's own antisymmetry sign flips (`A(z,w) = -A(w,z)`, `A(w,x) = -A(x,w)`), not
a convention introduced here.
-/

/-- `a₁ = ↑(A′(z,w)) = -↑(R(U(x,ν))·A(shift_ν x, μ))`. -/
noncomputable def a1LM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  -(bondMatRLM (U (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))

/-- `a₂ = ↑(A′(w,x)) = -↑(A(x,ν))`. -/
noncomputable def a2LM (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  -(bondMatLM (p.1, p.2.1.2))

/-- `a₃ = ↑(A′(x,y)) = ↑(A(x,μ))`. -/
noncomputable def a3LM (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  bondMatLM (p.1, p.2.1.1)

/-- `a₄ = ↑(A′(y,z)) = ↑(R(U(x,μ))·A(shift_μ x, ν))`. -/
noncomputable def a4LM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  bondMatRLM (U (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)

theorem a1LM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a1LM U p A = ((AprimeZW U A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem a2LM_apply (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a2LM p A = ((AprimeWX A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem a3LM_apply (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a3LM p A = ((AprimeXY A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem a4LM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a4LM U p A = ((AprimeYZ U A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- The `φ`-transported components `bᵢ = I • aᵢ`, exactly `commutatorMatrixSumTransported`'s own
`a1`-`a4` `let`-bindings. -/
noncomputable def b1LM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  smulILM ∘ₗ a1LM U p

noncomputable def b2LM (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := smulILM ∘ₗ a2LM (L := L) p

noncomputable def b3LM (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := smulILM ∘ₗ a3LM (L := L) p

noncomputable def b4LM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  smulILM ∘ₗ a4LM U p

#print axioms a1LM
#print axioms a2LM
#print axioms a3LM
#print axioms a4LM
#print axioms a1LM_apply
#print axioms a2LM_apply
#print axioms a3LM_apply
#print axioms a4LM_apply
#print axioms b1LM
#print axioms b2LM
#print axioms b3LM
#print axioms b4LM

/-! ## §3 — THE PER-PLAQUETTE BILINEAR FORM

`pairBil f g` is ONE of `commutatorMatrixSumTransported`'s six brackets, traced against
`imHolonomy U p`, with the two matrix orderings kept separate so that each is bilinear in `(A,B)`:
the source bracket `aᵢaⱼ - aⱼaᵢ` becomes `f(A)g(B) - g(B)f(A)`, and the second of those is a `flip`
because its `A`-dependent factor sits on the RIGHT. The formula's own leading `I` (present in
CMP99b (3.10) itself, NOT part of the `φ`-transport) is the extra `smulILM` in front of the first
argument of each `traceForm`; `Matrix.smul_mul` is what lets it be moved there, and that move is
discharged inside `secondBilPlaq_diag`, not assumed.
-/

/-- One of the six brackets, traced against `Im U(∂p)`. -/
noncomputable def pairBil
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  traceForm (imHolonomy U p) (smulILM ∘ₗ f) g
    - (traceForm (imHolonomy U p) (smulILM ∘ₗ g) f).flip

/-- CMP99b (3.10)'s FIRST `Δ′` term, as a bilinear form. **BILLING QUALIFIED (S75, conviction
banner (1)+(3)):** this is the `η = 1` specialization of (3.10) — the printed formula carries the
weight `η^d η^{-2}` and this type has no `η` binder — and it uses RAW `Matrix.trace`, i.e. it is
`2 ×` the source-normalized term (source p.392: `tr 1 = 1`). The source-normalized object is §N's
`deltaPrimeBilNormalized`. -/
noncomputable def firstBilPlaq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  traceForm (reHolonomy U p - 1) (smulILM ∘ₗ curlMatLM U p) (smulILM ∘ₗ curlMatLM U p)

/-- CMP99b (3.10)'s SECOND `Δ′` term, as a bilinear form: all SIX pairs `i<j` of
`{1,2,3,4}` — `(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)` — in `DeltaPrime`'s own order.
**BILLING QUALIFIED exactly as `firstBilPlaq` above:** `η = 1` specialization, RAW trace (`2 ×`
source-normalized). -/
noncomputable def secondBilPlaq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  pairBil U p (b1LM U p) (b2LM p) + pairBil U p (b1LM U p) (b3LM p)
    + pairBil U p (b1LM U p) (b4LM U p) + pairBil U p (b2LM p) (b3LM p)
    + pairBil U p (b2LM p) (b4LM U p) + pairBil U p (b3LM p) (b4LM U p)

/-- The full per-plaquette bilinear summand of `Δ′`. -/
noncomputable def bilPlaq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  firstBilPlaq U p + secondBilPlaq U p

theorem pairBil_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo) :
    pairBil U p f g A B
      = (Matrix.trace (smulILM (f A) * g B * imHolonomy U p)).re
        - (Matrix.trace (smulILM (g B) * f A * imHolonomy U p)).re := rfl

theorem firstBilPlaq_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    firstBilPlaq U p A B
      = (Matrix.trace (smulILM (curlMatLM U p A) * smulILM (curlMatLM U p B)
          * (reHolonomy U p - 1))).re := rfl

theorem secondBilPlaq_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    secondBilPlaq U p A B
      = pairBil U p (b1LM U p) (b2LM p) A B + pairBil U p (b1LM U p) (b3LM p) A B
        + pairBil U p (b1LM U p) (b4LM U p) A B + pairBil U p (b2LM p) (b3LM p) A B
        + pairBil U p (b2LM p) (b4LM U p) A B + pairBil U p (b3LM p) (b4LM U p) A B := rfl

theorem bilPlaq_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    bilPlaq U p A B = firstBilPlaq U p A B + secondBilPlaq U p A B := rfl

/-- **THE ATOM COUNT, KERNEL-CHECKED** (§S class 3: the docstring's "13 atoms = 1 + 6 brackets × 2
orderings" is asserted here as an identity, not only in prose). The right-hand side is written out
atom by atom: one first-term trace, then the six brackets `(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)`, each
as a DIFFERENCE of its two matrix orderings. -/
theorem bilPlaq_atoms
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    bilPlaq U p A B
      = (Matrix.trace (smulILM (curlMatLM U p A) * smulILM (curlMatLM U p B)
            * (reHolonomy U p - 1))).re
        + ((Matrix.trace (smulILM (b1LM U p A) * b2LM p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b2LM p B) * b1LM U p A * imHolonomy U p)).re)
        + ((Matrix.trace (smulILM (b1LM U p A) * b3LM p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b3LM p B) * b1LM U p A * imHolonomy U p)).re)
        + ((Matrix.trace (smulILM (b1LM U p A) * b4LM U p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b4LM U p B) * b1LM U p A * imHolonomy U p)).re)
        + ((Matrix.trace (smulILM (b2LM p A) * b3LM p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b3LM p B) * b2LM p A * imHolonomy U p)).re)
        + ((Matrix.trace (smulILM (b2LM p A) * b4LM U p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b4LM U p B) * b2LM p A * imHolonomy U p)).re)
        + ((Matrix.trace (smulILM (b3LM p A) * b4LM U p B * imHolonomy U p)).re
            - (Matrix.trace (smulILM (b4LM U p B) * b3LM p A * imHolonomy U p)).re) := by
  rw [bilPlaq_apply, firstBilPlaq_apply, secondBilPlaq_apply]
  simp only [pairBil_apply]
  ring

/-- **DIAGONAL, first term** — definitional. -/
theorem firstBilPlaq_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    firstBilPlaq U p A A = deltaPrimeFirstTermTransported U A p := rfl

/-- **DIAGONAL, commutator term.** The only non-definitional step in the whole construction: the
source writes ONE trace of `I • (Σ of six brackets) · Im U(∂p)`, this module writes TWELVE traces,
and they agree by `Matrix.smul_mul`/`Matrix.add_mul`/`Matrix.sub_mul` + additivity of `trace` and of
`Complex.re`. Nothing is dropped and nothing is added: the twelve atoms are exactly the six brackets'
two orderings. -/
theorem secondBilPlaq_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    secondBilPlaq U p A A = deltaPrimeSecondTermTransported U A p := by
  show (traceForm (imHolonomy U p) (smulILM ∘ₗ b1LM U p) (b2LM p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b2LM p) (b1LM U p) A A)
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ b1LM U p) (b3LM p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b3LM p) (b1LM U p) A A)
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ b1LM U p) (b4LM U p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b4LM U p) (b1LM U p) A A)
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ b2LM p) (b3LM p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b3LM p) (b2LM p) A A)
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ b2LM p) (b4LM U p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b4LM U p) (b2LM p) A A)
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ b3LM p) (b4LM U p) A A
      - traceForm (imHolonomy U p) (smulILM ∘ₗ b4LM U p) (b3LM p) A A)
    = _
  simp only [traceForm_apply, LinearMap.comp_apply, deltaPrimeSecondTermTransported,
    commutatorMatrixSumTransported]
  simp only [b1LM, b2LM, b3LM, b4LM, a1LM, a2LM, a3LM, a4LM, bondMatLM, bondMatRLM,
    smulILM, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearMap.neg_apply,
    LinearMap.proj_apply, Submodule.coe_subtype, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_neg,
    smul_eq_mul, Matrix.mul_assoc,
    AprimeXY, AprimeYZ, AprimeZW, AprimeWX, NegMemClass.coe_neg]
  simp only [← Complex.sub_re, ← Complex.add_re]
  congr 1
  ring

/-- **DIAGONAL, per plaquette.** -/
theorem bilPlaq_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    bilPlaq U p A A
      = deltaPrimeFirstTermTransported U A p + deltaPrimeSecondTermTransported U A p := by
  show firstBilPlaq U p A A + secondBilPlaq U p A A = _
  rw [firstBilPlaq_diag, secondBilPlaq_diag]

#print axioms bilPlaq_atoms
#print axioms pairBil_apply
#print axioms firstBilPlaq_apply
#print axioms secondBilPlaq_apply
#print axioms bilPlaq_apply
#print axioms pairBil
#print axioms firstBilPlaq
#print axioms secondBilPlaq
#print axioms bilPlaq
#print axioms firstBilPlaq_diag
#print axioms secondBilPlaq_diag
#print axioms bilPlaq_diag

/-! ## §4 — THE LATTICE SUM, AND THE SYMMETRIZATION

`deltaPrimeBilRaw` is the plaquette sum. It is bilinear (a finite sum in the module of bilinear
maps) and its DIAGONAL is `deltaPrimeQuadFormTransported`, but it is **not symmetric** — §9 proves
that with an explicit pair of fields, so the symmetrization below is demonstrably load-bearing
rather than defensive.
-/

/-- `Δ′`'s bilinear form, before symmetrization. -/
noncomputable def deltaPrimeBilRaw
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  ∑ p : PeriodicLatticePlaquette L, bilPlaq U p

theorem deltaPrimeBilRaw_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) :
    deltaPrimeBilRaw U A B = ∑ p : PeriodicLatticePlaquette L, bilPlaq U p A B := by
  show (∑ p : PeriodicLatticePlaquette L, bilPlaq U p) A B = _
  rw [LinearMap.sum_apply, LinearMap.sum_apply]

/-- **THE DIAGONAL OF THE RAW FORM IS `Δ′`.** -/
theorem deltaPrimeBilRaw_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaPrimeBilRaw U A A = deltaPrimeQuadFormTransported U A := by
  rw [deltaPrimeBilRaw_apply, deltaPrimeQuadFormTransported]
  exact Finset.sum_congr rfl (fun p _ => bilPlaq_diag U p A)

/-- **`Δ′`'s SYMMETRIC bilinear form** — the deliverable of §1-§4. -/
noncomputable def deltaPrimeBil
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • (deltaPrimeBilRaw U + (deltaPrimeBilRaw U).flip)

theorem deltaPrimeBil_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) :
    deltaPrimeBil U A B
      = (1 / 2 : ℝ) * (deltaPrimeBilRaw U A B + deltaPrimeBilRaw U B A) := rfl

/-- **SYMMETRY — proved, not assumed** (§0b). -/
theorem deltaPrimeBil_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) :
    deltaPrimeBil U A B = deltaPrimeBil U B A := by
  rw [deltaPrimeBil_apply, deltaPrimeBil_apply, add_comm]

/-- **THE DIAGONAL SURVIVES SYMMETRIZATION**: `½(Q + Q) = Q`. -/
theorem deltaPrimeBil_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaPrimeBil U A A = deltaPrimeQuadFormTransported U A := by
  rw [deltaPrimeBil_apply, deltaPrimeBilRaw_diag]
  ring

#print axioms deltaPrimeBilRaw
#print axioms deltaPrimeBilRaw_apply
#print axioms deltaPrimeBilRaw_diag
#print axioms deltaPrimeBil
#print axioms deltaPrimeBil_apply
#print axioms deltaPrimeBil_symm
#print axioms deltaPrimeBil_diag

/-! ## §5 — TRANSPORT TO THE INNER-PRODUCT CARRIER `BondFnL2 L`

Through `BondSU2Space.bondFnL2Equiv`, which is `WithLp.linearEquiv` — purely algebraic, needing only
`Module ℝ`, exactly the technique `CStarDeltaKCOperator` §2 uses for `C`. No topology and no norm
instance enters, ~~so §0a of that module's `letI` discussion does not arise until §6.~~

**S75 note (2026-08-09, `compute/norm_diamond_install/`):** that discussion no longer arises
anywhere. `CovariantOperators.instNormedAddCommGroupBondFnL2` has been deleted (0 dependents among
24090 declarations), `CStarDeltaKCOperator` §0a is struck, and this file's three `letI`s in §6 are
removed — the instance they installed is the one ordinary search now returns. The sentence's
substantive content, that §5's transport is purely algebraic, is unaffected and still true.
-/

/-- `Δ′`'s symmetric bilinear form on `BondFnL2 L`. -/
noncomputable def deltaPrimeBilL2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L →ₗ[ℝ] ℝ :=
  ((deltaPrimeBil U).compl₂ (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).toLinearMap) ∘ₗ
    (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).toLinearMap

theorem deltaPrimeBilL2_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    deltaPrimeBilL2 U x y
      = deltaPrimeBil U (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L x)
          (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L y) := rfl

theorem deltaPrimeBilL2_toLp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) :
    deltaPrimeBilL2 U (WithLp.toLp 2 A) (WithLp.toLp 2 B) = deltaPrimeBil U A B := rfl

theorem deltaPrimeBilL2_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    deltaPrimeBilL2 U x y = deltaPrimeBilL2 U y x := by
  rw [deltaPrimeBilL2_apply, deltaPrimeBilL2_apply, deltaPrimeBil_symm]

#print axioms deltaPrimeBilL2
#print axioms deltaPrimeBilL2_apply
#print axioms deltaPrimeBilL2_toLp
#print axioms deltaPrimeBilL2_symm

/-! ## §6 — THE OPERATOR `Δ′`, AND `hT2`

`CStarDeltaKCOperator.bilinToOperatorBond` is REUSED (LAW-19): it closes the Riesz half, so this
section is three lines of plumbing plus the `hT2` identity.
-/

/-- **`Δ′` AS AN OPERATOR** on `BondFnL2 L`. -/
noncomputable def deltaPrimeOp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  bilinToOperatorBond (deltaPrimeBilL2 U)

theorem inner_deltaPrimeOp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    (inner ℝ x (deltaPrimeOp U y) : ℝ) = deltaPrimeBilL2 U x y :=
  inner_bilinToOperatorBond _ x y

/-- **SELF-ADJOINT** — from §4's symmetry, which is NOT a diagonal-only fact (§0b). -/
theorem bondAdjoint_deltaPrimeOp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    bondAdjoint (deltaPrimeOp U) = deltaPrimeOp U :=
  bondAdjoint_bilinToOperatorBond _ (deltaPrimeBilL2_symm U)

theorem inner_deltaPrimeOp_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    (inner ℝ (deltaPrimeOp U x) y : ℝ) = inner ℝ x (deltaPrimeOp U y) :=
  (bondAdjoint_eq_self_iff _).1 (bondAdjoint_deltaPrimeOp U) x y

/-- **`T2` — the sandwich's missing input, in its exact requested shape
`BondFnL2 L →L[ℝ] BondFnL2 L`.** -/
noncomputable def deltaPrimeCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (deltaPrimeOp U)

/-- **`hT2`, PROVED** — the diagonal identity the sandwich consumes, verbatim in its shape. -/
theorem inner_deltaPrimeCLM_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (deltaPrimeCLM U (WithLp.toLp 2 A)) : ℝ)
      = deltaPrimeQuadFormTransported U A := by
  show (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (deltaPrimeOp U (WithLp.toLp 2 A)) : ℝ) = _
  rw [inner_deltaPrimeOp, deltaPrimeBilL2_toLp, deltaPrimeBil_diag]

theorem inner_deltaPrimeCLM_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    (inner ℝ (deltaPrimeCLM U x) y : ℝ) = inner ℝ x (deltaPrimeCLM U y) :=
  inner_deltaPrimeOp_symm U x y

#print axioms deltaPrimeOp
#print axioms inner_deltaPrimeOp
#print axioms bondAdjoint_deltaPrimeOp
#print axioms inner_deltaPrimeOp_symm
#print axioms deltaPrimeCLM
#print axioms inner_deltaPrimeCLM_eq
#print axioms inner_deltaPrimeCLM_symm

/-! ## §7 — `Δ_k` AND `C*Δ_kC`, NOW UNCONDITIONAL

This is the deliverable that matters. `CStarDeltaKCOperator` §10's theorems all carried `T2` + `hT2`
as hypotheses; instantiated at §6's `deltaPrimeCLM U` they become theorems about a named operator
with no hypothesis about `Δ′` at all.
-/

/-- **`Δ_k = D_U^*D_U + Δ′` AS AN UNCONDITIONAL OPERATOR** (`DeltaKFull` §9 residual 4: the
bundled `H →L[ℝ] H`, which that file could only state as a conditional assembly). -/
noncomputable def deltaKCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  dstarDCLM U + deltaPrimeCLM U

/-- Its quadratic form is ~~CMP99b (3.10)'s FAITHFUL assembly~~ **[SUPERSEDED, S75, conviction
banner (1) — struck in place, statement RETAINED because it is true of the named raw object]**
`DeltaKFull.deltaKQuadFormCorrected = dstarDQuadForm + deltaPrimeQuadFormTransported`. That
assembly is `D*D + 2·Δ′_source`, NOT source-normalized `Δ_k`: `dstarDQuadForm` carries `hsInner`'s
`-(1/2)Tr` (verified in §N.1, not trusted from a docstring) while
`deltaPrimeQuadFormTransported` uses raw `Matrix.trace`. The source-normalized statement is §N.4's
`inner_deltaKCLMNormalized_eq`. -/
theorem inner_deltaKCLM_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (deltaKCLM U (WithLp.toLp 2 A)) : ℝ)
      = AdalyFormal.Balaban.DeltaKFull.deltaKQuadFormCorrected U A :=
  AdalyFormal.Balaban.CStarDeltaKCOperator.deltaKFull_T1_discharged U (deltaPrimeCLM U)
    (inner_deltaPrimeCLM_eq U) A

/-- `Δ_k` is symmetric — UNCONDITIONALLY. `D_U^*D_U` is symmetric by
`CStarDeltaKCOperator.inner_dstarDLM_symm`, `Δ′` by §6. ~~This is the `hsym` datum that pins `T2`
uniquely (§0b).~~ **[SUPERSEDED, S75, conviction banner (2) — struck in place; the theorem itself
is retained and true.]** Symmetry here is S82-FORCED: `deltaPrimeBil := ½(raw + raw.flip)` is
symmetric for EVERY raw form, including `0` and arbitrary garbage, so this declaration is a
consistency fact and NOT evidence about the source expansion. It does pin `T2` GIVEN the diagonal
and the fixed inner product; it does not pin the source content. §N.7 supplies the non-forced
source checks. -/
theorem deltaKCLM_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    (inner ℝ (deltaKCLM U x) y : ℝ) = inner ℝ x (deltaKCLM U y) := by
  show (inner ℝ ((dstarDCLM U + deltaPrimeCLM U) x) y : ℝ)
    = inner ℝ x ((dstarDCLM U + deltaPrimeCLM U) y)
  rw [show ((dstarDCLM U + deltaPrimeCLM U) x : BondFnL2 L)
        = dstarDCLM U x + deltaPrimeCLM U x from rfl,
    show ((dstarDCLM U + deltaPrimeCLM U) y : BondFnL2 L)
        = dstarDCLM U y + deltaPrimeCLM U y from rfl, inner_add_left, inner_add_right]
  rw [show ((dstarDCLM U) x : BondFnL2 L) = dstarDLM U x from rfl,
    show ((dstarDCLM U) y : BondFnL2 L) = dstarDLM U y from rfl,
    inner_dstarDLM_symm, inner_deltaPrimeCLM_symm]

/-- `Δ_k` is a self-adjoint OPERATOR (Bałaban states `Δ` is hermitian; this is that statement for
the ~~faithful~~ **[SUPERSEDED, S75: RAW, `η = 1`, `2 ×` source-normalized in its `Δ′` half — see
§N.4 for the source-normalized twin]** (3.10) assembly, unconditionally). Self-adjointness itself
is S82-FORCED (banner (2)). -/
theorem bondAdjoint_deltaKCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    bondAdjoint (deltaKCLM U).toLinearMap = (deltaKCLM U).toLinearMap :=
  (bondAdjoint_eq_self_iff _).2 (deltaKCLM_symm U)

/-- **THE TASK'S ITEM 4 — `⟪B̃, (C*Δ_kC) B̃⟫ = Δ_k-form at `C B̃`, UNCONDITIONALLY.**
The `T2` slot is filled by §6's `deltaPrimeCLM U`; `C` is CMP99b (3.157)'s own `fullC` (identified
by `rfl` in `CStarDeltaKCOperator` §2); ~~the middle map is the FAITHFUL (3.10) assembly~~
**[SUPERSEDED, S75, conviction banner (1) — struck in place; the theorem is RETAINED and true of
the raw object]**: the middle map is `D*D + 2·Δ′_source`, the `η = 1` specialization with a raw
trace in its `Δ′` half. The source-normalized statement is §N.4's
`inner_cStarDeltaKCCLM_normalized_unconditional`. No hypothesis about `Δ′` remains — that part is
unaffected. -/
theorem inner_cStarDeltaKCCLM_unconditional
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (B : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
        (cStarDeltaKCCLM U ell Dinv (deltaPrimeCLM U) (WithLp.toLp 2 B)) : ℝ)
      = AdalyFormal.Balaban.DeltaKFull.deltaKQuadFormCorrected U
          (AdalyFormal.Balaban.FullReparamC.fullC U ell Dinv B) :=
  inner_cStarDeltaKCCLM_eq U ell Dinv (deltaPrimeCLM U) (inner_deltaPrimeCLM_eq U) B

/-- The same at the unbundled `LinearMap` sandwich. **[QUALIFIED, S75, conviction banner (1):** this
is the theorem Sol convicted as "an identity about `D*D + 2·Δ′_source`, NOT about `Δ_k`". The
statement is RETAINED unchanged because it is true of the named raw object; the source-normalized
replacement is §N.4's `inner_cStarDeltaKC_normalized_unconditional`.**]** -/
theorem inner_cStarDeltaKC_unconditional
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (B : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
        (cStarDeltaKC U ell Dinv (deltaPrimeCLM U) (WithLp.toLp 2 B)) : ℝ)
      = AdalyFormal.Balaban.DeltaKFull.deltaKQuadFormCorrected U
          (AdalyFormal.Balaban.FullReparamC.fullC U ell Dinv B) :=
  inner_cStarDeltaKC_eq U ell Dinv (deltaPrimeCLM U) (inner_deltaPrimeCLM_eq U) B

/-- **`C*Δ_kC` IS SELF-ADJOINT — UNCONDITIONALLY.** `bondAdjoint_cStarDeltaKC`'s `hsym` hypothesis
is discharged by `deltaKCLM_symm`. This is the conclusion that is NOT diagonal-only, and it is what
makes the supplied `T2` the unique one compatible with `hT2` (§0b).
**[QUALIFIED, S75, conviction banner (1)+(2) — struck nothing, added:** the object is the RAW
(`2 × Δ′_source`) sandwich, so this is not a statement about source-normalized `C*Δ_kC` (§N.4's
`bondAdjoint_cStarDeltaKC_normalized_unconditional` is); AND self-adjointness is S82-FORCED —
Sol compiled the same conclusion for the zero form and for arbitrary nonzero garbage, so it is a
consistency fact, not evidence that `bilPlaq` transcribes the source. §N.7 supplies the checks that
DO fail under a coherent substitution.**]** -/
theorem bondAdjoint_cStarDeltaKC_unconditional
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    bondAdjoint (cStarDeltaKC U ell Dinv (deltaPrimeCLM U))
      = cStarDeltaKC U ell Dinv (deltaPrimeCLM U) :=
  bondAdjoint_cStarDeltaKC U ell Dinv (deltaPrimeCLM U) (deltaKCLM_symm U)

#print axioms deltaKCLM
#print axioms inner_deltaKCLM_eq
#print axioms deltaKCLM_symm
#print axioms bondAdjoint_deltaKCLM
#print axioms inner_cStarDeltaKCCLM_unconditional
#print axioms inner_cStarDeltaKC_unconditional
#print axioms bondAdjoint_cStarDeltaKC_unconditional

/-! ## §8 — NON-DEGENERACY: THE OPERATOR IS NOT ZERO, AND IT MOVES WITH `U`

§DEGEN/§GREEN: a supplied `T2` that happened to be `0` would satisfy every *shape* requirement
above, so the two facts below are the controls. They use `DeltaPrime`'s OWN already-banked witness
values (`-8` at `witnessU`, `0` at `trivialU`), reused rather than recomputed (LAW-19).
-/

/-- **`Δ′`'s operator is NOT the zero map** — at `DeltaPrime`'s `witnessU`/`deltaWitnessConfig` its
diagonal is `-8`. -/
theorem inner_deltaPrimeOp_witnessU :
    (inner ℝ (WithLp.toLp 2 deltaWitnessConfig :
        BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
      (deltaPrimeOp witnessU (WithLp.toLp 2 deltaWitnessConfig)) : ℝ) = -8 := by
  rw [inner_deltaPrimeOp, deltaPrimeBilL2_toLp, deltaPrimeBil_diag]
  exact deltaPrimeQuadFormTransported_witnessU_eq

theorem deltaPrimeOp_ne_zero_at_witnessU :
    deltaPrimeOp witnessU ≠
      (0 : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL →ₗ[ℝ]
        BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL) := by
  intro h
  have hv := inner_deltaPrimeOp_witnessU
  rw [h] at hv
  simp at hv

/-- **`Δ′`'s operator VANISHES at the flat background.** Not merely its diagonal: the SYMMETRIC form
with identically-zero diagonal is identically zero by polarization
(`2·b(A,B) = b(A+B,A+B) - b(A,A) - b(B,B)`), and symmetry is §4's proved
`deltaPrimeBil_symm`. Together with the previous theorem this proves the supplied `T2` is genuinely
`U`-dependent — it is `0` exactly where `DeltaPrime` proves `Δ′` is, and nonzero elsewhere. -/
theorem deltaPrimeBil_trivialU (A B : Bond L → SuTwo) :
    deltaPrimeBil (trivialU (L := L)) A B = 0 := by
  have hd : ∀ C : Bond L → SuTwo, deltaPrimeBil (trivialU (L := L)) C C = 0 := by
    intro C
    rw [deltaPrimeBil_diag]
    exact deltaPrimeQuadFormTransported_vanishes_at_trivial C
  have hexp : deltaPrimeBil (trivialU (L := L)) (A + B) (A + B)
      = deltaPrimeBil (trivialU (L := L)) A A + deltaPrimeBil (trivialU (L := L)) A B
        + (deltaPrimeBil (trivialU (L := L)) B A + deltaPrimeBil (trivialU (L := L)) B B) := by
    simp only [map_add, LinearMap.add_apply]
    ring
  rw [hd (A + B), hd A, hd B, ← deltaPrimeBil_symm (trivialU (L := L)) A B] at hexp
  linarith

theorem deltaPrimeOp_trivialU :
    deltaPrimeOp (trivialU (L := L)) = 0 := by
  refine LinearMap.ext (fun y => ?_)
  refine ext_inner_left ℝ (fun v => ?_)
  rw [inner_deltaPrimeOp, deltaPrimeBilL2_apply, deltaPrimeBil_trivialU, LinearMap.zero_apply,
    inner_zero_right]

/-- **`Δ′` IS NOT POSITIVE SEMIDEFINITE** — hence `inner_cStarDeltaKC_nonneg`'s hypothesis is NOT
available for `Δ_k = D*D + Δ′` from `Δ′`'s side, and §0c's refusal to state any positivity is a
measured fact rather than caution. -/
theorem deltaPrimeOp_not_nonneg :
    ¬ (∀ x : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL,
        (0 : ℝ) ≤ inner ℝ x (deltaPrimeOp witnessU x)) := by
  intro h
  have := h (WithLp.toLp 2 deltaWitnessConfig)
  rw [inner_deltaPrimeOp_witnessU] at this
  norm_num at this

#print axioms inner_deltaPrimeOp_witnessU
#print axioms deltaPrimeOp_ne_zero_at_witnessU
#print axioms deltaPrimeBil_trivialU
#print axioms deltaPrimeOp_trivialU
#print axioms deltaPrimeOp_not_nonneg

/-! ## §9 — FALSIFIABILITY: BOTH HALVES ARE LOAD-BEARING, AT AN EXPLICIT WITNESS

§8's `-8` witness is `DeltaPrime`'s own, and it does NOT test the commutator half: at
`witnessU`/`deltaWitnessConfig` the second term is `0` at every one of the four exceptional
plaquettes (`DeltaPrime.deltaPrimeSecondTerm_witnessU_witnessPlaquette` and its three siblings), so
the whole `-8` comes from the first term. **A construction that dropped the six commutator brackets
entirely would reproduce every number in §7 and §8.** That is exactly §GREEN's degenerate-test-point
failure, and this section removes it.

The structural reason is worth recording: the tree carried only TWO `𝔰𝔲(2)` elements,
`suTwoWitness = i·σ₃` and `witnessM = i·σ₂`, and `[i·σ₃, i·σ₂] ∝ σ₁` is trace-orthogonal to
`Im U(∂p) ∝ σ₂` at `witnessPlaquette`. A THIRD direction is needed and is built here.

What is proved below, at `witnessU` on `witnessPlaquette` with two explicit single-bond fields
`discA` (at `(witnessY,1)`, value `i·σ₃`) and `discB` (at `(witnessY,0)`, value `i·σ₁`):

* the commutator half alone contributes `4`, the first-term half `0`
  (`secondBilPlaq_disc`, `firstBilPlaq_disc`) — so **dropping any of the six brackets, or the whole
  second term, changes a proved number**;
* the RAW form is **NOT symmetric** — `4` one way and `0` the other, globally on the lattice
  (`deltaPrimeBilRaw_disc`, `deltaPrimeBilRaw_disc_swap`, `deltaPrimeBilRaw_not_symm`) — so §4's
  symmetrization is load-bearing, not decoration, and the symmetrized value is `2`
  (`deltaPrimeBil_disc`);
* `deltaPrimeOp witnessU` is therefore not symmetric "by accident of the diagonal": the OFF-diagonal
  values are pinned, `⟪discA, Δ′ discB⟫ = 2` (`inner_deltaPrimeOp_disc`), which is a statement `hT2`
  alone cannot make (§0b).
-/

/-! ### W1 — a third `𝔰𝔲(2)` direction -/

/-- `i·σ₁`. -/
def sigma1IVal : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]

theorem sigma1IVal_mem : sigma1IVal ∈ suTwo := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [sigma1IVal, Matrix.conjTranspose_apply]
  · simp [sigma1IVal, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- The third generator, as a `SuTwo` element (L7 witness: nonzero, proved below). -/
def sigma1I : SuTwo := ⟨sigma1IVal, sigma1IVal_mem⟩

theorem sigma1I_coe : ((sigma1I : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = sigma1IVal := rfl

theorem sigma1I_ne_zero : sigma1I ≠ 0 := by
  intro h
  have h01 : sigma1IVal 0 1 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
    have := congrArg (fun z : SuTwo => (z : Matrix (Fin 2) (Fin 2) ℂ)) h
    rw [sigma1I_coe] at this
    simpa using congrFun (congrFun this 0) 1
  simp only [sigma1IVal, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.zero_apply, Matrix.of_apply] at h01
  exact Complex.I_ne_zero h01

/-! ### W2 — vanishing lemmas for the per-plaquette form -/

/-- Each of `pairBil`'s TWO trace atoms contains the `f`-factor evaluated at the FIRST argument, so
the whole pair vanishes when that factor does. -/
theorem pairBil_eq_zero_of_left_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo)
    (h : f A = 0) : pairBil U p f g A B = 0 := by
  rw [pairBil_apply, h]
  simp [smulILM_apply]

/-- Dually, both atoms contain the `g`-factor evaluated at the SECOND argument. -/
theorem pairBil_eq_zero_of_right_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo)
    (h : g B = 0) : pairBil U p f g A B = 0 := by
  rw [pairBil_apply, h]
  simp [smulILM_apply]

/-- **THE COMMUTATOR HALF IS BLIND TO COMMUTING COMPONENTS.** If the two `A′`-components paired by a
bracket COMMUTE, that bracket contributes nothing — which is why a witness family supported on a
SINGLE `𝔰𝔲(2)` direction cannot see the second term of `Δ′` at all, and why `DeltaPrime`'s own
`deltaWitnessConfig` has `deltaPrimeSecondTerm = 0` at all four of its exceptional plaquettes. This
is the general statement behind §9's degeneracy control. -/
theorem pairBil_eq_zero_of_commute
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo)
    (h : f A * g B = g B * f A) : pairBil U p f g A B = 0 := by
  rw [pairBil_apply, smulILM_apply, smulILM_apply]
  simp only [Matrix.smul_mul]
  rw [h, sub_self]

theorem b1LM_eq_zero_of_bond_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (h : A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0) : b1LM U p A = 0 := by
  show smulILM (a1LM U p A) = 0
  rw [show a1LM U p A = ((AprimeZW U A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    show AprimeZW U A p = -RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
      from rfl, h]
  simp [smulILM_apply]

theorem b2LM_eq_zero_of_bond_zero (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (h : A (p.1, p.2.1.2) = 0) : b2LM p A = 0 := by
  show smulILM (a2LM p A) = 0
  rw [show a2LM p A = ((AprimeWX A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    show AprimeWX A p = -A (p.1, p.2.1.2) from rfl, h]
  simp [smulILM_apply]

theorem b3LM_eq_zero_of_bond_zero (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (h : A (p.1, p.2.1.1) = 0) : b3LM p A = 0 := by
  show smulILM (a3LM p A) = 0
  rw [show a3LM p A = ((AprimeXY A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    show AprimeXY A p = A (p.1, p.2.1.1) from rfl, h]
  simp [smulILM_apply]

theorem b4LM_eq_zero_of_bond_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (h : A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0) : b4LM U p A = 0 := by
  show smulILM (a4LM U p A) = 0
  rw [show a4LM U p A = ((AprimeYZ U A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    show AprimeYZ U A p = RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
      from rfl, h]
  simp [smulILM_apply]

theorem curlMatLM_eq_zero_of_bonds_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (h1 : A (p.1, p.2.1.1) = 0) (h2 : A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0)
    (h3 : A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0) (h4 : A (p.1, p.2.1.2) = 0) :
    curlMatLM U p A = 0 := by
  rw [curlMatLM_apply]
  have hc : curlValueCovariant U A p = 0 := by
    show A (p.1, p.2.1.1) + RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
      - RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
      - A (p.1, p.2.1.2) = 0
    rw [h1, h2, h3, h4]
    simp
  rw [hc]
  simp

/-- **If the FIRST argument vanishes on all four boundary bonds of `p`, the whole per-plaquette
bilinear form vanishes there** — every one of the 13 atoms carries a first-argument factor. -/
theorem bilPlaq_eq_zero_of_left_bonds_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo)
    (h1 : A (p.1, p.2.1.1) = 0) (h2 : A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0)
    (h3 : A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0) (h4 : A (p.1, p.2.1.2) = 0) :
    bilPlaq U p A B = 0 := by
  have hb1 := b1LM_eq_zero_of_bond_zero U p A h3
  have hb2 := b2LM_eq_zero_of_bond_zero p A h4
  have hb3 := b3LM_eq_zero_of_bond_zero p A h1
  have hc := curlMatLM_eq_zero_of_bonds_zero U p A h1 h2 h3 h4
  rw [bilPlaq_apply, firstBilPlaq_apply, hc, secondBilPlaq_apply,
    pairBil_eq_zero_of_left_zero U p _ _ A B hb1,
    pairBil_eq_zero_of_left_zero U p _ _ A B hb1,
    pairBil_eq_zero_of_left_zero U p _ _ A B hb1,
    pairBil_eq_zero_of_left_zero U p _ _ A B hb2,
    pairBil_eq_zero_of_left_zero U p _ _ A B hb2,
    pairBil_eq_zero_of_left_zero U p _ _ A B hb3]
  simp [smulILM_apply]

/-- Dually for the SECOND argument. -/
theorem bilPlaq_eq_zero_of_right_bonds_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo)
    (h1 : B (p.1, p.2.1.1) = 0) (h2 : B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0)
    (h3 : B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0) (h4 : B (p.1, p.2.1.2) = 0) :
    bilPlaq U p A B = 0 := by
  have hb2 := b2LM_eq_zero_of_bond_zero p B h4
  have hb3 := b3LM_eq_zero_of_bond_zero p B h1
  have hb4 := b4LM_eq_zero_of_bond_zero U p B h2
  have hc := curlMatLM_eq_zero_of_bonds_zero U p B h1 h2 h3 h4
  rw [bilPlaq_apply, firstBilPlaq_apply, hc, secondBilPlaq_apply,
    pairBil_eq_zero_of_right_zero U p _ _ A B hb2,
    pairBil_eq_zero_of_right_zero U p _ _ A B hb3,
    pairBil_eq_zero_of_right_zero U p _ _ A B hb4,
    pairBil_eq_zero_of_right_zero U p _ _ A B hb3,
    pairBil_eq_zero_of_right_zero U p _ _ A B hb4,
    pairBil_eq_zero_of_right_zero U p _ _ A B hb4]
  simp [smulILM_apply]

/-! ### W3 — the two discriminating fields -/

/-- `i·σ₃` on the single bond `(witnessY, 1)`. -/
noncomputable def discA : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo :=
  fun e => if e = (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (1 : Fin 3)) then suTwoWitness
    else 0

/-- `i·σ₁` on the single bond `(witnessY, 0)`. -/
noncomputable def discB : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo :=
  fun e => if e = (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)) then sigma1I else 0

theorem discA_at : discA (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (1 : Fin 3))
    = suTwoWitness := by simp [discA]

theorem discA_elsewhere {e : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL}
    (h : e ≠ (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (1 : Fin 3))) : discA e = 0 := by
  simp [discA, h]

theorem discB_at : discB (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3))
    = sigma1I := by simp [discB]

theorem discB_elsewhere {e : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL}
    (h : e ≠ (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3))) : discB e = 0 := by
  simp [discB, h]

/-! ### W4 — local data at `witnessPlaquette` -/

/-- `Im U(∂p) = !![0,-i;i,0]` at `witnessU`/`witnessPlaquette`. Computed from the tree's own
holonomy values (`holonomy_witnessU_witnessPlaquette`, `holonomyElemInv_witnessU_witnessPlaquette`,
`witnessMElem_inv_coe_eq_conjTranspose`) — reused, not recomputed (LAW-19). NOTE the holonomy there
is `witnessMElem` itself, NOT its inverse (the inverse occurs at `p3`/`p4`); getting that backwards
flips the sign of every number in this section. -/
theorem imHolonomy_witnessU_witnessPlaquette :
    imHolonomy witnessU witnessPlaquette = !![0, -Complex.I; Complex.I, 0] := by
  have hsub : (witnessMElem : Matrix (Fin 2) (Fin 2) ℂ)
      - ((witnessMElem⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) = !![0, 2; -2, 0] := by
    rw [witnessMElem_inv_coe_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [witnessMElem, witnessM, Matrix.conjTranspose_apply] <;> ring
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    rw [div_eq_div_iff (by simp [Complex.I_ne_zero]) (by norm_num)]
    simp
    ring_nf
    simp [Complex.I_sq]
  show (1 / (2 * Complex.I) : ℂ) • ((holonomyElem witnessU witnessPlaquette :
      Matrix (Fin 2) (Fin 2) ℂ) - (holonomyElemInv witnessU witnessPlaquette :
      Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [holonomy_witnessU_witnessPlaquette, holonomyElemInv_witnessU_witnessPlaquette, hsub, hI]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]

theorem reHolonomy_sub_one_witnessPlaquette :
    reHolonomy witnessU witnessPlaquette - 1 = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [reHolonomy_witnessU_witnessPlaquette, zero_sub]

/-! ### W5 — the `A′` components of the two fields at `witnessPlaquette` -/

theorem AprimeZW_discA : AprimeZW witnessU discA witnessPlaquette = 0 := by
  show -RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.2))
    (discA (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.2,
      witnessPlaquette.2.1.1)) = 0
  rw [discA_elsewhere (show _ ≠ _ by decide)]
  simp

theorem AprimeXY_discA : AprimeXY discA witnessPlaquette = 0 :=
  discA_elsewhere (show _ ≠ _ by decide)

theorem AprimeYZ_discA : AprimeYZ witnessU discA witnessPlaquette = 0 := by
  show RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.1))
    (discA (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.1,
      witnessPlaquette.2.1.2)) = 0
  rw [discA_elsewhere (show _ ≠ _ by decide)]
  simp

theorem AprimeWX_discA : AprimeWX discA witnessPlaquette = -suTwoWitness := by
  show -discA (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (1 : Fin 3)) = -suTwoWitness
  rw [discA_at]

theorem AprimeZW_discB : AprimeZW witnessU discB witnessPlaquette = 0 := by
  show -RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.2))
    (discB (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.2,
      witnessPlaquette.2.1.1)) = 0
  rw [discB_elsewhere (show _ ≠ _ by decide)]
  simp

theorem AprimeWX_discB : AprimeWX discB witnessPlaquette = 0 := by
  show -discB (witnessPlaquette.1, witnessPlaquette.2.1.2) = 0
  rw [discB_elsewhere (show _ ≠ _ by decide)]
  simp

theorem AprimeYZ_discB : AprimeYZ witnessU discB witnessPlaquette = 0 := by
  show RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.1))
    (discB (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.1,
      witnessPlaquette.2.1.2)) = 0
  rw [discB_elsewhere (show _ ≠ _ by decide)]
  simp

theorem AprimeXY_discB : AprimeXY discB witnessPlaquette = sigma1I := discB_at

/-! ### W6 — the surviving `bᵢ` values, as explicit matrices -/

theorem b1LM_discA : b1LM witnessU witnessPlaquette discA = 0 :=
  b1LM_eq_zero_of_bond_zero _ _ _ (discA_elsewhere (show _ ≠ _ by decide))

theorem b3LM_discA : b3LM witnessPlaquette discA = 0 :=
  b3LM_eq_zero_of_bond_zero _ _ (discA_elsewhere (show _ ≠ _ by decide))

theorem b4LM_discA : b4LM witnessU witnessPlaquette discA = 0 :=
  b4LM_eq_zero_of_bond_zero _ _ _ (discA_elsewhere (show _ ≠ _ by decide))

theorem b1LM_discB : b1LM witnessU witnessPlaquette discB = 0 :=
  b1LM_eq_zero_of_bond_zero _ _ _ (discB_elsewhere (show _ ≠ _ by decide))

theorem b2LM_discB : b2LM witnessPlaquette discB = 0 :=
  b2LM_eq_zero_of_bond_zero _ _ (discB_elsewhere (show _ ≠ _ by decide))

theorem b4LM_discB : b4LM witnessU witnessPlaquette discB = 0 :=
  b4LM_eq_zero_of_bond_zero _ _ _ (discB_elsewhere (show _ ≠ _ by decide))

/-- `b₂(discA) = I • (-i·σ₃) = !![1,0;0,-1]`. -/
theorem b2LM_discA : b2LM witnessPlaquette discA = !![1, 0; 0, -1] := by
  show smulILM (a2LM witnessPlaquette discA) = _
  rw [show a2LM witnessPlaquette discA
      = ((AprimeWX discA witnessPlaquette : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    AprimeWX_discA]
  rw [smulILM_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.Balaban.CovariantOperators.suTwoWitness,
      AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal, Matrix.smul_apply]

/-- `b₃(discB) = I • (i·σ₁) = !![0,-1;-1,0]`. -/
theorem b3LM_discB : b3LM witnessPlaquette discB = !![0, -1; -1, 0] := by
  show smulILM (a3LM witnessPlaquette discB) = _
  rw [show a3LM witnessPlaquette discB
      = ((AprimeXY discB witnessPlaquette : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    AprimeXY_discB, sigma1I_coe, smulILM_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma1IVal, Matrix.smul_apply]

theorem curlMatLM_discA : curlMatLM witnessU witnessPlaquette discA
    = -(AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal) := by
  rw [curlMatLM_apply]
  have hc : curlValueCovariant witnessU discA witnessPlaquette = -suTwoWitness := by
    show discA (witnessPlaquette.1, witnessPlaquette.2.1.1)
        + RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.1))
            (discA (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.1,
              witnessPlaquette.2.1.2))
        - RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.2))
            (discA (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.2,
              witnessPlaquette.2.1.1))
        - discA (witnessPlaquette.1, witnessPlaquette.2.1.2) = -suTwoWitness
    rw [discA_elsewhere (show _ ≠ _ by decide), discA_elsewhere (show _ ≠ _ by decide),
      discA_elsewhere (show _ ≠ _ by decide),
      show discA (witnessPlaquette.1, witnessPlaquette.2.1.2)
        = discA (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (1 : Fin 3)) from rfl, discA_at]
    simp
  rw [hc]
  simp [AdalyFormal.Balaban.CovariantOperators.suTwoWitness]

theorem curlMatLM_discB : curlMatLM witnessU witnessPlaquette discB = sigma1IVal := by
  rw [curlMatLM_apply]
  have hc : curlValueCovariant witnessU discB witnessPlaquette = sigma1I := by
    show discB (witnessPlaquette.1, witnessPlaquette.2.1.1)
        + RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.1))
            (discB (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.1,
              witnessPlaquette.2.1.2))
        - RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.2))
            (discB (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.2,
              witnessPlaquette.2.1.1))
        - discB (witnessPlaquette.1, witnessPlaquette.2.1.2) = sigma1I
    rw [show discB (witnessPlaquette.1, witnessPlaquette.2.1.1)
        = discB (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)) from rfl, discB_at,
      discB_elsewhere (show _ ≠ _ by decide), discB_elsewhere (show _ ≠ _ by decide),
      discB_elsewhere (show _ ≠ _ by decide)]
    simp
  rw [hc, sigma1I_coe]

/-! ### W7 — the two discriminating VALUES -/

/-- **The first term contributes NOTHING at this witness** — so the `4` below is entirely the
commutator half. -/
theorem firstBilPlaq_disc : firstBilPlaq witnessU witnessPlaquette discA discB = 0 := by
  rw [firstBilPlaq_apply, curlMatLM_discA, curlMatLM_discB, reHolonomy_sub_one_witnessPlaquette,
    smulILM_apply, smulILM_apply]
  have h1 : (Complex.I • (-(AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal)))
      = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal, Matrix.smul_apply]
  have h2 : (Complex.I • sigma1IVal) = !![0, -1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigma1IVal, Matrix.smul_apply]
  rw [h1, h2, Matrix.mul_neg, Matrix.mul_one, Matrix.trace_neg, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of]
  norm_num

theorem firstBilPlaq_disc_swap : firstBilPlaq witnessU witnessPlaquette discB discA = 0 := by
  rw [firstBilPlaq_apply, curlMatLM_discA, curlMatLM_discB, reHolonomy_sub_one_witnessPlaquette,
    smulILM_apply, smulILM_apply]
  have h1 : (Complex.I • (-(AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal)))
      = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal, Matrix.smul_apply]
  have h2 : (Complex.I • sigma1IVal) = !![0, -1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigma1IVal, Matrix.smul_apply]
  rw [h1, h2, Matrix.mul_neg, Matrix.mul_one, Matrix.trace_neg, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of]
  norm_num

/-- **THE COMMUTATOR HALF IS NONZERO** — exactly the `(2,3)` bracket survives, with value `4`. Any
construction that dropped it, or dropped the `(2,3)` pair, or transposed one of the two matrix
orderings inside it, would contradict this theorem. -/
theorem secondBilPlaq_disc : secondBilPlaq witnessU witnessPlaquette discA discB = 4 := by
  rw [secondBilPlaq_apply,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBil_eq_zero_of_right_zero _ _ _ _ _ _ b4LM_discB,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b3LM_discA,
    pairBil_apply, b2LM_discA, b3LM_discB, imHolonomy_witnessU_witnessPlaquette, smulILM_apply,
    smulILM_apply]
  have h1 : (Complex.I • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![Complex.I, 0; 0, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  have h2 : (Complex.I • (!![0, -1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![0, -Complex.I; -Complex.I, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  rw [h1, h2, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of, Matrix.trace_fin_two_of]
  simp only [Complex.add_re]
  norm_num [Complex.I_mul_I, Complex.ext_iff]

/-- And it vanishes with the two arguments EXCHANGED — the raw form is not symmetric. -/
theorem secondBilPlaq_disc_swap : secondBilPlaq witnessU witnessPlaquette discB discA = 0 := by
  rw [secondBilPlaq_apply,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discB,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discB,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discB,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b2LM_discB,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b2LM_discB,
    pairBil_eq_zero_of_right_zero _ _ _ _ _ _ b4LM_discA]
  norm_num

theorem bilPlaq_disc : bilPlaq witnessU witnessPlaquette discA discB = 4 := by
  rw [bilPlaq_apply, firstBilPlaq_disc, secondBilPlaq_disc]
  norm_num

theorem bilPlaq_disc_swap : bilPlaq witnessU witnessPlaquette discB discA = 0 := by
  rw [bilPlaq_apply, firstBilPlaq_disc_swap, secondBilPlaq_disc_swap]
  norm_num

/-! ### W8 — the GLOBAL statement: the lattice sum reduces to this one plaquette -/

/-- **Off `witnessPlaquette`, one of the two fields vanishes on ALL FOUR boundary bonds.** Uses
`CovariantHj.eq_witnessPlaquette_or_myWitnessPlaquette2`, `CovariantHj.plaquette_snd_dir_ne_zero`
and `DeltaPrime.eq_p3_or_p4` — the tree's own uniqueness lemmas for the bond `(witnessY,0)`
(LAW-19), plus direction/site mismatches for `(witnessY,1)` on the three other exceptional
plaquettes. -/
theorem disc_bonds_vanish_of_ne
    {p : PeriodicLatticePlaquette AdalyFormal.Balaban.AdmissibleSubspace.witnessL}
    (hp : p ≠ witnessPlaquette) :
    (discA (p.1, p.2.1.1) = 0 ∧ discA (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0
      ∧ discA (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0 ∧ discA (p.1, p.2.1.2) = 0)
    ∨ (discB (p.1, p.2.1.1) = 0 ∧ discB (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0
      ∧ discB (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0 ∧ discB (p.1, p.2.1.2) = 0) := by
  by_cases h2 : p = myWitnessPlaquette2
  · subst h2
    exact Or.inl ⟨discA_elsewhere (by decide), discA_elsewhere (by decide),
      discA_elsewhere (by decide), discA_elsewhere (by decide)⟩
  by_cases h3 : p = p3
  · subst h3
    exact Or.inl ⟨discA_elsewhere (by decide), discA_elsewhere (by decide),
      discA_elsewhere (by decide), discA_elsewhere (by decide)⟩
  by_cases h4 : p = p4
  · subst h4
    exact Or.inl ⟨discA_elsewhere (by decide), discA_elsewhere (by decide),
      discA_elsewhere (by decide), discA_elsewhere (by decide)⟩
  refine Or.inr ⟨?_, ?_, ?_, ?_⟩
  · refine discB_elsewhere (fun hcon => ?_)
    rcases eq_witnessPlaquette_or_myWitnessPlaquette2 (congrArg Prod.fst hcon)
        (congrArg Prod.snd hcon) with h | h
    · exact hp h
    · exact h2 h
  · exact discB_elsewhere (fun hcon => plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon))
  · refine discB_elsewhere (fun hcon => ?_)
    rcases eq_p3_or_p4 (congrArg Prod.fst hcon) (congrArg Prod.snd hcon) with h | h
    · exact h3 h
    · exact h4 h
  · exact discB_elsewhere (fun hcon => plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon))

theorem bilPlaq_disc_eq_zero_of_ne
    {p : PeriodicLatticePlaquette AdalyFormal.Balaban.AdmissibleSubspace.witnessL}
    (hp : p ≠ witnessPlaquette) : bilPlaq witnessU p discA discB = 0 := by
  rcases disc_bonds_vanish_of_ne hp with ⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩
  · exact bilPlaq_eq_zero_of_left_bonds_zero _ _ _ _ g1 g2 g3 g4
  · exact bilPlaq_eq_zero_of_right_bonds_zero _ _ _ _ g1 g2 g3 g4

theorem bilPlaq_disc_swap_eq_zero_of_ne
    {p : PeriodicLatticePlaquette AdalyFormal.Balaban.AdmissibleSubspace.witnessL}
    (hp : p ≠ witnessPlaquette) : bilPlaq witnessU p discB discA = 0 := by
  rcases disc_bonds_vanish_of_ne hp with ⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩
  · exact bilPlaq_eq_zero_of_right_bonds_zero _ _ _ _ g1 g2 g3 g4
  · exact bilPlaq_eq_zero_of_left_bonds_zero _ _ _ _ g1 g2 g3 g4

/-- **THE RAW LATTICE FORM AT THE WITNESS: `4`.** -/
theorem deltaPrimeBilRaw_disc : deltaPrimeBilRaw witnessU discA discB = 4 := by
  rw [deltaPrimeBilRaw_apply,
    Finset.sum_eq_single witnessPlaquette (fun p _ hp => bilPlaq_disc_eq_zero_of_ne hp)
      (fun h => absurd (Finset.mem_univ witnessPlaquette) h)]
  exact bilPlaq_disc

/-- **AND `0` THE OTHER WAY.** -/
theorem deltaPrimeBilRaw_disc_swap : deltaPrimeBilRaw witnessU discB discA = 0 := by
  rw [deltaPrimeBilRaw_apply]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  by_cases hp : p = witnessPlaquette
  · subst hp; exact bilPlaq_disc_swap
  · exact bilPlaq_disc_swap_eq_zero_of_ne hp

/-- **THE SYMMETRIZATION IS LOAD-BEARING** — `deltaPrimeBilRaw` is genuinely NOT symmetric, so §4's
`½(raw + raw.flip)` changes the object rather than decorating it. -/
theorem deltaPrimeBilRaw_not_symm :
    ¬ (∀ A B : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo,
        deltaPrimeBilRaw witnessU A B = deltaPrimeBilRaw witnessU B A) := by
  intro h
  have := h discA discB
  rw [deltaPrimeBilRaw_disc, deltaPrimeBilRaw_disc_swap] at this
  norm_num at this

/-- The symmetrized value: `½(4 + 0) = 2`. -/
theorem deltaPrimeBil_disc : deltaPrimeBil witnessU discA discB = 2 := by
  rw [deltaPrimeBil_apply, deltaPrimeBilRaw_disc, deltaPrimeBilRaw_disc_swap]
  norm_num

/-- **AN OFF-DIAGONAL VALUE OF THE OPERATOR IS PINNED** — `⟪discA, Δ′ discB⟫ = 2`. This is the one
statement in this module that `hT2` alone could never make (§0b): it constrains the operator off the
diagonal, and it does so because the form was symmetrized. -/
theorem inner_deltaPrimeOp_disc :
    (inner ℝ (WithLp.toLp 2 discA :
        BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
      (deltaPrimeOp witnessU (WithLp.toLp 2 discB)) : ℝ) = 2 := by
  rw [inner_deltaPrimeOp, deltaPrimeBilL2_toLp, deltaPrimeBil_disc]

#print axioms sigma1IVal
#print axioms sigma1IVal_mem
#print axioms sigma1I
#print axioms sigma1I_coe
#print axioms sigma1I_ne_zero
#print axioms pairBil_eq_zero_of_left_zero
#print axioms pairBil_eq_zero_of_right_zero
#print axioms b1LM_eq_zero_of_bond_zero
#print axioms b2LM_eq_zero_of_bond_zero
#print axioms b3LM_eq_zero_of_bond_zero
#print axioms b4LM_eq_zero_of_bond_zero
#print axioms curlMatLM_eq_zero_of_bonds_zero
#print axioms bilPlaq_eq_zero_of_left_bonds_zero
#print axioms bilPlaq_eq_zero_of_right_bonds_zero
#print axioms discA
#print axioms discB
#print axioms discA_at
#print axioms discA_elsewhere
#print axioms discB_at
#print axioms discB_elsewhere
#print axioms imHolonomy_witnessU_witnessPlaquette
#print axioms reHolonomy_sub_one_witnessPlaquette
#print axioms AprimeZW_discA
#print axioms AprimeXY_discA
#print axioms AprimeYZ_discA
#print axioms AprimeWX_discA
#print axioms AprimeZW_discB
#print axioms AprimeWX_discB
#print axioms AprimeYZ_discB
#print axioms AprimeXY_discB
#print axioms b1LM_discA
#print axioms b3LM_discA
#print axioms b4LM_discA
#print axioms b1LM_discB
#print axioms b2LM_discB
#print axioms b4LM_discB
#print axioms b2LM_discA
#print axioms b3LM_discB
#print axioms curlMatLM_discA
#print axioms curlMatLM_discB
#print axioms firstBilPlaq_disc
#print axioms firstBilPlaq_disc_swap
#print axioms secondBilPlaq_disc
#print axioms secondBilPlaq_disc_swap
#print axioms bilPlaq_disc
#print axioms bilPlaq_disc_swap
#print axioms disc_bonds_vanish_of_ne
#print axioms bilPlaq_disc_eq_zero_of_ne
#print axioms bilPlaq_disc_swap_eq_zero_of_ne
#print axioms deltaPrimeBilRaw_disc
#print axioms deltaPrimeBilRaw_disc_swap
#print axioms deltaPrimeBilRaw_not_symm
#print axioms deltaPrimeBil_disc
#print axioms inner_deltaPrimeOp_disc

/-! ### W9 — THE DEGENERACY CONTROL (§GREEN, §DEGEN)

`discA2` is `discA` moved onto `discB`'s `𝔰𝔲(2)` DIRECTION — same bond, same plaquette, same
background, everything identical except that the two fields now commute. The commutator half then
contributes exactly `0` instead of `4`. So the `4` is a fact about the non-commutativity the bracket
measures, not an artifact of the construction's shape; and a witness family confined to one direction
— which is all the tree had before this section — reports `0` here no matter what the commutator half
is. That is precisely the degenerate test point §GREEN warns about, exhibited rather than described.
-/

/-- `discA`, moved onto `discB`'s direction: `i·σ₁` on `(witnessY, 1)`. -/
noncomputable def discA2 : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo :=
  fun e => if e = (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (1 : Fin 3)) then sigma1I else 0

theorem discA2_at : discA2 (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (1 : Fin 3))
    = sigma1I := by simp [discA2]

theorem discA2_elsewhere {e : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL}
    (h : e ≠ (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (1 : Fin 3))) : discA2 e = 0 := by
  simp [discA2, h]

theorem b1LM_discA2 : b1LM witnessU witnessPlaquette discA2 = 0 :=
  b1LM_eq_zero_of_bond_zero _ _ _ (discA2_elsewhere (show _ ≠ _ by decide))

theorem b3LM_discA2 : b3LM witnessPlaquette discA2 = 0 :=
  b3LM_eq_zero_of_bond_zero _ _ (discA2_elsewhere (show _ ≠ _ by decide))

theorem b4LM_discA2 : b4LM witnessU witnessPlaquette discA2 = 0 :=
  b4LM_eq_zero_of_bond_zero _ _ _ (discA2_elsewhere (show _ ≠ _ by decide))

/-- The one surviving component of `discA2` is MINUS the one surviving component of `discB` — same
`𝔰𝔲(2)` direction, so they commute. -/
theorem b2LM_discA2_eq : b2LM witnessPlaquette discA2 = -(b3LM witnessPlaquette discB) := by
  rw [b3LM_discB]
  show smulILM (a2LM witnessPlaquette discA2) = _
  rw [show a2LM witnessPlaquette discA2
      = ((AprimeWX discA2 witnessPlaquette : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    show AprimeWX discA2 witnessPlaquette
      = -discA2 (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (1 : Fin 3)) from rfl,
    discA2_at, NegMemClass.coe_neg, sigma1I_coe, smulILM_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma1IVal, Matrix.smul_apply]

/-- **THE DEGENERACY CONTROL, PROVED**: same bond, same background, same plaquette, only the `𝔰𝔲(2)`
direction changed, and the commutator half drops from `4` to `0`. -/
theorem secondBilPlaq_disc_degenerate :
    secondBilPlaq witnessU witnessPlaquette discA2 discB = 0 := by
  rw [secondBilPlaq_apply,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA2,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA2,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA2,
    pairBil_eq_zero_of_commute _ _ _ _ _ _
      (by rw [b2LM_discA2_eq]; rw [neg_mul, mul_neg]),
    pairBil_eq_zero_of_right_zero _ _ _ _ _ _ b4LM_discB,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b3LM_discA2]
  norm_num

/-- Stated as a difference, so the discrimination is one theorem rather than two numbers a reader
has to compare. -/
theorem secondBilPlaq_disc_ne_degenerate :
    secondBilPlaq witnessU witnessPlaquette discA discB
      ≠ secondBilPlaq witnessU witnessPlaquette discA2 discB := by
  rw [secondBilPlaq_disc, secondBilPlaq_disc_degenerate]
  norm_num

#print axioms pairBil_eq_zero_of_commute
#print axioms discA2
#print axioms discA2_at
#print axioms discA2_elsewhere
#print axioms b1LM_discA2
#print axioms b3LM_discA2
#print axioms b4LM_discA2
#print axioms b2LM_discA2_eq
#print axioms secondBilPlaq_disc_degenerate
#print axioms secondBilPlaq_disc_ne_degenerate

/-! ## §11 — THE POINTWISE `D_U^*`: A FINDING, NOT A BUILD (LAW-19, BUILD DISCIPLINE #2)

`CStarDeltaKCOperator` §4 states that `DeltaKFull` §7 Residual 1's *explicit combinatorial formula*
for the covariant curl adjoint "remains unbuilt and is a genuinely different deliverable". **That is
STALE: the object already exists in this tree**, in `Balaban/DeltaKU.lean` §1-§4 — the explicit
`curlCovariantAdjointValue`, WITH its Gram identity
`covPlaqInner (D_U A) F = covBondInner A (D_U^* F)` (`covPlaqInner_curlValueCovariant_eq_covBondInner`),
in a file with zero `sorry`. `DeltaKU` imports `DeltaKFull`, so it is DOWNSTREAM of the file whose
residual list it discharges, which is why neither `DeltaKFull` nor `CStarDeltaKCOperator` could see it.

Nothing is rebuilt here. What is added is the CONNECTION, in both directions:

* the abstract `LinearMap.adjoint`-based `curlAdjoint` that the whole `C*Δ_kC` chain runs on **IS**
  `DeltaKU`'s hand-built combinatorial co-differential (`curlAdjoint_toLp`) — two independent
  constructions of one object, which is a cross-check neither file could perform alone;
* consequently `dstarDCLM U : BondFnL2 L →L[ℝ] BondFnL2 L` **IS** the transport of `DeltaKU`'s
  `deltaKUOp` to the inner-product carrier (`dstarDCLM_toLp`) — the step `DeltaKU`'s own docstring
  names as *"blocked by the §6/§8e ambient-vs-norm PiLp diamond — a named formalization residual"*.
  It is not blocked; `CStarDeltaKCOperator` §0a's one-line instance shadow is what unblocks it.

Net effect on the residual ledger of this chain: `DeltaKFull` §9 residuals 1, 2 and 4 are all
discharged — 1 by this connection, 2 by §1-§6 of this file, 4 by §7's `deltaKCLM`. Residual 3 is a
propagation instruction about a DIFFERENT object (`bondLaplacianCovCLM_L2`) and is untouched.
-/

/-- **THE ABSTRACT ADJOINT IS THE EXPLICIT ONE.** `curlAdjoint` is defined through Mathlib's
`LinearMap.adjoint` (no formula); `curlCovariantAdjointValue` is `DeltaKU`'s hand-written
co-differential. They agree on every transported plaquette field, hence everywhere. -/
theorem curlAdjoint_toLp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (F : PeriodicLatticePlaquette L → SuTwo) :
    curlAdjoint U (WithLp.toLp 2 F)
      = (WithLp.toLp 2 (curlCovariantAdjointValue U F) : BondFnL2 L) := by
  refine ext_inner_left ℝ (fun v => ?_)
  have hv : (WithLp.toLp 2 (WithLp.ofLp v) : BondFnL2 L) = v := rfl
  rw [← hv, inner_curlAdjoint_right, curlCovariantLM_L2_toLp,
    AdalyFormal.Balaban.CovariantHjMinimizer.inner_plaqFnL2_eq_covPlaqInner,
    AdalyFormal.Balaban.BondSU2Space.inner_bondFnL2_eq_covBondInner,
    covPlaqInner_curlValueCovariant_eq_covBondInner]

/-- **`D_U^*D_U` ON THE INNER-PRODUCT CARRIER IS `DeltaKU.deltaKUOp`, POINTWISE.** -/
theorem dstarDLM_toLp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    dstarDLM U (WithLp.toLp 2 A) = (WithLp.toLp 2 (deltaKUOp U A) : BondFnL2 L) := by
  show curlAdjoint U (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U (WithLp.toLp 2 A)) = _
  rw [curlCovariantLM_L2_toLp, curlAdjoint_toLp, deltaKUOp_apply]

/-- The bundled form: `dstarDCLM` is the `BondFnL2 →L[ℝ] BondFnL2` transport of `deltaKUOp` that
`DeltaKU`'s docstring names as blocked. -/
theorem dstarDCLM_toLp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    dstarDCLM U (WithLp.toLp 2 A) = (WithLp.toLp 2 (deltaKUOp U A) : BondFnL2 L) :=
  dstarDLM_toLp U A

/-- **`Δ_k`'s `D*D` HALF IS NOW POINTWISE EXPLICIT.** Combining with §7: the value of `Δ_k`'s first
term at a transported field is `DeltaKU`'s explicit combinatorial expression, and its second term is
§6's Riesz vector of `Δ′`'s bilinear form. -/
theorem deltaKCLM_toLp_first_term
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaKCLM U (WithLp.toLp 2 A)
      = (WithLp.toLp 2 (deltaKUOp U A) : BondFnL2 L) + deltaPrimeOp U (WithLp.toLp 2 A) := by
  show (dstarDCLM U + deltaPrimeCLM U) (WithLp.toLp 2 A) = _
  rw [show ((dstarDCLM U + deltaPrimeCLM U) (WithLp.toLp 2 A) : BondFnL2 L)
      = dstarDCLM U (WithLp.toLp 2 A) + deltaPrimeCLM U (WithLp.toLp 2 A) from rfl,
    dstarDCLM_toLp]
  rfl

#print axioms curlAdjoint_toLp
#print axioms dstarDLM_toLp
#print axioms dstarDCLM_toLp
#print axioms deltaKCLM_toLp_first_term

/-! ## §N — THE NORMALIZATION REPAIR, AND THE NON-FORCED SOURCE CHECKS

Filed against the de-correlated Sol prosecution recorded in this file's conviction banner
(`compute/sol_deltaprime/SOL_PROSECUTION_DELTAPRIME.md`). Three things are done here:

* **N.1** verifies — rather than trusting `DeltaKFull`'s docstring — that the `D*D` half really does
  carry the source normalization, by exhibiting the `1/2` against raw `Matrix.trace` and proving the
  un-normalized sum takes a DIFFERENT value at a named witness. So the relative coefficient is wrong
  in the `Δ′` direction, not the `D*D` direction.
* **N.2-N.5** route the whole operator chain through the SOURCE-NORMALIZED `Δ′`, consuming
  `NormalizationAudit.deltaPrimeQuadFormNormalizedTransported_eq_half_transported` (LAW-19: that
  lemma predates this repair by four days and is not re-derived), and re-derive Sol's numeric witness
  `-4` (not `-8`) at the OPERATOR level.
* **N.7** answers the second conviction: it builds SIX coherent alternative bilinear forms — each a
  genuine bilinear form for which all seven S82-forced symmetry/self-adjointness facts hold verbatim
  — and proves each one DIFFERS from `bilPlaq` at an explicit witness. It also exhibits the
  degenerate background at which all seven coincide, so the discrimination is shown to be a property
  of the witness rather than of the checks.

**Option taken (banner):** (b) — the raw layer is untouched, the normalized layer is new. No existing
declaration changes meaning. `traceForm` is deliberately NOT rescaled: it is the generic trace
pairing that `bilPlaq_atoms` and every `*_diag` `rfl`-pin are stated against, and those pins must
keep asserting exactly what the imported `DeltaPrime.lean` says.

**`η` scope, stated inline once (banner (3)):** CMP99b's printed (3.10) carries the weight
`η^d η^{-2}`; no type in this file has an `η` binder. Every object below, normalized or raw, is the
`η = 1` (unit-spacing) specialization of (3.10).
-/

/-! ### N.1 — DOES THE `D*D` HALF REALLY CARRY THE SOURCE NORMALIZATION? (task item 3) -/

/-- **CHECKED, NOT TRUSTED.** `CovariantHj.dstarDQuadForm` written out against RAW `Matrix.trace`:
the `-(1/2)` is EXHIBITED, by `rfl`, through `covPlaqInner`/`hsInner`. `hsInner`'s own docstring
derives that `1/2` as Bałaban's normalized trace `tr = ½Tr` for `N = 2`; this theorem is the
kernel-checked version of that sentence, so the `D*D` half's normalization is now a proof rather
than a docstring. -/
theorem dstarDQuadForm_explicit_half
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    dstarDQuadForm U A
      = ∑ p : PeriodicLatticePlaquette L,
          -(1 / 2 : ℝ) * (Matrix.trace
            ((curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ)
              * (curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ))).re := rfl

/-- The same sum with the normalization DROPPED — what `dstarDQuadForm` would be if the `D*D` half
carried a raw trace like the `Δ′` half does. -/
noncomputable def dstarDRawTraceSum
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L,
    -(Matrix.trace ((curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ)
      * (curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ))).re

theorem dstarDRawTraceSum_eq_two_mul
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    dstarDRawTraceSum U A = 2 * dstarDQuadForm U A := by
  rw [dstarDQuadForm_explicit_half, Finset.mul_sum, dstarDRawTraceSum]
  exact Finset.sum_congr rfl (fun p _ => by ring)

theorem dstarDRawTraceSum_witness_eq_eight :
    dstarDRawTraceSum witnessU deltaWitnessConfig = 8 := by
  rw [dstarDRawTraceSum_eq_two_mul, dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four]
  norm_num

/-- **THE `D*D` NORMALIZATION IS DISCRIMINABLE**: `8 ≠ 4` at `witnessU`/`deltaWitnessConfig`. So
`dstarDQuadForm`'s `1/2` is not a vacuous decoration — dropping it provably moves a number. Together
with `dstarDQuadForm_explicit_half` this settles the direction of the factor-2 defect: the `D*D` half
IS source-normalized, so it is the `Δ′` half that is `2 ×` too large, exactly as the conviction
states, and NOT the other way round. -/
theorem dstarD_normalization_discriminable :
    dstarDRawTraceSum witnessU deltaWitnessConfig
      ≠ dstarDQuadForm witnessU deltaWitnessConfig := by
  rw [dstarDRawTraceSum_witness_eq_eight, dstarDQuadForm_witnessU_deltaWitnessConfig_eq_four]
  norm_num

#print axioms dstarDQuadForm_explicit_half
#print axioms dstarDRawTraceSum
#print axioms dstarDRawTraceSum_eq_two_mul
#print axioms dstarDRawTraceSum_witness_eq_eight
#print axioms dstarD_normalization_discriminable

/-! ### N.2 — THE SOURCE-NORMALIZED BILINEAR LAYER -/

/-- **`Δ′`'s SOURCE-NORMALIZED symmetric bilinear form** — `η = 1` specialization of CMP99b (3.10),
now with the page-392 trace normalization `tr = ½Tr` applied. -/
noncomputable def deltaPrimeBilNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • deltaPrimeBil U

theorem deltaPrimeBilNormalized_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) :
    deltaPrimeBilNormalized U A B = (1 / 2 : ℝ) * deltaPrimeBil U A B := rfl

/-- Symmetric. **S82-FORCED** exactly as `deltaPrimeBil_symm` is (a scalar multiple of a symmetric
form is symmetric for every form), and recorded as such rather than advertised as evidence. -/
theorem deltaPrimeBilNormalized_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) :
    deltaPrimeBilNormalized U A B = deltaPrimeBilNormalized U B A := by
  rw [deltaPrimeBilNormalized_apply, deltaPrimeBilNormalized_apply, deltaPrimeBil_symm]

/-- **THE DIAGONAL IS THE SOURCE-NORMALIZED `Δ′` QUADRATIC FORM** —
`NormalizationAudit.deltaPrimeQuadFormNormalizedTransported`, CONSUMED via that file's own
`_eq_half_transported` (LAW-19), not re-derived here. -/
theorem deltaPrimeBilNormalized_diag
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaPrimeBilNormalized U A A = deltaPrimeQuadFormNormalizedTransported U A := by
  rw [deltaPrimeBilNormalized_apply, deltaPrimeBil_diag,
    deltaPrimeQuadFormNormalizedTransported_eq_half_transported]

noncomputable def deltaPrimeBilL2Normalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • deltaPrimeBilL2 U

theorem deltaPrimeBilL2Normalized_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    deltaPrimeBilL2Normalized U x y = (1 / 2 : ℝ) * deltaPrimeBilL2 U x y := rfl

theorem deltaPrimeBilL2Normalized_toLp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) :
    deltaPrimeBilL2Normalized U (WithLp.toLp 2 A) (WithLp.toLp 2 B)
      = deltaPrimeBilNormalized U A B := rfl

theorem deltaPrimeBilL2Normalized_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    deltaPrimeBilL2Normalized U x y = deltaPrimeBilL2Normalized U y x := by
  rw [deltaPrimeBilL2Normalized_apply, deltaPrimeBilL2Normalized_apply, deltaPrimeBilL2_symm]

#print axioms deltaPrimeBilNormalized
#print axioms deltaPrimeBilNormalized_apply
#print axioms deltaPrimeBilNormalized_symm
#print axioms deltaPrimeBilNormalized_diag
#print axioms deltaPrimeBilL2Normalized
#print axioms deltaPrimeBilL2Normalized_apply
#print axioms deltaPrimeBilL2Normalized_toLp
#print axioms deltaPrimeBilL2Normalized_symm

/-! ### N.3 — THE NORMALIZED OPERATOR, AND THE FACTOR-`1/2` THEOREM (task item 2) -/

/-- **`Δ′_source` AS AN OPERATOR** on `BondFnL2 L`, promoted through the SAME reused Riesz map
`bilinToOperatorBond`. -/
noncomputable def deltaPrimeOpNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  bilinToOperatorBond (deltaPrimeBilL2Normalized U)

theorem inner_deltaPrimeOpNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    (inner ℝ x (deltaPrimeOpNormalized U y) : ℝ) = deltaPrimeBilL2Normalized U x y :=
  inner_bilinToOperatorBond _ x y

/-- **THE FACTOR-`1/2` THEOREM, AT THE OPERATOR LEVEL — PROVED, NOT ASSERTED (task item 2).**
`deltaPrimeOpNormalized U = ½ · deltaPrimeOp U` as maps, for every `U` and every extent. The proof is
Riesz uniqueness (`ext_inner_left`), so it is a statement about the two OPERATORS and not merely
about their diagonals: this is the exact factor by which Sol's conviction says the old chain was
wrong, now a theorem in the same file as the convicted declarations. -/
theorem deltaPrimeOpNormalized_eq_half_smul
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    deltaPrimeOpNormalized U = (1 / 2 : ℝ) • deltaPrimeOp U := by
  refine LinearMap.ext (fun y => ?_)
  refine ext_inner_left ℝ (fun v => ?_)
  rw [inner_deltaPrimeOpNormalized, deltaPrimeBilL2Normalized_apply, LinearMap.smul_apply,
    real_inner_smul_right, inner_deltaPrimeOp]

/-- Self-adjoint. **S82-FORCED** (banner (2)); recorded, not advertised. -/
theorem bondAdjoint_deltaPrimeOpNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    bondAdjoint (deltaPrimeOpNormalized U) = deltaPrimeOpNormalized U :=
  bondAdjoint_bilinToOperatorBond _ (deltaPrimeBilL2Normalized_symm U)

theorem inner_deltaPrimeOpNormalized_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    (inner ℝ (deltaPrimeOpNormalized U x) y : ℝ) = inner ℝ x (deltaPrimeOpNormalized U y) :=
  (bondAdjoint_eq_self_iff _).1 (bondAdjoint_deltaPrimeOpNormalized U) x y

/-- **`T2`, SOURCE-NORMALIZED**, in the sandwich's exact requested shape. -/
noncomputable def deltaPrimeCLMNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (deltaPrimeOpNormalized U)

/-- **`hT2`, SOURCE-NORMALIZED.** Same diagonal-only caveat as §0b: it fixes the form, not the
operator. -/
theorem inner_deltaPrimeCLMNormalized_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (deltaPrimeCLMNormalized U (WithLp.toLp 2 A)) : ℝ)
      = deltaPrimeQuadFormNormalizedTransported U A := by
  show (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
    (deltaPrimeOpNormalized U (WithLp.toLp 2 A)) : ℝ) = _
  rw [inner_deltaPrimeOpNormalized, deltaPrimeBilL2Normalized_toLp, deltaPrimeBilNormalized_diag]

theorem inner_deltaPrimeCLMNormalized_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    (inner ℝ (deltaPrimeCLMNormalized U x) y : ℝ) = inner ℝ x (deltaPrimeCLMNormalized U y) :=
  inner_deltaPrimeOpNormalized_symm U x y

#print axioms deltaPrimeOpNormalized
#print axioms inner_deltaPrimeOpNormalized
#print axioms deltaPrimeOpNormalized_eq_half_smul
#print axioms bondAdjoint_deltaPrimeOpNormalized
#print axioms inner_deltaPrimeOpNormalized_symm
#print axioms deltaPrimeCLMNormalized
#print axioms inner_deltaPrimeCLMNormalized_eq
#print axioms inner_deltaPrimeCLMNormalized_symm

/-! ### N.4 — `Δ_k` AND `C*Δ_kC`, SOURCE-NORMALIZED AND STILL UNCONDITIONAL (task item 1) -/

/-- **`Δ_k = D_U^*D_U + Δ′_source` AS AN UNCONDITIONAL OPERATOR**, source-normalized in BOTH halves.
This, not `deltaKCLM`, is the object CMP99b (3.10) names at `η = 1`. -/
noncomputable def deltaKCLMNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  dstarDCLM U + deltaPrimeCLMNormalized U

theorem inner_deltaKCLMNormalized_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (deltaKCLMNormalized U (WithLp.toLp 2 A)) : ℝ)
      = deltaKQuadFormNormalizedCorrected U A := by
  show (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
    ((dstarDCLM U + deltaPrimeCLMNormalized U) (WithLp.toLp 2 A)) : ℝ) = _
  rw [show ((dstarDCLM U + deltaPrimeCLMNormalized U) (WithLp.toLp 2 A) : BondFnL2 L)
        = dstarDCLM U (WithLp.toLp 2 A) + deltaPrimeCLMNormalized U (WithLp.toLp 2 A) from rfl,
    inner_add_right, inner_dstarDCLM_eq_dstarDQuadForm, inner_deltaPrimeCLMNormalized_eq]
  rfl

/-- Symmetric. **S82-FORCED** in its `Δ′` half (banner (2)). -/
theorem deltaKCLMNormalized_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x y : BondFnL2 L) :
    (inner ℝ (deltaKCLMNormalized U x) y : ℝ) = inner ℝ x (deltaKCLMNormalized U y) := by
  show (inner ℝ ((dstarDCLM U + deltaPrimeCLMNormalized U) x) y : ℝ)
    = inner ℝ x ((dstarDCLM U + deltaPrimeCLMNormalized U) y)
  rw [show ((dstarDCLM U + deltaPrimeCLMNormalized U) x : BondFnL2 L)
        = dstarDCLM U x + deltaPrimeCLMNormalized U x from rfl,
    show ((dstarDCLM U + deltaPrimeCLMNormalized U) y : BondFnL2 L)
        = dstarDCLM U y + deltaPrimeCLMNormalized U y from rfl, inner_add_left, inner_add_right]
  rw [show ((dstarDCLM U) x : BondFnL2 L) = dstarDLM U x from rfl,
    show ((dstarDCLM U) y : BondFnL2 L) = dstarDLM U y from rfl,
    inner_dstarDLM_symm, inner_deltaPrimeCLMNormalized_symm]

theorem bondAdjoint_deltaKCLMNormalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    bondAdjoint (deltaKCLMNormalized U).toLinearMap = (deltaKCLMNormalized U).toLinearMap :=
  (bondAdjoint_eq_self_iff _).2 (deltaKCLMNormalized_symm U)

/-- **THE REPAIRED HEADLINE.** `inner_cStarDeltaKC_unconditional`, re-proved against the
SOURCE-NORMALIZED `Δ_k`: `⟪B̃, (C*Δ_kC) B̃⟫ = deltaKQuadFormNormalizedCorrected` at `C B̃`. Still
hypothesis-free in `Δ′` (no `T2`, no `hT2`); still a FORM identity, not an operator equality (§0b);
still the `η = 1` specialization; and still NO positivity, coercivity, or lower bound of any kind is
claimed — `deltaPrimeOpNormalized_not_nonneg` below proves `Δ′_source` is indefinite too. -/
theorem inner_cStarDeltaKC_normalized_unconditional
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (B : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
        (cStarDeltaKC U ell Dinv (deltaPrimeCLMNormalized U) (WithLp.toLp 2 B)) : ℝ)
      = deltaKQuadFormNormalizedCorrected U
          (AdalyFormal.Balaban.FullReparamC.fullC U ell Dinv B) := by
  show (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
      (cStarMC (reparamCL2 U ell Dinv)
        ((dstarDCLM U + deltaPrimeCLMNormalized U).toLinearMap) (WithLp.toLp 2 B)) : ℝ) = _
  rw [inner_cStarMC_self, reparamCL2_apply]
  exact inner_deltaKCLMNormalized_eq U _

/-- The same at the bundled `cStarDeltaKCCLM`. -/
theorem inner_cStarDeltaKCCLM_normalized_unconditional
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (B : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
        (cStarDeltaKCCLM U ell Dinv (deltaPrimeCLMNormalized U) (WithLp.toLp 2 B)) : ℝ)
      = deltaKQuadFormNormalizedCorrected U
          (AdalyFormal.Balaban.FullReparamC.fullC U ell Dinv B) :=
  inner_cStarDeltaKC_normalized_unconditional U ell Dinv B

/-- Self-adjointness of the source-normalized sandwich. **S82-FORCED** (banner (2)) — stated for
completeness of the chain, explicitly NOT offered as source evidence. -/
theorem bondAdjoint_cStarDeltaKC_normalized_unconditional
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    bondAdjoint (cStarDeltaKC U ell Dinv (deltaPrimeCLMNormalized U))
      = cStarDeltaKC U ell Dinv (deltaPrimeCLMNormalized U) :=
  bondAdjoint_cStarDeltaKC U ell Dinv (deltaPrimeCLMNormalized U) (deltaKCLMNormalized_symm U)

#print axioms deltaKCLMNormalized
#print axioms inner_deltaKCLMNormalized_eq
#print axioms deltaKCLMNormalized_symm
#print axioms bondAdjoint_deltaKCLMNormalized
#print axioms inner_cStarDeltaKC_normalized_unconditional
#print axioms inner_cStarDeltaKCCLM_normalized_unconditional
#print axioms bondAdjoint_cStarDeltaKC_normalized_unconditional

/-! ### N.5 — SOL's NUMERIC WITNESS, RE-DERIVED HERE AT THE OPERATOR LEVEL -/

/-- **`-4`, NOT `-8`.** Sol proved this at the level of the quadratic FORM; this is the same number
as a diagonal value of the named OPERATOR `deltaPrimeCLMNormalized witnessU`. -/
theorem inner_deltaPrimeCLMNormalized_witnessU :
    (inner ℝ (WithLp.toLp 2 deltaWitnessConfig :
        BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
      (deltaPrimeCLMNormalized witnessU (WithLp.toLp 2 deltaWitnessConfig)) : ℝ) = -4 := by
  rw [inner_deltaPrimeCLMNormalized_eq,
    deltaPrimeQuadFormNormalizedTransported_eq_half_transported,
    deltaPrimeQuadFormTransported_witnessU_eq]
  norm_num

/-- The convicted raw value `-8`, restated at the CLM so the two sit side by side. -/
theorem inner_deltaPrimeCLM_witnessU_raw :
    (inner ℝ (WithLp.toLp 2 deltaWitnessConfig :
        BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
      (deltaPrimeCLM witnessU (WithLp.toLp 2 deltaWitnessConfig)) : ℝ) = -8 := by
  rw [inner_deltaPrimeCLM_eq]
  exact deltaPrimeQuadFormTransported_witnessU_eq

/-- **THE REPAIR IS SUBSTANTIVE, NOT A RELABELLING**: `-4 ≠ -8`. -/
theorem deltaPrime_normalized_ne_raw_at_witness :
    (inner ℝ (WithLp.toLp 2 deltaWitnessConfig :
        BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
      (deltaPrimeCLMNormalized witnessU (WithLp.toLp 2 deltaWitnessConfig)) : ℝ)
    ≠ (inner ℝ (WithLp.toLp 2 deltaWitnessConfig :
        BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
      (deltaPrimeCLM witnessU (WithLp.toLp 2 deltaWitnessConfig)) : ℝ) := by
  rw [inner_deltaPrimeCLMNormalized_witnessU, inner_deltaPrimeCLM_witnessU_raw]
  norm_num

/-- And the full source-normalized `Δ_k` diagonal at that witness is `0`, where the raw assembly gave
`-4` (`NormalizationAudit`'s own §3, consumed). Recorded as a FACT; no inference about positivity is
drawn from a single point, and none is available — see the next theorem. -/
theorem inner_deltaKCLMNormalized_witnessU :
    (inner ℝ (WithLp.toLp 2 deltaWitnessConfig :
        BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
      (deltaKCLMNormalized witnessU (WithLp.toLp 2 deltaWitnessConfig)) : ℝ) = 0 := by
  rw [inner_deltaKCLMNormalized_eq]
  exact deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero

/-- **`Δ′_source` IS INDEFINITE TOO** — the normalization repair does NOT buy positivity. Exactly as
`deltaPrimeOp_not_nonneg` for the raw operator. -/
theorem deltaPrimeOpNormalized_not_nonneg :
    ¬ (∀ x : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL,
        (0 : ℝ) ≤ inner ℝ x (deltaPrimeOpNormalized witnessU x)) := by
  intro h
  have hx := h (WithLp.toLp 2 deltaWitnessConfig)
  rw [show (inner ℝ (WithLp.toLp 2 deltaWitnessConfig :
      BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
      (deltaPrimeOpNormalized witnessU (WithLp.toLp 2 deltaWitnessConfig)) : ℝ)
    = inner ℝ (WithLp.toLp 2 deltaWitnessConfig :
      BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
      (deltaPrimeCLMNormalized witnessU (WithLp.toLp 2 deltaWitnessConfig)) from rfl,
    inner_deltaPrimeCLMNormalized_witnessU] at hx
  norm_num at hx

#print axioms inner_deltaPrimeCLMNormalized_witnessU
#print axioms inner_deltaPrimeCLM_witnessU_raw
#print axioms deltaPrime_normalized_ne_raw_at_witness
#print axioms inner_deltaKCLMNormalized_witnessU
#print axioms deltaPrimeOpNormalized_not_nonneg

/-! ### N.6 — THE TWO ORDERED TRACE ATOMS OF THE `(2,3)` BRACKET, PINNED NUMERICALLY

§9 proved the `(2,3)` bracket contributes `4` at `(discA, discB)`. That `4` is a DIFFERENCE of two
of the twelve elementary trace atoms `bilPlaq_atoms` counts. Pinning the two atoms SEPARATELY is
strictly more information: it is what lets N.7 evaluate a variant that recombines the same two atoms
with a different sign (the anticommutator), which is the single most likely wrong transcription of a
bracket and is invisible to any check that only sees the difference.
-/

/-- `tr( i·A′₂(discA) · A′₃(discB) · Im U(∂p) )·ᵣₑ = 2`. -/
theorem traceAtom23_disc :
    (Matrix.trace (smulILM (b2LM witnessPlaquette discA) * b3LM witnessPlaquette discB
        * imHolonomy witnessU witnessPlaquette)).re = 2 := by
  rw [b2LM_discA, b3LM_discB, imHolonomy_witnessU_witnessPlaquette, smulILM_apply]
  have h1 : (Complex.I • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![Complex.I, 0; 0, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  rw [h1, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  norm_num [Complex.I_mul_I, Complex.ext_iff]

/-- The OTHER matrix ordering of the same bracket: `-2`. Difference `2 - (-2) = 4` reproduces §9's
`secondBilPlaq_disc`; SUM `2 + (-2) = 0` is what N.7's anticommutator variant reports. -/
theorem traceAtom32_disc :
    (Matrix.trace (smulILM (b3LM witnessPlaquette discB) * b2LM witnessPlaquette discA
        * imHolonomy witnessU witnessPlaquette)).re = -2 := by
  rw [b2LM_discA, b3LM_discB, imHolonomy_witnessU_witnessPlaquette, smulILM_apply]
  have h2 : (Complex.I • (!![0, -1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![0, -Complex.I; -Complex.I, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  rw [h2, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  norm_num [Complex.I_mul_I, Complex.ext_iff]

#print axioms traceAtom23_disc
#print axioms traceAtom32_disc

/-! ### N.7 — SIX COHERENT ALTERNATIVE BILINEAR FORMS, EACH PROVED DIFFERENT (task item 4)

**What this section answers.** Sol proved that seven advertised symmetry/self-adjointness facts are
S82-FORCED: `symm(raw) := ½(raw + raw.flip)` is symmetric for EVERY raw form, so those seven survive
substituting the zero form or arbitrary nonzero garbage, and cannot be evidence that
`bilPlaq` transcribes CMP99b (3.10) correctly. Sol's sharp point was that the earlier "16/16
mutations killed" does not answer this either, because mutation M12 died of INCOHERENCE — it changed
the operator while leaving surrounding restatements aimed at the old form — and a COHERENT
substitution stays self-adjoint.

**The construction here takes that argument at its word.** Each `bilPlaqXXX` below is a fully
coherent object: a genuine `(Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ` for every `U` and `p`,
so `½(· + ·.flip)` symmetrizes it, `bilinToOperatorBond` promotes it, and ALL SEVEN of the forced
facts hold for it verbatim with the same proofs. Nothing about them fails by incoherence. What DOES
fail is a VALUE: each is proved `≠ bilPlaq` at an explicit witness. So the separation theorems below
are checks on the source CONTENT of `bilPlaq` that a coherent substitution breaks.

**The six variants, and the transcription error each one represents.**

| variant | wrong transcription it models | value at the witness | `bilPlaq` there |
|---|---|---:|---:|
| `0` | the whole term dropped (Sol's own coherent zero form) | `0` | `4` |
| `bilPlaqAnticommutator` | `aᵢaⱼ + aⱼaᵢ` read for `aᵢaⱼ - aⱼaᵢ` | `0` | `4` |
| `firstBilPlaq` | second (commutator) term dropped | `0` | `4` |
| `secondBilPlaq` | first (`Re U - 1`) term dropped | `0` (diagonal) | `-2` (diagonal) |
| `bilPlaqHolonomySwap` | `Re U(∂p) - 1` and `Im U(∂p)` swapped between the two terms | `0` | `4` |
| `bilPlaqDrop23` | one of the six `i<j` brackets omitted | `0` | `4` |
| `bilPlaqDoubled` | **the convicted defect itself** — a factor `2` in the trace normalization | `8` | `4` |

**Measured limitation, stated because it is a fact and not a verdict.** The witness pair
`(discA, discB)` activates exactly the `A′₂` and `A′₃` slots, so it separates any variant that
changes the `(2,3)` bracket, either holonomy factor, the relative sign inside a bracket, or the
overall scale. It does NOT separate a variant that only alters brackets among
`(1,2),(1,3),(1,4),(2,4),(3,4)` while leaving `(2,3)` intact — for instance "keep only the three
adjacent pairs `(1,2),(2,3),(3,4)`" evaluates to `4` here as well. Separating those needs fields
supported on the plaquette's OTHER two boundary bonds (activating `A′₁` via `AprimeZW` and `A′₄` via
`AprimeYZ`). **§N.8 builds exactly those and CLOSES the family**: it exhibits, for each of the six
`i<j` brackets, an argument pair at which that bracket is nonzero, and proves that omitting ANY ONE
of the six changes the form. So this limitation of `(discA, discB)` is a limitation of ONE witness
pair, not a residual of the module.
-/

theorem traceForm_zero_middle
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo) :
    traceForm (0 : Matrix (Fin 2) (Fin 2) ℂ) f g A B = 0 := by
  rw [traceForm_apply]
  simp

/-! #### V1 — ANTICOMMUTATOR in place of the commutator -/

noncomputable def pairBilAnti
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  traceForm (imHolonomy U p) (smulILM ∘ₗ f) g
    + (traceForm (imHolonomy U p) (smulILM ∘ₗ g) f).flip

theorem pairBilAnti_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo) :
    pairBilAnti U p f g A B
      = (Matrix.trace (smulILM (f A) * g B * imHolonomy U p)).re
        + (Matrix.trace (smulILM (g B) * f A * imHolonomy U p)).re := rfl

theorem pairBilAnti_eq_zero_of_left_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo)
    (h : f A = 0) : pairBilAnti U p f g A B = 0 := by
  rw [pairBilAnti_apply, h]
  simp [smulILM_apply]

theorem pairBilAnti_eq_zero_of_right_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo)
    (h : g B = 0) : pairBilAnti U p f g A B = 0 := by
  rw [pairBilAnti_apply, h]
  simp [smulILM_apply]

noncomputable def secondBilPlaqAnti
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  pairBilAnti U p (b1LM U p) (b2LM p) + pairBilAnti U p (b1LM U p) (b3LM p)
    + pairBilAnti U p (b1LM U p) (b4LM U p) + pairBilAnti U p (b2LM p) (b3LM p)
    + pairBilAnti U p (b2LM p) (b4LM U p) + pairBilAnti U p (b3LM p) (b4LM U p)

theorem secondBilPlaqAnti_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    secondBilPlaqAnti U p A B
      = pairBilAnti U p (b1LM U p) (b2LM p) A B + pairBilAnti U p (b1LM U p) (b3LM p) A B
        + pairBilAnti U p (b1LM U p) (b4LM U p) A B + pairBilAnti U p (b2LM p) (b3LM p) A B
        + pairBilAnti U p (b2LM p) (b4LM U p) A B
        + pairBilAnti U p (b3LM p) (b4LM U p) A B := rfl

noncomputable def bilPlaqAnticommutator
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  firstBilPlaq U p + secondBilPlaqAnti U p

/-! #### V4 — the two holonomy factors SWAPPED between the two terms -/

noncomputable def pairBilReSwap
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  traceForm (reHolonomy U p - 1) (smulILM ∘ₗ f) g
    - (traceForm (reHolonomy U p - 1) (smulILM ∘ₗ g) f).flip

theorem pairBilReSwap_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo) :
    pairBilReSwap U p f g A B
      = (Matrix.trace (smulILM (f A) * g B * (reHolonomy U p - 1))).re
        - (Matrix.trace (smulILM (g B) * f A * (reHolonomy U p - 1))).re := rfl

theorem pairBilReSwap_eq_zero_of_left_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo)
    (h : f A = 0) : pairBilReSwap U p f g A B = 0 := by
  rw [pairBilReSwap_apply, h]
  simp [smulILM_apply]

theorem pairBilReSwap_eq_zero_of_right_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo)
    (h : g B = 0) : pairBilReSwap U p f g A B = 0 := by
  rw [pairBilReSwap_apply, h]
  simp [smulILM_apply]

noncomputable def secondBilPlaqReSwap
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  pairBilReSwap U p (b1LM U p) (b2LM p) + pairBilReSwap U p (b1LM U p) (b3LM p)
    + pairBilReSwap U p (b1LM U p) (b4LM U p) + pairBilReSwap U p (b2LM p) (b3LM p)
    + pairBilReSwap U p (b2LM p) (b4LM U p) + pairBilReSwap U p (b3LM p) (b4LM U p)

theorem secondBilPlaqReSwap_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    secondBilPlaqReSwap U p A B
      = pairBilReSwap U p (b1LM U p) (b2LM p) A B + pairBilReSwap U p (b1LM U p) (b3LM p) A B
        + pairBilReSwap U p (b1LM U p) (b4LM U p) A B + pairBilReSwap U p (b2LM p) (b3LM p) A B
        + pairBilReSwap U p (b2LM p) (b4LM U p) A B
        + pairBilReSwap U p (b3LM p) (b4LM U p) A B := rfl

noncomputable def firstBilPlaqImSwap
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  traceForm (imHolonomy U p) (smulILM ∘ₗ curlMatLM U p) (smulILM ∘ₗ curlMatLM U p)

theorem firstBilPlaqImSwap_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    firstBilPlaqImSwap U p A B
      = (Matrix.trace (smulILM (curlMatLM U p A) * smulILM (curlMatLM U p B)
          * imHolonomy U p)).re := rfl

noncomputable def bilPlaqHolonomySwap
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  firstBilPlaqImSwap U p + secondBilPlaqReSwap U p

/-! #### V6 — the `(2,3)` bracket DROPPED, the other five kept -/

noncomputable def secondBilPlaqDrop23
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  pairBil U p (b1LM U p) (b2LM p) + pairBil U p (b1LM U p) (b3LM p)
    + pairBil U p (b1LM U p) (b4LM U p)
    + pairBil U p (b2LM p) (b4LM U p) + pairBil U p (b3LM p) (b4LM U p)

theorem secondBilPlaqDrop23_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    secondBilPlaqDrop23 U p A B
      = pairBil U p (b1LM U p) (b2LM p) A B + pairBil U p (b1LM U p) (b3LM p) A B
        + pairBil U p (b1LM U p) (b4LM U p) A B
        + pairBil U p (b2LM p) (b4LM U p) A B + pairBil U p (b3LM p) (b4LM U p) A B := rfl

noncomputable def bilPlaqDrop23
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  firstBilPlaq U p + secondBilPlaqDrop23 U p

/-! #### V5 — the CONVICTED misnormalization itself, as a coherent variant -/

noncomputable def bilPlaqDoubled
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  (2 : ℝ) • bilPlaq U p

theorem bilPlaqDoubled_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    bilPlaqDoubled U p A B = (2 : ℝ) * bilPlaq U p A B := rfl

/-! #### THE DISCRIMINATING VALUES at `(discA, discB)` on `witnessPlaquette` -/

theorem pairBilAnti_23_disc :
    pairBilAnti witnessU witnessPlaquette (b2LM witnessPlaquette) (b3LM witnessPlaquette)
      discA discB = 0 := by
  rw [pairBilAnti_apply, traceAtom23_disc, traceAtom32_disc]
  norm_num

theorem secondBilPlaqAnti_disc : secondBilPlaqAnti witnessU witnessPlaquette discA discB = 0 := by
  rw [secondBilPlaqAnti_apply,
    pairBilAnti_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBilAnti_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBilAnti_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBilAnti_eq_zero_of_right_zero _ _ _ _ _ _ b4LM_discB,
    pairBilAnti_eq_zero_of_left_zero _ _ _ _ _ _ b3LM_discA,
    pairBilAnti_23_disc]
  norm_num

theorem bilPlaqAnticommutator_disc :
    bilPlaqAnticommutator witnessU witnessPlaquette discA discB = 0 := by
  show firstBilPlaq witnessU witnessPlaquette discA discB
    + secondBilPlaqAnti witnessU witnessPlaquette discA discB = 0
  rw [firstBilPlaq_disc, secondBilPlaqAnti_disc]
  norm_num

theorem firstBilPlaqImSwap_disc :
    firstBilPlaqImSwap witnessU witnessPlaquette discA discB = 0 := by
  rw [firstBilPlaqImSwap_apply, curlMatLM_discA, curlMatLM_discB,
    imHolonomy_witnessU_witnessPlaquette, smulILM_apply, smulILM_apply]
  have h1 : (Complex.I • (-(AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal)))
      = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal, Matrix.smul_apply]
  have h2 : (Complex.I • sigma1IVal) = !![0, -1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigma1IVal, Matrix.smul_apply]
  rw [h1, h2, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  norm_num [Complex.I_mul_I, Complex.ext_iff]

theorem pairBilReSwap_23_disc :
    pairBilReSwap witnessU witnessPlaquette (b2LM witnessPlaquette) (b3LM witnessPlaquette)
      discA discB = 0 := by
  rw [pairBilReSwap_apply, b2LM_discA, b3LM_discB, reHolonomy_sub_one_witnessPlaquette,
    smulILM_apply, smulILM_apply]
  have h1 : (Complex.I • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![Complex.I, 0; 0, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  have h2 : (Complex.I • (!![0, -1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![0, -Complex.I; -Complex.I, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  rw [h1, h2, Matrix.mul_neg, Matrix.mul_one, Matrix.mul_neg, Matrix.mul_one,
    Matrix.trace_neg, Matrix.trace_neg, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of, Matrix.trace_fin_two_of]
  norm_num [Complex.I_mul_I, Complex.ext_iff]

theorem secondBilPlaqReSwap_disc :
    secondBilPlaqReSwap witnessU witnessPlaquette discA discB = 0 := by
  rw [secondBilPlaqReSwap_apply,
    pairBilReSwap_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBilReSwap_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBilReSwap_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBilReSwap_eq_zero_of_right_zero _ _ _ _ _ _ b4LM_discB,
    pairBilReSwap_eq_zero_of_left_zero _ _ _ _ _ _ b3LM_discA,
    pairBilReSwap_23_disc]
  norm_num

theorem bilPlaqHolonomySwap_disc :
    bilPlaqHolonomySwap witnessU witnessPlaquette discA discB = 0 := by
  show firstBilPlaqImSwap witnessU witnessPlaquette discA discB
    + secondBilPlaqReSwap witnessU witnessPlaquette discA discB = 0
  rw [firstBilPlaqImSwap_disc, secondBilPlaqReSwap_disc]
  norm_num

theorem secondBilPlaqDrop23_disc :
    secondBilPlaqDrop23 witnessU witnessPlaquette discA discB = 0 := by
  rw [secondBilPlaqDrop23_apply,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBil_eq_zero_of_right_zero _ _ _ _ _ _ b4LM_discB,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b3LM_discA]
  norm_num

theorem bilPlaqDrop23_disc : bilPlaqDrop23 witnessU witnessPlaquette discA discB = 0 := by
  show firstBilPlaq witnessU witnessPlaquette discA discB
    + secondBilPlaqDrop23 witnessU witnessPlaquette discA discB = 0
  rw [firstBilPlaq_disc, secondBilPlaqDrop23_disc]
  norm_num

theorem bilPlaqDoubled_disc : bilPlaqDoubled witnessU witnessPlaquette discA discB = 8 := by
  rw [bilPlaqDoubled_apply, bilPlaq_disc]
  norm_num

/-! #### The DIAGONAL values at `(discA, discA)`, which separate the FIRST term -/

theorem firstBilPlaq_disc_diag :
    firstBilPlaq witnessU witnessPlaquette discA discA = -2 := by
  rw [firstBilPlaq_apply, curlMatLM_discA, reHolonomy_sub_one_witnessPlaquette, smulILM_apply]
  have h1 : (Complex.I • (-(AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal)))
      = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal, Matrix.smul_apply]
  rw [h1, Matrix.mul_neg, Matrix.mul_one, Matrix.trace_neg, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of]
  norm_num

theorem secondBilPlaq_disc_diag :
    secondBilPlaq witnessU witnessPlaquette discA discA = 0 := by
  rw [secondBilPlaq_apply,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b1LM_discA,
    pairBil_eq_zero_of_right_zero _ _ _ _ _ _ b3LM_discA,
    pairBil_eq_zero_of_right_zero _ _ _ _ _ _ b4LM_discA,
    pairBil_eq_zero_of_left_zero _ _ _ _ _ _ b3LM_discA]
  norm_num

theorem bilPlaq_disc_diag : bilPlaq witnessU witnessPlaquette discA discA = -2 := by
  rw [bilPlaq_apply, firstBilPlaq_disc_diag, secondBilPlaq_disc_diag]
  norm_num

/-! #### THE SEVEN SEPARATION THEOREMS — each fails for a COHERENT substitution -/

/-- Sol's own coherent counter-object: the ZERO form. It is symmetric, self-adjoint after promotion,
and passes all seven forced facts — and it is `≠ bilPlaq`. -/
theorem bilPlaq_ne_zeroForm :
    bilPlaq witnessU witnessPlaquette
      ≠ (0 : (Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo) →ₗ[ℝ]
          (Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo) →ₗ[ℝ] ℝ) := by
  intro h
  have hv := congrArg (fun b => b discA discB) h
  simp only [LinearMap.zero_apply] at hv
  rw [bilPlaq_disc] at hv
  norm_num at hv

theorem bilPlaq_ne_anticommutator :
    bilPlaq witnessU witnessPlaquette ≠ bilPlaqAnticommutator witnessU witnessPlaquette := by
  intro h
  have hv := congrArg (fun b => b discA discB) h
  rw [bilPlaq_disc, bilPlaqAnticommutator_disc] at hv
  norm_num at hv

theorem bilPlaq_ne_firstTermOnly :
    bilPlaq witnessU witnessPlaquette ≠ firstBilPlaq witnessU witnessPlaquette := by
  intro h
  have hv := congrArg (fun b => b discA discB) h
  rw [bilPlaq_disc, firstBilPlaq_disc] at hv
  norm_num at hv

theorem bilPlaq_ne_secondTermOnly :
    bilPlaq witnessU witnessPlaquette ≠ secondBilPlaq witnessU witnessPlaquette := by
  intro h
  have hv := congrArg (fun b => b discA discA) h
  rw [bilPlaq_disc_diag, secondBilPlaq_disc_diag] at hv
  norm_num at hv

theorem bilPlaq_ne_holonomySwap :
    bilPlaq witnessU witnessPlaquette ≠ bilPlaqHolonomySwap witnessU witnessPlaquette := by
  intro h
  have hv := congrArg (fun b => b discA discB) h
  rw [bilPlaq_disc, bilPlaqHolonomySwap_disc] at hv
  norm_num at hv

theorem bilPlaq_ne_drop23 :
    bilPlaq witnessU witnessPlaquette ≠ bilPlaqDrop23 witnessU witnessPlaquette := by
  intro h
  have hv := congrArg (fun b => b discA discB) h
  rw [bilPlaq_disc, bilPlaqDrop23_disc] at hv
  norm_num at hv

/-- **THE CONVICTED DEFECT IS ITSELF DISCRIMINABLE AT THE FORM LEVEL.** So the factor-2
normalization is not a matter of taste inside this construction: `bilPlaq` and `2·bilPlaq` are
different bilinear forms, provably, at a named witness. -/
theorem bilPlaq_ne_doubled :
    bilPlaq witnessU witnessPlaquette ≠ bilPlaqDoubled witnessU witnessPlaquette := by
  intro h
  have hv := congrArg (fun b => b discA discB) h
  rw [bilPlaq_disc, bilPlaqDoubled_disc] at hv
  norm_num at hv

/-! #### THE DEGENERACY CONTROL — at the FLAT background all seven forms COINCIDE -/

theorem firstBilPlaq_trivialU_eq_zero (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    firstBilPlaq (trivialU (L := L)) p A B = 0 := by
  rw [firstBilPlaq_apply, reHolonomy_trivialU, sub_self]
  simp

theorem firstBilPlaqImSwap_trivialU_eq_zero (p : PeriodicLatticePlaquette L)
    (A B : Bond L → SuTwo) : firstBilPlaqImSwap (trivialU (L := L)) p A B = 0 := by
  rw [firstBilPlaqImSwap_apply, imHolonomy_trivialU]
  simp

theorem pairBil_trivialU_eq_zero (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo) :
    pairBil (trivialU (L := L)) p f g A B = 0 := by
  rw [pairBil_apply, imHolonomy_trivialU]
  simp

theorem pairBilAnti_trivialU_eq_zero (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo) :
    pairBilAnti (trivialU (L := L)) p f g A B = 0 := by
  rw [pairBilAnti_apply, imHolonomy_trivialU]
  simp

theorem pairBilReSwap_trivialU_eq_zero (p : PeriodicLatticePlaquette L)
    (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo) :
    pairBilReSwap (trivialU (L := L)) p f g A B = 0 := by
  rw [pairBilReSwap_apply, reHolonomy_trivialU, sub_self]
  simp

/-- **THE DEGENERATE TEST POINT, EXHIBITED (§GREEN class 5, §DEGEN).** At the FLAT background all
seven forms — the built `bilPlaq`, the zero form, and the five coherent wrong transcriptions — are
IDENTICALLY equal (all zero) for every plaquette and every argument pair. So every separation
theorem above would report "agree" there no matter which transcription is right: the discrimination
is a property of the WITNESS `witnessU`, not of the checks, and `trivialU` is exactly the point at
which this whole section reports green while proving nothing. -/
theorem all_variants_coincide_at_trivialU (p : PeriodicLatticePlaquette L)
    (A B : Bond L → SuTwo) :
    bilPlaq (trivialU (L := L)) p A B = 0
      ∧ bilPlaqAnticommutator (trivialU (L := L)) p A B = 0
      ∧ bilPlaqHolonomySwap (trivialU (L := L)) p A B = 0
      ∧ bilPlaqDrop23 (trivialU (L := L)) p A B = 0
      ∧ bilPlaqDoubled (trivialU (L := L)) p A B = 0
      ∧ firstBilPlaq (trivialU (L := L)) p A B = 0
      ∧ secondBilPlaq (trivialU (L := L)) p A B = 0 := by
  have hs : secondBilPlaq (trivialU (L := L)) p A B = 0 := by
    rw [secondBilPlaq_apply, pairBil_trivialU_eq_zero, pairBil_trivialU_eq_zero,
      pairBil_trivialU_eq_zero, pairBil_trivialU_eq_zero, pairBil_trivialU_eq_zero,
      pairBil_trivialU_eq_zero]
    norm_num
  have hf : firstBilPlaq (trivialU (L := L)) p A B = 0 := firstBilPlaq_trivialU_eq_zero p A B
  have hb : bilPlaq (trivialU (L := L)) p A B = 0 := by
    rw [bilPlaq_apply, hf, hs]; norm_num
  refine ⟨hb, ?_, ?_, ?_, ?_, hf, hs⟩
  · show firstBilPlaq (trivialU (L := L)) p A B
      + secondBilPlaqAnti (trivialU (L := L)) p A B = 0
    rw [hf, secondBilPlaqAnti_apply, pairBilAnti_trivialU_eq_zero, pairBilAnti_trivialU_eq_zero,
      pairBilAnti_trivialU_eq_zero, pairBilAnti_trivialU_eq_zero, pairBilAnti_trivialU_eq_zero,
      pairBilAnti_trivialU_eq_zero]
    norm_num
  · show firstBilPlaqImSwap (trivialU (L := L)) p A B
      + secondBilPlaqReSwap (trivialU (L := L)) p A B = 0
    rw [firstBilPlaqImSwap_trivialU_eq_zero, secondBilPlaqReSwap_apply,
      pairBilReSwap_trivialU_eq_zero, pairBilReSwap_trivialU_eq_zero,
      pairBilReSwap_trivialU_eq_zero, pairBilReSwap_trivialU_eq_zero,
      pairBilReSwap_trivialU_eq_zero, pairBilReSwap_trivialU_eq_zero]
    norm_num
  · show firstBilPlaq (trivialU (L := L)) p A B
      + secondBilPlaqDrop23 (trivialU (L := L)) p A B = 0
    rw [hf, secondBilPlaqDrop23_apply, pairBil_trivialU_eq_zero, pairBil_trivialU_eq_zero,
      pairBil_trivialU_eq_zero, pairBil_trivialU_eq_zero, pairBil_trivialU_eq_zero]
    norm_num
  · rw [bilPlaqDoubled_apply, hb]; norm_num

#print axioms traceForm_zero_middle
#print axioms pairBilAnti
#print axioms pairBilAnti_apply
#print axioms pairBilAnti_eq_zero_of_left_zero
#print axioms pairBilAnti_eq_zero_of_right_zero
#print axioms secondBilPlaqAnti
#print axioms secondBilPlaqAnti_apply
#print axioms bilPlaqAnticommutator
#print axioms pairBilReSwap
#print axioms pairBilReSwap_apply
#print axioms pairBilReSwap_eq_zero_of_left_zero
#print axioms pairBilReSwap_eq_zero_of_right_zero
#print axioms secondBilPlaqReSwap
#print axioms secondBilPlaqReSwap_apply
#print axioms firstBilPlaqImSwap
#print axioms firstBilPlaqImSwap_apply
#print axioms bilPlaqHolonomySwap
#print axioms secondBilPlaqDrop23
#print axioms secondBilPlaqDrop23_apply
#print axioms bilPlaqDrop23
#print axioms bilPlaqDoubled
#print axioms bilPlaqDoubled_apply
#print axioms pairBilAnti_23_disc
#print axioms secondBilPlaqAnti_disc
#print axioms bilPlaqAnticommutator_disc
#print axioms firstBilPlaqImSwap_disc
#print axioms pairBilReSwap_23_disc
#print axioms secondBilPlaqReSwap_disc
#print axioms bilPlaqHolonomySwap_disc
#print axioms secondBilPlaqDrop23_disc
#print axioms bilPlaqDrop23_disc
#print axioms bilPlaqDoubled_disc
#print axioms firstBilPlaq_disc_diag
#print axioms secondBilPlaq_disc_diag
#print axioms bilPlaq_disc_diag
#print axioms bilPlaq_ne_zeroForm
#print axioms bilPlaq_ne_anticommutator
#print axioms bilPlaq_ne_firstTermOnly
#print axioms bilPlaq_ne_secondTermOnly
#print axioms bilPlaq_ne_holonomySwap
#print axioms bilPlaq_ne_drop23
#print axioms bilPlaq_ne_doubled
#print axioms firstBilPlaq_trivialU_eq_zero
#print axioms firstBilPlaqImSwap_trivialU_eq_zero
#print axioms pairBil_trivialU_eq_zero
#print axioms pairBilAnti_trivialU_eq_zero
#print axioms pairBilReSwap_trivialU_eq_zero
#print axioms all_variants_coincide_at_trivialU

/-! ### N.8 — ALL SIX BRACKETS SEPARATED: closing what N.7 could not

N.7's witness pair `(discA, discB)` activates only the `A′₂` and `A′₃` slots, so it cannot separate a
variant that leaves the `(2,3)` bracket intact and alters another. That limitation is CLOSED here
rather than left as a residual.

Two further single-bond field FAMILIES are built, parametrised by their `𝔰𝔲(2)` value:

* `cField V` sits on the bond `(shift_ν x, μ) = (shift_1 witnessY, 0)`, which is the bond
  `AprimeZW` reads, so it activates `A′₁` — and only `A′₁` (`b2LM_cField`/`b3LM_cField`/`b4LM_cField`
  are all `0`). Since `witnessU (witnessY, 1) = 1`, `RMap_one` gives `A′₁ = -V` exactly.
* `dField V` sits on `(shift_μ x, ν) = (shift_0 witnessY, 1)`, the bond `AprimeYZ` reads, so it
  activates `A′₄` and only `A′₄`. Since `witnessU (witnessY, 0) = witnessMElem`, `A′₄ = R(M)V`, and
  `R(M)` is computed on both available `𝔰𝔲(2)` directions: `RMap_witnessMElem` (already in the tree)
  and `RMap_witnessMElem_sigma1I` (proved here) — both send their generator to its negative.

With `discA` (activates `A′₂`), `discB` (`A′₃`), `cField` (`A′₁`) and `dField` (`A′₄`), each of the six
ordered pairs `i<j` gets an argument pair at which its bracket is NONZERO:

| bracket | argument pair | value |
|---|---|---:|
| `(1,2)` | `(cField sigma1I, discA)` | `4` |
| `(1,3)` | `(cField suTwoWitness, discB)` | `4` |
| `(1,4)` | `(cField suTwoWitness, dField sigma1I)` | `-4` |
| `(2,3)` | `(discA, discB)` | `4` |
| `(2,4)` | `(discA, dField sigma1I)` | `-4` |
| `(3,4)` | `(discB, dField suTwoWitness)` | `-4` |

`bilPlaqDropPair U p f g := bilPlaq U p - pairBil U p f g` is ONE coherent variant schema covering
all six omissions (and `bilPlaqDrop23_eq_dropPair` proves N.7's hand-written `bilPlaqDrop23` is its
`(2,3)` instance, so the two constructions agree). The six separations then say: **omitting ANY ONE of
the six brackets changes the form.** Hence no proper subset of the six reproduces `bilPlaq` — which
subsumes the "three adjacent pairs only" variant N.7 could not reach, and closes the family.

Direction check the values themselves supply: the bracket is antisymmetric, so `(1,2)` at
`(cField sigma1I, discA)` is `+4` while `(1,4)` at `(cField suTwoWitness, dField sigma1I)` is `-4`;
the two `𝔰𝔲(2)` generators enter in opposite orders. A transcription that symmetrised a bracket, or
transposed one matrix ordering inside it, moves these numbers.
-/

/-! The `A′₁` activator: a single-bond field on `(shift_ν x, μ)` = `(shift_1 witnessY, 0)`. -/
noncomputable def cBond : Bond witnessL := (periodicLatticeShift witnessY 1, (0 : Fin 3))

noncomputable def dBond : Bond witnessL := (periodicLatticeShift witnessY 0, (1 : Fin 3))

noncomputable def cField (V : SuTwo) : Bond witnessL → SuTwo :=
  fun e => if e = cBond then V else 0

noncomputable def dField (V : SuTwo) : Bond witnessL → SuTwo :=
  fun e => if e = dBond then V else 0

theorem cField_at (V : SuTwo) : cField V cBond = V := by simp [cField]

theorem cField_elsewhere (V : SuTwo) {e : Bond witnessL} (h : e ≠ cBond) : cField V e = 0 := by
  simp [cField, h]

theorem dField_at (V : SuTwo) : dField V dBond = V := by simp [dField]

theorem dField_elsewhere (V : SuTwo) {e : Bond witnessL} (h : e ≠ dBond) : dField V e = 0 := by
  simp [dField, h]

/-! ### The four `A′` slots of `cField V` at `witnessPlaquette` -/

theorem AprimeZW_cField (V : SuTwo) :
    AprimeZW witnessU (cField V) witnessPlaquette = -V := by
  show -RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.2))
    (cField V (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.2,
      witnessPlaquette.2.1.1)) = -V
  rw [show (witnessPlaquette.1, witnessPlaquette.2.1.2) = (witnessY, (1 : Fin 3)) from rfl,
    witnessU_at_x_nu,
    show (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.2,
        witnessPlaquette.2.1.1) = cBond from rfl,
    cField_at, RMap_one]
  rfl

theorem AprimeWX_cField (V : SuTwo) : AprimeWX (cField V) witnessPlaquette = 0 := by
  show -(cField V (witnessPlaquette.1, witnessPlaquette.2.1.2)) = 0
  rw [cField_elsewhere V (show (witnessPlaquette.1, witnessPlaquette.2.1.2) ≠ cBond by decide)]
  simp

theorem AprimeXY_cField (V : SuTwo) : AprimeXY (cField V) witnessPlaquette = 0 :=
  cField_elsewhere V (show (witnessPlaquette.1, witnessPlaquette.2.1.1) ≠ cBond by decide)

theorem AprimeYZ_cField (V : SuTwo) : AprimeYZ witnessU (cField V) witnessPlaquette = 0 := by
  show RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.1))
    (cField V (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.1,
      witnessPlaquette.2.1.2)) = 0
  rw [cField_elsewhere V (show (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.1,
    witnessPlaquette.2.1.2) ≠ cBond by decide)]
  simp

/-! ### The four `A′` slots of `dField V` at `witnessPlaquette` -/

theorem AprimeYZ_dField (V : SuTwo) :
    AprimeYZ witnessU (dField V) witnessPlaquette = RMap witnessMElem V := by
  show RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.1))
    (dField V (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.1,
      witnessPlaquette.2.1.2)) = _
  rw [show (witnessPlaquette.1, witnessPlaquette.2.1.1) = (witnessY, (0 : Fin 3)) from rfl,
    witnessU_at_x_mu,
    show (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.1,
        witnessPlaquette.2.1.2) = dBond from rfl,
    dField_at]

theorem AprimeZW_dField (V : SuTwo) : AprimeZW witnessU (dField V) witnessPlaquette = 0 := by
  show -RMap (witnessU (witnessPlaquette.1, witnessPlaquette.2.1.2))
    (dField V (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.2,
      witnessPlaquette.2.1.1)) = 0
  rw [dField_elsewhere V (show (periodicLatticeShift witnessPlaquette.1 witnessPlaquette.2.1.2,
    witnessPlaquette.2.1.1) ≠ dBond by decide)]
  simp

theorem AprimeWX_dField (V : SuTwo) : AprimeWX (dField V) witnessPlaquette = 0 := by
  show -(dField V (witnessPlaquette.1, witnessPlaquette.2.1.2)) = 0
  rw [dField_elsewhere V (show (witnessPlaquette.1, witnessPlaquette.2.1.2) ≠ dBond by decide)]
  simp

theorem AprimeXY_dField (V : SuTwo) : AprimeXY (dField V) witnessPlaquette = 0 :=
  dField_elsewhere V (show (witnessPlaquette.1, witnessPlaquette.2.1.1) ≠ dBond by decide)

/-! ### The `bᵢ` reads -/

theorem b1LM_cField (V : SuTwo) :
    b1LM witnessU witnessPlaquette (cField V)
      = Complex.I • (-(V : Matrix (Fin 2) (Fin 2) ℂ)) := by
  show smulILM (a1LM witnessU witnessPlaquette (cField V)) = _
  rw [show a1LM witnessU witnessPlaquette (cField V)
      = ((AprimeZW witnessU (cField V) witnessPlaquette : SuTwo) :
          Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    AprimeZW_cField, smulILM_apply]
  simp

theorem b2LM_cField (V : SuTwo) : b2LM witnessPlaquette (cField V) = 0 := by
  show smulILM (a2LM witnessPlaquette (cField V)) = 0
  rw [show a2LM witnessPlaquette (cField V)
      = ((AprimeWX (cField V) witnessPlaquette : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    AprimeWX_cField, smulILM_apply]
  simp

theorem b3LM_cField (V : SuTwo) : b3LM witnessPlaquette (cField V) = 0 := by
  show smulILM (a3LM witnessPlaquette (cField V)) = 0
  rw [show a3LM witnessPlaquette (cField V)
      = ((AprimeXY (cField V) witnessPlaquette : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    AprimeXY_cField, smulILM_apply]
  simp

theorem b4LM_cField (V : SuTwo) : b4LM witnessU witnessPlaquette (cField V) = 0 := by
  show smulILM (a4LM witnessU witnessPlaquette (cField V)) = 0
  rw [show a4LM witnessU witnessPlaquette (cField V)
      = ((AprimeYZ witnessU (cField V) witnessPlaquette : SuTwo) :
          Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    AprimeYZ_cField, smulILM_apply]
  simp

theorem b4LM_dField (V : SuTwo) :
    b4LM witnessU witnessPlaquette (dField V)
      = Complex.I • ((RMap witnessMElem V : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  show smulILM (a4LM witnessU witnessPlaquette (dField V)) = _
  rw [show a4LM witnessU witnessPlaquette (dField V)
      = ((AprimeYZ witnessU (dField V) witnessPlaquette : SuTwo) :
          Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    AprimeYZ_dField, smulILM_apply]

theorem b1LM_dField (V : SuTwo) : b1LM witnessU witnessPlaquette (dField V) = 0 := by
  show smulILM (a1LM witnessU witnessPlaquette (dField V)) = 0
  rw [show a1LM witnessU witnessPlaquette (dField V)
      = ((AprimeZW witnessU (dField V) witnessPlaquette : SuTwo) :
          Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    AprimeZW_dField, smulILM_apply]
  simp

theorem b2LM_dField (V : SuTwo) : b2LM witnessPlaquette (dField V) = 0 := by
  show smulILM (a2LM witnessPlaquette (dField V)) = 0
  rw [show a2LM witnessPlaquette (dField V)
      = ((AprimeWX (dField V) witnessPlaquette : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    AprimeWX_dField, smulILM_apply]
  simp

theorem b3LM_dField (V : SuTwo) : b3LM witnessPlaquette (dField V) = 0 := by
  show smulILM (a3LM witnessPlaquette (dField V)) = 0
  rw [show a3LM witnessPlaquette (dField V)
      = ((AprimeXY (dField V) witnessPlaquette : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
    AprimeXY_dField, smulILM_apply]
  simp

/-! ### `RMap witnessMElem sigma1I = -sigma1I` -/

theorem RMap_witnessMElem_sigma1I : RMap witnessMElem sigma1I = -sigma1I := by
  apply Subtype.ext
  rw [AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply]
  change witnessM * sigma1IVal * Matrix.conjTranspose witnessM = -sigma1IVal
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessM, sigma1IVal, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The four concrete `bᵢ` matrix values -/

theorem b1LM_cField_witness :
    b1LM witnessU witnessPlaquette (cField suTwoWitness)
      = (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [b1LM_cField]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.Balaban.CovariantOperators.suTwoWitness, suTwoWitnessVal, Matrix.smul_apply]

theorem b1LM_cField_sigma1 :
    b1LM witnessU witnessPlaquette (cField sigma1I)
      = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [b1LM_cField, sigma1I_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma1IVal, Matrix.smul_apply]

theorem b4LM_dField_witness :
    b4LM witnessU witnessPlaquette (dField suTwoWitness)
      = (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [b4LM_dField, RMap_witnessMElem]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.Balaban.CovariantOperators.suTwoWitness, suTwoWitnessVal, Matrix.smul_apply]

theorem b4LM_dField_sigma1 :
    b4LM witnessU witnessPlaquette (dField sigma1I)
      = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [b4LM_dField, RMap_witnessMElem_sigma1I]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma1I, sigma1IVal, Matrix.smul_apply]

/-! ### The curls -/

theorem curlMatLM_cField (V : SuTwo) :
    curlMatLM witnessU witnessPlaquette (cField V) = -(V : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [curlMatLM_apply, ← sum_Aprime_eq_curl, AprimeXY_cField, AprimeYZ_cField, AprimeZW_cField,
    AprimeWX_cField]
  simp

theorem curlMatLM_dField (V : SuTwo) :
    curlMatLM witnessU witnessPlaquette (dField V)
      = ((RMap witnessMElem V : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [curlMatLM_apply, ← sum_Aprime_eq_curl, AprimeXY_dField, AprimeYZ_dField, AprimeZW_dField,
    AprimeWX_dField]
  simp

theorem curlMatLM_cField_witness :
    Complex.I • curlMatLM witnessU witnessPlaquette (cField suTwoWitness)
      = (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [curlMatLM_cField]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.Balaban.CovariantOperators.suTwoWitness, suTwoWitnessVal, Matrix.smul_apply]

theorem curlMatLM_cField_sigma1 :
    Complex.I • curlMatLM witnessU witnessPlaquette (cField sigma1I)
      = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [curlMatLM_cField, sigma1I_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma1IVal, Matrix.smul_apply]

theorem curlMatLM_dField_witness :
    Complex.I • curlMatLM witnessU witnessPlaquette (dField suTwoWitness)
      = (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [curlMatLM_dField, RMap_witnessMElem]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.Balaban.CovariantOperators.suTwoWitness, suTwoWitnessVal, Matrix.smul_apply]

theorem curlMatLM_dField_sigma1 :
    Complex.I • curlMatLM witnessU witnessPlaquette (dField sigma1I)
      = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [curlMatLM_dField, RMap_witnessMElem_sigma1I]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma1I, sigma1IVal, Matrix.smul_apply]

/-! ### Generic bracket evaluation, then the four scalar brackets -/

theorem pairBil_witness_eq
    (f g : (Bond witnessL → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ)
    (A B : Bond witnessL → SuTwo)
    {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hf : f A = X) (hg : g B = Y) :
    pairBil witnessU witnessPlaquette f g A B
      = (Matrix.trace (Complex.I • X * Y * !![0, -Complex.I; Complex.I, 0])).re
        - (Matrix.trace (Complex.I • Y * X * !![0, -Complex.I; Complex.I, 0])).re := by
  rw [pairBil_apply, imHolonomy_witnessU_witnessPlaquette, smulILM_apply, smulILM_apply, hf, hg]

theorem firstBilPlaq_witness_eq
    (A B : Bond witnessL → SuTwo) {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : Complex.I • curlMatLM witnessU witnessPlaquette A = X)
    (hB : Complex.I • curlMatLM witnessU witnessPlaquette B = Y) :
    firstBilPlaq witnessU witnessPlaquette A B
      = (Matrix.trace (X * Y * (-(1 : Matrix (Fin 2) (Fin 2) ℂ)))).re := by
  rw [firstBilPlaq_apply, reHolonomy_sub_one_witnessPlaquette, smulILM_apply, smulILM_apply, hA, hB]

theorem trBracket_QP :
    (Matrix.trace (Complex.I • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0]
        * !![0, -Complex.I; Complex.I, 0])).re
      - (Matrix.trace (Complex.I • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, -1]
        * !![0, -Complex.I; Complex.I, 0])).re = -4 := by
  have h1 : (Complex.I • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![Complex.I, 0; 0, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  have h2 : (Complex.I • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![0, Complex.I; Complex.I, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  rw [h1, h2, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of, Matrix.trace_fin_two_of]
  simp only [Complex.add_re]
  norm_num [Complex.I_mul_I, Complex.ext_iff]

theorem trBracket_PQ :
    (Matrix.trace (Complex.I • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 0; 0, -1]
        * !![0, -Complex.I; Complex.I, 0])).re
      - (Matrix.trace (Complex.I • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0]
        * !![0, -Complex.I; Complex.I, 0])).re = 4 := by
  have h := trBracket_QP
  linarith

theorem trBracket_Q_negP :
    (Matrix.trace (Complex.I • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, -1; -1, 0]
        * !![0, -Complex.I; Complex.I, 0])).re
      - (Matrix.trace (Complex.I • (!![0, -1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
        * !![1, 0; 0, -1] * !![0, -Complex.I; Complex.I, 0])).re = 4 := by
  have h1 : (Complex.I • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![Complex.I, 0; 0, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  have h2 : (Complex.I • (!![0, -1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![0, -Complex.I; -Complex.I, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  rw [h1, h2, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.trace_fin_two_of, Matrix.trace_fin_two_of]
  simp only [Complex.add_re]
  norm_num [Complex.I_mul_I, Complex.ext_iff]

theorem trBracket_negP_Q :
    (Matrix.trace (Complex.I • (!![0, -1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
        * !![1, 0; 0, -1] * !![0, -Complex.I; Complex.I, 0])).re
      - (Matrix.trace (Complex.I • (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)
        * !![0, -1; -1, 0] * !![0, -Complex.I; Complex.I, 0])).re = -4 := by
  have h := trBracket_Q_negP
  linarith

/-! ### The five remaining brackets, each NONZERO at its own witness pair -/

theorem pairBil_12_witness :
    pairBil witnessU witnessPlaquette (b1LM witnessU witnessPlaquette) (b2LM witnessPlaquette)
      (cField sigma1I) discA = 4 := by
  rw [pairBil_witness_eq _ _ _ _ b1LM_cField_sigma1 b2LM_discA, trBracket_PQ]

theorem pairBil_13_witness :
    pairBil witnessU witnessPlaquette (b1LM witnessU witnessPlaquette) (b3LM witnessPlaquette)
      (cField suTwoWitness) discB = 4 := by
  rw [pairBil_witness_eq _ _ _ _ b1LM_cField_witness b3LM_discB, trBracket_Q_negP]

theorem pairBil_14_witness :
    pairBil witnessU witnessPlaquette (b1LM witnessU witnessPlaquette)
      (b4LM witnessU witnessPlaquette) (cField suTwoWitness) (dField sigma1I) = -4 := by
  rw [pairBil_witness_eq _ _ _ _ b1LM_cField_witness b4LM_dField_sigma1, trBracket_QP]

theorem pairBil_24_witness :
    pairBil witnessU witnessPlaquette (b2LM witnessPlaquette)
      (b4LM witnessU witnessPlaquette) discA (dField sigma1I) = -4 := by
  rw [pairBil_witness_eq _ _ _ _ b2LM_discA b4LM_dField_sigma1, trBracket_QP]

theorem pairBil_34_witness :
    pairBil witnessU witnessPlaquette (b3LM witnessPlaquette)
      (b4LM witnessU witnessPlaquette) discB (dField suTwoWitness) = -4 := by
  rw [pairBil_witness_eq _ _ _ _ b3LM_discB b4LM_dField_witness, trBracket_negP_Q]

theorem pairBil_23_witness :
    pairBil witnessU witnessPlaquette (b2LM witnessPlaquette) (b3LM witnessPlaquette)
      discA discB = 4 := by
  rw [pairBil_apply, traceAtom23_disc, traceAtom32_disc]
  norm_num

/-! ### THE DROP-ONE-BRACKET VARIANT, AND SIX SEPARATIONS -/

noncomputable def bilPlaqDropPair
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (p : PeriodicLatticePlaquette witnessL)
    (f g : (Bond witnessL → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) :
    (Bond witnessL → SuTwo) →ₗ[ℝ] (Bond witnessL → SuTwo) →ₗ[ℝ] ℝ :=
  bilPlaq U p - pairBil U p f g

theorem bilPlaqDropPair_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (p : PeriodicLatticePlaquette witnessL)
    (f g : (Bond witnessL → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ)
    (A B : Bond witnessL → SuTwo) :
    bilPlaqDropPair U p f g A B = bilPlaq U p A B - pairBil U p f g A B := rfl

theorem bilPlaqDrop23_eq_dropPair
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (p : PeriodicLatticePlaquette witnessL) :
    bilPlaqDrop23 U p = bilPlaqDropPair U p (b2LM p) (b3LM p) := by
  refine LinearMap.ext (fun A => LinearMap.ext (fun B => ?_))
  show firstBilPlaq U p A B + secondBilPlaqDrop23 U p A B
    = bilPlaq U p A B - pairBil U p (b2LM p) (b3LM p) A B
  rw [secondBilPlaqDrop23_apply, bilPlaq_apply, secondBilPlaq_apply]
  ring

theorem bilPlaq_ne_dropPair_12 :
    bilPlaq witnessU witnessPlaquette
      ≠ bilPlaqDropPair witnessU witnessPlaquette (b1LM witnessU witnessPlaquette)
          (b2LM witnessPlaquette) := by
  intro h
  have hv := congrArg (fun b => b (cField sigma1I) discA) h
  rw [bilPlaqDropPair_apply, pairBil_12_witness] at hv
  linarith

theorem bilPlaq_ne_dropPair_13 :
    bilPlaq witnessU witnessPlaquette
      ≠ bilPlaqDropPair witnessU witnessPlaquette (b1LM witnessU witnessPlaquette)
          (b3LM witnessPlaquette) := by
  intro h
  have hv := congrArg (fun b => b (cField suTwoWitness) discB) h
  rw [bilPlaqDropPair_apply, pairBil_13_witness] at hv
  linarith

theorem bilPlaq_ne_dropPair_14 :
    bilPlaq witnessU witnessPlaquette
      ≠ bilPlaqDropPair witnessU witnessPlaquette (b1LM witnessU witnessPlaquette)
          (b4LM witnessU witnessPlaquette) := by
  intro h
  have hv := congrArg (fun b => b (cField suTwoWitness) (dField sigma1I)) h
  rw [bilPlaqDropPair_apply, pairBil_14_witness] at hv
  linarith

theorem bilPlaq_ne_dropPair_23 :
    bilPlaq witnessU witnessPlaquette
      ≠ bilPlaqDropPair witnessU witnessPlaquette (b2LM witnessPlaquette)
          (b3LM witnessPlaquette) := by
  intro h
  have hv := congrArg (fun b => b discA discB) h
  rw [bilPlaqDropPair_apply, pairBil_23_witness] at hv
  linarith

theorem bilPlaq_ne_dropPair_24 :
    bilPlaq witnessU witnessPlaquette
      ≠ bilPlaqDropPair witnessU witnessPlaquette (b2LM witnessPlaquette)
          (b4LM witnessU witnessPlaquette) := by
  intro h
  have hv := congrArg (fun b => b discA (dField sigma1I)) h
  rw [bilPlaqDropPair_apply, pairBil_24_witness] at hv
  linarith

theorem bilPlaq_ne_dropPair_34 :
    bilPlaq witnessU witnessPlaquette
      ≠ bilPlaqDropPair witnessU witnessPlaquette (b3LM witnessPlaquette)
          (b4LM witnessU witnessPlaquette) := by
  intro h
  have hv := congrArg (fun b => b discB (dField suTwoWitness)) h
  rw [bilPlaqDropPair_apply, pairBil_34_witness] at hv
  linarith


#print axioms cBond
#print axioms dBond
#print axioms cField
#print axioms dField
#print axioms cField_at
#print axioms cField_elsewhere
#print axioms dField_at
#print axioms dField_elsewhere
#print axioms AprimeZW_cField
#print axioms AprimeWX_cField
#print axioms AprimeXY_cField
#print axioms AprimeYZ_cField
#print axioms AprimeYZ_dField
#print axioms AprimeZW_dField
#print axioms AprimeWX_dField
#print axioms AprimeXY_dField
#print axioms b1LM_cField
#print axioms b2LM_cField
#print axioms b3LM_cField
#print axioms b4LM_cField
#print axioms b4LM_dField
#print axioms b1LM_dField
#print axioms b2LM_dField
#print axioms b3LM_dField
#print axioms RMap_witnessMElem_sigma1I
#print axioms b1LM_cField_witness
#print axioms b1LM_cField_sigma1
#print axioms b4LM_dField_witness
#print axioms b4LM_dField_sigma1
#print axioms curlMatLM_cField
#print axioms curlMatLM_dField
#print axioms curlMatLM_cField_witness
#print axioms curlMatLM_cField_sigma1
#print axioms curlMatLM_dField_witness
#print axioms curlMatLM_dField_sigma1
#print axioms pairBil_witness_eq
#print axioms firstBilPlaq_witness_eq
#print axioms trBracket_QP
#print axioms trBracket_PQ
#print axioms trBracket_Q_negP
#print axioms trBracket_negP_Q
#print axioms pairBil_12_witness
#print axioms pairBil_13_witness
#print axioms pairBil_14_witness
#print axioms pairBil_24_witness
#print axioms pairBil_34_witness
#print axioms pairBil_23_witness
#print axioms bilPlaqDropPair
#print axioms bilPlaqDropPair_apply
#print axioms bilPlaqDrop23_eq_dropPair
#print axioms bilPlaq_ne_dropPair_12
#print axioms bilPlaq_ne_dropPair_13
#print axioms bilPlaq_ne_dropPair_14
#print axioms bilPlaq_ne_dropPair_23
#print axioms bilPlaq_ne_dropPair_24
#print axioms bilPlaq_ne_dropPair_34

/-! ### N.9 — THE NORMALIZATION IS PINNED AGAINST *EVERY* RESCALING, NOT JUST THE FACTOR 2

§S's uniform-rescale test ("if I multiplied this by 2, which assertion fails?") is answered by
`bilPlaq_ne_doubled`. The two theorems below strengthen that from the single factor `2` to the whole
scalar group, and state exactly what the `η = 1` specialization does and does NOT cost.

**What is proved:** no scalar rescaling of `bilPlaq` is invisible at the witness, and a common
rescaling of both sides preserves every separation. So the six/seven coherent-substitution
separations of §N.7 and §N.8 are not artifacts of this file's choice of overall normalization.

**What is NOT proved, said plainly so it is not misread:** this does NOT show that CMP99b (3.10)'s
`η^d η^{-2}` weight is an overall scalar multiple of the object built here. It is not. In the source,
`η` also enters the field normalization (`U′ = exp(iηA)`, p.390) and the difference operators, so the
general-`η` object is NOT `η^{d-2} ·` (the `η = 1` object), and no such factorization is claimed
anywhere in this module. The honest content of N.9 is narrower and exact: **whatever positive overall
constant a general-`η` treatment ends up carrying, it cannot make a wrong transcription agree with a
right one**, because a common nonzero rescaling preserves the separations. Building the genuinely
`η`-indexed carrier is a definitional gap in this tree (no type here has an `η` binder), recorded in
§10 item 9 and NOT closed here.
-/

/-- **NO SCALAR RESCALING IS INVISIBLE.** For every `c ≠ 1`, `c · bilPlaq ≠ bilPlaq`. This is §S's
uniform-rescale test in its strongest form for this object: the normalization is pinned at the form
level by the value `4` at `(discA, discB)`, not merely up to the factor-2 the conviction found. -/
theorem bilPlaq_ne_smul (c : ℝ) (hc : c ≠ 1) :
    bilPlaq witnessU witnessPlaquette ≠ c • bilPlaq witnessU witnessPlaquette := by
  intro h
  have hv := congrArg (fun b => b discA discB) h
  rw [show ((c • bilPlaq witnessU witnessPlaquette) discA discB : ℝ)
      = c * bilPlaq witnessU witnessPlaquette discA discB from rfl, bilPlaq_disc] at hv
  exact hc (by linarith)

/-- **A COMMON NONZERO RESCALING PRESERVES EVERY SEPARATION.** If two bilinear forms differ at a
point, so do their common rescalings by any `c ≠ 0`. Applied with `b` any of §N.7's or §N.8's
variants, this says the separations survive multiplication of the whole expression by whatever
positive constant a general-`η` treatment carries — see the section docstring for the exact scope of
that statement, which is NOT a factorization claim about `η`. -/
theorem separation_survives_common_rescaling
    (b : (Bond witnessL → SuTwo) →ₗ[ℝ] (Bond witnessL → SuTwo) →ₗ[ℝ] ℝ)
    (A B : Bond witnessL → SuTwo) (c : ℝ) (hc : c ≠ 0)
    (h : bilPlaq witnessU witnessPlaquette A B ≠ b A B) :
    (c • bilPlaq witnessU witnessPlaquette) A B ≠ (c • b) A B := by
  intro hcon
  rw [show ((c • bilPlaq witnessU witnessPlaquette) A B : ℝ)
      = c * bilPlaq witnessU witnessPlaquette A B from rfl,
    show ((c • b) A B : ℝ) = c * b A B from rfl] at hcon
  exact h (mul_left_cancel₀ hc hcon)

#print axioms bilPlaq_ne_smul
#print axioms separation_survives_common_rescaling

/-! ## §10 — HONEST LIMITS

1. **No coercivity, no positivity.** Nothing here bounds `C*Δ_kC` below. `deltaPrimeOp_not_nonneg`
   shows `Δ′` alone is indefinite, so `CStarDeltaKCOperator.inner_cStarDeltaKC_nonneg`'s hypothesis
   is not supplied and the sandwich's PSD is NOT claimed. The refuted naive coercivity target
   (`[CSTAR-LEVEL-MISMATCH]`) and the wrong-way ordering (`[CSTAR-SCHUR-GAP]`) are untouched.
2. **Diagonal-only vs not.** Enumerated in §0b. In particular `hT2` (= `inner_deltaPrimeCLM_eq`)
   does not by itself determine `T2`; the pinning datum is `deltaKCLM_symm`, proved here, and §9's
   `inner_deltaPrimeOp_disc` is an actual off-diagonal value.
3. **The convention is inherited, not decided here.** `deltaPrimeQuadFormTransported` (the
   `φ`-transported reading, `= -deltaPrimeQuadForm`) is used throughout because that is what
   `DeltaKFull.deltaKQuadFormCorrected` consumes. `DeltaPrime.lean` §11's own verdict — that which
   of the two readings is Bałaban's intent is a cross-file question tied to `curlValueCovariant`'s
   convention — is unchanged by this module. If that verdict ever flips, the flip is a single sign on
   `deltaPrimeBilRaw` and every theorem here transports.
4. **No `ell` hypothesis appears** because no domain is stated. `CStarDeltaKCOperator` §7(e) still
   applies to consumers: anything pairing this operator with the faithful `anchoredVFull` domain
   must carry `2 ≤ ell` (`ell = 1` collapses that domain to `⊥`).
5. **`witnessL` is a degenerate extent for OTHER purposes** — `AdmissibleSubspace.witnessL = fun _ => 3`
   fails `4 ≤ L μ` (`RegularUCurvedWitness.witnessL_fails_hL`). §8/§9 use it only as a
   NON-DEGENERACY witness (exhibiting nonzero values of a form defined for every extent), never to
   establish anything general, so that limitation does not bear on them. The general theorems
   (§1-§7) are stated for an arbitrary `L` and an arbitrary `U`.
6. **`k` does not appear.** As in `CStarDeltaKCOperator` §7(c): `Δ′` is a fine-scale plaquette sum
   with no RG level, and no `k`-dependence is claimed anywhere.
7. **TWO NORMALIZATIONS NOW LIVE IN THIS FILE, and the raw one is NOT the source's** (conviction
   banner (1), repaired in §N). `deltaPrimeBil`/`deltaPrimeOp`/`deltaPrimeCLM`/`deltaKCLM` and every
   §7 theorem built on them use RAW `Matrix.trace`, hence `2 × Δ′_source`; the source-normalized
   chain is §N's `deltaPrimeBilNormalized`/`deltaPrimeOpNormalized`/`deltaPrimeCLMNormalized`/
   `deltaKCLMNormalized`, related by the proved `deltaPrimeOpNormalized_eq_half_smul`. **A consumer
   that wants CMP99b's `Δ_k` must take the `…Normalized` declarations.** The raw ones are retained
   because their names are already referenced and because they are the literal transcription against
   Mathlib's trace; they are not wrong statements, they are statements about a rescaled object.
8. **THE MEASURED S82-FORCED SET** (conviction banner (2)). Forced = a garbage bilinear form
   substituted for `Δ′`'s re-derives the same conclusion verbatim. This was RUN, not argued:
   `compute/deltaprime_normalization/S82_forced_probe.lean` compiles ten garbage analogues, EXIT 0,
   all `#print axioms`-clean. The forced declarations in this module are therefore:
   `deltaPrimeBil_symm`, `deltaPrimeBilL2_symm`, `bondAdjoint_deltaPrimeOp`,
   `inner_deltaPrimeOp_symm`, `inner_deltaPrimeCLM_symm`, `deltaKCLM_symm`,
   `bondAdjoint_cStarDeltaKC_unconditional` (Sol's seven), their `…Normalized` twins
   `deltaPrimeBilNormalized_symm`, `deltaPrimeBilL2Normalized_symm`,
   `bondAdjoint_deltaPrimeOpNormalized`, `inner_deltaPrimeOpNormalized_symm`,
   `inner_deltaPrimeCLMNormalized_symm`, `deltaKCLMNormalized_symm`,
   `bondAdjoint_deltaKCLMNormalized`, `bondAdjoint_cStarDeltaKC_normalized_unconditional`,
   **and — disclosed rather than discovered later — §N.3's headline
   `deltaPrimeOpNormalized_eq_half_smul`**, whose garbage analogue also compiles. That last one is
   a consequence of how the normalized form is DEFINED; it exhibits the factor but does not justify
   it. The `1/2` is justified by `deltaPrimeBilNormalized_diag` together with `NormalizationAudit`'s
   general lemma, and THAT chain is falsifiable: mutant M2 asserts the normalized witness diagonal
   is `-8` (the pre-repair value) and FAILS with `⊢ False`.
   **The non-forced source evidence in this module is exactly:** §9's value theorems, §N.1's `D*D`
   normalization check (mutant M7 makes its `rfl` fail), §N.6's two ordered trace atoms, §N.7's
   seven coherent-substitution separations, and §N.8's six per-bracket separations. Ten mutants,
   `compute/deltaprime_normalization/mutants/`, all EXIT 1 on a genuine value or definitional-equality
   error, with one positive control at EXIT 0.
9. **`η = 1` throughout.** No object in this file carries CMP99b (3.10)'s `η^d η^{-2}` weight; there
   is no `η` binder in any type here. Closing the general-`η` statement needs a scale-indexed
   carrier, which does not exist in this tree — that is a definitional gap, named, not a claim.
10. **What ONE witness pair does not separate, measured — and closed.** `(discA, discB)` activates
   only the `A′₂`/`A′₃` slots, so by itself it cannot separate a variant that alters only brackets
   among `(1,2),(1,3),(1,4),(2,4),(3,4)`. §N.8 adds the `cField`/`dField` families (activating `A′₁`
   and `A′₄`), computes all six brackets at their own witness pairs, and proves omitting ANY ONE of
   the six changes the form (`bilPlaq_ne_dropPair_12` … `_34`). **What remains genuinely untested by
   §N.7+§N.8:** a variant that changes two or more brackets so their contributions CANCEL at every
   one of the six witness pairs used. No such variant is exhibited and none is ruled out; separating
   that class would need either more witness pairs or an argument that the six values determine the
   form. That is a stated limit of the check, not a claim about `bilPlaq`.
-/

end AdalyFormal.Balaban.DeltaPrimeOperator
