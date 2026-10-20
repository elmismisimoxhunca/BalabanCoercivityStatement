/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BridgeInverseCarrier
import AdalyFormal.Balaban.CoercivityRegular

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.longLine false

/-!
# `BridgeInverseControls.lean` — the two controls, both directions

## must-fire (`U`-dependence)

`bridge_at_curvedRegularU` instantiates the ENTIRE construction — `G₁`, `T = QG₁Q*`,
`S = (QG₁Q*)⁻¹`, and the bridge bound — at `CoercivityRegular.curvedRegularU`, a background whose
holonomy at `curvedPlaq` is `rotElem 10⁻⁷ ≠ 1` (`curvedRegularU_curved`) and which is provably not
a gauge transform of any flat configuration (`curvedRegularU_not_gaugeTransform_of_flat`).

**The control is not cosmetic.** The `U = 1`-only ingredient in the development is
`FullySupplied.qc_comp_suTwoLift` (the last-layer section), which `qCLM_surjective_trivialU`
consumes. `bridge_at_curvedRegularU` does NOT go through it: it goes through §E's `range Q`
corestriction plus `qCLM_ne_zero`, both of which are proved at an arbitrary `U`. If the construction
had secretly depended on `U = 1`, this theorem could not exist.

## must-not-fire (non-vacuity)

* the coarse carrier is nontrivial (`instNontrivialCoarseFnL2` at the full space,
  `nontrivial_range` + `qCLM_ne_zero` at the range carrier) — the degenerate
  `EuclideanSpace ℝ (Fin 0)` witness that satisfied the previous bridge bundle is impossible;
* `sOp ≠ 0` and `tOp ≠ 0` (`sOp_ne_zero`, `tOp_ne_zero`);
* `Q ≠ 0` and `Q* ≠ 0` are theorems, not assumptions (`qCLM_ne_zero`,
  `q_ne_zero_of_qstar_injective`);
* the constant `q` is `‖Q‖`, which is `> 0` for the same reason.

## What is still a HYPOTHESIS, said plainly

`hDP` — the coercivity `γ‖x‖² ≤ ⟨x,Δ_πx⟩ + ⟨x,Px⟩` of the GAUGE-FIXED fine operator on the WHOLE
fine space. That is the one genuine piece of mathematics the source defers, and it is not proved
here or anywhere in this tree. Everything else in the `hG1`/`hTS` pair is now discharged.
-/

namespace AdalyFormal.Balaban.BridgeInverse

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.CoercivityRegular (curvedRegularU)

variable {L : PeriodicLatticeExtent}

/-! ## §6 — the operator-norm constant, and `hQ` -/

theorem qCLM_norm_pos {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    0 < ‖qCLM U ell‖ := by
  rcases (norm_nonneg (qCLM U ell)).lt_or_eq with h | h
  · exact h
  · exfalso
    refine qCLM_ne_zero hell hdvd hwide U (ContinuousLinearMap.ext fun x => ?_)
    have hb := (qCLM U ell).le_opNorm x
    rw [← h, zero_mul] at hb
    have hz : ‖qCLM U ell x‖ = 0 := le_antisymm hb (norm_nonneg _)
    simpa using norm_eq_zero.1 hz

theorem qCLM_le (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (x : BondFnL2 L) : ‖qCLM U ell x‖ ≤ ‖qCLM U ell‖ * ‖x‖ :=
  (qCLM U ell).le_opNorm x

/-! ## §7 — THE BRIDGE AT THE REAL CARRIER, `U = 1` (full coarse space) -/

/-- **The bridge at the campaign's own `Q`, on the full coarse space, at `U = 1`.**
`G₁`, `T` and `S` are constructed; `hadj` is `qCLM_hadj`; surjectivity of `Q` is
`qCLM_surjective_trivialU`. The only surviving hypothesis about the fine operator is `hDP`. -/
theorem bridge_at_lattice_trivialU {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (Delta P : BondFnL2 L →L[ℝ] BondFnL2 L) (a γ : ℝ)
    (hDsym : ∀ u v : BondFnL2 L, (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hγ : 0 < γ) (ha : 0 ≤ a)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))
    (B : CoarseFnL2 L ell) :
    (γ / ‖qCLM (trivialU L) ell‖ ^ 2) * ‖B‖ ^ 2
      ≤ (inner ℝ B
          (sOp Delta P (qCLM (trivialU L) ell) (qstarCLM (trivialU L) ell) a γ
            (qCLM_hadj (trivialU L) ell) hγ ha hDP
            (qstar_injective_of_surjective _ _ (qCLM_hadj (trivialU L) ell)
              (qCLM_surjective_trivialU hell hdvd)) B) : ℝ) - a * ‖B‖ ^ 2 :=
  bridge_constructed Delta P (qCLM (trivialU L) ell) (qstarCLM (trivialU L) ell) a γ
    ‖qCLM (trivialU L) ell‖ (qCLM_hadj (trivialU L) ell) hDsym hPsym hγ
    (qCLM_norm_pos hell hdvd hwide _) ha hDP (qCLM_surjective_trivialU hell hdvd)
    (qCLM_le (trivialU L) ell) B

/-! ## §8 — THE RANGE CARRIER: `hTS` at an ARBITRARY background, no smallness -/

section RangeAtU

variable {ell : ℕ}
  (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)

/-- `Q*` corestricted: `Q_r* = Q* ∘ ι`, because `Q = ι ∘ Q_r`. No second adjoint is built. -/
noncomputable def qRangeStar :
    (LinearMap.range (qCLM U ell : BondFnL2 L →ₗ[ℝ] CoarseFnL2 L ell)) →L[ℝ] BondFnL2 L :=
  (qstarCLM U ell).comp (Submodule.subtypeL _)

theorem qRange_hadj (x : BondFnL2 L)
    (B : (LinearMap.range (qCLM U ell : BondFnL2 L →ₗ[ℝ] CoarseFnL2 L ell))) :
    (inner ℝ (qRangeStar U B) x : ℝ) = (inner ℝ B (qRange (qCLM U ell) x) : ℝ) := by
  show (inner ℝ (qstarCLM U ell (B : CoarseFnL2 L ell)) x : ℝ)
      = (inner ℝ B (qRange (qCLM U ell) x) : ℝ)
  rw [qCLM_hadj U ell x (B : CoarseFnL2 L ell)]
  rfl

theorem qRange_le (x : BondFnL2 L) : ‖qRange (qCLM U ell) x‖ ≤ ‖qCLM U ell‖ * ‖x‖ :=
  qCLM_le U ell x

end RangeAtU

/-! ## §9 — THE MUST-FIRE CONTROL: everything at `curvedRegularU`

`witL5 μ = 5`, so `L μ + 1 = 6`; at `ell = 2` both guards hold (`2 ∣ 6`, `4 ≤ 6`). -/

theorem witL5_dvd_two : ∀ μ : Fin 3, 2 ∣ (witL5 μ + 1) := by
  intro μ
  show (2 : ℕ) ∣ (5 + 1)
  norm_num

theorem witL5_wide_two : ∀ μ : Fin 3, 2 * 2 ≤ (witL5 μ + 1) := by
  intro μ
  show 2 * 2 ≤ (5 + 1)
  norm_num

/-- Non-vacuity of the range carrier at the CURVED background. -/
theorem nontrivial_range_curved :
    Nontrivial (LinearMap.range
      (qCLM curvedRegularU 2 : BondFnL2 witL5 →ₗ[ℝ] CoarseFnL2 witL5 2)) :=
  nontrivial_range (qCLM curvedRegularU 2)
    (qCLM_ne_zero (by norm_num) witL5_dvd_two witL5_wide_two curvedRegularU)

/-- **THE MUST-FIRE CONTROL.** The full construction — `G₁`, `T = QG₁Q*`, `S = (QG₁Q*)⁻¹` and the
bridge bound — at the CURVED regular background `curvedRegularU`, on the nontrivial carrier
`ran Q`. `FullySupplied.qc_comp_suTwoLift` (the `U = 1`-only section) is NOT used. -/
theorem bridge_at_curvedRegularU
    (Delta P : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) (a γ : ℝ)
    (hDsym : ∀ u v : BondFnL2 witL5, (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 witL5, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hγ : 0 < γ) (ha : 0 ≤ a)
    (hDP : ∀ x : BondFnL2 witL5,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))
    (B : (LinearMap.range
      (qCLM curvedRegularU 2 : BondFnL2 witL5 →ₗ[ℝ] CoarseFnL2 witL5 2))) :
    (γ / ‖qCLM curvedRegularU 2‖ ^ 2) * ‖B‖ ^ 2
      ≤ (inner ℝ B
          (sOp Delta P (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) a γ
            (qRange_hadj curvedRegularU) hγ ha hDP
            (qstar_injective_of_surjective _ _ (qRange_hadj curvedRegularU)
              (qRange_surjective (qCLM curvedRegularU 2))) B) : ℝ) - a * ‖B‖ ^ 2 :=
  bridge_constructed Delta P (qRange (qCLM curvedRegularU 2)) (qRangeStar curvedRegularU) a γ
    ‖qCLM curvedRegularU 2‖ (qRange_hadj curvedRegularU) hDsym hPsym hγ
    (qCLM_norm_pos (by norm_num) witL5_dvd_two witL5_wide_two curvedRegularU) ha hDP
    (qRange_surjective (qCLM curvedRegularU 2)) (qRange_le curvedRegularU) B

/-! ## §10 — THE SOURCE CHAIN AT THE REAL `Δ`: (3.10) ⟹ (3.120) ⟹ (3.128) ⟹ (3.156)

§9 leaves `Δ_π` a free parameter (as `RecursiveBridge.fineMapOf` deliberately does). This section
removes that freedom on the `Δ` half: `Δ_π := deltaKCLMNormalized U − Δ′_π`, CMP99b (3.120) at the
source-normalized (3.10) operator. What remains parametric is exactly what the source leaves
parametric: `Δ′_π` (whose bound p.419 defers — *"Later we will write bounds for this form"*) and the
gauge-fixing `P = (RD*)*(RD*)`. -/

/-- **`Δ_π = Δ − Δ′_π`**, CMP99b (3.120), bundled at the source-normalized (3.10) operator. -/
noncomputable def piCLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (DeltaPrimePi : BondFnL2 L →L[ℝ] BondFnL2 L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U - DeltaPrimePi

theorem piCLM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (DeltaPrimePi : BondFnL2 L →L[ℝ] BondFnL2 L) (x : BondFnL2 L) :
    piCLM U DeltaPrimePi x
      = AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U x - DeltaPrimePi x := rfl

theorem piCLM_symm (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (DeltaPrimePi : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hPiSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ)) (u v : BondFnL2 L) :
    (inner ℝ u (piCLM U DeltaPrimePi v) : ℝ) = (inner ℝ (piCLM U DeltaPrimePi u) v : ℝ) := by
  rw [piCLM_apply, piCLM_apply, inner_sub_right, inner_sub_left, hPiSym u v,
    AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized_symm U u v]

/-- **(3.10)'s coercivity, on the WHOLE fine space, transported to the operator.** -/
theorem deltaKCLMNormalized_coercive
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (γ₀ : ℝ)
    (h310 : ∀ A : AdalyFormal.Balaban.AdmissibleSubspace.Bond L → SuTwo,
      γ₀ * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2
        ≤ AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected U A)
    (x : BondFnL2 L) :
    γ₀ * ‖x‖ ^ 2
      ≤ (inner ℝ x (AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U x) : ℝ) :=
  AdalyFormal.Balaban.RecursiveBridge.operator_coercive_of_quadForm_on
    (AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U)
    (AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected U) γ₀
    (fun _ => True)
    (AdalyFormal.Balaban.DeltaPrimeOperator.inner_deltaKCLMNormalized_eq U)
    (fun A _ => h310 A) x trivial

/-- **`hDP` from the source chain**: `(3.10)`-coercivity `γ₀`, a TWO-SIDED bound `δ` on the
indefinite `Δ′_π` (p.419's deferred estimate), and positivity of the gauge-fixing term `P`. -/
theorem hDP_of_source_chain
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (DeltaPrimePi P : BondFnL2 L →L[ℝ] BondFnL2 L) (γ₀ δ : ℝ)
    (h310 : ∀ A : AdalyFormal.Balaban.AdmissibleSubspace.Bond L → SuTwo,
      γ₀ * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2
        ≤ AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected U A)
    (hpi : ∀ x : BondFnL2 L, |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ)) (x : BondFnL2 L) :
    (γ₀ - δ) * ‖x‖ ^ 2
      ≤ (inner ℝ x (piCLM U DeltaPrimePi x) : ℝ) + (inner ℝ x (P x) : ℝ) := by
  rw [piCLM_apply, inner_sub_right]
  have h1 := deltaKCLMNormalized_coercive U γ₀ h310 x
  have h2 : (inner ℝ x (DeltaPrimePi x) : ℝ) ≤ δ * ‖x‖ ^ 2 := le_trans (le_abs_self _) (hpi x)
  have h3 := hPpos x
  nlinarith [h1, h2, h3]

/-- **THE SOURCE CHAIN AT THE CURVED BACKGROUND, WITH `hG1` AND `hTS` CONSTRUCTED.**
`Δ` is `deltaKCLMNormalized curvedRegularU`; `Q` is the campaign's faithful covariant block average
at `curvedRegularU`; `Q*` is its adjoint; `G₁ = (Δ_π+P+Q*aQ)⁻¹` and `S = (QG₁Q*)⁻¹` are built. The
hypotheses that remain are exactly the source's own deferred estimates. -/
theorem bridge_source_chain_at_curvedRegularU
    (DeltaPrimePi P : BondFnL2 witL5 →L[ℝ] BondFnL2 witL5) (a γ₀ δ : ℝ)
    (hPiSym : ∀ u v : BondFnL2 witL5,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 witL5, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hγδ : 0 < γ₀ - δ) (ha : 0 ≤ a)
    (h310 : ∀ A : AdalyFormal.Balaban.AdmissibleSubspace.Bond witL5 → SuTwo,
      γ₀ * ‖(WithLp.toLp 2 A : BondFnL2 witL5)‖ ^ 2
        ≤ AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
            curvedRegularU A)
    (hpi : ∀ x : BondFnL2 witL5, |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hPpos : ∀ x : BondFnL2 witL5, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (B : (LinearMap.range
      (qCLM curvedRegularU 2 : BondFnL2 witL5 →ₗ[ℝ] CoarseFnL2 witL5 2))) :
    ((γ₀ - δ) / ‖qCLM curvedRegularU 2‖ ^ 2) * ‖B‖ ^ 2
      ≤ (inner ℝ B
          (sOp (piCLM curvedRegularU DeltaPrimePi) P (qRange (qCLM curvedRegularU 2))
            (qRangeStar curvedRegularU) a (γ₀ - δ)
            (qRange_hadj curvedRegularU) hγδ ha
            (hDP_of_source_chain curvedRegularU DeltaPrimePi P γ₀ δ h310 hpi hPpos)
            (qstar_injective_of_surjective _ _ (qRange_hadj curvedRegularU)
              (qRange_surjective (qCLM curvedRegularU 2))) B) : ℝ) - a * ‖B‖ ^ 2 :=
  bridge_constructed (piCLM curvedRegularU DeltaPrimePi) P (qRange (qCLM curvedRegularU 2))
    (qRangeStar curvedRegularU) a (γ₀ - δ) ‖qCLM curvedRegularU 2‖
    (qRange_hadj curvedRegularU) (piCLM_symm curvedRegularU DeltaPrimePi hPiSym) hPsym hγδ
    (qCLM_norm_pos (by norm_num) witL5_dvd_two witL5_wide_two curvedRegularU) ha
    (hDP_of_source_chain curvedRegularU DeltaPrimePi P γ₀ δ h310 hpi hPpos)
    (qRange_surjective (qCLM curvedRegularU 2)) (qRange_le curvedRegularU) B

/-! ## §11 — `hG1` in the LITERAL shape `RecursiveBridge.bridge_from_fine_operator` asks for

`RecursiveBridge.fineMapOf` lives on `BondFnL2 L` and takes bare functions; this section hands its
`hG1` slot a proof, so that consumer is discharged without restating anything. Stated at the
CONCRETE coarse carrier: with an abstract coarse type the elaborator cannot synthesize
`InnerProductSpace ℝ (BondFnL2 L)` (the `PiLp` diamond `RecursiveBridge` §9b documents). -/

theorem fineCLM_eq_fineMapOf {ell : ℕ} (Delta P : BondFnL2 L →L[ℝ] BondFnL2 L)
    (Q : BondFnL2 L →L[ℝ] CoarseFnL2 L ell) (Qstar : CoarseFnL2 L ell →L[ℝ] BondFnL2 L)
    (a : ℝ) (x : BondFnL2 L) :
    AdalyFormal.Balaban.RecursiveBridge.fineMapOf (L := L) (K := CoarseFnL2 L ell)
        (fun y => Delta y) (fun y => P y) (fun y => Q y) (fun B => Qstar B) a x
      = fineCLM Delta P Q Qstar a x := by
  rw [AdalyFormal.Balaban.RecursiveBridge.fineMapOf_apply, fineCLM_apply, map_smul]

/-- **`RecursiveBridge`'s `hG1`, DISCHARGED at the lattice carrier.** -/
theorem hG1_fineMapOf {ell : ℕ} (Delta P : BondFnL2 L →L[ℝ] BondFnL2 L)
    (Q : BondFnL2 L →L[ℝ] CoarseFnL2 L ell) (Qstar : CoarseFnL2 L ell →L[ℝ] BondFnL2 L)
    (a γ : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : CoarseFnL2 L ell),
      (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hγ : 0 < γ) (ha : 0 ≤ a)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))
    (x : BondFnL2 L) :
    AdalyFormal.Balaban.RecursiveBridge.fineMapOf (L := L) (K := CoarseFnL2 L ell)
        (fun y => Delta y) (fun y => P y) (fun y => Q y) (fun B => Qstar B) a
        (gOne Delta P Q Qstar a γ hadj hγ ha hDP x) = x := by
  rw [fineCLM_eq_fineMapOf]
  exact gOne_fineCLM_right Delta P Q Qstar a γ hadj hγ ha hDP x

/-! ## §12 — CLOSING A MILLIMETRE `RecursiveBridge` §9f LEFT OPEN

`RecursiveBridge` §9f states the unrestricted-(3.10) refutation as TWO halves —
`h310_unrestricted_forces_zero_norm_at_witnessU` (`‖v‖ = 0`) and `toLp_deltaWitnessConfig_ne_zero`
(`v ≠ 0`) — and records, verbatim, that they were not combined into `False` because *"the last
millimetre — `‖v‖ = 0 → v = 0` — needs `norm_eq_zero`, which resolves the norm through
`NormedAddCommGroup.toNorm` while this statement's norm comes from `PiLp.instNorm`"*.

That step goes through in this module's instance context. The combined statement is proved below,
under the name `RecursiveBridge`'s own prose already cites twice
(`RecursiveBridge.lean:927` and `:1296`) but which existed nowhere in the tree. -/

/-- **The unrestricted (3.10) coercivity hypothesis is UNSATISFIABLE at `witnessU`**, for every
`γ > 0`. This is why hypothesis (1) of `BridgeInverseCore` is stated on `Δ_π + P` and never on
`Δ_π` alone. -/
theorem h310_unrestricted_impossible_at_witnessU (γ : ℝ) (hγ : 0 < γ) :
    ¬ (∀ A : AdalyFormal.Balaban.AdmissibleSubspace.Bond
          AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo,
        γ * ‖(WithLp.toLp 2 A :
              BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)‖ ^ 2
          ≤ AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
              AdalyFormal.Balaban.CovariantOperators.witnessU A) := by
  intro h310
  have hz := AdalyFormal.Balaban.RecursiveBridge.h310_unrestricted_forces_zero_norm_at_witnessU
    γ hγ h310
  exact AdalyFormal.Balaban.RecursiveBridge.toLp_deltaWitnessConfig_ne_zero (norm_eq_zero.1 hz)

/-! ## §10 — axiom audit -/

#print axioms invOfInjective
#print axioms invOfInjective_right
#print axioms invOfInjective_ne_zero
#print axioms exists_coercive_of_posDef
#print axioms fineCLM_coercive
#print axioms fineCLM_symm
#print axioms gOne
#print axioms gOne_fineCLM_right
#print axioms gOne_posDef
#print axioms qstar_injective_of_surjective
#print axioms surjective_of_qstar_injective
#print axioms tOp
#print axioms tOp_posDef
#print axioms sOp
#print axioms tOp_sOp
#print axioms sOp_tOp
#print axioms sOp_posDef
#print axioms sOp_ne_zero
#print axioms tOp_ne_zero
#print axioms bridge_constructed
#print axioms bridge_constructed_with_source
#print axioms injective_id_add_of_norm_lt_one
#print axioms surjective_of_perturbation
#print axioms compression_zero_on_orthogonal
#print axioms qRange_surjective
#print axioms nontrivial_range
#print axioms instNontrivialCoarseFnL2
#print axioms qCLM_hadj
#print axioms qCLM_surjective_trivialU
#print axioms pathSite_eq_base_iff
#print axioms qCLM_ne_zero
#print axioms qCLM_norm_pos
#print axioms bridge_at_lattice_trivialU
#print axioms qRange_hadj
#print axioms nontrivial_range_curved
#print axioms bridge_at_curvedRegularU
#print axioms fineCLM_eq_fineMapOf
#print axioms hG1_fineMapOf
#print axioms piCLM_symm
#print axioms deltaKCLMNormalized_coercive
#print axioms hDP_of_source_chain
#print axioms bridge_source_chain_at_curvedRegularU
#print axioms h310_unrestricted_impossible_at_witnessU

end AdalyFormal.Balaban.BridgeInverse
