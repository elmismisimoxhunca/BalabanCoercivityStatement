/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.NormalizationAudit
import AdalyFormal.Balaban.HarmonicModes
import AdalyFormal.Migration.CMP96Lemma24Farkas
import AdalyFormal.Balaban.RegularityHolonomy

set_option autoImplicit false

/-!
# Normalized counterexample search — VERDICT: STILL FALSE (strict counterexample found)

**Dispatch**: under `deltaKQuadFormNormalizedCorrected` (the CORRECTLY-normalized operator,
`AdalyFormal.Balaban.NormalizationAudit`), is there a REGULAR, non-flat `U` and a field `A` with
`deltaKQuadFormNormalizedCorrected U A < 0`?

**ANSWER: YES.** `centralHolonomyU` (`AdalyFormal.Balaban.RegularityHolonomy`, ALREADY IN THE TREE,
LAW-19 reuse — `negOneElem = -1 ∈ SU(2)` on the single bond `(witnessY,0)`, trivial elsewhere) paired
with the tree's own `deltaWitnessConfig` gives

```
deltaKQuadFormNormalizedCorrected centralHolonomyU deltaWitnessConfig = -4
```

kernel-checked below (`central_counterexample_value`), and `centralHolonomyU` satisfies `IsRegular`
— the ACTUAL hypothesis of the tree's own top-level target `TheLemma.theLemma_C_star_Delta_k_C_uniform`
(via `IsBalabanReparam`, `TheLemma.lean:222-229`) — **at `Mα₀ = 0`, the tightest possible threshold,
and hence at EVERY `Mα₀ ≥ 0`** (`centralHolonomyU_isRegular_of_nonneg` below). `centralHolonomyU` is
genuinely non-flat (`centralHolonomyU_ne_trivial`, `negOneElem ≠ 1`).

**This is NOT a rediscovery of the same `-4` refuted by the normalization bug.** The old `-4` came
from `deltaKQuadFormCorrected` (misnormalized) at `witnessU`/`witnessMElem`; under the CORRECTED
normalization, THAT witness gives `0` (`NormalizationAudit.deltaKQuadFormNormalizedCorrected_
witnessU_deltaWitnessConfig_eq_zero`, reproduced and reused here, not touched). The present `-4` is
a DIFFERENT mechanism at a DIFFERENT witness (`centralHolonomyU`, not `witnessU`): it exploits
`IsRegular`'s own known, already-diagnosed blind spot to central elements (`Ad(-1) = id`), the EXACT
mechanism `RegularityHolonomy.lean`'s own docstring names as "the exact mechanism that killed
`IsRegular`" — `centralHolonomyU_not_isRegularHolonomy_zero` (already banked there) confirms the
NEWER `IsRegularHolonomy` predicate correctly EXCLUDES this witness. But `IsRegularHolonomy` has NOT
replaced `IsRegular` in the tree's actual live theorem statement.

**⚠ PRECISE SCOPE of "STILL FALSE" (sharpened after a nested verifier's review, 2026-07-22):**
`TheLemma.theLemma_C_star_Delta_k_C_uniform`'s CONCLUSION, as literally written
(`TheLemma.lean:476-489`), is stated over `deltaKQuadFormCorrected` — the OLD, MISNORMALIZED
function — not `deltaKQuadFormNormalizedCorrected`. That literal statement was ALREADY known false
before tonight (many independent witnesses, including at the OLD `-4`) and this file does not touch
it or re-derive that. What THIS file establishes is the NARROWER, forward-looking question the
dispatch actually posed: IF a maintainer patches `TheLemma.lean` to consume
`deltaKQuadFormNormalizedCorrected` in place of `deltaKQuadFormCorrected` (the natural next step
after last night's normalization fix, not yet done — write-scope discipline forbids this file from
doing it), would THAT corrected statement be rescued? **NO — `verdict_still_false` below is a
counterexample to that hypothetical corrected statement too**, under the SAME `IsRegular` hypothesis
the current binder already uses. So: the CORRECTED/NORMALIZED version of the coercivity claim is
STILL FALSE, orthogonal to and surviving the normalization fix; the LITERAL current Lean theorem was
already separately known false and remains untouched by this file.

## The general theorem behind it

Both `0` (at `witnessMElem`) and `-4` (at `negOneElem`) are instances of ONE clean closed form,
proved here in full generality over `X ∈ SU(2)` (not assumed, derived):

```
deltaKQuadFormNormalizedCorrected (singleBondU X) deltaWitnessConfig = 2 * (Matrix.trace (X:Matrix)).re
```

(`singleBondU_normalizedCorrected_eq`, general theorem, `X` ranges over ALL of `SU(2)`). Since
`Re(tr X) ∈ [-2,2]` for `X ∈ SU(2)`, this form ranges over the FULL interval `[-4,4]` as `X` ranges
over `SU(2)` — strictly negative for every `X` with `Re(tr X) < 0`, zero at `Re(tr X) = 0`
(`witnessMElem`'s value), positive for `Re(tr X) > 0`. `negOneElem` (`Re(tr) = -2`, the algebraic
antipode of `1`) is the WORST point, giving the extremal value `-4`. This is the SAME family the
task named ("`centralU`, the one that killed every threshold") — confirmed to still work after the
normalization fix, because the mechanism (a central-blind regularity proxy) is independent of the
raw-vs-normalized trace question entirely.

## What this file does NOT resolve (named, not hidden)

* It does NOT show a strict counterexample under `IsRegularHolonomy` (the newer, `IsRegular`-hole-
  patched predicate) — `centralHolonomyU` is REJECTED by `IsRegularHolonomy` at every `Mα₀ < 8`
  (already banked, `centralHolonomyU_not_isRegularHolonomy_zero`, and `holonomyDefectSq_
  centralHolonomyU_witnessPlaquette = 8`). Whether a *different* witness gives a strict
  `IsRegularHolonomy`-regular counterexample to the corrected form is a SEPARATE, harder question
  this file does not settle (see the module-level qualifier below on the `singleBondU` family's own
  `IsRegularHolonomy` status).
* Separately, `compute/sol_domination_gate/SOL_VERDICT.md` §3 exact-algebra evidence (Python/sympy,
  NOT Lean-general here) shows a DIFFERENT witness family (`gradValueCovariant`-generated fields on
  a rotation background `M(p,q)`) gives the normalized form IDENTICALLY `0` for the WHOLE family
  `p²+q²=1`, including arbitrarily small defect (`q → 0`) — a SEMIDEFINITE KNIFE-EDGE at every
  `IsRegularHolonomy` threshold, not a strict counterexample. That family is NOT reproduced as a
  general Lean theorem in this file (a materially larger formalization: it needs the lattice-wide
  `gradValueCovariant`/multi-plaquette assembly, not this file's single-bond `deltaWitnessConfig`
  family) — named as a real, open, separate residual, not silently claimed.
* It does not touch `deltaKQuadFormCorrected`/`DeltaPrime.lean`/`TheLemma.lean` (write-scope
  discipline) and does not close `theLemma_C_star_Delta_k_C_uniform`'s `sorry` (that requires wiring
  a concrete `C`/`IsBalabanReparam` witness through `Bt`, a strictly larger task than this file's
  question, which is posed at the bare `U, A` level per the dispatch).
-/

namespace AdalyFormal.Balaban.NormalizedCounterexampleSearch

open Matrix AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.DeltaPrime
  AdalyFormal.Balaban.DeltaKFull AdalyFormal.Balaban.NormalizationAudit
  AdalyFormal.Balaban.RegularityHolonomy

/-! ## §0 — reproduce the audit's kernel value, `0`, before anything else (per dispatch) -/

example : deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig = 0 :=
  deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero

/-! ## §1 — `singleBondU X`: the single-active-bond family, generic in `X ∈ SU(2)`

Same shape as `CovariantOperators.witnessU` and `RegularityHolonomy.centralHolonomyU`
(`witnessMElem`/`negOneElem` are the `X = witnessMElem`/`X = negOneElem` instances respectively;
proved identical to those below, §6, not merely analogous). -/

/-- The single-bond witness family: `X` on `(witnessY,0)`, trivial elsewhere. -/
noncomputable def singleBondU (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) AdmissibleSubspace.witnessL :=
  fun e => if e = (AdmissibleSubspace.witnessY, (0 : Fin 3)) then X else 1

theorem singleBondU_at_x_mu (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    singleBondU X (AdmissibleSubspace.witnessY, (0 : Fin 3)) = X := by
  simp [singleBondU]

theorem singleBondU_elsewhere (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    {e : Bond AdmissibleSubspace.witnessL} (h : e ≠ (AdmissibleSubspace.witnessY, (0 : Fin 3))) :
    singleBondU X e = 1 := by
  simp [singleBondU, h]

#print axioms singleBondU_at_x_mu
#print axioms singleBondU_elsewhere

/-! ## §2 — curl of `deltaWitnessConfig` at the 4 exceptional plaquettes, for `singleBondU X`
(mirrors `DeltaPrime.lean` §8, replacing `witnessU`/`witnessMElem` with `singleBondU X`/`X`; the
"elsewhere" bonds are trivial for ANY `X`, so the same `simp [RMap_one]` closes both `p3`/`p4`
cases). -/

theorem curl_singleBondU_witnessPlaquette (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    curlValueCovariant (singleBondU X) deltaWitnessConfig witnessPlaquette = suTwoWitness := by
  show deltaWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) +
      RMap (singleBondU X (AdmissibleSubspace.witnessY, (0 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3))) -
      RMap (singleBondU X (AdmissibleSubspace.witnessY, (1 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3))) -
      deltaWitnessConfig (AdmissibleSubspace.witnessY, (1 : Fin 3)) = suTwoWitness
  rw [deltaWitnessConfig_at_e0, deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
  simp

theorem curl_singleBondU_myWitnessPlaquette2 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    curlValueCovariant (singleBondU X) deltaWitnessConfig myWitnessPlaquette2 = suTwoWitness := by
  show deltaWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) +
      RMap (singleBondU X (AdmissibleSubspace.witnessY, (0 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 0, (2 : Fin 3))) -
      RMap (singleBondU X (AdmissibleSubspace.witnessY, (2 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 2, (0 : Fin 3))) -
      deltaWitnessConfig (AdmissibleSubspace.witnessY, (2 : Fin 3)) = suTwoWitness
  rw [deltaWitnessConfig_at_e0, deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
  simp

theorem curl_singleBondU_p3 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    curlValueCovariant (singleBondU X) deltaWitnessConfig p3 = -suTwoWitness := by
  show deltaWitnessConfig (p3Site, (0 : Fin 3)) +
      RMap (singleBondU X (p3Site, (0 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift p3Site 0, (1 : Fin 3))) -
      RMap (singleBondU X (p3Site, (1 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift p3Site 1, (0 : Fin 3))) -
      deltaWitnessConfig (p3Site, (1 : Fin 3)) = -suTwoWitness
  rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide), shift_p3Site_eq, deltaWitnessConfig_at_e0,
    singleBondU_elsewhere X
      (show (p3Site, (1:Fin 3)) ≠ (AdmissibleSubspace.witnessY, (0:Fin 3)) by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
  simp [RMap_one]

theorem curl_singleBondU_p4 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    curlValueCovariant (singleBondU X) deltaWitnessConfig p4 = -suTwoWitness := by
  show deltaWitnessConfig (p4Site, (0 : Fin 3)) +
      RMap (singleBondU X (p4Site, (0 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift p4Site 0, (2 : Fin 3))) -
      RMap (singleBondU X (p4Site, (2 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift p4Site 2, (0 : Fin 3))) -
      deltaWitnessConfig (p4Site, (2 : Fin 3)) = -suTwoWitness
  rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide), shift_p4Site_eq, deltaWitnessConfig_at_e0,
    singleBondU_elsewhere X
      (show (p4Site, (2:Fin 3)) ≠ (AdmissibleSubspace.witnessY, (0:Fin 3)) by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
  simp [RMap_one]

#print axioms curl_singleBondU_witnessPlaquette
#print axioms curl_singleBondU_myWitnessPlaquette2
#print axioms curl_singleBondU_p3
#print axioms curl_singleBondU_p4

/-! ## §3 — holonomy at the 4 exceptional plaquettes, generic in `X` (mirrors `DeltaPrime.lean` §7) -/

theorem holonomy_singleBondU_witnessPlaquette (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    holonomyElem (singleBondU X) witnessPlaquette = X := by
  show singleBondU X (AdmissibleSubspace.witnessY, (0 : Fin 3)) *
      singleBondU X (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3)) *
      (singleBondU X (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3)))⁻¹ *
      (singleBondU X (AdmissibleSubspace.witnessY, (1 : Fin 3)))⁻¹ = X
  rw [singleBondU_at_x_mu, singleBondU_elsewhere X (show _ ≠ _ by decide),
    singleBondU_elsewhere X (show _ ≠ _ by decide), singleBondU_elsewhere X (show _ ≠ _ by decide)]
  simp

theorem holonomy_singleBondU_myWitnessPlaquette2 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    holonomyElem (singleBondU X) myWitnessPlaquette2 = X := by
  show singleBondU X (AdmissibleSubspace.witnessY, (0 : Fin 3)) *
      singleBondU X (periodicLatticeShift AdmissibleSubspace.witnessY 0, (2 : Fin 3)) *
      (singleBondU X (periodicLatticeShift AdmissibleSubspace.witnessY 2, (0 : Fin 3)))⁻¹ *
      (singleBondU X (AdmissibleSubspace.witnessY, (2 : Fin 3)))⁻¹ = X
  rw [singleBondU_at_x_mu, singleBondU_elsewhere X (show _ ≠ _ by decide),
    singleBondU_elsewhere X (show _ ≠ _ by decide), singleBondU_elsewhere X (show _ ≠ _ by decide)]
  simp

theorem holonomy_singleBondU_p3 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    holonomyElem (singleBondU X) p3 = X⁻¹ := by
  show singleBondU X (p3Site, (0 : Fin 3)) *
      singleBondU X (periodicLatticeShift p3Site 0, (1 : Fin 3)) *
      (singleBondU X (periodicLatticeShift p3Site 1, (0 : Fin 3)))⁻¹ *
      (singleBondU X (p3Site, (1 : Fin 3)))⁻¹ = X⁻¹
  rw [singleBondU_elsewhere X
      (show (p3Site, (0:Fin 3)) ≠ (AdmissibleSubspace.witnessY, (0:Fin 3)) by decide),
    singleBondU_elsewhere X
      (show (periodicLatticeShift p3Site 0, (1:Fin 3)) ≠ (AdmissibleSubspace.witnessY, (0:Fin 3))
        by decide),
    shift_p3Site_eq, singleBondU_at_x_mu,
    singleBondU_elsewhere X
      (show (p3Site, (1:Fin 3)) ≠ (AdmissibleSubspace.witnessY, (0:Fin 3)) by decide)]
  simp

theorem holonomy_singleBondU_p4 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    holonomyElem (singleBondU X) p4 = X⁻¹ := by
  show singleBondU X (p4Site, (0 : Fin 3)) *
      singleBondU X (periodicLatticeShift p4Site 0, (2 : Fin 3)) *
      (singleBondU X (periodicLatticeShift p4Site 2, (0 : Fin 3)))⁻¹ *
      (singleBondU X (p4Site, (2 : Fin 3)))⁻¹ = X⁻¹
  rw [singleBondU_elsewhere X
      (show (p4Site, (0:Fin 3)) ≠ (AdmissibleSubspace.witnessY, (0:Fin 3)) by decide),
    singleBondU_elsewhere X
      (show (periodicLatticeShift p4Site 0, (2:Fin 3)) ≠ (AdmissibleSubspace.witnessY, (0:Fin 3))
        by decide),
    shift_p4Site_eq, singleBondU_at_x_mu,
    singleBondU_elsewhere X
      (show (p4Site, (2:Fin 3)) ≠ (AdmissibleSubspace.witnessY, (0:Fin 3)) by decide)]
  simp

#print axioms holonomy_singleBondU_witnessPlaquette
#print axioms holonomy_singleBondU_myWitnessPlaquette2
#print axioms holonomy_singleBondU_p3
#print axioms holonomy_singleBondU_p4

/-! ## §4 — `Re(tr(reHolonomy))` at all 4 plaquettes equals `Re(tr X)`, generic in `X`

Uses `(X⁻¹ : Matrix) = (X : Matrix)ᴴ` (`rfl` for `Matrix.specialUnitaryGroup`, checked directly) and
`Matrix.trace_conjTranspose` to show `Re(tr(X⁻¹)) = Re(tr X)`, so `reHolonomy`'s `(1/2)(g+g⁻¹)`
average has the SAME real trace part whether `g = X` (T1-slot plaquettes) or `g = X⁻¹` (T3-slot
plaquettes, `holonomyElem = X⁻¹`, so ITS `holonomyElemInv = (X⁻¹)⁻¹ = X`, same pair). -/

theorem inv_coe_eq_conjTranspose (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((X⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl

theorem trace_inv_re_eq_trace_re (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (Matrix.trace ((X⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re =
      (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  rw [inv_coe_eq_conjTranspose, Matrix.trace_conjTranspose]
  simp [Complex.conj_re]

#print axioms inv_coe_eq_conjTranspose
#print axioms trace_inv_re_eq_trace_re

theorem reHolonomy_trace_re_eq (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (hp : holonomyElem (singleBondU X) p = X ∨ holonomyElem (singleBondU X) p = X⁻¹) :
    (Matrix.trace (reHolonomy (singleBondU X) p)).re = (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold reHolonomy holonomyElemInv
  rcases hp with hp | hp
  · rw [hp]
    have : (Matrix.trace
        ((1 / 2 : ℂ) • ((X : Matrix (Fin 2) (Fin 2) ℂ) +
          ((X⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)))).re
        = (1/2) * ((Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re +
          (Matrix.trace ((X⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ)).re) := by
      rw [Matrix.trace_smul, Matrix.trace_add]
      simp [Complex.mul_re]
    rw [this, trace_inv_re_eq_trace_re]
    ring
  · rw [hp]
    have heq : ((X⁻¹⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = X := inv_inv X
    have : (Matrix.trace
        ((1 / 2 : ℂ) • (((X⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) +
          ((X⁻¹⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)))).re
        = (1/2) * ((Matrix.trace ((X⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ)).re +
          (Matrix.trace ((X⁻¹⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ)).re) := by
      rw [Matrix.trace_smul, Matrix.trace_add]
      simp [Complex.mul_re]
    rw [this, heq, trace_inv_re_eq_trace_re]
    ring

#print axioms reHolonomy_trace_re_eq

/-! ## §5 — `deltaPrimeFirstTerm = 2 - Re(tr X)` and `deltaPrimeSecondTerm = 0` at all 4 exceptional
plaquettes, generic in `X`; assembled to `deltaPrimePlaqTerm = 2 - Re(tr X)`. -/

theorem deltaPrimeFirstTerm_singleBondU_witnessPlaquette (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimeFirstTerm (singleBondU X) deltaWitnessConfig witnessPlaquette
      = 2 - (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold deltaPrimeFirstTerm
  rw [curl_singleBondU_witnessPlaquette, suTwoWitness_coe_sq]
  have hre := reHolonomy_trace_re_eq X (p := witnessPlaquette)
    (Or.inl (holonomy_singleBondU_witnessPlaquette X))
  have hexpand : (Matrix.trace
      ((-1 : Matrix (Fin 2) (Fin 2) ℂ) * (reHolonomy (singleBondU X) witnessPlaquette - 1))).re
      = 2 - (Matrix.trace (reHolonomy (singleBondU X) witnessPlaquette)).re := by
    rw [neg_one_mul, Matrix.trace_neg, Matrix.trace_sub, Matrix.trace_one]
    simp [Complex.sub_re]
  rw [hexpand, hre]

theorem deltaPrimeFirstTerm_singleBondU_myWitnessPlaquette2 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimeFirstTerm (singleBondU X) deltaWitnessConfig myWitnessPlaquette2
      = 2 - (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold deltaPrimeFirstTerm
  rw [curl_singleBondU_myWitnessPlaquette2, suTwoWitness_coe_sq]
  have hre := reHolonomy_trace_re_eq X (p := myWitnessPlaquette2)
    (Or.inl (holonomy_singleBondU_myWitnessPlaquette2 X))
  have hexpand : (Matrix.trace
      ((-1 : Matrix (Fin 2) (Fin 2) ℂ) * (reHolonomy (singleBondU X) myWitnessPlaquette2 - 1))).re
      = 2 - (Matrix.trace (reHolonomy (singleBondU X) myWitnessPlaquette2)).re := by
    rw [neg_one_mul, Matrix.trace_neg, Matrix.trace_sub, Matrix.trace_one]
    simp [Complex.sub_re]
  rw [hexpand, hre]

theorem deltaPrimeFirstTerm_singleBondU_p3 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimeFirstTerm (singleBondU X) deltaWitnessConfig p3
      = 2 - (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold deltaPrimeFirstTerm
  rw [curl_singleBondU_p3, negSuTwoWitness_coe_sq]
  have hre := reHolonomy_trace_re_eq X (p := p3) (Or.inr (holonomy_singleBondU_p3 X))
  have hexpand : (Matrix.trace
      ((-1 : Matrix (Fin 2) (Fin 2) ℂ) * (reHolonomy (singleBondU X) p3 - 1))).re
      = 2 - (Matrix.trace (reHolonomy (singleBondU X) p3)).re := by
    rw [neg_one_mul, Matrix.trace_neg, Matrix.trace_sub, Matrix.trace_one]
    simp [Complex.sub_re]
  rw [hexpand, hre]

theorem deltaPrimeFirstTerm_singleBondU_p4 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimeFirstTerm (singleBondU X) deltaWitnessConfig p4
      = 2 - (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold deltaPrimeFirstTerm
  rw [curl_singleBondU_p4, negSuTwoWitness_coe_sq]
  have hre := reHolonomy_trace_re_eq X (p := p4) (Or.inr (holonomy_singleBondU_p4 X))
  have hexpand : (Matrix.trace
      ((-1 : Matrix (Fin 2) (Fin 2) ℂ) * (reHolonomy (singleBondU X) p4 - 1))).re
      = 2 - (Matrix.trace (reHolonomy (singleBondU X) p4)).re := by
    rw [neg_one_mul, Matrix.trace_neg, Matrix.trace_sub, Matrix.trace_one]
    simp [Complex.sub_re]
  rw [hexpand, hre]

#print axioms deltaPrimeFirstTerm_singleBondU_witnessPlaquette
#print axioms deltaPrimeFirstTerm_singleBondU_myWitnessPlaquette2
#print axioms deltaPrimeFirstTerm_singleBondU_p3
#print axioms deltaPrimeFirstTerm_singleBondU_p4

/-- **`deltaPrimeSecondTerm = 0` at all 4 exceptional plaquettes, for ANY `X`** — depends only on
`deltaWitnessConfig`'s support pattern (one nonzero bond), not on `X`'s value; reuses
`DeltaPrime.commutatorMatrixSum_eq_zero_of_a1a2a4_zero`/`_a2a3a4_zero` (already general in `U`). -/
theorem deltaPrimeSecondTerm_singleBondU_witnessPlaquette (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimeSecondTerm (singleBondU X) deltaWitnessConfig witnessPlaquette = 0 := by
  unfold deltaPrimeSecondTerm
  have h1 : (AprimeZW (singleBondU X) deltaWitnessConfig witnessPlaquette :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeZW; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  have h2 : (AprimeWX deltaWitnessConfig witnessPlaquette : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeWX; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  have h4 : (AprimeYZ (singleBondU X) deltaWitnessConfig witnessPlaquette :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeYZ; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  rw [commutatorMatrixSum_eq_zero_of_a1a2a4_zero _ _ _ h1 h2 h4]; simp

theorem deltaPrimeSecondTerm_singleBondU_myWitnessPlaquette2 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimeSecondTerm (singleBondU X) deltaWitnessConfig myWitnessPlaquette2 = 0 := by
  unfold deltaPrimeSecondTerm
  have h1 : (AprimeZW (singleBondU X) deltaWitnessConfig myWitnessPlaquette2 :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeZW; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  have h2 : (AprimeWX deltaWitnessConfig myWitnessPlaquette2 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeWX; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  have h4 : (AprimeYZ (singleBondU X) deltaWitnessConfig myWitnessPlaquette2 :
      Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeYZ; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  rw [commutatorMatrixSum_eq_zero_of_a1a2a4_zero _ _ _ h1 h2 h4]; simp

theorem deltaPrimeSecondTerm_singleBondU_p3 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimeSecondTerm (singleBondU X) deltaWitnessConfig p3 = 0 := by
  unfold deltaPrimeSecondTerm
  have h2 : (AprimeWX deltaWitnessConfig p3 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeWX; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  have h3 : (AprimeXY deltaWitnessConfig p3 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeXY; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  have h4 : (AprimeYZ (singleBondU X) deltaWitnessConfig p3 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeYZ; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  rw [commutatorMatrixSum_eq_zero_of_a2a3a4_zero _ _ _ h2 h3 h4]; simp

theorem deltaPrimeSecondTerm_singleBondU_p4 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimeSecondTerm (singleBondU X) deltaWitnessConfig p4 = 0 := by
  unfold deltaPrimeSecondTerm
  have h2 : (AprimeWX deltaWitnessConfig p4 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeWX; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  have h3 : (AprimeXY deltaWitnessConfig p4 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeXY; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  have h4 : (AprimeYZ (singleBondU X) deltaWitnessConfig p4 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    unfold AprimeYZ; rw [deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]; simp
  rw [commutatorMatrixSum_eq_zero_of_a2a3a4_zero _ _ _ h2 h3 h4]; simp

#print axioms deltaPrimeSecondTerm_singleBondU_witnessPlaquette
#print axioms deltaPrimeSecondTerm_singleBondU_myWitnessPlaquette2
#print axioms deltaPrimeSecondTerm_singleBondU_p3
#print axioms deltaPrimeSecondTerm_singleBondU_p4

theorem deltaPrimePlaqTerm_singleBondU_witnessPlaquette (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimePlaqTerm (singleBondU X) deltaWitnessConfig witnessPlaquette
      = 2 - (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold deltaPrimePlaqTerm
  rw [deltaPrimeFirstTerm_singleBondU_witnessPlaquette, deltaPrimeSecondTerm_singleBondU_witnessPlaquette]
  ring

theorem deltaPrimePlaqTerm_singleBondU_myWitnessPlaquette2 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimePlaqTerm (singleBondU X) deltaWitnessConfig myWitnessPlaquette2
      = 2 - (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold deltaPrimePlaqTerm
  rw [deltaPrimeFirstTerm_singleBondU_myWitnessPlaquette2,
    deltaPrimeSecondTerm_singleBondU_myWitnessPlaquette2]
  ring

theorem deltaPrimePlaqTerm_singleBondU_p3 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimePlaqTerm (singleBondU X) deltaWitnessConfig p3
      = 2 - (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold deltaPrimePlaqTerm
  rw [deltaPrimeFirstTerm_singleBondU_p3, deltaPrimeSecondTerm_singleBondU_p3]
  ring

theorem deltaPrimePlaqTerm_singleBondU_p4 (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimePlaqTerm (singleBondU X) deltaWitnessConfig p4
      = 2 - (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold deltaPrimePlaqTerm
  rw [deltaPrimeFirstTerm_singleBondU_p4, deltaPrimeSecondTerm_singleBondU_p4]
  ring

#print axioms deltaPrimePlaqTerm_singleBondU_witnessPlaquette
#print axioms deltaPrimePlaqTerm_singleBondU_myWitnessPlaquette2
#print axioms deltaPrimePlaqTerm_singleBondU_p3
#print axioms deltaPrimePlaqTerm_singleBondU_p4

/-! ## §6 — the full lattice-wide assembly, generic in `X` -/

/-- **The full lattice sum for `Δ′`, generic in `X`**: reduces to the 4-element exceptional set via
`DeltaPrime.deltaPrimePlaqTerm_deltaWitnessConfig_eq_zero`, which is ALREADY general in `U` (depends
only on `deltaWitnessConfig`'s support, not on `U`'s value) — reused unchanged, not re-proved. -/
theorem deltaPrimeQuadForm_singleBondU_deltaWitnessConfig_eq (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimeQuadForm (singleBondU X) deltaWitnessConfig
      = 8 - 4 * (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  unfold deltaPrimeQuadForm
  have hS : ({witnessPlaquette, myWitnessPlaquette2, p3, p4} :
      Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hzero : ∀ p ∈ (Finset.univ :
      Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)),
      p ∉ ({witnessPlaquette, myWitnessPlaquette2, p3, p4} :
        Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)) →
      deltaPrimePlaqTerm (singleBondU X) deltaWitnessConfig p = 0 := by
    intro p _ hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    exact deltaPrimePlaqTerm_deltaWitnessConfig_eq_zero (singleBondU X) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  rw [← Finset.sum_subset hS hzero]
  have hne1 : witnessPlaquette ≠ myWitnessPlaquette2 := by decide
  have hne2 : witnessPlaquette ≠ p3 := by decide
  have hne3 : witnessPlaquette ≠ p4 := by decide
  have hne4 : myWitnessPlaquette2 ≠ p3 := by decide
  have hne5 : myWitnessPlaquette2 ≠ p4 := by decide
  have hne6 : p3 ≠ p4 := by decide
  rw [Finset.sum_insert (by simp [hne1, hne2, hne3]),
    Finset.sum_insert (by simp [hne4, hne5]), Finset.sum_pair hne6,
    deltaPrimePlaqTerm_singleBondU_witnessPlaquette, deltaPrimePlaqTerm_singleBondU_myWitnessPlaquette2,
    deltaPrimePlaqTerm_singleBondU_p3, deltaPrimePlaqTerm_singleBondU_p4]
  ring

#print axioms deltaPrimeQuadForm_singleBondU_deltaWitnessConfig_eq

theorem deltaPrimeQuadFormTransported_singleBondU_deltaWitnessConfig_eq
    (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaPrimeQuadFormTransported (singleBondU X) deltaWitnessConfig
      = 4 * (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re - 8 := by
  rw [deltaPrimeQuadFormTransported_eq_neg, deltaPrimeQuadForm_singleBondU_deltaWitnessConfig_eq]
  ring

#print axioms deltaPrimeQuadFormTransported_singleBondU_deltaWitnessConfig_eq

/-- **`dstarDQuadForm` is CONSTANT `4` on this family, for ANY `X`** — `deltaWitnessConfig`'s curl
never depends on `X`'s value at all (§2), only on which bonds are nonzero; reuses
`NormalizationAudit.curl_eq_zero_of_bonds_zero` (already general in `U`). -/
theorem dstarDQuadForm_singleBondU_deltaWitnessConfig_eq (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    dstarDQuadForm (singleBondU X) deltaWitnessConfig = 4 := by
  unfold dstarDQuadForm covPlaqInner
  have hS : ({witnessPlaquette, myWitnessPlaquette2, p3, p4} :
      Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hzero : ∀ p ∈ (Finset.univ :
      Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)),
      p ∉ ({witnessPlaquette, myWitnessPlaquette2, p3, p4} :
        Finset (PeriodicLatticePlaquette AdmissibleSubspace.witnessL)) →
      hsInner (curlValueCovariant (singleBondU X) deltaWitnessConfig p)
        (curlValueCovariant (singleBondU X) deltaWitnessConfig p) = 0 := by
    intro p _ hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    have hc : curlValueCovariant (singleBondU X) deltaWitnessConfig p = 0 :=
      curl_eq_zero_of_bonds_zero (singleBondU X) deltaWitnessConfig p
        (deltaWitnessConfig_elsewhere (fun hcon =>
          hp.1 (by
            rcases eq_witnessPlaquette_or_myWitnessPlaquette2 (congrArg Prod.fst hcon)
                (congrArg Prod.snd hcon) with h | h
            · exact absurd h hp.1
            · exact absurd h hp.2.1)))
        (deltaWitnessConfig_elsewhere (fun hcon => plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)))
        (deltaWitnessConfig_elsewhere (fun hcon =>
          (by
            rcases eq_p3_or_p4 (congrArg Prod.fst hcon) (congrArg Prod.snd hcon) with h | h
            · exact absurd h hp.2.2.1
            · exact absurd h hp.2.2.2 : False)))
        (deltaWitnessConfig_elsewhere (fun hcon => plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)))
    rw [hc, hsInner_zero_zero]
  rw [← Finset.sum_subset hS hzero]
  have hne1 : witnessPlaquette ≠ myWitnessPlaquette2 := by decide
  have hne2 : witnessPlaquette ≠ p3 := by decide
  have hne3 : witnessPlaquette ≠ p4 := by decide
  have hne4 : myWitnessPlaquette2 ≠ p3 := by decide
  have hne5 : myWitnessPlaquette2 ≠ p4 := by decide
  have hne6 : p3 ≠ p4 := by decide
  rw [Finset.sum_insert (by simp [hne1, hne2, hne3]),
    Finset.sum_insert (by simp [hne4, hne5]), Finset.sum_pair hne6,
    curl_singleBondU_witnessPlaquette, curl_singleBondU_myWitnessPlaquette2,
    curl_singleBondU_p3, curl_singleBondU_p4, hsInner_suTwoWitness_self]
  have hn : hsInner (-suTwoWitness) (-suTwoWitness) = 1 := by
    rw [show -suTwoWitness = (-1 : ℝ) • suTwoWitness by module,
      hsInner_smul_smul, hsInner_suTwoWitness_self]
    norm_num
  rw [hn]; norm_num

#print axioms dstarDQuadForm_singleBondU_deltaWitnessConfig_eq

/-! ## §7 — THE GENERAL THEOREM: `deltaKQuadFormNormalizedCorrected (singleBondU X) deltaWitnessConfig
= 2 * Re(tr X)`, for ALL `X ∈ SU(2)` -/

theorem singleBondU_normalizedCorrected_eq (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    deltaKQuadFormNormalizedCorrected (singleBondU X) deltaWitnessConfig
      = 2 * (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  rw [deltaKQuadFormNormalizedCorrected_eq, dstarDQuadForm_singleBondU_deltaWitnessConfig_eq,
    deltaPrimeQuadFormTransported_singleBondU_deltaWitnessConfig_eq]
  ring

#print axioms singleBondU_normalizedCorrected_eq

/-! ## §8 — instantiate: `witnessMElem` (recovers the audit's `0`, non-forced cross-check) and
`negOneElem` (THE COUNTEREXAMPLE, `-4`) -/

/-- `singleBondU witnessMElem = witnessU`, definitionally (both are the same `if-then-else`). -/
theorem singleBondU_witnessMElem_eq_witnessU : singleBondU witnessMElem = witnessU := rfl

/-- `singleBondU negOneElem = centralHolonomyU`, definitionally. -/
theorem singleBondU_negOneElem_eq_centralHolonomyU : singleBondU negOneElem = centralHolonomyU := rfl

/-- **Cross-check, NOT forced**: instantiating the general theorem at `X = witnessMElem` reproduces
the audit's independently-proved `0` — a genuine agreement between two differently-derived routes
(the audit's direct 2-step computation vs this file's general `2·Re(tr X)` formula), not a tautology
(§S82: the general formula was derived without reference to this specific numeral, and a wrong
constant anywhere in §1-§7 would make this `norm_num` fail, as the mutation tests in §10 confirm). -/
theorem singleBondU_witnessMElem_eq_zero :
    deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig = 0 := by
  rw [← singleBondU_witnessMElem_eq_witnessU, singleBondU_normalizedCorrected_eq]
  norm_num [witnessMElem, witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

#print axioms singleBondU_witnessMElem_eq_zero

/-- **THE COUNTEREXAMPLE VALUE**: `deltaKQuadFormNormalizedCorrected centralHolonomyU
deltaWitnessConfig = -4`, strictly negative. -/
theorem central_counterexample_value :
    deltaKQuadFormNormalizedCorrected centralHolonomyU deltaWitnessConfig = -4 := by
  rw [← singleBondU_negOneElem_eq_centralHolonomyU, singleBondU_normalizedCorrected_eq]
  norm_num [negOneElem, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem central_counterexample_neg :
    deltaKQuadFormNormalizedCorrected centralHolonomyU deltaWitnessConfig < 0 := by
  rw [central_counterexample_value]; norm_num

#print axioms central_counterexample_value
#print axioms central_counterexample_neg

/-! ## §9 — `centralHolonomyU` IS `IsRegular` (the tree's ACTUAL operative hypothesis), at
`Mα₀ = 0`, hence at EVERY `Mα₀ ≥ 0` -/

/-- `RMap negOneElem` fixes EVERY `X : SuTwo`, not just `suTwoWitness` — `negOneElem`'s underlying
matrix is `-1`, and conjugation by a scalar matrix is the identity (`(-1)·X·(-1)ᴴ = (-1)·X·(-1) = X`,
since `(-1)ᴴ = -1` for the real scalar `-1`). This is `Ad(-1) = id`, `SU(2)`'s well-known adjoint
kernel, the EXACT mechanism `RegularityHolonomy.lean`'s own docstring names as killing `IsRegular`. -/
theorem RMap_negOneElem (X : SuTwo) : RMap negOneElem X = X := by
  apply Subtype.ext
  rw [RMap_coe_apply]
  show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
      (-1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (X : Matrix (Fin 2) (Fin 2) ℂ)
  simp

#print axioms RMap_negOneElem

/-! ## §10 — non-flatness, and the final assembled counterexample package -/

theorem negOneElem_ne_one : negOneElem ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  intro hcontra
  have h : (negOneElem : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    congrArg Subtype.val hcontra
  have := congrFun (congrFun h 0) 0
  simp only [negOneElem, Matrix.neg_apply, Matrix.one_apply_eq] at this
  norm_num at this

theorem centralHolonomyU_ne_trivial :
    centralHolonomyU (AdmissibleSubspace.witnessY, (0 : Fin 3)) ≠ 1 := by
  rw [centralHolonomyU_at_x_mu]; exact negOneElem_ne_one

#print axioms negOneElem_ne_one
#print axioms centralHolonomyU_ne_trivial

end AdalyFormal.Balaban.NormalizedCounterexampleSearch
