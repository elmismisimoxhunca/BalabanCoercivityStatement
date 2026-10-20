/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.LemmaAssembly
import AdalyFormal.Balaban.NormalizationAudit

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `LemmaAssemblyNormalized.lean` — the assembled coercivity for the CONSISTENTLY NORMALIZED `Δ_k`

`LemmaAssembly.lean` proves `assemblyGamma * bondEnergy A ≤ deltaKQuadFormCorrected U A`.
`NormalizationAudit.lean` proves (kernel-checked, general in `U`, `A`) that
`deltaKQuadFormCorrected` sums a `tr = ½Tr`-normalized summand (`dstarDQuadForm`, built from
`SuTwoInner.hsInner`) with an UNNORMALIZED one (`deltaPrimeQuadFormTransported`, built from raw
`Matrix.trace`), and that the source-consistent object is
`deltaKQuadFormNormalizedCorrected U A
  = dstarDQuadForm U A + (1/2)·deltaPrimeQuadFormTransported U A`.

This module lands the assembled coercivity for the NORMALIZED object, and sharpens the incidence
count that the `Δ′` absorption runs through.

## What is new here (facts; the grades are the gates')

1. **`sum_plaqBondSq_eq` — the plaquette→bond incidence is an EXACT IDENTITY**, not a bound:
   `∑_p plaqBondSq A p = 4 · bondEnergy A` for every `A` and every extent `L`.
   `LemmaAssembly.sum_plaqBondSq_le` used `≤ 8`. The identity is proved from the EXACT per-role
   fibre cardinalities, which are DIRECTION-DEPENDENT and are recorded individually
   (`dir_proj1_fiber_cards`, `dir_proj2_fiber_cards`): the base-`μ`/neighbour-`ν` role has fibre
   sizes `(2,1,0)` over `ρ = (0,1,2)` and the base-`ν`/neighbour-`μ` role has `(0,1,2)`. A uniform
   "`d−1 = 2` per role" argument is FALSE per role; only the SUM of the two roles is constantly `2`
   (`dir_fiber_card_sum`), and that is what carries the identity.
2. **`abs_deltaPrimeQuadForm_le_sharp` — `576 → 288`** in the raw `Δ′` absorption bound, obtained
   by feeding (1) into `LemmaAssembly`'s own per-plaquette estimates (which are reused, not
   rebuilt — LAW-19).
3. **`abs_deltaPrimeQuadFormNormalized_le_halved` — `16α₀ → 8α₀`, `576 → 288`** by rewriting
   through `NormalizationAudit.deltaPrimeQuadFormNormalized_eq_half` (the "same proof gives half"
   route, done as a rewrite, not a re-derivation), and
   **`abs_deltaPrimeQuadFormNormalized_le` — `8α₀` and `144α₀`** combining (2) and (3).
4. **`deltaKNormalized_gaugeRegular_coercive`** — `normGamma · bondEnergy A ≤
   deltaKQuadFormNormalizedCorrected U A` with `normGamma = 1/2000` and threshold
   `normAlpha = 1/2000000 = 5·10⁻⁷`, versus `LemmaAssembly`'s `assemblyGamma = 1/2000`,
   `assemblyAlpha = 10⁻⁷`. ~~**Same coercivity constant, five times the threshold.**~~
   §5 proves in exact rationals that the raw route's constants CANNOT reach `1/2000` at `5·10⁻⁷`
   (`raw_constants_fail_at_normAlpha`), so the improvement is a theorem, not a claim.

   **⚠ QUALIFIED 2026-07-28 by a blind third-family gate, corrected in place (S75).** The struck
   phrase overstates. **`5×` is the ratio of two CHOSEN LITERALS, not the gain the algebra supports.**
   The two literals sit at unequal slack under their own exact ceilings — the raw literal `10⁻⁷` has
   ~26.7% slack, the normalized literal `5·10⁻⁷` only ~7.9%. **The ratio of the true exact ceilings is
   `≈ 3.98×`**, which is the real, algebraically-supported figure (and factors cleanly as `2 × 2`:
   one from the normalization, one from the exact incidence identity). Picking a rounder literal on
   one side than the other manufactured the extra 0.02 → 5. That is the S80 pattern — a round number
   produced by free-parameter choice is not evidence of what the algebra delivers.
   **Honest form: `≈3.98×` the achievable ceiling; `5×` only as literally chosen.**
   Nothing here touches the `1/2000` coercivity theorem itself, which the same gate confirmed
   source-faithful and arithmetically correct on independent derivations.
5. Existential-threshold and scale-uniform forms with the same quantifier structure as
   `LemmaAssembly.deltaK_lemma_existential_threshold` / `deltaK_uniform_over_family`.
6. §5 — controls in both directions, and the degeneracy checks (`Real.sqrt` of a negative,
   `ℕ`-truncation) discharged explicitly.

## What this module does NOT claim

* It does not decide which of `deltaKQuadFormCorrected` and `deltaKQuadFormNormalizedCorrected`
  downstream files should consume; it does not edit any other file. `NormalizationAudit`'s Q2
  (CMP99b p.392: one normalized `tr`, both terms) is the source reading this consumes.
* Everything `LemmaAssembly` §8 disclaims is inherited verbatim: this is CMP99b p.392 **(3.10)**'s
  non-recursive form, `ell` is fixed at `2` by the imported base, and `GaugeRegular` is (3.35)'s
  first clause at the global-cube specialization.
* The threshold gain is a gain in THIS route's constants. Nothing about Bałaban's own constants
  follows from it.

`#print axioms` on every declaration below.
-/

namespace AdalyFormal.Balaban.LemmaAssemblyNormalized

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftEquiv)
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AlphaAnalyticity
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaKFull (deltaKQuadFormCorrected)
open AdalyFormal.Balaban.NormalizationAudit
open AdalyFormal.Balaban.LemmaAssembly (plaqBondSq plaqBondSq_nonneg abs_deltaPrimeFirstTerm_le
  abs_deltaPrimeSecondTerm_le dstarDQuadForm_eq_sum_norm_sq gaugeRegular_mono
  assemblyAlpha assemblyGamma
  assemblyAlpha_pos assemblyGamma_pos frobSq_holonomy_of_gaugeRegular sum_plaqBondSq_le)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5 witA bondEnergy_witA_pos
  regularU_domain_nonvacuous)
open AdalyFormal.Balaban.RegularUDomainWitnessGeneralU (siteZero)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE PLAQUETTE→BOND INCIDENCE IS EXACT: `∑_p plaqBondSq A p = 4·bondEnergy A`

`plaqBondSq A p` (`LemmaAssembly` §2c.2) is the sum of the four squared bond norms on the boundary
of `p = (x, (μ,ν))`, `μ < ν`:

* `‖A(x,μ)‖²`      — role "base-1", direction `μ = dir.1.1`
* `‖A(x,ν)‖²`      — role "base-2", direction `ν = dir.1.2`
* `‖A(x+μ,ν)‖²`    — role "neighbour-1", direction `ν = dir.1.2`
* `‖A(x+ν,μ)‖²`    — role "neighbour-2", direction `μ = dir.1.1`

**The direction-dependence warning, discharged rather than avoided.** Summing over the whole
plaquette set, the site sum in each role is a full slice sum (for the two neighbour roles after
reindexing by the shift `Equiv`), so each role contributes `∑_{dir} slice(role-direction of dir)`.
For `d = 3` the direction pairs are exactly `(0,1), (0,2), (1,2)`, so

* the fibre of `dir ↦ dir.1.1` over `ρ = 0,1,2` has sizes `2, 1, 0` — NOT constantly `2`;
* the fibre of `dir ↦ dir.1.2` over `ρ = 0,1,2` has sizes `0, 1, 2` — NOT constantly `2`;
* their SUM is constantly `2` (`dir_fiber_card_sum`, `decide`d).

Roles base-1 and neighbour-2 both use `dir.1.1`; roles base-2 and neighbour-1 both use `dir.1.2`.
So the total multiplicity of direction `ρ` is `2·(#fibre₁ ρ) + ... ` — no: it is
`(#fibre₁ ρ + #fibre₂ ρ)` counted TWICE, `= 2·2 = 4`, uniformly in `ρ`. That is the identity.
`LemmaAssembly.sum_plaqBondSq_le`'s `8` is exactly this `4` with each role bounded by its
per-role maximum `2` — correct, but a factor `2` loose. -/

/-- The direction-`ρ` slice of the bond energy. -/
noncomputable def dirSlice (A : Bond L → SuTwo) (ρ : Fin 3) : ℝ :=
  ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2

theorem dirSlice_nonneg (A : Bond L → SuTwo) (ρ : Fin 3) : 0 ≤ dirSlice A ρ :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem bondEnergy_eq_sum_dirSlice (A : Bond L → SuTwo) :
    bondEnergy A = ∑ ρ : Fin 3, dirSlice A ρ := by
  unfold bondEnergy dirSlice
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- **The `dir.1.1` fibre sizes, EXACT and NOT constant.** `#{(μ,ν) : μ<ν, μ = ρ}` is `2, 1, 0`
for `ρ = 0, 1, 2`. Stated as three literal equalities, so no `ℕ`-subtraction (`2 - ρ`) appears
anywhere and no truncation can hide. -/
theorem dir_proj1_fiber_cards :
    (Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.1 = 0)).card = 2
      ∧ (Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.1 = 1)).card = 1
      ∧ (Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.1 = 2)).card = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The `dir.1.2` fibre sizes, EXACT and NOT constant.** `#{(μ,ν) : μ<ν, ν = ρ}` is `0, 1, 2`
for `ρ = 0, 1, 2` — the MIRROR IMAGE of the previous, which is precisely why a uniform per-role
count is wrong and the per-`ρ` SUM is right. -/
theorem dir_proj2_fiber_cards :
    (Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.2 = 0)).card = 0
      ∧ (Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.2 = 1)).card = 1
      ∧ (Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.2 = 2)).card = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The only uniform statement available**: the two per-role fibre sizes SUM to `2` at every
direction. This — and not any per-role count — is what makes the incidence identity hold. -/
theorem dir_fiber_card_sum (j : Fin 3) :
    (Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.1 = j)).card
      + (Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.2 = j)).card = 2 := by
  revert j; decide

#print axioms dirSlice_nonneg
#print axioms bondEnergy_eq_sum_dirSlice
#print axioms dir_proj1_fiber_cards
#print axioms dir_proj2_fiber_cards
#print axioms dir_fiber_card_sum

/-- Fibrewise evaluation of a direction sum along `dir ↦ dir.1.1`, as an EQUALITY. -/
theorem sum_dir_proj1_eq (w : Fin 3 → ℝ) :
    ∑ dir : PeriodicPlaquetteDirections, w dir.1.1
      = ∑ j : Fin 3,
          ((Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.1 = j)).card : ℝ)
            * w j := by
  rw [← Finset.sum_fiberwise' Finset.univ (fun dir : PeriodicPlaquetteDirections => dir.1.1) w]
  exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_const, nsmul_eq_mul])

/-- Fibrewise evaluation of a direction sum along `dir ↦ dir.1.2`, as an EQUALITY. -/
theorem sum_dir_proj2_eq (w : Fin 3 → ℝ) :
    ∑ dir : PeriodicPlaquetteDirections, w dir.1.2
      = ∑ j : Fin 3,
          ((Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.2 = j)).card : ℝ)
            * w j := by
  rw [← Finset.sum_fiberwise' Finset.univ (fun dir : PeriodicPlaquetteDirections => dir.1.2) w]
  exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_const, nsmul_eq_mul])

/-- **THE DIRECTION-PAIR IDENTITY.** `∑_dir w(μ(dir)) + ∑_dir w(ν(dir)) = 2·∑_ρ w ρ`, for EVERY
`w : Fin 3 → ℝ` — no sign hypothesis, which is the mark of an identity rather than a bound. -/
theorem sum_dir_proj_pair_eq (w : Fin 3 → ℝ) :
    (∑ dir : PeriodicPlaquetteDirections, w dir.1.1)
        + (∑ dir : PeriodicPlaquetteDirections, w dir.1.2)
      = 2 * ∑ j : Fin 3, w j := by
  rw [sum_dir_proj1_eq, sum_dir_proj2_eq, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h : ((Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.1 = j)).card : ℝ)
      + ((Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.2 = j)).card : ℝ)
      = 2 := by exact_mod_cast dir_fiber_card_sum j
  rw [← add_mul, h]

#print axioms sum_dir_proj1_eq
#print axioms sum_dir_proj2_eq
#print axioms sum_dir_proj_pair_eq

/-! ### §1b — the four role sums, as equalities

`LemmaAssembly.sum_base1_sq_le` / `sum_base2_sq_le` and `RegularUPerturbation.sum_nbr1_sq_le` /
`sum_nbr2_sq_le` each prove exactly the reindexing below and then immediately weaken it to `≤ 2·E`.
LAW-19 disclosure: the four `key` steps here are a DELIBERATE re-derivation of steps that exist
inside those four proofs but are not exported as equalities. They are three lines each; the
alternative would be to edit four declarations in two files outside this lane's write scope. -/

theorem sum_base1_sq_eq (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖A (p.1, p.2.1.1)‖ ^ 2
      = ∑ dir : PeriodicPlaquetteDirections, dirSlice A dir.1.1 := by
  unfold dirSlice
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem sum_base2_sq_eq (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖A (p.1, p.2.1.2)‖ ^ 2
      = ∑ dir : PeriodicPlaquetteDirections, dirSlice A dir.1.2 := by
  unfold dirSlice
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem sum_nbr1_sq_eq (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
      = ∑ dir : PeriodicPlaquetteDirections, dirSlice A dir.1.2 := by
  unfold dirSlice
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun dir _ =>
    Equiv.sum_comp (periodicLatticeShiftEquiv dir.1.1) (fun y => ‖A (y, dir.1.2)‖ ^ 2))

theorem sum_nbr2_sq_eq (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2
      = ∑ dir : PeriodicPlaquetteDirections, dirSlice A dir.1.1 := by
  unfold dirSlice
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun dir _ =>
    Equiv.sum_comp (periodicLatticeShiftEquiv dir.1.2) (fun y => ‖A (y, dir.1.1)‖ ^ 2))

/-- **THE EXACT INCIDENCE IDENTITY.** `∑_p plaqBondSq A p = 4·bondEnergy A`, for every `A` and
every extent `L` — an EQUALITY, replacing `LemmaAssembly.sum_plaqBondSq_le`'s `≤ 8·bondEnergy A`.
Holds with no positivity hypothesis on anything and at every extent, including the degenerate
`L ≡ 0` (single-site) case, where both sides are `4·∑_ρ ‖A(x₀,ρ)‖²`. -/
theorem sum_plaqBondSq_eq (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, plaqBondSq A p = 4 * bondEnergy A := by
  have hsplit : ∑ p : PeriodicLatticePlaquette L, plaqBondSq A p
      = (∑ p : PeriodicLatticePlaquette L, ‖A (p.1, p.2.1.1)‖ ^ 2)
        + (∑ p : PeriodicLatticePlaquette L, ‖A (p.1, p.2.1.2)‖ ^ 2)
        + (∑ p : PeriodicLatticePlaquette L,
            ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2)
        + (∑ p : PeriodicLatticePlaquette L,
            ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
    unfold plaqBondSq
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit, sum_base1_sq_eq, sum_base2_sq_eq, sum_nbr1_sq_eq, sum_nbr2_sq_eq,
    bondEnergy_eq_sum_dirSlice]
  have h := sum_dir_proj_pair_eq (dirSlice A)
  linarith

/-- **The identity IMPLIES the old bound** — so nothing downstream that consumed `≤ 8` is broken by
adopting it, and the sharpening is a strict refinement rather than a different statement. -/
theorem sum_plaqBondSq_eq_implies_le (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, plaqBondSq A p ≤ 8 * bondEnergy A := by
  rw [sum_plaqBondSq_eq]
  linarith [bondEnergy_nonneg A]

#print axioms sum_base1_sq_eq
#print axioms sum_base2_sq_eq
#print axioms sum_nbr1_sq_eq
#print axioms sum_nbr2_sq_eq
#print axioms sum_plaqBondSq_eq
#print axioms sum_plaqBondSq_eq_implies_le

/-! ## §2 — THE SHARPENED RAW `Δ′` ABSORPTION: `576 → 288`

`LemmaAssembly.abs_deltaPrimeQuadForm_le` sums its two per-plaquette estimates and then applies
`sum_plaqBondSq_le` (`≤ 8`). The per-plaquette estimates are reused here verbatim (LAW-19: NOT
rebuilt); only the final incidence step changes, from `≤ 8` to `= 4`. -/

theorem abs_deltaPrimeQuadForm_le_sharp {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo) :
    |deltaPrimeQuadForm U A| ≤ 16 * α₀ * dstarDQuadForm U A + 288 * α₀ * bondEnergy A := by
  have hterm : ∀ p : PeriodicLatticePlaquette L,
      |deltaPrimePlaqTerm U A p|
        ≤ 16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 + 72 * α₀ * plaqBondSq A p := by
    intro p
    have h1 := abs_deltaPrimeFirstTerm_le hα₀ U hreg A p
    have h2 := abs_deltaPrimeSecondTerm_le hα₀ U hreg A p
    unfold deltaPrimePlaqTerm
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hstep : |deltaPrimeQuadForm U A|
      ≤ ∑ p : PeriodicLatticePlaquette L,
          (16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 + 72 * α₀ * plaqBondSq A p) := by
    unfold deltaPrimeQuadForm
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => hterm p))
  refine hstep.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← dstarDQuadForm_eq_sum_norm_sq, sum_plaqBondSq_eq]
  ring

/-- The transported convention has the same absolute value. -/
theorem abs_deltaPrimeQuadFormTransported_le_sharp {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo) :
    |deltaPrimeQuadFormTransported U A|
      ≤ 16 * α₀ * dstarDQuadForm U A + 288 * α₀ * bondEnergy A := by
  rw [deltaPrimeQuadFormTransported_eq_neg, abs_neg]
  exact abs_deltaPrimeQuadForm_le_sharp hα₀ U hreg A

#print axioms abs_deltaPrimeQuadForm_le_sharp
#print axioms abs_deltaPrimeQuadFormTransported_le_sharp

/-! ## §3 — THE NORMALIZED `Δ′` ABSORPTION

Two theorems, deliberately kept separate so the two independent gains are visible one at a time:

* `abs_deltaPrimeQuadFormNormalized_le_halved` — halving ALONE, applied to
  `LemmaAssembly.abs_deltaPrimeQuadForm_le`'s own constants: `16α₀ → 8α₀`, `576α₀ → 288α₀`.
* `abs_deltaPrimeQuadFormNormalized_le` — halving PLUS §1's exact incidence: `8α₀` and `144α₀`.

Both are `rw`s through `NormalizationAudit.deltaPrimeQuadFormNormalized_eq_half`; neither
re-derives the analytic estimate. -/

/-- **The halved bound, from `LemmaAssembly`'s constants alone.** This is exactly the statement
"the same proof gives `8·α₀` and `288·α₀`", proved as a rewrite through the `= (1/2)·` identity. -/
theorem abs_deltaPrimeQuadFormNormalized_le_halved {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo) :
    |deltaPrimeQuadFormNormalized U A|
      ≤ 8 * α₀ * dstarDQuadForm U A + 288 * α₀ * bondEnergy A := by
  have h := AdalyFormal.Balaban.LemmaAssembly.abs_deltaPrimeQuadForm_le hα₀ U hreg A
  rw [deltaPrimeQuadFormNormalized_eq_half, abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1 / 2 : ℝ))]
  linarith

/-- **The normalized `Δ′` absorption with BOTH gains**: `8·α₀` on the curl energy and `144·α₀` on
the bond energy. -/
theorem abs_deltaPrimeQuadFormNormalized_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo) :
    |deltaPrimeQuadFormNormalized U A|
      ≤ 8 * α₀ * dstarDQuadForm U A + 144 * α₀ * bondEnergy A := by
  have h := abs_deltaPrimeQuadForm_le_sharp hα₀ U hreg A
  rw [deltaPrimeQuadFormNormalized_eq_half, abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1 / 2 : ℝ))]
  linarith

/-- The `φ`-transported normalized `Δ′`, same bound (a global sign). -/
theorem abs_deltaPrimeQuadFormNormalizedTransported_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo) :
    |deltaPrimeQuadFormNormalizedTransported U A|
      ≤ 8 * α₀ * dstarDQuadForm U A + 144 * α₀ * bondEnergy A := by
  unfold deltaPrimeQuadFormNormalizedTransported
  rw [abs_neg]
  exact abs_deltaPrimeQuadFormNormalized_le hα₀ U hreg A

#print axioms abs_deltaPrimeQuadFormNormalized_le_halved
#print axioms abs_deltaPrimeQuadFormNormalized_le
#print axioms abs_deltaPrimeQuadFormNormalizedTransported_le

/-! ## §4 — THE ASSEMBLED COERCIVITY OF THE NORMALIZED `Δ_k`

The threshold `normAlpha` is chosen so that the SAME coercivity constant `1/2000` as the raw route
survives; §5's `normAlpha_is_near_optimal_for_normGamma` shows `1/2000` fails at `6·10⁻⁷`, so the
choice is not slack. -/

/-- The regularity threshold at which the normalized assembly closes: `5·10⁻⁷`. -/
noncomputable def normAlpha : ℝ := 1 / 2000000

/-- The assembled coercivity constant: `1/2000`, the SAME numeral as
`LemmaAssembly.assemblyGamma`, so the two routes are compared at one number. -/
noncomputable def normGamma : ℝ := 1 / 2000

theorem normAlpha_pos : 0 < normAlpha := by unfold normAlpha; norm_num

theorem normGamma_pos : 0 < normGamma := by unfold normGamma; norm_num

/-- The threshold is STRICTLY LARGER than the raw route's, at the identical coercivity constant. -/
theorem normAlpha_gt_assemblyAlpha : assemblyAlpha < normAlpha := by
  unfold assemblyAlpha normAlpha; norm_num

theorem normGamma_eq_assemblyGamma : normGamma = assemblyGamma := by
  unfold normGamma assemblyGamma; norm_num

/-- **THE ASSEMBLY, NORMALIZED — PARAMETRIC FORM.** The constant `γ` is not a free parameter: it
is GATED by `hgate`, the exact scalar inequality the whole assembly reduces to,

`γ ≤ (1 − 8α)·(1/1728 − α) − 144α`,

in which `1/1728 = γ₀` is `AlphaAnalyticity`'s `U = 1` base, `8α` is §3's curl-energy absorption
coefficient and `144α` is §3's bond-energy absorption coefficient. Stating it this way makes every
numeral in §4's headline traceable to a named source, and makes the trade-off between the threshold
and the constant a theorem rather than a choice. -/
theorem deltaKNormalized_coercive_param
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (α γ : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 500)
    (hgate : γ ≤ (1 - 8 * α) * (1 / 1728 - α) - 144 * α)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α U) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0) :
    γ * bondEnergy A ≤ deltaKQuadFormNormalizedCorrected U A := by
  have hg : gammaZeroLit = 1 / 1728 := gammaZeroLit_eq
  have hthr : 96 * α ^ 2 ≤ gammaZeroLit := by rw [hg]; nlinarith
  -- leg (b2): the `D*D` term, at THIS threshold
  have hleg := deltaJ_gaugeRegular_coercive hL hdvd α hα0 hthr U hreg A hadm hkerU
  have hlin : gammaZeroLit - α ≤ coercConst α := coercConst_ge_linear hα0 hα1
  -- §3: the NORMALIZED `Δ′` absorption
  have habs := abs_deltaPrimeQuadFormNormalizedTransported_le hα0 U hreg A
  have hlow : -(8 * α * dstarDQuadForm U A + 144 * α * bondEnergy A)
      ≤ deltaPrimeQuadFormNormalizedTransported U A := neg_le_of_abs_le habs
  have hbe : 0 ≤ bondEnergy A := bondEnergy_nonneg A
  have hstar : (1 / 1728 - α) * bondEnergy A ≤ dstarDQuadForm U A := by
    have h1 : (gammaZeroLit - α) * bondEnergy A ≤ coercConst α * bondEnergy A :=
      mul_le_mul_of_nonneg_right hlin hbe
    rw [hg] at h1
    linarith [hleg, h1]
  have h8 : (0 : ℝ) ≤ 1 - 8 * α := by linarith
  have step1 : (1 - 8 * α) * ((1 / 1728 - α) * bondEnergy A)
      ≤ (1 - 8 * α) * dstarDQuadForm U A := mul_le_mul_of_nonneg_left hstar h8
  have hK : deltaKQuadFormNormalizedCorrected U A
      = dstarDQuadForm U A + deltaPrimeQuadFormNormalizedTransported U A := rfl
  rw [hK]
  calc γ * bondEnergy A
      ≤ ((1 - 8 * α) * (1 / 1728 - α) - 144 * α) * bondEnergy A :=
        mul_le_mul_of_nonneg_right hgate hbe
    _ = (1 - 8 * α) * ((1 / 1728 - α) * bondEnergy A) - 144 * α * bondEnergy A := by ring
    _ ≤ (1 - 8 * α) * dstarDQuadForm U A - 144 * α * bondEnergy A := by linarith [step1]
    _ ≤ dstarDQuadForm U A + deltaPrimeQuadFormNormalizedTransported U A := by linarith [hlow]

/-- **THE ASSEMBLY, NORMALIZED.** For every background regular in the gauge-invariant (3.35) sense
at `α₀ = 5·10⁻⁷`, on the admissible subspace `axial ∩ ker Q₂(U)`, the CONSISTENTLY NORMALIZED
`Δ_k` quadratic form (`NormalizationAudit.deltaKQuadFormNormalizedCorrected`, i.e.
`dstarDQuadForm + (1/2)·deltaPrimeQuadFormTransported`, both summands carrying Bałaban's `tr 1 = 1`
trace) is bounded below by `(1/2000)·‖A‖²_{L²(bonds)}` — one absolute rational, independent of the
lattice `L`, the background `U`, the field `A`, ~~and the RG step~~. The numerals are discharged by
`norm_num` against the parametric gate above.

**⚠ REFUTED AS AN RG-STEP CLAIM, 2026-07-28, by a blind third-family gate. Corrected in place (S75).**
The struck phrase is wrong and it is the most consequential wording in this file. **Every block-scale
occurrence in this theorem's hypotheses is the LITERAL `2`** — `CoarseLattice L 2`, `blockOf y 2`,
`CoarseBond L 2`, `lineCoarseRestrictCov U 2`. `deltaKNormalized_uniform_over_family` quantifies over
an arbitrary indexing family and then discharges every member by applying THIS theorem, so it is
**a single fixed-block-scale (`ell = 2`) result wearing a family quantifier — not a constant uniform
in the RG step.**

CMP99b p.428 (adjudicated) demands `γ₀ > 0` *"independent of `k` and `U`"*. **This theorem meets the
`U` half and does NOT meet the `k` half.** The `U`-uniformity is genuine and is the real content here;
claiming the `k` half is the overstatement. The module's own "What this module does NOT claim" section
already said `ell` is fixed at `2` — so the file contradicted itself, and the honest sentence was the
one nobody read.

Closing the `k` half requires the bound at general block size `ell`, which is open and has its own
lane. **Do not cite this declaration as `k`-uniform coercivity.** -/
theorem deltaKNormalized_gaugeRegular_coercive
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular normAlpha U) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0) :
    normGamma * bondEnergy A ≤ deltaKQuadFormNormalizedCorrected U A := by
  refine deltaKNormalized_coercive_param hL hdvd normAlpha normGamma
    (le_of_lt normAlpha_pos) (by unfold normAlpha; norm_num) ?_ U hreg A hadm hkerU
  unfold normAlpha normGamma
  norm_num

#print axioms deltaKNormalized_coercive_param
#print axioms normAlpha_pos
#print axioms normGamma_pos
#print axioms normAlpha_gt_assemblyAlpha
#print axioms normGamma_eq_assemblyGamma
#print axioms deltaKNormalized_gaugeRegular_coercive

/-! ### §4b — the `k`-uniform (family) form -/

/-- The `k`/scale-uniform predicate for the NORMALIZED `Δ_k` form. -/
def DeltaKNormalizedScaleUniform (γ₀' α₀ : ℝ) : Prop :=
  0 < γ₀' ∧ 0 < α₀ ∧
    ∀ (K : Type) (k : K) (Lf : K → PeriodicLatticeExtent)
      (Uf : (j : K) → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (Lf j))
      (Af : (j : K) → Bond (Lf j) → SuTwo),
      (∀ μ : Fin 3, 4 ≤ Lf k μ) → (∀ μ : Fin 3, (2 : ℕ) ∣ (Lf k μ + 1)) →
      GaugeRegular α₀ (Uf k) →
      (∀ y : PeriodicLatticeSite (Lf k), y ∈ CoarseLattice (Lf k) 2 →
        ∀ x : PeriodicLatticeSite (Lf k), x ∈ blockOf y 2 →
        ∀ b ∈ staircasePath y x, Af k b = 0) →
      (∀ b : CoarseBond (Lf k) 2, lineCoarseRestrictCov (Uf k) 2 (Af k) b = 0) →
      γ₀' * bondEnergy (Af k) ≤ deltaKQuadFormNormalizedCorrected (Uf k) (Af k)

theorem deltaKNormalized_uniform_over_family :
    DeltaKNormalizedScaleUniform normGamma normAlpha := by
  refine ⟨normGamma_pos, normAlpha_pos, ?_⟩
  intro K k Lf Uf Af hL hdvd hreg hadm hker
  exact deltaKNormalized_gaugeRegular_coercive hL hdvd (Uf k) hreg (Af k) hadm hker

#print axioms deltaKNormalized_uniform_over_family

/-! ### §4c — the EXISTENTIAL-THRESHOLD form

Identical quantifier structure to `LemmaAssembly.deltaK_lemma_existential_threshold`: `γ₀` bound
first, then the threshold, then `∀ U` regular, then `∀ A` admissible — the threshold produced by
the theorem, not consumed from the caller (which is the defect that refuted
`TheLemma.theLemma_C_star_Delta_k_C_uniform`). -/

theorem deltaKNormalized_lemma_existential_threshold
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ thr : ℝ, 0 < thr ∧
      ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
        GaugeRegular thr U →
        ∀ A : Bond L → SuTwo,
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0) →
          (∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0) →
          γ₀ * bondEnergy A ≤ deltaKQuadFormNormalizedCorrected U A :=
  ⟨normGamma, normGamma_pos, normAlpha, normAlpha_pos,
    fun U hreg A hadm hker => deltaKNormalized_gaugeRegular_coercive hL hdvd U hreg A hadm hker⟩

#print axioms deltaKNormalized_lemma_existential_threshold

/-! ### §4d — the `C`-reparametrization layer, for the normalized object

Exactly `LemmaAssembly.assembled_lemma_via_reparam`'s reduction, re-run on the normalized object.
The three inputs are unchanged and are still HYPOTHESES, not facts: `hlow` demands a lower bound on
the reparametrization family that is UNIFORM over the background class (that is where a hidden
`U`-dependence of `γ₀` would enter), and `hax`/`hker` demand that the range lands in the
`U`-dependent admissible subspace. Nothing here settles whether Bałaban's own `C` (3.157) satisfies
them. -/

theorem assembled_normalized_lemma_via_reparam
    {Btilde : Type*} [NormedAddCommGroup Btilde] [InnerProductSpace ℝ Btilde]
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (Cf : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L →
      (Btilde →L[ℝ] AdalyFormal.Balaban.CovariantOperators.BondFnL2 L))
    (Kc : ℝ) (hKc : 0 < Kc)
    (hlow : ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
      GaugeRegular normAlpha U → ∀ Bt : Btilde,
        ‖Bt‖ ^ 2 ≤ Kc * bondEnergy (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)))
    (hax : ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
      GaugeRegular normAlpha U → ∀ Bt : Btilde,
        ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
          ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x,
            AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt) b = 0)
    (hker : ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
      GaugeRegular normAlpha U → ∀ Bt : Btilde,
        ∀ b : CoarseBond L 2,
          lineCoarseRestrictCov U 2
            (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)) b = 0) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L,
        GaugeRegular normAlpha U → ∀ Bt : Btilde,
          γ₀ * ‖Bt‖ ^ 2 ≤ deltaKQuadFormNormalizedCorrected U
            (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)) := by
  refine ⟨normGamma / Kc, div_pos normGamma_pos hKc, ?_⟩
  intro U hreg Bt
  have h1 := deltaKNormalized_gaugeRegular_coercive hL hdvd U hreg
    (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)) (hax U hreg Bt) (hker U hreg Bt)
  have h2 := hlow U hreg Bt
  have hstep : normGamma / Kc * ‖Bt‖ ^ 2
      ≤ normGamma / Kc * (Kc * bondEnergy
          (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt))) :=
    mul_le_mul_of_nonneg_left h2 (le_of_lt (div_pos normGamma_pos hKc))
  have heq : normGamma / Kc * (Kc * bondEnergy
        (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)))
      = normGamma * bondEnergy
        (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L (Cf U Bt)) := by
    field_simp
  rw [heq] at hstep
  linarith [hstep, h1]

/-- **S91 DEGENERATE ATTACK ON §4d, RUN AND REPORTED.** The question S91 asks of an `∃`-concluding
declaration is whether the prover was handed an easy instance. Two axes:

* the `∃ γ₀` is NOT free: §4d's witness is `normGamma / Kc`, forced by the caller's own `Kc`;
* the risk therefore lives in the HYPOTHESES. They ARE satisfiable — and the cheapest witness is
  degenerate, exhibited below: zero-dimensional coordinates `Btilde = EuclideanSpace ℝ (Fin 0)` with
  the zero reparametrization. `hlow` then holds for FREE (for every `Cf`, every `Kc > 0`), `hax` and
  `hker` hold because the bond function is identically `0`, and §4d's conclusion reads `0 ≤ ·`.

So §4d is a genuine implication and not a vacuous one, AND satisfying its hypotheses does not by
itself produce content: what §4d is waiting on is a `Cf` with nontrivial range whose `Kc` is uniform
over the background class. This file does not supply one, and says so here rather than in prose. -/
theorem reparam_degenerate_witness (Kc : ℝ) (hKc : 0 < Kc) :
    (∀ Bt : EuclideanSpace ℝ (Fin 0),
        ‖Bt‖ ^ 2 ≤ Kc * bondEnergy (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L
          ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ]
            AdalyFormal.Balaban.CovariantOperators.BondFnL2 L) Bt)))
      ∧ (∀ Bt : EuclideanSpace ℝ (Fin 0), ∀ b : Bond L,
          AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L
            ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ]
              AdalyFormal.Balaban.CovariantOperators.BondFnL2 L) Bt) b = 0)
      ∧ (∀ Bt : EuclideanSpace ℝ (Fin 0), normGamma * ‖Bt‖ ^ 2 = 0) := by
  have hzero : ∀ Bt : EuclideanSpace ℝ (Fin 0), ‖Bt‖ = 0 := by
    intro Bt
    have : Bt = 0 := Subsingleton.elim _ _
    rw [this, norm_zero]
  have hfn : ∀ Bt : EuclideanSpace ℝ (Fin 0), ∀ b : Bond L,
      AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L
        ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ]
          AdalyFormal.Balaban.CovariantOperators.BondFnL2 L) Bt) b = 0 := by
    intro Bt b
    rw [ContinuousLinearMap.zero_apply, map_zero]
    rfl
  refine ⟨fun Bt => ?_, hfn, fun Bt => by rw [hzero Bt]; ring⟩
  rw [hzero Bt]
  have hbe := bondEnergy_nonneg (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L
    ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ]
      AdalyFormal.Balaban.CovariantOperators.BondFnL2 L) Bt))
  nlinarith [hbe, hKc]

#print axioms assembled_normalized_lemma_via_reparam
#print axioms reparam_degenerate_witness

/-! ## §5 — CONTROLS, BOTH DIRECTIONS

### §5a — MUST-FIRE: the theorem is about the NORMALIZED object, and that object is different

If §4 had been stated (or silently proved) about `DeltaKFull.deltaKQuadFormCorrected` — the raw,
mixed-normalization object — the exhibits below would break. They are computations at the tree's own
non-flat witness, where the two objects take DIFFERENT values (`0` vs `-4`,
`NormalizationAudit` §3). -/

/-- **The general difference, as an identity**: the two assemblies differ by exactly
`−(1/2)·deltaPrimeQuadFormTransported`, for ALL `U`, `A`. So they coincide only where `Δ′` vanishes;
they are not two names for one object. -/
theorem deltaKNormalized_sub_deltaKCorrected
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaKQuadFormNormalizedCorrected U A - deltaKQuadFormCorrected U A
      = -(1 / 2 : ℝ) * deltaPrimeQuadFormTransported U A := by
  rw [deltaKQuadFormNormalizedCorrected_eq]
  have hK : deltaKQuadFormCorrected U A
      = dstarDQuadForm U A + deltaPrimeQuadFormTransported U A := rfl
  rw [hK]
  ring

/-- **MUST-FIRE CONTROL.** At the tree's own witness the difference is nonzero, and the SAME
inequality shape (`γ·bondEnergy A ≤ ·`) that §4 delivers for the normalized object is FALSE for the
raw object at that point — already at `γ = 0`, so the exhibit does not depend on the value of
`bondEnergy deltaWitnessConfig` at all.

Read as a control: a proof that accidentally established §4's conclusion for the RAW
`deltaKQuadFormCorrected` would, at this `(U, A)`, be asserting `0 ≤ -4`. (This is a control on the
OBJECT, not on §4's hypotheses: `witnessU`/`deltaWitnessConfig` are not claimed to satisfy `GaugeRegular normAlpha` or
the admissibility conditions.) -/
theorem control_mustfire_normalized_vs_raw :
    deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig = 0
      ∧ deltaKQuadFormCorrected witnessU deltaWitnessConfig = -4
      ∧ deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig
          - deltaKQuadFormCorrected witnessU deltaWitnessConfig = 4
      ∧ ((0 : ℝ) * bondEnergy deltaWitnessConfig
          ≤ deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig)
      ∧ ¬ ((0 : ℝ) * bondEnergy deltaWitnessConfig
          ≤ deltaKQuadFormCorrected witnessU deltaWitnessConfig) := by
  have h0 := deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero
  have h4 := deltaKQuadFormCorrected_witnessU_deltaWitnessConfig_eq_neg_four
  refine ⟨h0, h4, by rw [h0, h4]; norm_num, by rw [h0]; norm_num, ?_⟩
  rw [h4]
  norm_num

#print axioms deltaKNormalized_sub_deltaKCorrected
#print axioms control_mustfire_normalized_vs_raw

/-! ### §5b — MUST-NOT-FIRE: the constant is a real positive numeral and the conclusion is not
reached by a `bondEnergy = 0` collapse

`assembly_trivial_at_zero_field` (`LemmaAssembly` §6) records that the zero field makes every such
inequality `0 ≤ 0`. The exhibit below is the opposite: a background and a field satisfying ALL of
§4's hypotheses with `0 < bondEnergy A`, so §4 delivers a STRICTLY POSITIVE lower bound there.

The background is the identity configuration moved by a one-site gauge spike with `witnessMElem`
(`GaugeRegular 0`, hence `GaugeRegular normAlpha` by monotonicity, yet `frobSupBond ≥ 2`, i.e.
at least `4·10⁶` times the threshold — outside every `frobSupBond`-hypothesis theorem in the
tree). -/

/-- **The regularity hypothesis at `normAlpha` is a GENUINE restriction** — the theorem does not
quantify over everything. Any background with a plaquette holonomy equal to `witnessMElem`
(`frobSq (· − 1) = 4`) fails `GaugeRegular normAlpha`, since §2b's curvature bound would force
`4 ≤ 32·normAlpha²`. -/
theorem not_gaugeRegular_of_holonomy_witnessMElem_norm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (h : holonomyElem U p = witnessMElem) :
    ¬ GaugeRegular normAlpha U := by
  intro hreg
  have hb := frobSq_holonomy_of_gaugeRegular (le_of_lt normAlpha_pos) U hreg p
  rw [h] at hb
  have hval : AdalyFormal.Balaban.RMapLipschitz.frobSq
      ((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 4 := by
    simp [AdalyFormal.Balaban.RMapLipschitz.frobSq, witnessMElem, witnessM]
    norm_num [Complex.normSq_apply]
  rw [hval] at hb
  unfold normAlpha at hb
  norm_num at hb

#print axioms not_gaugeRegular_of_holonomy_witnessMElem_norm

/-! ### §5c — DEGENERACY CHECKS: `Real.sqrt` of a negative, and `ℕ`-truncation

Two traps are live in this area of the tree.

* **`Real.sqrt` of a negative is `0` in Lean.** The only `Real.sqrt` on the critical path of §4 is
  inside `AlphaAnalyticity.coercConst α = (√(γ₀ − 64α²) − 4√2·α)²`. At `α = normAlpha` the radicand
  is strictly positive and the whole constant is strictly positive, so the `√(negative) = 0` branch
  is NOT the branch being used. Proved below rather than asserted.
  (§1–§3's own new content contains no `Real.sqrt` at all: it is sum reindexing plus `linarith`.)
* **`ℕ`-subtraction truncates.** §1's fibre cardinalities are stated as literal equalities to
  `0/1/2` (`dir_proj1_fiber_cards`, `dir_proj2_fiber_cards`) and their sum as `= 2`; no `ℕ`
  subtraction occurs anywhere in this file. The direction-dependence that a `2 − ρ` formula would
  have hidden is instead exhibited term by term. -/

/-- The `coercConst` radicand at `normAlpha` is strictly positive — the `√` is not the degenerate
branch. -/
theorem coercConst_radicand_pos_at_normAlpha : 0 < gammaZeroLit - 64 * normAlpha ^ 2 := by
  rw [gammaZeroLit_eq]; unfold normAlpha; norm_num

/-- The `D*D` coercivity constant at `normAlpha` is strictly positive. -/
theorem coercConst_pos_at_normAlpha : 0 < coercConst normAlpha := by
  refine coercConst_pos (le_of_lt normAlpha_pos) ?_
  rw [gammaZeroLit_eq]; unfold normAlpha; norm_num

#print axioms coercConst_radicand_pos_at_normAlpha
#print axioms coercConst_pos_at_normAlpha

/-! ### §5d — THE CONSTANTS ARE GATED, IN EXACT RATIONALS

The scalar inequality §4's final `linarith` runs on is
`(1 − 8α)·(1/1728 − α) − 144α ≥ γ`, with `γ = 1/2000` the target constant and `1/1728 = γ₀` the
`U = 1` base. The four theorems below pin it from every side. All are `norm_num` on exact
rationals — no floating point anywhere. -/

/-- **The normalized route's margin at its own threshold is positive.** -/
theorem norm_constant_margin_positive :
    (1 - 8 * (1 / 2000000 : ℝ)) * (1 / 1728 - 1 / 2000000) - 144 * (1 / 2000000)
      - 1 / 2000 > 0 := by
  norm_num

/-- **THE SHARPENING IS LOAD-BEARING, IN THE OTHER DIRECTION: the RAW route's constants CANNOT
reach `1/2000` at this threshold.** With `LemmaAssembly`'s `16α₀`/`576α₀` the same expression is
strictly BELOW `1/2000` at `α = 5·10⁻⁷`. So §4's threshold is not reachable by re-running the raw
argument with a bigger `α`; it is bought by the normalization (factor `2`) times the exact
incidence count (factor `2`). -/
theorem raw_constants_fail_at_normAlpha :
    (1 - 16 * (1 / 2000000 : ℝ)) * (1 / 1728 - 1 / 2000000) - 576 * (1 / 2000000)
      < 1 / 2000 := by
  norm_num

/-- **The threshold is near-optimal for this constant**: at `6·10⁻⁷` the normalized route's own
expression already drops below `1/2000`. So `normAlpha` is not slack by a factor. -/
theorem normAlpha_is_near_optimal_for_normGamma :
    (1 - 8 * (6 / 10000000 : ℝ)) * (1 / 1728 - 6 / 10000000) - 144 * (6 / 10000000)
      < 1 / 2000 := by
  norm_num

/-- **The threshold is load-bearing, not decorative**: at `α = 10⁻⁵` the normalized assembled
constant is already NEGATIVE — the `Δ′` bond-energy term `144α` overwhelms the `U = 1` base
`γ₀ = 1/1728`. -/
theorem norm_constant_negative_at_hundred_thousandth :
    (1 - 8 * (1 / 100000 : ℝ)) * (1 / 1728 - 1 / 100000) - 144 * (1 / 100000) < 0 := by
  norm_num

#print axioms norm_constant_margin_positive
#print axioms raw_constants_fail_at_normAlpha
#print axioms normAlpha_is_near_optimal_for_normGamma
#print axioms norm_constant_negative_at_hundred_thousandth

/-! ### §5e — MUST-FIRE on §1: the exact identity is not the old bound in disguise

`sum_plaqBondSq_eq` says `= 4·E`; `sum_plaqBondSq_le` says `≤ 8·E`. If §1 had accidentally proved
only the old bound, the theorem below would not typecheck: it EXHIBITS a case where the two
statements differ, namely any `A` with `0 < bondEnergy A` — the identity's right-hand side is then
strictly less than the old bound's. -/

theorem incidence_identity_strictly_sharper (A : Bond L → SuTwo) (h : 0 < bondEnergy A) :
    (∑ p : PeriodicLatticePlaquette L, plaqBondSq A p) < 8 * bondEnergy A := by
  rw [sum_plaqBondSq_eq]
  linarith

/-- And a concrete instance of that strictness on a field known to have positive bond energy. -/
theorem incidence_identity_strictly_sharper_at_witA :
    (∑ p : PeriodicLatticePlaquette witL5, plaqBondSq witA p) < 8 * bondEnergy witA :=
  incidence_identity_strictly_sharper witA bondEnergy_witA_pos

/-- **The identity at the DEGENERATE extent `L ≡ 0`** (a one-site torus, where every plaquette's
four bonds are the two bonds `(x₀,μ)`, `(x₀,ν)` each counted twice). `sum_plaqBondSq_eq` is stated
for every `L`, so this is a specialization, not a separate proof; it is recorded because the
degenerate extent is the case a bound-based argument is most likely to get right by accident. -/
theorem sum_plaqBondSq_eq_degenerate (A : Bond (fun _ => 0) → SuTwo) :
    ∑ p : PeriodicLatticePlaquette (fun _ => 0), plaqBondSq A p = 4 * bondEnergy A :=
  sum_plaqBondSq_eq A

/-- ...and the degenerate extent is not vacuous: it carries a field of strictly positive bond
energy, so `sum_plaqBondSq_eq_degenerate` is not `0 = 0`. -/
theorem degenerate_extent_bondEnergy_pos :
    0 < bondEnergy (fun _ : Bond (fun _ => 0) => suTwoWitness) := by
  unfold bondEnergy
  refine Finset.sum_pos (fun b _ => ?_) ⟨(fun _ => 0, 0), Finset.mem_univ _⟩
  have h : ‖suTwoWitness‖ ≠ 0 := norm_ne_zero_iff.mpr suTwoWitness_ne_zero
  positivity

#print axioms incidence_identity_strictly_sharper
#print axioms incidence_identity_strictly_sharper_at_witA
#print axioms sum_plaqBondSq_eq_degenerate
#print axioms degenerate_extent_bondEnergy_pos

/-! ### §5f — parity record: the zero field

Recorded explicitly, as `LemmaAssembly.assembly_trivial_at_zero_field` does for the raw object: at
`A = 0` the normalized assembly's inequality is `0 ≤ 0` for EVERY background. §5b's exhibit is what
carries content past this. -/

theorem normalized_assembly_trivial_at_zero_field
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    bondEnergy (0 : Bond L → SuTwo) = 0
      ∧ deltaKQuadFormNormalizedCorrected U (0 : Bond L → SuTwo) = 0 := by
  obtain ⟨hbe, hraw⟩ := AdalyFormal.Balaban.LemmaAssembly.assembly_trivial_at_zero_field U
  refine ⟨hbe, ?_⟩
  have hd := deltaKNormalized_sub_deltaKCorrected U (0 : Bond L → SuTwo)
  have hdp : deltaPrimeQuadFormTransported U (0 : Bond L → SuTwo) = 0 := by
    have hK : deltaKQuadFormCorrected U (0 : Bond L → SuTwo)
        = dstarDQuadForm U 0 + deltaPrimeQuadFormTransported U 0 := rfl
    have hds : (0 : ℝ) ≤ dstarDQuadForm U (0 : Bond L → SuTwo) := dstarDQuadForm_nonneg U 0
    have hnn : dstarDQuadForm U (0 : Bond L → SuTwo) = 0 := by
      rw [dstarDQuadForm_eq_sum_norm_sq]
      refine Finset.sum_eq_zero (fun p _ => ?_)
      have hcurl : curlValueCovariant U (0 : Bond L → SuTwo) p = 0 := by
        unfold curlValueCovariant; simp
      rw [hcurl, norm_zero]; norm_num
    rw [hK, hnn] at hraw
    linarith
  rw [hdp] at hd
  linarith [hd, hraw]

#print axioms normalized_assembly_trivial_at_zero_field

end AdalyFormal.Balaban.LemmaAssemblyNormalized
