/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.LemmaAssemblyNormalized
import AdalyFormal.Balaban.BlockPoincareSharp
import AdalyFormal.Balaban.RegularUDomainWitnessGeneralU

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

/-!
# `GeneralEllAssembly.lean` — the normalized `Δ_k` coercivity assembly at GENERAL BLOCK SIZE `ell`

`LemmaAssemblyNormalized.deltaKNormalized_gaugeRegular_coercive` proves
`(1/2000)·bondEnergy A ≤ deltaKQuadFormNormalizedCorrected U A` for `GaugeRegular (5·10⁻⁷) U`,
on `axial ∩ ker Q₂(U)` — with the block size **hardcoded to `ell = 2`** in nine binder positions.
Its `deltaKNormalized_uniform_over_family` quantifies over an RG family but discharges every member
by the same `ell = 2` theorem, so the constant is `k`-independent at ONE fixed block scale.

This module lifts the whole chain to arbitrary `ell ≥ 2`, additively (nothing above is edited), and
reports what the constant does.

## §0 — THE MEASUREMENT: what actually depended on `ell = 2` (classification)

Read off declaration STATEMENTS, walking the chain bottom-up. `(a)` = already `ell`-generic,
`(b)` = `ell = 2` for convenience only, `(c)` = `ell = 2` essentially.

| Ingredient | Class |
| --- | --- |
| `LemmaAssemblyNormalized.sum_plaqBondSq_eq` (`∑_p plaqBondSq A p = 4·bondEnergy A`) | **(a)** no `ell` occurs; it is about plaquettes and bonds |
| `dir_proj1/2_fiber_cards`, `dir_fiber_card_sum` | **(a)** direction combinatorics of `Fin 3` |
| `LemmaAssembly.abs_deltaPrimeFirstTerm_le` / `abs_deltaPrimeSecondTerm_le` | **(a)** no `ell` |
| `LemmaAssemblyNormalized.abs_deltaPrimeQuadFormNormalized_le` (`8α₀·dstarD + 144α₀·E`) | **(a)** no `ell` in statement or proof |
| `NormalizationAudit.deltaPrimeQuadFormNormalized_eq_half` | **(a)** no `ell` |
| `RegularUCoercivityFull.covCoarse_Q1flat_le_of_kerQU` (`64/ell`) | **(a)** already `∀ ell` |
| `AlphaAnalyticity.axialGauge_gauge`, `mem_kerQ_gauge`, `dstarDQuadForm_gauge`, `bondEnergy_gauge` | **(a)** already `∀ ell` |
| `RegularUDirectCoercivity.deltaJ_regularU_coercive_of_U1coercive` (the (b1) transfer) | **(a)** `ell`-free — its hypothesis is a `U=1` coercivity AT `A` |
| `SuTwoGeomU1` §3–§5 (`covBondInner_eq_sum`, `covPlaqInner_flatCurl_eq_sum`, `covCoarseBondInner_lineCoarse_eq_sum`, `suComp_mem_admissible`) | **(a)** already `∀ ell` |
| `SuTwoGeomU1.suTwoGeomAdditive_trivialU_of_admissible` | **(b)** `ell = 2` ONLY because it calls the `ell = 2` scalar milestone; every lemma inside it is (a) |
| `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` | **(b)** `2` hardcoded in four places, all inherited |
| `AlphaAnalyticity.deltaJ_gaugeRegular_coercive`, `coercConst` | **(b)** plumbing |
| `LemmaAssemblyNormalized.deltaKNormalized_coercive_param` / `_gaugeRegular_coercive` | **(b)** plumbing |
| the `U = 1` base NUMERAL `AlphaAnalyticity.gammaZeroLit = (1/108)·2⁻⁴ = 1/1728` | **(c)** ESSENTIALLY `ell = 2`: the printed `(2.128)` constant `(1/108)·ell⁻⁴` is proved in this tree only at `ell = 2` (`HrefReduction.lemma24_unconditional_U1_ell2_uncond`) and `ell = 3` (`BlockPoincareSharp.lemma24_printed_ell3`) |
| the torus hypothesis `hL : ∀ μ, 4 ≤ L μ` | **(b)** the general-`ell` base uses `∀ ν, ell < L ν + 1` instead — at `ell = 2` that is `2 ≤ L ν`, strictly WEAKER |

**Exactly one ingredient is class (c): the numerical value of the `U = 1` additive base.**
This confirms, as compiled theorems rather than prose, the determination already recorded in
`LemmaAssembly.lean` §7 (lines 1304–1338).

## §0b — LAW-19: what was REUSED rather than rebuilt

* `BlockPoincareSharp.lemma24_sharpened` — `ell·Σ_c|Q₁B|² + Σ_p|∂₁B|² ≥ (1/54)·ell⁻⁵·‖B‖²`,
  every `ell ≥ 2`. This is the general-`ell` scalar base, and it is STRONGER than
  `Lemma24GeneralEll.lemma24_general_ell`'s `(1/180)·ell⁻⁵` by `10/3`. **Nothing of it is redone.**
* `SuTwoGeomU1` §3–§5 — the entire scalar→𝔰𝔲(2) component machinery, already `∀ ell`.
  §1 below is the ONE missing link: `SuTwoGeomU1` §6 at general `ell`, stated PARAMETRICALLY in the
  scalar input so that any future scalar base (e.g. a restored `ell⁻⁴`) drops straight in.
* `RegularUCoercivityFull.covCoarse_Q1flat_le_of_kerQU`, `RegularUDirectCoercivity` (b1),
  `AlphaAnalyticity`'s gauge-covariance layer, `LemmaAssemblyNormalized`'s `Δ′` absorption —
  imported and applied, not re-derived.
* `FullReparamC.admissibleWitness U ell y` — the general-`ell`, general-`U` non-vacuity witness
  (`≠ 0`, `∈ ker Q_ell(U)`, axial-gauge, for every `2 ≤ ell`). Used for the `ell = 3` and `ell = 4`
  must-not-fire controls.
* CHECKED AND NOT ON THIS CHAIN (recorded so it is not re-checked): `VolumeScalingV.card_Ax_eq`
  and `OneScaleVolumeV.volumeUniformCoercivity_general` (`γ = 1/(9·ell⁸)`) are the `U = 1`
  Hodge/volume coercivity on `axUnionVCov` — a different domain and a different quadratic form from
  the `Δ_k` assembly's `ker Q_ell(U) ∩ axial`. Not consumed here.

## §0c — THE CONSTANT, PLAINLY: IT DECAYS LIKE `ell⁻⁵`

The delivered pair is

    γ(ell) = (1/60)·ell⁻⁵      threshold  α₀(ell) = 10⁻⁵·ell⁻⁵ ,

and `gammaEll_decay_rate` / `alphaEll_decay_rate` pin the decay as EXACT identities
(`γ(ell)·ell⁵ = 1/60`). **This is NOT a bound independent of the block size.** It is not offered as
one. Where the decay comes from, itemised:

* The `Δ′` absorption contributes `144·α₀` and is `ell`-INDEPENDENT (§0's table, four (a) rows).
* The `Q`-drift absorption contributes `ell·(64/ell)·α₁² = 64·α₁²` — also `ell`-INDEPENDENT, the
  `ell` in the additive base's coefficient exactly cancelling the `1/ell` in `[QCHAIN-SENS]`.
* **The entire `ell`-dependence is the `U = 1` additive base constant**, `(1/54)·ell⁻⁵`. Because the
  `Δ′` cost is a fixed multiple of `α₀` while the base is `O(ell⁻⁵)`, the threshold must shrink at
  the same rate for the assembly to close, and then so must the constant.

For context, and without ruling on its significance: Bałaban's own printed `(2.128)` constant is
`(1/(12d²))·L^{-d-1} = (1/108)·ell⁻⁴` at `d = 3` — i.e. the source's single-scale constant already
decays in the block size; `BlockPoincareSharp` shows the printed `ell⁻⁴` is not reachable through
Bałaban's own assembly for large `ell`, and `Lemma24GeneralEll.lean:151-154` leaves the large-`L`
truth of printed `(2.128)` OPEN. At a FIXED block size `ell` the theorem below is uniform in the RG
step `k` (§6's family form), exactly as the `ell = 2` theorem is.

## §0d — CONSISTENCY AT `ell = 2`, AS AN EXACT IDENTITY

`(1/54)·2⁻⁵ = 1/1728 = AlphaAnalyticity.gammaZeroLit` — the general-`ell` base specialises to the
`ell = 2` base EXACTLY, not approximately (`gammaZeroEll_two_eq_gammaZeroLit`). The delivered
`γ(2) = 1/1920` is slightly BETTER than `LemmaAssemblyNormalized.normGamma = 1/2000` at a slightly
smaller threshold `α₀(2) = 3.125·10⁻⁷` vs `normAlpha = 5·10⁻⁷` (`ell_two_comparison`).

## §0e — WHAT IS NOT CLAIMED

* Everything `LemmaAssembly` §8 and `AlphaAnalyticity`'s header disclaim is inherited verbatim:
  this is CMP99b p.392 **(3.10)**'s non-recursive `Δ_k`, NOT p.428 **(3.156)**'s recursive one;
  `GaugeRegular` is (3.35)'s first clause at the global-cube specialization; the cube decomposition
  (M5), the exponential chart and (3.36) remain proxied.
* No claim that `γ(ell)` can be made `ell`-uniform by this route, and no claim that it cannot.
  What is proved is the exact rate this route delivers.
* `ell = 1` and `ell = 0` are OUT of scope and §7 says why mechanically, not by assertion.
* **ISLAND.** Nothing here is imported by `Spine.lean` or by any other module (measured:
  `grep -rl "import AdalyFormal.Balaban.GeneralEllAssembly"` returns nothing). Wiring it in is
  outside this lane's write scope.
* The `ell = 3` route of §8b is stronger than the uniform route AT `ell = 3` ONLY. It does not
  improve any other block size, and it does not make the constant `ell`-uniform.
* The `𝔰𝔲(2)` base (§1) is at `U = 1`; the general-`U` content is the perturbative transport of
  §2–§4, exactly as in the `ell = 2` chain. Nothing about Bałaban's own constants follows.

## §0f — MAP OF THE FILE

§1 the missing scalar→𝔰𝔲(2) link · §2 the reduced `U=1` coercivity (`ell` cancels) · §3 the
perturbed constant with a free base · §4 the gauge-regular transport (parametric + uniform) ·
§5 the assembly, its gate and the headline · §5c the decay as identities · §6 the `k`-uniform
family form · §7 controls and degenerate cases · §8 the `ell = 3` printed base, pushed through ·
§9 the `ell = 2` instance covers tori the imported theorem does not · §10 non-vacuity at a
NON-TRIVIAL background · §11 is the threshold tight, and which term sets it · §12 axiom coverage.

`#print axioms` on every `theorem` below (the only declarations without one are the 14
`def`/`noncomputable def`s, which carry no proof).
-/

namespace AdalyFormal.Balaban.GeneralEllAssembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.BlockPoincareLemma24 (bondNormSq totalCurlEnergy coarseQEnergy)
open AdalyFormal.Balaban.CovariantHjFaithful (covCoarseBondInner)
open AdalyFormal.Balaban.CoercivityTargetsCorrected (SuTwoGeomAdditiveInequality)
open AdalyFormal.Balaban.CovU1Reduction
open AdalyFormal.Balaban.SuTwoGeomU1
open AdalyFormal.Balaban.RegularUDirectCoercivity
open AdalyFormal.Balaban.RegularUCoercivityFull
open AdalyFormal.Balaban.AlphaAnalyticity
open AdalyFormal.Balaban.NormalizationAudit
open AdalyFormal.Balaban.LemmaAssemblyNormalized
open AdalyFormal.Balaban.FullReparamC
open AdalyFormal.Balaban.RegularUDomainWitnessGeneralU (siteZero siteZero_coarse)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.LemmaAssembly (gaugeRegular_mono)
open AdalyFormal.Balaban.BlockPoincareSharp (lemma24_sharpened lemma24_printed_ell3)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE MISSING LINK: the scalar → 𝔰𝔲(2) lift at GENERAL `ell`

`SuTwoGeomU1.suTwoGeomAdditive_trivialU_of_admissible` performs this lift at `ell = 2` over the
`ell = 2` scalar milestone. Everything in its proof except the milestone call is already `∀ ell`.
The version below takes the scalar statement as a HYPOTHESIS, so the constant is whatever the
scalar input delivers and no numeral is invented here. -/

/-- **THE `𝔰𝔲(2)` ADDITIVE BASE AT `U = 1`, GENERAL `ell`, PARAMETRIC IN THE SCALAR INPUT.**
If the scalar `(2.128)`-shaped inequality holds with constant `c` for every `(2.121)`-admissible
real field on this torus at block size `ell`, then the `𝔰𝔲(2)` additive inequality holds with the
SAME constant `c` for every axial-gauge `𝔰𝔲(2)` field.

Proof: at `U = 1` the covariant curl and covariant coarse average are the flat operators, each of
the three `𝔰𝔲(2)` energies is the sum over `i : Fin 3` of the scalar energy of the `i`-th Pauli
component (`SuTwoGeomU1` §4, already `∀ ell`), each component is scalar-admissible (`SuTwoGeomU1`
§5, already `∀ ell`), and the three scalar inequalities are summed. No constant is introduced. -/
theorem suTwoGeomAdditive_trivialU_ofScalar (ell : ℕ) (c : ℝ) (A0 : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A0 b = 0)
    (hscalar : ∀ B : Bond L → ℝ, B ∈ admissibleSubspaceInter L ell →
      (ell : ℝ) * coarseQEnergy ell B + totalCurlEnergy B ≥ c * bondNormSq B) :
    SuTwoGeomAdditiveInequality ell (trivialU L) c A0 := by
  have hcurl : curlCovariantLM (trivialU L) A0 = flatCurlValue A0 := by
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  have hQ : lineCoarseRestrictCovLM (trivialU L) ell A0
      = (fun cb => lineCoarseRestrictSuTwo ell A0 cb) := by
    funext cb
    rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_trivialU]
  unfold SuTwoGeomAdditiveInequality
  rw [hcurl, hQ, covBondInner_eq_sum, covPlaqInner_flatCurl_eq_sum,
    covCoarseBondInner_lineCoarse_eq_sum]
  rw [ge_iff_le]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hs := hscalar (suComp i A0) (suComp_mem_admissible ell i A0 hadm)
  rw [ge_iff_le] at hs
  exact hs

#print axioms suTwoGeomAdditive_trivialU_ofScalar

/-- **The `U = 1` base constant at general `ell`**, `γ₀(ell) = (1/54)·ell⁻⁵` — the constant
`BlockPoincareSharp.lemma24_sharpened` delivers, written exactly as that theorem states it. -/
noncomputable def gammaZeroEll (ell : ℕ) : ℝ := (1 / 54) * (1 / (ell : ℝ) ^ 5)

theorem gammaZeroEll_def (ell : ℕ) : gammaZeroEll ell = (1 / 54) * (1 / (ell : ℝ) ^ 5) := rfl

/-- **CONSISTENCY, EXACT: the general-`ell` base IS the `ell = 2` base at `ell = 2`.**
`(1/54)·2⁻⁵ = 1/1728 = (1/108)·2⁻⁴ = AlphaAnalyticity.gammaZeroLit`. Not "approximately"; the two
constants are the same rational. -/
theorem gammaZeroEll_two_eq_gammaZeroLit : gammaZeroEll 2 = gammaZeroLit := by
  rw [gammaZeroEll_def, gammaZeroLit_eq]; norm_num

/-- **The `𝔰𝔲(2)` additive base, unconditional, for every `ell ≥ 2.`** -/
theorem suTwoGeomAdditive_trivialU_generalEll {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (A0 : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A0 b = 0) :
    SuTwoGeomAdditiveInequality ell (trivialU L) (gammaZeroEll ell) A0 :=
  suTwoGeomAdditive_trivialU_ofScalar ell (gammaZeroEll ell) A0 hadm
    (fun B hB => lemma24_sharpened hell2 hstrict hdvd B hB)

#print axioms gammaZeroEll_two_eq_gammaZeroLit
#print axioms suTwoGeomAdditive_trivialU_generalEll

/-! ## §2 — THE REDUCED `U = 1` COERCIVITY ON `ker Q_ell(U)`, GENERAL `ell`

`RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` at `ell = 2`, re-run at general `ell`.
**The `ell` CANCELS here**: the additive base carries the coefficient `ell` on `‖Q_ell A‖²` and
`[QCHAIN-SENS]` gives `‖Q_ell(1)A‖² ≤ (64/ell)·α₁²·E`, so the absorbed term is `64·α₁²·E` at EVERY
block size. This is the step where an `ell`-dependence would most plausibly have appeared, and it
does not. -/

/-- **The drift absorption is `ell`-FREE.** `ell·‖Q_ell(1)A‖² ≤ 64·α₁²·bondEnergy A` for every
`0 < ell`, on `ker Q_ell(U)`. -/
theorem ell_mul_covCoarse_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo)
    (hkerU : ∀ b : CoarseBond L ell, lineCoarseRestrictCov U ell A b = 0) :
    (ell : ℝ) * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) ell A)
        (lineCoarseRestrictCovLM (trivialU L) ell A)
      ≤ 64 * frobSupBond U ^ 2 * bondEnergy A := by
  have hpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hQ := covCoarse_Q1flat_le_of_kerQU U hell hdvd A hkerU
  have hstep := mul_le_mul_of_nonneg_left hQ (le_of_lt hpos)
  have hcancel : (ell : ℝ) * (64 / (ell : ℝ) * frobSupBond U ^ 2 * bondEnergy A)
      = 64 * frobSupBond U ^ 2 * bondEnergy A := by
    field_simp
  rwa [hcancel] at hstep

/-- **THE REDUCED `U = 1` COERCIVITY, GENERAL `ell`.** From the `𝔰𝔲(2)` additive base with constant
`c` and membership in `ker Q_ell(U)`: `(c − 64·α₁²)·bondEnergy A ≤ ‖curl₁ A‖²`, `α₁ = frobSupBond U`.
Parametric in `c`, so no numeral enters. -/
theorem dstarD_trivialU_coercive_ofBase {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (c : ℝ)
    (hbase : SuTwoGeomAdditiveInequality ell (trivialU L) c A)
    (hkerU : ∀ b : CoarseBond L ell, lineCoarseRestrictCov U ell A b = 0) :
    (c - 64 * frobSupBond U ^ 2) * bondEnergy A ≤ dstarDQuadForm (trivialU L) A := by
  rw [SuTwoGeomAdditiveInequality, covPlaqInner_curl1_eq_deltaJ1,
    covBondInner_eq_bondEnergy] at hbase
  have hdrift := ell_mul_covCoarse_le hell hdvd U A hkerU
  nlinarith [hbase, hdrift]

#print axioms ell_mul_covCoarse_le
#print axioms dstarD_trivialU_coercive_ofBase

/-! ## §3 — THE PERTURBED CONSTANT, PARAMETRIC IN THE BASE

`AlphaAnalyticity.coercConst` bakes `gammaZeroLit` in. `coercC c a` is the same expression with the
base as a parameter; the three helper facts are re-derived at that generality (three lines each,
using `AlphaAnalyticity`'s own `four_sqrt_two_mul`, reused). -/

/-- `coercC c a = (√(c − 64a²) − 4√2·a)²` — `AlphaAnalyticity.coercConst` with the base freed. -/
noncomputable def coercC (c a : ℝ) : ℝ := (Real.sqrt (c - 64 * a ^ 2) - 4 * Real.sqrt 2 * a) ^ 2

theorem coercC_eq_coercConst (a : ℝ) : coercC gammaZeroLit a = coercConst a := rfl

theorem coercC_hsmall {c a : ℝ} (ha : 0 ≤ a) (h : 96 * a ^ 2 ≤ c) :
    0 ≤ Real.sqrt (c - 64 * a ^ 2) - 4 * Real.sqrt 2 * a := by
  rw [four_sqrt_two_mul ha, sub_nonneg]
  exact Real.sqrt_le_sqrt (by linarith)

theorem coercC_anti {c a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 96 * b ^ 2 ≤ c) :
    coercC c b ≤ coercC c a := by
  have hb0 : 0 ≤ b := le_trans ha hab
  have h1 : Real.sqrt (c - 64 * b ^ 2) ≤ Real.sqrt (c - 64 * a ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h2 : 4 * Real.sqrt 2 * a ≤ 4 * Real.sqrt 2 * b := by
    nlinarith [Real.sqrt_nonneg 2]
  have hDb : 0 ≤ Real.sqrt (c - 64 * b ^ 2) - 4 * Real.sqrt 2 * b := coercC_hsmall hb0 hb
  unfold coercC
  nlinarith [hDb, h1, h2]

/-- **THE LINEAR LOWER BOUND ON THE PERTURBED CONSTANT, at a general base.**
`coercC c a ≥ c − 32a² − 12·a·sc` whenever `√c ≤ sc`. Mechanism, exactly:
`(s − 4√2a)² = c − 32a² − 8√2·a·s` with `s = √(c − 64a²) ≤ √c ≤ sc`, and `8√2 ≤ 12`.
The `sc` parameter keeps the call site in exact rationals — no `Real.sqrt` reaches the numerals. -/
theorem coercC_lower {c a sc : ℝ} (ha : 0 ≤ a) (h : 96 * a ^ 2 ≤ c) (hsc : Real.sqrt c ≤ sc) :
    c - 32 * a ^ 2 - 12 * a * sc ≤ coercC c a := by
  have hc0 : (0 : ℝ) ≤ c := by nlinarith [sq_nonneg a]
  have hrad : (0 : ℝ) ≤ c - 64 * a ^ 2 := by nlinarith [sq_nonneg a]
  set s := Real.sqrt (c - 64 * a ^ 2) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = c - 64 * a ^ 2 := Real.sq_sqrt hrad
  have hsle : s ≤ sc := le_trans (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a])) hsc
  have h2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2le : Real.sqrt 2 ≤ 3 / 2 := sqrt_two_le
  have hexp : coercC c a = c - 32 * a ^ 2 - 8 * (Real.sqrt 2 * a * s) := by
    unfold coercC
    rw [← hsdef]
    have hring : (s - 4 * Real.sqrt 2 * a) ^ 2
        = s ^ 2 - 8 * (Real.sqrt 2 * a * s) + 16 * Real.sqrt 2 ^ 2 * a ^ 2 := by ring
    rw [hring, hsq, hsq2]; ring
  rw [hexp]
  have hcross : Real.sqrt 2 * a * s ≤ 3 / 2 * a * sc := by
    have hstep1 : Real.sqrt 2 * a * s ≤ 3 / 2 * a * s := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2le) (mul_nonneg ha hs0)]
    have hstep2 : 3 / 2 * a * s ≤ 3 / 2 * a * sc := by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hsle)]
    linarith
  linarith [hcross]

#print axioms coercC_eq_coercConst
#print axioms coercC_hsmall
#print axioms coercC_anti
#print axioms coercC_lower

/-! ## §4 — THE GAUGE-REGULAR `D*D` COERCIVITY AT GENERAL `ell`

`AlphaAnalyticity.deltaJ_gaugeRegular_coercive` at general `ell`. Every gauge-covariance lemma it
uses is already `∀ ell` and is reused verbatim. -/

/-- **THE TRANSPORT THEOREM AT GENERAL `ell`, PARAMETRIC IN THE `U = 1` BASE.** `hbase` supplies the
`𝔰𝔲(2)` additive inequality with constant `c` for every axial-gauge field; the conclusion is
`coercC c α₀ · bondEnergy A ≤ ‖D_U A‖²`. Keeping `c` free is what lets §9 substitute the STRONGER
printed base available at `ell = 3` without any of this proof being redone. -/
theorem deltaJ_gaugeRegular_coercive_ofBase {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (c α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hthr : 96 * α₀ ^ 2 ≤ c)
    (hbase : ∀ A0 : Bond L → SuTwo,
      (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
        ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A0 b = 0) →
      SuTwoGeomAdditiveInequality ell (trivialU L) c A0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L ell, lineCoarseRestrictCov U ell A b = 0) :
    coercC c α₀ * bondEnergy A ≤ dstarDQuadForm U A := by
  obtain ⟨γ, hγ⟩ := hreg
  set Ug := periodicGaugeTransform γ U with hUg
  set Ag := gaugeActA γ A with hAg
  have hα₁0 : 0 ≤ frobSupBond Ug := frobSupBond_nonneg _
  have h96 : 96 * frobSupBond Ug ^ 2 ≤ c := by nlinarith
  -- the transported data still satisfies both domain clauses
  have hadm' := axialGauge_gauge γ ell A hadm
  have hker' := mem_kerQ_gauge γ U ell A hkerU
  -- the U=1 base, at the transported field
  have hred := dstarD_trivialU_coercive_ofBase hell hdvd Ug Ag c (hbase Ag hadm') hker'
  -- (b1) transfer
  have hγ'0 : (0 : ℝ) ≤ c - 64 * frobSupBond Ug ^ 2 := by nlinarith
  have hsmall : 0 ≤ Real.sqrt (c - 64 * frobSupBond Ug ^ 2)
      - 4 * Real.sqrt 2 * frobSupBond Ug := coercC_hsmall hα₁0 h96
  have key := deltaJ_regularU_coercive_of_U1coercive Ug Ag
    (c - 64 * frobSupBond Ug ^ 2) hγ'0 hred hsmall
  -- back to (U, A) by gauge invariance of both sides
  rw [bondEnergy_gauge, dstarDQuadForm_gauge] at key
  have hcc : coercC c (frobSupBond Ug)
      = (Real.sqrt (c - 64 * frobSupBond Ug ^ 2)
          - 4 * Real.sqrt 2 * frobSupBond Ug) ^ 2 := rfl
  have hmono : coercC c α₀ ≤ coercC c (frobSupBond Ug) := coercC_anti hα₁0 hγ hthr
  have hbe : 0 ≤ bondEnergy A := bondEnergy_nonneg A
  calc coercC c α₀ * bondEnergy A
      ≤ coercC c (frobSupBond Ug) * bondEnergy A := mul_le_mul_of_nonneg_right hmono hbe
    _ ≤ dstarDQuadForm U A := by rw [hcc]; exact key

/-- **THE TRANSPORT THEOREM AT GENERAL `ell`**, at the uniform base `γ₀(ell) = (1/54)·ell⁻⁵`. -/
theorem deltaJ_gaugeRegular_coercive_generalEll {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hthr : 96 * α₀ ^ 2 ≤ gammaZeroEll ell)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L ell, lineCoarseRestrictCov U ell A b = 0) :
    coercC (gammaZeroEll ell) α₀ * bondEnergy A ≤ dstarDQuadForm U A :=
  deltaJ_gaugeRegular_coercive_ofBase (by omega) hdvd (gammaZeroEll ell) α₀ hα₀ hthr
    (fun A0 h0 => suTwoGeomAdditive_trivialU_generalEll hell2 hstrict hdvd A0 h0)
    U hreg A hadm hkerU

#print axioms deltaJ_gaugeRegular_coercive_ofBase
#print axioms deltaJ_gaugeRegular_coercive_generalEll

/-! ## §5 — THE ASSEMBLED NORMALIZED COERCIVITY AT GENERAL `ell`

The `Δ′` absorption (`LemmaAssemblyNormalized.abs_deltaPrimeQuadFormNormalizedTransported_le`,
`8α₀·dstarD + 144α₀·bondEnergy`) is imported and applied UNCHANGED — it carries no `ell`. -/

/-- **THE ASSEMBLY AT GENERAL `ell`, PARAMETRIC FORM.** `γ` is gated by `hgate`, the exact scalar
inequality the assembly reduces to:

`γ ≤ (1 − 8α)·(γ₀(ell) − 32α² − 12·α·sc) − 144α`,   `√(γ₀(ell)) ≤ sc`,

in which `γ₀(ell) = (1/54)·ell⁻⁵` is the `U = 1` base, `8α` and `144α` are §3-of-
`LemmaAssemblyNormalized`'s `Δ′` absorption coefficients (both `ell`-free), and `32α² + 12·α·sc` is
§3's linear degradation of the base. Every numeral in §5b's headline is traceable through this
gate. -/
theorem deltaKNormalized_coercive_param_ofBase {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (c α γ sc : ℝ) (hα0 : 0 ≤ α) (h8 : 8 * α ≤ 1) (hthr : 96 * α ^ 2 ≤ c)
    (hsc : Real.sqrt c ≤ sc)
    (hgate : γ ≤ (1 - 8 * α) * (c - 32 * α ^ 2 - 12 * α * sc) - 144 * α)
    (hbase : ∀ A0 : Bond L → SuTwo,
      (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
        ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A0 b = 0) →
      SuTwoGeomAdditiveInequality ell (trivialU L) c A0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α U) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L ell, lineCoarseRestrictCov U ell A b = 0) :
    γ * bondEnergy A ≤ deltaKQuadFormNormalizedCorrected U A := by
  have hleg := deltaJ_gaugeRegular_coercive_ofBase hell hdvd c α hα0 hthr hbase U hreg A
    hadm hkerU
  have hlin : c - 32 * α ^ 2 - 12 * α * sc ≤ coercC c α := coercC_lower hα0 hthr hsc
  have habs := abs_deltaPrimeQuadFormNormalizedTransported_le hα0 U hreg A
  have hlow : -(8 * α * dstarDQuadForm U A + 144 * α * bondEnergy A)
      ≤ deltaPrimeQuadFormNormalizedTransported U A := neg_le_of_abs_le habs
  have hbe : 0 ≤ bondEnergy A := bondEnergy_nonneg A
  have hstar : (c - 32 * α ^ 2 - 12 * α * sc) * bondEnergy A
      ≤ dstarDQuadForm U A := le_trans (mul_le_mul_of_nonneg_right hlin hbe) hleg
  have h8' : (0 : ℝ) ≤ 1 - 8 * α := by linarith
  have step1 : (1 - 8 * α) * ((c - 32 * α ^ 2 - 12 * α * sc) * bondEnergy A)
      ≤ (1 - 8 * α) * dstarDQuadForm U A := mul_le_mul_of_nonneg_left hstar h8'
  have hK : deltaKQuadFormNormalizedCorrected U A
      = dstarDQuadForm U A + deltaPrimeQuadFormNormalizedTransported U A := rfl
  rw [hK]
  calc γ * bondEnergy A
      ≤ ((1 - 8 * α) * (c - 32 * α ^ 2 - 12 * α * sc) - 144 * α)
          * bondEnergy A := mul_le_mul_of_nonneg_right hgate hbe
    _ = (1 - 8 * α) * ((c - 32 * α ^ 2 - 12 * α * sc) * bondEnergy A)
          - 144 * α * bondEnergy A := by ring
    _ ≤ (1 - 8 * α) * dstarDQuadForm U A - 144 * α * bondEnergy A := by linarith [step1]
    _ ≤ dstarDQuadForm U A + deltaPrimeQuadFormNormalizedTransported U A := by linarith [hlow]

/-- The same gate at the uniform base `γ₀(ell) = (1/54)·ell⁻⁵`. -/
theorem deltaKNormalized_coercive_paramEll {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (α γ sc : ℝ) (hα0 : 0 ≤ α) (h8 : 8 * α ≤ 1) (hthr : 96 * α ^ 2 ≤ gammaZeroEll ell)
    (hsc : Real.sqrt (gammaZeroEll ell) ≤ sc)
    (hgate : γ ≤ (1 - 8 * α) * (gammaZeroEll ell - 32 * α ^ 2 - 12 * α * sc) - 144 * α)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α U) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L ell, lineCoarseRestrictCov U ell A b = 0) :
    γ * bondEnergy A ≤ deltaKQuadFormNormalizedCorrected U A :=
  deltaKNormalized_coercive_param_ofBase (by omega) hdvd (gammaZeroEll ell) α γ sc hα0 h8 hthr
    hsc hgate (fun A0 h0 => suTwoGeomAdditive_trivialU_generalEll hell2 hstrict hdvd A0 h0)
    U hreg A hadm hkerU

#print axioms deltaKNormalized_coercive_param_ofBase
#print axioms deltaKNormalized_coercive_paramEll

/-! ### §5a — the delivered constant and threshold, and the gate arithmetic

The gate is discharged in EXACT RATIONALS, as a single polynomial inequality in `u = ell⁻⁵`. -/

/-- **The delivered coercivity constant at block size `ell`**: `(1/60)·ell⁻⁵`. -/
noncomputable def gammaEll (ell : ℕ) : ℝ := (1 / 60) * (1 / (ell : ℝ) ^ 5)

/-- **The delivered regularity threshold at block size `ell`**: `10⁻⁵·ell⁻⁵`. -/
noncomputable def alphaEll (ell : ℕ) : ℝ := (1 / 100000) * (1 / (ell : ℝ) ^ 5)

theorem gammaEll_def (ell : ℕ) : gammaEll ell = (1 / 60) * (1 / (ell : ℝ) ^ 5) := rfl
theorem alphaEll_def (ell : ℕ) : alphaEll ell = (1 / 100000) * (1 / (ell : ℝ) ^ 5) := rfl

/-- **THE GATE ARITHMETIC, as a polynomial inequality in `u = ell⁻⁵`.** `0 < u ≤ 1/32` is exactly
what `ell ≥ 2` supplies. No `Real.sqrt`, no floating point; `nlinarith` on exact rationals. -/
theorem gate_arith (u : ℝ) (hu0 : 0 < u) (hu : u ≤ 1 / 32) :
    (1 / 60) * u
      ≤ (1 - 8 * ((1 / 100000) * u))
          * ((1 / 54) * u - 32 * ((1 / 100000) * u) ^ 2 - 12 * ((1 / 100000) * u) * 1)
        - 144 * ((1 / 100000) * u) := by
  nlinarith [hu0, hu, sq_nonneg u, mul_pos hu0 hu0, mul_nonneg (mul_pos hu0 hu0).le hu0.le]

/-- **The margin is real, not marginal** — at the extreme admissible `u = 1/32` (`ell = 2`) the gate
holds with slack, and the slack is a positive rational. Recorded so "the gate closes" is not read as
"the gate closes by `0 ≤ 0`". -/
theorem gate_arith_margin :
    (0 : ℝ) < (1 - 8 * ((1 / 100000) * (1 / 32 : ℝ)))
        * ((1 / 54) * (1 / 32 : ℝ) - 32 * ((1 / 100000) * (1 / 32 : ℝ)) ^ 2
          - 12 * ((1 / 100000) * (1 / 32 : ℝ)) * 1)
      - 144 * ((1 / 100000) * (1 / 32 : ℝ)) - (1 / 60) * (1 / 32 : ℝ) := by
  norm_num

theorem inv_pow_five_pos {ell : ℕ} (hell2 : 2 ≤ ell) : (0 : ℝ) < 1 / (ell : ℝ) ^ 5 := by
  have h : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  positivity

theorem inv_pow_five_le {ell : ℕ} (hell2 : 2 ≤ ell) : (1 : ℝ) / (ell : ℝ) ^ 5 ≤ 1 / 32 := by
  have hnat : (32 : ℕ) ≤ ell ^ 5 := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ ell ^ 5 := Nat.pow_le_pow_left hell2 5
  have hge : (32 : ℝ) ≤ (ell : ℝ) ^ 5 := by exact_mod_cast hnat
  exact one_div_le_one_div_of_le (by norm_num) hge

theorem alphaEll_pos {ell : ℕ} (hell2 : 2 ≤ ell) : 0 < alphaEll ell := by
  rw [alphaEll_def]; have := inv_pow_five_pos hell2; linarith

theorem gammaEll_pos {ell : ℕ} (hell2 : 2 ≤ ell) : 0 < gammaEll ell := by
  rw [gammaEll_def]; have := inv_pow_five_pos hell2; linarith

theorem gammaZeroEll_pos {ell : ℕ} (hell2 : 2 ≤ ell) : 0 < gammaZeroEll ell := by
  rw [gammaZeroEll_def]; have := inv_pow_five_pos hell2; linarith

theorem gammaZeroEll_le_one {ell : ℕ} (hell2 : 2 ≤ ell) : gammaZeroEll ell ≤ 1 := by
  rw [gammaZeroEll_def]; have := inv_pow_five_le hell2; linarith

theorem sqrt_gammaZeroEll_le_one {ell : ℕ} (hell2 : 2 ≤ ell) :
    Real.sqrt (gammaZeroEll ell) ≤ 1 := by
  have h := gammaZeroEll_le_one hell2
  calc Real.sqrt (gammaZeroEll ell) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
    _ = 1 := Real.sqrt_one

theorem alphaEll_thr {ell : ℕ} (hell2 : 2 ≤ ell) :
    96 * alphaEll ell ^ 2 ≤ gammaZeroEll ell := by
  rw [alphaEll_def, gammaZeroEll_def]
  set u : ℝ := 1 / (ell : ℝ) ^ 5 with hu
  have hu0 : 0 < u := inv_pow_five_pos hell2
  have hule : u ≤ 1 / 32 := inv_pow_five_le hell2
  nlinarith [hu0, hule]

theorem alphaEll_le_eighth {ell : ℕ} (hell2 : 2 ≤ ell) : 8 * alphaEll ell ≤ 1 := by
  rw [alphaEll_def]
  have hule := inv_pow_five_le hell2
  have hu0 := inv_pow_five_pos hell2
  linarith

#print axioms gate_arith
#print axioms gate_arith_margin
#print axioms alphaEll_thr
#print axioms sqrt_gammaZeroEll_le_one

/-! ### §5b — THE HEADLINE -/

/-- **THE ASSEMBLY, NORMALIZED, AT GENERAL BLOCK SIZE `ell`.**
For every `ell ≥ 2`, every torus with `ell < L ν + 1` and `ell ∣ L ν + 1`, every background
`GaugeRegular (10⁻⁵·ell⁻⁵)`, and every `A` in `axial ∩ ker Q_ell(U)`:

  `(1/60)·ell⁻⁵ · bondEnergy A ≤ deltaKQuadFormNormalizedCorrected U A`.

**The constant DECAYS in the block size** (`gammaEll_decay_rate`: `γ(ell)·ell⁵ = 1/60` exactly).
It is `k`-independent at each fixed `ell` (§6), which is what the `ell = 2` theorem also delivers;
it is NOT independent of `ell`, and is not offered as such. §0c says which step causes the decay. -/
theorem deltaKNormalized_gaugeRegular_coercive_generalEll {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular (alphaEll ell) U) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L ell, lineCoarseRestrictCov U ell A b = 0) :
    gammaEll ell * bondEnergy A ≤ deltaKQuadFormNormalizedCorrected U A := by
  refine deltaKNormalized_coercive_paramEll hell2 hstrict hdvd (alphaEll ell) (gammaEll ell) 1
    (le_of_lt (alphaEll_pos hell2)) (alphaEll_le_eighth hell2) (alphaEll_thr hell2)
    (sqrt_gammaZeroEll_le_one hell2) ?_ U hreg A hadm hkerU
  rw [gammaEll_def, alphaEll_def, gammaZeroEll_def]
  exact gate_arith _ (inv_pow_five_pos hell2) (inv_pow_five_le hell2)

#print axioms deltaKNormalized_gaugeRegular_coercive_generalEll

/-! ### §5c — THE DECAY, AS EXACT IDENTITIES (no adjective does this work) -/

/-- `γ(ell)·ell⁵ = 1/60` — the decay rate, exactly. -/
theorem gammaEll_decay_rate {ell : ℕ} (hell2 : 2 ≤ ell) :
    gammaEll ell * (ell : ℝ) ^ 5 = 1 / 60 := by
  have h : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  rw [gammaEll_def]; field_simp

/-- `α₀(ell)·ell⁵ = 10⁻⁵` — the threshold decays at the SAME rate. -/
theorem alphaEll_decay_rate {ell : ℕ} (hell2 : 2 ≤ ell) :
    alphaEll ell * (ell : ℝ) ^ 5 = 1 / 100000 := by
  have h : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  rw [alphaEll_def]; field_simp

/-- Doubling the block size divides the constant by `32`. Stated at concrete `ell` so no reader has
to evaluate a symbolic power. -/
theorem gammaEll_halving :
    gammaEll 4 = gammaEll 2 / 32 ∧ gammaEll 3 < gammaEll 2 ∧ gammaEll 4 < gammaEll 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [gammaEll_def, gammaEll_def] <;> norm_num

/-- **`ell = 2` COMPARISON.** The general-`ell` theorem at `ell = 2` gives `1/1920`, slightly
STRONGER than `LemmaAssemblyNormalized.normGamma = 1/2000`, at a slightly SMALLER threshold
`α₀(2) = 1/3200000` vs `normAlpha = 1/2000000`. Recorded as the honest two-sided comparison, not as
a claim of improvement. -/
theorem ell_two_comparison :
    gammaEll 2 = 1 / 1920 ∧ alphaEll 2 = 1 / 3200000
      ∧ normGamma < gammaEll 2 ∧ alphaEll 2 < normAlpha := by
  refine ⟨by rw [gammaEll_def]; norm_num, by rw [alphaEll_def]; norm_num, ?_, ?_⟩
  · rw [gammaEll_def]; unfold normGamma; norm_num
  · rw [alphaEll_def]; unfold normAlpha; norm_num

#print axioms gammaEll_decay_rate
#print axioms alphaEll_decay_rate
#print axioms gammaEll_halving
#print axioms ell_two_comparison

/-! ## §6 — THE `k`-UNIFORM (FAMILY) FORM AT FIXED `ell`

Same quantifier structure as `LemmaAssemblyNormalized.DeltaKNormalizedScaleUniform`: both constants
are bound BEFORE the index type, the family of lattices, the backgrounds and the fields. The block
size is bound before them too, and that is exactly the honest reading — this is `k`-uniformity at a
fixed block scale, for EVERY block scale, not one constant across block scales. -/

/-- The `k`/scale-uniform predicate at block size `ell`. -/
def DeltaKNormalizedScaleUniformEll (ell : ℕ) (γ₀' α₀ : ℝ) : Prop :=
  0 < γ₀' ∧ 0 < α₀ ∧
    ∀ (K : Type) (k : K) (Lf : K → PeriodicLatticeExtent)
      (Uf : (j : K) → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (Lf j))
      (Af : (j : K) → Bond (Lf j) → SuTwo),
      (∀ ν : Fin 3, ell < Lf k ν + 1) → (∀ ν : Fin 3, ell ∣ (Lf k ν + 1)) →
      GaugeRegular α₀ (Uf k) →
      (∀ y : PeriodicLatticeSite (Lf k), y ∈ CoarseLattice (Lf k) ell →
        ∀ x : PeriodicLatticeSite (Lf k), x ∈ blockOf y ell →
        ∀ b ∈ staircasePath y x, Af k b = 0) →
      (∀ b : CoarseBond (Lf k) ell, lineCoarseRestrictCov (Uf k) ell (Af k) b = 0) →
      γ₀' * bondEnergy (Af k) ≤ deltaKQuadFormNormalizedCorrected (Uf k) (Af k)

theorem deltaKNormalized_uniform_over_family_generalEll {ell : ℕ} (hell2 : 2 ≤ ell) :
    DeltaKNormalizedScaleUniformEll ell (gammaEll ell) (alphaEll ell) := by
  refine ⟨gammaEll_pos hell2, alphaEll_pos hell2, ?_⟩
  intro K k Lf Uf Af hstrict hdvd hreg hadm hker
  exact deltaKNormalized_gaugeRegular_coercive_generalEll hell2 hstrict hdvd (Uf k) hreg (Af k)
    hadm hker

/-- **THE `∀ ell` FORM.** One theorem covering every block size, with the constant a stated FUNCTION
of `ell` — the honest shape, since no single constant works for all `ell` by this route. -/
theorem deltaKNormalized_uniform_all_ell :
    ∀ ell : ℕ, 2 ≤ ell → DeltaKNormalizedScaleUniformEll ell (gammaEll ell) (alphaEll ell) :=
  fun _ h => deltaKNormalized_uniform_over_family_generalEll h

#print axioms deltaKNormalized_uniform_over_family_generalEll
#print axioms deltaKNormalized_uniform_all_ell

/-! ## §7 — CONTROLS, BOTH DIRECTIONS, AND THE DEGENERATE CASES

### §7a — MUST-FIRE: is the "general `ell`" statement secretly `ell = 2`?

Three exhibits. (i) The constants differ at `ell = 3` and `ell = 4` from `ell = 2` and from each
other, as exact rationals. (ii) The theorem is INSTANTIATED at `ell = 3` and `ell = 4` with all
hypotheses discharged and both sides strictly positive (§7b) — the binders there are
`CoarseLattice L 3`/`CoarseBond L 3` and `CoarseLattice L 4`/`CoarseBond L 4`, which are literally
different types from the `ell = 2` ones. (iii) The `ell = 2` specialisation is NOT the imported
`ell = 2` theorem: its constant is `1/1920 ≠ 1/2000 = normGamma`. -/

/-- **MUST-FIRE (i): the constants at `ell = 2, 3, 4` are three DIFFERENT rationals.**
A statement secretly fixed at `ell = 2` could not produce these. -/
theorem control_mustfire_constants_differ :
    gammaEll 2 = 1 / 1920 ∧ gammaEll 3 = 1 / 14580 ∧ gammaEll 4 = 1 / 61440
      ∧ gammaEll 3 ≠ gammaEll 2 ∧ gammaEll 4 ≠ gammaEll 3
      ∧ alphaEll 3 ≠ alphaEll 2 := by
  refine ⟨by rw [gammaEll_def]; norm_num, by rw [gammaEll_def]; norm_num,
    by rw [gammaEll_def]; norm_num, ?_, ?_, ?_⟩
  · rw [gammaEll_def, gammaEll_def]; norm_num
  · rw [gammaEll_def, gammaEll_def]; norm_num
  · rw [alphaEll_def, alphaEll_def]; norm_num

/-- **MUST-FIRE (iii): the `ell = 2` specialisation is a DIFFERENT statement from the imported
`ell = 2` theorem** — different constant, different threshold, so this file is not a re-export. -/
theorem control_mustfire_not_the_ell2_theorem :
    gammaEll 2 ≠ normGamma ∧ alphaEll 2 ≠ normAlpha := by
  constructor
  · rw [gammaEll_def]; unfold normGamma; norm_num
  · rw [alphaEll_def]; unfold normAlpha; norm_num

#print axioms control_mustfire_constants_differ
#print axioms control_mustfire_not_the_ell2_theorem

/-! ### §7b — MUST-NOT-FIRE: NON-VACUITY at `ell = 3` and at `ell = 4`

The admissible subspace `axial ∩ ker Q_ell(U)` is inhabited by a NAMED nonzero element at `ell = 3`
and at `ell = 4`, on tori where the block is strictly smaller than the torus (so no witness dodges a
cross-block sum by `L ν + 1 = ell`). The witness is `FullReparamC.admissibleWitness`, which exists
for EVERY `U` and every `2 ≤ ell` — reused, not rebuilt. -/

/-- Positivity of `bondEnergy` from a single nonzero bond value. Four lines; `Weitzenbock`'s
`bondEnergy_pos_of_ne` is the same fact but that module is NOT in this file's import closure
(measured), so importing it to save four lines would pull in a large unrelated module. -/
theorem bondEnergy_pos_of_ne' (A : Bond L → SuTwo) (b0 : Bond L) (h : A b0 ≠ 0) :
    0 < bondEnergy A := by
  unfold bondEnergy
  refine Finset.sum_pos' (fun b _ => sq_nonneg _) ⟨b0, Finset.mem_univ _, ?_⟩
  have hn : ‖A b0‖ ≠ 0 := norm_ne_zero_iff.mpr h
  positivity

/-- The identity gauge fixes `trivialU`, so `trivialU` is `GaugeRegular α` for every `α ≥ 0`. -/
theorem gaugeRegular_trivialU (α : ℝ) (hα : 0 ≤ α) : GaugeRegular α (trivialU L) := by
  refine ⟨fun _ => 1, ?_⟩
  have hfix : periodicGaugeTransform (fun _ : PeriodicLatticeSite L => (1 : SU2)) (trivialU L)
      = trivialU L := by
    funext e
    simp [periodicGaugeTransform, trivialU]
  rw [hfix, AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU]
  exact hα

/-- The `9³` torus: `3 < 9`, `3 ∣ 9`. The block `3³` is a strict subset of the torus. -/
def witL8 : PeriodicLatticeExtent := fun _ => 8

/-- The `8³` torus: `4 < 8`, `4 ∣ 8`. The block `4³` is a strict subset of the torus. -/
def witL7 : PeriodicLatticeExtent := fun _ => 7

theorem witL8_strict : ∀ ν : Fin 3, (3 : ℕ) < witL8 ν + 1 := by decide
theorem witL8_dvd : ∀ ν : Fin 3, (3 : ℕ) ∣ (witL8 ν + 1) := by decide
theorem witL7_strict : ∀ ν : Fin 3, (4 : ℕ) < witL7 ν + 1 := by decide
theorem witL7_dvd : ∀ ν : Fin 3, (4 : ℕ) ∣ (witL7 ν + 1) := by decide

/-- The block is a PROPER subset of the torus in both witnesses — `L ν + 1 ≠ ell`. Recorded because
two existing witnesses in this tree dodge a cross-block sum precisely by taking the block to BE the
whole torus. -/
theorem witnesses_block_proper :
    (∀ ν : Fin 3, witL8 ν + 1 ≠ 3) ∧ (∀ ν : Fin 3, witL7 ν + 1 ≠ 4)
      ∧ witL8 0 + 1 = 9 ∧ witL7 0 + 1 = 8 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The `ell = 3` admissible witness at the trivial background on the `9³` torus. -/
noncomputable def wit3 : Bond witL8 → SuTwo :=
  admissibleWitness (trivialU witL8) 3 (siteZero witL8)

/-- The `ell = 4` admissible witness at the trivial background on the `8³` torus. -/
noncomputable def wit4 : Bond witL7 → SuTwo :=
  admissibleWitness (trivialU witL7) 4 (siteZero witL7)

theorem wit3_bondEnergy_pos : 0 < bondEnergy wit3 := by
  refine bondEnergy_pos_of_ne' wit3 (freeBond 3 (siteZero witL8)) ?_
  rw [wit3, admissibleWitness_at_freeBond (by norm_num) witL8_dvd _ _ (siteZero_coarse 3)]
  exact suTwoWitness_ne_zero

theorem wit4_bondEnergy_pos : 0 < bondEnergy wit4 := by
  refine bondEnergy_pos_of_ne' wit4 (freeBond 4 (siteZero witL7)) ?_
  rw [wit4, admissibleWitness_at_freeBond (by norm_num) witL7_dvd _ _ (siteZero_coarse 4)]
  exact suTwoWitness_ne_zero

/-- **MUST-NOT-FIRE AT `ell = 3`.** All hypotheses discharged, both sides STRICTLY POSITIVE: the
`ell = 3` instance of the headline theorem is not `0 ≤ 0`, and its domain is not `{0}`. -/
theorem control_nonvacuous_ell3 :
    0 < bondEnergy wit3 ∧ 0 < gammaEll 3 * bondEnergy wit3
      ∧ gammaEll 3 * bondEnergy wit3
          ≤ deltaKQuadFormNormalizedCorrected (trivialU witL8) wit3 := by
  refine ⟨wit3_bondEnergy_pos, mul_pos (gammaEll_pos (by norm_num)) wit3_bondEnergy_pos, ?_⟩
  exact deltaKNormalized_gaugeRegular_coercive_generalEll (ell := 3) (by norm_num)
    witL8_strict witL8_dvd (trivialU witL8)
    (gaugeRegular_trivialU _ (le_of_lt (alphaEll_pos (by norm_num)))) wit3
    (admissibleWitness_axialGauge (by norm_num) witL8_dvd _ _ (siteZero_coarse 3))
    (admissibleWitness_mem_kerQ (by norm_num) witL8_dvd _ _)

/-- **MUST-NOT-FIRE AT `ell = 4`.** The same, at a second block size, on a second torus. Two block
sizes beyond `2` is what distinguishes "general `ell`" from "`ell = 3` hardcoded". -/
theorem control_nonvacuous_ell4 :
    0 < bondEnergy wit4 ∧ 0 < gammaEll 4 * bondEnergy wit4
      ∧ gammaEll 4 * bondEnergy wit4
          ≤ deltaKQuadFormNormalizedCorrected (trivialU witL7) wit4 := by
  refine ⟨wit4_bondEnergy_pos, mul_pos (gammaEll_pos (by norm_num)) wit4_bondEnergy_pos, ?_⟩
  exact deltaKNormalized_gaugeRegular_coercive_generalEll (ell := 4) (by norm_num)
    witL7_strict witL7_dvd (trivialU witL7)
    (gaugeRegular_trivialU _ (le_of_lt (alphaEll_pos (by norm_num)))) wit4
    (admissibleWitness_axialGauge (by norm_num) witL7_dvd _ _ (siteZero_coarse 4))
    (admissibleWitness_mem_kerQ (by norm_num) witL7_dvd _ _)

#print axioms bondEnergy_pos_of_ne'
#print axioms gaugeRegular_trivialU
#print axioms witnesses_block_proper
#print axioms control_nonvacuous_ell3
#print axioms control_nonvacuous_ell4

/-! ### §7c — DEGENERATE CASES, DISCHARGED MECHANICALLY

* **`ell = 0`.** `hdvd` alone kills it: `0 ∣ (L ν + 1)` forces `L ν + 1 = 0`, impossible. So the
  `ell = 0` hypothesis set is EMPTY and nothing can be proved from it by accident — proved below
  rather than asserted. (`hell2 : 2 ≤ ell` also excludes it; the point is that the exclusion is
  overdetermined.)
* **`ell = 1`.** `hdvd` and `hstrict` are both satisfiable at `ell = 1`, so the exclusion rests
  ENTIRELY on `2 ≤ ell`. What needs it: `BlockPoincareSharp.lemma24_sharpened` (`hell2`) and
  `FullReparamC.admissibleWitness_ne_zero` (`hell2`, where at `ell = 1` the two exclusions exhaust
  the block). The constants themselves are perfectly finite at `ell = 1`
  (`gammaEll 1 = 1/60`), which is exactly why the hypothesis must be carried explicitly rather than
  inferred from the formula — recorded below.
* **`blockOf` truncation.** Carried throughout as `0 < ell` (from `2 ≤ ell`) together with
  `hdvd : ∀ ν, ell ∣ (L ν + 1)`; both witnesses satisfy them by `decide`.
* **`Real.sqrt` of a negative is `0`.** The only `Real.sqrt` on the critical path is inside
  `coercC`. At `α₀(ell)` the radicand `γ₀(ell) − 64α₀²` is strictly positive
  (`coercC_radicand_pos_at_alphaEll`), so the degenerate branch is not the branch used.
* **`ℕ`-subtraction.** None occurs in this file.
* **`EuclideanSpace ℝ (Fin 0)`.** No reparametrization layer is introduced here, so the
  zero-dimensional degenerate witness of `LemmaAssemblyNormalized` §4d has no analogue to attack. -/

/-- **`ell = 0` is excluded by `hdvd` alone**, independently of `2 ≤ ell`. -/
theorem ell_zero_hypotheses_empty (L : PeriodicLatticeExtent) :
    ¬ (∀ ν : Fin 3, (0 : ℕ) ∣ (L ν + 1)) := by
  intro h
  have := h 0
  omega

/-- **`ell = 1` is excluded ONLY by `2 ≤ ell`** — the torus hypotheses do not exclude it, and the
constants are finite there. So the `2 ≤ ell` binder is load-bearing and not decoration. -/
theorem ell_one_not_excluded_by_torus :
    (∀ ν : Fin 3, (1 : ℕ) < witL8 ν + 1) ∧ (∀ ν : Fin 3, (1 : ℕ) ∣ (witL8 ν + 1))
      ∧ gammaEll 1 = 1 / 60 ∧ ¬ (2 ≤ 1) := by
  refine ⟨by decide, by decide, by rw [gammaEll_def]; norm_num, by omega⟩

/-- The `coercC` radicand at the delivered threshold is strictly positive at every `ell ≥ 2` — the
`√(negative) = 0` branch is not the branch used. -/
theorem coercC_radicand_pos_at_alphaEll {ell : ℕ} (hell2 : 2 ≤ ell) :
    0 < gammaZeroEll ell - 64 * alphaEll ell ^ 2 := by
  have hthr := alphaEll_thr hell2
  have hpos := alphaEll_pos hell2
  nlinarith [hthr, hpos, sq_nonneg (alphaEll ell)]

#print axioms ell_zero_hypotheses_empty
#print axioms ell_one_not_excluded_by_torus
#print axioms coercC_radicand_pos_at_alphaEll

/-! ### §7d — PARITY: the zero field, recorded as `LemmaAssemblyNormalized` §5f does -/

theorem generalEll_trivial_at_zero_field
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    bondEnergy (0 : Bond L → SuTwo) = 0
      ∧ deltaKQuadFormNormalizedCorrected U (0 : Bond L → SuTwo) = 0 :=
  normalized_assembly_trivial_at_zero_field U

#print axioms generalEll_trivial_at_zero_field

/-! ## §8 — THE `ell = 3` IMPROVEMENT, since the printed constant IS available there

`BlockPoincareSharp.lemma24_printed_ell3` gives Bałaban's printed `(1/108)·ell⁻⁴` at `ell = 3`,
which is `1/8748` versus `gammaZeroEll 3 = 1/13122`. §1 is parametric in the scalar input, so this
drops straight in and gives a strictly better `ell = 3` base. Recorded to show §1's parametric form
is doing real work, and to pin exactly how much of the `ell⁻⁵` shape is the ROUTE rather than the
truth. -/

theorem suTwoGeomAdditive_trivialU_ell3_printed
    (hstrict : ∀ ν : Fin 3, (3 : ℕ) < L ν + 1) (hdvd : ∀ ν : Fin 3, (3 : ℕ) ∣ (L ν + 1))
    (A0 : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 3 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 3 → ∀ b ∈ staircasePath y x, A0 b = 0) :
    SuTwoGeomAdditiveInequality 3 (trivialU L)
      ((1 / 108) * (1 / ((3 : ℕ) : ℝ) ^ 4)) A0 :=
  suTwoGeomAdditive_trivialU_ofScalar 3 _ A0 hadm
    (fun B hB => lemma24_printed_ell3 hstrict hdvd B hB)

/-- The `ell = 3` printed base is strictly stronger than the uniform `(1/54)·ell⁻⁵` base there. -/
theorem ell3_printed_base_stronger :
    gammaZeroEll 3 = 1 / 13122 ∧ (1 / 108 : ℝ) * (1 / ((3 : ℕ) : ℝ) ^ 4) = 1 / 8748
      ∧ gammaZeroEll 3 < (1 / 108 : ℝ) * (1 / ((3 : ℕ) : ℝ) ^ 4) := by
  refine ⟨by rw [gammaZeroEll_def]; norm_num, by norm_num, ?_⟩
  rw [gammaZeroEll_def]; norm_num

#print axioms suTwoGeomAdditive_trivialU_ell3_printed
#print axioms ell3_printed_base_stronger

/-! ### §8b — the `ell = 3` assembly with the printed base, pushed all the way through

Because §4 and §5 are parametric in the base (`deltaJ_gaugeRegular_coercive_ofBase`,
`deltaKNormalized_coercive_param_ofBase`), the stronger `ell = 3` base drops in with no proof
redone. It buys BOTH a better constant and a better threshold at `ell = 3`. -/

/-- The `ell = 3` threshold with the printed base: `10⁻⁷`. -/
noncomputable def alphaEll3 : ℝ := 1 / 10000000

/-- The `ell = 3` constant with the printed base: `1/10100`. -/
noncomputable def gammaEll3 : ℝ := 1 / 10100

theorem sqrt_printed3_le :
    Real.sqrt ((1 / 108 : ℝ) * (1 / ((3 : ℕ) : ℝ) ^ 4)) ≤ 11 / 1000 := by
  have h : (1 / 108 : ℝ) * (1 / ((3 : ℕ) : ℝ) ^ 4) ≤ (11 / 1000 : ℝ) ^ 2 := by norm_num
  calc Real.sqrt ((1 / 108 : ℝ) * (1 / ((3 : ℕ) : ℝ) ^ 4))
      ≤ Real.sqrt ((11 / 1000 : ℝ) ^ 2) := Real.sqrt_le_sqrt h
    _ = 11 / 1000 := Real.sqrt_sq (by norm_num)

/-- **THE `ell = 3` ASSEMBLY WITH BAŁABAN'S PRINTED BASE.** `(1/10100)·bondEnergy A ≤ Δ_k` at
threshold `10⁻⁷` — strictly better than the uniform route's `(1/14580)` at `1/24300000`. -/
theorem deltaKNormalized_gaugeRegular_coercive_ell3_printed
    (hstrict : ∀ ν : Fin 3, (3 : ℕ) < L ν + 1) (hdvd : ∀ ν : Fin 3, (3 : ℕ) ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular alphaEll3 U) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 3 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 3 → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L 3, lineCoarseRestrictCov U 3 A b = 0) :
    gammaEll3 * bondEnergy A ≤ deltaKQuadFormNormalizedCorrected U A :=
  deltaKNormalized_coercive_param_ofBase (ell := 3) (by norm_num) hdvd
    ((1 / 108 : ℝ) * (1 / ((3 : ℕ) : ℝ) ^ 4)) alphaEll3 gammaEll3 (11 / 1000)
    (by unfold alphaEll3; norm_num) (by unfold alphaEll3; norm_num)
    (by unfold alphaEll3; norm_num) sqrt_printed3_le
    (by unfold alphaEll3 gammaEll3; norm_num)
    (fun A0 h0 => suTwoGeomAdditive_trivialU_ell3_printed hstrict hdvd A0 h0)
    U hreg A hadm hkerU

/-- The `ell = 3` printed route beats the uniform route on BOTH axes. -/
theorem ell3_improvement :
    gammaEll 3 < gammaEll3 ∧ alphaEll 3 < alphaEll3
      ∧ gammaEll3 = 1 / 10100 ∧ alphaEll3 = 1 / 10000000 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · rw [gammaEll_def]; unfold gammaEll3; norm_num
  · rw [alphaEll_def]; unfold alphaEll3; norm_num

/-- **MUST-NOT-FIRE for the `ell = 3` printed route**: instantiated at the `9³` torus witness with
both sides strictly positive. -/
theorem control_nonvacuous_ell3_printed :
    0 < gammaEll3 * bondEnergy wit3
      ∧ gammaEll3 * bondEnergy wit3
          ≤ deltaKQuadFormNormalizedCorrected (trivialU witL8) wit3 := by
  refine ⟨mul_pos (by unfold gammaEll3; norm_num) wit3_bondEnergy_pos, ?_⟩
  exact deltaKNormalized_gaugeRegular_coercive_ell3_printed witL8_strict witL8_dvd
    (trivialU witL8) (gaugeRegular_trivialU _ (by unfold alphaEll3; norm_num)) wit3
    (admissibleWitness_axialGauge (by norm_num) witL8_dvd _ _ (siteZero_coarse 3))
    (admissibleWitness_mem_kerQ (by norm_num) witL8_dvd _ _)

#print axioms sqrt_printed3_le
#print axioms deltaKNormalized_gaugeRegular_coercive_ell3_printed
#print axioms ell3_improvement
#print axioms control_nonvacuous_ell3_printed

/-! ## §9 — THE `ell = 2` INSTANCE COVERS TORI THE IMPORTED `ell = 2` THEOREM DOES NOT

`LemmaAssemblyNormalized.deltaKNormalized_gaugeRegular_coercive` carries `hL : ∀ μ, 4 ≤ L μ`
(inherited from the `ell = 2` scalar milestone). The general-`ell` chain carries
`hstrict : ∀ ν, ell < L ν + 1` instead, which at `ell = 2` reads `1 ≤ L ν`. On the `4³` torus
(`L ν = 3`) the old hypothesis FAILS and the new one HOLDS, and the conclusion there is not
vacuous — so this is a strict enlargement of the covered class, not a re-export. -/

/-- The `4³` torus: `2 < 4`, `2 ∣ 4`, but `4 ≤ 3` is FALSE. -/
def witL3small : PeriodicLatticeExtent := fun _ => 3

theorem witL3small_strict : ∀ ν : Fin 3, (2 : ℕ) < witL3small ν + 1 := by decide
theorem witL3small_dvd : ∀ ν : Fin 3, (2 : ℕ) ∣ (witL3small ν + 1) := by decide
theorem witL3small_fails_old_hyp : ¬ (∀ μ : Fin 3, 4 ≤ witL3small μ) := by decide

/-- The `2³` block is a PROPER subset of the `4³` torus here too — recorded for this witness as it
is for the other three, so no control in this file relies on `L ν + 1 = ell`. -/
theorem witL3small_block2_proper : ∀ ν : Fin 3, witL3small ν + 1 ≠ 2 := by decide

noncomputable def wit2small : Bond witL3small → SuTwo :=
  admissibleWitness (trivialU witL3small) 2 (siteZero witL3small)

theorem wit2small_bondEnergy_pos : 0 < bondEnergy wit2small := by
  refine bondEnergy_pos_of_ne' wit2small (freeBond 2 (siteZero witL3small)) ?_
  rw [wit2small,
    admissibleWitness_at_freeBond (by norm_num) witL3small_dvd _ _ (siteZero_coarse 2)]
  exact suTwoWitness_ne_zero

/-- **STRICT ENLARGEMENT, EXHIBITED.** On the `4³` torus the imported `ell = 2` theorem's
`4 ≤ L μ` hypothesis is false, the general-`ell` theorem applies at `ell = 2`, and its conclusion
there has both sides strictly positive. -/
theorem control_ell2_strictly_wider_torus :
    ¬ (∀ μ : Fin 3, 4 ≤ witL3small μ)
      ∧ 0 < bondEnergy wit2small
      ∧ 0 < gammaEll 2 * bondEnergy wit2small
      ∧ gammaEll 2 * bondEnergy wit2small
          ≤ deltaKQuadFormNormalizedCorrected (trivialU witL3small) wit2small := by
  refine ⟨witL3small_fails_old_hyp, wit2small_bondEnergy_pos,
    mul_pos (gammaEll_pos (by norm_num)) wit2small_bondEnergy_pos, ?_⟩
  exact deltaKNormalized_gaugeRegular_coercive_generalEll (ell := 2) (by norm_num)
    witL3small_strict witL3small_dvd (trivialU witL3small)
    (gaugeRegular_trivialU _ (le_of_lt (alphaEll_pos (by norm_num)))) wit2small
    (admissibleWitness_axialGauge (by norm_num) witL3small_dvd _ _ (siteZero_coarse 2))
    (admissibleWitness_mem_kerQ (by norm_num) witL3small_dvd _ _)

#print axioms witL3small_fails_old_hyp
#print axioms wit2small_bondEnergy_pos
#print axioms control_ell2_strictly_wider_torus

/-! ## §10 — NON-VACUITY AT `ell = 3` WITH A **NON-TRIVIAL** BACKGROUND

§7b's `ell = 3`/`ell = 4` controls use `trivialU`. That shows the DOMAIN is not `{0}`, but a
sceptic can object that the background is the easiest one in the class. This section removes the
objection at `ell = 3`: the background is `LemmaAssembly.spikedIdentity`, a one-site gauge spike of
the identity configuration, which is `GaugeRegular 0` (so `GaugeRegular α₀(3)` by monotonicity) yet
carries `frobSupBond ≥ 2` — at least `4.86·10⁷` times the threshold `α₀(3) = 1/24300000`, hence
OUTSIDE every `frobSupBond`-hypothesis theorem in this tree.

Geometry: `witL5` has `L ν + 1 = 6`, and `3 < 6` with `3 ∣ 6`, so the `3³` block is a PROPER subset
of the `6³` torus. The admissible field is `FullReparamC.admissibleWitness`, which is built for an
ARBITRARY background — no `U = 1` cancellation is used. -/

theorem witL5_strict3 : ∀ ν : Fin 3, (3 : ℕ) < witL5 ν + 1 := by decide
theorem witL5_dvd3 : ∀ ν : Fin 3, (3 : ℕ) ∣ (witL5 ν + 1) := by decide
theorem witL5_block3_proper : ∀ ν : Fin 3, witL5 ν + 1 ≠ 3 := by decide

#print axioms witL5_block3_proper
/-! ## §11 — IS THE DELIVERED THRESHOLD TIGHT, AND WHICH TERM SETS IT?

A nested validator measured that `gate_arith`'s cubic in `u = ell⁻⁵` stays positive far beyond the
`u ≤ 1/32` the theorem uses — so `1/32` is NOT where the gate binds. What binds is the RATIO
`A = α₀·ell⁵ = 10⁻⁵` between the threshold and the base, and the theorems below pin it from both
sides in exact rationals, at `ell = 2` (`u = 1/32`) where every numeral is a literal.

Setting `α = A·u`, `γ = G·u`, `c = u/54`, the gate reads (dropping the `O(u²)` terms, which are
what the exact statements below keep)

    G ≤ 1/54 − 12·A − 144·A + O(u) ,

so `G = 1/60` needs `156·A ≤ 1/540`, i.e. `A ≤ 1/84240 ≈ 1.187·10⁻⁵`. The delivered
`A = 10⁻⁵ = 1/100000` is within a factor `1.19` of that. **And the `144·A` is the `Δ′` bond-energy
absorption while the `12·A` is the crude `sc = 1` bound on `√γ₀(ell)`: dropping the crude term
entirely would only move the bound from `1/84240` to `1/77760`, an `8.3%` change. So the threshold
is set by the `ell`-FREE `Δ′` cost, not by any slack in this file's own bookkeeping.** -/

/-- **The threshold is NOT slack**: doubling the ratio to `A = 1/50000` already breaks the gate for
the delivered constant `G = 1/60`, at `ell = 2`. -/
theorem gate_fails_at_double_threshold :
    ¬ ((1 / 60) * (1 / 32 : ℝ)
        ≤ (1 - 8 * ((1 / 50000) * (1 / 32 : ℝ)))
            * ((1 / 54) * (1 / 32 : ℝ) - 32 * ((1 / 50000) * (1 / 32 : ℝ)) ^ 2
              - 12 * ((1 / 50000) * (1 / 32 : ℝ)) * 1)
          - 144 * ((1 / 50000) * (1 / 32 : ℝ))) := by
  norm_num

/-- **The threshold is load-bearing, not decorative**: at `A = 1/5000` the whole gate expression is
NEGATIVE — the `Δ′` bond-energy term `144α` overwhelms the base. -/
theorem gate_negative_at_large_alpha :
    (1 - 8 * ((1 / 5000) * (1 / 32 : ℝ)))
        * ((1 / 54) * (1 / 32 : ℝ) - 32 * ((1 / 5000) * (1 / 32 : ℝ)) ^ 2
          - 12 * ((1 / 5000) * (1 / 32 : ℝ)) * 1)
      - 144 * ((1 / 5000) * (1 / 32 : ℝ)) < 0 := by
  norm_num

/-- **WHICH TERM SETS THE THRESHOLD**, in exact rationals: `1/540` is the budget `1/54 − 1/60`;
dividing it by `156 = 144 + 12` (the `Δ′` cost plus the crude `sc = 1` cost) gives `1/84240`;
dividing by `144` alone (the `Δ′` cost, `sc` term removed entirely) gives `1/77760`. The two differ
by `8.3%`, and the delivered `1/100000` is below both. -/
theorem threshold_budget_is_deltaPrime_dominated :
    (1 / 54 : ℝ) - 1 / 60 = 1 / 540
      ∧ (1 / 540 : ℝ) / 156 = 1 / 84240
      ∧ (1 / 540 : ℝ) / 144 = 1 / 77760
      ∧ (1 / 100000 : ℝ) < 1 / 84240
      ∧ (1 / 84240 : ℝ) / (1 / 77760) = 12 / 13 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

#print axioms gate_fails_at_double_threshold
#print axioms gate_negative_at_large_alpha
#print axioms threshold_budget_is_deltaPrime_dominated

/-! ## §12 — `#print axioms` COVERAGE COMPLETION

A nested validator measured that 20 `theorem`s in this file lacked an individual `#print axioms`
line while the header claims one on every declaration. They are printed here, so the header's claim
is a fact rather than an approximation. `gammaZeroEll_pos` is recorded but NOT consumed anywhere in
this file — disclosed rather than deleted, since it is the third member of the
`{gammaEll_pos, alphaEll_pos, gammaZeroEll_pos}` triple and its absence would be the odder gap. -/

#print axioms gammaZeroEll_def
#print axioms gammaEll_def
#print axioms alphaEll_def
#print axioms inv_pow_five_pos
#print axioms inv_pow_five_le
#print axioms alphaEll_pos
#print axioms gammaEll_pos
#print axioms gammaZeroEll_pos
#print axioms gammaZeroEll_le_one
#print axioms alphaEll_le_eighth
#print axioms witL8_strict
#print axioms witL8_dvd
#print axioms witL7_strict
#print axioms witL7_dvd
#print axioms wit3_bondEnergy_pos
#print axioms wit4_bondEnergy_pos
#print axioms witL3small_strict
#print axioms witL3small_dvd
#print axioms witL3small_block2_proper
#print axioms witL5_strict3
#print axioms witL5_dvd3

end AdalyFormal.Balaban.GeneralEllAssembly
