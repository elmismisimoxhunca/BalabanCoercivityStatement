/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.FibreCoercivity
import AdalyFormal.Balaban.SplitBaseCase
import AdalyFormal.Balaban.GammaContourTree
import AdalyFormal.Balaban.DeltaPrimeBound
import AdalyFormal.Balaban.BridgeRestricted

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-!
# `ComposedCoercivity.lean` — the five pieces, ASSEMBLED

Lane record: `compute/lemma_composition/PROGRESS.md`.

This module states and proves the composed coercivity lemma from the five pieces that already have
their mathematics on disk. It **defines no new mathematics**; every step is an application of an
imported theorem, and every constant is produced by one.

## The pieces, and the exact declaration consumed from each

| piece | declaration consumed | what it supplies |
|---|---|---|
| fibre | `FibreCoercivity.bond_energy_bound_deltaK` | `‖A b‖² ≤ 69088·(Δ_k + P_Ax)` on `{QA=0}`, PER BOND |
| axial | `AxialCoercivity.inner_pAxCLM_eq` | `P_Ax` as the operator the bridge's `P` slot wants |
| kappa | `GammaContourTree.hlam_at_kappa_sq_768_gamma` | `siteEnergy λ ≤ 768·bondEnergy A` |
| delta | `DeltaPrimeBound.abs_deltaPrimePiForm_le` | `\|⟨A,Δ′_πA⟩\| ≤ Jsup·κ·(28+48κ)·bondEnergy A` |
| recursion | `GammaRecursion.gammaSeq` / `uniformStepGamma_of_lt_one` | `γ_{k+1} = (γ_k−δ)/q²` |

`SplitBaseCase` is imported and its refutations are cited, but **its constant `γ_split = ℓ₀` is NOT
substituted into the recursion** — see the first finding below, which is that module's own ruling.

## ⚠ FOUR FINDINGS. Read these before reading any theorem.

**F1 — `γ_split` DOES NOT COMPOSE WITH THE RECURSION, and `SplitBaseCase` says so itself.**
That module's `⚠ HONEST SCOPE` reads, verbatim:

> "The recursion `GammaRecursion.chain_gamma` consumes `γ‖x‖² ≤ ⟨x, Δx⟩`; `γ_split = ℓ₀` is a
> constant in a DIFFERENT pairing and must not be substituted into `δ ≤ γ(1 − q²)`."

The mismatch, both declarations named: `SplitBaseCase.ell_mul_coarseCurlEnergy_le_deltaJ` carries
`(ell:ℝ) * coarseCurlEnergy hdvd (Q_ell B)` on the left — the coarse CURL energy of the coarse
field — whereas `GammaRecursion.CoerciveOn Δ γ` is `∀ x, γ‖x‖² ≤ ⟪x, Δx⟫` and
`uniformStepGamma_of_lt_one`'s `hfix : δ ≤ γ₀(1−q²)` compares two constants both normalised against
`‖x‖²`. The minimal repair would be a reverse bound `c‖B‖² ≤ coarseCurlEnergy (Q_ell B)`; that is
refuted on the un-gauge-fixed domain by `SplitBaseCase.coarse_bond_energy_base_case_refuted`, and on
`{Q A = 0}` the left side is identically `0` (`SplitBaseCase.coarseCurlEnergy_of_kernel`).
**So the base case that can feed the recursion is the FIBRE one, and `γ₀ = 1/69088`.**

**F2 — the fibre bound is at the FLAT background only. HALF-CLOSED HERE (§3b).**
`bond_energy_bound_deltaK` fixes `trivialU L` in the `Q` clause AND in the operator.
* The **operator** half is closed: §3b moves the flat curl energy under the CURVED `Δ_k(U)` using
  `RegularUPerturbation.norm_curlDrift_sq_le` and `LemmaAssemblyNormalized.sum_plaqBondSq_eq`,
  paying `544α₀ + 64α₀²` in `bondEnergy` (`curlEnergy_le_curved`), and delivers
  `AggregateFibreBound L U γ` at a positive `γ` for a genuinely curved `U`
  (`aggregateFibreBound_curved`, inhabited by `aggregateFibreBound_curved_inhabited`).
* The **`Q` clause** half is NOT closed and is carried inside the definition of
  `AggregateFibreBound` rather than in prose: the clause stays `lineCoarseRestrictCov (trivialU L)`.
  §3b's closing note names the exact missing primitive and why it cannot be supplied from outside
  `FibreCoercivity` (that module's `Q_kills_inter_block` consumes `hQ` as an EXACT equation).
* The `ℓ^∞` clause (§1) remains flat: §3b's route pays its remainder in `bondEnergy`, which is not
  absorbable into `bondSup` without the volume factor.

**F3 — PER-BOND is not AGGREGATE.** `bond_energy_bound_deltaK` is per-bond. The honest volume-free
repackaging is the SUP norm — `bondSup`, §1. The aggregate `L²` form costs `Fintype.card (Bond L)`
(`FibreCoercivity.bondEnergy_le_with_volume_factor`, whose name is the disclosure). The aggregate is
therefore carried here as an explicitly NAMED hypothesis, `AggregateFibreBound` (§3), stated exactly
in the shape the iteration consumes, and DISCHARGED at the volume-dependent constant
`1/(69088·N)` so the hypothesis class is provably inhabited rather than empty. ~~A volume-FREE
discharge is the open leg; when a lane lands it, it plugs into `hagg` with no restatement here.~~
**SUPERSEDED (2026-08-01):** a volume-free discharge is no longer open — it exists, elsewhere, and
this module does not import it. `FibreAggregate.aggregate_fibre_bound` (`γ = 1/3316224`,
volume-free) and `CovariantFibreTransfer.aggregate_fibre_bound_curved` (covariant fibre, continuous
degradation under a curved `U`) are both proved and kernel-checked
(`compute/covariant_fibre/PROGRESS.md` FINDING A). Neither is imported here, so `AggregateFibreBound`
and `hagg` in this file are unchanged and still carried exactly as below — nothing here is
restated — but a consumer wanting the volume-free constant should go to `FibreAggregate`, not wait
on a future lane.

**F4 — the admissible `α₀` shrinks by a factor `69088/2000 = 34.544` once `γ₀` is the fibre
constant.** `KappaBound.criterion_closes_at_four_e_minus_ten` closes at `α₀ = 4·10⁻¹⁰` because it
uses `γ₀ = normGamma = 1/2000`. At `γ₀ = 1/69088` that same `α₀` **fails**
(`criterion_fails_at_four_e_minus_ten_at_gammaFibre`); the threshold moves to `≈1.2·10⁻¹¹`, pinned
two-sidedly in §5. Consequence for the non-vacuity witness: `GammaContourTree.curvedTinyU` is
`curvedFamilyU 10⁻¹¹`, carrying only `frobSupBond ≤ 2√2·10⁻¹¹ ≈ 2.83·10⁻¹¹`, so it is **not** known
to lie in the tighter class. §6 builds the finer witness `curvedFineU = curvedFamilyU 10⁻¹²` and
proves it is both in the class and genuinely curved.

## Which binder each live lane is expected to discharge

* `hagg : AggregateFibreBound L γstar` — the block-local `L²` fibre bound (volume-free). Until then,
  `aggregateFibreBound_volume_costed` discharges it at `γstar = 1/(69088·N)`.
* `hmean` — `Q′λ = 0` at `ell = 2` in the `(1.7)` transport. Carried RAW and deliberately: the
  ker-membership route (`GammaContourTree.poincare_for_gaugeParam`) is not called by
  `hlam_at_kappa_sq_768_gamma`, and the operator `Q′` is not yet pinned at source.
* `hweak`, `hadj`, `hproj` — the weak Euler–Lagrange identity, the adjoint RELATION for `D*`, and
  `‖R‖ ≤ 1`. These are `KappaBound`'s own remaining inputs, passed through unchanged.
* `hJdef` — that the current `J` really is `η⁻²·D*Im ∂U` in the four-plaquette shape.

**DISCLOSURE (2026-08-01, `compute/joint_prosecution/VERDICT.md` item F): `hJdef` is
under-constrained, and injectivity of `pl` is not a sufficient fix.** `pl` is free data in this
theorem, and `hJdef` only pins `J` to a FORMULA in `pl`, so `hJdef` is dischargeable by DEFINING `J`
from any `pl` — including a junk selection that forces `J ≡ 0` identically at every background, not
only the flat one. `AdalyFormal.Balaban.JointInstantiation.jointJ_trivialU_eq_zero` exhibits exactly
this at the flat background; that same module's `jointPl` was later found (`DiscriminatingConfig.
jointPl_not_injective`) to collide two of its four plaquette slots, ~~so `J ≡ 0` there for every `U`,
not only `trivialU L` — a stronger degeneracy than `hJdef`'s own shape discloses.~~ **CORRECTION
(2026-08-01, `compute/kimi_composed/VERDICT.md` §Q6(a)): FALSE as struck.** The collision
(`DiscriminatingConfig.jointPl_slots_collide`, slots `2 = 3`) cancels only the `+imH(pl b 2) −
imH(pl b 3)` terms, leaving `jointJ` a TWO-TERM difference `η·(imH(pl b 0) − imH(pl b 1))` — not
identically `0`. A counterexample at the tree's own curved background:
`DiscriminatingConfig.imHolonomy_truePl0` proves `imHolonomy (discU t) truePl0 =
((rotB t : ℂ) * Complex.I) • rotGenVal ≠ 0` for `rotB t ≠ 0`, and `jointPl discBond 0 = truePl0` (via
`DiscriminatingConfig.truePl0_base`), so `jointJ η (discU t) discBond ≠ 0` there — the collision does
NOT make `J ≡ 0` at every `U`. The disclosure's main conclusion (`hJdef` under-constrained; the
`pl`-injectivity repair alone is insufficient) is unaffected — `hJdef_does_not_pin_the_current`,
cited below, proves that independently — but the "stronger degeneracy" sentence overstated it. The natural repair
— require `pl` injective at every bond — is PROVED insufficient:
`AdalyFormal.Balaban.DiscriminatingConfig.hJdef_does_not_pin_the_current` exhibits an injective `pl`
(`flatPl`) at a genuinely curved background that still forces `J ≡ 0`. What DOES preserve content is
pinning the selection to the plaquettes that actually contain the bond: `DiscriminatingConfig` §13
names them (`truePlStar`, proved to contain `bStar` via `truePlStar_contains` and to be pairwise
distinct via `truePlStar_injective`) and shows the resulting current is nonzero there. That repair is
pinned AT one bond only — no claim is made that a selection pinned this way exists globally in this
tree — and it is not applied here: `hJdef`'s shape in this file is unchanged. -/

namespace AdalyFormal.Balaban.ComposedCoercivity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg frobSupBond)
open AdalyFormal.Balaban.GeneralUHodgeDrift (siteEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeRegular gaugeRegular_of_frobSupBond_le)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.AxialCoercivity (pAx pAx_nonneg pAxCLM inner_pAxCLM_eq)
open AdalyFormal.Balaban.FibreCoercivity (bond_energy_bound_deltaK curlEnergy
  deltaK_trivialU_eq_curlEnergy bondEnergy_le_with_volume_factor zeroSite)
open AdalyFormal.Balaban.DeltaPrimeBound (deltaPiConst deltaPrimePiForm abs_deltaPrimePiForm_le
  frobNorm_current_le weightedQ_two alphaThresholdPi)
open AdalyFormal.Balaban.GammaContourTree (hlam_at_kappa_sq_768_gamma gammaM)
open AdalyFormal.Balaban.GammaRecursion (gammaSeq UniformStepGamma uniformStepGamma_of_lt_one)
open AdalyFormal.Balaban.RegularUCurvedWitness (curvedFamilyU curvedPlaq
  curvedFamilyU_curvature_ne_one frobSupBond_curvedFamilyU_le)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — `√768`, bracketed once, and the `κ`-slot identity

Every numeric statement below runs through these two facts and nothing else about `√768`. Both are
`KappaBound`'s (`kappa_bounds`, `kappa_lower_sharp`), re-exported here so the arithmetic sections
read as consequences of a theorem rather than of a numeral. -/

/-- `κ = √768`, the value `KappaBound` derives (`κ² = rsq·Psq² = 12·8² = 768`). Named so that no
section below writes the numeral in a hypothesis position. -/
noncomputable def kappaTree : ℝ := Real.sqrt 768

theorem kappaTree_sq : kappaTree ^ 2 = 768 := Real.sq_sqrt (by norm_num)

theorem kappaTree_nonneg : (0 : ℝ) ≤ kappaTree := Real.sqrt_nonneg _

/-- `27.7 < κ < 27.72`. Lower half is `KappaBound.kappa_lower_sharp`; upper half is proved from
`kappaTree_sq` (`27.72² = 768.3984 > 768`), sharper than `KappaBound.kappa_bounds`' `28`. -/
theorem kappaTree_bracket : (277 / 10 : ℝ) < kappaTree ∧ kappaTree < (2772 / 100 : ℝ) := by
  refine ⟨AdalyFormal.Balaban.KappaBound.kappa_lower_sharp, ?_⟩
  nlinarith [kappaTree_sq, kappaTree_nonneg]

/-- **THE `κ`-POLYNOMIAL OF `deltaPiConst` IS LINEAR IN `κ`, EXACTLY.** `κ(28 + 48κ) = 28κ + 48κ²`
and `κ² = 768`, so the quadratic collapses: `κ(28 + 48κ) = 28κ + 36864`. Every numeric statement
in §5 runs through this identity, which is why none of them needs a quadratic estimate on `√768`. -/
theorem kappaPoly_eq : kappaTree * (28 + 48 * kappaTree) = 28 * kappaTree + 36864 := by
  linear_combination 48 * kappaTree_sq

/-- `37639 < κ(28 + 48κ) < 37641`. Both halves from `kappaTree_bracket` through `kappaPoly_eq`;
the true value is `28√768 + 36864 ≈ 37639.96`. -/
theorem kappaPoly_bracket :
    (37639 : ℝ) < kappaTree * (28 + 48 * kappaTree)
      ∧ kappaTree * (28 + 48 * kappaTree) < (37641 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := kappaTree_bracket
  rw [kappaPoly_eq]
  constructor <;> linarith

/-- `deltaPiConst Jsup κ = Jsup · (κ(28 + 48κ))` — the associativity step that lets §5 be linear
arithmetic in the bracketed polynomial. -/
theorem deltaPiConst_eq (Jsup : ℝ) :
    deltaPiConst Jsup kappaTree = Jsup * (kappaTree * (28 + 48 * kappaTree)) := by
  unfold deltaPiConst; ring

#print axioms kappaTree
#print axioms kappaTree_sq
#print axioms kappaTree_nonneg
#print axioms kappaTree_bracket
#print axioms kappaPoly_eq
#print axioms kappaPoly_bracket
#print axioms deltaPiConst_eq

/-! ## §1 — THE VOLUME-FREE NORM, AND THE FLAT COMPOSED COERCIVITY

`FibreCoercivity.bond_energy_bound_deltaK` is PER BOND. Its honest volume-free aggregation is the
SUP over bonds, not the sum: summing costs `Fintype.card (Bond L)` and that factor is real (F3).
`bondSup` names the sup so the composed statement is a statement in a NORM. -/

/-- The bond set is nonempty, so `sup'` is available. Reuses `FibreCoercivity.zeroSite`. -/
theorem bond_univ_nonempty : (Finset.univ : Finset (Bond L)).Nonempty :=
  ⟨(zeroSite L, (0 : Fin 3)), Finset.mem_univ _⟩

/-- **The `ℓ^∞` bond energy** `max_b ‖A b‖²`. This is the norm in which the fibre bound is
volume-free. -/
noncomputable def bondSup (A : Bond L → SuTwo) : ℝ :=
  (Finset.univ : Finset (Bond L)).sup' bond_univ_nonempty (fun b => ‖A b‖ ^ 2)

theorem le_bondSup (A : Bond L → SuTwo) (b : Bond L) : ‖A b‖ ^ 2 ≤ bondSup A :=
  Finset.le_sup' (fun c => ‖A c‖ ^ 2) (Finset.mem_univ b)

theorem bondSup_nonneg (A : Bond L → SuTwo) : 0 ≤ bondSup A :=
  le_trans (sq_nonneg _) (le_bondSup A (zeroSite L, (0 : Fin 3)))

theorem bondSup_le {A : Bond L → SuTwo} {c : ℝ} (h : ∀ b : Bond L, ‖A b‖ ^ 2 ≤ c) :
    bondSup A ≤ c :=
  Finset.sup'_le _ _ (fun b _ => h b)

/-- **THE COMPOSED COERCIVITY, FLAT BACKGROUND, VOLUME-FREE.**

`(1/69088)·max_b ‖A b‖² ≤ ⟨A, Δ_k A⟩ + P_Ax(A)` on `{Q A = 0}`, at block side `2`, at every
periodic extent with `2 ∣ (L μ + 1)`, with NO volume factor and no other hypothesis on `A`.

This is `FibreCoercivity.bond_energy_bound_deltaK` aggregated in the only norm in which its constant
survives aggregation. -/
theorem composed_coercivity_sup (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0) :
    (1 / 69088 : ℝ) * bondSup A
      ≤ deltaKQuadFormNormalizedCorrected (trivialU L) A + pAx A (CoarseLattice L 2) 2 := by
  have h : bondSup A
      ≤ 69088 * (deltaKQuadFormNormalizedCorrected (trivialU L) A
        + pAx A (CoarseLattice L 2) 2) :=
    bondSup_le (fun b => bond_energy_bound_deltaK hdvd A hQ b)
  linarith

/-- **THE SAME, WITH `P_Ax` AS THE OPERATOR THE BRIDGE'S `P` SLOT CONSUMES.** `pAxCLM` is
`AxialCoercivity`'s continuous-linear-map form of CMP95 `(1.10)`; `inner_pAxCLM_eq` is the identity
that makes its diagonal `P_Ax`. Nothing is re-derived here — this is the composition of §1's bound
with that identity, and it is what lets the composed statement be quoted against an operator
inequality rather than against a quadratic form. -/
theorem composed_coercivity_sup_operator (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0) :
    (1 / 69088 : ℝ) * bondSup A
      ≤ deltaKQuadFormNormalizedCorrected (trivialU L) A
        + (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
            (pAxCLM (CoarseLattice L 2) 2 (WithLp.toLp 2 A)) : ℝ) := by
  rw [inner_pAxCLM_eq (CoarseLattice L 2) 2 A]
  exact composed_coercivity_sup hdvd A hQ

#print axioms bond_univ_nonempty
#print axioms bondSup
#print axioms le_bondSup
#print axioms bondSup_nonneg
#print axioms bondSup_le
#print axioms composed_coercivity_sup
#print axioms composed_coercivity_sup_operator

/-! ## §2 — NON-VACUITY OF §1, AND THE THREE CLAUSES

A coercivity statement whose left-hand side is always `0` proves nothing. `FibreCoercivity.altMode`
is closed, `Q`-free and `P_Ax`-visible; at a nonzero fibre vector its sup energy is strictly
positive, so §1 constrains a genuinely nonzero quantity. The drop-one controls
(`FibreCoercivity.clauses_are_load_bearing`) are cited, not restated. -/

open AdalyFormal.Balaban.FibreCoercivity (altMode altMode_eq par zeroSite_even)

/-- **§1's LEFT-HAND SIDE IS NOT IDENTICALLY ZERO.** At the closed alternating mode with any
nonzero `w`, `bondSup > 0`. -/
theorem bondSup_altMode_pos (w : SuTwo) (hw : w ≠ 0) : 0 < bondSup (altMode (L := L) w) := by
  refine lt_of_lt_of_le ?_ (le_bondSup (altMode (L := L) w) (zeroSite L, (0 : Fin 3)))
  rw [altMode_eq w (b := ((zeroSite L, (0 : Fin 3)) : Bond L)) rfl]
  have hpar : par (zeroSite L) = 1 := by
    unfold par; rw [if_pos (zeroSite_even (L := L) 0)]
  rw [hpar, one_smul]
  exact pow_pos (norm_pos_iff.2 hw) 2

/-- **NON-VACUITY AT A CONCRETE FIBRE VECTOR.** `BridgeRestricted.rotGen` is the tree's own nonzero
`𝔰𝔲(2)` element. -/
theorem bondSup_altMode_rotGen_pos :
    0 < bondSup (altMode (L := L) AdalyFormal.Balaban.BridgeRestricted.rotGen) :=
  bondSup_altMode_pos _ AdalyFormal.Balaban.BridgeRestricted.rotGen_ne_zero

#print axioms bondSup_altMode_pos
#print axioms bondSup_altMode_rotGen_pos

/-! ## §3 — `AggregateFibreBound`: the `L²` leg, NAMED

§1 is in `ℓ^∞`. The recursion (`GammaRecursion.CoerciveOn`) and the bridge's demand
(`AxialCoercivity.pAxCLM_alternating_demand_iff`) are in `L²`. Summing §1's per-bond bound over
bonds is legitimate and costs `Fintype.card (Bond L)`
(`FibreCoercivity.bondEnergy_le_with_volume_factor` — the factor is in that theorem's NAME).

The aggregate is therefore carried as an explicit `Prop` over no free data: `γ` is a parameter, `A`
is universally quantified, and the conclusion is an inequality — there is no existential for a
degenerate instance to satisfy. `aggregateFibreBound_volume_costed` proves the class is INHABITED at
a positive constant, so no theorem below is about an empty hypothesis class. -/

/-- **THE NAMED `L²` LEG.** Exactly the shape `GammaRecursion.CoerciveOn` consumes, on the
subspace `{Q A = 0}`, for the three-clause operator `Δ_k(U) + P_Ax`.

**The background `U` is a parameter of the OPERATOR only.** The `Q` clause stays at `trivialU L`
even when `U` is curved — that is the exact half of F2 that §3b does NOT close, and carrying it in
the definition rather than in prose is what stops it being over-read. See §3b's closing note for
the named primitive the covariant `Q` clause would need. -/
def AggregateFibreBound (L : PeriodicLatticeExtent)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (γ : ℝ) : Prop :=
  ∀ A : Bond L → SuTwo,
    (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0) →
      γ * bondEnergy A
        ≤ deltaKQuadFormNormalizedCorrected U A + pAx A (CoarseLattice L 2) 2

/-- The bond carrier is nonempty, so its cardinality is a positive real. -/
theorem card_bond_pos : (0 : ℝ) < (Fintype.card (Bond L) : ℝ) := by
  have h : 0 < Fintype.card (Bond L) :=
    Fintype.card_pos_iff.mpr ⟨(zeroSite L, (0 : Fin 3))⟩
  exact_mod_cast h

/-- **THE `L²` LEG, DISCHARGED — AT A COST THAT IS IN THE STATEMENT.** The aggregate bound holds
with `γ = 1/(69088·N)`, `N = Fintype.card (Bond L)`. The volume factor is real and is not hidden:
this is `FibreCoercivity.bondEnergy_le_with_volume_factor` rearranged, and it is what makes
`AggregateFibreBound` a NON-EMPTY hypothesis class rather than a decorative binder. -/
theorem aggregateFibreBound_volume_costed (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    AggregateFibreBound L (trivialU L) (1 / (69088 * (Fintype.card (Bond L) : ℝ))) := by
  intro A hQ
  have hN := card_bond_pos (L := L)
  have hvol := bondEnergy_le_with_volume_factor hdvd A hQ
  rw [← deltaK_trivialU_eq_curlEnergy A] at hvol
  have hden : (0 : ℝ) < 69088 * (Fintype.card (Bond L) : ℝ) := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
  have heq : (deltaKQuadFormNormalizedCorrected (trivialU L) A + pAx A (CoarseLattice L 2) 2)
        * (69088 * (Fintype.card (Bond L) : ℝ))
      = (Fintype.card (Bond L) : ℝ)
        * (69088 * (pAx A (CoarseLattice L 2) 2
            + deltaKQuadFormNormalizedCorrected (trivialU L) A)) := by ring
  rw [heq]
  exact hvol

/-- **THE CONSTANT DEGRADES WITH THE VOLUME, EXACTLY.** `alphaThresholdPi` is linear in `γ₀`, so
the admissible regularity radius at the volume-costed constant is the volume-free one divided by
`N`. Stated so the cost of F3 is a formula and not a remark: a volume-free discharge of
`AggregateFibreBound` is worth exactly a factor `N` in the admissible `α₀`. -/
theorem alphaThreshold_scales_with_volume (etaInvSq kappa gamma q N : ℝ) :
    alphaThresholdPi etaInvSq kappa (gamma / N) q = alphaThresholdPi etaInvSq kappa gamma q / N := by
  unfold alphaThresholdPi
  ring

#print axioms AggregateFibreBound
#print axioms card_bond_pos
#print axioms aggregateFibreBound_volume_costed
#print axioms alphaThreshold_scales_with_volume

/-! ### §3b — F2, HALF-CLOSED: the OPERATOR may be curved

F2 said the fibre bound is at the flat background. Half of that is not a wall, it is a computation
the tree already has the primitive for: `RegularUPerturbation.norm_curlDrift_sq_le` bounds the
single-scale drift `D_U A − D_1 A` plaquette-wise by the holonomy deviation. Aggregating it against
`LemmaAssemblyNormalized.sum_plaqBondSq_eq`'s exact incidence identity, and paying
`DeltaPrimeBound.abs_deltaPrimeQuadFormNormalizedTransported_le_bondEnergy` for the `Δ′` term, moves
the FLAT curl energy under the CURVED `Δ_k(U)` with an explicit `α₀`-linear remainder.

**What this closes:** `AggregateFibreBound L U γ` at a genuinely curved `U`, with an explicit
positive `γ` under an explicit smallness condition. **What it does NOT close:** the `Q` clause is
still the flat `lineCoarseRestrictCov (trivialU L)`. Making it covariant is not available from
outside `FibreCoercivity`: `FibreCoercivity.Q_kills_inter_block` consumes `hQ` as an EXACT equation
to conclude `|B(y)|·A(y+e_μ,μ) = 0`, and replacing it by `Q_U A = 0` turns that into an approximate
identity with an `α₀`-sized remainder, which has to be threaded back through
`inter_dev_bound`/`block_summand_dev` inside that module's own chain. That is a write-scope
collision, not a mathematical obstruction, and ~~the named primitive it needs is:
`‖(rZeroA U y x A μ 2) − (rZeroA (trivialU L) y x A μ 2)‖ ≤ c·frobSupBond U·(‖A(x,μ)‖ + ‖A(x+e_μ,μ)‖)`
— the `Q`-analogue of `norm_curlDrift_le`, provable by the same `RMapLipschitz.norm_RMap_sub_self_le`
step that `RegularUQChain` already telescopes.~~ **CORRECTED (2026-08-01): that primitive was never
missing, it was unread.** `RegularUQChain.norm_rZeroA_trivialU_sub_le` proves exactly this bound, at
general `ell` (not only `ell = 2`), already banked and axiom-clean before this note was written.
`CovariantFibreTransfer.rZeroA_drift_le` specializes it to `ell = 2` with the constant `c = 16`
wired to `RegularUQChain`'s own path-length theorem, and that module's `aggregate_fibre_bound_curved`
carries the covariant `Q` clause the rest of this paragraph describes as unavailable
(`compute/covariant_fibre/PROGRESS.md`, FINDING A). Neither module is imported here, so the `Q`
clause of `AggregateFibreBound` in THIS file is unchanged and still the flat
`lineCoarseRestrictCov (trivialU L)` — this correction is about where the primitive lives, not about
what this file proves. -/

open AdalyFormal.Balaban.RegularUPerturbation (curlDrift curlDrift_apply norm_curlDrift_sq_le
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlValueCovariant_trivialU_local)
open AdalyFormal.Balaban.LemmaAssembly (plaqBondSq dstarDQuadForm_eq_sum_norm_sq)
open AdalyFormal.Balaban.FibreCoercivity (sq_two curlEnergy_nonneg)

/-- **THE AGGREGATED DRIFT.** `Σ_p ‖(D_U − D_1)A(p)‖² ≤ 32·α²·bondEnergy A`. Both factors are
counted: `8` from `norm_curlDrift_sq_le`'s four-term Cauchy–Schwarz, `4` from
`LemmaAssemblyNormalized.sum_plaqBondSq_eq`'s EXACT bond-incidence identity. No volume factor. -/
theorem sum_curlDrift_sq_le {α : ℝ} (hα0 : 0 ≤ α)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ α) (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖curlDrift U A p‖ ^ 2 ≤ 32 * α ^ 2 * bondEnergy A := by
  have hbond : ∀ b : Bond L,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α :=
    fun b => le_trans (frobNorm_le_frobSupBond U b) hsup
  have hpt : ∀ p : PeriodicLatticePlaquette L,
      ‖curlDrift U A p‖ ^ 2 ≤ 8 * α ^ 2 * plaqBondSq A p := by
    intro p
    have h := norm_curlDrift_sq_le U A p α hα0 hbond
    have hle : ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
          + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2
        ≤ plaqBondSq A p := by
      unfold plaqBondSq
      have h1 := sq_nonneg ‖A (p.1, p.2.1.1)‖
      have h2 := sq_nonneg ‖A (p.1, p.2.1.2)‖
      linarith
    nlinarith [h, hle, sq_nonneg α]
  calc ∑ p : PeriodicLatticePlaquette L, ‖curlDrift U A p‖ ^ 2
      ≤ ∑ p : PeriodicLatticePlaquette L, 8 * α ^ 2 * plaqBondSq A p :=
        Finset.sum_le_sum (fun p _ => hpt p)
    _ = 8 * α ^ 2 * ∑ p : PeriodicLatticePlaquette L, plaqBondSq A p := by
        rw [Finset.mul_sum]
    _ = 8 * α ^ 2 * (4 * bondEnergy A) := by
        rw [AdalyFormal.Balaban.LemmaAssemblyNormalized.sum_plaqBondSq_eq]
    _ = 32 * α ^ 2 * bondEnergy A := by ring

/-- The `α₀`-linear remainder the curved operator costs: `544α₀ + 64α₀²`. `544 = 2·272` is twice
`DeltaPrimeBound`'s `Δ′` constant; `64 = 2·32` is twice the aggregated drift. Both counted. -/
noncomputable def driftRemainder (α₀ : ℝ) : ℝ := 544 * α₀ + 64 * α₀ ^ 2

theorem driftRemainder_nonneg {α₀ : ℝ} (hα₀ : 0 ≤ α₀) : 0 ≤ driftRemainder α₀ := by
  unfold driftRemainder; positivity

/-- **THE FLAT CURL ENERGY, UNDER THE CURVED OPERATOR.**
`curlEnergy A ≤ 2·⟨A, Δ_k(U) A⟩ + (544α₀ + 64α₀²)·bondEnergy A` whenever `frobSupBond U ≤ α₀`.
At `α₀ = 0` (i.e. `U = 1`) it degenerates to `curlEnergy ≤ 2·Δ_k(1)`, consistent with
`FibreCoercivity.deltaK_trivialU_eq_curlEnergy`'s equality (the `2` is the Cauchy–Schwarz slack of
`sq_two`, not an error). -/
theorem curlEnergy_le_curved {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ α₀) (A : Bond L → SuTwo) :
    curlEnergy A
      ≤ 2 * deltaKQuadFormNormalizedCorrected U A + driftRemainder α₀ * bondEnergy A := by
  have hE := bondEnergy_nonneg A
  -- pointwise: the flat curl is the covariant curl minus the drift
  have hsplit : ∀ p : PeriodicLatticePlaquette L,
      ‖flatCurlValue A p‖ ^ 2
        ≤ 2 * ‖AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U A p‖ ^ 2
          + 2 * ‖curlDrift U A p‖ ^ 2 := by
    intro p
    have hid : flatCurlValue A p
        = AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U A p
          + (- curlDrift U A p) := by
      have hd : curlDrift U A p
          = AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U A p
            - flatCurlValue A p := by
        show (AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U A
            - AdalyFormal.Balaban.CovariantOperators.curlValueCovariant (trivialU L) A) p = _
        rw [Pi.sub_apply, curlValueCovariant_trivialU_local]
      rw [hd]; abel
    have hb := sq_two (AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U A p)
      (- curlDrift U A p)
    rw [← hid, norm_neg] at hb
    exact hb
  have hsum : curlEnergy A
      ≤ 2 * (∑ p : PeriodicLatticePlaquette L,
            ‖AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U A p‖ ^ 2)
        + 2 * ∑ p : PeriodicLatticePlaquette L, ‖curlDrift U A p‖ ^ 2 := by
    unfold curlEnergy
    calc ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2
        ≤ ∑ p : PeriodicLatticePlaquette L,
            (2 * ‖AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U A p‖ ^ 2
              + 2 * ‖curlDrift U A p‖ ^ 2) :=
          Finset.sum_le_sum (fun p _ => hsplit p)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the covariant curl energy IS `dstarDQuadForm U`
  have hdstar : (∑ p : PeriodicLatticePlaquette L,
        ‖AdalyFormal.Balaban.CovariantOperators.curlValueCovariant U A p‖ ^ 2)
      = AdalyFormal.Balaban.CovariantHj.dstarDQuadForm U A :=
    (dstarDQuadForm_eq_sum_norm_sq U A).symm
  -- and `dstarDQuadForm U = Δ_k(U) − Δ′`, with `|Δ′| ≤ 272 α₀ bondEnergy`
  have hprime :=
    AdalyFormal.Balaban.DeltaPrimeBound.abs_deltaPrimeQuadFormNormalizedTransported_le_bondEnergy
      hα₀ U (gaugeRegular_of_frobSupBond_le hsup) A
  have hdk : deltaKQuadFormNormalizedCorrected U A
      = AdalyFormal.Balaban.CovariantHj.dstarDQuadForm U A
        + AdalyFormal.Balaban.NormalizationAudit.deltaPrimeQuadFormNormalizedTransported U A := rfl
  have habs := abs_le.mp hprime
  have hdrift := sum_curlDrift_sq_le hα₀ U hsup A
  rw [hdstar] at hsum
  unfold driftRemainder
  nlinarith [hsum, hdrift, habs.1, habs.2, hdk, hE]

/-- **F2, HALF-CLOSED — `AggregateFibreBound` AT A CURVED OPERATOR.** With `N = Fintype.card (Bond
L)` and `C = 544α₀ + 64α₀²`, and under the explicit smallness condition `69088·N·C < 1`, the
three-clause `L²` bound holds with the CURVED `Δ_k(U)` and the explicit positive constant
`(1 − 69088·N·C)/(2·69088·N)`.

Two honest limits, both visible in the statement: the constant still carries the volume `N` (F3,
inherited — this theorem consumes `bondEnergy_le_with_volume_factor`), and the smallness condition
is therefore volume-dependent too. At `α₀ = 0` the constant is `1/(2·69088·N)`, a factor `2` off
`aggregateFibreBound_volume_costed` — the `sq_two` slack, disclosed rather than absorbed. -/
theorem aggregateFibreBound_curved (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ α₀)
    (hsmall : 69088 * (Fintype.card (Bond L) : ℝ) * driftRemainder α₀ < 1) :
    0 < (1 - 69088 * (Fintype.card (Bond L) : ℝ) * driftRemainder α₀)
        / (2 * 69088 * (Fintype.card (Bond L) : ℝ))
      ∧ AggregateFibreBound L U
        ((1 - 69088 * (Fintype.card (Bond L) : ℝ) * driftRemainder α₀)
          / (2 * 69088 * (Fintype.card (Bond L) : ℝ))) := by
  have hNpos := card_bond_pos (L := L)
  refine ⟨div_pos (by linarith [hsmall]) (by positivity), ?_⟩
  intro A hQ
  have hN := card_bond_pos (L := L)
  have hP : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 := pAx_nonneg A _ 2
  have hE := bondEnergy_nonneg A
  have hC := driftRemainder_nonneg hα₀
  have hvol := bondEnergy_le_with_volume_factor hdvd A hQ
  have hcurl := curlEnergy_le_curved hα₀ U hsup A
  -- rearrange the volume bound
  have h2 : bondEnergy A
      ≤ 69088 * (Fintype.card (Bond L) : ℝ) * pAx A (CoarseLattice L 2) 2
        + 69088 * (Fintype.card (Bond L) : ℝ) * curlEnergy A := by linarith [hvol]
  have h1 : 69088 * (Fintype.card (Bond L) : ℝ) * curlEnergy A
      ≤ 69088 * (Fintype.card (Bond L) : ℝ)
        * (2 * deltaKQuadFormNormalizedCorrected U A + driftRemainder α₀ * bondEnergy A) :=
    mul_le_mul_of_nonneg_left hcurl (by positivity)
  have hPN : (0 : ℝ) ≤ 69088 * (Fintype.card (Bond L) : ℝ) * pAx A (CoarseLattice L 2) 2 := by
    positivity
  have hden : (0 : ℝ) < 2 * 69088 * (Fintype.card (Bond L) : ℝ) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [h1, h2, hPN, hP]

#print axioms sum_curlDrift_sq_le
#print axioms driftRemainder
#print axioms driftRemainder_nonneg
#print axioms curlEnergy_le_curved
#print axioms aggregateFibreBound_curved

/-! ## §4 — `κ` DISCHARGED INTO `δ`: the wiring the two source modules could not do

`DeltaPrimeBound.abs_deltaPrimePiForm_le` takes `hlam : siteEnergy lam ≤ κ²·bondEnergy A` with `κ`
a FREE parameter — its own header flags that as hollow read alone. `KappaBound` /
`GammaContourTree` produce exactly that inequality at `κ² = 768`, but **`DeltaPrimeBound` has zero
importers and `KappaBound` deliberately declines to import it**, so the two halves were never
joined. They are joined here: the `κ` slot is filled by a theorem, and no `κ` remains free.

`hmean`, `hweak`, `hadj`, `hproj` are `KappaBound`'s own inputs and are passed through RAW —
deliberately, and per the standing verdict on that module: the ker-membership derivation
(`GammaContourTree.poincare_for_gaugeParam`) is not on the path of `hlam_at_kappa_sq_768_gamma`,
and `Q′` is not yet pinned at source. -/

/-- **`δ` WITH `κ` DISCHARGED.** `|⟨A, Δ′_π A⟩| ≤ Jsup·√768·(28 + 48√768)·bondEnergy A`, with no
free `κ`: the `hlam` slot of `abs_deltaPrimePiForm_le` is filled by
`hlam_at_kappa_sq_768_gamma`. -/
theorem deltaPrimePi_bound_kappa_discharged
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (lam src dstarA : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) (Jsup : ℝ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (hmean : ∀ y ∈ CoarseLattice L 2, ∑ p : Bool × Bool × Bool, gammaM U lam y p = 0)
    (hweak : bondEnergy (AdalyFormal.Balaban.CovariantOperators.gradValueCovariant U lam)
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner
            (AdalyFormal.Balaban.CovariantOperators.gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA)
    (hJ : ∀ b, frobNorm (J b) ≤ Jsup) :
    |deltaPrimePiForm U J lam A| ≤ deltaPiConst Jsup kappaTree * bondEnergy A := by
  have hk : siteEnergy lam ≤ 768 * bondEnergy A :=
    hlam_at_kappa_sq_768_gamma U lam src dstarA A hdvd hmean hweak hadj hproj
  refine abs_deltaPrimePiForm_le U J lam A Jsup kappaTree hJ kappaTree_nonneg ?_
  rw [kappaTree_sq]
  exact hk

/-- **THE SAME AT A REGULAR BACKGROUND, WITH `Jsup` DISCHARGED TOO.**
`DeltaPrimeBound.frobNorm_current_le` supplies `Jsup ≤ 24·η⁻²·α₀` from `GaugeRegular α₀ U`, so the
composed `δ` depends on nothing but `(α₀, η⁻²)` — both `κ` and `Jsup` are now theorems. -/
theorem deltaPrimePi_bound_at_regular_U
    {α₀ etaInvSq : ℝ} (hα₀ : 0 ≤ α₀) (hη : 0 ≤ etaInvSq)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (pl : Bond L → Fin 4 → PeriodicLatticePlaquette L)
    (hJdef : ∀ b, J b = (etaInvSq : ℂ) •
      (AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 0)
        - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 1)
        + AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 2)
        - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 3)))
    (lam src dstarA : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (hmean : ∀ y ∈ CoarseLattice L 2, ∑ p : Bool × Bool × Bool, gammaM U lam y p = 0)
    (hweak : bondEnergy (AdalyFormal.Balaban.CovariantOperators.gradValueCovariant U lam)
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner
            (AdalyFormal.Balaban.CovariantOperators.gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA) :
    |deltaPrimePiForm U J lam A|
      ≤ deltaPiConst (24 * etaInvSq * α₀) kappaTree * bondEnergy A :=
  deltaPrimePi_bound_kappa_discharged U J lam src dstarA A (24 * etaInvSq * α₀) hdvd hmean hweak
    hadj hproj (fun b => frobNorm_current_le hα₀ hη U hreg J pl hJdef b)

#print axioms deltaPrimePi_bound_kappa_discharged
#print axioms deltaPrimePi_bound_at_regular_U

/-! ## §5 — THE FIXED-POINT CRITERION AT THE FIBRE CONSTANT

`q = 1/2` is the source-faithful weighted blocking norm at `ell = 2` and is NOT written as a
literal: `DeltaPrimeBound.weightedQ_two` proves `√(2^{3−5}) = 1/2`, and `criterion_at_weighted_q`
below states the criterion in the derived form.

`γ₀` is the FIBRE constant. `gammaFibre_is_the_fibre_constant` proves the numeral is the one §1
delivers, so nothing here is a fitted number. -/

/-- The level-`0` coercivity constant the composition actually has: `FibreCoercivity`'s. -/
noncomputable def gammaFibre : ℝ := 1 / 69088

theorem gammaFibre_pos : 0 < gammaFibre := by unfold gammaFibre; norm_num

/-- **THE NUMERAL IS WIRED TO §1, not chosen.** `gammaFibre` is exactly the constant of
`composed_coercivity_sup`. -/
theorem gammaFibre_is_the_fibre_constant (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0) :
    gammaFibre * bondSup A
      ≤ deltaKQuadFormNormalizedCorrected (trivialU L) A + pAx A (CoarseLattice L 2) 2 :=
  composed_coercivity_sup hdvd A hQ

/-- **THE CRITERION CLOSES AT `α₀ = 10⁻¹¹`.** `δ = 24·10⁻¹¹·κ(28+48κ) ≤ 9.04·10⁻⁶` against
`γ_fibre·(1 − 1/4) = 3/276352 ≈ 1.0856·10⁻⁵`. Margin `≈1.20×`. -/
theorem criterion_closes_at_gammaFibre :
    deltaPiConst (24 * (1 / 10 ^ 11 : ℝ)) kappaTree ≤ gammaFibre * (1 - (1 / 2 : ℝ) ^ 2) := by
  obtain ⟨hlo, hhi⟩ := kappaPoly_bracket
  rw [deltaPiConst_eq]
  unfold gammaFibre
  nlinarith [hlo, hhi]

/-- **THE THRESHOLD FROM BELOW — `1.2·10⁻¹¹` STILL CLOSES.** Paired with
`criterion_fails_at_thirteen_e_minus_twelve_at_gammaFibre` this pins the admissible boundary
strictly between `1.2·10⁻¹¹` and `1.3·10⁻¹¹`, i.e. to within `8.3%`. -/
theorem criterion_closes_at_twelve_e_minus_twelve_at_gammaFibre :
    deltaPiConst (24 * (12 / 10 ^ 12 : ℝ)) kappaTree ≤ gammaFibre * (1 - (1 / 2 : ℝ) ^ 2) := by
  obtain ⟨hlo, hhi⟩ := kappaPoly_bracket
  rw [deltaPiConst_eq]
  unfold gammaFibre
  nlinarith [hlo, hhi]

/-- **MUST-FIRE, HALF ONE — `4·10⁻¹⁰` FAILS at the fibre constant.** This is F4 as a theorem: the
class `KappaBound.criterion_closes_at_four_e_minus_ten` certifies is certified against
`γ₀ = normGamma = 1/2000`, which is `34.544×` larger than `gammaFibre`. At the constant the
composition actually has, that `α₀` is `≈33×` too big. -/
theorem criterion_fails_at_four_e_minus_ten_at_gammaFibre :
    ¬ (deltaPiConst (24 * (4 / 10 ^ 10 : ℝ)) kappaTree
        ≤ gammaFibre * (1 - (1 / 2 : ℝ) ^ 2)) := by
  obtain ⟨hlo, hhi⟩ := kappaPoly_bracket
  rw [deltaPiConst_eq]
  unfold gammaFibre
  intro hc
  nlinarith [hlo, hhi, hc]

/-- **MUST-FIRE, HALF TWO — THE THRESHOLD IS PINNED TO WITHIN 30%.** At `α₀ = 1.3·10⁻¹¹` the
criterion already fails. With `criterion_closes_at_gammaFibre` this brackets the admissible boundary
strictly between `1.0·10⁻¹¹` and `1.3·10⁻¹¹`, so `10⁻¹¹` is not an arbitrarily small number chosen
to make a statement true. -/
theorem criterion_fails_at_thirteen_e_minus_twelve_at_gammaFibre :
    ¬ (deltaPiConst (24 * (13 / 10 ^ 12 : ℝ)) kappaTree
        ≤ gammaFibre * (1 - (1 / 2 : ℝ) ^ 2)) := by
  obtain ⟨hlo, hhi⟩ := kappaPoly_bracket
  rw [deltaPiConst_eq]
  unfold gammaFibre
  intro hc
  nlinarith [hlo, hhi, hc]

/-- **MUST-NOT-FIRE.** `δ` is strictly positive at the parameters used, so
`criterion_closes_at_gammaFibre` is not a `0 ≤ positive` triviality. -/
theorem deltaPiConst_pos_at_used_point :
    0 < deltaPiConst (24 * (1 / 10 ^ 11 : ℝ)) kappaTree := by
  obtain ⟨hlo, _⟩ := kappaPoly_bracket
  rw [deltaPiConst_eq]
  nlinarith [hlo]

/-- **THE FLOOR, PINNED — no existential over a free starting constant.**
`GammaRecursion.UniformStepGamma` is `∃ γ₀ γmin, …`; that existential is exactly the shape this
campaign prosecutes, so the floor is stated here at the SPECIFIC constant the composition has.
Whenever `δ ≤ γ(1 − q²)`, every level of the recursion `γ_{k+1} = (γ_k − δ)/q²` stays at or above
`γ` itself. -/
theorem gammaSeq_floor_pinned {γ δ q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hfix : δ ≤ γ * (1 - q ^ 2)) (k : ℕ) : γ ≤ gammaSeq γ δ q k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hq2 : (0 : ℝ) < q ^ 2 := by positivity
    have hq2' : q ^ 2 < 1 := by nlinarith
    have hstep : gammaSeq γ δ q (n + 1) = (gammaSeq γ δ q n - δ) / q ^ 2 :=
      AdalyFormal.Balaban.GammaRecursion.gammaSeq_succ γ δ q n
    rw [hstep, le_div_iff₀ hq2]
    nlinarith [ih, hfix, hq2']

/-- **THE ITERATION KEEPS THE FIBRE FLOOR at `α₀ = 10⁻¹¹`**, pinned at `γ_fibre` itself. -/
theorem gammaSeq_floor_at_gammaFibre (k : ℕ) :
    gammaFibre
      ≤ gammaSeq gammaFibre (deltaPiConst (24 * (1 / 10 ^ 11 : ℝ)) kappaTree) (1 / 2 : ℝ) k :=
  gammaSeq_floor_pinned (by norm_num) (by norm_num) criterion_closes_at_gammaFibre k

/-- The unpinned re-export, for consumers that want `GammaRecursion`'s own predicate. -/
theorem uniformStepGamma_at_gammaFibre :
    UniformStepGamma (deltaPiConst (24 * (1 / 10 ^ 11 : ℝ)) kappaTree) (1 / 2 : ℝ) :=
  uniformStepGamma_of_lt_one (γ₀ := gammaFibre) (by norm_num) (by norm_num) gammaFibre_pos
    criterion_closes_at_gammaFibre

/-- **`q` IS THE DERIVED RATIO, NOT A LITERAL.** The same criterion with `q` written as
`√(2^{3−5})`, the weighted blocking norm at `ell = 2` that `DeltaPrimeBound.weightedQ_two`
computes. -/
theorem criterion_at_weighted_q :
    UniformStepGamma (deltaPiConst (24 * (1 / 10 ^ 11 : ℝ)) kappaTree)
      (Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) - 5))) := by
  rw [weightedQ_two]
  exact uniformStepGamma_at_gammaFibre

#print axioms gammaFibre
#print axioms gammaFibre_pos
#print axioms gammaFibre_is_the_fibre_constant
#print axioms criterion_closes_at_gammaFibre
#print axioms criterion_closes_at_twelve_e_minus_twelve_at_gammaFibre
#print axioms criterion_fails_at_four_e_minus_ten_at_gammaFibre
#print axioms criterion_fails_at_thirteen_e_minus_twelve_at_gammaFibre
#print axioms deltaPiConst_pos_at_used_point
#print axioms gammaSeq_floor_pinned
#print axioms gammaSeq_floor_at_gammaFibre
#print axioms uniformStepGamma_at_gammaFibre
#print axioms criterion_at_weighted_q

/-! ## §6 — A GENUINELY CURVED BACKGROUND INSIDE THE TIGHTER CLASS

F4 costs the witness. `GammaContourTree.curvedTinyU = curvedFamilyU 10⁻¹¹` carries only
`frobSupBond ≤ 2√2·10⁻¹¹ ≈ 2.83·10⁻¹¹`, which does NOT establish membership in the `10⁻¹¹` class
that §5's criterion needs. The family is a continuum, so the repair is one line of the family's own
lemmas at a smaller parameter — done here rather than named as a residual. -/

/-- `t = 10⁻¹²`, one decade finer than `GammaContourTree.curvedTiny`. -/
noncomputable def curvedFineT : ℝ := 1 / 10 ^ 12

theorem curvedFineT_pos : 0 < curvedFineT := by unfold curvedFineT; norm_num

/-- A genuinely curved background of the `α₀ ≤ 10⁻¹¹` class — the class in which §5's criterion
closes at the FIBRE constant. -/
noncomputable abbrev curvedFineU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdalyFormal.Balaban.RegularUDomainWitness.witL5 :=
  curvedFamilyU curvedFineT

/-- **IT IS IN THE CLASS.** `2√2·10⁻¹² ≤ 10⁻¹¹` since `2√2 ≤ 4 ≤ 10`. -/
theorem curvedFineU_gaugeRegular : GaugeRegular (1 / 10 ^ 11 : ℝ) curvedFineU := by
  refine gaugeRegular_of_frobSupBond_le ?_
  have h := frobSupBond_curvedFamilyU_le curvedFineT
  have habs : |curvedFineT| = curvedFineT := abs_of_pos curvedFineT_pos
  rw [habs] at h
  refine le_trans h ?_
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs : Real.sqrt 2 ≤ 2 := by nlinarith
  unfold curvedFineT
  nlinarith

/-- **AND IT IS NOT FLAT.** -/
theorem curvedFineU_curved :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (curvedFamilyU curvedFineT) curvedPlaq
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  curvedFamilyU_curvature_ne_one (ne_of_gt curvedFineT_pos)

/-- **THE `10⁻¹¹` CLASS IS INHABITED BY A CURVED BACKGROUND, AND THE CRITERION CLOSES THERE.** The
two halves that §5 and §6 have to deliver jointly, in one statement, so neither can be read without
the other. -/
theorem curved_witness_in_class_and_criterion_closes :
    GaugeRegular (1 / 10 ^ 11 : ℝ) curvedFineU
      ∧ AdalyFormal.Balaban.DeltaPrime.holonomyElem (curvedFamilyU curvedFineT) curvedPlaq
          ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ deltaPiConst (24 * (1 / 10 ^ 11 : ℝ)) kappaTree
          ≤ gammaFibre * (1 - (1 / 2 : ℝ) ^ 2) :=
  ⟨curvedFineU_gaugeRegular, curvedFineU_curved, criterion_closes_at_gammaFibre⟩

#print axioms curvedFineT
#print axioms curvedFineT_pos
#print axioms curvedFineU
#print axioms curvedFineU_gaugeRegular
#print axioms curvedFineU_curved
#print axioms curved_witness_in_class_and_criterion_closes

/-! ## §7 — THE COMPOSED LEMMA

Two statements, deliberately separated.

* **`composed_coercivity_unconditional`** — everything the five pieces discharge TODAY, with no
  open hypothesis at all beyond the extent's tileability. It is at the flat background and in the
  `ℓ^∞` norm (F2, F3), and it is non-vacuous.
* **`composed_coercivity_general`** — the general-`U`, `L²`, iterated form, with every open leg an
  explicit NAMED binder: `hagg` (the volume-free aggregate fibre bound), `hmean`/`hweak`/`hadj`/
  `hproj` (`KappaBound`'s inputs), `hJdef` (the current's shape), `hcrit` (the criterion at the
  binder's own constant). ~~No binder is free data: each carries a hypothesis that forces
  content~~ **CORRECTION (2026-08-01, `compute/kimi_composed/VERDICT.md` §Q6(b)): this contradicted
  the `hJdef` bullet's own F-disclosure below, which states `pl` IS free data.** Scoped correctly:
  every OTHER binder carries a hypothesis that forces content; `pl` does not — `hJdef` only pins `J`
  to a formula in `pl`, and `pl` itself is unconstrained (the disclosed under-constraint the
  `hJdef` bullet below names). `§3`/`§6` exhibit inhabitants of the two classes that could otherwise
  be empty. -/

/-- **THE COMPOSED LEMMA, UNCONDITIONAL PART.** At every periodic extent with `2 ∣ (L μ + 1)`, at
block side `2` and the flat background, the three-clause form is coercive in `ℓ^∞` with the explicit
constant `1/69088`, the aggregate `L²` form holds at `1/(69088·N)`, and the left-hand side is not
identically zero. -/
theorem composed_coercivity_unconditional (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    (∀ A : Bond L → SuTwo,
        (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
          lineCoarseRestrictCov (trivialU L) 2 A b = 0) →
        gammaFibre * bondSup A
          ≤ deltaKQuadFormNormalizedCorrected (trivialU L) A + pAx A (CoarseLattice L 2) 2)
      ∧ AggregateFibreBound L (trivialU L) (1 / (69088 * (Fintype.card (Bond L) : ℝ)))
      ∧ 0 < gammaFibre
      ∧ 0 < bondSup (altMode (L := L) AdalyFormal.Balaban.BridgeRestricted.rotGen) :=
  ⟨fun A hQ => gammaFibre_is_the_fibre_constant hdvd A hQ,
    aggregateFibreBound_volume_costed hdvd,
    gammaFibre_pos,
    bondSup_altMode_rotGen_pos⟩

/-- **THE COMPOSED LEMMA, GENERAL FORM.** Every open leg is a named binder.

Conclusion, four clauses:
1. the `L²` three-clause coercivity at the binder's own constant `γstar`, **at the general
   background `U`** — `AggregateFibreBound L U γstar` carries `U` in the OPERATOR (§3b discharges
   it at a curved `U`); its `{Q A = 0}` clause is still the flat one, which is why `hQ` below is
   stated at `trivialU L`;
2. the volume-free `ℓ^∞` coercivity at `1/69088` — this one needs NO binder, and it is flat in
   both the operator and the clause;
3. the `(3.120)` correction bounded by `δ = 24·η⁻²·α₀·√768·(28 + 48√768)`, with both `κ` and `Jsup`
   discharged from theorems;
4. the iterated bridge keeps the floor `γstar` at EVERY level `k` **and stays strictly positive
   there** — pinned at the binder's own constant, not an existential over a free starting constant
   as `GammaRecursion.UniformStepGamma` is. The positivity half is what consumes `hγstar`, so that
   binder is load-bearing rather than decorative: without it a hostile `γstar ≤ 0` would satisfy
   clause 1 and the floor half trivially.

`hcrit` is the only place where the three constants meet, and it is stated at `γstar`, so a consumer
that later discharges `hagg` volume-freely gets clause 4 at that constant with no restatement.

**DISCLOSURE (2026-08-01, `compute/composed_prosecution/VERDICT.md` item A/B): clause 2 is
padding.** Clause 2's proof term is `gammaFibre_is_the_fibre_constant hdvd A hQ`, which is
`composed_coercivity_sup` from §1 — byte-for-byte, restated inside this theorem — and it touches
NONE of the "general" binders: not `U`, `hreg`, `γstar`, `hagg`, `hcrit`, `hmean`, `hweak`, `hadj`,
`hproj`, `J`, `pl`, or `hJdef`. It is true and it is not hidden (the bullet above already says
clause 2 "needs NO binder" and is "flat in both the operator and the clause"), but a reader who
takes "four clauses, every open leg a named binder" to mean all four clauses depend on the general
machinery is reading it wrong: only clauses 1, 3, 4 do. The four-clause count overstates the
theorem's general-binder content by exactly one clause. The clause is NOT removed — removing it
would be a statement change, and the two grade-2 modules restating this theorem's conclusions
byte-identically forbid that.

**DISCLOSURE (2026-08-01, `compute/kimi_composed/VERDICT.md` §Q1): item 3's `hJdef` bullet above
admits an `etaInvSq := 0` route that the `pl`-degeneracy disclosure below does not close.** `hη :
0 ≤ etaInvSq` admits `etaInvSq := 0`. At that value `hJdef` is discharged by `J := 0` for EVERY
`pl` — including the `truePlStar`-pinned repair the `pl`-disclosure below names as the fix — because
`(0 : ℂ) • x = 0` regardless of which plaquettes `pl` selects. `hcrit` then collapses to
`deltaPiConst 0 kappaTree = 0 ≤ γstar * (1 - (1/2)²)`, vacuous, and clause 3 collapses to `|0| ≤ 0`
at every background. This route is cheaper than the disclosed `pl`-degeneracy: it needs no choice of
`pl` at all, only `etaInvSq := 0`. The instantiations below (`JointInstantiation.
joint_instantiation_flat`/`joint_instantiation_curved`) use `etaInvSq := 1`, so the exhibited
non-vacuous cases do not take this route — but the headline binder `hη` still admits it, and closing
it (`0 < etaInvSq`) is a statement change, not made here. -/
theorem composed_coercivity_general
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    -- the background, and the regularity class
    {α₀ etaInvSq : ℝ} (hα₀ : 0 ≤ α₀) (hη : 0 ≤ etaInvSq)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U)
    -- the curvature current, at (3.120)'s shape
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (pl : Bond L → Fin 4 → PeriodicLatticePlaquette L)
    (hJdef : ∀ b, J b = (etaInvSq : ℂ) •
      (AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 0)
        - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 1)
        + AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 2)
        - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 3)))
    -- the field, and the coarse-average-free clause
    (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    -- KappaBound's own inputs, carried RAW
    (lam src dstarA : PeriodicLatticeSite L → SuTwo)
    (hmean : ∀ y ∈ CoarseLattice L 2, ∑ p : Bool × Bool × Bool, gammaM U lam y p = 0)
    (hweak : bondEnergy (AdalyFormal.Balaban.CovariantOperators.gradValueCovariant U lam)
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner
            (AdalyFormal.Balaban.CovariantOperators.gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA)
    -- the L² fibre leg, NAMED
    {γstar : ℝ} (hγstar : 0 < γstar) (hagg : AggregateFibreBound L U γstar)
    -- the criterion, at THAT constant
    (hcrit : deltaPiConst (24 * etaInvSq * α₀) kappaTree ≤ γstar * (1 - (1 / 2 : ℝ) ^ 2)) :
    γstar * bondEnergy A
        ≤ deltaKQuadFormNormalizedCorrected U A + pAx A (CoarseLattice L 2) 2
      ∧ gammaFibre * bondSup A
        ≤ deltaKQuadFormNormalizedCorrected (trivialU L) A + pAx A (CoarseLattice L 2) 2
      ∧ |deltaPrimePiForm U J lam A|
        ≤ deltaPiConst (24 * etaInvSq * α₀) kappaTree * bondEnergy A
      ∧ ∀ k : ℕ,
          0 < gammaSeq γstar (deltaPiConst (24 * etaInvSq * α₀) kappaTree) (1 / 2 : ℝ) k
            ∧ γstar
              ≤ gammaSeq γstar (deltaPiConst (24 * etaInvSq * α₀) kappaTree) (1 / 2 : ℝ) k :=
  ⟨hagg A hQ,
    gammaFibre_is_the_fibre_constant hdvd A hQ,
    deltaPrimePi_bound_at_regular_U hα₀ hη U hreg J pl hJdef lam src dstarA A hdvd hmean hweak
      hadj hproj,
    fun k => ⟨lt_of_lt_of_le hγstar (gammaSeq_floor_pinned (by norm_num) (by norm_num) hcrit k),
      gammaSeq_floor_pinned (by norm_num) (by norm_num) hcrit k⟩⟩

#print axioms composed_coercivity_unconditional
#print axioms composed_coercivity_general

/-! ## §8 — THE HYPOTHESIS CLASSES OF §7 ARE NOT EMPTY

Three of `composed_coercivity_general`'s binders could in principle be unsatisfiable, which would
make the theorem vacuous. Each is exhibited inhabited here, at the tree's own witness geometry
`witL5 = fun _ => 5` (where `2 ∣ 6`, so `hdvd` is discharged by `decide`). ~~What is NOT exhibited
is a simultaneous inhabitant of `hmean`/`hweak`/`hadj`/`hproj` — those are `KappaBound`'s open
inputs and are the subject of a separate lane; §7 carries them as binders precisely for that
reason.~~ **CORRECTION (2026-08-01, `compute/kimi_composed/VERDICT.md` §Q6(c)): STALE.**
`AdalyFormal.Balaban.JointInstantiation.joint_instantiation_flat` exhibits exactly such a
simultaneous inhabitant, at the flat background (all four supplied: `hmean_altSite`,
`hweak_of_gradCovariantAdjoint`, `hadj_of_gradCovariantAdjoint`, `hproj_altConfig`), and
`AdalyFormal.Balaban.JointInstantiation.joint_instantiation_curved` exhibits another at a genuinely
curved background; `hweak`/`hadj` themselves are discharged for EVERY `U`/`λ`/`A` by
`hweak_of_gradCovariantAdjoint`/`hadj_of_gradCovariantAdjoint`. -/

open AdalyFormal.Balaban.RegularUDomainWitness (witL5)

theorem hdvd_witL5 : ∀ μ : Fin 3, (2 : ℕ) ∣ (witL5 μ + 1) :=
  AdalyFormal.Balaban.FibreCoercivity.hdvd_witL5

/-- **`hagg` IS INHABITED** at `witL5`, at a strictly positive constant. -/
theorem hagg_inhabited_at_witL5 :
    0 < 1 / (69088 * (Fintype.card (Bond witL5) : ℝ))
      ∧ AggregateFibreBound witL5 (trivialU witL5) (1 / (69088 * (Fintype.card (Bond witL5) : ℝ))) := by
  refine ⟨?_, aggregateFibreBound_volume_costed hdvd_witL5⟩
  have hN := card_bond_pos (L := witL5)
  positivity

/-- **`hreg` IS INHABITED BY A CURVED BACKGROUND, AND `hcrit` HOLDS THERE** — at `η⁻² = 1`,
`α₀ = 10⁻¹¹`, `γstar = gammaFibre`. The three facts §7 needs from §5/§6, together. -/
theorem hreg_and_hcrit_inhabited :
    GaugeRegular (1 / 10 ^ 11 : ℝ) curvedFineU
      ∧ AdalyFormal.Balaban.DeltaPrime.holonomyElem (curvedFamilyU curvedFineT) curvedPlaq
          ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ deltaPiConst (24 * 1 * (1 / 10 ^ 11 : ℝ)) kappaTree
          ≤ gammaFibre * (1 - (1 / 2 : ℝ) ^ 2) := by
  refine ⟨curvedFineU_gaugeRegular, curvedFineU_curved, ?_⟩
  have h := criterion_closes_at_gammaFibre
  have hrw : (24 : ℝ) * 1 * (1 / 10 ^ 11 : ℝ) = 24 * (1 / 10 ^ 11 : ℝ) := by ring
  rw [hrw]
  exact h

/-- **`hQ` IS INHABITED BY A NONZERO FIELD.** `FibreCoercivity.altMode` is coarse-average-free and
nonzero, so the subspace `{Q A = 0}` on which §7's clauses live is not `{0}`. -/
theorem hQ_inhabited_at_witL5 :
    (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2,
        lineCoarseRestrictCov (trivialU witL5) 2
          (altMode AdalyFormal.Balaban.BridgeRestricted.rotGen) b = 0)
      ∧ 0 < bondSup (altMode (L := witL5) AdalyFormal.Balaban.BridgeRestricted.rotGen) :=
  ⟨AdalyFormal.Balaban.FibreCoercivity.altMode_Q hdvd_witL5
      AdalyFormal.Balaban.BridgeRestricted.rotGen,
    bondSup_altMode_rotGen_pos⟩

/-! ### §8b — `AggregateFibreBound` AT A CURVED OPERATOR IS INHABITED TOO

`aggregateFibreBound_curved` carries a smallness condition `69088·N·driftRemainder α₀ < 1`. A
condition no background meets would make §3b vacuous. It is met, at every extent, by scaling the
curved family with the volume — and the resulting background is genuinely curved. No numeric
evaluation of `Fintype.card (Bond witL5)` is needed: the witness is defined IN TERMS of it. -/

/-- The volume-scaled curvature parameter `t = 1/(10¹⁰·N)`. -/
noncomputable def curvedVolT : ℝ := 1 / (10 ^ 10 * (Fintype.card (Bond witL5) : ℝ))

/-- The regularity radius it lands in, `α₀ = 1/(10⁹·N)`. -/
noncomputable def curvedVolAlpha : ℝ := 1 / (10 ^ 9 * (Fintype.card (Bond witL5) : ℝ))

theorem curvedVolT_pos : 0 < curvedVolT := by
  unfold curvedVolT
  have := card_bond_pos (L := witL5)
  positivity

theorem curvedVolAlpha_pos : 0 < curvedVolAlpha := by
  unfold curvedVolAlpha
  have := card_bond_pos (L := witL5)
  positivity

/-- `N·α₀ = 10⁻⁹` exactly — the identity that makes the smallness condition volume-free. -/
theorem card_mul_curvedVolAlpha :
    (Fintype.card (Bond witL5) : ℝ) * curvedVolAlpha = 1 / 10 ^ 9 := by
  have hN := card_bond_pos (L := witL5)
  unfold curvedVolAlpha
  field_simp

theorem curvedVolAlpha_le : curvedVolAlpha ≤ 1 / 10 ^ 9 := by
  have hN : (1 : ℝ) ≤ (Fintype.card (Bond witL5) : ℝ) := by
    have h : 0 < Fintype.card (Bond witL5) :=
      Fintype.card_pos_iff.mpr ⟨(zeroSite witL5, (0 : Fin 3))⟩
    exact_mod_cast h
  unfold curvedVolAlpha
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hN]

/-- **THE SMALLNESS CONDITION IS MET.** `69088·N·driftRemainder α₀ ≤ 69088·545·10⁻⁹ ≈ 0.0377 < 1`.
The `N` cancels against `α₀`'s own `1/N`, so the margin is volume-INDEPENDENT — a factor `≈26`. -/
theorem curvedVol_smallness :
    69088 * (Fintype.card (Bond witL5) : ℝ) * driftRemainder curvedVolAlpha < 1 := by
  have hN := card_bond_pos (L := witL5)
  have ha0 := le_of_lt curvedVolAlpha_pos
  have hale := curvedVolAlpha_le
  have hNa := card_mul_curvedVolAlpha
  have h1 : driftRemainder curvedVolAlpha ≤ 545 * curvedVolAlpha := by
    unfold driftRemainder
    nlinarith [ha0, hale]
  have h2 : 69088 * (Fintype.card (Bond witL5) : ℝ) * driftRemainder curvedVolAlpha
      ≤ 69088 * (Fintype.card (Bond witL5) : ℝ) * (545 * curvedVolAlpha) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [h2, hNa]

/-- The curved witness at the volume-scaled parameter. -/
noncomputable abbrev curvedVolU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5 :=
  curvedFamilyU curvedVolT

theorem curvedVolU_frobSup : frobSupBond curvedVolU ≤ curvedVolAlpha := by
  have hN := card_bond_pos (L := witL5)
  have h := frobSupBond_curvedFamilyU_le curvedVolT
  rw [abs_of_pos curvedVolT_pos] at h
  refine le_trans h ?_
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs : Real.sqrt 2 ≤ 2 := by nlinarith
  unfold curvedVolT curvedVolAlpha
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hN, hs, hs0,
    mul_nonneg (sub_nonneg.mpr hs) (le_of_lt hN)]

/-- **§3b IS NOT ABOUT AN EMPTY CLASS.** At `witL5` the aggregate fibre bound holds with a
GENUINELY CURVED operator, at a strictly positive explicit constant. -/
theorem aggregateFibreBound_curved_inhabited :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem curvedVolU curvedPlaq
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ 0 < (1 - 69088 * (Fintype.card (Bond witL5) : ℝ) * driftRemainder curvedVolAlpha)
          / (2 * 69088 * (Fintype.card (Bond witL5) : ℝ))
      ∧ AggregateFibreBound witL5 curvedVolU
          ((1 - 69088 * (Fintype.card (Bond witL5) : ℝ) * driftRemainder curvedVolAlpha)
            / (2 * 69088 * (Fintype.card (Bond witL5) : ℝ))) := by
  have hN := card_bond_pos (L := witL5)
  obtain ⟨hpos, hbound⟩ :=
    aggregateFibreBound_curved hdvd_witL5 (le_of_lt curvedVolAlpha_pos) curvedVolU
      curvedVolU_frobSup curvedVol_smallness
  exact ⟨curvedFamilyU_curvature_ne_one (ne_of_gt curvedVolT_pos), hpos, hbound⟩

#print axioms hdvd_witL5
#print axioms curvedVolT
#print axioms curvedVolAlpha
#print axioms curvedVolT_pos
#print axioms curvedVolAlpha_pos
#print axioms card_mul_curvedVolAlpha
#print axioms curvedVolAlpha_le
#print axioms curvedVol_smallness
#print axioms curvedVolU
#print axioms curvedVolU_frobSup
#print axioms aggregateFibreBound_curved_inhabited
#print axioms hagg_inhabited_at_witL5
#print axioms hreg_and_hcrit_inhabited
#print axioms hQ_inhabited_at_witL5

/-! ## §9 — WHAT IS **NOT** PROVED HERE, stated so nobody over-reads §7

* **The `Q` clause is flat everywhere.** After §3b, clause 1 of `composed_coercivity_general` IS
  at the general `U` (through `AggregateFibreBound L U γstar`), but its subspace `{Q A = 0}` is
  still cut out by `lineCoarseRestrictCov (trivialU L)`. Clause 2 (`ℓ^∞`) is flat in BOTH the
  operator and the clause. §3b's closing note names the missing covariant-`Q` primitive.
* **§3b costs a factor `2`** against `aggregateFibreBound_volume_costed` at `α₀ = 0` — the `sq_two`
  Cauchy–Schwarz slack. It is in the statement, not absorbed.
* **No volume-free `L²` fibre bound.** `hagg` is discharged here only at `1/(69088·N)`;
  `alphaThreshold_scales_with_volume` prices exactly what a volume-free discharge is worth.
* **`γ_split` is not used.** F1. `SplitBaseCase` is imported for its refutations
  (`fine_energy_base_case_refuted`, `coarse_bond_energy_base_case_refuted`,
  `levelCorrectedCoercivityTargetUniform_refuted`), which are what rule out the two shapes the
  composed statement might otherwise have been given.
* **`AxialCoercivity.norm_sq_tree_bond_le_pAx` is NOT consumed**, per the standing note that it is
  overclaimed (direction-`0` bonds only).
* **`SplitBaseCase.split_base_case_sandwich` is NOT consumed**: it takes `Dinv` with no `hinv`
  hypothesis, so it holds for an arbitrary `Dinv` and is not the `(3.157)` reparametrisation
  reading.
* **`hmean` is not derived.** It is a binder, deliberately. -/

end AdalyFormal.Balaban.ComposedCoercivity
