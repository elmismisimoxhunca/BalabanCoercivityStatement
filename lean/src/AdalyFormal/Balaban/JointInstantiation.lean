/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.QPrimeDenotation
import AdalyFormal.Balaban.FibreAggregate
import AdalyFormal.Balaban.RegularUDirectCoercivity

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-!
# `JointInstantiation.lean` — the composed lemma, AT A CONFIGURATION

Lane record: `compute/joint_instantiation/PROGRESS.md`.

`ComposedCoercivity.composed_coercivity_general` is a conditional theorem with 23 binders. Its §9
lists what is NOT proved there; `QPrimeDenotation` §9 discharged the `hmean` leg in SHAPE (through
`ker Q′`). This module discharges the REMAINING interface legs — `hweak`, `hadj`, `hproj` — with
CONSTRUCTED witnesses, and instantiates the whole binder conjunction at ONE concrete configuration,
at the flat background AND at a genuinely curved one.

## What is actually new here, stated as facts

1. **`hadj` and `hweak` are not open at all — the tree already contained their witnesses.**
   `CovariantHjMinimizer` §5 builds `D_U^*` explicitly (`gradCovariantAdjointValue`) and proves
   `covBondInner (D_U λ) A = covSiteInner λ (D_U^* A)`
   (`covBondInner_gradValueCovariant_eq_covSiteInner`). Taking `dstarA := D_U^* A` discharges
   `hadj` for EVERY `U` and EVERY `A`; taking `src := D_U^* D_U λ` discharges `hweak` for EVERY `U`
   and EVERY `λ`. §1 does exactly that and nothing more.
   **`KappaBound`'s own §1a says, verbatim, "`Dstar` (the adjoint `D_U^*`) is NOT constructed."**
   That sentence is stale inside its own import closure: `KappaBound` opens
   `CovariantHjMinimizer (covSiteInner periodicLatticeShiftEquiv)`, i.e. it already imports the
   module in which `D_U^*` is constructed. Recorded as a FINDING, not repaired (write scope).

2. **`hproj` is the only genuinely configuration-dependent leg**, and it is an inequality between
   two divergences, `siteEnergy (D_U^*D_U λ) ≤ siteEnergy (D_U^* A)`. §2 computes both sides in
   closed form at the alternating configuration and discharges it with a factor-`4` margin. §7's
   `hproj_fails_at_unit_ratio` shows the leg is NOT vacuous: at the same configuration with the
   ratio parameter `c = 1` it is FALSE.

3. **The admissible `α₀` at the volume-free aggregate constant.** `ComposedCoercivity` §5 pins the
   threshold at `≈1.2·10⁻¹¹` for `γ_fibre = 1/69088`. At `FibreAggregate`'s `γ_agg = 1/3316224`
   (the iterable, `L`-free constant) the threshold tightens by the multiplicity factor `48`:
   §3 proves it CLOSES at `2.5·10⁻¹³` and FAILS at `2.6·10⁻¹³`, and that the old `1.2·10⁻¹¹`
   fails outright.

4. **A volume-free CURVED aggregate bound.** `ComposedCoercivity.aggregateFibreBound_curved` runs
   the drift argument on `bondEnergy_le_with_volume_factor` and therefore carries `Fintype.card
   (Bond L)`. §4 runs the SAME argument on `FibreAggregate.aggregate_fibre_bound` instead and
   carries no volume at all: `γ_c(α₀) = (1 − 3316224·(544α₀+64α₀²))/(2·3316224)`.
   The transfer cost consumed here is the LINEAR-dominated `driftRemainder α₀ = 544α₀ + 64α₀²`,
   so it is the `544α₀` term that sets the threshold, and §6 derives that threshold two-sided
   (`1.2·10⁻¹³` closes, `1.3·10⁻¹³` fails) rather than reusing any envelope arithmetic.

5. **The joint instantiation.** §5 (flat) and §6 (curved) each produce the full four-clause
   conclusion of `composed_coercivity_general` with EVERY binder discharged, at `L = witL5`
   (extent `6`, `2 ∣ 6` — the one extent at which the fibre side and the curved-witness side are
   both available), and with clauses 1, 2 non-vacuous (`§7`).

6. **F2's open half, closed AT THE CONFIGURATION (§8).** `ComposedCoercivity` F2 records that
   `AggregateFibreBound`'s `{Q A = 0}` clause stays the FLAT `lineCoarseRestrictCov (trivialU L)`
   even at a curved operator, and that the general repair is inside `FibreCoercivity`'s chain. The
   instantiation does not need the general repair: at this configuration the covariant `Q_2(U)` and
   the flat `Q_2(1)` are EQUAL on the field (`lineCoarseRestrictCov_eq_flat_of_line`), because every
   path holonomy of the background fixes `rotGen` and every value of `altMode rotGen` lies on
   `ℝ·rotGen`. So `altMode_Q_covariant` gives `Q_2(curvedAggU)(altMode rotGen) = 0` EXACTLY — not
   up to `WindowStokesGeneralU.norm_lineCoarse_cov_sub_flat_le_block`'s `8α/ℓ³`, which bounds a
   difference that is identically `0` here.

7. **`L`-freeness of the instantiation (§9).** The flat instantiation is stated generically in the
   extent and exhibited at `4³` and at `6³`, whose bond counts differ (`192 ≠ 648`), with the SAME
   constant `γ_agg` — which a volume-costed constant could not do.

## ⚠ WHAT THIS DOES **NOT** DELIVER — measured, not hedged

* **Clause 3's left-hand side is IDENTICALLY ZERO at this configuration**, and §7 proves it
  (`deltaPrimePiForm_eq_zero_at_config`). The reason is structural and is worth stating exactly:
  every term of `DeltaPrimeBound.piBondValue` is an `iComm` of a `λ`-value against an `A`-value,
  `iComm X Y = i(XY − YX)` is alternating, and at this configuration `λ` and `A` are COLLINEAR in
  `𝔰𝔲(2)` (both proportional to `rotGen`). Collinearity is forced, not chosen: the curved
  background's only non-trivial link is `curvedBond`, whose DIRECTION IS `0`
  (`curvedBond = freeBond 2 (siteZero witL5)` and `freeBond ell y = (…, (0 : Fin 3))`), so both the
  `λ`-side and the `A`-side must lie in the fixed line of `RMap (rotElem t)` for the transports to
  cancel. A clause-3-non-vacuous configuration therefore needs either a curved witness on a
  direction-`≠0` bond or a perturbative (non-exact) treatment of the transport defect; neither is
  built here.
* **At the FLAT background clause 3 is zero for a second, independent reason**: `J` is the
  `(3.120)` current and `imHolonomy (trivialU L) p = 0`, so `J ≡ 0` (`jointJ_trivialU_eq_zero`).
* **`pl` is unconstrained data in `composed_coercivity_general`.** `hJdef` only says `J` has the
  four-plaquette SHAPE at the given `pl`; nothing pins `pl` to the four plaquettes containing the
  bond. So `hJdef` is dischargeable by DEFINING `J`, which is what §5 does. The bound of clause 3
  is uniform over all `pl`, which is stronger than needing the true one — but the theorem never
  pins `J` to the actual current, and that is a statement-level fact about the headline, recorded
  here rather than left for a prosecutor.
* ~~**The `Q` clause is flat.** Inherited verbatim from `AggregateFibreBound`'s definition (F2 of
  `ComposedCoercivity`); nothing here changes it.~~ **SUPERSEDED IN THE SAME PASS by §8** (S75,
  struck in place rather than deleted). The DEFINITION `AggregateFibreBound` still carries the flat
  clause — that is unchanged and is not repairable from outside `FibreCoercivity`. What §8 shows is
  that AT THE INSTANTIATED CONFIGURATION the flat clause and the covariant clause are the SAME
  statement, so `joint_instantiation_curved`'s `hQ` is not a weaker hypothesis than the covariant
  one would be. The general case remains as `ComposedCoercivity` §3b describes it.
-/

namespace AdalyFormal.Balaban.JointInstantiation

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one RMap_mul_apply gradValueCovariant)
open AdalyFormal.Balaban.CovariantHj (covBondInner)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU covSiteInner gradCovariantAdjointValue
  periodicLatticeShiftBack periodicLatticeShift_shiftBack
  covBondInner_gradValueCovariant_eq_covSiteInner)
open AdalyFormal.Balaban.GeneralUHodgeDrift (siteEnergy siteEnergy_nonneg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg frobSupBond)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.AxialCoercivity (pAx pAx_nonneg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeRegular gaugeRegular_of_frobSupBond_le)
open AdalyFormal.Balaban.FibreCoercivity (par par_ne par_shift0 altMode altMode_eq altMode_ne
  altMode_Q zeroSite zeroSite_even curlEnergy)
open AdalyFormal.Balaban.GammaContourTree (gammaM gammaTransport gCorner gCorner_true gCorner_false
  gInner)
open AdalyFormal.Balaban.FibreAggregate (gammaAgg gammaAgg_eq gammaAgg_pos aggregate_fibre_bound
  aggregate_fibre_bound_gamma)
open AdalyFormal.Balaban.ComposedCoercivity (kappaTree kappaTree_sq kappaTree_nonneg
  kappaPoly_bracket deltaPiConst_eq AggregateFibreBound driftRemainder driftRemainder_nonneg
  curlEnergy_le_curved bondSup bondSup_altMode_pos gammaFibre composed_coercivity_general)
open AdalyFormal.Balaban.DeltaPrimeBound (deltaPiConst deltaPrimePiForm piBondValue iComm)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5 frobSupBond_trivialU)
open AdalyFormal.Balaban.RegularUCurvedWitness (curvedFamilyU curvedPlaq curvedBond bondU bondU_at
  bondU_off curvedFamilyU_curvature_ne_one frobSupBond_curvedFamilyU_le)
open AdalyFormal.Balaban.BridgeRestricted (rotGen rotGen_ne_zero RMap_rotElem_rotGen)
open AdalyFormal.Balaban.NonFlatBackground (rotElem)
open AdalyFormal.Balaban.RegularUDirectCoercivity (covBondInner_eq_bondEnergy)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `hadj` AND `hweak`, DISCHARGED FOR EVERY BACKGROUND AND EVERY FIELD

Nothing is constructed in this section: both witnesses are `CovariantHjMinimizer` §5's, applied.
LAW-19 — the adjoint is not rebuilt here. -/

/-- **`hadj`'s WITNESS: `dstarA := D_U^* A`.** This is `composed_coercivity_general`'s `hadj`
binder verbatim, discharged with no hypothesis on `U` or `A` whatsoever. -/
theorem hadj_of_gradCovariantAdjoint
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    ∀ w : PeriodicLatticeSite L → SuTwo,
      covSiteInner w (gradCovariantAdjointValue U A)
        = covBondInner (gradValueCovariant U w) A :=
  fun w => (covBondInner_gradValueCovariant_eq_covSiteInner U w A).symm

/-- **`hweak`'s WITNESS: `src := D_U^* D_U λ`.** The weak Euler–Lagrange identity of
`composed_coercivity_general`, discharged with no hypothesis on `U` or `λ`. It is the Gram identity
`⟨λ, D^*Dλ⟩ = ⟨Dλ, Dλ⟩ = bondEnergy (Dλ)`. -/
theorem hweak_of_gradCovariantAdjoint
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) :
    bondEnergy (gradValueCovariant U lam)
      = covSiteInner lam (gradCovariantAdjointValue U (gradValueCovariant U lam)) := by
  rw [← covBondInner_eq_bondEnergy]
  exact covBondInner_gradValueCovariant_eq_covSiteInner U lam (gradValueCovariant U lam)

#print axioms hadj_of_gradCovariantAdjoint
#print axioms hweak_of_gradCovariantAdjoint

/-! ## §2 — THE ALTERNATING CONFIGURATION, AND `hproj`

The field is `FibreCoercivity.altMode w` (already known `Q`-free and nonzero); the gauge parameter
is its SITE analogue `altSite v`. Both the covariant gradient and the covariant divergence collapse
to closed forms under one hypothesis on the background:

`hUw : ∀ b, RMap (U b) w = w` — the fibre direction is fixed by every link's adjoint action.

That hypothesis holds at `trivialU` (`RMap 1 = id`) and at `curvedFamilyU t` with `w = rotGen`
(`BridgeRestricted.RMap_rotElem_rotGen`), which is why one configuration serves both §5 and §6. -/

/-- The site-level alternating mode `λ_v(x) = par(x)·v`, the exact site analogue of
`FibreCoercivity.altMode`. -/
noncomputable def altSite (v : SuTwo) : PeriodicLatticeSite L → SuTwo := fun x => par x • v

theorem altSite_apply (v : SuTwo) (x : PeriodicLatticeSite L) : altSite v x = par x • v := rfl

theorem par_sq (z : PeriodicLatticeSite L) : par z ^ 2 = 1 := by
  unfold par; split_ifs <;> norm_num

theorem norm_smul_sq (a : ℝ) (v : SuTwo) : ‖a • v‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- The backward companion of `FibreCoercivity.par_shift0`. -/
theorem par_shiftBack0 (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (y : PeriodicLatticeSite L) :
    par (periodicLatticeShiftBack y 0) = - par y := by
  have h := par_shift0 hdvd (periodicLatticeShiftBack y 0)
  rw [periodicLatticeShift_shiftBack] at h
  linarith

/-- If a link's adjoint action fixes `v`, so does its inverse's. -/
theorem RMap_inv_fix {g : Matrix.specialUnitaryGroup (Fin 2) ℂ} {v : SuTwo}
    (h : RMap g v = v) : RMap g⁻¹ v = v := by
  have hc := RMap_mul_apply g⁻¹ g v
  rw [h, inv_mul_cancel, RMap_one] at hc
  simpa using hc

/-- Fixing `v` fixes the whole line `ℝ·v`. -/
theorem RMap_fix_smul {g : Matrix.specialUnitaryGroup (Fin 2) ℂ} {v : SuTwo}
    (h : RMap g v = v) (c : ℝ) : RMap g (c • v) = c • v := by
  rw [map_smul, h]

/-- **THE COVARIANT GRADIENT OF `altSite v` IS AN `altMode`.**
`D_U(altSite v) = altMode ((−2)·v)` whenever every link fixes `v`. Direction `0` picks up the
parity flip (`par_shift0`); the transverse directions cancel exactly (`par_ne` plus the fixing
hypothesis). -/
theorem grad_altSite (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {v : SuTwo}
    (hUv : ∀ b : Bond L, RMap (U b) v = v) :
    gradValueCovariant U (altSite v) = altMode ((-2 : ℝ) • v) := by
  funext b
  obtain ⟨x, μ⟩ := b
  by_cases hμ : μ = 0
  · subst hμ
    rw [altMode_eq ((-2 : ℝ) • v) (b := ((x, (0 : Fin 3)) : Bond L)) rfl]
    show RMap (U (x, (0 : Fin 3))) (altSite v (periodicLatticeShift x 0)) - altSite v x = _
    rw [altSite_apply, altSite_apply, par_shift0 hdvd x, map_smul, hUv, smul_smul, neg_smul]
    show -(par x • v) - par x • v = (par x * (-2 : ℝ)) • v
    rw [show par x * (-2 : ℝ) = -(par x) + -(par x) by ring, add_smul, neg_smul]
    abel
  · rw [altMode_ne ((-2 : ℝ) • v) (b := ((x, μ) : Bond L)) hμ]
    show RMap (U (x, μ)) (altSite v (periodicLatticeShift x μ)) - altSite v x = 0
    rw [altSite_apply, altSite_apply, par_ne x hμ, map_smul, hUv, sub_self]

/-- **THE COVARIANT DIVERGENCE OF AN `altMode` IS A SITE ALTERNATION.**
`D_U^*(altMode w)(y) = (−2·par y)·w` whenever every link fixes `w`. Only the direction-`0` term
survives, because `altMode` is supported in direction `0`. -/
theorem dstar_altMode (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {w : SuTwo}
    (hUw : ∀ b : Bond L, RMap (U b) w = w) (y : PeriodicLatticeSite L) :
    gradCovariantAdjointValue U (altMode w) y = ((-2 : ℝ) * par y) • w := by
  show (∑ μ : Fin 3, (RMap (U (periodicLatticeShiftBack y μ, μ))⁻¹
      (altMode w (periodicLatticeShiftBack y μ, μ)) - altMode w (y, μ))) = _
  rw [Fin.sum_univ_three]
  have hd10 : (1 : Fin 3) ≠ 0 := by decide
  have hd20 : (2 : Fin 3) ≠ 0 := by decide
  have h1 : altMode w ((periodicLatticeShiftBack y (1 : Fin 3)), (1 : Fin 3)) = 0 :=
    altMode_ne w (b := ((periodicLatticeShiftBack y 1, (1 : Fin 3)) : Bond L)) hd10
  have h1' : altMode w (y, (1 : Fin 3)) = 0 :=
    altMode_ne w (b := ((y, (1 : Fin 3)) : Bond L)) hd10
  have h2 : altMode w ((periodicLatticeShiftBack y (2 : Fin 3)), (2 : Fin 3)) = 0 :=
    altMode_ne w (b := ((periodicLatticeShiftBack y 2, (2 : Fin 3)) : Bond L)) hd20
  have h2' : altMode w (y, (2 : Fin 3)) = 0 :=
    altMode_ne w (b := ((y, (2 : Fin 3)) : Bond L)) hd20
  have h0 : altMode w ((periodicLatticeShiftBack y (0 : Fin 3)), (0 : Fin 3))
      = (par (periodicLatticeShiftBack y 0)) • w :=
    altMode_eq w (b := ((periodicLatticeShiftBack y 0, (0 : Fin 3)) : Bond L)) rfl
  have h0' : altMode w (y, (0 : Fin 3)) = (par y) • w :=
    altMode_eq w (b := ((y, (0 : Fin 3)) : Bond L)) rfl
  rw [h1, h1', h2, h2', h0, h0', par_shiftBack0 hdvd y]
  rw [map_zero, map_zero, map_smul,
    RMap_inv_fix (hUw ((periodicLatticeShiftBack y 0, (0 : Fin 3)) : Bond L))]
  rw [show ((-2 : ℝ) * par y) = -(par y) + -(par y) by ring, add_smul, neg_smul]
  abel

/-- **`src`, IN CLOSED FORM.** `D_U^*D_U(altSite (c·w))(y) = (4c·par y)·w`. -/
theorem src_altConfig (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {w : SuTwo}
    (hUw : ∀ b : Bond L, RMap (U b) w = w) (c : ℝ) (y : PeriodicLatticeSite L) :
    gradCovariantAdjointValue U (gradValueCovariant U (altSite (c • w))) y
      = ((4 * c) * par y) • w := by
  rw [grad_altSite hdvd U (fun b => RMap_fix_smul (hUw b) c)]
  rw [dstar_altMode hdvd U
    (w := (-2 : ℝ) • (c • w)) (fun b => RMap_fix_smul (RMap_fix_smul (hUw b) c) (-2)) y]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- **`hproj`, DISCHARGED.** `siteEnergy (D^*Dλ) ≤ siteEnergy (D^*A)` at the alternating
configuration `λ = altSite (c·w)`, `A = altMode w`, under `4c² ≤ 1`. Both sides are computed in
closed form: `16c²‖w‖²` per site against `4‖w‖²` per site. -/
theorem hproj_altConfig (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {w : SuTwo}
    (hUw : ∀ b : Bond L, RMap (U b) w = w) {c : ℝ} (hc : 4 * c ^ 2 ≤ 1) :
    siteEnergy (gradCovariantAdjointValue U (gradValueCovariant U (altSite (c • w))))
      ≤ siteEnergy (gradCovariantAdjointValue U (altMode w)) := by
  refine Finset.sum_le_sum (fun y _ => ?_)
  rw [src_altConfig hdvd U hUw c y, dstar_altMode hdvd U hUw y, norm_smul_sq, norm_smul_sq]
  have hp := par_sq y
  have hn : (0 : ℝ) ≤ ‖w‖ ^ 2 := sq_nonneg _
  have hLL : (4 * c * par y) ^ 2 = 16 * c ^ 2 := by rw [mul_pow, hp]; ring
  have hRR : ((-2 : ℝ) * par y) ^ 2 = 4 := by rw [mul_pow, hp]; ring
  rw [hLL, hRR]
  nlinarith [hn, hc, mul_nonneg (by linarith [hc] : (0:ℝ) ≤ 1 - 4 * c ^ 2) hn]

#print axioms altSite
#print axioms altSite_apply
#print axioms par_sq
#print axioms norm_smul_sq
#print axioms par_shiftBack0
#print axioms RMap_inv_fix
#print axioms RMap_fix_smul
#print axioms grad_altSite
#print axioms dstar_altMode
#print axioms src_altConfig
#print axioms hproj_altConfig

/-! ### §2b — `hmean` AT THE SAME CONFIGURATION

`altSite v` lies in `ker Q′(U)` for every background fixing `v`, and — this is what makes the
statement cheap — the cancellation is PAIRWISE over the eight `(1.7)` corners: the two corners
`(false,b,c)` and `(true,b,c)` differ by one step in direction `0`, so their `par` values are
opposite, while their transports agree on the line `ℝ·v`. No hypothesis `y ∈ CoarseLattice L 2` is
needed; the identity holds at every site. -/

/-- Every `(1.7)` transport fixes `v` when every link does. -/
theorem RMap_gammaTransport_fix
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {v : SuTwo}
    (hUv : ∀ b : Bond L, RMap (U b) v = v) (y : PeriodicLatticeSite L)
    (p : Bool × Bool × Bool) : RMap (gammaTransport U y p) v = v := by
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;>
    simp only [gammaTransport, RMap_one, LinearMap.id_apply, ← RMap_mul_apply, hUv]

/-- **THE PAIR CANCELLATION.** The two corners of `B(y)` differing by the direction-`0` step
contribute opposite transported values. -/
theorem gammaM_pair_altSite (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {v : SuTwo}
    (hUv : ∀ b : Bond L, RMap (U b) v = v) (y : PeriodicLatticeSite L) (b c : Bool) :
    gammaM U (altSite v) y (true, b, c) + gammaM U (altSite v) y (false, b, c) = 0 := by
  show RMap (gammaTransport U y (true, b, c)) (altSite v (gCorner y (true, b, c)))
      + RMap (gammaTransport U y (false, b, c)) (altSite v (gCorner y (false, b, c))) = 0
  rw [gCorner_true, gCorner_false, altSite_apply, altSite_apply,
    par_shift0 hdvd (gInner y b c), map_smul, map_smul,
    RMap_gammaTransport_fix U hUv y (true, b, c),
    RMap_gammaTransport_fix U hUv y (false, b, c), neg_smul]
  abel

/-- **`hmean`, DISCHARGED**, in `composed_coercivity_general`'s own shape. -/
theorem hmean_altSite (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {v : SuTwo}
    (hUv : ∀ b : Bond L, RMap (U b) v = v) :
    ∀ y ∈ CoarseLattice L 2, ∑ p : Bool × Bool × Bool, gammaM U (altSite v) y p = 0 := by
  intro y _
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun q _ => ?_)
  obtain ⟨b, c⟩ := q
  exact gammaM_pair_altSite hdvd U hUv y b c

#print axioms RMap_gammaTransport_fix
#print axioms gammaM_pair_altSite
#print axioms hmean_altSite

/-! ## §3 — THE THRESHOLD AT THE VOLUME-FREE AGGREGATE CONSTANT

`ComposedCoercivity` §5 pinned the criterion at `γ_fibre = 1/69088` to `(1.2·10⁻¹¹, 1.3·10⁻¹¹)`.
`FibreAggregate.gammaAgg = 1/3316224 = 1/(69088·48)` is the constant that is `L`-FREE, hence the
one an iteration can consume, and it is `48×` smaller. `alphaThresholdPi` is linear in `γ₀`
(`ComposedCoercivity.alphaThreshold_scales_with_volume`), so the admissible radius divides by `48`.
Both halves are proved, so the number is bracketed, not asserted. -/

/-- **CLOSES AT `α₀ = 2.5·10⁻¹³`.** `δ = 24·2.5·10⁻¹³·κ(28+48κ) ≤ 2.2585·10⁻⁷` against
`γ_agg·(1 − 1/4) = 3/13264896 ≈ 2.2616·10⁻⁷`. -/
theorem criterion_closes_at_gammaAgg :
    deltaPiConst (24 * (25 / 10 ^ 14 : ℝ)) kappaTree ≤ gammaAgg * (1 - (1 / 2 : ℝ) ^ 2) := by
  obtain ⟨hlo, hhi⟩ := kappaPoly_bracket
  rw [deltaPiConst_eq, gammaAgg_eq]
  nlinarith [hlo, hhi]

/-- **FAILS AT `α₀ = 2.6·10⁻¹³`** — the threshold is pinned to within `4%`. -/
theorem criterion_fails_at_gammaAgg :
    ¬ (deltaPiConst (24 * (26 / 10 ^ 14 : ℝ)) kappaTree
        ≤ gammaAgg * (1 - (1 / 2 : ℝ) ^ 2)) := by
  obtain ⟨hlo, hhi⟩ := kappaPoly_bracket
  rw [deltaPiConst_eq, gammaAgg_eq]
  intro hcon
  nlinarith [hlo, hhi, hcon]

/-- **MUST-FIRE — THE `48` IS REAL.** `ComposedCoercivity`'s own admissible radius `1.2·10⁻¹¹`,
which CLOSES at `γ_fibre`, FAILS at `γ_agg`. -/
theorem fibre_threshold_fails_at_gammaAgg :
    ¬ (deltaPiConst (24 * (12 / 10 ^ 12 : ℝ)) kappaTree
        ≤ gammaAgg * (1 - (1 / 2 : ℝ) ^ 2)) := by
  obtain ⟨hlo, hhi⟩ := kappaPoly_bracket
  rw [deltaPiConst_eq, gammaAgg_eq]
  intro hcon
  nlinarith [hlo, hhi, hcon]

/-- **THE FACTOR IS EXACTLY `48`, AS AN IDENTITY**, not an observation: `γ_fibre = 48·γ_agg`. -/
theorem gammaFibre_eq_48_gammaAgg : gammaFibre = 48 * gammaAgg := by
  show (1 / 69088 : ℝ) = 48 * (1 / 3316224 : ℝ)
  norm_num

/-- **MUST-NOT-FIRE.** `δ` is strictly positive at the closing point, so
`criterion_closes_at_gammaAgg` is not `0 ≤ positive`. -/
theorem deltaPiConst_pos_at_gammaAgg_point :
    0 < deltaPiConst (24 * (25 / 10 ^ 14 : ℝ)) kappaTree := by
  obtain ⟨hlo, _⟩ := kappaPoly_bracket
  rw [deltaPiConst_eq]
  nlinarith [hlo]

#print axioms criterion_closes_at_gammaAgg
#print axioms criterion_fails_at_gammaAgg
#print axioms fibre_threshold_fails_at_gammaAgg
#print axioms gammaFibre_eq_48_gammaAgg
#print axioms deltaPiConst_pos_at_gammaAgg_point

/-! ## §4 — THE VOLUME-FREE CURVED AGGREGATE BOUND

`ComposedCoercivity.aggregateFibreBound_curved` is `FibreCoercivity.bondEnergy_le_with_volume_factor`
+ `curlEnergy_le_curved`, and therefore carries `Fintype.card (Bond L)` in BOTH its constant and its
smallness condition. Replacing the first input by `FibreAggregate.aggregate_fibre_bound` — the same
argument, a strictly better first input — removes the volume from both. -/

/-- `γ_c(α₀) = (1 − 3316224·(544α₀ + 64α₀²))/(2·3316224)`, the curved aggregate constant. -/
noncomputable def gammaAggCurved (α₀ : ℝ) : ℝ :=
  (1 - 3316224 * driftRemainder α₀) / (2 * 3316224)

/-- **`AggregateFibreBound` AT A CURVED OPERATOR, WITH NO VOLUME FACTOR.** -/
theorem aggregateFibreBound_curved_volume_free (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ α₀)
    (hsmall : 3316224 * driftRemainder α₀ < 1) :
    0 < gammaAggCurved α₀ ∧ AggregateFibreBound L U (gammaAggCurved α₀) := by
  refine ⟨div_pos (by linarith [hsmall]) (by norm_num), ?_⟩
  intro A hQ
  have hP : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 := pAx_nonneg A _ 2
  have hE := bondEnergy_nonneg A
  have hagg := aggregate_fibre_bound hdvd A hQ
  have hcurl := curlEnergy_le_curved hα₀ U hsup A
  have hC := driftRemainder_nonneg hα₀
  unfold gammaAggCurved
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 2 * 3316224)]
  nlinarith [hagg, hcurl, hP, hE, hC]

#print axioms gammaAggCurved
#print axioms aggregateFibreBound_curved_volume_free

/-! ## §5 — THE JOINT INSTANTIATION, FLAT BACKGROUND

Every binder of `ComposedCoercivity.composed_coercivity_general` is supplied. The extent is
`witL5` (`= fun _ => 5`, i.e. `6³` sites, `2 ∣ 6`), the block side is `2`, the field is
`altMode rotGen`, the gauge parameter is `altSite ((1/4)·rotGen)`, and the constant is `γ_agg`. -/

open AdalyFormal.Balaban.FibreCoercivity (hdvd_witL5)

/-- The four-plaquette selection. `composed_coercivity_general` leaves `pl` FREE, so this choice is
one of many and the theorem's clause-3 bound is uniform over all of them (see the header). -/
noncomputable def jointPl (L : PeriodicLatticeExtent) :
    Bond L → Fin 4 → PeriodicLatticePlaquette L :=
  fun b i => (b.1, if i = 0 then AdalyFormal.Balaban.RegularUCurvedWitness.dir01
    else if i = 1 then ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩
    else ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩)

/-- The `(3.120)` current at that selection, DEFINED by `hJdef`'s formula — which is why `hJdef`
is `rfl`-dischargeable. -/
noncomputable def jointJ (etaInvSq : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Bond L → Matrix (Fin 2) (Fin 2) ℂ :=
  fun b => (etaInvSq : ℂ) •
    (AdalyFormal.Balaban.DeltaPrime.imHolonomy U (jointPl L b 0)
      - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (jointPl L b 1)
      + AdalyFormal.Balaban.DeltaPrime.imHolonomy U (jointPl L b 2)
      - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (jointPl L b 3))

theorem jointJ_def (etaInvSq : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    jointJ etaInvSq U b = (etaInvSq : ℂ) •
      (AdalyFormal.Balaban.DeltaPrime.imHolonomy U (jointPl L b 0)
        - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (jointPl L b 1)
        + AdalyFormal.Balaban.DeltaPrime.imHolonomy U (jointPl L b 2)
        - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (jointPl L b 3)) := rfl

/-- Every link of `trivialU` fixes every fibre vector. -/
theorem trivialU_fix (v : SuTwo) (b : Bond L) : RMap ((trivialU L) b) v = v := by
  show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) v = v
  rw [RMap_one]; rfl

/-- **THE COMPOSED LEMMA, INSTANTIATED — FLAT BACKGROUND, NO OPEN BINDER.**

At `L = witL5`, `U = trivialU`, `A = altMode rotGen`, `λ = altSite ((1/4)·rotGen)`,
`α₀ = 2.5·10⁻¹³`, `η⁻² = 1`, `γ* = γ_agg = 1/3316224`, every hypothesis of
`ComposedCoercivity.composed_coercivity_general` is discharged and its four conclusions hold. -/
theorem joint_instantiation_flat :
    gammaAgg * bondEnergy (altMode (L := witL5) rotGen)
        ≤ deltaKQuadFormNormalizedCorrected (trivialU witL5) (altMode rotGen)
          + pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2
      ∧ gammaFibre * bondSup (altMode (L := witL5) rotGen)
        ≤ deltaKQuadFormNormalizedCorrected (trivialU witL5) (altMode rotGen)
          + pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2
      ∧ |deltaPrimePiForm (trivialU witL5) (jointJ 1 (trivialU witL5))
            (altSite ((1 / 4 : ℝ) • rotGen)) (altMode rotGen)|
        ≤ deltaPiConst (24 * 1 * (25 / 10 ^ 14 : ℝ)) kappaTree
            * bondEnergy (altMode (L := witL5) rotGen)
      ∧ ∀ k : ℕ,
          0 < AdalyFormal.Balaban.GammaRecursion.gammaSeq gammaAgg
                (deltaPiConst (24 * 1 * (25 / 10 ^ 14 : ℝ)) kappaTree) (1 / 2 : ℝ) k
            ∧ gammaAgg
              ≤ AdalyFormal.Balaban.GammaRecursion.gammaSeq gammaAgg
                  (deltaPiConst (24 * 1 * (25 / 10 ^ 14 : ℝ)) kappaTree) (1 / 2 : ℝ) k := by
  have hcrit : deltaPiConst (24 * 1 * (25 / 10 ^ 14 : ℝ)) kappaTree
      ≤ gammaAgg * (1 - (1 / 2 : ℝ) ^ 2) := by
    rw [show (24 : ℝ) * 1 * (25 / 10 ^ 14 : ℝ) = 24 * (25 / 10 ^ 14 : ℝ) by ring]
    exact criterion_closes_at_gammaAgg
  refine composed_coercivity_general (L := witL5) hdvd_witL5
    (α₀ := (25 / 10 ^ 14 : ℝ)) (etaInvSq := 1) (by norm_num) (by norm_num)
    (trivialU witL5) ?_ (jointJ 1 (trivialU witL5)) (jointPl witL5)
    (fun b => jointJ_def 1 (trivialU witL5) b)
    (altMode rotGen) (altMode_Q hdvd_witL5 rotGen)
    (altSite ((1 / 4 : ℝ) • rotGen))
    (gradCovariantAdjointValue (trivialU witL5)
      (gradValueCovariant (trivialU witL5) (altSite ((1 / 4 : ℝ) • rotGen))))
    (gradCovariantAdjointValue (trivialU witL5) (altMode rotGen))
    (hmean_altSite hdvd_witL5 (trivialU witL5) (fun b => trivialU_fix _ b))
    (hweak_of_gradCovariantAdjoint (trivialU witL5) (altSite ((1 / 4 : ℝ) • rotGen)))
    (hadj_of_gradCovariantAdjoint (trivialU witL5) (altMode rotGen))
    (hproj_altConfig hdvd_witL5 (trivialU witL5) (fun b => trivialU_fix rotGen b)
      (c := (1 / 4 : ℝ)) (by norm_num))
    (γstar := gammaAgg) gammaAgg_pos ?_ hcrit
  · exact gaugeRegular_of_frobSupBond_le (by rw [frobSupBond_trivialU]; norm_num)
  · exact fun A hQ => aggregate_fibre_bound_gamma hdvd_witL5 A hQ

#print axioms jointPl
#print axioms jointJ
#print axioms jointJ_def
#print axioms trivialU_fix
#print axioms joint_instantiation_flat

/-! ## §6 — THE JOINT INSTANTIATION, CURVED BACKGROUND

`ComposedCoercivity` §6 built `curvedFineU = curvedFamilyU 10⁻¹²` for the `10⁻¹¹` class. At the
aggregate constant that class is `48×` too coarse (§3), and §4's curved constant costs a further
factor `2`, so the admissible radius drops again. The witness is rebuilt at `t = 10⁻¹⁴` and the
threshold re-derived two-sided at the constant that is actually consumed, `gammaAggCurved`. -/

/-- `t = 10⁻¹⁴`, two decades finer than `ComposedCoercivity.curvedFineT`. -/
noncomputable def curvedAggT : ℝ := 1 / 10 ^ 14

theorem curvedAggT_pos : 0 < curvedAggT := by unfold curvedAggT; norm_num

/-- The admissible radius at the curved aggregate constant, `α₀ = 1.2·10⁻¹³`. -/
noncomputable def curvedAggAlpha : ℝ := 12 / 10 ^ 14

theorem curvedAggAlpha_pos : 0 < curvedAggAlpha := by unfold curvedAggAlpha; norm_num

/-- The curved background this section instantiates at. -/
noncomputable abbrev curvedAggU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5 :=
  curvedFamilyU curvedAggT

/-- **IT IS IN THE CLASS.** `2√2·10⁻¹⁴ ≤ 1.2·10⁻¹³` since `2√2 ≤ 4 ≤ 12`. -/
theorem curvedAggU_frobSup : frobSupBond curvedAggU ≤ curvedAggAlpha := by
  have h := frobSupBond_curvedFamilyU_le curvedAggT
  rw [abs_of_pos curvedAggT_pos] at h
  refine le_trans h ?_
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs : Real.sqrt 2 ≤ 2 := by nlinarith
  unfold curvedAggT curvedAggAlpha
  nlinarith

theorem curvedAggU_gaugeRegular : GaugeRegular curvedAggAlpha curvedAggU :=
  gaugeRegular_of_frobSupBond_le curvedAggU_frobSup

/-- **AND IT IS NOT FLAT.** -/
theorem curvedAggU_curved :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem curvedAggU curvedPlaq
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  curvedFamilyU_curvature_ne_one (ne_of_gt curvedAggT_pos)

/-- Every link of `curvedFamilyU t` fixes `rotGen`: off `curvedBond` the link is `1`, and at
`curvedBond` it is `rotElem t`, whose adjoint action fixes its own generator. -/
theorem curvedFamilyU_fix_rotGen (t : ℝ) (b : Bond witL5) :
    RMap (curvedFamilyU t b) rotGen = rotGen := by
  by_cases hb : b = curvedBond
  · rw [hb, show curvedFamilyU t curvedBond = rotElem t from bondU_at curvedBond _]
    exact RMap_rotElem_rotGen t
  · rw [show curvedFamilyU t b = 1 from bondU_off curvedBond _ hb, RMap_one]
    rfl

/-- The smallness condition of §4 is met with a factor `≈1.5·10⁵` to spare. -/
theorem curvedAgg_smallness : 3316224 * driftRemainder curvedAggAlpha < 1 := by
  unfold driftRemainder curvedAggAlpha
  norm_num

/-- A rational lower bound on the curved aggregate constant at the chosen radius, so §6's criterion
is linear arithmetic in `κ`. `γ_c(1.2·10⁻¹³) ≈ 1.50741·10⁻⁷`. -/
theorem gammaAggCurved_lower : (1507 / 10 ^ 10 : ℝ) ≤ gammaAggCurved curvedAggAlpha := by
  unfold gammaAggCurved driftRemainder curvedAggAlpha
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2 * 3316224)]
  norm_num

theorem gammaAggCurved_pos_at_alpha : 0 < gammaAggCurved curvedAggAlpha :=
  lt_of_lt_of_le (by norm_num) gammaAggCurved_lower

/-- **THE CURVED THRESHOLD CLOSES AT `α₀ = 1.2·10⁻¹³`.** `δ = 24·1.2·10⁻¹³·κ(28+48κ) ≤
1.0841·10⁻⁷` against `γ_c·(3/4) ≥ 1.13025·10⁻⁷`. -/
theorem curved_criterion_closes :
    deltaPiConst (24 * 1 * curvedAggAlpha) kappaTree
      ≤ gammaAggCurved curvedAggAlpha * (1 - (1 / 2 : ℝ) ^ 2) := by
  obtain ⟨hlo, hhi⟩ := kappaPoly_bracket
  have hg := gammaAggCurved_lower
  rw [show (24 : ℝ) * 1 * curvedAggAlpha = 24 * curvedAggAlpha by ring, deltaPiConst_eq]
  unfold curvedAggAlpha at *
  nlinarith [hlo, hhi, hg]

/-- **AND FAILS AT `1.3·10⁻¹³`** — the curved threshold is pinned to within `8.3%`. The upper bound
`γ_c ≤ 1.50774·10⁻⁷` is used on this side, so the two halves do not lean on the same estimate. -/
theorem gammaAggCurved_upper (α₀ : ℝ) (hα₀ : 0 ≤ α₀) :
    gammaAggCurved α₀ ≤ 1 / (2 * 3316224) := by
  unfold gammaAggCurved
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith [driftRemainder_nonneg hα₀]

theorem curved_criterion_fails_at_thirteen :
    ¬ (deltaPiConst (24 * 1 * (13 / 10 ^ 14 : ℝ)) kappaTree
        ≤ gammaAggCurved (13 / 10 ^ 14 : ℝ) * (1 - (1 / 2 : ℝ) ^ 2)) := by
  obtain ⟨hlo, hhi⟩ := kappaPoly_bracket
  have hg := gammaAggCurved_upper (13 / 10 ^ 14 : ℝ) (by norm_num)
  rw [show (24 : ℝ) * 1 * (13 / 10 ^ 14 : ℝ) = 24 * (13 / 10 ^ 14 : ℝ) by ring, deltaPiConst_eq]
  intro hcon
  nlinarith [hlo, hhi, hg, hcon]

/-- **THE COMPOSED LEMMA, INSTANTIATED — GENUINELY CURVED BACKGROUND, NO OPEN BINDER.** -/
theorem joint_instantiation_curved :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem curvedAggU curvedPlaq
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ 0 < gammaAggCurved curvedAggAlpha
      ∧ gammaAggCurved curvedAggAlpha * bondEnergy (altMode (L := witL5) rotGen)
        ≤ deltaKQuadFormNormalizedCorrected curvedAggU (altMode rotGen)
          + pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2
      ∧ gammaFibre * bondSup (altMode (L := witL5) rotGen)
        ≤ deltaKQuadFormNormalizedCorrected (trivialU witL5) (altMode rotGen)
          + pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2
      ∧ |deltaPrimePiForm curvedAggU (jointJ 1 curvedAggU)
            (altSite ((1 / 4 : ℝ) • rotGen)) (altMode rotGen)|
        ≤ deltaPiConst (24 * 1 * curvedAggAlpha) kappaTree
            * bondEnergy (altMode (L := witL5) rotGen)
      ∧ ∀ k : ℕ,
          0 < AdalyFormal.Balaban.GammaRecursion.gammaSeq (gammaAggCurved curvedAggAlpha)
                (deltaPiConst (24 * 1 * curvedAggAlpha) kappaTree) (1 / 2 : ℝ) k
            ∧ gammaAggCurved curvedAggAlpha
              ≤ AdalyFormal.Balaban.GammaRecursion.gammaSeq (gammaAggCurved curvedAggAlpha)
                  (deltaPiConst (24 * 1 * curvedAggAlpha) kappaTree) (1 / 2 : ℝ) k := by
  obtain ⟨hpos, hagg⟩ :=
    aggregateFibreBound_curved_volume_free hdvd_witL5 (le_of_lt curvedAggAlpha_pos)
      curvedAggU curvedAggU_frobSup curvedAgg_smallness
  refine ⟨curvedAggU_curved, hpos, ?_⟩
  exact composed_coercivity_general (L := witL5) hdvd_witL5
    (α₀ := curvedAggAlpha) (etaInvSq := 1) (le_of_lt curvedAggAlpha_pos) (by norm_num)
    curvedAggU curvedAggU_gaugeRegular (jointJ 1 curvedAggU) (jointPl witL5)
    (fun b => jointJ_def 1 curvedAggU b)
    (altMode rotGen) (altMode_Q hdvd_witL5 rotGen)
    (altSite ((1 / 4 : ℝ) • rotGen))
    (gradCovariantAdjointValue curvedAggU
      (gradValueCovariant curvedAggU (altSite ((1 / 4 : ℝ) • rotGen))))
    (gradCovariantAdjointValue curvedAggU (altMode rotGen))
    (hmean_altSite hdvd_witL5 curvedAggU
      (fun b => RMap_fix_smul (curvedFamilyU_fix_rotGen curvedAggT b) (1 / 4 : ℝ)))
    (hweak_of_gradCovariantAdjoint curvedAggU (altSite ((1 / 4 : ℝ) • rotGen)))
    (hadj_of_gradCovariantAdjoint curvedAggU (altMode rotGen))
    (hproj_altConfig hdvd_witL5 curvedAggU
      (fun b => curvedFamilyU_fix_rotGen curvedAggT b) (c := (1 / 4 : ℝ)) (by norm_num))
    (γstar := gammaAggCurved curvedAggAlpha) hpos hagg curved_criterion_closes

#print axioms curvedAggT
#print axioms curvedAggT_pos
#print axioms curvedAggAlpha
#print axioms curvedAggAlpha_pos
#print axioms curvedAggU
#print axioms curvedAggU_frobSup
#print axioms curvedAggU_gaugeRegular
#print axioms curvedAggU_curved
#print axioms curvedFamilyU_fix_rotGen
#print axioms curvedAgg_smallness
#print axioms gammaAggCurved_lower
#print axioms gammaAggCurved_pos_at_alpha
#print axioms gammaAggCurved_upper
#print axioms curved_criterion_closes
#print axioms curved_criterion_fails_at_thirteen
#print axioms joint_instantiation_curved

/-! ## §7 — CONTROLS, AND THE MEASURED LIMITS OF THE CONFIGURATION

Three things a reader is entitled to demand of §5/§6, all proved rather than asserted:
a MUST-FIRE for `hproj` (the leg is false one step outside the discharged range), a NON-VACUITY
statement for the clauses that carry content, and an explicit proof of the one clause that does
NOT (clause 3), with its reason. -/

/-- The site set is nonempty. -/
theorem site_univ_nonempty : (Finset.univ : Finset (PeriodicLatticeSite L)).Nonempty :=
  ⟨zeroSite L, Finset.mem_univ _⟩

/-- **MUST-FIRE FOR `hproj`.** At the SAME configuration with the ratio parameter `c = 1` — one
step outside `hproj_altConfig`'s range `4c² ≤ 1` — the leg is FALSE: the gauge-parameter divergence
strictly exceeds the field divergence. So `hproj` is a real constraint on the configuration and
`hproj_altConfig`'s hypothesis is load-bearing, not decorative. -/
theorem hproj_fails_at_unit_ratio (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {w : SuTwo}
    (hUw : ∀ b : Bond L, RMap (U b) w = w) (hw : w ≠ 0) :
    ¬ (siteEnergy (gradCovariantAdjointValue U (gradValueCovariant U (altSite ((1 : ℝ) • w))))
        ≤ siteEnergy (gradCovariantAdjointValue U (altMode w))) := by
  have hwpos : (0 : ℝ) < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw) 2
  have hstrict : ∀ y : PeriodicLatticeSite L,
      ‖gradCovariantAdjointValue U (altMode w) y‖ ^ 2
        < ‖gradCovariantAdjointValue U
            (gradValueCovariant U (altSite ((1 : ℝ) • w))) y‖ ^ 2 := by
    intro y
    rw [src_altConfig hdvd U hUw 1 y, dstar_altMode hdvd U hUw y, norm_smul_sq, norm_smul_sq]
    have hp := par_sq y
    have hLL : (4 * (1 : ℝ) * par y) ^ 2 = 16 := by rw [mul_pow, hp]; ring
    have hRR : ((-2 : ℝ) * par y) ^ 2 = 4 := by rw [mul_pow, hp]; ring
    rw [hLL, hRR]
    nlinarith [hwpos]
  intro hcon
  have hlt : siteEnergy (gradCovariantAdjointValue U (altMode w))
      < siteEnergy (gradCovariantAdjointValue U
          (gradValueCovariant U (altSite ((1 : ℝ) • w)))) :=
    Finset.sum_lt_sum_of_nonempty site_univ_nonempty (fun y _ => hstrict y)
  linarith

/-- **NON-VACUITY OF CLAUSES 1 AND 2, AT THE INSTANTIATED CONFIGURATION.** Both sides of the
instantiated bound are strictly positive at `altMode rotGen`, so §5's clauses 1 and 2 constrain a
genuinely nonzero quantity. `FibreAggregate.aggregate_nonvacuous` supplies the `L²` half;
`ComposedCoercivity.bondSup_altMode_pos` the `ℓ^∞` half. -/
theorem joint_config_nonvacuous :
    0 < gammaAgg * bondEnergy (altMode (L := witL5) rotGen)
      ∧ 0 < deltaKQuadFormNormalizedCorrected (trivialU witL5) (altMode rotGen)
          + pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2
      ∧ 0 < bondSup (altMode (L := witL5) rotGen)
      ∧ altSite ((1 / 4 : ℝ) • rotGen) (zeroSite witL5) = (1 / 4 : ℝ) • rotGen := by
  obtain ⟨_, _, hpos, hrhs, _⟩ :=
    AdalyFormal.Balaban.FibreAggregate.aggregate_nonvacuous hdvd_witL5 rotGen rotGen_ne_zero
  refine ⟨?_, hrhs, bondSup_altMode_pos rotGen rotGen_ne_zero, ?_⟩
  · rw [gammaAgg_eq]; exact hpos
  · rw [altSite_apply]
    have hpar : par (zeroSite witL5) = 1 := by
      unfold par; rw [if_pos (zeroSite_even (L := witL5) 0)]
    rw [hpar, one_smul]

/-- **THE FLAT CURRENT IS ZERO.** `imHolonomy (trivialU L) p = 0`, so the `(3.120)` current
built by `jointJ` vanishes identically at the flat background — for EVERY `η⁻²` and every choice
of `pl`. This is the first of the two independent reasons clause 3 carries no content in §5. -/
theorem trivialU_eq_deltaPrime_trivialU :
    (trivialU L) = (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) := rfl

theorem jointJ_trivialU_eq_zero (etaInvSq : ℝ) (b : Bond L) :
    jointJ etaInvSq (trivialU L) b = 0 := by
  rw [jointJ_def, trivialU_eq_deltaPrime_trivialU]
  rw [AdalyFormal.Balaban.DeltaPrime.imHolonomy_trivialU,
    AdalyFormal.Balaban.DeltaPrime.imHolonomy_trivialU,
    AdalyFormal.Balaban.DeltaPrime.imHolonomy_trivialU,
    AdalyFormal.Balaban.DeltaPrime.imHolonomy_trivialU]
  simp

/-- `i[X,Y]` is alternating, so it VANISHES on a line: any two real multiples of the same `𝔰𝔲(2)`
vector commute. -/
theorem iComm_collinear (a b : ℝ) (w : SuTwo) : iComm (a • w) (b • w) = 0 := by
  show Complex.I • ((((a • w : SuTwo)) : Matrix (Fin 2) (Fin 2) ℂ)
      * (((b • w : SuTwo)) : Matrix (Fin 2) (Fin 2) ℂ)
      - (((b • w : SuTwo)) : Matrix (Fin 2) (Fin 2) ℂ)
        * (((a • w : SuTwo)) : Matrix (Fin 2) (Fin 2) ℂ)) = 0
  simp only [SetLike.val_smul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm a b,
    sub_self, smul_zero]

/-- Every value the configuration feeds to `piBondValue` lies on the line `ℝ·w`, and the scalar is
NAMED rather than existentially quantified (S91: no free data in the conclusion). -/
theorem altMode_eq_smul (w : SuTwo) (b : Bond L) :
    altMode w b = (if b.2 = 0 then par b.1 else (0 : ℝ)) • w := by
  by_cases h : b.2 = 0
  · rw [if_pos h, altMode_eq w h]
  · rw [if_neg h, altMode_ne w h, zero_smul]

/-- **EVERY BOND VALUE OF `(3.120)` VANISHES AT THIS CONFIGURATION.** -/
theorem piBondValue_eq_zero_at_config (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {w : SuTwo}
    (hUw : ∀ b : Bond L, RMap (U b) w = w) (c : ℝ) (b : Bond L) :
    piBondValue U (altSite (c • w)) (altMode w) b = 0 := by
  have h2 := altMode_eq_smul w b
  have h1 : altSite (c • w) b.1 = (par b.1 * c) • w := by rw [altSite_apply, smul_smul]
  have h3 : RMap (U b) (altSite (c • w) (periodicLatticeShift b.1 b.2))
      = (par (periodicLatticeShift b.1 b.2) * c) • w := by
    rw [altSite_apply, smul_smul, RMap_fix_smul (hUw b)]
  have h4 : gradValueCovariant U (altSite (c • w)) b
      = (((if b.2 = 0 then par b.1 else (0 : ℝ)) * (-2)) * c) • w := by
    rw [grad_altSite hdvd U (fun b' => RMap_fix_smul (hUw b') c),
      altMode_eq_smul ((-2 : ℝ) • (c • w)) b, smul_smul, smul_smul]
  show iComm (altSite (c • w) b.1) (altMode w b)
      - iComm (altMode w b) (RMap (U b) (altSite (c • w) (periodicLatticeShift b.1 b.2)))
      - iComm (altSite (c • w) b.1) (gradValueCovariant U (altSite (c • w)) b) = 0
  rw [h1, h2, h3, h4, iComm_collinear, iComm_collinear, iComm_collinear, sub_zero, sub_zero]

/-- **CLAUSE 3'S LEFT-HAND SIDE IS IDENTICALLY ZERO AT THE INSTANTIATED CONFIGURATION**, for every
background fixing `w`, every current `J`, and every ratio `c`. Stated as a theorem so the limit of
§5/§6 is a measured fact and not a caveat: at a configuration where `λ` and `A` are collinear in
`𝔰𝔲(2)`, `(3.120)` is blind, because every one of its three terms is an `iComm` of one against the
other. -/
theorem deltaPrimePiForm_eq_zero_at_config (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {w : SuTwo}
    (hUw : ∀ b : Bond L, RMap (U b) w = w) (c : ℝ)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ) :
    deltaPrimePiForm U J (altSite (c • w)) (altMode w) = 0 := by
  show (∑ b : Bond L, (Matrix.trace (piBondValue U (altSite (c • w)) (altMode w) b * J b)).re) = 0
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [piBondValue_eq_zero_at_config hdvd U hUw c b, Matrix.zero_mul, Matrix.trace_zero]
  simp

/-- **THE TWO INSTANTIATIONS, WITH THEIR CLAUSE-3 CONTENT MEASURED.** Clauses 1, 2 are non-vacuous
(`joint_config_nonvacuous`); clause 3 is the trivial `0 ≤ δ·bondEnergy` at BOTH backgrounds, and
here is the proof, at the flat one through `jointJ_trivialU_eq_zero` as well. -/
theorem clause_three_is_trivial_at_both :
    deltaPrimePiForm (trivialU witL5) (jointJ 1 (trivialU witL5))
        (altSite ((1 / 4 : ℝ) • rotGen)) (altMode rotGen) = 0
      ∧ deltaPrimePiForm curvedAggU (jointJ 1 curvedAggU)
        (altSite ((1 / 4 : ℝ) • rotGen)) (altMode rotGen) = 0
      ∧ ∀ b : Bond witL5, jointJ 1 (trivialU witL5) b = 0 :=
  ⟨deltaPrimePiForm_eq_zero_at_config hdvd_witL5 (trivialU witL5)
      (fun b => trivialU_fix rotGen b) (1 / 4 : ℝ) _,
    deltaPrimePiForm_eq_zero_at_config hdvd_witL5 curvedAggU
      (fun b => curvedFamilyU_fix_rotGen curvedAggT b) (1 / 4 : ℝ) _,
    fun b => jointJ_trivialU_eq_zero 1 b⟩

#print axioms site_univ_nonempty
#print axioms hproj_fails_at_unit_ratio
#print axioms joint_config_nonvacuous
#print axioms trivialU_eq_deltaPrime_trivialU
#print axioms jointJ_trivialU_eq_zero
#print axioms iComm_collinear
#print axioms altMode_eq_smul
#print axioms piBondValue_eq_zero_at_config
#print axioms deltaPrimePiForm_eq_zero_at_config
#print axioms clause_three_is_trivial_at_both

/-! ## §8 — F2's OPEN HALF, CLOSED **AT THIS CONFIGURATION**: the `Q` CLAUSE IS COVARIANT TOO

`ComposedCoercivity` F2 records that `AggregateFibreBound`'s `{Q A = 0}` clause is the FLAT
`lineCoarseRestrictCov (trivialU L)` even when the operator is curved, and §3b names the missing
primitive for the general repair. That repair is inside `FibreCoercivity`'s own chain and is a
write-scope matter, not touched here.

**But the instantiation does not need the general repair.** At the configuration §5/§6 actually
use, the covariant `Q` and the flat `Q` COINCIDE on the field, so the clause discharged is
simultaneously the flat one and the covariant one. The reason is the same one that makes §2 work:
`lineCoarseRestrictCov` transports the bond values by `RMap` of path holonomies, every link of the
background fixes `w`, every value of `altMode w` lies on `ℝ·w`, and a product of maps fixing `w`
fixes `w`. Nothing is approximated — this is an equality, not an `α`-small remainder. -/

/-- Every path holonomy fixes `v` when every link does. Induction on the step list; the inverse
steps are covered by `RMap_inv_fix`. -/
theorem RMap_periodicPathHolonomy_fix
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {v : SuTwo}
    (hUv : ∀ b : Bond L, RMap (U b) v = v) :
    ∀ (steps : List (Fin 3 × Bool)) (x : PeriodicLatticeSite L),
      RMap (periodicPathHolonomy U x steps) v = v := by
  intro steps
  induction steps with
  | nil =>
    intro x
    show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) v = v
    rw [RMap_one]; rfl
  | cons step rest ih =>
    intro x
    show RMap ((if step.2 then U (x, step.1)
        else (U (periodicLatticeStep x step, step.1))⁻¹)
        * periodicPathHolonomy U (periodicLatticeStep x step) rest) v = v
    rw [← RMap_mul_apply, ih (periodicLatticeStep x step)]
    by_cases h : step.2 = true
    · rw [if_pos h, hUv]
    · rw [if_neg h, RMap_inv_fix (hUv _)]

/-- **THE TRANSPORTED LINE INTEGRAL IS THE UNTRANSPORTED ONE** for a field valued on the fixed
line `ℝ·v`. The scalar profile `coef` is NAMED, so there is no free data (S91). -/
theorem rZeroA_of_line
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {v : SuTwo}
    (hUv : ∀ b : Bond L, RMap (U b) v = v) (coef : Bond L → ℝ) (A : Bond L → SuTwo)
    (hA : ∀ b : Bond L, A b = coef b • v)
    (cMinus x : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ) :
    AdalyFormal.Balaban.Q1Real.rZeroA U cMinus x A μ ell
      = ∑ i ∈ Finset.range ell, A (AdalyFormal.Balaban.QOne.pathSite x μ i, μ) := by
  show (∑ i ∈ Finset.range ell,
      RMap (periodicPathHolonomy U cMinus
        (AdalyFormal.Balaban.Q1Real.transportPath cMinus x μ i))
        (A (AdalyFormal.Balaban.QOne.pathSite x μ i, μ))) = _
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hA, RMap_fix_smul (RMap_periodicPathHolonomy_fix U hUv _ cMinus)]

/-- **`Q_ℓ(U) = Q_ℓ(1)` ON THE LINE `ℝ·v`.** Exact, with no `α`-remainder — so
`WindowStokesGeneralU.norm_lineCoarse_cov_sub_flat_le_block`'s `8α/ℓ³` bound is not merely small
here, the difference it bounds is `0`. -/
theorem lineCoarseRestrictCov_eq_flat_of_line
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {v : SuTwo}
    (hUv : ∀ b : Bond L, RMap (U b) v = v) (coef : Bond L → ℝ) (A : Bond L → SuTwo)
    (hA : ∀ b : Bond L, A b = coef b • v) (ell : ℕ)
    (b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell) :
    lineCoarseRestrictCov U ell A b = lineCoarseRestrictCov (trivialU L) ell A b := by
  simp only [lineCoarseRestrictCov]
  refine congrArg _ (Finset.sum_congr rfl (fun x _ => ?_))
  rw [rZeroA_of_line U hUv coef A hA b.1.1 x b.2 ell,
    rZeroA_of_line (trivialU L) (fun b' => trivialU_fix v b') coef A hA b.1.1 x b.2 ell]

/-- **THE COARSE-AVERAGE-FREE CLAUSE, COVARIANTLY.** `altMode w` is annihilated by the FAITHFUL
covariant `Q_2(U)` at every background whose links fix `w` — in particular at `curvedAggU`. This
is the clause `composed_coercivity_general`'s `hQ` would carry if `AggregateFibreBound`'s definition
were covariantized; at this configuration the two clauses are the same statement. -/
theorem altMode_Q_covariant (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {w : SuTwo}
    (hUw : ∀ b : Bond L, RMap (U b) w = w)
    (b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2) :
    lineCoarseRestrictCov U 2 (altMode w) b = 0 := by
  rw [lineCoarseRestrictCov_eq_flat_of_line U hUw
    (fun b' => if b'.2 = 0 then par b'.1 else (0 : ℝ)) (altMode w) (altMode_eq_smul w) 2 b]
  exact altMode_Q hdvd w b

/-- **THE CURVED INSTANTIATION'S FIELD IS COVARIANTLY COARSE-AVERAGE-FREE.** Stated at the exact
background §6 uses, so F2's caveat is void for `joint_instantiation_curved`. -/
theorem curved_config_Q_covariant
    (b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2) :
    lineCoarseRestrictCov curvedAggU 2 (altMode rotGen) b = 0
      ∧ lineCoarseRestrictCov (trivialU witL5) 2 (altMode rotGen) b = 0 :=
  ⟨altMode_Q_covariant hdvd_witL5 curvedAggU
      (fun b' => curvedFamilyU_fix_rotGen curvedAggT b') b,
    altMode_Q hdvd_witL5 rotGen b⟩

#print axioms RMap_periodicPathHolonomy_fix
#print axioms rZeroA_of_line
#print axioms lineCoarseRestrictCov_eq_flat_of_line
#print axioms altMode_Q_covariant
#print axioms curved_config_Q_covariant

/-! ## §9 — THE INSTANTIATION IS `L`-FREE: THE SAME CONSTANT AT A SECOND EXTENT

`γ_agg` does not depend on the extent (`FibreAggregate.aggregate_two_extents`), and neither does
anything else §5 uses. The flat instantiation is therefore stated once, generically in `L`, and
exhibited at TWO extents with different bond counts (`witL3` has `192` bonds, `witL5` has `648`).
A volume-dependent constant could not do this. -/

open AdalyFormal.Balaban.FibreAggregate (witL3 hdvd_witL3 card_bond_witL3 card_bond_witL5
  card_bond_differs)

/-- **THE FLAT INSTANTIATION, GENERIC IN THE EXTENT.** `joint_instantiation_flat` is its `witL5`
instance. -/
theorem joint_instantiation_flat_general (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    gammaAgg * bondEnergy (altMode (L := L) rotGen)
        ≤ deltaKQuadFormNormalizedCorrected (trivialU L) (altMode rotGen)
          + pAx (altMode (L := L) rotGen) (CoarseLattice L 2) 2
      ∧ gammaFibre * bondSup (altMode (L := L) rotGen)
        ≤ deltaKQuadFormNormalizedCorrected (trivialU L) (altMode rotGen)
          + pAx (altMode (L := L) rotGen) (CoarseLattice L 2) 2
      ∧ |deltaPrimePiForm (trivialU L) (jointJ 1 (trivialU L))
            (altSite ((1 / 4 : ℝ) • rotGen)) (altMode rotGen)|
        ≤ deltaPiConst (24 * 1 * (25 / 10 ^ 14 : ℝ)) kappaTree
            * bondEnergy (altMode (L := L) rotGen)
      ∧ ∀ k : ℕ,
          0 < AdalyFormal.Balaban.GammaRecursion.gammaSeq gammaAgg
                (deltaPiConst (24 * 1 * (25 / 10 ^ 14 : ℝ)) kappaTree) (1 / 2 : ℝ) k
            ∧ gammaAgg
              ≤ AdalyFormal.Balaban.GammaRecursion.gammaSeq gammaAgg
                  (deltaPiConst (24 * 1 * (25 / 10 ^ 14 : ℝ)) kappaTree) (1 / 2 : ℝ) k := by
  have hcrit : deltaPiConst (24 * 1 * (25 / 10 ^ 14 : ℝ)) kappaTree
      ≤ gammaAgg * (1 - (1 / 2 : ℝ) ^ 2) := by
    rw [show (24 : ℝ) * 1 * (25 / 10 ^ 14 : ℝ) = 24 * (25 / 10 ^ 14 : ℝ) by ring]
    exact criterion_closes_at_gammaAgg
  exact composed_coercivity_general (L := L) hdvd
    (α₀ := (25 / 10 ^ 14 : ℝ)) (etaInvSq := 1) (by norm_num) (by norm_num)
    (trivialU L)
    (gaugeRegular_of_frobSupBond_le (by rw [frobSupBond_trivialU]; norm_num))
    (jointJ 1 (trivialU L)) (jointPl L)
    (fun b => jointJ_def 1 (trivialU L) b)
    (altMode rotGen) (altMode_Q hdvd rotGen)
    (altSite ((1 / 4 : ℝ) • rotGen))
    (gradCovariantAdjointValue (trivialU L)
      (gradValueCovariant (trivialU L) (altSite ((1 / 4 : ℝ) • rotGen))))
    (gradCovariantAdjointValue (trivialU L) (altMode rotGen))
    (hmean_altSite hdvd (trivialU L) (fun b => trivialU_fix _ b))
    (hweak_of_gradCovariantAdjoint (trivialU L) (altSite ((1 / 4 : ℝ) • rotGen)))
    (hadj_of_gradCovariantAdjoint (trivialU L) (altMode rotGen))
    (hproj_altConfig hdvd (trivialU L) (fun b => trivialU_fix rotGen b)
      (c := (1 / 4 : ℝ)) (by norm_num))
    (γstar := gammaAgg) gammaAgg_pos (fun A hQ => aggregate_fibre_bound_gamma hdvd A hQ) hcrit

/-- **THE SAME CONSTANT AT `4³` AND AT `6³`.** The two extents have DIFFERENT bond counts
(`192 ≠ 648`, `FibreAggregate.card_bond_differs`), and the instantiated coercivity constant is the
SAME numeral at both — which a volume-costed constant could not be. -/
theorem joint_instantiation_two_extents :
    (gammaAgg * bondEnergy (altMode (L := witL3) rotGen)
        ≤ deltaKQuadFormNormalizedCorrected (trivialU witL3) (altMode rotGen)
          + pAx (altMode (L := witL3) rotGen) (CoarseLattice witL3 2) 2)
      ∧ (gammaAgg * bondEnergy (altMode (L := witL5) rotGen)
        ≤ deltaKQuadFormNormalizedCorrected (trivialU witL5) (altMode rotGen)
          + pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2)
      ∧ Fintype.card (Bond witL3) ≠ Fintype.card (Bond witL5) :=
  ⟨(joint_instantiation_flat_general hdvd_witL3).1,
    (joint_instantiation_flat_general hdvd_witL5).1,
    card_bond_differs⟩

/-- **THE CURVED INSTANTIATION AND ITS COVARIANT `Q` CLAUSE, IN ONE STATEMENT**, so neither can be
read without the other: at `curvedAggU` the field is annihilated by BOTH the flat and the faithful
covariant coarse restriction, the aggregate coercivity holds at the volume-free curved constant,
and the background is genuinely curved. -/
theorem joint_instantiation_curved_with_covariant_Q :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem curvedAggU curvedPlaq
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2,
          lineCoarseRestrictCov curvedAggU 2 (altMode rotGen) b = 0
            ∧ lineCoarseRestrictCov (trivialU witL5) 2 (altMode rotGen) b = 0)
      ∧ 0 < gammaAggCurved curvedAggAlpha
      ∧ gammaAggCurved curvedAggAlpha * bondEnergy (altMode (L := witL5) rotGen)
        ≤ deltaKQuadFormNormalizedCorrected curvedAggU (altMode rotGen)
          + pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2 := by
  obtain ⟨hcurv, hpos, hmain⟩ := joint_instantiation_curved
  exact ⟨hcurv, curved_config_Q_covariant, hpos, hmain.1⟩

#print axioms joint_instantiation_flat_general
#print axioms joint_instantiation_two_extents
#print axioms joint_instantiation_curved_with_covariant_Q

end AdalyFormal.Balaban.JointInstantiation
