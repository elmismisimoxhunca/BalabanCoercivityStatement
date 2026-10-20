/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.ThirdLevelArrows
import AdalyFormal.Balaban.ThirdLevelWitness
import AdalyFormal.Balaban.BlockedGaugeCore

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `TowerLawCovariant.lean` — `[Q-TRANSPORT-COMPOSE]`, stated and then REFUTED

## What this module is

`ThirdLevelArrows.tower_law` proves `Q₁ ∘ Q_{ℓ₀} = Q_{ℓ₀·m}` **at `U = 1`**, where the unit→coarse
arrow `unitToCoarse` carries NO transport. Its HONEST SCOPE section names the covariant statement
`[Q-TRANSPORT-COMPOSE]` as open: *"the covariant arrow needs the unit-lattice transports and is not
built here"*.

This module builds that arrow (`unitToCoarseCov`), states the covariant tower law, and then proves
that **no unit-level background whatsoever makes it true at a curved `U`**.

## The statement, and why the level index cannot collapse

CMP99b p.393 (3.15): `Q_j(U) = Q(Ū^{j−1})⋯Q(Ū¹)Q(U)` — each factor is the SAME one-step averaging
template evaluated at a SUCCESSIVELY BLOCKED background. In this tree's block-side indexing the
two-step instance reads

  `unitToCoarseCov ℓ₀ m V (Q_{ℓ₀}(U) v) = Q_{ℓ₀·m}(U) v`,       (TOWER-COV)

with `V` the UNIT-level background (Bałaban's `Ū`; `BlockedGauge.blockedGaugeAsConfig` is the
source's instance, and `blockedGaugeAsConfig P ell U : PeriodicLinkConfiguration G L` has exactly
the type `V` occupies here). Both arrows are kept apart by TYPE, as
`ThirdLevelArrows`'s table demands: `unitToCoarseCov`'s domain is `CoarseBond L ℓ₀ → SuTwo`, so
feeding it a fine field, or feeding `lineCoarseRestrictCovLM` a unit field, is a type error.
`CStarLevelCorrected.LevelSplit` supplies the block-side bookkeeping (`ℓ₀ < ℓ₁`, `ℓ₀ ∣ ℓ₁`); §7
below instantiates against it so the `ℓ₀ = ℓ₁` collapse that produced
`CStarDeltaKCCoercive.cStarDeltaKC_coercivity_refuted` is unstateable here too.

**`V` is a PARAMETER, never existentially quantified (S91).** Every theorem below is either
`∀ V, …` or is stated at a named `V`. The refutation is `∀ V, ¬ …`, so it does not depend on which
`Ū` one builds.

## What is proved

* **§2** `unitToCoarseCov ℓ₀ m V` — the covariant unit→coarse arrow, with `+`/`•` laws and its
  `LinearMap` promotion. It is `unitToCoarse`'s template with `RMap` of a UNIT-scale
  CMP95 (1.7) contour holonomy inserted, exactly as `lineCoarseRestrictCov` is the block average of
  `Q1Real.rZeroA`.
* **§3 MUST-NOT-FIRE CONTROL.** At `V = 1` the arrow collapses to `ThirdLevelArrows.unitToCoarse`
  (`unitToCoarseCov_trivialU`), so (TOWER-COV) REDUCES to the existing proved `tower_law` at
  `U = 1` (`tower_law_cov_at_trivial`) rather than contradicting it.
* **§4** the two EXPANSIONS: both sides of (TOWER-COV) written over the SAME index set
  `(u, i, x, j)` with the same weight `1/(ℓ₀m)⁴`, differing only in a transport group element
  (`lhs_expand`, `rhs_expand`). This is where all the combinatorics lives, and it says the tower law
  is a statement about TRANSPORTS ONLY.
* **§5** `TransportCompose` and `tower_law_cov_of_transportCompose` — (TOWER-COV) holds under the
  exact termwise transport hypothesis. The honest EXACT form.
* **§5c/§5d/§5e THE QUANTITATIVE CHAIN.** `towerDefect_norm_le` bounds the defect displacement by
  (total route length)·(per-link displacement), via `R`'s isometry rather than any matrix-norm
  triangle inequality; `expansion_card` proves the term count is EXACTLY `(ℓ₀m)⁴`, so the arrows'
  own weight cancels it (`tower_law_cov_error_uniform`: the error is at most the worst per-term
  defect); and `tower_law_cov_error_alpha` assembles them into
  `‖LHS − RHS‖ ≤ N · 2α₁ · Kv` with `α₁` the per-link Frobenius distance from `1`, `Kv` a bound on
  the field, `N` a bound on the routes' length. At `α₁ = 0` the bound is `0`.
* **§5b THE ERROR-CARRYING FORM** `tower_law_cov_error_bound`:
  `‖LHS − RHS‖ ≤ (1/(ℓ₀m)⁴)·Σ_{(u,i,x,j)} ‖R(defect)·v(b) − v(b)‖`, the defect being the loop
  holonomy `rhsTransport⁻¹ · lhsTransport`. The bound is a SUM of per-term defect displacements
  under the arrows' own normalization — not a `‖v‖`-times-constant estimate, and NOT `k`-uniform.
  `tower_law_cov_of_zero_defect` shows it collapses to the exact identity when every defect acts
  trivially.
* **§6 THE OBSTRUCTION.** `TransportCompose` FORCES a `V`-FREE identity on `U` alone
  (`transportCompose_forces_contourSplit`): the CMP95 contour must be ADDITIVE under block
  splitting, `hol_U(y,Γ_{y,u})·hol_U(u,Γ_{u,x}) = hol_U(y,Γ_{y,x})`. That is false at a curved `U`
  (`contourSplit_fails`), hence `no_unit_background_transportComposes`.
* **§6b THE OPERATOR-LEVEL REFUTATION** `tower_law_cov_refuted`: for the explicit curved `towerU`
  on `witL7` at the split `(ℓ₀,ℓ₁) = (2,4)`, **NO** `V` satisfies (TOWER-COV) — proved from two
  named single-bond test fields, with no appeal to §5's termwise route.

## HONEST SCOPE

* The refutation is at ONE explicit curved background on ONE explicit torus. It refutes the EXACT
  operator identity; it says nothing against the error-carrying form of §5b, which is what survives.
  **[STRUCK 2026-07-29, Kimi third gate on the survivor: "and what the tower actually needs" is
  FALSE, on three compiled counts. The bound is a true theorem that is WEAKER THAN ASSERTING
  NOTHING at the parameters that matter.]** See §5e's own strike for the numbers.
* §5b's bound is stated per coarse bond and in the `SuTwo` norm. It is NOT a `k`-uniform bound:
  nothing here controls the defect uniformly in the RG step, and converting the per-term sum into
  `C·α₁(U)·‖v‖` needs a bound on `‖R(defect) − id‖` (available in the shape
  `RMapLipschitz.norm_RMap_sub_self_le`) TOGETHER with a bound on the defect's own distance from
  `1`, which is a statement about the accumulated curvature over an `ℓ₁`-block and is NOT proved
  here. That is the remaining content of `[Q-TRANSPORT-COMPOSE]`.
* The refutation uses `towerU` on `witL7`, not `CoercivityRegular.curvedRegularU`: the latter lives
  on `witL5` (`6` sites per direction), where `4 ∤ 6`, so the split `(ℓ₀,ℓ₁) = (2,4)` is not even
  stateable there. `towerU`'s curvature is proved (`towerU_curved`), not asserted, and the
  flat/curved contrast is a ONE-PARAMETER mutation on the same torus and same split
  (`contourSplit_holds_at_trivialU` vs `contourSplit_fails`).
* `d = 3` throughout (the lattice layer is `Fin 3`), `SU(2)` throughout.
-/

namespace AdalyFormal.Balaban.TowerLawCov

open scoped Matrix

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.Q1Real (rZeroA transportPath GammaPath GammaPath_self straightSegment
  straightSegment_self periodicPathHolonomy_append periodicPathHolonomy_trivialU_eq_one)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne
  periodicLatticeShift_injective)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_blockOf_eq_image)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf unitToCoarse pathSite_mul_coarse
  shift_mul_blockOf blockOf_eq_biUnion_units units_pairwiseDisjoint sum_range_mul_decomp
  unit_block_sum tower_law)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the UNIT-scale path primitives

A unit-level forward path is a list of DIRECTIONS, each step advancing `ell` fine sites
(`coarseShift`). This is the level-`ℓ₀` analogue of `Target.ClayStatement.periodicPathHolonomy`,
restricted to forward steps — which is all the source's contours use, since every contour runs from
a block base to a point of its own block (`inBlock` gives `y μ ≤ x μ` coordinatewise). -/

/-- Endpoint of a unit-level forward path. -/
def coarsePathEndpoint (ell : ℕ) : PeriodicLatticeSite L → List (Fin 3) → PeriodicLatticeSite L
  | y, [] => y
  | y, μ :: rest => coarsePathEndpoint ell (coarseShift y ell μ) rest

/-- **Holonomy of a UNIT-level background `V` along a unit-level forward path.** Each factor
`V (y, μ)` is a unit bond — the coarse link from `y` to `coarseShift y ell μ`. This is the arrow
`Q(Ū)` needs and which `periodicPathHolonomy` cannot supply: `periodicPathHolonomy` steps by ONE
fine site, so it would read `Ū` at fine spacing and be the wrong object. -/
def coarsePathHolonomy {G : Type*} [Group G] (ell : ℕ) (V : PeriodicLinkConfiguration G L) :
    PeriodicLatticeSite L → List (Fin 3) → G
  | _, [] => 1
  | y, μ :: rest => V (y, μ) * coarsePathHolonomy ell V (coarseShift y ell μ) rest

/-- The trivial unit background transports nothing, along ANY unit path. -/
theorem coarsePathHolonomy_trivialU (ell : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    coarsePathHolonomy ell (trivialU L) y p = 1 := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih =>
    show (trivialU L) (y, μ) * coarsePathHolonomy ell (trivialU L) (coarseShift y ell μ) rest = 1
    rw [ih]
    simp [trivialU]

/-- The number of UNIT steps in direction `μ` carrying `a`'s `μ`-coordinate to `b`'s: the fine
count (`Q1Real.coordSteps`, exact across wraparound by `Fin` subtraction) divided by `ell`. -/
def coarseCoordSteps (ell : ℕ) (a b : PeriodicLatticeSite L) (μ : Fin 3) : ℕ :=
  (b μ - a μ).val / ell

/-- A unit-scale straight segment — `Q1Real.straightSegment` one level up. -/
def coarseStraightSegment (ell : ℕ) (a b : PeriodicLatticeSite L) (μ : Fin 3) : List (Fin 3) :=
  List.replicate (coarseCoordSteps ell a b μ) μ

/-- **`Γ̄_{y,u}` — CMP95 (1.7)'s staircase contour AT UNIT SCALE**: change coordinate `2`, then `1`,
then `0`, in that DESCENDING order, in unit steps. Structurally identical to `Q1Real.GammaPath`
(same `Function.update` chain, same order); only the step length differs. -/
def coarseGammaPath (ell : ℕ) (y x : PeriodicLatticeSite L) : List (Fin 3) :=
  coarseStraightSegment ell y x 2 ++
    (coarseStraightSegment ell (Function.update y 2 (x 2)) x 1 ++
      coarseStraightSegment ell (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0)

/-- **The unit-level transport path** CMP98 p.28's `Γ_{c₋,u} ∪ [u, u(i)]` assigns to the `i`-th unit
bond of the coarse bond based at `c₋` — `Q1Real.transportPath` one level up. -/
def coarseTransportPath (ell : ℕ) (cMinus u : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    List (Fin 3) :=
  coarseGammaPath ell cMinus u ++ List.replicate i μ

/-- The contour from a unit site to ITSELF is empty — the unit-scale analogue of
`Q1Real.GammaPath_self`, and the fact §6 turns into a `V`-free obstruction. -/
theorem coarseGammaPath_self (ell : ℕ) (a : PeriodicLatticeSite L) :
    coarseGammaPath ell a a = [] := by
  have h21 : ((2 : Fin 3)) ≠ ((1 : Fin 3)) := by decide
  have h20 : ((2 : Fin 3)) ≠ ((0 : Fin 3)) := by decide
  have h10 : ((1 : Fin 3)) ≠ ((0 : Fin 3)) := by decide
  simp only [coarseGammaPath, coarseStraightSegment, coarseCoordSteps,
    Function.update_of_ne h21.symm, Function.update_of_ne h20.symm, Function.update_of_ne h10.symm,
    sub_self]
  simp

theorem coarseTransportPath_self (ell : ℕ) (a : PeriodicLatticeSite L) (μ : Fin 3) :
    coarseTransportPath ell a a μ 0 = [] := by
  simp [coarseTransportPath, coarseGammaPath_self]

/-- `Q1Real.transportPath` at step `0` is exactly the bare contour. -/
theorem transportPath_zero (a b : PeriodicLatticeSite L) (μ : Fin 3) :
    transportPath a b μ 0 = GammaPath a b := by
  simp [transportPath, pathSite_zero, straightSegment_self]

#print axioms coarsePathHolonomy_trivialU
#print axioms coarseGammaPath_self
#print axioms coarseTransportPath_self
#print axioms transportPath_zero

/-! ## §2 — the COVARIANT unit → coarse arrow -/

/-- **`Q₁(V)` — the covariant unit→coarse arrow.** The one-step block-line average one level up,
carrying the unit-scale transport: average the unit bond field `B` over the `m³` unit sites of the
`ℓ₁`-block of `c₋`, line-integrating over `m` consecutive unit bonds in direction `c.2`, each
transported by `R` of the unit holonomy of the UNIT background `V` along `Γ̄_{c₋,u} ∪ [u,u(i)]`,
normalized `1/m⁴` (the true average at the unit lattice's own scale).

This is `ThirdLevelArrows.unitToCoarse` with `RMap (coarsePathHolonomy …)` inserted, in exactly the
place `LineIntegralCovariant.lineCoarseRestrictCov` inserts `RMap (periodicPathHolonomy …)` (via
`Q1Real.rZeroA`) at the fine level. -/
noncomputable def unitToCoarseCov (ell₀ m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L ell₀ → SuTwo) (c : CoarseBond L (ell₀ * m)) : SuTwo :=
  (1 / (m : ℝ) ^ 4) • ∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1,
    ∑ i ∈ Finset.range m,
      if h : pathSite u.1 c.2 (i * ell₀) ∈ CoarseLattice L ell₀ then
        RMap (coarsePathHolonomy ell₀ V c.1.1 (coarseTransportPath ell₀ c.1.1 u.1 c.2 i))
          (B (⟨pathSite u.1 c.2 (i * ell₀), h⟩, c.2))
      else 0

theorem unitToCoarseCov_add (ell₀ m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B1 B2 : CoarseBond L ell₀ → SuTwo) (c : CoarseBond L (ell₀ * m)) :
    unitToCoarseCov ell₀ m V (B1 + B2) c
      = unitToCoarseCov ell₀ m V B1 c + unitToCoarseCov ell₀ m V B2 c := by
  unfold unitToCoarseCov
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : pathSite u.1 c.2 (i * ell₀) ∈ CoarseLattice L ell₀
  · rw [dif_pos h, dif_pos h, dif_pos h]
    show RMap _ (B1 _ + B2 _) = _
    rw [map_add]
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

theorem unitToCoarseCov_smul (ell₀ m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (r : ℝ)
    (B : CoarseBond L ell₀ → SuTwo) (c : CoarseBond L (ell₀ * m)) :
    unitToCoarseCov ell₀ m V (r • B) c = r • unitToCoarseCov ell₀ m V B c := by
  unfold unitToCoarseCov
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : pathSite u.1 c.2 (i * ell₀) ∈ CoarseLattice L ell₀
  · rw [dif_pos h, dif_pos h]
    show RMap _ (r • B _) = r • RMap _ (B _)
    rw [map_smul]
  · rw [dif_neg h, dif_neg h, smul_zero]

/-- The covariant arrow as a `LinearMap`. Its DOMAIN is unit-bond fields — the type-level
realization of the two-arrow table (`ThirdLevelArrows` §, `CStarLevelCorrected.LevelSplit`). -/
noncomputable def unitToCoarseCovLM (ell₀ m : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (CoarseBond L ell₀ → SuTwo) →ₗ[ℝ] (CoarseBond L (ell₀ * m) → SuTwo) where
  toFun B := unitToCoarseCov ell₀ m V B
  map_add' B1 B2 := funext fun c => unitToCoarseCov_add ell₀ m V B1 B2 c
  map_smul' r B := funext fun c => unitToCoarseCov_smul ell₀ m V r B c

#print axioms unitToCoarseCov_add
#print axioms unitToCoarseCov_smul

/-! ## §3 — MUST-NOT-FIRE CONTROL: at `V = 1` the covariant arrow IS the flat one -/

/-- **The reduction.** `unitToCoarseCov ℓ₀ m 1 = ThirdLevelArrows.unitToCoarse ℓ₀ m`. -/
theorem unitToCoarseCov_trivialU (ell₀ m : ℕ) (B : CoarseBond L ell₀ → SuTwo)
    (c : CoarseBond L (ell₀ * m)) :
    unitToCoarseCov ell₀ m (trivialU L) B c = unitToCoarse ell₀ m B c := by
  unfold unitToCoarseCov unitToCoarse
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : pathSite u.1 c.2 (i * ell₀) ∈ CoarseLattice L ell₀
  · rw [dif_pos h, dif_pos h, coarsePathHolonomy_trivialU, RMap_one]
    rfl
  · rw [dif_neg h, dif_neg h]

/-- **THE CONTROL FIRES THE RIGHT WAY.** At `U = 1` and `V = 1` the covariant tower law REDUCES to
`ThirdLevelArrows.tower_law` — it agrees with the existing proved identity rather than contradicting
it. (This is the "must-not-fire" half: a covariant statement that broke the flat case would be
wrong.) -/
theorem tower_law_cov_at_trivial {ell₀ m : ℕ} (hell₀ : 0 < ell₀) (hm : 0 < m)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1)) (v : Bond L → SuTwo) :
    unitToCoarseCov ell₀ m (trivialU L) (lineCoarseRestrictCovLM (trivialU L) ell₀ v)
      = lineCoarseRestrictCovLM (trivialU L) (ell₀ * m) v := by
  funext c
  rw [unitToCoarseCov_trivialU]
  exact congrFun (tower_law hell₀ hm hdvd₀ v) c

#print axioms unitToCoarseCov_trivialU
#print axioms tower_law_cov_at_trivial

/-! ## §4 — THE TWO EXPANSIONS

Both sides of (TOWER-COV), written over the SAME index set `(u, i, x, j)` and with the SAME weight
`1/(ℓ₀m)⁴`. After this the tower law is a statement about GROUP ELEMENTS ONLY: the combinatorics is
discharged, and only the transports can differ. -/

/-- The TWO-STEP transport attached to the datum `(u, i, x, j)`: unit-level holonomy of `V` from
`c₋` to the `i`-th unit site, then fine holonomy of `U` from there to the `j`-th fine bond. -/
noncomputable def lhsTransport (ell₀ : ℕ)
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y u x : PeriodicLatticeSite L) (μ : Fin 3) (i j : ℕ) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  coarsePathHolonomy ell₀ V y (coarseTransportPath ell₀ y u μ i)
    * periodicPathHolonomy U (pathSite u μ (i * ell₀))
        (transportPath (pathSite u μ (i * ell₀)) (pathSite x μ (i * ell₀)) μ j)

/-- The ONE-STEP transport at the same datum: fine holonomy of `U` all the way from `c₋`. -/
noncomputable def rhsTransport (ell₀ : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y x : PeriodicLatticeSite L) (μ : Fin 3) (i j : ℕ) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  periodicPathHolonomy U y (transportPath y x μ (i * ell₀ + j))

/-- The scalar bookkeeping: the two one-step normalizations compose into the two-step one,
`(1/m⁴)·(1/ℓ₀⁴) = 1/(ℓ₀m)⁴`. Isolated so the uniform-rescale test has a single target. -/
theorem norm_compose (ell₀ m : ℕ) :
    (1 / (m : ℝ) ^ 4) * (1 / (ell₀ : ℝ) ^ 4) = 1 / ((ell₀ : ℝ) * (m : ℝ)) ^ 4 := by
  rw [one_div_mul_one_div, mul_pow]
  ring

theorem lhs_expand {ell₀ m : ℕ} (hell₀ : 0 < ell₀)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) (c : CoarseBond L (ell₀ * m)) :
    unitToCoarseCov ell₀ m V (lineCoarseRestrictCovLM U ell₀ v) c
      = (1 / ((ell₀ : ℝ) * (m : ℝ)) ^ 4) •
          ∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∑ i ∈ Finset.range m,
            ∑ x ∈ blockOf u.1 ell₀, ∑ j ∈ Finset.range ell₀,
              RMap (lhsTransport ell₀ V U c.1.1 u.1 x c.2 i j)
                (v (pathSite x c.2 (i * ell₀ + j), c.2)) := by
  have hinj : ∀ n : ℕ,
      Function.Injective (fun x : PeriodicLatticeSite L => pathSite x c.2 n) := fun n =>
    Function.Injective.iterate (periodicLatticeShift_injective c.2) n
  have hterm : ∀ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∀ i ∈ Finset.range m,
      (if h : pathSite u.1 c.2 (i * ell₀) ∈ CoarseLattice L ell₀ then
        RMap (coarsePathHolonomy ell₀ V c.1.1 (coarseTransportPath ell₀ c.1.1 u.1 c.2 i))
          (lineCoarseRestrictCovLM U ell₀ v (⟨pathSite u.1 c.2 (i * ell₀), h⟩, c.2))
      else 0)
        = (1 / (ell₀ : ℝ) ^ 4) • ∑ x ∈ blockOf u.1 ell₀, ∑ j ∈ Finset.range ell₀,
            RMap (lhsTransport ell₀ V U c.1.1 u.1 x c.2 i j)
              (v (pathSite x c.2 (i * ell₀ + j), c.2)) := by
    intro u _ i _
    rw [dif_pos (pathSite_mul_coarse ell₀ hdvd₀ u.2 c.2 i), lineCoarseRestrictCovLM_apply]
    show RMap _ (lineCoarseRestrictCov U ell₀ v _) = _
    unfold lineCoarseRestrictCov
    rw [map_smul, map_sum]
    congr 1
    rw [shift_mul_blockOf hell₀ hdvd₀ u.2 c.2 i,
      Finset.sum_image (fun a _ b _ h => hinj (i * ell₀) h)]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold rZeroA
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcomp : pathSite x c.2 (i * ell₀ + j) = pathSite (pathSite x c.2 (i * ell₀)) c.2 j := by
      rw [show i * ell₀ + j = j + i * ell₀ by ring]
      exact Function.iterate_add_apply _ j (i * ell₀) x
    unfold lhsTransport
    rw [RMap_mul_apply, hcomp]
  unfold unitToCoarseCov
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun i hi => hterm u hu i hi))]
  simp only [← Finset.smul_sum]
  rw [smul_smul, norm_compose]

theorem rhs_expand {ell₀ m : ℕ} (hell₀ : 0 < ell₀)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) (c : CoarseBond L (ell₀ * m)) :
    lineCoarseRestrictCovLM U (ell₀ * m) v c
      = (1 / ((ell₀ : ℝ) * (m : ℝ)) ^ 4) •
          ∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∑ i ∈ Finset.range m,
            ∑ x ∈ blockOf u.1 ell₀, ∑ j ∈ Finset.range ell₀,
              RMap (rhsTransport ell₀ U c.1.1 x c.2 i j)
                (v (pathSite x c.2 (i * ell₀ + j), c.2)) := by
  have hsplit : ∀ g : ℕ → SuTwo, ∑ k ∈ Finset.range (ell₀ * m), g k
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range ell₀, g (i * ell₀ + j) := by
    intro g
    rw [show ell₀ * m = m * ell₀ from Nat.mul_comm ell₀ m, sum_range_mul_decomp m ell₀ hell₀,
      Finset.sum_product]
  have hdecomp : ∀ x : PeriodicLatticeSite L,
      rZeroA U c.1.1 x v c.2 (ell₀ * m)
        = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range ell₀,
            RMap (rhsTransport ell₀ U c.1.1 x c.2 i j)
              (v (pathSite x c.2 (i * ell₀ + j), c.2)) := by
    intro x
    unfold rZeroA rhsTransport
    exact hsplit _
  rw [lineCoarseRestrictCovLM_apply]
  show lineCoarseRestrictCov U (ell₀ * m) v c = _
  unfold lineCoarseRestrictCov
  have hcast : (1 / ((ell₀ * m : ℕ) : ℝ) ^ 4) = (1 / ((ell₀ : ℝ) * (m : ℝ)) ^ 4) := by
    push_cast
    ring
  rw [hcast]
  congr 1
  rw [blockOf_eq_biUnion_units hell₀ (Dvd.intro m rfl) hdvd₀ c.1.2,
    Finset.sum_biUnion (units_pairwiseDisjoint ell₀ (ell₀ * m) c.1.1)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_congr rfl (fun x _ => hdecomp x), Finset.sum_comm]

#print axioms norm_compose
#print axioms lhs_expand
#print axioms rhs_expand

/-! ## §5 — the EXACT covariant tower law, under the termwise transport hypothesis -/

/-- **`[Q-TRANSPORT-COMPOSE]`, stated exactly.** The two-step transport equals the one-step one, on
every term of the expansion. -/
def TransportCompose (ell₀ m : ℕ)
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) : Prop :=
  ∀ u ∈ unitSitesOf ell₀ (ell₀ * m) y, ∀ i ∈ Finset.range m, ∀ x ∈ blockOf u.1 ell₀,
    ∀ j ∈ Finset.range ell₀,
      lhsTransport ell₀ V U y u.1 x μ i j = rhsTransport ell₀ U y x μ i j

set_option maxHeartbeats 1000000 in
/-- **(TOWER-COV) holds under `TransportCompose`.** -/
theorem tower_law_cov_of_transportCompose {ell₀ m : ℕ} (hell₀ : 0 < ell₀)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) (c : CoarseBond L (ell₀ * m))
    (h : TransportCompose ell₀ m V U c.1.1 c.2) :
    unitToCoarseCov ell₀ m V (lineCoarseRestrictCovLM U ell₀ v) c
      = lineCoarseRestrictCovLM U (ell₀ * m) v c := by
  rw [lhs_expand hell₀ hdvd₀ V U v c, rhs_expand hell₀ hdvd₀ U v c]
  refine congrArg _ (Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun i hi =>
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun j hj => ?_)
  rw [h u hu i hi x hx j hj]

#print axioms tower_law_cov_of_transportCompose

/-! ## §5b — THE ERROR-CARRYING FORM

An exact operator identity is too strong at general `U` (§6 proves it false). What IS true is a
bound: the two sides differ by exactly the accumulated TRANSPORT DEFECT

  `towerDefect := (one-step transport)⁻¹ · (two-step transport)`,

a loop holonomy based at `c₋`. When every defect is `1` the bound is `0` and the identity is
recovered; the flat case (§3) is that instance. A gate specifically noted the error-carrying
version was stated nowhere; this is it. -/

/-- **The transport defect** — the closed loop `c₋ → (two-step route) → bond base → (one-step route
reversed) → c₋`. This is the object `[Q-TRANSPORT-COMPOSE]` is really about. -/
noncomputable def towerDefect (ell₀ : ℕ)
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y u x : PeriodicLatticeSite L) (μ : Fin 3) (i j : ℕ) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  (rhsTransport ell₀ U y x μ i j)⁻¹ * lhsTransport ell₀ V U y u x μ i j

/-- Unitary LEFT-invariance of `frobSq`.

**LAW-19 prior-art disclosure (completed after a nested-validator finding).** This exact statement,
under this exact name, already exists at `Balaban/LemmaAssembly.lean:291`; the isometry
`‖R(g)X‖ = ‖X‖` below already exists at `Balaban/AlphaAnalyticity.lean:323` and
`Balaban/FaithfulCoercivitySU2.lean:205`. **None of those three modules is in this module's import
closure** (checked by walking the closure, not assumed), and importing any of them would pull a
heavy chain in for four lines of algebra — so both are re-proved here rather than imported. The
duplication is deliberate and is recorded so it is not rediscovered a fourth time. -/
theorem frobSq_mul_left_isometry (W M : Matrix (Fin 2) (Fin 2) ℂ) (hW : Wᴴ * W = 1) :
    RMapLipschitz.frobSq (W * M) = RMapLipschitz.frobSq M := by
  rw [RMapLipschitz.frobSq_eq_trace, Matrix.conjTranspose_mul,
    show W * M * (Mᴴ * Wᴴ) = W * (M * Mᴴ) * Wᴴ by noncomm_ring,
    Matrix.trace_mul_comm (W * (M * Mᴴ)) Wᴴ,
    show Wᴴ * (W * (M * Mᴴ)) = Wᴴ * W * (M * Mᴴ) by noncomm_ring, hW, Matrix.one_mul,
    ← RMapLipschitz.frobSq_eq_trace]

/-- **`R(g)` is an isometry of `𝔰𝔲(2)`.** -/
theorem norm_RMap (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    ‖RMap g X‖ = ‖X‖ := by
  have hg : (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp g.2.1
    rwa [Matrix.star_eq_conjTranspose] at h
  have hgh : (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * ((g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)ᴴ = 1 := by
    rwa [Matrix.conjTranspose_conjTranspose]
  have hsq : ‖RMap g X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [RMapLipschitz.norm_sq_eq_half_frobSq, RMapLipschitz.norm_sq_eq_half_frobSq,
      RMap_coe_apply, RMapLipschitz.frobSq_mul_right_isometry _ _ hgh,
      frobSq_mul_left_isometry _ _ hg]
  rw [← Real.sqrt_sq (norm_nonneg (RMap g X)), hsq, Real.sqrt_sq (norm_nonneg X)]

/-- Two transports applied to the same vector differ by exactly the defect, ISOMETRICALLY. -/
theorem norm_transport_diff (ell₀ : ℕ)
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y u x : PeriodicLatticeSite L) (μ : Fin 3) (i j : ℕ) (Y : SuTwo) :
    ‖RMap (lhsTransport ell₀ V U y u x μ i j) Y - RMap (rhsTransport ell₀ U y x μ i j) Y‖
      = ‖RMap (towerDefect ell₀ V U y u x μ i j) Y - Y‖ := by
  set gR := rhsTransport ell₀ U y x μ i j with hgR
  set gL := lhsTransport ell₀ V U y u x μ i j with hgL
  have hfac : gL = gR * towerDefect ell₀ V U y u x μ i j := by
    unfold towerDefect
    rw [← hgR, ← hgL, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hfac, RMap_mul, LinearMap.comp_apply, ← map_sub, norm_RMap]

set_option maxHeartbeats 1000000 in
/-- **THE ERROR-CARRYING TOWER LAW.** The failure of (TOWER-COV) at a coarse bond is bounded by the
normalized sum of the `(ℓ₀m)⁴` transport defects. Every constant is counted, not chosen: the weight
`1/(ℓ₀m)⁴` is the SAME one both arrows carry (§4), and the index set is the same. Exact identity
⇔ every defect acts trivially on the field. -/
theorem tower_law_cov_error_bound {ell₀ m : ℕ} (hell₀ : 0 < ell₀)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) (c : CoarseBond L (ell₀ * m)) :
    ‖unitToCoarseCov ell₀ m V (lineCoarseRestrictCovLM U ell₀ v) c
        - lineCoarseRestrictCovLM U (ell₀ * m) v c‖
      ≤ (1 / ((ell₀ : ℝ) * (m : ℝ)) ^ 4) *
          ∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∑ i ∈ Finset.range m,
            ∑ x ∈ blockOf u.1 ell₀, ∑ j ∈ Finset.range ell₀,
              ‖RMap (towerDefect ell₀ V U c.1.1 u.1 x c.2 i j)
                  (v (pathSite x c.2 (i * ell₀ + j), c.2))
                - v (pathSite x c.2 (i * ell₀ + j), c.2)‖ := by
  rw [lhs_expand hell₀ hdvd₀ V U v c, rhs_expand hell₀ hdvd₀ U v c, ← smul_sub]
  rw [show (∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∑ i ∈ Finset.range m,
        ∑ x ∈ blockOf u.1 ell₀, ∑ j ∈ Finset.range ell₀,
          RMap (lhsTransport ell₀ V U c.1.1 u.1 x c.2 i j)
            (v (pathSite x c.2 (i * ell₀ + j), c.2)))
      - (∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∑ i ∈ Finset.range m,
        ∑ x ∈ blockOf u.1 ell₀, ∑ j ∈ Finset.range ell₀,
          RMap (rhsTransport ell₀ U c.1.1 x c.2 i j)
            (v (pathSite x c.2 (i * ell₀ + j), c.2)))
      = ∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∑ i ∈ Finset.range m,
        ∑ x ∈ blockOf u.1 ell₀, ∑ j ∈ Finset.range ell₀,
          (RMap (lhsTransport ell₀ V U c.1.1 u.1 x c.2 i j)
              (v (pathSite x c.2 (i * ell₀ + j), c.2))
            - RMap (rhsTransport ell₀ U c.1.1 x c.2 i j)
              (v (pathSite x c.2 (i * ell₀ + j), c.2))) from by
    simp only [← Finset.sum_sub_distrib]]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((ell₀:ℝ)*(m:ℝ))^4)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun u _ => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun x _ => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  exact le_of_eq (norm_transport_diff ell₀ V U c.1.1 u.1 x c.2 i j _)

/-- **THE EXACT CASE IS THE ZERO-DEFECT CASE.** If every defect acts trivially on the field, the
error bound is `0` and (TOWER-COV) holds exactly. This is the must-not-fire direction of §5b: the
bound is not a vacuous inequality that never becomes an equality. -/
theorem tower_law_cov_of_zero_defect {ell₀ m : ℕ} (hell₀ : 0 < ell₀)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) (c : CoarseBond L (ell₀ * m))
    (h : ∀ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∀ i ∈ Finset.range m,
      ∀ x ∈ blockOf u.1 ell₀, ∀ j ∈ Finset.range ell₀,
        RMap (towerDefect ell₀ V U c.1.1 u.1 x c.2 i j)
            (v (pathSite x c.2 (i * ell₀ + j), c.2))
          = v (pathSite x c.2 (i * ell₀ + j), c.2)) :
    unitToCoarseCov ell₀ m V (lineCoarseRestrictCovLM U ell₀ v) c
      = lineCoarseRestrictCovLM U (ell₀ * m) v c := by
  have hb := tower_law_cov_error_bound hell₀ hdvd₀ V U v c
  have hzero : (∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∑ i ∈ Finset.range m,
      ∑ x ∈ blockOf u.1 ell₀, ∑ j ∈ Finset.range ell₀,
        ‖RMap (towerDefect ell₀ V U c.1.1 u.1 x c.2 i j)
            (v (pathSite x c.2 (i * ell₀ + j), c.2))
          - v (pathSite x c.2 (i * ell₀ + j), c.2)‖) = 0 := by
    refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun i hi =>
      Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun j hj => ?_
    rw [h u hu i hi x hx j hj, sub_self, norm_zero]
  rw [hzero, mul_zero] at hb
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)

#print axioms frobSq_mul_left_isometry
#print axioms norm_RMap
#print axioms norm_transport_diff
#print axioms tower_law_cov_error_bound
#print axioms tower_law_cov_of_zero_defect

/-! ### §5c — the defect is CONTROLLED BY THE BACKGROUND'S DEVIATION FROM FLAT

§5b leaves the defect abstract. Here it is bounded by the number of links the two routes traverse
times the per-link displacement — the `O(path length · α₁)` shape Bałaban's own "localizing the
operators in `Δ_k`" step needs.

**Method note (why no matrix-norm triangle inequality appears).** The natural route
— `‖R(d) − id‖ ≲ frobNorm(d − 1)` and then Minkowski on `frobNorm` — is BLOCKED in this import
closure: `RMapLipschitz` supplies only `frobSq_sub_le` (with a factor `2`, not subadditivity), and
Mathlib's Frobenius `NormedAddCommGroup` on `Matrix (Fin 2) (Fin 2) ℂ` cannot be opened here
without colliding with `CovariantOperators.instNormedSpaceRealMatrix`, a GLOBAL instance built over
the `L²`-operator norm. The route taken instead needs no matrix norm at all: split the product
inside `R` and use `R`'s isometry (`norm_RMap`). It is also sharper, since it never passes through
the lossy `frobSq_sub_le`. -/

/-- **THE COMPOSITION ESTIMATE.** `‖R(gh)X − X‖ ≤ ‖R(h)X − X‖ + ‖R(g)X − X‖`. -/
theorem norm_RMap_mul_sub_self_le (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    ‖RMap (g * h) X - X‖ ≤ ‖RMap h X - X‖ + ‖RMap g X - X‖ := by
  have hsplit : RMap (g * h) X - X = RMap g (RMap h X - X) + (RMap g X - X) := by
    rw [map_sub, RMap_mul_apply]
    abel
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_RMap]

/-- Inverting a transport does not change its displacement. -/
theorem norm_RMap_inv_sub_self (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    ‖RMap g⁻¹ X - X‖ = ‖RMap g X - X‖ := by
  have h : RMap g (RMap g⁻¹ X - X) = X - RMap g X := by
    rw [map_sub, RMap_mul_apply, mul_inv_cancel, RMap_one]
    rfl
  calc ‖RMap g⁻¹ X - X‖ = ‖RMap g (RMap g⁻¹ X - X)‖ := (norm_RMap g _).symm
    _ = ‖X - RMap g X‖ := by rw [h]
    _ = ‖RMap g X - X‖ := norm_sub_rev _ _

/-- **FINE PATHS.** A holonomy's displacement is at most the path length times the per-link
displacement. Handles backward steps (`norm_RMap_inv_sub_self`). -/
theorem norm_RMap_hol_sub_self_le {α : ℝ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (X : SuTwo)
    (hU : ∀ b : Bond L, ‖RMap (U b) X - X‖ ≤ α) :
    ∀ (y : PeriodicLatticeSite L) (s : List (Fin 3 × Bool)),
      ‖RMap (periodicPathHolonomy U y s) X - X‖ ≤ (s.length : ℝ) * α := by
  intro y s
  induction s generalizing y with
  | nil =>
    show ‖RMap 1 X - X‖ ≤ _
    rw [RMap_one]
    simp
  | cons st rest ih =>
    have hstep : ‖RMap (if st.2 then U (y, st.1) else (U (periodicLatticeStep y st, st.1))⁻¹) X
        - X‖ ≤ α := by
      by_cases hs : st.2 = true
      · rw [hs]
        simpa using hU (y, st.1)
      · have hs' : st.2 = false := by simpa using hs
        rw [hs']
        simp only [Bool.false_eq_true, if_false, norm_RMap_inv_sub_self]
        exact hU _
    have hrest := ih (periodicLatticeStep y st)
    show ‖RMap ((if st.2 then U (y, st.1) else (U (periodicLatticeStep y st, st.1))⁻¹)
        * periodicPathHolonomy U (periodicLatticeStep y st) rest) X - X‖ ≤ _
    refine le_trans (norm_RMap_mul_sub_self_le _ _ X) ?_
    simp only [List.length_cons]
    push_cast
    linarith

/-- **UNIT PATHS.** The same bound for the unit-scale holonomy of `V`. -/
theorem norm_RMap_coarseHol_sub_self_le {α : ℝ} (ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (X : SuTwo)
    (hV : ∀ b : Bond L, ‖RMap (V b) X - X‖ ≤ α) :
    ∀ (y : PeriodicLatticeSite L) (p : List (Fin 3)),
      ‖RMap (coarsePathHolonomy ell V y p) X - X‖ ≤ (p.length : ℝ) * α := by
  intro y p
  induction p generalizing y with
  | nil =>
    show ‖RMap 1 X - X‖ ≤ _
    rw [RMap_one]
    simp
  | cons μ rest ih =>
    have hrest := ih (coarseShift y ell μ)
    show ‖RMap (V (y, μ) * coarsePathHolonomy ell V (coarseShift y ell μ) rest) X - X‖ ≤ _
    refine le_trans (norm_RMap_mul_sub_self_le _ _ X) ?_
    have h1 := hV (y, μ)
    simp only [List.length_cons]
    push_cast
    linarith

/-- **THE DEFECT BOUND.** The transport defect's displacement is at most the TOTAL number of links
the two routes traverse, times the per-link displacement `α`. At `α = 0` (both backgrounds acting
trivially on `X`) the defect vanishes and `tower_law_cov_of_zero_defect` gives the exact identity —
so the bound is tight at the flat point, not merely valid there. -/
theorem towerDefect_norm_le {α : ℝ} (ell₀ : ℕ)
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (X : SuTwo)
    (hU : ∀ b : Bond L, ‖RMap (U b) X - X‖ ≤ α)
    (hV : ∀ b : Bond L, ‖RMap (V b) X - X‖ ≤ α)
    (y u x : PeriodicLatticeSite L) (μ : Fin 3) (i j : ℕ) :
    ‖RMap (towerDefect ell₀ V U y u x μ i j) X - X‖
      ≤ (((coarseTransportPath ell₀ y u μ i).length : ℝ)
          + ((transportPath (pathSite u μ (i * ell₀)) (pathSite x μ (i * ell₀)) μ j).length : ℝ)
          + ((transportPath y x μ (i * ell₀ + j)).length : ℝ)) * α := by
  have hL : ‖RMap (lhsTransport ell₀ V U y u x μ i j) X - X‖
      ≤ ((transportPath (pathSite u μ (i * ell₀)) (pathSite x μ (i * ell₀)) μ j).length : ℝ) * α
        + ((coarseTransportPath ell₀ y u μ i).length : ℝ) * α := by
    refine le_trans (norm_RMap_mul_sub_self_le _ _ X) (add_le_add ?_ ?_)
    · exact norm_RMap_hol_sub_self_le U X hU _ _
    · exact norm_RMap_coarseHol_sub_self_le ell₀ V X hV _ _
  have hR : ‖RMap (rhsTransport ell₀ U y x μ i j) X - X‖
      ≤ ((transportPath y x μ (i * ell₀ + j)).length : ℝ) * α :=
    norm_RMap_hol_sub_self_le U X hU _ _
  have hRinv : ‖RMap (rhsTransport ell₀ U y x μ i j)⁻¹ X - X‖
      ≤ ((transportPath y x μ (i * ell₀ + j)).length : ℝ) * α := by
    rw [norm_RMap_inv_sub_self]
    exact hR
  unfold towerDefect
  refine le_trans (norm_RMap_mul_sub_self_le _ _ X) ?_
  have := hL
  have := hRinv
  linarith

#print axioms norm_RMap_mul_sub_self_le
#print axioms norm_RMap_inv_sub_self
#print axioms norm_RMap_hol_sub_self_le
#print axioms norm_RMap_coarseHol_sub_self_le
#print axioms towerDefect_norm_le

/-! ### §5d — the assembled bound: the weight and the term count CANCEL EXACTLY

The `1/(ℓ₀m)⁴` in front is the arrows' own normalization; the expansion has exactly `(ℓ₀m)⁴` terms.
Counting them is what turns §5b's sum into a clean sup bound, and it is also the uniform-rescale
test on the load-bearing normalization: multiply the weight by any `t ≠ 1` and this cancellation —
hence `tower_law_cov_error_uniform` and, at `t`-scaled weight, `tower_law_cov_at_trivial` — fails. -/

/-- **THE TERM COUNT.** `|unitSites| · m · |ℓ₀-block| · ℓ₀ = m³ · m · ℓ₀³ · ℓ₀ = (ℓ₀m)⁴`. The unit
count `m³` is DERIVED (from the block partition and `card_blockOf_of_coarse`), not asserted. -/
theorem expansion_card {ell₀ m : ℕ} (hell₀ : 0 < ell₀)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1)) (hdvd₁ : ∀ μ : Fin 3, (ell₀ * m) ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L (ell₀ * m)) :
    ∑ u ∈ unitSitesOf ell₀ (ell₀ * m) y, ∑ _i ∈ Finset.range m, ∑ _x ∈ blockOf u.1 ell₀,
      ∑ _j ∈ Finset.range ell₀, (1 : ℝ) = ((ell₀ : ℝ) * (m : ℝ)) ^ 4 := by
  -- the unit count, derived from the partition
  have hpart : (blockOf y (ell₀ * m)).card
      = ∑ u ∈ unitSitesOf ell₀ (ell₀ * m) y, (blockOf u.1 ell₀).card := by
    rw [blockOf_eq_biUnion_units hell₀ (Dvd.intro m rfl) hdvd₀ hy]
    exact Finset.card_biUnion (fun a ha b hb hne =>
      units_pairwiseDisjoint ell₀ (ell₀ * m) y (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne)
  have hblk : ∀ u ∈ unitSitesOf ell₀ (ell₀ * m) y,
      (blockOf (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell₀}).1 ell₀).card
        = ell₀ ^ 3 := fun u _ => card_blockOf_of_coarse hdvd₀ u.2
  rw [Finset.sum_congr rfl hblk, Finset.sum_const, smul_eq_mul,
    card_blockOf_of_coarse hdvd₁ hy] at hpart
  have hunits : (unitSitesOf ell₀ (ell₀ * m) y).card = m ^ 3 := by
    have he : (0 : ℕ) < ell₀ ^ 3 := pow_pos hell₀ 3
    have : (unitSitesOf ell₀ (ell₀ * m) y).card * ell₀ ^ 3 = m ^ 3 * ell₀ ^ 3 := by
      rw [← hpart]; ring
    exact Nat.eq_of_mul_eq_mul_right he this
  -- now collapse the four constant sums
  have hstep : ∀ u ∈ unitSitesOf ell₀ (ell₀ * m) y,
      (∑ _i ∈ Finset.range m,
        ∑ _x ∈ blockOf (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell₀}).1 ell₀,
          ∑ _j ∈ Finset.range ell₀, (1 : ℝ))
        = (m : ℝ) * (ell₀ : ℝ) ^ 3 * (ell₀ : ℝ) := by
    intro u hu
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hblk u hu]
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_const, hunits, nsmul_eq_mul]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- **THE ASSEMBLED ERROR BOUND.** The tower-law failure at a coarse bond is at most the WORST
per-term defect displacement — the normalization and the term count cancel exactly. Combining with
`towerDefect_norm_le` gives the fully quantitative statement: the error is at most
`(total route length) · (per-link displacement)`. -/
theorem tower_law_cov_error_uniform {ell₀ m : ℕ} (hell₀ : 0 < ell₀) (hm : 0 < m)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1)) (hdvd₁ : ∀ μ : Fin 3, (ell₀ * m) ∣ (L μ + 1))
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) (c : CoarseBond L (ell₀ * m)) (E : ℝ)
    (hE : ∀ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∀ i ∈ Finset.range m,
      ∀ x ∈ blockOf u.1 ell₀, ∀ j ∈ Finset.range ell₀,
        ‖RMap (towerDefect ell₀ V U c.1.1 u.1 x c.2 i j)
            (v (pathSite x c.2 (i * ell₀ + j), c.2))
          - v (pathSite x c.2 (i * ell₀ + j), c.2)‖ ≤ E) :
    ‖unitToCoarseCov ell₀ m V (lineCoarseRestrictCovLM U ell₀ v) c
        - lineCoarseRestrictCovLM U (ell₀ * m) v c‖ ≤ E := by
  refine le_trans (tower_law_cov_error_bound hell₀ hdvd₀ V U v c) ?_
  have hcount := expansion_card (L := L) hell₀ hdvd₀ hdvd₁ c.1.2
  have hbound : (∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∑ i ∈ Finset.range m,
      ∑ x ∈ blockOf u.1 ell₀, ∑ j ∈ Finset.range ell₀,
        ‖RMap (towerDefect ell₀ V U c.1.1 u.1 x c.2 i j)
            (v (pathSite x c.2 (i * ell₀ + j), c.2))
          - v (pathSite x c.2 (i * ell₀ + j), c.2)‖)
      ≤ ∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∑ _i ∈ Finset.range m,
          ∑ _x ∈ blockOf u.1 ell₀, ∑ _j ∈ Finset.range ell₀, E := by
    refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun i hi =>
      Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun j hj => hE u hu i hi x hx j hj
  have hEnn : 0 ≤ E := by
    have hne : (unitSitesOf ell₀ (ell₀ * m) c.1.1).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp] at hcount
      simp only [Finset.sum_empty] at hcount
      have : (0 : ℝ) < ((ell₀ : ℝ) * (m : ℝ)) ^ 4 := by
        have h1 : (0 : ℝ) < (ell₀ : ℝ) := by exact_mod_cast hell₀
        have h2 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        positivity
      linarith
    obtain ⟨u, hu⟩ := hne
    obtain ⟨x, hx⟩ : (blockOf (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell₀}).1
        ell₀).Nonempty :=
      ⟨u.1, by rw [mem_blockOf]; exact fun ρ => ⟨le_refl _, by omega⟩⟩
    exact le_trans (norm_nonneg _)
      (hE u hu 0 (Finset.mem_range.mpr hm) x hx 0 (Finset.mem_range.mpr hell₀))
  have hEsum : (∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∑ _i ∈ Finset.range m,
      ∑ _x ∈ blockOf u.1 ell₀, ∑ _j ∈ Finset.range ell₀, E)
      = ((ell₀ : ℝ) * (m : ℝ)) ^ 4 * E := by
    rw [← hcount, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => (one_mul E).symm
  rw [hEsum] at hbound
  have hpos : (0 : ℝ) < ((ell₀ : ℝ) * (m : ℝ)) ^ 4 := by
    have h1 : (0 : ℝ) < (ell₀ : ℝ) := by exact_mod_cast hell₀
    have h2 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    positivity
  calc (1 / ((ell₀ : ℝ) * (m : ℝ)) ^ 4) * _
      ≤ (1 / ((ell₀ : ℝ) * (m : ℝ)) ^ 4) * (((ell₀ : ℝ) * (m : ℝ)) ^ 4 * E) := by
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = E := by field_simp

#print axioms expansion_card
#print axioms tower_law_cov_error_uniform

/-! ### §5e — the `α₁` form: `‖LHS − RHS‖ ≤ N · 2α₁ · ‖v‖`

**[BILLING STRUCK 2026-07-29 — Kimi third gate, MIXED verdict. The theorem SURVIVES; the sentence
"The shape the tower actually needs" does not.]**

`α₁` bounds each link's Frobenius distance from `1`, `N` bounds the links the two routes traverse,
`Kv` bounds the field. At `α₁ = 0` the bound is `0` and the identity is exact.

**WHAT SURVIVED the prosecution** (and it is not nothing): the theorem is kernel-true; it is NOT
content-free — `hlen` pins `N` from BELOW, with `N_max = 20` computed on a concrete torus, so a
caller cannot shrink `N` to trivialise the statement; it is degenerate-safe across `m = 1`,
`ell₀ = 1`, `v = 0`, `Kv = 0`, boundary `c`, and `N = 0`; and the chain
`_error_bound → _uniform → _alpha` is faithful, with `expansion_card`'s `(ell₀·m)⁴` cancelling the
normalisation EXACTLY rather than approximately.

**WHAT DID NOT, measured on this file's OWN curved witness with `α₁` and `Kv` proved TIGHT**
(`towerU_alpha_tight`, `testField_kv_tight` — so the slop is in the bound, not in loose inputs):

| quantity | value |
|---|---|
| true LHS | `1/128` |
| this bound's RHS, at the tightest legal `N = 20` | `20 · 2 · 2 · 1 = 80` |
| trivial a-priori bound on the LHS | `2·Kv = 2` |

**The bound is 40× WEAKER than the trivial a-priori bound, and 10240× off the truth.** Arithmetic
re-checked by hand by the main loop, and the tightness lemmas re-elaborated independently. A bound
one may always replace by "the norm is at most `2·Kv`" and lose nothing is not the shape anything
needs.

**And it does not survive iteration on this file's own stated scalings.** With `α₁^unit ~ ell₀·α₁^fine`
and `N ~ 3·ell₁`, the per-step defect bound grows like `ell₀²`, **crosses the trivial bound between
RG steps `k = 2` and `k = 3`**, and accumulates like `4^k`.

**A STRUCTURAL FINDING, and the sharpest of the three:** this file **cannot even STATE the
cross-step compounding question from its own quantifiers.** `α₁` at step 2 depends on the
already-coarsened field from step 1, which is itself carrying step-1's error — and nothing here
tracks that. So "does the bound survive iteration" is not merely unproved here; it is not
expressible here.

`k`-uniformity is therefore **NOT DETERMINED**, honestly, and the missing ingredient is named: a
loop/curvature defect estimate plus cross-step `α₁` control. That is what a successor form has to
supply, and it must beat `2·Kv` to be worth stating at all.

**One over-strong hypothesis, also compiled:** `hdvd₁` is NOT needed for the conclusion — a
`hdvd₁`-free reproof compiles. It is inherited, not load-bearing.

`N` is left as a HYPOTHESIS rather than computed: bounding the CMP95 staircase's length needs the
block geometry (`3ℓ₁` in the worst case), which is a separate computation and is NOT done here. -/

/-- The per-link displacement hypothesis of §5c, supplied from the tree's own sharp Lipschitz bound
`RMapLipschitz.norm_RMap_sub_self_le` (reused, not re-derived — LAW-19). -/
theorem link_displacement_le {α₁ : ℝ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (X : SuTwo)
    (hU : ∀ b : Bond L,
      RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α₁) :
    ∀ b : Bond L, ‖RMap (U b) X - X‖ ≤ 2 * α₁ * ‖X‖ := by
  intro b
  refine le_trans (RMapLipschitz.norm_RMap_sub_self_le (U b) X) ?_
  have h1 := hU b
  have h2 := norm_nonneg X
  have h3 := RMapLipschitz.frobNorm_nonneg ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **THE `α₁` ERROR BOUND.** With every fine link and every unit link within Frobenius distance
`α₁` of `1`, the field bounded by `Kv`, and each term's two routes traversing at most `N` links, the
covariant tower law holds up to `N · 2α₁ · Kv`. Setting `α₁ = 0` recovers the exact identity. -/
theorem tower_law_cov_error_alpha {ell₀ m : ℕ} (hell₀ : 0 < ell₀) (hm : 0 < m)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1)) (hdvd₁ : ∀ μ : Fin 3, (ell₀ * m) ∣ (L μ + 1))
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) (c : CoarseBond L (ell₀ * m))
    {α₁ Kv : ℝ} (N : ℕ) (hα₁ : 0 ≤ α₁)
    (hUf : ∀ b : Bond L, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α₁)
    (hVf : ∀ b : Bond L, RMapLipschitz.frobNorm ((V b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α₁)
    (hv : ∀ b : Bond L, ‖v b‖ ≤ Kv)
    (hlen : ∀ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1, ∀ i ∈ Finset.range m,
      ∀ x ∈ blockOf u.1 ell₀, ∀ j ∈ Finset.range ell₀,
        (coarseTransportPath ell₀ c.1.1 u.1 c.2 i).length
          + (transportPath (pathSite u.1 c.2 (i * ell₀)) (pathSite x c.2 (i * ell₀)) c.2 j).length
          + (transportPath c.1.1 x c.2 (i * ell₀ + j)).length ≤ N) :
    ‖unitToCoarseCov ell₀ m V (lineCoarseRestrictCovLM U ell₀ v) c
        - lineCoarseRestrictCovLM U (ell₀ * m) v c‖ ≤ (N : ℝ) * (2 * α₁ * Kv) := by
  refine tower_law_cov_error_uniform hell₀ hm hdvd₀ hdvd₁ V U v c _ ?_
  intro u hu i hi x hx j hj
  set Y := v (pathSite x c.2 (i * ell₀ + j), c.2) with hY
  have hstep := towerDefect_norm_le (L := L) (α := 2 * α₁ * ‖Y‖) ell₀ V U Y
    (link_displacement_le U Y hUf) (link_displacement_le V Y hVf)
    c.1.1 u.1 x c.2 i j
  refine le_trans hstep ?_
  have hlen' := hlen u hu i hi x hx j hj
  have hlenR : ((coarseTransportPath ell₀ c.1.1 u.1 c.2 i).length : ℝ)
      + ((transportPath (pathSite u.1 c.2 (i * ell₀)) (pathSite x c.2 (i * ell₀)) c.2 j).length : ℝ)
      + ((transportPath c.1.1 x c.2 (i * ell₀ + j)).length : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hlen'
  have hYK : ‖Y‖ ≤ Kv := hv _
  have hYnn : (0 : ℝ) ≤ ‖Y‖ := norm_nonneg _
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h2a : (0 : ℝ) ≤ 2 * α₁ * ‖Y‖ := by positivity
  calc _ ≤ (N : ℝ) * (2 * α₁ * ‖Y‖) := mul_le_mul_of_nonneg_right hlenR h2a
    _ ≤ (N : ℝ) * (2 * α₁ * Kv) := by
        refine mul_le_mul_of_nonneg_left ?_ hNnn
        nlinarith [hYK, hα₁]

#print axioms link_displacement_le
#print axioms tower_law_cov_error_alpha

/-! ## §6 — THE OBSTRUCTION: `TransportCompose` forces a `V`-FREE identity on `U` -/

/-- Every site is in its own block, once the block has sites. -/
theorem self_mem_blockOf {ell : ℕ} (hell : 0 < ell) (a : PeriodicLatticeSite L) :
    a ∈ blockOf a ell := by
  rw [mem_blockOf]
  intro ρ
  exact ⟨le_refl _, by omega⟩

/-- **THE `V`-FREE CONSEQUENCE.** `TransportCompose` forces the CMP95 (1.7) contour to be ADDITIVE
under block splitting: the contour from the coarse base `y` to a fine site `x` must have the same
holonomy as the contour to `x`'s unit corner `u` followed by the contour from `u` to `x`. The unit
background `V` has been eliminated — it is pinned by the `x = u` instance and then cancelled. -/
theorem transportCompose_forces_contourSplit {ell₀ m : ℕ} (hell₀ : 0 < ell₀) (hm : 0 < m)
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (μ : Fin 3)
    (h : TransportCompose ell₀ m V U y μ)
    (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell₀})
    (hu : u ∈ unitSitesOf ell₀ (ell₀ * m) y)
    (x : PeriodicLatticeSite L) (hx : x ∈ blockOf u.1 ell₀) :
    periodicPathHolonomy U y (GammaPath y u.1) * periodicPathHolonomy U u.1 (GammaPath u.1 x)
      = periodicPathHolonomy U y (GammaPath y x) := by
  have h0m : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.mpr hm
  have h0e : (0 : ℕ) ∈ Finset.range ell₀ := Finset.mem_range.mpr hell₀
  -- the `x = u` instance PINS the unit holonomy
  have hpin := h u hu 0 h0m u.1 (self_mem_blockOf hell₀ u.1) 0 h0e
  have hgen := h u hu 0 h0m x hx 0 h0e
  simp only [lhsTransport, rhsTransport, Nat.zero_mul, Nat.zero_add, pathSite_zero,
    transportPath_zero, GammaPath_self] at hpin hgen
  -- `hpin : H̄ * hol_U(u, []) = hol_U(y, Γ_{y,u})`, i.e. `H̄ = hol_U(y, Γ_{y,u})`
  have hH : coarsePathHolonomy ell₀ V y (coarseTransportPath ell₀ y u.1 μ 0)
      = periodicPathHolonomy U y (GammaPath y u.1) := by
    rw [← hpin]
    show _ = _ * periodicPathHolonomy U u.1 []
    rw [show periodicPathHolonomy U u.1 ([] : List (Fin 3 × Bool)) = 1 from rfl, mul_one]
  rw [← hH]
  exact hgen

#print axioms self_mem_blockOf
#print axioms transportCompose_forces_contourSplit

/-! ### §6a — the contour-split identity FAILS at a curved background

The `V`-free consequence of §6 is a statement about `U` alone. Here it is refuted, in the kernel, on
the torus `witL7` (`L μ = 7`, `8` sites per direction, so BOTH `2 ∣ 8` and `4 ∣ 8`) at the split
`(ℓ₀, ℓ₁) = (2, 4)` — the same torus and split as `ThirdLevelWitness.third_level_nondegeneracy`,
reused rather than re-invented (LAW-19).

**Every base point is INTERIOR.** `y₇ = (4,4,4)` is the far `ℓ₁`-block, not the origin: the
truncation trap (`8 − 0 = 8` does not truncate, so an origin-based block hides `blockOf`'s
truncation) is avoided by construction, and `y₇ + 4 = 8` exactly tiles. -/

/-- A single-link background never traverses a bond: decidable predicate, so every concrete check
below is `decide`-able instead of hand-unfolded. Handles backward steps too (the bond a backward
step uses is based at the STEPPED site). -/
def hitsBond (b₀ : Bond L) : PeriodicLatticeSite L → List (Fin 3 × Bool) → Bool
  | _, [] => false
  | y, st :: rest =>
      decide ((if st.2 then (y, st.1) else (periodicLatticeStep y st, st.1)) = b₀)
        || hitsBond b₀ (periodicLatticeStep y st) rest

/-- **A path that avoids the one nontrivial link has holonomy `1`.** General in `G`, `L`, `b₀`. -/
theorem hol_singleLink_eq_one {G : Type*} [Group G] (b₀ : Bond L) (M : G) :
    ∀ (y : PeriodicLatticeSite L) (s : List (Fin 3 × Bool)), hitsBond b₀ y s = false →
      periodicPathHolonomy (fun e => if e = b₀ then M else 1) y s = 1 := by
  intro y s
  induction s generalizing y with
  | nil => intro _; rfl
  | cons st rest ih =>
    intro h
    rw [hitsBond, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    show (if st.2 then _ else _) * periodicPathHolonomy _ (periodicLatticeStep y st) rest = 1
    rw [ih (periodicLatticeStep y st) h.2, mul_one]
    by_cases hs : st.2 = true
    · rw [hs] at h ⊢
      simp only [if_true] at h ⊢
      exact if_neg h.1
    · have hs' : st.2 = false := by simpa using hs
      rw [hs'] at h ⊢
      simp only [Bool.false_eq_true, if_false] at h ⊢
      rw [if_neg h.1, inv_one]

#print axioms hol_singleLink_eq_one

open AdalyFormal.Balaban.ThirdLevelWitness (witL7 witL7_two_dvd witL7_four_dvd)

/-- `y₇ = (4,4,4)` — the INTERIOR `ℓ₁ = 4` block base (not the origin). -/
def y7 : PeriodicLatticeSite witL7 := fun _ => 4

/-- `u₇ = (4,6,6)` — a unit (`ℓ₀ = 2`) site inside `B₄(y₇)`, with `μ`-coordinate equal to `y₇`'s. -/
def u7 : PeriodicLatticeSite witL7 := fun ρ => if ρ = 0 then 4 else 6

/-- `x₇ = (4,7,7)` — a fine site of `u₇`'s `ℓ₀`-block, again on the lowest `μ = 0` layer. -/
def x7 : PeriodicLatticeSite witL7 := fun ρ => if ρ = 0 then 4 else 7

/-- `(4,4,6)` — the base of the ONE link carrying curvature. It lies on the `Γ_{y₇,x₇}` contour and
on NEITHER `Γ_{y₇,u₇}` nor `Γ_{u₇,x₇}`: that is the whole mechanism. -/
def badSite : PeriodicLatticeSite witL7 := fun ρ => if ρ = 2 then 6 else 4

/-- **The curved background.** `M = !![0,1;-1,0]` on the single link `((4,4,6), 2)`, `1` elsewhere
— `CovariantOperators.witnessMElem`, reused (LAW-19). -/
noncomputable def towerU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL7 :=
  fun e => if e = (badSite, (2 : Fin 3)) then witnessMElem else 1

theorem towerU_on : towerU (badSite, (2 : Fin 3)) = witnessMElem := if_pos rfl

theorem y7_coarse : y7 ∈ CoarseLattice witL7 (2 * 2) := by
  rw [mem_CoarseLattice]; decide

theorem u7_coarse : u7 ∈ CoarseLattice witL7 2 := by
  rw [mem_CoarseLattice]; decide

theorem u7_mem_units :
    (⟨u7, u7_coarse⟩ : {z : PeriodicLatticeSite witL7 // z ∈ CoarseLattice witL7 2})
      ∈ unitSitesOf 2 (2 * 2) y7 := by
  rw [unitSitesOf, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [mem_blockOf]; decide⟩

theorem x7_mem_block : x7 ∈ blockOf u7 2 := by
  rw [mem_blockOf]; decide

/-- One FORWARD step of a holonomy, as a rewrite rule (the definition is stated with `let`s, so
`rw` cannot see through it). -/
theorem hol_cons_fwd {G : Type*} [Group G] (U : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) (rest : List (Fin 3 × Bool)) :
    periodicPathHolonomy U y ((μ, true) :: rest)
      = U (y, μ) * periodicPathHolonomy U (periodicLatticeShift y μ) rest := rfl

/-- `hol_singleLink_eq_one` at `towerU`, in `rw`-usable form (`rw` will not unfold `towerU`). -/
theorem towerU_hol_eq_one (y : PeriodicLatticeSite witL7) (s : List (Fin 3 × Bool))
    (h : hitsBond (badSite, (2 : Fin 3)) y s = false) :
    periodicPathHolonomy towerU y s = 1 :=
  hol_singleLink_eq_one (badSite, (2 : Fin 3)) witnessMElem y s h

/-- `Γ_{y₇,u₇}` avoids the curved link, so its holonomy is `1`. -/
theorem hol_y7_u7 : periodicPathHolonomy towerU y7 (GammaPath y7 u7) = 1 :=
  towerU_hol_eq_one y7 (GammaPath y7 u7) (by decide)

/-- `Γ_{u₇,x₇}` avoids it too. -/
theorem hol_u7_x7 : periodicPathHolonomy towerU u7 (GammaPath u7 x7) = 1 :=
  towerU_hol_eq_one u7 (GammaPath u7 x7) (by decide)

/-- **But `Γ_{y₇,x₇}` DOES traverse it**: split the contour at `badSite`. -/
theorem hol_y7_x7 : periodicPathHolonomy towerU y7 (GammaPath y7 x7) = witnessMElem := by
  have hsplit : GammaPath y7 x7
      = [((2 : Fin 3), true), ((2 : Fin 3), true)]
        ++ (((2 : Fin 3), true) :: [((1 : Fin 3), true), ((1 : Fin 3), true),
             ((1 : Fin 3), true)]) := by decide
  have hend : periodicPathEndpoint y7 [((2 : Fin 3), true), ((2 : Fin 3), true)] = badSite := by
    decide
  rw [hsplit, periodicPathHolonomy_append, hend,
    towerU_hol_eq_one y7 _ (by decide), one_mul, hol_cons_fwd, towerU_on,
    towerU_hol_eq_one _ _ (by decide), mul_one]

/-- `M ≠ 1`: entry `(0,0)` is `0` on one side and `1` on the other. -/
theorem witnessMElem_ne_one :
    witnessMElem ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  intro h
  have h' : (witnessM : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    rw [show (witnessM : Matrix (Fin 2) (Fin 2) ℂ)
      = ((witnessMElem : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) from rfl, h]
    rfl
  simp only [witnessM, Matrix.cons_val', Matrix.cons_val_zero, Matrix.of_apply,
    Matrix.one_apply_eq] at h'
  exact zero_ne_one h'

/-- **THE CONTOUR-SPLIT IDENTITY IS FALSE at `towerU`.** The CMP95 (1.7) contour is NOT additive
under block splitting once the background is curved: going `y₇ → u₇ → x₇` picks up `1`, going
`y₇ → x₇` directly picks up `M`. -/
theorem contourSplit_fails :
    periodicPathHolonomy towerU y7 (GammaPath y7 u7)
        * periodicPathHolonomy towerU u7 (GammaPath u7 x7)
      ≠ periodicPathHolonomy towerU y7 (GammaPath y7 x7) := by
  rw [hol_y7_u7, hol_u7_x7, hol_y7_x7, mul_one]
  exact fun h => witnessMElem_ne_one h.symm

/-! #### Controls for §6a — both directions

The refutation must be about CURVATURE, not about the definitions. Three checks. -/

/-- **MUST-NOT-FIRE (flat).** At `U = 1` the contour-split identity HOLDS, for every `y, u, x` —
so `contourSplit_fails` is not an artefact of the contour construction. This is the
one-parameter mutation: same torus, same split, same sites, only the background moves. -/
theorem contourSplit_holds_at_trivialU (y u x : PeriodicLatticeSite L) :
    periodicPathHolonomy (trivialU L) y (GammaPath y u)
        * periodicPathHolonomy (trivialU L) u (GammaPath u x)
      = periodicPathHolonomy (trivialU L) y (GammaPath y x) := by
  rw [periodicPathHolonomy_trivialU_eq_one, periodicPathHolonomy_trivialU_eq_one,
    periodicPathHolonomy_trivialU_eq_one, mul_one]

/-- **NON-VACUITY of `TransportCompose`.** The predicate is SATISFIED at `U = 1, V = 1`, for every
`ℓ₀, m, y, μ`. So `no_unit_background_transportComposes` is not the refutation of a predicate that
nothing could satisfy (the S91/L7 trap in its `Prop`-valued form). -/
theorem transportCompose_at_trivial (ell₀ m : ℕ) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    TransportCompose ell₀ m (trivialU L) (trivialU L) y μ := by
  intro u _ i _ x _ j _
  simp only [lhsTransport, rhsTransport, coarsePathHolonomy_trivialU,
    periodicPathHolonomy_trivialU_eq_one, one_mul]

/-- **`towerU` IS CURVED — proved, not adjectival.** The `(2,1)` plaquette loop based at the
curved link's own base site has holonomy `M ≠ 1`. (The loop is closed: `endpoint = badSite`.) -/
theorem towerU_curved :
    periodicPathEndpoint badSite
        [((2 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), false), ((1 : Fin 3), false)]
      = badSite
  ∧ periodicPathHolonomy towerU badSite
        [((2 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), false), ((1 : Fin 3), false)]
      ≠ 1 := by
  refine ⟨by decide, ?_⟩
  rw [hol_cons_fwd, towerU_on, towerU_hol_eq_one _ _ (by decide), mul_one]
  exact witnessMElem_ne_one

/-- The `ℓ₁`-block is a PROPER part of the torus (`4 < 8` per direction): the origin is outside it,
so "block = whole torus" is not the degenerate regime the refutation runs in. -/
theorem block_proper : (fun _ => 0 : PeriodicLatticeSite witL7) ∉ blockOf y7 (2 * 2) := by
  rw [mem_blockOf]; decide

#print axioms contourSplit_holds_at_trivialU
#print axioms transportCompose_at_trivial
#print axioms towerU_curved
#print axioms block_proper

/-- **NO UNIT BACKGROUND COMPOSES.** For EVERY unit-level background `V` and every coarse-bond
direction `μ`, `TransportCompose` fails at `towerU`. So `[Q-TRANSPORT-COMPOSE]` in its exact
termwise form is not merely unproved — it is FALSE, and no choice of `Ū` can repair it. -/
theorem no_unit_background_transportComposes
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL7) (μ : Fin 3) :
    ¬ TransportCompose 2 2 V towerU y7 μ := by
  intro h
  exact contourSplit_fails
    (transportCompose_forces_contourSplit (by norm_num) (by norm_num) V towerU y7 μ h
      ⟨u7, u7_coarse⟩ u7_mem_units x7 x7_mem_block)

#print axioms towerU_on
#print axioms y7_coarse
#print axioms u7_coarse
#print axioms u7_mem_units
#print axioms x7_mem_block
#print axioms hol_cons_fwd
#print axioms towerU_hol_eq_one
#print axioms hol_y7_u7
#print axioms hol_u7_x7
#print axioms hol_y7_x7
#print axioms witnessMElem_ne_one
#print axioms contourSplit_fails
#print axioms no_unit_background_transportComposes

/-! ### §6b — THE OPERATOR-LEVEL REFUTATION

§6a kills the TERMWISE route. This kills (TOWER-COV) itself: no unit background `V` makes the
covariant tower law hold as an operator identity at `towerU`. The argument uses only two named
single-bond test fields and never mentions `TransportCompose`.

The mechanism: on the LOWEST `μ = 0` layer of the `ℓ₁`-block, exactly ONE index quadruple
`(u, i, x, j)` of the §4 expansion reaches a given bond, so both sides collapse to a single
transport applied to `suTwoWitness`. The first field PINS `R(V`-holonomy`)` to the identity; the
second then forces `suTwoWitness = −suTwoWitness`. -/

/-- `pathSite`'s own coordinate advances mod the extent. `pathSite x μ k` and `coarseShift x k μ`
are the SAME iterate, so this is `CoarseCurl.coarseShift_val_eq` re-typed (LAW-19, no new
induction). -/
theorem pathSite_val (x : PeriodicLatticeSite L) (μ : Fin 3) (k : ℕ) :
    ((pathSite x μ k) μ).val = ((x μ).val + k) % (L μ + 1) :=
  coarseShift_val_eq x k μ

/-- **The isolation arithmetic.** On the lowest `μ = 0` layer of `B₄(y₇)` the only way a fine bond
of the expansion lands on `x₀` is the zeroth one. `ℕ`-truncation and torus wraparound are both
handled explicitly: `(x₀ 0).val = 4` and `(x 0).val ∈ [4,8)` and `k < 4` give `(x 0).val + k ≤ 10`,
so `(x 0).val + k ≡ 4 (mod 8)` forces `= 4`, not `= 12`. -/
theorem pathSite_hit (x x₀ : PeriodicLatticeSite witL7) (hx : x ∈ blockOf y7 (2 * 2))
    (hx₀ : (x₀ (0 : Fin 3)).val = 4) (k : ℕ) (hk : k < 4)
    (h : pathSite x (0 : Fin 3) k = x₀) : k = 0 ∧ x = x₀ := by
  have hb := mem_blockOf.mp hx (0 : Fin 3)
  have hy0 : (y7 (0 : Fin 3)).val = 4 := rfl
  have hval : ((pathSite x (0 : Fin 3) k) (0 : Fin 3)).val
      = ((x (0 : Fin 3)).val + k) % (witL7 (0 : Fin 3) + 1) := pathSite_val x 0 k
  rw [h, hx₀] at hval
  -- `witL7 0 + 1` is definitionally `8`; retype rather than rewrite (dependent motive)
  have hval8 : 4 = ((x (0 : Fin 3)).val + k) % 8 := hval
  have hlt : (x (0 : Fin 3)).val < 8 := (x (0 : Fin 3)).isLt
  have hk0 : k = 0 := by omega
  subst hk0
  exact ⟨rfl, by rw [← h, pathSite_zero]⟩

/-- The single-bond test field: `suTwoWitness` on one bond, `0` elsewhere. Named data, no
existential (S91). -/
noncomputable def testField (b₀ : Bond witL7) : Bond witL7 → SuTwo :=
  fun b => if b = b₀ then suTwoWitness else 0

set_option maxHeartbeats 2000000 in
/-- Every non-hitting term of the §4 expansion vanishes on a single-bond test field. -/
theorem expansion_term_zero (T : {z : PeriodicLatticeSite witL7 // z ∈ CoarseLattice witL7 2} →
      ℕ → PeriodicLatticeSite witL7 → ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (x₀ : PeriodicLatticeSite witL7) (hx₀ : (x₀ (0 : Fin 3)).val = 4)
    (u : {z : PeriodicLatticeSite witL7 // z ∈ CoarseLattice witL7 2})
    (hu : u ∈ unitSitesOf 2 (2 * 2) y7) (i : ℕ) (hi : i ∈ Finset.range 2)
    (x : PeriodicLatticeSite witL7) (hx : x ∈ blockOf u.1 2) (j : ℕ) (hj : j ∈ Finset.range 2)
    (hne : ¬(i = 0 ∧ j = 0 ∧ x = x₀)) :
    RMap (T u i x j)
      (testField (x₀, (0 : Fin 3)) (pathSite x (0 : Fin 3) (i * 2 + j), (0 : Fin 3))) = 0 := by
  have hxblk : x ∈ blockOf y7 (2 * 2) := by
    rw [blockOf_eq_biUnion_units (L := witL7) (by norm_num) (Dvd.intro 2 rfl) witL7_two_dvd
      y7_coarse]
    exact Finset.mem_biUnion.mpr ⟨u, hu, hx⟩
  have hi2 := Finset.mem_range.mp hi
  have hj2 := Finset.mem_range.mp hj
  have hcond : ¬((pathSite x (0 : Fin 3) (i * 2 + j), (0 : Fin 3)) = (x₀, (0 : Fin 3))) := by
    intro hc
    obtain ⟨hk0, hxx⟩ := pathSite_hit x x₀ hxblk hx₀ (i * 2 + j) (by omega)
      (congrArg Prod.fst hc)
    exact hne ⟨by omega, by omega, hxx⟩
  rw [testField, if_neg hcond, map_zero]

set_option maxHeartbeats 2000000 in
/-- **THE ISOLATION.** On a single-bond test field based at the lowest `μ = 0` layer, the whole
quadruple sum of §4 collapses to ONE term. -/
theorem expansion_isolate
    (T : {z : PeriodicLatticeSite witL7 // z ∈ CoarseLattice witL7 2} →
      ℕ → PeriodicLatticeSite witL7 → ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (x₀ : PeriodicLatticeSite witL7) (hx₀ : (x₀ (0 : Fin 3)).val = 4)
    (u₀ : {z : PeriodicLatticeSite witL7 // z ∈ CoarseLattice witL7 2})
    (hu₀ : u₀ ∈ unitSitesOf 2 (2 * 2) y7) (hx₀m : x₀ ∈ blockOf u₀.1 2) :
    (∑ u ∈ unitSitesOf 2 (2 * 2) y7, ∑ i ∈ Finset.range 2, ∑ x ∈ blockOf u.1 2,
        ∑ j ∈ Finset.range 2,
          RMap (T u i x j)
            (testField (x₀, (0 : Fin 3)) (pathSite x (0 : Fin 3) (i * 2 + j), (0 : Fin 3))))
      = RMap (T u₀ 0 x₀ 0) suTwoWitness := by
  have hzero : ∀ u ∈ unitSitesOf 2 (2 * 2) y7, ∀ i ∈ Finset.range 2, ∀ x ∈ blockOf u.1 2,
      ∀ j ∈ Finset.range 2, ¬(i = 0 ∧ j = 0 ∧ x = x₀) →
      RMap (T u i x j)
        (testField (x₀, (0 : Fin 3)) (pathSite x (0 : Fin 3) (i * 2 + j), (0 : Fin 3))) = 0 :=
    fun u hu i hi x hx j hj hne => expansion_term_zero T x₀ hx₀ u hu i hi x hx j hj hne
  rw [Finset.sum_eq_single_of_mem u₀ hu₀ ?_]
  · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by norm_num)) ?_]
    · rw [Finset.sum_eq_single_of_mem x₀ hx₀m ?_]
      · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by norm_num)) ?_]
        · rw [show (0 : ℕ) * 2 + 0 = 0 from rfl, pathSite_zero, testField, if_pos rfl]
        · intro j hj hjne
          exact hzero u₀ hu₀ 0 (Finset.mem_range.mpr (by norm_num)) x₀ hx₀m j hj
            (fun hc => hjne hc.2.1)
      · intro x hx hxne
        refine Finset.sum_eq_zero fun j hj => ?_
        exact hzero u₀ hu₀ 0 (Finset.mem_range.mpr (by norm_num)) x hx j hj
          (fun hc => hxne hc.2.2)
    · intro i hi hine
      refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun j hj => ?_
      exact hzero u₀ hu₀ i hi x hx j hj (fun hc => hine hc.1)
  · intro u hu hune
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun x hx =>
      Finset.sum_eq_zero fun j hj => ?_
    refine hzero u hu i hi x hx j hj (fun hc => hune ?_)
    -- `x = x₀ ∈ blockOf u.1 2 ∩ blockOf u₀.1 2` forces `u = u₀` (coarse blocks tile)
    have hxu : x₀ ∈ blockOf u.1 2 := hc.2.2 ▸ hx
    exact Subtype.ext (coarseLattice_unique 2 u.2 u₀.2 hxu hx₀m)

/-- **THE CORE OBSTRUCTION, INDEPENDENT OF THE UNIT CONTOUR CHOICE.**

No group element `H` whatsoever can serve as the unit-level transport `c₋ → u₇`. The `x = u₇`
datum forces `R(H)` to fix `suTwoWitness`; the `x = x₇` datum then demands
`suTwoWitness = −suTwoWitness`.

Why this matters for the scope of §6b: both data share the SAME unit index `(u, i) = (u₇, 0)`, so
`H` enters as an opaque group element. The refutation therefore does not depend on which unit-level
contour family, or which unit background `V`, the arrow is built from — only on the fact that the
two-step transport FACTORS as (something depending on the unit datum alone) × (the inner `Q_{ℓ₀}`
transport), which is exactly what "the same one-step averaging template, one level up" means. -/
theorem no_unit_transport_element (H : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (h1 : RMap (H * periodicPathHolonomy towerU u7 (GammaPath u7 u7)) suTwoWitness
        = RMap (periodicPathHolonomy towerU y7 (GammaPath y7 u7)) suTwoWitness)
    (h2 : RMap (H * periodicPathHolonomy towerU u7 (GammaPath u7 x7)) suTwoWitness
        = RMap (periodicPathHolonomy towerU y7 (GammaPath y7 x7)) suTwoWitness) : False := by
  rw [GammaPath_self, show periodicPathHolonomy towerU u7 ([] : List (Fin 3 × Bool)) = 1 from rfl,
    mul_one, hol_y7_u7] at h1
  simp only [RMap_one, LinearMap.id_coe, id_eq] at h1
  rw [hol_u7_x7, mul_one, hol_y7_x7] at h2
  rw [h1, RMap_witnessMElem] at h2
  exact suTwoWitness_ne_neg_self h2

#print axioms no_unit_transport_element

/-- The coarse bond at which the refutation is run: base `y₇`, direction `0`. -/
def towerC : CoarseBond witL7 (2 * 2) := (⟨y7, y7_coarse⟩, (0 : Fin 3))

/-- `x₇` sits on the lowest `μ = 0` layer. -/
theorem x7_layer : (x7 (0 : Fin 3)).val = 4 := rfl

/-- …and so does `u₇`. -/
theorem u7_layer : (u7 (0 : Fin 3)).val = 4 := rfl

theorem u7_mem_self_block : u7 ∈ blockOf u7 2 := self_mem_blockOf (by norm_num) u7

/-- **THE OPERATOR-LEVEL REFUTATION OF `[Q-TRANSPORT-COMPOSE]`.**

For the explicit curved background `towerU` on `witL7`, at the non-degenerate split
`(ℓ₀, ℓ₁) = (2, 4)` and the interior coarse bond `towerC = ((4,4,4), 0)`: **NO** unit-level
background `V` satisfies the covariant tower law. So (TOWER-COV) is not merely unproved — the exact
operator identity is FALSE, whatever `Ū` one constructs. -/
theorem tower_law_cov_refuted
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL7) :
    ¬ (∀ v : Bond witL7 → SuTwo,
        unitToCoarseCov 2 2 V (lineCoarseRestrictCovLM towerU 2 v) towerC
          = lineCoarseRestrictCovLM towerU (2 * 2) v towerC) := by
  intro htow
  have hy : (towerC.1 : PeriodicLatticeSite witL7) = y7 := rfl
  have hμ : towerC.2 = (0 : Fin 3) := rfl
  have hsc : (1 / ((2 : ℝ) * (2 : ℝ)) ^ 4) ≠ 0 := by norm_num
  -- the two collapsed identities, one per test field
  have hcollapse : ∀ (x₀ : PeriodicLatticeSite witL7), (x₀ (0 : Fin 3)).val = 4 →
      ∀ (u₀ : {z : PeriodicLatticeSite witL7 // z ∈ CoarseLattice witL7 2}),
        u₀ ∈ unitSitesOf 2 (2 * 2) y7 → x₀ ∈ blockOf u₀.1 2 →
      RMap (lhsTransport 2 V towerU y7 u₀.1 x₀ (0 : Fin 3) 0 0) suTwoWitness
        = RMap (rhsTransport 2 towerU y7 x₀ (0 : Fin 3) 0 0) suTwoWitness := by
    intro x₀ hx₀ u₀ hu₀ hx₀m
    have h := htow (testField (x₀, (0 : Fin 3)))
    rw [lhs_expand (L := witL7) (by norm_num) witL7_two_dvd V towerU _ towerC,
      rhs_expand (L := witL7) (by norm_num) witL7_two_dvd towerU _ towerC] at h
    rw [hy, hμ] at h
    rw [expansion_isolate (fun u i x j => lhsTransport 2 V towerU y7 u.1 x (0 : Fin 3) i j)
        x₀ hx₀ u₀ hu₀ hx₀m,
      expansion_isolate (fun _ i x j => rhsTransport 2 towerU y7 x (0 : Fin 3) i j)
        x₀ hx₀ u₀ hu₀ hx₀m] at h
    have h2 := congrArg (fun z : SuTwo => (((2 : ℝ) * (2 : ℝ)) ^ 4) • z) h
    simpa [smul_smul, hsc] using h2
  -- the `u₇` field pins the unit-level holonomy to the identity
  have hpin := hcollapse u7 u7_layer ⟨u7, u7_coarse⟩ u7_mem_units u7_mem_self_block
  have hgen := hcollapse x7 x7_layer ⟨u7, u7_coarse⟩ u7_mem_units x7_mem_block
  simp only [lhsTransport, rhsTransport, Nat.zero_mul, Nat.zero_add, pathSite_zero,
    transportPath_zero] at hpin hgen
  exact no_unit_transport_element _ hpin hgen

/-- **AT BAŁABAN'S OWN `Ū`.** `BlockedGauge.blockedGaugeAsConfig P ell U` is CMP109 (0.4)'s blocked
gauge field, typed as a link configuration on the same lattice — the object whose absence made
`[Q-TRANSPORT-COMPOSE]` unstateable. The refutation applies to it for EVERY `LogExpAd P` (including
`SuTwoLogExpCore.su2LogExp`) and every blocking side `ell`, because §6b quantifies over all `V`.

So the covariant tower law is not waiting on a better construction of `Ū`: at a curved background
the exact identity fails for all of them. -/
theorem tower_law_cov_refuted_at_blockedGauge
    {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : BlockedGauge.LogExpAd (Matrix.specialUnitaryGroup (Fin 2) ℂ) 𝔤) (ell : ℕ) :
    ¬ (∀ v : Bond witL7 → SuTwo,
        unitToCoarseCov 2 2 (BlockedGauge.blockedGaugeAsConfig P ell towerU)
            (lineCoarseRestrictCovLM towerU 2 v) towerC
          = lineCoarseRestrictCovLM towerU (2 * 2) v towerC) :=
  tower_law_cov_refuted (BlockedGauge.blockedGaugeAsConfig P ell towerU)

#print axioms pathSite_val
#print axioms pathSite_hit
#print axioms expansion_term_zero
#print axioms expansion_isolate
#print axioms x7_layer
#print axioms u7_layer
#print axioms u7_mem_self_block
#print axioms tower_law_cov_refuted
#print axioms tower_law_cov_refuted_at_blockedGauge

/-! ## §7 — the `LevelSplit` reading: the two block sides that produced this obstruction

`CStarLevelCorrected.LevelSplit` makes `ℓ₀ = ℓ₁` unstateable. The obstruction above lives at the
`LevelSplit` `⟨2, 4, …⟩` — a genuine, non-collapsed split (`ℓ₀ = 2 < 4 = ℓ₁`, `2 ∣ 4`), so it is not
an artefact of a degenerate level identification. Recorded as a term, so the claim is checked rather
than asserted. -/

/-- The split at which §6 refutes the tower law: `(ℓ₀, ℓ₁) = (2, 4)`, `m = 2`. -/
def towerSplit : CStarLevelCorrected.LevelSplit := ⟨2, 4, by norm_num, by norm_num, by norm_num⟩

theorem towerSplit_ne : towerSplit.fibre ≠ towerSplit.constr :=
  CStarLevelCorrected.LevelSplit.ne towerSplit

theorem towerSplit_product : towerSplit.fibre * 2 = towerSplit.constr := rfl

/-- **The degenerate contrast the obstruction is NOT.** At `ℓ₀ = 1` a block is a single site, so
`Γ_{y,u}` and `Γ_{u,x}` degenerate and no splitting question arises; every contrast above uses
`ℓ₀ = 2 ≥ 2`. -/
theorem towerSplit_fibre_ge_two : 2 ≤ towerSplit.fibre := Nat.le_refl 2

/-- **The HONEST-SCOPE arithmetic, asserted rather than narrated.** `CoercivityRegular`'s curved
witness lives on `RegularUDomainWitness.witL5` (`L μ = 5`, six sites per direction), where the
coarse level `ℓ₁ = 4` does NOT tile — so the split `(2,4)` used above is not stateable there and
`curvedRegularU` could not have been the refutation's background. -/
theorem witL5_four_not_dvd :
    ¬ ((4 : ℕ) ∣ (AdalyFormal.Balaban.RegularUDomainWitness.witL5 (0 : Fin 3) + 1)) := by decide

/-- …while `witL7` DOES tile at both levels — the reason the refutation runs there. -/
theorem witL7_both_levels :
    (∀ μ : Fin 3, (2 : ℕ) ∣ (witL7 μ + 1)) ∧ (∀ μ : Fin 3, (2 * 2 : ℕ) ∣ (witL7 μ + 1)) :=
  ⟨witL7_two_dvd, witL7_four_dvd⟩

#print axioms witL5_four_not_dvd
#print axioms witL7_both_levels

#print axioms towerSplit_ne
#print axioms towerSplit_product
#print axioms towerSplit_fibre_ge_two

/-! ## §9 — SECOND-FAMILY PROSECUTION (Sol, 2026-07-28): CONVICTED on the object, and the
    main loop's own catch on the prosecution's central artifact

**Read this before citing anything above.** The status of this module's headline is now
CANNOT-DETERMINE, and it is important to be exact about why, because BOTH the refutation and its
refutation are overstated.

### (a) What Sol's compiled counter-construction actually proves — the main loop's finding

Sol filed `compute/sol_towerlaw/scratch/SourceHierarchicalContour.lean` and reported
`tower_law_cov_holds_hierarchical` as showing *"the covariant tower law HOLDS for the
source-recursive two-level contour"*. **It does not.** The theorem reads

  `unitToCoarseCov ell₀ m V (lineCoarseRestrictCovLM U ell₀ v) c = hierarchicalQ2 … c`

and is closed by `rw [lhs_expand …]; rfl`. Its right-hand side `hierarchicalQ2` is built from
`sourceHierTransport`, whose body the main loop diffed against this file's own `lhsTransport`
(`:311-317`) and found **BYTE-IDENTICAL**. So `hierarchicalQ2` IS the left-hand side's own
expansion under another name, and the theorem asserts `LHS = LHS`. It is a TAUTOLOGY and carries
no information about the tower law, whose content is `LHS = rhsTransport`-side, i.e. the DIRECT
one-shot coarse restriction that `tower_law_cov_refuted` addresses.

This is the `[[claim-is-not-certificate]]` shape again, and the same de-tautologising that was
applied to `RecursiveBridge.fineMapOf_surjective_of_hG1` earlier this campaign: a conclusion
character-identical to its own hypothesis, proved by `rfl`. A compiled, axiom-clean theorem is
not thereby an informative one.

### (b) What SURVIVES Sol's prosecution — and it is serious

The source findings do NOT depend on that Lean file. They rest on page images Sol rendered fresh
(SHA-256s recorded in `compute/sol_towerlaw/SOL_TOWERLAW_PROSECUTION.md`), and they are checkable
independently:

1. **CMP98 printed pp.29-30** define the higher-order contour variable RECURSIVELY through the
   intermediate block corners:
   `U₀(Γ^(j)_{x_j,x}) = Ū₀^{j-1}(Γ_{x_j,x_{j-1}})·…·Ū₀(Γ_{x_2,x_1})·U₀(Γ_{x_1,x})`.
   **CMP99b p.393 (3.15) defines `Q_j(U)` as the COMPOSITION of the one-step operators**, and its
   (3.19) writes the result with that higher-order `Γ^(j)` — not with a fresh one-shot staircase
   at side `L^j`. CMP99b p.401 (3.55) expands the same way.
2. **CMP98 (124) has FIVE terms**; `unitToCoarseCov`/`lineCoarseRestrictCov` implement only the
   first, which CMP98 (125) separates and names `Q₀`. `Q1Real.lean` says so about itself. This
   module nevertheless bills the map as the `Q(V)` factor of (3.15).
3. **`towerU` is order-one curved**, while CMP98 p.36's linearization of `Q(V)` is explicitly a
   small-field statement. The witness may sit outside the regime where the source's object is
   even defined. (Sol's item 5: QUALIFIED.)

### (b2) SETTLED, 2026-07-28 — third-family source adjudication: THE TOWER LAW IS A DEFINITION

A third family (Kimi), blind to both prior verdicts, read the page images directly and ruled
**DEFINITIONAL**:

* **CMP99b p.393 (3.15) defines `Q_j(U)` as the composition, with NO PROOF VERB** — a bare
  definition, not a derived identity.
* The ONLY one-shot large-block formula anywhere on the four pages examined is **(3.19)**, and it
  applies only to the **PRIMED** operator `Q'_j`.
* (3.19)'s own kernel is **itself defined** by the same corner-by-corner product — CMP98 p.29's
  *"Let us denote…"*.

So there is **no independently-defined one-shot object** in the source to compare the composite
against. The "tower law" is definitional representation, not a substantive theorem, and **a
definition cannot be refuted**. Two families (Sol, Kimi) reached this independently from the same
pages; the term count of CMP98 (124) at FIVE was also re-counted independently and confirmed.

**What this means for `tower_law_cov_refuted`.** The theorem is CORRECT and its proof is sound —
but the identity it refutes is between the two-step composite and a ONE-SHOT large-block average
that is **OUR construction, not Bałaban's**. It refutes a claim the source never makes. The
mathematics stands; the target was ours.

**Consequence for the `k` half, and it is a redirection rather than a closure.** Coercivity cannot
be transferred across scales by proving an identity, because there is no identity to prove — the
coarse operator IS the composite by definition. The bound must be established **for the composite
directly**, which is what `tower_law_cov_error_alpha` starts on and what `k`-uniformity of that
error would finish. Everything above about `α₁^unit ~ ell₀·α₁^fine` and the growth of `N` is
therefore the live question, not a fallback.

**O1 — CLOSED, 2026-07-29, DEFINITION-RECURSIVE.** A second family chased the primary definition.
The `Γ^(j)` construction is **recursive through intermediate block corners**, so the definitional
ruling extends to the **primed** operator too and nothing is owed as a deferred claim. CMP98
printed p.29, read from the page image and re-verified by the main loop:

> *"Let us denote `U₀(Γ^(j)_{x_j,x}) = Ū₀^{j−1}(Γ_{x_j,x_{j−1}})⋯Ū₀(Γ_{x_2,x_1})U₀(Γ_{x_1,x})`,
> then …"*

A bare `Let us denote` — no proof verb, no forward reference. CMP98 p.30 (77) continues it and
says *"the symbol … is defined by the last equation"*. CMP99b p.401 makes the corner chain
explicit: *"where the sequence of points `y = x_j, …, x_1, x = x_0` is defined by the conditions
`x_l ∈ B(x_{l+1})`"*. No competing direct large-scale formula for `Γ^(j)` exists on those pages.

**BUT IT CLOSED BY AN UNEXPECTED ROUTE, AND THAT ROUTE IS ITSELF A FINDING — A CITATION DEFECT IN
THE SOURCE.** CMP99b p.393 states *"The contours `Γ^(j)_{y,x}` … were defined by (52), (53) in
[5]"*, and p.401 repeats *"By the definitions (52), (53) in [5]"*. **Those labels are wrong
against the PUBLISHED CMP98.** Printed p.26's (52) is
`|U(∂p) − 1| < α₀η², η = L^{−k}` — introduced by *"we have to assume that"* and followed by *"on
some set of plaquettes"* — a plaquette-smallness ASSUMPTION; (53) is the matching inductive
plaquette bound, closed in place (*"Thus the inequality (53) is proved for all j ≦ k"*). **Neither
display contains a `Γ`, a contour, or any path construction.** The main loop opened the p.26 crop
and confirmed this directly, not by transcription.

Not a blanket renumbering: CMP99b p.433 cites *"(61), (78)–(80) in [5]"* and those DO match
published CMP98 (pp.28, 30). The origin of the two wrong numbers is **unverified** — CMP99b's
bibliography gives [5] as *"Harvard preprint HUTMP B147, to be published in CMP"*, and that
preprint is not in our corpus, so whether this is a typo or a preprint-to-publication artifact
cannot be settled here. It is recorded as unresolved rather than explained away.

**Why this matters operationally:** anyone following CMP99b's own locator into published CMP98 —
as this campaign was about to — lands on a plaquette bound and finds no contour definition there.
That is a live trap for any future lane, and it is Bałaban's, not ours. `[[render-the-page-nobody-
rendered]]` again: the finding required opening a page no one had opened.

### (c) THE ACTUAL POSITION, stated carefully

If Bałaban DEFINES `Q_j(U)` as the composition, then the "tower law" is definitional for him and
was never a theorem to refute — and the mathematical content moves to a different question:
**does that recursive composite equal the direct block average at scale `ell₀·m`?** That question
is exactly what `contourSplit_fails` answers negatively for curved `U`, so this module's
MECHANISM survives even though its BILLING may not.

So the honest reading of `tower_law_cov_refuted` is: it refutes an identity between the two-step
composite and a ONE-SHOT large-block average. ~~Whether our tree, rather than the source, is the
origin of the claim that those coincide is **NOT YET SETTLED** and is the live question.~~

**SETTLED 2026-07-29 — THE CLAIM IS OURS.** The primary definition was read from the page images:
CMP98 p.29, an **unnumbered display between (76) and (77)**, gives
`U₀(Γ^{(j)}_{x_j,x}) = Ū₀^{j-1}(Γ_{x_j,x_{j-1}})·…·Ū₀(Γ_{x_2,x_1}) U₀(Γ_{x_1,x})` — an ordered
product with one factor per RG level, the level-`l` factor a holonomy of the `l`-times-blocked field
on **its own** lattice; CMP99b p.401 (3.55) pins the chain by `x_l ∈ B(x_{l+1})`. Bałaban's one-shot
form therefore transports by `U(Γ^{(j)})`, **the composite's own transport** — the shape of
`lhsTransport` — and never by `rhsTransport`'s single-field fine holonomy. There is no
independently-defined one-shot object in the source to disagree with.

Consequence: `tower_law_cov_refuted` is **correct mathematics about an object this tree
constructed**, not a refutation of anything Bałaban asserts. Every proof gate passed it — 61
theorems, 0 `sorry`, 61/61 axiom-clean — and none could have caught this, because the defect was
never in a proof. It took reading the page. The formalization of the source's actual object at
arbitrary `j` is `Balaban/Cmp98GammaPrimary.lean`, whose `lhsTransport_eq_gammaVarOf` proves this
module's own `lhs_expand` IS CMP99b (3.19) at `j = 2`.

**What must not be concluded from any of this:** not "the tower law is false" (the object is in
doubt), and not "the tower law holds" (the only artifact offering that is a tautology). The
`k`-uniformity question is untouched by all of it — the error-carrying form
`tower_law_cov_error_alpha` remains the surviving target either way, and remains not proved
uniform. -/

end AdalyFormal.Balaban.TowerLawCov
