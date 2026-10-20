/-
Copyright (c) 2026 Project Adaly. All rights reserved.
-/
import AdalyFormal.Balaban.CoarseCurlScaleTwo
import AdalyFormal.Balaban.CStarDeltaKCOperator
import AdalyFormal.Balaban.NonDegenerateInstances
import AdalyFormal.Balaban.BondSU2Space
import AdalyFormal.Balaban.AnchoredVFull

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `IslandBridge` — connecting lemmas for the unreachable-module cluster

This module exists to make island content CONSUMABLE. It states nothing new about Bałaban; every
theorem here either (a) CHAINS already-proved island theorems into one statement on one carrier, or
(b) settles a named carrier blocker of `GOAL_LEMMA.md` §7 item 1 as mechanical or as a proved
obstruction.

**Facts, not verdicts.**

* §1 chains `CoarseCurlPoincare.coarseCurlPoincare_scaled_ell0_one` into
  `CoarseCurlCovariant.summedTransferCov_ell1`. Measured: they compose by `le_trans` with no
  adapter, at `U = trivialU L`.
* §2 carries the composite onto `BondFnL2 L` — a carrier that DOES have an `InnerProductSpace ℝ`
  instance — and onto the OPERATOR `CStarDeltaKCOperator.dstarDLM`, producing a statement of
  literally the shape `Balaban.CoercivityHypothesis.coercive` demands:
  `γ * ‖v‖ ^ 2 ≤ inner ℝ v (Δ v)`. This settles blockers 2 and 3 of §7 item 1 FOR THIS OBJECT:
  both were already solved in-tree (`BondSU2Space`, `CStarDeltaKCOperator`) and merely never
  applied to the island content.
* §3 builds the su(2)→scalar carrier map `ι` and its explicit adjoint, and proves that a coercivity
  bound on `BondFnL2 L` DESCENDS to `EuclideanSpace ℝ (Bond L)` — `Spine.coerc_u_main`'s own
  carrier. What descends is the restriction of the su(2) statement to one su(2) direction; that is
  stated in the theorem, not hidden.
* §4 turns `CStarDeltaKCOperator`'s docstring assertion "*they are not isomorphic (different finite
  dimensions whenever `Bond` is nonempty)*" into a THEOREM. There was no declaration for it. This
  is the sense in which blocker 1 is NOT mechanical: no `≃ₗ[ℝ]` exists, so nothing can be
  transported along one; §3's one-way descent is what is available instead.
-/

namespace AdalyFormal.Balaban.IslandBridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.CoarseCurlCovariant
open AdalyFormal.Balaban.CoarseCurlPoincare
open AdalyFormal.Balaban.RegularUGamma0
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDLM inner_dstarDLM_eq_dstarDQuadForm)
open AdalyFormal.Balaban.BondSU2Space (inner_bondFnL2_eq_covBondInner)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — BRIDGE 1: the two proved base cases CHAIN, unconditionally

`CoarseCurlPoincare.coarseCurlPoincare_scaled_ell0_one` (every `m ≥ 2`, constant `1/(56 m⁵)`) and
`CoarseCurlCovariant.summedTransferCov_ell1` (every `U`, an equality) are stated over the SAME
middle object, `coarseCurlEnergyCov hdvd1 (coarseBackground U 1) (lineCoarseRestrictCovLM U 1 B)`.

This is deliberately NOT routed through `gamma0AtScale_of_two_primitives`: that reduction's second
antecedent (`CoarseCurlPoincareAtScale m`) is refuted in `CoarseCurlScaleTwo`, so a consumer built
through it would be vacuous. -/

/-- **BRIDGE 1.** For every torus `L`, every coarsening `m ≥ 2` with `m ∣ L ν + 1` and
`m < L ν + 1`, every level list, and every axial-gauge field `B` in `ker Q_m`:

`(1/(56 m⁵)) · ⟪Q₁B, Q₁B⟫ ≤ deltaJQuadFormCovFaithful 1 levels (trivialU L) B`. -/
theorem gamma0_ell0_one_trivialU {m : ℕ} (hm : 2 ≤ m)
    (hstrict : ∀ ν : Fin 3, m < L ν + 1) (hdvdm : ∀ ν : Fin 3, m ∣ (L ν + 1))
    (hdvd1 : ∀ ν : Fin 3, (1 : ℕ) ∣ (L ν + 1))
    (levels : List (KernelSubspace.Level L))
    [(CovariantHjMinimizer.deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels (trivialU L)).HasOrthogonalProjection]
    (B : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L m →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y m → ∀ b ∈ staircasePath y x, B b = 0)
    (hker : ∀ c : CoarseBond L m, lineCoarseRestrictCov (trivialU L) m B c = 0) :
    ((1 : ℝ) / 56 / (m : ℝ) ^ 5)
        * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) 1 B)
          (lineCoarseRestrictCovLM (trivialU L) 1 B)
      ≤ deltaJQuadFormCovFaithful 1 levels (trivialU L) B := by
  refine le_trans
    (coarseCurlPoincare_scaled_ell0_one hm hstrict hdvdm hdvd1 B hadm hker) ?_
  simpa using summedTransferCov_ell1 (trivialU L) hdvd1 levels B

/-! ## §2 — BRIDGE 2: onto `BondFnL2 L` and onto the OPERATOR `dstarDLM`

Every ingredient is in-tree and was never applied to the island content:
* `BondSU2Space.inner_bondFnL2_eq_covBondInner` — `BondFnL2 L`'s inner product IS `covBondInner`;
* `RegularUDirectCoercivity.covBondInner_eq_bondEnergy` — `covBondInner A A = bondEnergy A`;
* `RegularUGamma0.covCoarseBondInner_one_eq_bondEnergy` — `Q₁` is an isometry, every `U`;
* `CovariantHjFaithful.deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm` — at `ell₀ = 1` the
  Schur projection is a no-op and the faithful form IS `dstarDQuadForm`;
* `CStarDeltaKCOperator.inner_dstarDLM_eq_dstarDQuadForm` — `dstarDLM U` is a genuine
  `BondFnL2 L →ₗ[ℝ] BondFnL2 L` whose quadratic form is `dstarDQuadForm U`. -/

/-- `‖·‖²` on `BondFnL2 L` IS `bondEnergy`. -/
theorem norm_sq_bondFnL2 (A : Bond L → SuTwo) :
    ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 = bondEnergy A := by
  rw [← real_inner_self_eq_norm_sq, inner_bondFnL2_eq_covBondInner,
    AdalyFormal.Balaban.RegularUDirectCoercivity.covBondInner_eq_bondEnergy]

/-- **BRIDGE 2 — `Spine`'s `coercive` SHAPE, at the su(2) L² carrier, with a real operator.**

`γ * ‖v‖ ^ 2 ≤ inner ℝ v (Δ v)` with `γ = 1/(56 m⁵)`, `Δ = dstarDLM (trivialU L)`,
`v = WithLp.toLp 2 B`, for every `B` in the axial gauge with `Q_m B = 0`.

Scope, stated in the binders and not hidden: `U = trivialU L`; `ell₀ = 1`; `γ` carries `m⁻⁵`, so
this is NOT the `k`-uniform lemma. `dstarDLM` is `D_U^*D_U`, which is RG-scale-CONSTANT
(`CStarDeltaKCOperator`'s own disclosure); no `k`-dependence is claimed. -/
theorem coercive_shape_bondFnL2 {m : ℕ} (hm : 2 ≤ m)
    (hstrict : ∀ ν : Fin 3, m < L ν + 1) (hdvdm : ∀ ν : Fin 3, m ∣ (L ν + 1))
    (hdvd1 : ∀ ν : Fin 3, (1 : ℕ) ∣ (L ν + 1))
    (levels : List (KernelSubspace.Level L))
    [(CovariantHjMinimizer.deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels (trivialU L)).HasOrthogonalProjection]
    (B : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L m →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y m → ∀ b ∈ staircasePath y x, B b = 0)
    (hker : ∀ c : CoarseBond L m, lineCoarseRestrictCov (trivialU L) m B c = 0) :
    ((1 : ℝ) / 56 / (m : ℝ) ^ 5) * ‖(WithLp.toLp 2 B : BondFnL2 L)‖ ^ 2
      ≤ (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
          (dstarDLM (trivialU L) (WithLp.toLp 2 B)) : ℝ) := by
  have h := gamma0_ell0_one_trivialU hm hstrict hdvdm hdvd1 levels B hadm hker
  rw [covCoarseBondInner_one_eq_bondEnergy,
    deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm] at h
  rw [norm_sq_bondFnL2, inner_dstarDLM_eq_dstarDQuadForm]
  exact h

/-! ## §3 — BRIDGE 3: the one-way descent to `Spine`'s scalar carrier

`Spine.coerc_u_main` lives on `Balaban.Coercivity.AnchoredBondSpace Lat = EuclideanSpace ℝ (Bond
Lat)`. §4 proves no `≃ₗ[ℝ]` to `BondFnL2` exists. What DOES exist is an isometric embedding
`ι : EuclideanSpace ℝ (Bond L) → BondFnL2 L`, `v ↦ (b ↦ v b · E₃)`, along one su(2) direction, and
its explicit adjoint. A LOWER bound restricts along an isometry, so coercivity descends.

**What descends is the restriction to the `E₃` direction** — the abelian sector. That is a strictly
weaker statement than the su(2) one and is written into the theorem name and statement. -/

/-- `ι : EuclideanSpace ℝ (Bond L) →ₗ[ℝ] BondFnL2 L`, the `E₃`-direction embedding. -/
noncomputable def euclidToBondE3 (L : PeriodicLatticeExtent) :
    EuclideanSpace ℝ (Bond L) →ₗ[ℝ] BondFnL2 L where
  toFun v := WithLp.toLp 2 (fun b : Bond L => (WithLp.ofLp v b) • pauliE3)
  map_add' u v := by
    apply (WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)).injective
    funext b
    simp [add_smul]
  map_smul' c v := by
    apply (WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)).injective
    funext b
    simp [mul_smul]

/-- `ι*`, written out: `W ↦ (b ↦ ⟪E₃, W b⟫)`. No `LinearMap.adjoint` and hence no instance
shadowing (`CStarDeltaKCOperator` §0a's `letI` is not needed). -/
noncomputable def bondE3ToEuclid (L : PeriodicLatticeExtent) :
    BondFnL2 L →ₗ[ℝ] EuclideanSpace ℝ (Bond L) where
  toFun W := WithLp.toLp 2 (fun b : Bond L => (inner ℝ pauliE3 (WithLp.ofLp W b) : ℝ))
  map_add' U V := by
    apply (WithLp.linearEquiv 2 ℝ (Bond L → ℝ)).injective
    funext b
    show (inner ℝ pauliE3 (WithLp.ofLp U b + WithLp.ofLp V b) : ℝ)
      = (inner ℝ pauliE3 (WithLp.ofLp U b) : ℝ) + (inner ℝ pauliE3 (WithLp.ofLp V b) : ℝ)
    rw [inner_add_right]
  map_smul' c W := by
    apply (WithLp.linearEquiv 2 ℝ (Bond L → ℝ)).injective
    funext b
    show (inner ℝ pauliE3 (c • WithLp.ofLp W b) : ℝ)
      = c * (inner ℝ pauliE3 (WithLp.ofLp W b) : ℝ)
    rw [real_inner_smul_right]

/-- **The adjoint identity**, proved by direct computation. -/
theorem inner_bondE3ToEuclid (v : EuclideanSpace ℝ (Bond L)) (W : BondFnL2 L) :
    (inner ℝ v (bondE3ToEuclid L W) : ℝ) = inner ℝ (euclidToBondE3 L v) W := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hL : ((bondE3ToEuclid L W).ofLp b) = (inner ℝ pauliE3 (WithLp.ofLp W b) : ℝ) := rfl
  have hR : ((euclidToBondE3 L v).ofLp b) = (WithLp.ofLp v b) • pauliE3 := rfl
  rw [hL, hR, real_inner_smul_left]
  simp [mul_comm]

/-- `ι` is an isometry: `‖ι v‖ = ‖v‖`, because `‖E₃‖ = 1`. -/
theorem inner_euclidToBondE3_self (v : EuclideanSpace ℝ (Bond L)) :
    (inner ℝ (euclidToBondE3 L v) (euclidToBondE3 L v) : ℝ) = inner ℝ v v := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hR : ((euclidToBondE3 L v).ofLp b) = (WithLp.ofLp v b) • pauliE3 := rfl
  rw [hR, real_inner_smul_left, real_inner_smul_right, inner_eq_hsInner, hsInner_e3_e3]
  simp
  ring

theorem norm_euclidToBondE3 (v : EuclideanSpace ℝ (Bond L)) :
    ‖euclidToBondE3 L v‖ = ‖v‖ := by
  have h := inner_euclidToBondE3_self (L := L) v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have h1 : (0 : ℝ) ≤ ‖euclidToBondE3 L v‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  nlinarith [h, h1, h2]

/-- **The pullback operator on `Spine`'s carrier**: `ι* ∘ T ∘ ι`. -/
noncomputable def euclidPullback (T : BondFnL2 L →ₗ[ℝ] BondFnL2 L) :
    EuclideanSpace ℝ (Bond L) →ₗ[ℝ] EuclideanSpace ℝ (Bond L) :=
  (bondE3ToEuclid L) ∘ₗ T ∘ₗ (euclidToBondE3 L)

theorem inner_euclidPullback (T : BondFnL2 L →ₗ[ℝ] BondFnL2 L)
    (v w : EuclideanSpace ℝ (Bond L)) :
    (inner ℝ v (euclidPullback T w) : ℝ)
      = inner ℝ (euclidToBondE3 L v) (T (euclidToBondE3 L w)) := by
  show (inner ℝ v (bondE3ToEuclid L (T (euclidToBondE3 L w))) : ℝ) = _
  rw [inner_bondE3ToEuclid]

/-- **BRIDGE 3 — a coercivity bound on `BondFnL2 L` DESCENDS to `EuclideanSpace ℝ (Bond L)`**,
`Spine.coerc_u_main`'s carrier, for the pullback operator. Note the hypothesis is the bound at the
EMBEDDED point only, so this is the honest one-way transport. -/
theorem coercive_descends (T : BondFnL2 L →ₗ[ℝ] BondFnL2 L) (γ : ℝ)
    (v : EuclideanSpace ℝ (Bond L))
    (h : γ * ‖euclidToBondE3 L v‖ ^ 2 ≤ (inner ℝ (euclidToBondE3 L v)
      (T (euclidToBondE3 L v)) : ℝ)) :
    γ * ‖v‖ ^ 2 ≤ (inner ℝ v (euclidPullback T v) : ℝ) := by
  rw [inner_euclidPullback, ← norm_euclidToBondE3 (L := L) v]
  exact h

/-- **BRIDGE 4 — the composite, on `Spine.coerc_u_main`'s OWN carrier.**

`γ * ‖v‖ ^ 2 ≤ inner ℝ v (Δ v)` with `γ = 1/(56 m⁵)`, `Δ = euclidPullback (dstarDLM (trivialU L))`,
`v : EuclideanSpace ℝ (Bond L)` — the carrier `Spine.coerc_u_main`'s `H` actually is.

The admissibility hypotheses are carried on the EMBEDDED su(2) field `b ↦ v b · E₃`, which is what
they constrain; nothing is assumed about `v` beyond them. This is the abelian (`E₃`-direction)
restriction of §2's su(2) statement — §4 proves no `≃ₗ[ℝ]` exists that could carry more. -/
theorem coercive_shape_euclid {m : ℕ} (hm : 2 ≤ m)
    (hstrict : ∀ ν : Fin 3, m < L ν + 1) (hdvdm : ∀ ν : Fin 3, m ∣ (L ν + 1))
    (hdvd1 : ∀ ν : Fin 3, (1 : ℕ) ∣ (L ν + 1))
    (levels : List (KernelSubspace.Level L))
    [(CovariantHjMinimizer.deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels (trivialU L)).HasOrthogonalProjection]
    (v : EuclideanSpace ℝ (Bond L))
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L m →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y m →
      ∀ b ∈ staircasePath y x, (WithLp.ofLp v b) • pauliE3 = (0 : SuTwo))
    (hker : ∀ c : CoarseBond L m,
      lineCoarseRestrictCov (trivialU L) m (fun b => (WithLp.ofLp v b) • pauliE3) c = 0) :
    ((1 : ℝ) / 56 / (m : ℝ) ^ 5) * ‖v‖ ^ 2
      ≤ (inner ℝ v (euclidPullback (dstarDLM (trivialU L)) v) : ℝ) := by
  refine coercive_descends _ _ v ?_
  exact coercive_shape_bondFnL2 hm hstrict hdvdm hdvd1 levels
    (fun b => (WithLp.ofLp v b) • pauliE3) hadm hker

/-- **§3 CONTROL — the adjoint identity relates NONZERO numbers, at a computed point.**
Both sides of `inner_bondE3ToEuclid` evaluate to `192 = card (Bond witnessL)` at
`v = 1`, `W = E₃`. Without this the identity could be the true-but-empty `0 = 0`.
The numeral comes from `NonDegenerateInstances.card_bond`. -/
theorem inner_bondE3ToEuclid_value_at_one :
    (inner ℝ (WithLp.toLp 2 (fun _ : Bond AdmissibleSubspace.witnessL => (1 : ℝ)) :
        EuclideanSpace ℝ (Bond AdmissibleSubspace.witnessL))
      (bondE3ToEuclid AdmissibleSubspace.witnessL
        (WithLp.toLp 2 (fun _ : Bond AdmissibleSubspace.witnessL => pauliE3))) : ℝ) = 192 := by
  rw [PiLp.inner_apply]
  have hterm : ∀ b : Bond AdmissibleSubspace.witnessL,
      (inner ℝ
        (WithLp.ofLp (WithLp.toLp 2 (fun _ : Bond AdmissibleSubspace.witnessL => (1 : ℝ)) :
          EuclideanSpace ℝ (Bond AdmissibleSubspace.witnessL)) b)
        (WithLp.ofLp (bondE3ToEuclid AdmissibleSubspace.witnessL
          (WithLp.toLp 2 (fun _ : Bond AdmissibleSubspace.witnessL => pauliE3))) b) : ℝ)
      = 1 := by
    intro b
    show (inner ℝ (1 : ℝ) (inner ℝ pauliE3 pauliE3 : ℝ) : ℝ) = 1
    rw [inner_eq_hsInner, hsInner_e3_e3]
    simp
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hterm b), Finset.sum_const,
    Finset.card_univ, NonDegenerateInstances.card_bond]
  norm_num

/-! ## §3a — NON-VACUITY: both bridges fire at a NONZERO field

A coercivity bound whose hypothesis set contains only `0` proves nothing. Both witnesses below are
in-tree objects, reused (LAW-19), not rebuilt. -/

/-- **BRIDGE 2 is NOT vacuous.** At `m = 2` and `U = 1`, `RegularUDomainWitnessGeneralU.genWitness`
is axial at level `2`, lies in `ker Q₂`, and has strictly positive bond energy — so both sides of
BRIDGE 2 are strictly positive. `hstrict` is discharged from `4 ≤ L μ`, not assumed. -/
theorem coercive_shape_bondFnL2_nondegenerate (hL : ∀ μ : Fin 3, 4 ≤ L μ)
    (hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    [(CovariantHjMinimizer.deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels (trivialU L)).HasOrthogonalProjection] :
    0 < ‖(WithLp.toLp 2 (RegularUDomainWitnessGeneralU.genWitness (trivialU L)) :
            BondFnL2 L)‖ ^ 2 ∧
      ((1 : ℝ) / 56 / (2 : ℝ) ^ 5)
          * ‖(WithLp.toLp 2 (RegularUDomainWitnessGeneralU.genWitness (trivialU L)) :
              BondFnL2 L)‖ ^ 2
        ≤ (inner ℝ (WithLp.toLp 2 (RegularUDomainWitnessGeneralU.genWitness (trivialU L)) :
              BondFnL2 L)
            (dstarDLM (trivialU L)
              (WithLp.toLp 2 (RegularUDomainWitnessGeneralU.genWitness (trivialU L)))) : ℝ) := by
  have hstrict : ∀ ν : Fin 3, 2 < L ν + 1 := fun ν => by have := hL ν; omega
  have hpos : 0 < bondEnergy (RegularUDomainWitnessGeneralU.genWitness (trivialU L)) :=
    RegularUDomainWitnessGeneralU.bondEnergy_genWitness_pos hdvd2 (trivialU L)
  refine ⟨by rw [norm_sq_bondFnL2]; exact hpos, ?_⟩
  have h := coercive_shape_bondFnL2 (m := 2) le_rfl hstrict hdvd2 (fun _ => one_dvd _) levels
    (RegularUDomainWitnessGeneralU.genWitness (trivialU L))
    (RegularUDomainWitnessGeneralU.genWitness_axial hdvd2 (trivialU L))
    (RegularUDomainWitnessGeneralU.genWitness_mem_kerQ hdvd2 (trivialU L))
  simpa using h

/-- **BRIDGE 4 is NOT vacuous.** `AnchoredVFull.wConfig m` is a NONZERO SCALAR field that is axial
and lies in `ker Q_m` (the scalar `lineCoarseRestrict`); its `E₃`-lift is therefore admissible for
the covariant `Q_m` at `U = 1` by `LineIntegralCovariant.lineCoarseRestrictSuTwo_smul_fixed`. So
BRIDGE 4's hypothesis set contains a nonzero vector on `Spine`'s own carrier. -/
theorem coercive_shape_euclid_nondegenerate {m : ℕ} (hm : 2 ≤ m)
    (hstrict : ∀ ν : Fin 3, m < L ν + 1) (hdvdm : ∀ ν : Fin 3, m ∣ (L ν + 1))
    (levels : List (KernelSubspace.Level L))
    [(CovariantHjMinimizer.deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels (trivialU L)).HasOrthogonalProjection] :
    0 < ‖(WithLp.toLp 2 (AnchoredVFull.wConfig (L := L) m) :
            EuclideanSpace ℝ (Bond L))‖ ^ 2 ∧
      ((1 : ℝ) / 56 / (m : ℝ) ^ 5)
          * ‖(WithLp.toLp 2 (AnchoredVFull.wConfig (L := L) m) :
              EuclideanSpace ℝ (Bond L))‖ ^ 2
        ≤ (inner ℝ (WithLp.toLp 2 (AnchoredVFull.wConfig (L := L) m) :
              EuclideanSpace ℝ (Bond L))
            (euclidPullback (dstarDLM (trivialU L))
              (WithLp.toLp 2 (AnchoredVFull.wConfig (L := L) m))) : ℝ) := by
  have hax : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L m →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y m →
      ∀ b ∈ staircasePath y x, AnchoredVFull.wConfig (L := L) m b = 0 :=
    mem_admissibleSubspaceInter.mp (AnchoredVFull.wConfig_mem_admissibleSubspaceInter m)
  have hq : ∀ c : CoarseBond L m,
      AdalyFormal.Balaban.LineIntegralAveraging.lineCoarseRestrict m
        (AnchoredVFull.wConfig (L := L) m) c = 0 :=
    AnchoredVFull.mem_kerQOne.mp (AnchoredVFull.wConfig_mem_kerQOne (hdvdm 2))
  have hne : (WithLp.toLp 2 (AnchoredVFull.wConfig (L := L) m) :
      EuclideanSpace ℝ (Bond L)) ≠ 0 := by
    intro h
    exact AnchoredVFull.wConfig_ne_zero hm (hdvdm 0) (hdvdm 2) (by simpa using congrArg WithLp.ofLp h)
  refine ⟨by positivity, ?_⟩
  refine coercive_shape_euclid hm hstrict hdvdm (fun _ => one_dvd _) levels _ ?_ ?_
  · intro y hy x hx b hb
    rw [show (WithLp.ofLp (WithLp.toLp 2 (AnchoredVFull.wConfig (L := L) m) :
      EuclideanSpace ℝ (Bond L)) b) = AnchoredVFull.wConfig (L := L) m b from rfl,
      hax y hy x hx b hb, zero_smul]
  · intro c
    rw [show (fun b => (WithLp.ofLp (WithLp.toLp 2 (AnchoredVFull.wConfig (L := L) m) :
        EuclideanSpace ℝ (Bond L)) b) • pauliE3)
      = (fun b => AnchoredVFull.wConfig (L := L) m b • pauliE3) from rfl,
      lineCoarseRestrictCov_trivialU, lineCoarseRestrictSuTwo_smul_fixed, hq c, zero_smul]

/-! ## §3b — HOW FAR BRIDGE 2's CONSTANT CAN BE PUSHED: `m⁻¹` is refuted

`CoarseCurlScaleTwo.not_coarseCurlPoincareFibreOne_one` refutes the `r = 1` fibre form of the
coarse-curl Poincaré. Because `CoarseCurlCovariant.coarseCurlEnergyCov_one_eq_deltaJ` is an
EQUALITY (not merely the `≤` of `summedTransferCov_ell1`), that refutation transports verbatim onto
the FAITHFUL Schur form this lane's bridges are stated over. So BRIDGE 2's `m⁻⁵` is not a lazily
chosen constant: no `m⁻¹` version of it exists. -/

/-- **BRIDGE 2's constant cannot be linear in `1/m`.** No `γ > 0` makes
`(γ/m)·⟪Q₁B,Q₁B⟫ ≤ deltaJQuadFormCovFaithful 1 [] U B` hold over the axial `∩ ker Q_m` domain
uniformly. Transported from `CoarseCurlScaleTwo`'s sawtooth witness through the `ell₀ = 1`
EQUALITY. -/
theorem no_linear_m_constant_for_deltaJ :
    ¬ ∃ γ : ℝ, 0 < γ ∧
      ∀ (L : PeriodicLatticeExtent) (m : ℕ), 2 ≤ m → (∀ μ : Fin 3, 4 ≤ L μ) →
        (∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1)) → (∀ μ : Fin 3, (1 * m) ∣ (L μ + 1)) →
        ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
          (B : Bond L → SuTwo),
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (1 * m) →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y (1 * m) →
            ∀ b ∈ staircasePath y x, B b = 0) →
          (∀ c : CoarseBond L (1 * m), lineCoarseRestrictCov U (1 * m) B c = 0) →
          (γ / (m : ℝ)) * covCoarseBondInner (lineCoarseRestrictCovLM U 1 B)
              (lineCoarseRestrictCovLM U 1 B)
            ≤ deltaJQuadFormCovFaithful 1 ([] : List (KernelSubspace.Level L)) U B := by
  rintro ⟨γ, hγ, h⟩
  refine CoarseCurlScaleTwo.not_coarseCurlPoincareFibreOne_one ⟨γ, hγ, ?_⟩
  intro L m hm hL hdvd1 hdvdm U B hadm hker
  have hk := h L m hm hL hdvd1 hdvdm U B hadm hker
  rw [pow_one, coarseCurlEnergyCov_one_eq_deltaJ U hdvd1 ([] : List (KernelSubspace.Level L)) B]
  exact hk

/-! ## §4 — blocker 1 is NOT mechanical: a PROVED dimension obstruction

`CStarDeltaKCOperator` §8's docstring asserts the two carriers "*are not isomorphic (different
finite dimensions whenever `Bond` is nonempty)*". Measured: there was NO declaration for this
anywhere in the tree (`grep` for `IsEmpty (… ≃ₗ …)` returned nothing). Here it is as a theorem. -/

/-- `E₁, E₂` are linearly independent, so `𝔰𝔲(2)`'s real dimension is at least `2`. -/
theorem two_le_finrank_suTwo : 2 ≤ Module.finrank ℝ SuTwo := by
  have hli : LinearIndependent ℝ ![pauliE1, pauliE2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (inner ℝ pauliE1 (s • pauliE1 + t • pauliE2) : ℝ) = 0 := by
      rw [hst]; exact inner_zero_right _
    have h2 : (inner ℝ pauliE2 (s • pauliE1 + t • pauliE2) : ℝ) = 0 := by
      rw [hst]; exact inner_zero_right _
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_eq_hsInner,
      inner_eq_hsInner, hsInner_e1_e1, hsInner_e1_e2] at h1
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_eq_hsInner,
      inner_eq_hsInner, hsInner_symm pauliE2 pauliE1, hsInner_e1_e2, hsInner_e2_e2] at h2
    constructor
    · linarith
    · linarith
  simpa using hli.fintype_card_le_finrank

/-- `finrank ℝ (BondFnL2 L) = card (Bond L) * finrank ℝ SuTwo`. -/
theorem finrank_bondFnL2 (L : PeriodicLatticeExtent) :
    Module.finrank ℝ (BondFnL2 L) = Fintype.card (Bond L) * Module.finrank ℝ SuTwo := by
  rw [(BondSU2Space.bondFnL2Equiv L).finrank_eq, Module.finrank_pi_fintype (R := ℝ),
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **THE OBSTRUCTION.** For every lattice, `EuclideanSpace ℝ (Bond L)` and `BondFnL2 L` are not
linearly isomorphic. Consequently NO adapter can carry a statement from the su(2) bond carrier to
`Spine.coerc_u_main`'s carrier; §3's one-way isometric descent is what is available instead. -/
theorem no_linearEquiv_euclid_bondFnL2 (L : PeriodicLatticeExtent) :
    IsEmpty (EuclideanSpace ℝ (Bond L) ≃ₗ[ℝ] BondFnL2 L) := by
  constructor
  intro e
  have hcard : 0 < Fintype.card (Bond L) := Fintype.card_pos
  have hdim := e.finrank_eq
  rw [finrank_euclideanSpace, finrank_bondFnL2] at hdim
  have h2 := two_le_finrank_suTwo
  nlinarith [hdim, hcard, h2]

/-- **The obstruction with the concrete numbers**, at `NonDegenerateInstances.witnessL`: the
scalar carrier has dimension `192`, the su(2) carrier at least `384`. Consumes
`NonDegenerateInstances.card_bond`. -/
theorem dimension_gap_at_witnessL :
    Module.finrank ℝ (EuclideanSpace ℝ (Bond AdmissibleSubspace.witnessL)) = 192 ∧
      384 ≤ Module.finrank ℝ (BondFnL2 AdmissibleSubspace.witnessL) := by
  refine ⟨?_, ?_⟩
  · rw [finrank_euclideanSpace, NonDegenerateInstances.card_bond]
  · rw [finrank_bondFnL2, NonDegenerateInstances.card_bond]
    have := two_le_finrank_suTwo
    omega

#print axioms coercive_shape_euclid
#print axioms inner_bondE3ToEuclid_value_at_one
#print axioms no_linear_m_constant_for_deltaJ
#print axioms coercive_shape_bondFnL2_nondegenerate
#print axioms coercive_shape_euclid_nondegenerate
#print axioms gamma0_ell0_one_trivialU
#print axioms norm_sq_bondFnL2
#print axioms coercive_shape_bondFnL2
#print axioms euclidToBondE3
#print axioms bondE3ToEuclid
#print axioms inner_bondE3ToEuclid
#print axioms inner_euclidToBondE3_self
#print axioms norm_euclidToBondE3
#print axioms euclidPullback
#print axioms inner_euclidPullback
#print axioms coercive_descends
#print axioms two_le_finrank_suTwo
#print axioms finrank_bondFnL2
#print axioms no_linearEquiv_euclid_bondFnL2
#print axioms dimension_gap_at_witnessL

end AdalyFormal.Balaban.IslandBridge
