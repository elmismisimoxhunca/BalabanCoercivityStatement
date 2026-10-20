/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RegularUPerturbation
import AdalyFormal.Balaban.CoercivityCov
import AdalyFormal.HoleHunt.LargeFieldKill
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `GeneralUHodgeDrift.lean` — the DIVERGENCE half of the single-scale drift bound

`RegularUPerturbation.lean` supplies the CURL half of the `U → 1` perturbation estimate:
`plaqEnergy (curlDrift U A) ≤ 32·α²·bondEnergy A` (`plaqEnergy_curlDrift_le`), where
`α` bounds `frobNorm(U b − 1)` uniformly over bonds.

The Hodge form `hodgeForm U B = ‖D¹_U B‖² + ‖(D⁰_U)^* B‖²` has TWO components, and the second one
— the covariant divergence `gradCovariantAdjointValue` — has **no drift bound anywhere in the
tree**. This module supplies it:

  `siteEnergy (divDrift U A) ≤ 12·α²·bondEnergy A`      (`siteEnergy_divDrift_le`)

with `divDrift U A := (D⁰_U)^*A − (D⁰_1)^*A`. The `12 = 3·4` is `d = 3` (Cauchy–Schwarz over the
three lattice directions) times the `2²` of `RMapLipschitz.norm_RMap_sub_self_le`. It is
`k`-independent and `L`-independent, exactly like the curl constant.

## Why the divergence drift is CHEAPER than the curl drift

`(D_U^*A)(y) = ∑_μ [R(U(y−e_μ,μ)⁻¹)(A(y−e_μ,μ)) − A(y,μ)]`. The OUTFLOW term `−A(y,μ)` carries no
`U` at all, so it cancels EXACTLY in the difference: the drift is a sum of three per-bond holonomy
deviations and nothing else (`divDrift_apply`). The curl drift needed a plaquette→bond incidence
count; this one needs only the shift bijection.

The one genuinely new ingredient is `frobNorm_inv_sub_one`: the deviation is measured at the
INVERSE holonomy `U(b)⁻¹`, and `frobNorm(U⁻¹ − 1) = frobNorm(U − 1)` because `U⁻¹ = Uᴴ` for a
special unitary and `frobSq` is conjugate-transpose invariant. Without it the bound would be stated
in a different (and non-`GaugeRegular`-comparable) quantity.

LAW-19: `RMapLipschitz.norm_RMap_sub_self_le`, `RegularUPerturbation.bondEnergy`,
`CovariantHjMinimizer.gradCovariantAdjointValue`, `CovariantHjMinimizer.bondShiftEquiv` are all
imported and reused; nothing is re-minted.
-/

namespace AdalyFormal.Balaban.GeneralUHodgeDrift

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.Balaban.AdmissibleSubspace AdalyFormal.Balaban.RegularUPerturbation

open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `frobNorm` at the INVERSE holonomy -/

/-- `frobSq` is invariant under conjugate transposition (`|conj z|² = |z|²`, entrywise). -/
theorem frobSq_conjTranspose (M : Matrix (Fin 2) (Fin 2) ℂ) :
    RMapLipschitz.frobSq Mᴴ = RMapLipschitz.frobSq M := by
  have hstar : ∀ z : ℂ, Complex.normSq (star z) = Complex.normSq z := by
    intro z
    simp [Complex.normSq_apply]
  simp only [RMapLipschitz.frobSq, Matrix.conjTranspose_apply, hstar]
  ring

/-- For a SPECIAL UNITARY `U`, the coerced group inverse is the conjugate transpose. -/
theorem coe_inv_eq_conjTranspose (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((U⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ :=
  Matrix.ext fun _ => congrFun rfl

/-- **The holonomy deviation is the same at `U` and at `U⁻¹`.**
`frobNorm(U⁻¹ − 1) = frobNorm(U − 1)`. This is what lets the divergence drift be measured in the
SAME quantity (`frobSupBond`, hence `GaugeRegular`'s first clause) as the curl drift. -/
theorem frobNorm_inv_sub_one (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    RMapLipschitz.frobNorm
        (((U⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      = RMapLipschitz.frobNorm ((U : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  have hstep : (((U⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      = ((U : Matrix (Fin 2) (Fin 2) ℂ) - 1)ᴴ := by
    rw [coe_inv_eq_conjTranspose, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  rw [hstep, RMapLipschitz.frobNorm, RMapLipschitz.frobNorm, frobSq_conjTranspose]

#print axioms frobSq_conjTranspose
#print axioms coe_inv_eq_conjTranspose
#print axioms frobNorm_inv_sub_one

/-! ## §2 — the site `L²` energy, and the divergence drift -/

/-- **Site `L²` energy** `= ∑_y ‖f y‖²`. The site-side analogue of
`RegularUPerturbation.plaqEnergy`/`bondEnergy`, kept as a plain real sum for the same
instance-diamond reason. -/
noncomputable def siteEnergy (f : PeriodicLatticeSite L → SuTwo) : ℝ :=
  ∑ y : PeriodicLatticeSite L, ‖f y‖ ^ 2

theorem siteEnergy_nonneg (f : PeriodicLatticeSite L → SuTwo) : 0 ≤ siteEnergy f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The single-scale divergence drift** `(D⁰_U)^*A − (D⁰_1)^*A`, as a bare site function. -/
noncomputable def divDrift
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : PeriodicLatticeSite L → SuTwo :=
  gradCovariantAdjointValue U A - gradCovariantAdjointValue (trivialU L) A

/-- **THE DIVERGENCE DRIFT IDENTITY.** The outflow term `−A(y,μ)` carries no `U`, so it cancels
exactly: at every site the drift is the sum over the three directions of the per-bond holonomy
deviation `R(U(b)⁻¹)A(b) − A(b)` at the INFLOWING bond `b = (y − e_μ, μ)`. First order in
`R(U(b)⁻¹) − id`, with no plaquette combinatorics. -/
theorem divDrift_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) :
    divDrift U A y =
      ∑ μ : Fin 3, (RMap (U (periodicLatticeShiftBack y μ, μ))⁻¹
          (A (periodicLatticeShiftBack y μ, μ)) - A (periodicLatticeShiftBack y μ, μ)) := by
  have hR : ∀ b : Bond L, RMap (trivialU L b)⁻¹ = LinearMap.id := by
    intro b
    show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)⁻¹ = LinearMap.id
    rw [inv_one]; exact RMap_one
  show gradCovariantAdjointValue U A y - gradCovariantAdjointValue (trivialU L) A y = _
  unfold gradCovariantAdjointValue
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hR]
  simp only [LinearMap.id_coe, id_eq]
  abel

#print axioms divDrift_apply

/-! ## §3 — the per-site bound -/

/-- **Per-site drift bound.** `‖divDrift U A y‖ ≤ 2α·∑_μ ‖A(y − e_μ, μ)‖`, `α` any uniform bound on
`frobNorm(U b − 1)`. Uses `RMapLipschitz.norm_RMap_sub_self_le` at the inverse holonomy, together
with §1's `frobNorm_inv_sub_one`. -/
theorem norm_divDrift_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    ‖divDrift U A y‖
      ≤ 2 * α * ∑ μ : Fin 3, ‖A (periodicLatticeShiftBack y μ, μ)‖ := by
  rw [divDrift_apply]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  set b : Bond L := (periodicLatticeShiftBack y μ, μ) with hb
  have hstep := RMapLipschitz.norm_RMap_sub_self_le (U b)⁻¹ (A b)
  rw [frobNorm_inv_sub_one] at hstep
  refine hstep.trans ?_
  have hAnn : (0 : ℝ) ≤ ‖A b‖ := norm_nonneg _
  have hle := hα b
  nlinarith [RMapLipschitz.frobNorm_nonneg ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)]

/-- **Per-site SQUARED drift bound.** `‖divDrift U A y‖² ≤ 12·α²·∑_μ ‖A(y − e_μ, μ)‖²`.
The `12 = 3·2²`: Cauchy–Schwarz over the `d = 3` directions times the `2` of
`norm_RMap_sub_self_le`. -/
theorem norm_divDrift_sq_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    ‖divDrift U A y‖ ^ 2
      ≤ 12 * α ^ 2 * ∑ μ : Fin 3, ‖A (periodicLatticeShiftBack y μ, μ)‖ ^ 2 := by
  have hlin := norm_divDrift_le U A y α hα0 hα
  have hnn : (0 : ℝ) ≤ 2 * α * ∑ μ : Fin 3, ‖A (periodicLatticeShiftBack y μ, μ)‖ := by
    have : (0 : ℝ) ≤ ∑ μ : Fin 3, ‖A (periodicLatticeShiftBack y μ, μ)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    positivity
  have hsq : ‖divDrift U A y‖ ^ 2
      ≤ (2 * α * ∑ μ : Fin 3, ‖A (periodicLatticeShiftBack y μ, μ)‖) ^ 2 := by
    have := norm_nonneg (divDrift U A y)
    nlinarith [hlin]
  refine hsq.trans ?_
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  set a0 := ‖A (periodicLatticeShiftBack y 0, 0)‖ with ha0
  set a1 := ‖A (periodicLatticeShiftBack y 1, 1)‖ with ha1
  set a2 := ‖A (periodicLatticeShiftBack y 2, 2)‖ with ha2
  have h0 : (0 : ℝ) ≤ a0 := norm_nonneg _
  have h1 : (0 : ℝ) ≤ a1 := norm_nonneg _
  have h2 : (0 : ℝ) ≤ a2 := norm_nonneg _
  nlinarith [sq_nonneg (a0 - a1), sq_nonneg (a0 - a2), sq_nonneg (a1 - a2), sq_nonneg α,
    sq_nonneg (a0 + a1 + a2)]

/-! ## §4 — the `L²` aggregation -/

/-- **The inflow reindexing.** `∑_y ∑_μ ‖A(y − e_μ, μ)‖² = bondEnergy A`, by the bond bijection
`(y,μ) ↦ (y − e_μ, μ)` (`CovariantHjMinimizer.bondShiftEquiv`, reused). -/
theorem sum_inflow_sq_eq_bondEnergy (A : Bond L → SuTwo) :
    ∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3,
        ‖A (periodicLatticeShiftBack y μ, μ)‖ ^ 2 = bondEnergy A := by
  have hsplit : ∑ b : Bond L, ‖A (periodicLatticeShiftBack b.1 b.2, b.2)‖ ^ 2
      = ∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3,
          ‖A (periodicLatticeShiftBack y μ, μ)‖ ^ 2 :=
    Fintype.sum_prod_type (fun b : Bond L => ‖A (periodicLatticeShiftBack b.1 b.2, b.2)‖ ^ 2)
  have hre : ∑ b : Bond L, ‖A (periodicLatticeShiftBack b.1 b.2, b.2)‖ ^ 2
      = ∑ b : Bond L, ‖A b‖ ^ 2 :=
    Fintype.sum_equiv (bondShiftEquiv (L := L)).symm _ _ fun _ => rfl
  rw [← hsplit, hre]
  rfl

/-- **THE `L²`-AGGREGATED DIVERGENCE DRIFT BOUND** — the missing half of the single-scale
perturbation estimate. `siteEnergy (divDrift U A) ≤ 12·α²·bondEnergy A`, with the explicit,
`k`-independent, `L`-independent constant `12`. -/
theorem siteEnergy_divDrift_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    siteEnergy (divDrift U A) ≤ 12 * α ^ 2 * bondEnergy A := by
  unfold siteEnergy
  refine le_trans (Finset.sum_le_sum fun y _ => norm_divDrift_sq_le U A y α hα0 hα) ?_
  rw [← Finset.mul_sum, sum_inflow_sq_eq_bondEnergy]

/-- **Consistency**: the drift is identically `0` at `U = 1`. -/
theorem divDrift_trivialU (A : Bond L → SuTwo) : divDrift (trivialU L) A = 0 := by
  unfold divDrift; simp

#print axioms norm_divDrift_le
#print axioms norm_divDrift_sq_le
#print axioms sum_inflow_sq_eq_bondEnergy
#print axioms siteEnergy_divDrift_le
#print axioms divDrift_trivialU

end AdalyFormal.Balaban.GeneralUHodgeDrift
