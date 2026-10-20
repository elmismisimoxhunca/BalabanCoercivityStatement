import AdalyFormal.Balaban.DeltaPrimeOperator

/-!
# ZLocOps -- plaquette-restricted `Δ = D*D + Δ'` of CMP99b (3.10) (the lane's localisation reading, not the printed sandwich)  [r6/r7 statement lane]

The r5 operator `Delta U := deltaKCLMNormalized U` sums over ALL plaquettes of the fine torus and so reads `U` on
bonds lying wholly outside `Ω₀`.  The print (CMP99b p.394, page image): "The operators with the boundary conditions
have a very important property. They depend on the configuration `U` restricted to `Ω₀`. ... All operators we will
consider will be defined by using Dirichlet boundary conditions on `Ω₀`."
(r7 note: the print gives the explicit sandwich only for the SITE operator `Δ'_a`; restricting the plaquette sums of (3.10) to a caller-supplied `P` is
the lane's reading, chosen because the literal bond sandwich is false; see ZT5A header.)

Here every plaquette sum is restricted to a plaquette set `P` (the caller supplies
`P = {p | all four boundary bonds of p have both endpoints in Ω₀}`):
* `dstarDLoc U P = D_U^* χ_P D_U`   (curl mask `χ_P`);
* `deltaPrimeOpLoc U P`            (source-normalised `Δ'`, `bilPlaq` summed over `p ∈ P` only);
* `deltaKLocCLM U P = dstarDLoc + Δ'_loc`.
`deltaKLocCLM U univ = deltaKCLMNormalized U` (theorem `deltaKLocCLM_univ`): the localisation is a genuine
restriction, equal to the r5 object when `P` is everything.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AdalyFormal.StatementLaneR6

open scoped RealInnerProductSpace
open Classical
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (bilinToOperatorBond inner_bilinToOperatorBond
  curlAdjoint dstarDLM dstarDCLM inner_curlAdjoint_right)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator

variable {L : PeriodicLatticeExtent}

/-! ## 1. plaquette mask on `PlaqFnL2` -/

/-- multiplication by the indicator of a plaquette set. -/
noncomputable def plaqMask (P : Set (PeriodicLatticePlaquette L)) : PlaqFnL2 L →ₗ[ℝ] PlaqFnL2 L where
  toFun f := WithLp.toLp 2 (fun p => if p ∈ P then (WithLp.ofLp f) p else 0)
  map_add' f g := by ext p; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' c f := by ext p; simp only [PiLp.smul_apply]; split_ifs <;> simp

theorem plaqMask_apply (P : Set (PeriodicLatticePlaquette L)) (f : PlaqFnL2 L)
    (p : PeriodicLatticePlaquette L) : (plaqMask P f) p = if p ∈ P then f p else 0 := rfl

theorem plaqMask_symm (P : Set (PeriodicLatticePlaquette L)) (f g : PlaqFnL2 L) :
    ⟪plaqMask P f, g⟫ = ⟪f, plaqMask P g⟫ := by
  simp only [PiLp.inner_apply, plaqMask_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs <;> simp

theorem plaqMask_idem (P : Set (PeriodicLatticePlaquette L)) (f : PlaqFnL2 L) :
    plaqMask P (plaqMask P f) = plaqMask P f := by
  ext x; simp only [plaqMask_apply]; split_ifs <;> simp

theorem plaqMask_univ (f : PlaqFnL2 L) : plaqMask (Set.univ : Set (PeriodicLatticePlaquette L)) f = f := by
  ext x; simp [plaqMask_apply]

/-- `⟪f, χ_P g⟫ = ⟪χ_P f, χ_P g⟫`. -/
theorem inner_plaqMask_self (P : Set (PeriodicLatticePlaquette L)) (f g : PlaqFnL2 L) :
    ⟪f, plaqMask P g⟫ = ⟪plaqMask P f, plaqMask P g⟫ := by
  rw [plaqMask_symm, plaqMask_idem]

/-! ## 2. `D*D` restricted to the plaquettes of `P` -/

/-- `D_U^* χ_P D_U`: the curl energy summed over the plaquettes of `P` only. -/
noncomputable def dstarDLoc (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) : BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  (curlAdjoint U) ∘ₗ (plaqMask P) ∘ₗ (curlCovariantLM_L2 U)

theorem inner_dstarDLoc (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    (inner ℝ x (dstarDLoc U P y) : ℝ)
      = inner ℝ (plaqMask P (curlCovariantLM_L2 U x)) (plaqMask P (curlCovariantLM_L2 U y)) := by
  show (inner ℝ x (curlAdjoint U (plaqMask P (curlCovariantLM_L2 U y))) : ℝ) = _
  rw [inner_curlAdjoint_right, inner_plaqMask_self]

theorem dstarDLoc_univ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    dstarDLoc U (Set.univ : Set (PeriodicLatticePlaquette L)) = dstarDLM U := by
  refine LinearMap.ext (fun y => ?_)
  show curlAdjoint U (plaqMask Set.univ (curlCovariantLM_L2 U y)) = curlAdjoint U (curlCovariantLM_L2 U y)
  rw [plaqMask_univ]

theorem inner_dstarDLoc_symm (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    (inner ℝ (dstarDLoc U P x) y : ℝ) = inner ℝ x (dstarDLoc U P y) := by
  rw [real_inner_comm y (dstarDLoc U P x), inner_dstarDLoc, inner_dstarDLoc,
    real_inner_comm]

/-! ## 3. `Δ'` restricted to the plaquettes of `P` -/

/-- raw `Δ'` bilinear form with the plaquette sum restricted to `P`. -/
noncomputable def deltaPrimeBilRawLoc
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  ∑ p : PeriodicLatticePlaquette L, if p ∈ P then bilPlaq U p else 0

theorem deltaPrimeBilRawLoc_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    deltaPrimeBilRawLoc U P A B = ∑ p : PeriodicLatticePlaquette L, if p ∈ P then bilPlaq U p A B else 0 := by
  unfold deltaPrimeBilRawLoc
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> simp

theorem deltaPrimeBilRawLoc_univ
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    deltaPrimeBilRawLoc U (Set.univ : Set (PeriodicLatticePlaquette L)) = deltaPrimeBilRaw U := by
  unfold deltaPrimeBilRawLoc deltaPrimeBilRaw
  simp

/-- source-normalised symmetric `Δ'` form, localised. -/
noncomputable def deltaPrimeBilNormLoc
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (deltaPrimeBilRawLoc U P + (deltaPrimeBilRawLoc U P).flip))

theorem deltaPrimeBilNormLoc_univ
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    deltaPrimeBilNormLoc U (Set.univ : Set (PeriodicLatticePlaquette L)) = deltaPrimeBilNormalized U := by
  unfold deltaPrimeBilNormLoc deltaPrimeBilNormalized deltaPrimeBil
  rw [deltaPrimeBilRawLoc_univ]

theorem deltaPrimeBilNormLoc_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    deltaPrimeBilNormLoc U P A B = deltaPrimeBilNormLoc U P B A := by
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  ring

/-- `Δ'_loc` on the `L²` carrier (Riesz promotion of the transported localised form). -/
noncomputable def deltaPrimeBilL2NormLoc
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) : BondFnL2 L →ₗ[ℝ] BondFnL2 L →ₗ[ℝ] ℝ :=
  ((deltaPrimeBilNormLoc U P).compl₂ (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).toLinearMap) ∘ₗ
    (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).toLinearMap

theorem deltaPrimeBilL2NormLoc_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    deltaPrimeBilL2NormLoc U P x y = deltaPrimeBilL2NormLoc U P y x :=
  deltaPrimeBilNormLoc_symm U P _ _

theorem deltaPrimeBilL2NormLoc_univ
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    deltaPrimeBilL2NormLoc U (Set.univ : Set (PeriodicLatticePlaquette L)) = deltaPrimeBilL2Normalized U := by
  refine LinearMap.ext (fun x => LinearMap.ext (fun y => ?_))
  rw [deltaPrimeBilL2Normalized_apply]
  show deltaPrimeBilNormLoc U Set.univ _ _ = _
  rw [deltaPrimeBilNormLoc_univ, deltaPrimeBilNormalized_apply, deltaPrimeBilL2_apply]
  rfl

noncomputable def deltaPrimeOpLoc
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) : BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  bilinToOperatorBond (deltaPrimeBilL2NormLoc U P)

theorem inner_deltaPrimeOpLoc
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    (inner ℝ x (deltaPrimeOpLoc U P y) : ℝ) = deltaPrimeBilL2NormLoc U P x y :=
  inner_bilinToOperatorBond _ x y

theorem deltaPrimeOpLoc_univ
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    deltaPrimeOpLoc U (Set.univ : Set (PeriodicLatticePlaquette L)) = deltaPrimeOpNormalized U := by
  unfold deltaPrimeOpLoc deltaPrimeOpNormalized
  rw [deltaPrimeBilL2NormLoc_univ]

/-! ## 4. the localised `Δ` -/

/-- `Δ_loc = D*χ_P D + Δ'_loc` (CMP99b (3.10), plaquettes of `P` only). -/
noncomputable def deltaKLocCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (dstarDLoc U P) + LinearMap.toContinuousLinearMap (deltaPrimeOpLoc U P)

theorem inner_deltaKLocCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    (inner ℝ x (deltaKLocCLM U P y) : ℝ)
      = inner ℝ (plaqMask P (curlCovariantLM_L2 U x)) (plaqMask P (curlCovariantLM_L2 U y))
        + deltaPrimeBilL2NormLoc U P x y := by
  show (inner ℝ x (dstarDLoc U P y + deltaPrimeOpLoc U P y) : ℝ) = _
  rw [inner_add_right, inner_dstarDLoc, inner_deltaPrimeOpLoc]

theorem deltaKLocCLM_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    (inner ℝ (deltaKLocCLM U P x) y : ℝ) = inner ℝ x (deltaKLocCLM U P y) := by
  rw [real_inner_comm y (deltaKLocCLM U P x), inner_deltaKLocCLM, inner_deltaKLocCLM,
    real_inner_comm (plaqMask P (curlCovariantLM_L2 U x)), deltaPrimeBilL2NormLoc_symm]

/-- THE LOCALISATION IS A RESTRICTION: with every plaquette allowed it is the r5 `Δ`. -/
theorem deltaKLocCLM_univ
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    deltaKLocCLM U (Set.univ : Set (PeriodicLatticePlaquette L)) = deltaKCLMNormalized U := by
  unfold deltaKLocCLM deltaKCLMNormalized deltaPrimeCLMNormalized dstarDCLM
  rw [dstarDLoc_univ, deltaPrimeOpLoc_univ]

#print axioms plaqMask_symm
#print axioms inner_dstarDLoc
#print axioms dstarDLoc_univ
#print axioms deltaPrimeBilRawLoc_univ
#print axioms deltaPrimeBilL2NormLoc_univ
#print axioms deltaPrimeOpLoc_univ
#print axioms inner_deltaKLocCLM
#print axioms deltaKLocCLM_symm
#print axioms deltaKLocCLM_univ

/-! ## 5. flat background -/

theorem bilPlaq_trivialU (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    bilPlaq (trivialU (L := L)) p A B = 0 := by
  rw [bilPlaq_apply, firstBilPlaq_apply, secondBilPlaq_apply]
  simp [pairBil_apply, reHolonomy_trivialU, imHolonomy_trivialU]

theorem deltaPrimeBilRawLoc_trivialU (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    deltaPrimeBilRawLoc (trivialU (L := L)) P A B = 0 := by
  rw [deltaPrimeBilRawLoc_apply]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  split_ifs
  · exact bilPlaq_trivialU p A B
  · rfl

theorem deltaPrimeBilNormLoc_trivialU (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    deltaPrimeBilNormLoc (trivialU (L := L)) P A B = 0 := by
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply,
    deltaPrimeBilRawLoc_trivialU, smul_eq_mul]
  ring

theorem deltaKLocCLM_flat_nonneg (P : Set (PeriodicLatticePlaquette L)) (y : BondFnL2 L) :
    0 ≤ ⟪y, deltaKLocCLM (trivialU (L := L)) P y⟫ := by
  rw [inner_deltaKLocCLM]
  have : deltaPrimeBilL2NormLoc (trivialU (L := L)) P y y = 0 :=
    deltaPrimeBilNormLoc_trivialU P _ _
  rw [this, add_zero]
  exact real_inner_self_nonneg

#print axioms deltaKLocCLM_flat_nonneg

end AdalyFormal.StatementLaneR6
