import ZR3C
import AdalyFormal.Balaban.DeltaKFull

/-!
# R3D1 -- tree facts about the ACTUAL covariant operators at the trivial configuration:
  (i) the covariant curl `D_U^1` annihilates a constant bond field when `U = 1`;
  (ii) a constant bond field is `L²`-orthogonal to every covariant gradient `D_U λ` when `U = 1`
       (i.e. `D*c = 0`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane3

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (SiteFnL2 PlaqFnL2 trivialU)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open scoped RealInnerProductSpace

variable {L : PeriodicLatticeExtent}

/-- the constant bond field `A(b) = X` -/
def constField (L : PeriodicLatticeExtent) (X : SuTwo) : BondFnL2 L := WithLp.toLp 2 (fun _ => X)

/-- `D_U : L²(sites, 𝔰𝔲(2)) → L²(bonds, 𝔰𝔲(2))`, the tree's covariant gradient on the `L²` carriers -/
noncomputable def gradL2 (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    SiteFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)).symm.toLinearMap ∘ₗ gradCovariantLM U ∘ₗ
      (WithLp.linearEquiv 2 ℝ (PeriodicLatticeSite L → SuTwo)).toLinearMap)

theorem gradL2_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : SiteFnL2 L) (b : Bond L) :
    (gradL2 U lam).ofLp b = RMap (U b) (lam.ofLp (periodicLatticeShift b.1 b.2)) - lam.ofLp b.1 := rfl

/-- (i) the curl of a constant field vanishes at the trivial configuration -/
theorem curl_const_trivial (X : SuTwo) :
    curlCovariantCLM_L2 (trivialU L) (constField L X) = 0 := by
  unfold constField
  rw [curlCovariantCLM_L2_toLp]
  have : curlValueCovariant (trivialU L) (fun _ => X) = 0 := by
    funext p
    simp [curlValueCovariant, trivialU, RMap_one]
  rw [this]; rfl

theorem shift_sum_eq (μ : Fin 3) (f : PeriodicLatticeSite L → ℝ) :
    ∑ x, f (periodicLatticeShift x μ) = ∑ x, f x := by
  classical
  have hinj : Function.Injective (fun x : PeriodicLatticeSite L => periodicLatticeShift x μ) :=
    shift_injective μ
  have hbij := Finite.injective_iff_bijective.mp hinj
  exact Equiv.sum_comp (Equiv.ofBijective _ hbij) f

/-- (ii) `D* c = 0` at the trivial configuration: `⟨c, D λ⟩ = 0` for every `λ` -/
theorem const_orth_grad_trivial (X : SuTwo) (lam : SiteFnL2 L) :
    ⟪constField L X, gradL2 (trivialU L) lam⟫ = 0 := by
  classical
  rw [PiLp.inner_apply]
  simp only [constField, gradL2_apply, WithLp.ofLp_toLp, trivialU, RMap_one, LinearMap.id_apply]
  have hsplit : ∀ F : Bond L → ℝ, ∑ b : Bond L, F b = ∑ μ : Fin 3, ∑ x : PeriodicLatticeSite L, F (x, μ) :=
    fun F => Fintype.sum_prod_type_right F
  rw [hsplit]
  refine Finset.sum_eq_zero fun μ _ => ?_
  have e : ∀ x : PeriodicLatticeSite L,
      ⟪X, lam.ofLp (periodicLatticeShift x μ) - lam.ofLp x⟫ =
        ⟪X, lam.ofLp (periodicLatticeShift x μ)⟫ - ⟪X, lam.ofLp x⟫ := fun x => inner_sub_right _ _ _
  simp only [e]
  rw [Finset.sum_sub_distrib, shift_sum_eq μ (fun x => ⟪X, lam.ofLp x⟫), sub_self]

theorem constField_norm_pos (X : SuTwo) (hX : X ≠ 0) :
    0 < ‖constField L X‖ ^ 2 := by
  classical
  have : constField L X ≠ 0 := by
    intro h
    have := congrArg (fun y : BondFnL2 L => y.ofLp ((fun _ => (0 : Fin _)) , (0 : Fin 3))) h
    simp [constField] at this
    exact hX this
  positivity

#print axioms curl_const_trivial
#print axioms const_orth_grad_trivial
#print axioms constField_norm_pos

end AdalyFormal.StatementLane3
