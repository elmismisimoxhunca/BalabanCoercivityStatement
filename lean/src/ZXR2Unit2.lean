import ZXR2Unit1

/-!
# R2Unit2 -- `C` of (3.157) (CMP99b p.428) and the corridor lift `h` (CMP109 p.267)

Printed (p.428, image read this session): "Variables B depend linearly on B̃ and we have B = CB̃, where
C is a linear operator. It is an identity operator on almost all bonds, except the bonds b₀ for which
a value (CB̃)(b₀) is equal to a solution of the equation (QB)(c) = 0, considered as an equation on
the variable B(b₀)."  with `b₀(c) = B(c) ∩ c` (tree: `droppedBondLast`).

Construction (valid for ANY linear `Q`): the coupled constraint matrix on the dropped bonds
`H₀ = ρ Q ι_D : (D → 𝔰𝔲(2)) → (D → 𝔰𝔲(2))`; if `H₀` is bijective, `h = ι_D H₀⁻¹ ρ` is the corridor lift
(`ρ Q h = ρ`, support on the dropped bonds) and `C = id − h Q`.  When `Q(c)` reads only `B(b₀(c))`
among the dropped bonds (decoupling, tree `droppedBondLast_not_reads` for the abelian block average)
`H₀` is block diagonal and `C B̃ (b₀(c))` is literally the solution of `(QB)(c)=0` for `B(b₀)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.IngredientFamilyR2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.StatementLane (scaleUp LamPrime IsDroppedIn CRowIn)

variable {L : PeriodicLatticeExtent}

/-- coarse bonds TOUCHING `Λ'` (r5 (3): `c₋ ∈ Λ'` or `c₊ ∈ Λ'`; r2..r4: `c₋ ∈ Λ'` only). -/
abbrev Dset (L : PeriodicLatticeExtent) (ell : ℕ) (Lam : Set (PeriodicLatticeSite L)) : Type :=
  {c : CoarseBond L ell // CRowIn ell Lam c}

noncomputable instance (ell : ℕ) (Lam : Set (PeriodicLatticeSite L)) : Fintype (Dset L ell Lam) := by
  classical
  exact inferInstance

/-- `ι_D`: place a coarse field on the dropped bonds. -/
noncomputable def iotaD (ell : ℕ) (Lam : Set (PeriodicLatticeSite L)) :
    (Dset L ell Lam → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) where
  toFun w := by
    classical
    exact fun b => ∑ c : Dset L ell Lam, if b = droppedBondLast ell c.1 then w c else 0
  map_add' w w' := by
    classical
    funext b
    simp [Finset.sum_add_distrib, ite_add_zero]
  map_smul' r w := by
    classical
    funext b
    simp [Finset.smul_sum, smul_ite]

/-- `ρ`: restrict a coarse field to `Λ'`. -/
def rhoD (ell : ℕ) (Lam : Set (PeriodicLatticeSite L)) :
    (CoarseBond L ell → SuTwo) →ₗ[ℝ] (Dset L ell Lam → SuTwo) where
  toFun f := fun c => f c.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem iotaD_apply_dropped {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (hinj : Function.Injective (droppedBondLast (L := L) ell)) (w : Dset L ell Lam → SuTwo)
    (c : Dset L ell Lam) : iotaD ell Lam w (droppedBondLast ell c.1) = w c := by
  classical
  show (∑ c' : Dset L ell Lam, if droppedBondLast ell c.1 = droppedBondLast ell c'.1 then w c' else 0) = _
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hne
    have : droppedBondLast ell c.1 ≠ droppedBondLast ell c'.1 := fun h =>
      hne (Subtype.ext (hinj h).symm)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ c) h

theorem iotaD_apply_not_dropped {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (w : Dset L ell Lam → SuTwo) (b : Bond L) (hb : ¬ IsDroppedIn Lam ell b) :
    iotaD ell Lam w b = 0 := by
  classical
  show (∑ c : Dset L ell Lam, if b = droppedBondLast ell c.1 then w c else 0) = 0
  refine Finset.sum_eq_zero (fun c _ => ?_)
  have : b ≠ droppedBondLast ell c.1 := fun h => hb ⟨c.1, c.2, h⟩
  simp [this]

/-- the coupled constraint matrix on the dropped bonds. -/
noncomputable def H0 {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo)) :
    (Dset L ell Lam → SuTwo) →ₗ[ℝ] (Dset L ell Lam → SuTwo) :=
  rhoD ell Lam ∘ₗ Q ∘ₗ iotaD ell Lam

/-- `H₀⁻¹` when `H₀` is bijective (else `0`). -/
noncomputable def H0inv {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo)) :
    (Dset L ell Lam → SuTwo) →ₗ[ℝ] (Dset L ell Lam → SuTwo) := by
  classical
  exact if h : Function.Bijective (H0 Lam Q) then (LinearEquiv.ofBijective (H0 Lam Q) h).symm.toLinearMap
    else 0

/-- THE CORRIDOR LIFT `h` (`Q h = id` on `Λ'`, supported on the dropped bonds). -/
noncomputable def hLift {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo)) :
    (CoarseBond L ell → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) :=
  iotaD ell Lam ∘ₗ H0inv Lam Q ∘ₗ rhoD ell Lam

/-- `C = id − h Q` (3.157). -/
noncomputable def Cop {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo)) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) :=
  LinearMap.id - hLift Lam Q ∘ₗ Q

theorem H0_H0inv {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo))
    (hb : Function.Bijective (H0 Lam Q)) (w : Dset L ell Lam → SuTwo) :
    H0 Lam Q (H0inv Lam Q w) = w := by
  classical
  unfold H0inv
  rw [dif_pos hb]
  exact (LinearEquiv.ofBijective (H0 Lam Q) hb).apply_symm_apply w

/-- `Q h = id` on `Λ'`: the LQ̃h = I of CMP109 p.267. -/
theorem rho_Q_hLift {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo))
    (hb : Function.Bijective (H0 Lam Q)) (w : CoarseBond L ell → SuTwo) :
    rhoD ell Lam (Q (hLift Lam Q w)) = rhoD ell Lam w := by
  show H0 Lam Q (H0inv Lam Q (rhoD ell Lam w)) = _
  exact H0_H0inv Lam Q hb _

/-- (3.157): `C` is the identity off the dropped bonds. -/
theorem Cop_id {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo)) (B : Bond L → SuTwo) (b : Bond L)
    (hb : ¬ IsDroppedIn Lam ell b) : Cop Lam Q B b = B b := by
  unfold Cop
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Pi.sub_apply]
  have : hLift Lam Q (Q B) b = 0 := iotaD_apply_not_dropped Lam _ b hb
  rw [this, sub_zero]

/-- (3.157): `Q(CB) = 0` at every `c` TOUCHING `Λ'` (r5 (3): `c₋ ∈ Λ'` or `c₊ ∈ Λ'`) — "(QB)(c) = 0" is solved. -/
theorem Cop_ker {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo))
    (hb : Function.Bijective (H0 Lam Q)) (B : Bond L → SuTwo) (c : CoarseBond L ell)
    (hc : CRowIn ell Lam c) : Q (Cop Lam Q B) c = 0 := by
  have h := rho_Q_hLift Lam Q hb (Q B)
  have h' := congrFun h ⟨c, hc⟩
  have e : (Cop Lam Q B) = B - hLift Lam Q (Q B) := rfl
  rw [e, map_sub]
  have : Q (hLift Lam Q (Q B)) c = Q B c := h'
  simp only [Pi.sub_apply]
  rw [this, sub_self]

#print axioms iotaD_apply_dropped
#print axioms rho_Q_hLift
#print axioms Cop_id
#print axioms Cop_ker

end AdalyFormal.IngredientFamilyR2
