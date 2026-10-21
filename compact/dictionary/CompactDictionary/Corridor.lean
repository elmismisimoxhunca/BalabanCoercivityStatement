import CompactDictionary.Jets

/-! Unit-level `Q₁`, the dropped-row reindexing, and the totalized corridor `C`. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace CompactDictionary
open BalabanCompact
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open scoped Classical
noncomputable section
variable {L : Extent}

/-- Algebraic pointwise Pauli map, also reindexing the finite carriers. -/
def piPauli {ι κ : Type*} (e : ι ≃ κ) : (ι → Vec) ≃ₗ[ℝ] (κ → SuTwo) :=
  (LinearEquiv.piCongrRight (fun _ => pauli.toLinearEquiv)).trans
    (LinearEquiv.funCongrLeft ℝ SuTwo e.symm)

@[simp] theorem piPauli_apply {ι κ : Type*} (e : ι ≃ κ) (v : ι → Vec) (j : κ) :
    piPauli e v j = pauli (v (e.symm j)) := rfl

@[simp] theorem piPauli_apply_equiv {ι κ : Type*} (e : ι ≃ κ) (v : ι → Vec) (j : ι) :
    piPauli e v (e j) = pauli (v j) := by simp

def drowEquiv (ell : ℕ) (Lam : Set (Site L)) : Drow (L := L) ell Lam ≃
    AdalyFormal.IngredientFamilyR2.Dset L ell Lam :=
  (coarseBondEquiv ell).subtypeEquiv (crowIn_iff ell Lam)

theorem suCoordF_pauli (B : Bond L → Vec) :
    AdalyFormal.IngredientFamilyR2.suCoordF (piPauli (Equiv.refl (Bond L)) B) = rawField L B := by
  funext b
  change AdalyFormal.IngredientFamilyR2.fromM2 (toM (B b)) = rawCoords (B b)
  rw [← toM2_rawCoords, AdalyFormal.IngredientFamilyR2.fromM2_toM2]

theorem suCoordFInv_raw (B : Bond L → Vec) :
    AdalyFormal.IngredientFamilyR2.suCoordFInv (rawField L B) = piPauli (Equiv.refl (Bond L)) B := by
  funext b
  apply Subtype.ext
  exact toM2_rawCoords (B b)

theorem Q1_conjugacy (ell : ℕ) (V : Cfg L) (B : Bond L → Vec) :
    piPauli (coarseBondEquiv ell) (Q1LM ell V B) =
      AdalyFormal.IngredientFamilyR2.Q1jet ell V (piPauli (Equiv.refl (Bond L)) B) := by
  funext c
  obtain ⟨c, rfl⟩ := (coarseBondEquiv (L := L) ell).surjective c
  rw [piPauli_apply_equiv]
  change pauli (((ell : ℝ)⁻¹) • QlinStep 1 ell V B c.1) = _
  rw [map_smul]
  unfold AdalyFormal.IngredientFamilyR2.Q1jet
  simp only [LinearMap.coe_mk, AddHom.coe_mk, suCoordF_pauli,
    ← QlinStep_conjugacy, suCoordFInv_raw]
  rfl

theorem C2tilde_conjugacy (ell : ℕ) (V : Cfg L) (B : Bond L → Vec) :
    piPauli (coarseBondEquiv ell) (C2tilde ell V B) =
      AdalyFormal.IngredientFamilyR2.C2tilde ell V (piPauli (Equiv.refl (Bond L)) B) := by
  funext c
  obtain ⟨c, rfl⟩ := (coarseBondEquiv (L := L) ell).surjective c
  rw [piPauli_apply_equiv]
  unfold AdalyFormal.IngredientFamilyR2.C2tilde
  rw [suCoordF_pauli, ← C2Step_conjugacy, suCoordFInv_raw]
  rfl

theorem iotaD_conjugacy (ell : ℕ) (Lam : Set (Site L)) (w : Drow (L := L) ell Lam → Vec) :
    piPauli (Equiv.refl (Bond L)) (iotaD ell Lam w) =
      AdalyFormal.IngredientFamilyR2.iotaD ell Lam (piPauli (drowEquiv ell Lam) w) := by
  funext b
  change pauli (∑ c : Drow (L := L) ell Lam, if b = droppedBond ell c.1.1 then w c else 0) = _
  rw [map_sum]
  change _ = ∑ c : AdalyFormal.IngredientFamilyR2.Dset L ell Lam,
    if b = AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell c.1 then
      piPauli (drowEquiv ell Lam) w c else 0
  rw [← (drowEquiv ell Lam).sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hd : AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell
      ((drowEquiv ell Lam c).1) = droppedBond ell c.1.1 := (droppedBond_eq ell c.1).symm
  rw [hd, piPauli_apply_equiv]
  split_ifs <;> simp

theorem rhoD_conjugacy (ell : ℕ) (Lam : Set (Site L)) (w : CoarseBond (L := L) ell → Vec) :
    piPauli (drowEquiv ell Lam) (rhoD ell Lam w) =
      AdalyFormal.IngredientFamilyR2.rhoD ell Lam (piPauli (coarseBondEquiv ell) w) := by
  funext c
  obtain ⟨c, rfl⟩ := (drowEquiv ell Lam).surjective c
  rw [piPauli_apply_equiv]
  rfl

section TotalInverse
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem bijective_conjugacy (e : E ≃ₗ[ℝ] F) (A : E →ₗ[ℝ] E) (B : F →ₗ[ℝ] F)
    (h : ∀ x, e (A x) = B (e x)) : Function.Bijective A ↔ Function.Bijective B := by
  have hB : (B : F → F) = e ∘ A ∘ e.symm := by
    funext x
    simpa using (h (e.symm x)).symm
  have hA : (A : E → E) = e.symm ∘ B ∘ e := by
    funext x
    simp only [Function.comp_apply, ← h, e.symm_apply_apply]
  constructor
  · intro ha
    rw [hB]
    exact e.bijective.comp (ha.comp e.symm.bijective)
  · intro hb
    rw [hA]
    exact e.symm.bijective.comp (hb.comp e.bijective)

/-- Transport the chosen inverse, including its zero branch, without matching proofs. -/
theorem guarded_inverse_conjugacy (e : E ≃ₗ[ℝ] F) (A : E →ₗ[ℝ] E) (B : F →ₗ[ℝ] F)
    (h : ∀ x, e (A x) = B (e x)) (x : E) :
    e ((if ha : Function.Bijective A then (LinearEquiv.ofBijective A ha).symm.toLinearMap else 0) x) =
      (if hb : Function.Bijective B then (LinearEquiv.ofBijective B hb).symm.toLinearMap else 0) (e x) := by
  by_cases ha : Function.Bijective A
  · have hb := (bijective_conjugacy e A B h).mp ha
    rw [dif_pos ha, dif_pos hb]
    apply hb.1
    rw [← h]
    change e ((LinearEquiv.ofBijective A ha) ((LinearEquiv.ofBijective A ha).symm x)) =
      (LinearEquiv.ofBijective B hb) ((LinearEquiv.ofBijective B hb).symm (e x))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · have hb : ¬ Function.Bijective B := fun hb => ha ((bijective_conjugacy e A B h).mpr hb)
    rw [dif_neg ha, dif_neg hb]
    exact e.map_zero
end TotalInverse

theorem H0_conjugacy (ell : ℕ) (Lam : Set (Site L)) (V : Cfg L) (w : Drow (L := L) ell Lam → Vec) :
    piPauli (drowEquiv ell Lam) (H0 ell Lam (Q1LM ell V) w) =
      AdalyFormal.IngredientFamilyR2.H0 Lam (AdalyFormal.IngredientFamilyR2.Q1jet ell V)
        (piPauli (drowEquiv ell Lam) w) := by
  change piPauli (drowEquiv ell Lam) (rhoD ell Lam (Q1LM ell V (iotaD ell Lam w))) = _
  rw [rhoD_conjugacy, Q1_conjugacy, iotaD_conjugacy]
  rfl

theorem H0inv_conjugacy (ell : ℕ) (Lam : Set (Site L)) (V : Cfg L) (w : Drow (L := L) ell Lam → Vec) :
    piPauli (drowEquiv ell Lam) (H0inv ell Lam (Q1LM ell V) w) =
      AdalyFormal.IngredientFamilyR2.H0inv Lam (AdalyFormal.IngredientFamilyR2.Q1jet ell V)
        (piPauli (drowEquiv ell Lam) w) :=
  guarded_inverse_conjugacy (piPauli (drowEquiv ell Lam)) _ _ (H0_conjugacy ell Lam V) w

theorem hLift_conjugacy (ell : ℕ) (Lam : Set (Site L)) (V : Cfg L) (w : CoarseBond (L := L) ell → Vec) :
    piPauli (Equiv.refl (Bond L)) (hLift ell Lam (Q1LM ell V) w) =
      AdalyFormal.IngredientFamilyR2.hLift Lam (AdalyFormal.IngredientFamilyR2.Q1jet ell V)
        (piPauli (coarseBondEquiv ell) w) := by
  change piPauli (Equiv.refl (Bond L)) (iotaD ell Lam (H0inv ell Lam (Q1LM ell V) (rhoD ell Lam w))) = _
  rw [iotaD_conjugacy, H0inv_conjugacy, rhoD_conjugacy]
  rfl

/-- The exact corridor, with no invertibility premise. -/
theorem Cop_conjugacy (ell : ℕ) (Lam : Set (Site L)) (V : Cfg L) (B : Bond L → Vec) :
    piPauli (Equiv.refl (Bond L)) (Cop ell Lam (Q1LM ell V) B) =
      AdalyFormal.IngredientFamilyR2.Cop Lam (AdalyFormal.IngredientFamilyR2.Q1jet ell V)
        (piPauli (Equiv.refl (Bond L)) B) := by
  change piPauli (Equiv.refl (Bond L)) (B - hLift ell Lam (Q1LM ell V) (Q1LM ell V B)) = _
  rw [map_sub, hLift_conjugacy, Q1_conjugacy]
  rfl

theorem hLift_zero_of_not_bijective (ell : ℕ) (Lam : Set (Site L))
    (Q : (Bond L → Vec) →ₗ[ℝ] (CoarseBond (L := L) ell → Vec))
    (h : ¬ Function.Bijective (H0 ell Lam Q)) : hLift ell Lam Q = 0 := by
  simp [hLift, H0inv, h]

theorem Cop_id_of_not_bijective (ell : ℕ) (Lam : Set (Site L))
    (Q : (Bond L → Vec) →ₗ[ℝ] (CoarseBond (L := L) ell → Vec))
    (h : ¬ Function.Bijective (H0 ell Lam Q)) : Cop ell Lam Q = LinearMap.id := by
  rw [Cop, hLift_zero_of_not_bijective ell Lam Q h]
  simp

theorem D2plain_conjugacy (ell : ℕ) (Lam : Set (Site L)) (V : Cfg L) (B : Bond L → Vec) :
    piPauli (Equiv.refl (Bond L)) (D2plain ell Lam V B) =
      ((ell : ℝ)⁻¹) • AdalyFormal.IngredientFamilyR2.hLift Lam (AdalyFormal.IngredientFamilyR2.Q1jet ell V)
        (AdalyFormal.IngredientFamilyR2.C2tilde ell V (piPauli (Equiv.refl (Bond L)) B)) := by
  rw [D2plain, map_smul, hLift_conjugacy, C2tilde_conjugacy]

end
end CompactDictionary
