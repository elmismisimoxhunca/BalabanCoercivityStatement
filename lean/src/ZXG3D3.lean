import ZXG3D2

/-!
# G3D3 -- `WellDef` is a real condition: it FAILS at the closed point when `a = 0` (the mass is what
makes `G₁⁻¹` invertible there).  No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)

/-- a symmetric positive-semidefinite operator kills every vector with zero quadratic form -/
theorem psd_zero_mode {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E) (hsym : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (hpos : ∀ y, 0 ≤ ⟪y, S y⟫)
    (c : E) (hc : ⟪c, S c⟫ = 0) : S c = 0 := by
  let Bf : LinearMap.BilinForm ℝ E :=
    LinearMap.mk₂ ℝ (fun x y => ⟪x, S y⟫)
      (fun x x' y => by simp [inner_add_left]) (fun r x y => by simp [inner_smul_left])
      (fun x y y' => by simp [inner_add_right]) (fun r x y => by simp [inner_smul_right])
  have hBf : ∀ x y, Bf x y = ⟪x, S y⟫ := fun x y => rfl
  have hs : ∀ x, 0 ≤ Bf x x := fun x => by rw [hBf]; exact hpos x
  have key : ∀ v, ⟪S c, v⟫ = 0 := by
    intro v
    have h := LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le Bf hs c v
    have hsm : Bf v c = Bf c v := by
      rw [hBf, hBf, ← hsym, real_inner_comm]
    rw [hsm, hBf c c, hc, zero_mul] at h
    have h0 : Bf c v = 0 := by nlinarith [sq_nonneg (Bf c v)]
    rw [hBf] at h0
    rw [hsym]; exact h0
  exact ext_inner_right ℝ (fun v => by rw [inner_zero_left]; exact key v)

#print axioms psd_zero_mode

section
variable (ell : ℕ) (hell : 0 < ell)

theorem P0_not_wellDef_a_zero : ¬ GenP.WellDef (P0 ell (Ltile ell) hell 0 Set.univ) := by
  rintro ⟨-, hG, -⟩
  have hsym := (P0 ell (Ltile ell) hell 0 Set.univ).G1inv_spec.symm
  have hform := (P0 ell (Ltile ell) hell 0 Set.univ).G1inv_spec.form
  have hJd : (P0 ell (Ltile ell) hell 0 Set.univ).data.J = 0 := by
    show (pE (P0 ell (Ltile ell) hell 0 Set.univ).G) (P0 ell (Ltile ell) hell 0 Set.univ).Jf = 0
    rw [Jf_flat _ rfl]; exact map_zero _
  have hpos : ∀ y, 0 ≤ ⟪y, (P0 ell (Ltile ell) hell 0 Set.univ).G1inv y⟫ := by
    intro y
    rw [hform y]
    unfold BaseDataS.K
    rw [hJd, P0_mass_inner]
    have h1 : 0 ≤ ⟪y, (P0 ell (Ltile ell) hell 0 Set.univ).data.Dpi y⟫ := by
      show 0 ≤ ⟪y, (pE (P0 ell (Ltile ell) hell 0 Set.univ).G)
        (DpiFull (P0 ell (Ltile ell) hell 0 Set.univ).G flatCfg 0
          (iE (P0 ell (Ltile ell) hell 0 Set.univ).G y))⟫
      rw [pE_inner_right]
      exact DpiFull_flat_nonneg _ _ _
    have h2 := sq_nonneg ‖(P0 ell (Ltile ell) hell 0 Set.univ).data.T y‖
    simp only [inner_zero_right, mul_zero, sub_zero, zero_mul, add_zero]
    linarith
  set c : ↥(bondSupp (P0 ell (Ltile ell) hell 0 Set.univ).G) :=
    ⟨AdalyFormal.StatementLane3.constField (scaleUp ell 0 (Ltile ell)) suTwoWitness, by
      rw [P0_bondSupp_top]; exact Submodule.mem_top⟩ with hc
  have hc0 : ⟪c, (P0 ell (Ltile ell) hell 0 Set.univ).G1inv c⟫ = 0 := by
    rw [hform c]
    unfold BaseDataS.K
    rw [hJd, P0_mass_inner]
    obtain ⟨h1, h2⟩ := AdalyFormal.StatementLane3.genuine_laws_on_const
      (P0 ell (Ltile ell) hell 0 Set.univ).G 0 suTwoWitness
    have h1' : ⟪c, (P0 ell (Ltile ell) hell 0 Set.univ).data.Dpi c⟫ = 0 := by
      show ⟪c, (pE (P0 ell (Ltile ell) hell 0 Set.univ).G)
        (DpiFull (P0 ell (Ltile ell) hell 0 Set.univ).G flatCfg 0
          (iE (P0 ell (Ltile ell) hell 0 Set.univ).G c))⟫ = 0
      rw [pE_inner_right]; exact h1
    have h2' : (P0 ell (Ltile ell) hell 0 Set.univ).data.T c = 0 := h2
    rw [h1', h2']; simp
  have hScz := psd_zero_mode _ hsym hpos c hc0
  have hnz : c ≠ 0 := by
    intro h0
    have hpos' : 0 < ‖c‖ ^ 2 :=
      AdalyFormal.StatementLane3.constField_norm_pos suTwoWitness suTwoWitness_ne_zero
    rw [h0] at hpos'; simp at hpos'
  exact hnz ((ContinuousLinearMap.isUnit_iff_bijective.mp hG).1 (by rw [hScz, map_zero]))

#print axioms P0_not_wellDef_a_zero

end

end AdalyFormal.StatementLaneG
