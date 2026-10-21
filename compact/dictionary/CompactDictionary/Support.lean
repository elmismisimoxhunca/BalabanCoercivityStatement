import CompactDictionary.BondOperators

/-! The frozen supported space embedded in the compact full bond space. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CompactDictionary
open BalabanCompact
open scoped Classical RealInnerProductSpace
noncomputable section
variable {L : Extent}
variable (G : AdalyFormal.IngredientFamilyR2.TowerGeom L)

abbrev Supported := ↥(AdalyFormal.IngredientFamilyR2.bondSupp G)

def includeE : Supported G →L[ℝ] Field L :=
  (fieldPauli (Bond L)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (AdalyFormal.IngredientFamilyR2.iE G)

def projectE : Field L →L[ℝ] Supported G :=
  (AdalyFormal.IngredientFamilyR2.pE G).comp
    (fieldPauli (Bond L)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem includeE_apply (x : Supported G) (b : Bond L) :
    includeE G x b = pauli.symm (x.val b) := rfl

theorem fieldPauli_includeE (x : Supported G) :
    fieldPauli (Bond L) (includeE G x) = AdalyFormal.IngredientFamilyR2.iE G x :=
  (fieldPauli (Bond L)).apply_symm_apply _

theorem includeE_inner (x y : Supported G) : ⟪includeE G x, includeE G y⟫ = ⟪x, y⟫ := by
  rw [← (fieldPauli (Bond L)).inner_map_map, fieldPauli_includeE, fieldPauli_includeE]
  rfl

theorem projectE_inner (x : Supported G) (y : Field L) :
    ⟪x, projectE G y⟫ = ⟪includeE G x, y⟫ := by
  change ⟪x, AdalyFormal.IngredientFamilyR2.pE G (fieldPauli (Bond L) y)⟫ = _
  rw [AdalyFormal.IngredientFamilyR2.pE_inner_right,
    ← fieldPauli_includeE, (fieldPauli (Bond L)).inner_map_map]

theorem projectE_includeE (x : Supported G) : projectE G (includeE G x) = x := by
  apply ext_inner_left ℝ
  intro y
  rw [projectE_inner, includeE_inner]

theorem projectE_comp_includeE : (projectE G).comp (includeE G) = 1 := by
  ext1 x
  exact projectE_includeE G x

theorem bondMask_includeE (x : Supported G) : bondMask G.Om0 (includeE G x) = includeE G x := by
  apply PiLp.ext
  intro b
  change (if b ∈ bondsTouch G.Om0 then pauli.symm (x.val b) else 0) = pauli.symm (x.val b)
  split_ifs with hb
  · rfl
  · have hz := x.property b hb
    rw [hz, map_zero]

theorem bondMask_symmetric (S : Set (Site L)) (x y : Field L) :
    ⟪bondMask S x, y⟫ = ⟪x, bondMask S y⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  change inner ℝ (if b ∈ bondsTouch S then x b else 0) (y b) =
    inner ℝ (x b) (if b ∈ bondsTouch S then y b else 0)
  split_ifs <;> simp

theorem includeE_projectE (x : Field L) : includeE G (projectE G x) = bondMask G.Om0 x := by
  let z : Supported G := ⟨fieldPauli (Bond L) (bondMask G.Om0 x), by
    intro b hb
    change pauli (if b ∈ bondsTouch G.Om0 then x b else 0) = 0
    change b ∉ bondsTouch G.Om0 at hb
    rw [if_neg hb, map_zero]⟩
  have hz : includeE G z = bondMask G.Om0 x := (fieldPauli (Bond L)).symm_apply_apply _
  have hp : projectE G x = z := by
    apply ext_inner_left ℝ
    intro y
    rw [projectE_inner, ← includeE_inner G y z, hz, ← bondMask_symmetric, bondMask_includeE]
  rw [hp, hz]

theorem includeE_adjoint : ContinuousLinearMap.adjoint (includeE G) = projectE G := by
  ext1 x
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, projectE_inner]

theorem projectE_adjoint : ContinuousLinearMap.adjoint (projectE G) = includeE G := by
  rw [← includeE_adjoint, ContinuousLinearMap.adjoint_adjoint]

/-- All singular and empty-support cases are retained by the final mask. -/
theorem inverse_supported (A : Supported G →L[ℝ] Supported G) :
    (Ring.inverse (pad (includeE G) (projectE G) A)).comp (bondMask G.Om0) =
      (includeE G).comp ((Ring.inverse A).comp (projectE G)) := by
  have hm : bondMask G.Om0 = (includeE G).comp (projectE G) := by
    ext1 x
    exact (includeE_projectE G x).symm
  rw [hm]
  exact inverse_pad_mask _ _ (projectE_comp_includeE G) A

end
end CompactDictionary
