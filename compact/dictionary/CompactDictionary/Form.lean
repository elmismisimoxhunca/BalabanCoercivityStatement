import CompactDictionary.Parameters
import CompactDictionary.CorrectedPropagators

/-! Exact parameter-level form dictionary, with all totalization branches retained. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8000
namespace CompactDictionary
open BalabanCompact
open scoped Classical RealInnerProductSpace
noncomputable section
variable (P : Prm) (hell : 0 < P.ell)
local notation "F" => frozenParams P hell

theorem baseData_eq :
    AdalyFormal.IngredientFamilyR2.baseData (F).G P.U P.a
      (AdalyFormal.IngredientFamilyR2.bondSectorOf (F).G P.U)
      (fieldPauli (Bond P.Lf) (Jfield (plaqIn (F).G.Om0) P.U)) = (F).data := by
  change AdalyFormal.IngredientFamilyR2.baseData (F).G P.U P.a
    (AdalyFormal.IngredientFamilyR2.bondSectorOf (F).G P.U)
    (fieldPauli (Bond P.Lf) P.Jf) = _
  rw [Jf_conjugacy]
  rfl

theorem frozen_inverse_spec :
    (AdalyFormal.IngredientFamilyR2.baseData (F).G P.U P.a
      (AdalyFormal.IngredientFamilyR2.bondSectorOf (F).G P.U)
      (fieldPauli (Bond P.Lf) (Jfield (plaqIn (F).G.Om0) P.U))).IsG1inv (F).G1inv := by
  rw [baseData_eq]
  exact (F).G1inv_spec

theorem prm_Nmat_conjugacy (f : FSp P.ell P.k P.strata) :
    sectorPauli (F).G (Nmat P.ell P.k P.bg (P.S.Om 0) P.strata P.U P.a f) =
      AdalyFormal.StatementLaneG.GenP.Nmat (F) (sectorPauli (F).G f) := by
  have h := Nmat_conjugacy (F).G P.U P.a (F).G1inv (frozen_inverse_spec P hell) f
  erw [baseData_eq P hell] at h
  dsimp only [frozenParams, AdalyFormal.IngredientFamilyR2.IngrBParams.G,
    AdalyFormal.IngredientFamilyR2.geomOf, towerEquiv, Equiv.coe_fn_mk,
    Prm.bg, Prm.strata, Prm.Lf, stratum, AdalyFormal.StatementLaneG.GenP.Nmat] at h ⊢
  exact h

theorem prm_H1E_conjugacy (f : FSp P.ell P.k P.strata) :
    H1E P.ell P.k P.bg (P.S.Om 0) P.strata P.U P.a f =
      includeE (F).G ((F).data.H1 (F).G1inv (sectorPauli (F).G f)) := by
  have h := H1E_conjugacy (F).G P.U P.a (F).G1inv (frozen_inverse_spec P hell) f
  erw [baseData_eq P hell] at h
  dsimp only [frozenParams, AdalyFormal.IngredientFamilyR2.IngrBParams.G,
    AdalyFormal.IngredientFamilyR2.geomOf, towerEquiv, Equiv.coe_fn_mk,
    Prm.bg, Prm.strata, Prm.Lf, stratum] at h ⊢
  exact h

/-- Top-level extraction, including its zero outside the constraint index set. -/
theorem tau_conjugacy (f : FSp P.ell P.k P.strata) :
    fieldPauli (Bond P.Lu) (tau P.ell P.k P.Lu P.strata f) = (F).tau (sectorPauli (F).G f) := by
  apply PiLp.ext
  intro b
  change pauli (if hb : unitBond P.ell P.k P.Lu b ∈ bondsLam P.ell P.k P.strata P.k then
    f ⟨⟨P.k, Nat.lt_succ_self P.k⟩, ⟨unitBond P.ell P.k P.Lu b, hb⟩⟩ else 0) = _
  change _ = if hb : unitBond P.ell P.k P.Lu b ∈ AdalyFormal.IngredientFamilyR2.bondsLam (F).G P.k then
    sectorPauli (F).G f ⟨Fin.last P.k, ⟨unitBond P.ell P.k P.Lu b, hb⟩⟩ else 0
  have hm : bondsLam P.ell P.k P.strata P.k = AdalyFormal.IngredientFamilyR2.bondsLam (F).G P.k :=
    bondsLam_eq (F).G P.k
  by_cases h : unitBond P.ell P.k P.Lu b ∈ bondsLam P.ell P.k P.strata P.k
  · have h' := hm ▸ h
    erw [dif_pos h, dif_pos h']
    rfl
  · have h' : unitBond P.ell P.k P.Lu b ∉ AdalyFormal.IngredientFamilyR2.bondsLam (F).G P.k :=
      fun hn => h (hm.symm ▸ hn)
    erw [dif_neg h, dif_neg h']
    exact pauli.map_zero

theorem tau_adjoint_conjugacy (B : Field P.Lu) :
    sectorPauli (F).G (ContinuousLinearMap.adjoint (tau P.ell P.k P.Lu P.strata) B) =
      ContinuousLinearMap.adjoint (F).tau (fieldPauli (Bond P.Lu) B) :=
  adjoint_conjugacy (sectorPauli (F).G) (fieldPauli (Bond P.Lu)) _ _ (tau_conjugacy P hell) B

theorem H1in_conjugacy (B : Field P.Lu) :
    fieldPauli (Bond P.Lf) (P.H1in B) = (F).H1in (fieldPauli (Bond P.Lu) B) := by
  change fieldPauli (Bond P.Lf) (H1E P.ell P.k P.bg (P.S.Om 0) P.strata P.U P.a
    (ContinuousLinearMap.adjoint (tau P.ell P.k P.Lu P.strata) B)) = _
  erw [prm_H1E_conjugacy P hell, fieldPauli_includeE, tau_adjoint_conjugacy]
  rfl

/-- Exact (3.156), not just a coercive bound: same eta, bare a, and source correction. -/
theorem genForm_eq (B : Field P.Lu) :
    genForm P B = AdalyFormal.StatementLaneG.GenP.genForm (F) (fieldPauli (Bond P.Lu) B) := by
  have hi := inverse_conjugacy (sectorPauli (F).G).toContinuousLinearEquiv _ _
    (prm_Nmat_conjugacy P hell)
    (ContinuousLinearMap.adjoint (tau P.ell P.k P.Lu P.strata) B)
  change sectorPauli (F).G (Ring.inverse (Nmat P.ell P.k P.bg (P.S.Om 0) P.strata P.U P.a)
    (ContinuousLinearMap.adjoint (tau P.ell P.k P.Lu P.strata) B)) =
    Ring.inverse (AdalyFormal.StatementLaneG.GenP.Nmat (F))
      (sectorPauli (F).G (ContinuousLinearMap.adjoint (tau P.ell P.k P.Lu P.strata) B)) at hi
  unfold genForm AdalyFormal.StatementLaneG.GenP.genForm AdalyFormal.StatementLaneG.GenP.firstTerm
  erw [← (sectorPauli (F).G).inner_map_map, hi, tau_adjoint_conjugacy]
  erw [(fieldPauli (Bond P.Lu)).inner_map_map]
  erw [← (fieldPauli (Bond P.Lf)).inner_map_map, H1in_conjugacy P hell,
    D2in_conjugacy, Jf_conjugacy]
  rfl

end
end CompactDictionary
