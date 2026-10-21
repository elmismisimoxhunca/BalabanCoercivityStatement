import CompactDictionary.LocalForms

/-! The parameter record, k-fold unit background, source, corridor and quadratic lift. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CompactDictionary
open BalabanCompact
open AdalyFormal.Balaban.SuTwoLogExp
noncomputable section

def frozenParams (P : Prm) (hell : 0 < P.ell) : AdalyFormal.IngredientFamilyR2.IngrBParams :=
  ⟨P.ell, P.k, P.Lu, hell, towerEquiv P.S, P.U, P.a, P.Lam⟩

theorem embY_eq (ell k : ℕ) (Lu : Extent) (hell : 0 < ell) (y : Site Lu) :
    embY ell k Lu y = AdalyFormal.IngredientFamilyR2.embY ell k Lu hell y := rfl

theorem unitV_eq (P : Prm) (hell : 0 < P.ell) :
    P.unitV = (frozenParams P hell).unitBgU := by
  funext b
  change bgTower P.ell P.U P.k (unitBond P.ell P.k P.Lu b) = _
  rw [bgTower_eq]
  rfl

/-- This is the exact C in both headlines, evaluated at the k-fold blocked background. -/
theorem genC_conjugacy (P : Prm) (hell : 0 < P.ell) (B : Bond P.Lu → Vec) :
    piPauli (Equiv.refl (Bond P.Lu)) (P.genC B) =
      AdalyFormal.StatementLaneG.GenP.genC (frozenParams P hell)
        (piPauli (Equiv.refl (Bond P.Lu)) B) := by
  change piPauli (Equiv.refl (Bond P.Lu)) (Cop P.ell P.Lam (Q1LM P.ell P.unitV) B) = _
  rw [Cop_conjugacy, unitV_eq P hell]
  rfl

theorem Jf_conjugacy (P : Prm) (hell : 0 < P.ell) :
    fieldPauli (Bond P.Lf) P.Jf = (frozenParams P hell).Jf := by
  change fieldPauli (Bond P.Lf) (Jfield (plaqIn (P.S.Om 0)) P.U) = _
  rw [Jfield_conjugacy, plaqIn_eq]
  rfl

theorem D2in_conjugacy (P : Prm) (hell : 0 < P.ell) (B : Field P.Lu) :
    fieldPauli (Bond P.Lu) (toField (D2plain P.ell P.Lam P.unitV (ofField B))) =
      (frozenParams P hell).D2in (fieldPauli (Bond P.Lu) B) := by
  unfold AdalyFormal.IngredientFamilyR2.IngrBParams.D2in
    AdalyFormal.IngredientFamilyR2.IngrBParams.Q1
  change fieldPauli (Bond P.Lu) (toField (D2plain P.ell P.Lam P.unitV (ofField B))) =
    WithLp.toLp 2 (((P.ell : ℝ)⁻¹) •
      AdalyFormal.IngredientFamilyR2.hLift P.Lam
        (AdalyFormal.IngredientFamilyR2.Q1jet P.ell (frozenParams P hell).unitBgU)
        (AdalyFormal.IngredientFamilyR2.C2tilde P.ell (frozenParams P hell).unitBgU
          (piPauli (Equiv.refl (Bond P.Lu)) (ofField B))))
  rw [← unitV_eq P hell]
  apply PiLp.ext
  intro b
  exact congrFun (D2plain_conjugacy P.ell P.Lam P.unitV (ofField B)) b

end
end CompactDictionary
