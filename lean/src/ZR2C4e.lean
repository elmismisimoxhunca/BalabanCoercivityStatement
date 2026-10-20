import ZR2C4d

/-!
# R2C4e -- the total family `goodFam` and the theorem `IngrB` is INHABITED (not vacuous).
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

open Classical in
noncomputable def goodFam (ell : ℕ) (hell : 0 < ell) : IngrFamK ell :=
  fun k Lu S U Lam =>
    if hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1 then goodIngr' ell hell k Lu U hd Lam
    else JunkCopy.junkIngr ell hell k Lu Lam

theorem goodFam_eq (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) :
    goodFam ell hell k Lu S U Lam = goodIngr' ell hell k Lu U hd Lam := by
  classical
  simp only [goodFam, dif_pos hd]

noncomputable def goodIngr'_IngrBAt (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (U : LinkCfg (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) :
    IngrBAt ell hell k Lu Lam U (fun _ => (1 : G2)) (goodIngr' ell hell k Lu U hd Lam) where
  base := goodBase ell hell k Lu U
  base_Q := rfl
  base_Qs := rfl
  base_a := rfl
  base_J := rfl
  a_pos := one_pos
  J_eq := rfl
  G1inv := (goodBase ell hell k Lu U).Ginv
  G1inv_spec := goodBase_isG1inv ell hell k Lu U
  G1_eq := rfl
  H1_eq := rfl
  Q_eq := fun A b => Qclm_apply ell hell k Lu U A b
  Q1_eq := rfl
  C_univ := fun h => by subst h; exact Clam_univ _
  Qraw := 0
  hlift := 0
  D2_eq := rfl

/-- **`IngrB` is inhabited** (so the class is non-empty at EVERY tiled point, every `U`, every `Λ`). -/
noncomputable def goodIngrB (ell : ℕ) (hell : 0 < ell) : IngrB ell hell (goodFam ell hell) where
  Ubar := fun _ _ _ => fun _ => (1 : G2)
  Ubar_one := fun _ _ => rfl
  at_ := fun k Lu hd S U Lam => by
    rw [goodFam_eq ell hell k Lu hd S U Lam]
    exact goodIngr'_IngrBAt ell hell k Lu hd U Lam

theorem IngrB_nonempty (ell : ℕ) (hell : 0 < ell) : Nonempty (IngrB ell hell (goodFam ell hell)) :=
  ⟨goodIngrB ell hell⟩

#print axioms goodIngr'_IngrBAt
#print axioms IngrB_nonempty

end AdalyFormal.StatementLane2
