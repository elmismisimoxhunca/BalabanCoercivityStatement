import ZR2C4c

/-!
# R2C4d -- TOTAL INHABITANT of `IngrB` (must-not-fire): a family whose ingredients are the pinned
ones plus the simplest abstract base data (`Dpi = id`, `T = 0`, `C2 = 0`, `a = 1`, `Ubar ≡ 1`,
`hlift = 0`, `Qraw = 0`).  It is in the class, hence the class is non-empty (at EVERY tiled
`(k, Lu, S, U, Λ)`, not just the flat point).  NOT claimed: that this family is Balaban's.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.FullReparamC (fullCLM dinvC)
open AdalyFormal.IngredientFamily (BaseData JSU2 D2unit D2unit_quad)
open scoped RealInnerProductSpace

section good
variable (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
  (U : LinkCfg (scaleUp ell k Lu))

noncomputable def goodBase : BaseData (BondFnL2 (scaleUp ell k Lu)) (BondFnL2 Lu) where
  Dpi := ContinuousLinearMap.id ℝ _
  T := 0
  Ts := 0
  Q := Qclm ell hell k Lu U
  Qs := ContinuousLinearMap.adjoint (Qclm ell hell k Lu U)
  a := 1
  C2 := fun _ => 0
  J := WithLp.toLp 2 (JSU2 (((ell : ℝ) ^ k)⁻¹) U)
  T_adj := by intro x y; simp
  Q_adj := fun x y => (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

theorem goodBase_isG1inv : (goodBase ell hell k Lu U).IsG1inv (goodBase ell hell k Lu U).Ginv := by
  have hform : ∀ A : BondFnL2 (scaleUp ell k Lu), ⟪A, (goodBase ell hell k Lu U).Ginv A⟫ =
      (goodBase ell hell k Lu U).K A := by
    intro A
    simp only [BaseData.Ginv, BaseData.K, goodBase, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, map_zero, inner_zero_left, inner_add_right, inner_smul_right,
      norm_zero]
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, inner_zero_right]
    ring
  refine ⟨?_, hform⟩
  intro x y
  simp only [BaseData.Ginv, goodBase, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, map_zero, inner_zero_left,
    inner_zero_right]
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_left]
  simp [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

theorem goodBase_unit : IsUnit (((goodBase ell hell k Lu U).Q.comp
    ((goodBase ell hell k Lu U).G1 (goodBase ell hell k Lu U).Ginv)).comp
      (goodBase ell hell k Lu U).Qs) := by
  refine (goodBase ell hell k Lu U).QG1Qs_isUnit (goodBase_isG1inv ell hell k Lu U)
    (c := 1) one_pos ?_ (Qs_injective ell hell k Lu U)
  intro x
  rw [(goodBase_isG1inv ell hell k Lu U).form x]
  simp only [BaseData.K, goodBase, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
    map_zero, inner_zero_left, norm_zero]
  rw [real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖(Qclm ell hell k Lu U) x‖]


variable (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (Lam : Set (PeriodicLatticeSite Lu))

/-- the inhabitant `Ingr` at a tiled point -/
noncomputable def goodIngr' : Ingr ell Lu (scaleUp ell k Lu) Lam where
  Q := Qclm ell hell k Lu U
  Qs := ContinuousLinearMap.adjoint (Qclm ell hell k Lu U)
  G1 := Ring.inverse (goodBase ell hell k Lu U).Ginv
  a := 1
  H1 := ((Ring.inverse (goodBase ell hell k Lu U).Ginv).comp
      (ContinuousLinearMap.adjoint (Qclm ell hell k Lu U))).comp
    (Ring.inverse (((Qclm ell hell k Lu U).comp (Ring.inverse (goodBase ell hell k Lu U).Ginv)).comp
      (ContinuousLinearMap.adjoint (Qclm ell hell k Lu U))))
  D2 := D2unit (0 : (CoarseBond Lu ell → SuTwo) →L[ℝ] BondFnL2 Lu)
    (0 : BondFnL2 Lu → (CoarseBond Lu ell → SuTwo))
  J := WithLp.toLp 2 (JSU2 (((ell : ℝ) ^ k)⁻¹) U)
  Q1 := lineCoarseRestrictCovLM (fun _ => (1 : G2)) ell
  C := Clam ell Lam (fun _ => (1 : G2))
  Qs_adj := fun x y => (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  D2_quad := fun c B => D2unit_quad _ _ c B
  QGQ_unit := goodBase_unit ell hell k Lu U
  C_id := fun B b h => Clam_id Lam _ B b h
  C_ker := fun B _ _ c hc => Clam_ker hell hd Lam _ B c hc

end good

end AdalyFormal.StatementLane2
