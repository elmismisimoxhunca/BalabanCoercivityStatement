import CompactDictionary.Support

/-! Full-space/Dirichlet dictionary for G and H; no invertibility assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CompactDictionary
open BalabanCompact
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open scoped RealInnerProductSpace
noncomputable section
variable {L : Extent}
variable (G : AdalyFormal.IngredientFamilyR2.TowerGeom L) (U : Cfg L) (a : ℝ) (J : BondFnL2 L)
local notation "bg" => bgTower G.ell U
local notation "D" => AdalyFormal.IngredientFamilyR2.baseData G U a
  (AdalyFormal.IngredientFamilyR2.bondSectorOf G U) J

theorem Dpi_compress (x : Supported G) :
    projectE G (Dpi G.ell G.k bg G.Om0 G.Lam U a (includeE G x)) = (D).Dpi x := by
  change AdalyFormal.IngredientFamilyR2.pE G (fieldPauli (Bond L) (Dpi _ _ _ _ _ _ _ _)) = _
  rw [Dpi_conjugacy, fieldPauli_includeE]
  rfl

theorem Mass_compress (x : Supported G) :
    projectE G (MassFull G.ell G.k bg G.Lam a (includeE G x)) = (D).Mass x := by
  change AdalyFormal.IngredientFamilyR2.pE G (fieldPauli (Bond L) (MassFull _ _ _ _ _ _)) = _
  rw [MassFull_conjugacy, fieldPauli_includeE]
  rfl

theorem Tfull_conjugacy (x : Field L) :
    fieldPauli (Site L) (Tfull G.ell G.k bg G.Om0 G.Lam U x) = (D).T (projectE G x) := by
  change fieldPauli (Site L) (Rproj _ _ _ _ _ _ (gradAdj U (bondMask G.Om0 x))) = _
  rw [Rproj_conjugacy, gradAdj_conjugacy, ← includeE_projectE, fieldPauli_includeE]
  rfl

theorem Tfull_adjoint (s : SiteL2 L) :
    ContinuousLinearMap.adjoint (Tfull G.ell G.k bg G.Om0 G.Lam U) s =
      includeE G ((D).Ts (fieldPauli (Site L) s)) := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, ← (fieldPauli (Site L)).inner_map_map,
    Tfull_conjugacy G U a J, (D).T_adj]
  exact (real_inner_comm _ _).trans ((projectE_inner G _ x).trans (real_inner_comm _ _))

theorem Qe_conjugacy (x : Field L) :
    sectorPauli G (Qe G.ell G.k bg G.Om0 G.Lam x) = (D).Q (projectE G x) := by
  change sectorPauli G (Qfull _ _ _ _ (bondMask G.Om0 x)) = _
  rw [Qfull_conjugacy, ← includeE_projectE, fieldPauli_includeE]
  rfl

theorem Qs_conjugacy (f : FSp G.ell G.k G.Lam) :
    Qs G.ell G.k bg G.Om0 G.Lam f = includeE G ((D).Qs (sectorPauli G f)) := by
  apply ext_inner_left ℝ
  intro x
  rw [Qs, ContinuousLinearMap.adjoint_inner_right, ← (sectorPauli G).inner_map_map,
    Qe_conjugacy G U a J, (D).Q_adj]
  exact (real_inner_comm _ _).trans ((projectE_inner G _ x).trans (real_inner_comm _ _))

theorem Ginv_pad : Ginv G.ell G.k bg G.Om0 G.Lam U a = pad (includeE G) (projectE G) (D).Ginv := by
  ext1 x
  simp only [Ginv, _root_.add_apply, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply, pad_apply, AdalyFormal.IngredientFamilyR2.BaseDataS.Ginv, map_add]
  rw [Tfull_adjoint G U a J, Tfull_conjugacy G U a J]
  rw [← includeE_projectE G x, ← includeE_projectE G (Dpi _ _ _ _ _ _ _ _),
    ← includeE_projectE G (MassFull _ _ _ _ _ _), Dpi_compress G U a J, Mass_compress G U a J]

theorem GE_conjugacy (x : Field L) :
    GE G.ell G.k bg G.Om0 G.Lam U a x = includeE G ((D).G (projectE G x)) := by
  unfold GE
  rw [Ginv_pad G U a J, inverse_supported]
  rfl

theorem QGEQs_conjugacy (f : FSp G.ell G.k G.Lam) :
    sectorPauli G (((Qe G.ell G.k bg G.Om0 G.Lam).comp
      (GE G.ell G.k bg G.Om0 G.Lam U a)).comp (Qs G.ell G.k bg G.Om0 G.Lam) f) =
    (((D).Q.comp (D).G).comp (D).Qs) (sectorPauli G f) := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [Qe_conjugacy G U a J, GE_conjugacy G U a J, projectE_includeE,
    Qs_conjugacy G U a J, projectE_includeE]

theorem HE_conjugacy (f : FSp G.ell G.k G.Lam) :
    HE G.ell G.k bg G.Om0 G.Lam U a f = includeE G ((D).H (sectorPauli G f)) := by
  unfold HE
  simp only [ContinuousLinearMap.comp_apply]
  rw [GE_conjugacy G U a J, Qs_conjugacy G U a J, projectE_includeE]
  have hi := inverse_conjugacy (sectorPauli G).toContinuousLinearEquiv _ _
    (QGEQs_conjugacy G U a J) f
  change sectorPauli G ((Ring.inverse (((Qe G.ell G.k bg G.Om0 G.Lam).comp
    (GE G.ell G.k bg G.Om0 G.Lam U a)).comp (Qs G.ell G.k bg G.Om0 G.Lam))) f) =
    Ring.inverse (((D).Q.comp (D).G).comp (D).Qs) (sectorPauli G f) at hi
  rw [hi]
  rfl

end
end CompactDictionary
