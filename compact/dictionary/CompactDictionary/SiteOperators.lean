import CompactDictionary.LocalForms
import CompactDictionary.Transport

/-! Site averaging, its Hilbert adjoint, and the totalized Dirichlet site chain. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CompactDictionary
open BalabanCompact
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open scoped Classical RealInnerProductSpace
noncomputable section
variable {L : Extent}

theorem pauli_Rmap (U : SU2) (v : Vec) : pauli (Rmap U v) = RMap U (pauli v) := by
  rw [show Rmap U v = conjM (U : M2) v by
    unfold Rmap conjM
    rw [AdalyFormal.Balaban.SuTwoLogExp.coe_matrix_inv]]
  exact pauli_conjM U v

theorem transport_eq (s : ℕ) (V : Cfg L) (y x : Site L)
    (h : ∀ μ, (y μ).val ≤ (x μ).val) :
    transport s V y x = AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy s V y
      (AdalyFormal.Balaban.TowerLawCov.coarseGammaPath s y x) := by
  rw [transport, coarseHol_eq, gammaPath_eq s y x h, ofMat_coe]

theorem stepAvg_conjugacy (s ell : ℕ) (V : Cfg L) (f : Site L → Vec) (y : Site L) :
    pauli (stepAvgLM s ell V f y) = AdalyFormal.Balaban.QjComposite.stepAverage s V ell
      (fun x => pauli (f x)) y := by
  change pauli (((ell : ℝ) ^ 3)⁻¹ • ∑ x ∈ stepBlock y s ell, Rmap (transport s V y x) (f x)) = _
  rw [map_smul, map_sum]
  unfold AdalyFormal.Balaban.QjComposite.stepAverage
  rw [one_div, ← stepBlock_eq]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [pauli_Rmap, transport_eq s V y x (fun μ => ((Finset.mem_filter.mp hx).2 μ).1)]

theorem Qcomp_conjugacy (ell : ℕ) (bg : ℕ → Cfg L) (j : ℕ) (f : Site L → Vec) :
    (fun y => pauli (QcompLM ell bg j f y)) =
      AdalyFormal.Balaban.QjComposite.Qcomposite bg ell j (fun x => pauli (f x)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext y
    change pauli (stepAvgLM (ell ^ j) ell (bg j) (QcompLM ell bg j f) y) = _
    rw [stepAvg_conjugacy, ih]
    rfl

theorem siteMask_conjugacy (S : Set (Site L)) (f : SiteL2 L) :
    fieldPauli (Site L) (siteMask S f) =
      AdalyFormal.IngredientFamilyR2.siteMask S (fieldPauli (Site L) f) := by
  apply PiLp.ext
  intro x
  change pauli (if x ∈ S then f x else 0) = if x ∈ S then pauli (f x) else 0
  split_ifs <;> simp

theorem gradL_conjugacy (U : Cfg L) (f : SiteL2 L) :
    fieldPauli (Bond L) (gradL U f) =
      AdalyFormal.IngredientFamilyR2.gradL2 U (fieldPauli (Site L) f) := by
  apply PiLp.ext
  intro b
  change pauli (Rmap (U b) (f (shift b.1 b.2)) - f b.1) = _
  rw [map_sub, pauli_Rmap]
  rfl

theorem gradAdj_conjugacy (U : Cfg L) (A : Field L) :
    fieldPauli (Site L) (gradAdj U A) =
      AdalyFormal.IngredientFamilyR2.gradAdj U (fieldPauli (Bond L) A) :=
  adjoint_conjugacy (fieldPauli (Site L)) (fieldPauli (Bond L)) _ _ (gradL_conjugacy U) A

theorem lapFull_conjugacy (U : Cfg L) (f : SiteL2 L) :
    fieldPauli (Site L) (lapFull U f) =
      AdalyFormal.IngredientFamilyR2.lapFull U (fieldPauli (Site L) f) := by
  change fieldPauli (Site L) (gradAdj U (gradL U f)) = _
  rw [gradAdj_conjugacy, gradL_conjugacy]
  rfl

theorem ajSeq_eq (a : ℝ) (ell j : ℕ) : ajSeq a ell j = AdalyFormal.IngredientFamilyR2.ajSeq a ell j := by
  have h : ∀ n, aSeqAux a (a / ((ell : ℝ) * ell)) n =
      AdalyFormal.Balaban.ConstantA.aSeqAux a (a / ((ell : ℝ) * ell)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [aSeqAux, AdalyFormal.Balaban.ConstantA.aSeqAux, ih]
  simp only [ajSeq, AdalyFormal.IngredientFamilyR2.ajSeq, AdalyFormal.Balaban.ConstantA.aSeq, h]

variable (G : AdalyFormal.IngredientFamilyR2.TowerGeom L) (U : Cfg L)

theorem bg_eq : bgTower G.ell U = AdalyFormal.IngredientFamilyR2.bgTower G U :=
  funext (bgTower_eq G.ell U)

theorem Qlev_conjugacy (j : ℕ) (y : Site L) (f : SiteL2 L) :
    pauli (Qlev G.ell (bgTower G.ell U) j y f) =
      AdalyFormal.IngredientFamilyR2.Qlev G U j y (fieldPauli (Site L) f) := by
  change pauli (QcompLM G.ell (bgTower G.ell U) j (WithLp.ofLp f) y) = _
  rw [congrFun (Qcomp_conjugacy G.ell (bgTower G.ell U) j (WithLp.ofLp f)) y, bg_eq G U]
  rfl

theorem Qpa_conjugacy (a : ℝ) (f : SiteL2 L) :
    fieldPauli (Site L) (Qpa G.ell G.k (bgTower G.ell U) G.Lam a f) =
      AdalyFormal.IngredientFamilyR2.Qpa G U a (fieldPauli (Site L) f) := by
  simp only [Qpa, AdalyFormal.IngredientFamilyR2.Qpa, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hy
  · simp only [ContinuousLinearMap.smul_apply, map_smul, ajSeq_eq, rankOne, ContinuousLinearMap.comp_apply]
    rw [adjoint_conjugacy (fieldPauli (Site L)) pauli _ _ (Qlev_conjugacy G U j y), Qlev_conjugacy]
  · simp

theorem DelpA_conjugacy (a : ℝ) (f : SiteL2 L) :
    fieldPauli (Site L) (DelpA G.ell G.k (bgTower G.ell U) G.Om0 G.Lam U a f) =
      AdalyFormal.IngredientFamilyR2.DelpA G U a (fieldPauli (Site L) f) := by
  simp only [DelpA, AdalyFormal.IngredientFamilyR2.DelpA, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, siteMask_conjugacy, map_add, lapFull_conjugacy, Qpa_conjugacy]

theorem Gp_conjugacy (a : ℝ) (f : SiteL2 L) :
    fieldPauli (Site L) (Gp G.ell G.k (bgTower G.ell U) G.Om0 G.Lam U a f) =
      AdalyFormal.IngredientFamilyR2.Gp G U a (fieldPauli (Site L) f) := by
  unfold Gp AdalyFormal.IngredientFamilyR2.Gp
  simp only [ContinuousLinearMap.comp_apply]
  have hi := inverse_conjugacy (fieldPauli (Site L)).toContinuousLinearEquiv
    (DelpA G.ell G.k (bgTower G.ell U) G.Om0 G.Lam U a + (1 - siteMask G.Om0))
    (AdalyFormal.IngredientFamilyR2.DelpA G U a + (1 - AdalyFormal.IngredientFamilyR2.siteMask G.Om0))
    (fun x => by
      change fieldPauli (Site L) (DelpA G.ell G.k (bgTower G.ell U) G.Om0 G.Lam U a x +
        (x - siteMask G.Om0 x)) = _
      simp only [_root_.add_apply, _root_.sub_apply, ContinuousLinearMap.one_apply,
        map_add, map_sub, DelpA_conjugacy, siteMask_conjugacy]
      rfl) (siteMask G.Om0 f)
  exact hi.trans (congrArg _ (siteMask_conjugacy G.Om0 f))

theorem NQp_mem_iff (f : SiteL2 L) :
    fieldPauli (Site L) f ∈ AdalyFormal.IngredientFamilyR2.NQp G U ↔
      f ∈ NQp G.ell G.k (bgTower G.ell U) G.Om0 G.Lam := by
  change ((∀ x, x ∉ G.Om0 → pauli (f x) = 0) ∧
    ∀ j, j ≤ G.k → ∀ y, y ∈ G.Lam j →
      AdalyFormal.IngredientFamilyR2.Qlev G U j y (fieldPauli (Site L) f) = 0) ↔
    ((∀ x, x ∉ G.Om0 → f x = 0) ∧
    ∀ j, j ≤ G.k → ∀ y, y ∈ G.Lam j → Qlev G.ell (bgTower G.ell U) j y f = 0)
  simp only [← Qlev_conjugacy, pauli_eq_zero_iff]

theorem lapDir_conjugacy (f : SiteL2 L) :
    fieldPauli (Site L) (lapDir G.Om0 U f) =
      AdalyFormal.IngredientFamilyR2.lapDir G U (fieldPauli (Site L) f) := by
  simp only [lapDir, AdalyFormal.IngredientFamilyR2.lapDir, ContinuousLinearMap.comp_apply,
    siteMask_conjugacy, lapFull_conjugacy]

theorem RImage_mem_iff (f : SiteL2 L) :
    fieldPauli (Site L) f ∈ AdalyFormal.IngredientFamilyR2.RImage G U ↔
      f ∈ RImage G.ell G.k (bgTower G.ell U) G.Om0 G.Lam U := by
  constructor
  · rintro ⟨g, hg, he⟩
    obtain ⟨x, rfl⟩ := (fieldPauli (Site L)).surjective g
    refine ⟨x, (NQp_mem_iff G U x).mp hg, (fieldPauli (Site L)).injective ?_⟩
    exact (lapDir_conjugacy G U x).trans he
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fieldPauli (Site L) x, (NQp_mem_iff G U x).mpr hx, (lapDir_conjugacy G U x).symm⟩

theorem Rproj_conjugacy (f : SiteL2 L) :
    fieldPauli (Site L) (Rproj G.ell G.k (bgTower G.ell U) G.Om0 G.Lam U f) =
      AdalyFormal.IngredientFamilyR2.Rproj G U (fieldPauli (Site L) f) :=
  projection_conjugacy (fieldPauli (Site L)) _ _ (RImage_mem_iff G U) f

theorem Wop_conjugacy (a : ℝ) (A : Field L) :
    fieldPauli (Bond L) (Wop G.ell G.k (bgTower G.ell U) G.Om0 G.Lam U a A) =
      AdalyFormal.IngredientFamilyR2.Wop G U a (fieldPauli (Bond L) A) := by
  simp only [Wop, AdalyFormal.IngredientFamilyR2.Wop, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply, map_sub,
    gradL_conjugacy, Gp_conjugacy, Rproj_conjugacy, gradAdj_conjugacy]

end
end CompactDictionary
