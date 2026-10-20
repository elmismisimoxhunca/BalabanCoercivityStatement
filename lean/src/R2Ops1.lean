import AdalyFormal.Balaban.DeltaPrimeOperator
import AdalyFormal.Balaban.UbarTowerCovariance
import AdalyFormal.Balaban.JointInstantiation
import AdalyFormal.Balaban.CovariantHjMinimizer
import AdalyFormal.Balaban.ConstantA
import AdalyFormal.Balaban.SuTwoLogExpCore
import AdalyFormal.Balaban.BondSU2Space
import R2Algebra

/-!
# R2Ops1 -- concrete printed operators on the SU(2) carriers, CMP99b pp.390-395, 419-420

Printed objects (page images read this session: CMP99b p391 (3.3)-(3.6), p392 (3.8)-(3.11),
p393 (3.15)-(3.19); adjudicated text pages p394 (3.20)-(3.25), p395 (3.26)-(3.27), p419 (3.117)-(3.120)):
 * `D` covariant gradient, `D*` its adjoint (3.8);          * `Δ_U = D*D` (3.23);
 * `Q'_j(U)` (3.18)-(3.19), `Q'*aQ'` (3.24) with `a_{j+1} = a a_j/(a L^{-2}+a_j)`, `a_1=a_0=a`;
 * `R = Δ_U N(Q')` orthogonal projection (3.21)-(3.22);     * `G' = (Δ'_a|Ω_0)^{-1}`, `Δ'_a = Δ_U + Q'*aQ'`;
 * `Δ_π` via (3.119): `⟨A,Δ_π A⟩ = ⟨A − D G' R D* A, Δ (A − D G' R D* A)⟩`.

CONVENTION (stated once, binding on this lane): the tree's covariant operators are the `η = 1`
(unit-spacing) specialisations; fine-lattice printed forms carry the lattice weight `η^d`, and each
operator below is the Riesz representative, in the UNWEIGHTED `PiLp 2` structure of the statement
carriers, of the printed form with the overall `η^{d-2}` factored out (all of `Δ`, `DRD*`, `Q*aQ`
scale by the same `η^{-2}`, cf. REPORT).  The `η`-free body is what is built here.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant gradCovariantLM)
open AdalyFormal.Balaban.CovariantHjMinimizer (gradCovariantAdjointValue covSiteInner)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

/-- Site fields, `L²`-wrapped. -/
abbrev SiteL2 (L : PeriodicLatticeExtent) : Type :=
  PiLp 2 (fun _ : PeriodicLatticeSite L => SuTwo)

/-- SU(2) link configurations. -/
abbrev Cfg (L : PeriodicLatticeExtent) : Type :=
  PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L

/-! ## 1. masks (Dirichlet projections `χ_{Ω₀}`) -/

open Classical in
/-- Multiplication by the indicator of a set of sites: the characteristic function `Ω₀` of p.394. -/
noncomputable def siteMask (S : Set (PeriodicLatticeSite L)) : SiteL2 L →L[ℝ] SiteL2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun x => if x ∈ S then (WithLp.ofLp f) x else 0)
      map_add' := fun f g => by ext x; simp only [PiLp.add_apply]; split_ifs <;> simp
      map_smul' := fun c f => by ext x; simp only [PiLp.smul_apply]; split_ifs <;> simp }

open Classical in
theorem siteMask_apply (S : Set (PeriodicLatticeSite L)) (f : SiteL2 L) (x : PeriodicLatticeSite L) :
    (siteMask S f) x = if x ∈ S then f x else 0 := rfl

theorem siteMask_symm (S : Set (PeriodicLatticeSite L)) (f g : SiteL2 L) :
    ⟪siteMask S f, g⟫ = ⟪f, siteMask S g⟫ := by
  classical
  simp only [PiLp.inner_apply, siteMask_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs <;> simp

theorem siteMask_idem (S : Set (PeriodicLatticeSite L)) (f : SiteL2 L) :
    siteMask S (siteMask S f) = siteMask S f := by
  classical
  ext x; simp only [siteMask_apply]; split_ifs <;> simp

/-! ## 2. gradient `D`, adjoint `D*` (3.8), Laplacian `Δ_U = D*D` (3.23) -/

/-- `D_U : sites → bonds` as a continuous linear map between the `L²` carriers. -/
noncomputable def gradL2 (U : Cfg L) : SiteL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)).symm.toLinearMap ∘ₗ (gradCovariantLM U) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (PeriodicLatticeSite L → SuTwo)).toLinearMap)

theorem gradL2_apply (U : Cfg L) (f : SiteL2 L) :
    WithLp.ofLp (gradL2 U f) = gradValueCovariant U (WithLp.ofLp f) := rfl

/-- `D*` (3.8): the genuine Hilbert-space adjoint of `D`. -/
noncomputable def gradAdj (U : Cfg L) : BondFnL2 L →L[ℝ] SiteL2 L :=
  ContinuousLinearMap.adjoint (gradL2 U)

/-- The adjoint IS the printed explicit divergence formula (3.8). -/
theorem gradAdj_apply (U : Cfg L) (A : BondFnL2 L) :
    WithLp.ofLp (gradAdj U A) = gradCovariantAdjointValue U (WithLp.ofLp A) := by
  have h : gradAdj U A = WithLp.toLp 2 (gradCovariantAdjointValue U (WithLp.ofLp A)) := by
    refine ext_inner_left ℝ (fun w => ?_)
    rw [gradAdj, ContinuousLinearMap.adjoint_inner_right]
    have hw : w = WithLp.toLp 2 (WithLp.ofLp w) := rfl
    have hA : A = WithLp.toLp 2 (WithLp.ofLp A) := rfl
    rw [hw]
    simp only [WithLp.ofLp_toLp]
    rw [AdalyFormal.Balaban.CovariantHjMinimizer.inner_siteFnL2_eq_covSiteInner]
    show (inner ℝ (gradL2 U (WithLp.toLp 2 (WithLp.ofLp w))) A : ℝ) = _
    rw [hA]
    simp only [WithLp.ofLp_toLp]
    rw [show gradL2 U (WithLp.toLp 2 (WithLp.ofLp w)) = WithLp.toLp 2 (gradValueCovariant U (WithLp.ofLp w)) from rfl,
      AdalyFormal.Balaban.BondSU2Space.inner_bondFnL2_eq_covBondInner]
    exact (AdalyFormal.Balaban.JointInstantiation.hadj_of_gradCovariantAdjoint U (WithLp.ofLp A) (WithLp.ofLp w)).symm
  rw [h]


/-- `Δ_U = D*D` (3.23) on site fields, FULL lattice (`η = 1`). -/
noncomputable def lapFull (U : Cfg L) : SiteL2 L →L[ℝ] SiteL2 L := (gradAdj U).comp (gradL2 U)

theorem lapFull_symm (U : Cfg L) (f g : SiteL2 L) : ⟪lapFull U f, g⟫ = ⟪f, lapFull U g⟫ := by
  simp only [lapFull, gradAdj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

theorem inner_lapFull (U : Cfg L) (f : SiteL2 L) : ⟪f, lapFull U f⟫ = ‖gradL2 U f‖ ^ 2 := by
  simp only [lapFull, gradAdj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

/-! ## 3. the tower geometry and `Q'_j` (3.18)-(3.19), `N(Q')` -/

/-- The geometric data `Ω₀`, `Λ_j` (p.393) the print's operators are "defined by". -/
structure TowerGeom (L : PeriodicLatticeExtent) where
  ell : ℕ
  k : ℕ
  Om0 : Set (PeriodicLatticeSite L)
  Lam : ℕ → Set (PeriodicLatticeSite L)

open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.Balaban.QjComposite (Qcomposite QcompositeLM)

/-- The background tower `U, Ū, …, Ū^{j}` (CMP98 (43), tree `UbarTower` at the SU(2) chart). -/
noncomputable def bgTower (G : TowerGeom L) (U : Cfg L) : ℕ → Cfg L :=
  UbarTower su2LogExp G.ell U

/-- `(Q'_j(U) λ)(y)` (3.19), first line, as an ℝ-linear map of site fields. -/
noncomputable def QpLM (G : TowerGeom L) (U : Cfg L) (j : ℕ) :
    SiteL2 L →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo) :=
  QcompositeLM (bgTower G U) G.ell j ∘ₗ (WithLp.linearEquiv 2 ℝ (PeriodicLatticeSite L → SuTwo)).toLinearMap

/-- `λ ↦ (Q'_j(U)λ)(y)` as a continuous linear functional-valued map. -/
noncomputable def Qlev (G : TowerGeom L) (U : Cfg L) (j : ℕ) (y : PeriodicLatticeSite L) :
    SiteL2 L →L[ℝ] SuTwo :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj y : (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] SuTwo) ∘ₗ QpLM G U j)

theorem Qlev_apply (G : TowerGeom L) (U : Cfg L) (j : ℕ) (y : PeriodicLatticeSite L) (f : SiteL2 L) :
    Qlev G U j y f = Qcomposite (bgTower G U) G.ell j (WithLp.ofLp f) y := rfl

/-- `N(Q')` (3.21): site fields vanishing off `Ω₀` with `Q'_j(U)λ = 0` on `Λ_j`, `j = 0..k`. -/
noncomputable def NQp (G : TowerGeom L) (U : Cfg L) : Submodule ℝ (SiteL2 L) where
  carrier := {f | (∀ x, x ∉ G.Om0 → f x = 0) ∧
    ∀ j, j ≤ G.k → ∀ y, y ∈ G.Lam j → Qlev G U j y f = 0}
  zero_mem' := ⟨fun x _ => by simp, fun j _ y _ => by simp⟩
  add_mem' := fun {f g} hf hg => ⟨fun x hx => by simp [hf.1 x hx, hg.1 x hx],
    fun j hj y hy => by rw [map_add, hf.2 j hj y hy, hg.2 j hj y hy, add_zero]⟩
  smul_mem' := fun c f hf => ⟨fun x hx => by simp [hf.1 x hx],
    fun j hj y hy => by rw [map_smul, hf.2 j hj y hy, smul_zero]⟩

/-! ## 4. `R` (3.21)-(3.22): the orthogonal projection onto `Δ_U N(Q')` -/

/-- `Δ_U|_{Ω₀} = Ω₀ D*D Ω₀` (p.394, Dirichlet). -/
noncomputable def lapDir (G : TowerGeom L) (U : Cfg L) : SiteL2 L →L[ℝ] SiteL2 L :=
  ((siteMask G.Om0).comp (lapFull U)).comp (siteMask G.Om0)

/-- The subspace `Δ_U N(Q')` of (3.21). -/
noncomputable def RImage (G : TowerGeom L) (U : Cfg L) : Submodule ℝ (SiteL2 L) :=
  Submodule.map (lapDir G U : SiteL2 L →ₗ[ℝ] SiteL2 L) (NQp G U)

/-- `R = R(U)` (3.21): orthogonal projection onto `Δ_U N(Q')`. -/
noncomputable def Rproj (G : TowerGeom L) (U : Cfg L) : SiteL2 L →L[ℝ] SiteL2 L :=
  (RImage G U).starProjection

theorem Rproj_symm (G : TowerGeom L) (U : Cfg L) (f g : SiteL2 L) :
    ⟪Rproj G U f, g⟫ = ⟪f, Rproj G U g⟫ :=
  Submodule.starProjection_isSymmetric (RImage G U) f g

theorem Rproj_idem (G : TowerGeom L) (U : Cfg L) (f : SiteL2 L) :
    Rproj G U (Rproj G U f) = Rproj G U f :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

theorem Rproj_adjoint (G : TowerGeom L) (U : Cfg L) :
    ContinuousLinearMap.adjoint (Rproj G U) = Rproj G U := by
  ext1 f
  refine ext_inner_left ℝ (fun g => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, Rproj_symm]

/-- `R*R = R` for the genuine adjoint (the identity `D R D* = (RD*)*(RD*)` needs it). -/
theorem Rproj_adjoint_mul (G : TowerGeom L) (U : Cfg L) :
    (ContinuousLinearMap.adjoint (Rproj G U)).comp (Rproj G U) = Rproj G U := by
  ext1 f
  rw [Rproj_adjoint]
  exact Rproj_idem G U f

end AdalyFormal.IngredientFamilyR2
