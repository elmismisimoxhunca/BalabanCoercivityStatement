import ZR2C4a

/-!
# R2C4b -- the pinned `Q` as a continuous linear map `BondFnL2 Lf →L BondFnL2 Lu`; surjective;
its adjoint is injective.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCov_add lineCoarseRestrictCov_smul)
open scoped RealInnerProductSpace

theorem embSite_inj (ell : ℕ) (hell : 0 < ell) (k : ℕ) {Lu : PeriodicLatticeExtent}
    {y y' : PeriodicLatticeSite Lu} (h : embSite ell hell k y = embSite ell hell k y') : y = y' := by
  funext μ
  have := congrArg Fin.val (congrFun h μ)
  simp only [embSite] at this
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left (pow_pos hell k) this)

noncomputable def Qlin (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (U : LinkCfg (scaleUp ell k Lu)) :
    (Bond (scaleUp ell k Lu) → SuTwo) →ₗ[ℝ] (Bond Lu → SuTwo) where
  toFun A b := lineCoarseRestrictCov U (ell ^ k) A
    ⟨⟨embSite ell hell k b.1, embSite_mem ell hell k b.1⟩, b.2⟩
  map_add' A B := by
    funext b; exact lineCoarseRestrictCov_add U (ell ^ k) A B _
  map_smul' c A := by
    funext b; exact lineCoarseRestrictCov_smul U (ell ^ k) c A _

/-- **The pinned `Q = Q_k(U)`** (fine → unit): the tree's covariant line-integral block average at
block size `ell^k` read through the coarse-site embedding `y ↦ ell^k y`. -/
noncomputable def Qclm (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (U : LinkCfg (scaleUp ell k Lu)) :
    BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 Lu :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Bond Lu → SuTwo)).symm.toLinearMap ∘ₗ Qlin ell hell k Lu U ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Bond (scaleUp ell k Lu) → SuTwo)).toLinearMap)

theorem Qclm_apply (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (U : LinkCfg (scaleUp ell k Lu)) (A : BondFnL2 (scaleUp ell k Lu)) (b : Bond Lu) :
    (Qclm ell hell k Lu U A).ofLp b = lineCoarseRestrictCov U (ell ^ k) A.ofLp
      ⟨⟨embSite ell hell k b.1, embSite_mem ell hell k b.1⟩, b.2⟩ := rfl

theorem Qclm_surj (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (U : LinkCfg (scaleUp ell k Lu)) : Function.Surjective (Qclm ell hell k Lu U) := by
  classical
  intro y
  have hdvd : ∀ μ : Fin 3, ell ^ k ∣ scaleUp ell k Lu μ + 1 := by
    intro μ
    have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by
      have := pow_pos hell k; positivity)
    simp only [scaleUp]
    rw [Nat.sub_add_cancel this]
    exact Dvd.intro_left _ rfl
  let B'' : CoarseBond (scaleUp ell k Lu) (ell ^ k) → SuTwo := fun c =>
    if h : ∃ b : Bond Lu, (⟨⟨embSite ell hell k b.1, embSite_mem ell hell k b.1⟩, b.2⟩ :
        CoarseBond (scaleUp ell k Lu) (ell ^ k)) = c then y.ofLp h.choose else 0
  obtain ⟨A, hA⟩ := coarseRestrictCov_surj (pow_pos hell k) hdvd U B''
  refine ⟨WithLp.toLp 2 A, ?_⟩
  ext b
  rw [Qclm_apply]
  simp only [WithLp.ofLp_toLp]
  rw [hA]
  have hex : ∃ b' : Bond Lu, (⟨⟨embSite ell hell k b'.1, embSite_mem ell hell k b'.1⟩, b'.2⟩ :
        CoarseBond (scaleUp ell k Lu) (ell ^ k)) =
      ⟨⟨embSite ell hell k b.1, embSite_mem ell hell k b.1⟩, b.2⟩ := ⟨b, rfl⟩
  simp only [B'']
  rw [dif_pos hex]
  have hc := hex.choose_spec
  have h1 := congrArg (fun c : CoarseBond (scaleUp ell k Lu) (ell ^ k) => c.1.1) hc
  have h2 := congrArg (fun c : CoarseBond (scaleUp ell k Lu) (ell ^ k) => c.2) hc
  simp only at h1 h2
  have : hex.choose = b := Prod.ext (embSite_inj ell hell k h1) h2
  rw [this]

theorem Qs_injective (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (U : LinkCfg (scaleUp ell k Lu)) :
    Function.Injective (ContinuousLinearMap.adjoint (Qclm ell hell k Lu U)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨A, hA⟩ := Qclm_surj ell hell k Lu U x
  have h1 : ⟪Qclm ell hell k Lu U A, x⟫ = ⟪A, ContinuousLinearMap.adjoint (Qclm ell hell k Lu U) x⟫ :=
    (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  rw [hx, hA, inner_zero_right] at h1
  exact inner_self_eq_zero.mp h1

#print axioms Qclm_surj
#print axioms Qs_injective

end AdalyFormal.StatementLane2
