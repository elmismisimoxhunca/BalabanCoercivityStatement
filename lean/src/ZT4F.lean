import ZXG3F
import ZT4A

/-!
# G4F -- (R3) the two `Ring.inverse` guards.  `Gp` (the print's `G' = (Δ'_a|Ω₀)⁻¹`) and the base `H = G Q* (Q G Q*)⁻¹`
(with `G = (G⁻¹)⁻¹`) are built with `Ring.inverse`, which is `0` off units.  `GenP.WellDefG` adds the three
units to the feasibility conjunct, and `GenP.Gp_genuine` / `GenP.QGQs_genuine` show that under them the junk
value is not used.  At the flat single-level point all three units are PROVED (`P1_guards`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

namespace GenP

theorem WellDefG.toWellDef {P : IngrBParams} (h : WellDefG P) : WellDef P := h.1

/-- under the guard, `G'` IS the inverse of `Δ'_a|Ω₀` on `L²(Ω₀)` (not the junk `0`) -/
theorem Gp_genuine (P : IngrBParams) (h : GuardsUnit P) (f : SiteL2 (scaleUp P.ell P.k P.Lu)) :
    siteMask P.G.Om0 (Gp P.G P.U P.a f) = Gp P.G P.U P.a f ∧
      DelpA P.G P.U P.a (Gp P.G P.U P.a f) = siteMask P.G.Om0 f :=
  Gp_spec P.G P.U P.a h.1 f

/-- under the guard, `G` is a genuine two-sided inverse of `G⁻¹` -/
theorem G_genuine (P : IngrBParams) (h : GuardsUnit P) :
    P.data.Ginv.comp P.data.G = 1 ∧ P.data.G.comp P.data.Ginv = 1 := by
  obtain ⟨u, hu⟩ := h.2.1
  have hG : P.data.G = ↑u⁻¹ := by
    unfold BaseDataS.G; rw [← hu, Ring.inverse_unit]
  rw [hG, ← hu]
  exact ⟨u.mul_inv, u.inv_mul⟩

/-- under the guard, `(Q G Q*)·Ring.inverse(Q G Q*) = 1`: the junk `0` of `H` is not used -/
theorem QGQs_genuine (P : IngrBParams) (h : GuardsUnit P) :
    ((P.data.Q.comp P.data.G).comp P.data.Qs).comp
      (Ring.inverse ((P.data.Q.comp P.data.G).comp P.data.Qs)) = 1 :=
  Ring.mul_inverse_cancel _ h.2.2

end GenP

section
variable {L : PeriodicLatticeExtent}

open Classical in
theorem qpa_inner_k0 (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hk : G.k = 0) (g : SiteL2 L) :
    ⟪g, Qpa G U a g⟫ = a * ∑ y : PeriodicLatticeSite L, if y ∈ G.Lam 0 then ‖g y‖ ^ 2 else 0 := by
  rw [inner_Qpa, hk]
  simp only [zero_add, Finset.range_one, Finset.sum_singleton]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hy : y ∈ G.Lam 0
  · rw [if_pos hy, if_pos hy]
    have hq : Qlev G U 0 y g = g y := by
      rw [Qlev_apply]; rfl
    rw [hq]
    have : ajSeq a G.ell 0 = a := by simp [ajSeq]
    rw [this]
    simp
  · rw [if_neg hy, if_neg hy]; simp

/-- coercivity of the padded Dirichlet operator at a single-level tower (`k = 0`, `Λ₀ = Ω₀`), ANY `U`. -/
theorem delp_coercive_k0 (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hk : G.k = 0)
    (hLam : G.Lam 0 = G.Om0) (f : SiteL2 L) :
    min a 1 * ‖f‖ ^ 2 ≤ ⟪f, (DelpA G U a + (1 - siteMask G.Om0)) f⟫ := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : SiteL2 L →L[ℝ] SiteL2 L, m = siteMask G.Om0 := ⟨_, rfl⟩
  have hsym : ∀ x y, ⟪m x, y⟫ = ⟪x, m y⟫ := by rw [hm]; exact siteMask_symm _
  have hid : ∀ x, m (m x) = m x := by rw [hm]; exact siteMask_idem _
  have e1 : ⟪f, m f⟫ = ‖m f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hsym, hid, real_inner_comm]
  have hq : 0 ≤ ‖f‖ ^ 2 - ‖m f‖ ^ 2 := by
    have h2 : ⟪f - m f, f - m f⟫ = ‖f‖ ^ 2 - ‖m f‖ ^ 2 := by
      have e2 : ⟪m f, f⟫ = ‖m f‖ ^ 2 := by rw [real_inner_comm]; exact e1
      have e3 : ⟪m f, m f⟫ = ‖m f‖ ^ 2 := real_inner_self_eq_norm_sq _
      simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
      rw [e1, e2]; ring
    rw [← h2]; exact real_inner_self_nonneg
  have hD : ⟪f, DelpA G U a f⟫ ≥ a * ‖m f‖ ^ 2 := by
    have hexp : ⟪f, DelpA G U a f⟫ =
        ⟪m f, lapFull U (m f)⟫ + ⟪m f, Qpa G U a (m f)⟫ := by
      unfold DelpA
      rw [← hm]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
      rw [← hsym f, inner_add_right]
    rw [hexp, inner_lapFull, qpa_inner_k0 G U a hk]
    have hsum : ∑ y : PeriodicLatticeSite L,
        (if y ∈ G.Lam 0 then ‖(m f) y‖ ^ 2 else 0) = ‖m f‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [hm, siteMask_apply, hLam]
      by_cases hy : y ∈ G.Om0
      · simp [hy]
      · simp [hy]
    rw [hsum]
    have := sq_nonneg ‖gradL2 U (m f)‖
    linarith
  have hpad : ⟪f, (1 - m) f⟫ = ‖f‖ ^ 2 - ‖m f‖ ^ 2 := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
      real_inner_self_eq_norm_sq, e1]
  have hpad' : ⟪f, (1 - siteMask G.Om0) f⟫ = ‖f‖ ^ 2 - ‖m f‖ ^ 2 := by rw [← hm]; exact hpad
  simp only [ContinuousLinearMap.add_apply, inner_add_right]
  rw [hpad']
  have h1 : min a 1 ≤ a := min_le_left _ _
  have h2 : min a 1 ≤ 1 := min_le_right _ _
  have h3 : 0 ≤ ‖m f‖ ^ 2 := sq_nonneg _
  nlinarith

end

section
variable (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu)) (S : Tower (scaleUp ell 0 Lu)) (hS1 : S.Om 1 = ∅)

local notation "PP" => P1 ell Lu hell a Lam S

include hS1

theorem P1_guards (ha : 0 < a) : GenP.GuardsUnit (PP) := by
  have hco : ∀ x, a * ‖x‖ ^ 2 ≤ ⟪x, (PP).data.Ginv x⟫ :=
    fun x => P1_Ginv_coercive ell Lu hell a Lam S hS1 x
  refine ⟨?_, ?_, ?_⟩
  · have hc : 0 < min a 1 := lt_min ha one_pos
    exact isUnit_of_coercive _ hc (fun x =>
      delp_coercive_k0 (PP).G (PP).U (PP).a rfl (P1_Lam0 ell Lu hell a Lam S hS1) x)
  · exact isUnit_of_coercive _ ha hco
  · exact isUnit_Q_inv_Qs (fun x y => (PP).data.Ginv_symm (PP).data_laws x y) ha hco (PP).data.Q_adj
      (P1_Qs_injective ell Lu hell a Lam S hS1)

end

#print axioms GenP.Gp_genuine
#print axioms GenP.G_genuine
#print axioms GenP.QGQs_genuine
#print axioms qpa_inner_k0
#print axioms delp_coercive_k0
#print axioms P1_guards

end AdalyFormal.StatementLaneG
