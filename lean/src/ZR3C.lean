import ZR3B

/-!
# R3C -- `P428Strong ell M R F (goodFam ell hell)` IS PROVABLE (for every `ell ≥ 2`, `M > 0`,
`10 ≤ F`, `F + 2 ≤ R`), with `a₀ = 1`, `γ₀ = 1`.

Hypotheses of `CoercAt2` actually used: `TorusOK` (first conjunct, `ell ∣ Lu μ + 1`) and the
dropped-bond clause of `OnLambdaTildeIn`.  NOT used: `Admissible`, `CoversOm0`, `LambdaOK`,
`PerCubeRegularMix` (the per-cube class), `OnLambdaT`, the smallness `F M α₀ ≤ a₀`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane3

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.IngredientFamily (D2unit)
open scoped RealInnerProductSpace

section
variable (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
  (U : LinkCfg (scaleUp ell k Lu)) (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1)
  (Lam : Set (PeriodicLatticeSite Lu))

theorem goodBase_Ginv : (goodBase ell hell k Lu U).Ginv =
    (1 : BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu)) +
      (ContinuousLinearMap.adjoint (Qclm ell hell k Lu U)).comp (Qclm ell hell k Lu U) := by
  ext y : 1
  simp [AdalyFormal.IngredientFamily.BaseData.Ginv, goodBase]

/-- the (3.156)-form of `goodIngr'` is bounded below by `‖v‖²` (this is the whole content) -/
theorem goodIngr'_form_ge (v : BondFnL2 Lu) :
    ‖v‖ ^ 2 ≤ (goodIngr' ell hell k Lu U hd Lam).form v := by
  have hS := goodBase_unit ell hell k Lu U
  rw [goodBase_Ginv] at hS
  have hc := form_core_coercive (Qclm ell hell k Lu U) (fun x => Qclm_norm_le ell hell k Lu U x) hS v
  have h0 : (goodIngr' ell hell k Lu U hd Lam).D2 v = 0 := by
    simp [goodIngr', D2unit]
  unfold Ingr.form
  rw [h0]
  simp only [map_zero, inner_zero_left, mul_zero, sub_zero]
  have e1 : (goodIngr' ell hell k Lu U hd Lam).a = 1 := rfl
  rw [e1, one_mul]
  have e2 : Ring.inverse (((goodIngr' ell hell k Lu U hd Lam).Q.comp
      (goodIngr' ell hell k Lu U hd Lam).G1).comp (goodIngr' ell hell k Lu U hd Lam).Qs)
      = Ring.inverse ((Qclm ell hell k Lu U).comp (Ring.inverse ((1 : BondFnL2 (scaleUp ell k Lu) →L[ℝ]
        BondFnL2 (scaleUp ell k Lu)) + (ContinuousLinearMap.adjoint (Qclm ell hell k Lu U)).comp
          (Qclm ell hell k Lu U)))
        |>.comp (ContinuousLinearMap.adjoint (Qclm ell hell k Lu U))) := by
    simp only [goodIngr', goodBase_Ginv ell hell k Lu U]
  rw [e2]
  exact hc

end

theorem goodIngr'_coerc (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (U : LinkCfg (scaleUp ell k Lu)) (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (Bt : Bond Lu → SuTwo)
    (hBt : OnLambdaTildeIn Lam ell Bt) :
    1 * bondEnergy Bt ≤ (goodIngr' ell hell k Lu U hd Lam).form
      (WithLp.toLp 2 ((goodIngr' ell hell k Lu U hd Lam).C Bt)) := by
  refine le_trans ?_ (goodIngr'_form_ge ell hell k Lu U hd Lam _)
  rw [PiLp.norm_sq_eq_of_L2, one_mul]
  unfold bondEnergy
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases h : IsDroppedIn Lam ell b
  · rw [hBt.2 b h]; simp
  · have : (goodIngr' ell hell k Lu U hd Lam).C Bt b = Bt b := Clam_id Lam _ Bt b h
    simp only [WithLp.ofLp_toLp, this]
    exact le_refl _

/-- **THE QUESTION, ANSWERED.**  `P428Strong` holds for `goodFam` (given the statement parameters). -/
theorem P428Strong_goodFam (ell M R F : ℕ) (hell : 0 < ell)
    (hp : 2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R) :
    P428Strong ell M R F (goodFam ell hell) := by
  refine ⟨hp, 1, one_pos, 1, one_pos, ?_⟩
  intro k Lu α₀ _ _ hT S _ _ Lam _ U _ Bt hBt _
  rw [goodFam_eq ell hell k Lu hT.1 S U Lam]
  exact goodIngr'_coerc ell hell k Lu U hT.1 Lam Bt hBt

/-- hence `P428Faithful2` holds for `goodFam`: it is only as discriminating as `IngrB` -/
theorem P428Faithful2_goodFam (ell M R F : ℕ) (hell : 0 < ell)
    (hp : 2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R) :
    P428Faithful2 ell M R F (goodFam ell hell) :=
  ⟨hell, IngrB_nonempty ell hell, P428Strong_goodFam ell M R F hell hp⟩

#print axioms goodIngr'_form_ge
#print axioms P428Strong_goodFam
#print axioms P428Faithful2_goodFam

end AdalyFormal.StatementLane3
