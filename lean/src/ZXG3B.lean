import ZXG3A
import ZR2B1
import ZR6A

/-!
# G3B -- NON-VACUITY of `P428Genuine` at `k = 0`, flat background, full tower:
(i) every hypothesis of `CoercGenAt` is satisfiable there (with a nonzero `B̃`);
(ii) the CONJUNCT `WellDef` (hb, hG, hN) is PROVED there (this is `IngrB0`'s content, re-assembled for
     the (3.155)-faithful `Nmat` on the multi-level constraint space).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- a symmetric-form coercive operator on a finite-dimensional real inner-product space is a unit -/
theorem isUnit_of_coercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, M x⟫) : IsUnit M := by
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have := h x
    rw [hx, inner_zero_right] at this
    have h0 : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : E →ₗ[ℝ] E))).mp hinj⟩

section
variable (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

/-- **`WellDef` at the closed point** (`k = 0`, flat, full tower, `0 < a`, `ell ∣ Lu μ + 1`). -/
theorem P0_wellDef (hdvd : ∀ μ, ell ∣ (Lu μ + 1)) (ha : 0 < a) :
    GenP.WellDef (P0 ell Lu hell a Lam) := by
  have hco : ∀ x, a * ‖x‖ ^ 2 ≤ ⟪x, (P0 ell Lu hell a Lam).data.Ginv x⟫ :=
    fun x => P0_Ginv_coercive ell Lu hell a Lam x
  have hε : ‖(P0 ell Lu hell a Lam).data.Delta2 (P0 ell Lu hell a Lam).data_laws‖ ≤ 0 := by
    rw [P0_Delta2_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero
  have hG := (P0 ell Lu hell a Lam).G1inv_spec
  have hco1 := (P0 ell Lu hell a Lam).data.G1inv_coercive (P0 ell Lu hell a Lam).data_laws hG hco hε
  refine ⟨P0_hb ell Lu hell a Lam hdvd, ?_, ?_⟩
  · exact isUnit_of_coercive _ ha (fun x => by simpa using hco1 x)
  · exact (P0 ell Lu hell a Lam).data.QG1Qs_isUnit_of_small (P0 ell Lu hell a Lam).data_laws hG
      (c := a) (ε := 0) ha hco hε (P0_Qs_injective ell Lu hell a Lam)
end

theorem fullTower_eq_Sk (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    fullTower ell k Lu = ⟨fun j => if j ≤ k then Set.univ else ∅⟩ := rfl

theorem flat_perCubeRegular2c (c k : ℕ) (hc : 10 ≤ c) {α₀ : ℝ} (hα : 0 < α₀) {L : PeriodicLatticeExtent}
    (S : Tower L) :
    PerCubeRegular2 2 1 c k S α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹ (flatCfg : LinkCfg L) := by
  have h := ufield_perCubeRegular2 (L := L) (ell := 2) (M := 1) (f := c) (k := k) (by norm_num)
    (by norm_num) hc S hα (fun _ => 0) (fun e => by simp; positivity)
  have hU : Ufield (((2 : ℕ) : ℝ) ^ k)⁻¹ (fun _ : Bond L => (0 : ℝ)) = (flatCfg : LinkCfg L) := by
    funext e
    simp [Ufield, flatCfg, Ug_zero]
  rw [hU] at h
  exact h

theorem flat_perCubeRegularMix (F k : ℕ) {α₀ : ℝ} (hα : 0 < α₀) {L : PeriodicLatticeExtent}
    (S : Tower L) :
    PerCubeRegularMix 2 1 F k S α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹ (flatCfg : LinkCfg L) :=
  fun f hf1 _ => flat_perCubeRegular2c f k hf1 hα S

/-- **NON-VACUITY OF THE HYPOTHESES, any `k ≥ 1`** (r5; the `k = 0` point is outside the printed range): at `ell = 2`, `M = 1`, any `R`,
unit torus `L10`, the full tower of height `k`, `Λ = univ`, flat `U` (in the fixed-factor class `c = 12` for every `α₀ > 0`) and
a NONZERO `B̃` in the touching class AND the both-endpoint class.  (The conjunct `WellDef` is NOT part of this statement; it is proved at
this point in `GU1I.PK_wellDef`, ported.) -/
theorem genuine_point_hyps (k : ℕ) (hk : 1 ≤ k) (R : ℕ) {α₀ : ℝ} (hα : 0 < α₀) :
    TorusOK 2 1 L10 ∧
    Admissible 2 1 R k (fullTower 2 k L10) ∧
    CoversOm0p 2 1 12 k (fullTower 2 k L10) ∧
    LambdaOK (Lu := L10) (Lf := scaleUp 2 k L10) 2 1 R k (fullTower 2 k L10) Set.univ ∧
    PerCubeRegular2 2 1 12 k (fullTower 2 k L10) α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹
      (flatCfg : LinkCfg (scaleUp 2 k L10)) ∧
    ∃ Bt : Bond L10 → SuTwo, OnLambdaTildeIn Set.univ 2 Bt ∧ OnLambdaT Set.univ Bt ∧
      OnLambda Set.univ Bt ∧ 0 < bondEnergy Bt := by
  have hf : ∀ μ, scaleUp 2 k L10 μ + 1 = (L10 μ + 1) * 2 ^ k := by
    intro μ
    have : 0 < (L10 μ + 1) * 2 ^ k := Nat.mul_pos (Nat.succ_pos _) (pow_pos (by norm_num) k)
    simp only [scaleUp]
    omega
  have hdiv : ∀ μ : Fin 3, 2 ^ k ∣ scaleUp 2 k L10 μ + 1 := by
    intro μ; rw [hf μ]; exact Dvd.intro_left _ rfl
  have hdvd : ∀ μ : Fin 3, 2 ∣ (L10 μ + 1) := by intro μ; simp [L10]
  obtain ⟨Bt, hBt, hpos⟩ := AdalyFormal.Balaban.CoercUMainDesigned.lambdaTilde_nonvacuous (L := L10) (ell := 2) (by norm_num) hdvd
  refine ⟨torusOK_L10, Sk_admissible k R hk hdiv, ?_, Sk_lambdaOK k R hf,
    flat_perCubeRegular2c 12 k (by norm_num) hα _, Bt,
    (onLambdaTildeIn_univ 2 Bt).mpr hBt, ?_, ?_, hpos⟩
  · refine SkG_coversp 2 1 k 12 (by norm_num) (by norm_num) (by norm_num) (fun μ => ?_)
    rw [hf μ]
    have h1 : 0 < 2 ^ k := pow_pos (by norm_num) k
    simp only [L10]; nlinarith
  · intro b hb; exact absurd (Or.inl (Set.mem_univ _)) hb
  · intro b hb; exact absurd ⟨Set.mem_univ _, Set.mem_univ _⟩ hb

#print axioms isUnit_of_coercive
#print axioms P0_wellDef
#print axioms flat_perCubeRegular2c
#print axioms flat_perCubeRegularMix
#print axioms genuine_point_hyps

end AdalyFormal.StatementLaneG
