import ZStatementP428
import AdalyFormal.Balaban.IslandBridge

/-!
# NonVacuity -- structural and non-vacuity facts about `StatementP428`.
No `sorry`, no `native_decide`, no axioms.  Nothing here proves the lemma.
-/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.FullReparamC (IsDropped)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg OnLambdaTilde lambdaTilde_nonvacuous)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice staircasePath)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

/-! ## N1 -- the trivial configuration is in the class (no geometry needed) -/

theorem one_perCubeRegular {L : PeriodicLatticeExtent} (ell M f k : ℕ) (hell : 0 < ell)
    (hM : 0 < M) (hf : 10 ≤ f) (S : Tower L) {α₀ η : ℝ} (hα : 0 < α₀) (hη : 0 < η) :
    PerCubeRegular ell M f k S α₀ η (fun _ => 1) := by
  intro sites j _
  have hfpos : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hell' : (0 : ℝ) < ell := by exact_mod_cast hell
  have hσ : 0 < ((ell : ℝ) ^ j * η)⁻¹ := inv_pos.mpr (mul_pos (pow_pos hell' j) hη)
  have hc : 0 < (f : ℝ) * M * α₀ := mul_pos (mul_pos hfpos hMpos) hα
  have hfrob0 : frobNorm (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    simp [frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]
  refine ⟨fun _ => 1, fun _ => 0, ?_, ?_, ?_⟩
  · intro e _
    refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
    · simp [periodicGaugeTransform]
    · rw [hfrob0]; positivity
  · intro μ ν x _ _
    simp only [sub_zero, smul_zero, hfrob0]
    positivity
  · intro ν x _ _
    simp only [add_zero, sub_zero, smul_zero, Finset.sum_const_zero, hfrob0]
    positivity

/-! ## N2 -- the class is gauge-invariant (a property the tree's `GaugeRegular` proxy shares only
for its value clause, and which the global-gauge islands do not use per cube) -/

theorem perCubeRegular_gauge {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} (h : PerCubeRegular ell M f k S α₀ η U)
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PerCubeRegular ell M f k S α₀ η (periodicGaugeTransform γ U) := by
  intro sites j hq
  obtain ⟨g, A, hA, hD, hLap⟩ := h sites j hq
  refine ⟨fun x => g x * (γ x)⁻¹, A, ?_, hD, hLap⟩
  intro e he
  obtain ⟨h1, h2, h3⟩ := hA e he
  refine ⟨h1, ?_, h3⟩
  have hg : periodicGaugeTransform (fun x => g x * (γ x)⁻¹) (periodicGaugeTransform γ U) e
      = periodicGaugeTransform g U e := by
    unfold periodicGaugeTransform
    group
  rw [hg]
  exact h2

/-! ## N3 -- the class is monotone in `α₀` -/

theorem perCubeRegular_mono {L : PeriodicLatticeExtent} {ell M f k : ℕ} (hell : 0 < ell)
    {S : Tower L} {α₀ α₁ η : ℝ} (hη : 0 < η) (hle : α₀ ≤ α₁) {U : LinkCfg L}
    (h : PerCubeRegular ell M f k S α₀ η U) : PerCubeRegular ell M f k S α₁ η U := by
  intro sites j hq
  obtain ⟨g, A, hA, hD, hLap⟩ := h sites j hq
  have hσ : 0 ≤ ((ell : ℝ) ^ j * η)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    exact (inv_pos.mpr (mul_pos (pow_pos this j) hη)).le
  have hc : (0 : ℝ) ≤ (f : ℝ) * M := by positivity
  have key : ∀ n : ℕ, (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ n)
      ≤ (f : ℝ) * M * α₁ * (((ell : ℝ) ^ j * η)⁻¹ ^ n) := by
    intro n
    have := pow_nonneg hσ n
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hle), this,
      mul_nonneg (mul_nonneg hc (sub_nonneg.mpr hle)) this]
  refine ⟨g, A, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, b, c⟩ := hA e he
    exact ⟨a, b, lt_of_lt_of_le c (key 1)⟩
  · intro μ ν x h1 h2
    exact lt_of_lt_of_le (hD μ ν x h1 h2) (key 2)
  · intro ν x h1 h2
    exact lt_of_lt_of_le (hLap ν x h1 h2) (key 3)

/-! ## N4 -- a concrete, non-degenerate instance of every hypothesis (tower height `k = 0`) -/

/-- The torus with 10 sites per direction. -/
def L10 : PeriodicLatticeExtent := fun _ => 9

/-- `Ω₀ = everything`, `Ω_j = ∅` for `j ≥ 1`. -/
def S0 : Tower L10 := ⟨fun j => if j = 0 then Set.univ else ∅⟩

/-- **r5 (2) control.** The r2..r4 `k = 0` point `Ω₀ = everything` is NOT admissible any more: at `k = 0`, `Ω₁ = ∅`, and the
printed collar law (CMP99b p.396: `Ω₀` = blocks within `RM` of `Ω₁`) forces `Ω₀ = ∅`.  (Under the r2..r4 guarded definition this was
`S0_admissible`, the basis of every `k = 0` closed point.) -/
theorem S0_not_admissible (R : ℕ) : ¬ Admissible 2 1 R 0 S0 := by
  intro h
  obtain ⟨-, hv, -, -, -, hc⟩ := h
  let x : PeriodicLatticeSite L10 := fun _ => 0
  have hx : x ∈ S0.Om 0 := by simp [S0]
  obtain ⟨y, hy, -⟩ := (hc x).mp hx
  have := hv 1 (by omega)
  rw [this] at hy
  exact hy

/-- A genuine class cube: the whole 10-site torus as one box of side `f · M · ell^0 = 10`. -/
theorem S0_classCube :
    ∃ (sites : Set (PeriodicLatticeSite L10)) (j : ℕ), IsClassCube 2 1 10 0 S0 sites j := by
  refine ⟨siteBox (fun _ => 0) 10, 0, ?_, ?_⟩
  · refine ⟨le_refl 0, ⟨fun _ => 0, ?_, ?_⟩, ?_, ?_⟩
    · intro μ; simp [bigSide]
    · simp [bigSide]
    · intro x _
      left
      simp [towerBj, S0]
    · refine ⟨fun _ => 0, ?_, ?_⟩
      · intro μ
        simp [L10]
      · simp [towerBj, S0]
  · intro i hi
    exact Nat.le_zero.mp hi.1

theorem lambdaUniv_ok (R : ℕ) : LambdaOK (Lu := L10) (Lf := L10) 2 1 R 0 S0 Set.univ := by
  refine ⟨?_, fun y => y, ?_, ?_, ?_⟩
  · intro x _ y _; exact Set.mem_univ y
  · intro y μ; simp
  · intro y _; simp [S0]
  · intro y _ y' hy'
    simp [S0] at hy'

theorem onLambdaTildeIn_univ {Lu : PeriodicLatticeExtent} (ell : ℕ) (B : Bond Lu → SuTwo) :
    OnLambdaTildeIn Set.univ ell B ↔ OnLambdaTilde ell B := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy x hx b hb => h1 y ⟨hy, fun _ _ => trivial⟩ x hx b hb, fun b hb => ?_⟩
    obtain ⟨c, hc⟩ := hb
    exact h2 b ⟨c, Or.inl ⟨c.1.2, fun _ _ => trivial⟩, hc⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy x hx b hb => h1 y hy.1 x hx b hb, fun b hb => ?_⟩
    obtain ⟨c, _, hc⟩ := hb
    exact h2 b ⟨c, hc⟩

/-! ## N5 -- the claim is satisfiable AND discriminating: a family for which it holds, and two for
which it fails, with ALL hypotheses of `CoercCore` jointly satisfiable (so failure is not vacuous). -/

/-- `Q = Q* = G₁ = id`, `a = 0`, `H₁ = 0`, `J = 0`, `Q₁ = 0`, `C = id`: `Δ_k = ‖·‖²`. -/
noncomputable def goodIngr (ell : ℕ) (Lu : PeriodicLatticeExtent)
    (Lam : Set (PeriodicLatticeSite Lu)) : Ingr ell Lu Lu Lam where
  Q := ContinuousLinearMap.id ℝ _
  Qs := ContinuousLinearMap.id ℝ _
  G1 := ContinuousLinearMap.id ℝ _
  a := 0
  H1 := 0
  D2 := fun _ => 0
  J := 0
  Q1 := 0
  C := LinearMap.id
  Qs_adj := by intro x y; simp
  D2_quad := by intro c B; simp
  QGQ_unit := by
    show IsUnit ((1 : BondFnL2 Lu →L[ℝ] BondFnL2 Lu) * 1 * 1)
    simp
  C_id := fun _ _ _ => rfl
  C_ker := fun B _ _ c _ => by simp

/-- Same but `a = 1`: `Δ_k ≡ 0`, the all-kernel operator. -/
noncomputable def zeroIngr (ell : ℕ) (Lu : PeriodicLatticeExtent)
    (Lam : Set (PeriodicLatticeSite Lu)) : Ingr ell Lu Lu Lam :=
  { goodIngr ell Lu Lam with a := 1 }

/-- Same but `a = 1000`: `Δ_k = -999‖·‖²`, negative definite. -/
noncomputable def negIngr (ell : ℕ) (Lu : PeriodicLatticeExtent)
    (Lam : Set (PeriodicLatticeSite Lu)) : Ingr ell Lu Lu Lam :=
  { goodIngr ell Lu Lam with a := 1000 }

theorem inverse_id (Lu : PeriodicLatticeExtent) :
    Ring.inverse (ContinuousLinearMap.id ℝ (BondFnL2 Lu)) = ContinuousLinearMap.id ℝ (BondFnL2 Lu) :=
  Ring.inverse_one _

theorem form_good (ell : ℕ) (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu))
    (B : BondFnL2 Lu) :
    (goodIngr ell Lu Lam).form B = ‖B‖ ^ 2 := by
  simp only [Ingr.form, goodIngr, ContinuousLinearMap.comp_id, inverse_id, ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq, zero_mul, sub_zero, zero_apply, inner_zero_left,
    inner_zero_right, mul_zero]

theorem form_scaled (ell : ℕ) (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu))
    (c : ℝ) (B : BondFnL2 Lu) :
    ({ goodIngr ell Lu Lam with a := c } : Ingr ell Lu Lu Lam).form B = (1 - c) * ‖B‖ ^ 2 := by
  simp only [Ingr.form, goodIngr, ContinuousLinearMap.comp_id, inverse_id, ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq, zero_apply, inner_zero_left, inner_zero_right,
    mul_zero, sub_zero]
  ring

/- (r5: `coercCore_good`, `hyps_satisfiable`, `coercCore_fails_of_neg` removed -- their witness is the `k = 0` point `S0`, outside the printed range.) -/
theorem torusOK_L10 : TorusOK 2 1 L10 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro μ <;> simp [L10]

#print axioms one_perCubeRegular
#print axioms perCubeRegular_gauge
#print axioms perCubeRegular_mono
#print axioms S0_not_admissible
#print axioms S0_classCube
#print axioms lambdaUniv_ok

end AdalyFormal.StatementLane
