import ZNonVacuity

/-!
# NonVacuity2 -- the hypotheses of `CoercCore` are jointly satisfiable at EVERY tower height `k`
(`ell = 2`, `M = 1`, any `R`), with `Λ_k` = the whole torus, a genuine class cube of index `k`,
`U = 1`, and a `B̃ ≠ 0`.  No `sorry`, no axioms.  Nothing here proves the lemma.
-/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg OnLambdaTilde lambdaTilde_nonvacuous)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- The constant tower: `Ω_j = T` for `j ≤ k`, `∅` above. -/
def Sk (L : PeriodicLatticeExtent) (k : ℕ) : Tower L := ⟨fun j => if j ≤ k then Set.univ else ∅⟩

theorem pdist_self {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) : pdist x x = 0 := by
  unfold pdist pcd
  simp

theorem Sk_admissible {L : PeriodicLatticeExtent} (k R : ℕ) (hk1 : 1 ≤ k) (hdiv : ∀ μ : Fin 3, 2 ^ k ∣ L μ + 1) :
    Admissible 2 1 R k (Sk L k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h : j ≤ k
    · simp [Sk, h]
    · have h2 : ¬ j + 1 ≤ k := by omega
      simp [Sk, h2] at hx
  · intro j hj
    have : ¬ j ≤ k := by omega
    simp [Sk, this]
  · intro j hj μ
    simp only [bigSide, one_mul]
    exact (pow_dvd_pow 2 hj).trans (hdiv μ)
  · intro j hj x _ y _
    simp [Sk, hj]
  · intro j hj x hx
    simp [Sk, hj] at hx
  · intro x
    simp only [Sk, Nat.zero_le, if_true, Set.mem_univ, true_iff]
    refine ⟨x, ?_, x, fun μ => rfl, ?_⟩
    · simp [hk1]
    · rw [pdist_self]; exact Nat.zero_le _

theorem Sk_classCube {L : PeriodicLatticeExtent} (k : ℕ) (hdiv : ∀ μ : Fin 3, 2 ^ k ∣ L μ + 1) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube 2 1 10 k (Sk L k) sites j := by
  have hsz : 0 < 10 * bigSide 1 2 k := by simp [bigSide]
  have hB : ∀ i, i < k → towerBj (Sk L k) i = ∅ := by
    intro i hi
    have h1 : i ≤ k := by omega
    have h2 : i + 1 ≤ k := by omega
    ext x
    simp [towerBj, Sk, h1, h2]
  have hBk : towerBj (Sk L k) k = Set.univ := by
    ext x
    simp [towerBj, Sk]
  have hnon : (siteBox (L := L) (fun μ => ⟨0, Nat.succ_pos _⟩) (10 * bigSide 1 2 k)
      ∩ towerBj (Sk L k) k).Nonempty := by
    refine ⟨fun μ => ⟨0, Nat.succ_pos _⟩, ?_, by rw [hBk]; exact Set.mem_univ _⟩
    intro μ
    have hN : 0 < L μ + 1 := Nat.succ_pos _
    simpa using hsz
  refine ⟨siteBox (fun μ => ⟨0, Nat.succ_pos _⟩) (10 * bigSide 1 2 k), k, ⟨le_refl k, ⟨_, ?_, rfl⟩, ?_, hnon⟩, ?_⟩
  · intro μ; simp
  · intro x _; left; rw [hBk]; exact Set.mem_univ _
  · intro i hi
    by_contra hne
    have hlt : i < k := lt_of_le_of_ne hi.1 hne
    obtain ⟨x, _, hx⟩ := hi.2.2.2
    rw [hB i hlt] at hx
    exact hx

theorem Sk_lambdaOK {Lu Lf : PeriodicLatticeExtent} (k R : ℕ) (hf : ∀ μ, Lf μ + 1 = (Lu μ + 1) * 2 ^ k) :
    LambdaOK (Lu := Lu) (Lf := Lf) 2 1 R k (Sk Lf k) Set.univ := by
  have hemb : ∀ (y : PeriodicLatticeSite Lu) (μ : Fin 3), 2 ^ k * (y μ).val < Lf μ + 1 := by
    intro y μ
    rw [hf μ, mul_comm]
    exact Nat.mul_lt_mul_of_pos_right (y μ).isLt (pow_pos (by norm_num) k)
  refine ⟨?_, fun y μ => ⟨2 ^ k * (y μ).val, hemb y μ⟩, ?_, ?_, ?_⟩
  · intro x _ y _; exact Set.mem_univ y
  · intro y μ; rfl
  · intro y _; simp [Sk]
  · intro y _ y' hy'
    simp [Sk] at hy'

theorem hyps_satisfiable_k (k R : ℕ) (hk1 : 1 ≤ k) (a₀ : ℝ) (ha₀ : 0 < a₀) (Lf : PeriodicLatticeExtent)
    (hLf : Lf = scaleUp 2 k L10) :
    TorusOK 2 1 L10 ∧ ∃ (S : Tower Lf), Admissible 2 1 R k S ∧
    ∃ (Lam : Set (PeriodicLatticeSite L10)), LambdaOK (Lu := L10) (Lf := Lf) 2 1 R k S Lam ∧
    ∃ (f : ℕ), 10 ≤ f ∧
    ∃ (α₀ : ℝ), 0 < α₀ ∧ (f : ℝ) * (1 : ℕ) * α₀ ≤ a₀ ∧
    ∃ (U : LinkCfg Lf), PerCubeRegular 2 1 f k S α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹ U ∧
    ∃ (Bt : Bond L10 → SuTwo), OnLambdaTildeIn Lam 2 Bt ∧ OnLambda Lam Bt ∧ 0 < bondEnergy Bt := by
  have hf : ∀ μ, Lf μ + 1 = (L10 μ + 1) * 2 ^ k := by
    intro μ
    subst hLf
    have : 0 < (L10 μ + 1) * 2 ^ k := Nat.mul_pos (Nat.succ_pos _) (pow_pos (by norm_num) k)
    simp only [scaleUp]
    omega
  have hdiv : ∀ μ : Fin 3, 2 ^ k ∣ Lf μ + 1 := by
    intro μ; rw [hf μ]; exact Dvd.intro_left _ rfl
  have hdvd : ∀ μ : Fin 3, 2 ∣ (L10 μ + 1) := by intro μ; simp [L10]
  obtain ⟨Bt, hBt, hpos⟩ := lambdaTilde_nonvacuous (L := L10) (ell := 2) (by norm_num) hdvd
  have hηpos : 0 < (((2 : ℕ) : ℝ) ^ k)⁻¹ := by positivity
  refine ⟨torusOK_L10, Sk Lf k, Sk_admissible k R hk1 hdiv, Set.univ, Sk_lambdaOK k R hf, 10, le_refl _, a₀ / 10,
    by positivity, ?_, fun _ => 1, ?_, Bt, (onLambdaTildeIn_univ 2 Bt).mpr hBt, ?_, hpos⟩
  · push_cast; nlinarith
  · exact one_perCubeRegular 2 1 10 k (by norm_num) (by norm_num) (le_refl _) _
      (by positivity) hηpos
  · intro b hb; exact absurd ⟨Set.mem_univ _, Set.mem_univ _⟩ hb

#print axioms Sk_admissible
#print axioms Sk_classCube
#print axioms Sk_lambdaOK
#print axioms hyps_satisfiable_k

end AdalyFormal.StatementLane
