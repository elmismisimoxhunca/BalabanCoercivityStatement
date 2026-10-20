import ZR2C4e

/-!
# R2D -- the repaired headline statement `P428Faithful2` and its control theorems.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- **SUPERSEDED (r2 ingredient-family form; r5 statement `P428Genuine5` was superseded by the r6 statement `ZT5A.P428Genuine8`).** THE REPAIRED CLAIM (strong reading).  `ell, M, R, F` are statement parameters
(`2 ≤ ell`, `0 < M`, `10 ≤ F` the cube-size cap, `F + 2 ≤ R`); `I` is an ingredient family IN THE
CLASS `IngrB` (so it is not free data) and satisfies the coercive bound for every `k`, tiled torus,
admissible covered tower, `Λ`, non-flat-allowed `U` in the per-cube class, `B̃ ∈ Λ̃`. -/
def P428Faithful2 (ell M R F : ℕ) (I : IngrFamK ell) : Prop :=
  ∃ hell : 0 < ell, Nonempty (IngrB ell hell I) ∧ P428Strong ell M R F I

/-- printed reading (`γ₀` may depend on the torus, still not on `k`, `U`) -/
def P428Faithful2Print (ell M R F : ℕ) (I : IngrFamK ell) : Prop :=
  ∃ hell : 0 < ell, Nonempty (IngrB ell hell I) ∧ P428Print ell M R F I

theorem P428Faithful2.toPrint {ell M R F : ℕ} {I : IngrFamK ell} (h : P428Faithful2 ell M R F I) :
    P428Faithful2Print ell M R F I := by
  obtain ⟨hell, hB, hS⟩ := h
  exact ⟨hell, hB, hS.toPrint⟩

/-- the class exclusion transfers: a family with `H1 = 0` at a tiled point never satisfies the claim -/
theorem not_P428Faithful2_of_H1_zero {ell M R F : ℕ} (I : IngrFamK ell) (k : ℕ)
    (Lu : PeriodicLatticeExtent) (hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (S U Lam)
    (h0 : (I k Lu S U Lam).H1 = 0) : ¬ P428Faithful2 ell M R F I := by
  rintro ⟨hell, ⟨B⟩, _⟩
  exact (IngrB.not_of_H1_zero (hell := hell) I k Lu hd S U Lam h0).false B

theorem P428Faithful2.pos_params {ell M R F : ℕ} {I : IngrFamK ell} (h : P428Faithful2 ell M R F I) :
    2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R := by
  obtain ⟨_, _, hp, _⟩ := h
  exact hp

/-! ## S83: the touching class strictly contains the both-endpoint class -/

/-- a nonzero `B̃` supported on a BOUNDARY bond of `Λ` (one endpoint inside, one outside): it is in the
touching class `OnLambdaT` (CMP96 p.245 convention) but NOT in r1's `OnLambda`. -/
theorem touching_strictly_larger {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    ∃ B : Bond Lu → SuTwo, OnLambdaT (Lam20 Lu) B ∧ ¬ OnLambda (Lam20 Lu) B ∧
      OnLambdaTildeIn (Lam20 Lu) 2 B ∧ 0 < bondEnergy B := by
  classical
  let p : PeriodicLatticeSite Lu := fun μ => ⟨if μ = 0 then 19 else 20, by
    have := hLu μ; split_ifs <;> omega⟩
  let b0 : Bond Lu := (p, (0 : Fin 3))
  have hb1 : (p 0).val = 19 := by simp [p]
  have hb2 : ((periodicLatticeShift p 0) 0).val = 20 := by
    rw [shift_apply]; simp only [if_true]
    rw [fin_succ_val 0 (by have := hLu 0; omega)]
    have h19 : (p 0).val = 19 := hb1
    rw [h19]
    have := hLu 0
    rw [Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun e => if e = b0 then suTwoWitness else 0, ?_, ?_, ?_, ?_⟩
  · intro b hb
    simp only []
    rw [if_neg]
    rintro rfl
    apply hb
    right
    simp only [Lam20, Set.mem_setOf_eq]
    exact hb2
  · intro h
    have := h b0 |>.mt
    have h2 : (fun e => if e = b0 then suTwoWitness else (0 : SuTwo)) b0 = 0 := by
      apply h b0
      rintro ⟨h1, _⟩
      simp only [Lam20, Set.mem_setOf_eq] at h1
      have : (b0.1 0).val = 19 := hb1
      omega
    simp at h2
    exact suTwoWitness_ne_zero h2
  · refine ⟨fun y hy => absurd hy (LamPrime_Lam20_empty hLu y), ?_⟩
    rintro b ⟨c, hc, _⟩
    exact absurd hc (not_or.mpr ⟨LamPrime_Lam20_empty hLu _, LamPrime_Lam20_empty hLu _⟩)
  · unfold bondEnergy
    apply Finset.sum_pos'
    · intro b _; positivity
    · refine ⟨b0, Finset.mem_univ _, ?_⟩
      simp only [if_true]
      have := norm_pos_iff.mpr suTwoWitness_ne_zero
      positivity

#print axioms P428Faithful2.toPrint
#print axioms not_P428Faithful2_of_H1_zero
#print axioms touching_strictly_larger

end AdalyFormal.StatementLane2
