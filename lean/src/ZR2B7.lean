import ZR2B6

/-!
# R2B7 -- hypotheses of `CoercAt2` are jointly satisfiable on a PROPER tower with a NON-FLAT `U`
(k = 0, ell = 2, M = 1, F = 10, R = 12 = F + 2, 60-site torus, Ω₀ = {x₀ < 40}); and the matching
MUST-FIRE facts on the same geometry.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice staircasePath)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

def Lam20 (Lu : PeriodicLatticeExtent) : Set (PeriodicLatticeSite Lu) := {y | (y 0).val = 20}

theorem pcd_far (N a b : ℕ) (hN : N = 60) (ha : a = 20) (hb : 40 ≤ b) (hb2 : b < 60) :
    12 < pcd N a b := by
  subst hN; subst ha
  unfold pcd
  split_ifs <;> omega

/- (r5: `Lam20_ok` and `proper_tower_satisfiable` removed: they live on the `k = 0` tower `T40`, not admissible under r5 (2).) -/

theorem torusOK_60 {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) : TorusOK 2 1 Lu := by
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;> rw [hLu μ] <;> norm_num

theorem LamPrime_Lam20_empty {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60)
    (y : PeriodicLatticeSite Lu) : y ∉ LamPrime 2 (Lam20 Lu) := by
  rintro ⟨hy, hblk⟩
  have hmod : (y 0).val % 2 = 0 := (AdalyFormal.Balaban.AdmissibleSubspace.mem_CoarseLattice.mp hy) 0
  have hlt : (y 0).val < 60 := by have := (y 0).isLt; have := hLu 0; omega
  have hlt1 : (y 0).val + 1 < Lu 0 + 1 := by have := hLu 0; omega
  have hself : y ∈ blockOf y 2 := by
    rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf]
    intro μ; omega
  have hx : Function.update y 0 ⟨(y 0).val + 1, hlt1⟩ ∈ blockOf y 2 := by
    rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf]
    intro μ
    by_cases h : μ = 0
    · subst h; simp
    · rw [Function.update_of_ne h]; omega
  have h1 := hblk y hself
  have h2 := hblk _ hx
  simp only [Lam20, Set.mem_setOf_eq] at h1 h2
  simp at h2
  omega

noncomputable def Bspike (Lu : PeriodicLatticeExtent) (hLu : ∀ μ, Lu μ + 1 = 60) : Bond Lu → SuTwo :=
  fun e => if e = ((fun μ => ⟨20, by have := hLu μ; omega⟩ : PeriodicLatticeSite Lu), (1 : Fin 3))
    then suTwoWitness else 0

theorem Bspike_props {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) :
    OnLambdaTildeIn (Lam20 Lu) 2 (Bspike Lu hLu) ∧ OnLambda (Lam20 Lu) (Bspike Lu hLu) ∧
      OnLambdaT (Lam20 Lu) (Bspike Lu hLu) ∧ 0 < bondEnergy (Bspike Lu hLu) := by
  refine ⟨⟨fun y hy => absurd hy (LamPrime_Lam20_empty hLu y), ?_⟩, ?_, ?_, ?_⟩
  · rintro b ⟨c, hc, _⟩
    exact absurd hc (not_or.mpr ⟨LamPrime_Lam20_empty hLu _, LamPrime_Lam20_empty hLu _⟩)
  · intro b hb
    unfold Bspike
    rw [if_neg]
    rintro rfl
    apply hb
    refine ⟨?_, ?_⟩
    · show (20 : ℕ) = 20; rfl
    · show ((periodicLatticeShift _ 1) 0).val = 20
      rw [shift_apply]; simp
  · intro b hb
    unfold Bspike
    rw [if_neg]
    rintro rfl
    apply hb
    left; show (20 : ℕ) = 20; rfl
  · unfold bondEnergy
    apply Finset.sum_pos'
    · intro b _; positivity
    · refine ⟨((fun μ => ⟨20, by have := hLu μ; omega⟩ : PeriodicLatticeSite Lu), (1 : Fin 3)),
        Finset.mem_univ _, ?_⟩
      unfold Bspike
      simp only [if_true]
      have := norm_pos_iff.mpr suTwoWitness_ne_zero
      positivity

end AdalyFormal.StatementLane2
