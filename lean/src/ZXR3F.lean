import ZXR3E

/-!
# R3F -- MUST-FIRE: `¬ Nonempty (IngrB3 ell hell (goodFam ell hell))`, hence `¬ P428Faithful3` for `goodFam`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane3

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

/-- the repaired headline with the two new laws -/
def P428Faithful3 (ell M R F : ℕ) (I : IngrFamK ell) : Prop :=
  ∃ hell : 0 < ell, Nonempty (IngrB3 ell hell I) ∧ P428Strong ell M R F I

theorem not_IngrB3_goodFam (ell : ℕ) (hell : 0 < ell) : ¬ Nonempty (IngrB3 ell hell (goodFam ell hell)) := by
  rintro ⟨B3⟩
  let Lu : PeriodicLatticeExtent := fun _ => ell - 1
  have hd : ∀ μ : Fin 3, ell ∣ Lu μ + 1 := fun μ => by
    show ell ∣ ell - 1 + 1
    rw [Nat.sub_add_cancel hell]
  let S : Tower (scaleUp ell 0 Lu) := Sk (scaleUp ell 0 Lu) 0
  have hS : S.Om 0 = Set.univ := by simp [S, Sk]
  have hP := B3.dpi_law 0 Lu hd S Set.univ hS
  have hT := B3.t_law 0 Lu hd S (trivialU (scaleUp ell 0 Lu)) Set.univ hS
  exact no_witness ell hell 0 Lu hd Set.univ _ (goodFam ell hell 0 Lu S (trivialU _) Set.univ)
    (goodFam_eq ell hell 0 Lu hd S _ Set.univ) (B3.toB.at_ 0 Lu hd S (trivialU _) Set.univ) hP hT

theorem not_P428Faithful3_goodFam (ell M R F : ℕ) (hell : 0 < ell) :
    ¬ P428Faithful3 ell M R F (goodFam ell hell) := by
  rintro ⟨_, hB, _⟩
  exact not_IngrB3_goodFam ell hell hB

#print axioms not_IngrB3_goodFam
#print axioms not_P428Faithful3_goodFam

end AdalyFormal.StatementLane3
