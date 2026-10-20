import ZXG3D1

/-!
# G3D2 -- mutants of the genuine (3.156) form: rescaling the first term or the mass term breaks the
proved zero-mode law at the closed point.  No sorry / native_decide / axiom.
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

/-- the genuine form with rescaled first term (`c1`) and mass term (`c2`); `genForm = genFormMut 1 1` -/
noncomputable def genFormMut (P : IngrBParams) (c1 c2 : ℝ) (B : BondFnL2 P.Lu) : ℝ :=
  c1 * GenP.firstTerm P B - c2 * (P.a * ⟪B, B⟫) - 2 * ⟪P.H1in (P.D2in B), P.Jf⟫

theorem genFormMut_one (P : IngrBParams) (B : BondFnL2 P.Lu) :
    genFormMut P 1 1 B = GenP.genForm P B := by
  unfold genFormMut GenP.genForm; ring

/-- on a zero mode of the genuine form (with `J = 0`) the mutant equals `(c1 - c2)·a·⟨B,B⟩` -/
theorem genFormMut_zeroMode (P : IngrBParams) (hJ : P.Jf = 0) (c1 c2 : ℝ) (B : BondFnL2 P.Lu)
    (hz : GenP.genForm P B = 0) : genFormMut P c1 c2 B = (c1 - c2) * (P.a * ⟪B, B⟫) := by
  unfold genFormMut
  unfold GenP.genForm at hz
  rw [hJ, inner_zero_right] at hz ⊢
  have hF : GenP.firstTerm P B = P.a * ⟪B, B⟫ := by linarith
  rw [hF]; ring

/-- a mutant `(c1,c2)` vanishes on a nondegenerate zero mode iff `c1 = c2` -/
theorem mutants_break_abs (P : IngrBParams) (hJ : P.Jf = 0) (B : BondFnL2 P.Lu)
    (hz : GenP.genForm P B = 0) (hpos : 0 < P.a * ⟪B, B⟫) :
    ∀ c1 c2 : ℝ, genFormMut P c1 c2 B = 0 → c1 = c2 := by
  intro c1 c2 hm
  rw [genFormMut_zeroMode P hJ c1 c2 B hz] at hm
  rcases mul_eq_zero.mp hm with h | h
  · linarith
  · exact absurd h hpos.ne'

section
variable (ell : ℕ) (hell : 0 < ell) (a : ℝ)

/-- **MUST-FIRE (2).**  At the closed point there is a nonzero zero mode `B` of the genuine form; the
mutants `(2,1)`, `(1,2)`, `(0,1)`, `(1,0)` of (first term, mass term) all fail to vanish on it while the
genuine `(1,1)` does. -/
theorem mutants_break (ha : 0 < a) :
    ∃ B : BondFnL2 (P0 ell (Ltile ell) hell a Set.univ).Lu,
      genFormMut (P0 ell (Ltile ell) hell a Set.univ) 2 1 B ≠ 0 ∧
      genFormMut (P0 ell (Ltile ell) hell a Set.univ) 1 2 B ≠ 0 ∧
      genFormMut (P0 ell (Ltile ell) hell a Set.univ) 0 1 B ≠ 0 ∧
      genFormMut (P0 ell (Ltile ell) hell a Set.univ) 1 0 B ≠ 0 ∧
      genFormMut (P0 ell (Ltile ell) hell a Set.univ) 1 1 B = 0 := by
  obtain ⟨x, hx, h0⟩ := P0_zeroMode_exists ell hell a ha
  have hn : ‖(P0 ell (Ltile ell) hell a Set.univ).tau ((P0 ell (Ltile ell) hell a Set.univ).data.Q x)‖ ^ 2
      = ‖x‖ ^ 2 := by
    calc _ = ⟪(P0 ell (Ltile ell) hell a Set.univ).tau ((P0 ell (Ltile ell) hell a Set.univ).data.Q x),
          (P0 ell (Ltile ell) hell a Set.univ).tau ((P0 ell (Ltile ell) hell a Set.univ).data.Q x)⟫ :=
          (real_inner_self_eq_norm_sq _).symm
      _ = ⟪(P0 ell (Ltile ell) hell a Set.univ).data.Q x, (P0 ell (Ltile ell) hell a Set.univ).data.Q x⟫ :=
          P0_tau_inner ell (Ltile ell) hell a Set.univ _ _
      _ = ‖(P0 ell (Ltile ell) hell a Set.univ).data.Q x‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = ‖x‖ ^ 2 := P0_Q_norm_sq ell (Ltile ell) hell a Set.univ x
  refine ⟨(P0 ell (Ltile ell) hell a Set.univ).tau ((P0 ell (Ltile ell) hell a Set.univ).data.Q x), ?_⟩
  have hpos : 0 < (P0 ell (Ltile ell) hell a Set.univ).a *
      ⟪(P0 ell (Ltile ell) hell a Set.univ).tau ((P0 ell (Ltile ell) hell a Set.univ).data.Q x),
        (P0 ell (Ltile ell) hell a Set.univ).tau ((P0 ell (Ltile ell) hell a Set.univ).data.Q x)⟫ := by
    rw [real_inner_self_eq_norm_sq, hn]
    exact mul_pos ha hx
  have hb := mutants_break_abs (P0 ell (Ltile ell) hell a Set.univ) (Jf_flat _ rfl) _ h0 hpos
  refine ⟨fun h => by have := hb _ _ h; norm_num at this,
    fun h => by have := hb _ _ h; norm_num at this,
    fun h => by have := hb _ _ h; norm_num at this,
    fun h => by have := hb _ _ h; norm_num at this, ?_⟩
  rw [genFormMut_one]; exact h0
end

#print axioms genFormMut_zeroMode
#print axioms mutants_break_abs
#print axioms mutants_break

end AdalyFormal.StatementLaneG
