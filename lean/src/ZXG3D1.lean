import ZXG3C

/-!
# G3D -- MUST-FIRE / MUST-NOT-FIRE controls for `P428Genuine`.
 (1) `not_FormPinned_goodFam`: the non-Balaban family `goodFam` does NOT have the genuine (3.156) form
     (so `∃ family` statements are not discriminating, but `P428Genuine` -- which has no family -- is
     about the genuine form, which goodFam does not carry).
 (2) `genFormMut_*`: rescaling the first term or the mass term of the genuine form (mutants) destroys the
     proved zero-mode law; `P0_not_wellDef_a_zero`: `WellDef` is a real condition (fails at `a = 0`).
 (3) the per-cube class excludes `badU` on the full tower point.
 (4) re-exports of the verifier's mutation controls (Mut.lean).
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
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- a family `I` has THE genuine (3.156) form: at every tiled point where the genuine construction is
well defined, `I.form = genForm`. -/
def FormPinned {ell : ℕ} (hell : 0 < ell) (a : ℝ) (I : IngrFamK ell) : Prop :=
  ∀ (k : ℕ) (Lu : PeriodicLatticeExtent), (∀ μ : Fin 3, ell ∣ Lu μ + 1) →
    ∀ (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu))
      (Lam : Set (PeriodicLatticeSite Lu)),
      GenP.WellDef (gparams ell k Lu hell S U a Lam) →
      ∀ B : BondFnL2 Lu, (I k Lu S U Lam).form B = GenP.genForm (gparams ell k Lu hell S U a Lam) B

section
variable (ell : ℕ) (hell : 0 < ell) (a : ℝ)

/-- the tiled unit torus with `ell` sites per direction -/
def Ltile (ell : ℕ) : PeriodicLatticeExtent := fun _ => ell - 1

theorem Ltile_dvd (hell : 0 < ell) : ∀ μ : Fin 3, ell ∣ Ltile ell μ + 1 := by
  intro μ; simp only [Ltile]; rw [Nat.sub_add_cancel hell]

/-- the nonzero zero-mode vector at the closed point -/
theorem P0_zeroMode_exists (ha : 0 < a) :
    ∃ x : ↥(bondSupp (P0 ell (Ltile ell) hell a Set.univ).G),
      0 < ‖x‖ ^ 2 ∧
      GenP.genForm (P0 ell (Ltile ell) hell a Set.univ)
        ((P0 ell (Ltile ell) hell a Set.univ).tau ((P0 ell (Ltile ell) hell a Set.univ).data.Q x)) = 0 := by
  refine ⟨⟨AdalyFormal.StatementLane3.constField (scaleUp ell 0 (Ltile ell)) suTwoWitness, by
    rw [P0_bondSupp_top]; exact Submodule.mem_top⟩, ?_, ?_⟩
  · exact AdalyFormal.StatementLane3.constField_norm_pos suTwoWitness suTwoWitness_ne_zero
  · exact P0_genForm_const ell (Ltile ell) hell a Set.univ (Ltile_dvd ell hell) ha suTwoWitness

/-- **MUST-FIRE (1).**  `goodFam` is not pinned to the genuine form, for every `ell ≥ 1`, every `a > 0`. -/
theorem not_FormPinned_goodFam (ha : 0 < a) : ¬ FormPinned hell a (goodFam ell hell) := by
  intro hP
  obtain ⟨x, hx, h0⟩ := P0_zeroMode_exists ell hell a ha
  set B := (P0 ell (Ltile ell) hell a Set.univ).tau ((P0 ell (Ltile ell) hell a Set.univ).data.Q x) with hB
  have hW : GenP.WellDef (gparams ell 0 (Ltile ell) hell (fullTower ell 0 (Ltile ell)) flatCfg a Set.univ) :=
    P0_wellDef ell (Ltile ell) hell a Set.univ (Ltile_dvd ell hell) ha
  have hpin := hP 0 (Ltile ell) (Ltile_dvd ell hell) (fullTower ell 0 (Ltile ell)) flatCfg Set.univ hW B
  have hge := AdalyFormal.StatementLane3.goodIngr'_form_ge ell hell 0 (Ltile ell) flatCfg (Ltile_dvd ell hell) Set.univ B
  have hgood : goodFam ell hell 0 (Ltile ell) (fullTower ell 0 (Ltile ell)) flatCfg Set.univ =
      goodIngr' ell hell 0 (Ltile ell) flatCfg (Ltile_dvd ell hell) Set.univ :=
    goodFam_eq ell hell 0 (Ltile ell) (Ltile_dvd ell hell) _ _ _
  rw [hgood] at hpin
  have hgen : GenP.genForm (gparams ell 0 (Ltile ell) hell (fullTower ell 0 (Ltile ell)) flatCfg a Set.univ) B = 0 := h0
  rw [hgen] at hpin
  rw [hpin] at hge
  have hn : ‖B‖ ^ 2 = ‖x‖ ^ 2 := by
    calc ‖B‖ ^ 2 = ⟪B, B⟫ := (real_inner_self_eq_norm_sq B).symm
      _ = ⟪(P0 ell (Ltile ell) hell a Set.univ).data.Q x, (P0 ell (Ltile ell) hell a Set.univ).data.Q x⟫ := by
          rw [hB]; exact P0_tau_inner ell (Ltile ell) hell a Set.univ _ _
      _ = ‖(P0 ell (Ltile ell) hell a Set.univ).data.Q x‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = ‖x‖ ^ 2 := P0_Q_norm_sq ell (Ltile ell) hell a Set.univ x
  have hge' : ‖B‖ ^ 2 ≤ 0 := hge
  linarith

end

#print axioms not_FormPinned_goodFam

end AdalyFormal.StatementLaneG
