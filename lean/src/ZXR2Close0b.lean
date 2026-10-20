import ZXR2Close0a

/-!
# R2Close0b -- `k = 0`, flat background, full tower: the whole `IngrB_genuine` is a CLOSED term
(`hb` and `hunit` both proved, `a > 0` the only hypothesis).  `k = 0` is degenerate (fine lattice =
unit lattice, `Q_0 = id`); it is a non-vacuity witness for the construction, not a multi-scale case.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.StatementLane (scaleUp Tower)

/-- the `k = 0`, flat, full-tower parameters. -/
def P0 (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) : IngrBParams :=
  ⟨ell, 0, Lu, hell, fullTower ell 0 Lu, flatCfg, a, Lam⟩

section
variable (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

theorem P0_Om0 : (P0 ell Lu hell a Lam).G.Om0 = Set.univ := by
  simp [P0, IngrBParams.G, geomOf, fullTower]

theorem P0_Lam0 : (P0 ell Lu hell a Lam).G.Lam 0 = Set.univ := by
  ext x
  show x ∈ (geomOf ell 0 (fullTower ell 0 Lu)).Lam 0 ↔ _
  simp [geomOf, fullTower]
  exact Set.mem_univ _

theorem P0_bondsLam0 (b : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell 0 Lu)) :
    b ∈ bondsLam (P0 ell Lu hell a Lam).G 0 := by
  have h := P0_Lam0 ell Lu hell a Lam
  have hk : (P0 ell Lu hell a Lam).G.k = 0 := rfl
  exact ⟨Or.inl (by rw [h]; exact Set.mem_univ _), fun hh => hh.elim (not_OmGe_of_lt (by omega) _) (not_OmGe_of_lt (by omega) _)⟩

theorem P0_bondSupp_top : bondSupp (P0 ell Lu hell a Lam).G = ⊤ := by
  refine top_unique (fun A _ => ?_)
  intro b hb
  exact absurd (by
    have h := P0_Om0 ell Lu hell a Lam
    unfold bondsOm0
    rw [h]; exact Or.inl (Set.mem_univ _)) hb

/-- `BIdx ≃ Bond` at `k = 0`. -/
noncomputable def idx0 : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell 0 Lu) ≃
    BIdx (P0 ell Lu hell a Lam).G where
  toFun b := ⟨⟨0, by simp [P0]⟩, ⟨b, P0_bondsLam0 ell Lu hell a Lam b⟩⟩
  invFun p := p.2.1
  left_inv b := rfl
  right_inv p := by
    obtain ⟨⟨j, hj⟩, ⟨b, hb⟩⟩ := p
    have hj1 : j < 1 := hj
    have hj0 : j = 0 := by omega
    subst hj0
    rfl

end

end AdalyFormal.IngredientFamilyR2
