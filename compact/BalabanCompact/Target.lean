import BalabanCompact.Ops2

/-!
# CMP99b p.428, dimension 3, SU(2)

Quantifier order of the frozen headline `AdalyFormal.StatementLaneG.P428Target8`.
-/

set_option autoImplicit false

namespace BalabanCompact

/-- The inequality at one `(S, Λ, U)`: every admissible `B̃` satisfies
`γ₀ ‖B̃‖² ≤ genForm (C B̃)`. -/
noncomputable def InstIneq (ell k : ℕ) (a γ₀ : ℝ) (Lu : Extent) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (Site Lu)) (U : Cfg (scaleUp ell k Lu)) : Prop :=
  ∀ Bt : Bond Lu → Vec, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    γ₀ * bondEnergy Bt ≤
      genForm ⟨ell, k, Lu, S, U, a, Lam⟩ (toField (genC_of ell k Lu S U a Lam Bt))
where
  genC_of (ell k : ℕ) (Lu : Extent) (S : Tower (scaleUp ell k Lu))
      (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (Site Lu)) :
      (Bond Lu → Vec) → Bond Lu → Vec :=
    (Prm.genC ⟨ell, k, Lu, S, U, a, Lam⟩)

/-- Torus, admissible tower, `Λ = B(Λ')`, and one class of cube factor `c`. -/
noncomputable def CoercG8At (ell M R k c : ℕ) (a : ℝ) (Lu : Extent) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ S : Tower (scaleUp ell k Lu), Admissible ell M R k S →
  ∀ Lam : Set (Site Lu), LambdaOK2 ell M R k S Lam →
  ∀ U : Cfg (scaleUp ell k Lu),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k a γ₀ Lu S Lam U

/-- `a₀`, `γ₀` chosen before `k`, the torus and `α₀`, with `c M α₀ ≤ a₀`. -/
noncomputable def P428Core8At (ell M R c : ℕ) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ k : ℕ, 1 ≤ k → ∀ Lu : Extent, ∀ α₀ : ℝ, 0 < α₀ → (c : ℝ) * (M : ℝ) * α₀ ≤ a₀ →
      CoercG8At ell M R k c a Lu α₀ γ₀

/-- Headline constants: cube factor `12`. -/
noncomputable def P428Core8 (ell M R : ℕ) (a : ℝ) : Prop :=
  P428Core8At ell M R 12 a

/-- `ℓ ≥ 2`, `M = ℓ^m` with `m ≥ 1`, `a > 0`. -/
def SidePow (ell M : ℕ) (a : ℝ) : Prop :=
  2 ≤ ell ∧ (∃ m : ℕ, 1 ≤ m ∧ M = ell ^ m) ∧ 0 < a

noncomputable def P428Genuine8 (ell M R : ℕ) (a : ℝ) : Prop :=
  SidePow ell M a ∧ P428Core8 ell M R a

/-- **Headline.** `ℓ ≥ 2` and `a > 0` first; then `m₀` and `R₀`; then `a₀`, `γ₀`
independent of `k ≥ 1`, the torus, `α₀`, the tower, `Λ`, `U` and `B̃`. -/
noncomputable def P428Target8 : Prop :=
  ∀ ell : ℕ, 2 ≤ ell → ∀ a : ℝ, 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8 ell (ell ^ m) R a

end BalabanCompact
