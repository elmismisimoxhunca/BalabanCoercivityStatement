import AdalyFormal.Balaban.QOne
import ZStatementP428

/-!
# IngredientQ1 -- `Q₁` of CMP99b (3.155)/(3.156) on the SU(2)-valued carriers of `StatementP428`

Printed definition (image-read this lane, corpus/renders/CMP96_p245-23.png, eq. (2.125), printed p.245):
  `|(Q₁B)(c)|² = | Σ_{x∈B(c₋)} L^{-(d+1)} B([x,x+Le_μ]) |²`,  c = ⟨c₋,c₋+Le_μ⟩;
and CMP95 p.20 (corpus/renders/CMP95_p20-04.png) eq. (1.18):
  `(Q_kA)_b = Σ_{x∈B^k(b₋)} η^{d+1} A([x,x(b)])`.
`B([x,x+Le_μ])` (long bond) is read as the sum of the `ell` unit-bond values along the segment
(`QOne.longBondValue`; consistency with the printed expanded tent formula was checked in QOne).
CMP99b does not restate the formula; p.428 only uses `Q₁B=0`.
Here the SAME formula acts fibrewise on `SuTwo`-valued fields (the real-linear average needs no
transport).  d = 3.  Nothing is proved about coercivity.
-/
set_option autoImplicit false
namespace AdalyFormal.IngredientFamily

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (pathSite qOnePathSum)

/-- `(Q₁A)(c) = ell^{-4} Σ_{x∈B(c₋)} Σ_{i<ell} A(x+i e_μ, μ)`, `SuTwo`-valued. -/
noncomputable def q1SU2 {Lu : PeriodicLatticeExtent} (ell : ℕ) :
    (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo) where
  toFun A b := (1 / (ell : ℝ) ^ 4) •
    ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell, A (pathSite x b.2 i, b.2)
  map_add' A B := by
    funext b
    simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add]
  map_smul' c A := by
    funext b
    simp only [Pi.smul_apply, RingHom.id_apply, ← Finset.smul_sum]
    rw [smul_comm]

theorem q1SU2_apply {Lu : PeriodicLatticeExtent} (ell : ℕ) (A : Bond Lu → SuTwo)
    (b : CoarseBond Lu ell) :
    q1SU2 ell A b = (1 / (ell : ℝ) ^ 4) •
      ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell, A (pathSite x b.2 i, b.2) := rfl

/-- Tie to the tree's scalar `Q₁`: on fields of the form `r(e)·X` the SU(2) average is the
scalar average times `X`. -/
theorem q1SU2_scalar_smul {Lu : PeriodicLatticeExtent} (ell : ℕ) (r : Bond Lu → ℝ) (X : SuTwo)
    (b : CoarseBond Lu ell) :
    q1SU2 ell (fun e => r e • X) b = qOnePathSum ell r b • X := by
  rw [q1SU2_apply]
  simp only [qOnePathSum, AdalyFormal.Balaban.QOne.longBondValue]
  simp only [← Finset.sum_smul, smul_smul]

/-- Tie in the other direction: every real linear functional commutes with the average. -/
theorem q1SU2_functional {Lu : PeriodicLatticeExtent} (ell : ℕ) (φ : SuTwo →ₗ[ℝ] ℝ)
    (A : Bond Lu → SuTwo) (b : CoarseBond Lu ell) :
    φ (q1SU2 ell A b) = qOnePathSum ell (fun e => φ (A e)) b := by
  rw [q1SU2_apply]
  simp only [qOnePathSum, AdalyFormal.Balaban.QOne.longBondValue, map_smul, map_sum, smul_eq_mul]

open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessEll)
open AdalyFormal.Balaban.QOne (checkerConfig d4Config targetCoarseBond)

/-- L7 witness (kernel side): a nonzero SU(2)-valued field in `ker Q₁` on the tree's witness lattice. -/
theorem q1SU2_ker_ne_bot (X : SuTwo) (hX : X ≠ 0) :
    ∃ A : Bond witnessL → SuTwo, A ≠ 0 ∧ q1SU2 witnessEll A = 0 := by
  refine ⟨fun e => checkerConfig e • X, ?_, ?_⟩
  · intro h
    obtain ⟨e, he⟩ : ∃ e, checkerConfig e ≠ 0 := by
      by_contra hc
      push Not at hc
      exact AdalyFormal.Balaban.QOne.checkerConfig_ne_zero (funext hc)
    have := congrFun h e
    simp only [Pi.zero_apply, smul_eq_zero] at this
    rcases this with h1 | h1
    · exact he h1
    · exact hX h1
  · funext b
    rw [q1SU2_scalar_smul, AdalyFormal.Balaban.QOne.qOnePathSum_checkerConfig_eq_zero]
    simp

/-- L7 witness (image side): `Q₁` is not zero. -/
theorem q1SU2_ne_zero (X : SuTwo) (hX : X ≠ 0) :
    ∃ A : Bond witnessL → SuTwo, q1SU2 witnessEll A ≠ 0 := by
  refine ⟨fun e => d4Config e • X, ?_⟩
  intro h
  have := congrFun h targetCoarseBond
  rw [q1SU2_scalar_smul, AdalyFormal.Balaban.QOne.qOnePathSum_d4Config] at this
  simp only [Pi.zero_apply, smul_eq_zero] at this
  rcases this with h1 | h1
  · norm_num at h1
  · exact hX h1

#print axioms q1SU2
#print axioms q1SU2_scalar_smul
#print axioms q1SU2_functional
#print axioms q1SU2_ker_ne_bot
#print axioms q1SU2_ne_zero

end AdalyFormal.IngredientFamily
