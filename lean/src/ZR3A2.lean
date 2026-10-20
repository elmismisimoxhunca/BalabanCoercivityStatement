import ZR3A1

/-!
# R3A2 -- `||Q_k(U)|| <= 1` for the pinned `Qclm` (all `k`, `Lu`, `U`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane3

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.Q1Real (rZeroA)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)

/-- one coarse bond: `||(Q A)_c||^2 <= n^-4 * ∑_{x∈B, i<n} ||A(pathSite x μ i, μ)||^2`, given `|B| = n^3` -/
theorem bond_sq_le {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (n : ℕ) (hn : 0 < n)
    (A : Bond L → SuTwo) (c : CoarseBond L n) (hcard : (blockOf c.1.1 n).card = n ^ 3) :
    ‖lineCoarseRestrictCov U n A c‖ ^ 2 ≤
      (1 / (n : ℝ) ^ 4) * ∑ x ∈ blockOf c.1.1 n, ∑ i ∈ Finset.range n,
        ‖A (pathSite x c.2 i, c.2)‖ ^ 2 := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set a : PeriodicLatticeSite L × ℕ → ℝ := fun s => ‖A (pathSite s.1 c.2 s.2, c.2)‖ with ha
  have h1 : ‖lineCoarseRestrictCov U n A c‖ ≤ (1 / (n : ℝ) ^ 4) *
      ∑ s ∈ (blockOf c.1.1 n) ×ˢ Finset.range n, a s := by
    unfold lineCoarseRestrictCov rZeroA
    rw [norm_smul, Finset.sum_product]
    have hn4 : ‖(1 / (n : ℝ) ^ 4)‖ = 1 / (n : ℝ) ^ 4 := by
      rw [Real.norm_eq_abs, abs_of_nonneg]; positivity
    rw [hn4]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [AdalyFormal.Balaban.FaithfulCoercivitySU2.norm_RMap]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (blockOf c.1.1 n) ×ˢ Finset.range n) (f := a)
  rw [Finset.card_product, Finset.card_range, hcard] at hcs
  have hS : (0 : ℝ) ≤ ∑ s ∈ (blockOf c.1.1 n) ×ˢ Finset.range n, a s :=
    Finset.sum_nonneg fun s _ => norm_nonneg _
  have h2 : ‖lineCoarseRestrictCov U n A c‖ ^ 2 ≤
      ((1 / (n : ℝ) ^ 4) * ∑ s ∈ (blockOf c.1.1 n) ×ˢ Finset.range n, a s) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : ((1 / (n : ℝ) ^ 4) * ∑ s ∈ (blockOf c.1.1 n) ×ˢ Finset.range n, a s) ^ 2
      = (1 / (n : ℝ) ^ 8) * (∑ s ∈ (blockOf c.1.1 n) ×ˢ Finset.range n, a s) ^ 2 := by
    field_simp
  have h4 : (1 / (n : ℝ) ^ 8) * (∑ s ∈ (blockOf c.1.1 n) ×ˢ Finset.range n, a s) ^ 2
      ≤ (1 / (n : ℝ) ^ 8) * (((n ^ 3 * n : ℕ) : ℝ) *
        ∑ s ∈ (blockOf c.1.1 n) ×ˢ Finset.range n, a s ^ 2) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  have h5 : (1 / (n : ℝ) ^ 8) * (((n ^ 3 * n : ℕ) : ℝ) *
        ∑ s ∈ (blockOf c.1.1 n) ×ˢ Finset.range n, a s ^ 2)
      = (1 / (n : ℝ) ^ 4) * ∑ s ∈ (blockOf c.1.1 n) ×ˢ Finset.range n, a s ^ 2 := by
    push_cast; field_simp
  have h6 : ∑ s ∈ (blockOf c.1.1 n) ×ˢ Finset.range n, a s ^ 2 =
      ∑ x ∈ blockOf c.1.1 n, ∑ i ∈ Finset.range n, ‖A (pathSite x c.2 i, c.2)‖ ^ 2 := by
    rw [Finset.sum_product]
  rw [← h6]
  linarith

#print axioms bond_sq_le

end AdalyFormal.StatementLane3
