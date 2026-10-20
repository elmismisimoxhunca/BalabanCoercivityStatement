import ZR3A2

/-!
# R3A3 -- `‖Qclm ell hell k Lu U A‖ ≤ ‖A‖` for EVERY `k`, `Lu`, `U` (uniform contraction).
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
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.QOne (pathSite)

theorem Qclm_norm_sq_le (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (U : LinkCfg (scaleUp ell k Lu)) (A : BondFnL2 (scaleUp ell k Lu)) :
    ‖Qclm ell hell k Lu U A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  classical
  have hn : 0 < ell ^ k := pow_pos hell k
  have hnR : (0 : ℝ) < (ell ^ k : ℕ) := by exact_mod_cast hn
  have hdvd : ∀ μ : Fin 3, ell ^ k ∣ scaleUp ell k Lu μ + 1 := by
    intro μ
    have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    simp only [scaleUp]
    rw [Nat.sub_add_cancel this]
    exact Dvd.intro_left _ rfl
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  -- per-bond bound
  have hb : ∀ b : Bond Lu, ‖(Qclm ell hell k Lu U A).ofLp b‖ ^ 2 ≤
      (1 / ((ell ^ k : ℕ) : ℝ) ^ 4) * ∑ x ∈ blockOf (embSite ell hell k b.1) (ell ^ k),
        ∑ i ∈ Finset.range (ell ^ k), ‖A.ofLp (pathSite x b.2 i, b.2)‖ ^ 2 := by
    intro b
    rw [Qclm_apply]
    have hc := AdalyFormal.Balaban.BlockedGauge.card_blockOf (L := scaleUp ell k Lu) hn hdvd
      (embSite_mem ell hell k b.1)
    exact bond_sq_le U (ell ^ k) hn A.ofLp
      ⟨⟨embSite ell hell k b.1, embSite_mem ell hell k b.1⟩, b.2⟩ hc
  refine (Finset.sum_le_sum fun b _ => hb b).trans ?_
  -- regroup
  rw [← Finset.mul_sum]
  have hreg : ∑ b : Bond Lu, ∑ x ∈ blockOf (embSite ell hell k b.1) (ell ^ k),
        ∑ i ∈ Finset.range (ell ^ k), ‖A.ofLp (pathSite x b.2 i, b.2)‖ ^ 2
      ≤ ((ell ^ k : ℕ) : ℝ) * ∑ b : Bond (scaleUp ell k Lu), ‖A.ofLp b‖ ^ 2 := by
    have hsplit : ∀ (F : Bond Lu → ℝ), ∑ b : Bond Lu, F b = ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite Lu, F (y, μ) := by
      intro F
      exact (Fintype.sum_prod_type_right F).symm ▸ rfl
    have hsplit' : ∀ (F : Bond (scaleUp ell k Lu) → ℝ), ∑ b : Bond (scaleUp ell k Lu), F b
        = ∑ μ : Fin 3, ∑ z : PeriodicLatticeSite (scaleUp ell k Lu), F (z, μ) := by
      intro F
      exact (Fintype.sum_prod_type_right F)
    rw [hsplit, hsplit', Finset.mul_sum]
    refine Finset.sum_le_sum fun μ _ => ?_
    have e1 : ∀ y : PeriodicLatticeSite Lu, ∑ x ∈ blockOf (embSite ell hell k y) (ell ^ k),
        ∑ i ∈ Finset.range (ell ^ k), ‖A.ofLp (pathSite x μ i, μ)‖ ^ 2
        = ∑ i ∈ Finset.range (ell ^ k), ∑ x ∈ blockOf (embSite ell hell k y) (ell ^ k),
        ‖A.ofLp (pathSite x μ i, μ)‖ ^ 2 := fun y => Finset.sum_comm
    have e2 : ∑ y : PeriodicLatticeSite Lu, ∑ x ∈ blockOf (embSite ell hell k y) (ell ^ k),
        ∑ i ∈ Finset.range (ell ^ k), ‖A.ofLp (pathSite x μ i, μ)‖ ^ 2
        = ∑ i ∈ Finset.range (ell ^ k), ∑ y : PeriodicLatticeSite Lu,
          ∑ x ∈ blockOf (embSite ell hell k y) (ell ^ k), ‖A.ofLp (pathSite x μ i, μ)‖ ^ 2 := by
      simp_rw [e1]; exact Finset.sum_comm
    show ∑ y : PeriodicLatticeSite Lu, ∑ x ∈ blockOf (embSite ell hell k (y, μ).1) (ell ^ k),
        ∑ i ∈ Finset.range (ell ^ k), ‖A.ofLp (pathSite x (y, μ).2 i, (y, μ).2)‖ ^ 2 ≤ _
    simp only []
    rw [e2]
    have e3 : ∀ i ∈ Finset.range (ell ^ k), ∑ y : PeriodicLatticeSite Lu,
          ∑ x ∈ blockOf (embSite ell hell k y) (ell ^ k), ‖A.ofLp (pathSite x μ i, μ)‖ ^ 2
        ≤ ∑ z : PeriodicLatticeSite (scaleUp ell k Lu), ‖A.ofLp (z, μ)‖ ^ 2 := by
      intro i _
      refine (block_sum_le ell hell k Lu (fun x => ‖A.ofLp (pathSite x μ i, μ)‖ ^ 2)
        (fun x => by positivity)).trans ?_
      exact sum_comp_pathSite_le μ i (fun z => ‖A.ofLp (z, μ)‖ ^ 2) (fun x => by positivity)
    refine (Finset.sum_le_sum e3).trans ?_
    simp
  have hS : 0 ≤ ∑ b : Bond (scaleUp ell k Lu), ‖A.ofLp b‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h1 : (1 : ℝ) ≤ ((ell ^ k : ℕ) : ℝ) := by exact_mod_cast hn
  calc (1 / ((ell ^ k : ℕ) : ℝ) ^ 4) * (∑ b : Bond Lu, ∑ x ∈ blockOf (embSite ell hell k b.1) (ell ^ k),
        ∑ i ∈ Finset.range (ell ^ k), ‖A.ofLp (pathSite x b.2 i, b.2)‖ ^ 2)
      ≤ (1 / ((ell ^ k : ℕ) : ℝ) ^ 4) * (((ell ^ k : ℕ) : ℝ) *
          ∑ b : Bond (scaleUp ell k Lu), ‖A.ofLp b‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hreg (by positivity)
    _ = (1 / ((ell ^ k : ℕ) : ℝ) ^ 3) * ∑ b : Bond (scaleUp ell k Lu), ‖A.ofLp b‖ ^ 2 := by
        field_simp
    _ ≤ 1 * ∑ b : Bond (scaleUp ell k Lu), ‖A.ofLp b‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hS
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ h1
    _ = _ := one_mul _

theorem Qclm_norm_le (ell : ℕ) (hell : 0 < ell) (k : ℕ) (Lu : PeriodicLatticeExtent)
    (U : LinkCfg (scaleUp ell k Lu)) (A : BondFnL2 (scaleUp ell k Lu)) :
    ‖Qclm ell hell k Lu U A‖ ≤ ‖A‖ :=
  le_of_sq_le_sq (Qclm_norm_sq_le ell hell k Lu U A) (norm_nonneg _)

#print axioms Qclm_norm_le

end AdalyFormal.StatementLane3
