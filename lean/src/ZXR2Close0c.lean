import ZXR2Close0b

/-!
# R2Close0c -- `k = 0`: `Q = id`, coercivity `G⁻¹ ≥ a`, `Δ^{(2)} = 0`, `Q*` injective, `hunit`, closed `Ingr`
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.IngredientFamilyR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.StatementLane (scaleUp Tower)

section
variable (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

local notation "PP" => P0 ell Lu hell a Lam

/-- at `k = 0` the level-0 composite is the identity: `Q_0 = id`. -/
theorem P0_QlinB (A : BondFnL2 (scaleUp ell 0 Lu)) :
    QlinB (PP).G (PP).U 0 A = A :=
  QlinB_zero _ _ A

theorem P0_Qfull_apply (A : BondFnL2 (scaleUp ell 0 Lu)) (p : BIdx (PP).G) :
    ((PP).sector.Qfull A) p = (WithLp.ofLp A) p.2.1 := by
  have hp : (p.1 : ℕ) = 0 := by
    have : (p.1 : ℕ) < 1 := p.1.isLt
    omega
  have key : ∀ (j : ℕ) (b : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell 0 Lu)), j = 0 →
      (((PP).G.ell : ℝ) ^ j)⁻¹ • (WithLp.ofLp (QlinB (PP).G (PP).U j A)) b = (WithLp.ofLp A) b := by
    intro j b hj
    subst hj
    rw [P0_QlinB, pow_zero, inv_one, one_smul]
  exact key (p.1 : ℕ) p.2.1 hp

/-- `Σ_p ‖y p.2.1‖² = ‖y‖²` (the index equivalence). -/
theorem P0_sum_index (y : BondFnL2 (scaleUp ell 0 Lu)) :
    ∑ p : BIdx (PP).G, ‖(WithLp.ofLp y) p.2.1‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact (Fintype.sum_equiv (idx0 ell Lu hell a Lam).symm _ _ (fun p => rfl))


theorem P0_mass_inner (x : ↥(bondSupp (PP).G)) :
    ⟪x, (PP).data.Mass x⟫ = a * ‖x‖ ^ 2 := by
  have h1 : ⟪x, (PP).data.Mass x⟫ = ⟪iE (PP).G x, MassFull (PP).G (PP).a (PP).sector (iE (PP).G x)⟫ := by
    show ⟪x, (pE (PP).G) ((MassFull (PP).G (PP).a (PP).sector) ((iE (PP).G) x))⟫ = _
    rw [pE_inner_right]
  rw [h1, inner_MassFull]
  have h2 : ∀ p : BIdx (PP).G,
      (PP).a * ((PP).G.ell : ℝ) ^ (p.1 : ℕ) * ‖(PP).sector.Qfull (iE (PP).G x) p‖ ^ 2
        = a * ‖(WithLp.ofLp (iE (PP).G x)) p.2.1‖ ^ 2 := by
    intro p
    have hp : (p.1 : ℕ) = 0 := by
      have : (p.1 : ℕ) < 1 := p.1.isLt
      omega
    have key : ∀ (j : ℕ), j = 0 →
        (PP).a * ((PP).G.ell : ℝ) ^ j * ‖(PP).sector.Qfull (iE (PP).G x) p‖ ^ 2
          = a * ‖(PP).sector.Qfull (iE (PP).G x) p‖ ^ 2 := by
      intro j hj; subst hj; rw [pow_zero, mul_one]; rfl
    rw [key _ hp, P0_Qfull_apply]
  rw [Finset.sum_congr rfl (fun p _ => h2 p), ← Finset.mul_sum, P0_sum_index]
  rfl

theorem P0_Ginv_coercive (x : ↥(bondSupp (PP).G)) :
    a * ‖x‖ ^ 2 ≤ ⟪x, (PP).data.Ginv x⟫ := by
  rw [BaseDataS.inner_Ginv, P0_mass_inner]
  have hD : 0 ≤ ⟪x, (PP).data.Dpi x⟫ := by
    show 0 ≤ ⟪x, (pE (PP).G) ((DpiFull (PP).G (PP).U (PP).a) ((iE (PP).G) x))⟫
    rw [pE_inner_right]
    exact DpiFull_flat_nonneg (PP).G (PP).a _
  have hT : 0 ≤ ‖(PP).data.T x‖ ^ 2 := sq_nonneg _
  linarith

theorem P0_Delta2_zero : (PP).data.Delta2 (PP).data_laws = 0 := by
  obtain ⟨hs, hf⟩ := (PP).data.Delta2_spec (PP).data_laws
  refine symm_unique hs (fun x y => by simp) (fun A => ?_)
  rw [hf A]
  have hJ : (PP).data.J = 0 := by
    show (pE (PP).G) (PP).Jf = 0
    rw [Jf_flat (PP) rfl]; exact map_zero _
  rw [hJ]; simp

theorem P0_Qs_injective : Function.Injective (PP).data.Qs := by
  have hsurj : ∀ f : FSp (PP).G, ∃ A : ↥(bondSupp (PP).G), (PP).data.Q A = f := by
    intro f
    refine ⟨⟨WithLp.toLp 2 (fun b => (WithLp.ofLp f) ((idx0 ell Lu hell a Lam) b)), ?_⟩, ?_⟩
    · rw [P0_bondSupp_top]; exact Submodule.mem_top
    · refine PiLp.ext (fun p => ?_)
      show (PP).sector.Qfull ((iE (PP).G) _) p = _
      rw [P0_Qfull_apply]
      show (WithLp.ofLp f) ((idx0 ell Lu hell a Lam) p.2.1) = _
      rw [show (idx0 ell Lu hell a Lam) p.2.1 = p from (idx0 ell Lu hell a Lam).right_inv p]
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨A, hA⟩ := hsurj y
  have h1 : ⟪(PP).data.Q A, y⟫ = ⟪A, (PP).data.Qs y⟫ := (PP).data.Q_adj A y
  rw [hy, inner_zero_right, hA] at h1
  exact inner_self_eq_zero.mp h1

end

end AdalyFormal.IngredientFamilyR2
