import ZXG3B
import ZXR3E

/-!
# G3C -- the genuine (3.156) form at the closed point `k = 0`, flat `U`, full tower, reduces EXACTLY to
`⟨x, Δ_π x⟩ + ‖R D* x‖²` (with `Δ_π = DpiFull`, `R D* = Tfull`, the printed operators of the
ingredient lane), and vanishes on the constant mode.  Used by G3D (must-fire).
No sorry / native_decide / axiom.
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section
variable (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

local notation "PP" => P0 ell Lu hell a Lam

theorem P0_Q_apply (x : ↥(bondSupp (PP).G)) (p : BIdx (PP).G) :
    ((PP).data.Q x) p = (WithLp.ofLp (iE (PP).G x)) p.2.1 :=
  P0_Qfull_apply ell Lu hell a Lam (iE (PP).G x) p

theorem P0_Q_norm_sq (x : ↥(bondSupp (PP).G)) : ‖(PP).data.Q x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  have h : ∀ p : BIdx (PP).G, ‖((PP).data.Q x) p‖ ^ 2 = ‖(WithLp.ofLp (iE (PP).G x)) p.2.1‖ ^ 2 := by
    intro p; rw [P0_Q_apply]
  rw [Finset.sum_congr rfl (fun p _ => h p), P0_sum_index]
  rfl

/-- `Q` is a linear isometry at `k = 0` -/
noncomputable def P0_Qiso : ↥(bondSupp (PP).G) →ₗᵢ[ℝ] FSp (PP).G where
  toLinearMap := ((PP).data.Q : ↥(bondSupp (PP).G) →ₗ[ℝ] FSp (PP).G)
  norm_map' := fun x => by
    have h := P0_Q_norm_sq ell Lu hell a Lam x
    have h1 : ‖(PP).data.Q x‖ = ‖x‖ := by
      have := sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp h
      exact this
    exact h1

theorem P0_Q_inner (x y : ↥(bondSupp (PP).G)) : ⟪(PP).data.Q x, (PP).data.Q y⟫ = ⟪x, y⟫ :=
  (P0_Qiso ell Lu hell a Lam).inner_map_map x y

theorem P0_Qs_Q (x : ↥(bondSupp (PP).G)) : (PP).data.Qs ((PP).data.Q x) = x := by
  refine ext_inner_left ℝ (fun y => ?_)
  rw [← (PP).data.Q_adj, P0_Q_inner]

theorem P0_Q_surj (f : FSp (PP).G) : ∃ A : ↥(bondSupp (PP).G), (PP).data.Q A = f := by
  refine ⟨⟨WithLp.toLp 2 (fun b => (WithLp.ofLp f) ((idx0 ell Lu hell a Lam) b)), ?_⟩, ?_⟩
  · rw [P0_bondSupp_top]; exact Submodule.mem_top
  · refine PiLp.ext (fun p => ?_)
    show (PP).sector.Qfull ((iE (PP).G) _) p = _
    rw [P0_Qfull_apply]
    show (WithLp.ofLp f) ((idx0 ell Lu hell a Lam) p.2.1) = _
    rw [show (idx0 ell Lu hell a Lam) p.2.1 = p from (idx0 ell Lu hell a Lam).right_inv p]

/-- first term of (3.156) at the closed point: `⟨Qx, N⁻¹ Qx⟩ = ⟨x, G₁⁻¹ x⟩` -/
theorem P0_firstTerm_core (hdvd : ∀ μ, ell ∣ (Lu μ + 1)) (ha : 0 < a) (x : ↥(bondSupp (PP).G)) :
    ⟪(PP).data.Q x, Ring.inverse (GenP.Nmat (PP)) ((PP).data.Q x)⟫ = ⟪x, (PP).G1inv x⟫ := by
  obtain ⟨hb, hG, hN⟩ := P0_wellDef ell Lu hell a Lam hdvd ha
  have hG1 : (PP).data.G1 (PP).G1inv ((PP).G1inv x) = x := by
    show Ring.inverse (PP).G1inv ((PP).G1inv x) = x
    have := Ring.inverse_mul_cancel _ hG
    exact ContinuousLinearMap.ext_iff.mp this x
  have hy : GenP.Nmat (PP) ((PP).data.Q ((PP).G1inv x)) = (PP).data.Q x := by
    show (PP).data.Q ((PP).data.G1 (PP).G1inv ((PP).data.Qs ((PP).data.Q ((PP).G1inv x)))) = _
    rw [P0_Qs_Q, hG1]
  have hinv : Ring.inverse (GenP.Nmat (PP)) ((PP).data.Q x) = (PP).data.Q ((PP).G1inv x) := by
    rw [← hy]
    have := Ring.inverse_mul_cancel _ hN
    exact ContinuousLinearMap.ext_iff.mp this _
  rw [hinv, P0_Q_inner]

/-- `τ` is an isometry in the full-support (`k = 0`, full tower) case: `τ* τ = id` -/
theorem P0_tau_inner (f g : FSp (PP).G) : ⟪(PP).tau f, (PP).tau g⟫ = ⟪f, g⟫ := by
  have hFS := fullTower_fullSupp ell 0 Lu hell flatCfg a Lam
  simp only [PiLp.inner_apply]
  rw [← Fintype.sum_equiv ((PP).eqv hFS) (fun e => ⟪(WithLp.ofLp ((PP).tau f)) e, (WithLp.ofLp ((PP).tau g)) e⟫)
      (fun p => ⟪(WithLp.ofLp f) p, (WithLp.ofLp g) p⟫)]
  · intro e
    rw [IngrBParams.tau_apply (PP) hFS, IngrBParams.tau_apply (PP) hFS]
  
theorem P0_taus_tau (f : FSp (PP).G) : ContinuousLinearMap.adjoint (PP).tau ((PP).tau f) = f := by
  refine ext_inner_left ℝ (fun g => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, P0_tau_inner]

/-- **THE REDUCTION.**  At `k = 0`, flat `U`, full tower, `0 < a`: for `B = τ Q x`,
`(3.156)(B) = ⟨x, Δ_π x⟩ + ‖R D* x‖²` (the mass term cancels against the `a`-term; `J = 0`). -/
theorem P0_genForm_eq (hdvd : ∀ μ, ell ∣ (Lu μ + 1)) (ha : 0 < a) (x : ↥(bondSupp (PP).G)) :
    GenP.genForm (PP) ((PP).tau ((PP).data.Q x)) =
      ⟪iE (PP).G x, DpiFull (PP).G flatCfg a (iE (PP).G x)⟫ + ‖Tfull (PP).G flatCfg (iE (PP).G x)‖ ^ 2 := by
  have hJ : (PP).Jf = 0 := Jf_flat (PP) rfl
  have hJd : (PP).data.J = 0 := by
    show (pE (PP).G) (PP).Jf = 0
    rw [hJ]; exact map_zero _
  have hK := (PP).G1inv_spec.form x
  have hKx : ⟪x, (PP).G1inv x⟫ =
      ⟪x, (PP).data.Dpi x⟫ + ‖(PP).data.T x‖ ^ 2 + a * ‖x‖ ^ 2 := by
    rw [hK]
    unfold BaseDataS.K
    rw [hJd, P0_mass_inner]
    simp
  have hη : (PP).eta = 1 := by simp [IngrBParams.eta, P0]
  unfold GenP.genForm GenP.firstTerm
  rw [hJ, inner_zero_right, mul_zero, sub_zero, hη, one_mul, P0_taus_tau, P0_firstTerm_core ell Lu hell a Lam hdvd ha,
    hKx, P0_tau_inner, P0_Q_inner]
  have h1 : ⟪x, (PP).data.Dpi x⟫ = ⟪iE (PP).G x, DpiFull (PP).G flatCfg a (iE (PP).G x)⟫ := by
    show ⟪x, (pE (PP).G) (DpiFull (PP).G flatCfg a (iE (PP).G x))⟫ = _
    rw [pE_inner_right]
  have h2 : (PP).data.T x = Tfull (PP).G flatCfg (iE (PP).G x) := rfl
  have ha' : (PP).a = a := rfl
  have hxx : ⟪x, x⟫ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  rw [h1, h2, ha', hxx]
  ring

/-- any `x` obeying the two flat laws (`curl`-type: `⟨x,Δ_π x⟩ = 0`; `D*`-type: `R D* x = 0`) is a zero
mode of the genuine (3.156) form -/
theorem P0_genForm_zero_of_laws (hdvd : ∀ μ, ell ∣ (Lu μ + 1)) (ha : 0 < a) (x : ↥(bondSupp (PP).G))
    (h1 : ⟪iE (PP).G x, DpiFull (PP).G flatCfg a (iE (PP).G x)⟫ = 0)
    (h2 : Tfull (PP).G flatCfg (iE (PP).G x) = 0) :
    GenP.genForm (PP) ((PP).tau ((PP).data.Q x)) = 0 := by
  rw [P0_genForm_eq ell Lu hell a Lam hdvd ha, h1, h2]; simp

/-- the constant mode: `(3.156)` vanishes on `τ Q (const)` -/
theorem P0_genForm_const (hdvd : ∀ μ, ell ∣ (Lu μ + 1)) (ha : 0 < a) (X : SuTwo) :
    GenP.genForm (PP) ((PP).tau ((PP).data.Q
      ⟨AdalyFormal.StatementLane3.constField (scaleUp ell 0 Lu) X, by
        rw [P0_bondSupp_top]; exact Submodule.mem_top⟩)) = 0 := by
  obtain ⟨h1, h2⟩ := AdalyFormal.StatementLane3.genuine_laws_on_const (PP).G a X
  exact P0_genForm_zero_of_laws ell Lu hell a Lam hdvd ha _ h1 h2

end

#print axioms P0_firstTerm_core
#print axioms P0_taus_tau
#print axioms P0_genForm_eq
#print axioms P0_genForm_zero_of_laws
#print axioms P0_genForm_const

end AdalyFormal.StatementLaneG
