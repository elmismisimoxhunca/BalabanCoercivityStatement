import ZR2B4

/-!
# R2B5 -- the spike field is genuinely non-flat: not gauge-equivalent to the trivial configuration.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open scoped Matrix

theorem Ug_ne_one {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) : Ug θ ≠ 1 := by
  intro h
  have hc : (Ug θ : M2') = 1 := by rw [h]; rfl
  have hX : Xm θ = Matrix.diagonal ![(θ : ℂ) * Complex.I, -((θ : ℂ) * Complex.I)] := by
    unfold Xm sig
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hE : (Ug θ : M2') = Matrix.diagonal (NormedSpace.exp ![(θ : ℂ) * Complex.I, -((θ : ℂ) * Complex.I)]) := by
    show NormedSpace.exp (Xm θ) = _
    rw [hX, Matrix.exp_diagonal]
  rw [hE] at hc
  have h00 := congrFun (congrFun hc 0) 0
  simp [Matrix.diagonal_apply_eq] at h00
  rw [← Complex.exp_eq_exp_ℂ] at h00
  have him := congrArg Complex.im h00
  rw [Complex.exp_ofReal_mul_I_im] at him
  simp at him
  have : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_gt_three])
  linarith

/-- the single-bond spike field -/
noncomputable def spike {L : PeriodicLatticeExtent} (e0 : Bond L) (c : ℝ) : Bond L → ℝ :=
  fun e => if e = e0 then c else 0

theorem plaq_spike {L : PeriodicLatticeExtent} (η c : ℝ) (z : PeriodicLatticeSite L)
    (hz : periodicLatticeShift z 0 ≠ z) :
    plaq (Ufield η (spike (periodicLatticeShift z 0, 1) c)) z = Ug (η * c) := by
  unfold plaq Ufield spike
  have h1 : ((z, (0 : Fin 3)) : PeriodicLatticeSite L × Fin 3) ≠ (periodicLatticeShift z 0, 1) := by
    simp
  have h2 : ((periodicLatticeShift z 1, (0 : Fin 3)) : PeriodicLatticeSite L × Fin 3)
      ≠ (periodicLatticeShift z 0, 1) := by simp
  have h3 : ((z, (1 : Fin 3)) : PeriodicLatticeSite L × Fin 3) ≠ (periodicLatticeShift z 0, 1) := by
    simp only [ne_eq, Prod.mk.injEq, and_true]
    exact fun h => hz h.symm
  simp [h1, h2, h3, Ug_zero]

/-- **The spike configuration is not pure gauge**: no gauge transformation makes it trivial. -/
theorem spike_not_pure_gauge {L : PeriodicLatticeExtent} (hN : 1 ≤ L 0) (η c : ℝ)
    (z : PeriodicLatticeSite L) (h0 : 0 < η * c) (h1 : η * c < 1) :
    ¬ ∃ g : PeriodicLatticeSite L → G2,
      periodicGaugeTransform g (Ufield η (spike (periodicLatticeShift z 0, 1) c))
        = (fun _ => (1 : G2)) := by
  rintro ⟨g, hg⟩
  have hp := plaq_gauge g (Ufield η (spike (periodicLatticeShift z 0, 1) c)) z
  rw [hg, plaq_spike η c z (shift_ne_self z 0 hN)] at hp
  have h1' : plaq (fun _ => (1 : G2)) z = 1 := by simp [plaq]
  rw [h1'] at hp
  have : Ug (η * c) = 1 := by
    have := congrArg (fun t => (g z)⁻¹ * t * g z) hp
    simpa [mul_assoc] using this.symm
  exact Ug_ne_one h0 h1 this

#print axioms Ug_ne_one
#print axioms spike_not_pure_gauge

end AdalyFormal.StatementLane2
