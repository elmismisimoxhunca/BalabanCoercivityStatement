/-
Smooth local logarithm at the identity of SU(2), and the jets of `su2Log ∘ G`.
Lane: compute/ingredient_family_20261009_r2/smoothlog (2026-10-09).
-/
import AdalyFormal.Balaban.RegularityGap
import AdalyFormal.Balaban.BlockedGaugeGuardAlgebraExp
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AdalyFormal.Balaban.SmoothLog

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Balaban.SuTwoLogExp
open Filter Topology

/-! ## (A) `exp` of a traceless anti-Hermitian matrix is in `SU(2)`; the guard is transparent.

Membership is REUSED (LAW-19) from `BlockedGaugeGuardAlgebraExp.exp_antiHerm_traceless_mem_special`. -/

theorem exp_mem_suTwo {X : M2} (hah : Xᴴ = -X) (htr : Matrix.trace X = 0) :
    NormedSpace.exp X ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  exp_antiHerm_traceless_mem_special hah htr

theorem su2Exp_coe_of_mem_suTwo {X : M2} (hah : Xᴴ = -X) (htr : Matrix.trace X = 0) :
    ((su2Exp X : SU2) : M2) = NormedSpace.exp X :=
  su2Exp_of_mem (exp_mem_suTwo hah htr)

/-! ## (B) The smooth local logarithm `Lg`: local inverse of `NormedSpace.exp` at `0`. -/

theorem exp_analyticAt_zero : AnalyticAt ℝ (NormedSpace.exp : M2 → M2) 0 :=
  NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) 0
    (by rw [NormedSpace.expSeries_radius_eq_top]; simp)

/-- `ContDiffAt ℝ ⊤` with `⊤ : WithTop ℕ∞`, i.e. analytic order `ω`. -/
theorem exp_contDiffAt_zero : ContDiffAt ℝ ⊤ (NormedSpace.exp : M2 → M2) 0 :=
  exp_analyticAt_zero.contDiffAt

theorem exp_hasFDerivAt_zero :
    HasFDerivAt (NormedSpace.exp : M2 → M2)
      ((ContinuousLinearEquiv.refl ℝ M2 : M2 ≃L[ℝ] M2) : M2 →L[ℝ] M2) 0 :=
  hasFDerivAt_exp_zero (𝕂 := ℝ)

theorem top_ne_zero' : (⊤ : WithTop ℕ∞) ≠ 0 := by simp

/-- **The smooth local logarithm**: Mathlib's local inverse of `NormedSpace.exp : M2 → M2` at `0`
(inverse function theorem, `ContDiffAt.localInverse`). -/
noncomputable def Lg : M2 → M2 :=
  exp_contDiffAt_zero.localInverse exp_hasFDerivAt_zero top_ne_zero'

theorem exp_hasStrictFDerivAt_zero :
    HasStrictFDerivAt (NormedSpace.exp : M2 → M2)
      ((ContinuousLinearEquiv.refl ℝ M2 : M2 ≃L[ℝ] M2) : M2 →L[ℝ] M2) 0 :=
  exp_contDiffAt_zero.hasStrictFDerivAt' exp_hasFDerivAt_zero top_ne_zero'

theorem Lg_eq_localInverse :
    Lg = exp_hasStrictFDerivAt_zero.localInverse _ _ _ := rfl

/-- `Lg` is `C^⊤` (analytic order) at `1`. -/
theorem Lg_contDiffAt : ContDiffAt ℝ ⊤ Lg 1 := by
  have h := exp_contDiffAt_zero.to_localInverse exp_hasFDerivAt_zero top_ne_zero'
  rw [NormedSpace.exp_zero] at h
  exact h

theorem Lg_contDiffAt_of_le (n : WithTop ℕ∞) : ContDiffAt ℝ n Lg 1 :=
  Lg_contDiffAt.of_le le_top

theorem Lg_one : Lg 1 = 0 := by
  have h := exp_contDiffAt_zero.localInverse_apply_image exp_hasFDerivAt_zero top_ne_zero'
  rw [NormedSpace.exp_zero] at h
  exact h

theorem Lg_exp_eventually : ∀ᶠ X in 𝓝 (0 : M2), Lg (NormedSpace.exp X) = X :=
  exp_hasStrictFDerivAt_zero.eventually_left_inverse

theorem exp_Lg_eventually : ∀ᶠ g in 𝓝 (1 : M2), NormedSpace.exp (Lg g) = g := by
  have h := exp_hasStrictFDerivAt_zero.eventually_right_inverse
  rw [NormedSpace.exp_zero] at h
  exact h

theorem Lg_hasStrictFDerivAt : HasStrictFDerivAt Lg (ContinuousLinearMap.id ℝ M2) 1 := by
  have h := exp_hasStrictFDerivAt_zero.to_localInverse
  rw [NormedSpace.exp_zero] at h
  exact h

theorem fderiv_Lg_one : fderiv ℝ Lg 1 = ContinuousLinearMap.id ℝ M2 :=
  Lg_hasStrictFDerivAt.hasFDerivAt.fderiv

/-! ### Agreement of `su2Log` with `Lg` on `SU(2)` near `1` -/

/-- The angle formula of `su2Angle`, on the ambient matrices. -/
noncomputable def angleM (g : M2) : ℝ := Real.arccos ((Matrix.trace g).re / 2)

theorem angleM_continuous : Continuous angleM :=
  Real.continuous_arccos.comp
    ((Complex.continuous_re.comp (continuous_id.matrix_trace)).div_const 2)

theorem angleM_one : angleM 1 = 0 := by
  simp [angleM, Matrix.trace_one]

theorem eventually_angleM_lt : ∀ᶠ g in 𝓝 (1 : M2), angleM g < Real.pi / 2 := by
  have ht := angleM_continuous.tendsto (1 : M2)
  rw [angleM_one] at ht
  exact ht.eventually (eventually_lt_nhds (by positivity))

theorem eventually_skew_small (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ g in 𝓝 (1 : M2), ‖g - gᴴ‖ < δ := by
  have hc : Continuous fun g : M2 => ‖g - gᴴ‖ :=
    (continuous_id.sub continuous_id.matrix_conjTranspose).norm
  have ht := hc.tendsto (1 : M2)
  simp only [Matrix.conjTranspose_one, sub_self, norm_zero] at ht
  exact ht.eventually (eventually_lt_nhds hδ)

theorem one_ne_negOne_M2 : (1 : M2) ≠ -1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp at h00
  norm_num at h00

theorem kappa_bound (g : SU2) (hθ : su2Angle g ≤ Real.pi / 2) :
    0 ≤ su2Kappa g ∧ su2Kappa g ≤ Real.pi / 2 := by
  have h0 : 0 ≤ su2Angle g := Real.arccos_nonneg _
  have hs : 0 ≤ Real.sin (su2Angle g) :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  refine ⟨div_nonneg h0 hs, ?_⟩
  rcases eq_or_lt_of_le hs with hz | hpos
  · rw [su2Kappa, ← hz, div_zero]; positivity
  · rw [su2Kappa, div_le_iff₀ hpos]
    have hj := Real.mul_le_sin h0 hθ
    have hpi := Real.pi_pos
    have : su2Angle g = Real.pi / 2 * (2 / Real.pi * su2Angle g) := by
      field_simp
    nlinarith

theorem norm_su2Log_le (g : SU2) (hθ : su2Angle g ≤ Real.pi / 2) :
    ‖su2Log g‖ ≤ Real.pi / 4 * ‖(g : M2) - (g : M2)ᴴ‖ := by
  obtain ⟨hk0, hk1⟩ := kappa_bound g hθ
  rw [su2Log, norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have hn := norm_nonneg ((g : M2) - (g : M2)ᴴ)
  have : su2Kappa g / 2 ≤ Real.pi / 4 := by linarith
  exact mul_le_mul_of_nonneg_right this hn

/-- `su2Log g` is the exponential logarithm of `g` for every `g ≠ −1` (reused branch lemma, plus
transparency of the guard from (A)). -/
theorem exp_su2Log (g : SU2) (hne : g ≠ su2NegOne) :
    NormedSpace.exp (su2Log g) = (g : M2) := by
  have hm := exp_mem_suTwo (su2Log_antiHermitian g) (su2Log_traceless g)
  have h := congrArg Subtype.val (AdalyFormal.Balaban.RegularityGap.su2_exp_log_of_ne_negOne g hne)
  rw [su2Exp_of_mem hm] at h
  exact h

/-- **(B) — agreement.** On `SU(2)`, in an `M2`-neighbourhood of `1`, `su2Log = Lg`. -/
theorem su2Log_eq_Lg_eventually :
    ∀ᶠ g in 𝓝 (1 : M2), ∀ h : g ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      su2Log ⟨g, h⟩ = Lg g := by
  obtain ⟨ε, εpos, hε⟩ := Metric.eventually_nhds_iff.mp Lg_exp_eventually
  have hδ : 0 < ε / Real.pi := div_pos εpos Real.pi_pos
  filter_upwards [eventually_angleM_lt, eventually_skew_small (ε / Real.pi) hδ,
    eventually_ne_nhds one_ne_negOne_M2] with g hg1 hg2 hg3 h
  have hθ : su2Angle ⟨g, h⟩ ≤ Real.pi / 2 := le_of_lt hg1
  have hb := norm_su2Log_le ⟨g, h⟩ hθ
  have hsmall : ‖su2Log ⟨g, h⟩‖ < ε := by
    have hpi := Real.pi_pos
    have e1 : Real.pi / 4 * (ε / Real.pi) = ε / 4 := by field_simp
    have : Real.pi / 4 * ‖g - gᴴ‖ < Real.pi / 4 * (ε / Real.pi) :=
      mul_lt_mul_of_pos_left hg2 (by positivity)
    change ‖su2Log ⟨g, h⟩‖ ≤ Real.pi / 4 * ‖g - gᴴ‖ at hb
    linarith
  have hne : (⟨g, h⟩ : SU2) ≠ su2NegOne := by
    intro he
    apply hg3
    have := congrArg Subtype.val he
    simpa using this
  have hl := hε (y := su2Log ⟨g, h⟩) (by rwa [dist_zero_right])
  rw [exp_su2Log ⟨g, h⟩ hne] at hl
  exact hl.symm

/-! ## (C) Consumer corollary: `A ↦ su2Log (G A)` is `C^n` at `0`, equal to `Lg ∘ G` near `0`. -/

section Consumer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem su2Log_comp_eventuallyEq (G : E → SU2)
    (hG : ContinuousAt (fun A => (G A : M2)) 0) (hG0 : G 0 = 1) :
    (fun A => su2Log (G A)) =ᶠ[𝓝 0] fun A => Lg (G A : M2) := by
  have ht : Tendsto (fun A => (G A : M2)) (𝓝 0) (𝓝 1) := by
    have h := hG.tendsto
    rw [hG0] at h
    exact h
  filter_upwards [ht.eventually su2Log_eq_Lg_eventually] with A hA
  exact hA (G A).2

theorem su2Log_comp_contDiffAt (G : E → SU2) {n : WithTop ℕ∞}
    (hG : ContDiffAt ℝ n (fun A => (G A : M2)) 0) (hG0 : G 0 = 1) :
    ContDiffAt ℝ n (fun A => su2Log (G A)) 0 := by
  have hL : ContDiffAt ℝ n Lg ((G 0 : SU2) : M2) := by
    rw [hG0]; exact Lg_contDiffAt_of_le n
  have hc : ContDiffAt ℝ n (fun A => Lg (G A : M2)) 0 := hL.comp (0 : E) hG
  exact hc.congr_of_eventuallyEq (su2Log_comp_eventuallyEq G hG.continuousAt hG0)

/-- First-order jet: `D(su2Log ∘ G)(0) = D(↑G)(0)`. -/
theorem fderiv_su2Log_comp (G : E → SU2)
    (hG : DifferentiableAt ℝ (fun A => (G A : M2)) 0) (hG0 : G 0 = 1) :
    fderiv ℝ (fun A => su2Log (G A)) 0 = fderiv ℝ (fun A => (G A : M2)) 0 := by
  rw [(su2Log_comp_eventuallyEq G hG.continuousAt hG0).fderiv_eq]
  have hL : HasFDerivAt Lg (ContinuousLinearMap.id ℝ M2) ((G 0 : SU2) : M2) := by
    rw [hG0]; exact Lg_hasStrictFDerivAt.hasFDerivAt
  have h := (hL.comp (0 : E) hG.hasFDerivAt).fderiv
  exact h.trans (ContinuousLinearMap.ext fun _ => rfl)

/-! ## (D) `G = su2Exp ∘ S` with `S` su(2)-valued and `S 0 = 0`: `su2Log ∘ G = S` near `0`. -/

theorem su2Log_su2Exp_eventuallyEq (S : E → M2) (hS : ContinuousAt S 0) (hS0 : S 0 = 0)
    (hah : ∀ A, (S A)ᴴ = -S A) (htr : ∀ A, Matrix.trace (S A) = 0) :
    (fun A => su2Log (su2Exp (S A))) =ᶠ[𝓝 0] S := by
  have hSt : Tendsto S (𝓝 0) (𝓝 0) := by
    have h := hS.tendsto; rw [hS0] at h; exact h
  have hEt : Tendsto (fun A => NormedSpace.exp (S A)) (𝓝 0) (𝓝 1) := by
    have h := (exp_contDiffAt_zero.continuousAt.tendsto).comp hSt
    rw [NormedSpace.exp_zero] at h
    exact h
  filter_upwards [hEt.eventually su2Log_eq_Lg_eventually, hSt.eventually Lg_exp_eventually]
    with A h1 h2
  have hm := exp_mem_suTwo (hah A) (htr A)
  have he : su2Exp (S A) = ⟨NormedSpace.exp (S A), hm⟩ :=
    Subtype.ext (su2Exp_coe_of_mem_suTwo (hah A) (htr A))
  rw [he, h1 hm]
  exact h2

theorem fderiv_su2Log_su2Exp (S : E → M2) (hS : ContinuousAt S 0) (hS0 : S 0 = 0)
    (hah : ∀ A, (S A)ᴴ = -S A) (htr : ∀ A, Matrix.trace (S A) = 0) :
    fderiv ℝ (fun A => su2Log (su2Exp (S A))) 0 = fderiv ℝ S 0 :=
  (su2Log_su2Exp_eventuallyEq S hS hS0 hah htr).fderiv_eq

/-- All jets (in particular the first and second Taylor coefficients) coincide with those of `S`. -/
theorem iteratedFDeriv_su2Log_su2Exp (S : E → M2) (hS : ContinuousAt S 0) (hS0 : S 0 = 0)
    (hah : ∀ A, (S A)ᴴ = -S A) (htr : ∀ A, Matrix.trace (S A) = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (fun A => su2Log (su2Exp (S A))) 0 = iteratedFDeriv ℝ n S 0 :=
  ((su2Log_su2Exp_eventuallyEq S hS hS0 hah htr).iteratedFDeriv ℝ n).eq_of_nhds

end Consumer

end AdalyFormal.Balaban.SmoothLog
