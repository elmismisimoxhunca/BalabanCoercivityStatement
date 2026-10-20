/-
Second-order jet of `A ↦ su2Log (G A)` for a general `C²` map `G : E → SU(2)` with `G 0 = 1`:

  D²(su2Log ∘ G)(0)[h,k] = D²G(0)[h,k] − ½ (DG(0)h · DG(0)k + DG(0)k · DG(0)h).

Route: a second-order chain rule at a point (from `HasFDerivAt.clm_comp`), the diagonal of
`D²exp(0)` from the exponential power series (`HasFPowerSeriesOnBall.factorial_smul`),
polarization with symmetry of second derivatives, and `Lg ∘ exp = id` near `0`.
-/
import SmoothLog

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AdalyFormal.Balaban.SmoothLog

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Balaban.SuTwoLogExp
open Filter Topology

section Chain

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Second-order transfer along an eventual equality. -/
theorem fderiv_fderiv_congr {f₁ f₂ : E → F} {x : E} (hf : f₁ =ᶠ[𝓝 x] f₂) :
    fderiv ℝ (fderiv ℝ f₁) x = fderiv ℝ (fderiv ℝ f₂) x := by
  have h1 : fderiv ℝ f₁ =ᶠ[𝓝 x] fderiv ℝ f₂ :=
    hf.eventuallyEq_nhds.mono fun _ hy => hy.fderiv_eq
  exact h1.fderiv_eq

/-- **Second-order chain rule at a point.** -/
theorem fderiv_fderiv_comp (Φ : F → H) (g : E → F) (x : E) (hΦ : ContDiffAt ℝ 2 Φ (g x))
    (hg : ContDiffAt ℝ 2 g x) (h k : E) :
    fderiv ℝ (fderiv ℝ (Φ ∘ g)) x h k =
      fderiv ℝ (fderiv ℝ Φ) (g x) (fderiv ℝ g x h) (fderiv ℝ g x k)
        + fderiv ℝ Φ (g x) (fderiv ℝ (fderiv ℝ g) x h k) := by
  have hg1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hΦ1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ Φ (g y) :=
    hg.continuousAt.tendsto.eventually
      ((hΦ.eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp))
  have hev : fderiv ℝ (Φ ∘ g) =ᶠ[𝓝 x] fun y => (fderiv ℝ Φ (g y)).comp (fderiv ℝ g y) := by
    filter_upwards [hg1, hΦ1] with y h1 h2
    exact fderiv_comp y h2 h1
  rw [hev.fderiv_eq]
  have hc : HasFDerivAt (fun y => fderiv ℝ Φ (g y))
      ((fderiv ℝ (fderiv ℝ Φ) (g x)).comp (fderiv ℝ g x)) x :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt.comp x
      (hg.differentiableAt (by simp)).hasFDerivAt
  have hd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  rw [(hc.clm_comp hd).fderiv]
  simp
  abel

end Chain

/-! ## The exponential at `0`: `D²exp(0)[u,v] = ½(uv + vu)` -/

theorem exp_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall (NormedSpace.exp : M2 → M2) (NormedSpace.expSeries ℝ M2) 0 ⊤ := by
  have h := NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos (𝕂 := ℝ) (𝔸 := M2)
    (by rw [NormedSpace.expSeries_radius_eq_top]; simp)
  rwa [NormedSpace.expSeries_radius_eq_top] at h

theorem d2exp_zero_diag (u : M2) :
    fderiv ℝ (fderiv ℝ (NormedSpace.exp : M2 → M2)) 0 u u = u * u := by
  have h := exp_hasFPowerSeriesOnBall.factorial_smul u 2
  simp only [iteratedFDeriv_two_apply] at h
  have h' : Nat.factorial 2 • (NormedSpace.expSeries ℝ M2 2 fun _ => u)
      = fderiv ℝ (fderiv ℝ (NormedSpace.exp : M2 → M2)) 0 u u := h
  rw [← h', NormedSpace.expSeries_apply_eq]
  rw [show Nat.factorial 2 = 2 from rfl, two_nsmul, ← add_smul, pow_two]
  norm_num

theorem exp_isSymm : IsSymmSndFDerivAt ℝ (NormedSpace.exp : M2 → M2) 0 :=
  exp_contDiffAt_zero.isSymmSndFDerivAt (by simp)

theorem d2exp_zero (u v : M2) :
    fderiv ℝ (fderiv ℝ (NormedSpace.exp : M2 → M2)) 0 u v = (1 / 2 : ℝ) • (u * v + v * u) := by
  set B := fderiv ℝ (fderiv ℝ (NormedSpace.exp : M2 → M2)) 0 with hB
  have hd := d2exp_zero_diag (u + v)
  rw [← hB] at hd
  have hu := d2exp_zero_diag u
  have hv := d2exp_zero_diag v
  rw [← hB] at hu hv
  have hs : B v u = B u v := exp_isSymm v u
  have hexp : B (u + v) (u + v) = B u u + B u v + (B v u + B v v) := by
    simp only [map_add, add_apply]; abel
  have h2 : B u v + B u v = u * v + v * u := by
    have e : B u u + B u v + (B v u + B v v) = (u + v) * (u + v) := by rw [← hexp]; exact hd
    rw [hu, hv, hs] at e
    have e2 : (u + v) * (u + v) = u * u + u * v + (v * u + v * v) := by noncomm_ring
    rw [e2] at e
    calc B u v + B u v = (u * u + B u v + (B u v + v * v)) - u * u - v * v := by abel
      _ = (u * u + u * v + (v * u + v * v)) - u * u - v * v := by rw [e]
      _ = u * v + v * u := by abel
  rw [← h2, ← two_smul ℝ (B u v), smul_smul]
  norm_num

/-! ## `D²Lg(1)[u,v] = −½(uv + vu)` -/

theorem d2Lg_one (u v : M2) :
    fderiv ℝ (fderiv ℝ Lg) 1 u v = -((1 / 2 : ℝ) • (u * v + v * u)) := by
  have hev : (Lg ∘ NormedSpace.exp) =ᶠ[𝓝 (0 : M2)] id := Lg_exp_eventually
  have h0 := fderiv_fderiv_congr hev
  have hΦ : ContDiffAt ℝ 2 Lg (NormedSpace.exp (0 : M2)) := by
    rw [NormedSpace.exp_zero]; exact Lg_contDiffAt_of_le 2
  have hc := fderiv_fderiv_comp Lg NormedSpace.exp (0 : M2) hΦ
    (exp_contDiffAt_zero.of_le le_top) u v
  rw [h0] at hc
  have hc' : fderiv ℝ (fderiv ℝ (id : M2 → M2)) 0 u v =
      fderiv ℝ (fderiv ℝ Lg) (NormedSpace.exp 0) (fderiv ℝ NormedSpace.exp 0 u)
          (fderiv ℝ NormedSpace.exp 0 v)
        + fderiv ℝ Lg (NormedSpace.exp 0) (fderiv ℝ (fderiv ℝ NormedSpace.exp) 0 u v) := hc
  clear hc
  have hid : fderiv ℝ (id : M2 → M2) = fun _ => ContinuousLinearMap.id ℝ M2 :=
    funext fun _ => fderiv_id
  have hD : fderiv ℝ (NormedSpace.exp : M2 → M2) 0 = ContinuousLinearMap.id ℝ M2 :=
    (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := M2)).fderiv
  rw [hid, fderiv_const_apply, NormedSpace.exp_zero, hD, fderiv_Lg_one, d2exp_zero] at hc'
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply] at hc'
  rw [eq_neg_iff_add_eq_zero]
  exact hc'.symm

/-! ## The consumer: general `G : E → SU(2)` -/

section Consumer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Second-order jet of `su2Log ∘ G`.** For `G` with `C²` coercion at `0` and `G 0 = 1`:
`D²(su2Log∘G)(0)[h,k] = D²G(0)[h,k] − ½(DG h · DG k + DG k · DG h)`. -/
theorem fderiv_fderiv_su2Log_comp (G : E → SU2)
    (hG : ContDiffAt ℝ 2 (fun A => (G A : M2)) 0) (hG0 : G 0 = 1) (h k : E) :
    fderiv ℝ (fderiv ℝ (fun A => su2Log (G A))) 0 h k =
      fderiv ℝ (fderiv ℝ (fun A => (G A : M2))) 0 h k
        - (1 / 2 : ℝ) • (fderiv ℝ (fun A => (G A : M2)) 0 h * fderiv ℝ (fun A => (G A : M2)) 0 k
            + fderiv ℝ (fun A => (G A : M2)) 0 k * fderiv ℝ (fun A => (G A : M2)) 0 h) := by
  have hev := su2Log_comp_eventuallyEq G hG.continuousAt hG0
  have e1 : fderiv ℝ (fderiv ℝ (fun A => su2Log (G A))) 0
      = fderiv ℝ (fderiv ℝ (fun A => Lg (G A : M2))) 0 := fderiv_fderiv_congr hev
  rw [e1]
  have hΦ : ContDiffAt ℝ 2 Lg ((fun A => (G A : M2)) 0) := by
    show ContDiffAt ℝ 2 Lg ((G 0 : SU2) : M2)
    rw [hG0]; exact Lg_contDiffAt_of_le 2
  have hc := fderiv_fderiv_comp Lg (fun A => (G A : M2)) (0 : E) hΦ hG h k
  have hc' : fderiv ℝ (fderiv ℝ (fun A => Lg (G A : M2))) 0 h k =
      fderiv ℝ (fderiv ℝ Lg) ((G 0 : SU2) : M2) (fderiv ℝ (fun A => (G A : M2)) 0 h)
          (fderiv ℝ (fun A => (G A : M2)) 0 k)
        + fderiv ℝ Lg ((G 0 : SU2) : M2) (fderiv ℝ (fderiv ℝ (fun A => (G A : M2))) 0 h k) := hc
  clear hc
  rw [hc', hG0, coe_one, d2Lg_one, fderiv_Lg_one, ContinuousLinearMap.id_apply]
  abel

/-- The same in `iteratedFDeriv` form. -/
theorem iteratedFDeriv_two_su2Log_comp (G : E → SU2)
    (hG : ContDiffAt ℝ 2 (fun A => (G A : M2)) 0) (hG0 : G 0 = 1) (h k : E) :
    iteratedFDeriv ℝ 2 (fun A => su2Log (G A)) 0 ![h, k] =
      iteratedFDeriv ℝ 2 (fun A => (G A : M2)) 0 ![h, k]
        - (1 / 2 : ℝ) • (fderiv ℝ (fun A => (G A : M2)) 0 h * fderiv ℝ (fun A => (G A : M2)) 0 k
            + fderiv ℝ (fun A => (G A : M2)) 0 k * fderiv ℝ (fun A => (G A : M2)) 0 h) := by
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact fderiv_fderiv_su2Log_comp G hG hG0 h k

/-- Diagonal (quadratic-form) version: `D²(su2Log∘G)(0)[h,h] = D²G(0)[h,h] − (DG h)²`. -/
theorem fderiv_fderiv_su2Log_comp_diag (G : E → SU2)
    (hG : ContDiffAt ℝ 2 (fun A => (G A : M2)) 0) (hG0 : G 0 = 1) (h : E) :
    fderiv ℝ (fderiv ℝ (fun A => su2Log (G A))) 0 h h =
      fderiv ℝ (fderiv ℝ (fun A => (G A : M2))) 0 h h
        - fderiv ℝ (fun A => (G A : M2)) 0 h * fderiv ℝ (fun A => (G A : M2)) 0 h := by
  rw [fderiv_fderiv_su2Log_comp G hG hG0 h h, ← two_smul ℝ, smul_smul]
  norm_num

end Consumer

end AdalyFormal.Balaban.SmoothLog
