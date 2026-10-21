import CompactDictionary.RawStep
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
Unconditional derivative transport, including Mathlib's nondifferentiability
junk. The second derivative uses an identity at *every* basepoint.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CompactDictionary

section General
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem fderiv_conjugacy (e : E ≃L[ℝ] F) (t : G ≃L[ℝ] H)
    (f : E → G) (g : F → H) (h : ∀ x, t (f x) = g (e x)) (x v : E) :
    t (fderiv ℝ f x v) = fderiv ℝ g (e x) (e v) := by
  have he : t ∘ f = g ∘ e := funext h
  have hd := congrArg (fun q => fderiv ℝ q x) he
  rw [t.comp_fderiv, e.comp_right_fderiv] at hd
  exact congrArg (fun A : E →L[ℝ] H => A v) hd

theorem fderiv_arrow_conjugacy (e : E ≃L[ℝ] F) (t : G ≃L[ℝ] H)
    (f : E → G) (g : F → H) (h : ∀ x, t (f x) = g (e x)) (x : E) :
    e.arrowCongr t (fderiv ℝ f x) = fderiv ℝ g (e x) := by
  ext w
  simpa [ContinuousLinearEquiv.arrowCongr_apply] using
    fderiv_conjugacy e t f g h x (e.symm w)

theorem second_fderiv_conjugacy (e : E ≃L[ℝ] F) (t : G ≃L[ℝ] H)
    (f : E → G) (g : F → H) (h : ∀ x, t (f x) = g (e x)) (x v w : E) :
    t (fderiv ℝ (fderiv ℝ f) x v w) =
      fderiv ℝ (fderiv ℝ g) (e x) (e v) (e w) := by
  have hd := fderiv_conjugacy e (e.arrowCongr t) (fderiv ℝ f) (fderiv ℝ g)
    (fderiv_arrow_conjugacy e t f g h) x v
  have hv := congrArg (fun A : F →L[ℝ] H => A (e w)) hd
  simpa only [ContinuousLinearEquiv.arrowCongr_apply, e.symm_apply_apply] using hv
end General

open BalabanCompact
noncomputable section
variable {L : Extent}

theorem QlinStep_conjugacy (s ell : ℕ) (V : Cfg L) (a : Bond L → Vec) :
    rawField L (QlinStep s ell V a) =
      AdalyFormal.IngredientFamilyR2.QlinStepL s ell V (rawField L a) := by
  funext c
  have h := fderiv_conjugacy (rawField L) rawCoordsCL
    (fun a => qStep s ell V a c) (AdalyFormal.IngredientFamilyR2.qStepComp s ell V c)
    (fun a => qStep_conjugacy s ell V a c) 0 a
  simp only [map_zero] at h
  convert h using 1 <;> rfl

theorem D2Step_conjugacy (s ell : ℕ) (V : Cfg L) (a b : Bond L → Vec) :
    rawField L (D2Step s ell V a b) =
      AdalyFormal.IngredientFamilyR2.D2StepL s ell V (rawField L a) (rawField L b) := by
  funext c
  have h := second_fderiv_conjugacy (rawField L) rawCoordsCL
    (fun a => qStep s ell V a c) (AdalyFormal.IngredientFamilyR2.qStepComp s ell V c)
    (fun a => qStep_conjugacy s ell V a c) 0 a b
  simp only [map_zero] at h
  convert h using 1 <;> rfl

theorem C2Step_conjugacy (s ell : ℕ) (V : Cfg L) (a : Bond L → Vec) :
    rawField L (C2Step s ell V a) =
      AdalyFormal.IngredientFamilyR2.C2StepL s ell V (rawField L a) := by
  rw [C2Step, map_smul, D2Step_conjugacy]
  rfl

theorem QlinComp_conjugacy (ell : ℕ) (bg : ℕ → Cfg L) (j : ℕ) (a : Bond L → Vec) :
    rawField L (QlinComp ell bg j a) =
      AdalyFormal.IngredientFamilyR2.QlinCompL ell bg j (rawField L a) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change rawField L (QlinStep (ell ^ j) ell (bg j) (QlinComp ell bg j a)) = _
    rw [QlinStep_conjugacy, ih]
    rfl

theorem D2Comp_conjugacy (ell : ℕ) (bg : ℕ → Cfg L) (j : ℕ) (a b : Bond L → Vec) :
    rawField L (D2CompLM ell bg j a b) =
      AdalyFormal.IngredientFamilyR2.D2CompL ell bg j (rawField L a) (rawField L b) := by
  induction j with
  | zero => exact (rawField L).map_zero
  | succ j ih =>
    change rawField L (QlinStep (ell ^ j) ell (bg j) (D2CompLM ell bg j a b) +
      D2Step (ell ^ j) ell (bg j) (QlinComp ell bg j a) (QlinComp ell bg j b)) = _
    rw [map_add, QlinStep_conjugacy, ih, D2Step_conjugacy,
      QlinComp_conjugacy, QlinComp_conjugacy]
    rfl

end
end CompactDictionary
