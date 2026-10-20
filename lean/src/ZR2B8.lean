import ZR2B7

/-!
# R2B8 -- the class is smallness-restricted on every covered tower; MUST-FIRE for r1's unbounded f.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- **Smallness-restriction (general).**  On ANY tower satisfying `CoversOm0` with `Ω₀ ≠ ∅`, and
`F M α₀ ≤ 1/2`, some configuration is outside `PerCubeRegularMix` (holonomy `−1` plaquette). -/
theorem covered_class_excludes_some_U {L : PeriodicLatticeExtent} (hN : ∀ μ, 1 ≤ L μ)
    {ell M F k : ℕ} (hell : 1 ≤ ell) (hM : 1 ≤ M) (S : Tower L)
    (hcov : CoversOm0 ell M F k S) (hne : (S.Om 0).Nonempty)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 < α₀) (hsmall : (F : ℝ) * M * α₀ ≤ 1 / 2) :
    ∃ U : LinkCfg L, ¬ PerCubeRegularMix ell M F k S α₀ η U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨sites, j, f, hf1, hf2, hc, _⟩ := hcov x hx
  have hfM : (f : ℝ) * M * α₀ ≤ 1 / 2 := by
    have : (f : ℝ) ≤ F := by exact_mod_cast hf2
    have hM' : (0 : ℝ) ≤ M := by positivity
    have : (f : ℝ) * M * α₀ ≤ F * M * α₀ := by
      apply mul_le_mul_of_nonneg_right _ hα.le
      exact mul_le_mul_of_nonneg_right this hM'
    linarith
  obtain ⟨U, hU⟩ := badU_not_perCubeRegular2 hN hell hM hf1 S hη hα hfM hc
  exact ⟨U, fun h => hU (h f hf1 hf2)⟩

/-- **Smallness-restriction, fixed cube factor (r5 (4)).**  On ANY tower satisfying `CoversOm0c` (one fixed factor `c ≥ 10`) with `Ω₀ ≠ ∅`
and `c M α₀ ≤ 1/2`, some configuration is outside the fixed-factor class `PerCubeRegular2 .. c ..`. -/
theorem coveredc_class_excludes_some_U {L : PeriodicLatticeExtent} (hN : ∀ μ, 1 ≤ L μ)
    {ell M c k : ℕ} (hell : 1 ≤ ell) (hM : 1 ≤ M) (hc10 : 10 ≤ c) (S : Tower L)
    (hcov : CoversOm0c ell M c k S) (hne : (S.Om 0).Nonempty)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 < α₀) (hsmall : (c : ℝ) * M * α₀ ≤ 1 / 2) :
    ∃ U : LinkCfg L, ¬ PerCubeRegular2 ell M c k S α₀ η U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨sites, j, hc, _⟩ := hcov x hx
  obtain ⟨U, hU⟩ := badU_not_perCubeRegular2 hN hell hM hc10 S hη hα hsmall hc
  exact ⟨U, hU⟩

/- (r5: `T40_class_excludes_some_U` and `r1_big_f_vacuous` removed with the `k = 0` tower `T40`.) -/

#print axioms covered_class_excludes_some_U
#print axioms coveredc_class_excludes_some_U

end AdalyFormal.StatementLane2
