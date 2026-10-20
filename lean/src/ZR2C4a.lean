import ZR2C3

/-!
# R2C4a -- the covariant coarse restriction `Q_ell(U)` is SURJECTIVE (tiled torus, any `U`):
right inverse = the dropped-bond lift `Σ_c single_{b₀(c)} (Dinv_c B(c))`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.ReparamCDisjoint (ReadsBond droppedBondLast droppedBondLast_not_reads
  lineCoarseRestrictCov_congr)
open AdalyFormal.Balaban.ReparamCSuTwo (coeffDc coeffDc_apply)
open AdalyFormal.Balaban.FullReparamC (dinvC dinvC_hinv)

theorem coarseRestrictCov_surj {L : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L ell → SuTwo) :
    ∃ A : Bond L → SuTwo, ∀ c, lineCoarseRestrictCov U ell A c = B c := by
  classical
  refine ⟨∑ c, Pi.single (droppedBondLast ell c) (dinvC U ell c (B c)), fun c' => ?_⟩
  have hlin : lineCoarseRestrictCov U ell
      (∑ c, Pi.single (droppedBondLast ell c) (dinvC U ell c (B c))) c' =
      ∑ c, lineCoarseRestrictCov U ell
        (Pi.single (droppedBondLast ell c) (dinvC U ell c (B c))) c' := by
    have := map_sum (lineCoarseRestrictCovLM U ell)
      (fun c => Pi.single (droppedBondLast ell c) (dinvC U ell c (B c))) Finset.univ
    have h2 := congrFun this c'
    simp only [Finset.sum_apply, lineCoarseRestrictCovLM_apply] at h2
    exact h2
  rw [hlin, Finset.sum_eq_single c']
  · rw [← coeffDc_apply]
    have := dinvC_hinv hell hdvd U c'
    exact LinearMap.congr_fun this (B c')
  · intro c _ hne
    have hz : lineCoarseRestrictCov U ell (0 : Bond L → SuTwo) c' = 0 := by
      simp [lineCoarseRestrictCov, AdalyFormal.Balaban.Q1Real.rZeroA]
    rw [← hz]
    apply lineCoarseRestrictCov_congr
    intro b hb
    by_cases h : b = droppedBondLast ell c
    · subst h
      exact absurd hb (droppedBondLast_not_reads hell hdvd c' c (Ne.symm hne))
    · simp [Pi.single_apply, h]
  · intro h; exact absurd (Finset.mem_univ c') h

#print axioms coarseRestrictCov_surj

end AdalyFormal.StatementLane2
