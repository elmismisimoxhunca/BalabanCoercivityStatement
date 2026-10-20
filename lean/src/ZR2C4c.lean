import ZR2C4b

/-!
# R2C4c -- `C` for a general `Λ`: the tree's `fullC` on the dropped bonds of coarse bonds based in `Λ'`,
identity elsewhere.  Satisfies the `Ingr` laws `C_id`, `C_ker` (Q₁ the covariant average at `Ub`)
and equals `fullCLM` for `Λ = T`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.ReparamCDisjoint (ReadsBond droppedBondLast droppedBondLast_not_reads
  lineCoarseRestrictCov_congr)
open AdalyFormal.Balaban.FullReparamC (fullC fullCLM fullCLM_apply dinvC IsDropped
  fullC_unconditional_mem_kerQ fullC_free)

open Classical in
noncomputable def Clam (ell : ℕ) {Lu : PeriodicLatticeExtent} (Lam : Set (PeriodicLatticeSite Lu))
    (Ub : LinkCfg Lu) : (Bond Lu → SuTwo) →ₗ[ℝ] (Bond Lu → SuTwo) where
  toFun B b := if IsDroppedIn Lam ell b then fullC Ub ell (dinvC Ub ell) B b else B b
  map_add' B B' := by
    funext b
    by_cases h : IsDroppedIn Lam ell b
    · simp only [Pi.add_apply, if_pos h]
      rw [AdalyFormal.Balaban.FullReparamC.fullC_add]; rfl
    · simp [h]
  map_smul' c B := by
    funext b
    by_cases h : IsDroppedIn Lam ell b
    · simp only [Pi.smul_apply, RingHom.id_apply, if_pos h]
      rw [AdalyFormal.Balaban.FullReparamC.fullC_smul]; rfl
    · simp [h]

theorem Clam_id {ell : ℕ} {Lu : PeriodicLatticeExtent} (Lam : Set (PeriodicLatticeSite Lu))
    (Ub : LinkCfg Lu) (B : Bond Lu → SuTwo) (b : Bond Lu) (h : ¬ IsDroppedIn Lam ell b) :
    Clam ell Lam Ub B b = B b := by
  classical
  show (if IsDroppedIn Lam ell b then _ else _) = _
  rw [if_neg h]

theorem Clam_ker {ell : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent}
    (hdvd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (Lam : Set (PeriodicLatticeSite Lu))
    (Ub : LinkCfg Lu) (B : Bond Lu → SuTwo) (c : CoarseBond Lu ell)
    (hc : CRowIn ell Lam c) :
    lineCoarseRestrictCovLM Ub ell (Clam ell Lam Ub B) c = 0 := by
  classical
  rw [lineCoarseRestrictCovLM_apply]
  rw [lineCoarseRestrictCov_congr Ub ell (Clam ell Lam Ub B) (fullC Ub ell (dinvC Ub ell) B) c]
  · exact fullC_unconditional_mem_kerQ hell hdvd Ub B c
  · intro b hb
    by_cases hD : IsDroppedIn Lam ell b
    · show (if IsDroppedIn Lam ell b then _ else _) = _
      rw [if_pos hD]
    · rw [Clam_id Lam Ub B b hD]
      symm
      apply fullC_free
      rintro ⟨c', rfl⟩
      by_cases hcc : c = c'
      · subst hcc
        exact hD ⟨c, hc, rfl⟩
      · exact droppedBondLast_not_reads hell hdvd c c' hcc hb

theorem Clam_univ {ell : ℕ} {Lu : PeriodicLatticeExtent} (Ub : LinkCfg Lu) :
    Clam ell Set.univ Ub = fullCLM Ub ell (dinvC Ub ell) := by
  classical
  apply LinearMap.ext
  intro B
  funext b
  by_cases hD : IsDroppedIn Set.univ ell b
  · show (if IsDroppedIn Set.univ ell b then _ else _) = _
    rw [if_pos hD]; rfl
  · show (if IsDroppedIn Set.univ ell b then _ else _) = _
    rw [if_neg hD]
    symm
    rw [fullCLM_apply]
    apply fullC_free
    rintro ⟨c', rfl⟩
    exact hD ⟨c', Or.inl ⟨c'.1.2, fun _ _ => Set.mem_univ _⟩, rfl⟩

#print axioms Clam_ker
#print axioms Clam_univ

end AdalyFormal.StatementLane2
