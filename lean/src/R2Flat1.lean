import R2RawX

/-!
# R2Flat1 -- first-order calculus of path holonomies of `exp a` at a FLAT background

`Tpath s y p` is the printed first-order expansion of the ordered product `∏_{b∈p} exp(a_b)`:
`D(hol)(0) a = Σ_{b ∈ p} toM2(a_b)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.IngredientFamilyR2

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.SmoothLog (su2Exp_coe_of_mem_suTwo exp_hasFDerivAt_zero)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-- the trivial (flat) background. -/
def flatCfg : PeriodicLinkConfiguration SU2 L := fun _ => 1

/-- coordinate functional `a ↦ toM2 (a b)`. -/
noncomputable def bondL (b : PeriodicLatticeEdge L) : XS L →L[ℝ] M2 :=
  toM2L.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) b)

theorem bondL_apply (b : PeriodicLatticeEdge L) (a : XS L) : bondL b a = toM2 (a b) := rfl

/-- first-order expansion of `∏_{b ∈ p} exp a_b`. -/
noncomputable def Tpath (s : ℕ) : PeriodicLatticeSite L → List (Fin 3) → (XS L →L[ℝ] M2)
  | _, [] => 0
  | y, μ :: rest => bondL (y, μ) + Tpath s (coarseShift y s μ) rest

theorem coe_prodCfg_flat (a : XS L) (b : PeriodicLatticeEdge L) :
    ((prodCfgX flatCfg a b : SU2) : M2) = NormedSpace.exp (toM2 (a b)) := by
  unfold prodCfgX flatCfg
  rw [mul_one]
  exact su2Exp_coe_of_mem_suTwo (toM2_mem _).1 (toM2_mem _).2

theorem hasFDerivAt_bond (b : PeriodicLatticeEdge L) :
    HasFDerivAt (fun a : XS L => ((prodCfgX flatCfg a b : SU2) : M2)) (bondL b) 0 := by
  have h0 : (fun a : XS L => ((prodCfgX flatCfg a b : SU2) : M2))
      = fun a => NormedSpace.exp (bondL b a) := by
    funext a; exact coe_prodCfg_flat a b
  rw [h0]
  have hl : HasFDerivAt (fun a : XS L => bondL b a) (bondL b) 0 := (bondL b).hasFDerivAt
  have hz : bondL b (0 : XS L) = 0 := map_zero _
  have he : HasFDerivAt (NormedSpace.exp : M2 → M2)
      ((ContinuousLinearEquiv.refl ℝ M2 : M2 ≃L[ℝ] M2) : M2 →L[ℝ] M2) (bondL b (0 : XS L)) := by
    rw [hz]; exact exp_hasFDerivAt_zero
  have := he.comp (0 : XS L) hl
  exact this.congr_fderiv (ContinuousLinearMap.id_comp _)

theorem prodCfgX_zero_flat : prodCfgX flatCfg (0 : XS L) = flatCfg := prodCfgX_zero flatCfg

theorem hol_flat (s : ℕ) (p : List (Fin 3)) :
    ∀ y, coarsePathHolonomy s (flatCfg : PeriodicLinkConfiguration SU2 L) y p = 1 := by
  induction p with
  | nil => intro y; rfl
  | cons μ rest ih =>
      intro y
      show flatCfg (y, μ) * coarsePathHolonomy s flatCfg (coarseShift y s μ) rest = 1
      rw [ih]; simp [flatCfg]

theorem hasFDerivAt_hol (s : ℕ) (p : List (Fin 3)) :
    ∀ y, HasFDerivAt (fun a : XS L => ((coarsePathHolonomy s (prodCfgX flatCfg a) y p : SU2) : M2))
      (Tpath s y p) 0 := by
  induction p with
  | nil =>
      intro y
      have : (fun a : XS L => ((coarsePathHolonomy s (prodCfgX flatCfg a) y [] : SU2) : M2))
          = fun _ => (1 : M2) := by funext a; rfl
      rw [this]
      exact hasFDerivAt_const _ _
  | cons μ rest ih =>
      intro y
      have h1 := hasFDerivAt_bond (L := L) (y, μ)
      have h2 := ih (coarseShift y s μ)
      have := h1.mul' h2
      have e : (fun a : XS L => ((coarsePathHolonomy s (prodCfgX flatCfg a) y (μ :: rest) : SU2) : M2))
          = (fun a : XS L => ((prodCfgX flatCfg a (y, μ) : SU2) : M2)) *
            (fun a : XS L => ((coarsePathHolonomy s (prodCfgX flatCfg a) (coarseShift y s μ) rest : SU2) : M2)) := by
        funext a; rfl
      rw [e]
      refine this.congr_fderiv ?_
      ext h
      simp only [prodCfgX_zero_flat, hol_flat, Tpath]
      simp [flatCfg]
      exact add_comm _ _

#print axioms hasFDerivAt_hol

end AdalyFormal.IngredientFamilyR2
