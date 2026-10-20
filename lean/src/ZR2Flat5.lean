import R2Flat4
import ZIngredientQ1

/-!
# R2Flat5 -- FLAT CROSS-CHECK: the jet of the printed (63) at `V₀ = 1`, stride 1, equals the printed
`ell · Q₁` of CMP96 (2.125) (`q1SU2`, r1's formula)  [a two-independent-paths check]
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.IngredientFamilyR2

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath
  coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepBlockOf_one)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS cPlusS_eq coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.AdmissibleSubspace (card_blockOf_of_coarse)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_blockOf_eq_image coarseShift_injective)

open Fin.NatCast

variable {L : PeriodicLatticeExtent}

/-- the `μ`-coordinate of a shifted site. -/
theorem coarseShift_coord_self (y : PeriodicLatticeSite L) (t : ℕ) (μ : Fin 3) :
    (coarseShift y t μ) μ = y μ + ((t : ℕ) : Fin (L μ + 1)) := by
  apply Fin.ext
  rw [coarseShift_val_eq, Fin.val_add, Fin.val_natCast]
  simp [Nat.add_mod]

theorem coarseShift_diff (y x : PeriodicLatticeSite L) (t : ℕ) (μ ν : Fin 3) :
    (coarseShift x t μ) ν - (coarseShift y t μ) ν = x ν - y ν := by
  by_cases h : ν = μ
  · subst h
    rw [coarseShift_coord_self, coarseShift_coord_self, add_sub_add_right_eq_sub]
  · rw [coarseShift_apply_ne x t μ ν h, coarseShift_apply_ne y t μ ν h]

/-- `Γ_{y,x}` depends only on the coordinate differences: translation invariance. -/
theorem coarseGammaPath_congr (s : ℕ) (y x y' x' : PeriodicLatticeSite L)
    (hd : ∀ ν : Fin 3, x' ν - y' ν = x ν - y ν) :
    coarseGammaPath s y' x' = coarseGammaPath s y x := by
  unfold coarseGammaPath coarseStraightSegment coarseCoordSteps
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  simp [Function.update_apply, h0, h1, h2]


/-- `T` of a straight line of `n` unit steps: `Σ_{i<n} toM2(a(x + i e_μ, μ))`. -/
theorem Tpath_replicate_one (μ : Fin 3) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, Tpath 1 y (List.replicate n μ)
      = ∑ i ∈ Finset.range n, bondL (pathSite y μ i, μ) := by
  induction n with
  | zero => intro y; simp [Tpath]
  | succ n ih =>
      intro y
      rw [List.replicate_succ, Tpath, ih, Finset.sum_range_succ']
      have hc : coarseShift y 1 μ = periodicLatticeShift y μ := rfl
      rw [hc]
      have hp : ∀ i, pathSite y μ (i + 1) = pathSite (periodicLatticeShift y μ) μ i := by
        intro i; exact Function.iterate_succ_apply _ i y
      simp only [hp, pathSite_zero]
      exact add_comm _ _

theorem Ds_one (ell : ℕ) (y : PeriodicLatticeSite L) :
    Ds 1 ell y = ∑ x ∈ blockOf y ell, Wt ell • Tpath 1 y (coarseGammaPath 1 y x) := by
  unfold Ds; rw [stepBlockOf_one]


/-- the `S₊` contour sum equals the translate of the `S₋` sum (translation invariance of `Γ` and the
shift bijection `B(c₋) → B(c₊)`). -/
theorem Ds_plus_eq (ell : ℕ) (hell : 0 < ell) (hdvd : ∀ μ, ell ∣ (L μ + 1))
    (e : PeriodicLatticeEdge L) (he : e.1 ∈ CoarseLattice L ell) :
    Ds 1 ell (cPlusS 1 ell e)
      = ∑ x ∈ blockOf e.1 ell, Wt ell • Tpath 1 (cPlusS 1 ell e) (coarseGammaPath 1 e.1 x) := by
  have hcp : cPlusS 1 ell e = coarseShift e.1 ell e.2 := by rw [cPlusS_eq, one_mul]
  rw [Ds_one, hcp, coarseShift_blockOf_eq_image hell (hdvd e.2) he,
    Finset.sum_image (fun x _ x' _ h => coarseShift_injective ell e.2 h)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [coarseGammaPath_congr 1 e.1 x (coarseShift e.1 ell e.2) (coarseShift x ell e.2)
    (fun ν => coarseShift_diff e.1 x ell e.2 ν)]

/-- THE FLAT CROSS-CHECK (stride 1): the printed linearisation of (63) at `V₀ = 1` is
`ell⁻³ Σ_{x∈B(c₋)} Σ_{i<ell} a(x + i e_μ, μ)`  (`= ell · Q₁` of CMP96 (2.125)). -/
theorem Dtot_flat_eq_printed (ell : ℕ) (hell : 0 < ell) (hdvd : ∀ μ, ell ∣ (L μ + 1))
    (e : PeriodicLatticeEdge L) (he : e.1 ∈ CoarseLattice L ell) :
    Dtot 1 ell e = ∑ x ∈ blockOf e.1 ell, Wt ell • ∑ i ∈ Finset.range ell, bondL (pathSite x e.2 i, e.2) := by
  have hcard := card_blockOf_of_coarse hdvd he
  have hW : Wt ell * ((ell : ℝ) ^ 3) = 1 := by
    unfold Wt; field_simp
  have hline : ∀ x : PeriodicLatticeSite L, Tpath 1 x (List.replicate ell e.2)
      = ∑ i ∈ Finset.range ell, bondL (pathSite x e.2 i, e.2) := fun x => Tpath_replicate_one e.2 ell x
  unfold Dtot Davg Tloop
  rw [Ds_plus_eq ell hell hdvd e he, Ds_one, stepBlockOf_one]
  simp only [smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    hcard, ← hline]
  have hc : ((ell ^ 3 : ℕ) • (Wt ell • Tpath 1 e.1 (List.replicate ell e.2)))
      = Tpath 1 e.1 (List.replicate ell e.2) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [mul_comm, hW, one_smul]
  rw [hc]
  abel

#print axioms Dtot_flat_eq_printed

end AdalyFormal.IngredientFamilyR2
