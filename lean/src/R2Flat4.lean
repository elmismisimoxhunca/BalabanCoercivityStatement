import R2Flat3

/-!
# R2Flat4 -- derivative of `rawStep` at the flat background, and of `qStepX`
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.IngredientFamilyR2

open scoped Matrix Matrix.Norms.Frobenius
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)

variable {L : PeriodicLatticeExtent}

theorem rProd_flat_eq (s : ℕ) (a : XS L) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    rProd s flatCfg (expCfgX a) y p = coarsePathHolonomy s (prodCfgX flatCfg a) y p := by
  rw [rProd_eq, hol_flat, inv_one, mul_one]
  rfl

/-- `D` of `sBlock` at the flat background. -/
noncomputable def Ds (s ell : ℕ) (y : PeriodicLatticeSite L) : XS L →L[ℝ] M2 :=
  ∑ x ∈ stepBlockOf y s ell, Wt ell • Tpath s y (coarseGammaPath s y x)

theorem hasFDerivAt_sBlock (s ell : ℕ) (y : PeriodicLatticeSite L) :
    HasFDerivAt (fun a : XS L => sBlock s ell flatCfg (expCfgX a) y) (Ds s ell y) 0 := by
  unfold sBlock Ds
  have hterm : ∀ x ∈ stepBlockOf y s ell,
      HasFDerivAt (fun a : XS L => Wt ell • su2Log (rProd s flatCfg (expCfgX a) y (coarseGammaPath s y x)))
        (Wt ell • Tpath s y (coarseGammaPath s y x)) 0 := by
    intro x _
    have h1 : HasD1 (fun a : XS L => rProd s flatCfg (expCfgX a) y (coarseGammaPath s y x))
        (Tpath s y (coarseGammaPath s y x)) := by
      have e : (fun a : XS L => rProd s flatCfg (expCfgX a) y (coarseGammaPath s y x))
          = fun a => coarsePathHolonomy s (prodCfgX flatCfg a) y (coarseGammaPath s y x) := by
        funext a; exact rProd_flat_eq s a y _
      rw [e]; exact hasD1_hol s y _
    have h2 := h1.log (by
      have e : (fun a : XS L => rProd s flatCfg (expCfgX a) y (coarseGammaPath s y x))
          = fun a => coarsePathHolonomy s (prodCfgX flatCfg a) y (coarseGammaPath s y x) := by
        funext a; exact rProd_flat_eq s a y _
      rw [e]; exact SG_hol s y _)
    exact h2.const_smul (Wt ell)
  have h := HasFDerivAt.fun_sum hterm
  have e : (fun a : XS L => ∑ x ∈ stepBlockOf y s ell,
        ((ell : ℚ) ^ 3)⁻¹ • su2Log (rProd s flatCfg (expCfgX a) y (coarseGammaPath s y x)))
      = fun a => ∑ x ∈ stepBlockOf y s ell,
        Wt ell • su2Log (rProd s flatCfg (expCfgX a) y (coarseGammaPath s y x)) := by
    funext a
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [qsmul_real, rat_cast_Wt]
  rw [e]
  exact h

theorem sBlock_flat_zero (s ell : ℕ) (y : PeriodicLatticeSite L) :
    sBlock s ell flatCfg (expCfgX (0 : XS L)) y = 0 := by
  unfold sBlock
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [rProd_flat_eq, prodCfgX_zero_flat, hol_flat, su2Log_one, smul_zero]

theorem hasD1_su2Exp_sBlock (s ell : ℕ) (y : PeriodicLatticeSite L) :
    HasD1 (fun a : XS L => su2Exp (sBlock s ell flatCfg (expCfgX a) y)) (Ds s ell y) := by
  refine hasD1_su2Exp (hasFDerivAt_sBlock s ell y) (sBlock_flat_zero s ell y) ?_ ?_
  · intro a; exact (sum_qsmul_su2Log_mem _ _ _).1
  · intro a; exact (sum_qsmul_su2Log_mem _ _ _).2

theorem hasD1_su2Exp_neg_sBlock (s ell : ℕ) (y : PeriodicLatticeSite L) :
    HasD1 (fun a : XS L => su2Exp (-(sBlock s ell flatCfg (expCfgX a) y))) (-(Ds s ell y)) := by
  refine hasD1_su2Exp (hasFDerivAt_sBlock s ell y).neg (by rw [sBlock_flat_zero, neg_zero]) ?_ ?_
  · intro a
    have hS : (sBlock s ell flatCfg (expCfgX a) y)ᴴ = -(sBlock s ell flatCfg (expCfgX a) y) :=
      (sum_qsmul_su2Log_mem (stepBlockOf y s ell) (((ell : ℚ) ^ 3)⁻¹)
        (fun x => rProd s flatCfg (expCfgX a) y (coarseGammaPath s y x))).1
    rw [Matrix.conjTranspose_neg, hS]
  · intro a
    have := (sum_qsmul_su2Log_mem (stepBlockOf y s ell) (((ell : ℚ) ^ 3)⁻¹)
      (fun x => rProd s flatCfg (expCfgX a) y (coarseGammaPath s y x))).2
    rw [Matrix.trace_neg]
    exact neg_eq_zero.mpr this

theorem avg_flat_eq_one (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    stridedBlockedGauge su2LogExp s ell (flatCfg : PeriodicLinkConfiguration SU2 L) c = 1 := by
  unfold stridedBlockedGauge
  have hl : ∀ x, loopVar s ell (flatCfg : PeriodicLinkConfiguration SU2 L) c x = 1 := by
    intro x
    unfold loopVar gammaVarStrided coarseBondVar
    rw [hol_flat, hol_flat, hol_flat, hol_flat]; simp
  simp only [hl, su2LogExp_log, su2Log_one, smul_zero, Finset.sum_const_zero, su2LogExp_exp,
    su2Exp_zero, coarseBondVar, hol_flat, one_mul]

/-- total derivative of the printed raw one-step averaging at the flat background. -/
noncomputable def Dtot (s ell : ℕ) (c : PeriodicLatticeEdge L) : XS L →L[ℝ] M2 :=
  ((-(Ds s ell c.1)) + Davg s ell c) + Ds s ell (cPlusS s ell c)

theorem hasD1_rawStep_flat (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    HasD1 (fun a : XS L => rawStep s ell flatCfg (expCfgX a) c) (Dtot s ell c) := by
  have e : (fun a : XS L => rawStep s ell flatCfg (expCfgX a) c)
      = fun a => su2Exp (-(sBlock s ell flatCfg (expCfgX a) c.1))
        * stridedBlockedGauge su2LogExp s ell (prodCfgX flatCfg a) c
        * su2Exp (sBlock s ell flatCfg (expCfgX a) (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell flatCfg c)⁻¹ := by
    funext a; exact rawStep_simp s ell flatCfg (expCfgX a) c
  rw [e]
  have h4 : HasD1 (fun _ : XS L => (stridedBlockedGauge su2LogExp s ell (flatCfg : PeriodicLinkConfiguration SU2 L) c)⁻¹) 0 := by
    rw [avg_flat_eq_one]
    simpa using (HasD1.const_one (E := XS L))
  have := (((hasD1_su2Exp_neg_sBlock s ell c.1).mul (hasD1_avg s ell c)).mul
    (hasD1_su2Exp_sBlock s ell (cPlusS s ell c))).mul h4
  convert this using 1
  unfold Dtot
  simp [add_assoc]

#print axioms hasD1_rawStep_flat

end AdalyFormal.IngredientFamilyR2
