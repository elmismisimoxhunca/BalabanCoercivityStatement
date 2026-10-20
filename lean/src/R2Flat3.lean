import R2Flat2

/-!
# R2Flat3 -- the first-order jet of the raw one-step averaging at the FLAT background

`QlinStepX s ell flat a c = fromM2 (Dtot s ell c a)` with
`Dtot = −S₋ + Σ_x w (Tγ_x + T_{line,x} − Tγ₊_x − T_c) + T_c + S₊`  (w = ell⁻³),
the literal linearisation of the printed (63).
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

theorem hasD1_hol (s : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    HasD1 (fun a : XS L => coarsePathHolonomy s (prodCfgX flatCfg a) y p) (Tpath s y p) := by
  refine ⟨?_, hasFDerivAt_hol s p y⟩
  show coarsePathHolonomy s (prodCfgX flatCfg (0 : XS L)) y p = 1
  rw [prodCfgX_zero_flat, hol_flat]

theorem SG_hol (s : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    SG (fun a : XS L => coarsePathHolonomy s (prodCfgX flatCfg a) y p) :=
  SG.hol (E := XS L) s (fun a => prodCfgX flatCfg a) (fun b => SG_prodCfgX flatCfg b) p y

/-- `T_{γ}` etc. -/
noncomputable def Tloop (s ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    XS L →L[ℝ] M2 :=
  ((Tpath s c.1 (coarseGammaPath s c.1 x) + Tpath s x (List.replicate ell c.2))
    + -(Tpath s (cPlusS s ell c) (coarseGammaPath s c.1 x)))
    + -(Tpath s c.1 (List.replicate ell c.2))

theorem hasD1_loop (s ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    HasD1 (fun a : XS L => loopVar s ell (prodCfgX flatCfg a) c x) (Tloop s ell c x) := by
  unfold loopVar gammaVarStrided coarseBondVar Tloop
  exact (((hasD1_hol s _ _).mul (hasD1_hol s _ _)).mul (hasD1_hol s _ _).inv).mul
    (hasD1_hol s _ _).inv

theorem hasFDerivAt_log_loop (s ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    HasFDerivAt (fun a : XS L => su2Log (loopVar s ell (prodCfgX flatCfg a) c x))
      (Tloop s ell c x) 0 :=
  (hasD1_loop s ell c x).log (SG_loopVar s ell flatCfg c x)


/-- `ell⁻³` (the printed `L^{-d}`, `d = 3`). -/
noncomputable def Wt (ell : ℕ) : ℝ := ((ell : ℝ) ^ 3)⁻¹

theorem cast_inv_cube (ell : ℕ) : (((ell : ℚ) ^ 3)⁻¹ : ℚ) = (((ell : ℚ) ^ 3)⁻¹) := rfl

theorem rat_cast_Wt (ell : ℕ) : ((((ell : ℚ) ^ 3)⁻¹ : ℚ) : ℝ) = Wt ell := by
  unfold Wt; push_cast; rfl

/-- `D` of the (43)-average of `V₁V₀` at the flat background. -/
noncomputable def Davg (s ell : ℕ) (c : PeriodicLatticeEdge L) : XS L →L[ℝ] M2 :=
  (∑ x ∈ stepBlockOf c.1 s ell, Wt ell • Tloop s ell c x) + Tpath s c.1 (List.replicate ell c.2)

theorem hasFDerivAt_sum_log_loop (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    HasFDerivAt (fun a : XS L => ∑ x ∈ stepBlockOf c.1 s ell,
        ((ell : ℚ) ^ 3)⁻¹ • su2Log (loopVar s ell (prodCfgX flatCfg a) c x))
      (∑ x ∈ stepBlockOf c.1 s ell, Wt ell • Tloop s ell c x) 0 := by
  have h := HasFDerivAt.fun_sum (u := stepBlockOf c.1 s ell)
    (fun x _ => (hasFDerivAt_log_loop s ell c x).const_smul (Wt ell))
  have e : (fun a : XS L => ∑ x ∈ stepBlockOf c.1 s ell,
        ((ell : ℚ) ^ 3)⁻¹ • su2Log (loopVar s ell (prodCfgX flatCfg a) c x))
      = fun a => ∑ x ∈ stepBlockOf c.1 s ell,
        Wt ell • su2Log (loopVar s ell (prodCfgX flatCfg a) c x) := by
    funext a
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [qsmul_real, rat_cast_Wt]
  rw [e]
  exact h

theorem hasD1_avg (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    HasD1 (fun a : XS L => stridedBlockedGauge su2LogExp s ell (prodCfgX flatCfg a) c) (Davg s ell c) := by
  unfold stridedBlockedGauge Davg
  have h1 : HasD1 (fun a : XS L => su2Exp (∑ x ∈ stepBlockOf c.1 s ell,
      ((ell : ℚ) ^ 3)⁻¹ • su2Log (loopVar s ell (prodCfgX flatCfg a) c x)))
      (∑ x ∈ stepBlockOf c.1 s ell, Wt ell • Tloop s ell c x) := by
    refine hasD1_su2Exp (hasFDerivAt_sum_log_loop s ell c) ?_ ?_ ?_
    · refine Finset.sum_eq_zero (fun x _ => ?_)
      have : loopVar s ell (prodCfgX flatCfg (0 : XS L)) c x = 1 := (hasD1_loop s ell c x).1
      rw [this, su2Log_one, smul_zero]
    · intro a
      exact (sum_qsmul_su2Log_mem (stepBlockOf c.1 s ell) (((ell : ℚ) ^ 3)⁻¹)
        (fun x => loopVar s ell (prodCfgX flatCfg a) c x)).1
    · intro a
      exact (sum_qsmul_su2Log_mem (stepBlockOf c.1 s ell) (((ell : ℚ) ^ 3)⁻¹)
        (fun x => loopVar s ell (prodCfgX flatCfg a) c x)).2
  have h2 := hasD1_hol s c.1 (List.replicate ell c.2)
  simpa [su2LogExp_log, su2LogExp_exp, coarseBondVar] using h1.mul h2

#print axioms hasD1_avg

end AdalyFormal.IngredientFamilyR2
