import ZR2A
import AdalyFormal.Balaban.Bch2
import AdalyFormal.Balaban.RegularUQChain
import AdalyFormal.Balaban.SuTwoLogExpTorus

/-!
# R2B2 -- the regularity class is smallness-restricted: a large-holonomy `U` is NOT in it.
Core: `‖exp(i c A) − 1‖_F ≤ |c| ‖A‖_F` (from the tree's closed forms), plaquette telescoping,
and the plaquette with holonomy `−1` (`‖−1 − 1‖_F = 2√2`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (HT)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.Bch2

abbrev G2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- `‖exp(i c A) − 1‖_F ≤ |c| ‖A‖_F` for `A` Hermitian traceless, when `|c|‖A‖_F ≤ 1`. -/
theorem frob_exp_sub_one_le {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : HT A) (c : ℝ)
    (hc : |c| * frobNorm A ≤ 1) (g : G2)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (((c : ℂ) * Complex.I) • A)) :
    frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ |c| * frobNorm A := by
  set X : Matrix (Fin 2) (Fin 2) ℂ := ((c : ℂ) * Complex.I) • A with hX
  have hXs : IsSu2 X := by
    refine ⟨?_, ?_⟩
    · rw [hX, Matrix.conjTranspose_smul, hA.1]
      simp [star_mul', neg_smul, mul_comm]
    · rw [hX, Matrix.trace_smul, hA.2, smul_zero]
  -- frobSq X = c^2 frobSq A
  have hfs : frobSq X = c ^ 2 * frobSq A := by
    have h1 : X = c • (Complex.I • A) := by
      rw [hX, ← Complex.coe_smul, smul_smul]
    have h2 : frobSq (Complex.I • A) = frobSq A := by
      simp [frobSq, Matrix.smul_apply, Complex.normSq_mul]
    rw [h1, frobSq_smul, h2]
  have hnorm : frobNorm X = |c| * frobNorm A := by
    unfold frobNorm; rw [hfs, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  have hnu : nu X ≤ Real.pi := by
    have h1 : nu X ≤ frobNorm X := by
      rw [frobNorm_eq_sqrt_two_mul_nu]
      have := nu_nonneg X
      have h2 : (1:ℝ) ≤ Real.sqrt 2 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith
    have h3 : Real.pi ≥ 3 := by linarith [Real.pi_gt_three]
    rw [hnorm] at h1
    linarith
  have hexpmem : NormedSpace.exp X ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := g.2 |> fun h => by
    rw [← hg]; exact h
  have hgs : su2Exp X = g := by
    apply Subtype.ext
    rw [su2Exp_of_mem hexpmem, hg]
  have hang : su2Angle g = nu X := by
    rw [← hgs]; exact angle_exp hXs hnu
  have hsq := frobSq_su2_sub_one g
  rw [hang] at hsq
  have hcos := one_sub_cos_le (x := nu X)
  have hcos' : 1 - Real.cos (nu X) ≤ nu X ^ 2 / 2 := by
    have := abs_le.mp hcos
    linarith [this.1, this.2]
  have hle : frobSq ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ frobSq X := by
    rw [hsq]
    have := nu_sq X
    nlinarith
  calc frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ frobNorm X := by
        unfold frobNorm; exact Real.sqrt_le_sqrt hle
    _ = |c| * frobNorm A := hnorm


/-! ## plaquette holonomy and its gauge covariance -/

open AdalyFormal.StatementLane (CubeBond siteBox bigSide IsClassCube)

noncomputable def dist1 (g : G2) : ℝ := frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1)

def plaq {L : PeriodicLatticeExtent} (U : LinkCfg L) (z : PeriodicLatticeSite L) : G2 :=
  U (z, 0) * U (periodicLatticeShift z 0, 1) * (U (periodicLatticeShift z 1, 0))⁻¹ * (U (z, 1))⁻¹

theorem shift_comm01 {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L) :
    periodicLatticeShift (periodicLatticeShift z 0) 1
      = periodicLatticeShift (periodicLatticeShift z 1) 0 := by
  funext ν
  fin_cases ν <;> simp [periodicLatticeShift, Function.update]

theorem plaq_gauge {L : PeriodicLatticeExtent} (g : PeriodicLatticeSite L → G2) (U : LinkCfg L)
    (z : PeriodicLatticeSite L) :
    plaq (periodicGaugeTransform g U) z = g z * plaq U z * (g z)⁻¹ := by
  unfold plaq periodicGaugeTransform
  simp only []
  rw [← shift_comm01 z]
  group

noncomputable def badU {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L) : LinkCfg L :=
  fun e => if e = (periodicLatticeShift z 0, 1) then su2NegOne else 1

theorem plaq_badU {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L)
    (hz : periodicLatticeShift z 0 ≠ z) : plaq (badU z) z = su2NegOne := by
  unfold plaq badU
  have h1 : ((z, (0 : Fin 3)) : PeriodicLatticeSite L × Fin 3) ≠ (periodicLatticeShift z 0, 1) := by
    simp
  have h2 : ((periodicLatticeShift z 1, (0 : Fin 3)) : PeriodicLatticeSite L × Fin 3)
      ≠ (periodicLatticeShift z 0, 1) := by simp
  have h3 : ((z, (1 : Fin 3)) : PeriodicLatticeSite L × Fin 3) ≠ (periodicLatticeShift z 0, 1) := by
    simp only [ne_eq, Prod.mk.injEq, and_true]
    exact fun h => hz h.symm
  simp [h1, h2, h3]

theorem conj_negOne (g : G2) : g * su2NegOne * g⁻¹ = su2NegOne := by
  have h : g * su2NegOne = su2NegOne * g := by
    apply Subtype.ext
    simp
  rw [h]; group

theorem dist1_negOne : dist1 su2NegOne = 2 * Real.sqrt 2 := by
  unfold dist1
  exact AdalyFormal.Balaban.RegularityGap.frobNorm_negOne_sub_one

theorem dist1_mul (a b : G2) : dist1 (a * b) ≤ dist1 a + dist1 b :=
  AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le a b

theorem dist1_inv (a : G2) : dist1 a⁻¹ = dist1 a :=
  AdalyFormal.Balaban.RegularUQChain.frobNorm_su_inv_sub_one a

/-- the plaquette of four group elements each within `r` of `1` is within `4r` of `1` -/
theorem dist1_plaq4 (a b c d : G2) : dist1 (a * b * c⁻¹ * d⁻¹) ≤ dist1 a + dist1 b + dist1 c + dist1 d := by
  have h1 := dist1_mul (a * b * c⁻¹) d⁻¹
  have h2 := dist1_mul (a * b) c⁻¹
  have h3 := dist1_mul a b
  rw [dist1_inv] at h1 h2
  linarith

#print axioms plaq_gauge
#print axioms plaq_badU
#print axioms dist1_plaq4

end AdalyFormal.StatementLane2
