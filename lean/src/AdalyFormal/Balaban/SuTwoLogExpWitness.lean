/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.SuTwoLogExpTorus
import AdalyFormal.Balaban.BlockedGaugeSeparation

set_option autoImplicit false
set_option maxRecDepth 40000

/-!
# `Ū` AT `SU(2)`: THE MUST-FIRE CONTROL FIRES, AND COVARIANCE IS INSTANTIATED

`BlockedGaugeWitness.blockedGauge_trivialLogExp` is the control: the degenerate `trivialLogExp`
satisfies every `LogExpAd` law and yields `Ū(c) = U(c)` exactly — no averaging at all. An
inhabitant of `Averaging.GaugeCovariant` built from it is worth nothing.

**This module proves that `SuTwoLogExpCore.su2LogExp` FAILS that control.** On a pinned
`4`-sites-per-direction periodic lattice with `ell = 2` (so `|B(c_-)| = 8 = 2^3` and Bałaban's
`L^{-d}` weight is exactly the block average), a pinned `SU(2)`-valued configuration `sU` and a
pinned coarse bond `wc`:

* `su2_blockedGauge_eq_torus` : `Ū(wc) = torus E` with `E` the (0.4) exponent of the abelian model;
* `su2_blockedGauge_ne_coarseHolonomy` : `Ū(wc) ≠ U(wc)`. **The control fires.**

and the covariance theorem is applied at a concrete point (the builder of `BlockedGaugeCore`
disclosed that no call site anywhere did that):

* `su2_blockedGauge_gauge_pinned` : `blockedGauge_gauge` at `su2LogExp`, `ell = 2`, the pinned
  lattice/bond/configuration and a pinned NON-CONSTANT gauge function `wGamma`;
* `su2_gaugeCovariant` : `Averaging.GaugeCovariant` inhabited at `SU(2)`.

## Method — nothing is evaluated numerically, and the `decide`s carry no ℚ

`ℚ` does not kernel-reduce in this Lean (`BlockedGaugeSeparation`'s own measurement). The bridge to
`SU(2)` is a group homomorphism `Φ : Multiplicative ℚ →* SU(2)`, `Φ(ofAdd t) = torus t`, together
with the `ℚ`-linear `ψ : ℚ →ₗ[ℚ] M₂(ℂ)`, `ψ(a) = a • J`. The two compatibilities

* `su2Exp (ψ a) = Φ (ofAdd a)` — for EVERY `a`, from `Matrix.exp_diagonal`;
* `su2Log (Φ (ofAdd a)) = ψ a` — for `0 ≤ a < π`, from `Real.arccos_cos`

let every (0.4) loop logarithm be transported. The branch condition `0 ≤ a < π` is discharged by a
**ℚ-free `decide`**: `contour_bondCount_le_one` counts, over the finite block and the finite contour
families, how many times a contour traverses the single excited bond — never more than once — so
every loop value lies in `[0, 1] ⊂ [0, π)`.
-/

namespace AdalyFormal.Balaban.SuTwoLogExp

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.BlockedGauge
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice)

/-! ## §1. Transport of a holonomy along a group homomorphism -/

theorem holonomy_map {G H : Type*} [Group G] [Group H] (F : G →* H)
    {L : PeriodicLatticeExtent} (U : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (s : List (Fin 3 × Bool)) :
    periodicPathHolonomy (fun b => F (U b)) y s = F (periodicPathHolonomy U y s) := by
  induction s generalizing y with
  | nil => simp [periodicPathHolonomy]
  | cons st rest ih =>
      simp only [periodicPathHolonomy]
      rw [ih (periodicLatticeStep y st), map_mul]
      congr 1
      by_cases hb : st.2 = true <;> simp [hb]

/-! ## §2. The bridge `Multiplicative ℚ → SU(2)` and `ℚ → su(2)` -/

/-- `Φ(ofAdd t) = diag(e^{it}, e^{-it})`: a genuine group homomorphism into `SU(2)`. -/
noncomputable def phiSU2 : Multiplicative ℚ →* SU2 where
  toFun x := torus ((Multiplicative.toAdd x : ℚ) : ℝ)
  map_one' := by
    show torus ((Multiplicative.toAdd (1 : Multiplicative ℚ) : ℚ) : ℝ) = 1
    simpa using torus_zero
  map_mul' x y := by
    show torus ((Multiplicative.toAdd (x * y) : ℚ) : ℝ)
      = torus ((Multiplicative.toAdd x : ℚ) : ℝ) * torus ((Multiplicative.toAdd y : ℚ) : ℝ)
    rw [show Multiplicative.toAdd (x * y)
        = Multiplicative.toAdd x + Multiplicative.toAdd y from rfl]
    push_cast
    exact torus_add _ _

@[simp] theorem phiSU2_apply (a : ℚ) : phiSU2 (Multiplicative.ofAdd a) = torus ((a : ℚ) : ℝ) := rfl

/-- `ℚ`-scalars act on `M₂(ℂ)` through the cast `ℚ → ℂ`. -/
theorem rat_smul_M2 (q : ℚ) (M : M2) : q • M = ((q : ℂ)) • M := by
  ext i j
  simp [Matrix.smul_apply, Rat.smul_def]

/-- `ψ(a) = a • J`, `ℚ`-linear by construction. -/
noncomputable def psiL : ℚ →ₗ[ℚ] M2 := LinearMap.toSpanSingleton ℚ M2 su2J

theorem psiL_apply (a : ℚ) : psiL a = psiR ((a : ℚ) : ℝ) := by
  show a • su2J = psiR ((a : ℚ) : ℝ)
  rw [rat_smul_M2, psiR]
  congr 1

/-- **`exp ∘ ψ = Φ ∘ ofAdd`, for EVERY rational.** No branch restriction. -/
theorem su2Exp_psiL (a : ℚ) : su2Exp (psiL a) = phiSU2 (Multiplicative.ofAdd a) := by
  rw [psiL_apply, su2Exp_psiR, phiSU2_apply]

/-- **`log ∘ Φ ∘ ofAdd = ψ` on the principal branch.** -/
theorem su2Log_phiSU2 {a : ℚ} (h0 : 0 ≤ a) (h1 : (a : ℝ) < Real.pi) :
    su2Log (phiSU2 (Multiplicative.ofAdd a)) = psiL a := by
  rw [phiSU2_apply, psiL_apply]
  exact su2Log_torus (by exact_mod_cast h0) h1

/-! ## §3. Counting bond traversals — the ℚ-free bound -/

variable {L : PeriodicLatticeExtent}

/-- How many times a forward bond list traverses a given bond. `ℕ`-valued, so it `decide`s. -/
def bondCount (b0 : PeriodicLatticeEdge L) : List (PeriodicLatticeEdge L) → ℕ
  | [] => 0
  | b :: rest => (if b = b0 then 1 else 0) + bondCount b0 rest

/-- The single-excited-bond field's forward sum IS the traversal count. -/
theorem fwdSum_eq_bondCount (b0 : PeriodicLatticeEdge L) (y : PeriodicLatticeSite L)
    (s : List (Fin 3 × Bool)) :
    fwdSum (fun b => if b = b0 then (1 : ℚ) else 0) y s = (bondCount b0 (fwdBonds y s) : ℚ) := by
  induction s generalizing y with
  | nil => simp [fwdSum, fwdBonds, bondCount]
  | cons st rest ih =>
      simp only [fwdSum, fwdBonds, bondCount, ih (periodicLatticeStep y st)]
      by_cases hb : ((y, st.1) : PeriodicLatticeEdge L) = b0 <;> simp [hb]

/-! ## §4. The pinned `SU(2)` configuration -/

/-- The `SU(2)` image of `BlockedGaugeSeparation`'s single-excited-bond configuration. Every link
is `1` except the direction-`1` bond at the origin, which carries `diag(e^{i}, e^{-i})`. -/
noncomputable def sU : PeriodicLinkConfiguration SU2 witLw := fun b => phiSU2 (wU b)

/-- **The ℚ-free `decide`d bound.** No contour of `G(c_-, x)` traverses the excited bond more than
once, over the whole block. Enumerated over `Fin`/`List`/`ℕ` data only. -/
theorem contour_bondCount_le_one :
    ∀ x ∈ blockOf wc.1 2, ∀ Γ ∈ contourFamily wc.1 x,
      bondCount wB0 (fwdBonds wc.1 Γ) ≤ 1 := by decide

theorem wloop_val_nonneg {Γ : List (Fin 3 × Bool)} : 0 ≤ fwdSum wf wc.1 Γ :=
  fwdSum_nonneg wf wf_nonneg _ _

theorem wloop_val_le_one {x : PeriodicLatticeSite witLw} (hx : x ∈ blockOf wc.1 2)
    {Γ : List (Fin 3 × Bool)} (hΓ : Γ ∈ contourFamily wc.1 x) :
    fwdSum wf wc.1 Γ ≤ 1 := by
  have hcount := contour_bondCount_le_one x hx Γ hΓ
  have hrw : fwdSum wf wc.1 Γ = (bondCount wB0 (fwdBonds wc.1 Γ) : ℚ) := by
    rw [show wf = (fun b => if b = wB0 then (1 : ℚ) else 0) from rfl]
    exact fwdSum_eq_bondCount wB0 wc.1 Γ
  rw [hrw]
  exact_mod_cast hcount

/-- **The (0.4) loop logarithm at `SU(2)`, transported.** -/
theorem su2_loop_log {x : PeriodicLatticeSite witLw} (hx : x ∈ blockOf wc.1 2)
    {Γ : List (Fin 3 × Bool)} (hΓ : Γ ∈ contourFamily wc.1 x)
    {Γ' : List (Fin 3 × Bool)} (hΓ' : Γ' ∈ contourFamily (cPlus 2 wc) (shiftBy x wc.2 2)) :
    su2LogExp.log (periodicPathHolonomy sU wc.1 (loopSteps 2 wc.2 Γ Γ'))
      = psiL (ratLogExp.log (periodicPathHolonomy wU wc.1 (loopSteps 2 wc.2 Γ Γ'))) := by
  have hval := wloop_log hx hΓ hΓ'
  have h0 : (0 : ℚ) ≤ fwdSum wf wc.1 Γ := wloop_val_nonneg
  have h1 : fwdSum wf wc.1 Γ ≤ 1 := wloop_val_le_one hx hΓ
  have hpi : ((fwdSum wf wc.1 Γ : ℚ) : ℝ) < Real.pi := by
    have : ((fwdSum wf wc.1 Γ : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith [Real.pi_gt_three]
  have hmap : periodicPathHolonomy sU wc.1 (loopSteps 2 wc.2 Γ Γ')
      = phiSU2 (periodicPathHolonomy wU wc.1 (loopSteps 2 wc.2 Γ Γ')) :=
    holonomy_map phiSU2 wU wc.1 _
  have hoa : periodicPathHolonomy wU wc.1 (loopSteps 2 wc.2 Γ Γ')
      = Multiplicative.ofAdd (fwdSum wf wc.1 Γ) := by
    rw [← hval]; rfl
  rw [hmap, hval, hoa]
  exact su2Log_phiSU2 h0 hpi

/-! ## §5. The (0.4) exponent, transported and bounded -/

/-- The (0.4) exponent of the abelian model. `wexponent_pos` gives `0 < wE`. -/
noncomputable def wE : ℚ :=
  ∑ x ∈ blockOf wc.1 2, (((2 : ℕ) : ℚ) ^ 3)⁻¹ • innerAvg ratLogExp 2 wU wc x

theorem wE_pos : 0 < wE := wexponent_pos

/-- Weighted averages with uniform weights are bounded by the bound on the summands. -/
theorem weighted_le_one {ι : Type*} (F : Finset ι) (hF : 0 < F.card) (f : ι → ℚ)
    (hf : ∀ i ∈ F, f i ≤ 1) : ∑ i ∈ F, ((F.card : ℚ))⁻¹ • f i ≤ 1 := by
  have hc : (0 : ℚ) < (F.card : ℚ) := by exact_mod_cast hF
  have hstep : ∑ i ∈ F, ((F.card : ℚ))⁻¹ • f i ≤ ∑ i ∈ F, ((F.card : ℚ))⁻¹ • (1 : ℚ) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hf i hi) (le_of_lt (inv_pos.mpr hc))
  refine hstep.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, smul_eq_mul, mul_one]
  rw [mul_inv_cancel₀ (ne_of_gt hc)]

theorem winner_le_one {x : PeriodicLatticeSite witLw} (hx : x ∈ blockOf wc.1 2) :
    innerAvg ratLogExp 2 wU wc x ≤ 1 := by
  classical
  simp only [innerAvg]
  refine weighted_le_one _ (contourFamily_card_pos wc.1 x) _ (fun Γ hΓ => ?_)
  refine weighted_le_one _ (contourFamily_card_pos _ _) _ (fun Γ' hΓ' => ?_)
  rw [wloop_log hx hΓ hΓ']
  exact wloop_val_le_one hx hΓ

theorem block_card : (blockOf wc.1 2).card = 8 := by
  have hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (witLw μ + 1) := by decide
  have := card_blockOf (L := witLw) (ell := 2) (by norm_num) hdvd w_coarse
  simpa using this

theorem wE_le_one : wE ≤ 1 := by
  classical
  have hcard : (blockOf wc.1 2).card = 8 := block_card
  have : wE ≤ ∑ _x ∈ blockOf wc.1 2, (((2 : ℕ) : ℚ) ^ 3)⁻¹ • (1 : ℚ) := by
    refine Finset.sum_le_sum (fun x hx => ?_)
    rw [smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (winner_le_one hx) (by norm_num)
  refine this.trans ?_
  rw [Finset.sum_const, hcard, nsmul_eq_mul, smul_eq_mul, mul_one]
  norm_num

/-! ## §6. `Ū` at `SU(2)`, evaluated -/

/-- Pushing `ψ` through a uniformly-weighted finite sum. Stated once so neither `su2_innerAvg`
nor `su2_exponent` needs `congr` on a `•` (which times out here). -/
theorem psiL_sum_smul {ι : Type*} (F : Finset ι) (w : ℚ) (g : ι → M2) (h : ι → ℚ)
    (hgh : ∀ i ∈ F, g i = psiL (h i)) :
    ∑ i ∈ F, w • g i = psiL (∑ i ∈ F, w • h i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [map_smul, hgh i hi]

theorem su2_innerAvg {x : PeriodicLatticeSite witLw} (hx : x ∈ blockOf wc.1 2) :
    innerAvg su2LogExp 2 sU wc x = psiL (innerAvg ratLogExp 2 wU wc x) := by
  simp only [innerAvg]
  refine psiL_sum_smul _ _ _ _ (fun Γ hΓ => ?_)
  exact psiL_sum_smul _ _ _ _ (fun Γ' hΓ' => su2_loop_log hx hΓ hΓ')

theorem su2_exponent :
    (∑ x ∈ blockOf wc.1 2, (((2 : ℕ) : ℚ) ^ 3)⁻¹ • innerAvg su2LogExp 2 sU wc x) = psiL wE := by
  rw [wE]
  exact psiL_sum_smul _ _ _ _ (fun x hx => su2_innerAvg hx)

/-- The bare coarse holonomy of the pinned configuration is trivial: the coarse bond runs in
direction `0`, the excited bond in direction `1`. -/
theorem su2_coarse_holonomy : periodicPathHolonomy sU wc.1 (straightSeg wc.2 2) = 1 := by
  rw [show sU = (fun b => phiSU2 (wU b)) from rfl, holonomy_map phiSU2 wU wc.1 _, wH_eq_one,
    map_one]

/-- **`Ū(wc) = torus E`** — the (0.4) object at `SU(2)`, evaluated in closed form. -/
theorem su2_blockedGauge_eq_torus :
    blockedGauge su2LogExp 2 sU wc = torus ((wE : ℚ) : ℝ) := by
  simp only [blockedGauge, su2LogExp_exp]
  rw [su2_exponent, su2_coarse_holonomy, mul_one, su2Exp_psiL, phiSU2_apply]

/-! ## §7. THE MUST-FIRE CONTROL -/

theorem torus_ne_one {t : ℝ} (h0 : 0 < t) (h1 : t < 2 * Real.pi) : torus t ≠ 1 := by
  intro h
  have h2 : torusM t = (1 : M2) := by
    have := congrArg (fun g : SU2 => (g : M2)) h
    rwa [coe_torus, coe_one] at this
  have h3 : Complex.exp ((t : ℂ) * Complex.I) = 1 := by
    have := congrFun (congrFun h2 0) 0
    rwa [torusM, dg_00, Matrix.one_apply_eq] at this
  have h4 : Real.cos t = 1 := by
    have := congrArg Complex.re h3
    rwa [cexp_re, Complex.one_re] at this
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h5 : t = 0 := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) h1).mp h4
  linarith

/-- **THE MUST-FIRE CONTROL FIRES AT `SU(2)`: `Ū(c) ≠ U(c)`.**

`BlockedGaugeWitness.blockedGauge_trivialLogExp` proves the degenerate `LogExpAd` gives
`Ū(c) = U(c)` exactly. This instance does not: on the pinned lattice/bond/configuration the blocked
field is `torus E` with `0 < E ≤ 1`, while the bare coarse holonomy is `1`. So the `SU(2)`
inhabitant of `Averaging.GaugeCovariant` below is NOT the decoration. -/
theorem su2_blockedGauge_ne_coarseHolonomy :
    blockedGauge su2LogExp 2 sU wc ≠ periodicPathHolonomy sU wc.1 (straightSeg wc.2 2) := by
  rw [su2_blockedGauge_eq_torus, su2_coarse_holonomy]
  refine torus_ne_one ?_ ?_
  · exact_mod_cast wE_pos
  · have h1 : ((wE : ℚ) : ℝ) ≤ 1 := by exact_mod_cast wE_le_one
    linarith [Real.pi_gt_three]

/-- The same separation stated against the degenerate instance itself. -/
theorem su2_blockedGauge_ne_trivialLogExp :
    blockedGauge su2LogExp 2 sU wc ≠ blockedGauge (trivialLogExp SU2 ℚ) 2 sU wc := by
  rw [blockedGauge_trivialLogExp]
  exact su2_blockedGauge_ne_coarseHolonomy

/-- …and `Ū` at `SU(2)` is not the trivial element either. -/
theorem su2_blockedGauge_ne_one : blockedGauge su2LogExp 2 sU wc ≠ 1 := by
  rw [su2_blockedGauge_eq_torus]
  refine torus_ne_one ?_ ?_
  · exact_mod_cast wE_pos
  · have h1 : ((wE : ℚ) : ℝ) ≤ 1 := by exact_mod_cast wE_le_one
    linarith [Real.pi_gt_three]

/-! ## §8. Degenerate points, and covariance INSTANTIATED -/

/-- `ell = 1`: a one-site block gives `Ū(c) = U(c)` at `SU(2)` too — the flagged degenerate point,
proved rather than assumed. Every must-fire control above uses `ell = 2`. -/
theorem su2_blockedGauge_ell_one (U : PeriodicLinkConfiguration SU2 witLw) (c : CoarseBond witLw) :
    blockedGauge su2LogExp 1 U c = periodicPathHolonomy U c.1 (straightSeg c.2 1) :=
  blockedGauge_ell_one su2LogExp su2Log_one su2Exp_zero U c

/-- A pinned NON-CONSTANT gauge function: `γ(y) = torus (y₁)`. -/
noncomputable def wGamma : PeriodicLatticeSite witLw → SU2 := fun y => torus ((y 1).val : ℝ)

theorem torus_zero_ne_torus_one : torus 0 ≠ torus 1 := by
  rw [torus_zero]
  intro h
  exact torus_ne_one (t := 1) (by norm_num) (by linarith [Real.pi_gt_three]) h.symm

theorem wGamma_nonconstant : wGamma (fun _ => 0) ≠ wGamma wX0 := by
  have h0 : wGamma (fun _ => 0) = torus 0 := by simp [wGamma]
  have h1 : wGamma wX0 = torus 1 := by simp [wGamma, wX0]
  rw [h0, h1]
  exact torus_zero_ne_torus_one

/-- **`blockedGauge_gauge` APPLIED AT A CONCRETE POINT.** Every parameter is a pinned `def`: the
lattice `witLw` (4 sites per direction), `ell = 2`, the coarse bond `wc`, the `SU(2)`
configuration `sU`, and the non-constant gauge function `wGamma`. No existential over free data. -/
theorem su2_blockedGauge_gauge_pinned :
    blockedGauge su2LogExp 2 (periodicGaugeTransform wGamma sU) wc
      = coarseGaugeTransform 2 wGamma (blockedGauge su2LogExp 2 sU) wc :=
  blockedGauge_gauge su2LogExp (by norm_num) wGamma sU wc w_dvd w_coarse

/-- The same at an arbitrary gauge function, still at the pinned lattice/bond/configuration. -/
theorem su2_blockedGauge_gauge_concrete (γ : PeriodicLatticeSite witLw → SU2) :
    blockedGauge su2LogExp 2 (periodicGaugeTransform γ sU) wc
      = coarseGaugeTransform 2 γ (blockedGauge su2LogExp 2 sU) wc :=
  blockedGauge_gauge su2LogExp (by norm_num) γ sU wc w_dvd w_coarse

/-- **`Averaging.GaugeCovariant` INHABITED AT `SU(2)`**, by the (0.4) object with the genuine
`SU(2)` logarithm and exponential — not by the degenerate pair. -/
theorem su2_gaugeCovariant :
    AdalyFormal.Balaban.GaugeCovariant
      (FineConfig := PeriodicLinkConfiguration SU2 witLw)
      (CoarseConfig := {c : CoarseBond witLw // c.2 = 0 ∧ c.1 ∈ CoarseLattice witLw 2} → SU2)
      (GaugeFn := PeriodicLatticeSite witLw → SU2)
      periodicGaugeTransform
      (fun γ V c => γ (c : CoarseBond witLw).1 * V c * (γ (cPlus 2 (c : CoarseBond witLw)))⁻¹)
      (fun U c => blockedGauge su2LogExp 2 U (c : CoarseBond witLw)) :=
  gaugeCovariant_blockedGauge su2LogExp (by norm_num) 0 (by decide)

end AdalyFormal.Balaban.SuTwoLogExp
