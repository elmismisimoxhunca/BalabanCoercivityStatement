/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CoercivityTargetsCorrected
import AdalyFormal.Balaban.HrefReduction
import AdalyFormal.Balaban.BlockPoincareLemma24

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `[SU2-GEOM-U1]` — the su(2) analogue of CMP96 (2.128) at `U=1`, LIFTED component-wise from the
scalar milestone.

This module lifts the PROVED scalar `U=1` Bałaban Lemma 2.4 / (2.128) milestone
(`HrefReduction.lemma24_unconditional_U1_ell2_uncond` :
`Lemma24Conclusion 2 B` for admissible `B : Bond L → ℝ`) to the su(2)-valued additive coercivity
`CoercivityTargetsCorrected.SuTwoGeomAdditiveInequality` at the trivial background `trivialU`.

## The mechanism (component-wise lift)

`𝔰𝔲(2) ≅ ℝ³` orthonormally for `SuTwoInner.hsInner`, with the three coordinate functionals
`suCoordLM i` read off the Pauli basis (`SuTwoInner.suTwo_decompose`). At `U=1`:

* the covariant curl `curlCovariantLM (trivialU)` is the FLAT su(2) curl `flatCurlValue`
  (`CovU1Reduction.curlCovariantLM_trivialU_eq_flatCurlLM`), whose formula is LITERALLY the scalar
  `LatticeOperators.curlValue` on each real coordinate, and
* the covariant averaging `lineCoarseRestrictCovLM (trivialU) ell` is the flat SuTwo block average
  `LineIntegralCovariant.lineCoarseRestrictSuTwo` (`lineCoarseRestrictCov_trivialU`), whose formula
  is LITERALLY the scalar `LineIntegralAveraging.lineCoarseRestrict` on each real coordinate.

Because each coordinate `suCoordLM i` is `ℝ`-linear and the su(2) operators are the scalar operators
applied entrywise, each of the three su(2) energies decomposes as a SUM over `i : Fin 3` of the
scalar energy of the `i`-th real component field `suComp i A0 = fun b => suCoordLM i (A0 b)`:

* `covBondInner A0 A0            = ∑ i, bondNormSq (suComp i A0)`
* `covPlaqInner (curl…) (curl…)  = ∑ i, totalCurlEnergy (suComp i A0)`   (at `U=1`)
* `covCoarseBondInner (Q…) (Q…)  = ∑ i, coarseQEnergy 2 (suComp i A0)`   (at `U=1`)

The su(2) (2.128) at `U=1` is then the sum of three copies of the scalar (2.128), one per component.

## HONEST SCOPE (§LEAN-D / no-success-lie)

* **`U=1` ONLY.** The regular-`U` case (the open frontier) is untouched. Every reduction uses
  `curlCovariantLM_trivialU_eq_flatCurlLM` / `lineCoarseRestrictCov_trivialU`, valid only at
  `trivialU`.
* **CONDITIONAL ON ADMISSIBILITY.** `SuTwoGeomAdditiveInequality` is a bare `∀ A0` `Prop` with NO
  admissibility restriction, but the scalar milestone REQUIRES `B ∈ admissibleSubspaceInter L 2`
  (Bałaban's axial gauge (2.121); without it the coarse+curl energies do not control `‖B‖²`). So the
  main theorem carries the su(2) axial-gauge hypothesis `hadm` (`A0` vanishes on every staircase
  `Γ_{y,x}`), from which component-admissibility follows because `suCoordLM i 0 = 0`. The unrestricted
  `∀ A0` form is NOT proved (and is expected false by the same curl-kernel counterexample class as the
  scalar object off its gauge).
* **This is the ADDITIVE (2.128), NOT `GaugeFixedCurlCoercivity`.** The additive object
  `ell·‖Q₁A‖² + ‖curl A‖² ≥ c‖A‖²` is a DIFFERENT statement from the fluctuation-subspace form
  `γ₀‖Q₁A‖² ≤ ‖curl A‖²` that `CoercivityTargetsCorrected.FaithfulCovCoercivityTargetGaugeFixed`
  reduces to. This module does NOT close that target; it establishes the su(2) (2.128) at `U=1`, the
  named §3 link of `CoercivityTargetsCorrected.lean`.
* **ISLAND.** Nothing here is wired to `coerc_u_main` or a consumed spine declaration.

`#print axioms` on every result below is `{propext, Classical.choice, Quot.sound}` — no `sorry`.
-/

namespace AdalyFormal.Balaban.SuTwoGeomU1

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovU1Reduction
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.CoercivityTargetsCorrected

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the three real coordinate functionals of `𝔰𝔲(2)`, as `ℝ`-linear maps -/

/-- **The `i`-th real coordinate of an `𝔰𝔲(2)` element**, w.r.t. the orthonormal Pauli basis
`{E₁,E₂,E₃}` of `SuTwoInner`: `suCoordLM 0 X = Im X₀₁`, `suCoordLM 1 X = Re X₀₁`,
`suCoordLM 2 X = Im X₀₀` — exactly the coefficients in `SuTwoInner.suTwo_decompose`. An `ℝ`-linear
map, so it commutes with `+`, `-`, `•` and `Finset.sum`. -/
noncomputable def suCoordLM (i : Fin 3) : SuTwo →ₗ[ℝ] ℝ where
  toFun X := match i with
    | 0 => ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im
    | 1 => ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re
    | 2 => ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im
  map_add' X Y := by
    fin_cases i <;>
      simp only [Submodule.coe_add, Matrix.add_apply, Complex.add_im, Complex.add_re]
  map_smul' r X := by
    fin_cases i <;>
      simp only [SetLike.val_smul, Matrix.smul_apply, Complex.real_smul, Complex.mul_im,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, RingHom.id_apply, smul_eq_mul] <;>
      ring

/-- The `i`-th real component field of a bond-valued `𝔰𝔲(2)` configuration. -/
noncomputable def suComp (i : Fin 3) (A : Bond L → SuTwo) : Bond L → ℝ :=
  fun b => suCoordLM i (A b)

@[simp] theorem suComp_apply (i : Fin 3) (A : Bond L → SuTwo) (b : Bond L) :
    suComp i A b = suCoordLM i (A b) := rfl

/-! ## §2 — `hsInner` is the standard `ℝ³` dot product in these coordinates -/

/-- **`⟪X,Y⟫ = ∑ᵢ (suCoordLM i X)(suCoordLM i Y)`** — the orthonormal-basis expansion of `hsInner`.
Proved from `suTwo_decompose` and the orthonormality values `hsInner_eᵢ_eⱼ` of `SuTwoInner`
(reused, LAW-19), so it consumes exactly the normalization pinned there. -/
theorem hsInner_eq_sum_coord (X Y : SuTwo) :
    hsInner X Y = ∑ i : Fin 3, suCoordLM i X * suCoordLM i Y := by
  have ar : ∀ A B C : SuTwo, hsInner A (B + C) = hsInner A B + hsInner A C := by
    intro A B C
    rw [hsInner_symm A, hsInner_add_left, hsInner_symm B A, hsInner_symm C A]
  have sr : ∀ (r : ℝ) (A B : SuTwo), hsInner A (r • B) = r * hsInner A B := by
    intro r A B
    rw [hsInner_symm A, hsInner_smul_left, hsInner_symm B A]
  have e21 : hsInner pauliE2 pauliE1 = 0 := by rw [hsInner_symm]; exact hsInner_e1_e2
  have e31 : hsInner pauliE3 pauliE1 = 0 := by rw [hsInner_symm]; exact hsInner_e1_e3
  have e32 : hsInner pauliE3 pauliE2 = 0 := by rw [hsInner_symm]; exact hsInner_e2_e3
  rw [Fin.sum_univ_three]
  conv_lhs => rw [suTwo_decompose X, suTwo_decompose Y]
  simp only [hsInner_add_left, hsInner_smul_left, ar, sr,
    hsInner_e1_e1, hsInner_e2_e2, hsInner_e3_e3, hsInner_e1_e2, hsInner_e1_e3, hsInner_e2_e3,
    e21, e31, e32]
  show _ = ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im * ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im
      + ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re * ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re
      + ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im * ((Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im
  ring

#print axioms suCoordLM
#print axioms hsInner_eq_sum_coord

/-! ## §3 — the su(2) operators at `U=1` are the scalar operators applied coordinate-wise -/

/-- **`suCoordLM i (flatCurlValue A p) = curlValue (suComp i A) p`** — the flat su(2) curl and the
scalar curl are LITERALLY the same signed 4-bond combination (`CovU1Reduction.flatCurlValue` vs
`LatticeOperators.curlValue`), so pushing the linear coordinate through is definitional after the
linearity rewrites. -/
theorem suCoordLM_flatCurlValue (i : Fin 3) (A : Bond L → SuTwo)
    (p : PeriodicLatticePlaquette L) :
    suCoordLM i (flatCurlValue A p) = curlValue (suComp i A) p := by
  simp only [flatCurlValue, curlValue, suComp_apply, map_add, map_sub]

/-- **`suCoordLM i (lineCoarseRestrictSuTwo ell A c) = lineCoarseRestrict ell (suComp i A) c`** — the
flat SuTwo block average and the scalar block average are the same `(1/ell⁴)·Σ_x Σ_j` combination
(`LineIntegralCovariant.lineCoarseRestrictSuTwo` vs `LineIntegralAveraging.lineCoarseRestrict` with
`lineIntegralValue`), with `pathSite = shift^[·]`. The coordinate commutes with the scalar factor and
the two nested sums by linearity. -/
theorem suCoordLM_lineCoarseRestrictSuTwo (i : Fin 3) (ell : ℕ) (A : Bond L → SuTwo)
    (c : CoarseBond L ell) :
    suCoordLM i (lineCoarseRestrictSuTwo ell A c)
      = lineCoarseRestrict ell (suComp i A) c := by
  simp only [lineCoarseRestrictSuTwo, lineCoarseRestrict, lineIntegralValue,
    QOne.pathSite, suComp_apply, map_smul, map_sum, smul_eq_mul]

#print axioms suCoordLM_flatCurlValue
#print axioms suCoordLM_lineCoarseRestrictSuTwo

/-! ## §4 — each su(2) energy = `∑ᵢ` (scalar energy of the `i`-th component field) -/

/-- **`covBondInner A A = ∑ᵢ bondNormSq (suComp i A)`.** -/
theorem covBondInner_eq_sum (A : Bond L → SuTwo) :
    covBondInner A A = ∑ i : Fin 3, bondNormSq (suComp i A) := by
  unfold covBondInner bondNormSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hsInner_eq_sum_coord]
  apply Finset.sum_congr rfl
  intro i _
  rw [suComp_apply, sq]

/-- **`covPlaqInner (flatCurlValue A) (flatCurlValue A) = ∑ᵢ totalCurlEnergy (suComp i A)`** — the
`U=1` covariant curl energy decomposes into the three scalar curl energies. -/
theorem covPlaqInner_flatCurl_eq_sum (A : Bond L → SuTwo) :
    covPlaqInner (flatCurlValue A) (flatCurlValue A)
      = ∑ i : Fin 3, totalCurlEnergy (suComp i A) := by
  unfold covPlaqInner totalCurlEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [hsInner_eq_sum_coord]
  apply Finset.sum_congr rfl
  intro i _
  rw [suCoordLM_flatCurlValue, sq]

/-- **`covCoarseBondInner (Q A) (Q A) = ∑ᵢ coarseQEnergy ell (suComp i A)`** for the flat SuTwo
average `Q = lineCoarseRestrictSuTwo` — the `U=1` covariant coarse-average energy decomposes into the
three scalar coarse energies. -/
theorem covCoarseBondInner_lineCoarse_eq_sum (ell : ℕ) (A : Bond L → SuTwo) :
    covCoarseBondInner (fun c => lineCoarseRestrictSuTwo ell A c)
        (fun c => lineCoarseRestrictSuTwo ell A c)
      = ∑ i : Fin 3, coarseQEnergy ell (suComp i A) := by
  unfold covCoarseBondInner coarseQEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [hsInner_eq_sum_coord]
  apply Finset.sum_congr rfl
  intro i _
  rw [suCoordLM_lineCoarseRestrictSuTwo, sq]

#print axioms covBondInner_eq_sum
#print axioms covPlaqInner_flatCurl_eq_sum
#print axioms covCoarseBondInner_lineCoarse_eq_sum

/-! ## §5 — component-admissibility: an axial-gauge su(2) field has scalar-admissible components -/

/-- If `A` vanishes on every staircase `Γ_{y,x}` (the su(2) axial gauge, the (2.121) analogue), then
each real component `suComp i A` lies in the scalar axial gauge `admissibleSubspaceInter L ell`,
because `suCoordLM i 0 = 0`. -/
theorem suComp_mem_admissible (ell : ℕ) (i : Fin 3) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A b = 0) :
    suComp i A ∈ admissibleSubspaceInter L ell := by
  rw [mem_admissibleSubspaceInter]
  intro y hy x hx b hb
  rw [suComp_apply, hadm y hy x hx b hb, map_zero]

#print axioms suComp_mem_admissible

/-! ## §6 — THE su(2) (2.128) AT `U=1`, LIFTED (the deliverable) -/

/-- **THE su(2) analogue of CMP96 (2.128) at `U=1`, `ell = 2`, from the scalar milestone.** For a
su(2) field `A0` on any compatible torus (`4 ≤ L μ`, `2 ∣ L μ + 1`) that satisfies the axial gauge
`hadm` (`A0` vanishes on every staircase `Γ_{y,x}`, the (2.121) analogue),
`SuTwoGeomAdditiveInequality 2 (trivialU L) ((1/108)·(1/2⁴)) A0` holds:

  `2·⟨Q₁A0, Q₁A0⟩ + ⟨curl A0, curl A0⟩  ≥  (1/108)·(1/2⁴)·⟨A0, A0⟩`   (su(2), at `U=1`).

Proof: at `U=1` the su(2) curl/average reduce to the flat operators, each su(2) energy decomposes
(§4) into three scalar energies of the components `suComp i A0`, each component is scalar-admissible
(§5), and the scalar milestone `HrefReduction.lemma24_unconditional_U1_ell2_uncond`
(`Lemma24Conclusion 2`) applies to each; summing the three scalar (2.128)'s gives the su(2) one.

`U=1` ONLY; CONDITIONAL on `hadm`; this is the additive (2.128), NOT `GaugeFixedCurlCoercivity`
(module docstring). -/
theorem suTwoGeomAdditive_trivialU_of_admissible
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A0 : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A0 b = 0) :
    SuTwoGeomAdditiveInequality 2 (trivialU L)
      ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4)) A0 := by
  -- reduce the two U=1 operators to their flat forms
  have hcurl : curlCovariantLM (trivialU L) A0 = flatCurlValue A0 := by
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  have hQ : lineCoarseRestrictCovLM (trivialU L) 2 A0
      = (fun c => lineCoarseRestrictSuTwo 2 A0 c) := by
    funext c
    rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_trivialU]
  unfold SuTwoGeomAdditiveInequality
  rw [hcurl, hQ, covBondInner_eq_sum, covPlaqInner_flatCurl_eq_sum,
    covCoarseBondInner_lineCoarse_eq_sum]
  -- now a per-component sum inequality
  rw [ge_iff_le]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hscalar := HrefReduction.lemma24_unconditional_U1_ell2_uncond hL hdvd
    (suComp i A0) (suComp_mem_admissible 2 i A0 hadm)
  rw [Lemma24Conclusion, ge_iff_le] at hscalar
  exact hscalar

#print axioms suTwoGeomAdditive_trivialU_of_admissible

end AdalyFormal.Balaban.SuTwoGeomU1
