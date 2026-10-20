/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.PerturbationRoute
import AdalyFormal.Balaban.BlockedBackground
import AdalyFormal.Balaban.RegularityGap
import AdalyFormal.Balaban.BlockedGaugeGuardAlgebra

set_option autoImplicit false

/-!
# `ClassPropagation` DECIDED FOR THE PINNED BLOCKING `ubarSU2` AT `ell = 2`

Lane record: `compute/class_propagation/PROGRESS.md`.

## §0 — THE QUESTION, AND THE ANSWER

`PerturbationRoute.ClassPropagation L k α₀ blk` takes a blocking family as DATA and asserts that
its tower stays inside the level class `LevelClass L k α₀` — i.e. `frobSupBond (U_j) ≤ α₀` at the
SAME numeric `α₀` at every level `j ≤ k`, each measured on that level's own lattice. That module
brackets the Prop (`classPropagation_holds_for_flattening` / `classPropagation_fails_for_expanding`)
but does not decide it for Bałaban's actual blocking. This module decides it, for the tree's pinned
map `BlockedBackground.ubarSU2` re-indexed onto the coarse lattice (`ubarCoarse 2`), which has
EXACTLY `ClassPropagation`'s `blk` type because `levelExtent L (j+1) = coarseExtent (levelExtent L j) 2`
holds by `rfl`.

**The verdict is REFUTATION, and it is not a large-field artefact.** For every `0 < α₀ ≤ 1` and every
depth `k ≥ 1`, `¬ ClassPropagation L k α₀ (ubarBlk L)` (`classPropagation_fails_for_ubarSU2`). The
witness is inside the perturbation route's own admissible radius — at `α₀ = 10⁻²⁰`,
`PerturbationRoute.gammaZero α₀ > 0` and the refutation still holds
(`classPropagation_fails_inside_admissible_radius`) — and the witness has IDENTICALLY TRIVIAL
plaquette holonomy (`holonomyElem_constU`), so the failure happens on the ZERO-CURVATURE sub-family
and cannot be blamed on curvature.

**And the honest quantitative positive that survives is proved, unconditionally.** For every
configuration whatever,

    frobSupBond (ubarCoarse 2 V)  ≤  (2 + 5π) · frobSupBond V ,   `frobSupBond_ubarCoarse_le_two`

with `2 + 5π = 17.70796…` composed from counted factors (§5), and no `c < 2` works
(`no_contraction_ubarCoarse`). So the two-sided sandwich for this map at `ell = 2` is

    2  ≤  C_blk  ≤  2 + 5π .

**The composed depth-vs-radius corollary** (`tower_coercive_to_depth`) is the exact statement of
what the source's assumed (1.66) would upgrade: our tower is coercive at level `j` with constant
`γ* − 320·C_blk^j·α₀`, which is positive as long as `C_blk^n·α₀ < γ*/320` — a FINITE depth `n`
determined by `α₀`. The source's (1.66) would make that depth-UNIFORM. The gap between the two IS
the hedge, and it is now a number: each blocking step costs a factor of at most `2 + 5π` and at
least `2` in the radius, and the admissible radius `γ*/320 ≈ 1.4·10⁻¹⁹` is fixed.

## §1 — THE SOURCE, VERBATIM

`corpus/pages/CMP99a_p87.md` (`verification_status: dual-read-diffed`, 400 dpi render
`render_sha256: 80632f84c5a0b5e2535e4c5efa5552cb06e3885753fc1262c4e362c5e8a564df`) prints, at
`#eq-1-65` and `#eq-1-66`:

```latex
|(\overline{U'U_0})^j - \bar{U}_0^j| = |\tilde{U}'^{j}-1| < 11d^2\alpha_0+\alpha_1
  \quad \text{on} \quad \Omega_j^{(j)}. \tag{1.65}
```

> **We will assume that the above bounds hold instead of (1.35).** For simplicity let us write
> `α₁` instead of the right-hand side above, so we assume that

```latex
|(\overline{U'U_0})^j - \bar{U}_0^j| = |\tilde{U}'^{j}-1| < \alpha_1
  \quad \text{on} \quad \Omega_j^{(j)}, \quad j = 0,1,\ldots,k. \tag{1.66}
```

So the source PROVES growth at this step — a blocked deviation bounded by `11d²α₀ + α₁`, strictly
larger than the input `α₁` — and then RELABELS the right-hand side as `α₁` and ASSUMES the relabelled
bound holds at every index. `RescaledTower.Assumed_1_66` is that hedge as a named `Prop` in this
tree; it is consumed by NOTHING and is cited here for contrast only. This module is the
kernel-checked version of the PROVED half at `ell = 2` in OUR units, plus the refutation of the
un-relabelled statement.

⚠ **UNITS, STATED AS OURS.** (1.65)'s `α₀`, `α₁` and `11d²` live in the source's rescaled
bookkeeping; our `frobSupBond` is the unrescaled dimensionless holonomy radius. `11d² = 99` at
`d = 3` and our `2 + 5π = 17.708` are NOT the same number in the same units and no comparison
between them is asserted anywhere in this file. What IS asserted is that in the units
`PerturbationRoute.LevelClass` is actually stated in — the same numeric `α₀` at every level, on that
level's own lattice, which is that module's own reading of (3.35) — the propagation is FALSE.

## §2 — WHAT IS PROVED, DECLARATION BY DECLARATION

1. **THE `su(2)` EXPONENTIAL BRICK (§3).** `exp_mem_special`: `exp` maps traceless anti-Hermitian
   `2×2` matrices into `SU(2)`, unconditionally; and `frobNorm_su2Exp_sub_one_le_uncond`:
   `‖exp H − 1‖_F ≤ ‖H‖_F` with **no branch hypothesis**. Route: Cayley–Hamilton gives
   `H·H = −(frobSq H / 2)·1` (`alg_sq`), so `H = r·J` with `J² = −1`, and `Complex.liftAux` (the
   technique `RegularityGap.su2_exp_log_of_ne_negOne` already uses, LAW-19) gives the closed form
   `exp H = cos r · 1 + (sin r / r) · H` (`exp_closed`).

   ⚠ **FINDING, OUT OF WRITE SCOPE (LAW-4)** ~~`exp_mem_special` is exactly the statement of
   `BlockedGaugeGuardAlgebraExp.exp_su2Alg_mem_special`, which is an OPEN `sorry` in this tree~~
   (STALE, corrected 2026-08-02 per the second-family gate's F1: the `su2algebra_glue` repair has
   since DISCHARGED that sorry by re-proving this route locally in that file — and additionally
   proved Route B's missing lemma, so the statement now carries TWO independent proofs there;
   the tree-wide sorry count moved 25 → 24). The historical record stands: at this module's build
   time the target was open (`[BLOCKED-SU2-ALGEBRA]`), the recorded routes A/B both stalled, and
   this module's Route C was the first working proof. `exp_su2Alg_mem_special_of_carrier` below
   states it in that module's own `su2Alg` vocabulary.

2. **THE BLOCK IS AT MOST `ell³` SITES (§4), WITH NO FITTING HYPOTHESIS.** `card_stepBlockOf_le`.
   `QjComposite.card_stepBlockOf` gives `= ell³` only under `hfit`; the `≤` direction needs nothing,
   which is what makes §6's bound unconditional even where the block TRUNCATES.

3. **THE STAIRCASE IS SHORT (§4).** `gammaPath_length_le`: `|Γ_{c_-,x}| ≤ 3(ell − 1)` for `x` in
   the block — `3` axes, each advanced at most `ell − 1` strided steps.

4. **THE LOOP VARIABLE, BY TELESCOPING (§5).** `frobNorm_loopVar_sub_one_le`:
   `‖W_x − 1‖_F ≤ (8·ell − 6)·frobSupBond V`. Counted: `2·|Γ| + 2·ell ≤ 6(ell−1) + 2ell = 8ell − 6`,
   from the four factors of `W_x = U(Γ_{c,x})·U(c)⁻¹` (two staircases, one `ell`-fold bond, one
   inverse bond). **This is NOT the source's curvature×area bound** — it does not use a spanning
   surface, and it is therefore weaker in the small-curvature regime; it is, however, unconditional,
   which is what `BlockedBackground` §8(a) could not obtain.

5. **THE QUANTITATIVE POSITIVE (§6).** `frobNorm_ubarSU2_sub_one_le`, then
   `frobSupBond_ubarSU2_le` and `frobSupBond_ubarCoarse_le`. At `ell = 2`:
   `C_blk = 2 + (π/2)·10 = 2 + 5π`, and `blkConst_bounds` asserts `17.7079 < 2 + 5π < 17.708`.

6. **THE REFUTATION (§7)** and **the two-sided lower end (§8)**.

7. **THE DEPTH COROLLARY (§9).** `tower_radius_le` (geometric growth) and
   `tower_coercive_to_depth`.

## §3a — WHAT IS **NOT** CLAIMED

* **`2 + 5π` is NOT claimed sharp.** The true constant lies in `[2, 2+5π]`; §5's telescoping is
  crude precisely because it ignores curvature. No sharpness statement appears anywhere below.
* **Nothing here says Bałaban's scheme fails.** `BlockedBackground`'s header limit 1 stands: the
  factor `ell` per level is dimensionally forced for the UNRESCALED functional, and the named
  missing object is a per-level rescaled regularity functional. This module does not build one.
  What is decided is the Prop `PerturbationRoute.ClassPropagation` AS STATED, in the units
  `LevelClass` is stated in.
* **The blocked object is `ubarCoarse 2`, i.e. `ubarSU2 1 2` read at coarse indices.** The stride is
  `1` because at each level the blocking acts on that level's OWN lattice. No claim is made about
  the composite `UbarTower`'s strided reading, which is a different map.
* **`Δ′_π` is absent, `J = 0`, `ell = 2`, `𝔰𝔲(2)`, periodic torus** — `PerturbationRoute`'s standing
  scope, unchanged.
-/

namespace AdalyFormal.Balaban.ClassPropagationUbar

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Exp_of_mem su2Exp_zero
  su2Log_mem_su2Alg exp_antiHerm_mem_unitary su2Alg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobSq_nonneg frobNorm_zero frobNorm_nonneg)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.BlockingLinkEstimate (blockExponent blockedLink
  frobNorm_su2Log_le_pi_div_two frobNorm_sum_le frobNorm_real_smul)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath coarseStraightSegment
  coarseCoordSteps)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.CovariantFibreTransfer (constU)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.U1AnchorCoarse (coarseExtent toFine)
open AdalyFormal.Balaban.TowerMilestone (levelExtent levelExtent_zero levelExtent_succ gammaStar
  gammaStar_pos gammaStar_eq VLat qLevel levelOK_of_pow)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarCoarse ubarCoarse_constU ubarSU2_constU
  ubarSU2_eq_blockedLink frobNorm_coarsePathHolonomy_sub_one_le frobNorm_coarseBondVar_sub_one_le
  frobSupBond_constU gOf frobSq_gOf frobSq_gOf_sq frobSupBond_constU_gOf_pos)
open AdalyFormal.Balaban.PerturbationRoute (ClassPropagation LevelClass blkTower gammaZero
  pertConst gammaZero_pos_at_1e_neg_20 lattice_uniform_perturbed_coercive)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-! ## §3 — THE `su(2)` EXPONENTIAL BRICK: `‖exp H − 1‖_F ≤ ‖H‖_F`, WITH NO BRANCH HYPOTHESIS

Every statement in this section is about an arbitrary traceless anti-Hermitian `H : M₂(ℂ)`. -/

section SuTwoExp

variable {H : M2}

/-- `Hᴴ = −H` entrywise. -/
theorem entry_star (hah : Hᴴ = -H) (i j : Fin 2) : star (H j i) = - H i j := by
  have := congrFun (congrFun hah i) j
  simpa [Matrix.conjTranspose_apply] using this

/-- The diagonal of an anti-Hermitian matrix is purely imaginary. -/
theorem e00re (hah : Hᴴ = -H) : (H 0 0).re = 0 := by
  have h := entry_star hah 0 0
  have := congrArg Complex.re h
  simp at this
  linarith

theorem e11 (htr : Matrix.trace H = 0) : H 1 1 = - H 0 0 := by
  rw [Matrix.trace_fin_two] at htr
  linear_combination htr

theorem e10 (hah : Hᴴ = -H) : H 1 0 = - (starRingEnd ℂ) (H 0 1) := by
  have h := entry_star hah 0 1
  rw [Complex.star_def] at h
  have h2 := congrArg (starRingEnd ℂ) h
  simpa using h2

/-- `frobSq H = 2(b² + |w|²)` with `b = Im H₀₀`, `w = H₀₁`. -/
theorem frobSq_eq (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    frobSq H = 2 * ((H 0 0).im ^ 2 + Complex.normSq (H 0 1)) := by
  have hre := e00re hah
  have h11 := e11 htr
  have h10 := e10 hah
  unfold frobSq
  rw [h11, h10]
  simp only [Complex.normSq_apply, Complex.neg_re, Complex.neg_im, Complex.conj_re,
    Complex.conj_im]
  rw [hre]
  ring

theorem scalar_val (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    H 0 0 * H 0 0 + H 0 1 * H 1 0 = ((-(frobSq H / 2) : ℝ) : ℂ) := by
  have hre := e00re hah
  have h10 := e10 hah
  rw [frobSq_eq hah htr, h10]
  apply Complex.ext <;>
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, hre, ← Complex.ofReal_pow] <;>
      ring

theorem offdiag01 (htr : Matrix.trace H = 0) : H 0 0 * H 0 1 + H 0 1 * H 1 1 = 0 := by
  rw [e11 htr]; ring

theorem offdiag10 (htr : Matrix.trace H = 0) : H 1 0 * H 0 0 + H 1 1 * H 1 0 = 0 := by
  rw [e11 htr]; ring

theorem diag11 (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    H 1 0 * H 0 1 + H 1 1 * H 1 1 = ((-(frobSq H / 2) : ℝ) : ℂ) := by
  rw [e11 htr, ← scalar_val hah htr]
  ring

/-- **CAYLEY–HAMILTON ON `su(2)`.** `H·H = −(frobSq H / 2)·1`. The scalar is REAL and NONPOSITIVE,
which is what makes `r⁻¹·H` a complex structure. -/
theorem alg_sq (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    H * H = ((-(frobSq H / 2) : ℝ) : ℂ) • (1 : M2) := by
  have k00 := scalar_val hah htr
  have k01 := offdiag01 htr
  have k10 := offdiag10 htr
  have k11 := diag11 hah htr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Fin.isValue] <;>
    simp [k00, k01, k10, k11]

/-- `frobSq` of a real combination `c·1 + d·H`. The cross term vanishes because `H` is traceless
with purely imaginary diagonal. -/
theorem comb_frobSq (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) (c d : ℝ) :
    frobSq (c • (1 : M2) + d • H) = 2 * c ^ 2 + d ^ 2 * frobSq H := by
  have hre := e00re hah
  have h11 := e11 htr
  have h10 := e10 hah
  have hf := frobSq_eq hah htr
  have o01 : ((1 : M2) 0 1) = 0 := Matrix.one_apply_ne (by decide)
  have o10 : ((1 : M2) 1 0) = 0 := Matrix.one_apply_ne (by decide)
  have o00 : ((1 : M2) 0 0) = 1 := Matrix.one_apply_eq _
  have o11 : ((1 : M2) 1 1) = 1 := Matrix.one_apply_eq _
  have hL : frobSq (c • (1 : M2) + d • H)
      = Complex.normSq ((c • (1 : M2) + d • H) 0 0)
        + Complex.normSq ((c • (1 : M2) + d • H) 0 1)
        + Complex.normSq ((c • (1 : M2) + d • H) 1 0)
        + Complex.normSq ((c • (1 : M2) + d • H) 1 1) := rfl
  rw [hL, hf]
  simp only [Matrix.add_apply, Matrix.smul_apply, o00, o01, o10, o11, h11, h10]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
    Complex.zero_re, Complex.zero_im, hre]
  ring

theorem comb_det (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) (c d : ℝ) :
    (c • (1 : M2) + d • H).det = ((c ^ 2 + d ^ 2 * (frobSq H / 2) : ℝ) : ℂ) := by
  have h11 := e11 htr
  have hsc := scalar_val hah htr
  have o01 : ((1 : M2) 0 1) = 0 := Matrix.one_apply_ne (by decide)
  have o10 : ((1 : M2) 1 0) = 0 := Matrix.one_apply_ne (by decide)
  have o00 : ((1 : M2) 0 0) = 1 := Matrix.one_apply_eq _
  have o11 : ((1 : M2) 1 1) = 1 := Matrix.one_apply_eq _
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, o00, o01, o10, o11, Complex.real_smul]
  rw [h11]
  have hexp : ((c ^ 2 + d ^ 2 * (frobSq H / 2) : ℝ) : ℂ)
      = (c : ℂ) ^ 2 - (d : ℂ) ^ 2 * ((-(frobSq H / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, ← hsc]
  push_cast
  ring

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open AdalyFormal.Balaban.RegularityGap (real_smul_eq)

/-- **THE CLOSED FORM.** `exp H = cos r · 1 + (sin r / r) · H` with `r = √(frobSq H / 2)`. -/
theorem exp_closed (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) {r : ℝ} (hr : 0 < r)
    (hr2 : r ^ 2 = frobSq H / 2) :
    NormedSpace.exp H = (Real.cos r) • (1 : M2) + (Real.sin r * r⁻¹) • H := by
  have hrne : r ≠ 0 := ne_of_gt hr
  set J : M2 := (r⁻¹ : ℝ) • H with hJdef
  have hHH : H * H = ((-(r ^ 2) : ℝ)) • (1 : M2) := by
    rw [alg_sq hah htr, hr2, real_smul_eq]
  have hJ : J * J = -1 := by
    rw [hJdef, smul_mul_assoc, mul_smul_comm, hHH, smul_smul, smul_smul]
    have : r⁻¹ * r⁻¹ * -(r ^ 2) = -1 := by field_simp
    rw [this, neg_one_smul]
  set phi : ℂ →ₐ[ℝ] M2 := Complex.liftAux J hJ with hphi
  have hcont : Continuous ((phi : ℂ →ₐ[ℝ] M2) : ℂ → M2) := by
    have hc2 : Continuous ((phi : ℂ →ₐ[ℝ] M2).toLinearMap : ℂ → M2) :=
      LinearMap.continuous_of_finiteDimensional _
    exact hc2
  have hphir : phi ((r : ℂ) * Complex.I) = H := by
    rw [hphi, Complex.liftAux_apply]
    have hre : ((r : ℂ) * Complex.I).re = 0 := by simp
    have him : ((r : ℂ) * Complex.I).im = r := by simp
    rw [hre, him, map_zero, zero_add, hJdef, smul_smul, mul_inv_cancel₀ hrne, one_smul]
  have hexp : NormedSpace.exp H = phi (Complex.exp ((r : ℂ) * Complex.I)) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.map_exp phi hcont, hphir]
    rfl
  rw [hexp, Complex.exp_mul_I, hphi, Complex.liftAux_apply]
  have hre : (Complex.cos (r : ℂ) + Complex.sin (r : ℂ) * Complex.I).re = Real.cos r := by
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  have him : (Complex.cos (r : ℂ) + Complex.sin (r : ℂ) * Complex.I).im = Real.sin r := by
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  rw [hre, him, Algebra.algebraMap_eq_smul_one, hJdef, smul_smul]

/-- **`exp` MAPS `su(2)` INTO `SU(2)` — UNCONDITIONALLY.** Unitarity is
`SuTwoLogExp.exp_antiHerm_mem_unitary` (reused, LAW-19); `det = 1` is `cos²r + sin²r` read off the
closed form. -/
theorem exp_mem_special (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    NormedSpace.exp H ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨exp_antiHerm_mem_unitary hah, ?_⟩
  rcases eq_or_lt_of_le (frobSq_nonneg H) with hz | hpos
  · have hH0 : H = 0 :=
      AdalyFormal.Balaban.AlphaAnalyticity.matrix_eq_zero_of_frobSq_zero hz.symm
    rw [hH0, NormedSpace.exp_zero, Matrix.det_one]
  · set r : ℝ := Real.sqrt (frobSq H / 2) with hrdef
    have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
    have hr2 : r ^ 2 = frobSq H / 2 := Real.sq_sqrt (by linarith)
    rw [exp_closed hah htr hrpos hr2, comb_det hah htr]
    have hone : Real.cos r ^ 2 + (Real.sin r * r⁻¹) ^ 2 * (frobSq H / 2) = 1 := by
      rw [← hr2]
      have hrne : r ≠ 0 := ne_of_gt hrpos
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq r]
    rw [hone]
    norm_num

/-- **THE BRICK.** `‖exp H − 1‖_F ≤ ‖H‖_F` for every traceless anti-Hermitian `H`, with NO branch
hypothesis. Compare `BlockingLinkEstimate.frobNorm_su2Exp_sub_one_le`, which needs
`su2Log (su2Exp H) = H`. -/
theorem frobNorm_su2Exp_sub_one_le_uncond (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    frobNorm (((su2Exp H : SU2) : M2) - 1) ≤ frobNorm H := by
  have hcoe : ((su2Exp H : SU2) : M2) = NormedSpace.exp H :=
    su2Exp_of_mem (exp_mem_special hah htr)
  rcases eq_or_lt_of_le (frobSq_nonneg H) with hz | hpos
  · have hH0 : H = 0 :=
      AdalyFormal.Balaban.AlphaAnalyticity.matrix_eq_zero_of_frobSq_zero hz.symm
    rw [hcoe, hH0, NormedSpace.exp_zero, sub_self]
  · set r : ℝ := Real.sqrt (frobSq H / 2) with hrdef
    have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hr2 : r ^ 2 = frobSq H / 2 := Real.sq_sqrt (by linarith)
    have hsub : NormedSpace.exp H - 1
        = (Real.cos r - 1) • (1 : M2) + (Real.sin r * r⁻¹) • H := by
      rw [exp_closed hah htr hrpos hr2, sub_smul, one_smul]
      abel
    have hfs : frobSq (NormedSpace.exp H - 1) = 4 * (1 - Real.cos r) := by
      have hr2' : frobSq H = 2 * r ^ 2 := by linarith
      rw [hsub, comb_frobSq hah htr, hr2']
      have hpy := Real.sin_sq_add_cos_sq r
      field_simp
      nlinarith [hpy]
    unfold frobNorm
    rw [hcoe, hfs]
    refine Real.sqrt_le_sqrt ?_
    have hc := Real.one_sub_sq_div_two_le_cos (x := r)
    nlinarith [hr2, hc]

/-- **THE SAME STATEMENT IN `BlockedGaugeGuardAlgebra`'s OWN VOCABULARY.** This is exactly
`BlockedGaugeGuardAlgebraExp.exp_su2Alg_mem_special` — ~~an open `sorry` there~~ (STALE, corrected
2026-08-02: since discharged in that file by the `su2algebra_glue` repair porting this route). -/
theorem exp_su2Alg_mem_special_of_carrier (A : ↥su2Alg) :
    NormedSpace.exp (A : M2) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  exp_mem_special A.2.2 A.2.1

/-! ### §3a — MUST-FIRE CONTROL: `htr` IS LOAD-BEARING

`exp_mem_special` takes TWO hypotheses. Anti-Hermitian alone is not enough — it gives unitarity but
not `det = 1`. The witness is `H = (π/2)i·1`: anti-Hermitian, trace `= iπ ≠ 0`, and
`exp H = i·1` has determinant `−1`. Kernel-checked, so the tracelessness clause is not decoration.

⚠ Note what this control does and does not say. It refutes `exp_mem_special` WITHOUT `htr`. It does
NOT claim `frobNorm_su2Exp_sub_one_le_uncond`'s conclusion is false without `htr`: `su2Exp`'s
totalising guard returns `1` exactly when the exponential leaves `SU(2)`, so at this witness the
left-hand side collapses to `0` and the inequality survives vacuously. That is disclosed rather than
hidden: the hypotheses of the norm bound are load-bearing for its PROOF and for the membership
statement it routes through, and no claim is made that they are load-bearing for its conclusion. -/

/-- An anti-Hermitian `2×2` matrix that is NOT traceless. -/
noncomputable def Hbad : M2 :=
  Matrix.diagonal ![(Real.pi / 2 : ℝ) * Complex.I, (Real.pi / 2 : ℝ) * Complex.I]

theorem Hbad_antiHerm : Hbadᴴ = -Hbad := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hbad, Matrix.conjTranspose_apply, Matrix.diagonal]

theorem Hbad_trace_ne : Matrix.trace Hbad ≠ 0 := by
  unfold Hbad
  rw [Matrix.trace_diagonal]
  simp [Fin.sum_univ_two, Complex.ext_iff]

theorem exp_Hbad : NormedSpace.exp Hbad = Matrix.diagonal ![Complex.I, Complex.I] := by
  unfold Hbad
  rw [Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.exp_def]
  fin_cases i <;> simp [← Complex.exp_eq_exp_ℂ]

/-- A traceless matrix that is NOT anti-Hermitian. -/
noncomputable def Hherm : M2 := Matrix.diagonal ![(1 : ℂ), (-1 : ℂ)]

theorem Hherm_trace : Matrix.trace Hherm = 0 := by
  unfold Hherm; rw [Matrix.trace_diagonal]; simp [Fin.sum_univ_two]

theorem Hherm_not_antiHerm : Hhermᴴ ≠ -Hherm := by
  intro hc
  have h := congrFun (congrFun hc 0) 0
  simp [Hherm, Matrix.conjTranspose_apply, Matrix.diagonal] at h
  norm_num at h

theorem exp_Hherm : NormedSpace.exp Hherm
    = Matrix.diagonal ![(Real.exp 1 : ℂ), ((Real.exp 1)⁻¹ : ℂ)] := by
  unfold Hherm
  rw [Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.exp_def]
  fin_cases i <;> simp [← Complex.exp_eq_exp_ℂ] <;>
    rw [show ((-1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_exp] <;>
    push_cast [Real.exp_neg] <;> ring

/-- **`hah` IS LOAD-BEARING TOO.** Traceless alone does not put `exp` in `SU(2)`: here `det = 1`
holds and it is UNITARITY that fails, which is the complementary half to `exp_Hbad_not_special`.
So both hypotheses of `exp_mem_special` are refuted-if-dropped, neither is decoration. -/
theorem exp_Hherm_not_special :
    NormedSpace.exp Hherm ∉ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  intro hmem
  have hu : NormedSpace.exp Hherm ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp hmem).1
  rw [Matrix.mem_unitaryGroup_iff] at hu
  have h := congrFun (congrFun hu 0) 0
  rw [exp_Hherm] at h
  simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.diagonal] at h
  have hone : Complex.exp 1 = ((Real.exp 1 : ℝ) : ℂ) := by
    rw [show ((1:ℂ)) = ((1:ℝ):ℂ) by norm_num, ← Complex.ofReal_exp]
  rw [hone, Complex.conj_ofReal, ← Complex.ofReal_mul] at h
  have h' : Real.exp 1 * Real.exp 1 = 1 := by exact_mod_cast h
  have he : (1:ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ); linarith
  nlinarith [h', he]

/-- **THE CONTROL.** Drop `htr` and `exp_mem_special` is FALSE. -/
theorem exp_Hbad_not_special :
    NormedSpace.exp Hbad ∉ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  intro hmem
  have hdet : (NormedSpace.exp Hbad).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hmem).2
  rw [exp_Hbad, Matrix.det_diagonal] at hdet
  simp [Fin.prod_univ_two, Complex.ext_iff] at hdet
  norm_num at hdet

end SuTwoExp

/-! ## §4 — THE BLOCK IS AT MOST `ell³` SITES, AND THE STAIRCASE IS SHORT

Both statements are needed WITHOUT the fitting hypothesis `hfit`, because §6's bound must hold at
every bond of every extent — including the bonds where `stepBlockOf` truncates
(`QjComposite.card_stepBlockOf_truncates`). Truncation can only REMOVE sites, so `≤ ell³` survives
it; the `= ell³` of `QjComposite.card_stepBlockOf` does not. -/

/-- **`|B_s(y)| ≤ ell³`, unconditionally.** Coordinates of a block site are `y_μ + s·q_μ` with
`q_μ < ell`, and the site is determined by `q`. -/
theorem card_stepBlockOf_le (y : PeriodicLatticeSite L) {s ell : ℕ} (hs : 0 < s) :
    (stepBlockOf y s ell).card ≤ ell ^ 3 := by
  classical
  set f : PeriodicLatticeSite L → (Fin 3 → ℕ) :=
    fun x μ => ((x μ).val - (y μ).val) / s with hf
  have hstep : ∀ x ∈ stepBlockOf y s ell, ∀ μ : Fin 3,
      (x μ).val - (y μ).val = s * (f x μ) := by
    intro x hx μ
    exact (Nat.mul_div_cancel' ((mem_stepBlockOf.mp hx) μ).2.2).symm
  have hlt : ∀ x ∈ stepBlockOf y s ell, ∀ μ : Fin 3, f x μ < ell := by
    intro x hx μ
    have h := (mem_stepBlockOf.mp hx) μ
    have hb : (x μ).val - (y μ).val < ell * s := by
      have := h.2.1; rw [Nat.mul_comm] at this ⊢; omega
    exact (Nat.div_lt_iff_lt_mul hs).mpr hb
  have hmem : ∀ x ∈ stepBlockOf y s ell,
      f x ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range ell) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro μ
    exact Finset.mem_range.mpr (hlt x hx μ)
  have hinj : Set.InjOn f (stepBlockOf y s ell : Set (PeriodicLatticeSite L)) := by
    intro a ha b hb hab
    funext μ
    have h1 := (mem_stepBlockOf.mp ha) μ
    have h2 := (mem_stepBlockOf.mp hb) μ
    have e1 := hstep a ha μ
    have e2 := hstep b hb μ
    have hq : f a μ = f b μ := congrFun hab μ
    rw [hq] at e1
    apply Fin.ext
    omega
  have hcard := Finset.card_le_card_of_injOn f hmem hinj
  refine le_trans hcard (le_of_eq ?_)
  rw [Fintype.card_piFinset]
  simp [pow_succ]

/-- **THE WEIGHTS SUM TO AT MOST `1`, unconditionally.** `BlockedBackground.weight_sum_eq_one` gives
equality only under `hfit`; §6 needs only this side. -/
theorem weight_sum_le_one (y : PeriodicLatticeSite L) {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell) :
    ∑ _x ∈ stepBlockOf y s ell, ((ell : ℝ) ^ 3)⁻¹ ≤ 1 := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((stepBlockOf y s ell).card : ℝ) ≤ (ell : ℝ) ^ 3 := by
    have := card_stepBlockOf_le y (ell := ell) hs
    exact_mod_cast this
  have hpos : (0 : ℝ) < (ell : ℝ) ^ 3 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  rw [inv_eq_one_div, mul_one_div, div_le_one hpos]
  exact hc

theorem coordSteps_lt (y x : PeriodicLatticeSite L) {s ell : ℕ} (hs : 0 < s)
    (hx : x ∈ stepBlockOf y s ell) (μ : Fin 3) : coarseCoordSteps s y x μ < ell := by
  have h := (mem_stepBlockOf.mp hx) μ
  have hle : y μ ≤ x μ := by rw [Fin.le_def]; exact h.1
  have hval : (x μ - y μ).val = (x μ).val - (y μ).val := Fin.sub_val_of_le hle
  have hb : (x μ).val - (y μ).val < ell * s := by
    have := h.2.1; rw [Nat.mul_comm] at this ⊢; omega
  show (x μ - y μ).val / s < ell
  rw [hval]
  exact (Nat.div_lt_iff_lt_mul hs).mpr hb

/-- **`|Γ̄_{y,x}| ≤ 3(ell − 1)`** for `x` in the block: three axes, each advanced at most `ell − 1`
strided steps. The two intermediate base points of the `2,1,0` staircase agree with `y` in the
direction being advanced, which is why one bound per axis suffices. -/
theorem gammaPath_length_le (y x : PeriodicLatticeSite L) {s ell : ℕ} (hs : 0 < s)
    (hx : x ∈ stepBlockOf y s ell) :
    (coarseGammaPath s y x).length ≤ 3 * (ell - 1) := by
  have h21 : ((2 : Fin 3)) ≠ ((1 : Fin 3)) := by decide
  have h20 : ((2 : Fin 3)) ≠ ((0 : Fin 3)) := by decide
  have h10 : ((1 : Fin 3)) ≠ ((0 : Fin 3)) := by decide
  have hu1 : (Function.update y 2 (x 2)) 1 = y 1 := Function.update_of_ne h21.symm _ _
  have hv0 : (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0 = y 0 := by
    rw [Function.update_of_ne h10.symm, Function.update_of_ne h20.symm]
  have hlen : (coarseGammaPath s y x).length
      = coarseCoordSteps s y x 2 + (coarseCoordSteps s (Function.update y 2 (x 2)) x 1
        + coarseCoordSteps s (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0) := by
    simp [coarseGammaPath, coarseStraightSegment]
  have e1 : coarseCoordSteps s (Function.update y 2 (x 2)) x 1 = coarseCoordSteps s y x 1 := by
    show (x 1 - (Function.update y 2 (x 2)) 1).val / s = _
    rw [hu1]; rfl
  have e0 : coarseCoordSteps s (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0
      = coarseCoordSteps s y x 0 := by
    show (x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val / s = _
    rw [hv0]; rfl
  rw [hlen, e1, e0]
  have b2 := coordSteps_lt y x hs hx 2
  have b1 := coordSteps_lt y x hs hx 1
  have b0 := coordSteps_lt y x hs hx 0
  omega

/-! ## §5 — THE LOOP VARIABLE, BY TELESCOPING

`W_x = U(Γ_{c,x})·U(c)⁻¹` has four factors: the staircase `Γ̄_{c_-,x}`, the `ell`-fold bond, the
inverse staircase based at `c_+`, and the inverse coarse bond. Telescoping each
(`BlockedBackground.frobNorm_coarsePathHolonomy_sub_one_le`) and adding
(`RegularUQChain.frobNorm_su_mul_sub_one_le`, `frobNorm_su_inv_sub_one`) gives

    2·|Γ̄| + 2·ell  ≤  6(ell − 1) + 2·ell  =  8·ell − 6 .

⚠ This is a PATH-LENGTH bound, not the source's curvature×area bound. It is strictly weaker in the
small-curvature regime and strictly unconditional, which is the trade `BlockedBackground` §8(a) could
not make: that section needed the spanning surface as an ORDERED WORD and could not build it. -/

theorem ell_pos_of_mem {y x : PeriodicLatticeSite L} {s ell : ℕ} (hs : 0 < s)
    (hx : x ∈ stepBlockOf y s ell) : 0 < ell := by
  have h := (mem_stepBlockOf.mp hx) 0
  rcases Nat.eq_zero_or_pos ell with h0 | h1
  · exfalso; rw [h0] at h; omega
  · exact h1

theorem frobNorm_loopVar_sub_one_le (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) {s ell : ℕ} (hs : 0 < s) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 s ell) :
    frobNorm (((loopVar s ell V c x : SU2) : M2) - 1) ≤ (8 * (ell : ℝ) - 6) * frobSupBond V := by
  have hell := ell_pos_of_mem hs hx
  have hglen := gammaPath_length_le c.1 x hs hx
  have hglenR : ((coarseGammaPath s c.1 x).length : ℝ) ≤ 3 * (ell : ℝ) - 3 := by
    have h1 : ((coarseGammaPath s c.1 x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by
      exact_mod_cast hglen
    have h3 : 3 * (ell - 1) + 3 = 3 * ell := by omega
    have h4 : ((3 * (ell - 1) + 3 : ℕ) : ℝ) = ((3 * ell : ℕ) : ℝ) := by rw [h3]
    push_cast at h4 h1
    linarith
  have hsup0 : 0 ≤ frobSupBond V := frobSupBond_nonneg V
  set P1 := coarsePathHolonomy s V c.1 (coarseGammaPath s c.1 x) with hP1
  set P2 := coarsePathHolonomy s V x (List.replicate ell c.2) with hP2
  set P3 := coarsePathHolonomy s V (cPlusS s ell c) (coarseGammaPath s c.1 x) with hP3
  set Uc := coarseBondVar s ell V c with hUc
  have b1 : frobNorm ((P1 : M2) - 1)
      ≤ ((coarseGammaPath s c.1 x).length : ℝ) * frobSupBond V :=
    frobNorm_coarsePathHolonomy_sub_one_le s V c.1 _
  have b3 : frobNorm ((P3 : M2) - 1)
      ≤ ((coarseGammaPath s c.1 x).length : ℝ) * frobSupBond V :=
    frobNorm_coarsePathHolonomy_sub_one_le s V _ _
  have b2 : frobNorm ((P2 : M2) - 1) ≤ (ell : ℝ) * frobSupBond V := by
    have h := frobNorm_coarsePathHolonomy_sub_one_le s V x (List.replicate ell c.2)
    rwa [List.length_replicate] at h
  have b4 : frobNorm ((Uc : M2) - 1) ≤ (ell : ℝ) * frobSupBond V :=
    frobNorm_coarseBondVar_sub_one_le s ell V c
  have b3' : frobNorm (((P3⁻¹ : SU2) : M2) - 1)
      ≤ ((coarseGammaPath s c.1 x).length : ℝ) * frobSupBond V := by
    rw [AdalyFormal.Balaban.RegularUQChain.frobNorm_su_inv_sub_one]; exact b3
  have b4' : frobNorm (((Uc⁻¹ : SU2) : M2) - 1) ≤ (ell : ℝ) * frobSupBond V := by
    rw [AdalyFormal.Balaban.RegularUQChain.frobNorm_su_inv_sub_one]; exact b4
  have hshape : loopVar s ell V c x = (P1 * P2 * P3⁻¹) * Uc⁻¹ := rfl
  have t1 := AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le (P1 * P2 * P3⁻¹) Uc⁻¹
  have t2 := AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le (P1 * P2) P3⁻¹
  have t3 := AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le P1 P2
  rw [hshape]
  have hlen0 : (0 : ℝ) ≤ ((coarseGammaPath s c.1 x).length : ℝ) := by positivity
  nlinarith [t1, t2, t3, b1, b2, b3', b4', hglenR, hsup0]

/-! ## §6 — THE QUANTITATIVE POSITIVE -/

theorem blockExponent_trace {i : Type*} (S : Finset i) (w : i → ℝ) (W : i → SU2) :
    Matrix.trace (blockExponent S w W) = 0 := by
  unfold blockExponent
  rw [Matrix.trace_sum]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [Matrix.trace_smul, (su2Log_mem_su2Alg (W x)).1, smul_zero]

theorem blockExponent_antiHerm {i : Type*} (S : Finset i) (w : i → ℝ) (W : i → SU2) :
    (blockExponent S w W)ᴴ = -(blockExponent S w W) := by
  unfold blockExponent
  rw [Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.conjTranspose_smul, (su2Log_mem_su2Alg (W x)).2, smul_neg]
  congr 2
  exact Complex.conj_ofReal (w x)

/-- `BlockingLinkEstimate.frobNorm_blockExponent_le` at `Σ w ≤ 1` rather than `Σ w = 1`: the
truncated block is admissible. -/
theorem frobNorm_blockExponent_le' {i : Type*} (S : Finset i) (w : i → ℝ) (W : i → SU2) (b : ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hsum : ∑ x ∈ S, w x ≤ 1) (hb : 0 ≤ b)
    (hbd : ∀ x ∈ S, frobNorm (su2Log (W x)) ≤ b) :
    frobNorm (blockExponent S w W) ≤ b := by
  have hstep : ∀ x ∈ S, frobNorm (((w x : ℝ) : ℂ) • su2Log (W x)) ≤ w x * b := by
    intro x hx
    rw [frobNorm_real_smul, abs_of_nonneg (hw x hx)]
    exact mul_le_mul_of_nonneg_left (hbd x hx) (hw x hx)
  calc frobNorm (blockExponent S w W)
      ≤ ∑ x ∈ S, frobNorm (((w x : ℝ) : ℂ) • su2Log (W x)) := frobNorm_sum_le S _
    _ ≤ ∑ x ∈ S, w x * b := Finset.sum_le_sum hstep
    _ = (∑ x ∈ S, w x) * b := by rw [Finset.sum_mul]
    _ ≤ 1 * b := mul_le_mul_of_nonneg_right hsum hb
    _ = b := one_mul b

/-- **THE BLOCKING CONSTANT AT STRIDE `ell`.** `C(ell) = ell + (π/2)·(8·ell − 6)`: the `ell` is the
coarse bond's own telescoping, the `(π/2)` is CMP98 (25)
(`BlockingLinkEstimate.frobNorm_su2Log_le_pi_div_two`), and `8·ell − 6` is §5's loop bound. Every
factor is counted, none fitted. -/
noncomputable def blkConstOf (ell : ℕ) : ℝ := (ell : ℝ) + Real.pi / 2 * (8 * (ell : ℝ) - 6)

/-- **THE CONSTANT AT THE CAMPAIGN'S STRIDE.** `C(2) = 2 + 5π`. -/
noncomputable def blkConst : ℝ := blkConstOf 2

theorem blkConst_eq : blkConst = 2 + 5 * Real.pi := by
  unfold blkConst blkConstOf; push_cast; ring

/-- The decimal the header quotes, ASSERTED: `17.7079 < 2 + 5π < 17.708`. -/
theorem blkConst_bounds : (17.7079 : ℝ) < blkConst ∧ blkConst < 17.708 := by
  rw [blkConst_eq]
  constructor
  · nlinarith [Real.pi_gt_d6]
  · nlinarith [Real.pi_lt_d6]

theorem blkConst_ge_one : (1 : ℝ) ≤ blkConst := by
  have := blkConst_bounds.1; linarith

theorem blkConst_pos : (0 : ℝ) < blkConst := lt_of_lt_of_le one_pos blkConst_ge_one

/-- **THE PER-BOND BOUND.** `‖Ū_c − 1‖_F ≤ C(ell)·frobSupBond V`, for EVERY bond of EVERY periodic
extent, with NO branch hypothesis, NO loop hypothesis and NO fitting hypothesis. -/
theorem frobNorm_ubarSU2_sub_one_le (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell) :
    frobNorm (((ubarSU2 s ell V c : SU2) : M2) - 1) ≤ blkConstOf ell * frobSupBond V := by
  have hsup0 : 0 ≤ frobSupBond V := frobSupBond_nonneg V
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  set S := stepBlockOf c.1 s ell with hS
  set w : PeriodicLatticeSite L → ℝ := fun _ => ((ell : ℝ) ^ 3)⁻¹ with hw
  set W : PeriodicLatticeSite L → SU2 := fun x => loopVar s ell V c x with hW
  set b : ℝ := Real.pi / 2 * ((8 * (ell : ℝ) - 6) * frobSupBond V) with hb
  have hbnn : 0 ≤ b := by
    have : (0 : ℝ) ≤ (8 * (ell : ℝ) - 6) := by linarith
    have hpi := Real.pi_pos
    rw [hb]; positivity
  have hlog : ∀ x ∈ S, frobNorm (su2Log (W x)) ≤ b := by
    intro x hx
    refine le_trans (frobNorm_su2Log_le_pi_div_two (W x)) ?_
    have hpi := Real.pi_pos
    exact mul_le_mul_of_nonneg_left (frobNorm_loopVar_sub_one_le V c hs x hx) (by positivity)
  have hE : frobNorm (blockExponent S w W) ≤ b :=
    frobNorm_blockExponent_le' S w W b (fun _ _ => by rw [hw]; positivity)
      (weight_sum_le_one c.1 hs hell) hbnn hlog
  have hexpb : frobNorm (((su2Exp (blockExponent S w W) : SU2) : M2) - 1) ≤ b :=
    le_trans (frobNorm_su2Exp_sub_one_le_uncond (blockExponent_antiHerm S w W)
      (blockExponent_trace S w W)) hE
  have hUcb : frobNorm (((coarseBondVar s ell V c : SU2) : M2) - 1) ≤ (ell : ℝ) * frobSupBond V :=
    frobNorm_coarseBondVar_sub_one_le s ell V c
  have hshape : ubarSU2 s ell V c
      = su2Exp (blockExponent S w W) * coarseBondVar s ell V c := by
    rw [ubarSU2_eq_blockedLink]; rfl
  rw [hshape]
  have ht := AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le
    (su2Exp (blockExponent S w W)) (coarseBondVar s ell V c)
  have hsum : blkConstOf ell * frobSupBond V
      = (ell : ℝ) * frobSupBond V + b := by
    rw [hb]; unfold blkConstOf; ring
  rw [hsum]
  linarith [ht, hexpb, hUcb]

/-- **THE `frobSupBond` FORM.** -/
theorem frobSupBond_ubarSU2_le (V : PeriodicLinkConfiguration SU2 L) {s ell : ℕ} (hs : 0 < s)
    (hell : 0 < ell) :
    frobSupBond (ubarSU2 s ell V) ≤ blkConstOf ell * frobSupBond V := by
  unfold frobSupBond
  refine Finset.sup'_le _ _ (fun c _ => ?_)
  exact frobNorm_ubarSU2_sub_one_le V c hs hell

/-- **THE COARSE-INDEXED FORM — the map `ClassPropagation` actually consumes.** -/
theorem frobSupBond_ubarCoarse_le (V : PeriodicLinkConfiguration SU2 L) {ell : ℕ} (hell : 0 < ell) :
    frobSupBond (ubarCoarse ell V) ≤ blkConstOf ell * frobSupBond V := by
  unfold frobSupBond
  refine Finset.sup'_le _ _ (fun c _ => ?_)
  exact frobNorm_ubarSU2_sub_one_le V (toFine L ell c.1, c.2) one_pos hell

/-- **THE HEADLINE POSITIVE, AT `ell = 2`.** `frobSupBond (Ū V) ≤ (2 + 5π)·frobSupBond V`, for
every `V`, unconditionally. -/
theorem frobSupBond_ubarCoarse_le_two (V : PeriodicLinkConfiguration SU2 L) :
    frobSupBond (ubarCoarse 2 V) ≤ blkConst * frobSupBond V :=
  frobSupBond_ubarCoarse_le V (by norm_num)

/-! ## §7 — THE REFUTATION -/

/-- **THE PINNED BLOCKING FAMILY.** `ubarCoarse 2` at every level. Its type IS
`ClassPropagation`'s `blk`, because `levelExtent L (j+1) = coarseExtent (levelExtent L j) 2` by
`rfl`. Nothing existential, nothing free: the map is the tree's `BlockedBackground.ubarSU2` at the
concrete `su2LogExp`. -/
noncomputable def ubarBlk (L : PeriodicLatticeExtent) :
    ∀ j : ℕ, PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L j) →
      PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L (j + 1)) :=
  fun _ V => ubarCoarse 2 V

@[simp] theorem blkTower_ubar_zero (L : PeriodicLatticeExtent)
    (U0 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L 0)) :
    blkTower (ubarBlk L) U0 0 = U0 := rfl

theorem blkTower_ubar_succ (L : PeriodicLatticeExtent)
    (U0 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L 0))
    (j : ℕ) :
    blkTower (ubarBlk L) U0 (j + 1) = ubarCoarse 2 (blkTower (ubarBlk L) U0 j) := rfl

/-- The boundary witness has `frobSupBond` EXACTLY `a`. -/
theorem frobSupBond_wit (Lam : PeriodicLatticeExtent) {a : ℝ} (ha : 0 ≤ a) (ha8 : a ^ 2 ≤ 8) :
    frobSupBond (constU (gOf (1 - a ^ 2 / 4)) Lam) = a := by
  rw [frobSupBond_constU]
  unfold frobNorm
  rw [frobSq_gOf _ (by nlinarith) (by nlinarith)]
  rw [show (4 : ℝ) * (1 - (1 - a ^ 2 / 4)) = a ^ 2 by ring]
  exact Real.sqrt_sq ha

/-- Its blocking has `frobSupBond` exactly `√(4a² − a⁴/2)`. -/
theorem frobSupBond_blocked_wit (Lam : PeriodicLatticeExtent) {a : ℝ} (ha8 : a ^ 2 ≤ 8) :
    frobSupBond (ubarCoarse 2 (constU (gOf (1 - a ^ 2 / 4)) Lam))
      = Real.sqrt (4 * a ^ 2 - a ^ 4 / 2) := by
  rw [ubarCoarse_constU, frobSupBond_constU]
  unfold frobNorm
  congr 1
  rw [frobSq_gOf_sq _ (by nlinarith) (by nlinarith)]
  ring

/-- **THE ARITHMETIC CORE OF BOTH REFUTATIONS.** The boundary witness at radius `a` blocks to a
STRICTLY larger radius, for every `0 < a ≤ 1`. Everything about `ClassPropagation` below is this
one inequality plus the choice of class convention. -/
theorem blocked_wit_gt (Lam : PeriodicLatticeExtent) {a : ℝ} (hpos : 0 < a) (hle : a ≤ 1) :
    a < frobSupBond (ubarCoarse 2 (constU (gOf (1 - a ^ 2 / 4)) Lam)) := by
  have ha : (0 : ℝ) ≤ a := le_of_lt hpos
  have ha8 : a ^ 2 ≤ 8 := by nlinarith
  rw [frobSupBond_blocked_wit Lam ha8]
  have hsq : (0 : ℝ) < a ^ 2 := by positivity
  have hs1 : a ^ 2 ≤ 1 := by nlinarith
  have h4 : a ^ 4 ≤ a ^ 2 := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a ^ 2) (le_of_lt hsq)
    nlinarith [this]
  have hkey : a ^ 2 < 4 * a ^ 2 - a ^ 4 / 2 := by linarith
  have := Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 * a ^ 2 - a ^ 4 / 2)
  nlinarith [Real.sqrt_nonneg (4 * a ^ 2 - a ^ 4 / 2)]

/-- **THE VERDICT: `ClassPropagation` IS FALSE FOR THE PINNED BLOCKING.** For every depth `k ≥ 1`
and every radius `0 < α₀ ≤ 1`, the level-`1` member of the tower generated by `ubarCoarse 2` from
a configuration ON the class boundary leaves the class.

Who chooses what: `α₀` and `k` are universally quantified (subject to the two stated inequalities);
the blocking family is FIXED DATA, not an existential; the witness `constU (gOf (1 − α₀²/4))` is
CONSTRUCTED FROM `α₀` inside the proof (S91: nothing is handed to the prover). -/
theorem classPropagation_fails_for_ubarSU2 (L : PeriodicLatticeExtent) (k : ℕ) (hk : 1 ≤ k)
    {alpha0 : ℝ} (hpos : 0 < alpha0) (hle : alpha0 ≤ 1) :
    ¬ ClassPropagation L k alpha0 (ubarBlk L) := by
  intro h
  have ha : (0 : ℝ) ≤ alpha0 := le_of_lt hpos
  have ha8 : alpha0 ^ 2 ≤ 8 := by nlinarith
  have h0 : frobSupBond (constU (gOf (1 - alpha0 ^ 2 / 4)) (levelExtent L 0)) ≤ alpha0 :=
    le_of_eq (frobSupBond_wit _ ha ha8)
  have h1 := h _ h0 1 hk
  rw [blkTower_ubar_succ] at h1
  exact absurd h1 (not_le.mpr (blocked_wit_gt (levelExtent L 0) hpos hle))

/-- **THE REFUTATION IS INSIDE THE ADMISSIBLE RADIUS.** At `α₀ = 10⁻²⁰` the perturbation route's own
constant `γ₀(α₀) = γ* − 320α₀` is STRICTLY POSITIVE — so the class at which propagation fails is a
class the coercivity theorems actually use, not a large-field artefact. -/
theorem classPropagation_fails_inside_admissible_radius (L : PeriodicLatticeExtent) (k : ℕ)
    (hk : 1 ≤ k) :
    0 < gammaZero (1 / 10 ^ 20) ∧ ¬ ClassPropagation L k (1 / 10 ^ 20) (ubarBlk L) :=
  ⟨gammaZero_pos_at_1e_neg_20,
    classPropagation_fails_for_ubarSU2 L k hk (by norm_num) (by norm_num)⟩

/-- **AND THE WITNESS HAS IDENTICALLY TRIVIAL CURVATURE.** Every plaquette holonomy of a CONSTANT
configuration is `1` on the nose, so the refutation lives entirely on the ZERO-CURVATURE sub-family:
it cannot be blamed on the background being rough. (A constant configuration is not the flat one —
`frobSupBond (constU g) = ‖g − 1‖_F` is positive for `g ≠ 1` — it is flat-but-nontrivial.) -/
theorem holonomyElem_constU (g : SU2) (p : PeriodicLatticePlaquette L) :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (constU g L) p = 1 := by
  show g * g * g⁻¹ * g⁻¹ = 1
  group

/-- The refutation witness is genuinely inside the class and genuinely non-flat, both asserted. -/
theorem refutation_witness_facts {alpha0 : ℝ} (hpos : 0 < alpha0) (hle : alpha0 ≤ 1)
    (Lam : PeriodicLatticeExtent) :
    frobSupBond (constU (gOf (1 - alpha0 ^ 2 / 4)) Lam) = alpha0
      ∧ 0 < frobSupBond (constU (gOf (1 - alpha0 ^ 2 / 4)) Lam)
      ∧ ∀ p : PeriodicLatticePlaquette Lam,
          AdalyFormal.Balaban.DeltaPrime.holonomyElem
            (constU (gOf (1 - alpha0 ^ 2 / 4)) Lam) p = 1 := by
  have ha : (0 : ℝ) ≤ alpha0 := le_of_lt hpos
  have ha8 : alpha0 ^ 2 ≤ 8 := by nlinarith
  refine ⟨frobSupBond_wit Lam ha ha8, ?_, fun p => holonomyElem_constU _ p⟩
  rw [frobSupBond_wit Lam ha ha8]; exact hpos

/-! ## §8 — THE OTHER SIDE: NO CONSTANT BELOW `2` WORKS

`BlockedBackground.no_contraction_constant` proves this for `ubarSU2 s 2`. The map
`ClassPropagation` consumes is `ubarCoarse 2`, whose values are `ubarSU2 1 2`'s at coarse indices, so
the statement has to be re-run at the coarse-indexed map; the ratio identity transports because
`ubarCoarse_constU` is the same exact identity. -/

/-- The exact blocking ratio at `ell = 2`, at the coarse-indexed map. -/
theorem coarse_blocking_ratio_two (t : ℝ) (ht : -1 ≤ t) (ht' : t < 1) :
    frobSupBond (ubarCoarse 2 (constU (gOf t) L))
      = Real.sqrt (2 * (1 + t)) * frobSupBond (constU (gOf t) L) := by
  rw [ubarCoarse_constU, frobSupBond_constU, frobSupBond_constU]
  unfold frobNorm
  rw [frobSq_gOf_sq t ht (le_of_lt ht'), frobSq_gOf t ht (le_of_lt ht')]
  rw [← Real.sqrt_mul (by nlinarith : (0 : ℝ) ≤ 2 * (1 + t))]
  congr 1
  ring

/-- **NO CONTRACTION CONSTANT BELOW `2`.** For every `c < 2` the claim "blocking multiplies
`frobSupBond` by at most `c`" is FALSE. Together with `frobSupBond_ubarCoarse_le_two` this brackets
the true constant: `2 ≤ C_blk ≤ 2 + 5π`. The witness is built from `c` inside the proof. -/
theorem no_contraction_ubarCoarse {c : ℝ} (hc : c < 2) :
    ¬ (∀ V : PeriodicLinkConfiguration SU2 L,
        frobSupBond (ubarCoarse 2 V) ≤ c * frobSupBond V) := by
  intro hall
  rcases le_or_gt c 0 with hneg | hpos
  · have hpos0 : 0 < frobSupBond (constU (gOf 0) L) :=
      frobSupBond_constU_gOf_pos 0 (by norm_num) (by norm_num)
    have h := hall (constU (gOf 0) L)
    rw [coarse_blocking_ratio_two 0 (by norm_num) (by norm_num)] at h
    have h2 : (1 : ℝ) ≤ Real.sqrt (2 * (1 + 0)) := by
      rw [show (2 : ℝ) * (1 + 0) = 2 by ring]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    nlinarith
  · have ht0 : (0 : ℝ) ≤ c ^ 2 / 4 := by positivity
    have ht1 : c ^ 2 / 4 < 1 := by nlinarith
    have hpos0 : 0 < frobSupBond (constU (gOf (c ^ 2 / 4)) L) :=
      frobSupBond_constU_gOf_pos _ (by linarith) ht1
    have h := hall (constU (gOf (c ^ 2 / 4)) L)
    rw [coarse_blocking_ratio_two (c ^ 2 / 4) (by linarith) ht1] at h
    have hsq : Real.sqrt (2 * (1 + c ^ 2 / 4)) ^ 2 = 2 * (1 + c ^ 2 / 4) :=
      Real.sq_sqrt (by nlinarith)
    have hgt : c < Real.sqrt (2 * (1 + c ^ 2 / 4)) := by
      nlinarith [Real.sqrt_nonneg (2 * (1 + c ^ 2 / 4)), hsq]
    nlinarith

/-- **THE SANDWICH, IN ONE STATEMENT.** -/
theorem blkConst_two_sided (V : PeriodicLinkConfiguration SU2 L) :
    frobSupBond (ubarCoarse 2 V) ≤ blkConst * frobSupBond V
      ∧ ∀ c : ℝ, c < 2 → ¬ (∀ W : PeriodicLinkConfiguration SU2 L,
          frobSupBond (ubarCoarse 2 W) ≤ c * frobSupBond W) :=
  ⟨frobSupBond_ubarCoarse_le_two V, fun _ hc => no_contraction_ubarCoarse hc⟩

/-! ## §9 — THE COMPOSED DEPTH-VS-RADIUS COROLLARY

This is the statement the source's assumed (1.66) would UPGRADE. Our tower's radius grows
GEOMETRICALLY with the level, at rate at most `C_blk`; the perturbation route's admissible radius is
`γ*/320`, a FIXED number. So coercivity survives to depth `n` exactly while `C_blk^n·α₀ < γ*/320`,
and no further. (1.66) asserts a `j`-independent bound `α₁`, which would make the depth unbounded.
Nothing here proves or disproves (1.66) in the source's own rescaled units; what is proved is that
this tree's `frobSupBond` bookkeeping does not deliver it. -/

/-- **GEOMETRIC GROWTH OF THE TOWER'S RADIUS.** -/
theorem tower_radius_le (L : PeriodicLatticeExtent)
    (U0 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L 0))
    {alpha0 : ℝ} (h0 : frobSupBond U0 ≤ alpha0) (j : ℕ) :
    frobSupBond (blkTower (ubarBlk L) U0 j) ≤ blkConst ^ j * alpha0 := by
  induction j with
  | zero => simpa using h0
  | succ i ih =>
      rw [blkTower_ubar_succ]
      refine le_trans (frobSupBond_ubarCoarse_le_two _) ?_
      have hc : (0 : ℝ) ≤ blkConst := le_of_lt blkConst_pos
      calc blkConst * frobSupBond (blkTower (ubarBlk L) U0 i)
          ≤ blkConst * (blkConst ^ i * alpha0) := mul_le_mul_of_nonneg_left ih hc
        _ = blkConst ^ (i + 1) * alpha0 := by ring

/-- **COERCIVE TO DEPTH `n`, EXPLICITLY.** At every level `j ≤ min k n`, the level-`j` lattice
operator at the level-`j` blocked background satisfies the perturbation route's inequality with
constant `γ* − 320·C_blk^j·α₀`, and that constant is STRICTLY POSITIVE as soon as
`C_blk^n·α₀ < γ*/320`.

Who chooses what: `α₀` and `n` are the consumer's; `L`, `k`, `j`, `U0` and `u` are universal; the
blocking family is fixed data. -/
theorem tower_coercive_to_depth (L : PeriodicLatticeExtent) {k n : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1))
    (U0 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L 0))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0) (h0 : frobSupBond U0 ≤ alpha0)
    (hdepth : blkConst ^ n * alpha0 < gammaStar / pertConst)
    (j : ℕ) (hj : j ≤ k) (hjn : j ≤ n)
    (u : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (levelExtent L j))
    (hu : VLat (levelExtent L (j + 1))
      (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u))) :
    0 < gammaStar - pertConst * (blkConst ^ j * alpha0)
      ∧ (gammaStar - pertConst * (blkConst ^ j * alpha0)) * ‖u‖ ^ 2
        ≤ (inner ℝ u (AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized
              (blkTower (ubarBlk L) U0 j) u) : ℝ)
          + (inner ℝ u (AdalyFormal.Balaban.AxialCoercivity.pAxCLM
              (AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice (levelExtent L j) 2) 2 u) : ℝ) := by
  have hrad := tower_radius_le L U0 h0 j
  have hnn : 0 ≤ blkConst ^ j * alpha0 := by
    have : (0 : ℝ) ≤ blkConst ^ j := pow_nonneg (le_of_lt blkConst_pos) j
    positivity
  have hmono : blkConst ^ j * alpha0 ≤ blkConst ^ n * alpha0 := by
    have hpow' : blkConst ^ j ≤ blkConst ^ n := pow_le_pow_right₀ blkConst_ge_one hjn
    exact mul_le_mul_of_nonneg_right hpow' halpha
  have hpc : (0 : ℝ) < pertConst := AdalyFormal.Balaban.PerturbationRoute.pertConst_pos
  have hposγ : 0 < gammaStar - pertConst * (blkConst ^ j * alpha0) := by
    have h1 : blkConst ^ j * alpha0 < gammaStar / pertConst := lt_of_le_of_lt hmono hdepth
    have h2 : pertConst * (blkConst ^ j * alpha0) < pertConst * (gammaStar / pertConst) :=
      mul_lt_mul_of_pos_left h1 hpc
    rw [mul_div_cancel₀ _ (ne_of_gt hpc)] at h2
    linarith
  exact ⟨hposγ,
    lattice_uniform_perturbed_coercive L hpow j hj hnn (blkTower (ubarBlk L) U0 j) hrad u hu⟩

/-- **THE DEPTH IS FINITE AND THE ADMISSIBLE RADIUS IS FIXED — the hedge, quantified.** At
`α₀ = 10⁻²⁰`, one blocking step already multiplies the radius by at least `2` and at most `2 + 5π`,
while the route's admissible radius is `γ*/320`. This records both numbers as exact rationals in one
place so that no consumer has to reconstruct them. -/
theorem admissible_radius_exact :
    gammaStar / pertConst = 1 / 7207217841090723840 ∧ (0 : ℝ) < 1 / 7207217841090723840 := by
  constructor
  · rw [gammaStar_eq]; unfold pertConst; norm_num
  · norm_num

/-- **NO CONTRACTION AT ANY STRIDE, coarse-indexed, with a LINEARLY GROWING lower bound.**
`BlockedBackground.no_contraction_at_any_ell` at the map `ClassPropagation` consumes. So the lower
end of the sandwich is not a stride-`2` accident: it grows like `2·ell/π`. -/
theorem no_contraction_ubarCoarse_at_any_ell {ell : ℕ} (hell : 1 ≤ ell) {c : ℝ}
    (hc : c < 2 * (ell : ℝ) / Real.pi) :
    ¬ (∀ V : PeriodicLinkConfiguration SU2 L,
        frobSupBond (ubarCoarse ell V) ≤ c * frobSupBond V) := by
  intro hall
  have hpi := Real.pi_pos
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set phi : ℝ := Real.pi / (ell : ℝ) with hphi
  have hppos : 0 < phi := by positivity
  have hple : phi ≤ Real.pi := by
    rw [hphi]; exact div_le_self (le_of_lt hpi) (by exact_mod_cast hell)
  have hin : frobSupBond (constU (AdalyFormal.Balaban.BlockedBackground.diagSU2 phi) L)
      = Real.sqrt (4 * (1 - Real.cos phi)) := by
    rw [frobSupBond_constU]
    have := AdalyFormal.Balaban.BlockedBackground.frobNorm_diagSU2_pow phi 1
    rw [pow_one, Nat.cast_one, one_mul] at this
    exact this
  have hcos : Real.cos ((ell : ℝ) * phi) = -1 := by
    rw [hphi, mul_div_cancel₀ _ (ne_of_gt hellR), Real.cos_pi]
  have hout : frobSupBond (ubarCoarse ell
      (constU (AdalyFormal.Balaban.BlockedBackground.diagSU2 phi) L)) = Real.sqrt 8 := by
    rw [ubarCoarse_constU, frobSupBond_constU]
    have := AdalyFormal.Balaban.BlockedBackground.frobNorm_diagSU2_pow phi ell
    rw [hcos] at this
    rw [this]
    norm_num
  have h := hall (constU (AdalyFormal.Balaban.BlockedBackground.diagSU2 phi) L)
  rw [hout, hin] at h
  have hhalf : Real.sin (phi / 2) ≤ phi / 2 := Real.sin_le (by positivity)
  have hsinpos : 0 < Real.sin (phi / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hcosp : 1 - Real.cos phi = 2 * Real.sin (phi / 2) ^ 2 := by
    have h2 : Real.cos (2 * (phi / 2)) = 2 * Real.cos (phi / 2) ^ 2 - 1 := Real.cos_two_mul _
    have h3 : (2 : ℝ) * (phi / 2) = phi := by ring
    rw [h3] at h2
    have h4 := Real.sin_sq_add_cos_sq (phi / 2)
    linarith
  have hbound : 4 * (1 - Real.cos phi) ≤ phi ^ 2 * 2 := by rw [hcosp]; nlinarith
  have hin_le : Real.sqrt (4 * (1 - Real.cos phi)) ≤ Real.sqrt (phi ^ 2 * 2) :=
    Real.sqrt_le_sqrt hbound
  have hp2 : Real.sqrt (phi ^ 2 * 2) = phi * Real.sqrt 2 := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hppos)]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hinpos : 0 < Real.sqrt (4 * (1 - Real.cos phi)) := by
    refine Real.sqrt_pos.mpr ?_
    rw [hcosp]; nlinarith
  rw [h8] at h
  have hcpos : 0 < c := by
    rcases le_or_gt c 0 with hc0 | hc0
    · exfalso; nlinarith
    · exact hc0
  have hchain : 2 * Real.sqrt 2 ≤ c * (phi * Real.sqrt 2) := by
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hcpos)
    rw [← hp2]; exact hin_le
  have hcp : 2 ≤ c * phi := by nlinarith
  have hA1 : 2 * (ell : ℝ) ≤ c * Real.pi := by
    rw [hphi] at hcp
    rw [div_eq_mul_inv, ← mul_assoc] at hcp
    have := mul_le_mul_of_nonneg_right hcp (le_of_lt hellR)
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hellR), mul_one] at this
    linarith
  have hA2 : c * Real.pi < 2 * (ell : ℝ) := by
    rw [lt_div_iff₀ hpi] at hc
    linarith
  linarith

/-! ## §8a — THE OTHER TWO UNIT CONVENTIONS, BOTH DECIDED

The brief's question "would a different unit convention change the answer?" is answered here by
deciding all three conventions the tree's own text names. `ClassPropagation`/`LevelClass` uses (a).

* **(a) SAME numeric `α₀` at every level, each on its own lattice.** `PerturbationRoute.LevelClass`,
  and `PerturbationRoute` §3's reading of (3.35). **REFUTED** (§7).
* **(b) GEOMETRIC**, radius `rate^j·α₀`. **HOLDS**, at `rate = C_blk`
  (`geomClassPropagation_holds_for_ubarSU2`), and `levelClassGeom_at_rate_one` shows (b) at
  `rate = 1` IS (a) — so (b) is exactly (a) with the growth put back in, and `blkConst > 1` is what
  separates them.
* **(c) FINE-LATTICE reading**, radius `α₀·2^{-j}` — `PerturbationRoute` §3's parenthesis, "on the
  FINE lattice the same display gives `√2 O(1)M α₀ L^{-j}`, which IMPROVES with `j`".
  **REFUTED a fortiori** (`fineClassPropagation_fails_for_ubarSU2`): it is strictly stronger than
  (a) at every `j ≥ 1`.

So the answer does NOT turn on the convention: of the three, only the one that BUILDS IN geometric
growth survives, and the rate it needs is bounded below by `2` (§8). -/

/-- Convention (b): the class whose radius may grow geometrically in the level. -/
def LevelClassGeom (L : PeriodicLatticeExtent) (k : ℕ) (alpha0 rate : ℝ)
    (U : ∀ j : ℕ, PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (levelExtent L j)) : Prop :=
  ∀ j : ℕ, j ≤ k → frobSupBond (U j) ≤ rate ^ j * alpha0

/-- **CONVENTION (b) HOLDS at rate `C_blk`.** -/
theorem geomClassPropagation_holds_for_ubarSU2 (L : PeriodicLatticeExtent) (k : ℕ) {alpha0 : ℝ}
    (U0 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L 0))
    (h0 : frobSupBond U0 ≤ alpha0) :
    LevelClassGeom L k alpha0 blkConst (blkTower (ubarBlk L) U0) :=
  fun j _ => tower_radius_le L U0 h0 j

/-- **CONVENTION (b) AT RATE `1` IS CONVENTION (a).** So (b) is not a different question; it is the
same question with the growth admitted, and `blkConst > 1` is the entire difference. -/
theorem levelClassGeom_at_rate_one (L : PeriodicLatticeExtent) (k : ℕ) (alpha0 : ℝ)
    (U : ∀ j : ℕ, PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (levelExtent L j)) :
    LevelClassGeom L k alpha0 1 U ↔ LevelClass L k alpha0 U := by
  constructor <;> intro h j hj <;> simpa using h j hj

/-- Convention (c): the FINE-lattice reading, radius IMPROVING as `2^{-j}`. -/
def LevelClassFine (L : PeriodicLatticeExtent) (k : ℕ) (alpha0 : ℝ)
    (U : ∀ j : ℕ, PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (levelExtent L j)) : Prop :=
  ∀ j : ℕ, j ≤ k → frobSupBond (U j) ≤ alpha0 / 2 ^ j

/-- **CONVENTION (c) IS REFUTED TOO**, by the SAME witness — a fortiori, since it demands a strictly
smaller radius than (a) at every `j ≥ 1`. -/
theorem fineClassPropagation_fails_for_ubarSU2 (L : PeriodicLatticeExtent) (k : ℕ) (hk : 1 ≤ k)
    {alpha0 : ℝ} (hpos : 0 < alpha0) (hle : alpha0 ≤ 1) :
    ¬ (∀ U0 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L 0),
        frobSupBond U0 ≤ alpha0 → LevelClassFine L k alpha0 (blkTower (ubarBlk L) U0)) := by
  intro h
  have ha : (0 : ℝ) ≤ alpha0 := le_of_lt hpos
  have ha8 : alpha0 ^ 2 ≤ 8 := by nlinarith
  have h0 : frobSupBond (constU (gOf (1 - alpha0 ^ 2 / 4)) (levelExtent L 0)) ≤ alpha0 :=
    le_of_eq (frobSupBond_wit _ ha ha8)
  have h1 := h _ h0 1 hk
  have hgt : alpha0 < frobSupBond (blkTower (ubarBlk L)
      (constU (gOf (1 - alpha0 ^ 2 / 4)) (levelExtent L 0)) 1) :=
    blocked_wit_gt (levelExtent L 0) hpos hle
  norm_num at h1
  linarith [h1, hgt, ha]

/-- **THE MUST-NOT-FIRE BOUNDARY OF THE REFUTATION.** At depth `k = 0` the class constrains only
level `0`, so propagation HOLDS — for the same map, at the same `α₀`. The refutation therefore
genuinely detects the BLOCKING STEP and is not a statement that fails for every `k`. -/
theorem classPropagation_holds_at_depth_zero (L : PeriodicLatticeExtent) (alpha0 : ℝ) :
    ClassPropagation L 0 alpha0 (ubarBlk L) := by
  intro U0 h0 j hj
  have : j = 0 := Nat.le_zero.mp hj
  subst this
  exact h0

/-- **THE DEPTH, AT TWO EXACT RADII, TWO-SIDED.** The tradeoff is not abstract. With
`C_blk = 2 + 5π` and the admissible radius `γ*/320 = 1/7207217841090723840`:

* at `α₀ = 10⁻²⁰` — the radius `PerturbationRoute`'s own witnesses use — the depth is **0**:
  level `0` is inside the radius and level `1` is already outside;
* at `α₀ = 10⁻²⁵` the depth is **4**: levels `0–4` are inside and level `5` is outside.

Both are stated with BOTH sides, so neither is a one-sided bound that could be satisfied vacuously.
This is exactly the quantity CMP99a (1.66) would make infinite by fiat. -/
theorem depth_exact_at_1e_neg_20 :
    blkConst ^ 0 * (1 / 10 ^ 20 : ℝ) < gammaStar / pertConst
      ∧ ¬ (blkConst ^ 1 * (1 / 10 ^ 20 : ℝ) < gammaStar / pertConst) := by
  rw [admissible_radius_exact.1]
  refine ⟨by rw [pow_zero, one_mul]; norm_num, ?_⟩
  have hb1 := blkConst_bounds.1
  intro hcon
  rw [pow_one] at hcon
  norm_num at hcon
  linarith

theorem depth_exact_at_1e_neg_25 :
    blkConst ^ 4 * (1 / 10 ^ 25 : ℝ) < gammaStar / pertConst
      ∧ ¬ (blkConst ^ 5 * (1 / 10 ^ 25 : ℝ) < gammaStar / pertConst) := by
  rw [admissible_radius_exact.1]
  have hb1 := blkConst_bounds.1
  have hb2 := blkConst_bounds.2
  have hpos := blkConst_pos
  have h4 : blkConst ^ 4 ≤ (17.708 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (le_of_lt hpos) (le_of_lt hb2) 4
  have h5 : ((17.7079 : ℝ)) ^ 5 ≤ blkConst ^ 5 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt hb1) 5
  constructor
  · nlinarith [h4]
  · intro hcon
    nlinarith [h5]

/-! ## §10 — CONTROLS

Every control is a statement that FAILS if the corresponding ingredient is removed. -/

/-- **MUST-NOT-FIRE.** At the flat background the blocking is the identity and the bound is tight at
`0 ≤ 0`, so §6 is not measuring an encoding artefact. -/
theorem ubarCoarse_trivialU (ell : ℕ) :
    ubarCoarse ell (trivialU L) = trivialU (coarseExtent L ell) := by
  have h : (trivialU L) = constU (1 : SU2) L := rfl
  rw [h, ubarCoarse_constU, one_pow]
  rfl

/-- **MUST-FIRE on `hs : 0 < s`.** `card_stepBlockOf_le` is false at `s = 0`: `inStepBlock y 0 ell`
demands `y_μ ≤ x_μ < y_μ` for `ell = 0`, but at `ell ≥ 1` and `s = 0` the condition
`0 ∣ (x_μ − y_μ)` forces `x_μ = y_μ`, so the block is a singleton — while the bound `≤ ell³` still
holds. The genuinely load-bearing use of `hs` is in `coordSteps_lt`, where the division `/ s`
returns `0` at `s = 0` and the DIVISIBILITY witness disappears; the statement recorded here is the
one that would silently change: at `s = 0` the map `f` of `card_stepBlockOf_le` is constantly `0`
and its injectivity argument collapses. This control asserts the concrete fact that makes the
`s = 0` block degenerate. -/
theorem stepBlockOf_zero_stride_singleton (y x : PeriodicLatticeSite L) {ell : ℕ} (hell : 0 < ell)
    (hx : x ∈ stepBlockOf y 0 ell) : x = y := by
  funext μ
  have h := (mem_stepBlockOf.mp hx) μ
  apply Fin.ext
  have hd : (0 : ℕ) ∣ ((x μ).val - (y μ).val) := h.2.2
  have : (x μ).val - (y μ).val = 0 := Nat.eq_zero_of_zero_dvd hd
  omega

/-- **MUST-FIRE on the `α₀ ≤ 1` side of the refutation.** The refutation's arithmetic genuinely uses
`α₀² < 6`: at `α₀ = √8` (i.e. `t = −1`, the antipodal constant) the blocked radius
`√(4α₀² − α₀⁴/2)` equals `0`, so the inequality `α₀ < √(4α₀² − α₀⁴/2)` is FALSE there and the
refutation's final step would not close. Kernel-checked at that point. -/
theorem refutation_arithmetic_fails_at_eight :
    ¬ (Real.sqrt 8 < Real.sqrt (4 * 8 - 8 ^ 2 / 2)) := by
  norm_num

/-- **NON-VACUITY of §6 at a computed point.** At the constant background `gOf (24/25)` the
positive bound is satisfied with BOTH sides strictly positive, and the actual ratio `7√2/5` sits
strictly between the two ends of the sandwich `[2, 2+5π]` — so neither end is attained here and the
bound is a genuine inequality, not an identity in disguise. -/
theorem positive_bound_nonvacuous (Lam : PeriodicLatticeExtent) :
    0 < frobSupBond (constU (gOf (24 / 25)) Lam)
      ∧ 0 < frobSupBond (ubarCoarse 2 (constU (gOf (24 / 25)) Lam))
      ∧ frobSupBond (ubarCoarse 2 (constU (gOf (24 / 25)) Lam))
          = (7 * Real.sqrt 2 / 5) * frobSupBond (constU (gOf (24 / 25)) Lam)
      ∧ (7 * Real.sqrt 2 / 5) < blkConst := by
  have hin : 0 < frobSupBond (constU (gOf (24 / 25)) Lam) :=
    frobSupBond_constU_gOf_pos (24 / 25) (by norm_num) (by norm_num)
  have hratio : frobSupBond (ubarCoarse 2 (constU (gOf (24 / 25)) Lam))
      = (7 * Real.sqrt 2 / 5) * frobSupBond (constU (gOf (24 / 25)) Lam) := by
    rw [coarse_blocking_ratio_two (24 / 25) (by norm_num) (by norm_num)]
    congr 1
    rw [show (2 : ℝ) * (1 + 24 / 25) = (7 / 5) ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    ring
  have hfac := AdalyFormal.Balaban.BlockedBackground.expansion_factor_bounds
  have hblk := blkConst_bounds
  refine ⟨hin, ?_, hratio, by linarith [hfac.2, hblk.1]⟩
  rw [hratio]
  have : (0 : ℝ) < 7 * Real.sqrt 2 / 5 := by linarith [hfac.1]
  positivity

/-! ## §11 — AXIOM AUDIT (total coverage, both message forms) -/

#print axioms entry_star
#print axioms e00re
#print axioms e11
#print axioms e10
#print axioms frobSq_eq
#print axioms scalar_val
#print axioms offdiag01
#print axioms offdiag10
#print axioms diag11
#print axioms alg_sq
#print axioms comb_frobSq
#print axioms comb_det
#print axioms exp_closed
#print axioms exp_mem_special
#print axioms frobNorm_su2Exp_sub_one_le_uncond
#print axioms exp_su2Alg_mem_special_of_carrier
#print axioms Hbad
#print axioms Hbad_antiHerm
#print axioms Hbad_trace_ne
#print axioms exp_Hbad
#print axioms exp_Hbad_not_special
#print axioms Hherm
#print axioms Hherm_trace
#print axioms Hherm_not_antiHerm
#print axioms exp_Hherm
#print axioms exp_Hherm_not_special
#print axioms card_stepBlockOf_le
#print axioms weight_sum_le_one
#print axioms coordSteps_lt
#print axioms gammaPath_length_le
#print axioms ell_pos_of_mem
#print axioms frobNorm_loopVar_sub_one_le
#print axioms blockExponent_trace
#print axioms blockExponent_antiHerm
#print axioms frobNorm_blockExponent_le'
#print axioms blkConstOf
#print axioms blkConst
#print axioms blkConst_eq
#print axioms blkConst_bounds
#print axioms blkConst_ge_one
#print axioms blkConst_pos
#print axioms frobNorm_ubarSU2_sub_one_le
#print axioms frobSupBond_ubarSU2_le
#print axioms frobSupBond_ubarCoarse_le
#print axioms frobSupBond_ubarCoarse_le_two
#print axioms ubarBlk
#print axioms blkTower_ubar_zero
#print axioms blkTower_ubar_succ
#print axioms frobSupBond_wit
#print axioms frobSupBond_blocked_wit
#print axioms blocked_wit_gt
#print axioms classPropagation_fails_for_ubarSU2
#print axioms classPropagation_fails_inside_admissible_radius
#print axioms holonomyElem_constU
#print axioms refutation_witness_facts
#print axioms coarse_blocking_ratio_two
#print axioms no_contraction_ubarCoarse
#print axioms blkConst_two_sided
#print axioms no_contraction_ubarCoarse_at_any_ell
#print axioms LevelClassGeom
#print axioms geomClassPropagation_holds_for_ubarSU2
#print axioms levelClassGeom_at_rate_one
#print axioms LevelClassFine
#print axioms fineClassPropagation_fails_for_ubarSU2
#print axioms classPropagation_holds_at_depth_zero
#print axioms tower_radius_le
#print axioms tower_coercive_to_depth
#print axioms admissible_radius_exact
#print axioms depth_exact_at_1e_neg_20
#print axioms depth_exact_at_1e_neg_25
#print axioms ubarCoarse_trivialU
#print axioms stepBlockOf_zero_stride_singleton
#print axioms refutation_arithmetic_fails_at_eight
#print axioms positive_bound_nonvacuous

end AdalyFormal.Balaban.ClassPropagationUbar
