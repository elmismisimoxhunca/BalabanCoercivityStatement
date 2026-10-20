import AdalyFormal.Balaban.LevelTargetWitness
import AdalyFormal.Balaban.LemmaAssembly
import AdalyFormal.Balaban.RegularUGamma0
import AdalyFormal.Balaban.FullySupplied

set_option autoImplicit false
set_option maxRecDepth 16000

/-!
# `WitnessInequality` — evaluating the level-corrected target's INEQUALITY at `wField`

`LevelTargetWitness.target_domain_nonempty` proved that
`ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform`'s two `Btil` clauses are satisfiable,
with strictly positive `bondEnergy`, by `wField = Pi.single ((1,0,0), 2) suTwoWitness`. It
deliberately said nothing about whether the target's INEQUALITY

  `γ₀ * bondEnergy Btil ≤ cStarDeltaKCFormCorr S levels U Dinv Btil`

holds there. This file answers that question. The answer is that **it does not, and cannot for any
`γ₀`**: the ratio is driven to zero along admissible data.

## The mechanism, stated before any construction

`bondEnergy wField = ‖suTwoWitness‖²` is a FIXED constant — it does not depend on `L`, on `S`, on
`levels` or on `U`. The right-hand side, by contrast, is a Schur complement taken over the fibre
`ker Q_{S.fibre}`, and CMP96 p.245's `Q_ell` carries the weight `ell^{-(d+1)} = ell^{-4}`. So
`Q_{S.fibre}` of a SINGLE-BOND SPIKE is `O(S.fibre^{-4})`, while the left-hand side does not move at
all. Since `γ₀` is quantified FIRST and `S` is quantified by the target's own `∀`, the chooser of
`S.fibre` is the adversary, and the statement is empty.

## What is actually built here

* §1 two general, reusable tools: the **projection-minimality** upper bound for
  `deltaJQuadFormCovFaithful` (the `v ∈ V` refinement of
  `CStarDeltaKCCoercive.deltaJQuadFormCovFaithful_le_dstarDQuadForm`, which is its `v = 0` case),
  and the **absolute curl bound** `plaqEnergy (flatCurlValue A) ≤ 32 · bondEnergy A` assembled from
  `LemmaAssembly.sum_plaqBondSq_le` (LAW-19: the incidence count is not rebuilt).
* §2 `spreadBond` — the block-constant lift of a coarse field — and the operator identity
  `Q_ell (spreadBond ell r) = (1/ell) • r` for every coarse `r` that is ANTISYMMETRIC under the
  coarse shift. This is the file's mathematical core and it is general in `ell`, `L` and `r`.
* §3 the explicit datum, and the closed form of `fullC` on it.
* §4 the upper bound on the target's right-hand side at `wField`.
* §5 the datum, the closed form of `fullC` on it, the competitor, the four spike counts, the
  consequence for the target (`target_refuted`), and §5g the strict POSITIVITY at the datum.

All of §2–§5 are at `U = trivialU`. That is not a weakening of the negative conclusion: a
counterexample at one admissible `U` refutes a statement quantified over all admissible `U`.

## ⚠ HONEST SCOPE — what is refuted, and what is NOT

* **What is refuted** is `ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform` AS WRITTEN in
  this tree. `target_refuted` negates that exact declaration, not a restated copy.
* **The located mechanism is a SCALE-NORMALISATION MISMATCH INSIDE THE TARGET STATEMENT**, and it is
  reported as a fact, not adjudicated. The target's left-hand side is `bondEnergy Btil`, the
  UNNORMALISED sum `∑_b ‖Btil b‖²` over FINE bonds, while `Btil` is a `Λ'`-level object and the
  right-hand side is built from `Q_{S.fibre}`, which carries CMP96 p.245's weight
  `S.fibre^{-(d+1)} = S.fibre^{-4}`. The chooser of `S.fibre` is the target's own `∀`; the chooser of
  `γ₀` is its `∃`, quantified FIRST. Whether the correct repair is a normalised left-hand side, an
  `ell`-dependent `γ₀`, or a restricted `Btil` class is a STATEMENT question and is not decided here.
* **This is NOT a refutation of Bałaban's Lemma, and no claim is made about CMP99b p.428.** It is a
  refutation of one formal encoding of it.
* **`wField` is admissible**: it satisfies both `Btil` clauses with strictly positive `bondEnergy`
  (`LevelTargetWitness.target_domain_nonempty`), and `target_refuted` consumes exactly those two
  clauses. So the counterexample is inside the target's own domain, not outside it.
* **The failure is a RATE failure, not a vanishing — and that is PROVED, §5g.**
  `cStar_wField_pos` establishes `0 < cStarDeltaKCFormCorr …` at the datum in the kernel, so the
  target is not being defeated by its right-hand side collapsing to `0` (the mode
  `CStarDeltaKCCoercive.cStarDeltaKC_coercivity_refuted` exhibits for the COLLAPSED encoding).
  ~~That strict positivity is NOT formalised here; only the upper bound is.~~ (SUPERSEDED in the same
  pass, retained struck: §5g formalises it.) Exploratory numerics (`compute/witness_inequality/`,
  which under the reform charter SIGN NOTHING) put the ratio at `2.25e-2, 3.61e-3, 8.31e-4, 2.45e-4`
  for `ell = 3,4,5,6`; only the SIGN and the upper bound are kernel facts, the rate is not.
* **The constant `768` is not sharp** and is not claimed to be: it is `32` (from
  `plaqEnergy_flatCurl_le`) times `24` (from `card_bond`, the crude `‖wS‖_∞`-times-cardinality bound
  on `bondEnergy wS`). The exponent `ell^{-3}` is likewise not sharp — the measured decay of the true
  minimum is faster. Nothing downstream should quote either as an estimate.
-/

namespace AdalyFormal.Balaban.WitnessInequality

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU oneLevelUniv deltaKernelImageCovH
  gradCovariantAdjointLM RcovLM RcovLM_oneLevelUniv_eq_zero plaqFnEquiv)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue flatCurlLM
  curlValueCovariant_trivialU_eq curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy bondEnergy_nonneg
  plaqEnergy_nonneg frobSupBond)
open AdalyFormal.Balaban.LemmaAssembly (plaqBondSq sum_plaqBondSq_le)
open AdalyFormal.Balaban.RegularUGamma0 (covPlaqInner_self_eq_plaqEnergy)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply lineCoarseRestrictCov_trivialU)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_eq pathSite_apply_ne pathSite_apply_self_val
  droppedBondLast)
open AdalyFormal.Balaban.CoarseCurl (coarseShift periodicLatticeShift_injective
  coarseShift_mem_coarseLattice CoarsePlaquette)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo stokesU stokesPhi stokesPhi_apply
  stokes_factoring hsInner_smul_right)
open AdalyFormal.Balaban.FullReparamC (fullC fullC_free fullC_dropped dinvC dinvC_hinv solvedValue
  IsDropped droppedBondLast_injective isDropped_droppedBondLast)
open AdalyFormal.Balaban.ReparamCSuTwo (restFunctional coeffDc)
open AdalyFormal.Balaban.FullySupplied (restFunctional_eq dinvC_trivialU)
open AdalyFormal.Balaban.LevelTargetWitness (oneSite oneSite_zero wBond wBond_dir
  wBond_base_zero wField wField_apply_self wField_apply_of_ne wField_axial wField_dropped
  wField_bondEnergy_pos wBond_ne_droppedBondLast)
open AdalyFormal.Balaban.CStarLevelCorrected (LevelSplit deltaKCorr cStarDeltaKCFormCorr)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — two general tools

Both are `ell`-, `levels`-, `U`- and `L`-general. Neither mentions the witness. -/

/-- **PROJECTION MINIMALITY, step 1.** Subtracting a member of the constraint subspace `V` does not
change the correction target `D_UA − P_{D_U(V)}(D_UA)`: the projection fixes `D_Uv`. -/
theorem hjCorrectionTargetCovFaithful_sub_mem (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A v : Bond L → SuTwo) (hv : v ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    hjCorrectionTargetCovFaithful ell levels U (A - v)
      = hjCorrectionTargetCovFaithful ell levels U A := by
  have hfix : curlImageCovProjFaithful ell levels U (curlCovariantLM U v)
      = curlCovariantLM U v :=
    curlImageCovProjFaithful_fixes ell levels U (curl_mem_curlImageCovFaithful_of_mem hv)
  have hsub : curlCovariantLM U (A - v) = curlCovariantLM U A - curlCovariantLM U v := by
    exact map_sub _ _ _
  have hlin : ∀ X Y : PeriodicLatticePlaquette L → SuTwo,
      curlImageCovProjFaithful ell levels U (X - Y)
        = curlImageCovProjFaithful ell levels U X
          - curlImageCovProjFaithful ell levels U Y := by
    intro X Y
    unfold curlImageCovProjFaithful
    rw [show (plaqFnEquiv L).symm (X - Y)
          = (plaqFnEquiv L).symm X - (plaqFnEquiv L).symm Y from map_sub _ _ _,
      map_sub, map_sub]
  have hproj : curlImageCovProjFaithful ell levels U
        (curlCovariantLM U A - curlCovariantLM U v)
      = curlImageCovProjFaithful ell levels U (curlCovariantLM U A) - curlCovariantLM U v := by
    rw [hlin, hfix]
  unfold hjCorrectionTargetCovFaithful
  rw [hsub, hproj]
  abel

/-- **PROJECTION MINIMALITY.** For EVERY `v` in the constraint subspace `V`,
`Δ_k(A) ≤ ‖D_U(A − v)‖²`. This is the strict refinement of
`deltaJQuadFormCovFaithful_le_dstarDQuadForm` (which is the `v = 0` case) that an UPPER bound on the
Schur complement needs: the Schur complement is a distance, and a distance is bounded by the length
of any competitor. -/
theorem deltaJQuadFormCovFaithful_le_of_sub (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A v : Bond L → SuTwo) (hv : v ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    deltaJQuadFormCovFaithful ell levels U A ≤ dstarDQuadForm U (A - v) := by
  have hkey : deltaJQuadFormCovFaithful ell levels U A
      = deltaJQuadFormCovFaithful ell levels U (A - v) := by
    unfold deltaJQuadFormCovFaithful
    rw [curlCov_hjExtensionCovFaithful, curlCov_hjExtensionCovFaithful,
      hjCorrectionTargetCovFaithful_sub_mem ell levels U A v hv]
  rw [hkey]
  exact CStarDeltaKCCoercive.deltaJQuadFormCovFaithful_le_dstarDQuadForm ell levels U (A - v)

/-- Four-term expansion bound in a normed space: `‖a+b−c−d‖² ≤ 4(‖a‖²+‖b‖²+‖c‖²+‖d‖²)`. -/
theorem norm_four_sq_le (a b c d : SuTwo) :
    ‖a + b - c - d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖d‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h1 : ‖a + b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc ‖a + b - c - d‖ ≤ ‖a + b - c‖ + ‖d‖ := norm_sub_le _ _
      _ ≤ (‖a + b‖ + ‖c‖) + ‖d‖ := by linarith [norm_sub_le (a + b) c]
      _ ≤ ((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖ := by linarith [norm_add_le a b]
      _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by ring
  have h2 : (0 : ℝ) ≤ ‖a + b - c - d‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖),
    sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖),
    norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg d]

/-- **THE ABSOLUTE CURL BOUND.** `plaqEnergy (∂A) ≤ 32 · bondEnergy A`, with a constant depending
only on the dimension: `4` from the four-term Cauchy–Schwarz and `8` from
`LemmaAssembly.sum_plaqBondSq_le`'s incidence count (four incidences of `2` — not rebuilt here,
LAW-19). No lattice size, no scale, no background. -/
theorem plaqEnergy_flatCurl_le (A : Bond L → SuTwo) :
    plaqEnergy (flatCurlValue A) ≤ 32 * bondEnergy A := by
  have hterm : ∀ p : PeriodicLatticePlaquette L,
      ‖flatCurlValue A p‖ ^ 2 ≤ 4 * plaqBondSq A p := by
    intro p
    unfold flatCurlValue plaqBondSq
    exact norm_four_sq_le _ _ _ _
  have hstep : plaqEnergy (flatCurlValue A)
      ≤ ∑ p : PeriodicLatticePlaquette L, 4 * plaqBondSq A p := by
    unfold plaqEnergy
    exact Finset.sum_le_sum fun p _ => hterm p
  rw [← Finset.mul_sum] at hstep
  have h8 := sum_plaqBondSq_le A
  linarith

/-- The same, expressed against `dstarDQuadForm` at the trivial background — the exact form §4
consumes. -/
theorem dstarDQuadForm_trivialU_le (A : Bond L → SuTwo) :
    dstarDQuadForm (trivialU L) A ≤ 32 * bondEnergy A := by
  have h : dstarDQuadForm (trivialU L) A = plaqEnergy (flatCurlValue A) := by
    unfold dstarDQuadForm
    rw [curlValueCovariant_trivialU_eq, covPlaqInner_self_eq_plaqEnergy]
  rw [h]
  exact plaqEnergy_flatCurl_le A

/-! ## §2 — `spreadBond`, and `Q_ell ∘ spread = (1/ell) • id` on antisymmetric coarse fields -/

/-- The coarse site of `x` — each coordinate rounded DOWN to a multiple of `ell`. This is the
witness `AdmissibleSubspace.coarseLattice_exists` already constructs inside its existential; named
here so it can be computed with. -/
def coarseSite (ell : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun μ => ⟨ell * ((x μ).val / ell), by
    have h := (x μ).isLt
    have : ell * ((x μ).val / ell) ≤ (x μ).val := by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    omega⟩

theorem coarseSite_val (ell : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((coarseSite ell x) μ).val = ell * ((x μ).val / ell) := rfl

theorem coarseSite_mem (ell : ℕ) (x : PeriodicLatticeSite L) :
    coarseSite ell x ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice]
  intro μ
  rw [coarseSite_val]
  exact Nat.mul_mod_right ell _

/-- **`spreadBond`** — the block-constant lift of a coarse bond field to a fine bond field: the
value at `(z, μ)` is the coarse field's value at the coarse bond `(coarseSite z, μ)`. -/
noncomputable def spreadBond (ell : ℕ) (r : CoarseBond L ell → SuTwo) : Bond L → SuTwo :=
  fun b => r (⟨coarseSite ell b.1, coarseSite_mem ell b.1⟩, b.2)

/-- Rounding down to the block base, when the point is inside the block. -/
theorem coarse_round {ell Y v : ℕ} (hell : 0 < ell) (hY : Y % ell = 0)
    (h1 : Y ≤ v) (h2 : v < Y + ell) : ell * (v / ell) = Y := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hY
  subst hk
  have hv : v = ell * k + (v - ell * k) := by omega
  rw [hv, Nat.mul_add_div hell, Nat.div_eq_of_lt (by omega), Nat.add_zero]

theorem coarseSite_of_coarse {ell : ℕ} (hell : 0 < ell) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) : coarseSite ell y = y := by
  funext μ
  apply Fin.ext
  rw [coarseSite_val]
  exact coarse_round hell (mem_CoarseLattice.mp hy μ) (le_refl _) (by omega)

/-- **STEP A — the coarse site of a path point started inside a block.** Walking `i < ell` steps in
direction `μ` from a point of `B(y)` either stays in `B(y)` or lands in the NEXT block along `μ`,
`B(y + ell·e_μ)`, and nowhere else. The `pathSite y μ ell` on the right is literally
`CoarseCurl.coarseShift y ell μ` (same `Nat.iterate`). -/
theorem coarseSite_pathSite {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell) (μ : Fin 3) {i : ℕ} (hi : i < ell) :
    coarseSite ell (pathSite x μ i)
      = if (x μ).val + i < (y μ).val + ell then y else pathSite y μ ell := by
  have hyc := mem_CoarseLattice.mp hy
  have hb := mem_blockOf.mp hx
  have hfit := coarseLattice_mem_fits hdvd hy
  funext ν
  apply Fin.ext
  by_cases hν : ν = μ
  · subst hν
    have hfitν : (y ν).val + ell ≤ L ν + 1 := hfit ν
    have hbν := hb ν
    have hrhs : ((if (x ν).val + i < (y ν).val + ell then y else pathSite y ν ell) ν).val
        = if (x ν).val + i < (y ν).val + ell then (y ν).val
          else ((y ν).val + ell) % (L ν + 1) := by
      split
      · rfl
      · exact pathSite_apply_self_val y ν ell
    have hmodell : ((y ν).val + ell) % ell = 0 := by
      rw [Nat.add_mod_right]; exact hyc ν
    rw [coarseSite_val, pathSite_apply_self_val, hrhs]
    split
    · rename_i hlt
      have hmod : ((x ν).val + i) % (L ν + 1) = (x ν).val + i :=
        Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      exact coarse_round hell (hyc ν) (by omega) (by omega)
    · rename_i hge
      rw [not_lt] at hge
      by_cases hedge : (y ν).val + ell = L ν + 1
      · have hmod : ((x ν).val + i) % (L ν + 1) = (x ν).val + i - (L ν + 1) := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hmod, hedge, Nat.mod_self]
        exact coarse_round hell (Nat.zero_mod ell) (Nat.zero_le _) (by omega)
      · have hroom : (y ν).val + ell + ell ≤ L ν + 1 :=
          ReparamCDisjoint.coarse_coord_add_ell_le hdvd ν ((y ν).val + ell) hmodell (by omega)
        have hmod : ((x ν).val + i) % (L ν + 1) = (x ν).val + i :=
          Nat.mod_eq_of_lt (by omega)
        rw [hmod, Nat.mod_eq_of_lt (by omega)]
        exact coarse_round hell hmodell (by omega) (by omega)
  · have hrhs : ((if (x μ).val + i < (y μ).val + ell then y else pathSite y μ ell) ν).val
        = (y ν).val := by
      split
      · rfl
      · rw [pathSite_apply_ne y μ ν ell hν]
    rw [coarseSite_val, pathSite_apply_ne x μ ν i hν, hrhs]
    exact coarse_round hell (hyc ν) (hb ν).1 (hb ν).2

/-! ### §2b — the two counting inputs -/

/-- The signed inner sum over the length-`ell` line integral: `ell − 2a`, where `a = V − Y` is the
point's `μ`-offset inside its block. Stated without natural subtraction. -/
theorem sum_sign_range {ell : ℕ} (hell : 0 < ell) {Y V : ℕ} (h1 : Y ≤ V) (h2 : V < Y + ell) :
    ∑ i ∈ Finset.range ell, (if V + i < Y + ell then (1 : ℝ) else -1)
      = 2 * (Y : ℝ) + (ell : ℝ) - 2 * (V : ℝ) := by
  classical
  have hfilter : (Finset.range ell).filter (fun i => V + i < Y + ell)
      = Finset.range (Y + ell - V) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hcard1 : ((Finset.range ell).filter (fun i => V + i < Y + ell)).card = Y + ell - V := by
    rw [hfilter, Finset.card_range]
  have hcard2 : ((Finset.range ell).filter (fun i => ¬ (V + i < Y + ell))).card = V - Y := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.range ell) (p := fun i => V + i < Y + ell)
    rw [hcard1, Finset.card_range] at h
    omega
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard1, hcard2]
  have e1 : ((Y + ell - V : ℕ) : ℝ) = (Y : ℝ) + (ell : ℝ) - (V : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : ((V - Y : ℕ) : ℝ) = (V : ℝ) - (Y : ℝ) := by
    rw [Nat.cast_sub h1]
  simp only [nsmul_eq_mul, mul_one, mul_neg_one, e1, e2]
  ring

/-- The `μ`-offset reflection of a block: `a ↦ ell − 1 − a`. An involution of `B(y)`. -/
def blockRefl (ell : ℕ) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (hell : 0 < ell) (hfit : (y μ).val + ell ≤ L μ + 1) (x : PeriodicLatticeSite L) :
    PeriodicLatticeSite L :=
  Function.update x μ ⟨(y μ).val + (ell - 1 - ((x μ).val - (y μ).val)), by omega⟩

theorem blockRefl_val {ell : ℕ} {y : PeriodicLatticeSite L} {μ : Fin 3}
    (hell : 0 < ell) (hfit : (y μ).val + ell ≤ L μ + 1) (x : PeriodicLatticeSite L) :
    ((blockRefl ell y μ hell hfit x) μ).val
      = (y μ).val + (ell - 1 - ((x μ).val - (y μ).val)) := by
  rw [blockRefl, Function.update_self]

theorem blockRefl_apply_ne {ell : ℕ} {y : PeriodicLatticeSite L} {μ ν : Fin 3}
    (hell : 0 < ell) (hfit : (y μ).val + ell ≤ L μ + 1) (x : PeriodicLatticeSite L)
    (hν : ν ≠ μ) : (blockRefl ell y μ hell hfit x) ν = x ν := by
  rw [blockRefl]; exact Function.update_of_ne hν _ _

theorem blockRefl_mem {ell : ℕ} {y : PeriodicLatticeSite L} {μ : Fin 3}
    (hell : 0 < ell) (hfit : (y μ).val + ell ≤ L μ + 1) {x : PeriodicLatticeSite L}
    (hx : x ∈ blockOf y ell) : blockRefl ell y μ hell hfit x ∈ blockOf y ell := by
  rw [mem_blockOf] at hx ⊢
  intro ν
  by_cases hν : ν = μ
  · subst hν
    rw [blockRefl_val hell hfit]
    have := hx ν
    omega
  · rw [blockRefl_apply_ne hell hfit x hν]
    exact hx ν

theorem blockRefl_invol {ell : ℕ} {y : PeriodicLatticeSite L} {μ : Fin 3}
    (hell : 0 < ell) (hfit : (y μ).val + ell ≤ L μ + 1) {x : PeriodicLatticeSite L}
    (hx : x ∈ blockOf y ell) :
    blockRefl ell y μ hell hfit (blockRefl ell y μ hell hfit x) = x := by
  have hxb := mem_blockOf.mp hx
  funext ν
  by_cases hν : ν = μ
  · subst hν
    apply Fin.ext
    rw [blockRefl_val hell hfit, blockRefl_val hell hfit]
    have := hxb ν
    omega
  · rw [blockRefl_apply_ne hell hfit _ hν, blockRefl_apply_ne hell hfit _ hν]

/-- **THE COORDINATE SUM OVER A BLOCK.** `2·∑_{x∈B(y)} x_μ + ell³ = ell³·(2y_μ + ell)`, by the
offset reflection `a ↦ ell−1−a` and `|B(y)| = ell³` (`card_blockOf_of_coarse`, LAW-19). Stated
subtraction-free so the cast to `ℝ` is a `push_cast`. -/
theorem two_mul_sum_coord {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    2 * (∑ x ∈ blockOf y ell, (x μ).val) + ell ^ 3 = ell ^ 3 * (2 * (y μ).val + ell) := by
  classical
  have hfit : (y μ).val + ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd hy μ
  have hmem : ∀ x ∈ blockOf y ell, blockRefl ell y μ hell hfit x ∈ blockOf y ell :=
    fun x hx => blockRefl_mem hell hfit hx
  have hinv : ∀ x ∈ blockOf y ell,
      blockRefl ell y μ hell hfit (blockRefl ell y μ hell hfit x) = x :=
    fun x hx => blockRefl_invol hell hfit hx
  have himg : Finset.image (blockRefl ell y μ hell hfit) (blockOf y ell) = blockOf y ell := by
    refine Finset.Subset.antisymm (Finset.image_subset_iff.mpr hmem) ?_
    intro x hx
    exact Finset.mem_image.mpr ⟨blockRefl ell y μ hell hfit x, hmem x hx, hinv x hx⟩
  have hinj : ∀ x ∈ blockOf y ell, ∀ x' ∈ blockOf y ell,
      blockRefl ell y μ hell hfit x = blockRefl ell y μ hell hfit x' → x = x' := by
    intro x hx x' hx' h
    rw [← hinv x hx, ← hinv x' hx', h]
  have hswap : ∑ x ∈ blockOf y ell, (x μ).val
      = ∑ x ∈ blockOf y ell, ((blockRefl ell y μ hell hfit x) μ).val := by
    conv_lhs => rw [← himg]
    exact Finset.sum_image hinj
  have hpair : ∑ x ∈ blockOf y ell,
        ((x μ).val + ((blockRefl ell y μ hell hfit x) μ).val + 1)
      = ∑ _x ∈ blockOf y ell, (2 * (y μ).val + ell) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxb := (mem_blockOf.mp hx) μ
    rw [blockRefl_val hell hfit]
    omega
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    card_blockOf_of_coarse hdvd hy, smul_eq_mul, smul_eq_mul, mul_one] at hpair
  rw [two_mul]
  conv_lhs => rw [hswap]
  omega

/-! ### §2c — THE OPERATOR IDENTITY -/

/-- **`Q_ell` ON BLOCK-CONSTANT, COARSE-ANTISYMMETRIC FIELDS.**

If `A` is constant on each block (`hconst`) and reverses sign under the coarse shift by `ell`
(`hanti`), then

  `Q_ell A (y, μ) = (1/ell) · A (y, μ)`   at every coarse bond.

The `1/ell` — not `1` — is the whole content: `Q_ell` carries CMP96 p.245's weight `ell^{-4}` over
`ell^4` summands, and the antisymmetry converts the triangular overlap between two adjacent blocks
into the single net factor `ell³/ell⁴`. General in `L`, `ell`, `A`, and the coarse bond; the only
hypotheses are `0 < ell` and the standing torus compatibility `ell ∣ L μ + 1`. -/
theorem Q_of_blockConst_anti {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : Bond L → SuTwo)
    (hconst : ∀ (z : PeriodicLatticeSite L) (ν : Fin 3), A (z, ν) = A (coarseSite ell z, ν))
    (hanti : ∀ (z : PeriodicLatticeSite L) (ν : Fin 3), A (pathSite z ν ell, ν) = - A (z, ν))
    (c : CoarseBond L ell) :
    lineCoarseRestrictCov (trivialU L) ell A c = (1 / (ell : ℝ)) • A (c.1.1, c.2) := by
  classical
  have hy : (c.1.1 : PeriodicLatticeSite L) ∈ CoarseLattice L ell := c.1.2
  set y : PeriodicLatticeSite L := (c.1.1 : PeriodicLatticeSite L) with hydef
  set μ : Fin 3 := c.2 with hmudef
  have hterm : ∀ x ∈ blockOf y ell, ∀ i ∈ Finset.range ell,
      A (pathSite x μ i, μ)
        = (if (x μ).val + i < (y μ).val + ell then (1 : ℝ) else -1) • A (y, μ) := by
    intro x hx i hi
    rw [hconst (pathSite x μ i) μ,
      coarseSite_pathSite hell hdvd hy hx μ (Finset.mem_range.mp hi)]
    split
    · rw [one_smul]
    · rw [hanti y μ, neg_one_smul]
  have hsum : ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell,
      (if (x μ).val + i < (y μ).val + ell then (1 : ℝ) else -1) = (ell : ℝ) ^ 3 := by
    have hinner : ∀ x ∈ blockOf y ell,
        ∑ i ∈ Finset.range ell, (if (x μ).val + i < (y μ).val + ell then (1 : ℝ) else -1)
          = 2 * ((y μ).val : ℝ) + (ell : ℝ) - 2 * ((x μ).val : ℝ) := by
      intro x hx
      have hxb := (mem_blockOf.mp hx) μ
      exact sum_sign_range hell hxb.1 hxb.2
    have hcoord := two_mul_sum_coord hell hdvd hy μ
    have hcoordR : 2 * (∑ x ∈ blockOf y ell, ((x μ).val : ℝ)) + (ell : ℝ) ^ 3
        = (ell : ℝ) ^ 3 * (2 * ((y μ).val : ℝ) + (ell : ℝ)) := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) hcoord
      push_cast at h
      linarith
    rw [Finset.sum_congr rfl hinner]
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_blockOf_of_coarse hdvd hy,
      nsmul_eq_mul, ← Finset.mul_sum]
    push_cast
    linarith
  have step1 : ∀ x ∈ blockOf y ell,
      ∑ i ∈ Finset.range ell, A (pathSite x μ i, μ)
        = (∑ i ∈ Finset.range ell,
            (if (x μ).val + i < (y μ).val + ell then (1 : ℝ) else -1)) • A (y, μ) := by
    intro x hx
    rw [Finset.sum_congr rfl (fun i hi => hterm x hx i hi), ← Finset.sum_smul]
  rw [lineCoarseRestrictCov_trivialU]
  unfold LineIntegralCovariant.lineCoarseRestrictSuTwo
  rw [Finset.sum_congr rfl step1, ← Finset.sum_smul, hsum, smul_smul]
  have hne : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show (1 / (ell : ℝ) ^ 4) * (ell : ℝ) ^ 3 = 1 / (ell : ℝ) by field_simp]


/-! ## §3 — the assembled bound: a block-constant antisymmetric COMPETITOR caps `Δ_k`

This is the step §1 and §2 exist for. Nothing here is specific to the witness. -/

/-- **THE COMPETITOR BOUND.** If a field `B`'s coarse average at the fibre level `ell` is reproduced
by a block-constant, coarse-antisymmetric `s` (in the precise sense
`Q_ell B (y,μ) = (1/ell) · s (y,μ)`, which by §2c is exactly `Q_ell B = Q_ell s`), then

  `Δ_k(B) ≤ 32 · bondEnergy s`.

The point: `s` is spread over `ell³` bonds per coarse bond, so `bondEnergy s` is SMALL when
`Q_ell B` is small — and `Q_ell` carries the weight `ell^{-4}`. -/
theorem deltaJ_le_of_competitor {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels (trivialU L)).HasOrthogonalProjection]
    (B s : Bond L → SuTwo)
    (hconst : ∀ (z : PeriodicLatticeSite L) (ν : Fin 3), s (z, ν) = s (coarseSite ell z, ν))
    (hanti : ∀ (z : PeriodicLatticeSite L) (ν : Fin 3), s (pathSite z ν ell, ν) = - s (z, ν))
    (hmatch : ∀ c : CoarseBond L ell,
      lineCoarseRestrictCov (trivialU L) ell B c = (1 / (ell : ℝ)) • s (c.1.1, c.2))
    (hR : RcovLM (trivialU L) levels (gradCovariantAdjointLM (trivialU L) (B - s)) = 0) :
    deltaJQuadFormCovFaithful ell levels (trivialU L) B ≤ 32 * bondEnergy s := by
  have hQv : lineCoarseRestrictCovLM (trivialU L) ell (B - s) = 0 := by
    have hlin : lineCoarseRestrictCovLM (trivialU L) ell (B - s)
        = lineCoarseRestrictCovLM (trivialU L) ell B
          - lineCoarseRestrictCovLM (trivialU L) ell s := map_sub _ _ _
    rw [hlin]
    funext c
    simp only [Pi.sub_apply, Pi.zero_apply, lineCoarseRestrictCovLM_apply]
    rw [hmatch c, Q_of_blockConst_anti hell hdvd s hconst hanti c, sub_self]
  have hv : (B - s) ∈ gaugeConstraintSubspaceCovFaithful ell levels (trivialU L) :=
    mem_gaugeConstraintSubspaceCovFaithful.mpr ⟨hQv, hR⟩
  have h1 := deltaJQuadFormCovFaithful_le_of_sub ell levels (trivialU L) B (B - s) hv
  rw [sub_sub_cancel] at h1
  exact le_trans h1 (dstarDQuadForm_trivialU_le s)

/-- The `oneLevelUniv` instance, where the `R`-clause of the constraint subspace is vacuous
(`RcovLM_oneLevelUniv_eq_zero`) and so `hR` is discharged for free. -/
theorem deltaJ_le_of_competitor_oneLevel {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    [(deltaKernelImageCovH (trivialU L) (oneLevelUniv L)).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell (oneLevelUniv L) (trivialU L)).HasOrthogonalProjection]
    (B s : Bond L → SuTwo)
    (hconst : ∀ (z : PeriodicLatticeSite L) (ν : Fin 3), s (z, ν) = s (coarseSite ell z, ν))
    (hanti : ∀ (z : PeriodicLatticeSite L) (ν : Fin 3), s (pathSite z ν ell, ν) = - s (z, ν))
    (hmatch : ∀ c : CoarseBond L ell,
      lineCoarseRestrictCov (trivialU L) ell B c = (1 / (ell : ℝ)) • s (c.1.1, c.2)) :
    deltaJQuadFormCovFaithful ell (oneLevelUniv L) (trivialU L) B ≤ 32 * bondEnergy s :=
  deltaJ_le_of_competitor hell hdvd (oneLevelUniv L) B s hconst hanti hmatch
    (RcovLM_oneLevelUniv_eq_zero (trivialU L) _)

/-! ## §4 — `pathSite` as a torus translation, and `Q` of a single spike -/

/-- `pathSite` composes additively (it is a `Nat.iterate`). -/
theorem pathSite_add (z : PeriodicLatticeSite L) (μ : Fin 3) (i j : ℕ) :
    pathSite z μ (i + j) = pathSite (pathSite z μ j) μ i := by
  show (fun w => periodicLatticeShift w μ)^[i + j] z
      = (fun w => periodicLatticeShift w μ)^[i] ((fun w => periodicLatticeShift w μ)^[j] z)
  rw [Function.iterate_add_apply]

/-- One full period returns to the start. -/
theorem pathSite_period (z : PeriodicLatticeSite L) (μ : Fin 3) :
    pathSite z μ (L μ + 1) = z := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    apply Fin.ext
    rw [pathSite_apply_self_val, Nat.add_mod_right, Nat.mod_eq_of_lt (z ν).isLt]
  · exact pathSite_apply_ne z μ ν _ hν

/-- **`pathSite · μ i` is a bijection of sites** — a torus translation. -/
theorem pathSite_bijective (μ : Fin 3) (i : ℕ) :
    Function.Bijective (fun z : PeriodicLatticeSite L => pathSite z μ i) :=
  Finite.injective_iff_bijective.mp
    ((periodicLatticeShift_injective (L := L) μ).iterate i)

/-- Solving `pathSite x μ i = z` for `x`: the unique solution is the backward translate. -/
theorem pathSite_eq_iff {μ : Fin 3} {i : ℕ} (hi : i ≤ L μ + 1)
    (x z : PeriodicLatticeSite L) :
    pathSite x μ i = z ↔ x = pathSite z μ (L μ + 1 - i) := by
  constructor
  · intro h
    have := pathSite_add x μ (L μ + 1 - i) i
    rw [show L μ + 1 - i + i = L μ + 1 by omega, pathSite_period] at this
    rw [← h, ← this]
  · intro h
    subst h
    rw [← pathSite_add, show i + (L μ + 1 - i) = L μ + 1 by omega, pathSite_period]

/-- Reindexing a full-torus sum by a translation. -/
theorem sum_pathSite_reindex (A : Bond L → SuTwo) (μ : Fin 3) (i : ℕ) :
    ∑ x : PeriodicLatticeSite L, A (pathSite x μ i, μ)
      = ∑ x : PeriodicLatticeSite L, A (x, μ) :=
  (pathSite_bijective (L := L) μ i).sum_comp (fun z => A (z, μ))

/-- **`Q_ell` OF A SINGLE SPIKE, same direction.** The double sum collapses to a count of the
translation steps `i < ell` whose backward translate of `z` lands in the block. -/
theorem Q_single_same_dir {ell : ℕ} (c : CoarseBond L ell) (hle : ell ≤ L c.2 + 1)
    (z : PeriodicLatticeSite L) (v : SuTwo) :
    lineCoarseRestrictCov (trivialU L) ell (Pi.single (z, c.2) v) c
      = (1 / (ell : ℝ) ^ 4) • ((((Finset.range ell).filter
          (fun i => pathSite z c.2 (L c.2 + 1 - i) ∈ blockOf c.1.1 ell)).card : ℝ) • v) := by
  classical
  rw [lineCoarseRestrictCov_trivialU]
  unfold LineIntegralCovariant.lineCoarseRestrictSuTwo
  rw [Finset.sum_comm]
  have hinner : ∀ i ∈ Finset.range ell,
      ∑ x ∈ blockOf c.1.1 ell, (Pi.single (z, c.2) v : Bond L → SuTwo) (pathSite x c.2 i, c.2)
        = if pathSite z c.2 (L c.2 + 1 - i) ∈ blockOf c.1.1 ell then v else 0 := by
    intro i hi
    have hile : i ≤ L c.2 + 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hstep : ∀ x : PeriodicLatticeSite L,
        (Pi.single (z, c.2) v : Bond L → SuTwo) (pathSite x c.2 i, c.2)
          = if x = pathSite z c.2 (L c.2 + 1 - i) then v else 0 := by
      intro x
      rw [Pi.single_apply]
      by_cases hx : x = pathSite z c.2 (L c.2 + 1 - i)
      · rw [if_pos hx, if_pos]
        rw [Prod.mk.injEq]
        exact ⟨(pathSite_eq_iff hile x z).mpr hx, rfl⟩
      · rw [if_neg hx, if_neg]
        intro hcon
        have h1 : pathSite x c.2 i = z := (Prod.ext_iff.mp hcon).1
        exact hx ((pathSite_eq_iff hile x z).mp h1)
    rw [Finset.sum_congr rfl (fun x _ => hstep x)]
    exact Finset.sum_ite_eq' _ _ _
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
    add_zero, Finset.filter_congr_decidable, Nat.cast_smul_eq_nsmul]

/-- **`Q_ell` OF A SINGLE SPIKE, other direction: zero.** `Q_ell` at a coarse bond of direction `μ`
reads only fine bonds of direction `μ`. -/
theorem Q_single_other_dir {ell : ℕ} (c : CoarseBond L ell) (z : PeriodicLatticeSite L)
    (ν : Fin 3) (hν : ν ≠ c.2) (v : SuTwo) :
    lineCoarseRestrictCov (trivialU L) ell (Pi.single (z, ν) v) c = 0 := by
  classical
  rw [lineCoarseRestrictCov_trivialU]
  unfold LineIntegralCovariant.lineCoarseRestrictSuTwo
  have hz : ∀ x ∈ blockOf c.1.1 ell, ∀ i ∈ Finset.range ell,
      (Pi.single (z, ν) v : Bond L → SuTwo) (pathSite x c.2 i, c.2) = 0 := by
    intro x _ i _
    rw [Pi.single_apply, if_neg]
    intro hcon
    exact hν ((Prod.ext_iff.mp hcon).2).symm
  rw [Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun i hi => hz x hx i hi)),
    Finset.sum_const_zero, Finset.sum_const_zero, smul_zero]


/-! ## §5 — THE DATUM

`L μ = 2m+5`, so `n := L μ + 1 = 2·(m+3)`. Fibre `ell := m+3 ≥ 3`; constraint level
`constr := 2·ell = n`, so the CONSTRAINT level has exactly one block (the whole torus) — which is
what collapses `fullC` to a two-bond field. Every hypothesis of
`ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform` holds: `2 ≤ ell`, `ell ∣ constr`,
`ell < constr`, `4 ≤ L μ`, `ell ∣ L μ + 1`, `constr ∣ L μ + 1`. -/

/-- The extent: `L μ = 2m+5` in every direction. -/
def wExt (m : ℕ) : PeriodicLatticeExtent := fun _ => 2 * m + 5

/-- The fibre block side. -/
def wEll (m : ℕ) : ℕ := m + 3

theorem wExt_succ (m : ℕ) (μ : Fin 3) : wExt m μ + 1 = 2 * wEll m := by
  simp only [wExt, wEll]; omega

theorem wEll_pos (m : ℕ) : 0 < wEll m := by simp only [wEll]; omega
theorem wEll_three (m : ℕ) : 3 ≤ wEll m := by simp only [wEll]; omega
theorem wConstr_pos (m : ℕ) : 0 < 2 * wEll m := by have := wEll_pos m; omega
theorem wExt_four (m : ℕ) (μ : Fin 3) : 4 ≤ wExt m μ := by simp only [wExt]; omega
theorem wEll_dvd (m : ℕ) (μ : Fin 3) : wEll m ∣ (wExt m μ + 1) :=
  ⟨2, by rw [wExt_succ]; ring⟩
theorem wConstr_dvd (m : ℕ) (μ : Fin 3) : (2 * wEll m) ∣ (wExt m μ + 1) :=
  ⟨1, by rw [wExt_succ]; ring⟩

/-- The `LevelSplit` of the datum: fibre `ell`, constraint `2·ell`. -/
def wSplit (m : ℕ) : LevelSplit :=
  ⟨wEll m, 2 * wEll m, wEll_pos m, ⟨2, by ring⟩, by have := wEll_pos m; omega⟩

theorem wSplit_fibre (m : ℕ) : (wSplit m).fibre = wEll m := rfl
theorem wSplit_constr (m : ℕ) : (wSplit m).constr = 2 * wEll m := rfl

/-- Every site coordinate is `< 2·ell`. -/
theorem site_lt {m : ℕ} (x : PeriodicLatticeSite (wExt m)) (μ : Fin 3) :
    (x μ).val < 2 * wEll m := by
  have h := (x μ).isLt
  simp only [wExt, wEll] at h ⊢
  omega

/-- **At the CONSTRAINT level the only coarse site is the origin.** -/
theorem coarse_at_full_val {m : ℕ} {y : PeriodicLatticeSite (wExt m)}
    (hy : y ∈ CoarseLattice (wExt m) (2 * wEll m)) (μ : Fin 3) : (y μ).val = 0 := by
  have h := mem_CoarseLattice.mp hy μ
  rwa [Nat.mod_eq_of_lt (site_lt y μ)] at h

/-- …so the block at the constraint level is the whole torus. -/
theorem block_full {m : ℕ} {y : PeriodicLatticeSite (wExt m)}
    (hy : y ∈ CoarseLattice (wExt m) (2 * wEll m)) :
    blockOf y (2 * wEll m) = Finset.univ := by
  refine Finset.eq_univ_of_forall fun x => ?_
  rw [mem_blockOf]
  intro μ
  have h0 := coarse_at_full_val hy μ
  have := site_lt x μ
  omega

/-- **At the FIBRE level every coarse coordinate is `0` or `ell`** (there are two blocks per axis). -/
theorem coarse_at_fibre_val {m : ℕ} {y : PeriodicLatticeSite (wExt m)}
    (hy : y ∈ CoarseLattice (wExt m) (wEll m)) (μ : Fin 3) :
    (y μ).val = 0 ∨ (y μ).val = wEll m := by
  have h := mem_CoarseLattice.mp hy μ
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  have hlt := site_lt y μ
  have hpos := wEll_pos m
  have hk2 : k < 2 := by
    by_contra hcon
    have : 2 * wEll m ≤ wEll m * k := by
      calc 2 * wEll m = wEll m * 2 := by ring
        _ ≤ wEll m * k := Nat.mul_le_mul_left _ (by omega)
    omega
  interval_cases k <;> omega

/-- **`Q` at the CONSTRAINT level is the plain torus average** — the block is everything and each
bond is read exactly `n` times, by the translation reindexing `sum_pathSite_reindex`. -/
theorem Q_full {m : ℕ} (A : Bond (wExt m) → SuTwo) (c : CoarseBond (wExt m) (2 * wEll m)) :
    lineCoarseRestrictCov (trivialU (wExt m)) (2 * wEll m) A c
      = (1 / ((2 * wEll m : ℕ) : ℝ) ^ 3) • ∑ x : PeriodicLatticeSite (wExt m), A (x, c.2) := by
  have hne : (((2 * wEll m : ℕ)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := wEll_pos m; omega)
  rw [lineCoarseRestrictCov_trivialU]
  unfold LineIntegralCovariant.lineCoarseRestrictSuTwo
  rw [block_full c.1.2, Finset.sum_comm,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (2 * wEll m)) =>
      sum_pathSite_reindex A c.2 i),
    Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    show (1 / (((2 * wEll m : ℕ)) : ℝ) ^ 4) * (((2 * wEll m : ℕ)) : ℝ)
      = 1 / (((2 * wEll m : ℕ)) : ℝ) ^ 3 by field_simp]

/-- The witness field's full-torus sum: `suTwoWitness` in direction `2`, zero otherwise. -/
theorem sum_wField {m : ℕ} (μ : Fin 3) :
    ∑ x : PeriodicLatticeSite (wExt m), wField (L := wExt m) (wExt_four m) (x, μ)
      = if μ = 2 then suTwoWitness else 0 := by
  classical
  by_cases hμ : μ = 2
  · subst hμ
    rw [if_pos rfl]
    have hstep : ∀ x : PeriodicLatticeSite (wExt m),
        wField (L := wExt m) (wExt_four m) (x, (2 : Fin 3))
          = if x = oneSite (wExt_four m) then suTwoWitness else 0 := by
      intro x
      by_cases hx : x = oneSite (wExt_four m)
      · rw [if_pos hx, hx]
        exact wField_apply_self (wExt_four m)
      · refine (wField_apply_of_ne (wExt_four m) ?_).trans (if_neg hx).symm
        intro hcon
        exact hx (Prod.ext_iff.mp hcon).1
    rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_ite_eq' _ _ _, if_pos
      (Finset.mem_univ _)]
  · rw [if_neg hμ]
    refine Finset.sum_eq_zero fun x _ => ?_
    refine wField_apply_of_ne (wExt_four m) ?_
    intro hcon
    exact hμ (Prod.ext_iff.mp hcon).2

/-- **THE `fullC` VALUE AT A DROPPED BOND.** `−suTwoWitness` at the direction-`2` coarse bond, `0` at
the other two. Read off from `restFunctional_eq` + `dinvC_trivialU` + `Q_full` + `sum_wField`. -/
theorem fullC_wField_dropped {m : ℕ} (c : CoarseBond (wExt m) (2 * wEll m)) :
    fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
        (wField (L := wExt m) (wExt_four m)) (droppedBondLast (2 * wEll m) c)
      = if c.2 = 2 then -suTwoWitness else 0 := by
  have hell : 0 < 2 * wEll m := wConstr_pos m
  have hell2 : 2 ≤ 2 * wEll m := by have := wEll_pos m; omega
  have hne : (((2 * wEll m : ℕ)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [fullC_dropped hell (wConstr_dvd m), solvedValue, restFunctional_eq,
    wField_dropped hell2 (wExt_four m) c, map_zero, sub_zero, dinvC_trivialU, Q_full, sum_wField]
  by_cases hc : c.2 = 2
  · rw [if_pos hc, if_pos hc, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      show (((2 * wEll m : ℕ)) : ℝ) ^ 3 * (1 / (((2 * wEll m : ℕ)) : ℝ) ^ 3) = 1 by field_simp,
      one_smul]
  · rw [if_neg hc, if_neg hc, smul_zero, LinearMap.smul_apply, LinearMap.id_apply, smul_zero,
      neg_zero]

/-- The unique direction-`2` coarse bond at the constraint level. -/
def wCoarseTwo (m : ℕ) : CoarseBond (wExt m) (2 * wEll m) :=
  (⟨fun _ => ⟨0, by have := wExt_four m 0; omega⟩, by
      rw [mem_CoarseLattice]; intro μ; exact Nat.zero_mod _⟩, 2)

/-- The one bond `fullC` writes to. -/
def wDrop (m : ℕ) : Bond (wExt m) := droppedBondLast (2 * wEll m) (wCoarseTwo m)

/-- A coarse bond at the constraint level is `wCoarseTwo` exactly when its direction is `2`. -/
theorem coarse_full_eq {m : ℕ} (c : CoarseBond (wExt m) (2 * wEll m)) (hc : c.2 = 2) :
    c = wCoarseTwo m := by
  refine Prod.ext ?_ hc
  refine Subtype.ext ?_
  funext μ
  apply Fin.ext
  rw [coarse_at_full_val c.1.2 μ]
  rfl

/-- **THE CLOSED FORM OF `fullC` AT THE WITNESS.** A TWO-bond field: the witness spike, and a single
compensating spike of the opposite sign on the one dropped bond of direction `2`. -/
theorem wB_eq (m : ℕ) :
    fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
        (wField (L := wExt m) (wExt_four m))
      = wField (L := wExt m) (wExt_four m)
        - (Pi.single (wDrop m) suTwoWitness : Bond (wExt m) → SuTwo) := by
  classical
  have hell : 0 < 2 * wEll m := wConstr_pos m
  have hell2 : 2 ≤ 2 * wEll m := by have := wEll_pos m; omega
  funext b
  by_cases hd : IsDropped (2 * wEll m) b
  · obtain ⟨c, hc⟩ := hd
    subst hc
    rw [fullC_wField_dropped c, Pi.sub_apply, wField_dropped hell2 (wExt_four m) c,
      Pi.single_apply]
    by_cases hc2 : c.2 = 2
    · rw [if_pos hc2, if_pos, zero_sub]
      rw [wDrop, coarse_full_eq c hc2]
    · rw [if_neg hc2, if_neg, sub_zero]
      intro hcon
      exact hc2 (congrArg (fun c' => c'.2)
        (droppedBondLast_injective hell (wConstr_dvd m) (hcon.trans rfl)))
  · rw [fullC_free _ _ _ hd, Pi.sub_apply, Pi.single_apply, if_neg, sub_zero]
    intro hcon
    exact hd (hcon ▸ isDropped_droppedBondLast (wCoarseTwo m))


/-! ### §5b — the COMPETITOR at the datum -/

/-- Rounding to the block base does not change which half of an axis a coordinate is in. -/
theorem coarseSite_lt_iff {m : ℕ} (z : PeriodicLatticeSite (wExt m)) (j : Fin 3) :
    ((coarseSite (wEll m) z) j).val < wEll m ↔ (z j).val < wEll m := by
  rw [coarseSite_val]
  have hlt := site_lt z j
  have hpos := wEll_pos m
  constructor
  · intro h
    by_contra hcon
    have h1 : 1 ≤ (z j).val / wEll m := (Nat.one_le_div_iff hpos).mpr (by omega)
    have h2 : wEll m ≤ wEll m * ((z j).val / wEll m) := by
      calc wEll m = wEll m * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h1
    omega
  · intro h
    rw [Nat.div_eq_of_lt h]
    omega

/-- The direction-`2` coordinate after a coarse shift by `ell` on a torus of side `2·ell`. -/
theorem pathSite_ell_coord_two {m : ℕ} (z : PeriodicLatticeSite (wExt m)) :
    ((pathSite z 2 (wEll m)) 2).val
      = if (z 2).val < wEll m then (z 2).val + wEll m else (z 2).val - wEll m := by
  have hn : wExt m 2 + 1 = 2 * wEll m := wExt_succ m 2
  have hlt := site_lt z 2
  have hpos := wEll_pos m
  rw [pathSite_apply_self_val]
  by_cases h : (z 2).val < wEll m
  · rw [if_pos h, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The `2`-axis profile of the competitor: `+ell^{-3}·w` on the lower half, `−ell^{-3}·w` on the
upper half. -/
noncomputable def wSval (m : ℕ) (t : ℕ) : SuTwo :=
  if t < wEll m then (1 / (wEll m : ℝ) ^ 3) • suTwoWitness
    else -((1 / (wEll m : ℝ) ^ 3) • suTwoWitness)

theorem wSval_pos (m : ℕ) : (0 : ℝ) < 1 / (wEll m : ℝ) ^ 3 := by
  have h : (0 : ℝ) < (wEll m : ℝ) := by
    have := wEll_pos m; exact_mod_cast this
  positivity

theorem wSval_norm (m : ℕ) (t : ℕ) :
    ‖wSval m t‖ = (1 / (wEll m : ℝ) ^ 3) * ‖suTwoWitness‖ := by
  have hpos := wSval_pos m
  unfold wSval
  split
  · rw [norm_smul]; simp [abs_of_pos hpos]
  · rw [norm_neg, norm_smul]; simp [abs_of_pos hpos]

/-- The `2`-axis profile flips sign under the coarse shift, because the torus has exactly TWO
`ell`-blocks per axis. -/
theorem wSval_shift {m : ℕ} {t : ℕ} (ht : t < 2 * wEll m) :
    wSval m (if t < wEll m then t + wEll m else t - wEll m) = - wSval m t := by
  have hpos := wEll_pos m
  unfold wSval
  by_cases h : t < wEll m
  · rw [if_pos h, if_pos h, if_neg (show ¬ (t + wEll m < wEll m) by omega)]
  · rw [if_neg h, if_neg h, if_pos (show t - wEll m < wEll m by omega), neg_neg]

/-- **THE COMPETITOR.** Direction-`2` only; supported on the transverse block `[0,ell)²`; the
`2`-axis profile `wSval`. Block-constant and coarse-antisymmetric by construction, and spread over
`2ell³` bonds — which is why its `bondEnergy` is `O(ell^{-3})` while it reproduces `Q_ell` of the
two-spike field exactly. -/
noncomputable def wS (m : ℕ) : Bond (wExt m) → SuTwo := fun b =>
  if b.2 = 2 ∧ (b.1 0).val < wEll m ∧ (b.1 1).val < wEll m then wSval m (b.1 2).val else 0

theorem wS_apply (m : ℕ) (z : PeriodicLatticeSite (wExt m)) (ν : Fin 3) :
    wS m (z, ν) = if ν = 2 ∧ (z 0).val < wEll m ∧ (z 1).val < wEll m then
      wSval m (z 2).val else 0 := rfl

theorem wS_blockConst (m : ℕ) : ∀ (z : PeriodicLatticeSite (wExt m)) (ν : Fin 3),
    wS m (z, ν) = wS m (coarseSite (wEll m) z, ν) := by
  intro z ν
  rw [wS_apply, wS_apply]
  refine if_congr ?_ ?_ rfl
  · exact ⟨fun h => ⟨h.1, (coarseSite_lt_iff z 0).mpr h.2.1, (coarseSite_lt_iff z 1).mpr h.2.2⟩,
      fun h => ⟨h.1, (coarseSite_lt_iff z 0).mp h.2.1, (coarseSite_lt_iff z 1).mp h.2.2⟩⟩
  · unfold wSval
    exact if_congr (coarseSite_lt_iff z 2).symm rfl rfl

theorem wS_anti (m : ℕ) : ∀ (z : PeriodicLatticeSite (wExt m)) (ν : Fin 3),
    wS m (pathSite z ν (wEll m), ν) = - wS m (z, ν) := by
  intro z ν
  rw [wS_apply, wS_apply]
  by_cases hν : ν = 2
  · subst hν
    by_cases hc : (z 0).val < wEll m ∧ (z 1).val < wEll m
    · have hcond : ((2 : Fin 3) = 2 ∧ ((pathSite z 2 (wEll m)) 0).val < wEll m
          ∧ ((pathSite z 2 (wEll m)) 1).val < wEll m) := by
        refine ⟨rfl, ?_, ?_⟩
        · rw [pathSite_apply_ne z 2 0 _ (by decide)]; exact hc.1
        · rw [pathSite_apply_ne z 2 1 _ (by decide)]; exact hc.2
      rw [if_pos hcond, if_pos (⟨rfl, hc.1, hc.2⟩ : ((2 : Fin 3) = 2
        ∧ (z 0).val < wEll m ∧ (z 1).val < wEll m)),
        pathSite_ell_coord_two z, wSval_shift (site_lt z 2)]
    · have hn1 : ¬ ((2 : Fin 3) = 2 ∧ ((pathSite z 2 (wEll m)) 0).val < wEll m
          ∧ ((pathSite z 2 (wEll m)) 1).val < wEll m) := by
        intro h
        refine hc ⟨?_, ?_⟩
        · rw [← pathSite_apply_ne z 2 0 (wEll m) (by decide)]; exact h.2.1
        · rw [← pathSite_apply_ne z 2 1 (wEll m) (by decide)]; exact h.2.2
      rw [if_neg hn1, if_neg (fun h => hc ⟨h.2.1, h.2.2⟩), neg_zero]
  · rw [if_neg (fun h => hν h.1), if_neg (fun h => hν h.1), neg_zero]

/-! ### §5c — the two energies -/

theorem card_bond (m : ℕ) : Fintype.card (Bond (wExt m)) = 24 * (wEll m) ^ 3 := by
  have hsite : Fintype.card (PeriodicLatticeSite (wExt m)) = (2 * wEll m) ^ 3 := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Fin.prod_univ_three, wExt_succ, wExt_succ, wExt_succ]
    ring
  show Fintype.card (PeriodicLatticeSite (wExt m) × Fin 3) = _
  rw [Fintype.card_prod, hsite, Fintype.card_fin]
  ring

theorem wS_norm_le {m : ℕ} (b : Bond (wExt m)) :
    ‖wS m b‖ ≤ (1 / (wEll m : ℝ) ^ 3) * ‖suTwoWitness‖ := by
  have hpos := wSval_pos m
  unfold wS
  split
  · rw [wSval_norm]
  · rw [norm_zero]
    positivity

theorem bondEnergy_wS_le (m : ℕ) :
    bondEnergy (wS m) ≤ 24 * (1 / (wEll m : ℝ) ^ 3) * ‖suTwoWitness‖ ^ 2 := by
  have hpos : (0 : ℝ) < (wEll m : ℝ) := by
    have := wEll_pos m; exact_mod_cast this
  have hstep : ∀ b : Bond (wExt m),
      ‖wS m b‖ ^ 2 ≤ ((1 / (wEll m : ℝ) ^ 3) * ‖suTwoWitness‖) ^ 2 := by
    intro b
    have h1 := wS_norm_le b
    have h2 : (0 : ℝ) ≤ ‖wS m b‖ := norm_nonneg _
    nlinarith
  calc bondEnergy (wS m) = ∑ b : Bond (wExt m), ‖wS m b‖ ^ 2 := rfl
    _ ≤ ∑ _b : Bond (wExt m), ((1 / (wEll m : ℝ) ^ 3) * ‖suTwoWitness‖) ^ 2 :=
        Finset.sum_le_sum fun b _ => hstep b
    _ = (Fintype.card (Bond (wExt m)) : ℝ) * ((1 / (wEll m : ℝ) ^ 3) * ‖suTwoWitness‖) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 24 * (1 / (wEll m : ℝ) ^ 3) * ‖suTwoWitness‖ ^ 2 := by
        rw [card_bond]
        push_cast
        field_simp

theorem bondEnergy_wField (m : ℕ) :
    bondEnergy (wField (L := wExt m) (wExt_four m)) = ‖suTwoWitness‖ ^ 2 := by
  classical
  unfold bondEnergy
  rw [Finset.sum_eq_single (wBond (wExt_four m))]
  · rw [wField_apply_self]
  · intro b _ hb
    rw [wField_apply_of_ne (wExt_four m) hb, norm_zero]
    norm_num
  · intro h
    exact absurd (Finset.mem_univ (wBond (wExt_four m))) h


/-! ### §5d — matching `Q_ell` of the two-spike field to the competitor

The one computation left: the coarse average, at the FIBRE level, of the two-bond field `fullC wField`
equals `(1/ell) · wS` at every coarse bond. Both spikes have direction `2`, so
`Q_single_other_dir` disposes of every coarse bond of direction `0` or `1`; the direction-`2` case is
the count of translation steps landing in each of the two `2`-axis blocks. -/

theorem forall_fin_three {P : Fin 3 → Prop} : (∀ ν, P ν) ↔ P 0 ∧ P 1 ∧ P 2 := by
  refine ⟨fun h => ⟨h 0, h 1, h 2⟩, fun h ν => ?_⟩
  fin_cases ν
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- The `2`-coordinate of the BACKWARD translate by `i` steps. -/
theorem back_coord {m : ℕ} (z : PeriodicLatticeSite (wExt m)) {i : ℕ} (hi : i ≤ 2 * wEll m) :
    ((pathSite z 2 (wExt m 2 + 1 - i)) 2).val
      = if i ≤ (z 2).val then (z 2).val - i else (z 2).val + 2 * wEll m - i := by
  have hn : wExt m 2 + 1 = 2 * wEll m := wExt_succ m 2
  have hlt := site_lt z 2
  have hpos := wEll_pos m
  rw [pathSite_apply_self_val]
  by_cases h : i ≤ (z 2).val
  · rw [if_pos h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]
    omega

theorem oneSite_coord {m : ℕ} (ν : Fin 3) :
    ((oneSite (wExt_four m)) ν).val = if ν = 0 then 1 else 0 := by
  unfold oneSite
  by_cases hν : ν = 0 <;> simp [hν]

theorem wDrop_dir (m : ℕ) : (wDrop m).2 = (2 : Fin 3) := rfl

theorem wDrop_coord (m : ℕ) (ν : Fin 3) :
    ((wDrop m).1 ν).val = if ν = 2 then 2 * wEll m - 1 else 0 := by
  have hn : wExt m 2 + 1 = 2 * wEll m := wExt_succ m 2
  have hpos := wEll_pos m
  have hz : ∀ κ : Fin 3, (((wCoarseTwo m).1 : PeriodicLatticeSite (wExt m)) κ).val = 0 :=
    fun κ => rfl
  show ((pathSite ((wCoarseTwo m).1 : PeriodicLatticeSite (wExt m)) 2
      (2 * wEll m - 1)) ν).val = _
  by_cases hν : ν = 2
  · subst hν
    rw [if_pos rfl, pathSite_apply_self_val, hz 2, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg hν, pathSite_apply_ne _ 2 ν _ hν, hz ν]

/-- Block membership of a backward translate, unpacked into pure arithmetic. -/
theorem back_mem_iff {m : ℕ} (z y : PeriodicLatticeSite (wExt m)) {i : ℕ} (hi : i ≤ 2 * wEll m) :
    pathSite z 2 (wExt m 2 + 1 - i) ∈ blockOf y (wEll m)
      ↔ ((y 0).val ≤ (z 0).val ∧ (z 0).val < (y 0).val + wEll m)
        ∧ ((y 1).val ≤ (z 1).val ∧ (z 1).val < (y 1).val + wEll m)
        ∧ ((y 2).val ≤ (if i ≤ (z 2).val then (z 2).val - i else (z 2).val + 2 * wEll m - i)
            ∧ (if i ≤ (z 2).val then (z 2).val - i else (z 2).val + 2 * wEll m - i)
                < (y 2).val + wEll m) := by
  rw [mem_blockOf]
  show (∀ μ : Fin 3, (y μ).val ≤ ((pathSite z 2 (wExt m 2 + 1 - i)) μ).val
      ∧ ((pathSite z 2 (wExt m 2 + 1 - i)) μ).val < (y μ).val + wEll m) ↔ _
  rw [forall_fin_three, pathSite_apply_ne z 2 0 _ (by decide),
    pathSite_apply_ne z 2 1 _ (by decide), back_coord z hi]


/-! ### §5e — the four counts -/

theorem oneSite_c0 {m : ℕ} : ((oneSite (wExt_four m)) 0).val = 1 := by simp [oneSite]
theorem oneSite_c1 {m : ℕ} : ((oneSite (wExt_four m)) 1).val = 0 := by simp [oneSite]
theorem oneSite_c2 {m : ℕ} : ((oneSite (wExt_four m)) 2).val = 0 := by simp [oneSite]
theorem wDrop_c0 (m : ℕ) : ((wDrop m).1 0).val = 0 := by rw [wDrop_coord]; simp
theorem wDrop_c1 (m : ℕ) : ((wDrop m).1 1).val = 0 := by rw [wDrop_coord]; simp
theorem wDrop_c2 (m : ℕ) : ((wDrop m).1 2).val = 2 * wEll m - 1 := by rw [wDrop_coord]; simp

/-- Both spikes have transverse coordinates in `{0,1}`, so a coarse block based at `ell` on a
transverse axis sees neither. -/
theorem filter_empty_transverse {m : ℕ} {y : PeriodicLatticeSite (wExt m)}
    (z : PeriodicLatticeSite (wExt m)) (hz0 : (z 0).val ≤ 1) (hz1 : (z 1).val ≤ 1)
    (hbad : (y 0).val = wEll m ∨ (y 1).val = wEll m) :
    ((Finset.range (wEll m)).filter (fun i =>
      pathSite z 2 (wExt m 2 + 1 - i) ∈ blockOf y (wEll m))).card = 0 := by
  have hpos := wEll_pos m
  have h3 := wEll_three m
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  have hir := Finset.mem_range.mp hi
  rw [back_mem_iff z y (by omega)]
  intro hmem
  rcases hbad with hb | hb
  · have := hmem.1.1; omega
  · have := hmem.2.1.1; omega

theorem card_one_lower {m : ℕ} {y : PeriodicLatticeSite (wExt m)}
    (h0 : (y 0).val = 0) (h1 : (y 1).val = 0) (h2 : (y 2).val = 0) :
    ((Finset.range (wEll m)).filter (fun i =>
      pathSite (oneSite (wExt_four m)) 2 (wExt m 2 + 1 - i)
        ∈ blockOf y (wEll m))).card = 1 := by
  have hpos := wEll_pos m
  have h3 := wEll_three m
  have hset : (Finset.range (wEll m)).filter (fun i =>
      pathSite (oneSite (wExt_four m)) 2 (wExt m 2 + 1 - i) ∈ blockOf y (wEll m)) = {0} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hir, hmem⟩
      rw [back_mem_iff _ y (by omega), oneSite_c0, oneSite_c1, oneSite_c2, h0, h1, h2] at hmem
      split_ifs at hmem <;> omega
    · rintro rfl
      refine ⟨by omega, ?_⟩
      rw [back_mem_iff _ y (by omega), oneSite_c0, oneSite_c1, oneSite_c2, h0, h1, h2]
      split_ifs <;> omega
  rw [hset, Finset.card_singleton]

theorem card_one_upper {m : ℕ} {y : PeriodicLatticeSite (wExt m)}
    (h0 : (y 0).val = 0) (h1 : (y 1).val = 0) (h2 : (y 2).val = wEll m) :
    ((Finset.range (wEll m)).filter (fun i =>
      pathSite (oneSite (wExt_four m)) 2 (wExt m 2 + 1 - i)
        ∈ blockOf y (wEll m))).card = wEll m - 1 := by
  have hpos := wEll_pos m
  have h3 := wEll_three m
  have hset : (Finset.range (wEll m)).filter (fun i =>
      pathSite (oneSite (wExt_four m)) 2 (wExt m 2 + 1 - i) ∈ blockOf y (wEll m))
      = Finset.Ico 1 (wEll m) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hir, hmem⟩
      rw [back_mem_iff _ y (by omega), oneSite_c0, oneSite_c1, oneSite_c2, h0, h1, h2] at hmem
      split_ifs at hmem <;> omega
    · rintro ⟨hi1, hi2⟩
      refine ⟨hi2, ?_⟩
      rw [back_mem_iff _ y (by omega), oneSite_c0, oneSite_c1, oneSite_c2, h0, h1, h2]
      split_ifs <;> omega
  rw [hset, Nat.card_Ico]

theorem card_drop_lower {m : ℕ} {y : PeriodicLatticeSite (wExt m)}
    (h0 : (y 0).val = 0) (h1 : (y 1).val = 0) (h2 : (y 2).val = 0) :
    ((Finset.range (wEll m)).filter (fun i =>
      pathSite ((wDrop m).1) 2 (wExt m 2 + 1 - i) ∈ blockOf y (wEll m))).card = 0 := by
  have hpos := wEll_pos m
  have h3 := wEll_three m
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  have hir := Finset.mem_range.mp hi
  rw [back_mem_iff _ y (by omega), wDrop_c0, wDrop_c1, wDrop_c2, h0, h1, h2]
  intro hmem
  rcases hmem with ⟨-, -, hlo, hhi⟩
  split_ifs at hlo hhi <;> omega

theorem card_drop_upper {m : ℕ} {y : PeriodicLatticeSite (wExt m)}
    (h0 : (y 0).val = 0) (h1 : (y 1).val = 0) (h2 : (y 2).val = wEll m) :
    ((Finset.range (wEll m)).filter (fun i =>
      pathSite ((wDrop m).1) 2 (wExt m 2 + 1 - i) ∈ blockOf y (wEll m))).card = wEll m := by
  have hpos := wEll_pos m
  have h3 := wEll_three m
  have hset : (Finset.range (wEll m)).filter (fun i =>
      pathSite ((wDrop m).1) 2 (wExt m 2 + 1 - i) ∈ blockOf y (wEll m))
      = Finset.range (wEll m) := by
    rw [Finset.filter_eq_self]
    intro i hi
    have hir := Finset.mem_range.mp hi
    rw [back_mem_iff _ y (by omega), wDrop_c0, wDrop_c1, wDrop_c2, h0, h1, h2]
    refine ⟨by omega, by omega, ?_⟩
    split_ifs <;> omega
  rw [hset, Finset.card_range]


/-! ### §5f — THE MATCH, THE BOUND, AND THE CONSEQUENCE FOR THE TARGET -/

theorem Q_single_two {m : ℕ} (c : CoarseBond (wExt m) (wEll m)) (hc : c.2 = 2)
    (z : PeriodicLatticeSite (wExt m)) (v : SuTwo) :
    lineCoarseRestrictCov (trivialU (wExt m)) (wEll m)
        (Pi.single (z, (2 : Fin 3)) v : Bond (wExt m) → SuTwo) c
      = (1 / (wEll m : ℝ) ^ 4) • ((((Finset.range (wEll m)).filter
          (fun i => pathSite z 2 (wExt m 2 + 1 - i) ∈ blockOf c.1.1 (wEll m))).card : ℝ) • v) := by
  have hle : wEll m ≤ wExt m c.2 + 1 := by
    rw [wExt_succ]; have := wEll_pos m; omega
  have h := Q_single_same_dir c hle z v
  rw [hc] at h
  exact h

/-- **THE MATCH.** `Q_ell (fullC wField) = (1/ell) · wS` at every coarse bond of the fibre level. -/
theorem Q_wB_match (m : ℕ) (c : CoarseBond (wExt m) (wEll m)) :
    lineCoarseRestrictCov (trivialU (wExt m)) (wEll m)
        (fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
          (wField (L := wExt m) (wExt_four m))) c
      = (1 / (wEll m : ℝ)) • wS m (c.1.1, c.2) := by
  classical
  have hpos := wEll_pos m
  have h3 := wEll_three m
  have hposR : (0 : ℝ) < (wEll m : ℝ) := by exact_mod_cast hpos
  have hne : (wEll m : ℝ) ≠ 0 := ne_of_gt hposR
  have hsplit : lineCoarseRestrictCov (trivialU (wExt m)) (wEll m)
        (fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
          (wField (L := wExt m) (wExt_four m))) c
      = lineCoarseRestrictCov (trivialU (wExt m)) (wEll m)
          (Pi.single (oneSite (wExt_four m), (2 : Fin 3)) suTwoWitness) c
        - lineCoarseRestrictCov (trivialU (wExt m)) (wEll m)
          (Pi.single ((wDrop m).1, (2 : Fin 3)) suTwoWitness) c := by
    have hmap := (lineCoarseRestrictCovLM (trivialU (wExt m)) (wEll m)).map_sub
      (wField (L := wExt m) (wExt_four m))
      (Pi.single (wDrop m) suTwoWitness : Bond (wExt m) → SuTwo)
    have h := congrFun hmap c
    rw [wB_eq m]
    exact h
  rw [hsplit]
  by_cases hc : c.2 = (2 : Fin 3)
  · rw [Q_single_two c hc, Q_single_two c hc, hc, wS_apply]
    by_cases htr : ((c.1.1 : PeriodicLatticeSite (wExt m)) 0).val < wEll m
        ∧ ((c.1.1 : PeriodicLatticeSite (wExt m)) 1).val < wEll m
    · have e0 : ((c.1.1 : PeriodicLatticeSite (wExt m)) 0).val = 0 := by
        rcases coarse_at_fibre_val c.1.2 0 with h | h
        · exact h
        · exact absurd htr.1 (by omega)
      have e1 : ((c.1.1 : PeriodicLatticeSite (wExt m)) 1).val = 0 := by
        rcases coarse_at_fibre_val c.1.2 1 with h | h
        · exact h
        · exact absurd htr.2 (by omega)
      rw [if_pos ⟨rfl, htr.1, htr.2⟩]
      rcases coarse_at_fibre_val c.1.2 2 with e2 | e2
      · rw [card_one_lower e0 e1 e2, card_drop_lower e0 e1 e2, e2, wSval, if_pos hpos]
        push_cast
        match_scalars
        all_goals (field_simp; try ring)
      · rw [card_one_upper e0 e1 e2, card_drop_upper e0 e1 e2, e2, wSval,
          if_neg (lt_irrefl (wEll m)), Nat.cast_sub hpos]
        push_cast
        match_scalars
        all_goals (field_simp; try ring)
    · have hbad : ((c.1.1 : PeriodicLatticeSite (wExt m)) 0).val = wEll m
          ∨ ((c.1.1 : PeriodicLatticeSite (wExt m)) 1).val = wEll m := by
        rcases coarse_at_fibre_val c.1.2 0 with h0 | h0
        · rcases coarse_at_fibre_val c.1.2 1 with h1 | h1
          · exact absurd ⟨by omega, by omega⟩ htr
          · exact Or.inr h1
        · exact Or.inl h0
      rw [filter_empty_transverse _ (le_of_eq oneSite_c0)
            (oneSite_c1.le.trans (by omega)) hbad,
          filter_empty_transverse _ ((wDrop_c0 m).le.trans (by omega))
            ((wDrop_c1 m).le.trans (by omega)) hbad,
          if_neg (by rintro ⟨-, ha, hb⟩; omega)]
      simp
  · rw [Q_single_other_dir c _ 2 (fun h => hc h.symm),
        Q_single_other_dir c _ 2 (fun h => hc h.symm), sub_zero, wS_apply,
        if_neg (fun h => hc h.1), smul_zero]

/-- **THE EVALUATION — the target's right-hand side at `wField` is `O(ell^{-3})`,
while its left-hand side does not move.** -/
theorem cStar_wField_le (m : ℕ)
    [(deltaKernelImageCovH (trivialU (wExt m))
      (oneLevelUniv (wExt m))).HasOrthogonalProjection]
    [(curlImageCovHFaithful (wEll m) (oneLevelUniv (wExt m))
      (trivialU (wExt m))).HasOrthogonalProjection] :
    cStarDeltaKCFormCorr (wSplit m) (oneLevelUniv (wExt m)) (trivialU (wExt m))
        (dinvC (trivialU (wExt m)) (2 * wEll m)) (wField (L := wExt m) (wExt_four m))
      ≤ 768 * (1 / (wEll m : ℝ) ^ 3)
        * bondEnergy (wField (L := wExt m) (wExt_four m)) := by
  have h1 := deltaJ_le_of_competitor_oneLevel (wEll_pos m) (wEll_dvd m)
    (fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
      (wField (L := wExt m) (wExt_four m))) (wS m) (wS_blockConst m) (wS_anti m) (Q_wB_match m)
  have h2 := bondEnergy_wS_le m
  rw [bondEnergy_wField]
  have hform : cStarDeltaKCFormCorr (wSplit m) (oneLevelUniv (wExt m)) (trivialU (wExt m))
      (dinvC (trivialU (wExt m)) (2 * wEll m)) (wField (L := wExt m) (wExt_four m))
      = deltaJQuadFormCovFaithful (wEll m) (oneLevelUniv (wExt m)) (trivialU (wExt m))
        (fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
          (wField (L := wExt m) (wExt_four m))) := rfl
  rw [hform]
  nlinarith [h1, h2]

/-- **THE TARGET'S INEQUALITY IS FALSE AT `wField` for every `γ₀` above `768/ell³`.** -/
theorem target_inequality_fails (m : ℕ) (γ₀ : ℝ)
    (hm : 768 * (1 / (wEll m : ℝ) ^ 3) < γ₀)
    [(deltaKernelImageCovH (trivialU (wExt m))
      (oneLevelUniv (wExt m))).HasOrthogonalProjection]
    [(curlImageCovHFaithful (wEll m) (oneLevelUniv (wExt m))
      (trivialU (wExt m))).HasOrthogonalProjection] :
    ¬ (γ₀ * bondEnergy (wField (L := wExt m) (wExt_four m))
        ≤ cStarDeltaKCFormCorr (wSplit m) (oneLevelUniv (wExt m)) (trivialU (wExt m))
            (dinvC (trivialU (wExt m)) (2 * wEll m)) (wField (L := wExt m) (wExt_four m))) := by
  intro hcon
  have h1 := cStar_wField_le m
  have hE : 0 < bondEnergy (wField (L := wExt m) (wExt_four m)) :=
    wField_bondEnergy_pos (wExt_four m)
  nlinarith

/-- The Archimedean step, stated as a `∀`-form so that NO declaration in this module concludes with
an `∃` (S91: an `∃`-concluding declaration hands the prover free data, and this one has none to give
— the witness is CONSTRUCTED from `γ₀`). `wEll N = N + 3`, so `768/γ₀ < N` already forces
`768 < γ₀ · (wEll N)³`. -/
theorem small_at (γ₀ : ℝ) (hγ : 0 < γ₀) (N : ℕ) (hN : 768 / γ₀ < (N : ℝ)) :
    768 * (1 / (wEll N : ℝ) ^ 3) < γ₀ := by
  have h3 : (3 : ℝ) ≤ ((wEll N : ℕ) : ℝ) := by
    have : 3 ≤ wEll N := wEll_three N
    exact_mod_cast this
  have hNle : (N : ℝ) ≤ ((wEll N : ℕ) : ℝ) := by
    have : N ≤ wEll N := by simp only [wEll]; omega
    exact_mod_cast this
  have hmul : (768 : ℝ) < γ₀ * (N : ℝ) := by
    have := (div_lt_iff₀ hγ).mp hN
    linarith
  have hcube : ((wEll N : ℕ) : ℝ) ≤ ((wEll N : ℕ) : ℝ) ^ 3 := by
    have hx : (0 : ℝ) ≤ ((wEll N : ℕ) : ℝ) := by linarith
    have hx1 : (0 : ℝ) ≤ ((wEll N : ℕ) : ℝ) - 1 := by linarith
    have hx2 : (0 : ℝ) ≤ ((wEll N : ℕ) : ℝ) + 1 := by linarith
    nlinarith [mul_nonneg (mul_nonneg hx hx1) hx2]
  rw [mul_one_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- **THE TARGET IS REFUTED.** `LevelCorrectedCoercivityTargetUniform` asserts a SINGLE `γ₀`,
quantified before `L` and `S`. At `wField` the left-hand side `γ₀ · bondEnergy wField` is a fixed
positive multiple of `‖suTwoWitness‖²`, independent of everything the `∀` ranges over, while the
right-hand side is `O(S.fibre^{-3})`. So no `γ₀` works. -/
theorem target_refuted : ¬ ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform := by
  rintro ⟨γ₀, α₀, hγ, hα, hT⟩
  obtain ⟨m, hmN⟩ := exists_nat_gt (768 / γ₀)
  have hm : 768 * (1 / (wEll m : ℝ) ^ 3) < γ₀ := small_at γ₀ hγ m hmN
  have hfrob : frobSupBond (trivialU (wExt m)) ≤ α₀ := by
    rw [RegularUDomainWitness.frobSupBond_trivialU]
    exact le_of_lt hα
  have hfib : 2 ≤ (wSplit m).fibre := by
    show 2 ≤ wEll m
    have := wEll_three m; omega
  have hcell : 2 ≤ 2 * wEll m := by have := wEll_pos m; omega
  have hineq := hT (wExt m) (wSplit m) hfib (wExt_four m) (wEll_dvd m) (wConstr_dvd m)
    (oneLevelUniv (wExt m)) (trivialU (wExt m)) hfrob
    (dinvC (trivialU (wExt m)) (2 * wEll m))
    (dinvC_hinv (wConstr_pos m) (wConstr_dvd m) (trivialU (wExt m)))
    (wField (L := wExt m) (wExt_four m))
    (wField_axial hcell (wExt_four m)) (wField_dropped hcell (wExt_four m))
  exact target_inequality_fails m γ₀ hm hineq


/-! ### §5g — NON-DEGENERATE, BUT NOT COERCIVE

The refutation above bounds the target's right-hand side from ABOVE. It would be a strictly weaker
finding if that right-hand side were simply ZERO at the datum (the failure mode
`CStarDeltaKCCoercive.cStarDeltaKC_coercivity_refuted` exhibits for the COLLAPSED encoding). It is
not: the Schur complement is strictly POSITIVE here. So the datum shows the target's domain is
inhabited (`LevelTargetWitness.target_domain_nonempty`), the form is non-degenerate on it, and the
inequality still fails — a RATE failure, not a vanishing. -/

/-- The origin, as a site of the datum's torus. -/
def zeroSiteW (m : ℕ) : PeriodicLatticeSite (wExt m) :=
  fun μ => ⟨0, by have := wExt_four m μ; omega⟩

theorem zeroSiteW_val (m : ℕ) (μ : Fin 3) : ((zeroSiteW m) μ).val = 0 := rfl

theorem zeroSiteW_coarse (m : ℕ) : zeroSiteW m ∈ CoarseLattice (wExt m) (wEll m) := by
  rw [mem_CoarseLattice]
  intro μ
  rw [zeroSiteW_val]
  exact Nat.zero_mod _

theorem coarseShift_zero_coord (m : ℕ) (μ : Fin 3) :
    ((coarseShift (zeroSiteW m) (wEll m) μ) μ).val = wEll m := by
  have hpos := wEll_pos m
  show ((pathSite (zeroSiteW m) μ (wEll m)) μ).val = wEll m
  rw [pathSite_apply_self_val, zeroSiteW_val, Nat.mod_eq_of_lt (by rw [wExt_succ]; omega)]
  omega

/-- **THE SCHUR COMPLEMENT IS STRICTLY POSITIVE AT THE DATUM.** Via
`CStarLevelCorrected.deltaJQuadFormCovFaithful_pos_of_factoring_witness` and the flat Stokes
factoring pair `ThirdLevelStokes.stokes_factoring` — both already in the tree (LAW-19). -/
theorem cStar_wField_pos (m : ℕ)
    [(deltaKernelImageCovH (trivialU (wExt m))
      (oneLevelUniv (wExt m))).HasOrthogonalProjection]
    [(curlImageCovHFaithful (wEll m) (oneLevelUniv (wExt m))
      (trivialU (wExt m))).HasOrthogonalProjection] :
    0 < cStarDeltaKCFormCorr (wSplit m) (oneLevelUniv (wExt m)) (trivialU (wExt m))
        (dinvC (trivialU (wExt m)) (2 * wEll m)) (wField (L := wExt m) (wExt_four m)) := by
  have hpos := wEll_pos m
  have h3 := wEll_three m
  have hposR : (0 : ℝ) < (wEll m : ℝ) := by exact_mod_cast hpos
  have hnz : (wEll m : ℝ) ≠ 0 := ne_of_gt hposR
  have hy := zeroSiteW_coarse m
  have hlt : (0 : Fin 3) < 2 := by decide
  have hqfun : lineCoarseRestrictCovLM (trivialU (wExt m)) (wEll m)
      (fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
        (wField (L := wExt m) (wExt_four m)))
      = fun c => (1 / (wEll m : ℝ)) • wS m (c.1.1, c.2) := by
    funext c
    exact Q_wB_match m c
  have hcurl : coarseCurlSuTwo (wEll_dvd m)
      (lineCoarseRestrictCovLM (trivialU (wExt m)) (wEll m)
        (fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
          (wField (L := wExt m) (wExt_four m))))
      ((⟨zeroSiteW m, hy⟩, ⟨(0, 2), hlt⟩) : CoarsePlaquette (wExt m) (wEll m))
      = (-(1 / (wEll m : ℝ) ^ 4)) • suTwoWitness := by
    unfold coarseCurlSuTwo
    rw [hqfun]
    simp only []
    rw [wS_apply, wS_apply, wS_apply, wS_apply,
      if_neg (by rintro ⟨h, -, -⟩; exact absurd h (by decide)),
      if_neg (by
        rintro ⟨-, h, -⟩
        rw [coarseShift_zero_coord] at h
        omega),
      if_neg (by rintro ⟨h, -, -⟩; exact absurd h (by decide)),
      if_pos ⟨rfl, by rw [zeroSiteW_val]; omega, by rw [zeroSiteW_val]; omega⟩]
    rw [zeroSiteW_val, wSval, if_pos hpos]
    match_scalars
    all_goals (field_simp; try ring)
  have hne : stokesPhi (wEll m) (wEll_dvd m) hy hlt suTwoWitness
      (lineCoarseRestrictCovLM (trivialU (wExt m)) (wEll m)
        (fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
          (wField (L := wExt m) (wExt_four m)))) ≠ 0 := by
    rw [stokesPhi_apply, hcurl, hsInner_smul_right]
    intro hcon
    have hw : hsInner suTwoWitness suTwoWitness ≠ 0 := fun h =>
      suTwoWitness_ne_zero (hsInner_self_eq_zero h)
    have hfac : (wEll m : ℝ) ^ 4 * (-(1 / (wEll m : ℝ) ^ 4)) = -1 := by field_simp
    rw [← mul_assoc, hfac] at hcon
    exact hw (by linarith [hcon])
  show 0 < deltaJQuadFormCovFaithful (wEll m) (oneLevelUniv (wExt m)) (trivialU (wExt m))
    (fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
      (wField (L := wExt m) (wExt_four m)))
  exact CStarLevelCorrected.deltaJQuadFormCovFaithful_pos_of_factoring_witness (wEll m)
    (oneLevelUniv (wExt m)) (trivialU (wExt m)) _ (stokesU (wEll m) (zeroSiteW m) hlt suTwoWitness)
    (stokesPhi (wEll m) (wEll_dvd m) hy hlt suTwoWitness)
    (fun v => stokes_factoring hpos (wEll_dvd m) hy hlt suTwoWitness v) hne

#print axioms cStar_wField_pos

#print axioms deltaJQuadFormCovFaithful_le_of_sub
#print axioms plaqEnergy_flatCurl_le
#print axioms dstarDQuadForm_trivialU_le
#print axioms coarseSite_pathSite
#print axioms two_mul_sum_coord
#print axioms Q_of_blockConst_anti
#print axioms deltaJ_le_of_competitor
#print axioms deltaJ_le_of_competitor_oneLevel
#print axioms Q_single_same_dir
#print axioms Q_single_other_dir
#print axioms fullC_wField_dropped
#print axioms wB_eq
#print axioms wS_blockConst
#print axioms wS_anti
#print axioms bondEnergy_wS_le
#print axioms bondEnergy_wField
#print axioms card_one_lower
#print axioms card_one_upper
#print axioms card_drop_lower
#print axioms card_drop_upper
#print axioms Q_wB_match
#print axioms cStar_wField_le
#print axioms target_inequality_fails
#print axioms small_at
#print axioms target_refuted

end AdalyFormal.Balaban.WitnessInequality
