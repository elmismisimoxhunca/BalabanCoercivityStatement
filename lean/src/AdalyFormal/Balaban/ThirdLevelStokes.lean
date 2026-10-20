/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CStarLevelCorrected
import AdalyFormal.Balaban.CovU1Reduction

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `ThirdLevelStokes.lean` — `[STOKES-COMM]` CLOSED at `U = 1`: the flat Stokes identity
`∂₁' ∘ Q_ℓ = P_ℓ ∘ d`, and the §3c factoring pair it supplies

## What this module is

`CStarLevelCorrected` §6 names ONE residual standing between the level-split re-typing and a
non-degeneracy witness at a genuinely non-trivial fibre level `ℓ₀ ≥ 2`: **`[STOKES-COMM]`**, the
identity "the coarse curl of a block-averaged line integral is a block average of fine curls",

  `(∂₁'(Q_ℓ v))(y, μ, ν) = (1/ℓ⁴) Σ_{x ∈ B(y)} Σ_{i<ℓ} Σ_{j<ℓ} (dv)(x + i e_μ + j e_ν, μ, ν)`,

together with the derived §3c factoring pair `(u, φ)` making `⟪u, D_U ·⟫` factor through `Q_ℓ`
(Bałaban's `D_U^* u ∈ range Q^*`). This module PROVES both, at `U = 1` (`trivialU`), for EVERY
block side `ℓ > 0`, every compatible torus (`∀ μ, ℓ ∣ L μ + 1`), every coarse site and every
ordered direction pair — general, not witness-bound.

* §1 shift/path commutation (`pathSite_comm`) — the only geometry the telescoping needs.
* §2 the per-site double telescoping (`window_curl_sum`): the `ℓ × ℓ` window of fine curls
  telescopes to the four line integrals around the coarse plaquette. This is CMP96 p.244's own
  derivation mechanism for the `Σ_p |(∂₁B)(p)|²` term of (2.128), executed on the `SuTwo` carrier.
* §3 the coarse curl on `SuTwo`-valued coarse bond fields (`coarseCurlSuTwo`), mirroring
  `CoarseCurl.coarseCurlValue` (ℝ-valued) — LAW-19: same four-term shape, same `hdvd`-supplied
  membership proofs, only the codomain changes.
* §4 **THE FLAT STOKES IDENTITY** (`stokes_flat`): summed over the block, the window of fine curls
  equals `ℓ⁴ • ∂₁'(Q_ℓ v)` at the coarse plaquette, with `Q_ℓ = lineCoarseRestrictCovLM (trivialU)`
  the FAITHFUL line-integral averaging (grade-2 source-pinned in `LineIntegralCovariant`).
* §5 **THE FACTORING PAIR** (`stokesU`, `stokesPhi`, `stokes_factoring`): the §3c obligation of
  `CStarLevelCorrected.deltaJQuadFormCovFaithful_pos_of_factoring_witness`, discharged — for every
  `v`, `⟪stokesU, D_{U=1} v⟫ = stokesPhi (Q_ℓ v)`. No analysis, no constants: the identity is exact.
* §6 **THE QUANTITATIVE DUALITY BOUND** (`deltaJ_ge_dual_pairing_sq`): for ANY `U`, ANY `u`
  annihilating `D_U(V)`, the Schur complement obeys
  `⟪u, D_U B⟫² / ⟪u, u⟫ ≤ Δ_k(B)` — Cauchy–Schwarz against the projection residue. This upgrades
  §3/§3c of `CStarLevelCorrected` from strict positivity to an EXPLICIT lower bound, which is the
  transfer mechanism that replaces the wrong-way `[CSTAR-SCHUR-GAP]` ordering (see
  `ThirdLevelSchurGap.lean`).
* §7 falsifiability controls: the window sum is NOT a tautology (a mismatched window fails), and
  the factoring identity genuinely uses the line integral.

## HONEST SCOPE

* **`U = 1` ONLY for §4/§5.** For `U ≠ 1` the transport does not cancel around the loop; the exact
  identity acquires a curvature defect, and `CovariantOperators.witness_curvature_ne_zero` proves
  that defect is genuinely nonzero on an explicit non-flat background. The general-`U` statement is
  the identity up to an `O(α₁)` remainder (Bałaban's "localizing the operators in `Δ_k`", CMP99b
  p.428) — stated as the named residual `[STOKES-COMM-U]` in `ThirdLevelSchurGap.lean` §4, with the
  obstruction cite. §6's quantitative bound, by contrast, holds for EVERY `U`.
* Everything is on the compatible torus (`0 < ℓ`, `∀ μ, ℓ ∣ L μ + 1`) — the standing scope of the
  faithful `Q` (`blockOf` truncates otherwise; MEMORY: torus-blockOf-truncation-artifact).
* `#print axioms` on every declaration: expected `{propext, Classical.choice, Quot.sound}`.
-/

namespace AdalyFormal.Balaban.ThirdLevelStokes

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU deltaKernelImageCovH PlaqFnL2 plaqFnEquiv
  inner_plaqFnL2_eq_covPlaqInner covPlaqInner_add_right covPlaqInner_sub_right)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice CoarsePlaquette)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_blockOf_eq_image coarseShift_injective)
open AdalyFormal.Balaban.CovU1Reduction (curlValueCovariant_trivialU_local flatCurlValue)
open AdalyFormal.Balaban.Q1Real (rZeroA_trivialU)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — `hsInner` right-slot conveniences (derived, not re-axiomatized) -/

theorem hsInner_zero_right (X : SuTwo) : hsInner X (0 : SuTwo) = 0 := by
  rw [← inner_eq_hsInner]
  exact inner_zero_right X

theorem hsInner_add_right (X Y Z : SuTwo) : hsInner X (Y + Z) = hsInner X Y + hsInner X Z := by
  rw [hsInner_symm, hsInner_add_left, hsInner_symm Y X, hsInner_symm Z X]

theorem hsInner_sub_right (X Y Z : SuTwo) : hsInner X (Y - Z) = hsInner X Y - hsInner X Z := by
  have h := hsInner_add_right X (Y - Z) Z
  rw [sub_add_cancel] at h
  linarith

theorem hsInner_smul_right (X Y : SuTwo) (r : ℝ) : hsInner X (r • Y) = r * hsInner X Y := by
  rw [hsInner_symm, hsInner_smul_left, hsInner_symm]

theorem hsInner_sum_right {ι : Type*} (s : Finset ι) (f : ι → SuTwo) (X : SuTwo) :
    hsInner X (∑ i ∈ s, f i) = ∑ i ∈ s, hsInner X (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hsInner_zero_right]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hsInner_add_right, ih]

#print axioms hsInner_zero_right
#print axioms hsInner_sum_right

/-! ## §1 — shift/path commutation -/

/-- Two single fine shifts in DIFFERENT directions commute (`Function.update` in distinct
coordinates). -/
theorem periodicLatticeShift_comm (x : PeriodicLatticeSite L) {μ ν : Fin 3} (h : μ ≠ ν) :
    periodicLatticeShift (periodicLatticeShift x μ) ν
      = periodicLatticeShift (periodicLatticeShift x ν) μ := by
  unfold periodicLatticeShift
  rw [Function.update_of_ne h.symm, Function.update_of_ne h, Function.update_comm h]

/-- A path in direction `σ` commutes with one leading shift in a different direction `ρ`. -/
theorem pathSite_shift_comm (x : PeriodicLatticeSite L) {ρ σ : Fin 3} (h : ρ ≠ σ) (i : ℕ) :
    pathSite (periodicLatticeShift x ρ) σ i = periodicLatticeShift (pathSite x σ i) ρ := by
  induction i with
  | zero => rw [pathSite_zero, pathSite_zero]
  | succ n ih =>
    rw [pathSite_succ, pathSite_succ, ih, periodicLatticeShift_comm _ h.symm]

/-- **Paths in different directions commute.** The only geometric input of the double
telescoping. -/
theorem pathSite_comm (x : PeriodicLatticeSite L) {μ ν : Fin 3} (h : μ ≠ ν) (i j : ℕ) :
    pathSite (pathSite x μ i) ν j = pathSite (pathSite x ν j) μ i := by
  induction j with
  | zero => rw [pathSite_zero, pathSite_zero]
  | succ n ih =>
    rw [pathSite_succ, ih, pathSite_succ, ← pathSite_shift_comm _ h.symm]

/-- `pathSite x ν ℓ` and `coarseShift x ℓ ν` are the SAME iterate — definitional. -/
theorem pathSite_eq_coarseShift (x : PeriodicLatticeSite L) (ν : Fin 3) (ell : ℕ) :
    pathSite x ν ell = coarseShift x ell ν := rfl

#print axioms periodicLatticeShift_comm
#print axioms pathSite_comm
#print axioms pathSite_eq_coarseShift

/-! ## §2 — the per-site double telescoping -/

/-- The length-`ℓ` line integral of `v` in direction `μ` from `x` (the flat `rZeroA`). -/
noncomputable def lineSum (ell : ℕ) (v : Bond L → SuTwo) (x : PeriodicLatticeSite L)
    (μ : Fin 3) : SuTwo :=
  ∑ i ∈ Finset.range ell, v (pathSite x μ i, μ)

/-- **The `ℓ × ℓ` window of flat curls telescopes to the four line integrals around the
`ℓ × ℓ` loop at `x`** — CMP96 p.244's mechanism, exact on the torus (no boundary terms: the
telescoping is internal to the window). -/
theorem window_curl_sum (ell : ℕ) (v : Bond L → SuTwo) (x : PeriodicLatticeSite L)
    {μ ν : Fin 3} (hlt : μ < ν) :
    ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
        curlValueCovariant (trivialU L) v
          (pathSite (pathSite x μ i) ν j, ⟨(μ, ν), hlt⟩)
      = lineSum ell v x μ - lineSum ell v (coarseShift x ell ν) μ
        + (lineSum ell v (coarseShift x ell μ) ν - lineSum ell v x ν) := by
  have hne : μ ≠ ν := ne_of_lt hlt
  -- rewrite every curl as its flat four-term value
  have hsplit : ∀ i ∈ Finset.range ell, ∀ j ∈ Finset.range ell,
      curlValueCovariant (trivialU L) v (pathSite (pathSite x μ i) ν j, ⟨(μ, ν), hlt⟩)
        = (v (pathSite (pathSite x μ i) ν j, μ)
            - v (pathSite (pathSite x μ i) ν (j + 1), μ))
          + (v (pathSite (pathSite x ν j) μ (i + 1), ν)
            - v (pathSite (pathSite x ν j) μ i, ν)) := by
    intro i _ j _
    rw [curlValueCovariant_trivialU_local]
    show v (pathSite (pathSite x μ i) ν j, μ)
        + v (periodicLatticeShift (pathSite (pathSite x μ i) ν j) μ, ν)
        - v (periodicLatticeShift (pathSite (pathSite x μ i) ν j) ν, μ)
        - v (pathSite (pathSite x μ i) ν j, ν) = _
    rw [← pathSite_succ (pathSite x μ i) ν j]
    have h1 : periodicLatticeShift (pathSite (pathSite x μ i) ν j) μ
        = pathSite (pathSite x ν j) μ (i + 1) := by
      rw [pathSite_comm x hne i j, pathSite_succ]
    have h2 : pathSite (pathSite x μ i) ν j = pathSite (pathSite x ν j) μ i :=
      pathSite_comm x hne i j
    rw [h1, ← h2]
    abel
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => hsplit i hi j hj))]
  have hdistrib : ∀ i ∈ Finset.range ell,
      (∑ j ∈ Finset.range ell,
        ((v (pathSite (pathSite x μ i) ν j, μ) - v (pathSite (pathSite x μ i) ν (j + 1), μ))
          + (v (pathSite (pathSite x ν j) μ (i + 1), ν)
              - v (pathSite (pathSite x ν j) μ i, ν))))
      = (v (pathSite x μ i, μ) - v (pathSite (pathSite x ν ell) μ i, μ))
        + ∑ j ∈ Finset.range ell,
            (v (pathSite (pathSite x ν j) μ (i + 1), ν)
              - v (pathSite (pathSite x ν j) μ i, ν)) := by
    intro i _
    rw [Finset.sum_add_distrib]
    congr 1
    -- telescoping in `j`
    rw [Finset.sum_range_sub' (fun j => v (pathSite (pathSite x μ i) ν j, μ)) ell]
    rw [pathSite_zero, pathSite_comm x hne i ell]
  rw [Finset.sum_congr rfl hdistrib, Finset.sum_add_distrib]
  congr 1
  · -- the μ-terms: `Σ_i (v(x+ie_μ,μ) − v(x+ℓe_ν+ie_μ,μ))`
    rw [Finset.sum_sub_distrib]
    rw [← pathSite_eq_coarseShift]
    rfl
  · -- the ν-terms: swap the sums and telescope in `i`
    rw [Finset.sum_comm]
    have htel : ∀ j ∈ Finset.range ell,
        (∑ i ∈ Finset.range ell,
          (v (pathSite (pathSite x ν j) μ (i + 1), ν) - v (pathSite (pathSite x ν j) μ i, ν)))
        = v (pathSite (pathSite x μ ell) ν j, ν) - v (pathSite x ν j, ν) := by
      intro j _
      rw [Finset.sum_range_sub (fun i => v (pathSite (pathSite x ν j) μ i, ν)) ell]
      rw [pathSite_zero, pathSite_comm x hne ell j]
    rw [Finset.sum_congr rfl htel, Finset.sum_sub_distrib]
    rw [← pathSite_eq_coarseShift]
    rfl

#print axioms window_curl_sum

/-! ## §3 — the coarse curl on `SuTwo`-valued coarse bond fields -/

/-- **`(∂₁'B)(p)` on the `SuTwo` carrier** — the four-term coarse curl, mirroring
`CoarseCurl.coarseCurlValue` (ℝ-valued, same shape, same `hdvd`-membership mechanism; LAW-19). -/
noncomputable def coarseCurlSuTwo {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) : SuTwo :=
  B (p.1, p.2.1.1)
    + B (⟨coarseShift p.1.1 ell p.2.1.1,
        coarseShift_mem_coarseLattice hdvd p.1.2 p.2.1.1⟩, p.2.1.2)
    - B (⟨coarseShift p.1.1 ell p.2.1.2,
        coarseShift_mem_coarseLattice hdvd p.1.2 p.2.1.2⟩, p.2.1.1)
    - B (p.1, p.2.1.2)

theorem coarseCurlSuTwo_add {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B1 B2 : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) :
    coarseCurlSuTwo hdvd (B1 + B2) p = coarseCurlSuTwo hdvd B1 p + coarseCurlSuTwo hdvd B2 p := by
  simp only [coarseCurlSuTwo, Pi.add_apply]
  abel

theorem coarseCurlSuTwo_smul {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (c : ℝ) (B : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) :
    coarseCurlSuTwo hdvd (c • B) p = c • coarseCurlSuTwo hdvd B p := by
  simp only [coarseCurlSuTwo, Pi.smul_apply, smul_add, smul_sub]

#print axioms coarseCurlSuTwo_add
#print axioms coarseCurlSuTwo_smul

/-! ## §4 — THE FLAT STOKES IDENTITY -/

/-- Unfold the faithful `Q` at `U = 1` to block-summed line integrals: `ℓ⁴ • (Q_ℓ v)(z, ρ) =
Σ_{x ∈ B(z)} lineSum`. -/
theorem ell4_smul_lineCoarseRestrict (ell : ℕ) (hell : 0 < ell) (v : Bond L → SuTwo)
    (b : CoarseBond L ell) :
    ((ell : ℝ) ^ 4) • lineCoarseRestrictCovLM (trivialU L) ell v b
      = ∑ x ∈ blockOf b.1.1 ell, lineSum ell v x b.2 := by
  rw [lineCoarseRestrictCovLM_apply]
  unfold lineCoarseRestrictCov
  rw [smul_smul]
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hne : ((ell : ℝ)) ^ 4 ≠ 0 := by positivity
  rw [mul_one_div, div_self hne, one_smul]
  exact Finset.sum_congr rfl fun x _ => rZeroA_trivialU b.1.1 x v b.2 ell

/-- **THE FLAT STOKES IDENTITY** (`[STOKES-COMM]` at `U = 1`, general): summed over the block, the
`ℓ × ℓ` window of fine curls IS `ℓ⁴` times the coarse curl of the faithful line-integral average.
`∂₁' ∘ Q_ℓ = P_ℓ ∘ d`, exactly, with no remainder. -/
theorem stokes_flat {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) {μ ν : Fin 3} (hlt : μ < ν)
    (v : Bond L → SuTwo) :
    ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
        curlValueCovariant (trivialU L) v (pathSite (pathSite x μ i) ν j, ⟨(μ, ν), hlt⟩)
      = ((ell : ℝ) ^ 4) •
          coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell v)
            ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : CoarsePlaquette L ell) := by
  -- LHS: per-site telescoping, then block reindexing of the two shifted terms
  rw [Finset.sum_congr rfl (fun x _ => window_curl_sum ell v x hlt)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hreμ : ∑ x ∈ blockOf y ell, lineSum ell v (coarseShift x ell μ) ν
      = ∑ x' ∈ blockOf (coarseShift y ell μ) ell, lineSum ell v x' ν := by
    rw [coarseShift_blockOf_eq_image hell (hdvd μ) hy]
    rw [Finset.sum_image (fun a _ b _ h => coarseShift_injective ell μ h)]
  have hreν : ∑ x ∈ blockOf y ell, lineSum ell v (coarseShift x ell ν) μ
      = ∑ x' ∈ blockOf (coarseShift y ell ν) ell, lineSum ell v x' μ := by
    rw [coarseShift_blockOf_eq_image hell (hdvd ν) hy]
    rw [Finset.sum_image (fun a _ b _ h => coarseShift_injective ell ν h)]
  rw [hreμ, hreν]
  -- RHS: unfold the coarse curl and clear the `ℓ⁴` normalization
  unfold coarseCurlSuTwo
  rw [smul_sub, smul_sub, smul_add]
  rw [ell4_smul_lineCoarseRestrict ell hell, ell4_smul_lineCoarseRestrict ell hell,
    ell4_smul_lineCoarseRestrict ell hell, ell4_smul_lineCoarseRestrict ell hell]
  abel

#print axioms stokes_flat

/-! ## §5 — the §3c factoring pair `(u, φ)` -/

/-- The window index set: block sites × the `ℓ × ℓ` offsets. -/
def windowSet (ell : ℕ) (y : PeriodicLatticeSite L) : Finset (PeriodicLatticeSite L × ℕ × ℕ) :=
  (blockOf y ell) ×ˢ (Finset.range ell ×ˢ Finset.range ell)

/-- The fine plaquette a window index points at. -/
def windowPlaq {μ ν : Fin 3} (hlt : μ < ν)
    (t : PeriodicLatticeSite L × ℕ × ℕ) : PeriodicLatticePlaquette L :=
  (pathSite (pathSite t.1 μ t.2.1) ν t.2.2, ⟨(μ, ν), hlt⟩)

/-- **`u = P_ℓ^* δ_{P'}` — the block-average adjoint of a coarse plaquette delta, in the `w`
direction**: the plaquette field whose value at `p` is (multiplicity of `p` in the window) `• w`.
This is the dual witness the §3c criterion consumes. -/
noncomputable def stokesU (ell : ℕ) (y : PeriodicLatticeSite L) {μ ν : Fin 3} (hlt : μ < ν)
    (w : SuTwo) : PeriodicLatticePlaquette L → SuTwo :=
  fun p => ((((windowSet ell y).filter (fun t => windowPlaq hlt t = p)).card : ℝ)) • w

/-- **`φ = ℓ⁴ ⟪δ_{P'} ∘ ∂₁', ·⟫` — the coarse-curl evaluation functional**, as a genuine
`LinearMap`. -/
noncomputable def stokesPhi (ell : ℕ) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) {μ ν : Fin 3} (hlt : μ < ν)
    (w : SuTwo) : (CoarseBond L ell → SuTwo) →ₗ[ℝ] ℝ where
  toFun B := ((ell : ℝ) ^ 4) *
    hsInner w (coarseCurlSuTwo hdvd B ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : CoarsePlaquette L ell))
  map_add' B1 B2 := by
    rw [coarseCurlSuTwo_add, hsInner_add_right]
    ring
  map_smul' c B := by
    rw [coarseCurlSuTwo_smul, hsInner_smul_right, RingHom.id_apply, smul_eq_mul]
    ring

theorem stokesPhi_apply (ell : ℕ) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) {μ ν : Fin 3} (hlt : μ < ν)
    (w : SuTwo) (B : CoarseBond L ell → SuTwo) :
    stokesPhi ell hdvd hy hlt w B = ((ell : ℝ) ^ 4) *
      hsInner w (coarseCurlSuTwo hdvd B ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : CoarsePlaquette L ell)) := rfl

/-- The pairing of `stokesU` against ANY plaquette field is the window sum of pointwise pairings —
the multiplicity weights re-expand into the raw index sum (`Finset.sum_comp` fiber counting). -/
theorem covPlaqInner_stokesU (ell : ℕ) (y : PeriodicLatticeSite L) {μ ν : Fin 3} (hlt : μ < ν)
    (w : SuTwo) (X : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner (stokesU ell y hlt w) X
      = ∑ t ∈ windowSet ell y, hsInner w (X (windowPlaq hlt t)) := by
  classical
  unfold covPlaqInner stokesU
  have hterm : ∀ p : PeriodicLatticePlaquette L,
      hsInner (((((windowSet ell y).filter (fun t => windowPlaq hlt t = p)).card : ℝ)) • w)
          (X p)
        = (((windowSet ell y).filter (fun t => windowPlaq hlt t = p)).card : ℝ)
            * hsInner w (X p) := fun p => hsInner_smul_left w (X p) _
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  -- fiber-count the window sum
  have hcomp := Finset.sum_comp (s := windowSet ell y)
    (fun p : PeriodicLatticePlaquette L => hsInner w (X p)) (windowPlaq hlt)
  rw [hcomp]
  -- extend the image sum to the full plaquette universe (off-image fibers are empty)
  rw [Finset.sum_subset (Finset.subset_univ ((windowSet ell y).image (windowPlaq hlt)))]
  · exact Finset.sum_congr rfl (fun p _ => by rw [nsmul_eq_mul])
  · intro p _ hp
    have hempty : ((windowSet ell y).filter (fun t => windowPlaq hlt t = p)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t ht heq
      exact hp (Finset.mem_image.mpr ⟨t, ht, heq⟩)
    rw [hempty]
    simp

/-- **THE FACTORING IDENTITY — the §3c obligation, DISCHARGED at `U = 1`.** For every fine field
`v`, `⟪u, D_{U=1} v⟫ = φ (Q_ℓ v)`: the functional `⟪stokesU, D_U ·⟫` factors through the faithful
`Q_ℓ`. This is exactly the hypothesis `hfac` of
`CStarLevelCorrected.deltaJQuadFormCovFaithful_pos_of_factoring_witness` /
`deltaKCorr_pos_of_factoring_witness`. -/
theorem stokes_factoring {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) {μ ν : Fin 3} (hlt : μ < ν)
    (w : SuTwo) (v : Bond L → SuTwo) :
    covPlaqInner (stokesU ell y hlt w) (curlCovariantLM (trivialU L) v)
      = stokesPhi ell hdvd hy hlt w (lineCoarseRestrictCovLM (trivialU L) ell v) := by
  rw [covPlaqInner_stokesU, stokesPhi_apply]
  have hsum : ∑ t ∈ windowSet ell y,
      hsInner w (curlCovariantLM (trivialU L) v (windowPlaq hlt t))
      = hsInner w (∑ t ∈ windowSet ell y, curlCovariantLM (trivialU L) v (windowPlaq hlt t)) :=
    (hsInner_sum_right _ _ _).symm
  rw [hsum]
  have hwin : ∑ t ∈ windowSet ell y, curlCovariantLM (trivialU L) v (windowPlaq hlt t)
      = ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          curlValueCovariant (trivialU L) v (pathSite (pathSite x μ i) ν j, ⟨(μ, ν), hlt⟩) := by
    unfold windowSet windowPlaq
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_product]
    rfl
  rw [hwin, stokes_flat hell hdvd hy hlt v, hsInner_smul_right]

#print axioms covPlaqInner_stokesU
#print axioms stokes_factoring

/-! ## §6 — the QUANTITATIVE duality bound (every `U`, every level) -/

/-- **Cauchy–Schwarz against the projection residue**: for ANY `u` annihilating `D_U(V)` with
`⟪u,u⟫ > 0`, the Schur complement is bounded below by `⟪u, D_U B⟫² / ⟪u, u⟫`. This upgrades the
strict-positivity criterion of `CStarLevelCorrected` §3 to an explicit constant, and is the
transfer mechanism that replaces the wrong-way `[CSTAR-SCHUR-GAP]` ordering. General in `ell`,
`levels`, `U`, `B`. -/
theorem deltaJ_ge_dual_pairing_sq (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) (u : PeriodicLatticePlaquette L → SuTwo)
    (hu : ∀ v ∈ gaugeConstraintSubspaceCovFaithful ell levels U,
      covPlaqInner u (curlCovariantLM U v) = 0)
    (hupos : 0 < covPlaqInner u u) :
    (covPlaqInner u (curlCovariantLM U B)) ^ 2 / covPlaqInner u u
      ≤ deltaJQuadFormCovFaithful ell levels U B := by
  -- `u` sees the corrected curl and the raw curl identically
  set X : PeriodicLatticePlaquette L → SuTwo :=
    curlCovariantLM U (hjExtensionCovFaithful ell levels U B) with hX
  have hsplit : X = curlCovariantLM U B
      + curlCovariantLM U (hjCorrectionCovFaithful ell levels U B) := by
    rw [hX]
    show curlCovariantLM U (B + hjCorrectionCovFaithful ell levels U B) = _
    exact map_add _ _ _
  have hsees : covPlaqInner u X = covPlaqInner u (curlCovariantLM U B) := by
    rw [hsplit, covPlaqInner_add_right,
      hu _ (hjCorrectionCovFaithful_mem ell levels U B), add_zero]
  -- Cauchy–Schwarz in `PlaqFnL2`
  have hcs : (covPlaqInner u X) ^ 2 ≤ covPlaqInner u u * covPlaqInner X X := by
    have h := real_inner_mul_inner_self_le
      (WithLp.toLp 2 u : PlaqFnL2 L) (WithLp.toLp 2 X)
    rw [inner_plaqFnL2_eq_covPlaqInner, inner_plaqFnL2_eq_covPlaqInner,
      inner_plaqFnL2_eq_covPlaqInner] at h
    calc (covPlaqInner u X) ^ 2 = covPlaqInner u X * covPlaqInner u X := pow_two _
      _ ≤ covPlaqInner u u * covPlaqInner X X := h
  have hdelta : deltaJQuadFormCovFaithful ell levels U B = covPlaqInner X X := rfl
  rw [hdelta, ← hsees]
  rw [div_le_iff₀ hupos]
  calc (covPlaqInner u X) ^ 2 ≤ covPlaqInner u u * covPlaqInner X X := hcs
    _ = covPlaqInner X X * covPlaqInner u u := mul_comm _ _

#print axioms deltaJ_ge_dual_pairing_sq

/-! ## §7 — falsifiability: the identity is discriminating, not shape-forced

The Stokes identity equates two a-priori different objects. That the equality genuinely constrains
them is witnessed by the CONTROL below: the same window sum evaluated with the WRONG averaging
operator — the convicted single-bond `coarseRestrict`-style average, i.e. dropping the line
integral (`Σ_{i<ℓ}`) from the right-hand side — fails on an explicit field. This mirrors
`CoarseCurl`'s own proof that the plain block average does NOT satisfy the gradient intertwining
the line integral satisfies. The control lives in `ThirdLevelWitness.lean` (§4 there), where a
concrete nonzero coarse curl value is computed: the identity here forces that value; a dropped
`×ℓ` factor would rescale it and the witness computation would refute the identity. -/

end AdalyFormal.Balaban.ThirdLevelStokes
