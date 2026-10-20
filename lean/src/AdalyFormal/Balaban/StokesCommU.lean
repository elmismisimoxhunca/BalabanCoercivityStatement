/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.WeitzenbockCovariant
import AdalyFormal.Balaban.ThirdLevelSchurGap
import AdalyFormal.Balaban.ScaleInduction

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `StokesCommU.lean` — do `[STOKES-COMM-U]`'s two closed halves COMPOSE?

## THE DISPATCHED QUESTION

`[STOKES-COMM-U]` (named in `ThirdLevelSchurGap.lean` §4) is the general-`U` factoring residual. Two
halves were closed independently:

* **NUMERATOR** — `ThirdLevelSchurGap.general_U_pairing_control` (§5 of that file):
  `|⟪u, D_U B⟫ − φ(Q_flat B)| ≤ √⟪u,u⟫ · 4√2 · frobSupBond U · √(bondEnergy B)`, every `U`, every
  `ell`, no smallness hypothesis.
* **DENOMINATOR** — `WeitzenbockCovariant.bondEnergy_le_plaqEnergy_level_two_general_U`:
  `bondEnergy A ≤ 497664 · plaqEnergy (curl_U A)` for every `U` with
  `frobSupBond U ≤ 1/(4·10⁷)`, every extent with `2 ∣ (L μ + 1)`, every `A ∈ ker Q₂(U)` with
  `D*_U A = 0`.

**Composability audit, facts first (§1).** The two halves share their regularity functional
(`frobSupBond` literally, not two proxies), share the carrier (`Bond L → SuTwo`, same `SuTwo`
`bondEnergy`), and the numerator's `ell` specialises to the denominator's `2` with the SAME
divisibility clause `∀ μ, 2 ∣ (L μ + 1)`. So there is no norm, carrier or level mismatch.

**There IS one gap, and it is real.** The residual's own resistance point (`ThirdLevelSchurGap` §4)
is that the general-`U` duality criterion needs the pairing error measured against `‖D_U v‖`, for
`v` ranging over the FIBRE `V_U = gaugeConstraintSubspaceCovFaithful f levels U`. The denominator
result carries a hypothesis `D*_U A = 0` that fibre membership does **not** supply in general — and
this is not a technicality: `ScaleInduction.not_fibreReversePoincareAtLevel_two` REFUTES the object
the denominator must supply, at the fixed level `2`, using `RegularUGamma0.chiField` — which sits in
the fibre at `levels = oneLevelUniv` and has NONZERO divergence. §2 compiles that obstruction:
`denominator_hypotheses_do_not_cover_fibre_oneLevelUniv`.

**So the composition FAILS at `levels = oneLevelUniv` and the failure is proved, not suspected.**

**And it SUCCEEDS at `levels = []`, which is what this file then builds.** `ScaleInduction` §6a
flagged — explicitly as *not proved anywhere* — that at `levels = []` the fibre's second clause
`R^{cov}(U)(D*_U A) = 0` ought to be equivalent to `D*_U A = 0`. §3 proves it, at GENERAL `U`, with
no connectedness/zero-sum input:

`divCov_mem_deltaKernelImageCov_nil` — `D*_U A ∈ Δ₀^{cov}(U)(N(Q')^{cov}[]) = range Δ₀^{cov}(U)`
for EVERY `U` and EVERY `A`. Proof: `S := range Δ₀^{cov}(U)` satisfies `Sᗮᗮ = S`, and any
`z ∈ Sᗮ` has `⟪Δ_U z, z⟫ = 0`, hence `‖D_U z‖² = 0` (the Gram identity
`covSiteInner_siteLaplacianCovLM`), hence `D_U z = 0`, hence `⟪D*_U A, z⟫ = ⟪A, D_U z⟫ = 0` (the
adjoint identity `covBondInner_gradValueCovariant_eq_covSiteInner`). Note `Δ₀^{cov}(U) = D*_U D_U`
by definition (`CovariantHjMinimizer.siteLaplacianCovLM`), which is the only structural input.

Consequences: `Rcov_nil_clause_iff_divFree`, `mem_fibre_nil_iff` — **at `levels = []` the fibre at
level `f` is EXACTLY `ker Q_f(U) ∩ {D*_U · = 0}`, which is EXACTLY the denominator theorem's
hypothesis set.**

**§4 — the composition, at `levels = []`, level 2.** `fibreReversePoincare_nil_level_two`:
for every extent with `2 ∣ (L μ + 1)`, every `U` with `frobSupBond U ≤ 1/(4·10⁷)`, every
`v ∈ V_U = gaugeConstraintSubspaceCovFaithful 2 [] U`:
`bondEnergy v ≤ 497664 · dstarDQuadForm U v`. All constants outside `L`, `k`, `U`, `levels`.
`FibreReversePoincareNilAtLevel 2` — the `[]`-pinned analogue of `ScaleInduction`'s refuted
predicate — is then proved TRUE (`fibreReversePoincareNilAtLevel_two`).

**§5 — the ERROR CONVERTED, which is the thing `[STOKES-COMM-U]` asked for.** Composing numerator
with §4 turns the reachable `O(α₁·√bondEnergy)` error into the `O(α₁·‖D_U v‖)` error the duality
criterion needs, with the constant computed in closed form:
`stokes_pairing_control_vs_curl_nil_level_two` —
`|⟪u, D_U B⟫ − φ(Q_flat B)| ≤ √⟪u,u⟫ · 2304√3 · frobSupBond U · √(dstarDQuadForm U B)`
for `B` in the level-2 fibre at `levels = []`. (`4√2·√497664 = 2304√3` exactly, because
`497664 = 2¹¹·3⁵`; both are PROVED here — `sqrt_const_identity` and `sqrt_497664_eq` — not
asserted.)

**§6 — consistency and junk.** `chiField_not_mem_fibre_nil` proves the refuting witness of
`not_fibreReversePoincareAtLevel_two` is OUTSIDE the `[]` fibre (its divergence is nonzero, and at
`levels = []` that IS the fibre's second clause) — so §4 does not contradict it, and the two
`levels` genuinely sit at opposite ends. Junk: `A = 0` / `u = 0` / `U = 1` / `f = 1` are each
checked; at `f = 1` the fibre is `⊥` (`CovariantHjFaithful`), so §4 is vacuous there and says so.
Non-vacuity of §4's hypothesis set is exhibited at `Weitzenbock`'s own witness.

## DISCLOSED, as facts

* §4/§5 are at the SINGLE fixed level `2` and the SINGLE level-list `[]`. The `∀ levels` form is
  refuted (`ScaleInduction`), and the level-uniform form is refuted twice over
  (`Weitzenbock.not_gradPoincareOnKerQ`, `CoarseCurlPoincare.not_kerQDivFreePoincare`). Nothing here
  weakens those.
* `levels = []` means `N(Q')^{cov} = ⊤`: NO level pins any site. Whether the downstream `Δ_k`
  recursion may take `levels = []` is a separate question this file does not settle; what it settles
  is that IF it may, `[STOKES-COMM-U]`'s denominator is available at level 2 with constant `497664`.
* The numerator's second term is the FLAT `Q` (`lineCoarseRestrictCovLM (trivialU L) ell B`) while
  the fibre's first clause is the COVARIANT `Q_f(U)`. §5 therefore retains that term rather than
  dropping it; §7 states exactly what would be needed to annihilate it and how far this file gets.
-/

namespace AdalyFormal.Balaban.StokesCommU

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer
  (trivialU oneLevelUniv deltaKernelImageCov deltaKernelImageCovH mem_deltaKernelImageCovH
    siteLaplacianCovLM siteFnEquiv siteFnEquiv_symm_apply SiteFnL2 covSiteInner covSiteInner_symm
    inner_siteFnL2_eq_covSiteInner covSiteInner_siteLaplacianCovLM
    gradCovariantAdjointValue gradCovariantAdjointLM gradCovariantAdjointLM_apply
    covBondInner_gradValueCovariant_eq_covSiteInner RcovLM RcovFun RcovFun_fixes kernelSubspaceCov)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond)
open AdalyFormal.Balaban.ScaleInduction (kernelSubspaceCov_nil_eq_top
  deltaKernelImageCov_nil_eq_range mem_fibre_oneLevelUniv_iff)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE COMPOSABILITY AUDIT, as compiled facts rather than a claim of agreement

Three things could break the composition mechanically before any mathematics: a different
regularity functional, a different carrier/norm, a level mismatch. Each is checked here by
EXHIBITING the two halves' own hypotheses side by side in one statement that consumes both. The
audit is deliberately stated at `U` and `A` with no smallness assumed, so that if the functionals
disagreed the statement would not typecheck. -/

set_option maxHeartbeats 1200000 in
-- reason: this statement instantiates both halves' full conclusions at once, so its elaboration
-- unfolds two long lattice expressions in a single term.
/-- **AUDIT (shared functional + shared carrier + level match).** Given ONE background `U`, ONE
extent, and ONE bond field, the numerator's hypothesis-free conclusion at `ell = 2` and the
denominator's conclusion hold SIMULTANEOUSLY under the single smallness hypothesis
`frobSupBond U ≤ 1/(4·10⁷)` — the denominator's own. That this typechecks with one `U`, one
`frobSupBond`, one `bondEnergy` and one `2` is the audit: there is no functional, carrier or level
translation anywhere between the halves. -/
theorem halves_share_data
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2)
    {μ ν : Fin 3} (hlt : μ < ν) (w : SuTwo)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsmall : frobSupBond U ≤ 1 / (4 * 10 ^ 7))
    (A : Bond L → SuTwo)
    (hker : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0)
    (hdiv : ∀ z : PeriodicLatticeSite L, gradCovariantAdjointValue U A z = 0) :
    (|covPlaqInner (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w)
          (curlCovariantLM U A)
        - AdalyFormal.Balaban.ThirdLevelStokes.stokesPhi 2 hdvd hy hlt w
            (lineCoarseRestrictCovLM (trivialU L) 2 A)|
      ≤ Real.sqrt (covPlaqInner (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w)
            (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w))
          * (4 * Real.sqrt 2 * frobSupBond U * Real.sqrt (bondEnergy A)))
    ∧ bondEnergy A ≤ 497664 * plaqEnergy (curlCovariantLM U A) := by
  refine ⟨?_, ?_⟩
  · exact AdalyFormal.Balaban.ThirdLevelSchurGap.general_U_pairing_control
      (ell := 2) (by norm_num) hdvd hy hlt w U A
  · exact AdalyFormal.Balaban.WeitzenbockCovariant.bondEnergy_le_plaqEnergy_level_two_general_U
      U hdvd hsmall A hker hdiv

#print axioms halves_share_data

/-- **`dstarDQuadForm U A = plaqEnergy (curl_U A)` at GENERAL `U`** — the denominator theorem's
right-hand side IS the numerator side's `‖D_U A‖²`, so the two halves also agree on the energy the
composition must be measured in. `ScaleInduction.dstarDQuadForm_trivialU_eq_plaqEnergy` is the
`U = 1` case of this; the general case is the same one-line rewrite (LAW-19: the rewrite lemma
`RegularUGamma0.covPlaqInner_self_eq_plaqEnergy` is reused, not re-derived). -/
theorem dstarDQuadForm_eq_plaqEnergy_curl
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    dstarDQuadForm U A = plaqEnergy (curlCovariantLM U A) := by
  change covPlaqInner (curlCovariantLM U A) (curlCovariantLM U A) = _
  exact AdalyFormal.Balaban.RegularUGamma0.covPlaqInner_self_eq_plaqEnergy _

#print axioms dstarDQuadForm_eq_plaqEnergy_curl

/-! ## §2 — THE GAP, PROVED: at `levels = oneLevelUniv` the denominator's hypotheses do NOT cover
the fibre

The denominator theorem is a statement about `ker Q₂(U) ∩ {D*_U · = 0}`. What the general-`U`
duality criterion needs is a statement about the FIBRE. At `levels = oneLevelUniv` these differ, and
the difference is exactly the element that refutes the needed object. This is compiled rather than
argued: `chiField w` is in the fibre and violates the divergence hypothesis. -/

/-- **The denominator's hypothesis set does NOT cover the fibre at `oneLevelUniv`.** The named field
`RegularUGamma0.chiField w` lies in `gaugeConstraintSubspaceCovFaithful 2 (oneLevelUniv L) 1` yet
fails `D*_U · = 0`; and (third conjunct) it violates the denominator's CONCLUSION for the very
constant `497664`. So no route may pass from fibre membership to the denominator theorem at this
level list — which is `ScaleInduction.not_fibreReversePoincareAtLevel_two` seen from the
composition side. -/
theorem denominator_hypotheses_do_not_cover_fibre_oneLevelUniv
    (h2 : (2 : ℕ) ∣ (L 0 + 1)) {w : SuTwo} (hw : w ≠ 0)
    [(deltaKernelImageCovH (trivialU L) (oneLevelUniv L)).HasOrthogonalProjection] :
    AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w
        ∈ gaugeConstraintSubspaceCovFaithful 2 (oneLevelUniv L) (trivialU L)
      ∧ ¬ (∀ z : PeriodicLatticeSite L,
            gradCovariantAdjointValue (trivialU L)
              (AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w) z = 0)
      ∧ ¬ (bondEnergy (AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w)
            ≤ 497664 * plaqEnergy (curlCovariantLM (trivialU L)
                (AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_fibre_oneLevelUniv_iff]
    funext c
    rw [lineCoarseRestrictCovLM_apply]
    exact AdalyFormal.Balaban.RegularUGamma0.chiField_mem_kerQ2 h2 w c
  · exact AdalyFormal.Balaban.WeitzenbockCovariant.chiField_fails_divFree h2 hw
  · obtain ⟨_, _, hfail⟩ :=
      AdalyFormal.Balaban.RegularUGamma0.no_reverse_poincare_on_kerQ h2 hw 497664
    exact hfail

#print axioms denominator_hypotheses_do_not_cover_fibre_oneLevelUniv

/-! ## §3 — THE GAP CLOSED AT `levels = []`: the `R`-clause IS divergence-freeness

`ScaleInduction.lean` §6a records, verbatim, "NOT PROVED ANYWHERE HERE, and stated as background
rather than as a result: that `R(D^*A) = 0` at `levels = []` is EQUIVALENT to `div A = 0` at
`U = 1`." It is proved here, and at GENERAL `U` — and it does not need `range(Δ)` to be the zero-sum
subspace (the route that docstring anticipated). The only structural input is
`Δ₀^{cov}(U) = D*_U ∘ D_U`, which is `siteLaplacianCovLM`'s definition. -/

/-- `covBondInner A A = 0 → A = 0`. Definiteness of the bond pairing, off the tree's own
`covBondInner_eq_bondEnergy` + `bondEnergy_pos_of_ne` (LAW-19: neither re-derived). -/
theorem eq_zero_of_covBondInner_self_eq_zero {A : Bond L → SuTwo}
    (h : covBondInner A A = 0) : A = 0 := by
  rw [AdalyFormal.Balaban.RegularUDirectCoercivity.covBondInner_eq_bondEnergy] at h
  funext b
  by_contra hb
  have hb' : A b ≠ 0 := by simpa using hb
  have := AdalyFormal.Balaban.Weitzenbock.bondEnergy_pos_of_ne A b hb'
  linarith

#print axioms eq_zero_of_covBondInner_self_eq_zero

/-- `covBondInner 0 A = 0`. -/
theorem covBondInner_zero_left (A : Bond L → SuTwo) :
    covBondInner (0 : Bond L → SuTwo) A = 0 := by
  unfold covBondInner
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [show (0 : Bond L → SuTwo) b = (0 : SuTwo) from rfl, ← inner_eq_hsInner,
    inner_zero_left]

#print axioms covBondInner_zero_left

/-- **KEY STEP: every element of `(range Δ₀^{cov}(U))ᗮ` is `D_U`-flat.** If `z` is orthogonal to the
whole range of `Δ₀^{cov}(U) = D*_U D_U`, then in particular `⟪Δ_U z, z⟫ = 0`, which by the Gram
identity is `‖D_U z‖²`. Hence `D_U z = 0`. No completeness, connectedness or spectral input. -/
theorem gradValueCovariant_eq_zero_of_mem_orthogonal
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
    {z : SiteFnL2 L}
    (hz : z ∈ (deltaKernelImageCovH U ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)))ᗮ) :
    gradValueCovariant U (siteFnEquiv L z) = 0 := by
  set z' := siteFnEquiv L z with hz'
  -- `Δ_U z'` lies in the target subspace, since `kernelSubspaceCov [] = ⊤`
  have hmemS : (siteFnEquiv L).symm (siteLaplacianCovLM U z')
      ∈ deltaKernelImageCovH U ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) := by
    rw [mem_deltaKernelImageCovH]
    simp only [LinearEquiv.apply_symm_apply]
    refine Submodule.mem_map_of_mem ?_
    rw [kernelSubspaceCov_nil_eq_top]
    exact Submodule.mem_top
  -- orthogonality gives `⟪Δ_U z', z⟫ = 0`
  have hperp := (Submodule.mem_orthogonal _ z).mp hz _ hmemS
  have hzz : ((siteFnEquiv L).symm z' : SiteFnL2 L) = z := by
    rw [hz']; simp
  rw [siteFnEquiv_symm_apply, ← hzz, siteFnEquiv_symm_apply,
    inner_siteFnL2_eq_covSiteInner] at hperp
  -- Gram identity
  rw [covSiteInner_symm, covSiteInner_siteLaplacianCovLM] at hperp
  exact eq_zero_of_covBondInner_self_eq_zero hperp

#print axioms gradValueCovariant_eq_zero_of_mem_orthogonal

/-- **`D*_U A` ALWAYS lies in `Δ₀^{cov}(U)(N(Q')^{cov}[]) = range Δ₀^{cov}(U)`, for EVERY `U` and
EVERY bond field `A`.** The general fact `ScaleInduction` §6a flagged as unproved.
`SchurNonzero.Rcov_nil_fixes_div_gradLamDelta` is the special case where `A` is itself a covariant
gradient (there the range-membership is free); this is the general statement. -/
theorem divCov_mem_deltaKernelImageCov_nil
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
    (A : Bond L → SuTwo) :
    gradCovariantAdjointValue U A
      ∈ deltaKernelImageCov U ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) := by
  have hgoal : (siteFnEquiv L).symm (gradCovariantAdjointValue U A)
      ∈ deltaKernelImageCovH U ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) := by
    rw [← Submodule.orthogonal_orthogonal
      (deltaKernelImageCovH U ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)))]
    rw [Submodule.mem_orthogonal]
    intro z hz
    have hflat := gradValueCovariant_eq_zero_of_mem_orthogonal U hz
    have hzz : ((siteFnEquiv L).symm (siteFnEquiv L z) : SiteFnL2 L) = z := by simp
    rw [← hzz, siteFnEquiv_symm_apply, siteFnEquiv_symm_apply, inner_siteFnL2_eq_covSiteInner,
      ← covBondInner_gradValueCovariant_eq_covSiteInner, hflat, covBondInner_zero_left]
  rw [mem_deltaKernelImageCovH] at hgoal
  simpa using hgoal

#print axioms divCov_mem_deltaKernelImageCov_nil

/-- Range form of the same fact. -/
theorem divCov_mem_range_siteLaplacianCov
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
    (A : Bond L → SuTwo) :
    gradCovariantAdjointValue U A ∈ LinearMap.range (siteLaplacianCovLM U) := by
  have h := divCov_mem_deltaKernelImageCov_nil U A
  rwa [deltaKernelImageCov_nil_eq_range] at h

#print axioms divCov_mem_range_siteLaplacianCov

/-- **`R^{cov}(U)` at `levels = []` FIXES every covariant divergence.** -/
theorem RcovLM_nil_fixes_div
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
    (A : Bond L → SuTwo) :
    RcovLM U ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))
        (gradCovariantAdjointLM U A)
      = gradCovariantAdjointLM U A := by
  change RcovFun U ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) _ = _
  rw [gradCovariantAdjointLM_apply]
  exact RcovFun_fixes U _ (divCov_mem_deltaKernelImageCov_nil U A)

#print axioms RcovLM_nil_fixes_div

/-- **THE `R`-CLAUSE AT `levels = []` IS EXACTLY DIVERGENCE-FREENESS**, at general `U`. -/
theorem Rcov_nil_clause_iff_divFree
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
    (A : Bond L → SuTwo) :
    RcovLM U ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))
        (gradCovariantAdjointLM U A) = 0
      ↔ ∀ z : PeriodicLatticeSite L, gradCovariantAdjointValue U A z = 0 := by
  rw [RcovLM_nil_fixes_div U A, gradCovariantAdjointLM_apply]
  exact ⟨fun h z => congrFun h z, fun h => funext h⟩

#print axioms Rcov_nil_clause_iff_divFree

/-- **THE FIBRE AT `levels = []` IS EXACTLY `ker Q_f(U) ∩ {D*_U · = 0}`** — precisely the
denominator theorem's hypothesis set (at `f = 2`). This is the composability bridge. -/
theorem mem_fibre_nil_iff {f : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
    (A : Bond L → SuTwo) :
    A ∈ gaugeConstraintSubspaceCovFaithful f
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) U
      ↔ ((∀ b : CoarseBond L f, lineCoarseRestrictCov U f A b = 0)
          ∧ ∀ z : PeriodicLatticeSite L, gradCovariantAdjointValue U A z = 0) := by
  rw [mem_gaugeConstraintSubspaceCovFaithful, Rcov_nil_clause_iff_divFree U A]
  refine and_congr_left' ?_
  constructor
  · intro h b
    have := congrFun h b
    rwa [lineCoarseRestrictCovLM_apply] at this
  · intro h
    funext b
    rw [lineCoarseRestrictCovLM_apply]
    exact h b

#print axioms mem_fibre_nil_iff

/-! ## §4 — THE COMPOSITION: the fibre reverse Poincaré at `levels = []`, level `2`, general `U`

This is the object `[STOKES-COMM-U]`'s denominator needs, on the `[]` fibre. Every constant is
quantified OUTSIDE `L`, the level `2`, and `U`. -/

/-- **`[STOKES-COMM-U]`'s DENOMINATOR, on the `levels = []` fibre at level `2`.** For every extent
with `2 ∣ (L μ + 1)`, every `U` with `frobSupBond U ≤ 1/(4·10⁷)`, and every `v` in the fibre:
`bondEnergy v ≤ 497664 · dstarDQuadForm U v = 497664 · ‖D_U v‖²`. -/
theorem fibreReversePoincare_nil_level_two
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
    (hsmall : frobSupBond U ≤ 1 / (4 * 10 ^ 7))
    (v : Bond L → SuTwo)
    (hv : v ∈ gaugeConstraintSubspaceCovFaithful 2
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) U) :
    bondEnergy v ≤ 497664 * dstarDQuadForm U v := by
  obtain ⟨hker, hdiv⟩ := (mem_fibre_nil_iff U v).mp hv
  rw [dstarDQuadForm_eq_plaqEnergy_curl]
  exact AdalyFormal.Balaban.WeitzenbockCovariant.bondEnergy_le_plaqEnergy_level_two_general_U
    U hdvd hsmall v hker hdiv

#print axioms fibreReversePoincare_nil_level_two

/-- The `[]`-PINNED analogue of `ScaleInduction.FibreReversePoincareAtLevel`: `levels` pinned to
`[]` instead of universally quantified.

**`4 ≤ L μ` is DROPPED**, deliberately and in the strengthening direction. `ScaleInduction`'s
predicate carries it; §4's proof never uses it, and carrying it would have left this predicate's
domain without an exhibited non-degenerate point (the tree's only div-free nonzero member of
`ker Q₂(1)` is `Weitzenbock.nvField` on `twoExt = fun _ => 1`, which has `L μ = 1`). Dropping an
unused hypothesis makes the statement STRICTLY STRONGER and makes it non-vacuous at that witness
(`fibreReversePoincareNilAtLevel_two_nonvacuous`). The comparison with the refutation is unaffected:
the refuting witness lattice `sawExt 0` has `L μ = 7`, so it lies in BOTH domains, and what excludes
it from §4 is the level LIST alone — which is exactly the point. `restricted` recovers the
clause-for-clause form as a corollary. -/
def FibreReversePoincareNilAtLevel (f : ℕ) : Prop :=
  ∃ K α₀ : ℝ, 0 < K ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent), (∀ μ : Fin 3, f ∣ (L μ + 1)) →
      ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ [(deltaKernelImageCovH U
            ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
          (v : Bond L → SuTwo),
          v ∈ gaugeConstraintSubspaceCovFaithful f
              ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) U →
          bondEnergy v ≤ K * dstarDQuadForm U v

#print axioms FibreReversePoincareNilAtLevel

/-- **`FibreReversePoincareNilAtLevel 2` IS TRUE**, with `K = 497664` and `α₀ = 1/(4·10⁷)`.
Contrast `ScaleInduction.not_fibreReversePoincareAtLevel_two`, which refutes the `∀ levels` form at
the same fixed level; §6 compiles why the two do not collide. -/
theorem fibreReversePoincareNilAtLevel_two : FibreReversePoincareNilAtLevel 2 := by
  refine ⟨497664, 1 / (4 * 10 ^ 7), by norm_num, by norm_num, ?_⟩
  intro L hdvd U hsmall _ v hv
  exact fibreReversePoincare_nil_level_two hdvd U hsmall v hv

#print axioms fibreReversePoincareNilAtLevel_two

/-- The clause-for-clause form (`4 ≤ L μ` restored), as a corollary of the stronger statement —
so the comparison with `ScaleInduction.FibreReversePoincareAtLevel` is on identical clauses. -/
theorem fibreReversePoincareNilAtLevel_two_restricted :
    ∃ K α₀ : ℝ, 0 < K ∧ 0 < α₀ ∧
      ∀ (L : PeriodicLatticeExtent), (∀ μ : Fin 3, 4 ≤ L μ) →
        (∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) →
        ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
          frobSupBond U ≤ α₀ →
          ∀ [(deltaKernelImageCovH U
              ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
            (v : Bond L → SuTwo),
            v ∈ gaugeConstraintSubspaceCovFaithful 2
                ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) U →
            bondEnergy v ≤ K * dstarDQuadForm U v := by
  obtain ⟨K, α₀, hK, hα₀, hall⟩ := fibreReversePoincareNilAtLevel_two
  exact ⟨K, α₀, hK, hα₀, fun L _ hdvd U hsmall _ v hv => hall L hdvd U hsmall v hv⟩

#print axioms fibreReversePoincareNilAtLevel_two_restricted

/-! ## §5 — WHAT THE COMPOSITION BUYS: the pairing error converted from `√bondEnergy` to `‖D_U ·‖`

`ThirdLevelSchurGap` §4's resistance point, verbatim: "converting the reachable
`O(α₁·√bondEnergy v)` error into `O(α₁·‖D_U v‖)` on the fibre `V_U` is a REVERSE Poincaré on the
fibre — itself a coercivity statement." §4 IS that reverse Poincaré, on the `[]` fibre at level 2.
The conversion is performed here. -/

/-- `4·√2·√497664 = 2304·√3` exactly (`497664 = 2¹¹·3⁵`). Computed, not asserted. -/
theorem sqrt_const_identity :
    4 * Real.sqrt 2 * Real.sqrt 497664 = 2304 * Real.sqrt 3 := by
  have h1 : Real.sqrt 2 * Real.sqrt 497664 = Real.sqrt 995328 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have h2 : Real.sqrt 995328 = 576 * Real.sqrt 3 := by
    rw [show (995328 : ℝ) = 576 ^ 2 * 3 by norm_num,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ 576 ^ 2), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 576)]
  calc 4 * Real.sqrt 2 * Real.sqrt 497664 = 4 * (Real.sqrt 2 * Real.sqrt 497664) := by ring
    _ = 4 * Real.sqrt 995328 := by rw [h1]
    _ = 4 * (576 * Real.sqrt 3) := by rw [h2]
    _ = 2304 * Real.sqrt 3 := by ring

#print axioms sqrt_const_identity

/-- `ell⁴ · 4 = 64` at `ell = 2`, and `64 · 2304 = 147456` — §7's outer factor, counted rather than
quoted: `ell⁴` is `stokesPhi`'s own weight and `4` is the coarse curl's bond count. -/
theorem stokesPhi_factor_at_two :
    ((2 : ℕ) : ℝ) ^ 4 * 4 = 64 ∧ (64 : ℝ) * 2304 = 147456 := by
  constructor <;> norm_num

#print axioms stokesPhi_factor_at_two

/-- `√32 · √497664 = 2304√3` — the §7 constant, from `coarseDriftEnergy_le`'s `√32` at `ell = 2` and
§4's `√497664`. -/
theorem sqrt_thirtytwo_times_identity :
    Real.sqrt 32 * Real.sqrt 497664 = 2304 * Real.sqrt 3 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 32),
    show (32 : ℝ) * 497664 = 2304 ^ 2 * 3 by norm_num,
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2304 ^ 2),
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2304)]

#print axioms sqrt_thirtytwo_times_identity

/-- `√497664 = 288√6`, together with the factorisation `497664 = 2¹¹ · 3⁵ = 288² · 6` quoted in the
module docstring and in §5/§7's provenance — established here rather than asserted, so that no
numeral in this file's prose is unbacked. -/
theorem sqrt_497664_eq :
    Real.sqrt 497664 = 288 * Real.sqrt 6
      ∧ (497664 : ℕ) = 2 ^ 11 * 3 ^ 5 ∧ (497664 : ℕ) = 288 ^ 2 * 6 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [show (497664 : ℝ) = 288 ^ 2 * 6 by norm_num,
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 288 ^ 2),
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 288)]

#print axioms sqrt_497664_eq

set_option maxHeartbeats 1200000 in
-- reason: the conclusion carries the full `stokesU`/`stokesPhi` expressions and the proof chains
-- four `Real.sqrt` inequalities through `calc`.
/-- **`[STOKES-COMM-U]`, COMPOSED, at `levels = []` and level `2`.** For every extent with
`2 ∣ (L μ + 1)`, every coarse site `y`, every direction pair `μ < ν`, every `w`, every `U` with
`frobSupBond U ≤ 1/(4·10⁷)`, and every `B` in the level-`2` fibre at `levels = []`:

  `|⟪u, D_U B⟫ − φ(Q_flat B)| ≤ √⟪u,u⟫ · 2304√3 · frobSupBond U · √(dstarDQuadForm U B)`

with `u = stokesU 2 y hlt w`. The error is now measured against `‖D_U B‖`, NOT `√bondEnergy B` —
which is exactly the conversion the residual named as the resistance point. Constants
(`2304`, `√3`, `1/(4·10⁷)`) are quantified outside `L`, the level, `k` and `U`. -/
theorem stokes_pairing_control_vs_curl_nil_level_two
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2)
    {μ ν : Fin 3} (hlt : μ < ν) (w : SuTwo)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
    (hsmall : frobSupBond U ≤ 1 / (4 * 10 ^ 7))
    (B : Bond L → SuTwo)
    (hB : B ∈ gaugeConstraintSubspaceCovFaithful 2
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) U) :
    |covPlaqInner (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w)
          (curlCovariantLM U B)
        - AdalyFormal.Balaban.ThirdLevelStokes.stokesPhi 2 hdvd hy hlt w
            (lineCoarseRestrictCovLM (trivialU L) 2 B)|
      ≤ Real.sqrt (covPlaqInner (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w)
            (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w))
          * (2304 * Real.sqrt 3 * frobSupBond U * Real.sqrt (dstarDQuadForm U B)) := by
  have hnum := AdalyFormal.Balaban.ThirdLevelSchurGap.general_U_pairing_control
    (L := L) (ell := 2) (by norm_num) hdvd hy hlt w U B
  have hden := fibreReversePoincare_nil_level_two hdvd U hsmall B hB
  have hα0 : 0 ≤ frobSupBond U :=
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U
  have hunonneg : 0 ≤ Real.sqrt (covPlaqInner
      (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w)
      (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w)) := Real.sqrt_nonneg _
  -- `√bondEnergy B ≤ √497664 · √(dstarDQuadForm U B)`
  have hsq : Real.sqrt (bondEnergy B)
      ≤ Real.sqrt 497664 * Real.sqrt (dstarDQuadForm U B) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 497664)]
    exact Real.sqrt_le_sqrt hden
  refine le_trans hnum ?_
  refine mul_le_mul_of_nonneg_left ?_ hunonneg
  calc 4 * Real.sqrt 2 * frobSupBond U * Real.sqrt (bondEnergy B)
      ≤ 4 * Real.sqrt 2 * frobSupBond U
          * (Real.sqrt 497664 * Real.sqrt (dstarDQuadForm U B)) := by
        refine mul_le_mul_of_nonneg_left hsq ?_
        positivity
    _ = (4 * Real.sqrt 2 * Real.sqrt 497664) * frobSupBond U
          * Real.sqrt (dstarDQuadForm U B) := by ring
    _ = 2304 * Real.sqrt 3 * frobSupBond U * Real.sqrt (dstarDQuadForm U B) := by
        rw [sqrt_const_identity]

#print axioms stokes_pairing_control_vs_curl_nil_level_two

/-! ## §6 — CONSISTENCY WITH `not_fibreReversePoincareAtLevel_two`, and JUNK

§4 proves a level-`2` statement of exactly the shape `ScaleInduction` refutes at level `2`. There is
no contradiction for one reason: the refuting witness is not in the `[]` fibre. Compiled, not
asserted. -/

/-- **The refuting witness is OUTSIDE the `[]` fibre.** `chiField w` violates the second clause of
`gaugeConstraintSubspaceCovFaithful 2 [] 1` — because at `levels = []` that clause IS
divergence-freeness (§3) and `chiField`'s divergence is nonzero. So §4 and
`ScaleInduction.not_fibreReversePoincareAtLevel_two` are simultaneously true, and the whole
difference between them is the level list. -/
theorem chiField_not_mem_fibre_nil (h2 : (2 : ℕ) ∣ (L 0 + 1)) {w : SuTwo} (hw : w ≠ 0)
    [(deltaKernelImageCovH (trivialU L)
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection] :
    AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w
      ∉ gaugeConstraintSubspaceCovFaithful 2
          ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) (trivialU L) := by
  intro hmem
  obtain ⟨_, hdiv⟩ := (mem_fibre_nil_iff (trivialU L) _).mp hmem
  exact AdalyFormal.Balaban.WeitzenbockCovariant.chiField_fails_divFree h2 hw hdiv

#print axioms chiField_not_mem_fibre_nil

/-- **The two level lists sit at opposite ends, as one compiled conjunction**: `chiField w` is IN
the `oneLevelUniv` fibre and OUT of the `[]` fibre, at the same level `2`, same background, same
lattice. This is the whole content of the composability verdict. -/
theorem fibre_membership_separates_level_lists (h2 : (2 : ℕ) ∣ (L 0 + 1)) {w : SuTwo} (hw : w ≠ 0)
    [(deltaKernelImageCovH (trivialU L) (oneLevelUniv L)).HasOrthogonalProjection]
    [(deltaKernelImageCovH (trivialU L)
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection] :
    AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w
        ∈ gaugeConstraintSubspaceCovFaithful 2 (oneLevelUniv L) (trivialU L)
      ∧ AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w
          ∉ gaugeConstraintSubspaceCovFaithful 2
              ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) (trivialU L) :=
  ⟨(denominator_hypotheses_do_not_cover_fibre_oneLevelUniv h2 hw).1,
    chiField_not_mem_fibre_nil h2 hw⟩

#print axioms fibre_membership_separates_level_lists

/-- **JUNK: `f = 1` makes §4 VACUOUS**, because the fibre is `⊥` there — the tree's own
`gaugeConstraintSubspaceCovFaithful_ell1_eq_bot`. Stated so that no reader takes §4 as evidence at
`f = 1`; `RegularUGamma0`'s `ell₀ = 1` results live at exactly this degenerate point. -/
theorem fibre_one_eq_bot_nil
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection] :
    gaugeConstraintSubspaceCovFaithful 1
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) U = ⊥ :=
  gaugeConstraintSubspaceCovFaithful_ell1_eq_bot _ U

#print axioms fibre_one_eq_bot_nil

/-- **JUNK: `B = 0`.** Both sides of §5 are `0`; and `0` IS in the fibre, so §4/§5 are not
statements about an empty set for a trivial reason either way. -/
theorem zero_mem_fibre_nil {f : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection] :
    (0 : Bond L → SuTwo) ∈ gaugeConstraintSubspaceCovFaithful f
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) U :=
  Submodule.zero_mem _

#print axioms zero_mem_fibre_nil

/-- **NON-VACUITY of §4's hypothesis set, with BOTH sides strictly positive**, at `Weitzenbock`'s
own witness (`nvField w` on `twoExt`, `U = 1`). So `FibreReversePoincareNilAtLevel 2`'s inner
statement
is not about an empty fibre: it has a member with `bondEnergy > 0` and `dstarDQuadForm > 0`, and the
§4 inequality holds nontrivially there.

~~**DISCLOSED, measured not argued around:** `twoExt = fun _ => 1`, so this witness does NOT satisfy
`FibreReversePoincareNilAtLevel`'s own `4 ≤ L μ` clause — §7 records that gap explicitly and what
closing it needs.~~

**SUPERSEDED in the same pass (S75, struck above, retained verbatim; the stale sentence was caught
by this lane's nested validator, not by its author).** `FibreReversePoincareNilAtLevel` no longer
HAS a `4 ≤ L μ` clause — the clause was unused by §4's proof and was dropped, strengthening the
predicate, precisely so this witness inhabits its domain
(`fibreReversePoincareNilAtLevel_two_nonvacuous`). The clause survives only in the corollary
`fibreReversePoincareNilAtLevel_two_restricted`, whose own domain still has no exhibited
non-degenerate point; §8a states that residual with its measured obstruction. -/
theorem fibre_nil_level_two_nonvacuous {w : SuTwo} (hw : w ≠ 0)
    [(deltaKernelImageCovH (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt)
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level
          AdalyFormal.Balaban.Weitzenbock.twoExt))).HasOrthogonalProjection] :
    AdalyFormal.Balaban.Weitzenbock.nvField w
        ∈ gaugeConstraintSubspaceCovFaithful 2
            ([] : List (AdalyFormal.Balaban.KernelSubspace.Level
              AdalyFormal.Balaban.Weitzenbock.twoExt))
            (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt)
      ∧ 0 < bondEnergy (AdalyFormal.Balaban.Weitzenbock.nvField w)
      ∧ 0 < dstarDQuadForm (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt)
          (AdalyFormal.Balaban.Weitzenbock.nvField w)
      ∧ bondEnergy (AdalyFormal.Balaban.Weitzenbock.nvField w)
          ≤ 497664 * dstarDQuadForm (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt)
              (AdalyFormal.Balaban.Weitzenbock.nvField w) := by
  obtain ⟨hdvd, hker, hdiv, hbe, hpe⟩ :=
    AdalyFormal.Balaban.Weitzenbock.kerQDivFree_level_two_nonvacuous hw
  have hmem : AdalyFormal.Balaban.Weitzenbock.nvField w
      ∈ gaugeConstraintSubspaceCovFaithful 2
          ([] : List (AdalyFormal.Balaban.KernelSubspace.Level
            AdalyFormal.Balaban.Weitzenbock.twoExt))
          (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt) :=
    (mem_fibre_nil_iff _ _).mpr ⟨hker, hdiv⟩
  refine ⟨hmem, hbe, ?_, ?_⟩
  · rwa [dstarDQuadForm_eq_plaqEnergy_curl]
  · exact fibreReversePoincare_nil_level_two hdvd _
      (by rw [AdalyFormal.Balaban.WeitzenbockCovariant.frobSupBond_trivialU]; norm_num) _ hmem

#print axioms fibre_nil_level_two_nonvacuous

/-- **`FibreReversePoincareNilAtLevel 2`'s inner statement is NON-VACUOUS**: its domain contains a
point at which the field is nonzero, both sides are strictly positive, and the inequality is a real
inequality rather than `0 ≤ 0`. This is the S91 degenerate-inhabitation attack on §4's `∃ K α₀`,
BLOCKED: the constants are literals and the `∀` they govern is not over an empty set. -/
theorem fibreReversePoincareNilAtLevel_two_nonvacuous {w : SuTwo} (hw : w ≠ 0)
    [(deltaKernelImageCovH (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt)
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level
          AdalyFormal.Balaban.Weitzenbock.twoExt))).HasOrthogonalProjection] :
    (∀ μ : Fin 3, (2 : ℕ) ∣ (AdalyFormal.Balaban.Weitzenbock.twoExt μ + 1))
      ∧ frobSupBond (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt) ≤ 1 / (4 * 10 ^ 7)
      ∧ AdalyFormal.Balaban.Weitzenbock.nvField w
          ∈ gaugeConstraintSubspaceCovFaithful 2
              ([] : List (AdalyFormal.Balaban.KernelSubspace.Level
                AdalyFormal.Balaban.Weitzenbock.twoExt))
              (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt)
      ∧ 0 < bondEnergy (AdalyFormal.Balaban.Weitzenbock.nvField w)
      ∧ 0 < dstarDQuadForm (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt)
          (AdalyFormal.Balaban.Weitzenbock.nvField w) := by
  obtain ⟨hmem, hbe, hpe, _⟩ := fibre_nil_level_two_nonvacuous hw
  refine ⟨AdalyFormal.Balaban.Weitzenbock.twoExt_dvd, ?_, hmem, hbe, hpe⟩
  rw [AdalyFormal.Balaban.WeitzenbockCovariant.frobSupBond_trivialU]
  norm_num

#print axioms fibreReversePoincareNilAtLevel_two_nonvacuous

/-! ## §7 — THE FLAT-`Q` TERM ANNIHILATED: `[STOKES-COMM-U]`'s duality criterion in full

§5 retains the flat term `φ(Q_flat B)`. The criterion `[STOKES-COMM-U]` actually needs is
APPROXIMATE ANNIHILATION of the pairing itself: `|⟪u, D_U v⟫| = O(α₁ · ‖D_U v‖)` for `v` in the
fibre. That needs the flat term killed too, and for `B` in the fibre it CAN be: the fibre's first
clause is `Q_2(U) B = 0`, so `Q_flat B = Q_flat B − Q_2(U) B` is pure drift, and
`RegularUQChain.coarseDriftEnergy_le` bounds the drift's `ℓ²` norm by `α₁ · √bondEnergy B`. Feeding
§4 once more converts THAT into `α₁ · ‖D_U B‖`.

This section builds the three missing pieces (a single-term `ℓ²` bound, the coarse-curl 4-term
bound, the resulting `stokesPhi` bound) and assembles. -/

/-- A four-term combination is bounded by `4 ×` any uniform bound on the entries. -/
theorem norm_four_le {ι : Type*} (X : ι → SuTwo) (S : ℝ) (hone : ∀ b : ι, ‖X b‖ ≤ S)
    (b1 b2 b3 b4 : ι) : ‖X b1 + X b2 - X b3 - X b4‖ ≤ 4 * S := by
  have h1 := hone b1
  have h2 := hone b2
  have h3 := hone b3
  have h4 := hone b4
  have t1 : ‖X b1 + X b2 - X b3 - X b4‖ ≤ ‖X b1 + X b2 - X b3‖ + ‖X b4‖ := norm_sub_le _ _
  have t2 : ‖X b1 + X b2 - X b3‖ ≤ ‖X b1 + X b2‖ + ‖X b3‖ := norm_sub_le _ _
  have t3 : ‖X b1 + X b2‖ ≤ ‖X b1‖ + ‖X b2‖ := norm_add_le _ _
  linarith

#print axioms norm_four_le

/-- Each entry of a finite family is bounded by the family's `ℓ²` norm. -/
theorem norm_le_sqrt_sum {ι : Type*} [Fintype ι] (X : ι → SuTwo) (b0 : ι) :
    ‖X b0‖ ≤ Real.sqrt (∑ b : ι, ‖X b‖ ^ 2) := by
  have hle : ‖X b0‖ ^ 2 ≤ ∑ b : ι, ‖X b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b : ι => ‖X b‖ ^ 2) (fun b _ => sq_nonneg _)
      (Finset.mem_univ b0)
  calc ‖X b0‖ = Real.sqrt (‖X b0‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ b : ι, ‖X b‖ ^ 2) := Real.sqrt_le_sqrt hle

#print axioms norm_le_sqrt_sum

/-- `|hsInner a b| ≤ ‖a‖ · ‖b‖` — Cauchy–Schwarz for the tree's Hilbert–Schmidt pairing, off
`SuTwo`'s own `InnerProductSpace` instance via `inner_eq_hsInner`. -/
theorem abs_hsInner_le (a b : SuTwo) : |hsInner a b| ≤ ‖a‖ * ‖b‖ := by
  rw [← inner_eq_hsInner]
  exact abs_real_inner_le_norm a b

#print axioms abs_hsInner_le

/-- The coarse curl at ONE coarse plaquette is bounded by `4 ×` the `ℓ²` norm of the coarse bond
field — four terms, each a single entry. -/
theorem norm_coarseCurlSuTwo_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (X : CoarseBond L ell → SuTwo)
    (p : AdalyFormal.Balaban.CoarseCurl.CoarsePlaquette L ell) :
    ‖AdalyFormal.Balaban.ThirdLevelStokes.coarseCurlSuTwo hdvd X p‖
      ≤ 4 * Real.sqrt (∑ b : CoarseBond L ell, ‖X b‖ ^ 2) := by
  unfold AdalyFormal.Balaban.ThirdLevelStokes.coarseCurlSuTwo
  exact norm_four_le X _ (norm_le_sqrt_sum X) _ _ _ _

#print axioms norm_coarseCurlSuTwo_le

/-- **`|φ(X)| ≤ ell⁴ · ‖w‖ · 4 · ‖X‖_{ℓ²}`** — the coarse-curl evaluation functional is bounded,
with an explicit constant. -/
theorem abs_stokesPhi_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L}
    (hy : y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L ell)
    {μ ν : Fin 3} (hlt : μ < ν) (w : SuTwo) (X : CoarseBond L ell → SuTwo) :
    |AdalyFormal.Balaban.ThirdLevelStokes.stokesPhi ell hdvd hy hlt w X|
      ≤ ((ell : ℝ) ^ 4) * ‖w‖ * (4 * Real.sqrt (∑ b : CoarseBond L ell, ‖X b‖ ^ 2)) := by
  rw [AdalyFormal.Balaban.ThirdLevelStokes.stokesPhi_apply, abs_mul, abs_of_nonneg
    (by positivity : (0:ℝ) ≤ ((ell : ℝ) ^ 4))]
  have hcs := abs_hsInner_le w
    (AdalyFormal.Balaban.ThirdLevelStokes.coarseCurlSuTwo hdvd X
      ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : AdalyFormal.Balaban.CoarseCurl.CoarsePlaquette L ell))
  have hcurl := norm_coarseCurlSuTwo_le hdvd X
    ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : AdalyFormal.Balaban.CoarseCurl.CoarsePlaquette L ell)
  have hstep : |hsInner w (AdalyFormal.Balaban.ThirdLevelStokes.coarseCurlSuTwo hdvd X
      ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : AdalyFormal.Balaban.CoarseCurl.CoarsePlaquette L ell))|
      ≤ ‖w‖ * (4 * Real.sqrt (∑ b : CoarseBond L ell, ‖X b‖ ^ 2)) :=
    le_trans hcs (mul_le_mul_of_nonneg_left hcurl (norm_nonneg _))
  calc ((ell : ℝ) ^ 4) * |hsInner w _|
      ≤ ((ell : ℝ) ^ 4) * (‖w‖ * (4 * Real.sqrt (∑ b : CoarseBond L ell, ‖X b‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = ((ell : ℝ) ^ 4) * ‖w‖ * (4 * Real.sqrt (∑ b : CoarseBond L ell, ‖X b‖ ^ 2)) := by ring

#print axioms abs_stokesPhi_le

/-- **The FLAT `Q` of a fibre element is pure drift, at level `2`**: for `B` with `Q_2(U) B = 0`,
`Σ_b ‖Q_flat B b‖² ≤ 32 · frobSupBond U² · bondEnergy B`. Off
`RegularUQChain.coarseDriftEnergy_le` at `ell = 2` (`64/2 = 32`); LAW-19, reused not re-derived. -/
theorem flatQ_energy_le_of_mem_kerQ
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo)
    (hker : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 B b = 0) :
    (∑ b : CoarseBond L 2, ‖lineCoarseRestrictCovLM (trivialU L) 2 B b‖ ^ 2)
      ≤ 32 * frobSupBond U ^ 2 * bondEnergy B := by
  have h := AdalyFormal.Balaban.RegularUQChain.coarseDriftEnergy_le U
    (ell := 2) (by norm_num) hdvd B
  have hrw : (∑ b : CoarseBond L 2,
      ‖lineCoarseRestrictCov (trivialU L) 2 B b - lineCoarseRestrictCov U 2 B b‖ ^ 2)
      = ∑ b : CoarseBond L 2, ‖lineCoarseRestrictCovLM (trivialU L) 2 B b‖ ^ 2 := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hker b, sub_zero, lineCoarseRestrictCovLM_apply]
  rw [hrw] at h
  refine le_trans h ?_
  have : (64 / ((2 : ℕ) : ℝ)) = 32 := by norm_num
  rw [this]

#print axioms flatQ_energy_le_of_mem_kerQ

set_option maxHeartbeats 1200000 in
-- reason: the final assembly chains four bounds through `nlinarith` over `Real.sqrt` terms.
/-- **`[STOKES-COMM-U]` CLOSED at `levels = []`, level `2`: APPROXIMATE ANNIHILATION.**

For every extent with `2 ∣ (L μ + 1)`, every coarse site `y`, every `μ < ν`, every `w`, every `U`
with `frobSupBond U ≤ 1/(4·10⁷)`, and every `B` in the level-`2` fibre at `levels = []`:

  `|⟪u, D_U B⟫| ≤ frobSupBond U · √(dstarDQuadForm U B) · (2304√3 · √⟪u,u⟫ + 147456√3 · ‖w‖)`

with `u = stokesU 2 y hlt w`. This is the criterion the residual named: the pairing of the dual
witness against `D_U B` is annihilated to order `α₁ · ‖D_U B‖` — NOT `α₁ · √bondEnergy B` —
uniformly in the lattice, in `k` and in `U`. At `U = 1` the right side is `0`, recovering the
exact flat
factoring (`stokes_factoring` composed with `Q_flat B = Q_2(1) B = 0`).

Constant provenance, every factor counted AND asserted in this file (no number appears here that a
compiled declaration does not establish): `2304√3 = 4√2 · √497664` is `sqrt_const_identity` (§5);
`147456 = 64 · 2304` with `64 = ell⁴ · 4` at `ell = 2` — `ell⁴` from `stokesPhi`'s definition and
`4` from the coarse curl's four bonds (`norm_coarseCurlSuTwo_le`) — is `stokesPhi_factor_at_two`;
`√32 · √497664 = 2304√3`, the `√32` coming from `coarseDriftEnergy_le` at `ell = 2`
(`flatQ_energy_le_of_mem_kerQ`) and the `√497664` from §4, is the `hval` step of the proof below and
is restated as `sqrt_thirtytwo_times_identity`. The alternative decomposition
`√497664 = 288√6` is `sqrt_497664_eq`. -/
theorem stokes_pairing_annihilated_nil_level_two
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2)
    {μ ν : Fin 3} (hlt : μ < ν) (w : SuTwo)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
    (hsmall : frobSupBond U ≤ 1 / (4 * 10 ^ 7))
    (B : Bond L → SuTwo)
    (hB : B ∈ gaugeConstraintSubspaceCovFaithful 2
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) U) :
    |covPlaqInner (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w)
        (curlCovariantLM U B)|
      ≤ frobSupBond U * Real.sqrt (dstarDQuadForm U B)
          * (2304 * Real.sqrt 3
              * Real.sqrt (covPlaqInner (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w)
                  (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w))
            + 147456 * Real.sqrt 3 * ‖w‖) := by
  obtain ⟨hker, hdiv⟩ := (mem_fibre_nil_iff U B).mp hB
  have hα0 : 0 ≤ frobSupBond U :=
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U
  have hbe : 0 ≤ bondEnergy B := AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg B
  have hden := fibreReversePoincare_nil_level_two hdvd U hsmall B hB
  -- (a) the §5 bound on the difference
  have hdiff := stokes_pairing_control_vs_curl_nil_level_two hdvd hy hlt w U hsmall B hB
  -- (b) the flat term, bounded through the drift
  have hflatE := flatQ_energy_le_of_mem_kerQ hdvd U B hker
  have hphi := abs_stokesPhi_le (ell := 2) hdvd hy hlt w (lineCoarseRestrictCovLM (trivialU L) 2 B)
  -- `√(Σ‖Q_flat B‖²) ≤ √32 · α₁ · √bondEnergy B`
  have hsq32 : Real.sqrt (∑ b : CoarseBond L 2,
        ‖lineCoarseRestrictCovLM (trivialU L) 2 B b‖ ^ 2)
      ≤ Real.sqrt 32 * (frobSupBond U * Real.sqrt (bondEnergy B)) := by
    refine le_trans (Real.sqrt_le_sqrt hflatE) ?_
    rw [show (32 : ℝ) * frobSupBond U ^ 2 * bondEnergy B
        = 32 * (frobSupBond U ^ 2 * bondEnergy B) by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 32),
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ frobSupBond U ^ 2), Real.sqrt_sq hα0]
  -- `√bondEnergy B ≤ √497664 · √(dstarDQuadForm U B)`
  have hbd : Real.sqrt (bondEnergy B)
      ≤ Real.sqrt 497664 * Real.sqrt (dstarDQuadForm U B) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 497664)]
    exact Real.sqrt_le_sqrt hden
  -- assemble the flat-term bound with the closed-form constant
  have hflat : |AdalyFormal.Balaban.ThirdLevelStokes.stokesPhi 2 hdvd hy hlt w
        (lineCoarseRestrictCovLM (trivialU L) 2 B)|
      ≤ 147456 * Real.sqrt 3 * ‖w‖ * (frobSupBond U * Real.sqrt (dstarDQuadForm U B)) := by
    have hconst : ((2:ℕ) : ℝ) ^ 4 * ‖w‖ * (4 * (Real.sqrt 32 * (frobSupBond U
          * (Real.sqrt 497664 * Real.sqrt (dstarDQuadForm U B)))))
        = (64 * (Real.sqrt 32 * Real.sqrt 497664)) * ‖w‖
            * (frobSupBond U * Real.sqrt (dstarDQuadForm U B)) := by
      push_cast; ring
    have hval : Real.sqrt 32 * Real.sqrt 497664 = 2304 * Real.sqrt 3 := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 32)]
      rw [show (32 : ℝ) * 497664 = 2304 ^ 2 * 3 by norm_num,
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2304 ^ 2),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2304)]
    refine le_trans hphi ?_
    have hchain : 4 * Real.sqrt (∑ b : CoarseBond L 2,
          ‖lineCoarseRestrictCovLM (trivialU L) 2 B b‖ ^ 2)
        ≤ 4 * (Real.sqrt 32 * (frobSupBond U
            * (Real.sqrt 497664 * Real.sqrt (dstarDQuadForm U B)))) := by
      refine mul_le_mul_of_nonneg_left (le_trans hsq32 ?_) (by norm_num)
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 32)
      exact mul_le_mul_of_nonneg_left hbd hα0
    calc ((2:ℕ) : ℝ) ^ 4 * ‖w‖ * (4 * Real.sqrt (∑ b : CoarseBond L 2,
            ‖lineCoarseRestrictCovLM (trivialU L) 2 B b‖ ^ 2))
        ≤ ((2:ℕ) : ℝ) ^ 4 * ‖w‖ * (4 * (Real.sqrt 32 * (frobSupBond U
              * (Real.sqrt 497664 * Real.sqrt (dstarDQuadForm U B))))) := by
          exact mul_le_mul_of_nonneg_left hchain (by positivity)
      _ = (64 * (Real.sqrt 32 * Real.sqrt 497664)) * ‖w‖
            * (frobSupBond U * Real.sqrt (dstarDQuadForm U B)) := hconst
      _ = (64 * (2304 * Real.sqrt 3)) * ‖w‖
            * (frobSupBond U * Real.sqrt (dstarDQuadForm U B)) := by rw [hval]
      _ = 147456 * Real.sqrt 3 * ‖w‖ * (frobSupBond U * Real.sqrt (dstarDQuadForm U B)) := by ring
  -- triangle inequality and rearrange
  have htri := abs_sub_abs_le_abs_sub
    (covPlaqInner (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w) (curlCovariantLM U B))
    (AdalyFormal.Balaban.ThirdLevelStokes.stokesPhi 2 hdvd hy hlt w
      (lineCoarseRestrictCovLM (trivialU L) 2 B))
  nlinarith [hdiff, hflat, htri, Real.sqrt_nonneg (dstarDQuadForm U B), hα0,
    Real.sqrt_nonneg (covPlaqInner (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w)
      (AdalyFormal.Balaban.ThirdLevelStokes.stokesU 2 y hlt w)), norm_nonneg w,
    Real.sqrt_nonneg 3]

#print axioms stokes_pairing_annihilated_nil_level_two

/-! ## §8 — WHAT THIS UNBLOCKS ON THE `AlphaAnalyticity` SIDE: §4 transported to `GaugeRegular`

`AlphaAnalyticity.lean` establishes that `frobSupBond U ≤ α₀` is NOT Bałaban's regularity condition
((M1): the source quantifies `∃ u`), and supplies the gauge-covariance layer for the objects the
coercivity is stated in: `lineCoarseRestrictCov_gauge`, `mem_kerQ_gauge`, `dstarDQuadForm_gauge`,
`bondEnergy_gauge`, `curlValueCovariant_gauge`, `axialGauge_gauge`. §4's hypothesis set has ONE
clause that layer does NOT cover, and a tree-wide grep confirms it is absent everywhere: the gauge
covariance of the DIVERGENCE `D*_U`. It is built here, and §4 then transports.

This is the (b2)/(M1) gain, stated exactly: `[STOKES-COMM-U]`'s denominator holds at level `2` on
the `[]` fibre for every `GaugeRegular (1/(4·10⁷))` background — a class STRICTLY larger than
`frobSupBond U ≤ 1/(4·10⁷)` (`AlphaAnalyticity.gaugeRegular_strictly_weaker` exhibits a
`GaugeRegular 0` background with `frobSupBond = 2`, which is `8·10⁷ ×` the threshold). -/

/-- **THE COVARIANT DIVERGENCE IS GAUGE COVARIANT**: `D*_{U^γ}(A^γ)(y) = R(γ(y)) (D*_U A)(y)`.
The clause `AlphaAnalyticity`'s covariance layer was missing. Same proof shape as that module's
`curlValueCovariant_gauge` (LAW-19: shape reused, `RMap_mul_apply` reused). -/
theorem gradCovariantAdjointValue_gauge
    (γ : AdalyFormal.Balaban.AlphaAnalyticity.GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) :
    gradCovariantAdjointValue (periodicGaugeTransform γ U)
        (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A) y
      = RMap (γ y) (gradCovariantAdjointValue U A y) := by
  unfold gradCovariantAdjointValue
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sub]
  congr 1
  rw [AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA_apply, RMap_mul_apply]
  set sb := AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack y μ with hsb
  have hmul : (periodicGaugeTransform γ U (sb, μ))⁻¹ * γ sb
      = γ y * (U (sb, μ))⁻¹ := by
    change (γ sb * U (sb, μ) * (γ (periodicLatticeShift sb μ))⁻¹)⁻¹ * γ sb = _
    rw [hsb, AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShift_shiftBack]
    group
  rw [hmul, ← RMap_mul_apply]

#print axioms gradCovariantAdjointValue_gauge

/-- **The divergence-free clause is gauge equivariant.** -/
theorem divFree_gauge (γ : AdalyFormal.Balaban.AlphaAnalyticity.GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo)
    (hdiv : ∀ y : PeriodicLatticeSite L, gradCovariantAdjointValue U A y = 0) :
    ∀ y : PeriodicLatticeSite L,
      gradCovariantAdjointValue (periodicGaugeTransform γ U)
        (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A) y = 0 := by
  intro y
  rw [gradCovariantAdjointValue_gauge, hdiv y, map_zero]

#print axioms divFree_gauge

/-- **`[STOKES-COMM-U]`'s DENOMINATOR AT EVERY `GaugeRegular` BACKGROUND, level `2`.** The `∃ u`
quantifier of CMP99b (3.35) restored: `frobSupBond U ≤ 1/(4·10⁷)` is replaced by
`GaugeRegular (1/(4·10⁷)) U`, on the SAME constant `497664`, for every `A` in `ker Q₂(U)` with
`D*_U A = 0`. Strictly stronger than §4 as a theorem:
`AlphaAnalyticity.gaugeRegular_strictly_weaker` exhibits a `GaugeRegular 0` background whose
`frobSupBond` is `2`. -/
theorem fibreReversePoincare_gaugeRegular_level_two
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : AdalyFormal.Balaban.AlphaAnalyticity.GaugeRegular (1 / (4 * 10 ^ 7)) U)
    (A : Bond L → SuTwo)
    (hker : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0)
    (hdiv : ∀ y : PeriodicLatticeSite L, gradCovariantAdjointValue U A y = 0) :
    bondEnergy A ≤ 497664 * dstarDQuadForm U A := by
  obtain ⟨γ, hγ⟩ := hreg
  have h := AdalyFormal.Balaban.WeitzenbockCovariant.bondEnergy_le_plaqEnergy_level_two_general_U
    (periodicGaugeTransform γ U) hdvd hγ
    (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A)
    (AdalyFormal.Balaban.AlphaAnalyticity.mem_kerQ_gauge γ U 2 A hker)
    (divFree_gauge γ U A hdiv)
  rw [← dstarDQuadForm_eq_plaqEnergy_curl] at h
  rwa [AdalyFormal.Balaban.AlphaAnalyticity.bondEnergy_gauge,
    AdalyFormal.Balaban.AlphaAnalyticity.dstarDQuadForm_gauge] at h

#print axioms fibreReversePoincare_gaugeRegular_level_two

/-- The same, phrased on the `[]` fibre — literally §4 with its hypothesis weakened. -/
theorem fibreReversePoincare_nil_gaugeRegular_level_two
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L))).HasOrthogonalProjection]
    (hreg : AdalyFormal.Balaban.AlphaAnalyticity.GaugeRegular (1 / (4 * 10 ^ 7)) U)
    (v : Bond L → SuTwo)
    (hv : v ∈ gaugeConstraintSubspaceCovFaithful 2
        ([] : List (AdalyFormal.Balaban.KernelSubspace.Level L)) U) :
    bondEnergy v ≤ 497664 * dstarDQuadForm U v := by
  obtain ⟨hker, hdiv⟩ := (mem_fibre_nil_iff U v).mp hv
  exact fibreReversePoincare_gaugeRegular_level_two hdvd U hreg v hker hdiv

#print axioms fibreReversePoincare_nil_gaugeRegular_level_two

/-! ### §8a — what does NOT transport, measured rather than asserted

§7's annihilation does NOT transport to `GaugeRegular` by the same move, and the reason is
structural, not a missing lemma. The gauge action rotates the curl PLAQUETTE-WISE, by
`R(γ(p₀))` with `p₀` the
plaquette's base site (`AlphaAnalyticity.curlValueCovariant_gauge`), whereas the dual witness
`stokesU ell y hlt w` is the SAME algebra element `w` at every plaquette of the window (scaled by an
integer multiplicity). So `⟪stokesU w, D_{U^γ} A^γ⟫ ≠ ⟪stokesU w, D_U A⟫` in general: `stokesU` is
not gauge covariant, and `dstarDQuadForm`'s invariance (which needs only `‖R(g)X‖ = ‖X‖`) does not
help a one-sided pairing. What WOULD transport is the pairing against the ROTATED witness
`p ↦ R(γ(p₀)) (stokesU ell y hlt w p)`, a different (non-`stokesU`) dual witness; building it
and re-running §5/§7 through it is not done here. §4/§8 — the DENOMINATOR — is where the gauge gain
lands.

~~`Weitzenbock.twoExt = fun _ => 1` also means `fibre_nil_level_two_nonvacuous`'s witness does not
meet `FibreReversePoincareNilAtLevel`'s `4 ≤ L μ` clause; a witness at an extent with `L μ` odd
and `≥ 5` (e.g. `ScaleInduction.sawExt 0`, `L μ = 7`) would need a nonzero divergence-free element
of `ker Q₂(1)` there, i.e. `Weitzenbock.nvField`'s three supporting lemmas re-proved at general
compatible extent. Not built here.~~

**SUPERSEDED in the same pass (S75, struck above, retained verbatim).** The `4 ≤ L μ` clause was
copied from `ScaleInduction`'s predicate and is NOT used by §4's proof, so it was DROPPED from
`FibreReversePoincareNilAtLevel` — a strengthening, never a weakening (L5). The predicate is now
non-vacuous at `twoExt` (`fibreReversePoincareNilAtLevel_two_nonvacuous`), and the clause-for-clause
form survives as the corollary `fibreReversePoincareNilAtLevel_two_restricted`. What remains NOT
built, stated as a fact: a nonzero divergence-free element of `ker Q₂(1)` at an extent with
`L μ ≥ 4`. The obstruction is measured — every `coordField μ ν h w` with `ν ≠ μ` is divergence-free
at `U = 1` for free, but its `ker Q₂` clause needs `∑_{x ∈ blockOf y 2} h (x ν) = 0`, a CROSS-BLOCK
sum; the tree's two existing instances (`Weitzenbock.nvField` on `twoExt`,
`CoarseCurlScaleTwo.SAW` on `sawExt q` at level `8q+8`) both dodge it because there the block IS the
whole torus, and no `blockOf`-product-decomposition lemma exists anywhere in the tree to do the
general case. -/

end AdalyFormal.Balaban.StokesCommU
