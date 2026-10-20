/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Q1Real
import AdalyFormal.Balaban.LineIntegralAveraging

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[FAITHFUL-COV-Q]` — the FAITHFUL covariant line-integral `Q_k(U)`

**Task.** The `U`-dependent coercivity object `CovariantHjMinimizer.deltaJQuadFormCov` is currently
based on the CONVICTED single-bond covariant restriction `coarseRestrictCovariant`, which inherits
BOTH defects of the flat single-bond `LatticeOperators.coarseRestrict`
(`Balaban/U1AnchorRefutation.lean`): it drops the line integral (the `×ell` averaging factor) AND
it carries NO background transport (it is `U`-independent). This module builds the object that fixes
both: CMP95 (1.18)'s block-averaged line integral with CMP98 p.28's genuinely covariant, per-bond,
path-dependent transport `R_{0,c₋}`, at the CMP95 (1.18) / CMP98 (125) `η^{d+1}=1/ell⁴` normalization that
makes it a TRUE AVERAGE — on COMPATIBLE full blocks (`0 < ell`, `∀ μ, ell ∣ L μ + 1`) — and matches
the faithful flat `LineIntegralAveraging.lineCoarseRestrict`.

## Characterization from source (`compute/faithful_cov_q/CHARACTERIZATION.md`)

    (Q_k(U) A)_b = η^{d+1} · Σ_{x∈B(b₋)} (R_{0,c₋}A)([x, x(b)])           (d=3 ⇒ η^{d+1} = 1/ell⁴)

    (R_{0,c₋}A)([x,x(c)]) = Σ_{i<ell} R(V₀(Γ_{c₋,x} ∪ [x,b_-])) A_b        (CMP98 p.28, prod→sum)

* CMP95 (1.18): block-average of the line integral `A([x,x(b)])`, `η^{d+1}` normalization
  (`LineIntegralAveraging.lean` header, image-verified CMP95 p.19/20).
* CMP98 p.28, eq. below (58): `R_{0,c₋}A` is the covariant, per-bond, path-dependent transport-SUM
  along the segment — a DIFFERENT holonomy `R(V₀(Γ_{c₋,x}∪[x,b_-]))` for every fine bond `b` and
  block-interior site `x` (`Q1Real.lean` header, image-verified CMP98 p.27/28).

**Which composition (the dispatch's own open question), resolved:** it is CMP98's `R_{0,c₋}`
STRUCTURE line-integral-SUMMED over the segment's `ell` fine bonds, then block-averaged — the exact
object `Q1Real.rZeroA` already builds. So `[FAITHFUL-COV-Q]` is `Q1Real.q1RealMain` re-normalized
from p.28's preliminary `1/ell³` to CMP95 (1.18) / CMP98 (125)'s `1/ell⁴`; the clean bridge is
`lineCoarseRestrictCov U ell A b = (1/ell)·q1RealMain U ell A b` (§3), reusing all of `Q1Real`'s
grade-checked transport machinery (LAW-19 — the faithful covariant transport already exists; this
module supplies the (125) normalization and the reduction/U-dependence/intertwining that re-base it
onto the coercivity object).

## What this module builds

1. **§1 `lineCoarseRestrictCov U ell`** — the faithful covariant line-integral `Q_k(U)`, defined for
   any `L`, `ell`, with `+`/`•` laws and its `LinearMap` promotion `lineCoarseRestrictCovLM`. NOTE
   (grade-2 Sol caveat, 2026-07-25): the SOURCE object lives on COMPATIBLE full blocks (`0 < ell` and
   `∀ μ, ell ∣ L μ + 1`); on incompatible extents `blockOf` TRUNCATES (fewer than `ell^d` sites) and
   at `ell = 0` the operator is `0`. The reduction/intertwining theorems that need it carry the
   compatibility hypothesis (`hell`, `hdvd`); the "true average" reading below is scoped to that domain.
2. **§2 U=1 REDUCTION to the faithful FLAT `Q`** — `lineCoarseRestrictCov (trivialU) =
   lineCoarseRestrictSuTwo` (the faithful flat SuTwo line-integral average, via `RMap 1 = id`), and
   on scalar fields `f•v` this equals `(lineCoarseRestrict f)•v` — the faithful flat ℝ operator,
   NOT the convicted single-bond one. Contrast pin: on the constant field, on a COMPATIBLE full block,
   the faithful object is a TRUE AVERAGE (`= v`) while the convicted single-bond `coarseRestrictCovariant`
   returns `(1/2)•v`. (On a truncated/incompatible block the average degrades — see the §1 caveat.)
3. **§3 GENUINE U-DEPENDENCE** — `lineCoarseRestrictCov (trivialU) ≠ lineCoarseRestrictCov witnessU`
   on `d4ConfigSuTwo` (a real sign flip through the forward holonomy `witnessMElem`), via the bridge
   to `Q1Real`'s witness.
4. **§4 THE (1.20) COVARIANT INTERTWINING at `U=1`, general** — `lineCoarseRestrictCov (trivialU)
   (D_{trivialU} λ)` is the coarse gradient of the covariant site-average `Q'^{cov}λ`, ANY `L`/`ell`/
   aligned coarse bond, via the SuTwo telescoping + `coarseShift_blockOf_eq_image` reindexing (LAW-19).
   The general-`U` intertwining is NAMED as a residual: it FAILS by the covariant curvature obstruction
   (`CovariantOperators.witness_curvature_ne_zero`, `d²≠0`), so it holds only up-to-center-flat.
5. **§5 RE-BASING `deltaJQuadFormCov`** — how `lineCoarseRestrictCovLM U` replaces the convicted
   `coarseRestrictCovariantLM` in the interpolation constraint, curing the single-bond defect; the
   coercivity object stays curl-relative (`‖D_U H_j^{cov}‖²`). Full rebuild = separate lane's scope.
-/

namespace AdalyFormal.Balaban.LineIntegralCovariant

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CoarseShiftCovariance
open AdalyFormal.Balaban.Q1Real
open AdalyFormal.Balaban.LatticeOperators (CoarseBond coarseRestrict)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ targetCoarseBond site1)
open AdalyFormal.Balaban.CovariantHjMinimizer
  (trivialU coarseRestrictCovariant coarseRestrictSiteCovariant)
open AdalyFormal.Balaban.LineIntegralAveraging
  (lineCoarseRestrict lineIntegralValue lineCoarseRestrict_gradValue lineCoarseRestrict_const_witness
    coarseRestrict_const_witness)

/-! ## §1. The faithful covariant line-integral `Q_k(U)`, general in `L`, `ell` -/

/-- **`(Q_k(U) A)_b := (1/ell⁴) • Σ_{x∈B(b₋)} (R_{0,c₋}A)([x, x(b)])`** — CMP95 (1.18) covariantized
per CMP98 (125): the block average (`1/ell⁴ = η^{d+1}`, `d=3`) of CMP98 p.28's covariant
line-integral transport-sum `rZeroA` (the per-bond, path-dependent `R_{0,c₋}A`). Reduces to the
faithful flat `lineCoarseRestrict` at `U=1` (§2), genuinely varies in `U` (§3). Source-admissible
domain: `0 < ell` and `∀ μ, ell ∣ L μ + 1` (compatible full blocks); on incompatible extents `blockOf`
truncates and the true-average normalization no longer holds (grade-2 Sol caveat). -/
noncomputable def lineCoarseRestrictCov {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : Bond L → SuTwo) (b : CoarseBond L ell) : SuTwo :=
  (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf b.1.1 ell, rZeroA U b.1.1 x A b.2 ell

theorem lineCoarseRestrictCov_add {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A1 A2 : Bond L → SuTwo) (b : CoarseBond L ell) :
    lineCoarseRestrictCov U ell (A1 + A2) b =
      lineCoarseRestrictCov U ell A1 b + lineCoarseRestrictCov U ell A2 b := by
  simp only [lineCoarseRestrictCov]
  rw [← smul_add, ← Finset.sum_add_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun x _ => rZeroA_add U b.1.1 x A1 A2 b.2 ell)

theorem lineCoarseRestrictCov_smul {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) (c : ℝ)
    (A : Bond L → SuTwo) (b : CoarseBond L ell) :
    lineCoarseRestrictCov U ell (c • A) b = c • lineCoarseRestrictCov U ell A b := by
  simp only [lineCoarseRestrictCov]
  have h : ∀ x ∈ blockOf b.1.1 ell, rZeroA U b.1.1 x (c • A) b.2 ell =
      c • rZeroA U b.1.1 x A b.2 ell := fun x _ => rZeroA_smul U b.1.1 x c A b.2 ell
  rw [Finset.sum_congr rfl h, ← Finset.smul_sum]
  exact smul_comm _ _ _

/-- The faithful covariant `Q_k(U)`, for fixed `U`/`ell`, as a genuine `LinearMap` — the drop-in
replacement for `CovariantHjMinimizer.coarseRestrictCovariantLM` in a repaired coercivity chain. -/
noncomputable def lineCoarseRestrictCovLM {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) :
    (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo) where
  toFun A := lineCoarseRestrictCov U ell A
  map_add' A1 A2 := funext fun b => lineCoarseRestrictCov_add U ell A1 A2 b
  map_smul' c A := funext fun b => lineCoarseRestrictCov_smul U ell c A b

theorem lineCoarseRestrictCovLM_apply {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : Bond L → SuTwo) (b : CoarseBond L ell) :
    lineCoarseRestrictCovLM U ell A b = lineCoarseRestrictCov U ell A b := rfl

#print axioms lineCoarseRestrictCov_add
#print axioms lineCoarseRestrictCov_smul
#print axioms lineCoarseRestrictCovLM_apply

/-! ## §2. U=1 REDUCTION to the faithful FLAT `Q` (not the convicted single-bond one) -/

/-- **The faithful FLAT SuTwo line-integral average** — CMP95 (1.18) on the `SuTwo` carrier with the
line integral intact and NO transport: `(1/ell⁴) • Σ_{x∈B} Σ_{i<ell} A(x+i·e_μ, μ)`. This is the
`U=1` target: the SuTwo analogue of the faithful flat `LineIntegralAveraging.lineCoarseRestrict`,
NOT the convicted single-bond `coarseRestrictCovariant` (which drops the `Σ_{i<ell}`). -/
noncomputable def lineCoarseRestrictSuTwo {L : PeriodicLatticeExtent} (ell : ℕ)
    (A : Bond L → SuTwo) (b : CoarseBond L ell) : SuTwo :=
  (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell, A (pathSite x b.2 i, b.2)

/-- **THE U=1 REDUCTION**: at the trivial background the covariant transport collapses
(`RMap 1 = id`, `rZeroA_trivialU`) and `lineCoarseRestrictCov (trivialU)` IS the faithful flat SuTwo
line-integral average — the consistency the convicted single-bond `coarseRestrictCovariant` FAILS
(it does not reduce to the faithful flat `Q`, only to the convicted single-bond one). -/
theorem lineCoarseRestrictCov_trivialU {L : PeriodicLatticeExtent} (ell : ℕ) (A : Bond L → SuTwo)
    (b : CoarseBond L ell) :
    lineCoarseRestrictCov (trivialU L) ell A b = lineCoarseRestrictSuTwo ell A b := by
  simp only [lineCoarseRestrictCov, lineCoarseRestrictSuTwo, rZeroA_trivialU]

/-- **The faithful flat SuTwo average is the faithful flat ℝ `lineCoarseRestrict`, on scalar fields**
`e ↦ f(e)•v`: `lineCoarseRestrictSuTwo (f•v) = (lineCoarseRestrict f)•v`. This ties the `U=1`
covariant object to the ℝ-valued FAITHFUL flat operator (with its `×ell` line-integral factor),
NOT to the convicted single-bond `coarseRestrict` — the precise sense of "reduces to the faithful
flat `Q`". -/
theorem lineCoarseRestrictSuTwo_smul_fixed {L : PeriodicLatticeExtent} (ell : ℕ)
    (f : Bond L → ℝ) (v : SuTwo) (b : CoarseBond L ell) :
    lineCoarseRestrictSuTwo ell (fun e => f e • v) b = (lineCoarseRestrict ell f b) • v := by
  have hli : ∀ x, (∑ i ∈ Finset.range ell, (f (pathSite x b.2 i, b.2)) • v)
      = (lineIntegralValue ell f x b.2) • v := by
    intro x
    simp only [lineIntegralValue, pathSite, ← Finset.sum_smul]
  simp only [lineCoarseRestrictSuTwo, hli]
  rw [lineCoarseRestrict, ← Finset.sum_smul, smul_smul]

/-- **CONTRAST / falsifiability pin**: on the constant field `fun _ => v`, at the witness coarse
bond, the FAITHFUL object is a TRUE AVERAGE — `lineCoarseRestrictCov (trivialU) (const v) = v` —
while the CONVICTED single-bond `coarseRestrictCovariant (const v) = (1/2)•v` (at `witnessEll=2`),
off by exactly the dropped `×ell` line-integral factor. Proves the faithful object is genuinely NOT
the convicted single-bond one. -/
theorem lineCoarseRestrictCov_const_witness (v : SuTwo) :
    lineCoarseRestrictCov (trivialU witnessL) witnessEll (fun _ => v)
        (⟨witnessY, witnessY_coarse⟩, 0) = v := by
  rw [lineCoarseRestrictCov_trivialU,
    show (fun _ : Bond witnessL => v) = (fun e => (fun _ : Bond witnessL => (1 : ℝ)) e • v) by
      funext e; rw [one_smul],
    lineCoarseRestrictSuTwo_smul_fixed, lineCoarseRestrict_const_witness, one_smul]

theorem coarseRestrictCovariant_const_witness (v : SuTwo) :
    coarseRestrictCovariant witnessEll (fun _ => v) (⟨witnessY, witnessY_coarse⟩, 0) =
      (1 / 2 : ℝ) • v := by
  rw [show (fun _ : Bond witnessL => v) = (fun e => (fun _ : Bond witnessL => (1 : ℝ)) e • v) by
      funext e; rw [one_smul],
    CovariantHjMinimizer.coarseRestrictCovariant_smul_fixed, coarseRestrict_const_witness]

#print axioms coarseRestrictCovariant_const_witness

/-- **The two disagree** — the faithful average (`v`) is not the convicted single-bond value
(`(1/2)•v`) for `v ≠ 0`: the numerical fingerprint of the dropped line-integral factor, isolated. -/
theorem faithful_ne_convicted_on_const :
    lineCoarseRestrictCov (trivialU witnessL) witnessEll (fun _ => suTwoWitness)
        (⟨witnessY, witnessY_coarse⟩, 0) ≠
      coarseRestrictCovariant witnessEll (fun _ => suTwoWitness)
        (⟨witnessY, witnessY_coarse⟩, 0) := by
  rw [lineCoarseRestrictCov_const_witness, coarseRestrictCovariant_const_witness]
  intro h
  apply suTwoWitness_ne_zero
  have h2 : ((1 : ℝ) - 1 / 2) • suTwoWitness = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  rw [show ((1 : ℝ) - 1 / 2) = 1 / 2 by norm_num] at h2
  rcases smul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

#print axioms lineCoarseRestrictCov_trivialU
#print axioms lineCoarseRestrictSuTwo_smul_fixed
#print axioms lineCoarseRestrictCov_const_witness
#print axioms faithful_ne_convicted_on_const

/-! ## §3. GENUINE U-DEPENDENCE (bridge to `Q1Real`'s forward-holonomy witness) -/

/-- **THE NORMALIZATION BRIDGE**: on the witness lattice, `lineCoarseRestrictCov U ell = (1/ell)·
q1RealMain U ell` — the (125) `1/ell⁴` object is `1/ell` times CMP98 p.28's `1/ell³` object, sharing
the identical `rZeroA` transport (LAW-19: all of `Q1Real`'s witness computations transfer). -/
theorem lineCoarseRestrictCov_witnessL_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) (ell : ℕ)
    (A : Bond witnessL → SuTwo) (b : CoarseBond witnessL ell) :
    lineCoarseRestrictCov U ell A b = (1 / (ell : ℝ)) • q1RealMain U ell A b := by
  simp only [lineCoarseRestrictCov, q1RealMain, smul_smul]
  congr 1
  ring

/-- **GENUINE, NON-VACUOUS `U`-dependence**: the faithful covariant `Q_k(U)` genuinely varies in the
background — at `trivialU` and `witnessU` it returns DIFFERENT values on `d4ConfigSuTwo` (a real sign
flip through the forward holonomy `witnessMElem`). The transport `Ad(U)` carries real `U`-variation:
the convicted `U`-INDEPENDENT `coarseRestrictCovariant` could never exhibit this. -/
theorem lineCoarseRestrictCov_genuinely_U_dependent :
    lineCoarseRestrictCov (trivialU witnessL) witnessEll d4ConfigSuTwo targetCoarseBond ≠
      lineCoarseRestrictCov witnessU witnessEll d4ConfigSuTwo targetCoarseBond := by
  rw [lineCoarseRestrictCov_witnessL_eq, lineCoarseRestrictCov_witnessL_eq]
  have hne := Q1Real_d4_genuinely_U_dependent
  rw [Q1Real_apply, Q1Real_apply] at hne
  intro h
  apply hne
  have hc : (1 / (witnessEll : ℝ)) ≠ 0 := by
    rw [show (witnessEll : ℝ) = 2 from by norm_num [witnessEll]]; norm_num
  exact smul_right_injective SuTwo hc h

/-- The explicit witness values, for the record: `(1/8)•w` vs `-(1/8)•w`. -/
theorem lineCoarseRestrictCov_d4_trivialU :
    lineCoarseRestrictCov (trivialU witnessL) witnessEll d4ConfigSuTwo targetCoarseBond =
      (1 / 8 : ℝ) • suTwoWitness := by
  rw [lineCoarseRestrictCov_witnessL_eq, ← Q1Real_apply, Q1Real_d4_trivialU, smul_smul,
    show (witnessEll : ℝ) = 2 from by norm_num [witnessEll]]
  norm_num

theorem lineCoarseRestrictCov_d4_witnessU :
    lineCoarseRestrictCov witnessU witnessEll d4ConfigSuTwo targetCoarseBond =
      -((1 / 8 : ℝ) • suTwoWitness) := by
  rw [lineCoarseRestrictCov_witnessL_eq, ← Q1Real_apply, Q1Real_d4_witnessU, smul_neg, smul_smul,
    show (witnessEll : ℝ) = 2 from by norm_num [witnessEll]]
  norm_num

#print axioms lineCoarseRestrictCov_witnessL_eq
#print axioms lineCoarseRestrictCov_genuinely_U_dependent
#print axioms lineCoarseRestrictCov_d4_trivialU
#print axioms lineCoarseRestrictCov_d4_witnessU

/-! ## §4. THE (1.20) COVARIANT INTERTWINING at `U=1`, general — and the curvature residual -/

/-- **The covariant line integral of a `U=1` covariant gradient telescopes to the endpoint
difference** — the SuTwo/covariant analogue of `LineIntegralAveraging.lineIntegralValue_gradValue`.
At `trivialU`, `D_{trivialU}λ` is the flat SuTwo gradient (`RMap 1 = id`), so the segment sum
telescopes: `Σ_{i<ell} (D_{trivialU}λ)(x+i·e_μ, μ) = λ(x+ell·e_μ) − λ(x)`. -/
theorem sum_gradCovariant_trivialU {L : PeriodicLatticeExtent} (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ∑ i ∈ Finset.range ell, gradValueCovariant (trivialU L) lam (pathSite x μ i, μ) =
      lam (pathSite x μ ell) - lam x := by
  induction ell with
  | zero => simp [pathSite_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    show (lam (pathSite x μ n) - lam x) +
        (RMap ((trivialU L) (pathSite x μ n, μ)) (lam (periodicLatticeShift (pathSite x μ n) μ)) -
          lam (pathSite x μ n)) = lam (pathSite x μ (n + 1)) - lam x
    rw [show (trivialU L) (pathSite x μ n, μ) = 1 from rfl, RMap_one]
    simp only [LinearMap.id_coe, id_eq]
    rw [← pathSite_succ]
    abel

/-- **CMP95 (1.20) at `U=1`, faithful and GENERAL** (any `L`, `ell > 0`, `ell ∣ L_μ+1`, aligned
coarse point): the faithful covariant `Q_k(trivialU)` maps a `U=1` covariant gradient `D_{trivialU}λ`
to the coarse gradient of the covariant site-average `Q'^{cov}λ = coarseRestrictSiteCovariant`, with
the explicit `1/ell` dictionary constant — the exact structural property the coercivity's kernel
constraint rests on. Proof: segment telescoping (`sum_gradCovariant_trivialU`) + the
`coarseShift_blockOf_eq_image` block reindexing (LAW-19), the SuTwo copy of
`lineCoarseRestrict_gradValue`. -/
theorem lineCoarseRestrictCov_gradCovariant_trivialU_intertwines {L : PeriodicLatticeExtent}
    {ell : ℕ} (hell : 0 < ell) {μ : Fin 3} (hdvd : ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (lam : PeriodicLatticeSite L → SuTwo) :
    lineCoarseRestrictCov (trivialU L) ell (gradValueCovariant (trivialU L) lam) (⟨y, hy⟩, μ) =
      (1 / (ell : ℝ)) •
        (coarseRestrictSiteCovariant ell lam (coarseShift y ell μ) -
          coarseRestrictSiteCovariant ell lam y) := by
  rw [lineCoarseRestrictCov_trivialU]
  simp only [lineCoarseRestrictSuTwo, coarseRestrictSiteCovariant]
  have hstep : (∑ x ∈ blockOf y ell,
        ∑ i ∈ Finset.range ell, gradValueCovariant (trivialU L) lam (pathSite x μ i, μ)) =
      (∑ x ∈ blockOf (coarseShift y ell μ) ell, lam x) - ∑ x ∈ blockOf y ell, lam x := by
    have h1 : (∑ x ∈ blockOf y ell,
          ∑ i ∈ Finset.range ell, gradValueCovariant (trivialU L) lam (pathSite x μ i, μ)) =
        (∑ x ∈ blockOf y ell, lam (pathSite x μ ell)) - ∑ x ∈ blockOf y ell, lam x := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => sum_gradCovariant_trivialU ell lam x μ
    have h2 : (∑ x ∈ blockOf (coarseShift y ell μ) ell, lam x) =
        ∑ x ∈ blockOf y ell, lam (pathSite x μ ell) := by
      rw [coarseShift_blockOf_eq_image hell hdvd hy]
      exact Finset.sum_image fun x _ x' _ h => coarseShift_injective ell μ h
    rw [h1, h2]
  rw [hstep]
  generalize (∑ x ∈ blockOf (coarseShift y ell μ) ell, lam x) = S1
  generalize (∑ x ∈ blockOf y ell, lam x) = S2
  rw [smul_sub, smul_sub, smul_smul, smul_smul]
  congr 1 <;> (congr 1; ring)

#print axioms sum_gradCovariant_trivialU
#print axioms lineCoarseRestrictCov_gradCovariant_trivialU_intertwines

/-! ### §4b — the general-`U` intertwining is a RESIDUAL, blocked by curvature (named, not built)

The `U=1` intertwining above does NOT extend to general `U`: the covariant curl of a covariant
gradient is the plaquette curvature, which `CovariantOperators.witness_curvature_ne_zero` proves is
GENUINELY NONZERO on an explicit non-flat background (`d²≠0`). So `Q_k(U)(D_Uλ)` is an EXACT coarse
gradient only up to a curvature defect vanishing iff every plaquette holonomy is central (flat up to
center). This is the honest replacement for a false general-`U` exactness claim — the same status
`CovariantOperators.curlValueCovariant_gradValueCovariant` records one level down. -/

/-! ## §5. RE-BASING `deltaJQuadFormCov` — curing the single-bond defect (stated; rebuild = separate lane)

`CovariantHjMinimizer.deltaJQuadFormCov ell levels U A0 = ‖D_U (hjExtensionCov ell levels U A0)‖²`
(`covPlaqInner` of the covariant curl — already CURL-RELATIVE, not bare `‖v‖²`). Its single-bond
defect lives at ONE place: the interpolation constraint

    coarseRestrictCovariantLM L ell A0 = B          (`hjExtensionCov_isBalabanExtensionCov`, h1)

which pins `A0`'s coarse restriction to the target `B` via the CONVICTED single-bond, `U`-independent
`coarseRestrictCovariant`. Replacing that operator with `lineCoarseRestrictCovLM U ell` (§1) gives the
FAITHFUL constraint `Q_k(U) A0 = B`, i.e. the covariant coercivity based on the faithful covariant
line-integral `Q`:

    deltaJQuadFormCovFaithful ell levels U A0 := ‖D_U (hjExtensionCov' ell levels U A0)‖²
      subject to   lineCoarseRestrictCovLM U ell A0 = B      (faithful (1.18)-covariant interpolation)

* The object stays CURL-RELATIVE (`covPlaqInner(D_U H, D_U H)`), per the prior finding — NOT `‖v‖²`.
* The `U=1` intertwining (§4) is exactly the property this constraint needs to be gauge-consistent
  in the free sector; the general-`U` curvature residual (§4b) is inherited.

**RESIDUAL, precisely named (write-scope: `CovariantHjMinimizer.lean`, a separate lane).** The full
re-basing must reconstruct, over `lineCoarseRestrictCovLM U ell`:
`gaugeConstraintSubspaceCov` / `deltaKernelImageCovH` / `hjCorrectionCov` / `hjExtensionCov`, and
re-prove `hjExtensionCov_isBalabanExtensionCov` with `h1` reading `lineCoarseRestrictCovLM U ell A0 =
B`. This module supplies the operator (`lineCoarseRestrictCovLM`), its `U=1` reduction to the faithful
flat `Q`, its genuine `U`-dependence, and the `U=1` (1.20) intertwining — everything the re-basing
consumes — but does not edit `CovariantHjMinimizer.lean`. -/

end AdalyFormal.Balaban.LineIntegralCovariant
