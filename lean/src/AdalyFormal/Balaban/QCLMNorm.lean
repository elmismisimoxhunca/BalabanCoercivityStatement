/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BridgeInverseControls
import AdalyFormal.Balaban.NormRMapClean
import AdalyFormal.Balaban.QcEquation

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.longLine false

/-!
# `QCLMNorm.lean` — THE NUMBER. `‖qCLM U ell‖` is bounded on BOTH sides, and it is `< 1`.

`GammaRecursion.curvedRegularU_Q_decides_uniformity` reduced p.428's `k`-uniform `γ₀`, along the
tree's iterated-bridge route, to the position of ONE real relative to `1`:
`‖BridgeInverse.qCLM CoercivityRegular.curvedRegularU 2‖`. Nothing in the tree bounded it against
`1` in either direction (`BridgeInverse.qCLM_norm_pos` gives only `0 <`).

This module computes it, two-sidedly:

    ell⁻⁴  ≤  ‖qCLM U ell‖  ≤  ell^(-3/2)      (any `U`, any compatible `ell`)

so at the parameters that matter — `curvedRegularU`, `ell = 2`, `witL5` — the number is
`≤ √(1/8) = 0.3535…` and `≥ 1/16 = 0.0625`. **It is `< 1`.** The `q ≥ 1` no-go
(`GammaRecursion.not_uniformStepGamma_of_one_le`) therefore does NOT fire on this route; the branch
that fires is `GammaRecursion.uniformStepGamma_of_lt_one`, i.e. along the tree's own `Q` the bridge
iterate does not decay — it grows.

## Why, in one line: `qCLM` is a normalised AVERAGE, not a block SUM

`LineIntegralCovariant.lineCoarseRestrictCov` is
`(1/ell⁴) • ∑_{x ∈ blockOf y ell} rZeroA U y x A μ ell`, and `Q1Real.rZeroA` is a sum over
`i ∈ range ell`. With `card_blockOf_of_coarse` the inner sum has `ell³ · ell = ell⁴` terms carrying
weight `ell⁻⁴` each: a TRUE average. `GammaRecursion` §7 had already proved the abstract dichotomy —
a block-SUMMING coarse-graining forces `1 < q` (`summing_forces_one_lt_q`), one divided by the block
volume admits `q < 1` (`quarterProjSumTwo_bound`). This module places the tree's ACTUAL `Q` on the
second side, with a number.

**Uniform-rescale test, run and shipped as a theorem** (`summing_variant_not_lt_one`): multiply
`qCLM` by `ell⁴` — i.e. delete exactly the `(1/ell⁴)` normalisation and nothing else — and the
conclusion `‖·‖ < 1` becomes FALSE (`1 ≤ ‖(ell⁴ : ℝ) • qCLM U ell‖`). The strict inequality is
carried by that prefactor alone.

## The estimate, and where each factor comes from

Write `c = (y, μ)`, `S_c = blockOf y ell ×ˢ range ell` (`blockIdx`), `φ_c(x,i) = (pathSite x μ i, μ)`
(`fineBond`).

1. `RMap` is an isometry (`FaithfulCoercivitySU2.norm_RMap`) ⟹
   `‖(QA)(c)‖ ≤ ell⁻⁴ · ∑_{t ∈ S_c} ‖A (φ_c t)‖` (`norm_lineCoarseRestrictCov_le`).
2. Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) with `|S_c| = ell⁴` (`card_blockIdx`, from
   `AdmissibleSubspace.card_blockOf_of_coarse`) ⟹
   `‖(QA)(c)‖² ≤ ell⁻⁴ · ∑_{t ∈ S_c} ‖A (φ_c t)‖²` (`norm_sq_lineCoarseRestrictCov_le`).
3. **Multiplicity `≤ ell`** (`sum_coarse_le`): for each FIXED `i`, the map `(c, x) ↦ (pathSite x μ i, μ)`
   is injective on `{(c,x) : x ∈ blockOf c.1.1 ell}`, because the owning coarse site is unique
   (`AdmissibleSubspace.coarseLattice_unique`, which needs `hdvd`) and `pathSite · μ i` is injective
   (`pathSite_injective`). Summing over the `ell` values of `i` costs a factor `ell` and no more.
4. `‖QA‖² ≤ ell⁻⁴ · ell · ‖A‖² = ell⁻³‖A‖²` (`qCLM_norm_sq_le`), hence `‖qCLM U ell‖ ≤ √(ell⁻³)`.

The lower bound is independent: a single-fine-bond field (`BridgeInverse.bondDelta`) is read by
exactly one `(x,i)` pair (`BridgeInverse.pathSite_eq_base_iff`, which needs `hwide`), giving
`(QA)(c₀) = ell⁻⁴ • R(·)v` and hence `ell⁻⁴ ≤ ‖qCLM U ell‖`.

## Non-vacuity

`qCLM_two_sided_curvedRegularU` exhibits both bounds at `curvedRegularU`, `ell = 2`, `witL5`, and
`two_sided_consistent` checks the two INDEPENDENTLY-derived numbers do not contradict
(`1/16 ≤ √(1/8)`). `bound_is_not_zero` records that the upper bound is not the trivial one that a
zero operator would satisfy. The `ell = 1` degenerate case is quarantined explicitly
(`opNorm_bound_at_one_is_one`): there the method yields exactly `≤ 1`, no strict inequality, which is
correct — at `ell = 1` the block is a single site and `Q` transports without averaging.

## PRIOR ART IN THIS TREE, found by the reuse grep and disclosed (LAW-19)

The identical constant `√(ell⁻³)` was ALREADY proved in `Balaban/QcEquation.lean`
(`qcOp_opNorm_le_sqrt`, via `qcOp_norm_sq_le` and `read_sum_eq`) — **for a different operator**:
`qcOp L ell : BondSpace L →L[ℝ] CoarseBondSpace L ell` is `lineCoarseRestrictCLM`, the FLAT,
ℝ-VALUED, `U`-INDEPENDENT line-integral average. `qCLM U ell` is the 𝔰𝔲(2)-valued COVARIANT one,
with `Q1Real.rZeroA`'s per-bond path-dependent transport inside the sum; it is the operator
`GammaRecursion` quantifies over and the one the bridge instantiates. The transport is exactly what
prevented the scalar result from transferring: it is removed only by `norm_RMap`, after which a
scalar-shaped sum remains.

`sum_coarse_le` is therefore a SECOND, independently-routed derivation of the same multiplicity
count as `QcEquation.read_sum_eq` (mine: image-of-an-injective-map, for any nonnegative bond weight;
theirs: `PoincareBridge.sum_eq_blocks` + `pathStep_bijective`, an EQUALITY for squares).
`multiplicity_exact` below imports theirs and proves the two agree — so the reuse miss is converted
into a de-correlated cross-check rather than hidden, and it shows my `≤ ell` is EXACTLY `ell`,
i.e. not lossy. `QcEquation.pathStep` is definitionally `QOne.pathSite` (that module says so itself).

`FullySupplied.opNorm_qc_le_one` is the other neighbour: `‖𝒬_c‖ ≤ 1` at `U = 1` in the SUP-norm
class on `FullySupplied.CoarseField`. It is neither the `L²` carrier nor a strict inequality, so it
does not decide the question either.

## What this does NOT claim

It says nothing about whether the UNWEIGHTED `PiLp 2` carriers (`CovariantOperators.BondFnL2`,
`BridgeInverse.CoarseFnL2`) are the source's carriers. CMP99b (3.16) p.393 carries a per-level
measure factor `(L^jη)^{d−2}` which this tree's carriers do not; `GammaRecursion` §5 records that
measurement. A different carrier weight would change this number. What is established here is the
number FOR THE OPERATOR THE TREE ACTUALLY BUILT, which is what
`GammaRecursion.curvedRegularU_Q_decides_uniformity` quantifies over.

`GammaRecursion` is NOT imported: its `.olean` does not exist in this checkout and building it would
write into the shared `.lake/build` that three live lanes are using. The two theorems below are
stated in exactly the shape that module's hypotheses consume (`1 < ‖qCLM …‖` / `‖qCLM …‖ < 1`), so
the composition is a one-liner once that `.olean` exists.
-/

namespace AdalyFormal.Balaban.QCLMNorm

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration
  PeriodicLatticeSite periodicPathHolonomy periodicLatticeShift)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice
  mem_CoarseLattice coarseLattice_unique card_blockOf_of_coarse)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictSuTwo
  lineCoarseRestrictCov_trivialU)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.Q1Real (rZeroA transportPath)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero)
open AdalyFormal.Balaban.BridgeInverse (qCLM qCLM_apply CoarseFnL2 bondDelta bondDelta_same
  bondDelta_ne rMap_injective pathSite_eq_base_iff siteZeroMem witL5_dvd_two witL5_wide_two)
open AdalyFormal.Balaban.FaithfulCoercivitySU2 (norm_RMap norm_suTwoWitness_sq)
open AdalyFormal.Balaban.CoercivityRegular (curvedRegularU)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the `L²` norm identity on the two carriers -/

/-- `‖x‖² = ∑ ‖x i‖²` on `PiLp 2` over `𝔰𝔲(2)` — both `BondFnL2 L` and `CoarseFnL2 L ell` are of
this shape, so one lemma serves both. -/
theorem norm_sq_pilp {ι : Type} [Fintype ι] (x : PiLp 2 (fun _ : ι => SuTwo)) :
    ‖x‖ ^ 2 = ∑ i : ι, ‖WithLp.ofLp x i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => real_inner_self_eq_norm_sq _

/-- One coordinate is dominated by the whole `L²` norm. -/
theorem norm_coord_le {ι : Type} [Fintype ι] (x : PiLp 2 (fun _ : ι => SuTwo)) (i : ι) :
    ‖WithLp.ofLp x i‖ ≤ ‖x‖ := by
  have hsum : ‖WithLp.ofLp x i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_pilp]
    exact Finset.single_le_sum (f := fun j : ι => ‖WithLp.ofLp x j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h := Real.sqrt_le_sqrt hsum
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-! ## §2 — the index set of the block average, and the fine bond each index reads -/

/-- The `(x, i)` pairs the block average at a coarse bond sums over: `blockOf y ell × range ell`. -/
def blockIdx (y : PeriodicLatticeSite L) (ell : ℕ) : Finset (PeriodicLatticeSite L × ℕ) :=
  blockOf y ell ×ˢ Finset.range ell

/-- The fine bond that the pair `(x, i)` reads, in direction `μ`. -/
def fineBond (μ : Fin 3) (t : PeriodicLatticeSite L × ℕ) : Bond L := (pathSite t.1 μ t.2, μ)

/-- `|S_c| = ell⁴` on a `CoarseLattice` centre — `ell³` sites times `ell` steps. This is the count
that makes `(1/ell⁴)` a TRUE average; it needs `hdvd` (else `blockOf` truncates). -/
theorem card_blockIdx {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    (blockIdx y ell).card = ell ^ 4 := by
  rw [blockIdx, Finset.card_product, card_blockOf_of_coarse hdvd hy, Finset.card_range]
  ring

/-- `pathSite · μ i` is injective — the `i`-fold iterate of the injective single step. -/
theorem pathSite_injective (μ : Fin 3) (i : ℕ) :
    Function.Injective (fun x : PeriodicLatticeSite L => pathSite x μ i) := by
  have h : (fun x : PeriodicLatticeSite L => pathSite x μ i)
      = (fun y : PeriodicLatticeSite L => periodicLatticeShift y μ)^[i] := by
    funext x; rfl
  rw [h]
  exact Function.Injective.iterate
    (AdalyFormal.Balaban.CoarseCurl.periodicLatticeShift_injective μ) i

/-! ## §3 — the pointwise `ℓ¹` bound (isometry of `RMap` is the whole content) -/

theorem norm_lineCoarseRestrictCov_le {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (c : CoarseBond L ell) :
    ‖lineCoarseRestrictCov U ell A c‖
      ≤ (1 / (ell : ℝ) ^ 4) * ∑ t ∈ blockIdx c.1.1 ell, ‖A (fineBond c.2 t)‖ := by
  have hk : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 4 := by positivity
  simp only [lineCoarseRestrictCov]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk]
  refine mul_le_mul_of_nonneg_left ?_ hk
  calc ‖∑ x ∈ blockOf c.1.1 ell, rZeroA U c.1.1 x A c.2 ell‖
      ≤ ∑ x ∈ blockOf c.1.1 ell, ‖rZeroA U c.1.1 x A c.2 ell‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ blockOf c.1.1 ell, ∑ i ∈ Finset.range ell, ‖A (pathSite x c.2 i, c.2)‖ := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [rZeroA]
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
        exact norm_RMap _ _
    _ = ∑ t ∈ blockIdx c.1.1 ell, ‖A (fineBond c.2 t)‖ := by
        simp only [blockIdx, fineBond, Finset.sum_product]

/-! ## §4 — Cauchy–Schwarz: the squared pointwise bound -/

theorem norm_sq_lineCoarseRestrictCov_le {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (c : CoarseBond L ell) :
    ‖lineCoarseRestrictCov U ell A c‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) * ∑ t ∈ blockIdx c.1.1 ell, ‖A (fineBond c.2 t)‖ ^ 2 := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hk : (0 : ℝ) < 1 / (ell : ℝ) ^ 4 := by positivity
  set S : ℝ := ∑ t ∈ blockIdx c.1.1 ell, ‖A (fineBond c.2 t)‖ with hS
  set S2 : ℝ := ∑ t ∈ blockIdx c.1.1 ell, ‖A (fineBond c.2 t)‖ ^ 2 with hS2
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h1 := norm_lineCoarseRestrictCov_le U A c
  have hcs : S ^ 2 ≤ (ell : ℝ) ^ 4 * S2 := by
    have hraw := sq_sum_le_card_mul_sum_sq (s := blockIdx c.1.1 ell)
      (f := fun t => ‖A (fineBond c.2 t)‖)
    rw [card_blockIdx hdvd c.1.2] at hraw
    simpa [hS, hS2] using hraw
  have hsq : ‖lineCoarseRestrictCov U ell A c‖ ^ 2 ≤ ((1 / (ell : ℝ) ^ 4) * S) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hexp : ((1 / (ell : ℝ) ^ 4) * S) ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) * S2 := by
    have hkey : ((1 / (ell : ℝ) ^ 4) * S) ^ 2 = (1 / (ell : ℝ) ^ 8) * S ^ 2 := by
      field_simp
    rw [hkey]
    have hmul := mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 1 / (ell : ℝ) ^ 8)
    refine hmul.trans (le_of_eq ?_)
    field_simp
  exact hsq.trans hexp

/-! ## §5 — MULTIPLICITY: every fine bond is read at most `ell` times, in total, by all coarse bonds

This is the combinatorial heart. The previous lane recorded that a sharp norm would need a
`blockOf` staircase multiplicity that "does not exist"; what is actually needed is far less — only
that for each FIXED step `i` the reading map is injective, which follows from two facts the tree
already carries: block tiling (`coarseLattice_unique`) and injectivity of the shift. -/

/-- For a fixed step `i`, the map `(c, x) ↦ (pathSite x c.2 i, c.2)` is injective on the pairs with
`x` in `c`'s own block. -/
theorem read_injOn {ell i : ℕ}
    (p q : (_ : CoarseBond L ell) × PeriodicLatticeSite L)
    (hp : p ∈ Finset.univ.sigma (fun c : CoarseBond L ell => blockOf c.1.1 ell))
    (hq : q ∈ Finset.univ.sigma (fun c : CoarseBond L ell => blockOf c.1.1 ell))
    (heq : ((pathSite p.2 p.1.2 i, p.1.2) : Bond L) = (pathSite q.2 q.1.2 i, q.1.2)) :
    p = q := by
  obtain ⟨cp, xp⟩ := p
  obtain ⟨cq, xq⟩ := q
  have hxp : xp ∈ blockOf cp.1.1 ell := (Finset.mem_sigma.mp hp).2
  have hxq : xq ∈ blockOf cq.1.1 ell := (Finset.mem_sigma.mp hq).2
  have hdir : cp.2 = cq.2 := congrArg (fun b : Bond L => b.2) heq
  have hsite : pathSite xp cp.2 i = pathSite xq cq.2 i := congrArg (fun b : Bond L => b.1) heq
  rw [hdir] at hsite
  have hx : xp = xq := pathSite_injective cq.2 i hsite
  subst hx
  have hy : cp.1.1 = cq.1.1 := coarseLattice_unique ell cp.1.2 cq.1.2 hxp hxq
  have hc : cp = cq := Prod.ext (Subtype.ext hy) hdir
  subst hc
  rfl

/-- **The multiplicity bound.** Summing a nonnegative bond weight over every coarse bond's whole
block average costs at most a factor `ell`.

NOTE — this needs NO divisibility hypothesis. `hdvd` was carried here in the first draft of this
module and the compiler's unused-variable linter caught it: block UNIQUENESS
(`coarseLattice_unique`) is unconditional, and `hdvd` is needed only for block EXISTENCE
(`coarseLattice_exists`) and for the `ell³` COUNT (`card_blockOf_of_coarse`). The multiplicity
argument uses uniqueness alone. Removed rather than left in place, so the statement does not
advertise a hypothesis it does not consume. -/
theorem sum_coarse_le {ell : ℕ}
    (g : Bond L → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ c : CoarseBond L ell, ∑ t ∈ blockIdx c.1.1 ell, g (fineBond c.2 t)
      ≤ (ell : ℝ) * ∑ b : Bond L, g b := by
  classical
  -- a single fixed step `i` costs at most one full copy of `∑ b, g b`
  have hstep : ∀ i : ℕ,
      ∑ c : CoarseBond L ell, ∑ x ∈ blockOf c.1.1 ell, g (pathSite x c.2 i, c.2)
        ≤ ∑ b : Bond L, g b := by
    intro i
    set T : Finset ((_ : CoarseBond L ell) × PeriodicLatticeSite L) :=
      Finset.univ.sigma (fun c : CoarseBond L ell => blockOf c.1.1 ell) with hT
    set Ψ : ((_ : CoarseBond L ell) × PeriodicLatticeSite L) → Bond L :=
      fun p => (pathSite p.2 p.1.2 i, p.1.2) with hΨ
    have hsig : ∑ c : CoarseBond L ell, ∑ x ∈ blockOf c.1.1 ell, g (pathSite x c.2 i, c.2)
        = ∑ p ∈ T, g (Ψ p) := by
      rw [hT, hΨ]
      exact Finset.sum_sigma' Finset.univ (fun c : CoarseBond L ell => blockOf c.1.1 ell)
        (fun c x => g (pathSite x c.2 i, c.2))
    rw [hsig]
    have himg : ∑ b ∈ T.image Ψ, g b = ∑ p ∈ T, g (Ψ p) :=
      Finset.sum_image (fun p hp q hq h => read_injOn p q hp hq h)
    rw [← himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hg b
  -- the block index set is `blockOf ×ˢ range ell`; swap the two sums and apply `hstep` to each `i`
  have hsplit : ∀ c : CoarseBond L ell,
      ∑ t ∈ blockIdx c.1.1 ell, g (fineBond c.2 t)
        = ∑ i ∈ Finset.range ell, ∑ x ∈ blockOf c.1.1 ell, g (pathSite x c.2 i, c.2) := by
    intro c
    simp only [blockIdx, fineBond, Finset.sum_product]
    exact Finset.sum_comm
  calc ∑ c : CoarseBond L ell, ∑ t ∈ blockIdx c.1.1 ell, g (fineBond c.2 t)
      = ∑ c : CoarseBond L ell, ∑ i ∈ Finset.range ell,
          ∑ x ∈ blockOf c.1.1 ell, g (pathSite x c.2 i, c.2) := by
        exact Finset.sum_congr rfl fun c _ => hsplit c
    _ = ∑ i ∈ Finset.range ell, ∑ c : CoarseBond L ell,
          ∑ x ∈ blockOf c.1.1 ell, g (pathSite x c.2 i, c.2) := Finset.sum_comm
    _ ≤ ∑ _i ∈ Finset.range ell, ∑ b : Bond L, g b :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (ell : ℝ) * ∑ b : Bond L, g b := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **CROSS-CHECK against the tree's own scalar twin.** `QcEquation.read_sum_eq` — proved by a
completely different route (`PoincareBridge.sum_eq_blocks` plus `pathStep_bijective`, not
image-of-an-injective-map) — gives the multiplicity as an EQUALITY for squares. Reading it through
`blockIdx`/`fineBond` shows my `sum_coarse_le`'s `≤ ell` is exactly `ell`, so §6's estimate loses
nothing at this step. `QcEquation.pathStep` is definitionally `QOne.pathSite`. -/
theorem multiplicity_exact {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (a : Bond L → ℝ) :
    ∑ c : CoarseBond L ell, ∑ t ∈ blockIdx c.1.1 ell, (a (fineBond c.2 t)) ^ 2
      = (ell : ℝ) * ∑ z : Bond L, (a z) ^ 2 := by
  rw [← AdalyFormal.Balaban.QcEquation.read_sum_eq hell hdvd a]
  exact Finset.sum_congr rfl fun c _ => by
    simp only [blockIdx, fineBond, Finset.sum_product, pathSite,
      AdalyFormal.Balaban.QcEquation.pathStep]

/-! ## §6 — THE UPPER BOUND -/

/-- `‖QA‖² ≤ ell⁻³ ‖A‖²`. -/
theorem qCLM_norm_sq_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : BondFnL2 L) :
    ‖qCLM U ell A‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 3) * ‖A‖ ^ 2 := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hstep1 : ‖qCLM U ell A‖ ^ 2
      = ∑ c : CoarseBond L ell, ‖lineCoarseRestrictCov U ell (WithLp.ofLp A) c‖ ^ 2 := by
    rw [norm_sq_pilp]
    exact Finset.sum_congr rfl fun c _ => by rw [qCLM_apply]
  have hstep2 : ∑ c : CoarseBond L ell, ‖lineCoarseRestrictCov U ell (WithLp.ofLp A) c‖ ^ 2
      ≤ ∑ c : CoarseBond L ell,
          (1 / (ell : ℝ) ^ 4) * ∑ t ∈ blockIdx c.1.1 ell, ‖WithLp.ofLp A (fineBond c.2 t)‖ ^ 2 :=
    Finset.sum_le_sum fun c _ => norm_sq_lineCoarseRestrictCov_le hell hdvd U (WithLp.ofLp A) c
  have hstep3 : ∑ c : CoarseBond L ell,
      (1 / (ell : ℝ) ^ 4) * ∑ t ∈ blockIdx c.1.1 ell, ‖WithLp.ofLp A (fineBond c.2 t)‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) * ∑ b : Bond L, ‖WithLp.ofLp A b‖ ^ 2) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact sum_coarse_le (fun b => ‖WithLp.ofLp A b‖ ^ 2) (fun _ => sq_nonneg _)
  have hfin : (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) * ∑ b : Bond L, ‖WithLp.ofLp A b‖ ^ 2)
      = (1 / (ell : ℝ) ^ 3) * ‖A‖ ^ 2 := by
    rw [norm_sq_pilp]
    field_simp
  rw [hstep1]
  exact (hstep2.trans hstep3).trans (le_of_eq hfin)

/-- **`‖qCLM U ell‖ ≤ √(ell⁻³)`** — the operator-norm form. -/
theorem qCLM_opNorm_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖qCLM U ell‖ ≤ Real.sqrt (1 / (ell : ℝ) ^ 3) := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun A => ?_
  have h := qCLM_norm_sq_le hell hdvd U A
  have hb : (0 : ℝ) ≤ Real.sqrt (1 / (ell : ℝ) ^ 3) * ‖A‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq : ‖qCLM U ell A‖ ^ 2 ≤ (Real.sqrt (1 / (ell : ℝ) ^ 3) * ‖A‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 / (ell : ℝ) ^ 3)]
    exact h
  have hroot := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hb] at hroot

/-- **`‖qCLM U ell‖ < 1` for every compatible `ell ≥ 2`, at EVERY background `U`.** -/
theorem qCLM_opNorm_lt_one {ell : ℕ} (hell : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖qCLM U ell‖ < 1 := by
  have hell0 : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hpos : (0 : ℝ) < (ell : ℝ) := by linarith
  have hlt : 1 / (ell : ℝ) ^ 3 < 1 := by
    rw [div_lt_one (by positivity)]
    have h8 : (2 : ℝ) ^ 3 ≤ (ell : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hellR 3
    norm_num at h8
    linarith
  have : Real.sqrt (1 / (ell : ℝ) ^ 3) < 1 := by
    have h := Real.sqrt_lt_sqrt (by positivity : (0:ℝ) ≤ 1 / (ell : ℝ) ^ 3) hlt
    rwa [Real.sqrt_one] at h
  exact lt_of_le_of_lt (qCLM_opNorm_le hell0 hdvd U) this

/-! ## §7 — THE LOWER BOUND, from a single fine bond -/

/-- The block average of a single-fine-bond field, at the coarse bond based at that bond's own base
site: exactly one `(x, i)` pair reads it, so the answer is `ell⁻⁴` times one transported value.
(The `x = y, i = 0` single-hit is `BridgeInverse.pathSite_eq_base_iff`, which is why `hwide` — the
"the block is not the whole torus" guard — appears.) -/
theorem lineCoarseRestrictCov_bondDelta {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) (v : SuTwo) :
    lineCoarseRestrictCov U ell (bondDelta (y, μ) v)
        ((⟨y, hy⟩ : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), μ)
      = (1 / (ell : ℝ) ^ 4) • RMap (periodicPathHolonomy U y (transportPath y y μ 0)) v := by
  have hyb : y ∈ blockOf y ell := mem_blockOf.mpr (fun _ => ⟨Nat.le_refl _, by omega⟩)
  have hterm : ∀ x ∈ blockOf y ell, rZeroA U y x (bondDelta (y, μ) v) μ ell
      = (if x = y then RMap (periodicPathHolonomy U y (transportPath y x μ 0)) v else 0) := by
    intro x hx
    unfold rZeroA
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
      rw [Finset.sum_eq_single 0]
      · rw [pathSite_zero, bondDelta_same]
      · intro i hi hine
        have hlt : i < ell := Finset.mem_range.mp hi
        have hne : ((pathSite x μ i, μ) : Bond L) ≠ (x, μ) := by
          intro hcc
          have := pathSite_eq_base_iff hell hdvd hwide hy hx μ hlt (congrArg Prod.fst hcc)
          exact hine this.2
        rw [bondDelta_ne v hne, map_zero]
      · intro hnm
        exact absurd (Finset.mem_range.mpr hell) hnm
    · rw [if_neg hxy]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hlt : i < ell := Finset.mem_range.mp hi
      have hne : ((pathSite x μ i, μ) : Bond L) ≠ (y, μ) := by
        intro hcc
        exact hxy (pathSite_eq_base_iff hell hdvd hwide hy hx μ hlt (congrArg Prod.fst hcc)).1
      rw [bondDelta_ne v hne, map_zero]
  show (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf y ell, rZeroA U y x (bondDelta (y, μ) v) μ ell
      = (1 / (ell : ℝ) ^ 4) • RMap (periodicPathHolonomy U y (transportPath y y μ 0)) v
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (blockOf y ell) y _, if_pos hyb]

/-- `‖suTwoWitness‖ = 1`. -/
theorem norm_suTwoWitness : ‖(suTwoWitness : SuTwo)‖ = 1 := by
  have h := norm_suTwoWitness_sq
  have hnn : (0 : ℝ) ≤ ‖(suTwoWitness : SuTwo)‖ := norm_nonneg _
  nlinarith

/-- **The unit witness**: a single nonzero `𝔰𝔲(2)` value on the fine bond based at the all-zero
site in direction `0`. -/
noncomputable def deltaWitness (L : PeriodicLatticeExtent) : BondFnL2 L :=
  WithLp.toLp 2 (bondDelta ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) suTwoWitness)

theorem norm_deltaWitness (L : PeriodicLatticeExtent) : ‖deltaWitness L‖ = 1 := by
  classical
  have hAsq : ‖deltaWitness L‖ ^ 2 = 1 := by
    rw [norm_sq_pilp]
    have hpt : ∀ b : Bond L, ‖WithLp.ofLp (deltaWitness L) b‖ ^ 2
        = if b = ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) then
            ‖(suTwoWitness : SuTwo)‖ ^ 2 else 0 := by
      intro b
      by_cases hb : b = ((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3))
      · subst hb; rw [if_pos rfl]; simp [deltaWitness, bondDelta]
      · rw [if_neg hb]; simp [deltaWitness, bondDelta, hb]
    rw [Finset.sum_congr rfl fun b _ => hpt b,
      Finset.sum_ite_eq' (Finset.univ : Finset (Bond L))
        (((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) : Bond L) _,
      if_pos (Finset.mem_univ _), norm_suTwoWitness]
    norm_num
  nlinarith [norm_nonneg (deltaWitness L), hAsq]

/-- The witness is read by exactly one `(x, i)` pair, so `Q` returns `ell⁻⁴` times a transported
copy of it — an explicit VALUE of `Q`, not merely a nonvanishing statement. -/
theorem norm_qCLM_deltaWitness {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    1 / (ell : ℝ) ^ 4 ≤ ‖qCLM U ell (deltaWitness L)‖ := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set y : PeriodicLatticeSite L := fun _ => 0 with hydef
  have hy : y ∈ CoarseLattice L ell := siteZeroMem L ell
  set c0 : CoarseBond L ell :=
    ((⟨y, hy⟩ : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), (0 : Fin 3)) with hc0
  have hcoord : ‖WithLp.ofLp (qCLM U ell (deltaWitness L)) c0‖ = 1 / (ell : ℝ) ^ 4 := by
    rw [qCLM_apply]
    have hofLp : WithLp.ofLp (deltaWitness L) = bondDelta (y, (0 : Fin 3)) suTwoWitness := by
      rw [deltaWitness]
    rw [hofLp, hc0, lineCoarseRestrictCov_bondDelta hell hdvd hwide U hy (0 : Fin 3) suTwoWitness,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (ell : ℝ) ^ 4),
      norm_RMap, norm_suTwoWitness, mul_one]
  rw [← hcoord]
  exact norm_coord_le _ _

/-- **`ell⁻⁴ ≤ ‖qCLM U ell‖`** — the operator is not merely nonzero; it is bounded below by the
normalisation itself. -/
theorem qCLM_opNorm_ge {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    1 / (ell : ℝ) ^ 4 ≤ ‖qCLM U ell‖ := by
  have h1 := norm_qCLM_deltaWitness hell hdvd hwide U
  have h2 : ‖qCLM U ell (deltaWitness L)‖ ≤ ‖qCLM U ell‖ * ‖deltaWitness L‖ :=
    (qCLM U ell).le_opNorm _
  rw [norm_deltaWitness, mul_one] at h2
  exact h1.trans h2

/-! ## §8 — THE UNIFORM-RESCALE TEST, as a theorem

Delete the `(1/ell⁴)` normalisation and nothing else — i.e. multiply `qCLM` by `ell⁴`, which is
exactly the block-SUMMING convention — and the conclusion `‖·‖ < 1` becomes false. So `< 1` is
carried by that prefactor and by nothing else in the construction. -/

/-- The block-SUMMING variant: `qCLM` with its `(1/ell⁴)` weight cancelled and nothing else changed. -/
noncomputable def qSumCLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) : BondFnL2 L →L[ℝ] CoarseFnL2 L ell := (ell : ℝ) ^ 4 • qCLM U ell

theorem summing_variant_one_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    1 ≤ ‖qSumCLM U ell‖ := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hw := norm_qCLM_deltaWitness hell hdvd hwide U
  have happ : qSumCLM U ell (deltaWitness L) = (ell : ℝ) ^ 4 • (qCLM U ell (deltaWitness L)) := rfl
  have hnorm : ‖qSumCLM U ell (deltaWitness L)‖
      = (ell : ℝ) ^ 4 * ‖qCLM U ell (deltaWitness L)‖ := by
    rw [happ, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (ell : ℝ) ^ 4)]
  have hlow : (1 : ℝ) ≤ ‖qSumCLM U ell (deltaWitness L)‖ := by
    rw [hnorm]
    have := mul_le_mul_of_nonneg_left hw (by positivity : (0:ℝ) ≤ (ell : ℝ) ^ 4)
    calc (1 : ℝ) = (ell : ℝ) ^ 4 * (1 / (ell : ℝ) ^ 4) := by field_simp
      _ ≤ (ell : ℝ) ^ 4 * ‖qCLM U ell (deltaWitness L)‖ := this
  have hop : ‖qSumCLM U ell (deltaWitness L)‖ ≤ ‖qSumCLM U ell‖ * ‖deltaWitness L‖ :=
    (qSumCLM U ell).le_opNorm _
  rw [norm_deltaWitness, mul_one] at hop
  exact hlow.trans hop

/-- The mutation FIRES: the summing variant does not satisfy the conclusion. -/
theorem summing_variant_not_lt_one {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ¬ (‖qSumCLM U ell‖ < 1) :=
  not_lt.mpr (summing_variant_one_le hell hdvd hwide U)

/-! ## §8b — THE EXACT VALUE AT `U = 1`: the upper bound of §6 is ATTAINED, not merely valid

The `ell⁻⁴` lower bound of §7 leaves a gap. It closes completely at the trivial background: the
CONSTANT field is an exact eigen-configuration of the averaging (`lineCoarseRestrictSuTwo_const`),
so the ratio `‖QA‖²/‖A‖²` is exactly `#CoarseBond / #Bond`, which the block tiling forces to be
`ell⁻³` (`card_site_eq`). Hence `‖qCLM (trivialU L) ell‖ = √(ell⁻³)` EXACTLY — §6's Cauchy–Schwarz
plus multiplicity estimate loses nothing at all. -/

/-- The block average of the CONSTANT field at `U = 1` is that constant — the defining property of a
TRUE average, at general `L` and general compatible `ell` (the tree carried this only at one
hard-coded witness lattice, `LineIntegralCovariant.lineCoarseRestrictCov_const_witness`). -/
theorem lineCoarseRestrictSuTwo_const {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (v : SuTwo) (c : CoarseBond L ell) :
    lineCoarseRestrictSuTwo ell
        (fun _ : Bond L => v) c = v := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hne : ((ell : ℝ) ^ 4) ≠ 0 := by positivity
  have hsum : ∑ _x ∈ blockOf c.1.1 ell, ∑ _i ∈ Finset.range ell, v = ((ell : ℝ) ^ 4) • v := by
    rw [Finset.sum_congr rfl (fun x _ => by rw [Finset.sum_const, Finset.card_range]),
      Finset.sum_const, card_blockOf_of_coarse hdvd c.1.2, smul_smul,
      ← Nat.cast_smul_eq_nsmul ℝ]
    have hc : ((ell ^ 3 * ell : ℕ) : ℝ) = (ell : ℝ) ^ 4 := by push_cast; ring
    rw [hc]
  rw [lineCoarseRestrictSuTwo, hsum, smul_smul, one_div,
    inv_mul_cancel₀ hne, one_smul]

/-- **The blocks TILE**: `#sites = ell³ · #coarse sites`. Existence of an owning centre is
`coarseLattice_exists` (needs `hdvd`), uniqueness is `coarseLattice_unique`, and each block has
`ell³` sites. -/
theorem card_site_eq {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Fintype.card (PeriodicLatticeSite L) = ell ^ 3 * (CoarseLattice L ell).card := by
  classical
  have hcover : (Finset.univ : Finset (PeriodicLatticeSite L))
      = (CoarseLattice L ell).biUnion (fun y => blockOf y ell) := by
    ext x
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion]
    obtain ⟨y, hy, hx⟩ :=
      AdalyFormal.Balaban.AdmissibleSubspace.coarseLattice_exists ell hell hdvd x
    exact ⟨y, hy, hx⟩
  have hdisj : ∀ y ∈ CoarseLattice L ell, ∀ y' ∈ CoarseLattice L ell, y ≠ y' →
      Disjoint (blockOf y ell) (blockOf y' ell) := by
    intro y hy y' hy' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hne (coarseLattice_unique ell hy hy' hx hx')
  calc Fintype.card (PeriodicLatticeSite L)
      = ((CoarseLattice L ell).biUnion (fun y => blockOf y ell)).card := by
        rw [← hcover, Finset.card_univ]
    _ = ∑ y ∈ CoarseLattice L ell, (blockOf y ell).card := Finset.card_biUnion hdisj
    _ = ∑ _y ∈ CoarseLattice L ell, ell ^ 3 :=
        Finset.sum_congr rfl fun _ hy => card_blockOf_of_coarse hdvd hy
    _ = ell ^ 3 * (CoarseLattice L ell).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The same count at the level of BONDS: `#Bond = ell³ · #CoarseBond`. -/
theorem card_bond_eq {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Fintype.card (Bond L) = ell ^ 3 * Fintype.card (CoarseBond L ell) := by
  have hb : Fintype.card (Bond L) = Fintype.card (PeriodicLatticeSite L) * 3 := by
    simp [Bond, Fintype.card_prod]
  have hc : Fintype.card (CoarseBond L ell) = (CoarseLattice L ell).card * 3 := by
    simp [CoarseBond, Fintype.card_prod, Fintype.card_coe]
  rw [hb, hc, card_site_eq hell hdvd, mul_assoc]

/-- The constant field, as an element of the `L²` carrier. -/
noncomputable def constWitness (L : PeriodicLatticeExtent) : BondFnL2 L :=
  WithLp.toLp 2 (fun _ : Bond L => (suTwoWitness : SuTwo))

theorem norm_constWitness_sq (L : PeriodicLatticeExtent) :
    ‖constWitness L‖ ^ 2 = (Fintype.card (Bond L) : ℝ) := by
  rw [norm_sq_pilp]
  have hpt : ∀ b : Bond L, ‖WithLp.ofLp (constWitness L) b‖ ^ 2 = (1 : ℝ) := by
    intro b
    show ‖(suTwoWitness : SuTwo)‖ ^ 2 = 1
    rw [norm_suTwoWitness]; norm_num
  rw [Finset.sum_congr rfl fun b _ => hpt b, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]

theorem norm_qCLM_trivialU_constWitness_sq {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖qCLM (trivialU L) ell (constWitness L)‖ ^ 2
      = (Fintype.card (CoarseBond L ell) : ℝ) := by
  rw [norm_sq_pilp]
  have hpt : ∀ c : CoarseBond L ell,
      ‖WithLp.ofLp (qCLM (trivialU L) ell
        (constWitness L)) c‖ ^ 2 = (1 : ℝ) := by
    intro c
    rw [qCLM_apply]
    show ‖lineCoarseRestrictCov (trivialU L) ell
      (fun _ : Bond L => (suTwoWitness : SuTwo)) c‖ ^ 2 = 1
    rw [lineCoarseRestrictCov_trivialU,
      lineCoarseRestrictSuTwo_const hell hdvd, norm_suTwoWitness]
    norm_num
  rw [Finset.sum_congr rfl fun c _ => hpt c, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]

/-- **The upper bound is ATTAINED at `U = 1`.** -/
theorem qCLM_trivialU_opNorm_ge {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Real.sqrt (1 / (ell : ℝ) ^ 3)
      ≤ ‖qCLM (trivialU L) ell‖ := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hNnn : (0 : ℝ) ≤ ‖qCLM (trivialU L) ell‖ := norm_nonneg (qCLM (trivialU L) ell)
  have hle : ‖qCLM (trivialU L) ell (constWitness L)‖
      ≤ ‖qCLM (trivialU L) ell‖ * ‖constWitness L‖ :=
    (qCLM (trivialU L) ell).le_opNorm (constWitness L)
  have hsq : ‖qCLM (trivialU L) ell (constWitness L)‖ ^ 2
      ≤ ‖qCLM (trivialU L) ell‖ ^ 2 * ‖constWitness L‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg (qCLM (trivialU L) ell (constWitness L))) hle 2
    rwa [mul_pow] at h
  set N : ℝ := ‖qCLM (trivialU L) ell‖ with hN
  rw [norm_qCLM_trivialU_constWitness_sq hell hdvd, norm_constWitness_sq,
    card_bond_eq hell hdvd] at hsq
  -- `#CoarseBond ≤ N² · ell³ · #CoarseBond`, and `#CoarseBond > 0`
  have hpos : (0 : ℝ) < (Fintype.card (CoarseBond L ell) : ℝ) := by
    have : 0 < Fintype.card (CoarseBond L ell) := Fintype.card_pos
    exact_mod_cast this
  have hkey : (1 : ℝ) ≤ N ^ 2 * (ell : ℝ) ^ 3 := by
    have hcast : ((ell ^ 3 * Fintype.card (CoarseBond L ell) : ℕ) : ℝ)
        = (ell : ℝ) ^ 3 * (Fintype.card (CoarseBond L ell) : ℝ) := by push_cast; ring
    rw [hcast] at hsq
    nlinarith [hsq, hpos]
  have hinv : 1 / (ell : ℝ) ^ 3 ≤ N ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hroot := Real.sqrt_le_sqrt hinv
  rwa [Real.sqrt_sq hNnn] at hroot

/-- **THE EXACT OPERATOR NORM AT `U = 1`.** `‖qCLM (trivialU L) ell‖ = √(ell⁻³)`. §6's estimate is
therefore not merely an upper bound: it is the value. -/
theorem qCLM_trivialU_opNorm_eq {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖qCLM (trivialU L) ell‖
      = Real.sqrt (1 / (ell : ℝ) ^ 3) :=
  le_antisymm (qCLM_opNorm_le hell hdvd _) (qCLM_trivialU_opNorm_ge hell hdvd)

/-! ## §9 — AT THE PARAMETERS THAT MATTER: `curvedRegularU`, `ell = 2`, `witL5` -/

/-- **THE NUMBER, decided.** `‖qCLM curvedRegularU 2‖ < 1` — this is the exact shape of the
hypothesis in `GammaRecursion.curvedRegularU_Q_decides_uniformity`'s SECOND branch, so along the
tree's own `Q` the `q ≥ 1` no-go does not fire. -/
theorem qCLM_curvedRegularU_two_lt_one : ‖qCLM curvedRegularU 2‖ < 1 :=
  qCLM_opNorm_lt_one (le_refl 2) witL5_dvd_two curvedRegularU

/-- The upper bound with its value: `≤ √(1/8) = 0.3535…`. -/
theorem qCLM_curvedRegularU_two_le : ‖qCLM curvedRegularU 2‖ ≤ Real.sqrt (1 / 8) := by
  have h := qCLM_opNorm_le (by norm_num) witL5_dvd_two curvedRegularU
  have hc : (1 : ℝ) / (((2 : ℕ) : ℝ)) ^ 3 = 1 / 8 := by norm_num
  rwa [hc] at h

/-- The lower bound with its value: `≥ 1/16`. -/
theorem qCLM_curvedRegularU_two_ge : (1 : ℝ) / 16 ≤ ‖qCLM curvedRegularU 2‖ := by
  have h := qCLM_opNorm_ge (by norm_num) witL5_dvd_two witL5_wide_two curvedRegularU
  have hc : (1 : ℝ) / (((2 : ℕ) : ℝ)) ^ 4 = 1 / 16 := by norm_num
  rwa [hc] at h

/-- **The two-sided sandwich at the decisive parameters.** -/
theorem qCLM_two_sided_curvedRegularU :
    (1 : ℝ) / 16 ≤ ‖qCLM curvedRegularU 2‖ ∧ ‖qCLM curvedRegularU 2‖ ≤ Real.sqrt (1 / 8) :=
  ⟨qCLM_curvedRegularU_two_ge, qCLM_curvedRegularU_two_le⟩

/-- **The exact value on the SAME lattice, at the trivial background**: `√(1/8) = 0.3535…`. Because
`qCLM_curvedRegularU_two_le` gives the same number as an upper bound at `curvedRegularU`, the
`< 1` verdict is not an artefact of a lossy estimate — the estimate is exactly attained one
background away. -/
theorem qCLM_trivialU_witL5_two_eq :
    ‖qCLM (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witL5) 2‖ = Real.sqrt (1 / 8) := by
  have h := qCLM_trivialU_opNorm_eq (L := witL5) (ell := 2) (by norm_num) witL5_dvd_two
  have hc : (1 : ℝ) / (((2 : ℕ) : ℝ)) ^ 3 = 1 / 8 := by norm_num
  rwa [hc] at h

/-! ## §10 — CONTROLS -/

/-- **CONSISTENCY of the two independent derivations.** The lower bound comes from a single-bond
witness, the upper from Cauchy–Schwarz plus a multiplicity count; they share no step. If either were
wrong by a power of `ell` this would be a contradiction. -/
theorem two_sided_consistent : (1 : ℝ) / 16 ≤ Real.sqrt (1 / 8) := by
  have h : Real.sqrt ((1:ℝ)/16) ≤ Real.sqrt (1/8) := Real.sqrt_le_sqrt (by norm_num)
  have hs : ((1:ℝ)/16) ≤ Real.sqrt ((1:ℝ)/16) := by
    have hq : ((1:ℝ)/16) = Real.sqrt (((1:ℝ)/16) ^ 2) := by
      rw [Real.sqrt_sq (by norm_num)]
    rw [hq]
    exact Real.sqrt_le_sqrt (by norm_num)
  exact hs.trans h

/-- **NOT VACUOUS.** The `< 1` is not the trivial statement about a zero operator: the operator norm
is bounded strictly away from `0` by an explicit positive number. -/
theorem bound_is_not_zero : (0 : ℝ) < ‖qCLM curvedRegularU 2‖ :=
  lt_of_lt_of_le (by norm_num) qCLM_curvedRegularU_two_ge

/-- **DEGENERATE POINT, quarantined.** At `ell = 1` the method yields exactly `≤ 1`, no strict
inequality — correct, since a `1`-block is a single site and `Q` then transports without averaging.
This is why `qCLM_opNorm_lt_one` carries `2 ≤ ell` and not `0 < ell`. -/
theorem opNorm_bound_at_one_is_one (U : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (hdvd : ∀ μ : Fin 3, (1:ℕ) ∣ (L μ + 1)) :
    ‖qCLM U 1‖ ≤ 1 := by
  have h := qCLM_opNorm_le (by norm_num) hdvd U
  have hc : (1 : ℝ) / (((1 : ℕ) : ℝ)) ^ 3 = 1 := by norm_num
  rw [hc, Real.sqrt_one] at h
  exact h

/-! ## §11 — axiom audit -/

#print axioms norm_sq_pilp
#print axioms norm_coord_le
#print axioms card_blockIdx
#print axioms pathSite_injective
#print axioms norm_lineCoarseRestrictCov_le
#print axioms norm_sq_lineCoarseRestrictCov_le
#print axioms read_injOn
#print axioms sum_coarse_le
#print axioms multiplicity_exact
#print axioms qCLM_norm_sq_le
#print axioms qCLM_opNorm_le
#print axioms qCLM_opNorm_lt_one
#print axioms lineCoarseRestrictCov_bondDelta
#print axioms norm_suTwoWitness
#print axioms norm_deltaWitness
#print axioms norm_qCLM_deltaWitness
#print axioms qCLM_opNorm_ge
#print axioms summing_variant_one_le
#print axioms summing_variant_not_lt_one
#print axioms lineCoarseRestrictSuTwo_const
#print axioms card_site_eq
#print axioms card_bond_eq
#print axioms norm_constWitness_sq
#print axioms norm_qCLM_trivialU_constWitness_sq
#print axioms qCLM_trivialU_opNorm_ge
#print axioms qCLM_trivialU_opNorm_eq
#print axioms qCLM_trivialU_witL5_two_eq
#print axioms qCLM_curvedRegularU_two_lt_one
#print axioms qCLM_curvedRegularU_two_le
#print axioms qCLM_curvedRegularU_two_ge
#print axioms qCLM_two_sided_curvedRegularU
#print axioms two_sided_consistent
#print axioms bound_is_not_zero
#print axioms opNorm_bound_at_one_is_one

end AdalyFormal.Balaban.QCLMNorm
