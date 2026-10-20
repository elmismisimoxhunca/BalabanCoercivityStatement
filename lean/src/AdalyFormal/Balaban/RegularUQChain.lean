/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.LineIntegralCovariant
import AdalyFormal.Balaban.RegularUPerturbation
import AdalyFormal.Balaban.FourierFaithfulU1
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `RegularUQChain.lean` — `[QCHAIN-SENS]`, the covariant coarse-graining domain-alignment sensitivity

**The single-scale sensitivity of the FAITHFUL covariant coarse-graining to the background.** The
regular-`U` DIRECT coercivity brick (`RegularUDirectCoercivity.lean`) proves the `(b1)` transfer on
`ker Q₁(1)` (the FLAT kernel). Bałaban's actual target domain is `ker Q₁(U)`, the `U`-dependent
gauge-fixed subspace `{Q₁(U)B = 0}`. To align the two domains one needs to bound how far the
`U`-coarse-graining moves from the flat one:

  `‖Q₁(1)A − Q₁(U)A‖_{L²} ≤ C_Q · α₁ · ‖A‖_{L²}`,   `α₁ = sup_b frobNorm(U b − 1)`,

with `C_Q` a `d,ell`-only (RG-step-`k`-independent) constant. `Q₁(U) =
`LineIntegralCovariant.lineCoarseRestrictCov U ell`, `Q₁(1) = lineCoarseRestrictCov (trivialU)`.

## The mechanism (source-faithful, k-free)

`lineCoarseRestrictCov U ell A b = (1/ell⁴)·∑_{x∈B(b₋)} rZeroA U b₋ x A b.2 ell`, and
`rZeroA U cMinus x A μ ell = ∑_{i<ell} RMap(periodicPathHolonomy U cMinus (transportPath cMinus x μ i))
 (A (pathSite x μ i, μ))` (`Q1Real.lean`). At `U = 1` every holonomy is `1` and `RMap 1 = id`
(`rZeroA_trivialU`), so the `U=1 − U` difference is, term by term,
`(id − RMap(hol_U)) (A(fine bond))`, a per-segment holonomy deviation. The sharp per-bond Lipschitz
brick `RMapLipschitz.norm_RMap_sub_self_le : ‖RMap V X − X‖ ≤ 2·frobNorm(V−1)·‖X‖` (reused, LAW-19)
controls each such deviation by `frobNorm(hol_U − 1)`, and the NEW telescoping bound
`frobNorm(periodicPathHolonomy U x steps − 1) ≤ (steps.length)·α₁` (§3) sums the per-bond deviations
along the transport path. Both `steps.length` (bounded by the block/segment length, a `d,ell`-only
count) and the number of terms are RG-step-independent, so `C_Q` carries no scale `k`.

## Scope honesty (READ THIS)

This is the SENSITIVITY brick ONLY. It does **not** prove regular-`U` coercivity on `ker Q₁(U)` —
that is the NEXT step (combine the `(b1)` flat-kernel transfer with this domain-alignment bound). It
supplies the `‖Q₁(1) − Q₁(U)‖ = O(α₁)` operator-sensitivity that step consumes. What is fully built
here (all `#print axioms`-clean below each): the holonomy path-telescoping Frobenius bound (§3), its
composition to the per-segment covariant-transport drift (§4), the per-block-site `rZeroA` sensitivity
(§5), the per-coarse-bond drift bound (§6), and the uniform `d,ell`-only path-length bound (§7). The
`L²`-aggregation to the coarse-bond norm, with its explicit `d,ell`-only constant `C_Q = 8/√ell`, IS
built here too, axiom-clean, in §9 (`coarseDriftEnergy_le`) — closing the §8 target statement. (This
sentence corrects a stale claim of "NOT yet built" that persisted in this header and in §8 after §9
landed; found by the Kimi third-gate prosecution, `compute/kimi_uqchain/VERDICT.md` Q6(g),
2026-08-01.) LAW-19: `RMap`, `frobNorm`, `frobSupBond`, `rZeroA`, `transportPath`,
`periodicPathHolonomy`, `lineCoarseRestrictCov` are all imported and reused.

## True consumers (as of 2026-08-01)

`norm_rZeroA_trivialU_sub_le` (§5) and `transportPath_length_le` (§7) are consumed by
`CovariantFibreTransfer.rZeroA_drift_le` (the §5-specialization at `ell = 2`); `coarseDriftEnergy_le`
(§9) is consumed by `RegularUCoercivityFull.covCoarse_Q1flat_le_of_kerQU`; `sum_coarse_Sblk_eq` (§9)
is also used directly by `MinSwapComposition`. `WindowStokesGeneralU.lean` does **not** import this
module and does not reference any declaration in it (Kimi third-gate finding, same VERDICT.md, Q6(f))
— an earlier lane record's framing that this module "carries the comparison bound used by
`WindowStokesGeneralU.lean`" is not correct; that module's comparison bound is drawn from
`TowerLawCovariant` instead. No docstring in this file made that claim, so nothing below is struck for
it; this note exists so the true consumer is stated in the one place a reader of this file would look.
-/

namespace AdalyFormal.Balaban.RegularUQChain

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.RMapLipschitz AdalyFormal.Balaban.Q1Real
  AdalyFormal.Balaban.LineIntegralCovariant AdalyFormal.Balaban.RegularUPerturbation
  AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU
  periodicLatticeShiftEquiv periodicLatticeShiftEquiv_apply)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.FourierFaithfulU1 (sum_coarse_blocks)

open scoped Matrix

/-! ## §0 — the Frobenius norm is a genuine norm (triangle inequality), via a `EuclideanSpace` bridge

`RMapLipschitz.frobSq`/`frobNorm` are plain functions (no norm typeclass, deliberately — to dodge the
`Matrix` norm-instance diamond flagged in `SuTwoInner.lean`). The telescoping in §3 needs the TRIANGLE
inequality for `frobNorm`, which those files do not carry. We obtain it cleanly by identifying `frobSq`
with the squared Euclidean norm of the `2×2` entry vector in `EuclideanSpace ℂ (Fin 2 × Fin 2)` — a
canonical Mathlib norm, so no diamond is ever placed on `Matrix`. -/

/-- The `2×2` complex matrix as a vector in `EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
noncomputable def frobVec (M : Matrix (Fin 2) (Fin 2) ℂ) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  (WithLp.equiv 2 (Fin 2 × Fin 2 → ℂ)).symm (fun ij => M ij.1 ij.2)

@[simp] theorem frobVec_apply (M : Matrix (Fin 2) (Fin 2) ℂ) (ij : Fin 2 × Fin 2) :
    frobVec M ij = M ij.1 ij.2 := rfl

theorem frobVec_add (M N : Matrix (Fin 2) (Fin 2) ℂ) : frobVec (M + N) = frobVec M + frobVec N := by
  ext ij; simp only [frobVec]; rfl

theorem frobVec_sub (M N : Matrix (Fin 2) (Fin 2) ℂ) : frobVec (M - N) = frobVec M - frobVec N := by
  ext ij; simp only [frobVec]; rfl

/-- `‖frobVec M‖² = frobSq M` — the bridge from the canonical Euclidean norm to `RMapLipschitz.frobSq`. -/
theorem norm_frobVec_sq (M : Matrix (Fin 2) (Fin 2) ℂ) : ‖frobVec M‖ ^ 2 = frobSq M := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  have h : ∀ ij : Fin 2 × Fin 2, ‖frobVec M ij‖ ^ 2 = Complex.normSq (M ij.1 ij.2) := by
    intro ij; rw [frobVec_apply, ← Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl (fun ij _ => h ij), Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  unfold frobSq; ring

/-- `frobNorm M = ‖frobVec M‖` — hands the entire `EuclideanSpace` norm toolkit to `frobNorm`. -/
theorem frobNorm_eq_norm_frobVec (M : Matrix (Fin 2) (Fin 2) ℂ) : frobNorm M = ‖frobVec M‖ := by
  rw [frobNorm, ← norm_frobVec_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **The Frobenius triangle inequality** — the missing normed-space fact the telescoping needs. -/
theorem frobNorm_add_le (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    frobNorm (M + N) ≤ frobNorm M + frobNorm N := by
  rw [frobNorm_eq_norm_frobVec, frobNorm_eq_norm_frobVec, frobNorm_eq_norm_frobVec, frobVec_add]
  exact norm_add_le _ _

/-! ## §1 — conjugate-transpose invariance and unitary (left) invariance of `frobSq`/`frobNorm` -/

theorem frobSq_conjTranspose (M : Matrix (Fin 2) (Fin 2) ℂ) : frobSq Mᴴ = frobSq M := by
  simp only [frobSq, Matrix.conjTranspose_apply, Complex.normSq_conj, RCLike.star_def]
  ring

theorem frobNorm_conjTranspose (M : Matrix (Fin 2) (Fin 2) ℂ) : frobNorm Mᴴ = frobNorm M := by
  rw [frobNorm, frobNorm, frobSq_conjTranspose]

/-- **Unitary LEFT-invariance of `frobSq`**: `frobSq (W·M) = frobSq M` when `Wᴴ·W = 1`. Derived from
the right-invariance brick (`RMapLipschitz.frobSq_mul_right_isometry`) via conjugate-transpose. -/
theorem frobSq_mul_left_iso (W M : Matrix (Fin 2) (Fin 2) ℂ) (hW : Wᴴ * W = 1) :
    frobSq (W * M) = frobSq M := by
  rw [← frobSq_conjTranspose (W * M), Matrix.conjTranspose_mul,
    frobSq_mul_right_isometry Mᴴ Wᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact hW),
    frobSq_conjTranspose]

theorem frobNorm_mul_left_iso (W M : Matrix (Fin 2) (Fin 2) ℂ) (hW : Wᴴ * W = 1) :
    frobNorm (W * M) = frobNorm M := by
  rw [frobNorm, frobNorm, frobSq_mul_left_iso W M hW]

#print axioms frobNorm_add_le
#print axioms frobNorm_conjTranspose
#print axioms frobNorm_mul_left_iso

/-! ## §2 — the SU(2) coercion facts and the per-factor telescoping step -/

/-- `((A⁻¹ : SU) : Matrix) = (↑A)ᴴ` — SU inverse coerces to conjugate transpose. -/
theorem su_coe_inv (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((A⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = ((A : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, Matrix.star_eq_conjTranspose]

/-- `(↑A)ᴴ · ↑A = 1` for `A ∈ SU(2)`. -/
theorem su_conjTranspose_mul (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((A : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (A : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp A.2.1
  rwa [Matrix.star_eq_conjTranspose] at h

/-- **`frobNorm(↑A⁻¹ − 1) = frobNorm(↑A − 1)`** — inverting an SU(2) element preserves the deviation. -/
theorem frobNorm_su_inv_sub_one (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobNorm ((A⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) - 1) =
      frobNorm ((A : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  rw [su_coe_inv,
    show ((A : Matrix (Fin 2) (Fin 2) ℂ))ᴴ - 1 = ((A : Matrix (Fin 2) (Fin 2) ℂ) - 1)ᴴ by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one],
    frobNorm_conjTranspose]

/-- **THE PER-FACTOR TELESCOPING STEP.** For `a, b ∈ SU(2)`,
`frobNorm(↑(a·b) − 1) ≤ frobNorm(↑a − 1) + frobNorm(↑b − 1)`. The engine of the path telescoping:
`ab − 1 = a·(b−1) + (a−1)`, triangle, then unitary left-invariance kills the `a` factor. -/
theorem frobNorm_su_mul_sub_one_le (a b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobNorm ((↑(a * b) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤
      frobNorm ((a : Matrix (Fin 2) (Fin 2) ℂ) - 1) +
        frobNorm ((b : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  set A := (a : Matrix (Fin 2) (Fin 2) ℂ) with hA
  set B := (b : Matrix (Fin 2) (Fin 2) ℂ) with hB
  have hcoe : ((↑(a * b) : Matrix (Fin 2) (Fin 2) ℂ)) = A * B := by
    rw [hA, hB]; exact Submonoid.coe_mul _ a b
  have heq : A * B - 1 = A * (B - 1) + (A - 1) := by noncomm_ring
  rw [hcoe, heq]
  calc frobNorm (A * (B - 1) + (A - 1))
      ≤ frobNorm (A * (B - 1)) + frobNorm (A - 1) := frobNorm_add_le _ _
    _ = frobNorm (B - 1) + frobNorm (A - 1) := by rw [frobNorm_mul_left_iso A (B - 1)
          (by rw [hA]; exact su_conjTranspose_mul a)]
    _ = frobNorm (A - 1) + frobNorm (B - 1) := by rw [add_comm]

#print axioms frobNorm_su_inv_sub_one
#print axioms frobNorm_su_mul_sub_one_le

/-! ## §3 — THE HOLONOMY PATH-TELESCOPING BOUND (the new, load-bearing brick) -/

/-- **`frobNorm(periodicPathHolonomy U x steps − 1) ≤ (steps.length)·α₁`**, `α₁ = frobSupBond U =
sup_b frobNorm(U b − 1)`. The holonomy along a lattice path of length `n` differs from the identity by
at most `n·α₁` in Frobenius norm: each of the `n` link factors (forward `U b` or backward `(U b)⁻¹`)
deviates from `1` by `≤ α₁` (inverse via `frobNorm_su_inv_sub_one`), and the per-factor telescoping
step (§2) sums the deviations. `α₁`-first-order, and — crucially — the constant is the PATH LENGTH,
a geometric count with NO RG step `k`. -/
theorem frobNorm_holonomy_sub_one_le {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (steps : List (Fin 3 × Bool)) (x : PeriodicLatticeSite L) :
    frobNorm ((↑(periodicPathHolonomy U x steps) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤
      (steps.length : ℝ) * frobSupBond U := by
  induction steps generalizing x with
  | nil =>
    show frobNorm ((↑(1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ _
    rw [OneMemClass.coe_one, sub_self, frobNorm_zero, List.length_nil, Nat.cast_zero, zero_mul]
  | cons s rest ih =>
    have hfactor : frobNorm ((↑(if s.2 then U (x, s.1)
        else (U (periodicLatticeStep x s, s.1))⁻¹) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ frobSupBond U := by
      cases hs : s.2 with
      | false =>
        simp only [Bool.false_eq_true, if_false]
        rw [frobNorm_su_inv_sub_one]
        exact frobNorm_le_frobSupBond U (periodicLatticeStep x s, s.1)
      | true =>
        simp only [if_true]
        exact frobNorm_le_frobSupBond U (x, s.1)
    have hstep : periodicPathHolonomy U x (s :: rest) =
        (if s.2 then U (x, s.1) else (U (periodicLatticeStep x s, s.1))⁻¹) *
          periodicPathHolonomy U (periodicLatticeStep x s) rest := rfl
    rw [hstep]
    refine le_trans (frobNorm_su_mul_sub_one_le _ _) ?_
    have := ih (periodicLatticeStep x s)
    rw [List.length_cons, Nat.cast_add, Nat.cast_one]
    have hα0 : 0 ≤ frobSupBond U := frobSupBond_nonneg U
    calc frobNorm ((↑(if s.2 then U (x, s.1) else (U (periodicLatticeStep x s, s.1))⁻¹) :
            Matrix (Fin 2) (Fin 2) ℂ) - 1) +
          frobNorm ((↑(periodicPathHolonomy U (periodicLatticeStep x s) rest) :
            Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ frobSupBond U + (rest.length : ℝ) * frobSupBond U := add_le_add hfactor this
      _ = ((rest.length : ℝ) + 1) * frobSupBond U := by ring

#print axioms frobNorm_holonomy_sub_one_le

/-! ## §4 — the per-segment covariant-transport drift `‖RMap(hol)X − X‖ ≤ 2·len·α₁·‖X‖` -/

/-- **The single covariant-transport deviation, along a path.** For any path `steps` and any field
value `X`, the covariant transport `RMap(holonomy)` differs from the identity (its `U=1` value) by
`‖RMap(periodicPathHolonomy U x steps) X − X‖ ≤ 2·(steps.length)·α₁·‖X‖`. Composition of the sharp
per-bond Lipschitz brick `RMapLipschitz.norm_RMap_sub_self_le` with the §3 telescoping bound. Vanishes
at `U = 1` (`α₁ = 0`) and at the empty path (`length = 0`). `k`-free (the constant is `2·(path length)`,
a geometric count). -/
theorem norm_RMap_holonomy_sub_self_le {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (steps : List (Fin 3 × Bool)) (x : PeriodicLatticeSite L) (X : SuTwo) :
    ‖RMap (periodicPathHolonomy U x steps) X - X‖ ≤
      2 * (steps.length : ℝ) * frobSupBond U * ‖X‖ := by
  refine le_trans (norm_RMap_sub_self_le (periodicPathHolonomy U x steps) X) ?_
  have h := frobNorm_holonomy_sub_one_le U steps x
  have hle : 2 * frobNorm ((↑(periodicPathHolonomy U x steps) : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖X‖
      ≤ 2 * ((steps.length : ℝ) * frobSupBond U) * ‖X‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg X)
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  exact le_trans hle (le_of_eq (by ring))

#print axioms norm_RMap_holonomy_sub_self_le

/-! ## §5 — the per-block-site `rZeroA` sensitivity (the covariant line-integral transport drift) -/

/-- **THE PER-BLOCK-SITE SENSITIVITY.** At every block-interior site `x`, the covariant line-integral
transport `rZeroA` at background `U` differs from its `U=1` value (the bare abelian segment sum,
`rZeroA_trivialU`) by
`‖rZeroA(1) − rZeroA(U)‖ ≤ ∑_{i<ell} 2·|transportPath cMinus x μ i|·α₁·‖A(pathSite x μ i, μ)‖`.
Each of the `ell` fine bonds along the segment contributes a covariant-transport deviation controlled
by the length of ITS OWN transport path (§4) — the faithful per-bond, path-dependent structure of
CMP98's `R_{0,c₋}A`. `α₁`-first-order, `k`-free. -/
theorem norm_rZeroA_trivialU_sub_le {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (cMinus x : PeriodicLatticeSite L) (A : Bond L → SuTwo) (μ : Fin 3) (ell : ℕ) :
    ‖rZeroA (trivialU L) cMinus x A μ ell - rZeroA U cMinus x A μ ell‖ ≤
      ∑ i ∈ Finset.range ell, 2 * ((transportPath cMinus x μ i).length : ℝ) * frobSupBond U *
        ‖A (pathSite x μ i, μ)‖ := by
  rw [rZeroA_trivialU,
    show rZeroA U cMinus x A μ ell = ∑ i ∈ Finset.range ell,
        RMap (periodicPathHolonomy U cMinus (transportPath cMinus x μ i)) (A (pathSite x μ i, μ))
      from rfl,
    ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
  rw [← norm_neg, neg_sub]
  exact norm_RMap_holonomy_sub_self_le U (transportPath cMinus x μ i) cMinus (A (pathSite x μ i, μ))

#print axioms norm_rZeroA_trivialU_sub_le

/-! ## §6 — the per-coarse-bond drift bound (block-aggregated, `L¹`-in-block) -/

/-- **THE PER-COARSE-BOND DRIFT BOUND.** At every coarse bond `b`, the difference of the faithful
covariant coarse-grainings is controlled, with the `1/ell⁴` block-average normalization intact, by the
block sum of the per-segment transport deviations:
`‖Q₁(1)A(b) − Q₁(U)A(b)‖ ≤ (1/ell⁴)·∑_{x∈B(b₋)}∑_{i<ell} 2·|transportPath b₋ x b.2 i|·α₁·‖A(x+i·e,b.2)‖`.
This is the pointwise (per-coarse-bond) statement of `[QCHAIN-SENS]`, `α₁`-first-order and `k`-free. The
`L²`-aggregation over coarse bonds with an explicit `d,ell`-only `C_Q` needs the fine-bond incidence
multiplicity of the block/line-integral index map (§7, NAMED residual). -/
theorem norm_lineCoarseRestrictCov_trivialU_sub_le {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : Bond L → SuTwo) (b : CoarseBond L ell) :
    ‖lineCoarseRestrictCov (trivialU L) ell A b - lineCoarseRestrictCov U ell A b‖ ≤
      (1 / (ell : ℝ) ^ 4) * ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
        2 * ((transportPath b.1.1 x b.2 i).length : ℝ) * frobSupBond U *
          ‖A (pathSite x b.2 i, b.2)‖ := by
  simp only [lineCoarseRestrictCov]
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x _ => ?_))
  exact norm_rZeroA_trivialU_sub_le U b.1.1 x A b.2 ell

#print axioms norm_lineCoarseRestrictCov_trivialU_sub_le

/-! ## §7 — THE UNIFORM `d,ell`-ONLY PATH-LENGTH BOUND (k-independence, made explicit)

The whole point of `k`-uniformity: the transport path length is a purely GEOMETRIC count on the block
`B(b₋)` (side `ell`) and the segment (length `< ell`), with NO RG step `k` and NO lattice-extent
dependence. Here `d = 3`, so every transport path has length `≤ 4·ell`. -/

/-- `(straightSegment a b μ).length = coordSteps a b μ`. -/
theorem straightSegment_length {L : PeriodicLatticeExtent} (a b : PeriodicLatticeSite L) (μ : Fin 3) :
    (straightSegment a b μ).length = coordSteps a b μ := by
  simp [straightSegment]

/-- Updating a DIFFERENT coordinate of the base leaves `coordSteps` in direction `ν` unchanged. -/
theorem coordSteps_update_ne {L : PeriodicLatticeExtent} (a b : PeriodicLatticeSite L)
    {ν κ : Fin 3} (w : Fin (L κ + 1)) (h : ν ≠ κ) :
    coordSteps (Function.update a κ w) b ν = coordSteps a b ν := by
  unfold coordSteps
  rw [Function.update_of_ne h]

/-- The `μ`-coordinate of `pathSite x μ i` is `x μ` advanced `i` steps (`Fin (L μ + 1)` arithmetic). -/
theorem pathSite_coord_self {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3)
    (i : ℕ) : (pathSite x μ i) μ = x μ + i • (1 : Fin (L μ + 1)) := by
  induction i with
  | zero => rw [pathSite_zero, zero_smul, add_zero]
  | succ n ih =>
    rw [pathSite_succ]
    simp only [periodicLatticeShift, Function.update_self, ih, succ_nsmul]
    abel

/-- The segment leg of the transport path has length `i % (L μ + 1)`. -/
theorem coordSteps_straight_eq {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3)
    (i : ℕ) : coordSteps x (pathSite x μ i) μ = i % (L μ + 1) := by
  unfold coordSteps
  rw [pathSite_coord_self, add_sub_cancel_left]
  exact nsmul_one_val (L μ) i

/-- **Each block-interior coordinate step is `< ell`.** For `x ∈ B(cMinus)` (side `ell`), the number
of forward steps in any direction is strictly less than the block side. -/
theorem coordSteps_lt_of_inBlock {L : PeriodicLatticeExtent} {cMinus x : PeriodicLatticeSite L}
    {ell : ℕ} (hx : inBlock cMinus ell x) (ν : Fin 3) : coordSteps cMinus x ν < ell := by
  obtain ⟨hlo, hhi⟩ := hx ν
  unfold coordSteps
  rw [Fin.sub_val_of_le (Fin.le_def.mpr hlo)]
  omega

/-- **THE UNIFORM `d,ell`-ONLY PATH-LENGTH BOUND.** Every transport path used by `rZeroA` inside the
block `B(cMinus)` (side `ell`) for a segment index `i < ell` has length `≤ 4·ell` — the `Γ`-contour
(`≤ 3·ell = d·ell`, `d = 3`) plus the segment leg (`< ell`). NO RG step `k`, NO lattice-extent
dependence: this is the geometric constant that makes `C_Q` `k`-independent. -/
theorem transportPath_length_le {L : PeriodicLatticeExtent} {cMinus x : PeriodicLatticeSite L}
    {ell : ℕ} (hx : inBlock cMinus ell x) {i : ℕ} (hi : i < ell) (μ : Fin 3) :
    (transportPath cMinus x μ i).length ≤ 4 * ell := by
  have h2 : coordSteps cMinus x 2 < ell := coordSteps_lt_of_inBlock hx 2
  have h1 : coordSteps cMinus x 1 < ell := coordSteps_lt_of_inBlock hx 1
  have h0 : coordSteps cMinus x 0 < ell := coordSteps_lt_of_inBlock hx 0
  have hgamma : (GammaPath cMinus x).length =
      coordSteps cMinus x 2 + coordSteps cMinus x 1 + coordSteps cMinus x 0 := by
    simp only [GammaPath, List.length_append, straightSegment_length]
    rw [coordSteps_update_ne cMinus x (x 2) (show (1 : Fin 3) ≠ 2 by decide),
      coordSteps_update_ne (Function.update cMinus 2 (x 2)) x (x 1) (show (0 : Fin 3) ≠ 1 by decide),
      coordSteps_update_ne cMinus x (x 2) (show (0 : Fin 3) ≠ 2 by decide)]
  have hseg : coordSteps x (pathSite x μ i) μ ≤ i := by
    rw [coordSteps_straight_eq]; exact Nat.mod_le _ _
  have hlen : (transportPath cMinus x μ i).length =
      (GammaPath cMinus x).length + coordSteps x (pathSite x μ i) μ := by
    simp only [transportPath, List.length_append, straightSegment_length]
  rw [hlen, hgamma]
  omega

#print axioms straightSegment_length
#print axioms coordSteps_update_ne
#print axioms pathSite_coord_self
#print axioms coordSteps_straight_eq
#print axioms coordSteps_lt_of_inBlock
#print axioms transportPath_length_le

/-! ## §7b — the per-coarse-bond drift with the UNIFORM `d,ell`-only path-length constant -/

/-- **THE PER-COARSE-BOND SENSITIVITY, with an explicit `k`-INDEPENDENT constant.** Chaining the
uniform path-length bound (§7, `≤ 4·ell`) into §6 replaces the per-path lengths by a single geometric
constant, giving
`‖Q₁(1)A(b) − Q₁(U)A(b)‖ ≤ (8/ell³)·α₁·∑_{x∈B(b₋)}∑_{i<ell} ‖A(pathSite x b.2 i, b.2)‖`.
The `8/ell³ = 2·(4·ell)/ell⁴` constant is EXPLICIT, `d,ell`-only, and carries NO RG step `k` — the
substance of the `[QCHAIN-SENS]` k-independence claim. (The `L²`-aggregation of the block sum to
`‖A‖_{L²}` needs the fine-bond incidence multiplicity, the §8 target statement — closed in §9.)

Note on `hell`: this proof's script recompiles green with `hell` deleted (Kimi third-gate finding,
`compute/kimi_uqchain/VERDICT.md` Q4(c), recompilation evidence, 2026-08-01) — the statement holds
vacuously at `ell = 0` too (`1/0⁴ = 0` in Lean, both sides of the inequality collapse to `0`). `hell`
is VESTIGIAL in this proof and is kept only for signature stability with `lineCoarseRestrictCov`'s
own documented domain (`0 < ell`, `LineIntegralCovariant.lean`); a future major version may drop it,
but doing so here would break call sites, so the binder is retained. -/
theorem norm_lineCoarseRestrictCov_trivialU_sub_le_uniform {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ} (hell : 0 < ell)
    (A : Bond L → SuTwo) (b : CoarseBond L ell) :
    ‖lineCoarseRestrictCov (trivialU L) ell A b - lineCoarseRestrictCov U ell A b‖ ≤
      (1 / (ell : ℝ) ^ 4) * ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
        2 * (4 * ell : ℝ) * frobSupBond U * ‖A (pathSite x b.2 i, b.2)‖ := by
  refine le_trans (norm_lineCoarseRestrictCov_trivialU_sub_le U ell A b) ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun i hi => ?_))
  have hxb : inBlock b.1.1 ell x := (AdmissibleSubspace.mem_blockOf).mp hx
  have hib : i < ell := Finset.mem_range.mp hi
  have hlen : ((transportPath b.1.1 x b.2 i).length : ℝ) ≤ 4 * ell := by
    have := transportPath_length_le hxb hib b.2
    exact_mod_cast this
  have hα0 : 0 ≤ frobSupBond U := frobSupBond_nonneg U
  have hA0 : 0 ≤ ‖A (pathSite x b.2 i, b.2)‖ := norm_nonneg _
  apply mul_le_mul_of_nonneg_right _ hA0
  apply mul_le_mul_of_nonneg_right _ hα0
  apply mul_le_mul_of_nonneg_left hlen (by norm_num)

#print axioms norm_lineCoarseRestrictCov_trivialU_sub_le_uniform

/-! ## §8 — the `L²`-AGGREGATION to `‖·‖_{L²(coarse)} ≤ C_Q·α₁·‖A‖_{L²(bonds)}` — target statement,
CLOSED by §9

**Status: BUILT, in §9, axiom-clean. (This status line and the "why not built here" paragraph below
had gone stale — they described this as an open residual after §9 had already closed it. Found by the
Kimi third-gate prosecution, `compute/kimi_uqchain/VERDICT.md` Q6(g), 2026-08-01.) This section states
the TARGET and the two reindexing counts it needs; §9 supplies both and assembles the aggregation as
`coarseDriftEnergy_le`.**

Writing `T_b := ∑_{x∈B(b₋)}∑_{i<ell} ‖A(pathSite x b.2 i, b.2)‖`, §7b gives, per coarse bond,
`‖Q₁(1)A(b) − Q₁(U)A(b)‖ ≤ (8/ell³)·α₁·T_b`. The `L²`-aggregation
`√(∑_b ‖Q₁(1)A(b) − Q₁(U)A(b)‖²) ≤ C_Q·α₁·√(∑_b ‖A b‖²)` then follows from real analysis already in
this tree (`Algebra.Order.Chebyshev.sq_sum_le_card_mul_sum_sq` — the exact Cauchy–Schwarz step §10–§11
of `RegularUPerturbation.lean` uses) PLUS the two counts:

* **(R1) block/segment index-card bound** — `(blockOf y ell).card ≤ ell ^ 3`, hence the index set
  `B(b₋) × range ell` has `≤ ell⁴` elements; Cauchy–Schwarz turns `T_b² ≤ ell⁴·∑_{x,i}‖A(...)‖²`. Built
  in §9 as `norm_lineCoarseRestrictCov_drift_sq_le`.
* **(R2) fine-bond incidence multiplicity** — `∑_b ∑_{x∈B(b₋)}∑_{i<ell} ‖A(pathSite x b.2 i, b.2)‖²
  ≤ ell · ∑_e ‖A e‖²` (`= ell · RegularUPerturbation.bondEnergy A`). This is the load-bearing count: for
  a fixed fine bond `(z, ρ)`, the triples `(b, x, i)` with `b.2 = ρ`, `x ∈ B(b₋)`, `i < ell`,
  `pathSite x ρ i = z` number **exactly `ell`** — for each `i ∈ [0, ell)`, `x = z − i·e_ρ` is forced and
  its owning coarse block `b₋` is UNIQUE. The uniqueness/existence is exactly
  `AdmissibleSubspace.coarseLattice_unique` / `coarseLattice_exists` (both already PROVED), under the
  standing tileability hypothesis `∀ μ, ell ∣ (L μ + 1)`. Built in §9 as `sum_coarse_Sblk_eq`, as an
  EXACT identity (not merely the `≤` stated above).

Composing (with `d = 3`, so the index card is `ell⁴` and the path bound is `4·ell`) yields the
EXPLICIT, `k`-independent, extent-independent constant
`C_Q = 8/√ell`   (i.e. `√(64·ell/ell²) = 8/√ell`): the aggregation loses a `√ell` from the incidence
count against the two extra `ell`-powers gained by Cauchy–Schwarz, off the `8/ell³` of §7b. This
composition is carried out in §9 as `coarseDriftEnergy_le`.

**Built in §9:** (R2) is a genuine `Finset`-reindexing over the tiling bijection
`(y ∈ Λ', x ∈ B(y)) ↔ x` (from `coarseLattice_exists`/`coarseLattice_unique`) COMPOSED with the
segment map `x ↦ pathSite x ρ i`; it is the block-line-integral analogue of
`RegularUPerturbation.sum_nbr1_sq_le` but strictly larger (a `d`-fold block sum, not a single
shift `Equiv`), and was a separate constructive brick from this sensitivity's §3–§7b core. §9 builds it
via the block-partition identity `FourierFaithfulU1.sum_coarse_blocks` plus the segment shift-`Equiv`
power (`pathSite_eq_shiftEquiv_pow`, `sum_pathSite_comp`). The mathematics of `[QCHAIN-SENS]` (the
`α₁`-first-order operator drift and its `k`-independent constant) is established by §3–§7b; (R1)/(R2)
are the bookkeeping that repackages the block sum as the `L²(bonds)` norm, and §9 closes both. -/

/-! ## §9 — THE `L²`-AGGREGATION `[L2-AGG]` (R1 + R2), explicit `k`-independent `C_Q = 8/√ell`

Closes the §8 residual, axiom-clean. Two `ell,d`-only reindexings:
* **(R2)** the fine-bond incidence, proved as an EXACT identity via block partition
  (`FourierFaithfulU1.sum_coarse_blocks`, LAW-19) + the segment shift-`Equiv` power;
* **(R1)** Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`, LAW-19) over the `ell⁴`-element
  `blockOf ×ˢ range ell` index set (card `= ell³·ell` via `card_blockOf_of_coarse`).

The aggregate `∑_b ‖(Q₁(1)−Q₁(U))A(b)‖² ≤ (64/ell)·α₁²·bondEnergy A` gives `C_Q = 8/√ell`
(`C_Q² = 64/ell`), EXPLICIT, `k`-free, extent-independent. Tileability `∀ μ, ell ∣ (L μ+1)` and
`0 < ell` are the standing compatible-block hypotheses (the source object's own domain). -/

/-- The `i`-step path map `x ↦ pathSite x μ i` is the `i`-th power of the shift `Equiv`
(`periodicLatticeShiftEquiv`), hence a bijection of the torus. -/
theorem pathSite_eq_shiftEquiv_pow {L : PeriodicLatticeExtent} (μ : Fin 3) (i : ℕ)
    (x : PeriodicLatticeSite L) :
    pathSite x μ i = ((periodicLatticeShiftEquiv (L := L) μ) ^ i) x := by
  have hfun : (⇑(periodicLatticeShiftEquiv (L := L) μ)) = fun y => periodicLatticeShift y μ := by
    funext y; exact periodicLatticeShiftEquiv_apply μ y
  rw [Equiv.Perm.coe_pow, hfun]
  rfl

/-- **The segment-shift bijection reindexing**: `∑_x g(pathSite x μ i) = ∑_z g z`, since
`x ↦ pathSite x μ i` is a torus bijection (`pathSite_eq_shiftEquiv_pow`). -/
theorem sum_pathSite_comp {L : PeriodicLatticeExtent} (μ : Fin 3) (i : ℕ)
    (g : PeriodicLatticeSite L → ℝ) :
    ∑ x : PeriodicLatticeSite L, g (pathSite x μ i) = ∑ z : PeriodicLatticeSite L, g z := by
  have h := Equiv.sum_comp ((periodicLatticeShiftEquiv (L := L) μ) ^ i) g
  rw [← h]
  exact Finset.sum_congr rfl (fun x _ => by rw [pathSite_eq_shiftEquiv_pow])

#print axioms pathSite_eq_shiftEquiv_pow
#print axioms sum_pathSite_comp

/-- **(R2) THE FINE-BOND INCIDENCE, as an EXACT identity.** Summing over all coarse bonds `b`, block
sites `x ∈ B(b₋)`, and segment offsets `i < ell` the squared fine-bond norm
`‖A(pathSite x b.2 i, b.2)‖²` counts every fine bond EXACTLY `ell` times (once per offset `i`), so
the total is `ell · bondEnergy A`. Blocks partition the torus (`sum_coarse_blocks`) and each offset
is a shift bijection (`sum_pathSite_comp`) — no overcounting: an equality, not `≤`. `k`-free. -/
theorem sum_coarse_Sblk_eq {L : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    (∑ b : CoarseBond L ell, ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
        ‖A (pathSite x b.2 i, b.2)‖ ^ 2)
      = (ell : ℝ) * bondEnergy A := by
  have step1 : (∑ b : CoarseBond L ell, ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
        ‖A (pathSite x b.2 i, b.2)‖ ^ 2)
      = ∑ ρ : Fin 3, ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell,
          ‖A (pathSite x ρ i, ρ)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [Finset.sum_subtype (CoarseLattice L ell) (fun _ => Iff.rfl)
      (fun y => ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ‖A (pathSite x ρ i, ρ)‖ ^ 2)]
  have step2 : ∀ ρ : Fin 3,
      (∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell,
          ‖A (pathSite x ρ i, ρ)‖ ^ 2)
      = (ell : ℝ) * ∑ z : PeriodicLatticeSite L, ‖A (z, ρ)‖ ^ 2 := by
    intro ρ
    rw [sum_coarse_blocks hell hdvd
        (fun x => ∑ i ∈ Finset.range ell, ‖A (pathSite x ρ i, ρ)‖ ^ 2), Finset.sum_comm,
      Finset.sum_congr rfl (fun i _ => sum_pathSite_comp ρ i (fun z => ‖A (z, ρ)‖ ^ 2)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hbe : bondEnergy A = ∑ ρ : Fin 3, ∑ z : PeriodicLatticeSite L, ‖A (z, ρ)‖ ^ 2 := by
    unfold bondEnergy; rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [step1, Finset.sum_congr rfl (fun ρ _ => step2 ρ), ← Finset.mul_sum, hbe]

#print axioms sum_coarse_Sblk_eq

/-- **(R1 + §7b) per-coarse-bond squared drift bound.** Combining §7b with Cauchy–Schwarz over the
`ell⁴`-element `blockOf ×ˢ range ell` index set gives, per coarse bond,
`‖(Q₁(1)−Q₁(U))A(b)‖² ≤ (64/ell²)·α₁²·∑_{x∈B(b₋)}∑_{i<ell}‖A(pathSite x b.2 i,b.2)‖²`,
`α₁ = frobSupBond U`. `k`-free. -/
theorem norm_lineCoarseRestrictCov_drift_sq_le {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (b : CoarseBond L ell) :
    ‖lineCoarseRestrictCov (trivialU L) ell A b - lineCoarseRestrictCov U ell A b‖ ^ 2
      ≤ (64 / (ell : ℝ) ^ 2) * frobSupBond U ^ 2 *
          (∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell, ‖A (pathSite x b.2 i, b.2)‖ ^ 2) := by
  have hα0 : 0 ≤ frobSupBond U := frobSupBond_nonneg U
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  set T := ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell, ‖A (pathSite x b.2 i, b.2)‖ with hTdef
  set S := ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell, ‖A (pathSite x b.2 i, b.2)‖ ^ 2
    with hSdef
  have hT0 : 0 ≤ T :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  -- §7b, with the constant `8·ell·α₁` pulled out of the block/segment sum
  have h7b := norm_lineCoarseRestrictCov_trivialU_sub_le_uniform U hell A b
  have hinner : (8 * (ell : ℝ) * frobSupBond U) * T
      = ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
          2 * (4 * ell : ℝ) * frobSupBond U * ‖A (pathSite x b.2 i, b.2)‖ := by
    rw [hTdef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [← hinner] at h7b
  -- h7b : ‖drift‖ ≤ (1/ell⁴) * ((8·ell·α₁) · T)
  have hdrift0 : 0 ≤ ‖lineCoarseRestrictCov (trivialU L) ell A b
      - lineCoarseRestrictCov U ell A b‖ := norm_nonneg _
  -- Cauchy–Schwarz on `T` over the product index set
  have hcard : ((blockOf b.1.1 ell ×ˢ Finset.range ell).card : ℝ) = (ell : ℝ) ^ 4 := by
    rw [Finset.card_product, card_blockOf_of_coarse hdvd b.1.2, Finset.card_range]
    push_cast; ring
  have hcs : T ^ 2 ≤ (ell : ℝ) ^ 4 * S := by
    have hCS := sq_sum_le_card_mul_sum_sq (s := blockOf b.1.1 ell ×ˢ Finset.range ell)
      (f := fun p : PeriodicLatticeSite L × ℕ => ‖A (pathSite p.1 b.2 p.2, b.2)‖)
    have hT_eq : (∑ p ∈ blockOf b.1.1 ell ×ˢ Finset.range ell,
        ‖A (pathSite p.1 b.2 p.2, b.2)‖) = T := by rw [hTdef, Finset.sum_product]
    have hS_eq : (∑ p ∈ blockOf b.1.1 ell ×ˢ Finset.range ell,
        ‖A (pathSite p.1 b.2 p.2, b.2)‖ ^ 2) = S := by rw [hSdef, Finset.sum_product]
    rw [hT_eq, hS_eq, hcard] at hCS
    exact hCS
  -- assemble: square §7b, apply CS, then evaluate the k-free constant
  calc ‖lineCoarseRestrictCov (trivialU L) ell A b - lineCoarseRestrictCov U ell A b‖ ^ 2
      ≤ ((1 / (ell : ℝ) ^ 4) * ((8 * (ell : ℝ) * frobSupBond U) * T)) ^ 2 :=
        pow_le_pow_left₀ hdrift0 h7b 2
    _ = ((1 / (ell : ℝ) ^ 4) * (8 * (ell : ℝ) * frobSupBond U)) ^ 2 * T ^ 2 := by ring
    _ ≤ ((1 / (ell : ℝ) ^ 4) * (8 * (ell : ℝ) * frobSupBond U)) ^ 2 * ((ell : ℝ) ^ 4 * S) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = (64 / (ell : ℝ) ^ 2) * frobSupBond U ^ 2 * S := by field_simp; ring

#print axioms norm_lineCoarseRestrictCov_drift_sq_le

/-- **`[QCHAIN-SENS]`, `L²`-AGGREGATED (the §8 deliverable).** The squared `L²(coarse-bond)` norm of
the covariant-coarse-graining domain-alignment drift is controlled by the `L²(bonds)` energy with
the EXPLICIT, `k`-INDEPENDENT, extent-independent constant `C_Q² = 64/ell` (`C_Q = 8/√ell`):
`∑_b ‖(Q₁(1)−Q₁(U))A(b)‖² ≤ (64/ell)·α₁²·bondEnergy A` (`α₁ = frobSupBond U`).
Sum the per-bond bound (R1), pull the constant, then substitute the exact incidence identity (R2). -/
theorem coarseDriftEnergy_le {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    (∑ b : CoarseBond L ell,
        ‖lineCoarseRestrictCov (trivialU L) ell A b - lineCoarseRestrictCov U ell A b‖ ^ 2)
      ≤ (64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A := by
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hstep : (∑ b : CoarseBond L ell,
        ‖lineCoarseRestrictCov (trivialU L) ell A b - lineCoarseRestrictCov U ell A b‖ ^ 2)
      ≤ ∑ b : CoarseBond L ell, (64 / (ell : ℝ) ^ 2) * frobSupBond U ^ 2 *
          (∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell, ‖A (pathSite x b.2 i, b.2)‖ ^ 2) :=
    Finset.sum_le_sum (fun b _ => norm_lineCoarseRestrictCov_drift_sq_le U hell hdvd A b)
  refine hstep.trans ?_
  have hid : (64 / (ell : ℝ) ^ 2) * frobSupBond U ^ 2 * ((ell : ℝ) * bondEnergy A)
      = (64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A := by
    field_simp
  rw [← Finset.mul_sum, sum_coarse_Sblk_eq hell hdvd A]
  exact le_of_eq hid

#print axioms coarseDriftEnergy_le

end AdalyFormal.Balaban.RegularUQChain
