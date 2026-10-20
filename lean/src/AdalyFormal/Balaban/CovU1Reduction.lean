/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantHjMinimizer

set_option autoImplicit false

/-!
# `U=1` reduction of the covariant coercivity operator (base case of the open target `(a)`)

**Dispatch**: CHARACTERIZE then BUILD the `U=1` reduction of `deltaJQuadFormCov` to the flat curl
form, as the base case of the real open target `(a)`: `deltaJQuadFormCov ≥ γ₀ > 0`.

## CHARACTERIZATION (established by reading the definitions, before proving)

The flat object `HjMinimizer.deltaJQuadForm ell levels A0` and the covariant object
`CovariantHjMinimizer.deltaJQuadFormCov ell levels U A0` live on **different carriers** and use
**different coarse-restriction operators**:

* FLAT: `A0 : BondSpace L = EuclideanSpace ℝ (Bond L)` (ℝ-valued); constraint subspace built from
  `LineIntegralAveraging.lineCoarseRestrictCLM` (the FAITHFUL block-averaged line-integral `Q_k`,
  CMP95 (1.11)/(1.18), to which `HjMinimizer.lean` was rewired 2026-07-24) and `curlCLM`.
* COVARIANT: `A0 : Bond L → SuTwo` (𝔰𝔲(2)-valued); constraint subspace `gaugeConstraintSubspaceCov`
  built from `coarseRestrictCovariant` (the SINGLE-BOND `Q_k` port) and `curlCovariantLM`.

**FINDING 1 (first-class, NEGATIVE).** The literal reduction `deltaJQuadFormCov (trivialU) =
deltaJQuadForm` is not even type-correct (𝔰𝔲(2)-valued vs ℝ-valued), and — carrier-matched —
**FAILS for `ell ≥ 2`**: the covariant object is built on the single-bond `coarseRestrictCovariant`,
whereas the flat object was rewired to the faithful line-integral `lineCoarseRestrictCLM`. Hence the
two constraint subspaces `gaugeConstraintSubspaceCov (trivialU)` and `gaugeConstraintSubspace` do
**not coincide even at `U=1`** for `ell ≥ 2`, so the covariant harmonic extension solves a genuinely
different variational problem. The flat `U=1` coercivity work (which lives on the faithful chain,
`U1CurlCoercivity.lean`/`U1Anchor.lean`) therefore does **not** transfer to `deltaJQuadFormCov`:
the covariant object inherits exactly the single-bond defect that `U1AnchorRefutation.lean` already
proved makes `BalabanFreeCoercivity` FALSE for the flat single-bond operator. **The covariant object
must be rebuilt on a faithful line-integral covariant `Q_k` before any `ell ≥ 2` coercivity is even
the right statement** — named residual, not attempted here (no covariant line-integral `Q_k` exists
anywhere in the tree; `grep` confirms).

**FINDING 2 (POSITIVE, `ell = 1`).** At `ell = 1` the two coarse-restriction operators literally
coincide (each block is a single site: `LineIntegralAveraging.lineCoarseRestrict_one_eq_coarseRestrict`
on the flat side; `coarseRestrictCovariantLM_one_eq_zero_imp` shows the covariant single-bond `Q_1`
is injective on the covariant side), the constraint subspace is `⊥`
(`gaugeConstraintSubspaceCov_ell1_eq_bot` / `gaugeConstraintSubspace_one_eq_bot`), no Schur
correction is possible, and `curlCovariantLM (trivialU) = ` the flat 𝔰𝔲(2) curl
(`curlValueCovariant`'s transport factors `R(1)=id` drop out). So the `ell=1` `U=1` reduction
**HOLDS**, carrier-matched, and is PROVED below
(`deltaJQuadFormCov_ell1_trivialU_eq_flatCurlEnergy`): the covariant Schur form collapses to a
manifestly `U`-INDEPENDENT flat-curl energy `covPlaqInner (flatCurlValue A0) (flatCurlValue A0)`.

**FINDING 3 (transfer of coercivity `(a)`, base case).** The `(a)`-shaped bound
`deltaJQuadFormCov 1 levels (trivialU) A0 ≥ γ₀ ‖A0‖²` is **FALSE for every `γ₀ > 0`**, already at
`ell=1`, `U=1`: a constant nonzero bond field `A0 ≡ v` has zero flat curl (hence
`deltaJQuadFormCov = 0`) but nonzero norm — proved below
(`coercivity_ell1_trivialU_lower_bound_false`). This mirrors, on the covariant carrier,
`U1AnchorRefutation.lean`'s flat refutation. The HONEST, non-false statement of `(a)`'s base case is
the coarse-curl-relative two-sided bound of CMP95 (1.67), `γ₀‖∂₁'B‖² ≤ ⟨B,Δ_jB⟩`; at `ell=1` that is
the **tautology `γ₀=γ₁=1`** (no coarsening: the coarse curl of the coarse restriction equals the fine
curl), i.e. the 𝔰𝔲(2) analogue of the DEGENERATE flat `u1_curl_coercivity_ell_one`. So `(a)` — a
genuine `γ₀ > 0` lower bound for `deltaJQuadFormCov` — is **NOT** established even at `U=1`, and the
reduction to flat work does not shortcut it: the useful bound needs `ell ≥ 2` (genuine coarsening),
which Finding 1 shows requires first rebuilding the covariant object on a faithful `Q_k`.

## What this file BUILDS (all sorry-free; axioms = the three standard ones)

1. `flatCurlValue` / `flatCurlLM` — the `U`-independent 𝔰𝔲(2) flat curl (CMP99b (3.4) with `R≡id`).
2. `curlValueCovariant_trivialU_local` / `curlCovariantLM_trivialU_eq_flatCurlLM` — the operator-level
   `U=1` reduction of the covariant curl to the flat curl.
3. `deltaJQuadFormCov_ell1_trivialU_eq_flatCurlEnergy` — **THE `ell=1` `U=1` REDUCTION** (Finding 2).
4. `flatCurlValue_const_eq_zero` / `deltaJQuadFormCov_ell1_trivialU_const_eq_zero` /
   `coercivity_ell1_trivialU_lower_bound_false` — **THE base-case coercivity REFUTATION** (Finding 3).
-/

namespace AdalyFormal.Balaban.CovU1Reduction

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the `U`-independent 𝔰𝔲(2) flat curl -/

/-- **`flatCurlValue A p := A(x,μ) + A(shift_μ x,ν) − A(shift_ν x,μ) − A(x,ν)`** — CMP99b (3.4)'s
covariant curl with every transport factor `R(U(·)) = R(1) = id` dropped. The `U`-INDEPENDENT flat
object `curlValueCovariant (trivialU)` reduces to (proved next). -/
noncomputable def flatCurlValue (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : SuTwo :=
  A (p.1, p.2.1.1) + A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) -
    A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.2)

theorem flatCurlValue_add (A B : Bond L → SuTwo) :
    flatCurlValue (A + B) = flatCurlValue A + flatCurlValue B := by
  funext p; simp only [flatCurlValue, Pi.add_apply]; abel

theorem flatCurlValue_smul (c : ℝ) (A : Bond L → SuTwo) :
    flatCurlValue (c • A) = c • flatCurlValue A := by
  funext p; simp only [flatCurlValue, Pi.smul_apply]; simp only [smul_sub, smul_add]

/-- `flatCurl` as a genuine `LinearMap` (the flat, `U`-independent analogue of `curlCovariantLM`). -/
noncomputable def flatCurlLM : (Bond L → SuTwo) →ₗ[ℝ] (PeriodicLatticePlaquette L → SuTwo) where
  toFun := flatCurlValue
  map_add' := flatCurlValue_add
  map_smul' c A := by simp only [RingHom.id_apply]; exact flatCurlValue_smul c A

#print axioms flatCurlValue_add
#print axioms flatCurlValue_smul

/-! ## §2 — the operator-level `U=1` reduction of the covariant curl -/

/-- **`curlValueCovariant (trivialU) = flatCurlValue`, pointwise** — the transport factors
`R(U(·)) = R(1) = id` drop out. Re-proved directly for `CovariantHjMinimizer.trivialU` (there is a
SECOND, distinct `trivialU` in `DeltaPrime.lean`; this one-liner sidesteps any cross-`trivialU`
defeq worry, mirroring `DeltaKU.curlValueCovariant_trivialU`). -/
theorem curlValueCovariant_trivialU_local (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    curlValueCovariant (trivialU L) A p = flatCurlValue A p := by
  simp only [curlValueCovariant, flatCurlValue, trivialU, RMap_one, LinearMap.id_coe, id_eq]

theorem curlValueCovariant_trivialU_eq (A : Bond L → SuTwo) :
    curlValueCovariant (trivialU L) A = flatCurlValue A :=
  funext (curlValueCovariant_trivialU_local A)

/-- **`curlCovariantLM (trivialU) = flatCurlLM`** — the `U=1` reduction at the level of linear maps.
`RMap 1 = id` turns the genuinely `U`-dependent covariant curl into the flat, `U`-independent one. -/
theorem curlCovariantLM_trivialU_eq_flatCurlLM :
    curlCovariantLM (trivialU L) = (flatCurlLM : (Bond L → SuTwo) →ₗ[ℝ] _) := by
  apply LinearMap.ext
  intro A
  funext p
  exact curlValueCovariant_trivialU_local A p

#print axioms curlValueCovariant_trivialU_local
#print axioms curlCovariantLM_trivialU_eq_flatCurlLM

/-! ## §3 — THE `ell=1` `U=1` REDUCTION (Finding 2) -/

/-- **THE REDUCTION (base case of `(a)` at `U=1`, `ell=1`)**: at the trivial background and `ell=1`,
`deltaJQuadFormCov` collapses to a manifestly `U`-INDEPENDENT flat-curl energy. Composes
`deltaJQuadFormCov_ell1_eq_dstarDQuadForm` (the Schur complement is trivial at `ell=1`: no gauge
freedom to correct against) with `curlValueCovariant_trivialU_eq` (transport drops at `U=1`). This
is the honest, carrier-matched sense in which the covariant object reduces to the flat one — but
ONLY at `ell=1` (see Finding 1 for why it fails at `ell ≥ 2`). -/
theorem deltaJQuadFormCov_ell1_trivialU_eq_flatCurlEnergy (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovH 1 levels (trivialU L)).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    deltaJQuadFormCov 1 levels (trivialU L) A0 =
      covPlaqInner (flatCurlValue A0) (flatCurlValue A0) := by
  rw [deltaJQuadFormCov_ell1_eq_dstarDQuadForm]
  unfold CovariantHj.dstarDQuadForm
  rw [curlValueCovariant_trivialU_eq]

#print axioms deltaJQuadFormCov_ell1_trivialU_eq_flatCurlEnergy

/-! ## §4 — THE base-case coercivity REFUTATION (Finding 3): `(a)` as `≥ γ₀‖A0‖²` is FALSE -/

/-- A constant bond field has zero flat curl: `v + v − v − v = 0`. The kernel of the flat curl is
huge (all constants, all pure gradients) — exactly why a `≥ γ₀‖A0‖²` bound cannot hold. -/
theorem flatCurlValue_const_eq_zero (v : SuTwo) :
    flatCurlValue (fun _ : Bond L => v) = (0 : PeriodicLatticePlaquette L → SuTwo) := by
  funext p; simp only [flatCurlValue, Pi.zero_apply]; abel

/-- **The reduction, applied to a constant field, gives exactly `0`** — for EVERY `v`. -/
theorem deltaJQuadFormCov_ell1_trivialU_const_eq_zero (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovH 1 levels (trivialU L)).HasOrthogonalProjection]
    (v : SuTwo) :
    deltaJQuadFormCov 1 levels (trivialU L) (fun _ : Bond L => v) = 0 := by
  rw [deltaJQuadFormCov_ell1_trivialU_eq_flatCurlEnergy, flatCurlValue_const_eq_zero]
  simp only [covPlaqInner, Pi.zero_apply, hsInner_zero_zero, Finset.sum_const_zero]

/-- `0 < hsInner v v` for `v ≠ 0` (positive-definiteness of the Killing-form pairing). -/
private theorem hsInner_self_pos {v : SuTwo} (hv : v ≠ 0) : 0 < hsInner v v := by
  rcases lt_or_eq_of_le (hsInner_self_nonneg v) with h | h
  · exact h
  · exact absurd (hsInner_self_eq_zero h.symm) hv

/-- **THE REFUTATION: the base case of `(a)` in its `≥ γ₀‖·‖²` form is FALSE.** There is no positive
`γ₀` with `γ₀ · covBondInner A0 A0 ≤ deltaJQuadFormCov 1 levels (trivialU) A0` for all `A0`: the
constant field `A0 ≡ suTwoWitness` makes the right side `0` while the left side is strictly positive.
Mirrors `U1AnchorRefutation.lean` on the covariant carrier. Requires `Nonempty (Bond L)` (always
holds — every periodic lattice has bonds — supplied as an honest, minimal hypothesis). -/
theorem coercivity_ell1_trivialU_lower_bound_false (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovH 1 levels (trivialU L)).HasOrthogonalProjection]
    [Nonempty (Bond L)] :
    ¬ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ A0 : Bond L → SuTwo,
        γ₀ * covBondInner A0 A0 ≤ deltaJQuadFormCov 1 levels (trivialU L) A0 := by
  rintro ⟨γ₀, hγ, hbound⟩
  have hle := hbound (fun _ => suTwoWitness)
  rw [deltaJQuadFormCov_ell1_trivialU_const_eq_zero levels suTwoWitness] at hle
  have hpos : 0 < covBondInner (fun _ : Bond L => suTwoWitness) (fun _ => suTwoWitness) := by
    unfold covBondInner
    exact Finset.sum_pos (fun b _ => hsInner_self_pos suTwoWitness_ne_zero) Finset.univ_nonempty
  nlinarith [mul_pos hγ hpos]

#print axioms flatCurlValue_const_eq_zero
#print axioms deltaJQuadFormCov_ell1_trivialU_const_eq_zero
#print axioms coercivity_ell1_trivialU_lower_bound_false

end AdalyFormal.Balaban.CovU1Reduction
