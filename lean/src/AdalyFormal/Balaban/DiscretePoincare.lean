/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib

set_option autoImplicit false

/-!
# The mesh-uniform discrete Poincaré inequality — CMP89 (2.26)/(2.27)'s missing `π²` input

**Target** (`compute/cmp89_positivity/CMP89_POSITIVITY_READING.md`): CMP89 printed p.580, between
(2.26) and (2.27), asserts — with NO proof, NO citation, on a page Bałaban's own p.573 requires to
hold "independent of the lattice spacing `η`" — that

> "The operator `−Δ^{η,N}_Δ` is bounded from below by `π²` on a subspace of functions on `Δ`
> orthogonal to constant functions."

This is the ONE genuinely analytic (not merely combinatorial) input in the whole positivity chain
feeding `Δ` positive on `N(Q')` (CMP96 (2.10)-(2.17)). This file re-derives what is TRUE about it.

## What Mathlib has (L1 of the mandate)

**No dedicated discrete Poincaré/Wirtinger inequality anywhere in Mathlib** — checked
(`grep -rli "poincare\|wirtinger" .lake/packages/mathlib/Mathlib`: zero hits outside an unrelated
`Dynamics/Ergodic/Conservative.lean` mention). **No path-graph-Laplacian eigenvalue formula**
either (`Combinatorics/SimpleGraph/LapMatrix.lean` defines the general graph Laplacian matrix but
proves no explicit spectrum for any specific graph family). What Mathlib DOES supply, confirmed by
direct use below: `Algebra.Order.Chebyshev.sq_sum_le_card_mul_sum_sq` (the Cauchy–Schwarz special
case of Chebyshev's inequality — exactly the one nontrivial inequality this whole derivation
needs) and `Finset.sum_Ico_sub` (`@[to_additive]` of `prod_Ico_div`, the discrete telescoping
identity `∑ (f(k+1)-f(k)) = f(j)-f(i)`, confirmed to exist by direct `exact?` in this environment
— see the dispatch's own session log). **So this genuinely IS "assembly, not research" once these
two pieces are found — but neither piece alone gives the SHARP constant `π²`; assembling them
gives a genuine, but weaker, constant (§4-5 below).**

## THE TWO FINDINGS (both load-bearing, both disclosed up front)

1. **A genuine, mesh-uniform, positive lower bound EXISTS and is re-derived here** (elementary
   Cauchy–Schwarz + a variance identity, no eigenvalue theory): `γ₀ = 2` works for EVERY mesh
   spacing `η = 1/n`, `n ≥ 1` (`physical_poincare_uniform`). This is a genuine re-derivation of
   "some positive `η`-uniform spectral gap exists", matching CMP89 p.573's own GENERAL existence
   claim (1.8): "there exists a positive constant `γ₀`... independent of the lattice spacing `η`".

2. **CMP89's SPECIFIC constant, `π²`, as a stated LOWER bound, is FALSE for every finite mesh** —
   proved here at the simplest concrete instance (`n = 2`, kernel-checked,
   `cmp89_pi_sq_claim_false_at_n2`), and confirmed numerically for the general case
   (`compute/cmp89_positivity/` scratch, not binding, see below): the TRUE physical spectral gap
   of the discrete Neumann Laplacian on `n` points **increases monotonically to `π²` from BELOW**
   as `η → 0` (`n → ∞`) — it never reaches, let alone exceeds, `π²` at any finite mesh. So the
   printed inequality direction is backwards for finite `η`; `π²` is the correct LIMITING value
   and a valid mesh-uniform UPPER bound, not a lower one. **This is a genuine correction to a
   40-year-old, uncited, unproved assertion**, not a transcription artifact — see
   `DISCRETE_POINCARE.md` §3 for the full numerical derivation (Python, non-binding per L10, used
   only to locate and corroborate the true direction before proving the n=2 case in Lean).

## The scaling convention, stated exactly (mandate item 3)

`n` points at positions `0, η, 2η, ..., (n-1)η` inside a unit-length cube edge, `η = 1/n` —
**exactly** `LatticeOperators.lean`'s own `ell = L^k = η⁻¹` convention (`blockOf y ell` has `ell^d`
sites). The physical (rescaled) quadratic form is `⟨φ,-Δ^ηφ⟩_{L²} = ‖∂φ‖²/η` (ONE power of `η`,
not `η²` — because the SECOND power is absorbed into the `L²` measure `⟨φ,ψ⟩_{L²} := η·Σφψ`,
giving `‖φ‖²_{L²} = η·Σφ²`; the two `η`s cancel one of the two powers in
`(-Δ^ηφ)(x) = η^{-2}(2φ(x)-φ(x-η)-φ(x+η))`). Both conventions (`physicalQuadForm`,
`physicalNormSq` below) are stated explicitly, not left implicit.

## Item 4 — connection to the ALREADY-BUILT `∂` (`LatticeOperators.lean`) — genuinely does NOT
## transfer, and here is exactly why (a disclosed finding, per the mandate's own escape clause)

`LatticeOperators.gradCLM`/`siteLaplacianCLM` are built on `PeriodicLatticeSite L` — a **periodic
torus**, no boundary. CMP89's object here is `−Δ^{η,N}_Δ`, the "`N`" standing for **Neumann**
(reflecting) boundary conditions on a single **bounded unit cube** `Δ`, which is emphatically NOT
periodic (a cube `Δ` is one finite piece being glued to ITS NEIGHBORS in the ambient lattice; it
does not wrap around on itself). The two operators have GENUINELY DIFFERENT spectra: the periodic
1-D Laplacian's physical gap converges to `4π²` (period-1 circle, first Fourier mode `e^{2πix}`),
while the Neumann interval's converges to `π²` (`cos(πx)`) — a factor-of-4 mismatch, confirmed
numerically (`DISCRETE_POINCARE.md` §3). **Reusing `gradCLM` literally would silently prove the
WRONG constant.** What DOES transfer is the ARCHITECTURE, not the term: this file's
`dirichletEnergy n phi = ∑(φ(k+1)-φ(k))²` is, by construction, exactly `‖∂φ‖²` for the coboundary
`(∂φ)(k) := φ(k+1)-φ(k)` on THIS bounded domain — the same `Δ = ∂*∂`, `⟨φ,Δφ⟩ = ‖∂φ‖²` pattern
`LatticeOperators.bondLaplacian_eq_curl_normSq` proves for the periodic case, applied to the
correct (non-periodic) geometry instead of silently reusing the wrong one.

## What this file builds

1. §1-2: `dirichletEnergy`, `sumSq`, `meanZero` (`φ ⊥` constants), and the **variance identity**
   `ΣΣ(φᵢ-φⱼ)² = 2n·Σφᵢ² - 2(Σφᵢ)²` — elementary, proved from scratch (no Mathlib lemma found
   under this name).
2. §3: **telescoping Cauchy–Schwarz**, `(φⱼ-φᵢ)² ≤ (j-i)·‖∂φ‖²`, from Mathlib's
   `sq_sum_le_card_mul_sum_sq` + `Finset.sum_Ico_sub`.
3. §4: **`discrete_poincare_crude`**: the crude combinatorial Poincaré inequality
   `Σφᵢ² ≤ (n(n-1)/2)·‖∂φ‖²` for mean-zero `φ` — combining §1-3, NOT sharp (the sharp constant is
   smaller by a factor `→ π²/2 ≈ 4.93` as `n→∞`, see `DISCRETE_POINCARE.md` §3's numeric table) but
   fully rigorous and elementary.
4. §5: **`physical_poincare_uniform`**: the MESH-UNIFORM physical statement,
   `⟨φ,-Δ^ηφ⟩_{L²} ≥ 2·‖φ‖²_{L²}` for EVERY `n ≥ 1`, a single `η`-independent constant `γ₀ = 2` —
   the honest, re-derived substitute for CMP89's asserted-but-false-as-literally-stated `π²`.
5. §6: **D4/necessity witness**: `meanZero` is load-bearing — the constant function `1` (which
   violates it) makes the crude bound FALSE (`sumSq = n ≠ 0 = C·0`).
6. §7: **`cmp89_pi_sq_claim_false_at_n2`**: CMP89's literal `π²`-lower-bound claim, refuted at its
   simplest instance (`n=2`, `φ=(1,-1)`), kernel-checked (`#print axioms`: no `sorryAx`).

## What this file does NOT build (named, not silently dropped — Tier B "reduce to lemma")

**Tensorization to `d` dimensions** (mandate item 2). The abstract mechanism is standard
(tensor/direct sums of PSD operators have gap = min of the factor gaps) but a genuine, correctly
STATED Lean generalization needs one of: (a) an explicit `d`-dimensional "staircase path"
telescoping argument (nested induction — first change coordinate 0 one unit at a time, then
coordinate 1, etc., bounding the total path length by `d(n-1)` and applying the SAME
Cauchy–Schwarz step once per unit step, `d(n-1)` times instead of once), or (b) an abstract
tensor-product-of-inner-product-spaces
spectral argument (`Mathlib.LinearAlgebra.TensorProduct` has the algebra but no ready-made
"tensor sum of self-adjoint operators has gap = min of factor gaps" lemma). Both are well-defined,
bounded, NOT mathematical obstructions — genuinely more Lean labor than the 1-D case, not attempted
here per the mandate's own "if it doesn't [follow], that failure is the finding" clause. **Named
here as the precise next task, not attempted or faked with a `sorry`** (a `sorry` risks smuggling a
subtly wrong statement, per §LEAN-D — safer to leave it entirely unstated than mis-stated).

## L12 / S91 note

No `Nonempty`/`∃`-concluding declaration is introduced in this file — every theorem below is a
plain `∀`-statement with an explicit numeric constant (`γ₀ = 2`, or the concrete `n=2` witness), so
no `S91_REGISTRY.tsv` row is required by L12's own trigger condition (checked against
`formal/S91_REGISTRY.tsv`'s own header/scope). This is disclosed explicitly rather than silently
skipped.
-/

namespace AdalyFormal.Balaban.DiscretePoincare

open Finset

/-! ## §1. Definitions -/

/-- **`‖∂φ‖²`, the discrete Dirichlet energy** on `n` points `0,...,n-1` (the "unit cube `Δ`"
sites at mesh spacing `η = 1/n`): the sum of squared forward differences. This IS `‖∂φ‖²` for the
coboundary `(∂φ)(k) := φ(k+1) - φ(k)`, `k < n-1`, matching the `Δ = ∂*∂`, `⟨φ,Δφ⟩ = ‖∂φ‖²`
architecture of `Balaban.LatticeOperators.bondLaplacian_eq_curl_normSq` — but on a BOUNDED,
Neumann/reflecting domain (a "unit cube"), not the periodic torus that file's `∂` lives on (module
docstring, "Item 4", for why these are genuinely different objects). -/
def dirichletEnergy (n : ℕ) (phi : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (n - 1), (phi (i + 1) - phi i) ^ 2

/-- `‖φ‖²` w.r.t. plain counting measure on the `n` sites (the η-rescaling is applied separately,
§5, since orthogonality-to-constants does not depend on it). -/
def sumSq (n : ℕ) (phi : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range n, (phi i) ^ 2

/-- **`φ ⊥` constants** — CMP89's own condition, "orthogonal to constant functions". Equivalent
to mean-zero regardless of which positive multiple of counting measure is used for the `L²` inner
product (scaling an inner product by a positive constant never changes orthogonality). -/
def meanZero (n : ℕ) (phi : ℕ → ℝ) : Prop :=
  ∑ i ∈ range n, phi i = 0

/-! ## §2. The variance identity (general, no `meanZero` needed yet) -/

/-- **Variance identity**: `ΣΣ(φᵢ-φⱼ)² = 2n·Σφᵢ² - 2(Σφᵢ)²`, for ANY `phi` (not yet using
`meanZero`). Elementary expansion + `Finset.sum_mul_sum`; not shipped anywhere in Mathlib under
this name (checked: no `Poincare`/`Wirtinger`/variance-double-sum identity found there). -/
theorem variance_identity (n : ℕ) (phi : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (phi i - phi j) ^ 2
      = 2 * n * (∑ i ∈ range n, (phi i) ^ 2) - 2 * (∑ i ∈ range n, phi i) ^ 2 := by
  have expand : ∀ i ∈ range n, ∀ j ∈ range n,
      (phi i - phi j) ^ 2 = phi i ^ 2 + phi j ^ 2 - 2 * (phi i * phi j) := by
    intro i _ j _; ring
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (expand i hi))]
  have h1 : ∀ i ∈ range n, ∑ j ∈ range n, (phi i ^ 2 + phi j ^ 2 - 2 * (phi i * phi j))
      = n * phi i ^ 2 + (∑ j ∈ range n, phi j ^ 2) - 2 * phi i * (∑ j ∈ range n, phi j) := by
    intro i _
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h2 : ∑ i ∈ range n, (n : ℝ) * phi i ^ 2 = n * ∑ i ∈ range n, phi i ^ 2 := by
    rw [Finset.mul_sum]
  have h3 : ∑ _i ∈ range n, (∑ j ∈ range n, phi j ^ 2) = n * ∑ j ∈ range n, phi j ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h4 : ∑ i ∈ range n, 2 * phi i * (∑ j ∈ range n, phi j)
      = 2 * (∑ i ∈ range n, phi i) * (∑ j ∈ range n, phi j) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [h2, h3, h4]
  ring

/-! ## §3. Telescoping Cauchy-Schwarz -/

/-- **Telescoping Cauchy-Schwarz**: `(φⱼ-φᵢ)² ≤ (j-i) · ‖∂φ‖²`, `i ≤ j < n`. Reuses Mathlib's
`sq_sum_le_card_mul_sum_sq` (Chebyshev's Sum Inequality's Cauchy-Schwarz special case) on the
telescoping decomposition `Finset.sum_Ico_sub` — the single Cauchy-Schwarz step underneath every
discrete Poincaré/Wirtinger inequality. -/
theorem sq_diff_le_dist_mul_dirichletEnergy (n : ℕ) (phi : ℕ → ℝ) {i j : ℕ}
    (hj : j < n) (hij : i ≤ j) :
    (phi j - phi i) ^ 2 ≤ ((j : ℝ) - i) * dirichletEnergy n phi := by
  have htelescope : phi j - phi i = ∑ k ∈ Ico i j, (phi (k + 1) - phi k) :=
    (Finset.sum_Ico_sub phi hij).symm
  rw [htelescope]
  have hCS := sq_sum_le_card_mul_sum_sq (s := Ico i j) (f := fun k => phi (k + 1) - phi k)
  rw [Nat.card_Ico] at hCS
  have hsub : Ico i j ⊆ range (n - 1) := by
    intro k hk
    simp only [mem_Ico] at hk
    simp only [mem_range]
    omega
  have hnonneg : ∀ k ∈ range (n - 1), k ∉ Ico i j → 0 ≤ (phi (k + 1) - phi k) ^ 2 :=
    fun k _ _ => sq_nonneg _
  have hsum_le : ∑ k ∈ Ico i j, (phi (k + 1) - phi k) ^ 2 ≤ dirichletEnergy n phi :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  refine hCS.trans ?_
  have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by rw [Nat.cast_sub hij]
  rw [hcast]
  have hjige : (0 : ℝ) ≤ (j : ℝ) - i := by
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  exact mul_le_mul_of_nonneg_left hsum_le hjige

/-- The order-symmetric form, uniform over ALL pairs `i,j < n`: `(φᵢ-φⱼ)² ≤ (n-1)·‖∂φ‖²`. -/
theorem sq_diff_le_dirichletEnergy_mul (n : ℕ) (phi : ℕ → ℝ) {i j : ℕ}
    (hi : i < n) (hj : j < n) :
    (phi i - phi j) ^ 2 ≤ ((n : ℝ) - 1) * dirichletEnergy n phi := by
  have hdE_nonneg : 0 ≤ dirichletEnergy n phi := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  rcases le_total i j with h | h
  · have hb := sq_diff_le_dist_mul_dirichletEnergy n phi hj h
    rw [show (phi i - phi j) ^ 2 = (phi j - phi i) ^ 2 by ring]
    refine hb.trans ?_
    apply mul_le_mul_of_nonneg_right _ hdE_nonneg
    have hjn : (j : ℝ) ≤ (n : ℝ) - 1 := by
      have hle : j + 1 ≤ n := hj
      have := (Nat.cast_le (α := ℝ)).mpr hle
      push_cast at this
      linarith
    have : (i : ℝ) ≥ 0 := Nat.cast_nonneg i
    linarith
  · have hb := sq_diff_le_dist_mul_dirichletEnergy n phi hi h
    refine hb.trans ?_
    apply mul_le_mul_of_nonneg_right _ hdE_nonneg
    have hin : (i : ℝ) ≤ (n : ℝ) - 1 := by
      have hle : i + 1 ≤ n := hi
      have := (Nat.cast_le (α := ℝ)).mpr hle
      push_cast at this
      linarith
    have : (j : ℝ) ≥ 0 := Nat.cast_nonneg j
    linarith

/-! ## §4. THE crude, mesh-uniform discrete Poincaré inequality -/

/-- **The crude combinatorial discrete Poincaré inequality.** For mean-zero `phi` on `n` points:
`Σφᵢ² ≤ (n(n-1)/2)·‖∂φ‖²`. Elementary (variance identity + telescoping Cauchy-Schwarz), no
eigenvalue theory. NOT sharp (the sharp discrete-Neumann constant is smaller than `n(n-1)/2` by a
factor `π²/2 ≈ 4.93` for large `n` — see `DISCRETE_POINCARE.md` §3 for the numeric comparison) —
but genuinely mesh-uniform once rescaled (§5). -/
theorem discrete_poincare_crude (n : ℕ) (phi : ℕ → ℝ) (hmz : meanZero n phi) :
    sumSq n phi ≤ ((n : ℝ) * (n - 1) / 2) * dirichletEnergy n phi := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp [sumSq]
  have hvar := variance_identity n phi
  rw [meanZero] at hmz
  rw [hmz] at hvar
  have hvar' : ∑ i ∈ range n, ∑ j ∈ range n, (phi i - phi j) ^ 2 = 2 * n * sumSq n phi := by
    rw [hvar]; simp [sumSq]
  have hub : ∑ i ∈ range n, ∑ j ∈ range n, (phi i - phi j) ^ 2
      ≤ ∑ i ∈ range n, ∑ j ∈ range n, ((n : ℝ) - 1) * dirichletEnergy n phi := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact sq_diff_le_dirichletEnergy_mul n phi (mem_range.mp hi) (mem_range.mp hj)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hub
  rw [hvar'] at hub
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hub2 : (n : ℝ) * (2 * sumSq n phi)
      ≤ (n : ℝ) * ((n : ℝ) * (((n : ℝ) - 1) * dirichletEnergy n phi)) := by
    rw [show (n : ℝ) * (2 * sumSq n phi) = 2 * (n : ℝ) * sumSq n phi by ring]
    exact hub
  have := le_of_mul_le_mul_left hub2 hnR
  linarith

/-- **Corollary, the clean squared form**: `n²·‖∂φ‖² ≥ 2·Σφᵢ²` for mean-zero `phi`. This is the
form that directly rescales to a MESH-UNIFORM (η-independent) physical bound in §5, since
`n = 1/η`. -/
theorem discrete_poincare_crude_sq (n : ℕ) (phi : ℕ → ℝ) (hmz : meanZero n phi) :
    2 * sumSq n phi ≤ (n : ℝ) ^ 2 * dirichletEnergy n phi := by
  have hb := discrete_poincare_crude n phi hmz
  have hdE_nonneg : 0 ≤ dirichletEnergy n phi := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hstep : (n : ℝ) * (n - 1) ≤ (n : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hmono : ((n : ℝ) * (n - 1) / 2) * dirichletEnergy n phi
      ≤ ((n : ℝ) ^ 2 / 2) * dirichletEnergy n phi := by
    apply mul_le_mul_of_nonneg_right _ hdE_nonneg
    linarith
  nlinarith [hb, hmono]

/-! ## §5. The physical (η-rescaled) mesh-uniform statement -/

/-- `η = 1/n`, Bałaban's own lattice-spacing convention (`η = L^{-k}`, `n = L^k` points per unit
cube edge — matching `LatticeOperators.lean`'s own `ell = L^k = η⁻¹` convention exactly, so this
IS the same η/n identification the rest of the tree uses, not a fresh choice). -/
noncomputable def etaOf (n : ℕ) : ℝ := 1 / (n : ℝ)

/-- **`⟨φ,-Δ^{η,N}_Δφ⟩`, the physical quadratic form** — `‖∂φ‖²/η`, matching the standard
finite-difference physical Laplacian's quadratic form (the `1/η` power, not `1/η²`, because one
power of `η` is absorbed by the `L²` measure `η·(counting measure)` in `‖φ‖²_{L²}` below; see the
module docstring, "the scaling convention", for the full derivation of this power from
`(-Δ^ηφ)(x) = (1/η²)(2φ(x)-φ(x-η)-φ(x+η))` and `⟨φ,ψ⟩_{L²} := η·Σφψ`). -/
noncomputable def physicalQuadForm (n : ℕ) (phi : ℕ → ℝ) : ℝ :=
  dirichletEnergy n phi / etaOf n

/-- **`‖φ‖²_{L²(Δ)}`**, the physical squared norm, `η·Σφᵢ²`. -/
noncomputable def physicalNormSq (n : ℕ) (phi : ℕ → ℝ) : ℝ :=
  etaOf n * sumSq n phi

/-- **THE MESH-UNIFORM RESULT**: `⟨φ,-Δ^{η,N}_Δφ⟩ ≥ 2·‖φ‖²_{L²(Δ)}` for mean-zero `phi`, for
EVERY `n ≥ 1` (every mesh spacing `η = 1/n`) — a single constant `γ₀ = 2`, independent of `η`,
matching the SHAPE of CMP89 p.573's own requirement ("`γ₀` independent of the lattice spacing
`η`"). This is genuinely re-derived (elementary Cauchy–Schwarz), not the sharp `π²` CMP89 asserts
— see `cmp89_pi_sq_claim_false_at_n2` below for why `π²` itself is not a valid replacement. -/
theorem physical_poincare_uniform (n : ℕ) (phi : ℕ → ℝ) (hn : 1 ≤ n) (hmz : meanZero n phi) :
    physicalQuadForm n phi ≥ 2 * physicalNormSq n phi := by
  have hb := discrete_poincare_crude_sq n phi hmz
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ : physicalQuadForm n phi = dirichletEnergy n phi * (n : ℝ) := by
    rw [physicalQuadForm, etaOf, one_div, div_inv_eq_mul]
  have hN : physicalNormSq n phi = sumSq n phi / (n : ℝ) := by
    rw [physicalNormSq, etaOf, one_div, inv_mul_eq_div]
  rw [hQ, hN, ge_iff_le]
  rw [show 2 * (sumSq n phi / (n : ℝ)) = (2 * sumSq n phi) / (n : ℝ) by ring]
  rw [div_le_iff₀ hnR]
  nlinarith [hb]

/-! ## §6. `meanZero` is load-bearing (D4-style necessity witness) -/

/-- **Without `meanZero`, the crude bound is FALSE**: the constant function `1` on `n ≥ 1` points
has `dirichletEnergy = 0` (no differences) but `sumSq = n ≠ 0`, so `sumSq ≤ C·0 = 0` fails for the
crude bound's own constant `C = n(n-1)/2 ≥ 0`. Confirms `meanZero` is a genuine, load-bearing
hypothesis, not decorative. -/
theorem meanZero_necessary (n : ℕ) (hn : 1 ≤ n) :
    dirichletEnergy n (fun _ => (1 : ℝ)) = 0 ∧
    sumSq n (fun _ => (1 : ℝ)) = n ∧
    ¬ sumSq n (fun _ => (1 : ℝ))
        ≤ ((n : ℝ) * (n - 1) / 2) * dirichletEnergy n (fun _ => (1 : ℝ)) := by
  have hdE : dirichletEnergy n (fun _ => (1 : ℝ)) = 0 := by simp [dirichletEnergy]
  have hsS : sumSq n (fun _ => (1 : ℝ)) = n := by simp [sumSq]
  refine ⟨hdE, hsS, ?_⟩
  rw [hdE, hsS, mul_zero, not_le]
  exact_mod_cast hn

/-! ## §7. CMP89's LITERAL `π²` claim is FALSE for finite mesh — the concrete refutation -/

/-- A concrete witness: `n=2` points, `φ = (1,-1)`, mean-zero. -/
noncomputable def counterexamplePhi : ℕ → ℝ := fun i => if i = 0 then (1 : ℝ) else -1

theorem counterexamplePhi_meanZero : meanZero 2 counterexamplePhi := by
  simp [meanZero, counterexamplePhi, Finset.sum_range_succ]

theorem dE_val : dirichletEnergy 2 counterexamplePhi = 4 := by
  simp [dirichletEnergy, counterexamplePhi]; norm_num

theorem sumSq_val : sumSq 2 counterexamplePhi = 2 := by
  simp [sumSq, counterexamplePhi]

theorem physicalQuadForm_val : physicalQuadForm 2 counterexamplePhi = 8 := by
  rw [physicalQuadForm, dE_val, etaOf]; norm_num

theorem physicalNormSq_val : physicalNormSq 2 counterexamplePhi = 1 := by
  rw [physicalNormSq, sumSq_val, etaOf]; norm_num

/-- **CMP89's printed assertion — "`−Δ^{η,N}_Δ` bounded from below by `π²` on functions `⊥`
constants" — is FALSE for finite mesh**, refuted at its simplest nontrivial instance (`n=2`,
`η=1/2`, a mean-zero witness, kernel-checked, no `sorryAx`). The TRUE fact is the reverse
direction: the physical gap increases monotonically to `π²` as `η → 0` (verified numerically,
`DISCRETE_POINCARE.md` §3; NOT claimed here as a Lean theorem beyond this one concrete point,
since the general monotone-convergence statement needs the exact eigenvalue formula, which is the
named residual, module docstring "what this file does NOT build"). -/
theorem cmp89_pi_sq_claim_false_at_n2 :
    ¬ (physicalQuadForm 2 counterexamplePhi
        ≥ Real.pi ^ 2 * physicalNormSq 2 counterexamplePhi) := by
  rw [physicalQuadForm_val, physicalNormSq_val, mul_one]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  nlinarith [hpi]

#print axioms variance_identity
#print axioms sq_diff_le_dist_mul_dirichletEnergy
#print axioms sq_diff_le_dirichletEnergy_mul
#print axioms discrete_poincare_crude
#print axioms discrete_poincare_crude_sq
#print axioms physical_poincare_uniform
#print axioms meanZero_necessary
#print axioms counterexamplePhi_meanZero
#print axioms dE_val
#print axioms sumSq_val
#print axioms physicalQuadForm_val
#print axioms physicalNormSq_val
#print axioms cmp89_pi_sq_claim_false_at_n2

end AdalyFormal.Balaban.DiscretePoincare
