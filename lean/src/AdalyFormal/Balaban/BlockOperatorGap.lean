/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DiscreteNeumannPoincare

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# CMP96 p.242 (2.109)–(2.110): the FULL-operator spectral gap `Δ₀ + a·Q'₁*Q'₁ ≥ γ₀'`
# on a side-`L` block, with an explicit MESH-UNIFORM constant `γ₀' = c₀/L²` (`d = 3` cross-section).

## Source pin (LAW-11, page images read directly)

* **CMP96 p.242 (2.109)–(2.110)** (`compute/kimi_ceq1_gate/renders/CMP96_p242-20.png`), verbatim:
  > "For `ω` satisfying `Q'₁ω = 0` the quadratic form `‖Δ₀ω‖² = ‖Δ₀ω + aQ'₁*Q'₁ω‖²` is bounded from
  > below by `γ₀'²‖ω‖²` because **the operator `Δ₀ + aQ'₁*Q'₁` is bounded from below by `γ₀' > 0`
  > (in fact we may get `γ₀' = π²/L²`)**."

  The sentence immediately preceding places this "in momentum representation **on the unit lattice**",
  so `Δ₀` is the plain (unit-spacing) discrete Neumann Laplacian and the gap is measured against the
  plain `ℓ²` norm `‖·‖² = Σ_x |·|²`.

* **CMP96 p.245, the sentence between (2.126) and (2.127)** (`compute/xsec_operator_recon/renders/
  CMP96_p245-23.png`), verbatim:
  > "The terms in parentheses on the right-hand side can be written as
  > `L^{-2}⟨B, (Δ_{Λ'}^{L^{-1},N} + Q'*_{Λ'}Q'_{Λ'})B⟩`, where the operators are defined on a
  > `d−1`-dimensional lattice. This quadratic form is bounded from below by
  > `L^{-d-1}Σ_{x∈Λ'}|B_μ(x)|²`, hence [(2.127)]."

  Dividing by `L^{-2}`: `⟨B,(Δ+Q'*Q')B⟩ ≥ L^{-(d-1)}Σ|B|²`, at `d=3` `⟨B,MB⟩ ≥ L^{-2}ΣB²` — the SAME
  full-operator gap `γ₀' = 1/L²`, but for `Δ_{Λ'}^{L^{-1},N}` on the `L^{-1}`-spacing lattice, NOT
  literally the unit-lattice `Δ₀` of p.242 (see the CONNECTION note in §4).

## CHARACTERIZATION VERDICT (JOB 1)

The load-bearing primitive of p.242 is the **operator lower bound** `Δ₀ + a·Q'₁*Q'₁ ≥ γ₀'·I` with
`γ₀'` mesh-uniform (`γ₀' = π²/L²` sharp; any fixed `c₀/L² > 0` suffices for coercivity). Balaban
STATES it without proof. Its content is the two-mode split, exactly reproduced here:
* `Δ₀` annihilates constants and has a **first-nonzero-Neumann-eigenvalue** gap `~ 1/L²` on the
  mean-zero (fluctuation) subspace;
* `a·Q'₁*Q'₁` is the averaging term `⟨B, a Q'₁*Q'₁ B⟩ = a·(mean B)²`, supplying a positive gap on
  the **mean** mode that `Δ₀` misses.
The gap of the SUM is `min(fluctuation gap, mean gap)`.

## What is PROVED here (UNCONDITIONAL, kernel-checked, `#print axioms` sorry-free)

`d = 3` cross-section `= n×n` grid, `n = L`, plain inner product `‖B‖² = sumSq2`, `Δ₀` quadratic
form `= gradEnergy2` (plain bond-difference Neumann energy), mean `m = sum2/n²`, and the averaging
term `⟨B,aQ'*Q'B⟩ = a·m²` (`Q'B = L^{-(d-1)}ΣB = m`, so `‖Q'B‖² = m²`; CMP96 p.242/p.245 `Q'₁`).

* `sumSq2_split` — the variance decomposition `sumSq2 = var2 + n²·m²` (mean/fluctuation
  orthogonality on the `n²`-site block), obtained from `CrossSectionPositivity.sq_sum_split`.
* `block_operator_gap_general` — **THE GAP, general coupling.** For every `n ≥ 1`, `a > 0`,
  `gradEnergy2 n f + a·m² ≥ (min(1,a)/n²)·sumSq2 n f`. Mesh-uniform: the constant is
  `γ₀' = min(1,a)/L²`, degrading exactly as `1/L²` (NOT faster) whenever `a` is a fixed positive
  constant. Proof = the mean/fluctuation split: fluctuation via `var2_le_nsq`
  (`gradEnergy2 ≥ var2/n²`), mean via `a·m² ≥ min(1,a)·m²`.
* `block_operator_gap` — **THE GAP, `c₀ = 1`.** For `a ≥ 1`, `gradEnergy2 n f + a·m² ≥
  (1/n²)·sumSq2 n f`, i.e. `γ₀' = 1/L²`, `c₀ = 1`. This is the p.242 (2.110) full-operator gap in
  the unit-lattice normalization, with the explicit mesh-uniform constant the coercivity needs.

The proved constant `1/L²` is the CRUDE Neumann gap (from `var2_le_nsq`, `var2 ≤ L²·gradEnergy2`),
not the sharp `π²/L²` (which would need the sharp first Neumann eigenvalue). Per the dispatch, `c₀=1`
suffices; the sharp `π²` is not claimed.

## CONNECTION to (2.127)/Lemma 2.4 — REDUCED, NOT CLOSED (JOB 3, honest verdict)

The p.245 use requires the gap for `Δ_{Λ'}^{L^{-1},N}` on the `L^{-1}`-spacing lattice, whose
quadratic form is `⟨B,Δ_{Λ'}^{L^{-1},N}B⟩ = c·gradEnergy2` with the RG normalization `c` still
unpinned (`[RES-CMP96-2127-XSEC-POINCARE]`; the three source readings `c = L^{-1}, L^{-2}, 1` are
recorded in `DiscreteNeumannPoincare.lean`). Under the naive plain-`ℓ²` reading with `c = L^{-1}` the
fluctuation term becomes `L^{-1}·gradEnergy2 ≥ L^{-3}·var2`, which is SHORT of the required
`L^{-2}·var2` by exactly one factor of `L` — the same factor-`L` gap flagged for (2.127). The gap
closes iff the `‖B‖²` on the RHS of (2.126) is the **scaled** norm `η^{d-1}ΣB² = L^{-2}ΣB²` (`d=3`)
matching a difference-operator normalization `η^{d-3}=1`, i.e. the closure is entirely a question of
the RG measure/gradient normalization of `Δ_{Λ'}^{L^{-1},N}`. THIS FILE does NOT resolve that
normalization; it supplies the **unit-lattice positivity that the transport consumes** (p.242's own
normalization, "on the unit lattice"), which is a genuine, unconditional brick. Closing (2.127)/
`BlockPoincareLemma24.Lemma24Conclusion` remains the named residual `[RES-CMP96-2127-XSEC-POINCARE]`
(plus `[RES-CMP96-2128-SLABLOCAL]` for the slab combinatorics), owned by other lanes' files.

## L12 / S91 note
No `Nonempty`/`∃`-concluding declaration is introduced — every theorem is a plain `∀`-statement with
explicit constants; no `S91_REGISTRY.tsv` row is triggered.
-/

namespace AdalyFormal.Balaban.BlockOperatorGap

open Finset
open AdalyFormal.Balaban.DiscreteNeumannPoincare
open AdalyFormal.Balaban.CrossSectionPositivity

/-! ## §1. The block mean and the two quadratic forms. -/

/-- **Block mean** `m = (Σ_x B(x)) / |Λ'| = sum2 / n²`. This is `Q'₁ B` for
`Q'₁ B = L^{-(d-1)} Σ B` at `d = 3` (`L^{-2} = 1/n²`). -/
noncomputable def blockMean (n : ℕ) (f : ℕ → ℕ → ℝ) : ℝ := sum2 n f / (n : ℝ) ^ 2

/-- **The averaging quadratic form** `⟨B, Q'₁*Q'₁ B⟩ = ‖Q'₁ B‖² = m²`. -/
noncomputable def meanForm (n : ℕ) (f : ℕ → ℕ → ℝ) : ℝ := (blockMean n f) ^ 2

/-- **The full-operator quadratic form** `⟨B, (Δ₀ + a·Q'₁*Q'₁) B⟩ = gradEnergy2 + a·m²`, `Δ₀` the
plain unit-lattice Neumann Laplacian (quadratic form `gradEnergy2`, the plain bond-difference
energy). -/
noncomputable def blockForm (n : ℕ) (a : ℝ) (f : ℕ → ℕ → ℝ) : ℝ :=
  gradEnergy2 n f + a * meanForm n f

/-! ## §2. Mean/fluctuation orthogonal decomposition of the norm. -/

/-- **Variance decomposition** `‖B‖² = ‖fluctuation‖² + ‖mean part‖²`, i.e.
`sumSq2 = var2 + n²·m²`. The mean part `m·𝟙` carries `‖·‖² = n²·m²`; the fluctuation `B − m` carries
`var2`. Obtained from `CrossSectionPositivity.sq_sum_split` on the `n²`-site product index set. -/
theorem sumSq2_split (n : ℕ) (hn : 1 ≤ n) (f : ℕ → ℕ → ℝ) :
    sumSq2 n f = var2 n f + (n : ℝ) ^ 2 * (blockMean n f) ^ 2 := by
  have hpos : 0 < n := hn
  set f' : ℕ × ℕ → ℝ := fun p => f p.1 p.2 with hf'
  set s : Finset (ℕ × ℕ) := (range n) ×ˢ (range n) with hs_def
  have hcardnat : s.card = n * n := by rw [hs_def, Finset.card_product, card_range]
  have hcard : (s.card : ℝ) = (n : ℝ) ^ 2 := by rw [hcardnat, Nat.cast_mul, ← pow_two]
  have hs : s.Nonempty :=
    ⟨(0, 0), by rw [hs_def, Finset.mem_product]; exact ⟨mem_range.mpr hpos, mem_range.mpr hpos⟩⟩
  have hsum : ∑ p ∈ s, f' p = sum2 n f := by rw [hs_def, Finset.sum_product]; rfl
  have hsumsq : ∑ p ∈ s, (f' p) ^ 2 = sumSq2 n f := by rw [hs_def, Finset.sum_product]; rfl
  have hvar : ∑ x ∈ s, (f' x - (∑ y ∈ s, f' y) / (s.card : ℝ)) ^ 2 = var2 n f := by
    rw [hsum, hcardnat, Nat.cast_mul, ← pow_two, hs_def, Finset.sum_product, var2]
  have hsplit := sq_sum_split s f' hs
  rw [hsumsq, hvar, hsum, hcard] at hsplit
  rw [hsplit, blockMean]

/-! ## §3. The full-operator gap (JOB 2). -/

/-- **THE p.242 (2.110) FULL-OPERATOR GAP — general coupling.** On the `d=3` side-`n` (`= L`) block,
`⟨B, (Δ₀ + a·Q'₁*Q'₁) B⟩ ≥ (min(1,a)/n²)·‖B‖²` for every `n ≥ 1`, `a > 0`. The constant
`γ₀' = min(1,a)/L²` is **mesh-uniform** — it degrades exactly as `1/L²` (the fluctuation Neumann gap),
never faster, whenever `a` is a fixed positive constant. Proof: the orthogonal mean/fluctuation split
`sumSq2 = var2 + n²m²`, with the fluctuation controlled by `var2_le_nsq`
(`gradEnergy2 ≥ var2/n²`) and the mean by `a·m² ≥ min(1,a)·m²`. -/
theorem block_operator_gap_general (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a) (f : ℕ → ℕ → ℝ) :
    blockForm n a f ≥ (min 1 a / (n : ℝ) ^ 2) * sumSq2 n f := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hsplit := sumSq2_split n hn f
  have hvar_le : var2 n f ≤ (n : ℝ) ^ 2 * gradEnergy2 n f := var2_le_nsq n f
  have hvar_nonneg : (0 : ℝ) ≤ var2 n f :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hmm : (0 : ℝ) ≤ (blockMean n f) ^ 2 := sq_nonneg _
  have hmin1 : min 1 a ≤ 1 := min_le_left _ _
  have hmina : min 1 a ≤ a := min_le_right _ _
  have hmin_nonneg : (0 : ℝ) ≤ min 1 a := le_min zero_le_one ha.le
  -- fluctuation term: (min1a/n²)·var2 ≤ gradEnergy2
  have hfluc : (min 1 a / (n : ℝ) ^ 2) * var2 n f ≤ gradEnergy2 n f := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn2]
    nlinarith [hvar_le, mul_le_mul_of_nonneg_right hmin1 hvar_nonneg]
  -- mean term: (min1a/n²)·(n²·m²) = min1a·m² ≤ a·m²
  have hnR0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hmean_eq : (min 1 a / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 * (blockMean n f) ^ 2)
      = min 1 a * (blockMean n f) ^ 2 := by
    field_simp
  have hmean :
      (min 1 a / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 * (blockMean n f) ^ 2)
        ≤ a * (blockMean n f) ^ 2 := by
    rw [hmean_eq]; exact mul_le_mul_of_nonneg_right hmina hmm
  -- assemble
  rw [blockForm, meanForm, ge_iff_le, hsplit, mul_add]
  linarith [hfluc, hmean]

/-- **THE p.242 (2.110) FULL-OPERATOR GAP — `c₀ = 1`, the coercivity form.** For `a ≥ 1`,
`⟨B, (Δ₀ + a·Q'₁*Q'₁) B⟩ ≥ (1/n²)·‖B‖²` on the `d=3` side-`n` (`= L`) block. The mesh-uniform gap is
`γ₀' = 1/L²` with `c₀ = 1` — the explicit constant CMP96 p.242's positivity needs (the source's
sharp `π²/L²` is a strictly better constant, not required for coercivity and not claimed here). -/
theorem block_operator_gap (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 1 ≤ a) (f : ℕ → ℕ → ℝ) :
    blockForm n a f ≥ (1 / (n : ℝ) ^ 2) * sumSq2 n f := by
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hgen := block_operator_gap_general n hn a (by linarith : (0:ℝ) < a) f
  have hmin : min 1 a = 1 := min_eq_left ha
  rw [hmin] at hgen
  exact hgen

#print axioms sumSq2_split
#print axioms block_operator_gap_general
#print axioms block_operator_gap

end AdalyFormal.Balaban.BlockOperatorGap
