/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# CMP96 `(2.126)→(2.127)` — the cross-sectional operator positivity, REDUCED to a named Poincaré
inequality, and the precise CHARACTERIZATION of the residual `[RES-CMP96-2127-XSEC-POINCARE]`.

## Source pin (LAW-11: rendered page read directly)

`compute/denotation_audit/CMP96_p245_render.png` (CMP96, Bałaban, *Propagators for Lattice Gauge
Theories II*, CMP 1984, printed p.245), the sentence between `(2.126)` and `(2.127)`, verbatim:

> "The terms in parentheses on the right-hand side can be written as
> `L^{-2}⟨B, (Δ_{Λ'}^{L^{-1},N} + Q'*_{Λ'} Q'_{Λ'}) B⟩`, where the operators are defined on a
> `d−1`-dimensional lattice. This quadratic form is bounded from below by
> `L^{-d-1} Σ_{x∈Λ'} |B_μ(x)|²`, hence [`(2.127)`]."

**CHARACTERIZATION VERDICT (JOB 1).** On p.245 this operator lower bound is **ASSERTED — no proof,
no citation.** The sentence states the bound and immediately writes "hence `(2.127)`". It is a
genuine DEFERRAL, of exactly the same kind as the main block-spin coercivity (the `p.428`-deferred
`C*Δ_kC` bound). It is a `(d−1)`-dimensional instance of the very block-spin operator positivity that
is the campaign's central open content.

The RHS exponent is `L^{-d-1} = L^{-(d+1)}` (NEGATIVE; image-confirmed, and — see
`operator_form_iff_poincare` below — the UNIQUE exponent for which the rank-one averaging term
`Q'*Q'` cancels exactly, leaving a pure Poincaré inequality; the dispatch text's `L^{-(d-1)}` does
NOT cancel and is ruled out internally). At `d=3`: `L^{-d} = L^{-3}`, `L^{-(d+1)} = L^{-4}`,
`N = |Λ'| = L^{d-1} = L²`.

## What is PROVED here (unconditional, kernel-checked)

The `(2.126)` parenthesis, at `d=3`, with `f := B_μ : Λ' → ℝ` on the cross-section `s = Λ'`
(`|s| = L²`), `G` the first term's gradient energy `Σ_{b⊂Λ'}|∂B_μ(b)|²`, and
`meanBar := (Σ f)/|s|`, reads
`T = L^{-3}·G + L^{-2}·meanBar²`, and `(2.127)`'s claim is `T ≥ L^{-4}·Σ_x f(x)²`.

* `sq_sum_split` — the variance decomposition `Σ f² = Σ(f − meanBar)² + |s|·meanBar²` on any
  nonempty finite index set. (Reusable; LAW-19.)
* `operator_form_iff_poincare` — the EXACT reduction: given the decomposition
  `SumSq = Var + L²·meanBar²` (i.e. `N = L²`), for every real `G`,
  `L^{-3}·G + L^{-2}·meanBar² ≥ L^{-4}·SumSq  ↔  Var ≤ L·G`.
  The `meanBar²` (rank-one `Q'*Q'`) terms cancel IDENTICALLY — this is why the exponent is exactly
  `L^{-(d+1)}` — leaving the **pure cross-sectional Poincaré inequality** `Var ≤ L·G`,
  `Var = Σ(f − meanBar)²`.
* `cross_section_2127_iff_poincare` — the two combined: `(2.127)`'s bound holds iff the concrete
  variance `Σ(f − meanBar)²` is `≤ L·G`.

So `(2.127)` positivity is EXACTLY the cross-sectional Poincaré inequality `Σ(f−meanBar)² ≤ L·G`.

## The residual, NAMED and SHARPENED — `[RES-CMP96-2127-XSEC-POINCARE]`

**The Poincaré constant `L` is NOT the plain-lattice constant.** With `G` the plain nearest-neighbour
gradient energy `Σ(f(x')−f(x))²` on the `L×L` cross-section, `Var ≤ L·G` is **FALSE from `L = 10`** (threshold kernel-proved in `compute/erratum_2127`, `theorem erratum_2127`; an earlier `L ≥ 16` here understated it):
the sharp Poincaré constant of the `L×L` discrete Neumann box is `C_P = 1/(2(1−cos(π/L))) ~ L²/π²`,
so the true bound is `Var ≤ (L²/π²)·G`, weaker than `Var ≤ L·G` by a factor `~L`. Deterministic
check (two independent paths — closed-form gap and numeric eigenvalue — plus a saturating-field and a
random-field control): `compute/eq2127/numeric_2127.py` and `analyze_2127.py`
(`PYTHONHASHSEED=0`). The literal `κ=1` reading FIRES (fails) at `L=16,32,64`; the `κ=L` reading
(gradient prefactor `~L`) closes for every tested field, with the minimal prefactor
`κ*(L) = C_P/L → L/π²` growing linearly.

Hence the residual is precise: `(2.127)` holds iff `Var ≤ L·G` where `G` is **not** the plain
lattice gradient but the RG-scaled operator form `⟨B, Δ_{Λ'}^{L^{-1},N} B⟩` (lattice spacing
`L^{-1}`, superscript on `Δ`), whose gradient normalization is `~L×` the plain one. That scaling —
carried by the operator superscript `L^{-1}` and **defined earlier in CMP96, not on p.245** — is the
load-bearing deferred content. `(2.127)` is therefore **not even faithfully statable as a scalar
inequality from p.245 alone**: the operators `Δ_{Λ'}^{L^{-1},N}`, `Q'_{Λ'}` must be retrieved from
their definition page.

## NOT claimed
This file does NOT prove `(2.127)` (needs the RG-scaled `Δ_{Λ'}^{L^{-1},N}` and the sharp
cross-sectional Poincaré with constant `L` for that operator) and does NOT prove
`BlockPoincareLemma24.Lemma24Conclusion` (which additionally needs the slab-incidence combinatorics —
the second residual, `[RES-CMP96-2128-SLABLOCAL]`; the crude scalar aggregation is separately
measured to fail, `compute/lemma24/`). It delivers the faithful REDUCTION of the first residual to a
named classical inequality, per the M3 "reduce to the named missing primitive" discipline.
-/

namespace AdalyFormal.Balaban.CrossSectionPositivity

open Finset

/-! ## §1. Variance decomposition on a finite index set. -/

/-- **Variance decomposition.** On a nonempty finite index set `s`, with `meanBar := (Σ f)/|s|`,
`Σ_{x∈s} f(x)² = Σ_{x∈s} (f(x) − meanBar)² + |s|·meanBar²`. This is the algebraic content that
`SumSq = Var + N·meanBar²` in `operator_form_iff_poincare` (with `N = |s|`). -/
theorem sq_sum_split {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hs : s.Nonempty) :
    ∑ x ∈ s, (f x) ^ 2
      = (∑ x ∈ s, (f x - (∑ y ∈ s, f y) / s.card) ^ 2)
        + (s.card : ℝ) * ((∑ y ∈ s, f y) / s.card) ^ 2 := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hSne : (s.card : ℝ) ≠ 0 := ne_of_gt hcard
  set c : ℝ := (∑ y ∈ s, f y) / s.card with hc
  have hexp : ∑ x ∈ s, (f x - c) ^ 2
      = (∑ x ∈ s, (f x) ^ 2) - 2 * c * (∑ x ∈ s, f x) + (s.card : ℝ) * c ^ 2 := by
    have hpt : ∀ x, (f x - c) ^ 2 = (f x) ^ 2 - 2 * c * f x + c ^ 2 := fun x => by ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
  rw [hexp, hc]
  field_simp
  ring

#print axioms sq_sum_split

/-! ## §2. The exact reduction of `(2.127)`'s operator bound to a Poincaré inequality (`d=3`). -/

/-- **`(2.126)→(2.127)` REDUCED to Poincaré (`d=3`).** With `N = L²` (the variance decomposition
`SumSq = Var + L²·meanBar²`), for EVERY real `G` the `(2.126)` parenthesis bound is EXACTLY the
cross-sectional Poincaré inequality:
`L^{-3}·G + L^{-2}·meanBar² ≥ L^{-4}·SumSq  ↔  Var ≤ L·G`.
The `meanBar²` (rank-one `Q'*Q'`) terms cancel identically — the unique-exponent fact fixing the
RHS power as `L^{-(d+1)}`. Unconditionally true (an iff over arbitrary reals). -/
theorem operator_form_iff_poincare (L : ℝ) (hL : 0 < L)
    (G meanBar SumSq Var : ℝ) (hdecomp : SumSq = Var + L ^ 2 * meanBar ^ 2) :
    (G / L ^ 3 + meanBar ^ 2 / L ^ 2 ≥ SumSq / L ^ 4) ↔ (Var ≤ L * G) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hL4 : (0 : ℝ) < L ^ 4 := by positivity
  have hid : (G / L ^ 3 + meanBar ^ 2 / L ^ 2) - SumSq / L ^ 4
      = (L * G - Var) / L ^ 4 := by
    rw [hdecomp]; field_simp; ring
  rw [ge_iff_le, ← sub_nonneg, hid, le_div_iff₀ hL4, zero_mul, sub_nonneg]

#print axioms operator_form_iff_poincare

/-- **`(2.127)` positivity is EXACTLY the cross-sectional Poincaré inequality.** Combining the
variance decomposition with the reduction: for `f : ι → ℝ` on the cross-section `s = Λ'` with
`|s| = L²` (`= N = L^{d-1}` at `d=3`), writing `SumSq := Σ f²`, `meanBar := (Σ f)/L²`, `G` the first
term's gradient energy, the `(2.127)` bound `L^{-3}·G + L^{-2}·meanBar² ≥ L^{-4}·SumSq` holds
**iff** `Σ_{x∈s} (f(x) − meanBar)² ≤ L·G`. This is the named residual
`[RES-CMP96-2127-XSEC-POINCARE]`: a sharp Poincaré inequality with constant `L`, provably FALSE for
the plain lattice gradient (needs the RG-scaled `Δ_{Λ'}^{L^{-1},N}`; see module docstring / compute
artifacts). -/
theorem cross_section_2127_iff_poincare {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hs : s.Nonempty)
    (L G : ℝ) (hL : 0 < L) (hcard : (s.card : ℝ) = L ^ 2) :
    (G / L ^ 3 + ((∑ y ∈ s, f y) / L ^ 2) ^ 2 / L ^ 2 ≥ (∑ x ∈ s, (f x) ^ 2) / L ^ 4)
      ↔ (∑ x ∈ s, (f x - (∑ y ∈ s, f y) / s.card) ^ 2 ≤ L * G) := by
  set meanBar : ℝ := (∑ y ∈ s, f y) / s.card with hmb
  set Var : ℝ := ∑ x ∈ s, (f x - (∑ y ∈ s, f y) / s.card) ^ 2 with hvar
  have hmb' : meanBar = (∑ y ∈ s, f y) / L ^ 2 := by rw [hmb, hcard]
  have hdecomp : (∑ x ∈ s, (f x) ^ 2) = Var + L ^ 2 * meanBar ^ 2 := by
    rw [hvar, hmb, ← hcard]; exact sq_sum_split s f hs
  rw [← hmb']
  exact operator_form_iff_poincare L hL G meanBar (∑ x ∈ s, (f x) ^ 2) Var hdecomp

#print axioms cross_section_2127_iff_poincare

end AdalyFormal.Balaban.CrossSectionPositivity
