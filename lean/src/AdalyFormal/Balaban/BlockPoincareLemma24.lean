/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BlockPoincare
import AdalyFormal.Balaban.LineIntegralAveraging

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# CMP96 Lemma 2.4 / `(2.128)` — the faithful STATEMENT (`d = 3`, `U=1` real sector), the PROVED
region-wide aggregate of `(2.123)` that de-islands `block_poincare`, and the precisely-named
residual `[RES-CMP96-2128-SLABLOCAL]`.

## Source pin (LAW-11: rendered pages, read directly, not the OCR text layer)

* `compute/denotation_audit/CMP96_p244_render.png` — CMP96 (Bałaban, *Propagators for Lattice Gauge
  Theories II*, CMP 1984) printed p.244: `(2.120)`–`(2.123)`.
* `compute/denotation_audit/CMP96_p245_render.png` — printed p.245: `(2.124)`–`(2.128)` and the
  statement of **Lemma 2.4**.

**Lemma 2.4 / (2.128), verbatim from the render** (`Λ = B(Λ')` a sum of blocks, `B` on `Λ`
satisfying `(2.121)` `B(Γ_{y,x})=0` for `x∈B(y)`, `y∈Λ'`, and `B=0` outside `Λ`):

> `L^{d-2} Σ_{c∈Λ'} |(Q₁B)(c)|² + Σ_p |(∂₁B)(p)|² ≥ (1/(12d²)) L^{-d-1} ‖B‖²`.

The RHS power is `L^{-d-1}` — a NEGATIVE exponent (leading minus sign, image-confirmed at high zoom
on `compute/lemma24/eq2128_zoom.png`; the same `L^{-d-1}` recurs in `(2.127)` and the intermediate
"`≥ L^{-d-1}Σ|B_μ|²`" step, internally consistent). The constant `1/(12d²)` is VOLUME-INDEPENDENT
(depends only on `d` and block side `L`). At `d = 3`, `L ↦ ell`: `L^{d-2} = ell`, `1/(12d²) = 1/108`,
`L^{-d-1} = L^{-4} = 1/ell⁴`, giving

> `ell·Σ_c |(Q₁B)(c)|² + Σ_p |(∂₁B)(p)|² ≥ (1/108)·(1/ell⁴)·‖B‖²`.   (this file's `Lemma24Conclusion`)

Here `Q₁ = LineIntegralAveraging.lineCoarseRestrict` (CONFIRMED faithful to `(2.125)`'s
`(Q₁B)(c) = Σ_{x∈B(c₋)} L^{-(d+1)} B([x,x+Le_μ])`: the module's `lineCoarseRestrict ell A b
= (1/ell⁴)·Σ_{x∈blockOf b.1.1 ell} lineIntegralValue ell A x b.2`, with `ell⁴ = L^{d+1}` at `d=3`,
`blockOf b.1.1 = B(c₋)`, `lineIntegralValue = B([x,x+ell·e_μ])`), and `∂₁ = LatticeOperators.curlValue`
(as in `BlockPoincare`). `‖B‖²` is the full fine-bond norm `Σ_{b} (B b)²`; for `B` supported on `Λ`
(the intended regime) this equals the source's `Σ_{b touching Λ}`.

## What is PROVED here, and what is a NAMED residual (disclosed precisely, no overselling)

### PROVED — `region_2123` (consumes `BlockPoincare.block_poincare`, the de-islanding).

`region_2123` sums the PROVED per-block `(2.123)` (`block_poincare`) over every coarse-lattice
centre `y ∈ CoarseLattice L ell`:

> `Σ_{y∈Λ'} Σ_{b⊂B(y)} (B b)²  ≤  3·ell³ · Σ_{y∈Λ'} Σ_{p⊂B(y)} (curlValue B p)²`.

This is the region-wide form of CMP96 `(2.123)` — one of the TWO inequalities the source cites
("The inequalities (2.123) and (2.127) imply … Lemma 2.4"). It genuinely IMPORTS and APPLIES
`block_poincare`, so `BlockPoincareLemma24` is a real consumer of the `(2.123)` brick (de-islanding
per LAW-19 / lean-glue). It controls the IN-BLOCK bond energy by the IN-BLOCK plaquette energy — the
ingredient that, in the source, absorbs `(2.127)`'s boundary-correction terms `-L^{-d}Σ_{b⊂B(c±)}`.

### NAMED RESIDUAL — `[RES-CMP96-2128-SLABLOCAL]` — the load-bearing `(2.127)` operator positivity
plus its SLAB-LOCAL combination. NOT proved here, NOT faked.

`(2.128)` is NOT obtained by GLOBALLY aggregating `(2.123)`+`(2.127)`. The naive route is measured to
FAIL, at the boundary-correction absorption: aggregating `(2.127)` over coarse bonds (×`L^{d-2}`)
gives `L^{-2}Ptot + ell·Qtot ≥ (1/3)L^{-3}Sbet - 2d·L^{-2}Sin` (`2d` = per-block incidence), whose
`Sin` correction has size `~ell^{-2}·Sin`; but `region_2123` only supplies `Ptot ≥ Sin/(3ell³)`,
i.e. it can return `~ell^{-3}·Sin`-worth of `Ptot` slack — SHORT of what is needed to cancel the
`~ell^{-2}·Sin` correction by a factor `~ell` (deterministic `sympy` check
`compute/lemma24/check_aggregation.py`: the `Sin` coefficient of `lower − need` is `≈ -6/ell² < 0`;
self-hashed in `compute/lemma24/NOTES.md`). Hence `(2.128)` is intrinsic to the source's
SLAB-LOCALIZED argument, where each block's correction is charged against ITS OWN local plaquettes
`Σ_{p⊂B(y)}` (not the global `Ptot`), so the factor-`ell` loss never occurs. The genuinely missing
analytic content is CMP96 `(2.126)→(2.127)`:

> the parenthesized terms `= L^{-2}⟨B,(Δ_{Λ'}^{L⁻¹,N} + Q'*_{Λ'}Q'_{Λ'})B⟩` on the `(d−1)`-dimensional
> cross-sectional lattice `Λ'` are `≥ L^{-d-1} Σ_{x∈Λ'} |B_μ(x)|²`

— a `(d−1)`-dimensional Neumann-Laplacian-plus-averaging operator-positivity bound, applied per
coarse bond `c = ⟨y, y+Le_μ⟩` and combined slab-locally with `(2.123)`. This operator
`Δ_{Λ'} + Q'*Q'` and its cross-sectional lattice are NOT built in this tree; `region_2123` here is
the OTHER (proved) ingredient. This file therefore delivers the faithful STATEMENT + the proved
`(2.123)`-aggregate + the precise residual, per the M3 discipline "reduce to the named missing
primitive"; it does NOT claim `(2.128)`.

### NOT claimed
`(2.128)` is ingredient 2 of the fine `U=1` coercivity chain `[(2.123)+(2.128)+(2.118)]`; it does
NOT discharge `coerc_u_main` (the `Δ_k`↔these-terms link `(2.118)` and the Δ-off-proxy are separate
steps). `Lemma24Conclusion` is stated as a `Prop`-valued `def` (a faithful TARGET), not asserted as
a theorem.
-/

namespace AdalyFormal.Balaban.BlockPoincareLemma24

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.LineIntegralAveraging

variable {L : PeriodicLatticeExtent}

/-! ## §1. The four energies of Lemma 2.4, as concrete finite sums. -/

/-- **In-block bond energy** `Σ_{y∈Λ'} Σ_{b⊂B(y)} (B b)²` — the fine bonds lying strictly inside
some block, the part of `‖B‖²` controlled by `(2.123)`. -/
noncomputable def inBlockBondEnergy (ell : ℕ) (B : Bond L → ℝ) : ℝ :=
  ∑ y ∈ CoarseLattice L ell, ∑ b ∈ bondsInBlock y ell, (B b) ^ 2

/-- **In-block plaquette (curl) energy** `Σ_{y∈Λ'} Σ_{p⊂B(y)} (∂₁B)(p)²`. -/
noncomputable def inBlockCurlEnergy (ell : ℕ) (B : Bond L → ℝ) : ℝ :=
  ∑ y ∈ CoarseLattice L ell, ∑ p ∈ plaqsInBlock y ell, (curlValue B p) ^ 2

/-- **Total coarse `Q₁` energy** `Σ_{c∈Λ'} |(Q₁B)(c)|²`, `Q₁ = lineCoarseRestrict` (faithful, (2.125)). -/
noncomputable def coarseQEnergy (ell : ℕ) (B : Bond L → ℝ) : ℝ :=
  ∑ c : CoarseBond L ell, (lineCoarseRestrict ell B c) ^ 2

/-- **Total fine curl energy** `Σ_p (∂₁B)(p)²`. -/
noncomputable def totalCurlEnergy (B : Bond L → ℝ) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, (curlValue B p) ^ 2

/-- **Full fine-bond norm** `‖B‖² = Σ_b (B b)²`. -/
noncomputable def bondNormSq (B : Bond L → ℝ) : ℝ :=
  ∑ b : Bond L, (B b) ^ 2

/-! ## §2. `region_2123` — CMP96 `(2.123)` summed over the whole coarse lattice.
This is where `BlockPoincare.block_poincare` is CONSUMED. -/

/-- **CMP96 `(2.123)`, region-wide** (`d=3`, `U=1` real sector): the total in-block bond energy is
bounded by `3·ell³` times the total in-block curl energy. Proved by summing the per-block headline
`BlockPoincare.block_poincare` over every `y ∈ CoarseLattice L ell` and pulling the block-size-only
constant `3·ell³` out of the sum. `3·ell³ = d·L^d` at `d=3` — VOLUME-INDEPENDENT.

This genuinely imports and applies `block_poincare` (de-islanding). It is the region-wide first of
the two inequalities CMP96 cites toward Lemma 2.4; the second, `(2.127)`, is the named residual
`[RES-CMP96-2128-SLABLOCAL]` (see module docstring). -/
theorem region_2123 {ell : ℕ}
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell) :
    inBlockBondEnergy ell B ≤ 3 * (ell : ℝ) ^ 3 * inBlockCurlEnergy ell B := by
  unfold inBlockBondEnergy inBlockCurlEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  exact block_poincare hstrict0 hstrict1 hstrict2 B hB y hy

#print axioms region_2123

/-! ## §3. The faithful STATEMENT of Lemma 2.4 / `(2.128)` at `d = 3`.

Stated as a `Prop`-valued `def` — a faithful TARGET for the residual to close, NOT asserted here.
Constant `(1/108)·(1/ell⁴)  =  (1/(12·3²))·L^{-d-1}` at `d=3` (`-d-1 = -4`); coarse coefficient
`ell = L^{d-2} = ell^{3-2}`. -/

/-- **CMP96 Lemma 2.4 / `(2.128)`, `d = 3`, `U=1` real sector, verbatim structure:**
`ell·Σ_c |(Q₁B)(c)|² + Σ_p |(∂₁B)(p)|²  ≥  (1/108)·(1/ell⁴)·‖B‖²`,
with `Q₁ = lineCoarseRestrict`, `∂₁ = curlValue`, `‖B‖² = Σ_b (B b)²`. Volume-independent constants
(`ell`-only). The RHS power is `L^{-d-1} = L^{-4} = 1/ell⁴` at `d=3` (the source exponent is NEGATIVE,
`L^{-d-1}`, image-confirmed on `compute/lemma24/eq2128_zoom.png` — a leading minus sign; an earlier
draft of this file mis-transcribed it as `L^{d-1} = ell²`, corrected here). This `Prop` is the target
of `[RES-CMP96-2128-SLABLOCAL]`. -/
noncomputable def Lemma24Conclusion (ell : ℕ) (B : Bond L → ℝ) : Prop :=
  (ell : ℝ) * coarseQEnergy ell B + totalCurlEnergy B
    ≥ (1 / 108) * (1 / (ell : ℝ) ^ 4) * bondNormSq B

/-- The constant of `Lemma24Conclusion` is `(1/(12d²))·L^{-d-1}` at `d=3`, `L=ell` — pinned as an
arithmetic identity so the numeral `1/108` and the NEGATIVE power `1/ell⁴` (`L^{-d-1}`, `-d-1=-4` at
`d=3`) are the source's, not free choices. -/
theorem lemma24_constant_pin (ell : ℕ) :
    (1 / 108 : ℝ) * (1 / (ell : ℝ) ^ 4)
      = (1 / (12 * (3 : ℝ) ^ 2)) * (1 / (ell : ℝ) ^ (3 + 1)) := by
  norm_num

/-- The coarse coefficient of `Lemma24Conclusion` is `L^{d-2}` at `d=3`, `L=ell` — i.e. `ell¹`. -/
theorem lemma24_coarseCoeff_pin (ell : ℕ) :
    (ell : ℝ) = (ell : ℝ) ^ (3 - 2) := by
  norm_num

#print axioms lemma24_constant_pin
#print axioms lemma24_coarseCoeff_pin

/-! ## §4. The residual, named precisely (not exposed as a tautological Prop).

`[RES-CMP96-2128-SLABLOCAL]` is the SLAB-LOCAL combination of `(2.127)` (the `(d−1)`-dim
operator-positivity `L^{-2}⟨B,(Δ_{Λ'}+Q'*Q')B⟩ ≥ L^{-d-1}Σ|B_μ|²`) with the region-wide
`(2.123)` (= `region_2123`, proved above) that closes `Lemma24Conclusion`. It is deliberately NOT
encoded as a Lean `Prop` here: an interface `Residual := Lemma24Conclusion` proved by `id` would be
pure tautology, and the FAILED global-aggregation reduction (§docstring: `region_2123` too weak by
`~ell` to absorb `(2.127)`'s boundary corrections) shows there is no honest finite reduction from
`region_2123` + an AGGREGATED `(2.127)` to
`Lemma24Conclusion`. Discharging the residual requires building the cross-sectional
`Δ_{Λ'} + Q'*Q'` operator on the `(d−1)`-dimensional lattice — not present in this tree. -/

end AdalyFormal.Balaban.BlockPoincareLemma24
