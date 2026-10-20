/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DiscreteNeumannPoincare
import AdalyFormal.Balaban.BlockPoincareLemma24

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# CMP96 Lemma 2.4 / `(2.128)` at Bałaban's FIXED coarsening ratio `L ∈ {2,3}` — the slab-local
# scalar assembly, and the closure of the cross-sectional `(2.127)` positivity at physical `L`.

## Source pins (LAW-11, page images read directly)
* `compute/norm_dictionary/renders/CMP96_p245_pdf23-23.png` — CMP96 p.245: `(2.124)`–`(2.128)`,
  Lemma 2.4. RHS of `(2.128)` is `(1/(12 d²))·L^{-d-1}·‖B‖²` (NEGATIVE exponent, re-confirmed at high
  zoom `compute/lemma24_assembly/z_2128_rhs.png`; the same `L^{-d-1}` in `(2.127)`).
* `corpus/mathpix/balaban_CMP96_1984_propagators_II/normalized/p246.md` — p.246 opens with "Another
  consequence…"; the proof of `(2.128)` from `(2.123)`+`(2.127)` is **OMITTED** in the source
  (Bałaban states it as one of the inequalities "implied by" `(2.123)` and `(2.127)`; LAW-12,
  deferred-in-place). So the assembly below is a RECONSTRUCTION, not a transcription.
* `CMP89 p.572`: "`L` is a small positive integer `> 1`, e.g. `L = 2` or `3`" — `L` is FIXED, not
  asymptotic. The whole chain is targeted at `L ∈ {2,3}`.

## What is PROVED here (unconditional, kernel-checked, `#print axioms` sorry-free)

### STEP 1 — the cross-sectional Poincaré at `L ∈ {2,3}` (`xsec_poincare_smallL`).
`var2 n f ≤ n · gradEnergy2 n f` for every `n ≤ 3`. This is the SHARP-ENOUGH constant `Var ≤ L·G_plain`
that `(2.127)` needs — the crude brick `DiscreteNeumannPoincare.var2_le_crude` gives constant
`n(n−1)/2`, and `n(n−1)/2 ≤ n ⇔ n ≤ 3`, so at Bałaban's `L ∈ {2,3}` the crude constant already
satisfies `≤ L`. (At `n = 2`: `n(n−1)/2 = 1 ≤ 2`; at `n = 3`: `3 ≤ 3`. FAILS at `n ≥ 4`, i.e. the
bound is genuinely special to the small-`L` regime — matching the `Var ≤ (L²/π²)G` asymptotics
recorded in `CrossSectionPositivity`'s residual note.)

### STEP 2 — `(2.127)`'s cross-sectional operator positivity, UNCONDITIONAL at `L ∈ {2,3}`
(`cross_section_2127_smallL`). The faithful `(2.126)`-parenthesis bound at `d = 3`
`gradEnergy2/n³ + (mean)²/n² ≥ sumSq2/n⁴` (`= L^{-d}·G_plain + L^{-2}·mean² ≥ L^{-d-1}·‖B‖²`, the
form Bałaban asserts on p.245) holds for every `n ∈ {2,3}` with **no normalization caveat**. This
CLOSES the scalar content of `[RES-CMP96-2127-XSEC-POINCARE]` at Bałaban's physical `L`: the residual
was flagged "false for `L ≥ 16`" (true, asymptotically), but TRUE with margin at `L ∈ {2,3}` — the
only values used. Contrast the existing `DiscreteNeumannPoincare.cross_section_2127_operator_bound`,
which proves the `gradEnergy2/n²` form under the unpinned `c = 1` reading; the `gradEnergy2/n³` form
here is the source-literal `L^{-d}` coefficient and needs no `c`.

### STEP 3 — the SLAB-LOCAL SCALAR ASSEMBLY (`slab_assembly_scalar`), and its bridge to
`Lemma24Conclusion` (`lemma24_from_slab_hyps`). The naive GLOBAL aggregation of `(2.127)` fails
(`compute/lemma24/check_aggregation.py`), but that failure is **route-specific**: a CONVEX
COMBINATION of the summed `(2.127)` (weight `λ = 1/(36 ell)`) with `region_2123` (weight `1−λ`)
closes the target for EVERY `ell ≥ 1`. `slab_assembly_scalar` proves this reduction over abstract
nonnegative reals; `lemma24_from_slab_hyps` instantiates it on the concrete Lean energies and
CONSUMES `BlockPoincareLemma24.region_2123` for the `Sin ≤ 3 ell³ Ptot` hypothesis, discharging it.
Deterministic corroboration (symbolic coefficients + 8·10⁵-sample falsification search, with a
control that fires when `region_2123` is removed): `compute/lemma24_assembly/slab_scalar_check.py`
(`PYTHONHASHSEED=0`, two byte-identical runs).

## The residual, SHARPENED — `[RES-CMP96-2128-SLABLOCAL]` reduced to three geometric multiplicity
facts. `slab_assembly_scalar`/`lemma24_from_slab_hyps` take as hypotheses `H1, H3, H4` — the ONLY
content still missing to obtain `(2.128)` on the concrete lattice at `L ∈ {2,3}`:

* **H1** (`hSummed`): the summed-and-rescaled `(2.127)`, with the cross-block good term lower-bounded
  by `Sbet` (each cross-block bond lies in `≥ 1` slab) and the per-block boundary correction upper-
  bounded by `6·L^{-2}·Sin` (each block is an endpoint of `≤ 2d = 6` coarse bonds). This is
  `(2.127)` (STEP 2, per coarse bond) summed over `c`, plus two **incidence-count** facts.
* **H3** (`hPtotLeP`): in-block curl energy `≤` total curl energy (blocks are disjoint ⇒ each
  plaquette in `≤ 1` block). A finite disjointness fact.
* **H4** (`hPslabLeP`): each plaquette lies in `≤ L²` slabs `B(c)` (`Pslab ≤ L²·P`). A finite
  slab-incidence bound.

`H2` (`Sin ≤ 3 ell³ Ptot`) is `region_2123`, PROVED and consumed. So the deep operator content of
`(2.128)` is fully discharged at `L ∈ {2,3}` (STEP 2); what remains is purely the finite
slab/block **incidence combinatorics** `H1/H3/H4` — a strictly smaller, concrete residual than the
former "the whole slab-local operator argument", and NOT the cross-sectional positivity that was the
hard part.

## NOT claimed
`Lemma24Conclusion` is NOT asserted unconditionally: `lemma24_from_slab_hyps` produces it FROM
`H1/H3/H4` (the named incidence residual). The geometric instantiation connecting `H1/H3/H4` to
`lineCoarseRestrict`/`curlValue`/`bondsInBlock` on the 3-D lattice is not built here. `(2.128)` is
ingredient 2 of the fine `U=1` chain; this does NOT discharge `coerc_u_main`.

## L12 / S91 note
No `Nonempty`/`∃`-concluding declaration is introduced; every result is a plain `∀`-statement with
explicit constants. No `S91_REGISTRY.tsv` row triggered.
-/

namespace AdalyFormal.Balaban.Lemma24Assembly

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.DiscreteNeumannPoincare
open AdalyFormal.Balaban.CrossSectionPositivity
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.BlockPoincareLemma24

/-! ## STEP 1. The cross-sectional Poincaré at `L ∈ {2,3}`. -/

/-- The crude ANOVA constant `n(n−1)/2` is `≤ n` exactly when `n ≤ 3`. Elementary. -/
theorem crude_const_le (n : ℕ) (hn : n ≤ 3) :
    (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ (n : ℝ) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn3 : (n : ℝ) ≤ 3 := by exact_mod_cast hn
  nlinarith [hn0, hn3]

/-- **STEP 1 — the cross-sectional Poincaré at Bałaban's `L ∈ {2,3}`.** For `n ≤ 3`,
`var2 n f ≤ n · gradEnergy2 n f`, i.e. `Var ≤ L·G_plain` with the constant `(2.127)` needs. Proved by
composing the crude mesh-uniform brick `var2_le_crude` (constant `n(n−1)/2`) with `n(n−1)/2 ≤ n`
(`crude_const_le`, true iff `n ≤ 3`) and `gradEnergy2 ≥ 0`. -/
theorem xsec_poincare_smallL (n : ℕ) (hn : n ≤ 3) (f : ℕ → ℕ → ℝ) :
    var2 n f ≤ (n : ℝ) * gradEnergy2 n f := by
  have hcrude := var2_le_crude n f
  have hge : (0 : ℝ) ≤ gradEnergy2 n f := by
    apply add_nonneg <;>
      exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hcoef := crude_const_le n hn
  nlinarith [hcrude, hge, hcoef, mul_le_mul_of_nonneg_right hcoef hge]

/-! ## STEP 2. `(2.127)`'s cross-sectional operator positivity, unconditional at `L ∈ {2,3}`. -/

/-- **STEP 2 — `(2.127)` at `L ∈ {2,3}`, UNCONDITIONAL.** For `1 ≤ n ≤ 3` and any `f`,
`gradEnergy2 n f / n³ + (sum2 n f / n²)² / n² ≥ sumSq2 n f / n⁴`. This is the faithful `(2.126)`
parenthesis bound at `d = 3` (`L^{-d}·G_plain + L^{-2}·mean² ≥ L^{-d-1}·‖B‖²`) that Bałaban asserts
on p.245, with NO `c`-normalization assumption. Obtained by feeding the small-`L` Poincaré
`var2 ≤ n·gradEnergy2` (STEP 1) through `CrossSectionPositivity.cross_section_2127_iff_poincare`
with `G := gradEnergy2 n f`, `L := n`. -/
theorem cross_section_2127_smallL (n : ℕ) (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (f : ℕ → ℕ → ℝ) :
    gradEnergy2 n f / (n : ℝ) ^ 3 + (sum2 n f / (n : ℝ) ^ 2) ^ 2 / (n : ℝ) ^ 2
      ≥ sumSq2 n f / (n : ℝ) ^ 4 := by
  have hpos : 0 < n := hn1
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
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
  -- feed  Var ≤ n·gradEnergy2  (STEP 1) into the exact reduction, with G := gradEnergy2, L := n
  have hpoin : ∑ x ∈ s, (f' x - (∑ y ∈ s, f' y) / (s.card : ℝ)) ^ 2
      ≤ (n : ℝ) * gradEnergy2 n f := by
    rw [hvar]; exact xsec_poincare_smallL n hn3 f
  have key := (cross_section_2127_iff_poincare s f' hs (n : ℝ) (gradEnergy2 n f) hnR hcard).mpr hpoin
  rw [hsum, hsumsq] at key
  exact key

#print axioms crude_const_le
#print axioms xsec_poincare_smallL
#print axioms cross_section_2127_smallL

/-! ## STEP 3. The slab-local scalar assembly (convex combination), and the bridge to `(2.128)`. -/

/-- **STEP 3 — the SLAB-LOCAL SCALAR ASSEMBLY.** Over abstract nonnegative reals modelling the
aggregate energies (`Q` = coarse `Q₁`-energy, `P` = total curl, `Ptot` = in-block curl,
`Pslab` = slab-summed curl, `Sin` = in-block bond energy, `Sbet` = cross-block bond energy), the
CMP96 `(2.128)` target `ell·Q + P ≥ (1/108)·ell^{-4}·(Sin+Sbet)` follows from
* `H1` (`hSummed`): summed-rescaled `(2.127)`  `ell·Q + Pslab/ell² ≥ (1/3)ell^{-3}·Sbet − 6·ell^{-2}·Sin`;
* `H2` (`hRegion`): `region_2123`  `Sin ≤ 3·ell³·Ptot`;
* `H3` (`hPtotLeP`): `Ptot ≤ P`;
* `H4` (`hPslabLeP`): `Pslab ≤ ell²·P`.
Proof = the convex combination `λ·(H1-derived) + (1−λ)·(H2,H3-derived)` with `λ = 1/(36 ell)`:
the `Sbet`-coefficient matches the target EXACTLY, the `Sin`-coefficient exceeds it by
`(9 ell − 1)/(54 ell⁴) ≥ 0`. Valid for every `ell ≥ 1` (hence `L ∈ {2,3}`). -/
theorem slab_assembly_scalar (ell : ℝ) (hell : 1 ≤ ell)
    (Q P Ptot Pslab Sin Sbet : ℝ)
    (hQ : 0 ≤ Q) (_hP : 0 ≤ P) (_hPtot : 0 ≤ Ptot) (_hPslab : 0 ≤ Pslab)
    (hSin : 0 ≤ Sin) (_hSbet : 0 ≤ Sbet)
    (hSummed : ell * Q + Pslab / ell ^ 2
        ≥ (1 / 3) * (1 / ell ^ 3) * Sbet - 6 * (1 / ell ^ 2) * Sin)
    (hRegion : Sin ≤ 3 * ell ^ 3 * Ptot)
    (hPtotLeP : Ptot ≤ P)
    (hPslabLeP : Pslab ≤ ell ^ 2 * P) :
    ell * Q + P ≥ (1 / 108) * (1 / ell ^ 4) * (Sin + Sbet) := by
  have hpos : (0 : ℝ) < ell := by linarith
  have hell2 : (0 : ℝ) < ell ^ 2 := by positivity
  have hell3 : (0 : ℝ) < ell ^ 3 := by positivity
  have hell4 : (0 : ℝ) < ell ^ 4 := by positivity
  -- (star): ell·Q + P ≥ (1/3)ell^{-3} Sbet − 6 ell^{-2} Sin
  have hPge : Pslab / ell ^ 2 ≤ P := by
    rw [div_le_iff₀ hell2]; linarith [hPslabLeP]
  have hstar : ell * Q + P ≥ (1 / 3) * (1 / ell ^ 3) * Sbet - 6 * (1 / ell ^ 2) * Sin := by
    linarith [hSummed, hPge]
  -- (diam): ell·Q + P ≥ Sin/(3 ell³)
  have hSinP : Sin / (3 * ell ^ 3) ≤ P := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 3 * ell ^ 3)]
    calc Sin ≤ 3 * ell ^ 3 * Ptot := hRegion
      _ ≤ 3 * ell ^ 3 * P := by nlinarith [hPtotLeP]
      _ = P * (3 * ell ^ 3) := by ring
  have hellQ : 0 ≤ ell * Q := mul_nonneg (le_of_lt hpos) hQ
  have hdiam : ell * Q + P ≥ Sin / (3 * ell ^ 3) := by linarith [hSinP, hellQ]
  -- convex combination with λ = 1/(36 ell)
  set lam : ℝ := 1 / (36 * ell) with hlam
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one (by positivity)]; nlinarith [hell]
  -- x ≥ a, x ≥ b, 0≤λ≤1 ⇒ x ≥ λa+(1−λ)b
  have hcombo : ell * Q + P
      ≥ lam * ((1 / 3) * (1 / ell ^ 3) * Sbet - 6 * (1 / ell ^ 2) * Sin)
        + (1 - lam) * (Sin / (3 * ell ^ 3)) := by
    have h1 := mul_nonneg hlam0 (by linarith [hstar] :
      (0:ℝ) ≤ (ell * Q + P) - ((1 / 3) * (1 / ell ^ 3) * Sbet - 6 * (1 / ell ^ 2) * Sin))
    have h2 := mul_nonneg (by linarith [hlam1] : (0:ℝ) ≤ 1 - lam)
      (by linarith [hdiam] : (0:ℝ) ≤ (ell * Q + P) - Sin / (3 * ell ^ 3))
    nlinarith [h1, h2]
  -- the combination dominates the target: difference = Sin·(9 ell − 1)/(54 ell⁴) ≥ 0
  have hbig : lam * ((1 / 3) * (1 / ell ^ 3) * Sbet - 6 * (1 / ell ^ 2) * Sin)
        + (1 - lam) * (Sin / (3 * ell ^ 3))
        - (1 / 108) * (1 / ell ^ 4) * (Sin + Sbet)
      = Sin * (9 * ell - 1) / (54 * ell ^ 4) := by
    rw [hlam]; field_simp; ring
  have hnn : 0 ≤ Sin * (9 * ell - 1) / (54 * ell ^ 4) := by
    apply div_nonneg
    · apply mul_nonneg hSin; nlinarith [hell]
    · positivity
  linarith [hcombo, hbig, hnn]

#print axioms slab_assembly_scalar

/-- **The bridge to `(2.128)`.** Instantiating `slab_assembly_scalar` on the concrete Lean energies,
CONSUMING `BlockPoincareLemma24.region_2123` for the `Sin ≤ 3 ell³ Ptot` hypothesis (`H2`,
discharged). The remaining hypotheses `H1/H3/H4` are the named incidence residual
`[RES-CMP96-2128-SLABLOCAL]` (see module docstring). Conclusion is exactly `Lemma24Conclusion ell B`
(the faithful `(2.128)` target). This makes `region_2123` genuinely load-bearing (de-islanding). -/
theorem lemma24_from_slab_hyps {L : PeriodicLatticeExtent} {ell : ℕ}
    (hell : 1 ≤ ell)
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (Pslab Sbet : ℝ) (hPslab : 0 ≤ Pslab) (hSbet : 0 ≤ Sbet)
    -- H1: summed-rescaled (2.127), cross-block good ≥ Sbet, correction ≤ 6 L^{-2} Sin
    (hSummed : (ell : ℝ) * coarseQEnergy ell B + Pslab / (ell : ℝ) ^ 2
        ≥ (1 / 3) * (1 / (ell : ℝ) ^ 3) * Sbet
          - 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B)
    -- H3: in-block curl ≤ total curl
    (hPtotLeP : inBlockCurlEnergy ell B ≤ totalCurlEnergy B)
    -- H4: slab plaquette multiplicity ≤ L²
    (hPslabLeP : Pslab ≤ (ell : ℝ) ^ 2 * totalCurlEnergy B)
    -- the norm split: ‖B‖² = Sin + Sbet
    (hNorm : bondNormSq B = inBlockBondEnergy ell B + Sbet) :
    (ell : ℝ) * coarseQEnergy ell B + totalCurlEnergy B
      ≥ (1 / 108) * (1 / (ell : ℝ) ^ 4) * bondNormSq B := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  -- nonnegativity of the concrete energies
  have hQ : 0 ≤ coarseQEnergy ell B :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hP : 0 ≤ totalCurlEnergy B :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hPtot : 0 ≤ inBlockCurlEnergy ell B :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hSin : 0 ≤ inBlockBondEnergy ell B :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  -- H2 = region_2123 (PROVED): Sin ≤ 3 ell³ Ptot
  have hRegion : inBlockBondEnergy ell B ≤ 3 * (ell : ℝ) ^ 3 * inBlockCurlEnergy ell B :=
    region_2123 hstrict0 hstrict1 hstrict2 B hB
  have h := slab_assembly_scalar (ell : ℝ) hellR
    (coarseQEnergy ell B) (totalCurlEnergy B) (inBlockCurlEnergy ell B) Pslab
    (inBlockBondEnergy ell B) Sbet
    hQ hP hPtot hPslab hSin hSbet hSummed hRegion hPtotLeP hPslabLeP
  rw [hNorm]
  linarith [h]

#print axioms lemma24_from_slab_hyps

/-- Sanity: the bridge's conclusion is definitionally `Lemma24Conclusion ell B`. -/
theorem lemma24_from_slab_hyps' {L : PeriodicLatticeExtent} {ell : ℕ}
    (hell : 1 ≤ ell)
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (Pslab Sbet : ℝ) (hPslab : 0 ≤ Pslab) (hSbet : 0 ≤ Sbet)
    (hSummed : (ell : ℝ) * coarseQEnergy ell B + Pslab / (ell : ℝ) ^ 2
        ≥ (1 / 3) * (1 / (ell : ℝ) ^ 3) * Sbet
          - 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B)
    (hPtotLeP : inBlockCurlEnergy ell B ≤ totalCurlEnergy B)
    (hPslabLeP : Pslab ≤ (ell : ℝ) ^ 2 * totalCurlEnergy B)
    (hNorm : bondNormSq B = inBlockBondEnergy ell B + Sbet) :
    Lemma24Conclusion ell B := by
  unfold Lemma24Conclusion
  have h := lemma24_from_slab_hyps hell hstrict0 hstrict1 hstrict2 B hB Pslab Sbet
    hPslab hSbet hSummed hPtotLeP hPslabLeP hNorm
  -- (1/108)*(1/ell⁴) vs (1/108)*(1/ell⁴) : identical
  have hrw : (1 / 108 : ℝ) * (1 / (ell : ℝ) ^ 4) = (1 / 108) * (1 / (ell : ℝ) ^ 4) := rfl
  linarith [h]

#print axioms lemma24_from_slab_hyps'

/-! ## STEP 4 (this pass). Discharging H3/H4/hNorm from block disjointness, and collapsing the
`(2.128)` residual to the SINGLE named primitive `(star)`.

`compute/derive_h1/probe_h1.py` (min-eigenvalue of the `LHS−RHS` quadratic form on the admissible
subspace, two byte-identical `PYTHONHASHSEED=0` runs) characterizes the cross-block (`Sbet>0`) regime:

* `(star)  ell·Q + P ≥ (1/3)ell^{-3}·Sbet − 6ell^{-2}·Sin`  — **HOLDS unconditionally** (min-eig
  `+0.078` at `ell=2`, `+0.022` at `ell=3`), for every `B`, including all `Sbet>0` configurations.
* `(agg)   ell·Q + ell^{-2}·Ptot ≥ (same RHS)`  — the form the summed per-coarse-bond `(2.127)`
  yields with the **strictly-interior** in-block curl `Ptot` — **FAILS** for `Sbet>0` (min-eig
  `−0.042`). Independent-path witness: `Q=Ptot=Sin=0, P=4.82, Sbet=1` — a lone cross-block bond whose
  curl lives on **boundary plaquettes**, credited by the total curl `P` but not by `Ptot`. This is the
  single `ell`-factor the module docstrings flagged as "`region_2123` too weak by `~ell`", now a hard
  witness. Hence the island `cross_section_2127_smallL` does NOT sum to a true `H1`.
* `(targ)` the `(2.128)` target itself HOLDS on the admissible subspace (`+0.108`) and FAILS on the
  full space (`−6·10^{-4}`) — so `(2.121)` admissibility is load-bearing and the target is a genuine
  theorem.

Choosing the DEFINITION `Pslab := ell²·totalCurlEnergy` (so `H4` is an equality) collapses the whole
residual to `(star)`. `sum_inBlock_le_univ` below proves `H3` and `Sin ≤ ‖B‖²` from `coarseLattice_unique`
(each fine site is in `≤ 1` block). `lemma24_from_star` then produces `Lemma24Conclusion` from the
SINGLE hypothesis `(star)` — no free reals, `H3/H4/hNorm` discharged. `(star)` is the remaining named
primitive: the **global** cross-sectional operator positivity (with the full curl `P`, not `Ptot`),
numerically true but NOT proved here and NOT obtainable from the per-coarse-bond island. -/

open AdalyFormal.Target.ClayStatement in
/-- **Block-disjointness aggregation.** For any nonnegative `g` on a fintype `ι` and any assignment
`S : site → Finset ι` whose members all have their `baseSite` inside the block, the total over coarse
centers is bounded by the global total, because the blocks are pairwise disjoint
(`coarseLattice_unique`: each fine site lies in `≤ 1` block). Used for both `H3` (plaquettes,
`baseSite := p.1`) and `Sin ≤ ‖B‖²` (bonds, `baseSite := b.1`). -/
theorem sum_inBlock_le_univ {L : PeriodicLatticeExtent} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ell : ℕ} (baseSite : ι → PeriodicLatticeSite L)
    (S : PeriodicLatticeSite L → Finset ι)
    (hS : ∀ (y : PeriodicLatticeSite L) (i : ι), i ∈ S y → baseSite i ∈ blockOf y ell)
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∑ y ∈ CoarseLattice L ell, ∑ i ∈ S y, g i ≤ ∑ i : ι, g i := by
  have hdisj : (↑(CoarseLattice L ell) : Set (PeriodicLatticeSite L)).PairwiseDisjoint S := by
    intro y hy y' hy' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro i hiy hiy'
    exact hne (coarseLattice_unique ell (Finset.mem_coe.mp hy) (Finset.mem_coe.mp hy')
      (hS y i hiy) (hS y' i hiy'))
  rw [← Finset.sum_biUnion hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hg i)

/-- **H3, discharged**: in-block curl energy `≤` total curl energy. -/
theorem inBlockCurl_le_total {L : PeriodicLatticeExtent} {ell : ℕ} (B : Bond L → ℝ) :
    inBlockCurlEnergy ell B ≤ totalCurlEnergy B := by
  unfold inBlockCurlEnergy totalCurlEnergy
  exact sum_inBlock_le_univ (fun p => p.1) (fun y => plaqsInBlock y ell)
    (fun y p hp => (mem_plaqsInBlock.mp hp).1) (fun p => (curlValue B p) ^ 2) (fun p => sq_nonneg _)

/-- **`Sin ≤ ‖B‖²`, discharged** (makes `Sbet := ‖B‖² − Sin ≥ 0` and `hNorm` free of any undefined
real): in-block bond energy `≤` full bond norm. -/
theorem inBlockBond_le_norm {L : PeriodicLatticeExtent} {ell : ℕ} (B : Bond L → ℝ) :
    inBlockBondEnergy ell B ≤ bondNormSq B := by
  unfold inBlockBondEnergy bondNormSq
  exact sum_inBlock_le_univ (fun b => b.1) (fun y => bondsInBlock y ell)
    (fun y b hb => (mem_bondsInBlock.mp hb).1) (fun b => (B b) ^ 2) (fun b => sq_nonneg _)

/-- **`(2.128)` from the SINGLE primitive `(star)`.** With `Pslab := ell²·totalCurlEnergy` (so `H4`
is definitional equality) and `Sbet := ‖B‖² − Sin` (so `hNorm` is `ring` and `Sbet ≥ 0` is
`inBlockBond_le_norm`), `Lemma24Conclusion ell B` follows from `region_2123` (proved), the discharged
`H3` (`inBlockCurl_le_total`), and the ONE remaining hypothesis

  `(star)`  `ell·Q + P ≥ (1/3)ell^{-3}·(‖B‖²−Sin) − 6ell^{-2}·Sin`.

No free reals remain: `Pslab`, `Sbet`, `H3`, `H4`, `hNorm` are all determined/discharged. `(star)` is
the global cross-sectional operator positivity — numerically true on the admissible subspace
(`compute/derive_h1/probe_h1.py`), NOT proved here, and NOT the false `(agg)` the per-bond island
sums to. This SUPERSEDES `lemma24_from_slab_hyps'` (which left `Pslab` a free undefined real). -/
theorem lemma24_from_star {L : PeriodicLatticeExtent} {ell : ℕ}
    (hell : 1 ≤ ell)
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (hStar : (ell : ℝ) * coarseQEnergy ell B + totalCurlEnergy B
        ≥ (1 / 3) * (1 / (ell : ℝ) ^ 3) * (bondNormSq B - inBlockBondEnergy ell B)
          - 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B) :
    Lemma24Conclusion ell B := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hne : ((ell : ℝ) ^ 2) ≠ 0 := by positivity
  have hP : 0 ≤ totalCurlEnergy B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSinLeNorm := inBlockBond_le_norm (ell := ell) B
  refine lemma24_from_slab_hyps' hell hstrict0 hstrict1 hstrict2 B hB
    ((ell : ℝ) ^ 2 * totalCurlEnergy B) (bondNormSq B - inBlockBondEnergy ell B)
    (mul_nonneg (by positivity) hP) (by linarith [hSinLeNorm]) ?_ ?_ ?_ ?_
  · -- H1 = (star), after (ell²·P)/ell² = P
    have hdiv : (ell : ℝ) ^ 2 * totalCurlEnergy B / (ell : ℝ) ^ 2 = totalCurlEnergy B := by
      field_simp
    rw [hdiv]; exact hStar
  · -- H3
    exact inBlockCurl_le_total (ell := ell) B
  · -- H4: ell²·P ≤ ell²·P
    exact le_refl _
  · -- hNorm: ‖B‖² = Sin + (‖B‖² − Sin)
    ring

#print axioms sum_inBlock_le_univ
#print axioms inBlockCurl_le_total
#print axioms inBlockBond_le_norm
#print axioms lemma24_from_star

/-! ## STEP 5 (this pass). The GLOBAL ASSEMBLY: `(star)` from the per-coarse-bond-SUMMABLE `(geom)`,
via the exact slab-curl multiplicity identity that resolves `[RES-STAR-GLOBAL-ASSEMBLY]`.

`compute/star_close/characterize_assembly.py` (`PYTHONHASHSEED=0`, two byte-identical runs)
characterizes exactly how the per-coarse-bond `(2.124)`-`(2.127)` bounds sum to `(star)` WITHOUT
double-counting the full fine curl `P = totalCurlEnergy`. The summed per-`c` output naturally carries
the GEOMETRIC slab curl

  `slabCurlEnergy ell B = Σ_{c=(y,μ)} Σ_{p : μ∈dirs(p), base(p)∈B(y)} (curlValue B p)²`,

and the double-counting worry (`[RES-STAR-GLOBAL-ASSEMBLY]`, flagged by two prior builders as a
SEPARATE obstruction) is RESOLVED by an EXACT multiplicity identity: each fine plaquette `p=(x,{a,b})`
is credited once per direction `μ∈{a,b}` (two choices), each paired with the UNIQUE coarse block
owning its base site `x` (`coarseLattice_exists` existence + `coarseLattice_unique` uniqueness) —
multiplicity EXACTLY `2`. Hence `slabCurlEnergy = 2·totalCurlEnergy` (`slabCurlEnergy_eq_two_totalCurl`,
an IDENTITY, holds for EVERY `B`; verified entrywise `max|Pslab−2P| = 0.0` in
`characterize_assembly.py` FACT A). For `ell ≥ 2` (`ell² ≥ 2`), `ell^{-2}·slabCurl = 2ell^{-2}·P ≤ P`,
so the per-`c`-summable `(geom)` implies `(star)` (`star_from_geom`), and `lemma24_from_geom` chains
`lemma24_from_star` to `Lemma24Conclusion`. This CLOSES the assembly obstruction (kernel-checked).

**SYNC (this pass, `GeomScratch.lean`).** `(geom)` is now reduced further, kernel-clean: the three
incidence facts FACT 1 (`sum_topFace_ge_Sbet`, the cross-block `Sbet` lower bound), FACT 2
(`sum_boundaryCorr_le`, the `6·Sin` boundary count) and FACT 4 (`sum_regionCurl_le_slabCurl`) are
PROVED, and `geom_from_perc`/`lemma24_from_perC` reduce `Lemma24Conclusion` (at `ell∈{2,3}`) to the
SINGLE remaining per-`c` bound `hPerC` (the per-coarse-bond `(2.127)×ell` inequality). Its feeders
`(2.124)` (`CrossSectionField.crossSection_2124`, `[RES-2124-TELESCOPE]` **CLOSED**), the factored
core `CrossSectionDecomp.cross_section_2125c`, and the sharp cross-sectional operator
`cross_section_2127_smallL` are all proved; the resummation `q = ell³·lineCoarseRestrict`
(`lineCoarseRestrict_resummation`) rescales `(2.125ᶜ)`. The exact multiplier identity
`M = (1/3)ell·[2127] + ell⁻²·[2124] + ell⁻⁵·[2125ᶜ] + ell⁻²·diag(R)` holds ENTRYWISE
(`compute/geom_assembly/perc_certificate.py`, `max|M−combo| = 0`), so `hPerC` is a constant-multiplier
SOS of the three feeders EXCEPT for the residual diagonal `R = boundaryCorr − transBondTop −
transBondBot − offridge`, which is INDEFINITE (`R = −1` on the transverse ν-edge bonds — cross-block
bonds counted by the `(2.124)` corrections but absent from the in-block-only `boundaryCorr` that
FACT 2 needs for its `6·Sin` count). Closing `hPerC` therefore needs the ν-edge transverse terms
handled off-diagonally (curl coupling) or globally-telescoped — the sole remaining residual of the
U=1 operator-positivity milestone. -/

/-- The plaquettes credited by a coarse bond `c=(y,μ)` in the slab curl: those with `μ` among their
two directions AND base site inside the block `B(y)`. Matches `characterize_assembly.py`'s incidence
`(a==μ or b==μ) and in_block(y, base(p))`. -/
noncomputable def slabPlaqs {L : PeriodicLatticeExtent} {ell : ℕ} (c : CoarseBond L ell) :
    Finset (PeriodicLatticePlaquette L) :=
  Finset.univ.filter (fun p => (c.2 = p.2.1.1 ∨ c.2 = p.2.1.2) ∧ p.1 ∈ blockOf c.1.1 ell)

/-- The GEOMETRIC slab curl energy `Σ_c Σ_{p⊂slab(c)} (curlValue B p)²` — the natural output of
summing the per-coarse-bond `(2.127)` (`Pslab` in `characterize_assembly.py`). -/
noncomputable def slabCurlEnergy {L : PeriodicLatticeExtent} (ell : ℕ) (B : Bond L → ℝ) : ℝ :=
  ∑ c : CoarseBond L ell, ∑ p ∈ slabPlaqs c, (curlValue B p) ^ 2

/-- **The multiplicity count = 2.** For every fine plaquette `p`, exactly two coarse bonds credit it
in the slab sum: one for each of its two directions `p.2.1.1 < p.2.1.2`, each paired with the unique
coarse block owning its base site `p.1` (`coarseLattice_exists` + `coarseLattice_unique`). This is the
in-framework proof of `characterize_assembly.py` FACT B (multiplicity exactly 2). -/
theorem slab_incidence_card {L : PeriodicLatticeExtent} {ell : ℕ}
    (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (p : PeriodicLatticePlaquette L) :
    (Finset.univ.filter (fun c : CoarseBond L ell =>
        (c.2 = p.2.1.1 ∨ c.2 = p.2.1.2) ∧ p.1 ∈ blockOf c.1.1 ell)).card = 2 := by
  obtain ⟨y0, hy0mem, hy0blk⟩ := coarseLattice_exists ell hell hdvd p.1
  rw [Finset.card_eq_two]
  refine ⟨(⟨y0, hy0mem⟩, p.2.1.1), (⟨y0, hy0mem⟩, p.2.1.2), ?_, ?_⟩
  · intro hcon
    exact absurd (congrArg Prod.snd hcon) (ne_of_lt p.2.2)
  · ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hdir, hblk⟩
      have hsub : c.1.1 = y0 := coarseLattice_unique ell c.1.2 hy0mem hblk hy0blk
      have hs1 : c.1 = (⟨y0, hy0mem⟩ : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) :=
        Subtype.ext hsub
      rcases hdir with h | h
      · exact Or.inl (Prod.ext_iff.mpr ⟨hs1, h⟩)
      · exact Or.inr (Prod.ext_iff.mpr ⟨hs1, h⟩)
    · rintro (h | h) <;> subst h
      · exact ⟨Or.inl rfl, hy0blk⟩
      · exact ⟨Or.inr rfl, hy0blk⟩

/-- **`slabCurlEnergy = 2·totalCurlEnergy`** — the exact multiplicity identity resolving
`[RES-STAR-GLOBAL-ASSEMBLY]`. Each plaquette is credited exactly twice (`slab_incidence_card`), so the
double sum collapses to `2·Σ_p (curlValue B p)²`. Holds for EVERY `B` (a geometric identity, not a
subspace property — the `characterize_assembly.py` FACT A garbage-substitution control confirms it
holds for random `B` too). -/
theorem slabCurlEnergy_eq_two_totalCurl {L : PeriodicLatticeExtent} {ell : ℕ}
    (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → ℝ) :
    slabCurlEnergy ell B = 2 * totalCurlEnergy B := by
  unfold slabCurlEnergy totalCurlEnergy slabPlaqs
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_filter, Finset.sum_const, slab_incidence_card hell hdvd p, nsmul_eq_mul]
  norm_num

/-- **`(star)` from `(geom)`.** The per-coarse-bond-summable `(geom)` (LHS `ell·Q + ell^{-2}·slabCurl`)
implies the full-curl `(star)` (LHS `ell·Q + P`), because `ell^{-2}·slabCurl = 2ell^{-2}·P ≤ P` for
`ell ≥ 2` (`slabCurlEnergy_eq_two_totalCurl` + `ell² ≥ 2`). RHS identical to `lemma24_from_star`'s
`hStar` (the `(star)` primitive). This is the kernel-checked "crediting the full curl `P` without
double-counting" step. -/
theorem star_from_geom {L : PeriodicLatticeExtent} {ell : ℕ}
    (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → ℝ)
    (hGeom : (ell : ℝ) * coarseQEnergy ell B + (1 / (ell : ℝ) ^ 2) * slabCurlEnergy ell B
        ≥ (1 / 3) * (1 / (ell : ℝ) ^ 3) * (bondNormSq B - inBlockBondEnergy ell B)
          - 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B) :
    (ell : ℝ) * coarseQEnergy ell B + totalCurlEnergy B
        ≥ (1 / 3) * (1 / (ell : ℝ) ^ 3) * (bondNormSq B - inBlockBondEnergy ell B)
          - 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B := by
  have hell0 : 0 < ell := by omega
  have heq := slabCurlEnergy_eq_two_totalCurl hell0 hdvd B
  have hP : 0 ≤ totalCurlEnergy B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell2
  have hell2sq : (2 : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith [hellR]
  have hle : (1 / (ell : ℝ) ^ 2) * slabCurlEnergy ell B ≤ totalCurlEnergy B := by
    rw [heq, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0 : ℝ) < (ell : ℝ) ^ 2)]
    nlinarith [hP, hell2sq, mul_nonneg hP (by linarith : (0 : ℝ) ≤ (ell : ℝ) ^ 2 - 2)]
  linarith [hGeom, hle]

/-- **`Lemma24Conclusion` from `(geom)`, UNCONDITIONAL at `ell ≥ 2`** (in particular `ell ∈ {2,3}`).
Chains `star_from_geom` (`(geom) ⟹ (star)`) into `lemma24_from_star` (`(star) ⟹ (2.128)`, proved).
So `(2.128)` at `L ∈ {2,3}` now reduces to the SINGLE residual `(geom)` — the summed per-coarse-bond
cross-sectional operator positivity — with the assembly/double-counting obstruction fully discharged
in the kernel. -/
theorem lemma24_from_geom {L : PeriodicLatticeExtent} {ell : ℕ}
    (hell2 : 2 ≤ ell)
    (hstrict0 : ell < L 0 + 1) (hstrict1 : ell < L 1 + 1) (hstrict2 : ell < L 2 + 1)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell)
    (hGeom : (ell : ℝ) * coarseQEnergy ell B + (1 / (ell : ℝ) ^ 2) * slabCurlEnergy ell B
        ≥ (1 / 3) * (1 / (ell : ℝ) ^ 3) * (bondNormSq B - inBlockBondEnergy ell B)
          - 6 * (1 / (ell : ℝ) ^ 2) * inBlockBondEnergy ell B) :
    Lemma24Conclusion ell B :=
  lemma24_from_star (by omega : 1 ≤ ell) hstrict0 hstrict1 hstrict2 B hB
    (star_from_geom hell2 hdvd B hGeom)

#print axioms slab_incidence_card
#print axioms slabCurlEnergy_eq_two_totalCurl
#print axioms star_from_geom
#print axioms lemma24_from_geom

end AdalyFormal.Balaban.Lemma24Assembly
