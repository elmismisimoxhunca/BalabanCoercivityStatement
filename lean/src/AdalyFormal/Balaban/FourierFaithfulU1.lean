/-
✓ NO LONGER A LEAF (substrate-wiring lane, 2026-07-24, `GOAL_LEMMA.md` §3 Piece 1, `compute/
wire_faithful_Q/BUILD.md`): the prosecutor's 2026-07-24 finding below is SUPERSEDED (S75) — it
correctly diagnosed the state BEFORE the wiring, and precisely specified what the wiring needed
to do. `HjMinimizer.lean`'s `gaugeConstraintSubspace`/`IsBalabanExtension` and `U1Anchor.lean`'s
`BalabanFreeCoercivity`/`HasBoundedSymbolRepresentation` have SINCE been rewired onto THIS
module's faithful `Q_k` (`lineCoarseRestrictCLM`), and `U1Anchor.lean` §7
(`balabanFreeCoercivity_lower_gamma0_one`) genuinely CONSUMES
`faithful_U1_coercivity_lower_norm` below (mutation-checked: removing the call breaks the proof) —
this module now has a real importer (`U1Anchor.lean`, hence `HjMinimizer`'s downstream consumers).
The original note is kept below, struck through in spirit, for the historical record of exactly
what was true before the repair:

~~⚠ DISCONNECTED LEAF (prosecutor 2026-07-24, compute/prosecute_u1lower/VERDICT.md): the
inequality below is GENUINE, sorry-free, correct math over the FAITHFUL Q (lineCoarseRestrict)
-- but this module is a LEAF (0 importers) and does NOT connect to U1Anchor.BalabanFreeCoercivity
(the Piece-1 target), which is stated over the WRONG Q (coarseRestrictCLM). The 'instantiate at
H_kB' bridge is PROSE ONLY. So this is NOT 'Piece 1 done' -- it is the reusable MATERIAL the
substrate-wiring lane consumes after rewiring HjMinimizer/U1Anchor onto the faithful Q.~~
-/
/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.LineIntegralAveraging

set_option autoImplicit false

/-!
# Piece 1, the quantitative `U = 1` base: the `∀ell`-uniform lower coercivity over the FAITHFUL `Q_k`
— PROVED, with the explicit sharp constant, WITHOUT the momentum-space machinery

**Dispatch** (`GOAL_LEMMA.md` §3 Piece 1, §6.8): prove the `∀ell`-uniform `U=1` coercivity
`γ₀·‖∂₁B‖² ≤ ⟨B, Δ_k(U=1) B⟩` with `γ₀ > 0` depending on `d` (and `L`) only, uniform in `k`/`ell`,
over the FAITHFUL `Q_k` (`LineIntegralAveraging.lineCoarseRestrict`), expected to require the
CMP95 (1.60)-(1.67) momentum-space reduction plus a `[SCALAR-SYMBOL-BOUND]` residual.

## THE HEADLINE, stated plainly: the target closes ELEMENTARILY, sharp, no Fourier, no residual.

`GOAL_LEMMA.md` §6.8 orders the elementary route exhausted BEFORE the infrastructure build. It
succeeds. The whole argument is three steps, none of them momentum-space:

1. **The minimum characterization eliminates `Δ_k`.** CMP95 p.29 (verbatim, corpus
   `p29.md` + `compute/how_he_proves_it/PROOF_OF_167.md`): `⟨B,Δ_kB⟩ = ⟨∂H_kB,∂H_kB⟩` (1.65) where
   `H_kB` "is a minimum of ½⟨∂A,∂A⟩ on the hyperplane {A : Q_kA = B, R∂*A = 0}". So the lower bound
   `γ₀‖∂₁B‖² ≤ ⟨B,Δ_kB⟩` follows from the PURELY QUANTIFIED statement
   **`∀ A, γ₀·‖∂₁(Q_kA)‖² ≤ ‖∂A‖²`** — instantiate at `A := H_kB` and use `Q_kH_kB = B` (same
   page). Adding constraints (`R∂*A = 0`, CMP99b's axial/`Λ`-restrictions, ANY further constraint
   set) only shrinks the feasible set and RAISES the minimum, so the `∀A` form transfers to every
   downstream constrained `Δ_k` a fortiori. No `H_k`, no `R`, no minimizer machinery is needed to
   STATE or PROVE it — and none is used.
2. **Discrete Stokes on the big square** (`lineIntegral_bigSquare_stokes`, §2): the coarse
   circulation of the four `ell`-bond line integrals around an `ell×ell` square equals the SUM of
   the `ell²` fine plaquette curls tiling it — a pure double-telescoping identity, valid on the
   periodic torus (everything is expressed through shifts; no coordinates, no boundary case).
   Consequently (`coarseCurl_lineCoarseRestrict_eq_blockSum`, §3) the coarse curl of the faithful
   `Q_k`-average is EXACTLY `(1/ell⁴)·Σ_{x∈B(y)}Σ_{i,j<ell}` of fine curls — `ell⁵` fine-curl terms
   against the `1/ell⁴` coefficient.
3. **Cauchy–Schwarz + exact reindexing** (§4): per coarse plaquette, `(Σ of ell⁵ terms)² ≤
   ell⁵·Σ(terms²)`; summing over coarse plaquettes, the blocks PARTITION the torus
   (`AdmissibleSubspace.coarseLattice_exists`/`coarseLattice_unique`, packaged here as
   `sum_coarse_blocks`) and each `(i,j)`-offset shift is a BIJECTION of the torus, so the total is
   EXACTLY `ell²·Σ_q(∂A)_q²` — no multiplicity-overcounting slack at all. Chain:
   `Σ_{p'}(∂₁'Q_kA)²(p') ≤ ell⁻⁸·ell⁵·ell²·Σ_q(∂A)_q² = (1/ell)·Σ_q(∂A)_q²`.

**MAIN THEOREM** (`faithful_U1_coercivity_lower`, §5):
`ell · Σ_{p'} (∂₁'(Q_k^{faithful}A))(p')² ≤ Σ_q ((∂A)(q))²` for EVERY `L`, EVERY aligned
`ell ∣ L_μ+1` (`ell > 0`), EVERY `A` — so **`γ₀ = 1` works uniformly in `k, ell, L`** (the sharp
form even GROWS like `ell`; the calibration §6 shows `ell·(...)` is exact at `ell = 1`, and the
smooth-field scaling heuristic says the factor `ell` is the true rate, matching the unit-vs-fine
lattice dictionary). `γ₀` here is a LITERAL — not an existential — so uniformity is manifest in
the statement, per `GOAL_LEMMA.md` §6.6 (no free parameters) and the S91 discipline (no
`∃`-conclusions anywhere in this module).

## Why this supersedes the module-level expectations it was dispatched under

* `U1FaithfulCoercivity.lean` §8 argued the elementary route "cannot supply the NUMBER" because
  nothing stops the achieved minimum from shrinking as `L, ell` grow. That argument considered only
  the qualitative-positivity route (positivity of a finite-dimensional minimum); the Stokes +
  Cauchy–Schwarz route DOES stop the shrinking, quantitatively, and §8's pessimism is hereby
  superseded for the LOWER bound. (Its verdict stands for the UPPER bound — see residuals.)
* `U1Anchor.exists_bounded_weight_symbol`'s `sorry` bundled BOTH directions of CMP95 (1.67) over
  the WRONG `Q`. Over the faithful `Q`, the lower direction is now PROVED outright; nothing in this
  module rests on that `sorry`, on `U1Anchor`, or on any `HjMinimizer` machinery.

## What this module does NOT prove (named precisely, not silently dropped)

* **The UPPER bound** `⟨B,Δ_kB⟩ ≤ γ₁‖∂₁B‖²` — the OTHER half of CMP95 (1.67). That direction needs
  the existence of a GOOD extension (`‖∂H_kB‖² ≤ γ₁‖∂₁'B‖²` for the minimizing `H_kB`), which is
  where Bałaban's momentum representation (1.60)-(1.63) and the scalar bound
  `0 < γ₀ ≤ Δ₀(p′)φ_μ(p′) ≤ γ₁` (CMP95 p.28, proved via CMP89 Lemma 2.4) genuinely live. Named
  residual `[UPPER-EXTENSION-BOUND]` (subsumes the dispatch's `[SCALAR-SYMBOL-BOUND]`): a real,
  bounded, momentum-space formalization target, NOT attempted here — and NOT needed for the
  dispatch's stated target, which is the lower coercivity only (the direction the
  `C*Δ_kC ≥ γ₀ > 0` lemma of `GOAL_LEMMA.md` §1 consumes).
* **The Fourier bridge itself** (finite-abelian character diagonalization of the faithful `Q_k`,
  its (1.31)/(1.61) symbol `u·v_μ` in factorized geometric-sum form): dispatched as the expected
  mechanism, made UNNECESSARY for the target theorem by the elementary route. What §7 DOES supply
  is the faithful-`Q` shift covariance (`lineCoarseRestrict_shift_intertwine`) — the exact analog
  of `CoarseShiftCovariance.coarseRestrict_shift_intertwine`, the structural prerequisite any
  future momentum-space work (e.g. `[UPPER-EXTENSION-BOUND]`) will need. The remaining
  quotient-duality/plane-wave-symbol items stay named in `CoarseShiftCovariance.lean`'s residual
  list, unchanged.
* **Wiring into `coerc_u_main`/Spine** — glue is the glue lane's scope (`GOAL_LEMMA.md` Wave 3).

## Source pins

* CMP95 printed p.29 (1.64)-(1.67) and the `H_kB` minimum characterization: corpus
  `corpus/mathpix/balaban_CMP95_1984_propagators_I/normalized/p29.md` (machine-draft), mechanism
  cross-verified against page images in `compute/how_he_proves_it/PROOF_OF_167.md` (LAW-11 renders,
  `compute/how_he_proves_it/renders/`, and `compute/ratio_identity/renders/CMP95_pdf13-13.png`).
* The faithful `Q_k` = CMP95 (1.11)/(1.18) WITH its line integral: `LineIntegralAveraging.lean`
  (grade-3-confirmed foundation, `GOAL_LEMMA.md` §5).
* `∂` (fine curl) = CMP95 (1.2) = `LatticeOperators.curlValue`; `∂₁` (unit/coarse-lattice curl) =
  the same four-term formula at coarse adjacency = `CoarseCurl.coarseCurlValue` (LAW-19, reused).

## Falsifiability / stated surface (S88)

* §6 `calibration_ell_one`: at `ell = 1` the main inequality is an EQUALITY — the constant `ell`
  is exactly calibrated, not slack, where the faithful and single-bond `Q` coincide
  (`lineCoarseRestrict_one_eq_coarseRestrict`) and the one true prior brick lives.
* §6 `mutation_doubled_constant_fails`: doubling the constant (`2·ell`) makes the statement FALSE
  on a concrete witness (kernel-checked counterexample: the single-bond bump field on the shared
  `4³` witness lattice at `ell = 1`) — the constant has no factor-2 slack at `ell = 1`, so the
  inequality proved here is sharp-at-calibration, not a vacuously weak bound.
* Non-vacuity: the same witness exhibits `Σ_q (∂A)_q² ≥ 1 > 0` with nonzero coarse curl of `Q A`
  at `ell = 1`, so the inequality genuinely constrains (both sides nonzero on the witness family).
-/

namespace AdalyFormal.Balaban.FourierFaithfulU1

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.KernelSubspace
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.CoarseShiftCovariance
open AdalyFormal.Balaban.LineIntegralAveraging

variable {L : PeriodicLatticeExtent}

/-! ## §1. Shift-iterate plumbing: `coarseShift` at arbitrary counts, and cross-direction
commutation of iterates (the torus-safe replacement for coordinate bookkeeping) -/

/-- `coarseShift x 0 μ = x` — zero iterates. -/
theorem coarseShift_zero (x : PeriodicLatticeSite L) (μ : Fin 3) : coarseShift x 0 μ = x := rfl

/-- `coarseShift x (n+1) μ = periodicLatticeShift (coarseShift x n μ) μ` — the successor step,
outermost form. -/
theorem coarseShift_succ (x : PeriodicLatticeSite L) (n : ℕ) (μ : Fin 3) :
    coarseShift x (n + 1) μ = periodicLatticeShift (coarseShift x n μ) μ := by
  unfold coarseShift
  exact Function.iterate_succ_apply' _ n x

/-- **Cross-direction commutation of shift iterates**: `s_μ^[i]` and `s_ν^[j]` commute for
`μ ≠ ν` — the torus-safe generalization of `LatticeOperators.periodicLatticeShift_comm`
(single steps) and `LineIntegralAveraging.coarseShift_comm` (equal counts), needed here at
MIXED counts `(i, j)`. -/
theorem coarseShift_coarseShift_comm (x : PeriodicLatticeSite L) (i j : ℕ) {μ ν : Fin 3}
    (h : μ ≠ ν) :
    coarseShift (coarseShift x j ν) i μ = coarseShift (coarseShift x i μ) j ν := by
  have hc : Function.Commute (fun z : PeriodicLatticeSite L => periodicLatticeShift z μ)
      (fun z : PeriodicLatticeSite L => periodicLatticeShift z ν) := by
    intro z
    exact periodicLatticeShift_comm z h.symm
  exact ((hc.iterate_left i).iterate_right j) x

/-- Single fine step in `ν` commutes past an `i`-fold iterate in `μ ≠ ν`. -/
theorem periodicLatticeShift_coarseShift_comm (x : PeriodicLatticeSite L) (i : ℕ) {μ ν : Fin 3}
    (h : μ ≠ ν) :
    periodicLatticeShift (coarseShift x i μ) ν = coarseShift (periodicLatticeShift x ν) i μ := by
  have h1 : periodicLatticeShift (coarseShift x i μ) ν = coarseShift (coarseShift x i μ) 1 ν := by
    rw [coarseShift_succ, coarseShift_zero]
  have h2 : coarseShift (periodicLatticeShift x ν) i μ = coarseShift (coarseShift x 1 ν) i μ := by
    rw [coarseShift_succ, coarseShift_zero]
  rw [h1, h2, coarseShift_coarseShift_comm x i 1 h]

/-- `lineIntegralValue` in `coarseShift` form — definitional bridge (the definition's iterate IS
`coarseShift` at count `j`). -/
theorem lineIntegralValue_eq_sum_coarseShift (ell : ℕ) (A : Bond L → ℝ)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    lineIntegralValue ell A x μ = ∑ j ∈ Finset.range ell, A (coarseShift x j μ, μ) := rfl

/-! ## §2. THE DISCRETE STOKES IDENTITY on the `ell × ell` big square -/

/-- **Discrete Stokes, big-square form.** The circulation of the four `ell`-bond line integrals
around the `ell × ell` square based at `x` (sides in directions `μ < ν`) equals the sum of the
`ell²` fine plaquette curls tiling the square:

`A([x → x+ellμ]) + A([x+ellμ → x+ellμ+ellν]) − A([x+ellν → x+ellν+ellμ]) − A([x → x+ellν])
  = Σ_{i,j<ell} (∂A)(x + iμ + jν; μν)`.

Pure double telescoping (`Finset.sum_range_sub`/`sub'`), valid on the periodic torus with NO
boundary caveat — every step is a shift identity. This is the mechanism by which the faithful
`Q_k`'s line integral converts coarse circulation into an exact average of fine curls, the
identity behind the sharp constant of the main theorem. -/
theorem lineIntegral_bigSquare_stokes (ell : ℕ) (A : Bond L → ℝ) (x : PeriodicLatticeSite L)
    {μ ν : Fin 3} (hlt : μ < ν) :
    lineIntegralValue ell A x μ + lineIntegralValue ell A (coarseShift x ell μ) ν
      - lineIntegralValue ell A (coarseShift x ell ν) μ - lineIntegralValue ell A x ν
    = ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
        curlValue A (coarseShift (coarseShift x j ν) i μ, ⟨(μ, ν), hlt⟩) := by
  have hne : μ ≠ ν := ne_of_lt hlt
  -- The summand, expanded: curl at s_μ^i s_ν^j x, with shifted corners re-expressed as
  -- neighbouring (i,j)-offsets.
  have hterm : ∀ i j : ℕ,
      curlValue A (coarseShift (coarseShift x j ν) i μ, ⟨(μ, ν), hlt⟩)
        = (A (coarseShift (coarseShift x j ν) i μ, μ)
            - A (coarseShift (coarseShift x (j + 1) ν) i μ, μ))
          + (A (coarseShift (coarseShift x j ν) (i + 1) μ, ν)
            - A (coarseShift (coarseShift x j ν) i μ, ν)) := by
    intro i j
    show A (coarseShift (coarseShift x j ν) i μ, μ)
        + A (periodicLatticeShift (coarseShift (coarseShift x j ν) i μ) μ, ν)
        - A (periodicLatticeShift (coarseShift (coarseShift x j ν) i μ) ν, μ)
        - A (coarseShift (coarseShift x j ν) i μ, ν) = _
    rw [show periodicLatticeShift (coarseShift (coarseShift x j ν) i μ) μ
          = coarseShift (coarseShift x j ν) (i + 1) μ from (coarseShift_succ _ i μ).symm,
      show periodicLatticeShift (coarseShift (coarseShift x j ν) i μ) ν
          = coarseShift (coarseShift x (j + 1) ν) i μ by
        rw [periodicLatticeShift_coarseShift_comm _ i hne, ← coarseShift_succ]]
    ring
  -- Split the double sum into the two telescoping halves.
  have hsplit : (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
      curlValue A (coarseShift (coarseShift x j ν) i μ, ⟨(μ, ν), hlt⟩))
      = (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          (A (coarseShift (coarseShift x j ν) i μ, μ)
            - A (coarseShift (coarseShift x (j + 1) ν) i μ, μ)))
        + ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
            (A (coarseShift (coarseShift x j ν) (i + 1) μ, ν)
              - A (coarseShift (coarseShift x j ν) i μ, ν)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  rw [hsplit]
  -- First half telescopes in j, second half telescopes in i (after swapping the sums).
  have h1 : (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
      (A (coarseShift (coarseShift x j ν) i μ, μ)
        - A (coarseShift (coarseShift x (j + 1) ν) i μ, μ)))
      = lineIntegralValue ell A x μ - lineIntegralValue ell A (coarseShift x ell ν) μ := by
    have htel : ∀ i ∈ Finset.range ell, (∑ j ∈ Finset.range ell,
        (A (coarseShift (coarseShift x j ν) i μ, μ)
          - A (coarseShift (coarseShift x (j + 1) ν) i μ, μ)))
        = A (coarseShift (coarseShift x 0 ν) i μ, μ)
          - A (coarseShift (coarseShift x ell ν) i μ, μ) := fun i _ =>
      Finset.sum_range_sub' (fun j => A (coarseShift (coarseShift x j ν) i μ, μ)) ell
    rw [Finset.sum_congr rfl htel, Finset.sum_sub_distrib]
    simp only [coarseShift_zero, lineIntegralValue_eq_sum_coarseShift]
  have h2 : (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
      (A (coarseShift (coarseShift x j ν) (i + 1) μ, ν)
        - A (coarseShift (coarseShift x j ν) i μ, ν)))
      = lineIntegralValue ell A (coarseShift x ell μ) ν - lineIntegralValue ell A x ν := by
    rw [Finset.sum_comm]
    have htel : ∀ j ∈ Finset.range ell, (∑ i ∈ Finset.range ell,
        (A (coarseShift (coarseShift x j ν) (i + 1) μ, ν)
          - A (coarseShift (coarseShift x j ν) i μ, ν)))
        = A (coarseShift (coarseShift x j ν) ell μ, ν)
          - A (coarseShift (coarseShift x j ν) 0 μ, ν) := fun j _ =>
      Finset.sum_range_sub (fun i => A (coarseShift (coarseShift x j ν) i μ, ν)) ell
    rw [Finset.sum_congr rfl htel, Finset.sum_sub_distrib]
    simp only [coarseShift_zero, lineIntegralValue_eq_sum_coarseShift]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coarseShift_coarseShift_comm x ell j hne]
  rw [h1, h2]
  ring

#print axioms lineIntegral_bigSquare_stokes

/-! ## §3. The coarse curl of the faithful `Q_k` is an exact block/square average of fine curls -/

/-- The faithful `Q_k` at a SHIFTED coarse bond, pulled back to the original block — the
faithful-`Q` version of the sum-reindexing step, via Lane A's block-image identity
(`CoarseShiftCovariance.coarseShift_blockOf_eq_image`, LAW-19). -/
theorem lineCoarseRestrict_shifted_block {ell : ℕ} (hell : 0 < ell) {μ : Fin 3}
    (hdvd : ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (hy' : coarseShift y ell μ ∈ CoarseLattice L ell) (A : Bond L → ℝ) (ν : Fin 3) :
    lineCoarseRestrict ell A (⟨coarseShift y ell μ, hy'⟩, ν) =
      (1 / (ell : ℝ) ^ 4) * ∑ x ∈ blockOf y ell, lineIntegralValue ell A (coarseShift x ell μ) ν :=
  by
  unfold lineCoarseRestrict
  congr 1
  rw [coarseShift_blockOf_eq_image hell hdvd hy]
  exact Finset.sum_image fun x _ x' _ h => coarseShift_injective ell μ h

/-- **The exact identity**: the coarse curl of the faithful `Q_k`-average is `(1/ell⁴)` times the
sum, over the `ell³` block sites and the `ell²` in-square offsets, of the fine plaquette curls —
`ell⁵` fine-curl terms in total. Combines §2's Stokes identity (per block site) with the
shifted-block reindexing above. This is CMP95's `∂₁Q_k = (average of) Q'∂`-type intertwining,
in the exact form the coercivity needs. -/
theorem coarseCurl_lineCoarseRestrict_eq_blockSum {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → ℝ)
    (y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell})
    (d : PeriodicPlaquetteDirections) :
    coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d) =
      (1 / (ell : ℝ) ^ 4) * ∑ x ∈ blockOf y.1 ell, ∑ i ∈ Finset.range ell,
        ∑ j ∈ Finset.range ell,
          curlValue A (coarseShift (coarseShift x j d.1.2) i d.1.1, d) := by
  obtain ⟨μν, hlt⟩ := d
  show lineCoarseRestrict ell A (y, μν.1)
      + lineCoarseRestrict ell A
          (⟨coarseShift y.1 ell μν.1, coarseShift_mem_coarseLattice hdvd y.2 μν.1⟩, μν.2)
      - lineCoarseRestrict ell A
          (⟨coarseShift y.1 ell μν.2, coarseShift_mem_coarseLattice hdvd y.2 μν.2⟩, μν.1)
      - lineCoarseRestrict ell A (y, μν.2) = _
  rw [lineCoarseRestrict_shifted_block hell (hdvd μν.1) y.2 _ A μν.2,
    lineCoarseRestrict_shifted_block hell (hdvd μν.2) y.2 _ A μν.1]
  show (1 / (ell : ℝ) ^ 4) * (∑ x ∈ blockOf y.1 ell, lineIntegralValue ell A x μν.1)
      + (1 / (ell : ℝ) ^ 4)
          * (∑ x ∈ blockOf y.1 ell, lineIntegralValue ell A (coarseShift x ell μν.1) μν.2)
      - (1 / (ell : ℝ) ^ 4)
          * (∑ x ∈ blockOf y.1 ell, lineIntegralValue ell A (coarseShift x ell μν.2) μν.1)
      - (1 / (ell : ℝ) ^ 4) * (∑ x ∈ blockOf y.1 ell, lineIntegralValue ell A x μν.2) = _
  rw [show (1 / (ell : ℝ) ^ 4) * (∑ x ∈ blockOf y.1 ell, lineIntegralValue ell A x μν.1)
      + (1 / (ell : ℝ) ^ 4)
          * (∑ x ∈ blockOf y.1 ell, lineIntegralValue ell A (coarseShift x ell μν.1) μν.2)
      - (1 / (ell : ℝ) ^ 4)
          * (∑ x ∈ blockOf y.1 ell, lineIntegralValue ell A (coarseShift x ell μν.2) μν.1)
      - (1 / (ell : ℝ) ^ 4) * (∑ x ∈ blockOf y.1 ell, lineIntegralValue ell A x μν.2)
      = (1 / (ell : ℝ) ^ 4) * ∑ x ∈ blockOf y.1 ell,
          (lineIntegralValue ell A x μν.1
            + lineIntegralValue ell A (coarseShift x ell μν.1) μν.2
            - lineIntegralValue ell A (coarseShift x ell μν.2) μν.1
            - lineIntegralValue ell A x μν.2) by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring]
  congr 1
  exact Finset.sum_congr rfl fun x _ => lineIntegral_bigSquare_stokes ell A x hlt

#print axioms coarseCurl_lineCoarseRestrict_eq_blockSum

/-! ## §4. The ℓ² assembly: Cauchy–Schwarz per coarse plaquette, then exact partition/bijection
reindexing over the torus -/

/-- **Blocks partition the torus**: summing any function block-by-block over the coarse lattice
is summing it over every fine site exactly once. Packaged from
`AdmissibleSubspace.coarseLattice_exists` (cover) + `coarseLattice_unique` (disjointness) via
`Finset.sum_biUnion` — the tree had proved both halves but never packaged the sum identity
(LAW-19: package once, here, for reuse). -/
theorem sum_coarse_blocks {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (f : PeriodicLatticeSite L → ℝ) :
    ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, f x = ∑ x, f x := by
  classical
  have hcover : (Finset.univ : Finset (PeriodicLatticeSite L))
      = (CoarseLattice L ell).biUnion (fun y => blockOf y ell) := by
    ext x
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion]
    obtain ⟨y, hy, hx⟩ := coarseLattice_exists ell hell hdvd x
    exact ⟨y, hy, hx⟩
  have hdisj : (↑(CoarseLattice L ell) : Set (PeriodicLatticeSite L)).PairwiseDisjoint
      (fun y => blockOf y ell) := by
    intro y hy y' hy' hne
    refine Finset.disjoint_left.mpr fun x hx hx' => hne ?_
    exact coarseLattice_unique ell (Finset.mem_coe.mp hy) (Finset.mem_coe.mp hy') hx hx'
  calc ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, f x
      = ∑ x ∈ (CoarseLattice L ell).biUnion (fun y => blockOf y ell), f x :=
        (Finset.sum_biUnion hdisj).symm
    _ = ∑ x, f x := by rw [← hcover]

#print axioms sum_coarse_blocks

/-- **The per-direction-pair ℓ² bound, with the sharp constant.** For each fixed plaquette
orientation `d = (μ<ν)`:
`ell · Σ_{y ∈ Λ'} (∂₁'(Q_kA))(y,d)² ≤ Σ_{z} (∂A)(z,d)²`.
Cauchy–Schwarz over the `ell⁵` terms of §3's identity, then the EXACT reindexing: blocks
partition the torus and each `(i,j)`-offset is a shift bijection — no overcounting slack. -/
theorem sum_sq_coarseCurl_le {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → ℝ) (d : PeriodicPlaquetteDirections) :
    (ell : ℝ) * ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        (coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d)) ^ 2
      ≤ ∑ z : PeriodicLatticeSite L, (curlValue A (z, d)) ^ 2 := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  -- the fine-curl-squared summed over block sites and offsets, as a function of the coarse center
  set T : PeriodicLatticeSite L → ℝ := fun y =>
    ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
      (curlValue A (coarseShift (coarseShift x j d.1.2) i d.1.1, d)) ^ 2 with hT
  -- Step 1: per coarse center, Cauchy–Schwarz with exactly ell^5 terms
  have hpointwise : ∀ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
      (coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d)) ^ 2
        ≤ (1 / (ell : ℝ) ^ 3) * T y.1 := by
    intro y
    set s : Finset (PeriodicLatticeSite L × (ℕ × ℕ)) :=
      (blockOf y.1 ell) ×ˢ (Finset.range ell ×ˢ Finset.range ell) with hs
    set F : PeriodicLatticeSite L × (ℕ × ℕ) → ℝ := fun t =>
      curlValue A (coarseShift (coarseShift t.1 t.2.2 d.1.2) t.2.1 d.1.1, d) with hF
    have hsum : (∑ t ∈ s, F t) = ∑ x ∈ blockOf y.1 ell, ∑ i ∈ Finset.range ell,
        ∑ j ∈ Finset.range ell,
          curlValue A (coarseShift (coarseShift x j d.1.2) i d.1.1, d) := by
      rw [hs, Finset.sum_product]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_product]
    have hsumsq : (∑ t ∈ s, (F t) ^ 2) = ∑ x ∈ blockOf y.1 ell, ∑ i ∈ Finset.range ell,
        ∑ j ∈ Finset.range ell,
          (curlValue A (coarseShift (coarseShift x j d.1.2) i d.1.1, d)) ^ 2 := by
      rw [hs, Finset.sum_product]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_product]
    have hcard : (s.card : ℝ) = (ell : ℝ) ^ 5 := by
      simp only [hs, Finset.card_product, Finset.card_range,
        card_blockOf_of_coarse hdvd y.2]
      push_cast
      ring
    have hCS : (∑ t ∈ s, F t) ^ 2 ≤ (ell : ℝ) ^ 5 * ∑ t ∈ s, (F t) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := s) (f := F)
      rw [hcard] at h
      exact h
    have hTy : T y.1 = ∑ t ∈ s, (F t) ^ 2 := by
      rw [hT]
      exact hsumsq.symm
    rw [coarseCurl_lineCoarseRestrict_eq_blockSum hell hdvd A y d, ← hsum, hTy]
    calc ((1 / (ell : ℝ) ^ 4) * ∑ t ∈ s, F t) ^ 2
        = (1 / (ell : ℝ) ^ 8) * (∑ t ∈ s, F t) ^ 2 := by ring
      _ ≤ (1 / (ell : ℝ) ^ 8) * ((ell : ℝ) ^ 5 * ∑ t ∈ s, (F t) ^ 2) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = (1 / (ell : ℝ) ^ 3) * ∑ t ∈ s, (F t) ^ 2 := by
          have hne : (ell : ℝ) ≠ 0 := ne_of_gt hellR
          field_simp
  -- Step 2: sum the pointwise bound over the coarse centers
  have hsumbound : (∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
      (coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d)) ^ 2)
      ≤ (1 / (ell : ℝ) ^ 3) * ∑ y ∈ CoarseLattice L ell, T y := by
    calc (∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
        (coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d)) ^ 2)
        ≤ ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
            (1 / (ell : ℝ) ^ 3) * T y.1 := Finset.sum_le_sum fun y _ => hpointwise y
      _ = (1 / (ell : ℝ) ^ 3) * ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
            T y.1 := by rw [Finset.mul_sum]
      _ = (1 / (ell : ℝ) ^ 3) * ∑ y ∈ CoarseLattice L ell, T y := by
          rw [Finset.sum_subtype (CoarseLattice L ell) (fun _ => Iff.rfl) T]
  -- Step 3: partition + bijection reindexing computes the T-total EXACTLY
  have hTtotal : (∑ y ∈ CoarseLattice L ell, T y)
      = (ell : ℝ) ^ 2 * ∑ z : PeriodicLatticeSite L, (curlValue A (z, d)) ^ 2 := by
    rw [hT]
    rw [sum_coarse_blocks hell hdvd (fun x =>
      ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
        (curlValue A (coarseShift (coarseShift x j d.1.2) i d.1.1, d)) ^ 2)]
    rw [Finset.sum_comm]
    have hinner : ∀ i ∈ Finset.range ell,
        (∑ x : PeriodicLatticeSite L, ∑ j ∈ Finset.range ell,
          (curlValue A (coarseShift (coarseShift x j d.1.2) i d.1.1, d)) ^ 2)
        = (ell : ℝ) * ∑ z : PeriodicLatticeSite L, (curlValue A (z, d)) ^ 2 := by
      intro i _
      rw [Finset.sum_comm]
      have hone : ∀ j ∈ Finset.range ell,
          (∑ x : PeriodicLatticeSite L,
            (curlValue A (coarseShift (coarseShift x j d.1.2) i d.1.1, d)) ^ 2)
          = ∑ z : PeriodicLatticeSite L, (curlValue A (z, d)) ^ 2 := by
        intro j _
        have hbij : Function.Bijective (fun x : PeriodicLatticeSite L =>
            coarseShift (coarseShift x j d.1.2) i d.1.1) :=
          (coarseShift_bijective i d.1.1).comp (coarseShift_bijective j d.1.2)
        exact Fintype.sum_bijective _ hbij _ _ (fun x => rfl)
      rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  -- Chain: ell * Σ ≤ ell * (1/ell³) * ell² * Σ_z = Σ_z
  calc (ell : ℝ) * ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
      (coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d)) ^ 2
      ≤ (ell : ℝ) * ((1 / (ell : ℝ) ^ 3) * ∑ y ∈ CoarseLattice L ell, T y) :=
        mul_le_mul_of_nonneg_left hsumbound (le_of_lt hellR)
    _ = (ell : ℝ) * ((1 / (ell : ℝ) ^ 3)
          * ((ell : ℝ) ^ 2 * ∑ z : PeriodicLatticeSite L, (curlValue A (z, d)) ^ 2)) := by
        rw [hTtotal]
    _ = ∑ z : PeriodicLatticeSite L, (curlValue A (z, d)) ^ 2 := by
        field_simp

#print axioms sum_sq_coarseCurl_le

/-! ## §5. THE MAIN THEOREM — the `∀ell`-uniform `U=1` lower coercivity over the faithful `Q_k` -/

/-- **THE MAIN THEOREM (Piece 1, the `U=1` base, lower direction — CMP95 (1.67) lower half over
the faithful `Q_k`, `∀ell`-uniform, sharp constant).** For EVERY lattice `L`, EVERY aligned
coarsening `ell ∣ L_μ+1` (`ell > 0`), and EVERY fine bond field `A`:

`ell · Σ_{p'} (∂₁'(Q_k^{faithful}A))(p')² ≤ Σ_q ((∂A)(q))²`.

Consequently `γ₀ = 1` (indeed `γ₀ = ell`) works **uniformly in `k`, `ell`, `L`** — a literal
constant, quantified over nothing. Via the minimum characterization of `Δ_k` (CMP95 p.29:
`⟨B,Δ_kB⟩ = ‖∂H_kB‖²` with `Q_kH_kB = B`; any added gauge/axial constraint only raises the
minimum), instantiating `A := H_kB` yields `γ₀·‖∂₁'B‖² ≤ ⟨B,Δ_kB⟩` for ANY faithful `Δ_k` built
as (or above) that minimum — see `lower_coercivity_for_any_extension` for the packaged interface.
NO Fourier, NO scalar-symbol residual: the dispatched `[SCALAR-SYMBOL-BOUND]` is needed only for
the UPPER (`γ₁`) direction, disclosed in the module docstring. -/
theorem faithful_U1_coercivity_lower {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → ℝ) :
    (ell : ℝ) * ∑ p : CoarsePlaquette L ell,
        (coarseCurlValue hdvd (lineCoarseRestrict ell A) p) ^ 2
      ≤ ∑ q : PeriodicLatticePlaquette L, (curlValue A q) ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  rw [show (∑ q : PeriodicLatticePlaquette L, (curlValue A q) ^ 2)
      = ∑ d : PeriodicPlaquetteDirections, ∑ z : PeriodicLatticeSite L,
          (curlValue A (z, d)) ^ 2 by rw [Fintype.sum_prod_type, Finset.sum_comm]]
  exact Finset.sum_le_sum fun d _ => sum_sq_coarseCurl_le hell hdvd A d

#print axioms faithful_U1_coercivity_lower

/-- **`γ₀ = 1`, the uniform-constant form** — the weakened-to-`γ₀=1` corollary, in exactly the
shape a downstream `BalabanFreeCoercivity`-style consumer quantifies (constant OUTSIDE, before
`∀ L`): `Σ_{p'} (∂₁'(Q_kA))² ≤ Σ_q (∂A)²`, every `L`, every aligned `ell > 0`, every `A`. -/
theorem faithful_U1_coercivity_gamma0_one {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → ℝ) :
    ∑ p : CoarsePlaquette L ell, (coarseCurlValue hdvd (lineCoarseRestrict ell A) p) ^ 2
      ≤ ∑ q : PeriodicLatticePlaquette L, (curlValue A q) ^ 2 := by
  have h := faithful_U1_coercivity_lower hell hdvd A
  have hell1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  nlinarith [Finset.sum_nonneg (fun p (_ : p ∈ Finset.univ) =>
    sq_nonneg (coarseCurlValue hdvd (lineCoarseRestrict ell A) p))]

#print axioms faithful_U1_coercivity_gamma0_one

/-- **The consumer interface: the lower coercivity transfers to ANY extension** — for any coarse
field `B` and ANY fine field `A` with `Q_k^{faithful}A = B` (in particular Bałaban's minimizer
`H_kB`, CMP95 p.29 `Q_kH_kB = B`, under ANY additional gauge/axial constraints):
`ell·Σ_{p'}(∂₁'B)² ≤ Σ_q(∂A)²`. Hence any faithful `Δ_k` whose quadratic form is
`min{‖∂A‖² : Q_kA = B, (extra constraints)}` satisfies `⟨B,Δ_kB⟩ ≥ ell·‖∂₁'B‖² ≥ ‖∂₁'B‖²`
the moment it exists — no Fourier bridge required, uniformly in `k, ell, L`. -/
theorem lower_coercivity_for_any_extension {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : CoarseBond L ell → ℝ) (A : Bond L → ℝ)
    (hQ : lineCoarseRestrict ell A = B) :
    (ell : ℝ) * ∑ p : CoarsePlaquette L ell, (coarseCurlValue hdvd B p) ^ 2
      ≤ ∑ q : PeriodicLatticePlaquette L, (curlValue A q) ^ 2 := by
  rw [← hQ]
  exact faithful_U1_coercivity_lower hell hdvd A

#print axioms lower_coercivity_for_any_extension

/-! ## §5b. Hilbert-space (norm) form — the drop-in shape for the CLM layer -/

/-- `‖v‖² = Σ_i (v i)²` on any real `EuclideanSpace` — squared-norm bridge. -/
theorem euclidean_norm_sq {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ^ 2 = ∑ i, (v i) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

/-- **The main theorem in CLM/norm form**: `ell·‖∂₁'(Q_k^{faithful}A)‖² ≤ ‖∂A‖²` for the genuine
`ContinuousLinearMap`s (`CoarseCurl.coarseCurlCLM`, `LineIntegralAveraging.lineCoarseRestrictCLM`,
`LatticeOperators.curlCLM`) on the `EuclideanSpace` layer — the exact shape a repaired faithful
anchor statement consumes. -/
theorem faithful_U1_coercivity_lower_norm {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : BondSpace L) :
    (ell : ℝ) * ‖coarseCurlCLM L ell hdvd (lineCoarseRestrictCLM L ell A)‖ ^ 2
      ≤ ‖curlCLM L A‖ ^ 2 := by
  rw [euclidean_norm_sq, euclidean_norm_sq]
  have hcc : ∀ p : CoarsePlaquette L ell,
      (coarseCurlCLM L ell hdvd (lineCoarseRestrictCLM L ell A)) p
        = coarseCurlValue hdvd (lineCoarseRestrict ell (bondEquiv L A)) p := by
    intro p
    have h1 := congrFun (coarseCurlCLM_apply L ell hdvd (lineCoarseRestrictCLM L ell A)) p
    have h2 : coarseBondEquiv L ell (lineCoarseRestrictCLM L ell A)
        = lineCoarseRestrict ell (bondEquiv L A) := lineCoarseRestrictCLM_apply L ell A
    rw [h2] at h1
    exact h1
  have hfc : ∀ q : PeriodicLatticePlaquette L,
      (curlCLM L A) q = curlValue (bondEquiv L A) q := fun q =>
    congrFun (curlCLM_apply L A) q
  rw [show (∑ p : CoarsePlaquette L ell,
      ((coarseCurlCLM L ell hdvd (lineCoarseRestrictCLM L ell A)) p) ^ 2)
      = ∑ p : CoarsePlaquette L ell,
          (coarseCurlValue hdvd (lineCoarseRestrict ell (bondEquiv L A)) p) ^ 2 from
    Finset.sum_congr rfl fun p _ => by rw [hcc p]]
  rw [show (∑ q : PeriodicLatticePlaquette L, ((curlCLM L A) q) ^ 2)
      = ∑ q : PeriodicLatticePlaquette L, (curlValue (bondEquiv L A) q) ^ 2 from
    Finset.sum_congr rfl fun q _ => by rw [hfc q]]
  exact faithful_U1_coercivity_lower hell hdvd (bondEquiv L A)

#print axioms faithful_U1_coercivity_lower_norm

/-! ## §6. Calibration and falsifiability (S88 stated surface) -/

/-- Every site is a coarse-lattice member at `ell = 1`. -/
theorem mem_coarseLattice_one (y : PeriodicLatticeSite L) : y ∈ CoarseLattice L 1 := by
  rw [mem_CoarseLattice]
  intro μ
  exact Nat.mod_one _

/-- `blockOf y 1 = {y}` — at `ell = 1` each block is the singleton of its own center. -/
theorem blockOf_one (y : PeriodicLatticeSite L) : blockOf y 1 = {y} := by
  ext x
  rw [mem_blockOf, Finset.mem_singleton]
  constructor
  · intro h
    funext μ
    have := h μ
    apply Fin.ext
    omega
  · intro h
    subst h
    intro μ
    omega

/-- At `ell = 1` the faithful `Q₁` is the identity (on the coarse=fine identification). -/
theorem lineCoarseRestrict_one_apply (A : Bond L → ℝ)
    (y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 1}) (μ : Fin 3) :
    lineCoarseRestrict 1 A (y, μ) = A (y.1, μ) := by
  unfold lineCoarseRestrict lineIntegralValue
  rw [blockOf_one]
  simp

/-- At `ell = 1` the coarse curl of `Q₁A` IS the fine curl (at the identified base point). -/
theorem coarseCurl_one_eq_curl (hdvd : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1)) (A : Bond L → ℝ)
    (y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L 1})
    (d : PeriodicPlaquetteDirections) :
    coarseCurlValue hdvd (lineCoarseRestrict 1 A) (y, d) = curlValue A (y.1, d) := by
  show lineCoarseRestrict 1 A (y, d.1.1)
      + lineCoarseRestrict 1 A (⟨coarseShift y.1 1 d.1.1, _⟩, d.1.2)
      - lineCoarseRestrict 1 A (⟨coarseShift y.1 1 d.1.2, _⟩, d.1.1)
      - lineCoarseRestrict 1 A (y, d.1.2) = _
  rw [lineCoarseRestrict_one_apply, lineCoarseRestrict_one_apply, lineCoarseRestrict_one_apply,
    lineCoarseRestrict_one_apply]
  rfl

/-- **CALIBRATION: at `ell = 1` the main inequality is an EQUALITY** — the constant `ell` is
exact where the faithful and single-bond operators coincide
(`LineIntegralAveraging.lineCoarseRestrict_one_eq_coarseRestrict`) and where the tree's one true
prior brick (`U1CurlCoercivity` PART B) lives. The sharpness half of the S88 surface. -/
theorem calibration_ell_one (hdvd : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1)) (A : Bond L → ℝ) :
    (1 : ℝ) * ∑ p : CoarsePlaquette L 1,
        (coarseCurlValue hdvd (lineCoarseRestrict 1 A) p) ^ 2
      = ∑ q : PeriodicLatticePlaquette L, (curlValue A q) ^ 2 := by
  rw [one_mul]
  have hbij : Function.Bijective (fun p : CoarsePlaquette L 1 =>
      ((p.1.1, p.2) : PeriodicLatticePlaquette L)) := by
    constructor
    · rintro ⟨⟨y, hy⟩, d⟩ ⟨⟨y', hy'⟩, d'⟩ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) h.2
    · rintro ⟨z, d⟩
      exact ⟨(⟨z, mem_coarseLattice_one z⟩, d), rfl⟩
  refine Fintype.sum_bijective _ hbij _ _ fun p => ?_
  obtain ⟨y, d⟩ := p
  rw [coarseCurl_one_eq_curl hdvd A y d]

#print axioms calibration_ell_one

/-- The witness bump field: the indicator of the single bond `((0,0,0), 0)` on the shared `4³`
witness lattice — a concrete field with NONZERO fine curl (next theorem), used for the
falsifiability controls. -/
noncomputable def bumpField : Bond AdmissibleSubspace.witnessL → ℝ :=
  fun b => if b = ((fun _ => 0 : PeriodicLatticeSite AdmissibleSubspace.witnessL), (0 : Fin 3))
    then 1 else 0

/-- The base plaquette at the origin with directions `(0,1)`. -/
def bumpPlaquette : PeriodicLatticePlaquette AdmissibleSubspace.witnessL :=
  ((fun _ => 0 : PeriodicLatticeSite AdmissibleSubspace.witnessL), ⟨(0, 1), by decide⟩)

/-- The bump field has fine curl EXACTLY `1` at the origin plaquette — non-vacuity witness
(kernel-checked term evaluation, no `decide` on `ℝ`). -/
theorem curl_bumpField_value : curlValue bumpField bumpPlaquette = 1 := by
  show bumpField (bumpPlaquette.1, bumpPlaquette.2.1.1)
      + bumpField (periodicLatticeShift bumpPlaquette.1 bumpPlaquette.2.1.1, bumpPlaquette.2.1.2)
      - bumpField (periodicLatticeShift bumpPlaquette.1 bumpPlaquette.2.1.2, bumpPlaquette.2.1.1)
      - bumpField (bumpPlaquette.1, bumpPlaquette.2.1.2) = 1
  unfold bumpField
  rw [if_pos (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  norm_num

/-- The total fine-curl energy of the bump field is at least `1` — strict non-vacuity of the
right-hand side on the witness. -/
theorem sum_sq_curl_bumpField_ge_one :
    (1 : ℝ) ≤ ∑ q : PeriodicLatticePlaquette AdmissibleSubspace.witnessL,
      (curlValue bumpField q) ^ 2 := by
  have h := Finset.single_le_sum (f := fun q => (curlValue bumpField q) ^ 2)
    (fun q _ => sq_nonneg _) (Finset.mem_univ bumpPlaquette)
  rw [curl_bumpField_value] at h
  norm_num at h
  exact h

/-- **MUTATION CONTROL (S88): doubling the constant makes the statement FALSE.** The uniform
statement with `2·ell` in place of `ell` fails on a concrete witness (`witnessL`, `ell = 1`,
`bumpField`): by `calibration_ell_one` the two sides are EQUAL there and `≥ 1 > 0`, so the doubled
inequality would force `2S ≤ S` with `S ≥ 1`. The constant proved is within a factor `2` of
optimal at calibration — the theorem is not a vacuously weak bound. -/
theorem mutation_doubled_constant_fails :
    ¬ (∀ (L : PeriodicLatticeExtent) (ell : ℕ), 0 < ell →
        ∀ (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → ℝ),
        2 * (ell : ℝ) * ∑ p : CoarsePlaquette L ell,
            (coarseCurlValue hdvd (lineCoarseRestrict ell A) p) ^ 2
          ≤ ∑ q : PeriodicLatticePlaquette L, (curlValue A q) ^ 2) := by
  intro hmut
  have hdvd1 : ∀ μ : Fin 3, (1 : ℕ) ∣ (AdmissibleSubspace.witnessL μ + 1) := fun _ => one_dvd _
  have h := hmut AdmissibleSubspace.witnessL 1 one_pos hdvd1 bumpField
  have hcal := calibration_ell_one hdvd1 bumpField
  rw [one_mul] at hcal
  rw [hcal] at h
  have hge := sum_sq_curl_bumpField_ge_one
  push_cast at h
  linarith

#print axioms mutation_doubled_constant_fails

/-! ## §7. The faithful-`Q` shift covariance — the dispatched Fourier prerequisite, delivered

Not needed for the main theorem (§5), but it is the structural fact any future momentum-space
work over the faithful `Q` (`[UPPER-EXTENSION-BOUND]`) starts from, and the dispatch explicitly
asked whether Lane A's covariance transfers. It does, verbatim in mechanism. -/

/-- `lineIntegralValue` commutes with the coarse shift in a DIFFERENT direction — pointwise
pullback compatibility. -/
theorem lineIntegralValue_coarseShift_comm (ell m : ℕ) (A : Bond L → ℝ)
    (x : PeriodicLatticeSite L) {μ ν : Fin 3} (h : μ ≠ ν) :
    lineIntegralValue ell A (coarseShift x m μ) ν =
      lineIntegralValue ell (fun b => A (coarseShift b.1 m μ, b.2)) x ν := by
  rw [lineIntegralValue_eq_sum_coarseShift, lineIntegralValue_eq_sum_coarseShift]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coarseShift_coarseShift_comm x m j h]

/-- `lineIntegralValue` commutes with the coarse shift in the SAME direction — trivially, since
iterates of one map commute with each other. -/
theorem lineIntegralValue_coarseShift_same (ell m : ℕ) (A : Bond L → ℝ)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    lineIntegralValue ell A (coarseShift x m μ) μ =
      lineIntegralValue ell (fun b => A (coarseShift b.1 m μ, b.2)) x μ := by
  rw [lineIntegralValue_eq_sum_coarseShift, lineIntegralValue_eq_sum_coarseShift]
  refine Finset.sum_congr rfl fun j _ => ?_
  show A (coarseShift (coarseShift x m μ) j μ, μ) = A (coarseShift (coarseShift x j μ) m μ, μ)
  unfold coarseShift
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

/-- **THE FAITHFUL-`Q` SHIFT COVARIANCE** — the exact analog of Lane A's
`CoarseShiftCovariance.coarseRestrict_shift_intertwine`, now for the FAITHFUL operator: the
faithful block-average at the SHIFTED coarse point equals the faithful block-average, at the
ORIGINAL point, of the shift-pulled-back field. `Q_k^{faithful}` intertwines with the coarse
lattice's own `ell`-periodic adjacency — the structural prerequisite for any momentum-space
diagonalization over the faithful `Q` (the `[UPPER-EXTENSION-BOUND]` route), established here so
that route starts from solid ground. -/
theorem lineCoarseRestrict_shift_intertwine {ell : ℕ} (hell : 0 < ell) {μ : Fin 3}
    (hdvd : ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    (hy' : coarseShift y ell μ ∈ CoarseLattice L ell) (A : Bond L → ℝ) (ν : Fin 3) :
    lineCoarseRestrict ell A (⟨coarseShift y ell μ, hy'⟩, ν) =
      lineCoarseRestrict ell (fun b => A (coarseShift b.1 ell μ, b.2)) (⟨y, hy⟩, ν) := by
  rw [lineCoarseRestrict_shifted_block hell hdvd hy hy' A ν]
  unfold lineCoarseRestrict
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hμν : μ = ν
  · subst hμν
    exact lineIntegralValue_coarseShift_same ell ell A x μ
  · exact lineIntegralValue_coarseShift_comm ell ell A x hμν

#print axioms lineCoarseRestrict_shift_intertwine

end AdalyFormal.Balaban.FourierFaithfulU1
