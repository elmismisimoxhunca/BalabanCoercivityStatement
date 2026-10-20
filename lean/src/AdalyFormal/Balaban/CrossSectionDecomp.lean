/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# CMP96 p.245 (2.124)/(2.125): the per-coarse-bond cross-sectional decomposition

The last U=1 operator-content primitive of the CMP96 Lemma 2.4 chain: the Abel/telescoping
cross-sectional decomposition, characterized against the page images and verified term-by-term.

## SOURCE-FIDELITY CHARACTERIZATION (JOB 1) — verified numerically, `compute/decomp_2124/`

Read directly from CMP96 p.244–245 page images (`compute/norm_dictionary/renders/CMP96_p244*,p245*`).
Coarse bond `c = ⟨y, y+L e_μ⟩`, `c₋ = y`, `c₊ = y+L e_μ`, `μ` = longitudinal direction. p.244 bottom,
VERBATIM: *"Let `c = ⟨y, y+Le_μ⟩` and `Δ', Δ''` denote the intersection of the planes
`x_μ = c_{+,μ}−1 = y_μ+(L−1)`, `x_μ = c_{+,μ} = y_μ+L` with the blocks `B(c₋), B(c₊)`."* Hence:

* `B(c₋) = B(y)`, `B(c₊) = B(y+Le_μ)` — the two side-`L` blocks at the endpoints.
* `Δ'`  = the top μ-layer of `B(y)` at `x_μ = y_μ+L−1`   (a `(d−1)`-dim cross-section).
* `Δ''` = the bottom μ-layer of `B(y+Le_μ)` at `x_μ = y_μ+L`.
* `B(b) = B_μ(x)` for `b = ⟨x, x+e_μ⟩` (p.245, verbatim identification).

These identifications are CONFIRMED numerically (`compute/decomp_2124/probe_2124_2125.py`,
`PYTHONHASHSEED=0`) by the fact that the (2.125) Abel-resummation is an EXACT identity
(max |residual| ≤ 2.2e-16 over 300 samples, every `d∈{2,3}`, `L∈{2,3}`, every `μ`):

    Q₁B(c) = Σ_{x∈B(y)} L^{-(d+1)} B([x,x+Le_μ])
           = L^{-(d+1)} Σ_{x∈B(y)\Δ'} (x_μ−y_μ+1) B_μ(x)          -- rising tent ramp
           + L^{-d}     Σ_{x∈Δ'} B_μ(x)                            -- ridge (weight L·L^{-1}=1)
           + L^{-(d+1)} Σ_{x∈B(y+Le_μ)} (2L−1+y_μ−x_μ) B_μ(x).     -- falling tent ramp

A wrong `Δ'/Δ''/B(c)` breaks this identity numerically; it holds to machine precision, so the
tent weights and the three-way set split are pinned.

## THE (2.125) SIGN CORRECTION — a printed typo, corrected here (fidelity finding)

CMP96 p.245 PRINTS (2.125) with `≦`:  `|Q₁B(c)|² ≦ (1/3)|Σ_{x∈Δ'} L^{-d}B_μ(x)|² − (bdry)`.
This is FALSE as printed (a field supported off `Δ'` gives LHS > 0, RHS < 0). The operative
statement — the one that assembles into (2.126), which IS printed correctly as `≥` — has the
OPPOSITE sign:

    (2.125ᶜ)   |Q₁B(c)|²  ≥  (1/3)|Σ_{x∈Δ'} L^{-d}B_μ(x)|²
                             − L^{-d} Σ_{⟨x,x+e_μ⟩⊂B(c₋)} |B_μ(x)|²
                             − L^{-d} Σ_{⟨x,x+e_μ⟩⊂B(c₊)} |B_μ(x)|².

Two independent proofs of the correction:
* ALGEBRA: assembling (2.126) [`≥`] as `L^{-d}·(2.124) + (2.125)` requires (2.125) as `≥`; the
  printed `≤` contributes a `−P₁₂₅` term that cannot be absorbed (worked out in the notes).
* NUMERICS (`compute/decomp_2124/probe_signs.py`, `PYTHONHASHSEED=0`, 400 samples each): the `≥`
  form (R2) holds with `frac≥0 = 1.000` in EVERY case `d∈{2,3}`, `L∈{2,3}`, every `μ`, while the
  printed `≤` form fails 100%. (2.126) and (2.127) both hold unconditionally (`frac≥0 = 1.000`).

Note: (2.124), (2.125ᶜ), (2.126), (2.127) all hold WITHOUT the (2.121) gauge constraint — the
constraint enters only at the (2.127)→(2.128) step (Lemma 2.4 proper), matching Bałaban's remark
that these are general inequalities.

## WHAT IS PROVED HERE (sorry-free, kernel-checked; `#print axioms` clean)

The genuine mathematical content of (2.125ᶜ) — the "hardest deferred primitive" — is an elementary
quadratic-form inequality + Cauchy–Schwarz. After factoring `L^{-d}` out of `Q₁B, M := Σ_{Δ'}L^{-d}B_μ,
T_±` (all carry `L^{-d}` or `L^{-2d}`; the inequality reduces to the scale where `q = μ̃ + r`):

* `quad_lower`   — the "`1/3` origin": `∀ u v, (1/3)v² − (1/2)u² ≤ (u+v)²`.
* `r2_core`      — `(1/3)μ² − B ≤ (μ+r)²` from `r² ≤ A` and `(1/2)A ≤ B`.
* `r2_weighted`  — the reusable core: for `r = Σ_S w·a`,
                   `(1/3)μ² − K·(Σ_S a²) ≤ (μ + Σ_S w·a)²` whenever `(1/2)Σ_S w² ≤ K`.
                   (Cauchy–Schwarz `sum_mul_sq_le_sq_mul_sq` + `quad_lower`.)
* `tentR_le`, `tentR_sq_div_le_one` — the tent weight `tentR L m = min(m+1, 2L−1−m) ≤ L`, so
  `(tentR L m / L)² ≤ 1`; the crude bound `tent ≤ L` (not `Σk²`) is all that is needed.
* `cross_section_2125c` — **(2.125ᶜ) in faithful factored form**, sorry-free: with `μ̃ = Σ_{p<P} a(p,L−1)`
  the middle-layer coherent mean and the off-ridge tent sum `r = Σ (tentR L m / L)·a`,

     `(1/3)·μ̃²  −  L^d·(Σ_{off-ridge} a²)  ≤  (μ̃ + r)²  ( = q² = the full tent-weighted Q₁B, rescaled )`,

  under `P·(L−1) ≤ L^d` (satisfied by the true transverse count `P = L^{d−1}`, `d≥1`,
  `transverse_count_ok`). This is corrected-(2.125), abstracted only in that the field is indexed by
  `(transverse p, longitudinal m)` rather than by lattice bonds — the resummation identity above (an
  exact numeric fact) is the bijection to the framework's `B_μ` on `blockOf`.

## RESIDUALS (named precisely; NOT closed here) — build discipline OPS-1/LAW-14

**SYNC NOTE (2026-07-24):** the first two residuals below are now **CLOSED in
`AdalyFormal.Balaban.CrossSectionField`** (sorry-free, `#print axioms` clean): `[RES-2124-TELESCOPE]`
by `crossSectionField.crossSection_2124` and `[RES-2125-RESUM-INFRAMEWORK]` (with its block→fiber
bijection) by `crossSectionField.lineCoarseRestrict_resummation`. They are retained struck below for
history; the third (`[RES-STAR-GLOBAL-ASSEMBLY]`) is separately superseded by
`Lemma24Assembly.slabCurlEnergy_eq_two_totalCurl`/`lemma24_from_geom`.

* ~~`[RES-2125-RESUM-INFRAMEWORK]`~~ **CLOSED** (`CrossSectionField.lineCoarseRestrict_resummation`) —
  the resummation *identity* `Q₁B(c) = μ̃ + r` in terms of the framework's
  `lineCoarseRestrict`/`Bond`/`blockOf` indexing (verified EXACT numerically; the index bijection is
  now proved in-`Bond`-framework via `block_fiber_sum` + `pair_conv_tent`).
* ~~`[RES-2124-TELESCOPE]`~~ **CLOSED** (`CrossSectionField.crossSection_2124`) — (2.124) itself
  (curl-energy ≥ ⅓ transverse-grad of `B_μ` on `Δ'` − transverse-bdry); holds unconditionally, proved
  by the elementary per-plaquette `(a+b−c−e)² ≥ ⅓(c−a)²−b²−e²` summed over `Δ'` (a one-layer bound, NOT
  the `dir1_bondSq_le` mechanism an earlier note guessed).
* `[RES-STAR-GLOBAL-ASSEMBLY]` — the global `(star)` (`Lemma24Assembly.lemma24_from_star` hypothesis)
  is NOT obtainable by naively summing the per-coarse-bond (2.127) over `c∈Λ'`: the LHS curl term
  `Σ_c Σ_{p⊂B(c)}` double-counts fine plaquettes across overlapping bond-blocks (the "full curl `P`
  vs in-block `Ptot`" gap already flagged in `Lemma24Assembly.lean`). This per-bond brick does NOT by
  itself make `(star)` / `Lemma24Conclusion` unconditional; that assembly is a separate obstruction.

## L12 / S91
No `Nonempty`/`∃`-concluding declaration; every theorem is a `∀`-statement with explicit constants.
No `S91_REGISTRY.tsv` row triggered.
-/

namespace AdalyFormal.Balaban.CrossSectionDecomp

open Finset

/-! ## §1. The elementary inequality — the `1/3` origin of (2.125). -/

/-- **The `1/3` mechanism.** For all reals, `(u+v)² ≥ (1/3)v² − (1/2)u²`. Equivalent to
`(3/2)u² + 3uv + v² ≥ 0`, whose discriminant `9 − 6 = 3 > 0`... in fact `(3/2)u²+3uv+v²
= (1/2)(√3 u + √3 v)²`-type SOS; `nlinarith` closes it from `(u+v)² ≥ 0` and `(u+2v)² ≥ 0`. -/
theorem quad_lower (u v : ℝ) : (1/3) * v ^ 2 - (1/2) * u ^ 2 ≤ (u + v) ^ 2 := by
  -- `(u+v)² − (1/3)v² + (1/2)u² = (1/6)(3u+2v)² ≥ 0`
  nlinarith [sq_nonneg (3 * u + 2 * v)]

/-- **Core assembly.** `(1/3)μ² − B ≤ (μ+r)²` given `r² ≤ A` and `(1/2)A ≤ B`. -/
theorem r2_core (μ r A B : ℝ) (hrA : r ^ 2 ≤ A) (hAB : (1/2) * A ≤ B) :
    (1/3) * μ ^ 2 - B ≤ (μ + r) ^ 2 := by
  have h1 : (1/3) * μ ^ 2 - (1/2) * r ^ 2 ≤ (r + μ) ^ 2 := quad_lower r μ
  have h2 : (1/2) * r ^ 2 ≤ B := by nlinarith [hrA, hAB]
  have hcomm : (r + μ) ^ 2 = (μ + r) ^ 2 := by ring
  rw [hcomm] at h1
  linarith

/-! ## §2. The reusable weighted core — Cauchy–Schwarz form of (2.125ᶜ). -/

/-- **THE (2.125ᶜ) CORE, weighted form.** For a finite index `S`, weights `w`, field `a`, ridge
mean `μ`, and any `K` with `(1/2)·Σ_S w² ≤ K`:
`(1/3)·μ² − K·(Σ_S a²) ≤ (μ + Σ_S w·a)²`. Proof: Cauchy–Schwarz `(Σ w·a)² ≤ (Σ w²)(Σ a²)`, then
`r2_core` with `A = (Σ w²)(Σ a²)`, `B = K·(Σ a²)` (using `Σ a² ≥ 0`). -/
theorem r2_weighted {ι : Type*} (S : Finset ι) (w a : ι → ℝ) (μ K : ℝ)
    (hK : (1/2) * (∑ i ∈ S, (w i) ^ 2) ≤ K) :
    (1/3) * μ ^ 2 - K * (∑ i ∈ S, (a i) ^ 2) ≤ (μ + ∑ i ∈ S, w i * a i) ^ 2 := by
  set A := (∑ i ∈ S, (w i) ^ 2) * (∑ i ∈ S, (a i) ^ 2) with hA
  have hCS : (∑ i ∈ S, w i * a i) ^ 2 ≤ A := by
    have := sum_mul_sq_le_sq_mul_sq S w a
    simpa [hA] using this
  have haNN : 0 ≤ ∑ i ∈ S, (a i) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hAB : (1/2) * A ≤ K * (∑ i ∈ S, (a i) ^ 2) := by
    rw [hA]
    have hstep : (1/2) * (∑ i ∈ S, (w i) ^ 2) * (∑ i ∈ S, (a i) ^ 2)
        ≤ K * (∑ i ∈ S, (a i) ^ 2) :=
      mul_le_mul_of_nonneg_right hK haNN
    nlinarith [hstep]
  exact r2_core μ (∑ i ∈ S, w i * a i) A (K * (∑ i ∈ S, (a i) ^ 2)) hCS hAB

/-! ## §3. The tent weight and its crude bound. -/

/-- The Abel tent weight `min(m+1, 2L−1−m)`, over ℝ to avoid ℕ-subtraction. Peaks at `m = L−1`
with value `L` (the ridge `Δ'`); on the off-ridge index it is `≤ L−1`. -/
noncomputable def tentR (L m : ℕ) : ℝ := min ((m : ℝ) + 1) (2 * (L : ℝ) - 1 - (m : ℝ))

/-- `tentR L m ≤ L`: one of the two arguments of the `min` is always `≤ L` (`m ≤ L−1` gives
`m+1 ≤ L`; `m ≥ L−1` gives `2L−1−m ≤ L`). -/
theorem tentR_le (L m : ℕ) (_hL : 1 ≤ L) : tentR L m ≤ (L : ℝ) := by
  unfold tentR
  rcases le_total ((m : ℝ) + 1) (L : ℝ) with h | h
  · exact le_trans (min_le_left _ _) h
  · -- `(L:ℝ) ≤ (m:ℝ)+1` (i.e. `m ≥ L−1`) ⟹ `2L−1−m ≤ L`
    have : 2 * (L : ℝ) - 1 - (m : ℝ) ≤ (L : ℝ) := by linarith
    exact le_trans (min_le_right _ _) this

/-- `0 ≤ tentR L m` for `m ≤ 2L−2` (both arguments of the `min` are `≥ 0` on the tent's support). -/
theorem tentR_nonneg (L m : ℕ) (hm : m ≤ 2 * L - 2) (hL : 1 ≤ L) : 0 ≤ tentR L m := by
  unfold tentR
  refine le_min (by positivity) ?_
  have h2L : 2 ≤ 2 * L := by omega
  have hmR : (m : ℝ) ≤ 2 * (L : ℝ) - 2 := by
    have hcast : (m : ℝ) ≤ ((2 * L - 2 : ℕ) : ℝ) := by exact_mod_cast hm
    rwa [Nat.cast_sub h2L, Nat.cast_mul, Nat.cast_ofNat] at hcast
  linarith

/-- `(tentR L m / L)² ≤ 1` for `m ≤ 2L−2` — the only weight fact `r2_weighted` needs. -/
theorem tentR_sq_div_le_one (L m : ℕ) (hm : m ≤ 2 * L - 2) (hL : 1 ≤ L) :
    (tentR L m / (L : ℝ)) ^ 2 ≤ 1 := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have h0 : 0 ≤ tentR L m := tentR_nonneg L m hm hL
  have hle : tentR L m ≤ (L : ℝ) := tentR_le L m hL
  rw [div_pow, div_le_one (by positivity)]
  have : tentR L m ^ 2 ≤ (L : ℝ) ^ 2 := by nlinarith [h0, hle]
  simpa using this

/-! ## §4. (2.125ᶜ) in faithful factored form — the sorry-free brick (JOB 3). -/

/-- The off-ridge index: `(transverse p < P) × (longitudinal m < 2L−1, m ≠ L−1)`. -/
noncomputable def offRidge (L P : ℕ) : Finset (ℕ × ℕ) :=
  (range P) ×ˢ ((range (2 * L - 1)).erase (L - 1))

theorem offRidge_card (L P : ℕ) (hL : 1 ≤ L) : (offRidge L P).card = P * (2 * L - 2) := by
  have hmem : (L - 1) ∈ range (2 * L - 1) := by rw [mem_range]; omega
  rw [offRidge, card_product, card_erase_of_mem hmem, card_range, card_range]
  have h : 2 * L - 1 - 1 = 2 * L - 2 := by omega
  rw [h]

/-- **CMP96 (2.125ᶜ), faithful factored form — sorry-free.** With `μ̃ = Σ_{p<P} a(p, L−1)` the
coherent middle-layer (`Δ'`) mean and `r = Σ_{off-ridge} (tentR L m / L)·a(p,m)` the off-ridge
tent-weighted sum (so `μ̃ + r` is the full tent-weighted `Q₁B(c)`, rescaled by `L^{-d}` out of both
sides), the corrected (2.125) holds:

    (1/3)·μ̃²  −  L^d·(Σ_{off-ridge} a²)  ≤  (μ̃ + r)²,

for every transverse count `P` with `P·(L−1) ≤ L^d` (the true count `P = L^{d−1}` qualifies, see
`transverse_count_ok`). The `L^d·Σa²` term is the source's `T₋ + T₊` (in-block longitudinal bond
energy) after the shared `L^{-d}` rescale. -/
theorem cross_section_2125c (L d P : ℕ) (hL : 1 ≤ L)
    (hPd : (P : ℝ) * ((L : ℝ) - 1) ≤ (L : ℝ) ^ d)
    (a : ℕ → ℕ → ℝ) :
    (1/3) * (∑ p ∈ range P, a p (L - 1)) ^ 2
        - (L : ℝ) ^ d * (∑ i ∈ offRidge L P, (a i.1 i.2) ^ 2)
      ≤ ((∑ p ∈ range P, a p (L - 1))
          + ∑ i ∈ offRidge L P, (tentR L i.2 / (L : ℝ)) * a i.1 i.2) ^ 2 := by
  set S := offRidge L P with hS
  -- weight bound: (1/2)·Σ_S (tentR/L)² ≤ L^d
  have hwsq : ∀ i ∈ S, (tentR L i.2 / (L : ℝ)) ^ 2 ≤ 1 := by
    intro i hi
    rw [hS, offRidge, mem_product] at hi
    have hi2 : i.2 ∈ (range (2 * L - 1)).erase (L - 1) := hi.2
    have hlt : i.2 < 2 * L - 1 := mem_range.mp (mem_of_mem_erase hi2)
    exact tentR_sq_div_le_one L i.2 (by omega) hL
  have hsum_le_card : (∑ i ∈ S, (tentR L i.2 / (L : ℝ)) ^ 2) ≤ (S.card : ℝ) := by
    calc (∑ i ∈ S, (tentR L i.2 / (L : ℝ)) ^ 2)
        ≤ ∑ _i ∈ S, (1 : ℝ) := sum_le_sum hwsq
      _ = (S.card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
  have hcardR : (S.card : ℝ) = (P : ℝ) * (2 * (L : ℝ) - 2) := by
    rw [hS, offRidge_card L P hL]
    have h2L : 2 ≤ 2 * L := by omega
    push_cast [Nat.cast_sub h2L]
    ring
  have hK : (1/2) * (∑ i ∈ S, (tentR L i.2 / (L : ℝ)) ^ 2) ≤ (L : ℝ) ^ d := by
    have h1 : (1/2) * (∑ i ∈ S, (tentR L i.2 / (L : ℝ)) ^ 2) ≤ (1/2) * (S.card : ℝ) :=
      by linarith [hsum_le_card]
    rw [hcardR] at h1
    have h2 : (1/2) * ((P : ℝ) * (2 * (L : ℝ) - 2)) = (P : ℝ) * ((L : ℝ) - 1) := by ring
    rw [h2] at h1
    linarith [hPd]
  exact r2_weighted S (fun i => tentR L i.2 / (L : ℝ)) (fun i => a i.1 i.2)
    (∑ p ∈ range P, a p (L - 1)) ((L : ℝ) ^ d) hK

/-- The true transverse count `P = L^{d−1}` satisfies the hypothesis `P·(L−1) ≤ L^d` of
`cross_section_2125c`, for `d ≥ 1` (`L^{d−1}(L−1) = L^d − L^{d−1} ≤ L^d`). -/
theorem transverse_count_ok (L d : ℕ) (hd : 1 ≤ d) :
    ((L ^ (d - 1) : ℕ) : ℝ) * ((L : ℝ) - 1) ≤ (L : ℝ) ^ d := by
  have hpow : (L : ℝ) ^ (d - 1) * (L : ℝ) = (L : ℝ) ^ d := by
    rw [← pow_succ]; congr 1; omega
  have hnn : (0 : ℝ) ≤ (L : ℝ) ^ (d - 1) := by positivity
  rw [Nat.cast_pow]
  nlinarith [hpow, hnn]

#print axioms quad_lower
#print axioms r2_core
#print axioms r2_weighted
#print axioms tentR_le
#print axioms tentR_sq_div_le_one
#print axioms cross_section_2125c
#print axioms transverse_count_ok

end AdalyFormal.Balaban.CrossSectionDecomp
