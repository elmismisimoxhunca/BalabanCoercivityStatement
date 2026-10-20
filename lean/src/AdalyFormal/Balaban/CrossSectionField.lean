/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BlockPoincareLemma24
import AdalyFormal.Balaban.CrossSectionDecomp

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# CMP96 p.244-245: the cross-sectional `Δ'` field object, `(2.124)` telescoping, and the
# `(2.125)` Abel-resummation identity — the last absent primitive of the U=1 Lemma 2.4 chain.

## Source pins (LAW-11, page image read directly: `compute/norm_dictionary/renders/CMP96_p245_pdf23-23.png`)

Coarse bond `c = ⟨y, y+L e_μ⟩`, `c₋ = y`, `c₊ = y+L e_μ`, `μ` the longitudinal direction. p.245:

* **"We identify `B(b) = B_μ(x)` for `b = ⟨x, x+e_μ⟩`."** — the longitudinal bond field.
* **`Δ'`** = top μ-layer of `B(y)`: `{x ∈ blockOf y ell : x_μ = y_μ + (ell−1)}` (a `(d−1)`-dim slice).
* **`Δ''`** = bottom μ-layer of `B(y+L e_μ)`: `{x ∈ blockOf (coarseShift y ell μ) ell : x_μ = (y+L e_μ)_μ}`.
* **`(2.124)`**: `Σ_{p⊂B(c)} |(∂₁B)(p)|² ≥ ⅓ Σ_{b⊂Δ'} |(∂B_μ)(b)|² − Σ_{b⊂Δ'} |B(b)|² − Σ_{b⊂Δ''} |B(b)|²`.
  **Read carefully (fidelity finding, `compute/xsec_field/check_2124.py`):** the correction terms
  `Σ_{b⊂Δ'} |B(b)|²`, `Σ_{b⊂Δ''} |B(b)|²` are the **transverse** `ν`-bonds (`ν ≠ μ`) inside `Δ'`,
  `Δ''` — their actual value `B(⟨x,x+e_ν⟩)` — NOT the longitudinal `B_μ`. The `B(b)=B_μ` identification
  applies ONLY to longitudinal bonds. The region `B(c)` = the single layer of `(μ,ν)`-plaquettes based
  at `x ∈ Δ'`, `ν ≠ μ` (the arrows in the p.245 figure connecting `Δ'` to `Δ''`).
* **`(2.125)` resummation identity** (first two lines of `(2.125)`, an EQUALITY):
  `(Q₁B)(c) = L^{-d}Σ_{x∈B(y)\Δ'} L^{-1}(x_μ−y_μ+1)B_μ(x) + L^{-d}Σ_{x∈Δ'}B_μ(x) + L^{-d}Σ_{x∈B(y+Le_μ)} L^{-1}(2L−1+y_μ−x_μ)B_μ(x)`.

## Numeric confirmation FIRST (`compute/xsec_field/`, PYTHONHASHSEED=0, all set-ids pinned)

* `confirm_xsec.py`/`run_confirm.py`: the `(2.125)` resummation identity is EXACT,
  `max|lineCoarseRestrict − (verbatim 3-term RHS)| = max|… − (tent form)| = 3.3e-16`, over every
  coarse `(y,μ)` on `{side 4 ell 2, side 6 ell 2, side 6 ell 3}`. The tent form is
  `(1/ell⁴)Σ_{fibers}Σ_{m<2ell−1} tent(ell,m)·B_μ(shift_μ^m x₀)`, `tent(ell,m)=min(m+1,2ell−1−m)`.
* `controls.py`: the per-fiber count identity `Σ_{i<ell}Σ_{j<ell} f(i+j) = Σ_{m<2ell−1} tent(ell,m)f(m)`
  (`tent = #{(i,j)∈[0,ell)²: i+j=m}`) holds to `1e-15`, `ell∈{2,3,4}`; MUT1 (perturbed tent peak)
  makes the resummation FAIL 60/60 — the identity is non-vacuous.
* `check_2124.py`: `(2.124)` TIGHT (correct region + transverse corrections), min-margin `+8.7`/`+33`,
  0 fails; MUT const `1/3→1` fails 2/60, MUT drop-boundary fails 3/60 at ell=2 — corrections load-bearing.

## What is PROVED here (sorry-free, kernel-checked, `#print axioms` clean)

* `crossSectionTop`/`crossSectionBot`/`crossSectionBase` — the `Δ'`, `Δ''`, and μ-fiber-base site
  sets, and `xsecCurl`/`transGrad` fields.
* `xsecCurl_sq_eq_curlValue_sq` — `xsecCurl B x μ ν` (the `(μ,ν)`-curl with `μ` as first leg) squares
  to `curlValue B (crossPlaq …)²`, so the region energy IS a genuine `∂₁`-curl energy (faithful).
* `pointwise_2124` — the elementary `(a+b−c−e)² ≥ ⅓(c−a)² − b² − e²` per-plaquette core.
* **`crossSection_2124`** — CMP96 `(2.124)` summed over `Δ'`, sorry-free. **Closes `[RES-2124-TELESCOPE]`.**
* `pair_conv_tent`/`pair_conv_tentCard` — the per-fiber convolution-count identity `Σ_{i<ell}Σ_{j<ell}
  f(i+j) = Σ_{m<2ell−1} tentCard(ell,m) f(m)`, `tentCard = #{(i,j)∈[0,ell)²: i+j=m}`.
* `block_fiber_sum` — the μ-fiber decomposition `Σ_{x∈blockOf} g = Σ_{x₀∈base}Σ_{i<ell} g(coarseShift
  x₀ i μ)` (the block→fiber bijection, `Finset.sum_bij'`, torus-wrap-free inside the block).
* **`lineCoarseRestrict_resummation`** — CMP96 `(2.125)` resummation `lineCoarseRestrict ell B (⟨y,_⟩,μ)
  = (1/ell⁴)Σ_{x₀∈base}Σ_{m<2ell−1} tentCard(ell,m)·B(coarseShift x₀ m μ,μ)`, kernel identity.
  **Closes `[RES-2125-RESUM-INFRAMEWORK]` AND the block-fiber bijection `[RES-2125-BLOCK-FIBER]`.**

## The remaining step toward `(geom)`/`(2.128)` — NAMED precisely (NOT built here).

The U=1 `(2.128)` is unconditional once `(geom)` is proved (`Lemma24Assembly.lemma24_from_geom`,
kernel-checked, `ell≥2`). This module delivers the two `(geom)`-feeding primitives `(2.124)`
(`crossSection_2124`) and the `(2.125)` resummation (`lineCoarseRestrict_resummation`); the proved
factored core `CrossSectionDecomp.cross_section_2125c` and cross-sectional Poincaré
`Lemma24Assembly.cross_section_2127_smallL` are the other two. What remains is the **assembly**:
* `[RES-2125-TENT-DICT]` — the arithmetic bridge from this module's `tentCard` to
  `cross_section_2125c`'s `tentR`. The WEIGHT-BOUND half `tentCard ell m ≤ ell` (all that
  `r2_weighted`'s Cauchy–Schwarz core needs, giving `(tentCard/ell)² ≤ 1`) is PROVED here
  (`tentCard_le`); the exact `tentCard ell m = tentR ell m = min(m+1,2ell−1−m)` for `m<2ell−1` is the
  remaining (unneeded-for-the-bound) equality;
* `[RES-GEOM-INCIDENCE]` — summing the per-`c` `(2.124)+(2.125ᶜ)+(2.127)` over `c∈Λ'` into `(geom)`:
  the finite slab/block incidence bookkeeping (`slabCurlEnergy = 2·totalCurl` is already proved as
  `Lemma24Assembly.slabCurlEnergy_eq_two_totalCurl`; the cross-block `Sbet` lower-bound and the
  `6·Sin` boundary-correction count are the remaining finite combinatorics). `(geom)`'s BINDING regime
  is `Sin≈0`/cross-block, where the `(2.121)` admissibility is load-bearing (`compute/xsec_field/
  check_geom.py`: on random `B` `(geom)` is vacuously true, its RHS dominated by `−6·Sin`).
-/

namespace AdalyFormal.Balaban.CrossSectionField

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.CrossSectionDecomp
open AdalyFormal.Balaban.CoarseCurl

variable {L : PeriodicLatticeExtent}

/-! ## §1. The cross-sectional `Δ'`, `Δ''` site sets and the longitudinal/transverse fields. -/

/-- **`Δ'` — the top μ-layer of the block `B(y)`.** Sites of `blockOf y ell` whose μ-coordinate is
`y_μ + (ell−1)` (the `(d−1)`-dimensional cross-section at the far μ-face of the block). -/
def crossSectionTop (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    Finset (PeriodicLatticeSite L) :=
  (blockOf y ell).filter (fun x => (x μ).val = (y μ).val + (ell - 1))

theorem mem_crossSectionTop {y x : PeriodicLatticeSite L} {ell : ℕ} {μ : Fin 3} :
    x ∈ crossSectionTop y ell μ ↔ x ∈ blockOf y ell ∧ (x μ).val = (y μ).val + (ell - 1) := by
  simp [crossSectionTop]

/-- **`Δ''` — the bottom μ-layer of the next block `B(y + L e_μ)`.** Sites of
`blockOf (coarseShift y ell μ) ell` whose μ-coordinate is that block's base μ-coordinate. -/
noncomputable def crossSectionBot (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    Finset (PeriodicLatticeSite L) :=
  (blockOf (coarseShift y ell μ) ell).filter
    (fun x => (x μ).val = ((coarseShift y ell μ) μ).val)

/-- **`xsecCurl B x μ ν` — the `(μ,ν)`-plaquette curl written with `μ` as the first leg:**
`B(x,μ) + B(x+e_μ,ν) − B(x+e_ν,μ) − B(x,ν)`. Equals `± curlValue B (ordered (μ,ν) plaquette)`, so its
square is a genuine `∂₁`-curl energy (`xsecCurl_sq_eq_curlValue_sq`). -/
def xsecCurl (B : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ ν : Fin 3) : ℝ :=
  B (x, μ) + B (periodicLatticeShift x μ, ν)
    - B (periodicLatticeShift x ν, μ) - B (x, ν)

/-- **`transGrad B x μ ν = B_μ(x+e_ν) − B_μ(x)`** — the transverse (`ν`-direction) gradient of the
longitudinal field `B_μ`, the object `(∂B_μ)(b)` for `b = ⟨x, x+e_ν⟩`. -/
def transGrad (B : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ ν : Fin 3) : ℝ :=
  B (periodicLatticeShift x ν, μ) - B (x, μ)

/-! ## §2. `(2.124)` — the elementary per-plaquette telescoping. -/

/-- **The pointwise `(2.124)` core.** For any four reals, `(a+b−c−e)² ≥ ⅓(c−a)² − b² − e²`. With
`a=B_μ(x)`, `b=B_ν(x+e_μ)`, `c=B_μ(x+e_ν)`, `e=B_ν(x)`: `a+b−c−e` is the plaquette curl, `c−a` the
transverse gradient of `B_μ`, and `b`, `e` the transverse `ν`-bonds at `Δ''`, `Δ'`. Proof: `c−a
= (b−e)−curl`, then `(b−e−curl)² ≤ 3(b²+e²+curl²)` (the `(X+Y+Z)²≤3(X²+Y²+Z²)` SOS). -/
theorem pointwise_2124 (a b c e : ℝ) :
    (1/3) * (c - a) ^ 2 - b ^ 2 - e ^ 2 ≤ (a + b - c - e) ^ 2 := by
  nlinarith [sq_nonneg (b + e), sq_nonneg (b + (a + b - c - e)), sq_nonneg (e - (a + b - c - e))]

/-- The ordered plaquette in the `(μ,ν)` coordinate plane based at `x` (picks the `<`-ordered pair). -/
noncomputable def crossPlaq (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : μ ≠ ν) :
    PeriodicLatticePlaquette L :=
  if hlt : μ < ν then (x, ⟨(μ, ν), hlt⟩)
  else (x, ⟨(ν, μ), lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm h)⟩)

/-- **`xsecCurl` squares to the genuine `∂₁`-curl energy.** `xsecCurl B x μ ν ^ 2
= curlValue B (crossPlaq x μ ν h)^2`, so the cross-section region energy is a faithful
`Σ |(∂₁B)(p)|²`. When `μ<ν` they are equal; when `ν<μ`, `xsecCurl = −curlValue`, squares agree. -/
theorem xsecCurl_sq_eq_curlValue_sq (B : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ ν : Fin 3)
    (h : μ ≠ ν) :
    xsecCurl B x μ ν ^ 2 = curlValue B (crossPlaq x μ ν h) ^ 2 := by
  unfold xsecCurl crossPlaq curlValue
  by_cases hlt : μ < ν
  · simp only [hlt, dif_pos]
  · simp only [hlt, dif_neg, not_false_iff]
    ring

#print axioms pointwise_2124
#print axioms xsecCurl_sq_eq_curlValue_sq

/-! ### The cross-sectional energies (region curl, transverse gradient, transverse bonds). -/

/-- Transverse directions to `μ`: `{ν : Fin 3 // ν ≠ μ}`, as a `Finset`. -/
def transDirs (μ : Fin 3) : Finset (Fin 3) := Finset.univ.erase μ

theorem mem_transDirs {μ ν : Fin 3} : ν ∈ transDirs μ ↔ ν ≠ μ := by
  simp [transDirs]

/-- Region curl energy `Σ_{p⊂B(c)} |(∂₁B)(p)|²` = `Σ_{x∈Δ'} Σ_{ν≠μ} xsecCurl²`. -/
noncomputable def regionCurlEnergy (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    ℝ :=
  ∑ x ∈ crossSectionTop y ell μ, ∑ ν ∈ transDirs μ, xsecCurl B x μ ν ^ 2

/-- Transverse-gradient energy `⅓Σ_{b⊂Δ'}|(∂B_μ)(b)|²`'s summand set: `Σ_{x∈Δ'} Σ_{ν≠μ} transGrad²`. -/
noncomputable def transGradEnergy (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    ℝ :=
  ∑ x ∈ crossSectionTop y ell μ, ∑ ν ∈ transDirs μ, transGrad B x μ ν ^ 2

/-- Transverse `ν`-bond energy at `Δ'`: `Σ_{b⊂Δ'}|B(b)|²` = `Σ_{x∈Δ'} Σ_{ν≠μ} B(x,ν)²`. -/
noncomputable def transBondTop (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    ℝ :=
  ∑ x ∈ crossSectionTop y ell μ, ∑ ν ∈ transDirs μ, B (x, ν) ^ 2

/-- Transverse `ν`-bond energy at `Δ''`: `Σ_{b⊂Δ''}|B(b)|²` = `Σ_{x∈Δ'} Σ_{ν≠μ} B(x+e_μ,ν)²`
(the site `x+e_μ` lies in `Δ''` for `x∈Δ'`). -/
noncomputable def transBondBot (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    ℝ :=
  ∑ x ∈ crossSectionTop y ell μ, ∑ ν ∈ transDirs μ, B (periodicLatticeShift x μ, ν) ^ 2

/-- **CMP96 `(2.124)`, summed over the cross-section `Δ'`, sorry-free.**
`regionCurlEnergy ≥ ⅓·transGradEnergy − transBondTop − transBondBot`, i.e.
`Σ_{p⊂B(c)}|(∂₁B)(p)|² ≥ ⅓Σ_{b⊂Δ'}|(∂B_μ)(b)|² − Σ_{b⊂Δ'}|B(b)|² − Σ_{b⊂Δ''}|B(b)|²`.
Proof: the pointwise `pointwise_2124` per `(x,ν)`, summed (the three RHS sums split off). -/
theorem crossSection_2124 (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    (1/3) * transGradEnergy B y ell μ - transBondTop B y ell μ - transBondBot B y ell μ
      ≤ regionCurlEnergy B y ell μ := by
  unfold regionCurlEnergy transGradEnergy transBondTop transBondBot
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro ν _
  -- pointwise: ⅓(transGrad)² − B(x+eμ,ν)² − B(x,ν)² ≤ xsecCurl²
  have := pointwise_2124 (B (x, μ)) (B (periodicLatticeShift x μ, ν))
    (B (periodicLatticeShift x ν, μ)) (B (x, ν))
  unfold xsecCurl transGrad
  linarith [this]

#print axioms crossSection_2124

/-! ## §3. The per-fiber convolution-count identity — the mathematical core of `(2.125)`. -/

/-- **The per-fiber count identity.** For any `f : ℕ → ℝ`,
`Σ_{i<ell} Σ_{j<ell} f(i+j) = Σ_{m<2ell−1} tentN(ell,m)·f(m)`, where `tentN ell m = #{(i,j)∈[0,ell)²
: i+j=m}` is the discrete tent multiplicity. This is the exact combinatorial mechanism the `(2.125)`
Abel resummation rests on (`compute/xsec_field/controls.py`, `max err 1e-15`). Proved by rewriting the
double sum as a sum over the fibre of `i+j`. -/
theorem pair_conv_tent (ell : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ range ell, ∑ j ∈ range ell, f (i + j)
      = ∑ m ∈ range (2 * ell - 1),
          ((((range ell ×ˢ range ell).filter (fun p => p.1 + p.2 = m)).card : ℝ) * f m) := by
  have hmaps : ∀ p ∈ range ell ×ˢ range ell, p.1 + p.2 ∈ range (2 * ell - 1) := by
    intro p hp
    rw [Finset.mem_product] at hp
    have h1 := Finset.mem_range.mp hp.1
    have h2 := Finset.mem_range.mp hp.2
    rw [Finset.mem_range]; omega
  have key := Finset.sum_fiberwise_of_maps_to hmaps (fun p => f (p.1 + p.2))
  rw [← Finset.sum_product']
  rw [← key]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])]
  rw [Finset.sum_const, nsmul_eq_mul]

#print axioms pair_conv_tent

/-- The discrete tent multiplicity `#{(i,j)∈[0,ell)² : i+j=m}` as a named `ℕ`. Equals
`min(m+1, 2ell−1−m)` on `[0,2ell−2]` (the `tentR` of `CrossSectionDecomp` over `ℝ`). -/
def tentCard (ell m : ℕ) : ℕ :=
  ((range ell ×ˢ range ell).filter (fun p => p.1 + p.2 = m)).card

theorem pair_conv_tentCard (ell : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ range ell, ∑ j ∈ range ell, f (i + j)
      = ∑ m ∈ range (2 * ell - 1), (tentCard ell m : ℝ) * f m := by
  rw [pair_conv_tent]; rfl

/-- **The tent multiplicity never exceeds the block side:** `tentCard ell m ≤ ell`. Each fiber
`{(i,j)∈[0,ell)² : i+j=m}` is determined by its first coordinate `i<ell` (the second is `m−i`), so
its cardinality is `≤ #(range ell) = ell`. This is the weight bound `(2.125ᶜ)`'s Cauchy–Schwarz core
(`CrossSectionDecomp.r2_weighted`) needs — `(tentCard/ell)² ≤ 1` — the arithmetic half of
`[RES-2125-TENT-DICT]`. -/
theorem tentCard_le (ell m : ℕ) : tentCard ell m ≤ ell := by
  unfold tentCard
  calc ((range ell ×ˢ range ell).filter (fun p => p.1 + p.2 = m)).card
      ≤ (range ell).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.1)
        · intro p hp
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
          exact hp.1.1
        · intro p hp q hq hpq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_range] at hp hq
          have hfst : p.1 = q.1 := hpq
          refine Prod.ext hfst ?_
          have hpm := hp.2; have hqm := hq.2
          omega
    _ = ell := card_range ell

#print axioms tentCard_le

/-! ## §4. The μ-fiber decomposition of a block sum — the block→fiber index bijection. -/

/-- The μ-bottom layer of `B(y)`: the fiber bases `{x ∈ blockOf y ell : x_μ = y_μ}`. Each block
site is `coarseShift x₀ i μ` for a unique base `x₀` and offset `i < ell`. -/
def crossSectionBase (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    Finset (PeriodicLatticeSite L) :=
  (blockOf y ell).filter (fun x => (x μ).val = (y μ).val)

/-- The fiber base of a block site `x`: set its μ-coordinate to `y_μ`. -/
def fiberBase (y : PeriodicLatticeSite L) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    PeriodicLatticeSite L :=
  Function.update x μ (y μ)

/-- The μ-coordinate of `fiberBase` is `y_μ`; other coordinates are `x`'s. -/
theorem fiberBase_apply_self (y x : PeriodicLatticeSite L) (μ : Fin 3) :
    (fiberBase y x μ) μ = y μ := by rw [fiberBase]; exact Function.update_self μ (y μ) x

theorem fiberBase_apply_ne (y x : PeriodicLatticeSite L) {μ ν : Fin 3} (h : ν ≠ μ) :
    (fiberBase y x μ) ν = x ν := by rw [fiberBase]; exact Function.update_of_ne h (y μ) x

/-- **Left inverse (fiber ⟶ block):** `coarseShift (fiberBase y x μ) (x_μ−y_μ) μ = x`, for a block
site `x`. -/
theorem coarseShift_fiberBase {y x : PeriodicLatticeSite L} {ell : ℕ} {μ : Fin 3}
    (hx : inBlock y ell x) :
    coarseShift (fiberBase y x μ) ((x μ).val - (y μ).val) μ = x := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    apply Fin.ext
    rw [coarseShift_val_eq, fiberBase_apply_self]
    have h1 := (hx ν).1; have h2 := (hx ν).2
    have hsum : (y ν).val + ((x ν).val - (y ν).val) = (x ν).val := by omega
    rw [hsum, Nat.mod_eq_of_lt (x ν).isLt]
  · rw [coarseShift_apply_ne _ _ _ _ hν, fiberBase_apply_ne _ _ hν]

/-- **Right inverse, fst (block ⟶ fiber):** `fiberBase y (coarseShift x₀ i μ) μ = x₀`, for a base
site `x₀` (`x₀_μ = y_μ`). -/
theorem fiberBase_coarseShift {y x0 : PeriodicLatticeSite L} {μ : Fin 3}
    (hx0 : (x0 μ).val = (y μ).val) (i : ℕ) :
    fiberBase y (coarseShift x0 i μ) μ = x0 := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    rw [fiberBase_apply_self]
    exact (Fin.ext hx0.symm)
  · rw [fiberBase_apply_ne _ _ hν, coarseShift_apply_ne _ _ _ _ hν]

/-- **The μ-fiber decomposition of a block sum.** For a fitting center (`y_ν+ell ≤ side_ν`),
`Σ_{x∈blockOf y ell} g x = Σ_{x₀∈base} Σ_{i<ell} g (coarseShift x₀ i μ)`, i.e. the block is the
disjoint μ-fibered union of its bottom layer. Proved by `Finset.sum_bij'` with forward
`x ↦ (fiberBase x, x_μ−y_μ)` and backward `(x₀,i) ↦ coarseShift x₀ i μ`; the coordinate bookkeeping
uses `coarseShift_val_eq` (μ-coord `= (x₀_μ+i) mod side`) and `coarseShift_apply_ne` (other coords
fixed), with `y_μ+i < side` ruling out μ-wrap inside the block. -/
theorem block_fiber_sum (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3)
    (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1) (g : PeriodicLatticeSite L → ℝ) :
    ∑ x ∈ blockOf y ell, g x
      = ∑ x0 ∈ crossSectionBase y ell μ, ∑ i ∈ range ell, g (coarseShift x0 i μ) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (fun x _ => (fiberBase y x μ, (x μ).val - (y μ).val))
    (fun p _ => coarseShift p.1 p.2 μ)
    ?_ ?_ ?_ ?_ ?_
  · -- forward maps into base ×ˢ range ell
    intro x hx
    rw [mem_blockOf] at hx
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · show fiberBase y x μ ∈ crossSectionBase y ell μ
      rw [crossSectionBase, Finset.mem_filter, mem_blockOf]
      refine ⟨fun ν => ?_, ?_⟩
      · by_cases hν : ν = μ
        · subst hν
          rw [fiberBase_apply_self]
          exact ⟨le_refl _, by have h1 := (hx ν).1; have h2 := (hx ν).2; omega⟩
        · rw [fiberBase_apply_ne _ _ hν]; exact hx ν
      · rw [fiberBase_apply_self]
    · show (x μ).val - (y μ).val ∈ range ell
      rw [Finset.mem_range]; have h1 := (hx μ).1; have h2 := (hx μ).2; omega
  · -- backward maps into blockOf
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [crossSectionBase, Finset.mem_filter, mem_blockOf] at hp1
    rw [Finset.mem_range] at hp2
    rw [mem_blockOf]
    intro ν
    by_cases hν : ν = μ
    · subst hν
      rw [coarseShift_val_eq, hp1.2]
      have hlt : (y ν).val + p.2 < L ν + 1 := by have := hfit ν; omega
      rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [coarseShift_apply_ne _ _ _ _ hν]; exact hp1.1 ν
  · -- left inverse
    intro x hx
    rw [mem_blockOf] at hx
    show coarseShift (fiberBase y x μ) ((x μ).val - (y μ).val) μ = x
    exact coarseShift_fiberBase (ell := ell) hx
  · -- right inverse
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [crossSectionBase, Finset.mem_filter, mem_blockOf] at hp1
    rw [Finset.mem_range] at hp2
    have hval : ((coarseShift p.1 p.2 μ) μ).val = (y μ).val + p.2 := by
      rw [coarseShift_val_eq, hp1.2]
      have hlt : (y μ).val + p.2 < L μ + 1 := by have := hfit μ; omega
      exact Nat.mod_eq_of_lt hlt
    refine Prod.ext ?_ ?_
    · exact fiberBase_coarseShift hp1.2 p.2
    · show ((coarseShift p.1 p.2 μ) μ).val - (y μ).val = p.2
      rw [hval]; omega
  · -- g-compatibility
    intro x hx
    rw [mem_blockOf] at hx
    show g x = g (coarseShift (fiberBase y x μ) ((x μ).val - (y μ).val) μ)
    rw [coarseShift_fiberBase (ell := ell) hx]

#print axioms coarseShift_fiberBase
#print axioms fiberBase_coarseShift
#print axioms block_fiber_sum

/-! ## §5. The `(2.125)` resummation identity, in-framework — `[RES-2125-RESUM-INFRAMEWORK]` CLOSED. -/

/-- **CMP96 `(2.125)` resummation identity, in the framework's own `lineCoarseRestrict`.** For a
fitting center,
`lineCoarseRestrict ell B (⟨y,_⟩, μ)
  = (1/ell⁴)·Σ_{x₀∈Δbase} Σ_{m<2ell−1} tentCard(ell,m)·B(coarseShift x₀ m μ, μ)`.
This is the exact Abel/tent resummation (`compute/xsec_field/`: residual `3.3e-16`), now a kernel
identity: the block μ-fibers (`block_fiber_sum`), each fiber telescopes by the convolution-count
`pair_conv_tentCard`, and `shift^[j]∘shift^[i] = shift^[i+j]` (`Function.iterate_add_apply`). Closes
`[RES-2125-RESUM-INFRAMEWORK]`. -/
theorem lineCoarseRestrict_resummation (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3)
    (hy : y ∈ CoarseLattice L ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1) (B : Bond L → ℝ) :
    lineCoarseRestrict ell B (⟨y, hy⟩, μ)
      = (1 / (ell : ℝ) ^ 4) * ∑ x0 ∈ crossSectionBase y ell μ,
          ∑ m ∈ range (2 * ell - 1), (tentCard ell m : ℝ) * B (coarseShift x0 m μ, μ) := by
  unfold lineCoarseRestrict
  congr 1
  -- ∑_{x∈blockOf} lineIntegralValue = ∑_{x0} ∑_{m} tentCard · B(coarseShift x0 m μ,μ)
  rw [block_fiber_sum y ell μ hfit (fun x => lineIntegralValue ell B x μ)]
  apply Finset.sum_congr rfl
  intro x0 _
  -- per fiber: ∑_{i<ell} lineIntegralValue ell B (coarseShift x0 i μ) μ = ∑_m tentCard · B(...)
  have hfib : ∀ i, lineIntegralValue ell B (coarseShift x0 i μ) μ
      = ∑ j ∈ range ell, B (coarseShift x0 (i + j) μ, μ) := by
    intro i
    unfold lineIntegralValue coarseShift
    apply Finset.sum_congr rfl
    intro j _
    rw [← Function.iterate_add_apply, Nat.add_comm j i]
  rw [Finset.sum_congr rfl (fun i _ => hfib i)]
  -- now ∑_{i<ell} ∑_{j<ell} B(coarseShift x0 (i+j) μ, μ) = ∑_m tentCard · B(coarseShift x0 m μ,μ)
  exact pair_conv_tentCard ell (fun m => B (coarseShift x0 m μ, μ))

#print axioms lineCoarseRestrict_resummation

end AdalyFormal.Balaban.CrossSectionField
