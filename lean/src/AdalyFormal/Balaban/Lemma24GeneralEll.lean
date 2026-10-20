/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.GeomScratch
import AdalyFormal.Balaban.BlockOperatorGap

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# CMP96 Lemma 2.4 / `(2.128)` for GENERAL block side `ell` — via Bałaban's own route, with the
# cross-sectional exponent CORRECTED from the printed `L^{-d-1}` to the true `L^{-d-2}`.

No numeric certificate, no SOS, no per-`ell` Gram object: the whole file is analytic.

## Source pin (LAW-11: 600 dpi renders made by this lane, read directly)

* `compute/lemma24_general_ell/CMP96_pdf23-23.png` — CMP96 (Bałaban, *Propagators for Lattice
  Gauge Theories II*, CMP **95** (1984) 17-40... printed pp. 222+), printed **p.245** (offset 222,
  `corpus/tools/page_offsets.json`, `constant_verified: true`; the running head reads "245").
  Contains `(2.124)`–`(2.128)` and the statement of Lemma 2.4.
* `compute/lemma24_general_ell/CMP96_pdf22-22.png` — printed **p.244**: `(2.120)`–`(2.123)`.
* Zooms: `zoom_2124.png`, `zoom_2125.png`, `zoom_2126.png`, `zoom_sentence_2126_2127.png`,
  `zoom_2127.png`.

### VERBATIM (600 dpi)

p.244, after (2.122):
> "Next let us consider bonds `b ∈ B(c) = {b : b₋ ∈ B(c₋), b₊ ∈ B(c₊)}` for some `c ∈ Λ'`.
> Let `c = ⟨y, y+Le_μ⟩` and `Δ'`, `Δ''` denote the intersection of the planes
> `x_μ = c_{+,μ} − 1 = y_μ + (L−1)`, `x_μ = c_{+,μ} = y_μ + L` with the blocks `B(c₋)`, `B(c₊)`
> correspondingly, as indicated in the figure below."

This PINS `Δ'` = the top `μ`-layer of `B(y)` (= `CrossSectionField.crossSectionTop`), `Δ''` = the
bottom `μ`-layer of `B(y+Le_μ)`, and `Σ_{b∈B(c)}|B(b)|²` = the LONGITUDINAL top-face energy
(= `GeomScratch.topFaceEnergy`) — the reading this file uses.

(2.123): `Σ_{b⊂B(y)}|B(b)|² ≤ d L^d Σ_{p⊂B(y)}|(∂₁B)(p)|²`   (= `region_2123`, PROVED in-tree).

(2.126): `L^{-d}Σ_{p⊂B(c)}|(∂₁B)(p)|² + |(Q₁B)(c)|² ≧ ⅓( L^{-d}Σ_{b⊂Δ'}|(∂B_μ)(b)|²
  + L^{-2}|Σ_{x∈Δ'}L^{-(d-1)}B_μ(x)|² ) − L^{-d}Σ_{b⊂B(c₋)}|B(b)|² − L^{-d}Σ_{b⊂B(c₊)}|B(b)|².`

Sentence between (2.126) and (2.127):
> "The terms in parentheses on the right-hand side can be written as
> `L^{-2}⟨B,(Δ_{Δ'}^{L^{-1},N} + Q'*_{Δ'}Q'_{Δ'})B⟩`, where the operators are defined on a
> `d−1`-dimensional lattice. This quadratic form is bounded from below by
> `L^{-d-1} Σ_{x∈Δ'}|B_μ(x)|²`, hence"

(2.127): `L^{-d}Σ_{p⊂B(c)}|(∂₁B)(p)|² + |(Q₁B)(c)|² ≧ ⅓L^{-d-1}Σ_{b∈B(c)}|B(b)|²
  − L^{-d}Σ_{b⊂B(c₋)}|B(b)|² − L^{-d}Σ_{b⊂B(c₊)}|B(b)|².`

(2.128): `L^{d-2}Σ_{c∈Λ'}|(Q₁B)(c)|² + Σ_p|(∂₁B)(p)|² ≧ (1/(12d²)) L^{-d-1}‖B‖².`

The exponent `-d-1` (LEADING MINUS) is re-confirmed at 600 dpi in the sentence, in (2.127) and in
(2.128).

## THE FINDING — the printed (2.126)→(2.127) step is FALSE for `L ≥ 10`.

Write `G = Σ_{b⊂Δ'}|∂B_μ(b)|²` (the interior/Neumann transverse gradient energy of `B_μ` on the
`L^{d-1}`-site face `Δ'`), `m = L^{-(d-1)}Σ_{Δ'}B_μ`, `T = Σ_{x∈Δ'}|B_μ(x)|²`, and
`V = T − L^{d-1}m²`.  The parenthesised quantity of (2.126) is `P = L^{-d}G + L^{-2}m²`.

Since `T = V + L^{d-1}m²`, the MEAN modes of the claim `P ≥ L^{-d-1}T` cancel EXACTLY
(`L^{-d-1}·L^{d-1}m² = L^{-2}m²`), so the claim is EQUIVALENT to the normalisation-free statement

>   `V ≤ L · G`   on every field on the side-`L`, `(d−1)`-dimensional grid.

The sharp constant is `V ≤ λ₁(L)^{-1}G` with `λ₁(L) = 2(1 − cos(π/L))` (first nonzero Neumann
eigenvalue of the side-`L` grid graph).  So the printed step holds iff `2L(1 − cos(π/L)) ≥ 1`:
true for `L ≤ 9`, FALSE from `L = 10` (`2·10·(1 − cos 18°) = 0.978871… < 1`).  Witnesses
(corrected 2026-08-08, kernel-proved in `compute/erratum_2127/stage/Erratum2127.lean`): the linear
field `f(x) = x_ν` has `V/G = L(L+1)/12`, which exceeds `L` only for `L ≥ 12` — it is NOT a
witness at `L ∈ {10, 11}` (`linear_not_witness_ten_eleven` proves this in-kernel); the failure at
the threshold is witnessed by the explicit rational fields `w10`/`w11` there, and the full
threshold statement (holds for `2 ≤ L ≤ 9`, fails from `L = 10`, corrected exponent always) is
`theorem erratum_2127`, sorryAx-free.

**This is an INTERNAL inconsistency of CMP96, needing no outside input.**  p.242 (2.109)-(2.110)
states, "in momentum representation on the unit lattice", that `Δ₀ + a Q'₁*Q'₁ ≥ γ₀'` with
"in fact we may get `γ₀' = π²/L²`".  But `P = L^{-d}⟨B,(Δ₀ + aQ'₁*Q'₁)B⟩` with `a = L^{d-2} ≥ 1`,
so p.242 gives `P ≥ π²·L^{-d-2}·T`, which implies p.245's `P ≥ L^{-d-1}T` only when `π² ≥ L`.
`π² = 9.8696…` — exactly the threshold `L ≤ 9` the spectral computation gives.  p.242 is right;
p.245's `L^{-d-1}` over-states it by a factor `L/π²`.

CONSEQUENCE for the tree: `GeomScratch.lemma24_from_perC`'s hypothesis `hPerC` IS `(2.127)×L^{d-2}`
at `d = 3` (with the source's `Σ_{b∈B(c)}` = `topFaceEnergy`), so its ONLY known derivation is the
broken one, from `ell ≥ 10`.  `hPerC` is moreover FALSE outright from `ell = 119`: take `B`
supported only on the longitudinal top-face bonds `(x,μ)`, `x ∈ crossSectionTop y ell μ`, every
block's face carrying the same zero-mean transverse profile `g`.  Such a `B` is admissible
(`Γ_{y,x}` never leaves its block, so it never uses those bonds), has `boundaryCorr(c) = 0` and
`lineCoarseRestrict ≡ 0`, and reduces `hPerC` to `Σg² ≤ 3·ell·R` with `R` the two-direction torus
Dirichlet energy of `g`; the sharp constant is the `Z_ell × Z_ell` graph-Laplacian gap
`λ₁ = 2(1−cos(2π/ell))`, so `hPerC` fails exactly when `3·ell·λ₁ < 1`, i.e. from `ell = 119`
(`3·119·λ₁ = 0.995023 < 1`; asymptotically `3ell·λ₁ → 12π²/ell = 118.435/ell`).  Verified, with the
closed form cross-checked against brute-force eigenvalues at `n = 3..6` (relative error `≤ 2e-16`),
in `compute/lemma24_general_ell/hperc_witness.py`.  [An earlier draft of this docstring said
"`false for ell ≳ 8`" — SUPERSEDED, that numeral was asserted without computation and is wrong by
more than an order of magnitude; the corrected threshold is `ell = 119`.]  Either way that route is
NOT taken here.

## WHAT IS PROVED HERE (unconditional, kernel-checked, `#print axioms` clean, no `sorry`)

`lemma24_general_ell` : for EVERY `ell ≥ 2`, every torus with `ell < L ν + 1` and `ell ∣ L ν + 1`,
and every `(2.121)`-admissible `B`,

>   `ell·Σ_c |(Q₁B)(c)|² + Σ_p |(∂₁B)(p)|²  ≥  (1/180)·ell^{-5}·‖B‖²`

(`Lemma24ConclusionCorrected`).  This is `(2.128)` at `d = 3` with `L^{-d-1}` replaced by the
exponent the cross-sectional gap actually supports, `L^{-d-2} = ell^{-5}`.

The chain is Bałaban's own, all of it general in `ell`:
* `face_poincare` — the corrected cross-sectional bound `T ≤ ell²G + S²/ell²`, from the PROVED
  `DiscreteNeumannPoincare.var2_le_nsq` and `BlockOperatorGap.sumSq2_split` (the p.242 two-mode
  split: `Δ₀` on the fluctuation, `Q'*Q'` on the mean).
* `face_2124` — CMP96 (2.124) in face coordinates: `G ≤ 3·R + 6·Corr`, from the proved pointwise
  core `CrossSectionField.pointwise_2124`, summed over the INTERIOR face bonds only (both endpoints
  in `Δ'`, resp. `Δ''` — the source's own `Σ_{b⊂Δ'}`), which is what keeps the correction inside
  `bondsInBlock`.
* `cs_2125` — CMP96 (2.125): `Q(c) = ell^{-3}S + ell^{-4}·(off-ridge)` (`Q_decomp`, an exact
  identity: the Abel ridge `k+m = ell−1` has exactly `ell` members and lands on `Δ'`), plus
  Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) and `CrossSectionDecomp.quad_lower`.
* `perC_bond` — the per-coarse-bond assembly.
* `lemma24_general_ell` — the global assembly, consuming the banked
  `BlockPoincareLemma24.region_2123` ((2.123)), `GeomScratch.sum_topFace_ge_Sbet`,
  `GeomScratch.sum_boundaryCorr_le`, `GeomScratch.sum_regionCurl_le_slabCurl`,
  `Lemma24Assembly.slabCurlEnergy_eq_two_totalCurl`, `Lemma24Assembly.inBlockCurl_le_total`.

### The arithmetic, and why `ell^{-4}` is out of reach by this route
With per-`c` constant `κ = (1/3)ell^{-3}·θ`, the assembly yields
`‖B‖² ≤ (3ell⁴/θ)·Qtot + [3ell³ + 6ell/θ + 54ell⁴/θ]·Ptot`, so `Lemma24Conclusion`'s `ell^{-4}`
needs `θ ≥ (6ell + 54ell⁴)/(108ell⁴ − 3ell³) → 1/2`.  `θ = 1` is the printed (false) value;
the true `θ = min(2ell(1−cos(π/ell)), 1)` satisfies this only for `ell ≤ 19`; the PROVED in-tree
`var2_le_crude` (`θ = min(2/(ell−1),1)`) only for `ell ≤ 4`; and the PROVED `var2_le_nsq`
(`θ = 1/ell`) for NO `ell ≥ 2` at all — it already fails at `ell = 2`
(`1/2 = 0.5 < 73/142 = 0.51408…`).  [SUPERSEDED, retained struck: an earlier draft of this
docstring said `var2_le_nsq` sufficed "only for `ell ≤ 2`" — that is an off-by-one, caught by this
lane's nested validator; exact-rational check
`compute/lemma24_general_ell/theta_thresholds.py`.  The claim is purely explanatory and is NOT
consumed by any proof in this file; the compiled assembly uses the closed-form
`3ell³ + 6ell² + 162ell⁵ ≤ 180ell⁵`, `3ell⁵ ≤ 180ell⁶` instead.]  Bałaban's constants are TIGHT
(`54/108 = 1/2`): there is no slack in (2.128) to absorb the missing factor of `ell`.

## WHAT IS NOT CLAIMED (no success lie)

* `BlockPoincareLemma24.Lemma24Conclusion ell B` (the printed `(1/108)·ell^{-4}`) is **NOT** proved
  here for general `ell`, and is NOT weakened: it is left exactly as it is.  This file adds a
  SEPARATE, strictly weaker `Prop`.
* This theorem does **NOT** subsume `HrefReduction.lemma24_unconditional_U1_ell2_uncond`.  At
  `ell = 2` that result gives `1/1728`; this one gives `1/5760`, which is WEAKER by a factor
  `10/3`.  The two are consistent, and the implication direction is proved in-file
  (`corrected_of_lemma24`, `ell2_consistency`): the printed conclusion implies the corrected one for
  every `ell ≥ 1`.  So the `ell = 2` milestone remains the strongest statement at `ell = 2`, and
  this file is the strongest statement available at every `ell ≥ 3`.
* Whether `(2.128)` with the printed `L^{-d-1}` is TRUE at large `L` is left OPEN.  It is not
  refuted here — only Bałaban's stated derivation of it is.  The natural repair target is a
  sharpening of (2.123) from `dL^d` to `O(L²)` (the expected sharp axial-gauge 1-form Poincaré
  constant), which would restore the exponent; that is a separate, unbuilt lemma.

## Non-vacuity
`lemma24_general_ell_nonvacuous_ell3` instantiates the theorem at `ell = 3` on the torus
`L ν + 1 = 9` with the unconditional admissible witness
`AdmissibleSubspace.generalWrapConfig`, and exhibits `0 < RHS ≤ LHS` — a genuine
positive-≤-positive instance at `ell = 3`, not `0 ≤ 0`, and not an `ell = 2` witness.

## L12 / S91 note
No `Nonempty`/`∃`-concluding declaration is introduced; no `S91_REGISTRY.tsv` row is triggered.
-/

namespace AdalyFormal.Balaban.Lemma24GeneralEll

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.BlockPoincare
open AdalyFormal.Balaban.BlockPoincareLemma24
open AdalyFormal.Balaban.CrossSectionField
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.Lemma24Assembly
open AdalyFormal.Balaban.DiscretePoincare
open AdalyFormal.Balaban.DiscreteNeumannPoincare
open AdalyFormal.Balaban.BlockOperatorGap
open AdalyFormal.Balaban.CrossSectionDecomp
open GeomScratch

variable {L : PeriodicLatticeExtent}

/-! ## §1. The two transverse directions, and face coordinates on `Δ'`. -/

/-- First transverse direction to `μ`. -/
def nu1 (μ : Fin 3) : Fin 3 := if μ = 0 then 1 else 0

/-- Second transverse direction to `μ`. -/
def nu2 (μ : Fin 3) : Fin 3 := if μ = 2 then 1 else 2

theorem nu1_ne (μ : Fin 3) : nu1 μ ≠ μ := by revert μ; decide

theorem nu2_ne (μ : Fin 3) : nu2 μ ≠ μ := by revert μ; decide

theorem nu1_ne_nu2 (μ : Fin 3) : nu1 μ ≠ nu2 μ := by revert μ; decide

/-- `Fin 3 = {μ, nu1 μ, nu2 μ}` — the exhaustiveness fact that lets a site be reconstructed from its
three coordinates. -/
theorem dirs_exhaust (μ ρ : Fin 3) : ρ = μ ∨ ρ = nu1 μ ∨ ρ = nu2 μ := by revert μ ρ; decide

/-- `transDirs μ = {nu1 μ, nu2 μ}` as a `Finset`. -/
theorem transDirs_eq_pair (μ : Fin 3) : transDirs μ = {nu1 μ, nu2 μ} := by
  revert μ; decide

/-- Sum over the two transverse directions, split. -/
theorem sum_transDirs (μ : Fin 3) (h : Fin 3 → ℝ) :
    ∑ ν ∈ transDirs μ, h ν = h (nu1 μ) + h (nu2 μ) := by
  rw [transDirs_eq_pair, Finset.sum_pair (nu1_ne_nu2 μ)]

/-- Commuting a single fine shift past a `coarseShift` in a different direction. -/
theorem coarseShift_shift_comm (W : PeriodicLatticeSite L) (k : ℕ) {ν ρ : Fin 3} (h : ν ≠ ρ) :
    coarseShift (periodicLatticeShift W ν) k ρ
      = periodicLatticeShift (coarseShift W k ρ) ν := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold coarseShift at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact periodicLatticeShift_comm _ h

/-- The corner site of the face `Δ'(y,μ)`: the `μ`-top layer, transverse coordinates at `y`. -/
def faceCorner (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) : PeriodicLatticeSite L :=
  coarseShift y (ell - 1) μ

/-- **Face coordinates.** `faceSite y ell μ i j` is the site of `Δ'(y,μ)` at transverse offsets
`(i, j)` in directions `(nu1 μ, nu2 μ)`. -/
def faceSite (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) (i j : ℕ) :
    PeriodicLatticeSite L :=
  coarseShift (coarseShift (faceCorner y ell μ) i (nu1 μ)) j (nu2 μ)

variable {y : PeriodicLatticeSite L} {ell : ℕ} {μ : Fin 3}

theorem faceSite_val_mu (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1) (i j : ℕ) :
    ((faceSite y ell μ i j) μ).val = (y μ).val + (ell - 1) := by
  unfold faceSite
  rw [coarseShift_apply_ne _ _ _ _ (Ne.symm (nu2_ne μ)),
    coarseShift_apply_ne _ _ _ _ (Ne.symm (nu1_ne μ))]
  unfold faceCorner
  rw [coarseShift_val_eq]
  have := hfit μ
  exact Nat.mod_eq_of_lt (by omega)

theorem faceSite_val_nu1 (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1) {i : ℕ} (hi : i < ell) (j : ℕ) :
    ((faceSite y ell μ i j) (nu1 μ)).val = (y (nu1 μ)).val + i := by
  unfold faceSite
  rw [coarseShift_apply_ne _ _ _ _ (nu1_ne_nu2 μ), coarseShift_val_eq]
  unfold faceCorner
  rw [coarseShift_apply_ne _ _ _ _ (nu1_ne μ)]
  have := hfit (nu1 μ)
  exact Nat.mod_eq_of_lt (by omega)

theorem faceSite_val_nu2 (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1) (i : ℕ) {j : ℕ} (hj : j < ell) :
    ((faceSite y ell μ i j) (nu2 μ)).val = (y (nu2 μ)).val + j := by
  unfold faceSite
  rw [coarseShift_val_eq, coarseShift_apply_ne _ _ _ _ (Ne.symm (nu1_ne_nu2 μ))]
  unfold faceCorner
  rw [coarseShift_apply_ne _ _ _ _ (nu2_ne μ)]
  have := hfit (nu2 μ)
  exact Nat.mod_eq_of_lt (by omega)

theorem faceSite_mem (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    {i j : ℕ} (hi : i < ell) (hj : j < ell) :
    faceSite y ell μ i j ∈ crossSectionTop y ell μ := by
  rw [mem_crossSectionTop, mem_blockOf]
  refine ⟨fun ρ => ?_, faceSite_val_mu hell hfit i j⟩
  rcases dirs_exhaust μ ρ with h | h | h
  · subst h; rw [faceSite_val_mu hell hfit i j]; omega
  · subst h; rw [faceSite_val_nu1 hfit hi j]; omega
  · subst h; rw [faceSite_val_nu2 hfit i hj]; omega

/-- **The face bijection.** Summation over `Δ'(y,μ)` equals the double sum over face coordinates. -/
theorem face_sum (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    (g : PeriodicLatticeSite L → ℝ) :
    ∑ x ∈ crossSectionTop y ell μ, g x
      = ∑ i ∈ range ell, ∑ j ∈ range ell, g (faceSite y ell μ i j) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (fun x _ => ((x (nu1 μ)).val - (y (nu1 μ)).val, (x (nu2 μ)).val - (y (nu2 μ)).val))
    (fun p _ => faceSite y ell μ p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_crossSectionTop, mem_blockOf] at hx
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by have := hx.1 (nu1 μ); omega, by have := hx.1 (nu2 μ); omega⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact faceSite_mem hell hfit hp.1 hp.2
  · -- left inverse
    intro x hx
    rw [mem_crossSectionTop, mem_blockOf] at hx
    have h1 : (x (nu1 μ)).val - (y (nu1 μ)).val < ell := by have := hx.1 (nu1 μ); omega
    have h2 : (x (nu2 μ)).val - (y (nu2 μ)).val < ell := by have := hx.1 (nu2 μ); omega
    show faceSite y ell μ _ _ = x
    funext ρ
    apply Fin.val_injective
    rcases dirs_exhaust μ ρ with h | h | h
    · subst h; rw [faceSite_val_mu hell hfit _ _]; omega
    · subst h; rw [faceSite_val_nu1 hfit h1 _]; have := hx.1 (nu1 μ); omega
    · subst h; rw [faceSite_val_nu2 hfit _ h2]; have := hx.1 (nu2 μ); omega
  · -- right inverse
    intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    refine Prod.ext ?_ ?_
    · show ((faceSite y ell μ p.1 p.2) (nu1 μ)).val - (y (nu1 μ)).val = p.1
      rw [faceSite_val_nu1 hfit hp.1 _]; omega
    · show ((faceSite y ell μ p.1 p.2) (nu2 μ)).val - (y (nu2 μ)).val = p.2
      rw [faceSite_val_nu2 hfit _ hp.2]; omega
  · intro x hx
    rw [mem_crossSectionTop, mem_blockOf] at hx
    have h1 : (x (nu1 μ)).val - (y (nu1 μ)).val < ell := by have := hx.1 (nu1 μ); omega
    have h2 : (x (nu2 μ)).val - (y (nu2 μ)).val < ell := by have := hx.1 (nu2 μ); omega
    show g x = g (faceSite y ell μ _ _)
    congr 1
    funext ρ
    apply Fin.val_injective
    rcases dirs_exhaust μ ρ with h | h | h
    · subst h; rw [faceSite_val_mu hell hfit _ _]; omega
    · subst h; rw [faceSite_val_nu1 hfit h1 _]; have := hx.1 (nu1 μ); omega
    · subst h; rw [faceSite_val_nu2 hfit _ h2]; have := hx.1 (nu2 μ); omega

/-- Stepping the first face coordinate is a `nu1`-shift. -/
theorem faceSite_succ_nu1 (i j : ℕ) :
    faceSite y ell μ (i + 1) j = periodicLatticeShift (faceSite y ell μ i j) (nu1 μ) := by
  unfold faceSite
  have h : coarseShift (faceCorner y ell μ) (i + 1) (nu1 μ)
      = periodicLatticeShift (coarseShift (faceCorner y ell μ) i (nu1 μ)) (nu1 μ) := by
    unfold coarseShift; rw [Function.iterate_succ_apply']
  rw [h, coarseShift_shift_comm _ _ (nu1_ne_nu2 μ)]

/-- Stepping the second face coordinate is a `nu2`-shift. -/
theorem faceSite_succ_nu2 (i j : ℕ) :
    faceSite y ell μ i (j + 1) = periodicLatticeShift (faceSite y ell μ i j) (nu2 μ) := by
  unfold faceSite coarseShift
  rw [Function.iterate_succ_apply']


/-! ## §2. The face field, and the cross-sectional Poincaré with the HONEST exponent. -/

/-- The longitudinal field `B_μ` read in face coordinates. -/
noncomputable def faceField (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    ℕ → ℕ → ℝ := fun i j => B (faceSite y ell μ i j, μ)

/-- `S = Σ_{x∈Δ'} B_μ(x)`, the unnormalised face sum. -/
noncomputable def faceSumLong (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    ℝ := ∑ x ∈ crossSectionTop y ell μ, B (x, μ)

theorem faceField_sumSq2 (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    (B : Bond L → ℝ) :
    sumSq2 ell (faceField B y ell μ) = topFaceEnergy B y ell μ := by
  unfold sumSq2 topFaceEnergy faceField
  exact (face_sum hell hfit (fun x => (B (x, μ)) ^ 2)).symm

theorem faceField_sum2 (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    (B : Bond L → ℝ) :
    sum2 ell (faceField B y ell μ) = faceSumLong B y ell μ := by
  unfold sum2 faceSumLong faceField
  exact (face_sum hell hfit (fun x => B (x, μ))).symm

/-- **The cross-sectional Poincaré with the exponent the Neumann gap ACTUALLY supports.**
`T ≤ ell²·G + S²/ell²`, `G` the interior (Neumann) transverse gradient energy of the face.
Equivalently `ell^{-4}·T ≤ ell^{-2}·G + ell^{-6}·S²`, i.e. the parenthesised quantity of CMP96
(2.126) is `≥ L^{-d-2}·T` — NOT the printed `L^{-d-1}·T` (see the module docstring). -/
theorem face_poincare (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1) (B : Bond L → ℝ) :
    topFaceEnergy B y ell μ
      ≤ (ell : ℝ) ^ 2 * gradEnergy2 ell (faceField B y ell μ)
        + (faceSumLong B y ell μ) ^ 2 / (ell : ℝ) ^ 2 := by
  set F := faceField B y ell μ with hF
  have hnR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hsplit := sumSq2_split ell hell F
  have hvar := var2_le_nsq ell F
  have hmean : (ell : ℝ) ^ 2 * (blockMean ell F) ^ 2
      = (faceSumLong B y ell μ) ^ 2 / (ell : ℝ) ^ 2 := by
    rw [blockMean, faceField_sum2 hell hfit B]
    field_simp
  rw [← faceField_sumSq2 hell hfit B, hsplit, ← hmean]
  linarith [hvar]

/-! ## §3. The face form of CMP96 (2.124): the interior transverse gradient energy is controlled by
the region curl energy plus the two blocks' own in-block bond energies. -/

/-- Injectivity of the face-coordinate map on the `ell × ell` grid. -/
theorem faceSite_injOn (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1) :
    Set.InjOn (fun p : ℕ × ℕ => faceSite y ell μ p.1 p.2)
      ((range ell ×ˢ range ell : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  intro p hp q hq hpq
  rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp hq
  have h1 : ((faceSite y ell μ p.1 p.2) (nu1 μ)).val
      = ((faceSite y ell μ q.1 q.2) (nu1 μ)).val := by rw [show
        faceSite y ell μ p.1 p.2 = faceSite y ell μ q.1 q.2 from hpq]
  have h2 : ((faceSite y ell μ p.1 p.2) (nu2 μ)).val
      = ((faceSite y ell μ q.1 q.2) (nu2 μ)).val := by rw [show
        faceSite y ell μ p.1 p.2 = faceSite y ell μ q.1 q.2 from hpq]
  rw [faceSite_val_nu1 hfit hp.1 _, faceSite_val_nu1 hfit hq.1 _] at h1
  rw [faceSite_val_nu2 hfit _ hp.2, faceSite_val_nu2 hfit _ hq.2] at h2
  exact Prod.ext (by omega) (by omega)

/-- Generic "sum over a grid of squares injecting into a bond set" bound. -/
theorem grid_sq_le {ι : Type*} [DecidableEq ι] (s : Finset (ℕ × ℕ)) (Φ : ℕ → ℕ → ι)
    (S : Finset ι) (f : ι → ℝ)
    (hinj : Set.InjOn (fun p : ℕ × ℕ => Φ p.1 p.2) (s : Set (ℕ × ℕ)))
    (hsub : ∀ p ∈ s, Φ p.1 p.2 ∈ S) :
    ∑ p ∈ s, (f (Φ p.1 p.2)) ^ 2 ≤ ∑ b ∈ S, (f b) ^ 2 := by
  rw [← Finset.sum_image (f := fun b => (f b) ^ 2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
  intro b hb
  rw [Finset.mem_image] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  exact hsub p hp

/-- The `μ`-shift of a face site lands on the base `μ`-layer of the NEXT block. -/
theorem faceShift_val_mu (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1) (i j : ℕ) :
    ((periodicLatticeShift (faceSite y ell μ i j) μ) μ).val
      = ((coarseShift y ell μ) μ).val := by
  have h1 : periodicLatticeShift (faceSite y ell μ i j) μ = coarseShift (faceSite y ell μ i j) 1 μ := by
    unfold coarseShift; rw [Function.iterate_one]
  rw [h1, coarseShift_val_eq, faceSite_val_mu hell hfit i j, coarseShift_val_eq]
  congr 1
  omega

theorem coarseShift_val_ne (ρ : Fin 3) (h : ρ ≠ μ) : (coarseShift y ell μ) ρ = y ρ :=
  coarseShift_apply_ne y ell μ ρ h

/-- `(faceSite, ν₁)` is a bond of `B(y)` when the first face coordinate can still step. -/
theorem faceBond_nu1_mem (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    {i j : ℕ} (hi : i + 1 < ell) (hj : j < ell) :
    (faceSite y ell μ i j, nu1 μ) ∈ bondsInBlock y ell := by
  rw [mem_bondsInBlock]
  refine ⟨(mem_crossSectionTop.mp (faceSite_mem hell hfit (by omega) hj)).1, ?_⟩
  rw [show (periodicLatticeShift (faceSite y ell μ i j) (nu1 μ))
      = faceSite y ell μ (i + 1) j from (faceSite_succ_nu1 i j).symm]
  exact (mem_crossSectionTop.mp (faceSite_mem hell hfit hi hj)).1

theorem faceBond_nu2_mem (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    {i j : ℕ} (hi : i < ell) (hj : j + 1 < ell) :
    (faceSite y ell μ i j, nu2 μ) ∈ bondsInBlock y ell := by
  rw [mem_bondsInBlock]
  refine ⟨(mem_crossSectionTop.mp (faceSite_mem hell hfit hi (by omega))).1, ?_⟩
  rw [show (periodicLatticeShift (faceSite y ell μ i j) (nu2 μ))
      = faceSite y ell μ i (j + 1) from (faceSite_succ_nu2 i j).symm]
  exact (mem_crossSectionTop.mp (faceSite_mem hell hfit hi hj)).1

/-- The `μ`-shifted face site lies in the next block. -/
theorem faceShift_mem_next (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    {i j : ℕ} (hi : i < ell) (hj : j < ell) :
    periodicLatticeShift (faceSite y ell μ i j) μ ∈ blockOf (coarseShift y ell μ) ell := by
  rw [mem_blockOf]
  intro ρ
  rcases dirs_exhaust μ ρ with h | h | h
  · subst h
    rw [faceShift_val_mu hell hfit i j]; omega
  · subst h
    rw [show (periodicLatticeShift (faceSite y ell μ i j) μ) (nu1 μ)
        = (faceSite y ell μ i j) (nu1 μ) from Function.update_of_ne (nu1_ne μ) _ _,
      coarseShift_val_ne (nu1 μ) (nu1_ne μ), faceSite_val_nu1 hfit hi j]
    omega
  · subst h
    rw [show (periodicLatticeShift (faceSite y ell μ i j) μ) (nu2 μ)
        = (faceSite y ell μ i j) (nu2 μ) from Function.update_of_ne (nu2_ne μ) _ _,
      coarseShift_val_ne (nu2 μ) (nu2_ne μ), faceSite_val_nu2 hfit i hj]
    omega

theorem faceShiftBond_nu1_mem (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    {i j : ℕ} (hi : i + 1 < ell) (hj : j < ell) :
    (periodicLatticeShift (faceSite y ell μ i j) μ, nu1 μ)
      ∈ bondsInBlock (coarseShift y ell μ) ell := by
  rw [mem_bondsInBlock]
  refine ⟨faceShift_mem_next hell hfit (by omega) hj, ?_⟩
  rw [show periodicLatticeShift (periodicLatticeShift (faceSite y ell μ i j) μ) (nu1 μ)
      = periodicLatticeShift (faceSite y ell μ (i + 1) j) μ by
        rw [faceSite_succ_nu1 i j]
        exact periodicLatticeShift_comm _ (Ne.symm (nu1_ne μ))]
  exact faceShift_mem_next hell hfit hi hj

theorem faceShiftBond_nu2_mem (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    {i j : ℕ} (hi : i < ell) (hj : j + 1 < ell) :
    (periodicLatticeShift (faceSite y ell μ i j) μ, nu2 μ)
      ∈ bondsInBlock (coarseShift y ell μ) ell := by
  rw [mem_bondsInBlock]
  refine ⟨faceShift_mem_next hell hfit hi (by omega), ?_⟩
  rw [show periodicLatticeShift (periodicLatticeShift (faceSite y ell μ i j) μ) (nu2 μ)
      = periodicLatticeShift (faceSite y ell μ i (j + 1)) μ by
        rw [faceSite_succ_nu2 i j]
        exact periodicLatticeShift_comm _ (Ne.symm (nu2_ne μ))]
  exact faceShift_mem_next hell hfit hi hj


/-- `regionCurlEnergy` split into its two transverse-direction pieces. -/
theorem regionCurl_split (B : Bond L → ℝ) :
    regionCurlEnergy B y ell μ
      = (∑ x ∈ crossSectionTop y ell μ, (xsecCurl B x μ (nu1 μ)) ^ 2)
        + ∑ x ∈ crossSectionTop y ell μ, (xsecCurl B x μ (nu2 μ)) ^ 2 := by
  unfold regionCurlEnergy
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => sum_transDirs μ (fun ν => (xsecCurl B x μ ν) ^ 2))

theorem prod_sub (hell : 0 < ell) :
    (range (ell - 1) ×ˢ range ell : Finset (ℕ × ℕ)) ⊆ range ell ×ˢ range ell := by
  intro p hp
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

theorem prod_sub' (hell : 0 < ell) :
    (range ell ×ˢ range (ell - 1) : Finset (ℕ × ℕ)) ⊆ range ell ×ˢ range ell := by
  intro p hp
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp ⊢
  exact ⟨hp.1, by omega⟩

/-- A grid sum over `Δ'`-indexed nonnegative terms, restricted to a sub-grid, is at most the
`Δ'`-sum. -/
theorem subgrid_le (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    (s : Finset (ℕ × ℕ)) (hs : s ⊆ range ell ×ˢ range ell) (g : PeriodicLatticeSite L → ℝ) :
    ∑ p ∈ s, (g (faceSite y ell μ p.1 p.2)) ^ 2
      ≤ ∑ x ∈ crossSectionTop y ell μ, (g x) ^ 2 := by
  rw [face_sum hell hfit (fun x => (g x) ^ 2), ← Finset.sum_product']
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)

/-- **CMP96 (2.124) in face coordinates.** The interior (Neumann) transverse gradient energy of
`B_μ` on `Δ'` is controlled by the region curl energy plus the two blocks' own in-block bond
energies.  Only bonds with BOTH endpoints in `Δ'` (resp. `Δ''`) are used, which is what keeps the
correction inside `bondsInBlock` — the source's own `Σ_{b⊂Δ'}`, `Σ_{b⊂Δ''}`. -/
theorem face_2124 (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1) (B : Bond L → ℝ) :
    gradEnergy2 ell (faceField B y ell μ)
      ≤ 3 * regionCurlEnergy B y ell μ + 6 * boundaryCorr B y ell μ := by
  set F := faceField B y ell μ with hF
  set sV : Finset (ℕ × ℕ) := range (ell - 1) ×ˢ range ell with hsV
  set sH : Finset (ℕ × ℕ) := range ell ×ˢ range (ell - 1) with hsH
  -- rewrite the two energies as product sums
  have hver : verEnergy ell F = ∑ p ∈ sV, (F (p.1 + 1) p.2 - F p.1 p.2) ^ 2 := by
    rw [hsV, Finset.sum_product]
    unfold verEnergy dirichletEnergy
    exact Finset.sum_comm
  have hhor : horEnergy ell F = ∑ p ∈ sH, (F p.1 (p.2 + 1) - F p.1 p.2) ^ 2 := by
    rw [hsH, Finset.sum_product]
    unfold horEnergy dirichletEnergy
    rfl
  -- pointwise bounds
  have hptV : ∀ p ∈ sV, (F (p.1 + 1) p.2 - F p.1 p.2) ^ 2
      ≤ 3 * ((xsecCurl B (faceSite y ell μ p.1 p.2) μ (nu1 μ)) ^ 2
          + (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, nu1 μ)) ^ 2
          + (B (faceSite y ell μ p.1 p.2, nu1 μ)) ^ 2) := by
    intro p _
    have hstep : F (p.1 + 1) p.2 = B (periodicLatticeShift (faceSite y ell μ p.1 p.2) (nu1 μ), μ) := by
      rw [hF]; unfold faceField; rw [faceSite_succ_nu1 p.1 p.2]
    have h := pointwise_2124 (B (faceSite y ell μ p.1 p.2, μ))
      (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, nu1 μ))
      (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) (nu1 μ), μ))
      (B (faceSite y ell μ p.1 p.2, nu1 μ))
    unfold xsecCurl
    rw [hstep]
    have hFp : F p.1 p.2 = B (faceSite y ell μ p.1 p.2, μ) := rfl
    rw [hFp]
    linarith [h]
  have hptH : ∀ p ∈ sH, (F p.1 (p.2 + 1) - F p.1 p.2) ^ 2
      ≤ 3 * ((xsecCurl B (faceSite y ell μ p.1 p.2) μ (nu2 μ)) ^ 2
          + (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, nu2 μ)) ^ 2
          + (B (faceSite y ell μ p.1 p.2, nu2 μ)) ^ 2) := by
    intro p _
    have hstep : F p.1 (p.2 + 1) = B (periodicLatticeShift (faceSite y ell μ p.1 p.2) (nu2 μ), μ) := by
      rw [hF]; unfold faceField; rw [faceSite_succ_nu2 p.1 p.2]
    have h := pointwise_2124 (B (faceSite y ell μ p.1 p.2, μ))
      (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, nu2 μ))
      (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) (nu2 μ), μ))
      (B (faceSite y ell μ p.1 p.2, nu2 μ))
    unfold xsecCurl
    rw [hstep]
    have hFp : F p.1 p.2 = B (faceSite y ell μ p.1 p.2, μ) := rfl
    rw [hFp]
    linarith [h]
  -- injectivity data
  have hinjV : Set.InjOn (fun p : ℕ × ℕ => faceSite y ell μ p.1 p.2) (sV : Set (ℕ × ℕ)) :=
    (faceSite_injOn hfit).mono (Finset.coe_subset.mpr (prod_sub hell))
  have hinjH : Set.InjOn (fun p : ℕ × ℕ => faceSite y ell μ p.1 p.2) (sH : Set (ℕ × ℕ)) :=
    (faceSite_injOn hfit).mono (Finset.coe_subset.mpr (prod_sub' hell))
  have hshiftinj : ∀ (t : Finset (ℕ × ℕ)) (ν : Fin 3),
      Set.InjOn (fun p : ℕ × ℕ => faceSite y ell μ p.1 p.2) (t : Set (ℕ × ℕ)) →
      Set.InjOn (fun p : ℕ × ℕ =>
        ((periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, ν) : Bond L)) (t : Set (ℕ × ℕ)) := by
    intro t ν hinj p hp q hq hpq
    have h1 : periodicLatticeShift (faceSite y ell μ p.1 p.2) μ
        = periodicLatticeShift (faceSite y ell μ q.1 q.2) μ := congrArg Prod.fst hpq
    exact hinj hp hq (GeomScratch.periodicLatticeShift_injective μ h1)
  have hbondinj : ∀ (t : Finset (ℕ × ℕ)) (ν : Fin 3),
      Set.InjOn (fun p : ℕ × ℕ => faceSite y ell μ p.1 p.2) (t : Set (ℕ × ℕ)) →
      Set.InjOn (fun p : ℕ × ℕ => ((faceSite y ell μ p.1 p.2, ν) : Bond L))
        (t : Set (ℕ × ℕ)) := by
    intro t ν hinj p hp q hq hpq
    exact hinj hp hq (congrArg Prod.fst hpq)
  -- the four in-block correction sums
  have hAV : ∑ p ∈ sV, (B (faceSite y ell μ p.1 p.2, nu1 μ)) ^ 2
      ≤ blockBondEnergy B y ell := by
    refine grid_sq_le sV (fun i j => ((faceSite y ell μ i j, nu1 μ) : Bond L))
      (bondsInBlock y ell) B (hbondinj sV (nu1 μ) hinjV) ?_
    intro p hp
    rw [hsV, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact faceBond_nu1_mem hell hfit (by omega) hp.2
  have hBV : ∑ p ∈ sV, (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, nu1 μ)) ^ 2
      ≤ blockBondEnergy B (coarseShift y ell μ) ell := by
    refine grid_sq_le sV
      (fun i j => ((periodicLatticeShift (faceSite y ell μ i j) μ, nu1 μ) : Bond L))
      (bondsInBlock (coarseShift y ell μ) ell) B (hshiftinj sV (nu1 μ) hinjV) ?_
    intro p hp
    rw [hsV, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact faceShiftBond_nu1_mem hell hfit (by omega) hp.2
  have hAH : ∑ p ∈ sH, (B (faceSite y ell μ p.1 p.2, nu2 μ)) ^ 2
      ≤ blockBondEnergy B y ell := by
    refine grid_sq_le sH (fun i j => ((faceSite y ell μ i j, nu2 μ) : Bond L))
      (bondsInBlock y ell) B (hbondinj sH (nu2 μ) hinjH) ?_
    intro p hp
    rw [hsH, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact faceBond_nu2_mem hell hfit hp.1 (by omega)
  have hBH : ∑ p ∈ sH, (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, nu2 μ)) ^ 2
      ≤ blockBondEnergy B (coarseShift y ell μ) ell := by
    refine grid_sq_le sH
      (fun i j => ((periodicLatticeShift (faceSite y ell μ i j) μ, nu2 μ) : Bond L))
      (bondsInBlock (coarseShift y ell μ) ell) B (hshiftinj sH (nu2 μ) hinjH) ?_
    intro p hp
    rw [hsH, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact faceShiftBond_nu2_mem hell hfit hp.1 (by omega)
  -- the two curl sums
  have hCV : ∑ p ∈ sV, (xsecCurl B (faceSite y ell μ p.1 p.2) μ (nu1 μ)) ^ 2
      ≤ ∑ x ∈ crossSectionTop y ell μ, (xsecCurl B x μ (nu1 μ)) ^ 2 :=
    subgrid_le hell hfit sV (prod_sub hell) (fun x => xsecCurl B x μ (nu1 μ))
  have hCH : ∑ p ∈ sH, (xsecCurl B (faceSite y ell μ p.1 p.2) μ (nu2 μ)) ^ 2
      ≤ ∑ x ∈ crossSectionTop y ell μ, (xsecCurl B x μ (nu2 μ)) ^ 2 :=
    subgrid_le hell hfit sH (prod_sub' hell) (fun x => xsecCurl B x μ (nu2 μ))
  -- assemble
  have hVsum : verEnergy ell F
      ≤ 3 * ((∑ p ∈ sV, (xsecCurl B (faceSite y ell μ p.1 p.2) μ (nu1 μ)) ^ 2)
        + (∑ p ∈ sV, (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, nu1 μ)) ^ 2)
        + ∑ p ∈ sV, (B (faceSite y ell μ p.1 p.2, nu1 μ)) ^ 2) := by
    rw [hver]
    calc ∑ p ∈ sV, (F (p.1 + 1) p.2 - F p.1 p.2) ^ 2
        ≤ ∑ p ∈ sV, 3 * ((xsecCurl B (faceSite y ell μ p.1 p.2) μ (nu1 μ)) ^ 2
            + (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, nu1 μ)) ^ 2
            + (B (faceSite y ell μ p.1 p.2, nu1 μ)) ^ 2) := Finset.sum_le_sum hptV
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hHsum : horEnergy ell F
      ≤ 3 * ((∑ p ∈ sH, (xsecCurl B (faceSite y ell μ p.1 p.2) μ (nu2 μ)) ^ 2)
        + (∑ p ∈ sH, (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, nu2 μ)) ^ 2)
        + ∑ p ∈ sH, (B (faceSite y ell μ p.1 p.2, nu2 μ)) ^ 2) := by
    rw [hhor]
    calc ∑ p ∈ sH, (F p.1 (p.2 + 1) - F p.1 p.2) ^ 2
        ≤ ∑ p ∈ sH, 3 * ((xsecCurl B (faceSite y ell μ p.1 p.2) μ (nu2 μ)) ^ 2
            + (B (periodicLatticeShift (faceSite y ell μ p.1 p.2) μ, nu2 μ)) ^ 2
            + (B (faceSite y ell μ p.1 p.2, nu2 μ)) ^ 2) := Finset.sum_le_sum hptH
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [gradEnergy2, regionCurl_split B, boundaryCorr]
  linarith [hVsum, hHsum, hAV, hBV, hAH, hBH, hCV, hCH]


/-! ## §4a. Full 3-D block coordinates (the face coordinates extended along `μ`). -/

/-- Block coordinates: `μ`-offset `k`, transverse offsets `(i,j)`.  `k` is NOT restricted to
`< ell`: `k ∈ [ell, 2ell−2]` addresses the NEXT block along `μ`. -/
def blkSite (y : PeriodicLatticeSite L) (μ : Fin 3) (i j k : ℕ) : PeriodicLatticeSite L :=
  coarseShift (coarseShift (coarseShift y k μ) i (nu1 μ)) j (nu2 μ)

theorem faceSite_eq_blkSite (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) (i j : ℕ) :
    faceSite y ell μ i j = blkSite y μ i j (ell - 1) := rfl

theorem coarseShift_add (W : PeriodicLatticeSite L) (a b : ℕ) (ν : Fin 3) :
    coarseShift (coarseShift W a ν) b ν = coarseShift W (a + b) ν := by
  unfold coarseShift
  rw [← Function.iterate_add_apply, Nat.add_comm]

theorem coarseShift_comm (W : PeriodicLatticeSite L) (a b : ℕ) {ν ρ : Fin 3} (h : ν ≠ ρ) :
    coarseShift (coarseShift W a ν) b ρ = coarseShift (coarseShift W b ρ) a ν := by
  induction a with
  | zero => rfl
  | succ n ih =>
    have h1 : coarseShift W (n + 1) ν = periodicLatticeShift (coarseShift W n ν) ν := by
      unfold coarseShift; rw [Function.iterate_succ_apply']
    have h2 : coarseShift (coarseShift W b ρ) (n + 1) ν
        = periodicLatticeShift (coarseShift (coarseShift W b ρ) n ν) ν := by
      unfold coarseShift; rw [Function.iterate_succ_apply']
    rw [h1, h2, coarseShift_shift_comm _ _ h, ih]

theorem blkSite_shift_mu (y : PeriodicLatticeSite L) (μ : Fin 3) (i j k m : ℕ) :
    coarseShift (blkSite y μ i j k) m μ = blkSite y μ i j (k + m) := by
  unfold blkSite
  rw [coarseShift_comm _ _ _ (nu2_ne μ), coarseShift_comm _ _ _ (nu1_ne μ), coarseShift_add]

/-- Re-basing a `μ`-offset `≥ ell` onto the next block. -/
theorem blkSite_next (y : PeriodicLatticeSite L) (μ : Fin 3) (ell i j t : ℕ) :
    blkSite y μ i j (ell + t) = blkSite (coarseShift y ell μ) μ i j t := by
  unfold blkSite
  rw [coarseShift_add]

variable {z : PeriodicLatticeSite L}

theorem blkSite_val_nu1 (hfit : ∀ ν, (z ν).val + ell ≤ L ν + 1) {i : ℕ} (hi : i < ell) (j k : ℕ) :
    ((blkSite z μ i j k) (nu1 μ)).val = (z (nu1 μ)).val + i := by
  unfold blkSite
  rw [coarseShift_apply_ne _ _ _ _ (nu1_ne_nu2 μ), coarseShift_val_eq,
    coarseShift_apply_ne _ _ _ _ (nu1_ne μ)]
  have := hfit (nu1 μ)
  exact Nat.mod_eq_of_lt (by omega)

theorem blkSite_val_nu2 (hfit : ∀ ν, (z ν).val + ell ≤ L ν + 1) (i : ℕ) {j : ℕ} (hj : j < ell)
    (k : ℕ) : ((blkSite z μ i j k) (nu2 μ)).val = (z (nu2 μ)).val + j := by
  unfold blkSite
  rw [coarseShift_val_eq, coarseShift_apply_ne _ _ _ _ (Ne.symm (nu1_ne_nu2 μ)),
    coarseShift_apply_ne _ _ _ _ (nu2_ne μ)]
  have := hfit (nu2 μ)
  exact Nat.mod_eq_of_lt (by omega)

theorem blkSite_val_mu (hfit : ∀ ν, (z ν).val + ell ≤ L ν + 1) (i j : ℕ) {k : ℕ} (hk : k < ell) :
    ((blkSite z μ i j k) μ).val = (z μ).val + k := by
  unfold blkSite
  rw [coarseShift_apply_ne _ _ _ _ (Ne.symm (nu2_ne μ)),
    coarseShift_apply_ne _ _ _ _ (Ne.symm (nu1_ne μ)), coarseShift_val_eq]
  have := hfit μ
  exact Nat.mod_eq_of_lt (by omega)

theorem blkSite_mem (hfit : ∀ ν, (z ν).val + ell ≤ L ν + 1)
    {i j k : ℕ} (hi : i < ell) (hj : j < ell) (hk : k < ell) :
    blkSite z μ i j k ∈ blockOf z ell := by
  rw [mem_blockOf]
  intro ρ
  rcases dirs_exhaust μ ρ with h | h | h
  · subst h; rw [blkSite_val_mu hfit i j hk]; omega
  · subst h; rw [blkSite_val_nu1 hfit hi j k]; omega
  · subst h; rw [blkSite_val_nu2 hfit i hj k]; omega

/-- The longitudinal bond `(blkSite z μ i j r, μ)` lies inside `B(z)` when `r + 1 < ell`. -/
theorem longBond_mem (hfit : ∀ ν, (z ν).val + ell ≤ L ν + 1)
    {i j r : ℕ} (hi : i < ell) (hj : j < ell) (hr : r + 1 < ell) :
    (blkSite z μ i j r, μ) ∈ bondsInBlock z ell := by
  rw [mem_bondsInBlock]
  refine ⟨blkSite_mem hfit hi hj (by omega), ?_⟩
  have hstep : periodicLatticeShift (blkSite z μ i j r) μ = blkSite z μ i j (r + 1) := by
    have h1 : periodicLatticeShift (blkSite z μ i j r) μ
        = coarseShift (blkSite z μ i j r) 1 μ := by
      unfold coarseShift; rw [Function.iterate_one]
    rw [h1, blkSite_shift_mu]
  rw [hstep]
  exact blkSite_mem hfit hi hj hr

/-- Injectivity of the full 3-D block coordinate map. -/
theorem blkSite_injOn3 (hfit : ∀ ν, (z ν).val + ell ≤ L ν + 1) :
    Set.InjOn (fun q : (ℕ × ℕ) × ℕ => blkSite z μ q.1.1 q.1.2 q.2)
      ((((range ell ×ˢ range ell) ×ˢ range ell : Finset ((ℕ × ℕ) × ℕ))) : Set ((ℕ × ℕ) × ℕ)) := by
  intro p hp q hq hpq
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp hq
  have heq : blkSite z μ p.1.1 p.1.2 p.2 = blkSite z μ q.1.1 q.1.2 q.2 := hpq
  have h1 : ((blkSite z μ p.1.1 p.1.2 p.2) (nu1 μ)).val
      = ((blkSite z μ q.1.1 q.1.2 q.2) (nu1 μ)).val := by rw [heq]
  have h2 : ((blkSite z μ p.1.1 p.1.2 p.2) (nu2 μ)).val
      = ((blkSite z μ q.1.1 q.1.2 q.2) (nu2 μ)).val := by rw [heq]
  have h3 : ((blkSite z μ p.1.1 p.1.2 p.2) μ).val
      = ((blkSite z μ q.1.1 q.1.2 q.2) μ).val := by rw [heq]
  rw [blkSite_val_nu1 hfit hp.1.1 _ _, blkSite_val_nu1 hfit hq.1.1 _ _] at h1
  rw [blkSite_val_nu2 hfit _ hp.1.2 _, blkSite_val_nu2 hfit _ hq.1.2 _] at h2
  rw [blkSite_val_mu hfit _ _ hp.2, blkSite_val_mu hfit _ _ hq.2] at h3
  exact Prod.ext (Prod.ext (by omega) (by omega)) (by omega)

/-- Generic injective-image square-sum bound. -/
theorem inj_sq_le {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (Φ : ι → κ) (S : Finset κ)
    (f : κ → ℝ) (hinj : Set.InjOn Φ (s : Set ι)) (hsub : ∀ a ∈ s, Φ a ∈ S) :
    ∑ a ∈ s, (f (Φ a)) ^ 2 ≤ ∑ b ∈ S, (f b) ^ 2 := by
  rw [← Finset.sum_image (f := fun b => (f b) ^ 2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
  intro b hb
  rw [Finset.mem_image] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact hsub a ha

/-- **The longitudinal in-block energy bound.** All `μ`-bonds at `μ`-offsets `< ell − 1` inside
`B(z)`, summed over the transverse grid, are at most `blockBondEnergy`. -/
theorem long_sum_le (hell : 0 < ell) (hfit : ∀ ν, (z ν).val + ell ≤ L ν + 1) (B : Bond L → ℝ) :
    ∑ q ∈ (range ell ×ˢ range ell) ×ˢ range (ell - 1),
        (B (blkSite z μ q.1.1 q.1.2 q.2, μ)) ^ 2
      ≤ blockBondEnergy B z ell := by
  have hsubset : ((range ell ×ˢ range ell) ×ˢ range (ell - 1) : Finset ((ℕ × ℕ) × ℕ))
      ⊆ (range ell ×ˢ range ell) ×ˢ range ell := by
    intro q hq
    simp only [Finset.mem_product, Finset.mem_range] at hq ⊢
    exact ⟨hq.1, by omega⟩
  refine inj_sq_le _ (fun q : (ℕ × ℕ) × ℕ => ((blkSite z μ q.1.1 q.1.2 q.2, μ) : Bond L))
    (bondsInBlock z ell) B ?_ ?_
  · intro p hp q hq hpq
    exact (blkSite_injOn3 hfit) (Finset.mem_coe.mpr (hsubset (Finset.mem_coe.mp hp)))
      (Finset.mem_coe.mpr (hsubset (Finset.mem_coe.mp hq))) (congrArg Prod.fst hpq)
  · intro q hq
    simp only [Finset.mem_product, Finset.mem_range] at hq
    exact longBond_mem hfit hq.1.1 hq.1.2 (by omega)


/-! ## §4b. The block sum, and CMP96 (2.125): `Q(c)` versus the face mean. -/

theorem blkSite_base_mem (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    {i j : ℕ} (hi : i < ell) (hj : j < ell) :
    blkSite y μ i j 0 ∈ crossSectionBase y ell μ := by
  rw [crossSectionBase, Finset.mem_filter]
  refine ⟨blkSite_mem hfit hi hj hell, ?_⟩
  rw [blkSite_val_mu hfit i j hell]
  omega

/-- The base-layer analogue of `face_sum`. -/
theorem base_sum (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    (g : PeriodicLatticeSite L → ℝ) :
    ∑ x ∈ crossSectionBase y ell μ, g x
      = ∑ i ∈ range ell, ∑ j ∈ range ell, g (blkSite y μ i j 0) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (fun x _ => ((x (nu1 μ)).val - (y (nu1 μ)).val, (x (nu2 μ)).val - (y (nu2 μ)).val))
    (fun p _ => blkSite y μ p.1 p.2 0)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [crossSectionBase, Finset.mem_filter, mem_blockOf] at hx
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by have := hx.1 (nu1 μ); omega, by have := hx.1 (nu2 μ); omega⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact blkSite_base_mem hell hfit hp.1 hp.2
  · intro x hx
    rw [crossSectionBase, Finset.mem_filter, mem_blockOf] at hx
    have h1 : (x (nu1 μ)).val - (y (nu1 μ)).val < ell := by have := hx.1 (nu1 μ); omega
    have h2 : (x (nu2 μ)).val - (y (nu2 μ)).val < ell := by have := hx.1 (nu2 μ); omega
    show blkSite y μ _ _ 0 = x
    funext ρ
    apply Fin.val_injective
    rcases dirs_exhaust μ ρ with h | h | h
    · subst h; rw [blkSite_val_mu hfit _ _ hell]; omega
    · subst h; rw [blkSite_val_nu1 hfit h1 _ _]; have := hx.1 (nu1 μ); omega
    · subst h; rw [blkSite_val_nu2 hfit _ h2 _]; have := hx.1 (nu2 μ); omega
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    refine Prod.ext ?_ ?_
    · show ((blkSite y μ p.1 p.2 0) (nu1 μ)).val - (y (nu1 μ)).val = p.1
      rw [blkSite_val_nu1 hfit hp.1 _ _]; omega
    · show ((blkSite y μ p.1 p.2 0) (nu2 μ)).val - (y (nu2 μ)).val = p.2
      rw [blkSite_val_nu2 hfit _ hp.2 _]; omega
  · intro x hx
    rw [crossSectionBase, Finset.mem_filter, mem_blockOf] at hx
    have h1 : (x (nu1 μ)).val - (y (nu1 μ)).val < ell := by have := hx.1 (nu1 μ); omega
    have h2 : (x (nu2 μ)).val - (y (nu2 μ)).val < ell := by have := hx.1 (nu2 μ); omega
    show g x = g (blkSite y μ _ _ 0)
    congr 1
    funext ρ
    apply Fin.val_injective
    rcases dirs_exhaust μ ρ with h | h | h
    · subst h; rw [blkSite_val_mu hfit _ _ hell]; omega
    · subst h; rw [blkSite_val_nu1 hfit h1 _ _]; have := hx.1 (nu1 μ); omega
    · subst h; rw [blkSite_val_nu2 hfit _ h2 _]; have := hx.1 (nu2 μ); omega

/-- The full 3-D block sum in block coordinates. -/
theorem block_sum3 (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    (g : PeriodicLatticeSite L → ℝ) :
    ∑ x ∈ blockOf y ell, g x
      = ∑ i ∈ range ell, ∑ j ∈ range ell, ∑ k ∈ range ell, g (blkSite y μ i j k) := by
  rw [block_fiber_sum y ell μ hfit g,
    base_sum hell hfit (fun x0 => ∑ k ∈ range ell, g (coarseShift x0 k μ))]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun k _ => ?_)))
  rw [blkSite_shift_mu, Nat.zero_add]

/-- The `(k,m)` diagonal `k+m = ell−1` — the "ridge" of the Abel tent. -/
def diagIdx (ell : ℕ) : Finset (ℕ × ℕ) :=
  (range ell ×ˢ range ell).filter (fun q => q.1 + q.2 = ell - 1)

/-- The off-ridge `(k,m)` pairs. -/
def offIdx (ell : ℕ) : Finset (ℕ × ℕ) :=
  (range ell ×ˢ range ell).filter (fun q => ¬ (q.1 + q.2 = ell - 1))

theorem diagIdx_card (hell : 0 < ell) : (diagIdx ell).card = ell := by
  have heq : diagIdx ell = (range ell).image (fun i => (i, ell - 1 - i)) := by
    ext q
    simp only [diagIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_image, Prod.ext_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨q.1, h1, rfl, by omega⟩
    · rintro ⟨i, hi, h1, h2⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [heq, Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.mp hab).1),
    Finset.card_range]

theorem offIdx_card_le (ell : ℕ) : ((offIdx ell).card : ℝ) ≤ (ell : ℝ) ^ 2 := by
  have h : (offIdx ell).card ≤ (range ell ×ˢ range ell : Finset (ℕ × ℕ)).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_product, Finset.card_range] at h
  calc ((offIdx ell).card : ℝ) ≤ ((ell * ell : ℕ) : ℝ) := by exact_mod_cast h
    _ = (ell : ℝ) ^ 2 := by push_cast; ring

/-- The off-ridge `μ`-offsets: `{0,…,2ell−2} \ {ell−1}`. -/
def offR (ell : ℕ) : Finset ℕ := (range (2 * ell - 1)).erase (ell - 1)

theorem offR_split (hell : 0 < ell) :
    offR ell = range (ell - 1) ∪ Finset.Ico ell (2 * ell - 1) := by
  ext r
  simp only [offR, Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
  omega

theorem offR_disj (hell : 0 < ell) :
    Disjoint (range (ell - 1)) (Finset.Ico ell (2 * ell - 1)) := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  rw [Finset.mem_range] at hr
  rw [Finset.mem_Ico] at hr'
  omega

/-- For a fixed `k < ell`, the off-ridge `m`-slice injects into `offR ell`. -/
theorem shift_slice_le (hell : 0 < ell) {k : ℕ} (hk : k < ell) (h : ℕ → ℝ)
    (hnn : ∀ r, 0 ≤ h r) :
    ∑ m ∈ (range ell).filter (fun m => ¬ (k + m = ell - 1)), h (k + m)
      ≤ ∑ r ∈ offR ell, h r := by
  have hinj : Set.InjOn (fun m => k + m)
      (((range ell).filter (fun m => ¬ (k + m = ell - 1)) : Finset ℕ) : Set ℕ) := by
    intro a _ b _ hab
    have hab' : k + a = k + b := hab
    omega
  rw [← Finset.sum_image (f := h) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hnn _)
  intro r hr
  rw [Finset.mem_image] at hr
  obtain ⟨m, hm, rfl⟩ := hr
  rw [Finset.mem_filter, Finset.mem_range] at hm
  simp only [offR, Finset.mem_erase, Finset.mem_range]
  exact ⟨hm.2, by omega⟩


/-- The off-ridge part of `Q(c)` (CMP96 (2.125)'s two non-`Δ'` groups, merged). -/
noncomputable def offSum (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) : ℝ :=
  ∑ q ∈ (range ell ×ˢ range ell) ×ˢ offIdx ell,
    B (blkSite y μ q.1.1 q.1.2 (q.2.1 + q.2.2), μ)

/-- **CMP96 (2.125), the exact resummation.** `Q₁B(c) = ell^{-3}·S + ell^{-4}·(off-ridge part)`,
`S = Σ_{x∈Δ'}B_μ(x)`.  The ridge `k+m = ell−1` has exactly `ell` members (`diagIdx_card`) and lands
on `Δ'`, which is where the `ell^{-3}` comes from. -/
theorem Q_decomp (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    (hy : y ∈ CoarseLattice L ell) (B : Bond L → ℝ) :
    lineCoarseRestrict ell B (⟨y, hy⟩, μ)
      = (1 / (ell : ℝ) ^ 3) * faceSumLong B y ell μ
        + (1 / (ell : ℝ) ^ 4) * offSum B y ell μ := by
  have hnR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hline : ∀ i j k : ℕ, lineIntegralValue ell B (blkSite y μ i j k) μ
      = ∑ m ∈ range ell, B (blkSite y μ i j (k + m), μ) := by
    intro i j k
    unfold lineIntegralValue
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [show ((fun z => periodicLatticeShift z μ)^[m] (blkSite y μ i j k))
        = blkSite y μ i j (k + m) from blkSite_shift_mu y μ i j k m]
  have hA : ∑ i ∈ range ell, ∑ j ∈ range ell, (ell : ℝ) * B (faceSite y ell μ i j, μ)
      = (ell : ℝ) * faceSumLong B y ell μ := by
    rw [faceSumLong, face_sum hell hfit (fun x => B (x, μ)), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm)
  have hC : ∑ i ∈ range ell, ∑ j ∈ range ell,
        ∑ r ∈ offIdx ell, B (blkSite y μ i j (r.1 + r.2), μ)
      = offSum B y ell μ := by
    rw [offSum, Finset.sum_product, Finset.sum_product]
  have hkey : ∑ x ∈ blockOf y ell, lineIntegralValue ell B x μ
      = (ell : ℝ) * faceSumLong B y ell μ + offSum B y ell μ := by
    rw [block_sum3 hell hfit (fun x => lineIntegralValue ell B x μ)]
    have hstep : ∀ i j : ℕ,
        (∑ k ∈ range ell, lineIntegralValue ell B (blkSite y μ i j k) μ)
          = (ell : ℝ) * B (faceSite y ell μ i j, μ)
            + ∑ r ∈ offIdx ell, B (blkSite y μ i j (r.1 + r.2), μ) := by
      intro i j
      have h1 : (∑ k ∈ range ell, lineIntegralValue ell B (blkSite y μ i j k) μ)
          = ∑ q ∈ (range ell ×ˢ range ell : Finset (ℕ × ℕ)),
              B (blkSite y μ i j (q.1 + q.2), μ) := by
        rw [Finset.sum_product]
        exact Finset.sum_congr rfl (fun k _ => hline i j k)
      rw [h1, ← Finset.sum_filter_add_sum_filter_not (range ell ×ˢ range ell)
        (fun q : ℕ × ℕ => q.1 + q.2 = ell - 1)]
      congr 1
      have hdiag : ∑ q ∈ diagIdx ell, B (blkSite y μ i j (q.1 + q.2), μ)
          = ∑ _q ∈ diagIdx ell, B (faceSite y ell μ i j, μ) := by
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [diagIdx, Finset.mem_filter] at hq
        rw [hq.2, faceSite_eq_blkSite]
      rw [show ((range ell ×ˢ range ell).filter (fun q : ℕ × ℕ => q.1 + q.2 = ell - 1))
          = diagIdx ell from rfl, hdiag, Finset.sum_const, diagIdx_card hell, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ range ell) =>
      Finset.sum_congr rfl (fun j (_ : j ∈ range ell) => hstep i j))]
    simp only [Finset.sum_add_distrib]
    rw [hA, hC]
  rw [lineCoarseRestrict, hkey]
  field_simp <;> ring

/-- **The off-ridge energy count.**  For each fixed `k` the map `m ↦ k+m` is injective, so the
`(k,m)`-indexed off-ridge sum of squares costs at most `ell` copies of the two blocks' own
longitudinal in-block energies. -/
theorem offSum_energy_le (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    (hfit' : ∀ ν, ((coarseShift y ell μ) ν).val + ell ≤ L ν + 1) (B : Bond L → ℝ) :
    ∑ q ∈ (range ell ×ˢ range ell) ×ˢ offIdx ell,
        (B (blkSite y μ q.1.1 q.1.2 (q.2.1 + q.2.2), μ)) ^ 2
      ≤ (ell : ℝ) * boundaryCorr B y ell μ := by
  -- per transverse cell, the off-ridge sum is at most `ell` times the `offR` sum
  have hcell : ∀ i j : ℕ,
      (∑ r ∈ offIdx ell, (B (blkSite y μ i j (r.1 + r.2), μ)) ^ 2)
        ≤ (ell : ℝ) * ∑ r ∈ offR ell, (B (blkSite y μ i j r, μ)) ^ 2 := by
    intro i j
    have h1 : (∑ r ∈ offIdx ell, (B (blkSite y μ i j (r.1 + r.2), μ)) ^ 2)
        = ∑ k ∈ range ell, ∑ m ∈ (range ell).filter (fun m => ¬ (k + m = ell - 1)),
            (B (blkSite y μ i j (k + m), μ)) ^ 2 := by
      rw [offIdx, Finset.sum_filter, Finset.sum_product]
      exact Finset.sum_congr rfl (fun k _ => (Finset.sum_filter _ _).symm)
    rw [h1]
    calc ∑ k ∈ range ell, ∑ m ∈ (range ell).filter (fun m => ¬ (k + m = ell - 1)),
            (B (blkSite y μ i j (k + m), μ)) ^ 2
        ≤ ∑ _k ∈ range ell, ∑ r ∈ offR ell, (B (blkSite y μ i j r, μ)) ^ 2 :=
          Finset.sum_le_sum (fun k hk => shift_slice_le hell (Finset.mem_range.mp hk)
            (fun r => (B (blkSite y μ i j r, μ)) ^ 2) (fun _ => sq_nonneg _))
      _ = (ell : ℝ) * ∑ r ∈ offR ell, (B (blkSite y μ i j r, μ)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the `offR` sum splits into the two blocks
  have hsplit : ∑ i ∈ range ell, ∑ j ∈ range ell, ∑ r ∈ offR ell,
        (B (blkSite y μ i j r, μ)) ^ 2
      ≤ boundaryCorr B y ell μ := by
    have hlow : ∑ i ∈ range ell, ∑ j ∈ range ell, ∑ r ∈ range (ell - 1),
          (B (blkSite y μ i j r, μ)) ^ 2
        ≤ blockBondEnergy B y ell := by
      have := long_sum_le (z := y) (μ := μ) hell hfit B
      rwa [Finset.sum_product, Finset.sum_product] at this
    have hhigh : ∑ i ∈ range ell, ∑ j ∈ range ell, ∑ r ∈ Finset.Ico ell (2 * ell - 1),
          (B (blkSite y μ i j r, μ)) ^ 2
        ≤ blockBondEnergy B (coarseShift y ell μ) ell := by
      have hre : ∀ i j : ℕ, (∑ r ∈ Finset.Ico ell (2 * ell - 1),
            (B (blkSite y μ i j r, μ)) ^ 2)
          = ∑ t ∈ range (ell - 1), (B (blkSite (coarseShift y ell μ) μ i j t, μ)) ^ 2 := by
        intro i j
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr (by congr 1; omega) (fun t _ => ?_)
        rw [blkSite_next]
      rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hre i j))]
      have := long_sum_le (z := coarseShift y ell μ) (μ := μ) hell hfit' B
      rwa [Finset.sum_product, Finset.sum_product] at this
    have hEq : ∀ i j : ℕ, (∑ r ∈ offR ell, (B (blkSite y μ i j r, μ)) ^ 2)
        = (∑ r ∈ range (ell - 1), (B (blkSite y μ i j r, μ)) ^ 2)
          + ∑ r ∈ Finset.Ico ell (2 * ell - 1), (B (blkSite y μ i j r, μ)) ^ 2 := by
      intro i j
      rw [offR_split hell, Finset.sum_union (offR_disj hell)]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hEq i j))]
    simp only [Finset.sum_add_distrib]
    rw [boundaryCorr]
    linarith [hlow, hhigh]
  have hnR : (0 : ℝ) ≤ (ell : ℝ) := by positivity
  calc ∑ q ∈ (range ell ×ˢ range ell) ×ˢ offIdx ell,
          (B (blkSite y μ q.1.1 q.1.2 (q.2.1 + q.2.2), μ)) ^ 2
      = ∑ i ∈ range ell, ∑ j ∈ range ell,
          ∑ r ∈ offIdx ell, (B (blkSite y μ i j (r.1 + r.2), μ)) ^ 2 := by
        rw [Finset.sum_product, Finset.sum_product]
    _ ≤ ∑ i ∈ range ell, ∑ j ∈ range ell,
          (ell : ℝ) * ∑ r ∈ offR ell, (B (blkSite y μ i j r, μ)) ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcell i j))
    _ = (ell : ℝ) * ∑ i ∈ range ell, ∑ j ∈ range ell, ∑ r ∈ offR ell,
          (B (blkSite y μ i j r, μ)) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm)
    _ ≤ (ell : ℝ) * boundaryCorr B y ell μ := by
        exact mul_le_mul_of_nonneg_left hsplit hnR

theorem boundaryCorr_nonneg (B : Bond L → ℝ) (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    0 ≤ boundaryCorr B y ell μ := by
  rw [boundaryCorr]
  exact add_nonneg (blockBondEnergy_nonneg B y ell) (blockBondEnergy_nonneg B _ ell)

/-- **CMP96 (2.125), in the form the assembly consumes.** -/
theorem cs_2125 (hell : 0 < ell) (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1)
    (hfit' : ∀ ν, ((coarseShift y ell μ) ν).val + ell ≤ L ν + 1)
    (hy : y ∈ CoarseLattice L ell) (B : Bond L → ℝ) :
    (1 / 3) * (1 / (ell : ℝ) ^ 5) * (faceSumLong B y ell μ) ^ 2
      - (1 / (ell : ℝ) ^ 2) * boundaryCorr B y ell μ
    ≤ (ell : ℝ) * (lineCoarseRestrict ell B (⟨y, hy⟩, μ)) ^ 2 := by
  have hnR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set S := faceSumLong B y ell μ with hS
  set O := offSum B y ell μ with hO
  set C := boundaryCorr B y ell μ with hC
  -- Cauchy–Schwarz on the off-ridge sum
  have hcard : (((range ell ×ˢ range ell) ×ˢ offIdx ell : Finset ((ℕ × ℕ) × ℕ × ℕ)).card : ℝ)
      ≤ (ell : ℝ) ^ 4 := by
    rw [Finset.card_product, Finset.card_product, Finset.card_range]
    push_cast
    nlinarith [offIdx_card_le (ell := ell), Nat.cast_nonneg (α := ℝ) (offIdx ell).card,
      sq_nonneg ((ell : ℝ)), Nat.cast_nonneg (α := ℝ) ell]
  have hCS : O ^ 2
      ≤ (((range ell ×ˢ range ell) ×ˢ offIdx ell : Finset ((ℕ × ℕ) × ℕ × ℕ)).card : ℝ)
        * ∑ q ∈ (range ell ×ˢ range ell) ×ˢ offIdx ell,
            (B (blkSite y μ q.1.1 q.1.2 (q.2.1 + q.2.2), μ)) ^ 2 := by
    rw [hO, offSum]
    exact sq_sum_le_card_mul_sum_sq
  have hEn := offSum_energy_le hell hfit hfit' (μ := μ) B
  have hEnNN : (0 : ℝ) ≤ ∑ q ∈ (range ell ×ˢ range ell) ×ˢ offIdx ell,
      (B (blkSite y μ q.1.1 q.1.2 (q.2.1 + q.2.2), μ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hCNN : (0 : ℝ) ≤ C := boundaryCorr_nonneg B y ell μ
  have hO2 : O ^ 2 ≤ (ell : ℝ) ^ 5 * C := by
    calc O ^ 2 ≤ _ := hCS
      _ ≤ (ell : ℝ) ^ 4 * ((ell : ℝ) * C) := by
          apply mul_le_mul hcard hEn hEnNN (by positivity)
      _ = (ell : ℝ) ^ 5 * C := by ring
  -- the algebraic core
  have hq := quad_lower ((1 / (ell : ℝ) ^ 4) * O) ((1 / (ell : ℝ) ^ 3) * S)
  rw [Q_decomp hell hfit hy B, ← hS, ← hO]
  have hrw : ((1 / (ell : ℝ) ^ 3) * S + (1 / (ell : ℝ) ^ 4) * O)
      = ((1 / (ell : ℝ) ^ 4) * O + (1 / (ell : ℝ) ^ 3) * S) := by ring
  rw [hrw]
  have hne : ((ell : ℝ)) ≠ 0 := ne_of_gt hnR
  have hexp : (1 / 3) * (1 / (ell : ℝ) ^ 5) * S ^ 2
      = (ell : ℝ) * ((1 / 3) * ((1 / (ell : ℝ) ^ 3) * S) ^ 2) := by
    field_simp <;> ring
  have hexp2 : (ell : ℝ) * ((1 / 2) * ((1 / (ell : ℝ) ^ 4) * O) ^ 2)
      ≤ (1 / (ell : ℝ) ^ 2) * C := by
    have hp : (0 : ℝ) < (ell : ℝ) ^ 7 := by positivity
    have h5C : (0 : ℝ) ≤ (ell : ℝ) ^ 5 * C := mul_nonneg (by positivity) hCNN
    rw [← sub_nonneg]
    have hid : (1 / (ell : ℝ) ^ 2) * C - (ell : ℝ) * ((1 / 2) * ((1 / (ell : ℝ) ^ 4) * O) ^ 2)
        = ((ell : ℝ) ^ 5 * C - (1 / 2) * O ^ 2) / (ell : ℝ) ^ 7 := by
      field_simp <;> ring
    rw [hid]
    refine div_nonneg ?_ (le_of_lt hp)
    nlinarith [hO2, h5C]
  have hmul : (ell : ℝ) * ((1 / 3) * ((1 / (ell : ℝ) ^ 3) * S) ^ 2
      - (1 / 2) * ((1 / (ell : ℝ) ^ 4) * O) ^ 2)
      ≤ (ell : ℝ) * (((1 / (ell : ℝ) ^ 4) * O + (1 / (ell : ℝ) ^ 3) * S) ^ 2) :=
    mul_le_mul_of_nonneg_left hq (le_of_lt hnR)
  rw [hexp]
  nlinarith [hmul, hexp2]

/-! ## §5. The per-coarse-bond bound — CMP96 (2.127)×`L^{d-2}` with the CORRECTED exponent. -/

/-- **The per-coarse-bond inequality.**  This is CMP96 `(2.127)` multiplied by `L^{d-2} = ell`
at `d = 3`, with `(1/3)·ell^{-3}` replaced by `(1/3)·ell^{-4}` — the exponent the cross-sectional
Neumann gap actually supports (see the module docstring; the printed `ell^{-3}` is FALSE for
`ell ≥ 10`).  The correction is `3·ell^{-2}·boundaryCorr` (the source's is `1·`; the extra factor
is the coarse `A+C ≤ 2·blockBondEnergy` count, not a change of content). -/
theorem perC_bond (hell : 0 < ell) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (B : Bond L → ℝ) (c : CoarseBond L ell) :
    (1 / 3) * (1 / (ell : ℝ) ^ 4) * topFaceEnergy B c.1.1 ell c.2
      ≤ (ell : ℝ) * (lineCoarseRestrict ell B c) ^ 2
        + (1 / (ell : ℝ) ^ 2) * regionCurlEnergy B c.1.1 ell c.2
        + 3 * (1 / (ell : ℝ) ^ 2) * boundaryCorr B c.1.1 ell c.2 := by
  obtain ⟨⟨y, hy⟩, μ⟩ := c
  set t : ℝ := (ell : ℝ) with hT
  have ht0 : (0 : ℝ) < t := by rw [hT]; exact_mod_cast hell
  have ht1 : (1 : ℝ) ≤ t := by rw [hT]; exact_mod_cast hell
  have hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1 := fun ν => coarseLattice_mem_fits hdvd hy ν
  have hy' := coarseShift_mem_coarseLattice hdvd hy μ
  have hfit' : ∀ ν, ((coarseShift y ell μ) ν).val + ell ≤ L ν + 1 :=
    fun ν => coarseLattice_mem_fits hdvd hy' ν
  set T := topFaceEnergy B y ell μ with hTT
  set G := gradEnergy2 ell (faceField B y ell μ) with hG
  set S := faceSumLong B y ell μ with hS
  set R := regionCurlEnergy B y ell μ with hR
  set C := boundaryCorr B y ell μ with hC
  have hPo : T ≤ t ^ 2 * G + S ^ 2 / t ^ 2 := face_poincare hell hfit B
  have h24 : G ≤ 3 * R + 6 * C := face_2124 hell hfit B
  have h25 := cs_2125 hell hfit hfit' hy B
  -- (1/3)t⁻⁴·T ≤ (1/3)t⁻²·G + (1/3)t⁻⁶·S²
  have hc4 : (0 : ℝ) ≤ (1 / 3) * (1 / t ^ 4) := by positivity
  have step1 : (1 / 3) * (1 / t ^ 4) * T ≤ (1 / 3) * (1 / t ^ 4) * (t ^ 2 * G + S ^ 2 / t ^ 2) :=
    mul_le_mul_of_nonneg_left hPo hc4
  have step2 : (1 / 3) * (1 / t ^ 4) * (t ^ 2 * G + S ^ 2 / t ^ 2)
      = (1 / 3) * (1 / t ^ 2) * G + (1 / 3) * (1 / t ^ 5) * S ^ 2 * (1 / t) := by
    field_simp <;> ring
  have hc2 : (0 : ℝ) ≤ (1 / 3) * (1 / t ^ 2) := by positivity
  have step3 : (1 / 3) * (1 / t ^ 2) * G ≤ (1 / 3) * (1 / t ^ 2) * (3 * R + 6 * C) :=
    mul_le_mul_of_nonneg_left h24 hc2
  have step4 : (1 / 3) * (1 / t ^ 2) * (3 * R + 6 * C) = (1 / t ^ 2) * R + 2 * ((1 / t ^ 2) * C) := by
    field_simp <;> ring
  -- the S² term loses one power of t (t ≥ 1)
  have hSnn : (0 : ℝ) ≤ (1 / 3) * (1 / t ^ 5) * S ^ 2 := by positivity
  have step5 : (1 / 3) * (1 / t ^ 5) * S ^ 2 * (1 / t) ≤ (1 / 3) * (1 / t ^ 5) * S ^ 2 := by
    have h1 : (1 : ℝ) / t ≤ 1 := by
      rw [div_le_one ht0]; exact ht1
    nlinarith [hSnn, h1]
  have hQeq : lineCoarseRestrict ell B ((⟨y, hy⟩ : {w // w ∈ CoarseLattice L ell}), μ)
      = lineCoarseRestrict ell B (⟨y, hy⟩, μ) := rfl
  rw [hQeq]
  linarith [step1, step3, step5, h25]

/-! ## §6. The global assembly — Bałaban's Lemma 2.4 for EVERY `ell ≥ 2`. -/

/-- **CMP96 Lemma 2.4 / (2.128) at `d = 3`, with the exponent corrected to `L^{-d-2}`.**
`ell·Σ_c|(Q₁B)(c)|² + Σ_p|(∂₁B)(p)|² ≥ (1/180)·ell^{-5}·‖B‖²`.
This is NOT a weakening of `BlockPoincareLemma24.Lemma24Conclusion` (which is left untouched); it is
a SEPARATE, strictly weaker `Prop`, and the printed `ell^{-4}` is not reachable by Bałaban's own
route for large `ell` (module docstring). -/
noncomputable def Lemma24ConclusionCorrected (ell : ℕ) (B : Bond L → ℝ) : Prop :=
  (ell : ℝ) * coarseQEnergy ell B + totalCurlEnergy B
    ≥ (1 / 180) * (1 / (ell : ℝ) ^ 5) * bondNormSq B

/-- `Lemma24Conclusion` (the printed constant) implies the corrected one, for every `ell ≥ 1`. -/
theorem corrected_of_lemma24 (hell : 0 < ell) (B : Bond L → ℝ)
    (h : Lemma24Conclusion ell B) : Lemma24ConclusionCorrected ell B := by
  have ht0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have ht1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hN : (0 : ℝ) ≤ bondNormSq B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Lemma24ConclusionCorrected, ge_iff_le]
  rw [Lemma24Conclusion, ge_iff_le] at h
  have hstep : (1 / 180 : ℝ) * (1 / (ell : ℝ) ^ 5) * bondNormSq B
      ≤ (1 / 108) * (1 / (ell : ℝ) ^ 4) * bondNormSq B := by
    have hp4 : (0 : ℝ) < (ell : ℝ) ^ 4 := by positivity
    have ha : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 5 := by positivity
    have h1 : (1 : ℝ) / (ell : ℝ) ^ 5 ≤ 1 / (ell : ℝ) ^ 4 := by
      apply one_div_le_one_div_of_le hp4
      nlinarith [pow_nonneg (le_trans zero_le_one ht1) 4, ht1]
    calc (1 / 180 : ℝ) * (1 / (ell : ℝ) ^ 5) * bondNormSq B
        ≤ (1 / 108 : ℝ) * (1 / (ell : ℝ) ^ 5) * bondNormSq B := by
          nlinarith [mul_nonneg ha hN]
      _ ≤ (1 / 108 : ℝ) * (1 / (ell : ℝ) ^ 4) * bondNormSq B := by
          nlinarith [mul_nonneg hN (sub_nonneg.mpr h1)]
  linarith [h, hstep]

/-- **THE GENERAL-`ell` THEOREM.** For every `ell ≥ 2`, every torus with `ell < L μ + 1` and
`ell ∣ L μ + 1`, and every `(2.121)`-admissible `B`, the corrected Lemma 2.4 holds — UNCONDITIONALLY,
with no numeric certificate and no `ell`-dependent case split. -/
theorem lemma24_general_ell (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (B : Bond L → ℝ) (hB : B ∈ admissibleSubspaceInter L ell) :
    Lemma24ConclusionCorrected ell B := by
  have hell : 0 < ell := by omega
  set t : ℝ := (ell : ℝ) with hT
  have ht0 : (0 : ℝ) < t := by rw [hT]; exact_mod_cast hell
  have ht2 : (2 : ℝ) ≤ t := by rw [hT]; exact_mod_cast hell2
  set N := bondNormSq B with hN
  set Sin := inBlockBondEnergy ell B with hSin
  set Ptot := totalCurlEnergy B with hPtot
  set Qtot := coarseQEnergy ell B with hQtot
  have hPnn : (0 : ℝ) ≤ Ptot := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQnn : (0 : ℝ) ≤ Qtot := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSinnn : (0 : ℝ) ≤ Sin :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  -- sum the per-c bound
  have hsum := Finset.sum_le_sum
    (fun c (_ : c ∈ (Finset.univ : Finset (CoarseBond L ell))) => perC_bond hell hdvd B c)
  have hLHS : ∑ c : CoarseBond L ell, (1 / 3) * (1 / t ^ 4) * topFaceEnergy B c.1.1 ell c.2
      = (1 / 3) * (1 / t ^ 4) * ∑ c : CoarseBond L ell, topFaceEnergy B c.1.1 ell c.2 := by
    rw [← Finset.mul_sum]
  have hRHS : ∑ c : CoarseBond L ell,
        ((t * (lineCoarseRestrict ell B c) ^ 2
          + (1 / t ^ 2) * regionCurlEnergy B c.1.1 ell c.2)
          + 3 * (1 / t ^ 2) * boundaryCorr B c.1.1 ell c.2)
      = t * Qtot + (1 / t ^ 2) * (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2)
        + 3 * (1 / t ^ 2) * (∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hQtot, coarseQEnergy]
  rw [hLHS, hRHS] at hsum
  -- the four banked facts
  have hF1 := sum_topFace_ge_Sbet (L := L) (ell := ell) hell hdvd hstrict B
  have hF2 := sum_boundaryCorr_le (L := L) (ell := ell) hdvd B
  rw [← hN, ← hSin] at hF1
  rw [← hSin] at hF2
  have hF4 := sum_regionCurl_le_slabCurl (L := L) (ell := ell) B
  have hslab := slabCurlEnergy_eq_two_totalCurl (L := L) (ell := ell) hell hdvd B
  have h2123 := region_2123 (L := L) (ell := ell) (hstrict 0) (hstrict 1) (hstrict 2) B hB
  have hPin := inBlockCurl_le_total (L := L) (ell := ell) B
  have hSin3 : Sin ≤ 3 * t ^ 3 * Ptot := by
    rw [hSin, hPtot, hT]; linarith [h2123, mul_le_mul_of_nonneg_left hPin
      (show (0 : ℝ) ≤ 3 * (ell : ℝ) ^ 3 by positivity)]
  have hR2 : (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2) ≤ 2 * Ptot := by
    rw [hPtot]; linarith [hF4, hslab]
  -- clear the denominators
  have hid : ∀ X : ℝ, 3 * t ^ 4 * ((1 / 3) * (1 / t ^ 4) * X) = X := by
    intro X; field_simp
  have hbig := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 3 * t ^ 4 by positivity)
  rw [hid] at hbig
  have hexpand : 3 * t ^ 4 * (t * Qtot
        + (1 / t ^ 2) * (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2)
        + 3 * (1 / t ^ 2) * (∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2))
      = 3 * t ^ 5 * Qtot
        + 3 * t ^ 2 * (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2)
        + 9 * t ^ 2 * (∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2) := by
    field_simp <;> ring
  rw [hexpand] at hbig
  have ht2nn : (0 : ℝ) ≤ t ^ 2 := by positivity
  have hA : 3 * t ^ 2 * (∑ c : CoarseBond L ell, regionCurlEnergy B c.1.1 ell c.2)
      ≤ 3 * t ^ 2 * (2 * Ptot) := by
    have := mul_le_mul_of_nonneg_left hR2 (show (0 : ℝ) ≤ 3 * t ^ 2 by positivity); linarith
  have hBc : 9 * t ^ 2 * (∑ c : CoarseBond L ell, boundaryCorr B c.1.1 ell c.2)
      ≤ 9 * t ^ 2 * (6 * Sin) := by
    have := mul_le_mul_of_nonneg_left hF2 (show (0 : ℝ) ≤ 9 * t ^ 2 by positivity)
    linarith [this]
  have hSinP : 54 * t ^ 2 * Sin ≤ 54 * t ^ 2 * (3 * t ^ 3 * Ptot) := by
    have := mul_le_mul_of_nonneg_left hSin3 (show (0 : ℝ) ≤ 54 * t ^ 2 by positivity); linarith
  -- the main size bound
  have hMain : N ≤ 3 * t ^ 5 * Qtot + (3 * t ^ 3 + 6 * t ^ 2 + 162 * t ^ 5) * Ptot := by
    linarith [hbig, hF1, hA, hBc, hSinP, hSin3, hPnn, hSinnn]
  -- conclude
  rw [Lemma24ConclusionCorrected, ge_iff_le, ← sub_nonneg, ← hN, ← hPtot, ← hQtot, ← hT]
  have hkey : t * Qtot + Ptot - (1 / 180) * (1 / t ^ 5) * N
      = (180 * t ^ 5 * (t * Qtot + Ptot) - N) / (180 * t ^ 5) := by
    field_simp <;> ring
  rw [hkey]
  refine div_nonneg ?_ (by positivity)
  have hc1 : (0 : ℝ) ≤ 180 * t ^ 6 - 3 * t ^ 5 := by nlinarith [ht2, pow_pos ht0 5]
  have hc2' : (0 : ℝ) ≤ 18 * t ^ 5 - 3 * t ^ 3 - 6 * t ^ 2 := by
    have hq1 : (0 : ℝ) ≤ t ^ 2 - 1 := by nlinarith [ht2, sq_nonneg (t - 2)]
    have hq2 : (0 : ℝ) ≤ t ^ 3 - 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht2) hq1, hq1, ht2]
    have h3 : t ^ 3 ≤ t ^ 5 := by
      nlinarith [mul_nonneg (le_of_lt (pow_pos ht0 3)) hq1]
    have h2' : t ^ 2 ≤ t ^ 5 := by
      nlinarith [mul_nonneg (le_of_lt (pow_pos ht0 2)) hq2]
    nlinarith [h3, h2', pow_pos ht0 5]
  nlinarith [hMain, mul_nonneg hc1 hQnn, mul_nonneg hc2' hPnn]

#print axioms lemma24_general_ell
#print axioms corrected_of_lemma24
#print axioms perC_bond
#print axioms face_2124
#print axioms cs_2125
#print axioms face_poincare

/-! ## §7. `ell = 2` consistency, and an `ell = 3` non-vacuity witness. -/

/-- **`ell = 2` consistency, numerically.** At `ell = 2` the existing milestone
`HrefReduction.lemma24_unconditional_U1_ell2_uncond` (constant `1/1728`) is STRICTLY STRONGER than
this file's conclusion (constant `1/5760`); the two agree in direction, so there is no conflict —
this file does not subsume the `ell = 2` result, it is implied by it. -/
theorem ell2_consistency :
    (1 / 180 : ℝ) * (1 / (2 : ℝ) ^ 5) ≤ (1 / 108 : ℝ) * (1 / (2 : ℝ) ^ 4) := by norm_num

section NonVacuity
set_option maxRecDepth 8000

/-- The non-vacuity torus: `L ν = 8`, so `L ν + 1 = 9`, `3 ∣ 9`, `3 < 9`. -/
def witL3 : PeriodicLatticeExtent := fun _ => 8

theorem witL3_strict : ∀ ν : Fin 3, (3 : ℕ) < witL3 ν + 1 := by decide

theorem witL3_dvd : ∀ ν : Fin 3, (3 : ℕ) ∣ (witL3 ν + 1) := by decide

theorem witnessNorm_pos : (0 : ℝ) < bondNormSq (generalWrapConfig witL3) := by
  rw [bondNormSq]
  refine Finset.sum_pos' (fun b _ => sq_nonneg _) ⟨generalWrapBond witL3, Finset.mem_univ _, ?_⟩
  have hval : generalWrapConfig witL3 (generalWrapBond witL3) = 1 := by
    simp [generalWrapConfig]
  rw [hval]; norm_num

/-- **NON-VACUITY at `ell = 3`.** The general-`ell` theorem, instantiated at `ell = 3` on the
`9³` torus with the unconditionally-admissible nonzero witness `generalWrapConfig`: BOTH sides are
strictly positive.  (`ell = 2` witnesses do not demonstrate generality; this one is `ell = 3`.) -/
theorem lemma24_general_ell_nonvacuous_ell3 :
    (0 : ℝ) < (1 / 180) * (1 / ((3 : ℕ) : ℝ) ^ 5) * bondNormSq (generalWrapConfig witL3)
    ∧ (1 / 180) * (1 / ((3 : ℕ) : ℝ) ^ 5) * bondNormSq (generalWrapConfig witL3)
        ≤ ((3 : ℕ) : ℝ) * coarseQEnergy 3 (generalWrapConfig witL3)
          + totalCurlEnergy (generalWrapConfig witL3)
    ∧ (0 : ℝ) < ((3 : ℕ) : ℝ) * coarseQEnergy 3 (generalWrapConfig witL3)
        + totalCurlEnergy (generalWrapConfig witL3) := by
  have hthm := lemma24_general_ell (L := witL3) (ell := 3) (by norm_num)
    witL3_strict witL3_dvd (generalWrapConfig witL3) generalWrapConfig_mem
  rw [Lemma24ConclusionCorrected, ge_iff_le] at hthm
  have hpos : (0 : ℝ) < (1 / 180) * (1 / ((3 : ℕ) : ℝ) ^ 5) * bondNormSq (generalWrapConfig witL3) := by
    have := witnessNorm_pos
    have hc : (0 : ℝ) < (1 / 180) * (1 / ((3 : ℕ) : ℝ) ^ 5) := by norm_num
    exact mul_pos hc this
  exact ⟨hpos, hthm, lt_of_lt_of_le hpos hthm⟩

end NonVacuity

#print axioms lemma24_general_ell
#print axioms lemma24_general_ell_nonvacuous_ell3
#print axioms ell2_consistency
#print axioms Q_decomp
#print axioms offSum_energy_le

end AdalyFormal.Balaban.Lemma24GeneralEll
