/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.U1AnchorPoincare
import AdalyFormal.Balaban.HjMinimizer

set_option autoImplicit false

/-!
# The coarse-lattice Poincaré lemma, and the flat lift `[UPPER-DEGENERATE]` needs

**What this file does.** `U1AnchorPoincare.lean` proves the discrete Poincaré/Hodge lemma on a
periodic 3-torus, for `LatticeOperators.curlValue`. `U1Anchor.exists_bounded_weight_symbol` needs
it for `CoarseCurl.coarseCurlValue` — the curl on the COARSE lattice `CoarseLattice L ell` with
its own adjacency `coarseShift · ell`. This file supplies the transport, and then the three
remaining pieces that turn it into `[UPPER-DEGENERATE]`.

The transport is an isomorphism of lattices, not an analogy: the coarse lattice at scale `ell`
inside `L` IS the periodic lattice of extent `coarseExtent L ell μ = (L μ + 1)/ell − 1`, with
`coarseShift · ell` corresponding to `periodicLatticeShift` (`toFine_shift`). So the Poincaré
lemma is PROVED ONCE and transported, not re-proved (LAW-19).

## §A — the four pieces

1. **`coarse_curlFree_eq_grad_add_const`** — coarse Poincaré: `∂₁'B = 0 ⟹ B = ∂₀'h + c` where
   `∂₀'h (y,μ) = h(coarseShift y ell μ) − h(y)` and `c` is the harmonic (direction-constant) part.
2. **`coarseRestrictSite_siteLift`** — `Q_ell'` (the SCALAR block average, `KernelSubspace`) is
   surjective onto functions on the coarse lattice, by the explicit block-delta lift (the same
   construction `HjMinimizer.coarseRestrict_coarseLiftValue` uses one level up, LAW-19 pattern).
3. **`lineCoarseRestrict_constBond`** — the FAITHFUL `Q_k` returns a constant bond field
   unchanged (this is exactly the property `LatticeOperators.coarseRestrict` FAILS, by its own
   `coarseRestrict_const_witness`: the dropped line integral costs a factor `ell`).
4. **`exists_flat_with_same_Q`** — assembly: if `∂₁'(Q_k A0) = 0` then there is a FINE field `A1`
   with `∂₁A1 = 0` and `Q_kA1 = Q_kA0`.

## §B — the load-bearing hypothesis, and why it is not optional

`exists_gaugeConstraint_with_same_curl` carries

  `hlev : ∀ lam ∈ kernelSubspace levels, ∀ y, coarseRestrictSite ell lam y = 0`

i.e. **`N(Q') ⊆ ker Q_ell'`: the RG level data must include the scale `ell` the coarse-graining is
performed at.** `faithfulLevels_hlev` discharges it from `(ell, Finset.univ) ∈ levels`, which is
Bałaban's own `N(Q_k')` (CMP96 (2.7)/(2.10) at the top scale).

**This hypothesis is NOT a convenience.** In `U1Anchor.lean`'s `exists_bounded_weight_symbol` the
binders `ell` and `levels` are INDEPENDENT. The exact place `hlev` is spent is
`lineCoarseRestrictCLM_gradCLM_eq_zero` (§6 below): the gauge correction `∂₀λ` restoring
`R∂₀*v = 0` is free of charge only when `Q_k(∂₀λ) = 0`, and by CMP95 (1.20) that is exactly
`Q_ell'λ = 0`. With `levels = []`, `kernelSubspace [] = ⊤` and nothing forces it, so the correction
moves `Q_k` and this construction stops.
**Grading of what is and is not proved.** KERNEL-CHECKED: `hlev` is discharged by
`(ell, Finset.univ) ∈ levels` (`faithfulLevels_hlev`), and it FAILS at `levels = []`
(`U1Anchor.faithfulLevels_hypothesis_fails_for_nil`). EXPLORATION-GRADE ONLY, proved nowhere in
this tree: that the target STATEMENT (not merely this proof of it) is false at `levels = []` —
Python dimension counts, which sign nothing (L10), smallest instance `ell = 2`, `L + 1 = (2,4,6)`,
`dim ker(∂₁'∘Q_k) = 134` versus `dim(V + ker ∂₁) = 132`, the same lattice at
`levels = [(ell, univ)]` giving `134 = 134`. Note `levels = []` gives
`deltaKernelImage = range Δ₀ = range ∂₀*`, so `RProj ∘ ∂₀* = ∂₀*` and `V = ker Q_k ∩ ker ∂₀*` —
the SMALLEST `V`, hence the HARDEST instance, not a degenerate one.
-/

namespace AdalyFormal.Balaban.U1AnchorCoarse

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.KernelSubspace
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.HjMinimizer
open AdalyFormal.Balaban.U1AnchorPoincare

variable {L : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1. The coarse lattice IS a periodic lattice -/

/-- The extent of the coarse lattice: `(L μ + 1)/ell` coarse sites in direction `μ`. -/
def coarseExtent (L : PeriodicLatticeExtent) (ell : ℕ) : PeriodicLatticeExtent :=
  fun μ => (L μ + 1) / ell - 1

theorem coarseExtent_spec (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (μ : Fin 3) :
    ell * (coarseExtent L ell μ + 1) = L μ + 1 := by
  obtain ⟨m, hm⟩ := hdvd μ
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hdiv : (L μ + 1) / ell = m := by
    rw [hm, Nat.mul_div_cancel_left _ hell]
  have hm1 : m - 1 + 1 = m := by omega
  simp only [coarseExtent, hdiv, hm1]
  exact hm.symm

/-- Coarse index → fine site. Total (the `%` is a no-op under `hdvd`, `toFine_val`). -/
def toFine (L : PeriodicLatticeExtent) (ell : ℕ) (a : PeriodicLatticeSite (coarseExtent L ell)) :
    PeriodicLatticeSite L :=
  fun μ => ⟨(ell * (a μ).val) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- Fine site → coarse index. -/
def toIdx (L : PeriodicLatticeExtent) (ell : ℕ) (y : PeriodicLatticeSite L) :
    PeriodicLatticeSite (coarseExtent L ell) :=
  fun μ => ⟨((y μ).val / ell) % (coarseExtent L ell μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem toFine_val (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (a : PeriodicLatticeSite (coarseExtent L ell)) (μ : Fin 3) :
    ((toFine L ell a) μ).val = ell * (a μ).val := by
  have hspec := coarseExtent_spec hell hdvd μ
  have hlt : ell * (a μ).val < L μ + 1 := by
    have := (a μ).isLt
    calc ell * (a μ).val < ell * (coarseExtent L ell μ + 1) :=
          mul_lt_mul_of_pos_left this hell
      _ = L μ + 1 := hspec
  simp only [toFine]
  exact Nat.mod_eq_of_lt hlt

theorem toFine_mem (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (a : PeriodicLatticeSite (coarseExtent L ell)) : toFine L ell a ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice]
  intro μ
  rw [toFine_val hell hdvd a μ, Nat.mul_mod_right]

theorem toIdx_val (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (y : PeriodicLatticeSite L) (μ : Fin 3) :
    ((toIdx L ell y) μ).val = (y μ).val / ell := by
  have hspec := coarseExtent_spec hell hdvd μ
  have hlt : (y μ).val / ell < coarseExtent L ell μ + 1 := by
    have h1 := (y μ).isLt
    have hspec' : (coarseExtent L ell μ + 1) * ell = L μ + 1 := by
      rw [Nat.mul_comm]; exact hspec
    rw [Nat.div_lt_iff_lt_mul hell]
    omega
  simp only [toIdx]
  exact Nat.mod_eq_of_lt hlt

theorem toIdx_toFine (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (a : PeriodicLatticeSite (coarseExtent L ell)) : toIdx L ell (toFine L ell a) = a := by
  funext μ
  apply Fin.ext
  rw [toIdx_val hell hdvd, toFine_val hell hdvd, Nat.mul_div_cancel_left _ hell]

theorem toFine_toIdx (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    toFine L ell (toIdx L ell y) = y := by
  funext μ
  apply Fin.ext
  rw [toFine_val hell hdvd, toIdx_val hell hdvd]
  rw [mem_CoarseLattice] at hy
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hy μ))

/-- **THE INTERTWINING**: the coarse index's own one-step shift is the fine lattice's `ell`-step
`coarseShift`. This is what makes the coarse lattice a periodic lattice in its own right. -/
theorem toFine_shift (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (a : PeriodicLatticeSite (coarseExtent L ell)) (μ : Fin 3) :
    toFine L ell (periodicLatticeShift a μ) = coarseShift (toFine L ell a) ell μ := by
  funext ν
  apply Fin.ext
  by_cases h : ν = μ
  · subst h
    rw [toFine_val hell hdvd, coarseShift_val_eq, toFine_val hell hdvd,
      U1AnchorPoincare.shift_val, ← coarseExtent_spec hell hdvd ν, ← Nat.mul_succ,
      Nat.mul_mod_mul_left]
  · rw [toFine_val hell hdvd, coarseShift_apply_ne _ _ _ _ h, toFine_val hell hdvd,
      U1AnchorPoincare.shift_apply_ne a μ ν h]

/-! ## §2. Transport of the Poincaré lemma to the coarse lattice -/

/-- The coarse bond field, pulled back to a bond field on the coarse-index lattice. -/
noncomputable def pullback (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → ℝ) : Bond (coarseExtent L ell) → ℝ :=
  fun b => B (⟨toFine L ell b.1, toFine_mem hell hdvd b.1⟩, b.2)

theorem curlFree_pullback (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → ℝ) (hB : ∀ p : CoarsePlaquette L ell, coarseCurlValue hdvd B p = 0) :
    U1AnchorPoincare.CurlFree (pullback hell hdvd B) := by
  intro p
  have hp := hB (⟨⟨toFine L ell p.1, toFine_mem hell hdvd p.1⟩, p.2⟩)
  simp only [coarseCurlValue] at hp
  simp only [curlValue, pullback]
  have e1 : (⟨toFine L ell (periodicLatticeShift p.1 p.2.1.1),
      toFine_mem hell hdvd (periodicLatticeShift p.1 p.2.1.1)⟩ :
      {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) =
      ⟨coarseShift (toFine L ell p.1) ell p.2.1.1,
        coarseShift_mem_coarseLattice hdvd (toFine_mem hell hdvd p.1) p.2.1.1⟩ :=
    Subtype.ext (toFine_shift hell hdvd p.1 p.2.1.1)
  have e2 : (⟨toFine L ell (periodicLatticeShift p.1 p.2.1.2),
      toFine_mem hell hdvd (periodicLatticeShift p.1 p.2.1.2)⟩ :
      {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) =
      ⟨coarseShift (toFine L ell p.1) ell p.2.1.2,
        coarseShift_mem_coarseLattice hdvd (toFine_mem hell hdvd p.1) p.2.1.2⟩ :=
    Subtype.ext (toFine_shift hell hdvd p.1 p.2.1.2)
  rw [e1, e2]
  linarith

/-- **THE COARSE POINCARÉ LEMMA.** A coarse-curl-free coarse bond field is a coarse gradient plus
a direction-constant field. Transported from `U1AnchorPoincare.curlFree_eq_grad_add_const`. -/
theorem coarse_curlFree_eq_grad_add_const (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : CoarseBond L ell → ℝ)
    (hB : ∀ p : CoarsePlaquette L ell, coarseCurlValue hdvd B p = 0) :
    ∃ (h : PeriodicLatticeSite L → ℝ) (c : Fin 3 → ℝ),
      ∀ (y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) (μ : Fin 3),
        B (y, μ) = h (coarseShift y.1 ell μ) - h y.1 + c μ := by
  obtain ⟨f, c, hf⟩ :=
    U1AnchorPoincare.curlFree_eq_grad_add_const (curlFree_pullback hell hdvd B hB)
  refine ⟨fun z => f (toIdx L ell z), c, ?_⟩
  intro y μ
  have hstep := hf (toIdx L ell y.1, μ)
  simp only [pullback] at hstep
  have hsub : (⟨toFine L ell (toIdx L ell y.1),
      toFine_mem hell hdvd (toIdx L ell y.1)⟩ :
      {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}) = y :=
    Subtype.ext (toFine_toIdx hell hdvd y.2)
  rw [hsub] at hstep
  have hkey : toIdx L ell (coarseShift y.1 ell μ) = periodicLatticeShift (toIdx L ell y.1) μ := by
    have h1 : coarseShift y.1 ell μ = toFine L ell (periodicLatticeShift (toIdx L ell y.1) μ) := by
      rw [toFine_shift hell hdvd, toFine_toIdx hell hdvd y.2]
    rw [h1, toIdx_toFine hell hdvd]
  rw [hstep]
  simp only [hkey]

/-! ## §3. `Q_ell'` is surjective onto the coarse lattice: the block-delta lift -/

/-- The block-delta lift of a function on coarse sites: all of the block's mass at the centre. -/
noncomputable def siteLift (ell : ℕ) (h : PeriodicLatticeSite L → ℝ) :
    PeriodicLatticeSite L → ℝ :=
  fun x => if x ∈ CoarseLattice L ell then (ell : ℝ) ^ 3 * h x else 0

/-- **The lift inverts `Q_ell'`.** Only the block's own centre survives, by
`coarseLattice_unique` (LAW-19: the identical argument
`HjMinimizer.coarseRestrict_coarseLiftValue` uses for the bond-level operator). -/
theorem coarseRestrictSite_siteLift (hell : 0 < ell) (h : PeriodicLatticeSite L → ℝ)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    coarseRestrictSite ell (siteLift ell h) y = h y := by
  have hself : y ∈ blockOf y ell := by
    rw [mem_blockOf]
    intro ν
    exact ⟨le_refl _, by omega⟩
  have hsum : (∑ x ∈ blockOf y ell, siteLift ell h x) = siteLift ell h y := by
    apply Finset.sum_eq_single
    · intro x hx hxy
      by_cases hxc : x ∈ CoarseLattice L ell
      · exfalso
        have hxself : x ∈ blockOf x ell := by
          rw [mem_blockOf]
          intro ν
          exact ⟨le_refl _, by omega⟩
        exact hxy (coarseLattice_unique ell hxc hy hxself hx)
      · simp only [siteLift, if_neg hxc]
    · intro hc
      exact absurd hself hc
  simp only [coarseRestrictSite]
  rw [hsum]
  simp only [siteLift, if_pos hy]
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  field_simp

/-! ## §4. The faithful `Q_k` on a constant bond field -/

/-- `∂₁∘∂₀ = 0`, in applied form. -/
theorem curlCLM_gradCLM (L : PeriodicLatticeExtent) (lam : SiteSpace L) :
    curlCLM L (gradCLM L lam) = 0 := by
  have h := curlCLM_comp_gradCLM_eq_zero L
  calc curlCLM L (gradCLM L lam) = ((curlCLM L).comp (gradCLM L)) lam := rfl
    _ = 0 := by rw [h]; rfl

/-- The direction-constant bond configuration, as a Hilbert-space vector. -/
noncomputable def constBond (L : PeriodicLatticeExtent) (c : Fin 3 → ℝ) : BondSpace L :=
  (bondEquiv L).symm (fun b : Bond L => c b.2)

theorem bondEquiv_constBond (L : PeriodicLatticeExtent) (c : Fin 3 → ℝ) :
    bondEquiv L (constBond L c) = fun b : Bond L => c b.2 := by
  simp [constBond]

theorem curlCLM_constBond (L : PeriodicLatticeExtent) (c : Fin 3 → ℝ) :
    curlCLM L (constBond L c) = 0 := by
  apply (plaquetteEquiv L).injective
  rw [curlCLM_apply, bondEquiv_constBond, map_zero]
  funext p
  exact U1AnchorPoincare.curlValue_of_const c p

/-- **The faithful `Q_k` returns a constant bond field unchanged** — the defining property the
line integral restores and `LatticeOperators.coarseRestrict` loses (there the same field returns
`c/ell`, `coarseRestrict_const_witness`). -/
theorem lineCoarseRestrict_constBond (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (c : Fin 3 → ℝ) (b : CoarseBond L ell) :
    lineCoarseRestrict ell (fun bd : Bond L => c bd.2) b = c b.2 := by
  have hline : ∀ x : PeriodicLatticeSite L,
      lineIntegralValue ell (fun bd : Bond L => c bd.2) x b.2 = (ell : ℝ) * c b.2 := by
    intro x
    simp only [lineIntegralValue, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [lineCoarseRestrict]
  rw [Finset.sum_congr rfl (fun x _ => hline x), Finset.sum_const,
    card_blockOf_of_coarse hdvd b.1.2, nsmul_eq_mul]
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  push_cast
  field_simp

/-! ## §5. THE FLAT LIFT -/

/-- **`∂₁'(Q_kA0) = 0 ⟹ there is a FLAT fine field with the same `Q_k`.** This is the whole
content of `[UPPER-DEGENERATE]` that does not involve the gauge condition. -/
theorem exists_flat_with_same_Q (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A0 : BondSpace L)
    (hflat : coarseCurlCLM L ell hdvd (lineCoarseRestrictCLM L ell A0) = 0) :
    ∃ A1 : BondSpace L, curlCLM L A1 = 0 ∧
      lineCoarseRestrictCLM L ell A1 = lineCoarseRestrictCLM L ell A0 := by
  have hBcurl : ∀ p : CoarsePlaquette L ell,
      coarseCurlValue hdvd (lineCoarseRestrict ell (bondEquiv L A0)) p = 0 := by
    intro p
    have hq := congrArg (coarsePlaquetteEquiv L ell) hflat
    rw [coarseCurlCLM_apply, map_zero, lineCoarseRestrictCLM_apply] at hq
    exact congrFun hq p
  obtain ⟨h, c, hgc⟩ := coarse_curlFree_eq_grad_add_const hell hdvd _ hBcurl
  refine ⟨gradCLM L ((siteEquiv L).symm (siteLift ell (fun z => (ell : ℝ) * h z))) +
      constBond L c, ?_, ?_⟩
  · rw [map_add, curlCLM_gradCLM, curlCLM_constBond, add_zero]
  · apply (coarseBondEquiv L ell).injective
    simp only [map_add, lineCoarseRestrictCLM_apply, gradCLM_apply, bondEquiv_constBond,
      LinearEquiv.apply_symm_apply]
    funext b
    obtain ⟨⟨y, hy⟩, μ⟩ := b
    change lineCoarseRestrict ell (gradValue (siteLift ell (fun z => (ell : ℝ) * h z)))
          ((⟨y, hy⟩ : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), μ) +
        lineCoarseRestrict ell (fun bd : Bond L => c bd.2)
          ((⟨y, hy⟩ : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), μ) =
        lineCoarseRestrict ell (bondEquiv L A0)
          ((⟨y, hy⟩ : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), μ)
    rw [lineCoarseRestrict_gradValue hell (hdvd μ) hy,
      lineCoarseRestrict_constBond hell hdvd c,
      coarseRestrictSite_siteLift hell _ (coarseShift_mem_coarseLattice hdvd hy μ),
      coarseRestrictSite_siteLift hell _ hy, hgc ⟨y, hy⟩ μ]
    have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
    field_simp

/-! ## §6. The gauge correction, and `[UPPER-DEGENERATE]` -/

/-- **The faithful-levels hypothesis**, discharged from `(ell, Finset.univ) ∈ levels` — Bałaban's
own `N(Q_k')` at the coarse-graining scale (CMP96 (2.7)/(2.10)). -/
theorem faithfulLevels_hlev {levels : List (Level L)} (hmem : (ell, Finset.univ) ∈ levels)
    (lam : PeriodicLatticeSite L → ℝ) (hlam : lam ∈ kernelSubspace levels)
    (y : PeriodicLatticeSite L) : coarseRestrictSite ell lam y = 0 :=
  (mem_kernelSubspace.mp hlam) (ell, Finset.univ) hmem y (Finset.mem_univ y)

/-- A `N(Q')`-gradient is in `ker Q_k` — **the step that spends the faithful-levels hypothesis**,
via CMP95 (1.20) (`lineCoarseRestrict_gradValue`). -/
theorem lineCoarseRestrictCLM_gradCLM_eq_zero (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (lam : SiteSpace L)
    (hlam : ∀ y : PeriodicLatticeSite L, coarseRestrictSite ell (siteEquiv L lam) y = 0) :
    lineCoarseRestrictCLM L ell (gradCLM L lam) = 0 := by
  apply (coarseBondEquiv L ell).injective
  rw [lineCoarseRestrictCLM_apply, gradCLM_apply, map_zero]
  funext b
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  rw [lineCoarseRestrict_gradValue hell (hdvd μ) hy, hlam, hlam]
  simp

/-- **`[UPPER-DEGENERATE]`, PROVED under the faithful-levels hypothesis.** If the coarse curl of
`Q_kA0` vanishes then `∂₁A0` lies in `∂₁V` — so `HjMinimizer.deltaJQuadForm` vanishes. -/
theorem exists_gaugeConstraint_with_same_curl (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (levels : List (Level L))
    (hlev : ∀ lam ∈ kernelSubspace levels, ∀ y : PeriodicLatticeSite L,
      coarseRestrictSite ell lam y = 0)
    (A0 : BondSpace L)
    (hflat : coarseCurlCLM L ell hdvd (lineCoarseRestrictCLM L ell A0) = 0) :
    ∃ v ∈ gaugeConstraintSubspace ell levels, curlCLM L v = curlCLM L A0 := by
  obtain ⟨A1, hA1curl, hA1Q⟩ := exists_flat_with_same_Q hell hdvd A0 hflat
  -- the residual gauge defect lives in the range of `R`, hence is `Δ₀` of an `N(Q')` element
  set r : SiteSpace L := RProj levels ((gradCLM L).adjoint (A0 - A1)) with hr
  have hrmem : r ∈ deltaKernelImage levels := RProj_apply_mem levels _
  obtain ⟨lam, hlamMem, hlamEq⟩ := Submodule.mem_map.mp hrmem
  have hlamQ : ∀ y : PeriodicLatticeSite L, coarseRestrictSite ell (siteEquiv L lam) y = 0 :=
    hlev _ (mem_kernelSubspaceH.mp hlamMem)
  have hDelta : (gradCLM L).adjoint (gradCLM L lam) = r := hlamEq
  refine ⟨A0 - A1 - gradCLM L lam, ?_, ?_⟩
  · rw [mem_gaugeConstraintSubspace]
    constructor
    · rw [map_sub, map_sub, hA1Q, sub_self, zero_sub,
        lineCoarseRestrictCLM_gradCLM_eq_zero hell hdvd lam hlamQ, neg_zero]
    · rw [map_sub, map_sub, hDelta, ← hr]
      have hfix : RProj levels r = r :=
        Submodule.starProjection_eq_self_iff.mpr hrmem
      rw [hfix, sub_self]
  · rw [map_sub, map_sub, hA1curl, sub_zero]
    rw [curlCLM_gradCLM, sub_zero]

end AdalyFormal.Balaban.U1AnchorCoarse
