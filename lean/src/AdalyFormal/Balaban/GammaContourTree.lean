/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.KappaBound
import AdalyFormal.Balaban.RegularUCurvedWitness

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-!
# `GammaContourTree.lean` — `Γ_{y,x}` WRITTEN DOWN, and `KappaBound`'s last hypothesis DISCHARGED

Lane record: `compute/gamma_denotation/PROGRESS.md`. Denotation authority:
`compute/gamma_denotation/CMP95_P18_READ.md` (the main loop's first-hand read of the 400 dpi render
`corpus/renders/CMP95_p18-02.png`, sha256
`51043df7a971ec51865c32c871aaf888e124a594ef1806739cbf6b7f8ccffeb9`).

## §0 — THE SOURCE, quoted

CMP95 printed p.18 (1.6), the block:

```
B(y) = {x ∈ T₁ : y_μ ≦ x_μ < y_μ + L, μ = 1, …, d},  y ∈ T_L^{(1)}
```

CMP95 printed p.18 (1.7), the contour:

```
Γ_{y,x} = [y, (y₁,…,y_{d−1},x_d)] ∪ … ∪ [(y₁,…,y_μ,x_{μ+1},…,x_d), (y₁,…,x_μ,x_{μ+1},…,x_d)]
          ∪ … ∪ [(y₁,x₂,…,x_d), x]
```

with the prose immediately below: *"where `[x₁,x₂]` is a line segment connecting points `x₁,x₂`. We
consider `Γ_{y,x}`, and all other contours appearing in the paper, as oriented contours, with
initial point `y` and final point `x`."*

**The denotation this pins.** The FIRST segment changes coordinate `d`; the generic segment changes
coordinate `μ` with `μ+1..d` already at `x` and `1..μ−1` still at `y`; the LAST segment changes
coordinate `1`. On the `d = 3` `Fin 3` carrier this is **index 2 first, then 1, then 0** —
DESCENDING axis order, walked from `y`.

## §0a — INVENTORY FIRST (`compute/BUILD_STANDARDS.md` §READ-FIRST), and what it found

FIVE staircase objects already existed in this tree. Their axis orders were read off their own
definitions, not from memory or from their docstrings:

1. **`AdmissibleSubspace.staircasePath`** (`AdmissibleSubspace.lean` §3) —
   `axisSegment y 2 … ∪ axisSegment (corner1 y x) 1 … ∪ axisSegment (corner2 y x) 0 …` with
   `corner1 y x = Function.update y 2 (x 2)` and `corner2 y x = Function.update (corner1 y x) 1
   (x 1)`. Coordinate `2` first, then `1`, then `0`. **DESCENDING — matches CMP95 (1.7).** Its own
   docstring records that it was derived from CMP96 p.244's telescoping argument and that an
   earlier revision of this tree had it backwards.
2. **`Q1Real.GammaPath`** — `straightSegment y x 2 ++ straightSegment (update y 2 (x 2)) x 1 ++
   straightSegment (update (update y 2 (x 2)) 1 (x 1)) x 0`. **DESCENDING**, and its docstring
   already says *"image-verified against CMP95 p.18"*.
3. **`TowerLawCovariant.coarseGammaPath`** — the same `Function.update` chain at coarse stride.
   **DESCENDING**, docstring cites CMP95 (1.7) explicitly.
4. **`AdmissibleSubspace.foilStaircasePath`** — the same construction in ASCENDING order (`0`, then
   `1`, then `2`), retained in-tree under a name that no longer claims to be `Γ_{y,x}`.
5. **`KappaBound.treeBondsTwo`** (`KappaBound.lean` §8a) — its own docstring says *"in the
   coordinate order `0 → 1 → 2`"*. Its seven bonds are
   `(y,2), (y,1), (s₁y,2), (y,0), (s₀y,2), (s₀y,1), (s₁s₀y,2)` — direction-`2` bonds at FOUR
   different tails and a single direction-`0` bond, the exact mirror image of the (1.7) pattern
   under the coordinate swap `0 ↔ 2`. **ASCENDING, not (1.7)'s.**

So three independent objects in this tree already denote (1.7) and agree with the page image; the
one that disagreed is `KappaBound`'s `ell = 2` bond list, which is not the tree's `Γ` object but a
bond list local to that file. This module builds the (1.7) bond set `gammaTreeBondsTwo` and
**proves it equals `⋃_{x∈B(y)} staircasePath y x`** (§4a,
`gammaTreeBondsTwo_eq_biUnion_staircasePath`), so the denotation is a kernel theorem, not a
docstring. `treeBondsTwo` is NOT redefined, NOT deleted and NOT edited; §7 proves the two bond sets
are DIFFERENT Finsets (`gammaTreeBondsTwo_ne_treeBondsTwo`) and, sharply,
`treeBondsTwo_bond_off_every_gamma_contour` exhibits a bond of `treeBondsTwo y` lying on NO (1.7)
contour of the block.

**Disclosed duplication (LAW-19), stated as fact.** `gammaTransport` is a NEW object: items 2 and 3
above are `List (Fin 3)`-valued PATHS with their own holonomy functions, not `ell = 2` corner-indexed
ordered products, and the prefix factorisation `Γ_{y,x} = Γ_{y,x′}·U_b` that
`KappaBound.transport_step_norm_eq` consumes is immediate for the corner-indexed form and would need
an append lemma for the list form. Reusing `Q1Real.GammaPath` would have required an extra module
import and a bridging theorem for no change in the result. This module does NOT prove
`gammaTransport = periodicPathHolonomy ∘ Q1Real.GammaPath`; the anchor it does prove is to
`staircasePath` (bond set) and to `corner1`/`corner2` (intermediate points).

## §0b — THE CONSTANT IS ORDER-INDEPENDENT; THE DENOTATION IS NOT. Kept separate, deliberately.

`KappaBound.tree_poincare_ell_two` proves `Σ‖m‖² ≤ 8·Σ_{7 tree bonds}‖Δm‖²` for eight vectors
summing to zero on a tree of a fixed SHAPE (root with three children; one child having two children,
one of those having one child; another child having one child). The (1.7) tree and the foil tree are
isomorphic as abstract trees, so **the constant `8` is the same for both, and this module does not,
and must not, manufacture a difference in the constant.** §5 reuses `tree_poincare_ell_two` verbatim
through a relabelling written out in `gamma_block_poincare`'s proof.

The order IS load-bearing in exactly two places, and both are proved here rather than asserted:

* the **bond set** — which seven lattice bonds carry the right-hand side (§7,
  `gammaTreeBondsTwo_ne_treeBondsTwo`); and
* the **operator `Q′` itself** — `Q′λ(y)` averages `R(Γ_{y,x})λ(x)`, so a different contour order is
  a different `Q′` with a different kernel, hence a different hypothesis `hmean`. §7's
  `descending_ne_ascending_transport` exhibits a concrete background at which the (1.7) transport to
  the far corner and the ascending transport to the SAME corner are different group elements.

## §1 — WHAT THIS FILE PROVES

* `gCorner` / `gammaTransport` — the eight sites of `B(y)` at `ell = 2` and the eight (1.7)
  transports `Γ_{y,x}`, written down as ordered products of link variables in the source's order.
* `gammaTreeBondsTwo_eq_biUnion_staircasePath` — the seven-bond set IS `⋃_{x∈B(y)} Γ_{y,x}`.
* `corner1_gCorner` / `corner2_gCorner` — the two intermediate corners of `staircasePath y x` are
  exactly the two intermediate points of `gCorner`'s iterated-shift walk, so the two encodings of
  (1.7) agree pointwise and not merely in their bond sets.
* `gamma_block_poincare` — the per-block inequality that `KappaBound` carried as the hypothesis
  `hblock`, PROVED for the (1.7) tree, from `KappaBound.tree_poincare_ell_two` +
  `KappaBound.transport_step_norm_eq`. **Stated precisely, because the difference matters:**
  `KappaBound.poincare_assembly_two` hard-codes `treeBondsTwo`, i.e. the FOIL bond set, so its
  `hblock` is a statement about the foil tree and CANNOT be instantiated by the (1.7) tree. This
  module therefore routes through the GENERIC `KappaBound.poincare_assembly`, which takes the bond
  family `tb` as a parameter, and supplies `gammaTreeBondsTwo`. `poincare_assembly_two`'s own
  `hblock` is left exactly as it was — it has no Lean consumer (`grep`: no module imports
  `KappaBound`; `DeltaPrimeBound` mentions it only in prose).
* `gamma_poincare_assembly` — `siteEnergy λ ≤ 8·bondEnergy (D_Uλ)`, i.e. `hPoin` of
  `KappaBound.hlam_at_kappa_sq_768`, PROVED.
* `hlam_at_kappa_sq_768_gamma` — the composition: `siteEnergy λ ≤ 768·bondEnergy A`, i.e.
  `κ² ≤ 768`, `κ ≤ 16√3`, **with the Poincaré hypothesis discharged**.
* `QprimeTwo` — Bałaban's `Q′` at `ell = 2` with the (1.7) transport, as a LINEAR MAP, so that the
  remaining hypothesis is membership in `LinearMap.ker (QprimeTwo U)` rather than a bare equation;
  and `poincare_for_gaugeParam`, which chains `KappaBound.gaugeParam_mem_ker_and_solves` at that
  same operator straight into the Poincaré inequality.

## §1a — WHAT IS *NOT* CLOSED HERE, STATED AS FACT

* `hmean` (`Q′λ = 0`, in the explicit form "the eight (1.7)-transported values of `λ` on each
  `ell = 2` block sum to zero") remains a HYPOTHESIS on `λ`. It is not free data and not an
  existential the prover may instantiate: it is a property of the particular `λ` the caller
  supplies, and `KappaBound.gaugeParam_mem_ker_and_solves` is what supplies it for `λ = G′Rf`.
  §8 exhibits a CONCRETE lattice, background and NONZERO `λ` satisfying it with `siteEnergy λ > 0`.
* The `ell^{-d}` normalization of `Q′` is not carried: `hmean` is a bare sum, and the block average
  differs from it by the positive scalar `8⁻¹`, which does not change the vanishing condition.
  Recorded, not hidden.
* This module is `ell = 2`, `d = 3`. The general-`ell` (1.7) bond set is not built here.
-/

namespace AdalyFormal.Balaban.GammaContourTree

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.AlphaAnalyticity (norm_RMap)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)
open AdalyFormal.Balaban.GeneralUHodgeDrift (siteEnergy siteEnergy_nonneg)
open AdalyFormal.Balaban.AdmissibleSubspace
  (Bond blockOf mem_blockOf CoarseLattice coarseLattice_mem_fits card_blockOf staircasePath
   axisSegment mem_axisSegment corner1 corner2)

variable {L : PeriodicLatticeExtent}

/-! ## §2 — SITE BOOKKEEPING -/

/-- Two sites agree once all three coordinate VALUES agree. -/
theorem site_eq_of_val_eq {p q : PeriodicLatticeSite L}
    (h : ∀ μ : Fin 3, (p μ).val = (q μ).val) : p = q := by
  funext μ
  exact Fin.ext (h μ)

/-- Two sites agree once they agree off one axis and their values agree on it. -/
theorem site_eq_of_agree {z w : PeriodicLatticeSite L} (μ : Fin 3)
    (hoff : ∀ ν : Fin 3, ν ≠ μ → z ν = w ν) (hval : (z μ).val = (w μ).val) : z = w := by
  funext ν
  by_cases h : ν = μ
  · subst h; exact Fin.ext hval
  · exact hoff ν h

/-- `Function.update z μ (w μ) = w` when `z` and `w` already agree off `μ`. -/
theorem update_eq_of_agree {z w : PeriodicLatticeSite L} (μ : Fin 3)
    (hoff : ∀ ν : Fin 3, ν ≠ μ → z ν = w ν) : Function.update z μ (w μ) = w := by
  funext ν
  by_cases h : ν = μ
  · subst h; exact Function.update_self _ _ _
  · rw [Function.update_of_ne h, hoff ν h]

/-- One step along the axis being stepped, when it does not wrap. Reuse of
`KappaBound.shift_val_self` (LAW-19). -/
theorem sval (x : PeriodicLatticeSite L) (μ : Fin 3) (h : (x μ).val < L μ) :
    ((periodicLatticeShift x μ) μ).val = (x μ).val + 1 :=
  KappaBound.shift_val_self x μ h

/-- The other coordinates are untouched. Reuse of `KappaBound.shift_apply_ne` (LAW-19). -/
theorem sapp_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    periodicLatticeShift x μ ν = x ν :=
  KappaBound.shift_apply_ne x μ ν h

theorem sval_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    ((periodicLatticeShift x μ) ν).val = (x ν).val := by
  rw [sapp_ne x μ ν h]

/-! ## §3 — THE EIGHT SITES OF `B(y)` AT `ell = 2`, WALKED IN (1.7)'s ORDER

`gCorner y (a,b,c)` is the corner of `B(y)` at offset `a` along axis `0`, `b` along axis `1`, `c`
along axis `2`. It is written as an ITERATED SHIFT in (1.7)'s order — axis `2` innermost (taken
FIRST), then axis `1`, then axis `0` outermost (taken LAST) — so the definition itself is the walk
`y → (y₀,y₁,x₂) → (y₀,x₁,x₂) → x` that (1.7) displays. -/

/-- The inner two steps of the (1.7) walk: axis `2` first, then axis `1`. -/
def gInner (y : PeriodicLatticeSite L) : Bool → Bool → PeriodicLatticeSite L
  | false, false => y
  | false, true  => periodicLatticeShift y 2
  | true,  false => periodicLatticeShift y 1
  | true,  true  => periodicLatticeShift (periodicLatticeShift y 2) 1

/-- The axis-`1` step of the (1.7) walk really is a single shift of the axis-`2` intermediate
point. -/
theorem gInner_true (y : PeriodicLatticeSite L) (c : Bool) :
    gInner y true c = periodicLatticeShift (gInner y false c) 1 := by
  cases c <;> rfl

/-- **THE EIGHT CORNERS OF `B(y)`, `ell = 2`, IN (1.7)'s ORDER.** -/
def gCorner (y : PeriodicLatticeSite L) (p : Bool × Bool × Bool) : PeriodicLatticeSite L :=
  if p.1 then periodicLatticeShift (gInner y p.2.1 p.2.2) 0 else gInner y p.2.1 p.2.2

theorem gCorner_false (y : PeriodicLatticeSite L) (b c : Bool) :
    gCorner y (false, b, c) = gInner y b c := by
  simp [gCorner]

theorem gCorner_true (y : PeriodicLatticeSite L) (b c : Bool) :
    gCorner y (true, b, c) = periodicLatticeShift (gInner y b c) 0 := by
  simp [gCorner]

/-- The offset of corner `p` along axis `μ`, as a natural number in `{0,1}`. -/
def gOff (p : Bool × Bool × Bool) (μ : Fin 3) : ℕ :=
  if μ = 0 then (if p.1 then 1 else 0)
  else if μ = 1 then (if p.2.1 then 1 else 0)
  else (if p.2.2 then 1 else 0)

theorem gOff_le_one (p : Bool × Bool × Bool) (μ : Fin 3) : gOff p μ ≤ 1 := by
  unfold gOff
  split_ifs <;> omega

/-- `gInner y false c` — the point after the axis-`2` step — agrees with `y` off axis `2`. -/
theorem gInner_false_agree (y : PeriodicLatticeSite L) (c : Bool) :
    ∀ ν : Fin 3, ν ≠ 2 → gInner y false c ν = y ν := by
  intro ν hν
  cases c
  · rfl
  · exact sapp_ne y 2 ν hν

/-- `gInner y b c` agrees with `gInner y false c` off axis `1`. -/
theorem gInner_agree_one (y : PeriodicLatticeSite L) (b c : Bool) :
    ∀ ν : Fin 3, ν ≠ 1 → gInner y b c ν = gInner y false c ν := by
  intro ν hν
  cases b
  · rfl
  · rw [gInner_true y c]
    exact sapp_ne (gInner y false c) 1 ν hν

/-- `gCorner y (a,b,c)` agrees with `gInner y b c` off axis `0`. -/
theorem gCorner_agree_zero (y : PeriodicLatticeSite L) (a b c : Bool) :
    ∀ ν : Fin 3, ν ≠ 0 → gCorner y (a, b, c) ν = gInner y b c ν := by
  intro ν hν
  cases a
  · rw [gCorner_false]
  · rw [gCorner_true]
    exact sapp_ne (gInner y b c) 0 ν hν

theorem gInner_val0 (y : PeriodicLatticeSite L) (b c : Bool) :
    ((gInner y b c) 0).val = (y 0).val := by
  rw [gInner_agree_one y b c 0 (by decide), gInner_false_agree y c 0 (by decide)]

theorem gInner_val1 (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (b c : Bool) : ((gInner y b c) 1).val = (y 1).val + (if b then 1 else 0) := by
  have hbase : ((gInner y false c) 1).val = (y 1).val := by
    rw [gInner_false_agree y c 1 (by decide)]
  cases b
  · simpa using hbase
  · rw [gInner_true y c, sval (gInner y false c) 1 (by rw [hbase]; exact hlt 1), hbase]
    simp

theorem gInner_val2 (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (b c : Bool) : ((gInner y b c) 2).val = (y 2).val + (if c then 1 else 0) := by
  have hbase : ((gInner y false c) 2).val = (y 2).val + (if c then 1 else 0) := by
    cases c
    · simp only [if_neg (by decide : ¬ (false = true))]
      rfl
    · show ((periodicLatticeShift y 2) 2).val = (y 2).val + (if true then 1 else 0)
      rw [sval y 2 (hlt 2)]
      simp
  rw [gInner_agree_one y b c 2 (by decide)]
  exact hbase

/-- **THE COORDINATE PROFILE OF EVERY CORNER.** -/
theorem gCorner_val (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (p : Bool × Bool × Bool) (μ : Fin 3) :
    ((gCorner y p) μ).val = (y μ).val + gOff p μ := by
  obtain ⟨a, b, c⟩ := p
  have hin0 : ((gInner y b c) 0).val < L 0 := by
    rw [gInner_val0 y b c]; exact hlt 0
  have h0 : ((gCorner y (a, b, c)) 0).val = (y 0).val + (if a then 1 else 0) := by
    cases a
    · rw [gCorner_false, gInner_val0]; simp
    · rw [gCorner_true, sval (gInner y b c) 0 hin0, gInner_val0]; simp
  have h1 : ((gCorner y (a, b, c)) 1).val = (y 1).val + (if b then 1 else 0) := by
    rw [gCorner_agree_zero y a b c 1 (by decide), gInner_val1 y hlt b c]
  have h2 : ((gCorner y (a, b, c)) 2).val = (y 2).val + (if c then 1 else 0) := by
    rw [gCorner_agree_zero y a b c 2 (by decide), gInner_val2 y hlt b c]
  have hoff : gOff (a, b, c) μ = if μ = 0 then (if a then 1 else 0)
      else if μ = 1 then (if b then 1 else 0) else (if c then 1 else 0) := rfl
  rw [hoff]
  by_cases e0 : μ = 0
  · subst e0; rw [if_pos rfl]; exact h0
  · by_cases e1 : μ = 1
    · subst e1; rw [if_neg e0, if_pos rfl]; exact h1
    · have e2 : μ = 2 := by
        have hv0 : μ.val ≠ 0 := fun h => e0 (Fin.ext h)
        have hv1 : μ.val ≠ 1 := fun h => e1 (Fin.ext h)
        have hlt3 := μ.isLt
        have h2v : ((2 : Fin 3)).val = 2 := rfl
        exact Fin.ext (by omega)
      subst e2; rw [if_neg e0, if_neg e1]; exact h2

/-- Every corner lies in the block. -/
theorem gCorner_mem_block (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (p : Bool × Bool × Bool) : gCorner y p ∈ blockOf y 2 := by
  rw [mem_blockOf]
  intro ν
  have h := gCorner_val y hlt p ν
  have h2 := gOff_le_one p ν
  omega

/-- **`B(y)` IS EXACTLY THE EIGHT CORNERS.** -/
theorem blockOf_two_eq_image (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ) :
    blockOf y 2 = Finset.image (gCorner y) (Finset.univ : Finset (Bool × Bool × Bool)) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rw [mem_blockOf] at hx
    refine ⟨(decide ((y 0).val < (x 0).val), decide ((y 1).val < (x 1).val),
             decide ((y 2).val < (x 2).val)), ?_⟩
    refine site_eq_of_val_eq (fun μ => ?_)
    rw [gCorner_val y hlt _ μ]
    have hg : gOff (decide ((y 0).val < (x 0).val), decide ((y 1).val < (x 1).val),
        decide ((y 2).val < (x 2).val)) μ
        = (if (y μ).val < (x μ).val then 1 else 0) := by
      unfold gOff
      fin_cases μ <;> simp
    rw [hg]
    have hμ := hx μ
    split_ifs with h <;> omega
  · rintro ⟨p, rfl⟩
    exact gCorner_mem_block y hlt p

/-- The eight corners are DISTINCT — obtained from the block's own cardinality law
(`AdmissibleSubspace.card_blockOf`, reused not rebuilt), not from twenty-eight hand disequalities. -/
theorem gCorner_injOn (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ) :
    Set.InjOn (gCorner y) ↑(Finset.univ : Finset (Bool × Bool × Bool)) := by
  have hfit : ∀ μ : Fin 3, (y μ).val + 2 ≤ L μ + 1 := by
    intro μ; have := hlt μ; omega
  have hcard : (Finset.image (gCorner y) (Finset.univ : Finset (Bool × Bool × Bool))).card
      = (Finset.univ : Finset (Bool × Bool × Bool)).card := by
    rw [← blockOf_two_eq_image y hlt, card_blockOf y 2 hfit]
    simp
  exact Finset.card_image_iff.mp hcard

theorem gCorner_inj (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    {p q : Bool × Bool × Bool} (h : gCorner y p = gCorner y q) : p = q :=
  gCorner_injOn y hlt (by simp) (by simp) h

/-- Summing any function over `B(y)` is summing it over the eight corners. -/
theorem sum_block_eq (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (F : PeriodicLatticeSite L → ℝ) :
    ∑ x ∈ blockOf y 2, F x = ∑ p : Bool × Bool × Bool, F (gCorner y p) := by
  rw [blockOf_two_eq_image y hlt,
    Finset.sum_image (fun p _ q _ h => gCorner_inj y hlt h)]

/-- The eight-term expansion of a sum over `Bool × Bool × Bool`. -/
theorem sum_bool3 {M : Type*} [AddCommGroup M] (G : Bool × Bool × Bool → M) :
    ∑ p : Bool × Bool × Bool, G p =
      G (false, false, false) + G (true, false, false) + G (false, true, false)
        + G (true, true, false) + G (false, false, true) + G (true, false, true)
        + G (false, true, true) + G (true, true, true) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  abel

/-! ## §4 — `gammaTreeBondsTwo` — THE SEVEN BONDS OF `⋃_{x∈B(y)} Γ_{y,x}` -/

/-- **THE SEVEN (1.7) TREE BONDS** of the `ell = 2` block at `y`: direction `2` from `y`;
direction `1` from `y` and from `y+e₂`; direction `0` from `y`, `y+e₂`, `y+e₁` and `y+e₂+e₁`. -/
def gammaTreeBondsTwo (y : PeriodicLatticeSite L) : Finset (Bond L) :=
  {(y, (2 : Fin 3)), (y, (1 : Fin 3)), (periodicLatticeShift y 2, (1 : Fin 3)),
   (y, (0 : Fin 3)), (periodicLatticeShift y 2, (0 : Fin 3)),
   (periodicLatticeShift y 1, (0 : Fin 3)),
   (periodicLatticeShift (periodicLatticeShift y 2) 1, (0 : Fin 3))}

/-- The four distinct tails appearing in `gammaTreeBondsTwo` are corners of the block, so the
disequalities needed to expand its seven-term sum come from `gCorner_inj`. -/
theorem gammaTails_ne (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ) :
    y ≠ periodicLatticeShift y 2 ∧ y ≠ periodicLatticeShift y 1
      ∧ y ≠ periodicLatticeShift (periodicLatticeShift y 2) 1
      ∧ periodicLatticeShift y 2 ≠ periodicLatticeShift y 1
      ∧ periodicLatticeShift y 2 ≠ periodicLatticeShift (periodicLatticeShift y 2) 1
      ∧ periodicLatticeShift y 1 ≠ periodicLatticeShift (periodicLatticeShift y 2) 1 := by
  have e0 : gCorner y (false, false, false) = y := rfl
  have e2 : gCorner y (false, false, true) = periodicLatticeShift y 2 := rfl
  have e1 : gCorner y (false, true, false) = periodicLatticeShift y 1 := rfl
  have e12 : gCorner y (false, true, true)
      = periodicLatticeShift (periodicLatticeShift y 2) 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
  · exact absurd (gCorner_inj y hlt (e0.trans (h.trans e2.symm))) (by decide)
  · exact absurd (gCorner_inj y hlt (e0.trans (h.trans e1.symm))) (by decide)
  · exact absurd (gCorner_inj y hlt (e0.trans (h.trans e12.symm))) (by decide)
  · exact absurd (gCorner_inj y hlt (e2.trans (h.trans e1.symm))) (by decide)
  · exact absurd (gCorner_inj y hlt (e2.trans (h.trans e12.symm))) (by decide)
  · exact absurd (gCorner_inj y hlt (e1.trans (h.trans e12.symm))) (by decide)

/-- Expansion of the seven-bond sum. -/
theorem sum_gammaTreeBondsTwo (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (H : Bond L → ℝ) :
    ∑ b ∈ gammaTreeBondsTwo y, H b =
      H (y, 2) + H (y, 1) + H (periodicLatticeShift y 2, 1) + H (y, 0)
        + H (periodicLatticeShift y 2, 0) + H (periodicLatticeShift y 1, 0)
        + H (periodicLatticeShift (periodicLatticeShift y 2) 1, 0) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := gammaTails_ne y hlt
  unfold gammaTreeBondsTwo
  rw [Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff, h01]),
    Finset.sum_insert (by simp [Prod.ext_iff]),
    Finset.sum_insert (by simp [Prod.ext_iff, h01, h02, h03]),
    Finset.sum_insert (by simp [Prod.ext_iff, h12, h13]),
    Finset.sum_insert (by simp [Prod.ext_iff, h23]), Finset.sum_singleton]
  ring

/-! ### §4a — THE DENOTATION ANCHOR

`gammaTreeBondsTwo y = ⋃_{x ∈ B(y)} Γ_{y,x}`, with `Γ` the tree's own `staircasePath` — the object
whose axis order (`2`, then `1`, then `0`) is the one CMP95 (1.7) displays. -/

theorem corner1_apply_ne (y x : PeriodicLatticeSite L) (ν : Fin 3) (h : ν ≠ 2) :
    corner1 y x ν = y ν := Function.update_of_ne h _ _

/-- **The axis-`2` corner of `staircasePath y x` IS the first point of the (1.7) walk.** -/
theorem corner1_gCorner (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (p : Bool × Bool × Bool) :
    corner1 y (gCorner y p) = gInner y false p.2.2 := by
  obtain ⟨a, b, c⟩ := p
  have hval : ((gCorner y (a, b, c)) 2).val = ((gInner y false c) 2).val := by
    rw [gCorner_val y hlt _ 2, gInner_val2 y hlt false c]
    rfl
  have hpt : (gCorner y (a, b, c)) 2 = (gInner y false c) 2 := Fin.ext hval
  show Function.update y 2 ((gCorner y (a, b, c)) 2) = gInner y false c
  rw [hpt]
  exact update_eq_of_agree 2 (fun ν hν => (gInner_false_agree y c ν hν).symm)

/-- **The axis-`1` corner of `staircasePath y x` IS the second point of the (1.7) walk.** -/
theorem corner2_gCorner (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (p : Bool × Bool × Bool) :
    corner2 y (gCorner y p) = gInner y p.2.1 p.2.2 := by
  obtain ⟨a, b, c⟩ := p
  have hval : ((gCorner y (a, b, c)) 1).val = ((gInner y b c) 1).val := by
    rw [gCorner_val y hlt _ 1, gInner_val1 y hlt b c]
    rfl
  have hpt : (gCorner y (a, b, c)) 1 = (gInner y b c) 1 := Fin.ext hval
  show Function.update (corner1 y (gCorner y (a, b, c))) 1 ((gCorner y (a, b, c)) 1)
      = gInner y b c
  rw [corner1_gCorner y hlt (a, b, c), hpt]
  exact update_eq_of_agree 1 (fun ν hν => (gInner_agree_one y b c ν hν).symm)

theorem min_max_gCorner (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (p : Bool × Bool × Bool) (μ : Fin 3) :
    min (y μ).val ((gCorner y p) μ).val = (y μ).val
      ∧ max (y μ).val ((gCorner y p) μ).val = (y μ).val + gOff p μ := by
  have h := gCorner_val y hlt p μ
  constructor
  · omega
  · omega

/-- **THE ANCHOR.** The seven named bonds are EXACTLY the union of the (1.7) contours over the
block. -/
theorem gammaTreeBondsTwo_eq_biUnion_staircasePath
    (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ) :
    gammaTreeBondsTwo y = (blockOf y 2).biUnion (staircasePath y) := by
  ext e
  simp only [Finset.mem_biUnion]
  constructor
  · intro he
    simp only [gammaTreeBondsTwo, Finset.mem_insert, Finset.mem_singleton] at he
    -- for each named bond, name the corner whose contour carries it
    have seg2 : ∀ p : Bool × Bool × Bool, p.2.2 = true →
        ((y, (2 : Fin 3)) : Bond L) ∈ staircasePath y (gCorner y p) := by
      intro p hp
      have hv := gCorner_val y hlt p 2
      have hone : gOff p 2 = 1 := by unfold gOff; simp [hp]
      unfold staircasePath
      simp only [Finset.mem_union]
      left; left
      rw [mem_axisSegment]
      refine ⟨rfl, fun ν _ => rfl, ?_, ?_⟩
      · show min (y 2).val ((gCorner y p) 2).val ≤ (y 2).val
        omega
      · show (y 2).val < max (y 2).val ((gCorner y p) 2).val
        omega
    have seg1 : ∀ p : Bool × Bool × Bool, p.2.1 = true →
        ((gInner y false p.2.2, (1 : Fin 3)) : Bond L) ∈ staircasePath y (gCorner y p) := by
      intro p hp
      have hv := gCorner_val y hlt p 1
      have hone : gOff p 1 = 1 := by unfold gOff; simp [hp]
      have hb : ((gInner y false p.2.2) 1).val = (y 1).val := by
        rw [gInner_false_agree y p.2.2 1 (by decide)]
      unfold staircasePath
      simp only [Finset.mem_union]
      left; right
      rw [mem_axisSegment, corner1_gCorner y hlt p]
      refine ⟨rfl, fun ν _ => rfl, ?_, ?_⟩
      · show min (y 1).val ((gCorner y p) 1).val ≤ ((gInner y false p.2.2) 1).val
        omega
      · show ((gInner y false p.2.2) 1).val < max (y 1).val ((gCorner y p) 1).val
        omega
    have seg0 : ∀ p : Bool × Bool × Bool, p.1 = true →
        ((gInner y p.2.1 p.2.2, (0 : Fin 3)) : Bond L) ∈ staircasePath y (gCorner y p) := by
      intro p hp
      have hv := gCorner_val y hlt p 0
      have hone : gOff p 0 = 1 := by unfold gOff; simp [hp]
      have hb : ((gInner y p.2.1 p.2.2) 0).val = (y 0).val := gInner_val0 y p.2.1 p.2.2
      unfold staircasePath
      simp only [Finset.mem_union]
      right
      rw [mem_axisSegment, corner2_gCorner y hlt p]
      refine ⟨rfl, fun ν _ => rfl, ?_, ?_⟩
      · show min (y 0).val ((gCorner y p) 0).val ≤ ((gInner y p.2.1 p.2.2) 0).val
        omega
      · show ((gInner y p.2.1 p.2.2) 0).val < max (y 0).val ((gCorner y p) 0).val
        omega
    rcases he with h | h | h | h | h | h | h <;> subst h
    · exact ⟨gCorner y (false, false, true), gCorner_mem_block y hlt _,
        seg2 (false, false, true) rfl⟩
    · exact ⟨gCorner y (false, true, false), gCorner_mem_block y hlt _,
        seg1 (false, true, false) rfl⟩
    · exact ⟨gCorner y (false, true, true), gCorner_mem_block y hlt _,
        seg1 (false, true, true) rfl⟩
    · exact ⟨gCorner y (true, false, false), gCorner_mem_block y hlt _,
        seg0 (true, false, false) rfl⟩
    · exact ⟨gCorner y (true, false, true), gCorner_mem_block y hlt _,
        seg0 (true, false, true) rfl⟩
    · exact ⟨gCorner y (true, true, false), gCorner_mem_block y hlt _,
        seg0 (true, true, false) rfl⟩
    · exact ⟨gCorner y (true, true, true), gCorner_mem_block y hlt _,
        seg0 (true, true, true) rfl⟩
  · rintro ⟨x, hx, hex⟩
    rw [blockOf_two_eq_image y hlt] at hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨hmin0, hmax0⟩ := min_max_gCorner y hlt p 0
    obtain ⟨hmin1, hmax1⟩ := min_max_gCorner y hlt p 1
    obtain ⟨hmin2, hmax2⟩ := min_max_gCorner y hlt p 2
    unfold staircasePath at hex
    simp only [Finset.mem_union] at hex
    simp only [gammaTreeBondsTwo, Finset.mem_insert, Finset.mem_singleton]
    rcases hex with (h2 | h1) | h0
    · -- axis-2 segment: forces `e = (y, 2)`
      rw [mem_axisSegment, hmin2, hmax2] at h2
      obtain ⟨hd, hoff, hlo, hhi⟩ := h2
      have hoff2 : gOff p 2 ≤ 1 := gOff_le_one p 2
      have hval : (e.1 2).val = (y 2).val := by omega
      have : e.1 = y := site_eq_of_agree 2 hoff hval
      left
      exact Prod.ext this hd
    · -- axis-1 segment: forces `e = (gInner y false c, 1)`
      rw [mem_axisSegment, hmin1, hmax1, corner1_gCorner y hlt p] at h1
      obtain ⟨hd, hoff, hlo, hhi⟩ := h1
      have hoff1 : gOff p 1 ≤ 1 := gOff_le_one p 1
      have hb : ((gInner y false p.2.2) 1).val = (y 1).val := by
        rw [gInner_false_agree y p.2.2 1 (by decide)]
      have hval : (e.1 1).val = ((gInner y false p.2.2) 1).val := by omega
      have hpt : e.1 = gInner y false p.2.2 := site_eq_of_agree 1 hoff hval
      have : e = ((gInner y false p.2.2, (1 : Fin 3)) : Bond L) := Prod.ext hpt hd
      rcases p with ⟨a, b, c⟩
      cases c
      · right; left; exact this
      · right; right; left; exact this
    · -- axis-0 segment: forces `e = (gInner y b c, 0)`
      rw [mem_axisSegment, hmin0, hmax0, corner2_gCorner y hlt p] at h0
      obtain ⟨hd, hoff, hlo, hhi⟩ := h0
      have hoff0 : gOff p 0 ≤ 1 := gOff_le_one p 0
      have hb : ((gInner y p.2.1 p.2.2) 0).val = (y 0).val := gInner_val0 y p.2.1 p.2.2
      have hval : (e.1 0).val = ((gInner y p.2.1 p.2.2) 0).val := by omega
      have hpt : e.1 = gInner y p.2.1 p.2.2 := site_eq_of_agree 0 hoff hval
      have hE : e = ((gInner y p.2.1 p.2.2, (0 : Fin 3)) : Bond L) := Prod.ext hpt hd
      rcases p with ⟨a, b, c⟩
      cases b <;> cases c
      · right; right; right; left; exact hE
      · right; right; right; right; left; exact hE
      · right; right; right; right; right; left; exact hE
      · right; right; right; right; right; right; exact hE

/-! ## §5 — THE (1.7) TRANSPORTS AND THE PER-BLOCK POINCARÉ INEQUALITY -/

/-- **`Γ_{y,x}` AS A GROUP ELEMENT** — the ordered product of link variables along the (1.7) walk,
axis `2` first and axis `0` last. `gammaTransport U y (false,false,false) = 1` is the DEGENERATE
`y = x` contour: the empty path, transport the identity. -/
noncomputable def gammaTransport
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) :
    Bool × Bool × Bool → Matrix.specialUnitaryGroup (Fin 2) ℂ
  | (false, false, false) => 1
  | (false, false, true)  => U (y, 2)
  | (false, true,  false) => U (y, 1)
  | (true,  false, false) => U (y, 0)
  | (false, true,  true)  => U (y, 2) * U (periodicLatticeShift y 2, 1)
  | (true,  false, true)  => U (y, 2) * U (periodicLatticeShift y 2, 0)
  | (true,  true,  false) => U (y, 1) * U (periodicLatticeShift y 1, 0)
  | (true,  true,  true)  =>
      U (y, 2) * U (periodicLatticeShift y 2, 1)
        * U (periodicLatticeShift (periodicLatticeShift y 2) 1, 0)

/-- The transported value of `λ` at the corner `p` of `B(y)` — the summand of Bałaban's `Q′`. -/
noncomputable def gammaM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L)
    (p : Bool × Bool × Bool) : SuTwo :=
  RMap (gammaTransport U y p) (lam (gCorner y p))

/-- **MUST-NOT-FIRE, degenerate contour.** At `x = y` the (1.7) contour is EMPTY and its transport
is the identity, so the transported value is `λ(y)` itself. -/
theorem gammaM_root (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    gammaM U lam y (false, false, false) = lam y := by
  show RMap 1 (lam y) = lam y
  rw [RMap_one]
  rfl

/-- Transport is an isometry, so the transported values have the same norms as `λ`'s. -/
theorem norm_gammaM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L)
    (p : Bool × Bool × Bool) : ‖gammaM U lam y p‖ = ‖lam (gCorner y p)‖ :=
  norm_RMap _ _

section Steps

variable (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
  (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L)

/-- Tree bond `(y,2)`: root → axis-`2` child. -/
theorem step_y2 : ‖gammaM U lam y (false, false, true) - gammaM U lam y (false, false, false)‖
    = ‖gradValueCovariant U lam (y, 2)‖ := by
  have h := KappaBound.transport_step_norm_eq U lam 1 y 2
  rw [one_mul] at h
  exact h

/-- Tree bond `(y,1)`: root → axis-`1` child. -/
theorem step_y1 : ‖gammaM U lam y (false, true, false) - gammaM U lam y (false, false, false)‖
    = ‖gradValueCovariant U lam (y, 1)‖ := by
  have h := KappaBound.transport_step_norm_eq U lam 1 y 1
  rw [one_mul] at h
  exact h

/-- Tree bond `(y,0)`: root → axis-`0` child. -/
theorem step_y0 : ‖gammaM U lam y (true, false, false) - gammaM U lam y (false, false, false)‖
    = ‖gradValueCovariant U lam (y, 0)‖ := by
  have h := KappaBound.transport_step_norm_eq U lam 1 y 0
  rw [one_mul] at h
  exact h

/-- Tree bond `(y+e₂, 1)`. -/
theorem step_s2_1 : ‖gammaM U lam y (false, true, true) - gammaM U lam y (false, false, true)‖
    = ‖gradValueCovariant U lam (periodicLatticeShift y 2, 1)‖ :=
  KappaBound.transport_step_norm_eq U lam (U (y, 2)) (periodicLatticeShift y 2) 1

/-- Tree bond `(y+e₂, 0)`. -/
theorem step_s2_0 : ‖gammaM U lam y (true, false, true) - gammaM U lam y (false, false, true)‖
    = ‖gradValueCovariant U lam (periodicLatticeShift y 2, 0)‖ :=
  KappaBound.transport_step_norm_eq U lam (U (y, 2)) (periodicLatticeShift y 2) 0

/-- Tree bond `(y+e₁, 0)`. -/
theorem step_s1_0 : ‖gammaM U lam y (true, true, false) - gammaM U lam y (false, true, false)‖
    = ‖gradValueCovariant U lam (periodicLatticeShift y 1, 0)‖ :=
  KappaBound.transport_step_norm_eq U lam (U (y, 1)) (periodicLatticeShift y 1) 0

/-- Tree bond `(y+e₂+e₁, 0)` — the deepest bond of the (1.7) tree. -/
theorem step_s12_0 : ‖gammaM U lam y (true, true, true) - gammaM U lam y (false, true, true)‖
    = ‖gradValueCovariant U lam (periodicLatticeShift (periodicLatticeShift y 2) 1, 0)‖ :=
  KappaBound.transport_step_norm_eq U lam (U (y, 2) * U (periodicLatticeShift y 2, 1))
    (periodicLatticeShift (periodicLatticeShift y 2) 1) 0

end Steps

/-- **`hblock` OF `KappaBound.poincare_assembly_two`, PROVED FOR THE (1.7) TREE.**

`hmean` is `Q′λ(y) = 0` written out: the eight `Γ_{y,x}`-transported values of `λ` on the block sum
to zero. The constant is `KappaBound.tree_poincare_ell_two`'s `8`, reused verbatim through the
relabelling

    m000 ↦ (f,f,f)   m001 ↦ (t,f,f)   m010 ↦ (f,t,f)   m011 ↦ (t,t,f)
    m100 ↦ (f,f,t)   m101 ↦ (t,f,t)   m110 ↦ (f,t,t)   m111 ↦ (t,t,t)

under which that lemma's seven tree edges become exactly the seven (1.7) bonds.

Note the two sides are the same seven summands in DIFFERENT orders — `sum_gammaTreeBondsTwo`
lists the bonds by direction (`2`, then the two `1`s, then the four `0`s), `tree_poincare_ell_two`
lists them by its own vertex labelling — so the last step is a linear rearrangement. -/
theorem gamma_block_poincare
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L)
    (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (hmean : ∑ p : Bool × Bool × Bool, gammaM U lam y p = 0) :
    ∑ x ∈ blockOf y 2, ‖lam x‖ ^ 2
      ≤ 8 * ∑ b ∈ gammaTreeBondsTwo y, ‖gradValueCovariant U lam b‖ ^ 2 := by
  -- left-hand side: the block sum is the sum of the transported norms
  have hL : ∑ x ∈ blockOf y 2, ‖lam x‖ ^ 2
      = ‖gammaM U lam y (false, false, false)‖ ^ 2 + ‖gammaM U lam y (true, false, false)‖ ^ 2
        + ‖gammaM U lam y (false, true, false)‖ ^ 2 + ‖gammaM U lam y (true, true, false)‖ ^ 2
        + ‖gammaM U lam y (false, false, true)‖ ^ 2 + ‖gammaM U lam y (true, false, true)‖ ^ 2
        + ‖gammaM U lam y (false, true, true)‖ ^ 2 + ‖gammaM U lam y (true, true, true)‖ ^ 2 := by
    rw [sum_block_eq y hlt, sum_bool3 (fun p => ‖lam (gCorner y p)‖ ^ 2)]
    simp only [norm_gammaM]
  -- mean-zero, in the lemma's argument order
  have hmean' : gammaM U lam y (false, false, false) + gammaM U lam y (true, false, false)
      + gammaM U lam y (false, true, false) + gammaM U lam y (true, true, false)
      + gammaM U lam y (false, false, true) + gammaM U lam y (true, false, true)
      + gammaM U lam y (false, true, true) + gammaM U lam y (true, true, true) = 0 := by
    rw [← sum_bool3 (fun p => gammaM U lam y p)]
    exact hmean
  -- right-hand side: the seven named bonds, rewritten as tree differences
  have hR : ∑ b ∈ gammaTreeBondsTwo y, ‖gradValueCovariant U lam b‖ ^ 2
      = ‖gammaM U lam y (false, false, true) - gammaM U lam y (false, false, false)‖ ^ 2
        + ‖gammaM U lam y (false, true, false) - gammaM U lam y (false, false, false)‖ ^ 2
        + ‖gammaM U lam y (false, true, true) - gammaM U lam y (false, false, true)‖ ^ 2
        + ‖gammaM U lam y (true, false, false) - gammaM U lam y (false, false, false)‖ ^ 2
        + ‖gammaM U lam y (true, false, true) - gammaM U lam y (false, false, true)‖ ^ 2
        + ‖gammaM U lam y (true, true, false) - gammaM U lam y (false, true, false)‖ ^ 2
        + ‖gammaM U lam y (true, true, true) - gammaM U lam y (false, true, true)‖ ^ 2 := by
    rw [sum_gammaTreeBondsTwo y hlt (fun b => ‖gradValueCovariant U lam b‖ ^ 2),
      ← step_y2 U lam y, ← step_y1 U lam y, ← step_s2_1 U lam y, ← step_y0 U lam y,
      ← step_s2_0 U lam y, ← step_s1_0 U lam y, ← step_s12_0 U lam y]
  have key := KappaBound.tree_poincare_ell_two (E := SuTwo)
    (gammaM U lam y (false, false, false))
    (gammaM U lam y (true, false, false)) (gammaM U lam y (false, true, false))
    (gammaM U lam y (true, true, false)) (gammaM U lam y (false, false, true))
    (gammaM U lam y (true, false, true)) (gammaM U lam y (false, true, true))
    (gammaM U lam y (true, true, true)) hmean'
  rw [hL, hR]
  linarith [key]

/-! ## §6 — THE LATTICE ASSEMBLY AND THE UNCONDITIONAL `κ² ≤ 768` -/

/-- Every tail of a (1.7) tree bond of the block at `y` lies in that block. -/
theorem gammaTreeBondsTwo_tail_mem (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L 2) :
    ∀ b ∈ gammaTreeBondsTwo y, b.1 ∈ blockOf y 2 := by
  have hfits := coarseLattice_mem_fits hdvd hy
  have hlt : ∀ μ : Fin 3, (y μ).val < L μ := by
    intro μ; have := hfits μ; omega
  intro b hb
  simp only [gammaTreeBondsTwo, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with h | h | h | h | h | h | h <;> subst h
  · exact gCorner_mem_block y hlt (false, false, false)
  · exact gCorner_mem_block y hlt (false, false, false)
  · exact gCorner_mem_block y hlt (false, false, true)
  · exact gCorner_mem_block y hlt (false, false, false)
  · exact gCorner_mem_block y hlt (false, false, true)
  · exact gCorner_mem_block y hlt (false, true, false)
  · exact gCorner_mem_block y hlt (false, true, true)

/-- The per-block (1.7) bond sets of distinct coarse centres are disjoint. -/
theorem gammaTreeBondsTwo_pairwiseDisjoint (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    ((CoarseLattice L 2 : Finset (PeriodicLatticeSite L)) :
        Set (PeriodicLatticeSite L)).PairwiseDisjoint gammaTreeBondsTwo := by
  intro y hy y' hy' hne
  simp only [Function.onFun]
  refine Finset.disjoint_left.mpr (fun b hb hb' => hne ?_)
  exact AdalyFormal.Balaban.AdmissibleSubspace.coarseLattice_unique 2
    (Finset.mem_coe.mp hy) (Finset.mem_coe.mp hy')
    (gammaTreeBondsTwo_tail_mem hdvd (Finset.mem_coe.mp hy) b hb)
    (gammaTreeBondsTwo_tail_mem hdvd (Finset.mem_coe.mp hy') b hb')

/-- **`hPoin` OF `KappaBound.hlam_at_kappa_sq_768`, PROVED.** No block-Poincaré hypothesis is left:
the only input is `Q′λ = 0` on every coarse block, in the (1.7) transport. -/
theorem gamma_poincare_assembly
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hmean : ∀ y ∈ CoarseLattice L 2, ∑ p : Bool × Bool × Bool, gammaM U lam y p = 0) :
    siteEnergy lam ≤ 8 * bondEnergy (gradValueCovariant U lam) := by
  refine KappaBound.poincare_assembly lam (gradValueCovariant U lam) 2 (by norm_num) hdvd
    gammaTreeBondsTwo (gammaTreeBondsTwo_pairwiseDisjoint hdvd) ?_
  intro y hy
  have hfits := coarseLattice_mem_fits hdvd hy
  have hlt : ∀ μ : Fin 3, (y μ).val < L μ := by
    intro μ; have := hfits μ; omega
  exact gamma_block_poincare U lam y hlt (hmean y hy)

/-- **THE HEADLINE: `κ² ≤ 768`, i.e. `κ ≤ 16√3`, WITH THE POINCARÉ HYPOTHESIS DISCHARGED.**

The hypotheses that remain are exactly: the weak Euler–Lagrange identity `hweak` (which is
`KappaBound.gaugeParam_mem_ker_and_solves`'s `Δ(G′Rf) = Rf` paired against `λ`), the adjoint
RELATION `hadj` (an identity pinning `D_U^*A`, not a size assumption), the projection bound `hproj`
(`‖R‖ ≤ 1`, `KappaBound.norm_apply_le_of_selfadjoint_idempotent`), the kernel condition
`hmean` (`Q′λ = 0`, the defining property of `λ = G′Rf`), and the tileability condition
`∀ μ, 2 ∣ L μ + 1`. -/
theorem hlam_at_kappa_sq_768_gamma
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam src dstarA : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hmean : ∀ y ∈ CoarseLattice L 2, ∑ p : Bool × Bool × Bool, gammaM U lam y p = 0)
    (hweak : bondEnergy (gradValueCovariant U lam)
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner (gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA) :
    siteEnergy lam ≤ 768 * bondEnergy A :=
  KappaBound.hlam_at_kappa_sq_768 U lam src dstarA A hweak
    (gamma_poincare_assembly U lam hdvd hmean) hadj hproj

/-! ### §6a — `hmean` IS NOT A BARE HYPOTHESIS: it is membership in the kernel of a NAMED operator

`gamma_poincare_assembly` takes `hmean` as a per-block equation. That is the same thing as membership
in the kernel of Bałaban's `Q′` — built here at `ell = 2` with CMP95 (1.7)'s transport — and
`KappaBound.gaugeParam_mem_ker_and_solves` delivers exactly that shape (`Q x = 0`) for `λ = G′Rf`.
This subsection closes the gap between `KappaBound` §2 and §6 by exhibiting the SAME operator in
both. -/

/-- **`Q′` AT `ell = 2`, WRITTEN DOWN AS A LINEAR MAP.** `(Q′λ)(y) = ∑_{x ∈ B(y)} R(Γ_{y,x})λ(x)`,
with `Γ` CMP95 (1.7)'s contour.

**S75 CORRECTION (2026-08-01, qprime_denotation lane).** Two claims in the original docstring were
wrong; both are struck and kept:

~~"The `ell^{-d}` prefactor of CMP95 (1.8)/(1.11) is omitted"~~ — (1.8)/(1.11) are the UNPRIMED
bond-sector `Q` acting on `A`, printed with `L^{-(d+1)}`. The printed `Q′` on gauge parameters is
CMP95 (1.13) and CMP99b p.393 (the untagged middle line of the (3.18)/(3.19) display; render
`corpus/renders/CMP99b_p393-05.png`), prefactor `L^{-d}`. The omission IS kernel-inert, but that is
now a theorem, not this docstring's assertion: `QPrimeDenotation.mem_ker_QprimeBalaban_iff`.

~~"it is the condition CMP99b's `N(Q′)` states"~~ — FALSE. The printed `Q′` imposes its condition
only on the coarse union `𝔅`, not at every site; this definition's kernel is STRICTLY smaller:
`QPrimeDenotation.ker_QprimeTwo_lt_ker_QprimeBalaban` (explicit witness), generalized to every
background and every extent with ≥ 4 sites per axis in
`QPrimeDenotation.ker_QprimeTwo_lt_ker_QprimeBalaban_general`. The source-faithful operator is
`CovarianceG1.QMap` (as `QPrimeDenotation.QprimeBalaban`), and the `hmean` discharge for the κ
headline is wired through THAT operator (`QPrimeDenotation.kappa_768_for_gaugeParam_qprime`) — not
through this one. This definition is retained only as the stronger every-site variant whose kernel
membership trivially supplies what `gamma_poincare_assembly` needs. -/
noncomputable def QprimeTwo
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo) where
  toFun lam := fun y => ∑ p : Bool × Bool × Bool, gammaM U lam y p
  map_add' lam1 lam2 := by
    funext y
    show (∑ p : Bool × Bool × Bool, gammaM U (lam1 + lam2) y p)
      = (∑ p : Bool × Bool × Bool, gammaM U lam1 y p)
        + ∑ p : Bool × Bool × Bool, gammaM U lam2 y p
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    show RMap (gammaTransport U y p) ((lam1 + lam2) (gCorner y p))
      = RMap (gammaTransport U y p) (lam1 (gCorner y p))
        + RMap (gammaTransport U y p) (lam2 (gCorner y p))
    rw [Pi.add_apply, map_add]
  map_smul' c lam := by
    funext y
    show (∑ p : Bool × Bool × Bool, gammaM U (c • lam) y p)
      = c • ∑ p : Bool × Bool × Bool, gammaM U lam y p
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    show RMap (gammaTransport U y p) ((c • lam) (gCorner y p))
      = c • RMap (gammaTransport U y p) (lam (gCorner y p))
    rw [Pi.smul_apply, map_smul]

theorem QprimeTwo_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    QprimeTwo U lam y = ∑ p : Bool × Bool × Bool, gammaM U lam y p := rfl

/-- **THE POINCARÉ INEQUALITY ON `N(Q′)`.** -/
theorem gamma_poincare_assembly_of_mem_ker
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hker : lam ∈ LinearMap.ker (QprimeTwo U)) :
    siteEnergy lam ≤ 8 * bondEnergy (gradValueCovariant U lam) := by
  refine gamma_poincare_assembly U lam hdvd (fun y _ => ?_)
  have h : QprimeTwo U lam = 0 := LinearMap.mem_ker.mp hker
  have hy := congrFun h y
  rw [QprimeTwo_apply] at hy
  exact hy

/-- **`KappaBound` §2's STRUCTURAL THEOREM, AT THIS OPERATOR.** `KappaBound
.gaugeParam_mem_ker_and_solves` is stated for an abstract `Q`; instantiated at `Q := QprimeTwo U` it
says that `λ = G′Rf` LIES IN `N(Q′)` — which is precisely the hypothesis
`gamma_poincare_assembly_of_mem_ker` consumes. The three hypotheses are CMP99b (3.24), the word
"inverse" on p.394, and (3.21), transcribed; none of them is new here. -/
theorem gaugeParam_mem_ker_QprimeTwo
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Δ M G R : (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo))
    (hM : ∀ x : PeriodicLatticeSite L → SuTwo, QprimeTwo U x = 0 → M x = 0)
    (hG : ∀ x : PeriodicLatticeSite L → SuTwo, G ((Δ + M) x) = x)
    (hR : LinearMap.range R = Submodule.map Δ (LinearMap.ker (QprimeTwo U)))
    (f : PeriodicLatticeSite L → SuTwo) :
    G (R f) ∈ LinearMap.ker (QprimeTwo U) ∧ Δ (G (R f)) = R f := by
  obtain ⟨h1, h2⟩ :=
    KappaBound.gaugeParam_mem_ker_and_solves (QprimeTwo U) Δ M G R hM hG hR f
  exact ⟨LinearMap.mem_ker.mpr h1, h2⟩

/-- **THE CHAIN, END TO END.** `λ = G′Rf` ⟹ `λ ∈ N(Q′)` ⟹ `siteEnergy λ ≤ 8·bondEnergy (D_Uλ)`. -/
theorem poincare_for_gaugeParam
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Δ M G R : (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo))
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hM : ∀ x : PeriodicLatticeSite L → SuTwo, QprimeTwo U x = 0 → M x = 0)
    (hG : ∀ x : PeriodicLatticeSite L → SuTwo, G ((Δ + M) x) = x)
    (hR : LinearMap.range R = Submodule.map Δ (LinearMap.ker (QprimeTwo U)))
    (f : PeriodicLatticeSite L → SuTwo) :
    siteEnergy (G (R f)) ≤ 8 * bondEnergy (gradValueCovariant U (G (R f))) :=
  gamma_poincare_assembly_of_mem_ker U (G (R f)) hdvd
    (gaugeParam_mem_ker_QprimeTwo U Δ M G R hM hG hR f).1

/-- **THE COMPOSITION, IN ONE DECLARATION.** The `κ` slot of `DeltaPrimeBound`'s
`abs_deltaPrimePiForm_le` is `hlam : siteEnergy lam ≤ κ²·bondEnergy A`; the first conjunct supplies
it at `κ² = 768`. The second conjunct is `GammaRecursion`'s criterion at that same `κ = √768`,
`q = 1/2`, `Jsup = 24·4·10⁻¹⁰`: the iterated bridge keeps a positive floor.

**Read the two conjuncts separately.** The second is `KappaBound.uniformStepGamma_at_four_e_minus_ten`
verbatim and depends on NONE of this theorem's hypotheses — it is a numeric fact about `√768`. The
content added here is that the first conjunct no longer carries a Poincaré hypothesis. -/
theorem kappa_bound_and_criterion_closes
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam src dstarA : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hmean : ∀ y ∈ CoarseLattice L 2, ∑ p : Bool × Bool × Bool, gammaM U lam y p = 0)
    (hweak : bondEnergy (gradValueCovariant U lam)
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner (gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA) :
    siteEnergy lam ≤ 768 * bondEnergy A
      ∧ AdalyFormal.Balaban.GammaRecursion.UniformStepGamma
          (KappaBound.deltaPiConstLocal (24 * (4 / 10 ^ 10 : ℝ)) (Real.sqrt 768)) (1/2 : ℝ) :=
  ⟨hlam_at_kappa_sq_768_gamma U lam src dstarA A hdvd hmean hweak hadj hproj,
    KappaBound.uniformStepGamma_at_four_e_minus_ten⟩

/-! ## §7 — CONTROLS

The three the dispatch asks for: a must-fire that the ORDER is a real distinction (in the bond set
and in the transport, not in the constant); and two must-not-fires (`y = x`, and `ell = 1`). -/

/-- **MUST-FIRE, denotation, half one: THE BOND SETS DIFFER.** `KappaBound.treeBondsTwo` carries the
direction-`0` bond `(y,0)` and no other; the (1.7) set carries FOUR direction-`0` bonds, among them
`(y+e₂+e₁, 0)`, which `treeBondsTwo` does not contain. So an instantiation in the ascending order
would be an instantiation of a DIFFERENT seven-bond set. -/
theorem gammaTreeBondsTwo_ne_treeBondsTwo (y : PeriodicLatticeSite L)
    (hlt : ∀ μ : Fin 3, (y μ).val < L μ) :
    gammaTreeBondsTwo y ≠ KappaBound.treeBondsTwo y := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := gammaTails_ne y hlt
  intro hc
  have hmem : ((periodicLatticeShift (periodicLatticeShift y 2) 1, (0 : Fin 3)) : Bond L)
      ∈ gammaTreeBondsTwo y := by
    simp [gammaTreeBondsTwo]
  rw [hc] at hmem
  simp only [KappaBound.treeBondsTwo, Finset.mem_insert, Finset.mem_singleton,
    Prod.ext_iff] at hmem
  rcases hmem with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨hs, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact h03 hs.symm
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **THE SHARP FORM OF THE MISMATCH.** `(y+e₀, 2)` is a bond of `KappaBound.treeBondsTwo y` that
lies on NO CMP95 (1.7) contour of the block at all. Immediate from §4a's anchor: the bonds of the
(1.7) contours are exactly `gammaTreeBondsTwo y`, whose ONLY direction-`2` bond is `(y,2)`. -/
theorem treeBondsTwo_bond_off_every_gamma_contour
    (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ) :
    ((periodicLatticeShift y 0, (2 : Fin 3)) : Bond L) ∈ KappaBound.treeBondsTwo y
      ∧ ∀ x ∈ blockOf y 2,
          ((periodicLatticeShift y 0, (2 : Fin 3)) : Bond L) ∉ staircasePath y x := by
  have hne : periodicLatticeShift y 0 ≠ y := by
    intro h
    have hg : gCorner y (true, false, false) = gCorner y (false, false, false) := h
    exact absurd (gCorner_inj y hlt hg) (by decide)
  refine ⟨by simp [KappaBound.treeBondsTwo], ?_⟩
  intro x hx hmem
  have hb : ((periodicLatticeShift y 0, (2 : Fin 3)) : Bond L)
      ∈ (blockOf y 2).biUnion (staircasePath y) := Finset.mem_biUnion.mpr ⟨x, hx, hmem⟩
  rw [← gammaTreeBondsTwo_eq_biUnion_staircasePath y hlt] at hb
  simp only [gammaTreeBondsTwo, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hb
  rcases hb with ⟨hs, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact hne hs
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **THE ASCENDING-ORDER TRANSPORT TO THE FAR CORNER**, written out for comparison: axis `0`
first, then `1`, then `2` — the order `KappaBound.treeBondsTwo` and
`AdmissibleSubspace.foilStaircasePath` use, and the one CMP95 (1.7) does NOT display. It is defined
here only as the foil of `gammaTransport`; nothing downstream consumes it. -/
noncomputable def ascTransportFar
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  U (y, 0) * U (periodicLatticeShift y 0, 1)
    * U (periodicLatticeShift (periodicLatticeShift y 0) 1, 2)

/-- `witnessMElem ≠ 1` — its `(0,0)` entry is `0`, the identity's is `1`. Needed because
`CovariantOperators` proves `RMap witnessMElem ≠ id` but never this. -/
theorem witnessMElem_ne_one : witnessMElem ≠ 1 := by
  intro hc
  have h : (witnessM : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have := congrArg (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ)) hc
    simpa [witnessMElem] using this
  have h00 := congrFun (congrFun h 0) 0
  simp [witnessM] at h00

/-- **MUST-NOT-FIRE, `ell = 1`.** The singleton block. `B(y)` at `ell = 1` is `{y}`, the (1.7)
contour family is the single empty contour, so the tree bond set is EMPTY; and the `ell = 1` kernel
condition `Q′λ(y) = 0` reads `λ(y) = 0`. The block inequality then holds — `0 ≤ 0` — rather than
breaking. -/
theorem blockOf_one_eq_singleton (y : PeriodicLatticeSite L) : blockOf y 1 = {y} := by
  ext x
  rw [mem_blockOf, Finset.mem_singleton]
  constructor
  · intro hx
    refine site_eq_of_val_eq (fun μ => ?_)
    have := hx μ
    omega
  · rintro rfl
    intro μ
    omega

theorem block_poincare_ell_one (lam : PeriodicLatticeSite L → SuTwo)
    (y : PeriodicLatticeSite L) (hmean : lam y = 0) (G : Bond L → SuTwo) :
    ∑ x ∈ blockOf y 1, ‖lam x‖ ^ 2 ≤ 8 * ∑ b ∈ (∅ : Finset (Bond L)), ‖G b‖ ^ 2 := by
  rw [blockOf_one_eq_singleton, Finset.sum_singleton, hmean]
  simp

/-! ## §8 — NON-VACUITY: A CONCRETE LATTICE, BACKGROUND AND NONZERO `λ` SATISFYING `hmean`

`hmean` is the only remaining hypothesis of §6 that is a condition on `λ` rather than an identity,
so it is the one that could be silently empty. It is not. -/

/-- The `2 × 2 × 2` periodic lattice: extent `L μ + 1 = 2` in each direction, exactly one `ell = 2`
block. -/
def witLTwo : PeriodicLatticeExtent := fun _ => 1

/-- Its unique coarse corner. -/
def witY : PeriodicLatticeSite witLTwo := fun _ => 0

theorem witY_fits : ∀ μ : Fin 3, (witY μ).val < witLTwo μ := by decide

theorem witLTwo_dvd : ∀ μ : Fin 3, 2 ∣ (witLTwo μ + 1) := by decide

/-- `λ`: `suTwoWitness` at the corner `y`, its negative at `y+e₀`, zero elsewhere. -/
noncomputable def witLam : PeriodicLatticeSite witLTwo → SuTwo := fun x =>
  if x = witY then suTwoWitness
  else if x = periodicLatticeShift witY 0 then -suTwoWitness else 0

/-- The flat background. -/
def witU : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witLTwo :=
  fun _ => 1

theorem witU_transport (p : Bool × Bool × Bool) : gammaTransport witU witY p = 1 := by
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;> simp [gammaTransport, witU]

theorem gammaM_witU (p : Bool × Bool × Bool) :
    gammaM witU witLam witY p = witLam (gCorner witY p) := by
  rw [gammaM, witU_transport, RMap_one]
  rfl

/-- **`hmean` IS SATISFIED BY A NONZERO `λ`.** -/
theorem witLam_mean_zero : ∑ p : Bool × Bool × Bool, gammaM witU witLam witY p = 0 := by
  rw [sum_bool3 (fun p => gammaM witU witLam witY p)]
  simp only [gammaM_witU]
  have h000 : gCorner witY (false, false, false) = witY := rfl
  have h100 : gCorner witY (true, false, false) = periodicLatticeShift witY 0 := rfl
  have hne : (periodicLatticeShift witY 0) ≠ witY := by decide
  have e000 : witLam (gCorner witY (false, false, false)) = suTwoWitness := by
    rw [h000, witLam, if_pos rfl]
  have e100 : witLam (gCorner witY (true, false, false)) = -suTwoWitness := by
    rw [h100, witLam, if_neg hne, if_pos rfl]
  have ezero : ∀ p : Bool × Bool × Bool, p ≠ (false, false, false) → p ≠ (true, false, false) →
      witLam (gCorner witY p) = 0 := by
    intro p hp0 hp1
    have hn0 : gCorner witY p ≠ witY := by
      intro hc
      exact hp0 (gCorner_inj witY witY_fits (hc.trans h000.symm))
    have hn1 : gCorner witY p ≠ periodicLatticeShift witY 0 := by
      intro hc
      exact hp1 (gCorner_inj witY witY_fits (hc.trans h100.symm))
    rw [witLam, if_neg hn0, if_neg hn1]
  rw [e000, e100, ezero (false, true, false) (by decide) (by decide),
    ezero (true, true, false) (by decide) (by decide),
    ezero (false, false, true) (by decide) (by decide),
    ezero (true, false, true) (by decide) (by decide),
    ezero (false, true, true) (by decide) (by decide),
    ezero (true, true, true) (by decide) (by decide)]
  abel

/-- **AND IT IS NOT THE ZERO FIELD**: its site energy is strictly positive, so §6's conclusion is
not `0 ≤ 0` on this witness. -/
theorem witLam_siteEnergy_pos : 0 < siteEnergy witLam := by
  have hterm : ∀ x : PeriodicLatticeSite witLTwo, 0 ≤ ‖witLam x‖ ^ 2 := fun x => sq_nonneg _
  have hy : ‖witLam witY‖ ^ 2 = ‖suTwoWitness‖ ^ 2 := by
    rw [witLam, if_pos rfl]
  have hpos : 0 < ‖witLam witY‖ ^ 2 := by
    rw [hy]
    have hn : (0:ℝ) < ‖suTwoWitness‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
    exact pow_pos hn 2
  calc (0:ℝ) < ‖witLam witY‖ ^ 2 := hpos
    _ ≤ siteEnergy witLam := by
        unfold siteEnergy
        exact Finset.single_le_sum (fun x _ => hterm x) (Finset.mem_univ witY)

/-- The single-bond background: `witnessMElem` on the bond `(y,0)` and `1` on every other bond. -/
noncomputable def spikeU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witLTwo :=
  fun b => if b = ((witY, (0 : Fin 3)) : Bond witLTwo) then witnessMElem else 1

theorem spikeU_off (b : Bond witLTwo) (h : b ≠ ((witY, (0 : Fin 3)) : Bond witLTwo)) :
    spikeU b = 1 := if_neg h

theorem spikeU_on : spikeU ((witY, (0 : Fin 3)) : Bond witLTwo) = witnessMElem := if_pos rfl

/-- The (1.7) contour to the far corner MISSES the spike bond: its last factor is the axis-`0` bond
based at `y+e₂+e₁`, not at `y`. -/
theorem spike_gammaTransport_far : gammaTransport spikeU witY (true, true, true) = 1 := by
  have h1 : ((witY, (2 : Fin 3)) : Bond witLTwo) ≠ ((witY, (0 : Fin 3)) : Bond witLTwo) := by
    decide
  have h2 : ((periodicLatticeShift witY 2, (1 : Fin 3)) : Bond witLTwo)
      ≠ ((witY, (0 : Fin 3)) : Bond witLTwo) := by decide
  have h3 : ((periodicLatticeShift (periodicLatticeShift witY 2) 1, (0 : Fin 3)) : Bond witLTwo)
      ≠ ((witY, (0 : Fin 3)) : Bond witLTwo) := by decide
  show spikeU (witY, 2) * spikeU (periodicLatticeShift witY 2, 1)
      * spikeU (periodicLatticeShift (periodicLatticeShift witY 2) 1, 0) = 1
  rw [spikeU_off _ h1, spikeU_off _ h2, spikeU_off _ h3, one_mul, one_mul]

/-- The ASCENDING contour to the SAME corner HITS it: its first factor is the axis-`0` bond based
at `y`. -/
theorem spike_ascTransport_far : ascTransportFar spikeU witY = witnessMElem := by
  have h2 : ((periodicLatticeShift witY 0, (1 : Fin 3)) : Bond witLTwo)
      ≠ ((witY, (0 : Fin 3)) : Bond witLTwo) := by decide
  have h3 : ((periodicLatticeShift (periodicLatticeShift witY 0) 1, (2 : Fin 3)) : Bond witLTwo)
      ≠ ((witY, (0 : Fin 3)) : Bond witLTwo) := by decide
  rw [ascTransportFar, spikeU_on, spikeU_off _ h2, spikeU_off _ h3, mul_one, mul_one]

/-- **MUST-FIRE, denotation, half two: THE TRANSPORTS DIFFER, at a concrete background.**

`Q′λ(y)` averages `R(Γ_{y,x})λ(x)`, so the contour order is not a labelling convention — it changes
the operator whose kernel §6's Poincaré inequality is proved on, hence changes the hypothesis
`hmean`. Here the (1.7) transport to the far corner is `1` and the ascending transport to the SAME
corner is `witnessMElem ≠ 1`. This is a difference in the OBJECT, not in the constant. -/
theorem descending_ne_ascending_transport :
    gammaTransport spikeU witY (true, true, true) ≠ ascTransportFar spikeU witY := by
  rw [spike_gammaTransport_far, spike_ascTransport_far]
  exact fun hc => witnessMElem_ne_one hc.symm

/-! ## §9 — THE WITNESS-CLASS FLAG: is the `α₀ ≤ 4·10⁻¹⁰` class EMPTY?

`KappaBound.criterion_closes_at_four_e_minus_ten` closes the fixed-point criterion at
`α₀ = 4·10⁻¹⁰`, three orders of magnitude below the tree's own `normAlpha = 5·10⁻⁷`. Two facts,
both checked rather than assumed.

**(i) Nothing needs re-instantiating.** No declaration in `KappaBound.lean` and none in this module
quantifies over a regularity class at all: `hlam_at_kappa_sq_768`, `poincare_assembly`,
`gamma_poincare_assembly` and `hlam_at_kappa_sq_768_gamma` take an ARBITRARY
`PeriodicLinkConfiguration` with no `GaugeRegular` hypothesis, and the `criterion_*` theorems are
inequalities between real numbers in which `normAlpha` and `4·10⁻¹⁰` occur as NUMERALS, not as class
parameters. So there is no theorem here quantifying over a class that could be empty.

**(ii) The class is not empty, and not only flat.** The flat background is trivially in it. Better,
a genuinely CURVED one is: `RegularUCurvedWitness.curvedFamilyU t` at `t = 10⁻¹¹` has
`frobSupBond ≤ 2√2·10⁻¹¹ < 4·10⁻¹⁰` and non-trivial holonomy.

**What is NOT claimed.** `CoercivityRegular.curvedRegularU = curvedFamilyU 10⁻⁷` carries only the
UPPER bound `frobSupBond ≤ normAlpha = 5·10⁻⁷`. That does not place it in the `4·10⁻¹⁰` class, and
this module does NOT prove it lies outside either: `GaugeRegular` is an existential over gauge
transformations, so excluding it would need a gauge-invariant LOWER bound, which is not derived
here. The honest statement is that `curvedRegularU` is not KNOWN to be in the class, and that
`curvedTinyU` is. -/

/-- `t = 10⁻¹¹`. -/
noncomputable def curvedTiny : ℝ := 1 / 10 ^ 11

theorem curvedTiny_pos : 0 < curvedTiny := by unfold curvedTiny; norm_num

/-- A genuinely curved background of the `α₀ ≤ 4·10⁻¹⁰` class. Kept `abbrev` so that the two
theorems below unify with `RegularUCurvedWitness`'s own lemmas without a delta step. -/
noncomputable abbrev curvedTinyU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdalyFormal.Balaban.RegularUDomainWitness.witL5 :=
  AdalyFormal.Balaban.RegularUCurvedWitness.curvedFamilyU curvedTiny

/-- **IT IS IN THE CLASS.** `2√2·10⁻¹¹ ≤ 4·10⁻¹⁰` since `2√2 ≤ 4 ≤ 40`. -/
theorem curvedTinyU_gaugeRegular :
    AdalyFormal.Balaban.AlphaAnalyticity.GaugeRegular (4 / 10 ^ 10 : ℝ) curvedTinyU := by
  refine AdalyFormal.Balaban.AlphaAnalyticity.gaugeRegular_of_frobSupBond_le ?_
  have h := AdalyFormal.Balaban.RegularUCurvedWitness.frobSupBond_curvedFamilyU_le curvedTiny
  have habs : |curvedTiny| = curvedTiny := abs_of_pos curvedTiny_pos
  rw [habs] at h
  refine le_trans h ?_
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs : Real.sqrt 2 ≤ 2 := by nlinarith
  unfold curvedTiny
  nlinarith

/-- **AND IT IS NOT FLAT.** -/
theorem curvedTinyU_curved :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem
        (AdalyFormal.Balaban.RegularUCurvedWitness.curvedFamilyU curvedTiny)
        AdalyFormal.Balaban.RegularUCurvedWitness.curvedPlaq
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  AdalyFormal.Balaban.RegularUCurvedWitness.curvedFamilyU_curvature_ne_one
    (ne_of_gt curvedTiny_pos)

#print axioms site_eq_of_val_eq
#print axioms site_eq_of_agree
#print axioms update_eq_of_agree
#print axioms sval
#print axioms sapp_ne
#print axioms sval_ne
#print axioms gInner
#print axioms gInner_true
#print axioms gCorner
#print axioms gCorner_false
#print axioms gCorner_true
#print axioms gOff
#print axioms gOff_le_one
#print axioms gInner_false_agree
#print axioms gInner_agree_one
#print axioms gCorner_agree_zero
#print axioms gInner_val0
#print axioms gInner_val1
#print axioms gInner_val2
#print axioms gCorner_val
#print axioms gCorner_mem_block
#print axioms blockOf_two_eq_image
#print axioms gCorner_injOn
#print axioms gCorner_inj
#print axioms sum_block_eq
#print axioms sum_bool3
#print axioms gammaTreeBondsTwo
#print axioms gammaTails_ne
#print axioms sum_gammaTreeBondsTwo
#print axioms corner1_apply_ne
#print axioms corner1_gCorner
#print axioms corner2_gCorner
#print axioms min_max_gCorner
#print axioms gammaTreeBondsTwo_eq_biUnion_staircasePath
#print axioms gammaTransport
#print axioms gammaM
#print axioms gammaM_root
#print axioms norm_gammaM
#print axioms step_y2
#print axioms step_y1
#print axioms step_y0
#print axioms step_s2_1
#print axioms step_s2_0
#print axioms step_s1_0
#print axioms step_s12_0
#print axioms gamma_block_poincare
#print axioms gammaTreeBondsTwo_tail_mem
#print axioms gammaTreeBondsTwo_pairwiseDisjoint
#print axioms gamma_poincare_assembly
#print axioms hlam_at_kappa_sq_768_gamma
#print axioms QprimeTwo
#print axioms QprimeTwo_apply
#print axioms gamma_poincare_assembly_of_mem_ker
#print axioms gaugeParam_mem_ker_QprimeTwo
#print axioms poincare_for_gaugeParam
#print axioms gammaTreeBondsTwo_ne_treeBondsTwo
#print axioms treeBondsTwo_bond_off_every_gamma_contour
#print axioms descending_ne_ascending_transport
#print axioms kappa_bound_and_criterion_closes
#print axioms curvedTiny
#print axioms curvedTiny_pos
#print axioms curvedTinyU
#print axioms curvedTinyU_gaugeRegular
#print axioms curvedTinyU_curved
#print axioms blockOf_one_eq_singleton
#print axioms block_poincare_ell_one
#print axioms witLTwo
#print axioms witY
#print axioms witY_fits
#print axioms witLTwo_dvd
#print axioms witLam
#print axioms witU
#print axioms witU_transport
#print axioms gammaM_witU
#print axioms witLam_mean_zero
#print axioms witLam_siteEnergy_pos
#print axioms ascTransportFar
#print axioms witnessMElem_ne_one
#print axioms spikeU
#print axioms spikeU_off
#print axioms spikeU_on
#print axioms spike_gammaTransport_far
#print axioms spike_ascTransport_far

end AdalyFormal.Balaban.GammaContourTree
