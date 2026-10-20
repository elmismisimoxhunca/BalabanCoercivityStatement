/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Claim18Carrier
import AdalyFormal.Balaban.LineIntegralAveraging
import AdalyFormal.Balaban.PoincareBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.longLine false

/-!
# `QcEquation.lean` — Claim 18's clauses with `𝒬_c` **SUPPLIED BY AN EQUATION**

## Why this module exists — the measurement that forced it

`Claim18Carrier.Clauses` fixed the CARRIER (two spaces, so a coarse average can be non-injective)
but still quantified EXISTENTIALLY over `(C2, Qc, Qc_inv)`. `compute/claim18_carrier/
carrier_attacks.lean`'s `carrier_clauses_land_by_linear_algebra` then measured the price: the
bundle is satisfiable at EVERY carrier pair with `finrank Hcoarse < finrank Hfine`, **by pure
linear algebra** — its only hypotheses are that dimension drop, `0 < L`, `0 ≤ Ccorr`, `0 ≤ α₀`.
A bundle that lets the prover choose the operator it is meant to constrain cannot constrain it,
however many clauses are added. So no set of INEQUALITIES on freely chosen operators will do; only
an EQUATION pinning `Qc` to Bałaban's actual averaging operator can.

This module supplies that equation.

## What is supplied, and from where (LAW-19 — nothing here is rebuilt)

* **`𝒬_c := LineIntegralAveraging.lineCoarseRestrictCLM L ell`**, the FAITHFUL `Q_k` of CMP95
  (1.11)/(1.18) — the block average of the straight-segment LINE INTEGRALS, `η^{d+1} = 1/ell⁴`
  against `ell³·ell = ell⁴` terms. It is already a `BondSpace L →L[ℝ] CoarseBondSpace L ell`, so
  no normed structure has to be built for it.
  *Decision, recorded:* the alternative route through `ThirdLevelArrows.unitToCoarseLM` was NOT
  taken — that arrow is a bare `→ₗ[ℝ]` with no normed structure and could not inhabit a `→L[ℝ]`
  clause without building one, while `lineCoarseRestrictCLM` needs nothing. `NameReconciliation`
  also names `lineCoarseRestrict` the CANONICAL spelling for this tree, and the naive
  `LatticeOperators.coarseRestrict` is the operator that DROPPED the `×ell` line-integral factor
  (`LineIntegralAveraging.coarseRestrict_const_witness`: it returns `1/2` on the constant field `1`
  at `ell = 2`, i.e. it is not an average at all).
* **`𝒬_c⁻¹ := qcSection L ell`**, built here, and it too is supplied rather than chosen:
  the coarse value `f(y,μ)`, weighted by `ell`, placed on the fine `μ`-bonds whose `μ`-offset
  inside their block is `ell - 1` (the LAST layer). `qc_comp_section` proves
  `𝒬_c ∘L 𝒬_c⁻¹ = id` EXACTLY, on any lattice with `0 < ell` and `ell ∣ L μ + 1`.

## The last-layer section is a COMPUTED choice, not a convenience — the arithmetic is recorded

Write `s_w^k(f)(z,μ) := w · f(π z, μ) · [offset_μ(z) = k]` with `π` the block corner. Then for
`x ∈ B(y)` with `μ`-offset `i` and `j < ell`, the site `x + j e_μ` has `μ`-offset `(i+j) % ell`
and lies in `B(y)` iff `i + j < ell`. Counting the pairs `(i,j)` in `[0,ell)²` gives, after the
`1/ell⁴` and the `ell²` transverse block positions:

| `k` | `𝒬_c ∘ s_1^k` | verdict | status |
|---|---|---|---|
| spread evenly over the block (Bałaban's constant extension) | `(1/ell²)[((ell+1)/2)·I + ((ell-1)/2)·T]` | **not a section** | formula: HAND ARITHMETIC; **the verdict itself is KERNEL-CHECKED** (`constExtLift_not_section`, §8c) |
| `k = 0` (first layer) | `(1/ell²)[1·I + (ell-1)·T]` | not a section | **HAND ARITHMETIC ONLY** |
| `k = ell - 1` (last layer), `w = ell` | `I` | **exact section** | **KERNEL-CHECKED** (`lineCoarseRestrict_lastLayerLift`) |

**Read the status column literally (§GREEN-8).** The two closed-form MATRICES in rows 1 and 2 are
pencil computation, recorded so the choice of layer is not a rabbit out of a hat, and they are NOT
verified by the kernel. Their arithmetic, so a reader can check it: over `(i,j) ∈ [0,ell)²` the
pairs with `i+j = k` number `k+1` (for `k < ell`) and those with `i+j = k+ell` number `ell-1-k`;
multiplying by the `ell²` transverse block positions and dividing by `ell⁴` gives the two rows, and
at `k = ell-1` the second count is `0` and the first is `ell`. `T` is the coarse shift by `ell·e_μ`.

**The load-bearing part of row 1 is a THEOREM, not arithmetic.** `constExtLift_not_section` (§8c)
proves, generally in `L` and `ell` (`2 ≤ ell`, tileable, at least two coarse sites along direction
`0`), that **Bałaban's own spreading map is not an exact right inverse of his own averaging map** —
so clause 1 (`Qc ∘L Qc_inv = id`) as the tree states it is not satisfied by the constant extension;
only by a genuine section. The proof does not compute any block count: it exhibits ONE fine bond
whose segment leaves the block, which makes the neighbouring coarse bond's indicator have strictly
positive average where the indicator itself is `0`.

## What the equation DOES and DOES NOT remove

With `Qc` and `Qc_inv` supplied, clauses 1–4 of `Claim18Carrier.Clauses` STOP BEING CLAUSES: they
become assertions about the actual lattice operator, each of which is here either PROVED or FALSE.

| clause | with `𝒬_c` supplied | status here |
|---|---|---|
| 1 `Qc ∘L Qc_inv = id` | a statement about the real average and the real lift | **PROVED** (`qc_comp_section`) |
| 2 `Injective Qc_inv` | ditto | **PROVED** (`qcSection_injective`) |
| 3 `‖Qc‖ ≤ 1 + Ccorr·L²·α₀` | ditto | **PROVED** (`qcOp_clause3`, via `qcOp_opNorm_le_one`) |
| 4a `1 ≤ ‖C2‖` | still about `C2` | still a clause |
| 4b `¬ Injective Qc` | a statement about the real average | **PROVED at `2 ≤ ell`** (`qcOp_not_injective`) |
| 5 `‖C2 ∘L Qc_inv‖ ≤ L^{d-1}` | still about `C2` | still a clause |
| 6 `C2 ∘L Qc_inv ≠ 0` | still about `C2` | still a clause |

What remains existentially quantified is `C2` ALONE. `compute/qc_equation/qc_attacks.lean`
measures what that costs, exactly as `carrier_attacks.lean` did for the previous statement, and
`§8` below states the residual precisely: the next equation the statement needs is one pinning
`C⁽²⁾`, not one pinning `𝒬_c`.

## HONEST SCOPE — the disclosed decisions, all deliberate

1. **Clause 3's norm class, decided rather than inherited.** CMP98 p.36 (126) reads
   `|(Q(V₀)A)_c| ≦ ‖A‖ + O(1)L²α₀‖A‖` — an ABSOLUTE bound with `‖Q₀‖ ≤ 1`, in the SUP norm on
   bond fields. `Claim18Carrier.Clauses` clause 3 is in the OPERATOR norm of the carrier. This
   module ships **BOTH**, as theorems about the same supplied operator:
   `qc_sup_bound` (the literal (126) shape: `|(𝒬_c A)_c| ≤ ‖A‖_∞` for every coarse bond) and
   `qcOp_opNorm_le_one` (the `ℓ²` operator norm, which is what the carrier clause consumes). The
   modelling simplification is therefore no longer load-bearing: whichever norm class is read,
   the supplied operator satisfies the constant `1`, and the two proofs are independent (the sup
   bound is the unit-mass-weights argument; the `ℓ²` bound is Cauchy–Schwarz plus the block
   tiling, and it yields the strictly stronger `‖𝒬_c‖ ≤ √(ell^{-3})`, which is
   `qcOp_opNorm_le_sqrt` — a declaration, not a docstring claim).
2. **`2 ≤ ell` for clause 4b.** At `ell = 1` the faithful average IS the identity-like single-bond
   operator (`LineIntegralAveraging.lineCoarseRestrict_one_eq_coarseRestrict`) and there is no
   coarsening to speak of; §DEGEN of `compute/BUILD_STANDARDS.md` lists `ell = 1` as a degenerate
   point for exactly this reason. Non-injectivity is stated at `2 ≤ ell` and PROVED there, with an
   explicit kernel element, not assumed.
3. **`C⁽²⁾` is not supplied.** It is a dynamical object (the second-order term of the effective
   action) and this tree does not define it. §8 states that residual and names the exhibit that
   measures it; the tag `[RES-O1-NEEDS-C2]` is PROPOSED for `compute/RESIDUAL_REGISTER.md` by this
   lane and is not asserted to be already filed there (the register has a single writer).
-/

namespace AdalyFormal.Balaban.QcEquation

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.LineIntegralAveraging
open ContinuousLinearMap

variable {L : PeriodicLatticeExtent}

/-! ## §0 — the straight-path site, and its two coordinate formulas

`LineIntegralAveraging.lineIntegralValue` sums over `(fun z => periodicLatticeShift z μ)^[j] x`.
`pathStep` below is that iterate under a name, DEFINITIONALLY equal to `QOne.pathSite`. The two
formulas are the same statements as `ReparamCDisjoint.pathSite_apply_ne` /
`pathSite_apply_self_val`; they are re-proved here (four lines each) rather than imported because
`ReparamCDisjoint` sits on top of the whole `ReparamCSuTwo` SU(2) chain and importing it for two
coordinate lemmas would drag that chain into every consumer of this module. Disclosed duplication,
not a re-derivation claim. -/

/-- `j` forward fine steps in direction `μ` — definitionally the iterate
`LineIntegralAveraging.lineIntegralValue` sums over, and definitionally `QOne.pathSite`. -/
def pathStep (x : PeriodicLatticeSite L) (μ : Fin 3) (j : ℕ) : PeriodicLatticeSite L :=
  (fun z => periodicLatticeShift z μ)^[j] x

theorem pathStep_zero (x : PeriodicLatticeSite L) (μ : Fin 3) : pathStep x μ 0 = x := rfl

theorem pathStep_succ (x : PeriodicLatticeSite L) (μ : Fin 3) (j : ℕ) :
    pathStep x μ (j + 1) = periodicLatticeShift (pathStep x μ j) μ :=
  Function.iterate_succ_apply' _ j x

/-- The fold lemma: `lineIntegralValue`'s raw iterate IS `pathStep` (by `rfl`), stated so that
`simp only` can fold it after `lineIntegralValue` is unfolded. -/
theorem iterate_eq_pathStep (x : PeriodicLatticeSite L) (μ : Fin 3) (j : ℕ) :
    (fun z => periodicLatticeShift z μ)^[j] x = pathStep x μ j := rfl

/-- Transverse coordinates are untouched by a `μ`-path. -/
theorem pathStep_apply_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (j : ℕ) (h : ν ≠ μ) :
    pathStep x μ j ν = x ν := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [pathStep_succ, periodicLatticeShift, Function.update_of_ne h, ih]

/-- The moved coordinate, as a `Nat` value: forward by `j`, modulo the periodic extent. -/
theorem pathStep_apply_self_val (x : PeriodicLatticeSite L) (μ : Fin 3) (j : ℕ) :
    ((pathStep x μ j) μ).val = ((x μ).val + j) % (L μ + 1) := by
  induction j with
  | zero => simp [pathStep_zero, Nat.mod_eq_of_lt (x μ).isLt]
  | succ n ih =>
    rw [pathStep_succ, periodicLatticeShift, Function.update_self, Fin.val_add, ih, Fin.val_one',
      ← Nat.add_mod]
    congr 1

/-- A `μ`-path of fixed length is injective on sites (iterate of the injective fine shift). -/
theorem pathStep_injective (μ : Fin 3) (j : ℕ) :
    Function.Injective (fun x : PeriodicLatticeSite L => pathStep x μ j) :=
  Function.Injective.iterate (AdalyFormal.Balaban.CoarseCurl.periodicLatticeShift_injective μ) j

theorem pathStep_bijective (μ : Fin 3) (j : ℕ) :
    Function.Bijective (fun x : PeriodicLatticeSite L => pathStep x μ j) :=
  Finite.injective_iff_bijective.mp (pathStep_injective μ j)

#print axioms pathStep_apply_ne
#print axioms pathStep_apply_self_val
#print axioms pathStep_bijective

/-! ## §1 — `π`, the block corner: the coarse site owning a fine site -/

/-- **`π z`** — the corner of the block containing `z`: every coordinate floored to a multiple of
the block side `ell`. -/
def blockCorner (ell : ℕ) (z : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun ν => ⟨(z ν).val - (z ν).val % ell, lt_of_le_of_lt (Nat.sub_le _ _) (z ν).isLt⟩

theorem blockCorner_val (ell : ℕ) (z : PeriodicLatticeSite L) (ν : Fin 3) :
    (blockCorner ell z ν).val = (z ν).val - (z ν).val % ell := rfl

/-- `π z` really is a coarse-lattice site. -/
theorem blockCorner_mem {ell : ℕ} (z : PeriodicLatticeSite L) :
    blockCorner ell z ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice]
  intro ν
  rw [blockCorner_val]
  have hdm := Nat.div_add_mod (z ν).val ell
  have hz : (z ν).val - (z ν).val % ell = ell * ((z ν).val / ell) := by omega
  rw [hz]
  exact Nat.mul_mod_right _ _

/-- **`π` recovers the corner it started from**: if `x ∈ B(y)` for a coarse `y`, then `π x = y`,
coordinate by coordinate. This is the tiling law in the form the section proof needs. -/
theorem blockCorner_of_mem_blockOf {ell : ℕ} {y x : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (hx : x ∈ blockOf y ell) : blockCorner ell x = y := by
  funext ν
  apply Fin.ext
  rw [blockCorner_val]
  have hb := (mem_blockOf.mp hx) ν
  have hy0 : (y ν).val % ell = 0 := (mem_CoarseLattice.mp hy) ν
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hy0
  have hxv : (x ν).val = ell * k + ((x ν).val - (y ν).val) := by omega
  have hlt : (x ν).val - (y ν).val < ell := by omega
  have hmod : (x ν).val % ell = (x ν).val - (y ν).val := by
    conv_lhs => rw [hxv]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  omega

#print axioms blockCorner_mem
#print axioms blockCorner_of_mem_blockOf

/-! ## §2 — `𝒬_c⁻¹`, the LAST-LAYER LIFT, supplied -/

/-- **`(𝒬_c⁻¹ f)(z,μ) := ell · f(π z, μ)` on the fine `μ`-bonds whose `μ`-offset inside their own
block is `ell - 1`, and `0` elsewhere.** The unique member of the one-parameter family
`s_w^k` (module docstring) that is an EXACT right inverse of the faithful average. -/
noncomputable def lastLayerLift (ell : ℕ) (f : CoarseBond L ell → ℝ) (b : Bond L) : ℝ :=
  if (b.1 b.2).val % ell = ell - 1 then
    (ell : ℝ) * f (⟨blockCorner ell b.1, blockCorner_mem b.1⟩, b.2)
  else 0

theorem lastLayerLift_add (ell : ℕ) (f g : CoarseBond L ell → ℝ) (b : Bond L) :
    lastLayerLift ell (f + g) b = lastLayerLift ell f b + lastLayerLift ell g b := by
  unfold lastLayerLift
  split_ifs with h
  · simp only [Pi.add_apply]; ring
  · ring

theorem lastLayerLift_smul (ell : ℕ) (c : ℝ) (f : CoarseBond L ell → ℝ) (b : Bond L) :
    lastLayerLift ell (c • f) b = c * lastLayerLift ell f b := by
  unfold lastLayerLift
  split_ifs with h
  · simp only [Pi.smul_apply, smul_eq_mul]; ring
  · ring

/-! ## §3 — THE SECTION EQUATION `𝒬_c ∘ 𝒬_c⁻¹ = id`, at the raw-function layer -/

/-- The residue count that makes the last layer work: for offsets `i, j < ell`, the path lands on
the last layer of its own block exactly at `j = ell - 1 - i`, and at no other `j`. -/
theorem residue_hit_iff {ell i j : ℕ} (hell : 0 < ell) (hi : i < ell) (hj : j < ell) :
    (i + j) % ell = ell - 1 ↔ j = ell - 1 - i := by
  constructor
  · intro h
    rcases lt_or_ge (i + j) ell with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · have hstep : (i + j) % ell = i + j - ell := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      omega
  · intro h
    subst h
    have he : i + (ell - 1 - i) = ell - 1 := by omega
    rw [he, Nat.mod_eq_of_lt (by omega)]

/-- **The per-site value of the lift's line integral.** For a coarse site `y`, a block member
`x ∈ B(y)` and a direction `μ`, the straight-segment line integral of the last-layer lift is
exactly `ell · f(y, μ)`: one hit, of weight `ell`. -/
theorem lineIntegralValue_lastLayerLift {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell)
    (μ : Fin 3) (f : CoarseBond L ell → ℝ) :
    lineIntegralValue ell (lastLayerLift ell f) x μ = (ell : ℝ) * f (⟨y, hy⟩, μ) := by
  classical
  -- the `μ`-offset of `x` inside its block
  set i : ℕ := (x μ).val - (y μ).val with hi_def
  have hbμ := (mem_blockOf.mp hx) μ
  have hy0 : (y μ).val % ell = 0 := (mem_CoarseLattice.mp hy) μ
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hy0
  have hi_lt : i < ell := by omega
  have hxval : (x μ).val = ell * k + i := by omega
  have hfit : (y μ).val + ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd hy μ
  -- the residue of the path coordinate
  have hres : ∀ j : ℕ, ((pathStep x μ j) μ).val % ell = (i + j) % ell := by
    intro j
    rw [pathStep_apply_self_val, Nat.mod_mod_of_dvd _ (hdvd μ), hxval]
    conv_lhs => rw [show ell * k + i + j = ell * k + (i + j) by ring]
    rw [Nat.mul_add_mod]
  -- the unique hit
  have hjstar : ell - 1 - i < ell := by omega
  rw [lineIntegralValue]
  rw [Finset.sum_eq_single (ell - 1 - i)]
  · -- the value at the hit
    have hcond : ((pathStep x μ (ell - 1 - i)) μ).val % ell = ell - 1 := by
      rw [hres]
      exact (residue_hit_iff hell hi_lt hjstar).mpr rfl
    simp only [lastLayerLift, iterate_eq_pathStep]
    rw [if_pos hcond]
    congr 2
    -- `π (pathStep x μ (ell-1-i)) = y`
    refine Prod.ext_iff.mpr ⟨?_, rfl⟩
    apply Subtype.ext
    funext ν
    apply Fin.ext
    rw [blockCorner_val]
    by_cases hν : ν = μ
    · subst hν
      have hvv : ((pathStep x ν (ell - 1 - i)) ν).val = ell * k + (ell - 1) := by
        rw [pathStep_apply_self_val, hxval]
        rw [show ell * k + i + (ell - 1 - i) = ell * k + (ell - 1) by omega]
        exact Nat.mod_eq_of_lt (by omega)
      have hvm : ((pathStep x ν (ell - 1 - i)) ν).val % ell = ell - 1 := by
        rw [hres]
        exact (residue_hit_iff hell hi_lt hjstar).mpr rfl
      show ((pathStep x ν (ell - 1 - i)) ν).val -
          ((pathStep x ν (ell - 1 - i)) ν).val % ell = (y ν).val
      omega
    · rw [pathStep_apply_ne x μ ν _ hν]
      have := congrArg (fun z : PeriodicLatticeSite L => (z ν).val)
        (blockCorner_of_mem_blockOf hy hx)
      simpa [blockCorner_val] using this
  · -- every other `j` misses
    intro j hjmem hjne
    rw [Finset.mem_range] at hjmem
    have hcond : ¬ ((pathStep x μ j) μ).val % ell = ell - 1 := by
      rw [hres]
      intro hc
      exact hjne ((residue_hit_iff hell hi_lt hjmem).mp hc)
    simp only [lastLayerLift, iterate_eq_pathStep]
    rw [if_neg hcond]
  · intro hnot
    exact absurd (Finset.mem_range.mpr hjstar) hnot

/-- **THE SECTION EQUATION, at the raw-function layer.** `𝒬_c (𝒬_c⁻¹ f) = f`, at every coarse
bond, on every lattice with `0 < ell` and `ell ∣ L μ + 1`. -/
theorem lineCoarseRestrict_lastLayerLift {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (f : CoarseBond L ell → ℝ) (b : CoarseBond L ell) :
    lineCoarseRestrict ell (lastLayerLift ell f) b = f b := by
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  rw [lineCoarseRestrict]
  rw [Finset.sum_congr rfl
    (fun x hx => lineIntegralValue_lastLayerLift hell hdvd hy hx μ f)]
  rw [Finset.sum_const, card_blockOf_of_coarse hdvd hy, nsmul_eq_mul]
  have hne : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  push_cast
  field_simp

#print axioms lineCoarseRestrict_lastLayerLift

/-! ## §4 — the Hilbert-space promotion of the section (mirrors `LineIntegralAveraging` §6) -/

/-- The last-layer lift as a `LinearMap` on raw function spaces. -/
noncomputable def lastLayerLiftLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    (CoarseBond L ell → ℝ) →ₗ[ℝ] (Bond L → ℝ) where
  toFun f := lastLayerLift ell f
  map_add' f g := funext fun b => lastLayerLift_add ell f g b
  map_smul' c f := funext fun b => lastLayerLift_smul ell c f b

/-- The last-layer lift, transported to the Hilbert-space layer. -/
noncomputable def lastLayerLiftLMH (L : PeriodicLatticeExtent) (ell : ℕ) :
    CoarseBondSpace L ell →ₗ[ℝ] BondSpace L :=
  (bondEquiv L).symm.toLinearMap.comp
    ((lastLayerLiftLM L ell).comp (coarseBondEquiv L ell).toLinearMap)

/-- **`𝒬_c⁻¹` as a genuine `ContinuousLinearMap`** — the SUPPLIED section. -/
noncomputable def qcSection (L : PeriodicLatticeExtent) (ell : ℕ) :
    CoarseBondSpace L ell →L[ℝ] BondSpace L :=
  LinearMap.toContinuousLinearMap (lastLayerLiftLMH L ell)

theorem qcSection_apply (L : PeriodicLatticeExtent) (ell : ℕ) (F : CoarseBondSpace L ell) :
    bondEquiv L (qcSection L ell F) = lastLayerLift ell (coarseBondEquiv L ell F) := rfl

/-- **`𝒬_c`, under the name the clause bundle uses.** Not a new object: this is
`LineIntegralAveraging.lineCoarseRestrictCLM`, reused (LAW-19). -/
noncomputable def qcOp (L : PeriodicLatticeExtent) (ell : ℕ) :
    BondSpace L →L[ℝ] CoarseBondSpace L ell :=
  lineCoarseRestrictCLM L ell

theorem qcOp_apply (L : PeriodicLatticeExtent) (ell : ℕ) (A : BondSpace L) :
    coarseBondEquiv L ell (qcOp L ell A) = lineCoarseRestrict ell (bondEquiv L A) := rfl

/-- **THE EQUATION, at the operator layer: `𝒬_c ∘L 𝒬_c⁻¹ = id`.** Clause 1 of
`Claim18Carrier.Clauses` is no longer a demand on a chosen witness; it is this theorem. -/
theorem qc_comp_section {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    qcOp L ell ∘L qcSection L ell = ContinuousLinearMap.id ℝ (CoarseBondSpace L ell) := by
  refine ContinuousLinearMap.ext fun F => ?_
  apply (coarseBondEquiv L ell).injective
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply, qcOp_apply, qcSection_apply]
  funext b
  exact lineCoarseRestrict_lastLayerLift hell hdvd _ b

#print axioms qc_comp_section

/-- Clause 2, likewise a theorem: an exact section is injective. -/
theorem qcSection_injective {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Function.Injective (qcSection L ell) :=
  Claim18Carrier.section_forces_inv_injective (qc_comp_section hell hdvd)

/-- Clause 1's other half, as a theorem: the faithful average is SURJECTIVE. -/
theorem qcOp_surjective {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Function.Surjective (qcOp L ell) :=
  Claim18Carrier.section_forces_surjective (qc_comp_section hell hdvd)

#print axioms qcSection_injective
#print axioms qcOp_surjective

/-! ## §5 — clause 4b as a THEOREM: the faithful average is NOT injective at `2 ≤ ell`

`Claim18Carrier.Clauses` clause 4 demands `¬ Function.Injective Qc` — "genuine coarsening", the
clause that kills every isometry and every rescaled isometry at once. With `Qc` supplied this is no
longer a demand on a witness: it is a statement about `LineIntegralAveraging.lineCoarseRestrict`,
proved here with an EXPLICIT kernel element rather than by a dimension count. -/

/-- **The kernel probe** `λ₀(x) := (x_0 mod ell)` — a site function of the `0`-coordinate's offset
inside its own block. It is invariant under EVERY coarse shift (`ell ∣ L μ + 1` makes the `μ = 0`
shift a no-op on the residue, and the other two directions do not move coordinate `0`), so all of
its block averages agree, so CMP95 (1.20) sends its gradient to `0`. -/
noncomputable def kerLam (ell : ℕ) (x : PeriodicLatticeSite L) : ℝ := (((x 0).val % ell : ℕ) : ℝ)

theorem coarseShift_eq_pathStep (x : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    AdalyFormal.Balaban.CoarseCurl.coarseShift x ell μ = pathStep x μ ell := rfl

/-- `λ₀` is invariant under every coarse shift. -/
theorem kerLam_coarseShift {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (μ : Fin 3)
    (x : PeriodicLatticeSite L) :
    kerLam ell (AdalyFormal.Balaban.CoarseCurl.coarseShift x ell μ) = kerLam ell x := by
  unfold kerLam
  rw [coarseShift_eq_pathStep]
  congr 1
  by_cases h : μ = 0
  · subst h
    rw [pathStep_apply_self_val, Nat.mod_mod_of_dvd _ (hdvd 0), Nat.add_mod_right]
  · rw [pathStep_apply_ne x μ 0 ell (fun hc => h hc.symm)]

/-- All of `λ₀`'s block averages agree, in the form CMP95 (1.20) consumes. -/
theorem coarseRestrictSite_kerLam_shift {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    AdalyFormal.Balaban.KernelSubspace.coarseRestrictSite ell (kerLam ell)
        (AdalyFormal.Balaban.CoarseCurl.coarseShift y ell μ)
      = AdalyFormal.Balaban.KernelSubspace.coarseRestrictSite ell (kerLam ell) y := by
  unfold AdalyFormal.Balaban.KernelSubspace.coarseRestrictSite
  congr 1
  rw [AdalyFormal.Balaban.CoarseShiftCovariance.coarseShift_blockOf_eq_image hell (hdvd μ) hy,
    Finset.sum_image
      (fun x _ x' _ h => AdalyFormal.Balaban.CoarseShiftCovariance.coarseShift_injective ell μ h)]
  exact Finset.sum_congr rfl fun x _ => kerLam_coarseShift hdvd μ x

/-- **`𝒬_c (∂₀λ₀) = 0` at EVERY coarse bond** — the kernel element, at the raw-function layer. -/
theorem lineCoarseRestrict_gradValue_kerLam {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (b : CoarseBond L ell) :
    lineCoarseRestrict ell (gradValue (kerLam ell)) b = 0 := by
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  rw [lineCoarseRestrict_gradValue hell (hdvd μ) hy, coarseRestrictSite_kerLam_shift hell hdvd hy μ]
  ring

/-- The lattice origin. -/
def originSite (L : PeriodicLatticeExtent) : PeriodicLatticeSite L := fun _ => ⟨0, Nat.succ_pos _⟩

/-- **`∂₀λ₀ ≠ 0`, exhibited at a NAMED bond**: `(∂₀λ₀)(origin, 0) = 1` whenever `2 ≤ ell` and the
lattice is tileable. Not "a nonzero element exists" — this one. -/
theorem gradValue_kerLam_origin {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    gradValue (kerLam ell) (originSite L, (0 : Fin 3)) = 1 := by
  have hL0 : 2 ≤ L 0 + 1 := by
    have := Nat.le_of_dvd (Nat.succ_pos _) (hdvd 0)
    omega
  have hone : (1 : Fin (L 0 + 1)).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hval : ((periodicLatticeShift (originSite L) (0 : Fin 3)) 0).val = 1 := by
    rw [AdalyFormal.Balaban.CoarseCurl.periodicLatticeShift_self]
    have hz : ((originSite L) (0 : Fin 3)) = (0 : Fin (L 0 + 1)) := rfl
    rw [hz, zero_add, hone]
  have h0 : ((originSite L) (0 : Fin 3)).val = 0 := rfl
  change kerLam ell (periodicLatticeShift (originSite L) 0) - kerLam ell (originSite L) = 1
  unfold kerLam
  rw [hval, h0, Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < ell)]
  norm_num

/-- The kernel element, in the Hilbert space. -/
noncomputable def kerWitness (L : PeriodicLatticeExtent) (ell : ℕ) : BondSpace L :=
  (bondEquiv L).symm (gradValue (kerLam ell))

theorem bondEquiv_kerWitness (L : PeriodicLatticeExtent) (ell : ℕ) :
    bondEquiv L (kerWitness L ell) = gradValue (kerLam ell) :=
  (bondEquiv L).apply_symm_apply _

/-- **`𝒬_c` kills the witness.** -/
theorem qcOp_kerWitness {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    qcOp L ell (kerWitness L ell) = 0 := by
  apply (coarseBondEquiv L ell).injective
  rw [qcOp_apply, map_zero, bondEquiv_kerWitness]
  funext b
  exact lineCoarseRestrict_gradValue_kerLam hell hdvd b

/-- **The witness is nonzero.** -/
theorem kerWitness_ne_zero {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    kerWitness L ell ≠ 0 := by
  intro hz
  have h1 : bondEquiv L (kerWitness L ell) (originSite L, (0 : Fin 3)) = 1 := by
    rw [bondEquiv_kerWitness]
    exact gradValue_kerLam_origin hell2 hdvd
  rw [hz, map_zero] at h1
  simp only [Pi.zero_apply] at h1
  exact zero_ne_one h1

/-- **CLAUSE 4b, PROVED about the supplied operator**: the faithful coarse average is NOT
injective, at every tileable lattice with `2 ≤ ell`. -/
theorem qcOp_not_injective {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ¬ Function.Injective (qcOp L ell) := by
  intro hinj
  have hell : 0 < ell := by omega
  have h : qcOp L ell (kerWitness L ell) = qcOp L ell 0 := by
    rw [qcOp_kerWitness hell hdvd, map_zero]
  exact kerWitness_ne_zero hell2 hdvd (hinj h)

#print axioms lineCoarseRestrict_gradValue_kerLam
#print axioms gradValue_kerLam_origin
#print axioms qcOp_not_injective

/-! ## §6 — clause 3, in BOTH norm classes, as theorems about the supplied operator

CMP98 p.36 (126) reads `|(Q(V₀)A)_c| ≦ ‖A‖ + O(1)L²α₀‖A‖` — an ABSOLUTE bound whose leading
constant is `‖Q₀‖ ≤ 1`, stated in the SUP norm on bond fields. `Claim18Carrier.Clauses` clause 3
is in the carrier's OPERATOR norm. Rather than pick one and disclose the other as a modelling
simplification (which is what the previous statement did), BOTH are proved here for the SAME
supplied operator:

* `qc_sup_bound` — the literal (126) shape: if `|A_z| ≤ M` for every fine bond then
  `|(𝒬_c A)_c| ≤ M` at every coarse bond. The mechanism is that the `ell⁴` weights are
  nonnegative and sum to exactly `1`, which is what makes the faithful `Q_k` an average and what
  the unfaithful `LatticeOperators.coarseRestrict` fails.
* `qcOp_opNorm_le_one` — the `ℓ²` operator norm, which is the functional the carrier clause
  consumes. Proved through the strictly stronger `qcOp_norm_sq_le`: `‖𝒬_c A‖² ≤ ell^{-3}‖A‖²`.
-/

/-- **CMP98 (126) IN ITS OWN NORM CLASS.** Nonnegative weights of total mass `1`. -/
theorem qc_sup_bound {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (a : Bond L → ℝ) (M : ℝ) (hM : ∀ z, |a z| ≤ M) (b : CoarseBond L ell) :
    |lineCoarseRestrict ell a b| ≤ M := by
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (originSite L, (0 : Fin 3)))
  have hne : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  have hpos : (0 : ℝ) < (ell : ℝ) := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    exact this
  -- each segment integral is bounded by `ell * M`
  have hseg : ∀ x : PeriodicLatticeSite L, |lineIntegralValue ell a x μ| ≤ (ell : ℝ) * M := by
    intro x
    rw [lineIntegralValue]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => hM _)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the block sum is bounded by `ell^3 * (ell * M)`
  have hblk : |∑ x ∈ blockOf y ell, lineIntegralValue ell a x μ|
      ≤ ((ell : ℝ) ^ 3) * ((ell : ℝ) * M) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun x _ => hseg x)) ?_
    rw [Finset.sum_const, card_blockOf_of_coarse hdvd hy, nsmul_eq_mul]
    push_cast
    exact le_refl _
  rw [lineCoarseRestrict, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (ell : ℝ) ^ 4)]
  have hstep : (1 / (ell : ℝ) ^ 4) * |∑ x ∈ blockOf y ell, lineIntegralValue ell a x μ|
      ≤ (1 / (ell : ℝ) ^ 4) * (((ell : ℝ) ^ 3) * ((ell : ℝ) * M)) := by
    exact mul_le_mul_of_nonneg_left hblk (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  field_simp <;> ring

#print axioms qc_sup_bound

/-- `‖·‖²` on `BondSpace`, coordinatewise. -/
theorem bondSpace_norm_sq (A : BondSpace L) : ‖A‖ ^ 2 = ∑ b : Bond L, (bondEquiv L A b) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun b _ => by rw [Real.norm_eq_abs, sq_abs]; rfl

/-- `‖·‖²` on `CoarseBondSpace`, coordinatewise. -/
theorem coarseBondSpace_norm_sq {ell : ℕ} (F : CoarseBondSpace L ell) :
    ‖F‖ ^ 2 = ∑ b : CoarseBond L ell, (coarseBondEquiv L ell F b) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun b _ => by rw [Real.norm_eq_abs, sq_abs]; rfl

/-- **The reindexing identity behind the `ℓ²` bound.** Summing the squared fine values read by
every coarse bond counts each fine bond exactly `ell` times: the blocks TILE the torus
(`PoincareBridge.sum_eq_blocks`, reused) and, at each fixed offset `j`, the `μ`-path is a
BIJECTION of sites (`pathStep_bijective`). -/
theorem read_sum_eq {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (a : Bond L → ℝ) :
    (∑ b : CoarseBond L ell, ∑ x ∈ blockOf b.1.1 ell, ∑ j ∈ Finset.range ell,
        (a (pathStep x b.2 j, b.2)) ^ 2)
      = (ell : ℝ) * ∑ z : Bond L, (a z) ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have hstep : ∀ μ : Fin 3,
      (∑ yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
          ∑ x ∈ blockOf ((yc, μ) : CoarseBond L ell).1.1 ell, ∑ j ∈ Finset.range ell,
            (a (pathStep x ((yc, μ) : CoarseBond L ell).2 j,
              ((yc, μ) : CoarseBond L ell).2)) ^ 2)
        = (ell : ℝ) * ∑ z : PeriodicLatticeSite L, (a (z, μ)) ^ 2 := by
    intro μ
    have hsets : @Finset.univ {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}
          (instFintypeCoarseSite L ell)
        = @Finset.univ {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}
          (Finset.Subtype.fintype (CoarseLattice L ell)) := by
      ext x
      simp
    have h1 : (∑ yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
          ∑ x ∈ blockOf (yc : PeriodicLatticeSite L) ell, ∑ j ∈ Finset.range ell,
            (a (pathStep x μ j, μ)) ^ 2)
        = ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, ∑ j ∈ Finset.range ell,
            (a (pathStep x μ j, μ)) ^ 2 :=
      (Finset.sum_congr hsets (fun _ _ => rfl)).trans
        (Finset.sum_coe_sort (CoarseLattice L ell)
          (fun y => ∑ x ∈ blockOf y ell, ∑ j ∈ Finset.range ell, (a (pathStep x μ j, μ)) ^ 2))
    rw [h1]
    have h2 : ∀ y : PeriodicLatticeSite L,
        (∑ x ∈ blockOf y ell, ∑ j ∈ Finset.range ell, (a (pathStep x μ j, μ)) ^ 2)
          = ∑ j ∈ Finset.range ell, ∑ x ∈ blockOf y ell, (a (pathStep x μ j, μ)) ^ 2 :=
      fun y => Finset.sum_comm
    rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm]
    have h3 : ∀ j : ℕ,
        (∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, (a (pathStep x μ j, μ)) ^ 2)
          = ∑ z : PeriodicLatticeSite L, (a (z, μ)) ^ 2 := by
      intro j
      rw [← AdalyFormal.Balaban.PoincareBridge.sum_eq_blocks ell hell hdvd
        (fun x => (a (pathStep x μ j, μ)) ^ 2)]
      exact (pathStep_bijective μ j).sum_comp (fun z => (a (z, μ)) ^ 2)
    rw [Finset.sum_congr rfl (fun j _ => h3 j), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun μ _ => hstep μ), ← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- **THE `ℓ²` BOUND, quantitative**: `‖𝒬_c A‖² ≤ ell^{-3}·‖A‖²`. Cauchy–Schwarz on the `ell⁴`
terms each coarse bond reads, then `read_sum_eq`. -/
theorem qcOp_norm_sq_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : BondSpace L) :
    ‖qcOp L ell A‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 3) * ‖A‖ ^ 2 := by
  classical
  set a : Bond L → ℝ := bondEquiv L A with ha
  have hpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hne : (ell : ℝ) ≠ 0 := ne_of_gt hpos
  -- per coarse bond
  have hCS : ∀ b : CoarseBond L ell,
      (lineCoarseRestrict ell a b) ^ 2
        ≤ (1 / (ell : ℝ) ^ 4) * ∑ x ∈ blockOf b.1.1 ell, ∑ j ∈ Finset.range ell,
            (a (pathStep x b.2 j, b.2)) ^ 2 := by
    rintro ⟨⟨y, hy⟩, μ⟩
    have hprod : (∑ x ∈ blockOf y ell, lineIntegralValue ell a x μ)
        = ∑ p ∈ (blockOf y ell) ×ˢ (Finset.range ell), a (pathStep p.1 μ p.2, μ) := by
      rw [Finset.sum_product]
      rfl
    have hprod2 : (∑ p ∈ (blockOf y ell) ×ˢ (Finset.range ell),
          (a (pathStep p.1 μ p.2, μ)) ^ 2)
        = ∑ x ∈ blockOf y ell, ∑ j ∈ Finset.range ell, (a (pathStep x μ j, μ)) ^ 2 :=
      Finset.sum_product _ _ _
    have hcard : (((blockOf y ell) ×ˢ (Finset.range ell)).card : ℝ) = (ell : ℝ) ^ 4 := by
      rw [Finset.card_product, card_blockOf_of_coarse hdvd hy, Finset.card_range]
      push_cast
      ring
    have hcs := sq_sum_le_card_mul_sum_sq (s := (blockOf y ell) ×ˢ (Finset.range ell))
      (f := fun p => a (pathStep p.1 μ p.2, μ))
    rw [hcard] at hcs
    have hLHS : (lineCoarseRestrict ell a (⟨y, hy⟩, μ)) ^ 2
        = (1 / (ell : ℝ) ^ 4) ^ 2 *
            (∑ p ∈ (blockOf y ell) ×ˢ (Finset.range ell), a (pathStep p.1 μ p.2, μ)) ^ 2 := by
      rw [lineCoarseRestrict, hprod, mul_pow]
    rw [hLHS, ← hprod2]
    have hnn : (0 : ℝ) ≤ (1 / (ell : ℝ) ^ 4) ^ 2 := by positivity
    calc (1 / (ell : ℝ) ^ 4) ^ 2 *
          (∑ p ∈ (blockOf y ell) ×ˢ (Finset.range ell), a (pathStep p.1 μ p.2, μ)) ^ 2
        ≤ (1 / (ell : ℝ) ^ 4) ^ 2 * ((ell : ℝ) ^ 4 *
            ∑ p ∈ (blockOf y ell) ×ˢ (Finset.range ell), (a (pathStep p.1 μ p.2, μ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hnn
      _ = (1 / (ell : ℝ) ^ 4) *
            ∑ p ∈ (blockOf y ell) ×ˢ (Finset.range ell), (a (pathStep p.1 μ p.2, μ)) ^ 2 := by
          field_simp <;> ring
  -- assemble
  rw [coarseBondSpace_norm_sq, bondSpace_norm_sq]
  have hpt : ∀ b : CoarseBond L ell,
      coarseBondEquiv L ell (qcOp L ell A) b = lineCoarseRestrict ell a b := by
    intro b
    rw [qcOp_apply]
  have hsum : (∑ b : CoarseBond L ell, (coarseBondEquiv L ell (qcOp L ell A) b) ^ 2)
      ≤ ∑ b : CoarseBond L ell, (1 / (ell : ℝ) ^ 4) *
          ∑ x ∈ blockOf b.1.1 ell, ∑ j ∈ Finset.range ell, (a (pathStep x b.2 j, b.2)) ^ 2 := by
    refine Finset.sum_le_sum fun b _ => ?_
    rw [hpt b]
    exact hCS b
  refine le_trans hsum ?_
  rw [← Finset.mul_sum, read_sum_eq hell hdvd a]
  rw [← ha]
  have : (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) * ∑ z : Bond L, (a z) ^ 2)
      = (1 / (ell : ℝ) ^ 3) * ∑ z : Bond L, (a z) ^ 2 := by
    field_simp <;> ring
  rw [this]

/-- **CLAUSE 3, PROVED about the supplied operator, in the carrier's own norm.**
`‖𝒬_c‖ ≤ 1`. -/
theorem qcOp_opNorm_le_one {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖qcOp L ell‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => ?_
  rw [one_mul]
  have hpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hone : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h := qcOp_norm_sq_le hell hdvd A
  have h3 : (1 / (ell : ℝ) ^ 3) * ‖A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    have hle : (1 / (ell : ℝ) ^ 3) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have h2 : (1 : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
      nlinarith [h2, hone]
    nlinarith [sq_nonneg ‖A‖]
  calc ‖qcOp L ell A‖ = Real.sqrt (‖qcOp L ell A‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖A‖ ^ 2) := Real.sqrt_le_sqrt (le_trans h h3)
    _ = ‖A‖ := Real.sqrt_sq (norm_nonneg _)

/-- **CLAUSE 3 in the exact shape `Claim18Carrier.Clauses` consumes**, for any nonnegative
`Ccorr`, `α₀` and any real `Lreal`. -/
theorem qcOp_clause3 {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lreal Ccorr α₀ : ℝ) (hC : 0 ≤ Ccorr) (hα : 0 ≤ α₀) :
    ‖qcOp L ell‖ ≤ 1 + Ccorr * Lreal ^ 2 * α₀ := by
  have h1 : (0 : ℝ) ≤ Ccorr * Lreal ^ 2 * α₀ := by positivity
  linarith [qcOp_opNorm_le_one hell hdvd]

/-- **The sharp form of the `ℓ²` bound**: `‖𝒬_c‖ ≤ √(ell^{-3})`. Stated as a declaration rather
than left in the module docstring (§GREEN-8). -/
theorem qcOp_opNorm_le_sqrt {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖qcOp L ell‖ ≤ Real.sqrt (1 / (ell : ℝ) ^ 3) := by
  have hpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hnn : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 3 := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun A => ?_
  have h := qcOp_norm_sq_le hell hdvd A
  calc ‖qcOp L ell A‖ = Real.sqrt (‖qcOp L ell A‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1 / (ell : ℝ) ^ 3) * ‖A‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (1 / (ell : ℝ) ^ 3) * ‖A‖ := by
        rw [Real.sqrt_mul hnn, Real.sqrt_sq (norm_nonneg _)]

#print axioms bondSpace_norm_sq
#print axioms read_sum_eq
#print axioms qcOp_norm_sq_le
#print axioms qcOp_opNorm_le_one
#print axioms qcOp_opNorm_le_sqrt
#print axioms qcOp_clause3

/-! ## §7 — THE PINNED BUNDLE, and the exact measurement of what freedom is left

`SuppliedClauses` is `Claim18Carrier.Clauses` with `Qc` and `Qc_inv` REPLACED BY THE SUPPLIED
OPERATORS. There is no existential over them: the equation `Qc = 𝒬_c` is discharged by
instantiation, which is the strongest form an equation can take in a dependent type theory.

`suppliedClauses_iff` then MEASURES what the bundle still leaves free. It is an `↔`, so it is not
a claim but a computation: four of the six clauses are theorems (§3–§6), and what remains is a
condition on `C⁽²⁾` ALONE. -/

/-- The lattice origin is a coarse site. -/
theorem originSite_mem_coarse {ell : ℕ} : originSite L ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice]
  intro ν
  show (0 : ℕ) % ell = 0
  exact Nat.zero_mod ell

/-- A named coarse bond, so the coarse space is provably not a point. -/
def originCoarseBond (L : PeriodicLatticeExtent) (ell : ℕ) : CoarseBond L ell :=
  (⟨originSite L, originSite_mem_coarse⟩, 0)

theorem qcSection_ne_zero {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    qcSection L ell ≠ 0 := by
  intro hz
  have hid : (ContinuousLinearMap.id ℝ (CoarseBondSpace L ell)) = 0 := by
    rw [← qc_comp_section hell hdvd, hz, ContinuousLinearMap.comp_zero]
  have h1 : (coarseBondEquiv L ell).symm (fun _ => (1 : ℝ)) = 0 := by
    have h := congrArg (fun T : CoarseBondSpace L ell →L[ℝ] CoarseBondSpace L ell =>
      T ((coarseBondEquiv L ell).symm (fun _ => (1 : ℝ)))) hid
    simpa using h
  have h2 := congrArg (coarseBondEquiv L ell) h1
  rw [LinearEquiv.apply_symm_apply, map_zero] at h2
  have h3 := congrFun h2 (originCoarseBond L ell)
  norm_num at h3

#print axioms qcSection_ne_zero

/-- **CLAIM 18'S CLAUSE BUNDLE WITH `𝒬_c` AND ITS SECTION SUPPLIED BY EQUATION.** The only thing
still quantified over is Bałaban's `C⁽²⁾`. -/
def SuppliedClauses (L : PeriodicLatticeExtent) (ell : ℕ) (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    (C2 : BondSpace L →L[ℝ] BondSpace L) : Prop :=
  Claim18Carrier.Clauses Lreal d Ccorr α₀ C2 (qcOp L ell) (qcSection L ell)

/-- The supplied form IMPLIES the abstract two-space form — the bridge that lets every consumer of
`Claim18Carrier.Clauses` be fed the pinned statement without restating anything. -/
theorem suppliedClauses_imp_clauses {ell : ℕ} (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : BondSpace L →L[ℝ] BondSpace L} (h : SuppliedClauses L ell Lreal d Ccorr α₀ C2) :
    Claim18Carrier.Clauses (Hfine := BondSpace L) (Hcoarse := CoarseBondSpace L ell)
      Lreal d Ccorr α₀ C2 (qcOp L ell) (qcSection L ell) := h

/-- **THE MEASUREMENT.** With `𝒬_c` and its section supplied, the six-clause bundle is EQUIVALENT
to a three-clause condition on `C⁽²⁾` alone. Clauses 1, 2, 3 and 4b have become theorems
(`qc_comp_section`, `qcSection_injective`, `qcOp_clause3`, `qcOp_not_injective`), so they impose
nothing on the witness; the surviving content is exactly the `C⁽²⁾` conditions.

Read this as the honest analogue of `carrier_clauses_land_by_linear_algebra`: it does not say the
bundle is empty or full, it says PRECISELY which of its clauses can still be traded against a
choice. -/
theorem suppliedClauses_iff {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ) (hC : 0 ≤ Ccorr) (hα : 0 ≤ α₀)
    (C2 : BondSpace L →L[ℝ] BondSpace L) :
    SuppliedClauses L ell Lreal d Ccorr α₀ C2 ↔
      ((1 ≤ Module.finrank ℝ (BondSpace L) → 1 ≤ ‖C2‖) ∧
        ‖C2 ∘L qcSection L ell‖ ≤ Lreal ^ ((d : ℝ) - 1) ∧
        C2 ∘L qcSection L ell ≠ 0) := by
  have hell : 0 < ell := by omega
  constructor
  · rintro ⟨-, -, -, ⟨h4a, -⟩, h5, h6⟩
    exact ⟨h4a, h5, h6⟩
  · rintro ⟨h4a, h5, h6⟩
    exact ⟨qc_comp_section hell hdvd, qcSection_injective hell hdvd,
      qcOp_clause3 hell hdvd Lreal Ccorr α₀ hC hα,
      ⟨h4a, qcOp_not_injective hell2 hdvd⟩, h5, h6⟩

#print axioms suppliedClauses_imp_clauses
#print axioms suppliedClauses_iff

/-! ## §8 — THE RESIDUAL, STATED AS A THEOREM RATHER THAN A LABEL

`suppliedClauses_iff` is the whole of `[RES-O1-NEEDS-C2]` in one line: after the `𝒬_c` equation,
the bundle constrains NOTHING except `C⁽²⁾`, and the three surviving conditions are one guarded
lower bound, one upper bound and one non-degeneracy — a shape that an upper bound on a composition
can always meet by rescaling. `compute/qc_equation/qc_attacks.lean` compiles the witness that does
exactly that, OUTSIDE the package (per `Spine.lean` §3b.1: a positive witness inside the package
would be a hole next to `main`).

So the honest statement of where Claim 18 now stands is:

* the `𝒬_c` freedom is GONE, by equation, and the four clauses it used to absorb are theorems;
* the `C⁽²⁾` freedom is UNTOUCHED, and it is the whole of what remains;
* the next equation the statement needs is one pinning `C⁽²⁾` — the second-order term of the
  effective action — which this tree does not define. That is not a re-statement of the same
  residual under a new name: `carrier_clauses_land_by_linear_algebra` could choose `Qc` itself and
  therefore made every clause negotiable; `suppliedClauses_iff` proves that only three inequalities
  about one operator are negotiable now, and names that operator.
-/

/-- **The zero `C⁽²⁾` dies against the pinned bundle** — the first junk attack on the new
statement, and it dies by clause 6 exactly as it did against the abstract bundle. -/
theorem supplied_blocks_zero_C2 {ell : ℕ} (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ) :
    ¬ SuppliedClauses L ell Lreal d Ccorr α₀ 0 :=
  Claim18Carrier.blocks_zero_C2 Lreal d Ccorr α₀ (qcOp L ell) (qcSection L ell)

/-- **Every `C⁽²⁾` annihilating the range of the supplied section dies** — the zero-transfer
family, which is the class the two-space carrier newly opened. -/
theorem supplied_blocks_zero_transfer {ell : ℕ} (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : BondSpace L →L[ℝ] BondSpace L} (hz : C2 ∘L qcSection L ell = 0) :
    ¬ SuppliedClauses L ell Lreal d Ccorr α₀ C2 :=
  Claim18Carrier.blocks_zero_transfer Lreal d Ccorr α₀ hz

/-- Clause 4b, projected out of the pinned bundle. -/
theorem supplied_forces_noninjective {ell : ℕ} (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : BondSpace L →L[ℝ] BondSpace L} (h : SuppliedClauses L ell Lreal d Ccorr α₀ C2) :
    ¬ Function.Injective (qcOp L ell) := h.2.2.2.1.2

/-- **The pinned bundle still forces the dimension drop** — inherited from
`Claim18Carrier.forces_dimension_drop`, now as a statement about the REAL spaces: the coarse bond
space is strictly smaller than the fine bond space. -/
theorem supplied_forces_dimension_drop {ell : ℕ} (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : BondSpace L →L[ℝ] BondSpace L} (h : SuppliedClauses L ell Lreal d Ccorr α₀ C2) :
    Module.finrank ℝ (CoarseBondSpace L ell) < Module.finrank ℝ (BondSpace L) :=
  Claim18Carrier.forces_dimension_drop Lreal d Ccorr α₀ h

#print axioms supplied_blocks_zero_C2
#print axioms supplied_blocks_zero_transfer
#print axioms supplied_forces_noninjective
#print axioms supplied_forces_dimension_drop

/-! ### §8a — `ell = 1`: the pinned bundle is PROVED EMPTY there

`§DEGEN` of `compute/BUILD_STANDARDS.md` lists `ell = 1` as this tree's standing degenerate point.
For the pinned bundle it is not merely degenerate, it is empty, and the proof is short: at `ell = 1`
each block is a single site and each line integral is a single bond, so `𝒬_c` is a relabelling of
the fine bond field — INJECTIVE — and clause 4b is false. -/

/-- At `ell = 1` a block is a single site. -/
theorem blockOf_one (y : PeriodicLatticeSite L) : blockOf y 1 = {y} := by
  ext x
  rw [mem_blockOf, Finset.mem_singleton]
  constructor
  · intro h
    funext ν
    apply Fin.ext
    have hν := h ν
    omega
  · rintro rfl
    intro ν
    omega

/-- **At `ell = 1` the faithful average is INJECTIVE** — it reads off the fine bond field. -/
theorem qcOp_one_injective : Function.Injective (qcOp L 1) := by
  intro A B hAB
  apply (bondEquiv L).injective
  funext b
  obtain ⟨z, μ⟩ := b
  have hy : z ∈ CoarseLattice L 1 := by
    rw [mem_CoarseLattice]
    intro ν
    exact Nat.mod_one _
  have hval : ∀ C : BondSpace L,
      coarseBondEquiv L 1 (qcOp L 1 C) ((⟨z, hy⟩, μ) : CoarseBond L 1) = bondEquiv L C (z, μ) := by
    intro C
    rw [qcOp_apply, lineCoarseRestrict, blockOf_one, Finset.sum_singleton, lineIntegralValue]
    simp
  have h := congrArg (fun F : CoarseBondSpace L 1 =>
    coarseBondEquiv L 1 F ((⟨z, hy⟩, μ) : CoarseBond L 1)) hAB
  rw [hval A, hval B] at h
  exact h

/-- **THE PINNED BUNDLE IS EMPTY AT `ell = 1`**, at every `Lreal`, `d`, `Ccorr`, `α₀`. -/
theorem supplied_unsatisfiable_at_ell_one (Lreal : ℝ) (d : ℕ) (Ccorr α₀ : ℝ) :
    ¬ ∃ C2 : BondSpace L →L[ℝ] BondSpace L, SuppliedClauses L 1 Lreal d Ccorr α₀ C2 := by
  rintro ⟨C2, h⟩
  exact (supplied_forces_noninjective Lreal d Ccorr α₀ h) qcOp_one_injective

#print axioms blockOf_one
#print axioms qcOp_one_injective
#print axioms supplied_unsatisfiable_at_ell_one

/-! ### §8b — the degenerate carriers the junk attacks aim at, closed by facts about the SUPPLIED
operators rather than by clauses

With `𝒬_c` and its section supplied, most of the junk families are not merely blocked, they are
NOT SUBSTITUTABLE: there is no witness slot to put them in. What is left to check is that the
supplied operators are themselves not degenerate, and that the carrier is not one of `§DEGEN`'s
collapse points. Both are theorems below. -/

/-- The supplied average is not the zero operator. -/
theorem qcOp_ne_zero {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    qcOp L ell ≠ 0 := by
  intro hz
  have hid : (ContinuousLinearMap.id ℝ (CoarseBondSpace L ell)) = 0 := by
    rw [← qc_comp_section hell hdvd, hz, ContinuousLinearMap.zero_comp]
  have h1 : (coarseBondEquiv L ell).symm (fun _ => (1 : ℝ)) = 0 := by
    have h := congrArg (fun T : CoarseBondSpace L ell →L[ℝ] CoarseBondSpace L ell =>
      T ((coarseBondEquiv L ell).symm (fun _ => (1 : ℝ)))) hid
    simpa using h
  have h2 := congrArg (coarseBondEquiv L ell) h1
  rw [LinearEquiv.apply_symm_apply, map_zero] at h2
  have h3 := congrFun h2 (originCoarseBond L ell)
  norm_num at h3

/-- The coarse bond space is not a point. -/
theorem one_le_finrank_coarse {ell : ℕ} : 1 ≤ Module.finrank ℝ (CoarseBondSpace L ell) := by
  rw [finrank_euclideanSpace]
  exact Fintype.card_pos_iff.mpr ⟨originCoarseBond L ell⟩

/-- **THE CARRIER IS A GENUINE COARSENING, PROVED WITHOUT ASSUMING THE BUNDLE.** At `2 ≤ ell` the
coarse bond space is strictly smaller than the fine bond space — so the `Hcoarse := Hfine` collapse
that killed the single-carrier encoding is not merely blocked by a clause here, it is false about
the actual spaces. -/
theorem coarse_finrank_lt {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Module.finrank ℝ (CoarseBondSpace L ell) < Module.finrank ℝ (BondSpace L) := by
  have hell : 0 < ell := by omega
  have hsurj : Function.Surjective ((qcOp L ell : BondSpace L →ₗ[ℝ] CoarseBondSpace L ell)) :=
    qcOp_surjective hell hdvd
  have hrange : LinearMap.range (qcOp L ell : BondSpace L →ₗ[ℝ] CoarseBondSpace L ell) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hker : LinearMap.ker (qcOp L ell : BondSpace L →ₗ[ℝ] CoarseBondSpace L ell) ≠ ⊥ := by
    intro hb
    exact qcOp_not_injective hell2 hdvd (LinearMap.ker_eq_bot.mp hb)
  have hkerpos :
      0 < Module.finrank ℝ (LinearMap.ker (qcOp L ell : BondSpace L →ₗ[ℝ] CoarseBondSpace L ell)) := by
    rcases Nat.eq_zero_or_pos
        (Module.finrank ℝ (LinearMap.ker (qcOp L ell : BondSpace L →ₗ[ℝ] CoarseBondSpace L ell)))
      with hz | hp
    · exact absurd (Submodule.finrank_eq_zero.mp hz) hker
    · exact hp
  have hrk :=
    LinearMap.finrank_range_add_finrank_ker (qcOp L ell : BondSpace L →ₗ[ℝ] CoarseBondSpace L ell)
  rw [hrange, finrank_top] at hrk
  omega

/-- **`§DEGEN`'s `finrank ≤ 1` point is not reachable**: the fine bond space has dimension at
least `2` whenever `2 ≤ ell` and the lattice tiles. -/
theorem two_le_finrank_bondSpace {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    2 ≤ Module.finrank ℝ (BondSpace L) := by
  have h1 := coarse_finrank_lt (L := L) hell2 hdvd
  have h2 := one_le_finrank_coarse (L := L) (ell := ell)
  omega

#print axioms qcOp_ne_zero
#print axioms one_le_finrank_coarse
#print axioms coarse_finrank_lt
#print axioms two_le_finrank_bondSpace

/-! ### §8c — BAŁABAN'S CONSTANT EXTENSION IS **NOT** AN EXACT SECTION, PROVED

The module docstring's family table records, as HAND ARITHMETIC, that the "spread the coarse value
evenly over the block" lift is not a right inverse of the faithful average. That row is the
uncomfortable one, so it is not left at hand-arithmetic status: the theorem below proves it, in
general, without computing any of the block counts. The mechanism is the one the counts encode —
the segment `[x, x + ell·e_μ]` starting at the LAST layer of `B(y)` leaves the block, so the coarse
value at the NEIGHBOURING coarse bond leaks into `(𝒬_c s_const f)(y,μ)`.

This is why `qcSection` is the last-layer lift and not the constant extension: clause 1 of
`Claim18Carrier.Clauses` demands an EXACT right inverse, and Bałaban's spreading map is not one. -/

/-- **The constant extension** `s_const f (z,μ) := f(π z, μ)` — spread the coarse value over every
fine bond of the block, weight `1`. -/
noncomputable def constExtLift (ell : ℕ) (f : CoarseBond L ell → ℝ) (b : Bond L) : ℝ :=
  f (⟨blockCorner ell b.1, blockCorner_mem b.1⟩, b.2)

/-- The site `(ell-1)·e_0` — the LAST layer of the origin block in direction `0`. -/
def lastLayerSite (L : PeriodicLatticeExtent) (ell : ℕ) (h : ell < L 0 + 1) :
    PeriodicLatticeSite L :=
  Function.update (originSite L) 0 ⟨ell - 1, by omega⟩

/-- The site `ell·e_0` — the corner of the NEXT coarse block in direction `0`. -/
def nextCornerSite (L : PeriodicLatticeExtent) (ell : ℕ) (h : ell < L 0 + 1) :
    PeriodicLatticeSite L :=
  Function.update (originSite L) 0 ⟨ell, h⟩

theorem nextCornerSite_mem_coarse {ell : ℕ} (h : ell < L 0 + 1) :
    nextCornerSite L ell h ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice]
  intro ν
  by_cases hν : ν = 0
  · subst hν
    show (ell : ℕ) % ell = 0
    exact Nat.mod_self ell
  · show ((Function.update (originSite L) 0 (⟨ell, h⟩ : Fin (L 0 + 1))) ν).val % ell = 0
    rw [Function.update_of_ne hν]
    show (0 : ℕ) % ell = 0
    exact Nat.zero_mod ell

theorem nextCornerSite_ne_origin {ell : ℕ} (hell2 : 2 ≤ ell) (h : ell < L 0 + 1) :
    nextCornerSite L ell h ≠ originSite L := by
  intro hz
  have hv := congrArg (fun z : PeriodicLatticeSite L => (z 0).val) hz
  simp only [nextCornerSite, Function.update_self] at hv
  have : (originSite L (0 : Fin 3)).val = 0 := rfl
  omega

theorem lastLayerSite_mem_block {ell : ℕ} (hell2 : 2 ≤ ell) (h : ell < L 0 + 1) :
    lastLayerSite L ell h ∈ blockOf (originSite L) ell := by
  rw [mem_blockOf]
  intro ν
  have h0 : (originSite L ν).val = 0 := rfl
  by_cases hν : ν = 0
  · subst hν
    simp only [lastLayerSite, Function.update_self]
    omega
  · have hv : ((lastLayerSite L ell h) ν).val = 0 := by
      change ((Function.update (originSite L) 0
        (⟨ell - 1, by omega⟩ : Fin (L 0 + 1))) ν).val = 0
      rw [Function.update_of_ne hν]
      rfl
    omega

/-- The one step that leaves the block: from the last layer, one forward step in direction `0`
lands in the NEXT coarse block. -/
theorem blockCorner_step_out {ell : ℕ} (hell2 : 2 ≤ ell) (h : ell < L 0 + 1) :
    blockCorner ell (pathStep (lastLayerSite L ell h) 0 1) = nextCornerSite L ell h := by
  funext ν
  apply Fin.ext
  rw [blockCorner_val]
  by_cases hν : ν = 0
  · subst hν
    have hval : ((pathStep (lastLayerSite L ell h) 0 1) 0).val = ell := by
      rw [pathStep_apply_self_val]
      have : ((lastLayerSite L ell h) (0 : Fin 3)).val = ell - 1 := by
        simp only [lastLayerSite, Function.update_self]
      rw [this]
      have hsum : ell - 1 + 1 = ell := by omega
      rw [hsum]
      exact Nat.mod_eq_of_lt h
    have hmod : ((pathStep (lastLayerSite L ell h) 0 1) 0).val % ell = 0 := by
      rw [hval]; exact Nat.mod_self ell
    have hnext : (nextCornerSite L ell h (0 : Fin 3)).val = ell := by
      simp only [nextCornerSite, Function.update_self]
    omega
  · rw [pathStep_apply_ne _ 0 ν 1 hν]
    have hls : ((lastLayerSite L ell h) ν).val = 0 := by
      change ((Function.update (originSite L) 0
        (⟨ell - 1, by omega⟩ : Fin (L 0 + 1))) ν).val = 0
      rw [Function.update_of_ne hν]
      rfl
    have hnc : (nextCornerSite L ell h ν).val = 0 := by
      change ((Function.update (originSite L) 0 (⟨ell, h⟩ : Fin (L 0 + 1))) ν).val = 0
      rw [Function.update_of_ne hν]
      rfl
    rw [hls, hnc, Nat.zero_mod]

/-- **THE THEOREM.** For every tileable lattice with `2 ≤ ell` and at least two coarse sites in
direction `0`, the constant extension is NOT a right inverse of the faithful average: the coarse
indicator of the NEIGHBOURING coarse bond has strictly positive average at the origin coarse bond,
where the indicator itself is `0`. Sorry-free, and general in `L` and `ell`. -/
theorem constExtLift_not_section {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hlt : ell < L 0 + 1) :
    ∃ f : CoarseBond L ell → ℝ,
      lineCoarseRestrict ell (constExtLift ell f) ≠ f := by
  classical
  have hell : 0 < ell := by omega
  set c₁ : CoarseBond L ell := (⟨nextCornerSite L ell hlt, nextCornerSite_mem_coarse hlt⟩, 0)
    with hc₁
  set f : CoarseBond L ell → ℝ := fun c => if c = c₁ then (1 : ℝ) else 0 with hf
  refine ⟨f, ?_⟩
  intro heq
  set c₀ : CoarseBond L ell := (⟨originSite L, originSite_mem_coarse⟩, 0) with hc₀
  -- the value of `f` at the origin coarse bond is `0`
  have hf0 : f c₀ = 0 := by
    simp only [hf]
    refine if_neg ?_
    intro hcc
    have := congrArg (fun c : CoarseBond L ell => (c.1 : PeriodicLatticeSite L)) hcc
    exact nextCornerSite_ne_origin hell2 hlt this.symm
  -- every term of the double sum is nonnegative
  have hfnn : ∀ b : Bond L, 0 ≤ constExtLift ell f b := by
    intro b
    simp only [constExtLift, hf]
    split_ifs <;> norm_num
  have hlnn : ∀ x : PeriodicLatticeSite L, 0 ≤ lineIntegralValue ell (constExtLift ell f) x 0 := by
    intro x
    rw [lineIntegralValue]
    exact Finset.sum_nonneg fun j _ => hfnn _
  -- the single term that is strictly positive
  have hone : constExtLift ell f (pathStep (lastLayerSite L ell hlt) 0 1, (0 : Fin 3)) = 1 := by
    simp only [constExtLift, hf]
    refine if_pos ?_
    rw [hc₁]
    refine Prod.ext_iff.mpr ⟨?_, rfl⟩
    apply Subtype.ext
    exact blockCorner_step_out hell2 hlt
  have hlpos : 0 < lineIntegralValue ell (constExtLift ell f) (lastLayerSite L ell hlt) 0 := by
    rw [lineIntegralValue]
    refine Finset.sum_pos' (fun j _ => hfnn _) ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [iterate_eq_pathStep, hone]
    norm_num
  have hspos : 0 < ∑ x ∈ blockOf (originSite L) ell,
      lineIntegralValue ell (constExtLift ell f) x 0 :=
    Finset.sum_pos' (fun x _ => hlnn x)
      ⟨lastLayerSite L ell hlt, lastLayerSite_mem_block hell2 hlt, hlpos⟩
  -- so the average at the origin coarse bond is strictly positive, contradicting `f c₀ = 0`
  have hval : lineCoarseRestrict ell (constExtLift ell f) c₀ = f c₀ := congrFun heq c₀
  rw [hf0, lineCoarseRestrict] at hval
  have hcoef : (0 : ℝ) < 1 / (ell : ℝ) ^ 4 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  nlinarith [hspos, hcoef, hval]

/-- **THE S91 CONTROL FOR `constExtLift_not_section`.** The zero coarse field does NOT discharge
that existential: the constant extension of `0` is the zero bond field, whose average is `0`, so the
disequality is FALSE at `f := 0`. The witness therefore has to be, and is, a specific nonzero
indicator. Recorded so the S91 attack on that target is a kernel-checked fact and not a remark. -/
theorem constExtLift_zero_no_discharge {ell : ℕ} :
    lineCoarseRestrict ell (constExtLift ell (0 : CoarseBond L ell → ℝ))
      = (0 : CoarseBond L ell → ℝ) := by
  have hz : constExtLift ell (0 : CoarseBond L ell → ℝ) = (fun _ : Bond L => (0 : ℝ)) := by
    funext b'
    rw [constExtLift]
    rfl
  funext b
  rw [hz, lineCoarseRestrict]
  simp [lineIntegralValue]

#print axioms constExtLift_not_section
#print axioms constExtLift_zero_no_discharge




end AdalyFormal.Balaban.QcEquation
