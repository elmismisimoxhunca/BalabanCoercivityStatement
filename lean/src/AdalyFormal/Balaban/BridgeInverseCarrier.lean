/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BridgeInverseAssembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.longLine false

/-!
# `BridgeInverseCarrier.lean` — the construction at the REAL lattice `Q`, and the `U`-controls

`BridgeInverseAssembly.bridge_constructed` is abstract. This module instantiates it at the
campaign's own objects:

* fine carrier `BondFnL2 L = PiLp 2 (fun _ : Bond L => 𝔰𝔲(2))`;
* coarse carrier `CoarseFnL2 L ell = PiLp 2 (fun _ : CoarseBond L ell => 𝔰𝔲(2))` (§1 — the `L²`
  twin of `FullySupplied.CoarseField`, which carries the sup norm and therefore cannot host an
  inner product);
* `Q := qCLM U ell`, the faithful covariant block average
  `LineIntegralCovariant.lineCoarseRestrictCov U ell`, CMP95 (1.18)/CMP98 (125);
* `Q* := qstarCLM U ell`, its genuine Hilbert-space adjoint — so `hadj` is a THEOREM here.

## The two controls, both directions

**must-not-fire (non-vacuity).** `Nontrivial (CoarseFnL2 L ell)` is PROVED from an exhibited
nonzero element (§2), not assumed; `sOp ≠ 0` and `tOp ≠ 0` come from `BridgeInverseCore`. The
degenerate coarse carrier `EuclideanSpace ℝ (Fin 0)` that satisfied the old bundle cannot occur.

**must-fire (`U`-dependence).** §5 instantiates the whole construction at
`CoercivityRegular.curvedRegularU`, a background with genuine curvature
(`curvedRegularU_curved`) that is NOT a gauge transform of a flat one
(`curvedRegularU_not_gaugeTransform_of_flat`). Nothing in §5 uses `trivialU`. The route it uses is
§4's `range Q` corestriction, which is available at EVERY background; the `U = 1`-only ingredient
(`FullySupplied.qc_comp_suTwoLift`) is confined to §3 and is never invoked in §5.

## Degeneracy guards actually carried

`hell : 0 < ell` and `hdvd : ∀ μ, ell ∣ L μ + 1` (else `blockOf` truncates silently) appear on
every statement that touches a block. §4's single-bond read additionally carries
`hwide : ∀ μ, 2 * ell ≤ L μ + 1`, which excludes the case `L μ + 1 = ell` — "the block IS the whole
torus" — where a fine bond can be reached twice by the same coarse average through the periodic
wrap. At `witL5` (`L μ = 5`) and `ell = 2` both hold: `2 ∣ 6` and `4 ≤ 6`.
-/

namespace AdalyFormal.Balaban.BridgeInverse

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration
  PeriodicLatticeSite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one
  suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice
  mem_CoarseLattice coarseLattice_mem_fits)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCov_trivialU lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero)
open AdalyFormal.Balaban.Q1Real (rZeroA transportPath)
open AdalyFormal.Balaban.FullySupplied (suTwoLift lineCoarseRestrictSuTwo_suTwoLift)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the coarse `L²` carrier and its instances -/

/-- **The coarse `L²` bond-field carrier.** `FullySupplied.CoarseField` carries the *sup* norm
(`Pi.normedAddCommGroup`) and therefore admits no inner product; the bridge needs an inner-product
space, so the `PiLp 2` twin is used here. Same underlying function type, hence every pointwise
identity about `lineCoarseRestrictCov` transports by `rfl`. -/
abbrev CoarseFnL2 (L : PeriodicLatticeExtent) (ell : ℕ) : Type :=
  PiLp 2 (fun _ : CoarseBond L ell => SuTwo)

/-- `𝔰𝔲(2)` is nontrivial — exhibited, not assumed. -/
instance instNontrivialSuTwo : Nontrivial SuTwo :=
  ⟨⟨suTwoWitness, 0, suTwoWitness_ne_zero⟩⟩

/-- The all-zero site, a member of every coarse lattice. -/
theorem siteZeroMem (L : PeriodicLatticeExtent) (ell : ℕ) :
    (fun _ => 0 : PeriodicLatticeSite L) ∈ CoarseLattice L ell :=
  mem_CoarseLattice.mpr (fun _ => by simp)

instance instNonemptyCoarseBond (L : PeriodicLatticeExtent) (ell : ℕ) :
    Nonempty (CoarseBond L ell) :=
  ⟨(⟨(fun _ => 0 : PeriodicLatticeSite L), siteZeroMem L ell⟩, 0)⟩

/-- **Non-vacuity of the coarse carrier, PROVED.** The blind gate's degenerate witness
`K := EuclideanSpace ℝ (Fin 0)` is impossible here. -/
instance instNontrivialCoarseFnL2 (L : PeriodicLatticeExtent) (ell : ℕ) :
    Nontrivial (CoarseFnL2 L ell) := by
  refine ⟨⟨WithLp.toLp 2 (fun _ => suTwoWitness), 0, ?_⟩⟩
  intro hcon
  have h := congrFun (congrArg (fun u : CoarseFnL2 L ell => WithLp.ofLp u) hcon)
    (Classical.arbitrary (CoarseBond L ell))
  simp only [WithLp.ofLp_toLp] at h
  exact suTwoWitness_ne_zero (by simpa using h)

/-! ## §2 — the real `Q`, its adjoint, and `hadj` as a theorem -/

/-- **`Q_k(U)` on the `L²` carriers** — the faithful covariant line-integral block average. -/
noncomputable def qCLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) : BondFnL2 L →L[ℝ] CoarseFnL2 L ell :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (CoarseBond L ell → SuTwo)).symm.toLinearMap.comp
      ((lineCoarseRestrictCovLM U ell).comp
        (WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)).toLinearMap))

theorem qCLM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (A : BondFnL2 L) (b : CoarseBond L ell) :
    WithLp.ofLp (qCLM U ell A) b = lineCoarseRestrictCov U ell (WithLp.ofLp A) b := rfl

/-- **`Q*`, the genuine Hilbert-space adjoint**, built with the tree's own recipe for this carrier
(`CStarDeltaKCOperator.bondAdjoint`, LAW-19): the BARE `LinearMap.adjoint`, whose type mentions no
topology. ~~under a `letI` that pins the `PiLp` normed structure. `ContinuousLinearMap.adjoint`
CANNOT be applied here — its type fixes the topology through `NormedAddCommGroup`, which does not
unify with `PiLp.topologicalSpace` (measured: `compute/bridge_inverses/` probe 2/3).~~

**⚠ SUPERSEDED (S75, 2026-08-09, `compute/norm_diamond_install/`) — both struck clauses are now
false, for two DIFFERENT reasons, and the difference matters.**

1. The two `letI`s are gone. On `BondFnL2 L` they were needed because
   `CovariantOperators.instNormedAddCommGroupBondFnL2` (frozen at the L²-operator fibre) won
   synthesis; that instance has been deleted, and ordinary search now returns exactly the instance
   the `letI` installed. On `CoarseFnL2 L ell` they were **never** needed: that carrier never had a
   frozen instance, and this file's `letI` on it was copied from the bond side.
2. `ContinuousLinearMap.adjoint` applies on BOTH carriers, and across them. Re-measured in this
   tree with no override — `compute/norm_diamond_install/probe/AdjointProbe.lean`
   (`logs/adjoint_probe.log`, exit=0, all declarations on `[propext, Classical.choice, Quot.sound]`):
   `A2` on `BondFnL2`, `B2` on `CoarseFnL2`, and `C1` on `BondFnL2 →L[ℝ] CoarseFnL2` — the exact
   shape this definition needs. For `CoarseFnL2` the struck sentence was **already** false before
   the deletion (`compute/norm_diamond/logs/diamond2.log` C5): it predates `SuTwoInner.lean`'s
   uniformity repair and was never re-measured after it.

`qstarLM` is deliberately left on the bare `LinearMap.adjoint` route. Nothing forces that any more;
it is kept because rewriting it would change `qstarCLM`'s definitional unfolding and every `rfl`
downstream of it, for no mathematical gain. -/
noncomputable def qstarLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) : CoarseFnL2 L ell →ₗ[ℝ] BondFnL2 L :=
  LinearMap.adjoint (𝕜 := ℝ) (E := BondFnL2 L) (F := CoarseFnL2 L ell)
    ((qCLM U ell : BondFnL2 L →ₗ[ℝ] CoarseFnL2 L ell))

noncomputable def qstarCLM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) : CoarseFnL2 L ell →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (qstarLM U ell)

theorem qstarCLM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (B : CoarseFnL2 L ell) : qstarCLM U ell B = qstarLM U ell B := rfl

/-- **`hadj` is a THEOREM at the real carrier**, not a hypothesis. -/
theorem qCLM_hadj (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (x : BondFnL2 L) (B : CoarseFnL2 L ell) :
    (inner ℝ (qstarCLM U ell B) x : ℝ) = (inner ℝ B (qCLM U ell x) : ℝ) := by
  have h : (inner ℝ x (qstarLM U ell B) : ℝ) = (inner ℝ (qCLM U ell x) B : ℝ) := by
    exact LinearMap.adjoint_inner_right (𝕜 := ℝ) (E := BondFnL2 L) (F := CoarseFnL2 L ell)
      ((qCLM U ell : BondFnL2 L →ₗ[ℝ] CoarseFnL2 L ell)) x B
  rw [qstarCLM_apply]
  rw [show (inner ℝ (qstarLM U ell B) x : ℝ) = (inner ℝ x (qstarLM U ell B) : ℝ) from
      real_inner_comm _ _, h]
  exact real_inner_comm _ _

/-! ## §3 — `Q` is SURJECTIVE at `U = 1`, from the tree's own exact section -/

/-- **`Q(1)` is surjective**, from `FullySupplied.qc_comp_suTwoLift`'s last-layer section, promoted
to the `L²` carriers. ⚠ This is the ONLY statement in this module that uses `trivialU`, and §5
never invokes it. -/
theorem qCLM_surjective_trivialU {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    Function.Surjective (qCLM (trivialU L) ell) := by
  intro F
  refine ⟨WithLp.toLp 2 (suTwoLift ell (WithLp.ofLp F)), ?_⟩
  refine (WithLp.linearEquiv 2 ℝ (CoarseBond L ell → SuTwo)).injective ?_
  funext b
  show lineCoarseRestrictCov (trivialU L) ell (suTwoLift ell (WithLp.ofLp F)) b
      = WithLp.ofLp F b
  rw [lineCoarseRestrictCov_trivialU]
  exact lineCoarseRestrictSuTwo_suTwoLift hell hdvd (WithLp.ofLp F) b

/-! ## §4 — `Q ≠ 0` at EVERY background, by an explicit single-bond read

This is what makes §5's `range Q` carrier non-vacuous WITHOUT any smallness assumption and without
`U = 1`. The mechanism: put a single nonzero `𝔰𝔲(2)` value on the fine bond based at a coarse site
`y` in direction `μ`, and read the coarse bond `(y, μ)`. Exactly ONE `(x, i)` pair in that block
average reaches that fine bond — `x = y`, `i = 0` — provided the block does not wrap
(`2 * ell ≤ L μ + 1`); and its transport is applied by `RMap`, which is invertible, so the value
survives. -/

/-- The single-fine-bond test field. -/
noncomputable def bondDelta (b : Bond L) (v : SuTwo) : Bond L → SuTwo :=
  fun b' => if b' = b then v else 0

theorem bondDelta_same (b : Bond L) (v : SuTwo) : bondDelta b v b = v := if_pos rfl

theorem bondDelta_ne {b b' : Bond L} (v : SuTwo) (h : b' ≠ b) : bondDelta b v b' = 0 := if_neg h

/-- `RMap g` is injective: `RMap g⁻¹` undoes it. -/
theorem rMap_injective (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Function.Injective (RMap g) := by
  intro u v huv
  have h : RMap g⁻¹ (RMap g u) = RMap g⁻¹ (RMap g v) := by rw [huv]
  rwa [RMap_mul_apply, RMap_mul_apply, inv_mul_cancel, RMap_one, LinearMap.id_apply,
    LinearMap.id_apply] at h

/-- **The single-hit lemma.** For `y` a coarse site, `x ∈ blockOf y ell` and `i < ell`, the moved
site `pathSite x μ i` equals `y` only for `x = y, i = 0` — provided `2 * ell ≤ L μ + 1`, which
excludes the wrap that occurs when the block is the whole torus in direction `μ`. -/
theorem pathSite_eq_base_iff {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell) (μ : Fin 3) {i : ℕ} (hi : i < ell)
    (heq : pathSite x μ i = y) : x = y ∧ i = 0 := by
  have hblk := mem_blockOf.mp hx
  have hlo : (y μ).val ≤ (x μ).val := (hblk μ).1
  have hhi : (x μ).val < (y μ).val + ell := (hblk μ).2
  have hfit : (y μ).val + ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd hy μ
  have hval : ((pathSite x μ i) μ).val = ((x μ).val + i) % (L μ + 1) :=
    AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_self_val x μ i
  have hyv : ((pathSite x μ i) μ).val = (y μ).val := by rw [heq]
  rw [hval] at hyv
  have hw : 2 * ell ≤ L μ + 1 := hwide μ
  have hi0 : i = 0 := by
    rcases lt_or_ge ((x μ).val + i) (L μ + 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hyv; omega
    · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at hyv
      omega
  refine ⟨?_, hi0⟩
  subst hi0
  rw [pathSite_zero] at heq
  exact heq

/-- **`Q ≠ 0` at EVERY background `U`** — no smallness, no `U = 1`. -/
theorem qCLM_ne_zero {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    qCLM U ell ≠ 0 := by
  set y : PeriodicLatticeSite L := fun _ => 0 with hydef
  have hy : y ∈ CoarseLattice L ell := siteZeroMem L ell
  set μ : Fin 3 := 0 with hμ
  set b0 : Bond L := (y, μ) with hb0
  set A : BondFnL2 L := WithLp.toLp 2 (bondDelta b0 suTwoWitness) with hA
  intro hcon
  -- the coarse bond we read
  set c : CoarseBond L ell := (⟨y, hy⟩, μ) with hc
  have hzero : lineCoarseRestrictCov U ell (bondDelta b0 suTwoWitness) c = 0 := by
    have h := congrFun (congrArg (fun u : CoarseFnL2 L ell => WithLp.ofLp u)
      (congrArg (fun T : BondFnL2 L →L[ℝ] CoarseFnL2 L ell => T A) hcon)) c
    simpa [qCLM_apply, hA] using h
  -- but it is a nonzero multiple of an `RMap` image of the witness
  have hterm : ∀ x ∈ blockOf y ell, rZeroA U y x (bondDelta b0 suTwoWitness) μ ell
      = (if x = y then
          RMap (AdalyFormal.Target.ClayStatement.periodicPathHolonomy U y (transportPath y x μ 0))
            suTwoWitness
        else 0) := by
    intro x hx
    unfold rZeroA
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
      rw [Finset.sum_eq_single 0]
      · rw [pathSite_zero, bondDelta_same]
      · intro i hi hine
        have hlt : i < ell := Finset.mem_range.mp hi
        have hne : (pathSite y μ i, μ) ≠ b0 := by
          intro hcc
          have := pathSite_eq_base_iff hell hdvd hwide hy hx μ hlt (congrArg Prod.fst hcc)
          exact hine this.2
        rw [bondDelta_ne suTwoWitness hne, map_zero]
      · intro hnm
        exact absurd (Finset.mem_range.mpr hell) hnm
    · rw [if_neg hxy]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hlt : i < ell := Finset.mem_range.mp hi
      have hne : (pathSite x μ i, μ) ≠ b0 := by
        intro hcc
        exact hxy (pathSite_eq_base_iff hell hdvd hwide hy hx μ hlt (congrArg Prod.fst hcc)).1
      rw [bondDelta_ne suTwoWitness hne, map_zero]
  rw [lineCoarseRestrictCov, Finset.sum_congr rfl hterm] at hzero
  rw [Finset.sum_ite_eq' (blockOf y ell) y _] at hzero
  have hyb : y ∈ blockOf y ell := mem_blockOf.mpr (fun _ => ⟨Nat.le_refl _, by omega⟩)
  rw [if_pos hyb] at hzero
  have hne0 : (RMap (AdalyFormal.Target.ClayStatement.periodicPathHolonomy U y
      (transportPath y y μ 0)) suTwoWitness) ≠ 0 := by
    intro hc0
    exact suTwoWitness_ne_zero
      (rMap_injective _ (by rw [hc0, map_zero]))
  have hsc : (1 / (ell : ℝ) ^ 4) ≠ 0 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  exact hne0 (by
    have := hzero
    rwa [smul_eq_zero, or_iff_right hsc] at this)

end AdalyFormal.Balaban.BridgeInverse
