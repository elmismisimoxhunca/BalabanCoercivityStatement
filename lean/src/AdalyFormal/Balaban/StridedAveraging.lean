/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BridgeInverseCarrier
import AdalyFormal.Balaban.QjComposite
import AdalyFormal.Balaban.ReparamCDisjoint
import AdalyFormal.Balaban.FullReparamC
import AdalyFormal.Balaban.NormRMapClean

set_option autoImplicit false
set_option linter.style.longLine false
-- NO `maxHeartbeats` / `synthInstance.maxHeartbeats` / `maxRecDepth` bump. The bumps this file was
-- drafted with were STRIPPED and the file recompiled: 0 errors, and the 80-line axiom-report output
-- was byte-identical with and without them (nested validator, item 8). Dead configuration removed
-- rather than left in place, so nothing here hides an elaboration cost.

/-!
# `StridedAveraging.lean` — `Q^{(s)}`, the BOND-sector averaging at a general stride

`Balaban/TowerOneStep.lean` §10b names exactly one missing object for a lattice RG ladder of depth
> 1:

> a bond-sector one-step averaging operator between two CONSECUTIVE coarse levels,
> `Q^{(s)} : CoarseFnL2 L s →L[ℝ] CoarseFnL2 L (s * ell)`, i.e. `lineCoarseRestrictCov` with a
> stride. … the missing primitive is the BOND-sector twin of `QjComposite.stepAverage`: the same
> `stepBlockOf`/`coarsePathHolonomy` data applied to a bond field.

This module builds it.

## The object

    (Q^{(s)}(V) A)_b  =  ell^{-4} · Σ_{x ∈ B_s(c₋)} Σ_{i<ell}
                            R( V( Γ^s_{c₋,x} ∪ [x, x + s·i·e_μ] ) ) · A( x + s·i·e_μ , μ )

`b = (c₋, μ)` is a coarse bond at scale `s·ell`; `A` is a coarse-bond field at scale `s`;
`B_s(c₋) = QjComposite.stepBlockOf c₋ s ell` is the strided block (`ell^3` sites, spacing `s`);
`Γ^s ∪ [·,·] = TowerLawCov.coarseTransportPath s c₋ x μ i` is the strided staircase followed by the
strided straight leg, and the holonomy is `TowerLawCov.coarsePathHolonomy s V`, whose factors
`V (y, μ)` are the level-`s` links. Every one of those four objects ALREADY EXISTED in the tree and
is reused, not rebuilt (LAW-19); what did not exist is their assembly on a BOND field, which is
what §3 supplies.

## Faithfulness to `lineCoarseRestrictCov` — the two checks a wrong encoding would fail

1. **The normalisation is `ell^{-4}` at EVERY stride, not `(s·ell)^{-4}`.** §6's
   `stepBondAvgAt_const_trivialU` shows the constant field is returned exactly: the strided block
   still has `ell^3` sites (`card_stepBlockOf`) and the strided line still has `ell` segments, so
   `ell^{-(d+1)} = ell^{-4}` is the true-average weight at every level. Rescaling the constant by
   any factor breaks that theorem.
2. **No summand is silently dropped.** A coarse-`s` field is a function on `CoarseBond L s`, so
   reading it at a site requires a proof that the site is on the `s`-lattice. §2's `coarseValAt`
   supplies a total extension by `0`, and §2's `stepPathSite_mem_coarseLattice` PROVES the `0`
   branch is never taken inside the sum, under `s ∣ L μ + 1`. §7 exhibits an extent where dropping
   that divisibility hypothesis makes the `0` branch fire on `ell^3(ell-1)` of the `ell^4`
   summands — i.e. the hypothesis is load-bearing, not decorative (S83).

## What is proved here

* §1–§3 the strided site walk, the total coarse read, the operator, linearity, `LinearMap`,
  `ContinuousLinearMap` `qStepCLM : CoarseFnL2 L s →L[ℝ] CoarseFnL2 L (s * ell)`.
* §4 **the `s = 1` ANCHOR**: `Q^{(1)}(U) = lineCoarseRestrictCov U ell`, through the canonical
  `CoarseBond L 1 ≃ Bond L`. Proved by bridging the two contour encodings the tree carries — the
  strided direction list (`coarseTransportPath`) and the signed fine step list
  (`Q1Real.transportPath`) — so this module introduces no third convention.
* §5 **the COMPOSITION LAW**: `bondComposite`/`qCompositeCLM` with
  `Q^{(ell^{j+1})}_{comp} = Q^{(ell^j)}_{step} ∘ Q^{(ell^j)}_{comp}`, the operator content of
  CMP98 pp.29–30's telescoping display (the UNNUMBERED display between printed (76) and (77); the
  "(52),(53)" pointer inherited from CMP99b p.393 is dead and is not used).
* §6 the explicit OPERATOR-NORM bound `ell^3 · ‖Q^{(s)} A‖² ≤ ‖A‖²`, i.e. `q_s = ell^{-3/2}`
  independent of `s`, hence `‖Q^{(ell^j)}_{comp}‖ ≤ (ell^{-3/2})^j` — derived from `RMap`'s
  isometry, Cauchy–Schwarz on the `ell^4` summands, and an INJECTION `(b,x) ↦ (x+s·i·e_μ, μ)` at
  each fixed `i`, not asserted.
* §7 the adjoint `qStepStarCLM` and `hadj` as a theorem; §8 surjectivity at `V = 1` via the strided
  last-layer lift, hence injectivity of the adjoint — the three properties `TowerOneStep.Rung`
  consumes.
* §9 controls: must-fire, must-not-fire, the degenerate strides, and the binder audit.
-/

namespace AdalyFormal.Balaban.StridedAveraging

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration
  PeriodicLatticeSite periodicPathHolonomy periodicLatticeStep periodicLatticeShift)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one RMap_mul_apply
  suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice
  mem_CoarseLattice coarseLattice_mem_fits unique_multiple_in_window)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.BridgeInverse (CoarseFnL2)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.Q1Real (rZeroA transportPath GammaPath straightSegment coordSteps)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.QjComposite (inStepBlock stepBlockOf mem_stepBlockOf stepBlockOf_one
  card_stepBlockOf stepBlockOf_subset_blockOf pathSite_add)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath
  coarseStraightSegment coarseCoordSteps coarseTransportPath coarsePathHolonomy_trivialU)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.QcEquation (blockCorner blockCorner_val blockCorner_mem
  blockCorner_of_mem_blockOf)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_eq pathSite_apply_ne pathSite_apply_self_val)
open AdalyFormal.Balaban.FaithfulCoercivitySU2 (norm_RMap)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the strided site walk `x ↦ x + s·i·e_μ`

The strided line integral reads the field at the ENDPOINTS of the strided straight leg of
`coarseTransportPath`. `stepPathSite` is that endpoint, and `stepPathSite_eq_endpoint` proves it —
so the transport used for a summand and the bond read by that summand are the same walk, which is
the one identity a mis-assembled covariant average would violate. -/

/-- `x` advanced `i` strided steps (each of length `s`) in direction `μ`. -/
def stepPathSite (s : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) : PeriodicLatticeSite L :=
  pathSite x μ (s * i)

theorem stepPathSite_zero (s : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    stepPathSite s x μ 0 = x := by simp [stepPathSite, pathSite_zero]

theorem stepPathSite_one_stride (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    stepPathSite 1 x μ i = pathSite x μ i := by simp [stepPathSite]

/-- `coarseShift y s μ` IS one strided step. -/
theorem coarseShift_eq_pathSite (y : PeriodicLatticeSite L) (s : ℕ) (μ : Fin 3) :
    coarseShift y s μ = pathSite y μ s := rfl

/-- **The walk is the endpoint of the transport path's straight leg.** `coarsePathEndpoint s x
(List.replicate i μ)` is where `coarseTransportPath s c x μ i` ends; this says the field is read
exactly there. -/
theorem stepPathSite_eq_endpoint (s : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    coarsePathEndpoint s x (List.replicate i μ) = stepPathSite s x μ i := by
  induction i generalizing x with
  | zero =>
      show x = stepPathSite s x μ 0
      exact (stepPathSite_zero s x μ).symm
  | succ i ih =>
      rw [List.replicate_succ]
      show coarsePathEndpoint s (coarseShift x s μ) (List.replicate i μ) = _
      rw [ih]
      show pathSite (pathSite x μ s) μ (s * i) = pathSite x μ (s * (i + 1))
      rw [pathSite_add]
      exact congrArg (pathSite x μ) (by ring)

theorem stepPathSite_apply_ne (s : ℕ) (x : PeriodicLatticeSite L) (μ ν : Fin 3) (i : ℕ)
    (h : ν ≠ μ) : stepPathSite s x μ i ν = x ν := pathSite_apply_ne x μ ν (s * i) h

theorem stepPathSite_apply_self_val (s : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    ((stepPathSite s x μ i) μ).val = ((x μ).val + s * i) % (L μ + 1) :=
  pathSite_apply_self_val x μ (s * i)

/-- **The walk is injective in its base point**, at every stride and every step count. This is the
combinatorial fact the norm bound of §6 rests on. -/
theorem stepPathSite_injective (s : ℕ) (μ : Fin 3) (i : ℕ) {x x' : PeriodicLatticeSite L}
    (h : stepPathSite s x μ i = stepPathSite s x' μ i) : x = x' := by
  funext ν
  rcases eq_or_ne ν μ with rfl | hν
  · have h1 : x ν + (s * i) • (1 : Fin (L ν + 1)) = x' ν + (s * i) • (1 : Fin (L ν + 1)) := by
      have hx : (stepPathSite s x ν i) ν = x ν + (s * i) • (1 : Fin (L ν + 1)) := by
        rw [stepPathSite, pathSite_eq, Function.update_self]
      have hx' : (stepPathSite s x' ν i) ν = x' ν + (s * i) • (1 : Fin (L ν + 1)) := by
        rw [stepPathSite, pathSite_eq, Function.update_self]
      rw [← hx, ← hx', h]
    exact add_right_cancel h1
  · have hx := stepPathSite_apply_ne s x μ ν i hν
    have hx' := stepPathSite_apply_ne s x' μ ν i hν
    rw [← hx, ← hx', h]

/-! ## §2 — reading a coarse-`s` bond field at a site, and the NO-DROP lemma

A coarse-`s` field lives on `CoarseBond L s`, whose site component carries a membership proof.
`coarseValAt` extends it totally by `0`; `stepPathSite_mem_coarseLattice` proves the `0` branch is
never taken inside the operator's own sum. -/

/-- The total extension of a coarse-`s` bond field to all (site, direction) pairs, by `0`. -/
noncomputable def coarseValAt (s : ℕ) (A : CoarseBond L s → SuTwo) (z : PeriodicLatticeSite L)
    (μ : Fin 3) : SuTwo :=
  if h : z ∈ CoarseLattice L s then A (⟨z, h⟩, μ) else 0

theorem coarseValAt_of_mem {s : ℕ} (A : CoarseBond L s → SuTwo) {z : PeriodicLatticeSite L}
    (hz : z ∈ CoarseLattice L s) (μ : Fin 3) : coarseValAt s A z μ = A (⟨z, hz⟩, μ) :=
  dif_pos hz

theorem coarseValAt_of_not_mem {s : ℕ} (A : CoarseBond L s → SuTwo) {z : PeriodicLatticeSite L}
    (hz : z ∉ CoarseLattice L s) (μ : Fin 3) : coarseValAt s A z μ = 0 :=
  dif_neg hz

theorem coarseValAt_add {s : ℕ} (A B : CoarseBond L s → SuTwo) (z : PeriodicLatticeSite L)
    (μ : Fin 3) : coarseValAt s (A + B) z μ = coarseValAt s A z μ + coarseValAt s B z μ := by
  unfold coarseValAt
  by_cases h : z ∈ CoarseLattice L s
  · simp [dif_pos h]
  · simp [dif_neg h]

theorem coarseValAt_smul {s : ℕ} (c : ℝ) (A : CoarseBond L s → SuTwo) (z : PeriodicLatticeSite L)
    (μ : Fin 3) : coarseValAt s (c • A) z μ = c • coarseValAt s A z μ := by
  unfold coarseValAt
  by_cases h : z ∈ CoarseLattice L s
  · simp [dif_pos h]
  · simp [dif_neg h]

theorem norm_coarseValAt_le {s : ℕ} (A : CoarseBond L s → SuTwo) (z : PeriodicLatticeSite L)
    (μ : Fin 3) : ‖coarseValAt s A z μ‖ ≤ ‖coarseValAt s A z μ‖ := le_refl _

/-- Every site is on the `1`-lattice. -/
theorem mem_coarseLattice_one (z : PeriodicLatticeSite L) : z ∈ CoarseLattice L 1 :=
  mem_CoarseLattice.mpr (fun _ => Nat.mod_one _)

/-- At stride `1` the total extension is just evaluation. -/
theorem coarseValAt_one (A : CoarseBond L 1 → SuTwo) (z : PeriodicLatticeSite L) (μ : Fin 3) :
    coarseValAt 1 A z μ = A (⟨z, mem_coarseLattice_one z⟩, μ) :=
  coarseValAt_of_mem A (mem_coarseLattice_one z) μ

/-- **A strided-block member is on the `s`-lattice.** `x ∈ B_s(c)` with `c` on the `s·ell`-lattice
forces every coordinate of `x` to be a multiple of `s`. -/
theorem stepBlock_mem_coarseLattice {s ell : ℕ} {c x : PeriodicLatticeSite L}
    (hc : c ∈ CoarseLattice L (s * ell)) (hx : x ∈ stepBlockOf c s ell) :
    x ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice]
  intro ν
  have hb := mem_stepBlockOf.mp hx ν
  have hc0 : (c ν).val % (s * ell) = 0 := mem_CoarseLattice.mp hc ν
  have hcs : s ∣ (c ν).val := dvd_trans (Dvd.intro ell rfl) (Nat.dvd_of_mod_eq_zero hc0)
  have hd : s ∣ ((x ν).val - (c ν).val) := hb.2.2
  have hle : (c ν).val ≤ (x ν).val := hb.1
  obtain ⟨p, hp⟩ := hcs
  obtain ⟨q, hq⟩ := hd
  have : (x ν).val = s * (p + q) := by rw [Nat.mul_add]; omega
  rw [this]
  exact Nat.mul_mod_right _ _

/-- **THE NO-DROP LEMMA.** The site the operator reads, `x + s·i·e_μ`, is again on the `s`-lattice,
so `coarseValAt`'s `0` branch never fires inside the sum. Needs `s ∣ L μ + 1`: the periodic
wraparound must preserve the `s`-sublattice, and §9 exhibits an extent where it does not. -/
theorem stepPathSite_mem_coarseLattice {s : ℕ} (hdvdS : ∀ ν : Fin 3, s ∣ (L ν + 1))
    {x : PeriodicLatticeSite L} (hx : x ∈ CoarseLattice L s) (μ : Fin 3) (i : ℕ) :
    stepPathSite s x μ i ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice]
  intro ν
  rcases eq_or_ne ν μ with rfl | hν
  · rw [stepPathSite_apply_self_val]
    have h1 : s ∣ ((x ν).val + s * i) :=
      Nat.dvd_add (Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hx ν)) (Dvd.intro i rfl)
    obtain ⟨t, ht⟩ := (Nat.dvd_mod_iff (hdvdS ν)).mpr h1
    rw [ht]
    exact Nat.mul_mod_right _ _
  · rw [stepPathSite_apply_ne s x μ ν i hν]
    exact mem_CoarseLattice.mp hx ν

/-! ## §3 — the operator `Q^{(s)}` -/

/-- **`(Q^{(s)}(V) A)(c,μ)`** — the strided bond-sector average. `lineCoarseRestrictCov`'s shape
with `blockOf → stepBlockOf`, `pathSite → stepPathSite`, and
`periodicPathHolonomy ∘ transportPath → coarsePathHolonomy s ∘ coarseTransportPath s`. Stated at a
raw (site, direction) pair so no dependent coercion appears in the formula; §3's `stepBondAvg`
packages it on `CoarseBond L (s * ell)`. -/
noncomputable def stepBondAvgAt (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (1 / (ell : ℝ) ^ 4) • ∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
    RMap (coarsePathHolonomy s V c (coarseTransportPath s c x μ i))
      (coarseValAt s A (stepPathSite s x μ i) μ)

/-- `Q^{(s)}` on the coarse bond index type at scale `s * ell`. -/
noncomputable def stepBondAvg (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseBond L s → SuTwo) (b : CoarseBond L (s * ell)) : SuTwo :=
  stepBondAvgAt s V ell A b.1.1 b.2

theorem stepBondAvgAt_add (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A B : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) :
    stepBondAvgAt s V ell (A + B) c μ
      = stepBondAvgAt s V ell A c μ + stepBondAvgAt s V ell B c μ := by
  simp only [stepBondAvgAt, coarseValAt_add, map_add]
  rw [← smul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl (fun x _ => ?_))
  rw [← Finset.sum_add_distrib]

theorem stepBondAvgAt_smul (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) (r : ℝ)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) :
    stepBondAvgAt s V ell (r • A) c μ = r • stepBondAvgAt s V ell A c μ := by
  simp only [stepBondAvgAt, coarseValAt_smul, map_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

theorem stepBondAvg_add (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A B : CoarseBond L s → SuTwo) (b : CoarseBond L (s * ell)) :
    stepBondAvg s V ell (A + B) b = stepBondAvg s V ell A b + stepBondAvg s V ell B b :=
  stepBondAvgAt_add s V ell A B b.1.1 b.2

theorem stepBondAvg_smul (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) (r : ℝ)
    (A : CoarseBond L s → SuTwo) (b : CoarseBond L (s * ell)) :
    stepBondAvg s V ell (r • A) b = r • stepBondAvg s V ell A b :=
  stepBondAvgAt_smul s V ell r A b.1.1 b.2

/-- `Q^{(s)}` as a `LinearMap` on the plain function carriers. -/
noncomputable def stepBondAvgLM (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) :
    (CoarseBond L s → SuTwo) →ₗ[ℝ] (CoarseBond L (s * ell) → SuTwo) where
  toFun A := stepBondAvg s V ell A
  map_add' A B := funext fun b => stepBondAvg_add s V ell A B b
  map_smul' r A := funext fun b => stepBondAvg_smul s V ell r A b

theorem stepBondAvgLM_apply (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseBond L s → SuTwo) (b : CoarseBond L (s * ell)) :
    stepBondAvgLM s V ell A b = stepBondAvg s V ell A b := rfl

/-- **`Q^{(s)} : CoarseFnL2 L s →L[ℝ] CoarseFnL2 L (s * ell)`** — the object §10b named. Built with
the same recipe as `BridgeInverse.qCLM` (LAW-19), so it lands on the same `L²` carriers the bridge
and the rung consume. -/
noncomputable def qStepCLM (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) :
    CoarseFnL2 L s →L[ℝ] CoarseFnL2 L (s * ell) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (CoarseBond L (s * ell) → SuTwo)).symm.toLinearMap.comp
      ((stepBondAvgLM s V ell).comp
        (WithLp.linearEquiv 2 ℝ (CoarseBond L s → SuTwo)).toLinearMap))

theorem qStepCLM_apply (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseFnL2 L s) (b : CoarseBond L (s * ell)) :
    WithLp.ofLp (qStepCLM s V ell A) b = stepBondAvg s V ell (WithLp.ofLp A) b := rfl

/-! ## §4 — THE `s = 1` ANCHOR: `Q^{(1)} = lineCoarseRestrictCov`

The tree carries two encodings of the same contour: `Q1Real.transportPath`, a list of SIGNED FINE
steps `Fin 3 × Bool` run by `periodicPathHolonomy`, and `TowerLawCov.coarseTransportPath`, a list of
DIRECTIONS run by `coarsePathHolonomy` in strided steps. §4a bridges them at stride `1`, so this
module introduces no third convention and §4b is an identification, not a look-alike. -/

/-- **The forward-path bridge.** A strided path at stride `1` is the same walk as the all-forward
signed fine path with the same direction list. -/
theorem coarsePathHolonomy_one_eq_periodic {G : Type*} [Group G]
    (U : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    coarsePathHolonomy 1 U y p = periodicPathHolonomy U y (p.map (fun ν => (ν, true))) := by
  induction p generalizing y with
  | nil => rfl
  | cons ν rest ih =>
      show U (y, ν) * coarsePathHolonomy 1 U (coarseShift y 1 ν) rest = _
      rw [ih]
      rfl

/-- **The staircase bridge.** `coarseGammaPath 1` maps onto `Q1Real.GammaPath` — same corner sites,
same descending `2,1,0` order, same segment lengths (`coarseCoordSteps 1 = coordSteps`). -/
theorem coarseGammaPath_one_map (y x : PeriodicLatticeSite L) :
    (coarseGammaPath 1 y x).map (fun ν : Fin 3 => (ν, true)) = GammaPath y x := by
  simp [coarseGammaPath, GammaPath, coarseStraightSegment, coarseCoordSteps, straightSegment,
    coordSteps, List.map_append, List.map_replicate, Nat.div_one, List.append_assoc]

/-- **The transport-path bridge**, including the straight leg. The hypothesis `i < L μ + 1` is the
no-wrap condition under which the fine leg has exactly `i` steps
(`FullReparamC.coordSteps_pathSite_self`); it is implied by `i < ell ≤ L μ + 1`. -/
theorem coarseTransportPath_one_map (c x : PeriodicLatticeSite L) (μ : Fin 3) {i : ℕ}
    (hi : i < L μ + 1) :
    (coarseTransportPath 1 c x μ i).map (fun ν : Fin 3 => (ν, true)) = transportPath c x μ i := by
  unfold coarseTransportPath transportPath straightSegment
  rw [List.map_append, coarseGammaPath_one_map, List.map_replicate,
    AdalyFormal.Balaban.FullReparamC.coordSteps_pathSite_self x μ i hi]

/-- **THE ANCHOR, pointwise.** At stride `1` the strided bond average IS `lineCoarseRestrictCov`'s
defining expression, at every base site and direction. -/
theorem stepBondAvgAt_one_eq (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (A : Bond L → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3)
    (hell : ell ≤ L μ + 1) :
    stepBondAvgAt 1 U ell (fun e : CoarseBond L 1 => A (e.1.1, e.2)) c μ
      = (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf c ell, rZeroA U c x A μ ell := by
  unfold stepBondAvgAt rZeroA
  rw [stepBlockOf_one]
  refine congrArg _ (Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i hi => ?_)))
  have hi' : i < L μ + 1 := lt_of_lt_of_le (Finset.mem_range.mp hi) hell
  rw [coarsePathHolonomy_one_eq_periodic, coarseTransportPath_one_map c x μ hi',
    stepPathSite_one_stride, coarseValAt_one]

/-- The canonical identification of the stride-`1` coarse bonds with the fine bonds. -/
def coarseBondOneEquiv (L : PeriodicLatticeExtent) : CoarseBond L 1 ≃ Bond L where
  toFun e := (e.1.1, e.2)
  invFun e := (⟨e.1, mem_coarseLattice_one e.1⟩, e.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **THE ANCHOR, on the coarse-bond carriers.** `Q^{(1)}(U)` transported along
`coarseBondOneEquiv` is exactly `LineIntegralCovariant.lineCoarseRestrictCov U ell`, the tree's
faithful covariant CMP95 (1.18) / CMP98 (125) block-averaged line integral. -/
theorem stepBondAvg_one (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (A : Bond L → SuTwo) (b : CoarseBond L (1 * ell)) (b' : CoarseBond L ell)
    (hsite : b.1.1 = b'.1.1) (hdir : b.2 = b'.2) (hell : ell ≤ L b.2 + 1) :
    stepBondAvg 1 U ell (fun e => A (coarseBondOneEquiv L e)) b
      = lineCoarseRestrictCov U ell A b' := by
  show stepBondAvgAt 1 U ell (fun e : CoarseBond L 1 => A (e.1.1, e.2)) b.1.1 b.2 = _
  rw [stepBondAvgAt_one_eq U A b.1.1 b.2 hell, hsite, hdir]
  rfl

/-! ## §5 — THE COMPOSITION LAW

CMP98 pp.29–30's telescoping display (the UNNUMBERED display between printed (76) and (77))
composes the level factors in the order "fine factor first, coarsest last". On the operator side
that is a recursion, and here it TYPECHECKS with no coercion: `ell ^ (j+1)` and `ell ^ j * ell` are
definitionally equal in `ℕ`, so `qStepCLM (ell^j) (bg j) ell` composes onto
`qCompositeCLM bg ell j` on the nose. -/

/-- **`Q^{(ell^j)}_{comp}`** — the `j`-fold strided bond average, from the fine bond carrier to the
level-`j` coarse bond carrier. `bg l` is the level-`ell^l` background. -/
noncomputable def qCompositeCLM
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) :
    (j : ℕ) → (CoarseFnL2 L 1 →L[ℝ] CoarseFnL2 L (ell ^ j))
  | 0 => ContinuousLinearMap.id ℝ (CoarseFnL2 L 1)
  | (j + 1) => (qStepCLM (ell ^ j) (bg j) ell).comp (qCompositeCLM bg ell j)

theorem qCompositeCLM_zero
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseFnL2 L 1) : qCompositeCLM bg ell 0 A = A := rfl

/-- **THE COMPOSITION LAW**: `Q^{(ell^{j+1})} = Q^{(ell^j)}_{step} ∘ Q^{(ell^j)}_{comp}` — the new
factor is the COARSEST and is applied LAST, the orientation the source's product forces. -/
theorem qCompositeCLM_succ
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell j : ℕ) :
    qCompositeCLM bg ell (j + 1)
      = (qStepCLM (ell ^ j) (bg j) ell).comp (qCompositeCLM bg ell j) := rfl

theorem qCompositeCLM_succ_apply
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell j : ℕ)
    (A : CoarseFnL2 L 1) :
    qCompositeCLM bg ell (j + 1) A = qStepCLM (ell ^ j) (bg j) ell (qCompositeCLM bg ell j A) := rfl

/-- **`Q^{(ell)}_{comp} = Q^{(1)}_{step}`** — the depth-one composite is the one-step operator,
which §4 identified with `lineCoarseRestrictCov`. So the ladder is anchored at the tree's own `Q`. -/
theorem qCompositeCLM_one
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseFnL2 L 1) : qCompositeCLM bg ell 1 A = qStepCLM 1 (bg 0) ell A := rfl

/-! ## §6 — THE OPERATOR-NORM BOUND, WITH `q_s` EXPLICIT

Nothing here is asserted. The constant is assembled from three counted facts:

* `RMap` is an isometry (`FaithfulCoercivitySU2.norm_RMap`), so the transport contributes `1`;
* the summand count is `ell^3 · ell = ell^4` (`card_stepBlockOf` × `Finset.range ell`), which is
  what Cauchy–Schwarz costs against the `ell^{-4}` prefactor;
* each fine index `i` contributes an INJECTION `(b, x) ↦ (x + s·i·e_μ, μ)` of the block indices
  into the coarse-`s` bonds (`block_sum_le_total`), so the `b`-sum costs a factor `ell` (one per
  value of `i`) and NOT the number of coarse bonds.

`ell^{-8} · ell^4 · ell = ell^{-3}`, giving **`q_s = ell^{-3/2} = ell^{-d/2}` at `d = 3`,
independent of the stride `s`** — hence `‖Q^{(ell^j)}_{comp}‖ ≤ (ell^{-3/2})^j`, geometric decay in
the depth. The uniform-rescale test: multiply the definition's prefactor by any `t > 0` and the
bound becomes `t² ell^{-3}`, so `qStepCLM_normSq_le` pins the normalisation, and
`stepBondAvgAt_const_trivialU` (§9) pins it a second, independent way. -/

/-- **The total extension is `L²`-faithful**: summing `‖coarseValAt‖²` over ALL bonds returns the
coarse field's own `ℓ²` mass. (If the extension were lossy — e.g. if a genuine value ever landed in
the `0` branch — this identity would fail.) -/
theorem sum_coarseValAt_normSq (s : ℕ) (A : CoarseBond L s → SuTwo) :
    ∑ e : Bond L, ‖coarseValAt s A e.1 e.2‖ ^ 2 = ∑ f : CoarseBond L s, ‖A f‖ ^ 2 := by
  classical
  set F : PeriodicLatticeSite L → ℝ :=
    fun z => ∑ μ : Fin 3, ‖coarseValAt s A z μ‖ ^ 2 with hF
  have hL : ∑ e : Bond L, ‖coarseValAt s A e.1 e.2‖ ^ 2
      = ∑ z : PeriodicLatticeSite L, F z := Fintype.sum_prod_type _
  have hR : ∑ f : CoarseBond L s, ‖A f‖ ^ 2
      = ∑ y : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L s},
          ∑ μ : Fin 3, ‖A (y, μ)‖ ^ 2 := Fintype.sum_prod_type _
  have hy : ∀ y : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L s},
      (∑ μ : Fin 3, ‖A (y, μ)‖ ^ 2) = F (y : PeriodicLatticeSite L) := by
    intro y
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [coarseValAt_of_mem A y.2 μ]
  have hfilter : (Finset.univ.filter (fun z : PeriodicLatticeSite L => z ∈ CoarseLattice L s))
      = CoarseLattice L s := by
    ext z; simp
  have hzero : ∀ z ∈ Finset.univ.filter
      (fun z : PeriodicLatticeSite L => ¬ z ∈ CoarseLattice L s), F z = 0 := by
    intro z hz
    have hz' : z ∉ CoarseLattice L s := (Finset.mem_filter.mp hz).2
    simp only [hF]
    exact Finset.sum_eq_zero (fun μ _ => by rw [coarseValAt_of_not_mem A hz' μ]; simp)
  rw [hL, hR]
  rw [Finset.sum_congr rfl (fun y _ => hy y)]
  rw [← Finset.sum_subtype (CoarseLattice L s) (fun _ => Iff.rfl) F]
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (PeriodicLatticeSite L)) (fun z => z ∈ CoarseLattice L s) F,
    Finset.sum_eq_zero hzero, add_zero, hfilter]

/-- **THE INJECTION.** For each fixed step count `i`, the map `(b, x) ↦ (x + s·i·e_μ, μ)` from
`{(coarse bond at scale s·ell, member of its strided block)}` to the bonds is INJECTIVE — the
direction is read off the target, the base `x` is recovered by undoing `i` strided steps
(`stepPathSite_injective`), and the block anchor is recovered by
`blockCorner_of_mem_blockOf`. So each `i` costs one copy of the total mass and no more. -/
theorem block_sum_le_total (s ell i : ℕ) (F : Bond L → ℝ) (hF : ∀ e, 0 ≤ F e) :
    ∑ b : CoarseBond L (s * ell), ∑ x ∈ stepBlockOf b.1.1 s ell,
        F (stepPathSite s x b.2 i, b.2)
      ≤ ∑ e : Bond L, F e := by
  classical
  set Psi : CoarseBond L (s * ell) × PeriodicLatticeSite L → Bond L :=
    fun p => (stepPathSite s p.2 p.1.2 i, p.1.2) with hPsi
  set T : Finset (CoarseBond L (s * ell) × PeriodicLatticeSite L) :=
    Finset.univ.filter (fun p => p.2 ∈ stepBlockOf p.1.1.1 s ell) with hT
  have hinj : ∀ p ∈ T, ∀ q ∈ T, Psi p = Psi q → p = q := by
    intro p hp q hq heq
    have hpb : p.2 ∈ stepBlockOf p.1.1.1 s ell := (Finset.mem_filter.mp hp).2
    have hqb : q.2 ∈ stepBlockOf q.1.1.1 s ell := (Finset.mem_filter.mp hq).2
    have hd : p.1.2 = q.1.2 := congrArg (fun e : Bond L => e.2) heq
    have hsite : stepPathSite s p.2 p.1.2 i = stepPathSite s q.2 q.1.2 i :=
      congrArg (fun e : Bond L => e.1) heq
    rw [hd] at hsite
    have hx : p.2 = q.2 := stepPathSite_injective s q.1.2 i hsite
    have hc1 : blockCorner (s * ell) p.2 = p.1.1.1 :=
      blockCorner_of_mem_blockOf p.1.1.2 (stepBlockOf_subset_blockOf hpb)
    have hc2 : blockCorner (s * ell) q.2 = q.1.1.1 :=
      blockCorner_of_mem_blockOf q.1.1.2 (stepBlockOf_subset_blockOf hqb)
    have hanchor : p.1.1.1 = q.1.1.1 := by rw [← hc1, ← hc2, hx]
    refine Prod.ext ?_ hx
    exact Prod.ext (Subtype.ext hanchor) hd
  have hrew : ∑ p ∈ T, F (Psi p)
      = ∑ b : CoarseBond L (s * ell), ∑ x ∈ stepBlockOf b.1.1 s ell,
          F (stepPathSite s x b.2 i, b.2) := by
    rw [hT, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hPsi, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← hrew, ← Finset.sum_image hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun e _ _ => hF e)

/-- **The pointwise Cauchy–Schwarz step.** `ell^4` summands, each of norm `‖A(·)‖` because `RMap`
is an isometry. -/
theorem norm_stepBondAvgAt_sq_le {s ell : ℕ}
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) (hell : 0 < ell)
    (hcard : (stepBlockOf c s ell).card = ell ^ 3) :
    ‖stepBondAvgAt s V ell A c μ‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) * ∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
          ‖coarseValAt s A (stepPathSite s x μ i) μ‖ ^ 2 := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set P : Finset (PeriodicLatticeSite L × ℕ) := (stepBlockOf c s ell) ×ˢ (Finset.range ell) with hP
  set g : PeriodicLatticeSite L × ℕ → ℝ :=
    fun p => ‖coarseValAt s A (stepPathSite s p.1 μ p.2) μ‖ with hg
  have hcardP : (P.card : ℝ) = (ell : ℝ) ^ 4 := by
    rw [hP, Finset.card_product, hcard, Finset.card_range]
    push_cast
    ring
  have hterm : ∀ x ∈ stepBlockOf c s ell, ∀ i ∈ Finset.range ell,
      ‖RMap (coarsePathHolonomy s V c (coarseTransportPath s c x μ i))
        (coarseValAt s A (stepPathSite s x μ i) μ)‖ = g (x, i) := by
    intro x _ i _
    rw [hg]
    exact norm_RMap _ _
  have hnormsum :
      ‖∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
        RMap (coarsePathHolonomy s V c (coarseTransportPath s c x μ i))
          (coarseValAt s A (stepPathSite s x μ i) μ)‖ ≤ ∑ p ∈ P, g p := by
    rw [hP, Finset.sum_product]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x hx => ?_))
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i hi => ?_))
    exact le_of_eq (hterm x hx i hi)
  have hcs : (∑ p ∈ P, g p) ^ 2 ≤ (ell : ℝ) ^ 4 * ∑ p ∈ P, g p ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := P) (f := g)
    rwa [hcardP] at h
  have hsqle : ‖∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
      RMap (coarsePathHolonomy s V c (coarseTransportPath s c x μ i))
        (coarseValAt s A (stepPathSite s x μ i) μ)‖ ^ 2
      ≤ (ell : ℝ) ^ 4 * ∑ p ∈ P, g p ^ 2 := by
    refine le_trans ?_ hcs
    have h0 := norm_nonneg (∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
      RMap (coarsePathHolonomy s V c (coarseTransportPath s c x μ i))
        (coarseValAt s A (stepPathSite s x μ i) μ))
    nlinarith [hnormsum, h0]
  have hsplit : ∑ p ∈ P, g p ^ 2
      = ∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
          ‖coarseValAt s A (stepPathSite s x μ i) μ‖ ^ 2 := by
    rw [hP, Finset.sum_product]
  have hpref : ‖stepBondAvgAt s V ell A c μ‖
      = (1 / (ell : ℝ) ^ 4) * ‖∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
        RMap (coarsePathHolonomy s V c (coarseTransportPath s c x μ i))
          (coarseValAt s A (stepPathSite s x μ i) μ)‖ := by
    rw [stepBondAvgAt, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hpref, mul_pow, ← hsplit]
  have hpos : (0 : ℝ) ≤ (1 / (ell : ℝ) ^ 4) ^ 2 := by positivity
  calc (1 / (ell : ℝ) ^ 4) ^ 2 * ‖∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
          RMap (coarsePathHolonomy s V c (coarseTransportPath s c x μ i))
            (coarseValAt s A (stepPathSite s x μ i) μ)‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) ^ 2 * ((ell : ℝ) ^ 4 * ∑ p ∈ P, g p ^ 2) :=
        mul_le_mul_of_nonneg_left hsqle hpos
    _ = (1 / (ell : ℝ) ^ 4) * ∑ p ∈ P, g p ^ 2 := by
        field_simp

/-- **THE NORM BOUND**: `ell^3 · ‖Q^{(s)} A‖² ≤ ‖A‖²`, i.e. `‖Q^{(s)}‖ ≤ ell^{-3/2}` at EVERY
stride `s`. The hypotheses are exactly the ones the strided block needs: `0 < ell` (else the
prefactor is undefined) and `(s·ell) ∣ (L ν + 1)` (else `stepBlockOf` truncates and the count
`ell^3` is false — the tree's known truncation artifact). -/
theorem qStepCLM_normSq_le {s ell : ℕ} (hell : 0 < ell) (hs : 0 < s)
    (hdvd : ∀ ν : Fin 3, (s * ell) ∣ (L ν + 1))
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseFnL2 L s) :
    ((ell : ℝ) ^ 3) * ‖qStepCLM s V ell A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set A' : CoarseBond L s → SuTwo := WithLp.ofLp A with hA'
  have hcardb : ∀ b : CoarseBond L (s * ell), (stepBlockOf b.1.1 s ell).card = ell ^ 3 := by
    intro b
    refine card_stepBlockOf b.1.1 s ell hs (fun ν => ?_)
    exact coarseLattice_mem_fits hdvd b.1.2 ν
  have hstep : ∀ b : CoarseBond L (s * ell),
      ‖stepBondAvg s V ell A' b‖ ^ 2
        ≤ (1 / (ell : ℝ) ^ 4) * ∑ x ∈ stepBlockOf b.1.1 s ell, ∑ i ∈ Finset.range ell,
            ‖coarseValAt s A' (stepPathSite s x b.2 i) b.2‖ ^ 2 :=
    fun b => norm_stepBondAvgAt_sq_le V A' b.1.1 b.2 hell (hcardb b)
  have hnormQ : ‖qStepCLM s V ell A‖ ^ 2
      = ∑ b : CoarseBond L (s * ell), ‖stepBondAvg s V ell A' b‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  have hnormA : ‖A‖ ^ 2 = ∑ f : CoarseBond L s, ‖A' f‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hbig : ∑ b : CoarseBond L (s * ell), ‖stepBondAvg s V ell A' b‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) * ∑ b : CoarseBond L (s * ell),
          ∑ x ∈ stepBlockOf b.1.1 s ell, ∑ i ∈ Finset.range ell,
            ‖coarseValAt s A' (stepPathSite s x b.2 i) b.2‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => hstep b)
  have hswap : ∑ b : CoarseBond L (s * ell),
      ∑ x ∈ stepBlockOf b.1.1 s ell, ∑ i ∈ Finset.range ell,
        ‖coarseValAt s A' (stepPathSite s x b.2 i) b.2‖ ^ 2
      = ∑ i ∈ Finset.range ell, ∑ b : CoarseBond L (s * ell),
          ∑ x ∈ stepBlockOf b.1.1 s ell,
            ‖coarseValAt s A' (stepPathSite s x b.2 i) b.2‖ ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
  have hper : ∀ i ∈ Finset.range ell,
      (∑ b : CoarseBond L (s * ell), ∑ x ∈ stepBlockOf b.1.1 s ell,
        ‖coarseValAt s A' (stepPathSite s x b.2 i) b.2‖ ^ 2) ≤ ∑ f : CoarseBond L s, ‖A' f‖ ^ 2 := by
    intro i _
    have h := block_sum_le_total s ell i (fun e : Bond L => ‖coarseValAt s A' e.1 e.2‖ ^ 2)
      (fun e => by positivity)
    rwa [sum_coarseValAt_normSq s A'] at h
  have htail : (∑ i ∈ Finset.range ell, ∑ b : CoarseBond L (s * ell),
      ∑ x ∈ stepBlockOf b.1.1 s ell, ‖coarseValAt s A' (stepPathSite s x b.2 i) b.2‖ ^ 2)
      ≤ (ell : ℝ) * ∑ f : CoarseBond L s, ‖A' f‖ ^ 2 := by
    have := Finset.sum_le_sum hper
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have hfinal : ‖qStepCLM s V ell A‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) * ∑ f : CoarseBond L s, ‖A' f‖ ^ 2) := by
    rw [hnormQ]
    refine le_trans hbig ?_
    rw [hswap]
    exact mul_le_mul_of_nonneg_left htail (by positivity)
  rw [hnormA]
  have hkey : ((ell : ℝ) ^ 3) * ‖qStepCLM s V ell A‖ ^ 2
      ≤ ((ell : ℝ) ^ 3) * ((1 / (ell : ℝ) ^ 4) * ((ell : ℝ) * ∑ f : CoarseBond L s, ‖A' f‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left hfinal (by positivity)
  refine le_trans hkey (le_of_eq ?_)
  field_simp

/-- The bound in operator-norm form: `q_s = ell^{-3/2}` (`Real.sqrt (1/ell^3)`), independent of the
stride. -/
theorem qStepCLM_opNorm_le {s ell : ℕ} (hell : 0 < ell) (hs : 0 < s)
    (hdvd : ∀ ν : Fin 3, (s * ell) ∣ (L ν + 1))
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖qStepCLM s V ell‖ ≤ Real.sqrt (1 / (ell : ℝ) ^ 3) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun A => ?_)
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have h := qStepCLM_normSq_le hell hs hdvd V A
  have h2 : ‖qStepCLM s V ell A‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 3) * ‖A‖ ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    linarith [h]
  have h3 : ‖qStepCLM s V ell A‖ ≤ Real.sqrt ((1 / (ell : ℝ) ^ 3) * ‖A‖ ^ 2) := by
    rw [show ‖qStepCLM s V ell A‖ = Real.sqrt (‖qStepCLM s V ell A‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)] at h3

/-- **The stride-dependence, stated**: the depth-`j` composite obeys `‖Q_comp‖ ≤ (ell^{-3/2})^j`.
Geometric decay in the depth, from a per-step constant that does NOT degrade with the stride. -/
theorem qCompositeCLM_opNorm_le {ell : ℕ} (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (j : ℕ)
    (hdvd : ∀ j' < j, ∀ ν : Fin 3, (ell ^ j' * ell) ∣ (L ν + 1)) :
    ‖qCompositeCLM bg ell j‖ ≤ Real.sqrt (1 / (ell : ℝ) ^ 3) ^ j := by
  revert hdvd
  induction j with
  | zero =>
      intro _
      have h1 : ‖qCompositeCLM bg ell 0‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      refine le_trans h1 ?_
      norm_num
  | succ j ih =>
      intro hdvd
      have ih := ih (fun j' hj' => hdvd j' (Nat.lt_succ_of_lt hj'))
      have hstep : ‖qStepCLM (ell ^ j) (bg j) ell‖ ≤ Real.sqrt (1 / (ell : ℝ) ^ 3) :=
        qStepCLM_opNorm_le hell (pow_pos hell j) (hdvd j (Nat.lt_succ_self j)) (bg j)
      have hcomp := (qStepCLM (ell ^ j) (bg j) ell).opNorm_comp_le (qCompositeCLM bg ell j)
      have hmul : ‖qStepCLM (ell ^ j) (bg j) ell‖ * ‖qCompositeCLM bg ell j‖
          ≤ Real.sqrt (1 / (ell : ℝ) ^ 3) * Real.sqrt (1 / (ell : ℝ) ^ 3) ^ j :=
        mul_le_mul hstep ih (norm_nonneg (qCompositeCLM bg ell j)) (Real.sqrt_nonneg _)
      have hgoal : ‖qCompositeCLM bg ell (j + 1)‖
          ≤ Real.sqrt (1 / (ell : ℝ) ^ 3) * Real.sqrt (1 / (ell : ℝ) ^ 3) ^ j :=
        le_trans hcomp hmul
      have hpow : Real.sqrt (1 / (ell : ℝ) ^ 3) ^ (j + 1)
          = Real.sqrt (1 / (ell : ℝ) ^ 3) * Real.sqrt (1 / (ell : ℝ) ^ 3) ^ j := by ring
      rw [hpow]
      exact hgoal

/-! ### §6b — THE CONSTANT IS EXACT, NOT MERELY AN UPPER BOUND

A bound whose constant is loose is a weak deliverable and an open prosecution surface. It is not
loose: `ell^{-3/2}` is ATTAINED, on the constant field at `V = 1` (`qStepCLM_normSq_sharp`, stated
in §9b once the constant-field evaluation it needs is available). The proof needs one genuine
combinatorial fact — the strided blocks based at `(s·ell)`-coarse sites PARTITION the `s`-lattice —
which is established here (`coarseLattice_eq_biUnion` + `stepBlockOf_pairwise_disjoint`) rather than
assumed. That partition is also the faithfulness statement `Q^{(s)}` needs in its own right: no
coarse-`s` bond is invisible to the family of coarse-`(s·ell)` averages. -/

/-- **COVERING.** Every `s`-lattice site lies in the strided block of its own `(s·ell)`-corner. -/
theorem stepBlockOf_covers {s ell : ℕ} (hm : 0 < s * ell) {z : PeriodicLatticeSite L}
    (hz : z ∈ CoarseLattice L s) : z ∈ stepBlockOf (blockCorner (s * ell) z) s ell := by
  rw [mem_stepBlockOf]
  intro ν
  have hc : (blockCorner (s * ell) z ν).val = (z ν).val - (z ν).val % (s * ell) :=
    blockCorner_val _ _ _
  have hmod : (z ν).val % (s * ell) < s * ell := Nat.mod_lt _ hm
  have hle : (z ν).val % (s * ell) ≤ (z ν).val := Nat.mod_le _ _
  refine ⟨by omega, by omega, ?_⟩
  have hzs : s ∣ (z ν).val := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hz ν)
  have hsm : s ∣ (s * ell) := Dvd.intro ell rfl
  have : (z ν).val - (blockCorner (s * ell) z ν).val = (z ν).val % (s * ell) := by omega
  rw [this]
  exact (Nat.dvd_mod_iff hsm).mpr hzs

/-- **DISJOINTNESS.** Distinct `(s·ell)`-anchors have disjoint strided blocks. -/
theorem stepBlockOf_pairwise_disjoint {s ell : ℕ} {c c' : PeriodicLatticeSite L}
    (hc : c ∈ CoarseLattice L (s * ell)) (hc' : c' ∈ CoarseLattice L (s * ell)) (hne : c ≠ c') :
    Disjoint (stepBlockOf c s ell) (stepBlockOf c' s ell) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  refine hne ?_
  rw [← blockCorner_of_mem_blockOf hc (stepBlockOf_subset_blockOf hz),
    ← blockCorner_of_mem_blockOf hc' (stepBlockOf_subset_blockOf hz')]

/-- **THE PARTITION.** The `s`-lattice is exactly the disjoint union of the strided blocks. -/
theorem coarseLattice_eq_biUnion {s ell : ℕ} (hm : 0 < s * ell) :
    CoarseLattice L s
      = (CoarseLattice L (s * ell)).biUnion (fun c => stepBlockOf c s ell) := by
  ext z
  rw [Finset.mem_biUnion]
  constructor
  · intro hz
    exact ⟨blockCorner (s * ell) z, blockCorner_mem z, stepBlockOf_covers hm hz⟩
  · rintro ⟨c, hc, hzc⟩
    exact stepBlock_mem_coarseLattice hc hzc

/-- **THE EXACT COUNT**: `|Λ_s| = |Λ_{s·ell}| · ell^3`. -/
theorem card_coarseLattice_step {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell)
    (hdvd : ∀ ν : Fin 3, (s * ell) ∣ (L ν + 1)) :
    (CoarseLattice L s).card = (CoarseLattice L (s * ell)).card * ell ^ 3 := by
  classical
  have hm : 0 < s * ell := Nat.mul_pos hs hell
  rw [coarseLattice_eq_biUnion hm,
    Finset.card_biUnion (fun c hc c' hc' hne => stepBlockOf_pairwise_disjoint hc hc' hne)]
  rw [Finset.sum_congr rfl (fun c hc =>
    card_stepBlockOf c s ell hs (coarseLattice_mem_fits hdvd hc))]
  rw [Finset.sum_const, smul_eq_mul]

/-- The `ℓ²` mass of a constant coarse field. -/
theorem norm_const_sq (s : ℕ) (v : SuTwo) :
    ‖(WithLp.toLp 2 (fun _ : CoarseBond L s => v) : CoarseFnL2 L s)‖ ^ 2
      = ((CoarseLattice L s).card : ℝ) * (3 * ‖v‖ ^ 2) := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  have h1 : ∀ f : CoarseBond L s,
      ‖(WithLp.toLp 2 (fun _ : CoarseBond L s => v) : CoarseFnL2 L s) f‖ ^ 2 = ‖v‖ ^ 2 :=
    fun _ => rfl
  rw [Finset.sum_congr rfl (fun f _ => h1 f), Fintype.sum_prod_type]
  have hinner : ∀ _y : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L s},
      (∑ _μ : Fin 3, ‖v‖ ^ 2) = 3 * ‖v‖ ^ 2 := by
    intro _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [Finset.sum_congr rfl (fun y _ => hinner y),
    ← Finset.sum_subtype (CoarseLattice L s) (fun _ => Iff.rfl)
      (fun _ => (3 : ℝ) * ‖v‖ ^ 2), Finset.sum_const, nsmul_eq_mul]

/-! ## §7 — THE ADJOINT PAIR

Built with the tree's own recipe for these carriers (`BridgeInverseCarrier.qstarLM`, LAW-19): the
BARE `LinearMap.adjoint`. ~~under a `letI` pinning the `PiLp` normed structure.
`ContinuousLinearMap.adjoint` cannot be applied here — its type fixes the topology through
`NormedAddCommGroup`, which does not unify with `PiLp.topologicalSpace`.~~ So `hadj` is a THEOREM at
this carrier, not a hypothesis, exactly as at stride `1`.

**⚠ SUPERSEDED (S75, 2026-08-09, `compute/norm_diamond_install/`) — the struck sentences are false,
and the second one was ALREADY false when it was written.** The four `letI`s this section carried
have been removed; they were on `CoarseFnL2`, a carrier that never had a frozen top-level instance,
and they were copied from `BridgeInverseCarrier`'s bond-side workaround where they WERE needed.
`ContinuousLinearMap.adjoint` applies on `CoarseFnL2` with no override — re-measured in this tree as
`B2` in `compute/norm_diamond_install/probe/AdjointProbe.lean` (`logs/adjoint_probe.log`, exit=0),
and measured to have been applicable already before the norm-diamond deletion
(`compute/norm_diamond/logs/diamond2.log` C5). The sentence predates `SuTwoInner.lean`'s uniformity
repair and was never re-measured after it.

`hadj` being a THEOREM here is unaffected: that is a fact about `qStepStarLM`'s construction, not
about which adjoint API was reachable. -/

noncomputable def qStepStarLM (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) :
    CoarseFnL2 L (s * ell) →ₗ[ℝ] CoarseFnL2 L s :=
  LinearMap.adjoint (𝕜 := ℝ) (E := CoarseFnL2 L s) (F := CoarseFnL2 L (s * ell))
    ((qStepCLM s V ell : CoarseFnL2 L s →ₗ[ℝ] CoarseFnL2 L (s * ell)))

noncomputable def qStepStarCLM (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) :
    CoarseFnL2 L (s * ell) →L[ℝ] CoarseFnL2 L s :=
  LinearMap.toContinuousLinearMap (qStepStarLM s V ell)

theorem qStepStarCLM_apply (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (B : CoarseFnL2 L (s * ell)) : qStepStarCLM s V ell B = qStepStarLM s V ell B := rfl

/-- **`hadj` at general stride, as a THEOREM.** This is the first of the three properties
`TowerOneStep.Rung` consumes (`Rung.hadj`). -/
theorem qStep_hadj (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (x : CoarseFnL2 L s) (B : CoarseFnL2 L (s * ell)) :
    (inner ℝ (qStepStarCLM s V ell B) x : ℝ) = (inner ℝ B (qStepCLM s V ell x) : ℝ) := by
  have h : (inner ℝ x (qStepStarLM s V ell B) : ℝ) = (inner ℝ (qStepCLM s V ell x) B : ℝ) := by
    exact LinearMap.adjoint_inner_right (𝕜 := ℝ) (E := CoarseFnL2 L s)
      (F := CoarseFnL2 L (s * ell))
      ((qStepCLM s V ell : CoarseFnL2 L s →ₗ[ℝ] CoarseFnL2 L (s * ell))) x B
  rw [qStepStarCLM_apply]
  rw [show (inner ℝ (qStepStarLM s V ell B) x : ℝ) = (inner ℝ x (qStepStarLM s V ell B) : ℝ) from
      real_inner_comm _ _, h]
  exact real_inner_comm _ _

/-! ## §8 — SURJECTIVITY AT `V = 1`, VIA THE STRIDED LAST-LAYER LIFT

`FullySupplied.suTwoLift` is the stride-`1` section: it loads the value on the fine bonds whose
`μ`-coordinate is `≡ ell-1 (mod ell)`, so each of the `ell^3` line integrals in a block picks up
exactly one of them. The strided twin loads it on the coarse-`s` bonds whose `μ`-coordinate is
`≡ s·(ell-1) (mod s·ell)`. §8's counting is proved, not inherited: the "exactly one `i` per block
member" statement is `stepLift_hit_unique`. -/

/-- The strided last-layer lift `CoarseFnL2 L (s·ell) → CoarseFnL2 L s`. -/
noncomputable def stepLift (s ell : ℕ) (F : CoarseBond L (s * ell) → SuTwo)
    (e : CoarseBond L s) : SuTwo :=
  if (e.1.1 e.2).val % (s * ell) = s * ell - s then
    (ell : ℝ) • F (⟨blockCorner (s * ell) e.1.1, blockCorner_mem _⟩, e.2)
  else 0

theorem stepLift_add (s ell : ℕ) (F G : CoarseBond L (s * ell) → SuTwo) (e : CoarseBond L s) :
    stepLift s ell (F + G) e = stepLift s ell F e + stepLift s ell G e := by
  unfold stepLift
  by_cases h : (e.1.1 e.2).val % (s * ell) = s * ell - s
  · rw [if_pos h, if_pos h, if_pos h, Pi.add_apply, smul_add]
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem stepLift_smul (s ell : ℕ) (r : ℝ) (F : CoarseBond L (s * ell) → SuTwo)
    (e : CoarseBond L s) : stepLift s ell (r • F) e = r • stepLift s ell F e := by
  unfold stepLift
  by_cases h : (e.1.1 e.2).val % (s * ell) = s * ell - s
  · rw [if_pos h, if_pos h, Pi.smul_apply]
    exact smul_comm _ _ _
  · rw [if_neg h, if_neg h, smul_zero]

/-- **THE SECTION EQUATION at general stride**: `Q^{(s)}(1) ∘ lift = id`. Every step of the count
is proved here — the unique hit `i = ell-1-j` inside each strided line, the block-corner read, and
the `ell^3 · ell / ell^4 = 1` normalisation. -/
theorem stepBondAvg_stepLift {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell)
    (hdvd : ∀ ν : Fin 3, (s * ell) ∣ (L ν + 1))
    (F : CoarseBond L (s * ell) → SuTwo) (b : CoarseBond L (s * ell)) :
    stepBondAvg s (trivialU L) ell (stepLift s ell F) b = F b := by
  classical
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  have hdvdS : ∀ ν : Fin 3, s ∣ (L ν + 1) :=
    fun ν => dvd_trans (Dvd.intro ell rfl) (hdvd ν)
  have hfit : ∀ ν : Fin 3, (y ν).val + s * ell ≤ L ν + 1 := coarseLattice_mem_fits hdvd hy
  have hcard : (stepBlockOf y s ell).card = ell ^ 3 := card_stepBlockOf y s ell hs hfit
  -- the value of one line, for a fixed block member
  have hline : ∀ x ∈ stepBlockOf y s ell,
      (∑ i ∈ Finset.range ell,
        RMap (coarsePathHolonomy s (trivialU L) y (coarseTransportPath s y x μ i))
          (coarseValAt s (stepLift s ell F) (stepPathSite s x μ i) μ))
        = (ell : ℝ) • F (⟨y, hy⟩, μ) := by
    intro x hx
    have hxc : x ∈ CoarseLattice L s := stepBlock_mem_coarseLattice hy hx
    have hblk := mem_stepBlockOf.mp hx μ
    -- the strided offset `j` of `x` in the block
    obtain ⟨j, hj⟩ := hblk.2.2
    have hjlt : j < ell := by
      have h1 : (x μ).val = (y μ).val + s * j := by omega
      have h2 : (x μ).val < (y μ).val + s * ell := hblk.2.1
      have : s * j < s * ell := by omega
      exact lt_of_mul_lt_mul_left this (Nat.zero_le s)
    have hxval : (x μ).val = (y μ).val + s * j := by omega
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy μ)
    -- the hit condition on `i`, reduced to `j + i = ell - 1`
    have hcond : ∀ i, i < ell →
        (((stepPathSite s x μ i) μ).val % (s * ell) = s * ell - s ↔ j + i = ell - 1) := by
      intro i hi
      rw [stepPathSite_apply_self_val, Nat.mod_mod_of_dvd _ (hdvd μ), hxval]
      have hrw : ((y μ).val + s * j + s * i) % (s * ell) = (s * (j + i)) % (s * ell) := by
        rw [show (y μ).val + s * j + s * i = (s * ell) * k + s * (j + i) by
          rw [Nat.mul_add]; omega, Nat.mul_add_mod]
      rw [hrw]
      constructor
      · intro hmod
        rcases lt_or_ge (j + i) ell with hlt | hge
        · have h1 : s * (j + i) < s * ell := mul_lt_mul_of_pos_left hlt hs
          rw [Nat.mod_eq_of_lt h1] at hmod
          have hsl : s * ell - s = s * (ell - 1) := by
            rw [Nat.mul_sub, Nat.mul_one]
          rw [hsl] at hmod
          have := Nat.eq_of_mul_eq_mul_left hs hmod
          omega
        · exfalso
          have hlt2 : s * (j + i) - s * ell < s * ell := by
            have : j + i - ell < ell := by omega
            have h2 : s * (j + i) - s * ell = s * ((j + i) - ell) := by
              rw [Nat.mul_sub]
            rw [h2]
            exact mul_lt_mul_of_pos_left this hs
          have hge2 : s * ell ≤ s * (j + i) := Nat.mul_le_mul_left s hge
          rw [Nat.mod_eq_sub_mod hge2, Nat.mod_eq_of_lt hlt2] at hmod
          have h3 : s * (j + i) - s * ell = s * ((j + i) - ell) := by rw [Nat.mul_sub]
          have hsl : s * ell - s = s * (ell - 1) := by rw [Nat.mul_sub, Nat.mul_one]
          rw [h3, hsl] at hmod
          have := Nat.eq_of_mul_eq_mul_left hs hmod
          omega
      · intro heq
        have h1 : s * (j + i) < s * ell := by
          have hji : j + i < ell := by omega
          exact mul_lt_mul_of_pos_left hji hs
        rw [Nat.mod_eq_of_lt h1, heq, Nat.mul_sub, Nat.mul_one]
    -- the block-corner read, at the hit
    have hcorner : ∀ i, i < ell → j + i = ell - 1 →
        blockCorner (s * ell) (stepPathSite s x μ i) = y := by
      intro i hi heq
      have hnowrap : ((stepPathSite s x μ i) μ).val = (y μ).val + s * (ell - 1) := by
        rw [stepPathSite_apply_self_val, hxval]
        have h2 : s * j + s * i = s * (ell - 1) := by rw [← Nat.mul_add, heq]
        have h1 : (y μ).val + s * j + s * i = (y μ).val + s * (ell - 1) := by omega
        rw [h1]
        refine Nat.mod_eq_of_lt ?_
        have h2 : s * (ell - 1) < s * ell :=
          mul_lt_mul_of_pos_left (by omega) hs
        have := hfit μ
        omega
      funext ν
      apply Fin.ext
      rcases eq_or_ne ν μ with rfl | hν
      · rw [blockCorner_val, hnowrap]
        have hmod : ((y ν).val + s * (ell - 1)) % (s * ell) = s * (ell - 1) := by
          rw [show (y ν).val + s * (ell - 1) = (s * ell) * k + s * (ell - 1) by omega,
            Nat.mul_add_mod]
          exact Nat.mod_eq_of_lt (mul_lt_mul_of_pos_left (by omega) hs)
        omega
      · rw [blockCorner_val, stepPathSite_apply_ne s x μ ν i hν,
          ← blockCorner_val (s * ell) x ν,
          blockCorner_of_mem_blockOf hy (stepBlockOf_subset_blockOf hx)]
    -- the summand, as a `Finset.sum_ite_eq` shape
    have hterm : ∀ i ∈ Finset.range ell,
        RMap (coarsePathHolonomy s (trivialU L) y (coarseTransportPath s y x μ i))
          (coarseValAt s (stepLift s ell F) (stepPathSite s x μ i) μ)
          = if i = ell - 1 - j then (ell : ℝ) • F (⟨y, hy⟩, μ) else 0 := by
      intro i hi
      have hi' : i < ell := Finset.mem_range.mp hi
      rw [coarsePathHolonomy_trivialU, RMap_one, LinearMap.id_apply,
        coarseValAt_of_mem _ (stepPathSite_mem_coarseLattice hdvdS hxc μ i) μ]
      show stepLift s ell F (⟨stepPathSite s x μ i, _⟩, μ) = _
      unfold stepLift
      by_cases hhit : ((stepPathSite s x μ i) μ).val % (s * ell) = s * ell - s
      · have heq : j + i = ell - 1 := (hcond i hi').1 hhit
        have hsub : (⟨blockCorner (s * ell) (stepPathSite s x μ i), blockCorner_mem _⟩ :
            {w : PeriodicLatticeSite L // w ∈ CoarseLattice L (s * ell)}) = ⟨y, hy⟩ :=
          Subtype.ext (hcorner i hi' heq)
        rw [if_pos hhit, if_pos (by omega : i = ell - 1 - j)]
        exact congrArg
          (fun z : {w : PeriodicLatticeSite L // w ∈ CoarseLattice L (s * ell)} =>
            (ell : ℝ) • F (z, μ)) hsub
      · have hne : ¬ (i = ell - 1 - j) := by
          intro hcon
          exact hhit ((hcond i hi').2 (by omega))
        rw [if_neg hhit, if_neg hne]
    rw [Finset.sum_congr rfl hterm,
      Finset.sum_ite_eq' (Finset.range ell) (ell - 1 - j) (fun _ => (ell : ℝ) • F (⟨y, hy⟩, μ)),
      if_pos (Finset.mem_range.mpr (by omega))]
  show stepBondAvgAt s (trivialU L) ell (stepLift s ell F) y μ = F (⟨y, hy⟩, μ)
  unfold stepBondAvgAt
  rw [Finset.sum_congr rfl hline, Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    smul_smul]
  have hne : ((ell : ℝ)) ^ 4 ≠ 0 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  push_cast
  rw [show 1 / (ell : ℝ) ^ 4 * (ell : ℝ) ^ 3 * (ell : ℝ) = 1 by field_simp, one_smul]

/-- **`Q^{(s)}(1)` is surjective** — the second property `Rung` consumes, at general stride. -/
theorem qStepCLM_surjective_trivialU {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell)
    (hdvd : ∀ ν : Fin 3, (s * ell) ∣ (L ν + 1)) :
    Function.Surjective (qStepCLM s (trivialU L) ell) := by
  intro G
  refine ⟨WithLp.toLp 2 (stepLift s ell (WithLp.ofLp G)), ?_⟩
  refine (WithLp.linearEquiv 2 ℝ (CoarseBond L (s * ell) → SuTwo)).injective ?_
  funext b
  show stepBondAvg s (trivialU L) ell (stepLift s ell (WithLp.ofLp G)) b = WithLp.ofLp G b
  exact stepBondAvg_stepLift hs hell hdvd (WithLp.ofLp G) b

/-- **`Q^{(s)*}(1)` is injective** — the third property `Rung` consumes (`Rung.hQstarInj`),
obtained from surjectivity by the tree's own `qstar_injective_of_surjective` (LAW-19). -/
theorem qStepStar_injective_trivialU {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell)
    (hdvd : ∀ ν : Fin 3, (s * ell) ∣ (L ν + 1)) :
    Function.Injective (qStepStarCLM s (trivialU L) ell) :=
  AdalyFormal.Balaban.BridgeInverse.qstar_injective_of_surjective _ _
    (qStep_hadj s (trivialU L) ell) (qStepCLM_surjective_trivialU hs hell hdvd)

/-! ## §9 — CONTROLS AND THE BINDER AUDIT

**Binder audit.** Every theorem below that asserts a POSITIVE fact about `Q^{(s)}` carries
`0 < s`, `0 < ell` and a divisibility hypothesis, and §9a shows each is load-bearing:

* `s * ell = 0` ⟹ the strided block is EMPTY and the operator is identically `0`
  (`stepBondAvgAt_of_mul_zero`) — so `0 < s` and `0 < ell` are not decoration.
* `(s·ell) ∤ (L ν + 1)` ⟹ `card_stepBlockOf` fails (the tree's truncation artifact) AND the
  `s`-sublattice is not preserved by the periodic wrap, so `coarseValAt`'s `0` branch fires on a
  genuinely nonzero field (`coarseValAt_drops_without_dvd`, an explicit `3³` witness).
* The `∀ j' < j` form of `qCompositeCLM_opNorm_le`'s hypothesis is deliberate: `∀ j` would be
  UNSATISFIABLE on any finite torus (`ell^j` eventually exceeds `L ν + 1`), which would make the
  theorem vacuous. §9c instantiates it at depth `3` on the `8³` torus, where it is not.
-/

section Controls

/-! ### §9a — the degenerate strides -/

/-- The strided block is EMPTY as soon as `s · ell = 0`. -/
theorem stepBlockOf_empty_of_mul_zero (y : PeriodicLatticeSite L) {s ell : ℕ} (h : s * ell = 0) :
    stepBlockOf y s ell = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  obtain ⟨h1, h2, -⟩ := mem_stepBlockOf.mp hx 0
  rw [h] at h2
  omega

/-- …hence the operator is identically `0` there. Recorded, not assumed away. -/
theorem stepBondAvgAt_of_mul_zero {s ell : ℕ} (h : s * ell = 0)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) :
    stepBondAvgAt s V ell A c μ = 0 := by
  unfold stepBondAvgAt
  rw [stepBlockOf_empty_of_mul_zero c h, Finset.sum_empty, smul_zero]

/-! ### §9b — MUST-FIRE: the normalisation is a TRUE AVERAGE at every stride -/

/-- **`Q^{(s)}` returns the constant field exactly, at every stride.** This is the theorem that
pins `ell^{-4}`: replace the prefactor by `t · ell^{-4}` and the conclusion becomes `t • v`, so the
normalisation cannot be rescaled without breaking it. It also pins the SUMMAND COUNT — `ell^3`
block members and `ell` line steps — since the proof consumes `card_stepBlockOf` and
`Finset.card_range` and nothing else. -/
theorem stepBondAvgAt_const_trivialU {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell)
    (hdvd : ∀ ν : Fin 3, (s * ell) ∣ (L ν + 1)) {c : PeriodicLatticeSite L}
    (hc : c ∈ CoarseLattice L (s * ell)) (μ : Fin 3) (v : SuTwo) :
    stepBondAvgAt s (trivialU L) ell (fun _ => v) c μ = v := by
  have hdvdS : ∀ ν : Fin 3, s ∣ (L ν + 1) :=
    fun ν => dvd_trans (Dvd.intro ell rfl) (hdvd ν)
  have hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1 := coarseLattice_mem_fits hdvd hc
  have hcard : (stepBlockOf c s ell).card = ell ^ 3 := card_stepBlockOf c s ell hs hfit
  have hterm : ∀ x ∈ stepBlockOf c s ell,
      (∑ i ∈ Finset.range ell,
        RMap (coarsePathHolonomy s (trivialU L) c (coarseTransportPath s c x μ i))
          (coarseValAt s (fun _ => v) (stepPathSite s x μ i) μ)) = (ell : ℝ) • v := by
    intro x hx
    have hxc : x ∈ CoarseLattice L s := stepBlock_mem_coarseLattice hc hx
    have hpt : ∀ i ∈ Finset.range ell,
        RMap (coarsePathHolonomy s (trivialU L) c (coarseTransportPath s c x μ i))
          (coarseValAt s (fun _ => v) (stepPathSite s x μ i) μ) = v := by
      intro i _
      rw [coarsePathHolonomy_trivialU, RMap_one, LinearMap.id_apply,
        coarseValAt_of_mem _ (stepPathSite_mem_coarseLattice hdvdS hxc μ i) μ]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ]
  unfold stepBondAvgAt
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    smul_smul]
  push_cast
  rw [show 1 / (ell : ℝ) ^ 4 * (ell : ℝ) ^ 3 * (ell : ℝ) = 1 by field_simp, one_smul]

/-- **SHARPNESS**: `ell^3 · ‖Q^{(s)} A‖² = ‖A‖²` on the constant field at `V = 1`. So
`q_s = ell^{-3/2}` is the OPERATOR NORM, not an over-estimate, and `qStepCLM_normSq_le` cannot be
improved. Every inequality in §6's chain is an equality here. -/
theorem qStepCLM_normSq_sharp {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell)
    (hdvd : ∀ ν : Fin 3, (s * ell) ∣ (L ν + 1)) (v : SuTwo) :
    ((ell : ℝ) ^ 3)
        * ‖qStepCLM s (trivialU L) ell (WithLp.toLp 2 (fun _ : CoarseBond L s => v))‖ ^ 2
      = ‖(WithLp.toLp 2 (fun _ : CoarseBond L s => v) : CoarseFnL2 L s)‖ ^ 2 := by
  classical
  have himg : qStepCLM s (trivialU L) ell (WithLp.toLp 2 (fun _ : CoarseBond L s => v))
      = WithLp.toLp 2 (fun _ : CoarseBond L (s * ell) => v) := by
    refine (WithLp.linearEquiv 2 ℝ (CoarseBond L (s * ell) → SuTwo)).injective ?_
    funext b
    show stepBondAvg s (trivialU L) ell (fun _ : CoarseBond L s => v) b = v
    exact stepBondAvgAt_const_trivialU hs hell hdvd b.1.2 b.2 v
  rw [himg, norm_const_sq, norm_const_sq, card_coarseLattice_step hs hell hdvd]
  push_cast
  ring

/-- The `8³` torus: `L ν + 1 = 8`, so `2`, `4` and `8` all divide it — enough for a depth-`3`
ladder at `ell = 2`, with strides `1, 2, 4`. -/
def qsWitL : PeriodicLatticeExtent := fun _ => 7

theorem qsWitL_dvd_four : ∀ ν : Fin 3, (2 * 2 : ℕ) ∣ (qsWitL ν + 1) := by decide

/-- The lattice origin, a member of every coarse lattice. -/
def qsOrigin : PeriodicLatticeSite qsWitL := fun _ => 0

theorem qsOrigin_mem : qsOrigin ∈ CoarseLattice qsWitL (2 * 2) :=
  mem_CoarseLattice.mpr (by decide)

/-- **MUST-FIRE at `s = 2`**: on the named constant field the operator returns a NONZERO value.
So the `stepBondAvgAt_cross_direction` control below (which returns `0`) is a genuine
must-not-fire, not the operator being identically zero. -/
theorem stepBondAvgAt_mustfire_s2 :
    stepBondAvgAt 2 (trivialU qsWitL) 2 (fun _ => suTwoWitness) qsOrigin 0 ≠ 0 := by
  rw [stepBondAvgAt_const_trivialU (by norm_num) (by norm_num) qsWitL_dvd_four qsOrigin_mem]
  exact suTwoWitness_ne_zero

/-- **MUST-FIRE FOR THE TRANSPORT.** `stepBondAvgAt_mustfire_s2` fires at the TRIVIAL background,
so on its own it does not test that the holonomy is doing anything. This one does: at stride `1` the
operator's value on `Q1Real.d4ConfigSuTwo` DIFFERS between `trivialU` and `witnessU` — a real sign
flip through the forward holonomy. It is obtained by pushing the tree's own
`LineIntegralCovariant.lineCoarseRestrictCov_genuinely_U_dependent` through §4's anchor, which is
what an anchor is FOR: `V`-dependence is inherited, not re-derived. -/
theorem stepBondAvgAt_genuinely_V_dependent :
    stepBondAvgAt 1 (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU
        AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
        AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
        (fun e : CoarseBond AdalyFormal.Balaban.AdmissibleSubspace.witnessL 1 =>
          AdalyFormal.Balaban.Q1Real.d4ConfigSuTwo (e.1.1, e.2))
        (AdalyFormal.Balaban.QOne.targetCoarseBond.1.1)
        (AdalyFormal.Balaban.QOne.targetCoarseBond.2)
      ≠ stepBondAvgAt 1 AdalyFormal.Balaban.CovariantOperators.witnessU
        AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
        (fun e : CoarseBond AdalyFormal.Balaban.AdmissibleSubspace.witnessL 1 =>
          AdalyFormal.Balaban.Q1Real.d4ConfigSuTwo (e.1.1, e.2))
        (AdalyFormal.Balaban.QOne.targetCoarseBond.1.1)
        (AdalyFormal.Balaban.QOne.targetCoarseBond.2) := by
  have hle : AdalyFormal.Balaban.AdmissibleSubspace.witnessEll
      ≤ AdalyFormal.Balaban.AdmissibleSubspace.witnessL
          AdalyFormal.Balaban.QOne.targetCoarseBond.2 + 1 := by
    show (2 : ℕ) ≤ 3 + 1
    norm_num
  rw [stepBondAvgAt_one_eq _ _ _ _ hle, stepBondAvgAt_one_eq _ _ _ _ hle]
  exact AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov_genuinely_U_dependent

/-! ### §9c — MUST-NOT-FIRE, and the composition law with numbers -/

/-- A single-coarse-bond test field. -/
noncomputable def coarseDelta (s : ℕ) (f : CoarseBond L s) (v : SuTwo) : CoarseBond L s → SuTwo :=
  fun e => if e = f then v else 0

/-- **MUST-NOT-FIRE**: a field supported on a bond of a DIFFERENT direction is invisible to
`Q^{(s)}` at direction `μ`. Every summand reads direction `μ` only, so the operator does not
report nonzero on everything. -/
theorem stepBondAvgAt_cross_direction (s ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (f : CoarseBond L s) (v : SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) (hne : f.2 ≠ μ) :
    stepBondAvgAt s V ell (coarseDelta s f v) c μ = 0 := by
  unfold stepBondAvgAt
  have hterm : ∀ x ∈ stepBlockOf c s ell,
      (∑ i ∈ Finset.range ell,
        RMap (coarsePathHolonomy s V c (coarseTransportPath s c x μ i))
          (coarseValAt s (coarseDelta s f v) (stepPathSite s x μ i) μ)) = 0 := by
    intro x _
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hz : coarseValAt s (coarseDelta s f v) (stepPathSite s x μ i) μ = 0 := by
      unfold coarseValAt coarseDelta
      by_cases h : stepPathSite s x μ i ∈ CoarseLattice L s
      · rw [dif_pos h, if_neg]
        intro hcon
        exact hne (congrArg (fun e : CoarseBond L s => e.2) hcon).symm
      · rw [dif_neg h]
    rw [hz, map_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, smul_zero]

/-- **THE COMPOSITION LAW WITH NUMBERS**: at `ell = 2` on the `8³` torus, the depth-`2` composite
is literally the stride-`2` step applied to the stride-`1` step, landing on `CoarseFnL2 _ 4`.
TWO DIFFERENT STRIDES, `1` and `2`, in one identity. -/
theorem qCompositeCLM_two_strides
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsWitL)
    (A : CoarseFnL2 qsWitL 1) :
    qCompositeCLM bg 2 2 A = qStepCLM 2 (bg 1) 2 (qStepCLM 1 (bg 0) 2 A) := rfl

/-- Depth `3` at `ell = 2` uses strides `1, 2, 4`; on the `8³` torus all three divisibilities
hold. This is what makes the depth-`3` norm bound a statement about a NONEMPTY situation. -/
theorem qsWitL_dvd_upto_three : ∀ j' < 3, ∀ ν : Fin 3, (2 ^ j' * 2 : ℕ) ∣ (qsWitL ν + 1) := by
  decide

/-- **THE LADDER AT DEPTH 3, WITH ITS CONSTANT**: `‖Q_comp‖ ≤ (2^{-3/2})^3 = 8^{-3/2}` on the
`8³` torus at `ell = 2`. The tower is instantiable at depth, and its constant is explicit. -/
theorem qCompositeCLM_depth_three
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsWitL) :
    ‖qCompositeCLM bg 2 3‖ ≤ Real.sqrt (1 / (2 : ℝ) ^ 3) ^ 3 :=
  qCompositeCLM_opNorm_le (by norm_num) bg 3 qsWitL_dvd_upto_three

/-! ### §9d — the divisibility hypothesis is LOAD-BEARING (S83)

If `s ∤ (L ν + 1)`, the periodic wrap carries the `s`-sublattice off itself, and the operator's
own summand lands OUTSIDE `CoarseBond L s`, where `coarseValAt` returns `0`. On the `3³` torus at
`s = 2` this is exhibited concretely: the site with all coordinates `2` is on the `2`-lattice, one
strided step in direction `0` lands on coordinate `(2+2) % 3 = 1`, which is not — so a field that
is `suTwoWitness` EVERYWHERE is read as `0` there. -/

/-- The `3³` torus: `L ν + 1 = 3`, and `2 ∤ 3`. -/
def qsWitLbad : PeriodicLatticeExtent := fun _ => 2

theorem qsWitLbad_not_dvd : ¬ ((2 : ℕ) ∣ (qsWitLbad 0 + 1)) := by decide

def qsBadSite : PeriodicLatticeSite qsWitLbad := fun _ => ⟨2, Nat.lt_succ_self 2⟩

theorem qsBadSite_mem : qsBadSite ∈ CoarseLattice qsWitLbad 2 :=
  mem_CoarseLattice.mpr (by decide)

/-- One strided step leaves the `s`-sublattice when `s ∤ (L ν + 1)`. -/
theorem stepPathSite_leaves_lattice :
    stepPathSite 2 qsBadSite 0 1 ∉ CoarseLattice qsWitLbad 2 := by
  rw [mem_CoarseLattice]
  intro hcon
  have h := hcon 0
  rw [stepPathSite_apply_self_val] at h
  revert h
  decide

/-- **THE S83 CONTROL**: without the divisibility hypothesis a genuinely nonzero field IS dropped
by the operator's own read. So `stepPathSite_mem_coarseLattice`'s `hdvdS` is not decoration. -/
theorem coarseValAt_drops_without_dvd :
    coarseValAt 2 (fun _ : CoarseBond qsWitLbad 2 => suTwoWitness)
        (stepPathSite 2 qsBadSite 0 1) 0 = 0 ∧ suTwoWitness ≠ (0 : SuTwo) :=
  ⟨coarseValAt_of_not_mem _ stepPathSite_leaves_lattice 0, suTwoWitness_ne_zero⟩

end Controls


/-! ## §11 — CONTENT-SENSITIVE TRANSPORT AT STRIDE `s > 1`

§9b's must-fires are all proved at `V = trivialU`, where `TowerLawCov.coarsePathHolonomy_trivialU`
returns `1` for ANY path argument. They therefore certify the COUNTING structure of the strided
block (how many summands, where each reads the field) and nothing about the CONTOUR: substituting
`[]` for `coarseTransportPath s c x μ i` reproduces every one of them verbatim. `s = 1` is covered
(`stepBondAvgAt_genuinely_V_dependent`, inherited through §4's anchor), but at `s > 1` the tree had
no test that the straight-leg-extended contour is the one actually traversed.

This section supplies one, at every stride and every `ell`. The probe is a SINGLE-BOND field placed
at the FAR ENDPOINT `c + s·ell·e_μ` of the strided line — one full coarse bond beyond the block.
`stepPathSite_eq_far_iff` shows that endpoint is reached only by summands with `i ≥ 1`, i.e. only
along a genuine STRAIGHT LEG, and `farDelta_weighted_sum` collapses the `ell⁴`-term double sum to
those summands for an ARBITRARY weight family. Feeding that lemma the real transport, the
staircase-only transport, and the constant `[]` therefore yields three DIFFERENT closed forms:

    real       :  ((ell−1)/ell⁴) · R( V(c,μ)·V(c+s·e_μ,μ)···V(c+s(ell−1)e_μ,μ) )   applied to `w`
    Γ-only     :  Σ_{1≤i<ell} ell⁻⁴ · R( holonomy of the first `ell−i` links )
    `[]`       :  ((ell−1)/ell⁴) · w

and the two mutations are separated from the real operator by a kernel-checked `≠` on named
backgrounds at `s = 2` (`8³` torus) and at `s = 4` (`16³` torus). The marked link in those
witnesses sits at `(c + s·e_μ, μ)`, which no staircase from `c` to a block member ever traverses at
`ell = 2` — the staircase's `μ`-segment there has length ≤ 1, so it can only use `(c,μ)`.

### WHAT THIS SECTION DOES AND DOES **NOT** TEST — read before citing the mutation kills

Two disclosures, both load-bearing for anyone reading the "kills" as coverage rather than as a list
of named facts. Item 1 has since been CLOSED and is retained struck; item 2 names where its
coverage actually lives.

**Warning on one cited file.** `compute/strided_repair/PROGRESS.md` is cited below for a
construction sketch. Its "Reach, stated plainly" section also asserts that §11 "tests the STRAIGHT
LEG …, its length, its base point and its direction". That LENGTH claim is FALSE of the witnesses
as they stood when it was written — `dropTerminal_cannot_separate_interior_ell4` below is the
kernel proof that a transport reading `ell − 1` links instead of `ell` reproduced the `ell = 4`
witness exactly. It is true only once `section StraightLegWitnessTerminal` is included. That file
is another lane's record and is not edited from here.

1. ~~**The descending coordinate order of the staircase is NOT tested here at `s > 1`.**~~
   **SUPERSEDED — the order IS now tested; the paragraph is retained struck.** It was accurate of
   the ON-AXIS probes and remains an accurate description of them: `coarseGammaPath` concatenates
   its coordinate segments in the descending order `2, 1, 0` (CMP95 (1.7)); every summand surviving
   an on-axis far-endpoint probe has `x = c + s·(ell−i)·e_μ`, a site differing from `c` in the
   SINGLE coordinate `μ`, so those staircases are pure `μ`-segments
   (`coarseGammaPath_replicate_stride`) and the segment order cannot enter their values.
   ~~What is no longer true is the conclusion that no control in this file pins the order.~~
   **CORRECTED — that sentence overclaimed and is retained struck. What `section
   StraightLegOffAxis` pins is the RELATIVE order of the two segments that are NON-EMPTY at its
   witness (`2` before `0`). Its surviving site `qsOrdX` shares coordinate `1` with `qsOrigin`, so
   the middle segment is empty there (`qsOrdX_middle_segment_empty`) and its relocation is
   invisible: the order `2,0,1` reproduces that witness's value exactly
   (`stepBondAvgAtOrd201_eq_real_at_ordX`, kernel-proved below). The FULL three-way order is pinned
   only by `section StraightLegOffAxisFull`, whose witness differs from the block corner in all
   three coordinates and whose `stepBondAvgAt_ne_ord_full` separates the real order from all five
   relocations at once.** `section
   StraightLegOffAxis` below decouples the strided line's BASE from the block corner
   (`stepPathSite_eq_far_iff_base`, `farDelta_weighted_sum_base`), which puts the surviving site off
   the `μ`-axis of `c` and makes the staircase two-segment; `stepBondAvgAt_ne_ascOrder_offAxis` then
   kernel-separates the real operator from `stepBondAvgAtAscOrder`, the same staircase with its
   segments concatenated in ASCENDING order `0, 1, 2`. The construction sketched in
   `compute/strided_repair/PROGRESS.md` is the one carried out there.
2. **The straight leg's TERMINAL link is covered only by
   `section StraightLegWitnessTerminal` below.** The `ell = 4` witness `qsBig4U` marks INTERIOR
   position `2`; a transport dropping exactly the last link of the strided line reproduces its
   value. That escape (mutation D) is defined, valued and killed at the end of this section, on a
   witness that marks the terminal position `3`. Do not read the `qsBig4U` kills as excluding it.
-/

section StraightLegTransport

open AdalyFormal.Balaban.CovariantOperators (witnessMElem RMap_witnessMElem)
open AdalyFormal.Balaban.QjComposite (coarsePathHolonomy_nil coarsePathHolonomy_cons)

section StraightLeg

/-! ### helpers -/

theorem coarseCoordSteps_of_le {s : ℕ} {y x : PeriodicLatticeSite L} (μ : Fin 3)
    (h : (y μ).val ≤ (x μ).val) :
    coarseCoordSteps s y x μ = ((x μ).val - (y μ).val) / s := by
  unfold coarseCoordSteps
  rw [Fin.sub_val_of_le (Fin.le_def.mpr h)]

/-- **The staircase to the `k`-th strided neighbour is `k` coarse links in direction `μ`.** -/
theorem coarseGammaPath_replicate_stride {s : ℕ} (hs : 0 < s) (c : PeriodicLatticeSite L)
    (μ : Fin 3) (k : ℕ) (hlt : (c μ).val + s * k < L μ + 1) :
    coarseGammaPath s c (stepPathSite s c μ k) = List.replicate k μ := by
  have h21 : ((2 : Fin 3)) ≠ ((1 : Fin 3)) := by decide
  have h20 : ((2 : Fin 3)) ≠ ((0 : Fin 3)) := by decide
  have h10 : ((1 : Fin 3)) ≠ ((0 : Fin 3)) := by decide
  have hxmu : ((stepPathSite s c μ k) μ).val = (c μ).val + s * k := by
    rw [stepPathSite_apply_self_val]
    exact Nat.mod_eq_of_lt hlt
  have hxne : ∀ ν : Fin 3, ν ≠ μ → (stepPathSite s c μ k) ν = c ν :=
    fun ν hν => stepPathSite_apply_ne s c μ ν k hν
  have key : ∀ (ν : Fin 3) (b : PeriodicLatticeSite L), b ν = c ν →
      coarseCoordSteps s b (stepPathSite s c μ k) ν = if ν = μ then k else 0 := by
    intro ν b hb
    have hbv : (b ν).val = (c ν).val := by rw [hb]
    rcases eq_or_ne ν μ with rfl | hν
    · rw [if_pos rfl, coarseCoordSteps_of_le ν (by rw [hbv, hxmu]; omega), hbv, hxmu,
        Nat.add_sub_cancel_left, Nat.mul_div_cancel_left k hs]
    · have hxv : ((stepPathSite s c μ k) ν).val = (c ν).val := by rw [hxne ν hν]
      rw [if_neg hν, coarseCoordSteps_of_le ν (by rw [hbv, hxv]), hbv, hxv,
        Nat.sub_self, Nat.zero_div]
  have hb1 : (Function.update c 2 ((stepPathSite s c μ k) 2) : PeriodicLatticeSite L) 1 = c 1 :=
    Function.update_of_ne h21.symm _ _
  have hb0 : (Function.update (Function.update c 2 ((stepPathSite s c μ k) 2)) 1
      ((stepPathSite s c μ k) 1) : PeriodicLatticeSite L) 0 = c 0 := by
    rw [Function.update_of_ne h10.symm, Function.update_of_ne h20.symm]
  simp only [coarseGammaPath, coarseStraightSegment, key 2 c rfl, key 1 _ hb1, key 0 _ hb0]
  fin_cases μ <;> simp

/-- `s·k` fits strictly inside the block width `s·ell` when `k < ell`. Kept as its own step because
`omega` cannot relate the atoms `s * k` and `s * ell`. -/
theorem mul_lt_of_lt_stride {s ell k : ℕ} (_hs : 0 < s) (hk : k < ell) :
    s * k + s ≤ s * ell := by
  have h1 : s * (k + 1) ≤ s * ell := Nat.mul_le_mul_left s (by omega)
  rw [Nat.mul_succ] at h1
  exact h1

/-- The `k`-th strided neighbour lies in the strided block, for `k < ell`. -/
theorem stepPathSite_mem_stepBlock_of_lt {s ell : ℕ} (hs : 0 < s) {c : PeriodicLatticeSite L}
    (μ : Fin 3) {k : ℕ} (hk : k < ell)
    (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) :
    stepPathSite s c μ k ∈ stepBlockOf c s ell := by
  have hb := mul_lt_of_lt_stride hs hk
  rw [mem_stepBlockOf]
  intro ν
  rcases eq_or_ne ν μ with rfl | hν
  · have hfitν := hfit ν
    have hv : ((stepPathSite s c ν k) ν).val = (c ν).val + s * k := by
      rw [stepPathSite_apply_self_val]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨by omega, by omega, ?_⟩
    rw [hv, Nat.add_sub_cancel_left]
    exact Dvd.intro k rfl
  · rw [stepPathSite_apply_ne s c μ ν k hν]
    have hfitν := hfit ν
    exact ⟨le_refl _, by omega, by simp⟩

/-! ### the far-endpoint uniqueness lemma -/

/-- **UNIQUE PREIMAGE OF THE FAR ENDPOINT, AT EVERY STRIDE AND EVERY `ell`.** The site
`c + s·ell·e_μ` — one full coarse bond beyond the block — is hit by the strided walk of
`x ∈ B_s(c)`, `i < ell` exactly when `i ≥ 1` and `x = c + s·(ell−i)·e_μ`. Every such summand has
`i ≥ 1`, so EVERY surviving summand's transport path contains a genuine STRAIGHT LEG. The
hypothesis `s·ell < L μ + 1` is load-bearing: if the torus is exactly one coarse bond wide in
direction `μ` the far endpoint wraps back onto `c` and `(x,i) = (c,0)` becomes a second preimage. -/
theorem stepPathSite_eq_far_iff {s ell : ℕ} (hs : 0 < s) {c : PeriodicLatticeSite L} (μ : Fin 3)
    (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) (hroom : s * ell < L μ + 1)
    {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf c s ell) {i : ℕ} (hi : i < ell) :
    stepPathSite s x μ i = stepPathSite s c μ ell ↔ (1 ≤ i ∧ x = stepPathSite s c μ (ell - i)) := by
  have hfitμ := hfit μ
  have hxμ := mem_stepBlockOf.mp hx μ
  obtain ⟨a, ha⟩ := hxμ.2.2
  have hxval : (x μ).val = (c μ).val + s * a := by omega
  have halt : a < ell := by
    by_contra hcon
    have hle : s * ell ≤ s * a := Nat.mul_le_mul_left s (by omega)
    omega
  have hBa := mul_lt_of_lt_stride hs halt
  have hBi := mul_lt_of_lt_stride hs hi
  constructor
  · intro heq
    have hmu : ((c μ).val + (s * a + s * i)) % (L μ + 1)
        = ((c μ).val + s * ell) % (L μ + 1) := by
      rw [← Nat.add_assoc, ← hxval, ← stepPathSite_apply_self_val s x μ i,
        ← stepPathSite_apply_self_val s c μ ell, heq]
    have hcancel : (s * a + s * i) ≡ (s * ell) [MOD (L μ + 1)] :=
      Nat.ModEq.add_left_cancel' (c μ).val hmu
    have hsum : s * a + s * i = s * ell := by
      rcases Nat.lt_or_ge (s * a + s * i) (s * ell) with hlt | hge
      · have hdvd := (Nat.modEq_iff_dvd' (le_of_lt hlt)).mp hcancel
        have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
      · have hdvd := (Nat.modEq_iff_dvd' hge).mp hcancel.symm
        have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
    have hai : s * (a + i) = s * ell := by rw [Nat.mul_add]; exact hsum
    have haisum : a + i = ell := Nat.eq_of_mul_eq_mul_left hs hai
    have hione : 1 ≤ i := by omega
    refine ⟨hione, ?_⟩
    funext ν
    rcases eq_or_ne ν μ with rfl | hν
    · apply Fin.ext
      rw [stepPathSite_apply_self_val, hxval, show ell - i = a by omega,
        Nat.mod_eq_of_lt (by omega)]
    · have hcf := congrFun heq ν
      rw [stepPathSite_apply_ne s x μ ν i hν, stepPathSite_apply_ne s c μ ν ell hν] at hcf
      rw [hcf, stepPathSite_apply_ne s c μ ν (ell - i) hν]
  · rintro ⟨hione, rfl⟩
    show pathSite (pathSite c μ (s * (ell - i))) μ (s * i) = pathSite c μ (s * ell)
    rw [pathSite_add, ← Nat.mul_add, Nat.add_sub_cancel' (le_of_lt hi)]

/-! ### the single-bond probe and the collapse -/

/-- Reading the far-endpoint delta field along the strided walk. -/
theorem coarseValAt_farDelta {s ell : ℕ} (hs : 0 < s) {c : PeriodicLatticeSite L} {μ : Fin 3}
    (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) (hroom : s * ell < L μ + 1)
    (ht : stepPathSite s c μ ell ∈ CoarseLattice L s) (w : SuTwo)
    {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf c s ell) {i : ℕ} (hi : i < ell) :
    coarseValAt s (coarseDelta s (⟨stepPathSite s c μ ell, ht⟩, μ) w) (stepPathSite s x μ i) μ
      = if 1 ≤ i ∧ x = stepPathSite s c μ (ell - i) then w else 0 := by
  by_cases hcase : 1 ≤ i ∧ x = stepPathSite s c μ (ell - i)
  · have heq : stepPathSite s x μ i = stepPathSite s c μ ell :=
      (stepPathSite_eq_far_iff hs μ hfit hroom hx hi).mpr hcase
    have hz : stepPathSite s x μ i ∈ CoarseLattice L s := by rw [heq]; exact ht
    rw [if_pos hcase, coarseValAt_of_mem _ hz μ]
    simp only [coarseDelta]
    rw [if_pos]
    simp only [Prod.mk.injEq, Subtype.mk.injEq, and_true]
    exact heq
  · rw [if_neg hcase]
    by_cases hz : stepPathSite s x μ i ∈ CoarseLattice L s
    · rw [coarseValAt_of_mem _ hz μ]
      simp only [coarseDelta]
      rw [if_neg]
      intro hcon
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hcon
      exact hcase ((stepPathSite_eq_far_iff hs μ hfit hroom hx hi).mp hcon.1)
    · exact coarseValAt_of_not_mem _ hz μ

/-- `∑_{i<n} [1 ≤ i] z = (n−1)·z`. -/
theorem sum_range_ite_one_le {M : Type*} [AddCommMonoid M] (n : ℕ) (z : M) :
    (∑ i ∈ Finset.range n, if 1 ≤ i then z else 0) = (n - 1) • z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have h1 : 1 ≤ n := hn
        rw [if_pos h1, show n + 1 - 1 = (n - 1) + 1 by omega, succ_nsmul]

/-- **THE COLLAPSE.** For ANY weight family `g` the double sum of the far-endpoint delta probe
collapses to the weights AT THE STRAIGHT-LEG POSITIONS `(c + s·(ell−i)·e_μ, i)`, `i = 1 … ell−1`.
Instantiating `g` with the real transport, with the staircase-only transport, and with the empty
path gives three DIFFERENT values below — which is what makes this a content-sensitive test. -/
theorem farDelta_weighted_sum {s ell : ℕ} (hs : 0 < s) {c : PeriodicLatticeSite L} {μ : Fin 3}
    (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) (hroom : s * ell < L μ + 1)
    (ht : stepPathSite s c μ ell ∈ CoarseLattice L s) (w : SuTwo)
    (g : PeriodicLatticeSite L → ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
        RMap (g x i) (coarseValAt s (coarseDelta s (⟨stepPathSite s c μ ell, ht⟩, μ) w)
          (stepPathSite s x μ i) μ))
      = ∑ i ∈ Finset.range ell,
          (if 1 ≤ i then RMap (g (stepPathSite s c μ (ell - i)) i) w else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hilt : i < ell := Finset.mem_range.mp hi
  have hterm : ∀ x ∈ stepBlockOf c s ell,
      RMap (g x i) (coarseValAt s (coarseDelta s (⟨stepPathSite s c μ ell, ht⟩, μ) w)
        (stepPathSite s x μ i) μ)
        = if 1 ≤ i ∧ x = stepPathSite s c μ (ell - i) then RMap (g x i) w else 0 := by
    intro x hx
    rw [coarseValAt_farDelta hs hfit hroom ht w hx hilt]
    split
    · rfl
    · exact map_zero _
  rw [Finset.sum_congr rfl hterm]
  by_cases h1 : 1 ≤ i
  · have hmem : stepPathSite s c μ (ell - i) ∈ stepBlockOf c s ell :=
      stepPathSite_mem_stepBlock_of_lt hs μ (by omega) hfit
    rw [if_pos h1]
    simp only [h1, true_and]
    rw [Finset.sum_ite_eq' (stepBlockOf c s ell) (stepPathSite s c μ (ell - i))
      (fun x => RMap (g x i) w), if_pos hmem]
  · rw [if_neg h1]
    exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => h1 h.1))

/-! ### the two path mutations, IN FILE -/

/-- **MUTATION A (the prosecutor's own):** the transport argument replaced by the constant `[]`. -/
noncomputable def stepBondAvgAtNoTransport (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (1 / (ell : ℝ) ^ 4) • ∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
    RMap (coarsePathHolonomy s V c ([] : List (Fin 3)))
      (coarseValAt s A (stepPathSite s x μ i) μ)

/-- **MUTATION B (the sharper one):** the STRAIGHT LEG deleted, staircase kept. -/
noncomputable def stepBondAvgAtGammaOnly (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (1 / (ell : ℝ) ^ 4) • ∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
    RMap (coarsePathHolonomy s V c (coarseGammaPath s c x))
      (coarseValAt s A (stepPathSite s x μ i) μ)

/-! ### the three values -/

/-- **THE REAL OPERATOR'S VALUE**: the holonomy of the FULL strided line of `ell` coarse links,
`V(c,μ)·V(c+s·e_μ,μ)···V(c+s(ell−1)e_μ,μ)`. Only `V(c,μ)` is reachable from the staircase; every
other factor is supplied by a STRAIGHT LEG. General stride `s`, general `ell`. -/
theorem stepBondAvgAt_farDelta_value {s ell : ℕ} (hs : 0 < s) {c : PeriodicLatticeSite L}
    {μ : Fin 3} (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) (hroom : s * ell < L μ + 1)
    (ht : stepPathSite s c μ ell ∈ CoarseLattice L s)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (w : SuTwo) :
    stepBondAvgAt s V ell (coarseDelta s (⟨stepPathSite s c μ ell, ht⟩, μ) w) c μ
      = (((ell - 1 : ℕ) : ℝ) / (ell : ℝ) ^ 4)
          • RMap (coarsePathHolonomy s V c (List.replicate ell μ)) w := by
  have hhol : ∀ i, 1 ≤ i → i < ell →
      coarsePathHolonomy s V c (coarseTransportPath s c (stepPathSite s c μ (ell - i)) μ i)
        = coarsePathHolonomy s V c (List.replicate ell μ) := by
    intro i h1 h2
    have hb := mul_lt_of_lt_stride hs (show ell - i < ell by omega)
    have hfitμ := hfit μ
    have hg := coarseGammaPath_replicate_stride hs c μ (ell - i) (by omega)
    show coarsePathHolonomy s V c
      (coarseGammaPath s c (stepPathSite s c μ (ell - i)) ++ List.replicate i μ) = _
    rw [hg, ← List.replicate_add, show ell - i + i = ell by omega]
  unfold stepBondAvgAt
  rw [farDelta_weighted_sum hs hfit hroom ht w
    (fun x i => coarsePathHolonomy s V c (coarseTransportPath s c x μ i))]
  have hcong : ∀ i ∈ Finset.range ell,
      (if 1 ≤ i then
        RMap (coarsePathHolonomy s V c
          (coarseTransportPath s c (stepPathSite s c μ (ell - i)) μ i)) w else 0)
        = if 1 ≤ i then RMap (coarsePathHolonomy s V c (List.replicate ell μ)) w else 0 := by
    intro i hi
    by_cases h1 : 1 ≤ i
    · rw [if_pos h1, if_pos h1, hhol i h1 (Finset.mem_range.mp hi)]
    · rw [if_neg h1, if_neg h1]
  rw [Finset.sum_congr rfl hcong, sum_range_ite_one_le,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  field_simp

/-- **MUTATION A's VALUE**: the straight legs are GONE — the value is the flat one. -/
theorem stepBondAvgAtNoTransport_farDelta_value {s ell : ℕ} (hs : 0 < s)
    {c : PeriodicLatticeSite L} {μ : Fin 3}
    (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) (hroom : s * ell < L μ + 1)
    (ht : stepPathSite s c μ ell ∈ CoarseLattice L s)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (w : SuTwo) :
    stepBondAvgAtNoTransport s V ell (coarseDelta s (⟨stepPathSite s c μ ell, ht⟩, μ) w) c μ
      = (((ell - 1 : ℕ) : ℝ) / (ell : ℝ) ^ 4) • w := by
  unfold stepBondAvgAtNoTransport
  rw [farDelta_weighted_sum hs hfit hroom ht w
    (fun _ _ => coarsePathHolonomy s V c ([] : List (Fin 3)))]
  simp only [coarsePathHolonomy_nil, RMap_one, LinearMap.id_apply]
  rw [sum_range_ite_one_le, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  field_simp

/-- **MUTATION B's VALUE**: only the STAIRCASE links survive — the straight-leg factors are lost,
and with them every link beyond `c + s·(ell−i)·e_μ`. -/
theorem stepBondAvgAtGammaOnly_farDelta_value {s ell : ℕ} (hs : 0 < s)
    {c : PeriodicLatticeSite L} {μ : Fin 3}
    (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) (hroom : s * ell < L μ + 1)
    (ht : stepPathSite s c μ ell ∈ CoarseLattice L s)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (w : SuTwo) :
    stepBondAvgAtGammaOnly s V ell (coarseDelta s (⟨stepPathSite s c μ ell, ht⟩, μ) w) c μ
      = ∑ i ∈ Finset.range ell, (if 1 ≤ i then
          (1 / (ell : ℝ) ^ 4)
            • RMap (coarsePathHolonomy s V c (List.replicate (ell - i) μ)) w else 0) := by
  have hg : ∀ i, 1 ≤ i → i < ell →
      coarsePathHolonomy s V c (coarseGammaPath s c (stepPathSite s c μ (ell - i)))
        = coarsePathHolonomy s V c (List.replicate (ell - i) μ) := by
    intro i h1 h2
    have hb := mul_lt_of_lt_stride hs (show ell - i < ell by omega)
    have hfitμ := hfit μ
    rw [coarseGammaPath_replicate_stride hs c μ (ell - i) (by omega)]
  unfold stepBondAvgAtGammaOnly
  rw [farDelta_weighted_sum hs hfit hroom ht w
    (fun x _ => coarsePathHolonomy s V c (coarseGammaPath s c x)), Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h1 : 1 ≤ i
  · rw [if_pos h1, if_pos h1, hg i h1 (Finset.mem_range.mp hi)]
  · rw [if_neg h1, if_neg h1, smul_zero]

end StraightLeg

/-! ### `ell = 2` specialisation, and the numeric witnesses -/

section StraightLegTwo

theorem coarsePathHolonomy_replicate_one (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : PeriodicLatticeSite L) (μ : Fin 3) :
    coarsePathHolonomy s V c (List.replicate 1 μ) = V (c, μ) := by
  show coarsePathHolonomy s V c [μ] = _
  rw [coarsePathHolonomy_cons, coarsePathHolonomy_nil, mul_one]

theorem coarsePathHolonomy_replicate_two (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : PeriodicLatticeSite L) (μ : Fin 3) :
    coarsePathHolonomy s V c (List.replicate 2 μ)
      = V (c, μ) * V (stepPathSite s c μ 1, μ) := by
  have hstep : coarseShift c s μ = stepPathSite s c μ 1 := by
    rw [coarseShift_eq_pathSite]
    show pathSite c μ s = pathSite c μ (s * 1)
    rw [Nat.mul_one]
  show coarsePathHolonomy s V c [μ, μ] = _
  rw [coarsePathHolonomy_cons, coarsePathHolonomy_cons, coarsePathHolonomy_nil, mul_one, hstep]

/-- The `ell = 2` value: exactly two links, the STAIRCASE link `V(c,μ)` and the STRAIGHT-LEG link
`V(c+s·e_μ,μ)`. -/
theorem stepBondAvgAt_farDelta_value_two {s : ℕ} (hs : 0 < s) {c : PeriodicLatticeSite L}
    {μ : Fin 3} (hfit : ∀ ν : Fin 3, (c ν).val + s * 2 ≤ L ν + 1) (hroom : s * 2 < L μ + 1)
    (ht : stepPathSite s c μ 2 ∈ CoarseLattice L s)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (w : SuTwo) :
    stepBondAvgAt s V 2 (coarseDelta s (⟨stepPathSite s c μ 2, ht⟩, μ) w) c μ
      = (1 / 16 : ℝ) • RMap (V (c, μ) * V (stepPathSite s c μ 1, μ)) w := by
  rw [stepBondAvgAt_farDelta_value hs hfit hroom ht V w, coarsePathHolonomy_replicate_two]
  norm_num

/-- Mutation A at `ell = 2`. -/
theorem stepBondAvgAtNoTransport_farDelta_value_two {s : ℕ} (hs : 0 < s)
    {c : PeriodicLatticeSite L} {μ : Fin 3}
    (hfit : ∀ ν : Fin 3, (c ν).val + s * 2 ≤ L ν + 1) (hroom : s * 2 < L μ + 1)
    (ht : stepPathSite s c μ 2 ∈ CoarseLattice L s)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (w : SuTwo) :
    stepBondAvgAtNoTransport s V 2 (coarseDelta s (⟨stepPathSite s c μ 2, ht⟩, μ) w) c μ
      = (1 / 16 : ℝ) • w := by
  rw [stepBondAvgAtNoTransport_farDelta_value hs hfit hroom ht V w]
  norm_num

/-- Mutation B at `ell = 2`: only the staircase link `V(c,μ)` survives. -/
theorem stepBondAvgAtGammaOnly_farDelta_value_two {s : ℕ} (hs : 0 < s)
    {c : PeriodicLatticeSite L} {μ : Fin 3}
    (hfit : ∀ ν : Fin 3, (c ν).val + s * 2 ≤ L ν + 1) (hroom : s * 2 < L μ + 1)
    (ht : stepPathSite s c μ 2 ∈ CoarseLattice L s)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (w : SuTwo) :
    stepBondAvgAtGammaOnly s V 2 (coarseDelta s (⟨stepPathSite s c μ 2, ht⟩, μ) w) c μ
      = (1 / 16 : ℝ) • RMap (V (c, μ)) w := by
  rw [stepBondAvgAtGammaOnly_farDelta_value hs hfit hroom ht V w, Finset.sum_range_succ,
    Finset.sum_range_one, if_neg (by norm_num), if_pos (le_refl 1), zero_add,
    show (2 : ℕ) - 1 = 1 from rfl, coarsePathHolonomy_replicate_one]
  norm_num

/-- The scalar separation used by every must-fire below. -/
theorem smul_neg_witness_ne {r : ℝ} (hr : r ≠ 0) : r • (-suTwoWitness) ≠ r • suTwoWitness := by
  intro hcon
  have h2 := smul_right_injective SuTwo hr hcon
  have hsum : (2 : ℝ) • suTwoWitness = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h2]
    exact neg_add_cancel _
  rcases smul_eq_zero.mp hsum with h | h
  · norm_num at h
  · exact suTwoWitness_ne_zero h

theorem smul_neg_witness_ne_zero {r : ℝ} (hr : r ≠ 0) : r • (-suTwoWitness) ≠ 0 := by
  intro hcon
  rcases smul_eq_zero.mp hcon with h | h
  · exact hr h
  · exact suTwoWitness_ne_zero (neg_eq_zero.mp h)

end StraightLegTwo

/-! ### the numeric witness at `s = 2` on the `8³` torus -/

section StraightLegWitness

/-- `c + 2·e_2` on the `8³` torus: the base of the surviving summand's straight leg. -/
abbrev qsLegSite : PeriodicLatticeSite qsWitL := stepPathSite 2 qsOrigin 2 1

/-- `c + 4·e_2`: the far endpoint, where the probe field sits. -/
abbrev qsFarSite : PeriodicLatticeSite qsWitL := stepPathSite 2 qsOrigin 2 2

theorem qsWitL_dvd_two : ∀ ν : Fin 3, (2 : ℕ) ∣ (qsWitL ν + 1) := by decide

theorem qsOrigin_mem_two : qsOrigin ∈ CoarseLattice qsWitL 2 :=
  mem_CoarseLattice.mpr (by decide)

theorem qsFarSite_mem : qsFarSite ∈ CoarseLattice qsWitL 2 :=
  stepPathSite_mem_coarseLattice qsWitL_dvd_two qsOrigin_mem_two 2 2

theorem qsFit : ∀ ν : Fin 3, (qsOrigin ν).val + 2 * 2 ≤ qsWitL ν + 1 := by decide

theorem qsRoom : (2 : ℕ) * 2 < qsWitL 2 + 1 := by decide

theorem qsOrigin_ne_leg : qsOrigin ≠ qsLegSite := by decide

theorem qsOrigin_ne_far : qsOrigin ≠ qsFarSite := by decide

theorem qsLeg_ne_far : qsLegSite ≠ qsFarSite := by decide

/-- **THE STRAIGHT-LEG BACKGROUND**: `M` on the single coarse link `(c + 2·e_2, 2)` — the link the
straight leg of the surviving summand traverses, and NO other. -/
noncomputable def qsLegU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsWitL :=
  fun e => if e = (qsLegSite, (2 : Fin 3)) then witnessMElem else 1

/-- **ONE STRIDED STEP FURTHER**: `M` on `(c + 4·e_2, 2)`, one strided position BEYOND the end of
the leg. -/
noncomputable def qsFarU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsWitL :=
  fun e => if e = (qsFarSite, (2 : Fin 3)) then witnessMElem else 1

/-- **SAME SITE, WRONG DIRECTION**: `M` on `(c + 2·e_2, 0)`. -/
noncomputable def qsCrossU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsWitL :=
  fun e => if e = (qsLegSite, (0 : Fin 3)) then witnessMElem else 1

/-- The probe field: `suTwoWitness` on the single coarse bond `(c + 4·e_2, 2)`. -/
noncomputable def qsProbe : CoarseBond qsWitL 2 → SuTwo :=
  coarseDelta 2 (⟨qsFarSite, qsFarSite_mem⟩, (2 : Fin 3)) suTwoWitness

theorem qsLegU_at_origin : qsLegU (qsOrigin, (2 : Fin 3)) = 1 := by
  unfold qsLegU
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  exact fun h => absurd h qsOrigin_ne_leg

theorem qsLegU_at_leg : qsLegU (qsLegSite, (2 : Fin 3)) = witnessMElem := by
  unfold qsLegU; rw [if_pos rfl]

theorem qsFarU_at_origin : qsFarU (qsOrigin, (2 : Fin 3)) = 1 := by
  unfold qsFarU
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  exact fun h => absurd h qsOrigin_ne_far

theorem qsFarU_at_leg : qsFarU (qsLegSite, (2 : Fin 3)) = 1 := by
  unfold qsFarU
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  exact fun h => absurd h qsLeg_ne_far

theorem qsCrossU_at_origin : qsCrossU (qsOrigin, (2 : Fin 3)) = 1 := by
  unfold qsCrossU
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  intro _ h
  exact absurd h (by decide)

theorem qsCrossU_at_leg : qsCrossU (qsLegSite, (2 : Fin 3)) = 1 := by
  unfold qsCrossU
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  intro _ h
  exact absurd h (by decide)

/-! #### the six values -/

theorem qsValue_legU :
    stepBondAvgAt 2 qsLegU 2 qsProbe qsOrigin 2 = (1 / 16 : ℝ) • (-suTwoWitness) := by
  unfold qsProbe
  rw [stepBondAvgAt_farDelta_value_two (by norm_num) qsFit qsRoom qsFarSite_mem qsLegU
    suTwoWitness]
  show (1 / 16 : ℝ) • RMap (qsLegU (qsOrigin, 2) * qsLegU (qsLegSite, 2)) suTwoWitness = _
  rw [qsLegU_at_origin, qsLegU_at_leg, one_mul, RMap_witnessMElem]

theorem qsValue_farU :
    stepBondAvgAt 2 qsFarU 2 qsProbe qsOrigin 2 = (1 / 16 : ℝ) • suTwoWitness := by
  unfold qsProbe
  rw [stepBondAvgAt_farDelta_value_two (by norm_num) qsFit qsRoom qsFarSite_mem qsFarU
    suTwoWitness]
  show (1 / 16 : ℝ) • RMap (qsFarU (qsOrigin, 2) * qsFarU (qsLegSite, 2)) suTwoWitness = _
  rw [qsFarU_at_origin, qsFarU_at_leg, one_mul, RMap_one, LinearMap.id_apply]

theorem qsValue_crossU :
    stepBondAvgAt 2 qsCrossU 2 qsProbe qsOrigin 2 = (1 / 16 : ℝ) • suTwoWitness := by
  unfold qsProbe
  rw [stepBondAvgAt_farDelta_value_two (by norm_num) qsFit qsRoom qsFarSite_mem qsCrossU
    suTwoWitness]
  show (1 / 16 : ℝ) • RMap (qsCrossU (qsOrigin, 2) * qsCrossU (qsLegSite, 2)) suTwoWitness = _
  rw [qsCrossU_at_origin, qsCrossU_at_leg, one_mul, RMap_one, LinearMap.id_apply]

theorem qsValue_trivialU :
    stepBondAvgAt 2 (trivialU qsWitL) 2 qsProbe qsOrigin 2 = (1 / 16 : ℝ) • suTwoWitness := by
  unfold qsProbe
  rw [stepBondAvgAt_farDelta_value_two (by norm_num) qsFit qsRoom qsFarSite_mem (trivialU qsWitL)
    suTwoWitness]
  show (1 / 16 : ℝ) • RMap ((trivialU qsWitL) (qsOrigin, 2)
    * (trivialU qsWitL) (qsLegSite, 2)) suTwoWitness = _
  rw [show (trivialU qsWitL) (qsOrigin, (2 : Fin 3)) = 1 from rfl,
    show (trivialU qsWitL) (qsLegSite, (2 : Fin 3)) = 1 from rfl, one_mul, RMap_one,
    LinearMap.id_apply]

theorem qsValue_noTransport :
    stepBondAvgAtNoTransport 2 qsLegU 2 qsProbe qsOrigin 2 = (1 / 16 : ℝ) • suTwoWitness := by
  unfold qsProbe
  exact stepBondAvgAtNoTransport_farDelta_value_two (by norm_num) qsFit qsRoom qsFarSite_mem
    qsLegU suTwoWitness

theorem qsValue_gammaOnly :
    stepBondAvgAtGammaOnly 2 qsLegU 2 qsProbe qsOrigin 2 = (1 / 16 : ℝ) • suTwoWitness := by
  unfold qsProbe
  rw [stepBondAvgAtGammaOnly_farDelta_value_two (by norm_num) qsFit qsRoom qsFarSite_mem qsLegU
    suTwoWitness]
  show (1 / 16 : ℝ) • RMap (qsLegU (qsOrigin, 2)) suTwoWitness = _
  rw [qsLegU_at_origin, RMap_one, LinearMap.id_apply]

/-! #### the must-fires -/

/-- The operator is not identically zero on the probe, so none of the separations below is a
statement about the zero object. -/
theorem qsValue_legU_ne_zero : stepBondAvgAt 2 qsLegU 2 qsProbe qsOrigin 2 ≠ 0 := by
  rw [qsValue_legU]
  exact smul_neg_witness_ne_zero (by norm_num)

/-- **THE CONVICTED GAP, CLOSED.** At stride `s = 2` the operator's value CHANGES when the
background changes on a single link that only the STRAIGHT LEG traverses. Every earlier `s > 1`
control in this module was proved at `trivialU`, where `coarsePathHolonomy_trivialU` discards the
path for ANY path; this one is not. -/
theorem stepBondAvgAt_straightLeg_mustfire_s2 :
    stepBondAvgAt 2 qsLegU 2 qsProbe qsOrigin 2
      ≠ stepBondAvgAt 2 (trivialU qsWitL) 2 qsProbe qsOrigin 2 := by
  rw [qsValue_legU, qsValue_trivialU]
  exact smul_neg_witness_ne (by norm_num)

/-- **MUTATION A DIES**: replacing the transport argument by `[]` changes the value. -/
theorem stepBondAvgAt_ne_noTransport_s2 :
    stepBondAvgAt 2 qsLegU 2 qsProbe qsOrigin 2
      ≠ stepBondAvgAtNoTransport 2 qsLegU 2 qsProbe qsOrigin 2 := by
  rw [qsValue_legU, qsValue_noTransport]
  exact smul_neg_witness_ne (by norm_num)

/-- **MUTATION B DIES**: deleting the STRAIGHT LEG and keeping the staircase changes the value. -/
theorem stepBondAvgAt_ne_gammaOnly_s2 :
    stepBondAvgAt 2 qsLegU 2 qsProbe qsOrigin 2
      ≠ stepBondAvgAtGammaOnly 2 qsLegU 2 qsProbe qsOrigin 2 := by
  rw [qsValue_legU, qsValue_gammaOnly]
  exact smul_neg_witness_ne (by norm_num)

/-- **POSITION SENSITIVITY**: moving the marked link ONE strided step along the same axis changes
the value — so the leg has exactly the certified length. -/
theorem stepBondAvgAt_leg_position_sensitive_s2 :
    stepBondAvgAt 2 qsLegU 2 qsProbe qsOrigin 2 ≠ stepBondAvgAt 2 qsFarU 2 qsProbe qsOrigin 2 := by
  rw [qsValue_legU, qsValue_farU]
  exact smul_neg_witness_ne (by norm_num)

/-- **DIRECTION SENSITIVITY**: the same site, direction `0` instead of `2`, is invisible. -/
theorem stepBondAvgAt_leg_direction_sensitive_s2 :
    stepBondAvgAt 2 qsLegU 2 qsProbe qsOrigin 2
      ≠ stepBondAvgAt 2 qsCrossU 2 qsProbe qsOrigin 2 := by
  rw [qsValue_legU, qsValue_crossU]
  exact smul_neg_witness_ne (by norm_num)

end StraightLegWitness

/-! ### the numeric witness at `s = 4` on the `16³` torus

`s = 2` alone could be dismissed as the smallest non-trivial stride. This repeats the separation at
stride `4`, where the block spacing (`4`) and the coarse bond length (`8`) both exceed every
constant appearing in the `8³` witness. -/

section StraightLegWitnessFour

/-- The `16³` torus. -/
def qsBigL : PeriodicLatticeExtent := fun _ => 15

def qsBigOrigin : PeriodicLatticeSite qsBigL := fun _ => 0

abbrev qsBigLeg : PeriodicLatticeSite qsBigL := stepPathSite 4 qsBigOrigin 2 1

abbrev qsBigFar : PeriodicLatticeSite qsBigL := stepPathSite 4 qsBigOrigin 2 2

theorem qsBigL_dvd_four : ∀ ν : Fin 3, (4 : ℕ) ∣ (qsBigL ν + 1) := by decide

theorem qsBigOrigin_mem : qsBigOrigin ∈ CoarseLattice qsBigL 4 :=
  mem_CoarseLattice.mpr (by decide)

theorem qsBigFar_mem : qsBigFar ∈ CoarseLattice qsBigL 4 :=
  stepPathSite_mem_coarseLattice qsBigL_dvd_four qsBigOrigin_mem 2 2

theorem qsBigFit : ∀ ν : Fin 3, (qsBigOrigin ν).val + 4 * 2 ≤ qsBigL ν + 1 := by decide

theorem qsBigRoom : (4 : ℕ) * 2 < qsBigL 2 + 1 := by decide

theorem qsBigOrigin_ne_leg : qsBigOrigin ≠ qsBigLeg := by decide

noncomputable def qsBigLegU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsBigL :=
  fun e => if e = (qsBigLeg, (2 : Fin 3)) then witnessMElem else 1

noncomputable def qsBigProbe : CoarseBond qsBigL 4 → SuTwo :=
  coarseDelta 4 (⟨qsBigFar, qsBigFar_mem⟩, (2 : Fin 3)) suTwoWitness

theorem qsBigLegU_at_origin : qsBigLegU (qsBigOrigin, (2 : Fin 3)) = 1 := by
  unfold qsBigLegU
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  exact fun h => absurd h qsBigOrigin_ne_leg

theorem qsBigLegU_at_leg : qsBigLegU (qsBigLeg, (2 : Fin 3)) = witnessMElem := by
  unfold qsBigLegU; rw [if_pos rfl]

theorem qsBigValue_legU :
    stepBondAvgAt 4 qsBigLegU 2 qsBigProbe qsBigOrigin 2 = (1 / 16 : ℝ) • (-suTwoWitness) := by
  unfold qsBigProbe
  rw [stepBondAvgAt_farDelta_value_two (by norm_num) qsBigFit qsBigRoom qsBigFar_mem qsBigLegU
    suTwoWitness]
  show (1 / 16 : ℝ) • RMap (qsBigLegU (qsBigOrigin, 2) * qsBigLegU (qsBigLeg, 2)) suTwoWitness = _
  rw [qsBigLegU_at_origin, qsBigLegU_at_leg, one_mul, RMap_witnessMElem]

theorem qsBigValue_trivialU :
    stepBondAvgAt 4 (trivialU qsBigL) 2 qsBigProbe qsBigOrigin 2
      = (1 / 16 : ℝ) • suTwoWitness := by
  unfold qsBigProbe
  rw [stepBondAvgAt_farDelta_value_two (by norm_num) qsBigFit qsBigRoom qsBigFar_mem
    (trivialU qsBigL) suTwoWitness]
  show (1 / 16 : ℝ) • RMap ((trivialU qsBigL) (qsBigOrigin, 2)
    * (trivialU qsBigL) (qsBigLeg, 2)) suTwoWitness = _
  rw [show (trivialU qsBigL) (qsBigOrigin, (2 : Fin 3)) = 1 from rfl,
    show (trivialU qsBigL) (qsBigLeg, (2 : Fin 3)) = 1 from rfl, one_mul, RMap_one,
    LinearMap.id_apply]

theorem qsBigValue_noTransport :
    stepBondAvgAtNoTransport 4 qsBigLegU 2 qsBigProbe qsBigOrigin 2
      = (1 / 16 : ℝ) • suTwoWitness := by
  unfold qsBigProbe
  exact stepBondAvgAtNoTransport_farDelta_value_two (by norm_num) qsBigFit qsBigRoom qsBigFar_mem
    qsBigLegU suTwoWitness

theorem qsBigValue_gammaOnly :
    stepBondAvgAtGammaOnly 4 qsBigLegU 2 qsBigProbe qsBigOrigin 2
      = (1 / 16 : ℝ) • suTwoWitness := by
  unfold qsBigProbe
  rw [stepBondAvgAtGammaOnly_farDelta_value_two (by norm_num) qsBigFit qsBigRoom qsBigFar_mem
    qsBigLegU suTwoWitness]
  show (1 / 16 : ℝ) • RMap (qsBigLegU (qsBigOrigin, 2)) suTwoWitness = _
  rw [qsBigLegU_at_origin, RMap_one, LinearMap.id_apply]

/-- **THE SEPARATION AT STRIDE `4`.** -/
theorem stepBondAvgAt_straightLeg_mustfire_s4 :
    stepBondAvgAt 4 qsBigLegU 2 qsBigProbe qsBigOrigin 2
      ≠ stepBondAvgAt 4 (trivialU qsBigL) 2 qsBigProbe qsBigOrigin 2 := by
  rw [qsBigValue_legU, qsBigValue_trivialU]
  exact smul_neg_witness_ne (by norm_num)

/-- Mutation A dies at stride `4` too. -/
theorem stepBondAvgAt_ne_noTransport_s4 :
    stepBondAvgAt 4 qsBigLegU 2 qsBigProbe qsBigOrigin 2
      ≠ stepBondAvgAtNoTransport 4 qsBigLegU 2 qsBigProbe qsBigOrigin 2 := by
  rw [qsBigValue_legU, qsBigValue_noTransport]
  exact smul_neg_witness_ne (by norm_num)

/-- Mutation B dies at stride `4` too. -/
theorem stepBondAvgAt_ne_gammaOnly_s4 :
    stepBondAvgAt 4 qsBigLegU 2 qsBigProbe qsBigOrigin 2
      ≠ stepBondAvgAtGammaOnly 4 qsBigLegU 2 qsBigProbe qsBigOrigin 2 := by
  rw [qsBigValue_legU, qsBigValue_gammaOnly]
  exact smul_neg_witness_ne (by norm_num)

end StraightLegWitnessFour


/-! ### `ell = 4`: the leg has FOUR links and the operator resolves WHICH one is marked

The `ell = 2` witnesses separate the leg's single link from the link one strided step beyond it.
At `ell = 4` the strided line carries four coarse links and the marked one is placed at INTERIOR
position `2` — neither the staircase link `(c,μ)` nor the last link.

~~A transport that read the wrong number of links, or read them from the wrong base, would miss
it.~~ **SUPERSEDED — the first clause is FALSE and is retained struck.** A transport reading
`ell − 1` links instead of `ell` — dropping exactly the TERMINAL link — reproduces this witness's
value on the nose (`qsBig4Value_dropTerminal`, `dropTerminal_cannot_separate_interior_ell4` below),
because position `2` is not position `3`. Only the WRONG-BASE half of the struck sentence survives
unqualified. The terminal-link escape is killed in `section StraightLegWitnessTerminal` on a
witness marking position `3`. -/

section StraightLegWitnessEllFour

open AdalyFormal.Balaban.CovariantOperators (witnessMElem RMap_witnessMElem)
open AdalyFormal.Balaban.QjComposite (coarsePathHolonomy_nil coarsePathHolonomy_cons)

/-- One strided step composes: `coarseShift` of the `k`-th line site is the `(k+1)`-st. -/
theorem coarseShift_stepPathSite {L : PeriodicLatticeExtent} (s : ℕ) (c : PeriodicLatticeSite L)
    (μ : Fin 3) (k : ℕ) :
    coarseShift (stepPathSite s c μ k) s μ = stepPathSite s c μ (k + 1) := by
  show pathSite (pathSite c μ (s * k)) μ s = pathSite c μ (s * (k + 1))
  rw [pathSite_add]
  congr 1
  ring

/-- The four-link strided line's holonomy, in the order the contour traverses it. -/
theorem coarsePathHolonomy_replicate_four {L : PeriodicLatticeExtent} (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : PeriodicLatticeSite L) (μ : Fin 3) :
    coarsePathHolonomy s V c (List.replicate 4 μ)
      = V (c, μ) * (V (stepPathSite s c μ 1, μ)
          * (V (stepPathSite s c μ 2, μ) * V (stepPathSite s c μ 3, μ))) := by
  have h1 := coarseShift_stepPathSite s c μ 0
  rw [stepPathSite_zero] at h1
  have h2 := coarseShift_stepPathSite s c μ 1
  have h3 := coarseShift_stepPathSite s c μ 2
  show coarsePathHolonomy s V c [μ, μ, μ, μ] = _
  rw [coarsePathHolonomy_cons, coarsePathHolonomy_cons, coarsePathHolonomy_cons,
    coarsePathHolonomy_cons, coarsePathHolonomy_nil, mul_one, h1, h2, h3]

abbrev qsBig4P1 : PeriodicLatticeSite qsBigL := stepPathSite 2 qsBigOrigin 2 1
abbrev qsBig4P2 : PeriodicLatticeSite qsBigL := stepPathSite 2 qsBigOrigin 2 2
abbrev qsBig4P3 : PeriodicLatticeSite qsBigL := stepPathSite 2 qsBigOrigin 2 3
abbrev qsBig4Far : PeriodicLatticeSite qsBigL := stepPathSite 2 qsBigOrigin 2 4

theorem qsBigL_dvd_two : ∀ ν : Fin 3, (2 : ℕ) ∣ (qsBigL ν + 1) := by decide

theorem qsBigOrigin_mem_two : qsBigOrigin ∈ CoarseLattice qsBigL 2 :=
  mem_CoarseLattice.mpr (by decide)

theorem qsBig4Far_mem : qsBig4Far ∈ CoarseLattice qsBigL 2 :=
  stepPathSite_mem_coarseLattice qsBigL_dvd_two qsBigOrigin_mem_two 2 4

theorem qsBig4Fit : ∀ ν : Fin 3, (qsBigOrigin ν).val + 2 * 4 ≤ qsBigL ν + 1 := by decide

theorem qsBig4Room : (2 : ℕ) * 4 < qsBigL 2 + 1 := by decide

theorem qsBigOrigin_ne_p2 : qsBigOrigin ≠ qsBig4P2 := by decide

theorem qsBig4P1_ne_p2 : qsBig4P1 ≠ qsBig4P2 := by decide

theorem qsBig4P3_ne_p2 : qsBig4P3 ≠ qsBig4P2 := by decide

/-- `M` on the THIRD link of the four-link strided line (interior position `2`). -/
noncomputable def qsBig4U :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsBigL :=
  fun e => if e = (qsBig4P2, (2 : Fin 3)) then witnessMElem else 1

noncomputable def qsBig4Probe : CoarseBond qsBigL 2 → SuTwo :=
  coarseDelta 2 (⟨qsBig4Far, qsBig4Far_mem⟩, (2 : Fin 3)) suTwoWitness

theorem qsBig4U_at_origin : qsBig4U (qsBigOrigin, (2 : Fin 3)) = 1 := by
  unfold qsBig4U
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  exact fun h => absurd h qsBigOrigin_ne_p2

theorem qsBig4U_at_p1 : qsBig4U (qsBig4P1, (2 : Fin 3)) = 1 := by
  unfold qsBig4U
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  exact fun h => absurd h qsBig4P1_ne_p2

theorem qsBig4U_at_p2 : qsBig4U (qsBig4P2, (2 : Fin 3)) = witnessMElem := by
  unfold qsBig4U; rw [if_pos rfl]

theorem qsBig4U_at_p3 : qsBig4U (qsBig4P3, (2 : Fin 3)) = 1 := by
  unfold qsBig4U
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  exact fun h => absurd h qsBig4P3_ne_p2

/-- **THE INTERIOR-LINK VALUE AT `ell = 4`.** Three of the `4⁴ = 256` summands survive the probe,
each transporting along all four links, and the marked interior link flips the sign. -/
theorem qsBig4Value_legU :
    stepBondAvgAt 2 qsBig4U 4 qsBig4Probe qsBigOrigin 2
      = ((3 : ℝ) / 256) • (-suTwoWitness) := by
  unfold qsBig4Probe
  rw [stepBondAvgAt_farDelta_value (by norm_num) qsBig4Fit qsBig4Room qsBig4Far_mem qsBig4U
    suTwoWitness, coarsePathHolonomy_replicate_four, qsBig4U_at_origin, qsBig4U_at_p1,
    qsBig4U_at_p2, qsBig4U_at_p3, mul_one, one_mul, one_mul, RMap_witnessMElem]
  norm_num

theorem qsBig4Value_trivialU :
    stepBondAvgAt 2 (trivialU qsBigL) 4 qsBig4Probe qsBigOrigin 2
      = ((3 : ℝ) / 256) • suTwoWitness := by
  unfold qsBig4Probe
  rw [stepBondAvgAt_farDelta_value (by norm_num) qsBig4Fit qsBig4Room qsBig4Far_mem
    (trivialU qsBigL) suTwoWitness, coarsePathHolonomy_replicate_four,
    show (trivialU qsBigL) (qsBigOrigin, (2 : Fin 3)) = 1 from rfl,
    show (trivialU qsBigL) (qsBig4P1, (2 : Fin 3)) = 1 from rfl,
    show (trivialU qsBigL) (qsBig4P2, (2 : Fin 3)) = 1 from rfl,
    show (trivialU qsBigL) (qsBig4P3, (2 : Fin 3)) = 1 from rfl, mul_one, one_mul, one_mul,
    RMap_one, LinearMap.id_apply]
  norm_num

theorem qsBig4Value_noTransport :
    stepBondAvgAtNoTransport 2 qsBig4U 4 qsBig4Probe qsBigOrigin 2
      = ((3 : ℝ) / 256) • suTwoWitness := by
  unfold qsBig4Probe
  rw [stepBondAvgAtNoTransport_farDelta_value (by norm_num) qsBig4Fit qsBig4Room qsBig4Far_mem
    qsBig4U suTwoWitness]
  norm_num

/-- **THE SEPARATION AT `ell = 4`, MARKED LINK INTERIOR.** -/
theorem stepBondAvgAt_straightLeg_mustfire_ell4 :
    stepBondAvgAt 2 qsBig4U 4 qsBig4Probe qsBigOrigin 2
      ≠ stepBondAvgAt 2 (trivialU qsBigL) 4 qsBig4Probe qsBigOrigin 2 := by
  rw [qsBig4Value_legU, qsBig4Value_trivialU]
  exact smul_neg_witness_ne (by norm_num)

/-- Mutation A dies at `ell = 4` too. -/
theorem stepBondAvgAt_ne_noTransport_ell4 :
    stepBondAvgAt 2 qsBig4U 4 qsBig4Probe qsBigOrigin 2
      ≠ stepBondAvgAtNoTransport 2 qsBig4U 4 qsBig4Probe qsBigOrigin 2 := by
  rw [qsBig4Value_legU, qsBig4Value_noTransport]
  exact smul_neg_witness_ne (by norm_num)

end StraightLegWitnessEllFour


/-! ### THE TERMINAL-LINK CONTROL — mutation D, and the witness that kills it

The `ell = 4` witness above marks INTERIOR position `2` of the four-link strided line. That leaves
a transport bug invisible to every control built so far: **read `i − 1` straight-leg links instead
of `i`**. For every surviving summand the staircase contributes `ell − i` links regardless of `i`,
so this mutation reads `(ell − i) + (i − 1) = ell − 1` links — always the SAME first `ell − 1`
links, always dropping exactly the terminal one, for every `i`. Marking position `2` of `0,1,2,3`
therefore cannot see it.

This block supplies the missing control:

* `stepBondAvgAtDropTerminal` — **mutation D**, in file, at general `s`, `ell`;
* `stepBondAvgAtDropTerminal_farDelta_value` — its closed form: `((ell−1)/ell⁴)·R(holonomy of the
  first `ell−1` links)`, to be compared with `stepBondAvgAt_farDelta_value`'s `ell` links;
* `qsBig4TermU` — the new witness, `M` on the **TERMINAL** link `(c + 3·s·e_μ, μ)` of the same
  `ell = 4` strided line on the `16³` torus at `s = 2`;
* `stepBondAvgAt_ne_dropTerminal_ell4_terminal` — **the kill**;
* `dropTerminal_cannot_separate_interior_ell4` — **the diagnosis**: on the OLD `ell = 4` witness
  the two operators are EQUAL, so the escape was real and is not being papered over; and
  `dropTerminal_survives_interior_mustfire` shows mutation D even passes the old must-fire.
* `stepBondAvgAtDropTerminal_eq_gammaOnly_two` — at `ell = 2` mutation D collapses onto mutation B,
  so the two `ell = 2` witnesses did already exclude it; the escape is specific to `ell ≥ 3` with
  the marked link away from the terminal position. `stepBondAvgAt_ne_dropTerminal_s2` /
  `_s4` record that consequence.
-/

section StraightLegWitnessTerminal

open AdalyFormal.Balaban.CovariantOperators (witnessMElem RMap_witnessMElem)
open AdalyFormal.Balaban.QjComposite (coarsePathHolonomy_nil coarsePathHolonomy_cons)

/-- **MUTATION D**: the straight leg is under-read by exactly one link (`i − 1` replicated links
instead of `i`), so the transported contour ALWAYS drops the TERMINAL link of the strided line, for
every surviving summand. Distinct from mutation A (`[]`) and from mutation B (staircase only): at
`ell ≥ 3` it still traverses a genuine, nonempty straight leg. -/
noncomputable def stepBondAvgAtDropTerminal (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (1 / (ell : ℝ) ^ 4) • ∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
    RMap (coarsePathHolonomy s V c (coarseGammaPath s c x ++ List.replicate (i - 1) μ))
      (coarseValAt s A (stepPathSite s x μ i) μ)

/-- **MUTATION D's VALUE**, general `s`, general `ell`: the holonomy of the first `ell − 1` links
of the strided line — the same prefactor `(ell−1)/ell⁴` as the real operator, one link short. -/
theorem stepBondAvgAtDropTerminal_farDelta_value {s ell : ℕ} (hs : 0 < s)
    {c : PeriodicLatticeSite L} {μ : Fin 3}
    (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) (hroom : s * ell < L μ + 1)
    (ht : stepPathSite s c μ ell ∈ CoarseLattice L s)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (w : SuTwo) :
    stepBondAvgAtDropTerminal s V ell (coarseDelta s (⟨stepPathSite s c μ ell, ht⟩, μ) w) c μ
      = (((ell - 1 : ℕ) : ℝ) / (ell : ℝ) ^ 4)
          • RMap (coarsePathHolonomy s V c (List.replicate (ell - 1) μ)) w := by
  have hhol : ∀ i, 1 ≤ i → i < ell →
      coarsePathHolonomy s V c
        (coarseGammaPath s c (stepPathSite s c μ (ell - i)) ++ List.replicate (i - 1) μ)
        = coarsePathHolonomy s V c (List.replicate (ell - 1) μ) := by
    intro i h1 h2
    have hb := mul_lt_of_lt_stride hs (show ell - i < ell by omega)
    have hfitμ := hfit μ
    have hg := coarseGammaPath_replicate_stride hs c μ (ell - i) (by omega)
    rw [hg, ← List.replicate_add, show ell - i + (i - 1) = ell - 1 by omega]
  unfold stepBondAvgAtDropTerminal
  rw [farDelta_weighted_sum hs hfit hroom ht w
    (fun x i => coarsePathHolonomy s V c (coarseGammaPath s c x ++ List.replicate (i - 1) μ))]
  have hcong : ∀ i ∈ Finset.range ell,
      (if 1 ≤ i then
        RMap (coarsePathHolonomy s V c
          (coarseGammaPath s c (stepPathSite s c μ (ell - i)) ++ List.replicate (i - 1) μ)) w
        else 0)
        = if 1 ≤ i then RMap (coarsePathHolonomy s V c (List.replicate (ell - 1) μ)) w else 0 := by
    intro i hi
    by_cases h1 : 1 ≤ i
    · rw [if_pos h1, if_pos h1, hhol i h1 (Finset.mem_range.mp hi)]
    · rw [if_neg h1, if_neg h1]
  rw [Finset.sum_congr rfl hcong, sum_range_ite_one_le,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  field_simp

/-- **AT `ell = 2` MUTATION D IS MUTATION B.** Both surviving indices `i ∈ {0,1}` give `i − 1 = 0`
in `ℕ`, so the appended leg is empty and the contour is the bare staircase. Hence the `ell = 2`
witnesses of this section DO already exclude mutation D — the escape it represents is specific to
`ell ≥ 3`. -/
theorem stepBondAvgAtDropTerminal_eq_gammaOnly_two (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) :
    stepBondAvgAtDropTerminal s V 2 A c μ = stepBondAvgAtGammaOnly s V 2 A c μ := by
  have hsum : ∀ x ∈ stepBlockOf c s 2,
      (∑ i ∈ Finset.range 2, RMap (coarsePathHolonomy s V c
          (coarseGammaPath s c x ++ List.replicate (i - 1) μ))
          (coarseValAt s A (stepPathSite s x μ i) μ))
        = ∑ i ∈ Finset.range 2, RMap (coarsePathHolonomy s V c (coarseGammaPath s c x))
            (coarseValAt s A (stepPathSite s x μ i) μ) := by
    intro x _
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have h0 : i - 1 = 0 := by
      have := Finset.mem_range.mp hi
      omega
    rw [h0, List.replicate_zero, List.append_nil]
  unfold stepBondAvgAtDropTerminal stepBondAvgAtGammaOnly
  rw [Finset.sum_congr rfl hsum]

/-- The three-link strided line's holonomy, in the order the contour traverses it. Needed because
mutation D reads exactly the first three of the `ell = 4` line's four links. -/
theorem coarsePathHolonomy_replicate_three (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : PeriodicLatticeSite L) (μ : Fin 3) :
    coarsePathHolonomy s V c (List.replicate 3 μ)
      = V (c, μ) * (V (stepPathSite s c μ 1, μ) * V (stepPathSite s c μ 2, μ)) := by
  have h1 := coarseShift_stepPathSite s c μ 0
  rw [stepPathSite_zero] at h1
  have h2 := coarseShift_stepPathSite s c μ 1
  show coarsePathHolonomy s V c [μ, μ, μ] = _
  rw [coarsePathHolonomy_cons, coarsePathHolonomy_cons, coarsePathHolonomy_cons,
    coarsePathHolonomy_nil, mul_one, h1, h2]

/-! #### the new witness: `M` on the TERMINAL link of the four-link line -/

theorem qsBigOrigin_ne_p3 : qsBigOrigin ≠ qsBig4P3 := by decide

theorem qsBig4P1_ne_p3 : qsBig4P1 ≠ qsBig4P3 := by decide

theorem qsBig4P2_ne_p3 : qsBig4P2 ≠ qsBig4P3 := by decide

/-- **THE TERMINAL-LINK BACKGROUND.** `M` on the FOURTH (last) link of the four-link strided line,
`(c + 3·s·e_μ, μ)` with `s = 2` — position `3` of `0,1,2,3`. This is the analogue of `qsBig4U`
(interior position `2`) with the mark moved to the leg's last position, and it is the only witness
in this module that a terminal-link-dropping transport can be seen by. -/
noncomputable def qsBig4TermU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsBigL :=
  fun e => if e = (qsBig4P3, (2 : Fin 3)) then witnessMElem else 1

theorem qsBig4TermU_at_origin : qsBig4TermU (qsBigOrigin, (2 : Fin 3)) = 1 := by
  unfold qsBig4TermU
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  exact fun h => absurd h qsBigOrigin_ne_p3

theorem qsBig4TermU_at_p1 : qsBig4TermU (qsBig4P1, (2 : Fin 3)) = 1 := by
  unfold qsBig4TermU
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  exact fun h => absurd h qsBig4P1_ne_p3

theorem qsBig4TermU_at_p2 : qsBig4TermU (qsBig4P2, (2 : Fin 3)) = 1 := by
  unfold qsBig4TermU
  rw [if_neg]
  simp only [Prod.mk.injEq, not_and]
  exact fun h => absurd h qsBig4P2_ne_p3

theorem qsBig4TermU_at_p3 : qsBig4TermU (qsBig4P3, (2 : Fin 3)) = witnessMElem := by
  unfold qsBig4TermU; rw [if_pos rfl]

/-! #### the values at the terminal witness -/

/-- **THE REAL OPERATOR SEES THE TERMINAL LINK**: all four links are traversed, the last one is
`M`, and the sign flips. -/
theorem qsBig4TermValue_legU :
    stepBondAvgAt 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2
      = ((3 : ℝ) / 256) • (-suTwoWitness) := by
  unfold qsBig4Probe
  rw [stepBondAvgAt_farDelta_value (by norm_num) qsBig4Fit qsBig4Room qsBig4Far_mem qsBig4TermU
    suTwoWitness, coarsePathHolonomy_replicate_four, qsBig4TermU_at_origin, qsBig4TermU_at_p1,
    qsBig4TermU_at_p2, qsBig4TermU_at_p3, one_mul, one_mul, one_mul, RMap_witnessMElem]
  norm_num

/-- **MUTATION D DOES NOT**: it reads only the first three links, all of them `1` here. -/
theorem qsBig4TermValue_dropTerminal :
    stepBondAvgAtDropTerminal 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2
      = ((3 : ℝ) / 256) • suTwoWitness := by
  unfold qsBig4Probe
  rw [stepBondAvgAtDropTerminal_farDelta_value (by norm_num) qsBig4Fit qsBig4Room qsBig4Far_mem
    qsBig4TermU suTwoWitness]
  show ((((4 : ℕ) - 1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) ^ 4) • RMap (coarsePathHolonomy 2 qsBig4TermU
    qsBigOrigin (List.replicate 3 (2 : Fin 3))) suTwoWitness = _
  rw [coarsePathHolonomy_replicate_three, qsBig4TermU_at_origin, qsBig4TermU_at_p1,
    qsBig4TermU_at_p2, one_mul, one_mul, RMap_one, LinearMap.id_apply]
  norm_num

theorem qsBig4TermValue_trivialU :
    stepBondAvgAt 2 (trivialU qsBigL) 4 qsBig4Probe qsBigOrigin 2
      = ((3 : ℝ) / 256) • suTwoWitness := qsBig4Value_trivialU

theorem qsBig4TermValue_noTransport :
    stepBondAvgAtNoTransport 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2
      = ((3 : ℝ) / 256) • suTwoWitness := by
  unfold qsBig4Probe
  rw [stepBondAvgAtNoTransport_farDelta_value (by norm_num) qsBig4Fit qsBig4Room qsBig4Far_mem
    qsBig4TermU suTwoWitness]
  norm_num

theorem qsBig4TermValue_gammaOnly :
    stepBondAvgAtGammaOnly 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2
      = ((3 : ℝ) / 256) • suTwoWitness := by
  unfold qsBig4Probe
  rw [stepBondAvgAtGammaOnly_farDelta_value (by norm_num) qsBig4Fit qsBig4Room qsBig4Far_mem
    qsBig4TermU suTwoWitness]
  have h1 : coarsePathHolonomy 2 qsBig4TermU qsBigOrigin (List.replicate 1 (2 : Fin 3)) = 1 := by
    rw [coarsePathHolonomy_replicate_one, qsBig4TermU_at_origin]
  have h2 : coarsePathHolonomy 2 qsBig4TermU qsBigOrigin (List.replicate 2 (2 : Fin 3)) = 1 := by
    rw [coarsePathHolonomy_replicate_two, qsBig4TermU_at_origin, qsBig4TermU_at_p1, one_mul]
  have h3 : coarsePathHolonomy 2 qsBig4TermU qsBigOrigin (List.replicate 3 (2 : Fin 3)) = 1 := by
    rw [coarsePathHolonomy_replicate_three, qsBig4TermU_at_origin, qsBig4TermU_at_p1,
      qsBig4TermU_at_p2, one_mul, one_mul]
  have g1 : coarsePathHolonomy 2 qsBig4TermU qsBigOrigin [(2 : Fin 3)] = 1 := h1
  have g2 : coarsePathHolonomy 2 qsBig4TermU qsBigOrigin [(2 : Fin 3), 2] = 1 := h2
  have g3 : coarsePathHolonomy 2 qsBig4TermU qsBigOrigin [(2 : Fin 3), 2, 2] = 1 := h3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [h1, h2, h3, g1, g2, g3, RMap_one]
  module

/-- Mutation D at the trivial background: the flat value, since every holonomy is `1`. -/
theorem qsBig4TrivialValue_dropTerminal :
    stepBondAvgAtDropTerminal 2 (trivialU qsBigL) 4 qsBig4Probe qsBigOrigin 2
      = ((3 : ℝ) / 256) • suTwoWitness := by
  unfold qsBig4Probe
  rw [stepBondAvgAtDropTerminal_farDelta_value (by norm_num) qsBig4Fit qsBig4Room qsBig4Far_mem
    (trivialU qsBigL) suTwoWitness, coarsePathHolonomy_trivialU, RMap_one, LinearMap.id_apply]
  norm_num

/-! #### THE KILL, and the diagnosis it repairs -/

/-- The operator is not identically zero on the terminal witness, so none of the separations below
is a statement about the zero object. -/
theorem qsBig4TermValue_legU_ne_zero :
    stepBondAvgAt 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2 ≠ 0 := by
  rw [qsBig4TermValue_legU]
  exact smul_neg_witness_ne_zero (by norm_num)

/-- **THE TERMINAL-LINK CONTROL FIRES.** The real operator and mutation D take DIFFERENT values on
`qsBig4TermU`. This is the control the `ell = 4` interior witness could not supply. -/
theorem stepBondAvgAt_ne_dropTerminal_ell4_terminal :
    stepBondAvgAt 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2
      ≠ stepBondAvgAtDropTerminal 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2 := by
  rw [qsBig4TermValue_legU, qsBig4TermValue_dropTerminal]
  exact smul_neg_witness_ne (by norm_num)

/-- The new witness is a genuine must-fire in its own right: it separates the real operator from
the trivial background, so the kill above is not a statement about a degenerate value. -/
theorem stepBondAvgAt_straightLeg_mustfire_ell4_terminal :
    stepBondAvgAt 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2
      ≠ stepBondAvgAt 2 (trivialU qsBigL) 4 qsBig4Probe qsBigOrigin 2 := by
  rw [qsBig4TermValue_legU, qsBig4TermValue_trivialU]
  exact smul_neg_witness_ne (by norm_num)

/-- Mutation A dies on the terminal witness too. -/
theorem stepBondAvgAt_ne_noTransport_ell4_terminal :
    stepBondAvgAt 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2
      ≠ stepBondAvgAtNoTransport 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2 := by
  rw [qsBig4TermValue_legU, qsBig4TermValue_noTransport]
  exact smul_neg_witness_ne (by norm_num)

/-- Mutation B dies on the terminal witness too. -/
theorem stepBondAvgAt_ne_gammaOnly_ell4_terminal :
    stepBondAvgAt 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2
      ≠ stepBondAvgAtGammaOnly 2 qsBig4TermU 4 qsBig4Probe qsBigOrigin 2 := by
  rw [qsBig4TermValue_legU, qsBig4TermValue_gammaOnly]
  exact smul_neg_witness_ne (by norm_num)

/-- **THE DIAGNOSIS, PART 1.** Mutation D's value on the OLD `ell = 4` witness: it reads links
`0,1,2`, the marked one is `2`, so it reproduces the real operator's separating value exactly. -/
theorem qsBig4Value_dropTerminal :
    stepBondAvgAtDropTerminal 2 qsBig4U 4 qsBig4Probe qsBigOrigin 2
      = ((3 : ℝ) / 256) • (-suTwoWitness) := by
  unfold qsBig4Probe
  rw [stepBondAvgAtDropTerminal_farDelta_value (by norm_num) qsBig4Fit qsBig4Room qsBig4Far_mem
    qsBig4U suTwoWitness]
  show ((((4 : ℕ) - 1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) ^ 4) • RMap (coarsePathHolonomy 2 qsBig4U
    qsBigOrigin (List.replicate 3 (2 : Fin 3))) suTwoWitness = _
  rw [coarsePathHolonomy_replicate_three, qsBig4U_at_origin, qsBig4U_at_p1, qsBig4U_at_p2,
    one_mul, one_mul, RMap_witnessMElem]
  norm_num

/-- **THE DIAGNOSIS, PART 2 — the equality that makes the repair non-vacuous.** On the OLD
`ell = 4` witness the real operator and mutation D are EQUAL. So an `ne`-style kill of mutation D
is FALSE at `qsBig4U`: the interior-position witness provably cannot separate them, and only the
terminal-position witness above can. -/
theorem dropTerminal_cannot_separate_interior_ell4 :
    stepBondAvgAtDropTerminal 2 qsBig4U 4 qsBig4Probe qsBigOrigin 2
      = stepBondAvgAt 2 qsBig4U 4 qsBig4Probe qsBigOrigin 2 := by
  rw [qsBig4Value_dropTerminal, qsBig4Value_legU]

/-- **THE DIAGNOSIS, PART 3.** Mutation D even PASSES the old `ell = 4` must-fire — it is
background-sensitive there, so "the must-fire fires" was never evidence against it. -/
theorem dropTerminal_survives_interior_mustfire :
    stepBondAvgAtDropTerminal 2 qsBig4U 4 qsBig4Probe qsBigOrigin 2
      ≠ stepBondAvgAtDropTerminal 2 (trivialU qsBigL) 4 qsBig4Probe qsBigOrigin 2 := by
  rw [qsBig4Value_dropTerminal, qsBig4TrivialValue_dropTerminal]
  exact smul_neg_witness_ne (by norm_num)

/-! #### mutation D at `ell = 2`: already excluded, via the collapse onto mutation B -/

theorem stepBondAvgAt_ne_dropTerminal_s2 :
    stepBondAvgAt 2 qsLegU 2 qsProbe qsOrigin 2
      ≠ stepBondAvgAtDropTerminal 2 qsLegU 2 qsProbe qsOrigin 2 := by
  rw [stepBondAvgAtDropTerminal_eq_gammaOnly_two]
  exact stepBondAvgAt_ne_gammaOnly_s2

theorem stepBondAvgAt_ne_dropTerminal_s4 :
    stepBondAvgAt 4 qsBigLegU 2 qsBigProbe qsBigOrigin 2
      ≠ stepBondAvgAtDropTerminal 4 qsBigLegU 2 qsBigProbe qsBigOrigin 2 := by
  rw [stepBondAvgAtDropTerminal_eq_gammaOnly_two]
  exact stepBondAvgAt_ne_gammaOnly_s4

end StraightLegWitnessTerminal


/-! ### THE STAIRCASE-ORDER CONTROL — an OFF-AXIS probe at `s > 1`

Everything above places the probe at `c + s·ell·e_μ`, on the `μ`-axis through the block corner.
The surviving summands' sites are then `c + s·(ell−i)·e_μ`, which differ from `c` in the SINGLE
coordinate `μ`, so `coarseGammaPath s c x` is a pure `μ`-segment and the DESCENDING `2,1,0` order
in which `coarseGammaPath` concatenates its three coordinate segments never enters any value.

This block removes that restriction. The strided line is based at an arbitrary block member `y`
sharing the corner's `μ`-coordinate, so the surviving sites differ from `c` in TWO coordinates and
the concatenation order becomes observable:

* `stepPathSite_eq_far_iff_base`, `coarseValAt_farDelta_base`, `farDelta_weighted_sum_base` —
  the uniqueness lemma and the collapse, re-proved with the line base `y` decoupled from the
  block corner `c`;
* `coarseGammaPathAsc` / `stepBondAvgAtAscOrder` — **mutation E**: the same staircase with its
  segments concatenated in ASCENDING order `0,1,2`. Same endpoints, same multiset of steps,
  different contour;
* `qsOrderU` — the witness: `M` on the single coarse link `(c + s·e_2, 0)`, which the DESCENDING
  contour traverses and the ASCENDING contour does not;
* `stepBondAvgAt_ne_ascOrder_offAxis` — **the kill**, at `s = 2`, `ell = 2`, `μ = 0` on the `8³`
  torus.

**SCOPE OF THIS BLOCK — read before citing it as an order control.** Two of the three coordinate
segments are non-empty at this witness, not three: the surviving site shares coordinate `1` with the
block corner. This block therefore pins the RELATIVE order of segments `2` and `0` and nothing about
where segment `1` sits (`qsOrdX_middle_segment_empty`, `stepBondAvgAtOrd201_eq_real_at_ordX`). The
three-segment witness that pins the FULL order is `section StraightLegOffAxisFull`, immediately
below.
-/

section StraightLegOffAxis

open AdalyFormal.Balaban.CovariantOperators (witnessMElem RMap_witnessMElem)
open AdalyFormal.Balaban.QjComposite (coarsePathHolonomy_nil coarsePathHolonomy_cons)

/-- A block member's `k`-th strided `μ`-neighbour is again a block member, when the member shares
the corner's `μ`-coordinate. The off-axis analogue of `stepPathSite_mem_stepBlock_of_lt`. -/
theorem stepPathSite_mem_stepBlock_of_base {s ell : ℕ} (hs : 0 < s) {c y : PeriodicLatticeSite L}
    (μ : Fin 3) (hy : y ∈ stepBlockOf c s ell) (hyμ : (y μ).val = (c μ).val) {k : ℕ} (hk : k < ell)
    (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) :
    stepPathSite s y μ k ∈ stepBlockOf c s ell := by
  have hb := mul_lt_of_lt_stride hs hk
  have hyb := mem_stepBlockOf.mp hy
  rw [mem_stepBlockOf]
  intro ν
  rcases eq_or_ne ν μ with rfl | hν
  · have hfitν := hfit ν
    have hv : ((stepPathSite s y ν k) ν).val = (c ν).val + s * k := by
      rw [stepPathSite_apply_self_val, hyμ]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨by omega, by omega, ?_⟩
    rw [hv, Nat.add_sub_cancel_left]
    exact Dvd.intro k rfl
  · rw [stepPathSite_apply_ne s y μ ν k hν]
    exact hyb ν

/-- **UNIQUE PREIMAGE OF AN OFF-AXIS FAR ENDPOINT.** `stepPathSite_eq_far_iff` with the strided
line's base `y` decoupled from the block corner `c`. -/
theorem stepPathSite_eq_far_iff_base {s ell : ℕ} (hs : 0 < s) {c y : PeriodicLatticeSite L}
    (μ : Fin 3) (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) (hroom : s * ell < L μ + 1)
    (hyμ : (y μ).val = (c μ).val)
    {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf c s ell) {i : ℕ} (hi : i < ell) :
    stepPathSite s x μ i = stepPathSite s y μ ell ↔ (1 ≤ i ∧ x = stepPathSite s y μ (ell - i)) := by
  have hfitμ := hfit μ
  have hxμ := mem_stepBlockOf.mp hx μ
  obtain ⟨a, ha⟩ := hxμ.2.2
  have hxval : (x μ).val = (c μ).val + s * a := by omega
  have halt : a < ell := by
    by_contra hcon
    have hle : s * ell ≤ s * a := Nat.mul_le_mul_left s (by omega)
    omega
  have hBa := mul_lt_of_lt_stride hs halt
  have hBi := mul_lt_of_lt_stride hs hi
  constructor
  · intro heq
    have hmu : ((c μ).val + (s * a + s * i)) % (L μ + 1)
        = ((c μ).val + s * ell) % (L μ + 1) := by
      rw [← Nat.add_assoc, ← hxval, ← stepPathSite_apply_self_val s x μ i, heq,
        stepPathSite_apply_self_val s y μ ell, hyμ]
    have hcancel : (s * a + s * i) ≡ (s * ell) [MOD (L μ + 1)] :=
      Nat.ModEq.add_left_cancel' (c μ).val hmu
    have hsum : s * a + s * i = s * ell := by
      rcases Nat.lt_or_ge (s * a + s * i) (s * ell) with hlt | hge
      · have hdvd := (Nat.modEq_iff_dvd' (le_of_lt hlt)).mp hcancel
        have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
      · have hdvd := (Nat.modEq_iff_dvd' hge).mp hcancel.symm
        have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        omega
    have hai : s * (a + i) = s * ell := by rw [Nat.mul_add]; exact hsum
    have haisum : a + i = ell := Nat.eq_of_mul_eq_mul_left hs hai
    have hione : 1 ≤ i := by omega
    refine ⟨hione, ?_⟩
    funext ν
    rcases eq_or_ne ν μ with rfl | hν
    · apply Fin.ext
      rw [stepPathSite_apply_self_val, hyμ, hxval, show ell - i = a by omega,
        Nat.mod_eq_of_lt (by omega)]
    · have hcf := congrFun heq ν
      rw [stepPathSite_apply_ne s x μ ν i hν, stepPathSite_apply_ne s y μ ν ell hν] at hcf
      rw [hcf, stepPathSite_apply_ne s y μ ν (ell - i) hν]
  · rintro ⟨hione, rfl⟩
    show pathSite (pathSite y μ (s * (ell - i))) μ (s * i) = pathSite y μ (s * ell)
    rw [pathSite_add, ← Nat.mul_add, Nat.add_sub_cancel' (le_of_lt hi)]

/-- Reading the off-axis far-endpoint delta field along the strided walk. -/
theorem coarseValAt_farDelta_base {s ell : ℕ} (hs : 0 < s) {c y : PeriodicLatticeSite L}
    {μ : Fin 3} (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) (hroom : s * ell < L μ + 1)
    (hyμ : (y μ).val = (c μ).val)
    (ht : stepPathSite s y μ ell ∈ CoarseLattice L s) (w : SuTwo)
    {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf c s ell) {i : ℕ} (hi : i < ell) :
    coarseValAt s (coarseDelta s (⟨stepPathSite s y μ ell, ht⟩, μ) w) (stepPathSite s x μ i) μ
      = if 1 ≤ i ∧ x = stepPathSite s y μ (ell - i) then w else 0 := by
  by_cases hcase : 1 ≤ i ∧ x = stepPathSite s y μ (ell - i)
  · have heq : stepPathSite s x μ i = stepPathSite s y μ ell :=
      (stepPathSite_eq_far_iff_base hs μ hfit hroom hyμ hx hi).mpr hcase
    have hz : stepPathSite s x μ i ∈ CoarseLattice L s := by rw [heq]; exact ht
    rw [if_pos hcase, coarseValAt_of_mem _ hz μ]
    simp only [coarseDelta]
    rw [if_pos]
    simp only [Prod.mk.injEq, Subtype.mk.injEq, and_true]
    exact heq
  · rw [if_neg hcase]
    by_cases hz : stepPathSite s x μ i ∈ CoarseLattice L s
    · rw [coarseValAt_of_mem _ hz μ]
      simp only [coarseDelta]
      rw [if_neg]
      intro hcon
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hcon
      exact hcase ((stepPathSite_eq_far_iff_base hs μ hfit hroom hyμ hx hi).mp hcon.1)
    · exact coarseValAt_of_not_mem _ hz μ

/-- **THE OFF-AXIS COLLAPSE.** For ANY weight family the double sum of the off-axis far-endpoint
delta probe collapses to the weights at `(y + s·(ell−i)·e_μ, i)`, `i = 1 … ell−1`. -/
theorem farDelta_weighted_sum_base {s ell : ℕ} (hs : 0 < s) {c y : PeriodicLatticeSite L}
    {μ : Fin 3} (hfit : ∀ ν : Fin 3, (c ν).val + s * ell ≤ L ν + 1) (hroom : s * ell < L μ + 1)
    (hy : y ∈ stepBlockOf c s ell) (hyμ : (y μ).val = (c μ).val)
    (ht : stepPathSite s y μ ell ∈ CoarseLattice L s) (w : SuTwo)
    (g : PeriodicLatticeSite L → ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
        RMap (g x i) (coarseValAt s (coarseDelta s (⟨stepPathSite s y μ ell, ht⟩, μ) w)
          (stepPathSite s x μ i) μ))
      = ∑ i ∈ Finset.range ell,
          (if 1 ≤ i then RMap (g (stepPathSite s y μ (ell - i)) i) w else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hilt : i < ell := Finset.mem_range.mp hi
  have hterm : ∀ x ∈ stepBlockOf c s ell,
      RMap (g x i) (coarseValAt s (coarseDelta s (⟨stepPathSite s y μ ell, ht⟩, μ) w)
        (stepPathSite s x μ i) μ)
        = if 1 ≤ i ∧ x = stepPathSite s y μ (ell - i) then RMap (g x i) w else 0 := by
    intro x hx
    rw [coarseValAt_farDelta_base hs hfit hroom hyμ ht w hx hilt]
    split
    · rfl
    · exact map_zero _
  rw [Finset.sum_congr rfl hterm]
  by_cases h1 : 1 ≤ i
  · have hmem : stepPathSite s y μ (ell - i) ∈ stepBlockOf c s ell :=
      stepPathSite_mem_stepBlock_of_base hs μ hy hyμ (by omega) hfit
    rw [if_pos h1]
    simp only [h1, true_and]
    rw [Finset.sum_ite_eq' (stepBlockOf c s ell) (stepPathSite s y μ (ell - i))
      (fun x => RMap (g x i) w), if_pos hmem]
  · rw [if_neg h1]
    exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => h1 h.1))

/-- `∑_{i<2} [1 ≤ i] z i = z 1`. -/
theorem farDelta_sum_two {M : Type*} [AddCommMonoid M] (z : ℕ → M) :
    (∑ i ∈ Finset.range 2, if 1 ≤ i then z i else 0) = z 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp

/-- **MUTATION E — THE STAIRCASE ORDER REVERSED.** `coarseGammaPath` concatenates its three
coordinate segments in CMP95 (1.7)'s DESCENDING order `2, 1, 0`; this is the same staircase with
the segments in ASCENDING order `0, 1, 2`. Same endpoints, same number of steps in each direction,
a different contour. -/
def coarseGammaPathAsc (s : ℕ) (y x : PeriodicLatticeSite L) : List (Fin 3) :=
  coarseStraightSegment s y x 0 ++
    (coarseStraightSegment s (Function.update y 0 (x 0)) x 1 ++
      coarseStraightSegment s (Function.update (Function.update y 0 (x 0)) 1 (x 1)) x 2)

/-- The order-reversed operator. -/
noncomputable def stepBondAvgAtAscOrder (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (1 / (ell : ℝ) ^ 4) • ∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
    RMap (coarsePathHolonomy s V c (coarseGammaPathAsc s c x ++ List.replicate i μ))
      (coarseValAt s A (stepPathSite s x μ i) μ)

/-! #### the off-axis witness: `s = 2`, `ell = 2`, line direction `0`, base `c + 2·e_2` -/

/-- `c + 2·e_0`: the first site of the ASCENDING contour, which the descending one never visits. -/
abbrev qsOrdA : PeriodicLatticeSite qsWitL := stepPathSite 2 qsOrigin 0 1

/-- `c + 2·e_2 + 2·e_0`: the unique surviving summand's site. -/
abbrev qsOrdX : PeriodicLatticeSite qsWitL := stepPathSite 2 qsLegSite 0 1

/-- `c + 2·e_2 + 4·e_0`: the off-axis far endpoint, where the probe field sits. -/
abbrev qsOrdFar : PeriodicLatticeSite qsWitL := stepPathSite 2 qsLegSite 0 2

theorem qsLegSite_mem_coarse : qsLegSite ∈ CoarseLattice qsWitL 2 :=
  stepPathSite_mem_coarseLattice qsWitL_dvd_two qsOrigin_mem_two 2 1

theorem qsOrdFar_mem : qsOrdFar ∈ CoarseLattice qsWitL 2 :=
  stepPathSite_mem_coarseLattice qsWitL_dvd_two qsLegSite_mem_coarse 0 2

theorem qsOrdRoom : (2 : ℕ) * 2 < qsWitL 0 + 1 := by decide

theorem qsLeg_mem_block : qsLegSite ∈ stepBlockOf qsOrigin 2 2 := by decide

theorem qsLeg_zero_val : (qsLegSite (0 : Fin 3)).val = (qsOrigin (0 : Fin 3)).val := by decide

/-- **THE ORDER WITNESS**: `M` on the single coarse link `(c + 2·e_2, 0)`. The DESCENDING staircase
`coarseGammaPath 2 c (c+2e_2+2e_0) = [2, 0]` traverses it as its second step; the ASCENDING
staircase `[0, 2]` does not traverse it at all. -/
noncomputable def qsOrderU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsWitL :=
  fun e => if e = (qsLegSite, (0 : Fin 3)) then witnessMElem else 1

/-- The probe field: `suTwoWitness` on the single coarse bond `(c + 2·e_2 + 4·e_0, 0)`. -/
noncomputable def qsOrderProbe : CoarseBond qsWitL 2 → SuTwo :=
  coarseDelta 2 (⟨qsOrdFar, qsOrdFar_mem⟩, (0 : Fin 3)) suTwoWitness

/-- The DESCENDING contour of the surviving summand, computed from `coarseGammaPath`'s definition. -/
theorem qsOrd_desc_path :
    coarseTransportPath 2 qsOrigin qsOrdX (0 : Fin 3) 1 = [(2 : Fin 3), 0, 0] := by decide

/-- The ASCENDING contour of the same summand: the SAME steps in a different order. -/
theorem qsOrd_asc_path :
    coarseGammaPathAsc 2 qsOrigin qsOrdX ++ List.replicate 1 (0 : Fin 3)
      = [(0 : Fin 3), 2, 0] := by decide

theorem qsOrdShift_origin_two : coarseShift qsOrigin 2 (2 : Fin 3) = qsLegSite := by
  have h := coarseShift_stepPathSite 2 qsOrigin (2 : Fin 3) 0
  rwa [stepPathSite_zero] at h

theorem qsOrdShift_leg_zero : coarseShift qsLegSite 2 (0 : Fin 3) = qsOrdX := by
  have h := coarseShift_stepPathSite 2 qsLegSite (0 : Fin 3) 0
  rwa [stepPathSite_zero] at h

theorem qsOrdShift_origin_zero : coarseShift qsOrigin 2 (0 : Fin 3) = qsOrdA := by
  have h := coarseShift_stepPathSite 2 qsOrigin (0 : Fin 3) 0
  rwa [stepPathSite_zero] at h

theorem qsOrdShift_a_two : coarseShift qsOrdA 2 (2 : Fin 3) = qsOrdX := by decide

theorem qsOrderU_at_origin_two : qsOrderU (qsOrigin, (2 : Fin 3)) = 1 := by
  unfold qsOrderU; rw [if_neg (by decide)]

theorem qsOrderU_at_leg_zero : qsOrderU (qsLegSite, (0 : Fin 3)) = witnessMElem := by
  unfold qsOrderU; rw [if_pos rfl]

theorem qsOrderU_at_x_zero : qsOrderU (qsOrdX, (0 : Fin 3)) = 1 := by
  unfold qsOrderU; rw [if_neg (by decide)]

theorem qsOrderU_at_origin_zero : qsOrderU (qsOrigin, (0 : Fin 3)) = 1 := by
  unfold qsOrderU; rw [if_neg (by decide)]

theorem qsOrderU_at_a_two : qsOrderU (qsOrdA, (2 : Fin 3)) = 1 := by
  unfold qsOrderU; rw [if_neg (by decide)]

/-- **THE REAL OPERATOR'S VALUE ON THE OFF-AXIS PROBE.** The single surviving summand transports
along the DESCENDING contour `[2, 0, 0]`, whose second link is the marked one. -/
theorem qsOrderValue_real :
    stepBondAvgAt 2 qsOrderU 2 qsOrderProbe qsOrigin 0 = (1 / 16 : ℝ) • (-suTwoWitness) := by
  unfold qsOrderProbe stepBondAvgAt
  rw [farDelta_weighted_sum_base (by norm_num) qsFit qsOrdRoom qsLeg_mem_block qsLeg_zero_val
    qsOrdFar_mem suTwoWitness
    (fun x i => coarsePathHolonomy 2 qsOrderU qsOrigin (coarseTransportPath 2 qsOrigin x 0 i)),
    farDelta_sum_two]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (coarsePathHolonomy 2 qsOrderU qsOrigin
    (coarseTransportPath 2 qsOrigin qsOrdX (0 : Fin 3) 1)) suTwoWitness = _
  rw [qsOrd_desc_path]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (qsOrderU (qsOrigin, (2 : Fin 3))
    * coarsePathHolonomy 2 qsOrderU (coarseShift qsOrigin 2 (2 : Fin 3)) [(0 : Fin 3), 0])
      suTwoWitness = _
  rw [qsOrdShift_origin_two]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (qsOrderU (qsOrigin, (2 : Fin 3))
    * (qsOrderU (qsLegSite, (0 : Fin 3))
      * coarsePathHolonomy 2 qsOrderU (coarseShift qsLegSite 2 (0 : Fin 3)) [(0 : Fin 3)]))
      suTwoWitness = _
  rw [qsOrdShift_leg_zero]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (qsOrderU (qsOrigin, (2 : Fin 3))
    * (qsOrderU (qsLegSite, (0 : Fin 3)) * (qsOrderU (qsOrdX, (0 : Fin 3)) * 1))) suTwoWitness = _
  rw [qsOrderU_at_origin_two, qsOrderU_at_leg_zero, qsOrderU_at_x_zero, mul_one, mul_one, one_mul,
    RMap_witnessMElem]
  norm_num

/-- **MUTATION E's VALUE.** The ASCENDING contour `[0, 2, 0]` visits `(c,0)`, `(c+2e_0,2)` and
`(c+2e_2+2e_0,0)` — the marked link `(c+2e_2,0)` is not among them. -/
theorem qsOrderValue_asc :
    stepBondAvgAtAscOrder 2 qsOrderU 2 qsOrderProbe qsOrigin 0 = (1 / 16 : ℝ) • suTwoWitness := by
  unfold qsOrderProbe stepBondAvgAtAscOrder
  rw [farDelta_weighted_sum_base (by norm_num) qsFit qsOrdRoom qsLeg_mem_block qsLeg_zero_val
    qsOrdFar_mem suTwoWitness
    (fun x i => coarsePathHolonomy 2 qsOrderU qsOrigin
      (coarseGammaPathAsc 2 qsOrigin x ++ List.replicate i (0 : Fin 3))),
    farDelta_sum_two]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (coarsePathHolonomy 2 qsOrderU qsOrigin
    (coarseGammaPathAsc 2 qsOrigin qsOrdX ++ List.replicate 1 (0 : Fin 3))) suTwoWitness = _
  rw [qsOrd_asc_path]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (qsOrderU (qsOrigin, (0 : Fin 3))
    * coarsePathHolonomy 2 qsOrderU (coarseShift qsOrigin 2 (0 : Fin 3)) [(2 : Fin 3), 0])
      suTwoWitness = _
  rw [qsOrdShift_origin_zero]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (qsOrderU (qsOrigin, (0 : Fin 3))
    * (qsOrderU (qsOrdA, (2 : Fin 3))
      * coarsePathHolonomy 2 qsOrderU (coarseShift qsOrdA 2 (2 : Fin 3)) [(0 : Fin 3)]))
      suTwoWitness = _
  rw [qsOrdShift_a_two]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (qsOrderU (qsOrigin, (0 : Fin 3))
    * (qsOrderU (qsOrdA, (2 : Fin 3)) * (qsOrderU (qsOrdX, (0 : Fin 3)) * 1))) suTwoWitness = _
  rw [qsOrderU_at_origin_zero, qsOrderU_at_a_two, qsOrderU_at_x_zero, mul_one, mul_one, one_mul,
    RMap_one, LinearMap.id_apply]
  norm_num

/-- **THE STAIRCASE ORDER IS OBSERVABLE AT `s > 1`.** Reversing `coarseGammaPath`'s coordinate
order changes the operator's value. ~~This closes the residual §11 formerly only disclosed: the
`2,1,0` order of CMP95 (1.7) is now pinned by a control, not merely by the definition.~~
**CORRECTED — that sentence overclaimed and is retained struck.** This witness's surviving site
`qsOrdX` shares coordinate `1` with `qsOrigin`, so the staircase's MIDDLE segment is empty here
(`qsOrdX_middle_segment_empty`). What this theorem pins is therefore the RELATIVE order of the two
NON-EMPTY segments, `2` before `0`; it does not locate the third. The order `2,0,1` — the same
relative order of `2` and `0`, with the empty segment relocated from the middle to the end — has
exactly this witness's value (`stepBondAvgAtOrd201_eq_real_at_ordX`). The full three-way order of
CMP95 (1.7) is pinned by `stepBondAvgAt_ne_ord_full` on the three-segment witness of
`section StraightLegOffAxisFull`. -/
theorem stepBondAvgAt_ne_ascOrder_offAxis :
    stepBondAvgAt 2 qsOrderU 2 qsOrderProbe qsOrigin 0
      ≠ stepBondAvgAtAscOrder 2 qsOrderU 2 qsOrderProbe qsOrigin 0 := by
  rw [qsOrderValue_real, qsOrderValue_asc]
  exact smul_neg_witness_ne (by norm_num)

/-- The off-axis probe is not about the zero object. -/
theorem qsOrderValue_real_ne_zero :
    stepBondAvgAt 2 qsOrderU 2 qsOrderProbe qsOrigin 0 ≠ 0 := by
  rw [qsOrderValue_real]
  exact smul_neg_witness_ne_zero (by norm_num)

/-- The off-axis witness is a must-fire in its own right. -/
theorem stepBondAvgAt_offAxis_mustfire :
    stepBondAvgAt 2 qsOrderU 2 qsOrderProbe qsOrigin 0
      ≠ stepBondAvgAt 2 (trivialU qsWitL) 2 qsOrderProbe qsOrigin 0 := by
  have htriv : stepBondAvgAt 2 (trivialU qsWitL) 2 qsOrderProbe qsOrigin 0
      = (1 / 16 : ℝ) • suTwoWitness := by
    unfold qsOrderProbe stepBondAvgAt
    rw [farDelta_weighted_sum_base (by norm_num) qsFit qsOrdRoom qsLeg_mem_block qsLeg_zero_val
      qsOrdFar_mem suTwoWitness
      (fun x i => coarsePathHolonomy 2 (trivialU qsWitL) qsOrigin
        (coarseTransportPath 2 qsOrigin x 0 i)),
      farDelta_sum_two, coarsePathHolonomy_trivialU, RMap_one, LinearMap.id_apply]
    norm_num
  rw [qsOrderValue_real, htriv]
  exact smul_neg_witness_ne (by norm_num)

end StraightLegOffAxis

/-! ### THE COMPLETING ORDER CONTROL — a witness OFF **ALL THREE** AXES

`section StraightLegOffAxis` above puts the surviving summand at `qsOrdX = c + 2·e_2 + 2·e_0`, which
shares coordinate `1` with the block corner `c`. So `coarseStraightSegment 2 c qsOrdX 1 = []`
(`qsOrdX_middle_segment_empty` below), and concatenating an empty list is invisible: at that witness
the contour of segment order `2,0,1` is TEXTUALLY the contour of the real order `2,1,0`
(`ordX_ord201_path_eq_desc`) and the two operators have the SAME value
(`stepBondAvgAtOrd201_eq_real_at_ordX`). `stepBondAvgAt_ne_ascOrder_offAxis` therefore pins only the
RELATIVE order of the two NON-EMPTY segments `2` and `0` — not the position of the third.

This block removes that restriction. The strided line's base is moved to `y = c + 2·e_1 + 2·e_2`,
still a block member sharing `c`'s `μ = 0` coordinate, so the unique surviving summand sits at
`x = c + 2·e_0 + 2·e_1 + 2·e_2` and ALL THREE coordinate segments have length one
(`qsTri_all_three_segments`).

* `coarseGammaPathOrd p q r` / `stepBondAvgAtOrd p q r` — the staircase with its three coordinate
  segments concatenated in the order `p, q, r`. `2,1,0` is `coarseGammaPath` itself and `0,1,2` is
  `coarseGammaPathAsc`, both by `rfl` (`coarseGammaPathOrd_desc`, `coarseGammaPathOrd_asc`), so this
  is a strict generalisation of the existing mutation E and introduces no second convention.
* `linkCount` / `coarseLinkList` / `coarsePathHolonomy_markLinkU` — the holonomy of a
  single-marked-link background along ANY unit path is `M ^ (number of times the path traverses the
  marked link)`. This is what makes one witness settle all six orders at once.
* `qsTriU` — the witness: `M` on the single coarse link `(c + 2·e_2, 1)`, the SECOND link of the
  descending contour (`qsTri_desc_links`) and a link that NO other segment order traverses
  (`qsTriCount_zero_of_ne_desc`).
* `stepBondAvgAt_ne_ord_full` — **the kill**: for every ordering of the three distinct coordinate
  directions other than the descending `2,1,0`, the reordered operator differs from the real one at
  this witness. The five named instances are `stepBondAvgAt_ne_ord201_full` (the `2,0,1` escape),
  `stepBondAvgAt_ne_ord120_full`, `stepBondAvgAt_ne_ord102_full`, `stepBondAvgAt_ne_ord021_full`
  and `stepBondAvgAt_ne_ascOrder_full` (mutation E).

The last sub-block repeats the whole construction at a SECOND stride, `s = 4` on the `16³` torus
(`qsBigTriU`, `stepBondAvgAt_ne_ord_full_s4`), so the order kill does not rest on one stride.

**SCOPE.** Like every control in this module these are WITNESS-BASED: they exhibit two concrete
configurations at which the six segment orders take different values, not a theorem that the orders
differ for all `s`, `ell`, `L` and all backgrounds. Both witnesses have `ell = 2`, because
`farDelta_sum_two` is the only collapse this module carries; an `ell = 4` full-order witness would
need a `farDelta_sum_four` analogue and does not exist here.
-/

section StraightLegOffAxisFull

/-! #### the links a unit path traverses, and a single-marked-link background -/

/-- The list of COARSE LINKS a unit-level forward path traverses, in order. -/
def coarseLinkList (ell : ℕ) : PeriodicLatticeSite L → List (Fin 3) →
    List (PeriodicLatticeSite L × Fin 3)
  | _, [] => []
  | y, μ :: rest => (y, μ) :: coarseLinkList ell (coarseShift y ell μ) rest

/-- The holonomy is the ordered product of the background over the traversed links. -/
theorem coarsePathHolonomy_eq_linkProd {G : Type*} [Group G] (ell : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    coarsePathHolonomy ell V y p = ((coarseLinkList ell y p).map V).prod := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih =>
    show V (y, μ) * coarsePathHolonomy ell V (coarseShift y ell μ) rest = _
    rw [ih]
    rfl

/-- How many times a unit-level forward path traverses ONE given coarse link. -/
def linkCount (ell : ℕ) (e0 : PeriodicLatticeSite L × Fin 3) :
    PeriodicLatticeSite L → List (Fin 3) → ℕ
  | _, [] => 0
  | y, μ :: rest => (if (y, μ) = e0 then 1 else 0) + linkCount ell e0 (coarseShift y ell μ) rest

theorem linkCount_eq_count (ell : ℕ) (e0 : PeriodicLatticeSite L × Fin 3)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    linkCount ell e0 y p = (coarseLinkList ell y p).count e0 := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih =>
    show (if (y, μ) = e0 then 1 else 0) + linkCount ell e0 (coarseShift y ell μ) rest
      = ((y, μ) :: coarseLinkList ell (coarseShift y ell μ) rest).count e0
    rw [List.count_cons, ih]
    by_cases h : (y, μ) = e0
    · rw [if_pos h, if_pos (show ((y, μ) == e0) = true by simp [h]), Nat.add_comm]
    · rw [if_neg h, if_neg (show ¬(((y, μ) == e0) = true) by simp [h]), Nat.add_comm]

/-- A background carrying `M` on ONE coarse link and `1` on every other. `qsLegU`, `qsFarU`,
`qsOrderU`, `qsBig4U` and `qsTriU` are all of this shape. -/
def markLinkU {G : Type*} [One G] (e0 : PeriodicLatticeSite L × Fin 3) (M : G) :
    PeriodicLinkConfiguration G L := fun e => if e = e0 then M else 1

/-- **THE SINGLE-MARK HOLONOMY LAW.** Along ANY unit-level forward path, a single-marked-link
background contributes `M` once per traversal of the marked link and nothing else. This is the
lemma that lets ONE witness decide ALL SIX segment orders. -/
theorem coarsePathHolonomy_markLinkU {G : Type*} [Group G] (ell : ℕ)
    (e0 : PeriodicLatticeSite L × Fin 3) (M : G) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    coarsePathHolonomy ell (markLinkU e0 M) y p = M ^ linkCount ell e0 y p := by
  induction p generalizing y with
  | nil => simp [coarsePathHolonomy, linkCount]
  | cons μ rest ih =>
    show markLinkU e0 M (y, μ) * coarsePathHolonomy ell (markLinkU e0 M) (coarseShift y ell μ) rest
      = M ^ ((if (y, μ) = e0 then 1 else 0) + linkCount ell e0 (coarseShift y ell μ) rest)
    rw [ih, pow_add]
    by_cases h : (y, μ) = e0
    · show (if (y, μ) = e0 then M else 1) * _ = _
      rw [if_pos h, if_pos h, pow_one]
    · show (if (y, μ) = e0 then M else 1) * _ = _
      rw [if_neg h, if_neg h, pow_zero, one_mul]

/-- The existing off-axis witness is exactly a single-marked-link background — the new machinery is
not a look-alike of the old one. -/
theorem qsOrderU_eq_markLinkU :
    qsOrderU = markLinkU ((qsLegSite : PeriodicLatticeSite qsWitL), (0 : Fin 3)) witnessMElem := rfl

/-! #### the staircase at an ARBITRARY segment order -/

/-- `coarseGammaPath` with its three coordinate segments concatenated in the order `p, q, r`. -/
def coarseGammaPathOrd (p q r : Fin 3) (s : ℕ) (y x : PeriodicLatticeSite L) : List (Fin 3) :=
  coarseStraightSegment s y x p ++
    (coarseStraightSegment s (Function.update y p (x p)) x q ++
      coarseStraightSegment s (Function.update (Function.update y p (x p)) q (x q)) x r)

/-- Order `2,1,0` IS `coarseGammaPath` — CMP95 (1.7)'s descending staircase. -/
theorem coarseGammaPathOrd_desc (s : ℕ) (y x : PeriodicLatticeSite L) :
    coarseGammaPathOrd 2 1 0 s y x = coarseGammaPath s y x := rfl

/-- Order `0,1,2` IS `coarseGammaPathAsc` — mutation E. -/
theorem coarseGammaPathOrd_asc (s : ℕ) (y x : PeriodicLatticeSite L) :
    coarseGammaPathOrd 0 1 2 s y x = coarseGammaPathAsc s y x := rfl

/-- **THE SIX VARIANTS DIFFER ONLY IN THE ORDER OF THE THREE DIRECTIONS.** Each straight segment
reads only the coordinate it steps in, and the `Function.update`s preceding it are at OTHER
coordinates, so they cannot change its length. Hence for distinct `p, q, r` the staircase is
literally `replicate (steps p) p ++ replicate (steps q) q ++ replicate (steps r) r`: nothing but the
concatenation ORDER distinguishes the six variants, and a mutation that only rewrites the
intermediate bases is a NO-OP. (Recorded because one mutant in this lane's battery
— `compute/strided_order/mutants/M5_NOOP_gammaPathOrd_third_base_drops_update.lean` — is exactly
such a
no-op and correctly does NOT fire.) -/
theorem coarseGammaPathOrd_eq_replicates {p q r : Fin 3} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (s : ℕ) (y x : PeriodicLatticeSite L) :
    coarseGammaPathOrd p q r s y x
      = List.replicate (coarseCoordSteps s y x p) p ++
        (List.replicate (coarseCoordSteps s y x q) q ++
          List.replicate (coarseCoordSteps s y x r) r) := by
  unfold coarseGammaPathOrd coarseStraightSegment coarseCoordSteps
  simp only [Function.update_of_ne hpq.symm, Function.update_of_ne hpr.symm,
    Function.update_of_ne hqr.symm]

/-- The operator whose staircase uses segment order `p, q, r`. -/
noncomputable def stepBondAvgAtOrd (p q r : Fin 3) (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (1 / (ell : ℝ) ^ 4) • ∑ x ∈ stepBlockOf c s ell, ∑ i ∈ Finset.range ell,
    RMap (coarsePathHolonomy s V c (coarseGammaPathOrd p q r s c x ++ List.replicate i μ))
      (coarseValAt s A (stepPathSite s x μ i) μ)

theorem stepBondAvgAtOrd_desc (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) :
    stepBondAvgAtOrd 2 1 0 s V ell A c μ = stepBondAvgAt s V ell A c μ := rfl

theorem stepBondAvgAtOrd_asc (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (A : CoarseBond L s → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) :
    stepBondAvgAtOrd 0 1 2 s V ell A c μ = stepBondAvgAtAscOrder s V ell A c μ := rfl

/-! #### DIAGNOSIS: what the two-segment witness cannot see -/

/-- The old witness's MIDDLE segment is empty. -/
theorem qsOrdX_middle_segment_empty :
    coarseStraightSegment 2 qsOrigin qsOrdX (1 : Fin 3) = [] := by decide

/-- Hence at the old witness the `2,0,1` contour is TEXTUALLY the real `2,1,0` contour. -/
theorem ordX_ord201_path_eq_desc :
    coarseGammaPathOrd 2 0 1 2 qsOrigin qsOrdX ++ List.replicate 1 (0 : Fin 3)
      = coarseTransportPath 2 qsOrigin qsOrdX (0 : Fin 3) 1 := by decide

theorem ordX_count_201 :
    linkCount 2 ((qsLegSite : PeriodicLatticeSite qsWitL), (0 : Fin 3)) qsOrigin
      (coarseGammaPathOrd 2 0 1 2 qsOrigin qsOrdX ++ List.replicate 1 (0 : Fin 3)) = 1 := by decide

/-- **THE ESCAPE, PROVED IN-MODULE.** At the two-segment witness of `section StraightLegOffAxis` the
`2,0,1` order — segment `1` relocated from the middle to the END, with `2` still before `0` — has
exactly the real operator's value. `stepBondAvgAt_ne_ascOrder_offAxis` does NOT pin the full order. -/
theorem stepBondAvgAtOrd201_eq_real_at_ordX :
    stepBondAvgAtOrd 2 0 1 2 qsOrderU 2 qsOrderProbe qsOrigin 0
      = stepBondAvgAt 2 qsOrderU 2 qsOrderProbe qsOrigin 0 := by
  rw [qsOrderValue_real]
  unfold qsOrderProbe stepBondAvgAtOrd
  rw [farDelta_weighted_sum_base (by norm_num) qsFit qsOrdRoom qsLeg_mem_block qsLeg_zero_val
    qsOrdFar_mem suTwoWitness
    (fun x i => coarsePathHolonomy 2 qsOrderU qsOrigin (coarseGammaPathOrd 2 0 1 2 qsOrigin x
      ++ List.replicate i (0 : Fin 3))),
    farDelta_sum_two]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (coarsePathHolonomy 2 qsOrderU qsOrigin
    (coarseGammaPathOrd 2 0 1 2 qsOrigin qsOrdX ++ List.replicate 1 (0 : Fin 3))) suTwoWitness = _
  rw [qsOrderU_eq_markLinkU, coarsePathHolonomy_markLinkU, ordX_count_201, pow_one,
    RMap_witnessMElem]
  norm_num

/-! #### the THREE-segment witness: `s = 2`, `ell = 2`, line direction `0`, base `c + 2e_1 + 2e_2` -/

/-- The line BASE `c + 2·e_1 + 2·e_2`: a block member sharing the corner's `0`-coordinate, off both
other axes of `c`. -/
abbrev qsTriBase : PeriodicLatticeSite qsWitL := stepPathSite 2 qsLegSite 1 1

/-- The unique surviving summand's site `c + 2·e_0 + 2·e_1 + 2·e_2` — differs from `c` in ALL THREE
coordinates. -/
abbrev qsTriX : PeriodicLatticeSite qsWitL := stepPathSite 2 qsTriBase 0 1

/-- The far endpoint `c + 4·e_0 + 2·e_1 + 2·e_2`, where the probe field sits. -/
abbrev qsTriFar : PeriodicLatticeSite qsWitL := stepPathSite 2 qsTriBase 0 2

theorem qsTriBase_mem_coarse : qsTriBase ∈ CoarseLattice qsWitL 2 :=
  stepPathSite_mem_coarseLattice qsWitL_dvd_two qsLegSite_mem_coarse 1 1

theorem qsTriFar_mem : qsTriFar ∈ CoarseLattice qsWitL 2 :=
  stepPathSite_mem_coarseLattice qsWitL_dvd_two qsTriBase_mem_coarse 0 2

theorem qsTri_mem_block : qsTriBase ∈ stepBlockOf qsOrigin 2 2 := by decide

theorem qsTri_zero_val : (qsTriBase (0 : Fin 3)).val = (qsOrigin (0 : Fin 3)).val := by decide

/-- **THE COMPLETING FACT.** Every one of the three coordinate segments from `c` to the surviving
summand has length one — no segment of this staircase is empty, so no relocation of a segment is
invisible. -/
theorem qsTri_all_three_segments : ∀ ν : Fin 3, coarseCoordSteps 2 qsOrigin qsTriX ν = 1 := by decide

/-- **THE FULL-ORDER WITNESS**: `M` on the single coarse link `(c + 2·e_2, 1)`. -/
noncomputable def qsTriU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsWitL :=
  markLinkU ((qsLegSite : PeriodicLatticeSite qsWitL), (1 : Fin 3)) witnessMElem

/-- The probe field: `suTwoWitness` on the single coarse bond `(qsTriFar, 0)`. -/
noncomputable def qsTriProbe : CoarseBond qsWitL 2 → SuTwo :=
  coarseDelta 2 (⟨qsTriFar, qsTriFar_mem⟩, (0 : Fin 3)) suTwoWitness

/-- The DESCENDING contour's four links, explicitly. The marked link `(qsLegSite, 1)` is its
second. -/
theorem qsTri_desc_links :
    coarseLinkList 2 qsOrigin
        (coarseGammaPathOrd 2 1 0 2 qsOrigin qsTriX ++ List.replicate 1 (0 : Fin 3))
      = [(qsOrigin, 2), (qsLegSite, 1), (qsTriBase, 0), (qsTriX, 0)] := by decide

/-- Mutation F's contour (`2,0,1`) — the same four steps, three of its four links different, and
the marked link is NOT among them. -/
theorem qsTri_ord201_links :
    coarseLinkList 2 qsOrigin
        (coarseGammaPathOrd 2 0 1 2 qsOrigin qsTriX ++ List.replicate 1 (0 : Fin 3))
      = [(qsOrigin, 2), (qsLegSite, 0), (qsOrdX, 1), (qsTriX, 0)] := by decide

/-- ANTI-STRAWMAN 1: every ordering of three distinct directions ends at the SAME far endpoint. -/
theorem qsTriOrd_same_endpoint : ∀ p q r : Fin 3, p ≠ q → q ≠ r → p ≠ r →
    coarsePathEndpoint 2 qsOrigin
      (coarseGammaPathOrd p q r 2 qsOrigin qsTriX ++ List.replicate 1 (0 : Fin 3)) = qsTriFar := by
  decide

/-- ANTI-STRAWMAN 2: every such ordering takes the SAME number of steps in each direction. -/
theorem qsTriOrd_same_step_counts : ∀ p q r : Fin 3, p ≠ q → q ≠ r → p ≠ r → ∀ ν : Fin 3,
    (coarseGammaPathOrd p q r 2 qsOrigin qsTriX ++ List.replicate 1 (0 : Fin 3)).count ν
      = [(2 : Fin 3), 1, 0, 0].count ν := by decide

/-! #### the values, and the kill -/

/-- **THE VALUE AT ANY SEGMENT ORDER.** One computation covers all six orders: the value is fixed by
how many times that order's contour traverses the marked link. -/
theorem qsTriValue_ord (p q r : Fin 3) :
    stepBondAvgAtOrd p q r 2 qsTriU 2 qsTriProbe qsOrigin 0
      = (1 / 16 : ℝ) • RMap (witnessMElem ^ linkCount 2
          ((qsLegSite : PeriodicLatticeSite qsWitL), (1 : Fin 3)) qsOrigin
          (coarseGammaPathOrd p q r 2 qsOrigin qsTriX ++ List.replicate 1 (0 : Fin 3)))
          suTwoWitness := by
  unfold qsTriProbe stepBondAvgAtOrd
  rw [farDelta_weighted_sum_base (by norm_num) qsFit qsOrdRoom qsTri_mem_block qsTri_zero_val
    qsTriFar_mem suTwoWitness
    (fun x i => coarsePathHolonomy 2 qsTriU qsOrigin (coarseGammaPathOrd p q r 2 qsOrigin x
      ++ List.replicate i (0 : Fin 3))),
    farDelta_sum_two]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (coarsePathHolonomy 2 qsTriU qsOrigin
    (coarseGammaPathOrd p q r 2 qsOrigin qsTriX ++ List.replicate 1 (0 : Fin 3))) suTwoWitness = _
  rw [show qsTriU = markLinkU ((qsLegSite : PeriodicLatticeSite qsWitL), (1 : Fin 3)) witnessMElem
    from rfl, coarsePathHolonomy_markLinkU]
  norm_num

theorem qsTriCount_desc :
    linkCount 2 ((qsLegSite : PeriodicLatticeSite qsWitL), (1 : Fin 3)) qsOrigin
      (coarseGammaPathOrd 2 1 0 2 qsOrigin qsTriX ++ List.replicate 1 (0 : Fin 3)) = 1 := by decide

/-- **THE MARKED LINK IS TRAVERSED BY THE DESCENDING ORDER ALONE.** For every ordering of three
distinct coordinate directions other than `2,1,0`, the contour misses it entirely. -/
theorem qsTriCount_zero_of_ne_desc : ∀ p q r : Fin 3, p ≠ q → q ≠ r → p ≠ r →
    ¬(p = 2 ∧ q = 1 ∧ r = 0) →
      linkCount 2 ((qsLegSite : PeriodicLatticeSite qsWitL), (1 : Fin 3)) qsOrigin
        (coarseGammaPathOrd p q r 2 qsOrigin qsTriX ++ List.replicate 1 (0 : Fin 3)) = 0 := by
  decide

/-- The real operator's value on the three-segment witness. -/
theorem qsTriValue_real :
    stepBondAvgAt 2 qsTriU 2 qsTriProbe qsOrigin 0 = (1 / 16 : ℝ) • (-suTwoWitness) := by
  rw [← stepBondAvgAtOrd_desc, qsTriValue_ord, qsTriCount_desc, pow_one, RMap_witnessMElem]

/-- Every other ordering's value. -/
theorem qsTriValue_ord_of_ne_desc {p q r : Fin 3} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (hne : ¬(p = 2 ∧ q = 1 ∧ r = 0)) :
    stepBondAvgAtOrd p q r 2 qsTriU 2 qsTriProbe qsOrigin 0 = (1 / 16 : ℝ) • suTwoWitness := by
  rw [qsTriValue_ord, qsTriCount_zero_of_ne_desc p q r hpq hqr hpr hne, pow_zero, RMap_one,
    LinearMap.id_apply]

/-- **THE FULL THREE-WAY STAIRCASE ORDER IS PINNED BY A CONTROL.** Reordering `coarseGammaPath`'s
three coordinate segments in ANY way other than CMP95 (1.7)'s descending `2,1,0` changes the
operator's value at this witness. Unlike `stepBondAvgAt_ne_ascOrder_offAxis`, no segment is empty
here, so this separates the real order from all FIVE relocations, not from one. -/
theorem stepBondAvgAt_ne_ord_full {p q r : Fin 3} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (hne : ¬(p = 2 ∧ q = 1 ∧ r = 0)) :
    stepBondAvgAt 2 qsTriU 2 qsTriProbe qsOrigin 0
      ≠ stepBondAvgAtOrd p q r 2 qsTriU 2 qsTriProbe qsOrigin 0 := by
  rw [qsTriValue_real, qsTriValue_ord_of_ne_desc hpq hqr hpr hne]
  exact smul_neg_witness_ne (by norm_num)

/-- **MUTATION F IS DEAD.** The `2,0,1` order that reproduced the real operator at the two-segment
witness (`stepBondAvgAtOrd201_eq_real_at_ordX`) is separated here. -/
theorem stepBondAvgAt_ne_ord201_full :
    stepBondAvgAt 2 qsTriU 2 qsTriProbe qsOrigin 0
      ≠ stepBondAvgAtOrd 2 0 1 2 qsTriU 2 qsTriProbe qsOrigin 0 :=
  stepBondAvgAt_ne_ord_full (by decide) (by decide) (by decide) (by decide)

theorem stepBondAvgAt_ne_ord120_full :
    stepBondAvgAt 2 qsTriU 2 qsTriProbe qsOrigin 0
      ≠ stepBondAvgAtOrd 1 2 0 2 qsTriU 2 qsTriProbe qsOrigin 0 :=
  stepBondAvgAt_ne_ord_full (by decide) (by decide) (by decide) (by decide)

theorem stepBondAvgAt_ne_ord102_full :
    stepBondAvgAt 2 qsTriU 2 qsTriProbe qsOrigin 0
      ≠ stepBondAvgAtOrd 1 0 2 2 qsTriU 2 qsTriProbe qsOrigin 0 :=
  stepBondAvgAt_ne_ord_full (by decide) (by decide) (by decide) (by decide)

theorem stepBondAvgAt_ne_ord021_full :
    stepBondAvgAt 2 qsTriU 2 qsTriProbe qsOrigin 0
      ≠ stepBondAvgAtOrd 0 2 1 2 qsTriU 2 qsTriProbe qsOrigin 0 :=
  stepBondAvgAt_ne_ord_full (by decide) (by decide) (by decide) (by decide)

/-- Mutation E (ascending `0,1,2`) is killed on the three-segment witness too. -/
theorem stepBondAvgAt_ne_ascOrder_full :
    stepBondAvgAt 2 qsTriU 2 qsTriProbe qsOrigin 0
      ≠ stepBondAvgAtAscOrder 2 qsTriU 2 qsTriProbe qsOrigin 0 := by
  rw [← stepBondAvgAtOrd_asc]
  exact stepBondAvgAt_ne_ord_full (by decide) (by decide) (by decide) (by decide)

/-- The three-segment probe is not about the zero object. -/
theorem qsTriValue_real_ne_zero : stepBondAvgAt 2 qsTriU 2 qsTriProbe qsOrigin 0 ≠ 0 := by
  rw [qsTriValue_real]
  exact smul_neg_witness_ne_zero (by norm_num)

/-- The three-segment witness is a must-fire in its own right. -/
theorem stepBondAvgAt_triWitness_mustfire :
    stepBondAvgAt 2 qsTriU 2 qsTriProbe qsOrigin 0
      ≠ stepBondAvgAt 2 (trivialU qsWitL) 2 qsTriProbe qsOrigin 0 := by
  have htriv : stepBondAvgAt 2 (trivialU qsWitL) 2 qsTriProbe qsOrigin 0
      = (1 / 16 : ℝ) • suTwoWitness := by
    unfold qsTriProbe stepBondAvgAt
    rw [farDelta_weighted_sum_base (by norm_num) qsFit qsOrdRoom qsTri_mem_block qsTri_zero_val
      qsTriFar_mem suTwoWitness
      (fun x i => coarsePathHolonomy 2 (trivialU qsWitL) qsOrigin
        (coarseTransportPath 2 qsOrigin x 0 i)),
      farDelta_sum_two, coarsePathHolonomy_trivialU, RMap_one, LinearMap.id_apply]
    norm_num
  rw [qsTriValue_real, htriv]
  exact smul_neg_witness_ne (by norm_num)

/-! #### THE SAME KILL AT A SECOND STRIDE — `s = 4` on the `16³` torus

The three-segment witness above is at `s = 2`. Nothing in the argument is special to that stride:
the same construction on `qsBigL` marks `(c + 4·e_2, 1)`, and the same enumeration shows the
descending order alone traverses it. This block exists so the order kill is not resting on one
stride. -/

theorem qsBigLeg_mem_coarse : qsBigLeg ∈ CoarseLattice qsBigL 4 :=
  stepPathSite_mem_coarseLattice qsBigL_dvd_four qsBigOrigin_mem 2 1

/-- `c + 4·e_1 + 4·e_2` on the `16³` torus. -/
abbrev qsBigTriBase : PeriodicLatticeSite qsBigL := stepPathSite 4 qsBigLeg 1 1

/-- `c + 4·e_0 + 4·e_1 + 4·e_2` — the surviving summand, off all three axes of `c`. -/
abbrev qsBigTriX : PeriodicLatticeSite qsBigL := stepPathSite 4 qsBigTriBase 0 1

/-- `c + 8·e_0 + 4·e_1 + 4·e_2` — the far endpoint. -/
abbrev qsBigTriFar : PeriodicLatticeSite qsBigL := stepPathSite 4 qsBigTriBase 0 2

theorem qsBigTriBase_mem_coarse : qsBigTriBase ∈ CoarseLattice qsBigL 4 :=
  stepPathSite_mem_coarseLattice qsBigL_dvd_four qsBigLeg_mem_coarse 1 1

theorem qsBigTriFar_mem : qsBigTriFar ∈ CoarseLattice qsBigL 4 :=
  stepPathSite_mem_coarseLattice qsBigL_dvd_four qsBigTriBase_mem_coarse 0 2

theorem qsBigTriRoom : (4 : ℕ) * 2 < qsBigL 0 + 1 := by decide

theorem qsBigTri_mem_block : qsBigTriBase ∈ stepBlockOf qsBigOrigin 4 2 :=
  mem_stepBlockOf.mpr (by decide)

theorem qsBigTri_zero_val : (qsBigTriBase (0 : Fin 3)).val = (qsBigOrigin (0 : Fin 3)).val := by
  decide

/-- All three coordinate segments have length one at `s = 4` too. -/
theorem qsBigTri_all_three_segments :
    ∀ ν : Fin 3, coarseCoordSteps 4 qsBigOrigin qsBigTriX ν = 1 := by decide

/-- The `s = 4` full-order witness: `M` on the single coarse link `(c + 4·e_2, 1)`. -/
noncomputable def qsBigTriU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) qsBigL :=
  markLinkU ((qsBigLeg : PeriodicLatticeSite qsBigL), (1 : Fin 3)) witnessMElem

noncomputable def qsBigTriProbe : CoarseBond qsBigL 4 → SuTwo :=
  coarseDelta 4 (⟨qsBigTriFar, qsBigTriFar_mem⟩, (0 : Fin 3)) suTwoWitness

/-- The `s = 4` descending contour's four links. -/
theorem qsBigTri_desc_links :
    coarseLinkList 4 qsBigOrigin
        (coarseGammaPathOrd 2 1 0 4 qsBigOrigin qsBigTriX ++ List.replicate 1 (0 : Fin 3))
      = [(qsBigOrigin, 2), (qsBigLeg, 1), (qsBigTriBase, 0), (qsBigTriX, 0)] := by decide

theorem qsBigTriValue_ord (p q r : Fin 3) :
    stepBondAvgAtOrd p q r 4 qsBigTriU 2 qsBigTriProbe qsBigOrigin 0
      = (1 / 16 : ℝ) • RMap (witnessMElem ^ linkCount 4
          ((qsBigLeg : PeriodicLatticeSite qsBigL), (1 : Fin 3)) qsBigOrigin
          (coarseGammaPathOrd p q r 4 qsBigOrigin qsBigTriX ++ List.replicate 1 (0 : Fin 3)))
          suTwoWitness := by
  unfold qsBigTriProbe stepBondAvgAtOrd
  rw [farDelta_weighted_sum_base (by norm_num) qsBigFit qsBigTriRoom qsBigTri_mem_block
    qsBigTri_zero_val qsBigTriFar_mem suTwoWitness
    (fun x i => coarsePathHolonomy 4 qsBigTriU qsBigOrigin
      (coarseGammaPathOrd p q r 4 qsBigOrigin x ++ List.replicate i (0 : Fin 3))),
    farDelta_sum_two]
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • RMap (coarsePathHolonomy 4 qsBigTriU qsBigOrigin
    (coarseGammaPathOrd p q r 4 qsBigOrigin qsBigTriX ++ List.replicate 1 (0 : Fin 3)))
      suTwoWitness = _
  rw [show qsBigTriU = markLinkU ((qsBigLeg : PeriodicLatticeSite qsBigL), (1 : Fin 3)) witnessMElem
    from rfl, coarsePathHolonomy_markLinkU]
  norm_num

theorem qsBigTriCount_desc :
    linkCount 4 ((qsBigLeg : PeriodicLatticeSite qsBigL), (1 : Fin 3)) qsBigOrigin
      (coarseGammaPathOrd 2 1 0 4 qsBigOrigin qsBigTriX ++ List.replicate 1 (0 : Fin 3)) = 1 := by
  decide

theorem qsBigTriCount_zero_of_ne_desc : ∀ p q r : Fin 3, p ≠ q → q ≠ r → p ≠ r →
    ¬(p = 2 ∧ q = 1 ∧ r = 0) →
      linkCount 4 ((qsBigLeg : PeriodicLatticeSite qsBigL), (1 : Fin 3)) qsBigOrigin
        (coarseGammaPathOrd p q r 4 qsBigOrigin qsBigTriX ++ List.replicate 1 (0 : Fin 3)) = 0 := by
  decide

theorem qsBigTriValue_real :
    stepBondAvgAt 4 qsBigTriU 2 qsBigTriProbe qsBigOrigin 0 = (1 / 16 : ℝ) • (-suTwoWitness) := by
  rw [← stepBondAvgAtOrd_desc, qsBigTriValue_ord, qsBigTriCount_desc, pow_one, RMap_witnessMElem]

/-- **THE FULL ORDER IS PINNED AT `s = 4` AS WELL.** -/
theorem stepBondAvgAt_ne_ord_full_s4 {p q r : Fin 3} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (hne : ¬(p = 2 ∧ q = 1 ∧ r = 0)) :
    stepBondAvgAt 4 qsBigTriU 2 qsBigTriProbe qsBigOrigin 0
      ≠ stepBondAvgAtOrd p q r 4 qsBigTriU 2 qsBigTriProbe qsBigOrigin 0 := by
  rw [qsBigTriValue_real, qsBigTriValue_ord,
    qsBigTriCount_zero_of_ne_desc p q r hpq hqr hpr hne, pow_zero, RMap_one, LinearMap.id_apply]
  exact smul_neg_witness_ne (by norm_num)

/-- Mutation F at `s = 4`. -/
theorem stepBondAvgAt_ne_ord201_full_s4 :
    stepBondAvgAt 4 qsBigTriU 2 qsBigTriProbe qsBigOrigin 0
      ≠ stepBondAvgAtOrd 2 0 1 4 qsBigTriU 2 qsBigTriProbe qsBigOrigin 0 :=
  stepBondAvgAt_ne_ord_full_s4 (by decide) (by decide) (by decide) (by decide)

/-- Mutation E at `s = 4`. -/
theorem stepBondAvgAt_ne_ascOrder_full_s4 :
    stepBondAvgAt 4 qsBigTriU 2 qsBigTriProbe qsBigOrigin 0
      ≠ stepBondAvgAtAscOrder 4 qsBigTriU 2 qsBigTriProbe qsBigOrigin 0 := by
  rw [← stepBondAvgAtOrd_asc]
  exact stepBondAvgAt_ne_ord_full_s4 (by decide) (by decide) (by decide) (by decide)

theorem qsBigTriValue_real_ne_zero :
    stepBondAvgAt 4 qsBigTriU 2 qsBigTriProbe qsBigOrigin 0 ≠ 0 := by
  rw [qsBigTriValue_real]
  exact smul_neg_witness_ne_zero (by norm_num)

/-- The `s = 4` three-segment witness is a must-fire in its own right. -/
theorem stepBondAvgAt_bigTriWitness_mustfire :
    stepBondAvgAt 4 qsBigTriU 2 qsBigTriProbe qsBigOrigin 0
      ≠ stepBondAvgAt 4 (trivialU qsBigL) 2 qsBigTriProbe qsBigOrigin 0 := by
  have htriv : stepBondAvgAt 4 (trivialU qsBigL) 2 qsBigTriProbe qsBigOrigin 0
      = (1 / 16 : ℝ) • suTwoWitness := by
    unfold qsBigTriProbe stepBondAvgAt
    rw [farDelta_weighted_sum_base (by norm_num) qsBigFit qsBigTriRoom qsBigTri_mem_block
      qsBigTri_zero_val qsBigTriFar_mem suTwoWitness
      (fun x i => coarsePathHolonomy 4 (trivialU qsBigL) qsBigOrigin
        (coarseTransportPath 4 qsBigOrigin x 0 i)),
      farDelta_sum_two, coarsePathHolonomy_trivialU, RMap_one, LinearMap.id_apply]
    norm_num
  rw [qsBigTriValue_real, htriv]
  exact smul_neg_witness_ne (by norm_num)

end StraightLegOffAxisFull

end StraightLegTransport

/-! ## §10 — AXIOM AUDIT: every declaration in this module -/

#print axioms stepPathSite
#print axioms stepPathSite_zero
#print axioms stepPathSite_one_stride
#print axioms coarseShift_eq_pathSite
#print axioms stepPathSite_eq_endpoint
#print axioms stepPathSite_apply_ne
#print axioms stepPathSite_apply_self_val
#print axioms stepPathSite_injective
#print axioms coarseValAt
#print axioms coarseValAt_of_mem
#print axioms coarseValAt_of_not_mem
#print axioms coarseValAt_add
#print axioms coarseValAt_smul
#print axioms norm_coarseValAt_le
#print axioms mem_coarseLattice_one
#print axioms coarseValAt_one
#print axioms stepBlock_mem_coarseLattice
#print axioms stepPathSite_mem_coarseLattice
#print axioms stepBondAvgAt
#print axioms stepBondAvg
#print axioms stepBondAvgAt_add
#print axioms stepBondAvgAt_smul
#print axioms stepBondAvg_add
#print axioms stepBondAvg_smul
#print axioms stepBondAvgLM
#print axioms stepBondAvgLM_apply
#print axioms qStepCLM
#print axioms qStepCLM_apply
#print axioms coarsePathHolonomy_one_eq_periodic
#print axioms coarseGammaPath_one_map
#print axioms coarseTransportPath_one_map
#print axioms stepBondAvgAt_one_eq
#print axioms coarseBondOneEquiv
#print axioms stepBondAvg_one
#print axioms qCompositeCLM
#print axioms qCompositeCLM_zero
#print axioms qCompositeCLM_succ
#print axioms qCompositeCLM_succ_apply
#print axioms qCompositeCLM_one
#print axioms sum_coarseValAt_normSq
#print axioms block_sum_le_total
#print axioms norm_stepBondAvgAt_sq_le
#print axioms qStepCLM_normSq_le
#print axioms qStepCLM_opNorm_le
#print axioms stepBlockOf_covers
#print axioms stepBlockOf_pairwise_disjoint
#print axioms coarseLattice_eq_biUnion
#print axioms card_coarseLattice_step
#print axioms norm_const_sq
#print axioms qStepCLM_normSq_sharp
#print axioms qCompositeCLM_opNorm_le
#print axioms qStepStarLM
#print axioms qStepStarCLM
#print axioms qStepStarCLM_apply
#print axioms qStep_hadj
#print axioms stepLift
#print axioms stepLift_add
#print axioms stepLift_smul
#print axioms stepBondAvg_stepLift
#print axioms qStepCLM_surjective_trivialU
#print axioms qStepStar_injective_trivialU
#print axioms stepBlockOf_empty_of_mul_zero
#print axioms stepBondAvgAt_of_mul_zero
#print axioms stepBondAvgAt_const_trivialU
#print axioms qsWitL
#print axioms qsWitL_dvd_four
#print axioms qsOrigin
#print axioms qsOrigin_mem
#print axioms stepBondAvgAt_mustfire_s2
#print axioms stepBondAvgAt_genuinely_V_dependent
#print axioms coarseDelta
#print axioms stepBondAvgAt_cross_direction
#print axioms qCompositeCLM_two_strides
#print axioms qsWitL_dvd_upto_three
#print axioms qCompositeCLM_depth_three
#print axioms qsWitLbad
#print axioms qsWitLbad_not_dvd
#print axioms qsBadSite
#print axioms qsBadSite_mem
#print axioms stepPathSite_leaves_lattice
#print axioms coarseValAt_drops_without_dvd

#print axioms coarseCoordSteps_of_le
#print axioms coarseGammaPath_replicate_stride
#print axioms mul_lt_of_lt_stride
#print axioms stepPathSite_mem_stepBlock_of_lt
#print axioms stepPathSite_eq_far_iff
#print axioms coarseValAt_farDelta
#print axioms sum_range_ite_one_le
#print axioms farDelta_weighted_sum
#print axioms stepBondAvgAtNoTransport
#print axioms stepBondAvgAtGammaOnly
#print axioms stepBondAvgAt_farDelta_value
#print axioms stepBondAvgAtNoTransport_farDelta_value
#print axioms stepBondAvgAtGammaOnly_farDelta_value
#print axioms coarsePathHolonomy_replicate_one
#print axioms coarsePathHolonomy_replicate_two
#print axioms stepBondAvgAt_farDelta_value_two
#print axioms stepBondAvgAtNoTransport_farDelta_value_two
#print axioms stepBondAvgAtGammaOnly_farDelta_value_two
#print axioms smul_neg_witness_ne
#print axioms smul_neg_witness_ne_zero
#print axioms qsLegSite
#print axioms qsFarSite
#print axioms qsWitL_dvd_two
#print axioms qsOrigin_mem_two
#print axioms qsFarSite_mem
#print axioms qsFit
#print axioms qsRoom
#print axioms qsOrigin_ne_leg
#print axioms qsOrigin_ne_far
#print axioms qsLeg_ne_far
#print axioms qsLegU
#print axioms qsFarU
#print axioms qsCrossU
#print axioms qsProbe
#print axioms qsLegU_at_origin
#print axioms qsLegU_at_leg
#print axioms qsFarU_at_origin
#print axioms qsFarU_at_leg
#print axioms qsCrossU_at_origin
#print axioms qsCrossU_at_leg
#print axioms qsValue_legU
#print axioms qsValue_farU
#print axioms qsValue_crossU
#print axioms qsValue_trivialU
#print axioms qsValue_noTransport
#print axioms qsValue_gammaOnly
#print axioms qsValue_legU_ne_zero
#print axioms stepBondAvgAt_straightLeg_mustfire_s2
#print axioms stepBondAvgAt_ne_noTransport_s2
#print axioms stepBondAvgAt_ne_gammaOnly_s2
#print axioms stepBondAvgAt_leg_position_sensitive_s2
#print axioms stepBondAvgAt_leg_direction_sensitive_s2
#print axioms qsBigL
#print axioms qsBigOrigin
#print axioms qsBigLeg
#print axioms qsBigFar
#print axioms qsBigL_dvd_four
#print axioms qsBigOrigin_mem
#print axioms qsBigFar_mem
#print axioms qsBigFit
#print axioms qsBigRoom
#print axioms qsBigOrigin_ne_leg
#print axioms qsBigLegU
#print axioms qsBigProbe
#print axioms qsBigLegU_at_origin
#print axioms qsBigLegU_at_leg
#print axioms qsBigValue_legU
#print axioms qsBigValue_trivialU
#print axioms qsBigValue_noTransport
#print axioms qsBigValue_gammaOnly
#print axioms stepBondAvgAt_straightLeg_mustfire_s4
#print axioms stepBondAvgAt_ne_noTransport_s4
#print axioms stepBondAvgAt_ne_gammaOnly_s4

#print axioms coarseShift_stepPathSite
#print axioms coarsePathHolonomy_replicate_four
#print axioms qsBig4P1
#print axioms qsBig4P2
#print axioms qsBig4P3
#print axioms qsBig4Far
#print axioms qsBigL_dvd_two
#print axioms qsBigOrigin_mem_two
#print axioms qsBig4Far_mem
#print axioms qsBig4Fit
#print axioms qsBig4Room
#print axioms qsBigOrigin_ne_p2
#print axioms qsBig4P1_ne_p2
#print axioms qsBig4P3_ne_p2
#print axioms qsBig4U
#print axioms qsBig4Probe
#print axioms qsBig4U_at_origin
#print axioms qsBig4U_at_p1
#print axioms qsBig4U_at_p2
#print axioms qsBig4U_at_p3
#print axioms qsBig4Value_legU
#print axioms qsBig4Value_trivialU
#print axioms qsBig4Value_noTransport
#print axioms stepBondAvgAt_straightLeg_mustfire_ell4
#print axioms stepBondAvgAt_ne_noTransport_ell4
#print axioms stepBondAvgAtDropTerminal
#print axioms stepBondAvgAtDropTerminal_farDelta_value
#print axioms stepBondAvgAtDropTerminal_eq_gammaOnly_two
#print axioms coarsePathHolonomy_replicate_three
#print axioms qsBigOrigin_ne_p3
#print axioms qsBig4P1_ne_p3
#print axioms qsBig4P2_ne_p3
#print axioms qsBig4TermU
#print axioms qsBig4TermU_at_origin
#print axioms qsBig4TermU_at_p1
#print axioms qsBig4TermU_at_p2
#print axioms qsBig4TermU_at_p3
#print axioms qsBig4TermValue_legU
#print axioms qsBig4TermValue_dropTerminal
#print axioms qsBig4TermValue_trivialU
#print axioms qsBig4TermValue_noTransport
#print axioms qsBig4TermValue_gammaOnly
#print axioms qsBig4TrivialValue_dropTerminal
#print axioms qsBig4TermValue_legU_ne_zero
#print axioms stepBondAvgAt_ne_dropTerminal_ell4_terminal
#print axioms stepBondAvgAt_straightLeg_mustfire_ell4_terminal
#print axioms stepBondAvgAt_ne_noTransport_ell4_terminal
#print axioms stepBondAvgAt_ne_gammaOnly_ell4_terminal
#print axioms qsBig4Value_dropTerminal
#print axioms dropTerminal_cannot_separate_interior_ell4
#print axioms dropTerminal_survives_interior_mustfire
#print axioms stepBondAvgAt_ne_dropTerminal_s2
#print axioms stepBondAvgAt_ne_dropTerminal_s4
#print axioms stepPathSite_mem_stepBlock_of_base
#print axioms stepPathSite_eq_far_iff_base
#print axioms coarseValAt_farDelta_base
#print axioms farDelta_weighted_sum_base
#print axioms farDelta_sum_two
#print axioms coarseGammaPathAsc
#print axioms stepBondAvgAtAscOrder
#print axioms qsOrdA
#print axioms qsOrdX
#print axioms qsOrdFar
#print axioms qsLegSite_mem_coarse
#print axioms qsOrdFar_mem
#print axioms qsOrdRoom
#print axioms qsLeg_mem_block
#print axioms qsLeg_zero_val
#print axioms qsOrderU
#print axioms qsOrderProbe
#print axioms qsOrd_desc_path
#print axioms qsOrd_asc_path
#print axioms qsOrdShift_origin_two
#print axioms qsOrdShift_leg_zero
#print axioms qsOrdShift_origin_zero
#print axioms qsOrdShift_a_two
#print axioms qsOrderU_at_origin_two
#print axioms qsOrderU_at_leg_zero
#print axioms qsOrderU_at_x_zero
#print axioms qsOrderU_at_origin_zero
#print axioms qsOrderU_at_a_two
#print axioms qsOrderValue_real
#print axioms qsOrderValue_asc
#print axioms stepBondAvgAt_ne_ascOrder_offAxis
#print axioms qsOrderValue_real_ne_zero
#print axioms stepBondAvgAt_offAxis_mustfire

#print axioms coarseLinkList
#print axioms coarsePathHolonomy_eq_linkProd
#print axioms linkCount
#print axioms linkCount_eq_count
#print axioms markLinkU
#print axioms coarsePathHolonomy_markLinkU
#print axioms qsOrderU_eq_markLinkU
#print axioms coarseGammaPathOrd
#print axioms coarseGammaPathOrd_desc
#print axioms coarseGammaPathOrd_asc
#print axioms coarseGammaPathOrd_eq_replicates
#print axioms stepBondAvgAtOrd
#print axioms stepBondAvgAtOrd_desc
#print axioms stepBondAvgAtOrd_asc
#print axioms qsOrdX_middle_segment_empty
#print axioms ordX_ord201_path_eq_desc
#print axioms ordX_count_201
#print axioms stepBondAvgAtOrd201_eq_real_at_ordX
#print axioms qsTriBase
#print axioms qsTriX
#print axioms qsTriFar
#print axioms qsTriBase_mem_coarse
#print axioms qsTriFar_mem
#print axioms qsTri_mem_block
#print axioms qsTri_zero_val
#print axioms qsTri_all_three_segments
#print axioms qsTriU
#print axioms qsTriProbe
#print axioms qsTri_desc_links
#print axioms qsTri_ord201_links
#print axioms qsTriOrd_same_endpoint
#print axioms qsTriOrd_same_step_counts
#print axioms qsTriValue_ord
#print axioms qsTriCount_desc
#print axioms qsTriCount_zero_of_ne_desc
#print axioms qsTriValue_real
#print axioms qsTriValue_ord_of_ne_desc
#print axioms stepBondAvgAt_ne_ord_full
#print axioms stepBondAvgAt_ne_ord201_full
#print axioms stepBondAvgAt_ne_ord120_full
#print axioms stepBondAvgAt_ne_ord102_full
#print axioms stepBondAvgAt_ne_ord021_full
#print axioms stepBondAvgAt_ne_ascOrder_full
#print axioms qsTriValue_real_ne_zero
#print axioms stepBondAvgAt_triWitness_mustfire
#print axioms qsBigLeg_mem_coarse
#print axioms qsBigTriBase
#print axioms qsBigTriX
#print axioms qsBigTriFar
#print axioms qsBigTriBase_mem_coarse
#print axioms qsBigTriFar_mem
#print axioms qsBigTriRoom
#print axioms qsBigTri_mem_block
#print axioms qsBigTri_zero_val
#print axioms qsBigTri_all_three_segments
#print axioms qsBigTriU
#print axioms qsBigTriProbe
#print axioms qsBigTri_desc_links
#print axioms qsBigTriValue_ord
#print axioms qsBigTriCount_desc
#print axioms qsBigTriCount_zero_of_ne_desc
#print axioms qsBigTriValue_real
#print axioms stepBondAvgAt_ne_ord_full_s4
#print axioms stepBondAvgAt_ne_ord201_full_s4
#print axioms stepBondAvgAt_ne_ascOrder_full_s4
#print axioms qsBigTriValue_real_ne_zero
#print axioms stepBondAvgAt_bigTriWitness_mustfire

end AdalyFormal.Balaban.StridedAveraging
