/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.ThirdLevelStokes

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `ThirdLevelWitness.lean` — the NON-DEGENERATE-FIBRE witness: `Δ_k > 0` at `ℓ₀ = 2 < 4 = ℓ₁`

## What this module proves

`CStarLevelCorrected` §5's honest scope says, verbatim: *"a witness at `ℓ₀ ≥ 2` is the thing that
would demonstrate the repair, it is NOT established here, and §3b proves there is no way to it
that avoids §6's `[STOKES-COMM]`"*. `ThirdLevelStokes` closed `[STOKES-COMM]` at `U = 1`; this
module cashes it in:

* **§1 the dipole kernel certificate** (`Q_dipole_zero`), general: a two-bond `±` dipole whose
  transverse coordinate stays inside one `ℓ`-window on every coarse centre lies in `ker Q_ℓ`.
  This is the reusable `ker Q_ℓ`-membership TOOL (the witL5 module's `witChi` cancellation,
  generalized from `ℓ = 2`-specific site enumeration to every `ℓ`), plus the exact evaluation
  formula `Q_dipole_apply_dir` for the nonzero values.
* **§2 the witness**: on the torus `witL7` (`L μ = 7`: `4 ≤ 7`, `2 ∣ 8`, `4 ∣ 8` — BOTH levels
  compatible), the dipole `B7` with transverse coordinate values `1, 2`:
  - `1, 2` lie in the SAME level-4 window `{0,…,3}` ⇒ **`Q₄ B7 = 0`** — `B7` satisfies the
    (3.157)/(3.155) constraint `δ(Q₁B)` at the CONSTRAINT level `ℓ₁ = 4`;
  - `1, 2` lie in DIFFERENT level-2 windows `{0,1}`, `{2,3}` ⇒ **`Q₂ B7 ≠ 0`**, with the exact
    value `(1/16) • w` at the origin coarse bond and `−(1/16) • w` two steps up — so the coarse
    curl of `Q₂ B7` at the origin coarse plaquette is `(1/8) • w ≠ 0`.
* **§3 THE HEADLINE** (`third_level_nondegeneracy`): at the split `(ℓ₀, ℓ₁) = (2, 4)`,
  `B7 ∈ ker Q_{ℓ₁}`, `B7 ≠ 0`, the Schur fibre `V(ℓ₀ = 2)` is genuinely NONTRIVIAL
  (`V2_witL7_ne_bot` — the projection is over a NONZERO subspace, unlike `splitK0`'s `V = ⊥`;
  whether it removes nonzero energy at `B7`'s own curl is NOT claimed either way), and
  **`0 < deltaKCorr split24 … B7`** — via the Stokes factoring pair through
  `deltaKCorr_pos_of_factoring_witness`. This is the first strict positivity of the corrected
  `Δ_k` at a fibre level where the Schur mechanism actually acts.
* **§4 THE SEPARATION AT A NON-DEGENERATE LEVEL** (`collapsed_at_4_zero`): the SAME field at the
  COLLAPSED typing (fibre = constraint = 4) gives `deltaJ = 0` identically — the
  `[CSTAR-LEVEL-MISMATCH]` mechanism — while the split fibre 2 gives `> 0`. This strengthens
  `CStarLevelCorrected.level_split_separates`, whose split side sat at the degenerate `ℓ₀ = 1`
  (`V = ⊥`, class-5 degenerate test point); here BOTH sides are non-degenerate levels.
* **§5 exact energy**: `bondEnergy B7 = 2⟨w,w⟩`, consumed by `ThirdLevelSchurGap`'s quantitative
  instantiation.

## HONEST SCOPE

* `U = trivialU` (the `U = 1` base point of the perturbation program), `levels = oneLevelUniv`
  (which makes the `R`-clause vacuous — with a live `R` the subspace `V` shrinks and `Δ_k` only
  grows, so positivity persists; the collapsed-side `= 0` statements are `oneLevelUniv`-scoped).
* One explicit torus (`witL7`), one explicit split (`(2,4)`). The GENERAL-`ℓ` transfer machinery
  is in `ThirdLevelStokes` §6 / `ThirdLevelSchurGap`; this file is the non-vacuity anchor.
* No claim of the uniform coercivity target: this is a witness that the corrected object is NOT
  identically degenerate at a genuine Schur fibre — the property the refuted collapsed encoding
  provably lacked, now at a level where the projected subspace is nonzero.
-/

namespace AdalyFormal.Balaban.ThirdLevelWitness

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU oneLevelUniv RcovLM_oneLevelUniv_eq_zero
  periodicLatticeShiftBack deltaKernelImageCovH)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.Q1Real (rZeroA_trivialU)
open AdalyFormal.Balaban.RegularUDomainWitness (shift_eq_iff_shiftBack)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.CStarLevelCorrected (LevelSplit deltaKCorr
  deltaKCorr_pos_of_factoring_witness)
open AdalyFormal.Balaban.ThirdLevelStokes

variable {L : PeriodicLatticeExtent}

/-! ## §0 — backward paths -/

/-- `i` backward fine steps in direction `μ`. -/
def pathSiteBack (s : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) : PeriodicLatticeSite L :=
  (fun z => periodicLatticeShiftBack z μ)^[i] s

theorem pathSiteBack_zero (s : PeriodicLatticeSite L) (μ : Fin 3) : pathSiteBack s μ 0 = s := rfl

theorem pathSiteBack_succ' (s : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    pathSiteBack s μ (i + 1) = pathSiteBack (periodicLatticeShiftBack s μ) μ i :=
  Function.iterate_succ_apply _ i s

/-- Forward path hits `s` iff the start is the backward path from `s`. -/
theorem pathSite_eq_iff_back (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ∀ (i : ℕ) (s : PeriodicLatticeSite L), pathSite x μ i = s ↔ x = pathSiteBack s μ i := by
  intro i
  induction i with
  | zero =>
    intro s
    rw [pathSite_zero, pathSiteBack_zero]
  | succ n ih =>
    intro s
    rw [pathSite_succ, shift_eq_iff_shiftBack, ih (periodicLatticeShiftBack s μ),
      pathSiteBack_succ']

/-- A single backward step leaves every OTHER coordinate untouched. -/
theorem shiftBack_apply_ne (z : PeriodicLatticeSite L) {μ ρ : Fin 3} (h : ρ ≠ μ) :
    (periodicLatticeShiftBack z μ) ρ = z ρ := by
  unfold periodicLatticeShiftBack
  exact Function.update_of_ne h _ _

/-- The backward path leaves every other coordinate untouched. -/
theorem pathSiteBack_apply_ne {μ ρ : Fin 3} (h : ρ ≠ μ) :
    ∀ (i : ℕ) (s : PeriodicLatticeSite L), (pathSiteBack s μ i) ρ = s ρ := by
  intro i
  induction i with
  | zero => intro s; rw [pathSiteBack_zero]
  | succ n ih =>
    intro s
    rw [pathSiteBack_succ', ih, shiftBack_apply_ne _ h]

/-- Backward step commutes with an update in a DIFFERENT coordinate. -/
theorem shiftBack_update_comm (z : PeriodicLatticeSite L) {μ ν : Fin 3} (h : ν ≠ μ)
    (a : Fin (L ν + 1)) :
    periodicLatticeShiftBack (Function.update z ν a) μ
      = Function.update (periodicLatticeShiftBack z μ) ν a := by
  unfold periodicLatticeShiftBack
  rw [Function.update_of_ne (Ne.symm h), Function.update_comm h]

/-- Backward paths commute with an update in a different coordinate. -/
theorem pathSiteBack_update_comm {μ ν : Fin 3} (h : ν ≠ μ) (a : _) :
    ∀ (i : ℕ) (s : PeriodicLatticeSite L),
      pathSiteBack (Function.update s ν a) μ i = Function.update (pathSiteBack s μ i) ν a := by
  intro i
  induction i with
  | zero => intro s; rw [pathSiteBack_zero, pathSiteBack_zero]
  | succ n ih =>
    intro s
    rw [pathSiteBack_succ', shiftBack_update_comm _ h, ih, pathSiteBack_succ']

#print axioms pathSite_eq_iff_back
#print axioms pathSiteBack_apply_ne
#print axioms pathSiteBack_update_comm

/-! ## §1 — the dipole and its `Q_ℓ` values -/

/-- **The `±` dipole**: `+w` on `(s, μ)`, `−w` on `(s', μ)`, `0` elsewhere. -/
noncomputable def dipole (s s' : PeriodicLatticeSite L) (μ : Fin 3) (w : SuTwo) :
    Bond L → SuTwo :=
  fun e => ((if e = (s, μ) then (1 : ℝ) else 0) - (if e = (s', μ) then (1 : ℝ) else 0)) • w

/-- The dipole's value at its `+` bond, when the bonds differ. -/
theorem dipole_apply_plus {s s' : PeriodicLatticeSite L} (hne : s ≠ s') (μ : Fin 3) (w : SuTwo) :
    dipole s s' μ w (s, μ) = w := by
  unfold dipole
  rw [if_pos rfl, if_neg (by simp [Prod.mk.injEq, hne]), sub_zero, one_smul]

/-- **`Q_ℓ(dipole)` at an OFF-DIRECTION coarse bond is `0`** — the dipole is supported on
direction-`μ` bonds, and the line integral in direction `c.2 ≠ μ` never meets them. -/
theorem Q_dipole_apply_offdir (ell : ℕ) (s s' : PeriodicLatticeSite L) (μ : Fin 3) (w : SuTwo)
    (c : CoarseBond L ell) (hc : c.2 ≠ μ) :
    lineCoarseRestrictCovLM (trivialU L) ell (dipole s s' μ w) c = 0 := by
  rw [lineCoarseRestrictCovLM_apply]
  unfold lineCoarseRestrictCov
  rw [Finset.sum_congr rfl (fun x _ => rZeroA_trivialU c.1.1 x _ c.2 ell)]
  have hz : ∀ x : PeriodicLatticeSite L, ∀ i,
      dipole s s' μ w (pathSite x c.2 i, c.2) = 0 := by
    intro x i
    unfold dipole
    rw [if_neg (by simp [Prod.mk.injEq, hc]), if_neg (by simp [Prod.mk.injEq, hc]), sub_self,
      zero_smul]
  simp only [hz, Finset.sum_const_zero, smul_zero]

/-- **The exact `Q_ℓ(dipole)` value at an ALIGNED coarse bond**: the difference of the two
window-hit counts, each a sum over the `ℓ` backward offsets of a single block-membership
indicator. This is what makes concrete evaluation CHEAP: each indicator is one 3-coordinate
test, no enumeration of the block. -/
theorem Q_dipole_apply_dir (ell : ℕ) (s s' : PeriodicLatticeSite L) (μ : Fin 3) (w : SuTwo)
    (yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) :
    lineCoarseRestrictCovLM (trivialU L) ell (dipole s s' μ w) (yc, μ)
      = (1 / (ell : ℝ) ^ 4) •
          (((∑ i ∈ Finset.range ell,
              if pathSiteBack s μ i ∈ blockOf yc.1 ell then (1 : ℝ) else 0)
            - ∑ i ∈ Finset.range ell,
              if pathSiteBack s' μ i ∈ blockOf yc.1 ell then (1 : ℝ) else 0) • w) := by
  rw [lineCoarseRestrictCovLM_apply]
  unfold lineCoarseRestrictCov
  congr 1
  rw [Finset.sum_congr rfl (fun x _ => rZeroA_trivialU yc.1 x _ μ ell)]
  have hsummand : ∀ x : PeriodicLatticeSite L, ∀ i,
      dipole s s' μ w (pathSite x μ i, μ)
        = ((if pathSite x μ i = s then (1 : ℝ) else 0)
            - (if pathSite x μ i = s' then (1 : ℝ) else 0)) • w := by
    intro x i
    unfold dipole
    simp only [Prod.mk.injEq, eq_self_iff_true, and_true]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => hsummand x i))]
  simp only [← Finset.sum_smul]
  congr 1
  simp only [Finset.sum_sub_distrib]
  have hcount : ∀ t : PeriodicLatticeSite L,
      (∑ x ∈ blockOf yc.1 ell, ∑ i ∈ Finset.range ell,
          if pathSite x μ i = t then (1 : ℝ) else 0)
        = ∑ i ∈ Finset.range ell, if pathSiteBack t μ i ∈ blockOf yc.1 ell then (1 : ℝ) else 0 := by
    intro t
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl
      (fun x _ => if_congr (pathSite_eq_iff_back x μ i t) rfl rfl)]
    exact Finset.sum_ite_eq' _ _ _
  rw [hcount s, hcount s']

#print axioms Q_dipole_apply_offdir
#print axioms Q_dipole_apply_dir

/-- **THE DIPOLE KERNEL CERTIFICATE.** If the two sites agree off coordinate `ν ≠ μ` and their
`ν`-values are indistinguishable by every coarse `ℓ`-window, the dipole lies in `ker Q_ℓ(1)` —
for EVERY coarse bond simultaneously. The reusable `ker Q_ℓ` tool. -/
theorem Q_dipole_zero (ell : ℕ) {s s' : PeriodicLatticeSite L} {μ ν : Fin 3} (hνμ : ν ≠ μ)
    (hcoords : ∀ ρ : Fin 3, ρ ≠ ν → s ρ = s' ρ)
    (hwin : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      (((y ν).val ≤ (s ν).val ∧ (s ν).val < (y ν).val + ell) ↔
        ((y ν).val ≤ (s' ν).val ∧ (s' ν).val < (y ν).val + ell)))
    (w : SuTwo) :
    lineCoarseRestrictCovLM (trivialU L) ell (dipole s s' μ w) = 0 := by
  funext c
  rw [Pi.zero_apply]
  obtain ⟨yc, d⟩ := c
  rcases eq_or_ne d μ with hd | hd
  · subst hd
    rw [Q_dipole_apply_dir]
    have hs' : s' = Function.update s ν (s' ν) := by
      funext ρ
      rcases eq_or_ne ρ ν with rfl | hρ
      · rw [Function.update_self]
      · rw [Function.update_of_ne hρ]
        exact (hcoords ρ hρ).symm
    have hcnt : ∀ i, (pathSiteBack s d i ∈ blockOf yc.1 ell)
        ↔ (pathSiteBack s' d i ∈ blockOf yc.1 ell) := by
      intro i
      have hback : pathSiteBack s' d i
          = Function.update (pathSiteBack s d i) ν (s' ν) := by
        conv_lhs => rw [hs']
        rw [pathSiteBack_update_comm hνμ]
      rw [hback, mem_blockOf, mem_blockOf]
      constructor
      · intro h ρ
        rcases eq_or_ne ρ ν with rfl | hρ
        · rw [Function.update_self]
          have hν := h ρ
          rw [pathSiteBack_apply_ne hνμ] at hν
          exact (hwin yc.1 yc.2).mp hν
        · rw [Function.update_of_ne hρ]
          exact h ρ
      · intro h ρ
        rcases eq_or_ne ρ ν with rfl | hρ
        · have hν := h ρ
          rw [Function.update_self] at hν
          rw [pathSiteBack_apply_ne hνμ]
          exact (hwin yc.1 yc.2).mpr hν
        · have hρ' := h ρ
          rw [Function.update_of_ne hρ] at hρ'
          exact hρ'
    rw [Finset.sum_congr rfl (fun i _ => if_congr (hcnt i) rfl rfl), sub_self, zero_smul,
      smul_zero]
  · exact Q_dipole_apply_offdir ell s s' μ w (yc, d) hd

#print axioms Q_dipole_zero

/-! ## §2 — the witness torus and field -/

/-- `L μ = 7`: eight sites per axis — `4 ≤ 7`, and BOTH `2 ∣ 8` and `4 ∣ 8`, so both levels of
the split `(2,4)` have full, non-truncating blocks. -/
def witL7 : PeriodicLatticeExtent := fun _ => 7

theorem witL7_four_le : ∀ μ : Fin 3, 4 ≤ witL7 μ := by decide
theorem witL7_two_dvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (witL7 μ + 1) := by decide
theorem witL7_four_dvd : ∀ μ : Fin 3, (4 : ℕ) ∣ (witL7 μ + 1) := by decide

/-- `(0,0,0)`. -/
def s7Z : PeriodicLatticeSite witL7 := fun _ => 0
/-- `(0,1,0)` — transverse (coordinate-1) value `1`. -/
def s7P : PeriodicLatticeSite witL7 := fun ρ => if ρ = 1 then 1 else 0
/-- `(0,2,0)` — transverse value `2`: SAME level-4 window as `1`, DIFFERENT level-2 window. -/
def s7M : PeriodicLatticeSite witL7 := fun ρ => if ρ = 1 then 2 else 0

/-- **THE WITNESS FIELD**: `+w` at `((0,1,0),0)`, `−w` at `((0,2,0),0)`. -/
noncomputable def B7 : Bond witL7 → SuTwo := dipole s7P s7M 0 suTwoWitness

/-- The auxiliary fibre witness: transverse values `0, 1` — same level-2 window `{0,1}`. -/
noncomputable def B7' : Bond witL7 → SuTwo := dipole s7Z s7P 0 suTwoWitness

theorem s7P_ne_s7M : s7P ≠ s7M := by decide
theorem s7Z_ne_s7P : s7Z ≠ s7P := by decide

theorem B7_ne_zero : B7 ≠ 0 := by
  intro h
  have hb : B7 (s7P, 0) = 0 := by rw [h]; rfl
  rw [show B7 (s7P, 0) = suTwoWitness from dipole_apply_plus s7P_ne_s7M 0 suTwoWitness] at hb
  exact suTwoWitness_ne_zero hb

theorem B7'_ne_zero : B7' ≠ 0 := by
  intro h
  have hb : B7' (s7Z, 0) = 0 := by rw [h]; rfl
  rw [show B7' (s7Z, 0) = suTwoWitness from dipole_apply_plus s7Z_ne_s7P 0 suTwoWitness] at hb
  exact suTwoWitness_ne_zero hb

/-- **`B7` lies in the CONSTRAINT kernel `ker Q₄(1)`** — the transverse values `1, 2` share every
level-4 window (`{0,…,3}` vs `{4,…,7}`). This is the `δ(Q₁B)` membership at `ℓ₁ = 4`. -/
theorem B7_kerQ4 : lineCoarseRestrictCovLM (trivialU witL7) 4 B7 = 0 := by
  show lineCoarseRestrictCovLM (trivialU witL7) 4 (dipole s7P s7M 0 suTwoWitness) = 0
  refine Q_dipole_zero (ν := 1) 4 (by decide) (by decide) (fun y hy => ?_) suTwoWitness
  have h1 := mem_CoarseLattice.mp hy 1
  have h2 := (y 1).isLt
  have hsP : (s7P 1).val = 1 := rfl
  have hsM : (s7M 1).val = 2 := rfl
  rw [hsP, hsM]
  omega

/-- **`B7'` lies in `ker Q₂(1)`** — transverse values `0, 1` share every level-2 window. -/
theorem B7'_kerQ2 : lineCoarseRestrictCovLM (trivialU witL7) 2 B7' = 0 := by
  show lineCoarseRestrictCovLM (trivialU witL7) 2 (dipole s7Z s7P 0 suTwoWitness) = 0
  refine Q_dipole_zero (ν := 1) 2 (by decide) (by decide) (fun y hy => ?_) suTwoWitness
  have h1 := mem_CoarseLattice.mp hy 1
  have h2 := (y 1).isLt
  have hsZ : (s7Z 1).val = 0 := rfl
  have hsP : (s7P 1).val = 1 := rfl
  rw [hsZ, hsP]
  omega

#print axioms B7_kerQ4
#print axioms B7'_kerQ2

/-- **The Schur fibre at `ℓ₀ = 2` is GENUINELY NONTRIVIAL** on `witL7` — `B7'` is a nonzero
member. Unlike `splitK0` (`ℓ₀ = 1`, `V = ⊥`, the class-5 degenerate test point), the projection
in `Δ_k`'s Schur complement is over a nonzero subspace at this fibre (no claim is made about
its action on any particular field's curl). -/
theorem V2_witL7_ne_bot :
    gaugeConstraintSubspaceCovFaithful 2 (oneLevelUniv witL7) (trivialU witL7) ≠ ⊥ := by
  intro hbot
  have hmem : B7' ∈ gaugeConstraintSubspaceCovFaithful 2 (oneLevelUniv witL7) (trivialU witL7) :=
    mem_gaugeConstraintSubspaceCovFaithful.mpr
      ⟨B7'_kerQ2, RcovLM_oneLevelUniv_eq_zero (trivialU witL7) _⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact B7'_ne_zero hmem

#print axioms V2_witL7_ne_bot

/-! ## §2b — the exact `Q₂ B7` values at the four bonds of the origin coarse plaquette -/

/-- The origin. -/
def y70 : PeriodicLatticeSite witL7 := fun _ => 0

theorem y70_coarse2 : y70 ∈ CoarseLattice witL7 2 := by
  rw [mem_CoarseLattice]; decide

/-- The ordered direction pair `(0,1)`'s ordering proof, standardized so every statement uses
the SAME term. -/
theorem hlt01 : (0 : Fin 3) < 1 := by decide

/-- `Q₂ B7` at the origin direction-`0` coarse bond: **`(1/16) • w`**. Backward-offset test:
`(0,1,0) ∈ B((0,0,0))` at `i = 0` is the only hit. -/
theorem Q2_B7_origin :
    lineCoarseRestrictCovLM (trivialU witL7) 2 B7 ((⟨y70, y70_coarse2⟩, 0) : CoarseBond witL7 2)
      = (1 / 16 : ℝ) • suTwoWitness := by
  have hP0 : inBlock y70 2 (pathSiteBack s7P 0 0) := by decide
  have hP1 : ¬ inBlock y70 2 (pathSiteBack s7P 0 1) := by decide
  have hM0 : ¬ inBlock y70 2 (pathSiteBack s7M 0 0) := by decide
  have hM1 : ¬ inBlock y70 2 (pathSiteBack s7M 0 1) := by decide
  rw [show B7 = dipole s7P s7M 0 suTwoWitness from rfl, Q_dipole_apply_dir]
  rw [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_succ, Finset.sum_range_one]
  rw [if_pos (mem_blockOf.mpr hP0), if_neg (fun h => hP1 (mem_blockOf.mp h)),
    if_neg (fun h => hM0 (mem_blockOf.mp h)), if_neg (fun h => hM1 (mem_blockOf.mp h))]
  rw [smul_smul]
  congr 1
  norm_num

/-- `Q₂ B7` at the direction-`0` coarse bond two steps up in direction `1` (the bond
`coarseCurlSuTwo` reads with a minus sign): **`−(1/16) • w`** — only `s7M = (0,2,0)` hits the
window `B((0,2,0))`. Stated with an ARBITRARY membership proof so it rewrites against the exact
subtype element `coarseCurlSuTwo` produces (proof irrelevance). -/
theorem Q2_B7_shifted (hmem : AdalyFormal.Balaban.CoarseCurl.coarseShift y70 2 1
      ∈ CoarseLattice witL7 2) :
    lineCoarseRestrictCovLM (trivialU witL7) 2 B7
        ((⟨AdalyFormal.Balaban.CoarseCurl.coarseShift y70 2 1, hmem⟩, 0) : CoarseBond witL7 2)
      = -((1 / 16 : ℝ) • suTwoWitness) := by
  have hP0 : ¬ inBlock (AdalyFormal.Balaban.CoarseCurl.coarseShift y70 2 1) 2
      (pathSiteBack s7P 0 0) := by decide
  have hP1 : ¬ inBlock (AdalyFormal.Balaban.CoarseCurl.coarseShift y70 2 1) 2
      (pathSiteBack s7P 0 1) := by decide
  have hM0 : inBlock (AdalyFormal.Balaban.CoarseCurl.coarseShift y70 2 1) 2
      (pathSiteBack s7M 0 0) := by decide
  have hM1 : ¬ inBlock (AdalyFormal.Balaban.CoarseCurl.coarseShift y70 2 1) 2
      (pathSiteBack s7M 0 1) := by decide
  rw [show B7 = dipole s7P s7M 0 suTwoWitness from rfl, Q_dipole_apply_dir]
  rw [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_succ, Finset.sum_range_one]
  rw [if_neg (fun h => hP0 (mem_blockOf.mp h)), if_neg (fun h => hP1 (mem_blockOf.mp h)),
    if_pos (mem_blockOf.mpr hM0), if_neg (fun h => hM1 (mem_blockOf.mp h))]
  rw [smul_smul, ← neg_smul]
  congr 1
  norm_num

/-- **`Q₂ B7 ≠ 0`** — the same field that IS in `ker Q₄`. The two levels genuinely separate on
`B7`: `ker Q_{ℓ₁} ⊄ ker Q_{ℓ₀}`. -/
theorem B7_not_kerQ2 : lineCoarseRestrictCovLM (trivialU witL7) 2 B7 ≠ 0 := by
  intro h
  have h0 := congrFun h ((⟨y70, y70_coarse2⟩, 0) : CoarseBond witL7 2)
  rw [Q2_B7_origin, Pi.zero_apply] at h0
  have : suTwoWitness = 0 := by
    have h16 : (16 : ℝ) • ((1 / 16 : ℝ) • suTwoWitness) = (16 : ℝ) • (0 : SuTwo) := by rw [h0]
    rwa [smul_smul, smul_zero, show (16 : ℝ) * (1 / 16) = 1 by norm_num, one_smul] at h16
  exact suTwoWitness_ne_zero this

#print axioms Q2_B7_origin
#print axioms Q2_B7_shifted
#print axioms B7_not_kerQ2

/-- The four-term expansion of `coarseCurlSuTwo`, with ARBITRARY membership proofs for the two
shifted subtype elements — `rfl` by definitional proof irrelevance, so callers can supply the
proofs they can compute with. -/
theorem coarseCurlSuTwo_apply {L : PeriodicLatticeExtent} {ell : ℕ}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : CoarseBond L ell → SuTwo)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) {μ ν : Fin 3} (hlt : μ < ν)
    (h1 : AdalyFormal.Balaban.CoarseCurl.coarseShift y ell μ ∈ CoarseLattice L ell)
    (h2 : AdalyFormal.Balaban.CoarseCurl.coarseShift y ell ν ∈ CoarseLattice L ell) :
    coarseCurlSuTwo hdvd B
        ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : AdalyFormal.Balaban.CoarseCurl.CoarsePlaquette L ell)
      = B (⟨y, hy⟩, μ)
        + B (⟨AdalyFormal.Balaban.CoarseCurl.coarseShift y ell μ, h1⟩, ν)
        - B (⟨AdalyFormal.Balaban.CoarseCurl.coarseShift y ell ν, h2⟩, μ)
        - B (⟨y, hy⟩, ν) := rfl

/-- Direction fact reused below. -/
theorem one_ne_zero_fin3 : (1 : Fin 3) ≠ 0 := by decide

theorem y70_shift0_coarse :
    AdalyFormal.Balaban.CoarseCurl.coarseShift y70 2 0 ∈ CoarseLattice witL7 2 := by
  rw [mem_CoarseLattice]; decide

theorem y70_shift1_coarse :
    AdalyFormal.Balaban.CoarseCurl.coarseShift y70 2 1 ∈ CoarseLattice witL7 2 := by
  rw [mem_CoarseLattice]; decide

/-- **The coarse curl of `Q₂ B7` at the origin coarse plaquette is `(1/8) • w`** — the four-term
combination: `(1/16)w + 0 − (−(1/16)w) − 0`. The direction-`1` bonds contribute `0` because the
dipole is direction-`0`-supported. -/
theorem coarseCurl_Q2_B7 :
    coarseCurlSuTwo witL7_two_dvd (lineCoarseRestrictCovLM (trivialU witL7) 2 B7)
        ((⟨y70, y70_coarse2⟩, ⟨(0, 1), hlt01⟩) :
          AdalyFormal.Balaban.CoarseCurl.CoarsePlaquette witL7 2)
      = (1 / 8 : ℝ) • suTwoWitness := by
  rw [coarseCurlSuTwo_apply witL7_two_dvd _ y70_coarse2 hlt01 y70_shift0_coarse
    y70_shift1_coarse]
  rw [Q2_B7_origin, Q2_B7_shifted y70_shift1_coarse,
    show lineCoarseRestrictCovLM (trivialU witL7) 2 B7
        ((⟨AdalyFormal.Balaban.CoarseCurl.coarseShift y70 2 0, y70_shift0_coarse⟩, 1) :
          CoarseBond witL7 2) = 0 from
      Q_dipole_apply_offdir 2 s7P s7M 0 suTwoWitness _ one_ne_zero_fin3,
    show lineCoarseRestrictCovLM (trivialU witL7) 2 B7
        ((⟨y70, y70_coarse2⟩, 1) : CoarseBond witL7 2) = 0 from
      Q_dipole_apply_offdir 2 s7P s7M 0 suTwoWitness _ one_ne_zero_fin3]
  rw [add_zero, sub_neg_eq_add, sub_zero, ← add_smul]
  norm_num

#print axioms coarseCurl_Q2_B7

/-! ## §3 — THE HEADLINE: strict positivity at the non-degenerate split `(2, 4)` -/

/-- The split `(ℓ₀, ℓ₁) = (2, 4)`. -/
def split24 : LevelSplit := ⟨2, 4, by norm_num, ⟨2, rfl⟩, by norm_num⟩

theorem split24_fibre : split24.fibre = 2 := rfl
theorem split24_constr : split24.constr = 4 := rfl

/-- `0 < ⟨w,w⟩` for the su(2) witness. -/
theorem hsInner_witness_pos : 0 < hsInner suTwoWitness suTwoWitness := by
  rcases lt_or_eq_of_le (hsInner_self_nonneg suTwoWitness) with h | h
  · exact h
  · exact absurd (hsInner_self_eq_zero h.symm) suTwoWitness_ne_zero

/-- The Stokes functional does NOT vanish on `Q₂ B7`: its value is `2⟨w,w⟩ > 0`. -/
theorem phi_Q2_B7_pos :
    0 < stokesPhi 2 witL7_two_dvd y70_coarse2 hlt01 suTwoWitness
        (lineCoarseRestrictCovLM (trivialU witL7) 2 B7) := by
  rw [stokesPhi_apply, coarseCurl_Q2_B7, hsInner_smul_right]
  have h := hsInner_witness_pos
  nlinarith

/-- **THE POSITIVITY.** At the split `(2, 4)`, on the constraint-kernel field `B7`
(`Q₄ B7 = 0`), the corrected `Δ_k` — the Schur complement over the GENUINELY NONTRIVIAL fibre
`V(2)` — is strictly positive. Route: the `[STOKES-COMM]` factoring pair through
`deltaKCorr_pos_of_factoring_witness`. -/
theorem third_level_positivity :
    0 < deltaKCorr split24 (oneLevelUniv witL7) (trivialU witL7) B7 := by
  refine deltaKCorr_pos_of_factoring_witness split24 (oneLevelUniv witL7) (trivialU witL7) B7
    (stokesU 2 y70 hlt01 suTwoWitness)
    (stokesPhi 2 witL7_two_dvd y70_coarse2 hlt01 suTwoWitness)
    (fun v => ?_) (ne_of_gt phi_Q2_B7_pos)
  exact stokes_factoring (by norm_num) witL7_two_dvd y70_coarse2 hlt01 suTwoWitness v

#print axioms third_level_positivity

/-- **THE DELIVERABLE, assembled**: at `(ℓ₀, ℓ₁) = (2, 4)` on `witL7`, `U = 1`:
constraint membership at `ℓ₁`, nonzero field, nontrivial Schur fibre at `ℓ₀`, and strict
positivity of the corrected `Δ_k`. Every object named, no existential over free data (S91). -/
theorem third_level_nondegeneracy :
    lineCoarseRestrictCovLM (trivialU witL7) 4 B7 = 0
  ∧ B7 ≠ 0
  ∧ gaugeConstraintSubspaceCovFaithful 2 (oneLevelUniv witL7) (trivialU witL7) ≠ ⊥
  ∧ 0 < deltaKCorr split24 (oneLevelUniv witL7) (trivialU witL7) B7 :=
  ⟨B7_kerQ4, B7_ne_zero, V2_witL7_ne_bot, third_level_positivity⟩

#print axioms third_level_nondegeneracy

/-! ## §4 — THE SEPARATION at a NON-degenerate level (the collapsed side, for contrast) -/

/-- **The COLLAPSED typing kills the very same field**: at fibre level 4 (= the constraint
level), `B7 ∈ V(4)` and the Schur form vanishes identically. Same field, same background, same
`levels`; only the fibre level moves `4 → 2`, and the value moves `0 → (> 0)`. This is
`[CSTAR-LEVEL-MISMATCH]` isolated at a level where the fibre is nontrivial on BOTH sides —
strengthening `CStarLevelCorrected.level_split_separates`, whose split side sat at the
degenerate `ℓ₀ = 1`. -/
theorem collapsed_at_4_zero :
    deltaJQuadFormCovFaithful 4 (oneLevelUniv witL7) (trivialU witL7) B7 = 0 :=
  deltaJQuadFormCovFaithful_eq_zero_of_mem_V 4 (oneLevelUniv witL7) (trivialU witL7) B7
    (mem_gaugeConstraintSubspaceCovFaithful.mpr
      ⟨B7_kerQ4, RcovLM_oneLevelUniv_eq_zero (trivialU witL7) _⟩)

/-- The two sides, juxtaposed. -/
theorem third_level_separation :
    deltaJQuadFormCovFaithful 4 (oneLevelUniv witL7) (trivialU witL7) B7 = 0
  ∧ 0 < deltaJQuadFormCovFaithful 2 (oneLevelUniv witL7) (trivialU witL7) B7 :=
  ⟨collapsed_at_4_zero, third_level_positivity⟩

#print axioms collapsed_at_4_zero
#print axioms third_level_separation

/-! ## §5 — exact energy of the witness -/

/-- `bondEnergy B7 = 2⟨w,w⟩` — exactly two unit-coefficient bonds. -/
theorem bondEnergy_B7 : bondEnergy B7 = 2 * hsInner suTwoWitness suTwoWitness := by
  unfold bondEnergy
  have hterm : ∀ e : Bond witL7,
      ‖B7 e‖ ^ 2 = ((if e = ((s7P, 0) : Bond witL7) then (1 : ℝ) else 0)
        + (if e = ((s7M, 0) : Bond witL7) then (1 : ℝ) else 0)) * hsInner suTwoWitness suTwoWitness := by
    intro e
    have hB : B7 e = ((if e = ((s7P, 0) : Bond witL7) then (1 : ℝ) else 0)
        - (if e = ((s7M, 0) : Bond witL7) then (1 : ℝ) else 0)) • suTwoWitness := rfl
    have hnorm : ‖suTwoWitness‖ ^ 2 = hsInner suTwoWitness suTwoWitness := by
      rw [← inner_eq_hsInner, real_inner_self_eq_norm_sq]
    rw [hB, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hnorm]
    congr 1
    by_cases hP : e = ((s7P, 0) : Bond witL7)
    · have hM : e ≠ ((s7M, 0) : Bond witL7) := by
        rw [hP]
        simp [Prod.mk.injEq, s7P_ne_s7M]
      norm_num [hP, hM, s7P_ne_s7M]
    · by_cases hM : e = ((s7M, 0) : Bond witL7)
      · norm_num [hP, hM, Ne.symm s7P_ne_s7M]
      · norm_num [hP, hM]
  rw [Finset.sum_congr rfl (fun e _ => hterm e)]
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ ((s7P, 0) : Bond witL7)
    (fun _ => (1 : ℝ)), Finset.sum_ite_eq' Finset.univ ((s7M, 0) : Bond witL7)
    (fun _ => (1 : ℝ))]
  rw [if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  norm_num

#print axioms bondEnergy_B7

end AdalyFormal.Balaban.ThirdLevelWitness
