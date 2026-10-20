/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.ThirdLevelSchurGap

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `ThirdLevelSandwich.lean` — `[SANDWICH-WITNESS]` CLOSED: the witness reaches the `C*Δ_kC`
sandwich itself

`ThirdLevelSchurGap` §Named-residuals left one gap between the witness and the corrected TARGET:
`B7` certifies `Δ_k > 0` on the (3.157) constraint kernel, but the target
`LevelCorrectedCoercivityTargetUniform` is phrased through the sandwich
`cStarDeltaKCFormCorr S … Dinv B̃ = ⟨B̃, C*Δ_kC B̃⟩`, so the witness must be exhibited IN the
range of the (3.157) reparametrization `C`. This module closes that gap:

* `B7_no_dropped` — `B7` vanishes on every level-4 dropped bond (its bonds sit at fine offset
  `0`, dropped bonds at offset `3 mod 4`).
* **`fullC_fixes_B7`** — `C(B7) = B7` for the canonical `C = fullC (dinvC)` at the constraint
  level `4`: since `B7` already satisfies every constraint (`Q₄B7 = 0`) and carries `0` on every
  dropped bond, each per-bond solve returns `0` (`solvedValue = −Dinv c (Q₄(B7)(c)) = 0`). So
  `B7` IS a point of the free-coordinate parametrization, with `B̃ = B7`.
* **`sandwich_positivity`** — `0 < ⟨B7, C*Δ_kC B7⟩` at the split `(2,4)`: the corrected
  SANDWICH itself is strictly positive at the witness — the exact quantity the refuted collapsed
  encoding (`cStarDeltaKC_coercivity_refuted`) proved is identically `0` in the one-level typing,
  now strictly positive in the two-level typing, at a non-degenerate fibre.
* **`sandwich_energy_bound`** — quantitatively: `(1/64)·bondEnergy B7 ≤ ⟨B7, C*Δ_kC B7⟩`.
  Together with `bondEnergy_B7 = 2⟨w,w⟩ > 0` this is a strictly positive coercivity ratio at
  the witness point of the corrected target's own functional.

Scope: `U = 1`, `levels = oneLevelUniv`, the explicit torus/split of `ThirdLevelWitness` —
inherited, disclosed there. This is an INSTANCE of the target's inequality shape at one point,
not the uniform target.
-/

namespace AdalyFormal.Balaban.ThirdLevelSandwich

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU oneLevelUniv)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ReparamCSuTwo (restFunctional constraintFunctional
  constraintFunctional_apply dropZero dropZero_apply)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast pathSite_apply_self_val)
open AdalyFormal.Balaban.FullReparamC (IsDropped fullC fullC_free fullC_dropped solvedValue
  dinvC)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.CStarLevelCorrected (deltaKCorr cStarDeltaKCFormCorr)
open AdalyFormal.Balaban.ThirdLevelWitness
open AdalyFormal.Balaban.ThirdLevelSchurGap (third_level_energy_bound)

/-! ## §1 — `B7` vanishes on every level-4 dropped bond -/

/-- No level-4 dropped bond is a direction-`0` bond whose base has fine offset `0` in
direction `0`: dropped bases sit at offset `3 mod 4`. -/
theorem droppedBond4_ne (c : CoarseBond witL7 4) (s : PeriodicLatticeSite witL7)
    (hs : (s 0).val = 0) : droppedBondLast 4 c ≠ ((s, 0) : Bond witL7) := by
  intro heq
  have hdir : c.2 = 0 := congrArg Prod.snd heq
  have hsite : (droppedBondLast 4 c).1 = s := congrArg Prod.fst heq
  have h0 : ((droppedBondLast 4 c).1 0).val = (((c.1.1 0).val + 3) % 8) := by
    show ((pathSite c.1.1 c.2 3) 0).val = _
    rw [hdir]
    exact pathSite_apply_self_val c.1.1 0 3
  have hc := mem_CoarseLattice.mp c.1.2 0
  have hlt := (c.1.1 0).isLt
  rw [hsite, hs] at h0
  have hlt' : (c.1.1 0).val < 8 := hlt
  omega

theorem s7P_coord0 : ((s7P 0).val = 0) := rfl
theorem s7M_coord0 : ((s7M 0).val = 0) := rfl

/-- `B7` vanishes on every level-4 dropped bond. -/
theorem B7_no_dropped : ∀ c : CoarseBond witL7 4, B7 (droppedBondLast 4 c) = 0 := by
  intro c
  show dipole s7P s7M 0 suTwoWitness (droppedBondLast 4 c) = 0
  unfold dipole
  rw [if_neg (droppedBond4_ne c s7P s7P_coord0), if_neg (droppedBond4_ne c s7M s7M_coord0),
    sub_self, zero_smul]

#print axioms B7_no_dropped

/-! ## §2 — the reparametrization FIXES `B7` -/

/-- Zeroing a slot `B7` already vanishes on is a no-op. -/
theorem dropZero_B7 (c : CoarseBond witL7 4) :
    dropZero (droppedBondLast 4 c) B7 = B7 := by
  funext b
  rw [dropZero_apply]
  by_cases hb : b = droppedBondLast 4 c
  · rw [if_pos hb, hb, B7_no_dropped c]
  · rw [if_neg hb]

/-- **`C(B7) = B7`**: the per-bond solve returns `0` on every dropped bond because `B7` already
satisfies every level-4 constraint with `0` in every dropped slot. -/
theorem fullC_fixes_B7 :
    fullC (trivialU witL7) 4 (dinvC (trivialU witL7) 4) B7 = B7 := by
  funext b
  by_cases hd : IsDropped 4 b
  · obtain ⟨c, rfl⟩ := hd
    rw [fullC_dropped (by norm_num) witL7_four_dvd (trivialU witL7)
      (dinvC (trivialU witL7) 4) B7 c, B7_no_dropped c]
    show -(dinvC (trivialU witL7) 4 c
      (restFunctional (trivialU witL7) 4 c (droppedBondLast 4 c) B7)) = 0
    have hrest : restFunctional (trivialU witL7) 4 c (droppedBondLast 4 c) B7 = 0 := by
      show constraintFunctional (trivialU witL7) 4 c (dropZero (droppedBondLast 4 c) B7) = 0
      rw [dropZero_B7 c, constraintFunctional_apply]
      have h := congrFun B7_kerQ4 c
      rwa [lineCoarseRestrictCovLM_apply, Pi.zero_apply] at h
    rw [hrest, map_zero, neg_zero]
  · exact fullC_free (trivialU witL7) (dinvC (trivialU witL7) 4) B7 hd

#print axioms fullC_fixes_B7

/-! ## §3 — the SANDWICH itself is positive at the witness -/

/-- **`0 < ⟨B7, C*Δ_kC B7⟩` at the split `(2,4)`** — the corrected sandwich
(`cStarDeltaKCFormCorr`, `C` at level 4, `Δ_k`'s fibre at level 2) is strictly positive at the
free-coordinate point `B̃ = B7`. The quantity that is IDENTICALLY ZERO in the collapsed typing
(`cStarDeltaKC_coercivity_refuted`) is strictly positive in the corrected one, at a fibre where
the Schur projection is over a nonzero subspace (`V2_witL7_ne_bot`). -/
theorem sandwich_positivity :
    0 < cStarDeltaKCFormCorr split24 (oneLevelUniv witL7) (trivialU witL7)
        (dinvC (trivialU witL7) 4) B7 := by
  show 0 < deltaKCorr split24 (oneLevelUniv witL7) (trivialU witL7)
    (fullC (trivialU witL7) 4 (dinvC (trivialU witL7) 4) B7)
  rw [fullC_fixes_B7]
  exact third_level_positivity

/-- **The quantitative sandwich bound**: `(1/64) · bondEnergy B7 ≤ ⟨B7, C*Δ_kC B7⟩`. -/
theorem sandwich_energy_bound :
    (1 / 64 : ℝ) * bondEnergy B7
      ≤ cStarDeltaKCFormCorr split24 (oneLevelUniv witL7) (trivialU witL7)
          (dinvC (trivialU witL7) 4) B7 := by
  show (1 / 64 : ℝ) * bondEnergy B7 ≤ deltaKCorr split24 (oneLevelUniv witL7) (trivialU witL7)
    (fullC (trivialU witL7) 4 (dinvC (trivialU witL7) 4) B7)
  rw [fullC_fixes_B7]
  exact third_level_energy_bound

#print axioms sandwich_positivity
#print axioms sandwich_energy_bound

end AdalyFormal.Balaban.ThirdLevelSandwich
