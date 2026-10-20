/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.WitnessInequality
import AdalyFormal.Balaban.StokesCommU

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `NilLevelTarget.lean` — the `levels = []` RESTRICTION of the level-corrected target, tested

`WitnessInequality.target_refuted` refuted
`ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform`
at `levels = oneLevelUniv`, by a RATE failure (`768 · ell^{-3}` against a fixed left-hand side). The
dispatched question: does restricting `levels` to `[]` — the one value at which the tree's
general-`U` machinery COMPOSES (`StokesCommU`) rather than being obstructed — repair it?

**It does not, and the reason is not the rate.** This file states the `[]` restriction (and, more
generally, the restriction along an ARBITRARY selector `choose : (L) → List (Level L)`) and refutes
every one of them at once, by a mechanism that is uniform in `levels`:

**The target's admissible-`B̃` class intersects the FIBRE.** A single plaquette loop field,
placed inside a fibre block, satisfies both of the target's `B̃` clauses at the CONSTRAINT level
and lies in the fibre `V(U) = ker Q_{S.fibre}(U) ∩ {R^{cov}(D*_U ·) = 0}` at the FIBRE level. For
such a `B̃`, `fullC B̃ = B̃` and the Schur complement — a DISTANCE from `D_U B̃` to `D_U(V)` — is
exactly `0`, while `bondEnergy B̃ > 0`. (An earlier draft of this sentence read
`bondEnergy B̃ = 4‖suTwoWitness‖²`; that VALUE is not computed by any declaration here and the
number is struck. `bondEnergy_loopField_pos` proves the strict positivity, which is all the
refutation consumes.)

## The four facts that make the loop work (each a theorem below, none assumed)

1. `loopField_div_eq_zero` — the loop is annihilated by `D*_U` at `U = 1`. Because the fibre's
   SECOND clause is `RcovLM U levels (D*_U ·) = 0` and `RcovLM` is linear, `D*_U B̃ = 0` discharges
   that clause for **EVERY** `levels` — `[]`, `oneLevelUniv`, and everything else. This is why no
   restriction of `levels` can repair the statement: the counterexample never touches `levels`.
2. `Q_loopField_fibre` — the loop is annihilated by `Q_{S.fibre}`. Its two same-direction spikes
   differ in a TRANSVERSE coordinate whose two values (`0` and `1`) are never separated by a fibre
   block (blocks start at `0` or `ell`, and `ell ≥ 3`), so the two block-counts of
   `Q_single_same_dir` are equal and cancel.
3. `Q_loopField_constr` — the loop is annihilated by `Q_{S.constr}`, which at this extent is the
   plain torus average (`WitnessInequality.Q_full`): each direction's two spikes have opposite sign.
   Hence `solvedValue = 0` and `fullC_loopField : fullC B̃ = B̃`.
4. `loopField_axial` / `loopField_dropped` — the loop's four bonds are off the constraint-level
   axial staircase and are not dropped bonds. Read from `AdmissibleSubspace.staircasePath`'s own
   definition: from `y`, the three segments are direction `2` at `(y₀,y₁,·)`, direction `1` at
   `(y₀,·,x₂)`, direction `0` at `(·,x₁,x₂)`. So every direction-`1` or direction-`2` staircase bond
   has base coordinate `0` equal to `y₀ = 0`, while all four loop bonds have base coordinate `0`
   equal to `1`; and the loop uses no direction-`0` bond at all. The three dropped bonds have base
   coordinate `0` in `{0, 2·ell − 1}`.

## What is PROVED here, and what is not

* PROVED: `targetAt_refuted` — for EVERY selector `choose`, `LevelCorrectedCoercivityTargetAt
  choose` is false. `nil_target_refuted` is the `choose = fun _ => []` instance.
* PROVED: `targetFibreClauses_refuted` — the OBVIOUS repair fails too. Moving the two `B̃`
  admissibility clauses from `S.constr` to `S.fibre` leaves the SAME datum admissible, so the
  axial-gauge-plus-dropped-bond class fails to exclude fibre elements at EITHER level.
* PROVED: `uniform_target_refuted` — a second, independent refutation of
  `ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform` (the `∀ levels` form), by VANISHING
  rather than by rate, at a single fixed `m` with no large-`ell` limit.
* NOT claimed: nothing here is a statement about CMP99b p.428 or about Bałaban's Lemma. It is a
  fact about one formal encoding — specifically about the interaction between the level at which
  `cStarDeltaKCFormCorr`'s admissibility clauses are imposed (`S.constr`) and the level at which its
  fibre is taken (`S.fibre`).
* NOT claimed: this does not say the `1/ell⁴` normalisation of `Q` is right or wrong. It says the
  `levels` quantifier is not where this encoding's defect lives — a strictly different finding from
  `WitnessInequality`'s, and the two are consistent (both bound the same right-hand side above).
* OFF-SPINE: `ThirdLevelSchurGap`, `WitnessInequality`, `StokesCommU` and this module are all
  unreachable from `AdalyFormal.lean` and from `Spine.lean`. Nothing here moves a milestone.
-/

namespace AdalyFormal.Balaban.NilLevelTarget

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU deltaKernelImageCovH RcovLM
  gradCovariantAdjointValue gradCovariantAdjointLM gradCovariantAdjointLM_apply
  periodicLatticeShiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast pathSite_apply_ne
  pathSite_apply_self_val)
open AdalyFormal.Balaban.ReparamCSuTwo (coeffDc)
open AdalyFormal.Balaban.FullySupplied (restFunctional_eq)
open AdalyFormal.Balaban.FullReparamC (fullC fullC_free fullC_dropped dinvC dinvC_hinv solvedValue
  IsDropped)
open AdalyFormal.Balaban.CStarLevelCorrected (LevelSplit deltaKCorr cStarDeltaKCFormCorr)
open AdalyFormal.Balaban.RegularUDomainWitness (shift_eq_iff_shiftBack)
open AdalyFormal.Balaban.WitnessInequality (wExt wEll wExt_succ wEll_pos wEll_three wConstr_pos
  wExt_four wEll_dvd wConstr_dvd wSplit Q_full coarse_at_full_val coarse_at_fibre_val
  Q_single_same_dir Q_single_other_dir deltaJQuadFormCovFaithful_le_of_sub)

/-! ## §1 — the four sites of one plaquette, deep inside a fibre block -/

private theorem lt_ext (m : ℕ) (μ : Fin 3) {k : ℕ} (h : k ≤ 2) : k < wExt m μ + 1 := by
  simp only [wExt]; omega

/-- `pA = (1,0,0)` — the base site of the plaquette. Coordinate `0` is `1`, which is what keeps all
four of its bonds off the constraint-level axial staircase (every direction-`1`/`2` staircase bond
has base coordinate `0` equal to the coarse site's, i.e. `0`). -/
def pA (m : ℕ) : PeriodicLatticeSite (wExt m) :=
  fun μ => if μ = 0 then ⟨1, lt_ext m μ (by norm_num)⟩ else ⟨0, lt_ext m μ (by norm_num)⟩

/-- `pB = pA + e₁ = (1,1,0)`. -/
def pB (m : ℕ) : PeriodicLatticeSite (wExt m) := periodicLatticeShift (pA m) 1

/-- `pC = pA + e₂ = (1,0,1)`. -/
def pC (m : ℕ) : PeriodicLatticeSite (wExt m) := periodicLatticeShift (pA m) 2

/-- `pD = pA + e₁ + e₂ = (1,1,1)`, the far corner. -/
def pD (m : ℕ) : PeriodicLatticeSite (wExt m) := periodicLatticeShift (pB m) 2

private theorem shift_eq_pathSite_one {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (μ : Fin 3) : periodicLatticeShift x μ = pathSite x μ 1 := by
  rw [pathSite_succ, pathSite_zero]

private theorem shift_val_self {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3)
    (h : (x μ).val + 1 < L μ + 1) :
    ((periodicLatticeShift x μ) μ).val = (x μ).val + 1 := by
  rw [shift_eq_pathSite_one, pathSite_apply_self_val, Nat.mod_eq_of_lt h]

private theorem shift_val_ne {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ ν : Fin 3)
    (h : ν ≠ μ) : (periodicLatticeShift x μ) ν = x ν := Function.update_of_ne h _ _

theorem pA_c0 (m : ℕ) : ((pA m) 0).val = 1 := by simp [pA]
theorem pA_c1 (m : ℕ) : ((pA m) 1).val = 0 := by simp [pA]
theorem pA_c2 (m : ℕ) : ((pA m) 2).val = 0 := by simp [pA]

theorem pB_c0 (m : ℕ) : ((pB m) 0).val = 1 := by
  rw [pB, shift_val_ne _ _ _ (by decide), pA_c0]

theorem pB_c1 (m : ℕ) : ((pB m) 1).val = 1 := by
  rw [pB, shift_val_self _ _ (by rw [pA_c1, wExt_succ]; have := wEll_three m; omega), pA_c1]

theorem pB_c2 (m : ℕ) : ((pB m) 2).val = 0 := by
  rw [pB, shift_val_ne _ _ _ (by decide), pA_c2]

theorem pC_c0 (m : ℕ) : ((pC m) 0).val = 1 := by
  rw [pC, shift_val_ne _ _ _ (by decide), pA_c0]

theorem pC_c1 (m : ℕ) : ((pC m) 1).val = 0 := by
  rw [pC, shift_val_ne _ _ _ (by decide), pA_c1]

theorem pC_c2 (m : ℕ) : ((pC m) 2).val = 1 := by
  rw [pC, shift_val_self _ _ (by rw [pA_c2, wExt_succ]; have := wEll_three m; omega), pA_c2]

theorem shift_pA_one (m : ℕ) : periodicLatticeShift (pA m) 1 = pB m := rfl
theorem shift_pA_two (m : ℕ) : periodicLatticeShift (pA m) 2 = pC m := rfl
theorem shift_pB_two (m : ℕ) : periodicLatticeShift (pB m) 2 = pD m := rfl

/-- The plaquette closes: `(pA + e₂) + e₁ = (pA + e₁) + e₂`. -/
theorem shift_pC_one (m : ℕ) : periodicLatticeShift (pC m) 1 = pD m := by
  rw [pC, pD, pB]
  exact AdalyFormal.Balaban.LemmaAssembly.shift_comm_local (pA m) (by decide : (2 : Fin 3) ≠ 1)

theorem pA_ne_pC (m : ℕ) : pA m ≠ pC m := by
  intro h
  have := congrArg (fun s => (s 2).val) h
  rw [pA_c2, pC_c2] at this
  exact absurd this (by norm_num)

/-! ## §2 — the loop field, and its value at bonds outside its support -/

/-- **THE PLAQUETTE LOOP FIELD.** The circulation of `suTwoWitness` around the `(1,2)`-plaquette
based at `(1,0,0)`: `+w` on `(pA,1)` and `(pB,2)`, `−w` on `(pC,1)` and `(pA,2)`. Grouped by
direction, which is the grouping the `Q` computation consumes. -/
noncomputable def loopField (m : ℕ) : Bond (wExt m) → SuTwo :=
  (Pi.single ((pA m, 1) : Bond (wExt m)) suTwoWitness
      - Pi.single ((pC m, 1) : Bond (wExt m)) suTwoWitness)
    + (Pi.single ((pB m, 2) : Bond (wExt m)) suTwoWitness
      - Pi.single ((pA m, 2) : Bond (wExt m)) suTwoWitness)

private theorem one_ne_two : (1 : Fin 3) ≠ 2 := by decide

private theorem single_eq_zero_of_site_ne {L : PeriodicLatticeExtent} (b : Bond L)
    (z : PeriodicLatticeSite L) (ν : Fin 3) (v : SuTwo) (h : b.1 ≠ z) :
    (Pi.single ((z, ν) : Bond L) v : Bond L → SuTwo) b = 0 := by
  classical
  rw [Pi.single_apply, if_neg]
  intro hcon
  exact h (congrArg Prod.fst hcon)

private theorem single_eq_zero_of_dir_ne {L : PeriodicLatticeExtent} (b : Bond L)
    (z : PeriodicLatticeSite L) (ν : Fin 3) (v : SuTwo) (h : b.2 ≠ ν) :
    (Pi.single ((z, ν) : Bond L) v : Bond L → SuTwo) b = 0 := by
  classical
  rw [Pi.single_apply, if_neg]
  intro hcon
  exact h (congrArg Prod.snd hcon)

/-- Every bond whose base site has coordinate `0` different from `1` is outside the loop. -/
theorem loopField_eq_zero_of_c0_ne (m : ℕ) (b : Bond (wExt m)) (h : (b.1 0).val ≠ 1) :
    loopField m b = 0 := by
  have hA : b.1 ≠ pA m := fun hc => h (by rw [hc, pA_c0])
  have hB : b.1 ≠ pB m := fun hc => h (by rw [hc, pB_c0])
  have hC : b.1 ≠ pC m := fun hc => h (by rw [hc, pC_c0])
  unfold loopField
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [single_eq_zero_of_site_ne b (pA m) 1 suTwoWitness hA,
    single_eq_zero_of_site_ne b (pC m) 1 suTwoWitness hC,
    single_eq_zero_of_site_ne b (pB m) 2 suTwoWitness hB,
    single_eq_zero_of_site_ne b (pA m) 2 suTwoWitness hA]
  abel

/-- The loop uses no direction-`0` bond. -/
theorem loopField_eq_zero_of_dir_zero (m : ℕ) (b : Bond (wExt m)) (h : b.2 = 0) :
    loopField m b = 0 := by
  have h1 : b.2 ≠ 1 := by rw [h]; decide
  have h2 : b.2 ≠ 2 := by rw [h]; decide
  unfold loopField
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [single_eq_zero_of_dir_ne b (pA m) 1 suTwoWitness h1,
    single_eq_zero_of_dir_ne b (pC m) 1 suTwoWitness h1,
    single_eq_zero_of_dir_ne b (pB m) 2 suTwoWitness h2,
    single_eq_zero_of_dir_ne b (pA m) 2 suTwoWitness h2]
  abel

theorem loopField_at_pA_one (m : ℕ) : loopField m (pA m, 1) = suTwoWitness := by
  classical
  unfold loopField
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [single_eq_zero_of_site_ne (pA m, 1) (pC m) 1 suTwoWitness (pA_ne_pC m),
    single_eq_zero_of_dir_ne (pA m, 1) (pB m) 2 suTwoWitness one_ne_two,
    single_eq_zero_of_dir_ne (pA m, 1) (pA m) 2 suTwoWitness one_ne_two,
    Pi.single_eq_same]
  abel

/-- `bondEnergy` of the loop is strictly positive — the datum is not the zero field. -/
theorem bondEnergy_loopField_pos (m : ℕ) : 0 < bondEnergy (loopField m) := by
  classical
  unfold bondEnergy
  refine Finset.sum_pos' (fun b _ => sq_nonneg _) ⟨(pA m, 1), Finset.mem_univ _, ?_⟩
  rw [loopField_at_pA_one]
  have h : 0 < ‖suTwoWitness‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
  positivity

/-! ## §3 — the loop is `D*_U`-free at `U = 1`, hence in the fibre's SECOND clause for EVERY
`levels` -/

/-- **The divergence of a single spike.** `D*_1 (Pi.single (z,ν) v) = v·(δ_{z+e_ν} − δ_z)`. -/
theorem div_single {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L) (ν : Fin 3)
    (v : SuTwo) (y : PeriodicLatticeSite L) :
    gradCovariantAdjointValue (trivialU L) (Pi.single ((z, ν) : Bond L) v : Bond L → SuTwo) y
      = (if y = periodicLatticeShift z ν then v else 0) - (if y = z then v else 0) := by
  classical
  have hin : ∑ μ : Fin 3,
        (Pi.single ((z, ν) : Bond L) v : Bond L → SuTwo) (periodicLatticeShiftBack y μ, μ)
      = if y = periodicLatticeShift z ν then v else 0 := by
    rw [Finset.sum_eq_single_of_mem ν (Finset.mem_univ ν)
      (fun b _ hb => single_eq_zero_of_dir_ne (periodicLatticeShiftBack y b, b) z ν v hb)]
    by_cases hy : y = periodicLatticeShift z ν
    · rw [if_pos hy,
        show ((periodicLatticeShiftBack y ν, ν) : Bond L) = (z, ν) by
          rw [hy, periodicLatticeShiftBack_shift],
        Pi.single_eq_same]
    · rw [if_neg hy]
      refine single_eq_zero_of_site_ne (periodicLatticeShiftBack y ν, ν) z ν v ?_
      intro hcon
      exact hy ((shift_eq_iff_shiftBack z y ν).mpr hcon.symm).symm
  have hout : ∑ μ : Fin 3, (Pi.single ((z, ν) : Bond L) v : Bond L → SuTwo) (y, μ)
      = if y = z then v else 0 := by
    rw [Finset.sum_eq_single_of_mem ν (Finset.mem_univ ν)
      (fun b _ hb => single_eq_zero_of_dir_ne (y, b) z ν v hb)]
    by_cases hy : y = z
    · rw [if_pos hy, hy, Pi.single_eq_same]
    · rw [if_neg hy]
      exact single_eq_zero_of_site_ne (y, ν) z ν v hy
  have hU : ∀ b : Bond L, RMap ((trivialU L) b)⁻¹ = LinearMap.id := by
    intro b
    change RMap ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))⁻¹ = LinearMap.id
    rw [inv_one, RMap_one]
  unfold gradCovariantAdjointValue
  simp only [hU, LinearMap.id_coe, id_eq]
  rw [Finset.sum_sub_distrib, hin, hout]

/-- **The loop is divergence-free at `U = 1`.** The four spike divergences cancel in pairs across
the plaquette's four corners: `δ_pB − δ_pA + δ_pD − δ_pB − (δ_pD − δ_pC) − (δ_pC − δ_pA) = 0`. -/
theorem loopField_div_eq_zero (m : ℕ) :
    gradCovariantAdjointLM (trivialU (wExt m)) (loopField m) = 0 := by
  classical
  unfold loopField
  rw [map_add, map_sub, map_sub]
  funext y
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, gradCovariantAdjointLM_apply]
  rw [div_single, div_single, div_single, div_single, shift_pA_one, shift_pA_two, shift_pB_two,
    shift_pC_one]
  abel

/-! ## §4 — the loop is annihilated by `Q_{S.fibre}` -/

/-- **Two same-direction spikes whose base sites differ ONLY in a transverse coordinate, with values
`0` and `1` there, have the SAME `Q_ell`.** At the fibre level the coarse sites have that coordinate
equal to `0` or `ell` (`coarse_at_fibre_val`) and `ell ≥ 3`, so no block separates `0` from `1`: the
two block-counts of `Q_single_same_dir` are literally the same `Finset`. -/
theorem block_mem_iff {m : ℕ} {y : PeriodicLatticeSite (wExt m)}
    (hy : y ∈ CoarseLattice (wExt m) (wEll m))
    (z z' : PeriodicLatticeSite (wExt m)) (ν ρ : Fin 3) (hρ : ρ ≠ ν)
    (hsame : ∀ σ : Fin 3, σ ≠ ρ → (z σ).val = (z' σ).val)
    (hz : (z ρ).val = 0) (hz' : (z' ρ).val = 1) (K : ℕ) :
    pathSite z ν K ∈ blockOf y (wEll m) ↔ pathSite z' ν K ∈ blockOf y (wEll m) := by
  rw [mem_blockOf, mem_blockOf]
  have hcoord : ∀ σ : Fin 3, σ ≠ ρ →
      ((pathSite z ν K) σ).val = ((pathSite z' ν K) σ).val := by
    intro σ hσ
    by_cases hsν : σ = ν
    · subst hsν
      rw [pathSite_apply_self_val, pathSite_apply_self_val, hsame σ hσ]
    · rw [pathSite_apply_ne z ν σ K hsν, pathSite_apply_ne z' ν σ K hsν, hsame σ hσ]
  have hzρ : ((pathSite z ν K) ρ).val = 0 := by
    rw [pathSite_apply_ne z ν ρ K hρ, hz]
  have hz'ρ : ((pathSite z' ν K) ρ).val = 1 := by
    rw [pathSite_apply_ne z' ν ρ K hρ, hz']
  have h3 := wEll_three m
  rcases coarse_at_fibre_val hy ρ with hy0 | hyl
  · constructor
    · intro h σ
      by_cases hσ : σ = ρ
      · subst hσ; rw [hz'ρ, hy0]; omega
      · rw [← hcoord σ hσ]; exact h σ
    · intro h σ
      by_cases hσ : σ = ρ
      · subst hσ; rw [hzρ, hy0]; omega
      · rw [hcoord σ hσ]; exact h σ
  · constructor
    · intro h
      have := h ρ
      rw [hzρ, hyl] at this
      omega
    · intro h
      have := h ρ
      rw [hz'ρ, hyl] at this
      omega

/-- The `Q_ell`-level consequence: the two spikes have equal `Q_ell`, at every coarse bond. -/
theorem Q_spike_pair_eq {m : ℕ} (c : CoarseBond (wExt m) (wEll m)) (ν : Fin 3)
    (z z' : PeriodicLatticeSite (wExt m)) (ρ : Fin 3) (hρ : ρ ≠ ν)
    (hsame : ∀ σ : Fin 3, σ ≠ ρ → (z σ).val = (z' σ).val)
    (hz : (z ρ).val = 0) (hz' : (z' ρ).val = 1) (v : SuTwo) :
    lineCoarseRestrictCov (trivialU (wExt m)) (wEll m) (Pi.single ((z, ν) : Bond (wExt m)) v) c
      = lineCoarseRestrictCov (trivialU (wExt m)) (wEll m)
          (Pi.single ((z', ν) : Bond (wExt m)) v) c := by
  classical
  by_cases hc : ν = c.2
  · subst hc
    have hle : wEll m ≤ wExt m c.2 + 1 := by
      rw [wExt_succ]; have := wEll_pos m; omega
    have hfilter : ((Finset.range (wEll m)).filter
          (fun i => pathSite z c.2 (wExt m c.2 + 1 - i) ∈ blockOf c.1.1 (wEll m)))
        = ((Finset.range (wEll m)).filter
          (fun i => pathSite z' c.2 (wExt m c.2 + 1 - i) ∈ blockOf c.1.1 (wEll m))) :=
      Finset.filter_congr fun i _ =>
        block_mem_iff c.1.2 z z' c.2 ρ hρ hsame hz hz' (wExt m c.2 + 1 - i)
    rw [Q_single_same_dir c hle z v, Q_single_same_dir c hle z' v, hfilter]
  · rw [Q_single_other_dir c z ν hc v, Q_single_other_dir c z' ν hc v]

/-- **THE FIBRE-LEVEL KERNEL CLAUSE.** `Q_{ell}(loopField) = 0`. -/
theorem Q_loopField_fibre (m : ℕ) :
    lineCoarseRestrictCovLM (trivialU (wExt m)) (wEll m) (loopField m) = 0 := by
  classical
  unfold loopField
  rw [map_add, map_sub, map_sub]
  funext c
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, lineCoarseRestrictCovLM_apply]
  rw [Q_spike_pair_eq c 1 (pA m) (pC m) 2 (by decide)
        (fun σ hσ => by rw [pC, shift_val_ne _ _ _ hσ]) (pA_c2 m) (pC_c2 m) suTwoWitness,
    Q_spike_pair_eq c 2 (pA m) (pB m) 1 (by decide)
        (fun σ hσ => by rw [pB, shift_val_ne _ _ _ hσ]) (pA_c1 m) (pB_c1 m) suTwoWitness]
  abel

/-! ## §5 — the loop is annihilated by `Q_{S.constr}`, so `fullC` fixes it -/

private theorem sum_single_dir {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L)
    (ν σ : Fin 3) (v : SuTwo) :
    ∑ x : PeriodicLatticeSite L, (Pi.single ((z, ν) : Bond L) v : Bond L → SuTwo) (x, σ)
      = if σ = ν then v else 0 := by
  classical
  by_cases h : σ = ν
  · subst h
    rw [if_pos rfl]
    have hstep : ∀ x : PeriodicLatticeSite L,
        (Pi.single ((z, σ) : Bond L) v : Bond L → SuTwo) (x, σ) = if x = z then v else 0 := by
      intro x
      by_cases hx : x = z
      · rw [if_pos hx, hx, Pi.single_eq_same]
      · rw [if_neg hx]
        exact single_eq_zero_of_site_ne (x, σ) z σ v hx
    rw [Finset.sum_congr rfl (fun x _ => hstep x),
      Finset.sum_ite_eq' Finset.univ z (fun _ => v), if_pos (Finset.mem_univ z)]
  · rw [if_neg h]
    have hstep : ∀ x : PeriodicLatticeSite L,
        (Pi.single ((z, ν) : Bond L) v : Bond L → SuTwo) (x, σ) = 0 :=
      fun x => single_eq_zero_of_dir_ne (x, σ) z ν v h
    rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_const_zero]

/-- Each direction's two spikes cancel in the full-torus sum. -/
theorem sum_loopField (m : ℕ) (σ : Fin 3) :
    ∑ x : PeriodicLatticeSite (wExt m), loopField m (x, σ) = 0 := by
  classical
  unfold loopField
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_single_dir (pA m) 1 σ suTwoWitness, sum_single_dir (pC m) 1 σ suTwoWitness,
    sum_single_dir (pB m) 2 σ suTwoWitness, sum_single_dir (pA m) 2 σ suTwoWitness]
  abel

/-- **THE CONSTRAINT-LEVEL KERNEL FACT.** `Q_{2·ell}(loopField) = 0`. At this extent the constraint
level has one block (the whole torus), so `Q_{2·ell}` is the plain torus average
(`WitnessInequality.Q_full`) and each direction's two opposite spikes cancel. -/
theorem Q_loopField_constr (m : ℕ) (c : CoarseBond (wExt m) (2 * wEll m)) :
    lineCoarseRestrictCov (trivialU (wExt m)) (2 * wEll m) (loopField m) c = 0 := by
  rw [Q_full (loopField m) c, sum_loopField m c.2, smul_zero]

/-- The three dropped bonds have base coordinate `0` in `{0, 2·ell − 1}`, so none of them is a loop
bond (all four of which have base coordinate `0` equal to `1`). -/
theorem loopField_dropped (m : ℕ) (c : CoarseBond (wExt m) (2 * wEll m)) :
    loopField m (droppedBondLast (2 * wEll m) c) = 0 := by
  refine loopField_eq_zero_of_c0_ne m _ ?_
  have h3 := wEll_three m
  have hz : ((c.1.1 : PeriodicLatticeSite (wExt m)) 0).val = 0 := coarse_at_full_val c.1.2 0
  change ((pathSite (c.1.1 : PeriodicLatticeSite (wExt m)) c.2 (2 * wEll m - 1)) 0).val ≠ 1
  by_cases hd : c.2 = 0
  · rw [hd] at *
    rw [pathSite_apply_self_val, hz, wExt_succ]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [pathSite_apply_ne _ _ _ _ (fun hcon => hd hcon.symm), hz]
    omega

/-- **`fullC` FIXES THE LOOP.** Both inputs to `solvedValue` vanish (`Q_{2·ell}(loop) = 0` and the
loop is `0` on every dropped bond), so the solved value is `0` — which is what the loop already
has there. -/
theorem fullC_loopField (m : ℕ) :
    fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
        (loopField m) = loopField m := by
  classical
  funext b
  by_cases hb : IsDropped (2 * wEll m) b
  · obtain ⟨c, rfl⟩ := hb
    rw [fullC_dropped (wConstr_pos m) (wConstr_dvd m), loopField_dropped m c]
    unfold solvedValue
    rw [restFunctional_eq, Q_loopField_constr m c, loopField_dropped m c, map_zero, sub_zero,
      map_zero, neg_zero]
  · rw [fullC_free _ _ _ hb]

/-! ## §6 — the loop is IN the fibre, for every `levels`; hence the Schur complement vanishes -/

/-- **THE LOOP IS IN THE FIBRE, AT EVERY `levels`.** The first clause is `Q_{ell} = 0` (§4); the
second is `RcovLM U levels (D*_U ·) = 0`, discharged by `D*_U(loop) = 0` (§3) and linearity — which
is why the value of `levels` is IRRELEVANT to this counterexample. -/
theorem loopField_mem_fibre (m : ℕ) (levels : List (KernelSubspace.Level (wExt m)))
    [(deltaKernelImageCovH (trivialU (wExt m)) levels).HasOrthogonalProjection] :
    loopField m ∈ gaugeConstraintSubspaceCovFaithful (wEll m) levels (trivialU (wExt m)) :=
  mem_gaugeConstraintSubspaceCovFaithful.mpr
    ⟨Q_loopField_fibre m, by rw [loopField_div_eq_zero m, map_zero]⟩

/-- **THE TARGET'S RIGHT-HAND SIDE VANISHES AT THE LOOP** — for every `levels`. The Schur complement
is the distance from `D_U B̃` to `D_U(V)`; the loop lies in `V`, so the distance is `0`. -/
theorem cStar_loopField_le_zero (m : ℕ) (levels : List (KernelSubspace.Level (wExt m)))
    [(deltaKernelImageCovH (trivialU (wExt m)) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful (wSplit m).fibre levels (trivialU (wExt m))).HasOrthogonalProjection] :
    cStarDeltaKCFormCorr (wSplit m) levels (trivialU (wExt m))
        (dinvC (trivialU (wExt m)) (2 * wEll m)) (loopField m) ≤ 0 := by
  have hform : cStarDeltaKCFormCorr (wSplit m) levels (trivialU (wExt m))
        (dinvC (trivialU (wExt m)) (2 * wEll m)) (loopField m)
      = deltaJQuadFormCovFaithful (wEll m) levels (trivialU (wExt m))
          (fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
            (loopField m)) := rfl
  rw [hform, fullC_loopField m]
  have hle := deltaJQuadFormCovFaithful_le_of_sub (wEll m) levels (trivialU (wExt m))
    (loopField m) (loopField m) (loopField_mem_fibre m levels)
  rw [sub_self] at hle
  -- `TheLemmaRepaired.dstarDQuadForm_zero` is the same fact, but that module is outside this
  -- off-spine import chain; re-proved in two lines rather than pulling it in.
  have hzero : dstarDQuadForm (trivialU (wExt m)) (0 : Bond (wExt m) → SuTwo) = 0 := by
    unfold dstarDQuadForm covPlaqInner
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [show curlValueCovariant (trivialU (wExt m)) (0 : Bond (wExt m) → SuTwo) p = 0 by
      simp [curlValueCovariant], hsInner_zero_zero]
  rw [hzero] at hle
  exact hle

/-- **…AND IT IS EXACTLY `0`**, not merely `≤ 0`: the failure at this datum is a VANISHING. This is
the sharp contrast with `WitnessInequality`'s datum, where the same right-hand side is strictly
POSITIVE (`WitnessInequality.cStar_wField_pos`) and only the RATE fails. -/
theorem cStar_loopField_eq_zero (m : ℕ) (levels : List (KernelSubspace.Level (wExt m)))
    [(deltaKernelImageCovH (trivialU (wExt m)) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful (wSplit m).fibre levels (trivialU (wExt m))).HasOrthogonalProjection] :
    cStarDeltaKCFormCorr (wSplit m) levels (trivialU (wExt m))
        (dinvC (trivialU (wExt m)) (2 * wEll m)) (loopField m) = 0 :=
  le_antisymm (cStar_loopField_le_zero m levels)
    (deltaJQuadFormCovFaithful_nonneg (wEll m) levels (trivialU (wExt m))
      (fullC (trivialU (wExt m)) (2 * wEll m) (dinvC (trivialU (wExt m)) (2 * wEll m))
        (loopField m)))

/-! ## §7 — THE STATEMENT, restricted along an arbitrary `levels` selector, and REFUTED -/

/-- **The level-corrected uniform coercivity target, with `levels` PINNED by a selector.**
Character-for-character `ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform` except that its
inner `∀ levels` is replaced by `choose L`. Taking `choose := fun _ => []` gives the `levels = []`
restriction the dispatch asked for; taking `choose := oneLevelUniv` gives the branch
`WitnessInequality` refuted. Every hypothesis, every clause and the conclusion are otherwise
unchanged, including the `2 ≤ S.fibre` non-degeneracy guard and the `4 ≤ L μ` extent guard. -/
def LevelCorrectedCoercivityTargetAt
    (choose : (L : PeriodicLatticeExtent) → List (KernelSubspace.Level L)) : Prop :=
  ∃ γ₀ α₀ : ℝ, 0 < γ₀ ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent) (S : LevelSplit), 2 ≤ S.fibre →
      (∀ μ : Fin 3, 4 ≤ L μ) →
      (∀ μ : Fin 3, S.fibre ∣ (L μ + 1)) → (∀ μ : Fin 3, S.constr ∣ (L μ + 1)) →
      ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ [(deltaKernelImageCovH U (choose L)).HasOrthogonalProjection]
          [(curlImageCovHFaithful S.fibre (choose L) U).HasOrthogonalProjection]
          (Dinv : CoarseBond L S.constr → (SuTwo →ₗ[ℝ] SuTwo)),
          (∀ c : CoarseBond L S.constr,
            (coeffDc U S.constr c (droppedBondLast S.constr c)).comp (Dinv c)
              = LinearMap.id) →
          ∀ (Btil : Bond L → SuTwo),
            (∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L S.constr →
              ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' S.constr →
              ∀ e ∈ staircasePath y' x, Btil e = 0) →
            (∀ c : CoarseBond L S.constr, Btil (droppedBondLast S.constr c) = 0) →
            γ₀ * bondEnergy Btil ≤ cStarDeltaKCFormCorr S (choose L) U Dinv Btil

/-- **THE `levels = []` RESTRICTION**, the object the dispatch asked to state and test. -/
def NilLevelCorrectedCoercivityTarget : Prop :=
  LevelCorrectedCoercivityTargetAt (fun L => ([] : List (KernelSubspace.Level L)))

/-- The loop's four bonds are off the constraint-level axial staircase. Read from
`staircasePath`'s definition: the direction-`2` segment is based at `y`, the direction-`1` segment
at `corner1 y x = update y 2 (x 2)` — both have coordinate `0` equal to `y 0`, which is `0` at the
constraint level (one block, `coarse_at_full_val`) — and the direction-`0` segment contributes only
direction-`0` bonds, which the loop does not use. -/
theorem loopField_axial_gen (m : ℕ) (y' x : PeriodicLatticeSite (wExt m))
    (hy0 : ((y' : PeriodicLatticeSite (wExt m)) 0).val ≠ 1) :
    ∀ e ∈ staircasePath y' x, loopField m e = 0 := by
  intro e he
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at he
  rcases he with (h1 | h2) | h3
  · rw [mem_axisSegment] at h1
    refine loopField_eq_zero_of_c0_ne m e ?_
    rw [h1.2.1 0 (by decide)]
    exact hy0
  · rw [mem_axisSegment] at h2
    refine loopField_eq_zero_of_c0_ne m e ?_
    rw [h2.2.1 0 (by decide), corner1, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2)]
    exact hy0
  · rw [mem_axisSegment] at h3
    exact loopField_eq_zero_of_dir_zero m e h3.1

theorem loopField_axial (m : ℕ) :
    ∀ y' : PeriodicLatticeSite (wExt m), y' ∈ CoarseLattice (wExt m) (2 * wEll m) →
      ∀ x : PeriodicLatticeSite (wExt m), x ∈ blockOf y' (2 * wEll m) →
      ∀ e ∈ staircasePath y' x, loopField m e = 0 := by
  intro y' hy' x _
  refine loopField_axial_gen m y' x ?_
  rw [coarse_at_full_val hy' 0]
  omega

/-! ### §6b — THE OBVIOUS REPAIR ALSO FAILS: imposing the two `B̃` clauses at the FIBRE level

The refutation locates the defect in the ADMISSIBILITY CLASS, which the target imposes at
`S.constr` while taking the fibre at `S.fibre`. The first repair anyone would try is to impose the
clauses at `S.fibre` instead. **That does not work either, at the same datum**: the loop is off the
FIBRE-level staircase too, because fibre-level coarse sites have coordinate `0` equal to `0` or
`ell ≥ 3`, and the loop's four bonds all have base coordinate `0` equal to `1`. -/

theorem loopField_axial_fibre (m : ℕ) :
    ∀ y' : PeriodicLatticeSite (wExt m), y' ∈ CoarseLattice (wExt m) (wEll m) →
      ∀ x : PeriodicLatticeSite (wExt m), x ∈ blockOf y' (wEll m) →
      ∀ e ∈ staircasePath y' x, loopField m e = 0 := by
  intro y' hy' x _
  refine loopField_axial_gen m y' x ?_
  have h3 := wEll_three m
  rcases coarse_at_fibre_val hy' 0 with h | h
  · rw [h]; omega
  · rw [h]; omega

theorem loopField_dropped_fibre (m : ℕ) (c : CoarseBond (wExt m) (wEll m)) :
    loopField m (droppedBondLast (wEll m) c) = 0 := by
  refine loopField_eq_zero_of_c0_ne m _ ?_
  have h3 := wEll_three m
  change ((pathSite (c.1.1 : PeriodicLatticeSite (wExt m)) c.2 (wEll m - 1)) 0).val ≠ 1
  rcases coarse_at_fibre_val c.1.2 0 with hz | hz
  · by_cases hd : c.2 = 0
    · rw [hd] at *
      rw [pathSite_apply_self_val, hz, wExt_succ]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [pathSite_apply_ne _ _ _ _ (fun hcon => hd hcon.symm), hz]
      omega
  · by_cases hd : c.2 = 0
    · rw [hd] at *
      rw [pathSite_apply_self_val, hz, wExt_succ]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [pathSite_apply_ne _ _ _ _ (fun hcon => hd hcon.symm), hz]
      omega

/-- **NO RESTRICTION OF `levels` REPAIRS THE TARGET.** For EVERY selector `choose`, the target with
`levels := choose L` is false — refuted at a single fixed extent (`m = 0`, so `L μ = 5`,
`S = (3, 6)`), by VANISHING of the right-hand side rather than by a rate, with no limit taken.

The datum is `loopField 0`, a plaquette circulation in the `(1,2)` plane based at `(1,0,0)`. It
satisfies the target's two `B̃` clauses (`loopField_axial`, `loopField_dropped`) with strictly
positive `bondEnergy` (`bondEnergy_loopField_pos`), and lies in the fibre for every `levels`
(`loopField_mem_fibre`), so the target's right-hand side is `≤ 0` (`cStar_loopField_le_zero`). -/
theorem targetAt_refuted (choose : (L : PeriodicLatticeExtent) → List (KernelSubspace.Level L)) :
    ¬ LevelCorrectedCoercivityTargetAt choose := by
  rintro ⟨γ₀, α₀, hγ, hα, hT⟩
  have hfrob : frobSupBond (trivialU (wExt 0)) ≤ α₀ := by
    rw [RegularUDomainWitness.frobSupBond_trivialU]
    exact le_of_lt hα
  have hfib : 2 ≤ (wSplit 0).fibre := by
    change 2 ≤ wEll 0
    have := wEll_three 0; omega
  have hineq := hT (wExt 0) (wSplit 0) hfib (wExt_four 0) (wEll_dvd 0) (wConstr_dvd 0)
    (trivialU (wExt 0)) hfrob
    (dinvC (trivialU (wExt 0)) (2 * wEll 0))
    (dinvC_hinv (wConstr_pos 0) (wConstr_dvd 0) (trivialU (wExt 0)))
    (loopField 0) (loopField_axial 0) (loopField_dropped 0)
  have hzero := cStar_loopField_le_zero 0 (choose (wExt 0))
  have hE := bondEnergy_loopField_pos 0
  have : 0 < γ₀ * bondEnergy (loopField 0) := mul_pos hγ hE
  linarith

/-- **THE `levels = []` RESTRICTION IS ALSO REFUTED** — the dispatched question, answered. -/
theorem nil_target_refuted : ¬ NilLevelCorrectedCoercivityTarget :=
  targetAt_refuted _

/-- **A SECOND, INDEPENDENT REFUTATION OF THE `∀ levels` TARGET** — by vanishing rather than rate.
`WitnessInequality.target_refuted` already proves this; the point of re-deriving it here is that
this proof exhibits a mechanism that survives every `levels`-restriction, whereas the rate
mechanism was tied to the branch `oneLevelUniv`, which the tree independently proved obstructed
(`StokesCommU.denominator_hypotheses_do_not_cover_fibre_oneLevelUniv`). -/
theorem uniform_target_refuted :
    ¬ ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform := by
  intro h
  refine targetAt_refuted (fun L => ([] : List (KernelSubspace.Level L))) ?_
  obtain ⟨γ₀, α₀, hγ, hα, hT⟩ := h
  refine ⟨γ₀, α₀, hγ, hα, ?_⟩
  intro L S hfib h4 hdf hdc U hfrob _ _ Dinv hinv Btil hax hdr
  exact hT L S hfib h4 hdf hdc [] U hfrob Dinv hinv Btil hax hdr

/-- **THE OBVIOUS REPAIR, STATED.** The same target with the two `B̃` admissibility clauses imposed
at the FIBRE level `S.fibre` instead of at the constraint level `S.constr`. Everything else is
unchanged — in particular `Dinv` and `fullC` stay at `S.constr`, because that is where the (3.157)
reparametrization is defined; only the two clauses move. -/
def LevelCorrectedCoercivityTargetFibreClauses
    (choose : (L : PeriodicLatticeExtent) → List (KernelSubspace.Level L)) : Prop :=
  ∃ γ₀ α₀ : ℝ, 0 < γ₀ ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent) (S : LevelSplit), 2 ≤ S.fibre →
      (∀ μ : Fin 3, 4 ≤ L μ) →
      (∀ μ : Fin 3, S.fibre ∣ (L μ + 1)) → (∀ μ : Fin 3, S.constr ∣ (L μ + 1)) →
      ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ [(deltaKernelImageCovH U (choose L)).HasOrthogonalProjection]
          [(curlImageCovHFaithful S.fibre (choose L) U).HasOrthogonalProjection]
          (Dinv : CoarseBond L S.constr → (SuTwo →ₗ[ℝ] SuTwo)),
          (∀ c : CoarseBond L S.constr,
            (coeffDc U S.constr c (droppedBondLast S.constr c)).comp (Dinv c)
              = LinearMap.id) →
          ∀ (Btil : Bond L → SuTwo),
            (∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L S.fibre →
              ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' S.fibre →
              ∀ e ∈ staircasePath y' x, Btil e = 0) →
            (∀ c : CoarseBond L S.fibre, Btil (droppedBondLast S.fibre c) = 0) →
            γ₀ * bondEnergy Btil ≤ cStarDeltaKCFormCorr S (choose L) U Dinv Btil

/-- **MOVING THE CLAUSES TO THE FIBRE LEVEL DOES NOT REPAIR IT EITHER.** The same datum refutes the
fibre-clause variant, for every selector: `loopField` is off the FIBRE-level axial staircase
(`loopField_axial_fibre`) and vanishes on every fibre-level dropped bond
(`loopField_dropped_fibre`), because fibre-level coarse sites have coordinate `0` in `{0, ell}` with
`ell ≥ 3` while all four loop bonds have base coordinate `0` equal to `1`.

So the defect is not the level MISMATCH between the clauses and the fibre: the axial-gauge plus
dropped-bond class does not exclude fibre elements at EITHER level. -/
theorem targetFibreClauses_refuted
    (choose : (L : PeriodicLatticeExtent) → List (KernelSubspace.Level L)) :
    ¬ LevelCorrectedCoercivityTargetFibreClauses choose := by
  rintro ⟨γ₀, α₀, hγ, hα, hT⟩
  have hfrob : frobSupBond (trivialU (wExt 0)) ≤ α₀ := by
    rw [RegularUDomainWitness.frobSupBond_trivialU]
    exact le_of_lt hα
  have hfib : 2 ≤ (wSplit 0).fibre := by
    change 2 ≤ wEll 0
    have := wEll_three 0; omega
  have hineq := hT (wExt 0) (wSplit 0) hfib (wExt_four 0) (wEll_dvd 0) (wConstr_dvd 0)
    (trivialU (wExt 0)) hfrob
    (dinvC (trivialU (wExt 0)) (2 * wEll 0))
    (dinvC_hinv (wConstr_pos 0) (wConstr_dvd 0) (trivialU (wExt 0)))
    (loopField 0) (loopField_axial_fibre 0) (loopField_dropped_fibre 0)
  have hzero := cStar_loopField_le_zero 0 (choose (wExt 0))
  have hE := bondEnergy_loopField_pos 0
  have : 0 < γ₀ * bondEnergy (loopField 0) := mul_pos hγ hE
  linarith

/-! ## §8 — why §7 does NOT contradict the POSITIVE sandwich witness at `B7`

`ThirdLevelSchurGap.lean`'s §4 residual list still names `[SANDWICH-WITNESS]` as open. **That line
is STALE and this module does not act on it.** `Balaban/ThirdLevelSandwich.lean` (already in the
tree) closed it: `fullC_fixes_B7`, `sandwich_positivity`, `sandwich_energy_bound` are there, so
`⟨B̃, C*Δ_kC B̃⟩` is STRICTLY POSITIVE at `B7`.

~~It is done here … `B7_dropped` … `fullC_B7` … `sandwich_B7_lower_bound`.~~ (STRUCK in this same
pass, retained struck per S75: an earlier draft of this section re-derived `B7_no_dropped`,
`fullC_fixes_B7`, `sandwich_positivity` and `sandwich_energy_bound` under the names `B7_dropped`,
`fullC_B7`, `sandwich_B7_pos`, `sandwich_B7_lower_bound`, having trusted `ThirdLevelSchurGap`'s
stale residual line instead of grepping for the closure. All four duplicates are DELETED, LAW-19.
The stale line in `ThirdLevelSchurGap.lean` is a FINDING, not this lane's to repair — that file is
outside this lane's write scope.)

What IS new, and is the reason this section exists, is the RECONCILIATION. §7 exhibits an
admissible `B̃` at which the same sandwich form is `0`; `ThirdLevelSandwich` exhibits `B7` at which
it is `> 0`. Both are facts, and `B7_not_axial` proves why there is no conflict: `B7` is NOT in the
target's admissible class — its `+` bond lies ON the constraint-level axial staircase. So the
positive witness and the refuting datum live in disjoint classes, which is precisely §7's point:
what fails is the ADMISSIBLE CLASS, not the form. -/

open AdalyFormal.Balaban.ThirdLevelWitness (witL7 s7Z s7P B7 s7P_ne_s7M dipole_apply_plus)

/-- The site `(1,1,0)` of `witL7`, a level-4 block member used to hit `B7`'s `+` bond with the
staircase. -/
def x7 : PeriodicLatticeSite witL7 := fun ρ => if ρ = 2 then 0 else 1

/-- **`B7` IS NOT IN THE TARGET'S ADMISSIBLE CLASS** — it lies on the constraint-level axial
staircase, at the direction-`0` segment `axisSegment (corner2 s7Z x7) 0 0 1`, whose only bond is
`(s7P, 0)` — `B7`'s `+` bond. So §8's positive sandwich witness is NOT a counterexample to §7's
refutation, and §7's refutation does not contradict `third_level_energy_bound`: the two data lie in
disjoint classes. -/
theorem B7_not_axial :
    ¬ (∀ y' : PeriodicLatticeSite witL7, y' ∈ CoarseLattice witL7 4 →
        ∀ x : PeriodicLatticeSite witL7, x ∈ blockOf y' 4 →
        ∀ e ∈ staircasePath y' x, B7 e = 0) := by
  intro h
  have hy : s7Z ∈ CoarseLattice witL7 4 := mem_CoarseLattice.mpr (by decide)
  have hx : x7 ∈ blockOf s7Z 4 := mem_blockOf.mpr (by decide)
  have hmem : ((s7P, 0) : Bond witL7) ∈ staircasePath s7Z x7 := by
    rw [staircasePath, Finset.mem_union, Finset.mem_union]
    refine Or.inr ?_
    rw [mem_axisSegment]
    exact ⟨rfl, by decide, by decide, by decide⟩
  have := h s7Z hy x7 hx _ hmem
  rw [show B7 (s7P, 0) = suTwoWitness from dipole_apply_plus s7P_ne_s7M 0 suTwoWitness] at this
  exact suTwoWitness_ne_zero this

#print axioms bondEnergy_loopField_pos
#print axioms cStar_loopField_eq_zero
#print axioms B7_not_axial
#print axioms loopField_div_eq_zero
#print axioms Q_loopField_fibre
#print axioms Q_loopField_constr
#print axioms fullC_loopField
#print axioms loopField_mem_fibre
#print axioms cStar_loopField_le_zero
#print axioms loopField_axial
#print axioms loopField_axial_gen
#print axioms loopField_axial_fibre
#print axioms loopField_dropped
#print axioms loopField_dropped_fibre
#print axioms targetFibreClauses_refuted
#print axioms targetAt_refuted
#print axioms nil_target_refuted
#print axioms uniform_target_refuted

end AdalyFormal.Balaban.NilLevelTarget
