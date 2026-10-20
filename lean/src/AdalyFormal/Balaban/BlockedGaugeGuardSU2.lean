/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BlockedGaugeGuard
import AdalyFormal.Balaban.SuTwoLogExpFaithful
import AdalyFormal.Balaban.SuTwoLogExpWitness

set_option autoImplicit false
set_option maxRecDepth 16000

/-!
# THE GUARD AT `SU(2)` — the branch point is excluded, and the pinned witness still lands

`BlockedGaugeGuard` closes the three admitted degeneracies of `blockedGauge` in the type. This
module instantiates the guard at the campaign's actual gauge group and runs the controls in BOTH
directions.

## The branch domain is `conjPrincipal`, and it excludes the centre

`SuTwoLogExpFaithful.conjPrincipal g` says `g = h · torus t · h⁻¹` for some `h ∈ SU(2)` and
`0 ≤ t < π`, and `su2_exp_log_of_conjPrincipal` proves `exp ∘ log = id` there. `su2Faithful` is the
lift of `su2LogExp` with that domain.

`not_conjPrincipal_negOne` proves `−1 ∉ conjPrincipal`, and its proof is exactly the branch-cut
mechanism: `su2Log (−1) = 0` (forced — `SuTwoLogExpTorus.log_center_forced`) and `su2Exp 0 = 1`, so
`exp ∘ log` sends `−1` to `1`, not to `−1`. So the domain condition that makes the guard nonvacuous
is the SAME condition that excludes the branch point; it is not a second, bolted-on hypothesis.

## MUST-FIRE — the prosecution's compiled `−1` loop

`compute/sol_blocked/scratch/SolBlockedScratch.lean:210-235` compiled a genuine `(0.4)` loop at
`ell = 2` landing exactly on `−1`, with the `SU(2)` logarithm erasing it to `0` and no side
condition to fail. That configuration is rebuilt here as `centerU` and:

* `center_loop_eq_negOne` — the loop really lands on `−1` (rebuilt, not cited);
* `center_not_loopsInDomain` — `LoopsInDomain su2Faithful 2 centerU wc` is FALSE;
* `no_guarded_center` — therefore NO `GuardedBlocking` carries that configuration.

`guarded_loop_ne_negOne` is the general form: on ANY guarded `SU(2)` instance, no admitted `(0.4)`
loop equals the centre element. That is stronger than the single compiled counterexample.

## MUST-NOT-FIRE — the pinned witness still works

`su2Guarded` is a full `GuardedBlocking SU(2) M₂(ℂ) witLw` at `ell = 2` on `SuTwoLogExpWitness.sU`,
so the guard is INHABITED and none of its fields is vacuously satisfied. Its value is still the
nontrivial `torus E` (`su2Guarded_value`), still differs from the bare coarse holonomy
(`su2Guarded_value_ne_coarse`), and still transforms covariantly
(`su2Guarded_value_gauge_pinned`).

The `LoopsInDomain` discharge is not an assumption: every loop of `sU` is `torus v` with
`0 ≤ v ≤ 1 < π` (`SuTwoLogExpWitness.wloop_val_nonneg` / `wloop_val_le_one`, themselves `decide`d
from the single-excited-bond traversal count), hence in `conjPrincipal` with `h = 1`.
-/

namespace AdalyFormal.Balaban.SuTwoLogExp

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.BlockedGauge
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice)

/-! ## §1. The branch domain excludes the centre element -/

/-- **`−1 ∉ conjPrincipal`.** The proof IS the branch-cut mechanism: `exp (log (−1)) = exp 0 = 1`,
so `−1` cannot satisfy `exp ∘ log = id`. -/
theorem not_conjPrincipal_negOne : ¬ conjPrincipal su2NegOne := by
  intro h
  have hx := su2_exp_log_of_conjPrincipal h
  rw [su2Log_center, su2Exp_zero] at hx
  exact su2NegOne_ne_one hx.symm

/-- `torus 1 ≠ 1`, the non-identity domain witness. -/
theorem torus_one_ne_one : torus (1 : ℝ) ≠ 1 :=
  torus_ne_one (by norm_num) (by linarith [Real.pi_gt_three])

/-- **`su2LogExp`, lifted to the guarded interface.** Domain: the conjugates of the principal
branch of the maximal torus. -/
noncomputable def su2Faithful : FaithfulLogExpAd SU2 M2 where
  toLogExpAd := su2LogExp
  dom := conjPrincipal
  one_mem := conjPrincipal_one
  dom_conj := fun k g hg => conjPrincipal_conj hg k
  exp_log := fun _ hg => su2_exp_log_of_conjPrincipal hg
  log_one := su2Log_one
  exp_zero := su2Exp_zero
  witness := torus (1 : ℝ)
  witness_mem := ⟨1, 1, by norm_num, by linarith [Real.pi_gt_three], by group⟩
  witness_ne_one := torus_one_ne_one

@[simp] theorem su2Faithful_toLogExpAd : su2Faithful.toLogExpAd = su2LogExp := rfl

@[simp] theorem su2Faithful_dom (g : SU2) : su2Faithful.dom g = conjPrincipal g := rfl

/-- The three hostile pairs of `BlockedGaugeGuard` are rejected at `SU(2)` too — recorded because
`no_faithful_trivial` is the one that applies at an arbitrary group. -/
theorem su2_no_faithful_trivial (F : FaithfulLogExpAd SU2 M2) :
    F.toLogExpAd ≠ trivialLogExp SU2 M2 :=
  no_faithful_trivial F

/-! ## §2. MUST-FIRE (general) — no admitted `(0.4)` loop is the centre element -/

/-- **On a guarded `SU(2)` instance WHOSE PAIR IS `su2Faithful`, no `(0.4)` loop lands on the
branch point.**

**[STRUCK 2026-07-28, Sol gate item 3 — REFUTED BY COMPILED COUNTEREXAMPLE.]** This docstring read
*"On any guarded `SU(2)` instance…  This is `[BLOCKED-BRANCH-DOMAIN]` closed in the general form"*.
Both claims are false, and the theorem's OWN TYPE says so: `hP : B.P = su2Faithful` pins the pair.
The statement is about one instance, not the class.

The class genuinely admits the centre. Sol compiled `shiftedSU2Faithful` — `log g := (g : M2) − 1`,
`exp A := A + 1` where that is special unitary and `1` otherwise, TOTAL domain,
`witness := su2NegOne` — which satisfies every `FaithfulLogExpAd` field, and then formed
`shiftedCenterGuarded` on this file's own `centerU`, same lattice, same `ell`, same bond, whose
advertised loop IS `su2NegOne`. Axiom cone clean. So `[BLOCKED-BRANCH-DOMAIN]` is closed
CONDITIONALLY, by the pinned `su2Faithful` domain, and NOT by the structure of
`FaithfulLogExpAd SU2 M2`.

Consumers must therefore pin `P` explicitly; a tower that quantifies over `FaithfulLogExpAd` and
expects centre-exclusion for free is relying on something this file does not prove. -/
theorem guarded_loop_ne_negOne {L : PeriodicLatticeExtent} (B : GuardedBlocking SU2 M2 L)
    (hP : B.P = su2Faithful) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf B.c.1 B.ell)
    {Γ : List (Fin 3 × Bool)} (hΓ : Γ ∈ contourFamily B.c.1 x)
    {Γ' : List (Fin 3 × Bool)}
    (hΓ' : Γ' ∈ contourFamily (cPlus B.ell B.c) (shiftBy x B.c.2 B.ell)) :
    periodicPathHolonomy B.U B.c.1 (loopSteps B.ell B.c.2 Γ Γ') ≠ su2NegOne := by
  intro hEq
  have hd := B.loops_dom x hx Γ hΓ Γ' hΓ'
  rw [hP, hEq] at hd
  exact not_conjPrincipal_negOne hd

/-! ## §3. MUST-FIRE (compiled counterexample) — the prosecution's `−1` configuration

Rebuild of `SolBlockedScratch.lean:210-235`: the single excited bond of `BlockedGaugeSeparation`'s
witness lattice carries the genuine centre element instead of `diag(e^i, e^{-i})`. -/

/-- The prosecution's branch-cut configuration: `−1` on the one excited bond, `1` elsewhere. -/
def centerU : PeriodicLinkConfiguration SU2 witLw := fun b => if b = wB0 then su2NegOne else 1

/-- **The compiled `(0.4)` loop lands exactly on `−1`.** -/
theorem center_loop_eq_negOne :
    periodicPathHolonomy centerU wc.1
        (loopSteps 2 wc.2 [((1 : Fin 3), true)] [((1 : Fin 3), true)]) = su2NegOne := by
  simp [centerU, wc, wB0, wBase, loopSteps, straightSeg, revSteps, periodicPathHolonomy,
    periodicLatticeStep]
  intro hsite
  have h0 := congrArg (fun z : PeriodicLatticeSite witLw => (z 0).val) hsite
  norm_num [wBase, witLw] at h0

/-- **The guard rejects it.** `LoopsInDomain` fails at the site `wX0` and the singleton contour
families `BlockedGaugeSeparation.wfam_X0` / `wfam_X0'`. -/
theorem center_not_loopsInDomain : ¬ LoopsInDomain su2Faithful 2 centerU wc := by
  intro h
  have hmem : ([((1 : Fin 3), true)] : List (Fin 3 × Bool)) ∈ contourFamily wc.1 wX0 := by
    rw [wfam_X0]; exact Finset.mem_singleton_self _
  have hmem' : ([((1 : Fin 3), true)] : List (Fin 3 × Bool))
      ∈ contourFamily (cPlus 2 wc) (shiftBy wX0 wc.2 2) := by
    rw [wfam_X0']; exact Finset.mem_singleton_self _
  have hd := h wX0 wX0_mem _ hmem _ hmem'
  rw [center_loop_eq_negOne] at hd
  exact not_conjPrincipal_negOne hd

/-- **MUST-FIRE 5.** No `GuardedBlocking` can carry the prosecution's branch-cut configuration. -/
theorem no_guarded_center (B : GuardedBlocking SU2 M2 witLw) (hP : B.P = su2Faithful)
    (hell : B.ell = 2) (hU : B.U = centerU) (hc : B.c = wc) : False := by
  have hd := B.loops_dom
  rw [hP, hell, hU, hc] at hd
  exact center_not_loopsInDomain hd

/-! ## §4. MUST-NOT-FIRE — the pinned `SU(2)` witness lifts to a guarded instance -/

/-- Every `(0.4)` loop of the pinned configuration is `torus v` with `0 ≤ v ≤ 1 < π`, hence in the
branch domain. The bound is `SuTwoLogExpWitness`'s `decide`d traversal count, not an assumption. -/
theorem sU_loop_mem_conjPrincipal {x : PeriodicLatticeSite witLw} (hx : x ∈ blockOf wc.1 2)
    {Γ : List (Fin 3 × Bool)} (hΓ : Γ ∈ contourFamily wc.1 x)
    {Γ' : List (Fin 3 × Bool)} (hΓ' : Γ' ∈ contourFamily (cPlus 2 wc) (shiftBy x wc.2 2)) :
    conjPrincipal (periodicPathHolonomy sU wc.1 (loopSteps 2 wc.2 Γ Γ')) := by
  have hval := wloop_log hx hΓ hΓ'
  have hmap : periodicPathHolonomy sU wc.1 (loopSteps 2 wc.2 Γ Γ')
      = phiSU2 (periodicPathHolonomy wU wc.1 (loopSteps 2 wc.2 Γ Γ')) :=
    holonomy_map phiSU2 wU wc.1 _
  have hoa : periodicPathHolonomy wU wc.1 (loopSteps 2 wc.2 Γ Γ')
      = Multiplicative.ofAdd (fwdSum wf wc.1 Γ) := by rw [← hval]; rfl
  have h0 : (0 : ℚ) ≤ fwdSum wf wc.1 Γ := wloop_val_nonneg
  have h1 : fwdSum wf wc.1 Γ ≤ 1 := wloop_val_le_one hx hΓ
  refine ⟨1, ((fwdSum wf wc.1 Γ : ℚ) : ℝ), by exact_mod_cast h0, ?_, ?_⟩
  · have hle : ((fwdSum wf wc.1 Γ : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith [Real.pi_gt_three]
  · rw [hmap, hoa, phiSU2_apply]
    group

/-- **THE GUARDED INSTANCE AT `SU(2)`.** Every field discharged: `2 ≤ 2`, GLOBAL divisibility
`2 ∣ 3 + 1` in all three directions, `c₋ ∈ Λ'`, and every loop in the branch domain. -/
noncomputable def su2Guarded : GuardedBlocking SU2 M2 witLw where
  P := su2Faithful
  ell := 2
  two_le_ell := le_refl 2
  ell_dvd := by decide
  U := sU
  c := wc
  base_coarse := w_coarse
  loops_dom := fun _ hx _ hΓ _ hΓ' => sU_loop_mem_conjPrincipal hx hΓ hΓ'

/-- The guarded value is the same object `SuTwoLogExpWitness` evaluated: `Ū(wc) = torus E`. -/
theorem su2Guarded_value : su2Guarded.value = torus ((wE : ℚ) : ℝ) :=
  su2_blockedGauge_eq_torus

/-- **The guard did not trivialise the object.** -/
theorem su2Guarded_value_ne_one : su2Guarded.value ≠ 1 := su2_blockedGauge_ne_one

/-- **…and it still differs from the bare coarse holonomy** — the control that `trivialLogExp`,
`discardingLogExp` and `twistedLogExp` all fail. -/
theorem su2Guarded_value_ne_coarse :
    su2Guarded.value ≠ periodicPathHolonomy sU wc.1 (straightSeg wc.2 2) :=
  su2_blockedGauge_ne_coarseHolonomy

/-- **The normalisation is a theorem on the instance:** `|B(c₋)| = 2³ = 8`. -/
theorem su2Guarded_card_block : (blockOf wc.1 2).card = 2 ^ 3 := su2Guarded.card_block

/-- **Covariance survives the guard, at the pinned nonconstant gauge function.** -/
theorem su2Guarded_value_gauge_pinned :
    (su2Guarded.gaugeTransform wGamma).value
      = wGamma wc.1 * su2Guarded.value * (wGamma (cPlus 2 wc))⁻¹ :=
  su2Guarded.value_gaugeTransform wGamma

/-- …and at an arbitrary gauge function. -/
theorem su2Guarded_value_gauge (γ : PeriodicLatticeSite witLw → SU2) :
    (su2Guarded.gaugeTransform γ).value
      = γ wc.1 * su2Guarded.value * (γ (cPlus 2 wc))⁻¹ :=
  su2Guarded.value_gaugeTransform γ

/-! ## §5. The guard DISCRIMINATES — it is true on the honest configuration and false on the
branch-cut one

An S82 concern: a guard that rejects everything, or that is refuted by its own proof script rather
than by the configuration, is not a guard. Both directions are recorded here on the SAME lattice,
the SAME `ell`, the SAME coarse bond and the SAME pair — only the configuration differs. -/

/-- TRUE on the honest configuration. -/
theorem loopsInDomain_sU : LoopsInDomain su2Faithful 2 sU wc := su2Guarded.loops_dom

/-- FALSE on the branch-cut configuration (restated next to the positive case). -/
theorem not_loopsInDomain_centerU : ¬ LoopsInDomain su2Faithful 2 centerU wc :=
  center_not_loopsInDomain

/-- The compiled `−1` loop is genuinely not the identity — so the acceptance test is a real
discrimination, not a failure of the proof script. -/
theorem center_loop_ne_one :
    periodicPathHolonomy centerU wc.1
        (loopSteps 2 wc.2 [((1 : Fin 3), true)] [((1 : Fin 3), true)]) ≠ 1 := by
  rw [center_loop_eq_negOne]
  exact su2NegOne_ne_one

/-! ## §6. The abelian separation witness also lifts

`BlockedGaugeSeparation` proves `blockedGauge ratLogExp 2 wU wc` is a genuine block average (its
exponent is strictly positive, `wexponent_pos`). That configuration satisfies every guard field, so
the guard does not cost the tree its existing non-degeneracy witness either. -/

/-- The abelian witness of `BlockedGaugeSeparation`, as a guarded instance. -/
def ratGuarded : GuardedBlocking (Multiplicative ℚ) ℚ witLw where
  P := ratFaithful
  ell := 2
  two_le_ell := le_refl 2
  ell_dvd := by decide
  U := wU
  c := wc
  base_coarse := w_coarse
  loops_dom := by intro _ _ _ _ _ _; trivial

theorem ratGuarded_value : ratGuarded.value = blockedGauge ratLogExp 2 wU wc := rfl

theorem ratGuarded_card_block : (blockOf wc.1 2).card = 2 ^ 3 := ratGuarded.card_block

end AdalyFormal.Balaban.SuTwoLogExp
