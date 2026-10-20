/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BlockedGaugeWitness

set_option autoImplicit false
set_option maxRecDepth 40000

/-!
# `Ū` GENUINELY READS THE BLOCK — the separation from the degenerate control

`BlockedGaugeWitness.blockedGauge_trivialLogExp` shows a `LogExpAd` exists for which
`Ū(c) = U(c)` exactly, and `blockedGauge_const` shows the whole CONSTANT family fails to separate
the two (on constants both give `U(c)`, because every (0.4) loop has zero net winding). So the
outstanding question is whether the (0.4) object EVER differs from the bare coarse holonomy.

**It does.** This module exhibits a non-flat configuration on a genuine `4`-sites-per-direction
periodic lattice with `ell = 2` — so `|B(c_-)| = 8 = ell^d = 2^3` and Bałaban's `L^{-d}` weight IS
the block-average normalisation, exactly as printed — and proves

  `Ū(c) ≠ U(c)`,  equivalently  `blockedGauge ratLogExp 2 Uw cw ≠ blockedGauge (trivial…) 2 Uw cw`.

## Method, and why it is not a numerical bluff

`ℚ` does NOT kernel-reduce in this Lean (`decide` gets stuck on `Rat.add`/`Rat.inv`; measured).
So the proof does **not** evaluate the 52 loop holonomies. It is structural:

1. the (0.4) loop's `log` splits as `fwdSum f c_- Γ + fwdSum f x [seg] − fwdSum f c_+ Γ′ −
   fwdSum f c_- [seg]` (`toAdd_loopSteps`), using only `holonomy_append`/`holonomy_revSteps`;
2. the two `[seg]` terms vanish because `f` is supported on a bond of direction `1` while the
   coarse bond runs in direction `0`;
3. the `Γ′` term vanishes because every bond `Γ′` traverses sits in `B(c_+)` — a **`decide`d,
   finite, ℚ-free** statement about `Fin`/`List` data (`gammaPrime_avoids`);
4. so every loop's `log` equals `fwdSum f c_- Γ ≥ 0`, and at the single site `x₀ = (0,1,0)` the
   unique contour is `[(1,true)]`, giving exactly `1`;
5. positivity of the whole weighted sum then follows, with no rational arithmetic evaluated.

The `decide`s carry only enumeration facts (`blockOf`, `contourFamily`, bond lists) — never a
value of the object under test.
-/

namespace AdalyFormal.Balaban.BlockedGauge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)

variable {L : PeriodicLatticeExtent}

/-! ## §1. Forward-path bond bookkeeping for an abelian `ofAdd`-configuration -/

/-- The bonds a FORWARD-ONLY step list traverses, in order. -/
def fwdBonds (y : PeriodicLatticeSite L) :
    List (Fin 3 × Bool) → List (PeriodicLatticeEdge L)
  | [] => []
  | st :: rest => (y, st.1) :: fwdBonds (periodicLatticeStep y st) rest

/-- The additive holonomy of a forward-only path in `Multiplicative ℚ`. -/
def fwdSum (f : PeriodicLatticeEdge L → ℚ) (y : PeriodicLatticeSite L) :
    List (Fin 3 × Bool) → ℚ
  | [] => 0
  | st :: rest => f (y, st.1) + fwdSum f (periodicLatticeStep y st) rest

/-- All steps of a contour of `G(y,x)` are FORWARD (p.252's contours only step in the direction of
the displacement, and on a block all displacements are non-negative). -/
def AllForward (s : List (Fin 3 × Bool)) : Prop := ∀ st ∈ s, st.2 = true

theorem allForward_replicate (μ : Fin 3) (k : ℕ) :
    AllForward (List.replicate k (μ, true)) := by
  intro st hst
  rw [List.eq_of_mem_replicate hst]

theorem allForward_append {s t : List (Fin 3 × Bool)} (hs : AllForward s) (ht : AllForward t) :
    AllForward (s ++ t) := by
  intro st hst
  rcases List.mem_append.mp hst with h | h
  · exact hs st h
  · exact ht st h

theorem allForward_contourSteps (π : Equiv.Perm (Fin 3)) (y x : PeriodicLatticeSite L) :
    AllForward (contourSteps π y x) :=
  allForward_append (allForward_replicate _ _)
    (allForward_append (allForward_replicate _ _) (allForward_replicate _ _))

theorem allForward_straightSeg (ν : Fin 3) (m : ℕ) : AllForward (straightSeg ν m) :=
  allForward_replicate ν m

/-- `toAdd` of a forward-only holonomy is the bond sum. -/
theorem toAdd_holonomy_fwd (f : PeriodicLatticeEdge L → ℚ) (y : PeriodicLatticeSite L)
    (s : List (Fin 3 × Bool)) (hs : AllForward s) :
    Multiplicative.toAdd
        (periodicPathHolonomy (fun b => Multiplicative.ofAdd (f b)) y s) = fwdSum f y s := by
  induction s generalizing y with
  | nil => rfl
  | cons st rest ih =>
      have hst : st.2 = true := hs st (List.mem_cons_self ..)
      have hrest : AllForward rest := fun a ha => hs a (List.mem_cons_of_mem _ ha)
      simp only [periodicPathHolonomy, hst, if_true, fwdSum]
      rw [← ih (periodicLatticeStep y st) hrest]
      rfl

theorem fwdSum_append (f : PeriodicLatticeEdge L → ℚ) (y : PeriodicLatticeSite L)
    (s t : List (Fin 3 × Bool)) :
    fwdSum f y (s ++ t) = fwdSum f y s + fwdSum f (periodicPathEndpoint y s) t := by
  induction s generalizing y with
  | nil => simp [fwdSum, periodicPathEndpoint]
  | cons st rest ih =>
      simp only [List.cons_append, fwdSum, periodicPathEndpoint, ih]
      ring

/-- A bond the path never traverses cannot contribute. -/
theorem fwdSum_eq_zero (f : PeriodicLatticeEdge L → ℚ) (y : PeriodicLatticeSite L)
    (s : List (Fin 3 × Bool)) (h : ∀ b ∈ fwdBonds y s, f b = 0) : fwdSum f y s = 0 := by
  induction s generalizing y with
  | nil => rfl
  | cons st rest ih =>
      simp only [fwdSum]
      rw [h (y, st.1) (List.mem_cons_self ..),
        ih (periodicLatticeStep y st) (fun b hb => h b (List.mem_cons_of_mem _ hb)), add_zero]

theorem fwdSum_nonneg (f : PeriodicLatticeEdge L → ℚ) (hf : ∀ b, 0 ≤ f b)
    (y : PeriodicLatticeSite L) (s : List (Fin 3 × Bool)) : 0 ≤ fwdSum f y s := by
  induction s generalizing y with
  | nil => exact le_refl 0
  | cons st rest ih => exact add_nonneg (hf _) (ih (periodicLatticeStep y st))

/-- Every bond of a straight `ν`-segment has direction `ν`. -/
theorem fwdBonds_straightSeg_dir (y : PeriodicLatticeSite L) (ν : Fin 3) (m : ℕ) :
    ∀ b ∈ fwdBonds y (straightSeg ν m), b.2 = ν := by
  induction m generalizing y with
  | zero => intro b hb; simp [fwdBonds, straightSeg] at hb
  | succ m ih =>
      intro b hb
      rw [straightSeg, List.replicate_succ] at hb
      simp only [fwdBonds, List.mem_cons] at hb
      rcases hb with rfl | hb
      · rfl
      · exact ih (periodicLatticeStep y (ν, true)) b hb

/-- **The (0.4) loop's `log`, split into four bond sums.** No rational arithmetic; pure
`holonomy_append` / `holonomy_revSteps`. -/
theorem toAdd_loopSteps (f : PeriodicLatticeEdge L → ℚ) (ell : ℕ) (c : CoarseBond L)
    (x : PeriodicLatticeSite L) {Γ Γ' : List (Fin 3 × Bool)}
    (hΓf : AllForward Γ) (hΓ'f : AllForward Γ')
    (hΓ : periodicPathEndpoint c.1 Γ = x)
    (hΓ' : periodicPathEndpoint (cPlus ell c) Γ' = shiftBy x c.2 ell) :
    Multiplicative.toAdd (periodicPathHolonomy (fun b => Multiplicative.ofAdd (f b)) c.1
        (loopSteps ell c.2 Γ Γ'))
      = fwdSum f c.1 Γ + fwdSum f x (straightSeg c.2 ell)
        - fwdSum f (cPlus ell c) Γ' - fwdSum f c.1 (straightSeg c.2 ell) := by
  set U : PeriodicLinkConfiguration (Multiplicative ℚ) L :=
    fun b => Multiplicative.ofAdd (f b) with hU
  have hrevΓ' : periodicPathHolonomy U (shiftBy x c.2 ell) (revSteps Γ')
      = (periodicPathHolonomy U (cPlus ell c) Γ')⁻¹ := by
    have := holonomy_revSteps U (cPlus ell c) Γ'
    rwa [hΓ'] at this
  have hrevSeg : periodicPathHolonomy U (cPlus ell c) (revSteps (straightSeg c.2 ell))
      = (periodicPathHolonomy U c.1 (straightSeg c.2 ell))⁻¹ := by
    have := holonomy_revSteps U c.1 (straightSeg c.2 ell)
    rwa [endpoint_straightSeg, ← cPlus] at this
  have hendRev : periodicPathEndpoint (shiftBy x c.2 ell) (revSteps Γ') = cPlus ell c := by
    have := endpoint_revSteps (cPlus ell c) Γ'
    rwa [hΓ'] at this
  simp only [loopSteps]
  rw [holonomy_append, hΓ, holonomy_append, endpoint_straightSeg, holonomy_append,
    hendRev, hrevΓ', hrevSeg]
  simp only [toAdd_mul, toAdd_inv]
  rw [toAdd_holonomy_fwd f c.1 Γ hΓf, toAdd_holonomy_fwd f x _ (allForward_straightSeg _ _),
    toAdd_holonomy_fwd f (cPlus ell c) Γ' hΓ'f,
    toAdd_holonomy_fwd f c.1 _ (allForward_straightSeg _ _)]
  ring


/-! ## §2. The concrete witness: `4` sites per direction, `ell = 2`, one excited bond

`witLw` gives `4` sites in every direction, so `|B(y)| = 2^3 = 8 = ell^d` and the `L^{-d}` weight
of (0.4) is EXACTLY the block average — the faithful normalisation, not a rescaling. The coarse
bond runs in direction `0`; the single excited bond runs in direction `1`, at the origin. -/

/-- `4` sites in each of the three directions. -/
abbrev witLw : PeriodicLatticeExtent := fun _ => 3

/-- The origin. -/
def wBase : PeriodicLatticeSite witLw := fun _ => 0

/-- The single excited bond: direction `1`, at the origin. -/
def wB0 : PeriodicLatticeEdge witLw := (wBase, 1)

/-- A single-bond (maximally non-flat) field. -/
def wf : PeriodicLatticeEdge witLw → ℚ := fun b => if b = wB0 then 1 else 0

/-- The corresponding `Multiplicative ℚ` link configuration. -/
def wU : PeriodicLinkConfiguration (Multiplicative ℚ) witLw := fun b => Multiplicative.ofAdd (wf b)

/-- The coarse bond under test: from the origin, in direction `0`, of length `ell = 2`. -/
def wc : CoarseBond witLw := (wBase, 0)

/-- The one block site whose contour is forced through the excited bond. -/
def wX0 : PeriodicLatticeSite witLw := fun μ => if μ = 1 then 1 else 0

theorem wf_nonneg : ∀ b, 0 ≤ wf b := by
  intro b; rw [wf]; split <;> norm_num

theorem wf_dir_zero {b : PeriodicLatticeEdge witLw} (h : b.2 = 0) : wf b = 0 := by
  rw [wf]
  have : b ≠ wB0 := by
    intro hb
    rw [hb] at h
    exact absurd h (by decide)
  simp [this]

theorem wf_wB0 : wf wB0 = 1 := by simp [wf]

theorem w_dvd : (2 : ℕ) ∣ (witLw wc.2 + 1) := by decide

theorem w_coarse : wc.1 ∈ CoarseLattice witLw 2 := by decide

/-- **The `decide`d support fact.** No contour of `G(c_+, x′)` ever traverses the excited bond:
those contours live in `B(c_+)`, whose direction-`0` coordinates are `2, 3`, while the excited bond
sits at the origin. Enumerated over `Fin`/`List` data only — no rational arithmetic. -/
theorem gammaPrime_avoids :
    ∀ x ∈ blockOf wc.1 2, ∀ Γ' ∈ contourFamily (cPlus 2 wc) (shiftBy x wc.2 2),
      wB0 ∉ fwdBonds (cPlus 2 wc) Γ' := by decide

theorem wX0_mem : wX0 ∈ blockOf wc.1 2 := by decide

theorem wfam_X0 : contourFamily wc.1 wX0 = {[((1 : Fin 3), true)]} := by decide

theorem wfam_X0' : contourFamily (cPlus 2 wc) (shiftBy wX0 wc.2 2) = {[((1 : Fin 3), true)]} := by
  decide

/-- Straight `ν = 0` segments never see the excited bond. -/
theorem fwdSum_seg_zero (y : PeriodicLatticeSite witLw) (m : ℕ) :
    fwdSum wf y (straightSeg wc.2 m) = 0 :=
  fwdSum_eq_zero wf y _ (fun b hb => wf_dir_zero (fwdBonds_straightSeg_dir y wc.2 m b hb))

/-- **Every (0.4) loop's `log` reduces to the FORWARD contour's bond sum.** -/
theorem wloop_log {x : PeriodicLatticeSite witLw} (hx : x ∈ blockOf wc.1 2)
    {Γ : List (Fin 3 × Bool)} (hΓ : Γ ∈ contourFamily wc.1 x)
    {Γ' : List (Fin 3 × Bool)} (hΓ' : Γ' ∈ contourFamily (cPlus 2 wc) (shiftBy x wc.2 2)) :
    ratLogExp.log (periodicPathHolonomy wU wc.1 (loopSteps 2 wc.2 Γ Γ')) = fwdSum wf wc.1 Γ := by
  have hle : ∀ μ : Fin 3, (wc.1 μ).val ≤ (x μ).val := fun μ => (mem_blockOf.mp hx μ).1
  have hle' : ∀ μ : Fin 3, ((cPlus 2 wc) μ).val ≤ ((shiftBy x wc.2 2) μ).val :=
    fun μ => shiftBy_le_shiftBy (by norm_num) w_dvd w_coarse hx μ
  have hΓfwd : AllForward Γ := by
    simp only [contourFamily, Finset.mem_image, Finset.mem_univ, true_and] at hΓ
    obtain ⟨π, rfl⟩ := hΓ
    exact allForward_contourSteps π _ _
  have hΓ'fwd : AllForward Γ' := by
    simp only [contourFamily, Finset.mem_image, Finset.mem_univ, true_and] at hΓ'
    obtain ⟨π, rfl⟩ := hΓ'
    exact allForward_contourSteps π _ _
  have hsplit := toAdd_loopSteps wf 2 wc x hΓfwd hΓ'fwd
    (endpoint_of_mem_contourFamily hle hΓ) (endpoint_of_mem_contourFamily hle' hΓ')
  have hzero' : fwdSum wf (cPlus 2 wc) Γ' = 0 :=
    fwdSum_eq_zero wf _ _ (fun b hb => by
      rw [wf]
      have hne : b ≠ wB0 := by
        intro hbe
        exact (gammaPrime_avoids x hx Γ' hΓ') (hbe ▸ hb)
      simp [hne])
  show Multiplicative.toAdd (periodicPathHolonomy wU wc.1 (loopSteps 2 wc.2 Γ Γ')) = _
  rw [show wU = (fun b => Multiplicative.ofAdd (wf b)) from rfl, hsplit, hzero',
    fwdSum_seg_zero, fwdSum_seg_zero]
  ring

theorem winner_nonneg {x : PeriodicLatticeSite witLw} (hx : x ∈ blockOf wc.1 2) :
    0 ≤ innerAvg ratLogExp 2 wU wc x := by
  simp only [innerAvg]
  refine Finset.sum_nonneg (fun Γ hΓ => ?_)
  rw [smul_eq_mul]
  refine mul_nonneg (by positivity) ?_
  refine Finset.sum_nonneg (fun Γ' hΓ' => ?_)
  rw [smul_eq_mul]
  refine mul_nonneg (by positivity) ?_
  rw [wloop_log hx hΓ hΓ']
  exact fwdSum_nonneg wf wf_nonneg _ _

/-- At `x₀ = (0,1,0)` the contour family is the singleton `[(1,true)]`, which traverses the excited
bond exactly once, so the inner average is exactly `1`. -/
theorem winner_X0 : innerAvg ratLogExp 2 wU wc wX0 = 1 := by
  simp only [innerAvg, wfam_X0, wfam_X0', Finset.sum_singleton, Finset.card_singleton]
  rw [wloop_log wX0_mem (by rw [wfam_X0]; exact Finset.mem_singleton_self _)
    (by rw [wfam_X0']; exact Finset.mem_singleton_self _)]
  have hb : fwdSum wf wc.1 [((1 : Fin 3), true)] = 1 := by
    simp only [fwdSum]
    rw [show ((wc.1, (1 : Fin 3)) : PeriodicLatticeEdge witLw) = wB0 from rfl, wf_wB0]
    norm_num
  rw [hb]
  norm_num

/-- **The (0.4) exponent is STRICTLY POSITIVE on this configuration.** -/
theorem wexponent_pos :
    0 < ∑ x ∈ blockOf wc.1 2, (((2 : ℕ) : ℚ) ^ 3)⁻¹ • innerAvg ratLogExp 2 wU wc x := by
  refine Finset.sum_pos' (fun x hx => ?_) ⟨wX0, wX0_mem, ?_⟩
  · rw [smul_eq_mul]
    exact mul_nonneg (by norm_num) (winner_nonneg hx)
  · rw [smul_eq_mul, winner_X0]
    norm_num

/-- **THE SEPARATION: `Ū(c) ≠ U(c)`.**

The blocked gauge field of CMP109 (0.4) is NOT the bare coarse holonomy. Consequently the
degenerate `trivialLogExp` inhabitant of `LogExpAd` — which satisfies every hypothesis of
`blockedGauge_gauge` and yields `Ū(c) = U(c)` — is a DIFFERENT map from the (0.4) object at the
abelian witness, so `gaugeCovariant_blockedGauge` is not a theorem about a projection that forgets
the block. -/
theorem blockedGauge_ne_coarseHolonomy :
    blockedGauge ratLogExp 2 wU wc ≠ periodicPathHolonomy wU wc.1 (straightSeg wc.2 2) := by
  have hH : Multiplicative.toAdd (periodicPathHolonomy wU wc.1 (straightSeg wc.2 2)) = 0 := by
    rw [show wU = (fun b => Multiplicative.ofAdd (wf b)) from rfl,
      toAdd_holonomy_fwd wf _ _ (allForward_straightSeg _ _)]
    exact fwdSum_seg_zero _ _
  intro hcon
  have hE := wexponent_pos
  have : Multiplicative.toAdd (blockedGauge ratLogExp 2 wU wc)
      = (∑ x ∈ blockOf wc.1 2, (((2 : ℕ) : ℚ) ^ 3)⁻¹ • innerAvg ratLogExp 2 wU wc x)
        + Multiplicative.toAdd (periodicPathHolonomy wU wc.1 (straightSeg wc.2 2)) := by
    simp only [blockedGauge, toAdd_mul]
    rfl
  rw [hH, add_zero] at this
  rw [hcon, hH] at this
  exact (ne_of_lt hE) this

/-- The bare coarse holonomy is trivial for this configuration (the coarse bond runs in direction
`0`, the excited bond in direction `1`), so `Ū(c) ≠ 1` here. -/
theorem wH_eq_one : periodicPathHolonomy wU wc.1 (straightSeg wc.2 2) = 1 := by
  apply Multiplicative.toAdd.injective
  rw [show wU = (fun b => Multiplicative.ofAdd (wf b)) from rfl,
    toAdd_holonomy_fwd wf _ _ (allForward_straightSeg _ _)]
  exact fwdSum_seg_zero _ _

/-- **Non-constancy of `Ū`, with EVERY parameter pinned** — no existential over free data, unlike
`blockedGauge_nonconstant` (S91: an `∃` over the lattice/bond/configurations lets the prover choose
the easiest instance). Here the lattice, the coarse bond and both configurations are named `def`s
fixed above. -/
theorem blockedGauge_nonconstant_pinned :
    blockedGauge ratLogExp 2 (fun _ => (1 : Multiplicative ℚ)) wc
      ≠ blockedGauge ratLogExp 2 wU wc := by
  rw [blockedGauge_trivialU ratLogExp rfl rfl]
  intro h
  exact blockedGauge_ne_coarseHolonomy (by rw [← h, wH_eq_one])

/-- The same statement in the form that matters for the control: the (0.4) object and the
degenerate one are DIFFERENT maps. -/
theorem blockedGauge_ne_trivialLogExp :
    blockedGauge ratLogExp 2 wU wc ≠ blockedGauge (trivialLogExp (Multiplicative ℚ) ℚ) 2 wU wc := by
  rw [blockedGauge_trivialLogExp]
  exact blockedGauge_ne_coarseHolonomy

end AdalyFormal.Balaban.BlockedGauge
