/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.SplitBaseCase
import AdalyFormal.Balaban.TowerLawCovariant

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-!
# `WindowStokesGeneralU.lean` — the general-`U` leg of the split base case

## What this module settles

`SplitBaseCase.base_case_general_U` proves the split base case at EVERY background `U`, but
CONDITIONALLY on one named `Prop`:

    WindowStokesAnnihilates ℓ U := ∀ v, Q_ℓ(U) v = 0 → ∀ P', windowSum (d_U v) P' = 0 ,

proved there only at `U = 1`. That hypothesis is the only thing between the composed lemma's base
case and background-uniformity. This module attacks it as a build target and settles it:

1. **§1 — the exact identity.** `windowSum (d_U v) P' = ℓ⁴·(∂₁' Q_ℓ(1) v)(P') + windowSum(drift)(P')`
   at EVERY `U`, where `drift = RegularUPerturbation.curlDrift U v`. An identity, not an estimate.
2. **§2 — the defect energy bound.** `Σ_{P'} ‖windowSum(drift) P'‖² ≤ 32 α² ℓ⁷ bondEnergy v`,
   composed from counted factors only, vanishing quadratically as `α → 0`.
3. **§3 — `WindowStokesAnnihilates` IS FALSE** (`windowStokesAnnihilates_UstarOf_false`). Explicit
   witness on `witL7` at `ℓ = 2`, kernel-checked.
4. **§4 — the quantitative replacement** (`quantitative_base_case`), UNCONDITIONAL at every `U`:

       ℓ · (coarse curl energy of Q_ℓ(1) A)  ≤  2·⟨B, Δ_k B⟩ + 64·α²·bondEnergy A ,
       A := hjExtension_{ℓ,levels,U}(B) ,   α ≥ sup_b frobNorm(U b − 1) .

5. **§5 — no smallness threshold rescues the exact form** (`no_smallness_threshold`): for EVERY
   `α > 0` there is a background with `frobSupBond U ≤ α` at which the hypothesis fails. So the
   `O(α²)` defect of §4 is FORCED, not an artifact of the estimate.

## Why the refutation works (mechanism, before any code)

`windowSum` adds curl vectors based at DIFFERENT lattice sites with NO transport between them. At
`U = 1` that is harmless — the telescoping of `ThirdLevelStokes.stokes_flat` is exact and the sum
factors through `Q_ℓ`. At `U ≠ 1` the sum picks up `curlDrift U v`, a LOCAL object supported where
`U` is, not where `Q_ℓ(U) v` is. The two supports can be SEPARATED by a parity: `Q_ℓ`'s transport
contour `Γ_{y,x}` (CMP95 (1.7), as built in `Q1Real`) starts at a COARSE site `y` and does its
direction-`2` leg at coordinate `0` equal to `y 0`, which is even. A background supported on a
single direction-`2` link based at ODD coordinate `0` is therefore invisible to `Q_ℓ` at every
coarse bond and every block site at once, while the covariant curl at the adjacent plaquette sees
it in full.

## ⚠ HONEST SCOPE

* Everything is on the compatible torus (`0 < ℓ`, `∀ μ, ℓ ∣ L μ + 1`) — the standing scope of the
  faithful `Q` (MEMORY: torus-blockOf-truncation-artifact).
* §4's left-hand side carries the FLAT `Q_ℓ(1)` applied to the CORRECTED field `A`, not `Q_ℓ(U)`
  applied to `B`. Moving to `Q_ℓ(U) B` costs a bound on `Q_ℓ(U) − Q_ℓ(1)`; **§7 BUILDS that bound**
  (`norm_lineCoarse_cov_sub_flat_le_block`, constant `8α/ℓ³`, path length discharged at `4ℓ`),
  reusing `TowerLawCov.norm_RMap_hol_sub_self_le` — NOT rebuilt (LAW-19). What remains after §7 is
  the `bondEnergy` factor below, not the transport.
* §4's `bondEnergy A` factor is NOT controlled by `⟨B, Δ_k B⟩` — `SplitBaseCase` §6/§7 show `Δ_k`
  is blind to directions `bondEnergy` measures. That is the residual §4 leaves, and it is named,
  not hidden.
* `J = 0` throughout; `levels` abstract; torus proxy for `ℤ³` — standing campaign scope.
* `#print axioms` on EVERY declaration of this file, definitions included (§8 sweeps the
  remainder): expected `{propext, Classical.choice, Quot.sound}` or a subset.
-/

namespace AdalyFormal.Balaban.WindowStokesGeneralU

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU deltaKernelImageCovH)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette)
open AdalyFormal.Balaban.ThirdLevelStokes (windowSet windowPlaq coarseCurlSuTwo)
open AdalyFormal.Balaban.RegularUPerturbation (curlDrift curlDrift_apply curlDrift_trivialU
  plaqEnergy bondEnergy plaqEnergy_curlDrift_le plaqEnergy_nonneg bondEnergy_nonneg
  frobSupBond frobSupBond_nonneg frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.SplitBaseCase (windowSum windowSum_add windowSum_curl windowSum_energy_le
  coarseCurlEnergy coarseCurlEnergy_nonneg hsInner_self_eq_norm_sq WindowStokesAnnihilates
  lineCoarse_hjExtension windowCurlEnergy)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE EXACT DEFECT IDENTITY

At `U = 1` the window sum of fine curls IS `ℓ⁴` times the coarse curl of `Q_ℓ` (`stokes_flat`,
restated as `SplitBaseCase.windowSum_curl`). At general `U` the covariant curl differs from the flat
one by EXACTLY the per-bond drift `curlDrift` (`RegularUPerturbation.curlDrift_apply`, an identity,
not an estimate). Pushing that through the — linear — window sum gives the general-`U` Stokes
identity WITH its defect term made explicit and named. No hypothesis on `U`. -/

/-- The covariant curl splits as flat curl `+` drift, as plaquette FUNCTIONS. -/
theorem curl_eq_flat_add_drift
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) :
    (curlCovariantLM U v : PeriodicLatticePlaquette L → SuTwo)
      = (curlCovariantLM (trivialU L) v : PeriodicLatticePlaquette L → SuTwo)
        + curlDrift U v := by
  funext p
  show curlValueCovariant U v p
      = curlValueCovariant (trivialU L) v p + curlDrift U v p
  show curlValueCovariant U v p
      = curlValueCovariant (trivialU L) v p
        + (curlValueCovariant U v - curlValueCovariant (trivialU L) v) p
  rw [Pi.sub_apply]
  abel

/-- **THE GENERAL-`U` WINDOW STOKES IDENTITY, EXACT.**

    windowSum (d_U v) P'  =  ℓ⁴ • (∂₁' (Q_ℓ(1) v)) P'  +  windowSum (curlDrift U v) P' .

Every term is defined; the equality is an identity, valid at EVERY background `U`, every `ℓ > 0`,
every compatible torus, every `v`. The `U = 1` specialisation is `windowSum_curl` (the drift
vanishes, `curlDrift_trivialU`). The `Q` on the right is the FLAT `Q_ℓ(1)`; §4 pays the cost of
moving to `Q_ℓ(U)`. -/
theorem windowSum_curl_general {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) (p : CoarsePlaquette L ell) :
    windowSum (curlCovariantLM U v) p
      = ((ell : ℝ) ^ 4) • coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell v) p
        + windowSum (curlDrift U v) p := by
  rw [show (curlCovariantLM U v : PeriodicLatticePlaquette L → SuTwo)
        = (curlCovariantLM (trivialU L) v : PeriodicLatticePlaquette L → SuTwo)
          + curlDrift U v from curl_eq_flat_add_drift U v,
    windowSum_add, windowSum_curl hell hdvd v p]

#print axioms curl_eq_flat_add_drift
#print axioms windowSum_curl_general

/-! ## §2 — THE DEFECT ENERGY BOUND

The defect term is `windowSum` applied to `curlDrift`. Both factors already have sharp estimates in
the tree, and they compose with NO new analysis:

* `SplitBaseCase.windowSum_energy_le` : `Σ_{P'} ‖windowSum X P'‖² ≤ ℓ⁷ Σ_q ‖X q‖²` (counted:
  `ℓ⁵` window size × `ℓ²` multiplicity);
* `RegularUPerturbation.plaqEnergy_curlDrift_le` : `Σ_q ‖curlDrift U A q‖² ≤ 32 α² Σ_b ‖A b‖²`
  (counted: `8 = 4·2` from `(2αa+2αb)² ≤ 8α²(a²+b²)`, times `2+2` plaquette→bond incidences).

The composite constant `32 ℓ⁷` is therefore composed from counted factors only, and it VANISHES as
`α → 0` — quadratically. -/

/-- **THE DEFECT ENERGY BOUND.** `Σ_{P'} ‖windowSum (curlDrift U v) P'‖² ≤ 32 α² ℓ⁷ bondEnergy v`,
for any uniform per-bond holonomy-deviation bound `α`. -/
theorem windowSum_drift_energy_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    ∑ p : CoarsePlaquette L ell, ‖windowSum (curlDrift U v) p‖ ^ 2
      ≤ 32 * α ^ 2 * ((ell : ℝ) ^ 7) * bondEnergy v := by
  have h1 := windowSum_energy_le (L := L) (ell := ell) hdvd (curlDrift U v)
  have h2 : ∑ q : PeriodicLatticePlaquette L, ‖curlDrift U v q‖ ^ 2
      ≤ 32 * α ^ 2 * bondEnergy v := plaqEnergy_curlDrift_le U v α hα0 hα
  have h7 : (0 : ℝ) ≤ ((ell : ℝ) ^ 7) := by positivity
  calc ∑ p : CoarsePlaquette L ell, ‖windowSum (curlDrift U v) p‖ ^ 2
      ≤ ((ell : ℝ) ^ 7) * ∑ q : PeriodicLatticePlaquette L, ‖curlDrift U v q‖ ^ 2 := h1
    _ ≤ ((ell : ℝ) ^ 7) * (32 * α ^ 2 * bondEnergy v) := mul_le_mul_of_nonneg_left h2 h7
    _ = 32 * α ^ 2 * ((ell : ℝ) ^ 7) * bondEnergy v := by ring

/-- The same with the literal `sup_b frobNorm(U b − 1)`. -/
theorem windowSum_drift_energy_le_sup {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) :
    ∑ p : CoarsePlaquette L ell, ‖windowSum (curlDrift U v) p‖ ^ 2
      ≤ 32 * (frobSupBond U) ^ 2 * ((ell : ℝ) ^ 7) * bondEnergy v :=
  windowSum_drift_energy_le hdvd U v (frobSupBond U) (frobSupBond_nonneg U)
    (frobNorm_le_frobSupBond U)

#print axioms windowSum_drift_energy_le
#print axioms windowSum_drift_energy_le_sup

/-! ## §3 — THE REFUTATION: `WindowStokesAnnihilates` is FALSE at a non-flat background

`SplitBaseCase.base_case_general_U` is conditional on

    WindowStokesAnnihilates ℓ U := ∀ v, Q_ℓ(U) v = 0 → ∀ P', windowSum (d_U v) P' = 0 ,

proved there only at `U = 1`. This section proves it is FALSE, with an explicit witness.

**The mechanism, stated before the code.** The window sum of fine curls is a sum of vectors based at
DIFFERENT lattice sites, added with NO transport between them. At `U = 1` that is harmless: the
telescoping of `stokes_flat` is exact and the sum factors through `Q_ℓ`. At `U ≠ 1` the same sum
acquires the drift `curlDrift U v` (§1, an identity), and the drift is a LOCAL object — it is
supported wherever `U` is, not where `Q_ℓ(U) v` is. So one can place the background's non-triviality
on a link that

* NO transport path of `Q_ℓ(U)` ever traverses — hence `Q_ℓ(U)` is literally the flat `Q_ℓ(1)` on
  the relevant bonds, and a flat-kernel dipole stays in `ker Q_ℓ(U)`; while
* the covariant curl DOES traverse — hence the drift, and with it the window sum, is nonzero.

The separation is achieved by a PARITY: every transport path `Γ_{y,x}` of `Q_ℓ` starts at a COARSE
site `y` and does its direction-`2` leg at coordinate `0` equal to `y 0`, which is even. Putting the
background's single non-trivial link on a direction-`2` link based at ODD coordinate `0` makes it
invisible to `Q_ℓ` at every coarse bond and every block site, at once.

`witnessM = !![0,1;-1,0]` and `R(M) w = −w` (`CovariantOperators.RMap_witnessMElem`) supply the
non-flatness; nothing about the size of `U − 1` is used, and §5 shows the refutation survives
shrinking it. -/

open AdalyFormal.Balaban.ThirdLevelWitness (dipole dipole_apply_plus Q_dipole_zero witL7
  witL7_two_dvd)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero)
open AdalyFormal.Balaban.Q1Real (GammaPath straightSegment transportPath rZeroA
  periodicPathHolonomy_append periodicPathHolonomy_trivialU_eq_one)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.SplitBaseCase (a7 a7' a7_ne_a7')

/-! ### §3a — a reusable holonomy-triviality tool -/

/-- **If a predicate `P` is preserved by the forward `μ`-step and forces `U(·,μ) = 1`, then every
forward `μ`-run has trivial holonomy.** General in the group, the extent, the direction and the
predicate; this is the only induction the refutation needs, and it is stated once. -/
theorem hol_replicate_one {G : Type*} [Group G] {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration G L) (μ : Fin 3)
    (P : PeriodicLatticeSite L → Prop)
    (hP : ∀ z, P z → P (periodicLatticeStep z (μ, true)))
    (hU : ∀ z, P z → U (z, μ) = 1) :
    ∀ (n : ℕ) (z : PeriodicLatticeSite L), P z →
      periodicPathHolonomy U z (List.replicate n (μ, true)) = 1 := by
  intro n
  induction n with
  | zero => intro z _; rfl
  | succ m ih =>
    intro z hz
    rw [List.replicate_succ]
    show U (z, μ) *
      periodicPathHolonomy U (periodicLatticeStep z (μ, true)) (List.replicate m (μ, true)) = 1
    rw [hU z hz, one_mul]
    exact ih _ (hP z hz)

/-- The same for a `straightSegment` (which IS such a run, `List.replicate`). -/
theorem hol_straight_one {G : Type*} [Group G] {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration G L) (μ : Fin 3)
    (P : PeriodicLatticeSite L → Prop)
    (hP : ∀ z, P z → P (periodicLatticeStep z (μ, true)))
    (hU : ∀ z, P z → U (z, μ) = 1)
    (a b z : PeriodicLatticeSite L) (hz : P z) :
    periodicPathHolonomy U z (straightSegment a b μ) = 1 :=
  hol_replicate_one U μ P hP hU _ z hz

#print axioms hol_replicate_one
#print axioms hol_straight_one

/-! ### §3b — the witness data -/

/-- `(1, 0, 7)` — the base site of the single non-trivial link. Coordinate `0` is `1`, ODD, hence
never a coordinate of a level-`2` coarse site; coordinate `2` is `7`, so the forward `2`-shift lands
on `a7 = (1,0,0)`, the dipole's `+` site. -/
def qStar : PeriodicLatticeSite witL7 := fun ρ => if ρ = 0 then 1 else if ρ = 2 then 7 else 0

theorem qStar_shift2 : periodicLatticeShift qStar 2 = a7 := by decide

/-- **`U*(M)`** — the group element `M` on the single direction-`2` link based at `qStar`, `1` on
every other link. PARAMETRIC in `M`, so that §5 can shrink `M − 1` towards `0` without rebuilding
any of §3c/§3d. -/
noncomputable def UstarOf (M : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL7 :=
  fun e => if e = (qStar, 2) then M else 1

variable (M : Matrix.specialUnitaryGroup (Fin 2) ℂ)

theorem UstarOf_of_ne {e : PeriodicLatticeEdge witL7} (h : e ≠ (qStar, 2)) :
    UstarOf M e = 1 := if_neg h

theorem UstarOf_at : UstarOf M (qStar, 2) = M := if_pos rfl

/-- `U*(M)` is trivial on EVERY link whose direction is not `2`. -/
theorem UstarOf_dir_ne_two (z : PeriodicLatticeSite witL7) {ρ : Fin 3} (h : ρ ≠ 2) :
    UstarOf M (z, ρ) = 1 :=
  UstarOf_of_ne M (by simp [Prod.mk.injEq, h])

/-- `U*(M)` is trivial on every direction-`2` link based at a site whose coordinate `0` is not
`1`. -/
theorem UstarOf_coord (z : PeriodicLatticeSite witL7) (h : z 0 ≠ qStar 0) :
    UstarOf M (z, 2) = 1 :=
  UstarOf_of_ne M
    (by simp only [ne_eq, Prod.mk.injEq, not_and]; intro hz; exact absurd (hz ▸ rfl) h)

/-- **The witness field**: the direction-`0` dipole `+w` at `a7 = (1,0,0)`, `−w` at
`a7' = (1,0,1)` — the two sites differ only in coordinate `2`, by `0` vs `1`, which sit in the same
level-`2` window at every coarse site. -/
noncomputable def vDip : Bond witL7 → SuTwo := dipole a7 a7' 0 suTwoWitness

theorem vDip_off_dir (z : PeriodicLatticeSite witL7) {ρ : Fin 3} (h : ρ ≠ 0) : vDip (z, ρ) = 0 := by
  unfold vDip dipole
  rw [if_neg (by simp [Prod.mk.injEq, h]), if_neg (by simp [Prod.mk.injEq, h]), sub_self, zero_smul]

theorem vDip_at_a7 : vDip (a7, 0) = suTwoWitness :=
  dipole_apply_plus a7_ne_a7' 0 suTwoWitness

/-- **The dipole is in the FLAT kernel** — `Q_dipole_zero` (LAW-19: the reusable `ker Q_ℓ(1)` tool,
not rebuilt), same window argument as `SplitBaseCase.Bax_kerQ2` one direction over. -/
theorem vDip_kerQ_flat : lineCoarseRestrictCovLM (trivialU witL7) 2 vDip = 0 := by
  show lineCoarseRestrictCovLM (trivialU witL7) 2 (dipole a7 a7' 0 suTwoWitness) = 0
  refine Q_dipole_zero (ν := 2) 2 (by decide) (by decide) (fun y hy => ?_) suTwoWitness
  have h1 := mem_CoarseLattice.mp hy 2
  have h2 : (y 2).val < 8 := (y 2).isLt
  have hA : (a7 2).val = 0 := rfl
  have hB : (a7' 2).val = 1 := rfl
  rw [hA, hB]
  omega

#print axioms qStar_shift2
#print axioms UstarOf_dir_ne_two
#print axioms UstarOf_coord
#print axioms vDip_off_dir
#print axioms vDip_at_a7
#print axioms vDip_kerQ_flat

/-! ### §3c — `Q_2(U*(M))` IS BLIND TO `U*(M)` (the parity), so the dipole stays in its kernel -/

theorem hol_UstarOf_dir_ne_two {ρ : Fin 3} (hρ : ρ ≠ 2) (a b z : PeriodicLatticeSite witL7) :
    periodicPathHolonomy (UstarOf M) z (straightSegment a b ρ) = 1 :=
  hol_straight_one (UstarOf M) ρ (fun _ => True) (fun _ _ => trivial)
    (fun w _ => UstarOf_dir_ne_two M w hρ) a b z trivial

theorem hol_UstarOf_dir_two (a b z : PeriodicLatticeSite witL7) (hz : z 0 ≠ qStar 0) :
    periodicPathHolonomy (UstarOf M) z (straightSegment a b 2) = 1 :=
  hol_straight_one (UstarOf M) 2 (fun u => u 0 ≠ qStar 0)
    (fun u hu => by
      show (Function.update u 2 (if (2, true).2 then u 2 + 1 else u 2 - 1)) 0 ≠ qStar 0
      rwa [Function.update_of_ne (by decide)])
    (fun u hu => UstarOf_coord M u hu) a b z hz

/-- **THE PARITY.** `Γ_{y,x}` does its direction-`2` leg at coordinate `0` equal to `y 0`; the other
two legs are directions `1` and `0`, on which `U*(M)` is trivial outright. So the whole contour
carries trivial `U*(M)`-holonomy whenever `y 0 ≠ 1`. -/
theorem hol_UstarOf_gamma (y x : PeriodicLatticeSite witL7) (hy : y 0 ≠ qStar 0) :
    periodicPathHolonomy (UstarOf M) y (GammaPath y x) = 1 := by
  unfold GammaPath
  rw [periodicPathHolonomy_append, periodicPathHolonomy_append,
    hol_UstarOf_dir_two M y x y hy, hol_UstarOf_dir_ne_two M (by decide : (1 : Fin 3) ≠ 2),
    hol_UstarOf_dir_ne_two M (by decide : (0 : Fin 3) ≠ 2), one_mul, one_mul]

/-- The full `Q_ℓ` transport path for a direction-`0` coarse bond carries trivial holonomy. -/
theorem hol_UstarOf_transport0 (y x : PeriodicLatticeSite witL7) (hy : y 0 ≠ qStar 0) (i : ℕ) :
    periodicPathHolonomy (UstarOf M) y (transportPath y x 0 i) = 1 := by
  unfold transportPath
  rw [periodicPathHolonomy_append, hol_UstarOf_gamma M y x hy,
    hol_UstarOf_dir_ne_two M (by decide : (0 : Fin 3) ≠ 2), one_mul]

/-- A level-`2` coarse site has EVEN coordinate `0`, hence never `qStar 0 = 1`. -/
theorem coarse_coord0_ne (yc : {y : PeriodicLatticeSite witL7 // y ∈ CoarseLattice witL7 2}) :
    yc.1 0 ≠ qStar 0 := by
  intro h
  have hmod := mem_CoarseLattice.mp yc.2 0
  rw [h] at hmod
  exact absurd hmod (by decide)

/-- **THE DIPOLE IS IN `ker Q_2(U*(M))`.** Not just in the flat kernel: the covariant one, at the
non-flat background `U*(M)`, for EVERY `M`. -/
theorem vDip_kerQ_UstarOf : lineCoarseRestrictCovLM (UstarOf M) 2 vDip = 0 := by
  funext b
  obtain ⟨yc, d⟩ := b
  rw [Pi.zero_apply, lineCoarseRestrictCovLM_apply]
  rcases eq_or_ne d 0 with rfl | hd
  · have hflat : lineCoarseRestrictCov (trivialU witL7) 2 vDip (yc, 0) = 0 := by
      have h2 := congrFun vDip_kerQ_flat (yc, 0)
      rwa [lineCoarseRestrictCovLM_apply, Pi.zero_apply] at h2
    have hsum : ∀ x ∈ blockOf yc.1 2, rZeroA (UstarOf M) yc.1 x vDip 0 2
        = rZeroA (trivialU witL7) yc.1 x vDip 0 2 := by
      intro x _
      unfold rZeroA
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hol_UstarOf_transport0 M yc.1 x (coarse_coord0_ne yc) i,
        periodicPathHolonomy_trivialU_eq_one]
    rw [← hflat]
    unfold lineCoarseRestrictCov
    rw [Finset.sum_congr rfl hsum]
  · unfold lineCoarseRestrictCov
    have hz : ∀ x ∈ blockOf yc.1 2, rZeroA (UstarOf M) yc.1 x vDip d 2 = 0 := by
      intro x _
      unfold rZeroA
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [vDip_off_dir (pathSite x d i) hd, map_zero]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, smul_zero]

#print axioms hol_UstarOf_gamma
#print axioms hol_UstarOf_transport0
#print axioms coarse_coord0_ne
#print axioms vDip_kerQ_UstarOf

/-! ### §3d — the drift lives on ONE plaquette, computed exactly -/

theorem hlt02 : (0 : Fin 3) < 2 := by decide

/-- The one plaquette the drift is supported on: base `qStar`, directions `(0,2)`. -/
def qPlaq : PeriodicLatticePlaquette witL7 := (qStar, ⟨(0, 2), hlt02⟩)

/-- The three ordered direction pairs, enumerated from the DEFINING constraint `μ < ν` on
`PeriodicPlaquetteDirections` (S83: enumerate against the definition, not the construction). -/
theorem dir_cases : ∀ μ ν : Fin 3, μ < ν →
    (μ = 0 ∧ ν = 1) ∨ (μ = 0 ∧ ν = 2) ∨ (μ = 1 ∧ ν = 2) := by decide

/-- **THE DRIFT, EXACTLY.** `curlDrift (U*(M)) vDip` vanishes at every plaquette except `qPlaq`,
where it is `−(R(M)w − w)`. Every case is closed by an identity, none by an estimate:
* any pair with `ν ≠ 0` kills the first bracket (`vDip` is a direction-`0` field);
* the pairs `(0,1)` and `(1,2)` kill the second bracket, the first because `U*(M)` is trivial in
  direction `1`, the second because `vDip(·,1) = 0`;
* the pair `(0,2)` away from `qStar` kills it because `U*(M)` is trivial there;
* at `qStar` it is exactly `−(R(M)w − w)`, the local holonomy deviation applied to `w`. -/
theorem curlDrift_UstarOf_vDip (q : PeriodicLatticePlaquette witL7) :
    curlDrift (UstarOf M) vDip q
      = if q = qPlaq then -(RMap M suTwoWitness - suTwoWitness) else 0 := by
  obtain ⟨x, ⟨⟨μ, ν⟩, hlt⟩⟩ := q
  rw [curlDrift_apply]
  rcases dir_cases μ ν hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- (0,1): first bracket dies on `vDip(·,1) = 0`, second on `U*(M)(·,1) = 1`
    have hne : ((x, ⟨((0 : Fin 3), (1 : Fin 3)), hlt⟩) : PeriodicLatticePlaquette witL7) ≠ qPlaq := by
      intro hq
      have h2 : ((0 : Fin 3), (1 : Fin 3)) = ((0 : Fin 3), (2 : Fin 3)) :=
        congrArg (fun r : PeriodicLatticePlaquette witL7 => r.2.1) hq
      exact absurd h2 (by decide)
    rw [if_neg hne,
      show vDip (periodicLatticeShift x 0, (1 : Fin 3)) = 0 from
        vDip_off_dir _ (by decide),
      UstarOf_dir_ne_two M x (by decide : (1 : Fin 3) ≠ 2), map_zero, RMap_one]
    simp only [LinearMap.id_coe, id_eq]
    abel
  · -- (0,2): the only live pair
    rw [show vDip (periodicLatticeShift x 0, (2 : Fin 3)) = 0 from vDip_off_dir _ (by decide),
      map_zero, sub_zero, zero_sub]
    rcases eq_or_ne x qStar with rfl | hx
    · have hq : ((qStar, ⟨((0 : Fin 3), (2 : Fin 3)), hlt⟩) : PeriodicLatticePlaquette witL7)
          = qPlaq := rfl
      rw [if_pos hq, qStar_shift2, vDip_at_a7, UstarOf_at]
    · have hne : ((x, ⟨((0 : Fin 3), (2 : Fin 3)), hlt⟩) : PeriodicLatticePlaquette witL7)
          ≠ qPlaq := fun hq => hx (congrArg Prod.fst hq)
      rw [if_neg hne, UstarOf_of_ne M (by simp [Prod.mk.injEq, hx]), RMap_one]
      simp only [LinearMap.id_coe, id_eq]
      abel
  · -- (1,2): both brackets die on `vDip(·,ρ) = 0` for `ρ ≠ 0`
    have hne : ((x, ⟨((1 : Fin 3), (2 : Fin 3)), hlt⟩) : PeriodicLatticePlaquette witL7) ≠ qPlaq := by
      intro hq
      have h2 : ((1 : Fin 3), (2 : Fin 3)) = ((0 : Fin 3), (2 : Fin 3)) :=
        congrArg (fun r : PeriodicLatticePlaquette witL7 => r.2.1) hq
      exact absurd h2 (by decide)
    rw [if_neg hne,
      show vDip (periodicLatticeShift x 1, (2 : Fin 3)) = 0 from vDip_off_dir _ (by decide),
      show vDip (periodicLatticeShift x 2, (1 : Fin 3)) = 0 from vDip_off_dir _ (by decide),
      map_zero, map_zero]
    abel

#print axioms dir_cases
#print axioms curlDrift_UstarOf_vDip

/-! ### §3e — the window sees that plaquette, so the window sum is NONZERO -/

/-- `(0,0,6)` — the level-`2` block corner of `qStar = (1,0,7)`. -/
def yStar : PeriodicLatticeSite witL7 := fun ρ => if ρ = 2 then 6 else 0

theorem yStar_coarse : yStar ∈ CoarseLattice witL7 2 := mem_CoarseLattice.mpr (by decide)

/-- The coarse plaquette whose window contains `qPlaq`. -/
def pStar : CoarsePlaquette witL7 2 := (⟨yStar, yStar_coarse⟩, ⟨(0, 2), hlt02⟩)

theorem qStar_mem_blockOf_yStar : qStar ∈ blockOf yStar 2 := mem_blockOf.mpr (by decide)

/-- **THE WINDOW SUM OF THE DRIFT IS NONZERO** as soon as `R(M)` moves `w`. The window of `pStar`
contains `qPlaq` (witness: the window index `(qStar, 0, 0)`), the drift is `−(R(M)w − w)` there and
`0` everywhere else, so the sum is a positive integer multiple of a nonzero vector. -/
theorem windowSum_drift_pStar_ne_zero (hM : RMap M suTwoWitness ≠ suTwoWitness) :
    windowSum (ell := 2) (curlDrift (UstarOf M) vDip) pStar ≠ 0 := by
  classical
  have hmem : ((qStar, 0, 0) : PeriodicLatticeSite witL7 × ℕ × ℕ) ∈ windowSet 2 yStar := by
    unfold windowSet
    rw [Finset.mem_product]
    exact ⟨qStar_mem_blockOf_yStar, by decide⟩
  have hhit : windowPlaq hlt02 ((qStar, 0, 0) : PeriodicLatticeSite witL7 × ℕ × ℕ) = qPlaq := rfl
  have hcard : ((windowSet 2 yStar).filter
      (fun t => windowPlaq hlt02 t = qPlaq)).card ≠ 0 := by
    refine Finset.card_ne_zero_of_mem (a := ((qStar, 0, 0) : PeriodicLatticeSite witL7 × ℕ × ℕ)) ?_
    exact Finset.mem_filter.mpr ⟨hmem, hhit⟩
  have hD : -(RMap M suTwoWitness - suTwoWitness) ≠ 0 :=
    neg_ne_zero.mpr (sub_ne_zero.mpr hM)
  show (∑ t ∈ windowSet 2 yStar, curlDrift (UstarOf M) vDip (windowPlaq hlt02 t)) ≠ 0
  rw [Finset.sum_congr rfl (fun t _ => curlDrift_UstarOf_vDip M (windowPlaq hlt02 t)),
    ← Finset.sum_filter, Finset.sum_const]
  intro hz
  rw [← Nat.cast_smul_eq_nsmul ℝ] at hz
  rcases smul_eq_zero.mp hz with hc | hw
  · exact hcard (by exact_mod_cast hc)
  · exact hD hw

#print axioms yStar_coarse
#print axioms qStar_mem_blockOf_yStar
#print axioms windowSum_drift_pStar_ne_zero

/-! ### §3f — THE REFUTATION -/

theorem coarseCurlSuTwo_zero {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (p : CoarsePlaquette L ell) :
    coarseCurlSuTwo hdvd (0 : CoarseBond L ell → SuTwo) p = 0 := by
  unfold coarseCurlSuTwo
  show (0 : SuTwo) + 0 - 0 - 0 = 0
  abel

/-- **`WindowStokesAnnihilates` IS FALSE at EVERY background whose local holonomy moves `w`.**
The hypothesis `SplitBaseCase.base_case_general_U` is conditional on does NOT hold at general `U`:
`vDip` lies in `ker Q_2(U*(M))` and its window Stokes sum at `pStar` is nonzero.

This is a permanent kill, not a failure to prove: the route "assume the window sum annihilates
`ker Q_ℓ(U)`" is not available at general `U`. §4 gives the quantitative statement that replaces
it, and §5 shows no smallness threshold on `U − 1` rescues the exact form. -/
theorem windowStokesAnnihilates_UstarOf_false (hM : RMap M suTwoWitness ≠ suTwoWitness) :
    ¬ WindowStokesAnnihilates 2 (UstarOf M) := by
  intro h
  have hzero := h vDip (vDip_kerQ_UstarOf M) pStar
  have hid := windowSum_curl_general (L := witL7) (ell := 2) (by norm_num) witL7_two_dvd
    (UstarOf M) vDip pStar
  rw [vDip_kerQ_flat, coarseCurlSuTwo_zero, smul_zero, zero_add] at hid
  exact windowSum_drift_pStar_ne_zero M hM (hid ▸ hzero)

/-- The concrete instance: `M = witnessM = !![0,1;-1,0]`, for which `R(M) w = −w ≠ w`. -/
noncomputable def Ustar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL7 :=
  UstarOf witnessMElem

theorem windowStokesAnnihilates_Ustar_false : ¬ WindowStokesAnnihilates 2 Ustar :=
  windowStokesAnnihilates_UstarOf_false witnessMElem (by
    rw [RMap_witnessMElem]
    exact fun h => suTwoWitness_ne_neg_self h.symm)

#print axioms coarseCurlSuTwo_zero
#print axioms windowStokesAnnihilates_Ustar_false

/-! ## §4 — THE QUANTITATIVE GENERAL-`U` BASE CASE

§3 kills the EXACT annihilation. What survives is the quantitative statement, and it is
unconditional: no hypothesis on `U` at all beyond a uniform per-bond holonomy-deviation bound `α`,
and the defect it carries vanishes QUADRATICALLY as `α → 0`.

    ℓ · (flat coarse curl energy of Q_ℓ(1) A)  ≤  2·⟨B, Δ_k B⟩  +  64·α²·bondEnergy A ,
    A := hjExtension_{ℓ,levels,U}(B) .

Every constant is composed from counted factors: `ℓ⁸` (two copies of the window's `ℓ⁴`) against
`ℓ⁵·ℓ²` (window size × plaquette multiplicity) gives the `ℓ`; the `2`s are the triangle
inequality `‖a−b‖² ≤ 2‖a‖²+2‖b‖²`; the `32` inside `64 = 2·32` is
`RegularUPerturbation.plaqEnergy_curlDrift_le`'s `8·(2+2)`.

**The residual this leaves is NAMED and it is the `bondEnergy A` factor** — see §6. -/

/-- `‖a − b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem norm_sub_sq_le_two (a b : SuTwo) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]

/-- **THE QUANTITATIVE BASE CASE AT EVERY BACKGROUND.** Unconditional: no gauge condition, no
restriction on `B`, no hypothesis on `U` except the uniform deviation bound `α`. At `α = 0` the
defect term vanishes identically and the bound degrades to `2×` `SplitBaseCase`'s sharp `U = 1`
inequality (see `quantitative_base_case_trivialU_consistency`). -/
theorem quantitative_base_case {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (B : Bond L → SuTwo) :
    (ell : ℝ) * coarseCurlEnergy hdvd
        (lineCoarseRestrictCovLM (trivialU L) ell (hjExtensionCovFaithful ell levels U B))
      ≤ 2 * deltaJQuadFormCovFaithful ell levels U B
        + 64 * α ^ 2 * bondEnergy (hjExtensionCovFaithful ell levels U B) := by
  classical
  set A : Bond L → SuTwo := hjExtensionCovFaithful ell levels U B with hA
  set X : PeriodicLatticePlaquette L → SuTwo := curlCovariantLM U A with hX
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hdelta : deltaJQuadFormCovFaithful ell levels U B
      = ∑ q : PeriodicLatticePlaquette L, ‖X q‖ ^ 2 := by
    show covPlaqInner X X = _
    unfold covPlaqInner
    exact Finset.sum_congr rfl fun q _ => hsInner_self_eq_norm_sq (X q)
  have hsplit : ∀ p : CoarsePlaquette L ell,
      ((ell : ℝ) ^ 4) •
          coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A) p
        = windowSum X p - windowSum (curlDrift U A) p := by
    intro p
    rw [hX, windowSum_curl_general hell hdvd U A p]
    abel
  have hpt : ∀ p : CoarsePlaquette L ell,
      ((ell : ℝ) ^ 8) *
          hsInner (coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A) p)
            (coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A) p)
        ≤ 2 * ‖windowSum X p‖ ^ 2 + 2 * ‖windowSum (curlDrift U A) p‖ ^ 2 := by
    intro p
    have h1 : ((ell : ℝ) ^ 8) *
          hsInner (coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A) p)
            (coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A) p)
        = ‖((ell : ℝ) ^ 4) •
            coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A) p‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((ell : ℝ) ^ 4)), hsInner_self_eq_norm_sq]
      ring
    rw [h1, hsplit p]
    exact norm_sub_sq_le_two _ _
  have hsum : ((ell : ℝ) ^ 8) *
      coarseCurlEnergy hdvd (lineCoarseRestrictCovLM (trivialU L) ell A)
      ≤ 2 * (∑ p : CoarsePlaquette L ell, ‖windowSum X p‖ ^ 2)
        + 2 * ∑ p : CoarsePlaquette L ell, ‖windowSum (curlDrift U A) p‖ ^ 2 := by
    have hrhs : 2 * (∑ p : CoarsePlaquette L ell, ‖windowSum X p‖ ^ 2)
        + 2 * ∑ p : CoarsePlaquette L ell, ‖windowSum (curlDrift U A) p‖ ^ 2
        = ∑ p : CoarsePlaquette L ell,
            (2 * ‖windowSum X p‖ ^ 2 + 2 * ‖windowSum (curlDrift U A) p‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    unfold coarseCurlEnergy
    rw [hrhs, Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => hpt p
  have hX2 : ∑ p : CoarsePlaquette L ell, ‖windowSum X p‖ ^ 2
      ≤ ((ell : ℝ) ^ 7) * deltaJQuadFormCovFaithful ell levels U B := by
    rw [hdelta]
    exact windowSum_energy_le hdvd X
  have hD2 : ∑ p : CoarsePlaquette L ell, ‖windowSum (curlDrift U A) p‖ ^ 2
      ≤ 32 * α ^ 2 * ((ell : ℝ) ^ 7) * bondEnergy A :=
    windowSum_drift_energy_le hdvd U A α hα0 hα
  have h7 : (0 : ℝ) < ((ell : ℝ) ^ 7) := by positivity
  have hfinal : ((ell : ℝ) ^ 7) *
        ((ell : ℝ) * coarseCurlEnergy hdvd (lineCoarseRestrictCovLM (trivialU L) ell A))
      ≤ ((ell : ℝ) ^ 7) *
        (2 * deltaJQuadFormCovFaithful ell levels U B + 64 * α ^ 2 * bondEnergy A) := by
    have hrw : ((ell : ℝ) ^ 7) *
        ((ell : ℝ) * coarseCurlEnergy hdvd (lineCoarseRestrictCovLM (trivialU L) ell A))
        = ((ell : ℝ) ^ 8) *
          coarseCurlEnergy hdvd (lineCoarseRestrictCovLM (trivialU L) ell A) := by ring
    rw [hrw]
    nlinarith [hsum, hX2, hD2, h7]
  exact le_of_mul_le_mul_left hfinal h7

/-- **CONSISTENCY CONTROL at `U = 1`.** At the trivial background `α = 0` is admissible
(`frobNorm 0 = 0`), the defect term vanishes, `Q_ℓ(1)` does not see the fibre correction
(`SplitBaseCase.lineCoarse_hjExtension`), and §4 reduces to `SplitBaseCase`'s sharp inequality with
the constant doubled — i.e. §4 is WEAKER at `U = 1`, never stronger. That is the correct direction:
a bound derived through a triangle inequality must not beat the exact one. -/
theorem quantitative_base_case_trivialU_consistency {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels (trivialU L)).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    (ell : ℝ) * coarseCurlEnergy hdvd (lineCoarseRestrictCovLM (trivialU L) ell B)
      ≤ 2 * deltaJQuadFormCovFaithful ell levels (trivialU L) B := by
  have h := quantitative_base_case (L := L) hell hdvd levels (trivialU L) 0 le_rfl
    (fun b => by
      rw [show ((trivialU L) b : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl, sub_self,
        AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]) B
  rw [lineCoarse_hjExtension levels (trivialU L) B] at h
  simpa using h

#print axioms norm_sub_sq_le_two
#print axioms quantitative_base_case
#print axioms quantitative_base_case_trivialU_consistency

/-! ## §5 — NO SMALLNESS THRESHOLD ON `U − 1` RESCUES THE EXACT ANNIHILATION

§3 refutes `WindowStokesAnnihilates` at `M = witnessM`, whose deviation `frobNorm(M − 1)` is
`2` — ~~`2√2`~~ STRUCK: `2√2` is this tree's constant for the CENTRAL element `−1`, not for
`witnessM`; the correct value is `2` and it is proved below (`frobNorm_witnessM_sub_one`).
~~agreeing with the tree's pre-existing kernel-checked `LemmaAssembly.frobNorm_witnessMElem_sub_one`~~
S75 STRUCK (2026-08-01, Kimi gate): NO such declaration exists anywhere in the tree — the citation
was dangling. The value `2` rests on the in-file theorem alone (and was independently recomputed
from raw matrix entries by the second-family gate).
Either way it is `O(1)`. A reader could hope that the campaign's own regularity class — `frobSupBond U ≤ α₀` with
`α₀` tiny — restores the hypothesis. It does not, and this section proves it: for EVERY `α₀ > 0`
there is a background inside that class at which the hypothesis fails.

The family is the real rotation `M(c,s) = !![c, s; −s, c]` with `c² + s² = 1`. It is in `SU(2)`
(real orthogonal, determinant `c²+s²`), it fails to commute with `w = diag(i,−i)` exactly when
`s ≠ 0`, and `frobSq(M − 1) = 2(c−1)² + 2s² → 0` as `(c,s) → (1,0)`. The Pythagorean
parametrisation `c = (1−t²)/(1+t²)`, `s = 2t/(1+t²)` keeps `c² + s² = 1` an ALGEBRAIC identity —
no square roots enter, so nothing here rests on a transcendental estimate. -/

open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobNorm_nonneg frobNorm_zero)

/-- The real rotation `!![c, s; −s, c]` inside the `2×2` complex matrices. -/
noncomputable def rotM (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c : ℂ), (s : ℂ); -(s : ℂ), (c : ℂ)]

theorem rotM_mem (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    rotM c s ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hc : ((c : ℂ)) ^ 2 + ((s : ℂ)) ^ 2 = 1 := by exact_mod_cast congrArg Complex.ofReal h
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotM, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hc
    · ring
    · ring
    · linear_combination hc
  · simp only [rotM, Matrix.det_fin_two_of]
    linear_combination hc

/-- The rotation, packaged as a group element. -/
noncomputable def rotElem (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨rotM c s, rotM_mem c s h⟩

/-- The `(0,0)` entry of the adjoint action of the rotation on `w = diag(i,−i)`. -/
theorem rot_conj_entry (c s : ℝ) :
    (rotM c s * suTwoWitnessVal * (rotM c s).conjTranspose) 0 0
      = Complex.I * (((c : ℂ)) ^ 2 - ((s : ℂ)) ^ 2) := by
  simp [rotM, suTwoWitnessVal, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring

/-- **THE ROTATION MOVES `w` EXACTLY WHEN `s ≠ 0`** — no smallness needed, and the failure is
first order in `s`. -/
theorem RMap_rotElem_ne (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    RMap (rotElem c s h) suTwoWitness ≠ suTwoWitness := by
  intro heq
  have hmat : rotM c s * suTwoWitnessVal * (rotM c s).conjTranspose = suTwoWitnessVal := by
    have hco := congrArg (fun X : SuTwo => (X : Matrix (Fin 2) (Fin 2) ℂ)) heq
    rw [RMap_coe_apply] at hco
    exact hco
  have h00 : Complex.I * (((c : ℂ)) ^ 2 - ((s : ℂ)) ^ 2) = Complex.I * 1 := by
    rw [← rot_conj_entry c s, hmat]
    show suTwoWitnessVal 0 0 = Complex.I * 1
    simp [suTwoWitnessVal]
  have hC : ((c : ℂ)) ^ 2 - ((s : ℂ)) ^ 2 = 1 := mul_left_cancel₀ Complex.I_ne_zero h00
  have hR : c ^ 2 - s ^ 2 = 1 := by exact_mod_cast hC
  exact hs (by nlinarith [h, hR, sq_nonneg s])

theorem frobSq_rotM_sub_one (c s : ℝ) :
    frobSq (rotM c s - 1) = 2 * (c - 1) ^ 2 + 2 * s ^ 2 := by
  unfold frobSq
  simp [rotM, Matrix.sub_apply, Complex.normSq_apply]
  ring

/-- `witnessM = !![0,1;-1,0]` IS the rotation at `(c,s) = (0,1)`. -/
theorem witnessM_eq_rotM : witnessM = rotM 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witnessM, rotM]

/-- **THE CORRECTED CONSTANT, AS A THEOREM.** `frobNorm(witnessM − 1) = 2`. The `2√2` this module's
§5 prose originally carried is the tree's constant for the CENTRAL element `−1`; `witnessM` is not
central. ~~Agrees with the tree's independent `LemmaAssembly.frobNorm_witnessMElem_sub_one`~~
S75 STRUCK (2026-08-01, Kimi gate): that declaration does not exist — dangling citation. This
in-file theorem is the sole and sufficient authority for the value. -/
theorem frobNorm_witnessM_sub_one :
    frobNorm ((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 2 := by
  have hco : ((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ)) = rotM 0 1 := witnessM_eq_rotM
  unfold frobNorm
  rw [hco, frobSq_rotM_sub_one]
  rw [show (2 : ℝ) * (0 - 1) ^ 2 + 2 * (1 : ℝ) ^ 2 = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem frobNorm_rotM_le (c s α : ℝ) (hα : 0 ≤ α)
    (hbd : 2 * (c - 1) ^ 2 + 2 * s ^ 2 ≤ α ^ 2) : frobNorm (rotM c s - 1) ≤ α := by
  unfold frobNorm
  rw [frobSq_rotM_sub_one]
  calc Real.sqrt (2 * (c - 1) ^ 2 + 2 * s ^ 2) ≤ Real.sqrt (α ^ 2) := Real.sqrt_le_sqrt hbd
    _ = α := Real.sqrt_sq hα

/-- `U*(M)` differs from `1` on ONE link, so its `sup` deviation is `M`'s own deviation. -/
theorem frobSupBond_UstarOf_le (α : ℝ) (hα : 0 ≤ α)
    (hM : frobNorm ((M : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    frobSupBond (UstarOf M) ≤ α := by
  refine Finset.sup'_le _ _ (fun b _ => ?_)
  by_cases hb : b = (qStar, 2)
  · rw [hb, UstarOf_at]
    exact hM
  · rw [UstarOf_of_ne M hb]
    have hone : (((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        = 0 := by
      rw [show ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl,
        sub_self]
    rw [hone, frobNorm_zero]
    exact hα

/-- A rotation of prescribed smallness that still moves `w`. Pure algebra: `c² + s² = 1` is an
identity in `t`, and `2(c−1)² + 2s² = 8t²/(1+t²) ≤ 8t² = α²/2`. -/
theorem exists_small_rot (α : ℝ) (hα : 0 < α) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ s ≠ 0 ∧ 2 * (c - 1) ^ 2 + 2 * s ^ 2 ≤ α ^ 2 := by
  set t : ℝ := α / 4 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hd0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  refine ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2), ?_, ?_, ?_⟩
  · field_simp
    ring
  · positivity
  · have hval : 2 * ((1 - t ^ 2) / (1 + t ^ 2) - 1) ^ 2 + 2 * (2 * t / (1 + t ^ 2)) ^ 2
        = 8 * t ^ 2 / (1 + t ^ 2) := by
      field_simp
      ring
    rw [hval]
    have h1 : 8 * t ^ 2 / (1 + t ^ 2) ≤ 8 * t ^ 2 :=
      div_le_self (by positivity) (by nlinarith [sq_nonneg t])
    have h2 : 8 * t ^ 2 = α ^ 2 / 2 := by rw [ht]; ring
    nlinarith [h1, h2, sq_nonneg α]

/-- **NO SMALLNESS THRESHOLD SAVES THE HYPOTHESIS.** For EVERY `α > 0` there is a background `U`
with `sup_b frobNorm(U b − 1) ≤ α` at which `WindowStokesAnnihilates 2 U` is FALSE.

So `SplitBaseCase.base_case_general_U` cannot be discharged by restricting to the campaign's
regular-`U` class, however small `α₀` is taken. What replaces it is §4, whose defect is `O(α²)` and
therefore genuinely small on that class — which is the correct shape, and the one this refutation
shows is FORCED. -/
theorem no_smallness_threshold (α : ℝ) (hα : 0 < α) :
    ∃ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL7,
      frobSupBond U ≤ α ∧ ¬ WindowStokesAnnihilates 2 U := by
  obtain ⟨c, s, hcs, hs0, hbd⟩ := exists_small_rot α hα
  refine ⟨UstarOf (rotElem c s hcs), ?_,
    windowStokesAnnihilates_UstarOf_false (rotElem c s hcs) (RMap_rotElem_ne c s hcs hs0)⟩
  refine frobSupBond_UstarOf_le (rotElem c s hcs) α (le_of_lt hα) ?_
  exact frobNorm_rotM_le c s α (le_of_lt hα) hbd

/-! ## §6 — NON-VACUITY CONTROLS

Two things could make everything above content-free: the refuted hypothesis could be about an empty
class, and §4's inequality could be `0 ≤ (nonneg)` at every point. Both are excluded, in the
kernel. -/

/-- **The refuted hypothesis is not about an empty class.** `WindowStokesAnnihilates 2` HOLDS at
`U = 1` (`SplitBaseCase.windowStokesAnnihilates_trivialU`) and FAILS at `U*`. So §3 refutes a
`Prop` that is genuinely satisfiable, and the refutation is a statement about `U ≠ 1`, not about a
malformed definition. -/
theorem windowStokesAnnihilates_holds_and_fails :
    WindowStokesAnnihilates 2 (trivialU witL7) ∧ ¬ WindowStokesAnnihilates 2 Ustar :=
  ⟨AdalyFormal.Balaban.SplitBaseCase.windowStokesAnnihilates_trivialU (by norm_num) witL7_two_dvd,
    windowStokesAnnihilates_Ustar_false⟩

/-- **The defect energy of §2 is strictly positive at `U*`** — so §2's bound is not `0 ≤ 0`, and at
`U*` it genuinely FORCES `α > 0` (a `0` deviation bound would give `Σ ≤ 0`, contradicting this).
That is the must-fire control on §2. -/
theorem windowSum_drift_energy_pos_Ustar :
    0 < ∑ p : CoarsePlaquette witL7 2, ‖windowSum (curlDrift Ustar vDip) p‖ ^ 2 := by
  refine Finset.sum_pos' (fun p _ => by positivity) ⟨pStar, Finset.mem_univ _, ?_⟩
  have hne : windowSum (ell := 2) (curlDrift Ustar vDip) pStar ≠ 0 :=
    windowSum_drift_pStar_ne_zero witnessMElem (by
      rw [RMap_witnessMElem]
      exact fun h => suTwoWitness_ne_neg_self h.symm)
  have : 0 < ‖windowSum (ell := 2) (curlDrift Ustar vDip) pStar‖ := norm_pos_iff.mpr hne
  positivity

/-- **§4's left-hand side is strictly positive at an explicit point** — `B7` on `witL7` at `ℓ = 2`
(`SplitBaseCase.coarseCurlEnergy_Q2_B7_pos`, an independent lane's witness). So the inequality of
§4/§4-consistency is not the content-free `0 ≤ (nonnegative)`. -/
theorem quantitative_base_case_lhs_pos :
    0 < ((2 : ℕ) : ℝ) * coarseCurlEnergy witL7_two_dvd
      (lineCoarseRestrictCovLM (trivialU witL7) 2
        AdalyFormal.Balaban.ThirdLevelWitness.B7) := by
  have h := AdalyFormal.Balaban.SplitBaseCase.coarseCurlEnergy_Q2_B7_pos
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2]
  linarith

#print axioms windowStokesAnnihilates_holds_and_fails
#print axioms windowSum_drift_energy_pos_Ustar
#print axioms quantitative_base_case_lhs_pos

#print axioms rotM_mem
#print axioms rot_conj_entry
#print axioms RMap_rotElem_ne
#print axioms frobSq_rotM_sub_one
#print axioms frobNorm_rotM_le
#print axioms frobSupBond_UstarOf_le
#print axioms exists_small_rot
#print axioms no_smallness_threshold


/-! ## §7 — THE COST OF MOVING FROM `Q_ℓ(1)` TO `Q_ℓ(U)`

§4's left-hand side carries the FLAT `Q_ℓ(1)`. `SplitBaseCase.lineCoarse_hjExtension` already gives
`Q_ℓ(U) A = Q_ℓ(U) B` at every background, so the whole distance between §4 and a statement about
`Q_ℓ(U) B` is a bound on `Q_ℓ(U) − Q_ℓ(1)`. This section builds it, with NO free parameter left
but `α`.

**LAW-19 — the analytic primitive was NOT rebuilt.** `TowerLawCov.norm_RMap_hol_sub_self_le` already
proves `‖R(hol_U(y,s))X − X‖ ≤ (length s)·α` from `∀ b, ‖R(U b)X − X‖ ≤ α`, by splitting the product
inside `R` and using `R`'s isometry — no matrix-norm triangle inequality, which that module's own
header records as blocked in this import closure. A rebuild of it was begun in this lane and
ABANDONED on finding it; only the `frobNorm`-relative restatement below is new. -/

open AdalyFormal.Balaban.Q1Real (rZeroA_trivialU coordSteps)


/-- Per-link deviation, in the `X`-relative form `TowerLawCovariant` consumes. -/
theorem norm_RMap_hol_sub_self_le_alpha
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α : ℝ)
    (hα : ∀ b : Bond L,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (X : SuTwo) (y : PeriodicLatticeSite L) (s : List (Fin 3 × Bool)) :
    ‖RMap (periodicPathHolonomy U y s) X - X‖ ≤ (s.length : ℝ) * (2 * α * ‖X‖) := by
  refine AdalyFormal.Balaban.TowerLawCov.norm_RMap_hol_sub_self_le U X (fun b => ?_) y s
  refine le_trans (AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (U b) X) ?_
  have h := hα b
  nlinarith [norm_nonneg X]

#print axioms norm_RMap_hol_sub_self_le_alpha

/-- The exact difference of the two line averages, before any estimate. -/
theorem lineCoarse_cov_sub_flat {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : Bond L → SuTwo) (b : CoarseBond L ell) :
    lineCoarseRestrictCov U ell v b - lineCoarseRestrictCov (trivialU L) ell v b
      = (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
          (RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 i))
              (v (pathSite x b.2 i, b.2)) - v (pathSite x b.2 i, b.2)) := by
  unfold lineCoarseRestrictCov
  rw [← smul_sub]
  have hstep : (∑ x ∈ blockOf b.1.1 ell, rZeroA U b.1.1 x v b.2 ell)
      - ∑ x ∈ blockOf b.1.1 ell, rZeroA (trivialU L) b.1.1 x v b.2 ell
      = ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
          (RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 i))
              (v (pathSite x b.2 i, b.2)) - v (pathSite x b.2 i, b.2)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [rZeroA_trivialU]
    unfold rZeroA
    rw [← Finset.sum_sub_distrib]
  rw [hstep]

#print axioms lineCoarse_cov_sub_flat

/-- **THE `Q_ℓ(U)` vs `Q_ℓ(1)` BOUND.** With `α` a uniform per-bond deviation bound and `Λ` a bound
on the transport-path lengths that the coarse bond `b` reads, the two line averages differ by at
most `(2 Λ α / ℓ⁴) · Σ_{x,i} ‖v(x + i e_μ, μ)‖`. -/
theorem norm_lineCoarse_cov_sub_flat_le {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α Λ : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (v : Bond L → SuTwo) (b : CoarseBond L ell)
    (hlen : ∀ x ∈ blockOf b.1.1 ell, ∀ i ∈ Finset.range ell,
      (((transportPath b.1.1 x b.2 i).length : ℕ) : ℝ) ≤ Λ) :
    ‖lineCoarseRestrictCov U ell v b - lineCoarseRestrictCov (trivialU L) ell v b‖
      ≤ (1 / (ell : ℝ) ^ 4) * (2 * Λ * α) *
          ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
            ‖v (pathSite x b.2 i, b.2)‖ := by
  classical
  rw [lineCoarse_cov_sub_flat U v b, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 4)]
  have hinner : ‖∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
        (RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 i))
            (v (pathSite x b.2 i, b.2)) - v (pathSite x b.2 i, b.2))‖
      ≤ (2 * Λ * α) * ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
          ‖v (pathSite x b.2 i, b.2)‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 := norm_RMap_hol_sub_self_le_alpha U α hα (v (pathSite x b.2 i, b.2)) b.1.1
      (transportPath b.1.1 x b.2 i)
    have h2 := hlen x hx i hi
    have h3 : (0 : ℝ) ≤ 2 * α * ‖v (pathSite x b.2 i, b.2)‖ := by positivity
    nlinarith [h1, h2, h3, norm_nonneg (v (pathSite x b.2 i, b.2))]
  have h4 : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 4 := by positivity
  calc (1 / (ell : ℝ) ^ 4) * ‖∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
        (RMap (periodicPathHolonomy U b.1.1 (transportPath b.1.1 x b.2 i))
            (v (pathSite x b.2 i, b.2)) - v (pathSite x b.2 i, b.2))‖
      ≤ (1 / (ell : ℝ) ^ 4) * ((2 * Λ * α) *
          ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
            ‖v (pathSite x b.2 i, b.2)‖) := mul_le_mul_of_nonneg_left hinner h4
    _ = (1 / (ell : ℝ) ^ 4) * (2 * Λ * α) *
          ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
            ‖v (pathSite x b.2 i, b.2)‖ := by ring

#print axioms norm_lineCoarse_cov_sub_flat_le

/-! ### The path-length discharge: `Λ = 4·ℓ` on the block -/

theorem length_straightSegment (a c : PeriodicLatticeSite L) (μ : Fin 3) :
    (straightSegment a c μ).length = coordSteps a c μ := by
  unfold straightSegment
  exact List.length_replicate

/-- `coordSteps` is exactly the coordinate gap when there is no wraparound. -/
theorem coordSteps_of_le (a c : PeriodicLatticeSite L) (μ : Fin 3)
    (h : (a μ).val ≤ (c μ).val) : coordSteps a c μ = (c μ).val - (a μ).val := by
  unfold coordSteps
  exact Fin.coe_sub_iff_le.mpr h

/-- On a block, every coordinate gap is `< ℓ`. -/
theorem coordSteps_lt_of_mem_blockOf {ell : ℕ} {y x : PeriodicLatticeSite L}
    (hx : x ∈ blockOf y ell) (μ : Fin 3) : coordSteps y x μ < ell := by
  have h := mem_blockOf.mp hx μ
  rw [coordSteps_of_le y x μ h.1]
  omega

/-- Adding `1` in `Fin (n+1)` raises the value by at most `1` (wraparound only lowers it). -/
theorem fin_val_add_one_le {μ : Fin 3} (a : Fin (L μ + 1)) : (a + 1).val ≤ a.val + 1 := by
  have h := Fin.val_add a (1 : Fin (L μ + 1))
  have h1 : (1 : Fin (L μ + 1)).val ≤ 1 := by
    exact Nat.mod_le 1 _
  have h2 := Nat.mod_le (a.val + (1 : Fin (L μ + 1)).val) (L μ + 1)
  omega

/-- **The last leg of the transport path is at most `i` links long.** Direct induction on `i`; no
`Fin`-cast bookkeeping, so nothing here depends on a `NatCast (Fin _)` instance resolving. -/
theorem coordSteps_pathSite_le (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    coordSteps x (pathSite x μ i) μ ≤ i := by
  unfold coordSteps
  induction i with
  | zero =>
    rw [AdalyFormal.Balaban.QOne.pathSite_zero, sub_self]
    exact Nat.zero_le _
  | succ n ih =>
    have hstep : (pathSite x μ (n + 1)) μ = (pathSite x μ n) μ + 1 := by
      rw [AdalyFormal.Balaban.QOne.pathSite_succ]
      show (Function.update (pathSite x μ n) μ ((pathSite x μ n) μ + 1)) μ = _
      exact Function.update_self _ _ _
    have hd : (pathSite x μ (n + 1)) μ - x μ = ((pathSite x μ n) μ - x μ) + 1 := by
      rw [hstep]; abel
    rw [hd]
    have := fin_val_add_one_le (μ := μ) ((pathSite x μ n) μ - x μ)
    omega

/-- **THE PATH-LENGTH BOUND.** Every transport path `Q_ℓ` uses at a coarse bond, read from a site of
its own block with offset `i < ℓ`, is shorter than `4ℓ`: three legs of `Γ_{y,x}`, each a coordinate
gap inside the block (`< ℓ`), plus the straight leg of length `≤ i < ℓ`. -/
theorem transportPath_length_lt {ell : ℕ} {y x : PeriodicLatticeSite L}
    (hx : x ∈ blockOf y ell) (μ : Fin 3) {i : ℕ} (hi : i < ell) :
    (transportPath y x μ i).length < 4 * ell := by
  have hlen : (transportPath y x μ i).length
      = coordSteps y x 2
        + (coordSteps (Function.update y 2 (x 2)) x 1
          + coordSteps (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0)
        + coordSteps x (pathSite x μ i) μ := by
    unfold transportPath GammaPath
    rw [List.length_append, List.length_append, List.length_append,
      length_straightSegment, length_straightSegment, length_straightSegment,
      length_straightSegment]
    omega
  have h1 : coordSteps (Function.update y 2 (x 2)) x 1 = coordSteps y x 1 := by
    unfold coordSteps
    rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  have h0 : coordSteps (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0
      = coordSteps y x 0 := by
    unfold coordSteps
    rw [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),
      Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2)]
  rw [hlen, h1, h0]
  have c2 := coordSteps_lt_of_mem_blockOf hx 2
  have c1 := coordSteps_lt_of_mem_blockOf hx 1
  have c0 := coordSteps_lt_of_mem_blockOf hx 0
  have ci := coordSteps_pathSite_le x μ i
  omega

/-- **THE `Q_ℓ(U)` vs `Q_ℓ(1)` BOUND, PATH-LENGTH DISCHARGED.** No free parameter left but `α`:

    ‖(Q_ℓ(U) − Q_ℓ(1)) v (b)‖ ≤ (8 α / ℓ³) · Σ_{x∈B(b₋)} Σ_{i<ℓ} ‖v(x + i e_μ, μ)‖ ,

(S75 correction, 2026-08-01, Kimi gate: an earlier rendering of this display carried a spurious
extra `(1/ℓ)` factor, claiming a bound `ℓ` times stronger than proved; the statement below and the
constant line following are and were the proved form)

i.e. the constant is `2 · (4ℓ) · α / ℓ⁴ = 8α/ℓ³`, composed from counted factors: the `2` of
`RMapLipschitz.norm_RMap_sub_self_le`, the `4ℓ` of `transportPath_length_lt` (three block legs plus
the straight leg), against the `ℓ⁴` of the `(1.18)` normalisation. It VANISHES linearly as
`α → 0`. -/
theorem norm_lineCoarse_cov_sub_flat_le_block {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (v : Bond L → SuTwo) (b : CoarseBond L ell) :
    ‖lineCoarseRestrictCov U ell v b - lineCoarseRestrictCov (trivialU L) ell v b‖
      ≤ (1 / (ell : ℝ) ^ 4) * (2 * (4 * (ell : ℝ)) * α) *
          ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
            ‖v (pathSite x b.2 i, b.2)‖ := by
  refine norm_lineCoarse_cov_sub_flat_le U α (4 * (ell : ℝ)) hα0 hα v b (fun x hx i hi => ?_)
  have h := transportPath_length_lt hx b.2 (Finset.mem_range.mp hi)
  have h' : ((transportPath b.1.1 x b.2 i).length : ℝ) < ((4 * ell : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

#print axioms length_straightSegment
#print axioms coordSteps_of_le
#print axioms coordSteps_lt_of_mem_blockOf
#print axioms fin_val_add_one_le
#print axioms coordSteps_pathSite_le
#print axioms transportPath_length_lt
#print axioms norm_lineCoarse_cov_sub_flat_le_block


/-! ## §8 — THE REMAINING `#print axioms`, so the sweep covers EVERY declaration in this file

A nested validator measured 37 of the then-52 declarations carrying an axiom check, and named the
6 THEOREMS that lacked one -- including `windowStokesAnnihilates_UstarOf_false`, the general
parametric refutation that §5 actually consumes. All are swept below, definitions included: the file
now carries 64 declarations and 64 anchored `#print axioms` lines, one each, 0 missing, 0 orphaned.
None is exempt because it is "only a definition". -/

#print axioms hlt02
#print axioms hol_UstarOf_dir_ne_two
#print axioms hol_UstarOf_dir_two
#print axioms UstarOf_at
#print axioms UstarOf_of_ne
#print axioms windowStokesAnnihilates_UstarOf_false
#print axioms qStar
#print axioms UstarOf
#print axioms vDip
#print axioms qPlaq
#print axioms yStar
#print axioms pStar
#print axioms Ustar
#print axioms rotM
#print axioms rotElem
#print axioms witnessM_eq_rotM
#print axioms frobNorm_witnessM_sub_one

end AdalyFormal.Balaban.WindowStokesGeneralU
