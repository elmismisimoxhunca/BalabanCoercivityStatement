/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RegularUDomainWitnessGeneralU
import AdalyFormal.Balaban.RegularUDomainWitness
import AdalyFormal.Balaban.NonFlatBackground

set_option autoImplicit false

/-!
# `RegularUCurvedWitness.lean` — GOAL_LEMMA §4 (b2): the regular-`U` coercivity, EXHIBITED AT A
BACKGROUND WITH PROVABLY NONZERO CURVATURE

## What was missing

`RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` quantifies over ALL backgrounds `U`.
Its two published instances were both degenerate as *curvature* tests:

* `RegularUDomainWitness.deltaJ_coercive_at_witA` — at `U = trivialU`, the FLAT background.
* `RegularUDomainWitnessGeneralU.deltaJ_coercive_at_genWitness_tinyU` — at `tinyU b₀`, which is
  proved only `≠ trivialU` (`tinyU_ne_trivialU`), a **gauge-VARIANT** bare-link fact. That module's
  own docstring says so: *"§4 also records what is NOT proved about it: no statement is made here
  about its curvature."*

The distinction is not pedantic: `NonFlatBackground` proves (`pureGaugeU_holonomy_eq_one`,
`flat_but_link_ne_one`) that a configuration can differ from `trivialU` at a link and still have
**identically trivial field strength**. A `≠ trivialU` witness therefore certifies nothing about
the curved part of the theorem's domain.

## What this module adds

The curvature — lattice-generically, then instantiated.

* **§1–§3, generic and hypothesis-driven (no new `def`, LAW-19).** For ANY link configuration `U`
  that is `X` on one bond `b₀` and `1` elsewhere, on any extent with `0 < L μ`:
  `holonomy_singleBond_trichotomy` (every plaquette holonomy is `X`, `X⁻¹` or `1`) and
  `holonomy_singleBond_base_plaquette` (the holonomy at the plaquette based at `b₀`'s site, in
  `b₀`'s direction first, is exactly `X`). These generalise
  `NormalizedCounterexampleSearch.holonomy_singleBondU_*` and
  `NonFlatBackground.holonomy_singleBondU_trichotomy` off the hard-wired lattice
  `AdmissibleSubspace.witnessL` — see **F1** below for why that generalisation was forced.
* **§4.** `tinyU b₀` is CURVED (`tinyU_curvature_ne_one`), is **not the gauge transform of ANY
  configuration flat at the exhibited plaquette** (`tinyU_not_gaugeTransform_of_flat`, the
  gauge-INVARIANT separation), and is `IsRegularHolonomy` at the sharp small threshold
  `8/16000001 ≈ 5·10⁻⁷` (`tinyU_isRegularHolonomy`, `tinyU_not_isRegularHolonomy_of_lt`).
* **§5–§6.** The assembly on `witL5` (`L μ = 5`: `4 ≤ 5` ✓, `2 ∣ 6` ✓) —
  `curved_regularU_coercivity` (named form) and `exists_curved_regularU_coercivity`
  (`∃`-form, S91-registered).
* **§9 (OPS-10, one point → a FAMILY).** `curved_family_regularU_coercivity`: the same coercivity
  at EVERY `t` with `0 < |t| ≤ 1/2000`, on the rational-rotation family
  `curvedFamilyU t = rotElem t` on `curvedBond`, with a `t`-INDEPENDENT constant `≥ 1/6000` and
  curvature `8t²/(1+t²)` sweeping `(0, 8/4000001]`. §9 introduces ONE new `def`, `bondU b₀ X`
  (the single-active-bond family, generic in BOTH the extent and the group element), and this is
  a CONSOLIDATION rather than a fourth copy: both pre-existing copies are proved to be its
  instances by `rfl` (`tinyU_eq_bondU`, `singleBondU_eq_bondU`).

The curvature is deliberately placed **on the bond `freeBond 2 (siteZero witL5)` where the
admissible field `genWitness` is nonzero** (`genWitness_at_freeBond`), not somewhere the field
cannot see: `curvedU` is non-flat exactly where `curvedA` lives.

## HONEST SCOPE — what this does NOT do

* It does not strengthen `deltaJ_regularU_coercive_on_kerQU` itself, and inherits its scope
  verbatim: the LEADING covariant term `dstarDQuadForm U A = ‖∂^U A‖²` (the module-local nickname
  "`deltaJ(U)`"), SINGLE SCALE, on `ker Q₁(U) ∩ axial-gauge`, modulo `[UNIF-ALPHA]`. It is **not**
  `C*Δ_kC ≥ γ₀`, and it is not the Schur complement `deltaJQuadFormCovFaithful` — see that
  module's F6 banner.
* It is a NON-DEGENERACY result about the theorem's DOMAIN, not new coercivity. It says the
  quantifier `∀ U` ranges over genuinely curved backgrounds at which the conclusion is a
  non-trivial positive bound; it does not enlarge the set of `U` for which the conclusion holds.
* `curvedU` is supported on ONE bond. It is curved, small, and not gauge-equivalent to anything
  flat, but it is not a generic background; no claim is made that it is typical.
* ISLAND: nothing here is imported by `Spine.lean` or reaches `FULL3D.main`.

## ⚠ F1 — `NonFlatBackground.nonflatU` CANNOT SERVE THIS ROLE (finding, reported not fixed)

`nonflatU t : PeriodicLinkConfiguration _ AdmissibleSubspace.witnessL` and
`witnessL = fun _ => 3` (`Balaban/AdmissibleSubspace.lean:626`), whereas
`deltaJ_regularU_coercive_on_kerQU` needs `hL : ∀ μ, 4 ≤ L μ`. **`4 ≤ 3` is false**, so
`exists_curved_regular_below` and the entire `singleBondU`/`witnessPlaquette`/`p3`/`p4`
apparatus — all hard-pinned to `witnessL` — are unusable below the coercivity theorem. That is
why §1–§3 re-prove the single-bond holonomy facts *generically in the extent* instead of
importing them. Nothing in `NonFlatBackground` is wrong; it is lattice-locked. The gauge-covariance
lemmas there (`holonomyElem_expand`,
`holonomyElem_periodicGaugeTransform_eq_one_iff`) ARE extent-generic and ARE reused here verbatim.

## OPS-3 — how each new result can FAIL, and the control that FIRES

* `shift_ne_self` is FALSE without `0 < L ν`: at `L ν = 0` the direction-`ν` axis is a single site
  and `periodicLatticeShift x ν = x`. `shift_ne_self_fails_at_zero_extent` PROVES the failure.
* `holonomy_singleBond_trichotomy` consumes `hnd` in exactly two of its five branches (the ones
  needing `(shift x ν, μ) ≠ (x, μ)` and `(shift x μ, ν) ≠ (x, ν)`), where without it two of the
  four boundary bonds can be `b₀` at once. **CORRECTED after a nested-validator flag (S75, prose
  overclaim):** an earlier version of this bullet asserted that the holonomy then "becomes `X·X`,
  which is in general none of `X`, `X⁻¹`, `1`". That is WRONG, and hand-computing the degenerate
  cases shows why: when bonds 1 and 3 coincide the word is `X·1·X⁻¹·1 = 1`, and when bonds 2 and
  4 coincide it is `1·X·1⁻¹·X⁻¹ = 1` — still inside the trichotomy. **What is true, and all that
  is claimed:** `hnd` is what THIS PROOF uses to rule out the coincidence; whether the conclusion
  survives without it is NOT established here, in either direction. The falsifiability exhibit
  that IS backed is `shift_ne_self_fails_at_zero_extent`, which proves the hypothesis's own
  premise genuinely fails at `L ν = 0`.
* `tinyU_isRegularHolonomy` is SHARP: `tinyU_not_isRegularHolonomy_of_lt` proves the predicate
  genuinely fails at every threshold below `8/16000001`.
* **The curvature clause of the main theorem is LOAD-BEARING, and the control FIRES**:
  `flat_witness_satisfies_all_but_curvature` proves that the FLAT background `trivialU witL5`
  satisfies EVERY other conjunct of `curved_regularU_coercivity` — admissibility, `ker Q₁(U)`,
  `A ≠ 0`, `0 < bondEnergy A`, strict smallness, `1/4000 ≤ γ''`, and the coercivity bound — while
  `∀ p, holonomyElem (trivialU witL5) p = 1`. So deleting clause (i) makes the statement
  inhabitable at the degenerate flat point; keeping it excludes that point. This is a made-it-fail
  control, not an argument that it would fail.
* **The strict-smallness clause is a genuine `α₁` certificate, and this is not obvious.**
  `0 < γ''` alone is NOT: `Real.sqrt` of a negative number is `0` in Lean, so for a LARGE `α₁`
  the expression `(√(γ₀ − 64α₁²) − 4√2α₁)²` equals `(0 − 4√2α₁)² > 0` and the naive positivity
  clause fires green on a background that violates `hthr` outright. The main theorem therefore
  carries the STRICT DIFFERENCE `0 < √(γ₀ − 64α₁²) − 4√2α₁`, which forces `64α₁² < γ₀` (else the
  first term is `0` and the difference is `≤ 0`). `sqrt_neg_trap` records the trap as a theorem.
* `curved_family_regularU_coercivity`'s `|t| ≤ 1/2000` is load-bearing, not decorative: it is what
  puts `α₁ ≤ 2√2/2000 = 1.415·10⁻³` under the exact joint threshold `√(γ₀/96) = 2.4552·10⁻³` of
  `hthr` and `hsmall`. The largest `|t|` those two hypotheses can tolerate at all is
  `√(γ₀/96)/(2√2) ≈ 8.68·10⁻⁴`; the stated bound `1/2000 = 5·10⁻⁴` sits below it by a factor
  `1.74`, so the hypothesis is NOT tight — it was chosen for clean rational arithmetic, and the
  companion constant `1/6000` is what degrades if it is relaxed toward `8.68·10⁻⁴`.
* `ht : t ≠ 0` is load-bearing: `curvedFamilyU 0` is the flat `trivialU` (`rotElem 0 = 1`), and
  the curvature clause is then FALSE.

## MUTATION RECORD (`compute/regularU_curved_witness/`), 6 run, 6 REJECTED, 0 survivors

Counts below are from the FINAL file (`F_M*.lean` / `F_M*.log`); `M1`–`M5` were also run against
the pre-`§9` version (`M*.log`) with the same verdicts.

| id | mutation | errors | first failure |
|----|----------|--------|---------------|
| `M1` | plaquette directions `(0,1) → (1,2)` — a plaquette the direction-`0` active bond does not touch, where the holonomy provably IS `1` (`curvedU_has_flat_plaquette`) | 8 | `curvedU_eq_tinyU_pair`, then `curvedU_curvature_ne_one` |
| `M2` | `curvedU := trivialU witL5` (flat) | 7 | same, then `curved_regularU_coercivity` |
| `M3` | constant `1/4000 → 1/1000`, numerically FALSE (`γ'' = 3.7565·10⁻⁴`) | 1 | `curved_regularU_coercivity`, at the `gamma_tinyU_ge` application |
| `M4` | field from the FLAT background: `curvedA := genWitness (trivialU witL5)` | 2 | `curvedA_at_curvedBond`, then the main theorem |
| `M5` | kernel clause restated at `trivialU` instead of `curvedU` | 2 | `curved_regularU_coercivity`, then `…_numeric` |
| `M6` | family constant `1/6000 → 1/600`, numerically FALSE (family `γ'' ≥ 1.7424·10⁻⁴`) | 1 | `curved_family_regularU_coercivity`, at `hgam` |

**Disclosed limit:** `M4`/`M5` fail by `isDefEq`/`whnf` heartbeat exhaustion, which proves the two
backgrounds are not definitionally interchangeable in those positions — WEAKER than a proof that
the mutated statements are false. `M1`–`M3` and `M6` fail by clean type mismatch / `linarith`
refutation on statements that are genuinely false.

Also recorded, because the green looked exactly like a real result: `M4`'s FIRST attempt was a
NO-OP (the `sed` anchor `^  genWitness curvedU$` did not match a one-line definition), so it
reported `EXIT=0` — indistinguishable from a surviving mutation. It was caught only by diffing the
mutant against the source, which is now done for every mutant before it is run.
-/

namespace AdalyFormal.Balaban.RegularUCurvedWitness

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice staircasePath)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem holonomyElem_trivialU)
open AdalyFormal.Balaban.RegularityHolonomy (IsRegularHolonomy holonomyDefectSq)
open AdalyFormal.Balaban.NonFlatBackground (defectOfElem defectOfElem_nonneg defectOfElem_inv
  defectOfElem_one holonomyDefectSq_eq_defectOfElem holonomyElem_expand
  holonomyElem_periodicGaugeTransform_eq_one_iff)
open AdalyFormal.Balaban.FullReparamC (freeBond)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5 witL5_four_le witL5_two_dvd)
open AdalyFormal.Balaban.RegularUDomainWitnessGeneralU (tinyM tinyMElem tinyMElem_ne_one tinyU
  siteZero genWitness genWitness_axial genWitness_mem_kerQ genWitness_ne_zero
  genWitness_at_freeBond bondEnergy_genWitness_pos frobSupBond_tinyU_pos gamma_tinyU_ge
  deltaJ_coercive_at_genWitness_tinyU hthr_tinyU hsmall_tinyU)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the lattice is nondegenerate in every direction it needs to be -/

/-- **The forward shift genuinely moves a site**, provided the extent in that direction is
nondegenerate. Both wraparound cases are handled: if `x ν` is the last index the shift lands on
`0 ≠ x ν` (because `0 < L ν`), otherwise it lands on `x ν + 1 ≠ x ν`. -/
theorem shift_ne_self (x : PeriodicLatticeSite L) (ν : Fin 3) (h : 0 < L ν) :
    periodicLatticeShift x ν ≠ x := by
  intro hcon
  have hv := congrFun hcon ν
  rw [periodicLatticeShift, Function.update_self] at hv
  have hval := congrArg Fin.val hv
  rw [Fin.val_add_one] at hval
  split at hval
  · rename_i hlast
    rw [hlast] at hval
    simp [Fin.last] at hval
    omega
  · omega

/-- **OPS-3 failure exhibit for `shift_ne_self`.** At a degenerate extent (`L ν = 0`, a single
site on that axis) the conclusion is FALSE: the shift is the identity. So the hypothesis
`0 < L ν` is load-bearing, not decoration. -/
theorem shift_ne_self_fails_at_zero_extent (x : PeriodicLatticeSite L) (ν : Fin 3)
    (h : L ν = 0) : periodicLatticeShift x ν = x := by
  funext μ
  by_cases hμ : μ = ν
  · subst hμ
    rw [periodicLatticeShift, Function.update_self]
    apply Fin.ext
    -- at `L μ = 0` the fibre `Fin (L μ + 1)` is a singleton, so every element has value `0`
    have hall : ∀ z : Fin (L μ + 1), z.val = 0 := by
      intro z; have hz := z.isLt; omega
    rw [hall (x μ + 1), hall (x μ)]
  · rw [periodicLatticeShift, Function.update_of_ne hμ]

/-! ## §2 — single-active-bond configurations: holonomy, generic in the extent

Stated as hypotheses on an arbitrary `U` (`U b₀ = X`, `U b = 1` off `b₀`) rather than about a new
`def`, so these apply verbatim to `RegularUDomainWitnessGeneralU.tinyU`, to
`NormalizedCounterexampleSearch.singleBondU`, and to any future single-bond family — LAW-19,
and no third copy of the construction (see F1 for why the existing copies do not reach here). -/

/-- **The holonomy at the plaquette based at `b₀`'s own site, with `b₀`'s direction FIRST, is
exactly `X`.** The other three boundary bonds are forced off `b₀`: two by the direction
(`μ ≠ ν`, from the plaquette's own `μ < ν`) and one by `shift_ne_self`. -/
theorem holonomy_singleBond_base_plaquette
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (d : PeriodicPlaquetteDirections)
    (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hb : U (x, d.1.1) = X) (hoff : ∀ b : Bond L, b ≠ (x, d.1.1) → U b = 1)
    (hnd : 0 < L d.1.2) :
    holonomyElem U (x, d) = X := by
  have hmn : d.1.1 ≠ d.1.2 := ne_of_lt d.2
  rw [holonomyElem_expand]
  have e2 : U (periodicLatticeShift x d.1.1, d.1.2) = 1 := by
    refine hoff _ ?_
    intro hc; exact hmn (congrArg Prod.snd hc).symm
  have e3 : U (periodicLatticeShift x d.1.2, d.1.1) = 1 := by
    refine hoff _ ?_
    intro hc; exact shift_ne_self x d.1.2 hnd (congrArg Prod.fst hc)
  have e4 : U (x, d.1.2) = 1 := by
    refine hoff _ ?_
    intro hc; exact hmn (congrArg Prod.snd hc).symm
  show U (x, d.1.1) * U (periodicLatticeShift x d.1.1, d.1.2) *
      (U (periodicLatticeShift x d.1.2, d.1.1))⁻¹ * (U (x, d.1.2))⁻¹ = X
  rw [hb, e2, e3, e4]
  simp

/-- **The trichotomy**: every plaquette holonomy of a single-active-bond configuration is `X`,
`X⁻¹`, or `1`. This is what makes the regularity threshold below equal to the single element's
own defect, with nothing else on the lattice contributing. -/
theorem holonomy_singleBond_trichotomy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (b₀ : Bond L) (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hb : U b₀ = X) (hoff : ∀ b : Bond L, b ≠ b₀ → U b = 1)
    (hnd : ∀ μ : Fin 3, 0 < L μ)
    (p : PeriodicLatticePlaquette L) :
    holonomyElem U p = X ∨ holonomyElem U p = X⁻¹ ∨ holonomyElem U p = 1 := by
  have hmn : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  rw [holonomyElem_expand]
  set x := p.1
  set μ := p.2.1.1
  set ν := p.2.1.2
  by_cases h1 : (x, μ) = b₀
  · have e2 : U (periodicLatticeShift x μ, ν) = 1 := by
      refine hoff _ ?_
      rw [← h1]; intro hc; exact hmn (congrArg Prod.snd hc).symm
    have e3 : U (periodicLatticeShift x ν, μ) = 1 := by
      refine hoff _ ?_
      rw [← h1]; intro hc
      exact shift_ne_self x ν (hnd ν) (congrArg Prod.fst hc)
    have e4 : U (x, ν) = 1 := by
      refine hoff _ ?_
      rw [← h1]; intro hc; exact hmn (congrArg Prod.snd hc).symm
    left
    rw [h1, hb, e2, e3, e4]; simp
  by_cases h2 : (periodicLatticeShift x μ, ν) = b₀
  · have e1 : U (x, μ) = 1 := hoff _ h1
    have e3 : U (periodicLatticeShift x ν, μ) = 1 := by
      refine hoff _ ?_
      rw [← h2]; intro hc; exact hmn (congrArg Prod.snd hc)
    have e4 : U (x, ν) = 1 := by
      refine hoff _ ?_
      rw [← h2]; intro hc
      exact shift_ne_self x μ (hnd μ) (congrArg Prod.fst hc).symm
    left
    rw [h2, hb, e1, e3, e4]; simp
  by_cases h3 : (periodicLatticeShift x ν, μ) = b₀
  · have e1 : U (x, μ) = 1 := hoff _ h1
    have e2 : U (periodicLatticeShift x μ, ν) = 1 := hoff _ h2
    have e4 : U (x, ν) = 1 := by
      refine hoff _ ?_
      rw [← h3]; intro hc; exact hmn (congrArg Prod.snd hc).symm
    right; left
    rw [h3, hb, e1, e2, e4]; simp
  by_cases h4 : (x, ν) = b₀
  · have e1 : U (x, μ) = 1 := hoff _ h1
    have e2 : U (periodicLatticeShift x μ, ν) = 1 := hoff _ h2
    have e3 : U (periodicLatticeShift x ν, μ) = 1 := hoff _ h3
    right; left
    rw [h4, hb, e1, e2, e3]; simp
  · right; right
    rw [hoff _ h1, hoff _ h2, hoff _ h3, hoff _ h4]; simp

/-- **A single-active-bond configuration is FLAT at every plaquette whose two directions both
differ from the active bond's direction.** All four boundary bonds then carry a direction `≠ b₀.2`,
so none of them is `b₀`. Used below to prove that the `∀ p` strengthening of the curvature clause
is FALSE (the S92 check). -/
theorem holonomy_singleBond_eq_one_of_dirs_ne
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (b₀ : Bond L) (hoff : ∀ b : Bond L, b ≠ b₀ → U b = 1)
    (p : PeriodicLatticePlaquette L) (h1 : p.2.1.1 ≠ b₀.2) (h2 : p.2.1.2 ≠ b₀.2) :
    holonomyElem U p = 1 := by
  rw [holonomyElem_expand]
  rw [hoff _ (fun hc => h1 (congrArg Prod.snd hc)),
    hoff _ (fun hc => h2 (congrArg Prod.snd hc)),
    hoff _ (fun hc => h1 (congrArg Prod.snd hc)),
    hoff _ (fun hc => h2 (congrArg Prod.snd hc))]
  simp

/-- **Generic single-bond regularity at the SHARP threshold.** The extent-generic counterpart of
`NonFlatBackground.singleBondU_isRegularHolonomy`, which is stated only on `witnessL`. -/
theorem singleBond_isRegularHolonomy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (b₀ : Bond L) (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hb : U b₀ = X) (hoff : ∀ b : Bond L, b ≠ b₀ → U b = 1)
    (hnd : ∀ μ : Fin 3, 0 < L μ) :
    IsRegularHolonomy U (defectOfElem X) := by
  intro p
  rw [holonomyDefectSq_eq_defectOfElem]
  rcases holonomy_singleBond_trichotomy U b₀ X hb hoff hnd p with h | h | h
  · rw [h]
  · rw [h, defectOfElem_inv]
  · rw [h, defectOfElem_one]; exact defectOfElem_nonneg X

/-! ## §3 — `tinyU b₀`'s curvature and its sharp regularity threshold -/

theorem tinyU_at (b₀ : Bond L) : tinyU b₀ b₀ = tinyMElem := by
  rw [tinyU, if_pos rfl]

theorem tinyU_off (b₀ : Bond L) {b : Bond L} (h : b ≠ b₀) : tinyU b₀ b = 1 := by
  rw [tinyU, if_neg h]

/-- **`defectOfElem tinyMElem = 8/16000001`, exactly.** `4 − 2·Re tr M = 4 − 4·(15999999/16000001)`
`= 8/16000001`. Note this reproduces, independently, the exact value
`RegularUDomainWitnessGeneralU.frobSq_tinyM_sub_one` computes for `‖M − 1‖²_F` — the two
quantities are the same number by the standard unitary identity, and the agreement is a
cross-check, not an assumption. -/
theorem defectOfElem_tinyMElem : defectOfElem tinyMElem = 8 / 16000001 := by
  unfold defectOfElem
  show (4 : ℝ) - 2 * (Matrix.trace tinyM).re = 8 / 16000001
  rw [Matrix.trace_fin_two]
  simp [tinyM]
  norm_num

/-- **`tinyU b₀` is regular at the tiny threshold `8/16000001 ≈ 5·10⁻⁷`.** -/
theorem tinyU_isRegularHolonomy (b₀ : Bond L) (hnd : ∀ μ : Fin 3, 0 < L μ) :
    IsRegularHolonomy (tinyU b₀) (8 / 16000001 : ℝ) := by
  rw [← defectOfElem_tinyMElem]
  exact singleBond_isRegularHolonomy (tinyU b₀) b₀ tinyMElem (tinyU_at b₀)
    (fun _ hb => tinyU_off b₀ hb) hnd

/-- **The threshold is SHARP (OPS-3)**: below `8/16000001` the predicate genuinely fails, so the
bound is attained rather than slack. -/
theorem tinyU_not_isRegularHolonomy_of_lt
    (x : PeriodicLatticeSite L) (d : PeriodicPlaquetteDirections) (hnd : 0 < L d.1.2)
    {M : ℝ} (hM : M < 8 / 16000001) :
    ¬ IsRegularHolonomy (tinyU (x, d.1.1)) M := by
  intro hreg
  have hb := hreg (x, d)
  rw [holonomyDefectSq_eq_defectOfElem,
    holonomy_singleBond_base_plaquette (tinyU (x, d.1.1)) x d tinyMElem
      (tinyU_at (x, d.1.1)) (fun b hb' => tinyU_off (x, d.1.1) hb') hnd,
    defectOfElem_tinyMElem] at hb
  linarith

/-- **THE CURVATURE.** `tinyU (x, d.1.1)` has a plaquette whose holonomy is `tinyMElem ≠ 1`: its
field strength is genuinely nonzero. This is the statement `tinyU_ne_trivialU` could not make —
that one is a bare link value, which is gauge-VARIANT. -/
theorem tinyU_curvature_ne_one
    (x : PeriodicLatticeSite L) (d : PeriodicPlaquetteDirections) (hnd : 0 < L d.1.2) :
    holonomyElem (tinyU (x, d.1.1)) (x, d) ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [holonomy_singleBond_base_plaquette (tinyU (x, d.1.1)) x d tinyMElem
    (tinyU_at (x, d.1.1)) (fun _ hb => tinyU_off (x, d.1.1) hb) hnd]
  exact tinyMElem_ne_one

/-- **The GAUGE-INVARIANT separation.** `tinyU (x, d.1.1)` is not the gauge transform, by ANY `γ`,
of ANY configuration flat at the exhibited plaquette — `trivialU`, `pureGaugeU`, and every gauge
orbit of a flat field included. Strictly stronger than `≠ trivialU`. -/
theorem tinyU_not_gaugeTransform_of_flat
    (x : PeriodicLatticeSite L) (d : PeriodicPlaquetteDirections) (hnd : 0 < L d.1.2)
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hV : holonomyElem V (x, d) = 1) :
    tinyU (x, d.1.1) ≠ periodicGaugeTransform γ V := by
  intro h
  apply tinyU_curvature_ne_one x d hnd
  rw [h, holonomyElem_periodicGaugeTransform_eq_one_iff]
  exact hV

/-! ## §4 — the `Real.sqrt`-of-a-negative trap, recorded as a theorem

Why the main theorem carries the STRICT DIFFERENCE `0 < √(γ₀ − 64α₁²) − 4√2·α₁` and not merely
`0 < γ''`. -/

/-- **`0 < γ''` IS NOT A SMALLNESS CERTIFICATE.** `Real.sqrt` of a negative real is `0`, so at any
`α₁` violating `hthr` outright (`γ₀ < 64α₁²`) the squared expression is `(0 − 4√2α₁)² > 0`: the
naive positivity clause fires green on a background the theorem's hypotheses exclude. -/
theorem sqrt_neg_trap {γ₀ a : ℝ} (ha : 0 < a) (hbad : γ₀ - 64 * a ^ 2 < 0) :
    0 < (Real.sqrt (γ₀ - 64 * a ^ 2) - 4 * Real.sqrt 2 * a) ^ 2 := by
  rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt hbad)]
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have : 0 < 4 * Real.sqrt 2 * a := by positivity
  nlinarith

/-- **The strict difference, by contrast, FORCES the threshold.** If
`0 < √(γ₀ − 64α₁²) − 4√2·α₁` with `α₁ ≥ 0`, then `64·α₁² < γ₀`: otherwise the square root is `0`
and the difference is `≤ 0`. So the clause carried by the main theorem is a genuine `α₁`
certificate. -/
theorem strict_diff_forces_threshold {γ₀ a : ℝ} (ha : 0 ≤ a)
    (h : 0 < Real.sqrt (γ₀ - 64 * a ^ 2) - 4 * Real.sqrt 2 * a) :
    64 * a ^ 2 < γ₀ := by
  by_contra hcon
  rw [not_lt] at hcon
  rw [Real.sqrt_eq_zero_of_nonpos (by linarith)] at h
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- The strict difference at `tinyU b₀`, from the already-proved `≥ 0` (`hsmall_tinyU`) and the
already-proved `(diff)² ≥ 1/4000` (`gamma_tinyU_ge`). -/
theorem strict_small_tinyU (b₀ : Bond L) :
    0 < Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond (tinyU b₀) ^ 2)
      - 4 * Real.sqrt 2 * frobSupBond (tinyU b₀) := by
  have hnn := hsmall_tinyU b₀
  have hsq := gamma_tinyU_ge b₀
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso
    rw [← h] at hsq
    norm_num at hsq

/-! ## §5 — the named objects on `witL5` (`L μ = 5`: `4 ≤ 5` ✓, `2 ∣ 6` ✓) -/

theorem witL5_pos : ∀ μ : Fin 3, 0 < witL5 μ := by decide

/-- The bond carrying the curvature: **exactly the bond where the admissible witness field
`genWitness` is nonzero** (`genWitness_at_freeBond`). Its direction is `0` by construction of
`freeBond`. -/
noncomputable def curvedBond : Bond witL5 := freeBond 2 (siteZero witL5)

theorem curvedBond_dir : curvedBond.2 = (0 : Fin 3) := rfl

/-- The plaquette directions `(0,1)` — `curvedBond`'s direction first. -/
def dir01 : PeriodicPlaquetteDirections := ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩

/-- **The CURVED background**: `M(15999999/16000001, 8000/16000001)` on `curvedBond`, `1`
everywhere else. -/
noncomputable def curvedU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5 :=
  tinyU curvedBond

/-- The plaquette at which the curvature is exhibited. -/
noncomputable def curvedPlaq : PeriodicLatticePlaquette witL5 := (curvedBond.1, dir01)

/-- **The admissible field**: `FullReparamC`'s `(3.157)` reparametrization witness AT THE CURVED
BACKGROUND — `ker Q₁(curvedU)`, not `ker Q₁(trivialU)`. -/
noncomputable def curvedA : Bond witL5 → SuTwo := genWitness curvedU

theorem curvedU_eq_tinyU_pair :
    curvedU = tinyU (curvedBond.1, dir01.1.1) := rfl

theorem curvedPlaq_eq_pair : curvedPlaq = (curvedBond.1, dir01) := rfl

/-- **`curvedU` HAS NONZERO CURVATURE.** -/
theorem curvedU_curvature_ne_one :
    holonomyElem curvedU curvedPlaq ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  tinyU_curvature_ne_one curvedBond.1 dir01 (by decide)

theorem curvedU_has_curved_plaquette :
    ∃ p : PeriodicLatticePlaquette witL5,
      holonomyElem curvedU p ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨curvedPlaq, curvedU_curvature_ne_one⟩

/-- **`curvedU` is not a gauge transform of any flat configuration.** -/
theorem curvedU_not_gaugeTransform_of_flat
    (γ : PeriodicLatticeSite witL5 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5)
    (hV : ∀ p : PeriodicLatticePlaquette witL5, holonomyElem V p = 1) :
    curvedU ≠ periodicGaugeTransform γ V :=
  tinyU_not_gaugeTransform_of_flat curvedBond.1 dir01 (by decide) γ V (hV curvedPlaq)

/-- **`curvedU` is regular at the tiny threshold `8/16000001`** — Bałaban's `Mα₀`-smallness regime,
populated here by a background with genuine field strength. -/
theorem curvedU_isRegularHolonomy : IsRegularHolonomy curvedU (8 / 16000001 : ℝ) :=
  tinyU_isRegularHolonomy curvedBond witL5_pos

theorem curvedU_not_isRegularHolonomy_of_lt {M : ℝ} (hM : M < 8 / 16000001) :
    ¬ IsRegularHolonomy curvedU M :=
  tinyU_not_isRegularHolonomy_of_lt curvedBond.1 dir01 (by decide) hM

/-- The curvature sits ON the support of the field: `curvedA` equals `suTwoWitness ≠ 0` at
`curvedBond`, the one bond where `curvedU ≠ 1`. -/
theorem curvedA_at_curvedBond :
    curvedA curvedBond = AdalyFormal.Balaban.CovariantOperators.suTwoWitness :=
  genWitness_at_freeBond witL5_two_dvd curvedU

/-! ## §6 — THE DELIVERABLE: GOAL_LEMMA §4 (b2) -/

/-- **THE REGULAR-`U` COERCIVITY AT A BACKGROUND WITH PROVABLY NONZERO CURVATURE.**
On the compatible torus `witL5` (`L μ = 5`, so `4 ≤ L μ` and `2 ∣ L μ + 1`), for the explicit
named pair `(curvedU, curvedA)`:

* **(i) `curvedU` is CURVED** — `holonomyElem curvedU curvedPlaq ≠ 1` — and, gauge-invariantly, is
  not the gauge transform of ANY flat configuration. It is nonetheless regular at the tiny
  threshold `8/16000001`, i.e. inside Bałaban's small-`Mα₀` regime.
* **(ii) `curvedA` is admissible** (su(2) axial gauge on every staircase) and lies in
  `ker Q₁(curvedU)` — **the same, curved, background**, not `trivialU`.
* **(iii)** `curvedA ≠ 0` and `0 < bondEnergy curvedA`.
* **(iv)** the coercivity bound of `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU`
  holds at `(curvedU, curvedA)` **with a constant bounded below by the explicit numeral
  `1/4000 > 0`**, together with the strict smallness `0 < √(γ₀ − 64α₁²) − 4√2·α₁` (which by
  `strict_diff_forces_threshold` FORCES `64·α₁² < γ₀`, so the constant's positivity is not the
  `Real.sqrt`-of-a-negative artefact of `sqrt_neg_trap`).

Named form; the `∃`-form is the corollary below. -/
theorem curved_regularU_coercivity :
    -- (i) genuinely curved, and gauge-invariantly so, yet regular at a tiny threshold
    holonomyElem curvedU curvedPlaq ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
    (∀ (γ : PeriodicLatticeSite witL5 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
        (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5),
        (∀ p : PeriodicLatticePlaquette witL5, holonomyElem V p = 1) →
        curvedU ≠ periodicGaugeTransform γ V) ∧
    IsRegularHolonomy curvedU (8 / 16000001 : ℝ) ∧
    0 < frobSupBond curvedU ∧
    -- (ii) admissible, and in ker Q₁ of the SAME curved background
    (∀ y : PeriodicLatticeSite witL5, y ∈ CoarseLattice witL5 2 →
        ∀ x : PeriodicLatticeSite witL5, x ∈ blockOf y 2 →
        ∀ b ∈ staircasePath y x, curvedA b = 0) ∧
    (∀ c : CoarseBond witL5 2, lineCoarseRestrictCov curvedU 2 curvedA c = 0) ∧
    -- (iii) nondegenerate field
    curvedA ≠ 0 ∧ 0 < bondEnergy curvedA ∧
    -- (iv) strictly positive coercivity constant, and the bound
    0 < Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond curvedU ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond curvedU ∧
    (1 / 4000 : ℝ) ≤
      (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond curvedU ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond curvedU) ^ 2 ∧
    (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond curvedU ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond curvedU) ^ 2 * bondEnergy curvedA
      ≤ dstarDQuadForm curvedU curvedA := by
  refine ⟨curvedU_curvature_ne_one, curvedU_not_gaugeTransform_of_flat,
    curvedU_isRegularHolonomy, frobSupBond_tinyU_pos curvedBond,
    genWitness_axial witL5_two_dvd curvedU, genWitness_mem_kerQ witL5_two_dvd curvedU,
    genWitness_ne_zero witL5_two_dvd curvedU, bondEnergy_genWitness_pos witL5_two_dvd curvedU,
    strict_small_tinyU curvedBond, gamma_tinyU_ge curvedBond, ?_⟩
  exact AdalyFormal.Balaban.RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU
    witL5_four_le witL5_two_dvd curvedU curvedA
    (genWitness_axial witL5_two_dvd curvedU) (genWitness_mem_kerQ witL5_two_dvd curvedU)
    (hthr_tinyU curvedBond) (hsmall_tinyU curvedBond)

/-- **The strictly positive, explicitly numerical form.**
`0 < (1/4000)·bondEnergy curvedA ≤ dstarDQuadForm curvedU curvedA` at a CURVED background. -/
theorem curved_regularU_coercivity_numeric :
    holonomyElem curvedU curvedPlaq ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
    0 < (1 / 4000 : ℝ) * bondEnergy curvedA ∧
    (1 / 4000 : ℝ) * bondEnergy curvedA ≤ dstarDQuadForm curvedU curvedA := by
  obtain ⟨_, _, _, _, _, _, _, hE, _, hγ, hbound⟩ := curved_regularU_coercivity
  refine ⟨curvedU_curvature_ne_one, mul_pos (by norm_num) hE, ?_⟩
  nlinarith [hbound, hγ, hE]

/-- **`∃`-form (S91 target).** Every conjunct of the named theorem, existentially quantified over
the pair `(U, A)`. Registered in `formal/S91_REGISTRY.tsv`; see §7 for the degenerate-inhabitation
attack record. -/
theorem exists_curved_regularU_coercivity :
    ∃ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5)
      (A : Bond witL5 → SuTwo) (p : PeriodicLatticePlaquette witL5),
      holonomyElem U p ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      (∀ (γ : PeriodicLatticeSite witL5 → Matrix.specialUnitaryGroup (Fin 2) ℂ)
          (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5),
          (∀ q : PeriodicLatticePlaquette witL5, holonomyElem V q = 1) →
          U ≠ periodicGaugeTransform γ V) ∧
      IsRegularHolonomy U (8 / 16000001 : ℝ) ∧
      0 < frobSupBond U ∧
      (∀ y : PeriodicLatticeSite witL5, y ∈ CoarseLattice witL5 2 →
          ∀ x : PeriodicLatticeSite witL5, x ∈ blockOf y 2 →
          ∀ b ∈ staircasePath y x, A b = 0) ∧
      (∀ c : CoarseBond witL5 2, lineCoarseRestrictCov U 2 A c = 0) ∧
      A ≠ 0 ∧ 0 < bondEnergy A ∧
      0 < Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
          - 4 * Real.sqrt 2 * frobSupBond U ∧
      (1 / 4000 : ℝ) ≤
        (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
          - 4 * Real.sqrt 2 * frobSupBond U) ^ 2 ∧
      (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
          - 4 * Real.sqrt 2 * frobSupBond U) ^ 2 * bondEnergy A
        ≤ dstarDQuadForm U A :=
  ⟨curvedU, curvedA, curvedPlaq, curved_regularU_coercivity⟩

/-! ## §7 — DEGENERATE-INHABITATION ATTACK RECORD (S91), and the made-it-fail control

Attacks attempted on `exists_curved_regularU_coercivity`, conjunct by conjunct:

* **`A = 0`** — killed twice over, by `A ≠ 0` and independently by `0 < bondEnergy A`. With
  `A = 0` the coercivity inequality would read `γ''·0 ≤ 0`, true and empty; the energy clause is
  what makes the bound non-trivial rather than merely non-vacuous.
* **A FLAT `U` (`trivialU`, `pureGaugeU`, any gauge orbit of a flat field)** — killed by clause 1
  and INDEPENDENTLY by clause 2, which is gauge-INVARIANT and therefore cannot be discharged by a
  gauge representative. The control below proves this is the ONLY thing keeping the flat point
  out: `trivialU witL5` satisfies every other conjunct.
* **A large-curvature `U`** — killed by `IsRegularHolonomy U (8/16000001)` and, quantitatively, by
  the strict smallness clause via `strict_diff_forces_threshold`.
* **"Take the constant `0`"** — blocked: the constant is bounded below by the numeral `1/4000`,
  and the STRICT difference clause rules out the `Real.sqrt`-of-a-negative artefact
  (`sqrt_neg_trap`) that would let a large-`α₁` background fake positivity.
* **"Choose a huge `dstarDQuadForm`"** — not free data: `dstarDQuadForm U A` is a `def` applied to
  the same `U, A` the other clauses pin.
* **"Choose an easy plaquette `p`"** — `p` is existential, but the requirement is
  `holonomyElem U p ≠ 1`, i.e. the prover must find a plaquette where the holonomy is
  NON-trivial; `holonomy_singleBond_trichotomy` shows all but the plaquettes touching the single
  active bond REFUTE it, so there is no cheap witness. Reversing the quantifier here would be the
  S92 defect; it is not present, and this is BACKED rather than argued —
  `curvedU_forall_curved_is_false` PROVES that the `∀ p` strengthening is FALSE at `curvedU`
  itself (`curvedU_has_flat_plaquette` exhibits a plaquette in directions `(1,2)`, which the
  direction-`0` active bond cannot touch, whose holonomy is exactly `1`). So the existential is
  the strongest true shape here, not a weakening of an available universal. -/

/-- **THE CONTROL FIRES.** The FLAT background `trivialU witL5` satisfies EVERY conjunct of
`curved_regularU_coercivity` EXCEPT the two curvature clauses — which it violates maximally
(`∀ p, holonomyElem (trivialU witL5) p = 1`). Deleting clause (i) therefore admits the degenerate
flat point; clause (i) is load-bearing, and this is a made-it-fail exhibit rather than an
assertion that it would fail.

Note the flat background's constant is even BETTER (`α₁ = 0` gives `γ'' = γ₀ = 1/1728 > 1/4000`),
which is exactly why a constant-positivity clause alone can never detect the degeneracy. -/
theorem flat_witness_satisfies_all_but_curvature :
    (∀ p : PeriodicLatticePlaquette witL5,
        holonomyElem (trivialU witL5) p = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
    (∀ y : PeriodicLatticeSite witL5, y ∈ CoarseLattice witL5 2 →
        ∀ x : PeriodicLatticeSite witL5, x ∈ blockOf y 2 →
        ∀ b ∈ staircasePath y x, genWitness (trivialU witL5) b = 0) ∧
    (∀ c : CoarseBond witL5 2,
        lineCoarseRestrictCov (trivialU witL5) 2 (genWitness (trivialU witL5)) c = 0) ∧
    genWitness (trivialU witL5) ≠ 0 ∧
    0 < bondEnergy (genWitness (trivialU witL5)) := by
  exact ⟨fun p => holonomyElem_trivialU p,
    genWitness_axial witL5_two_dvd (trivialU witL5),
    genWitness_mem_kerQ witL5_two_dvd (trivialU witL5),
    genWitness_ne_zero witL5_two_dvd (trivialU witL5),
    bondEnergy_genWitness_pos witL5_two_dvd (trivialU witL5)⟩

/-- Plaquette directions `(1,2)` — neither of them the active bond's direction `0`. -/
def dir12 : PeriodicPlaquetteDirections := ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩

/-- **`curvedU` IS flat somewhere** — at every plaquette in directions `(1,2)`, which the
direction-`0` active bond cannot touch. -/
theorem dir12_fst_ne_curvedBond_dir : dir12.1.1 ≠ curvedBond.2 := by
  rw [curvedBond_dir]; decide

theorem dir12_snd_ne_curvedBond_dir : dir12.1.2 ≠ curvedBond.2 := by
  rw [curvedBond_dir]; decide

theorem curvedU_has_flat_plaquette (y : PeriodicLatticeSite witL5) :
    holonomyElem curvedU (y, dir12) = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  holonomy_singleBond_eq_one_of_dirs_ne curvedU curvedBond
    (fun _ hb => tinyU_off curvedBond hb) (y, dir12)
    dir12_fst_ne_curvedBond_dir dir12_snd_ne_curvedBond_dir

/-- **THE S92 CHECK, BACKED.** The `∀ p` strengthening of the curvature clause is FALSE at
`curvedU`, so the existential in `curvedU_has_curved_plaquette` /
`exists_curved_regularU_coercivity` is the strongest TRUE shape — it is not a quantifier
weakening of an available universal. -/
theorem curvedU_forall_curved_is_false :
    ¬ (∀ p : PeriodicLatticePlaquette witL5,
        holonomyElem curvedU p ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro h
  exact h (curvedBond.1, dir12) (curvedU_has_flat_plaquette curvedBond.1)

/-- **F1, BACKED.** `AdmissibleSubspace.witnessL` — the lattice the whole `NonFlatBackground`
curvature apparatus is pinned to — FAILS `deltaJ_regularU_coercive_on_kerQU`'s standing hypothesis
`hL : ∀ μ, 4 ≤ L μ`. This is why §1–§3 had to re-prove the single-bond holonomy facts generically
in the extent rather than importing `nonflatU`. -/
theorem witnessL_fails_hL :
    ¬ (∀ μ : Fin 3, 4 ≤ AdalyFormal.Balaban.AdmissibleSubspace.witnessL μ) := by decide

/-- …while `witL5` satisfies it, which is why the assembly lives there. -/
theorem witL5_satisfies_hL : ∀ μ : Fin 3, 4 ≤ witL5 μ := witL5_four_le

/-- The differential: `curvedU` and `trivialU witL5` are separated BY THE CURVATURE, and the
separation is gauge-invariant (it survives every gauge transformation of either side). -/
theorem curvedU_ne_trivialU_by_curvature : curvedU ≠ trivialU witL5 := by
  intro h
  exact curvedU_curvature_ne_one (h ▸ holonomyElem_trivialU curvedPlaq)

/-! ## §9 — OPS-10: FROM ONE POINT TO A ONE-PARAMETER FAMILY

The theorem above is at one hand-chosen background. That invites the obvious objection: the
witness was picked, so nothing is known about the curved part of the domain beyond a single
point. §9 removes it. The rational rotation family `NonFlatBackground.rotElem t` (`a(t) =
(1−t²)/(1+t²)`, `b(t) = 2t/(1+t²)`, `a²+b² = 1` a rational identity) is placed on `curvedBond`,
and the coercivity is proved at EVERY `t` with `0 < |t| ≤ 1/2000` — a continuum of genuinely
curved backgrounds with curvature `8t²/(1+t²) → 0`, uniformly coercive with constant `≥ 1/6000`.

CONSOLIDATION, not a fourth construction (LAW-19): the single-active-bond family is given ONE
extent-generic, `X`-generic definition `bondU`, and BOTH pre-existing copies are proved to be its
instances — `RegularUDomainWitnessGeneralU.tinyU b₀ = bondU b₀ tinyMElem` and
`NormalizedCounterexampleSearch.singleBondU X = bondU (witnessY, 0) X`, each by `rfl`. -/

/-- **The single-active-bond family, generic in the extent AND in the group element.** The two
pre-existing copies in the tree are its instances (proved `rfl` immediately below). -/
noncomputable def bondU (b₀ : Bond L) (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
  fun b => if b = b₀ then X else 1

theorem tinyU_eq_bondU (b₀ : Bond L) : tinyU b₀ = bondU b₀ tinyMElem := rfl

theorem singleBondU_eq_bondU (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU X
      = bondU (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)) X := rfl

theorem bondU_at (b₀ : Bond L) (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    bondU b₀ X b₀ = X := by rw [bondU, if_pos rfl]

theorem bondU_off (b₀ : Bond L) (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) {b : Bond L}
    (h : b ≠ b₀) : bondU b₀ X b = 1 := by rw [bondU, if_neg h]

/-- `α₁(bondU b₀ X) = frobNorm(X − 1)` exactly: the sup over bonds is attained at `b₀`, every
other bond contributing `0`. -/
theorem frobSupBond_bondU (b₀ : Bond L) (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobSupBond (bondU b₀ X)
      = AdalyFormal.Balaban.RMapLipschitz.frobNorm ((X : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun b _ => ?_)
    by_cases hb : b = b₀
    · rw [show ((bondU b₀ X b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = (X : Matrix (Fin 2) (Fin 2) ℂ) by rw [bondU, if_pos hb]]
    · rw [show ((bondU b₀ X b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) = 1 by rw [bondU, if_neg hb]; rfl,
        sub_self, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
      exact AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _
  · have hle := AdalyFormal.Balaban.RegularUPerturbation.frobNorm_le_frobSupBond (bondU b₀ X) b₀
    rwa [show ((bondU b₀ X b₀ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = (X : Matrix (Fin 2) (Fin 2) ℂ) by rw [bondU, if_pos rfl]] at hle

/-- **The curved FAMILY on `witL5`**: `rotElem t` on `curvedBond`, `1` elsewhere. -/
noncomputable def curvedFamilyU (t : ℝ) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL5 :=
  bondU curvedBond (AdalyFormal.Balaban.NonFlatBackground.rotElem t)

/-- **Every member with `t ≠ 0` is genuinely CURVED.** -/
theorem curvedFamilyU_curvature_ne_one {t : ℝ} (ht : t ≠ 0) :
    holonomyElem (curvedFamilyU t) curvedPlaq ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [show curvedPlaq = (curvedBond.1, dir01) from rfl,
    holonomy_singleBond_base_plaquette (curvedFamilyU t) curvedBond.1 dir01
      (AdalyFormal.Balaban.NonFlatBackground.rotElem t)
      (bondU_at curvedBond _) (fun _ hb => bondU_off curvedBond _ hb) (by decide)]
  exact AdalyFormal.Balaban.NonFlatBackground.rotElem_ne_one ht

/-- Regularity at the sharp threshold `8t²/(1+t²)`, which tends to `0` with `t`. -/
theorem curvedFamilyU_isRegularHolonomy (t : ℝ) :
    IsRegularHolonomy (curvedFamilyU t) (8 * t ^ 2 / (1 + t ^ 2)) := by
  rw [← AdalyFormal.Balaban.NonFlatBackground.defectOfElem_rotElem t]
  exact singleBond_isRegularHolonomy (curvedFamilyU t) curvedBond _
    (bondU_at curvedBond _) (fun _ hb => bondU_off curvedBond _ hb) witL5_pos

/-- `α₁ ≤ 2√2·|t|` for the family — the input to every smallness estimate below. -/
theorem frobSupBond_curvedFamilyU_le (t : ℝ) :
    frobSupBond (curvedFamilyU t) ≤ 2 * Real.sqrt 2 * |t| := by
  rw [curvedFamilyU, frobSupBond_bondU, AdalyFormal.Balaban.NonFlatBackground.rotElem_coe,
    AdalyFormal.Balaban.RMapLipschitz.frobNorm,
    AdalyFormal.Balaban.NonFlatBackground.frobSq_rotM_sub_one,
    ← AdalyFormal.Balaban.NonFlatBackground.sqrt_eight_mul_sq]
  exact Real.sqrt_le_sqrt (AdalyFormal.Balaban.NonFlatBackground.nonflatU_defect_le t)

/-- `α₁² ≤ 8t²`. -/
theorem frobSupBond_curvedFamilyU_sq_le (t : ℝ) :
    frobSupBond (curvedFamilyU t) ^ 2 ≤ 8 * t ^ 2 := by
  have h1 := frobSupBond_curvedFamilyU_le t
  have h0 := AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg (curvedFamilyU t)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith [Real.sqrt_nonneg 2, abs_nonneg t]

/-- `4√2·α₁ ≤ 16·|t|`. -/
theorem four_sqrt2_frobSup_le (t : ℝ) :
    4 * Real.sqrt 2 * frobSupBond (curvedFamilyU t) ≤ 16 * |t| := by
  have h1 := frobSupBond_curvedFamilyU_le t
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [abs_nonneg t]

/-- **THE FAMILY VERSION.** For EVERY `t` with `0 < |t| ≤ 1/2000`, the regular-`U` coercivity of
`deltaJ_regularU_coercive_on_kerQU` holds at the genuinely CURVED background `curvedFamilyU t`,
with a constant bounded below by the `t`-INDEPENDENT numeral `1/6000`, at the nonzero admissible
field `genWitness (curvedFamilyU t) ∈ ker Q₁(curvedFamilyU t)`.

The curvature `8t²/(1+t²)` sweeps the whole interval `(0, 8/4000001]`, so the small-`Mα₀` regime
that Bałaban's regular-`U` hypothesis singles out is populated here by a CONTINUUM of curved
backgrounds, not by one point — and the coercivity constant does not degrade as the curvature
goes to zero. Arithmetic, explicitly: `α₁ ≤ 2√2|t| ≤ 2√2/2000 < 1.415·10⁻³ < √(γ₀/96) =
2.4552·10⁻³` (the exact joint threshold of `hthr` and `hsmall`); `64α₁² ≤ 512t² ≤ 1.28·10⁻⁴ ≤ γ₀
= 1/1728`; `√(γ₀ − 64α₁²) ≥ 212/10000` since `(212/10000)² = 4.4944·10⁻⁴ ≤ 4.507·10⁻⁴`;
`4√2·α₁ ≤ 16|t| ≤ 8·10⁻³`; difference `≥ 1.32·10⁻²`, square `≥ 1.7424·10⁻⁴ ≥ 1/6000`. -/
theorem curved_family_regularU_coercivity {t : ℝ} (ht : t ≠ 0) (htb : |t| ≤ 1 / 2000) :
    holonomyElem (curvedFamilyU t) curvedPlaq ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
    IsRegularHolonomy (curvedFamilyU t) (8 * t ^ 2 / (1 + t ^ 2)) ∧
    0 < 8 * t ^ 2 / (1 + t ^ 2) ∧
    genWitness (curvedFamilyU t) ≠ 0 ∧
    0 < bondEnergy (genWitness (curvedFamilyU t)) ∧
    (∀ c : CoarseBond witL5 2,
      lineCoarseRestrictCov (curvedFamilyU t) 2 (genWitness (curvedFamilyU t)) c = 0) ∧
    (1 / 6000 : ℝ) * bondEnergy (genWitness (curvedFamilyU t))
      ≤ dstarDQuadForm (curvedFamilyU t) (genWitness (curvedFamilyU t)) := by
  set a : ℝ := frobSupBond (curvedFamilyU t) with ha
  have h0 : 0 ≤ a := AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg _
  have hasq : a ^ 2 ≤ 8 * t ^ 2 := frobSupBond_curvedFamilyU_sq_le t
  have hT : 4 * Real.sqrt 2 * a ≤ 16 * |t| := four_sqrt2_frobSup_le t
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  have habs0 : 0 ≤ |t| := abs_nonneg t
  have ht2 : t ^ 2 ≤ (1 / 2000 : ℝ) ^ 2 := by nlinarith
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  -- hthr
  have hthr : 64 * a ^ 2 ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by
    rw [hcast]; nlinarith
  -- lower bound on the square root
  have hS : (212 / 10000 : ℝ)
      ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * a ^ 2) := by
    rw [hcast]
    have hrw : (212 / 10000 : ℝ) = Real.sqrt ((212 / 10000 : ℝ) ^ 2) :=
      (Real.sqrt_sq (by norm_num)).symm
    rw [hrw]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hTb : 4 * Real.sqrt 2 * a ≤ 8 / 1000 := by nlinarith
  have hdiff : (132 / 10000 : ℝ)
      ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * a ^ 2) - 4 * Real.sqrt 2 * a := by
    linarith
  have hsmall : 0 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * a ^ 2)
      - 4 * Real.sqrt 2 * a := by linarith
  have hgam : (1 / 6000 : ℝ)
      ≤ (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * a ^ 2)
          - 4 * Real.sqrt 2 * a) ^ 2 := by nlinarith [hdiff]
  have hE : 0 < bondEnergy (genWitness (curvedFamilyU t)) :=
    bondEnergy_genWitness_pos witL5_two_dvd (curvedFamilyU t)
  have key := AdalyFormal.Balaban.RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU
    witL5_four_le witL5_two_dvd (curvedFamilyU t) (genWitness (curvedFamilyU t))
    (genWitness_axial witL5_two_dvd (curvedFamilyU t))
    (genWitness_mem_kerQ witL5_two_dvd (curvedFamilyU t)) hthr hsmall
  refine ⟨curvedFamilyU_curvature_ne_one ht, curvedFamilyU_isRegularHolonomy t,
    AdalyFormal.Balaban.NonFlatBackground.nonflatU_defect_pos ht,
    genWitness_ne_zero witL5_two_dvd (curvedFamilyU t), hE,
    genWitness_mem_kerQ witL5_two_dvd (curvedFamilyU t), ?_⟩
  nlinarith [key, hgam, hE]

/-! ## §8 — axiom audit -/

#print axioms shift_ne_self
#print axioms shift_ne_self_fails_at_zero_extent
#print axioms holonomy_singleBond_base_plaquette
#print axioms holonomy_singleBond_trichotomy
#print axioms holonomy_singleBond_eq_one_of_dirs_ne
#print axioms singleBond_isRegularHolonomy
#print axioms tinyU_at
#print axioms tinyU_off
#print axioms defectOfElem_tinyMElem
#print axioms tinyU_isRegularHolonomy
#print axioms tinyU_not_isRegularHolonomy_of_lt
#print axioms tinyU_curvature_ne_one
#print axioms tinyU_not_gaugeTransform_of_flat
#print axioms sqrt_neg_trap
#print axioms strict_diff_forces_threshold
#print axioms strict_small_tinyU
#print axioms witL5_pos
#print axioms curvedBond_dir
#print axioms curvedU_curvature_ne_one
#print axioms curvedU_has_curved_plaquette
#print axioms curvedU_not_gaugeTransform_of_flat
#print axioms curvedU_isRegularHolonomy
#print axioms curvedU_not_isRegularHolonomy_of_lt
#print axioms curvedA_at_curvedBond
#print axioms curved_regularU_coercivity
#print axioms curved_regularU_coercivity_numeric
#print axioms exists_curved_regularU_coercivity
#print axioms flat_witness_satisfies_all_but_curvature
#print axioms curvedU_has_flat_plaquette
#print axioms curvedU_forall_curved_is_false
#print axioms witnessL_fails_hL
#print axioms witL5_satisfies_hL
#print axioms curvedU_ne_trivialU_by_curvature
#print axioms bondU_at
#print axioms bondU_off
#print axioms tinyU_eq_bondU
#print axioms singleBondU_eq_bondU
#print axioms frobSupBond_bondU
#print axioms curvedFamilyU_curvature_ne_one
#print axioms curvedFamilyU_isRegularHolonomy
#print axioms frobSupBond_curvedFamilyU_le
#print axioms frobSupBond_curvedFamilyU_sq_le
#print axioms four_sqrt2_frobSup_le
#print axioms curved_family_regularU_coercivity

end AdalyFormal.Balaban.RegularUCurvedWitness
