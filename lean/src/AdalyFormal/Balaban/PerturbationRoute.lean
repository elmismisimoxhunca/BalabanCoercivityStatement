/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CurvedTower

set_option autoImplicit false

/-!
# `PerturbationRoute.lean` — p.428's shape by FLAT BASE + a `k`-UNIFORM PERTURBATION BOUND

Lane record: `compute/perturbation_route/PROGRESS.md`.

## §0 — WHY THIS MODULE EXISTS

`compute/sectB_pages/` established what CMP99b's Sect. B actually does: it proves its `U ≠ 1`
statements by **base-minus-perturbation** — a base operator at a configuration, a perturbation whose
OPERATOR NORM is `O(α)`, and a resolvent series — and it NEVER runs a recursion on coercivity
constants. This module runs that architecture on this tree's own carriers.

The two halves:

* **the flat base** is already banked: `TowerMilestone.tower_uniform_coercive` gives
  `γ*‖u‖² ≤ ⟨u,Δ_j u⟩ + ⟨u,P_Ax u⟩` at EVERY level `j ≤ k` with `γ* = 1/22522555753408512`, no decay;
* **the perturbation bound** is what this module adds: a TWO-SIDED bound on the operator DIFFERENCE
  `Δ_k(U) − Δ_k(1)` with an absolute, extent-free constant.

## §1 — WHAT IS PROVED

1. **THE BRICK (§4-§5).** For every periodic extent, every background with `frobSupBond U ≤ α₀` and
   every `v` on the carrier,

       |⟨v, (Δ_k(U) − Δ_k(1)) v⟩|  ≤  320 · α₀ · ‖v‖² ,        `abs_inner_pertOp_le`

   with `320 = 272 + 48` counted from banked theorems and **no `α₀²` term**. Nothing in the statement
   or the proof mentions the extent, so the SAME constant is available at every level's lattice —
   that is where the `k`-uniformity comes from, and it comes exactly as the source's bookkeeping says
   it should (§3 on the units). No level-dependence appears; the brief asked for it to be pinned if
   it did, and the pin is that the constant is an absolute numeral proved at an arbitrary extent.

   ⚠ This is NOT `ComposedCoercivity.curlEnergy_le_curved`. That theorem is a ONE-SIDED domination
   with a factor `2` and a remainder `544α₀ + 64α₀²`; it does not bound the difference of the two
   forms and cannot transport a lower bound from `Δ_k(1)` to `Δ_k(U)`. The two-sided difference bound
   is new here, and its remainder is strictly sharper (`320α₀`, purely linear), because the factor-`2`
   Cauchy–Schwarz split is replaced by an `α₀`-weighted Young step at the parameter `2α₀`.

2. **THE COMPOSITION (§6), one inequality.** For every `Level Λ` — the invariant-carrying structure
   the flat tower is built from, so this covers BOTH the lattice operator and the tower's own RG
   images — every `α₀`-small background at `Λ`, and every `u` whose coarse datum lies in p.428's
   subspace at the next lattice,

       (γ* − 320α₀)·‖u‖² ≤ ⟨u, (Δ_Λ + pertOp U) u⟩ + ⟨u, P_Ax u⟩ .  `perturbed_gf_on_preimage`

3. **THE `k`-UNIFORM HEADLINES (§7a).** At every level `j ≤ k`, with ONE constant free of `j` and `k`:
   * `lattice_uniform_perturbed_coercive` — the level-`j` LATTICE operator `Δ_k(U_j)` at the level-`j`
     background. The source-shaped reading; `coercive_on_VSrc_perturbed` (§8a) states its `j = 0` case
     in `VRestrictedRoute`'s own vocabulary.
   * `tower_uniform_perturbed_coercive` — the flat tower's own level-`j` operator (`TowerMilestone.
     towerAt`, the `j`-fold RG image) dressed by that level's curvature correction.
   * `class_uniform_coercive` — the same quantified over `LevelClass`, i.e. over (3.35).
   `dressed_dominates_lattice` (§7) proves the second's form dominates the first's, so the lattice
   reading is the STRONGER of the two; they are not independent claims.

4. **THE CLASS (§3) AND `γ₀` (§8).** `LevelClass` is a MODELING PROXY for (3.35) in level units
   — NOT a transcription (Sol correction, 2026-08-02; the printed (3.35) is about ONE fine
   configuration, with a PER-CUBE gauge existential, and carries a DERIVATIVE bound; `LevelClass`
   is arbitrary per-level data with a global identity-gauge frobSupBond bound only, plus the
   units step marked as OURS — four structural replacements, all now enumerated). `gammaZero α₀ = γ* − 320α₀`; `gammaZero_at_zero` shows it recovers `γ*`
   EXACTLY in the flat limit (no residue); `gammaZero_exact_at_1e_neg_20` is the exact rational;
   `gammaZero_pos_at_1e_neg_20` / `gammaZero_nonpos_at_1e_neg_18` bracket the threshold on both sides.

5. **NON-VACUITY (§9), PER HEADLINE THEOREM, AT `j = 0` AND AT `j = 1`.** A genuinely curved
   background (plaquette holonomy `≠ 1`, kernel-checked) inside the class at every level of a real
   extent tower (`TowerMilestone.witL`, sides `16 → 8 → 4`), a nonzero `u` whose coarse datum is a
   NONZERO element of the subspace (so the witness is not drawn from `ker Q`, where the hypothesis is
   free), and both sides of each theorem's OWN conclusion strictly positive. The tower reading gets
   its own witness (§9a) rather than inheriting the lattice reading's.

6. **CONTROLS (§10).** The smallness hypothesis is load-bearing: `pert_bound_needs_hypothesis` makes
   the brick FAIL when the hypothesis is dropped, at `Δ_k`'s own kernel-checked value `−4`; and
   `central_witness_outside_class` shows the class excludes that witness for every `α₀ < 2`.

## §2 — THE TWO DELTAS THE BRIEF NAMED, AND WHAT HAPPENED TO THEM (§11)

Neither is left at a name.

* **DELTA 1, the denotation bridge (§11a).** It splits. The INTERNAL half — is the tower's level-`j`
  operator the level-`j` lattice's own `Δ_k(1)`? — is **REFUTED**: `denotation_bridge_false`. It holds
  at `j = 0` (`denotation_bridge_at_zero`) and FAILS at `j = 1`, because the RG image dominates
  `2·curlEnergy` (`next_ge_two_curl` — the factor `2` that `TowerMilestone.stepLevel` discards) while
  the lattice operator's form IS `curlEnergy`, and the level-`1` lattice carries a field of strictly
  positive curl energy. So the two readings of §7a are genuinely two, and §7's domination is the only
  relation between them that holds. The EXTERNAL half — is either family the `Δ_k` of CMP99b p.428? —
  is not formalisable at all: `Δ_k` occurs on NO other page of that paper (measured,
  `compute/sectB_pages/`), so there is no second display to check a candidate against. It is stated
  as prose, not as a `Prop`, because a `Prop` about a Lean object could only ever be a stipulation.

* **DELTA 2, cross-level class propagation (§11b).** The obvious statement of it is **CONVICTED HERE
  AS CONTENT-FREE**: `weakClassPropagation_trivially_true` proves it for every lattice and every
  depth, by flattening the family above level `0` — the S91 failure mode (an existential over free
  data) committed inside a disclosure. The corrected statement `ClassPropagation` carries the
  blocking family as DATA, and it is bracketed on both sides: it HOLDS for a flattening map
  (`classPropagation_holds_for_flattening`) and FAILS for a map that leaves the class
  (`classPropagation_fails_for_expanding`), so it constrains the dynamics rather than nothing.
  Which side Bałaban's actual blocking falls on is CMP99a (1.66)'s territory and the CONSUMER's
  burden, not this lemma's: p.428 quantifies over `U` IN THE CLASS, and (3.35) is one condition on
  one configuration imposing a bound at every index in that index's own units. ⚠ It is not a
  formality either: `BlockedBackground`'s `ubarSU2_constU` chain shows the SU(2) blocking is the
  `ell`-th power map on constants and EXPANDS `frobSupBond` there. That module is not imported here
  and nothing in this file asserts anything about its map.

**RELATION TO THE OLD ROUTE.** `RescaledTower.lean` and `CurlFreeSection.lean` stand untouched as
theorems about the `(γ−δ)/q²` RECURSION route, and `CurvedTower` §10a's `stepRho_ge_exact` (the
`ρ`-growth by `≥ 6791626784` per level) remains correct and is exactly why THAT route is not
`k`-uniform. Nothing here contradicts them, because nothing here propagates a level's parameters into
the next level: the uniformity here is uniformity over the family of level lattices with one
extent-free constant, obtained by re-deriving at each level, NOT by a recursion that converges. What
this route does NOT do is compose the levels — that is DELTA 2, and it is disclosed above, not used.

## §2a — THREE MORE THINGS THIS MODULE IS NOT, STATED BEFORE A READER HAS TO FIND THEM

1. **THE DRESSED TOWER OPERATOR IS NOT `CurvedTower.curvedStepLevel`'s CURVED RG IMAGE.**
   `tower_uniform_perturbed_coercive`'s operator is `towerAt_j.op + pertOp U_j`: the FLAT RG image
   dressed by the level's own correction. The genuine curved RG image — block-invert the CURVED
   operator, then take `S − a·I` — is `CurvedTower.curvedStepLevel`, and NO theorem here proves the
   two equal. They are not obviously equal and this file does not assume they are; the dressed
   operator is a definite operator, the statement about it is a theorem about that operator, and the
   identification is not claimed. (`denotation_bridge_false` shows how badly the analogous
   identification fails one level down, which is the reason this disclosure is here.) The LATTICE
   reading (`lattice_uniform_perturbed_coercive`, `class_uniform_coercive`) is free of this question
   entirely: its operator is `Δ_k(U_j)` at the level-`j` lattice and nothing else.

2. ~~**THE SUBSPACE CLAUSE IS THE FLAT `Q`, NOT THE COVARIANT `Q₁(Ū)`.** … So the two doors are
   restricted to DIFFERENT subspaces, and neither result contains the other. Closing this would mean
   re-running the flat half at the covariant clause; it is not done here and is not assumed.~~
   **SUPERSEDED IN THE SAME PASS (S75) — §12 CLOSES IT.** The headlines of §7a do use
   `TowerMilestone.VLat`, whose clause (c3) is the FLAT `lineCoarseRestrictCov (trivialU Λ) 2 A = 0`,
   and `CurvedTower.VCurved` argues the source's `Q₁` is the covariant block average at the coarse
   background. §12 therefore states the SAME perturbation result at the COVARIANT clause
   (`covariant_perturbed_gf_on_preimage`, `covariant_uniform_perturbed_coercive`), by composing the
   brick with `CurvedTower.curved_gf_on_preimage` at `(c,ρ,σ) = (1,0,0)` rather than rebuilding
   anything (LAW-19), with its own witness (`covariant_uniform_nonvacuous`). What remains true is
   only that the two clauses cut out different subspaces; BOTH now carry the perturbation result with
   a `j`- and `k`-free constant.

3. **THE CONSTANTS ARE INHERITED, NOT IMPROVED.** `γ* = 1/22522555753408512 ≈ 4.4·10⁻¹⁷` is
   `VRestrictedRoute`'s, and the admissible radius `α₀ < γ*/320 ≈ 1.4·10⁻¹⁹` is a consequence of it.
   This module makes the `α₀`-dependence linear and exact; it does not enlarge `γ*`.

**STANDING SCOPE, unchanged:** `J = 0`, `ell = 2`, `𝔰𝔲(2)`, periodic torus, `Q` the flat averaging,
and (3.120)'s correction `Δ′_π` NOT present — the operators here are `Δ_k`, not `Δ_π`
(`CurvedTower`'s taxed door is the one that carries `δ`).
-/

namespace AdalyFormal.Balaban.PerturbationRoute

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLatticePlaquette PeriodicLinkConfiguration)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.BridgeInverse (qCLM)
open AdalyFormal.Balaban.U1AnchorCoarse (coarseExtent)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm)
open AdalyFormal.Balaban.FibreCoercivity (curlEnergy curlEnergy_nonneg
  deltaK_trivialU_eq_curlEnergy)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg frobSupBond
  curlDrift)
open AdalyFormal.Balaban.AxialCoercivity (pAx pAxCLM pAxCLM_pos inner_pAxCLM_eq')
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized inner_deltaKCLMNormalized_eq
  deltaKCLMNormalized_symm)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.OnRangeCoercivity (norm_sq_eq_bondEnergy inner_deltaK_flat)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlValueCovariant_trivialU_local)
open AdalyFormal.Balaban.ComposedCoercivity (sum_curlDrift_sq_le)
open AdalyFormal.Balaban.LemmaAssembly (dstarDQuadForm_eq_sum_norm_sq)
open AdalyFormal.Balaban.DeltaPrimeBound (dstarDQuadForm_le_bondEnergy
  abs_deltaPrimeQuadFormNormalizedTransported_le_bondEnergy)
open AdalyFormal.Balaban.AlphaAnalyticity (gaugeRegular_of_frobSupBond_le)
open AdalyFormal.Balaban.RegularUDomainWitness (frobSupBond_trivialU)
open AdalyFormal.Balaban.FibreCoercivity (zeroSite)
open AdalyFormal.Balaban.RegularUCurvedWitness (bondU bondU_at bondU_off
  holonomy_singleBond_base_plaquette)
open AdalyFormal.Balaban.NonFlatBackground (rotElem rotElem_ne_one)
open AdalyFormal.Balaban.CurvedTower (frobSupBond_bondRot_le sqrt_two_le_two VCurved CurvedLevel
  curved_gf_on_preimage gammaLevel vWitFine_mem_VCurved bondRot_fix_rotGen)
open AdalyFormal.Balaban.CovariantFibreTransfer (gammaCurved gammaCurved_pos_iff)
open AdalyFormal.Balaban.TowerOneStep (Rung piOp)
open AdalyFormal.Balaban.TowerMilestone (levelRung rung_inner_next_lift towerAt_law
  hcurl_is_load_bearing witL_extents)
open AdalyFormal.Balaban.VRestrictedRoute (pullS coarseCurlEnergy curlEnergy_pullS
  coarseCurlEnergy_Q_le)
open AdalyFormal.Balaban.BridgeRestricted (rotGen rotGen_ne_zero)
open AdalyFormal.Balaban.VRestrictedRoute (gammaV gammaV_pos two_dvd_of_four coarse_two_dvd)
open AdalyFormal.Balaban.TowerMilestone (VLat qLevel Level baseLevel levelExtent levelOK_of_pow
  levelExtent_even levelExtent_four towerAt gammaStar gammaStar_pos gammaStar_eq
  level_gf_on_preimage witL witL_pow)

variable {L Λ : PeriodicLatticeExtent}

/-! ## §3 — THE `(3.35)`-CLASS, IN LEVEL UNITS

`corpus/pages/CMP99b_p396.md#eq-3-35` (400 dpi render `corpus/renders/CMP99b_p396-08.png`,
`render_sha256: d0f0d665232fc871e005f2e721ea338e96c1a52763e151c3966bf7fcb47568ec`,
`verification_status: adjudicated`) prints, for a cube `□` of index `j`:

```
|A| < O(1) M α₀ (L^j η)^{-1},   |∇^η A| < O(1) M α₀ (L^j η)^{-2}   on □,
where O(1)M is a size of □ in T_{L^{-j}};                                    (3.35)
```

Three features of that display are what this module's uniformity rests on, and all three are
literal, not interpretation:

1. it is a condition on **one** configuration `U` on the fine torus;
2. it is imposed at **every** index `j = 0,…,k` simultaneously;
3. the number `α₀` is **the same at every index** — the whole `j`-dependence sits in the units
   factor `(L^jη)^{-1}`.

**THE UNITS BRIDGE, STATED AS OURS.** This tree's smallness parameter is the dimensionless holonomy
radius `frobSupBond U = sup_b ‖U(b) − 1‖_F`. With a link `U(b) = exp(i a A(b))` at lattice spacing
`a`, `‖U(b) − 1‖_F ≈ √2 · a · |A|`. At the level-`j` lattice the spacing IS `a = L^jη`, so (3.35)
reads `‖U_j(b) − 1‖_F ≲ √2 · O(1)M α₀` — **a `j`-independent number**. (On the FINE lattice the same
display gives `√2 O(1)M α₀ L^{-j}`, which IMPROVES with `j`; the level's own units are the ones in
which the class is `j`-uniform, and they are the ones (3.35) is written in.) The step from `|A|` to
`‖U − 1‖_F` is OUR reading of the exponential map's first order and is recorded here as such; it is
not a display of the source.

`LevelClass` below is that reading as a MODELING PROXY (not a transcription — Sol correction,
2026-08-02): one background per level, each with the same radius at its own lattice; the printed
condition's one-configuration structure, per-cube gauge existential, and derivative clause are
NOT modeled. -/

/-- **(3.35) IN LEVEL UNITS.** A family of backgrounds, one on each level lattice, all with the same
holonomy radius `α₀` — the level-`j` member measured at the level-`j` lattice, i.e. in that level's
own units. Who chooses what: `α₀` is chosen by the statement that consumes this; the family `U` is
universally quantified; `j` and `k` are universal. -/
def LevelClass (L : PeriodicLatticeExtent) (k : ℕ) (alpha0 : ℝ)
    (U : ∀ j : ℕ, PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (levelExtent L j)) : Prop :=
  ∀ j : ℕ, j ≤ k → frobSupBond (U j) ≤ alpha0

/-- The flat family is in the class at every radius `≥ 0`: the class is not empty for a trivial
reason. §7 supplies a GENUINELY CURVED member, which is the witness that matters. -/
theorem levelClass_trivial (L : PeriodicLatticeExtent) (k : ℕ) {alpha0 : ℝ} (h : 0 ≤ alpha0) :
    LevelClass L k alpha0 (fun j => trivialU (levelExtent L j)) := by
  intro j _
  rw [frobSupBond_trivialU]; exact h

/-! ## §4 — THE BRICK: a TWO-SIDED bound on the operator difference `Δ_k(U) − Δ_k(1)`

The chain, with every constant traced to a banked theorem:

* `Σ_p ‖D_1A(p)‖² = curlEnergy A ≤ 16·bondEnergy A` and `Σ_p ‖D_UA(p)‖² = dstarDQuadForm U A ≤
  16·bondEnergy A` — `DeltaPrimeBound.dstarDQuadForm_le_bondEnergy`, at `U = 1` and at `U`;
* `Σ_p ‖(D_U − D_1)A(p)‖² ≤ 32·α²·bondEnergy A` — `ComposedCoercivity.sum_curlDrift_sq_le`;
* per plaquette `|‖x‖² − ‖y‖²| ≤ ‖x−y‖(‖x‖+‖y‖)`, then Young at the parameter `2α`:
  `2α·‖d‖(a+b) ≤ ‖d‖² + 2α²(a²+b²)`, which sums to `2α·S ≤ 32α²E + 2α²·32E = 96α²E`, i.e.
  `S ≤ 48αE`. **`48 = 16 + 32`**: `16 = 32/2` is half the drift constant, `32 = 16 + 16` is the two
  energy dominations. No `α²` survives.
* `|Δ′| ≤ 272α·bondEnergy A` — `DeltaPrimeBound.abs_deltaPrimeQuadFormNormalizedTransported_le_bondEnergy`.

`320 = 272 + 48`. Every one of `272`, `32`, `16`, `16` is quoted from a theorem in the import
closure; none is fitted.

**`320` IS NOT OPTIMAL — disclosed per the second-family gate (2026-08-01), not tightened.** The
Young parameter `2α₀` is the clean choice, not the minimizing one: at `s = √2·α₀` the same chain
gives `272 + 32√2 ≈ 317.255`, and the gate kernel-verified the theorem at the integer constant
`318` (its own fresh proof term) while kernel-refuting `317` in the same arrangement — so `318`
is this chain's exact integer optimum, and anything lower would need a sharper `272` or a
drift–energy correlation argument. `320` is retained for the transparent `2α₀` parameter and the
exact-rational corollaries that pin it; every consumer takes the constant as a hypothesis-side
number, so the looseness is safe. No claim of sharpness is made anywhere in this file. -/

/-- The flat curl energy IS the covariant one at `U = 1`. -/
theorem dstarDQuadForm_trivialU_eq_curlEnergy (A : Bond L → SuTwo) :
    dstarDQuadForm (trivialU L) A = curlEnergy A := by
  rw [dstarDQuadForm_eq_sum_norm_sq]
  show ∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant (trivialU L) A p‖ ^ 2
      = ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2
  exact Finset.sum_congr rfl (fun p _ => by rw [curlValueCovariant_trivialU_local])

/-- `curlEnergy A ≤ 16·bondEnergy A` — `dstarDQuadForm_le_bondEnergy` read at `U = 1`. -/
theorem curlEnergy_le_bondEnergy (A : Bond L → SuTwo) : curlEnergy A ≤ 16 * bondEnergy A := by
  have h := dstarDQuadForm_le_bondEnergy (trivialU L) A
  rwa [dstarDQuadForm_trivialU_eq_curlEnergy] at h

/-- The drift at a plaquette is exactly the difference of the two curl values. -/
theorem curlDrift_eq_sub
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    curlDrift U A p = curlValueCovariant U A p - flatCurlValue A p := by
  show (curlValueCovariant U A - curlValueCovariant (trivialU L) A) p = _
  rw [Pi.sub_apply, curlValueCovariant_trivialU_local]

/-- The per-plaquette two-sided step: `|‖x‖² − ‖y‖²| ≤ ‖x−y‖(‖x‖+‖y‖)`. -/
theorem abs_sq_sub_sq_le_drift
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    |‖curlValueCovariant U A p‖ ^ 2 - ‖flatCurlValue A p‖ ^ 2|
      ≤ ‖curlDrift U A p‖ * (‖curlValueCovariant U A p‖ + ‖flatCurlValue A p‖) := by
  have hsub : ‖curlValueCovariant U A p - flatCurlValue A p‖ = ‖curlDrift U A p‖ := by
    rw [curlDrift_eq_sub]
  have h1 : |‖curlValueCovariant U A p‖ - ‖flatCurlValue A p‖| ≤ ‖curlDrift U A p‖ := by
    rw [← hsub]; exact abs_norm_sub_norm_le _ _
  have hfac : ‖curlValueCovariant U A p‖ ^ 2 - ‖flatCurlValue A p‖ ^ 2
      = (‖curlValueCovariant U A p‖ - ‖flatCurlValue A p‖)
        * (‖curlValueCovariant U A p‖ + ‖flatCurlValue A p‖) := by ring
  rw [hfac, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖curlValueCovariant U A p‖ + ‖flatCurlValue A p‖)]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- **THE COVARIANT-VS-FLAT CURL ENERGY DIFFERENCE, TWO-SIDED AND LINEAR IN `α`.**
`|dstarDQuadForm U A − curlEnergy A| ≤ 48·α·bondEnergy A`. -/
theorem abs_dstarD_sub_curlEnergy_le {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0) (A : Bond L → SuTwo) :
    |dstarDQuadForm U A - curlEnergy A| ≤ 48 * alpha0 * bondEnergy A := by
  classical
  set E : ℝ := bondEnergy A with hE
  have hE0 : 0 ≤ E := bondEnergy_nonneg A
  have hX : dstarDQuadForm U A
      = ∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant U A p‖ ^ 2 :=
    dstarDQuadForm_eq_sum_norm_sq U A
  have hY : curlEnergy A = ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2 := rfl
  have hdrift := sum_curlDrift_sq_le halpha U hsup A
  have hXle : dstarDQuadForm U A ≤ 16 * E := dstarDQuadForm_le_bondEnergy U A
  have hYle : curlEnergy A ≤ 16 * E := curlEnergy_le_bondEnergy A
  -- the summed two-sided step
  have hS : |dstarDQuadForm U A - curlEnergy A|
      ≤ ∑ p : PeriodicLatticePlaquette L,
          ‖curlDrift U A p‖ * (‖curlValueCovariant U A p‖ + ‖flatCurlValue A p‖) := by
    rw [hX, hY, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun p _ => abs_sq_sub_sq_le_drift U A p)
  rcases lt_or_eq_of_le halpha with hpos | hzero
  · -- `α > 0`: Young at the parameter `2α`
    have hyoung : ∀ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette L)),
        ‖curlDrift U A p‖ * (‖curlValueCovariant U A p‖ + ‖flatCurlValue A p‖)
          ≤ 1 / (2 * alpha0) * ‖curlDrift U A p‖ ^ 2
            + alpha0 * (‖curlValueCovariant U A p‖ ^ 2 + ‖flatCurlValue A p‖ ^ 2) := by
      intro p _
      set d := ‖curlDrift U A p‖ with hd
      set a := ‖curlValueCovariant U A p‖ with ha
      set b := ‖flatCurlValue A p‖ with hb
      have hd0 : 0 ≤ d := norm_nonneg _
      have ha0 : 0 ≤ a := norm_nonneg _
      have hb0 : 0 ≤ b := norm_nonneg _
      have h2a : (0 : ℝ) < 2 * alpha0 := by linarith
      have hkey : 0 ≤ d ^ 2 + 2 * alpha0 ^ 2 * (a ^ 2 + b ^ 2) - 2 * alpha0 * (d * (a + b)) := by
        nlinarith [sq_nonneg (d - 2 * alpha0 * a), sq_nonneg (d - 2 * alpha0 * b)]
      rw [← sub_nonneg]
      have heq : 1 / (2 * alpha0) * d ^ 2 + alpha0 * (a ^ 2 + b ^ 2) - d * (a + b)
          = (d ^ 2 + 2 * alpha0 ^ 2 * (a ^ 2 + b ^ 2) - 2 * alpha0 * (d * (a + b)))
            / (2 * alpha0) := by
        field_simp
      rw [heq]
      exact div_nonneg hkey (le_of_lt h2a)
    have hsum : ∑ p : PeriodicLatticePlaquette L,
        ‖curlDrift U A p‖ * (‖curlValueCovariant U A p‖ + ‖flatCurlValue A p‖)
        ≤ 1 / (2 * alpha0) * (∑ p : PeriodicLatticePlaquette L, ‖curlDrift U A p‖ ^ 2)
          + alpha0 * ((∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant U A p‖ ^ 2)
            + ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2) := by
      refine le_trans (Finset.sum_le_sum hyoung) (le_of_eq ?_)
      have e1 : ∑ p : PeriodicLatticePlaquette L,
            (1 / (2 * alpha0) * ‖curlDrift U A p‖ ^ 2
              + alpha0 * (‖curlValueCovariant U A p‖ ^ 2 + ‖flatCurlValue A p‖ ^ 2))
          = (∑ p : PeriodicLatticePlaquette L, 1 / (2 * alpha0) * ‖curlDrift U A p‖ ^ 2)
            + ∑ p : PeriodicLatticePlaquette L,
                alpha0 * (‖curlValueCovariant U A p‖ ^ 2 + ‖flatCurlValue A p‖ ^ 2) :=
        Finset.sum_add_distrib
      have e2 : (∑ p : PeriodicLatticePlaquette L,
            alpha0 * (‖curlValueCovariant U A p‖ ^ 2 + ‖flatCurlValue A p‖ ^ 2))
          = alpha0 * ((∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant U A p‖ ^ 2)
            + ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      have e3 : (∑ p : PeriodicLatticePlaquette L, 1 / (2 * alpha0) * ‖curlDrift U A p‖ ^ 2)
          = 1 / (2 * alpha0) * ∑ p : PeriodicLatticePlaquette L, ‖curlDrift U A p‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      rw [e1, e2, e3]
    have h2a : (0 : ℝ) < 2 * alpha0 := by linarith
    have hinv : (0 : ℝ) < 1 / (2 * alpha0) := by positivity
    have hfin : 1 / (2 * alpha0) * (∑ p : PeriodicLatticePlaquette L, ‖curlDrift U A p‖ ^ 2)
          + alpha0 * ((∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant U A p‖ ^ 2)
            + ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2)
        ≤ 48 * alpha0 * E := by
      have h1 : 1 / (2 * alpha0) * (∑ p : PeriodicLatticePlaquette L, ‖curlDrift U A p‖ ^ 2)
          ≤ 1 / (2 * alpha0) * (32 * alpha0 ^ 2 * E) :=
        mul_le_mul_of_nonneg_left hdrift (le_of_lt hinv)
      have h1' : 1 / (2 * alpha0) * (32 * alpha0 ^ 2 * E) = 16 * alpha0 * E := by
        field_simp; ring
      have h2 : (∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant U A p‖ ^ 2)
            + ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2 ≤ 32 * E := by
        rw [← hX, ← hY]; linarith
      have h3 : alpha0 * ((∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant U A p‖ ^ 2)
            + ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue A p‖ ^ 2)
          ≤ alpha0 * (32 * E) := mul_le_mul_of_nonneg_left h2 halpha
      rw [h1'] at h1
      linarith
    linarith [hS, hsum, hfin]
  · -- `α = 0`: the drift vanishes identically, so the two sums are equal
    have hz : (0 : ℝ) = alpha0 := hzero
    have hd0 : ∑ p : PeriodicLatticePlaquette L, ‖curlDrift U A p‖ ^ 2 ≤ 0 := by
      have := hdrift; rw [← hz] at this; simpa using this
    have hzero' : ∀ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette L)),
        ‖curlDrift U A p‖ ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => sq_nonneg _)).1 ?_
      exact le_antisymm hd0 (Finset.sum_nonneg (fun p _ => sq_nonneg _))
    have hterm : ∀ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette L)),
        ‖curlDrift U A p‖ * (‖curlValueCovariant U A p‖ + ‖flatCurlValue A p‖) = 0 := by
      intro p hp
      have h := hzero' p hp
      have : ‖curlDrift U A p‖ = 0 := by nlinarith [norm_nonneg (curlDrift U A p)]
      rw [this, zero_mul]
    have hSum0 : ∑ p : PeriodicLatticePlaquette L,
        ‖curlDrift U A p‖ * (‖curlValueCovariant U A p‖ + ‖flatCurlValue A p‖) = 0 :=
      Finset.sum_eq_zero hterm
    rw [hSum0] at hS
    rw [← hz]
    simpa using hS

/-- **THE PERTURBATION CONSTANT.** `320 = 272 + 48`, both summands quoted from banked theorems and
composed in §4's header. Named so that no consumer carries a bare literal. -/
noncomputable def pertConst : ℝ := 320

theorem pertConst_pos : 0 < pertConst := by unfold pertConst; norm_num

/-- **THE BRICK, IN QUADRATIC-FORM SHAPE.**
`|Δ_k(U)(A) − curlEnergy A| ≤ 320·α·bondEnergy A` — a TWO-SIDED bound on the DIFFERENCE, linear in
`α`, with no extent anywhere in the statement or the proof. -/
theorem abs_deltaK_sub_curlEnergy_le {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0) (A : Bond L → SuTwo) :
    |deltaKQuadFormNormalizedCorrected U A - curlEnergy A|
      ≤ pertConst * alpha0 * bondEnergy A := by
  have hd := abs_dstarD_sub_curlEnergy_le halpha U hsup A
  have hp := abs_deltaPrimeQuadFormNormalizedTransported_le_bondEnergy halpha U
    (gaugeRegular_of_frobSupBond_le hsup) A
  have hid : deltaKQuadFormNormalizedCorrected U A
      = dstarDQuadForm U A
        + AdalyFormal.Balaban.NormalizationAudit.deltaPrimeQuadFormNormalizedTransported U A := rfl
  have h1 := abs_le.mp hd
  have h2 := abs_le.mp hp
  rw [hid, abs_le]
  unfold pertConst
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## §5 — THE PERTURBATION AS AN OPERATOR

`pertOp U` is a DEFINITE operator determined by `U` — the difference of the tree's own `Δ_k` at `U`
and at `1`. It is not free data, and §8's control shows the bound on it is false without the
smallness hypothesis. -/

/-- **THE LEVEL'S CURVATURE CORRECTION.** `Δ_k(U) − Δ_k(1)`, at the lattice `U` lives on. -/
noncomputable def pertOp (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  deltaKCLMNormalized U - deltaKCLMNormalized (trivialU L)

@[simp] theorem pertOp_trivialU : pertOp (trivialU L) = 0 := by
  unfold pertOp; exact sub_self _

/-- `Δ_k(1) + pertOp U = Δ_k(U)` — an EXACT ALGEBRAIC operator identity, NOT definitional (Sol
third-family correction, 2026-08-02: `rfl` fails on this type, kernel-checked by Sol's mutant;
the proof is `abel`, additive-group cancellation after unfolding. Two prior gates and the root
banner had called it "definitional"; the identity is on the nose as an EQUATION, not by
reduction). -/
theorem baseLevel_add_pertOp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (baseLevel L).op + pertOp U = deltaKCLMNormalized U := by
  show deltaKCLMNormalized (trivialU L)
      + (deltaKCLMNormalized U - deltaKCLMNormalized (trivialU L)) = _
  abel

theorem pertOp_symm (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (u v : BondFnL2 L) :
    (inner ℝ u (pertOp U v) : ℝ) = (inner ℝ (pertOp U u) v : ℝ) := by
  have h1 : (inner ℝ u (pertOp U v) : ℝ)
      = (inner ℝ u (deltaKCLMNormalized U v) : ℝ)
        - (inner ℝ u (deltaKCLMNormalized (trivialU L) v) : ℝ) := by
    show (inner ℝ u (deltaKCLMNormalized U v - deltaKCLMNormalized (trivialU L) v) : ℝ) = _
    rw [inner_sub_right]
  have h2 : (inner ℝ (pertOp U u) v : ℝ)
      = (inner ℝ (deltaKCLMNormalized U u) v : ℝ)
        - (inner ℝ (deltaKCLMNormalized (trivialU L) u) v : ℝ) := by
    show (inner ℝ (deltaKCLMNormalized U u - deltaKCLMNormalized (trivialU L) u) v : ℝ) = _
    rw [inner_sub_left]
  rw [h1, h2, deltaKCLMNormalized_symm U u v, deltaKCLMNormalized_symm (trivialU L) u v]

/-- **THE `k`-UNIFORM PERTURBATION BOUND.** `|⟨v, (Δ_k(U) − Δ_k(1)) v⟩| ≤ 320·α·‖v‖²` for every `v`
on the carrier at every periodic extent. The extent appears nowhere; this is the same theorem at
every level's lattice, which is exactly the source's bookkeeping in level units (§3). -/
theorem abs_inner_pertOp_le {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0) (v : BondFnL2 L) :
    |(inner ℝ v (pertOp U v) : ℝ)| ≤ pertConst * alpha0 * ‖v‖ ^ 2 := by
  obtain ⟨A, rfl⟩ : ∃ A : Bond L → SuTwo, v = WithLp.toLp 2 A := ⟨WithLp.ofLp v, rfl⟩
  have hsplit : (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
        (pertOp U (WithLp.toLp 2 A)) : ℝ)
      = deltaKQuadFormNormalizedCorrected U A - curlEnergy A := by
    show (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
      ((deltaKCLMNormalized U - deltaKCLMNormalized (trivialU L)) (WithLp.toLp 2 A)) : ℝ) = _
    rw [show ((deltaKCLMNormalized U - deltaKCLMNormalized (trivialU L))
          (WithLp.toLp 2 A) : BondFnL2 L)
        = deltaKCLMNormalized U (WithLp.toLp 2 A)
          - deltaKCLMNormalized (trivialU L) (WithLp.toLp 2 A) from rfl,
      inner_sub_right, inner_deltaKCLMNormalized_eq, inner_deltaKCLMNormalized_eq,
      deltaK_trivialU_eq_curlEnergy]
  rw [hsplit, norm_sq_eq_bondEnergy]
  exact abs_deltaK_sub_curlEnergy_le halpha U hsup A

/-! ## §6 — THE COMPOSITION: ONE INEQUALITY

`TowerMilestone.level_gf_on_preimage` is the flat door at an ARBITRARY `Level Λ`: it consumes only
the level's own invariant `hcurl`, and its constant `γ_V = γ*` is `L`-free. Adding §5's bound to it
is a single `linarith`, and it is the whole of the perturbation route's composition step. -/

/-- `⟨v, pertOp U v⟩ = ⟨v, Δ_k(U) v⟩ − ⟨v, Δ_k(1) v⟩`. -/
theorem inner_pertOp_eq (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (v : BondFnL2 L) :
    (inner ℝ v (pertOp U v) : ℝ)
      = (inner ℝ v (deltaKCLMNormalized U v) : ℝ)
        - (inner ℝ v (deltaKCLMNormalized (trivialU L) v) : ℝ) := by
  show (inner ℝ v (deltaKCLMNormalized U v - deltaKCLMNormalized (trivialU L) v) : ℝ) = _
  rw [inner_sub_right]

/-- `⟨v, (Δ + pertOp U) v⟩ = ⟨v, Δ v⟩ + ⟨v, pertOp U v⟩`. -/
theorem inner_add_pertOp (D : BondFnL2 L →L[ℝ] BondFnL2 L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (v : BondFnL2 L) :
    (inner ℝ v ((D + pertOp U) v) : ℝ)
      = (inner ℝ v (D v) : ℝ) + (inner ℝ v (pertOp U v) : ℝ) := by
  show (inner ℝ v (D v + pertOp U v) : ℝ) = _
  rw [inner_add_right]

/-- **THE PERTURBED DOOR, AT AN ARBITRARY LEVEL.** `γ₀ = γ* − 320α` with `γ*` the flat tower's own
constant. Every constant is `L`-free and level-free; the ONLY inputs are the level's invariant and
§5's operator bound. -/
theorem perturbed_gf_on_preimage (lvl : Level Λ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hsup : frobSupBond U ≤ alpha0) (u : BondFnL2 Λ)
    (hu : VLat (coarseExtent Λ 2) (WithLp.ofLp (qLevel hdvd u))) :
    (gammaStar - pertConst * alpha0) * ‖u‖ ^ 2
      ≤ (inner ℝ u ((lvl.op + pertOp U) u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := by
  have hflat := level_gf_on_preimage lvl hdvd hdvd' u hu
  have hg : gammaStar = gammaV := rfl
  have hpert := abs_le.mp (abs_inner_pertOp_le halpha U hsup u)
  rw [inner_add_pertOp, hg]
  linarith [hflat, hpert.1]

/-- **THE PERTURBED DOOR AT THE LATTICE OPERATOR.** `Δ_k(1) + pertOp U` IS `Δ_k(U)`
(`baseLevel_add_pertOp`), so the same inequality is a statement about the lattice's own curved
operator with nothing added or removed. -/
theorem lattice_perturbed_gf_on_preimage (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hsup : frobSupBond U ≤ alpha0) (u : BondFnL2 Λ)
    (hu : VLat (coarseExtent Λ 2) (WithLp.ofLp (qLevel hdvd u))) :
    (gammaStar - pertConst * alpha0) * ‖u‖ ^ 2
      ≤ (inner ℝ u (deltaKCLMNormalized U u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := by
  rw [← baseLevel_add_pertOp U]
  exact perturbed_gf_on_preimage (baseLevel Λ) hdvd hdvd' halpha U hsup u hu

/-! ## §7 — THE TWO READINGS, AND WHICH IS STRONGER

`Level.op_dominates_flat` is one line from the invariant, and it is the only relation between the
tower's RG-image operators and the level lattices' own operators that this tree can prove. It is an
INEQUALITY, not an identification: nothing here says the RG image IS the lattice operator, and §11's
`DenotationBridge` is exactly the missing identification, left open. -/

/-- **EVERY LEVEL'S OPERATOR DOMINATES ITS LATTICE'S FLAT OPERATOR.** Immediate from the invariant
`hcurl` together with `inner_deltaK_flat`; stated because it is what orders the two readings. -/
theorem Level.op_dominates_flat (lvl : Level Λ) (v : BondFnL2 Λ) :
    (inner ℝ v (deltaKCLMNormalized (trivialU Λ) v) : ℝ) ≤ (inner ℝ v (lvl.op v) : ℝ) := by
  rw [inner_deltaK_flat]
  exact lvl.hcurl v

/-- **THE DRESSED TOWER OPERATOR DOMINATES THE CURVED LATTICE OPERATOR.** So the lattice reading is
the STRONGER statement and the tower reading follows from it; they are not two independent claims. -/
theorem dressed_dominates_lattice (lvl : Level Λ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ) (v : BondFnL2 Λ) :
    (inner ℝ v (deltaKCLMNormalized U v) : ℝ) ≤ (inner ℝ v ((lvl.op + pertOp U) v) : ℝ) := by
  rw [inner_add_pertOp, inner_pertOp_eq]
  linarith [Level.op_dominates_flat lvl v]

/-! ### §7a — THE `k`-UNIFORM HEADLINES

The level index enters ONLY through the lattice `levelExtent L j`. Every constant above is an
absolute numeral proved at an arbitrary periodic extent, so the SAME `γ₀` is delivered at every
`j ≤ k` — that is the whole content of the uniformity, and it is stated here rather than inferred.

⚠ **WHAT THE UNIFORMITY IS AND IS NOT.** It is uniformity over the family of level lattices with one
constant. It is NOT a statement about composing the levels: no theorem here transports a level's
data into the next level. The composition question is §11's two named Props. -/

/-- Every level at or below `k` has a positive extent in every direction (from `4 ∣ side`). -/
theorem levelExtent_pos {k : ℕ} (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) {j : ℕ}
    (hj : j ≤ k) (μ : Fin 3) : 0 < levelExtent L j μ := by
  obtain ⟨c, hc⟩ := levelExtent_four hpow hj μ
  omega

/-- Every level STRICTLY ABOVE an admissible one still has a positive extent: the block does not
wrap (`LevelOK`'s second clause gives `4 ≤ side`, and halving leaves `≥ 2`). Needed because `j = k`
is admissible while `j + 1` need not be. -/
theorem levelExtent_succ_pos {k : ℕ} (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) {j : ℕ}
    (hj : j ≤ k) (μ : Fin 3) : 0 < levelExtent L (j + 1) μ := by
  have hwide := (levelOK_of_pow hpow hj).2 μ
  have hcs := AdalyFormal.Balaban.U1AnchorCoarse.coarseExtent_spec
    (L := levelExtent L j) (ell := 2) (by norm_num) (levelOK_of_pow hpow hj).1 μ
  have hEq : levelExtent L (j + 1) μ = coarseExtent (levelExtent L j) 2 μ := rfl
  omega

/-- **THE HEADLINE, LATTICE READING — `k`-UNIFORM.** At every level `j ≤ k`, at the level-`j`
lattice's own `Δ_k` at a level-`j` background of radius `α₀`, on the preimage of p.428's subspace at
the level-`(j+1)` lattice:

    (γ* − 320α₀)·‖u‖² ≤ ⟨u, Δ_k(U_j) u⟩ + ⟨u, P_Ax u⟩ .

`γ*` and `320` are absolute; neither `j` nor `k` occurs in either. -/
theorem lattice_uniform_perturbed_coercive (L : PeriodicLatticeExtent) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k)
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L j))
    (hsup : frobSupBond U ≤ alpha0) (u : BondFnL2 (levelExtent L j))
    (hu : VLat (levelExtent L (j + 1))
      (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u))) :
    (gammaStar - pertConst * alpha0) * ‖u‖ ^ 2
      ≤ (inner ℝ u (deltaKCLMNormalized U u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent L j) 2) 2 u) : ℝ) :=
  lattice_perturbed_gf_on_preimage (levelOK_of_pow hpow hj).1
    (levelExtent_even hpow (j := j + 1) (by omega)) halpha U hsup u hu

/-- **THE HEADLINE, TOWER READING — `k`-UNIFORM.** The same, with the flat tower's OWN level-`j`
operator (the `j`-fold RG image, `TowerMilestone.towerAt`) dressed by that level's curvature
correction. By `dressed_dominates_lattice` this is implied by the lattice reading; it is stated
separately because it is the statement about the tower's own operators. -/
theorem tower_uniform_perturbed_coercive (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k)
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L j))
    (hsup : frobSupBond U ≤ alpha0) (u : BondFnL2 (levelExtent L j))
    (hu : VLat (levelExtent L (j + 1))
      (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u))) :
    (gammaStar - pertConst * alpha0) * ‖u‖ ^ 2
      ≤ (inner ℝ u (((towerAt L ha hpow j (by omega)).op + pertOp U) u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent L j) 2) 2 u) : ℝ) :=
  perturbed_gf_on_preimage (towerAt L ha hpow j (by omega)) (levelOK_of_pow hpow hj).1
    (levelExtent_even hpow (j := j + 1) (by omega)) halpha U hsup u hu

/-- **THE HEADLINE OVER THE CLASS.** `LevelClass L k α₀ U` is our MODELING PROXY for (3.35) in
level units (§3 — see the enumerated drops there; Sol third-family correction, 2026-08-02:
"transcribes" was too strong). This is p.428's shape on our carriers: ONE `j,k`-uniform
coefficient `γ* − 320·α₀`, POSITIVE exactly when `α₀ < γ*/320` (the admissible radius — an
earlier wording said "positive constant" unqualified; the theorem itself admits every `α₀ ≥ 0`
and this file proves the coefficient nonpositive at `10⁻¹⁸`). -/
theorem class_uniform_coercive (L : PeriodicLatticeExtent) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : ∀ j : ℕ, PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (levelExtent L j))
    (hU : LevelClass L k alpha0 U) (j : ℕ) (hj : j ≤ k) (u : BondFnL2 (levelExtent L j))
    (hu : VLat (levelExtent L (j + 1))
      (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u))) :
    (gammaStar - pertConst * alpha0) * ‖u‖ ^ 2
      ≤ (inner ℝ u (deltaKCLMNormalized (U j) u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent L j) 2) 2 u) : ℝ) :=
  lattice_uniform_perturbed_coercive L hpow j hj halpha (U j) (hU j hj) u hu

/-! ## §8 — `γ₀`, EXACTLY, AND BRACKETED FROM BOTH SIDES -/

/-- `γ₀(α₀) = γ* − 320α₀`. -/
noncomputable def gammaZero (alpha0 : ℝ) : ℝ := gammaStar - pertConst * alpha0

/-- **THE EXACT RATIONAL AT `α₀ = 10⁻²⁰`.** -/
theorem gammaZero_exact_at_1e_neg_20 :
    gammaZero (1 / 10 ^ 20)
      = 9279278215890927616 / 225225557534085120000000000000000000 := by
  unfold gammaZero pertConst
  rw [gammaStar_eq]
  norm_num

/-- **POSITIVE AT `α₀ = 10⁻²⁰`** — with a factor `≈ 13.9` of margin against `γ*`. -/
theorem gammaZero_pos_at_1e_neg_20 : 0 < gammaZero (1 / 10 ^ 20) := by
  rw [gammaZero_exact_at_1e_neg_20]; norm_num

/-- **NONPOSITIVE AT `α₀ = 10⁻¹⁸`** — the other side of the threshold, so the criterion is a real
constraint on `α₀` and not an inequality that holds for every radius. -/
theorem gammaZero_nonpos_at_1e_neg_18 : gammaZero (1 / 10 ^ 18) ≤ 0 := by
  unfold gammaZero pertConst
  rw [gammaStar_eq]
  norm_num

/-- **THE THRESHOLD, TWO-SIDED, IN ONE STATEMENT.** -/
theorem gammaZero_threshold_two_sided :
    0 < gammaZero (1 / 10 ^ 20) ∧ gammaZero (1 / 10 ^ 18) ≤ 0 :=
  ⟨gammaZero_pos_at_1e_neg_20, gammaZero_nonpos_at_1e_neg_18⟩

/-- **NO LOSS IN THE FLAT LIMIT.** `γ₀(0) = γ*` exactly — the perturbation route degenerates to the
flat tower's own constant with no residue. (For contrast, `CurvedTower.gammaLevel_flat_recovers_gammaV`
recovers `γ_V` only to a relative `10⁻⁹`, because that route's `defA` merges two coefficients of the
master defect bound. Nothing is merged here: the flat door is used unchanged and the perturbation is
subtracted from its conclusion.) -/
theorem gammaZero_at_zero : gammaZero 0 = gammaStar := by
  unfold gammaZero; ring

/-- **STILL POSITIVE AT `α₀ = 10⁻¹⁹`.** Recorded as a FACT about this route's own constant, next to
the fact that `CurvedTower.gammaLevel_nonpos_at_1e_neg_19` reports THAT route's constant nonpositive
at the same radius. The two are constants of DIFFERENT statements — `CurvedTower`'s carries (3.120)'s
tax `δ = 272α₀` and the covariant `Q₁(Ū)` clause, this one carries neither — so this is a comparison
of numbers, not a claim that one theorem supersedes the other. -/
theorem gammaZero_pos_at_1e_neg_19 : 0 < gammaZero (1 / 10 ^ 19) := by
  unfold gammaZero pertConst
  rw [gammaStar_eq]
  norm_num

/-! ### §8a — THE LEVEL-`0` STATEMENT IN THE SOURCE'S OWN VOCABULARY

`VRestrictedRoute.VSrc` is p.428's subspace as that module states it. `TowerMilestone.vLat_eq_vSrc`
says `VSrc` and `VLat` are the SAME predicate, so the level-`0` case of §7 can be read there with no
re-proof. Stated because it is the form a consumer of `VRestrictedRoute` can use directly. -/

/-- **p.428's SHAPE AT THE LATTICE, PERTURBATION ROUTE.** For every background of radius `α₀` and
every field whose flat coarse datum lies in `VSrc`,

    (γ* − 320α₀)·bondEnergy A ≤ ⟨A, Δ_k(U) A⟩ + P_Ax(A) . -/
theorem coercive_on_VSrc_perturbed (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0) (A : Bond L → SuTwo)
    (hA : AdalyFormal.Balaban.VRestrictedRoute.VSrc hdvd4
      (AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov (trivialU L) 2 A)) :
    (gammaStar - pertConst * alpha0) * bondEnergy A
      ≤ deltaKQuadFormNormalizedCorrected U A + pAx A (CoarseLattice L 2) 2 := by
  have hmem : VLat (coarseExtent L 2)
      (WithLp.ofLp (qLevel (two_dvd_of_four hdvd4) (WithLp.toLp 2 A : BondFnL2 L))) :=
    (AdalyFormal.Balaban.TowerMilestone.vLat_eq_vSrc hdvd4 _).1 hA
  have hmain := lattice_perturbed_gf_on_preimage (two_dvd_of_four hdvd4) (coarse_two_dvd hdvd4)
    halpha U hsup (WithLp.toLp 2 A) hmem
  rw [norm_sq_eq_bondEnergy, inner_deltaKCLMNormalized_eq, inner_pAxCLM_eq'] at hmain
  exact hmain

/-! ## §9 — NON-VACUITY: a GENUINELY CURVED background in the class, AT EVERY LEVEL

The class hypothesis is satisfied by a background whose PLAQUETTE HOLONOMY is proved `≠ 1`, so no
headline above is the flat case in disguise; and the subspace hypothesis is satisfied at a NONZERO
`u` whose coarse datum is a NONZERO element of the subspace, so no headline is a statement about
`{0}`. Both are discharged at `j = 0` AND at `j = 1` on a real extent tower (`witL`, sides `16 → 8
→ 4`), i.e. at a level where the lattice has genuinely changed. -/

/-- The class witness at an arbitrary lattice: a rotation by `t = 10⁻²¹` on ONE bond. LAW-19: the
family and its radius bound are `CurvedTower`'s, reused at a general extent. -/
noncomputable def witU (Λ : PeriodicLatticeExtent) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ :=
  bondU (zeroSite Λ, (0 : Fin 3)) (rotElem (1 / 10 ^ 21))

/-- It is inside the `α₀ = 10⁻²⁰` class: `2√2·10⁻²¹ ≤ 4·10⁻²¹ ≤ 10⁻²⁰`. -/
theorem witU_frobSup (Λ : PeriodicLatticeExtent) :
    frobSupBond (witU Λ) ≤ 1 / 10 ^ 20 := by
  refine le_trans (frobSupBond_bondRot_le _ (1 / 10 ^ 21)) ?_
  rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 10 ^ 21)]
  nlinarith [sqrt_two_le_two, Real.sqrt_nonneg (2 : ℝ)]

/-- **IT IS GENUINELY CURVED.** The plaquette holonomy at the bond's own base plaquette is
`rotElem 10⁻²¹ ≠ 1`. -/
theorem witU_curved (Λ : PeriodicLatticeExtent) (hpos : 0 < Λ 1) :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (witU Λ)
        (zeroSite Λ,
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
      ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  have h : AdalyFormal.Balaban.DeltaPrime.holonomyElem (witU Λ)
      (zeroSite Λ,
        (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
      = rotElem (1 / 10 ^ 21) := by
    unfold witU
    exact holonomy_singleBond_base_plaquette _ _ _ (rotElem (1 / 10 ^ 21))
      (bondU_at _ _) (fun _ hb => bondU_off _ _ hb) hpos
  rw [h]
  exact rotElem_ne_one (by norm_num)

/-- The class family: the curved witness at every level lattice. -/
noncomputable def witClassU (L : PeriodicLatticeExtent) (j : ℕ) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L j) :=
  witU (levelExtent L j)

/-- **THE CLASS IS INHABITED BY A CURVED FAMILY.** -/
theorem witClassU_mem (L : PeriodicLatticeExtent) (k : ℕ) :
    LevelClass L k (1 / 10 ^ 20) (witClassU L) :=
  fun j _ => witU_frobSup (levelExtent L j)

/-- **`class_uniform_coercive` FIRES, WITH BOTH SIDES STRICTLY POSITIVE, AT A CURVED BACKGROUND AND
A NONZERO FIELD, AT EVERY LEVEL `j ≤ k`.** The five conjuncts are, in order: the background is
genuinely curved at level `j`; the field is nonzero; its coarse datum is a NONZERO element of the
subspace (so the witness is not drawn from `ker Q`, where the hypothesis is free); the left side is
strictly positive; and hence — by APPLYING the headline itself — so is the right side. -/
theorem class_uniform_coercive_nonvacuous (L : PeriodicLatticeExtent) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k) :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (witClassU L j)
        (zeroSite (levelExtent L j),
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ ∃ u : BondFnL2 (levelExtent L j),
          VLat (levelExtent L (j + 1))
              (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u))
            ∧ u ≠ 0
            ∧ qLevel (levelOK_of_pow hpow hj).1 u ≠ 0
            ∧ 0 < gammaZero (1 / 10 ^ 20) * ‖u‖ ^ 2
            ∧ 0 < (inner ℝ u (deltaKCLMNormalized (witClassU L j) u) : ℝ)
                + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent L j) 2) 2 u) : ℝ) := by
  refine ⟨witU_curved (levelExtent L j) (levelExtent_pos hpow hj 1), ?_⟩
  obtain ⟨u, hVL, hune, hQne, -, -⟩ :=
    AdalyFormal.Balaban.TowerMilestone.level_gf_on_preimage_nonvacuous
      (baseLevel (levelExtent L j)) (levelExtent_four hpow hj)
  have hlhs : 0 < gammaZero (1 / 10 ^ 20) * ‖u‖ ^ 2 := by
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hune
    have hg := gammaZero_pos_at_1e_neg_20
    positivity
  refine ⟨u, hVL, hune, hQne, hlhs, lt_of_lt_of_le hlhs ?_⟩
  have h := class_uniform_coercive L hpow (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20)
    (witClassU L) (witClassU_mem L k) j hj u hVL
  have hgz : gammaZero (1 / 10 ^ 20) = gammaStar - pertConst * (1 / 10 ^ 20) := rfl
  rw [hgz]
  exact h

/-- The witness lattice is `TowerMilestone.witL` (side `16`), REUSED (LAW-19): its extent tower is
already computed there — `witL_extents : 15 → 7 → 3`, i.e. sides `16 → 8 → 4` — so `j = 1` is a
genuinely different lattice and this module defines no second numeral extent. -/
theorem prL_extents_reexport :
    (∀ μ : Fin 3, levelExtent witL 0 μ = 15) ∧ (∀ μ : Fin 3, levelExtent witL 1 μ = 7)
      ∧ (∀ μ : Fin 3, levelExtent witL 2 μ = 3) :=
  AdalyFormal.Balaban.TowerMilestone.witL_extents

/-- **NON-VACUITY AT `j = 0`, at a closed numeral lattice.** -/
theorem nonvacuous_depth_zero :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (witClassU witL 0)
        (zeroSite (levelExtent witL 0),
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ ∃ u : BondFnL2 (levelExtent witL 0),
          VLat (levelExtent witL 1)
              (WithLp.ofLp (qLevel (levelOK_of_pow witL_pow (by omega : 0 ≤ 1)).1 u))
            ∧ u ≠ 0
            ∧ qLevel (levelOK_of_pow witL_pow (by omega : 0 ≤ 1)).1 u ≠ 0
            ∧ 0 < gammaZero (1 / 10 ^ 20) * ‖u‖ ^ 2
            ∧ 0 < (inner ℝ u (deltaKCLMNormalized (witClassU witL 0) u) : ℝ)
                + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent witL 0) 2) 2 u) : ℝ) :=
  class_uniform_coercive_nonvacuous witL witL_pow 0 (by omega)

/-- **NON-VACUITY AT `j = 1` — a genuinely curved background at a LEVEL-`1` LATTICE.** This is the
witness the brief asks for: the lattice has halved (side `16 → 8`), the background there has
plaquette holonomy `≠ 1`, and both sides of the headline's conclusion are strictly positive. -/
theorem nonvacuous_depth_one :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (witClassU witL 1)
        (zeroSite (levelExtent witL 1),
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ ∃ u : BondFnL2 (levelExtent witL 1),
          VLat (levelExtent witL 2)
              (WithLp.ofLp (qLevel (levelOK_of_pow witL_pow (by omega : 1 ≤ 1)).1 u))
            ∧ u ≠ 0
            ∧ qLevel (levelOK_of_pow witL_pow (by omega : 1 ≤ 1)).1 u ≠ 0
            ∧ 0 < gammaZero (1 / 10 ^ 20) * ‖u‖ ^ 2
            ∧ 0 < (inner ℝ u (deltaKCLMNormalized (witClassU witL 1) u) : ℝ)
                + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent witL 1) 2) 2 u) : ℝ) :=
  class_uniform_coercive_nonvacuous witL witL_pow 1 (by omega)

/-! ### §9a — THE TOWER READING'S OWN WITNESS

`tower_uniform_perturbed_coercive` is a DIFFERENT theorem from `class_uniform_coercive`: its operator
is the RG image dressed, not the lattice operator. Per S91/§3a discipline it gets its own witness,
at `j = 1`, rather than inheriting one. -/

theorem tower_perturbed_nonvacuous (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k) :
    ∃ u : BondFnL2 (levelExtent L j),
      VLat (levelExtent L (j + 1)) (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u))
        ∧ u ≠ 0
        ∧ qLevel (levelOK_of_pow hpow hj).1 u ≠ 0
        ∧ 0 < gammaZero (1 / 10 ^ 20) * ‖u‖ ^ 2
        ∧ 0 < (inner ℝ u (((towerAt L ha hpow j (by omega)).op
              + pertOp (witClassU L j)) u) : ℝ)
            + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent L j) 2) 2 u) : ℝ) := by
  obtain ⟨u, hVL, hune, hQne, -, -⟩ :=
    AdalyFormal.Balaban.TowerMilestone.level_gf_on_preimage_nonvacuous
      (towerAt L ha hpow j (by omega)) (levelExtent_four hpow hj)
  have hlhs : 0 < gammaZero (1 / 10 ^ 20) * ‖u‖ ^ 2 := by
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hune
    have hg := gammaZero_pos_at_1e_neg_20
    positivity
  refine ⟨u, hVL, hune, hQne, hlhs, lt_of_lt_of_le hlhs ?_⟩
  have h := tower_uniform_perturbed_coercive L ha hpow j hj
    (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) (witClassU L j) (witU_frobSup _) u hVL
  have hgz : gammaZero (1 / 10 ^ 20) = gammaStar - pertConst * (1 / 10 ^ 20) := rfl
  rw [hgz]
  exact h

theorem tower_perturbed_nonvacuous_depth_one :
    ∃ u : BondFnL2 (levelExtent witL 1),
      VLat (levelExtent witL 2) (WithLp.ofLp (qLevel (levelOK_of_pow witL_pow
          (by omega : 1 ≤ 1)).1 u))
        ∧ u ≠ 0
        ∧ qLevel (levelOK_of_pow witL_pow (by omega : 1 ≤ 1)).1 u ≠ 0
        ∧ 0 < gammaZero (1 / 10 ^ 20) * ‖u‖ ^ 2
        ∧ 0 < (inner ℝ u (((towerAt witL (by norm_num : (0:ℝ) < 1) witL_pow 1
              (by omega)).op + pertOp (witClassU witL 1)) u) : ℝ)
            + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent witL 1) 2) 2 u) : ℝ) :=
  tower_perturbed_nonvacuous witL (by norm_num) witL_pow 1 (by omega)

/-! ## §10 — CONTROLS: the smallness hypothesis is LOAD-BEARING

§4's brick is not an inequality that would hold anyway. Dropping the hypothesis on `U` makes it
FALSE, and the failure is exhibited at this tree's own kernel-checked negative value for `Δ_k`, not
argued. -/

/-- **THE DIFFERENCE IS `≥ 4` AT `Δ_k`'s OWN NEGATIVE WITNESS.** `Δ_k(centralHolonomyU)` takes the
value `−4` on `deltaWitnessConfig` (`NormalizedCounterexampleSearch.central_counterexample_value`,
REUSED) while `curlEnergy ≥ 0`, so the two forms differ by at least `4` there. -/
theorem pert_difference_ge_four_at_central_witness :
    (4 : ℝ) ≤ |deltaKQuadFormNormalizedCorrected
        AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU
        AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig
      - curlEnergy AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig| := by
  rw [AdalyFormal.Balaban.NormalizedCounterexampleSearch.central_counterexample_value]
  have hc := curlEnergy_nonneg (AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig)
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **MUST-FAIL — the brick is FALSE without a hypothesis on `U`.** At `α₀ = 0` the brick's
conclusion would force the curved and flat forms to agree everywhere; the central witness refutes it.
So `abs_deltaK_sub_curlEnergy_le` is not a theorem that holds for every background, and the
hypothesis `frobSupBond U ≤ α₀` is doing work. -/
theorem pert_bound_needs_hypothesis :
    ¬ (∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
          AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
        (A : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo),
        |deltaKQuadFormNormalizedCorrected U A - curlEnergy A|
          ≤ pertConst * 0 * bondEnergy A) := by
  intro h
  have hx := h AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU
    AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig
  have h4 := pert_difference_ge_four_at_central_witness
  unfold pertConst at hx
  simp only [mul_zero, zero_mul] at hx
  linarith

/-- **THE CLASS EXCLUDES THAT WITNESS, BY A THEOREM.** `frobSupBond centralHolonomyU ≥ 2`
(`CurvedTower.frobSupBond_centralHolonomyU_ge_two`, REUSED), so it is not merely outside the
`α₀ = 10⁻²⁰` class — it is outside every class with `α₀ < 2`. The two-sided control on `LevelClass`
is therefore complete: `witClassU` is a curved family INSIDE it, `centralHolonomyU` is OUTSIDE it,
and the brick's conclusion holds on the first and fails on the second. -/
theorem central_witness_outside_class {alpha0 : ℝ} (h : alpha0 < 2) :
    ¬ (frobSupBond AdalyFormal.Balaban.RegularityHolonomy.centralHolonomyU ≤ alpha0) := by
  intro hc
  have h2 := AdalyFormal.Balaban.CurvedTower.frobSupBond_centralHolonomyU_ge_two
  linarith

/-! ## §11 — THE TWO DELTAS, ATTACKED

The brief named these two as deltas to disclose. Neither is left at a name: the first is REFUTED as
an internal identification, and the second is convicted as content-free AS FIRST STATED, restated
correctly, and then bracketed on both sides. -/

/-! ### §11a — DELTA 1, THE DENOTATION BRIDGE: REFUTED INTERNALLY

The bridge splits in two, and only one half is about the paper:

* the INTERNAL half — is this tree's level-`j` tower operator the level-`j` lattice's own `Δ_k(1)`?
  That is a statement about Lean objects and it is decidable here. It is **FALSE at `j = 1`**
  (`denotation_bridge_false`). At `j = 0` it HOLDS (`TowerMilestone.towerAt_zero`), which is exactly
  why a reader could slip into assuming it upward.
* the EXTERNAL half — is either family the `Δ_k` of CMP99b p.428? That cannot be settled in a proof
  assistant at all: `Δ_k` occurs on NO other page of that paper (measured, `compute/sectB_pages/`),
  so there is no second display to check a candidate against. It is stated here as prose, not as a
  fake `Prop`, because a `Prop` about a Lean object could only ever be a stipulation.

The refutation is quantitative, not a parity trick: the RG image dominates TWICE the coarse curl
energy (`next_ge_two_curl`, the factor `2` that `TowerMilestone.stepLevel` throws away when it
records only `curlEnergy ≤ ⟨B,next B⟩`), while the lattice operator's form IS the coarse curl energy
exactly. So the two differ by a factor at every `B` of positive curl energy. -/

/-- **THE RG IMAGE DOMINATES `2·curlEnergy`.** `TowerMilestone.stepLevel` proves the level invariant
with a factor `2` to spare and then discards the factor when it packages `Level.hcurl`. Here the
factor is kept: `2·curlEnergy(B) ≤ ⟨B, Δ_{j+1} B⟩`. Same four inputs as `stepLevel` — the lift
identity, `P_Ax ≥ 0`, the level's own invariant, and Stokes at `ell = 2`. -/
theorem next_ge_two_curl (lvl : Level Λ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * 2 ≤ Λ μ + 1) {a : ℝ} (ha : 0 < a)
    (B : BondFnL2 (coarseExtent Λ 2)) :
    2 * curlEnergy (WithLp.ofLp B)
      ≤ (inner ℝ B ((levelRung lvl hdvd hwide ha).next B) : ℝ) := by
  have hlift := rung_inner_next_lift (levelRung lvl hdvd hwide ha) B
  have hop : (inner ℝ ((levelRung lvl hdvd hwide ha).G
        ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))
      (piOp lvl.op 0 ((levelRung lvl hdvd hwide ha).G
        ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))) : ℝ)
      = (inner ℝ ((levelRung lvl hdvd hwide ha).G
          ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))
        (lvl.op ((levelRung lvl hdvd hwide ha).G
          ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)))) : ℝ) := by
    simp [piOp]
  rw [hop] at hlift
  set u : BondFnL2 Λ := (levelRung lvl hdvd hwide ha).G
    ((levelRung lvl hdvd hwide ha).Qstar ((levelRung lvl hdvd hwide ha).S B)) with hu
  have hPnn : (0 : ℝ) ≤ (inner ℝ u ((levelRung lvl hdvd hwide ha).P u) : ℝ) :=
    pAxCLM_pos (CoarseLattice Λ 2) 2 u
  have hQu : (levelRung lvl hdvd hwide ha).Q u = B := (levelRung lvl hdvd hwide ha).T_S B
  have hofLp : WithLp.ofLp B
      = pullS (by norm_num) hdvd
        (AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov
          (trivialU Λ) 2 (WithLp.ofLp u)) := by
    rw [← hQu]; rfl
  have hcurlB : curlEnergy (WithLp.ofLp B)
      = coarseCurlEnergy hdvd (AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov
          (trivialU Λ) 2 (WithLp.ofLp u)) := by
    rw [hofLp]; exact curlEnergy_pullS _ _ _
  have hstokes := coarseCurlEnergy_Q_le (L := Λ) (ell := 2) (by norm_num) hdvd (WithLp.ofLp u)
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at hstokes
  have hlvlc := lvl.hcurl u
  rw [hcurlB]
  linarith

/-- **DELTA 1, INTERNAL HALF — the identification of the tower's level operator with the level
lattice's own `Δ_k(1)`.** Stated as a `Prop` so that the refutation below has something to refute.
It HOLDS at `j = 0` by `TowerMilestone.towerAt_zero`. -/
def DenotationBridge (L : PeriodicLatticeExtent) (a : ℝ) (ha : 0 < a) (k : ℕ)
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) : Prop :=
  ∀ (j : ℕ) (hj : j ≤ k + 1),
    (towerAt L ha hpow j hj).op = deltaKCLMNormalized (trivialU (levelExtent L j))

/-- **IT HOLDS AT `j = 0`** — recorded so that the refutation below is visibly about the levels
ABOVE the base, and is not a type-level artifact. -/
theorem denotation_bridge_at_zero (L : PeriodicLatticeExtent) {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (h0 : 0 ≤ k + 1) :
    (towerAt L ha hpow 0 h0).op = deltaKCLMNormalized (trivialU (levelExtent L 0)) := rfl

/-- **DELTA 1 IS REFUTED.** On `witL` (sides `16 → 8 → 4`) at depth `k = 1` the bridge is FALSE: at
`j = 1` the tower's operator dominates `2·curlEnergy` while the lattice operator's form IS
`curlEnergy`, and the level-`1` lattice carries a field of strictly positive curl energy
(`TowerMilestone.hcurl_is_load_bearing`, REUSED). So the two operators are different operators, and
no theorem of this file may be read as being about the level lattice's own `Δ_k` at `j ≥ 1` unless it
says so — which is why §7 states the lattice reading SEPARATELY. -/
theorem denotation_bridge_false :
    ¬ DenotationBridge witL 1 (by norm_num) 1 witL_pow := by
  intro h
  have hdvd1 : ∀ μ : Fin 3, (2 : ℕ) ∣ (levelExtent witL 1 μ + 1) :=
    levelExtent_even witL_pow (j := 1) (by omega)
  have hp1 : 1 < levelExtent witL 1 0 + 1 := by
    rw [witL_extents.2.1 0]; omega
  obtain ⟨B, hBne, hBcurl, -, -⟩ :=
    hcurl_is_load_bearing (Λ := levelExtent witL 1) hdvd1 hp1 rotGen_ne_zero 1
  have hbridge := h 1 (by omega)
  have hlaw := towerAt_law witL (a := 1) (by norm_num) witL_pow 0 (by omega)
  have hlow := next_ge_two_curl (towerAt witL (a := 1) (by norm_num) witL_pow 0 (by omega))
    (levelOK_of_pow witL_pow (by omega : (0:ℕ) ≤ 1)).1
    (levelOK_of_pow witL_pow (by omega : (0:ℕ) ≤ 1)).2 (by norm_num : (0:ℝ) < 1) B
  rw [← hlaw] at hlow
  rw [hbridge] at hlow
  have hlow2 : 2 * curlEnergy (WithLp.ofLp B)
      ≤ (inner ℝ B (deltaKCLMNormalized (trivialU (levelExtent witL 1)) B) : ℝ) := hlow
  rw [inner_deltaK_flat] at hlow2
  linarith

/-! ### §11b — DELTA 2, CROSS-LEVEL CLASS PROPAGATION: FIRST STATEMENT CONVICTED, RESTATED

⚠ **THE FIRST STATEMENT WAS CONTENT-FREE, AND THAT IS RECORDED HERE RATHER THAN REPAIRED SILENTLY
(S75).** This section originally carried

~~`CrossLevelClassPropagation L k := ∀ α₀ ≥ 0, ∀ U0 with frobSupBond U0 ≤ α₀, ∃ U with U 0 = U0 and
LevelClass L k α₀ U`~~

as the named open Prop. It is **TRUE for every `L` and `k`, trivially** — take `U j := trivialU` for
`j ≥ 1` (`weakClassPropagation_trivially_true` below proves exactly that). This is the S91 failure
mode (an existential over free data hands the prover the easiest instance) committed inside a
disclosure, where it is at its most dangerous: a reader would have taken it for the missing
mathematics. The corrected statement fixes the blocking map as DATA, so nothing is left for an
existential to choose. -/

/-- The convicted first statement, kept so the conviction is checkable. -/
def WeakClassPropagation (L : PeriodicLatticeExtent) (k : ℕ) : Prop :=
  ∀ alpha0 : ℝ, 0 ≤ alpha0 →
    ∀ U0 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L 0),
      frobSupBond U0 ≤ alpha0 →
        ∃ U : ∀ j : ℕ, PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
          (levelExtent L j), U 0 = U0 ∧ LevelClass L k alpha0 U

/-- **THE CONVICTION.** The first statement is provable for every lattice and every depth, so it
asserted nothing about the RG dynamics. -/
theorem weakClassPropagation_trivially_true (L : PeriodicLatticeExtent) (k : ℕ) :
    WeakClassPropagation L k := by
  intro alpha0 halpha U0 hU0
  refine ⟨fun j => Nat.rec (motive := fun i =>
      PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L i))
    U0 (fun i _ => trivialU (levelExtent L (i + 1))) j, rfl, ?_⟩
  intro j _
  cases j with
  | zero => exact hU0
  | succ i => rw [frobSupBond_trivialU]; exact halpha

/-- The level-`j` member of the tower generated by a FIXED family of blocking maps. Dependent
recursion over the level index; nothing existential. -/
noncomputable def blkTower {L : PeriodicLatticeExtent}
    (blk : ∀ j : ℕ, PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (levelExtent L j) → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (levelExtent L (j + 1)))
    (U0 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L 0)) :
    ∀ j : ℕ, PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L j)
  | 0 => U0
  | (j + 1) => blk j (blkTower blk U0 j)

@[simp] theorem blkTower_zero {L : PeriodicLatticeExtent} (blk : _) (U0 : _) :
    blkTower (L := L) blk U0 0 = U0 := rfl

/-- **DELTA 2, RESTATED.** The blocking map is DATA; the statement is that ITS tower stays inside
the class. This is CMP99a (1.66)'s territory and is the CONSUMER's burden, not this lemma's:
p.428 quantifies over `U` IN THE CLASS, and (3.35) is one condition on one configuration imposing a
bound at every index in that index's own units (§3).

⚠ What is known against it: `BlockedBackground`'s `ubarSU2_constU` chain shows the SU(2) blocking is
the `ell`-th power map on constant configurations and therefore EXPANDS `frobSupBond` there
(`no_contraction_constant`: for every `c < 2` the contraction `frobSupBond (Ū V) ≤ c·frobSupBond V`
fails). That module is NOT imported here and nothing below asserts anything about its map; the
sentence is a pointer, and the question of which side Bałaban's actual blocking falls on is left
exactly where it is. -/
def ClassPropagation (L : PeriodicLatticeExtent) (k : ℕ) (alpha0 : ℝ)
    (blk : ∀ j : ℕ, PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (levelExtent L j) → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (levelExtent L (j + 1))) : Prop :=
  ∀ U0 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L 0),
    frobSupBond U0 ≤ alpha0 → LevelClass L k alpha0 (blkTower blk U0)

/-- **THE RESTATED PROP IS NOT VACUOUS: it HOLDS for a map that flattens.** -/
theorem classPropagation_holds_for_flattening (L : PeriodicLatticeExtent) (k : ℕ)
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0) :
    ClassPropagation L k alpha0 (fun j _ => trivialU (levelExtent L (j + 1))) := by
  intro U0 hU0 j _
  cases j with
  | zero => exact hU0
  | succ i => rw [show blkTower (L := L) (fun j _ => trivialU (levelExtent L (j + 1))) U0 (i + 1)
      = trivialU (levelExtent L (i + 1)) from rfl, frobSupBond_trivialU]; exact halpha

/-- The constant `−1` background at an arbitrary lattice: the simplest configuration OUTSIDE every
class of radius `< 2`. `CurvedTower.frobSupBond_centralHolonomyU_ge_two` is the same computation at
one fixed lattice and one marked bond; this is it at an arbitrary lattice, so it is usable at every
level. -/
noncomputable def negOneU (Lam : PeriodicLatticeExtent) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lam :=
  fun _ => AdalyFormal.Balaban.DeltaKFull.negOneElem

/-- `‖(−1) − 1‖_F = √8 > 2`. -/
theorem frobSupBond_negOneU_ge_two (Lam : PeriodicLatticeExtent) :
    (2 : ℝ) ≤ frobSupBond (negOneU Lam) := by
  refine le_trans ?_ (AdalyFormal.Balaban.RegularUPerturbation.frobNorm_le_frobSupBond
    (negOneU Lam) (zeroSite Lam, (0 : Fin 3)))
  have hm : ((AdalyFormal.Balaban.DeltaKFull.negOneElem :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1
      = !![(-2 : ℂ), 0; 0, -2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AdalyFormal.Balaban.DeltaKFull.negOneElem] <;> ring
  have hsq : AdalyFormal.Balaban.RMapLipschitz.frobSq
      (((AdalyFormal.Balaban.DeltaKFull.negOneElem :
        Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 8 := by
    rw [hm]
    simp [AdalyFormal.Balaban.RMapLipschitz.frobSq, Complex.normSq_apply]
    norm_num
  show (2 : ℝ) ≤ AdalyFormal.Balaban.RMapLipschitz.frobNorm
    (((AdalyFormal.Balaban.DeltaKFull.negOneElem :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
  unfold AdalyFormal.Balaban.RMapLipschitz.frobNorm
  rw [hsq]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8), Real.sqrt_nonneg (8:ℝ)]

/-- **AND IT FAILS for a map that leaves the class** — so it is a real constraint on the map, not a
theorem that holds whatever the dynamics does. The failing map sends every configuration to the
central `−1` background, whose radius is `≥ 2` (`CurvedTower.frobSupBond_centralHolonomyU_ge_two`,
REUSED via §10's `central_witness_outside_class`). Together with the previous theorem this brackets
the restated Prop on both sides. -/
theorem classPropagation_fails_for_expanding (L : PeriodicLatticeExtent) (k : ℕ) (hk : 1 ≤ k)
    {alpha0 : ℝ} (halpha : alpha0 < 2) (halpha0 : 0 ≤ alpha0) :
    ¬ ClassPropagation L k alpha0 (fun j _ => negOneU (levelExtent L (j + 1))) := by
  intro h
  have h0 : frobSupBond (trivialU (levelExtent L 0)) ≤ alpha0 := by
    rw [frobSupBond_trivialU]; exact halpha0
  have h1 := h _ h0 1 hk
  have h2 : blkTower (L := L) (fun j _ => negOneU (levelExtent L (j + 1)))
      (trivialU (levelExtent L 0)) 1 = negOneU (levelExtent L 1) := rfl
  rw [h2] at h1
  have h3 := frobSupBond_negOneU_ge_two (levelExtent L 1)
  linarith


/-! ## §12 — THE SAME RESULT AT THE **COVARIANT** SUBSPACE CLAUSE

`CurvedTower.VCurved Λ Ū` is p.428's three clauses with (c3) read at the COVARIANT block average
`Q₁(Ū)` — the reading that module argues is the source's. The perturbation route does not care which
clause the flat half is stated at: it only needs SOME positive lower bound on `⟨u,Δu⟩ + ⟨u,P u⟩`, and
then subtracts §5's operator bound from it. So the whole of §6-§7a runs again at the covariant clause
with `CurvedTower.curved_gf_on_preimage` in place of `TowerMilestone.level_gf_on_preimage`, and
nothing is rebuilt (LAW-19): a `Level` is a `CurvedLevel` at `(c,ρ,σ) = (1,0,0)`.

The constant changes — it becomes `CurvedTower.gammaLevel 1 0 0 (γ_c(ᾱ,ε))`, which
`CurvedTower.gammaLevel_flat_recovers_gammaV` pins to within a relative `10⁻⁹` of `γ*` in the flat
limit — but it is still free of `j` and of `k`, and the `α₀`-loss is the same `320α₀`. -/

/-- **A `Level` IS A `CurvedLevel` AT `(1,0,0)`.** `hcurl` is the invariant plus `P_Ax ≥ 0`; `hlow` is
`Level.hpsd`. This is the bridge that lets the covariant door be read at the flat tower's levels. -/
noncomputable def curvedLevelOfLevel (lvl : Level Λ) : CurvedLevel Λ 1 0 0 where
  op := lvl.op
  hsym := lvl.hsym
  hcurl := by
    intro v
    have h := lvl.hcurl v
    have hP : (0 : ℝ) ≤ (inner ℝ v (pAxCLM (CoarseLattice Λ 2) 2 v) : ℝ) := pAxCLM_pos _ _ v
    linarith
  hlow := by
    intro v
    have h := lvl.hpsd v
    linarith

@[simp] theorem curvedLevelOfLevel_op (lvl : Level Λ) : (curvedLevelOfLevel lvl).op = lvl.op := rfl

/-- **THE PERTURBED DOOR AT THE COVARIANT CLAUSE.** Same statement as `perturbed_gf_on_preimage`,
same `320α₀` loss, with the subspace read at `Q₁(Ū)`. -/
theorem covariant_perturbed_gf_on_preimage (lvl : Level Λ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (Λ μ + 1))
    (hdvd' : ∀ μ : Fin 3, (2 : ℕ) ∣ (coarseExtent Λ 2 μ + 1))
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (coarseExtent Λ 2))
    {abar : ℝ} (habar : 0 ≤ abar) (hsupbar : frobSupBond Ubar ≤ abar)
    {eps : ℝ} (heps : 0 < eps) (hgc : 0 < gammaCurved abar eps)
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Λ)
    (hsup : frobSupBond U ≤ alpha0) (u : BondFnL2 Λ)
    (hu : VCurved (coarseExtent Λ 2) Ubar (WithLp.ofLp (qLevel hdvd u))) :
    (gammaLevel 1 0 0 (gammaCurved abar eps) - pertConst * alpha0) * ‖u‖ ^ 2
      ≤ (inner ℝ u ((lvl.op + pertOp U) u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice Λ 2) 2 u) : ℝ) := by
  have hbase := curved_gf_on_preimage (curvedLevelOfLevel lvl) (by norm_num) hdvd hdvd'
    Ubar habar hsupbar heps hgc u hu
  have hpert := abs_le.mp (abs_inner_pertOp_le halpha U hsup u)
  rw [inner_add_pertOp]
  rw [curvedLevelOfLevel_op] at hbase
  linarith [hbase, hpert.1]

/-- **THE COVARIANT-CLAUSE HEADLINE, `k`-UNIFORM.** At the level-`j` LATTICE operator at the level-`j`
background, on the preimage of p.428's subspace at the level-`(j+1)` lattice read COVARIANTLY. -/
theorem covariant_uniform_perturbed_coercive (L : PeriodicLatticeExtent) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k)
    (Ubar : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (levelExtent L (j + 1)))
    {abar : ℝ} (habar : 0 ≤ abar) (hsupbar : frobSupBond Ubar ≤ abar)
    {eps : ℝ} (heps : 0 < eps) (hgc : 0 < gammaCurved abar eps)
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (levelExtent L j))
    (hsup : frobSupBond U ≤ alpha0) (u : BondFnL2 (levelExtent L j))
    (hu : VCurved (levelExtent L (j + 1)) Ubar
      (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u))) :
    (gammaLevel 1 0 0 (gammaCurved abar eps) - pertConst * alpha0) * ‖u‖ ^ 2
      ≤ (inner ℝ u (deltaKCLMNormalized U u) : ℝ)
        + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent L j) 2) 2 u) : ℝ) := by
  have h := covariant_perturbed_gf_on_preimage (baseLevel (levelExtent L j))
    (levelOK_of_pow hpow hj).1 (levelExtent_even hpow (j := j + 1) (by omega))
    Ubar habar hsupbar heps hgc halpha U hsup u hu
  rwa [baseLevel_add_pertOp] at h

/-- The covariant-clause constant is positive at the point the witnesses use: `ᾱ = 10⁻²⁰`, `ε = 1`,
`α₀ = 10⁻²⁰`. Exact rational arithmetic, no floating point. -/
theorem covariant_gamma_pos_at_witness :
    0 < gammaLevel 1 0 0 (gammaCurved (1 / 10 ^ 20) 1) - pertConst * (1 / 10 ^ 20 : ℝ) := by
  unfold gammaLevel pertConst AdalyFormal.Balaban.CurvedTower.defKappa
    AdalyFormal.Balaban.CurvedTower.defA AdalyFormal.Balaban.CurvedTower.defB
    AdalyFormal.Balaban.CovariantFibreTransfer.gammaCurved
  norm_num

/-- **NON-VACUITY FOR THE COVARIANT-CLAUSE HEADLINE, AT EVERY LEVEL `j ≤ k`.** Its own witness, not
inherited: the covariant subspace `VCurved` is a DIFFERENT predicate from `VLat`, so §9's witnesses
do not certify it. Both backgrounds (fine and coarse) are genuinely curved, the field is nonzero,
its coarse datum is a nonzero element of the covariant subspace, and both sides of THIS theorem's
conclusion are strictly positive — the right-hand side by applying the theorem itself. -/
theorem covariant_uniform_nonvacuous (L : PeriodicLatticeExtent) {k : ℕ}
    (hpow : ∀ μ : Fin 3, (2 : ℕ) ^ (k + 2) ∣ (L μ + 1)) (j : ℕ) (hj : j ≤ k) :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (witClassU L j)
        (zeroSite (levelExtent L j),
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ AdalyFormal.Balaban.DeltaPrime.holonomyElem (witClassU L (j + 1))
        (zeroSite (levelExtent L (j + 1)),
          (⟨(0, 1), by decide⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections))
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ ∃ u : BondFnL2 (levelExtent L j),
          VCurved (levelExtent L (j + 1)) (witClassU L (j + 1))
              (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u))
            ∧ u ≠ 0
            ∧ qLevel (levelOK_of_pow hpow hj).1 u ≠ 0
            ∧ 0 < (gammaLevel 1 0 0 (gammaCurved (1 / 10 ^ 20) 1)
                - pertConst * (1 / 10 ^ 20 : ℝ)) * ‖u‖ ^ 2
            ∧ 0 < (inner ℝ u (deltaKCLMNormalized (witClassU L j) u) : ℝ)
                + (inner ℝ u (pAxCLM (CoarseLattice (levelExtent L j) 2) 2 u) : ℝ) := by
  have hposj : 0 < levelExtent L j 1 := levelExtent_pos hpow hj 1
  have hposj1 : 0 < levelExtent L (j + 1) 1 := levelExtent_succ_pos hpow hj 1
  refine ⟨witU_curved (levelExtent L j) hposj, witU_curved (levelExtent L (j + 1)) hposj1, ?_⟩
  -- the coarse witness lives in the COVARIANT subspace because every link of `witClassU` fixes
  -- `rotGen` (`CurvedTower.bondRot_fix_rotGen`), so `Q₁(Ū)` and `Q₁(1)` agree on it exactly.
  have hmem : VCurved (levelExtent L (j + 1)) (witClassU L (j + 1))
      (AdalyFormal.Balaban.VRestrictedRoute.vWitFine
        (Lc := levelExtent L (j + 1)) rotGen) :=
    vWitFine_mem_VCurved (levelExtent_even hpow (j := j + 1) (by omega))
      (witClassU L (j + 1)) (fun b => bondRot_fix_rotGen _ (1 / 10 ^ 21) b)
  have hne : AdalyFormal.Balaban.VRestrictedRoute.vWitFine
      (Lc := levelExtent L (j + 1)) rotGen ≠ 0 := by
    refine AdalyFormal.Balaban.TowerMilestone.vWitFine_ne_zero ?_ rotGen_ne_zero
    have h := levelExtent_succ_pos hpow hj 0
    omega
  set B : BondFnL2 (levelExtent L (j + 1)) :=
    WithLp.toLp 2 (AdalyFormal.Balaban.VRestrictedRoute.vWitFine
      (Lc := levelExtent L (j + 1)) rotGen) with hB
  have hBne : B ≠ 0 := fun h => hne (congrArg WithLp.ofLp h)
  obtain ⟨u, hu⟩ := AdalyFormal.Balaban.TowerMilestone.qLevel_surjective
    (Λ := levelExtent L j) (levelOK_of_pow hpow hj).1 B
  have hune : u ≠ 0 := by
    intro h; refine hBne ?_; rw [← hu, h]; exact map_zero _
  have hVC : VCurved (levelExtent L (j + 1)) (witClassU L (j + 1))
      (WithLp.ofLp (qLevel (levelOK_of_pow hpow hj).1 u)) := by rw [hu]; exact hmem
  have hQne : qLevel (levelOK_of_pow hpow hj).1 u ≠ 0 := by rw [hu]; exact hBne
  have hlhs : 0 < (gammaLevel 1 0 0 (gammaCurved (1 / 10 ^ 20) 1)
      - pertConst * (1 / 10 ^ 20 : ℝ)) * ‖u‖ ^ 2 := by
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hune
    have hg := covariant_gamma_pos_at_witness
    positivity
  refine ⟨u, hVC, hune, hQne, hlhs, lt_of_lt_of_le hlhs ?_⟩
  have hgcpos : 0 < gammaCurved (1 / 10 ^ 20 : ℝ) 1 := by
    rw [gammaCurved_pos_iff]; norm_num
  exact covariant_uniform_perturbed_coercive L hpow j hj (witClassU L (j + 1))
    (by norm_num) (witU_frobSup _) (by norm_num) hgcpos
    (by norm_num : (0:ℝ) ≤ 1 / 10 ^ 20) (witClassU L j) (witU_frobSup _) u hVC

#print axioms curvedLevelOfLevel
#print axioms curvedLevelOfLevel_op
#print axioms covariant_perturbed_gf_on_preimage
#print axioms covariant_uniform_perturbed_coercive
#print axioms covariant_gamma_pos_at_witness
#print axioms covariant_uniform_nonvacuous

/-! ## §13 — AXIOM AUDIT -/


#print axioms LevelClass
#print axioms pertConst
#print axioms pertConst_pos
#print axioms pertOp
#print axioms gammaZero
#print axioms witU
#print axioms witClassU
#print axioms DenotationBridge
#print axioms WeakClassPropagation
#print axioms blkTower
#print axioms ClassPropagation
#print axioms negOneU
#print axioms dstarDQuadForm_trivialU_eq_curlEnergy
#print axioms curlEnergy_le_bondEnergy
#print axioms curlDrift_eq_sub
#print axioms abs_sq_sub_sq_le_drift
#print axioms abs_dstarD_sub_curlEnergy_le
#print axioms abs_deltaK_sub_curlEnergy_le
#print axioms pertOp_trivialU
#print axioms baseLevel_add_pertOp
#print axioms pertOp_symm
#print axioms abs_inner_pertOp_le
#print axioms inner_pertOp_eq
#print axioms inner_add_pertOp
#print axioms perturbed_gf_on_preimage
#print axioms lattice_perturbed_gf_on_preimage
#print axioms Level.op_dominates_flat
#print axioms dressed_dominates_lattice
#print axioms levelExtent_pos
#print axioms levelExtent_succ_pos
#print axioms lattice_uniform_perturbed_coercive
#print axioms tower_uniform_perturbed_coercive
#print axioms class_uniform_coercive
#print axioms gammaZero_exact_at_1e_neg_20
#print axioms gammaZero_pos_at_1e_neg_20
#print axioms gammaZero_nonpos_at_1e_neg_18
#print axioms gammaZero_threshold_two_sided
#print axioms gammaZero_at_zero
#print axioms gammaZero_pos_at_1e_neg_19
#print axioms coercive_on_VSrc_perturbed
#print axioms levelClass_trivial
#print axioms witU_frobSup
#print axioms witU_curved
#print axioms witClassU_mem
#print axioms class_uniform_coercive_nonvacuous
#print axioms witL_pow
#print axioms prL_extents_reexport
#print axioms nonvacuous_depth_zero
#print axioms nonvacuous_depth_one
#print axioms tower_perturbed_nonvacuous
#print axioms tower_perturbed_nonvacuous_depth_one
#print axioms pert_difference_ge_four_at_central_witness
#print axioms pert_bound_needs_hypothesis
#print axioms central_witness_outside_class
#print axioms next_ge_two_curl
#print axioms denotation_bridge_at_zero
#print axioms denotation_bridge_false
#print axioms weakClassPropagation_trivially_true
#print axioms blkTower_zero
#print axioms classPropagation_holds_for_flattening
#print axioms frobSupBond_negOneU_ge_two
#print axioms classPropagation_fails_for_expanding


end AdalyFormal.Balaban.PerturbationRoute
