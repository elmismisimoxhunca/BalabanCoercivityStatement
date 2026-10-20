/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RegularUDirectCoercivity
import AdalyFormal.Balaban.RegularUQChain

set_option autoImplicit false

/-!
# `RegularUCoercivityFull.lean` — the regular-`U` SINGLE-SCALE coercivity of the leading covariant
term `deltaJ(U)` on the TARGET domain `ker Q₁(U) ∩ axial-gauge`, modulo `[UNIF-ALPHA]`.

## ⚠ NOMENCLATURE (F6, 2026-07-26) — `deltaJ(U)` HERE IS THE CURL ENERGY,
**NOT** THE SCHUR COMPLEMENT

Every occurrence of "`deltaJ(U)`" in this module's prose, and in its declaration NAMES
(`deltaJ_regularU_coercive_on_kerQU`, `deltaJ_coercive_at_witA`, …), is a **local nickname** for

    CovariantHj.dstarDQuadForm U A
      := covPlaqInner (curlValueCovariant U A) (curlValueCovariant U A)   =   ‖∂^U A‖²

— the covariant curl / `D_U^*D_U` energy, which is what every Lean STATEMENT in this module
actually contains (read the conclusion of `deltaJ_regularU_coercive_on_kerQU`: it is
`… ≤ dstarDQuadForm U A`).

It is a **DIFFERENT DECLARATION** from `CovariantHjFaithful.deltaJQuadFormCovFaithful`, the Schur
complement / minimized curl energy `‖curl_U A₀ − P_W(curl_U A₀)‖²` standing for CMP99b
(3.156)'s `Δ_j`. The tree PROVES they are not interchangeable, and in the unusable direction:

    CStarDeltaKCCoercive.deltaJQuadFormCovFaithful_le_dstarDQuadForm :
      deltaJQuadFormCovFaithful ell levels U A₀  ≤  dstarDQuadForm U A₀

so a LOWER bound on `dstarDQuadForm` — which is exactly what this module proves — is **not** a
lower bound on `deltaJQuadFormCovFaithful`; and on the subspace `V` the smaller object is
identically zero
(`CovariantHjFaithful.deltaJQuadFormCovFaithful_eq_zero_of_mem_V`).

**The Lean statements here are clean; the nickname was the defect.** Filed by the level-collapse
sweep as F6 (`compute/level_collapse_sweep/FINDINGS.md`): this naming is what let "coercivity of
`deltaJ`" read as progress toward `Δ_k`. Declaration names are deliberately NOT renamed (a rename
is a semantic-risk edit while lanes are live); the nickname is pinned to its object instead. The
"NOT the full `C*Δ_kC`" bullet in HONEST SCOPE below is the correct reading, and this banner says
WHY in terms of the two declarations.

**The culminating brick of the regular-`U` coercivity constant.** It combines three axiom-clean
inputs proved this campaign:

* **(b1)** `RegularUDirectCoercivity.deltaJ_regularU_coercive_of_U1coercive` — the single-scale
  operator transfer `deltaJ(U)A ≥ (√γ' − 4√2·α₁)²·bondEnergy A` from a `U=1` coercivity `hcoerc1` at
  `A` and smallness `4√2·α₁ ≤ √γ'` (`α₁ = frobSupBond U`);
* **(b2)** the su(2) `U=1` ADDITIVE base `SuTwoGeomU1.suTwoGeomAdditive_trivialU_of_admissible`
  (`2·‖Q₁(1)A‖² + deltaJ(1)A ≥ γ₀·bondEnergy A` on the su(2) axial gauge, `γ₀ = (1/108)(1/2⁴)`) — the
  base needs ONLY the axial gauge, NOT `Q₁(1)A = 0`;
* **`[QCHAIN-SENS]`, `L²`-aggregated** `RegularUQChain.coarseDriftEnergy_le`
  (`∑_b ‖(Q₁(1)−Q₁(U))A(b)‖² ≤ (64/ell)·α₁²·bondEnergy A`, `C_Q² = 64/ell`, `k`-free).

## The domain-perturbation combine (the content)

On the TARGET domain `A ∈ ker Q₁(U)` (i.e. `Q₁(U)A = 0` pointwise), the drift equals the flat coarse
restriction, so `[QCHAIN-SENS]` at `ell = 2` gives
`covCoarseBondInner (Q₁(1)A) (Q₁(1)A) = ∑_b ‖Q₁(1)A(b)‖² ≤ 32·α₁²·bondEnergy A` — `A` is only
APPROXIMATELY in `ker Q₁(1)` (its flat coarse energy is `O(α₁²)`, not exactly `0`). Feeding this into
the su(2) additive base (which needs only the axial gauge) removes the coarse term:
`deltaJ(1)A ≥ γ₀·bondEnergy A − 2·(32·α₁²·bondEnergy A) = (γ₀ − 64·α₁²)·bondEnergy A =: γ'·bondEnergy A`,
a genuine `U=1` coercivity at `A` with the REDUCED constant `γ' = γ₀ − 64·α₁²`. The (b1) transfer then
yields, on `ker Q₁(U) ∩ axial-gauge`,

  `(√(γ₀ − 64·α₁²) − 4√2·α₁)² · bondEnergy A  ≤  deltaJ(U)A`,

with the EXPLICIT, `k`-INDEPENDENT constant `γ'' = (√(γ₀ − 64·α₁²) − 4√2·α₁)²`, positive under the
smallness threshold `α₁ < √(γ₀/96)` (`96·α₁² ≤ γ₀` ⟺ `4√2·α₁ ≤ √(γ₀ − 64·α₁²)`).

## HONEST SCOPE (§LEAN-D / no-success-lie) — READ THIS

* This is the regular-`U` coercivity of the LEADING covariant term `deltaJ(U) = ‖D_U A‖²` on
  `ker Q₁(U) ∩ axial-gauge`, SINGLE SCALE. The two smallness hypotheses (`hthr`, `hsmall`) are the
  exact `α₁`-threshold, stated — not hidden.
* **`γ''` and `C_Q = 8/√ell` are EXPLICIT and `k`-INDEPENDENT** (`γ₀ = (1/108)(1/2⁴)` is a literal,
  `α₁ = frobSupBond U` carries no RG step `k`). This is the whole point.
* **`[UNIF-ALPHA]`** — `k`-uniformity across scales is NOT a further theorem here: it is exactly the
  standing regularity hypothesis that `sup_b ‖U_k b − 1‖` is uniformly small in `k` (Bałaban's
  scale-adapted (3.35)–(3.36)). "Regular `U`" SUPPLIES it by definition; a single scale carries no `k`.
* **NOT the full `C*Δ_kC ≥ γ₀`.** That target additionally needs the `C`-reparametrization wiring and
  the fluctuation-subspace bridge (both separately NAMED residuals). This brick is the `deltaJ(U)`
  leading-term coercivity on `ker Q₁(U)`, which those steps consume — it does not close them.
* LAW-19: every ingredient is imported and reused; nothing re-derived. **ISLAND** — not wired to
  `coerc_u_main` or a consumed spine declaration.
* ✅ **NON-VACUITY PROVED — `[REGU-DOMAIN-NONVAC]` RESOLVED (2026-07-26).** The `∀ A` domain here is
  `axial-gauge ∩ ker Q₁(U)` under `hthr`/`hsmall`. It is **NOT `{0}`**:
  `Balaban/RegularUDomainWitness.lean` exhibits an explicit NONZERO `witA` on `witL5` (`L μ = 5`, so
  `4 ≤ 5` ✓ and `2 ∣ 6` ✓, full `2³` blocks, no `blockOf` truncation) lying in
  `axial-gauge ∩ ker Q₁(trivialU)` — `regularU_domain_nonvacuous` — with `0 < bondEnergy witA`
  (`bondEnergy_witA_pos`) and the present theorem INSTANTIATED at it (`deltaJ_coercive_at_witA`), so the
  inequality here is NON-TRIVIAL, not merely non-vacuous. Construction: a ± cancelling pair of
  top-coordinate direction-`0` bonds (the earlier candidates failed — `generalWrapConfig` leaves
  `ker Q₁`, `checkerConfigSuTwo` fails the gauge). Both falsifiability controls FIRE: deleting the `−`
  bond breaks `ker Q₁` with the exact value `(1/8)•w` (`witASingle_not_mem_kerQ1`), and moving the
  support off the top coordinate breaks the gauge (`witALow_not_axial`) — so this is not a degenerate
  test point. `lean4checker` ACCEPTED.
  ✅ **`[REGU-DOMAIN-NONVAC-GENERALU]` ALSO CLOSED (2026-07-26)** — non-vacuity now holds for an
  ARBITRARY `U`, not just `trivialU`. `FullReparamC` §9 exhibits the NAMED (not existential) field
  `admissibleWitness U ell y := fullC U ell (dinvC U ell) (Pi.single (freeBond ell y) suTwoWitness)`
  and proves all three properties for EVERY `U`: `admissibleWitness_ne_zero`,
  `admissibleWitness_mem_kerQ` (every coarse bond), `admissibleWitness_axialGauge` (every staircase),
  needing only `2 ≤ ell`. The route is the one predicted here — the `C`-reparametrization, since
  `fullC B̃ ∈ ker Q₁(U)` BY CONSTRUCTION (`fullC_unconditional_mem_kerQ`, every `0 < ell` with
  `ell ∣ L μ + 1`, no assumed inverse) — so no `U=1`-only cancellation is needed.
  ⚠ Note what this does and does NOT give: it says the domain `V(Λ̃)` CONTAINS A NONZERO VECTOR at
  every `U`. It does NOT supply a positive lower bound on the form over all of `V(Λ̃)` — that is the
  coercivity itself, and remains this theorem's `hthr`/`hsmall`-conditional content.

`#print axioms` on every result below is `{propext, Classical.choice, Quot.sound}` — no `sorry`.
-/

namespace AdalyFormal.Balaban.RegularUCoercivityFull

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.SuTwoGeomU1
open AdalyFormal.Balaban.RegularUDirectCoercivity
open AdalyFormal.Balaban.RegularUQChain
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CoercivityTargetsCorrected
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the coarse-field `L²` inner product as an explicit squared-norm sum -/

/-- **`covCoarseBondInner B B = ∑_c ‖B c‖²`** — bridges the faithful coarse-field inner product
(`CovariantHjFaithful.covCoarseBondInner`, a `hsInner` sum) to the explicit `L²` energy that
`[QCHAIN-SENS]` controls, via `hsInner X X = ‖X‖²` (`SuTwoInner.inner_eq_hsInner`). -/
theorem covCoarseBondInner_self_eq_sum {ell : ℕ} (B : CoarseBond L ell → SuTwo) :
    covCoarseBondInner B B = ∑ c : CoarseBond L ell, ‖B c‖ ^ 2 := by
  unfold covCoarseBondInner
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← inner_eq_hsInner, real_inner_self_eq_norm_sq]

#print axioms covCoarseBondInner_self_eq_sum

/-! ## §2 — on `ker Q₁(U)`, the FLAT coarse-average energy is `O(α₁²)` small -/

/-- **The flat coarse energy is `O(α₁²)` on `ker Q₁(U)`.** For `A ∈ ker Q₁(U)` (`Q₁(U)A = 0`
pointwise, `hkerU`), the flat covariant coarse-average energy `‖Q₁(1)A‖²_{L²(coarse)}` is bounded by
`(64/ell)·α₁²·bondEnergy A`, `α₁ = frobSupBond U`: the drift equals `Q₁(1)A` on the target domain, so
`[QCHAIN-SENS]` (`coarseDriftEnergy_le`) applies verbatim. `k`-free, `C_Q² = 64/ell`. -/
theorem covCoarse_Q1flat_le_of_kerQU
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {ell : ℕ}
    (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hkerU : ∀ b : CoarseBond L ell, lineCoarseRestrictCov U ell A b = 0) :
    covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) ell A)
        (lineCoarseRestrictCovLM (trivialU L) ell A)
      ≤ (64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergy A := by
  rw [covCoarseBondInner_self_eq_sum]
  have hbridge : (∑ c : CoarseBond L ell, ‖lineCoarseRestrictCovLM (trivialU L) ell A c‖ ^ 2)
      = ∑ b : CoarseBond L ell,
          ‖lineCoarseRestrictCov (trivialU L) ell A b - lineCoarseRestrictCov U ell A b‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [lineCoarseRestrictCovLM_apply, hkerU c, sub_zero]
  rw [hbridge]
  exact coarseDriftEnergy_le U hell hdvd A

#print axioms covCoarse_Q1flat_le_of_kerQU

/-! ## §3 — THE REGULAR-`U` SINGLE-SCALE COERCIVITY on `ker Q₁(U) ∩ axial-gauge` (the deliverable) -/

/-- **THE REGULAR-`U` SINGLE-SCALE COERCIVITY of `deltaJ(U)` on `ker Q₁(U) ∩ axial-gauge`.**
For ANY background `U` and ANY su(2) field `A` on a compatible torus (`4 ≤ L μ`, `2 ∣ L μ + 1`) that
(i) satisfies the su(2) axial gauge `hadm` (`A` vanishes on every staircase `Γ_{y,x}`) and
(ii) lies in the target domain `ker Q₁(U)` (`hkerU : ∀ b, Q₁(U)A b = 0`), GIVEN the two `α₁`-smallness
hypotheses `hthr` (`64·α₁² ≤ γ₀`, so `γ' = γ₀ − 64·α₁² ≥ 0`) and `hsmall` (`4√2·α₁ ≤ √γ'`),

  `(√(γ₀ − 64·α₁²) − 4√2·α₁)² · bondEnergy A  ≤  deltaJ(U)A`,     `γ₀ = (1/108)(1/2⁴)`,

`α₁ = frobSupBond U = sup_b frobNorm(U b − 1)`. The coercivity constant
`γ'' = (√(γ₀ − 64·α₁²) − 4√2·α₁)²` is EXPLICIT and `k`-INDEPENDENT (single scale, `γ₀` literal), and
positive whenever `96·α₁² < γ₀`. See the module docstring for the honest scope: leading-term
`deltaJ(U)` coercivity, single scale, modulo `[UNIF-ALPHA]`; NOT yet the full `C*Δ_kC`. -/
theorem deltaJ_regularU_coercive_on_kerQU
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0)
    (hthr : 64 * frobSupBond U ^ 2 ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4))
    (hsmall : 0 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond U) :
    (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond U) ^ 2 * bondEnergy A
      ≤ dstarDQuadForm U A := by
  -- the U=1 additive base (needs only the axial gauge)
  have hbase := suTwoGeomAdditive_trivialU_of_admissible hL hdvd A hadm
  rw [SuTwoGeomAdditiveInequality, covPlaqInner_curl1_eq_deltaJ1,
    covBondInner_eq_bondEnergy] at hbase
  -- [QCHAIN-SENS] small on ker Q₁(U)
  have hQ := covCoarse_Q1flat_le_of_kerQU U (by norm_num) hdvd A hkerU
  simp only [Nat.cast_ofNat] at hbase hQ hthr hsmall ⊢
  set γ₀ : ℝ := (1 / 108) * (1 / (2 : ℝ) ^ 4) with hγ₀
  have hγ0 : 0 ≤ γ₀ := by rw [hγ₀]; positivity
  set γ' : ℝ := γ₀ - 64 * frobSupBond U ^ 2 with hγ'
  have hγ'0 : 0 ≤ γ' := by rw [hγ']; linarith [hthr]
  -- reduced U=1 coercivity at A: γ' · bondEnergy A ≤ deltaJ(1)A
  have hcoerc1 : γ' * bondEnergy A ≤ dstarDQuadForm (trivialU L) A := by
    rw [hγ']
    nlinarith [hbase, hQ,
      covCoarseBondInner_self_nonneg (lineCoarseRestrictCovLM (trivialU L) 2 A)]
  -- (b1) transfer
  have key := deltaJ_regularU_coercive_of_U1coercive U A γ' hγ'0 hcoerc1 hsmall
  rwa [hγ'] at key

#print axioms deltaJ_regularU_coercive_on_kerQU

end AdalyFormal.Balaban.RegularUCoercivityFull
