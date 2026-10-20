/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RegularUPerturbation
import AdalyFormal.Balaban.SuTwoGeomU1

set_option autoImplicit false

/-!
# `RegularUDirectCoercivity.lean` — the DIRECT single-scale regular-`U` coercivity TRANSFER of the
leading covariant term `deltaJ(U) = ‖D_U A‖²`, off the `U=1` base, and the (A)-vs-(B) resolution.

## ⚠ NOMENCLATURE (F6, 2026-07-26) — `deltaJ(U)` HERE IS THE CURL ENERGY,
**NOT** THE SCHUR COMPLEMENT

"`deltaJ(U)`" in this module's prose and declaration names
(`deltaJ_regularU_coercive_of_U1coercive`, `deltaJ_regularU_coercive_on_flatKernel`,
`covPlaqInner_curl1_eq_deltaJ1`, …) is a **local nickname** for

    CovariantHj.dstarDQuadForm U A
      := covPlaqInner (curlValueCovariant U A) (curlValueCovariant U A)   =   ‖∂^U A‖²

— the covariant curl / `D_U^*D_U` energy. That is literally what §3's
`covPlaqInner_curl1_eq_deltaJ1` says (`… = dstarDQuadForm (trivialU L) A`, by `rfl`), and it is
what every Lean statement in this module contains.

`dstarDQuadForm` is a **DIFFERENT DECLARATION** from
`CovariantHjFaithful.deltaJQuadFormCovFaithful`, the Schur complement / minimized curl energy
standing for CMP99b (3.156)'s `Δ_j`. The tree proves
`CStarDeltaKCCoercive.deltaJQuadFormCovFaithful_le_dstarDQuadForm`
(`deltaJQuadFormCovFaithful ≤ dstarDQuadForm`), so the lower bounds proved here do **not**
transfer to the Schur complement, and on the subspace `V` the latter is identically zero
(`deltaJQuadFormCovFaithful_eq_zero_of_mem_V`). The §"HONEST SCOPE" bullet "does NOT prove
`C*Δ_kC ≥ γ₀`" below is the correct reading; this banner names the two declarations that make it
so. Filed by the level-collapse sweep as F6 (`compute/level_collapse_sweep/FINDINGS.md`). Statements
clean, nickname corrected; no declaration renamed.

## THE STRATEGIC VERDICT (source-pinned, `compute/regularU_frontier/CMP99b_p428-40.png`, 600 dpi)

The dispatch's fork was: is the `k`-uniform coercivity `C*Δ_kC ≥ γ₀` proved by a **(A) DIRECT
single-scale perturbation** off `U=1`, or does it **(B) NEED the multi-scale random-walk expansion /
the `C`-chain sensitivity**? CMP99b p.428 ~~settles it VERBATIM~~ **ASSERTS the following. The quote
is verbatim; the claim inside it is not proved on that page** (see the strike below):

> "It is more convenient to work with the operator `C̃⁽ᵏ⁾(Λ)`, because it is defined by a positive
> definite operator `C*Δ_kC` **with a lower bound `γ₀ > 0` independent of `k` and `U`**. We have
> proved it in [4], Lemma 2.4, **for operators with `U = 1`. Localizing the operators in `Δ_k` and
> using the methods of Sect. B we can prove it for `C*Δ_kC` with an arbitrary configuration `U`
> satisfying (3.35), (3.36) with `Mα₀` sufficiently small.** This property, together with a uniform
> exponential decay of `C*Δ_kC` implies bounds and uniform exponential decay for `C̃⁽ᵏ⁾(Λ)` ... Now
> we are interested much more in generalized random walk expansions ..."

So the answer is **(A) for the coercivity LOWER BOUND**: the constant `γ₀` is ~~proved~~ **claimed by
Bałaban to be reachable** from `Lemma 2.4` (the `U=1` base — our
`SuTwoGeomU1.suTwoGeomAdditive_trivialU_of_admissible`, the su(2) lift of Bałaban's Lemma 2.4) PLUS
"the methods of Sect. B" (the SINGLE-STEP perturbation off `U=1`, CMP99b (3.82)–(3.86)).

**[HEDGE RESTORED 2026-07-29 — "settles"/"proved" overstated the source TWICE over.]**
(i) p.428's own sentence is *"…we **can prove it** for `C*Δ_kC` with an arbitrary configuration `U`…"*
— a statement of reachability, not a proof. Bałaban asserts; he does not carry it out there.
(ii) The route it points to is itself **conditional**. CMP99b p.407, verbatim from the page image:
*"Using the bounds (3.73), (3.77), (3.83) and **assuming that Theorem 3.3 holds for `G(U)`**, we get"*
→ (3.85). Theorem 3.3's general-`U` discharge is not completed on that page — p.407 opens
*"Let us consider a general configuration `U` satisfying the regularity condition"* and runs on past
the page break. So (3.85), the single-step sensitivity this file's route rests on, is printed under
an open hypothesis.

This does **not** invalidate anything below: nothing in this file derives (3.85) or Theorem 3.3, and
`deltaJ_regularU_coercive_of_U1coercive` takes the `U=1` coercivity as an **explicit hypothesis**
(`hcoerc1`) rather than importing it from Theorem 3.3. The correction is to the BILLING — this file
must not be read as saying the general-`U` lower bound is settled in the literature. It is not.
Standing rule: never build on deferred claims. Source: `corpus/pages/CMP99b_p407.md`.

The multi-scale random-walk expansion is invoked SEPARATELY and AFTERWARD, and
only for the propagator's uniform exponential DECAY / localization ("together with a uniform
exponential decay ...", "Now we are interested much more in ..."), **not for the coercivity constant
`γ₀`**. The prior tree note "the multi-scale expansion is genuinely required for the coercivity" is
CORRECTED by this read: it is required for decay, not for the lower bound.

## BUT the direct argument needs TWO single-scale sensitivities — the deltaJ brick supplies ONE

The object bounded below is `C*Δ_kC` on the subspace `{B = 0 on Λᶜ, B = 0 on Ax(y), Q₁B = 0}`,
reparametrized `B = CB̃` with `C` "an identity operator on almost all bonds, except the bonds `b₀`"
(p.428, verbatim) — a LOCAL, almost-identity map. The direct transfer therefore decomposes into:

* **(b1) `Δ_k(U)`-operator sensitivity** — `|deltaJ(U)A − deltaJ(1)A| ≤ C·α₁·√(bondEnergy A)·(√deltaJ(U)A + √deltaJ(1)A)`,
  `C = 4√2`, `k`-independent. **SUPPLIED**: `RegularUPerturbation.abs_deltaJ_sub_L2_le_sup`.
* **(b2) the `C`-map + `Q₁`-domain sensitivity** — the base coercivity holds on the FLAT axial gauge
  / `ker Q₁(1)`, but the target domain is `ker Q₁(U)` and the object carries `C`. Transferring across
  the domain move needs `‖Q₁(1)A − Q₁(U)A‖ ≤ C_Q·α₁·‖A‖` (and the `C`-map's local sensitivity). `C`
  is a local almost-identity, so this is again "the methods of Sect. B" — but it is a SECOND
  single-scale estimate, NOT the one the deltaJ brick provides. **NAMED RESIDUAL `[QCHAIN-SENS]`.**

**This file builds the (b1)-half rigorously as a coercivity TRANSFER**, and names (b2) precisely.
This resolves the fork: the remaining path is the local `Q₁`/`C` sensitivity `[QCHAIN-SENS]` +
uniform `α₁`-across-scales `[UNIF-ALPHA]`, NOT a multi-scale random-walk expansion for the constant.

## What is delivered (all `sorry`-free; `#print axioms` = `{propext, Classical.choice, Quot.sound}`)

1. **§1 `sq_lower_of_pert`** — the abstract quadratic-in-`√` real lemma: from `|x²−b²| ≤ 4√2·α·e·(x+b)`
   (`x,b,e,α ≥ 0`), `γ₀·e² ≤ b²` (the `U=1` coercivity), and `4√2·α ≤ √γ₀` (smallness), conclude
   `(√γ₀ − 4√2·α)²·e² ≤ x²`. This is the "solve the self-referential `√deltaJ(U)` on the RHS" step
   the dispatch flags, done in full: `x ≥ b − 4√2·α·e ≥ √γ₀·e − 4√2·α·e`.
2. **§2 `deltaJ_regularU_coercive_of_U1coercive`** — THE TRANSFER BRICK. For ANY regular `U` and ANY
   `A`, GIVEN the `U=1` leading coercivity `γ₀·bondEnergy A ≤ deltaJ(1)A` AT THAT `A` and
   `4√2·(sup_b frobNorm(U b − 1)) ≤ √γ₀`,
   `(√γ₀ − 4√2·sup_b frobNorm(U b − 1))²·bondEnergy A ≤ deltaJ(U)A`.
   Single scale — no `k`, no multi-scale expansion. The regular-`U` coercivity constant is
   `γ' = (√γ₀ − 4√2·α₁)²`, positive for `α₁ < √γ₀/(4√2)`.
3. **§3 bridges** — `covBondInner A A = bondEnergy A` and `covPlaqInner (curl₁ A)(curl₁ A) = deltaJ(1)A`,
   identifying the `U=1` additive base's energies with the perturbation brick's.
4. **§4 `deltaJ_regularU_coercive_on_flatKernel`** — the CONCRETE instantiation: on the FLAT kernel
   `ker Q₁(1)` (coarse-average energy `= 0`) with the su(2) axial gauge, the `U=1` additive base
   (`suTwoGeomAdditive_trivialU_of_admissible`) supplies the coercivity hypothesis, giving genuine
   regular-`U` leading coercivity `(√γ₀ − 4√2·α₁)²·bondEnergy A0 ≤ deltaJ(U)A0`, `γ₀ = (1/108)(1/2⁴)`.
   **On `ker Q₁(1)`, NOT `ker Q₁(U)`** — the honest domain, with `[QCHAIN-SENS]` naming the gap.

## HONEST SCOPE (§LEAN-D / no-success-lie)

* This is the **(b1)-half single-scale**. It does NOT prove `C*Δ_kC ≥ γ₀`. It proves the deltaJ
  operator transfer, CONDITIONAL on the `U=1` coercivity at the same `A`, single scale.
* **`[QCHAIN-SENS]`** (the `Q₁`/`C` domain-alignment sensitivity, uniform in `k`) and
  **`[UNIF-ALPHA]`** (`sup_b frobNorm(U b − 1) < √γ₀/(4√2)` UNIFORMLY across all scales `k`, from the
  scale-adapted regularity (3.35)–(3.36)) are NAMED, not built.
* §4's domain is `ker Q₁(1)` (flat), not the target `ker Q₁(U)`; closing that IS `[QCHAIN-SENS]`.
* LAW-19: every ingredient (`abs_deltaJ_sub_L2_le_sup`, `bondEnergy`, `frobSupBond`, `dstarDQuadForm`,
  `suTwoGeomAdditive_trivialU_of_admissible`, `covBondInner`, `covPlaqInner`) is imported and reused.
* **ISLAND.** Not wired to `coerc_u_main` or a consumed spine declaration.
-/

namespace AdalyFormal.Balaban.RegularUDirectCoercivity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.SuTwoGeomU1
open AdalyFormal.Balaban.CoercivityTargetsCorrected
open AdalyFormal.Balaban.CovU1Reduction
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LineIntegralCovariant

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the abstract quadratic-in-`√` transfer lemma (the "solve for `√deltaJ(U)`" step) -/

/-- **`sq_lower_of_pert`.** For nonnegative reals `x, b, e, γ₀, α` with
`|x² − b²| ≤ 4√2·α·e·(x + b)` (the single-scale perturbation), `γ₀·e² ≤ b²` (the base coercivity),
and `0 ≤ √γ₀ − 4√2·α` (smallness), one has `(√γ₀ − 4√2·α)²·e² ≤ x²`.

Mechanism: the perturbation gives `x ≥ b − 4√2·α·e` (from `(x+b)(x−b+4√2αe) ≥ 0`, `x+b ≥ 0`), the
base coercivity gives `√γ₀·e ≤ b`, so `x ≥ √γ₀·e − 4√2·α·e = (√γ₀−4√2α)·e ≥ 0`; square. -/
theorem sq_lower_of_pert
    (x b e γ₀ α : ℝ) (hx : 0 ≤ x) (hb : 0 ≤ b) (he : 0 ≤ e) (hγ0 : 0 ≤ γ₀) (hα : 0 ≤ α)
    (hpert : |x ^ 2 - b ^ 2| ≤ 4 * Real.sqrt 2 * α * e * (x + b))
    (hcoerc : γ₀ * e ^ 2 ≤ b ^ 2)
    (hsmall : 0 ≤ Real.sqrt γ₀ - 4 * Real.sqrt 2 * α) :
    (Real.sqrt γ₀ - 4 * Real.sqrt 2 * α) ^ 2 * e ^ 2 ≤ x ^ 2 := by
  set c := 4 * Real.sqrt 2 * α with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg (by positivity) hα
  -- perturbation lower half:  b − c·e ≤ x
  have hlow : -(c * e * (x + b)) ≤ x ^ 2 - b ^ 2 := (abs_le.mp hpert).1
  have hp : 0 ≤ (x + b) * (x - b + c * e) := by nlinarith [hlow]
  have hF2 : b - c * e ≤ x := by
    rcases (add_nonneg hx hb).lt_or_eq with hpos | h0
    · have hmul : (x + b) * 0 ≤ (x + b) * (x - b + c * e) := by rw [mul_zero]; exact hp
      have hxbce : 0 ≤ x - b + c * e := le_of_mul_le_mul_left hmul hpos
      linarith
    · -- 0 = x + b  ⟹  x = b = 0
      have hxz : x = 0 := le_antisymm (by linarith) hx
      have hbz : b = 0 := le_antisymm (by linarith) hb
      rw [hxz, hbz]; linarith [mul_nonneg hc0 he]
  -- base coercivity:  √γ₀·e ≤ b
  have hF1 : Real.sqrt γ₀ * e ≤ b := by
    have h1 : Real.sqrt (γ₀ * e ^ 2) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hcoerc
    rwa [Real.sqrt_mul hγ0, Real.sqrt_sq he, Real.sqrt_sq hb] at h1
  -- combine:  (√γ₀ − c)·e ≤ x, both sides ≥ 0, square
  have hmex : (Real.sqrt γ₀ - c) * e ≤ x := by
    have hexp : (Real.sqrt γ₀ - c) * e = Real.sqrt γ₀ * e - c * e := by ring
    rw [hexp]; linarith [hF1, hF2]
  have hme0 : 0 ≤ (Real.sqrt γ₀ - c) * e := mul_nonneg hsmall he
  calc (Real.sqrt γ₀ - c) ^ 2 * e ^ 2 = ((Real.sqrt γ₀ - c) * e) ^ 2 := by ring
    _ ≤ x ^ 2 := pow_le_pow_left₀ hme0 hmex 2

#print axioms sq_lower_of_pert

/-! ## §2 — THE TRANSFER BRICK: regular-`U` single-scale coercivity of `deltaJ(U)` off `U=1` -/

/-- **THE DIRECT SINGLE-SCALE REGULAR-`U` COERCIVITY TRANSFER.** For ANY background `U` and ANY field
`A`, GIVEN the `U=1` leading coercivity `γ₀·bondEnergy A ≤ deltaJ(1)A` AT THAT `A` (hypothesis
`hcoerc1`, supplied by the `U=1` base on the appropriate domain) and the smallness
`4√2·(sup_b frobNorm(U b − 1)) ≤ √γ₀` (`hsmall`),

  `(√γ₀ − 4√2·sup_b frobNorm(U b − 1))² · bondEnergy A  ≤  deltaJ(U)A`.

Single scale: the constant `4√2` is `k`-independent (`RegularUPerturbation` §12), no multi-scale
expansion. The regular-`U` coercivity constant is `γ' = (√γ₀ − 4√2·α₁)²`, positive for
`α₁ = sup_b frobNorm(U b − 1) < √γ₀/(4√2)`. This is the (A)-half the source (p.428) confirms is the
route for the coercivity LOWER BOUND (`Lemma 2.4` + "methods of Sect. B"). -/
theorem deltaJ_regularU_coercive_of_U1coercive
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (γ₀ : ℝ) (hγ0 : 0 ≤ γ₀)
    (hcoerc1 : γ₀ * bondEnergy A ≤ dstarDQuadForm (trivialU L) A)
    (hsmall : 0 ≤ Real.sqrt γ₀ - 4 * Real.sqrt 2 * frobSupBond U) :
    (Real.sqrt γ₀ - 4 * Real.sqrt 2 * frobSupBond U) ^ 2 * bondEnergy A
      ≤ dstarDQuadForm U A := by
  have hxsq : Real.sqrt (dstarDQuadForm U A) ^ 2 = dstarDQuadForm U A :=
    Real.sq_sqrt (dstarDQuadForm_nonneg U A)
  have hbsq : Real.sqrt (dstarDQuadForm (trivialU L) A) ^ 2 = dstarDQuadForm (trivialU L) A :=
    Real.sq_sqrt (dstarDQuadForm_nonneg (trivialU L) A)
  have hesq : Real.sqrt (bondEnergy A) ^ 2 = bondEnergy A :=
    Real.sq_sqrt (bondEnergy_nonneg A)
  have hpert : |Real.sqrt (dstarDQuadForm U A) ^ 2 - Real.sqrt (dstarDQuadForm (trivialU L) A) ^ 2|
      ≤ 4 * Real.sqrt 2 * frobSupBond U * Real.sqrt (bondEnergy A)
        * (Real.sqrt (dstarDQuadForm U A) + Real.sqrt (dstarDQuadForm (trivialU L) A)) := by
    rw [hxsq, hbsq]; exact abs_deltaJ_sub_L2_le_sup U A
  have key := sq_lower_of_pert
    (Real.sqrt (dstarDQuadForm U A)) (Real.sqrt (dstarDQuadForm (trivialU L) A))
    (Real.sqrt (bondEnergy A)) γ₀ (frobSupBond U)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hγ0 (frobSupBond_nonneg U)
    hpert
    (by rw [hesq, hbsq]; exact hcoerc1)
    hsmall
  rwa [hxsq, hesq] at key

#print axioms deltaJ_regularU_coercive_of_U1coercive

/-! ## §3 — bridges: the `U=1` additive base's energies = the perturbation brick's energies -/

/-- **`covBondInner A A = bondEnergy A`** — the `U=1` base's `⟨A,A⟩` is the perturbation brick's
`∑_b ‖A b‖²`, because the su(2) inner product IS `hsInner` (`SuTwoInner.inner_eq_hsInner`) and
`hsInner X X = ‖X‖²`. -/
theorem covBondInner_eq_bondEnergy (A : Bond L → SuTwo) :
    covBondInner A A = bondEnergy A := by
  unfold covBondInner bondEnergy
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← inner_eq_hsInner, real_inner_self_eq_norm_sq]

/-- **`covPlaqInner (curlCovariantLM (trivialU) A)(curlCovariantLM (trivialU) A) = deltaJ(1)A`** —
the `U=1` additive base's curl energy IS `dstarDQuadForm (trivialU)`, since `curlCovariantLM U`'s
`toFun` is `curlValueCovariant U` (`rfl`). -/
theorem covPlaqInner_curl1_eq_deltaJ1 (A : Bond L → SuTwo) :
    covPlaqInner (curlCovariantLM (trivialU L) A) (curlCovariantLM (trivialU L) A)
      = dstarDQuadForm (trivialU L) A := rfl

#print axioms covBondInner_eq_bondEnergy
#print axioms covPlaqInner_curl1_eq_deltaJ1

/-! ## §4 — CONCRETE: regular-`U` coercivity on the FLAT kernel `ker Q₁(1)`, from the `U=1` base -/

/-- **CONCRETE regular-`U` single-scale coercivity on `ker Q₁(1)`.** For a su(2) field `A0` on a
compatible torus that (i) satisfies the su(2) axial gauge `hadm` and (ii) has VANISHING flat
coarse-average energy `hQ1zero` (`A0 ∈ ker Q₁(1)`), the `U=1` additive base
(`suTwoGeomAdditive_trivialU_of_admissible`) gives `deltaJ(1)A0 ≥ γ₀·bondEnergy A0` with
`γ₀ = (1/108)(1/2⁴)`, and the §2 transfer then yields, for ANY background `U` with
`4√2·(sup_b frobNorm(U b − 1)) ≤ √γ₀`,

  `(√γ₀ − 4√2·sup_b frobNorm(U b − 1))² · bondEnergy A0  ≤  deltaJ(U)A0`.

**HONEST DOMAIN: `ker Q₁(1)` (flat), not the target `ker Q₁(U)`.** Closing the domain move is the
named residual `[QCHAIN-SENS]` (the `Q₁`/`C` sensitivity); `[UNIF-ALPHA]` is the uniform-`α₁`-across-
scales hypothesis needed for `k`-uniformity. -/
theorem deltaJ_regularU_coercive_on_flatKernel
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A0 : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A0 b = 0)
    (hQ1zero : covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) 2 A0)
        (lineCoarseRestrictCovLM (trivialU L) 2 A0) = 0)
    (hsmall : 0 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4))
        - 4 * Real.sqrt 2 * frobSupBond U) :
    (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4)) - 4 * Real.sqrt 2 * frobSupBond U) ^ 2
        * bondEnergy A0
      ≤ dstarDQuadForm U A0 := by
  set γ₀ : ℝ := (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) with hγ₀
  have hγ0 : 0 ≤ γ₀ := by rw [hγ₀]; positivity
  -- U=1 additive base
  have hbase := suTwoGeomAdditive_trivialU_of_admissible hL hdvd A0 hadm
  rw [SuTwoGeomAdditiveInequality] at hbase
  -- hbase : (2:ℕ):ℝ) * covCoarse + covPlaq(curl₁) ≥ γ₀ * covBond
  rw [hQ1zero, covPlaqInner_curl1_eq_deltaJ1, covBondInner_eq_bondEnergy] at hbase
  -- hbase : ((2:ℕ):ℝ) * 0 + deltaJ(1)A0 ≥ γ₀ * bondEnergy A0
  have hcoerc1 : γ₀ * bondEnergy A0 ≤ dstarDQuadForm (trivialU L) A0 := by
    have : ((2 : ℕ) : ℝ) * 0 + dstarDQuadForm (trivialU L) A0 = dstarDQuadForm (trivialU L) A0 := by
      ring
    rw [ge_iff_le, this] at hbase
    exact hbase
  exact deltaJ_regularU_coercive_of_U1coercive U A0 γ₀ hγ0 hcoerc1 hsmall

#print axioms deltaJ_regularU_coercive_on_flatKernel

end AdalyFormal.Balaban.RegularUDirectCoercivity
