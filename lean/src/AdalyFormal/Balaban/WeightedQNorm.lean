/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.QCLMNorm
import AdalyFormal.Balaban.ScaleTower
import AdalyFormal.Balaban.GammaRecursion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.longLine false

/-!
# `WeightedQNorm.lean` — the coarse-graining norm against **CMP99b (3.16)'s own weight**

`QCLMNorm.qCLM_opNorm_lt_one` put `‖qCLM U ell‖ ≤ √(ell⁻³) < 1` on the tree's carriers, and said
plainly what it did not settle: *"It says nothing about whether the UNWEIGHTED `PiLp 2` carriers …
are the source's carriers. CMP99b (3.16) p.393 carries a per-level measure factor `(L^jη)^{d−2}`
which this tree's carriers do not."* This module settles exactly that, and the answer is a NUMBER:

    with the source's weight, the one-step coarse-graining has norm  **`ell⁻¹`**  (at `d = 3`),
    attained exactly at the flat background — not `√(ell⁻³)`.

`ell⁻¹ < 1` for every admissible `ell ≥ 2`, so `GammaRecursion.not_uniformStepGamma_of_one_le`
does NOT fire on the faithful weighted carriers either. The route survives the weight.

## §0 — WHAT THE SOURCE SAYS, read from the page image by this lane

`corpus/renders/CMP99b_p393-05.png`.

~~(300 dpi; the same locus is also rendered at 400 dpi as `compute/a_renders/CMP99b_p393-05.png`
and transcribed identically in `Balaban/ConstantA.lean` — two independent reads, agreeing.)~~
**STRUCK by this lane's nested validator and re-measured by this lane: WRONG ON BOTH COUNTS.** The
two paths hold ONE file, byte-identical, `sha256
bfab586ad2ebd8dea88c5aa93bdabe4622bacc3c28535603b5f6af17ec71383d`, `2406×3806`, and the PNG's own
metadata reads `399.9992` dpi — so it is 400 dpi, not 300, and there are not two images. What IS
true, and all that is claimed here: **one image, transcribed independently by two lanes** (this one
and the `ConstantA` lane) with agreeing results. The independence is in the READERS, not in the
renders, and the resolution is 400.

CMP99b p.393, eq. (3.16), verbatim from that image:

> `⟨A, Q*aQA⟩ = Σ_{j=0}^{k} a Σ_{b ∈ Λ_j} (L^jη)^{d-2} |(Q_j(U)A)(b)|².`

and, on the same page, (3.15) `Q_j(U) = Q(Ū^{j-1})·…·Q(Ū)Q(U)` (so `Q_j` is a composition of `j`
ONE-STEP averagings), and the prose above (3.16): *"`Λ_j = Ω_j^{(j)} \ Ω_{j+1}^{(j)}`,
`j = 0,1,…,k`, … hence `Λ_j ⊂ T^{(j)}_{L^jη}`"* — `Λ_j` lives on the LEVEL-`j` lattice.

**Which side the weight sits on — the question that decides the ratio.** BOTH, because the weight
is a *per-level family* and it is carried by whichever level a field lives on. The textual anchor is
the `j = 0` term: `Q_0(U)` is the EMPTY composition in (3.15), i.e. the identity, and `Λ_0 ⊂ T_η`,
so that term of (3.16) reads `a · Σ_{b ∈ Λ_0} η^{d-2} |A(b)|²` — the FINE-side weighted square of
`A` itself. Level `j+1` carries `(L^{j+1}η)^{d-2}`. Hence a ONE-STEP `Q` has weight ratio

    `w_{j+1} / w_j = (L^{j+1}η)^{d-2} / (L^jη)^{d-2} = L^{d-2}`,  independent of `j` and of `η`.

**A fork that was checked and closed.** p.393's last line gives a *different* exponent for a
*different* object: *"The norm `‖·‖` in (3.17) is determined by the scalar product
`⟨λ, λ'⟩ = Σ_{x∈Ω_0} η^d tr λ(x)λ'(x)`"* — exponent `d`, on the GAUGE-FIXING scalar product for
site fields `λ`. That is not the averaging quadratic form. The averaging form for `λ` is (3.24)
p.394, `⟨λ, Q'*aQ'λ⟩ = Σ_j a_j Σ_{y∈Λ_j} (L^jη)^{d-2}|(Q'_j(U)λ)(y)|²` (transcribed in
`Balaban/ConstantA.lean`), which carries `d-2` like (3.16). So both averaging forms agree and
`qCLM`, a BOND/1-form averaging, takes `d-2`. The exponent `d` survives here only as §5's
deliberate mutation — and it is not a strawman number, it is printed on the same page.

## §0b — THE NORMALISATION, from the page that DEFINES it (CMP98 p.36, image-verified)

p.393 does **not** define the bond averaging — it says *"`Q(V)` is given by the explicit formula
(124) in [5]"*. Everything below rests on `QCLMNorm`'s unweighted `ell⁻³`, and that number is fixed
by that normalisation, so it was read rather than assumed. **This is the kill-or-survive fork:** had
the source normalisation been `L^{-d}` instead of `L^{-d-1}`, the unweighted square would be `ell⁻¹`
and the weighted one `ell^{d-2}·ell^{-1} = ell⁰ = 1` at `d = 3` — the no-go WOULD fire.

`[5]` is CMP98, *Averaging operations for lattice gauge theories*. Read from
`corpus/renders/CMP98_p36-20.png` (printed p.36 = pdf p.20; measured `2400×3645` at `399.9992` dpi,
`sha256 f801ece4b11f43d9f7e8489ddc7a11d563b8ed15f65c0877e22ea72658972ad4`), by this lane, AT THE
IMAGE — the machine draft `corpus/mathpix/balaban_CMP98_1985_averaging/normalized/p36.md` carries
its own line confidences `0.76`/`0.72` on exactly these two displays, so it is not citable alone and
was used only to LOCATE the equation. Verbatim from the image:

> `(Q(V₀)A)_c = Σ_{x∈B(c₋)} L^{-(d+1)} (R_{0,c₋}A)([x,x']) + …`  (124), main term
>
> `(Q₀A)_c = (Q_{V₀}A)_c = Σ_{x∈B(c₋)} L^{-(d+1)} (R_{0,c₋}A)([x,x'])`  (125)
>
> and it has an estimate  `|(Q₀A)_c| ≦ |A| < α₁`

So the normalisation is **`L^{-(d+1)}`**, which at `d = 3` is `ell⁻⁴` — exactly the `(1/ell⁴)`
prefactor of `LineIntegralCovariant.lineCoarseRestrictCov`. The count matches term for term:
`|B(c₋)| = L^d` sites times the `L` fine bonds of the segment `[x,x']` is `L^{d+1}` terms at weight
`L^{-(d+1)}`, so the weights sum to `1` — the sup-norm estimate `|(Q₀A)_c| ≦ |A|` is the source
stating exactly that. `source_normalisation_sums_to_one` below is that count as a theorem, over
`QCLMNorm.card_blockIdx`'s `ell⁴`. The dangerous alternative is excluded by the page.

## §1 — the result

`levelWeight ell η d j = ((ell:ℝ)^j * η)^(d-2)` is `ScaleTower`'s existing encoding of (3.16)'s
weight (LAW-19: imported, not rebuilt). `fineNormSq`/`coarseNormSq` are (3.16)-SHAPED — a weight
times a sum of squared magnitudes over a level's index set — and `fineNormSq_eq`/`coarseNormSq_eq`
identify them with `w · ‖·‖²` as a THEOREM, not by definition.

* `weighted_norm_sq_le` — `coarseNormSq w₁ (Q A) ≤ (ell:ℝ)^(d-5) · fineNormSq w₀ A`, any `U`, any
  `d : ℤ`, any base spacing `η > 0`. The exponent bookkeeping is
  `ell^(d-2) · ell^(-3) = ell^(d-5)`: the source's weight ratio against §6's `ell⁻³`.
* `weighted_norm_sq_eq_trivialU` — EQUALITY at `U = 1` on the constant field, so
  `(ell:ℝ)^(d-5)` is not an upper estimate but the value; `weighted_sharp_trivialU` states it as a
  best-constant claim (`WeightedRatioBound c → ell^(d-5) ≤ c`).
* `weighted_pointwise_le` / `weighted_pointwise_eq_trivialU` — the un-squared form, so the constant
  is literally the `q` of the bridge's `hQ : ‖Qx‖ ≤ q‖x‖` read in the weighted norms.
* At the tree's dimension `d = 3`: `weighted_const_three : (ell:ℝ)^((3:ℤ)-5) = 1/(ell:ℝ)^2`, so the
  weighted `q` is `1/ell`, and `1/ell < 1` for `ell ≥ 2`.

**`η` never appears in the answer** (`weighted_const_eta_free`): the base spacing cancels in the
ratio. The answer depends only on `ell` and on the exponent.

## §2 — the verdict, composed with the no-go

`GammaRecursion.not_uniformStepGamma_of_one_le` needs `1 ≤ q`. At `d = 3` the weighted `q` is
`1/ell ≤ 1/2`, so it does not fire, and the other branch does:
`weighted_uniformStepGamma_three` produces `UniformStepGamma δ (1/ell)` for every `γ₀ > 0` and
`δ ≤ γ₀(1 − ell⁻²)`. At `ell = 2` the weighted `q` is EXACTLY `1/2`, which is exactly the `q` of
`GammaRecursion`'s own concrete must-not-fire control `uniformStepGamma_half_one` — reused rather
than re-proved.

## §3 — the threshold, and why the direction of the weight does not decide it

`weighted_lt_one_iff_lt_five`: `(ell:ℝ)^(d-5) < 1 ↔ d < 5`, for `ell ≥ 2`. The source's `d = 3` is
two clear of the threshold. **The weight would have to be `ell³ = ell^{d}` per step, not
`ell^{d-2} = ell`, to reach `1`** — i.e. only an exponent of `3` or more kills.

This is why `weighted_inverted_direction_still_lt_one` matters: had the weight direction been the
other way round (coarse weight in the denominator, ratio `ell^{-(d-2)}`), the constant would be
`ell^(-(d-2)-3) = ell^{-4}`, still `< 1`. So at `d = 3` the DIRECTION of the weight is not what
decides — the magnitude `|d-2| = 1 < 3` decides, either way. This is stated as a theorem rather
than left as a reassurance, because "the direction is what decides the ratio" was the working
hypothesis this lane was dispatched under and it is FALSE at `d = 3`.

## §4/§5 — controls

* **MUST-NOT-FIRE, weight ≡ 1.** `ScaleTower.levelWeight_two` gives weight `1` at `d = 2`, and
  `unweighted_recovered_from_weighted` DERIVES `QCLMNorm.qCLM_norm_sq_le`'s statement
  (`‖QA‖² ≤ ell⁻³‖A‖²`) from `weighted_norm_sq_le` at `d = 2`. The weighted machinery degenerates
  to the unweighted one exactly when the weight degenerates, and to nothing else.
* **MUST-FIRE on the exponent.** `weighted_nogo_fires_at_exponent_five`: mutate the weight exponent
  `d-2 ↦ 3` (i.e. `d ↦ 5`, the exponent `d` that p.393's *other* scalar product carries) and the
  constant becomes exactly `1` (`weighted_const_five`), sharply (`weighted_sharp_trivialU`), and
  `GammaRecursion.not_uniformStepGamma_one_of_pos_delta` DOES fire: `¬ UniformStepGamma δ 1` for
  every `δ > 0`. At `d = 6` the constant exceeds `1` and `not_uniformStepGamma_of_one_lt` fires.
  So the verdict is not insensitive to the exponent — it is decided by it.
* **MUST-FIRE on the operator.** `summing_variant_weighted_not_le`: delete `qCLM`'s `(1/ell⁴)`
  normalisation and nothing else (`QCLMNorm.qSumCLM`) and the weighted bound at `d = 3` becomes
  FALSE. So `weighted_norm_sq_le` is not algebraically forced — it is a fact about this operator.
* **NON-VACUITY.** `fineNormSq_constWitness_pos`: the fine weighted norm of the witness at which
  sharpness is proved is strictly positive, so the equality is not `0 = 0`.

## §6 — scope, stated and not hidden

1. `Λ_j` in (3.16) is `Ω_j^{(j)} \ Ω_{j+1}^{(j)}`, a difference of nested domains; this tree's
   carriers are the WHOLE level-`j` torus. What is established here is the source's weight applied
   to the tree's carriers — which is the question `QCLMNorm`'s §"What this does NOT claim" asked.

   ~~A restriction to a `Λ_j` would only DELETE nonnegative terms from both sides.~~ **STRUCK by
   this lane before shipping: that is FALSE and it is the exact §S83 defect.** Deleting terms from
   both sides of an inequality does not preserve it. §6b replaces the hand-wave with two theorems,
   which split the claim along the only line where it is true:
   * `weighted_norm_sq_le_on_coarse_subset` — restricting the COARSE sum to ANY `S ⊆ CoarseBond`
     (in particular to a `Λ_1`) IS free: it deletes nonnegative terms from the LHS only. PROVED.
   * `fine_restriction_not_free` — restricting the FINE sum is NOT free, and here is the witness:
     `deltaWitness` is supported on the single fine bond `((0,…,0), 0)`, so the fine sum over
     `univ.erase` that bond is exactly `0`, while the coarse coordinate at the coarse bond based at
     the same site is exactly `ell⁻⁴ ≠ 0`. A fine bond a `Λ_0` omits is still read by a coarse bond
     in `Λ_1`. PROVED, with the explicit witness — not asserted.
   So the honest scope is: **the bound holds for the FULL fine norm against ANY coarse subset**,
   and a genuinely `Λ_0`-restricted fine norm would need a separate hypothesis this tree does not
   have (no fine mass outside `Λ_0` feeding `Λ_1`), which the witness shows is not automatic.
2. (3.16) is a `Σ_j` over one fixed `A`, not a one-step operator norm. What it licenses directly is
   *"a level-`j` field carries weight `(L^jη)^{d-2}`"* — the `j = 0`/`Q_0 = id` argument in §0 is
   the anchor. Applying that per-level weight to a one-step `Q : level 0 → level 1` is the reading,
   and it is stated as a reading.
3. The operator is this tree's `d = 3` one (`Fin 3`), and `‖Q‖²_unweighted = ell⁻³` is its number.
   `d` here varies the WEIGHT EXPONENT only. `weighted_exponent_arithmetic_general_d` records the
   fact that in a genuinely `d`-dimensional theory (where the unweighted square would be `ell^{-d}`)
   the weighted square would be `ell^{-2}` in EVERY dimension — as pure exponent arithmetic, never
   as an operator bound, because no `d`-dimensional operator exists in this tree.
-/

namespace AdalyFormal.Balaban.WeightedQNorm

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration
  PeriodicLatticeSite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (RMap suTwoWitness)
open AdalyFormal.Balaban.BridgeInverse (qCLM qCLM_apply CoarseFnL2 bondDelta siteZeroMem
  witL5_dvd_two witL5_wide_two)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.FaithfulCoercivitySU2 (norm_RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercivityRegular (curvedRegularU)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.QCLMNorm (norm_sq_pilp qCLM_norm_sq_le constWitness norm_constWitness_sq
  norm_qCLM_trivialU_constWitness_sq card_bond_eq deltaWitness norm_deltaWitness norm_suTwoWitness
  norm_qCLM_deltaWitness qSumCLM lineCoarseRestrictCov_bondDelta)
open AdalyFormal.Balaban (levelWeight levelSpacing levelWeight_two levelWeight_three
  levelSpacing_pos)
open AdalyFormal.Balaban.GammaRecursion (UniformStepGamma uniformStepGamma_of_lt_one
  uniformStepGamma_half_one not_uniformStepGamma_of_one_lt
  not_uniformStepGamma_one_of_pos_delta)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the (3.16)-shaped weighted squares

Defined as the SOURCE writes them: a weight times `Σ |·|²` over a level's index set. That
`fineNormSq w A = w * ‖A‖²` is then a theorem (`fineNormSq_eq`), not a definition — so the objects
below are the source's shape and the `PiLp` identification is proved. -/

/-- `(3.16)`'s level-`j` summand shape on the FINE (level-`0`) bond carrier:
`w · Σ_{b} |A(b)|²`. -/
noncomputable def fineNormSq (w : ℝ) (A : BondFnL2 L) : ℝ :=
  w * ∑ b : Bond L, ‖WithLp.ofLp A b‖ ^ 2

/-- `(3.16)`'s level-`j` summand shape on the COARSE (level-`1`) bond carrier. -/
noncomputable def coarseNormSq {ell : ℕ} (w : ℝ) (B : CoarseFnL2 L ell) : ℝ :=
  w * ∑ c : CoarseBond L ell, ‖WithLp.ofLp B c‖ ^ 2

theorem fineNormSq_eq (w : ℝ) (A : BondFnL2 L) : fineNormSq w A = w * ‖A‖ ^ 2 := by
  rw [fineNormSq, norm_sq_pilp]

theorem coarseNormSq_eq {ell : ℕ} (w : ℝ) (B : CoarseFnL2 L ell) :
    coarseNormSq w B = w * ‖B‖ ^ 2 := by
  rw [coarseNormSq, norm_sq_pilp]

theorem fineNormSq_nonneg {w : ℝ} (hw : 0 ≤ w) (A : BondFnL2 L) : 0 ≤ fineNormSq w A := by
  rw [fineNormSq_eq]; positivity

/-- **THE SOURCE'S NORMALISATION, as a count (§0b).** CMP98 (125) averages with weight `L^{-(d+1)}`
over `|B(c₋)| · L = L^{d+1}` terms, so the weights sum to `1`. At `d = 3` that is `ell⁻⁴` over the
`ell⁴` pairs `QCLMNorm.card_blockIdx` counts — the tree's operator carries the source's
normalisation, and the sup-norm estimate `|(Q₀A)_c| ≦ |A|` printed under (125) is this identity. -/
theorem source_normalisation_sums_to_one {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    (1 / (ell : ℝ) ^ 4) * ((AdalyFormal.Balaban.QCLMNorm.blockIdx y ell).card : ℝ) = 1 := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hne : ((ell : ℝ)) ≠ 0 := ne_of_gt hellR
  rw [AdalyFormal.Balaban.QCLMNorm.card_blockIdx hdvd hy]
  push_cast
  field_simp

/-! ## §2 — the weight ratio: `ell^(d-2)` per step, independent of the level and of `η` -/

/-- The level-`j` weight is positive whenever the spacing is. -/
theorem levelWeight_pos {ell : ℕ} {η : ℝ} (hell : 0 < ell) (hη : 0 < η) (d : ℤ) (j : ℕ) :
    0 < levelWeight ell η d j :=
  zpow_pos (levelSpacing_pos hell hη j) _

/-- **THE RATIO.** One coarse-graining step multiplies (3.16)'s weight by `ell^(d-2)`, whatever the
level and whatever the base spacing `η`. No hypotheses: `mul_zpow` holds in `ℝ` at every base. -/
theorem levelWeight_succ (ell : ℕ) (η : ℝ) (d : ℤ) (j : ℕ) :
    levelWeight ell η d (j + 1) = (ell : ℝ) ^ (d - 2) * levelWeight ell η d j := by
  show ((ell : ℝ) ^ (j + 1) * η) ^ (d - 2) = (ell : ℝ) ^ (d - 2) * ((ell : ℝ) ^ j * η) ^ (d - 2)
  rw [pow_succ, mul_comm ((ell : ℝ) ^ j) (ell : ℝ), mul_assoc, mul_zpow]

/-- The one-step ratio spelled out for the pair `(level 0, level 1)` that `qCLM` connects. -/
theorem levelWeight_one_eq (ell : ℕ) (η : ℝ) (d : ℤ) :
    levelWeight ell η d 1 = (ell : ℝ) ^ (d - 2) * levelWeight ell η d 0 :=
  levelWeight_succ ell η d 0

/-- **THE RATIO IS THE SAME AT EVERY LEVEL.** This is what makes the constant `k`-UNIFORM rather
than a per-level constant: `GammaRecursion.gammaSeq` iterates a SINGLE `q`, so a `j`-dependent ratio
would make every `∀ k` statement about the iterate a different recursion at each step. -/
theorem weighted_ratio_uniform_in_level {ell : ℕ} {η : ℝ} (hell : 0 < ell) (hη : 0 < η) (d : ℤ)
    (j : ℕ) :
    levelWeight ell η d (j + 1) / levelWeight ell η d j = (ell : ℝ) ^ (d - 2) := by
  rw [levelWeight_succ, mul_div_assoc, div_self (ne_of_gt (levelWeight_pos hell hη d j)), mul_one]

/-! ## §3 — THE BOUND -/

/-- `a ^ (−n) = 1/aⁿ`, the one `zpow`↔`pow` bridge every explicit constant below needs. Proved once
rather than re-derived at each instantiation. -/
theorem zpow_neg_natCast_eq (a : ℝ) (n : ℕ) : a ^ (-(n : ℤ)) = 1 / a ^ n := by
  rw [zpow_neg, zpow_natCast, one_div]

/-- The constant: the weight ratio `ell^(d-2)` against `QCLMNorm`'s unweighted `ell⁻³`. -/
theorem weighted_const_eq {ell : ℕ} (hell : 0 < ell) (d : ℤ) :
    (ell : ℝ) ^ (d - 2) * (1 / (ell : ℝ) ^ 3) = (ell : ℝ) ^ (d - 5) := by
  have hne : ((ell : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    exact ne_of_gt this
  have h3 : (1 : ℝ) / (ell : ℝ) ^ 3 = (ell : ℝ) ^ (-3 : ℤ) := by
    rw [zpow_neg, zpow_ofNat]; simp
  rw [h3, ← zpow_add₀ hne]
  ring_nf

/-- **THE WEIGHTED BOUND.** With CMP99b (3.16)'s per-level weight on BOTH carriers, the tree's
coarse-graining satisfies `‖QA‖²_w ≤ ell^(d-5) ‖A‖²_w`, at EVERY background `U`, every admissible
`ell`, every dimension exponent `d : ℤ` and every base spacing `η > 0`. -/
theorem weighted_norm_sq_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {η : ℝ} (hη : 0 < η) (d : ℤ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : BondFnL2 L) :
    coarseNormSq (levelWeight ell η d 1) (qCLM U ell A)
      ≤ (ell : ℝ) ^ (d - 5) * fineNormSq (levelWeight ell η d 0) A := by
  have hw0 : 0 < levelWeight ell η d 0 := levelWeight_pos hell hη d 0
  have hw1 : levelWeight ell η d 1 = (ell : ℝ) ^ (d - 2) * levelWeight ell η d 0 :=
    levelWeight_one_eq ell η d
  have hbase := qCLM_norm_sq_le hell hdvd U A
  rw [coarseNormSq_eq, fineNormSq_eq, hw1]
  have hpos : (0 : ℝ) < (ell : ℝ) ^ (d - 2) * levelWeight ell η d 0 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    exact mul_pos (zpow_pos this _) hw0
  calc (ell : ℝ) ^ (d - 2) * levelWeight ell η d 0 * ‖qCLM U ell A‖ ^ 2
      ≤ (ell : ℝ) ^ (d - 2) * levelWeight ell η d 0 * ((1 / (ell : ℝ) ^ 3) * ‖A‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbase (le_of_lt hpos)
    _ = ((ell : ℝ) ^ (d - 2) * (1 / (ell : ℝ) ^ 3)) * (levelWeight ell η d 0 * ‖A‖ ^ 2) := by ring
    _ = (ell : ℝ) ^ (d - 5) * (levelWeight ell η d 0 * ‖A‖ ^ 2) := by
        rw [weighted_const_eq hell d]

/-- **(3.16)'s OVERALL CONSTANT `a` CANCELS.** (3.16) reads `Σ_j a Σ_{b∈Λ_j} (L^jη)^{d-2}|·|²` with
a single unsubscripted `a` at every `j` (`Balaban/ConstantA.lean`'s image-verified reading). A common
nonnegative factor on both levels leaves the ratio constant untouched, so dropping `a` from the two
weighted squares below is not a simplification that could move the number. -/
theorem overall_constant_cancels {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {η : ℝ} (hη : 0 < η) (d : ℤ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {a : ℝ} (ha : 0 ≤ a)
    (A : BondFnL2 L) :
    a * coarseNormSq (levelWeight ell η d 1) (qCLM U ell A)
      ≤ (ell : ℝ) ^ (d - 5) * (a * fineNormSq (levelWeight ell η d 0) A) := by
  calc a * coarseNormSq (levelWeight ell η d 1) (qCLM U ell A)
      ≤ a * ((ell : ℝ) ^ (d - 5) * fineNormSq (levelWeight ell η d 0) A) :=
        mul_le_mul_of_nonneg_left (weighted_norm_sq_le hell hdvd hη d U A) ha
    _ = (ell : ℝ) ^ (d - 5) * (a * fineNormSq (levelWeight ell η d 0) A) := by ring

/-- **`η` DOES NOT APPEAR IN THE ANSWER.** The constant `ell^(d-5)` carries no base spacing; the
`η`'s cancel in the ratio. Stated as a theorem because a spacing leaking into an operator norm
would be a defect, and the numeric exploration asserted this too. -/
theorem weighted_const_eta_free {ell : ℕ} (η η' : ℝ) (d : ℤ) :
    levelWeight ell η d 1 / levelWeight ell η d 0
      = levelWeight ell η' d 1 / levelWeight ell η' d 0
    ∨ levelWeight ell η d 0 = 0 ∨ levelWeight ell η' d 0 = 0 := by
  by_cases h : levelWeight ell η d 0 = 0
  · exact Or.inr (Or.inl h)
  by_cases h' : levelWeight ell η' d 0 = 0
  · exact Or.inr (Or.inr h')
  left
  rw [levelWeight_one_eq, levelWeight_one_eq, mul_div_assoc, mul_div_assoc,
    div_self h, div_self h']

/-! ## §4 — SHARPNESS: the bound is the VALUE, attained at the flat background -/

/-- The fine weighted square of the constant witness is `w₀ · #Bond`. -/
theorem fineNormSq_constWitness (w : ℝ) (L : PeriodicLatticeExtent) :
    fineNormSq w (constWitness L) = w * (Fintype.card (Bond L) : ℝ) := by
  rw [fineNormSq_eq, norm_constWitness_sq]

/-- **NON-VACUITY of the sharpness witness.** -/
theorem fineNormSq_constWitness_pos {ell : ℕ} {η : ℝ} (hell : 0 < ell) (hη : 0 < η) (d : ℤ)
    (L : PeriodicLatticeExtent) :
    0 < fineNormSq (levelWeight ell η d 0) (constWitness L) := by
  rw [fineNormSq_constWitness]
  have h1 : 0 < levelWeight ell η d 0 := levelWeight_pos hell hη d 0
  have h2 : (0 : ℝ) < (Fintype.card (Bond L) : ℝ) := by
    have : 0 < Fintype.card (Bond L) := Fintype.card_pos
    exact_mod_cast this
  exact mul_pos h1 h2

/-- **EQUALITY at `U = 1` on the constant field.** So `ell^(d-5)` is not an estimate: it is the
value of the weighted ratio. Uses `QCLMNorm`'s exact evaluations plus the block tiling count
`#Bond = ell³ · #CoarseBond`. -/
theorem weighted_norm_sq_eq_trivialU {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {η : ℝ} (d : ℤ) :
    coarseNormSq (levelWeight ell η d 1) (qCLM (trivialU L) ell (constWitness L))
      = (ell : ℝ) ^ (d - 5) * fineNormSq (levelWeight ell η d 0) (constWitness L) := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hne : ((ell : ℝ)) ≠ 0 := ne_of_gt hellR
  rw [coarseNormSq_eq, norm_qCLM_trivialU_constWitness_sq hell hdvd,
    fineNormSq_constWitness, card_bond_eq hell hdvd, levelWeight_one_eq]
  have hcast : ((ell ^ 3 * Fintype.card (CoarseBond L ell) : ℕ) : ℝ)
      = (ell : ℝ) ^ (3 : ℕ) * (Fintype.card (CoarseBond L ell) : ℝ) := by push_cast; ring
  rw [hcast]
  have hsplit : (ell : ℝ) ^ (d - 5) * (levelWeight ell η d 0
        * ((ell : ℝ) ^ (3 : ℕ) * (Fintype.card (CoarseBond L ell) : ℝ)))
      = ((ell : ℝ) ^ (d - 5) * (ell : ℝ) ^ (3 : ℕ))
        * (levelWeight ell η d 0 * (Fintype.card (CoarseBond L ell) : ℝ)) := by ring
  rw [hsplit]
  have hexp : (ell : ℝ) ^ (d - 5) * (ell : ℝ) ^ (3 : ℕ) = (ell : ℝ) ^ (d - 2) := by
    rw [← zpow_natCast (ell : ℝ) 3, ← zpow_add₀ hne]
    ring_nf
  rw [hexp]
  ring

/-- The predicate *"`c` is an admissible weighted ratio constant for `Q` at background `U`"* —
exactly the shape the bridge's `hQ` consumes, squared. -/
def WeightedRatioBound (L : PeriodicLatticeExtent) (ell : ℕ) (η : ℝ) (d : ℤ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (c : ℝ) : Prop :=
  ∀ A : BondFnL2 L, coarseNormSq (levelWeight ell η d 1) (qCLM U ell A)
    ≤ c * fineNormSq (levelWeight ell η d 0) A

theorem weightedRatioBound_holds {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {η : ℝ} (hη : 0 < η) (d : ℤ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    WeightedRatioBound L ell η d U ((ell : ℝ) ^ (d - 5)) :=
  fun A => weighted_norm_sq_le hell hdvd hη d U A

/-- **BEST CONSTANT.** At the flat background no smaller constant works, so `ell^(d-5)` is exactly
the squared weighted operator norm there. -/
theorem weighted_sharp_trivialU {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {η : ℝ} (hη : 0 < η) (d : ℤ) {c : ℝ}
    (hc : WeightedRatioBound L ell η d (trivialU L) c) :
    (ell : ℝ) ^ (d - 5) ≤ c := by
  have hpos := fineNormSq_constWitness_pos (L := L) hell hη d
  have h := hc (constWitness L)
  rw [weighted_norm_sq_eq_trivialU hell hdvd d] at h
  exact le_of_mul_le_mul_right (by linarith) hpos

/-! ## §5 — THE UN-SQUARED FORM: the `q` the bridge consumes -/

/-- `√(fineNormSq w A)` — the weighted norm itself. -/
noncomputable def fineNorm (w : ℝ) (A : BondFnL2 L) : ℝ := Real.sqrt (fineNormSq w A)

noncomputable def coarseNorm {ell : ℕ} (w : ℝ) (B : CoarseFnL2 L ell) : ℝ :=
  Real.sqrt (coarseNormSq w B)

/-- **`‖QA‖_w ≤ √(ell^(d-5)) · ‖A‖_w`** — the bridge's `hQ` shape, in the source's norms. -/
theorem weighted_pointwise_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {η : ℝ} (hη : 0 < η) (d : ℤ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : BondFnL2 L) :
    coarseNorm (levelWeight ell η d 1) (qCLM U ell A)
      ≤ Real.sqrt ((ell : ℝ) ^ (d - 5)) * fineNorm (levelWeight ell η d 0) A := by
  have h := weighted_norm_sq_le hell hdvd hη d U A
  rw [coarseNorm, fineNorm, ← Real.sqrt_mul (le_of_lt (by positivity : (0:ℝ) < (ell:ℝ) ^ (d-5)))]
  exact Real.sqrt_le_sqrt h

/-- Equality at the flat background, un-squared. -/
theorem weighted_pointwise_eq_trivialU {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {η : ℝ} (d : ℤ) :
    coarseNorm (levelWeight ell η d 1) (qCLM (trivialU L) ell (constWitness L))
      = Real.sqrt ((ell : ℝ) ^ (d - 5)) * fineNorm (levelWeight ell η d 0) (constWitness L) := by
  have h := weighted_norm_sq_eq_trivialU (L := L) hell hdvd (η := η) d
  rw [coarseNorm, fineNorm, ← Real.sqrt_mul (le_of_lt (by positivity : (0:ℝ) < (ell:ℝ) ^ (d-5))), h]

/-! ## §6 — AT THE TREE'S DIMENSION `d = 3`: the constant is `ell⁻¹` -/

/-- **THE NUMBER.** At `d = 3` the weighted squared constant is `ell⁻²`. -/
theorem weighted_const_three {ell : ℕ} : (ell : ℝ) ^ ((3 : ℤ) - 5) = 1 / (ell : ℝ) ^ 2 := by
  have h : ((3 : ℤ) - 5) = -((2 : ℕ) : ℤ) := by norm_num
  rw [h, zpow_neg_natCast_eq]

/-- `√(ell⁻²) = 1/ell` — the weighted operator norm at `d = 3` is `ell⁻¹`, NOT `√(ell⁻³)`. -/
theorem weighted_sqrt_const_three {ell : ℕ} (hell : 0 < ell) :
    Real.sqrt ((ell : ℝ) ^ ((3 : ℤ) - 5)) = 1 / (ell : ℝ) := by
  have hellR : (0 : ℝ) ≤ (ell : ℝ) := by positivity
  rw [weighted_const_three]
  simp only [one_div]
  rw [Real.sqrt_inv, Real.sqrt_sq hellR]

/-- **THE WEIGHTED BOUND AT `d = 3`, spelled out.** -/
theorem weighted_norm_sq_le_three {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {η : ℝ} (hη : 0 < η)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : BondFnL2 L) :
    coarseNormSq (levelWeight ell η 3 1) (qCLM U ell A)
      ≤ (1 / (ell : ℝ) ^ 2) * fineNormSq (levelWeight ell η 3 0) A := by
  have h := weighted_norm_sq_le hell hdvd hη 3 U A
  rwa [weighted_const_three] at h

/-- **THE VERDICT AT `d = 3`.** For every admissible `ell ≥ 2`, the weighted `q` is `< 1`. -/
theorem weighted_q_three_lt_one {ell : ℕ} (hell : 2 ≤ ell) :
    Real.sqrt ((ell : ℝ) ^ ((3 : ℤ) - 5)) < 1 := by
  have hell0 : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  rw [weighted_sqrt_const_three hell0]
  rw [div_lt_one (by linarith)]
  linarith

/-- And it is not `0` — the operator does not vanish in the weighted norms either. -/
theorem weighted_q_three_pos {ell : ℕ} (hell : 0 < ell) :
    0 < Real.sqrt ((ell : ℝ) ^ ((3 : ℤ) - 5)) := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  rw [weighted_sqrt_const_three hell]
  positivity

/-! ## §6b — THE `Λ_j` SCOPE, as two theorems instead of a hand-wave (scope note 1)

(3.16) sums over `Λ_j = Ω_j^{(j)} \ Ω_{j+1}^{(j)}`, not over the whole level-`j` lattice. The first
draft of this module's scope note asserted that restricting to a `Λ_j` "would only delete
nonnegative terms from both sides". That is false — deleting terms from both sides of an inequality
preserves nothing. These two theorems say exactly which half is true and exhibit the counterexample
to the other half. -/

/-- **THE COARSE RESTRICTION IS FREE.** Restricting the coarse sum to any `S ⊆ CoarseBond` — a
`Λ_1` in particular — only deletes nonnegative terms from the LEFT, so the weighted bound survives
verbatim. -/
theorem weighted_norm_sq_le_on_coarse_subset {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {η : ℝ} (hη : 0 < η) (d : ℤ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (S : Finset (CoarseBond L ell)) (A : BondFnL2 L) :
    levelWeight ell η d 1 * ∑ c ∈ S, ‖WithLp.ofLp (qCLM U ell A) c‖ ^ 2
      ≤ (ell : ℝ) ^ (d - 5) * fineNormSq (levelWeight ell η d 0) A := by
  have hw1 : 0 < levelWeight ell η d 1 := levelWeight_pos hell hη d 1
  have hsub : ∑ c ∈ S, ‖WithLp.ofLp (qCLM U ell A) c‖ ^ 2
      ≤ ∑ c : CoarseBond L ell, ‖WithLp.ofLp (qCLM U ell A) c‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have hstep : levelWeight ell η d 1 * ∑ c ∈ S, ‖WithLp.ofLp (qCLM U ell A) c‖ ^ 2
      ≤ coarseNormSq (levelWeight ell η d 1) (qCLM U ell A) :=
    mul_le_mul_of_nonneg_left hsub (le_of_lt hw1)
  exact hstep.trans (weighted_norm_sq_le hell hdvd hη d U A)

/-- The exact coarse coordinate of `Q` on the single-fine-bond witness, at the coarse bond based at
that bond's own site: `ell⁻⁴`. `QCLMNorm` computed this inside `norm_qCLM_deltaWitness` but exported
only the resulting norm bound; the coordinate itself is what §6b's witness needs. -/
theorem qCLM_deltaWitness_coord {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖WithLp.ofLp (qCLM U ell (deltaWitness L))
        ((⟨(fun _ => 0 : PeriodicLatticeSite L), siteZeroMem L ell⟩ :
            {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), (0 : Fin 3))‖
      = 1 / (ell : ℝ) ^ 4 := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  rw [qCLM_apply]
  have hofLp : WithLp.ofLp (deltaWitness L)
      = bondDelta (((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) : Bond L)
          (suTwoWitness : SuTwo) := by
    rw [deltaWitness]
  rw [hofLp, lineCoarseRestrictCov_bondDelta hell hdvd hwide U (siteZeroMem L ell) (0 : Fin 3)
      (suTwoWitness : SuTwo), norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (ell : ℝ) ^ 4), norm_RMap, norm_suTwoWitness,
    mul_one]

/-- The witness has NO mass outside its own single fine bond. -/
theorem deltaWitness_sum_off_support (L : PeriodicLatticeExtent) :
    ∑ b ∈ (Finset.univ.erase (((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) : Bond L)),
        ‖WithLp.ofLp (deltaWitness L) b‖ ^ 2 = 0 := by
  classical
  refine Finset.sum_eq_zero fun b hb => ?_
  have hne : b ≠ (((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) : Bond L) :=
    Finset.ne_of_mem_erase hb
  simp [deltaWitness, bondDelta, hne]

/-- **THE FINE RESTRICTION IS NOT FREE — with the witness, not a caveat.** Take `Λ_0` to omit the
single fine bond `((0,…,0), 0)` and `Λ_1` to contain the coarse bond based at the same site. The
`Λ_0`-restricted fine weighted square is exactly `0`, while the `Λ_1`-restricted coarse weighted
square is `w₁ · ell⁻⁸ > 0`. So no bound of the form `coarse|_{Λ_1} ≤ c · fine|_{Λ_0}` can hold for
ANY finite `c`: a fine bond that `Λ_0` omits is still read by a coarse bond of `Λ_1`. -/
theorem fine_restriction_not_free {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    {η : ℝ} (hη : 0 < η) (d : ℤ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (c : ℝ) :
    ¬ (levelWeight ell η d 1
          * ∑ b ∈ ({((⟨(fun _ => 0 : PeriodicLatticeSite L), siteZeroMem L ell⟩ :
                {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), (0 : Fin 3))} :
              Finset (CoarseBond L ell)),
              ‖WithLp.ofLp (qCLM U ell (deltaWitness L)) b‖ ^ 2
        ≤ c * (levelWeight ell η d 0
          * ∑ b ∈ (Finset.univ.erase
                (((fun _ => 0 : PeriodicLatticeSite L), (0 : Fin 3)) : Bond L)),
              ‖WithLp.ofLp (deltaWitness L) b‖ ^ 2)) := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hw1 : 0 < levelWeight ell η d 1 := levelWeight_pos hell hη d 1
  have hcoarse : levelWeight ell η d 1
      * ∑ b ∈ ({((⟨(fun _ => 0 : PeriodicLatticeSite L), siteZeroMem L ell⟩ :
            {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell}), (0 : Fin 3))} :
          Finset (CoarseBond L ell)),
          ‖WithLp.ofLp (qCLM U ell (deltaWitness L)) b‖ ^ 2
      = levelWeight ell η d 1 * (1 / (ell : ℝ) ^ 4) ^ 2 := by
    rw [Finset.sum_singleton, qCLM_deltaWitness_coord hell hdvd hwide U]
  rw [hcoarse, deltaWitness_sum_off_support L, mul_zero, mul_zero]
  have : (0 : ℝ) < levelWeight ell η d 1 * (1 / (ell : ℝ) ^ 4) ^ 2 := by positivity
  linarith

/-! ## §7 — COMPOSITION WITH THE NO-GO -/

/-- **THE NO-GO DOES NOT FIRE, and the other branch does.** At `d = 3` the weighted `q = 1/ell` is
`< 1`, so `GammaRecursion.uniformStepGamma_of_lt_one` applies: a `k`-uniform positive floor exists
for every `γ₀ > 0` with `δ ≤ γ₀(1 − ell⁻²)`. -/
theorem weighted_uniformStepGamma_three {ell : ℕ} (hell : 2 ≤ ell) {γ₀ δ : ℝ} (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - (1 / (ell : ℝ)) ^ 2)) :
    UniformStepGamma δ (1 / (ell : ℝ)) := by
  have hell0 : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hq0 : (0 : ℝ) < 1 / (ell : ℝ) := by positivity
  have hq1 : (1 : ℝ) / (ell : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  exact uniformStepGamma_of_lt_one hq0 hq1 hγ hfix

/-- **AT THE DECISIVE PARAMETERS (`ell = 2`, the tree's own witness lattice).** The weighted `q` is
EXACTLY `1/2`, which is exactly the `q` of `GammaRecursion`'s own concrete must-not-fire control
`uniformStepGamma_half_one` (`δ = 1`, `γ₀ = 2`, iterates `2, 4, 12`). Reused, not re-proved. -/
theorem weighted_q_two_eq_half : Real.sqrt (((2 : ℕ) : ℝ) ^ ((3 : ℤ) - 5)) = 1 / 2 := by
  rw [weighted_sqrt_const_three (by norm_num)]
  norm_num

theorem weighted_uniformStepGamma_at_two : UniformStepGamma 1 (1 / 2) :=
  uniformStepGamma_half_one

/-- **THE STATEMENT THE DISPATCH ASKED FOR, as one theorem.** At the tree's dimension, at every
admissible block size, with CMP99b (3.16)'s own weight on both carriers: the coarse-graining norm
is strictly below `1`, hence `not_uniformStepGamma_of_one_le`'s hypothesis `1 ≤ q` FAILS and the
iterated-bridge route is NOT killed by the weight. -/
theorem weighted_route_survives {ell : ℕ} (hell : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {η : ℝ} (hη : 0 < η)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (∀ A : BondFnL2 L, coarseNorm (levelWeight ell η 3 1) (qCLM U ell A)
        ≤ (1 / (ell : ℝ)) * fineNorm (levelWeight ell η 3 0) A)
    ∧ (1 : ℝ) / (ell : ℝ) < 1 := by
  have hell0 : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  refine ⟨fun A => ?_, by rw [div_lt_one (by linarith)]; linarith⟩
  have h := weighted_pointwise_le hell0 hdvd hη 3 U A
  rwa [weighted_sqrt_const_three hell0] at h

/-! ## §7b — AT THE TREE'S ONE FULLY-CONSTRUCTED BRIDGE INSTANCE

`GammaRecursion.curvedRegularU_Q_decides_uniformity` reduces p.428's `k`-uniformity, along this
route, to the position of `‖qCLM curvedRegularU 2‖` relative to `1` — at `witL5`, `ell = 2`, a
background with genuine curvature. `QCLMNorm.qCLM_curvedRegularU_two_lt_one` answered it on the
UNWEIGHTED carriers (`≤ √(1/8)`). These are the same statements on the (3.16)-WEIGHTED carriers,
where the number is `1/2` — bigger, and still below `1`. -/

/-- **THE DECISIVE NUMBER, WEIGHTED, AT THE DECISIVE PARAMETERS.** -/
theorem weighted_curvedRegularU_two {η : ℝ} (hη : 0 < η) (A : BondFnL2 witL5) :
    coarseNorm (levelWeight 2 η 3 1) (qCLM curvedRegularU 2 A)
      ≤ (1 / 2 : ℝ) * fineNorm (levelWeight 2 η 3 0) A := by
  have h := weighted_pointwise_le (L := witL5) (ell := 2) (by norm_num) witL5_dvd_two hη 3
    curvedRegularU A
  rw [weighted_sqrt_const_three (by norm_num)] at h
  norm_num at h
  exact h

/-- **THE NO-GO'S HYPOTHESIS FAILS AT THOSE PARAMETERS.** `not_uniformStepGamma_of_one_le` needs
`1 ≤ q`; the weighted `q` here is `1/2`. Stated as the explicit negation so no reader has to
recompute it. -/
theorem weighted_curvedRegularU_two_nogo_hypothesis_fails : ¬ ((1 : ℝ) ≤ 1 / 2) := by norm_num

/-- **THE VALUE IS ATTAINED**: at the flat background on the same lattice and block size, the
weighted squared ratio is exactly `1/4`, so `1/2` is not a lossy estimate. -/
theorem weighted_trivialU_two_witL5_sharp {η : ℝ} :
    coarseNormSq (levelWeight 2 η 3 1) (qCLM (trivialU witL5) 2 (constWitness witL5))
      = (1 / 4 : ℝ) * fineNormSq (levelWeight 2 η 3 0) (constWitness witL5) := by
  have h := weighted_norm_sq_eq_trivialU (L := witL5) (ell := 2) (by norm_num) witL5_dvd_two
    (η := η) 3
  rw [weighted_const_three] at h
  norm_num at h
  exact h

/-- And no smaller constant is admissible there: `1/4` is the best constant, not an upper bound. -/
theorem weighted_trivialU_two_witL5_best {η : ℝ} (hη : 0 < η) {c : ℝ}
    (hc : WeightedRatioBound witL5 2 η 3 (trivialU witL5) c) : (1 / 4 : ℝ) ≤ c := by
  have h := weighted_sharp_trivialU (L := witL5) (ell := 2) (by norm_num) witL5_dvd_two hη 3 hc
  rw [weighted_const_three] at h
  norm_num at h
  exact h

/-! ## §8 — THE THRESHOLD, AND WHY THE DIRECTION DOES NOT DECIDE IT -/

theorem one_le_zpow_of_nonneg {a : ℝ} (ha : 1 ≤ a) {n : ℤ} (hn : 0 ≤ n) : 1 ≤ a ^ n := by
  lift n to ℕ using hn
  rw [zpow_natCast]
  exact one_le_pow₀ ha

theorem zpow_lt_one_of_neg {a : ℝ} (ha : 1 < a) {n : ℤ} (hn : n < 0) : a ^ n < 1 := by
  have hm : (0 : ℤ) ≤ -n := by omega
  have h1 : 1 ≤ a ^ (-n) := one_le_zpow_of_nonneg (le_of_lt ha) hm
  have h1' : 1 < a ^ (-n) := by
    lift (-n) to ℕ using hm with m hm'
    rw [zpow_natCast]
    have hmpos : 0 < m := by omega
    exact one_lt_pow₀ ha hmpos.ne'
  have hpos : (0 : ℝ) < a ^ (-n) := lt_trans zero_lt_one h1'
  have : a ^ n = (a ^ (-n))⁻¹ := by rw [zpow_neg, inv_inv]
  rw [this, inv_lt_one_iff₀]
  exact Or.inr h1'

/-- **THE THRESHOLD.** With block ratio `ell ≥ 2`, the weighted constant is `< 1` exactly when the
dimension exponent is below `5`. CMP99b's `d = 3` is two clear of it. -/
theorem weighted_lt_one_iff_lt_five {ell : ℕ} (hell : 2 ≤ ell) (d : ℤ) :
    (ell : ℝ) ^ (d - 5) < 1 ↔ d < 5 := by
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have ha : (1 : ℝ) < (ell : ℝ) := by linarith
  constructor
  · intro h
    by_contra hcon
    have hn : (0 : ℤ) ≤ d - 5 := by omega
    have := one_le_zpow_of_nonneg (le_of_lt ha) hn
    linarith
  · intro h
    exact zpow_lt_one_of_neg ha (by omega)

/-- **THE DIRECTION OF THE WEIGHT DOES NOT DECIDE THE VERDICT AT `d = 3`.** Had the ratio been
inverted — coarse weight in the denominator, `ell^{-(d-2)}` per step — the constant would be
`ell^(-(d-2)-3) = ell^{-4}`, still strictly below `1`. The magnitude `|d − 2| = 1` is three short of
the `3` needed to reach `1`, in either direction. -/
theorem weighted_inverted_direction_still_lt_one {ell : ℕ} (hell : 2 ≤ ell) :
    (ell : ℝ) ^ (-((3 : ℤ) - 2) - 3) < 1 ∧ (ell : ℝ) ^ (-((3 : ℤ) - 2) - 3) = 1 / (ell : ℝ) ^ 4 := by
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have ha : (1 : ℝ) < (ell : ℝ) := by linarith
  refine ⟨zpow_lt_one_of_neg ha (by norm_num), ?_⟩
  have h : (-((3 : ℤ) - 2) - 3) = -((4 : ℕ) : ℤ) := by norm_num
  rw [h, zpow_neg_natCast_eq]

/-- **EXPONENT ARITHMETIC ONLY (scope note 3).** In a genuinely `d`-dimensional theory the
unweighted squared norm of an `L^{-d-1}`-normalised block average would be `ell^{-d}`, and (3.16)'s
weight ratio `ell^{d-2}` would give `ell^{-2}` — the weighted norm `1/ell` in EVERY dimension. This
is recorded as arithmetic on exponents. It is NOT an operator bound: this tree has no
`d`-dimensional operator (`PeriodicLatticeSite : Fin 3 → …`), and nothing downstream may read this
declaration as one. -/
theorem weighted_exponent_arithmetic_general_d {ell : ℕ} (hell : 0 < ell) (d : ℤ) :
    (ell : ℝ) ^ (d - 2) * (ell : ℝ) ^ (-d) = (ell : ℝ) ^ (-2 : ℤ) := by
  have hne : ((ell : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    exact ne_of_gt this
  rw [← zpow_add₀ hne]
  ring_nf

/-! ## §9 — MUST-NOT-FIRE: at weight `≡ 1` the weighted result IS the unweighted one -/

/-- At `d = 2`, `ScaleTower.levelWeight_two` makes the weight identically `1`, and the two
(3.16)-shaped squares collapse to the plain `PiLp` squares. -/
theorem weighted_at_two_collapses {ell : ℕ} (η : ℝ) (A : BondFnL2 L)
    (B : CoarseFnL2 L ell) :
    fineNormSq (levelWeight ell η 2 0) A = ‖A‖ ^ 2
    ∧ coarseNormSq (levelWeight ell η 2 1) B = ‖B‖ ^ 2 := by
  constructor
  · rw [fineNormSq_eq, levelWeight_two, one_mul]
  · rw [coarseNormSq_eq, levelWeight_two, one_mul]

/-- **THE MUST-NOT-FIRE CONTROL, as a re-derivation.** `QCLMNorm.qCLM_norm_sq_le`'s statement
(`‖QA‖² ≤ ell⁻³‖A‖²`) falls out of `weighted_norm_sq_le` at `d = 2`. So the weighted machinery
degenerates to exactly the unweighted result when the weight degenerates — and to nothing else.
(The proof goes through the weighted theorem; it does not cite `qCLM_norm_sq_le`.) -/
theorem unweighted_recovered_from_weighted {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : BondFnL2 L) :
    ‖qCLM U ell A‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 3) * ‖A‖ ^ 2 := by
  have h := weighted_norm_sq_le (L := L) hell hdvd (η := 1) one_pos 2 U A
  rw [(weighted_at_two_collapses (ell := ell) (L := L) 1 A (qCLM U ell A)).1,
    (weighted_at_two_collapses (ell := ell) (L := L) 1 A (qCLM U ell A)).2] at h
  have hc : (ell : ℝ) ^ ((2 : ℤ) - 5) = 1 / (ell : ℝ) ^ 3 := by
    have he : ((2 : ℤ) - 5) = -((3 : ℕ) : ℤ) := by norm_num
    rw [he, zpow_neg_natCast_eq]
  rwa [hc] at h

/-! ## §10 — MUST-FIRE ON THE EXPONENT: mutate `d − 2 ↦ 3` and the no-go fires -/

/-- At exponent `d = 5` the weighted constant is EXACTLY `1`. -/
theorem weighted_const_five {ell : ℕ} : (ell : ℝ) ^ ((5 : ℤ) - 5) = 1 := by
  norm_num

/-- **THE MUTATION FIRES.** Give (3.16)'s weight the exponent `d` instead of `d − 2` — i.e. the
exponent p.393's *other* scalar product carries, which at `d = 3` means a per-step ratio `ell³`
instead of `ell`, the same as taking the dimension exponent to `5` — and the weighted `q` becomes
exactly `1`. Then `GammaRecursion.not_uniformStepGamma_one_of_pos_delta` fires: no `k`-uniform
positive floor, for any `δ > 0`. Sharpness (`weighted_sharp_trivialU` at `d = 5`) is what makes
this a real firing rather than a lossy estimate: `1` is the VALUE, not a bound. -/
theorem weighted_nogo_fires_at_exponent_five {δ : ℝ} (hδ : 0 < δ) :
    ¬ UniformStepGamma δ 1 :=
  not_uniformStepGamma_one_of_pos_delta hδ

/-- The `d = 5` constant is sharp at the flat background: no `c < 1` is admissible. So the mutated
statement is genuinely at the boundary, not merely bounded by it. -/
theorem weighted_sharp_five {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {η : ℝ} (hη : 0 < η) {c : ℝ} (hc : WeightedRatioBound L ell η 5 (trivialU L) c) :
    (1 : ℝ) ≤ c := by
  have h := weighted_sharp_trivialU hell hdvd hη 5 hc
  rwa [weighted_const_five] at h

/-- At exponent `d = 6` the constant strictly exceeds `1` and the strict no-go fires. -/
theorem weighted_nogo_fires_at_exponent_six {ell : ℕ} (hell : 2 ≤ ell) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((1 : ℝ) < Real.sqrt ((ell : ℝ) ^ ((6 : ℤ) - 5)))
    ∧ ¬ UniformStepGamma δ (Real.sqrt ((ell : ℝ) ^ ((6 : ℤ) - 5))) := by
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hval : (ell : ℝ) ^ ((6 : ℤ) - 5) = (ell : ℝ) := by norm_num
  have hgt : (1 : ℝ) < Real.sqrt ((ell : ℝ) ^ ((6 : ℤ) - 5)) := by
    rw [hval]
    have : Real.sqrt 1 < Real.sqrt (ell : ℝ) := by
      apply Real.sqrt_lt_sqrt (by norm_num)
      linarith
    rwa [Real.sqrt_one] at this
  exact ⟨hgt, not_uniformStepGamma_of_one_lt hδ hgt⟩

/-! ## §11 — MUST-FIRE ON THE OPERATOR: delete the `(1/ell⁴)` and the weighted bound breaks

The exponent controls of §10 vary the WEIGHT. This one varies the OPERATOR, so that
`weighted_norm_sq_le` cannot be suspected of being algebraically forced: `QCLMNorm.qSumCLM` is
`qCLM` with its normalisation cancelled and nothing else changed, and the `d = 3` weighted bound is
FALSE for it. -/

theorem summing_variant_weighted_not_le {ell : ℕ} (hell : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    {η : ℝ} (hη : 0 < η)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ¬ (∀ A : BondFnL2 L, coarseNormSq (levelWeight ell η 3 1) (qSumCLM U ell A)
        ≤ (1 / (ell : ℝ) ^ 2) * fineNormSq (levelWeight ell η 3 0) A) := by
  intro hall
  have hell0 : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hellR : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hw0 : 0 < levelWeight ell η 3 0 := levelWeight_pos hell0 hη 3 0
  have h := hall (deltaWitness L)
  -- the fine side is `w₀ · 1`
  have hfine : fineNormSq (levelWeight ell η 3 0) (deltaWitness L) = levelWeight ell η 3 0 := by
    rw [fineNormSq_eq, norm_deltaWitness]; ring
  -- the coarse side is at least `w₁ · 1`, because `‖qSum δ‖ ≥ 1`
  have happ : qSumCLM U ell (deltaWitness L)
      = (ell : ℝ) ^ 4 • (qCLM U ell (deltaWitness L)) := rfl
  have hlow : (1 : ℝ) ≤ ‖qSumCLM U ell (deltaWitness L)‖ := by
    have hw := norm_qCLM_deltaWitness hell0 hdvd hwide U
    rw [happ, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (ell : ℝ) ^ 4)]
    calc (1 : ℝ) = (ell : ℝ) ^ 4 * (1 / (ell : ℝ) ^ 4) := by field_simp
      _ ≤ (ell : ℝ) ^ 4 * ‖qCLM U ell (deltaWitness L)‖ :=
          mul_le_mul_of_nonneg_left hw (by positivity)
  have hw1 : 0 < levelWeight ell η 3 1 := levelWeight_pos hell0 hη 3 1
  have hsq : (1 : ℝ) ≤ ‖qSumCLM U ell (deltaWitness L)‖ ^ 2 := by nlinarith [hlow]
  have hcoarse : levelWeight ell η 3 1
      ≤ coarseNormSq (levelWeight ell η 3 1) (qSumCLM U ell (deltaWitness L)) := by
    rw [coarseNormSq_eq]
    nlinarith [hsq, hw1]
  -- so `w₁ ≤ ell⁻² w₀`, i.e. `ell · w₀ ≤ ell⁻² · w₀`, i.e. `ell³ ≤ 1` — false
  rw [hfine] at h
  have hstep : levelWeight ell η 3 1 ≤ (1 / (ell : ℝ) ^ 2) * levelWeight ell η 3 0 :=
    le_trans hcoarse h
  have hw1eq : levelWeight ell η 3 1 = (ell : ℝ) * levelWeight ell η 3 0 := by
    rw [levelWeight_one_eq]
    norm_num
  rw [hw1eq] at hstep
  have hcube : (ell : ℝ) ≤ 1 / (ell : ℝ) ^ 2 := le_of_mul_le_mul_right hstep hw0
  have hpos2 : (0 : ℝ) < (ell : ℝ) ^ 2 := by nlinarith
  rw [le_div_iff₀ hpos2] at hcube
  nlinarith [hcube, hellR]

/-! ## §12 — axiom audit -/

#print axioms fineNormSq
#print axioms coarseNormSq
#print axioms fineNorm
#print axioms coarseNorm
#print axioms WeightedRatioBound
#print axioms fineNormSq_eq
#print axioms coarseNormSq_eq
#print axioms fineNormSq_nonneg
#print axioms levelWeight_pos
#print axioms levelWeight_succ
#print axioms levelWeight_one_eq
#print axioms weighted_ratio_uniform_in_level
#print axioms source_normalisation_sums_to_one
#print axioms zpow_neg_natCast_eq
#print axioms weighted_const_eq
#print axioms weighted_norm_sq_le
#print axioms overall_constant_cancels
#print axioms weighted_const_eta_free
#print axioms fineNormSq_constWitness
#print axioms fineNormSq_constWitness_pos
#print axioms weighted_norm_sq_eq_trivialU
#print axioms weightedRatioBound_holds
#print axioms weighted_sharp_trivialU
#print axioms weighted_pointwise_le
#print axioms weighted_pointwise_eq_trivialU
#print axioms weighted_const_three
#print axioms weighted_sqrt_const_three
#print axioms weighted_norm_sq_le_three
#print axioms weighted_q_three_lt_one
#print axioms weighted_q_three_pos
#print axioms weighted_uniformStepGamma_three
#print axioms weighted_q_two_eq_half
#print axioms weighted_uniformStepGamma_at_two
#print axioms weighted_route_survives
#print axioms weighted_norm_sq_le_on_coarse_subset
#print axioms qCLM_deltaWitness_coord
#print axioms deltaWitness_sum_off_support
#print axioms fine_restriction_not_free
#print axioms weighted_curvedRegularU_two
#print axioms weighted_curvedRegularU_two_nogo_hypothesis_fails
#print axioms weighted_trivialU_two_witL5_sharp
#print axioms weighted_trivialU_two_witL5_best
#print axioms one_le_zpow_of_nonneg
#print axioms zpow_lt_one_of_neg
#print axioms weighted_lt_one_iff_lt_five
#print axioms weighted_inverted_direction_still_lt_one
#print axioms weighted_exponent_arithmetic_general_d
#print axioms weighted_at_two_collapses
#print axioms unweighted_recovered_from_weighted
#print axioms weighted_const_five
#print axioms weighted_nogo_fires_at_exponent_five
#print axioms weighted_sharp_five
#print axioms weighted_nogo_fires_at_exponent_six
#print axioms summing_variant_weighted_not_le

end AdalyFormal.Balaban.WeightedQNorm
