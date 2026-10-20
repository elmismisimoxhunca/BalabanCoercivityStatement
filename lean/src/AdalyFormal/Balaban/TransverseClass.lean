/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.NilLevelTarget
import AdalyFormal.Balaban.BlockPoincareLemma24

set_option autoImplicit false
set_option maxRecDepth 12000

/-!
# `TransverseClass.lean` — what CMP99b p.428's subspace must be, and which side is at fault

## The dispatched question

`NilLevelTarget.targetAt_refuted` / `.targetFibreClauses_refuted` refute the tree's level-corrected
coercivity target at a datum — `NilLevelTarget.loopField`, one plaquette circulation — that is
simultaneously (i) admissible for both of the target's `B̃` clauses and (ii) **in the fibre**
`V = ker Q_{S.fibre} ∩ {R(D*_U ·) = 0}`. Since the right-hand side is a distance to `D_U(V)`, it
vanishes at any admissible element of the fibre. The dispatched hypothesis was that the *admissible
class* must therefore carry a transversality condition nobody has encoded.

**That hypothesis is false, and the source says why.** The defect is on the LEFT-hand side: the
target measures `B̃` with the **fine** `ℓ²` norm `bondEnergy` while taking the fibre of the
**fine → unit** averaging map. In CMP99b those are one renormalisation level apart, and an element
of the fibre is a field whose *unit-lattice* image is ZERO — so the source's own left-hand side
vanishes on it too, and no transversality is needed or available.

## Source, verbatim

Both pages `verification_status: adjudicated`.
`corpus/pages/CMP99b_p428.md`, render sha256
`128b1172e7090661d2c2ead70d9514244567c17a43c709ff87b18603b3012d54`;
`corpus/pages/CMP99b_p427.md`, render sha256
`59b96e187b52b094baff8aa991dab8ddba5f0a72883d6467041155117f60db02`.

**Transcription convention for the two quotes below.** They are word-for-word from the corpus page's
`VERBATIM` section, with the page's LaTeX transliterated into this tree's plain notation
(`\bigcup → ⋃`, `\tilde B → B̃`, `\langle·,·\rangle → ⟨·,·⟩`, `\upharpoonright → ↾`,
`\tfrac12 → ½`, superscripts to Unicode). **No word is added, removed or reordered, and no emphasis
in the source is dropped**; where a quote is truncated it is marked `…`. Any emphasis shown is the
source's own — nothing here is bolded by this file. A disputed reading goes to the page image, per
LAW-11; nothing below is disputed.

CMP99b p.428, the sentence that fixes the subspace:

> "This form is considered on the subspace `{B : B=0 on Λ^c, B=0 on ⋃_{y∈Λ'} Ax(y), Q₁B=0}`. We can
> parametrize this subspace in the same way as in [4] (2.154-2.155), using part of the variables
> `B`, which we denote by `B̃`. These are variables `B` restricted to the set of bonds
> `Λ̃ = Λ \ (⋃_{y∈Λ'} Ax(y) ∪ ⋃_{c∈Λ'} B(c)∩c)`."

The clause this file leans on is "*These are variables `B` restricted to the set of bonds `Λ̃`*" —
emphasis added HERE, not in the source.

CMP99b p.428 (3.159), the display that carries BOTH averaging arrows at once, quoted in full:

> `exp(½⟨g, C⁽ᵏ⁾(Λ)g⟩) = (Z⁽ᵏ⁾(Λ))⁻¹ ∫ dB↾_Λ δ(Q₁B) δ_Ax(B)`
> `  × exp[⟨H₁D̃⁽²⁾(B), J⟩ + ⟨B,g⟩]`
> `  × Z_k⁻¹ ∫ dA δ(QA − B) δ_R(RD*A)`
> `  × exp[−½⟨A, (Δ+Δ⁽²⁾)A⟩].`

Reading off the arrows (this is `CStarLevelCorrected.lean`'s own level table, re-derived here from
the same display, not taken on trust):

| source object | arrow | role |
|---|---|---|
| `Q`, in `δ(QA − B)` | fine `A` → unit `B` | the Schur **fibre**: minimise
`⟨A,(Δ+Δ⁽²⁾)A⟩` over `QA = B` |
| `Q₁`, in `δ(Q₁B)` | unit `B` → `Λ'` | an **admissibility clause on `B`**, with
`B = 0` on `Ax(y)` |
| `B̃` | `B` restricted to unit bonds `Λ̃` | the free coordinate; `B = CB̃` |

Two consequences, both load-bearing and both from the quoted text:

1. **`B̃` is a UNIT-lattice object** ("variables `B` restricted to the set of bonds `Λ̃`"), so
   `⟨B̃,B̃⟩` — the norm against which p.428 asserts "`C*Δ_kC` … with a lower bound `γ₀ > 0`
   independent of `k` and `U`" — is a norm at the level of `B`, i.e. at the level `Q` lands on.
2. `Δ_k`'s fibre is `{A : QA = 0}`, one level FINER. Its members are not unit-lattice fields at all.

The tree's encoding pulls everything back to the single space `Bond L → SuTwo` and indexes the tower
by block side, `Q_{ell} := lineCoarseRestrictCovLM U ell`. In that presentation `Bond L` plays the
FINE role (it is `Q_{S.fibre}`'s domain), `CoarseBond L S.fibre` plays the UNIT role, and the
correct left-hand side of the coercivity inequality is the **unit-lattice** norm of `B̃`'s image,

  `coarseUnitEnergy S.fibre U B̃ := Σ_{c : CoarseBond L S.fibre} ‖(Q_{S.fibre} B̃)(c)‖²`,

NOT `bondEnergy B̃ = Σ_{b : Bond L} ‖B̃ b‖²`. `ThirdLevelSchurGap.
LevelCorrectedCoercivityTargetUniform` and `NilLevelTarget.LevelCorrectedCoercivityTargetAt` use the
latter. That is the defect this file localises, and `CStarLevelCorrected.lean`'s own docstring
already contains the fact in isolation ("the source puts the MASS at the `Q` level, not the `Q₁`
level — `a⟨B,B⟩` in (3.156) is the norm of the unit field `B = QA`") without drawing this
consequence for the target's left-hand side.

## What is PROVED here

* **§2 — `coarseUnitEnergy_eq_zero_of_mem_fibre`.** EVERY element of the fibre
  `V = ker Q_{ell} ∩ {R(D*_U ·) = 0}` has corrected left-hand side exactly `0`, at every `ell`,
  every `levels`, every `U`. The fibre's FIRST clause *is* `Q_{ell}B = 0`.
* **§2 — `fibre_element_cannot_refute`.** Hence for every `γ₀ ≥ 0` and every fibre element the
  corrected inequality HOLDS (`0 ≤ RHS`, and `RHS ≥ 0` always). **No admissible fibre element can
  ever refute the corrected target**, whatever the admissible class is. So the class does not need
  to be transverse to the fibre — the dispatched premise fails once the norm is at the right level.
* **§3 — `loopField_coarseUnitEnergy_zero` / `loopField_satisfies_corrected`.** The specific datum:
  `NilLevelTarget.loopField` has corrected left-hand side `0`, and satisfies the corrected
  inequality for every `γ₀`. The refutation mechanism of `NilLevelTarget` is dead against it.
* **§4 — `UnitNormCoercivityTargetAt`, stated**, character-for-character
  `NilLevelTarget.LevelCorrectedCoercivityTargetAt` except for the left-hand side; and
  `corrected_target_domain_nonvacuous`: at `m = 0` the datum `wField` is admissible for both
  clauses, has **strictly positive** corrected left-hand side (`0 < coarseUnitEnergy`) and strictly
  positive right-hand side. So the corrected statement is not vacuous — it is not satisfied by
  making every left-hand side zero.
* **§5 — `class_transverse_to_curlFree`, the theorem the dispatch asked for.** In the real sector
  (`U = 1`), the class p.428 PRINTS — `B = 0` on `⋃_{y∈Λ'} Ax(y)` (`admissibleSubspaceInter`,
  CMP96 (2.121)) together with `Q₁B = 0` (`lineCoarseRestrict`, CMP96 (2.125)) — is transverse to
  the CURL-FREE subspace: `curlValue B = 0` forces `B = 0`. Unconditionally, at every block side
  `ell ≥ 1` with `ell ∣ L μ + 1` and `ell < L μ + 1`. The curl-free subspace is the zero set of the
  energy `⟨A,ΔA⟩` that (3.159)'s inner integral minimises, so this is the transversality the source
  actually needs, and it is a property of the class AS PRINTED — nothing has to be added to it.
  **Notably this is the QUALITATIVE half of CMP96 Lemma 2.4 and it needs NONE of that lemma's
  residual `(2.127)`** (`BlockPoincareLemma24`'s `[RES-CMP96-2128-SLABLOCAL]`): at `curl = 0` the
  quantitative cross-sectional operator bound is not required, because the interface bonds are
  forced constant along each interface and then killed by `Q₁B = 0` exactly.
* **§6 — `loopField_curl_ne_zero` / `loopField_dstarD_pos`.** The counterexample datum is NOT in
  the curl-free subspace: its circulation around its own plaquette is `4·suTwoWitness ≠ 0`, and
  `dstarDQuadForm (trivialU) (loopField m) > 0`. So under §5's fibre the loop is excluded, which is
  the cheap check the dispatch asked to run first.

## What is NOT claimed

* **No coercivity.** `γ₀ · coarseUnitEnergy ≤ cStarDeltaKCFormCorr` is NOT proved for any `γ₀ > 0`.
  §2–§4 establish that the two refutation mechanisms in this tree (`WitnessInequality`'s rate and
  `NilLevelTarget`'s vanishing) do not apply to the corrected left-hand side, and that the corrected
  statement has a non-vacuous domain. That is strictly weaker than proving it.
* §5 is in the **real sector** (`Bond L → ℝ`, `U = 1`, `curlValue`), because
  `BlockPoincare.block_poincare` — the `(2.123)` brick it consumes — is stated there. The
  general-`U`
  statement is not proved here.
* **§5 encodes TWO of p.428's THREE clauses; the third is VACUOUS in this setting, and that is a
  scope restriction, not a fidelity claim.** p.428's subspace is
  `{B : B=0 on Λ^c, B=0 on ⋃_{y∈Λ'}Ax(y), Q₁B=0}`. `class_transverse_to_curlFree` imposes the
  second (`admissibleSubspaceInter L ell`, quantified over EVERY `y ∈ CoarseLattice L ell` and every
  `x ∈ B(y)`; `AxialContour.axUnionLocus_eq_iInf` proves that reading of "`B = 0` on a union of
  `Ax(y)`" agrees with the intersection-of-subspaces reading, and
  `AxialContour.cmp95AxLocus L ell` is that union at `S := CoarseLattice L ell`) and the third
  (`hQ`, over every `c : CoarseBond L ell`).

  **The FIRST clause, `B = 0` on `Λ^c`, is not imposed and cannot be**: this tree works on the full
  periodic torus, so `Λ` is everything and `Λ^c = ∅`. `AxialContour.cmp95AxLocus`'s own docstring
  records the matching caveat from the other side — that union over the FULL coarse lattice is
  CMP95 (1.10), "*the unrestricted single-scale axial gauge condition, no `Λ'` restriction*",
  whereas "*the `(3.156)` subspace instead uses a restricted `S`*". The two coincide exactly when
  `Λ` is the whole torus, which is this theorem's setting. So §5 is the whole-torus case `Λ = Λ_k`:
  it DROPS a hypothesis rather than adding one, which makes it stronger on its own domain, but it is
  NOT the Dirichlet-boundary statement p.428 needs for a proper subdomain `Λ ⊂ Λ_k`, where `Λ'` is a
  strict subset of `CoarseLattice L ell` and the axial union is correspondingly smaller. No claim
  about that case is made here. Both `hdvd` (`ell ∣ L μ + 1`, exact tiling) and
  `hstrict` (`ell < L μ + 1`, more than one block per axis) are genuinely used; `hdvd` in particular
  is what stops `blockOf` from silently truncating.
* §5's fibre is the curl-free subspace. `ker Δ_k ⊆ {curl = 0}` requires the intertwining
  `curl ∘ Q = Q' ∘ curl` (`[STOKES-COMM]`, closed in this tree only at `levels = []`/level 2 and
  compiled-refuted at `oneLevelUniv`); §5 is therefore a statement about a subspace that CONTAINS
  the source's `ker Δ_k` under that intertwining, and stands on its own without it.
* **NO REGISTERED RESIDUAL IS CLOSED HERE.** Explicitly: `[RES-CMP96-2128-SLABLOCAL]`
  (`BlockPoincareLemma24` §4, the cross-sectional `(2.127)` operator positivity) is NOT discharged —
  §5 proves the `curl = 0` SPECIALISATION of `(2.128)`'s consequence, which needs no quantitative
  absorption, and says nothing about `(2.128)` itself. And `[LEM-COERC-U]`
  (`compute/RESIDUAL_REGISTER.md` row 1, `Δ_k(U) ≥ γ″ > 0` uniform in `k` and `U`) is NOT touched:
  §5 is at `U = 1`, and the general-`U` sentence on p.428 is exactly what that row records as
  asserted-without-proof.
* **OFF-SPINE.** This module, `NilLevelTarget`, `WitnessInequality`, `ThirdLevelSchurGap` are all
  unreachable from `AdalyFormal.lean` and `Spine.lean`. Nothing here moves a milestone.
-/

namespace AdalyFormal.Balaban.TransverseClass

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU deltaKernelImageCovH RcovLM
  gradCovariantAdjointLM)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond curlValue)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.LineIntegralAveraging (lineCoarseRestrict lineIntegralValue)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.Balaban.ReparamCSuTwo (coeffDc)
open AdalyFormal.Balaban.FullReparamC (fullC dinvC dinvC_hinv)
open AdalyFormal.Balaban.CStarLevelCorrected (LevelSplit cStarDeltaKCFormCorr)
open AdalyFormal.Balaban.BlockPoincare (bondsInBlock mem_bondsInBlock plaqsInBlock mem_plaqsInBlock
  block_poincare)
open AdalyFormal.Balaban.WitnessInequality (wExt wEll wExt_succ wEll_pos wEll_three wConstr_pos
  wExt_four wEll_dvd wConstr_dvd wSplit Q_single_same_dir Q_single_other_dir)
open AdalyFormal.Balaban.LevelTargetWitness (oneSite wBond wField wField_axial wField_dropped)
open AdalyFormal.Balaban.NilLevelTarget (loopField pA pB pC pA_c0 pA_c1 pA_c2 pB_c0 pB_c1 pB_c2
  pC_c0 pC_c1 pC_c2 pA_ne_pC loopField_at_pA_one bondEnergy_loopField_pos loopField_axial
  loopField_dropped loopField_mem_fibre)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the corrected LEFT-HAND SIDE: the norm of `B̃`'s UNIT-lattice image

`coarseUnitEnergy ell U B := Σ_{c} ‖(Q_ell B)(c)‖²`, the `ℓ²` norm of `B̃` measured at the level
`Q_{ell}` lands on. This is `⟨B,B⟩` of CMP99b (3.156) in the tree's pulled-back presentation, where
`Bond L` is `Q_{S.fibre}`'s DOMAIN (the fine level) and `CoarseBond L S.fibre` is its codomain (the
unit level, where `B` lives). Compare `RegularUPerturbation.bondEnergy`, which sums over `Bond L`
— one level too fine. -/

/-- **The unit-lattice energy of a field's coarse image** —
`Σ_{c : CoarseBond L ell} ‖(Q_ell B)(c)‖²`.
Same shape as `bondEnergy`, one level up: the sum runs over the codomain of `Q_ell`, not its
domain. -/
noncomputable def coarseUnitEnergy (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) : ℝ :=
  ∑ c : CoarseBond L ell, ‖lineCoarseRestrictCov U ell B c‖ ^ 2

theorem coarseUnitEnergy_nonneg (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) : 0 ≤ coarseUnitEnergy ell U B :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The corrected left-hand side vanishes exactly when the field's unit-lattice image vanishes. -/
theorem coarseUnitEnergy_eq_zero_iff (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) :
    coarseUnitEnergy ell U B = 0 ↔ lineCoarseRestrictCovLM U ell B = 0 := by
  classical
  constructor
  · intro h
    funext c
    have hterm : ∀ c' : CoarseBond L ell, (c' ∈ (Finset.univ : Finset (CoarseBond L ell))) →
        ‖lineCoarseRestrictCov U ell B c'‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp h
    have := hterm c (Finset.mem_univ c)
    rw [lineCoarseRestrictCovLM_apply, Pi.zero_apply]
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  · intro h
    refine Finset.sum_eq_zero fun c _ => ?_
    have : lineCoarseRestrictCov U ell B c = 0 := by
      rw [← lineCoarseRestrictCovLM_apply, h, Pi.zero_apply]
    rw [this, norm_zero]
    norm_num

/-! ## §2 — NO ELEMENT OF THE FIBRE CAN REFUTE THE CORRECTED STATEMENT

The fibre's FIRST clause is `Q_{ell}B = 0` (`mem_gaugeConstraintSubspaceCovFaithful`), which is
literally "the unit-lattice image of `B` is zero". So the corrected left-hand side is `0` on the
whole fibre — no matter what the admissible class is, and no matter what `γ₀` is. This is the
precise sense in which the dispatched premise ("the admissible class has to be transverse to the
fibre") fails: it is an artefact of measuring `B̃` at the fine level. -/

/-- **THE FIBRE HAS ZERO CORRECTED LEFT-HAND SIDE.** Every `B ∈ V = ker Q_{ell} ∩ {R(D*_U ·)=0}`
has `coarseUnitEnergy ell U B = 0`, at every `ell`, `levels`, `U`. -/
theorem coarseUnitEnergy_eq_zero_of_mem_fibre {ell : ℕ}
    {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {B : Bond L → SuTwo} (hB : B ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    coarseUnitEnergy ell U B = 0 :=
  (coarseUnitEnergy_eq_zero_iff ell U B).mpr
    (mem_gaugeConstraintSubspaceCovFaithful.mp hB).1

/-- **NO FIBRE ELEMENT REFUTES THE CORRECTED INEQUALITY**, for EVERY real `γ₀` — no sign hypothesis
is needed, because the corrected left-hand side is exactly `0` on the fibre — any admissible class,
any `S`, `levels`, `U`, `Dinv`. The right-hand side is always `≥ 0`. This is the general
statement of
which §3's `loopField` fact is one instance; it says the whole mechanism of
`NilLevelTarget.targetAt_refuted` is unavailable against the corrected left-hand side, independently
of which datum one picks inside the fibre. -/
theorem fibre_element_cannot_refute {S : LevelSplit} {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful S.fibre levels U).HasOrthogonalProjection]
    (Dinv : CoarseBond L S.constr → (SuTwo →ₗ[ℝ] SuTwo))
    (γ₀ : ℝ) {B : Bond L → SuTwo}
    (hB : B ∈ gaugeConstraintSubspaceCovFaithful S.fibre levels U) :
    γ₀ * coarseUnitEnergy S.fibre U B ≤ cStarDeltaKCFormCorr S levels U Dinv B := by
  rw [coarseUnitEnergy_eq_zero_of_mem_fibre hB, mul_zero]
  exact deltaJQuadFormCovFaithful_nonneg S.fibre levels U _

/-! ## §3 — the specific datum: `NilLevelTarget.loopField` -/

/-- **THE COUNTEREXAMPLE'S CORRECTED LEFT-HAND SIDE IS `0`.** `NilLevelTarget.Q_loopField_fibre`
proves `Q_{ell}(loopField) = 0`; that is exactly the statement that the loop's unit-lattice image
vanishes, so the corrected left-hand side vanishes with it. The loop's `bondEnergy` is strictly
positive (`NilLevelTarget.bondEnergy_loopField_pos`) — the two numbers disagree, and the
disagreement
IS the level defect. -/
theorem loopField_coarseUnitEnergy_zero (m : ℕ) :
    coarseUnitEnergy (wEll m) (trivialU (wExt m)) (loopField m) = 0 :=
  (coarseUnitEnergy_eq_zero_iff _ _ _).mpr (NilLevelTarget.Q_loopField_fibre m)

/-- **THE LOOP SATISFIES THE CORRECTED INEQUALITY, for every real `γ₀` and every `levels`.** Both
sides are `≥ 0` and the left is `0`. Contrast `NilLevelTarget.targetAt_refuted`, where the same
datum
kills the statement outright because the left-hand side there is `bondEnergy (loopField) > 0`. -/
theorem loopField_satisfies_corrected (m : ℕ) (levels : List (KernelSubspace.Level (wExt m)))
    [(deltaKernelImageCovH (trivialU (wExt m)) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful (wSplit m).fibre levels (trivialU (wExt m))).HasOrthogonalProjection]
    (γ₀ : ℝ) :
    γ₀ * coarseUnitEnergy (wSplit m).fibre (trivialU (wExt m)) (loopField m)
      ≤ cStarDeltaKCFormCorr (wSplit m) levels (trivialU (wExt m))
          (dinvC (trivialU (wExt m)) (2 * wEll m)) (loopField m) :=
  fibre_element_cannot_refute _ γ₀ (loopField_mem_fibre m levels)

/-- The two left-hand sides at the SAME datum: the corrected one is `0`, the tree's is `> 0`. A
one-line separation of the two levels, so the defect is not an argument but a pair of numbers. -/
theorem loopField_levels_disagree (m : ℕ) :
    coarseUnitEnergy (wEll m) (trivialU (wExt m)) (loopField m) = 0 ∧
      0 < bondEnergy (loopField m) :=
  ⟨loopField_coarseUnitEnergy_zero m, bondEnergy_loopField_pos m⟩

/-! ## §4 — THE CORRECTED TARGET, STATED, AND ITS DOMAIN IS NON-VACUOUS

`UnitNormCoercivityTargetAt` is `NilLevelTarget.LevelCorrectedCoercivityTargetAt` with ONE change:
`bondEnergy Btil` becomes `coarseUnitEnergy S.fibre U Btil`. Every hypothesis and both `B̃` clauses
are unchanged, including the `2 ≤ S.fibre` and `4 ≤ L μ` guards. -/

/-- **The corrected target, in PARAMETRIZED `∀`-FORM.** Only the left-hand side differs from
`NilLevelTarget.LevelCorrectedCoercivityTargetAt`: `bondEnergy Btil` becomes
`coarseUnitEnergy S.fibre U Btil`.

**The outer `∃ γ₀ α₀` of `NilLevelTarget.LevelCorrectedCoercivityTargetAt` is DELIBERATELY NOT
FORMED here.** `γ₀` and `α₀` are explicit parameters and the two positivity conjuncts
`0 < γ₀`, `0 < α₀` are hypotheses, so this declaration has NO existential conclusion and hands a
prover no free data (S91). The source's own quantifier — p.428's "`C*Δ_kC` … with a lower bound
`γ₀ > 0` independent of `k` and `U`" — is the statement `∃ γ₀ α₀, 0 < γ₀ ∧ 0 < α₀ ∧
UnitNormCoercivityAt γ₀ α₀ choose`, which is recorded here in prose and left unformed in Lean
precisely because nothing below proves or refutes it: every theorem in this file is about the
inequality at a given `γ₀`, and forming the existential would only add an unattacked
existential-target surface. -/
def UnitNormCoercivityAt (γ₀ α₀ : ℝ)
    (choose : (L : PeriodicLatticeExtent) → List (KernelSubspace.Level L)) : Prop :=
  0 < γ₀ → 0 < α₀ →
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
            γ₀ * coarseUnitEnergy S.fibre U Btil ≤ cStarDeltaKCFormCorr S (choose L) U Dinv Btil

/-- **The `levels = []` instance**, matching `NilLevelTarget.NilLevelCorrectedCoercivityTarget`
(again in parametrized `∀`-form, no existential). -/
def NilUnitNormCoercivityAt (γ₀ α₀ : ℝ) : Prop :=
  UnitNormCoercivityAt γ₀ α₀ (fun L => ([] : List (KernelSubspace.Level L)))

/-! ### §4b — the non-vacuity witness: `wField` has STRICTLY POSITIVE corrected left-hand side

The corrected left-hand side is a weaker functional than `bondEnergy`, so the honest question is
whether it is EVER positive on the admissible class — otherwise `UnitNormCoercivityTargetAt` would
be true for trivial reasons. It is: `LevelTargetWitness.wField`, the single `suTwoWitness` spike on
the direction-`2` bond at `(1,0,0)`, is admissible for both clauses at the constraint level and has
`Q_{ell}(wField) ≠ 0` at the coarse bond based at the origin. -/

/-- The origin of the `wExt m` torus, as a member of the fibre-level coarse lattice. -/
def zeroSite (m : ℕ) : PeriodicLatticeSite (wExt m) :=
  fun μ => ⟨0, by have := wExt_four m μ; omega⟩

theorem zeroSite_mem (m : ℕ) : zeroSite m ∈ CoarseLattice (wExt m) (wEll m) :=
  mem_CoarseLattice.mpr fun _ => by simp [zeroSite]

/-- The fibre-level coarse bond of direction `2` based at the origin — the one at which the witness
spike's coarse average is nonzero. -/
def wCoarseFibre (m : ℕ) : CoarseBond (wExt m) (wEll m) :=
  (⟨zeroSite m, zeroSite_mem m⟩, 2)

/-- **THE WITNESS'S COARSE IMAGE IS NONZERO at `m = 0`.** `wEll 0 = 3`, `L μ + 1 = 6`. The count of
`Q_single_same_dir` is over `i ∈ {0,1,2}` of whether `oneSite` shifted `6 − i` steps in
direction `2`
lands in the origin block `[0,3)³`: at `i = 0` the shift is a full period and lands back on
`(1,0,0) ∈ [0,3)³`; at `i = 1, 2` the coordinate-`2` value is `5`, `4`, both outside. So the
count is
`1` and the value is `(1/81) • suTwoWitness ≠ 0`. -/
theorem Q_wField_ne_zero :
    lineCoarseRestrictCov (trivialU (wExt 0)) (wEll 0)
        (wField (L := wExt 0) (wExt_four 0)) (wCoarseFibre 0) ≠ 0 := by
  classical
  have hle : wEll 0 ≤ wExt 0 (wCoarseFibre 0).2 + 1 := by
    rw [wExt_succ]; have := wEll_pos 0; omega
  have hval := Q_single_same_dir (L := wExt 0) (wCoarseFibre 0) hle
    (oneSite (L := wExt 0) (wExt_four 0)) suTwoWitness
  have hwf : wField (L := wExt 0) (wExt_four 0)
      = (Pi.single ((oneSite (L := wExt 0) (wExt_four 0), (wCoarseFibre 0).2) : Bond (wExt 0))
          suTwoWitness) := rfl
  rw [hwf, hval]
  have hcard : (((Finset.range (wEll 0)).filter
      (fun i => QOne.pathSite (oneSite (L := wExt 0) (wExt_four 0)) (wCoarseFibre 0).2
        (wExt 0 (wCoarseFibre 0).2 + 1 - i)
          ∈ blockOf (wCoarseFibre 0).1.1 (wEll 0))).card) = 1 := by
    decide
  rw [hcard]
  simp only [Nat.cast_one, one_smul]
  intro hcon
  have : (1 / ((wEll 0 : ℕ) : ℝ) ^ 4) ≠ 0 := by
    have : ((wEll 0 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := wEll_pos 0; omega)
    positivity
  exact suTwoWitness_ne_zero (by
    have := smul_eq_zero.mp hcon
    rcases this with h | h
    · exact absurd h ‹(1 / ((wEll 0 : ℕ) : ℝ) ^ 4) ≠ 0›
    · exact h)

/-- **THE CORRECTED LEFT-HAND SIDE IS STRICTLY POSITIVE AT `wField`.** -/
theorem coarseUnitEnergy_wField_pos :
    0 < coarseUnitEnergy (wEll 0) (trivialU (wExt 0)) (wField (L := wExt 0) (wExt_four 0)) := by
  classical
  refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨wCoarseFibre 0, Finset.mem_univ _, ?_⟩
  have h := Q_wField_ne_zero
  have : 0 < ‖lineCoarseRestrictCov (trivialU (wExt 0)) (wEll 0)
      (wField (L := wExt 0) (wExt_four 0)) (wCoarseFibre 0)‖ := norm_pos_iff.mpr h
  positivity

/-- **THE CORRECTED TARGET'S DOMAIN IS NON-VACUOUS.** At `m = 0` the datum `wField` satisfies both
`B̃` clauses of `UnitNormCoercivityTargetAt` at the constraint level `2·wEll 0 = 6` and has strictly
positive corrected left-hand side. So the corrected statement is a genuine inequality on a nonempty
class, not one made true by a vanishing left-hand side.

Pattern follows `LevelTargetWitness.target_domain_nonempty`, as the dispatch's trap note
requires. -/
theorem corrected_target_domain_nonvacuous :
    (∀ y' : PeriodicLatticeSite (wExt 0), y' ∈ CoarseLattice (wExt 0) (2 * wEll 0) →
        ∀ x : PeriodicLatticeSite (wExt 0), x ∈ blockOf y' (2 * wEll 0) →
        ∀ e ∈ staircasePath y' x, wField (L := wExt 0) (wExt_four 0) e = 0) ∧
      (∀ c : CoarseBond (wExt 0) (2 * wEll 0),
        wField (L := wExt 0) (wExt_four 0) (droppedBondLast (2 * wEll 0) c) = 0) ∧
      0 < coarseUnitEnergy (wEll 0) (trivialU (wExt 0)) (wField (L := wExt 0) (wExt_four 0)) := by
  have h2 : 2 ≤ 2 * wEll 0 := by have := wEll_pos 0; omega
  exact ⟨wField_axial h2 (wExt_four 0), wField_dropped h2 (wExt_four 0),
    coarseUnitEnergy_wField_pos⟩

/-! ## §5 — THE TRANSVERSALITY THEOREM: p.428's class, AS PRINTED, kills the curl-free fibre

The fibre the source's `Δ_k` actually has is not `ker Q`: (3.159)'s inner integral MINIMISES
`⟨A,(Δ+Δ⁽²⁾)A⟩` over `{A : QA = B}`, so `⟨B,Δ_kB⟩ = 0` needs a MINIMISER with zero energy, i.e. a
curl-free `A`. The subspace to be transverse to is therefore the CURL-FREE one, and this section
proves p.428's printed class is transverse to it, unconditionally:

  `B = 0 on ⋃_{y∈Λ'} Ax(y)`  ∧  `Q₁B = 0`  ∧  `∂₁B = 0`   ⟹   `B = 0`.

`Ax` is `AdmissibleSubspace.admissibleSubspaceInter` (CMP96 (2.121), universal in `y ∈ Λ'` and
`x ∈ B(y)`); `Q₁` is `LineIntegralAveraging.lineCoarseRestrict` (CMP96 (2.125), with its `1/ell⁴`
weight); `∂₁` is `LatticeOperators.curlValue` (CMP95 (1.2)).

**This is the QUALITATIVE half of CMP96 Lemma 2.4 and it needs none of that lemma's residual.**
`BlockPoincareLemma24` states `(2.128)` — `ell·Σ_c|(Q₁B)(c)|² + Σ_p|(∂₁B)(p)|² ≥ (1/108)ell⁻⁴‖B‖²` —
as a `Prop`-valued target and names `[RES-CMP96-2128-SLABLOCAL]` (the cross-sectional operator
positivity `(2.127)`) as its missing ingredient. `(2.128)` with both left-hand terms `0` would give
exactly this section's conclusion, so the theorem below is a CONSEQUENCE of the unproved `(2.128)` —
but it is proved here WITHOUT it, from the `(2.123)` brick alone (`BlockPoincare.block_poincare`,
which IS proved) plus an exact interface argument. The reason the residual is not needed is that at
`∂₁B = 0` no quantitative absorption happens: `(2.123)` kills the in-block bonds exactly, the curl
then forces each cross-block bond to be constant along its interface, and `Q₁B = 0` is a nonzero
multiple of that constant.

Real sector (`U = 1`, `Bond L → ℝ`) because `block_poincare` is stated there. -/

section RealSector

/-! ### §5a — arithmetic and geometry helpers -/

/-- A purely linear arithmetic fact, stated with the product `ell·(v/ell)` already abstracted to a
variable `t` so `omega` can see it. Used three times below. -/
private theorem window_arith (ell v n t r : ℕ) (ht : t + r = v) (hr : r < ell)
    (hne : r ≠ ell - 1) (hfit : t + ell ≤ n) : v + 1 < n := by omega

/-- `(b+j) % ell` only depends on `b`'s offset above any `ell`-multiple `a ≤ b`. -/
private theorem mod_add_of_base (ell a b j : ℕ) (hdvd : ell ∣ a) (hab : a ≤ b) :
    (b + j) % ell = (b - a + j) % ell := by
  obtain ⟨k, hk⟩ := hdvd
  have heq : b + j = (b - a + j) + ell * k := by rw [← hk]; omega
  rw [heq, Nat.add_mul_mod_self_left]

/-- **THE UNIQUENESS OF THE INTERFACE INDEX.** For offsets `r, j < ell`, `(r+j) % ell = ell − 1`
happens at exactly one `j`, namely `j = ell − 1 − r`. -/
private theorem mod_ne_of_ne (ell r j : ℕ) (hr : r < ell) (hj : j < ell)
    (hne : j ≠ ell - 1 - r) : (r + j) % ell ≠ ell - 1 := by
  by_cases h : r + j < ell
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- `y`'s block fits inside the torus: `y_σ + ell ≤ L σ + 1`, for a coarse-lattice centre `y` on an
extent divisible by `ell`. -/
theorem coarse_block_fits {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (σ : Fin 3) :
    (y σ).val + ell ≤ L σ + 1 := by
  obtain ⟨q, hq⟩ := hdvd σ
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy σ)
  have hlt : (y σ).val < L σ + 1 := (y σ).isLt
  rw [hk, hq] at hlt ⊢
  have hkq : k < q := by
    by_contra hcon
    exact absurd hlt (not_lt.mpr (Nat.mul_le_mul_left ell (not_lt.mp hcon)))
  calc ell * k + ell = ell * (k + 1) := by ring
    _ ≤ ell * q := Nat.mul_le_mul_left ell (by omega)

/-- The forward shift's own coordinate, as a `%` expression. -/
theorem shiftVal (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((periodicLatticeShift x μ) μ).val = ((x μ).val + 1) % (L μ + 1) := by
  rw [show periodicLatticeShift x μ = QOne.pathSite x μ 1 by
    rw [QOne.pathSite_succ, QOne.pathSite_zero]]
  exact ReparamCDisjoint.pathSite_apply_self_val x μ 1

/-- The forward shift leaves every other coordinate alone. -/
theorem shiftNe (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    (periodicLatticeShift x μ) ν = x ν := Function.update_of_ne h _ _

/-- **The canonical block centre of a site** — coordinatewise `ell·⌊x_μ/ell⌋`. -/
def bcen (ell : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun μ => ⟨ell * ((x μ).val / ell), lt_of_le_of_lt
    (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _) (x μ).isLt⟩

theorem bcen_val (ell : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((bcen ell x) μ).val = ell * ((x μ).val / ell) := rfl

theorem bcen_mem (ell : ℕ) (x : PeriodicLatticeSite L) : bcen ell x ∈ CoarseLattice L ell :=
  mem_CoarseLattice.mpr fun μ => by rw [bcen_val]; exact Nat.mul_mod_right _ _

theorem mem_blockOf_bcen {ell : ℕ} (hell : 0 < ell) (x : PeriodicLatticeSite L) :
    x ∈ blockOf (bcen ell x) ell := by
  refine mem_blockOf.mpr fun μ => ?_
  rw [bcen_val]
  have h1 := Nat.div_add_mod (x μ).val ell
  have h2 := Nat.mod_lt (x μ).val hell
  omega

/-- Inside a block based at a coarse centre, `% ell` is the offset from the centre. -/
theorem mod_eq_sub_of_mem_block {ell : ℕ} {y z : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (hz : z ∈ blockOf y ell) (ν : Fin 3) :
    (z ν).val % ell = (z ν).val - (y ν).val := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy ν)
  have hb := mem_blockOf.mp hz ν
  have hr : (z ν).val - (y ν).val < ell := by omega
  have heq : (z ν).val = ((z ν).val - (y ν).val) + ell * k := by rw [← hk]; omega
  conv_lhs => rw [heq]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-! ### §5b — the in-block bonds die on the curl-free subspace -/

/-- **`(2.123)` at `∂₁B = 0`: every bond inside a block vanishes.** `block_poincare` bounds the
in-block bond energy by `3ell³` times the in-block curl energy, which is `0`. -/
theorem inblock_zero {ell : ℕ} (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    {B : Bond L → ℝ} (hax : B ∈ admissibleSubspaceInter L ell)
    (hcurl : ∀ p : PeriodicLatticePlaquette L, curlValue B p = 0)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    {b : Bond L} (hb : b ∈ bondsInBlock y ell) : B b = 0 := by
  classical
  have hp := block_poincare (hstrict 0) (hstrict 1) (hstrict 2) B hax y hy
  have hz : ∑ p ∈ plaqsInBlock y ell, (curlValue B p) ^ 2 = 0 :=
    Finset.sum_eq_zero fun p _ => by rw [hcurl p]; ring
  rw [hz, mul_zero] at hp
  have h0 : ∑ b' ∈ bondsInBlock y ell, (B b') ^ 2 = 0 :=
    le_antisymm hp (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp h0 b hb
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hterm

/-- **Every bond that is NOT at a block interface vanishes.** A bond `(x,μ)` whose base coordinate
`x_μ` is not the last site of its `ell`-window has both endpoints in the same block, so
`inblock_zero`
applies. The interface bonds — `x_μ % ell = ell − 1` — are the only survivors. -/
theorem bond_zero_of_mod_ne {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    {B : Bond L → ℝ} (hax : B ∈ admissibleSubspaceInter L ell)
    (hcurl : ∀ p : PeriodicLatticePlaquette L, curlValue B p = 0)
    (b : Bond L) (h : (b.1 b.2).val % ell ≠ ell - 1) : B b = 0 := by
  have hmem : periodicLatticeShift b.1 b.2 ∈ blockOf (bcen ell b.1) ell := by
    refine mem_blockOf.mpr fun σ => ?_
    by_cases hσ : σ = b.2
    · subst hσ
      have hfit := coarse_block_fits hdvd (bcen_mem ell b.1) b.2
      rw [bcen_val] at hfit
      have hd := Nat.div_add_mod (b.1 b.2).val ell
      have hm := Nat.mod_lt (b.1 b.2).val hell
      have hno : (b.1 b.2).val + 1 < L b.2 + 1 :=
        window_arith ell (b.1 b.2).val (L b.2 + 1) (ell * ((b.1 b.2).val / ell))
          ((b.1 b.2).val % ell) hd hm h hfit
      rw [bcen_val, shiftVal, Nat.mod_eq_of_lt hno]
      omega
    · rw [shiftNe b.1 b.2 σ hσ]
      exact mem_blockOf.mp (mem_blockOf_bcen hell b.1) σ
  exact inblock_zero hstrict hax hcurl (bcen_mem ell b.1)
    (mem_bondsInBlock.mpr ⟨mem_blockOf_bcen hell b.1, hmem⟩)

/-! ### §5c — the curl forces each interface bond to be constant along its interface -/

/-- **THE ONE-STEP TRANSVERSE CONSTANCY.** For `ν ≠ μ`, if the base site's `ν`-coordinate is not at
the end of its window then `B(z,μ) = B(z+e_ν,μ)`. Both direction-`ν` bonds of the `(μ,ν)`-plaquette
based at `z` are non-interface bonds — `(z,ν)` by hypothesis, and `(z+e_μ,ν)` because shifting in
direction `μ` does not move the `ν`-coordinate — so they vanish and the curl relation collapses to
the two direction-`μ` bonds. -/
theorem move_step {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    {B : Bond L → ℝ} (hax : B ∈ admissibleSubspaceInter L ell)
    (hcurl : ∀ p : PeriodicLatticePlaquette L, curlValue B p = 0)
    (z : PeriodicLatticeSite L) (μ ν : Fin 3) (hne : ν ≠ μ)
    (h : (z ν).val % ell ≠ ell - 1) :
    B (z, μ) = B (periodicLatticeShift z ν, μ) := by
  have hzν : B (z, ν) = 0 := bond_zero_of_mod_ne hell hdvd hstrict hax hcurl (z, ν) h
  have hshν : B (periodicLatticeShift z μ, ν) = 0 := by
    refine bond_zero_of_mod_ne hell hdvd hstrict hax hcurl (periodicLatticeShift z μ, ν) ?_
    change ((periodicLatticeShift z μ) ν).val % ell ≠ ell - 1
    rw [shiftNe z μ ν hne]; exact h
  rcases lt_or_gt_of_ne (Ne.symm hne : μ ≠ ν) with hlt | hgt
  · have hc := hcurl ((z, (⟨(μ, ν), hlt⟩ : PeriodicPlaquetteDirections)))
    simp only [curlValue] at hc
    rw [hzν, hshν] at hc
    linarith
  · have hc := hcurl ((z, (⟨(ν, μ), hgt⟩ : PeriodicPlaquetteDirections)))
    simp only [curlValue] at hc
    rw [hzν, hshν] at hc
    linarith

/-- Walking `k` steps in direction `ν` from a site in a block stays in the block, without
wraparound,
as long as the target coordinate is still inside the window. -/
theorem pathSite_in_block {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (ν : Fin 3) :
    ∀ (k : ℕ) (z : PeriodicLatticeSite L), z ∈ blockOf y ell →
      (z ν).val + k < (y ν).val + ell →
      ((QOne.pathSite z ν k) ν).val = (z ν).val + k ∧ QOne.pathSite z ν k ∈ blockOf y ell := by
  intro k
  induction k with
  | zero =>
    intro z hz _
    refine ⟨?_, by rw [QOne.pathSite_zero]; exact hz⟩
    rw [QOne.pathSite_zero]
    omega
  | succ n ih =>
    intro z hz hlt
    have hfit := coarse_block_fits hdvd hy ν
    have hbz := mem_blockOf.mp hz ν
    have hno : (z ν).val + 1 < L ν + 1 := by omega
    have hval : ((periodicLatticeShift z ν) ν).val = (z ν).val + 1 := by
      rw [shiftVal, Nat.mod_eq_of_lt hno]
    have hmem : periodicLatticeShift z ν ∈ blockOf y ell := by
      refine mem_blockOf.mpr fun σ => ?_
      by_cases hσ : σ = ν
      · subst hσ; rw [hval]; omega
      · rw [shiftNe z ν σ hσ]; exact mem_blockOf.mp hz σ
    have hiter : QOne.pathSite z ν (n + 1) = QOne.pathSite (periodicLatticeShift z ν) ν n := by
      unfold QOne.pathSite; rw [Function.iterate_succ_apply]
    have hrec := ih (periodicLatticeShift z ν) hmem (by rw [hval]; omega)
    exact ⟨by rw [hiter, hrec.1, hval]; omega, by rw [hiter]; exact hrec.2⟩

/-- **PUSH ONE COORDINATE TO THE TOP OF ITS WINDOW.** For any direction `ν`, a site `z` in the block
whose `μ`-coordinate is already at the top of its window can be replaced, without changing
`B(·,μ)`, by a site whose `ν`-coordinate is also at the top and which agrees with `z` elsewhere.
When `ν = μ` the replacement is `z` itself, so no case analysis on `μ` is needed downstream. -/
def pushSite (ell : ℕ) (ν : Fin 3) (y z : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  QOne.pathSite z ν ((y ν).val + ell - 1 - (z ν).val)

theorem pushSite_apply_ne (ell : ℕ) (ν : Fin 3) (y z : PeriodicLatticeSite L) (σ : Fin 3)
    (hσ : σ ≠ ν) : (pushSite ell ν y z) σ = z σ :=
  ReparamCDisjoint.pathSite_apply_ne z ν σ _ hσ

theorem push_step {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    {B : Bond L → ℝ} (hax : B ∈ admissibleSubspaceInter L ell)
    (hcurl : ∀ p : PeriodicLatticePlaquette L, curlValue B p = 0)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ ν : Fin 3)
    (z : PeriodicLatticeSite L) (hz : z ∈ blockOf y ell)
    (hzμ : (z μ).val = (y μ).val + ell - 1) :
    pushSite ell ν y z ∈ blockOf y ell ∧ ((pushSite ell ν y z) μ).val = (y μ).val + ell - 1 ∧
      ((pushSite ell ν y z) ν).val = (y ν).val + ell - 1 ∧
      B (z, μ) = B (pushSite ell ν y z, μ) := by
  by_cases hνμ : ν = μ
  · subst hνμ
    have hk0 : (y ν).val + ell - 1 - (z ν).val = 0 := by omega
    have hid : pushSite ell ν y z = z := by
      unfold pushSite; rw [hk0, QOne.pathSite_zero]
    rw [hid]
    exact ⟨hz, hzμ, hzμ, rfl⟩
  · -- walk up in direction `ν`, one step at a time
    have hne : ν ≠ μ := hνμ
    have key : ∀ (k : ℕ) (z' : PeriodicLatticeSite L), z' ∈ blockOf y ell →
        (z' ν).val + k = (y ν).val + ell - 1 → B (z', μ) = B (QOne.pathSite z' ν k, μ) := by
      intro k
      induction k with
      | zero => intro z' _ _; rw [QOne.pathSite_zero]
      | succ n ih =>
        intro z' hz' hk
        have hbz := mem_blockOf.mp hz' ν
        have hmodv := mod_eq_sub_of_mem_block hy hz' ν
        have hmod : (z' ν).val % ell ≠ ell - 1 := by rw [hmodv]; omega
        have hstepB := move_step hell hdvd hstrict hax hcurl z' μ ν hne hmod
        have hfit := coarse_block_fits hdvd hy ν
        have hno : (z' ν).val + 1 < L ν + 1 := by omega
        have hval : ((periodicLatticeShift z' ν) ν).val = (z' ν).val + 1 := by
          rw [shiftVal, Nat.mod_eq_of_lt hno]
        have hmem : periodicLatticeShift z' ν ∈ blockOf y ell := by
          refine mem_blockOf.mpr fun σ => ?_
          by_cases hσ : σ = ν
          · subst hσ; rw [hval]; omega
          · rw [shiftNe z' ν σ hσ]; exact mem_blockOf.mp hz' σ
        have hiter : QOne.pathSite z' ν (n + 1)
            = QOne.pathSite (periodicLatticeShift z' ν) ν n := by
          unfold QOne.pathSite; rw [Function.iterate_succ_apply]
        rw [hstepB, hiter]
        exact ih (periodicLatticeShift z' ν) hmem (by rw [hval]; omega)
    have hbz := mem_blockOf.mp hz ν
    have hksum : (z ν).val + ((y ν).val + ell - 1 - (z ν).val) = (y ν).val + ell - 1 := by omega
    have hpath := pathSite_in_block hdvd hy ν ((y ν).val + ell - 1 - (z ν).val) z hz (by omega)
    refine ⟨hpath.2, ?_, by unfold pushSite; rw [hpath.1]; omega,
      key ((y ν).val + ell - 1 - (z ν).val) z hz hksum⟩
    rw [pushSite_apply_ne ell ν y z μ (fun hc => hνμ hc.symm)]
    exact hzμ

/-- **The top corner of a block** — the site all of whose coordinates are at the end of their
window. -/
def topOf {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) : PeriodicLatticeSite L :=
  fun σ => ⟨(y σ).val + ell - 1, by have := coarse_block_fits hdvd hy σ; omega⟩

theorem topOf_val {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (σ : Fin 3) :
    ((topOf hell hdvd hy) σ).val = (y σ).val + ell - 1 := rfl

theorem topOf_mem {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    topOf hell hdvd hy ∈ blockOf y ell :=
  mem_blockOf.mpr fun σ => by rw [topOf_val]; omega

/-- **EVERY INTERFACE BOND OF A BLOCK CARRIES THE SAME VALUE.** Any `z` in the block whose
`μ`-coordinate is at the top of its window has `B(z,μ) = B(topOf y, μ)`. Proved by pushing
coordinates `0`, `1`, `2` to the top in turn — the push in direction `μ` is a no-op, so the argument
is uniform in `μ`. -/
theorem interface_eq_top {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    {B : Bond L → ℝ} (hax : B ∈ admissibleSubspaceInter L ell)
    (hcurl : ∀ p : PeriodicLatticePlaquette L, curlValue B p = 0)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3)
    (z : PeriodicLatticeSite L) (hz : z ∈ blockOf y ell)
    (hzμ : (z μ).val = (y μ).val + ell - 1) :
    B (z, μ) = B (topOf hell hdvd hy, μ) := by
  obtain ⟨hw0mem, hw0μ, hw00, hB0⟩ :=
    push_step hell hdvd hstrict hax hcurl hy μ 0 z hz hzμ
  obtain ⟨hw1mem, hw1μ, hw11, hB1⟩ :=
    push_step hell hdvd hstrict hax hcurl hy μ 1 (pushSite ell 0 y z) hw0mem hw0μ
  obtain ⟨hw2mem, hw2μ, hw22, hB2⟩ :=
    push_step hell hdvd hstrict hax hcurl hy μ 2
      (pushSite ell 1 y (pushSite ell 0 y z)) hw1mem hw1μ
  set w0 := pushSite ell 0 y z with hw0def
  set w1 := pushSite ell 1 y w0 with hw1def
  set w2 := pushSite ell 2 y w1 with hw2def
  have hw10 : (w1 0).val = (y 0).val + ell - 1 := by
    rw [hw1def, pushSite_apply_ne ell 1 y w0 0 (by decide)]; exact hw00
  have hw20 : (w2 0).val = (y 0).val + ell - 1 := by
    rw [hw2def, pushSite_apply_ne ell 2 y w1 0 (by decide)]; exact hw10
  have hw21 : (w2 1).val = (y 1).val + ell - 1 := by
    rw [hw2def, pushSite_apply_ne ell 2 y w1 1 (by decide)]; exact hw11
  have hall : ∀ s : Fin 3, s = 0 ∨ s = 1 ∨ s = 2 := by decide
  have hfin : w2 = topOf hell hdvd hy := by
    funext σ
    refine Fin.ext ?_
    rw [topOf_val]
    rcases hall σ with h | h | h
    · rw [h]; exact hw20
    · rw [h]; exact hw21
    · rw [h]; exact hw22
  rw [hB0, hB1, hB2, hfin]

/-! ### §5d — `Q₁` reads exactly one bond per line, and it is an interface bond -/

/-- **THE LINE INTEGRAL COLLAPSES TO ITS SINGLE INTERFACE BOND.** On the curl-free admissible class,
`B([x, x+ell·e_μ]) = B(topOf y, μ)` for every `x` in the block `B(y)`: of the `ell` bonds of the
segment exactly one is an interface bond (the one whose base `μ`-coordinate is `≡ ell − 1`), the
rest
vanish by `bond_zero_of_mod_ne`, and the survivor equals `B(topOf y, μ)` by `interface_eq_top`. -/
theorem lineIntegral_eq_top {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    {B : Bond L → ℝ} (hax : B ∈ admissibleSubspaceInter L ell)
    (hcurl : ∀ p : PeriodicLatticePlaquette L, curlValue B p = 0)
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3)
    (x : PeriodicLatticeSite L) (hx : x ∈ blockOf y ell) :
    lineIntegralValue ell B x μ = B (topOf hell hdvd hy, μ) := by
  classical
  have hdvdμ : ell ∣ (L μ + 1) := hdvd μ
  have hdvdy : ell ∣ (y μ).val := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy μ)
  have hxb := mem_blockOf.mp hx μ
  have hr : (x μ).val - (y μ).val < ell := by omega
  -- the unique interface index, as an offset
  have hj0lt : ell - 1 - ((x μ).val - (y μ).val) < ell := by omega
  -- `% ell` of the `μ`-coordinate after `j` steps, wraparound included
  have hps : ∀ j : ℕ, (fun z => periodicLatticeShift z μ)^[j] x = QOne.pathSite x μ j :=
    fun _ => rfl
  have hmodpath : ∀ j : ℕ, (((fun z => periodicLatticeShift z μ)^[j] x) μ).val % ell
      = ((x μ).val - (y μ).val + j) % ell := by
    intro j
    rw [hps j, ReparamCDisjoint.pathSite_apply_self_val x μ j, Nat.mod_mod_of_dvd _ hdvdμ,
      mod_add_of_base ell (y μ).val (x μ).val j hdvdy hxb.1]
  have hother : ∀ (j : ℕ) (σ : Fin 3), σ ≠ μ →
      ((fun z => periodicLatticeShift z μ)^[j] x) σ = x σ := fun j σ hσ =>
    ReparamCDisjoint.pathSite_apply_ne x μ σ j hσ
  -- each term is `0` except at the interface index
  have hterm : ∀ j ∈ Finset.range ell,
      B ((fun z => periodicLatticeShift z μ)^[j] x, μ)
        = if j = ell - 1 - ((x μ).val - (y μ).val) then B (topOf hell hdvd hy, μ) else 0 := by
    intro j hj
    have hjlt : j < ell := Finset.mem_range.mp hj
    have hfit := coarse_block_fits hdvd hy μ
    by_cases hjeq : j = ell - 1 - ((x μ).val - (y μ).val)
    · subst hjeq
      rw [if_pos rfl]
      have hno : (x μ).val + (ell - 1 - ((x μ).val - (y μ).val)) < L μ + 1 := by omega
      have hvalj : (((fun z => periodicLatticeShift z μ)^[ell - 1 - ((x μ).val - (y μ).val)] x)
          μ).val = (x μ).val + (ell - 1 - ((x μ).val - (y μ).val)) := by
        rw [hps _, ReparamCDisjoint.pathSite_apply_self_val x μ _, Nat.mod_eq_of_lt hno]
      have hmemj : (fun z => periodicLatticeShift z μ)^[ell - 1 - ((x μ).val - (y μ).val)] x
          ∈ blockOf y ell := by
        refine mem_blockOf.mpr fun σ => ?_
        by_cases hσ : σ = μ
        · rw [hσ, hvalj]; omega
        · rw [hother _ σ hσ]; exact mem_blockOf.mp hx σ
      refine interface_eq_top hell hdvd hstrict hax hcurl hy μ _ hmemj ?_
      rw [hvalj]; omega
    · rw [if_neg hjeq]
      refine bond_zero_of_mod_ne hell hdvd hstrict hax hcurl _ ?_
      change (((fun z => periodicLatticeShift z μ)^[j] x) μ).val % ell ≠ ell - 1
      rw [hmodpath j]
      exact mod_ne_of_ne ell ((x μ).val - (y μ).val) j hr hjlt hjeq
  unfold lineIntegralValue
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ _ _,
    if_pos (Finset.mem_range.mpr hj0lt)]

/-! ### §5e — the theorem -/

/-- **THE TRANSVERSALITY THEOREM.** CMP99b p.428's printed subspace — `B = 0` on `⋃_{y∈Λ'} Ax(y)`
(CMP96 (2.121), `admissibleSubspaceInter`) together with `Q₁B = 0` (CMP96 (2.125),
`lineCoarseRestrict`) — meets the CURL-FREE subspace only at `0`. Unconditional in the real sector,
at every block side `ell` with `0 < ell`, `ell ∣ L μ + 1` and `ell < L μ + 1` (Bałaban's own regime:
more than one block per axis, blocks tiling exactly).

This is the transversality the dispatch asked for, and it holds for the class AS PRINTED — no clause
has to be added. The `Q₁` clause is genuinely load-bearing: without it the interface bonds survive
(§5f exhibits `ifaceField`, a NONZERO curl-free admissible field, so the theorem is not trivial and
`Q₁B = 0` is not redundant; `ifaceField_Q_ne_zero` reads that off this theorem). -/
theorem class_transverse_to_curlFree {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hstrict : ∀ μ : Fin 3, ell < L μ + 1)
    {B : Bond L → ℝ} (hax : B ∈ admissibleSubspaceInter L ell)
    (hQ : ∀ c : CoarseBond L ell, lineCoarseRestrict ell B c = 0)
    (hcurl : ∀ p : PeriodicLatticePlaquette L, curlValue B p = 0) : B = 0 := by
  classical
  funext b
  obtain ⟨x, μ⟩ := b
  by_cases hmod : (x μ).val % ell = ell - 1
  · -- an interface bond: `Q₁ = 0` at the coarse bond of its own block kills it
    have hymem : bcen ell x ∈ CoarseLattice L ell := bcen_mem ell x
    have hxmem : x ∈ blockOf (bcen ell x) ell := mem_blockOf_bcen hell x
    have hQc := hQ ((⟨bcen ell x, hymem⟩, μ) : CoarseBond L ell)
    unfold lineCoarseRestrict at hQc
    have hsum : ∑ x' ∈ blockOf (bcen ell x) ell, lineIntegralValue ell B x' μ
        = (blockOf (bcen ell x) ell).card * B (topOf hell hdvd hymem, μ) := by
      rw [Finset.sum_congr rfl fun x' hx' =>
        lineIntegral_eq_top hell hdvd hstrict hax hcurl hymem μ x' hx', Finset.sum_const]
      rw [nsmul_eq_mul]
    have hcardpos : 0 < (blockOf (bcen ell x) ell).card :=
      Finset.card_pos.mpr ⟨x, hxmem⟩
    have hne4 : (1 / (ell : ℝ) ^ 4) ≠ 0 := by
      have : ((ell : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      positivity
    have hzero : ((blockOf (bcen ell x) ell).card : ℝ) * B (topOf hell hdvd hymem, μ) = 0 := by
      have := hQc
      rw [hsum] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hne4
      · exact h
    have htop : B (topOf hell hdvd hymem, μ) = 0 := by
      have hcardne : ((blockOf (bcen ell x) ell).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h hcardne
      · exact h
    have hxtop : (x μ).val = ((bcen ell x) μ).val + ell - 1 := by
      have hmm := mod_eq_sub_of_mem_block hymem hxmem μ
      have hb := mem_blockOf.mp hxmem μ
      omega
    rw [Pi.zero_apply,
      interface_eq_top hell hdvd hstrict hax hcurl hymem μ x hxmem hxtop, htop]
  · rw [Pi.zero_apply]
    exact bond_zero_of_mod_ne hell hdvd hstrict hax hcurl (x, μ) hmod

/-! ### §5f — THE `Q₁` CLAUSE IS LOAD-BEARING: a NONZERO curl-free ADMISSIBLE field

`class_transverse_to_curlFree` would be trivial if the axial clause alone already forced `B = 0` on
curl-free fields. It does not. `ifaceField` — the indicator of the direction-`0` bonds sitting on a
block interface — is curl-free, satisfies CMP96 (2.121) at every `y ∈ Λ'` and `x ∈ B(y)`, and is
nonzero. So the theorem's second hypothesis `Q₁B = 0` is exactly what closes it, and (by the theorem
itself, contrapositively) `Q₁(ifaceField) ≠ 0`. -/

/-- **THE INTERFACE INDICATOR.** `1` on every direction-`0` bond whose base coordinate `0` is the
last site of its `ell`-window, `0` elsewhere. These are precisely the bonds `inblock_zero` cannot
reach. -/
def ifaceField (L : PeriodicLatticeExtent) (ell : ℕ) : Bond L → ℝ :=
  fun b => if b.2 = 0 ∧ (b.1 0).val % ell = ell - 1 then 1 else 0

theorem ifaceField_of_dir_ne {ell : ℕ} (b : Bond L) (h : b.2 ≠ 0) : ifaceField L ell b = 0 := by
  unfold ifaceField; rw [if_neg]; exact fun hc => h hc.1

theorem ifaceField_dir_zero {ell : ℕ} (x : PeriodicLatticeSite L) :
    ifaceField L ell (x, (0 : Fin 3)) = if (x 0).val % ell = ell - 1 then 1 else 0 := by
  unfold ifaceField
  by_cases h : (x 0).val % ell = ell - 1
  · rw [if_pos ⟨rfl, h⟩, if_pos h]
  · rw [if_neg (fun hc => h hc.2), if_neg h]

/-- **`ifaceField` IS CURL-FREE.** A plaquette not containing direction `0` reads four zeros. A
plaquette containing it reads its two direction-`0` bonds, whose base coordinates `0` agree (the
transverse shift does not move coordinate `0`), so they cancel. -/
theorem ifaceField_curl_zero {ell : ℕ} :
    ∀ p : PeriodicLatticePlaquette L, curlValue (ifaceField L ell) p = 0 := by
  intro p
  obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := p
  have hνval : (μ : ℕ) < (ν : ℕ) := hμν
  have hν0 : ν ≠ (0 : Fin 3) := by
    intro h
    rw [h] at hνval
    exact Nat.not_lt_zero _ hνval
  simp only [curlValue]
  by_cases hμ0 : μ = (0 : Fin 3)
  · subst hμ0
    rw [ifaceField_of_dir_ne ((periodicLatticeShift x 0, ν) : Bond L) hν0,
      ifaceField_of_dir_ne ((x, ν) : Bond L) hν0,
      ifaceField_dir_zero x, ifaceField_dir_zero (periodicLatticeShift x ν),
      shiftNe x ν 0 (fun hc => hν0 hc.symm)]
    ring
  · rw [ifaceField_of_dir_ne ((x, μ) : Bond L) hμ0,
      ifaceField_of_dir_ne ((periodicLatticeShift x ν, μ) : Bond L) hμ0,
      ifaceField_of_dir_ne ((periodicLatticeShift x μ, ν) : Bond L) hν0,
      ifaceField_of_dir_ne ((x, ν) : Bond L) hν0]
    ring

/-- **`ifaceField` SATISFIES CMP96 (2.121).** The staircase's direction-`0` segment runs over base
coordinates `0` in `[y_0, x_0)`, and `x_0 < y_0 + ell`, so it never reaches `y_0 + ell − 1`: the
staircase misses every interface bond. The other two segments carry no direction-`0` bond at all. -/
theorem ifaceField_axial {ell : ℕ} (hell : 0 < ell) :
    ifaceField L ell ∈ admissibleSubspaceInter L ell := by
  rw [mem_admissibleSubspaceInter]
  intro y hy x hx e he
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at he
  rcases he with (h2 | h1) | h0
  · rw [mem_axisSegment] at h2
    exact ifaceField_of_dir_ne e (by rw [h2.1]; decide)
  · rw [mem_axisSegment] at h1
    exact ifaceField_of_dir_ne e (by rw [h1.1]; decide)
  · rw [mem_axisSegment] at h0
    have hx0 := mem_blockOf.mp hx 0
    have hmin : min (y 0).val (x 0).val = (y 0).val := by omega
    have hmax : max (y 0).val (x 0).val = (x 0).val := by omega
    rw [hmin, hmax] at h0
    -- `e.1` lies in `B(y)`: coordinate `0` inside `[y_0, x_0)`, the others pinned to `x`'s
    have hemem : e.1 ∈ blockOf y ell := by
      rw [mem_blockOf]
      intro σ
      by_cases hσ : σ = 0
      · rw [hσ]; exact ⟨h0.2.2.1, by omega⟩
      · rw [h0.2.1 σ hσ]
        by_cases hσ1 : σ = 1
        · rw [hσ1, corner2, Function.update_self]; exact mem_blockOf.mp hx 1
        · have hσ2 : σ = 2 := by
            have hall : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
            rcases hall σ with h | h | h
            · exact absurd h hσ
            · exact absurd h hσ1
            · exact h
          rw [hσ2, corner2, Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1), corner1,
            Function.update_self]
          exact mem_blockOf.mp hx 2
    have hmod := mod_eq_sub_of_mem_block hy hemem 0
    unfold ifaceField
    rw [if_neg]
    intro hc
    rw [hmod] at hc
    omega

/-- **`ifaceField` IS NONZERO**, at any `ell` with `0 < ell ≤ L 0 + 1`: the direction-`0` bond based
at the site with coordinate `0` equal to `ell − 1` carries the value `1`. -/
theorem ifaceField_ne_zero {ell : ℕ} (hell : 0 < ell) (hstrict : ell < L 0 + 1) :
    ifaceField L ell ≠ (0 : Bond L → ℝ) := by
  classical
  intro h
  set xs : PeriodicLatticeSite L :=
    Function.update (fun σ => (⟨0, Nat.succ_pos _⟩ : Fin (L σ + 1))) 0
      ⟨ell - 1, by omega⟩ with hxs
  have h0 : (xs 0).val = ell - 1 := by rw [hxs]; simp
  have hmod : (xs 0).val % ell = ell - 1 := by rw [h0, Nat.mod_eq_of_lt (by omega)]
  have hval := congrFun h (xs, (0 : Fin 3))
  rw [ifaceField_dir_zero xs, if_pos hmod] at hval
  simp at hval

/-- **HENCE `Q₁(ifaceField) ≠ 0`** — read straight off `class_transverse_to_curlFree`, whose other
two hypotheses `ifaceField` satisfies while being nonzero. This is the kernel-checked statement that
the `Q₁B = 0` clause of CMP99b p.428's subspace is not redundant: drop it and the class is no longer
transverse to the curl-free fibre. -/
theorem ifaceField_Q_ne_zero {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hstrict : ∀ μ : Fin 3, ell < L μ + 1) :
    ¬ (∀ c : CoarseBond L ell, lineCoarseRestrict ell (ifaceField L ell) c = 0) := by
  intro hQ
  exact ifaceField_ne_zero hell (hstrict 0)
    (class_transverse_to_curlFree hell hdvd hstrict (ifaceField_axial hell) hQ
      ifaceField_curl_zero)

end RealSector

/-! ## §6 — THE COUNTEREXAMPLE DATUM IS NOT IN THE CURL-FREE FIBRE

The cheap check the dispatch asked to run first. `NilLevelTarget.loopField` is a plaquette
circulation, so its own plaquette carries curl `4·suTwoWitness ≠ 0`: under §5's fibre it is
excluded,
and `dstarDQuadForm (trivialU) (loopField m) > 0`. Contrast the tree's fibre
`ker Q_{S.fibre} ∩ {R(D*_U ·) = 0}`, which contains it (`NilLevelTarget.loopField_mem_fibre`). -/

theorem pA_ne_pB (m : ℕ) : pA m ≠ pB m := by
  intro h
  have := congrArg (fun s => (s 1).val) h
  rw [pA_c1, pB_c1] at this
  exact absurd this (by norm_num)

private theorem single_zero_site {L' : PeriodicLatticeExtent} (b : Bond L')
    (z : PeriodicLatticeSite L') (ν : Fin 3) (v : SuTwo) (h : b.1 ≠ z) :
    (Pi.single ((z, ν) : Bond L') v : Bond L' → SuTwo) b = 0 := by
  classical
  rw [Pi.single_apply, if_neg]
  intro hcon
  exact h (congrArg Prod.fst hcon)

private theorem single_zero_dir {L' : PeriodicLatticeExtent} (b : Bond L')
    (z : PeriodicLatticeSite L') (ν : Fin 3) (v : SuTwo) (h : b.2 ≠ ν) :
    (Pi.single ((z, ν) : Bond L') v : Bond L' → SuTwo) b = 0 := by
  classical
  rw [Pi.single_apply, if_neg]
  intro hcon
  exact h (congrArg Prod.snd hcon)

theorem loopField_at_pB_two (m : ℕ) : loopField m (pB m, 2) = suTwoWitness := by
  classical
  unfold loopField
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [single_zero_dir (pB m, 2) (pA m) 1 suTwoWitness (show (2 : Fin 3) ≠ 1 by decide),
    single_zero_dir (pB m, 2) (pC m) 1 suTwoWitness (show (2 : Fin 3) ≠ 1 by decide),
    single_zero_site (pB m, 2) (pA m) 2 suTwoWitness (fun hc => pA_ne_pB m hc.symm),
    Pi.single_eq_same]
  abel

theorem loopField_at_pC_one (m : ℕ) : loopField m (pC m, 1) = -suTwoWitness := by
  classical
  unfold loopField
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [single_zero_site (pC m, 1) (pA m) 1 suTwoWitness (fun hc => pA_ne_pC m hc.symm),
    single_zero_dir (pC m, 1) (pB m) 2 suTwoWitness (show (1 : Fin 3) ≠ 2 by decide),
    single_zero_dir (pC m, 1) (pA m) 2 suTwoWitness (show (1 : Fin 3) ≠ 2 by decide),
    Pi.single_eq_same]
  abel

theorem loopField_at_pA_two (m : ℕ) : loopField m (pA m, 2) = -suTwoWitness := by
  classical
  unfold loopField
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [single_zero_dir (pA m, 2) (pA m) 1 suTwoWitness (show (2 : Fin 3) ≠ 1 by decide),
    single_zero_dir (pA m, 2) (pC m) 1 suTwoWitness (show (2 : Fin 3) ≠ 1 by decide),
    single_zero_site (pA m, 2) (pB m) 2 suTwoWitness (pA_ne_pB m),
    Pi.single_eq_same]
  abel

/-- The plaquette the loop circulates: base `(1,0,0)`, directions `(1,2)`. -/
def loopPlaq (m : ℕ) : PeriodicLatticePlaquette (wExt m) :=
  (pA m, (⟨(1, 2), by decide⟩ : PeriodicPlaquetteDirections))

/-- **THE LOOP IS NOT CURL-FREE**: `(D_1 loopField)(loopPlaq) = 4·suTwoWitness ≠ 0`. So under §5's
fibre — the curl-free subspace, which is the zero set of the energy (3.159)'s inner integral
minimises — the counterexample datum is EXCLUDED. This is the check the dispatch asked to run
first, and it passes. -/
theorem loopField_curl_ne_zero (m : ℕ) :
    curlValueCovariant (trivialU (wExt m)) (loopField m) (loopPlaq m) ≠ 0 := by
  have hU : ∀ b : Bond (wExt m), RMap ((trivialU (wExt m)) b) = LinearMap.id := by
    intro b
    change RMap ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = LinearMap.id
    exact RMap_one
  have hval : curlValueCovariant (trivialU (wExt m)) (loopField m) (loopPlaq m)
      = (4 : ℝ) • suTwoWitness := by
    unfold curlValueCovariant loopPlaq
    simp only [hU, LinearMap.id_coe, id_eq]
    rw [NilLevelTarget.shift_pA_one, NilLevelTarget.shift_pA_two,
      loopField_at_pA_one, loopField_at_pB_two, loopField_at_pC_one, loopField_at_pA_two]
    module
  rw [hval]
  exact smul_ne_zero (by norm_num) suTwoWitness_ne_zero

/-- **AND THE CURL ENERGY AT THE LOOP IS STRICTLY POSITIVE** — `⟨A, D*_U D_U A⟩ > 0`, the quantity
whose vanishing is what `Δ_k(B) = 0` would require of a minimiser. -/
theorem loopField_dstarD_pos (m : ℕ) : 0 < dstarDQuadForm (trivialU (wExt m)) (loopField m) := by
  classical
  unfold dstarDQuadForm covPlaqInner
  refine Finset.sum_pos' (fun p _ => hsInner_self_nonneg _) ⟨loopPlaq m, Finset.mem_univ _, ?_⟩
  rcases lt_or_eq_of_le (hsInner_self_nonneg
    (curlValueCovariant (trivialU (wExt m)) (loopField m) (loopPlaq m))) with h | h
  · exact h
  · exact absurd (hsInner_self_eq_zero h.symm) (loopField_curl_ne_zero m)

/-! ### §4c — THE QUANTITATIVE SEPARATION: the corrected left-hand side is `O(ell⁻⁶)` at a spike

§2–§3 kill `NilLevelTarget`'s VANISHING mechanism. The other refutation in this tree,
`WitnessInequality.target_refuted`, is a RATE failure: it bounds the right-hand side above by a
quantity decaying in `ell` against a left-hand side (`bondEnergy wField = ‖suTwoWitness‖²`) that is
completely `ell`-independent. The corrected left-hand side is NOT `ell`-independent — at a single
spike it decays like `ell⁻⁶`, because `Q_{ell}` carries CMP96 (2.125)'s `1/ell⁴` weight and a
single spike contributes to at most `ell` of the `ell⁴` terms it averages.

This subsection proves that, generally in `L`, `ell`, `z`, `ν`, `v`, with an explicit constant. It
does NOT claim the rate refutation is repaired — that would need the exact right-hand side rate,
which is not computed here — it establishes the ONE fact the rate argument turns on: the two
left-hand sides scale differently, by `ell⁻⁶`. -/

/-- `Q_{ell}` of a single spike has norm at most `ell⁻³‖v‖`: exactly `ell⁻⁴·N·‖v‖` with
`N ≤ ell` the number of translation steps landing in the block (`Q_single_same_dir`), and `0` at
coarse bonds of a different direction (`Q_single_other_dir`). -/
theorem Q_single_norm_le {ell : ℕ} (hell : 0 < ell) (hle : ∀ μ : Fin 3, ell ≤ L μ + 1)
    (c : CoarseBond L ell) (z : PeriodicLatticeSite L) (ν : Fin 3) (v : SuTwo) :
    ‖lineCoarseRestrictCov (trivialU L) ell (Pi.single ((z, ν) : Bond L) v) c‖
      ≤ (1 / (ell : ℝ) ^ 3) * ‖v‖ := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := Nat.cast_pos.mpr hell
  by_cases hν : ν = c.2
  · subst hν
    rw [Q_single_same_dir c (hle c.2) z v]
    set N := ((Finset.range ell).filter
      (fun i => QOne.pathSite z c.2 (L c.2 + 1 - i) ∈ blockOf c.1.1 ell)).card with hN
    have hNle : (N : ℝ) ≤ (ell : ℝ) := by
      have : N ≤ ell := by
        rw [hN]
        calc _ ≤ (Finset.range ell).card := Finset.card_filter_le _ _
          _ = ell := Finset.card_range ell
      exact_mod_cast this
    have hnormeq : ‖(1 / (ell : ℝ) ^ 4) • ((N : ℝ) • v)‖
        = (1 / (ell : ℝ) ^ 4) * ((N : ℝ) * ‖v‖) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < 1 / (ell : ℝ) ^ 4),
        abs_of_nonneg (Nat.cast_nonneg N)]
    rw [hnormeq]
    have hstep : (1 / (ell : ℝ) ^ 4) * ((N : ℝ) * ‖v‖)
        ≤ (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) * ‖v‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right hNle (norm_nonneg v)
    refine le_trans hstep ?_
    rw [show (1 / (ell : ℝ) ^ 4) * ((ell : ℝ) * ‖v‖) = (1 / (ell : ℝ) ^ 3) * ‖v‖ by
      field_simp]
  · rw [Q_single_other_dir c z ν hν v, norm_zero]
    positivity

/-- **THE `ell⁻⁶` DECAY OF THE CORRECTED LEFT-HAND SIDE AT A SPIKE.** General in `L`, `ell`, `z`,
`ν`, `v`. The constant is the number of coarse bonds, symbolic on purpose — at the witness family
`wExt m` / `wEll m` there are exactly two blocks per axis, so it is `3·2³ = 24`, independent of `m`.
Compare `bondEnergy_single_eq`: the FINE left-hand side at the same datum is `‖v‖²`, with no
`ell` in
it at all. -/
theorem coarseUnitEnergy_single_le {ell : ℕ} (hell : 0 < ell) (hle : ∀ μ : Fin 3, ell ≤ L μ + 1)
    (z : PeriodicLatticeSite L) (ν : Fin 3) (v : SuTwo) :
    coarseUnitEnergy ell (trivialU L) (Pi.single ((z, ν) : Bond L) v)
      ≤ (Fintype.card (CoarseBond L ell) : ℝ) * ((1 / (ell : ℝ) ^ 6) * ‖v‖ ^ 2) := by
  classical
  have hbound : ∀ c ∈ (Finset.univ : Finset (CoarseBond L ell)),
      ‖lineCoarseRestrictCov (trivialU L) ell (Pi.single ((z, ν) : Bond L) v) c‖ ^ 2
        ≤ (1 / (ell : ℝ) ^ 6) * ‖v‖ ^ 2 := by
    intro c _
    have h := Q_single_norm_le hell hle c z ν v
    have hsq := mul_self_le_mul_self (norm_nonneg _) h
    rw [← pow_two, ← pow_two] at hsq
    refine le_trans hsq ?_
    rw [mul_pow]
    have : ((1 : ℝ) / (ell : ℝ) ^ 3) ^ 2 = 1 / (ell : ℝ) ^ 6 := by
      rw [div_pow, one_pow, ← pow_mul]
    rw [this]
  have hsum := Finset.sum_le_card_nsmul (Finset.univ : Finset (CoarseBond L ell))
    (fun c => ‖lineCoarseRestrictCov (trivialU L) ell (Pi.single ((z, ν) : Bond L) v) c‖ ^ 2)
    ((1 / (ell : ℝ) ^ 6) * ‖v‖ ^ 2) hbound
  unfold coarseUnitEnergy
  rw [nsmul_eq_mul, Finset.card_univ] at hsum
  exact hsum

/-- The FINE left-hand side at the same datum: `bondEnergy (Pi.single b v) = ‖v‖²`, with no `ell`
dependence. This is the whole content of §4c: at one and the same spike the two left-hand sides
differ by a factor `ell⁻⁶` up to the (bounded) coarse-bond count. -/
theorem bondEnergy_single_eq (b : Bond L) (v : SuTwo) :
    bondEnergy (Pi.single b v : Bond L → SuTwo) = ‖v‖ ^ 2 := by
  classical
  unfold bondEnergy
  have hstep : ∀ b' : Bond L, ‖(Pi.single b v : Bond L → SuTwo) b'‖ ^ 2
      = if b' = b then ‖v‖ ^ 2 else 0 := by
    intro b'
    by_cases hb : b' = b
    · rw [if_pos hb, hb, Pi.single_eq_same]
    · rw [if_neg hb, Pi.single_eq_of_ne hb, norm_zero]
      norm_num
  rw [Finset.sum_congr rfl (fun b' _ => hstep b'), Finset.sum_ite_eq' _ _ _,
    if_pos (Finset.mem_univ b)]

#print axioms coarseUnitEnergy_eq_zero_iff
#print axioms coarseUnitEnergy_eq_zero_of_mem_fibre
#print axioms Q_single_norm_le
#print axioms coarseUnitEnergy_single_le
#print axioms bondEnergy_single_eq
#print axioms fibre_element_cannot_refute
#print axioms loopField_coarseUnitEnergy_zero
#print axioms loopField_satisfies_corrected
#print axioms loopField_levels_disagree
#print axioms Q_wField_ne_zero
#print axioms coarseUnitEnergy_wField_pos
#print axioms corrected_target_domain_nonvacuous
#print axioms coarse_block_fits
#print axioms mod_eq_sub_of_mem_block
#print axioms inblock_zero
#print axioms bond_zero_of_mod_ne
#print axioms move_step
#print axioms pathSite_in_block
#print axioms push_step
#print axioms interface_eq_top
#print axioms lineIntegral_eq_top
#print axioms class_transverse_to_curlFree
#print axioms ifaceField_curl_zero
#print axioms ifaceField_axial
#print axioms ifaceField_ne_zero
#print axioms ifaceField_Q_ne_zero
#print axioms loopField_at_pB_two
#print axioms loopField_at_pC_one
#print axioms loopField_at_pA_two
#print axioms loopField_curl_ne_zero
#print axioms loopField_dstarD_pos
#print axioms coarseUnitEnergy_nonneg
#print axioms zeroSite_mem
#print axioms shiftVal
#print axioms shiftNe
#print axioms bcen_val
#print axioms bcen_mem
#print axioms mem_blockOf_bcen
#print axioms pushSite_apply_ne
#print axioms topOf_val
#print axioms topOf_mem
#print axioms ifaceField_of_dir_ne
#print axioms ifaceField_dir_zero
#print axioms pA_ne_pB

end AdalyFormal.Balaban.TransverseClass
