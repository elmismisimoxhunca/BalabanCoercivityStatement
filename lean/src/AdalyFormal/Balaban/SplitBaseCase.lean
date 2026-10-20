/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.ThirdLevelSandwich

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-!
# `SplitBaseCase.lean` — the base case for the object the lemma is ACTUALLY about

## The gap this module addresses

`CStarLevelProbe.regularU_bound_holds_where_schur_vanishes` proves that on the hypothesis domain of
the tree's regular-`U` coercivity theorem the Schur complement is IDENTICALLY ZERO. So the constant
`γ₀` the recursion `γ_{k+1} = (γ_k − δ)/q²` starts from is a constant for `dstarDQuadForm`, not for
`Δ_k`. This module supplies a lower bound on `Δ_k` itself, at split levels.

## THE FIRST QUESTION IS THE SHAPE, AND TWO CANDIDATE SHAPES ARE FALSE (§6, §7)

Before proving any bound, two candidate left-hand sides are refuted in the kernel.

1. **`γ · bondEnergy B ≤ Δ_k(B)` is false** on any domain containing a nonzero member of the Schur
   fibre `V = ker Q_{ℓ₀} ∩ ker R`. `deltaJ_shift_invariant` proves `Δ_k(B + v) = Δ_k(B)` for
   `v ∈ V`: the operator is BLIND to `V` while `bondEnergy` is not. At split levels `V` is nontrivial
   by design (`ThirdLevelWitness.V2_witL7_ne_bot`). See `fine_energy_base_case_refuted`.
2. **`γ · ⟨Q_{ℓ₀}B, Q_{ℓ₀}B⟩ ≤ Δ_k(B)` is also false.** `Δ_k` is a curl energy — a minimum of
   `‖d_UA‖²` over a fibre — so it vanishes at every CLOSED field (`deltaJ_eq_zero_of_closed`), and the
   CONSTANT field is closed while `Q_ℓ` fixes constants (`lineCoarse_constField`). See
   `coarse_bond_energy_base_case_refuted`. Independent corroboration from another lane and another
   witness: `CoarseCurlScaleTwo`'s header records that the fine axial gauge does NOT descend to the
   coarse lattice at fibre `ℓ₀ ≥ 2`.

So the only available shape is the **coarse CURL energy** — which is what CMP96 (2.128) carries on its
left-hand side and what the next level's Lemma 2.4 consumes.

## WHAT IS PROVED

**§4, headline** (`ell_mul_coarseCurlEnergy_le_deltaJ`), at `U = 1`, general block side `ℓ > 0`,
general compatible torus, general `levels`, general `B`, with no gauge condition, no smallness and no
restriction on `B`:

    ℓ · (coarse curl energy of Q_ℓ B)  ≤  ⟨B, Δ_k B⟩ .

**§5** the same on the corrected split object (`split_base_case`, typed by `LevelSplit`, so
`ℓ₀ = ℓ₁` is unstateable) and through the (3.157) reparametrisation (`split_base_case_sandwich`).

**§4b, general `U`** (`base_case_general_U`): the identical bound at EVERY background, in the
intrinsic `windowCurlEnergy`, conditional on ONE named `Prop` quantifying over no free data —

    WindowStokesAnnihilates ℓ U := ∀ v, Q_ℓ(U) v = 0 → ∀ P', windowSum (d_U v) P' = 0 .

`windowStokesAnnihilates_trivialU` proves it at `U = 1`, so the hypothesis class is inhabited, and
`windowCurlEnergy_trivialU` identifies the two energies there.

## METHOD — a Schur test, which is what the tree lacked

Every quantitative bound on `Δ_k` in this tree is POINTWISE in a coarse plaquette
(`ThirdLevelSchurGap.deltaJ_ge_coarse_curl_sq`) or sits at one witness point
(`third_level_energy_bound`, `ThirdLevelSandwich.sandwich_energy_bound`). A pointwise bound is not a
bound in a norm. Naming the plaquette block average as an operator and estimating it is the step:

* `windowSum` — the window sum `P_ℓ` before normalisation;
* `windowSum_curl` — `P_ℓ ∘ d = ℓ⁴ · ∂₁' ∘ Q_ℓ` (`ThirdLevelStokes.stokes_flat`, undestructured);
* `card_windowSet` — the window has `ℓ⁵` members;
* `plaq_multiplicity` — every fine plaquette is read at most `ℓ²` times;
* `windowSum_energy_le` — `Σ_{P'} ‖windowSum X‖² ≤ ℓ⁷ Σ_q ‖X q‖²`, i.e. `‖P_ℓ‖²_op ≤ 1/ℓ`;
* `lineCoarse_hjExtension` — `Q_ℓ(U)` does not see the fibre correction. **General `U`.**

The constant is composed from counted factors only: `ℓ⁸ / (ℓ⁵ · ℓ²) = ℓ`. So `γ_split = ℓ₀`.

## WHY THE GENERAL-`U` RESIDUAL HERE IS SMALLER THAN THE ONE THE TREE RECORDS

`ThirdLevelSchurGap` §5 splits `[STOKES-COMM-U]` into (i) a pairing-drift bound (closed there) and
(ii) an ε-annihilation of `D_U(V_U)` measured against `‖D_U v‖`, and records (ii) as a reverse
Poincaré on the fibre, hence near-circular. **In this route (ii) does not arise.** The route never
needs a dual vector orthogonal to `d_U(V_U)`; it needs the window sum to factor through `Q_ℓ(U)`, and
factoring through `Q_ℓ(U)` annihilates `ker Q_ℓ(U)` by an EXACT identity at every background
(`lineCoarse_hjExtension`). What remains is `WindowStokesAnnihilates` and nothing else.

## PRIOR ART REUSED, NOT REBUILT (LAW-19)

* `plaq_multiplicity` is the plaquette analogue of `QCLMNorm.sum_coarse_le` (same mechanism: block
  tiling `AdmissibleSubspace.coarseLattice_unique` plus shift injectivity, one level down).
* `windowSum` is the `𝔰𝔲(2)`-valued form of the pairing `ThirdLevelStokes.covPlaqInner_stokesU`
  already computes scalar-wise: `covPlaqInner (stokesU ℓ y hlt w) X = hsInner w (windowSum X P')`.
  It is named here because an operator estimate needs the vector, not one of its components.
* `stokes_flat`, `windowSet`, `windowPlaq`, `coarseCurlSuTwo`, `card_blockOf`,
  `coarseLattice_mem_fits`, `coarseLattice_exists` are all imported.

**TWO REBUILDS THIS LANE MADE, FOUND BY ITS OWN NESTED VALIDATOR AND DISCLOSED RATHER THAN HIDDEN.**
* `hsInner_self_eq_norm_sq` **already exists** as `LemmaAssembly.hsInner_self_eq_norm_sq`, identical
  statement, different proof (`inner_eq_hsInner` + `real_inner_self_eq_norm_sq` there; `Real.sq_sqrt`
  on the `rfl`-level norm here). Not imported because `LemmaAssembly` is not in this module's import
  cone; the two independent proofs are a de-correlated cross-check, but this WAS a reuse miss.
* `curlImageCovProjFaithful_add` **already exists** as
  `DeltaKUnitLevel.curlImageCovProjFaithful_add`, same conclusion. The copy here carries one fewer
  typeclass hypothesis. Again a reuse miss, not a reuse.
* `constField` is a near-duplicate of `MinSwap.constField` (that one takes `L` explicitly).
None of the three changes any statement; they are recorded because an undisclosed duplicate is how
this campaign lost a ~170-line rebuild once already.

## ⚠ HONEST SCOPE

* **`U = 1` unconditionally; general `U` CONDITIONALLY** on `WindowStokesAnnihilates`, which is NOT
  proved for `U ≠ 1` here. `CovariantOperators.witness_curvature_ne_zero` exhibits the curvature
  defect that blocks the exact flat identity at `U ≠ 1`; the honest general-`U` form is with an
  `O(α₁)` remainder, which this module does not build.
* **NO `CoerciveOn`-shaped base case is delivered, and §6/§7 prove none exists** for `Δ_k` on the
  un-gauge-fixed domain in either the fine or the coarse `L²` norm. The recursion
  `GammaRecursion.chain_gamma` consumes `γ‖x‖² ≤ ⟨x, Δx⟩`; `γ_split = ℓ₀` is a constant in a
  DIFFERENT pairing and must not be substituted into `δ ≤ γ(1 − q²)`.
* **`J = 0`** throughout (the `−2⟨H₁D̃⁽²⁾(B),J⟩` term of (3.156) is absent) — standing campaign scope.
* **`levels` abstract**, `R`-clause as-is; torus proxy for `ℤ³`.
* ~~Nothing here proves `LevelCorrectedCoercivityTargetUniform` and nothing here refutes it: that
  target is stated with `bondEnergy B̃` on the left AND an axial-gauge hypothesis on `B̃`, and §6's
  refutation does not apply to fields the axial gauge excludes. Whether the axial gauge excludes
  `V ∩ (free coordinates)` is NOT settled here.~~
  **STRUCK, and settled in §9 of this same module (S75, corrected before shipping).** The axial gauge
  at the CONSTRAINT level does not exclude the fibre at the FIBRE level:
  `levelCorrectedCoercivityTargetUniform_refuted` proves the target FALSE, with the explicit witness
  `Bax` meeting every one of its hypotheses. This module therefore does refute it, and the earlier
  sentence was written before §9 existed.

## ⚠ WHAT §9 DOES AND DOES NOT SAY ABOUT BAŁABAN

`LevelCorrectedCoercivityTargetUniform` is THIS TREE'S formalisation of p.428's `C*Δ_kC ≥ γ₀`, with
`bondEnergy B̃` chosen as the norm — a choice `ThirdLevelSchurGap`'s own docstring flags as an open
check ("the norm is `bondEnergy` … Bałaban's exact normalization is a flagged open check,
GOAL_LEMMA §3"). §9 refutes THE FORMALISATION. It does not refute CMP99b, and it does not say the
source is wrong: what it shows is that with the constraint-level axial gauge as the only gauge
condition, the fibre-level pure-gauge directions survive, and `Δ_k` cannot see them. A statement that
survives must either gauge-fix at the FIBRE level, or measure the fibre-level coarse curl instead —
which is what §4 does.
-/

namespace AdalyFormal.Balaban.SplitBaseCase

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU oneLevelUniv deltaKernelImageCovH)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette periodicLatticeShift_injective)
open AdalyFormal.Balaban.ThirdLevelStokes (windowSet windowPlaq coarseCurlSuTwo stokes_flat
  hsInner_smul_right hsInner_zero_right hsInner_sum_right)
open AdalyFormal.Balaban.CStarLevelCorrected (LevelSplit deltaKCorr)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — two elementary bridges -/

/-- `⟨X,X⟩ = ‖X‖²` on `𝔰𝔲(2)`; the shipped norm is `√⟨X,X⟩` by `rfl`
(`SuTwoInner.norm_eq_sqrt_hsInner`). -/
theorem hsInner_self_eq_norm_sq (X : SuTwo) : hsInner X X = ‖X‖ ^ 2 := by
  show hsInner X X = (Real.sqrt (hsInner X X)) ^ 2
  exact (Real.sq_sqrt (hsInner_self_nonneg X)).symm

/-- Cauchy–Schwarz for a finite sum of `𝔰𝔲(2)` vectors: `‖Σ a‖² ≤ card · Σ ‖a‖²`. -/
theorem norm_sum_sq_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → SuTwo) :
    ‖∑ t ∈ s, a t‖ ^ 2 ≤ (s.card : ℝ) * ∑ t ∈ s, ‖a t‖ ^ 2 := by
  have h1 : ‖∑ t ∈ s, a t‖ ≤ ∑ t ∈ s, ‖a t‖ := norm_sum_le s a
  have hnn : (0 : ℝ) ≤ ‖∑ t ∈ s, a t‖ := norm_nonneg _
  have h2 : (∑ t ∈ s, ‖a t‖) ^ 2 ≤ (s.card : ℝ) * ∑ t ∈ s, ‖a t‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  nlinarith [h1, hnn, h2]

#print axioms hsInner_self_eq_norm_sq
#print axioms norm_sum_sq_le

/-! ## §1 — the plaquette block-average `P_ℓ`, as a window SUM

`ThirdLevelStokes` builds the flat Stokes identity in the shape "window sum of fine curls `=` `ℓ⁴` ×
coarse curl of `Q_ℓ`". `windowSum` names the left-hand operator so that it can be estimated as an
operator, which is the step every existing site in this tree omitted: every quantitative bound on
`Δ_k` in the tree is pointwise in the coarse plaquette (`ThirdLevelSchurGap.deltaJ_ge_coarse_curl_sq`)
or at one witness point, and a pointwise bound is not a bound in a norm. -/

/-- `(P_ℓ X)(P')` **before normalisation**: the sum of `X` over the `ℓ × ℓ` window of fine plaquettes
attached to the coarse plaquette `P'`. -/
noncomputable def windowSum {ell : ℕ} (X : PeriodicLatticePlaquette L → SuTwo)
    (p : CoarsePlaquette L ell) : SuTwo :=
  ∑ t ∈ windowSet ell p.1.1, X (windowPlaq p.2.2 t)

/-- The window has `ℓ⁵ = ℓ³ · ℓ · ℓ` members: `ℓ³` block sites times the `ℓ × ℓ` offsets. -/
theorem card_windowSet {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    (windowSet ell y).card = ell ^ 5 := by
  unfold windowSet
  rw [Finset.card_product, Finset.card_product,
    card_blockOf y ell (coarseLattice_mem_fits hdvd hy)]
  simp only [Finset.card_range]
  ring

/-- **`P_ℓ ∘ d = ∂₁' ∘ Q_ℓ`, in `windowSum` form** — `ThirdLevelStokes.stokes_flat` restated with the
window sum named, and with the coarse plaquette left as a single variable rather than destructured
into `(y, μ, ν)`. This is the form the operator estimate consumes. -/
theorem windowSum_curl {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (v : Bond L → SuTwo) (p : CoarsePlaquette L ell) :
    windowSum (curlCovariantLM (trivialU L) v) p
      = ((ell : ℝ) ^ 4) • coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell v) p := by
  obtain ⟨⟨y, hy⟩, ⟨⟨μ, ν⟩, hlt⟩⟩ := p
  show (∑ t ∈ windowSet ell y, curlCovariantLM (trivialU L) v (windowPlaq hlt t)) = _
  have hwin : ∑ t ∈ windowSet ell y, curlCovariantLM (trivialU L) v (windowPlaq hlt t)
      = ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          curlValueCovariant (trivialU L) v (pathSite (pathSite x μ i) ν j, ⟨(μ, ν), hlt⟩) := by
    unfold windowSet windowPlaq
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_product]
    rfl
  rw [hwin, stokes_flat hell hdvd hy hlt v]

#print axioms card_windowSet
#print axioms windowSum_curl

/-! ## §2 — MULTIPLICITY: every fine plaquette is read at most `ℓ²` times by all coarse plaquettes

This is the combinatorial heart of the operator bound, and it is the plaquette analogue of
`QCLMNorm.sum_coarse_le` (which does the same count one level down, for bonds). The mechanism is
identical and is disclosed as such (LAW-19): for each FIXED offset pair `(i,j)` the reading map is
injective, by block tiling (`AdmissibleSubspace.coarseLattice_unique`) plus injectivity of the
lattice shift; there are `ℓ²` offset pairs and no more. -/

/-- For a fixed offset pair `(i,j)`, the map `(P', x) ↦ windowPlaq (x,i,j)` is injective on the pairs
with `x` in `P'`'s own block. -/
theorem read_plaq_injOn {ell i j : ℕ}
    (P₁ P₂ : (_ : CoarsePlaquette L ell) × PeriodicLatticeSite L)
    (h₁ : P₁ ∈ Finset.univ.sigma (fun p : CoarsePlaquette L ell => blockOf p.1.1 ell))
    (h₂ : P₂ ∈ Finset.univ.sigma (fun p : CoarsePlaquette L ell => blockOf p.1.1 ell))
    (heq : windowPlaq P₁.1.2.2 (P₁.2, i, j) = windowPlaq P₂.1.2.2 (P₂.2, i, j)) :
    P₁ = P₂ := by
  obtain ⟨p, xp⟩ := P₁
  obtain ⟨q, xq⟩ := P₂
  have hxp : xp ∈ blockOf p.1.1 ell := (Finset.mem_sigma.mp h₁).2
  have hxq : xq ∈ blockOf q.1.1 ell := (Finset.mem_sigma.mp h₂).2
  have hdir : p.2 = q.2 := by
    have h := congrArg Prod.snd heq
    unfold windowPlaq at h
    exact h
  have hsite : pathSite (pathSite xp p.2.1.1 i) p.2.1.2 j
      = pathSite (pathSite xq q.2.1.1 i) q.2.1.2 j := congrArg Prod.fst heq
  rw [hdir] at hsite
  have hinj2 : Function.Injective (fun z : PeriodicLatticeSite L => pathSite z q.2.1.2 j) :=
    Function.Injective.iterate (periodicLatticeShift_injective q.2.1.2) j
  have hinj1 : Function.Injective (fun z : PeriodicLatticeSite L => pathSite z q.2.1.1 i) :=
    Function.Injective.iterate (periodicLatticeShift_injective q.2.1.1) i
  have hx : xp = xq := hinj1 (hinj2 hsite)
  subst hx
  have hy : p.1.1 = q.1.1 := coarseLattice_unique ell p.1.2 q.1.2 hxp hxq
  have hpq : p = q := Prod.ext (Subtype.ext hy) hdir
  subst hpq
  rfl

/-- **THE MULTIPLICITY BOUND.** Summing a nonnegative plaquette weight over every coarse plaquette's
whole `ℓ × ℓ` window costs at most a factor `ℓ²`. No divisibility hypothesis: block UNIQUENESS is
unconditional (the same observation `QCLMNorm.sum_coarse_le` records for its bond twin). -/
theorem plaq_multiplicity {ell : ℕ} (g : PeriodicLatticePlaquette L → ℝ) (hg : ∀ q, 0 ≤ g q) :
    ∑ p : CoarsePlaquette L ell, ∑ t ∈ windowSet ell p.1.1, g (windowPlaq p.2.2 t)
      ≤ ((ell : ℝ) ^ 2) * ∑ q : PeriodicLatticePlaquette L, g q := by
  classical
  have hstep : ∀ i j : ℕ,
      ∑ p : CoarsePlaquette L ell, ∑ x ∈ blockOf p.1.1 ell, g (windowPlaq p.2.2 (x, i, j))
        ≤ ∑ q : PeriodicLatticePlaquette L, g q := by
    intro i j
    set T : Finset ((_ : CoarsePlaquette L ell) × PeriodicLatticeSite L) :=
      Finset.univ.sigma (fun p : CoarsePlaquette L ell => blockOf p.1.1 ell) with hT
    set Ψ : ((_ : CoarsePlaquette L ell) × PeriodicLatticeSite L) →
        PeriodicLatticePlaquette L :=
      fun P => windowPlaq P.1.2.2 (P.2, i, j) with hΨ
    have hsig : ∑ p : CoarsePlaquette L ell, ∑ x ∈ blockOf p.1.1 ell,
          g (windowPlaq p.2.2 (x, i, j)) = ∑ P ∈ T, g (Ψ P) := by
      rw [hT, hΨ]
      exact Finset.sum_sigma' Finset.univ (fun p : CoarsePlaquette L ell => blockOf p.1.1 ell)
        (fun p x => g (windowPlaq p.2.2 (x, i, j)))
    rw [hsig]
    have himg : ∑ q ∈ T.image Ψ, g q = ∑ P ∈ T, g (Ψ P) :=
      Finset.sum_image (fun P hP P' hP' h => read_plaq_injOn P P' hP hP' h)
    rw [← himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun q _ _ => hg q
  have hsplit : ∀ p : CoarsePlaquette L ell,
      ∑ t ∈ windowSet ell p.1.1, g (windowPlaq p.2.2 t)
        = ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
            ∑ x ∈ blockOf p.1.1 ell, g (windowPlaq p.2.2 (x, i, j)) := by
    intro p
    have h1 : ∑ t ∈ windowSet ell p.1.1, g (windowPlaq p.2.2 t)
        = ∑ x ∈ blockOf p.1.1 ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
            g (windowPlaq p.2.2 (x, i, j)) := by
      unfold windowSet
      rw [Finset.sum_product]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_product _ _ _
    rw [h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  calc ∑ p : CoarsePlaquette L ell, ∑ t ∈ windowSet ell p.1.1, g (windowPlaq p.2.2 t)
      = ∑ p : CoarsePlaquette L ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          ∑ x ∈ blockOf p.1.1 ell, g (windowPlaq p.2.2 (x, i, j)) :=
        Finset.sum_congr rfl fun p _ => hsplit p
    _ = ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, ∑ p : CoarsePlaquette L ell,
          ∑ x ∈ blockOf p.1.1 ell, g (windowPlaq p.2.2 (x, i, j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ ∑ _i ∈ Finset.range ell, ∑ _j ∈ Finset.range ell,
          ∑ q : PeriodicLatticePlaquette L, g q :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hstep i j
    _ = ((ell : ℝ) ^ 2) * ∑ q : PeriodicLatticePlaquette L, g q := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

#print axioms read_plaq_injOn
#print axioms plaq_multiplicity

/-! ## §3 — the operator bound `‖P_ℓ‖² ≤ 1/ℓ` (in window-sum normalisation, `‖windowSum‖² ≤ ℓ⁷‖·‖²`) -/

/-- **THE OPERATOR ESTIMATE.** `Σ_{P'} ‖(windowSum X)(P')‖² ≤ ℓ⁷ · Σ_q ‖X(q)‖²`. The two factors are
counted, not fitted: `ℓ⁵` from Cauchy–Schwarz over the window (`card_windowSet`) and `ℓ²` from the
multiplicity (`plaq_multiplicity`). Divided by the `ℓ⁴` of `windowSum_curl` twice, this is the Schur
test `‖P_ℓ‖²_op ≤ ℓ⁷/ℓ⁸ = 1/ℓ`. -/
theorem windowSum_energy_le {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (X : PeriodicLatticePlaquette L → SuTwo) :
    ∑ p : CoarsePlaquette L ell, ‖windowSum X p‖ ^ 2
      ≤ ((ell : ℝ) ^ 7) * ∑ q : PeriodicLatticePlaquette L, ‖X q‖ ^ 2 := by
  classical
  have hpt : ∀ p : CoarsePlaquette L ell,
      ‖windowSum X p‖ ^ 2
        ≤ ((ell : ℝ) ^ 5) * ∑ t ∈ windowSet ell p.1.1, ‖X (windowPlaq p.2.2 t)‖ ^ 2 := by
    intro p
    have hcs := norm_sum_sq_le (windowSet ell p.1.1) (fun t => X (windowPlaq p.2.2 t))
    rw [card_windowSet hdvd p.1.2] at hcs
    have hcast : (((ell ^ 5 : ℕ)) : ℝ) = ((ell : ℝ) ^ 5) := by push_cast; ring
    rw [hcast] at hcs
    exact hcs
  calc ∑ p : CoarsePlaquette L ell, ‖windowSum X p‖ ^ 2
      ≤ ∑ p : CoarsePlaquette L ell,
          ((ell : ℝ) ^ 5) * ∑ t ∈ windowSet ell p.1.1, ‖X (windowPlaq p.2.2 t)‖ ^ 2 :=
        Finset.sum_le_sum fun p _ => hpt p
    _ = ((ell : ℝ) ^ 5) * ∑ p : CoarsePlaquette L ell,
          ∑ t ∈ windowSet ell p.1.1, ‖X (windowPlaq p.2.2 t)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ ((ell : ℝ) ^ 5) * (((ell : ℝ) ^ 2) * ∑ q : PeriodicLatticePlaquette L, ‖X q‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact plaq_multiplicity (fun q => ‖X q‖ ^ 2) (fun q => by positivity)
    _ = ((ell : ℝ) ^ 7) * ∑ q : PeriodicLatticePlaquette L, ‖X q‖ ^ 2 := by ring

#print axioms windowSum_energy_le

/-! ## §4 — the coarse curl energy, and the base-case inequality at `U = 1` -/

/-- **The coarse curl energy** `Σ_{P'} |∂₁'B(P')|²` — the `L²` norm of the coarse curl of a coarse
bond field. This is the quantity CMP96 (2.128)'s left-hand side is built from, and it is the
quantity the NEXT level's Lemma 2.4 consumes. -/
noncomputable def coarseCurlEnergy {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) : ℝ :=
  ∑ p : CoarsePlaquette L ell, hsInner (coarseCurlSuTwo hdvd B p) (coarseCurlSuTwo hdvd B p)

theorem coarseCurlEnergy_nonneg {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) : 0 ≤ coarseCurlEnergy hdvd B :=
  Finset.sum_nonneg fun _p _ => hsInner_self_nonneg _

/-- The Schur fibre `V` is invisible to `Q_ℓ`: the `hj` correction has zero coarse field, so the
coarse field of the corrected extension equals the coarse field of `B` itself. -/
theorem lineCoarse_hjExtension {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    lineCoarseRestrictCovLM U ell (hjExtensionCovFaithful ell levels U B)
      = lineCoarseRestrictCovLM U ell B := by
  have hmem := hjCorrectionCovFaithful_mem ell levels U B
  have hzero : lineCoarseRestrictCovLM U ell (hjCorrectionCovFaithful ell levels U B) = 0 :=
    (mem_gaugeConstraintSubspaceCovFaithful.mp hmem).1
  show lineCoarseRestrictCovLM U ell (B + hjCorrectionCovFaithful ell levels U B) = _
  rw [map_add, hzero, add_zero]

/-- The energy of an ABSTRACT coarse-curl map, so the base case can be stated once and instantiated
at `U = 1` (where the map is `coarseCurlSuTwo`) and, conditionally, at general `U`. -/
noncomputable def ccEnergyOf {ell : ℕ}
    (cc : (CoarseBond L ell → SuTwo) → CoarsePlaquette L ell → SuTwo)
    (B : CoarseBond L ell → SuTwo) : ℝ :=
  ∑ p : CoarsePlaquette L ell, hsInner (cc B p) (cc B p)

theorem ccEnergyOf_nonneg {ell : ℕ}
    (cc : (CoarseBond L ell → SuTwo) → CoarsePlaquette L ell → SuTwo)
    (B : CoarseBond L ell → SuTwo) : 0 ≤ ccEnergyOf cc B :=
  Finset.sum_nonneg fun _p _ => hsInner_self_nonneg _

/-- **THE BASE CASE, from window factoring alone.** If the window sum of `d_U` FACTORS through
`Q_ℓ(U)` via some coarse-curl map `cc` — that is, if `P_ℓ ∘ d_U = ∂₁'_U ∘ Q_ℓ(U)` in the window
normalisation — then

  `ℓ · (cc-energy of Q_ℓ(U) B)  ≤  ⟨B, Δ_k B⟩`,

for EVERY background `U`, every level list, every field. The constant `ℓ` is composed from counted
factors only: `ℓ⁸` (two copies of `windowSum`'s `ℓ⁴`) against `ℓ⁵ · ℓ²` (window size × multiplicity).

**What this buys.** The Schur fibre `V = ker Q_ℓ(U) ∩ ker R` is annihilated for free, because a
functional factoring through `Q_ℓ(U)` cannot see `ker Q_ℓ(U)` — `lineCoarse_hjExtension`, which is
proved here for GENERAL `U`. So the whole general-`U` question collapses onto the factoring
hypothesis and nothing else. (Compare `ThirdLevelSchurGap` §5, which splits the general-`U` residual
into a pairing half and an "ε-annihilation of `D_U(V_U)`" half and records the second as
near-circular: in this route the second half is not an estimate at all, it is an identity.)

`cc` is a ∀-bound HYPOTHESIS, never an ∃ over free data (S91): the caller must SUPPLY a map making
the identity true. `windowSum_curl` supplies one at `U = 1` — see `ell_mul_coarseCurlEnergy_le_deltaJ`
— so the hypothesis class is inhabited and the theorem is not about an empty class. -/
theorem base_case_of_window_factoring {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (cc : (CoarseBond L ell → SuTwo) → CoarsePlaquette L ell → SuTwo)
    (hfac : ∀ (v : Bond L → SuTwo) (p : CoarsePlaquette L ell),
      windowSum (curlCovariantLM U v) p
        = ((ell : ℝ) ^ 4) • cc (lineCoarseRestrictCovLM U ell v) p)
    (B : Bond L → SuTwo) :
    (ell : ℝ) * ccEnergyOf cc (lineCoarseRestrictCovLM U ell B)
      ≤ deltaJQuadFormCovFaithful ell levels U B := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set A : Bond L → SuTwo := hjExtensionCovFaithful ell levels U B with hA
  set X : PeriodicLatticePlaquette L → SuTwo := curlCovariantLM U A with hX
  -- the Schur complement IS `‖X‖²`
  have hdelta : deltaJQuadFormCovFaithful ell levels U B
      = ∑ q : PeriodicLatticePlaquette L, ‖X q‖ ^ 2 := by
    show covPlaqInner X X = _
    unfold covPlaqInner
    exact Finset.sum_congr rfl fun q _ => hsInner_self_eq_norm_sq (X q)
  -- the window sum of `X` sees the coarse curl of `Q_ℓ B` — the fibre is invisible to `Q_ℓ`
  have hws : ∀ p : CoarsePlaquette L ell,
      windowSum X p
        = ((ell : ℝ) ^ 4) • cc (lineCoarseRestrictCovLM U ell B) p := by
    intro p
    rw [hX, hfac A p, lineCoarse_hjExtension levels U B]
  -- pointwise: `ℓ⁸ ‖cc(p)‖² = ‖windowSum X p‖²`
  have hpt : ∀ p : CoarsePlaquette L ell,
      ((ell : ℝ) ^ 8) *
          hsInner (cc (lineCoarseRestrictCovLM U ell B) p)
            (cc (lineCoarseRestrictCovLM U ell B) p)
        = ‖windowSum X p‖ ^ 2 := by
    intro p
    rw [hws p, norm_smul, Real.norm_eq_abs, mul_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((ell : ℝ) ^ 4)),
      hsInner_self_eq_norm_sq]
    ring
  have hsum : ((ell : ℝ) ^ 8) * ccEnergyOf cc (lineCoarseRestrictCovLM U ell B)
      = ∑ p : CoarsePlaquette L ell, ‖windowSum X p‖ ^ 2 := by
    unfold ccEnergyOf
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => hpt p
  have hmain : ((ell : ℝ) ^ 8) * ccEnergyOf cc (lineCoarseRestrictCovLM U ell B)
      ≤ ((ell : ℝ) ^ 7) * deltaJQuadFormCovFaithful ell levels U B := by
    rw [hsum, hdelta]
    exact windowSum_energy_le hdvd X
  have h7 : (0 : ℝ) < ((ell : ℝ) ^ 7) := by positivity
  nlinarith [hmain, h7, hellR, ccEnergyOf_nonneg cc (lineCoarseRestrictCovLM U ell B)]

/-- **THE BASE CASE, at `U = 1` and general block side `ℓ`.**

  `ℓ · (coarse curl energy of Q_ℓ B)  ≤  ⟨B, Δ_k B⟩`.

General in the block side `ℓ > 0`, the compatible torus, the level list, and the fine field `B`. No
witness, no smallness, no gauge condition, no restriction on `B`. -/
theorem ell_mul_coarseCurlEnergy_le_deltaJ {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels (trivialU L)).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    (ell : ℝ) * coarseCurlEnergy hdvd (lineCoarseRestrictCovLM (trivialU L) ell B)
      ≤ deltaJQuadFormCovFaithful ell levels (trivialU L) B :=
  base_case_of_window_factoring hell hdvd levels (trivialU L) (coarseCurlSuTwo hdvd)
    (fun v p => windowSum_curl hell hdvd v p) B

#print axioms lineCoarse_hjExtension
#print axioms base_case_of_window_factoring
#print axioms ell_mul_coarseCurlEnergy_le_deltaJ

/-! ### §4b — THE GENERAL-`U` FORM, and the single primitive it needs

`base_case_of_window_factoring` asks for a coarse-curl MAP. A weaker and cleaner hypothesis
suffices, and it quantifies over no data at all: that the window sum of `d_U` ANNIHILATES
`ker Q_ℓ(U)`. With it, the base case holds at every background `U`, with the same constant `ℓ`, in
the intrinsic energy `windowCurlEnergy` — which at `U = 1` IS the coarse curl energy of `Q_ℓ B`.

**This is the exact residual for the general-`U` case, and it is strictly smaller than the one the
tree records.** `ThirdLevelSchurGap` §5 splits `[STOKES-COMM-U]` into (i) a pairing-drift bound
(closed there) and (ii) an ε-annihilation of `D_U(V_U)` measured against `‖D_U v‖`, noting (ii) is a
reverse Poincaré on the fibre and therefore near-circular. In the route below, (ii) does not appear:
the fibre is annihilated by `lineCoarse_hjExtension`, an EXACT identity at every `U`. What is left is
`WindowStokesAnnihilates` alone. -/

/-- The intrinsic window-curl energy at background `U`: `ℓ⁻⁸ Σ_{P'} ‖(P_ℓ d_U B)(P')‖²`. -/
noncomputable def windowCurlEnergy (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) : ℝ :=
  (1 / (ell : ℝ) ^ 8) *
    ∑ p : CoarsePlaquette L ell, ‖windowSum (ell := ell) (curlCovariantLM U B) p‖ ^ 2

theorem windowCurlEnergy_nonneg (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) : 0 ≤ windowCurlEnergy ell U B := by
  unfold windowCurlEnergy
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _p _ => by positivity)

/-- **THE NAMED PRIMITIVE.** No existential, no free data: a `Prop` about `(ell, U)` only. -/
def WindowStokesAnnihilates (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop :=
  ∀ v : Bond L → SuTwo, lineCoarseRestrictCovLM U ell v = 0 →
    ∀ p : CoarsePlaquette L ell, windowSum (ell := ell) (curlCovariantLM U v) p = 0

/-- `windowSum` is additive in its plaquette-field argument. -/
theorem windowSum_add {ell : ℕ} (X Y : PeriodicLatticePlaquette L → SuTwo)
    (p : CoarsePlaquette L ell) :
    windowSum (X + Y) p = windowSum X p + windowSum Y p := by
  unfold windowSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => rfl

/-- **THE BASE CASE AT GENERAL `U`, conditional on `WindowStokesAnnihilates` and nothing else.** -/
theorem base_case_general_U {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (hann : WindowStokesAnnihilates ell U) (B : Bond L → SuTwo) :
    (ell : ℝ) * windowCurlEnergy ell U B ≤ deltaJQuadFormCovFaithful ell levels U B := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set X : PeriodicLatticePlaquette L → SuTwo :=
    curlCovariantLM U (hjExtensionCovFaithful ell levels U B) with hX
  have hdelta : deltaJQuadFormCovFaithful ell levels U B
      = ∑ q : PeriodicLatticePlaquette L, ‖X q‖ ^ 2 := by
    show covPlaqInner X X = _
    unfold covPlaqInner
    exact Finset.sum_congr rfl fun q _ => hsInner_self_eq_norm_sq (X q)
  -- the correction is invisible to the window sum
  have hsplit : ∀ p : CoarsePlaquette L ell,
      windowSum X p = windowSum (curlCovariantLM U B) p := by
    intro p
    have hcurl : X = curlCovariantLM U B
        + curlCovariantLM U (hjCorrectionCovFaithful ell levels U B) := by
      rw [hX]
      show curlCovariantLM U (B + hjCorrectionCovFaithful ell levels U B) = _
      exact map_add _ _ _
    rw [hcurl, windowSum_add,
      hann (hjCorrectionCovFaithful ell levels U B)
        (mem_gaugeConstraintSubspaceCovFaithful.mp
          (hjCorrectionCovFaithful_mem ell levels U B)).1 p, add_zero]
  have hmain : ∑ p : CoarsePlaquette L ell, ‖windowSum (curlCovariantLM U B) p‖ ^ 2
      ≤ ((ell : ℝ) ^ 7) * deltaJQuadFormCovFaithful ell levels U B := by
    rw [hdelta, ← Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => congrArg (‖·‖ ^ 2) (hsplit p))]
    exact windowSum_energy_le hdvd X
  have hnn : (0 : ℝ) ≤ ∑ p : CoarsePlaquette L ell, ‖windowSum (curlCovariantLM U B) p‖ ^ 2 :=
    Finset.sum_nonneg fun _p _ => by positivity
  unfold windowCurlEnergy
  have hne : ((ell : ℝ)) ≠ 0 := ne_of_gt hellR
  have h7 : (0 : ℝ) < ((ell : ℝ) ^ 7) := by positivity
  have hrw : (ell : ℝ) * ((1 / (ell : ℝ) ^ 8) *
      ∑ p : CoarsePlaquette L ell, ‖windowSum (ell := ell) (curlCovariantLM U B) p‖ ^ 2)
      = (∑ p : CoarsePlaquette L ell, ‖windowSum (ell := ell) (curlCovariantLM U B) p‖ ^ 2)
        / (ell : ℝ) ^ 7 := by
    field_simp
  rw [hrw, div_le_iff₀ h7, mul_comm]
  exact hmain

/-- **THE PRIMITIVE HOLDS AT `U = 1`**, so `base_case_general_U` is not a statement about an empty
hypothesis class. -/
theorem windowStokesAnnihilates_trivialU {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    WindowStokesAnnihilates ell (trivialU L) := by
  intro v hv p
  rw [windowSum_curl hell hdvd v p, hv]
  have hz : coarseCurlSuTwo hdvd (0 : CoarseBond L ell → SuTwo) p = 0 := by
    unfold coarseCurlSuTwo
    show (0 : SuTwo) + 0 - 0 - 0 = 0
    abel
  rw [hz, smul_zero]

/-- At `U = 1`, `windowCurlEnergy` IS the coarse curl energy of `Q_ℓ B` — the `ℓ⁻⁸` cancels the two
copies of `windowSum_curl`'s `ℓ⁴` exactly. -/
theorem windowCurlEnergy_trivialU {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → SuTwo) :
    windowCurlEnergy ell (trivialU L) B
      = coarseCurlEnergy hdvd (lineCoarseRestrictCovLM (trivialU L) ell B) := by
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have h8 : ((ell : ℝ) ^ 8) ≠ 0 := by positivity
  unfold windowCurlEnergy coarseCurlEnergy
  have hterm : ∀ p : CoarsePlaquette L ell,
      ‖windowSum (ell := ell) (curlCovariantLM (trivialU L) B) p‖ ^ 2
        = ((ell : ℝ) ^ 8) *
            hsInner (coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell B) p)
              (coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell B) p) := by
    intro p
    rw [windowSum_curl hell hdvd B p, norm_smul, Real.norm_eq_abs, mul_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((ell : ℝ) ^ 4)),
      hsInner_self_eq_norm_sq]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.mul_sum]
  field_simp

#print axioms windowCurlEnergy_nonneg
#print axioms windowSum_add
#print axioms base_case_general_U
#print axioms windowStokesAnnihilates_trivialU
#print axioms windowCurlEnergy_trivialU

/-! ## §5 — the same statement on the SPLIT object, and on the `C*Δ_kC` sandwich -/

/-- **THE SPLIT-LEVEL BASE CASE.** `deltaKCorr S levels U = deltaJQuadFormCovFaithful S.fibre …`
definitionally, so §4 lands directly on the corrected object. `S.fibre_pos` discharges `0 < ℓ₀` from
the `LevelSplit` structure itself; `S.proper` guarantees `ℓ₀ ≠ ℓ₁`, which §7 shows is exactly the
condition under which the left-hand side is not identically zero. -/
theorem split_base_case (S : LevelSplit) (hdvd : ∀ μ : Fin 3, S.fibre ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful S.fibre levels (trivialU L)).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    ((S.fibre : ℕ) : ℝ) *
        coarseCurlEnergy hdvd (lineCoarseRestrictCovLM (trivialU L) S.fibre B)
      ≤ deltaKCorr S levels (trivialU L) B :=
  ell_mul_coarseCurlEnergy_le_deltaJ S.fibre_pos hdvd levels B

/-- The same through the (3.157) reparametrisation `C`: a lower bound on the corrected SANDWICH
`⟨B̃, C*Δ_kC B̃⟩`, in the coarse curl energy of `Q_{ℓ₀}(C B̃)`. -/
theorem split_base_case_sandwich (S : LevelSplit) (hdvd : ∀ μ : Fin 3, S.fibre ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful S.fibre levels (trivialU L)).HasOrthogonalProjection]
    (Dinv : CoarseBond L S.constr → (SuTwo →ₗ[ℝ] SuTwo)) (Btil : Bond L → SuTwo) :
    ((S.fibre : ℕ) : ℝ) *
        coarseCurlEnergy hdvd (lineCoarseRestrictCovLM (trivialU L) S.fibre
          (AdalyFormal.Balaban.FullReparamC.fullC (trivialU L) S.constr Dinv Btil))
      ≤ AdalyFormal.Balaban.CStarLevelCorrected.cStarDeltaKCFormCorr S levels (trivialU L)
          Dinv Btil :=
  split_base_case S hdvd levels _

#print axioms split_base_case
#print axioms split_base_case_sandwich

/-! ## §6 — WHY THE BASE CASE CANNOT BE STATED IN `bondEnergy`

This section is the reason §4's left-hand side is a COARSE energy and not `bondEnergy B`. It is a
statement about the object, not about the difficulty of proving anything.

`Δ_k` is the Schur complement over the fibre `V = ker Q_{ℓ₀} ∩ ker R`; its value at `B` depends only
on `B` modulo `V` (`deltaJ_shift_invariant`). So `Δ_k` is blind to the part of `B` living in `V`,
while `bondEnergy` is not. Any inequality `γ · bondEnergy B ≤ Δ_k(B)` with `γ > 0` is therefore FALSE
at every nonzero member of `V` — and at split levels `V` is nontrivial by design
(`ThirdLevelWitness.V2_witL7_ne_bot`). -/

/-- The projection onto the curl image is additive (it is a composite of linear maps). -/
theorem curlImageCovProjFaithful_add (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A₁ A₂ : PeriodicLatticePlaquette L → SuTwo) :
    curlImageCovProjFaithful ell levels U (A₁ + A₂)
      = curlImageCovProjFaithful ell levels U A₁ + curlImageCovProjFaithful ell levels U A₂ := by
  unfold curlImageCovProjFaithful
  rw [map_add, map_add, map_add]

/-- **`Δ_k` IS BLIND TO THE FIBRE.** Shifting `B` by any member of the Schur fibre `V` leaves the
Schur complement unchanged. -/
theorem deltaJ_shift_invariant (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B v : Bond L → SuTwo) (hv : v ∈ gaugeConstraintSubspaceCovFaithful ell levels U) :
    deltaJQuadFormCovFaithful ell levels U (B + v)
      = deltaJQuadFormCovFaithful ell levels U B := by
  have htarget : hjCorrectionTargetCovFaithful ell levels U (B + v)
      = hjCorrectionTargetCovFaithful ell levels U B := by
    unfold hjCorrectionTargetCovFaithful
    rw [map_add, curlImageCovProjFaithful_add,
      curlImageCovProjFaithful_fixes ell levels U (curl_mem_curlImageCovFaithful_of_mem hv)]
    abel
  have hrw : ∀ A : Bond L → SuTwo, deltaJQuadFormCovFaithful ell levels U A
      = covPlaqInner (hjCorrectionTargetCovFaithful ell levels U A)
          (hjCorrectionTargetCovFaithful ell levels U A) := by
    intro A
    unfold deltaJQuadFormCovFaithful
    rw [curlCov_hjExtensionCovFaithful]
  rw [hrw (B + v), hrw B, htarget]

/-- **THE SHAPE REFUTATION.** No positive `γ` makes `γ · bondEnergy · ≤ Δ_k ·` hold on a domain
containing a nonzero member of the Schur fibre. The proof needs nothing but the vanishing of `Δ_k`
on `V` — no smallness, no level condition, no torus condition.

This is why the base case that feeds the recursion must be stated in a COARSE energy: `bondEnergy`
measures a direction the operator cannot see. -/
theorem fine_energy_base_case_refuted (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    {γ : ℝ} (hγ : 0 < γ) (v : Bond L → SuTwo)
    (hv : v ∈ gaugeConstraintSubspaceCovFaithful ell levels U) (hvE : 0 < bondEnergy v) :
    ¬ (γ * bondEnergy v ≤ deltaJQuadFormCovFaithful ell levels U v) := by
  rw [deltaJQuadFormCovFaithful_eq_zero_of_mem_V ell levels U v hv]
  exact not_le.mpr (mul_pos hγ hvE)

#print axioms curlImageCovProjFaithful_add
#print axioms deltaJ_shift_invariant
#print axioms fine_energy_base_case_refuted

/-! ## §7 — THE COARSE **BOND** ENERGY IS ALSO UNREACHABLE, and the reason is a closed form

§6 rules out `bondEnergy B`. This section rules out the next candidate, the coarse `L²` energy
`⟨Q_ℓ B, Q_ℓ B⟩` (`massCorr`), and it does so with a witness so simple it needs no lattice geometry:
the CONSTANT field. Its curl vanishes identically, so `Δ_k` vanishes at it; its coarse average is the
same constant, so its coarse bond energy is strictly positive.

The structural reading: `Δ_k` is a CURL energy (a minimum of `‖dA‖²` over a fibre), and a curl energy
cannot dominate an `L²` norm without a gauge condition — closed forms are free. The gauge condition
is what the (3.157) reparametrisation `C` is supposed to supply; `CoarseCurlScaleTwo`'s header
records, from a different lane and a different witness, that the FINE axial gauge does not descend to
the coarse lattice at fibre `ℓ₀ ≥ 2`, so `C` does not supply it at the coarse level either. Both
observations point at the same missing object. -/

/-- The constant `𝔰𝔲(2)` bond field. -/
noncomputable def constField (w : SuTwo) : Bond L → SuTwo := fun _ => w

/-- A constant field is CLOSED: its flat curl is identically zero (the four terms cancel in pairs). -/
theorem curl_constField (w : SuTwo) :
    curlCovariantLM (trivialU L) (constField w) = 0 := by
  funext p
  show curlValueCovariant (trivialU L) (constField w) p = (0 : SuTwo)
  rw [AdalyFormal.Balaban.CovU1Reduction.curlValueCovariant_trivialU_local]
  show w + w - w - w = (0 : SuTwo)
  abel

theorem curlImageCovProjFaithful_zero (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection] :
    curlImageCovProjFaithful ell levels U 0 = 0 := by
  unfold curlImageCovProjFaithful
  rw [map_zero, map_zero, map_zero]

/-- **`Δ_k` vanishes at every closed field.** No hypothesis on `ell`, `levels`, `U` or the torus. -/
theorem deltaJ_eq_zero_of_closed (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) (hB : curlCovariantLM U B = 0) :
    deltaJQuadFormCovFaithful ell levels U B = 0 := by
  have hrw : deltaJQuadFormCovFaithful ell levels U B
      = covPlaqInner (hjCorrectionTargetCovFaithful ell levels U B)
          (hjCorrectionTargetCovFaithful ell levels U B) := by
    unfold deltaJQuadFormCovFaithful
    rw [curlCov_hjExtensionCovFaithful]
  have htz : hjCorrectionTargetCovFaithful ell levels U B = 0 := by
    unfold hjCorrectionTargetCovFaithful
    rw [hB, curlImageCovProjFaithful_zero, sub_zero]
  rw [hrw, htz]
  unfold covPlaqInner
  refine Finset.sum_eq_zero fun q _ => ?_
  show hsInner (0 : SuTwo) (0 : SuTwo) = 0
  rw [hsInner_self_eq_norm_sq, norm_zero]
  ring

/-- **`Q_ℓ` fixes constants** (at `U = 1`): the block-line average of a constant field is the same
constant, because the `ℓ³ · ℓ` terms carry exactly the weight `ℓ⁻⁴`. -/
theorem lineCoarse_constField {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (w : SuTwo) (b : CoarseBond L ell) :
    lineCoarseRestrictCovLM (trivialU L) ell (constField w) b = w := by
  have h := AdalyFormal.Balaban.ThirdLevelStokes.ell4_smul_lineCoarseRestrict
    ell hell (constField w) b
  have hline : ∀ x : PeriodicLatticeSite L,
      AdalyFormal.Balaban.ThirdLevelStokes.lineSum ell (constField w) x b.2 = (ell : ℕ) • w := by
    intro x
    show (∑ _i ∈ Finset.range ell, w) = _
    rw [Finset.sum_const, Finset.card_range]
  rw [Finset.sum_congr rfl (fun x _ => hline x), Finset.sum_const,
    card_blockOf b.1.1 ell (coarseLattice_mem_fits hdvd b.1.2)] at h
  have hcast : (ell ^ 3) • ((ell : ℕ) • w) = ((ell : ℝ) ^ 4) • w := by
    rw [smul_smul, ← Nat.cast_smul_eq_nsmul ℝ]
    congr 1
    push_cast
    ring
  rw [hcast] at h
  have hne : ((ell : ℝ) ^ 4) ≠ 0 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  exact smul_right_injective SuTwo hne h

/-- **THE COARSE-ENERGY SHAPE REFUTATION.** No positive `γ` makes
`γ · ⟨Q_ℓ B, Q_ℓ B⟩ ≤ Δ_k(B)` hold at a closed field with nonzero coarse average — and the constant
field is one, at every block side, every torus, every level list. -/
theorem coarse_bond_energy_base_case_refuted {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels (trivialU L)).HasOrthogonalProjection]
    {γ : ℝ} (hγ : 0 < γ) {w : SuTwo} (hw : w ≠ 0) :
    ¬ (γ * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) ell (constField w))
          (lineCoarseRestrictCovLM (trivialU L) ell (constField w))
        ≤ deltaJQuadFormCovFaithful ell levels (trivialU L) (constField w)) := by
  have hQ : lineCoarseRestrictCovLM (trivialU L) ell (constField w) ≠ 0 := by
    intro h
    obtain ⟨y, hy, -⟩ :=
      coarseLattice_exists ell hell hdvd (fun _ => 0 : PeriodicLatticeSite L)
    have hval := lineCoarse_constField hell hdvd w ((⟨y, hy⟩, 0) : CoarseBond L ell)
    rw [h] at hval
    exact hw (by simpa using hval.symm)
  rw [deltaJ_eq_zero_of_closed ell levels (trivialU L) (constField w) (curl_constField w)]
  exact not_le.mpr (mul_pos hγ (covCoarseBondInner_pos_of_ne hQ))

#print axioms curl_constField
#print axioms deltaJ_eq_zero_of_closed
#print axioms lineCoarse_constField
#print axioms coarse_bond_energy_base_case_refuted

/-! ## §8 — NON-VACUITY AND FALSIFIABILITY CONTROLS -/

open AdalyFormal.Balaban.ThirdLevelWitness (witL7 witL7_two_dvd witL7_four_dvd B7 B7_kerQ4
  y70 y70_coarse2 hlt01 coarseCurl_Q2_B7 hsInner_witness_pos bondEnergy_B7 split24)

/-- The single-plaquette contribution, exactly: `⟨(1/8)w, (1/8)w⟩ = (1/64)⟨w,w⟩`. -/
theorem coarseCurlEnergy_Q2_B7_ge :
    (1 / 64 : ℝ) * hsInner suTwoWitness suTwoWitness
      ≤ coarseCurlEnergy witL7_two_dvd (lineCoarseRestrictCovLM (trivialU witL7) 2 B7) := by
  unfold coarseCurlEnergy
  have hterm : hsInner (coarseCurlSuTwo witL7_two_dvd
        (lineCoarseRestrictCovLM (trivialU witL7) 2 B7)
        ((⟨y70, y70_coarse2⟩, ⟨(0, 1), hlt01⟩) : CoarsePlaquette witL7 2))
      (coarseCurlSuTwo witL7_two_dvd (lineCoarseRestrictCovLM (trivialU witL7) 2 B7)
        ((⟨y70, y70_coarse2⟩, ⟨(0, 1), hlt01⟩) : CoarsePlaquette witL7 2))
      = (1 / 64 : ℝ) * hsInner suTwoWitness suTwoWitness := by
    rw [coarseCurl_Q2_B7, hsInner_smul_left, hsInner_smul_right]
    ring
  rw [← hterm]
  exact Finset.single_le_sum
    (f := fun p : CoarsePlaquette witL7 2 =>
      hsInner (coarseCurlSuTwo witL7_two_dvd (lineCoarseRestrictCovLM (trivialU witL7) 2 B7) p)
        (coarseCurlSuTwo witL7_two_dvd (lineCoarseRestrictCovLM (trivialU witL7) 2 B7) p))
    (fun p _ => hsInner_self_nonneg _) (Finset.mem_univ _)

/-- **NON-VACUITY.** At the split `(2,4)` on `witL7`, the LEFT-hand side of §4's bound is strictly
positive on the `ℓ₁`-constraint-kernel field `B7`: the bound is not `0 ≤ Δ_k`. -/
theorem coarseCurlEnergy_Q2_B7_pos :
    0 < coarseCurlEnergy witL7_two_dvd (lineCoarseRestrictCovLM (trivialU witL7) 2 B7) := by
  have h := coarseCurlEnergy_Q2_B7_ge
  have hw := hsInner_witness_pos
  nlinarith

/-- **THE WITNESS INSTANCE of §5**, at the split `(2,4)` on `witL7`, `U = 1`:

  `(1/32)·⟨w,w⟩ ≤ ⟨B7, Δ_k B7⟩`

obtained from §4's general bound with `ℓ₀ = 2` and the single-plaquette contribution. -/
theorem witness_split_base_bound :
    (1 / 32 : ℝ) * hsInner suTwoWitness suTwoWitness
      ≤ deltaKCorr split24 (oneLevelUniv witL7) (trivialU witL7) B7 := by
  have hmain : (2 : ℝ) * coarseCurlEnergy witL7_two_dvd
        (lineCoarseRestrictCovLM (trivialU witL7) 2 B7)
      ≤ deltaJQuadFormCovFaithful 2 (oneLevelUniv witL7) (trivialU witL7) B7 := by
    have h := ell_mul_coarseCurlEnergy_le_deltaJ (L := witL7) (ell := 2)
      (by norm_num) witL7_two_dvd (oneLevelUniv witL7) B7
    simpa using h
  have hlow := coarseCurlEnergy_Q2_B7_ge
  have hgoal : deltaKCorr split24 (oneLevelUniv witL7) (trivialU witL7) B7
      = deltaJQuadFormCovFaithful 2 (oneLevelUniv witL7) (trivialU witL7) B7 := rfl
  rw [hgoal]
  nlinarith [hmain, hlow]

/-- **DE-CORRELATED CROSS-CHECK.** `ThirdLevelSchurGap.third_level_energy_bound` proves
`(1/64)·bondEnergy B7 ≤ deltaKCorr split24 … B7` by a completely different route — ONE dual vector
`stokesU`, its self-norm bound `⟪u,u⟫ ≤ ℓ⁷⟨w,w⟩`, and `deltaJ_ge_dual_pairing_sq`. §4's route is a
Schur test over ALL coarse plaquettes at once and shares none of that machinery. The two numbers are
IDENTICAL: `(1/64)·bondEnergy B7 = (1/64)·2⟨w,w⟩ = (1/32)⟨w,w⟩`. -/
theorem constants_agree_at_witness :
    (1 / 64 : ℝ) * bondEnergy B7 = (1 / 32 : ℝ) * hsInner suTwoWitness suTwoWitness := by
  rw [bondEnergy_B7]
  ring

/-- The left-hand side collapses to `0` on any field the fibre map kills. -/
theorem coarseCurlEnergy_of_kernel {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) (hker : lineCoarseRestrictCovLM U ell B = 0) :
    coarseCurlEnergy hdvd (lineCoarseRestrictCovLM U ell B) = 0 := by
  rw [hker]
  unfold coarseCurlEnergy
  refine Finset.sum_eq_zero fun p _ => ?_
  have hz : coarseCurlSuTwo hdvd (0 : CoarseBond L ell → SuTwo) p = 0 := by
    unfold coarseCurlSuTwo
    show (0 : SuTwo) + 0 - 0 - 0 = 0
    abel
  rw [hz, hsInner_self_eq_norm_sq, norm_zero]
  ring

/-- **THE `ℓ₀ = ℓ₁` DEGENERACY IS EXPLICITLY EXCLUDED, and the control shows it must be.** On the
SAME field `B7` and the SAME background:

* at the COLLAPSED levels (`ℓ₀ = ℓ₁ = 4`, the level at which `B7` satisfies the (3.157) constraint)
  §4's left-hand side is identically `0` — the bound is `0 ≤ 0`, content-free, exactly matching
  `CStarLevelProbe.equal_levels_force_zero` on the right-hand side;
* at the SPLIT levels (`ℓ₀ = 2 < 4 = ℓ₁`) it is strictly positive.

`LevelSplit.proper` makes the first case unstateable in §5; this pair is the measurement showing that
the exclusion is load-bearing and not decoration. -/
theorem bound_has_content_only_at_split :
    coarseCurlEnergy witL7_four_dvd (lineCoarseRestrictCovLM (trivialU witL7) 4 B7) = 0
  ∧ 0 < coarseCurlEnergy witL7_two_dvd (lineCoarseRestrictCovLM (trivialU witL7) 2 B7) :=
  ⟨coarseCurlEnergy_of_kernel witL7_four_dvd (trivialU witL7) B7 B7_kerQ4,
    coarseCurlEnergy_Q2_B7_pos⟩

/-- **MUST-FIRE on the Cauchy–Schwarz `card` factor.** `norm_sum_sq_le` with `card` replaced by `1`
is FALSE: two copies of a nonzero vector have `‖Σ‖² = 4‖w‖² > 2‖w‖²`. So the `ℓ⁵` in
`windowSum_energy_le` is not decoration; deleting it breaks the estimate. -/
theorem norm_sum_sq_le_card_is_load_bearing :
    ¬ (‖suTwoWitness + suTwoWitness‖ ^ 2 ≤ ‖suTwoWitness‖ ^ 2 + ‖suTwoWitness‖ ^ 2) := by
  have hw : 0 < ‖suTwoWitness‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
  have h2 : suTwoWitness + suTwoWitness = (2 : ℝ) • suTwoWitness := (two_smul ℝ suTwoWitness).symm
  rw [h2, norm_smul, Real.norm_eq_abs, mul_pow]
  have : |(2 : ℝ)| = 2 := by norm_num
  rw [this]
  nlinarith [hw]

/-- **MUST-FIRE on the `ℓ⁴` normalisation of `windowSum_curl`.** At the witness plaquette the window
sum is `2 • w` while the coarse curl is `(1/8) • w`: deleting the `ℓ⁴` factor makes the Stokes
identity FALSE at an explicit point. -/
theorem windowSum_normalisation_is_load_bearing :
    windowSum (curlCovariantLM (trivialU witL7) B7)
        ((⟨y70, y70_coarse2⟩, ⟨(0, 1), hlt01⟩) : CoarsePlaquette witL7 2)
      ≠ coarseCurlSuTwo witL7_two_dvd (lineCoarseRestrictCovLM (trivialU witL7) 2 B7)
          ((⟨y70, y70_coarse2⟩, ⟨(0, 1), hlt01⟩) : CoarsePlaquette witL7 2) := by
  rw [windowSum_curl (by norm_num) witL7_two_dvd B7, coarseCurl_Q2_B7, smul_smul]
  have hc : (((2 : ℕ) : ℝ) ^ 4) * (1 / 8 : ℝ) = 2 := by norm_num
  rw [hc]
  intro h
  have hsub : ((2 : ℝ) - (1 / 8 : ℝ)) • suTwoWitness = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hsub with hz | hz
  · norm_num at hz
  · exact suTwoWitness_ne_zero hz

#print axioms coarseCurlEnergy_Q2_B7_pos
#print axioms coarseCurlEnergy_Q2_B7_ge
#print axioms witness_split_base_bound
#print axioms constants_agree_at_witness
#print axioms coarseCurlEnergy_of_kernel
#print axioms bound_has_content_only_at_split
#print axioms norm_sum_sq_le_card_is_load_bearing
#print axioms windowSum_normalisation_is_load_bearing

/-! ## §9 — THE TREE'S STATED UNIFORM TARGET IS FALSE, and here is the witness

`ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform` is the honest two-level restatement of
CMP99b p.428's `C*Δ_kC ≥ γ₀`, and it is the statement this campaign's coercivity chain aims at. It
puts `γ₀ · bondEnergy B̃` on the left. §6 shows that shape is refutable at any nonzero member of the
Schur fibre; §6 alone does NOT refute the target, because the target additionally requires `B̃` to be
in the axial gauge at the CONSTRAINT level and to vanish on the constraint-level dropped bonds. The
question §6 leaves open is whether those two conditions exclude the fibre.

**They do not, and the witness is explicit.** On `witL7`, at the split `(ℓ₀, ℓ₁) = (2, 4)`, at
`U = 1`, take the direction-`1` dipole

    Bax := dipole (1,0,0) (1,0,1) 1 w .

* **Axial gauge at level 4.** `staircasePath` walks `(2, 1, 0)` from `y`
  (`AdmissibleSubspace.staircasePath`), so its only direction-`1` bonds are based at
  `corner1 y x = update y 2 (x 2)`, whose coordinate `0` is `y 0`. For `y ∈ CoarseLattice witL7 4`
  that is `0` or `4`, never `1`. So no staircase bond ever meets `Bax`.
* **Dropped bonds at level 4.** `droppedBondLast 4 c` is based at `pathSite c.1.1 c.2 3`, whose
  coordinate `0` is `(c.1.1) 0 ≡ 0 (mod 4)`, again never `1`.
* **In the fibre at level 2.** The two sites differ only in coordinate `2`, by `0` vs `1`, which lie
  in the same level-2 window for every coarse site — so `Q₂ Bax = 0`, and likewise `Q₄ Bax = 0`.
* Hence `C(B̃) = B̃` (`fullC_fixes_Bax`, the same mechanism as
  `ThirdLevelSandwich.fullC_fixes_B7`), `⟨B̃, C*Δ_kC B̃⟩ = 0`, and `bondEnergy B̃ > 0`.

**The gauge condition at the CONSTRAINT level does not constrain the FIBRE level.** That is the
mechanism, and it is the same one `CoarseCurlScaleTwo` records from the other side ("the fine axial
gauge does not descend to the coarse lattice"). The target is not false because its constant is too
large; it is false because its left-hand side measures a direction its right-hand side cannot see. -/

open AdalyFormal.Balaban.ThirdLevelWitness (dipole dipole_apply_plus Q_dipole_zero)
open AdalyFormal.Balaban.FullReparamC (IsDropped fullC fullC_free fullC_dropped dinvC dinvC_hinv)
open AdalyFormal.Balaban.ReparamCSuTwo (restFunctional constraintFunctional
  constraintFunctional_apply dropZero dropZero_apply)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast pathSite_apply_ne)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.CStarLevelCorrected (cStarDeltaKCFormCorr)
open AdalyFormal.Balaban.CovariantHjMinimizer (RcovLM_oneLevelUniv_eq_zero)

/-- `(1, 0, 0)` — coordinate `0` is `1`, which is OFF every level-4 staircase and every level-4
dropped bond (both sit at coordinate `0 ≡ 0 mod 4`). -/
def a7 : PeriodicLatticeSite witL7 := fun ρ => if ρ = 0 then 1 else 0

/-- `(1, 0, 1)` — the same, shifted by `e₂`; coordinates `0` and `1` share every level-2 AND every
level-4 window with `a7`. -/
def a7' : PeriodicLatticeSite witL7 := fun ρ => if ρ = 0 then 1 else if ρ = 2 then 1 else 0

theorem a7_ne_a7' : a7 ≠ a7' := by decide

/-- **THE WITNESS.** A direction-`1` dipole in the level-4 axial gauge, vanishing on every level-4
dropped bond, lying in the level-2 Schur fibre, with strictly positive bond energy. -/
noncomputable def Bax : Bond witL7 → SuTwo := dipole a7 a7' 1 suTwoWitness

/-- `Bax` vanishes at every bond that is not a direction-`1` bond based at coordinate `0 = 1`. -/
theorem Bax_eq_zero_of {e : Bond witL7} (h : ¬ ((e.1 0).val = 1 ∧ e.2 = 1)) : Bax e = 0 := by
  unfold Bax dipole
  have h1 : e ≠ ((a7, 1) : Bond witL7) := by
    intro he; subst he; exact h ⟨rfl, rfl⟩
  have h2 : e ≠ ((a7', 1) : Bond witL7) := by
    intro he; subst he; exact h ⟨rfl, rfl⟩
  rw [if_neg h1, if_neg h2, sub_self, zero_smul]

theorem Bax_kerQ2 : lineCoarseRestrictCovLM (trivialU witL7) 2 Bax = 0 := by
  refine Q_dipole_zero (ν := 2) 2 (by decide) (by decide) (fun y hy => ?_) suTwoWitness
  have h1 := mem_CoarseLattice.mp hy 2
  have h2 : (y 2).val < 8 := (y 2).isLt
  have hA : (a7 2).val = 0 := rfl
  have hB : (a7' 2).val = 1 := rfl
  rw [hA, hB]
  omega

theorem Bax_kerQ4 : lineCoarseRestrictCovLM (trivialU witL7) 4 Bax = 0 := by
  refine Q_dipole_zero (ν := 2) 4 (by decide) (by decide) (fun y hy => ?_) suTwoWitness
  have h1 := mem_CoarseLattice.mp hy 2
  have h2 : (y 2).val < 8 := (y 2).isLt
  have hA : (a7 2).val = 0 := rfl
  have hB : (a7' 2).val = 1 := rfl
  rw [hA, hB]
  omega

theorem Bax_ne_zero : Bax ≠ 0 := by
  intro h
  have hb : Bax ((a7, 1) : Bond witL7) = 0 := by rw [h]; rfl
  rw [show Bax ((a7, 1) : Bond witL7) = suTwoWitness from
    dipole_apply_plus a7_ne_a7' 1 suTwoWitness] at hb
  exact suTwoWitness_ne_zero hb

theorem bondEnergy_Bax_pos : 0 < bondEnergy Bax := by
  unfold bondEnergy
  refine Finset.sum_pos' (fun b _ => by positivity)
    ⟨((a7, 1) : Bond witL7), Finset.mem_univ _, ?_⟩
  rw [show Bax ((a7, 1) : Bond witL7) = suTwoWitness from
    dipole_apply_plus a7_ne_a7' 1 suTwoWitness]
  have hn : 0 < ‖suTwoWitness‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
  positivity

/-- **`Bax` IS IN THE LEVEL-4 AXIAL GAUGE.** The staircase's only direction-`1` segment is based at
`corner1 y x`, whose coordinate `0` is `y 0 ≡ 0 (mod 4)`. -/
theorem Bax_axial (y : PeriodicLatticeSite witL7) (hy : y ∈ CoarseLattice witL7 4)
    (x : PeriodicLatticeSite witL7) (_hx : x ∈ blockOf y 4)
    (e : PeriodicLatticeEdge witL7) (he : e ∈ staircasePath y x) : Bax e = 0 := by
  refine Bax_eq_zero_of ?_
  rintro ⟨hcoord, hdir⟩
  rw [staircasePath, Finset.mem_union, Finset.mem_union] at he
  rcases he with (h2 | h1) | h0
  · have hz := (mem_axisSegment.mp h2).1
    rw [hdir] at hz
    exact absurd hz (by decide)
  · have hbase := (mem_axisSegment.mp h1).2.1 0 (by decide)
    have hc1 : corner1 y x 0 = y 0 := by
      show Function.update y 2 (x 2) 0 = y 0
      exact Function.update_of_ne (by decide) _ _
    rw [hc1] at hbase
    rw [hbase] at hcoord
    have hy0 := mem_CoarseLattice.mp hy 0
    omega
  · have hz := (mem_axisSegment.mp h0).1
    rw [hdir] at hz
    exact absurd hz (by decide)

/-- **`Bax` VANISHES ON EVERY LEVEL-4 DROPPED BOND.** -/
theorem Bax_no_dropped (c : CoarseBond witL7 4) : Bax (droppedBondLast 4 c) = 0 := by
  refine Bax_eq_zero_of ?_
  rintro ⟨hcoord, hdir⟩
  have hd : c.2 = 1 := hdir
  have hbase : ((droppedBondLast 4 c).1 0) = (c.1.1) 0 := by
    show (pathSite c.1.1 c.2 3) 0 = _
    exact pathSite_apply_ne c.1.1 c.2 0 3 (by rw [hd]; decide)
  rw [hbase] at hcoord
  have hy0 := mem_CoarseLattice.mp c.1.2 0
  omega

theorem dropZero_Bax (c : CoarseBond witL7 4) :
    dropZero (droppedBondLast 4 c) Bax = Bax := by
  funext b
  rw [dropZero_apply]
  by_cases hb : b = droppedBondLast 4 c
  · rw [if_pos hb, hb, Bax_no_dropped c]
  · rw [if_neg hb]

/-- **`C` FIXES `Bax`**: every constraint is already satisfied and every dropped slot already
carries `0`, so each per-bond solve returns `0`. -/
theorem fullC_fixes_Bax :
    fullC (trivialU witL7) 4 (dinvC (trivialU witL7) 4) Bax = Bax := by
  funext b
  by_cases hd : IsDropped 4 b
  · obtain ⟨c, rfl⟩ := hd
    rw [fullC_dropped (by norm_num) witL7_four_dvd (trivialU witL7)
      (dinvC (trivialU witL7) 4) Bax c, Bax_no_dropped c]
    show -(dinvC (trivialU witL7) 4 c
      (restFunctional (trivialU witL7) 4 c (droppedBondLast 4 c) Bax)) = 0
    have hrest : restFunctional (trivialU witL7) 4 c (droppedBondLast 4 c) Bax = 0 := by
      show constraintFunctional (trivialU witL7) 4 c (dropZero (droppedBondLast 4 c) Bax) = 0
      rw [dropZero_Bax c, constraintFunctional_apply]
      have h := congrFun Bax_kerQ4 c
      rwa [lineCoarseRestrictCovLM_apply, Pi.zero_apply] at h
    rw [hrest, map_zero, neg_zero]
  · exact fullC_free (trivialU witL7) (dinvC (trivialU witL7) 4) Bax hd

/-- **THE SANDWICH VANISHES AT `Bax`.** -/
theorem cStarDeltaKC_Bax_zero :
    cStarDeltaKCFormCorr split24 (oneLevelUniv witL7) (trivialU witL7)
      (dinvC (trivialU witL7) 4) Bax = 0 := by
  show deltaKCorr split24 (oneLevelUniv witL7) (trivialU witL7)
    (fullC (trivialU witL7) 4 (dinvC (trivialU witL7) 4) Bax) = 0
  rw [fullC_fixes_Bax]
  exact deltaJQuadFormCovFaithful_eq_zero_of_mem_V 2 (oneLevelUniv witL7) (trivialU witL7) Bax
    (mem_gaugeConstraintSubspaceCovFaithful.mpr
      ⟨Bax_kerQ2, RcovLM_oneLevelUniv_eq_zero (trivialU witL7) _⟩)

/-- **THE REFUTATION.** `ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform` — the campaign's
stated uniform coercivity target for the level-corrected `C*Δ_kC` — is FALSE. Every one of its
hypotheses is met at `(witL7, split24, oneLevelUniv, U = 1, dinvC, Bax)`, its right-hand side is `0`,
and its left-hand side is `γ₀ · bondEnergy Bax > 0` for every `γ₀ > 0`. -/
theorem levelCorrectedCoercivityTargetUniform_refuted :
    ¬ AdalyFormal.Balaban.ThirdLevelSchurGap.LevelCorrectedCoercivityTargetUniform := by
  rintro ⟨γ₀, α₀, hγ, hα, h⟩
  have hfrob : frobSupBond (trivialU witL7) ≤ α₀ := by
    rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU witL7]
    exact le_of_lt hα
  have hcon := h witL7 split24 (by exact le_refl 2) (by decide) witL7_two_dvd witL7_four_dvd
    (oneLevelUniv witL7) (trivialU witL7) hfrob (dinvC (trivialU witL7) 4)
    (dinvC_hinv (by norm_num) witL7_four_dvd (trivialU witL7)) Bax Bax_axial Bax_no_dropped
  rw [cStarDeltaKC_Bax_zero] at hcon
  exact absurd hcon (not_le.mpr (mul_pos hγ bondEnergy_Bax_pos))

#print axioms a7_ne_a7'
#print axioms Bax_eq_zero_of
#print axioms Bax_kerQ2
#print axioms Bax_kerQ4
#print axioms Bax_ne_zero
#print axioms bondEnergy_Bax_pos
#print axioms Bax_axial
#print axioms Bax_no_dropped
#print axioms fullC_fixes_Bax
#print axioms cStarDeltaKC_Bax_zero
#print axioms levelCorrectedCoercivityTargetUniform_refuted

/-! ## §10 — the remaining `#print axioms`, so the sweep covers EVERY declaration in this file

A nested validator measured 43 of 56 declarations carrying an axiom check. The other 13 are below;
none is exempt because it is "only a definition". -/

#print axioms windowSum
#print axioms coarseCurlEnergy
#print axioms coarseCurlEnergy_nonneg
#print axioms ccEnergyOf
#print axioms ccEnergyOf_nonneg
#print axioms windowCurlEnergy
#print axioms WindowStokesAnnihilates
#print axioms constField
#print axioms curlImageCovProjFaithful_zero
#print axioms a7
#print axioms a7'
#print axioms Bax
#print axioms dropZero_Bax

end AdalyFormal.Balaban.SplitBaseCase
