/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.GammaRecursion
import AdalyFormal.Balaban.LemmaAssemblyNormalized
import AdalyFormal.Balaban.GeneralUHodgeDrift

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `KappaBound.lean` — DECIDING `κ`, the free parameter of `DeltaPrimeBound`

Lane record: `compute/kappa_bound/PROGRESS.md`.

**THE TARGET.** `DeltaPrimeBound.abs_deltaPrimePiForm_le` bounds `Δ′_π` by
`Jsup·κ·(28+48κ)·bondEnergy A` under the hypothesis
`hlam : siteEnergy lam ≤ κ^2 · bondEnergy A`, where `lam` is CMP99b's `λ = G′RD*A`. That `κ` was
carried as free data. If it is unbounded the bound is vacuous exactly where it matters.

## §0 — THE SOURCE, and what it does and does not give

`corpus/pages/CMP99b_p394.md` (`verification_status: single-read`, so a STRONG LEAD, not
adjudicated ground truth; `render_png: corpus/renders/CMP99b_p394-06.png`,
`render_sha256: 16765ae58769905aed389432038581763f4b1950a0d6024c571dc784a3e3e733`) prints, VERBATIM:

```
(3.20)  (3.17) = exp(-(1/2a)||RD*A||^2)
        where R = R(U) is an orthogonal projection in the Hilbert space L^2(Om_0,g) onto the
        subspace
(3.21)  R = Delta_U^eta N(Q'),  N(Q') = {lam : Q'lam = 0}
(3.22)  Rf = Delta_U^eta lam_0, lam_0 a minimum of  lam in N(Q'), lam -> ||f - Delta_U^eta lam||^2
(3.23)  Delta_U^eta = D_U^{eta*} D_U^eta
        Delta'_a = Delta'_a(U) = (Delta_U^eta + Q'^* a Q') restricted to Om_0
(3.24)  <lam, Q'^* a Q' lam> = Sum_{j=0}^k a_j Sum_{y in Lam_j} (L^j eta)^{d-2} |(Q'_j(U)lam)(y)|^2
        "...the operator Delta'_a |_{Om_0} = Om_0 Delta'_a Om_0. ... Its inverse is denoted by G',
        or G'(U)."
(3.25)  Rf = (I - G'Q'^*(Q'G'^2Q'^*)^{-1} Q'G')f,  where G' = G'(U) = (Delta'_a)^{-1}
```

**THE DEFERRED CLAIM, LOCATED PRECISELY.** `corpus/pages/CMP99b_p416.md`
(`verification_status: adjudicated`; `render_sha256:
182ab014208b5b331f3ee8a8cbeaa28361bdd9e8493bf407181ff2e6ed63f786`) prints, VERBATIM:

```
Theorem 3.11. Under the assumptions of the Theorems 3.1-3.10 (i.e. for M sufficiently large and
alpha_0 sufficiently small) the operators Delta'_a, G', (Q'G'^2Q'^*)^{-1}, Delta_a, G are positive
definite.

This is obvious for the first three operators, and also for P and R, hence it is enough to prove
it for G.
```

Two facts, and the second is the operative one. (i) The dispatch is right that the proof is
deferred — "This is obvious" — for exactly the three operators `Delta'_a`, `G'`,
`(Q'G'^2Q'^*)^{-1}` one would have wanted. (ii) **Theorem 3.11 asserts only POSITIVITY. It is not
a quantitative estimate and could not have bounded `κ` even if fully proved.** Nothing in this
file uses it, so its deferral is not on the critical path.

## §1 — WHAT THIS FILE PROVES

1. **`Q′` AND `G′` DISAPPEAR** (§2, `gaugeParam_mem_ker_and_solves`). From (3.21), (3.23), (3.24)
   and the single word "inverse" in *"Its inverse is denoted by `G′`"* — no positivity, no
   self-adjointness, no inner product, no idempotence of `R`, no Theorem 3.11 — one gets
   `Q′(G′Rf) = 0` and `Δ(G′Rf) = Rf`. That is: `λ = G′RD*A` LIES IN `N(Q′)` and SOLVES
   `Δ_U λ = RD*A` there. The whole `G′`/`R`/`(Q'G'^2Q'^*)^{-1}` apparatus collapses, for the
   purpose of `κ`, to those two facts. The load-bearing input is that `Q'^*aQ'` VANISHES on
   `N(Q′)`, immediate from (3.24) whose right-hand side is a sum of `|(Q'_jλ)(y)|²`.

2. **`κ` IS `‖D‖ ×` A POINCARÉ CONSTANT** (§6, `siteEnergy_le_of_poincare`). If
   `siteEnergy λ ≤ Psq · bondEnergy (D_U λ)` for `λ ∈ N(Q′)` and `siteEnergy src ≤ rsq·bondEnergy A`,
   then `siteEnergy λ ≤ (rsq·Psq²)·bondEnergy A` — which is `hlam` at `κ² = rsq·Psq²`.

3. **THE POINCARÉ CONSTANT IS BACKGROUND-INDEPENDENT** (§4, `transport_step_norm_eq`). Bałaban's
   `Q′` averages the TRANSPORTED field `μ(x) = R(Γ_{y,x})λ(x)`, and his `Γ_{y,x}` is the
   coordinate-order (staircase) path family, which is PREFIX-CLOSED: the path to `x` is the path
   to its predecessor extended by ONE bond. A prefix-closed family rooted at `y` is a SPANNING
   TREE of the block, and along a tree bond `b = (x′,μ)` one has `Γ_{y,x} = Γ_{y,x′}·U_b` exactly,
   so `‖μ(x) − μ(x′)‖ = ‖(D_U λ)(b)‖` EXACTLY — no curvature defect, no `α₀`, no regularity
   class. Hence the covariant block Poincaré inequality on `N(Q′)` is EXACTLY a mean-zero
   Poincaré inequality on a fixed finite tree, with a purely combinatorial constant.

4. **THE CONSTANT AT `ell = 2`, `d = 3`** (§5, `tree_poincare_ell_two`): eight vectors summing to
   zero on the staircase tree of `{0,1}³` satisfy `Σ‖μ‖² ≤ 8·Σ_{7 tree bonds}‖Δμ‖²`, so
   `Psq = 8`. (`compute/kappa_bound/tree_gap.py` MEASURES the sharp constant for this tree as
   `1/λ₂ = 3.9859…`. Per `GOAL.md`/`REFORM_PROGRAM.md` python signs nothing: that number is
   recorded as a sharpening target, is NOT used anywhere, and carries no weight. The `8` proved
   here is what everything below consumes.)

5. **THE NUMBER, AND THE COMPOSITION** (§7). With `rsq = 12` (`‖D_U‖² ≤ 12`, §6) and `Psq = 8`:
   `κ² ≤ 768`, i.e. `κ ≤ 16√3 ≈ 27.71`. Composed with `DeltaPrimeBound`'s own fixed-point
   criterion at `ell = 2` (`q = 1/2`, `γ₀ = normGamma`, `Jsup = 24·η⁻²·α₀`):
   **the criterion FAILS at the tree's `normAlpha = 5·10⁻⁷`** (`criterion_fails_at_normAlpha`)
   and **CLOSES at `α₀ = 4·10⁻¹⁰`** (`criterion_closes_at_four_e_minus_ten`). So `κ` is bounded,
   and the price of the real `κ` is that the admissible regularity radius drops by three orders
   of magnitude.

## §0a — THE THREE LOAD-BEARING READINGS WERE IMAGE-VERIFIED BY THIS LANE (LAW-11)

`corpus/pages/CMP99b_p394.md` is `verification_status: single-read`, i.e. a strong lead and NOT
adjudicated ground truth, so every reading §2 leans on was taken to the page image directly:
`corpus/renders/CMP99b_p394-06.png` (sha256 `16765ae58769905aed389432038581763f4b1950a0d6024c571d
c784a3e3e733`, matching the page front matter; 2406×3800), read in three 400-dpi crops. Confirmed
on the image: (3.21) in full including the preceding "orthogonal projection … onto the subspace";
(3.23); (3.24) — **every summand carries `|(Q'_j(U)λ)(y)|²`, so the form vanishes on `N(Q')`, which
IS the hypothesis `hM`**; the sentence "Its inverse is denoted by `G'`, or `G'(U)`" — the hypothesis
`hG`; and (3.25) with "where `G' = G'(U) = (Δ'_a)^{-1}`".

One fact visible on the image and worth recording: "By the definition of space `N(Q')` the functions
`λ` in (3.22) vanish on `Ω₁ᶜ`." So `N(Q')` carries a SUPPORT restriction as well. That makes `N(Q')`
SMALLER, which only strengthens §5's Poincaré step (proved on the larger block-mean-zero set), and
does not touch §2, which uses `ker Q` abstractly.

## §1a — WHAT IS *NOT* CLOSED HERE, STATED AS FACT, NOT AS A LABEL

* ~~`tree_poincare_ell_two` is proved for the eight sites of ONE block, indexed by eight named
  vectors. **The lattice assembly** — partitioning `PeriodicLatticeSite L` into `ell`-blocks and
  summing the per-block inequality into `bondEnergy` — is carried as the explicit hypothesis
  `hPoin` of §6 and is NOT proved here.~~ **SUPERSEDED in the same pass by §8**, which proves the
  assembly: `siteEnergy_eq_sum_blocks` (the blocks tile, from `AdmissibleSubspace`'s own
  `coarseLattice_exists`/`coarseLattice_unique`, reused not rebuilt), `sum_treeBonds_le_bondEnergy`
  (the per-block bond sets sum into `bondEnergy`), `poincare_assembly`. §8a then names the seven
  tree bonds concretely (`treeBondsTwo`) and DISCHARGES the disjointness hypothesis
  (`treeBondsTwo_pairwiseDisjoint`), giving `poincare_assembly_two`. The `blockOf` truncation
  hazard is handled the only safe way: `0 < ell` and `∀ μ, ell ∣ L μ + 1` are carried explicitly
  through every declaration in §8.
* **WHAT REMAINS, EXACTLY ONE THING:** `hblock` of `poincare_assembly_two` — the per-block
  inequality `∑_{x∈B(y)} ‖λ(x)‖² ≤ 8·∑_{b∈treeBondsTwo y} ‖(D_Uλ)(b)‖²`. Both of its ingredients
  are proved here (`tree_poincare_ell_two` for the eight transported values;
  `transport_step_norm_eq` for each of the seven bonds). Instantiating it requires WRITING DOWN
  `Γ_{y,x}` — the eight explicit transports — and expanding `blockOf y 2` into its eight sites.
  That is deliberately NOT done in this pass: `Γ_{y,x}`'s coordinate order is a known silent-defect
  site in this campaign (it was built backwards four times before the defining equation was located
  in CMP95 (1.7), an earlier paper of the same series), and guessing it here would produce a
  statement that compiles, passes every gate, and denotes the wrong object. The correct next step
  is a source-audit pass on CMP95 (1.7) at 300+ dpi, then instantiation. **Note that the constant
  `8` does not depend on which coordinate order is used**: all six orders give isomorphic staircase
  trees, so the order affects WHICH bonds `treeBondsTwo` names, not the inequality's constant.
* `‖R‖ ≤ 1` is proved ABSTRACTLY here (`norm_apply_le_of_selfadjoint_idempotent`) for a
  self-adjoint idempotent on any real inner product space — which is exactly (3.20)'s *"R is an
  orthogonal projection"*. Its instantiation at the concrete site carrier is carried as a
  hypothesis, because `PeriodicLatticeSite L → SuTwo` deliberately carries no `InnerProductSpace`
  instance in this tree (the instance-diamond note in `CovariantHj.lean`).
* ~~`Dstar` (the adjoint `D_U^*`) is NOT constructed.~~ **CORRECTION (2026-08-01, post-cap repair
  batch): FALSE.** `D_U^*` IS constructed, by this module's own import closure:
  `AdalyFormal.Balaban.CovariantHjMinimizer` §5 builds it explicitly
  (`gradCovariantAdjointValue U A := Σ_μ [R(U(shiftBack_μy,μ))⁻¹(A(shiftBack_μy,μ)) - A(y,μ)]`,
  the combinatorial adjoint), and `JointInstantiation.hweak_of_gradCovariantAdjoint`/
  `hadj_of_gradCovariantAdjoint` (`JointInstantiation.lean:159`/`:148`) consume that construction to
  discharge `hweak`/`hadj` for EVERY `U`/`λ`/`A`, with no hypothesis on either. What §6 of THIS file
  takes as a hypothesis is not the construction of `D_U^*` but the RELATION `hadj : ∀ w,
  covSiteInner w S = covBondInner (gradValueCovariant U w) A` naming an ARBITRARY `S` — i.e. this
  module's `§6` is agnostic to which `S` satisfies the relation, and does not itself need to know
  `S` is `gradCovariantAdjointValue U A`; the two are reconciled downstream at the
  `JointInstantiation` call site. That relation PINS `S` uniquely; it is an identity, not a size
  assumption, and `siteEnergy S ≤ 12·bondEnergy A` is DERIVED from it (`siteEnergy_le_of_adjoint`),
  not assumed.

**Import note (LAW-4).** `DeltaPrimeBound.lean` has no `.olean` and a concurrent lane was running
`lake env lean` on it while this file was written, so it is NOT imported, and its
`siteEnergy_le_of_gap`, `abs_covSiteInner_le`, `sqrt_three_le`, `sum_lam_tail_sq_eq`,
`sum_lam_head_sq_eq` and `bondEnergy_gradValueCovariant_le` are NOT reused. The facts needed here
are re-derived by a route that avoids `Real.sqrt` entirely. Disclosed duplication, not novelty.
-/

namespace AdalyFormal.Balaban.KappaBound

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer (covSiteInner periodicLatticeShiftEquiv)
open AdalyFormal.Balaban.CovariantHj (covBondInner)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)
open AdalyFormal.Balaban.GeneralUHodgeDrift (siteEnergy siteEnergy_nonneg)
open AdalyFormal.Balaban.AlphaAnalyticity (norm_RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LemmaAssembly (hsInner_self_eq_norm_sq)

/-! ## §2 — THE STRUCTURAL THEOREM: `G′` AND `R` ELIMINATED

Nothing in this section is specific to gauge theory. It is the algebra of (3.21)+(3.23)+(3.24)
plus the word "inverse" in *"Its inverse is denoted by `G′`"*. -/

section Structural

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **`λ = G′Rf` LIES IN `N(Q′)` AND SOLVES `Δλ = Rf` THERE.**

Hypotheses, each a transcription of the source and nothing more:

* `hM` — `Q'^*aQ'` annihilates `N(Q')`. Immediate from CMP99b (3.24), whose right-hand side
  `Σ_j a_j Σ_y (L^jη)^{d−2}|(Q'_jλ)(y)|²` vanishes identically when `Q'λ = 0`.
* `hG` — `G` is a LEFT inverse of `Δ' = Δ + M`, i.e. p.394's *"Its inverse is denoted by `G'`"*.
  Only the left-inverse half is used.
* `hR` — `range R = Δ(ker Q)`, which is CMP99b (3.21) verbatim.

Neither positivity nor self-adjointness nor idempotence of `R` is used, so Theorem 3.11's deferred
proof is off the critical path. The explicit formula (3.25) is not needed either: it is an
independent confirmation, since the range of `I − G'Q'^*(Q'G'^2Q'^*)^{-1}Q'G'` is `ker(Q'G')`, and
`ker(Q'G') = Δ(ker Q)` by exactly the argument below. -/
theorem gaugeParam_mem_ker_and_solves
    (Q : E →ₗ[ℝ] F) (Δ M G R : E →ₗ[ℝ] E)
    (hM : ∀ x : E, Q x = 0 → M x = 0)
    (hG : ∀ x : E, G ((Δ + M) x) = x)
    (hR : LinearMap.range R = Submodule.map Δ (LinearMap.ker Q))
    (f : E) :
    Q (G (R f)) = 0 ∧ Δ (G (R f)) = R f := by
  have hmem : R f ∈ LinearMap.range R := ⟨f, rfl⟩
  rw [hR] at hmem
  obtain ⟨μ, hμker, hμ⟩ := hmem
  have hμQ : Q μ = 0 := LinearMap.mem_ker.mp hμker
  have hMμ : M μ = 0 := hM μ hμQ
  have hΔ' : (Δ + M) μ = R f := by
    simp only [LinearMap.add_apply, hMμ, add_zero]
    exact hμ
  have hGval : G (R f) = μ := by rw [← hΔ', hG]
  rw [hGval]
  exact ⟨hμQ, hμ⟩

end Structural

#print axioms gaugeParam_mem_ker_and_solves

/-! ### §2a — MUST-FIRE CONTROLS for §2

Explicit named instances (not existentials over free data) showing each non-trivial hypothesis is
load-bearing: drop it and the conclusion is FALSE at a concrete point. -/

namespace Control

/-- `Q(x,y) = x`. -/
def ctrlQ : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ

/-- `Δ(x,y) = (y,0)`. -/
def ctrlD : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := (LinearMap.snd ℝ ℝ ℝ).prod 0

/-- `M = id` — the `hM` violator: it does NOT vanish on `ker Q`. -/
def ctrlM : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := LinearMap.id

/-- `G(u,v) = (u − v, v)`, the genuine inverse of `Δ + M : (x,y) ↦ (x+y, y)`. -/
def ctrlG : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.snd ℝ ℝ ℝ)

/-- `R(x,y) = (x,0)`. -/
def ctrlR : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := (LinearMap.fst ℝ ℝ ℝ).prod 0

theorem ctrlQ_apply (p : ℝ × ℝ) : ctrlQ p = p.1 := rfl
theorem ctrlD_apply (p : ℝ × ℝ) : ctrlD p = (p.2, 0) := rfl
theorem ctrlM_apply (p : ℝ × ℝ) : ctrlM p = p := rfl
theorem ctrlG_apply (p : ℝ × ℝ) : ctrlG p = (p.1 - p.2, p.2) := rfl
theorem ctrlR_apply (p : ℝ × ℝ) : ctrlR p = (p.1, 0) := rfl

/-- `hG` HOLDS for the control: `G` really is a left inverse of `Δ + M`. -/
theorem ctrl_hG : ∀ x : ℝ × ℝ, ctrlG ((ctrlD + ctrlM) x) = x := by
  intro x
  have h1 : ((ctrlD + ctrlM) x).1 = x.2 + x.1 := by
    simp [LinearMap.add_apply, ctrlD_apply, ctrlM_apply]
  have h2 : ((ctrlD + ctrlM) x).2 = x.2 := by
    simp [LinearMap.add_apply, ctrlD_apply, ctrlM_apply]
  rw [ctrlG_apply, h1, h2]
  have h3 : (x.2 + x.1 - x.2 : ℝ) = x.1 := by ring
  rw [h3]

/-- `hR` HOLDS for the control, in the elementwise form §2's proof consumes: `R f ∈ Δ(ker Q)`,
witnessed by `μ = (0, f.1)`. -/
theorem ctrl_hR_pointwise (f : ℝ × ℝ) :
    ctrlQ ((0, f.1) : ℝ × ℝ) = 0 ∧ ctrlD ((0, f.1) : ℝ × ℝ) = ctrlR f := ⟨rfl, rfl⟩

/-- `hM` FAILS for the control, at a concrete point of `ker Q`. -/
theorem ctrl_hM_fails : ctrlQ ((0, 1) : ℝ × ℝ) = 0 ∧ ctrlM ((0, 1) : ℝ × ℝ) ≠ 0 := by
  refine ⟨rfl, ?_⟩
  rw [ctrlM_apply]
  simp only [ne_eq, Prod.mk_eq_zero, not_and]
  intro _
  norm_num

/-- **MUST-FIRE.** With `hG` and `hR` intact and only `hM` dropped, §2's conclusion is FALSE:
`Q(G(R f)) = 1 ≠ 0` at `f = (1,0)`. So CMP99b (3.24)'s *"`Q'^*aQ'` vanishes on `N(Q')`"* is
load-bearing, not decorative. -/
theorem ctrl_conclusion_fails : ctrlQ (ctrlG (ctrlR ((1, 0) : ℝ × ℝ))) ≠ 0 := by
  rw [ctrlR_apply, ctrlG_apply, ctrlQ_apply]
  norm_num

/-- **MUST-FIRE for `hR`.** On `E = F = ℝ` take `Q = Δ = G = R = id`, `M = 0`. Then `hM` and `hG`
both hold, `hR` FAILS (`range R = ⊤`, `Δ(ker Q) = ⊥`), and the conclusion is false at `f = 1`. -/
theorem ctrl_hR_needed :
    (∀ x : ℝ, x = 0 → (0 : ℝ →ₗ[ℝ] ℝ) x = 0)
      ∧ (∀ x : ℝ, (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
            (((LinearMap.id : ℝ →ₗ[ℝ] ℝ) + (0 : ℝ →ₗ[ℝ] ℝ)) x) = x)
      ∧ LinearMap.range (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
          ≠ Submodule.map (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (LinearMap.ker (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
      ∧ (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (1 : ℝ) ≠ 0 := by
  refine ⟨fun _ _ => rfl, fun x => by simp, ?_, by norm_num⟩
  intro hc
  rw [LinearMap.range_id, LinearMap.ker_id, Submodule.map_bot] at hc
  have h1 : (1 : ℝ) ∈ (⊤ : Submodule ℝ ℝ) := Submodule.mem_top
  rw [hc] at h1
  simp only [Submodule.mem_bot] at h1
  norm_num at h1

end Control

#print axioms Control.ctrlQ
#print axioms Control.ctrlD
#print axioms Control.ctrlM
#print axioms Control.ctrlG
#print axioms Control.ctrlR
#print axioms Control.ctrlQ_apply
#print axioms Control.ctrlD_apply
#print axioms Control.ctrlM_apply
#print axioms Control.ctrlG_apply
#print axioms Control.ctrlR_apply
#print axioms Control.ctrl_hG
#print axioms Control.ctrl_hR_pointwise
#print axioms Control.ctrl_hM_fails
#print axioms Control.ctrl_conclusion_fails
#print axioms Control.ctrl_hR_needed

/-! ## §3 — `‖R‖ ≤ 1` FOR AN ORTHOGONAL PROJECTION (CMP99b (3.20)'s own word) -/

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A self-adjoint idempotent is a contraction.** `‖Rv‖² = ⟪Rv,Rv⟫ = ⟪v,R(Rv)⟫ = ⟪v,Rv⟫ ≤
‖v‖‖Rv‖`. This is CMP99b (3.20)'s *"R = R(U) is an orthogonal projection"*, and it is the ONLY
property of `R` any size estimate below needs. -/
theorem norm_apply_le_of_selfadjoint_idempotent
    (R : E →ₗ[ℝ] E) (hidem : ∀ x : E, R (R x) = R x)
    (hsa : ∀ x y : E, (inner ℝ (R x) y : ℝ) = (inner ℝ x (R y) : ℝ)) (v : E) :
    ‖R v‖ ≤ ‖v‖ := by
  have h1 : (inner ℝ (R v) (R v) : ℝ) = (inner ℝ v (R v) : ℝ) := by
    rw [hsa v (R v), hidem v]
  have h2 : ‖R v‖ ^ 2 = (inner ℝ v (R v) : ℝ) := by
    rw [← h1, real_inner_self_eq_norm_sq]
  have h3 : (inner ℝ v (R v) : ℝ) ≤ ‖v‖ * ‖R v‖ := real_inner_le_norm v (R v)
  have h4 : ‖R v‖ ^ 2 ≤ ‖v‖ * ‖R v‖ := by rw [h2]; exact h3
  rcases eq_or_lt_of_le (norm_nonneg (R v)) with h | h
  · rw [← h]; exact norm_nonneg v
  · nlinarith [h4, h]

/-- **MUST-FIRE for `hidem`.** `R = 2·id` is self-adjoint but not idempotent, and it is not a
contraction: `‖R v‖ = 2‖v‖ > ‖v‖` at any `v ≠ 0`. -/
theorem contraction_needs_idempotent (v : E) (hv : v ≠ 0) :
    ‖((2 : ℝ) • (LinearMap.id : E →ₗ[ℝ] E)) v‖ > ‖v‖ := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have : ‖((2 : ℝ) • (LinearMap.id : E →ₗ[ℝ] E)) v‖ = 2 * ‖v‖ := by
    simp [norm_smul]
  rw [this]
  linarith

end Projection

#print axioms norm_apply_le_of_selfadjoint_idempotent
#print axioms contraction_needs_idempotent

/-! ## §4 — THE TREE-GAUGE IDENTITY: the Poincaré constant is BACKGROUND-INDEPENDENT

Bałaban's `Q′` (CMP99b p.430 (3.169)) averages `μ(x) = R(Γ_{y,x})λ(x)` over the block `B(y)`, along
the coordinate-order path family `Γ_{y,x}`. That family is PREFIX-CLOSED — the path to `x` is the
path to its coordinate-order predecessor `x′` extended by the single bond `b = (x′,μ)` — so
`Γ_{y,x} = Γ_{y,x′}·U_b` EXACTLY. The theorem below is the consequence, and it is the reason the
covariant block Poincaré constant does not depend on the background at all. -/

variable {L : PeriodicLatticeExtent}

/-- **THE TREE-GAUGE IDENTITY.** If the transport to `x = shift x′ μ` factors as `g·U(x′,μ)` through
the transport `g` to `x′` — which is exactly what prefix-closedness of `Γ` gives — then the
difference of TRANSPORTED values has EXACTLY the norm of the covariant derivative on that bond.

No regularity class, no `α₀`, no curvature: `RMap g` is an isometry and the two transports differ
by precisely the bond variable. -/
theorem transport_step_norm_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ‖RMap (g * U (x, μ)) (lam (periodicLatticeShift x μ)) - RMap g (lam x)‖
      = ‖gradValueCovariant U lam (x, μ)‖ := by
  have h1 : RMap (g * U (x, μ)) (lam (periodicLatticeShift x μ))
      = RMap g (RMap (U (x, μ)) (lam (periodicLatticeShift x μ))) :=
    (RMap_mul_apply g (U (x, μ)) (lam (periodicLatticeShift x μ))).symm
  rw [h1, ← map_sub, norm_RMap]
  rfl

/-- **MUST-FIRE / DENOTATION CONTROL.** The identity is about the transport that factors THROUGH
the bond. If one instead compares `RMap g (lam (shift x μ))` to `RMap g (lam x)` — i.e. forgets the
`U(x,μ)` factor, the exact silent error §LEAN-D warns about — one gets the FLAT difference, and at
the concrete non-flat `witnessU`, `witnessMElem` background these two differ: `RMap witnessMElem`
sends `suTwoWitness` to `-suTwoWitness`, so the covariant difference has norm `2‖suTwoWitness‖`
while the flat difference has norm `0`. -/
theorem transport_step_flat_differs :
    ‖RMap (1 * witnessMElem) suTwoWitness - RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
        suTwoWitness‖
      ≠ ‖RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) suTwoWitness
        - RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) suTwoWitness‖ := by
  have h1 : RMap (1 * witnessMElem) suTwoWitness = -suTwoWitness := by
    rw [one_mul, RMap_witnessMElem]
  have h2 : RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) suTwoWitness = suTwoWitness := by
    rw [RMap_one]; rfl
  rw [h1, h2, sub_self, norm_zero]
  have h3 : (-suTwoWitness - suTwoWitness) = (-2 : ℝ) • suTwoWitness := by
    module
  rw [h3, norm_smul]
  have h4 : ‖suTwoWitness‖ ≠ 0 := norm_ne_zero_iff.mpr suTwoWitness_ne_zero
  simp only [Real.norm_eq_abs]
  intro hc
  apply h4
  have : |(-2 : ℝ)| = 2 := by norm_num
  rw [this] at hc
  linarith [norm_nonneg (suTwoWitness), hc]

#print axioms transport_step_norm_eq
#print axioms transport_step_flat_differs

/-! ## §5 — THE MEAN-ZERO POINCARÉ INEQUALITY ON THE `ell = 2`, `d = 3` STAIRCASE TREE

The block `B(y)` at `ell = 2` in `d = 3` has eight sites `{0,1}³`. The coordinate-order path family
rooted at `000` is the spanning tree with the seven bonds

    000-001,  000-010,  010-011,  000-100,  100-101,  100-110,  110-111

(`compute/kappa_bound/tree_gap.py` enumerates the same seven from the predecessor rule). By §4 the
transported differences along these seven bonds are EXACTLY the covariant derivatives on them. -/

section TreePoincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- `‖a + b‖² ≤ 2(‖a‖² + ‖b‖²)`. -/
theorem norm_add_sq_le_two (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := norm_add_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + b), sq_nonneg (‖a‖ - ‖b‖), h]

omit [InnerProductSpace ℝ E] in
/-- `‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)`. -/
theorem norm_add3_sq_le_three (a b c : E) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    le_trans (norm_add_le _ _) (by linarith [norm_add_le a b])
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg (a + b + c),
    sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖), h1]

/-- **MEAN-ZERO SHIFT.** If eight vectors sum to zero then their energy is at most their energy
about ANY point: `Σ‖m_i‖² ≤ Σ‖m_i − c‖²`, because the difference is `+8‖c‖² ≥ 0`. -/
theorem mean_zero_le_shift (m0 m1 m2 m3 m4 m5 m6 m7 c : E)
    (h : m0 + m1 + m2 + m3 + m4 + m5 + m6 + m7 = 0) :
    ‖m0‖ ^ 2 + ‖m1‖ ^ 2 + ‖m2‖ ^ 2 + ‖m3‖ ^ 2 + ‖m4‖ ^ 2 + ‖m5‖ ^ 2 + ‖m6‖ ^ 2 + ‖m7‖ ^ 2
      ≤ ‖m0 - c‖ ^ 2 + ‖m1 - c‖ ^ 2 + ‖m2 - c‖ ^ 2 + ‖m3 - c‖ ^ 2
        + ‖m4 - c‖ ^ 2 + ‖m5 - c‖ ^ 2 + ‖m6 - c‖ ^ 2 + ‖m7 - c‖ ^ 2 := by
  have hsum : (inner ℝ (m0 + m1 + m2 + m3 + m4 + m5 + m6 + m7) c : ℝ) = 0 := by
    rw [h, inner_zero_left]
  simp only [inner_add_left] at hsum
  have hexp : ∀ x : E, ‖x - c‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℝ x c : ℝ) + ‖c‖ ^ 2 := by
    intro x
    exact norm_sub_sq_real x c
  rw [hexp m0, hexp m1, hexp m2, hexp m3, hexp m4, hexp m5, hexp m6, hexp m7]
  nlinarith [hsum, sq_nonneg ‖c‖]

/-- **THE `ell = 2` BLOCK POINCARÉ INEQUALITY, `Psq = 8`.**

`m000 … m111` are the transported values `μ(x) = R(Γ_{y,x})λ(x)` at the eight sites of one block;
`hmean` is `Q′λ(y) = 0` (the block average vanishes; the `ell^{-d}` prefactor is a positive scalar
and clears). The right-hand side is the sum over the SEVEN staircase-tree bonds, whose summands are
by §4 exactly `‖(D_Uλ)(b)‖²`.

Constant `8`, from the path-length weights `(1,3,2,8,2,5,3)` of the seven tree bonds. -/
theorem tree_poincare_ell_two
    (m000 m001 m010 m011 m100 m101 m110 m111 : E)
    (hmean : m000 + m001 + m010 + m011 + m100 + m101 + m110 + m111 = 0) :
    ‖m000‖ ^ 2 + ‖m001‖ ^ 2 + ‖m010‖ ^ 2 + ‖m011‖ ^ 2
        + ‖m100‖ ^ 2 + ‖m101‖ ^ 2 + ‖m110‖ ^ 2 + ‖m111‖ ^ 2
      ≤ 8 * (‖m001 - m000‖ ^ 2 + ‖m010 - m000‖ ^ 2 + ‖m011 - m010‖ ^ 2
            + ‖m100 - m000‖ ^ 2 + ‖m101 - m100‖ ^ 2 + ‖m110 - m100‖ ^ 2
            + ‖m111 - m110‖ ^ 2) := by
  refine le_trans (mean_zero_le_shift m000 m001 m010 m011 m100 m101 m110 m111 m000 hmean) ?_
  have e0 : ‖m000 - m000‖ ^ 2 = 0 := by rw [sub_self, norm_zero]; ring
  have e011 : m011 - m000 = (m011 - m010) + (m010 - m000) := by abel
  have e101 : m101 - m000 = (m101 - m100) + (m100 - m000) := by abel
  have e110 : m110 - m000 = (m110 - m100) + (m100 - m000) := by abel
  have e111 : m111 - m000 = (m111 - m110) + (m110 - m100) + (m100 - m000) := by abel
  have b011 : ‖m011 - m000‖ ^ 2 ≤ 2 * (‖m011 - m010‖ ^ 2 + ‖m010 - m000‖ ^ 2) := by
    rw [e011]; exact norm_add_sq_le_two _ _
  have b101 : ‖m101 - m000‖ ^ 2 ≤ 2 * (‖m101 - m100‖ ^ 2 + ‖m100 - m000‖ ^ 2) := by
    rw [e101]; exact norm_add_sq_le_two _ _
  have b110 : ‖m110 - m000‖ ^ 2 ≤ 2 * (‖m110 - m100‖ ^ 2 + ‖m100 - m000‖ ^ 2) := by
    rw [e110]; exact norm_add_sq_le_two _ _
  have b111 : ‖m111 - m000‖ ^ 2
      ≤ 3 * (‖m111 - m110‖ ^ 2 + ‖m110 - m100‖ ^ 2 + ‖m100 - m000‖ ^ 2) := by
    rw [e111]; exact norm_add3_sq_le_three _ _ _
  have p1 : (0:ℝ) ≤ ‖m001 - m000‖ ^ 2 := sq_nonneg _
  have p2 : (0:ℝ) ≤ ‖m010 - m000‖ ^ 2 := sq_nonneg _
  have p3 : (0:ℝ) ≤ ‖m011 - m010‖ ^ 2 := sq_nonneg _
  have p4 : (0:ℝ) ≤ ‖m100 - m000‖ ^ 2 := sq_nonneg _
  have p5 : (0:ℝ) ≤ ‖m101 - m100‖ ^ 2 := sq_nonneg _
  have p6 : (0:ℝ) ≤ ‖m110 - m100‖ ^ 2 := sq_nonneg _
  have p7 : (0:ℝ) ≤ ‖m111 - m110‖ ^ 2 := sq_nonneg _
  linarith [e0, b011, b101, b110, b111, p1, p2, p3, p4, p5, p6, p7]

omit [InnerProductSpace ℝ E] in
/-- **MUST-FIRE for `hmean`.** Without the vanishing block average the inequality is FALSE: take
all eight values equal to a nonzero `v`. Every tree difference is `0`, so the right-hand side is
`0`, while the left-hand side is `8‖v‖² > 0`. -/
theorem tree_poincare_needs_mean_zero (v : E) (hv : v ≠ 0) :
    ¬ (‖v‖ ^ 2 + ‖v‖ ^ 2 + ‖v‖ ^ 2 + ‖v‖ ^ 2 + ‖v‖ ^ 2 + ‖v‖ ^ 2 + ‖v‖ ^ 2 + ‖v‖ ^ 2
        ≤ 8 * (‖v - v‖ ^ 2 + ‖v - v‖ ^ 2 + ‖v - v‖ ^ 2 + ‖v - v‖ ^ 2 + ‖v - v‖ ^ 2
              + ‖v - v‖ ^ 2 + ‖v - v‖ ^ 2)) := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  simp only [sub_self, norm_zero]
  nlinarith [hpos]

end TreePoincare

#print axioms norm_add_sq_le_two
#print axioms norm_add3_sq_le_three
#print axioms mean_zero_le_shift
#print axioms tree_poincare_ell_two
#print axioms tree_poincare_needs_mean_zero

/-! ## §6 — `κ` FROM THE POINCARÉ CONSTANT

Cauchy–Schwarz in SQUARED form throughout, so `Real.sqrt` never enters. -/

/-- `|hsInner a b| ≤ ‖a‖‖b‖`. (`StokesCommU.abs_hsInner_le` is the same fact but that module is
not in this import closure; re-derived in one line from `inner_eq_hsInner`.) -/
theorem abs_hsInner_le' (a b : SuTwo) : |hsInner a b| ≤ ‖a‖ * ‖b‖ := by
  rw [← inner_eq_hsInner]
  exact abs_real_inner_le_norm a b

/-- `covSiteInner f f = siteEnergy f`. -/
theorem covSiteInner_self (f : PeriodicLatticeSite L → SuTwo) :
    covSiteInner f f = siteEnergy f :=
  Finset.sum_congr rfl (fun x _ => hsInner_self_eq_norm_sq (f x))

/-- Cauchy–Schwarz for `covSiteInner`, squared form. -/
theorem covSiteInner_sq_le (f g : PeriodicLatticeSite L → SuTwo) :
    covSiteInner f g ^ 2 ≤ siteEnergy f * siteEnergy g := by
  have h1 : |covSiteInner f g| ≤ ∑ x : PeriodicLatticeSite L, ‖f x‖ * ‖g x‖ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun x _ => ?_))
    exact abs_hsInner_le' (f x) (g x)
  have h2 : (∑ x : PeriodicLatticeSite L, ‖f x‖ * ‖g x‖) ^ 2
      ≤ (∑ x : PeriodicLatticeSite L, ‖f x‖ ^ 2) * (∑ x : PeriodicLatticeSite L, ‖g x‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => ‖f x‖) (fun x => ‖g x‖)
  have habs : (0:ℝ) ≤ |covSiteInner f g| := abs_nonneg _
  have hsq : covSiteInner f g ^ 2 = |covSiteInner f g| ^ 2 := (sq_abs _).symm
  have h3 : |covSiteInner f g| ^ 2 ≤ (∑ x : PeriodicLatticeSite L, ‖f x‖ * ‖g x‖) ^ 2 := by
    nlinarith [habs, h1]
  rw [hsq]
  exact le_trans h3 h2

/-- Cauchy–Schwarz for `covBondInner`, squared form. -/
theorem covBondInner_sq_le (A B : Bond L → SuTwo) :
    covBondInner A B ^ 2 ≤ bondEnergy A * bondEnergy B := by
  have h1 : |covBondInner A B| ≤ ∑ b : Bond L, ‖A b‖ * ‖B b‖ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun b _ => ?_))
    exact abs_hsInner_le' (A b) (B b)
  have h2 : (∑ b : Bond L, ‖A b‖ * ‖B b‖) ^ 2
      ≤ (∑ b : Bond L, ‖A b‖ ^ 2) * (∑ b : Bond L, ‖B b‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => ‖A b‖) (fun b => ‖B b‖)
  have habs : (0:ℝ) ≤ |covBondInner A B| := abs_nonneg _
  have hsq : covBondInner A B ^ 2 = |covBondInner A B| ^ 2 := (sq_abs _).symm
  have h3 : |covBondInner A B| ^ 2 ≤ (∑ b : Bond L, ‖A b‖ * ‖B b‖) ^ 2 := by
    nlinarith [habs, h1]
  rw [hsq]
  exact le_trans h3 h2

/-- `∑_b ‖λ(b₋)‖² = 3·siteEnergy λ` — EXACT. (Re-derived; see the import note in §1a.) -/
theorem sum_tail_sq_eq (lam : PeriodicLatticeSite L → SuTwo) :
    ∑ b : Bond L, ‖lam b.1‖ ^ 2 = 3 * siteEnergy lam := by
  rw [Fintype.sum_prod_type (f := fun b : PeriodicLatticeSite L × Fin 3 => ‖lam b.1‖ ^ 2)]
  unfold siteEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp [Finset.sum_const]

/-- `∑_b ‖λ(b₊)‖² = 3·siteEnergy λ` — same count after the shift bijection. -/
theorem sum_head_sq_eq (lam : PeriodicLatticeSite L → SuTwo) :
    ∑ b : Bond L, ‖lam (periodicLatticeShift b.1 b.2)‖ ^ 2 = 3 * siteEnergy lam := by
  rw [Fintype.sum_prod_type
    (f := fun b : PeriodicLatticeSite L × Fin 3 => ‖lam (periodicLatticeShift b.1 b.2)‖ ^ 2)]
  rw [Finset.sum_comm]
  have hone : ∀ μ : Fin 3,
      (∑ x : PeriodicLatticeSite L, ‖lam (periodicLatticeShift x μ)‖ ^ 2) = siteEnergy lam := by
    intro μ
    exact Equiv.sum_comp (periodicLatticeShiftEquiv (L := L) μ) (fun y => ‖lam y‖ ^ 2)
  rw [Finset.sum_congr rfl (fun μ (_ : μ ∈ (Finset.univ : Finset (Fin 3))) => hone μ)]
  simp [Finset.sum_const]

/-- **`‖D_U‖² ≤ 12`.** (Re-derived; see the import note in §1a.) -/
theorem bondEnergy_grad_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) :
    bondEnergy (gradValueCovariant U lam) ≤ 12 * siteEnergy lam := by
  have hpt : ∀ b : Bond L, ‖gradValueCovariant U lam b‖ ^ 2
      ≤ 2 * ‖lam (periodicLatticeShift b.1 b.2)‖ ^ 2 + 2 * ‖lam b.1‖ ^ 2 := by
    intro b
    have hR : ‖RMap (U b) (lam (periodicLatticeShift b.1 b.2))‖
        = ‖lam (periodicLatticeShift b.1 b.2)‖ := norm_RMap _ _
    have h := norm_sub_le (RMap (U b) (lam (periodicLatticeShift b.1 b.2))) (lam b.1)
    rw [hR] at h
    have hg : ‖gradValueCovariant U lam b‖
        ≤ ‖lam (periodicLatticeShift b.1 b.2)‖ + ‖lam b.1‖ := h
    nlinarith [hg, norm_nonneg (gradValueCovariant U lam b),
      sq_nonneg (‖lam (periodicLatticeShift b.1 b.2)‖ - ‖lam b.1‖)]
  calc bondEnergy (gradValueCovariant U lam)
      = ∑ b : Bond L, ‖gradValueCovariant U lam b‖ ^ 2 := rfl
    _ ≤ ∑ b : Bond L, (2 * ‖lam (periodicLatticeShift b.1 b.2)‖ ^ 2 + 2 * ‖lam b.1‖ ^ 2) :=
        Finset.sum_le_sum (fun b _ => hpt b)
    _ = 12 * siteEnergy lam := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_head_sq_eq, sum_tail_sq_eq]
        ring

/-- **`rsq = 12` DERIVED, not assumed.** `hadj` is the adjoint RELATION — an identity that pins
`S = D_U^* A` uniquely, not a size assumption. From it and `‖D_U‖² ≤ 12`:
`‖S‖² = ⟨D_U S, A⟩ ≤ ‖D_U S‖‖A‖ ≤ √12‖S‖‖A‖`, hence `‖S‖² ≤ 12‖A‖²`. -/
theorem siteEnergy_le_of_adjoint
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (S : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      covSiteInner w S = covBondInner (gradValueCovariant U w) A) :
    siteEnergy S ≤ 12 * bondEnergy A := by
  have h0 : siteEnergy S = covBondInner (gradValueCovariant U S) A := by
    rw [← hadj S]; exact (covSiteInner_self S).symm
  have hcs : covBondInner (gradValueCovariant U S) A ^ 2
      ≤ bondEnergy (gradValueCovariant U S) * bondEnergy A := covBondInner_sq_le _ _
  have hD : bondEnergy (gradValueCovariant U S) ≤ 12 * siteEnergy S := bondEnergy_grad_le U S
  have hS0 : 0 ≤ siteEnergy S := siteEnergy_nonneg S
  have hE0 : 0 ≤ bondEnergy A := bondEnergy_nonneg A
  have hkey : siteEnergy S ^ 2 ≤ 12 * siteEnergy S * bondEnergy A := by
    calc siteEnergy S ^ 2 = covBondInner (gradValueCovariant U S) A ^ 2 := by rw [← h0]
      _ ≤ bondEnergy (gradValueCovariant U S) * bondEnergy A := hcs
      _ ≤ 12 * siteEnergy S * bondEnergy A := by
          exact mul_le_mul_of_nonneg_right hD hE0
  rcases eq_or_lt_of_le hS0 with h | h
  · rw [← h]; positivity
  · nlinarith [hkey, h]

/-- **THE `κ` BOUND.** `hweak` is the weak Euler–Lagrange equation `⟨λ, Δ_Uλ⟩ = ⟨λ, src⟩` at
`μ = λ`, i.e. exactly §2's `Δ(G′Rf) = Rf` paired against `λ`, using `Δ_U = D_U^*D_U` (CMP99b
(3.23)). `hPoin` is the block Poincaré inequality on `N(Q′)` — legitimate precisely because §2
proves `Q′λ = 0`. Conclusion: `hlam` of `DeltaPrimeBound.abs_deltaPrimePiForm_le` at
`κ² = rsq·Psq²`. -/
theorem siteEnergy_le_of_poincare
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam src : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) (Psq rsq : ℝ)
    (hrsq : 0 ≤ rsq)
    (hweak : bondEnergy (gradValueCovariant U lam) = covSiteInner lam src)
    (hPoin : siteEnergy lam ≤ Psq * bondEnergy (gradValueCovariant U lam))
    (hsrc : siteEnergy src ≤ rsq * bondEnergy A) :
    siteEnergy lam ≤ rsq * Psq ^ 2 * bondEnergy A := by
  have hS0 : 0 ≤ siteEnergy lam := siteEnergy_nonneg lam
  have hE0 : 0 ≤ bondEnergy A := bondEnergy_nonneg A
  have hsrc0 : 0 ≤ siteEnergy src := siteEnergy_nonneg src
  have hstep : siteEnergy lam ≤ Psq * covSiteInner lam src := by rw [← hweak]; exact hPoin
  have hcs : covSiteInner lam src ^ 2 ≤ siteEnergy lam * siteEnergy src :=
    covSiteInner_sq_le lam src
  have hI0 : 0 ≤ Psq * covSiteInner lam src := le_trans hS0 hstep
  have hsq : siteEnergy lam ^ 2 ≤ (Psq * covSiteInner lam src) ^ 2 := by
    nlinarith [hstep, hS0, hI0]
  have hkey : siteEnergy lam ^ 2 ≤ Psq ^ 2 * (siteEnergy lam * siteEnergy src) := by
    calc siteEnergy lam ^ 2 ≤ (Psq * covSiteInner lam src) ^ 2 := hsq
      _ = Psq ^ 2 * covSiteInner lam src ^ 2 := by ring
      _ ≤ Psq ^ 2 * (siteEnergy lam * siteEnergy src) := by
          exact mul_le_mul_of_nonneg_left hcs (sq_nonneg Psq)
  have hkey2 : siteEnergy lam ^ 2 ≤ Psq ^ 2 * siteEnergy lam * (rsq * bondEnergy A) := by
    have := mul_le_mul_of_nonneg_left hsrc (mul_nonneg (sq_nonneg Psq) hS0)
    nlinarith [hkey, this]
  rcases eq_or_lt_of_le hS0 with h | h
  · rw [← h]; positivity
  · nlinarith [hkey2, h]

#print axioms abs_hsInner_le'
#print axioms covSiteInner_self
#print axioms covSiteInner_sq_le
#print axioms covBondInner_sq_le
#print axioms sum_tail_sq_eq
#print axioms sum_head_sq_eq
#print axioms bondEnergy_grad_le
#print axioms siteEnergy_le_of_adjoint
#print axioms siteEnergy_le_of_poincare

/-- **THE HEADLINE, ASSEMBLED AT `ell = 2`.** `Psq = 8` (§5) and `rsq = 12` (§6) give
`κ² = 12·64 = 768`, i.e. `κ = 16√3 ≈ 27.71`. The two remaining hypotheses are exactly the two
disclosed in §1a: the block-Poincaré ASSEMBLY over the lattice, and `‖R‖ ≤ 1` at the concrete
site carrier (proved abstractly in §3). -/
theorem hlam_at_kappa_sq_768
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam src dstarA : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo)
    (hweak : bondEnergy (gradValueCovariant U lam) = covSiteInner lam src)
    (hPoin : siteEnergy lam ≤ 8 * bondEnergy (gradValueCovariant U lam))
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      covSiteInner w dstarA = covBondInner (gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA) :
    siteEnergy lam ≤ 768 * bondEnergy A := by
  have hsrc : siteEnergy src ≤ 12 * bondEnergy A :=
    le_trans hproj (siteEnergy_le_of_adjoint U dstarA A hadj)
  have h := siteEnergy_le_of_poincare U lam src A 8 12 (by norm_num) hweak hPoin hsrc
  calc siteEnergy lam ≤ 12 * (8:ℝ) ^ 2 * bondEnergy A := h
    _ = 768 * bondEnergy A := by ring

#print axioms hlam_at_kappa_sq_768

/-! ## §7 — THE COMPOSITION: does `δ ≤ γ₀(1−q²)` still close at `ell = 2`?

`deltaPiConstLocal` duplicates `DeltaPrimeBound.deltaPiConst` (not imported — see §1a). `Jsup`
enters through `DeltaPrimeBound`'s own chain `Jsup ≤ 24·η⁻²·α₀`, taken at `η⁻² = 1` (unit lattice).
-/

/-- `Jsup·κ·(28 + 48κ)` — the duplicate of `DeltaPrimeBound.deltaPiConst`. -/
noncomputable def deltaPiConstLocal (Jsup kappa : ℝ) : ℝ := Jsup * kappa * (28 + 48 * kappa)

/-- `κ = √768 = 16√3`, and `27 < κ < 28`. -/
theorem kappa_bounds : (27 : ℝ) < Real.sqrt 768 ∧ Real.sqrt 768 < 28 := by
  have h0 : (0:ℝ) ≤ 768 := by norm_num
  have hsq : Real.sqrt 768 ^ 2 = 768 := Real.sq_sqrt h0
  have hnn : (0:ℝ) ≤ Real.sqrt 768 := Real.sqrt_nonneg _
  constructor
  · nlinarith [hsq, hnn]
  · nlinarith [hsq, hnn]

/-- **THE COMPOSITION VERDICT, HALF ONE.** At the real `κ = √768` the fixed-point criterion
`δ ≤ γ₀(1−q²)` is STRICTLY VIOLATED at the tree's own regularity radius
`normAlpha = 5·10⁻⁷` (with `Jsup = 24·normAlpha`, `q = 1/2`, `γ₀ = normGamma`). -/
theorem criterion_fails_at_normAlpha :
    ¬ (deltaPiConstLocal (24 * AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha)
          (Real.sqrt 768)
        ≤ AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma * (1 - (1/2 : ℝ) ^ 2)) := by
  obtain ⟨hlo, hhi⟩ := kappa_bounds
  unfold deltaPiConstLocal AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha
    AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  intro hc
  nlinarith [hlo, hhi, hc]

/-- **THE COMPOSITION VERDICT, HALF TWO.** At `α₀ = 4·10⁻¹⁰` (about `1/1250` of `normAlpha`) the
criterion DOES close at the same `κ = √768`. -/
theorem criterion_closes_at_four_e_minus_ten :
    deltaPiConstLocal (24 * (4 / 10 ^ 10 : ℝ)) (Real.sqrt 768)
      ≤ AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma * (1 - (1/2 : ℝ) ^ 2) := by
  obtain ⟨hlo, hhi⟩ := kappa_bounds
  have hnn : (0:ℝ) ≤ Real.sqrt 768 := Real.sqrt_nonneg _
  unfold deltaPiConstLocal AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  nlinarith [hlo, hhi, hnn]

/-- Sharper lower bound: `27.7 < √768`, since `27.7² = 767.29 < 768`. -/
theorem kappa_lower_sharp : (277 / 10 : ℝ) < Real.sqrt 768 := by
  have h0 : (0:ℝ) ≤ 768 := by norm_num
  have hsq : Real.sqrt 768 ^ 2 = 768 := Real.sq_sqrt h0
  have hnn : (0:ℝ) ≤ Real.sqrt 768 := Real.sqrt_nonneg _
  nlinarith [hsq, hnn]

/-- **THE THRESHOLD IS PINNED TO WITHIN 8%, so `4·10⁻¹⁰` is not an arbitrarily small number chosen
to make the statement true.** At `α₀ = 4.3·10⁻¹⁰` the criterion ALREADY FAILS. Together with
`criterion_closes_at_four_e_minus_ten` this puts the admissible boundary strictly between
`4.0·10⁻¹⁰` and `4.3·10⁻¹⁰`. -/
theorem criterion_fails_at_four_point_three_e_minus_ten :
    ¬ (deltaPiConstLocal (24 * (43 / 10 ^ 11 : ℝ)) (Real.sqrt 768)
        ≤ AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma * (1 - (1/2 : ℝ) ^ 2)) := by
  have hlo := kappa_lower_sharp
  have hnn : (0:ℝ) ≤ Real.sqrt 768 := Real.sqrt_nonneg _
  have hsq : Real.sqrt 768 ^ 2 = 768 := Real.sq_sqrt (by norm_num)
  unfold deltaPiConstLocal AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma
  intro hc
  nlinarith [hlo, hnn, hsq, hc]

/-- **THE ITERATED BRIDGE KEEPS A POSITIVE FLOOR at `α₀ = 4·10⁻¹⁰`.** Consumes
`GammaRecursion.uniformStepGamma_of_lt_one` at `q = 1/2 < 1`, `γ₀ = normGamma > 0`. -/
theorem uniformStepGamma_at_four_e_minus_ten :
    AdalyFormal.Balaban.GammaRecursion.UniformStepGamma
      (deltaPiConstLocal (24 * (4 / 10 ^ 10 : ℝ)) (Real.sqrt 768)) (1/2 : ℝ) :=
  AdalyFormal.Balaban.GammaRecursion.uniformStepGamma_of_lt_one
    (by norm_num) (by norm_num)
    AdalyFormal.Balaban.LemmaAssemblyNormalized.normGamma_pos
    criterion_closes_at_four_e_minus_ten

/-- **MUST-NOT-FIRE CONTROL.** `deltaPiConstLocal` is not vacuously zero at the parameters used:
at `Jsup = 24·4·10⁻¹⁰` and `κ = √768` it is strictly positive, so
`criterion_closes_at_four_e_minus_ten` is not a `0 ≤ positive` triviality. -/
theorem deltaPiConstLocal_pos_at_used_point :
    0 < deltaPiConstLocal (24 * (4 / 10 ^ 10 : ℝ)) (Real.sqrt 768) := by
  obtain ⟨hlo, _⟩ := kappa_bounds
  unfold deltaPiConstLocal
  nlinarith [hlo]

/-- **MUST-FIRE CONTROL for the `κ`-dependence.** The composition verdict is genuinely about the
SIZE of `κ`: at `κ = 1` (the stand-in `DeltaPrimeBound` used for its numeric instance) the same
`Jsup = 24·normAlpha` gives a value more than `100×` smaller than at `κ = √768`. This shows the
factor is carried by `κ` and not by `Jsup`. -/
theorem kappa_drives_the_failure :
    100 * deltaPiConstLocal (24 * AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha) 1
      < deltaPiConstLocal (24 * AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha)
          (Real.sqrt 768) := by
  obtain ⟨hlo, hhi⟩ := kappa_bounds
  unfold deltaPiConstLocal AdalyFormal.Balaban.LemmaAssemblyNormalized.normAlpha
  nlinarith [hlo, hhi]

/-! ## §8 — THE LATTICE ASSEMBLY OF THE BLOCK POINCARÉ INEQUALITY

§5 gives the inequality on ONE block. This section sums it over the lattice. The two bookkeeping
facts are: the `CoarseLattice` blocks PARTITION the sites (reusing `AdmissibleSubspace`'s own
`coarseLattice_exists`/`coarseLattice_unique`, LAW-19 — not rebuilt), and the per-block tree-bond
sets are pairwise disjoint so their total is a SUB-SUM of `bondEnergy`.

`hdvd : ∀ μ, ell ∣ (L μ + 1)` and `0 < ell` are carried explicitly — this is the exact pair whose
omission makes `blockOf` truncate silently on the torus. -/

section Assembly

open AdalyFormal.Balaban.AdmissibleSubspace
  (CoarseLattice blockOf coarseLattice_exists coarseLattice_unique)

/-- **THE BLOCKS TILE.** `univ` is the union of the `CoarseLattice` blocks. -/
theorem univ_eq_biUnion_blocks (ell : ℕ) (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    (Finset.univ : Finset (PeriodicLatticeSite L))
      = (CoarseLattice L ell).biUnion (fun y => blockOf y ell) := by
  ext x
  simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion]
  obtain ⟨y, hy, hx⟩ := coarseLattice_exists ell hell hdvd x
  exact ⟨y, hy, hx⟩

/-- **THE BLOCKS DO NOT OVERLAP.** -/
theorem blocks_pairwiseDisjoint (ell : ℕ) :
    ((CoarseLattice L ell : Finset (PeriodicLatticeSite L)) :
        Set (PeriodicLatticeSite L)).PairwiseDisjoint (fun y => blockOf y ell) := by
  intro y hy y' hy' hne
  simp only [Function.onFun]
  refine Finset.disjoint_left.mpr (fun x hx hx' => hne ?_)
  exact coarseLattice_unique ell (Finset.mem_coe.mp hy) (Finset.mem_coe.mp hy') hx hx'

/-- `siteEnergy` decomposes exactly into the per-block energies. -/
theorem siteEnergy_eq_sum_blocks (lam : PeriodicLatticeSite L → SuTwo) (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    siteEnergy lam = ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, ‖lam x‖ ^ 2 := by
  unfold siteEnergy
  rw [show (Finset.univ : Finset (PeriodicLatticeSite L))
        = (CoarseLattice L ell).biUnion (fun y => blockOf y ell) from
      univ_eq_biUnion_blocks ell hell hdvd,
    Finset.sum_biUnion (blocks_pairwiseDisjoint ell)]

/-- **THE PER-BLOCK BOND SETS SUM INTO `bondEnergy`** — provided they are pairwise disjoint. -/
theorem sum_treeBonds_le_bondEnergy (G : Bond L → SuTwo) (ell : ℕ)
    (tb : PeriodicLatticeSite L → Finset (Bond L))
    (hdisj : ((CoarseLattice L ell : Finset (PeriodicLatticeSite L)) :
        Set (PeriodicLatticeSite L)).PairwiseDisjoint tb) :
    ∑ y ∈ CoarseLattice L ell, ∑ b ∈ tb y, ‖G b‖ ^ 2 ≤ bondEnergy G := by
  rw [← Finset.sum_biUnion hdisj]
  unfold bondEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => sq_nonneg _)

/-- **THE ASSEMBLY.** The per-block Poincaré inequality at constant `8` (which is §5's
`tree_poincare_ell_two` transported by §4) summed over the lattice gives
`siteEnergy λ ≤ 8·bondEnergy (D_Uλ)` — i.e. exactly `hPoin` of `hlam_at_kappa_sq_768`. -/
theorem poincare_assembly
    (lam : PeriodicLatticeSite L → SuTwo) (G : Bond L → SuTwo) (ell : ℕ)
    (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (tb : PeriodicLatticeSite L → Finset (Bond L))
    (hdisj : ((CoarseLattice L ell : Finset (PeriodicLatticeSite L)) :
        Set (PeriodicLatticeSite L)).PairwiseDisjoint tb)
    (hblock : ∀ y ∈ CoarseLattice L ell,
        ∑ x ∈ blockOf y ell, ‖lam x‖ ^ 2 ≤ 8 * ∑ b ∈ tb y, ‖G b‖ ^ 2) :
    siteEnergy lam ≤ 8 * bondEnergy G := by
  rw [siteEnergy_eq_sum_blocks lam ell hell hdvd]
  have h1 : ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, ‖lam x‖ ^ 2
      ≤ ∑ y ∈ CoarseLattice L ell, 8 * ∑ b ∈ tb y, ‖G b‖ ^ 2 := Finset.sum_le_sum hblock
  have h2 : ∑ y ∈ CoarseLattice L ell, 8 * ∑ b ∈ tb y, ‖G b‖ ^ 2
      = 8 * ∑ y ∈ CoarseLattice L ell, ∑ b ∈ tb y, ‖G b‖ ^ 2 := by rw [Finset.mul_sum]
  have h3 := sum_treeBonds_le_bondEnergy G ell tb hdisj
  linarith [h1, h2.le, h2.ge, h3]

/-! ### §8a — THE SEVEN TREE BONDS AT `ell = 2`, CONCRETELY, AND `hdisj` DISCHARGED -/

/-- `((shift x μ) μ).val = (x μ).val + 1` when the step does not wrap. -/
theorem shift_val_self (x : PeriodicLatticeSite L) (μ : Fin 3) (h : (x μ).val < L μ) :
    ((periodicLatticeShift x μ) μ).val = (x μ).val + 1 := by
  have hupd : (periodicLatticeShift x μ) μ = x μ + 1 := Function.update_self _ _ _
  rw [hupd]
  exact Fin.val_add_one_of_lt h

/-- The other coordinates are untouched. (`U1Anchor` has the same one-liner but is not in this
import closure; re-derived from `Function.update_of_ne`.) -/
theorem shift_apply_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    periodicLatticeShift x μ ν = x ν :=
  Function.update_of_ne h _ _

/-- A one-step shift of a fitting corner stays inside its own `ell = 2` block. -/
theorem shift_mem_blockTwo {y : PeriodicLatticeSite L} (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (μ : Fin 3) : periodicLatticeShift y μ ∈ AdmissibleSubspace.blockOf y 2 := by
  rw [AdmissibleSubspace.mem_blockOf]
  intro ν
  by_cases h : ν = μ
  · subst h
    rw [shift_val_self y ν (hlt ν)]
    omega
  · rw [shift_apply_ne y μ ν h]
    omega

/-- The diagonal corner `y + e₀ + e₁` also stays inside the `ell = 2` block. -/
theorem shift2_mem_blockTwo {y : PeriodicLatticeSite L} (hlt : ∀ μ : Fin 3, (y μ).val < L μ) :
    periodicLatticeShift (periodicLatticeShift y 0) 1 ∈ AdmissibleSubspace.blockOf y 2 := by
  have a01 : ((periodicLatticeShift y 0) (1 : Fin 3)).val = (y 1).val := by
    rw [shift_apply_ne y 0 1 (by decide)]
  rw [AdmissibleSubspace.mem_blockOf]
  intro ν
  by_cases h1 : ν = 1
  · subst h1
    rw [shift_val_self (periodicLatticeShift y 0) 1 (by rw [a01]; exact hlt 1), a01]
    omega
  · rw [shift_apply_ne (periodicLatticeShift y 0) 1 ν h1]
    by_cases h0 : ν = 0
    · subst h0
      rw [shift_val_self y 0 (hlt 0)]
      omega
    · rw [shift_apply_ne y 0 ν h0]
      omega

/-- `y` is in its own block. -/
theorem self_mem_blockTwo (y : PeriodicLatticeSite L) :
    y ∈ AdmissibleSubspace.blockOf y 2 := by
  rw [AdmissibleSubspace.mem_blockOf]
  intro ν
  omega

/-- **THE SEVEN STAIRCASE-TREE BONDS** of the `ell = 2` block based at `y`, in the coordinate order
`0 → 1 → 2` (`compute/kappa_bound/tree_gap.py` enumerates the same seven from the predecessor rule):
`000-001`, `000-010`, `010-011`, `000-100`, `100-101`, `100-110`, `110-111`. -/
def treeBondsTwo (y : PeriodicLatticeSite L) : Finset (Bond L) :=
  {(y, (2 : Fin 3)), (y, (1 : Fin 3)), (periodicLatticeShift y 1, (2 : Fin 3)),
   (y, (0 : Fin 3)), (periodicLatticeShift y 0, (2 : Fin 3)),
   (periodicLatticeShift y 0, (1 : Fin 3)),
   (periodicLatticeShift (periodicLatticeShift y 0) 1, (2 : Fin 3))}

/-- Every tree bond of the block at `y` has its TAIL inside that block. -/
theorem treeBondsTwo_tail_mem (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ AdmissibleSubspace.CoarseLattice L 2) :
    ∀ b ∈ treeBondsTwo y, b.1 ∈ AdmissibleSubspace.blockOf y 2 := by
  have hfits := AdmissibleSubspace.coarseLattice_mem_fits hdvd hy
  have hlt : ∀ μ : Fin 3, (y μ).val < L μ := by
    intro μ; have := hfits μ; omega
  intro b hb
  simp only [treeBondsTwo, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with h | h | h | h | h | h | h <;> subst h
  · exact self_mem_blockTwo y
  · exact self_mem_blockTwo y
  · exact shift_mem_blockTwo hlt 1
  · exact self_mem_blockTwo y
  · exact shift_mem_blockTwo hlt 0
  · exact shift_mem_blockTwo hlt 0
  · exact shift2_mem_blockTwo hlt

/-- **`hdisj` DISCHARGED** for the concrete `treeBondsTwo`: bonds of distinct coarse blocks are
distinct, because their tails lie in disjoint blocks. -/
theorem treeBondsTwo_pairwiseDisjoint (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    ((AdmissibleSubspace.CoarseLattice L 2 : Finset (PeriodicLatticeSite L)) :
        Set (PeriodicLatticeSite L)).PairwiseDisjoint treeBondsTwo := by
  intro y hy y' hy' hne
  simp only [Function.onFun]
  refine Finset.disjoint_left.mpr (fun b hb hb' => hne ?_)
  exact AdmissibleSubspace.coarseLattice_unique 2 (Finset.mem_coe.mp hy) (Finset.mem_coe.mp hy')
    (treeBondsTwo_tail_mem hdvd (Finset.mem_coe.mp hy) b hb)
    (treeBondsTwo_tail_mem hdvd (Finset.mem_coe.mp hy') b hb')

/-- **THE ASSEMBLY AT `ell = 2`, WITH `hdisj` GONE.** Only the per-block inequality remains as a
hypothesis, and that is `tree_poincare_ell_two` transported by `transport_step_norm_eq`. -/
theorem poincare_assembly_two
    (lam : PeriodicLatticeSite L → SuTwo) (G : Bond L → SuTwo)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hblock : ∀ y ∈ AdmissibleSubspace.CoarseLattice L 2,
        ∑ x ∈ AdmissibleSubspace.blockOf y 2, ‖lam x‖ ^ 2
          ≤ 8 * ∑ b ∈ treeBondsTwo y, ‖G b‖ ^ 2) :
    siteEnergy lam ≤ 8 * bondEnergy G :=
  poincare_assembly lam G 2 (by norm_num) hdvd treeBondsTwo
    (treeBondsTwo_pairwiseDisjoint hdvd) hblock

end Assembly

/-- **MUST-FIRE for `hdisj`.** Without pairwise disjointness the sub-sum step is FALSE: two index
values reusing the SAME one-element bond set give total `2` against an ambient `1`. -/
theorem subsum_needs_disjointness :
    ¬ (∑ _y : Fin 2, ∑ _b ∈ (Finset.univ : Finset (Fin 1)), (1:ℝ)
        ≤ ∑ _b ∈ (Finset.univ : Finset (Fin 1)), (1:ℝ)) := by
  norm_num

/-- **BOTH READINGS OF `N(Q′)` ARE COVERED.** CMP99b (3.24) sums `j = 0 … k`, so if `Q′` is read as
the FULL tower including `Q'_0` (which CMP95 (1.20) makes the identity up to `η^d`), then
`N(Q′) = {0}`, `λ ≡ 0`, and `hlam` holds trivially at every `κ` — this branch. If instead `Q′`
carries the `ell`-scale block averaging (the non-degenerate reading everything else here assumes),
§5's Poincaré applies. There is no third reading in which the `ell`-block constraint is absent AND
`N(Q′)` is non-trivial, because the constraint set only shrinks as scales are added. -/
theorem hlam_at_degenerate_kernel (A : Bond L → SuTwo) :
    siteEnergy (fun _ : PeriodicLatticeSite L => (0 : SuTwo)) ≤ 768 * bondEnergy A := by
  have h0 : siteEnergy (fun _ : PeriodicLatticeSite L => (0 : SuTwo)) = 0 := by
    unfold siteEnergy
    simp
  rw [h0]
  have := bondEnergy_nonneg A
  linarith

#print axioms univ_eq_biUnion_blocks
#print axioms blocks_pairwiseDisjoint
#print axioms siteEnergy_eq_sum_blocks
#print axioms sum_treeBonds_le_bondEnergy
#print axioms poincare_assembly
#print axioms shift_val_self
#print axioms shift_apply_ne
#print axioms shift_mem_blockTwo
#print axioms shift2_mem_blockTwo
#print axioms self_mem_blockTwo
#print axioms treeBondsTwo
#print axioms treeBondsTwo_tail_mem
#print axioms treeBondsTwo_pairwiseDisjoint
#print axioms poincare_assembly_two
#print axioms subsum_needs_disjointness
#print axioms hlam_at_degenerate_kernel

#print axioms deltaPiConstLocal
#print axioms kappa_bounds
#print axioms criterion_fails_at_normAlpha
#print axioms kappa_lower_sharp
#print axioms criterion_fails_at_four_point_three_e_minus_ten
#print axioms criterion_closes_at_four_e_minus_ten
#print axioms uniformStepGamma_at_four_e_minus_ten
#print axioms deltaPiConstLocal_pos_at_used_point
#print axioms kappa_drives_the_failure

end AdalyFormal.Balaban.KappaBound
