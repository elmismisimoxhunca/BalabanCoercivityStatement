/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.TowerLawCovariant

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `Cmp98GammaPrimary.lean` — the PRIMARY definition of `U(Γ^{(j)}_{y,x})`, and what follows

## The source, quoted

`TowerLawCovariant`'s closing note records that CMP99b p.393 and p.401 both cite *"(52), (53) in
[5]"* for the contours `Γ^{(j)}_{y,x}`, that those labels do NOT match published CMP98, and that
the origin of the mismatch was **unresolved**. It also poses a live question:

> *"Whether our tree, rather than the source, is the origin of the claim that those coincide is
> NOT YET SETTLED and is the live question."*

This module carries the answer. The primary definition was found, and it is not at (52),(53); it
is an **unnumbered display on CMP98 printed p.29**, sitting between (76) and (77) — the likeliest
reason it was mis-cited: it has no number to cite. Verbatim, from the 300 dpi page image
(`compute/cmp98_gamma_o1/renders/CMP98_pdf13-13.png`, pdf p.13 = printed p.29, offset 16):

> Let us denote  `U₀(Γ^{(j)}_{x_j,x}) = Ū₀^{j-1}(Γ_{x_j,x_{j-1}})·…·Ū₀(Γ_{x_2,x_1}) U₀(Γ_{x_1,x})`,
> then `(R̄^j_{0,x_{j+1}} R̄^{j-1}_{0,x_j}·…·R̄_{0,x_2} R_{0,x_1} u)(x)`
> `= R(U₀(Γ^{(j+1)}_{x_{j+1},x})) u(x)`, and we have the equality

and CMP98 p.30, immediately after (77) (`renders/CMP98_pdf14-14.png`):

> where the symbol `(R_{0,x_{j+1}} U₁)(Γ^{(j+1)}_{x_{j+1},x})` is defined by the last equation.

CMP99b p.401 (3.55) applies exactly that display to the field `U'U`
(`renders/CMP99b_pdf13-13.png`), and pins the index chain in the prose below it:

> where the sequence of points `y = x_j, x_{j-1},…,x_2, x_1, x = x_0` is defined by the conditions
> `x_l ∈ B(x_{l+1})`, or `x ∈ B^l(x_l)`.

## THE ANSWER: RECURSIVE, and therefore NOT DEFERRED

`Γ^{(j)}_{y,x}` standing alone is never given as a set of bonds anywhere in CMP98. Only the group
element `U₀(Γ^{(j)}_{y,x})` is defined, and it is defined — by DENOTATION, "let us denote" — as an
ordered product with **one factor per RG level**, the factor at level `l` being a holonomy of the
`l`-times blocked field `Ū₀^l` along the ONE-STEP contour `Γ_{x_{l+1},x_l}` at spacing `L^l η`.
Coarsest factor leftmost.

Three consequences; the third settles this tree's live question.

1. **CMP99b (3.19)'s second equality is true BY DEFINITION** — `Q'_j(U) = Q'(Ū^{j-1})⋯Q'(U)`
   expanded is a sum over `x ∈ B^j(y)` whose transport is precisely that ordered product. There is
   no deferred assertion at (3.19), and no independently-defined one-shot object either: (3.19)
   contains nothing that (3.18) did not.
2. **`U(Γ^{(j)}_{y,x})` is NOT a fine-lattice parallel transport.** It reads the whole tower
   `Ū⁰,…,Ū^{j-1}`, each on its own lattice. The notation `Γ^{(j)}` names no path. §6's
   `gammaVarOf_not_determined_by_level_zero` makes this a theorem rather than a remark.
3. **Therefore the identity `composite = one-shot average of the FINE field`, which
   `TowerLawCov.tower_law_cov_refuted` kills, is OURS, not Bałaban's.** The source's one-shot form
   (3.19) uses `U(Γ^{(j)})`, i.e. the composite's own transport — not `rhsTransport`'s fine
   holonomy. `tower_law_cov_refuted` remains correct mathematics; it refutes a statement the
   source never makes.

## What is built here

* **§1** `gammaVarOf` / `stepVar` / `gammaVar` — the p.29 object, at ARBITRARY `j`. The tree
  previously had only the `j = 2` instance, implicit inside `TowerLawCov.lhsTransport`.
* **§2** `gammaVarOf_eq_prod`, `RMap_gammaVarOf_foldl` — CMP99b (3.19) as a composition law at
  arbitrary `j`: applying the one-step transports in RG order (level `0` first) equals `R` of the
  single element `U(Γ^{(j)}_{y,x})`. EXACT, no error term, at any background.
* **§3** `norm_RMap_gammaVarOf_sub_self_le` — the accumulation law. The defect of the whole tower
  product is at most the **SUM** of the per-level defects: additive, not multiplicative.
* **§4** `geometricAccumulation_le`, `norm_RMap_gammaVarOf_sub_self_le_geometric` — **the
  `j`-uniform corollary.** If the per-level defects decay geometrically towards the coarse end,
  the total is bounded by a constant with NO `j` in it. That is the shape CMP99b p.401 itself
  uses: its bounds carry `ξ = L^{-j}` against a level factor `L^{l+1}`, so the level-`l` term is
  `O(1)α₁L^{l+1-j}` and the printed total under (3.57) is
  `|(U'U)(Γ^{(j)}_{y,x})(U(Γ^{(j)}_{y,x}))^{-1} − 1| < O(1)α₁` — no `j` in it.
* **§4b** `geometric_beats_trivial` and its must-fire control — §4's bound is stronger than the
  trivial `2‖X‖` **iff** `c/(1−r) < 2`. `GOAL_LEMMA` §7d's own bar, made a theorem. Nothing here
  claims that condition holds for Bałaban's tower.
* **§5** `lhsTransport_eq_gammaVarOf` — the DENOTATION BRIDGE: the tree's existing `lhsTransport`
  IS this object at `j = 2`. So `TowerLawCov.lhs_expand`, already proved and axiom-clean, is
  CMP99b (3.19) at `j = 2`, and §2 is its extension to all `j`.
* **§6** controls: must-not-fire at the trivial tower; a dependence witness showing the level-`≥1`
  data genuinely enters (abstract in §6, and again at the CONCRETE field level on the tree's own
  `witL7` torus at `ell = 2` in §6b); a garbage substitution showing §3 is not algebraically forced.

## HONEST SCOPE

* §3/§4 take the per-level defect bounds as HYPOTHESES. Supplying them from a curvature bound on
  `U` is NOT done here and is not claimed: it needs a contour-holonomy bound at every level, i.e.
  CMP98 Prop. 1 (51) / Prop. 2 (54) plus the axial-gauge conditions (64),(66),(67). What §3/§4
  establish is the ACCUMULATION LAW — that the level defects enter additively and, under geometric
  decay, `j`-uniformly. That is the piece `TowerLawCovariant`'s own scope note called unstateable
  there ("nothing tracks that"), because that module carries a single unit-level field `V` and no
  tower.
* §4's `geometricAccumulation_le` is arithmetic about a hypothesised decay profile. It does NOT
  assert that Bałaban's `α₁` bounds hold, and it is NOT a proof of `k`-uniformity of anything.
* `d = 3`, `SU(2)`, and the tree's `coarseGammaPath` staircase throughout — the same conventions
  `TowerLawCovariant` uses, so the §5 bridge is an identity and not a re-encoding.
* This module does not touch `Spine`, proves no coercivity, and asserts nothing about `Δ_k`.
-/

namespace AdalyFormal.Balaban.Cmp98Gamma

open scoped Matrix

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.Q1Real (transportPath GammaPath)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath coarseTransportPath
  coarsePathHolonomy_trivialU coarseGammaPath_self lhsTransport witnessMElem_ne_one)
open AdalyFormal.Balaban.ThirdLevelWitness (witL7)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE OBJECT (CMP98 p.29, the unnumbered display between (76) and (77))

`gammaVarOf` is the ordered product with the source's ORDER: coarsest factor LEFTMOST, exactly as
printed (`Ū₀^{j-1}(Γ_{x_j,x_{j-1}})·…·Ū₀(Γ_{x_2,x_1})U₀(Γ_{x_1,x})`, and again in CMP99b (3.55)).
Taking the step family as an argument keeps the ORDER law (§2/§3) separate from the CHOICE of step
(§1's `stepVar`), so §5 can instantiate it against the tree's existing `lhsTransport` without
re-encoding anything. -/

/-- **`U₀(Γ^{(j)}_{x_j,x})`, given a family of one-step contour variables.** `T l` is the level-`l`
factor `Ū₀^l(Γ_{x_{l+1},x_l})`. `gammaVarOf T j = T (j-1) * … * T 1 * T 0`. -/
def gammaVarOf (T : ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ
  | 0 => 1
  | (l + 1) => T l * gammaVarOf T l

@[simp] theorem gammaVarOf_zero (T : ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    gammaVarOf T 0 = 1 := rfl

@[simp] theorem gammaVarOf_succ (T : ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ) (l : ℕ) :
    gammaVarOf T (l + 1) = T l * gammaVarOf T l := rfl

/-- **The level-`l` one-step contour variable `Ū₀^l(Γ_{x_{l+1},x_l})`.** `Ubar l` is Bałaban's
`Ū₀^l` (`Ubar 0 = U₀`); `anc l` is the source's `x_l`, with `anc 0 = x` and `anc j = y`, the chain
pinned by CMP99b p.401's *"`x_l ∈ B(x_{l+1})`, or `x ∈ B^l(x_l)`"*. The level-`l` lattice has
spacing `ell^l`, which is why the holonomy is read at `ell ^ l`. -/
noncomputable def stepVar (ell : ℕ)
    (Ubar : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (anc : ℕ → PeriodicLatticeSite L) (l : ℕ) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  coarsePathHolonomy (ell ^ l) (Ubar l) (anc (l + 1))
    (coarseGammaPath (ell ^ l) (anc (l + 1)) (anc l))

/-- **`U₀(Γ^{(j)}_{y,x})` — CMP98 p.29, in the tree's conventions.** -/
noncomputable def gammaVar (ell : ℕ)
    (Ubar : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (anc : ℕ → PeriodicLatticeSite L) (j : ℕ) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  gammaVarOf (stepVar ell Ubar anc) j

/-! ## §2 — CMP99b (3.19), AS A COMPOSITION LAW, AT ARBITRARY `j`

`Q'_j(U) = Q'(Ū^{j-1})⋯Q'(Ū)Q'(U)` acts on the algebra by applying `R` of the level-`0` transport,
then `R` of the level-`1` transport, …. (3.19) says that equals `R` of the SINGLE element
`U(Γ^{(j)}_{y,x})`. Given §1's definition of that element, this is exactly the statement that the
ordered product telescopes — and it is EXACT: no error term, at any `j`, at any background. -/

/-- The ordered product, written as a `List.prod` — the source's `Ū^{j-1}(Γ)·…·U(Γ)` literally. -/
theorem gammaVarOf_eq_prod (T : ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ) (j : ℕ) :
    gammaVarOf T j = (((List.range j).map T).reverse).prod := by
  induction j with
  | zero => simp
  | succ l ih =>
    rw [gammaVarOf_succ, ih, List.range_succ, List.map_append, List.reverse_append]
    simp

/-- **(3.19), transport half, arbitrary `j`.** Applying the one-step transports in RG order — level
`0` first, then level `1`, … — is the same as applying `R` of `U(Γ^{(j)}_{y,x})`. -/
theorem RMap_gammaVarOf_foldl (T : ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ) (j : ℕ) (X : SuTwo) :
    RMap (gammaVarOf T j) X = (List.range j).foldl (fun Y l => RMap (T l) Y) X := by
  induction j with
  | zero => simp [RMap_one]
  | succ l ih =>
    rw [List.range_succ, List.foldl_append, ← ih, gammaVarOf_succ, ← RMap_mul_apply]
    simp

/-! ## §3 — THE ACCUMULATION LAW

The defect of the whole tower product is at most the SUM of the per-level defects. Additive, not
multiplicative: `R` of each factor is an ISOMETRY of `𝔰𝔲(2)` (`TowerLawCov.norm_RMap`), so no
level's defect is amplified by the levels below it. -/

/-- **`‖R(U(Γ^{(j)}))X − X‖ ≤ (Σ_{l<j} δ l)·‖X‖`.** -/
theorem norm_RMap_gammaVarOf_sub_self_le (T : ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (δ : ℕ → ℝ) (j : ℕ) (X : SuTwo)
    (hδ : ∀ l < j, 2 * RMapLipschitz.frobNorm ((T l : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ l) :
    ‖RMap (gammaVarOf T j) X - X‖ ≤ (∑ l ∈ Finset.range j, δ l) * ‖X‖ := by
  induction j with
  | zero => simp [RMap_one]
  | succ l ih =>
    have ihl : ‖RMap (gammaVarOf T l) X - X‖ ≤ (∑ i ∈ Finset.range l, δ i) * ‖X‖ :=
      ih (fun i hi => hδ i (Nat.lt_succ_of_lt hi))
    have hiso : ‖RMap (gammaVarOf T l) X‖ = ‖X‖ :=
      AdalyFormal.Balaban.TowerLawCov.norm_RMap _ X
    have hstep : ‖RMap (T l) (RMap (gammaVarOf T l) X) - RMap (gammaVarOf T l) X‖
        ≤ δ l * ‖X‖ := by
      refine le_trans (RMapLipschitz.norm_RMap_sub_self_le (T l) (RMap (gammaVarOf T l) X)) ?_
      rw [hiso]
      exact mul_le_mul_of_nonneg_right (hδ l (Nat.lt_succ_self l)) (norm_nonneg X)
    have hsplit : RMap (gammaVarOf T (l + 1)) X - X
        = (RMap (T l) (RMap (gammaVarOf T l) X) - RMap (gammaVarOf T l) X)
          + (RMap (gammaVarOf T l) X - X) := by
      rw [gammaVarOf_succ, ← RMap_mul_apply]
      abel
    calc ‖RMap (gammaVarOf T (l + 1)) X - X‖
        ≤ ‖RMap (T l) (RMap (gammaVarOf T l) X) - RMap (gammaVarOf T l) X‖
            + ‖RMap (gammaVarOf T l) X - X‖ := by rw [hsplit]; exact norm_add_le _ _
      _ ≤ δ l * ‖X‖ + (∑ i ∈ Finset.range l, δ i) * ‖X‖ := add_le_add hstep ihl
      _ = (∑ i ∈ Finset.range (l + 1), δ i) * ‖X‖ := by
            rw [Finset.sum_range_succ]; ring

/-! ## §4 — THE `j`-UNIFORM COROLLARY -/

/-- `∑_{i<j} r^i ≤ 1/(1−r)` for `0 ≤ r < 1`, uniform in `j`. -/
theorem geom_sum_le_inv (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (j : ℕ) :
    (∑ i ∈ Finset.range j, r ^ i) ≤ 1 / (1 - r) := by
  have hpos : (0 : ℝ) < 1 - r := by linarith
  induction j with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg zero_le_one (le_of_lt hpos)
  | succ l ih =>
    have hstep : (∑ i ∈ Finset.range (l + 1), r ^ i) = r * (∑ i ∈ Finset.range l, r ^ i) + 1 :=
      geom_sum_succ
    have hkey : r * (∑ i ∈ Finset.range l, r ^ i) ≤ r * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left ih hr0
    have harith : r * (1 / (1 - r)) + 1 = 1 / (1 - r) := by
      field_simp
      ring
    rw [hstep]
    linarith

/-- **`∑_{l<j} c·r^{j−1−l} ≤ c/(1−r)` — a bound with NO `j` in it.** The level index is reflected:
the level-`l` term carries `r^{j−1−l}`, i.e. decay towards the COARSE end, which is the profile
CMP99b p.401 produces from `ξ = L^{−j}` against the level factor `L^{l+1}`. -/
theorem geometricAccumulation_le (c r : ℝ) (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) (j : ℕ) :
    (∑ l ∈ Finset.range j, c * r ^ (j - 1 - l)) ≤ c / (1 - r) := by
  have hrev : (∑ l ∈ Finset.range j, c * r ^ (j - 1 - l))
      = ∑ i ∈ Finset.range j, c * r ^ i :=
    Finset.sum_range_reflect (fun i => c * r ^ i) j
  rw [hrev, ← Finset.mul_sum]
  calc c * (∑ i ∈ Finset.range j, r ^ i) ≤ c * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_sum_le_inv r hr0 hr1 j) hc
    _ = c / (1 - r) := by ring

/-- **The `j`-uniform tower-defect bound.** Under a geometrically decaying per-level defect
profile, `R(U(Γ^{(j)}))` moves any algebra vector by at most `c/(1−r)·‖X‖`, with `j` absent from
the constant. -/
theorem norm_RMap_gammaVarOf_sub_self_le_geometric
    (T : ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ) (c r : ℝ) (j : ℕ) (X : SuTwo)
    (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδ : ∀ l < j, 2 * RMapLipschitz.frobNorm ((T l : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      ≤ c * r ^ (j - 1 - l)) :
    ‖RMap (gammaVarOf T j) X - X‖ ≤ (c / (1 - r)) * ‖X‖ := by
  refine le_trans (norm_RMap_gammaVarOf_sub_self_le T (fun l => c * r ^ (j - 1 - l)) j X hδ) ?_
  exact mul_le_mul_of_nonneg_right (geometricAccumulation_le c r hc hr0 hr1 j) (norm_nonneg X)

/-! ### §4b — DOES IT BEAT ASSERTING NOTHING?

`GOAL_LEMMA` §7d sets the bar explicitly — the surviving error form there was measured at `80`
against a trivial a-priori bound of `2·Kv = 2`, i.e. **40× weaker than asserting nothing**, and the
verdict was *"it must beat `2·Kv` to be worth stating at all."* The trivial bound here is `2‖X‖`
(`R` is an isometry). So §4's bound is worth stating exactly when `c/(1−r) < 2`, and that
comparison is made a THEOREM rather than a remark. It is a CONDITION, not a claim that the
condition holds: nothing here asserts what `c` and `r` are for Bałaban's tower. -/

/-- The trivial a-priori bound. (`RegularUPerturbation.norm_RMap_sub_self_le_two` is the same
statement and already exists in the tree; it is re-proved in two lines here rather than imported,
because adding an import to a module this heavily shared risks §PIN-INSTANCE. LAW-19 disclosure:
this is a deliberate non-reuse, not an oversight.) -/
theorem norm_RMap_sub_self_le_two_local (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    ‖RMap g X - X‖ ≤ 2 * ‖X‖ := by
  refine le_trans (norm_sub_le _ _) ?_
  rw [AdalyFormal.Balaban.TowerLawCov.norm_RMap]
  linarith

/-- **§4 beats the trivial bound iff `c/(1−r) < 2`.** Both halves are proved: the bound holds, and
under the stated condition it is strictly stronger than asserting nothing. -/
theorem geometric_beats_trivial
    (T : ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ) (c r : ℝ) (j : ℕ) (X : SuTwo)
    (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) (hbar : c / (1 - r) < 2) (hX : X ≠ 0)
    (hδ : ∀ l < j, 2 * RMapLipschitz.frobNorm ((T l : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      ≤ c * r ^ (j - 1 - l)) :
    ‖RMap (gammaVarOf T j) X - X‖ ≤ (c / (1 - r)) * ‖X‖ ∧ (c / (1 - r)) * ‖X‖ < 2 * ‖X‖ := by
  refine ⟨norm_RMap_gammaVarOf_sub_self_le_geometric T c r j X hc hr0 hr1 hδ, ?_⟩
  exact mul_lt_mul_of_pos_right hbar (norm_pos_iff.mpr hX)

/-- **MUST-FIRE CONTROL for §4b.** Drop the condition `c/(1−r) < 2` and the comparison FAILS: at
`c = 4, r = 0` the §4 bound is `4‖X‖`, strictly WEAKER than the trivial `2‖X‖`. So `hbar` is not
decoration. -/
theorem geometric_does_not_always_beat_trivial (X : SuTwo) (hX : X ≠ 0) :
    ¬ ((4 : ℝ) / (1 - 0) * ‖X‖ < 2 * ‖X‖) := by
  have hpos : (0 : ℝ) < ‖X‖ := norm_pos_iff.mpr hX
  intro h
  norm_num at h
  linarith

/-! ## §5 — THE DENOTATION BRIDGE

`TowerLawCov.lhsTransport` — the transport `TowerLawCov.lhs_expand` already puts under the sum,
axiom-clean — IS this module's object at `j = 2`, with the level-`1` factor the unit-scale holonomy
of `V` (Bałaban's `Ū`) and the level-`0` factor the fine holonomy of `U`. So `lhs_expand` IS
CMP99b (3.19) at `j = 2`; §2 extends it to all `j`. -/

/-- **The bridge.** -/
theorem lhsTransport_eq_gammaVarOf (ell₀ : ℕ)
    (V U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y u x : PeriodicLatticeSite L) (μ : Fin 3) (i j : ℕ) :
    lhsTransport ell₀ V U y u x μ i j
      = gammaVarOf
          (fun l => if l = 0 then
              periodicPathHolonomy U (pathSite u μ (i * ell₀))
                (transportPath (pathSite u μ (i * ell₀)) (pathSite x μ (i * ell₀)) μ j)
            else coarsePathHolonomy ell₀ V y (coarseTransportPath ell₀ y u μ i)) 2 := by
  simp [gammaVarOf, lhsTransport]

/-! ## §6 — CONTROLS -/

/-- **MUST-NOT-FIRE.** At the trivial tower every factor is `1`, so the composite kernel is `1` at
every `j`: §1's object is not manufacturing curvature out of the block combinatorics. -/
theorem gammaVar_trivialTower (ell : ℕ) (anc : ℕ → PeriodicLatticeSite L) (j : ℕ) :
    gammaVar ell (fun _ => trivialU L) anc j = 1 := by
  induction j with
  | zero => rfl
  | succ l ih =>
    rw [gammaVar, gammaVarOf_succ, ← gammaVar] at *
    rw [ih, mul_one, stepVar, coarsePathHolonomy_trivialU]

/-- The two step families used by the dependence witness: identical at level `0`, different at
level `1`. -/
def depT : ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  fun l => if l = 1 then witnessMElem else 1

def depT' : ℕ → Matrix.specialUnitaryGroup (Fin 2) ℂ := fun _ => 1

theorem depT_level_zero : depT 0 = depT' 0 := by simp [depT, depT']

theorem suTwoWitness_ne_zero : (suTwoWitness : SuTwo) ≠ 0 := by
  intro h
  have h' : (suTwoWitnessVal : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
    congrFun (congrFun (congrArg Subtype.val h) 0) 0
  simp [suTwoWitnessVal] at h'

/-- **`U(Γ^{(j)})` IS NOT DETERMINED BY THE LEVEL-`0` FIELD.** Two step families that agree at
level `0` give different composite kernels at `j = 2`. So the CMP98 p.29 product is genuinely a
functional of the whole tower `Ū⁰,…,Ū^{j−1}` — it is not a parallel transport of the fine field
along any path, and the notation `Γ^{(j)}` names no contour. This is the theorem behind consequence
(2) in the header, and it is why `TowerLawCov.rhsTransport`'s fine holonomy is a different object
from the source's `U(Γ^{(j)}_{y,x})`. -/
theorem gammaVarOf_not_determined_by_level_zero :
    depT 0 = depT' 0 ∧ gammaVarOf depT 2 ≠ gammaVarOf depT' 2 := by
  refine ⟨depT_level_zero, ?_⟩
  have hT : gammaVarOf depT 2 = witnessMElem := by simp [gammaVarOf, depT]
  have hT' : gammaVarOf depT' 2 = 1 := by simp [gammaVarOf, depT']
  rw [hT, hT']
  intro h
  have hX : RMap witnessMElem (suTwoWitness : SuTwo) = RMap 1 (suTwoWitness : SuTwo) := by rw [h]
  rw [RMap_witnessMElem, RMap_one] at hX
  simp only [LinearMap.id_coe, id_eq] at hX
  have : (2 : ℝ) • (suTwoWitness : SuTwo) = 0 := by
    rw [two_smul]
    have := hX
    linear_combination (norm := module) -this
  rcases smul_eq_zero.mp this with h2 | h0
  · norm_num at h2
  · exact suTwoWitness_ne_zero h0

/-! ### §6b — THE DEPENDENCE WITNESS AT THE CONCRETE FIELD LEVEL

`gammaVarOf_not_determined_by_level_zero` above lives at the abstract step-family level. A nested
validator flagged that it is not instantiated against concrete `Ubar`/`anc` through `stepVar`. It is
now, on the tree's own `witL7` torus at `ell = 2` — NOT at the degenerate `ell ∈ {0,1}` this
campaign's `ell`-binder audit warns about. -/

/-- Level-`2` base on `witL7` (`8` sites per direction). -/
def wy : PeriodicLatticeSite witL7 := fun _ => 4

/-- Its level-`1` child: ONE COARSE step (`ell = 2`) in direction `2`. -/
def wu : PeriodicLatticeSite witL7 := fun ρ => if ρ = 2 then 6 else 4

/-- The ancestry chain `x₂ = wy`, `x₁ = x₀ = wu`, in CMP99b p.401's sense. -/
def wanc : ℕ → PeriodicLatticeSite witL7 := fun l => if 2 ≤ l then wy else wu

/-- The level-`1` contour on this datum is the single coarse step `[2]`. -/
theorem coarseGammaPath_wy_wu : coarseGammaPath 2 wy wu = [(2 : Fin 3)] := by decide

/-- Tower A: trivial at level `0`, the curved constant `M` at level `1`. -/
noncomputable def towerA :
    ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL7 :=
  fun l => if l = 1 then (fun _ => witnessMElem) else trivialU witL7

/-- Tower B: trivial at every level. Same level-`0` field as tower A. -/
noncomputable def towerB :
    ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witL7 :=
  fun _ => trivialU witL7

theorem towerA_level_zero : towerA 0 = towerB 0 := by
  simp [towerA, towerB]

theorem wanc_two : wanc 2 = wy := by norm_num [wanc]

theorem wanc_one : wanc 1 = wu := by norm_num [wanc]

theorem towerA_one : towerA 1 = (fun _ => witnessMElem) := by simp [towerA]

theorem gammaVar_towerA : gammaVar 2 towerA wanc 2 = witnessMElem := by
  have h0 : stepVar 2 towerA wanc 0 = 1 := by
    rw [stepVar, show towerA 0 = trivialU witL7 by simp [towerA], coarsePathHolonomy_trivialU]
  have h1 : stepVar 2 towerA wanc 1 = witnessMElem := by
    rw [stepVar, towerA_one, pow_one, wanc_two, wanc_one, coarseGammaPath_wy_wu]
    simp [coarsePathHolonomy]
  rw [gammaVar, gammaVarOf_succ, gammaVarOf_succ, gammaVarOf_zero, h0, h1, mul_one, mul_one]

theorem gammaVar_towerB : gammaVar 2 towerB wanc 2 = 1 :=
  gammaVar_trivialTower 2 wanc 2

/-- **THE CONCRETE-FIELD DEPENDENCE WITNESS.** Two towers of ACTUAL link configurations on `witL7`
with the SAME level-`0` field give different `U(Γ^{(2)}_{y,x})` at `ell = 2`. So the CMP98 p.29
product is genuinely a functional of the whole blocked tower, at the field level and not merely at
the abstract step-family level. -/
theorem gammaVar_not_determined_by_level_zero_field :
    towerA 0 = towerB 0 ∧ gammaVar 2 towerA wanc 2 ≠ gammaVar 2 towerB wanc 2 := by
  refine ⟨towerA_level_zero, ?_⟩
  rw [gammaVar_towerA, gammaVar_towerB]
  exact witnessMElem_ne_one

/-- **S82 GARBAGE SUBSTITUTION on §3.** Feed the accumulation law a defect profile that is NOT a
bound for the actual steps (`δ ≡ 0` against a step that moves `suTwoWitness` to its negative) and
the conclusion becomes FALSE. So `norm_RMap_gammaVarOf_sub_self_le` is not algebraically forced:
its hypothesis carries the weight. -/
theorem accumulation_is_not_forced :
    ¬ (‖RMap (gammaVarOf depT 2) (suTwoWitness : SuTwo) - suTwoWitness‖
        ≤ (∑ _l ∈ Finset.range 2, (0 : ℝ)) * ‖(suTwoWitness : SuTwo)‖) := by
  have hT : gammaVarOf depT 2 = witnessMElem := by simp [gammaVarOf, depT]
  rw [hT, RMap_witnessMElem]
  intro hle
  have hle0 : ‖(-suTwoWitness - (suTwoWitness : SuTwo))‖ ≤ 0 := by simpa using hle
  have hzero : (-suTwoWitness - (suTwoWitness : SuTwo)) = 0 :=
    norm_eq_zero.mp (le_antisymm hle0 (norm_nonneg _))
  have : (2 : ℝ) • (suTwoWitness : SuTwo) = 0 := by
    rw [two_smul]
    linear_combination (norm := module) -hzero
  rcases smul_eq_zero.mp this with h2 | h0
  · norm_num at h2
  · exact suTwoWitness_ne_zero h0

/-- **MUST-NOT-FIRE for §3**: at the trivial tower, `δ ≡ 0` IS a valid profile and the bound holds
with both sides `0`. So the mutation above fires on curvature, not on the shape of the statement. -/
theorem accumulation_at_trivialTower (ell : ℕ) (anc : ℕ → PeriodicLatticeSite L) (j : ℕ)
    (X : SuTwo) :
    ‖RMap (gammaVar ell (fun _ => trivialU L) anc j) X - X‖
      ≤ (∑ _l ∈ Finset.range j, (0 : ℝ)) * ‖X‖ := by
  rw [gammaVar_trivialTower, RMap_one]
  simp

#print axioms gammaVarOf_eq_prod
#print axioms RMap_gammaVarOf_foldl
#print axioms norm_RMap_gammaVarOf_sub_self_le
#print axioms geom_sum_le_inv
#print axioms geometricAccumulation_le
#print axioms norm_RMap_gammaVarOf_sub_self_le_geometric
#print axioms norm_RMap_sub_self_le_two_local
#print axioms geometric_beats_trivial
#print axioms geometric_does_not_always_beat_trivial
#print axioms lhsTransport_eq_gammaVarOf
#print axioms gammaVar_trivialTower
#print axioms gammaVarOf_not_determined_by_level_zero
#print axioms coarseGammaPath_wy_wu
#print axioms gammaVar_towerA
#print axioms gammaVar_towerB
#print axioms gammaVar_not_determined_by_level_zero_field
#print axioms accumulation_is_not_forced
#print axioms accumulation_at_trivialTower

end AdalyFormal.Balaban.Cmp98Gamma
