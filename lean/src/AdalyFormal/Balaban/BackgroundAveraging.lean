/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.QOne
import AdalyFormal.Balaban.DeltaPrime
import AdalyFormal.Balaban.BondSU2Space

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `Q₁(U)` — CMP99b's BACKGROUND-FIELD averaging operator, `Q₁(U) = Q'₁ + F_{2,1}(U)`

## ⚖ CANONICAL RULING ON `Q` vs `Q₁` — READ THIS BEFORE THE SECTION BELOW (2026-07-26)

**Adjudication document: `compute/q1_adjudication/RULING.md`** (verbatim quotes + 600-dpi renders,
every load-bearing page image-verified). **Counterpart header: `Balaban/CovarianceG1.lean` §0c**,
which banked the OPPOSITE ruling ("`Q₁` is a genuinely distinct … seventh ingredient"). The tree
carried both, unreconciled, and the `C*Δ_kC` line was built on this one. Both are PARTIALLY RIGHT.

**VERDICT: SAME MAP, DIFFERENT LEVELS.**

| symbol in (3.155)-(3.159) | domain | codomain |
|---|---|---|
| `Q` (in `δ(QA−B)`, `(QG₁Q*)⁻¹`) | **fine** lattice `T_η` (variable `A`) | unit lattice `Λ ⊂ Λ_k = Ω_k^{(k)}` |
| `Q₁` (in `δ(Q₁B)`, `Q₁B=0`) | **unit** lattice `Λ` (variable `B`) | `Λ'`, one level ABOVE the unit lattice |

Source pins (all image-verified at 600 dpi by the adjudication, page numbers read off the images):
* CMP99b p.428 **(3.159)** puts `δ(Q₁B)` and `δ(QA−B)` in ONE display, with `A` carrying the fine
  operator `Δ = Δ^η(U)` and `B` integrated as `dB↾_Λ` — **different domains, same display**.
* CMP99b p.427 §E: *"We need operators with Dirichlet boundary conditions outside some domain `Λ`
  **of the unit lattice** … `Λ` is a union of big blocks"* — so `B` is a unit-lattice field and `Λ'`
  is one level up.
* **CMP96 (=[4]) p.245 (2.125) is `Q₁`'s DEFINING formula**, exactly where CMP99b p.428 points
  (*"in the same way as in [4] (2.154-2.155)"*): `(Q₁B)(c) = Σ_{x∈B(c₋)} L^{−(d+1)} B([x,x+Le_μ])`,
  a **unit-lattice bond field averaged onto coarse bonds**.
* CMP96 p.241 (2.103): `Q'_{j+1} = Q'₁ ∘ Q'_j`, with `Q'₁` applied to `μ` *"defined on the unit
  lattice"* — the composition law that makes both readings simultaneously true.
* CMP99b p.428 itself writes the SAME constraint's component form as **`(QB)(c) = 0`** — bare `Q`,
  two lines under `Q₁B = 0`, while the display above uses bare `Q` for the fine→unit arrow. **On one
  page the bare symbol denotes two different arrows.** That is the trap, in the author's own hand.

**WHAT THIS FILE'S OBJECTS ARE.** `qPrimeSuTwo` / `Q1LM` are `(1/(ell:ℝ)^4) • ∑ x ∈ blockOf b.1.1
ell, longBondValueSuTwo A x b.2 ell` — the **level-GENERIC** bond-sector averaging template with the
block side `ell` FREE, the same template as `QOne.qOnePathSum` and
`LineIntegralCovariant.lineCoarseRestrictCov`. **`ell` IS Bałaban's level index**, and the source
requires exactly this: (3.19) rescales the **block** to `B^j(y)` and the gauge-sector **weight** to
`L^{−jd}`, so the bond-sector weight `(L^j)^{−(d+1)} = 1/ell⁴` at `d = 3` is correct at EVERY level.
So `Q1LM` is `Q_j` at whichever `ell` it is instantiated — it is **not `Q₁` intrinsically**, and the
file's name is a level-specific reading of a level-generic object.

**[STRUCK 2026-07-29 — the sentence above ORIGINALLY read "(3.19) gives the `j`-step operator as the
one-step formula with `L → L^j`". That is FALSE, and the false half is the TRANSPORT.]** The block
and the weight rescale; the transport does **not**. Bałaban's `U₀(Γ^{(j)}_{x_j,x})` is an ordered
product with **one factor per RG level** — the level-`l` factor a holonomy of the `l`-times-blocked
field `Ū₀^l` on **its own** lattice (spacing `L^l η`), coarsest leftmost — not a single fine-field
holonomy along a rescaled path. Primary source, CMP98 p.29, an **unnumbered display between (76) and
(77)**, verbatim: `U₀(Γ^{(j)}_{x_j,x}) = Ū₀^{j-1}(Γ_{x_j,x_{j-1}})·…·Ū₀(Γ_{x_2,x_1}) U₀(Γ_{x_1,x})`;
CMP99b p.401 (3.55) pins the chain by `x_l ∈ B(x_{l+1})`. The `1/ell⁴` conclusion is **unaffected**
and no theorem in this file is invalidated — the billing was wrong for `j ≥ 2` at curved `U`.
Formalized at arbitrary `j` in `Balaban/Cmp98GammaPrimary.lean` (`gammaVarOf`, `gammaVarOf_eq_prod`),
which also proves `lhsTransport_eq_gammaVarOf`: this tree's existing `lhs_expand` IS (3.19) at
`j = 2`. Consequence for the residual `[Q1-BACKGROUND-ARG]` below: its "*NOT verbatim*: `Q(Ū^k)`"
caveat is **upgraded to verbatim** for the general composite, by (3.19) line 3 and by CMP98 p.29
independently.

**Therefore the `[CSTAR-LEVEL-MISMATCH]` defect was NOT a missing object** — it was instantiating
this one family at **ONE value of `ell` for BOTH roles** (`Q`'s Schur fibre and `Q₁∘Q`'s constraint),
which forces the constraint image into the fibre's kernel and collapses the form to zero. The repair
is two values, `ell₀ ∣ ell₁` with `ell₁/ell₀ ≥ 2`; see `Balaban/CStarLevelCorrected.lean`, which
reached this verdict independently and carries the `refines : fibre ∣ constr` field.
(An earlier draft of this note asserted "no Lean object for `Q` exists"; that was **wrong** and is
struck — see `compute/q1_adjudication/RULING.md` §5-SUPERSEDED/§5a.)

**Residual left open (earned, not elected): `[Q1-BACKGROUND-ARG]`** — which configuration `V` enters
`Q₁`'s `R(V(Γ))`. Inference from (3.15)'s pattern (NOT verbatim): `Q(Ū^k)`. See RULING.md §3.

## ⚠ THE TRAP THIS FILE IS BUILT TO AVOID (`compute/kimi_omega_gate/VERDICT.md`, image-verified)

**⚠ S75 — PARTIALLY SUPERSEDED 2026-07-26 by `compute/q1_adjudication/RULING.md` §4. Retained
struck, not deleted. RIGHT:** `Q₁` is a ONE-STEP averaging, a single application of the `Q(V)`
template — confirmed by CMP96 (2.125) and (2.103). **WRONG (1):** ~~"NOT CMP95's abelian block
average"~~ — it is *exactly* that object; CMP96 (2.125) defines `Q₁B` as the abelian block average
of a unit-lattice bond field, and the nonabelian version only adds (3.18)/(3.19)'s `R(V(Γ))`
conjugation. **WRONG (2), the one that cost the theorem:** ~~`Q₁(U) = Q(U)` read as an identity of
ARROWS~~ — it is an identity of **map templates only**. `Q_1(U) = Q(U)` of (3.15) has the **fine**
lattice as domain; (3.156)'s `Q₁` has the **unit** lattice as domain. Reading it as an arrow
identity is what licensed one Lean map for both roles.

~~CMP99b's `Q₁` in the `(3.156)` restriction is **NOT** CMP95's abelian block average.~~ It is the
one-step member (`j=1`) of the `U`-dependent family `Q_j(U)`, CMP99b p.393 (3.15):
`Q_j(U) = Q(Ū^{j-1})⋯Q(Ū)Q(U)`, ~~so `Q₁(U) = Q(U)`~~ — a SINGLE application of CMP98's `Q(V₀)`
(formula (124), imported by CMP99b's own citation) **applied at the UNIT-lattice level, not the
fine level**. CMP99b p.433 (3.193)-(3.194) states CMP99b's
own decomposition:

```
Q_j(U)A = Q'_j A + F_{2,j}(U)A,   F_{2,j}(U) "small".
```

`Q'₁` here is the SAME abelian block average `QOne.lean` already built (`qOnePathSum`/
`qOnePathSumCLM`, CMP96 p.245, `η^{d+1}`-weighted, no conjugation) — **imported unchanged
(LAW-19), never re-derived**. `F_{2,1}(U)` is the genuinely new content this file adds.

## THE SOURCE OF `F_{2,1}(U)`, VERBATIM (`corpus/pages/CMP98_p36.md`, `verification_status:
adjudicated`, formulas (124)-(125), reproduced exactly, not paraphrased)

```
(Q(V₀)A)_c = Σ_{x∈B(c₋)} L^{-(d+1)}(R_{0,c₋}A)([x,x'])                          ← MAIN TERM (125)
           + Σ_{x∈B(c₋)} L^{-(d+1)}·[g(-i·ad_Y)g⁻¹(-i·ad_{Y_x}) - 1](R_{0,c₋}A)(Γ_{c₋,x})
           + Σ_{x∈B(c₋)} L^{-(d+1)}[g(-i·ad_Y)g⁻¹(-i·ad_{Y_x}) - 1]·(R_{0,c₋}A)([x,x'])
           - Σ_{x∈B(c₋)} L^{-(d+1)}·[g(-i·ad_Y)g⁻¹(i·ad_{Y_x})e^{-i·ad_Y} - 1]R̄_{0,c}(R_{0,c₊}A)(Γ_{c₊,x'})
           + [e^{i·ad_Y} - g(-i·ad_Y)Σ_{x∈B(c₋)}L^{-d}g⁻¹(i·ad_{Y_x})]L^{-1}(R_{0,c₋}A)(c)
```

Balaban's own text (same page): *"The first term ... is the main term in this linear form, and
it resembles the definition of the averaging operation `Q` in [2]. The remaining terms are small
because the functions `g(-z), g⁻¹(z), e^{iz}` are equal to `1` for `z=0` ... We will denote the
main term by `Q_{V₀}`, or `Q₀`."*

**Reading committed to, and CONFIRMED against `QOne.lean`'s own object**: at `V₀ = 1` (trivial
background), `R_{0,c₋} = id` (parallel transport along ANY path in a flat/trivial connection is
the identity, proved generally below, `periodicPathHolonomy_trivialU_eq_one`), and `Y = Y_x = 0`
(the linearized background-deviation fields, defined relative to `V₀`, vanish when `V₀=1`) — so
`Q(V₀=1)A` reduces to the bare `Σ_{x∈B(c₋)}L^{-(d+1)}A([x,x'])`, **exactly `QOne.qOnePathSum`**.
This is the correctness anchor CMP99b's own (3.194) needs: `Q'_1 = Q₀` at `V₀=1`, i.e.
`Q'₁ := QOne.qOnePathSum` (already built, LAW-19) IS the `V₀=1` specialization of CMP98's own
main term `Q₀`.

## WHAT THIS FILE BUILDS (the honest, partial `F_{2,1}(U)`) — and WHAT IT NAMES, NOT BUILDS

Formula (124) has **five** terms. This file builds:

1. `qPrimeSuTwo`/`qPrimeSuTwoLM` — the `SuTwo`-valued generalization of `QOne.qOnePathSum`
   (the SAME defining sum, `(★)` of `QOne.lean`, module-valued instead of `ℝ`-valued — reusing
   `QOne.pathSite`/`pathSite_zero`/`pathSite_succ` directly, LAW-19). This is `Q'_1` for
   `𝔰𝔲(2)`-valued fields (`Q'₁`'s `ℝ`-valued incarnation, `QOne.qOnePathSum`, is untouched).
2. `R0` — a CONCRETE conjugation `R_{0,c₋}`, built as `RMap` (CMP99b's own adjoint-action
   conjugation, `CovariantOperators.RMap`, LAW-19) of a group-valued holonomy along an EXPLICIT
   reference path (`refOrigin`/`refSteps`, using `ClayStatement.periodicPathHolonomy`, LAW-19).
   **Named limitation, stated not hidden**: CMP98's own precise definition of the reference point
   "`0`" and the specific transport path realizing `R_{0,c}` is NOT independently re-derived here
   (it sits earlier in CMP98, outside this dispatch's render budget) — `refOrigin`/`refSteps` is
   ONE CONCRETE, REASONABLE CHOICE (a single-step coordinate path ending at `witnessY`, the
   `QOne.targetCoarseBond` base), chosen so the two STRUCTURAL FACTS that matter are provably
   correct regardless of the exact path CMP98 uses: (a) at `V₀=1`, EVERY choice of path gives
   `R_{0,c₋}=id` (proved generally, not path-specific); (b) at a genuinely non-flat background,
   the SPECIFIC path chosen here picks up a genuinely non-trivial group element (computed
   concretely, not merely argued). The FULL family `R_{0,c}` varying faithfully with EVERY coarse
   bond `c` (not just `targetCoarseBond`) is not built — `Q1LM` below uses the SAME `R0(U)` for
   every coarse bond, a simplification named in `Q1LM`'s own docstring.
3. `q1MainTerm`/`Q1LM` — `Q₀(U) := R0(U) ∘ Q'₁` (linearity lets the SINGLE, `x`-independent
   conjugation `R_{0,c₋}` be pulled outside formula (125)'s block sum, an EXACT identity, not an
   approximation, since `R0(U)` does not vary with `x` inside `B(c₋)`).
4. **NOT BUILT, named exactly**: formula (124)'s four remaining "ad_Y correction" terms. Each
   requires the linearized background-deviation fields `Y`, `Y_x` (CMP98's own notation for the
   first-order departure of the background connection from `V₀` at the reference point vs. at
   `x`) and the operators `g(-i·ad_Y)`, `g⁻¹(z)`, `e^{iz}` acting on `𝔰𝔲(2)` via the adjoint
   representation — NONE of `Y`, `Y_x`, or `g` is defined anywhere in this tree (checked:
   `grep -rn "ad_Y\|\bY_x\b" formal/AdalyFormal/AdalyFormal` finds no prior construction). Building
   them needs CMP98's own earlier sections (where `V₀`, `Y`, `g` are first introduced,
   `compute/kimi_omega_gate/VERDICT.md`'s own "not verified" list already flags CMP98 pp.~44-46 as
   unread). Per Balaban's own estimate (123)/(126), these four terms are `O(L²α₀)` — small when
   the background curvature `α₀` is small, and IDENTICALLY ZERO at `V₀=1` (since
   `g(-z),g⁻¹(z),e^{iz}` are literally `1` at `z=0`) — so the reduction-at-`U=1` anchor
   (`Q1LM_trivialU` below) is honestly claimed for the FULL `Q₁(U)`, not merely the `q1MainTerm`
   partial, even though only the partial is what this file's `Q1LM` computes away from `U=1`.

**Consequently**: `Q1LM` below is `Q₀(U) = R0(U) ∘ Q'₁`, CMP98's own "main term" of `Q₁(U)` — the
LARGEST, source-named piece, not the full `Q₁(U)`. This is the honest partial the dispatch's
"name exactly what it requires" clause asks for.

## THE DECISIVE MINI-CHECK — `Q1LM · deltaWitnessConfig`, both at `U=1` and at a genuinely
non-flat `U`

`DeltaPrime.deltaWitnessConfig` (the single-bond spike at `(witnessY,0)`) is fed through `Q1LM` at
`QOne.targetCoarseBond` (base `witnessY`, direction `0`), the ONE coarse bond `R0` is faithfully
built for. **HEADLINE RESULT**: `Q1LM · deltaWitnessConfig ≠ 0` at BOTH `U = AdalyFormal.Balaban.CovariantHjMinimizer.trivialU` (value
`(1/16)•suTwoWitness`) AND `U = witnessU` (a background differing from trivial at EXACTLY the
`(witnessY,0)` link, value `-(1/16)•suTwoWitness` — sign FLIPS, confirming genuine `U`-dependence,
not a degenerate/tautological non-vacuity). **This means the `Q₁(U)B=0` clause of `(3.156)`
excludes `deltaWitnessConfig`'s image at BOTH tested backgrounds** — even the bare abelian `Q'₁`
already excludes it (the `F_{2,1}` correction is not NEEDED for this particular exclusion, though
it genuinely changes the value, confirming it is not vacuous either).

## Honesty notes carried over from `SpikeExclusion.lean` (not re-litigated, cited not repeated)

The other two clauses of `(3.156)`'s subspace — `Λ` (free data, relative to an unbuilt `{Ω_j}`
sequence) and `Ax(y)` (never independently spelled out in the rendered page range) — remain
UNBUILT, per `SpikeExclusion.lean`'s own already-banked finding (LAW-19, not re-derived here).
This file's result is about the `Q₁` clause ALONE — a real, useful, non-vacuous data point, not a
full resolution of `(3.156)`'s subspace membership question.
-/

namespace AdalyFormal.Balaban.BackgroundAveraging

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantOperators AdalyFormal.Balaban.DeltaPrime
  AdalyFormal.Balaban.BondSU2Space
open AdalyFormal.Balaban.QOne (targetCoarseBond)

/-! ## §1 — `qPrimeSuTwo`: the `SuTwo`-valued generalization of `QOne.qOnePathSum`, reusing
`QOne.pathSite` (LAW-19; that function is not `ℝ`-specific, it is pure lattice-site combinatorics)
-/

/-- **`B([x,x+ell·e_μ]) := Σ_{i=0}^{ell-1} B_μ(x+i·e_μ)`**, `SuTwo`-valued — literally
`QOne.longBondValue`'s formula `(★)`, generalized from `Bond L → ℝ` to `Bond L → SuTwo`. -/
noncomputable def longBondValueSuTwo {L : PeriodicLatticeExtent} (A : Bond L → SuTwo)
    (x : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ) : SuTwo :=
  ∑ i ∈ Finset.range ell, A (QOne.pathSite x μ i, μ)

theorem longBondValueSuTwo_add {L : PeriodicLatticeExtent} (A1 A2 : Bond L → SuTwo)
    (x : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ) :
    longBondValueSuTwo (A1 + A2) x μ ell =
      longBondValueSuTwo A1 x μ ell + longBondValueSuTwo A2 x μ ell := by
  simp only [longBondValueSuTwo, Pi.add_apply]
  rw [Finset.sum_add_distrib]

theorem longBondValueSuTwo_smul {L : PeriodicLatticeExtent} (c : ℝ) (A : Bond L → SuTwo)
    (x : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ) :
    longBondValueSuTwo (c • A) x μ ell = c • longBondValueSuTwo A x μ ell := by
  simp only [longBondValueSuTwo, Pi.smul_apply]
  rw [Finset.smul_sum]

/-- `(★)` unfolded at `ell=2` — the exact case `Q₁` uses at the witness lattice, mirroring
`QOne.longBondValue_ell2` term-for-term via `QOne.pathSite_zero`/`pathSite_succ` (reused). -/
theorem longBondValueSuTwo_ell2 {L : PeriodicLatticeExtent} (A : Bond L → SuTwo)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    longBondValueSuTwo A x μ 2 = A (x, μ) + A (periodicLatticeShift x μ, μ) := by
  simp [longBondValueSuTwo, Finset.sum_range_succ, QOne.pathSite_zero, QOne.pathSite_succ]

/-- **`Q'₁`, `SuTwo`-valued**: `QOne.qOnePathSum`'s exact defining sum
(block-average with weight `1/ell⁴`), module-valued. This is CMP99b (3.194)'s `Q'_1` at `j=1`. -/
noncomputable def qPrimeSuTwo {L : PeriodicLatticeExtent} (ell : ℕ)
    (A : Bond L → SuTwo) (b : LatticeOperators.CoarseBond L ell) : SuTwo :=
  (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf b.1.1 ell, longBondValueSuTwo A x b.2 ell

theorem qPrimeSuTwo_add {L : PeriodicLatticeExtent} (ell : ℕ) (A1 A2 : Bond L → SuTwo)
    (b : LatticeOperators.CoarseBond L ell) :
    qPrimeSuTwo ell (A1 + A2) b = qPrimeSuTwo ell A1 b + qPrimeSuTwo ell A2 b := by
  simp only [qPrimeSuTwo]
  rw [← smul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => longBondValueSuTwo_add A1 A2 x b.2 ell

theorem qPrimeSuTwo_smul {L : PeriodicLatticeExtent} (ell : ℕ) (c : ℝ) (A : Bond L → SuTwo)
    (b : LatticeOperators.CoarseBond L ell) :
    qPrimeSuTwo ell (c • A) b = c • qPrimeSuTwo ell A b := by
  simp only [qPrimeSuTwo]
  have h : ∀ x ∈ blockOf b.1.1 ell, longBondValueSuTwo (c • A) x b.2 ell =
      c • longBondValueSuTwo A x b.2 ell := fun x _ => longBondValueSuTwo_smul c A x b.2 ell
  rw [Finset.sum_congr rfl h, ← Finset.smul_sum]
  exact smul_comm _ _ _

noncomputable def qPrimeSuTwoLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    (Bond L → SuTwo) →ₗ[ℝ] (LatticeOperators.CoarseBond L ell → SuTwo) where
  toFun A := qPrimeSuTwo ell A
  map_add' A1 A2 := funext fun b => qPrimeSuTwo_add ell A1 A2 b
  map_smul' c A := funext fun b => qPrimeSuTwo_smul ell c A b

#print axioms longBondValueSuTwo_add
#print axioms longBondValueSuTwo_smul
#print axioms longBondValueSuTwo_ell2
#print axioms qPrimeSuTwo_add
#print axioms qPrimeSuTwo_smul
#print axioms qPrimeSuTwoLM

/-! ## §2 — `qPrimeSuTwo(deltaWitnessConfig)` at `targetCoarseBond`: nonzero, unconditionally
(no `U`/`R0` needed yet — this is the bare `Q'₁` clause) -/

/-- **`shift₀(witnessY) ≠ witnessY`, and more generally every OTHER member of the block fails to
reach `(witnessY,0)` via either the direct or the shift term** — the concrete combinatorial fact
isolating `x = witnessY` as the UNIQUE contributor, decided over the (small, `64`-site) witness
lattice, exactly the scale `QOne.lean`'s own `card_coarseBond_lt_card_bond` already decides. -/
theorem witnessY_unique_contributor :
    ∀ x ∈ blockOf witnessY witnessEll, x ≠ witnessY →
      x ≠ witnessY ∧ periodicLatticeShift x 0 ≠ witnessY := by decide

theorem witnessY_mem_blockOf_self : witnessY ∈ blockOf witnessY witnessEll := by decide

theorem shift0_witnessY_ne_witnessY : periodicLatticeShift witnessY 0 ≠ witnessY := by decide

/-- **THE BLOCK-SUM COMPUTATION**: `Σ_{x∈B(witnessY)} longBondValueSuTwo(deltaWitnessConfig,x,0,2)
= suTwoWitness`, extracted from the SINGLE nonzero contributor `x=witnessY` via
`Finset.sum_eq_single`. -/
theorem sum_longBondValueSuTwo_deltaWitnessConfig :
    ∑ x ∈ blockOf witnessY witnessEll, longBondValueSuTwo deltaWitnessConfig x 0 witnessEll =
      suTwoWitness := by
  have hEll : witnessEll = 2 := rfl
  rw [Finset.sum_eq_single witnessY]
  · rw [hEll, longBondValueSuTwo_ell2, deltaWitnessConfig_at_e0,
      deltaWitnessConfig_elsewhere
        (show (periodicLatticeShift witnessY 0, (0 : Fin 3)) ≠ (witnessY, (0 : Fin 3)) by
          intro h; exact shift0_witnessY_ne_witnessY (Prod.mk.injEq .. ▸ h).1)]
    simp
  · intro x hx hne
    obtain ⟨-, hshift⟩ := witnessY_unique_contributor x hx hne
    rw [hEll, longBondValueSuTwo_ell2,
      deltaWitnessConfig_elsewhere
        (show (x, (0 : Fin 3)) ≠ (witnessY, (0 : Fin 3)) by
          intro h; exact hne (Prod.mk.injEq .. ▸ h).1),
      deltaWitnessConfig_elsewhere
        (show (periodicLatticeShift x 0, (0 : Fin 3)) ≠ (witnessY, (0 : Fin 3)) by
          intro h; exact hshift (Prod.mk.injEq .. ▸ h).1)]
    simp
  · intro h; exact absurd witnessY_mem_blockOf_self h

/-- **`Q'₁(deltaWitnessConfig)` at `targetCoarseBond`: `(1/16)•suTwoWitness ≠ 0`** — the abelian
clause ALONE already excludes `deltaWitnessConfig` from `ker(Q'₁)`, before any `U`-correction. -/
theorem qPrimeSuTwo_deltaWitnessConfig :
    qPrimeSuTwo witnessEll deltaWitnessConfig targetCoarseBond = (1 / 16 : ℝ) • suTwoWitness := by
  show (1 / (witnessEll : ℝ) ^ 4) •
      ∑ x ∈ blockOf targetCoarseBond.1.1 witnessEll,
        longBondValueSuTwo deltaWitnessConfig x targetCoarseBond.2 witnessEll = _
  have hbase : (targetCoarseBond : LatticeOperators.CoarseBond witnessL witnessEll).1.1 =
      witnessY := rfl
  have hdir : (targetCoarseBond : LatticeOperators.CoarseBond witnessL witnessEll).2 =
      (0 : Fin 3) := rfl
  rw [hbase, hdir, sum_longBondValueSuTwo_deltaWitnessConfig]
  have hEll : witnessEll = 2 := rfl
  rw [hEll]
  norm_num

#print axioms witnessY_unique_contributor
#print axioms witnessY_mem_blockOf_self
#print axioms shift0_witnessY_ne_witnessY
#print axioms sum_longBondValueSuTwo_deltaWitnessConfig
#print axioms qPrimeSuTwo_deltaWitnessConfig

/-! ## §3 — `R0`: the reference-path conjugation `R_{0,c₋}` at `c₋ = witnessY`, built from
`periodicPathHolonomy` (reused, LAW-19) and `RMap` (reused, LAW-19) -/

/-- **The reference path**: origin `shift₀(witnessY)`, one BACKWARD step in direction `0`, landing
exactly at `witnessY` — the base of `targetCoarseBond`. This is a NAMED, CONCRETE choice (not
independently re-derived from CMP98's own "`0`" convention — see the file header). -/
def refOrigin : PeriodicLatticeSite witnessL := periodicLatticeShift witnessY 0

def refSteps : List (Fin 3 × Bool) := [((0 : Fin 3), false)]

theorem refOrigin_step : periodicLatticeStep refOrigin (0, false) = witnessY := by decide

theorem refSteps_endpoint : periodicPathEndpoint refOrigin refSteps = witnessY := by
  show periodicPathEndpoint (periodicLatticeStep refOrigin (0, false)) [] = witnessY
  rw [refOrigin_step]
  rfl

/-- **The reference-path holonomy reduces to a SINGLE link inverse**: `U(witnessY,0)⁻¹`, general
in `U` — the general fact `R0` is built from, not asserted per-background. -/
theorem periodicPathHolonomy_ref
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    periodicPathHolonomy U refOrigin refSteps = (U (witnessY, (0 : Fin 3)))⁻¹ := by
  show (if (false : Bool) then U (refOrigin, 0) else (U (periodicLatticeStep refOrigin (0, false),
      (0 : Fin 3)))⁻¹) * periodicPathHolonomy U (periodicLatticeStep refOrigin (0, false)) [] = _
  rw [refOrigin_step]
  simp [periodicPathHolonomy]

/-- ⚠ **CORRECTION BANNER — added 2026-07-26 (degenerate-test-point sweep, defect 1). THIS
OBJECT IS BACKGROUND-BLIND, AND ITS NAME OVERCLAIMS.** The docstring below calls it
`R_{0,c₋}(U)`, but the definition takes NO `c₋` (and no `b`, and no `x`): by
`periodicPathHolonomy_ref` it is exactly `RMap (U (witnessY,0)⁻¹)`, one fixed single-link
conjugation reused for every coarse bond (§4's own "named simplification" says as much for the
`b`-dependence; the `c₋`-dependence is the same omission).

**Consequence, now a THEOREM** (`AdalyFormal/Balaban/NonFlatBackground.lean` §8): since
`RMap g` is a linear automorphism, `NonFlatBackground.q1Kernel_eq_ker_qPrimeSuTwoLM` proves
`q1Kernel U = LinearMap.ker (qPrimeSuTwoLM witnessL witnessEll)` **for EVERY `U`**, hence
`NonFlatBackground.q1Kernel_background_blind : q1Kernel U = q1Kernel U'` for any two
backgrounds — `trivialU`, `witnessU`, and the genuinely CURVED `NonFlatBackground.nonflatU t`
(`q1Kernel_nonflatU_eq_trivialU`) all give the SAME subspace. Nothing computed below is false;
what is false is any reading in which the `Q₁`-clause SEES the background.

**Do NOT patch `R0` here** (live lanes). The faithful, genuinely `c₋`/per-block-site transport
already exists in the tree as `Q1Real.rZeroA` / `Q1Real.q1RealMain`; that is the repair path,
**Named open residual, NOT asserted here**: whether `Q1Real.q1RealKernel U` actually DIFFERS from
`q1Kernel U` is UNPROVED — no theorem anywhere in this tree relates the two subspaces (they are
both `Submodule ℝ (Bond witnessL → SuTwo)`, so the comparison is well-posed; it is simply not
made). What is known is only that `Q1Real`'s transport is genuinely `x`-dependent
(`Q1Real.transport_varies_within_single_x`) whereas `R0`'s is not, so the invertible-conjugation
argument that forces `q1Kernel`'s blindness does NOT apply to `q1RealKernel`. The missing
theorem, precisely: exhibit `U` and `A` with `A ∈ q1Kernel U` but `A ∉ q1RealKernel U`. The
loaded candidate is `A := checkerConfigSuTwo` (in `q1Kernel U` for EVERY `U`, immediately from
`NonFlatBackground.q1Kernel_background_blind` plus the banked
`checkerConfigSuTwo_mem_q1Kernel_trivialU`) at a CURVED background such as
`NonFlatBackground.nonflatU t` or `witnessU`: the checkerboard's pairwise cancellation
`A(x,0) + A(x+e₀,0) = 0` is what `q1RealMain` transports with two DIFFERENT holonomies, so it
should survive at `trivialU` (`Q1Real.checkerConfigSuTwo_mem_q1RealKernel_trivialU`, banked) and
break at a curved one. Not attempted in this pass.

**`R_{0,c₋}(U) := RMap(holonomy along the reference path)`** — the conjugation formula (125)
names, built concretely. -/
noncomputable def R0 (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) : SuTwo →ₗ[ℝ] SuTwo :=
  RMap (periodicPathHolonomy U refOrigin refSteps)

/-- **GENERAL FACT (any `L`, `x`, `steps`): the trivial background has trivial holonomy along ANY
path** — every link factor is `1` or `1⁻¹=1` regardless of the path taken, so this does NOT depend
on `refOrigin`/`refSteps`'s specific choice, unlike the concrete computation above. -/
theorem periodicPathHolonomy_trivialU_eq_one {L : PeriodicLatticeExtent}
    (x : PeriodicLatticeSite L) (steps : List (Fin 3 × Bool)) :
    periodicPathHolonomy (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) x steps = 1 := by
  induction steps generalizing x with
  | nil => rfl
  | cons step rest ih =>
    show (if step.2 then (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) (x, step.1)
        else ((AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) (periodicLatticeStep x step, step.1))⁻¹) *
      periodicPathHolonomy (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) (periodicLatticeStep x step) rest = 1
    rw [ih]
    unfold AdalyFormal.Balaban.CovariantHjMinimizer.trivialU
    rcases step.2 with hb | hb <;> simp

/-- **`R0` at the trivial background is the identity** — the reduction anchor. -/
theorem R0_trivialU : R0 (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) = LinearMap.id := by
  unfold R0
  rw [periodicPathHolonomy_trivialU_eq_one]
  exact RMap_one

/-- **`R0` at `witnessU` (non-flat, differing from trivial at EXACTLY `(witnessY,0)`) sends
`suTwoWitness ↦ -suTwoWitness`** — genuinely non-trivial, using the ALREADY-BUILT
`RMap_witnessMElem_inv` (LAW-19, `BondSU2Space.lean`). -/
theorem R0_witnessU_suTwoWitness : R0 witnessU suTwoWitness = -suTwoWitness := by
  unfold R0
  rw [periodicPathHolonomy_ref, witnessU_at_x_mu, RMap_witnessMElem_inv]

#print axioms refOrigin_step
#print axioms refSteps_endpoint
#print axioms periodicPathHolonomy_ref
#print axioms periodicPathHolonomy_trivialU_eq_one
#print axioms R0_trivialU
#print axioms R0_witnessU_suTwoWitness

/-! ## §4 — `Q1LM`: `Q₀(U) = R0(U) ∘ Q'₁`, CMP98 (125)'s main term, as a genuine `LinearMap`.

**Named simplification** (stated, not hidden): the SAME `R0(U)` (built for `c₋ = witnessY` only)
is used for EVERY coarse bond `b` below, for TYPE-level uniformity with `qPrimeSuTwoLM`'s
codomain. This is CMP98-faithful ONLY at `b = targetCoarseBond`; for other `b`, CMP98's own
`R_{0,c₋}` genuinely depends on `c₋` and this file does not build that dependence. All theorems
below are stated (and needed) only at `targetCoarseBond`. -/

noncomputable def Q1LM (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) : (Bond witnessL → SuTwo) →ₗ[ℝ]
    (LatticeOperators.CoarseBond witnessL witnessEll → SuTwo) where
  toFun A b := R0 U (qPrimeSuTwo witnessEll A b)
  map_add' A1 A2 := funext fun b => by
    simp only [qPrimeSuTwo_add]
    exact map_add (R0 U) _ _
  map_smul' c A := funext fun b => by
    simp only [qPrimeSuTwo_smul]
    exact map_smul (R0 U) c _

theorem Q1LM_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (A : Bond witnessL → SuTwo) (b : LatticeOperators.CoarseBond witnessL witnessEll) :
    Q1LM U A b = R0 U (qPrimeSuTwo witnessEll A b) := rfl

/-- **THE REDUCTION ANCHOR**: `Q₁(AdalyFormal.Balaban.CovariantHjMinimizer.trivialU) = Q'₁` — CMP99b (3.194)'s own claim, proved here (not
assumed) for the main-term partial this file builds. -/
theorem Q1LM_trivialU : Q1LM (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) = qPrimeSuTwoLM witnessL witnessEll := by
  apply LinearMap.ext; intro A; funext b
  rw [Q1LM_apply, R0_trivialU]
  rfl

#print axioms Q1LM_apply
#print axioms Q1LM_trivialU

/-! ## §5 — THE DECISIVE MINI-CHECK: `Q1LM · deltaWitnessConfig` at `targetCoarseBond`, both
backgrounds -/

/-- **At `U = AdalyFormal.Balaban.CovariantHjMinimizer.trivialU`**: `Q₁(deltaWitnessConfig) = (1/16)•suTwoWitness ≠ 0`. -/
theorem Q1LM_trivialU_deltaWitnessConfig' :
    Q1LM (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) deltaWitnessConfig targetCoarseBond = (1 / 16 : ℝ) • suTwoWitness := by
  rw [Q1LM_trivialU]
  show qPrimeSuTwoLM witnessL witnessEll deltaWitnessConfig targetCoarseBond = _
  show qPrimeSuTwo witnessEll deltaWitnessConfig targetCoarseBond = _
  exact qPrimeSuTwo_deltaWitnessConfig

/-- **At `U = witnessU`** (genuinely non-flat, differing from trivial at exactly the SPIKE'S OWN
bond `(witnessY,0)`): `Q₁(deltaWitnessConfig) = -(1/16)•suTwoWitness ≠ 0` — the SIGN FLIPS
relative to the trivial background, the concrete, non-degenerate `F_{2,1}`-content the mandate
asked to test. -/
theorem Q1LM_witnessU_deltaWitnessConfig :
    Q1LM witnessU deltaWitnessConfig targetCoarseBond = -((1 / 16 : ℝ) • suTwoWitness) := by
  rw [Q1LM_apply, qPrimeSuTwo_deltaWitnessConfig]
  show R0 witnessU ((1 / 16 : ℝ) • suTwoWitness) = _
  rw [map_smul, R0_witnessU_suTwoWitness, smul_neg]

theorem Q1LM_trivialU_deltaWitnessConfig_ne_zero :
    Q1LM (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) deltaWitnessConfig targetCoarseBond ≠ 0 := by
  rw [Q1LM_trivialU_deltaWitnessConfig']
  exact smul_ne_zero (by norm_num) suTwoWitness_ne_zero

theorem Q1LM_witnessU_deltaWitnessConfig_ne_zero :
    Q1LM witnessU deltaWitnessConfig targetCoarseBond ≠ 0 := by
  rw [Q1LM_witnessU_deltaWitnessConfig]
  intro h
  apply smul_ne_zero (show (1 / 16 : ℝ) ≠ 0 by norm_num) suTwoWitness_ne_zero
  exact neg_eq_zero.mp h

/-- **Genuinely `U`-dependent**: the two values DIFFER (not merely both nonzero) — `F_{2,1}` is
not a vacuous correction at this witness. -/
theorem Q1LM_deltaWitnessConfig_genuinely_U_dependent :
    Q1LM (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) deltaWitnessConfig targetCoarseBond ≠
      Q1LM witnessU deltaWitnessConfig targetCoarseBond := by
  rw [Q1LM_trivialU_deltaWitnessConfig', Q1LM_witnessU_deltaWitnessConfig]
  intro h
  apply suTwoWitness_ne_zero
  have h2 : (1 / 16 : ℝ) • suTwoWitness + (1 / 16 : ℝ) • suTwoWitness = 0 := by
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  rw [← add_smul] at h2
  have h3 : (1 / 16 + 1 / 16 : ℝ) = 1 / 8 := by norm_num
  rw [h3] at h2
  rcases smul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

#print axioms Q1LM_trivialU_deltaWitnessConfig'
#print axioms Q1LM_witnessU_deltaWitnessConfig
#print axioms Q1LM_trivialU_deltaWitnessConfig_ne_zero
#print axioms Q1LM_witnessU_deltaWitnessConfig_ne_zero

/-! ## §6 — the `Q₁(U)B=0` locus, as a genuine `U`-parameterized `Submodule` (the third clause of
`(3.156)`, at `targetCoarseBond`) -/

/-- ⚠ **CORRECTION BANNER (2026-07-26, defect 1): `q1Kernel` IS A CONSTANT FUNCTION OF `U`.**
Proved in `AdalyFormal/Balaban/NonFlatBackground.lean`:
`q1Kernel U = LinearMap.ker (qPrimeSuTwoLM witnessL witnessEll)` for every background
(`NonFlatBackground.q1Kernel_eq_ker_qPrimeSuTwoLM`), because `R0 U` is a single invertible
`RMap` applied uniformly. Any downstream statement quantified as "for ANY `U`" over this
subspace is produced BY that degeneracy, not earned by it — in particular
`TheLemmaFaithful.faithfulSubspace`'s `Q₁` clause has no `U`-dependence. See the `R0` banner
in §3. -/
noncomputable def q1Kernel (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) : Submodule ℝ (Bond witnessL → SuTwo) := LinearMap.ker (Q1LM U)

/-- **`deltaWitnessConfig ∉ q1Kernel(AdalyFormal.Balaban.CovariantHjMinimizer.trivialU)`**: the abelian `Q₁`-clause EXCLUDES the
counterexample. -/
theorem deltaWitnessConfig_notMem_q1Kernel_trivialU :
    deltaWitnessConfig ∉ q1Kernel (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) := by
  intro hmem
  rw [q1Kernel, LinearMap.mem_ker] at hmem
  exact Q1LM_trivialU_deltaWitnessConfig_ne_zero (congrFun hmem targetCoarseBond)

/-- ⚠ **CORRECTION BANNER (2026-07-26, defect 1): THIS IS NOT AN INDEPENDENT CHECK AND CANNOT
FAIL ON ITS OWN.** The claim below of "same conclusion, different reason" does not survive:
`NonFlatBackground.control_witnessU_iff_trivialU` proves that for EVERY field `A`,
`A ∈ q1Kernel witnessU ↔ A ∈ q1Kernel (trivialU witnessL)`. This theorem is therefore
LOGICALLY EQUIVALENT to `deltaWitnessConfig_notMem_q1Kernel_trivialU` — the same check
post-composed with an invertible conjugation. It is a falsifiability control with zero
independent falsifying power; the sign flip in `Q1LM_witnessU_deltaWitnessConfig` changes the
VALUE but can never change its vanishing. See the `R0` banner above.

**`deltaWitnessConfig ∉ q1Kernel(witnessU)`**: the corrected, non-flat `Q₁`-clause ALSO
excludes it (same conclusion, different reason — the `F_{2,1}` correction flips the sign but not
the exclusion, at this witness). -/
theorem deltaWitnessConfig_notMem_q1Kernel_witnessU :
    deltaWitnessConfig ∉ q1Kernel witnessU := by
  intro hmem
  rw [q1Kernel, LinearMap.mem_ker] at hmem
  exact Q1LM_witnessU_deltaWitnessConfig_ne_zero (congrFun hmem targetCoarseBond)

/-- **`q1Kernel` is genuinely a restriction (`≠ ⊤`) at BOTH backgrounds** — not the vacuous "every
kernel test trivially passes" failure mode. -/
theorem q1Kernel_trivialU_ne_top : q1Kernel (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) ≠ ⊤ := fun h =>
  deltaWitnessConfig_notMem_q1Kernel_trivialU (h ▸ Submodule.mem_top)

theorem q1Kernel_witnessU_ne_top : q1Kernel witnessU ≠ ⊤ := fun h =>
  deltaWitnessConfig_notMem_q1Kernel_witnessU (h ▸ Submodule.mem_top)

/-- **`q1Kernel ≠ ⊥`** (satisfiable, non-trivially) at `U = AdalyFormal.Balaban.CovariantHjMinimizer.trivialU`, via `QOne`'s ALREADY-PROVED
`checkerConfig` (LAW-19: the SAME `SuTwo`-independent argument does not transfer directly since
`checkerConfig : Bond L → ℝ`; instead we exhibit `(0 : Bond witnessL → SuTwo)`'s nontrivial
SCALAR-multiple analogue is trivial — genuine non-degeneracy at the `SuTwo` level reuses the exact
`QOne.checkerConfig`-style checkerboard, generalized). -/
noncomputable def checkerConfigSuTwo : Bond witnessL → SuTwo :=
  fun e => if e.2 = (0 : Fin 3) then ((-1 : ℝ) ^ (e.1 0).val) • suTwoWitness else 0

theorem checkerConfigSuTwo_ne_zero : checkerConfigSuTwo ≠ 0 := by
  intro h
  have := congrFun h (witnessY, (0 : Fin 3))
  simp only [checkerConfigSuTwo, witnessY, Pi.zero_apply] at this
  norm_num at this
  exact suTwoWitness_ne_zero this

theorem checkerConfigSuTwo_pointwise_cancel (x : PeriodicLatticeSite witnessL) :
    checkerConfigSuTwo (x, (0 : Fin 3)) +
      checkerConfigSuTwo (periodicLatticeShift x 0, (0 : Fin 3)) = 0 := by
  have hshift : (periodicLatticeShift x 0) 0 = x 0 + 1 := by
    simp [periodicLatticeShift, Function.update_self]
  have h1 : checkerConfigSuTwo (x, (0 : Fin 3)) = ((-1 : ℝ) ^ (x 0).val) • suTwoWitness := by
    simp [checkerConfigSuTwo]
  have h2 : checkerConfigSuTwo (periodicLatticeShift x 0, (0 : Fin 3)) =
      ((-1 : ℝ) ^ ((periodicLatticeShift x 0) 0).val) • suTwoWitness := by
    simp [checkerConfigSuTwo]
  rw [h1, h2, hshift, ← add_smul]
  generalize hv : x 0 = v
  have : ((-1 : ℝ) ^ v.val + (-1 : ℝ) ^ (v + 1).val) = 0 := by
    fin_cases v <;> norm_num [Fin.add_def, witnessL]
  rw [this, zero_smul]

theorem longBondValueSuTwo_checkerConfigSuTwo_eq_zero (x : PeriodicLatticeSite witnessL) :
    longBondValueSuTwo checkerConfigSuTwo x 0 witnessEll = 0 := by
  have hEll : witnessEll = 2 := rfl
  rw [hEll, longBondValueSuTwo_ell2]
  exact checkerConfigSuTwo_pointwise_cancel x

theorem checkerConfigSuTwo_mem_q1Kernel_trivialU :
    checkerConfigSuTwo ∈ q1Kernel (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) := by
  rw [q1Kernel, LinearMap.mem_ker, Q1LM_trivialU]
  funext b
  show qPrimeSuTwo witnessEll checkerConfigSuTwo b = 0
  unfold qPrimeSuTwo
  rcases eq_or_ne b.2 0 with hmu | hmu
  · have hzero : ∀ x ∈ blockOf b.1.1 witnessEll,
        longBondValueSuTwo checkerConfigSuTwo x b.2 witnessEll = 0 := by
      intro x _; rw [hmu]; exact longBondValueSuTwo_checkerConfigSuTwo_eq_zero x
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, smul_zero]
  · have hzero : ∀ x ∈ blockOf b.1.1 witnessEll,
        longBondValueSuTwo checkerConfigSuTwo x b.2 witnessEll = 0 := by
      intro x _
      apply Finset.sum_eq_zero
      intro i _
      simp only [checkerConfigSuTwo]
      rw [if_neg hmu]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, smul_zero]

theorem q1Kernel_trivialU_ne_bot : q1Kernel (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) ≠ ⊥ := by
  intro hbot
  apply checkerConfigSuTwo_ne_zero
  rw [← Submodule.mem_bot ℝ (x := checkerConfigSuTwo), ← hbot]
  exact checkerConfigSuTwo_mem_q1Kernel_trivialU

#print axioms deltaWitnessConfig_notMem_q1Kernel_trivialU
#print axioms deltaWitnessConfig_notMem_q1Kernel_witnessU
#print axioms q1Kernel_trivialU_ne_top
#print axioms q1Kernel_witnessU_ne_top
#print axioms checkerConfigSuTwo_ne_zero
#print axioms checkerConfigSuTwo_pointwise_cancel
#print axioms longBondValueSuTwo_checkerConfigSuTwo_eq_zero
#print axioms checkerConfigSuTwo_mem_q1Kernel_trivialU
#print axioms q1Kernel_trivialU_ne_bot

/-! ## §7 — S82 MUTATION CHECKS: exhibit inputs where the headline claims genuinely FLIP -/

/-- **MUTATION 1** (garbage substitution, S82): the zero configuration is trivially IN the
kernel at every background — contrasts with `deltaWitnessConfig`'s exclusion, confirming the
non-membership results above are not a tautology of `q1Kernel`'s definition. -/
theorem zero_mem_q1Kernel (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) : (0 : Bond witnessL → SuTwo) ∈ q1Kernel U := by
  rw [q1Kernel, LinearMap.mem_ker]; exact map_zero (Q1LM U)

/-- **MUTATION 2**: if `R0` were WRONGLY built as the constant identity (ignoring `U`, the exact
"forgot the conjugation" error class this file's own header warns about), the `witnessU`
computation would give `+(1/16)•suTwoWitness`, not `-(1/16)•suTwoWitness` — i.e. it would COINCIDE
with the `AdalyFormal.Balaban.CovariantHjMinimizer.trivialU` value, making `Q1LM_deltaWitnessConfig_genuinely_U_dependent` FALSE. That
theorem's proof genuinely uses `RMap_witnessMElem_inv` (not `RMap_one`) — swapping the lemma at
that one `rw` site is exactly the mutation that would break it; recorded here as the mutation this
file's construction must NOT reduce to. -/
theorem mutation_note_R0_id_would_collapse :
    R0 (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) suTwoWitness = suTwoWitness ∧
      R0 witnessU suTwoWitness = -suTwoWitness ∧
      R0 (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) suTwoWitness ≠ R0 witnessU suTwoWitness := by
  refine ⟨by rw [R0_trivialU]; rfl, R0_witnessU_suTwoWitness, ?_⟩
  rw [R0_trivialU, R0_witnessU_suTwoWitness]
  intro h
  apply suTwoWitness_ne_zero
  have hshow : suTwoWitness = -suTwoWitness := h
  have h2 : suTwoWitness + suTwoWitness = 0 := by
    nth_rewrite 1 [hshow]
    exact neg_add_cancel _
  rw [← two_smul ℝ] at h2
  rcases smul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

#print axioms zero_mem_q1Kernel
#print axioms mutation_note_R0_id_would_collapse

end AdalyFormal.Balaban.BackgroundAveraging
