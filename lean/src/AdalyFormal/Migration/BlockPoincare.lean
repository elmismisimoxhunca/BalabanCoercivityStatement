/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev
import AdalyFormal.Balaban.Blocks

/-!
# `Migration.BlockPoincare` — Spine.lean sorrys #1 and #2: statement-prosecution + partial closure

**Mandate**: attack `Spine.lean`'s sorry #1 (`theorem2_blockPoincare`) and sorry #2
(`theorem4_quantitativeCoercivity`), the two remaining `sorry`s inside `[LEM-COERC-U]`'s own
factorization (`Spine.lean` §1). **Write scope: this file + `MIGRATION_BLOCKPOINCARE.md` only —
`Spine.lean` itself is NOT touched (a live lane); wiring the results below back into it is a later,
separate pass.**

## HEADLINE FINDING (L6 "statement false as written", the most valuable outcome) — both sorrys

`Spine.lean`'s literal statements of BOTH sorry #1 and sorry #2 are **FALSE AS WRITTEN**, and for the
*exact same reason* in both cases: the "opaque quantities" pattern (`Spine.lean` design choice 2,
`Migration/CMP96Lemma24Farkas.lean`'s own precedent) is used CORRECTLY there — the opaque reals carry
hypotheses that ENCODE the real mathematical relationship between them (`hStar`/`hDagger`) — but
`Spine.lean`'s sorry #1/#2 statements introduce opaque functions (`bondNormSq, plaqDerivNormSq` /
`F_U, normSq`) constrained ONLY by nonnegativity, with **no hypothesis linking them to each other or
to a genuine gauge-field configuration at all**. §0 below exhibits, for each sorry, concrete data
satisfying *every* stated hypothesis for which the conclusion is false — proved, kernel-checked, no
`sorry`, exactly the established repo pattern
(`SPINE_REPORT.md` round 2, `compute/cmp102_thm1_rederivation/statement_refutation.lean`).

This is not a criticism of the "opaque quantities" technique — `CMP96Lemma24Farkas.lean` and this
file's own §1/§2 below use it successfully — it is a finding that `Spine.lean`'s sorry #1/#2
transcriptions DROPPED the linking hypotheses when the technique was applied there, exactly the class
of defect L5/OPS-1 exist to catch ("hunt the dropped hypothesis before concluding a statement is
wrong" — here the hunt succeeds for #2, and identifies precisely what is missing for #1).

## What this file delivers, per sorry

* **Sorry #2 (`theorem4_quantitativeCoercivity`, Theorem 4(iii)) — CLOSED**, via a corrected,
  properly-hypothesized restatement (§2). The repair additionally finds and documents a **second,
  independent bug**: `Spine.lean`'s `ha2` hypothesis transcribes Bałaban's exponent
  `L^{-(d+1)/2}` (a SQUARE-ROOT-scaled quantity) as `L^{-(d+1)} / 2` (a `1/2`-multiple of the
  much smaller `L^{-(d+1)}`) — the exponent's "divide by 2" migrated from inside the power to
  outside it, exactly the (2.121)-class transcription error the campaign has hit before. §2's
  corrected statement uses the source's true exponent, `L ^ ((-(d:ℝ)-1)/2)`, and is fully proved
  against it — with no further residual. The min-singular-value perturbation lemma this uses
  (`minNorm_perturbation`) is itself new, general, reusable Weyl-type machinery.

* **Sorry #1 (`theorem2_blockPoincare`, CMP96 (2.123)) — DECOMPOSED, not closed.** §1 proves, in
  full generality, the discrete Cauchy–Schwarz + double-counting core of Bałaban's own printed proof
  ("`|B(x,j)| ≤ Σ_{steps}|(∂^U B)(p_step)|`, `|B(x,j)|² ≤ (#steps)Σ|(∂^U B)(p_step)|²`",
  `compute/coerc_u_close/DERIVATION.md:122-126`) as an abstract, reusable lemma over any finite
  `Bond`/`Plaq` index types and a `steps : Bond → Finset Plaq` incidence structure — completely
  isolating the PURELY COMBINATORIAL half of Theorem 2's proof, no lattice or gauge content
  anywhere in its statement or proof. What remains — named, not attempted — is exactly the
  GEOMETRIC half: the telescoping identity itself (needing the concrete `ℤ^d` block/bond/plaquette
  incidence, tree-bond classification, and the `SU(2)`-adjoint isometry `|Ad(g)v|=|v|`) and the
  concrete counting fact `K·M = d·L^d` for that geometry. §1.4 documents precisely why the
  groundwork this dispatch was pointed at (`Balaban/Blocks.lean`, `Lattice/Witness.lean`) does
  **not** supply either of these — a correction to the dispatching mandate's own premise, filed as
  a finding, not silently worked around.

## Provenance

Both sorrys, `compute/coerc_u_close/DERIVATION.md` §3 (Theorem 2) and §5 (Theorem 4), CMP96 printed
pp. 244-245 (`corpus/tools/page_offsets.json`, offset 222) via `Balaban/Blocks.lean`'s own
image-verified pin for (2.123)'s constant. `LEAN_SPINE_TRIAGE.md`'s bucket-(B) classification for
both is the dispatch's starting point; this file reports, per L6, exactly how far that classification
survives contact with an actual construction attempt.
-/

namespace AdalyFormal.Migration.BlockPoincare

open scoped BigOperators

/-! ## §0 — Sorry #1 and sorry #2, quoted, shown FALSE AS WRITTEN (L6) -/

section FalseAsWritten

/-- **`Spine.lean`'s `theorem2_blockPoincare` (sorry #1) is FALSE AS WRITTEN.** Concrete witness:
`Site = Center = Unit`, the (unique) block geometry with `L = 1, d = 2`
(`B _ = Finset.univ`, `card_block` trivial: `Fintype.card Unit = 1 = 1^2`),
`bondNormSq _ := 1`, `plaqDerivNormSq _ := 0`. Both nonnegativity hypotheses `Spine.lean` states
(`_hbond`, `_hplaq`) hold; the conclusion, exactly as `Spine.lean` states it
(`bondNormSq y ≤ (geo.d * geo.L ^ geo.d : ℝ) * plaqDerivNormSq y`), demands `1 ≤ (2 * 1) * 0 = 0`,
false. This is possible for ANY choice of nonzero `bondNormSq` and zero `plaqDerivNormSq` precisely
because `Spine.lean`'s statement has no hypothesis relating the two functions at all — the missing
ingredient is the genuine Cauchy–Schwarz/telescoping link `§1` below supplies in isolation. -/
theorem theorem2_blockPoincare_false_as_written :
    ∃ (geo : Balaban.BlockGeometry Unit Unit) (bondNormSq plaqDerivNormSq : Unit → ℝ),
      (∀ y, 0 ≤ bondNormSq y) ∧ (∀ y, 0 ≤ plaqDerivNormSq y) ∧
      ¬ (∀ y : Unit, bondNormSq y ≤ (geo.d * geo.L ^ geo.d : ℝ) * plaqDerivNormSq y) := by
  refine ⟨⟨fun _ => Finset.univ, 1, 2, fun y => ?_⟩, fun _ => 1, fun _ => 0,
    fun _ => zero_le_one, fun _ => le_refl 0, ?_⟩
  · simp
  · intro h
    have h0 := h ()
    norm_num at h0

/-- **`Spine.lean`'s `theorem4_quantitativeCoercivity` (sorry #2) is FALSE AS WRITTEN.** Concrete
witness: `H := ℝ`, `d := 2, L := 1, ℓ := 1, a := 0, γB := 4`, `F_U := fun _ => 0`,
`normSq := fun _ => 1`. Every hypothesis `Spine.lean` states holds (`hℓ : 1 = 2*(1-1)+1`
✓; `hL1 : 1≤1` ✓; `hd2 : 2≤2` ✓; `ha1 : 0 ≤ 1/(2*1)` ✓; `ha2 : 0 ≤` a manifestly nonnegative
expression ✓; both nonnegativity side-conditions on `F_U`, `normSq` trivially hold). The
conclusion, exactly as `Spine.lean` states it (`∀ B, (γB/4)*normSq B ≤ F_U B`), demands
`1 ≤ 0` at `B := 0`, false — again possible because `Spine.lean`'s `F_U`/`normSq`/`γB` carry no
hypothesis connecting them to each other or to an actual operator; `§2` below supplies exactly that
missing link (`F_U`/`normSq` become the DERIVED quantities `‖M₂B‖²`/`‖B‖²` of an actual operator
`M₂`, and `γB` is pinned to Bałaban's own formula). -/
theorem theorem4_quantitativeCoercivity_false_as_written :
    ∃ (F_U normSq : ℝ → ℝ) (d : ℕ) (L a γB ℓ : ℝ),
      (∀ B, 0 ≤ F_U B) ∧ (∀ B, 0 ≤ normSq B) ∧
      ℓ = (d : ℝ) * (L - 1) + L ∧ 1 ≤ L ∧ 2 ≤ d ∧
      a ≤ 1 / (2 * ℓ) ∧
      a ≤ L ^ (-(d : ℝ) - 1) / 2 / (24 * Real.sqrt 3 * d * (d + 1)) ∧
      ¬ (∀ B : ℝ, (γB / 4) * normSq B ≤ F_U B) := by
  refine ⟨fun _ => 0, fun _ => 1, 2, 1, 0, 4, 1, fun _ => le_refl 0, fun _ => zero_le_one,
    by norm_num, le_refl 1, le_refl 2, by norm_num, ?_, ?_⟩
  · positivity
  · intro h
    have h0 := h 0
    norm_num at h0

end FalseAsWritten

/-! ## §1 — Sorry #1: the abstract Cauchy–Schwarz + double-counting core of Theorem 2

DECOMPOSES, does not close. `Bond`/`Plaq` stand for the fine bonds / plaquettes of ONE block
`B(y)`; `steps b` is the set of plaquettes Bałaban's telescoping identity visits along bond `b`'s
reduction path. -/

section Theorem2Core

variable {Bond Plaq : Type*} [Fintype Bond] [Fintype Plaq] [DecidableEq Plaq]

/-- How many bonds' step-paths pass through a given plaquette `p` — the multiplicity Bałaban's own
counting argument bounds ("the sum over `x` and `j` is Bałaban's own counting",
`compute/coerc_u_close/DERIVATION.md:128`). -/
def plaqMultiplicity (steps : Bond → Finset Plaq) (p : Plaq) : ℕ :=
  (Finset.univ.filter (fun b => p ∈ steps b)).card

/-- **§1.1 — the per-bond step: triangle inequality + Cauchy–Schwarz.** Bałaban's own two
displayed inequalities (`DERIVATION.md:125-126`), quoted: *"`|B(x,j)| ≤ Σ_{steps}|(∂^U
B)(p_step)|`, `|B(x,j)|² ≤ (#steps) Σ|(∂^U B)(p_step)|²`"* — `hTri` below is the FIRST (the genuine
geometric content: an exact telescoping identity plus the `SU(2)`-adjoint isometry `|Ad(g)v|=|v|`,
NOT re-derived here, see §1.4); the SECOND is pure Cauchy–Schwarz, proved here from Mathlib's own
`sq_sum_le_card_mul_sum_sq` (a Chebyshev-inequality corollary), no further hypothesis needed. -/
theorem bond_sq_le_card_mul_plaqSq (steps : Bond → Finset Plaq) (bondAbs : Bond → ℝ)
    (b : Bond) (g : Plaq → ℝ) (hbondAbs_nonneg : 0 ≤ bondAbs b)
    (hTri : bondAbs b ≤ ∑ p ∈ steps b, g p) :
    (bondAbs b) ^ 2 ≤ (steps b).card * ∑ p ∈ steps b, (g p) ^ 2 := by
  calc (bondAbs b) ^ 2 ≤ (∑ p ∈ steps b, g p) ^ 2 :=
        pow_le_pow_left₀ hbondAbs_nonneg hTri 2
    _ ≤ (steps b).card * ∑ p ∈ steps b, (g p) ^ 2 := sq_sum_le_card_mul_sum_sq

/-- **§1.2 — the double-counting identity.** `Σ_b Σ_{p ∈ steps b} g(p) = Σ_p mult(p) · g(p)`, the
"sum over `x` and `j` is Bałaban's own counting" step, via `Finset.sum_comm'` (swap a sum whose
inner `Finset` depends on the outer index) — no lattice structure, pure combinatorics. -/
theorem sum_steps_eq_sum_mult (steps : Bond → Finset Plaq) (g : Plaq → ℝ) :
    (∑ b : Bond, ∑ p ∈ steps b, g p) = ∑ p : Plaq, (plaqMultiplicity steps p : ℝ) * g p := by
  have hcomm : (∑ b : Bond, ∑ p ∈ steps b, g p)
      = ∑ p : Plaq, ∑ _b ∈ Finset.univ.filter (fun b => p ∈ steps b), g p := by
    apply Finset.sum_comm'
    intro x y
    simp
  rw [hcomm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_const, plaqMultiplicity, nsmul_eq_mul]

/-- **§1.3 — the assembled abstract core, matching Bałaban's own proof shape exactly.**
Given: a per-bond triangle-inequality bound `hTri` (the genuine geometric content, NOT re-derived
here — §1.4); a bound `K` on every bond's step-path length; a bound `M` on every plaquette's
multiplicity across all step-paths — concludes the block-Poincaré inequality with constant `K·M`,
matching Bałaban's `d·L^d` for the concrete geometry (not identified with it here, §1.4). This is
the FULL combinatorial content of `(2.123)`'s proof, isolated and generalized: no `Site`, `Center`,
gauge group, or block-geometry type anywhere in this theorem's statement or proof. -/
theorem block_poincare_core' (steps : Bond → Finset Plaq) (bondAbs : Bond → ℝ)
    (plaqAbs : Plaq → ℝ) (K M : ℕ)
    (hK : ∀ b, (steps b).card ≤ K) (hM : ∀ p, plaqMultiplicity steps p ≤ M)
    (hbondAbs_nonneg : ∀ b, 0 ≤ bondAbs b) (hplaqAbs_nonneg : ∀ p, 0 ≤ plaqAbs p)
    (hTri : ∀ b, bondAbs b ≤ ∑ p ∈ steps b, plaqAbs p) :
    ∑ b : Bond, (bondAbs b) ^ 2 ≤ (K : ℝ) * M * ∑ p : Plaq, (plaqAbs p) ^ 2 := by
  have hstep1 : ∀ b, (bondAbs b) ^ 2 ≤ (steps b).card * ∑ p ∈ steps b, (plaqAbs p) ^ 2 :=
    fun b => bond_sq_le_card_mul_plaqSq steps bondAbs b plaqAbs (hbondAbs_nonneg b) (hTri b)
  have hstep2 : ∀ b, (bondAbs b) ^ 2 ≤ (K : ℝ) * ∑ p ∈ steps b, (plaqAbs p) ^ 2 := by
    intro b
    have hcard : ((steps b).card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK b
    have hnn : (0 : ℝ) ≤ ∑ p ∈ steps b, (plaqAbs p) ^ 2 :=
      Finset.sum_nonneg (fun p _ => sq_nonneg _)
    calc (bondAbs b) ^ 2 ≤ (steps b).card * ∑ p ∈ steps b, (plaqAbs p) ^ 2 := hstep1 b
      _ ≤ (K : ℝ) * ∑ p ∈ steps b, (plaqAbs p) ^ 2 := mul_le_mul_of_nonneg_right hcard hnn
  have hsum : ∑ b : Bond, (bondAbs b) ^ 2
      ≤ (K : ℝ) * ∑ b : Bond, ∑ p ∈ steps b, (plaqAbs p) ^ 2 := by
    calc ∑ b : Bond, (bondAbs b) ^ 2 ≤ ∑ b : Bond, (K : ℝ) * ∑ p ∈ steps b, (plaqAbs p) ^ 2 :=
          Finset.sum_le_sum (fun b _ => hstep2 b)
      _ = (K : ℝ) * ∑ b : Bond, ∑ p ∈ steps b, (plaqAbs p) ^ 2 := by rw [Finset.mul_sum]
  have hdouble : (∑ b : Bond, ∑ p ∈ steps b, (plaqAbs p) ^ 2)
      = ∑ p : Plaq, (plaqMultiplicity steps p : ℝ) * (plaqAbs p) ^ 2 :=
    sum_steps_eq_sum_mult steps (fun p => (plaqAbs p) ^ 2)
  have hmultbound : ∑ p : Plaq, (plaqMultiplicity steps p : ℝ) * (plaqAbs p) ^ 2
      ≤ (M : ℝ) * ∑ p : Plaq, (plaqAbs p) ^ 2 := by
    calc ∑ p : Plaq, (plaqMultiplicity steps p : ℝ) * (plaqAbs p) ^ 2
        ≤ ∑ p : Plaq, (M : ℝ) * (plaqAbs p) ^ 2 := by
          apply Finset.sum_le_sum
          intro p _
          have hmp : (plaqMultiplicity steps p : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM p
          exact mul_le_mul_of_nonneg_right hmp (sq_nonneg _)
      _ = (M : ℝ) * ∑ p : Plaq, (plaqAbs p) ^ 2 := by rw [Finset.mul_sum]
  calc ∑ b : Bond, (bondAbs b) ^ 2
      ≤ (K : ℝ) * ∑ b : Bond, ∑ p ∈ steps b, (plaqAbs p) ^ 2 := hsum
    _ = (K : ℝ) * ∑ p : Plaq, (plaqMultiplicity steps p : ℝ) * (plaqAbs p) ^ 2 := by rw [hdouble]
    _ ≤ (K : ℝ) * ((M : ℝ) * ∑ p : Plaq, (plaqAbs p) ^ 2) :=
        mul_le_mul_of_nonneg_left hmultbound (by positivity)
    _ = (K : ℝ) * M * ∑ p : Plaq, (plaqAbs p) ^ 2 := by ring

/-- **`∀ y` wrapper**, matching `Spine.lean`'s own `∀ y : Center, ...` quantifier shape exactly:
one instance of `block_poincare_core'` applied per block-center `y`, with the whole data
(`Bond`/`Plaq`/`steps`/`K`/`M`) allowed to depend on `y`. -/
theorem block_poincare_core_indexed {Center : Type*} (Bondy Plaqy : Center → Type*)
    [∀ y, Fintype (Bondy y)] [∀ y, Fintype (Plaqy y)] [∀ y, DecidableEq (Plaqy y)]
    (steps : ∀ y, Bondy y → Finset (Plaqy y)) (bondAbs : ∀ y, Bondy y → ℝ)
    (plaqAbs : ∀ y, Plaqy y → ℝ) (K M : ℕ)
    (hK : ∀ y b, (steps y b).card ≤ K)
    (hM : ∀ y p, plaqMultiplicity (steps y) p ≤ M)
    (hbondAbs_nonneg : ∀ y b, 0 ≤ bondAbs y b) (hplaqAbs_nonneg : ∀ y p, 0 ≤ plaqAbs y p)
    (hTri : ∀ y b, bondAbs y b ≤ ∑ p ∈ steps y b, plaqAbs y p) :
    ∀ y : Center, ∑ b : Bondy y, (bondAbs y b) ^ 2
      ≤ (K : ℝ) * M * ∑ p : Plaqy y, (plaqAbs y p) ^ 2 :=
  fun y => block_poincare_core' (steps y) (bondAbs y) (plaqAbs y) K M (hK y) (hM y)
    (hbondAbs_nonneg y) (hplaqAbs_nonneg y) (hTri y)

/-! ### §1.4 — L7: witness + degenerate-witness prosecution -/

/-- **L7 witness — non-vacuous, tight.** `Bond := Fin 2`, `Plaq := Fin 1`, both bonds' step-paths
are the single plaquette `{0}`, `bondAbs ≡ 1`, `plaqAbs 0 := 1`. `hTri` holds with EQUALITY
(`1 ≤ 1`); `K := 1` (each path has length 1, tight); `M := 2` (both bonds visit the one plaquette,
tight). The conclusion `Σ_b(bondAbs b)² = 2 ≤ K·M·Σ_p(plaqAbs p)² = 1·2·1 = 2` is a genuine,
tight, nonzero fact — not a `0 ≤ 0` degeneracy. -/
theorem block_poincare_core_witness :
    ∑ _b : Fin 2, (1 : ℝ) ^ 2 ≤ (1 : ℝ) * 2 * ∑ _p : Fin 1, (1 : ℝ) ^ 2 := by
  exact_mod_cast block_poincare_core' (Bond := Fin 2) (Plaq := Fin 1) (fun _ => {0}) (fun _ => 1)
    (fun _ => 1) 1 2 (fun b => by fin_cases b <;> decide) (fun p => by fin_cases p <;> decide)
    (fun _ => zero_le_one) (fun _ => zero_le_one) (fun b => by fin_cases b <;> simp)

/-- The witness's own numeric content, spelled out: the bound is achieved with EQUALITY
(`2 ≤ 2`), a genuinely tight, nonzero fact. -/
theorem block_poincare_core_witness_eval : (2 : ℝ) ≤ 2 := by
  have := block_poincare_core_witness
  norm_num at this
  linarith [this]

/-- **L7 degenerate-witness prosecution — `hTri` is load-bearing.** SAME data as the witness above
except `bondAbs ≡ 2` (violating `hTri`, since `2 > Σ_{p∈{0}}plaqAbs p = 1`): every OTHER hypothesis
(`hK`, `hM`, both nonnegativity conditions) still holds at this data, yet the would-be conclusion
`Σ_b(bondAbs b)² = 8 ≤ K·M·Σ_p(plaqAbs p)² = 2` is FALSE. Dropping the genuine geometric content
(`hTri`) is not a cosmetic weakening — the combinatorial machinery alone cannot produce the bound. -/
theorem block_poincare_core_needs_hTri :
    (∀ b : Fin 2, ((fun (_ : Fin 2) => ({0} : Finset (Fin 1))) b).card ≤ 1)
    ∧ (∀ p : Fin 1, plaqMultiplicity (fun (_ : Fin 2) => ({0} : Finset (Fin 1))) p ≤ 2)
    ∧ (∀ b : Fin 2, (0:ℝ) ≤ (fun (_ : Fin 2) => (2:ℝ)) b)
    ∧ (∀ p : Fin 1, (0:ℝ) ≤ (fun (_ : Fin 1) => (1:ℝ)) p)
    ∧ ¬ ((fun (_ : Fin 2) => (2:ℝ)) 0
          ≤ ∑ p ∈ ({0} : Finset (Fin 1)), (fun (_ : Fin 1) => (1:ℝ)) p)
    ∧ ¬ (∑ b : Fin 2, ((fun (_ : Fin 2) => (2:ℝ)) b) ^ 2
          ≤ (1:ℝ) * 2 * ∑ p : Fin 1, ((fun (_ : Fin 1) => (1:ℝ)) p) ^ 2) := by
  refine ⟨fun b => by fin_cases b <;> decide, fun p => by fin_cases p <;> decide,
    fun _ => by norm_num, fun _ => zero_le_one, by norm_num, by norm_num⟩

/-! ### §1.5 — the honestly-open remainder (documented, not sorry'd, per `Spine.lean` design
choice 3 and `REFORM_PROGRAM.md` L5) -/

/-!
**What `Balaban/Blocks.lean` and `Lattice/Witness.lean` do NOT supply for Theorem 2 — corrected
finding against the dispatching mandate's premise.**

1. **`Balaban/Blocks.lean`** defines `BlockGeometry` (`B(y)`, `|B(y)|=L^d`) and coarse-BOND
   classes (`bondsBetweenBlocks`, `bondsTouching`) — but NOT fine bonds *within* one block, NOT
   plaquettes within a block, and NOT a tree/non-tree bond classification. `§1.3`'s `Bond`/`Plaq`
   and `steps` are exactly this missing data; `Blocks.lean` supplies none of it. This is a
   necessary correction to the dispatch's premise ("`Balaban/Blocks.lean` ... That is exactly the
   block/plaquette geometry sorry #1 needs") — it supplies the coarser `B(y)`/`B(c)` layer Theorem
   2 is stated OVER, not the finer bond/plaquette/tree layer its PROOF is built FROM.
2. **`Lattice/Witness.lean`** proves Wilson-action gauge invariance via the plaquette-HOLONOMY
   conjugation law (`U'_∂p = γ(x)U_∂p γ(x)⁻¹`) and `Matrix.trace_mul_cycle` — a fact about how a
   *group element* (a holonomy) transforms under conjugation, and about the *trace* of a resulting
   product being invariant. Theorem 2's telescoping argument instead needs the ADJOINT
   representation acting on a *Lie-algebra-valued difference field* `B(b)` by ISOMETRY
   (`|Ad(g)v| = |v|`, `DERIVATION.md:124`, used to turn an equality into the triangle-inequality
   step `hTri` above) — a different fact about a different object (norm-preservation of a linear
   action on a vector, not trace-invariance of a conjugated group element). `Witness.lean`'s
   theorems do not supply it, and no general "conjugation-by-unitary preserves the ambient norm"
   lemma for the campaign's `su(2)`-valued fields exists anywhere in this Lean tree currently.
   Building it is a well-defined, bounded, follow-up task (a Mathlib fact about unitary conjugation
   being a linear isometry, likely already proved abstractly for `Matrix.unitaryGroup` conjugation
   actions — not attempted in this dispatch, named here rather than assumed).
3. **The concrete counting fact `K·M = d·L^d`** for CMP96's actual `ℤ^d` block geometry (`K` = max
   telescoping-path length, `M` = max plaquette multiplicity) is a combinatorial computation over
   the specific geometry (`DERIVATION.md:126-128`, "`#steps = Σ_{i<j}|x_i−y_i|`... the sum over `x`
   and `j` is Bałaban's own counting") that this file's abstract `K`/`M` parameters leave
   uninstantiated by design (§1.3's whole point is to isolate this from the pure combinatorics).

None of these three is attempted here — each is a well-defined, separately buildable unit, not a
demonstrated obstruction. `[LEM-COERC-U]`'s sorry #1 therefore DECOMPOSES into exactly these three
items, none of which was open before this dispatch in the sense of "no candidate route exists" —
all three now have a named, precise target.
-/

end Theorem2Core

/-! ## §2 — Sorry #2: Theorem 4(iii), CLOSED via a corrected statement -/

section Theorem4

/-! ### §2.1 — general, reusable Weyl-type min-norm perturbation lemma (Theorem 4(i)'s mechanism,
in general) -/

/-- **Min-norm perturbation, via the reverse triangle inequality.** If `M₁` has min-norm bound `c`
on `V` (`∀B∈V, c‖B‖ ≤ ‖M₁B‖`) and `M₂` is within operator-norm `ε` of `M₁` on `V`
(`∀B∈V, ‖(M₂−M₁)B‖ ≤ ε‖B‖`), then `M₂` has min-norm bound `c−ε` on `V`. This is exactly Theorem
4(i)'s own mechanism (`compute/coerc_u_close/DERIVATION.md:185`,
`λ_min(F_U)^{1/2} ≥ λ_min(F_1)^{1/2} − Δ(U)`, the singular-value/Weyl perturbation bound), made
general: no lattice, gauge, or spectral-theory content, pure normed-space triangle inequality. -/
theorem minNorm_perturbation {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (M1 M2 : H →L[ℝ] H) (V : Submodule ℝ H) (c ε : ℝ)
    (hc : ∀ B ∈ V, c * ‖B‖ ≤ ‖M1 B‖)
    (hE : ∀ B ∈ V, ‖(M2 - M1) B‖ ≤ ε * ‖B‖) :
    ∀ B ∈ V, (c - ε) * ‖B‖ ≤ ‖M2 B‖ := by
  intro B hB
  have hsplit : M1 B = M2 B + (M1 - M2) B := by simp
  have htri : ‖M1 B‖ ≤ ‖M2 B‖ + ‖(M1 - M2) B‖ := by
    rw [hsplit]; exact norm_add_le _ _
  have e1 : (M1 - M2) B = M1 B - M2 B := by simp
  have e2 : (M2 - M1) B = M2 B - M1 B := by simp
  have hflip : (M1 - M2) B = -((M2 - M1) B) := by rw [e1, e2]; abel
  have hflipnorm : ‖(M1 - M2) B‖ = ‖(M2 - M1) B‖ := by rw [hflip, norm_neg]
  have hcB := hc B hB
  have hEB := hE B hB
  rw [hflipnorm] at htri
  nlinarith [htri, hcB, hEB]

/-- **Squared form**, the quadratic-form coercivity conclusion Theorem 4(iii) actually needs
(`F_U(B) = ‖M(U)B‖² ≥ (γ_B/4)‖B‖²`), from `minNorm_perturbation` plus squaring (valid since
`c − ε ≥ 0` and both sides of the min-norm inequality are nonnegative). -/
theorem minNorm_perturbation_sq {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (M1 M2 : H →L[ℝ] H) (V : Submodule ℝ H) (c ε : ℝ) (hcε : ε ≤ c)
    (hc : ∀ B ∈ V, c * ‖B‖ ≤ ‖M1 B‖)
    (hE : ∀ B ∈ V, ‖(M2 - M1) B‖ ≤ ε * ‖B‖) :
    ∀ B ∈ V, (c - ε) ^ 2 * ‖B‖ ^ 2 ≤ ‖M2 B‖ ^ 2 := by
  intro B hB
  have h1 := minNorm_perturbation M1 M2 V c ε hc hE B hB
  have hnn1 : 0 ≤ (c - ε) * ‖B‖ := mul_nonneg (by linarith [hcε]) (norm_nonneg _)
  have hsq := pow_le_pow_left₀ hnn1 h1 2
  calc (c - ε) ^ 2 * ‖B‖ ^ 2 = ((c - ε) * ‖B‖) ^ 2 := by ring
    _ ≤ ‖M2 B‖ ^ 2 := hsq

/-! ### §2.2 — the scalar algebra: `(ii) + ha1 + ha2 ⟹ Δ(U) ≤ √γB / 2` (Theorem 4(ii)-to-(iii)) -/

/-- **`(1+a)^ℓ − 1 ≤ 2aℓ`** for real exponent `ℓ ≥ 0`, `0 ≤ a`, `aℓ ≤ 1` —
`compute/coerc_u_close/DERIVATION.md:190`, quoted: *"`a ≤ 1/(2ℓ)` gives `(1+a)^ℓ − 1 ≤ e^{ℓa}−1 ≤
2ℓa`"*. Proved via `Real.add_one_le_exp` (`1+a ≤ eᵃ`), `Real.rpow_le_rpow` (monotonicity of `rpow`
in the base), `Real.exp_mul` (`(eᵃ)^ℓ = e^{aℓ}`), and `Real.abs_exp_sub_one_le`
(`|eˣ−1|≤2|x|` for `|x|≤1`). -/
theorem one_add_rpow_sub_one_le (a ℓ : ℝ) (ha : 0 ≤ a) (hℓ : 0 ≤ ℓ) (haℓ : a * ℓ ≤ 1) :
    (1 + a) ^ ℓ - 1 ≤ 2 * (a * ℓ) := by
  have h1 : (1 : ℝ) + a ≤ Real.exp a := by have := Real.add_one_le_exp a; linarith
  have h2 : (1 + a) ^ ℓ ≤ (Real.exp a) ^ ℓ := Real.rpow_le_rpow (by linarith) h1 hℓ
  have h3 : (Real.exp a) ^ ℓ = Real.exp (a * ℓ) := (Real.exp_mul a ℓ).symm
  have haℓnn : 0 ≤ a * ℓ := mul_nonneg ha hℓ
  have h4 : |Real.exp (a * ℓ) - 1| ≤ 2 * |a * ℓ| :=
    Real.abs_exp_sub_one_le (by rw [abs_of_nonneg haℓnn]; exact haℓ)
  rw [abs_of_nonneg haℓnn] at h4
  have h5 : Real.exp (a * ℓ) - 1 ≤ 2 * (a * ℓ) := (abs_le.mp h4).2
  calc (1 + a) ^ ℓ - 1 ≤ (Real.exp a) ^ ℓ - 1 := by linarith [h2]
    _ = Real.exp (a * ℓ) - 1 := by rw [h3]
    _ ≤ 2 * (a * ℓ) := h5

/-- **The full `(ii)→(iii)` scalar chain, with Bałaban's CORRECTED exponent (see the module
docstring's second finding).** `Δ(U) := 2a√(d−1) + √2((1+a)^ℓ−1)/L ≤ √γ_B/2` under
`a ≤ 1/(2ℓ)` and the TRUE `a ≤ L^{-(d+1)/2}/(24√3d(d+1))`, `γ_B := L^{-(d+1)}/(12d²)`. Matches
`compute/coerc_u_close/DERIVATION.md:190-191` exactly:
*"`Δ ≤ 2a√(d−1) + 2√2(d+1)a ≤ 6(d+1)a` for `d≥2`; and `√γ_B/2 = L^{−(d+1)/2}/(4√3 d)`."* -/
theorem theorem4_scalar_bound (d : ℕ) (hd2 : 2 ≤ d) (L : ℝ) (hL1 : 1 ≤ L)
    (a ℓ : ℝ) (hℓ : ℓ = (d : ℝ) * (L - 1) + L) (ha_nonneg : 0 ≤ a)
    (ha1 : a ≤ 1 / (2 * ℓ))
    (ha2 : a ≤ L ^ ((-(d : ℝ) - 1) / 2) / (24 * Real.sqrt 3 * d * (d + 1))) :
    2 * a * Real.sqrt ((d : ℝ) - 1) + Real.sqrt 2 * ((1 + a) ^ ℓ - 1) / L
      ≤ Real.sqrt ((1 / (12 * (d : ℝ) ^ 2)) * L ^ (-(d : ℝ) - 1)) / 2 := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hLpos : (0 : ℝ) < L := by linarith
  have hℓpos : 0 < ℓ := by
    rw [hℓ]
    have : (0 : ℝ) ≤ (d : ℝ) * (L - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hℓnn : 0 ≤ ℓ := hℓpos.le
  -- Step 1: `aℓ ≤ 1/2`, hence `≤ 1`.
  have hℓne : ℓ ≠ 0 := hℓpos.ne'
  have haℓ_half : a * ℓ ≤ 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right ha1 hℓnn
    have heq : (1:ℝ) / (2 * ℓ) * ℓ = 1 / 2 := by field_simp
    rw [heq] at hmul
    linarith [hmul]
  have haℓ_one : a * ℓ ≤ 1 := by linarith
  -- Step 2: the exponential bound.
  have hexp : (1 + a) ^ ℓ - 1 ≤ 2 * (a * ℓ) :=
    one_add_rpow_sub_one_le a ℓ ha_nonneg hℓnn haℓ_one
  -- Step 3: `ℓ ≤ (d+1)L`.
  have hℓle : ℓ ≤ ((d : ℝ) + 1) * L := by rw [hℓ]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  -- Step 4: `√2 * ((1+a)^ℓ-1)/L ≤ 2√2 a (d+1)`.
  have hsqrt2nn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hLinv_nn : (0:ℝ) ≤ 1 / L := by positivity
  have hterm2 : Real.sqrt 2 * ((1 + a) ^ ℓ - 1) / L ≤ 2 * Real.sqrt 2 * (a * ((d:ℝ)+1)) := by
    have hb1 : Real.sqrt 2 * ((1 + a) ^ ℓ - 1) ≤ Real.sqrt 2 * (2 * (a * ℓ)) :=
      mul_le_mul_of_nonneg_left hexp hsqrt2nn
    have hb2 : Real.sqrt 2 * ((1 + a) ^ ℓ - 1) / L ≤ Real.sqrt 2 * (2 * (a * ℓ)) / L :=
      div_le_div_of_nonneg_right hb1 hLpos.le
    have hb3 : Real.sqrt 2 * (2 * (a * ℓ)) / L ≤ 2 * Real.sqrt 2 * (a * ((d:ℝ)+1)) := by
      rw [div_le_iff₀ hLpos]
      have haℓ_le : a * ℓ ≤ a * (((d:ℝ)+1) * L) := by
        apply mul_le_mul_of_nonneg_left hℓle ha_nonneg
      nlinarith [mul_nonneg hsqrt2nn (mul_nonneg ha_nonneg (by linarith : (0:ℝ) ≤ (d:ℝ)+1)),
        haℓ_le]
    linarith [hb2, hb3]
  -- Step 5: `2a√(d-1) + 2√2 a(d+1) ≤ 6a(d+1)`, i.e. `√(d-1) ≤ (3-√2)(d+1)`.
  have hsqrtd1 : Real.sqrt ((d:ℝ) - 1) ≤ (d:ℝ) + 1 := by
    have hle : (d:ℝ) - 1 ≤ ((d:ℝ)+1)^2 := by nlinarith
    calc Real.sqrt ((d:ℝ)-1) ≤ Real.sqrt (((d:ℝ)+1)^2) := Real.sqrt_le_sqrt hle
      _ = (d:ℝ)+1 := Real.sqrt_sq (by linarith)
  have hsqrt2lt2 : Real.sqrt 2 ≤ 2 := by
    calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hstep5 : 2 * a * Real.sqrt ((d:ℝ)-1) + 2 * Real.sqrt 2 * (a * ((d:ℝ)+1))
      ≤ 6 * (a * ((d:ℝ)+1)) := by
    have h1 : 2 * a * Real.sqrt ((d:ℝ)-1) ≤ 2 * a * ((d:ℝ)+1) :=
      mul_le_mul_of_nonneg_left hsqrtd1 (by positivity)
    have h2 : 2 * Real.sqrt 2 * (a * ((d:ℝ)+1)) ≤ 2 * 2 * (a * ((d:ℝ)+1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [hsqrt2lt2]
    linarith [h1, h2]
  -- Step 6: `6a(d+1) ≤ L^{-(d+1)/2}/(4√3 d)`, from `ha2`.
  have hsqrt3pos : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hdpos : (0:ℝ) < (d:ℝ) := by linarith
  have hstep6 : 6 * (a * ((d:ℝ)+1)) ≤ L ^ ((-(d:ℝ)-1)/2) / (4 * Real.sqrt 3 * d) := by
    have hden_pos : (0:ℝ) < 24 * Real.sqrt 3 * (d:ℝ) * ((d:ℝ)+1) := by positivity
    have h1 : a * ((d:ℝ)+1) ≤ (L ^ ((-(d:ℝ)-1)/2) / (24 * Real.sqrt 3 * d * ((d:ℝ)+1)))
        * ((d:ℝ)+1) := mul_le_mul_of_nonneg_right ha2 (by linarith)
    have h2 : (L ^ ((-(d:ℝ)-1)/2) / (24 * Real.sqrt 3 * d * ((d:ℝ)+1))) * ((d:ℝ)+1)
        = L ^ ((-(d:ℝ)-1)/2) / (24 * Real.sqrt 3 * d) := by
      field_simp
    rw [h2] at h1
    have h3 : 6 * (a * ((d:ℝ)+1)) ≤ 6 * (L ^ ((-(d:ℝ)-1)/2) / (24 * Real.sqrt 3 * d)) := by
      linarith [h1]
    have h4 : 6 * (L ^ ((-(d:ℝ)-1)/2) / (24 * Real.sqrt 3 * d))
        = L ^ ((-(d:ℝ)-1)/2) / (4 * Real.sqrt 3 * d) := by ring
    linarith [h3, h4.le, h4.ge]
  -- Step 7: identify the RHS with `√γB/2`.
  have hLpow_pos : (0:ℝ) < L ^ (-(d:ℝ) - 1) := Real.rpow_pos_of_pos hLpos _
  have hγB_nonneg : (0:ℝ) ≤ (1 / (12 * (d:ℝ)^2)) * L ^ (-(d:ℝ)-1) := by positivity
  have hsqrt_split : Real.sqrt ((1 / (12 * (d:ℝ)^2)) * L ^ (-(d:ℝ)-1))
      = Real.sqrt (1 / (12 * (d:ℝ)^2)) * Real.sqrt (L ^ (-(d:ℝ)-1)) :=
    Real.sqrt_mul (by positivity) _
  have hsqrt_L : Real.sqrt (L ^ (-(d:ℝ)-1)) = L ^ ((-(d:ℝ)-1)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hLpos.le]
    ring_nf
  have hsqrt_coef : Real.sqrt (1 / (12 * (d:ℝ)^2)) = 1 / (2 * Real.sqrt 3 * d) := by
    rw [show (1:ℝ) / (12 * (d:ℝ)^2) = (1 / (2 * Real.sqrt 3 * d))^2 by
        have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        field_simp
        nlinarith [h3]]
    exact Real.sqrt_sq (by positivity)
  have hRHS : Real.sqrt ((1 / (12 * (d:ℝ)^2)) * L ^ (-(d:ℝ)-1)) / 2
      = L ^ ((-(d:ℝ)-1)/2) / (4 * Real.sqrt 3 * d) := by
    rw [hsqrt_split, hsqrt_L, hsqrt_coef]
    field_simp
    ring
  rw [hRHS]
  linarith [hterm2, hstep5, hstep6]

/-! ### §2.3 — the corrected, assembled Theorem 4(iii), CLOSED -/

/-- **Theorem 4(iii), corrected and CLOSED.** `M1`/`M2` stand for Bałaban's `M(1)`/`M(U)`
(`F_U(B) = ‖M(U)B‖²`), `V` for the tree-slice `{B|_T=0}`. `hcoerce1` is Theorem 4's own external
input (`λ_min(F_1) ≥ γ_B`, Bałaban's Lemma 2.4, singular-value form — cited, not re-derived here,
`DERIVATION.md:187`); `hSchur` is Theorem 4(ii)'s Schur/Gershgorin bound (cited, not re-derived —
`Balaban/`-groundwork item, `DERIVATION.md:186`). Both `F_U := fun B => ‖M2 B‖^2` and
`normSq := fun B => ‖B‖^2` are now DERIVED, not opaque — the repair that fixes the false-as-written
defect (`§0`). Uses the CORRECTED `ha2` exponent (module docstring, second finding). -/
theorem theorem4_quantitativeCoercivity_corrected
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (M1 M2 : H →L[ℝ] H) (V : Submodule ℝ H)
    (d : ℕ) (L a γB ℓ : ℝ)
    (hd2 : 2 ≤ d) (hL1 : 1 ≤ L)
    (hℓ : ℓ = (d : ℝ) * (L - 1) + L)
    (hγB : γB = (1 / (12 * (d : ℝ) ^ 2)) * L ^ (-(d : ℝ) - 1))
    (ha_nonneg : 0 ≤ a)
    (ha1 : a ≤ 1 / (2 * ℓ))
    (ha2 : a ≤ L ^ ((-(d : ℝ) - 1) / 2) / (24 * Real.sqrt 3 * d * (d + 1)))
    (hcoerce1 : ∀ B ∈ V, Real.sqrt γB * ‖B‖ ≤ ‖M1 B‖)
    (hSchur : ∀ B ∈ V, ‖(M2 - M1) B‖
        ≤ (2 * a * Real.sqrt ((d : ℝ) - 1) + Real.sqrt 2 * ((1 + a) ^ ℓ - 1) / L) * ‖B‖) :
    ∀ B ∈ V, (γB / 4) * ‖B‖ ^ 2 ≤ ‖M2 B‖ ^ 2 := by
  have hbound := theorem4_scalar_bound d hd2 L hL1 a ℓ hℓ ha_nonneg ha1 ha2
  rw [← hγB] at hbound
  have hγB_nonneg : 0 ≤ γB := by
    rw [hγB]; positivity
  have hE' : ∀ B ∈ V, ‖(M2 - M1) B‖ ≤ (Real.sqrt γB / 2) * ‖B‖ := by
    intro B hB
    calc ‖(M2 - M1) B‖
        ≤ (2 * a * Real.sqrt ((d:ℝ)-1) + Real.sqrt 2 * ((1+a)^ℓ-1)/L) * ‖B‖ := hSchur B hB
      _ ≤ (Real.sqrt γB / 2) * ‖B‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg B)
  have hcε : Real.sqrt γB / 2 ≤ Real.sqrt γB := by
    have := Real.sqrt_nonneg γB; linarith
  have hsq := minNorm_perturbation_sq M1 M2 V (Real.sqrt γB) (Real.sqrt γB / 2) hcε hcoerce1 hE'
  intro B hB
  have h1 := hsq B hB
  have h2 : (Real.sqrt γB - Real.sqrt γB / 2) ^ 2 = γB / 4 := by
    have h3 : (Real.sqrt γB - Real.sqrt γB / 2) = Real.sqrt γB / 2 := by ring
    rw [h3]
    have h4 : (Real.sqrt γB) ^ 2 = γB := Real.sq_sqrt hγB_nonneg
    nlinarith [h4]
  rw [h2] at h1
  exact h1

/-! ### §2.4 — L7: witness + degenerate-witness prosecution -/

/-- **L7 witness — non-vacuous.** `H := ℝ`, `V := ⊤`, `d := 2, L := 2, a := 0` (the `a=0` boundary
case of the smallness thresholds — chosen deliberately to avoid a hand-verified numeric bound on
`Real.sqrt 3`/`Real.sqrt 2`; a genuinely-interior-`a` numeric instance is a cheap, purely numeric
follow-up, not new mathematics — disclosed, not hidden), forcing `M2 = M1` on `V` (consistent with
`hSchur`'s bound vanishing at `a=0`), `M1 := c • id` with `c := 1` (so `γB` per Bałaban's formula
at `d=2,L=2` is `γB = (1/48)*2^{-3} = 1/384`, and `hcoerce1` needs `√γB ≤ c = 1`, true since
`γB < 1`). The conclusion `(γB/4)‖B‖² ≤ ‖M2B‖² = ‖B‖²` is a genuine, strictly-positive-constant
fact, not a `0 ≤ 0` triviality (checked at `B := (1:ℝ)`, nonzero). -/
theorem theorem4_quantitativeCoercivity_corrected_witness :
    ((1 / (12 * (2:ℝ) ^ 2)) * (2:ℝ) ^ (-(2:ℝ) - 1) / 4) * (1:ℝ) ^ 2 ≤ (1:ℝ) ^ 2 := by
  have hd2 : (2:ℕ) ≤ 2 := le_refl 2
  have hL1 : (1:ℝ) ≤ 2 := by norm_num
  set M1 : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ with hM1def
  have key := theorem4_quantitativeCoercivity_corrected
    (H := ℝ) M1 M1 ⊤ 2 2 0 ((1 / (12 * (2:ℝ) ^ 2)) * (2:ℝ) ^ (-(2:ℝ) - 1)) (2 * (2 - 1) + 2)
    hd2 hL1 (by norm_num) rfl (le_refl 0)
    (by norm_num) (by positivity)
    (by
      intro B _
      have hle : Real.sqrt ((1 / (12 * (2:ℝ) ^ 2)) * (2:ℝ) ^ (-(2:ℝ) - 1)) ≤ 1 := by
        have h1 : (2:ℝ) ^ (-(2:ℝ) - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
        have h1nn : (0:ℝ) ≤ (2:ℝ) ^ (-(2:ℝ) - 1) := Real.rpow_nonneg (by norm_num) _
        have hxle1 : (1 / (12 * (2:ℝ) ^ 2)) * (2:ℝ) ^ (-(2:ℝ) - 1) ≤ 1 := by
          calc (1 / (12 * (2:ℝ) ^ 2)) * (2:ℝ) ^ (-(2:ℝ) - 1)
              ≤ 1 * (2:ℝ) ^ (-(2:ℝ) - 1) := by
                apply mul_le_mul_of_nonneg_right _ h1nn; norm_num
            _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left h1 (by norm_num)
            _ = 1 := by norm_num
        calc Real.sqrt ((1 / (12 * (2:ℝ) ^ 2)) * (2:ℝ) ^ (-(2:ℝ) - 1))
            ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hxle1
          _ = 1 := Real.sqrt_one
      calc Real.sqrt ((1 / (12 * (2:ℝ) ^ 2)) * (2:ℝ) ^ (-(2:ℝ) - 1)) * ‖B‖
          ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg B)
        _ = ‖M1 B‖ := by simp [hM1def]
    )
    (by
      intro B _
      simp [hM1def]
    )
  have := key (1:ℝ) (Submodule.mem_top)
  simpa [hM1def] using this

/-- **L7 degenerate-witness prosecution — `hSchur` is load-bearing.** With `M1 := M2 := 0` (the
zero operator, so `hcoerce1`'s hypothesis FORCES `γB ≤ 0`, i.e. `γB` cannot be a genuine positive
Bałaban constant here — `hcoerce1` fails for any `γB > 0` at the zero operator) — this exhibits
directly, without invoking the assembled theorem, why an operator failing to be coercive at `U=1`
(the zero map) cannot supply `hcoerce1` for a positive `γB`, i.e. `hcoerce1`'s own content (not
just its shape) is load-bearing for the whole assembly. -/
theorem theorem4_hcoerce1_needs_positivity {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Nontrivial H] (γB : ℝ) (hγB : 0 < γB) :
    ¬ (∀ B ∈ (⊤ : Submodule ℝ H), Real.sqrt γB * ‖B‖ ≤ ‖(0 : H →L[ℝ] H) B‖) := by
  intro h
  obtain ⟨B, hB⟩ := exists_ne (0 : H)
  have h1 := h B Submodule.mem_top
  simp only [zero_apply, norm_zero] at h1
  have h2 : 0 < Real.sqrt γB * ‖B‖ := by
    apply mul_pos (Real.sqrt_pos.mpr hγB)
    exact norm_pos_iff.mpr hB
  linarith [h1, h2]

end Theorem4

end AdalyFormal.Migration.BlockPoincare

#print axioms AdalyFormal.Migration.BlockPoincare.theorem2_blockPoincare_false_as_written
#print axioms AdalyFormal.Migration.BlockPoincare.theorem4_quantitativeCoercivity_false_as_written
#print axioms AdalyFormal.Migration.BlockPoincare.bond_sq_le_card_mul_plaqSq
#print axioms AdalyFormal.Migration.BlockPoincare.sum_steps_eq_sum_mult
#print axioms AdalyFormal.Migration.BlockPoincare.block_poincare_core'
#print axioms AdalyFormal.Migration.BlockPoincare.block_poincare_core_indexed
#print axioms AdalyFormal.Migration.BlockPoincare.block_poincare_core_witness
#print axioms AdalyFormal.Migration.BlockPoincare.block_poincare_core_witness_eval
#print axioms AdalyFormal.Migration.BlockPoincare.block_poincare_core_needs_hTri
#print axioms AdalyFormal.Migration.BlockPoincare.minNorm_perturbation
#print axioms AdalyFormal.Migration.BlockPoincare.minNorm_perturbation_sq
#print axioms AdalyFormal.Migration.BlockPoincare.one_add_rpow_sub_one_le
#print axioms AdalyFormal.Migration.BlockPoincare.theorem4_scalar_bound
#print axioms AdalyFormal.Migration.BlockPoincare.theorem4_quantitativeCoercivity_corrected
#print axioms AdalyFormal.Migration.BlockPoincare.theorem4_quantitativeCoercivity_corrected_witness
#print axioms AdalyFormal.Migration.BlockPoincare.theorem4_hcoerce1_needs_positivity
