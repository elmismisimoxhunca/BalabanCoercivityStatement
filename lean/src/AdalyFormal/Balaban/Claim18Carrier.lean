/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# `Claim18Carrier.lean` — Claim 18's clause bundle at the TWO-SPACE carrier (`[RES-CLAIM18-CARRIER]`)

## Why this module exists

`Spine.Claim18Clauses` states Claim 18 at the single carrier `H →L[ℝ] H`, and at that carrier the
bundle is **PROVED UNSATISFIABLE** in the genuine-coarsening regime
(`Spine.claim18_corrected_unsatisfiable_at_zero_field_nontrivial`: `1 < L`, every `d`, `α₀ = 0`,
`1 ≤ finrank ℝ H`), so `Spine.claim18_exists` is FALSE AS WRITTEN there. The reason is a THEOREM, not
a suspicion: `Spine.claim18_carrier_obstruction` shows clause 1 (`Qc ∘L Qc_inv = id`) forces `Qc`
INJECTIVE on a finite-dimensional space, while Bałaban's `𝒬_c` averages many fine bonds onto one
coarse bond and is therefore NON-injective, its kernel being the fluctuation subspace. The two are
inconsistent at one space, so no clause statable at `H →L[ℝ] H` can express the object.

This module carries the bundle at `Hfine →L[ℝ] Hcoarse`, where `Qc` CAN be a genuine coarse average:
a section forces `Qc` SURJECTIVE, and surjectivity forces injectivity only when the two spaces have
the same dimension. `forces_dimension_drop` below turns that sentence into a theorem.

## The clause-by-clause diff against `Spine.Claim18Clauses`, and its provenance

| # | `Spine.Claim18Clauses` (single carrier) | here (two carriers) | why |
|---|---|---|---|
| 1 | `Qc ∘L Qc_inv = id H` | `Qc ∘L Qc_inv = id Hcoarse` | same clause, now between two spaces |
| 2 | `Function.Injective Qc_inv` | unchanged | `[RES-SPINE-GAP2-NONDEGEN]`'s prescribed minimum, retained visibly |
| 3 | `‖Qc‖ ≤ L^{-d}(1 + Ccorr·L^{d+1}·α₀)` | `‖Qc‖ ≤ 1 + Ccorr·L²·α₀` | **Spine §3b.0's own prescription for this carrier**, and the FAITHFUL form: CMP98 p.36 (126) reads `|(Q(V₀)A)_c| ≦ \|A\| + O(1)L²α₀\|A\|`, an ABSOLUTE operator bound with `‖Q₀‖ ≤ 1` (grade 2: Claude + blind Sol, `compute/page_adjudications_0726/`). The `L^{-d}` form is that same estimate taken RELATIVE to the main term and is what made the single-carrier squeeze bite. |
| 4 | `(1 ≤ finrank → 1 ≤ ‖C2‖) ∧ (2 ≤ finrank → Qc` non-scalar`)` | `(1 ≤ finrank ℝ Hfine → 1 ≤ ‖C2‖) ∧ ¬ Function.Injective Qc` | non-scalarity is UNSTATABLE between two different spaces (there is no `id : Hfine →L Hcoarse` to compare against) and was only ever a PROXY for "`Qc` is not essentially invertible". The content it proxied — non-injectivity, kernel = the fluctuation subspace — is statable here, and is strictly stronger than the proxy: it kills every injective `Qc`, hence every isometry and every rescaled isometry, in one clause (`blocks_injective_Qc`). |
| 5 | `‖C2 ∘L Qc_inv‖ ≤ L^{(d:ℝ)-1}` | unchanged | Claim 18's own constant; the ℝ exponent is Spine §3d's repair (the ℕ-truncating `L^(d-1)` imposed nothing at `d = 0`) |
| 6 | — | `C2 ∘L Qc_inv ≠ 0` | **NEW, and it is load-bearing.** Without it the two-space bundle is satisfiable with a ZERO transfer operator: `C2` may annihilate `range Qc_inv` while keeping `‖C2‖ ≥ 1` on `ker Qc` — the original zero-witness defect ("an upper bound on a composition is defeated by shrinking either factor") re-entering through the door the carrier change opens. `compute/claim18_carrier/carrier_attacks.lean` compiles the landing witness for clauses 1-5 alone (`ClausesWithoutTransferNondegeneracy`), which is what makes clause 6 a measurement rather than a decoration. It is the weakest non-degeneracy that does the job: a qualitative `≠ 0`, never a numeric floor. A floor `1 ≤ ‖C2 ∘L Qc_inv‖` would conflict with clause 5 at `d = 0` (`1 ≤ L^{-1}` is false for `1 < L`) and so would re-create a false-as-written point inside `main`'s own admitted `d` range; a `≠ 0` cannot conflict with an upper bound, because the transfer can always be rescaled. |

**Clause 4's guard is retained and its reason respected** (Spine §3c): `1 ≤ ‖C2‖` is FALSE when
`Hfine = 0`, so it keeps its `1 ≤ finrank ℝ Hfine` guard. Non-injectivity needs no guard: it is not
false at a degenerate carrier, it is merely unsatisfiable there, and that unsatisfiability is exactly
the genuine-coarsening requirement (`forces_two_le_finrank_fine`).

## HONEST SCOPE — three disclosed limits, none of them silent

1. **The norm class.** CMP98 (126) is a bound in the SUP norm on bond fields; the clause is stated in
   the OPERATOR norm of whatever carrier norms are supplied. For a genuine average both give `≤ 1`
   (a convex combination in sup norm; a unit-mass weight vector in `ℓ²`), so the constant `1` is not
   an artefact of the choice — ~~but the two norms are not the same functional, and this is a disclosed
   simplification of the same kind `IteratedAveraging.lean` uses for its point-evaluation stand-in.~~
   **SUPERSEDED 2026-07-27 (S75, `Balaban/QcEquation.lean` §6): the two norms are still not the same
   functional, but the simplification is no longer load-bearing — for the SUPPLIED operator BOTH are
   proved, `QcEquation.qc_sup_bound` (CMP98 (126)'s own sup-norm class) and
   `QcEquation.qcOp_opNorm_le_one` (the `ℓ²` operator norm this clause consumes), so the clause holds
   whichever norm class is read.**
2. ~~**`Qc` is still EXISTENTIALLY quantified, not the lattice averaging.** This module fixes the
   CARRIER; it does not supply Bałaban's `𝒬_c`. The residual for that is `[RES-O1-NEEDS-QC]`, and~~
   **SUPERSEDED 2026-07-27 (S75): `Balaban/QcEquation.lean` supplies `𝒬_c` BY EQUATION
   (`QcEquation.SuppliedClauses` instantiates THIS predicate at
   `Qc := LineIntegralAveraging.lineCoarseRestrictCLM` and `Qc_inv := QcEquation.qcSection`), and
   `QcEquation.suppliedClauses_iff` proves the surviving freedom is three conditions on `C⁽²⁾` alone —
   the successor residual is `[RES-O1-NEEDS-C2]`. The sentences below still describe THIS predicate,
   which is deliberately left existential so that consumers at abstract carriers keep type-checking:**
   `compute/claim18_carrier/carrier_attacks.lean` measures exactly how much room the existential still
   has: the bundle is satisfiable by pure linear algebra at EVERY carrier pair with a dimension drop
   (`carrier_clauses_land_by_linear_algebra`, sorry-free, outside the package). That is a fact about
   this statement, and it is the reason the positive exhibits are kept out of the tree.
3. **The kernel is only pinned to be NONZERO, not to be `N(Q′)`.** `¬ Function.Injective Qc` says
   `ker Qc ≠ ⊥`; identifying that kernel with the fluctuation subspace this tree's `PoincareBridge`
   is about needs the subspace as a PARAMETER, ~~which needs `𝒬_c`~~ **(S75, 2026-07-27: `𝒬_c` is now
   available — `QcEquation.qcOp` — so this is no longer blocked by a missing object; what is not done
   here is the IDENTIFICATION of `ker QcEquation.qcOp` with `PoincareBridge`'s fluctuation subspace,
   which is a separate statement about two named objects, not a residual of this module)**. Naming it
   here as a `Submodule`
   field would be free data (the witness would pick its own kernel and then "identify" it), i.e. S91,
   so it is not done.

## What is IN this module and what is deliberately NOT

IN: the definition, the STRUCTURAL theorems (what the clauses force), and every NEGATIVE junk block.
NOT: any positive inhabitation. Per `Spine.lean` §3b.1's standing doctrine — *"a positive witness
against the repaired statement would be a hole next to `main`, so the one that DOES land is kept out
of the package"* — all landing witnesses live in `compute/claim18_carrier/carrier_attacks.lean`,
compiled and sorry-free, outside the package. Nothing in this file can discharge
`Spine.claim18_exists`.
-/

namespace AdalyFormal.Balaban.Claim18Carrier

open ContinuousLinearMap

variable {Hfine Hcoarse : Type*}
  [NormedAddCommGroup Hfine] [NormedSpace ℝ Hfine]
  [NormedAddCommGroup Hcoarse] [NormedSpace ℝ Hcoarse]

/-! ## §1 — the bundle -/

/-- **Claim 18's clause bundle at the two-space carrier.** `Qc : Hfine →L[ℝ] Hcoarse` is the coarse
average, `Qc_inv : Hcoarse →L[ℝ] Hfine` its section, `C2 : Hfine →L[ℝ] Hfine` Bałaban's `C⁽²⁾`, and
the transfer operator is `D̃⁽²⁾ = C2 ∘L Qc_inv : Hcoarse →L[ℝ] Hfine`. See the module docstring for
the clause-by-clause diff against `Spine.Claim18Clauses` and the provenance of each change. -/
def Clauses (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    (C2 : Hfine →L[ℝ] Hfine) (Qc : Hfine →L[ℝ] Hcoarse) (Qc_inv : Hcoarse →L[ℝ] Hfine) : Prop :=
  -- 1. `Qc_inv` is a genuine SECTION of the coarse average (kills the ZERO `Qc_inv`).
  Qc ∘L Qc_inv = ContinuousLinearMap.id ℝ Hcoarse ∧
  -- 2. the prescribed minimum, retained visibly (implied by 1; insufficient alone).
  Function.Injective Qc_inv ∧
  -- 3. the FAITHFUL absolute block-average bound, CMP98 p.36 (126).
  ‖Qc‖ ≤ 1 + Ccorr * L ^ 2 * α₀ ∧
  -- 4. non-degeneracy: the anti-shrink floor on `C2` (guarded, it is false at `Hfine = 0`), and
  --    GENUINE COARSENING — `Qc` is not injective, i.e. it kills a nonzero fluctuation.
  ((1 ≤ Module.finrank ℝ Hfine → 1 ≤ ‖C2‖) ∧ ¬ Function.Injective Qc) ∧
  -- 5. Claim 18's transfer bound, at Bałaban's own constant, ℝ exponent (Spine §3d).
  ‖C2 ∘L Qc_inv‖ ≤ L ^ ((d : ℝ) - 1) ∧
  -- 6. the transfer operator is not the zero operator.
  C2 ∘L Qc_inv ≠ 0

/-- **Clauses 1-5 only** — the bundle WITHOUT the transfer non-degeneracy, kept so that clause 6's
load-bearingness is a measurement and not a claim: `compute/claim18_carrier/carrier_attacks.lean`
compiles a witness for THIS predicate whose transfer operator is `0`. -/
def ClausesWithoutTransferNondegeneracy (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    (C2 : Hfine →L[ℝ] Hfine) (Qc : Hfine →L[ℝ] Hcoarse) (Qc_inv : Hcoarse →L[ℝ] Hfine) : Prop :=
  Qc ∘L Qc_inv = ContinuousLinearMap.id ℝ Hcoarse ∧
  Function.Injective Qc_inv ∧
  ‖Qc‖ ≤ 1 + Ccorr * L ^ 2 * α₀ ∧
  ((1 ≤ Module.finrank ℝ Hfine → 1 ≤ ‖C2‖) ∧ ¬ Function.Injective Qc) ∧
  ‖C2 ∘L Qc_inv‖ ≤ L ^ ((d : ℝ) - 1)

/-- The full bundle is strictly stronger than the clause-1-5 bundle — the direction that makes
clause 6 an ADDED demand rather than a restatement. -/
theorem clauses_imp_without_transferNondegeneracy (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (h : Clauses L d Ccorr α₀ C2 Qc Qc_inv) :
    ClausesWithoutTransferNondegeneracy L d Ccorr α₀ C2 Qc Qc_inv :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

#print axioms clauses_imp_without_transferNondegeneracy

/-! ## §2 — what clause 1 does and does NOT force at two spaces -/

/-- Applying a section pointwise. -/
theorem section_apply {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (hsec : Qc ∘L Qc_inv = ContinuousLinearMap.id ℝ Hcoarse) (v : Hcoarse) :
    Qc (Qc_inv v) = v := by
  have h : (Qc ∘L Qc_inv) v = v := by rw [hsec]; rfl
  simpa using h

/-- **Clause 1 forces `Qc` SURJECTIVE** — the half of the single-carrier obstruction that survives
the carrier change. -/
theorem section_forces_surjective {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (hsec : Qc ∘L Qc_inv = ContinuousLinearMap.id ℝ Hcoarse) : Function.Surjective Qc :=
  fun v => ⟨Qc_inv v, section_apply hsec v⟩

/-- Clause 1 forces `Qc_inv` injective (clause 2 is implied, and retained visibly). -/
theorem section_forces_inv_injective {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (hsec : Qc ∘L Qc_inv = ContinuousLinearMap.id ℝ Hcoarse) : Function.Injective Qc_inv := by
  intro u v huv
  have h1 : Qc (Qc_inv u) = Qc (Qc_inv v) := by rw [huv]
  rw [section_apply hsec u, section_apply hsec v] at h1
  exact h1

/-- **THE CARRIER CHANGE, AS THE ONE THEOREM IT AMOUNTS TO.** `Spine.claim18_carrier_obstruction`
proves that at ONE finite-dimensional space a section forces `Qc` injective, which is inconsistent
with `Qc` being a genuine coarse average. Here the same clause 1 leaves non-injectivity available,
and the price is exactly a dimension drop: the clauses FORCE `finrank Hcoarse < finrank Hfine`.
So "genuine coarsening" is not an extra assumption bolted on — it is a consequence of the bundle. -/
theorem forces_dimension_drop [FiniteDimensional ℝ Hfine] (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (h : Clauses L d Ccorr α₀ C2 Qc Qc_inv) :
    Module.finrank ℝ Hcoarse < Module.finrank ℝ Hfine := by
  obtain ⟨hsec, -, -, ⟨-, hnoninj⟩, -, -⟩ := h
  have hsurj : Function.Surjective ((Qc : Hfine →ₗ[ℝ] Hcoarse)) := section_forces_surjective hsec
  have hrange : LinearMap.range (Qc : Hfine →ₗ[ℝ] Hcoarse) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hker : LinearMap.ker (Qc : Hfine →ₗ[ℝ] Hcoarse) ≠ ⊥ := by
    intro hb
    exact hnoninj (LinearMap.ker_eq_bot.mp hb)
  have hkerpos : 0 < Module.finrank ℝ (LinearMap.ker (Qc : Hfine →ₗ[ℝ] Hcoarse)) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℝ (LinearMap.ker (Qc : Hfine →ₗ[ℝ] Hcoarse))) with
      hz | hp
    · exact absurd (Submodule.finrank_eq_zero.mp hz) hker
    · exact hp
  have hrk := LinearMap.finrank_range_add_finrank_ker (Qc : Hfine →ₗ[ℝ] Hcoarse)
  rw [hrange] at hrk
  rw [finrank_top] at hrk
  omega

#print axioms forces_dimension_drop

/-- **THE `Hcoarse := Hfine` COLLAPSE IS BLOCKED, PROVED.** Any carrier pair WITHOUT a strict
dimension drop makes the bundle unsatisfiable — in particular taking the coarse space to be the fine
space itself (the degenerate instantiation the single-carrier encoding was), or any pair related by a
linear isomorphism. This is the compiled answer to the first junk attack on the new statement. -/
theorem unsatisfiable_of_no_dimension_drop [FiniteDimensional ℝ Hfine]
    (hdim : Module.finrank ℝ Hfine ≤ Module.finrank ℝ Hcoarse)
    (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ) :
    ¬ ∃ (C2 : Hfine →L[ℝ] Hfine) (Qc : Hfine →L[ℝ] Hcoarse) (Qc_inv : Hcoarse →L[ℝ] Hfine),
        Clauses L d Ccorr α₀ C2 Qc Qc_inv := by
  rintro ⟨C2, Qc, Qc_inv, h⟩
  have := forces_dimension_drop L d Ccorr α₀ h
  omega

/-- **The single-carrier encoding is still empty — now for a REASON INTERNAL TO THIS BUNDLE**, with
no reference to clause 3's exponent, no squeeze, and no `α₀ = 0`. `Spine`'s
`claim18_corrected_unsatisfiable_at_zero_field_nontrivial` gets the same emptiness at `H →L[ℝ] H`
from the norm squeeze; this gets it from the dimensions alone, at EVERY `L`, `d`, `Ccorr`, `α₀`. Two
independent proofs of the same emptiness, which is why "the defect was the carrier" is a measurement
rather than a story. -/
theorem unsatisfiable_at_single_carrier {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ) :
    ¬ ∃ (C2 Qc Qc_inv : H →L[ℝ] H), Clauses L d Ccorr α₀ C2 Qc Qc_inv :=
  unsatisfiable_of_no_dimension_drop (le_refl _) L d Ccorr α₀

#print axioms unsatisfiable_at_single_carrier

/-- **THE STEP THE SINGLE-CARRIER SQUEEZE NEEDED IS PROVABLY UNAVAILABLE HERE.**
`Spine.claim18_section_forces_two_sided` derives `Qc_inv ∘L Qc = id` from clause 1 at one space, and
`Spine.claim18_corrected_norm_squeeze` uses exactly that to factor `C2 = (C2 ∘L Qc_inv) ∘L Qc` and
cap `‖C2‖`. At two spaces the bundle IMPLIES THE NEGATION of that step, so the squeeze does not
merely fail to go through — it is refuted. -/
theorem two_sided_step_unavailable (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (h : Clauses L d Ccorr α₀ C2 Qc Qc_inv) :
    Qc_inv ∘L Qc ≠ ContinuousLinearMap.id ℝ Hfine := by
  intro hid
  refine h.2.2.2.1.2 ?_
  intro x y hxy
  have hx : (Qc_inv ∘L Qc) x = x := by rw [hid]; rfl
  have hy : (Qc_inv ∘L Qc) y = y := by rw [hid]; rfl
  have : Qc_inv (Qc x) = Qc_inv (Qc y) := by rw [hxy]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hx hy
  rw [hx, hy] at this
  exact this

#print axioms two_sided_step_unavailable

/-- **THE CLAUSE THAT WAS CONTRADICTORY AT ONE SPACE IS A THEOREM AT TWO.**
`Spine.claim18_nonInvertible_strengthening_unsatisfiable` proves that ADDING
`Qc_inv ∘L Qc ≠ id` — the one clause distinguishing Bałaban's `𝒬_c` from a rescaled isometry — makes
the single-carrier bundle UNSATISFIABLE. Here it needs no adding: it is `two_sided_step_unavailable`,
implied by the bundle. That inversion is the whole content of `[RES-CLAIM18-CARRIER]`. -/
theorem nonInvertibility_now_implied (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ) :
    ∀ {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine},
      Clauses L d Ccorr α₀ C2 Qc Qc_inv →
        (Qc ∘L Qc_inv = ContinuousLinearMap.id ℝ Hcoarse ∧
          Qc_inv ∘L Qc ≠ ContinuousLinearMap.id ℝ Hfine) :=
  fun h => ⟨h.1, two_sided_step_unavailable L d Ccorr α₀ h⟩

/-- **WHAT SURVIVES OF THE SQUEEZE, STATED SHARPLY.** Clauses 3 and 5 still cap `C2` — but only on
`range Qc_inv`, through the projection `Qc_inv ∘L Qc`. `‖C2‖` itself is uncapped because `C2` is free
on `ker Qc`, and `ker Qc ≠ ⊥` is exactly what clause 4 now demands. So the single-carrier
contradiction with `1 ≤ ‖C2‖` is not patched over; it has no premise left. -/
theorem squeeze_only_on_range (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (h : Clauses L d Ccorr α₀ C2 Qc Qc_inv) :
    ‖C2 ∘L (Qc_inv ∘L Qc)‖ ≤ L ^ ((d : ℝ) - 1) * (1 + Ccorr * L ^ 2 * α₀) := by
  obtain ⟨-, -, hscale, -, hbound, -⟩ := h
  have hfac : C2 ∘L (Qc_inv ∘L Qc) = (C2 ∘L Qc_inv) ∘L Qc := by
    rw [ContinuousLinearMap.comp_assoc]
  rw [hfac]
  exact le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
    (mul_le_mul hbound hscale (norm_nonneg _) (le_trans (norm_nonneg _) hbound))

#print axioms squeeze_only_on_range

/-! ## §3 — the junk witnesses, all BLOCKED and all NEGATIVE

Every theorem in this section is a negation, so none of them can inhabit anything. The witnesses are
exactly the classes that killed the single-carrier bundle three times (zero, identity, rescaled
isometry) plus the two classes the carrier change newly makes available (a degenerate carrier pair,
and a zero transfer). -/

/-- **JUNK 1 — the ZERO section dies**, at every nontrivial coarse space, for every `C2`, `Qc`, `L`,
`d`, `Ccorr`, `α₀`: `Qc ∘L 0 = 0 ≠ id`. -/
theorem blocks_zero_Qc_inv [Nontrivial Hcoarse] (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    (C2 : Hfine →L[ℝ] Hfine) (Qc : Hfine →L[ℝ] Hcoarse) :
    ¬ Clauses L d Ccorr α₀ C2 Qc 0 := by
  rintro ⟨hsec, -, -, -, -, -⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Hcoarse)
  have h0 : (Qc ∘L (0 : Hcoarse →L[ℝ] Hfine)) v = v := by rw [hsec]; rfl
  rw [ContinuousLinearMap.comp_zero] at h0
  simp only [ContinuousLinearMap.zero_apply] at h0
  exact hv h0.symm

/-- **JUNK 2 — the ZERO `C2` dies** by clause 6, for every `Qc`, `Qc_inv`, at every carrier. -/
theorem blocks_zero_C2 (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    (Qc : Hfine →L[ℝ] Hcoarse) (Qc_inv : Hcoarse →L[ℝ] Hfine) :
    ¬ Clauses L d Ccorr α₀ 0 Qc Qc_inv := by
  rintro ⟨-, -, -, -, -, hne⟩
  exact hne (ContinuousLinearMap.zero_comp _)

/-- **JUNK 3 — EVERY INJECTIVE `Qc` DIES, in one clause.** This single theorem kills the identity
witness (at any carrier where `id` is typable), every linear isometry, every rescaled isometry
`s • R` with `s ≠ 0`, and every isomorphism — the whole family that survived at the single carrier and
that clause 4's non-scalarity proxy could only reach case by case. -/
theorem blocks_injective_Qc (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (hinj : Function.Injective Qc) : ¬ Clauses L d Ccorr α₀ C2 Qc Qc_inv := by
  rintro ⟨-, -, -, ⟨-, hnoninj⟩, -, -⟩
  exact hnoninj hinj

/-- **JUNK 3a — the RESCALED-ISOMETRY family, spelled out at the new carrier.** `s • R` for a linear
isometry equivalence `R` and `s ≠ 0` is injective, so it dies by `blocks_injective_Qc`. At `s = 0`
it dies by clause 1 instead (`blocks_zero_Qc`, below), so the family is dead for every `s`. -/
theorem blocks_scaled_isometry_equiv [Nontrivial Hcoarse] (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    (R : Hfine ≃ₗᵢ[ℝ] Hcoarse) (s : ℝ) (hs : s ≠ 0)
    (C2 : Hfine →L[ℝ] Hfine) (Qc_inv : Hcoarse →L[ℝ] Hfine) :
    ¬ Clauses L d Ccorr α₀ C2
        (s • (R.toLinearIsometry.toContinuousLinearMap : Hfine →L[ℝ] Hcoarse)) Qc_inv := by
  refine blocks_injective_Qc L d Ccorr α₀ ?_
  intro x y hxy
  simp only [ContinuousLinearMap.smul_apply] at hxy
  have h1 : R x = R y := smul_right_injective Hcoarse hs hxy
  exact R.injective h1

/-- **JUNK 3b — the ZERO `Qc` dies** by clause 1, at every nontrivial coarse space. Together with
`blocks_scaled_isometry_equiv` this closes the rescaled-isometry family at every scalar. -/
theorem blocks_zero_Qc [Nontrivial Hcoarse] (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    (C2 : Hfine →L[ℝ] Hfine) (Qc_inv : Hcoarse →L[ℝ] Hfine) :
    ¬ Clauses L d Ccorr α₀ C2 0 Qc_inv := by
  rintro ⟨hsec, -, -, -, -, -⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Hcoarse)
  have h0 : ((0 : Hfine →L[ℝ] Hcoarse) ∘L Qc_inv) v = v := by rw [hsec]; rfl
  rw [ContinuousLinearMap.zero_comp] at h0
  simp only [ContinuousLinearMap.zero_apply] at h0
  exact hv h0.symm

/-- **JUNK 4 — the ZERO-TRANSFER family dies**: any `C2` annihilating `range Qc_inv` fails clause 6.
This is the class the carrier change newly opens (`C2` can be large on `ker Qc` and vanish on
`range Qc_inv`, keeping `1 ≤ ‖C2‖` while the transfer is `0`), and it is the reason clause 6 exists.
`compute/claim18_carrier/carrier_attacks.lean` compiles a witness proving it LANDS against
`ClausesWithoutTransferNondegeneracy`, so this block is not shadow-boxing. -/
theorem blocks_zero_transfer (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (hz : C2 ∘L Qc_inv = 0) : ¬ Clauses L d Ccorr α₀ C2 Qc Qc_inv := by
  rintro ⟨-, -, -, -, -, hne⟩
  exact hne hz

/-- **JUNK 5 — a TRIVIAL coarse space dies.** If the coarse space is a point, every map out of it is
`0`, so the transfer is `0` and clause 6 fails. Consequence: the bundle FORCES a nontrivial coarse
space, without that being assumed anywhere. -/
theorem blocks_subsingleton_coarse [Subsingleton Hcoarse] (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    (C2 : Hfine →L[ℝ] Hfine) (Qc : Hfine →L[ℝ] Hcoarse) (Qc_inv : Hcoarse →L[ℝ] Hfine) :
    ¬ Clauses L d Ccorr α₀ C2 Qc Qc_inv := by
  rintro ⟨-, -, -, -, -, hne⟩
  refine hne ?_
  ext v
  have hv : v = 0 := Subsingleton.elim v 0
  rw [hv]
  simp

#print axioms blocks_subsingleton_coarse

/-! ## §4 — what the bundle FORCES about the carrier (the degenerate points, enumerated) -/

/-- The bundle forces the coarse space to be nontrivial — derived from clause 6, not assumed. -/
theorem forces_nontrivial_coarse (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (h : Clauses L d Ccorr α₀ C2 Qc Qc_inv) : Nontrivial Hcoarse := by
  by_contra hcon
  have : Subsingleton Hcoarse := not_nontrivial_iff_subsingleton.mp hcon
  exact blocks_subsingleton_coarse L d Ccorr α₀ C2 Qc Qc_inv h

/-- **`finrank ℝ Hfine ≤ 1` IS BLOCKED** — the `§DEGEN` low-dimension point where the single-carrier
clause 4 had nothing to say (`Spine.claim18_nonScalar_vacuous_at_finrank_one`). Here it is not a
weak point but an empty one: the bundle forces `2 ≤ finrank ℝ Hfine`, because it forces both a
nonzero kernel and a nontrivial (hence at least 1-dimensional) coarse image. -/
theorem forces_two_le_finrank_fine [FiniteDimensional ℝ Hfine] (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (h : Clauses L d Ccorr α₀ C2 Qc Qc_inv) : 2 ≤ Module.finrank ℝ Hfine := by
  have hdrop := forces_dimension_drop L d Ccorr α₀ h
  haveI := forces_nontrivial_coarse L d Ccorr α₀ h
  haveI : FiniteDimensional ℝ Hcoarse :=
    Module.Finite.of_surjective (Qc : Hfine →ₗ[ℝ] Hcoarse) (section_forces_surjective h.1)
  have hpos : 0 < Module.finrank ℝ Hcoarse := Module.finrank_pos
  omega

#print axioms forces_two_le_finrank_fine

/-- **The bundle is empty at `finrank ℝ Hfine ≤ 1`** — the corollary in the form a junk attack
meets it. -/
theorem unsatisfiable_at_finrank_fine_le_one [FiniteDimensional ℝ Hfine]
    (hfr : Module.finrank ℝ Hfine ≤ 1) (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ) :
    ¬ ∃ (C2 : Hfine →L[ℝ] Hfine) (Qc : Hfine →L[ℝ] Hcoarse) (Qc_inv : Hcoarse →L[ℝ] Hfine),
        Clauses L d Ccorr α₀ C2 Qc Qc_inv := by
  rintro ⟨C2, Qc, Qc_inv, h⟩
  have := forces_two_le_finrank_fine L d Ccorr α₀ h
  omega

/-- The transfer operator is injective on nothing in particular — but it IS nonzero, and its
factorization through the section is recorded, so consumers read the same object Claim 18 names. -/
theorem transfer_ne_zero (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (h : Clauses L d Ccorr α₀ C2 Qc Qc_inv) : C2 ∘L Qc_inv ≠ 0 := h.2.2.2.2.2

/-- Claim 18's transfer bound, projected — the clause consumers actually use. -/
theorem transfer_norm_bound (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (h : Clauses L d Ccorr α₀ C2 Qc Qc_inv) : ‖C2 ∘L Qc_inv‖ ≤ L ^ ((d : ℝ) - 1) :=
  h.2.2.2.2.1

/-- The block-average bound, projected. -/
theorem blockScale_bound (L : ℝ) (d : ℕ) (Ccorr α₀ : ℝ)
    {C2 : Hfine →L[ℝ] Hfine} {Qc : Hfine →L[ℝ] Hcoarse} {Qc_inv : Hcoarse →L[ℝ] Hfine}
    (h : Clauses L d Ccorr α₀ C2 Qc Qc_inv) : ‖Qc‖ ≤ 1 + Ccorr * L ^ 2 * α₀ :=
  h.2.2.1

end AdalyFormal.Balaban.Claim18Carrier
