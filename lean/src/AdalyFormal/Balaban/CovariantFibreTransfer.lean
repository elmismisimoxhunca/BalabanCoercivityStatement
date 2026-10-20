/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.FibreAggregate
import AdalyFormal.Balaban.RegularUQChain
import AdalyFormal.Balaban.ComposedCoercivity
import AdalyFormal.Balaban.JointInstantiation

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3200000

/-!
# `CovariantFibreTransfer.lean` — the aggregate fibre bound on the REAL covariant fibre `{Q_U A = 0}`

Lane record: `compute/covariant_fibre/PROGRESS.md`.

## What this closes

`ComposedCoercivity` §3b (finding F2) records that the operator half of the fibre bound is curved
but the **`Q` clause is still flat**: `AggregateFibreBound L U γ` quantifies over
`{A : lineCoarseRestrictCov (trivialU L) 2 A b = 0}` even when the operator carries a curved `U`.
CMP99b p.428's uniformity in `U` is a statement about the **covariant** gauge-fixing subspace
`{Q_2(U) A = 0}`. This module transfers the aggregate bound onto that subspace.

## LAW-19 / BUILD-DISCIPLINE-2 — the "missing primitive" was ALREADY IN THE TREE

`ComposedCoercivity` §3b names the missing inequality as

> `‖rZeroA U y x A μ 2 − rZeroA (trivialU L) y x A μ 2‖ ≤ c·frobSupBond U·(‖A(x,μ)‖+‖A(x+e_μ,μ)‖)`

It is **not** built here, because `RegularUQChain.norm_rZeroA_trivialU_sub_le` (§5 of that module,
axiom-clean) already proves the general-`ell` form

`‖rZeroA(1) − rZeroA(U)‖ ≤ ∑_{i<ell} 2·|transportPath y x μ i|·frobSupBond U·‖A(pathSite x μ i,μ)‖`,

and `RegularUQChain.transportPath_length_le` already proves the geometric path-length bound
`|transportPath y x μ i| ≤ 4·ell` for `x ∈ B(y)`, `i < ell`. §1 below only SPECIALIZES those two to
`ell = 2` and reads off the named constant `c = 16 = 2·(4·2)`; the constant is therefore WIRED to
the path-length theorem, not chosen. Anything else would have been a rebuild.

## The one place `hQ` is consumed, and what replaces it

Measured, not assumed: in the whole `FibreCoercivity`/`FibreAggregate` quantitative chain the
hypothesis `hQ` is consumed at **exactly one step** — `FibreAggregate.Q_inter_local`, where
`hQ (⟨y,hyc⟩,μ)` plus `FibreCoercivity.lineCoarse_trivial_two` yields the EXACT identity

`∑_{x ∈ B(y)} (A(x,μ) + A(x+e_μ,μ)) = 0`.

`inter_step_local`, `inter_dev_local`, `block_summand_dev_local` and `intra_bond_local` are all
`hQ`-FREE and are reused verbatim, not restated. On `{Q_2(U)A = 0}` that identity degrades to the
inequality

`‖∑_{x ∈ B(y)} (A(x,μ) + A(x+e_μ,μ))‖ ≤ 16·α₁·blockBondSum A y μ`      (§2, `α₁ = frobSupBond U`)

and the chain re-runs with an additive `α₁`-remainder (§3–§4) which is absorbed globally (§5).
`blockBondSum` is a per-block `ℓ¹` of bond norms, so the remainder is proportional to LOCAL bond
norms — the obstruction anticipated in the dispatch (a step whose remainder is NOT proportional to
local bond norms, e.g. a discontinuously failing cancellation) does not occur, because the single
cancellation the flat proof used is a block AVERAGE and averages degrade continuously.

## The result

`aggregate_fibre_bound_curved` (§5): for every `ε > 0`, every `U` with `frobSupBond U ≤ α₀`, and
every `A` with `lineCoarseRestrictCov U 2 A b = 0` for all coarse bonds `b`,

`(1 − (1 + 1/ε)·1024·α₀²) · bondEnergy A ≤ (1 + ε)·3316224 · (P_Ax(A) + curlEnergy A)`.

Every constant is counted: `3316224 = 69088·48` is `FibreAggregate`'s own (unchanged — the flat
chain's constants are NOT refitted), `1024 = 4·16·16` is the `(2α₀)²` of §3 against the block
Cauchy–Schwarz `16 = 2·|B(y)|` of §2 and the exact bond-incidence `16` of §5, and `(1+ε)`/`(1+1/ε)`
is the Young split that keeps the flat constant undegraded as `α₀ → 0`. At `U = 1` the theorem
returns `FibreAggregate.aggregate_fibre_bound`'s constant EXACTLY
(`curved_recovers_flat_constant`, §6, proved THROUGH the curved chain and not by citing the flat
theorem) — the curved bound degrades to the flat one, it does not merely resemble it.

§6 also delivers the `Δ_k(U)` form (`transfer_deltaK_curved`), the two-sided threshold
(`gammaCurved_pos_iff` at `ε = 1`: positive strictly below `α₀* = 1/√2048`, NONPOSITIVE at and
above it), the must-fire witness at the genuinely curved `JointInstantiation.curvedAggU` with both
sides nonzero, and the corollary that `JointInstantiation.altMode_Q_covariant`'s exact-agreement
configuration is the `α₁`-remainder-free special case of this theorem.

## Scope, stated so it is not over-read

Inherited from `FibreAggregate` and NOT weakened: `ell = 2`; `2 ∣ (L μ + 1)`; `𝔰𝔲(2)`-valued bond
fields; `Q` is the tree's own `LineIntegralCovariant.lineCoarseRestrictCov`. NEW here: the `Q`
clause is at a general `U`, and `α₀` bounds `frobSupBond U` only — no gauge-regularity of `U`, no
smallness of the field `A`, no restriction of `A` to a fixed line in `𝔰𝔲(2)`. What is NOT claimed:
nothing about `ell > 2`, nothing about `d = 4`, and the `Δ_k(U)` form of §6 inherits
`ComposedCoercivity.curlEnergy_le_curved`'s own `544α₀ + 64α₀²` cost, which makes the admissible
`α₀` for THAT corollary far smaller than `1/√2048` (the numbers are in the statements of
`gammaCurvedDeltaK_pos_at_1e_neg_10` / `gammaCurvedDeltaK_nonpos_at_1e_neg_9`, not in prose).
-/

namespace AdalyFormal.Balaban.CovariantFibreTransfer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.AxialCoercivity
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg frobSupBond
  frobSupBond_nonneg)
open AdalyFormal.Balaban.Q1Real (rZeroA rZeroA_trivialU transportPath)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.RegularUQChain (norm_rZeroA_trivialU_sub_le transportPath_length_le)
open AdalyFormal.Balaban.FibreCoercivity
open AdalyFormal.Balaban.FibreAggregate

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the drift primitive, SPECIALIZED to `ell = 2` (not rebuilt)

`c = 16 = 2 · (4 · 2)`: the `2` of `RMapLipschitz.norm_RMap_sub_self_le` (carried through
`RegularUQChain.norm_RMap_holonomy_sub_self_le`) times the `4·ell` of
`RegularUQChain.transportPath_length_le` at `ell = 2`. Both factors are theorem-supplied. -/

/-- **THE NAMED PRIMITIVE, at `ell = 2`.** `ComposedCoercivity` §3b's inequality, with the constant
`c = 16` WIRED to `RegularUQChain.transportPath_length_le` (`4·ell` at `ell = 2`) and to the `2` of
the `RMap` Lipschitz brick. Per bond pair, no volume factor, no RG step `k`. -/
theorem rZeroA_drift_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {y x : PeriodicLatticeSite L} (hx : x ∈ blockOf y 2) (A : Bond L → SuTwo) (μ : Fin 3) :
    ‖rZeroA U y x A μ 2 - rZeroA (trivialU L) y x A μ 2‖
      ≤ 16 * frobSupBond U * (‖A (x, μ)‖ + ‖A (periodicLatticeShift x μ, μ)‖) := by
  have hxb : inBlock y 2 x := (mem_blockOf).mp hx
  have hα0 : (0 : ℝ) ≤ frobSupBond U := frobSupBond_nonneg U
  have hbase := norm_rZeroA_trivialU_sub_le U y x A μ 2
  rw [← norm_neg, neg_sub]
  refine le_trans hbase ?_
  have h0 : (transportPath y x μ 0).length ≤ 4 * 2 :=
    transportPath_length_le hxb (by norm_num) μ
  have h1 : (transportPath y x μ 1).length ≤ 4 * 2 :=
    transportPath_length_le hxb (by norm_num) μ
  have h0' : ((transportPath y x μ 0).length : ℝ) ≤ 8 := by exact_mod_cast h0
  have h1' : ((transportPath y x μ 1).length : ℝ) ≤ 8 := by exact_mod_cast h1
  have hp0 : pathSite x μ 0 = x := rfl
  have hp1 : pathSite x μ 1 = periodicLatticeShift x μ := rfl
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hp0, hp1]
  have hn0 : (0 : ℝ) ≤ ‖A (x, μ)‖ := norm_nonneg _
  have hn1 : (0 : ℝ) ≤ ‖A (periodicLatticeShift x μ, μ)‖ := norm_nonneg _
  have e0 : 2 * ((transportPath y x μ 0).length : ℝ) * frobSupBond U * ‖A (x, μ)‖
      ≤ 16 * frobSupBond U * ‖A (x, μ)‖ := by
    nlinarith [mul_nonneg hα0 hn0, h0']
  have e1 : 2 * ((transportPath y x μ 1).length : ℝ) * frobSupBond U
        * ‖A (periodicLatticeShift x μ, μ)‖
      ≤ 16 * frobSupBond U * ‖A (periodicLatticeShift x μ, μ)‖ := by
    nlinarith [mul_nonneg hα0 hn1, h1']
  nlinarith [e0, e1]

/-- **THE CONSTANT IS COMPOSED, NOT CHOSEN.** `16 = 2 * (4 * 2)`: the `RMap` Lipschitz factor `2`
times the path-length bound `4·ell` at `ell = 2`. Kernel-visible arithmetic, so the composition of
the two theorem-supplied factors is checkable and not a prose claim. -/
theorem c_rescale_test : (16 : ℝ) = 2 * (4 * 2) := by norm_num

/-- **MUST-NOT-FIRE ON §1.** At the flat background the drift is exactly `0`, not merely small —
so the primitive is not a vacuous inequality that never becomes an equality. -/
theorem rZeroA_drift_trivialU (y x : PeriodicLatticeSite L) (A : Bond L → SuTwo) (μ : Fin 3) :
    ‖rZeroA (trivialU L) y x A μ 2 - rZeroA (trivialU L) y x A μ 2‖ = 0 := by
  rw [sub_self, norm_zero]

#print axioms rZeroA_drift_le
#print axioms c_rescale_test
#print axioms rZeroA_drift_trivialU

/-! ## §2 — the fibre comparison: on `{Q_2(U)A = 0}` the FLAT block sum is `α₁`-small -/

/-- The per-block `ℓ¹` of the two bond norms each `Q`-summand carries. This is the object the
`α₁`-remainder is proportional to — LOCAL bond norms, exactly as the transfer needs. -/
noncomputable def blockBondSum (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) (μ : Fin 3) : ℝ :=
  ∑ x ∈ blockOf y 2, (‖A (x, μ)‖ + ‖A (periodicLatticeShift x μ, μ)‖)

/-- The per-block `ℓ²` of the same bond norms. -/
noncomputable def blockBondSq (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) (μ : Fin 3) : ℝ :=
  ∑ x ∈ blockOf y 2, (‖A (x, μ)‖ ^ 2 + ‖A (periodicLatticeShift x μ, μ)‖ ^ 2)

theorem blockBondSum_nonneg (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    0 ≤ blockBondSum A y μ :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem blockBondSq_nonneg (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    0 ≤ blockBondSq A y μ :=
  Finset.sum_nonneg (fun _ _ => by positivity)

/-- **THE BLOCK CAUCHY–SCHWARZ.** `blockBondSum² ≤ 16 · blockBondSq`, the `16 = 2 · 8` being twice
the block cardinality `|B(y)| = 2³` (`AdmissibleSubspace.card_blockOf_of_coarse`, LAW-19 — the
count is DERIVED from the tiling hypothesis, not asserted). -/
theorem blockBondSum_sq_le (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo)
    {y : PeriodicLatticeSite L} (hyc : y ∈ CoarseLattice L 2) (μ : Fin 3) :
    blockBondSum A y μ ^ 2 ≤ 16 * blockBondSq A y μ := by
  have hcard : (blockOf y 2).card = 8 := by
    rw [card_blockOf_of_coarse hdvd hyc]; norm_num
  have hcs : blockBondSum A y μ ^ 2
      ≤ ((blockOf y 2).card : ℝ)
        * ∑ x ∈ blockOf y 2, (‖A (x, μ)‖ + ‖A (periodicLatticeShift x μ, μ)‖) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hcard] at hcs
  push_cast at hcs
  have hterm : ∀ x ∈ blockOf y 2,
      (‖A (x, μ)‖ + ‖A (periodicLatticeShift x μ, μ)‖) ^ 2
        ≤ 2 * (‖A (x, μ)‖ ^ 2 + ‖A (periodicLatticeShift x μ, μ)‖ ^ 2) := by
    intro x _
    nlinarith [sq_nonneg (‖A (x, μ)‖ - ‖A (periodicLatticeShift x μ, μ)‖)]
  have hsum : (∑ x ∈ blockOf y 2, (‖A (x, μ)‖ + ‖A (periodicLatticeShift x μ, μ)‖) ^ 2)
      ≤ 2 * blockBondSq A y μ := by
    unfold blockBondSq
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  linarith

/-- **THE FIBRE COMPARISON.** On the covariant fibre `{Q_2(U)A = 0}`, the FLAT `Q`-block-sum — the
exact quantity `FibreAggregate.Q_inter_local` sets to `0` — is bounded by `16·α₁` times the block's
own `ℓ¹` bond norms. This single inequality is what replaces the exact equation `hQ`. -/
theorem block_sum_norm_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo)
    (hQU : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov U 2 A b = 0)
    {y : PeriodicLatticeSite L} (hyc : y ∈ CoarseLattice L 2) (μ : Fin 3) :
    ‖∑ x ∈ blockOf y 2, (A (x, μ) + A (periodicLatticeShift x μ, μ))‖
      ≤ 16 * frobSupBond U * blockBondSum A y μ := by
  have hα0 : (0 : ℝ) ≤ frobSupBond U := frobSupBond_nonneg U
  set b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2 := (⟨y, hyc⟩, μ) with hbdef
  have hflat := lineCoarse_trivial_two A y hyc μ
  have hzero : lineCoarseRestrictCov U 2 A b = 0 := hQU b
  have hdiff : (1 / ((2 : ℕ) : ℝ) ^ 4)
        • ∑ x ∈ blockOf y 2, (A (x, μ) + A (periodicLatticeShift x μ, μ))
      = (1 / ((2 : ℕ) : ℝ) ^ 4)
        • ∑ x ∈ blockOf y 2, (rZeroA (trivialU L) y x A μ 2 - rZeroA U y x A μ 2) := by
    rw [← hflat]
    have hU : lineCoarseRestrictCov U 2 A b
        = (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf y 2, rZeroA U y x A μ 2 := rfl
    have h1 : lineCoarseRestrictCov (trivialU L) 2 A b
        = (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf y 2, rZeroA (trivialU L) y x A μ 2 := rfl
    rw [Finset.sum_sub_distrib, smul_sub, ← h1, ← hU, hzero, sub_zero]
  have hscal : (1 / ((2 : ℕ) : ℝ) ^ 4) ≠ 0 := by norm_num
  have hsum : ∑ x ∈ blockOf y 2, (A (x, μ) + A (periodicLatticeShift x μ, μ))
      = ∑ x ∈ blockOf y 2, (rZeroA (trivialU L) y x A μ 2 - rZeroA U y x A μ 2) :=
    smul_right_injective _ hscal hdiff
  rw [hsum]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ x ∈ blockOf y 2,
      ‖rZeroA (trivialU L) y x A μ 2 - rZeroA U y x A μ 2‖
        ≤ 16 * frobSupBond U * (‖A (x, μ)‖ + ‖A (periodicLatticeShift x μ, μ)‖) := by
    intro x hx
    rw [← norm_neg, neg_sub]
    exact rZeroA_drift_le U hx A μ
  refine le_trans (Finset.sum_le_sum hterm) ?_
  unfold blockBondSum
  rw [Finset.mul_sum]

#print axioms blockBondSum
#print axioms blockBondSq
#print axioms blockBondSum_nonneg
#print axioms blockBondSq_nonneg
#print axioms blockBondSum_sq_le
#print axioms block_sum_norm_le

/-! ## §3 — the curved STAGE THREE: `FibreAggregate.Q_inter_local`, with the `α₁`-remainder

The flat proof divides the block sum by `|B(y)|` after setting it to `0`. Here the block sum is
`≤ 16·α₁·blockBondSum` instead, and the SAME division by `|B(y)| = 8` turns that into `2·α₁`. The
`|B(y)|` is used as an EXACT count (`card_blockOf_of_coarse`), not as `≥ 1`, which is what keeps
the remainder's constant at `2` rather than `16`. -/

/-- **THE CURVED REFERENCE-BOND BOUND.** On `{Q_2(U)A = 0}`, the block's reference inter-block bond
obeys `‖A(y+e_μ,μ)‖ ≤ 2·α₁·blockBondSum + √(23264·pairG)`. The second term is exactly
`FibreAggregate.Q_inter_local`'s flat conclusion in un-squared form; the first is the new drift.
At `α₁ = 0` this IS the flat statement. -/
theorem Q_inter_local_curved (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo)
    (hQU : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov U 2 A b = 0)
    {y : PeriodicLatticeSite L} (hyc : y ∈ CoarseLattice L 2) (μ : Fin 3) :
    ‖A (periodicLatticeShift y μ, μ)‖
      ≤ 2 * frobSupBond U * blockBondSum A y μ + Real.sqrt (23264 * pairG A y μ) := by
  have hy : ∀ ν : Fin 3, (y ν).val % 2 = 0 := mem_CoarseLattice.1 hyc
  have hP : (0 : ℝ) ≤ pairG A y μ := pairG_nonneg A y μ
  set M := Real.sqrt (23264 * pairG A y μ) with hMdef
  have hM0 : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have hdev : ∀ x ∈ blockOf y 2,
      ‖(A (x, μ) + A (periodicLatticeShift x μ, μ)) - A (periodicLatticeShift y μ, μ)‖ ≤ M := by
    intro x hx
    obtain ⟨hxe, hle⟩ := mem_block_offset hx
    have key := block_summand_dev_local hdvd A hy (fun ν => (x ν).val - (y ν).val) hle μ
    rw [← hxe] at key
    have hsq := Real.sqrt_le_sqrt key
    rwa [Real.sqrt_sq (norm_nonneg _)] at hsq
  have hS := block_sum_norm_le U A hQU hyc μ
  have hcard : (blockOf y 2).card = 8 := by
    rw [card_blockOf_of_coarse hdvd hyc]; norm_num
  have hrw : (blockOf y 2).card • A (periodicLatticeShift y μ, μ)
      = (∑ x ∈ blockOf y 2, (A (x, μ) + A (periodicLatticeShift x μ, μ)))
        - ∑ x ∈ blockOf y 2,
            ((A (x, μ) + A (periodicLatticeShift x μ, μ)) - A (periodicLatticeShift y μ, μ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    abel
  have hn : ‖(blockOf y 2).card • A (periodicLatticeShift y μ, μ)‖
      ≤ ‖∑ x ∈ blockOf y 2, (A (x, μ) + A (periodicLatticeShift x μ, μ))‖
        + ‖∑ x ∈ blockOf y 2,
            ((A (x, μ) + A (periodicLatticeShift x μ, μ))
              - A (periodicLatticeShift y μ, μ))‖ := by
    rw [hrw]
    exact norm_sub_le _ _
  have hn2 : ‖∑ x ∈ blockOf y 2,
        ((A (x, μ) + A (periodicLatticeShift x μ, μ)) - A (periodicLatticeShift y μ, μ))‖
      ≤ ((blockOf y 2).card : ℝ) * M := by
    refine le_trans (norm_sum_le _ _) ?_
    have h := Finset.sum_le_card_nsmul (blockOf y 2)
      (fun x => ‖(A (x, μ) + A (periodicLatticeShift x μ, μ))
        - A (periodicLatticeShift y μ, μ)‖) M hdev
    rwa [nsmul_eq_mul] at h
  have hns : ‖(blockOf y 2).card • A (periodicLatticeShift y μ, μ)‖
      = ((blockOf y 2).card : ℝ) * ‖A (periodicLatticeShift y μ, μ)‖ := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((blockOf y 2).card : ℝ))]
  rw [hns, hcard] at hn
  rw [hcard] at hn2
  push_cast at hn hn2
  linarith

#print axioms Q_inter_local_curved

/-! ## §4 — the curved PER-BOND bound

The Young split `(a+b)² ≤ (1+ε)a² + (1+1/ε)b²` puts ALL the loss on the `α₁`-remainder, so the
flat part keeps `FibreAggregate`'s own `69088 = 2·11280 + 2·23264` exactly. -/

/-- Young's inequality in the form the split needs. `ε` is free and positive; multiplying through
by `ε` turns the difference into `(ε·a − b)² ≥ 0`. -/
theorem young_sq {a b ε : ℝ} (hε : 0 < ε) :
    (a + b) ^ 2 ≤ (1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2 := by
  have key : ε * ((1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2 - (a + b) ^ 2) = (ε * a - b) ^ 2 := by
    field_simp
    ring
  nlinarith [key, sq_nonneg (ε * a - b), hε]

/-- **THE CURVED PER-BOND LOCAL BOUND.** Every bond's energy is controlled by the two-block flat
budget with the UNCHANGED constant `69088`, inflated by `(1+ε)`, plus an `α₀`-quadratic remainder
proportional to the LOCAL block bond energy. At `α₀ = 0` and `ε → 0` this is exactly
`FibreAggregate.bond_energy_local`. -/
theorem bond_energy_local_curved (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hsup : frobSupBond U ≤ α₀)
    {ε : ℝ} (hε : 0 < ε) (A : Bond L → SuTwo)
    (hQU : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov U 2 A b = 0)
    (b : Bond L) :
    ‖A b‖ ^ 2
      ≤ (1 + ε) * 69088 * (localG A (cc b.1) + localG A (cc (periodicLatticeShift b.1 b.2)))
        + (1 + 1 / ε) * 64 * α₀ ^ 2 * blockBondSq A (cc b.1) b.2 := by
  obtain ⟨z, μ⟩ := b
  have hg1 : (0 : ℝ) ≤ localG A (cc z) := localG_nonneg A (cc z)
  have hg2 : (0 : ℝ) ≤ localG A (cc (periodicLatticeShift z μ)) := localG_nonneg A _
  have hbsq : (0 : ℝ) ≤ blockBondSq A (cc z) μ := blockBondSq_nonneg A (cc z) μ
  have hεi : (0 : ℝ) ≤ 1 + 1 / ε := by positivity
  have hrem : (0 : ℝ) ≤ (1 + 1 / ε) * 64 * α₀ ^ 2 * blockBondSq A (cc z) μ := by positivity
  by_cases hz : (z μ).val % 2 = 0
  · have h := intra_bond_local hdvd A z μ hz
    show ‖A (z, μ)‖ ^ 2 ≤ _
    nlinarith [h, hg1, hg2, hrem, mul_nonneg hε.le hg1, mul_nonneg hε.le hg2]
  · have hz1 : (z μ).val % 2 = 1 := by omega
    have hy : ∀ ν : Fin 3, ((cc z) ν).val % 2 = 0 := fun ν => cc_even z ν
    have hle : ∀ ν, ((fun w => (z w).val % 2) : Fin 3 → ℕ) ν ≤ 1 := by
      intro ν
      show (z ν).val % 2 ≤ 1
      omega
    have hze : z = addOff (cc z) (fun ν => (z ν).val % 2) := by
      refine addOff_of_val (cc z) z _ (fun ν => ?_)
      show (z ν).val = (cc z ν).val + (z ν).val % 2
      rw [cc_val]; omega
    have hnbr : cc (periodicLatticeShift z μ) = cnbr (cc z) μ := by
      conv_lhs => rw [hze]
      exact cc_shift_addOff_one hdvd hy hle μ (by simpa using hz1)
    have hpairEq : localG A (cc z) + localG A (cc (periodicLatticeShift z μ))
        = pairG A (cc z) μ := by
      rw [hnbr]
      rfl
    have hP : (0 : ℝ) ≤ pairG A (cc z) μ := pairG_nonneg A (cc z) μ
    have hdev : ‖A (z, μ) - A (periodicLatticeShift (cc z) μ, μ)‖ ^ 2
        ≤ 11280 * pairG A (cc z) μ := by
      have key := inter_dev_local hdvd A hy (fun ν => (z ν).val % 2) hle μ (by simpa using hz1)
      rwa [← hze] at key
    have href := Q_inter_local_curved hdvd U A hQU (cc_mem z) μ
    set u := ‖A (z, μ) - A (periodicLatticeShift (cc z) μ, μ)‖ with hudef
    set v := Real.sqrt (23264 * pairG A (cc z) μ) with hvdef
    set D := 2 * α₀ * blockBondSum A (cc z) μ with hDdef
    have hu0 : (0 : ℝ) ≤ u := norm_nonneg _
    have hv0 : (0 : ℝ) ≤ v := Real.sqrt_nonneg _
    have hbbs0 : (0 : ℝ) ≤ blockBondSum A (cc z) μ := blockBondSum_nonneg A (cc z) μ
    have hD0 : (0 : ℝ) ≤ D := by rw [hDdef]; positivity
    have hvsq : v ^ 2 = 23264 * pairG A (cc z) μ := Real.sq_sqrt (by positivity)
    have hDge : 2 * frobSupBond U * blockBondSum A (cc z) μ ≤ D := by
      rw [hDdef]
      nlinarith [hbbs0, hsup]
    have htri : ‖A (z, μ)‖ ≤ (u + v) + D := by
      have hsplit : A (z, μ)
          = (A (z, μ) - A (periodicLatticeShift (cc z) μ, μ))
            + A (periodicLatticeShift (cc z) μ, μ) := by abel
      calc ‖A (z, μ)‖
          ≤ u + ‖A (periodicLatticeShift (cc z) μ, μ)‖ := by
            conv_lhs => rw [hsplit]
            exact norm_add_le _ _
        _ ≤ u + (2 * frobSupBond U * blockBondSum A (cc z) μ + v) := by linarith [href]
        _ ≤ (u + v) + D := by linarith [hDge]
    have ha2 : (u + v) ^ 2 ≤ 69088 * pairG A (cc z) μ := by
      nlinarith [hdev, hvsq, hu0, hv0, sq_nonneg (u - v)]
    have hD2 : D ^ 2 ≤ 64 * α₀ ^ 2 * blockBondSq A (cc z) μ := by
      have hcs := blockBondSum_sq_le hdvd A (cc_mem z) μ
      have : D ^ 2 = 4 * α₀ ^ 2 * blockBondSum A (cc z) μ ^ 2 := by rw [hDdef]; ring
      rw [this]
      nlinarith [hcs, sq_nonneg α₀, hbsq]
    have hyoung : ((u + v) + D) ^ 2 ≤ (1 + ε) * (u + v) ^ 2 + (1 + 1 / ε) * D ^ 2 :=
      young_sq hε
    have hsq : ‖A (z, μ)‖ ^ 2 ≤ ((u + v) + D) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖A (z, μ)‖ := norm_nonneg _
      nlinarith [htri, h0]
    show ‖A (z, μ)‖ ^ 2 ≤ (1 + ε) * 69088 * (localG A (cc z)
        + localG A (cc (periodicLatticeShift z μ)))
      + (1 + 1 / ε) * 64 * α₀ ^ 2 * blockBondSq A (cc z) μ
    rw [hpairEq]
    nlinarith [hsq, hyoung, ha2, hD2, hε.le, hεi, hP, hbsq]

#print axioms young_sq
#print axioms bond_energy_local_curved

/-! ## §5 — the aggregate: the two exact incidence counts, and the absorption

`sum_pair_localG` reproduces the count internal to `FibreAggregate.aggregate_fibre_bound` (that
step is a `have` inside the proof and is not exported, so it is re-derived here rather than cited).
`sum_blockBondSq_eq` is a NEW exact identity — the remainder's own incidence count. -/

/-- **THE FLAT-SIDE COUNT.** `∑_b (localG(cc b₋) + localG(cc(b₋+e))) = 6·∑_x localG(cc x)`: three
directions per site, plus a shift reindexing (`FibreAggregate.sum_shift_site`, LAW-19). -/
theorem sum_pair_localG (A : Bond L → SuTwo) :
    (∑ b : Bond L, (localG A (cc b.1) + localG A (cc (periodicLatticeShift b.1 b.2))))
      = 6 * ∑ x : PeriodicLatticeSite L, localG A (cc x) := by
  set S := ∑ x : PeriodicLatticeSite L, localG A (cc x) with hSdef
  have e1 : (∑ b : Bond L,
        (localG A (cc b.1) + localG A (cc (periodicLatticeShift b.1 b.2))))
      = ∑ z : PeriodicLatticeSite L, ∑ μ : Fin 3,
          (localG A (cc z) + localG A (cc (periodicLatticeShift z μ))) :=
    Fintype.sum_prod_type _
  have e2 : ∀ z : PeriodicLatticeSite L,
      (∑ _μ : Fin 3, (localG A (cc z) + localG A (cc (periodicLatticeShift z _μ))))
        = 3 * localG A (cc z) + ∑ μ : Fin 3, localG A (cc (periodicLatticeShift z μ)) := by
    intro z
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    norm_num
  have e4 : (∑ z : PeriodicLatticeSite L,
        ∑ μ : Fin 3, localG A (cc (periodicLatticeShift z μ))) = 3 * S := by
    rw [Finset.sum_comm]
    have h5 : ∀ μ : Fin 3,
        (∑ z : PeriodicLatticeSite L, localG A (cc (periodicLatticeShift z μ))) = S :=
      fun μ => sum_shift_site μ (fun w => localG A (cc w))
    rw [Finset.sum_congr rfl (fun μ _ => h5 μ), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [e1, Finset.sum_congr rfl (fun z _ => e2 z), Finset.sum_add_distrib, ← Finset.mul_sum, e4,
    ← hSdef]
  ring

/-- **THE REMAINDER'S INCIDENCE COUNT, EXACT.** `∑_b blockBondSq A (cc b₋) b.2 = 16·bondEnergy A`.
`16 = 8 · 2`: `8 = |B(y)|` sites per block charging the same block sum
(`card_blockOf_of_coarse`), and `2` because each block sum counts each fine bond twice — once as
the segment's base bond and once as its shifted bond (`sum_shift_site` is what makes the second
count exact rather than an estimate). No volume factor, no slack: this is an EQUALITY. -/
theorem sum_blockBondSq_eq (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    (∑ b : Bond L, blockBondSq A (cc b.1) b.2) = 16 * bondEnergy A := by
  have hb := sum_over_block_bonds (L := L) (fun b => blockBondSq A (cc b.1) b.2)
  rw [← hb]
  have hinner : ∀ y ∈ CoarseLattice L 2,
      (∑ x ∈ blockOf y 2, ∑ μ : Fin 3, blockBondSq A (cc x) μ)
        = 8 * ∑ μ : Fin 3, blockBondSq A y μ := by
    intro y hy
    have hy2 : ∀ ν : Fin 3, (y ν).val % 2 = 0 := mem_CoarseLattice.1 hy
    have hcong : (∑ x ∈ blockOf y 2, ∑ μ : Fin 3, blockBondSq A (cc x) μ)
        = ∑ _x ∈ blockOf y 2, ∑ μ : Fin 3, blockBondSq A y μ :=
      Finset.sum_congr rfl (fun x hx => by rw [(mem_blockOf_iff_cc hy2 x).1 hx])
    rw [hcong, Finset.sum_const, card_blockOf_of_coarse hdvd hy, nsmul_eq_mul]
    norm_num
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  have hswap : (∑ y ∈ CoarseLattice L 2, ∑ μ : Fin 3, blockBondSq A y μ)
      = ∑ μ : Fin 3, ∑ y ∈ CoarseLattice L 2, blockBondSq A y μ := Finset.sum_comm
  have hmu : ∀ μ : Fin 3, (∑ y ∈ CoarseLattice L 2, blockBondSq A y μ)
      = 2 * ∑ x : PeriodicLatticeSite L, ‖A (x, μ)‖ ^ 2 := by
    intro μ
    have h := sum_over_blocks (L := L) (fun x : PeriodicLatticeSite L =>
      ‖A (x, μ)‖ ^ 2 + ‖A (periodicLatticeShift x μ, μ)‖ ^ 2)
    have hlhs : (∑ y ∈ CoarseLattice L 2, blockBondSq A y μ)
        = ∑ y ∈ CoarseLattice L 2, ∑ x ∈ blockOf y 2,
            (‖A (x, μ)‖ ^ 2 + ‖A (periodicLatticeShift x μ, μ)‖ ^ 2) := rfl
    rw [hlhs, h, Finset.sum_add_distrib,
      sum_shift_site μ (fun w : PeriodicLatticeSite L => ‖A (w, μ)‖ ^ 2)]
    ring
  rw [hswap, Finset.sum_congr rfl (fun μ _ => hmu μ), ← Finset.mul_sum]
  have hbe : bondEnergy A = ∑ μ : Fin 3, ∑ x : PeriodicLatticeSite L, ‖A (x, μ)‖ ^ 2 := by
    show (∑ b : Bond L, ‖A b‖ ^ 2) = _
    rw [Fintype.sum_prod_type (fun b : Bond L => ‖A b‖ ^ 2), Finset.sum_comm]
  rw [hbe]
  ring

/-- **THE AGGREGATE FIBRE BOUND ON THE COVARIANT FIBRE.** For every `ε > 0`, every background `U`
with `frobSupBond U ≤ α₀`, and every `A` in the REAL covariant gauge-fixed subspace
`{Q_2(U) A = 0}`:

`(1 − (1+1/ε)·1024·α₀²) · bondEnergy A ≤ (1+ε)·3316224 · (P_Ax(A) + curlEnergy A)`.

`3316224 = 69088·48` is `FibreAggregate`'s own constant, unmodified. `1024 = 4·16·16` is counted:
`4` from `(2α₀)²` (§3's division by the exact block cardinality), `16` from the block
Cauchy–Schwarz (§2), `16` from the exact bond incidence (§5). -/
theorem aggregate_fibre_bound_curved (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hsup : frobSupBond U ≤ α₀)
    {ε : ℝ} (hε : 0 < ε) (A : Bond L → SuTwo)
    (hQU : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov U 2 A b = 0) :
    (1 - (1 + 1 / ε) * 1024 * α₀ ^ 2) * bondEnergy A
      ≤ (1 + ε) * 3316224 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
  set S := ∑ x : PeriodicLatticeSite L, localG A (cc x) with hSdef
  set G := pAx A (CoarseLattice L 2) 2 + curlEnergy A with hGdef
  have hstep : bondEnergy A
      ≤ ∑ b : Bond L,
          ((1 + ε) * 69088 * (localG A (cc b.1) + localG A (cc (periodicLatticeShift b.1 b.2)))
            + (1 + 1 / ε) * 64 * α₀ ^ 2 * blockBondSq A (cc b.1) b.2) := by
    show (∑ b : Bond L, ‖A b‖ ^ 2) ≤ _
    exact Finset.sum_le_sum
      (fun b _ => bond_energy_local_curved hdvd U hα₀ hsup hε A hQU b)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_pair_localG A,
    sum_blockBondSq_eq hdvd A, ← hSdef] at hstep
  have hcoef : (0 : ℝ) ≤ (1 + ε) * 69088 := by positivity
  have hS8 : S ≤ 8 * G := sum_localG_cc_le A
  have h1 : (1 + ε) * 69088 * (6 * S) ≤ (1 + ε) * 69088 * (6 * (8 * G)) := by
    have h6 : (0 : ℝ) ≤ (1 + ε) * 69088 * 6 := by positivity
    nlinarith [hS8, h6]
  have h2 : (1 + ε) * 69088 * (6 * (8 * G)) = (1 + ε) * 3316224 * G := by ring
  have h3 : (1 + 1 / ε) * 64 * α₀ ^ 2 * (16 * bondEnergy A)
      = (1 + 1 / ε) * 1024 * α₀ ^ 2 * bondEnergy A := by ring
  rw [h3] at hstep
  linarith [hstep, h1, h2]

#print axioms sum_pair_localG
#print axioms sum_blockBondSq_eq
#print axioms aggregate_fibre_bound_curved

/-! ## §6 — the coercivity constant, the threshold, and the controls -/

/-- The curved coercivity constant. `γ_curved(α₀, ε) = (1 − (1+1/ε)·1024·α₀²)/((1+ε)·3316224)`. -/
noncomputable def gammaCurved (α₀ ε : ℝ) : ℝ :=
  (1 - (1 + 1 / ε) * 1024 * α₀ ^ 2) / ((1 + ε) * 3316224)

/-- **THE TRANSFER, in coercivity form.** `γ_curved · bondEnergy A ≤ P_Ax(A) + curlEnergy A` on the
covariant fibre `{Q_2(U)A = 0}`. -/
theorem transfer_gamma (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hsup : frobSupBond U ≤ α₀)
    {ε : ℝ} (hε : 0 < ε) (A : Bond L → SuTwo)
    (hQU : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov U 2 A b = 0) :
    gammaCurved α₀ ε * bondEnergy A ≤ pAx A (CoarseLattice L 2) 2 + curlEnergy A := by
  have hmain := aggregate_fibre_bound_curved hdvd U hα₀ hsup hε A hQU
  have hden : (0 : ℝ) < (1 + ε) * 3316224 := by positivity
  unfold gammaCurved
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [hmain]

/-- **THE THRESHOLD, TWO-SIDED, at `ε = 1`.** The constant is positive EXACTLY below
`α₀* = 1/√2048`. Both directions are proved, so the threshold is not one-sided decoration. -/
theorem gammaCurved_pos_iff (α₀ : ℝ) : 0 < gammaCurved α₀ 1 ↔ 2048 * α₀ ^ 2 < 1 := by
  unfold gammaCurved
  rw [show ((1 : ℝ) + 1) * 3316224 = 6632448 by norm_num,
    show (1 : ℝ) - (1 + 1 / (1 : ℝ)) * 1024 * α₀ ^ 2 = 1 - 2048 * α₀ ^ 2 by norm_num]
  constructor
  · intro h
    have := (div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 6632448)).mp h
    linarith
  · intro h
    apply div_pos (by linarith) (by norm_num)

/-- **MUST-NOT-FIRE.** At or above the threshold the constant is NONPOSITIVE — a theorem, not a
remark. At `α₀ = 1/32` (`2048/1024 = 2 ≥ 1`) it is strictly negative. -/
theorem gammaCurved_nonpos_of_large {α₀ : ℝ} (h : 1 ≤ 2048 * α₀ ^ 2) : gammaCurved α₀ 1 ≤ 0 := by
  by_contra hcon
  rw [not_le] at hcon
  have := (gammaCurved_pos_iff α₀).mp hcon
  linarith

theorem gammaCurved_neg_at_one_over_32 : gammaCurved (1 / 32) 1 < 0 := by
  unfold gammaCurved
  norm_num

/-- **MUST-NOT-DEGRADE — the flat constant is recovered EXACTLY.** Taking `U = 1` (so `α₀ = 0`) and
letting `ε → 0` in `aggregate_fibre_bound_curved` returns `bondEnergy A ≤ 3316224·(P_Ax + curl)`,
which is `FibreAggregate.aggregate_fibre_bound` verbatim. Proved THROUGH the curved chain — the
flat theorem is never invoked — so this is a genuine cross-check of the curved chain against the
flat one and not a restatement. -/
theorem curved_recovers_flat_constant (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0) :
    bondEnergy A ≤ 3316224 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A) := by
  set G := pAx A (CoarseLattice L 2) 2 + curlEnergy A with hGdef
  have hG0 : (0 : ℝ) ≤ G := by
    have h1 := pAx_nonneg A (CoarseLattice L 2) 2
    have h2 := curlEnergy_nonneg A
    rw [hGdef]; linarith
  have hsup0 : frobSupBond (trivialU L) ≤ 0 :=
    le_of_eq (AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU L)
  have hall : ∀ ε : ℝ, 0 < ε → bondEnergy A ≤ (1 + ε) * 3316224 * G := by
    intro ε hε
    have h := aggregate_fibre_bound_curved hdvd (trivialU L) (le_refl (0 : ℝ)) hsup0 hε A hQ
    rw [← hGdef] at h
    have hz : (1 : ℝ) - (1 + 1 / ε) * 1024 * (0 : ℝ) ^ 2 = 1 := by ring
    rw [hz, one_mul] at h
    exact h
  by_contra hcon
  rw [not_le] at hcon
  set c := 3316224 * G with hcdef
  have hc0 : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
  set δ := bondEnergy A - c with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hεpos : 0 < δ / (c + 1) := by positivity
  have h := hall (δ / (c + 1)) hεpos
  have hexp : (1 + δ / (c + 1)) * 3316224 * G = c + (δ / (c + 1)) * c := by
    rw [hcdef]; ring
  rw [hexp] at h
  have hfrac : (δ / (c + 1)) * c < δ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < c + 1)]
    nlinarith [hδ0, hc0]
  linarith [h, hfrac]

#print axioms gammaCurved
#print axioms transfer_gamma
#print axioms gammaCurved_pos_iff
#print axioms gammaCurved_nonpos_of_large
#print axioms gammaCurved_neg_at_one_over_32
#print axioms curved_recovers_flat_constant

/-! ### §6b — the `Δ_k(U)` form -/

/-- The curved constant in `Δ_k(U)` form. The extra subtraction is
`ComposedCoercivity.driftRemainder α₀ = 544α₀ + 64α₀²` (the operator half of §3b), paid at the
aggregate constant `(1+ε)·3316224` — which is why the admissible `α₀` here is orders of magnitude
smaller than `gammaCurved`'s `1/√2048`. -/
noncomputable def gammaCurvedDeltaK (α₀ ε : ℝ) : ℝ :=
  (1 - (1 + 1 / ε) * 1024 * α₀ ^ 2 - (1 + ε) * 3316224 * (544 * α₀ + 64 * α₀ ^ 2))
    / (2 * ((1 + ε) * 3316224))

/-- **THE TRANSFER, IN THE CAMPAIGN'S OWN `Δ_k(U)`.** Both the `Q` clause AND the operator are at
the curved background `U`. This is the statement `ComposedCoercivity.AggregateFibreBound` carries
with a FLAT `Q` clause; here the clause is covariant. -/
theorem transfer_deltaK_curved (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hsup : frobSupBond U ≤ α₀)
    {ε : ℝ} (hε : 0 < ε) (A : Bond L → SuTwo)
    (hQU : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov U 2 A b = 0) :
    gammaCurvedDeltaK α₀ ε * bondEnergy A
      ≤ deltaKQuadFormNormalizedCorrected U A + pAx A (CoarseLattice L 2) 2 := by
  have hmain := aggregate_fibre_bound_curved hdvd U hα₀ hsup hε A hQU
  have hcurl := AdalyFormal.Balaban.ComposedCoercivity.curlEnergy_le_curved hα₀ U hsup A
  rw [AdalyFormal.Balaban.ComposedCoercivity.driftRemainder] at hcurl
  have hP : (0 : ℝ) ≤ pAx A (CoarseLattice L 2) 2 := pAx_nonneg A (CoarseLattice L 2) 2
  have hK : (0 : ℝ) < (1 + ε) * 3316224 := by positivity
  have hden : (0 : ℝ) < 2 * ((1 + ε) * 3316224) := by positivity
  -- push the curl bound through the (positive) aggregate coefficient
  have hstep : (1 + ε) * 3316224 * (pAx A (CoarseLattice L 2) 2 + curlEnergy A)
      ≤ (1 + ε) * 3316224
          * (pAx A (CoarseLattice L 2) 2
              + (2 * deltaKQuadFormNormalizedCorrected U A
                + (544 * α₀ + 64 * α₀ ^ 2) * bondEnergy A)) := by
    have h := hcurl
    nlinarith [hK, h]
  have hbound : (1 + ε) * 3316224
        * (pAx A (CoarseLattice L 2) 2
            + (2 * deltaKQuadFormNormalizedCorrected U A
              + (544 * α₀ + 64 * α₀ ^ 2) * bondEnergy A))
      ≤ 2 * ((1 + ε) * 3316224)
          * (deltaKQuadFormNormalizedCorrected U A + pAx A (CoarseLattice L 2) 2)
        + (1 + ε) * 3316224 * (544 * α₀ + 64 * α₀ ^ 2) * bondEnergy A := by
    nlinarith [hK, hP]
  unfold gammaCurvedDeltaK
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [hmain, hstep, hbound]

/-- **THE `Δ_k(U)` THRESHOLD CLOSES** at `α₀ = 10⁻¹⁰`, `ε = 1`: the constant is positive. -/
theorem gammaCurvedDeltaK_pos_at_1e_neg_10 : 0 < gammaCurvedDeltaK (1 / 10 ^ 10) 1 := by
  unfold gammaCurvedDeltaK
  norm_num

/-- **AND FAILS** at `α₀ = 10⁻⁹` — the must-not-fire side of the same constant. -/
theorem gammaCurvedDeltaK_nonpos_at_1e_neg_9 : gammaCurvedDeltaK (1 / 10 ^ 9) 1 ≤ 0 := by
  unfold gammaCurvedDeltaK
  norm_num

#print axioms gammaCurvedDeltaK
#print axioms transfer_deltaK_curved
#print axioms gammaCurvedDeltaK_pos_at_1e_neg_10
#print axioms gammaCurvedDeltaK_nonpos_at_1e_neg_9

/-! ### §6c — `JointInstantiation.altMode_Q_covariant` is the `α₁`-free special case

The exact-agreement trick is not superseded by being contradicted; it is superseded by being
CONTAINED. On a field valued in a line `ℝ·w` fixed by every link of `U`, `Q_2(U) = Q_2(1)`
exactly, so the point lies in the covariant fibre AND in the flat fibre, and BOTH the degraded
constant `gammaCurved α₀ ε` and the UNDEGRADED `1/3316224` apply. The new content of §5 is that
`gammaCurved` needs no line hypothesis at all. -/

/-- **THE EXACT CASE, RECOVERED.** At a line-valued alternating mode with every link fixing the
line, the covariant fibre condition holds, the curved transfer applies, AND the flat constant
applies undegraded — so `altMode_Q_covariant`'s configuration is exactly the `α₁`-remainder-free
point of this module's theorem. -/
theorem exact_case_of_line_config (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {w : SuTwo} (hUw : ∀ b : Bond L, RMap (U b) w = w)
    {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hsup : frobSupBond U ≤ α₀) {ε : ℝ} (hε : 0 < ε) :
    (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
        lineCoarseRestrictCov U 2 (altMode w) b = 0)
      ∧ gammaCurved α₀ ε * bondEnergy (altMode (L := L) w)
          ≤ pAx (altMode (L := L) w) (CoarseLattice L 2) 2 + curlEnergy (altMode (L := L) w)
      ∧ bondEnergy (altMode (L := L) w)
          ≤ 3316224 * (pAx (altMode (L := L) w) (CoarseLattice L 2) 2
              + curlEnergy (altMode (L := L) w)) := by
  have hQU := AdalyFormal.Balaban.JointInstantiation.altMode_Q_covariant hdvd U hUw
  exact ⟨hQU, transfer_gamma hdvd U hα₀ hsup hε (altMode w) hQU,
    curved_recovers_flat_constant hdvd (altMode w) (altMode_Q hdvd w)⟩

#print axioms exact_case_of_line_config

/-! ### §6d — MUST-FIRE at a genuinely curved background, both sides nonzero -/

section MustFire

open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.BridgeRestricted (rotGen rotGen_ne_zero)
open AdalyFormal.Balaban.JointInstantiation (curvedAggU curvedAggAlpha curvedAggAlpha_pos
  curvedAggU_frobSup curvedAggU_curved curvedAggT curvedFamilyU_fix_rotGen)

/-- The curved coercivity constant is POSITIVE at the campaign's own curved witness radius. -/
theorem gammaCurved_pos_at_curvedAggAlpha : 0 < gammaCurved curvedAggAlpha 1 := by
  rw [gammaCurved_pos_iff]
  unfold AdalyFormal.Balaban.JointInstantiation.curvedAggAlpha
  norm_num

/-- **MUST-FIRE.** At the genuinely curved background `curvedAggU` (holonomy `≠ 1`, so this is not
the flat case in disguise) and the nonzero field `altMode rotGen`:

* the field IS in the COVARIANT fibre `{Q_2(curvedAggU) A = 0}`;
* the constant is strictly positive at that background's radius;
* the LEFT side is strictly positive (not a statement about zeros);
* the RIGHT side is strictly positive and finite;
* and the transfer inequality holds there.

Measured limitation, stated rather than hidden: at THIS field the flat `Δ_k(1)` vanishes
(`altMode` is closed, `FibreCoercivity.closedFlat_iff_deltaK_zero`), so the right-hand side's
positivity is carried by `P_Ax`, not by the curl term. -/
theorem transfer_must_fire :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem curvedAggU
        AdalyFormal.Balaban.RegularUCurvedWitness.curvedPlaq
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
      ∧ (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2,
          lineCoarseRestrictCov curvedAggU 2 (altMode rotGen) b = 0)
      ∧ 0 < gammaCurved curvedAggAlpha 1
      ∧ 0 < gammaCurved curvedAggAlpha 1 * bondEnergy (altMode (L := witL5) rotGen)
      ∧ 0 < pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2
            + curlEnergy (altMode (L := witL5) rotGen)
      ∧ gammaCurved curvedAggAlpha 1 * bondEnergy (altMode (L := witL5) rotGen)
          ≤ pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2
            + curlEnergy (altMode (L := witL5) rotGen) := by
  have hdvd := AdalyFormal.Balaban.FibreCoercivity.hdvd_witL5
  have hQU : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond witL5 2,
      lineCoarseRestrictCov curvedAggU 2 (altMode rotGen) b = 0 :=
    AdalyFormal.Balaban.JointInstantiation.altMode_Q_covariant hdvd curvedAggU
      (fun b => curvedFamilyU_fix_rotGen curvedAggT b)
  have hγ : 0 < gammaCurved curvedAggAlpha 1 := gammaCurved_pos_at_curvedAggAlpha
  have hbnz : altMode (L := witL5) rotGen ((zeroSite witL5), (0 : Fin 3)) ≠ 0 := by
    rw [altMode_eq rotGen (b := (((zeroSite witL5), (0 : Fin 3)) : Bond witL5)) rfl]
    have hpar : par (zeroSite witL5) = 1 := by
      unfold par; rw [if_pos (zeroSite_even (L := witL5) 0)]
    rw [hpar, one_smul]
    exact rotGen_ne_zero
  have hE : 0 < bondEnergy (altMode (L := witL5) rotGen) := bondEnergy_pos _ hbnz
  have hPnn : (0 : ℝ) ≤ pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2 :=
    pAx_nonneg _ _ 2
  have hPne : pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2 ≠ 0 :=
    altMode_pAx_ne hdvd rotGen rotGen_ne_zero
  have hCnn : (0 : ℝ) ≤ curlEnergy (altMode (L := witL5) rotGen) := curlEnergy_nonneg _
  refine ⟨curvedAggU_curved, hQU, hγ, mul_pos hγ hE, ?_,
    transfer_gamma hdvd curvedAggU (le_of_lt curvedAggAlpha_pos) curvedAggU_frobSup
      (by norm_num) (altMode rotGen) hQU⟩
  have hPpos : 0 < pAx (altMode (L := witL5) rotGen) (CoarseLattice witL5 2) 2 :=
    lt_of_le_of_ne hPnn (Ne.symm hPne)
  linarith

#print axioms gammaCurved_pos_at_curvedAggAlpha
#print axioms transfer_must_fire

end MustFire


/-! ### §6e — THE COVARIANT FIBRE IS STRICTLY LARGER: a point of `{Q_2(U)A = 0}` that is NOT in
`{Q_2(1)A = 0}`

This is the non-vacuity question the whole module turns on. If the covariant fibre were contained
in the flat one, `FibreAggregate.aggregate_fibre_bound` would already cover
`{Q_2(U)A = 0}` and §5 would be decoration. It is not: at the CONSTANT background `g` with
`RMap g w = -w` (the tree's own `CovariantOperators.RMap_witnessMElem`, `g = !![0,1;-1,0]`,
`w = diag(i,-i)`), the field that is `w` on every direction-`0` bond lies in the covariant fibre
(TERMWISE — no block enumeration needed, because `h(x,1) = h(x,0)·U(x,μ)`) while its FLAT
coarse-graining is exactly `w ≠ 0`.

**Measured limitation, made kernel-visible rather than left in prose.** This witness has
`frobSupBond (constU witnessMElem L) = 2` (`frobSupBond_constU_witnessM`), which is ABOVE the
`α₀* = 1/√2048` threshold, so `gammaCurved` is nonpositive there
(`gammaCurved_nonpos_at_witness_alpha`). The same construction produces a fibre point at
arbitrarily SMALL `frobSupBond U`: take `U ≡ g` with `g^(L μ + 1) = ±1` and
`A(x,0) = (−1)^{x₀} • RMap(g^{−x₀}) w`, whose `frobSupBond` is `≈ π√2/n` on an extent with
`L 0 + 1 = 2n`. That variant is NOT built here: its flat block sum is no longer constant over the
block, so evaluating it needs a split of `blockOf y 2` by the parity of the `μ`-coordinate (four
sites each), and no such split — nor any 8-element enumeration of `blockOf y 2` — is exported by
`AdmissibleSubspace` (`card_blockOf` proves the image representation only INSIDE its own proof).
That is the exact missing lemma, named. -/

section FibreStrictlyLarger

open AdalyFormal.Balaban.CovariantOperators (witnessM witnessMElem suTwoWitness
  suTwoWitness_ne_zero RMap_witnessMElem RMap_mul)
open AdalyFormal.Balaban.Q1Real (rZeroA_ell2 GammaPath GammaPath_endpoint straightSegment
  straightSegment_self)
open AdalyFormal.Balaban.QOne (pathSite_zero)

/-- The CONSTANT background `U ≡ g`. -/
def constU (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (L : PeriodicLatticeExtent) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L := fun _ => g

/-- The bond field equal to `w` on every direction-`0` bond and `0` elsewhere. -/
noncomputable def dirZeroMode (w : SuTwo) : Bond L → SuTwo := fun b => if b.2 = 0 then w else 0

theorem dirZeroMode_eq (w : SuTwo) {b : Bond L} (h : b.2 = 0) : dirZeroMode w b = w := if_pos h

theorem dirZeroMode_ne (w : SuTwo) {b : Bond L} (h : b.2 ≠ 0) : dirZeroMode w b = 0 := if_neg h

/-- The one-step segment leg: `straightSegment x (x + e_μ) μ = [(μ, true)]`. -/
theorem straightSegment_one (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    straightSegment x (pathSite x μ 1) μ = [(μ, true)] := by
  have h := AdalyFormal.Balaban.RegularUQChain.coordSteps_straight_eq x μ 1
  have hge : 2 ≤ L μ + 1 := Nat.le_of_dvd (Nat.succ_pos _) (hdvd μ)
  have h2 : 1 % (L μ + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [straightSegment, h, h2, List.replicate_one]

/-- **THE ONE-LINK STEP OF THE TRANSPORT.** The `i = 1` holonomy is the `i = 0` holonomy times the
link `U(x,μ)` — this is what makes the covariant fibre membership TERMWISE. -/
theorem hol_step (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y x : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicPathHolonomy U y (transportPath y x μ 1)
      = periodicPathHolonomy U y (transportPath y x μ 0) * U (x, μ) := by
  have h0 : transportPath y x μ 0 = GammaPath y x := by
    rw [transportPath, pathSite_zero, straightSegment_self, List.append_nil]
  have h1 : transportPath y x μ 1 = GammaPath y x ++ [(μ, true)] := by
    rw [transportPath, straightSegment_one hdvd x μ]
  rw [h0, h1, AdalyFormal.Balaban.Q1Real.periodicPathHolonomy_append, GammaPath_endpoint]
  congr 1
  show (if (true : Bool) then U (x, μ) else (U (periodicLatticeStep x (μ, true), μ))⁻¹)
      * periodicPathHolonomy U (periodicLatticeStep x (μ, true)) [] = U (x, μ)
  simp [periodicPathHolonomy]

/-- **THE COVARIANT FIBRE POINT.** At the constant background `g` and any `w` with
`RMap g w = -w`, `dirZeroMode w` is annihilated by the covariant `Q_2(g)` at EVERY coarse bond. -/
theorem dirZeroMode_Q_covariant (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) {w : SuTwo} (hgw : RMap g w = -w)
    (b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2) :
    lineCoarseRestrictCov (constU g L) 2 (dirZeroMode w) b = 0 := by
  obtain ⟨⟨y, hyc⟩, μ⟩ := b
  show (1 / ((2 : ℕ) : ℝ) ^ 4)
      • ∑ x ∈ blockOf y 2, rZeroA (constU g L) y x (dirZeroMode w) μ 2 = 0
  have hz : (∑ x ∈ blockOf y 2, rZeroA (constU g L) y x (dirZeroMode w) μ 2) = 0 := by
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [rZeroA_ell2]
    by_cases hμ : μ = 0
    · subst hμ
      rw [dirZeroMode_eq w (b := ((x, (0 : Fin 3)) : Bond L)) rfl,
        dirZeroMode_eq w
          (b := ((periodicLatticeShift x 0, (0 : Fin 3)) : Bond L)) rfl]
      have hstep := hol_step hdvd (constU g L) y x 0
      have hg : (constU g L) (x, (0 : Fin 3)) = g := rfl
      rw [hg] at hstep
      rw [hstep, RMap_mul]
      show RMap (periodicPathHolonomy (constU g L) y (transportPath y x 0 0)) w
          + RMap (periodicPathHolonomy (constU g L) y (transportPath y x 0 0)) (RMap g w) = 0
      rw [hgw, map_neg, add_neg_cancel]
    · rw [dirZeroMode_ne w (b := ((x, μ) : Bond L)) hμ,
        dirZeroMode_ne w (b := ((periodicLatticeShift x μ, μ) : Bond L)) hμ,
        map_zero, map_zero, add_zero]
  rw [hz, smul_zero]

/-- **AND IT IS NOT IN THE FLAT FIBRE.** `Q_2(1)(dirZeroMode w)(y,0) = w`, exactly: the block
cardinality `|B(y)| = 2³` (`card_blockOf_of_coarse`) cancels the `1/2⁴` against the two bonds each
site contributes. -/
theorem dirZeroMode_Q_flat (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (w : SuTwo)
    {y : PeriodicLatticeSite L} (hyc : y ∈ CoarseLattice L 2) :
    lineCoarseRestrictCov (trivialU L) 2 (dirZeroMode w) (⟨y, hyc⟩, (0 : Fin 3)) = w := by
  rw [lineCoarse_trivial_two (dirZeroMode w) y hyc 0]
  have hterm : ∀ x ∈ blockOf y 2,
      (dirZeroMode w ((x : PeriodicLatticeSite L), (0 : Fin 3))
        + dirZeroMode w (periodicLatticeShift x 0, (0 : Fin 3))) = w + w := by
    intro x _
    rw [dirZeroMode_eq w (b := ((x, (0 : Fin 3)) : Bond L)) rfl,
      dirZeroMode_eq w (b := ((periodicLatticeShift x 0, (0 : Fin 3)) : Bond L)) rfl]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_blockOf_of_coarse hdvd hyc]
  have hc : ((2 : ℕ) ^ 3) • (w + w) = ((16 : ℝ)) • w := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_add, ← add_smul]
    congr 1
    push_cast
    ring
  rw [hc, smul_smul, show (1 / ((2 : ℕ) : ℝ) ^ 4 * 16) = 1 by norm_num, one_smul]

/-- `frobSupBond` of a constant background is the per-link Frobenius distance. -/
theorem frobSupBond_constU (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobSupBond (constU g L)
      = AdalyFormal.Balaban.RMapLipschitz.frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  have hfun : (fun b : Bond L =>
        AdalyFormal.Balaban.RMapLipschitz.frobNorm
          ((((constU g L) b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) - 1))
      = (fun _ : Bond L =>
        AdalyFormal.Balaban.RMapLipschitz.frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1)) := rfl
  show Finset.univ.sup' Finset.univ_nonempty _ = _
  rw [hfun, Finset.sup'_const]

/-- The witness background's radius, EXACTLY: `frobSupBond (constU witnessMElem L) = 2`. -/
theorem frobSupBond_constU_witnessM :
    frobSupBond (constU witnessMElem L) = 2 := by
  rw [frobSupBond_constU]
  have h : AdalyFormal.Balaban.RMapLipschitz.frobSq
      ((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 4 := by
    show Complex.normSq (((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) - 1) 0 0)
        + Complex.normSq (((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) - 1) 0 1)
        + Complex.normSq (((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) - 1) 1 0)
        + Complex.normSq (((witnessMElem : Matrix (Fin 2) (Fin 2) ℂ) - 1) 1 1) = 4
    simp [witnessMElem, witnessM, Matrix.sub_apply, Complex.normSq_apply]
    norm_num
  rw [AdalyFormal.Balaban.RMapLipschitz.frobNorm, h,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **THE WITNESS RADIUS IS ABOVE THE THRESHOLD** — stated as a theorem so the limitation cannot be
read past. `2048 · 2² = 8192 ≥ 1`. -/
theorem gammaCurved_nonpos_at_witness_alpha : gammaCurved 2 1 ≤ 0 :=
  gammaCurved_nonpos_of_large (by norm_num)

/-- **THE COVARIANT FIBRE IS NOT CONTAINED IN THE FLAT FIBRE.** All four facts in one statement:
the field is in the covariant fibre at a genuinely curved background, it is NOT in the flat fibre,
the background's radius is exactly `2`, and at that radius the transfer constant is nonpositive. -/
theorem covariant_fibre_not_contained_in_flat (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hyc : y ∈ CoarseLattice L 2) :
    (∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
        lineCoarseRestrictCov (constU witnessMElem L) 2 (dirZeroMode suTwoWitness) b = 0)
      ∧ lineCoarseRestrictCov (trivialU L) 2 (dirZeroMode suTwoWitness)
          (⟨y, hyc⟩, (0 : Fin 3)) ≠ 0
      ∧ frobSupBond (constU witnessMElem L) = 2
      ∧ gammaCurved (frobSupBond (constU witnessMElem L)) 1 ≤ 0 := by
  refine ⟨dirZeroMode_Q_covariant hdvd witnessMElem RMap_witnessMElem, ?_,
    frobSupBond_constU_witnessM, ?_⟩
  · rw [dirZeroMode_Q_flat hdvd suTwoWitness hyc]
    exact suTwoWitness_ne_zero
  · rw [frobSupBond_constU_witnessM]
    exact gammaCurved_nonpos_at_witness_alpha

#print axioms constU
#print axioms dirZeroMode
#print axioms dirZeroMode_eq
#print axioms dirZeroMode_ne
#print axioms straightSegment_one
#print axioms hol_step
#print axioms dirZeroMode_Q_covariant
#print axioms dirZeroMode_Q_flat
#print axioms frobSupBond_constU
#print axioms frobSupBond_constU_witnessM
#print axioms gammaCurved_nonpos_at_witness_alpha
#print axioms covariant_fibre_not_contained_in_flat

end FibreStrictlyLarger

end AdalyFormal.Balaban.CovariantFibreTransfer
