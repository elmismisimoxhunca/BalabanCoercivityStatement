/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Lemma L8c (perturbation transfer) — coercivity survives a small operator-norm perturbation

**Migration target.** `REFORM_PROGRAM.md` Phase 3;
`compute/lean_spine_triage/LEAN_SPINE_TRIAGE.md` §2.1 row 1, §4 item 2 (rank **#2** on the whole
spine by load-bearing). This file formalizes and proves, as a kernel-checked Lean theorem, the
campaign's own reduction lemma L8c, whose true location is
**`compute/gap1_kernel_rgstep/DERIVATION.md:802-805`** (the triage self-corrected an earlier
mis-citation: `compute/coerc_u_close/DERIVATION.md:22` only *inherits* it, it is not the source).

## The source (quoted, `compute/gap1_kernel_rgstep/DERIVATION.md:802-805`)

> **Lemma L8c (perturbation transfer; proved and certified here).** If `Δ(1) ≥ γ` on `V` and
> `E := Δ(U) − Δ(1)` satisfies `‖P_V E P_V‖ ≤ ε`, then `Δ(U) ≥ γ − ε` on `V`. *Proof:* for `B ∈ V`,
> `⟨B,Δ(U)B⟩ = ⟨B,Δ(1)B⟩ + ⟨B,EB⟩ ≥ γ‖B‖² − ε‖B‖²`. ∎

Its role in the spine (same file, surrounding prose, and `compute/coerc_u_close/DERIVATION.md:22,
254-257`): it reduces the four-consumer primitive `[LEM-COERC-U]` (`Δ_k(U) ≥ γ'' > 0` on `V`,
uniform in `k` and `U`) to the single quantitative estimate
`‖P_V(Δ_k(U) − Δ_k(1))P_V‖ ≤ ε(α₀) < (γ₀/12d²)L^{−d−1}`, uniformly in `k` — a norm bound that is
`[LEM-COERC-U]`'s remaining genuinely-open half. L8c itself is the elementary perturbation-transfer
half; the certificate `compute/gap1_kernel_rgstep/cert_r2.py` gate `G-C2` measured it **16/16
forced** on Python evidence (`compute/S86_TALLY.md`, `LEAN_SPINE_TRIAGE.md` header) — this file
replaces that forced Python evidence with a kernel-checked proof, per `REFORM_PROGRAM.md` L10
("Python artifacts carry no grade and sign nothing").

## Statement design — abstract objects, no lattice/gauge machinery (per dispatch mandate)

The dispatch requires this file to stand alone, over "operators on a finite-dimensional real
inner-product space, a subspace projection `P_V`" — **not** importing the in-progress `Balaban/` or
`Lattice/` modules. Concretely:

* `H` is an abstract finite-dimensional real inner-product space (the campaign's own `B` lives in a
  concrete bond/block `L²`-type space, e.g. `Balaban/Coercivity.lean`'s `H`, but this lemma's proof
  uses NOTHING about that space beyond the inner-product-space axioms and finite-dimensionality —
  exactly as the source's own three-line proof does).
* `Δ₁, Δ₂ : H →L[ℝ] H` are opaque continuous linear operators (in finite dimension every linear map
  is automatically continuous — `LinearMap.continuous_of_finiteDimensional` — so this loses no
  generality versus the source's implicit `Δ₁, Δ₂` matrices/operators).
* **`P_V` is not a hypothesized/axiomatized object.** It is `V.starProjection : H →L[ℝ] H`,
  Mathlib's own canonical orthogonal projection onto a submodule `V`, together with Mathlib's own
  proofs that it is idempotent onto `V` (`Submodule.starProjection_eq_self_iff`) and
  **self-adjoint** (`Submodule.inner_starProjection_left_eq_right`). This is a deliberate
  strengthening over
  "any operator `P` satisfying projection axioms as hypotheses": a hypothesized `P` could be rigged
  (e.g. idempotent but not self-adjoint) to make the theorem provable vacuously or falsely: see
  `perturbation_transfer_needs_selfadjoint_projection` below, which exhibits exactly this failure
  for a genuine (non-orthogonal) idempotent in place of `V.starProjection`. Using Mathlib's own
  constructed orthogonal projection closes that rigging channel by construction (LEAN-P,
  `REFORM_PROGRAM.md` §LEAN-P: "definition-rigging ... NO mechanical detector" — this file avoids
  the channel rather than merely asserting it is closed).
* The norm hypothesis `‖P_V E P_V‖ ≤ ε` is Mathlib's REAL `ContinuousLinearMap` operator norm
  (`ContinuousLinearMap.opNorm`, notation `‖·‖`), not a restatement — using
  `ContinuousLinearMap.le_of_opNorm_le` for the norm-to-pointwise-bound step, exactly the API named
  by the triage row (`LEAN_SPINE_TRIAGE.md` §2.1 row 1).

## What the proof below does (the source's three lines, spelled out)

For `B ∈ V`: `P_V B = B` (idempotence onto `V`). Hence
`⟨B, EB⟩ = ⟨P_V B, EB⟩ = ⟨B, P_V(EB)⟩` (self-adjointness of `P_V`) `= ⟨B, P_V(E(P_V B))⟩`
(since `P_V B = B` again) `= ⟨B, (P_V E P_V) B⟩`. Cauchy–Schwarz plus the operator-norm hypothesis
then gives `|⟨B, EB⟩| ≤ ‖P_V E P_V‖‖B‖² ≤ ε‖B‖²`, and `⟨B,Δ₂B⟩ = ⟨B,Δ₁B⟩ + ⟨B,EB⟩ ≥ (γ−ε)‖B‖²`
follows by linearity of the inner product and the hypothesis on `Δ₁`. This is exactly the source's
argument — no step beyond it is used, and no lattice/gauge content enters anywhere.

## L7 — witness instance and degenerate-witness prosecution

`perturbation_transfer_witness` below exhibits genuinely nontrivial data (`H = ℝ²`, a proper
nontrivial `V` of dimension 1, `γ > ε > 0` both strictly positive, `Δ₁ ≠ Δ₂`, and a nonzero
`B ∈ V`) satisfying every hypothesis with room to spare, so the theorem is not vacuous.
`perturbation_transfer_needs_hγ` and `perturbation_transfer_needs_hE` show each hypothesis is
load-bearing: dropping either produces concrete data for which the stated bound fails.
`perturbation_transfer_needs_selfadjoint_projection` shows the theorem's own mechanism genuinely
needs `P_V` self-adjoint (an orthogonal projection), not merely idempotent — a degenerate,
non-self-adjoint idempotent "projection" onto the SAME subspace `V` breaks the identity the proof
relies on, at concrete numeric data, confirming the design choice above is not decorative.
-/

namespace AdalyFormal.Migration.L8c

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-! ## The theorem -/

/-- **Lemma L8c (perturbation transfer).**
`V.starProjection` is Mathlib's canonical orthogonal projection onto `V` (self-adjoint, idempotent
onto `V` — proved facts, not hypotheses). If `Δ₁` is coercive by `γ` on `V`, and the operator norm
of `P_V ∘ (Δ₂ − Δ₁) ∘ P_V` is at most `ε`, then `Δ₂` is coercive by `γ − ε` on `V`.

(`FiniteDimensional ℝ H` is not used by the proof itself — self-adjointness and idempotence of
`V.starProjection` only need `[V.HasOrthogonalProjection]`, which finite-dimensionality of `H`
supplies automatically at every instantiation below; the theorem is stated over the finite-dim
section variable per the dispatch mandate, so the compiler's unused-section-variable lint on this
one declaration is expected and does not indicate a missing hypothesis.) -/
theorem perturbation_transfer (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (Δ₁ Δ₂ : H →L[ℝ] H) (γ ε : ℝ)
    (hγ : ∀ B ∈ V, γ * ‖B‖ ^ 2 ≤ inner ℝ B (Δ₁ B))
    (hE : ‖V.starProjection ∘L ((Δ₂ - Δ₁) ∘L V.starProjection)‖ ≤ ε) :
    ∀ B ∈ V, (γ - ε) * ‖B‖ ^ 2 ≤ inner ℝ B (Δ₂ B) := by
  intro B hB
  have hPB : V.starProjection B = B := Submodule.starProjection_eq_self_iff.mpr hB
  set F : H →L[ℝ] H := V.starProjection ∘L ((Δ₂ - Δ₁) ∘L V.starProjection) with hFdef
  -- `F B = P_V(E B)` since `P_V B = B` (idempotence) collapses the INNER application.
  have hFB : F B = V.starProjection ((Δ₂ - Δ₁) B) := by
    simp only [hFdef, ContinuousLinearMap.comp_apply, hPB]
  -- Self-adjointness of `P_V` transfers `⟨B, E B⟩` to `⟨B, P_V(E B)⟩ = ⟨B, F B⟩`.
  have hSelfAdj : inner ℝ B ((Δ₂ - Δ₁) B) = inner ℝ B (F B) := by
    have h1 : inner ℝ (V.starProjection B) ((Δ₂ - Δ₁) B)
        = inner ℝ B (V.starProjection ((Δ₂ - Δ₁) B)) :=
      Submodule.inner_starProjection_left_eq_right V B ((Δ₂ - Δ₁) B)
    rw [hPB] at h1
    rw [hFB]
    exact h1
  -- Cauchy–Schwarz plus the operator-norm hypothesis: `|⟨B, F B⟩| ≤ ε‖B‖²`.
  have hCS : ‖(inner ℝ B (F B) : ℝ)‖ ≤ ‖B‖ * ‖F B‖ := norm_inner_le_norm B (F B)
  have hFnorm : ‖F B‖ ≤ ε * ‖B‖ := F.le_of_opNorm_le hE B
  have hBnn : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have hbound : |inner ℝ B (F B)| ≤ ε * ‖B‖ ^ 2 := by
    calc |inner ℝ B (F B)| = ‖(inner ℝ B (F B) : ℝ)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖B‖ * ‖F B‖ := hCS
      _ ≤ ‖B‖ * (ε * ‖B‖) := mul_le_mul_of_nonneg_left hFnorm hBnn
      _ = ε * ‖B‖ ^ 2 := by ring
  have hge : -(ε * ‖B‖ ^ 2) ≤ inner ℝ B (F B) := neg_le_of_abs_le hbound
  -- linearity: `⟨B,Δ₂B⟩ = ⟨B,Δ₁B⟩ + ⟨B,EB⟩`.
  have hsplit : inner ℝ B (Δ₂ B) = inner ℝ B (Δ₁ B) + inner ℝ B ((Δ₂ - Δ₁) B) := by
    have hE' : (Δ₂ - Δ₁) B = Δ₂ B - Δ₁ B := by
      simp
    rw [hE', inner_sub_right]
    ring
  have hγB := hγ B hB
  calc (γ - ε) * ‖B‖ ^ 2 = γ * ‖B‖ ^ 2 - ε * ‖B‖ ^ 2 := by ring
    _ ≤ inner ℝ B (Δ₁ B) - ε * ‖B‖ ^ 2 := by linarith [hγB]
    _ ≤ inner ℝ B (Δ₁ B) + inner ℝ B (F B) := by linarith [hge]
    _ = inner ℝ B (Δ₁ B) + inner ℝ B ((Δ₂ - Δ₁) B) := by rw [← hSelfAdj]
    _ = inner ℝ B (Δ₂ B) := hsplit.symm

/-! ## A reusable scalar-operator family, for the witness and degenerate-witness data below.

`scaleOp c := c • id` is the simplest genuinely-nonzero, non-identity operator family: it is
coercive with the SHARP constant `c` on every subspace (not just on `V`), and its perturbation
operator `P_V(scaleOp c₂ − scaleOp c₁)P_V` has operator norm EXACTLY controlled by `|c₂ − c₁|`
(via submultiplicativity and `‖P_V‖ ≤ 1`), so both `hγ` and `hE` can be instantiated with fully
explicit, hand-checked numeric data below — no lattice, gauge, or spectral computation needed. -/

section ScalarFamily

variable (c : ℝ)

/-- `c • id`, the scalar multiple of the identity operator. -/
def scaleOp : H →L[ℝ] H := c • ContinuousLinearMap.id ℝ H

@[simp] theorem scaleOp_apply (x : H) : scaleOp (H := H) c x = c • x := rfl

/-- `scaleOp c` is coercive by exactly `c` on EVERY subspace (in particular on `V`), with equality:
`⟨B, (scaleOp c) B⟩ = c‖B‖²`. -/
theorem inner_scaleOp (x : H) : inner ℝ x (scaleOp (H := H) c x) = c * ‖x‖ ^ 2 := by
  rw [scaleOp_apply, inner_smul_right, real_inner_self_eq_norm_sq]

/-- The perturbation operator between two scalar families is bounded by the plain scalar gap,
for ANY subspace `V` (uses only `‖V.starProjection‖ ≤ 1` and operator-norm submultiplicativity —
no exact value of `V.starProjection` is ever computed). -/
theorem scaleOp_perturbation_norm_le (V : Submodule ℝ H) [V.HasOrthogonalProjection] (c₁ c₂ : ℝ)
    [Nontrivial H] :
    ‖V.starProjection ∘L ((scaleOp (H := H) c₂ - scaleOp (H := H) c₁) ∘L V.starProjection)‖
      ≤ |c₂ - c₁| := by
  have hPle : ‖V.starProjection‖ ≤ 1 := V.starProjection_norm_le
  have hPnn : (0:ℝ) ≤ ‖V.starProjection‖ := norm_nonneg _
  have hE : scaleOp (H := H) c₂ - scaleOp (H := H) c₁ = (c₂ - c₁) • ContinuousLinearMap.id ℝ H := by
    simp [scaleOp, sub_smul]
  have hEnorm : ‖scaleOp (H := H) c₂ - scaleOp (H := H) c₁‖ = |c₂ - c₁| := by
    rw [hE, norm_smul, ContinuousLinearMap.norm_id]
    simp [Real.norm_eq_abs]
  calc ‖V.starProjection ∘L
        ((scaleOp (H := H) c₂ - scaleOp (H := H) c₁) ∘L V.starProjection)‖
      ≤ ‖V.starProjection‖ * ‖(scaleOp (H := H) c₂ - scaleOp (H := H) c₁) ∘L V.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖V.starProjection‖ * (‖scaleOp (H := H) c₂ - scaleOp (H := H) c₁‖ * ‖V.starProjection‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hPnn
    _ = ‖V.starProjection‖ * ‖V.starProjection‖ * |c₂ - c₁| := by rw [hEnorm]; ring
    _ ≤ 1 * 1 * |c₂ - c₁| := by
        have h1 : ‖V.starProjection‖ * ‖V.starProjection‖ ≤ 1 * 1 :=
          mul_le_mul hPle hPle hPnn (by norm_num)
        nlinarith [abs_nonneg (c₂ - c₁), h1]
    _ = |c₂ - c₁| := by ring

end ScalarFamily

/-! ## L7 — witness instance: `H = ℝ²`, a genuine proper nontrivial `V`, strictly positive slack. -/

/-- The witness space: the real plane, as an inner-product space. -/
abbrev WitnessSpace : Type := EuclideanSpace ℝ (Fin 2)

/-- The witness subspace: the span of the first standard basis vector — a PROPER, NONTRIVIAL
(neither `⊥` nor `⊤`) subspace of `WitnessSpace`, so the theorem is genuinely exercised on a
partial constraint, not on the whole space or the zero space. -/
noncomputable def WitnessV : Submodule ℝ WitnessSpace :=
  Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)}

/-- **Nontrivial witness (L7).** `Δ₁ = 10 • id`, `Δ₂ = 11 • id`, `γ = 10`, `ε = 1`: every hypothesis
of `perturbation_transfer` holds (with `hγ` exact, `hE` exact via `scaleOp_perturbation_norm_le`),
`γ − ε = 9 > 0` is a genuinely nontrivial (non-vacuous, strictly positive) bound, and the witness
vector `B := EuclideanSpace.single 0 1 ∈ WitnessV` is NONZERO (`‖B‖ = 1 ≠ 0`), so the conclusion
`9 ≤ ⟨B, Δ₂B⟩ = 11` is a genuine, non-degenerate numeric fact, not a `0 ≤ 0` triviality. -/
theorem perturbation_transfer_witness :
    ∀ B ∈ WitnessV, ((10 : ℝ) - 1) * ‖B‖ ^ 2 ≤ inner ℝ B (scaleOp (H := WitnessSpace) 11 B) := by
  have hγ : ∀ B ∈ WitnessV, (10 : ℝ) * ‖B‖ ^ 2 ≤ inner ℝ B (scaleOp (H := WitnessSpace) 10 B) :=
    fun B _ => le_of_eq (inner_scaleOp 10 B).symm
  have hE : ‖WitnessV.starProjection ∘L
      ((scaleOp (H := WitnessSpace) 11 - scaleOp (H := WitnessSpace) 10) ∘L
        WitnessV.starProjection)‖ ≤ (1 : ℝ) := by
    have h := scaleOp_perturbation_norm_le (H := WitnessSpace) WitnessV 10 11
    have h1 : |(11 : ℝ) - 10| = 1 := by norm_num
    rwa [h1] at h
  exact perturbation_transfer WitnessV (scaleOp (H := WitnessSpace) 10)
    (scaleOp (H := WitnessSpace) 11) 10 1 hγ hE

/-- The witness's own instantiating vector is genuinely nonzero, and its bound is a strictly
positive, non-degenerate number — confirming `perturbation_transfer_witness` is not a `0 ≤ 0`
vacuity. -/
theorem perturbation_transfer_witness_nontrivial :
    EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∈ WitnessV
      ∧ ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ≠ 0
      ∧ (0 : ℝ) < ((10 : ℝ) - 1) * ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2 := by
  refine ⟨Submodule.mem_span_singleton_self _, ?_, ?_⟩
  · simp
  · simp

/-! ## L7 — degenerate-witness prosecution: every hypothesis of `perturbation_transfer` is
load-bearing. -/

/-- **Dropping `hγ` breaks the conclusion.** At `γ = 100` (a value NOT actually satisfied by
`Δ₁ = 10 • id` — `hγ` would be the false statement `100 ≤ 10`), the "conclusion"
`(100 − 1)‖B‖² ≤ ⟨B, Δ₂B⟩ = 11‖B‖²` is false for any nonzero `B` (`99 ≤ 11` is false). This shows
`hγ`'s actual numeric content (not just its shape) is load-bearing: the theorem does not somehow
produce the right bound from `Δ₂` alone. -/
theorem perturbation_transfer_needs_hγ :
    ¬ ((100 : ℝ) * ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2
        ≤ inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
            (scaleOp (H := WitnessSpace) 10 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))
    ∧ ¬ (((100 : ℝ) - 1) * ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2
        ≤ inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
            (scaleOp (H := WitnessSpace) 11 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))) := by
  have hinner10 : inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      (scaleOp (H := WitnessSpace) 10 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) = 10 := by
    rw [inner_scaleOp]; simp
  have hinner11 : inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      (scaleOp (H := WitnessSpace) 11 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) = 11 := by
    rw [inner_scaleOp]; simp
  have hnorm : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ = 1 := by simp
  rw [hinner10, hinner11, hnorm]
  norm_num

/-- **Dropping `hE` (using a wrong, too-small `ε`) breaks the conclusion — AND the claimed `hE`
itself is genuinely false, not merely "the conclusion happens to fail".** Take `Δ₁ = 10 • id`
(same `γ = 10` as the witness, `hγ` exact) but `Δ₂ = 9 • id` (a DECREASE, so the perturbation
pushes the wrong way, unlike the witness's `Δ₂ = 11 • id`). The true perturbation operator
`F := P_V(Δ₂−Δ₁)P_V` satisfies `F B = −B` at the witness vector `B` (computed directly below), so
`‖F‖ ≥ ‖F B‖ = ‖B‖ = 1` (`ContinuousLinearMap.unit_le_opNorm`, no assumption): the claimed bound
`‖F‖ ≤ 2/5` is FALSE, exactly parallel to the Farkas-migration pattern's own hypothesis-failure
witnesses (`CMP96Lemma24Farkas.lean`'s `farkas_core_needs_hStar`). And with that false `ε = 2/5`,
the naively-expected conclusion `(10 − 2/5)‖B‖² ≤ ⟨B,Δ₂B⟩ = 9‖B‖²` is ALSO false (`9.6 ≤ 9` fails)
— so the numeric value of `ε`, not merely its existence, is load-bearing. -/
theorem perturbation_transfer_needs_hE :
    (10 : ℝ) * ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2
        ≤ inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
            (scaleOp (H := WitnessSpace) 10 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
    ∧ ¬ (‖WitnessV.starProjection ∘L
            ((scaleOp (H := WitnessSpace) 9 - scaleOp (H := WitnessSpace) 10) ∘L
              WitnessV.starProjection)‖ ≤ (2/5 : ℝ))
    ∧ ¬ (((10 : ℝ) - 2/5) * ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2
        ≤ inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
            (scaleOp (H := WitnessSpace) 9 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))) := by
  set B : WitnessSpace := EuclideanSpace.single (0 : Fin 2) (1 : ℝ) with hBdef
  have hBmemV : B ∈ WitnessV := Submodule.mem_span_singleton_self _
  have hnorm : ‖B‖ = 1 := by simp [hBdef]
  have hPB : WitnessV.starProjection B = B := Submodule.starProjection_eq_self_iff.mpr hBmemV
  refine ⟨le_of_eq (inner_scaleOp 10 B).symm, ?_, ?_⟩
  · intro hcontra
    set F : WitnessSpace →L[ℝ] WitnessSpace :=
      WitnessV.starProjection ∘L
        ((scaleOp (H := WitnessSpace) 9 - scaleOp (H := WitnessSpace) 10) ∘L
          WitnessV.starProjection) with hFdef
    have hFB : F B = -B := by
      have heq : (scaleOp (H := WitnessSpace) 9 - scaleOp (H := WitnessSpace) 10) B
          = ((9 : ℝ) - 10) • B := by
        rw [sub_apply, scaleOp_apply, scaleOp_apply, sub_smul]
      have hstep : (scaleOp (H := WitnessSpace) 9 - scaleOp (H := WitnessSpace) 10) B = -B := by
        rw [heq]
        have h910 : ((9 : ℝ) - 10) = -1 := by norm_num
        rw [h910, neg_one_smul]
      simp only [hFdef, ContinuousLinearMap.comp_apply, hPB, hstep, map_neg]
    have hlow : ‖F B‖ ≤ ‖F‖ := F.unit_le_opNorm B (le_of_eq hnorm)
    rw [hFB, norm_neg, hnorm] at hlow
    linarith [hcontra, hlow]
  · have h1 : inner ℝ B (scaleOp (H := WitnessSpace) 9 B) = 9 := by
      rw [inner_scaleOp, hnorm]; norm_num
    rw [h1, hnorm]
    norm_num

/-! ## The self-adjointness necessity witness — `P_V` cannot be weakened to "any idempotent onto
`V`". This is `perturbation_transfer`'s own key identity step tested against a rigged, merely-
idempotent stand-in for `V.starProjection` (LEAN-P: "definition-rigging ... NO mechanical
detector" — this is the hostile-reading check the mandate calls for). -/

/-- A genuinely idempotent linear endomorphism of `WitnessSpace`, with range exactly `WitnessV`
(fixes `e₀`), but which is **not self-adjoint**: it sends `e₁` (orthogonal to `WitnessV`) to
`e₀ ∈ WitnessV` instead of annihilating it, unlike the true orthogonal projection
`WitnessV.starProjection`. -/
noncomputable def obliqueQ : WitnessSpace →ₗ[ℝ] WitnessSpace where
  toFun x := (x 0 + x 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  map_add' x y := by
    change ((x + y) 0 + (x + y) 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
        = (x 0 + x 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
          + (y 0 + y 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
    rw [PiLp.add_apply, PiLp.add_apply, ← add_smul]
    congr 1
    ring
  map_smul' c x := by
    change ((c • x) 0 + (c • x) 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
        = (RingHom.id ℝ c) • ((x 0 + x 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    rw [PiLp.smul_apply, PiLp.smul_apply, RingHom.id_apply, smul_eq_mul, smul_eq_mul, smul_smul]
    congr 1
    ring

@[simp] theorem obliqueQ_apply (x : WitnessSpace) :
    obliqueQ x = (x 0 + x 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := rfl

/-- `obliqueQ`, as a continuous linear map (automatic in finite dimension). -/
noncomputable def obliqueQCLM : WitnessSpace →L[ℝ] WitnessSpace :=
  LinearMap.toContinuousLinearMap obliqueQ

@[simp] theorem obliqueQCLM_apply (x : WitnessSpace) : obliqueQCLM x = obliqueQ x := rfl

/-- The perturbation used by this witness: sends `e₀ ↦ e₁`, `e₁ ↦ 0` — i.e. it moves the
witness vector STRICTLY off `WitnessV`, exactly what is needed to expose the difference between a
self-adjoint and a merely-idempotent "projection". -/
noncomputable def flipOp : WitnessSpace →ₗ[ℝ] WitnessSpace where
  toFun x := x 0 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  map_add' x y := by
    change (x + y) 0 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
        = x 0 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
          + y 0 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
    rw [PiLp.add_apply, add_smul]
  map_smul' c x := by
    change (c • x) 0 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
        = (RingHom.id ℝ c) • (x 0 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
    rw [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul]

@[simp] theorem flipOp_apply (x : WitnessSpace) :
    flipOp x = x 0 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := rfl

/-- `flipOp`, as a continuous linear map. -/
noncomputable def flipOpCLM : WitnessSpace →L[ℝ] WitnessSpace :=
  LinearMap.toContinuousLinearMap flipOp

@[simp] theorem flipOpCLM_apply (x : WitnessSpace) : flipOpCLM x = flipOp x := rfl

/-- **`P_V`'s self-adjointness, not just idempotence, is load-bearing.** With `E := flipOpCLM`
and `B := e₀ ∈ WitnessV`: the TRUE value `⟨B, EB⟩ = 0` (`e₀ ⊥ e₁`, direct computation, no
projection needed at all). But substituting the merely-idempotent, non-self-adjoint `obliqueQCLM`
for `V.starProjection` in `perturbation_transfer`'s own key identity gives
`⟨B, (Q E Q) B⟩ = 1 ≠ 0`: the identity `⟨B,EB⟩ = ⟨B,(QEQ)B⟩` the proof relies on (there licensed by
`Submodule.inner_starProjection_left_eq_right`, i.e. self-adjointness) is genuinely FALSE for this
idempotent. Using Mathlib's own `V.starProjection` — proved self-adjoint, not merely assumed
idempotent — is therefore not a cosmetic strengthening: the proof's mechanism breaks without it. -/
theorem perturbation_transfer_needs_selfadjoint_projection :
    inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
        (flipOpCLM (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) = (0 : ℝ)
    ∧ inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
        (obliqueQCLM (flipOpCLM (obliqueQCLM (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))))
        = (1 : ℝ) := by
  constructor
  · simp [EuclideanSpace.inner_single_left]
  · simp

end AdalyFormal.Migration.L8c

#print axioms AdalyFormal.Migration.L8c.perturbation_transfer
#print axioms AdalyFormal.Migration.L8c.scaleOp_perturbation_norm_le
#print axioms AdalyFormal.Migration.L8c.perturbation_transfer_witness
#print axioms AdalyFormal.Migration.L8c.perturbation_transfer_witness_nontrivial
#print axioms AdalyFormal.Migration.L8c.perturbation_transfer_needs_hγ
#print axioms AdalyFormal.Migration.L8c.perturbation_transfer_needs_hE
#print axioms AdalyFormal.Migration.L8c.perturbation_transfer_needs_selfadjoint_projection
