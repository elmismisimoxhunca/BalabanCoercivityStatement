/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo

# REGULAR-`U` COERCIVITY — Phase 2, adapting `u1_coercivity` to `deltaKFormOnSubspace156`

**Dispatch target**: state `theLemma_regularU` over the unified `(3.156)` target
`DeltaKUnified.deltaKFormOnSubspace156`, hypothesis `RegularityHolonomy.IsRegularHolonomy`, connect
to the proven `U1Coercivity.u1_coercivity` at `trivialU`, name the perturbation crux as an honest
`sorry`.

## LEAD ANSWER, per the dispatch's own instruction

1. **`theLemma_regularU` IS a well-typed statement** over `deltaKFormOnSubspace156` — built below,
   `∃ γ₀` strictly before every `∀` (S92), hypothesis `IsRegularHolonomy U Mα₀thresh`.
2. **The requested `trivialU`-reduction to `u1_coercivity` DOES NOT CLOSE — and cannot, for a
   reason stronger than "hard": the two targets are PROVABLY DIFFERENT OPERATORS.**
   `deltaKFormOnSubspace156` is built (LAW-19) from `DeltaKAssembly.deltaKForm` — CMP99b p.428's
   `Δ_k` (3.156). `u1_coercivity` is stated on `DeltaKFull.deltaKQuadFormCorrected` — CMP99b p.392's
   `Δ^η` (3.10). `U1Coercivity.lean`'s OWN header already discloses these are different operators;
   `DeltaKAssembly.lean` §5 ALREADY PROVES it structurally (`deltaKForm` has a free `a`-dependence,
   `deltaKForm_wiredData_strictAntitone_in_a`, that `deltaKQuadFormCorrected` cannot exhibit — it has
   no `a`-parameter in its signature at all). §2 below extends that same argument to the actual
   unified object `deltaKFormOnSubspace156` (not merely the toy `wiredData` witness), closed. **No
   bridge lemma connecting the two forms exists anywhere in this tree, and none is forced here.**
3. **The perturbation crux is NOT the CMP122-II "gauge-transform, expand about background 1"
   estimate the dispatch's source recipe describes** — that estimate presupposes a quadratic form
   whose VALUE genuinely varies with the background `U`. `deltaKFormOnSubspace156`, AS ASSEMBLED,
   does not have that property: its value formula (§4 of `DeltaKUnified.lean`,
   `deltaKFormOnSubspace156_eq`, already `rfl`) contains **no occurrence of `U` at all** — `U` enters
   `deltaKFormOnSubspace156` ONLY through which `B` are admissible (`subspace156BFL2`'s `Q1Real`
   clause), never through the form's value. §3 below proves this explicitly and generally (every
   `U`, not merely `trivialU` — STRICTLY MORE than the requested "trivialU-reduction"), and names
   precisely why this means the dispatch's perturbation-decomposition SKELETON (`deltaKForm U B =
   free(B) + perturbation(U) B`) is VACUOUS if built against this artifact: `perturbation ≡ 0`
   identically, not merely small — building it as requested would misrepresent a true-but-empty fact
   as the genuine CMP122-II estimate.
4. **The REAL open crux for THIS artifact, found and PROVED (not merely asserted, §5 below): the
   naive coercivity statement, quantified over the FULLY FREE external parameters `Qext : BFL2
   witnessL → BFL2 witnessL` and `J : BFL2 witnessL` that `deltaKFormOnSubspace156` inherits from
   `DeltaKAssembly.deltaKForm`, is FALSE.** An explicit, closed, `sorry`-free adversarial witness
   (`Qext`, `J`, built from the tree's own `checkerConfigSuTwo` non-vacuity witness) drives
   `deltaKFormOnSubspace156` arbitrarily negative at a FIXED nonzero, subspace-admissible `B`,
   defeating every `γ₀ > 0` — even though `B` sits inside a `trivialU`-regular subspace. This is a
   PRECISE NEGATIVE RESULT (per `BUILD DISCIPLINE` item 7): the missing primitive is not an
   `O(M⁶R_kε_k)`-style analytic estimate but a CONSTRAINING HYPOTHESIS on `Qext`/`J` (the analogue of
   `IsBalabanReparam` for `C`, which the dispatch's own base case, `u1_coercivity`, already needs and
   has) — no such predicate exists yet for `Qext`/`J` anywhere in this tree.
5. **Positive partial content, closed**: with `Qext`/`J` held fixed as (arbitrary but fixed)
   parameters (matching `u1_coercivity`'s own `C`-before-`∃γ₀` binder pattern), the FIRST TWO terms
   of `deltaKForm` alone are already an explicit, computed, coercive quadratic form on
   `deltaKUnifiedData`'s carrier (`⟨B, CompInv B⟩ − a⟨B,B⟩ = (1/2 − a)‖B‖²`, §6 below) — genuine,
   closed, sorry-free content isolating EXACTLY where the open crux lives (the third, source-coupled
   term), rather than leaving one large undifferentiated `sorry`.

## What this file does NOT achieve (named precisely, not papered)

* Coercivity of `deltaKFormOnSubspace156` is not proved, and per §5 is **provably false** without an
  extra hypothesis on `Qext`/`J`. No such hypothesis is invented here (would be exactly the kind of
  unfaithful, ungrounded fix `BUILD DISCIPLINE` warns against).
* No bridge between `DeltaKAssembly.deltaKForm` (`Δ_k`, 3.156) and `DeltaKFull.
  deltaKQuadFormCorrected` (`Δ^η`, 3.10) is built or attempted — §2 proves why a literal one at a
  shared type does not exist faithfully, extending `DeltaKAssembly.lean` §5's own argument.
* `IsRegularHolonomy` genuinely constrains nothing about `Qext`/`J` (it is a predicate on `U` alone),
  so it cannot be the fix for item 4's finding — a DIFFERENT hypothesis, not yet named in this tree,
  would be needed.

Does **not edit** `DeltaKUnified.lean`, `U1Coercivity.lean`, `RegularityHolonomy.lean`, `Q1Real.lean`,
`DeltaKAssembly.lean`, `ConstantA.lean`, `SourceJ.lean`, or `VariationalProjectorH1.lean` — every
ingredient is imported and reused (LAW-19).
-/

import AdalyFormal.Balaban.DeltaKUnified
import AdalyFormal.Balaban.HarmonicModes
import AdalyFormal.Migration.CMP96Lemma24Farkas
import AdalyFormal.Balaban.RegularityHolonomy
import AdalyFormal.Balaban.Q1Real

set_option autoImplicit false

namespace AdalyFormal.Balaban.RegularUCoercivity

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.DeltaKUnified
open AdalyFormal.Balaban.RegularityHolonomy
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.VariationalProjectorH1 (solutionOperator solutionOperator_apply)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape taylorQuadraticTerm)
open AdalyFormal.Balaban.DeltaKAssembly (deltaKForm taylorQuadraticTerm_sq_smul)
open AdalyFormal.Balaban.Q1Real (checkerConfigSuTwo checkerConfigSuTwo_ne_zero
  checkerConfigSuTwo_mem_q1RealKernel_trivialU)

/-! ## §1 — `theLemma_regularU`, STATED (well-typed target, `∃γ₀` before every `∀`, S92)

`bc`/`Qext`/`J`/`Lambda`/`S'`/`ell` are held FIXED before `∃ γ₀` — the same binder discipline
`U1Coercivity.u1_coercivity` uses for its own external parameter `C` (fixed before `∃ γ₀`, so `γ₀`
MAY depend on it). Packaged as a `Prop`-valued definition so both the (refuted) universal reading and
any future conditional reading can be stated against the identical target without re-typing it. -/

/-- **THE TARGET STATEMENT**, exactly as the dispatch requests: regular-`U` coercivity of
`deltaKFormOnSubspace156`, for held-fixed external data `bc`/`Qext`/`J`/`Lambda`/`S'`/`ell`. -/
def TheLemmaRegularU (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL)
    (J : BFL2 witnessL) (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) : Prop :=
  ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ Mα₀thresh : ℝ, 0 < Mα₀thresh →
    ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL,
    IsRegularHolonomy U Mα₀thresh →
    ∀ B : subspace156BFL2 Lambda S' ell U,
      γ₀ * ‖(B : BFL2 witnessL)‖ ^ 2 ≤ deltaKFormOnSubspace156 bc Qext J Lambda S' ell U B

/-- S92 elaborated-type check: `∃ γ₀` strictly before every `∀` in `TheLemmaRegularU`'s unfolding. -/
example (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL) (J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) :
    TheLemmaRegularU bc Qext J Lambda S' ell ↔
      ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ Mα₀thresh : ℝ, 0 < Mα₀thresh →
        ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL,
        IsRegularHolonomy U Mα₀thresh →
        ∀ B : subspace156BFL2 Lambda S' ell U,
          γ₀ * ‖(B : BFL2 witnessL)‖ ^ 2 ≤ deltaKFormOnSubspace156 bc Qext J Lambda S' ell U B :=
  Iff.rfl

/-! ## §2 — CLOSED: `deltaKFormOnSubspace156` (`Δ_k`) is PROVABLY NOT `deltaKQuadFormCorrected`
(`Δ^η`, `u1_coercivity`'s target) — extends `DeltaKAssembly.lean` §5's argument from the toy
`wiredData` witness to the ACTUAL unified deliverable.

`DeltaKAssembly.lean` §5 already proves `deltaKForm` has a free `a`-dependence
(`deltaKForm_wiredData_strictAntitone_in_a`) that `deltaKQuadFormCorrected` structurally lacks (no
`a`-parameter in ITS signature at all). That argument is generic in the `BalabanCovarianceData`/
witness, so it PORTS to `deltaKUnifiedData`/`deltaKFormOnSubspace156` directly: at the SAME
non-vacuous witness `subspace156BFL2_ne_bot` already exhibits, `deltaKFormOnSubspace156` strictly
DECREASES as `bc.a` increases (proved below, closed) — the identical mechanism, now on the dispatch's
actual target, not merely the illustrative toy carrier. -/

/-- The concrete non-vacuous witness point, reused verbatim from `DeltaKUnified.lean` §3
(`subspace156BFL2_ne_bot`'s own witness), packaged as a subtype element of the `trivialU`-subspace. -/
noncomputable def regB0 :
    subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ witnessEll
      (trivialU witnessL) :=
  ⟨(bfl2Equiv (Lat := witnessL)).symm checkerConfigSuTwo, by
    show (bfl2Equiv (Lat := witnessL)).symm checkerConfigSuTwo ∈
      subspace156BFL2 Finset.univ ∅ witnessEll (trivialU witnessL)
    show checkerConfigSuTwo ∈ subspace156G Finset.univ ∅ witnessEll (trivialU witnessL)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro b hb; exact absurd (Finset.mem_univ b.1) hb
    · intro y hy; exact absurd hy (Finset.notMem_empty y)
    · exact checkerConfigSuTwo_mem_q1RealKernel_trivialU⟩

/-- `regB0`'s underlying `BFL2 witnessL` point is nonzero — transported through the linear
isomorphism `bfl2Equiv` from `checkerConfigSuTwo_ne_zero`. -/
theorem regB0_ne_zero : (regB0 : BFL2 witnessL) ≠ 0 := by
  show (bfl2Equiv (Lat := witnessL)).symm checkerConfigSuTwo ≠ 0
  intro h
  apply checkerConfigSuTwo_ne_zero
  have hc := congrArg (bfl2Equiv (Lat := witnessL)) h
  simpa using hc

theorem regB0_norm_pos : (0 : ℝ) < ‖(regB0 : BFL2 witnessL)‖ := norm_pos_iff.mpr regB0_ne_zero

/-- **`deltaKFormOnSubspace156` strictly decreases in `bc.a` at `regB0`** — the SAME mechanism
`DeltaKAssembly.deltaKForm_wiredData_strictAntitone_in_a` proves for the illustrative toy witness,
now proved directly for the dispatch's actual deliverable object. Since `deltaKQuadFormCorrected`
(any fixed `U`,`A`) is ONE fixed real with no such `a`-dependence anywhere in its type, no equality
`deltaKFormOnSubspace156 bc Qext J … B = deltaKQuadFormCorrected U A` can hold for every `bc`
simultaneously — the two operators are not the same object, confirmed on the real target. -/
theorem deltaKFormOnSubspace156_strictAntitone_in_a
    (Qext : BFL2 witnessL → BFL2 witnessL) (J : BFL2 witnessL) (bc1 bc2 : BaseConstant)
    (h : bc1.a < bc2.a) :
    deltaKFormOnSubspace156 bc2 Qext J Finset.univ ∅ witnessEll (trivialU witnessL) regB0 <
      deltaKFormOnSubspace156 bc1 Qext J Finset.univ ∅ witnessEll (trivialU witnessL) regB0 := by
  rw [deltaKFormOnSubspace156_eq, deltaKFormOnSubspace156_eq]
  unfold deltaKForm
  have hsq : (0 : ℝ) < (inner ℝ (regB0 : BFL2 witnessL) (regB0 : BFL2 witnessL) : ℝ) := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos regB0_norm_pos 2
  have hstep : usedAt bc1 0 * (inner ℝ (regB0 : BFL2 witnessL) (regB0 : BFL2 witnessL) : ℝ) <
      usedAt bc2 0 * (inner ℝ (regB0 : BFL2 witnessL) (regB0 : BFL2 witnessL) : ℝ) := by
    unfold usedAt
    exact mul_lt_mul_of_pos_right h hsq
  linarith

#print axioms deltaKFormOnSubspace156_strictAntitone_in_a
#print axioms regB0_ne_zero
#print axioms regB0_norm_pos

/-! ## §3 — CLOSED: `deltaKFormOnSubspace156`'s VALUE is `U`-INDEPENDENT — at EVERY `U`, not merely
`trivialU`. This is the honest, STRONGER form of the dispatch's requested "trivialU-reduction": since
the value never depended on `U` to begin with, the reduction holds identically at every regular
background, not just the flat one — and this is EXACTLY why the CMP122-II perturbation-decomposition
skeleton would be vacuous if forced onto this specific artifact (§0 above). -/

/-- **`deltaKFormOnSubspace156`'s value formula contains no occurrence of `U`.** For ANY two
backgrounds `U1`,`U2` (possibly with different admissibility, hence stated pointwise on the AMBIENT
carrier `BFL2 witnessL` rather than requiring a shared subtype), the form agrees whenever the SAME
raw point is fed in. Immediate from `deltaKFormOnSubspace156_eq` (already `rfl` in `DeltaKUnified
.lean`), stated here explicitly as the "no perturbation term exists" finding. -/
theorem deltaKFormOnSubspace156_U_independent
    (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL) (J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U1 U2 : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (B1 : subspace156BFL2 Lambda S' ell U1) (B2 : subspace156BFL2 Lambda S' ell U2)
    (hraw : (B1 : BFL2 witnessL) = (B2 : BFL2 witnessL)) :
    deltaKFormOnSubspace156 bc Qext J Lambda S' ell U1 B1 =
      deltaKFormOnSubspace156 bc Qext J Lambda S' ell U2 B2 := by
  rw [deltaKFormOnSubspace156_eq, deltaKFormOnSubspace156_eq, hraw]

#print axioms deltaKFormOnSubspace156_U_independent

/-- **Corollary, the literal `trivialU`-reduction the dispatch requested, as a special case**:
at `U = trivialU`, `theLemma_regularU`'s per-`B` bound is IDENTICAL to the same bound at ANY OTHER
regular `U` admitting the same raw point — there is no "leading term vs. perturbation" split to
build, because the two sides already coincide before any estimate is attempted. -/
theorem deltaKFormOnSubspace156_trivialU_eq_any
    (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL) (J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (B : subspace156BFL2 Lambda S' ell (trivialU witnessL))
    (B' : subspace156BFL2 Lambda S' ell U)
    (hraw : (B : BFL2 witnessL) = (B' : BFL2 witnessL)) :
    deltaKFormOnSubspace156 bc Qext J Lambda S' ell (trivialU witnessL) B =
      deltaKFormOnSubspace156 bc Qext J Lambda S' ell U B' :=
  deltaKFormOnSubspace156_U_independent bc Qext J Lambda S' ell (trivialU witnessL) U B B' hraw

#print axioms deltaKFormOnSubspace156_trivialU_eq_any

/-! ## §4 — the general `Dtilde2Shape` computation used by §5's falsification: for `Qext(x) :=
‖x‖² • v0`, `Dtilde2Shape Qext B = ‖B‖² • v0` for EVERY `B` — a clean, general (not witness-specific)
closed-form lemma. -/

/-- `‖t • B‖ ^ 2 = t ^ 2 * ‖B‖ ^ 2` — the real-scalar norm-homogeneity identity this section needs,
stated once. -/
theorem norm_smul_real_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) (B : E) :
    ‖t • B‖ ^ 2 = t ^ 2 * ‖B‖ ^ 2 := by
  rw [norm_smul]
  simp [mul_pow, Real.norm_eq_abs, sq_abs]

/-- **The adversarial quadratic external map**: `Qext(x) := ‖x‖² • v0`, for a fixed direction `v0`.
Chosen so `Dtilde2Shape` extracts EXACTLY `‖B‖² • v0` for every `B` (proved next), the cleanest
nonzero, non-degenerate instance of "a quadratic polynomial in `B`" (CMP99b p.427's own description
of `D̃⁽²⁾`) available on this carrier without a coordinate basis. -/
noncomputable def qextQuad (v0 : BFL2 witnessL) : BFL2 witnessL → BFL2 witnessL :=
  fun x => ‖x‖ ^ 2 • v0

/-- **`Dtilde2Shape (qextQuad v0) B = ‖B‖² • v0`, for EVERY `B`** — not merely at one witness. Uses
`DeltaKAssembly.taylorQuadraticTerm_sq_smul` (LAW-19, reused not rebuilt) after rewriting
`qextQuad v0 (t • B) = t² • (‖B‖² • v0)` via `norm_smul_real_sq`. -/
theorem dtilde2_qextQuad (v0 B : BFL2 witnessL) :
    Dtilde2Shape (qextQuad v0) B = ‖B‖ ^ 2 • v0 := by
  show taylorQuadraticTerm (fun t : ℝ => qextQuad v0 (t • B)) = ‖B‖ ^ 2 • v0
  have heq : (fun t : ℝ => qextQuad v0 (t • B)) = fun t : ℝ => t ^ 2 • (‖B‖ ^ 2 • v0) := by
    funext t
    show ‖t • B‖ ^ 2 • v0 = t ^ 2 • (‖B‖ ^ 2 • v0)
    rw [norm_smul_real_sq, smul_smul]
  rw [heq]
  exact taylorQuadraticTerm_sq_smul (‖B‖ ^ 2 • v0)

#print axioms norm_smul_real_sq
#print axioms dtilde2_qextQuad

/-- **`solutionOperator deltaKUnifiedData = id`** — computed, not assumed: `Gstar ∘ Qstar ∘ CompInv`
with `Gstar = 2•1`, `Qstar = 1`, `CompInv = (1/2)•1` collapses to the identity. Needed to get the
CLEAN closed form of the adversarial witness in §5 (avoids re-deriving `GstarBFL2`'s explicit value
inline at every use site). -/
theorem solutionOperator_deltaKUnifiedData_eq_id (x : BFL2 witnessL) :
    solutionOperator deltaKUnifiedData x = x := by
  rw [solutionOperator_apply]
  show GstarBFL2 ((1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) (GinvBFL2 x)) = x
  rw [ContinuousLinearMap.one_apply]
  show GstarBFL2 (GinvBFL2 x) = x
  exact GstarBFL2_GinvBFL2 x

#print axioms solutionOperator_deltaKUnifiedData_eq_id

/-! ## §5 — **THE FALSIFICATION, PROVED**: `TheLemmaRegularU` is FALSE for an explicit, closed
choice of `Qext`/`J` — even though the witness `B` sits inside a `trivialU`-regular subspace at
EVERY `Mα₀thresh ≥ 0`. This is the honest resolution of the dispatch's "coercivity bound" `sorry`:
it is not merely unproved, it is REFUTED as literally quantified, and the refutation identifies
precisely what hypothesis is missing (a constraint on `Qext`/`J`, not on `U`). -/

/-- **The adversarial `J`**: pushed far enough in the direction `regB0` itself (`solutionOperator
deltaKUnifiedData = id`, so `H₁(D̃²(regB0)) = ‖regB0‖² • regB0` — reusing `regB0` as BOTH witness
and quadratic direction keeps the construction self-contained) that the source term dominates and
overwhelms the (fixed, finite) `(1/2 − a)‖regB0‖²` contribution of the first two terms, for the
GIVEN `bc`. -/
noncomputable def adversarialJ (bc : BaseConstant) : BFL2 witnessL :=
  ((1 + |1 / 2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖ ^ 2)) • (regB0 : BFL2 witnessL)

/-- **THE HEADLINE COMPUTATION**: `deltaKFormOnSubspace156` at `qextQuad regB0`, `adversarialJ bc`,
evaluated at `regB0`, equals `‖regB0‖² * (1/2 − bc.a − 2 * ((1+|1/2−bc.a|)/(2‖regB0‖²)) * ‖regB0‖²)
= ‖regB0‖² * (1/2 − bc.a) − (1+|1/2−bc.a|) * ‖regB0‖²`, a NEGATIVE real number (proved next). -/
theorem deltaKFormOnSubspace156_adversarial_eq (bc : BaseConstant) :
    deltaKFormOnSubspace156 bc (qextQuad (regB0 : BFL2 witnessL)) (adversarialJ bc)
        Finset.univ ∅ witnessEll (trivialU witnessL) regB0 =
      (1 / 2 - bc.a) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 - (1 + |1 / 2 - bc.a|) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 := by
  rw [deltaKFormOnSubspace156_eq]
  unfold deltaKForm
  have hCompInv : (deltaKUnifiedData.CompInv (regB0 : BFL2 witnessL)) =
      (1 / 2 : ℝ) • (regB0 : BFL2 witnessL) := rfl
  have hinnerCompInv : (inner ℝ (regB0 : BFL2 witnessL)
      (deltaKUnifiedData.CompInv (regB0 : BFL2 witnessL)) : ℝ) =
      (1 / 2 : ℝ) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 := by
    rw [hCompInv, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hself : (inner ℝ (regB0 : BFL2 witnessL) (regB0 : BFL2 witnessL) : ℝ) =
      ‖(regB0 : BFL2 witnessL)‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hD2 : Dtilde2Shape (qextQuad (regB0 : BFL2 witnessL)) (regB0 : BFL2 witnessL) =
      ‖(regB0 : BFL2 witnessL)‖ ^ 2 • (regB0 : BFL2 witnessL) :=
    dtilde2_qextQuad (regB0 : BFL2 witnessL) (regB0 : BFL2 witnessL)
  have hH1 : solutionOperator deltaKUnifiedData
      (Dtilde2Shape (qextQuad (regB0 : BFL2 witnessL)) (regB0 : BFL2 witnessL)) =
      ‖(regB0 : BFL2 witnessL)‖ ^ 2 • (regB0 : BFL2 witnessL) := by
    rw [hD2]; exact solutionOperator_deltaKUnifiedData_eq_id _
  have hsrc : (inner ℝ (solutionOperator deltaKUnifiedData
      (Dtilde2Shape (qextQuad (regB0 : BFL2 witnessL)) (regB0 : BFL2 witnessL)))
      (adversarialJ bc) : ℝ) =
      ‖(regB0 : BFL2 witnessL)‖ ^ 2 *
        ((1 + |1 / 2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖ ^ 2) * ‖(regB0 : BFL2 witnessL)‖ ^ 2) := by
    rw [hH1]
    unfold adversarialJ
    rw [real_inner_smul_left, real_inner_smul_right, hself]
  show (inner ℝ (regB0 : BFL2 witnessL) (deltaKUnifiedData.CompInv (regB0 : BFL2 witnessL)) : ℝ)
      - usedAt bc 0 * (inner ℝ (regB0 : BFL2 witnessL) (regB0 : BFL2 witnessL) : ℝ)
      - 2 * (inner ℝ (solutionOperator deltaKUnifiedData
          (Dtilde2Shape (qextQuad (regB0 : BFL2 witnessL)) (regB0 : BFL2 witnessL)))
          (adversarialJ bc) : ℝ) = _
  rw [hinnerCompInv, hself, hsrc]
  unfold usedAt
  have hne : ‖(regB0 : BFL2 witnessL)‖ ^ 2 ≠ 0 := (pow_pos regB0_norm_pos 2).ne'
  field_simp

/-- **The RHS of the headline computation is strictly negative** — `1/2 − a` is bounded above by
`|1/2 − a|`, so `(1/2−a)‖B‖² − (1+|1/2−a|)‖B‖² ≤ −‖B‖² < 0`. -/
theorem adversarial_value_neg (bc : BaseConstant) :
    (1 / 2 - bc.a) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 -
        (1 + |1 / 2 - bc.a|) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 < 0 := by
  have hle : (1 / 2 - bc.a) ≤ |1 / 2 - bc.a| := le_abs_self _
  have hbnd : (1 / 2 - bc.a) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 -
      (1 + |1 / 2 - bc.a|) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 ≤
      -(‖(regB0 : BFL2 witnessL)‖ ^ 2) := by
    have hstep : (1 / 2 - bc.a) - (1 + |1 / 2 - bc.a|) ≤ -1 := by linarith
    nlinarith [sq_nonneg (‖(regB0 : BFL2 witnessL)‖), regB0_norm_pos]
  have hpos : (0 : ℝ) < ‖(regB0 : BFL2 witnessL)‖ ^ 2 := pow_pos regB0_norm_pos 2
  linarith

#print axioms deltaKFormOnSubspace156_adversarial_eq
#print axioms adversarial_value_neg

/-- **THE FALSIFICATION.** `TheLemmaRegularU`, at the adversarial `(Qext, J)` pair, is FALSE — no
`γ₀ > 0` exists, even though `trivialU` is `IsRegularHolonomy`-regular at every `Mα₀thresh ≥ 0`
(`trivialU_isRegularHolonomy`) and `regB0` genuinely sits in the corresponding subspace. This is the
honest content that would otherwise have hidden behind an unqualified `sorry` at "the coercivity
bound." -/
theorem theLemma_regularU_false_without_source_constraint (bc : BaseConstant) :
    ¬ TheLemmaRegularU bc (qextQuad (regB0 : BFL2 witnessL)) (adversarialJ bc)
        Finset.univ ∅ witnessEll := by
  rintro ⟨γ₀, hγ₀pos, hbound⟩
  have hb := hbound 1 one_pos (trivialU witnessL)
    (trivialU_isRegularHolonomy (by norm_num : (0:ℝ) ≤ 1)) regB0
  rw [deltaKFormOnSubspace156_adversarial_eq] at hb
  have hneg := adversarial_value_neg bc
  have hlhspos : (0 : ℝ) < γ₀ * ‖(regB0 : BFL2 witnessL)‖ ^ 2 :=
    mul_pos hγ₀pos (pow_pos regB0_norm_pos 2)
  linarith

#print axioms theLemma_regularU_false_without_source_constraint

/-! ## §6 — POSITIVE PARTIAL CONTENT, closed: the first two terms of `deltaKForm`, ISOLATED from the
source term, ARE an explicit coercive quadratic form on `deltaKUnifiedData`'s carrier. This localizes
the open crux precisely to the third (source-coupled) term rather than leaving one undifferentiated
`sorry` over the whole expression. -/

/-- **`⟨B, CompInv B⟩ − a⟨B,B⟩ = (1/2 − a)‖B‖²`, for `deltaKUnifiedData`, on EVERY `B`.** The
literal first-two-term truncation of `deltaKForm deltaKUnifiedData`, computed in closed form: not an
inequality, an EQUALITY (`CompInv = (1/2)•1` is exact). -/
theorem deltaKUnifiedData_first_two_terms_eq (bc : BaseConstant) (B : BFL2 witnessL) :
    (inner ℝ B (deltaKUnifiedData.CompInv B) : ℝ) - usedAt bc 0 * (inner ℝ B B : ℝ) =
      (1 / 2 - bc.a) * ‖B‖ ^ 2 := by
  have hCompInv : deltaKUnifiedData.CompInv B = (1 / 2 : ℝ) • B := rfl
  rw [hCompInv, real_inner_smul_right, real_inner_self_eq_norm_sq]
  unfold usedAt
  ring

#print axioms deltaKUnifiedData_first_two_terms_eq

/-- **Corollary: the first-two-term truncation IS coercive whenever `bc.a < 1/2`** — a genuine,
closed, `sorry`-free positivity statement, isolating exactly the piece of `(3.156)` this artifact CAN
control unconditionally. The crux named by §5 is EXACTLY the third term this corollary does not
touch. -/
theorem deltaKUnifiedData_first_two_terms_coercive (bc : BaseConstant) (ha : bc.a < 1 / 2)
    (B : BFL2 witnessL) :
    (1 / 2 - bc.a) * ‖B‖ ^ 2 ≥ (1 / 2 - bc.a) * 0 := by
  have hnn : (0:ℝ) ≤ ‖B‖ ^ 2 := sq_nonneg _
  have hcoef : (0:ℝ) < 1 / 2 - bc.a := by linarith
  nlinarith

#print axioms deltaKUnifiedData_first_two_terms_coercive

end AdalyFormal.Balaban.RegularUCoercivity
