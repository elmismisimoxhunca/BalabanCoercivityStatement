/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib
import AdalyFormal.Balaban.DeltaKAssembly
import AdalyFormal.Balaban.DomainSequence
import AdalyFormal.Balaban.AxialContour
import AdalyFormal.Balaban.QOne

set_option autoImplicit false

/-!
# `Δ_k` ASSEMBLY, REPAIRED — closing Sol's three convictions (grade 2, `SOL_VERDICT.md`,
commit `27f06582`) and adding the `(3.156)` subspace restriction

**Does not edit** `DeltaKAssembly.lean`, `CovarianceG1.lean`, `VariationalProjectorH1.lean`,
`ConstantA.lean`, `SourceJ.lean`, `DomainSequence.lean`, `AxialContour.lean`, or `QOne.lean` — every
ingredient is IMPORTED and REUSED (LAW-19). This file supersedes `DeltaKAssembly.lean`'s claims
where Sol convicted them; it does not touch that file's own declarations.

## §0 — WHAT SOL CONVICTED, AND THE EXACT REPAIR EACH ONE GETS BELOW

1. **WEAK WITNESS.** `deltaKForm`'s old witness used `J = (1,0)` — a `Fine`-space vector that reads
   only the FIRST coordinate. Sol compiled `plus_mutation_same_headline`: replacing `wQData`'s
   `Rconj` (`(id,−id) ↦ (id,id)`, a genuine, load-bearing sign-flip mutation of `Q`) leaves
   `deltaKForm`'s value UNCHANGED, because the resulting sign flip lands entirely in `H₁`'s SECOND
   coordinate, which `J=(1,0)` never reads. **Repair, §2 below**: `wJ2 := (1,1)` reads BOTH
   coordinates. §2 reproduces Sol's own mutation with `wJ2` and proves it now DOES change the value
   (`plusData_wJ2_ne_wiredData_wJ2`), immediately after reproducing that it is STILL degenerate at
   the OLD `J=(1,0)` (`plusData_wJ10_eq_wiredData_wJ10`, the exact defect, kept visible rather than
   quietly deleted). §3 then exhibits FIVE further mutations — a genuine magnitude-changing `Q`
   mutation (not a sign flip, since `s²=1` makes a mere sign flip of `Rconj` ALGEBRAICALLY FORCED to
   leave `Comp` invariant, an S82 finding worth stating explicitly), a `G₁` mutation, an `H₁`-shape
   mutation, the pre-existing `D̃⁽²⁾` mutation, and a `J`-value mutation — each proved to change the
   headline value against the SAME `wJ2` baseline.
2. **OVERCLAIMED DISTINCTNESS.** §4 below DROPS "provably distinct from `Δ^η`" and states the
   honest content plainly: `deltaKForm` and `DeltaKFull.deltaKQuadFormCorrected` differ BY
   CONSTRUCTION (three terms with a free `a`-parameter vs. two terms with none) — an arity/signature
   difference, not a proved inequality of operators at a shared type. No claim of structural
   distinctness is made.
3. **STALE ARITHMETIC.** Not reproduced here: every number below is computed fresh, in this file,
   against ITS OWN theorem statements — no inherited "-a" vs "8/7-a" mismatch is possible because no
   prose here states a number without immediately being the LHS of the theorem beside it.
4. **LEAF ANCHORING.** §5 states plainly, with no upgrade attempted beyond what §6's subspace section
   achieves: `wG0`/`wP` (standing for CMP99b's `G₀`/`Δ'_π+Δ⁽²⁾_π`) and `QData.Rconj` remain FREE
   parameters — `CovarianceG1.lean` itself does not build them (its own docstring says so), and
   `Rconj` carries no orthogonality/holonomy law (`CovarianceG1.lean` §1b's own named residual). No
   claim of "wired to the source lattice" is made for these. What DOES anchor further in this file:
   §6's `Q₁`-clause uses `QOne.qOnePathSumLM` — a genuinely page-derived (CMP96 p.245, `(★)`),
   NOT-free construction, replacing any use of `BackgroundAveraging.q1Kernel`
   (**CONVICTED wrong-object, commit `09ab9237`, Sol grade 2, discovered AFTER this dispatch was
   written — see §6's own note**).

## §6 pre-note — why `BackgroundAveraging.q1Kernel` is NOT used here

The dispatch instructed: if a rebuilt `Q1Real.lean` exists, use its kernel; otherwise fall back to
`BackgroundAveraging.q1Kernel`, parametrically, with an explicit note that it "consumes the
(being-rebuilt) `Q₁`." Neither condition is followed literally, for a reason found DURING this
build, not before it: `Q1Real.lean` does not exist, but `git log` shows `BackgroundAveraging`'s own
`Q1LM`/`q1Kernel` (the `U`-dependent, background-field construction) was **CONVICTED wrong-object**
by Sol in commit `09ab9237` (same day, hours before this dispatch), for pulling a single fixed
conjugation `R0(U)` outside a sum that CMP98 (58) keeps INSIDE, per a page (CMP98 pp.27-28) outside
that build's own citation chain. Using it here — even "parametrically, with a note" — would silently
launder a known-wrong-object into a fresh artifact's headline claim. `QOne.lean`'s
`qOnePathSumLM`/`qOnePathSum` is a **different, NOT-convicted** construction: the abelian/`U=1`
path-dependent `(★)`-sum Q₁ (CMP96 p.245, direct page derivation), which Sol's OWN commit message
explicitly states SURVIVES ("At `U=1`: the ABELIAN `Q'₁` excludes the spike, `+1/16`, genuine, scout
+ Sol, 2 families. SURVIVES."). This file therefore uses `QOne.qOnePathSumLM`'s kernel as the
`(3.156)` `Q₁`-clause, under the EXPLICIT, NAMED restriction that it is the abelian/`U=1` instance,
not the full background-field `Q₁(U)` (which remains genuinely open — `QOne.lean`'s own header
already says `Q₁(U) = Q'₁ + F_{2,1}(U)` is not fully built). Stated, not hidden.

## What this file builds

* §1 — imports/reuses `deltaKForm`, `wiredData`, and every ingredient from `DeltaKAssembly.lean`
  unchanged (LAW-19).
* §2 — the REPAIRED witness `wJ2`, the headline value at `wJ2`, and the exact "Sol repair"
  before/after pair (`plusData` degenerate at old `J`, non-degenerate at `wJ2`).
* §3 — five further mutations (`Q` by magnitude, `G₁`, `H₁`-shape, `D̃⁽²⁾`, `J`-value), each proved to
  change the value against the `wJ2` baseline — S82 discipline, non-degeneracy honestly earned.
* §4 — the honest, de-escalated distinctness statement (arity/signature only).
* §5 — the leaf-anchoring disclosure (prose, no new claims).
* §6 — the real `(3.156)` subspace: `LambdaComplementLocus` (Λᶜ-vanishing), reusing
  `AxialContour.AxUnionLocus` (Ax-vanishing) and `QOne.qOnePathSumLM`'s kernel (`Q₁`-vanishing, at
  `U=1`), assembled as `subspace156`, plus the generic restriction machinery `deltaKFormOnSubspace`
  — and the NAMED, undischarged residual connecting the two (§6's closing note).
-/

namespace AdalyFormal.Balaban.DeltaKAssemblyRepaired

open AdalyFormal.Balaban.DeltaKAssembly
open AdalyFormal.Balaban.CovarianceG1
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  solutionOperator_apply)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape taylorQuadraticTerm)
open Matrix WithLp

/-! ## §2 — THE REPAIRED WITNESS `wJ2`, and the exact Sol-repair before/after -/

/-- **The repaired background source**: BOTH `Fine`-coordinates nonzero, unlike `DeltaKAssembly
.wJ = (1,0)`. This is the entire fix to Sol's D-defect: `wH1`'s output changes in EITHER coordinate
under a genuine mutation, and `wJ2` reads both. -/
noncomputable def wJ2 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 1]

theorem wJ2_apply : WithLp.ofLp wJ2 = ![(1:ℝ), 1] := rfl

/-- **`⟨H₁D̃⁽²⁾(B), wJ2⟩ = 2/7`** — both coordinates of `wH1_wDtilde2_wB = (8/7,-6/7)` contribute. -/
theorem inner_wH1_wDtilde2_wB_wJ2 :
    (inner ℝ (wH1 (Dtilde2Shape wQext wB)) wJ2 : ℝ) = 2 / 7 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, wH1_wDtilde2_wB, wJ2_apply]
  simp only [dotProduct, Fin.sum_univ_two, star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **THE REPAIRED HEADLINE**: `deltaKForm wiredData bc wQext wJ2 wB = 4/7 - a`, for any `bc`. -/
theorem deltaKForm_wiredData_wJ2_eq (bc : BaseConstant) :
    deltaKForm wiredData bc wQext wJ2 wB = 4 / 7 - usedAt bc 0 := by
  show (inner ℝ wB (wCompInv wB) : ℝ) - usedAt bc 0 * (inner ℝ wB wB : ℝ)
    - 2 * (inner ℝ (wH1 (Dtilde2Shape wQext wB)) wJ2 : ℝ) = 4 / 7 - usedAt bc 0
  rw [inner_wB_wCompInv_wB, inner_wB_wB, inner_wH1_wDtilde2_wB_wJ2]
  ring

#print axioms wJ2_apply
#print axioms inner_wH1_wDtilde2_wB_wJ2
#print axioms deltaKForm_wiredData_wJ2_eq

/-! ### §2a — reproducing Sol's OWN mutation (`Rconj : (id,−id) ↦ (id,id)`), kept visible as
"still degenerate at the OLD `J`", then repaired at `wJ2` -/

/-- **`plusData`'s `QData`** — Sol's exact exhibit (`Rconj` with NO sign flip). Reused field-for-
field from `SOL_VERDICT.md`'s own construction, not reinvented. -/
noncomputable def wQDataPlus : QData (Fin 2) (Fin 1) ℝ where
  B := fun _ => Finset.univ
  L := 2
  d := 1
  card_block := fun _ => by decide
  Rconj := fun _ _ => LinearMap.id

noncomputable def wQL2Plus : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm.toLinearMap ∘ₗ
    (QLinearMap wQDataPlus) ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap

noncomputable def wQCLMPlus : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  LinearMap.toContinuousLinearMap wQL2Plus

theorem wQCLMPlus_apply (v : EuclideanSpace ℝ (Fin 2)) :
    WithLp.ofLp (wQCLMPlus v) = ![(WithLp.ofLp v 0 + WithLp.ofLp v 1) / 2] := by
  show WithLp.ofLp (wQL2Plus v) = _
  show WithLp.ofLp ((WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm
    (QLinearMap wQDataPlus (WithLp.ofLp v))) = _
  rw [WithLp.coe_symm_linearEquiv, WithLp.toLp_ofLp, QLinearMap_apply]
  funext i
  fin_cases i
  show QMap wQDataPlus (WithLp.ofLp v) 0 = _
  unfold QMap wQDataPlus
  simp [Fin.sum_univ_two]
  ring

noncomputable def wQstarPlus : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(1/2:ℝ); (1/2:ℝ)])

theorem wQstarPlus_apply (t : EuclideanSpace ℝ (Fin 1)) :
    WithLp.ofLp (wQstarPlus t) = ![WithLp.ofLp t 0 / 2, WithLp.ofLp t 0 / 2] := by
  unfold wQstarPlus
  rw [matCLM_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> ring

theorem wQPlus_Qstar_adjoint (v : EuclideanSpace ℝ (Fin 2)) (w : EuclideanSpace ℝ (Fin 1)) :
    (inner ℝ (wQCLMPlus v) w : ℝ) = inner ℝ v (wQstarPlus w) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    wQCLMPlus_apply, wQstarPlus_apply]
  simp only [dotProduct, Fin.sum_univ_one, Fin.sum_univ_two, star_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **`Comp` is UNCHANGED under the sign flip: `7/8`, algebraically FORCED** (S82 finding, worth
stating explicitly: `wComp_eq`'s composite depends on `Rconj`'s square, `s²`, which is `1` for BOTH
`s=-1` (`wQData`) and `s=1` (`wQDataPlus`) — a sign-flip mutation of `Rconj` can NEVER move `Comp`
in this witness, no matter what `J` is used; this is exactly why the D-defect needed a `Q`-MAGNITUDE
mutation, not a second sign-flip mutation, to be genuinely repaired in §3 below). -/
theorem wCompPlus_eq (t : EuclideanSpace ℝ (Fin 1)) : wComp t = wQCLMPlus (wG1 (wQstarPlus t)) := by
  apply WithLp.ofLp_injective 2
  rw [wQCLMPlus_apply]
  have hQstar := wQstarPlus_apply t
  have hG1 : WithLp.ofLp (wG1 (wQstarPlus t)) = ![2 * WithLp.ofLp (wQstarPlus t) 0,
      (3/2) * WithLp.ofLp (wQstarPlus t) 1] := by
    rw [wG1_eq']
    unfold diagCLM
    rw [matCLM_apply]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hG1]
  simp only [wComp, _root_.smul_apply, ContinuousLinearMap.id_apply, WithLp.ofLp_smul]
  funext i
  fin_cases i
  show (7/8 : ℝ) * WithLp.ofLp t 0 =
      (![2 * WithLp.ofLp (wQstarPlus t) 0, (3/2) * WithLp.ofLp (wQstarPlus t) 1] 0 +
        ![2 * WithLp.ofLp (wQstarPlus t) 0, (3/2) * WithLp.ofLp (wQstarPlus t) 1] 1) / 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hQstar]
  simp
  ring

noncomputable def plusData : BalabanCovarianceData
    (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1)) where
  Ginv := wGinv
  Gstar := wG1
  Ginv_Gstar := wGinv_wG1
  Gstar_Ginv := wG1_wGinv
  Ginv_selfAdjoint := wGinv_selfAdjoint
  Ginv_posSemidef := wGinv_posSemidef
  Q := wQCLMPlus
  Qstar := wQstarPlus
  Q_Qstar_adjoint := wQPlus_Qstar_adjoint
  Comp := wComp
  Comp_eq := wCompPlus_eq
  CompInv := wCompInv
  Comp_CompInv := wComp_wCompInv
  CompInv_Comp := wCompInv_wComp

#print axioms wQCLMPlus_apply
#print axioms wQstarPlus_apply
#print axioms wQPlus_Qstar_adjoint
#print axioms wCompPlus_eq
#print axioms plusData

/-- **`H₁` under `plusData`: `(8/7,6/7)`** — the second coordinate's SIGN flips relative to
`wiredData`'s `(8/7,-6/7)` (`wQstarPlus` has no sign flip), exactly Sol's finding. -/
theorem plusH1_wDtilde2_wB :
    WithLp.ofLp (solutionOperator plusData (Dtilde2Shape wQext wB)) = ![(8:ℝ)/7, 6/7] := by
  rw [wDtilde2_wB, solutionOperator_apply]
  show WithLp.ofLp (wG1 (wQstarPlus (wCompInv wB))) = _
  have hCompInv : WithLp.ofLp (wCompInv wB) = ![(8:ℝ)/7] := by
    show WithLp.ofLp ((8/7:ℝ) • wB) = _
    unfold wB; funext i; fin_cases i; simp
  have hQstar : WithLp.ofLp (wQstarPlus (wCompInv wB)) = ![(4:ℝ)/7, 4/7] := by
    rw [wQstarPlus_apply, hCompInv]
    funext i
    fin_cases i <;> simp <;> norm_num
  rw [wG1_eq']
  unfold diagCLM
  rw [matCLM_apply, hQstar]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

theorem inner_plusH1_wDtilde2_wB_wJ :
    (inner ℝ (solutionOperator plusData (Dtilde2Shape wQext wB)) wJ : ℝ) = 8 / 7 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, plusH1_wDtilde2_wB]
  unfold wJ
  simp only [dotProduct, Fin.sum_univ_two, star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem inner_plusH1_wDtilde2_wB_wJ2 :
    (inner ℝ (solutionOperator plusData (Dtilde2Shape wQext wB)) wJ2 : ℝ) = 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, plusH1_wDtilde2_wB, wJ2_apply]
  simp only [dotProduct, Fin.sum_univ_two, star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem inner_wB_plusData_CompInv_wB : (inner ℝ wB (plusData.CompInv wB) : ℝ) = 8 / 7 :=
  inner_wB_wCompInv_wB

/-- **§ THE DEFECT, REPRODUCED (not deleted): at the OLD `J = wJ` (`= (1,0)`), `plusData` and
`wiredData` STILL give the SAME headline value** — the sign flip lands in the second coordinate,
`wJ` never reads it. This is Sol's exact finding, kept as a visible fact rather than quietly made
to disappear when the witness is repaired. -/
theorem deltaKForm_plusData_wJ_eq_wiredData_wJ (bc : BaseConstant) :
    deltaKForm plusData bc wQext wJ wB = deltaKForm wiredData bc wQext wJ wB := by
  show (inner ℝ wB (wCompInv wB) : ℝ) - usedAt bc 0 * (inner ℝ wB wB : ℝ)
      - 2 * (inner ℝ (solutionOperator plusData (Dtilde2Shape wQext wB)) wJ : ℝ)
    = (inner ℝ wB (wCompInv wB) : ℝ) - usedAt bc 0 * (inner ℝ wB wB : ℝ)
      - 2 * (inner ℝ (wH1 (Dtilde2Shape wQext wB)) wJ : ℝ)
  rw [inner_plusH1_wDtilde2_wB_wJ, inner_wH1_wDtilde2_wB_wJ]

#print axioms plusH1_wDtilde2_wB
#print axioms inner_plusH1_wDtilde2_wB_wJ
#print axioms inner_plusH1_wDtilde2_wB_wJ2
#print axioms inner_wB_plusData_CompInv_wB
#print axioms deltaKForm_plusData_wJ_eq_wiredData_wJ

/-- **THE REPAIR, CONFIRMED: at `wJ2`, the SAME mutation NOW changes the value.** -/
theorem deltaKForm_plusData_wJ2_ne_wiredData_wJ2 (bc : BaseConstant) :
    deltaKForm plusData bc wQext wJ2 wB ≠ deltaKForm wiredData bc wQext wJ2 wB := by
  have hplus : deltaKForm plusData bc wQext wJ2 wB = 8 / 7 - usedAt bc 0 - 2 * 2 := by
    rw [deltaKForm_eq_CMP99b_3_156, inner_wB_plusData_CompInv_wB, inner_wB_wB,
      inner_plusH1_wDtilde2_wB_wJ2]
    ring
  rw [hplus, deltaKForm_wiredData_wJ2_eq]
  intro h
  linarith

#print axioms deltaKForm_plusData_wJ2_ne_wiredData_wJ2

/-! ## §3 — FIVE FURTHER MUTATIONS AT `wJ2`: `Q` (by magnitude), `G₁`, `H₁`-shape, `D̃⁽²⁾`, `J` -/

/-! ### §3a — `Q` mutation BY MAGNITUDE (not sign) — the genuine repair of the S82 finding in §2a:
a sign flip of `Rconj` is algebraically forced to leave `Comp` unchanged (`s²=1`); scaling `Rconj`
is NOT forced, and does move `Comp`. -/

/-- **`wQData2`**: `Rconj 1 := (-2) • id`, a genuine MAGNITUDE change (not a sign flip). This is a
deliberately non-physical mutation (`QData.Rconj` carries no orthogonality/conjugation law in this
formalization — `CovarianceG1.lean` §1b's own named residual — so nothing in the TYPE forbids it);
its role here is purely to exhibit that `Q`'s specific values, not merely its arity, are
load-bearing (S82 garbage substitution), not to model a physically valid alternative `Q`. -/
noncomputable def wQData2 : QData (Fin 2) (Fin 1) ℝ where
  B := fun _ => Finset.univ
  L := 2
  d := 1
  card_block := fun _ => by decide
  Rconj := fun _ x => if x = 0 then LinearMap.id else (-2 : ℝ) • LinearMap.id

noncomputable def wQL2_2 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm.toLinearMap ∘ₗ
    (QLinearMap wQData2) ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap

noncomputable def wQCLM2 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  LinearMap.toContinuousLinearMap wQL2_2

theorem wQCLM2_apply (v : EuclideanSpace ℝ (Fin 2)) :
    WithLp.ofLp (wQCLM2 v) = ![WithLp.ofLp v 0 / 2 - WithLp.ofLp v 1] := by
  show WithLp.ofLp (wQL2_2 v) = _
  show WithLp.ofLp ((WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm
    (QLinearMap wQData2 (WithLp.ofLp v))) = _
  rw [WithLp.coe_symm_linearEquiv, WithLp.toLp_ofLp, QLinearMap_apply]
  funext i
  fin_cases i
  show QMap wQData2 (WithLp.ofLp v) 0 = _
  unfold QMap wQData2
  simp [Fin.sum_univ_two]
  ring

noncomputable def wQstar2 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(1/2:ℝ); (-1:ℝ)])

theorem wQstar2_apply (t : EuclideanSpace ℝ (Fin 1)) :
    WithLp.ofLp (wQstar2 t) = ![WithLp.ofLp t 0 / 2, - WithLp.ofLp t 0] := by
  unfold wQstar2
  rw [matCLM_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> ring

theorem wQ2_Qstar_adjoint (v : EuclideanSpace ℝ (Fin 2)) (w : EuclideanSpace ℝ (Fin 1)) :
    (inner ℝ (wQCLM2 v) w : ℝ) = inner ℝ v (wQstar2 w) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    wQCLM2_apply, wQstar2_apply]
  simp only [dotProduct, Fin.sum_univ_one, Fin.sum_univ_two, star_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **`Comp2 := 2 • id`, hand-computed: `Q₂(G₁(Q₂*(t))) = Q₂(t,-3t/2) = t/2-(-3t/2) = 2t`** — GENUINELY
different from `wComp = 7/8`, confirming the magnitude mutation IS load-bearing (unlike §2a's sign
flip). -/
noncomputable def wComp2 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))

noncomputable def wCompInv2 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))

theorem wComp2_eq (t : EuclideanSpace ℝ (Fin 1)) : wComp2 t = wQCLM2 (wG1 (wQstar2 t)) := by
  apply WithLp.ofLp_injective 2
  rw [wQCLM2_apply]
  have hQstar := wQstar2_apply t
  have hG1 : WithLp.ofLp (wG1 (wQstar2 t)) = ![2 * WithLp.ofLp (wQstar2 t) 0,
      (3/2) * WithLp.ofLp (wQstar2 t) 1] := by
    rw [wG1_eq']
    unfold diagCLM
    rw [matCLM_apply]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hG1]
  simp only [wComp2, _root_.smul_apply, ContinuousLinearMap.id_apply, WithLp.ofLp_smul]
  funext i
  fin_cases i
  show (2 : ℝ) * WithLp.ofLp t 0 =
      ![2 * WithLp.ofLp (wQstar2 t) 0, (3/2) * WithLp.ofLp (wQstar2 t) 1] 0 / 2 -
        ![2 * WithLp.ofLp (wQstar2 t) 0, (3/2) * WithLp.ofLp (wQstar2 t) 1] 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hQstar]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem wComp2_wCompInv2 (t : EuclideanSpace ℝ (Fin 1)) : wComp2 (wCompInv2 t) = t := by
  simp only [wComp2, wCompInv2, _root_.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
  norm_num

theorem wCompInv2_wComp2 (t : EuclideanSpace ℝ (Fin 1)) : wCompInv2 (wComp2 t) = t := by
  simp only [wComp2, wCompInv2, _root_.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
  norm_num

noncomputable def wiredDataQMut : BalabanCovarianceData
    (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1)) where
  Ginv := wGinv
  Gstar := wG1
  Ginv_Gstar := wGinv_wG1
  Gstar_Ginv := wG1_wGinv
  Ginv_selfAdjoint := wGinv_selfAdjoint
  Ginv_posSemidef := wGinv_posSemidef
  Q := wQCLM2
  Qstar := wQstar2
  Q_Qstar_adjoint := wQ2_Qstar_adjoint
  Comp := wComp2
  Comp_eq := wComp2_eq
  CompInv := wCompInv2
  Comp_CompInv := wComp2_wCompInv2
  CompInv_Comp := wCompInv2_wComp2

#print axioms wQCLM2_apply
#print axioms wQstar2_apply
#print axioms wQ2_Qstar_adjoint
#print axioms wComp2_eq
#print axioms wComp2_wCompInv2
#print axioms wCompInv2_wComp2
#print axioms wiredDataQMut

theorem inner_wB_wCompInv2_wB : (inner ℝ wB (wCompInv2 wB) : ℝ) = 1 / 2 := by
  have h : WithLp.ofLp (wCompInv2 wB) = ![(1:ℝ)/2] := by
    show WithLp.ofLp ((1/2:ℝ) • wB) = _
    unfold wB; funext i; fin_cases i; simp
  rw [EuclideanSpace.inner_eq_star_dotProduct, h]
  unfold wB
  simp [dotProduct]
#print axioms inner_wB_wCompInv2_wB

theorem qmutH1_wDtilde2_wB :
    WithLp.ofLp (solutionOperator wiredDataQMut (Dtilde2Shape wQext wB)) = ![(1:ℝ)/2, -3/4] := by
  rw [wDtilde2_wB, solutionOperator_apply]
  show WithLp.ofLp (wG1 (wQstar2 (wCompInv2 wB))) = _
  have hCompInv : WithLp.ofLp (wCompInv2 wB) = ![(1:ℝ)/2] := by
    show WithLp.ofLp ((1/2:ℝ) • wB) = _
    unfold wB; funext i; fin_cases i; simp
  have hQstar : WithLp.ofLp (wQstar2 (wCompInv2 wB)) = ![(1:ℝ)/4, -1/2] := by
    rw [wQstar2_apply, hCompInv]
    funext i
    fin_cases i <;> simp <;> norm_num
  rw [wG1_eq']
  unfold diagCLM
  rw [matCLM_apply, hQstar]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

theorem inner_qmutH1_wDtilde2_wB_wJ2 :
    (inner ℝ (solutionOperator wiredDataQMut (Dtilde2Shape wQext wB)) wJ2 : ℝ) = -1 / 4 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, qmutH1_wDtilde2_wB, wJ2_apply]
  simp only [dotProduct, Fin.sum_univ_two, star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **`Q` MUTATION CHANGES THE VALUE**: `deltaKForm wiredDataQMut bc wQext wJ2 wB = 1 - a ≠ 4/7 - a
= deltaKForm wiredData bc wQext wJ2 wB`. -/
theorem deltaKForm_wiredDataQMut_wJ2_ne (bc : BaseConstant) :
    deltaKForm wiredDataQMut bc wQext wJ2 wB ≠ deltaKForm wiredData bc wQext wJ2 wB := by
  have heq : deltaKForm wiredDataQMut bc wQext wJ2 wB = 1 - usedAt bc 0 := by
    rw [deltaKForm_eq_CMP99b_3_156]
    have hcomp : (inner ℝ wB (wiredDataQMut.CompInv wB) : ℝ) = 1 / 2 := inner_wB_wCompInv2_wB
    rw [hcomp, inner_wB_wB, inner_qmutH1_wDtilde2_wB_wJ2]
    ring
  rw [heq, deltaKForm_wiredData_wJ2_eq]
  intro h
  have : (1:ℝ) - usedAt bc 0 = 4/7 - usedAt bc 0 := h
  norm_num at this

#print axioms qmutH1_wDtilde2_wB
#print axioms inner_qmutH1_wDtilde2_wB_wJ2
#print axioms deltaKForm_wiredDataQMut_wJ2_ne

/-! ### §3b — `G₁` mutation (a different `wP`, the real construction's own input) -/

/-- `wP2 := diag(1/3, 1/4)`, a different `G₁`-input from `DeltaKAssembly.wP = diag(1/2,1/3)`. -/
noncomputable def wP2 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  diagCLM (1 / 3) (1 / 4)

/-- **THE MUTATED `G₁`, computed**: `gOneOfNeumann wG0 wP2 = diag(3/2, 4/3)`. -/
theorem wG1_2_eq : gOneOfNeumann wG0 wP2 = diagCLM (3 / 2) (4 / 3) := by
  unfold gOneOfNeumann wG0 wP2
  have hPG0 : diagCLM (1/3 : ℝ) (1/4) * diagCLM (1:ℝ) 1 = diagCLM (1/3) (1/4) := by
    rw [diagCLM_mul]; norm_num
  rw [hPG0, ← diagCLM_one, diagCLM_sub]
  have hsub : (1:ℝ) - 1/3 = 2/3 := by norm_num
  have hsub2 : (1:ℝ) - 1/4 = 3/4 := by norm_num
  rw [hsub, hsub2, ring_inverse_diagCLM (2/3) (3/4) (by norm_num) (by norm_num)]
  have e1 : (2/3:ℝ)⁻¹ = 3/2 := by norm_num
  have e2 : (3/4:ℝ)⁻¹ = 4/3 := by norm_num
  rw [e1, e2, diagCLM_one, one_mul]

#print axioms wG1_2_eq

noncomputable def wG1Mut : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  gOneOfNeumann wG0 wP2

theorem wG1Mut_eq' : wG1Mut = diagCLM (3 / 2) (4 / 3) := wG1_2_eq
#print axioms wG1Mut_eq'

noncomputable def wGinvMut : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  diagCLM (2 / 3) (3 / 4)

theorem wGinvMut_wG1Mut (x : EuclideanSpace ℝ (Fin 2)) : wGinvMut (wG1Mut x) = x := by
  have h : wGinvMut * wG1Mut = 1 := by
    rw [wG1Mut_eq']; unfold wGinvMut; rw [diagCLM_mul]
    have e1 : (2/3:ℝ) * (3/2) = 1 := by norm_num
    have e2 : (3/4:ℝ) * (4/3) = 1 := by norm_num
    rw [e1, e2]; exact diagCLM_one
  exact DFunLike.congr_fun h x
#print axioms wGinvMut_wG1Mut

theorem wG1Mut_wGinvMut (x : EuclideanSpace ℝ (Fin 2)) : wG1Mut (wGinvMut x) = x := by
  have h : wG1Mut * wGinvMut = 1 := by
    rw [wG1Mut_eq']; unfold wGinvMut; rw [diagCLM_mul]
    have e1 : (3/2:ℝ) * (2/3) = 1 := by norm_num
    have e2 : (4/3:ℝ) * (3/4) = 1 := by norm_num
    rw [e1, e2]; exact diagCLM_one
  exact DFunLike.congr_fun h x
#print axioms wG1Mut_wGinvMut

theorem wGinvMut_selfAdjoint (x y : EuclideanSpace ℝ (Fin 2)) :
    (inner ℝ (wGinvMut x) y : ℝ) = inner ℝ x (wGinvMut y) := by
  unfold wGinvMut diagCLM
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    matCLM_apply, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring
#print axioms wGinvMut_selfAdjoint

theorem wGinvMut_posSemidef (x : EuclideanSpace ℝ (Fin 2)) :
    (0 : ℝ) ≤ inner ℝ x (wGinvMut x) := by
  unfold wGinvMut diagCLM
  rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, mul_comm]
  nlinarith [sq_nonneg (WithLp.ofLp x 0), sq_nonneg (WithLp.ofLp x 1)]
#print axioms wGinvMut_posSemidef

/-- **`Comp3 := (17/24) • id`, hand-computed**, from `wQCLM`/`wQstar` (the ORIGINAL, UNMUTATED
`Q`) composed with the MUTATED `wG1Mut`. -/
noncomputable def wComp3 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (17 / 24 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))

noncomputable def wCompInv3 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (24 / 17 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))

theorem wComp3_eq (t : EuclideanSpace ℝ (Fin 1)) : wComp3 t = wQCLM (wG1Mut (wQstar t)) := by
  apply WithLp.ofLp_injective 2
  rw [wQCLM_apply]
  have hQstar := wQstar_apply t
  have hG1 : WithLp.ofLp (wG1Mut (wQstar t)) = ![(3/2) * WithLp.ofLp (wQstar t) 0,
      (4/3) * WithLp.ofLp (wQstar t) 1] := by
    rw [wG1Mut_eq']
    unfold diagCLM
    rw [matCLM_apply]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hG1]
  simp only [wComp3, _root_.smul_apply, ContinuousLinearMap.id_apply, WithLp.ofLp_smul]
  funext i
  fin_cases i
  show (17/24 : ℝ) * WithLp.ofLp t 0 =
      (![(3/2) * WithLp.ofLp (wQstar t) 0, (4/3) * WithLp.ofLp (wQstar t) 1] 0 -
        ![(3/2) * WithLp.ofLp (wQstar t) 0, (4/3) * WithLp.ofLp (wQstar t) 1] 1) / 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hQstar]
  simp
  ring

theorem wComp3_wCompInv3 (t : EuclideanSpace ℝ (Fin 1)) : wComp3 (wCompInv3 t) = t := by
  simp only [wComp3, wCompInv3, _root_.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
  norm_num

theorem wCompInv3_wComp3 (t : EuclideanSpace ℝ (Fin 1)) : wCompInv3 (wComp3 t) = t := by
  simp only [wComp3, wCompInv3, _root_.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
  norm_num

noncomputable def wiredDataGMut : BalabanCovarianceData
    (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1)) where
  Ginv := wGinvMut
  Gstar := wG1Mut
  Ginv_Gstar := wGinvMut_wG1Mut
  Gstar_Ginv := wG1Mut_wGinvMut
  Ginv_selfAdjoint := wGinvMut_selfAdjoint
  Ginv_posSemidef := wGinvMut_posSemidef
  Q := wQCLM
  Qstar := wQstar
  Q_Qstar_adjoint := wQ_Qstar_adjoint
  Comp := wComp3
  Comp_eq := wComp3_eq
  CompInv := wCompInv3
  Comp_CompInv := wComp3_wCompInv3
  CompInv_Comp := wCompInv3_wComp3

#print axioms wComp3_eq
#print axioms wComp3_wCompInv3
#print axioms wCompInv3_wComp3
#print axioms wiredDataGMut

theorem inner_wB_wCompInv3_wB : (inner ℝ wB (wCompInv3 wB) : ℝ) = 24 / 17 := by
  have h : WithLp.ofLp (wCompInv3 wB) = ![(24:ℝ)/17] := by
    show WithLp.ofLp ((24/17:ℝ) • wB) = _
    unfold wB; funext i; fin_cases i; simp
  rw [EuclideanSpace.inner_eq_star_dotProduct, h]
  unfold wB
  simp [dotProduct]
#print axioms inner_wB_wCompInv3_wB

theorem gmutH1_wDtilde2_wB :
    WithLp.ofLp (solutionOperator wiredDataGMut (Dtilde2Shape wQext wB)) = ![(18:ℝ)/17, -16/17] := by
  rw [wDtilde2_wB, solutionOperator_apply]
  show WithLp.ofLp (wG1Mut (wQstar (wCompInv3 wB))) = _
  have hCompInv : WithLp.ofLp (wCompInv3 wB) = ![(24:ℝ)/17] := by
    show WithLp.ofLp ((24/17:ℝ) • wB) = _
    unfold wB; funext i; fin_cases i; simp
  have hQstar : WithLp.ofLp (wQstar (wCompInv3 wB)) = ![(12:ℝ)/17, -12/17] := by
    rw [wQstar_apply, hCompInv]
    funext i
    fin_cases i <;> simp <;> norm_num
  rw [wG1Mut_eq']
  unfold diagCLM
  rw [matCLM_apply, hQstar]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

theorem inner_gmutH1_wDtilde2_wB_wJ2 :
    (inner ℝ (solutionOperator wiredDataGMut (Dtilde2Shape wQext wB)) wJ2 : ℝ) = 2 / 17 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, gmutH1_wDtilde2_wB, wJ2_apply]
  simp only [dotProduct, Fin.sum_univ_two, star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **`G₁` MUTATION CHANGES THE VALUE**: `deltaKForm wiredDataGMut bc wQext wJ2 wB = 20/17 - a ≠
4/7 - a`. -/
theorem deltaKForm_wiredDataGMut_wJ2_ne (bc : BaseConstant) :
    deltaKForm wiredDataGMut bc wQext wJ2 wB ≠ deltaKForm wiredData bc wQext wJ2 wB := by
  have heq : deltaKForm wiredDataGMut bc wQext wJ2 wB = 20 / 17 - usedAt bc 0 := by
    rw [deltaKForm_eq_CMP99b_3_156]
    have hcomp : (inner ℝ wB (wiredDataGMut.CompInv wB) : ℝ) = 24/17 := inner_wB_wCompInv3_wB
    rw [hcomp, inner_wB_wB, inner_gmutH1_wDtilde2_wB_wJ2]
    ring
  rw [heq, deltaKForm_wiredData_wJ2_eq]
  intro h
  have : (20:ℝ)/17 - usedAt bc 0 = 4/7 - usedAt bc 0 := h
  norm_num at this

#print axioms gmutH1_wDtilde2_wB
#print axioms inner_gmutH1_wDtilde2_wB_wJ2
#print axioms deltaKForm_wiredDataGMut_wJ2_ne

/-! ### §3c — `H₁`-SHAPE mutation: swap `solutionOperator wiredData` (`= G₁∘Q*∘CompInv`) for
`wQstar` alone, at FIXED `wiredData` — shows `H₁`'s OWN composition (not merely its `Q`/`G₁`
ingredients in isolation) is load-bearing. -/

theorem inner_wQstar_wDtilde2_wB_wJ2 :
    (inner ℝ (wQstar (Dtilde2Shape wQext wB)) wJ2 : ℝ) = 0 := by
  rw [wDtilde2_wB, EuclideanSpace.inner_eq_star_dotProduct, wQstar_apply, wJ2_apply]
  unfold wB
  simp only [dotProduct, Fin.sum_univ_two, star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **`H₁`-SHAPE MUTATION CHANGES THE VALUE**: replacing `solutionOperator wiredData` by the
alternative, SAME-TYPE (`K →L[ℝ] H`) map `wQstar` gives `8/7 - a`, not `4/7 - a`. -/
theorem deltaKForm_H1shapeMut_wJ2_ne (bc : BaseConstant) :
    ((inner ℝ wB (wCompInv wB) : ℝ) - usedAt bc 0 * (inner ℝ wB wB : ℝ)
        - 2 * (inner ℝ (wQstar (Dtilde2Shape wQext wB)) wJ2 : ℝ))
      ≠ deltaKForm wiredData bc wQext wJ2 wB := by
  rw [inner_wB_wCompInv_wB, inner_wB_wB, inner_wQstar_wDtilde2_wB_wJ2, deltaKForm_wiredData_wJ2_eq]
  intro h
  have : (8:ℝ)/7 - usedAt bc 0 * 1 - 2 * 0 = 4/7 - usedAt bc 0 := h
  norm_num at this

#print axioms inner_wQstar_wDtilde2_wB_wJ2
#print axioms deltaKForm_H1shapeMut_wJ2_ne

/-! ### §3d — `D̃⁽²⁾` mutation (`DeltaKAssembly.wQextLinear`, reused; recomputed at `wJ2`) -/

theorem deltaKForm_wiredData_wQextLinear_wJ2_eq (bc : BaseConstant) :
    deltaKForm wiredData bc wQextLinear wJ2 wB = 8 / 7 - usedAt bc 0 := by
  show (inner ℝ wB (wCompInv wB) : ℝ) - usedAt bc 0 * (inner ℝ wB wB : ℝ)
    - 2 * (inner ℝ (wH1 (Dtilde2Shape wQextLinear wB)) wJ2 : ℝ) = 8 / 7 - usedAt bc 0
  rw [inner_wB_wCompInv_wB, inner_wB_wB, wDtilde2_wQextLinear_eq_zero]
  simp

/-- **`D̃⁽²⁾` MUTATION CHANGES THE VALUE** (again, now against the `wJ2` baseline): `8/7 - a ≠
4/7 - a`. -/
theorem deltaKForm_wQextLinear_wJ2_ne (bc : BaseConstant) :
    deltaKForm wiredData bc wQextLinear wJ2 wB ≠ deltaKForm wiredData bc wQext wJ2 wB := by
  rw [deltaKForm_wiredData_wQextLinear_wJ2_eq, deltaKForm_wiredData_wJ2_eq]
  intro h
  have : (8:ℝ)/7 - usedAt bc 0 = 4/7 - usedAt bc 0 := h
  norm_num at this

#print axioms deltaKForm_wiredData_wQextLinear_wJ2_eq
#print axioms deltaKForm_wQextLinear_wJ2_ne

/-! ### §3e — `J` VALUE mutation (`wJ2 ↦ wJ`, `DeltaKAssembly`'s own old witness, reused) -/

theorem deltaKForm_wiredData_wJ_wJ2_ne (bc : BaseConstant) :
    deltaKForm wiredData bc wQext wJ wB ≠ deltaKForm wiredData bc wQext wJ2 wB := by
  rw [deltaKForm_wiredData_eq, deltaKForm_wiredData_wJ2_eq]
  intro h
  have : (-8:ℝ)/7 - usedAt bc 0 = 4/7 - usedAt bc 0 := h
  norm_num at this

#print axioms deltaKForm_wiredData_wJ_wJ2_ne

/-! ### §3f — `a` MUTATION: reused directly, `deltaKForm_wiredData_strictAntitone_in_a`
(`DeltaKAssembly.lean`) already covers `a`; restated here at `wJ2` for completeness of the
six-ingredient roster. -/

theorem deltaKForm_wiredData_wJ2_strictAntitone_in_a (bc1 bc2 : BaseConstant) (h : bc1.a < bc2.a) :
    deltaKForm wiredData bc2 wQext wJ2 wB < deltaKForm wiredData bc1 wQext wJ2 wB := by
  rw [deltaKForm_wiredData_wJ2_eq, deltaKForm_wiredData_wJ2_eq]
  show 4/7 - usedAt bc2 0 < 4/7 - usedAt bc1 0
  unfold usedAt
  linarith

#print axioms deltaKForm_wiredData_wJ2_strictAntitone_in_a

/-! ## §4 — DISTINCTNESS, DE-ESCALATED: arity/signature only, no structural claim -/

/-- **The honest statement**: `deltaKForm`'s value is a NONCONSTANT function of `bc.a`
(`deltaKForm_wiredData_wJ2_strictAntitone_in_a`), while `DeltaKFull.deltaKQuadFormCorrected U A`
has NO `a`-parameter anywhere in its signature or definition (`DeltaKFull.lean` §3) — so for ANY
fixed `(U,A)`, `deltaKQuadFormCorrected U A` is a single fixed real number, structurally unable to
reproduce `deltaKForm`'s `a`-dependence. This is exactly, and ONLY, an arity/signature difference:
**no claim is made here that the two are different OPERATORS at a shared type** — there is no
common instantiation making them the same Lean type for a literal `≠` to typecheck (see
`DeltaKAssembly.lean` §5's own docstring for why forcing one would be an unfaithful shortcut). The
honest substitute is: "different by construction — three terms with a free `a` vs. two terms with
none," not "provably distinct." -/
theorem deltaKForm_has_a_dependence_deltaKQuadFormCorrected_does_not (bc1 bc2 : BaseConstant)
    (h : bc1.a < bc2.a) :
    deltaKForm wiredData bc2 wQext wJ2 wB ≠ deltaKForm wiredData bc1 wQext wJ2 wB :=
  ne_of_lt (deltaKForm_wiredData_wJ2_strictAntitone_in_a bc1 bc2 h)

#print axioms deltaKForm_has_a_dependence_deltaKQuadFormCorrected_does_not

/-! ## §5 — LEAF-ANCHORING DISCLOSURE (prose statement, no new Lean claim)

`wG0`/`wP` (`G₀`/`Δ'_π+Δ⁽²⁾_π`) and every `QData.Rconj` used above (`wQData`, `wQDataPlus`,
`wQData2`) remain FREE, hand-chosen parameters, exactly as in `DeltaKAssembly.lean`. No theorem in
this file claims otherwise. `CovarianceG1.lean` itself does not build `G0`/`P` (its own §2's own
practice), and `Rconj` carries no orthogonality/holonomy law connecting it to CMP99b's actual
`R(V(Γ_{y,x}))` (`CovarianceG1.lean` §1b's own named residual — unformalized SU(2)/lattice
instantiation). `wQext`/`wJ`/`wJ2` remain the two disclosed EXTERNAL parameters `DeltaKAssembly.lean`
§0 already names (findings 2 and 3: `D̃⁽²⁾`'s CMP99b-specific `Q_j` instantiation is blocked on
Bałaban's `[5]`/CMP98 `Ū^j` construction; `J`'s carrier convention (Hermitian `𝔤ᶜ` vs. this tree's
anti-Hermitian `SuTwo`) needs the same `φ:X↦iX` transport `CarrierBridge.lean` names as unbuilt).
The ONE genuine anchoring improvement in THIS file is §6's `Q₁`-clause: `QOne.qOnePathSumLM` is a
real, page-derived (CMP96 p.245) construction, not a free parameter — replacing any use of the
CONVICTED `BackgroundAveraging.q1Kernel` (§0's pre-note). -/

/-! ## §6 — THE REAL `(3.156)` SUBSPACE: `{B : B=0 on Λᶜ, B=0 on ∪_{y∈Λ'}Ax(y), Q₁B=0}`
(CMP99b p.428, exact wording confirmed at `corpus/pages/CMP99b_p428.md` and
`compute/kimi_omega_gate/VERDICT.md` line 131-132), assembled from three REAL clauses -/

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.AxialContour (AxUnionLocus)
open AdalyFormal.Balaban.QOne (qOnePathSumLM)

variable {Lat : PeriodicLatticeExtent}

/-- **Clause 1: `B = 0` on `Λᶜ`.** Read as "every bond whose BASE SITE lies outside `Lambda`
vanishes" (`Bond Lat := PeriodicLatticeSite Lat × Fin 3`, `b.1` its base site) — one reasonable,
stated (not silently assumed) formalization of the source's site-indexed `Λᶜ` condition applied to
a bond-indexed field; CMP99b p.428 does not spell out the site/bond correspondence for THIS specific
clause beyond what `DomainSequence.lean`/`AxialContour.lean` already establish for the other two
clauses. Same three-field `Submodule` shape as `AxialContour.AxLocus`/`AxUnionLocus` (LAW-19
precedent, not reinvented). -/
def LambdaComplementLocus (Lambda : Finset (PeriodicLatticeSite Lat)) :
    Submodule ℝ (Bond Lat → ℝ) where
  carrier := {B | ∀ b : Bond Lat, b.1 ∉ Lambda → B b = 0}
  zero_mem' := by intro b _; rfl
  add_mem' := by
    intro B1 B2 hB1 hB2 b hb
    simp [hB1 b hb, hB2 b hb]
  smul_mem' := by
    intro c B hB b hb
    simp [hB b hb]

theorem mem_LambdaComplementLocus {Lambda : Finset (PeriodicLatticeSite Lat)} {B : Bond Lat → ℝ} :
    B ∈ LambdaComplementLocus Lambda ↔ ∀ b : Bond Lat, b.1 ∉ Lambda → B b = 0 := Iff.rfl

/-- **THE `(3.156)` SUBSPACE, ASSEMBLED**: `Λᶜ`-vanishing (clause 1) `⊓` `Ax`-vanishing over the
center set `S'` (clause 2, `AxialContour.AxUnionLocus`, REUSED not rebuilt) `⊓` `Q₁`-kernel (clause
3, `QOne.qOnePathSumLM`'s kernel — the abelian/`U=1` instance, REUSED, §0's pre-note). All three
factors are REAL constructions from earlier files, not opaque stand-ins. -/
noncomputable def subspace156 (Lambda S' : Finset (PeriodicLatticeSite Lat)) (ell : ℕ) :
    Submodule ℝ (Bond Lat → ℝ) :=
  LambdaComplementLocus Lambda ⊓ AxUnionLocus S' ell ⊓ LinearMap.ker (qOnePathSumLM Lat ell)

/-- **`subspace156` is a genuine (proper, `≠⊤`) restriction whenever its `Q₁`-clause alone is
proper** — a general lattice fact (an infimum with a proper factor is proper), applied to the
CONCRETE non-degeneracy `QOne.lean` already proved at its own witness lattice
(`qOnePathSumLM_ker_ne_top`, reused, LAW-19). -/
theorem subspace156_ne_top_of_ker_ne_top {Lambda S' : Finset (PeriodicLatticeSite Lat)} {ell : ℕ}
    (h : LinearMap.ker (qOnePathSumLM Lat ell) ≠ ⊤) :
    subspace156 Lambda S' ell ≠ ⊤ := by
  intro htop
  apply h
  refine top_le_iff.mp ?_
  rw [← htop]
  unfold subspace156
  exact inf_le_right

/-- **Instantiated at `AdmissibleSubspace.witnessL`/`witnessEll`**: `subspace156` is a genuine
proper restriction there, since `QOne.qOnePathSumLM_ker_ne_top` (reused) supplies exactly the
hypothesis `subspace156_ne_top_of_ker_ne_top` needs — for ANY choice of `Lambda`, `S'` at that
lattice. -/
theorem subspace156_witnessL_ne_top (Lambda S' :
    Finset (PeriodicLatticeSite AdalyFormal.Balaban.AdmissibleSubspace.witnessL)) :
    subspace156 Lambda S' AdalyFormal.Balaban.AdmissibleSubspace.witnessEll ≠ ⊤ :=
  subspace156_ne_top_of_ker_ne_top
    AdalyFormal.Balaban.QOne.qOnePathSumLM_ker_ne_top

#print axioms mem_LambdaComplementLocus
#print axioms subspace156_ne_top_of_ker_ne_top
#print axioms subspace156_witnessL_ne_top

/-! ### §6a — `deltaKForm` RESTRICTED to a subspace: the generic machinery

Generic over ANY `(H,K)` `BalabanCovarianceData` and ANY `Submodule ℝ K` — this is real, reusable
restriction machinery, independent of which concrete subspace is supplied. -/

/-- **`deltaKForm` restricted to `S`**: literally `deltaKForm` pre-composed with the inclusion
`S ↪ K`, i.e. `deltaKForm` viewed as a function on the SUBTYPE `S`, not on all of `K`. This is the
honest Lean shape of "the form on the subspace." -/
noncomputable def deltaKFormOnSubspace {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (D : BalabanCovarianceData H K)
    (bc : BaseConstant) (Qext : K → K) (J : H) (S : Submodule ℝ K) (B : S) : ℝ :=
  deltaKForm D bc Qext J (B : K)

theorem deltaKFormOnSubspace_eq {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (D : BalabanCovarianceData H K)
    (bc : BaseConstant) (Qext : K → K) (J : H) (S : Submodule ℝ K) (B : S) :
    deltaKFormOnSubspace D bc Qext J S B = deltaKForm D bc Qext J (B : K) := rfl

#print axioms deltaKFormOnSubspace_eq

/-! ### §6b — THE NAMED, UNDISCHARGED RESIDUAL connecting §6 and §6a

**Not claimed, stated plainly.** `subspace156` lives in `Submodule ℝ (Bond Lat → ℝ)` — the REAL
fine bond-field space. `deltaKFormOnSubspace`, at the concrete `wiredData`/`plusData`/
`wiredDataQMut`/`wiredDataGMut` witnesses of §§2-3, is a function on `Submodule ℝ (EuclideanSpace ℝ
(Fin 1))` — a `1`-DIMENSIONAL TOY coarse space, not `Bond Lat → ℝ`. There is no Lean term in this
file (and none is manufactured) identifying `EuclideanSpace ℝ (Fin 1)` with (a quotient/subspace
of) `Bond Lat → ℝ` for any concrete `Lat`. This is the SAME "two-space simplification" family of
gap `DeltaKAssembly.lean` §0 already discloses for `RGScaleFamily`'s single ambient `H` — restated
here for the SUBSPACE, not silently assumed away: `deltaKFormOnSubspace wiredData bc wQext wJ2
subspace156 …` **does not typecheck** for any real `subspace156` at a concrete `Lat`, because the
two live in different types. Closing this residual requires either (a) a faithful `K := Bond Lat →
ℝ` instantiation of `BalabanCovarianceData` (blocked on the SAME leaf-anchoring gap `SOL_VERDICT.md`
names for `G₁`/`Q`'s own inputs, §5 above), or (b) a genuine `EuclideanSpace ℝ (Fin 1)`-valued
reduction of `subspace156` via an honest, source-derived projection — neither is attempted here.

**A second, separate residual, also named and not attempted**: `subspace156 ≠ ⊥` (a genuine nonzero
element satisfying ALL THREE clauses simultaneously) is NOT proved in this file. Only `≠ ⊤`
(properness) is established. A joint nonzero witness would need a bond field supported inside a
chosen `Lambda`, vanishing on `Ax(y)` for every `y ∈ S'`, AND lying in `Q₁`'s (non-local, "tent"-
weighted) kernel at every coarse bond simultaneously — genuinely harder than any one clause alone
(`QOne.lean`'s own `checkerConfig` construction, built purely to satisfy ONE such non-local
condition globally, already needed a dedicated periodic-cancellation argument; it independently
fails the OTHER two clauses, since it is nonzero on every direction-`0` bond of the whole lattice,
not merely inside `Ax(y)`'s complement). Left open rather than forced. -/

end AdalyFormal.Balaban.DeltaKAssemblyRepaired
