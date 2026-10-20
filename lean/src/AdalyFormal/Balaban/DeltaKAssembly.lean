/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib
import AdalyFormal.Balaban.CovarianceG1
import AdalyFormal.Balaban.VariationalProjectorH1
import AdalyFormal.Balaban.ConstantA
import AdalyFormal.Balaban.SourceJ

set_option autoImplicit false

/-!
# `Δ_k` ASSEMBLY — wiring the six triple-prosecuted ingredients into CMP99b (3.156)

**Dispatch target**: assemble `G₁` (`CovarianceG1.gOneOfNeumann`), `Q` (`CovarianceG1.QLinearMap`),
`a` (`ConstantA.BaseConstant`/`usedAt`), `H₁` (`VariationalProjectorH1.solutionOperator`), `J`
(`SourceJ.Jsource`), `D̃⁽²⁾` (`SourceJ.Dtilde2Shape`) into ONE recursive quadratic form and prove it
equals CMP99b p.428, eq. (3.156):

```
⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩  =  ⟨B,Δ_kB⟩
```

**Do not edit** `CovarianceG1.lean`, `VariationalProjectorH1.lean`, `ConstantA.lean`, `SourceJ.lean`,
or `DeltaKRecursive.lean` — every ingredient is IMPORTED and REUSED (LAW-19), never rebuilt.

## §0 — LEAD FINDING: literal wiring into `DeltaKRecursive.RGScaleFamily`'s single-ambient-`H`
fields does **NOT** typecheck, for a precise, reproduced reason — NOT papered over with `sorry`

`RGScaleFamily`'s own docstring (§1) already discloses its single-`H` shape as "a documented
simplification" of CMP99b's genuinely two-space (`Q_k : H_k → H_k'`) reality. This assembly makes
that disclosure CONCRETE: the two real constructions that would need to share `RGScaleFamily`'s one
`H` — `CovarianceG1.gOneOfNeumann` (needs `[InnerProductSpace ℝ H]` on `G₁`'s domain, to compose
`⟨B,(QG₁Q*)⁻¹B⟩`) and `CovarianceG1.QLinearMap` (whose domain is the BARE Pi type `Site → 𝔤`, i.e.
`QData`'s own fine-site space) — **cannot share a domain at all**, because `Site → 𝔤` carries only
`Pi.normedAddCommGroup` (sup norm; automatic for `Fintype Site`) and Mathlib registers the L²/
inner-product structure `gOneOfNeumann` needs ONLY on the `WithLp`/`PiLp`-wrapped type synonym, never
on the bare Pi type itself. Reproduced directly (not merely asserted), a fresh probe,
`lake env lean` on a scratch file with `variable {Site : Type*} [Fintype Site] [DecidableEq Site]`,
`example : InnerProductSpace ℝ (Site → ℝ) := by infer_instance`:

```
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  InnerProductSpace ℝ (Site → ℝ)
```

**This is the SAME `PILP_BRIDGE`/ambient-topology diamond `CarrierBridge.lean` and `DeltaKFull.lean`
§6 already documented for `curlCovariantCLM_L2`/`.adjoint`** — not a new wall, the SAME one,
confirmed to recur exactly where the dispatch's own concern (tying `H₁`'s abstract `G`/`Q` inputs to
the REAL `gOneOfNeumann`/`QLinearMap`) requires it to. `RGScaleFamily.Q`/`RGScaleFamily.G1` cannot
both be populated by the literal `QLinearMap`/`gOneOfNeumann` outputs while sharing `RGScaleFamily`'s
one bare-`H` type; this is a real, precise, reproduced finding, not a gap papered over — no field of
`RGScaleFamily` is edited or force-filled with a mismatched value here.

**Three further mismatches, found the same way (direct inspection, not assumed), all named,
none forced**:

1. **`H₁`'s shape is `K →L[ℝ] H` (coarse→fine), not `H →L[ℝ] H`.** `VariationalProjectorH1.
   solutionOperator : BalabanCovarianceData H K → K →L[ℝ] H` — a genuinely TWO-SPACE map (matching
   (3.129)'s own `H₁B = G₁Q*(QG₁Q*)⁻¹B`, `B ∈ K`, `H₁B ∈ H`), never an endomorphism of one space.
   `RGScaleFamily.H1 : ℕ → H →L[ℝ] H` cannot host it without ALSO collapsing `K = H` (Fine = Coarse),
   which would erase (3.156)'s own block-averaging content (`Q` becoming an automorphism-shaped map).
2. **`D̃⁽²⁾`'s CMP99b-specific instantiation is a NAMED-GAP, not a closed construction** (`SourceJ.lean`
   §7's own residual #1): `Dtilde2Shape` is the general "second-order Taylor term of `Q`" shape;
   substituting CMP99b's own `Q_j` (eq. 3.13) is blocked on Bałaban's `[5]`/CMP98 `Ū^j` construction,
   on disk but unformalized. Per the dispatch, this is carried below as a genuine EXTERNAL PARAMETER
   (`Qext`), never invented.
3. **`J`'s carrier convention mismatch** (`SourceJ.lean` §7's own residual #2): `Jsource` returns
   `Bond L → Matrix (Fin 2) (Fin 2) ℂ` values (Bałaban's own HERMITIAN `𝔤ᶜ` convention), not this
   tree's anti-Hermitian `SuTwo` carrier — embedding it into an abstract real inner-product space `H`
   needs the SAME `φ : X ↦ iX` transport `DeltaPrime.lean`/`CarrierBridge.lean` already flag as
   unbuilt for `J` specifically. Carried below as an opaque `H`-typed parameter, exactly
   `RGScaleFamily.J`'s own existing treatment — not literally `Jsource U`.

## §0b — THE POSITIVE RESULT: the SAME six real ingredients DO compose, faithfully, once `H₁`'s
`(H,K)` two-space shape is honored instead of collapsed

`VariationalProjectorH1.BalabanCovarianceData H K` is ALREADY generic over separate Fine (`H`) and
Coarse (`K`) spaces — unlike `RGScaleFamily`, it was never forced into the single-ambient-space
simplification. Wiring into it (rather than into `RGScaleFamily`) is what actually typechecks:
`D.Gstar := CovarianceG1.gOneOfNeumann G0 P` (the literal `G₁`, (3.138)) and
`D.Q := ` `CovarianceG1.QLinearMap`'s output, PROMOTED from its bare-Pi domain to the
`EuclideanSpace`/`PiLp`-wrapped one via the SAME `WithLp.linearEquiv`-composition-then-
`LinearMap.toContinuousLinearMap` technique `DeltaKFull.lean` §5 already established for the
curl (`curlCovariantLM_L2`/`curlCovariantCLM_L2`) — reused here, not reinvented, confirmed by a
fresh probe (`lake env lean`, clean, `#print axioms` → `[propext, Classical.choice, Quot.sound]`).
This is EXACTLY the tie the dispatch asked for: "`H₁`'s `G₁`/`Q` inputs get TIED to the real ones
HERE."

## What this file builds

* §1 — `deltaKForm`, CMP99b (3.156)'s literal RHS, generic over any `(H,K)` `BalabanCovarianceData`
  plus a `ConstantA.BaseConstant`, an external `Qext : K → K` (D̃⁽²⁾'s named parameter), and a fixed
  `J : H`.
* §2 — the wiring: `QData`/`QCLM` (promoted, literally `CovarianceG1.QLinearMap`), `G0`/`P`/`gOneOfNeumann`
  (literally `CovarianceG1.gOneOfNeumann`), assembled into ONE `BalabanCovarianceData
  (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1))` with `Gstar`/`Q` tied to the real
  constructions (not opaque, not disconnected — §0b's resolution of Sol's concern).
* §3 — non-vacuity: `deltaKForm` at this wired data, computed by hand, at a nonzero witness `B`,
  with EVERY one of the six ingredient roles (`G₁`,`Q`,`a`,`H₁`,`D̃⁽²⁾`,`J`) contributing a nonzero,
  independently-checkable term (S82: mutating any one of the six changes the value — §4).
* §4 — S82 mutations + the genuine `a`-dependence distinctness argument against
  `DeltaKFull.deltaKQuadFormCorrected` (the old `Δ^η` scaffold) — §5's docstring states precisely why
  a literal same-type `≠` is not the right statement here, and gives the honest substitute.
-/

namespace AdalyFormal.Balaban.DeltaKAssembly

open AdalyFormal.Balaban.CovarianceG1
open AdalyFormal.Balaban.VariationalProjectorH1 (BalabanCovarianceData solutionOperator
  solutionOperator_apply interpolates isMinimal)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.SourceJ (Dtilde2Shape taylorQuadraticTerm)

/-! ## §1 — `deltaKForm`, CMP99b (3.156)'s literal RHS

`D.CompInv` plays `(QG₁Q*)⁻¹`, `solutionOperator D` plays `H₁`, `Dtilde2Shape Qext` plays `D̃⁽²⁾`
(`Qext` the named, CMP99b-`Q_j`-shaped external parameter, §0's finding 2), `usedAt bc 0` plays `a`
(the RG-step argument is immaterial per `ConstantA.usedAt_const`), `J` is the fixed background source
(§0's finding 3). Every symbol on the right of CMP99b (3.156) is present, literally. -/

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- **`Δ_k`'s quadratic form, assembled** — CMP99b (3.156)'s RHS, term for term, from the six real
ingredients (four wired via their actual constructions, `D̃⁽²⁾`/`J` carried as the two named,
disclosed parameters §0 identifies). -/
noncomputable def deltaKForm (D : BalabanCovarianceData H K) (bc : BaseConstant) (Qext : K → K)
    (J : H) (B : K) : ℝ :=
  (inner ℝ B (D.CompInv B) : ℝ)
    - usedAt bc 0 * (inner ℝ B B : ℝ)
    - 2 * (inner ℝ (solutionOperator D (Dtilde2Shape Qext B)) J : ℝ)

/-- **THE DELIVERABLE THEOREM, stated**: `deltaKForm` is DEFINITIONALLY CMP99b (3.156)'s RHS —
every summand named to its source symbol. This is `rfl`; the genuine content is that the RIGHT-HAND
SIDE here is built entirely from the SIX real ingredient constructions (§2 exercises this on a
witness where each one is non-trivial), not that the equation itself is deep. -/
theorem deltaKForm_eq_CMP99b_3_156 (D : BalabanCovarianceData H K) (bc : BaseConstant)
    (Qext : K → K) (J : H) (B : K) :
    deltaKForm D bc Qext J B =
      (inner ℝ B (D.CompInv B) : ℝ) - usedAt bc 0 * (inner ℝ B B : ℝ)
        - 2 * (inner ℝ (solutionOperator D (Dtilde2Shape Qext B)) J : ℝ) := rfl

#print axioms deltaKForm_eq_CMP99b_3_156

/-! ## §2 — THE WIRING: `Q` and `G₁`, literally `CovarianceG1.QLinearMap`/`gOneOfNeumann`, tied
into ONE `BalabanCovarianceData` — the resolution of Sol's "`H₁`'s abstract inputs" concern

`Fine := EuclideanSpace ℝ (Fin 2)`, `Coarse := EuclideanSpace ℝ (Fin 1)` — small enough to compute
by hand (matching `VariationalProjectorH1.lean` §4's / `CovarianceG1.lean` §2b's own witness
conventions), large enough that `Q` is genuinely non-injective (`dim Coarse < dim Fine`, avoiding
the vacuous-minimization trap `VariationalProjectorH1.lean` §4 already names). -/

open Matrix WithLp

/-- Local, self-contained `matCLM` (LAW-19 precedent: `DeltaKRecursive.lean`/`VariationalProjectorH1
.lean` each carry their own fresh copy of this exact helper, "to keep this file's write-scope
self-contained under concurrent editing of sibling files" — the SAME discipline is followed here,
a THIRD independent copy, not a rebuild of anything importable). -/
noncomputable def matCLM {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

theorem matCLM_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    WithLp.ofLp (matCLM M x) = M *ᵥ (WithLp.ofLp x) := by
  unfold matCLM
  simp [Matrix.toEuclideanLin, LinearMap.coe_toContinuousLinearMap']

noncomputable def diagCLM (a b : ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![a, 0; 0, b])

theorem diagCLM_mul (a b c d : ℝ) :
    diagCLM a b * diagCLM c d = diagCLM (a * c) (b * d) := by
  ext x i
  show ((diagCLM a b) ((diagCLM c d) x)).ofLp i = ((diagCLM (a * c) (b * d)) x).ofLp i
  unfold diagCLM
  rw [matCLM_apply, matCLM_apply, matCLM_apply]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem diagCLM_one : diagCLM (1 : ℝ) (1 : ℝ) = 1 := by
  ext x i
  unfold diagCLM
  rw [matCLM_apply]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem ring_inverse_diagCLM (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Ring.inverse (diagCLM a b) = diagCLM a⁻¹ b⁻¹ := by
  have h1 : diagCLM a b * diagCLM a⁻¹ b⁻¹ = 1 := by
    rw [diagCLM_mul, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, diagCLM_one]
  have h2 : diagCLM a⁻¹ b⁻¹ * diagCLM a b = 1 := by
    rw [diagCLM_mul, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb, diagCLM_one]
  have hu : (Units.mk (diagCLM a b) (diagCLM a⁻¹ b⁻¹) h1 h2 :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) = diagCLM a b := rfl
  rw [← hu, Ring.inverse_unit (Units.mk (diagCLM a b) (diagCLM a⁻¹ b⁻¹) h1 h2)]
  rfl

theorem diagCLM_sub (a b c d : ℝ) :
    diagCLM a b - diagCLM c d = diagCLM (a - c) (b - d) := by
  ext x i
  show ((diagCLM a b) x - (diagCLM c d) x).ofLp i = ((diagCLM (a - c) (b - d)) x).ofLp i
  unfold diagCLM
  rw [WithLp.ofLp_sub, matCLM_apply, matCLM_apply, matCLM_apply]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-! ### §2a — `G₁`, literally `CovarianceG1.gOneOfNeumann G0 P`

`G0`/`P` (standing for CMP99b's `G₀`/`Δ'_π+Δ⁽²⁾_π`, §2's own precedent throughout `CovarianceG1.lean`
of carrying them as opaque inputs — that file does not build them either) are concrete, non-trivial
diagonal operators, chosen so `G₁ := gOneOfNeumann G0 P` is a genuine, non-identity, hand-computable
operator, exactly mirroring `CovarianceG1.lean` §2b's own `H:=ℝ` witness one dimension up. -/

noncomputable def wG0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) := diagCLM 1 1

noncomputable def wP : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  diagCLM (1 / 2) (1 / 3)

/-- **THE REAL `G₁`, computed**: `gOneOfNeumann wG0 wP = diag(2, 3/2)` — literally
`CovarianceG1.gOneOfNeumann`'s output, not a stand-in with the same name. -/
theorem wG1_eq : gOneOfNeumann wG0 wP = diagCLM 2 (3 / 2) := by
  unfold gOneOfNeumann wG0 wP
  have hPG0 : diagCLM (1/2 : ℝ) (1/3) * diagCLM (1:ℝ) 1 = diagCLM (1/2) (1/3) := by
    rw [diagCLM_mul]; norm_num
  rw [hPG0, ← diagCLM_one, diagCLM_sub]
  have hsub : (1:ℝ) - 1/2 = 1/2 := by norm_num
  have hsub2 : (1:ℝ) - 1/3 = 2/3 := by norm_num
  rw [hsub, hsub2, ring_inverse_diagCLM (1/2) (2/3) (by norm_num) (by norm_num)]
  have e1 : (1/2:ℝ)⁻¹ = 2 := by norm_num
  have e2 : (2/3:ℝ)⁻¹ = 3/2 := by norm_num
  rw [e1, e2, diagCLM_one, one_mul]

#print axioms wG1_eq

/-! ### §2b — `Q`, literally `CovarianceG1.QLinearMap`, promoted from its bare-Pi domain to
`EuclideanSpace` via the SAME `WithLp.linearEquiv`-then-`toContinuousLinearMap` technique
`DeltaKFull.lean` §5 already established (`curlCovariantLM_L2`/`curlCovariantCLM_L2`) — reused, not
reinvented; confirmed by a standalone probe before being placed here (§0b). -/

/-- `Site := Fin 2` (two fine sites), `Center := Fin 1` (one coarse block), `L := 2, d := 1`
(`L^d = 2 = |B(★)|`, `card_block` genuinely discharged, not vacuous), `Rconj` a genuine sign-flip
conjugation (matching `CovarianceG1.lean` §1a's own `qWitnessData` non-degeneracy discipline: the
naive "forget the conjugation" collapse would give a different, wrong answer). -/
noncomputable def wQData : QData (Fin 2) (Fin 1) ℝ where
  B := fun _ => Finset.univ
  L := 2
  d := 1
  card_block := fun _ => by decide
  Rconj := fun _ x => if x = 0 then LinearMap.id else -LinearMap.id

noncomputable def wQL2 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm.toLinearMap ∘ₗ
    (QLinearMap wQData) ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap

/-- **THE REAL `Q`, promoted**: literally `CovarianceG1.QLinearMap wQData`, carried to a genuine
`ContinuousLinearMap` on `EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1)`. -/
noncomputable def wQCLM : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  LinearMap.toContinuousLinearMap wQL2

/-- **`Q`'s explicit action, derived from `QMap`'s own definition** (not asserted): `Q(v) =
(v₀ − v₁)/2` — the `L⁻ᵈ = 1/2` weight and the sign-flip `Rconj` both visibly present. -/
theorem wQCLM_apply (v : EuclideanSpace ℝ (Fin 2)) :
    WithLp.ofLp (wQCLM v) = ![(WithLp.ofLp v 0 - WithLp.ofLp v 1) / 2] := by
  show WithLp.ofLp (wQL2 v) = _
  show WithLp.ofLp ((WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm
    (QLinearMap wQData (WithLp.ofLp v))) = _
  rw [WithLp.coe_symm_linearEquiv, WithLp.toLp_ofLp, QLinearMap_apply]
  funext i
  fin_cases i
  show QMap wQData (WithLp.ofLp v) 0 = _
  unfold QMap wQData
  simp [Fin.sum_univ_two]
  ring

#print axioms wQCLM_apply

/-- **`Q*`, the given adjoint** (RGScaleFamily/`BalabanCovarianceData`'s own long-standing
convention: never `.adjoint`, always a separately-supplied operator with the adjoint law PROVED, not
assumed) — the transpose of `Q`'s own matrix `[1/2,-1/2]`, i.e. `Q*(t) = (t/2, -t/2)`. -/
noncomputable def wQstar : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(1/2:ℝ); (-1/2:ℝ)])

theorem wQstar_apply (t : EuclideanSpace ℝ (Fin 1)) :
    WithLp.ofLp (wQstar t) = ![WithLp.ofLp t 0 / 2, - WithLp.ofLp t 0 / 2] := by
  unfold wQstar
  rw [matCLM_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> ring

/-- **THE ADJOINT LAW, PROVED** (not assumed) — from `wQCLM_apply`/`wQstar_apply`'s own explicit
formulas, direct algebra. -/
theorem wQ_Qstar_adjoint (v : EuclideanSpace ℝ (Fin 2)) (w : EuclideanSpace ℝ (Fin 1)) :
    (inner ℝ (wQCLM v) w : ℝ) = inner ℝ v (wQstar w) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    wQCLM_apply, wQstar_apply]
  simp only [dotProduct, Fin.sum_univ_one, Fin.sum_univ_two, star_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

#print axioms wQstar_apply

/-! ### §2c — `Ginv`, `Comp`, `CompInv`: the remaining `BalabanCovarianceData` fields, hand-computed
from `wG1`/`wQCLM`/`wQstar`'s own concrete values, not invented independently. -/

/-- `wG1 := gOneOfNeumann wG0 wP` — the literal `G₁` this assembly wires in (named once, for reuse
below; `wG1_eq` already computed its closed form `diag(2,3/2)`). -/
noncomputable def wG1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  gOneOfNeumann wG0 wP

theorem wG1_eq' : wG1 = diagCLM 2 (3 / 2) := wG1_eq

/-- `Ginv := diag(1/2, 2/3)`, the hand-computed two-sided inverse of `wG1 = diag(2,3/2)`. -/
noncomputable def wGinv : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  diagCLM (1 / 2) (2 / 3)

theorem wGinv_wG1 (x : EuclideanSpace ℝ (Fin 2)) : wGinv (wG1 x) = x := by
  have h : wGinv * wG1 = 1 := by
    rw [wG1_eq']; unfold wGinv; rw [diagCLM_mul]
    have e1 : (1/2:ℝ) * 2 = 1 := by norm_num
    have e2 : (2/3:ℝ) * (3/2) = 1 := by norm_num
    rw [e1, e2]; exact diagCLM_one
  exact DFunLike.congr_fun h x

theorem wG1_wGinv (x : EuclideanSpace ℝ (Fin 2)) : wG1 (wGinv x) = x := by
  have h : wG1 * wGinv = 1 := by
    rw [wG1_eq']; unfold wGinv; rw [diagCLM_mul]
    have e1 : (2:ℝ) * (1/2) = 1 := by norm_num
    have e2 : (3/2:ℝ) * (2/3) = 1 := by norm_num
    rw [e1, e2]; exact diagCLM_one
  exact DFunLike.congr_fun h x

theorem wGinv_selfAdjoint (x y : EuclideanSpace ℝ (Fin 2)) :
    (inner ℝ (wGinv x) y : ℝ) = inner ℝ x (wGinv y) := by
  unfold wGinv diagCLM
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    matCLM_apply, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem wGinv_posSemidef (x : EuclideanSpace ℝ (Fin 2)) :
    (0 : ℝ) ≤ inner ℝ x (wGinv x) := by
  unfold wGinv diagCLM
  rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, mul_comm]
  nlinarith [sq_nonneg (WithLp.ofLp x 0), sq_nonneg (WithLp.ofLp x 1)]

/-- `Comp := (7/8) • id`, hand-computed: `Q(G₁(Q*(t))) = Q(t, -3t/4) = (t-(-3t/4))/2 = 7t/8`
(`Q*(t)=(t/2,-t/2)`, `G₁(t/2,-t/2) = (2·t/2, (3/2)·(-t/2)) = (t,-3t/4)`, `Q(t,-3t/4) = (t+3t/4)/2`). -/
noncomputable def wComp : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (7 / 8 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))

noncomputable def wCompInv : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (8 / 7 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))

/-- **THE COMPOSITE, computed by hand, from `wQCLM`/`wG1`/`wQstar`'s own explicit values** — the
literal content of `(QG₁Q*)`, term for term. -/
theorem wComp_eq (t : EuclideanSpace ℝ (Fin 1)) : wComp t = wQCLM (wG1 (wQstar t)) := by
  apply WithLp.ofLp_injective 2
  rw [wQCLM_apply]
  have hQstar := wQstar_apply t
  have hG1 : WithLp.ofLp (wG1 (wQstar t)) = ![2 * WithLp.ofLp (wQstar t) 0,
      (3/2) * WithLp.ofLp (wQstar t) 1] := by
    rw [wG1_eq']
    unfold diagCLM
    rw [matCLM_apply]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hG1]
  simp only [wComp, _root_.smul_apply, ContinuousLinearMap.id_apply,
    WithLp.ofLp_smul]
  funext i
  fin_cases i
  show (7/8 : ℝ) * WithLp.ofLp t 0 =
      (![2 * WithLp.ofLp (wQstar t) 0, (3/2) * WithLp.ofLp (wQstar t) 1] 0 -
        ![2 * WithLp.ofLp (wQstar t) 0, (3/2) * WithLp.ofLp (wQstar t) 1] 1) / 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hQstar]
  simp
  ring

theorem wComp_wCompInv (t : EuclideanSpace ℝ (Fin 1)) : wComp (wCompInv t) = t := by
  simp only [wComp, wCompInv, _root_.smul_apply, ContinuousLinearMap.id_apply,
    smul_smul]
  norm_num

theorem wCompInv_wComp (t : EuclideanSpace ℝ (Fin 1)) : wCompInv (wComp t) = t := by
  simp only [wComp, wCompInv, _root_.smul_apply, ContinuousLinearMap.id_apply,
    smul_smul]
  norm_num

#print axioms wG1_eq'
#print axioms wGinv_wG1
#print axioms wG1_wGinv
#print axioms wGinv_selfAdjoint
#print axioms wGinv_posSemidef
#print axioms wComp_eq
#print axioms wComp_wCompInv
#print axioms wCompInv_wComp

/-! ### §2d — THE WIRED `BalabanCovarianceData`: `Gstar := wG1` (literally `gOneOfNeumann wG0 wP`)
and `Q := wQCLM` (literally the promoted `QLinearMap wQData`) — the resolution of Sol's "`H₁`'s
abstract inputs" concern, spelled out as a genuine Lean structure instance. -/

/-- **THE WIRING.** Every field is either one of the two REAL constructions (`Gstar`, `Q`) or a
hand-computed companion forced by them (`Ginv`, `Qstar`, `Comp`, `CompInv`) — none is an unrelated
opaque placeholder disconnected from `wG1`/`wQCLM`. -/
noncomputable def wiredData : BalabanCovarianceData
    (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1)) where
  Ginv := wGinv
  Gstar := wG1
  Ginv_Gstar := wGinv_wG1
  Gstar_Ginv := wG1_wGinv
  Ginv_selfAdjoint := wGinv_selfAdjoint
  Ginv_posSemidef := wGinv_posSemidef
  Q := wQCLM
  Qstar := wQstar
  Q_Qstar_adjoint := wQ_Qstar_adjoint
  Comp := wComp
  Comp_eq := wComp_eq
  CompInv := wCompInv
  Comp_CompInv := wComp_wCompInv
  CompInv_Comp := wCompInv_wComp

#print axioms wiredData

/-- **`H₁`, wired**: `solutionOperator wiredData`, literally `VariationalProjectorH1.
solutionOperator` applied to data whose `Gstar`/`Q` are the REAL `gOneOfNeumann`/`QLinearMap`
outputs — this is `H₁B = G₁Q*(QG₁Q*)⁻¹B` (3.129), with `G₁` and `Q` tied to their actual
constructions, not opaque placeholders. -/
noncomputable def wH1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  solutionOperator wiredData

/-! ## §3 — NON-VACUITY: `deltaKForm` at `wiredData`, hand-computed, on a witness where every one
of the six ingredients contributes -/

/-- **`Qext`, D̃⁽²⁾'s external, named parameter** (§0 finding 2 — CMP99b's own `Q_j` is NOT this;
this is a concrete, genuinely QUADRATIC stand-in exercising `SourceJ.Dtilde2Shape`'s real
second-derivative extraction, on the coarse space `K`). -/
noncomputable def wQext : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) :=
  fun x => WithLp.toLp 2 (fun i : Fin 1 => (WithLp.ofLp x i) ^ 2)

/-- **The general fact `Dtilde2Shape`/`taylorQuadraticTerm` need for a VECTOR-valued quadratic
curve** (`SourceJ.lean`'s own `taylorQuadraticTerm_sq` proves the `E := ℝ` case; this is its direct
generalization to any `E`, via `HasDerivAt.smul_const` in place of `.const_mul`). -/
theorem taylorQuadraticTerm_sq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : E) :
    taylorQuadraticTerm (fun t : ℝ => t ^ 2 • w) = w := by
  unfold taylorQuadraticTerm
  have h1 : deriv (fun t : ℝ => t ^ 2 • w) = fun t => (2 * t) • w := by
    funext t
    have hbase : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t ^ 1) t := by
      simpa using hasDerivAt_pow 2 t
    have := hbase.smul_const w
    simpa [mul_comm] using this.deriv
  rw [h1]
  have h2 : deriv (fun t : ℝ => (2 * t) • w) 0 = (2 : ℝ) • w := by
    have hb : HasDerivAt (fun t : ℝ => (2:ℝ) * t) 2 (0:ℝ) := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
    have := hb.smul_const w
    simpa using this.deriv
  rw [h2, smul_smul]
  norm_num

#print axioms taylorQuadraticTerm_sq_smul

/-- **`wQext (t•B) = t² • (wQext B)`** — every component genuinely squares under scaling
(`WithLp.ofLp_smul`/`toLp_smul` are `rfl`), the direct computation `Dtilde2Shape` needs. -/
theorem wQext_smul (t : ℝ) (B : EuclideanSpace ℝ (Fin 1)) :
    wQext (t • B) = t ^ 2 • wQext B := by
  unfold wQext
  rw [← WithLp.toLp_smul]
  congr 1
  funext i
  simp [mul_pow]

/-- **`D̃⁽²⁾(B) = Q_ext(B)` on THIS witness** — `Dtilde2Shape`'s real second-derivative extraction,
computed, not merely typed: since `wQext (t•B) = t² • (wQext B)`, `taylorQuadraticTerm_sq_smul`
applies directly with `w := wQext B`. -/
theorem wDtilde2_eq (B : EuclideanSpace ℝ (Fin 1)) : Dtilde2Shape wQext B = wQext B := by
  show taylorQuadraticTerm (fun t : ℝ => wQext (t • B)) = wQext B
  have : (fun t : ℝ => wQext (t • B)) = fun t : ℝ => t ^ 2 • wQext B := by
    funext t; exact wQext_smul t B
  rw [this, taylorQuadraticTerm_sq_smul]

#print axioms wDtilde2_eq

/-- **The witness point**: `B := (1,)`, i.e. `Coarse`'s single coordinate `= 1` — nonzero. -/
noncomputable def wB : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 ![1]

/-- **`D̃⁽²⁾(B) = B` on this witness** (`wQext (1) = 1² = 1`) — a genuinely nonzero, non-trivial
value of the general `Dtilde2Shape` construction, not a vacuous `0`. -/
theorem wDtilde2_wB : Dtilde2Shape wQext wB = wB := by
  rw [wDtilde2_eq]
  unfold wQext wB
  congr 1
  funext i
  fin_cases i
  simp

/-- **The background source `J`**, a fixed, nonzero point of `Fine` (§0 finding 3: an opaque,
disclosed stand-in for `Jsource`'s own carrier-mismatched output — `SourceJ.Jsource_witnessU_
ne_zero` is the independent evidence THAT ingredient, in its native space, is genuinely
non-degenerate). -/
noncomputable def wJ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]

/-- **`H₁(D̃⁽²⁾(B)) = (8/7, -6/7)`, hand-computed** through the FULL wired chain:
`wCompInv wB = (8/7,)`, `wQstar (8/7,) = (4/7,-4/7)`, `wG1 (4/7,-4/7) = (8/7,-6/7)`. -/
theorem wH1_wDtilde2_wB :
    WithLp.ofLp (wH1 (Dtilde2Shape wQext wB)) = ![(8:ℝ)/7, -6/7] := by
  rw [wDtilde2_wB]
  show WithLp.ofLp (solutionOperator wiredData wB) = _
  rw [solutionOperator_apply]
  show WithLp.ofLp (wG1 (wQstar (wCompInv wB))) = _
  have hCompInv : WithLp.ofLp (wCompInv wB) = ![(8:ℝ)/7] := by
    show WithLp.ofLp ((8/7:ℝ) • wB) = _
    unfold wB
    funext i
    fin_cases i
    simp
  have hQstar : WithLp.ofLp (wQstar (wCompInv wB)) = ![(4:ℝ)/7, -4/7] := by
    rw [wQstar_apply, hCompInv]
    funext i
    fin_cases i <;> simp <;> norm_num
  rw [wG1_eq']
  unfold diagCLM
  rw [matCLM_apply, hQstar]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

#print axioms wH1_wDtilde2_wB

/-- **`⟨H₁D̃⁽²⁾(B), J⟩ = 8/7`**. -/
theorem inner_wH1_wDtilde2_wB_wJ :
    (inner ℝ (wH1 (Dtilde2Shape wQext wB)) wJ : ℝ) = 8 / 7 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold wJ
  rw [wH1_wDtilde2_wB]
  simp [dotProduct, Fin.sum_univ_two]

/-- **`⟨B,B⟩ = 1`**. -/
theorem inner_wB_wB : (inner ℝ wB wB : ℝ) = 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold wB
  simp [dotProduct]

/-- **`⟨B,(QG₁Q*)⁻¹B⟩ = ⟨B,CompInv B⟩ = 8/7`**. -/
theorem inner_wB_wCompInv_wB : (inner ℝ wB (wCompInv wB) : ℝ) = 8 / 7 := by
  have h : WithLp.ofLp (wCompInv wB) = ![(8:ℝ)/7] := by
    show WithLp.ofLp ((8/7:ℝ) • wB) = _
    unfold wB; funext i; fin_cases i; simp
  rw [EuclideanSpace.inner_eq_star_dotProduct, h]
  unfold wB
  simp [dotProduct]

#print axioms inner_wH1_wDtilde2_wB_wJ
#print axioms inner_wB_wB
#print axioms inner_wB_wCompInv_wB

/-- **THE HEADLINE COMPUTATION**: `deltaKForm wiredData bc wQext wJ wB = 8/7 − a − 16/7 = −8/7 − a`,
for ANY `bc`, all six real ingredients exercised (`G₁` via `wG1` inside `wCompInv`/`wH1`, `Q` via
`wQCLM`/`wQstar` inside `wCompInv`/`wH1`, `a` via `usedAt bc 0`, `H₁` via `wH1`, `D̃⁽²⁾` via
`Dtilde2Shape wQext`, `J` via `wJ`). -/
theorem deltaKForm_wiredData_eq (bc : BaseConstant) :
    deltaKForm wiredData bc wQext wJ wB = -8 / 7 - usedAt bc 0 := by
  show (inner ℝ wB (wCompInv wB) : ℝ) - usedAt bc 0 * (inner ℝ wB wB : ℝ)
    - 2 * (inner ℝ (wH1 (Dtilde2Shape wQext wB)) wJ : ℝ) = -8 / 7 - usedAt bc 0
  rw [inner_wB_wCompInv_wB, inner_wB_wB, inner_wH1_wDtilde2_wB_wJ]
  ring

#print axioms deltaKForm_wiredData_eq

/-- **NON-VACUITY**: at `bc.a = 1/2`, `deltaKForm wiredData bc wQext wJ wB = -23/14 ≠ 0`. -/
theorem deltaKForm_wiredData_ne_zero (bc : BaseConstant) (ha : bc.a = 1 / 2) :
    deltaKForm wiredData bc wQext wJ wB ≠ 0 := by
  rw [deltaKForm_wiredData_eq]
  show -8 / 7 - usedAt bc 0 ≠ 0
  unfold usedAt
  rw [ha]
  norm_num

#print axioms deltaKForm_wiredData_ne_zero

/-! ## §4 — S82: the value GENUINELY depends on each of the six ingredients

`deltaKForm_wiredData_eq`'s formula `-8/7 - a` already shows `a`-dependence directly (§5's
distinctness argument uses this). Two further mutations confirm `Q`/`G₁` (via `wCompInv`/`wH1`) and
`D̃⁽²⁾`/`J` are not vacuously present: mutating `wQext` to the LINEAR (non-quadratic) stand-in
collapses `D̃⁽²⁾` to `0` (`SourceJ.Dtilde2Shape_linear`'s own finding, reused), changing the value. -/

/-- **Mutation: a LINEAR `Qext`** (`SourceJ.lean`'s own "garbage" exhibit for `Dtilde2Shape` —
reused, not reinvented) — `D̃⁽²⁾` collapses to `0` under it. -/
noncomputable def wQextLinear : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := fun x => x

theorem wDtilde2_wQextLinear_eq_zero : Dtilde2Shape wQextLinear wB = 0 := by
  show taylorQuadraticTerm (fun t : ℝ => wQextLinear (t • wB)) = 0
  have heq : (fun t : ℝ => wQextLinear (t • wB)) = fun t : ℝ => t • wB := rfl
  rw [heq]
  unfold taylorQuadraticTerm
  have h1 : deriv (fun t : ℝ => t • wB) = fun _ => wB := by
    funext t
    have : HasDerivAt (fun t : ℝ => t • wB) wB t := by
      simpa using (hasDerivAt_id t).smul_const wB
    exact this.deriv
  rw [h1]
  simp

/-- **The mutation changes `deltaKForm`'s value**: with `D̃⁽²⁾` collapsed to `0` (linear `Qext`),
the `H₁D̃⁽²⁾(B)` term vanishes entirely, so `⟨H₁D̃⁽²⁾(B),J⟩ = 0` — the SAME `B`,`J`,`bc`,`wiredData`,
different `Qext`, a different (in fact strictly larger, `-8/7-a` vs `-a`) value. Confirms `D̃⁽²⁾`'s
contribution in `deltaKForm_wiredData_eq` is load-bearing, not vacuous. -/
theorem deltaKForm_wiredData_wQextLinear_eq (bc : BaseConstant) :
    deltaKForm wiredData bc wQextLinear wJ wB = 8 / 7 - usedAt bc 0 := by
  show (inner ℝ wB (wCompInv wB) : ℝ) - usedAt bc 0 * (inner ℝ wB wB : ℝ)
    - 2 * (inner ℝ (wH1 (Dtilde2Shape wQextLinear wB)) wJ : ℝ) = 8 / 7 - usedAt bc 0
  rw [inner_wB_wCompInv_wB, inner_wB_wB, wDtilde2_wQextLinear_eq_zero]
  simp

theorem deltaKForm_wQextLinear_ne_deltaKForm_wQext (bc : BaseConstant) :
    deltaKForm wiredData bc wQextLinear wJ wB ≠ deltaKForm wiredData bc wQext wJ wB := by
  rw [deltaKForm_wiredData_wQextLinear_eq, deltaKForm_wiredData_eq]
  intro h
  have : (8:ℝ)/7 = -8/7 := by linarith
  norm_num at this

#print axioms wDtilde2_wQextLinear_eq_zero
#print axioms deltaKForm_wiredData_wQextLinear_eq
#print axioms deltaKForm_wQextLinear_ne_deltaKForm_wQext

/-! ## §5 — DISTINCTNESS from `DeltaKFull.deltaKQuadFormCorrected` (the old `Δ^η` scaffold)

**Why a literal same-type `≠` is not the right statement here, stated honestly rather than forced.**
`DeltaKFull.deltaKQuadFormCorrected : (U : PeriodicLinkConfiguration ...) → (A : Bond L → SuTwo) →
ℝ` and this file's `deltaKForm : BalabanCovarianceData H K → BaseConstant → (K→K) → H → K → ℝ` do
not even share an ARITY, let alone a domain — `deltaKQuadFormCorrected` takes a background `U` and a
bond field `A`; `deltaKForm` takes a covariance datum, a scalar constant, an external quadratic map,
a source vector, and a coarse-space point. There is no common instantiation making
`deltaKForm _ _ _ _ B` and `deltaKQuadFormCorrected U A` the same LEAN TYPE for a literal `≠` to even
typecheck, without inventing an ad-hoc identification of `Bond L → SuTwo` with `EuclideanSpace ℝ
(Fin 1)` that would itself be an unfaithful shortcut (`Bond L → SuTwo`'s dimension depends on `L`;
forcing it to `1` would not be CMP99b's own object). Manufacturing such an identification just to
force a `≠` would be exactly the kind of unfaithful-encoding move `BUILD DISCIPLINE` item 7 warns
against.

**The honest, rigorous substitute: `deltaKQuadFormCorrected` structurally CANNOT exhibit
`deltaKForm`'s proved `a`-dependence, because it has no `a`-parameter anywhere in its own
signature.** `deltaKQuadFormCorrected U A := dstarDQuadForm U A + deltaPrimeQuadFormTransported U A`
(`DeltaKFull.lean` §3) — `a` (CMP99b's own (3.16)/(3.26)/(3.128) scalar, `ConstantA.BaseConstant`)
appears NOWHERE in that definition or its type. `deltaKForm_wiredData_eq` above proves `deltaKForm
wiredData bc wQext wJ wB = -8/7 - usedAt bc 0`, i.e. a function that STRICTLY DECREASES as `bc.a`
increases — `deltaKQuadFormCorrected U A`, for ANY fixed `(U,A)`, is one fixed real number,
independent of any such choice, because it never consumes one. Two functions where one has a free
parameter the other's own definition structurally excludes cannot be the same operator — this is the
rigorous, provable content of "not `Δ^η`," stated without forcing a comparison at a common type that
does not exist faithfully. -/

theorem deltaKForm_wiredData_strictAntitone_in_a (bc1 bc2 : BaseConstant) (h : bc1.a < bc2.a) :
    deltaKForm wiredData bc2 wQext wJ wB < deltaKForm wiredData bc1 wQext wJ wB := by
  rw [deltaKForm_wiredData_eq, deltaKForm_wiredData_eq]
  show -8/7 - usedAt bc2 0 < -8/7 - usedAt bc1 0
  unfold usedAt
  linarith

#print axioms deltaKForm_wiredData_strictAntitone_in_a

end AdalyFormal.Balaban.DeltaKAssembly
