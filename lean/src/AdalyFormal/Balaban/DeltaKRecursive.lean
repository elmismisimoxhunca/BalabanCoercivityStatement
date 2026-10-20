/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib

set_option autoImplicit false

/-!
# `Δ_k` — THE ACTUAL RECURSIVE OBJECT, CMP99b eq. (3.156)

## ⚠ REPAIR PASS (2026-07-22) — READ THIS FIRST

`compute/pros_deltak_rec/PROS_DELTAK_REC.md` (commit `0c1dc1bf`) convicted the prior version of this
file on three counts. Mid-repair, a sibling lane's `CovarianceG1.lean` (commit `441d0d0e`,
`formal/AdalyFormal/COVARIANCE_G1.md`) landed a FOURTH, structural finding that supersedes part of
this repair's own original mandate. Both are addressed here; **this docstring records exactly what
changed and why**, since a prior correction on this same file (line 21-29, now itself further
corrected below) already showed the failure mode of a fix that doesn't fully propagate.

**C1 (recursion permits, does not force) — RETRACTED-AND-SHARPENED, not merely qualified.** The
prosecution found `G1_succ_eq_feed_deltaKQuadForm` (`rfl`) holds for every `feed`, including a
disguised-constant one, so it discriminates nothing on its own. `CovarianceG1.lean` then went
further and **proved** (`feedFromNeumann_forces_argument_independence`,
`G1_indep_of_deltaK_affecting_fields`) that **no (3.138)-faithful instantiation of `feed` CAN depend
on its `Δ_k`-quadratic-form argument at all** — (3.138)'s actual content is
`G₁ = G₀(I−(Δ'_π+Δ⁽²⁾_π)G₀)⁻¹`, a function of the CURRENT scale's `G₀` and correction terms, never of
the PREVIOUS scale's `Δ_k` VALUES. So the old plan (item 3 of this repair's original dispatch: "add a
field-level law forcing `feed` to depend on its argument") would have **criminalized the faithful
case** — it is now abandoned. §2b below states, instead of forcing it, exactly what CAN be forced
faithfully (the OPERATOR-valued dependency, via new `DeltaOp`/`feedOp` fields) and what remains a
bare, honestly-labelled permissive placeholder (the original `feed`/`G1`/`deltaKQuadForm` machinery).

**C2 (a field named "invert" that never inverts) — FIXED, with a mandatory field-level law.**
`invertQGQstar_spec` (§1) now REQUIRES every instantiation to make `invertQGQstar` equal
`Ring.inverse` of the actual `(QG₁Q^*)` composite — an instantiation that merely passes its
`G`-argument through (the convicted `witnessFamily.invertQGQstar := fun _ _ G _ => G`) cannot supply
a valid proof of this field except in the measure-zero case where the composite happens to be its
own inverse. §4's `richWitnessFamily` supplies a genuine proof; §4's own mutation-argument shows the
old pass-through provably cannot.

**C3 (`Q₁` distinct from `Q`, restriction never imposed) — `Q₁` ADDED as a field; the (3.156)
subspace is now IMPOSED and genuinely exercised.** Per `CovarianceG1.lean`'s own independent check
(pp.421–430, checked page-by-page): **`Q₁`'s defining formula is NOT located anywhere in that page
range.** This repair does **not** invent it — `Q1` is carried as an opaque field (matching the
file's existing treatment of every other unbuilt ingredient), and the (3.156) subspace restriction
`{B:B=0 on Λ^c, B=0 on ∪Ax(y), Q₁B=0}` is now built from it, `LambdaSmall` (Λ) and `AxZeroLocus`
(the `∪_{y∈Λ'}Ax(y)` zero-locus, itself also opaque — `Ax(y)`'s own bond geometry is likewise
unbuilt) as a genuine intersection of submodules (§2). §4's witness proves a real point IS in this
subspace and a real point is NOT — the restriction is exercised, not merely declared.

## THE DEFINITION, VERBATIM (`corpus/pages/CMP99b_p428.md`, `verification_status: adjudicated`,
own image re-verified this pass, `corpus/renders/CMP99b_p428-40.png`, header "428 / T. Balaban"
confirmed)

CMP99b p.428, eq. (3.156):

```
⟨B, (QG₁Q*)⁻¹B⟩  −  a⟨B,B⟩  −  2⟨H₁ D̃⁽²⁾(B), J⟩   =   ⟨B, Δ_k B⟩
```

"This form is considered on the subspace `{B : B=0 on Λ^c, B=0 on ⋃_{y∈Λ'} Ax(y), Q₁B=0}`."
(p.428, immediately following (3.156)).

## (3.138), the true source of the `k`-recursion (`corpus/renders/CMP99b_p423 via
compute/g1_renders/CMP99b_pdf35-35.png`, own image re-verified this pass, header "Propagators for
Lattice Gauge Theories / 423" confirmed) — **NOT pp.427–429** as this file's own prior version
assumed:

```
G₁ = G₀(I − (Δ'_π + Δ⁽²⁾_π)G₀)⁻¹ = Σ_{n=0}^∞ G₀((Δ'_π + Δ⁽²⁾_π)G₀)ⁿ.        (3.138)
```

with `G₀ = (Δ + DRD* + Q*aQ)⁻¹` (p.421) built from the PREVIOUS scale's `Δ` (an OPERATOR). This is
the genuine `k`-recursion driver: `Δ` (operator, scale `k`) `→ G₀` (scale `k+1`) `→ G₁` (scale `k+1`,
via the Neumann series) `→ Δ_k` (scale `k+1`'s quadratic form, via (3.156), this file's
`deltaKQuadForm`). See §2b.

## INGREDIENT INVENTORY — page-cited, have/close/lack, checked directly (not assumed)

| Ingredient | CMP99b locus | Our tree | Verdict |
|---|---|---|---|
| `Q` (block average) | p.427 §E, p.428 (3.156)/(3.157) | **CLOSED** — `CovarianceG1.lean` §1 (`QData`/`QMap`/`QLinearMap`), page-cited to p.430's spelled-out formula; confirmed NOT the same object as `Averaging.lean`'s `averageAt`/`linearAverageAt` | **CLOSED** (SU(2) instantiation of `Rconj` still separately open) |
| `Q₁` (gauge-fixing on `B`, distinct from `Q`) | p.427 (3.155) `δ(Q₁B)`, p.428 (3.156) `Q₁B=0` | **NEW field, `RGScaleFamily.Q1`, §1 below.** Genuinely distinct symbol from `Q` in the source (checked twice, at two scales, by `CovarianceG1.lean §0c` and independently here). **Its own defining formula is NOT located in pp.421–430** — carried opaque, not invented. | **NAMED, CARRIED OPAQUE, UNLOCATED CONTENT** |
| `G₁` (previous-scale covariance) | p.423 (3.138) | **CLOSED** as a genuine Neumann-series construction — `CovarianceG1.lean` §2 (`gOneOfNeumann`), with the cancellation identity PROVED. `Δ'_π`/`Δ⁽²⁾_π` themselves remain opaque inputs to it. | **CLOSED** (as a construction; its own further ingredients remain opaque) |
| `a` (scalar constant) | (3.10), (3.128), (3.155)/(3.156) | **NEW field, `RGScaleFamily.a`, §1 below** — and `ConstantA.lean` now carries a dedicated `BaseConstant`/`usedAt` object in `Balaban/`. ~~No CMP99b-specific `a` constant defined anywhere; only the ambient field `ℝ`~~ | **NAMED, CARRIED AS A FIELD** ~~LACK~~ |
| `H₁` (harmonic projector, variational-problem sense) | p.421 | **NEW field, `RGScaleFamily.H1`, §1 below** — and `VariationalProjectorH1.lean` now builds the real `H₁` (`solutionOperator`, its own §2, "literally (3.126)/(3.129)"), page-pinned to p.421. `HarmonicModes.lean` remains a DIFFERENT object (topological winding modes) — that part of the row stands. ~~**LACK** (same-named-sounding-but-distinct object exists; the real `H₁` does not)~~ | **CLOSED as a construction** (its own inputs `G`/`Q`/`Q*` remain opaque) |
| `D̃⁽²⁾` (quadratic-in-`B` polynomial) | p.427 | **NEW field, `RGScaleFamily.Dtilde2`, §1 below** — and `SourceJ.lean` §6 builds the general SHAPE (`Dtilde2Shape`/`taylorQuadraticTerm`, the second-Taylor-coefficient extraction). CMP99b's own `Q_j` (eq. 3.13) instantiation is still open, blocked on CMP98's `Ū^j`. ~~Nothing matching~~ | **SHAPE CLOSED, `Q_j` INSTANTIATION NAMED-OPEN** ~~LACK~~ |
| `J` (background source) | p.421 (3.127)/(3.128), p.427 (3.155)/(3.156), **and (3.11) p.392, which DEFINES it** | **NEW field, `RGScaleFamily.J`, §1 below** — and `SourceJ.lean` builds `Jsource`, (3.9)+(3.11)'s explicit combinatorial formula, from `U`. ~~No dedicated `J : H` object anywhere in `Balaban/`~~ | **NAMED, CARRIED AS A FIELD — with a KNOWN DENOTATION DEFECT**: CMP99b (3.11) p.392 reads "where `J = D*η⁻² Im ∂U`", so `J` is a FUNCTION OF `U`, while `RGScaleFamily.J : ℕ → H` is `U`-blind (this structure carries no `Uconfig` type at all). `SourceJFaithful.no_kIndexed_J_realizes_faithful_source` proves the `ℕ → H` shape cannot realize a `U`-varying source; `SourceJFaithful.UFaithfulSourceIngredients` is the repaired interface (`Jof : ℕ → Uconfig → carrier`). No claim here is invalidated — no statement in this cluster quantifies over configurations — but nothing here may be read as uniformity in `U` |
| `Λ ⊂ Λ_k`, `Ax(y)` (domain restrictions) | p.427 §E, p.428 | `RGScaleFamily.Lambda`/`Lambda_anti` carries `Λ_k`; **new** `LambdaSmall`/`AxZeroLocus` (§1) carry `Λ` and the `Ax(y)`-zero-locus, both genuinely intersected into the (3.156) subspace (§2). `Ax(y)`'s own bond geometry remains unbuilt (opaque). | **PARTIALLY CLOSED**: the restriction is now IMPOSED as a submodule intersection; the geometric content of `Ax(y)` itself is still LACK |

This file does not manufacture any LACK ingredient from nothing — it builds the recursive SHAPE
CMP99b (3.156) actually has, with every missing ingredient carried as an explicit, individually
named, page-cited PARAMETER of a structure, never silently assumed or faked.
-/

namespace AdalyFormal.Balaban.DeltaKRecursive

/-! ## §1 — The recursive family structure

Every field below is named after, and page-cited to, its CMP99b ingredient (the inventory above).
Fields the tree cannot yet supply are OPAQUE (given, not derived) — never silently assumed to exist
"for free," and never smuggled in as an `axiom`: every opaque ingredient is an ordinary structure
FIELD, supplied explicitly by whoever instantiates the structure. This file has zero `axiom`s. -/

/-- **One RG scale family**, on a FIXED ambient real inner product space `H` (a documented
simplification: CMP99b's `Q_k` genuinely maps between DIFFERENT spaces `H_k → H_k'` as `k` varies —
carrying all scales on one `H` avoids re-opening `DeltaKFull.lean`'s ambient-topology wall, at the
cost of literal fidelity to the shrinking-domain aspect, which `Lambda`/`Lambda_anti`/`LambdaSmall`
below restore at the SUBSPACE level instead). -/
structure RGScaleFamily (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- `Λ_k ⊂ H`, CMP99b p.427 §E: "`Λ ⊂ Λ_k`... a union of big blocks... distance to `Λ_k^c` bigger
  than `RM`." Carried here as a genuine nested SUBMODULE family. -/
  Lambda : ℕ → Submodule ℝ H
  /-- The nesting CMP99b's scale tower requires: `Λ_{k+1} ⊆ Λ_k`. -/
  Lambda_anti : Antitone Lambda
  /-- **`Λ` itself** (p.427/428, DISTINCT from `Λ_k` above: `Λ ⊂ Λ_k`, the (3.156)-specific domain,
  "a union of big blocks... distance between `Λ` and `Λ_k^c` bigger than `RM`"). Used in the
  (3.156) subspace restriction `{B=0 on Λ^c, ...}` — see `deltaKSubspace` (§2). -/
  LambdaSmall : ℕ → Submodule ℝ H
  /-- CMP99b's own stated inclusion, p.427: "`Λ ⊂ Λ_k`." -/
  LambdaSmall_le : ∀ k, LambdaSmall k ≤ Lambda k
  /-- **`∪_{y∈Λ'} Ax(y)`'s zero-locus** (p.428, (3.156)'s subspace clause "`B=0` on
  `⋃_{y∈Λ'}Ax(y)`"). `Ax(y)`'s own bond geometry is NOT built anywhere in this tree (checked
  directly against pp.421-430 by `CovarianceG1.lean §0c` and again here) — carried OPAQUE as the
  submodule of vectors this condition selects, exactly as `Lambda` is already carried opaque rather
  than derived from block geometry. -/
  AxZeroLocus : ℕ → Submodule ℝ H
  /-- `Q_k`, the block-average operator (p.427 §E, p.428 (3.156)/(3.157)). -/
  Q : ℕ → H →L[ℝ] H
  /-- `Q_k^*`, carried as a SEPARATE given operator — never `.adjoint` (sidesteps
  `DeltaKFull.lean` §6's ambient-topology wall entirely, by construction). -/
  Qstar : ℕ → H →L[ℝ] H
  /-- **`Q₁_k`, CMP99b p.427 (3.155)'s `δ(Q_1B)` / p.428 (3.156)'s `Q_1B=0`** — a symbol VISIBLY
  DISTINCT from `Q` in the same equation (confirmed twice, at two scales, against the page images).
  Its own defining formula is NOT located anywhere in CMP99b pp.421–430 (checked page-by-page,
  `CovarianceG1.lean §0c`) — carried here OPAQUE, its content a NAMED, UNLOCATED residual, not
  invented. -/
  Q1 : ℕ → H →L[ℝ] H
  /-- `a_k`, the scalar constant of (3.155)/(3.156) (and (3.10), (3.128) at other scales). -/
  a : ℕ → ℝ
  /-- `H₁,ₖ`, Balaban's harmonic projector from the variational problem (3.127)/(3.110), p.421 —
  **not** `HarmonicModes.lean`'s winding-mode object (inventory table above). -/
  H1 : ℕ → H →L[ℝ] H
  /-- `D̃⁽²⁾_k(B)`, the quadratic-in-`B` polynomial map, p.427. -/
  Dtilde2 : ℕ → H → H
  /-- `J_k`, the background source configuration. -/
  J : ℕ → H
  /-- The BASE CASE: `G₁` at scale `0` has no previous scale to recurse from. CMP99b's own base
  propagator at this point in the induction is `G₀ = (Δ + DRD* + Q*aQ)⁻¹` (p.421). `G1base` stands
  for `(Q₀G₀Q₀^*)⁻¹` directly, matching that base case. -/
  G1base : H →L[ℝ] H
  /-- The composite-inversion primitive: intended to send `(Q_k, G₁_k, Q_k^*)` to
  `(Q_kG₁_kQ_k^*)⁻¹`. **Now constrained by `invertQGQstar_spec` below** — an instantiation can no
  longer supply a value that merely passes its `G`-argument through and still typecheck (except in
  the measure-zero case where that happens to equal the actual inverse). p.428 itself states this
  object needs [4]'s Lemma 2.4 (a SEPARATE hard theorem, at `U=1` only) just to know it is
  positive-definite with a `k`-independent lower bound — that QUANTITATIVE content remains a named,
  separate residual; `invertQGQstar_spec` only pins down the ALGEBRAIC fact of being a genuine
  two-sided inverse whenever one exists. -/
  invertQGQstar : ℕ → (H →L[ℝ] H) → (H →L[ℝ] H) → (H →L[ℝ] H) → (H →L[ℝ] H)
  /-- **THE FIX FOR C2.** Whenever the composite `Q_k G Q_k^*` is genuinely invertible (two-sided,
  in the ring `H →L[ℝ] H` under composition), `invertQGQstar` MUST equal its `Ring.inverse` — the
  actual, unique, two-sided inverse. A field named "invert" that merely returns its `G`-argument
  (the convicted defect) cannot supply this proof except when `G` happens to already be its own
  inverse conjugated by `Q_k,Q_k^*` — never the case in `richWitnessFamily` below (§4's mutation
  argument makes this concrete, not merely asserted). -/
  invertQGQstar_spec : ∀ (k : ℕ) (G : H →L[ℝ] H),
      IsUnit ((Q k).comp (G.comp (Qstar k))) →
      invertQGQstar k (Q k) G (Qstar k) = Ring.inverse ((Q k).comp (G.comp (Qstar k)))
  /-- **THE RECURSIVE STEP (original, permissive-placeholder shape — see §2b for why this is now
  known NOT to be faithful to (3.138)).** Consumes scale `k`'s `Δ_k` QUADRATIC FORM (a function
  `H → ℝ`) and produces the `G₁` ingredient for scale `k+1`. `CovarianceG1.lean` PROVES no
  (3.138)-faithful construction can depend on this argument at all
  (`feedFromNeumann_forces_argument_independence`) — so this field is retained ONLY as a permissive
  interface demonstrating the bare TYPE can carry `k`-varying data, not as a faithful reconstruction
  of Balaban's actual mechanism. -/
  feed : ℕ → (H → ℝ) → (H →L[ℝ] H)
  /-- **`Δ_k` AS AN OPERATOR** (as opposed to `deltaKQuadForm` below, its quadratic-FORM version) —
  the genuine driver of (3.138)'s recursion (`Δ` feeds `G₀ = (Δ+DRD*+Q*aQ)⁻¹` at the next scale).
  Carried OPAQUE: promoting `Δ_k` to a bundled operator on this ambient `H` is exactly
  `DeltaKFull.lean` §6's already-deferred wall (a Riesz-representation / `.adjoint` /
  `InnerProductSpace.toDual` ambient-topology diamond) — NOT solved here. The intended correspondence
  `⟨B, DeltaOp k B⟩ = deltaKQuadForm F k B` (this file's own (3.156) identity) is documented, not
  enforced as a structural law (enforcing it exactly IS that same deferred wall). -/
  DeltaOp : ℕ → H →L[ℝ] H
  /-- **THE (3.138)-SHAPED RECURSIVE STEP.** Consumes scale `k`'s `Δ_k` AS AN OPERATOR (unlike
  `feed`, which `CovarianceG1.lean` proved cannot depend on the quadratic-form argument if built
  faithfully from (3.138)). This is the field CMP99b's actual mechanism should be threaded through:
  `G₀_{k+1} = (Δ_k + \text{DRD*+Q*aQ at }k+1)^{-1}`, `G₁_{k+1} = \text{gOneOfNeumann}(G₀_{k+1}, P_{k+1})`
  (`CovarianceG1.lean §2`, cited not imported — importing it here would create a circular module
  dependency, since it already imports this file). §4 demonstrates a concrete, genuinely
  `k`-dependent instantiation; whether `feedOp` can be built to literally equal the (3.138) Neumann
  series with `DeltaOp` tied to the TRUE operator-promoted `Δ_k` is NOT shown here — that still needs
  `DeltaKFull.lean` §6's wall resolved. What IS shown: widening the domain from `H → ℝ` to
  `H →L[ℝ] H` removes `CovarianceG1.lean`'s proved obstruction, so this is a live, unblocked route. -/
  feedOp : ℕ → (H →L[ℝ] H) → (H →L[ℝ] H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## §2 — THE RECURSION ITSELF

`Δ_k` is built here as a QUADRATIC FORM (`H → ℝ`), not a bundled self-adjoint operator — matching
`DeltaKFull.lean`'s own already-documented finding (its §6) that promoting even the SINGLE-SCALE
`Δ`/`Δ′` to a genuine `ContinuousLinearMap` hits a hard, currently-open Mathlib-instance wall. The
quadratic form is exactly what (3.156) itself states as the defining IDENTITY (`⟨B,Δ_kB⟩ = ...`), so
working with the form is not a weakening of the source statement.

`G1 F k` stands for the composite `(Q_kG₁_kQ_k^*)⁻¹` this file's ingredient inventory calls
`invertQGQstar k (Q k) (G₁ at level k) (Qstar k)`. -/

/-- **The (3.156) subspace, imposed.** `{B : B=0 on Λ^c, B=0 on ∪_{y∈Λ'}Ax(y), Q₁B=0}`, literally,
as the intersection of the three submodules carrying each clause: `LambdaSmall k` (vectors supported
on `Λ`, i.e. `=0` off it), `AxZeroLocus k` (vectors `=0` on the `Ax(y)`-union), and
`LinearMap.ker (Q1 k)` (`Q₁B=0`). §4 proves a concrete point genuinely lies in this subspace and a
concrete point genuinely does not — the restriction is exercised, not merely declared. -/
def deltaKSubspace (F : RGScaleFamily H) (k : ℕ) : Submodule ℝ H :=
  F.LambdaSmall k ⊓ F.AxZeroLocus k ⊓ LinearMap.ker (F.Q1 k : H →ₗ[ℝ] H)

/-- **The recursive family, level by level (original, permissive-placeholder mechanism — §2b).**
`G1 F 0 = F.G1base`. `G1 F (k+1) = F.feed k (Δ_k's own quadratic form)`. -/
noncomputable def G1 (F : RGScaleFamily H) : ℕ → H →L[ℝ] H
  | 0 => F.G1base
  | (k + 1) =>
      F.feed k (fun B =>
        (inner ℝ B (F.invertQGQstar k (F.Q k) (G1 F k) (F.Qstar k) B) : ℝ)
          - F.a k * (inner ℝ B B : ℝ)
          - 2 * (inner ℝ (F.H1 k (F.Dtilde2 k B)) (F.J k) : ℝ))

/-- **`Δ_k`'s quadratic form**, CMP99b (3.156)'s LHS, literally. -/
noncomputable def deltaKQuadForm (F : RGScaleFamily H) (k : ℕ) (B : H) : ℝ :=
  (inner ℝ B (F.invertQGQstar k (F.Q k) (G1 F k) (F.Qstar k) B) : ℝ)
    - F.a k * (inner ℝ B B : ℝ)
    - 2 * (inner ℝ (F.H1 k (F.Dtilde2 k B)) (F.J k) : ℝ)

/-- **CORRECTED DOCSTRING (was the false claim convicted in C1).** This is a definitional unfold,
`rfl` for EVERY `F` (degenerate `feed`s included) — it carries NO non-triviality content by itself.
It does not "make this file's object recursive rather than a disguised constant family"; only §4's
witness-specific, concrete-value theorems do that work, and only for that one instantiation. -/
theorem G1_succ_eq_feed_deltaKQuadForm (F : RGScaleFamily H) (k : ℕ) :
    G1 F (k + 1) = F.feed k (deltaKQuadForm F k) := rfl

/-- **The base case, stated explicitly**: `G1` at scale `0` is exactly the given base ingredient
`F.G1base`, with no recursive dependency. -/
theorem G1_zero_eq_G1base (F : RGScaleFamily H) : G1 F 0 = F.G1base := rfl

#print axioms G1_succ_eq_feed_deltaKQuadForm
#print axioms G1_zero_eq_G1base

/-! ### §2b — THE (3.138)-SHAPED MECHANISM: a SEPARATE, PARALLEL recursion through `DeltaOp`/`feedOp`

`CovarianceG1.lean` proved that no (3.138)-faithful `feed` can depend on `deltaKQuadForm`'s VALUE
(§2 above). What (3.138) DOES show is genuine dependence on the PREVIOUS scale's `Δ` **as an
operator**. This section builds the parallel recursive mechanism through that operator, and §4
demonstrates it is genuinely `k`-dependent (not forced degenerate the way `feed` is). -/

/-- **The (3.138)-shaped recursive family**: `G1Op F 0 = F.G1base` (same base case).
`G1Op F (k+1) = F.feedOp k (F.DeltaOp k)` — level `k+1`'s ingredient is a genuine function of level
`k`'s `Δ_k` **as an operator**, the shape (3.138) actually supports. -/
noncomputable def G1Op (F : RGScaleFamily H) : ℕ → H →L[ℝ] H
  | 0 => F.G1base
  | (k + 1) => F.feedOp k (F.DeltaOp k)

theorem G1Op_succ_eq_feedOp_DeltaOp (F : RGScaleFamily H) (k : ℕ) :
    G1Op F (k + 1) = F.feedOp k (F.DeltaOp k) := rfl

theorem G1Op_zero_eq_G1base (F : RGScaleFamily H) : G1Op F 0 = F.G1base := rfl

#print axioms G1Op_succ_eq_feedOp_DeltaOp
#print axioms G1Op_zero_eq_G1base

/-! ## §3 — `witnessFamily`/`degenerateFamily`, `H := ℝ` — carried forward, FIXED for the new
mandatory fields

**SUPERSEDED AND REMOVED, 2026-07-22**: the prior version's `witnessFamily_G1_eq`,
`witnessFamily_deltaKQuadForm_eq`, `witnessFamily_deltaKQuadForm_ne_succ` (closed form `G1 = (k+1)•id`,
"unboundedly growing") are FALSE once `invertQGQstar` is fixed to genuinely invert (C2) — the
corrected recursion is `s_0=1, s_{k+1}=1+1/s_k` (`1, 2, 3/2, 5/3, 8/5, ...`, a Fibonacci-ratio
sequence converging to the golden ratio, NOT `k+1`). This matches the prosecution's own
`reciprocalFamily` finding (`1, 2, 3/2`) exactly, confirming the fix is consistent across two
independent artifacts. §4's `richWitnessFamily` is the new headline non-degeneracy witness (task
item 4); `witnessFamily`/`degenerateFamily` are kept ONLY for the (still-valid, orthogonal)
feed-permits-not-forces demonstration (§3b). -/

/-- **`witnessFamily`, fixed for C2**: `invertQGQstar` now genuinely inverts (`Ring.inverse`, not a
pass-through) — trivially satisfies `invertQGQstar_spec` since `Q=Q*=id` makes the composite equal
`G` itself. All the C3 fields (`Q1`, `LambdaSmall`, `AxZeroLocus`) are carried at their honestly
DEGENERATE values on this `1`-dimensional carrier (matching the file's existing disclosure style for
`Lambda := ⊤` here) — `richWitnessFamily` (§4) is where these are genuinely exercised. -/
noncomputable def witnessFamily : RGScaleFamily ℝ where
  Lambda := fun _ => ⊤
  Lambda_anti := antitone_const
  LambdaSmall := fun _ => ⊤
  LambdaSmall_le := fun _ => le_refl ⊤
  AxZeroLocus := fun _ => ⊤
  Q := fun _ => ContinuousLinearMap.id ℝ ℝ
  Qstar := fun _ => ContinuousLinearMap.id ℝ ℝ
  Q1 := fun _ => 0
  a := fun _ => 0
  H1 := fun _ => 0
  Dtilde2 := fun _ B => B
  J := fun _ => 0
  G1base := (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  invertQGQstar := fun _ _ G _ => Ring.inverse G
  invertQGQstar_spec := by
    intro k G _
    simp
  feed := fun _ g => (g 1 + 1) • ContinuousLinearMap.id ℝ ℝ
  DeltaOp := fun _ => 0
  feedOp := fun _ _ => (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ

#print axioms witnessFamily

/-! ### §3b — GARBAGE SUBSTITUTION (S82): `feed` CAN ignore its argument (this is now KNOWN to be
required for (3.138)-faithfulness, per §2b — retained as the "permits" demonstration, not a defect
of this file). -/

/-- **The degenerate mutation**: identical to `witnessFamily` except `feed` ignores its `g`
argument entirely. -/
noncomputable def degenerateFamily : RGScaleFamily ℝ where
  Lambda := fun _ => ⊤
  Lambda_anti := antitone_const
  LambdaSmall := fun _ => ⊤
  LambdaSmall_le := fun _ => le_refl ⊤
  AxZeroLocus := fun _ => ⊤
  Q := fun _ => ContinuousLinearMap.id ℝ ℝ
  Qstar := fun _ => ContinuousLinearMap.id ℝ ℝ
  Q1 := fun _ => 0
  a := fun _ => 0
  H1 := fun _ => 0
  Dtilde2 := fun _ B => B
  J := fun _ => 0
  G1base := (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  invertQGQstar := fun _ _ G _ => Ring.inverse G
  invertQGQstar_spec := by
    intro k G _
    simp
  feed := fun _ _ => (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  DeltaOp := fun _ => 0
  feedOp := fun _ _ => (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ

/-- **The mutation collapses the recursion**: `G1` is constant at every level under the degenerate
`feed` — confirming §4's genuine witness's non-degeneracy is NOT an artifact of the structure's
type, but a real consequence of `feed` actually reading its argument. -/
theorem degenerateFamily_G1_eq (k : ℕ) :
    G1 degenerateFamily k = (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  cases k with
  | zero => simp [G1, degenerateFamily]
  | succ n => rfl

/-- **The mutation makes the non-degeneracy claim FALSE** — `Δ_k = Δ_{k+1}` identically under the
degenerate `feed`, for every `k`. -/
theorem degenerateFamily_deltaKQuadForm_eq_succ (k : ℕ) :
    deltaKQuadForm degenerateFamily k = deltaKQuadForm degenerateFamily (k + 1) := by
  funext B
  simp only [deltaKQuadForm]
  rw [degenerateFamily_G1_eq, degenerateFamily_G1_eq]
  simp only [degenerateFamily]

#print axioms degenerateFamily_G1_eq
#print axioms degenerateFamily_deltaKQuadForm_eq_succ

/-! ## §4 — `richWitnessFamily`: the REPLACEMENT non-degeneracy witness (task item 4), on
`H := EuclideanSpace ℝ (Fin 2)` — large enough for `Q`, `Q*`, `Q₁` and the inverse to be genuinely
distinct maps, not scalars. -/

open Matrix WithLp

/-- A `Matrix m n ℝ` gives a genuine `EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m`, mirroring the
established `matCLM` pattern (`VariationalProjectorH1.lean §4`, NOT imported here — a fresh local
copy, to keep this file's write-scope self-contained under concurrent editing of that sibling
file). -/
noncomputable def matCLM {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

theorem matCLM_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    WithLp.ofLp (matCLM M x) = M *ᵥ (WithLp.ofLp x) := by
  unfold matCLM
  simp [Matrix.toEuclideanLin, LinearMap.coe_toContinuousLinearMap']

/-- `e₀ = (1,0)`, the "physical" test vector — genuinely inside the (3.156) subspace this section
builds (`richWitnessFamily_eZero_mem_subspace` below), unlike `e₁`. -/
noncomputable def eZero : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]

/-- `e₁ = (0,1)`, the falsifiability counterpart — genuinely OUTSIDE the subspace
(`richWitnessFamily_eOne_not_mem_subspace` below). -/
noncomputable def eOne : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]

/-- A diagonal operator on `EuclideanSpace ℝ (Fin 2)` — the workhorse for every concrete operator
in this section (`Q`, `Q*`, `Q₁`, `G₁`, their composite, and its inverse). -/
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

/-- `Ring.inverse` of a diagonal operator with both entries nonzero — the GENUINE two-sided
inverse, constructed by hand and identified with `Ring.inverse` via `Units.mk`/`Ring.inverse_unit`
(not merely asserted to exist). -/
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

theorem inner_eZero_diagCLM (a b : ℝ) :
    (inner ℝ eZero (diagCLM a b eZero) : ℝ) = a := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold diagCLM
  rw [matCLM_apply]
  unfold eZero
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `Q_k := diag(2,1)`, `Q^*_k := diag(3,1)` — CONSTANT in `k`, genuinely distinct from each other
(`2≠3`) and from `id` (`diag(1,1)`), acting invertibly on the "physical" coordinate and trivially
on the coordinate `Q₁` (below) kills. -/
noncomputable def richQ : ℕ → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  fun _ => diagCLM 2 1

noncomputable def richQstar : ℕ → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  fun _ => diagCLM 3 1

/-- **`Q₁ := diag(0,1)`** — GENUINELY DISTINCT from `richQ`/`richQstar` (a non-invertible
projection, not an invertible diagonal scaling): kills the first ("physical") coordinate, keeps the
second. `ker(Q₁) = span{e₀}` — a genuine PROPER subspace, not all of `H` and not `{0}`. -/
noncomputable def richQ1 : ℕ → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  fun _ => diagCLM 0 1

theorem richQ1_eZero : richQ1 0 eZero = 0 := by
  show diagCLM 0 1 eZero = 0
  ext i
  unfold diagCLM
  rw [matCLM_apply]
  unfold eZero
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem richQ1_eOne_ne_zero : richQ1 0 eOne ≠ 0 := by
  show diagCLM 0 1 eOne ≠ 0
  intro h
  have h1 := congrFun (congrArg (fun (v : EuclideanSpace ℝ (Fin 2)) => WithLp.ofLp v) h) 1
  unfold diagCLM at h1
  rw [matCLM_apply] at h1
  unfold eOne at h1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1

/-- **`richWitnessFamily`**: `H := EuclideanSpace ℝ (Fin 2)`. `Q ≠ Q^* ≠ id ≠ Q₁` genuinely as
operators (task item 4). `invertQGQstar := fun k Q G Qstar => Ring.inverse (Q.comp(G.comp Qstar))`
— GENUINELY inverts by construction (task item 2), for ANY `Q,G,Qstar`, not merely this witness's
own. `a,H1,J := 0`, `Dtilde2 := id` (isolates the `G₁`-recursion, matching the established
`witnessFamily` convention). `feed k g := diag(g(e₀)+1, 1)` — reads its argument at `e₀`, mirroring
`witnessFamily`'s own load-bearing choice, now on a richer carrier. -/
noncomputable def richWitnessFamily : RGScaleFamily (EuclideanSpace ℝ (Fin 2)) where
  Lambda := fun _ => ⊤
  Lambda_anti := antitone_const
  LambdaSmall := fun _ => ⊤
  LambdaSmall_le := fun _ => le_refl ⊤
  AxZeroLocus := fun _ => ⊤
  Q := richQ
  Qstar := richQstar
  Q1 := richQ1
  a := fun _ => 0
  H1 := fun _ => 0
  Dtilde2 := fun _ B => B
  J := fun _ => 0
  G1base := diagCLM 1 1
  invertQGQstar := fun _ Q G Qstar => Ring.inverse (Q.comp (G.comp Qstar))
  invertQGQstar_spec := fun _ _ _ => rfl
  feed := fun _ g => diagCLM (g eZero + 1) 1
  DeltaOp := fun k => diagCLM (k : ℝ) 0
  feedOp := fun _ D => diagCLM (WithLp.ofLp (D eZero) 0 + 1) 1

#print axioms richWitnessFamily

/-! ### §4a — the (3.156) subspace is genuinely exercised: `e₀` IS in it, `e₁` is NOT -/

theorem richWitnessFamily_deltaKSubspace_eq (k : ℕ) :
    deltaKSubspace richWitnessFamily k =
      LinearMap.ker (richQ1 k : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  unfold deltaKSubspace richWitnessFamily
  simp

theorem richWitnessFamily_eZero_mem_subspace (k : ℕ) :
    eZero ∈ deltaKSubspace richWitnessFamily k := by
  rw [richWitnessFamily_deltaKSubspace_eq]
  show richQ1 k eZero = 0
  show diagCLM 0 1 eZero = 0
  ext i
  unfold diagCLM
  rw [matCLM_apply]
  unfold eZero
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem richWitnessFamily_eOne_not_mem_subspace (k : ℕ) :
    eOne ∉ deltaKSubspace richWitnessFamily k := by
  rw [richWitnessFamily_deltaKSubspace_eq]
  show ¬ richQ1 k eOne = 0
  exact richQ1_eOne_ne_zero

#print axioms richWitnessFamily_deltaKSubspace_eq
#print axioms richWitnessFamily_eZero_mem_subspace
#print axioms richWitnessFamily_eOne_not_mem_subspace

/-! ### §4b — S82 mutation: a degenerate `Q1` makes the subspace VACUOUS

If `Q1` were the zero operator instead (the "I forgot the gauge-fixing condition" mutation),
`ker(Q1) = ⊤` and the (3.156) restriction would exclude NOTHING — confirming
`richWitnessFamily_eOne_not_mem_subspace` above is not vacuous, and genuinely depends on `Q1`'s
specific (non-degenerate) value. -/

theorem degenerate_Q1_subspace_vacuous :
    LinearMap.ker (0 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = ⊤ :=
  LinearMap.ker_zero

#print axioms degenerate_Q1_subspace_vacuous

/-! ### §4c — S82 mutation: the OLD pass-through `invertQGQstar` cannot satisfy `invertQGQstar_spec`
at this witness's own concrete data

At `k=0`: composite `= richQ 0 ∘ (G1 richWitnessFamily 0) ∘ richQstar 0 = diag(2,1)∘diag(1,1)∘diag(3,1)
= diag(6,1)`, a genuine unit. A pass-through `invertQGQstar := fun _ _ G _ => G` would need
`G1 richWitnessFamily 0 = diag(1,1)` to equal `Ring.inverse(diag(6,1)) = diag(1/6,1)` — false
(`1 ≠ 1/6`). The convicted shape is not merely undesirable here, it is UNSATISFIABLE. -/

theorem richWitnessFamily_G1_zero : G1 richWitnessFamily 0 = diagCLM 1 1 := rfl

theorem richWitnessFamily_composite_zero :
    (richQ 0).comp ((G1 richWitnessFamily 0).comp (richQstar 0)) = diagCLM 6 1 := by
  rw [richWitnessFamily_G1_zero]
  show diagCLM 2 1 * (diagCLM 1 1 * diagCLM 3 1) = diagCLM 6 1
  rw [diagCLM_mul, diagCLM_mul]
  norm_num

theorem passthrough_invertQGQstar_fails_spec_at_zero :
    G1 richWitnessFamily 0 ≠
      Ring.inverse ((richQ 0).comp ((G1 richWitnessFamily 0).comp (richQstar 0))) := by
  rw [richWitnessFamily_composite_zero, richWitnessFamily_G1_zero,
    ring_inverse_diagCLM 6 1 (by norm_num) (by norm_num)]
  intro h
  have := congrFun (congrArg (fun (f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) =>
    WithLp.ofLp (f eZero)) h) 0
  unfold diagCLM at this
  rw [matCLM_apply, matCLM_apply] at this
  unfold eZero at this
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this

#print axioms richWitnessFamily_G1_zero
#print axioms richWitnessFamily_composite_zero
#print axioms passthrough_invertQGQstar_fails_spec_at_zero

/-! ### §4d — the genuine non-degeneracy witness: `deltaKQuadForm` at scale `0` vs scale `1`, at the
point `e₀` which IS in the (3.156) subspace, under a `invertQGQstar` that GENUINELY inverts -/

theorem richWitnessFamily_deltaKQuadForm_zero_eZero :
    deltaKQuadForm richWitnessFamily 0 eZero = 1 / 6 := by
  unfold deltaKQuadForm
  show (inner ℝ eZero (Ring.inverse ((richQ 0).comp ((G1 richWitnessFamily 0).comp (richQstar 0)))
      eZero) : ℝ) - (0:ℝ) * _ - 2 * (inner ℝ (0:EuclideanSpace ℝ (Fin 2)) (0:EuclideanSpace ℝ (Fin 2)) : ℝ)
      = 1 / 6
  rw [richWitnessFamily_composite_zero, ring_inverse_diagCLM 6 1 (by norm_num) (by norm_num)]
  simp [inner_eZero_diagCLM]

theorem richWitnessFamily_G1_one : G1 richWitnessFamily 1 = diagCLM (7 / 6) 1 := by
  show richWitnessFamily.feed 0 (deltaKQuadForm richWitnessFamily 0) = diagCLM (7/6) 1
  show diagCLM (deltaKQuadForm richWitnessFamily 0 eZero + 1) 1 = diagCLM (7/6) 1
  rw [richWitnessFamily_deltaKQuadForm_zero_eZero]
  norm_num

theorem richWitnessFamily_composite_one :
    (richQ 1).comp ((G1 richWitnessFamily 1).comp (richQstar 1)) = diagCLM 7 1 := by
  rw [richWitnessFamily_G1_one]
  show diagCLM 2 1 * (diagCLM (7/6) 1 * diagCLM 3 1) = diagCLM 7 1
  rw [diagCLM_mul, diagCLM_mul]
  norm_num

theorem richWitnessFamily_deltaKQuadForm_one_eZero :
    deltaKQuadForm richWitnessFamily 1 eZero = 1 / 7 := by
  unfold deltaKQuadForm
  show (inner ℝ eZero (Ring.inverse ((richQ 1).comp ((G1 richWitnessFamily 1).comp (richQstar 1)))
      eZero) : ℝ) - (0:ℝ) * _ - 2 * (inner ℝ (0:EuclideanSpace ℝ (Fin 2)) (0:EuclideanSpace ℝ (Fin 2)) : ℝ)
      = 1 / 7
  rw [richWitnessFamily_composite_one, ring_inverse_diagCLM 7 1 (by norm_num) (by norm_num)]
  simp [inner_eZero_diagCLM]

/-- **THE HEADLINE REPLACEMENT WITNESS.** `deltaKQuadForm richWitnessFamily 0 e₀ = 1/6 ≠ 1/7 =
deltaKQuadForm richWitnessFamily 1 e₀`, at a point `e₀` GENUINELY IN the (3.156) subspace
(`richWitnessFamily_eZero_mem_subspace`), under a GENUINELY inverting `invertQGQstar`
(`passthrough_invertQGQstar_fails_spec_at_zero` shows the old pass-through could not have produced
this). This is honest, non-monotone (`1/6 < 1/7` is FALSE — `1/6 > 1/7`; the sequence DECREASES here,
matching the prosecution's own `reciprocalFamily` finding that genuine inversion does not give
"unbounded growth") — no claim of monotonicity or unboundedness is made, only genuine, non-vacuous,
kernel-checked difference. -/
theorem richWitnessFamily_deltaKQuadForm_zero_ne_one_at_eZero :
    deltaKQuadForm richWitnessFamily 0 eZero ≠ deltaKQuadForm richWitnessFamily 1 eZero := by
  rw [richWitnessFamily_deltaKQuadForm_zero_eZero, richWitnessFamily_deltaKQuadForm_one_eZero]
  norm_num

#print axioms richWitnessFamily_deltaKQuadForm_zero_eZero
#print axioms richWitnessFamily_G1_one
#print axioms richWitnessFamily_composite_one
#print axioms richWitnessFamily_deltaKQuadForm_one_eZero
#print axioms richWitnessFamily_deltaKQuadForm_zero_ne_one_at_eZero

/-! ### §4e — the (3.138)-shaped `G1Op`/`feedOp`/`DeltaOp` mechanism is ALSO genuinely `k`-dependent
(§2b's positive demonstration) -/

theorem richWitnessFamily_G1Op_succ (k : ℕ) :
    G1Op richWitnessFamily (k + 1) = diagCLM ((k : ℝ) + 1) 1 := by
  show richWitnessFamily.feedOp k (richWitnessFamily.DeltaOp k) = diagCLM ((k:ℝ)+1) 1
  show diagCLM (WithLp.ofLp ((diagCLM (k:ℝ) 0) eZero) 0 + 1) 1 = diagCLM ((k:ℝ)+1) 1
  congr 2
  unfold diagCLM
  rw [matCLM_apply]
  unfold eZero
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **`G1Op` genuinely varies with `k`** (e.g. level `1` vs level `2` differ, `diag(1,1) ≠
diag(2,1)`) — driven entirely by `DeltaOp`, an OPERATOR argument, which is exactly the shape §2b
argues (3.138) supports and `feed`'s `H → ℝ` shape does not. -/
theorem richWitnessFamily_G1Op_one_ne_two :
    G1Op richWitnessFamily 1 ≠ G1Op richWitnessFamily 2 := by
  rw [richWitnessFamily_G1Op_succ 0, richWitnessFamily_G1Op_succ 1]
  intro h
  have := congrFun (congrArg (fun (f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) =>
    WithLp.ofLp (f eZero)) h) 0
  unfold diagCLM at this
  rw [matCLM_apply, matCLM_apply] at this
  unfold eZero at this
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this

#print axioms richWitnessFamily_G1Op_succ
#print axioms richWitnessFamily_G1Op_one_ne_two

/-! ### §4f — S82 mutation: a degenerate `feedOp` (ignoring `D`) collapses `G1Op` too, confirming
`richWitnessFamily_G1Op_one_ne_two` is not vacuous -/

/-- Identical to `richWitnessFamily` except `feedOp` ignores its `D` argument. -/
noncomputable def richWitnessFamilyDegenerateFeedOp :
    RGScaleFamily (EuclideanSpace ℝ (Fin 2)) where
  Lambda := fun _ => ⊤
  Lambda_anti := antitone_const
  LambdaSmall := fun _ => ⊤
  LambdaSmall_le := fun _ => le_refl ⊤
  AxZeroLocus := fun _ => ⊤
  Q := richQ
  Qstar := richQstar
  Q1 := richQ1
  a := fun _ => 0
  H1 := fun _ => 0
  Dtilde2 := fun _ B => B
  J := fun _ => 0
  G1base := diagCLM 1 1
  invertQGQstar := fun _ Q G Qstar => Ring.inverse (Q.comp (G.comp Qstar))
  invertQGQstar_spec := fun _ _ _ => rfl
  feed := fun _ g => diagCLM (g eZero + 1) 1
  DeltaOp := fun k => diagCLM (k : ℝ) 0
  feedOp := fun _ _ => diagCLM 1 1

theorem richWitnessFamilyDegenerateFeedOp_G1Op_eq (k : ℕ) :
    G1Op richWitnessFamilyDegenerateFeedOp k = diagCLM 1 1 := by
  cases k with
  | zero => rfl
  | succ n => rfl

#print axioms richWitnessFamilyDegenerateFeedOp_G1Op_eq

/-! ### §4g — nested-verifier finding (2026-07-22): `DeltaOp` itself was NOT separately mutated
(§4f only mutated `feedOp`). Closed here: identical to `richWitnessFamily` except `DeltaOp` is
CONSTANT in `k` — isolates `DeltaOp`'s own contribution from `feedOp`'s. -/

/-- Identical to `richWitnessFamily` except `DeltaOp` is constant (`diag(0,0)` at every `k`,
instead of `diag(k,0)`). -/
noncomputable def richWitnessFamilyConstantDeltaOp :
    RGScaleFamily (EuclideanSpace ℝ (Fin 2)) where
  Lambda := fun _ => ⊤
  Lambda_anti := antitone_const
  LambdaSmall := fun _ => ⊤
  LambdaSmall_le := fun _ => le_refl ⊤
  AxZeroLocus := fun _ => ⊤
  Q := richQ
  Qstar := richQstar
  Q1 := richQ1
  a := fun _ => 0
  H1 := fun _ => 0
  Dtilde2 := fun _ B => B
  J := fun _ => 0
  G1base := diagCLM 1 1
  invertQGQstar := fun _ Q G Qstar => Ring.inverse (Q.comp (G.comp Qstar))
  invertQGQstar_spec := fun _ _ _ => rfl
  feed := fun _ g => diagCLM (g eZero + 1) 1
  DeltaOp := fun _ => diagCLM 0 0
  feedOp := fun _ D => diagCLM (WithLp.ofLp (D eZero) 0 + 1) 1

/-- **`DeltaOp`'s own contribution is load-bearing, independent of `feedOp`'s**: with the SAME
(non-degenerate) `feedOp` as `richWitnessFamily`, but a CONSTANT `DeltaOp`, `G1Op` collapses to a
constant sequence — confirming `richWitnessFamily_G1Op_one_ne_two`'s non-degeneracy genuinely needs
BOTH `feedOp` to read its argument AND `DeltaOp` to vary with `k`, not merely one or the other. -/
theorem richWitnessFamilyConstantDeltaOp_G1Op_eq (k : ℕ) :
    G1Op richWitnessFamilyConstantDeltaOp (k + 1) = diagCLM 1 1 := by
  show richWitnessFamilyConstantDeltaOp.feedOp k (richWitnessFamilyConstantDeltaOp.DeltaOp k)
    = diagCLM 1 1
  show diagCLM (WithLp.ofLp ((diagCLM (0:ℝ) 0) eZero) 0 + 1) 1 = diagCLM 1 1
  congr 2
  unfold diagCLM
  rw [matCLM_apply]
  unfold eZero
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

#print axioms richWitnessFamilyConstantDeltaOp_G1Op_eq

/-! ### §4h — NAMED RESIDUAL, not papered over (nested-verifier finding): `LambdaSmall`/
`AxZeroLocus` carry NO independent falsifiability evidence in THIS witness

`richWitnessFamily_deltaKSubspace_eq` shows `deltaKSubspace richWitnessFamily k` collapses to
`ker(Q1 k)` alone, because `LambdaSmall`/`AxZeroLocus` are BOTH `⊤` here — every membership/
non-membership fact in §4a is driven entirely by `Q1`, not by these two fields. This was attempted
and found to hit a genuine, disclosed obstruction, not silently elided: on a `2`-dimensional
carrier, ANY submodule properly containing `eZero` and strictly smaller than `⊤` must equal
`span{eZero} = ker(Q1)` itself (a `1`-dimensional space has no room for a THIRD distinct
non-trivial subspace alongside `⊥`, `span{eZero}`, `⊤`) — so `LambdaSmall`/`AxZeroLocus` cannot be
given a value on THIS carrier that both (a) keeps `eZero` a member and (b) is independently
falsifiable from `Q1`'s own kernel. Closing this genuinely (not just asserting the field's TYPE is
non-vacuous, which `LambdaChain` §5 and `Q1`'s own kernel already establish for `Submodule ℝ H`)
would need a carrier of dimension `≥3` and a` matCLM`/`diagCLM` generalization to match — named here
as the exact missing primitive for the next lane, not built in this pass. `AxZeroLocus`'s own
bond-geometry content (`Ax(y)` itself) remains separately LACK regardless of carrier dimension (see
the ingredient inventory table, §0). -/

/-! ## §5 — WHAT `Λ` DOES: a genuinely strictly-shrinking chain of submodules (ACQUITTED, unchanged)

`LambdaChain`, on `H' := Fin 2 → ℝ` (independent of `richWitnessFamily`'s
`H := EuclideanSpace ℝ (Fin 2)`), is a genuine, non-vacuous, strictly-shrinking 2-step chain,
independently confirmed by the prosecution (`PROS_DELTAK_REC.md` C4, ACQUITTED-AS-TESTED). Carried
forward verbatim. -/

/-- **A genuinely strictly-shrinking `Λ`-chain**, on `H' := Fin 2 → ℝ`: `Λ_0 = ⊤` (all of `H'`,
dimension `2`), `Λ_1 = \ker(\mathrm{proj}_0)` (dimension `1`), `Λ_{k≥2} = ⊥` (dimension `0`). -/
def LambdaChain : ℕ → Submodule ℝ (Fin 2 → ℝ)
  | 0 => ⊤
  | 1 => (LinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).ker
  | _ + 2 => ⊥

/-- The chain satisfies the SAME nesting hypothesis `RGScaleFamily.Lambda_anti` requires. -/
theorem LambdaChain_antitone : Antitone LambdaChain := by
  apply antitone_nat_of_succ_le
  intro n
  match n with
  | 0 => exact le_top
  | 1 => exact bot_le
  | n + 2 => exact le_refl _

/-- **`Λ_1` is a PROPER subspace of `Λ_0`**. -/
theorem LambdaChain_one_ne_top : LambdaChain 1 ≠ ⊤ := by
  intro h
  have hmem : (fun _ : Fin 2 => (1 : ℝ)) ∈ LambdaChain 1 := by rw [h]; trivial
  change (fun _ : Fin 2 => (1 : ℝ)) ∈ (LinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).ker
    at hmem
  simp [LinearMap.mem_ker, LinearMap.proj_apply] at hmem

/-- **`Λ_2` is a PROPER subspace of `Λ_1`**. -/
theorem LambdaChain_two_ne_one : LambdaChain 2 ≠ LambdaChain 1 := by
  intro h
  have hne : (Pi.single (1 : Fin 2) (1 : ℝ)) ∈ LambdaChain 1 := by
    change Pi.single (1 : Fin 2) (1 : ℝ) ∈ (LinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).ker
    simp [LinearMap.mem_ker, LinearMap.proj_apply, Pi.single_eq_of_ne]
  rw [← h] at hne
  change Pi.single (1 : Fin 2) (1 : ℝ) ∈ (⊥ : Submodule ℝ (Fin 2 → ℝ)) at hne
  rw [Submodule.mem_bot] at hne
  have := congrFun hne 1
  simp [Pi.single_eq_same] at this

#print axioms LambdaChain_antitone
#print axioms LambdaChain_one_ne_top
#print axioms LambdaChain_two_ne_one

/-! ## §6 — WHAT COSTS THE DROP: `BondFnL2 L` (`BondSU2Space.lean`) has NO `Lambda` field at all
(ACQUITTED-context finding, unchanged) — every consumer of `BondFnL2 L` as CMP99b's unit-lattice bond
space is implicitly asserting `Λ_k = ` the whole lattice at every scale, which is false to the
source. This file does not repair that consumer (out of write-scope). -/

end AdalyFormal.Balaban.DeltaKRecursive
