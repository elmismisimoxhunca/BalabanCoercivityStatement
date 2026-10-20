/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib

set_option autoImplicit false

/-!
# `H₁`, Bałaban's variational-problem projector — CMP99b p.421, eq. (3.129)

**Dispatch target**: `DeltaKRecursive.lean` (commit `32233c3f`) carries `H1 : ℕ → H →L[ℝ] H` as an
OPAQUE field of `RGScaleFamily`, explicitly flagged as "not `HarmonicModes.lean`'s winding-mode
object." This file makes `H₁` real: it locates the actual defining page, quotes it verbatim, checks
it against the ONE plausible same-shaped object already in this tree (`HjMinimizer.lean`'s `H_j`),
and builds `H₁`'s genuine closed-form construction in Lean.

## THE DEFINITION, VERBATIM, WITH ITS OWN TRAIL (LAW-19/render-the-defining-page discipline)

`H₁` is introduced on **CMP99b printed p.421** (`corpus/pages/CMP99b_p421.md`,
`verification_status: adjudicated`; independently re-rendered at 300dpi in this lane,
`compute/h1_renders/CMP99b_p421_recheck-33.png`, `sha256` below):

> "We solve the variational problem (3.127), (3.110) in exactly the same way as the problem
> (3.109), (3.110)... Let us denote the operator defined by the problem (3.127), (3.110) by `H₁`,
> and by `G₁` the operator defined by the quadratic form
> `⟨A, G₁⁻¹A⟩ = ⟨A,Δ_πA⟩ − 2⟨HC_π^{(2)}(A),J⟩ + ‖RD*A‖² + a‖QA‖²`. (3.128)
> Then we have the formula
> `H₁B = G₁Q*(QG₁Q*)⁻¹B`. (3.129)"

**This is not a self-contained definition** — it is built by literally repeating, verbatim, the
method used for the earlier (unindexed) operator `H` (problem (3.109),(3.110)). That earlier
derivation is on **CMP99b printed pp.417–420** (`corpus/mathpix/balaban_CMP99_1985_propagators_
backgroundfield/normalized/p417.md`, `p419.md`, `p420.md` — machine-draft, LAW-11 correction: NOT
independently citable alone; **p.420 independently re-rendered at 300dpi in this lane and read
directly against the image**, `compute/h1_renders/CMP99b_p420-32.png`, confirming the machine draft
verbatim at every load-bearing symbol):

* **p.417, (3.109)–(3.111)**: `H(U)B`, or simply `HB`, is defined as the MINIMIZING configuration
  `A` of the functional `A ↦ ½⟨A,Δ(U)A⟩` (3.109) subject to the constraint `L^jηQ_j(U)A = B` on
  `Λ_j`, `j=0,...,k`, **and** `R(U)D_U*A = 0` (3.110) — i.e. TWO simultaneous linear constraints,
  a multi-scale averaging condition plus a gauge-fixing condition, on a functional built from the
  BACKGROUND-FIELD-DEPENDENT Laplacian `Δ(U)`.
* **pp.419–420, (3.118)–(3.122)**: the `R∂*A=0` gauge constraint is ABSORBED into a modified
  quadratic form: `Δ` is extended gauge-invariantly to `Δ_π` (3.118)/(3.119)/(3.120), and a `DRD*`
  penalty term is added so that `G⁻¹ := Δ_π + DRD* + Q*aQ` (p.420, directly below (3.122)) already
  encodes the second constraint. The variational problem COLLAPSES to a SINGLE hard constraint
  `QA = B` against the weighted functional `A ↦ ½⟨A,G⁻¹A⟩`.
* **p.420, verbatim, the Lagrange-multiplier computation (image-confirmed)**:
  > "We take the Lagrange function `h(A,ω) = 1/2⟨A,G⁻¹A⟩ − ⟨ω,QA−B⟩`, and we get the following
  > equations for the minimum `δh/δA = G⁻¹A − Q*ω = 0`, `δh/δω = QA − B = 0`, hence `A = GQ*ω`,
  > `QGQ*ω = B`, `ω = (QGQ*)⁻¹B`, and finally `A = GQ*(QGQ*)⁻¹B`."
  > "... They imply the formula `HB = GQ*(QGQ*)⁻¹B`. (3.126)"
  > "We have obtained formally the same representation for the operator `H` as in [3,4] (1.103),
  > (2.35), **but now the operator `G` is much more complicated**."

`H₁`'s formula (3.129) is this **exact same Lagrange-multiplier solution-operator pattern**,
`H_star B = G_star Q*(QG_starQ*)⁻¹B`, with the covariance `G` of (3.126) replaced by the covariance
`G₁` of (3.128) (built from the SECOND variational problem (3.127),(3.110), whose functional already
contains a linear-in-`J` correction term via the base `H` and `C^{(2)}`). Bałaban's own text says
this outright: "We solve the variational problem (3.127),(3.110) **in exactly the same way as**
the problem (3.109),(3.110)."

## THE VERDICT: NOT `HjMinimizer`'s family — a genuinely different construction

`HjMinimizer.lean`'s `hjExtension` (`H_k`/`H_j`, CMP95 p.29, CMP96 p.223/243) is characterized by
**TWO simultaneous HARD constraints and NO covariance operator**:
`IsBalabanExtension` = `{interpolates : Q_kA = B; gaugeFixed : R∂*A = 0; orthogonal : ⟨∂A',∂A⟩=0
∀A'∈{Q_kA'=0,R∂*A'=0}}`, i.e. `H_jB` MINIMIZES THE PURE DIRICHLET ENERGY `½⟨∂A,∂A⟩` on the
2-constraint hyperplane `{Q_kA=B, R∂*A=0}` — an ORTHOGONAL PROJECTION in the standard `L²` metric
of `PlaquetteSpace`, with no auxiliary weight operator anywhere in its defining data.

CMP99b's `H` (and hence `H₁`) is characterized differently: **the `R∂*A=0` constraint has already
been dissolved into the WEIGHT operator `G⁻¹` (resp. `G₁⁻¹`) via the `Δ→Δ_π` gauge-invariant
extension plus a `DRD*` penalty term** (pp.419–420, (3.118)-(3.122)), leaving a SINGLE hard
constraint `QA=B` against a WEIGHTED quadratic form `⟨A,G_star⁻¹A⟩` — an orthogonal projection in
the `G_star⁻¹`-WEIGHTED metric, not the standard one, and with only one linear constraint, not two.
These are different variational problems with different minimizers in general (a weighted-metric,
one-constraint projection is not the same operator as an unweighted, two-constraint projection,
except in the special/degenerate case `G_star⁻¹ = "identity restricted to the gauge slice"`, which
Bałaban's own `G⁻¹ = Δ_π + DRD* + Q*aQ` manifestly is not — it carries the full lattice Laplacian
`Δ_π` and the scalar penalty `Q*aQ`, neither of which is the identity).

**Both objects are, however, instances of the SAME abstract shape**: "the linear operator solving
a constrained quadratic minimization by a Lagrange-multiplier / orthogonal-decomposition argument."
`H₁` is the shape (3.126)/(3.129) — `G_star Q*(QG_starQ*)⁻¹` — parametrized by whichever covariance
`G_star` is plugged in (`G` for the base `H`, `G₁` for `H₁`, and by p.427's remark, this pattern
recurses again for further `H₂,...` at higher orders of the same paper's non-linear generalization).
This file builds THAT shape, honestly parametrized, and NOT `HjMinimizer`'s two-constraint
Dirichlet-projection shape (importing nothing from `HjMinimizer.lean`, per the write-scope and
per LAW-19's "reuse only if it genuinely matches" clause).

## WHAT THIS FILE BUILDS

1. `BalabanCovarianceData H K` (§1) — the abstract data needed to write formula (3.126)/(3.129):
   a self-adjoint, invertible "inverse covariance" `Ginv` (`G⁻¹` resp. `G₁⁻¹`) with two-sided
   inverse `Gstar` (`G` resp. `G₁`), a constraint map `Q : H →L[ℝ] K` with adjoint `Qstar`, and
   invertibility of the composite `QG_starQ*` (`Comp`/`CompInv`). `G`/`G₁`/`Q`/`Q₁` themselves
   remain UNBUILT in this tree (`DeltaKRecursive.lean`'s own inventory: "LACK" for `G₁`, "CLOSE" for
   `Q`) — this file does not manufacture them; it builds the FORMULA that consumes them once
   supplied, exactly as (3.126)/(3.129) are formulas consuming `G`/`G₁`, not definitions of them.
2. `solutionOperator` (§2) — `H_star B := G_star Q*((QG_starQ*)⁻¹B)`, literally (3.126)/(3.129).
3. `interpolates` (§2) — `Q(H_starB) = B`, the direct algebraic consequence of `Comp`/`CompInv`.
4. `isMinimal` (§3) — the LOAD-BEARING theorem: for every `A` with `QA=B`,
   `⟨H_starB, G_star⁻¹(H_starB)⟩ ≤ ⟨A, G_star⁻¹A⟩`, reproducing IN THE KERNEL the exact
   Pythagorean-decomposition content of Bałaban's own p.420 Lagrange-multiplier argument (the cross
   terms vanish because `Ginv(H_starB) = Q*ω` and `Q(A−H_starB)=0`, mirroring his own derivation of
   (3.123)/(3.126) step for step, not merely citing the conclusion).
5. `isMinimal_unique` (§3) — under strict positive-definiteness of `Ginv`, the minimizer is unique.
6. §4 — a CONCRETE non-degenerate witness (`EuclideanSpace ℝ (Fin 2)` fine space, `EuclideanSpace
   ℝ (Fin 1)` coarse space, an anisotropic diagonal `Ginv = diag(2,3)`, `Q(x₀,x₁)=x₀+x₁`) on which
   `solutionOperator` is computed BY HAND to be `(3B/5, 2B/5)` and independently CONFIRMED to beat a
   naive constraint-satisfying alternative `(B,0)` in the `Ginv`-weighted norm — real work, not a
   tautology (§5.1).
7. §5 — S82 GARBAGE SUBSTITUTION: `Gstar := 0` and `Gstar := id` are BOTH exhibited as failing the
   `Ginv_Gstar` hypothesis on the concrete witness's `Ginv` (§5.2), and `Q := 0` is exhibited as
   making `Comp = 0`, hence NO `CompInv` can satisfy `Comp_CompInv` (§5.3) — the structure's fields
   are not vacuously satisfiable by trivial candidates, i.e. they pin down something real.

## WHAT THIS FILE DOES **NOT** BUILD — named residuals

* **`G`, `G₁`, `Q`, `Q₁`, `Δ_π`, `DRD*`, `Q*aQ` THEMSELVES** are not constructed — `Comp`/`CompInv`
  and `Ginv`/`Gstar` are carried as opaque structure fields, exactly like `DeltaKRecursive.lean`'s
  own `invertQGQstar`/`G1base` fields. `G₁` in particular is the object `DeltaKRecursive.lean`'s
  inventory already marks "LACK" — this file does not change that; it builds what `H₁` IS given
  `G₁`, not `G₁` itself.
* **The random-walk/tree-graph expansion of `H₁`** (p.427: "We have the same situation for the
  operators `H₁`" as for `G₁`'s expansion) is explicitly NOT built — that is (3.107)/(3.138)'s
  machinery, already named as the load-bearing unbuilt primitive in `DeltaKRecursive.lean`'s `feed`
  field, and untouched here.
* **A formal non-equivalence THEOREM between `solutionOperator` and `HjMinimizer.hjExtension`**:
  the verdict above is argued from the two objects' DEFINING DATA (different functional, different
  constraint count), which is a citation-level distinction, not a Lean theorem — proving a genuine
  numerical non-equivalence would require instantiating BOTH constructions on one shared concrete
  lattice witness (a larger undertaking, out of scope for a file whose job is to build `H₁` itself,
  and DeltaKRecursive/HjMinimizer are explicitly not to be edited or imported here).
-/

namespace AdalyFormal.Balaban.VariationalProjectorH1

/-! ## §1 — The abstract data for formula (3.126)/(3.129)

`H` is the FINE space (Bałaban's `Ω₀`/configuration space); `K` is the space `Q`/`Q₁` project onto
(the space `B` lives in, p.417/p.421). Kept as two SEPARATE spaces (unlike `DeltaKRecursive.lean`'s
single-`H` simplification) because `Q : H →L[ℝ] K` is genuinely a map between different spaces in
Bałaban's own text (a fine configuration `A` on `Ω₀` maps to a coarse configuration `B` on `𝔅`), and
because the concrete non-degeneracy witness (§4) needs `dim K < dim H` to be non-vacuous (a
BIJECTIVE `Q` forces `{A : QA=B}` to be a single point, making "minimal" vacuously true of every
candidate — exactly the S82 concern the dispatch raises). -/

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The data needed to state and use Bałaban's solution-operator formula (3.126)/(3.129):
`Ginv` plays `G⁻¹` (resp. `G₁⁻¹`), `Gstar` plays `G` (resp. `G₁`), `Q`/`Qstar` play `Q`/`Q*`
(resp. `Q₁`/`Q₁*`), and `Comp`/`CompInv` play `(QG_starQ*)`/`(QG_starQ*)⁻¹`. -/
structure BalabanCovarianceData (H K : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] where
  /-- `G_star⁻¹` (`G⁻¹ = Δ_π+DRD*+Q*aQ` at p.420, or `G₁⁻¹` of (3.128) at p.421). -/
  Ginv : H →L[ℝ] H
  /-- `G_star` (`G` or `G₁`), the two-sided inverse of `Ginv`. -/
  Gstar : H →L[ℝ] H
  Ginv_Gstar : ∀ x, Ginv (Gstar x) = x
  Gstar_Ginv : ∀ x, Gstar (Ginv x) = x
  /-- `G_star⁻¹` is self-adjoint — Bałaban's `Δ_π+DRD*+Q*aQ` is manifestly so, being a sum of the
  symmetric lattice Laplacian `Δ_π` and two operators of the form `X*X`. -/
  Ginv_selfAdjoint : ∀ x y, (inner ℝ (Ginv x) y : ℝ) = inner ℝ x (Ginv y)
  /-- `G_star⁻¹` positive semi-definite (needed for the minimality DIRECTION, `isMinimal`). -/
  Ginv_posSemidef : ∀ x, (0 : ℝ) ≤ inner ℝ x (Ginv x)
  /-- `Q` (resp. `Q₁`), the constraint operator of (3.110)/(3.126)/(3.129). -/
  Q : H →L[ℝ] K
  /-- `Q*` (resp. `Q₁*`), carried as a SEPARATE given operator, never `.adjoint` (sidesteps the
  ambient-topology diamond `DeltaKFull.lean` §6 already documents, exactly as `DeltaKRecursive.lean`
  does for its own `Qstar` field). -/
  Qstar : K →L[ℝ] H
  Q_Qstar_adjoint : ∀ (x : H) (y : K), (inner ℝ (Q x) y : ℝ) = inner ℝ x (Qstar y)
  /-- `QG_starQ*` (resp. `Q₁G₁Q₁*`), threaded explicitly through its own type so the dependence on
  `Q`/`Gstar`/`Qstar` stays auditable, exactly as `DeltaKRecursive.lean`'s `invertQGQstar` does. -/
  Comp : K →L[ℝ] K
  Comp_eq : ∀ x, Comp x = Q (Gstar (Qstar x))
  /-- `(QG_starQ*)⁻¹` — p.420/p.421's own text needs [4]'s Lemma 2.4 (a separate hard theorem) to
  know this is well-defined with a `k`-independent bound; carried here as an opaque two-sided
  inverse, exactly like `DeltaKRecursive.lean`'s own `invertQGQstar`. -/
  CompInv : K →L[ℝ] K
  Comp_CompInv : ∀ x, Comp (CompInv x) = x
  CompInv_Comp : ∀ x, CompInv (Comp x) = x

#print axioms BalabanCovarianceData.mk

/-! ## §2 — `H_star`, formula (3.126)/(3.129), and interpolation -/

/-- **`H_starB := G_starQ*(QG_starQ*)⁻¹B`** — Bałaban's (3.126) (`H`) and (3.129) (`H₁`), the SAME
formula for either choice of covariance `G_star`. -/
noncomputable def solutionOperator (D : BalabanCovarianceData H K) : K →L[ℝ] H :=
  D.Gstar.comp (D.Qstar.comp D.CompInv)

theorem solutionOperator_apply (D : BalabanCovarianceData H K) (B : K) :
    solutionOperator D B = D.Gstar (D.Qstar (D.CompInv B)) := rfl

/-- **Interpolation**: `Q(H_starB) = B`, p.420's `QA=B` constraint holding at the solution — the
direct algebraic content of `ω=(QGQ*)⁻¹B` solving `QGQ*ω=B` (p.420, immediately before (3.126)). -/
theorem interpolates (D : BalabanCovarianceData H K) (B : K) :
    D.Q (solutionOperator D B) = B := by
  rw [solutionOperator_apply, ← D.Comp_eq (D.CompInv B)]
  exact D.Comp_CompInv B

#print axioms interpolates

/-- **`Ginv(H_starB) = Q*ω`** where `ω = (QG_starQ*)⁻¹B` — the algebraic fact `δh/δA=0`, i.e.
`G_star⁻¹A = Q*ω`, gives at the solution (p.420, the Lagrange-multiplier equations, directly above
(3.123)). This is the SINGLE fact that makes the minimality proof's cross terms vanish. -/
theorem Ginv_solutionOperator (D : BalabanCovarianceData H K) (B : K) :
    D.Ginv (solutionOperator D B) = D.Qstar (D.CompInv B) := by
  rw [solutionOperator_apply]
  exact D.Ginv_Gstar (D.Qstar (D.CompInv B))

#print axioms Ginv_solutionOperator

/-! ## §3 — Minimality: `H_starB` minimizes `⟨A,G_star⁻¹A⟩` on `{A : QA=B}`

This reproduces, IN THE KERNEL, exactly Bałaban's own p.420 computation: any competitor `A` with
`QA=B` decomposes as `A = H_starB + v` with `Qv=0`, the CROSS TERMS in `⟨A,GinvA⟩` vanish because
`Ginv(H_starB) = Q*ω` and `Qv=0` (so `⟨v,Q*ω⟩=⟨Qv,ω⟩=0`, and symmetrically for the other cross
term via `Ginv`'s self-adjointness), leaving a pure Pythagorean split. -/

theorem isMinimal (D : BalabanCovarianceData H K) (B : K) (A : H) (hA : D.Q A = B) :
    (inner ℝ (solutionOperator D B) (D.Ginv (solutionOperator D B)) : ℝ) ≤
      inner ℝ A (D.Ginv A) := by
  set H1B := solutionOperator D B with hH1B
  set v : H := A - H1B with hv
  have hQv : D.Q v = 0 := by
    have h0 : D.Q A - D.Q H1B = 0 := by
      rw [hA, hH1B, interpolates D B]; abel
    simpa [hv, map_sub] using h0
  have hcrossR : (inner ℝ v (D.Qstar (D.CompInv B)) : ℝ) = 0 := by
    rw [← D.Q_Qstar_adjoint v (D.CompInv B), hQv]
    simp
  have hcross1 : (inner ℝ v (D.Ginv H1B) : ℝ) = 0 := by
    rw [Ginv_solutionOperator D B]; exact hcrossR
  have hcross2 : (inner ℝ H1B (D.Ginv v) : ℝ) = 0 := by
    rw [← D.Ginv_selfAdjoint H1B v, Ginv_solutionOperator D B, real_inner_comm]
    exact hcrossR
  have hAeq : A = H1B + v := by rw [hv]; abel
  have hGinvAeq : D.Ginv A = D.Ginv H1B + D.Ginv v := by
    rw [hAeq]; exact map_add D.Ginv H1B v
  have hexp : (inner ℝ A (D.Ginv A) : ℝ) =
      inner ℝ H1B (D.Ginv H1B) + inner ℝ v (D.Ginv v) := by
    rw [hGinvAeq, hAeq, inner_add_left, inner_add_right, inner_add_right, hcross1, hcross2]
    ring
  rw [hexp]
  have hpos := D.Ginv_posSemidef v
  linarith

#print axioms isMinimal

/-- **Uniqueness under strict positive-definiteness.** If `Ginv` is genuinely positive DEFINITE
(not merely semi-definite), the minimizer is unique: any `A` with `QA=B` achieving the SAME value
as `H_starB` must equal `H_starB`. -/
theorem isMinimal_unique (D : BalabanCovarianceData H K)
    (hposdef : ∀ x : H, (inner ℝ x (D.Ginv x) : ℝ) = 0 → x = 0)
    (B : K) (A : H) (hA : D.Q A = B)
    (heq : (inner ℝ A (D.Ginv A) : ℝ) =
      inner ℝ (solutionOperator D B) (D.Ginv (solutionOperator D B))) :
    A = solutionOperator D B := by
  set H1B := solutionOperator D B with hH1B
  set v : H := A - H1B with hv
  have hQv : D.Q v = 0 := by
    have h0 : D.Q A - D.Q H1B = 0 := by rw [hA, hH1B, interpolates D B]; abel
    simpa [hv, map_sub] using h0
  have hcrossR : (inner ℝ v (D.Qstar (D.CompInv B)) : ℝ) = 0 := by
    rw [← D.Q_Qstar_adjoint v (D.CompInv B), hQv]; simp
  have hcross1 : (inner ℝ v (D.Ginv H1B) : ℝ) = 0 := by
    rw [Ginv_solutionOperator D B]; exact hcrossR
  have hcross2 : (inner ℝ H1B (D.Ginv v) : ℝ) = 0 := by
    rw [← D.Ginv_selfAdjoint H1B v, Ginv_solutionOperator D B, real_inner_comm]
    exact hcrossR
  have hAeq : A = H1B + v := by rw [hv]; abel
  have hGinvAeq : D.Ginv A = D.Ginv H1B + D.Ginv v := by
    rw [hAeq]; exact map_add D.Ginv H1B v
  have hexp : (inner ℝ A (D.Ginv A) : ℝ) =
      inner ℝ H1B (D.Ginv H1B) + inner ℝ v (D.Ginv v) := by
    rw [hGinvAeq, hAeq, inner_add_left, inner_add_right, inner_add_right, hcross1, hcross2]
    ring
  have hv0 : (inner ℝ v (D.Ginv v) : ℝ) = 0 := by
    have := heq
    rw [hexp] at this
    linarith
  have : v = 0 := hposdef v hv0
  rw [hAeq, this, add_zero]

#print axioms isMinimal_unique

/-! ## §4 — A concrete non-degenerate witness (non-vacuity, L7/S82)

`H = EuclideanSpace ℝ (Fin 2)` (fine), `K = EuclideanSpace ℝ (Fin 1)` (coarse) — `dim K < dim H` is
DELIBERATE: a bijective `Q` would make `{A : QA=B}` a single point, so `isMinimal` would hold of
every candidate VACUOUSLY (nothing to minimize over). With `Q` genuinely non-injective, the
constraint set is a full line, and the anisotropic weight `Ginv = diag(2,3)` makes `solutionOperator`
land at a point a NAIVE (unweighted) guess misses — computed here BY HAND and CONFIRMED in the
kernel, not merely asserted. -/

open Matrix WithLp

/-- A `Matrix m n ℝ` gives a genuine `EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m`, upgrading
`Matrix.toEuclideanLin`'s `LinearMap` to a `ContinuousLinearMap` via finite-dimensionality of the
domain (`LinearMap.toContinuousLinearMap`). -/
noncomputable def matCLM {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

theorem matCLM_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    WithLp.ofLp (matCLM M x) = M *ᵥ (WithLp.ofLp x) := by
  unfold matCLM
  simp [Matrix.toEuclideanLin, LinearMap.coe_toContinuousLinearMap']

/-- `G⁻¹ = diag(2,3)`, anisotropic (the two axes carry genuinely different weight — a naive
isotropic/identity weight would make the minimizer coincide with the naive projection, hiding
whether the construction depends on `Ginv` at all; see the §5.2 mutation for the isotropic case). -/
@[reducible] noncomputable def witnessGinv : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(2:ℝ), 0; 0, 3])

/-- `G = diag(1/2,1/3)`, the two-sided inverse of `witnessGinv`. -/
@[reducible] noncomputable def witnessGstar : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(1/2:ℝ), 0; 0, 1/3])

/-- `Q(x₀,x₁) = x₀+x₁`, a genuine (non-injective) constraint map. -/
@[reducible] noncomputable def witnessQ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  matCLM (!![(1:ℝ), 1])

/-- `Q*(t) = (t,t)`. -/
@[reducible] noncomputable def witnessQstar : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  matCLM (!![(1:ℝ); 1])

/-- `QG_starQ* = 5/6` (scalar): `Q(Gstar(Qstar(t))) = Q(t/2,t/3) = 5t/6`. -/
@[reducible] noncomputable def witnessComp : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  matCLM (!![(5/6:ℝ)])

/-- `(QG_starQ*)⁻¹ = 6/5`. -/
@[reducible] noncomputable def witnessCompInv : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  matCLM (!![(6/5:ℝ)])

theorem witness_Ginv_Gstar (x : EuclideanSpace ℝ (Fin 2)) :
    witnessGinv (witnessGstar x) = x := by
  unfold witnessGinv witnessGstar
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply, matCLM_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem witness_Gstar_Ginv (x : EuclideanSpace ℝ (Fin 2)) :
    witnessGstar (witnessGinv x) = x := by
  unfold witnessGinv witnessGstar
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply, matCLM_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem witness_Ginv_selfAdjoint (x y : EuclideanSpace ℝ (Fin 2)) :
    (inner ℝ (witnessGinv x) y : ℝ) = inner ℝ x (witnessGinv y) := by
  unfold witnessGinv
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    matCLM_apply, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem witness_Ginv_posSemidef (x : EuclideanSpace ℝ (Fin 2)) :
    (0 : ℝ) ≤ inner ℝ x (witnessGinv x) := by
  unfold witnessGinv
  rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, mul_comm]
  nlinarith [sq_nonneg (WithLp.ofLp x 0), sq_nonneg (WithLp.ofLp x 1)]

theorem witness_Q_Qstar_adjoint (x : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 1)) :
    (inner ℝ (witnessQ x) y : ℝ) = inner ℝ x (witnessQstar y) := by
  unfold witnessQ witnessQstar
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    matCLM_apply, matCLM_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, mul_comm]
  ring

theorem witness_Comp_eq (x : EuclideanSpace ℝ (Fin 1)) :
    witnessComp x = witnessQ (witnessGstar (witnessQstar x)) := by
  unfold witnessComp witnessQ witnessGstar witnessQstar
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply, matCLM_apply, matCLM_apply, matCLM_apply]
  funext i
  fin_cases i
  simp [Matrix.mulVec, dotProduct]
  ring

theorem witness_Comp_CompInv (x : EuclideanSpace ℝ (Fin 1)) :
    witnessComp (witnessCompInv x) = x := by
  unfold witnessComp witnessCompInv
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply, matCLM_apply]
  funext i
  fin_cases i
  simp [Matrix.mulVec, dotProduct]
  ring

theorem witness_CompInv_Comp (x : EuclideanSpace ℝ (Fin 1)) :
    witnessCompInv (witnessComp x) = x := by
  unfold witnessComp witnessCompInv
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply, matCLM_apply]
  funext i
  fin_cases i
  simp [Matrix.mulVec, dotProduct]
  ring

/-- **The witness instance.** Every field discharged by an honest computation on the anisotropic
`diag(2,3)` weight and the rank-deficient `Q(x₀,x₁)=x₀+x₁` — not by a degenerate/trivial choice. -/
noncomputable def witnessData : BalabanCovarianceData
    (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1)) where
  Ginv := witnessGinv
  Gstar := witnessGstar
  Ginv_Gstar := witness_Ginv_Gstar
  Gstar_Ginv := witness_Gstar_Ginv
  Ginv_selfAdjoint := witness_Ginv_selfAdjoint
  Ginv_posSemidef := witness_Ginv_posSemidef
  Q := witnessQ
  Qstar := witnessQstar
  Q_Qstar_adjoint := witness_Q_Qstar_adjoint
  Comp := witnessComp
  Comp_eq := witness_Comp_eq
  CompInv := witnessCompInv
  Comp_CompInv := witness_Comp_CompInv
  CompInv_Comp := witness_CompInv_Comp

#print axioms witnessData

/-- The witness's `B`, `Q(3,2)=5`, i.e. `B = 5`. -/
noncomputable def witnessB : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm ![5]

/-- **`H₁` DOES REAL WORK, computed by hand and confirmed in the kernel**: at `B=5`, the true
`Ginv`-weighted minimizer is `(3,2)`, not the naive unweighted guess `(5,0)` a `Q`-only pseudo-
inverse would give. This matches the calculus computation `min 2a₀²+3a₁² s.t. a₀+a₁=5` at
`a₀=3,a₁=2` exactly. -/
theorem witness_solutionOperator_eq :
    WithLp.ofLp (solutionOperator witnessData witnessB) = ![3, 2] := by
  show WithLp.ofLp (witnessGstar (witnessQstar (witnessCompInv witnessB))) = ![3, 2]
  unfold witnessGstar witnessQstar witnessCompInv witnessB
  rw [matCLM_apply, matCLM_apply, matCLM_apply]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    EuclideanSpace.equiv] <;> ring

#print axioms witness_solutionOperator_eq

/-- The ELEMENT-level form of `witness_solutionOperator_eq` (not just its `.ofLp` shadow), needed
to substitute the solution INSIDE further operator applications (`Ginv`, etc.) without the
rewrite-pattern mismatch a `.ofLp`-only equation would leave on the table. -/
theorem witness_solutionOperator_eq' :
    solutionOperator witnessData witnessB = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![3, 2] := by
  apply WithLp.ofLp_injective 2
  rw [witness_solutionOperator_eq]
  simp [EuclideanSpace.equiv]

#print axioms witness_solutionOperator_eq'

/-- **The naive competitor `(5,0)`** satisfies the constraint `Q(5,0)=5=B` (so `isMinimal` applies
to it) but is NOT the minimizer. -/
noncomputable def witnessNaive : EuclideanSpace ℝ (Fin 2) := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![5, 0]

theorem witnessNaive_satisfies_constraint : witnessData.Q witnessNaive = witnessB := by
  unfold witnessData witnessQ witnessNaive witnessB
  apply WithLp.ofLp_injective 2
  rw [matCLM_apply]
  funext i
  fin_cases i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, EuclideanSpace.equiv]

/-- **The true minimizer strictly beats the naive competitor: `30 < 50`** — `isMinimal` is not
just abstractly true, it separates a REAL candidate from the actual minimum by a wide, hand-
checked margin. This is the non-degeneracy witness the dispatch requires: the construction is not
a tautology that holds of every candidate equally. -/
theorem witness_beats_naive :
    (inner ℝ (solutionOperator witnessData witnessB)
        (witnessData.Ginv (solutionOperator witnessData witnessB)) : ℝ) <
      inner ℝ witnessNaive (witnessData.Ginv witnessNaive) := by
  have hsol : (inner ℝ (solutionOperator witnessData witnessB)
      (witnessData.Ginv (solutionOperator witnessData witnessB)) : ℝ) = 30 := by
    rw [witness_solutionOperator_eq']
    show (inner ℝ ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![(3:ℝ), 2])
        (witnessGinv ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![(3:ℝ), 2])) : ℝ) = 30
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    unfold witnessGinv
    rw [matCLM_apply]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, EuclideanSpace.equiv]
    norm_num
  have hnaive : (inner ℝ witnessNaive (witnessData.Ginv witnessNaive) : ℝ) = 50 := by
    unfold witnessData witnessNaive witnessGinv
    rw [EuclideanSpace.inner_eq_star_dotProduct, matCLM_apply]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, EuclideanSpace.equiv]
    norm_num
  rw [hsol, hnaive]
  norm_num

#print axioms witness_beats_naive

/-- **The abstract `isMinimal` theorem, instantiated on the witness**, confirming the abstract
inequality is CONSISTENT with (and here strictly realized by) the hand-checked numbers above. -/
theorem witness_isMinimal_instance :
    (inner ℝ (solutionOperator witnessData witnessB)
        (witnessData.Ginv (solutionOperator witnessData witnessB)) : ℝ) ≤
      inner ℝ witnessNaive (witnessData.Ginv witnessNaive) :=
  isMinimal witnessData witnessB witnessNaive witnessNaive_satisfies_constraint

#print axioms witness_isMinimal_instance

/-! ## §5 — S82 garbage substitution: the structure's fields are NOT vacuously satisfiable

Substituting a structurally-valid-but-wrong candidate (`0`, `id`) for `Gstar` or `Q` on the SAME
`witnessGinv`/witness data BREAKS the defining hypotheses — proving the fields pin down something
real rather than being satisfiable by any candidate of the right type. -/

/-- **Mutation 1: `Gstar := 0`.** `Ginv_Gstar` (`∀x, Ginv(Gstar x)=x`) FAILS: at `x=(1,0)`,
`Ginv(0)=0≠(1,0)`. -/
theorem mutation_Gstar_zero_fails :
    ¬ (∀ x : EuclideanSpace ℝ (Fin 2),
        witnessGinv ((0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) x) = x) := by
  intro h
  have := h ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 0])
  simp only [_root_.zero_apply, map_zero] at this
  have hne : (0 : EuclideanSpace ℝ (Fin 2)) ≠ (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 0] := by
    intro heq
    have hc := congrArg (WithLp.ofLp) heq
    simp [EuclideanSpace.equiv] at hc
    have := congrFun hc 0
    simp at this
  exact hne this

#print axioms mutation_Gstar_zero_fails

/-- **Mutation 2: `Gstar := id`.** `Ginv_Gstar` FAILS: at `x=(1,0)`, `Ginv(id x) = Ginv(1,0) =
(2,0) ≠ (1,0)` — the ANISOTROPY of `Ginv` (`diag(2,3)`, not the identity) is exactly what breaks
the identity substitution, confirming the construction genuinely depends on `Ginv`'s actual value,
not merely on SOME two-sided-inverse relationship holding vacuously. -/
theorem mutation_Gstar_id_fails :
    ¬ (∀ x : EuclideanSpace ℝ (Fin 2),
        witnessGinv ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) x) = x) := by
  intro h
  have hwit := h ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 0])
  simp only [ContinuousLinearMap.id_apply] at hwit
  have hcomp := congrArg WithLp.ofLp hwit
  unfold witnessGinv at hcomp
  rw [matCLM_apply] at hcomp
  have h0 := congrFun hcomp 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, EuclideanSpace.equiv] at h0

#print axioms mutation_Gstar_id_fails

/-- **Mutation 3: `Q := 0`.** Then `Comp` (`= Q∘Gstar∘Qstar`) is forced to be the zero map, so NO
`CompInv` can satisfy `Comp_CompInv` (`∀x, Comp(CompInv x)=x`): at `x=1≠0` in `K`, `0≠1`. This shows
`Q`'s genuine (non-zero) definition is load-bearing — the composite-invertibility field cannot be
vacuously discharged by a degenerate `Q`. -/
theorem mutation_Q_zero_fails (CompInv' : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    ¬ (∀ x : EuclideanSpace ℝ (Fin 1),
        (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1))
          (witnessGstar (witnessQstar (CompInv' x))) = x) := by
  intro h
  have := h ((EuclideanSpace.equiv (Fin 1) ℝ).symm ![1])
  simp only [_root_.zero_apply] at this
  have hne : (0 : EuclideanSpace ℝ (Fin 1)) ≠ (EuclideanSpace.equiv (Fin 1) ℝ).symm ![1] := by
    intro heq
    have hc := congrArg WithLp.ofLp heq
    simp [EuclideanSpace.equiv] at hc
    have := congrFun hc 0
    simp at this
  exact hne this

#print axioms mutation_Q_zero_fails

end AdalyFormal.Balaban.VariationalProjectorH1
