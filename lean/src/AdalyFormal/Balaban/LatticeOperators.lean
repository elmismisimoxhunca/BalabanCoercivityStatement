/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.AdmissibleSubspace

set_option autoImplicit false

/-!
# The lattice coboundary operators `∂₀`, `∂₁` — the bottom of Balaban's `Δ_j` chain

**Task**: build `∂`, the lattice exterior derivative / coboundary, as a genuine
`ContinuousLinearMap` on a bond Hilbert space, and (secondary) `Q_j`, the coarse-graining
restriction map.

## Source pins (LAW-11: rendered images read directly, not the OCR text layer)

* CMP96 printed pp. 223-226 (`balaban_CMP96_1984_propagators_II.pdf`, offset 222,
  `constant_verified: true`): the paper's own Introduction states **"This paper is a continuation
  of [4] and we use all the notations introduced there without further explanation"** — `∂` itself
  is NOT (re-)defined in CMP96; it is imported wholesale from `[4]` = CMP95, "Propagators and
  Renormalization Transformations for Lattice Gauge Theories. I" (already ingested,
  `balaban_CMP95_1984_propagators_I`, offset 16, `constant_verified: true`).
* **CMP95 printed p.18, eq. (1.2)** (the actual defining equation, `pdf_page 2`, mathpix
  `corpus/mathpix/balaban_CMP95_1984_propagators_I/normalized/p18.md`, read directly): for a
  plaquette `p = ⟨x,y,z,w⟩` (corners in orientation order),
  `F(p) = (∂A)(p) = ε⁻¹A(∂p) = ε⁻¹(A(x,y)+A(y,z)+A(z,w)+A(w,x))`, and "the last equalities hold if
  we identify `p` with `⟨x,x+εe_μ,x+εe_μ+εe_ν,x+εe_ν⟩` for some `μ<ν`." This is the **bond →
  plaquette curl**, `∂₁` below. Antisymmetry is stated explicitly on the same page: "we assume
  that `A_b` is defined for bonds `b` with arbitrary orientation and that
  `A_{⟨x,x'⟩} = -A_{⟨x',x⟩}`" — the campaign's `Bond L` type (one real per FORWARD-oriented edge,
  `AdmissibleSubspace.Bond`) stores exactly the forward value, so a reversed traversal contributes
  its NEGATIVE, which is how the four-term sum below gets two `+` and two `-` terms.
* **CMP95 printed p.18, eq. (1.4)** (same page): gauge transformations act by
  `A_b^λ = A_b - (∂λ)(b)`, `(∂λ)(b) = ε⁻¹(λ(b_+)-λ(b_-))`, `b = ⟨b_-,b_+⟩` — the **site → bond
  gradient**, `∂₀` below. On the rescaled unit lattice (eq. 1.5, `ε → 1`) both `ε⁻¹` factors
  vanish; this file works entirely on that unit-lattice convention, matching
  `Target/ClayStatement.lean`'s existing combinatorics (no `η`/`ε` anywhere in that file either).
* **CMP96 printed p.226, eq. (2.19)**: `Δ_a = ∂*∂ + ∂R∂* + Q*aQ = Δ - ∂P∂* + Q*aQ`. **A genuine
  correction to `RG_LINEARIZATION.md`'s prior reading**, reached by tracing types through p.224's
  eq. (2.8)-(2.9) (`(∂*A)(x)`, `x` a SITE, so `∂*` there maps `Bonds → Sites`, i.e. `∂` there is
  `∂₀`) versus p.243's eq. (2.116)-(2.118) (`⟨H_jB,(Δ-∂P_j∂*)H_jB⟩ = ‖∂H_jB‖²` with `H_jB` a BOND
  configuration, forcing `Δ = ∂*∂` there to mean `∂₁*∂₁`, `∂₁ : Bonds → Plaquettes`). **Eq. (2.19)
  genuinely OVERLOADS both `∂`s in one formula**: the first `∂*∂` term (giving `Δ`, matching the
  `Δ` used at (2.116)-(2.118)) is `∂₁*∂₁`; the `∂R∂*` correction term (with `R` an
  orthogonal-projection built from the SITE Laplacian `N(Q')⊂L²(sites)`, p.225 eq. 2.10-2.11) uses
  `∂₀`/`∂₀*`. This file builds BOTH `∂₀` and `∂₁` precisely because eq. (2.19) needs both, even
  though only `∂₁` is required for the SIMPLEST, most load-bearing identity, `‖∂₁H_jB‖²`, that the
  mandate's primary target serves.
* **CMP95 printed p.19-20, eq. (1.18)** (`Q_k`, the coarse-graining restriction, CMP96's `Q_j`):
  `(Q_kA)_b = Σ_{x∈B^k(b_-)} η^{d+1} A([x,x(b)])`, where (same page) `x(b) = x+e_μ` when
  `b = ⟨y,y+e_μ⟩` — ~~i.e. `[x,x(b)]` is the SINGLE unit bond `(x,μ)` in the SAME direction as
  `b`,~~ **← SUPERSEDED, RETAINED STRUCK. THIS GLOSS IS FALSE AND IS THE ROOT OF THE `coarseRestrict`
  DEFECT (see the ⚠ CORRECTION on `coarseRestrict`, §8).** The source's very next clause reads
  "`x(b)` is a point in `B^k(b_+)`" — the OTHER block — and `b ⊂ T_1^{(k)} = ℤ^d ∩ T_η` is a bond of
  the UNIT lattice inside the FINE lattice `T_η`, so `e_μ` spans `η^{-1} = ell` fine bonds and
  `A([x,x(b)]) = Σ_{b'⊂[x,x(b)]} A_{b'}` is a CONTOUR SUM of `ell` terms (p.19, below (1.8):
  "`A(Γ) = Σ_{b⊂Γ} A_b` for arbitrary contour `Γ`", with "`x(c) = x + Le_μ`" spelled out at `k=1`).
  Image-verified by the denotation-repair lane at 300 dpi
  (`compute/mismatch_repairs/p19_eq18.png`, `p20_eq118.png`, `p20_prose.png`) and at 600 dpi
  (`compute/cmp98_defining/RENDER_HASHES.txt`). The sum ranges over the fine block sitting under the
  coarse bond's base site, and — the dropped part — over the `ell` fine bonds of the segment. This
  is the **secondary** target (§8 below), and §8's `coarseRestrict` implements only the single-bond
  version; the faithful operators are `LineIntegralAveraging.lineCoarseRestrict` and
  `QOne.qOnePathSum`, in downstream modules.

## What NEITHER of the above pages settle, and is NOT attempted here

`R`, `N(Q')`, `Δ_a`, `G`, `H_j`, `Δ_j` itself — all require the Lagrange-multiplier variational
construction of `R` (CMP96 pp. 225-226, eq. 2.10-2.17), resting on `Δ₀` positivity on `N(Q')`
sourced to CMP89 (2.26)/(2.27) (a page not yet read by any lane). Per the mandate's explicit
NO-GO, none of these are attempted; `∂₀`, `∂₁` are exactly the two objects both are BUILT FROM.

## What this module builds

1. `gradValue`/`gradLM`/`gradCLM` — `∂₀ : Sites → Bonds` (CMP95 eq. 1.4), as a value function, a
   `LinearMap`, and a `ContinuousLinearMap` between finite-dimensional `EuclideanSpace ℝ`-valued
   Hilbert spaces.
2. `curlValue`/`curlLM`/`curlCLM` — `∂₁ : Bonds → Plaquettes` (CMP95 eq. 1.2), same three layers,
   reusing `Target.ClayStatement.periodicPlaquetteHolonomy`'s EXACT combinatorial structure
   (base site + ordered direction pair, `periodicLatticeShift`) additively/linearized instead of
   multiplicatively — a genuine cross-check against already-audited code (LAW-19), not a fresh
   invention of the plaquette geometry.
3. **`curl_comp_grad_eq_zero`**: `∂₁ ∘ ∂₀ = 0`, the discrete "curl of a gradient vanishes" identity
   — proved, not assumed, from `Function.update_comm` (the two shifted directions in a plaquette
   commute because `μ ≠ ν`). This is literally why gauge transformations `A → A - ∂₀λ` leave the
   plaquette variable `F(p)` invariant (CMP95 p.18: "The covariant derivative `∂A`... invariant
   with respect to a group of gauge transformations") — the mandate's headline correctness fact,
   not a decorative side lemma.
4. **`siteLaplacianCLM`/`bondLaplacianCLM`** — `Δ₀ := ∂₀*∂₀`, `Δ₁ := ∂₁*∂₁` (eq. 2.19's two
   overloaded meanings, both actually built), plus **`bondLaplacian_eq_curl_normSq`**:
   `⟨A,Δ₁A⟩ = ‖∂₁A‖²` for every bond configuration `A` — the exact general identity specializing
   to CMP96 (2.117)-(2.118)'s `⟨B,Δ_jB⟩ = ‖∂H_jB‖²` once `H_j` (out of scope here) restricts it.
5. **D4 falsifiability (§6)**: a garbage "curl" that DROPS the two antisymmetric sign flips
   (`curlValueWrongSign`) — the exact silent, coherent-looking defect class §LEAN-D warns about —
   is proved to violate the exactness identity (nonzero on a named witness, where the TRUE curl is
   proved zero on the same input), showing the sign convention is load-bearing, not decorative.
6. **§8, secondary**: `coarseRestrict`/`coarseRestrictLM`/`coarseRestrictCLM` — the SINGLE-UNIT-BOND
   block sum with CMP95 eq. (1.18)'s `η^{d+1} = 1/ell⁴` COEFFICIENT, built on
   `AdmissibleSubspace.CoarseLattice`/`blockOf` (LAW-19 reuse). ~~CMP95 eq. (1.18)'s `Q_ell` … with
   the LITERAL `η^{d+1} = 1/ell⁴` normalization~~ **← the word "LITERAL", and the identification
   with (1.18)'s `Q_ell`, are WITHDRAWN (S75, in place; see the ⚠ CORRECTION on `coarseRestrict`
   itself in §8).** The COEFFICIENT is (1.18)'s; the OPERATOR is not: (1.18)'s `A([x,x(b)])` is a
   line integral over the `ell` fine bonds of the segment, and this operator sums ONE fine bond per
   block site. Kernel-checked consequence: on the constant field it returns `c/ell`, not `c`
   (`coarseRestrict_const_eq_div`, `witness_coarseRestrict_const_eq_half`,
   `witness_coarseRestrict_const_ne_one`). The faithful operators are
   `LineIntegralAveraging.lineCoarseRestrict` and `QOne.qOnePathSum` (downstream modules). Read the
   rest of this item as being about the COEFFICIENT only. **R2 CORRECTION (S75, in place):** ~~with
   the discrete
   arithmetic-mean normalization `1/ell³` standing in for the paper's `η^{d+1}` (disclosed
   simplification — the physical-lattice-spacing normalization is dropped because this whole tree
   works on the unit combinatorial lattice, matching `Target/ClayStatement.lean`)~~ — an
   independent source audit (`compute/lattice_operator_audit/OPERATOR_AUDIT.md`) found this framing
   wrong: CMP95 p.20 eq. (1.18) itself reads `η^{d+1}`, one power of `ell` MORE than the plain
   arithmetic mean `η^d = 1/ell³`, and no page anywhere sets that extra factor to `1` (unlike `∂`'s
   legitimate `ε→1` unit-lattice drop, §1.3). Fixed to `1/ell⁴` — the literal (1.18) COEFFICIENT,
   which is as far as that repair went (it did not add the line integral); see
   `LATTICE_OPERATORS_R2.md` for the full re-derivation and a D4 control (§9 below) proving the two
   normalizations give numerically DIFFERENT answers on a concrete witness (not merely a relabeled
   constant).

## What this module does NOT build (named, not silently dropped)

* `R`, `N(Q')`, `Δ_a`, `G`, `H_j`, `Δ_j` — explicit NO-GO per the mandate.
* Wiring any of this into `Balaban.Coercivity`'s `CoercivityHypothesis` — that file is NO-GO
  (live-edited by a concurrent lane).
* A THIRD independent `EuclideanSpace ℝ (Bond L)`-style Hilbert-space promotion is built here
  (`SiteSpace`/`BondSpace`/`PlaquetteSpace`) because `RGLinearization.lean`'s `BondHilbert` and
  `Coercivity.lean`'s `Anchoring.AnchoredBondSpace` are BOTH NO-GO (live-edited) and cannot safely
  be imported (a concurrent edit could silently change their meaning mid-build). **This is now the
  THIRD reproduction of the identical trivial promotion** (`RG_LINEARIZATION.md` §6 already flagged
  the first duplication) — a dedup pass consolidating all three into one shared module is a real,
  cheap, and now THRICE-motivated follow-up, disclosed here rather than performed (write-scope
  isolation forces the duplication, it does not excuse leaving it unnamed).
-/

namespace AdalyFormal.Balaban.LatticeOperators

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace

variable {L : PeriodicLatticeExtent}

/-! ## §1. `∂₀` — the site → bond gradient (CMP95 p.18, eq. 1.4) -/

/-- **`(∂₀λ)(b) = λ(b_+) - λ(b_-)`, CMP95 eq. (1.4), unit-lattice (`ε=1`) convention.** `b_- = b.1`
(the base site), `b_+ = periodicLatticeShift b.1 b.2` (the forward endpoint), matching
`AdmissibleSubspace.Bond`'s own convention (a bond IS a base site plus a forward direction). -/
def gradValue (lam : PeriodicLatticeSite L → ℝ) (b : Bond L) : ℝ :=
  lam (periodicLatticeShift b.1 b.2) - lam b.1

theorem gradValue_add (lam1 lam2 : PeriodicLatticeSite L → ℝ) (b : Bond L) :
    gradValue (lam1 + lam2) b = gradValue lam1 b + gradValue lam2 b := by
  simp only [gradValue, Pi.add_apply]; ring

theorem gradValue_smul (c : ℝ) (lam : PeriodicLatticeSite L → ℝ) (b : Bond L) :
    gradValue (c • lam) b = c * gradValue lam b := by
  simp only [gradValue, Pi.smul_apply, smul_eq_mul]; ring

/-- `∂₀` as a genuine `LinearMap`. -/
def gradLM (L : PeriodicLatticeExtent) : (PeriodicLatticeSite L → ℝ) →ₗ[ℝ] (Bond L → ℝ) where
  toFun := gradValue
  map_add' lam1 lam2 := funext fun b => gradValue_add lam1 lam2 b
  map_smul' c lam := funext fun b => gradValue_smul c lam b

/-! ## §2. `∂₁` — the bond → plaquette curl (CMP95 p.18, eq. 1.2) -/

/-- **`(∂₁A)(p) = A(x,μ) + A(x+e_μ,ν) - A(x+e_ν,μ) - A(x,ν)`, CMP95 eq. (1.2), unit-lattice
convention.** For `p = (x,⟨μ,ν⟩)` identified with corners `⟨x,x+e_μ,x+e_μ+e_ν,x+e_ν⟩` (`μ<ν` per
`PeriodicPlaquetteDirections`), `F(p) = A(x,x+e_μ)+A(x+e_μ,x+e_μ+e_ν)+A(x+e_μ+e_ν,x+e_ν)+A(x+e_ν,x)`
per the page's own formula; the last two terms are traversed BACKWARDS relative to `Bond`'s stored
forward orientation, so antisymmetry (`A_{⟨x,x'⟩}=-A_{⟨x',x⟩}`, same page) turns them negative.
Reuses `periodicPlaquetteHolonomy`'s EXACT base/direction/shift structure (LAW-19), additively
instead of multiplicatively — the discrete linearization of the same Wilson plaquette word. -/
def curlValue (A : Bond L → ℝ) (p : PeriodicLatticePlaquette L) : ℝ :=
  A (p.1, p.2.1.1) + A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) -
    A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.2)

theorem curlValue_add (A1 A2 : Bond L → ℝ) (p : PeriodicLatticePlaquette L) :
    curlValue (A1 + A2) p = curlValue A1 p + curlValue A2 p := by
  simp only [curlValue, Pi.add_apply]; ring

theorem curlValue_smul (c : ℝ) (A : Bond L → ℝ) (p : PeriodicLatticePlaquette L) :
    curlValue (c • A) p = c * curlValue A p := by
  simp only [curlValue, Pi.smul_apply, smul_eq_mul]; ring

/-- `∂₁` as a genuine `LinearMap`. -/
def curlLM (L : PeriodicLatticeExtent) : (Bond L → ℝ) →ₗ[ℝ] (PeriodicLatticePlaquette L → ℝ) where
  toFun := curlValue
  map_add' A1 A2 := funext fun p => curlValue_add A1 A2 p
  map_smul' c A := funext fun p => curlValue_smul c A p

#print axioms gradLM
#print axioms curlLM

/-! ## §3. Exactness: `∂₁ ∘ ∂₀ = 0` — the discrete "curl of a gradient vanishes" identity -/

/-- Shifts in two DIFFERENT coordinate directions commute. The one nontrivial combinatorial fact
underneath `curl_comp_grad_eq_zero`: it genuinely uses `μ ≠ ν` (via `Function.update_comm`), it is
not a tautology. -/
theorem periodicLatticeShift_comm (x : PeriodicLatticeSite L) {μ ν : Fin 3} (h : μ ≠ ν) :
    periodicLatticeShift (periodicLatticeShift x μ) ν =
      periodicLatticeShift (periodicLatticeShift x ν) μ := by
  simp only [periodicLatticeShift]
  rw [Function.update_of_ne h.symm, Function.update_of_ne h]
  exact Function.update_comm h _ _ x

/-- **The general curl-of-gradient identity, worked out symbolically.** Every term except the two
"diagonal" evaluations cancels; what remains is exactly the commutator obstruction
`λ(shift_μ(shift_ν x)) - λ(shift_ν(shift_μ x))`, which `periodicLatticeShift_comm` kills because a
plaquette's two directions satisfy `μ < ν` hence `μ ≠ ν`. -/
theorem curlValue_gradValue (lam : PeriodicLatticeSite L → ℝ) (p : PeriodicLatticePlaquette L) :
    curlValue (gradValue lam) p = 0 := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  simp only [curlValue, gradValue]
  rw [periodicLatticeShift_comm p.1 hne]
  ring

/-- **`∂₁ ∘ ∂₀ = 0`, as an equation of `LinearMap`s.** The mandate's headline correctness fact:
gauge transformations `A ↦ A - ∂₀λ` leave the plaquette curl invariant precisely because this
composite vanishes (CMP95 p.18's stated gauge-invariance of `F(p)`, now a proved identity rather
than an assertion). -/
theorem curl_comp_grad_eq_zero (L : PeriodicLatticeExtent) :
    (curlLM L).comp (gradLM L) = 0 := by
  apply LinearMap.ext
  intro lam
  funext p
  exact curlValue_gradValue lam p

#print axioms periodicLatticeShift_comm
#print axioms curlValue_gradValue
#print axioms curl_comp_grad_eq_zero

/-! ## §4. Hilbert-space promotion: `SiteSpace`, `BondSpace`, `PlaquetteSpace` -/

/-- `Sites`, as a finite-dimensional real Hilbert space (`ℓ²`). A THIRD, disclosed reproduction of
the `EuclideanSpace ℝ`-promotion pattern already built twice elsewhere in this tree (module
docstring, "What this module does NOT build"). -/
abbrev SiteSpace (L : PeriodicLatticeExtent) := EuclideanSpace ℝ (PeriodicLatticeSite L)

/-- `Bonds`, as a finite-dimensional real Hilbert space. -/
abbrev BondSpace (L : PeriodicLatticeExtent) := EuclideanSpace ℝ (Bond L)

/-- `Plaquettes`, as a finite-dimensional real Hilbert space. -/
abbrev PlaquetteSpace (L : PeriodicLatticeExtent) := EuclideanSpace ℝ (PeriodicLatticePlaquette L)

/-- The identity-on-underlying-functions equivalence `SiteSpace L ≃ (Sites → ℝ)`. -/
noncomputable def siteEquiv (L : PeriodicLatticeExtent) :
    SiteSpace L ≃ₗ[ℝ] (PeriodicLatticeSite L → ℝ) :=
  (EuclideanSpace.equiv (PeriodicLatticeSite L) ℝ).toLinearEquiv

/-- The identity-on-underlying-functions equivalence `BondSpace L ≃ (Bond L → ℝ)`. -/
noncomputable def bondEquiv (L : PeriodicLatticeExtent) : BondSpace L ≃ₗ[ℝ] (Bond L → ℝ) :=
  (EuclideanSpace.equiv (Bond L) ℝ).toLinearEquiv

/-- The identity-on-underlying-functions equivalence
`PlaquetteSpace L ≃ (PeriodicLatticePlaquette L → ℝ)`. -/
noncomputable def plaquetteEquiv (L : PeriodicLatticeExtent) :
    PlaquetteSpace L ≃ₗ[ℝ] (PeriodicLatticePlaquette L → ℝ) :=
  (EuclideanSpace.equiv (PeriodicLatticePlaquette L) ℝ).toLinearEquiv

/-- **`∂₀ : SiteSpace L →ₗ[ℝ] BondSpace L`**, transported across `siteEquiv`/`bondEquiv`. -/
noncomputable def gradLMH (L : PeriodicLatticeExtent) : SiteSpace L →ₗ[ℝ] BondSpace L :=
  (bondEquiv L).symm.toLinearMap.comp ((gradLM L).comp (siteEquiv L).toLinearMap)

/-- **`∂₁ : BondSpace L →ₗ[ℝ] PlaquetteSpace L`**, transported across `bondEquiv`/
`plaquetteEquiv`. -/
noncomputable def curlLMH (L : PeriodicLatticeExtent) : BondSpace L →ₗ[ℝ] PlaquetteSpace L :=
  (plaquetteEquiv L).symm.toLinearMap.comp ((curlLM L).comp (bondEquiv L).toLinearMap)

/-- **`∂₀`, as a genuine `ContinuousLinearMap` on the bond/site Hilbert spaces** — the mandate's
primary deliverable's sibling. Finite-dimensional domain makes every linear map continuous
(`LinearMap.toContinuousLinearMap`); no `axiom`, no `native_decide`. -/
noncomputable def gradCLM (L : PeriodicLatticeExtent) : SiteSpace L →L[ℝ] BondSpace L :=
  LinearMap.toContinuousLinearMap (gradLMH L)

/-- **`∂₁`, as a genuine `ContinuousLinearMap` on the bond/plaquette Hilbert spaces** — the
mandate's PRIMARY deliverable. -/
noncomputable def curlCLM (L : PeriodicLatticeExtent) : BondSpace L →L[ℝ] PlaquetteSpace L :=
  LinearMap.toContinuousLinearMap (curlLMH L)

theorem gradCLM_apply (L : PeriodicLatticeExtent) (lam : SiteSpace L) :
    bondEquiv L (gradCLM L lam) = gradValue (siteEquiv L lam) := rfl

theorem curlCLM_apply (L : PeriodicLatticeExtent) (A : BondSpace L) :
    plaquetteEquiv L (curlCLM L A) = curlValue (bondEquiv L A) := rfl

/-- **`∂₁ ∘ ∂₀ = 0` transported to the `ContinuousLinearMap` layer** — the same fact §3 proved,
now at the level the mandate actually asked for. -/
theorem curlCLM_comp_gradCLM_eq_zero (L : PeriodicLatticeExtent) :
    (curlCLM L).comp (gradCLM L) = 0 := by
  apply ContinuousLinearMap.ext
  intro lam
  simp only [ContinuousLinearMap.comp_apply, zero_apply]
  apply (plaquetteEquiv L).injective
  rw [curlCLM_apply, gradCLM_apply, map_zero]
  funext p
  exact curlValue_gradValue (siteEquiv L lam) p

#print axioms gradCLM_apply
#print axioms curlCLM_apply
#print axioms curlCLM_comp_gradCLM_eq_zero

/-! ## §5. Adjoints: `Δ₀ := ∂₀*∂₀`, `Δ₁ := ∂₁*∂₁` (eq. 2.19's two overloaded meanings, both
built) -/

/-- **`Δ₀ := ∂₀*∂₀`, the SITE Laplacian** — the `Δ` used at CMP96 p.224-225 (eq. 2.8-2.11, `(Δλ)(x)`
site-valued) and the `∂R∂*` correction term of eq. (2.19) (which uses `∂₀`/`∂₀*`, not the
bond-space `∂₁`, per this file's source-reading correction above). -/
noncomputable def siteLaplacianCLM (L : PeriodicLatticeExtent) : SiteSpace L →L[ℝ] SiteSpace L :=
  (gradCLM L).adjoint.comp (gradCLM L)

/-- **`Δ₁ := ∂₁*∂₁`, the BOND (covariant) Laplacian** — the `Δ` that CMP96 p.243 eq. (2.116)-(2.118)
actually needs (`⟨H_jB,(Δ-∂P_j∂*)H_jB⟩ = ‖∂H_jB‖²`, `H_jB` bond-valued forces this reading). -/
noncomputable def bondLaplacianCLM (L : PeriodicLatticeExtent) : BondSpace L →L[ℝ] BondSpace L :=
  (curlCLM L).adjoint.comp (curlCLM L)

/-- **The general identity behind CMP96 (2.117)-(2.118)**: `⟨A,Δ₁A⟩ = ‖∂₁A‖²` for EVERY bond
configuration `A`, not merely the `H_jB` restriction the source states it for — the general fact
`⟪x,(T†∘T)x⟫ = ‖Tx‖²` specialized to `T = ∂₁`. `H_j`/`Δ_j` themselves are out of scope; this is the
exact quadratic-form identity they would restrict, proved here in full generality. -/
theorem bondLaplacian_eq_curl_normSq (L : PeriodicLatticeExtent) (A : BondSpace L) :
    (inner ℝ A (bondLaplacianCLM L A) : ℝ) = ‖curlCLM L A‖ ^ 2 := by
  unfold bondLaplacianCLM
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  simp

#print axioms bondLaplacian_eq_curl_normSq

/-! ## §6. D4 FALSIFIABILITY — a garbage curl that drops the antisymmetric signs, and fails -/

/-- **D4 GARBAGE**: the same four terms as `curlValue`, but WITHOUT the two antisymmetric sign
flips — exactly the "silent, coherent-looking" wrong transcription §LEAN-D warns about (forgetting
`A_{⟨x,x'⟩}=-A_{⟨x',x⟩}` and treating all four edges as positively oriented). This is NOT shipped
as the campaign's `∂₁` — it exists solely to be refuted below. -/
def curlValueWrongSign (A : Bond L → ℝ) (p : PeriodicLatticePlaquette L) : ℝ :=
  A (p.1, p.2.1.1) + A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) +
    A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) + A (p.1, p.2.1.2)

/-- **The wrong formula's general value on a gradient**: `2·(λ(shift_μ(shift_ν x)) - λ(x))` — the
missing sign flips leave a residue instead of cancelling to zero (contrast `curlValue_gradValue`,
where the analogous computation is IDENTICALLY zero). -/
theorem curlValueWrongSign_gradValue (lam : PeriodicLatticeSite L → ℝ)
    (p : PeriodicLatticePlaquette L) :
    curlValueWrongSign (gradValue lam) p =
      2 * (lam (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2) - lam p.1) := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  simp only [curlValueWrongSign, gradValue]
  rw [← periodicLatticeShift_comm p.1 hne]
  ring

/-- **Concrete witness lattice for the D4 test**: extent `3` (`Fin 4` per coordinate), directions
`μ=0, ν=1` (a valid `μ<ν` pair), base site `witnessY` (reused from `AdmissibleSubspace`, LAW-19). -/
def d4Plaquette : PeriodicLatticePlaquette AdmissibleSubspace.witnessL :=
  (AdmissibleSubspace.witnessY, ⟨(0, 1), by decide⟩)

/-- **A concrete `λ` avoiding equality-deciding entirely**: the real-valued coordinate-0 reading of
a site, `λ(z) := (z 0).val`. Purely `Fin`-arithmetic, no `if`/`Decidable` branching, so every step
below reduces by direct computation rather than case-splitting on site equality. -/
noncomputable def d4Lam : PeriodicLatticeSite AdmissibleSubspace.witnessL → ℝ :=
  fun z => ((z 0 : Fin 4).val : ℝ)

/-- The double-shift in `d4Plaquette`'s two directions moves coordinate `0` from `0` to `1` (a
single-step `Fin 4` increment, no wraparound), computed directly. -/
theorem d4_shift_coord0 :
    (periodicLatticeShift (periodicLatticeShift AdmissibleSubspace.witnessY 0) 1) 0 =
      (1 : Fin 4) := by
  decide

/-- **The D4 acceptance test**: on this concrete witness, the WRONG curl of a gradient is nonzero
(`2·(1-0) = 2 ≠ 0`)... -/
theorem d4_wrongSign_nonzero :
    curlValueWrongSign (gradValue d4Lam) d4Plaquette ≠ 0 := by
  rw [curlValueWrongSign_gradValue]
  change (2:ℝ) * (d4Lam
      (periodicLatticeShift (periodicLatticeShift AdmissibleSubspace.witnessY 0) 1)
      - d4Lam AdmissibleSubspace.witnessY) ≠ 0
  simp only [d4Lam, d4_shift_coord0, AdmissibleSubspace.witnessY]
  norm_num

/-- ... **while the TRUE curl of the SAME gradient, on the SAME plaquette, is exactly `0`** —
`curlValue_gradValue` specialized, giving the direct contrast the D4 handle requires. -/
theorem d4_trueSign_zero :
    curlValue (gradValue d4Lam) d4Plaquette = 0 :=
  curlValue_gradValue d4Lam d4Plaquette

#print axioms d4_shift_coord0
#print axioms d4_wrongSign_nonzero
#print axioms d4_trueSign_zero

/-! ## §7. `L7` witness: `∂₁` is genuinely non-degenerate on the shared witness lattice -/

/-- **A concrete nonzero bond configuration, again avoiding equality-deciding**: the coordinate-`0`
reading of the bond's BASE SITE only (ignoring direction entirely). -/
noncomputable def witnessBondConfig : Bond AdmissibleSubspace.witnessL → ℝ :=
  fun b => ((b.1 0 : Fin 4).val : ℝ)

/-- **`∂₁` is not the zero map**: on this configuration, three of the four boundary terms of
`curlValue` cancel or reduce to a shared base value, leaving exactly `1` (the single `+1` picked up
by the `μ`-direction shift's effect on coordinate `0`). -/
theorem witness_curlValue_ne_zero : curlValue witnessBondConfig d4Plaquette = 1 := by
  simp only [curlValue, d4Plaquette, witnessBondConfig]
  show ((AdmissibleSubspace.witnessY 0 : Fin 4).val : ℝ)
      + ((periodicLatticeShift AdmissibleSubspace.witnessY 0) 0 : Fin 4).val
      - ((periodicLatticeShift AdmissibleSubspace.witnessY 1) 0 : Fin 4).val
      - ((AdmissibleSubspace.witnessY 0 : Fin 4).val : ℝ) = 1
  have h1 : (periodicLatticeShift AdmissibleSubspace.witnessY 0) 0 = (1 : Fin 4) := by decide
  have h2 : (periodicLatticeShift AdmissibleSubspace.witnessY 1) 0 =
      AdmissibleSubspace.witnessY 0 := by decide
  rw [h1, h2]
  simp [AdmissibleSubspace.witnessY]

#print axioms witness_curlValue_ne_zero

/-! ## §8. SECONDARY: `Q_ell`, the coarse-graining restriction (CMP95 eq. 1.18) -/

/-- **Coarse bonds**: bonds based at a `CoarseLattice`-member site (CMP95 eq. 1.18's
`b ⊂ T_1^(k)`). Built on `AdmissibleSubspace.CoarseLattice`, not a fresh index type (LAW-19). -/
abbrev CoarseBond (L : PeriodicLatticeExtent) (ell : ℕ) :=
  {y : PeriodicLatticeSite L // y ∈ AdmissibleSubspace.CoarseLattice L ell} × Fin 3

instance instFintypeCoarseSite (L : PeriodicLatticeExtent) (ell : ℕ) :
    Fintype {y : PeriodicLatticeSite L // y ∈ AdmissibleSubspace.CoarseLattice L ell} :=
  Subtype.fintype _

/-- **`(Q_ell A)(b) := (1/ell⁴) Σ_{x ∈ blockOf b.1 ell} A(x, b.2)` — the SINGLE-UNIT-BOND operator.
This is NOT CMP95 (1.18); (1.18)'s line integral is DROPPED here.**

## ⚠ CORRECTION (denotation-repair lane): this docstring previously called the body "LITERAL
## normalization" of CMP95 (1.18). THE WORD "LITERAL" WAS WRONG AND IS WITHDRAWN.

**What the body actually computes.** For a coarse bond `b = (y, μ)` it sums `A (x, b.2)` — the
ONE fine bond `(x, μ)` based at each block site `x ∈ blockOf y ell` — and multiplies by `1/ell⁴`.
No contour, no line integral, `ell³` summands.

**What CMP95 (1.18) says**, verbatim, image-verified by this lane at 300 dpi
(`compute/mismatch_repairs/p20_eq118.png`, `p20_prose.png`, from
`compute/balaban_su2_papers/balaban_CMP95_1984_propagators_I.pdf` pdf-page 4 = printed p.20, offset
16 per `corpus/tools/page_offsets.json`; independently at 600 dpi,
`compute/cmp98_defining/RENDER_HASHES.txt`):

  `(Q_kA)_b = Σ_{x∈B^k(b_-)} η^{d+1} A([x, x(b)]),  b ⊂ T_1^{(k)} = ℤ^d ∩ T_η,  η = L^{-k},`

and, in the prose IMMEDIATELY BELOW the display (this is the clause that settles it):

  "and `x(b)` is a point in `B^k(b_+)` obtained from `x` by translation by `b`. If
   `b = ⟨y, y+e_μ⟩`, then `x(b) = x + e_μ`."

`x ∈ B^k(b_-)` while `x(b) ∈ B^k(b_+)` — the two ends of `[x,x(b)]` lie in DIFFERENT blocks, so
`[x,x(b)]` cannot be a single fine bond: `b` is a bond of the UNIT lattice `T_1^{(k)}` sitting
inside the FINE lattice `T_η`, so `e_μ` spans `η^{-1} = ell` fine bonds. And `A(Γ)` is a contour
SUM: CMP95 printed p.19, below (1.8) (`compute/mismatch_repairs/p19_eq18.png`), "where
`A(Γ) = Σ_{b⊂Γ} A_b` for arbitrary contour `Γ`, and `x(c)` denotes a point in the block `B(c_+)`
obtained by translation of `x` by the bond `c`, so if `c = ⟨y, y+Le_μ⟩` then `x(c) = x + Le_μ`."
So (1.18) has `ell³ · ell = ell⁴` summands against its `η^{d+1} = 1/ell⁴`; the body below has
`ell³`.

**Arithmetic consequence, PROVED below, not asserted**: on a TILING extent (`ell ∣ L μ + 1` for
every `μ` — without it `blockOf` can silently truncate below `ell³` sites and the value is
something else again), on the constant field `A ≡ c` this operator returns `c/ell`, not `c`
(`coarseRestrict_const_eq_div`), and `c/ell ≠ c` whenever additionally `ell > 1` and `c ≠ 0`
(`coarseRestrict_const_ne_self`); at the tree's own witness the value is `1/2 ≠ 1`
(`witness_coarseRestrict_const_eq_half`, `witness_coarseRestrict_const_ne_one`). A faithful `Q_k`
is a TRUE AVERAGE and returns `c`.

**The faithful alternatives, which exist and are built** (do not re-derive them, LAW-19):
* `AdalyFormal.Balaban.LineIntegralAveraging.lineCoarseRestrict` — CMP95 (1.11)/(1.18) WITH the
  line integral (`lineIntegralValue`), returning `c` on the constant field
  (`lineCoarseRestrict_const_witness`, against `coarseRestrict_const_witness` in the same file).
* `AdalyFormal.Balaban.QOne.qOnePathSum` — the same repair in the `QOne` lane.
* `AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov` — the covariant version.
They AGREE with this operator exactly at `ell = 1`
(`LineIntegralAveraging.lineCoarseRestrict_one_eq_coarseRestrict`), which is why `ell = 1` results
built over `coarseRestrict` are unaffected.

**NOT CHANGED.** The definition below is left exactly as it was: several lanes consume it
(`HjMinimizer.lean`, `CoarseCurl.lean`, `U1Anchor.lean`, `LagrangeMultiplier.lean`, …), and
`U1AnchorRefutation.lean` already proves what the drop costs those statements. This is a denotation
correction to the DOCSTRING plus five new kernel-checked facts (`coarseRestrict_const_eq_div`,
`coarseRestrict_const_ne_self`, `witnessEll_dvd_extent`, `witness_coarseRestrict_const_eq_half`,
`witness_coarseRestrict_const_ne_one`); the operator itself is untouched.

**Retained for the record (the `1/ell⁴` coefficient's own history), STILL CORRECT AS FAR AS IT
GOES:** R2 REPAIR — see `LATTICE_OPERATORS_R2.md`; the pre-repair code used `1/ell³`, one power of
`ell` too few relative to (1.18)'s `η^{d+1}`. That repair fixed the COEFFICIENT and did not add the
line integral, which is why the operator now under-counts by exactly the factor `ell` (the number
of fine bonds in `[x,x(b)]`) instead of over-counting by nothing.

**Convention, stated precisely, per the mandate:** `η = L^{-k}` is Bałaban's own lattice-spacing
parameter at coarse-graining level `k` (CMP95 p.20 eq. 1.18's own `η = L^{-k}`); `ell` in this file
is the BLOCK SIDE LENGTH at that level, i.e. `ell = L^k = η⁻¹` (so `blockOf y ell`, CMP95's
`B^k(y)`, has exactly `ell^d` sites, `d = 3` the spatial dimension of this tree's lattice, PROVED as
`AdmissibleSubspace.card_blockOf`). Eq. (1.18) itself (CMP95 printed p.20, image-confirmed,
`sha256 e79ec13eb77f458dedafb12dcf78895daad789c4f8540efea2eb1e4a454bfcd8`):
`(Q_kA)_b = Σ_{x∈B^k(b_-)} η^{d+1} A([x,x(b)])`. In `ell`-terms: `η^{d+1} = (1/ell)^{d+1} = 1/ell⁴`
for `d=3` — ONE POWER OF `1/ell` MORE than the plain arithmetic mean `η^d = 1/ell³` a bare average
over the block would carry.

**Why the extra power is real, not an artifact of the unit-lattice rescaling that legitimately
drops `∂`'s `ε⁻¹` (§1.3 above):** the SAME source page distinguishes TWO coarse-graining maps
sharing the identical block geometry — `Q_k` (eq. 1.18, acting on the BOND field `A`, coefficient
`η^{d+1}`) and `Q_k'` (eq. 1.20, acting on the SITE-valued gauge parameter `λ`, coefficient `η^d`,
the plain average). No page anywhere sets `Q_k`'s extra `η` to `1`; it is intrinsic to how a
lattice CONNECTION (`A`) coarse-grains, as opposed to a scalar (`λ`) — the pre-repair code had
silently implemented `Q_k'`'s coefficient on `Q_k`'s object. The averaging CONTENT (which sites get
summed) is unchanged from the pre-repair code; only the power of `ell` in the coefficient is
corrected. **← and THAT unchanged averaging content is precisely the defect the ⚠ CORRECTION at the
top of this docstring records: with `ell³` single-bond summands against a `1/ell⁴` coefficient this
operator is `1/ell` times a true average (`coarseRestrict_const_eq_div`). The R2 repair was
necessary and is not undone; it was not sufficient.** -/
noncomputable def coarseRestrict {L : PeriodicLatticeExtent} (ell : ℕ)
    (A : Bond L → ℝ) (b : CoarseBond L ell) : ℝ :=
  (1 / (ell : ℝ) ^ 4) * ∑ x ∈ AdmissibleSubspace.blockOf b.1.1 ell, A (x, b.2)

/-- **THE DROPPED LINE INTEGRAL, MADE KERNEL-VISIBLE: on the constant field `A ≡ c`,
`coarseRestrict` returns `c/ell`, not `c`.**

A faithful CMP95 (1.18) `Q_k` is a true average — `η^{-d}` block sites × `η^{-1}` fine bonds per
segment `= η^{-(d+1)}` summands against the `η^{d+1}` coefficient — so it returns `c`. This
operator has only the `ell³ = η^{-d}` block sites, so it returns `c·ell³/ell⁴ = c/ell`. The
missing factor is exactly the number of fine bonds in `[x,x(b)]`.

The hypothesis `hdvd` is the block-tiling condition (`AdmissibleSubspace.card_blockOf_of_coarse`):
without it `blockOf` can SILENTLY TRUNCATE to fewer than `ell³` sites on an incompatible periodic
extent, and the statement would be false. `hdvd` also forces `ell ≠ 0`.

Contrast (downstream, already built): `LineIntegralAveraging.lineCoarseRestrict_const_witness`
returns the constant, while `LineIntegralAveraging.coarseRestrict_const_witness` reproduces this
statement's `c/ell` at the single point `ell = 2`, `c = 1`. This lemma is the GENERAL form, stated
in the operator's own module so the discrepancy is visible where the operator is defined. -/
theorem coarseRestrict_const_eq_div {L : PeriodicLatticeExtent} {ell : ℕ}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (c : ℝ) (b : CoarseBond L ell) :
    coarseRestrict ell (fun _ => c) b = c / (ell : ℝ) := by
  have hell : ell ≠ 0 := by
    intro h
    have hd := hdvd 0
    rw [h] at hd
    have := Nat.eq_zero_of_zero_dvd hd
    omega
  have hcard : (AdmissibleSubspace.blockOf b.1.1 ell).card = ell ^ 3 :=
    AdmissibleSubspace.card_blockOf_of_coarse hdvd b.1.2
  have hne : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell
  simp only [coarseRestrict, Finset.sum_const, hcard, nsmul_eq_mul]
  push_cast
  field_simp

/-- **`c/ell ≠ c` for `ell > 1`, `c ≠ 0`** — the constant-field discrepancy of
`coarseRestrict_const_eq_div` is a genuine failure of the averaging property, not a vacuous
restatement. At `ell = 1` (where the faithful and single-bond operators provably agree,
`LineIntegralAveraging.lineCoarseRestrict_one_eq_coarseRestrict`) there is no discrepancy, and this
lemma correctly does not apply. -/
theorem coarseRestrict_const_ne_self {L : PeriodicLatticeExtent} {ell : ℕ}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hell : 1 < ell) {c : ℝ} (hc : c ≠ 0)
    (b : CoarseBond L ell) :
    coarseRestrict ell (fun _ => c) b ≠ c := by
  rw [coarseRestrict_const_eq_div hdvd]
  intro h
  have hne : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_eq_iff hne] at h
  have h1 : c * (1 : ℝ) = c * (ell : ℝ) := by rw [mul_one]; exact h
  have h2 : (1 : ℝ) = (ell : ℝ) := mul_left_cancel₀ hc h1
  have h3 : ((1 : ℕ) : ℝ) = ((ell : ℕ) : ℝ) := by exact_mod_cast h2
  have h4 : (1 : ℕ) = ell := Nat.cast_injective h3
  omega

/-- The witness lattice tiles: `witnessEll = 2` divides `witnessL μ + 1 = 4`. Identical in content
to `CoarseCurl.witnessHdvd`, which CANNOT be imported here (`CoarseCurl` is DOWNSTREAM of this
module); stated locally only for that reason (LAW-19 disclosure, not a silent rebuild). -/
theorem witnessEll_dvd_extent : ∀ μ : Fin 3,
    AdmissibleSubspace.witnessEll ∣ (AdmissibleSubspace.witnessL μ + 1) := by decide

/-- **NON-VACUITY of `coarseRestrict_const_eq_div`**: its hypotheses ARE satisfiable, and on the
tree's own witness (`witnessL`, `witnessEll = 2`) the constant field `1` averages to `1/2`. A
faithful `Q_k` would return `1`. -/
theorem witness_coarseRestrict_const_eq_half :
    coarseRestrict AdmissibleSubspace.witnessEll (fun _ => (1 : ℝ))
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) = 1 / 2 := by
  rw [coarseRestrict_const_eq_div witnessEll_dvd_extent]
  norm_num [AdmissibleSubspace.witnessEll]

/-- **THE AVERAGING PROPERTY FAILS, kernel-checked at the witness** — `coarseRestrict` of the
constant field `1` is NOT `1`. This is the mutation test for the two lemmas above: the mutated
statement "`coarseRestrict` returns the constant" is REFUTED, not merely unproved. -/
theorem witness_coarseRestrict_const_ne_one :
    coarseRestrict AdmissibleSubspace.witnessEll (fun _ => (1 : ℝ))
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) ≠ 1 :=
  coarseRestrict_const_ne_self witnessEll_dvd_extent (by decide) one_ne_zero _

#print axioms coarseRestrict_const_eq_div
#print axioms coarseRestrict_const_ne_self
#print axioms witnessEll_dvd_extent
#print axioms witness_coarseRestrict_const_eq_half
#print axioms witness_coarseRestrict_const_ne_one

theorem coarseRestrict_add {L : PeriodicLatticeExtent} (ell : ℕ) (A1 A2 : Bond L → ℝ)
    (b : CoarseBond L ell) :
    coarseRestrict ell (A1 + A2) b = coarseRestrict ell A1 b + coarseRestrict ell A2 b := by
  simp only [coarseRestrict, Pi.add_apply]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]

theorem coarseRestrict_smul {L : PeriodicLatticeExtent} (ell : ℕ) (c : ℝ) (A : Bond L → ℝ)
    (b : CoarseBond L ell) :
    coarseRestrict ell (c • A) b = c * coarseRestrict ell A b := by
  simp only [coarseRestrict, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- `Q_ell` as a genuine `LinearMap`. -/
noncomputable def coarseRestrictLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    (Bond L → ℝ) →ₗ[ℝ] (CoarseBond L ell → ℝ) where
  toFun A := coarseRestrict ell A
  map_add' A1 A2 := funext fun b => coarseRestrict_add ell A1 A2 b
  map_smul' c A := funext fun b => coarseRestrict_smul ell c A b

/-- `CoarseBond L ell` as a finite-dimensional real Hilbert space. -/
abbrev CoarseBondSpace (L : PeriodicLatticeExtent) (ell : ℕ) := EuclideanSpace ℝ (CoarseBond L ell)

/-- The identity-on-underlying-functions equivalence. -/
noncomputable def coarseBondEquiv (L : PeriodicLatticeExtent) (ell : ℕ) :
    CoarseBondSpace L ell ≃ₗ[ℝ] (CoarseBond L ell → ℝ) :=
  (EuclideanSpace.equiv (CoarseBond L ell) ℝ).toLinearEquiv

/-- `Q_ell : BondSpace L →ₗ[ℝ] CoarseBondSpace L ell`, transported. -/
noncomputable def coarseRestrictLMH (L : PeriodicLatticeExtent) (ell : ℕ) :
    BondSpace L →ₗ[ℝ] CoarseBondSpace L ell :=
  (coarseBondEquiv L ell).symm.toLinearMap.comp
    ((coarseRestrictLM L ell).comp (bondEquiv L).toLinearMap)

/-- **`Q_ell`, as a genuine `ContinuousLinearMap`** — the secondary target. -/
noncomputable def coarseRestrictCLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    BondSpace L →L[ℝ] CoarseBondSpace L ell :=
  LinearMap.toContinuousLinearMap (coarseRestrictLMH L ell)

/-- **`coarseRestrictCLM`'s value, transported to the raw-function layer** — same pattern as
`gradCLM_apply`/`curlCLM_apply` just above. **Relocated here (substrate-wiring lane, 2026-07-24)
from `HjMinimizer.lean` §8a**, where an identical `rfl` copy of this lemma lived even though it
uses NOTHING from `HjMinimizer` (only `coarseRestrictCLM`/`coarseBondEquiv`/`bondEquiv`/
`coarseRestrict`, all defined right here) — `U1CommutingSquare.lean` needed this fact and,
pre-fix, obtained it transitively via `CoarseCurl.lean`'s (vestigial, now-removed) import of
`HjMinimizer`. Moving the lemma to its natural home (next to its own definition) breaks that
hidden dependency without duplicating content: `HjMinimizer.lean` keeps calling this same
declaration (now via `LatticeOperators.coarseRestrictCLM_apply`) rather than re-proving it. -/
theorem coarseRestrictCLM_apply {L : PeriodicLatticeExtent} (ell : ℕ) (A : BondSpace L) :
    coarseBondEquiv L ell (coarseRestrictCLM L ell A) = coarseRestrict ell (bondEquiv L A) := rfl

/-- **A concrete indicator bond configuration for the `Q_ell` witness** — `1` on the single fine
bond `(witnessY, 0)`, `0` elsewhere. Deliberately a DIFFERENT object from `witnessBondConfig` (§7,
whose job there was to avoid equality-deciding entirely): `Finset.sum_eq_single` is the natural
tool for an indicator, so there is no reason to fight it here. -/
noncomputable def coarseWitnessConfig : Bond AdmissibleSubspace.witnessL → ℝ :=
  fun b => if b = (AdmissibleSubspace.witnessY, (0 : Fin 3)) then 1 else 0

/-- **Shared computation**: the raw (un-normalized) block-sum of `coarseWitnessConfig`'s indicator
against itself is exactly `1` — the SINGLE fine bond `(witnessY,0)` inside `blockOf witnessY
witnessEll` that carries the indicator's `1`. Factored out so both the correct `coarseRestrict` and
the D4 garbage-normalization controls (§9 below) share this one proof of the averaging CONTENT,
differing only in which constant multiplies it — isolating exactly the fact under audit (the
constant), not re-deriving the geometry each time. -/
theorem witness_block_sum_eq_one :
    (∑ x ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll,
      (if (x, (0 : Fin 3)) = (AdmissibleSubspace.witnessY, (0 : Fin 3)) then (1 : ℝ) else 0)) =
    1 := by
  have hmem : AdmissibleSubspace.witnessY ∈
      AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll := by
    rw [AdmissibleSubspace.mem_blockOf]
    intro μ
    fin_cases μ <;> decide
  rw [Finset.sum_eq_single AdmissibleSubspace.witnessY]
  · simp
  · intro x _ hne
    simp only [ite_eq_right_iff]
    intro h
    exact absurd (Prod.mk.injEq .. ▸ h : x = AdmissibleSubspace.witnessY ∧ (0:Fin 3) = 0).1 hne
  · intro h; exact absurd hmem h

/-- **L7 witness, non-degeneracy**: the coarse bond `(witnessY, 0)` (`witnessY ∈ CoarseLattice`,
proved in `AdmissibleSubspace.witnessY_coarse`) picks up a NONZERO average from
`coarseWitnessConfig` (`1` on exactly one fine bond inside `blockOf witnessY witnessEll`). -/
theorem witness_coarseRestrict_ne_zero :
    coarseRestrict AdmissibleSubspace.witnessEll coarseWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) ≠ 0 := by
  simp only [coarseRestrict, coarseWitnessConfig]
  rw [witness_block_sum_eq_one]
  unfold AdmissibleSubspace.witnessEll
  norm_num

/-- **Degenerate/garbage-input test**: a bond configuration supported ENTIRELY OUTSIDE the block
`blockOf witnessY witnessEll` gives `Q_ell A = 0` at the coarse bond `(witnessY,0)` — the
restriction to the correct block is genuinely load-bearing, not vacuous (`coarseRestrict` does not
"see" fine data outside the block it is defined to average). -/
theorem witness_coarseRestrict_outside_eq_zero :
    coarseRestrict AdmissibleSubspace.witnessEll
        (fun b => if b = AdmissibleSubspace.witnessOutsideBond then (1 : ℝ) else 0)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) = 0 := by
  simp only [coarseRestrict]
  have hz : ∀ x ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll,
      (if (x, (0 : Fin 3)) = AdmissibleSubspace.witnessOutsideBond then (1 : ℝ) else 0) = 0 := by
    intro x hx
    rw [if_neg]
    intro heq
    have hxeq : x = (AdmissibleSubspace.witnessOutsideBond).1 := (Prod.ext_iff.mp heq).1
    rw [AdmissibleSubspace.mem_blockOf] at hx
    have h2 := hx 2
    have hx2 : x 2 = AdmissibleSubspace.witnessOutsideBond.1 2 := congrFun hxeq 2
    rw [hx2] at h2
    have hob2 : (AdmissibleSubspace.witnessOutsideBond.1 2).val = 2 := by decide
    have hy2 : (AdmissibleSubspace.witnessY 2).val = 0 := by decide
    have hell : AdmissibleSubspace.witnessEll = 2 := rfl
    rw [hob2, hy2, hell] at h2
    omega
  rw [Finset.sum_congr rfl hz]
  simp

#print axioms witness_coarseRestrict_ne_zero
#print axioms witness_coarseRestrict_outside_eq_zero

/-! ## §9. D4 FALSIFIABILITY for `Q_ell`'s NORMALIZATION CONSTANT

The `∂₁∘∂₀=0` D4 test (§6) refutes a WRONG SIGN CONVENTION on `curlValue`. This is the analogous
test for `coarseRestrict`'s NORMALIZATION CONSTANT — the exact defect an independent source audit
found in this file's own prior history (`compute/lattice_operator_audit/OPERATOR_AUDIT.md`,
`LATTICE_OPERATORS_R2.md`): a coefficient of `η^d = 1/ell³` (CMP95 eq. 1.20's `Q_k'`, the plain
average of a SCALAR) where the source's own eq. (1.18) for `Q_k` (averaging a CONNECTION `A`)
requires `η^{d+1} = 1/ell⁴`. Since this is a purely numerical fact (a rational constant, not a sign
or a combinatorial shape), the falsifiability handle is a WITNESS-level numeric disagreement: two
garbage exponents (`d`, under-normalizing, and `d+2`, over-normalizing) are shown to give DIFFERENT
answers than the correct `d+1` on the identical witness data, so the correct exponent is not merely
"a choice that happens to typecheck" — it is pinned by a concrete number. -/

/-- **D4 GARBAGE #1 (the historical bug)**: `coarseRestrict`'s exact PRE-REPAIR coefficient
`η^d = 1/ell³` — not a strawman invented for this test, but byte-for-byte what this file's
`coarseRestrict` computed before the R2 repair (`LATTICE_OPERATORS_R2.md`), i.e. CMP95 eq. (1.20)'s
`Q_k'` coefficient silently applied to the eq. (1.18) `Q_k`-shaped bond-averaging construction. -/
noncomputable def coarseRestrictUnderNorm {L : PeriodicLatticeExtent} (ell : ℕ)
    (A : Bond L → ℝ) (b : CoarseBond L ell) : ℝ :=
  (1 / (ell : ℝ) ^ 3) * ∑ x ∈ AdmissibleSubspace.blockOf b.1.1 ell, A (x, b.2)

/-- **D4 GARBAGE #2 (the other direction)**: an OVER-normalization, `η^{d+2} = 1/ell⁵` — checked so
this test does not merely confirm "any perturbation changes the number" but specifically brackets
the one correct exponent `d+1` against wrong exponents on BOTH sides. -/
noncomputable def coarseRestrictOverNorm {L : PeriodicLatticeExtent} (ell : ℕ)
    (A : Bond L → ℝ) (b : CoarseBond L ell) : ℝ :=
  (1 / (ell : ℝ) ^ 5) * ∑ x ∈ AdmissibleSubspace.blockOf b.1.1 ell, A (x, b.2)

/-- **The CORRECT normalization's value on the shared witness**: `ell=2`, raw block-sum `=1`
(`witness_block_sum_eq_one`), so `coarseRestrict = 1/2⁴ = 1/16`. -/
theorem coarseRestrict_witness_value :
    coarseRestrict AdmissibleSubspace.witnessEll coarseWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) = 1 / 16 := by
  simp only [coarseRestrict, coarseWitnessConfig]
  rw [witness_block_sum_eq_one]
  unfold AdmissibleSubspace.witnessEll
  norm_num

/-- **GARBAGE #1's value on the SAME witness**: `1/2³ = 1/8` — exactly DOUBLE the correct answer.
The missing power of `ell` bites concretely: this is the precise numeric shape of the bug the
audit found (an answer that is off by a clean factor of `ell`, not a wildly different number),
matching how a scale-sensitive normalization error typically manifests. -/
theorem coarseRestrictUnderNorm_witness_value :
    coarseRestrictUnderNorm AdmissibleSubspace.witnessEll coarseWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) = 1 / 8 := by
  simp only [coarseRestrictUnderNorm, coarseWitnessConfig]
  rw [witness_block_sum_eq_one]
  unfold AdmissibleSubspace.witnessEll
  norm_num

/-- **GARBAGE #2's value on the SAME witness**: `1/2⁵ = 1/32` — half the correct answer, the
opposite-direction mutation. -/
theorem coarseRestrictOverNorm_witness_value :
    coarseRestrictOverNorm AdmissibleSubspace.witnessEll coarseWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) = 1 / 32 := by
  simp only [coarseRestrictOverNorm, coarseWitnessConfig]
  rw [witness_block_sum_eq_one]
  unfold AdmissibleSubspace.witnessEll
  norm_num

/-- **D4 VERDICT #1**: the historical bug's coefficient disagrees with the correct one, on the
identical witness data — `1/16 ≠ 1/8`. This is the exact mutation this dispatch repairs, shown to
FIRE (not vacuous: the two sides are genuinely different rationals, not a tautological restatement
of the definitions). -/
theorem coarseRestrict_ne_coarseRestrictUnderNorm_witness :
    coarseRestrict AdmissibleSubspace.witnessEll coarseWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) ≠
    coarseRestrictUnderNorm AdmissibleSubspace.witnessEll coarseWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) := by
  rw [coarseRestrict_witness_value, coarseRestrictUnderNorm_witness_value]
  norm_num

/-- **D4 VERDICT #2**: the over-correction also disagrees with the correct coefficient —
`1/16 ≠ 1/32` — confirming the D4 handle brackets the correct exponent from both sides, not just
the one direction the historical bug happened to take. -/
theorem coarseRestrict_ne_coarseRestrictOverNorm_witness :
    coarseRestrict AdmissibleSubspace.witnessEll coarseWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) ≠
    coarseRestrictOverNorm AdmissibleSubspace.witnessEll coarseWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) := by
  rw [coarseRestrict_witness_value, coarseRestrictOverNorm_witness_value]
  norm_num

#print axioms witness_block_sum_eq_one
#print axioms coarseRestrict_witness_value
#print axioms coarseRestrictUnderNorm_witness_value
#print axioms coarseRestrictOverNorm_witness_value
#print axioms coarseRestrict_ne_coarseRestrictUnderNorm_witness
#print axioms coarseRestrict_ne_coarseRestrictOverNorm_witness

end AdalyFormal.Balaban.LatticeOperators
