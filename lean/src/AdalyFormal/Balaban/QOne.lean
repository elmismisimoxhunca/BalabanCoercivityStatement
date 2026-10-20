/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.AdmissibleSubspace
import AdalyFormal.Balaban.LatticeOperators

set_option autoImplicit false

/-!
# ~~`Q₁` — CMP99b (3.156)'s seventh ingredient, built and page-cited~~
# `Q₁` — CMP99b (3.156)'s one-step unit→coarse averaging arrow (level-generic template), built and page-cited

## ⚠ SUPERSEDED FRAMING (S75, struck 2026-07-26) — see `compute/q1_adjudication/RULING.md`

~~"Seventh ingredient"~~ is **SUPERSEDED**. `compute/q1_adjudication/RULING.md` (adjudicated
2026-07-26; §4, §5a, §7 row 2) settles the `Q`-vs-`Q₁` question this header's title begged: `Q` and
`Q₁` are **the same one-step block-averaging MAP TEMPLATE** ((3.15)'s `Q(V)`; defining formula
CMP96 (2.125) — `compute/denotation_dict/DENOTATION_DICT.tsv` rows `q_onestep_template_QV`,
`q96_q1_defining_2125`), applied as **two different ARROWS**: `Q` in `δ(QA−B)` is FINE→UNIT (the
Schur fibre, CMP99b (3.159)); `Q₁` in `δ(Q₁B)` is UNIT→COARSE (the (3.156)/(3.157) constraint).
`ell` IS Bałaban's level index (CMP99b (3.19): the `j`-step operator is the one-step formula with
`L → L^j`). This module's `qOnePathSum` (weight `1/ell⁴`) is itself **level-generic** in `ell` —
the object built below is correct and faithful; only this header's framing ("seventh ingredient",
implying a free-standing, unlocated primitive of unknown identity) was wrong. The formula IS
located — CMP96 (2.125), read below — so "not stated anywhere in CMP99b" (next section) remains
true of CMP99b alone but the ingredient itself is not new or mysterious once CMP96 is read.

## THE DEFINITION, VERBATIM, IMAGE-VERIFIED (LAW-11: render read directly, not the OCR layer)

`Q₁`'s own arithmetic formula is **not stated anywhere in CMP99b** (`DeltaKRecursive.lean §0c`,
`CovarianceG1.lean §0c`: pp.421–430 checked page-by-page, zero hits). CMP99b inherits it by explicit
citation to "`[4]` `(2.154–2.155)`" `= CMP96`. Rendered fresh, `compute/qone_renders/CMP96_p245.png`
(byte-identical to the pre-existing `compute/q1_axy/renders/CMP96_p245-23.png`,
`sha256 696a95edcada0dd34414f92d80354a834bd521bca79cdff7ac7d57c3315bf4d0`), printed header
**"Propagators for Lattice Gauge Theories. II" / "245"** confirmed at the top of the page,
immediately above Lemma 2.4:

```
|(Q₁B)(c)|² = |Σ_{x∈B(c₋)} L^{-(d+1)} B([x, x+Le_μ])|²
            = |L^{-d} Σ_{x∈B(y)\Δ'} L^{-1}(x_μ-y_μ+1)B_μ(x)
                + L^{-d} Σ_{x∈Δ'} B_μ(x)
                + L^{-d} Σ_{x∈B(y+Le_μ)} L^{-1}(2L-1+y_μ-x_μ)B_μ(x)|²
```

with `c = ⟨c₋,c₊⟩`, `c₋ = y`, `c₊ = y+Le_μ` (the figure on the same page, labels confirmed by direct
image inspection), and "We identify `B(b) = B_μ(x)` for `b = ⟨x,x+e_μ⟩`" (same page, immediately
above the display) — `B_μ(x)` is the **fine, UNIT-length bond value**, matching this tree's own
`Bond L := PeriodicLatticeSite L × Fin 3` (`AdmissibleSubspace.Bond`) exactly: one real per
forward-oriented unit edge.

## THE READING THIS FILE COMMITS TO, DERIVED (not assumed) FROM THE EXPANSION ABOVE

`B([x,x+Le_μ])` — the value of the bond field on the **LONG** segment from `x` to `x+Le_μ` — is
**not** a primitive of `Bond L → ℝ` (that type only stores UNIT bonds). The middle line of the
display above is the operative evidence for how to read it: expanding
`Σ_{x∈B(c₋)} L^{-(d+1)}B([x,x+Le_μ])` term-by-term in the FINE unit-bond values `B_μ(x)` produces a
`Σ`over `x` ranging across **the whole doubled block width** (`x ∈ B(y)\Δ'`, `x ∈ Δ'`,
`x ∈ B(y+Le_μ)` — three overlapping windows spanning `[y_μ, y_μ+2L-1)`, not merely `[y_μ,y_μ+L)`)
with **linearly-ramping coefficients** (`(x_μ-y_μ+1)`, constant `1`, `(2L-1+y_μ-x_μ)`) — the exact
"tent"/triangular shape produced by convolving TWO width-`L` indicators. This is precisely what
results from
```
B([x, x+Le_μ]) := Σ_{i=0}^{L-1} B_μ(x + i·e_μ)     (★)
```
(the natural additive/telescoping extension of a bond field over a longer segment — the SAME
additive convention `LatticeOperators.lean` already uses throughout for `gradValue`/`curlValue`,
never a multiplicative holonomy in this file's ℝ-linear setting) summed again over
`x ∈ B(c₋)` (the OUTER sum, `L^d` terms): for a FIXED fine bond `B_μ(z)`, its total multiplicity
across the DOUBLE sum `Σ_{x∈B(c₋)}Σ_{i=0}^{L-1}[z = x+ie_μ]` is exactly the discrete convolution of
two width-`L` boxcars, i.e. the triangular function of `z_μ - y_μ` peaking at `L` in the middle
`(2L-1)`-wide window and ramping linearly down to `1` at both ends — reproducing the displayed
coefficients (`L^{-d}·L^{-1}·(x_μ-y_μ+1)`, `L^{-d}·1`, `L^{-d}·L^{-1}·(2L-1+y_μ-x_μ)`) exactly, term
for term, once the shared prefactor `L^{-(d+1)}` is distributed. **This is the derivation, not an
assumption**: §2 below checks it numerically on a concrete witness (`ell=2`) against the source's
OWN worked example, not merely by symbolic pattern-matching.

## `Q₁` = `Q_k` AT `k=1`: THE RELATION TO `Q`, ESTABLISHED FROM CMP95's OWN SENTENCE

CMP95 printed p.20 (`compute/qone_renders/CMP95_p20.png`, byte-identical to
`compute/q1_axy/renders/CMP95_p20-04.png`, `sha256
87cd15502f41e1806a723d009f5624c8311c13cb084cea7b1964929475a32c26`, header "20 / T. Balaban"
confirmed) discusses "Compositions of Renormalization Transformations": *"We can apply the
renormalization transformation again to (1.14). A composition of two transformations is easy to
calculate: ... where `z⁽²⁾` is a numerical factor coming from scaling transformations and `Q₂`
is defined as `Q` only with the number `L` replaced by `L²` in all definitions."* — i.e. the
UNSUBSCRIPTED `Q` used in the SINGLE application (1.14)/(1.10)-family **is itself `Q_k` at
`k=1`** (the base blocking factor `L`, one RG step), and `Q_2` is the SAME formula with `L → L²`
(`k=2`). Eq. (1.18) (same page, quoted in `LatticeOperators.lean`) is this general `Q_k` family:
`(Q_kA)_b = Σ_{x∈B^k(b_-)}η^{d+1}A([x,x(b)])`, `η=L^{-k}`. **CMP96's `Q₁` (p.245) is this same
family at `k=1`** — the SAME symbol Balaban already uses bare (`Q`) for the single-step case in
CMP95's own composition discussion, confirmed by matching weight (`η^{d+1}=L^{-(d+1)}`, both
pages), matching shape (block-sum of a long-bond value), and by CMP96's own explicit
"Introduction... we use all the notations introduced there [CMP95] without further explanation."

**`Q₁` (this family) is emphatically NOT the same object as `CovarianceG1.QMap`/`QLinearMap`
(CMP99b p.430's spelled-out `Q'`)** — `CovarianceG1.lean §0c` already found this independently; this
file adds the PRECISE reason, derived from (★) above: `Q'` (CMP95 eq. 1.20, p.20, the SAME page)
acts on a SITE-valued SCALAR gauge parameter `λ`, `(Q_k'λ)(y) = Σ_{x∈B^k(y)}η^dλ(x)` — a PLAIN
average, ONE FEWER power of `η` than `Q_k`, because a scalar site-value has no "which unit step
along the block" degree of freedom to sum over (★) supplies for a BOND/connection value. `Q₁`'s
extra power of `L^{-1}` is not a free coefficient choice; it is FORCED by the extra summation
(★) contributes, and this file's `qOnePathSum` (§1) literally builds that extra sum, unlike the
pre-existing `coarseRestrict` (`LatticeOperators.lean §8`), which does NOT (see §3's D4 finding
below).

## §0d — WHY `LatticeOperators.coarseRestrictCLM` IS **NOT** REUSED AS `Q₁` (a genuine finding, not
a strawman)

`coarseRestrict ell A b := (1/ell⁴) · Σ_{x∈blockOf b.1 ell} A(x, b.2)` (`LatticeOperators.lean §8`,
its own R2-repaired normalization) sums a SINGLE fine unit bond `A(x,b.2)` per block site `x` — it
never builds `(★)`'s inner path-sum over the `L` unit steps forming the long bond `[x,x+Le_μ]`. Its
own docstring correctly re-derives the *coefficient* `η^{d+1}=1/ell⁴` from CMP95 (1.18) directly (a
real, useful repair, `LATTICE_OPERATORS_R2.md`), but the coefficient alone does not make the sum
faithful: the coefficient `1/ell⁴` is only the CORRECT normalization once the numerator ALSO sums
`ell` path-steps per block site (giving `ell³·ell = ell⁴` total terms, each weight `1`, i.e. a
genuine arithmetic mean over `ell⁴` fine-bond-instances) — `coarseRestrict` supplies only `ell³`
terms (one per block site), so its normalization and its summand count are mismatched by exactly
the factor `(★)`'s inner sum supplies. **§3 below proves this numerically**: `qOnePathSum` and
`LatticeOperators.coarseRestrict` disagree on a shared witness (not a relabelled constant — a
genuinely different value), so adopting `coarseRestrictCLM` unmodified as `Q₁` would have been
the exact "same-shaped, wrong-object" hazard the mandate warns about. `coarseRestrict`'s TYPE,
its `CoarseBond`/`CoarseBondSpace` Hilbert-space promotion, and its surrounding
`blockOf`/`CoarseLattice` infrastructure ARE reused here (LAW-19) — only its ARITHMETIC BODY is
not.

## What this file builds

1. **§1 — `qOnePathSum`/`qOnePathSumLM`/`qOnePathSumCLM`**: the faithful `Q_k`-family single-level
   block average, `(★)`'s double sum, as a value function / `LinearMap` / `ContinuousLinearMap`,
   reusing `LatticeOperators.CoarseBond`/`CoarseBondSpace`/`coarseBondEquiv` (LAW-19).
2. **§2 — numeric cross-check against the source's OWN worked coefficients** on a small witness
   (`ell=2`), confirming (★) is not merely symbolically plausible but reproduces the PRINTED
   `(x_μ-y_μ+1)`-type ramp exactly at a concrete point.
3. **§3 — D4 falsifiability**: `qOnePathSum` vs `coarseRestrict`, proved numerically UNEQUAL on a
   shared witness — the reuse candidate's disqualification, kernel-checked, not asserted.
4. **§4 — `ker(Q₁)`**, built as a genuine `Submodule`, with:
   - `ker(Q₁) ≠ ⊤` (a real restriction) via a witness bond configuration outside the kernel;
   - `ker(Q₁) ≠ ⊥` (satisfiable, nontrivially) via a genuine nonzero cancelling configuration;
   - the four named degeneracies checked explicitly (§5): `ell=1` (collapses the restriction —
     proved, not merely asserted, and used to show why the non-degeneracy witnesses above are
     NOT run there), constant bond configurations (checked against the kernel directly), and the
     `U≡1`/central-`U` degeneracies explicitly named as INAPPLICABLE to `Q₁` itself (it is a
     REAL-linear, non-conjugated object — those degeneracies belong to `Q'`'s
     `R(·)`-conjugation, `CovarianceG1.lean`, a different operator; stated, not silently
     elided).
5. **§6 — wiring**: how `qOnePathSumCLM` could instantiate `DeltaKRecursive.RGScaleFamily.Q1`'s
   opaque field, WITHOUT editing that file.

## What this file does NOT build (named, not silently dropped)

* The `R(·)`-conjugation / SU(2) instantiation (`CovarianceG1.lean`'s own named residual, unrelated
  to `Q₁` itself, which carries no conjugation in CMP96's own formula).
* `Ax(y)`'s bond geometry, `Λ`, `H₁`, `D̃⁽²⁾`, `J`, `a` — unrelated ingredients, out of scope.
* Editing `DeltaKRecursive.lean`/`CovarianceG1.lean`/`LatticeOperators.lean` (write-scope NO-GO;
  four sibling lanes are live). `qOnePathSumCLM`'s use as a value for `RGScaleFamily.Q1` is stated
  (§6) but not wired by editing that file.
-/

namespace AdalyFormal.Balaban.QOne

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `qOnePathSum`: the faithful `Q_k`-family single-level block average, `(★)` built
literally -/

/-- **The `i`-th site along the path from `x` in direction `μ`** — `x` shifted by
`periodicLatticeShift` `i` times. Built via `Nat.iterate`, not assumed to equal any closed form
(§1a proves the closed form as a THEOREM, not a definition, so the periodic wraparound behavior is
exactly what `periodicLatticeShift` already establishes, not a fresh assumption). -/
def pathSite (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) : PeriodicLatticeSite L :=
  (fun y => periodicLatticeShift y μ)^[i] x

theorem pathSite_zero (x : PeriodicLatticeSite L) (μ : Fin 3) : pathSite x μ 0 = x := rfl

theorem pathSite_succ (x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    pathSite x μ (i + 1) = periodicLatticeShift (pathSite x μ i) μ :=
  Function.iterate_succ_apply' _ i x

/-- **`B([x,x+Le_μ]) := Σ_{i=0}^{ell-1} B_μ(x+ie_μ)`, formula `(★)`** — the additive telescoping
extension of a unit bond field to the long segment of length `ell`, CMP96 p.245's own `[x,x+Le_μ]`
notation, made concrete. `A` is the FINE (unit) bond field (`Bond L → ℝ`, matching the page's own
`B_μ(x)`), `μ` the shared direction, `x` the base site, `ell` the segment length (`=L` at `k=1`, the
`Q₁` case; general `ell = L^k` for `Q_k`). -/
def longBondValue (A : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ell, A (pathSite x μ i, μ)

theorem longBondValue_add (A1 A2 : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ) :
    longBondValue (A1 + A2) x μ ell = longBondValue A1 x μ ell + longBondValue A2 x μ ell := by
  simp only [longBondValue, Pi.add_apply]
  rw [Finset.sum_add_distrib]

theorem longBondValue_smul (c : ℝ) (A : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ : Fin 3)
    (ell : ℕ) : longBondValue (c • A) x μ ell = c * longBondValue A x μ ell := by
  simp only [longBondValue, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

/-- **`(Q₁A)(c) := L^{-(d+1)} Σ_{x∈B(c₋)} A([x,x+Le_μ])`, CMP96 p.245, literally** (`d=3` throughout
this tree, matching `LatticeOperators.lean`'s own fixed convention) — the OUTER block sum composed
with `(★)`'s inner path sum. `b : LatticeOperators.CoarseBond L ell` (REUSED, LAW-19: base site
constrained to `CoarseLattice`, direction in `Fin 3`, exactly CMP96's `c = ⟨c₋,c₊⟩` with `c₋ ∈ Λ'`,
`c₊ = c₋ + Le_μ`). -/
noncomputable def qOnePathSum {L : PeriodicLatticeExtent} (ell : ℕ)
    (A : Bond L → ℝ) (b : LatticeOperators.CoarseBond L ell) : ℝ :=
  (1 / (ell : ℝ) ^ 4) * ∑ x ∈ blockOf b.1.1 ell, longBondValue A x b.2 ell

theorem qOnePathSum_add {L : PeriodicLatticeExtent} (ell : ℕ) (A1 A2 : Bond L → ℝ)
    (b : LatticeOperators.CoarseBond L ell) :
    qOnePathSum ell (A1 + A2) b = qOnePathSum ell A1 b + qOnePathSum ell A2 b := by
  simp only [qOnePathSum]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => longBondValue_add A1 A2 x b.2 ell

theorem qOnePathSum_smul {L : PeriodicLatticeExtent} (ell : ℕ) (c : ℝ) (A : Bond L → ℝ)
    (b : LatticeOperators.CoarseBond L ell) :
    qOnePathSum ell (c • A) b = c * qOnePathSum ell A b := by
  simp only [qOnePathSum]
  have h : ∀ x ∈ blockOf b.1.1 ell, longBondValue (c • A) x b.2 ell =
      c * longBondValue A x b.2 ell := fun x _ => longBondValue_smul c A x b.2 ell
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
  ring

/-- `Q₁` (general level, parameter `ell`) as a genuine `LinearMap`. -/
noncomputable def qOnePathSumLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    (Bond L → ℝ) →ₗ[ℝ] (LatticeOperators.CoarseBond L ell → ℝ) where
  toFun A := qOnePathSum ell A
  map_add' A1 A2 := funext fun b => qOnePathSum_add ell A1 A2 b
  map_smul' c A := funext fun b => qOnePathSum_smul ell c A b

/-- The `rfl`-unfold making `(qOnePathSumLM L ell) A` usable via `rw`/`simp` without re-deriving the
`FunLike` coercion each time — mirrors `LatticeOperators.QLinearMap_apply`'s own pattern. -/
theorem qOnePathSumLM_apply (L : PeriodicLatticeExtent) (ell : ℕ) (A : Bond L → ℝ) :
    qOnePathSumLM L ell A = qOnePathSum ell A := rfl

/-- `Q₁` as a genuine `ContinuousLinearMap`, on the SAME Hilbert-space promotion
(`LatticeOperators.BondSpace`/`CoarseBondSpace`) `LatticeOperators.coarseRestrictCLM` already uses
(LAW-19 reuse of the Hilbert-space layer, NOT the arithmetic body — see §3). -/
noncomputable def qOnePathSumCLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    LatticeOperators.BondSpace L →L[ℝ] LatticeOperators.CoarseBondSpace L ell :=
  LinearMap.toContinuousLinearMap
    ((LatticeOperators.coarseBondEquiv L ell).symm.toLinearMap.comp
      ((qOnePathSumLM L ell).comp (LatticeOperators.bondEquiv L).toLinearMap))

#print axioms pathSite_zero
#print axioms pathSite_succ
#print axioms longBondValue_add
#print axioms longBondValue_smul
#print axioms qOnePathSum_add
#print axioms qOnePathSum_smul
#print axioms qOnePathSumLM_apply
#print axioms qOnePathSumLM
#print axioms qOnePathSumCLM

/-! ## §1a — reusable general facts: `longBondValue` at `ell=2` unfolds to two terms;
`periodicLatticeShift` is injective. Both used repeatedly in §2-§5's concrete evaluations. -/

/-- **`(★)` unfolded at `ell=2`** — the exact case `Q₁` uses when the witness lattice's blocking
factor is `2` (`AdmissibleSubspace.witnessEll`). General in `L`, `A`, `x`, `μ` — not tied to any one
witness. -/
theorem longBondValue_ell2 (A : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    longBondValue A x μ 2 = A (x, μ) + A (periodicLatticeShift x μ, μ) := by
  simp [longBondValue, Finset.sum_range_succ, pathSite_zero, pathSite_succ]

/-- **`periodicLatticeShift (·) μ` is injective** — it is `Function.update x μ (x μ + 1)`, and
`Fin (n+1)`'s `+1` is cancellable (an additive group), so distinct `x` give distinct images. A
general fact about `Target.ClayStatement.periodicLatticeShift`, proved here (not assumed),
reused throughout §2-§5 to extract the unique block site whose long-bond path lands on a given
target bond. -/
theorem periodicLatticeShift_injective (μ : Fin 3) :
    Function.Injective (fun x : PeriodicLatticeSite L => periodicLatticeShift x μ) := by
  intro x x' h
  simp only [periodicLatticeShift] at h
  funext ν
  by_cases hν : ν = μ
  · subst hν
    have hxx' := congrFun h ν
    rw [Function.update_self, Function.update_self] at hxx'
    exact add_right_cancel hxx'
  · have hxx' := congrFun h ν
    rw [Function.update_of_ne hν, Function.update_of_ne hν] at hxx'
    exact hxx'

/-- **The "isolated indicator" sum identity**: summing an indicator `x = a` over a Finset picks out
`1` exactly when `a` is a member, `0` otherwise. Direct restatement of `Finset.sum_ite_eq'` in the
exact shape §2-§5 need. -/
theorem sum_ite_eq_of_mem {s : Finset (PeriodicLatticeSite L)} {a : PeriodicLatticeSite L} :
    ∑ x ∈ s, (if x = a then (1 : ℝ) else 0) = if a ∈ s then 1 else 0 := by
  simp [Finset.sum_ite_eq']

/-- **The "isolated shifted-indicator" sum identity**: summing an indicator `shift x μ = a` over a
Finset `s`, given a KNOWN member `x0 ∈ s` with `shift x0 μ = a`, evaluates to exactly `1` —
injectivity (`periodicLatticeShift_injective`) rules out any OTHER member of `s` also hitting
`a`. -/
theorem sum_ite_shift_eq_of_mem {s : Finset (PeriodicLatticeSite L)} {μ : Fin 3}
    {a x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ s) (heq : periodicLatticeShift x0 μ = a) :
    ∑ x ∈ s, (if periodicLatticeShift x μ = a then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single x0]
  · simp [heq]
  · intro b hb hne
    simp only [ite_eq_right_iff]
    intro hcontra
    exact absurd (periodicLatticeShift_injective μ (hcontra.trans heq.symm)) hne
  · intro h
    exact absurd hx0 h

#print axioms longBondValue_ell2
#print axioms periodicLatticeShift_injective
#print axioms sum_ite_eq_of_mem
#print axioms sum_ite_shift_eq_of_mem

/-! ## §2 — CONCRETE WITNESS: `qOnePathSum` vs `LatticeOperators.coarseRestrict`, on
`AdmissibleSubspace.witnessL`/`witnessY`/`witnessEll = 2` (LAW-19 reuse of the SAME witness lattice
already exercised throughout `Balaban/`) — the D4 disqualification of naive reuse,
kernel-checked. -/

open AdmissibleSubspace (witnessL witnessY witnessEll witnessY_coarse)

/-- `site1 := (1,0,0)` on the witness lattice — the SECOND site of the `μ=0` axis inside
`blockOf witnessY witnessEll` (`witnessY = (0,0,0)` is the first). -/
def site1 : PeriodicLatticeSite witnessL := fun μ => if μ.val = 0 then 1 else 0

theorem site1_mem_block : site1 ∈ blockOf witnessY witnessEll := by decide

theorem witnessY_mem_block : witnessY ∈ blockOf witnessY witnessEll := by decide

/-- `periodicLatticeShift witnessY 0 = site1` — the base site's forward `μ=0` neighbour IS `site1`,
computed directly (`Fin 4` arithmetic, `0+1=1`). -/
theorem shift_witnessY_eq_site1 : periodicLatticeShift witnessY 0 = site1 := by decide

/-- The target coarse bond both witnesses below coarse-average onto: base `witnessY` (a genuine
`CoarseLattice` member), direction `0`. -/
noncomputable def targetCoarseBond : LatticeOperators.CoarseBond witnessL witnessEll :=
  (⟨witnessY, witnessY_coarse⟩, (0 : Fin 3))

/-- **The D4 witness configuration**: the indicator of the single fine bond `(site1, 0)` — chosen
(not `(witnessY,0)`) precisely because it is reached by BOTH terms of `longBondValue_ell2` at TWO
different block sites (`x=witnessY` via the SHIFT term, `x=site1` via the DIRECT term), the exact
"multiplicity-`2`" case the tent-function derivation in this file's header predicts (peak
multiplicity `=ell=2` at the interior site). -/
noncomputable def d4Config : Bond witnessL → ℝ := fun e => if e = (site1, (0 : Fin 3)) then 1 else 0

/-- **`qOnePathSum`'s value on `d4Config`: `1/8`** — `longBondValue` contributes `1` from `x =
witnessY` (its SHIFT term hits `site1`) AND `1` from `x = site1` (its DIRECT term hits `site1`
itself), total block-sum `2`, times the `1/16` prefactor. -/
theorem qOnePathSum_d4Config : qOnePathSum witnessEll d4Config targetCoarseBond = 1 / 8 := by
  change (1 / (2 : ℝ) ^ 4) *
      ∑ x ∈ blockOf witnessY 2, longBondValue d4Config x 0 2 = 1 / 8
  have hsite1 : site1 ∈ blockOf witnessY 2 := by decide
  have hwy : witnessY ∈ blockOf witnessY 2 := by decide
  have hshift : periodicLatticeShift witnessY 0 = site1 := by decide
  have hsum : ∀ x ∈ blockOf witnessY 2, longBondValue d4Config x 0 2 =
      (if x = site1 then (1 : ℝ) else 0) +
        (if periodicLatticeShift x 0 = site1 then (1 : ℝ) else 0) := by
    intro x _
    rw [longBondValue_ell2]
    simp only [d4Config, Prod.mk.injEq, and_true]
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib,
    sum_ite_eq_of_mem (s := blockOf witnessY 2) (a := site1),
    sum_ite_shift_eq_of_mem (s := blockOf witnessY 2) (μ := 0) (a := site1) (x0 := witnessY)
      hwy hshift, if_pos hsite1]
  norm_num

/-- **`LatticeOperators.coarseRestrict`'s value on the SAME configuration: `1/16`** — it sums only
the DIRECT term (`x = site1` contributes `1`; every other block site contributes `0`), never the
shift term — exactly the missing inner path-sum this file's header identifies. -/
theorem coarseRestrict_d4Config :
    LatticeOperators.coarseRestrict witnessEll d4Config targetCoarseBond = 1 / 16 := by
  change (1 / (2 : ℝ) ^ 4) * ∑ x ∈ blockOf witnessY 2, d4Config (x, 0) = 1 / 16
  have hsite1 : site1 ∈ blockOf witnessY 2 := by decide
  have hsum : ∀ x ∈ blockOf witnessY 2, d4Config (x, (0 : Fin 3)) =
      (if x = site1 then (1 : ℝ) else 0) := by
    intro x _
    simp only [d4Config, Prod.mk.injEq, and_true]
  rw [Finset.sum_congr rfl hsum, sum_ite_eq_of_mem (s := blockOf witnessY 2) (a := site1),
    if_pos hsite1]
  norm_num

/-- **THE D4 VERDICT**: `qOnePathSum` and `LatticeOperators.coarseRestrict` genuinely DISAGREE on
the SAME configuration and the SAME coarse bond (`1/8 ≠ 1/16`) — reusing `coarseRestrictCLM`
unmodified as `Q₁` would have been the exact same-shaped-wrong-object hazard the mandate warns
about. Kernel-checked, not asserted. -/
theorem qOnePathSum_ne_coarseRestrict_d4Config :
    qOnePathSum witnessEll d4Config targetCoarseBond ≠
      LatticeOperators.coarseRestrict witnessEll d4Config targetCoarseBond := by
  rw [qOnePathSum_d4Config, coarseRestrict_d4Config]
  norm_num

#print axioms site1_mem_block
#print axioms witnessY_mem_block
#print axioms shift_witnessY_eq_site1
#print axioms qOnePathSum_d4Config
#print axioms coarseRestrict_d4Config
#print axioms qOnePathSum_ne_coarseRestrict_d4Config

set_option maxRecDepth 8000

/-! ## §3 — `ker(Q₁)`: NON-DEGENERACY BOTH WAYS, on the witness lattice

`ker(Q₁) ≠ ⊤` (task item 5's first half: the (3.156) restriction is a REAL restriction, some
configuration fails it) reuses `d4Config` (§2): its image at `targetCoarseBond` is `1/8 ≠ 0`, so
`d4Config` is genuinely excluded.

`ker(Q₁) ≠ ⊥` (satisfiable, non-trivially) needs a GENUINE nonzero configuration whose coarse
average vanishes **at every coarse bond**, not merely one — the first attempt at this
(a two-bond cancelling pair, `2·[witnessY,0] − [site1,0]`) was tried and FOUND TO FAIL exactly this
global requirement: on the periodic torus, the coarse block based at `(2,0,0)` reaches `witnessY`'s
own bond via its OWN shift term (the wraparound coupling adjacent coarse blocks), so that pair's
image is `0` at `targetCoarseBond` but **`1/8 ≠ 0` at the coarse bond based at `(2,0,0)`** — a
genuinely non-degenerate-LOOKING configuration that is nonetheless NOT a global kernel element.
This resistance is recorded, not papered over: a `python3` cross-check
(`/tmp/.../q1_kernel_check.py`, both branches computed) confirms it numerically (naive pair:
`0` at coarse base `0`, `2` at coarse base `2`). The FIX below (a period-`2` checkerboard
alternator) is chosen because it cancels **pointwise, before the block-sum even runs** —
`longBondValue` itself vanishes at every site — sidestepping the wraparound coupling entirely
rather than fighting it. -/

/-- **The checkerboard alternator**: `A(x,0) = (-1)^{(x 0).val}`, `A(x,μ)=0` for `μ≠0`. A genuine,
GLOBAL, nonzero configuration. -/
noncomputable def checkerConfig : Bond witnessL → ℝ :=
  fun e => if e.2 = (0 : Fin 3) then (-1 : ℝ) ^ (e.1 0).val else 0

theorem checkerConfig_ne_zero : checkerConfig ≠ 0 := by
  intro h
  have := congrFun h (witnessY, (0 : Fin 3))
  simp only [checkerConfig, witnessY, Pi.zero_apply] at this
  norm_num at this

/-- Incrementing coordinate `0` by one step (`periodicLatticeShift`) reads off as `x 0 + 1` in
`Fin 4` (`Function.update_self`). -/
theorem checker_shift_flips (x : PeriodicLatticeSite witnessL) :
    (periodicLatticeShift x 0) 0 = x 0 + 1 := by
  simp [periodicLatticeShift, Function.update_self]

/-- **The pointwise cancellation**: for EVERY value `v : Fin 4` of `x 0`, `(-1)^v.val +
(-1)^(v+1).val = 0` — a concrete `4`-way case check (including the periodic wraparound `3 ↦ 0`,
odd to even), not an assumed general fact. -/
theorem checker_pointwise_cancel (x : PeriodicLatticeSite witnessL) :
    checkerConfig (x, (0 : Fin 3)) + checkerConfig (periodicLatticeShift x 0, (0 : Fin 3)) = 0 := by
  simp only [checkerConfig, checker_shift_flips]
  generalize hv : x 0 = v
  fin_cases v <;> norm_num [Fin.add_def, witnessL]

/-- **`longBondValue checkerConfig x 0 2 = 0` for EVERY `x`** — the checkerboard cancels before any
block-sum runs at all, so it is trivially in the kernel of `qOnePathSum` at `ell=2` for EVERY coarse
bond, not merely one. -/
theorem longBondValue_checkerConfig_eq_zero (x : PeriodicLatticeSite witnessL) :
    longBondValue checkerConfig x 0 2 = 0 := by
  rw [longBondValue_ell2]
  exact checker_pointwise_cancel x

/-- **`checkerConfig`'s image is `0` at EVERY `ell=2` coarse bond, EVERY base, EVERY direction** —
the genuine global membership `qOnePathSumLM_ker_ne_bot` needs. Direction `μ≠0`: `checkerConfig` is
`0` on every such bond by construction, so `longBondValue` is trivially `0`. Direction `μ=0`:
`longBondValue_checkerConfig_eq_zero`, for every `x`, makes the whole block-sum `0` regardless of
which coarse base the block sits at — genuinely global, not merely at `targetCoarseBond`. Stated
specifically at `ell = witnessEll = 2` (the value `longBondValue_checkerConfig_eq_zero` was proved
for) — NOT a claim for arbitrary `ell`. -/
theorem qOnePathSum_checkerConfig_eq_zero (b : LatticeOperators.CoarseBond witnessL witnessEll) :
    qOnePathSum witnessEll checkerConfig b = 0 := by
  unfold qOnePathSum
  rcases eq_or_ne b.2 0 with hμ | hμ
  · have hzero : ∀ x ∈ blockOf b.1.1 witnessEll,
        longBondValue checkerConfig x b.2 witnessEll = 0 := by
      intro x _
      rw [hμ]
      exact longBondValue_checkerConfig_eq_zero x
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, mul_zero]
  · have hzero : ∀ x ∈ blockOf b.1.1 witnessEll,
        longBondValue checkerConfig x b.2 witnessEll = 0 := by
      intro x _
      apply Finset.sum_eq_zero
      intro i _
      simp only [checkerConfig]
      rw [if_neg hμ]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, mul_zero]

#print axioms checkerConfig_ne_zero
#print axioms checker_shift_flips
#print axioms checker_pointwise_cancel
#print axioms longBondValue_checkerConfig_eq_zero
#print axioms qOnePathSum_checkerConfig_eq_zero

/-! ## §3a — `ker(Q₁) ≠ ⊤`, `ker(Q₁) ≠ ⊥` at the `LinearMap` level (the honest home for these
facts: `qOnePathSumLM` acts directly on `Bond L → ℝ`, with no Hilbert-space-equivalence plumbing
needed to state kernel membership). -/

theorem qOnePathSumLM_ker_ne_top :
    LinearMap.ker (qOnePathSumLM witnessL witnessEll) ≠ ⊤ := by
  intro htop
  have hmem : d4Config ∈ LinearMap.ker (qOnePathSumLM witnessL witnessEll) :=
    htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, qOnePathSumLM_apply] at hmem
  have := congrFun hmem targetCoarseBond
  rw [Pi.zero_apply, qOnePathSum_d4Config] at this
  norm_num at this

theorem qOnePathSumLM_ker_ne_bot :
    LinearMap.ker (qOnePathSumLM witnessL witnessEll) ≠ ⊥ := by
  intro hbot
  have hmem : checkerConfig ∈ LinearMap.ker (qOnePathSumLM witnessL witnessEll) := by
    rw [LinearMap.mem_ker, qOnePathSumLM_apply]
    funext b
    exact qOnePathSum_checkerConfig_eq_zero b
  rw [hbot, Submodule.mem_bot] at hmem
  exact checkerConfig_ne_zero hmem

#print axioms qOnePathSumLM_ker_ne_top
#print axioms qOnePathSumLM_ker_ne_bot

/-! ## §3b — the SAME facts transported to the `ContinuousLinearMap` layer (`qOnePathSumCLM`,
`LatticeOperators.BondSpace`/`CoarseBondSpace`) — the literal `ker(Q₁)` the mandate names, since
`Q₁`'s natural home is the Hilbert-space operator, not the bare `LinearMap`. The transport is via
the linear EQUIVALENCE `bondEquiv`/`coarseBondEquiv` (isomorphisms, so kernel non-degeneracy carries
over exactly, not merely "morally"). `LinearMap.ker` is stated on the EXPLICIT `LinearMap`
coercion of the `ContinuousLinearMap` (`(f : A →ₗ[ℝ] B)`), matching `DeltaKRecursive.lean`'s own
`(F.Q1 k : H →ₗ[ℝ] H)` coercion idiom. -/

theorem qOnePathSumCLM_apply (ell : ℕ) (A : LatticeOperators.BondSpace witnessL) :
    LatticeOperators.coarseBondEquiv witnessL ell (qOnePathSumCLM witnessL ell A) =
      qOnePathSum ell (LatticeOperators.bondEquiv witnessL A) := by
  change LatticeOperators.coarseBondEquiv witnessL ell
      ((LatticeOperators.coarseBondEquiv witnessL ell).symm
        (qOnePathSumLM witnessL ell (LatticeOperators.bondEquiv witnessL A)))
      = qOnePathSum ell (LatticeOperators.bondEquiv witnessL A)
  rw [LinearEquiv.apply_symm_apply, qOnePathSumLM_apply]

/-- Abbreviation for `qOnePathSumCLM`'s explicit `LinearMap` coercion, used repeatedly below to keep
the `ker`-facts' statements readable (mirrors `DeltaKRecursive.lean`'s own `(F.Q1 k : H →ₗ[ℝ] H)`
coercion idiom). -/
noncomputable abbrev qOnePathSumCLMasLM :
    LatticeOperators.BondSpace witnessL →ₗ[ℝ] LatticeOperators.CoarseBondSpace witnessL
    witnessEll := qOnePathSumCLM witnessL witnessEll

theorem qOnePathSumCLM_ker_ne_top : LinearMap.ker qOnePathSumCLMasLM ≠ ⊤ := by
  intro htop
  set A0 : LatticeOperators.BondSpace witnessL := (LatticeOperators.bondEquiv witnessL).symm
    d4Config with hA0
  have hmem : A0 ∈ LinearMap.ker qOnePathSumCLMasLM := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hmem
  have hval := qOnePathSumCLM_apply witnessEll A0
  rw [hmem] at hval
  simp only [map_zero, hA0, LinearEquiv.apply_symm_apply] at hval
  have := congrFun hval.symm targetCoarseBond
  rw [Pi.zero_apply, qOnePathSum_d4Config] at this
  norm_num at this

theorem qOnePathSumCLM_ker_ne_bot : LinearMap.ker qOnePathSumCLMasLM ≠ ⊥ := by
  intro hbot
  set A0 : LatticeOperators.BondSpace witnessL := (LatticeOperators.bondEquiv witnessL).symm
    checkerConfig with hA0
  have hA0_ne : A0 ≠ 0 := by
    intro h
    apply checkerConfig_ne_zero
    have := congrArg (LatticeOperators.bondEquiv witnessL) h
    rwa [hA0, LinearEquiv.apply_symm_apply, map_zero] at this
  have hmem : A0 ∈ LinearMap.ker qOnePathSumCLMasLM := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    apply (LatticeOperators.coarseBondEquiv witnessL witnessEll).injective
    rw [qOnePathSumCLM_apply, map_zero]
    funext b
    rw [hA0, LinearEquiv.apply_symm_apply]
    exact qOnePathSum_checkerConfig_eq_zero b
  rw [hbot, Submodule.mem_bot] at hmem
  exact hA0_ne hmem

#print axioms qOnePathSumCLM_apply
#print axioms qOnePathSumCLM_ker_ne_top
#print axioms qOnePathSumCLM_ker_ne_bot

/-! ## §4 — THE FOUR NAMED DEGENERACIES, checked explicitly

**`ell=1`** (§4a): `qOnePathSum` collapses to the literal identity, and its kernel becomes trivial
(`⊥`) — the exact "everything collapses, every check passes green" failure mode the mandate warns
against, PROVED here (not merely asserted) precisely so the non-degeneracy witnesses of §3 can be
seen NOT to be run in this degenerate regime (`ell = witnessEll = 2 ≠ 1`).

**Constant bond configurations** (§4b): `Q₁` is a FIXED POINT on constants (`Q₁(c) = c` exactly,
for any coarse bond whose base's block genuinely fits) — so a constant configuration is excluded
from `ker(Q₁)` for every `c ≠ 0`, confirming the kernel does not accidentally swallow the whole
"constant" subspace.

**`U ≡ 1`, central `U` (`Ad(±I)=id`)** (§4c): named EXPLICITLY INAPPLICABLE to `Q₁` itself, not
silently elided — `Q₁` (CMP96 p.245) is a REAL-LINEAR, NON-conjugated block average (this file's
header derives this: no `R(V(Γ_{y,x}))` factor anywhere in CMP96's formula, unlike `Q'`
p.430/`CovarianceG1.QMap`). These two degeneracies are properties of `R(·)`-conjugation
specifically (`CovarianceG1.lean §1a`'s own `qWitnessCollapsed`/`Rconj:=id` check already exercises
exactly this for `Q'`) — `Q₁` has no conjugation factor to degenerate in the first place. -/

/-! ### §4a — `ell = 1` collapses `Q₁` to the identity, and its kernel to `⊥` -/

theorem mem_CoarseLattice_one {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) :
    y ∈ CoarseLattice L 1 := by
  rw [mem_CoarseLattice]
  intro μ
  omega

theorem blockOf_one_eq_singleton {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) :
    blockOf y 1 = {y} := by
  ext x
  simp only [mem_blockOf, inBlock, Finset.mem_singleton]
  constructor
  · intro h
    funext ν
    apply Fin.ext
    have h1 := (h ν).1
    have h2 := (h ν).2
    omega
  · intro h
    subst h
    intro ν
    refine ⟨le_refl _, ?_⟩
    omega

/-- **`Q₁` at `ell=1` is the literal identity** (reindexed through `CoarseLattice L 1 = univ`) —
the collapse the mandate names. -/
theorem qOnePathSum_one_eq {L : PeriodicLatticeExtent} (A : Bond L → ℝ)
    (y : PeriodicLatticeSite L) (μ : Fin 3) :
    qOnePathSum 1 A (⟨y, mem_CoarseLattice_one y⟩, μ) = A (y, μ) := by
  unfold qOnePathSum
  rw [blockOf_one_eq_singleton, Finset.sum_singleton]
  simp only [longBondValue, Finset.sum_range_one, pathSite_zero]
  norm_num

/-- **The kernel genuinely COLLAPSES to `⊥` at `ell=1`** — matching the mandate's warning that
"at a degenerate lattice both may collapse". Contrast `qOnePathSumLM_ker_ne_bot` (§3a), which is
run at `ell=witnessEll=2`, NOT here. -/
theorem qOnePathSumLM_one_ker_eq_bot (L : PeriodicLatticeExtent) :
    LinearMap.ker (qOnePathSumLM L 1) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro A hA
  rw [LinearMap.mem_ker, qOnePathSumLM_apply] at hA
  funext e
  obtain ⟨y, μ⟩ := e
  have h := congrFun hA (⟨y, mem_CoarseLattice_one y⟩, μ)
  rw [Pi.zero_apply, qOnePathSum_one_eq] at h
  exact h

#print axioms mem_CoarseLattice_one
#print axioms blockOf_one_eq_singleton
#print axioms qOnePathSum_one_eq
#print axioms qOnePathSumLM_one_ker_eq_bot

/-! ### §4b — constant bond configurations: `Q₁` is a fixed point, NOT collapsed -/

/-- **`Q₁(c) = c` on constants**, whenever the base's block genuinely fits (`hfit`, matching
`AdmissibleSubspace.card_blockOf`'s own hypothesis) and `ell > 0`. General in `L`, `ell`, `y`, `μ`
— not a witness-specific coincidence. -/
theorem qOnePathSum_const {L : PeriodicLatticeExtent} (ell : ℕ) (hell : 0 < ell) (c : ℝ)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L ell)
    (hfit : ∀ ν, (y ν).val + ell ≤ L ν + 1) (μ : Fin 3) :
    qOnePathSum ell (fun _ => c) (⟨y, hy⟩, μ) = c := by
  unfold qOnePathSum
  have hlb : ∀ x ∈ blockOf y ell, longBondValue (fun _ => c) x μ ell = (ell : ℝ) * c := by
    intro x _
    simp only [longBondValue, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hlb, Finset.sum_const, card_blockOf y ell hfit]
  have hellR : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  field_simp
  ring

/-- **Corollary, at the witness data**: `Q₁(c) = c` at `targetCoarseBond` — a constant configuration
is EXCLUDED from `ker(Q₁)` for every `c ≠ 0`, i.e. `Q₁` does not collapse the constant subspace. -/
theorem qOnePathSum_const_witness (c : ℝ) :
    qOnePathSum witnessEll (fun _ => c) targetCoarseBond = c :=
  qOnePathSum_const witnessEll (by decide) c witnessY witnessY_coarse witnessY_fits 0

theorem const_notMem_ker_of_ne_zero (c : ℝ) (hc : c ≠ 0) :
    (fun _ : Bond witnessL => c) ∉ LinearMap.ker (qOnePathSumLM witnessL witnessEll) := by
  intro hmem
  rw [LinearMap.mem_ker, qOnePathSumLM_apply] at hmem
  have h := congrFun hmem targetCoarseBond
  rw [Pi.zero_apply, qOnePathSum_const_witness] at h
  exact hc h

#print axioms qOnePathSum_const
#print axioms qOnePathSum_const_witness
#print axioms const_notMem_ker_of_ne_zero

/-! ### §4c — `U≡1`/central `U` (`Ad(±I)=id`): named INAPPLICABLE, not silently elided

`Q₁`'s own formula (CMP96 p.245, this file's header) carries no group-valued field and no
`R(·)`-conjugation factor at all — it is a REAL-LINEAR average of a REAL bond field `B`. The
degeneracies "`U≡1`" (the gauge field is the group identity everywhere) and "central `U`"
(`Ad(U)=id` for `U` in the center, e.g. `±I` in `SU(2)`) are both statements about how a
**conjugation** action collapses — they are properties of `CovarianceG1.QMap`'s `Rconj` field
(the p.430 `Q'` operator, one RG level up, which DOES carry `R(V(Γ_{y,x}))`), already exercised
concretely by `CovarianceG1.lean §1a`'s `qWitnessCollapsed` (`Rconj := id` exhibits `1` where the
genuine conjugation gives `0`). `Q₁` has no such field to degenerate — this is a genuine STRUCTURAL
fact about which operator carries the conjugation, not a gap in this file's own coverage. -/

/-! ## §5 — WIRING: how `qOnePathSumCLM` COULD instantiate `DeltaKRecursive.RGScaleFamily.Q1`
(NOT built by editing that file — NO-GO, live-edited by a sibling lane)

`RGScaleFamily.Q1 : ℕ → H →L[ℝ] H` — a SINGLE ambient Hilbert space `H`, used for BOTH the domain
AND the codomain at every level `k`. `qOnePathSumCLM L ell : BondSpace L →L[ℝ] CoarseBondSpace L
ell` — by contrast, GENUINELY changes type between domain and codomain (`Bond L` vs
`CoarseBond L ell`, index sets of DIFFERENT cardinality — `card_blockOf`/`card_blockOf_of_coarse`
already establish `|CoarseBond L ell| < |Bond L|` whenever `ell > 1`). **This is not a defect of
this file's construction — it is the EXACT type-level content of `DeltaKRecursive.lean`'s own
disclosed simplification** ("`RGScaleFamily`... carrying all scales on one `H`... at the cost of
literal fidelity to the shrinking-domain aspect"): `qOnePathSumCLM` cannot populate
`RGScaleFamily.Q1` AS STATED, for any single fixed `H`, because `RGScaleFamily.Q1`'s own type
has already erased the domain/codomain distinction the faithful `Q_k`-family genuinely has. -/

/-- **The genuine dimension mismatch, kernel-checked**: on the witness lattice at `ell=2`,
`CoarseBond witnessL witnessEll` has STRICTLY FEWER elements than `Bond witnessL` (`24` vs `192`) —
the concrete instance of the type-level obstruction above, not merely an assertion about it. -/
theorem card_coarseBond_lt_card_bond :
    Fintype.card (LatticeOperators.CoarseBond witnessL witnessEll) <
      Fintype.card (Bond witnessL) := by
  decide

#print axioms card_coarseBond_lt_card_bond

/- **The honest wiring statement**: the ONLY way `qOnePathSumCLM`-shaped data populates a
`RGScaleFamily.Q1 : ℕ → H →L[ℝ] H` field on ONE fixed `H` is via the `H :=
ℝ`/`degenerateFamily`-style degenerate case (`Q1 := 0`, `witnessFamily`/`richWitnessFamily`'s
own existing convention, `DeltaKRecursive.lean §3`), OR by widening `RGScaleFamily` to a
genuinely `k`-varying carrier `H k`/`H (k+1)` — the SAME wall `DeltaKFull.lean §6` already names
for `Δ_k` itself. This is not attempted here (editing `DeltaKRecursive.lean` is NO-GO); recorded
as the exact reason `Q1` cannot be wired in AS A REPLACEMENT for the opaque field without first
widening that file's own type. -/

end AdalyFormal.Balaban.QOne
