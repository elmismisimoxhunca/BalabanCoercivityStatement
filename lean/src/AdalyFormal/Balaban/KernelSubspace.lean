/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.LatticeOperators

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `N(Q')`, `Δ₀`-positivity, `Q'*aQ'` vanishing — CMP96 pp.225-226, the fourth link in the chain

**Task** (`RG_LINEARIZATION.md`, `compute/cmp96_bridge/CMP96_BRIDGE_READING.md`): build `N(Q')` as a
genuine `Submodule`, state `Δ₀ := ∂₀*∂₀`'s positivity on it with the mesh-uniform discrete Poincaré
fact (CMP89 (2.26)/(2.27), asserted uncited in CMP89 itself, a sibling lane's own target) carried as
an EXPLICIT HYPOTHESIS — never an `axiom`, never a `sorry` — and prove, in full, the genuinely
provable-NOW fact that `Q'*aQ'` vanishes on `N(Q')`.

## Source pins (LAW-11: consumed from a prior lane's own independently image-confirmed reading,
`compute/cmp96_bridge/CMP96_BRIDGE_READING.md`, CMP96 printed pp.225-226, image hashes
`e71de8599cd35803679d7c8a57835d9484692edd22f727d9a8572f7fba5b28cd` / `cd7896c19519586cb5c588009749
212f844106eb935619fdccbd530df7473ce3` recorded there)

* **(2.7)/(2.10)**: `N(Q') = {λ : λ=0 on Λ₀, Q_j'λ=0 on Λ_j, j=1,...,k}` — a genuine multi-scale
  JOINT KERNEL condition (not a single-cube "orthogonal to constants" simplification).
* **(2.14)**: `⟨λ,Q'*aQ'λ⟩ = Σ_{j=0}^k Σ_{y∈Λ_j} a_j(L^jη)^{d-2}|(Q_j'λ)(y)|²`, together with the
  page's own remark "we assume that `(Q_0'λ)(x)=λ(x), x∈Λ_0`" — i.e. level 0's map IS the identity,
  by the paper's own convention. The bridge reading (§4, "BRIDGE CONFIRMED") verified DIRECTLY from
  these two facts, by substitution, that every term of this sum vanishes for `λ ∈ N(Q')` — the
  theorem this module ships (§8).
* **p.225, immediately after (2.10)**: "the Laplace operator `Δ` is positive on the subspace
  `N(Q')`... hence it is invertible on this subspace," with the quantitative form (2.11) citing
  CMP89 `[3, 2.26 and 2.27]` — CMP89's own page (`compute/cmp89_positivity/CMP89_POSITIVITY_
  READING.md`) shows this rests on an UNPROVED, UNCITED, mesh-uniform discrete Poincaré/spectral-gap
  assertion ("folklore," not derived on that page either). Per the mandate: carried here as an
  EXPLICIT HYPOTHESIS parameter to the positivity theorems (§7), not proved, not assumed via
  `axiom`, not stubbed with `sorry` — a sibling lane owns closing that hypothesis.
* **CMP95 p.20 eq. (1.20)** (traced via `LATTICE_OPERATORS_R2.md`'s own R2 finding): `Q_k'`, the
  SITE/scalar-valued coarse-restriction (plain average, coefficient `η^d`), is the DISTINCT sibling
  of `Q_k` (already built as `LatticeOperators.coarseRestrict`, BOND/connection-valued, coefficient
  `η^{d+1}` — one power of `ell` MORE). `coarseRestrictSite` below (§1-2) is `Q_k'` built fresh:
  same block geometry (`AdmissibleSubspace.blockOf`, LAW-19 reuse) and the SAME structural pattern
  as `coarseRestrict`, but a genuinely DIFFERENT carrier (`Site → ℝ`, not `Bond → ℝ`) and a
  genuinely DIFFERENT normalization exponent (`ell³`, not `ell⁴`) — confirmed by §3's D4 test to
  give numerically different answers, not a cosmetic relabeling.

## A disclosed modeling simplification (stated up front, not discovered mid-proof)

`AdmissibleSubspace.admissibleSubspace` (a DIFFERENT `(2.121)` object, earlier in the chain) required
`y ∈ CoarseLattice L ell` as an explicit TYPE-LEVEL antecedent (its own R2 repair, guarding against
Sol's exploit of unconstrained centers). **This module's `Level`/`coarseRestrictSite` do NOT repeat
that discipline**: `coarseRestrictSite`'s averaging formula is well-defined for ANY site `y`
(`AdmissibleSubspace.blockOf y ell` is defined for every `y` regardless), and `Λ_j` here is carried
as a free `Finset (PeriodicLatticeSite L)` — matching CMP96's own `Λ_j ⊂ Site` as DATA, a hypothesis
on which sites are used, not a constraint this module's TYPES need to enforce (no theorem below
requires `y ∈ CoarseLattice L ell`, unlike `admissibleSubspace`'s own use of `R`, which genuinely
needed non-overlapping centers to avoid Sol's exploit). This keeps `Level` a plain, NON-dependent
`ℕ × Finset (PeriodicLatticeSite L)` throughout — deliberate, disclosed, and unrelated to any defect
class (no vacuity/D1 risk: `kernelSubspace`'s own non-degeneracy is checked directly in §5).

## What this module builds

1. **`coarseRestrictSite`** (§1) — `Q_j'`, CMP95 (1.20)'s scalar coarse-restriction, as a value
   function/`LinearMap`, reusing `blockOf` (LAW-19).
2. **`coarseRestrictSite_one_eq_self`** (§2) — `Q_0' = id`, DERIVED (not merely assumed, strengthening
   CMP96's own stated convention) from the general formula at `ell=1` (`blockOf y 1 = {y}`).
3. **D4 normalization-exponent falsifiability** (§3) — mirrors `LatticeOperators.lean` §9's own
   pattern: garbage exponents `ell²` (under) and `ell⁴` (over — literally `coarseRestrict`'s OWN
   exponent, a genuine cross-object numeric collision check) disagree with the correct `ell³` on a
   concrete witness.
4. **`kernelSubspace`** (§4) — `N(Q')`, CMP96 (2.7)/(2.10), as a genuine `Submodule ℝ (Site → ℝ)`,
   parametrized by an arbitrary FINITE LIST of levels `(ell_j, Λ_j)` — faithfully capturing the
   source's arbitrary-`k`, per-level-varying-scale structure without inventing the full torus
   domain-decomposition geometry (a sibling lane's own scope, `ScaleLadder.lean`).
5. **Concrete two-level instantiation + non-degeneracy** (§5) — `witnessLevels` (level 0 = identity
   at the SAME `witnessY` `AdmissibleSubspace.lean`'s own witness lattice already anchors, level 1 =
   the coarse-average at `witnessEll`), `kernelSubspace_ne_top` (general) + a concrete `≠ ⊥` witness,
   plus a **D4 quantifier-weakening test** (§8b): dropping the level-0 requirement admits an element
   the true `N(Q')` excludes, for which the quadratic form (item 7) is NONZERO — the `∀`, not `∃`,
   over levels is load-bearing.
6. **`kernelSubspaceH`** (§6) — transported into the genuine Hilbert space `LatticeOperators.
   SiteSpace L`, mirroring `RGLinearization.lean`'s own `admissibleSubspaceH` transport pattern
   (LAW-19).
7. **Positivity, hypothesis-carrying** (§7) — `positive_of_poincare`/`eq_zero_of_laplacian_eq_zero_
   of_poincare`: GIVEN the mesh-uniform Poincaré bound as an explicit parameter (never proved here,
   never an axiom/sorry), `Δ₀ := LatticeOperators.siteLaplacianCLM` is positive-definite and hence
   injective on `kernelSubspaceH` — CMP96 p.225's own stated consequence, "positive... hence
   invertible on this subspace," now a genuine theorem downstream of the named hypothesis.
   **D4 (§7b)**: the constant function is a NONZERO vector with `⟨v,Δ₀v⟩ = 0` GLOBALLY (Δ₀ has the
   constants as its zero-eigenspace, matching CMP89's own stated fact "eigenvectors corresponding to
   eigenvalue 0") — confirming the restriction to `kernelSubspaceH` in the positivity hypothesis is
   genuinely load-bearing, not decorative: Δ₀ is NOT globally positive.
8. **`qFormQstarAQ_eq_zero_of_mem_kernelSubspace`** (§8) — THE theorem the mandate names as
   "genuinely provable now": `⟨λ,Q'*aQ'λ⟩ = 0` for every `λ ∈ N(Q')`, by direct substitution from
   the defining membership condition, matching the bridge reading's own confirmed mechanism exactly.

## What this module does NOT build (named, not silently dropped)

* The full torus/annulus domain-decomposition geometry realizing `Λ_j` as genuine nested regions of
  a single ambient lattice (as opposed to the free `Finset` DATA this module consumes) —
  `ScaleLadder.lean`'s own scope, NOT this dispatch's, and NOT invented here.
* The mesh-uniform discrete Poincaré/spectral-gap constant itself (CMP89 (2.26)/(2.27)'s uncited
  in-page assertion) — a sibling lane's explicit target, carried here strictly as a named hypothesis.
* `R`, `Δ_a`, `G`, `H_j`, `Δ_j` — unchanged NO-GO from every prior lane on this chain.
-/

namespace AdalyFormal.Balaban.KernelSubspace

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace

variable {L : PeriodicLatticeExtent}

/-! ## §1. `coarseRestrictSite` — `Q_j'`, CMP95 eq. (1.20), the SCALAR coarse-restriction -/

/-- **`(Q_ell'λ)(y) := (1/ell³) Σ_{x∈B(y)} λ(x)`, CMP95 eq. (1.20)'s plain-average coefficient
`η^d` (`d=3`)**, contrasting `LatticeOperators.coarseRestrict`'s `η^{d+1} = 1/ell⁴` (the DISTINCT
sibling `Q_ell` averaging a CONNECTION, per the R2 finding this module's docstring traces). Reuses
`blockOf` (LAW-19), NOT re-invented block geometry. Defined for ANY site `y` (see the module
docstring's disclosed simplification: `Λ'`-membership is carried as DATA, not a type constraint). -/
noncomputable def coarseRestrictSite {L : PeriodicLatticeExtent} (ell : ℕ)
    (lam : PeriodicLatticeSite L → ℝ) (y : PeriodicLatticeSite L) : ℝ :=
  (1 / (ell : ℝ) ^ 3) * ∑ x ∈ AdmissibleSubspace.blockOf y ell, lam x

theorem coarseRestrictSite_add {L : PeriodicLatticeExtent} (ell : ℕ)
    (lam1 lam2 : PeriodicLatticeSite L → ℝ) (y : PeriodicLatticeSite L) :
    coarseRestrictSite ell (lam1 + lam2) y =
      coarseRestrictSite ell lam1 y + coarseRestrictSite ell lam2 y := by
  simp only [coarseRestrictSite, Pi.add_apply]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]

theorem coarseRestrictSite_smul {L : PeriodicLatticeExtent} (ell : ℕ) (c : ℝ)
    (lam : PeriodicLatticeSite L → ℝ) (y : PeriodicLatticeSite L) :
    coarseRestrictSite ell (c • lam) y = c * coarseRestrictSite ell lam y := by
  simp only [coarseRestrictSite, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- `Q_ell'` as a genuine `LinearMap`. -/
noncomputable def coarseRestrictSiteLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    (PeriodicLatticeSite L → ℝ) →ₗ[ℝ] (PeriodicLatticeSite L → ℝ) where
  toFun lam := coarseRestrictSite ell lam
  map_add' lam1 lam2 := funext fun y => coarseRestrictSite_add ell lam1 lam2 y
  map_smul' c lam := funext fun y => coarseRestrictSite_smul ell c lam y

/-! ## §2. `Q_0' = id` — DERIVED from the general formula at `ell = 1`, not merely assumed -/

/-- **`blockOf y 1 = {y}`**: a block of side `1` contains exactly its own corner — the single
combinatorial fact `coarseRestrictSite_one_eq_self` needs. -/
theorem blockOf_one_eq_singleton (y : PeriodicLatticeSite L) :
    AdmissibleSubspace.blockOf y 1 = {y} := by
  ext x
  rw [AdmissibleSubspace.mem_blockOf, AdmissibleSubspace.inBlock, Finset.mem_singleton]
  constructor
  · intro h
    funext μ
    have h1 := (h μ).1
    have h2 := (h μ).2
    apply Fin.ext
    omega
  · rintro rfl
    intro μ
    omega

/-- **`self_mem_blockOf`**: every site lies in its own block, for any positive side length —
the elementary fact `coarseRestrictSite`'s D4 witness (§3) needs, general and reusable. -/
theorem self_mem_blockOf (y : PeriodicLatticeSite L) {ell : ℕ} (hell : 0 < ell) :
    y ∈ AdmissibleSubspace.blockOf y ell := by
  rw [AdmissibleSubspace.mem_blockOf, AdmissibleSubspace.inBlock]
  intro μ
  omega

/-- **`Q_0' = id`, DERIVED (not assumed), for EVERY site** — CMP96's own stated convention ("we
assume that `(Q_0'λ)(x)=λ(x)`") is here a genuine consequence of the general definition at `ell=1`,
strictly stronger than an assumption (no side hypothesis needed, per the module's disclosed
simplification). -/
theorem coarseRestrictSite_one_eq_self (lam : PeriodicLatticeSite L → ℝ) (y : PeriodicLatticeSite L) :
    coarseRestrictSite 1 lam y = lam y := by
  simp only [coarseRestrictSite, blockOf_one_eq_singleton, Finset.sum_singleton]
  norm_num

#print axioms blockOf_one_eq_singleton
#print axioms self_mem_blockOf
#print axioms coarseRestrictSite_one_eq_self

/-! ## §3. D4 FALSIFIABILITY for `coarseRestrictSite`'s NORMALIZATION EXPONENT
(mirrors `LatticeOperators.lean` §9's own pattern, for the DISTINCT `Q_ell'` object) -/

/-- **D4 GARBAGE #1 (under-normalization)**: exponent `ell²` instead of the correct `ell³`. -/
noncomputable def coarseRestrictSiteUnderNorm {L : PeriodicLatticeExtent} (ell : ℕ)
    (lam : PeriodicLatticeSite L → ℝ) (y : PeriodicLatticeSite L) : ℝ :=
  (1 / (ell : ℝ) ^ 2) * ∑ x ∈ AdmissibleSubspace.blockOf y ell, lam x

/-- **D4 GARBAGE #2 (over-normalization)**: exponent `ell⁴` — literally `LatticeOperators.
coarseRestrict`'s OWN exponent, a genuine cross-object collision check confirming `Q_ell` and
`Q_ell'` are not secretly the same coefficient. -/
noncomputable def coarseRestrictSiteOverNorm {L : PeriodicLatticeExtent} (ell : ℕ)
    (lam : PeriodicLatticeSite L → ℝ) (y : PeriodicLatticeSite L) : ℝ :=
  (1 / (ell : ℝ) ^ 4) * ∑ x ∈ AdmissibleSubspace.blockOf y ell, lam x

/-- **The witness indicator**: `1` at `witnessY` itself, `0` elsewhere — a single-site indicator,
distinct in shape from `LatticeOperators.lean`'s own bond-valued witnesses (a genuinely different
carrier here). -/
noncomputable def coarseWitnessSiteConfig : PeriodicLatticeSite AdmissibleSubspace.witnessL → ℝ :=
  fun x => if x = AdmissibleSubspace.witnessY then 1 else 0

/-- `witnessY` witnesses its own membership in `blockOf witnessY witnessEll` (via `self_mem_blockOf`,
`witnessEll = 2 > 0`). -/
theorem witnessY_mem_own_block :
    AdmissibleSubspace.witnessY ∈
      AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll :=
  self_mem_blockOf AdmissibleSubspace.witnessY (by unfold AdmissibleSubspace.witnessEll; norm_num)

/-- **Shared block-sum computation**: the raw sum of the witness indicator over
`blockOf witnessY witnessEll` is exactly `1` (the single site `witnessY` itself carries the
indicator's `1`, every other site in the block carries `0`). Factored out so the correct
normalization and both D4 garbage controls share this one geometric fact, isolating exactly the
constant under audit. -/
theorem coarseWitnessSite_block_sum_eq_one :
    (∑ x ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll,
      coarseWitnessSiteConfig x) = 1 := by
  rw [Finset.sum_eq_single AdmissibleSubspace.witnessY]
  · simp [coarseWitnessSiteConfig]
  · intro x _ hne
    simp only [coarseWitnessSiteConfig, ite_eq_right_iff]
    intro h; exact absurd h hne
  · intro h; exact absurd witnessY_mem_own_block h

theorem coarseRestrictSite_witness_value :
    coarseRestrictSite AdmissibleSubspace.witnessEll coarseWitnessSiteConfig
        AdmissibleSubspace.witnessY = 1 / 8 := by
  simp only [coarseRestrictSite]
  rw [coarseWitnessSite_block_sum_eq_one]
  unfold AdmissibleSubspace.witnessEll
  norm_num

theorem coarseRestrictSiteUnderNorm_witness_value :
    coarseRestrictSiteUnderNorm AdmissibleSubspace.witnessEll coarseWitnessSiteConfig
        AdmissibleSubspace.witnessY = 1 / 4 := by
  simp only [coarseRestrictSiteUnderNorm]
  rw [coarseWitnessSite_block_sum_eq_one]
  unfold AdmissibleSubspace.witnessEll
  norm_num

theorem coarseRestrictSiteOverNorm_witness_value :
    coarseRestrictSiteOverNorm AdmissibleSubspace.witnessEll coarseWitnessSiteConfig
        AdmissibleSubspace.witnessY = 1 / 16 := by
  simp only [coarseRestrictSiteOverNorm]
  rw [coarseWitnessSite_block_sum_eq_one]
  unfold AdmissibleSubspace.witnessEll
  norm_num

/-- **D4 VERDICT #1**: `1/8 ≠ 1/4` — the under-normalization genuinely disagrees. -/
theorem coarseRestrictSite_ne_underNorm_witness :
    coarseRestrictSite AdmissibleSubspace.witnessEll coarseWitnessSiteConfig
        AdmissibleSubspace.witnessY ≠
    coarseRestrictSiteUnderNorm AdmissibleSubspace.witnessEll coarseWitnessSiteConfig
        AdmissibleSubspace.witnessY := by
  rw [coarseRestrictSite_witness_value, coarseRestrictSiteUnderNorm_witness_value]; norm_num

/-- **D4 VERDICT #2**: `1/8 ≠ 1/16` — the over-normalization (`coarseRestrict`'s own exponent)
genuinely disagrees too, confirming `Q_ell` and `Q_ell'` are numerically distinct objects, not a
relabeling. -/
theorem coarseRestrictSite_ne_overNorm_witness :
    coarseRestrictSite AdmissibleSubspace.witnessEll coarseWitnessSiteConfig
        AdmissibleSubspace.witnessY ≠
    coarseRestrictSiteOverNorm AdmissibleSubspace.witnessEll coarseWitnessSiteConfig
        AdmissibleSubspace.witnessY := by
  rw [coarseRestrictSite_witness_value, coarseRestrictSiteOverNorm_witness_value]; norm_num

/-- **D4, the `ell=1`-identity claim, checked to FAIL at `ell=2`** — confirming
`coarseRestrictSite_one_eq_self` genuinely needs `ell=1`: at `ell=2`, `Q_2'` applied to the witness
indicator does NOT return the indicator's own value at `witnessY` (`1/8 ≠ 1`). -/
theorem coarseRestrictSite_two_ne_self_witness :
    coarseRestrictSite AdmissibleSubspace.witnessEll coarseWitnessSiteConfig
        AdmissibleSubspace.witnessY ≠
      coarseWitnessSiteConfig AdmissibleSubspace.witnessY := by
  rw [coarseRestrictSite_witness_value]
  simp only [coarseWitnessSiteConfig, if_pos rfl]
  norm_num

#print axioms coarseWitnessSite_block_sum_eq_one
#print axioms coarseRestrictSite_witness_value
#print axioms coarseRestrictSiteUnderNorm_witness_value
#print axioms coarseRestrictSiteOverNorm_witness_value
#print axioms coarseRestrictSite_ne_underNorm_witness
#print axioms coarseRestrictSite_ne_overNorm_witness
#print axioms coarseRestrictSite_two_ne_self_witness

/-! ## §4. `kernelSubspace` — `N(Q')`, CMP96 (2.7)/(2.10), as a genuine `Submodule` -/

/-- **A single "level"**: a coarse scale `ell` together with the subset `Λ_j` of sites where
`Q_ell'λ` must vanish — CMP96's own per-level data `(ell_j, Λ_j)`. A PLAIN, non-dependent pair
(see the module docstring's disclosed simplification: `Λ'`-membership is data, not a type
constraint here). -/
abbrev Level (L : PeriodicLatticeExtent) := ℕ × Finset (PeriodicLatticeSite L)

/-- **`N(Q')`, CMP96 (2.7)/(2.10), genuinely a function of a FINITE LIST of levels** — faithfully
capturing "λ=0 on Λ₀ [level 0, `ell=1`, `Q_0'=id` by §2] AND `Q_j'λ=0` on `Λ_j` for `j=1,...,k`" as
a `List (Level L)` of arbitrary finite length, each level free to carry its own scale — WITHOUT
inventing the torus/annulus domain-decomposition geometry realizing `Λ_j` as nested regions (that
is `ScaleLadder.lean`'s own scope, a sibling lane's, not this dispatch's). -/
def kernelSubspace {L : PeriodicLatticeExtent} (levels : List (Level L)) :
    Submodule ℝ (PeriodicLatticeSite L → ℝ) where
  carrier := {lam | ∀ lvl ∈ levels, ∀ y ∈ lvl.2, coarseRestrictSite lvl.1 lam y = 0}
  zero_mem' := by
    intro lvl _ y _
    simp [coarseRestrictSite]
  add_mem' := by
    intro lam1 lam2 h1 h2 lvl hlvl y hy
    rw [coarseRestrictSite_add, h1 lvl hlvl y hy, h2 lvl hlvl y hy, add_zero]
  smul_mem' := by
    intro c lam h lvl hlvl y hy
    rw [coarseRestrictSite_smul, h lvl hlvl y hy, mul_zero]

theorem mem_kernelSubspace {L : PeriodicLatticeExtent} {levels : List (Level L)}
    {lam : PeriodicLatticeSite L → ℝ} :
    lam ∈ kernelSubspace levels ↔
      ∀ lvl ∈ levels, ∀ y ∈ lvl.2, coarseRestrictSite lvl.1 lam y = 0 := Iff.rfl

#print axioms mem_kernelSubspace

/-! ## §5. Concrete two-level instantiation on the shared witness lattice, and non-degeneracy -/

/-- **Level 0**: `ell=1` (forced identity, §2), `Λ_0 = {witnessY}` — the SAME site
`AdmissibleSubspace.lean`'s own witness data already anchors (LAW-19 reuse, not a fresh witness). -/
def witnessLevel0 : Level AdmissibleSubspace.witnessL := (1, {AdmissibleSubspace.witnessY})

/-- **Level 1**: `ell = witnessEll = 2`, `Λ_1 = {witnessY}`. -/
def witnessLevel1 : Level AdmissibleSubspace.witnessL :=
  (AdmissibleSubspace.witnessEll, {AdmissibleSubspace.witnessY})

/-- The concrete two-level list this section exercises. -/
def witnessLevels : List (Level AdmissibleSubspace.witnessL) := [witnessLevel0, witnessLevel1]

/-- **Membership on the concrete witness data, unfolded to the two literal conditions** — the
single lemma every later concrete fact in this section is built from. -/
theorem mem_kernelSubspace_witnessLevels_iff
    (lam : PeriodicLatticeSite AdmissibleSubspace.witnessL → ℝ) :
    lam ∈ kernelSubspace witnessLevels ↔
      lam AdmissibleSubspace.witnessY = 0 ∧
      coarseRestrictSite AdmissibleSubspace.witnessEll lam AdmissibleSubspace.witnessY = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h witnessLevel0 (by simp [witnessLevels]) AdmissibleSubspace.witnessY
        (by simp [witnessLevel0])
      simpa only [witnessLevel0, coarseRestrictSite_one_eq_self] using h0
    · exact h witnessLevel1 (by simp [witnessLevels]) AdmissibleSubspace.witnessY
        (by simp [witnessLevel1])
  · rintro ⟨h0, h1⟩ lvl hlvl y hy
    simp only [witnessLevels, List.mem_cons, List.not_mem_nil, or_false] at hlvl
    rcases hlvl with hlvl | hlvl
    · subst hlvl
      simp only [witnessLevel0, Finset.mem_singleton] at hy
      subst hy
      simp only [witnessLevel0, coarseRestrictSite_one_eq_self]
      exact h0
    · subst hlvl
      simp only [witnessLevel1, Finset.mem_singleton] at hy
      subst hy
      exact h1

/-- **General non-triviality**: whenever level `0`'s `Λ_0` is nonempty, the constant-`1` function
fails membership there (`Q_0' 1 = 1 ≠ 0` by the derived identity, §2) — `N(Q')` is genuinely
proper for ANY choice of levels including a nonempty level 0, not merely on the concrete witness. -/
theorem kernelSubspace_ne_top_of_level0_nonempty {L : PeriodicLatticeExtent}
    (levels : List (Level L)) (lvl0 : Level L) (hlvl0 : lvl0 ∈ levels) (hell0 : lvl0.1 = 1)
    (hne : lvl0.2.Nonempty) : kernelSubspace levels ≠ ⊤ := by
  intro htop
  obtain ⟨y, hy⟩ := hne
  have hmem : (fun _ : PeriodicLatticeSite L => (1 : ℝ)) ∈ kernelSubspace levels :=
    htop ▸ Submodule.mem_top
  have h0 := (mem_kernelSubspace).mp hmem lvl0 hlvl0 y hy
  rw [hell0, coarseRestrictSite_one_eq_self] at h0
  norm_num at h0

theorem witness_kernelSubspace_ne_top : kernelSubspace witnessLevels ≠ ⊤ :=
  kernelSubspace_ne_top_of_level0_nonempty witnessLevels witnessLevel0
    (by simp [witnessLevels]) rfl (by simp [witnessLevel0])

/-- **Two distinct sites inside `blockOf witnessY witnessEll`, both `≠ witnessY`**, used to build a
genuine nonzero member of `kernelSubspace witnessLevels` below (a "difference" configuration:
`+1`/`-1` at two DIFFERENT non-`witnessY` block members, summing to `0` on average, and `0` at
`witnessY` itself, so BOTH level conditions hold while the function is not identically zero). -/
def kernelWitnessSiteA : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
  fun μ => if μ.val = 0 then 1 else 0

def kernelWitnessSiteB : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
  fun μ => if μ.val = 1 then 1 else 0

theorem kernelWitnessSiteA_mem_block :
    kernelWitnessSiteA ∈
      AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll := by
  decide

theorem kernelWitnessSiteB_mem_block :
    kernelWitnessSiteB ∈
      AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll := by
  decide

theorem kernelWitnessSiteA_ne_witnessY : kernelWitnessSiteA ≠ AdmissibleSubspace.witnessY := by
  decide

theorem kernelWitnessSiteA_ne_B : kernelWitnessSiteA ≠ kernelWitnessSiteB := by
  decide

theorem kernelWitnessSiteB_ne_witnessY : kernelWitnessSiteB ≠ AdmissibleSubspace.witnessY := by
  decide

/-- **The nonzero witness configuration**: `+1` at `kernelWitnessSiteA`, `-1` at
`kernelWitnessSiteB`, `0` elsewhere (including at `witnessY`). -/
noncomputable def kernelWitnessLam : PeriodicLatticeSite AdmissibleSubspace.witnessL → ℝ :=
  fun x => if x = kernelWitnessSiteA then 1 else if x = kernelWitnessSiteB then -1 else 0

theorem kernelWitnessLam_at_A : kernelWitnessLam kernelWitnessSiteA = 1 := by
  unfold kernelWitnessLam
  rw [if_pos rfl]

theorem kernelWitnessLam_at_B : kernelWitnessLam kernelWitnessSiteB = -1 := by
  unfold kernelWitnessLam
  rw [if_neg (Ne.symm kernelWitnessSiteA_ne_B), if_pos rfl]

theorem kernelWitnessLam_at_witnessY : kernelWitnessLam AdmissibleSubspace.witnessY = 0 := by
  unfold kernelWitnessLam
  rw [if_neg (Ne.symm kernelWitnessSiteA_ne_witnessY), if_neg (Ne.symm kernelWitnessSiteB_ne_witnessY)]

theorem kernelWitnessLam_ne_zero : kernelWitnessLam ≠ 0 := by
  intro h
  have := congrFun h kernelWitnessSiteA
  rw [kernelWitnessLam_at_A] at this
  norm_num at this

/-- The block-sum of `kernelWitnessLam` over `blockOf witnessY witnessEll` is `0`
(`+1` and `-1` at the two distinct block members, cancelling exactly). -/
theorem kernelWitnessLam_block_sum_eq_zero :
    (∑ x ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll,
      kernelWitnessLam x) = 0 := by
  rw [← Finset.insert_erase kernelWitnessSiteA_mem_block,
    Finset.sum_insert (Finset.notMem_erase _ _)]
  have hBmem : kernelWitnessSiteB ∈
      (AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll).erase
        kernelWitnessSiteA :=
    Finset.mem_erase.mpr ⟨kernelWitnessSiteA_ne_B.symm, kernelWitnessSiteB_mem_block⟩
  rw [← Finset.insert_erase hBmem, Finset.sum_insert (Finset.notMem_erase _ _)]
  have hrest : ∀ x ∈ ((AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll).erase kernelWitnessSiteA).erase kernelWitnessSiteB,
      kernelWitnessLam x = 0 := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxB, hxA, -⟩ := hx
    simp only [kernelWitnessLam, if_neg hxA, if_neg hxB]
  rw [Finset.sum_eq_zero hrest, kernelWitnessLam_at_A, kernelWitnessLam_at_B]
  ring

theorem kernelWitnessLam_mem : kernelWitnessLam ∈ kernelSubspace witnessLevels := by
  rw [mem_kernelSubspace_witnessLevels_iff]
  refine ⟨kernelWitnessLam_at_witnessY, ?_⟩
  simp only [coarseRestrictSite]
  rw [kernelWitnessLam_block_sum_eq_zero]
  ring

/-- **Concrete non-vacuity**: `kernelSubspace witnessLevels ≠ ⊥`. -/
theorem witness_kernelSubspace_ne_bot : kernelSubspace witnessLevels ≠ ⊥ := by
  intro hbot
  have hmem := kernelWitnessLam_mem
  rw [hbot, Submodule.mem_bot] at hmem
  exact kernelWitnessLam_ne_zero hmem

#print axioms mem_kernelSubspace_witnessLevels_iff
#print axioms kernelSubspace_ne_top_of_level0_nonempty
#print axioms witness_kernelSubspace_ne_top
#print axioms kernelWitnessLam_block_sum_eq_zero
#print axioms kernelWitnessLam_mem
#print axioms witness_kernelSubspace_ne_bot

/-! ## §6. `kernelSubspaceH` — transported into the genuine Hilbert space (mirrors
`RGLinearization.lean`'s own `admissibleSubspaceH` transport pattern, LAW-19) -/

/-- **`N(Q')`, transported into `LatticeOperators.SiteSpace L`** — the SAME subspace, now living
in the Hilbert space `Δ₀`'s positivity/adjoint machinery is built on. -/
noncomputable def kernelSubspaceH {L : PeriodicLatticeExtent} (levels : List (Level L)) :
    Submodule ℝ (AdalyFormal.Balaban.LatticeOperators.SiteSpace L) :=
  (kernelSubspace levels).map
    (AdalyFormal.Balaban.LatticeOperators.siteEquiv L).symm.toLinearMap

theorem mem_kernelSubspaceH {L : PeriodicLatticeExtent} {levels : List (Level L)}
    {v : AdalyFormal.Balaban.LatticeOperators.SiteSpace L} :
    v ∈ kernelSubspaceH levels ↔
      AdalyFormal.Balaban.LatticeOperators.siteEquiv L v ∈ kernelSubspace levels := by
  unfold kernelSubspaceH
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨lam, hlam, hEq⟩
    have heq2 : (AdalyFormal.Balaban.LatticeOperators.siteEquiv L).symm lam = v := hEq
    rw [← heq2]
    simpa using hlam
  · intro hv
    exact ⟨AdalyFormal.Balaban.LatticeOperators.siteEquiv L v, hv, by simp⟩

#print axioms mem_kernelSubspaceH

/-! ## §7. Positivity of `Δ₀ := LatticeOperators.siteLaplacianCLM` on `kernelSubspaceH`, GIVEN the
mesh-uniform discrete Poincaré fact as an EXPLICIT HYPOTHESIS (never proved here, never an axiom,
never a `sorry` — CMP96 p.225's own stated consequence, "positive... hence invertible") -/

/-- **Positivity, given the Poincaré bound as an explicit parameter.** `c` is the mesh-uniform
constant CMP96 (2.11) states (citing CMP89 (2.26)/(2.27), a sibling lane's own open target); `hbound`
IS that inequality, supplied as a hypothesis, not derived. Everything downstream is a genuine proof. -/
theorem positive_of_poincare {L : PeriodicLatticeExtent} (levels : List (Level L))
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ v : AdalyFormal.Balaban.LatticeOperators.SiteSpace L, v ∈ kernelSubspaceH levels →
      c * ‖v‖ ^ 2 ≤
        (inner ℝ v (AdalyFormal.Balaban.LatticeOperators.siteLaplacianCLM L v) : ℝ))
    (v : AdalyFormal.Balaban.LatticeOperators.SiteSpace L) (hv : v ∈ kernelSubspaceH levels)
    (hv0 : v ≠ 0) :
    0 < (inner ℝ v (AdalyFormal.Balaban.LatticeOperators.siteLaplacianCLM L v) : ℝ) := by
  have h1 := hbound v hv
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have h2 : 0 < c * ‖v‖ ^ 2 := by positivity
  exact lt_of_lt_of_le h2 h1

/-- **`Δ₀` is injective on `kernelSubspaceH`, hence "invertible on this subspace"** (CMP96 p.225's
own stated consequence of positivity) — a direct corollary of `positive_of_poincare`, by
contraposition. -/
theorem eq_zero_of_laplacian_eq_zero_of_poincare {L : PeriodicLatticeExtent}
    (levels : List (Level L)) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ v : AdalyFormal.Balaban.LatticeOperators.SiteSpace L, v ∈ kernelSubspaceH levels →
      c * ‖v‖ ^ 2 ≤
        (inner ℝ v (AdalyFormal.Balaban.LatticeOperators.siteLaplacianCLM L v) : ℝ))
    (v : AdalyFormal.Balaban.LatticeOperators.SiteSpace L) (hv : v ∈ kernelSubspaceH levels)
    (hzero : AdalyFormal.Balaban.LatticeOperators.siteLaplacianCLM L v = 0) : v = 0 := by
  by_contra hne
  have hpos := positive_of_poincare levels c hc hbound v hv hne
  rw [hzero, inner_zero_right] at hpos
  exact absurd hpos (lt_irrefl 0)

#print axioms positive_of_poincare
#print axioms eq_zero_of_laplacian_eq_zero_of_poincare

/-! ## §7b. D4: `Δ₀` is NOT globally positive — confirming the `kernelSubspaceH` restriction in
`hbound`'s hypothesis is genuinely load-bearing, not decorative. The constant function is a
concrete NONZERO vector with `⟨v,Δ₀v⟩ = 0` on ALL of `SiteSpace L` — matching CMP89's own stated
fact that constants are `−Δ`'s eigenvectors for eigenvalue `0`. -/

/-- The constant-`c` function, as an element of `SiteSpace L`. -/
noncomputable def constSite (L : PeriodicLatticeExtent) (c : ℝ) :
    AdalyFormal.Balaban.LatticeOperators.SiteSpace L :=
  (AdalyFormal.Balaban.LatticeOperators.siteEquiv L).symm (fun _ => c)

theorem siteEquiv_constSite (c : ℝ) :
    AdalyFormal.Balaban.LatticeOperators.siteEquiv L (constSite L c) = fun _ => c := by
  simp [constSite]

theorem gradValue_const (c : ℝ) (b : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) :
    AdalyFormal.Balaban.LatticeOperators.gradValue (fun _ : PeriodicLatticeSite L => c) b = 0 := by
  simp [AdalyFormal.Balaban.LatticeOperators.gradValue]

theorem gradCLM_constSite_eq_zero (c : ℝ) :
    AdalyFormal.Balaban.LatticeOperators.gradCLM L (constSite L c) = 0 := by
  apply (AdalyFormal.Balaban.LatticeOperators.bondEquiv L).injective
  rw [AdalyFormal.Balaban.LatticeOperators.gradCLM_apply, siteEquiv_constSite, map_zero]
  funext b
  exact gradValue_const c b

theorem siteLaplacian_constSite_eq_zero (c : ℝ) :
    AdalyFormal.Balaban.LatticeOperators.siteLaplacianCLM L (constSite L c) = 0 := by
  unfold AdalyFormal.Balaban.LatticeOperators.siteLaplacianCLM
  simp [gradCLM_constSite_eq_zero]

theorem constSite_witness_ne_zero : constSite AdmissibleSubspace.witnessL (1 : ℝ) ≠ 0 := by
  intro h
  have hc := congrArg (AdalyFormal.Balaban.LatticeOperators.siteEquiv AdmissibleSubspace.witnessL) h
  rw [siteEquiv_constSite, map_zero] at hc
  have hc2 := congrFun hc AdmissibleSubspace.witnessY
  norm_num at hc2

/-- **THE D4 CHECK**: the constant function `1` is a NONZERO vector on which `⟨v,Δ₀v⟩` is `0`, not
positive — `Δ₀` is genuinely NOT globally positive-definite; the `kernelSubspaceH` membership
hypothesis in `positive_of_poincare`/`hbound` is load-bearing, exactly matching CMP89's own stated
fact ("`−Δ` bounded below by `π²` on functions ORTHOGONAL TO CONSTANTS, which are its eigenvectors
for eigenvalue `0`"). -/
theorem constSite_witness_laplacian_not_positive :
    ¬ (0 <
      (inner ℝ (constSite AdmissibleSubspace.witnessL (1:ℝ))
        (AdalyFormal.Balaban.LatticeOperators.siteLaplacianCLM AdmissibleSubspace.witnessL
          (constSite AdmissibleSubspace.witnessL (1:ℝ))) : ℝ)) := by
  rw [siteLaplacian_constSite_eq_zero, inner_zero_right]
  exact lt_irrefl 0

#print axioms gradValue_const
#print axioms gradCLM_constSite_eq_zero
#print axioms siteLaplacian_constSite_eq_zero
#print axioms constSite_witness_ne_zero
#print axioms constSite_witness_laplacian_not_positive

/-! ## §8. `Q'*aQ'` vanishes on `N(Q')` — CMP96 (2.14), CONFIRMED provable NOW (bridge reading §4) -/

/-- **`⟨λ,Q'*aQ'λ⟩`, CMP96 (2.14)**, as a function of an arbitrary FINITE list of levels and a
per-level coefficient `coeff : ℕ → ℝ` (indexed by the level's own scale `ell_j`, a disclosed,
honest simplification of CMP96's `a_j(L^jη)^{d-2}` — the per-level SCALAR weight, since this
module does not build the lattice-spacing bookkeeping `(L^jη)^{d-2}` itself, out of scope; the
vanishing mechanism below is unaffected by what the coefficient's numeric VALUE is, only that it
multiplies a squared term). -/
noncomputable def qFormQstarAQ {L : PeriodicLatticeExtent} (levels : List (Level L))
    (coeff : ℕ → ℝ) (lam : PeriodicLatticeSite L → ℝ) : ℝ :=
  (levels.map (fun lvl => ∑ y ∈ lvl.2, coeff lvl.1 * (coarseRestrictSite lvl.1 lam y) ^ 2)).sum

/-- **THE THEOREM the mandate names as "genuinely provable now"**: `⟨λ,Q'*aQ'λ⟩ = 0` for every
`λ ∈ N(Q')` — CMP96's own extra-term-vanishing mechanism (bridge reading §4, "BRIDGE CONFIRMED"),
by direct substitution from the defining membership condition, for ANY finite level list and ANY
coefficient function (the mechanism is coefficient-agnostic, matching the source: it is the SQUARED
`Q_j'λ` term that vanishes, independent of what multiplies it). -/
theorem qFormQstarAQ_eq_zero_of_mem_kernelSubspace {L : PeriodicLatticeExtent}
    (levels : List (Level L)) (coeff : ℕ → ℝ) (lam : PeriodicLatticeSite L → ℝ)
    (hlam : lam ∈ kernelSubspace levels) :
    qFormQstarAQ levels coeff lam = 0 := by
  unfold qFormQstarAQ
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨lvl, hlvl, rfl⟩ := List.mem_map.mp hx
  apply Finset.sum_eq_zero
  intro y hy
  rw [(mem_kernelSubspace).mp hlam lvl hlvl y hy]
  ring

/-- **Concrete instantiation on the witness levels**: `⟨λ,Q'*aQ'λ⟩ = 0` for the concrete
`kernelWitnessLam` built in §5, with an arbitrary coefficient function (e.g. `fun _ => 1`). -/
theorem witness_qFormQstarAQ_eq_zero :
    qFormQstarAQ witnessLevels (fun _ => 1) kernelWitnessLam = 0 :=
  qFormQstarAQ_eq_zero_of_mem_kernelSubspace witnessLevels (fun _ => 1) kernelWitnessLam
    kernelWitnessLam_mem

#print axioms qFormQstarAQ_eq_zero_of_mem_kernelSubspace
#print axioms witness_qFormQstarAQ_eq_zero

/-! ## §8b. D4, QUANTIFIER-WEAKENING (S83 style): dropping level 0 from `∀ lvl ∈ levels` to
"level 1 only" admits an element the true `N(Q')` excludes, for which the quadratic form is
NONZERO — the `∀`, not merely `∃` or "the top level," is load-bearing. -/

/-- **The GARBAGE membership predicate**: satisfies ONLY level 1's condition (average zero over
the coarse block), dropping level 0's (`λ(witnessY)=0`) entirely — the exact quantifier-weakening
`∀ lvl ∈ levels` → "one particular `lvl`" that §LEAN-D/S83 warns is a silent, coherent-looking
defect class. -/
def weakKernelPredicate (lam : PeriodicLatticeSite AdmissibleSubspace.witnessL → ℝ) : Prop :=
  coarseRestrictSite AdmissibleSubspace.witnessEll lam AdmissibleSubspace.witnessY = 0

/-- **The D4 witness**: `λ(witnessY) = 1`, `λ(kernelWitnessSiteA) = -1`, else `0` — satisfies
level 1 (average over the block is `1 + -1 = 0`, divided by `8`) but VIOLATES level 0
(`λ(witnessY) = 1 ≠ 0`). -/
noncomputable def weakWitnessLam : PeriodicLatticeSite AdmissibleSubspace.witnessL → ℝ :=
  fun x => if x = AdmissibleSubspace.witnessY then 1
    else if x = kernelWitnessSiteA then -1 else 0

theorem weakWitnessLam_at_witnessY : weakWitnessLam AdmissibleSubspace.witnessY = 1 := by
  unfold weakWitnessLam
  rw [if_pos rfl]

theorem weakWitnessLam_at_A : weakWitnessLam kernelWitnessSiteA = -1 := by
  unfold weakWitnessLam
  rw [if_neg kernelWitnessSiteA_ne_witnessY, if_pos rfl]

theorem weakWitnessLam_block_sum_eq_zero :
    (∑ x ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll,
      weakWitnessLam x) = 0 := by
  rw [← Finset.insert_erase witnessY_mem_own_block, Finset.sum_insert (Finset.notMem_erase _ _)]
  have hAmem : kernelWitnessSiteA ∈
      (AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
        AdmissibleSubspace.witnessEll).erase AdmissibleSubspace.witnessY :=
    Finset.mem_erase.mpr ⟨kernelWitnessSiteA_ne_witnessY, kernelWitnessSiteA_mem_block⟩
  rw [← Finset.insert_erase hAmem, Finset.sum_insert (Finset.notMem_erase _ _)]
  have hrest : ∀ x ∈ ((AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll).erase AdmissibleSubspace.witnessY).erase
      kernelWitnessSiteA, weakWitnessLam x = 0 := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxA, hxY, -⟩ := hx
    simp only [weakWitnessLam, if_neg hxY, if_neg hxA]
  rw [Finset.sum_eq_zero hrest, weakWitnessLam_at_witnessY, weakWitnessLam_at_A]
  ring

/-- **`weakWitnessLam` satisfies the WEAK (garbage) predicate**. -/
theorem weakWitnessLam_satisfies_weak : weakKernelPredicate weakWitnessLam := by
  unfold weakKernelPredicate coarseRestrictSite
  rw [weakWitnessLam_block_sum_eq_zero]
  ring

/-- **...but `weakWitnessLam` is NOT a member of the TRUE `kernelSubspace witnessLevels`** (it fails
level 0). -/
theorem weakWitnessLam_not_mem_kernelSubspace :
    weakWitnessLam ∉ kernelSubspace witnessLevels := by
  rw [mem_kernelSubspace_witnessLevels_iff]
  rintro ⟨h0, -⟩
  rw [weakWitnessLam_at_witnessY] at h0
  norm_num at h0

/-- **THE D4 VERDICT**: on this garbage-predicate-satisfying element, the quadratic form
`qFormQstarAQ` (computed over the FULL, correct two-level list) is NONZERO — the level-0 term
contributes `1 · (λ(witnessY))² = 1` while level 1's contributes `0`. The vanishing theorem (§8)
genuinely needs membership in the TRUE `∀`-quantified `kernelSubspace`, not merely the weakened
single-level predicate. -/
theorem weakWitnessLam_qForm_ne_zero :
    qFormQstarAQ witnessLevels (fun _ => 1) weakWitnessLam ≠ 0 := by
  unfold qFormQstarAQ witnessLevels witnessLevel0 witnessLevel1
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Finset.sum_singleton]
  rw [coarseRestrictSite_one_eq_self, weakWitnessLam_at_witnessY]
  unfold coarseRestrictSite
  rw [weakWitnessLam_block_sum_eq_zero]
  norm_num

#print axioms weakWitnessLam_block_sum_eq_zero
#print axioms weakWitnessLam_satisfies_weak
#print axioms weakWitnessLam_not_mem_kernelSubspace
#print axioms weakWitnessLam_qForm_ne_zero

end AdalyFormal.Balaban.KernelSubspace
