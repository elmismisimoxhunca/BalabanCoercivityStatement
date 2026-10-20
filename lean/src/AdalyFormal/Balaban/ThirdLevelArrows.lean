/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.ThirdLevelStokes

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `ThirdLevelArrows.lean` — the genuine UNIT → COARSE arrow, and `[Q-SEMIGROUP]` closed at `U = 1`

## The three levels, as three TYPES

`[CSTAR-LEVEL-MISMATCH]` happened because one Lean map played two roles. `CStarLevelCorrected`'s
`LevelSplit` fixed the ROLE bookkeeping (two block sides that cannot coincide); this module builds
the missing ARROW, so that the two roles have two different TYPES and the collapse becomes a type
error rather than a discipline:

| arrow | domain | codomain | Lean object |
|---|---|---|---|
| `Q` (fine → unit, the Schur fibre of (3.159)) | `Bond L → SuTwo` | `CoarseBond L ℓ₀ → SuTwo` | `lineCoarseRestrictCovLM U ℓ₀` |
| `Q₁` (unit → coarse, the (3.157)/(3.155) constraint) | `CoarseBond L ℓ₀ → SuTwo` | `CoarseBond L (ℓ₀·m) → SuTwo` | **`unitToCoarseLM ℓ₀ m` (NEW)** |

Applying `unitToCoarseLM` to a fine field, or `lineCoarseRestrictCovLM` in the `Q₁` slot, is now
ill-typed. This is the q1-adjudication's "same map TEMPLATE, two different ARROWS"
(`compute/q1_adjudication/RULING.md`) realized in the type system: `unitToCoarse` is the SAME
one-step block-line-average template, instantiated one level up — averaging over the `m³` unit
sites of an `ℓ₁`-block, line-integrating over `m` consecutive UNIT bonds (each a step of `ℓ₀`
fine steps), with the same true-average normalization `1/m⁴`.

## `[Q-SEMIGROUP]` — the tower law, CLOSED at `U = 1`

`CStarLevelCorrected` §6 named `[Q-SEMIGROUP]` (`Q₁ ∘ Q_{ℓ₀} = Q_{ℓ₀·m}` — Bałaban's
`Q_j(U) = Q(Ū^{j−1})⋯Q(U)`, p.393 (3.15)) as the identification debt of the block-side-indexed
presentation, and §7 checked only its 1-D coefficient core (`tower_coeff_L2/L3`, by `decide`).
**`tower_law` below proves the full three-dimensional operator identity at `U = 1`**:

  `unitToCoarse ℓ₀ m (Q_{ℓ₀} v) = Q_{ℓ₀·m} v`   for every `v`, every compatible torus
  (`0 < ℓ₀`, `0 < m`, `∀ μ, ℓ₀ ∣ L μ + 1`).

Mechanism: the `ℓ₁`-block partitions into `m³` unit-owned `ℓ₀`-blocks
(`blockOf_eq_biUnion_units`, via `coarseLattice_exists/unique` — LAW-19), each `i`-th unit step
shifts an `ℓ₀`-block to an `ℓ₀`-block (`shift_mul_blockOf`, iterating
`coarseShift_blockOf_eq_image`), and the fine offset decomposes uniquely as `k = i·ℓ₀ + j`
(`sum_range_mul_decomp`). The normalizations compose exactly: `(1/m⁴)·(1/ℓ₀⁴) = 1/(ℓ₀m)⁴`.

What it buys, per `CStarLevelCorrected` §6: the translation
`v ∈ ker Q_{ℓ₁} ⟺ Q_{ℓ₀} v ∈ ker Q₁` (`ker_translation` below) — i.e. the pulled-back
constraint of the corrected typing really is "the unit field `B = Q_{ℓ₀}v` lies in `ker Q₁`", as
(3.156) demands. The witness `B7` of `ThirdLevelWitness` thereby genuinely certifies the
unit-level constraint, not merely its fine-level pullback.

## HONEST SCOPE

* `U = 1` only. The covariant tower law is `[Q-TRANSPORT-COMPOSE]` (the transports must compose
  along the two-step path — the same curvature question as `[STOKES-COMM-U]`,
  `CovariantOperators.witness_curvature_ne_zero` the obstruction). `unitToCoarse` as defined
  carries no transport, so it IS the `U = 1` (and abelian-sector) arrow; the covariant arrow
  needs the unit-lattice transports and is not built here.

  **[UPDATED 2026-07-28, then WALKED BACK the same night — read the walk-back at the end of this
  bullet before using any of it.]** The covariant arrow HAS been built
  (`Balaban.TowerLawCovariant.unitToCoarseCov`), and the update below asserted that the law it was
  built to satisfy is FALSE.
  `Balaban.TowerLawCovariant.unitToCoarseCov` is that arrow, and `tower_law_cov_refuted` proves
  that for an explicit curved background at the split `(ℓ₀,ℓ₁) = (2,4)`, **NO** unit-level
  background `V` makes the exact operator identity hold —
  `tower_law_cov_refuted_at_blockedGauge` instantiating it at Bałaban's own `Ū` for EVERY
  `LogExpAd`, so it is not waiting on a better blocked field. The must-not-fire control holds: at
  `V = 1` the covariant arrow IS `unitToCoarse` and the law IS this file's `tower_law`
  (`tower_law_cov_at_trivial`), so the refutation does not contradict what is proved here — it
  bounds how far it can be pushed.

  **Two qualifications, both live.** (i) The refutation's mechanism runs through
  `transportCompose_forces_contourSplit`: the law forces the staircase contour to be ADDITIVE
  under block splitting, and it is not. That is stated over `BlockedGaugeCore.contourFamily`,
  whose forward-only convention has NOT been proved equivalent to CMP109 p.252's printed SIGNED
  prescription (see the fidelity note on `contourSteps`). Whether the refutation is a fact about
  the geometry or about our path convention is UNDER PROSECUTION. (ii) The survivor is the
  error-carrying form `tower_law_cov_error_alpha`, `‖LHS − RHS‖ ≤ N·2α₁·Kv`, exact at `α₁ = 0`
  and NOT proved `k`-uniform.

  **THE WALK-BACK (same night, second-family prosecution + main loop).** "Resolved negatively" is
  NOT the status. A Sol prosecution convicted the refutation on OBJECT IDENTITY — CMP99b p.393
  (3.15) defines `Q_j(U)` as the COMPOSITION of one-step operators, and CMP98 pp.29-30 build the
  higher-order contour RECURSIVELY through block corners, not as the fresh one-shot large-scale
  staircase the refutation's right-hand side uses. Separately, `unitToCoarseCov` implements only
  the first of CMP98 (124)'s five terms.

  The prosecution's own compiled claim that the tower law HOLDS under the recursive contour is a
  TAUTOLOGY — the main loop diffed its transport against the refutation's `lhsTransport` and found
  them byte-identical, so the theorem says `LHS = LHS`. It does not establish the converse.

  **SETTLED later the same night by a third-family (Kimi) source adjudication, blind:** CMP99b
  p.393 (3.15) DEFINES `Q_j(U)` as the composition, no proof verb; the only one-shot large-block
  formula there is (3.19), for the PRIMED operator alone, whose kernel is itself defined by the
  same corner-by-corner product. **The tower law is a DEFINITION — there is no independent
  one-shot object to compare against, and a definition cannot be refuted.**
  `tower_law_cov_refuted` is sound mathematics about an identity WE constructed, not one Bałaban
  asserts. The `k` half must therefore be attacked at the composite DIRECTLY (the error-carrying
  form), not through an identity. Open residual O1: CMP98 (52),(53) — the primary definition both
  (3.19) and (3.55) defer to — was not in the evidence set.

  Status of `[Q-TRANSPORT-COMPOSE]` was, in order: "open" (original), "false" (my overreach),
  "CANNOT-DETERMINE" (walk-back), and now **DEFINITIONAL**. Recording the sequence because the
  middle two were wrong and a reader should see how the object came into focus, not just where it
  landed. What IS established is that this tree's
  stated tower law may not be the source's statement. `Balaban/TowerLawCovariant.lean` §9 carries
  the full account. The error-carrying form remains the surviving target in every reading, and
  remains not proved `k`-uniform.
* Compatible torus (`ℓ₀ ∣ L μ + 1`) throughout — the standing `blockOf` scope. Note the tower
  law does NOT need `ℓ₁ ∣ L μ + 1`: the partition argument is val-interval arithmetic and the
  unit-step shifts move by `ℓ₀`-multiples only.
-/

namespace AdalyFormal.Balaban.ThirdLevelArrows

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice
  periodicLatticeShift_injective)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_blockOf_eq_image coarseShift_injective)
open AdalyFormal.Balaban.Q1Real (rZeroA_trivialU)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the unit sites of a coarse block, and the arrow -/

/-- The unit (`ℓ₀`-coarse) sites lying in the `ℓ₁`-block of `y`. -/
def unitSitesOf (ell₀ ell₁ : ℕ) (y : PeriodicLatticeSite L) :
    Finset {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell₀} :=
  Finset.univ.filter (fun u => u.1 ∈ blockOf y ell₁)

/-- **THE UNIT → COARSE ARROW `Q₁`.** The one-step block-line average, one level up: for a
coarse bond `c` at level `ℓ₀·m`, average the unit bond field `B` over the `m³` unit sites of the
`ℓ₁`-block, line-integrating over `m` consecutive unit bonds in direction `c.2` (each unit step
= `ℓ₀` fine steps), normalized `1/m⁴` (the true average, `η^{d+1}` at the unit lattice's own
scale). The `dite` supplies the `CoarseLattice` membership of the stepped site; on the
compatible torus it always holds (`pathSite_mul_coarse`), and off it the term is `0`. -/
noncomputable def unitToCoarse (ell₀ m : ℕ) (B : CoarseBond L ell₀ → SuTwo)
    (c : CoarseBond L (ell₀ * m)) : SuTwo :=
  (1 / (m : ℝ) ^ 4) • ∑ u ∈ unitSitesOf ell₀ (ell₀ * m) c.1.1,
    ∑ i ∈ Finset.range m,
      if h : pathSite u.1 c.2 (i * ell₀) ∈ CoarseLattice L ell₀ then
        B (⟨pathSite u.1 c.2 (i * ell₀), h⟩, c.2)
      else 0

theorem unitToCoarse_add (ell₀ m : ℕ) (B1 B2 : CoarseBond L ell₀ → SuTwo)
    (c : CoarseBond L (ell₀ * m)) :
    unitToCoarse ell₀ m (B1 + B2) c = unitToCoarse ell₀ m B1 c + unitToCoarse ell₀ m B2 c := by
  unfold unitToCoarse
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : pathSite u.1 c.2 (i * ell₀) ∈ CoarseLattice L ell₀
  · rw [dif_pos h, dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

theorem unitToCoarse_smul (ell₀ m : ℕ) (r : ℝ) (B : CoarseBond L ell₀ → SuTwo)
    (c : CoarseBond L (ell₀ * m)) :
    unitToCoarse ell₀ m (r • B) c = r • unitToCoarse ell₀ m B c := by
  unfold unitToCoarse
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : pathSite u.1 c.2 (i * ell₀) ∈ CoarseLattice L ell₀
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h, smul_zero]

/-- The arrow as a `LinearMap` — the type-level realization of the two-arrow table: its DOMAIN is
the unit-bond fields, so handing it a fine field (or handing `lineCoarseRestrictCovLM` a unit
field) is a type error. The collapse of `[CSTAR-LEVEL-MISMATCH]` is now unstateable at the arrow
level, not merely at the block-side bookkeeping level. -/
noncomputable def unitToCoarseLM (ell₀ m : ℕ) :
    (CoarseBond L ell₀ → SuTwo) →ₗ[ℝ] (CoarseBond L (ell₀ * m) → SuTwo) where
  toFun B := unitToCoarse ell₀ m B
  map_add' B1 B2 := funext fun c => unitToCoarse_add ell₀ m B1 B2 c
  map_smul' r B := funext fun c => unitToCoarse_smul ell₀ m r B c

#print axioms unitToCoarse_add
#print axioms unitToCoarse_smul

/-! ## §2 — geometry: unit steps, shifted blocks, and the block partition -/

/-- One unit step is `ℓ₀` fine steps: the successor decomposition. -/
theorem pathSite_succ_mul (u : PeriodicLatticeSite L) (μ : Fin 3) (i ell₀ : ℕ) :
    pathSite u μ ((i + 1) * ell₀) = coarseShift (pathSite u μ (i * ell₀)) ell₀ μ := by
  show (fun z => periodicLatticeShift z μ)^[(i + 1) * ell₀] u = _
  rw [show (i + 1) * ell₀ = ell₀ + i * ell₀ by ring, Function.iterate_add_apply]
  rfl

/-- Unit steps stay on the unit lattice (compatible torus). -/
theorem pathSite_mul_coarse (ell₀ : ℕ) (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
    {u : PeriodicLatticeSite L} (hu : u ∈ CoarseLattice L ell₀) (μ : Fin 3) :
    ∀ i : ℕ, pathSite u μ (i * ell₀) ∈ CoarseLattice L ell₀ := by
  intro i
  induction i with
  | zero =>
    rw [Nat.zero_mul, pathSite_zero]
    exact hu
  | succ n ih =>
    rw [pathSite_succ_mul]
    exact coarseShift_mem_coarseLattice hdvd₀ ih μ

/-- The `i`-th unit step maps the `ℓ₀`-block to the `ℓ₀`-block of the stepped base — iterated
`coarseShift_blockOf_eq_image`. -/
theorem shift_mul_blockOf {ell₀ : ℕ} (hell₀ : 0 < ell₀)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
    {u : PeriodicLatticeSite L} (hu : u ∈ CoarseLattice L ell₀) (μ : Fin 3) :
    ∀ i : ℕ, blockOf (pathSite u μ (i * ell₀)) ell₀
      = (blockOf u ell₀).image (fun x => pathSite x μ (i * ell₀)) := by
  intro i
  induction i with
  | zero =>
    rw [Nat.zero_mul, pathSite_zero]
    have hid : (fun x : PeriodicLatticeSite L => pathSite x μ 0) = fun x => x := by
      funext x
      rw [pathSite_zero]
    rw [hid, Finset.image_id']
  | succ n ih =>
    rw [pathSite_succ_mul,
      coarseShift_blockOf_eq_image hell₀ (hdvd₀ μ) (pathSite_mul_coarse ell₀ hdvd₀ hu μ n), ih,
      Finset.image_image]
    congr 1
    funext x
    show coarseShift (pathSite x μ (n * ell₀)) ell₀ μ = _
    rw [← pathSite_succ_mul]

#print axioms pathSite_mul_coarse
#print axioms shift_mul_blockOf

/-- Two multiples of `e` cannot be strictly closer than `e`. -/
theorem mult_add_le {a b e : ℕ} (ha : e ∣ a) (hb : e ∣ b) (h : a < b) : a + e ≤ b := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp at h
    · exact he
  have hpq : p < q := Nat.lt_of_mul_lt_mul_left (a := e) h
  calc e * p + e = e * (p + 1) := by ring
    _ ≤ e * q := Nat.mul_le_mul_left e hpq

/-- **The `ℓ₁`-block PARTITIONS into unit-owned `ℓ₀`-blocks.** -/
theorem blockOf_eq_biUnion_units {ell₀ ell₁ : ℕ} (hell₀ : 0 < ell₀) (hsplit : ell₀ ∣ ell₁)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell₁) :
    blockOf y ell₁ = (unitSitesOf ell₀ ell₁ y).biUnion (fun u => blockOf u.1 ell₀) := by
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · intro hx
    obtain ⟨u, hu, hxu⟩ := coarseLattice_exists ell₀ hell₀ hdvd₀ x
    have hub : u ∈ blockOf y ell₁ := by
      rw [mem_blockOf] at hx hxu ⊢
      intro ρ
      have hyρ : ell₀ ∣ (y ρ).val :=
        dvd_trans hsplit (Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy ρ))
      have huρ : ell₀ ∣ (u ρ).val := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hu ρ)
      constructor
      · -- `y ρ ≤ u ρ`: otherwise `u ρ + ℓ₀ ≤ y ρ ≤ x ρ`, contradicting `x ρ < u ρ + ℓ₀`
        by_contra hlt
        rw [not_le] at hlt
        have hstep := mult_add_le huρ hyρ hlt
        have h1 := (hx ρ).1
        have h2 := (hxu ρ).2
        omega
      · -- `u ρ < y ρ + ℓ₁`: through `u ρ ≤ x ρ < y ρ + ℓ₁`
        have h1 := (hxu ρ).1
        have h2 := (hx ρ).2
        omega
    exact ⟨⟨u, hu⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hub⟩, hxu⟩
  · rintro ⟨u, hu, hxu⟩
    have huB := (Finset.mem_filter.mp hu).2
    rw [mem_blockOf] at hxu huB ⊢
    intro ρ
    have hyρ : ell₀ ∣ (y ρ).val :=
      dvd_trans hsplit (Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy ρ))
    have huρ : ell₀ ∣ (u.1 ρ).val := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp u.2 ρ)
    have hsum : ell₀ ∣ ((y ρ).val + ell₁) := Nat.dvd_add hyρ hsplit
    constructor
    · have h1 := (huB ρ).1
      have h2 := (hxu ρ).1
      omega
    · -- `x ρ < u ρ + ℓ₀ ≤ y ρ + ℓ₁` (multiples of `ℓ₀` a strict step apart)
      have hstep : (u.1 ρ).val + ell₀ ≤ (y ρ).val + ell₁ :=
        mult_add_le huρ hsum (huB ρ).2
      have h2 := (hxu ρ).2
      omega

/-- The unit-owned `ℓ₀`-blocks are pairwise disjoint. -/
theorem units_pairwiseDisjoint (ell₀ ell₁ : ℕ) (y : PeriodicLatticeSite L) :
    Set.PairwiseDisjoint ↑(unitSitesOf ell₀ ell₁ y)
      (fun u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L ell₀} => blockOf u.1 ell₀) := by
  intro u _ u' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hxu hxu'
  exact hne (Subtype.ext (coarseLattice_unique ell₀ u.2 u'.2 hxu hxu'))

#print axioms blockOf_eq_biUnion_units
#print axioms units_pairwiseDisjoint

/-! ## §3 — the two sum reindexings -/

/-- Summing any `G` over the `i`-th-step blocks of all unit sites = summing the stepped `G` over
the whole `ℓ₁`-block. -/
theorem unit_block_sum {ell₀ m : ℕ} (hell₀ : 0 < ell₀)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L (ell₀ * m)) (μ : Fin 3) (i : ℕ)
    (G : PeriodicLatticeSite L → SuTwo) :
    ∑ u ∈ unitSitesOf ell₀ (ell₀ * m) y, ∑ z ∈ blockOf (pathSite u.1 μ (i * ell₀)) ell₀, G z
      = ∑ x ∈ blockOf y (ell₀ * m), G (pathSite x μ (i * ell₀)) := by
  have hinj : Function.Injective (fun x : PeriodicLatticeSite L => pathSite x μ (i * ell₀)) :=
    Function.Injective.iterate (periodicLatticeShift_injective μ) (i * ell₀)
  have hstep : ∀ u ∈ unitSitesOf ell₀ (ell₀ * m) y,
      (∑ z ∈ blockOf (pathSite u.1 μ (i * ell₀)) ell₀, G z)
        = ∑ x ∈ blockOf u.1 ell₀, G (pathSite x μ (i * ell₀)) := by
    intro u _
    rw [shift_mul_blockOf hell₀ hdvd₀ u.2 μ i,
      Finset.sum_image (fun a _ b _ h => hinj h)]
  rw [Finset.sum_congr rfl hstep,
    ← Finset.sum_biUnion (units_pairwiseDisjoint ell₀ (ell₀ * m) y),
    ← blockOf_eq_biUnion_units hell₀ (Dvd.intro m rfl) hdvd₀ hy]

/-- `range (m·ℓ₀)` decomposes as `range m × range ℓ₀` via `k = i·ℓ₀ + j`. -/
theorem sum_range_mul_decomp {M : Type*} [AddCommMonoid M] (m ell₀ : ℕ) (hell₀ : 0 < ell₀)
    (g : ℕ → M) :
    ∑ k ∈ Finset.range (m * ell₀), g k
      = ∑ p ∈ Finset.range m ×ˢ Finset.range ell₀, g (p.1 * ell₀ + p.2) := by
  refine Finset.sum_nbij' (fun k => (k / ell₀, k % ell₀)) (fun p => p.1 * ell₀ + p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hk), Nat.mod_lt _ hell₀⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    rw [Finset.mem_range]
    calc p.1 * ell₀ + p.2 < p.1 * ell₀ + ell₀ := by omega
      _ = (p.1 + 1) * ell₀ := by ring
      _ ≤ m * ell₀ := Nat.mul_le_mul_right ell₀ (by omega)
  · intro k _
    show (k / ell₀) * ell₀ + k % ell₀ = k
    rw [Nat.mul_comm, Nat.div_add_mod]
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    have h1 : (p.1 * ell₀ + p.2) / ell₀ = p.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hell₀, Nat.div_eq_of_lt hp.2, Nat.zero_add]
    have h2 : (p.1 * ell₀ + p.2) % ell₀ = p.2 := by
      rw [Nat.mul_comm p.1 ell₀, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hp.2
    show ((p.1 * ell₀ + p.2) / ell₀, (p.1 * ell₀ + p.2) % ell₀) = p
    rw [h1, h2]
  · intro k _
    show g k = g (k / ell₀ * ell₀ + k % ell₀)
    rw [Nat.mul_comm, Nat.div_add_mod]

#print axioms unit_block_sum

/-! ## §4 — THE TOWER LAW (`[Q-SEMIGROUP]` at `U = 1`) -/

/-- **`Q₁ ∘ Q_{ℓ₀} = Q_{ℓ₀·m}` at `U = 1`** — Bałaban's (3.15) semigroup property for the
faithful line-integral averagings, proved as an exact operator identity on every compatible
torus. -/
theorem tower_law {ell₀ m : ℕ} (hell₀ : 0 < ell₀) (hm : 0 < m)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1)) (v : Bond L → SuTwo) :
    unitToCoarse ell₀ m (lineCoarseRestrictCovLM (trivialU L) ell₀ v)
      = lineCoarseRestrictCovLM (trivialU L) (ell₀ * m) v := by
  funext c
  obtain ⟨yc, μ⟩ := c
  unfold unitToCoarse
  rw [lineCoarseRestrictCovLM_apply]
  show _ = lineCoarseRestrictCov (trivialU L) (ell₀ * m) v (yc, μ)
  unfold lineCoarseRestrictCov
  rw [Finset.sum_congr rfl (fun x _ => rZeroA_trivialU yc.1 x v μ (ell₀ * m))]
  -- discharge the `dite` and unfold the inner `Q`
  have hterm : ∀ u ∈ unitSitesOf ell₀ (ell₀ * m) yc.1, ∀ i ∈ Finset.range m,
      (if h : pathSite u.1 μ (i * ell₀) ∈ CoarseLattice L ell₀ then
        lineCoarseRestrictCovLM (trivialU L) ell₀ v (⟨pathSite u.1 μ (i * ell₀), h⟩, μ)
      else 0)
        = (1 / (ell₀ : ℝ) ^ 4) •
            ∑ z ∈ blockOf (pathSite u.1 μ (i * ell₀)) ell₀,
              ∑ j ∈ Finset.range ell₀, v (pathSite z μ j, μ) := by
    intro u _ i _
    rw [dif_pos (pathSite_mul_coarse ell₀ hdvd₀ u.2 μ i)]
    rw [lineCoarseRestrictCovLM_apply]
    unfold lineCoarseRestrictCov
    congr 1
    exact Finset.sum_congr rfl (fun z _ => rZeroA_trivialU _ z v μ ell₀)
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun i hi => hterm u hu i hi))]
  -- pull the inner normalization out
  simp only [← Finset.smul_sum]
  rw [smul_smul]
  -- the combinatorial core
  have hcore : (∑ u ∈ unitSitesOf ell₀ (ell₀ * m) yc.1, ∑ i ∈ Finset.range m,
      ∑ z ∈ blockOf (pathSite u.1 μ (i * ell₀)) ell₀,
        ∑ j ∈ Finset.range ell₀, v (pathSite z μ j, μ))
      = ∑ x ∈ blockOf yc.1 (ell₀ * m), ∑ k ∈ Finset.range (ell₀ * m), v (pathSite x μ k, μ) := by
    -- swap `u` and `i`
    rw [Finset.sum_comm]
    -- per `i`: collapse the unit-block double sum to the big block
    have hstep : ∀ i ∈ Finset.range m,
        (∑ u ∈ unitSitesOf ell₀ (ell₀ * m) yc.1,
          ∑ z ∈ blockOf (pathSite u.1 μ (i * ell₀)) ell₀,
            ∑ j ∈ Finset.range ell₀, v (pathSite z μ j, μ))
          = ∑ x ∈ blockOf yc.1 (ell₀ * m),
              ∑ j ∈ Finset.range ell₀, v (pathSite (pathSite x μ (i * ell₀)) μ j, μ) := by
      intro i _
      exact unit_block_sum hell₀ hdvd₀ yc.2 μ i
        (fun z => ∑ j ∈ Finset.range ell₀, v (pathSite z μ j, μ))
    rw [Finset.sum_congr rfl hstep]
    -- swap back and decompose the fine range
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (ell₀ * m) = m * ell₀ by ring, sum_range_mul_decomp m ell₀ hell₀,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    have hcomp : pathSite x μ (i * ell₀ + j) = pathSite (pathSite x μ (i * ell₀)) μ j := by
      rw [show i * ell₀ + j = j + i * ell₀ by ring]
      exact Function.iterate_add_apply _ j (i * ell₀) x
    exact hcomp.symm
  rw [hcore]
  congr 1
  have hm' : ((m : ℝ)) ^ 4 ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    positivity
  have hell' : ((ell₀ : ℝ)) ^ 4 ≠ 0 := by
    have : (0 : ℝ) < (ell₀ : ℝ) := by exact_mod_cast hell₀
    positivity
  push_cast
  field_simp

#print axioms tower_law

/-! ## §5 — what the tower law buys: the kernel translation -/

/-- **`v ∈ ker Q_{ℓ₀·m} ⟺ Q_{ℓ₀} v ∈ ker Q₁`** — the exact statement `CStarLevelCorrected` §6
says the pulled-back constraint needs: the corrected typing's `ℓ₁`-kernel membership IS the
unit-level (3.156) constraint `Q₁B = 0` on `B = Q_{ℓ₀}v`. -/
theorem ker_translation {ell₀ m : ℕ} (hell₀ : 0 < ell₀) (hm : 0 < m)
    (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1)) (v : Bond L → SuTwo) :
    lineCoarseRestrictCovLM (trivialU L) (ell₀ * m) v = 0
      ↔ unitToCoarse ell₀ m (lineCoarseRestrictCovLM (trivialU L) ell₀ v) = 0 := by
  rw [tower_law hell₀ hm hdvd₀ v]

#print axioms ker_translation

end AdalyFormal.Balaban.ThirdLevelArrows
