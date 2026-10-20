/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.AxialContour
import AdalyFormal.Balaban.BridgeRestricted
import AdalyFormal.Balaban.RegularUPerturbation

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `AxialCoercivity.lean` — the axial gauge-fixing QUADRATIC FORM on the CMP95 `(1.7)` contours

Lane record: `compute/axial_coercivity/PROGRESS.md`.

## The question this module exists to answer

`BridgeRestricted.lean` proved that the surviving burden of the bridge is a coercivity statement
about the gauge-fixing term `P` alone, on a mode that BOTH `Δ_k` and `Q` annihilate:
`BridgeRestricted.alternating_field_forces_P_coercive` states
`(γ − δ)‖v‖² ≤ ⟨v, P v⟩` at `v = axisField 0 altC rotGen`, and nothing in the tree supplied it.

This module builds the source's own candidate for `P` — CMP95 `(1.10)`'s axial gauge fixing on the
`(1.7)` contours — as a genuine quadratic form and a genuine symmetric positive-semidefinite
operator, and computes it at that mode.

## §0 — THE SOURCE, and the one normalization choice, stated not hidden

CMP95 printed p.18, `(1.7)` (the DEFINING page, image-read twice: this module does not re-read it,
it reuses the object; see `compute/gamma_denotation/CMP95_P18_READ.md`,
render `corpus/renders/CMP95_p18-02.png` sha256
`51043df7a971ec51865c32c871aaf888e124a594ef1806739cbf6b7f8ccffeb9`, and the independent second
read recorded in `AxialContour.lean`'s header) defines the contour family `Γ_{y,x}`, oriented
`y → x`, switching coordinates in DESCENDING axis order `d, d−1, …, 1`. On this `d = 3`,
`0`-indexed carrier that is `2, 1, 0`.

CMP95 printed p.19, `(1.10)` (render `corpus/renders/CMP95_p19-03.png` sha256
`487414cfbd696d345de8ede6f6e74f9e9c1bd160fb32221fbe4b23c50cee00b9`) prints the axial gauge fixing

```
δ_Ax(A) = ∏_{y ∈ T_L^{(1)}} ∏_{x ∈ B(y), x ≠ y} δ(A(Γ_{y,x}))
```

**`Γ_{y,x}` IS NOT REDEFINED HERE.** `AdmissibleSubspace.staircasePath` is reused verbatim
(LAW-19, and BUILD-DISCIPLINE 3): it is the object already fidelity-checked against `(1.7)` at the
page image by two independent passes. `blockOf` (`= B(y)`, `(1.6)`) and `CoarseLattice`
(`= T_L^{(1)}`) are likewise reused, as is `AxialContour.Ax` for the bond-form slice. This module
adds exactly one new geometric object, `pathIntegral` (`= A(Γ_{y,x})`, the sum of `A` over the
contour's bonds), and the quadratic form built from it.

**THE NORMALIZATION, and why no constant here is forced by the source.** `(1.10)` is a product of
DIRAC DELTAS — a hard linear constraint, carrying no quadratic weight of its own. Any quadratic
`P` whose null space is exactly the `(1.10)` locus is a legitimate soft form of it, and the family
is `ξ⁻¹ · P_Ax` for `ξ > 0` (the standard gauge-fixing parameter; `ξ → 0` recovers the delta).
This module fixes **`ξ = 1`, unit weight per pair `(y,x)`**:

`P_Ax(A) := ∑_{y ∈ S} ∑_{x ∈ B(y), x ≠ y} ‖A(Γ_{y,x})‖²`.

Consequences, stated so no reader has to infer them:
* every statement of the form "`P_Ax` vanishes / is positive / has this null space" is
  `ξ`-INDEPENDENT;
* every statement of the form "`P_Ax(A) ≥ c · bondEnergy A` " carries `c` linearly in `ξ⁻¹`, so the
  CONSTANT `1/2` proved in §4 is a constant OF THIS NORMALIZATION and is not attributed to CMP95.
  (Uniform-rescale test, run against the DECLARATIONS THAT EXIST: multiply `pAx` by `2` and
  `pAx_altField` (`= 108‖rotGen‖²`), `inner_pAxCLM_altVec_eq_half` and the THIRD conjunct of
  `gauge_fixing_sees_the_closed_mode` (`= ½·bondEnergy`) all fail, while the FOURTH conjunct of
  `gauge_fixing_sees_the_closed_mode` (`0 < pAx`), every §2 control, §7's
  `deltaK_plus_pAx_not_coercive`, §8's `pAx_eq_zero_of_support_off_coarse` and §9's
  `norm_sq_tree_bond_le_pAx` all survive — that is exactly the intended split. The `1/2` and the
  `108`/`216` are `ξ`-dependent; nothing else in this file is.)

## §0b — what is built

1. `pathIntegral A y x = A(Γ_{y,x})` and `pAxBlock`/`pAx` (§1).
2. Controls (§2): non-negativity; `pAx = 0` exactly on the `(1.10)` locus; `pAx = 0` on the
   STRONGER bond-form slice `AxialContour.Ax`; the `ell = 1` and boundary-truncation degeneracies.
3. The axis-field path-integral formula (§3), general in the profile `c` and the background — the
   contour integral of `(1.10)` is BARE (no parallel transport: `(1.7)`/`(1.10)` are stated in
   CMP95, the `U = 1` paper), so `pAx` does not depend on `U` at all. That is why the §4 result is
   background-independent.
4. **The must-fire (§4)**: at `witL5`, `ell = 2`, on `BridgeRestricted.axisField 0 altC rotGen` —
   the field `Δ_k` annihilates and `Q` annihilates — `pAx` is EXACTLY `½ · bondEnergy`.
5. The operator form (§5): `pAxOp` / `pAxCLM`, symmetric, PSD, with `⟨A, pAxCLM A⟩ = pAx A`, so it
   is a legal value of the bridge's `P` slot.
6. §6 discharges `BridgeRestricted.alternating_field_forces_P_coercive`'s demand at that mode with
   the explicit constant `1/2`.
7. §7 is the tree-control theorem: `pAx` dominates the energy of EVERY bond of the spanning tree
   `Ax(y)`, at `ell = 2` — the half of CMP95 p.19's positivity claim that needs no curl.
-/

namespace AdalyFormal.Balaban.AxialCoercivity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.AxialContour
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)

variable {L : PeriodicLatticeExtent}

/-! ## §1. `A(Γ_{y,x})` and the quadratic form `P_Ax` -/

/-- **`A(Γ_{y,x})`, CMP95 `(1.10)`'s argument.** The line integral of the bond field `A` along the
contour `Γ_{y,x}` — the plain sum of `A` over the contour's bonds. All bonds of `staircasePath y x`
are traversed in the POSITIVE coordinate direction when `x ∈ B(y)` (`blockOf` is the half-open box
`y_μ ≤ x_μ < y_μ + ell`, so `x_μ ≥ y_μ` and no segment runs backwards), so no orientation signs
appear; `staircasePath`'s `min`/`max` bounds already encode this. NOT parallel-transported: CMP95 is
the `U = 1` paper and `(1.7)`/`(1.10)` carry no transport. -/
noncomputable def pathIntegral (A : Bond L → SuTwo) (y x : PeriodicLatticeSite L) : SuTwo :=
  ∑ b ∈ staircasePath y x, A b

/-- **The single-block gauge-fixing energy**, `∑_{x ∈ B(y), x ≠ y} ‖A(Γ_{y,x})‖²`. The `x ≠ y`
comes from `(1.10)`'s own inner product quantifier, realized as `Finset.erase` so it is visibly
`B(y)` minus one point (same idiom as `AxialContour.Ax`, no silent re-quantification). -/
noncomputable def pAxBlock (A : Bond L → SuTwo) (ell : ℕ) (y : PeriodicLatticeSite L) : ℝ :=
  ∑ x ∈ (blockOf y ell).erase y, ‖pathIntegral A y x‖ ^ 2

/-- **`P_Ax`**, the axial gauge-fixing quadratic form over a center set `S`. `S := CoarseLattice L
ell` is CMP95 `(1.10)`'s own `∏_{y ∈ T_L^{(1)}}`; a proper sub-`Finset` is CMP96 `(2.121)` /
CMP99b `(3.156)`'s restricted `Λ'`. Unit weight per pair — see §0's normalization statement. -/
noncomputable def pAx (A : Bond L → SuTwo) (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) : ℝ :=
  ∑ y ∈ S, pAxBlock A ell y

/-- CMP95 `(1.10)`'s own instance: every coarse center. -/
noncomputable abbrev pAxCmp95 (A : Bond L → SuTwo) (ell : ℕ) : ℝ :=
  pAx A (CoarseLattice L ell) ell

theorem pAxBlock_nonneg (A : Bond L → SuTwo) (ell : ℕ) (y : PeriodicLatticeSite L) :
    0 ≤ pAxBlock A ell y :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem pAx_nonneg (A : Bond L → SuTwo) (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) :
    0 ≤ pAx A S ell :=
  Finset.sum_nonneg (fun _ _ => pAxBlock_nonneg A ell _)

/-- `P_Ax` is homogeneous of degree `2`, as any quadratic form must be. Used by §5's operator
identification and by the rescale control of §0. -/
theorem pAx_smul (A : Bond L → SuTwo) (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) (t : ℝ) :
    pAx (fun b => t • A b) S ell = t ^ 2 * pAx A S ell := by
  unfold pAx pAxBlock
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hpi : pathIntegral (fun b => t • A b) y x = t • pathIntegral A y x := by
    unfold pathIntegral
    exact (Finset.smul_sum).symm
  rw [hpi, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-! ## §2. CONTROLS — the must-not-fire, and the two degeneracies -/

/-- **MUST-NOT-FIRE (the `(1.10)` locus, exactly).** `P_Ax A S ell = 0` iff every one of `(1.10)`'s
contour integrals vanishes. This is the sharp statement that `pAx`'s null space is EXACTLY the
source's gauge-fixing locus — not merely that it contains it. Vanishing there is the term's job. -/
theorem pAx_eq_zero_iff (A : Bond L → SuTwo) (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) :
    pAx A S ell = 0 ↔
      ∀ y ∈ S, ∀ x ∈ (blockOf y ell).erase y, pathIntegral A y x = 0 := by
  unfold pAx pAxBlock
  constructor
  · intro h y hy x hx
    have h1 : ∀ z ∈ S, (∑ w ∈ (blockOf z ell).erase z, ‖pathIntegral A z w‖ ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))).1 h
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 (h1 y hy) x hx
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  · intro h
    refine Finset.sum_eq_zero (fun y hy => Finset.sum_eq_zero (fun x hx => ?_))
    rw [h y hy x hx, norm_zero]
    norm_num

/-- **MUST-NOT-FIRE on the STRONGER, bond-form slice.** CMP96 `(2.121)` / CMP99b `(3.156)` impose
`A = 0` on every bond of `Ax(y)` (the union of the contours), which is strictly stronger than
`(1.10)`'s sum condition. `pAx` vanishes there too — reusing `AxialContour.Ax` as the bond set, and
`AxialContour.mem_Ax` as the membership rewrite, rather than re-deriving either. -/
theorem pAx_eq_zero_of_vanishing_on_Ax (A : Bond L → SuTwo)
    (S : Finset (PeriodicLatticeSite L)) (ell : ℕ)
    (hA : ∀ y ∈ S, ∀ b ∈ Ax y ell, A b = 0) :
    pAx A S ell = 0 := by
  rw [pAx_eq_zero_iff]
  intro y hy x hx
  unfold pathIntegral
  refine Finset.sum_eq_zero (fun b hb => ?_)
  refine hA y hy b (mem_Ax.2 ⟨x, (Finset.mem_erase.1 hx).2, (Finset.mem_erase.1 hx).1, hb⟩)

/-- **The gauge-fixing term is NOT vacuous as a control**: `pAx` vanishing on the slice is a real
constraint precisely because `pAx` does NOT vanish identically. Paired with §4's must-fire, the two
controls bracket the object. Stated here as the trivial half (`0` field), so the §2/§4 pair is a
genuine must-not-fire / must-fire pair on the SAME object. -/
theorem pAx_zero_field (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) :
    pAx (fun _ => (0 : SuTwo)) S ell = 0 := by
  rw [pAx_eq_zero_iff]
  intro y _ x _
  exact Finset.sum_const_zero

/-- **DEGENERACY 1 — `ell = 1`.** Singleton blocks: `B(y) = {y}`, so `(1.10)`'s inner product is
empty and `P_Ax ≡ 0` for EVERY field. Proved in general (any `L`, any `S`, any `A`), reusing
`AxialContour.blockOf_one`. The gauge fixing has no content at the trivial block scale — the honest
formal reading of the source's own degenerate case. -/
theorem pAx_ell_one (A : Bond L → SuTwo) (S : Finset (PeriodicLatticeSite L)) :
    pAx A S 1 = 0 := by
  unfold pAx pAxBlock
  refine Finset.sum_eq_zero (fun y _ => ?_)
  rw [blockOf_one, Finset.erase_singleton]
  simp

/-- **DEGENERACY 2 — `blockOf` truncation at a periodic-extent corner.** The SAME conclusion by a
DIFFERENT mechanism (boundary truncation of the half-open box, at `ell = 2 > 1`), reusing
`AxialContour.boundaryCenter_blockOf_eq_singleton`. This is the `blockOf`-truncation guard carried
explicitly: a center whose block is truncated to a point contributes NOTHING to `P_Ax`, so a center
set containing such points silently loses gauge-fixing strength there. §4 works on `witL5` with
`ell = 2`, where `2 ∣ 6` and every coarse block is a full `2³` box, so no center is truncated. -/
theorem pAxBlock_boundaryCenter (A : Bond witnessL → SuTwo) :
    pAxBlock A witnessEll boundaryCenter = 0 := by
  unfold pAxBlock
  rw [boundaryCenter_blockOf_eq_singleton, Finset.erase_singleton]
  simp

#print axioms pathIntegral
#print axioms pAxBlock
#print axioms pAx
#print axioms pAxCmp95
#print axioms pAxBlock_nonneg
#print axioms pAx_nonneg
#print axioms pAx_smul
#print axioms pAx_eq_zero_iff
#print axioms pAx_eq_zero_of_vanishing_on_Ax
#print axioms pAx_zero_field
#print axioms pAx_ell_one
#print axioms pAxBlock_boundaryCenter

/-! ## §3. The contour integral of an AXIS FIELD — general in profile and background

`BridgeRestricted.axisField d c X b = if b.2 = d then c b.1 • X else 0`. For `d = 0` — the
direction of the closed alternating mode — only the LAST segment of `Γ_{y,x}` (the one that
switches coordinate `0`, which the `(1.7)` descending order puts last) can contribute. -/

section AxisField

open AdalyFormal.Balaban.BridgeRestricted (axisField axisField_eq_smul axisField_pair)

/-- The direction-`0` segment of `Γ_{y,x}`: the third summand of `staircasePath`, based at
`corner2 y x = (y₀, x₁, x₂)`. Named so the formulas below do not repeat it. -/
noncomputable def dirZeroSegment (y x : PeriodicLatticeSite L) : Finset (Bond L) :=
  axisSegment (corner2 y x) 0 (min (y 0).val (x 0).val) (max (y 0).val (x 0).val)

theorem dirZeroSegment_subset (y x : PeriodicLatticeSite L) :
    dirZeroSegment y x ⊆ staircasePath y x := by
  unfold dirZeroSegment staircasePath
  exact Finset.subset_union_right

/-- **Every direction-`0` bond of `Γ_{y,x}` lies in its last segment.** The first two segments carry
directions `2` and `1` by construction, so a direction-`0` bond can only come from the third. -/
theorem mem_dirZeroSegment_of_mem_staircasePath {y x : PeriodicLatticeSite L} {b : Bond L}
    (hb : b ∈ staircasePath y x) (hd : b.2 = 0) : b ∈ dirZeroSegment y x := by
  unfold staircasePath at hb
  rcases Finset.mem_union.1 hb with hb' | hb'
  · rcases Finset.mem_union.1 hb' with h | h
    · have h2 := (mem_axisSegment.1 h).1
      rw [hd] at h2
      exact absurd h2 (by decide)
    · have h2 := (mem_axisSegment.1 h).1
      rw [hd] at h2
      exact absurd h2 (by decide)
  · exact hb'

/-- **THE AXIS-FIELD CONTOUR FORMULA.** `A(Γ_{y,x}) = (∑ over the last segment of the profile) • X`,
for every `y`, `x`, every profile `c`, every `X` — no hypothesis on the background at all, because
the contour integral of `(1.10)` carries no parallel transport. -/
theorem pathIntegral_axisField (c : PeriodicLatticeSite L → ℝ) (X : SuTwo)
    (y x : PeriodicLatticeSite L) :
    pathIntegral (axisField (0 : Fin 3) c X) y x = (∑ b ∈ dirZeroSegment y x, c b.1) • X := by
  unfold pathIntegral
  rw [← Finset.sum_subset (dirZeroSegment_subset y x) ?_]
  · rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hd : b.2 = 0 := by
      unfold dirZeroSegment at hb
      exact (mem_axisSegment.1 hb).1
    rw [axisField_eq_smul, if_pos hd]
  · intro b _ hbn
    have hd : b.2 ≠ 0 := by
      intro h
      exact hbn (mem_dirZeroSegment_of_mem_staircasePath (by assumption) h)
    rw [axisField_eq_smul, if_neg hd, zero_smul]

end AxisField

#print axioms dirZeroSegment
#print axioms dirZeroSegment_subset
#print axioms mem_dirZeroSegment_of_mem_staircasePath
#print axioms pathIntegral_axisField

/-! ## §3b. Two elementary segment computations -/

/-- An axis segment with an empty sweep range is empty. -/
theorem axisSegment_self_empty (base : PeriodicLatticeSite L) (μ : Fin 3) (a : ℕ) :
    axisSegment base μ a a = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 (fun e he => ?_)
  have h := mem_axisSegment.1 he
  omega

/-- An axis segment sweeping exactly one step from `base`'s own coordinate is the singleton
containing the bond based at `base`. -/
theorem axisSegment_succ_singleton (base : PeriodicLatticeSite L) (μ : Fin 3) :
    axisSegment base μ (base μ).val ((base μ).val + 1) = {(base, μ)} := by
  ext e
  rw [mem_axisSegment, Finset.mem_singleton]
  constructor
  · rintro ⟨h2, hν, ha, hb⟩
    have hμ : e.1 μ = base μ := Fin.ext (by omega)
    have h1 : e.1 = base := by
      funext ν
      by_cases hν0 : ν = μ
      · subst hν0; exact hμ
      · exact hν ν hν0
    exact Prod.ext h1 h2
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl, le_rfl, Nat.lt_succ_self _⟩

/-- `corner2 y x` keeps `y`'s coordinate `0` — the `(1.7)` order switches coordinate `0` LAST, so
the base of the last segment still sits at `y₀`. -/
theorem corner2_apply_zero (y x : PeriodicLatticeSite L) : (corner2 y x) 0 = y 0 := by
  show Function.update (corner1 y x) 1 (x 1) 0 = y 0
  rw [Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide)]
  show Function.update y 2 (x 2) 0 = y 0
  rw [Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)]

theorem dirZeroSegment_eq_empty (y x : PeriodicLatticeSite L) (h : (x 0).val = (y 0).val) :
    dirZeroSegment y x = ∅ := by
  unfold dirZeroSegment
  rw [show min (y 0).val (x 0).val = (y 0).val by omega,
    show max (y 0).val (x 0).val = (y 0).val by omega]
  exact axisSegment_self_empty _ _ _

theorem dirZeroSegment_succ (y x : PeriodicLatticeSite L) (h : (x 0).val = (y 0).val + 1) :
    dirZeroSegment y x = {(corner2 y x, 0)} := by
  unfold dirZeroSegment
  rw [show min (y 0).val (x 0).val = ((corner2 y x) 0).val by rw [corner2_apply_zero]; omega,
    show max (y 0).val (x 0).val = ((corner2 y x) 0).val + 1 by rw [corner2_apply_zero]; omega]
  exact axisSegment_succ_singleton _ _

#print axioms axisSegment_self_empty
#print axioms axisSegment_succ_singleton
#print axioms corner2_apply_zero
#print axioms dirZeroSegment_eq_empty
#print axioms dirZeroSegment_succ

/-! ## §4. THE MUST-FIRE — `P_Ax` SEES THE MODE `Δ_k` AND `Q` BOTH MISS

`BridgeRestricted.axisField 0 altC rotGen` at `witL5` is the field on which
`deltaKQuadFormNormalizedCorrected_axisField_eq_zero` gives `⟨v, Δ_k v⟩ = 0` and
`qCLM_axisField_altC_eq_zero_at_curvedRegularU` gives `Q v = 0`. This section computes `P_Ax` on it
EXACTLY, at `ell = 2` with `S = CoarseLattice witL5 2` (CMP95 `(1.10)`'s own center set). -/

section MustFire

open AdalyFormal.Balaban.BridgeRestricted (axisField axisField_eq_smul axisField_pair altC rotGen
  rotGen_ne_zero curvedRegularU_linkFixes_rotGen altC_transverse altC_alternates
  deltaKQuadFormNormalizedCorrected_axisField_eq_zero
  qCLM_axisField_altC_eq_zero_at_curvedRegularU)
open AdalyFormal.Balaban.CoercivityRegular (curvedRegularU)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)

/-- `altC` takes values `±1`, so its absolute value is `1`. -/
theorem altC_abs_one (z : PeriodicLatticeSite witL5) : |altC z| = 1 := by
  unfold altC
  split_ifs <;> norm_num

theorem altC_corner2 (y x : PeriodicLatticeSite witL5) : altC (corner2 y x) = altC y := by
  unfold altC
  rw [corner2_apply_zero]

/-- `‖(altC z) • rotGen‖² = ‖rotGen‖²`. -/
theorem norm_sq_altC_smul (z : PeriodicLatticeSite witL5) :
    ‖(altC z) • rotGen‖ ^ 2 = ‖rotGen‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, altC_abs_one, one_mul]

/-! ### §4a — the per-pair value -/

/-- **THE PER-PAIR VALUE.** Inside a block of side `2`, `x₀` is either `y₀` (contour integral `0`)
or `y₀ + 1` (contour integral `altC y • rotGen`, of norm `‖rotGen‖`). No other case occurs, because
`blockOf` is the half-open box. -/
theorem pathIntegral_altField_norm_sq (y x : PeriodicLatticeSite witL5)
    (hx : x ∈ blockOf y 2) :
    ‖pathIntegral (axisField (0 : Fin 3) altC rotGen) y x‖ ^ 2
      = if (x 0).val = (y 0).val + 1 then ‖rotGen‖ ^ 2 else 0 := by
  have hb := mem_blockOf.1 hx 0
  by_cases h : (x 0).val = (y 0).val + 1
  · rw [if_pos h, pathIntegral_axisField, dirZeroSegment_succ y x h, Finset.sum_singleton,
      altC_corner2]
    exact norm_sq_altC_smul y
  · have h0 : (x 0).val = (y 0).val := by omega
    rw [if_neg h, pathIntegral_axisField, dirZeroSegment_eq_empty y x h0]
    simp

/-! ### §4b — the counts, done with `Fintype.piFinset` (no `decide` over the 216-site carrier) -/

/-- `T_L^{(1)}` is a product of one-coordinate sets. -/
theorem coarseLattice_eq_piFinset (L : PeriodicLatticeExtent) (ell : ℕ) :
    CoarseLattice L ell
      = Fintype.piFinset (fun μ : Fin 3 =>
          Finset.univ.filter (fun i : Fin (L μ + 1) => i.val % ell = 0)) := by
  ext y
  rw [mem_CoarseLattice, Fintype.mem_piFinset]
  simp

/-- **`|T_L^{(1)}| = 27` at `witL5`, `ell = 2`** — `3` even values (`0,2,4`) per axis, three axes. -/
theorem card_coarseLattice_witL5 : (CoarseLattice witL5 2).card = 27 := by
  rw [coarseLattice_eq_piFinset, Fintype.card_piFinset]
  simp only [Fin.prod_univ_three]
  decide

/-- The `x₀ = y₀ + 1` slice of a block, as a product of one-coordinate sets. -/
theorem blockOf_slice_eq_piFinset (y : PeriodicLatticeSite L) (ell : ℕ) :
    (blockOf y ell).filter (fun x => (x 0).val = (y 0).val + 1)
      = Fintype.piFinset (fun μ : Fin 3 =>
          Finset.univ.filter (fun i : Fin (L μ + 1) =>
            (y μ).val ≤ i.val ∧ i.val < (y μ).val + ell ∧ (μ = 0 → i.val = (y μ).val + 1))) := by
  ext x
  simp only [Finset.mem_filter, mem_blockOf, Fintype.mem_piFinset, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hb, h0⟩ μ
    exact ⟨(hb μ).1, (hb μ).2, fun hμ => by subst hμ; exact h0⟩
  · intro h
    exact ⟨fun μ => ⟨(h μ).1, (h μ).2.1⟩, (h 0).2.2 rfl⟩

/-- **The slice has exactly `4` points** at `witL5`, `ell = 2`, for an aligned (coarse) center:
`1` choice in the swept coordinate `0`, `2` in each of the two transverse coordinates. The
alignment hypothesis is what rules out `blockOf` truncation (`y₀ = 5` would give a slice of `0`). -/
theorem card_blockOf_slice_witL5 (y : PeriodicLatticeSite witL5)
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) :
    ((blockOf y 2).filter (fun x => (x 0).val = (y 0).val + 1)).card = 4 := by
  rw [blockOf_slice_eq_piFinset, Fintype.card_piFinset]
  have key : ∀ j : Fin 3 → Fin 6, (∀ μ : Fin 3, (j μ).val % 2 = 0) →
      (∏ μ : Fin 3, (Finset.univ.filter (fun i : Fin 6 =>
          (j μ).val ≤ i.val ∧ i.val < (j μ).val + 2
            ∧ (μ = 0 → i.val = (j μ).val + 1))).card) = 4 := by
    decide
  exact key y hy

/-! ### §4c — the block value, the total, and the comparison with `bondEnergy` -/

theorem pAxBlock_altField (y : PeriodicLatticeSite witL5) (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) :
    pAxBlock (axisField (0 : Fin 3) altC rotGen) 2 y = 4 * ‖rotGen‖ ^ 2 := by
  unfold pAxBlock
  have hyzero : ‖pathIntegral (axisField (0 : Fin 3) altC rotGen) y y‖ ^ 2 = 0 := by
    rw [pathIntegral_axisField, dirZeroSegment_eq_empty y y rfl]
    simp
  rw [Finset.sum_erase (f := fun x => ‖pathIntegral (axisField (0 : Fin 3) altC rotGen) y x‖ ^ 2)
    (blockOf y 2) hyzero]
  rw [Finset.sum_congr rfl (fun x hx => pathIntegral_altField_norm_sq y x hx)]
  rw [← Finset.sum_filter, Finset.sum_const, card_blockOf_slice_witL5 y hy, nsmul_eq_mul]
  norm_num

/-- **`P_Ax` ON THE CLOSED ALTERNATING MODE, EXACTLY.** `27` coarse blocks, `4` contributing
contours each, unit weight per contour. -/
theorem pAx_altField :
    pAx (axisField (0 : Fin 3) altC rotGen) (CoarseLattice witL5 2) 2 = 108 * ‖rotGen‖ ^ 2 := by
  unfold pAx
  rw [Finset.sum_congr rfl (fun y hy =>
    pAxBlock_altField y (mem_CoarseLattice.1 hy))]
  rw [Finset.sum_const, card_coarseLattice_witL5, nsmul_eq_mul]
  push_cast
  ring

/-- **The same mode's total bond energy.** `216` sites, one nonzero (direction-`0`) bond each. -/
theorem bondEnergy_altField :
    bondEnergy (axisField (0 : Fin 3) altC rotGen) = 216 * ‖rotGen‖ ^ 2 := by
  show (∑ b : Bond witL5, ‖axisField (0 : Fin 3) altC rotGen b‖ ^ 2) = _
  rw [Fintype.sum_prod_type]
  have hz : ∀ z : PeriodicLatticeSite witL5,
      (∑ μ : Fin 3, ‖axisField (0 : Fin 3) altC rotGen (z, μ)‖ ^ 2) = ‖rotGen‖ ^ 2 := by
    intro z
    have e0 : axisField (0 : Fin 3) altC rotGen (z, (0 : Fin 3)) = (altC z) • rotGen := by
      rw [axisField_pair, if_pos rfl]
    have e1 : axisField (0 : Fin 3) altC rotGen (z, (1 : Fin 3)) = 0 := by
      rw [axisField_pair, if_neg (show ¬((1 : Fin 3) = 0) by decide), zero_smul]
    have e2 : axisField (0 : Fin 3) altC rotGen (z, (2 : Fin 3)) = 0 := by
      rw [axisField_pair, if_neg (show ¬((2 : Fin 3) = 0) by decide), zero_smul]
    simp only [Fin.sum_univ_three]
    rw [e0, e1, e2, norm_zero, norm_sq_altC_smul z]
    norm_num
  have hcard : Fintype.card (PeriodicLatticeSite witL5) = 216 := by
    rw [Fintype.card_pi]
    simp only [Fin.prod_univ_three]
    decide
  rw [Finset.sum_congr rfl (fun z _ => hz z), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hcard]
  norm_num

/-- **THE HEADLINE, AS ONE STATEMENT.** On `witL5` at block scale `2`, with CMP95 `(1.10)`'s own
center set, the field `v = axisField 0 altC rotGen` satisfies simultaneously:

* `⟨v, Δ_k v⟩ = 0` at `curvedRegularU` (`BridgeRestricted`, §8a) — `Δ_k` misses it;
* `Q v = 0` at `curvedRegularU` (`BridgeRestricted`, §8b) — `Q` misses it;
* `P_Ax(v) = ½ · bondEnergy(v) > 0` — **the gauge-fixing term SEES it**, with a constant.

The `P_Ax` value is background-independent (§3's contour integral carries no transport), so the
third clause holds at EVERY `U`; only the first two clauses are `curvedRegularU`-specific. -/
theorem gauge_fixing_sees_the_closed_mode :
    deltaKQuadFormNormalizedCorrected curvedRegularU
        (axisField (0 : Fin 3) altC rotGen) = 0
      ∧ AdalyFormal.Balaban.BridgeInverse.qCLM curvedRegularU 2
          (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) : BondFnL2 witL5) = 0
      ∧ pAx (axisField (0 : Fin 3) altC rotGen) (CoarseLattice witL5 2) 2
          = (1 / 2 : ℝ) * bondEnergy (axisField (0 : Fin 3) altC rotGen)
      ∧ 0 < pAx (axisField (0 : Fin 3) altC rotGen) (CoarseLattice witL5 2) 2 := by
  refine ⟨deltaKQuadFormNormalizedCorrected_axisField_eq_zero curvedRegularU (0 : Fin 3) altC
      rotGen curvedRegularU_linkFixes_rotGen altC_transverse,
    qCLM_axisField_altC_eq_zero_at_curvedRegularU, ?_, ?_⟩
  · rw [pAx_altField, bondEnergy_altField]; ring
  · rw [pAx_altField]
    have : 0 < ‖rotGen‖ ^ 2 := pow_pos (norm_pos_iff.2 rotGen_ne_zero) 2
    linarith

end MustFire

#print axioms altC_abs_one
#print axioms altC_corner2
#print axioms norm_sq_altC_smul
#print axioms pathIntegral_altField_norm_sq
#print axioms coarseLattice_eq_piFinset
#print axioms card_coarseLattice_witL5
#print axioms blockOf_slice_eq_piFinset
#print axioms card_blockOf_slice_witL5
#print axioms pAxBlock_altField
#print axioms pAx_altField
#print axioms bondEnergy_altField
#print axioms gauge_fixing_sees_the_closed_mode

/-! ## §5. `P_Ax` AS A GENUINE OPERATOR ON `BondFnL2`

A quadratic form is not a legal value of the bridge's `P` slot; a symmetric positive-semidefinite
`BondFnL2 →L[ℝ] BondFnL2` is. This section builds one whose diagonal is `pAx`, by REUSING
`CStarDeltaKCOperator.bilinToOperatorBond` (the Riesz map the tree already carries) rather than
rebuilding a Riesz correspondence (LAW-19). -/

section Operator

open AdalyFormal.Balaban.CStarDeltaKCOperator (bilinToOperatorBond inner_bilinToOperatorBond
  bondAdjoint bondAdjoint_bilinToOperatorBond bondAdjoint_eq_self_iff)

theorem ofLp_add_apply (A B : BondFnL2 L) (b : Bond L) :
    (WithLp.ofLp (A + B)) b = (WithLp.ofLp A) b + (WithLp.ofLp B) b := rfl

theorem ofLp_smul_apply (c : ℝ) (A : BondFnL2 L) (b : Bond L) :
    (WithLp.ofLp (c • A)) b = c • (WithLp.ofLp A) b := rfl

theorem pathIntegral_ofLp_add (A B : BondFnL2 L) (y x : PeriodicLatticeSite L) :
    pathIntegral (WithLp.ofLp (A + B)) y x
      = pathIntegral (WithLp.ofLp A) y x + pathIntegral (WithLp.ofLp B) y x := by
  unfold pathIntegral
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun b _ => ofLp_add_apply A B b)

theorem pathIntegral_ofLp_smul (c : ℝ) (A : BondFnL2 L) (y x : PeriodicLatticeSite L) :
    pathIntegral (WithLp.ofLp (c • A)) y x = c • pathIntegral (WithLp.ofLp A) y x := by
  unfold pathIntegral
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun b _ => ofLp_smul_apply c A b)

/-- **The gauge-fixing BILINEAR form** `∑_{y,x} ⟪A(Γ_{y,x}), B(Γ_{y,x})⟫`. Its diagonal is `pAx`. -/
noncomputable def pAxBil (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun A B => ∑ y ∈ S, ∑ x ∈ (blockOf y ell).erase y,
      (inner ℝ (pathIntegral (WithLp.ofLp A) y x) (pathIntegral (WithLp.ofLp B) y x) : ℝ))
    (by
      intro A₁ A₂ B
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [pathIntegral_ofLp_add, inner_add_left])
    (by
      intro c A B
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [pathIntegral_ofLp_smul, real_inner_smul_left, smul_eq_mul])
    (by
      intro A B₁ B₂
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [pathIntegral_ofLp_add, inner_add_right])
    (by
      intro c A B
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [pathIntegral_ofLp_smul, real_inner_smul_right, smul_eq_mul])

theorem pAxBil_apply (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) (A B : BondFnL2 L) :
    pAxBil S ell A B = ∑ y ∈ S, ∑ x ∈ (blockOf y ell).erase y,
      (inner ℝ (pathIntegral (WithLp.ofLp A) y x) (pathIntegral (WithLp.ofLp B) y x) : ℝ) := rfl

theorem pAxBil_symm (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) (A B : BondFnL2 L) :
    pAxBil S ell A B = pAxBil S ell B A := by
  rw [pAxBil_apply, pAxBil_apply]
  exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => real_inner_comm _ _))

/-- **THE GAUGE-FIXING OPERATOR.** -/
noncomputable def pAxOp (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  bilinToOperatorBond (pAxBil S ell)

/-- The bridge's `P` slot wants a `→L[ℝ]`. Finite dimension makes the promotion free. -/
noncomputable def pAxCLM (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (pAxOp S ell)

/-- **THE DIAGONAL IDENTITY** — `⟨A, P_Ax A⟩ = P_Ax(A)`. This is what makes `pAxCLM` the operator
form of CMP95 `(1.10)`'s gauge fixing and not merely some positive operator. -/
theorem inner_pAxCLM_eq (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (pAxCLM S ell (WithLp.toLp 2 A)) : ℝ)
      = pAx A S ell := by
  show (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (pAxOp S ell (WithLp.toLp 2 A)) : ℝ) = _
  rw [pAxOp, inner_bilinToOperatorBond, pAxBil_apply]
  unfold pAx pAxBlock
  exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ =>
    real_inner_self_eq_norm_sq _))

/-- The same identity phrased on an arbitrary `BondFnL2` vector. -/
theorem inner_pAxCLM_eq' (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) (v : BondFnL2 L) :
    (inner ℝ v (pAxCLM S ell v) : ℝ) = pAx (WithLp.ofLp v) S ell :=
  inner_pAxCLM_eq S ell (WithLp.ofLp v)

/-- **Symmetric** — in exactly the shape the bridge's `hPsym` binder wants. -/
theorem pAxCLM_symm (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) (u v : BondFnL2 L) :
    (inner ℝ u (pAxCLM S ell v) : ℝ) = (inner ℝ (pAxCLM S ell u) v : ℝ) := by
  show (inner ℝ u (pAxOp S ell v) : ℝ) = (inner ℝ (pAxOp S ell u) v : ℝ)
  rw [pAxOp, inner_bilinToOperatorBond, real_inner_comm, inner_bilinToOperatorBond, pAxBil_symm]

/-- **Positive semidefinite** — in exactly the shape the bridge's `hPpos` binder wants. -/
theorem pAxCLM_pos (S : Finset (PeriodicLatticeSite L)) (ell : ℕ) (v : BondFnL2 L) :
    (0 : ℝ) ≤ (inner ℝ v (pAxCLM S ell v) : ℝ) := by
  rw [inner_pAxCLM_eq']
  exact pAx_nonneg _ _ _

end Operator

#print axioms ofLp_add_apply
#print axioms ofLp_smul_apply
#print axioms pathIntegral_ofLp_add
#print axioms pathIntegral_ofLp_smul
#print axioms pAxBil
#print axioms pAxBil_apply
#print axioms pAxBil_symm
#print axioms pAxOp
#print axioms pAxCLM
#print axioms inner_pAxCLM_eq
#print axioms inner_pAxCLM_eq'
#print axioms pAxCLM_symm
#print axioms pAxCLM_pos

/-! ## §6. THE RESIDUAL OF `BridgeRestricted` §9, DISCHARGED AT THE CLOSED MODE

`BridgeRestricted.alternating_field_forces_P_coercive` says: supplying the bridge's `hDPa` at
`curvedRegularU` REQUIRES `(γ − δ)‖v‖² ≤ ⟨v, P v⟩` at `v = axisField 0 altC rotGen`. This section
computes both sides for `P := pAxCLM (CoarseLattice witL5 2) 2` and settles the demand exactly. -/

section Residual

open AdalyFormal.Balaban.BridgeRestricted (axisField altC rotGen rotGen_ne_zero)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)

/-- The `L²` norm of a bond field is its `bondEnergy`. -/
theorem norm_toLp_sq (A : Bond L → SuTwo) :
    ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 = bondEnergy A := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  show (∑ b : Bond L, (inner ℝ (A b) (A b) : ℝ)) = _
  exact Finset.sum_congr rfl (fun b _ => real_inner_self_eq_norm_sq (A b))

/-- The closed alternating mode, as a `BondFnL2` vector. -/
noncomputable abbrev altVec : BondFnL2 witL5 :=
  (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) altC rotGen) : BondFnL2 witL5)

theorem norm_altVec_sq : ‖altVec‖ ^ 2 = 216 * ‖rotGen‖ ^ 2 := by
  rw [norm_toLp_sq, bondEnergy_altField]

theorem inner_pAxCLM_altVec :
    (inner ℝ altVec (pAxCLM (CoarseLattice witL5 2) 2 altVec) : ℝ) = 108 * ‖rotGen‖ ^ 2 := by
  rw [inner_pAxCLM_eq, pAx_altField]

/-- **`P_Ax` SUPPLIES EXACTLY HALF THE NORM ON THE CLOSED MODE.** -/
theorem inner_pAxCLM_altVec_eq_half :
    (inner ℝ altVec (pAxCLM (CoarseLattice witL5 2) 2 altVec) : ℝ) = (1 / 2 : ℝ) * ‖altVec‖ ^ 2 := by
  rw [inner_pAxCLM_altVec, norm_altVec_sq]; ring

/-- **THE RESIDUAL, SETTLED — AND SHARP.** The demand
`BridgeRestricted.alternating_field_forces_P_coercive` places on `P` at the closed alternating mode
holds for the axial gauge-fixing operator **iff `γ − δ ≤ 1/2`**. Both directions are proved, so this
is not a one-sided sufficiency statement: `1/2` is the exact coercivity constant that CMP95
`(1.10)`'s gauge fixing, at unit weight, supplies on the mode `Δ_k` and `Q` both annihilate. -/
theorem pAxCLM_alternating_demand_iff (γ δ : ℝ) :
    ((γ - δ) * ‖altVec‖ ^ 2
        ≤ (inner ℝ altVec (pAxCLM (CoarseLattice witL5 2) 2 altVec) : ℝ))
      ↔ γ - δ ≤ (1 / 2 : ℝ) := by
  have hpos : (0 : ℝ) < ‖altVec‖ ^ 2 := by
    rw [norm_altVec_sq]
    have : 0 < ‖rotGen‖ ^ 2 := pow_pos (norm_pos_iff.2 rotGen_ne_zero) 2
    linarith
  rw [inner_pAxCLM_altVec_eq_half]
  constructor
  · intro h
    nlinarith [h, hpos]
  · intro h
    nlinarith [h, hpos]

end Residual

#print axioms norm_toLp_sq
#print axioms altVec
#print axioms norm_altVec_sq
#print axioms inner_pAxCLM_altVec
#print axioms inner_pAxCLM_altVec_eq_half
#print axioms pAxCLM_alternating_demand_iff

/-! ## §7. THE JOINT FORM — WHY `Q` CANNOT BE DROPPED (a proved no-go)

CMP95 printed p.19 asserts, without printed proof, that the quadratic form is positive on the
subspace `{QA = 0, A(Γ_{y,x}) = 0}`. The dispatch asks whether `⟨A, Δ_k A⟩ + P_Ax(A) ≥ c·bondEnergy A`
holds. This section answers the two-term question outright: **NO, and the source's own `QA = 0`
clause is exactly what is missing.**

`P_Ax` on an axis field is BLIND to the profile's values on ODD coordinate-`0` slices (§7a: at
`ell = 2` the one contributing contour's single direction-`0` bond always sits at the EVEN
coordinate `y₀`). `blockC` is such a profile — it is `∂φ` for `φ = 1{x₀ ∈ {0,1}}`, a function
constant on every block of side `2` — so it is annihilated by `Δ_k` (it is an axis field) AND by
`P_Ax` (odd support) while being nonzero. `Q` sees it (§7c), which is why this refutes the
TWO-term statement and CORROBORATES rather than contradicts the source's three-clause one. -/

section JointForm

open AdalyFormal.Balaban.BridgeRestricted (axisField axisField_pair altC rotGen rotGen_ne_zero
  toLp_axisField_ne_zero LinkFixed RMap_axisField_of_fixed
  RMap_periodicPathHolonomy_of_linkFixed curvedRegularU_linkFixes_rotGen zeroCoarseBond
  zeroCoarseBond_dir deltaKQuadFormNormalizedCorrected_axisField_eq_zero)
open AdalyFormal.Balaban.CoercivityRegular (curvedRegularU)
open AdalyFormal.Balaban.RegularUDomainWitness (witL5)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.Q1Real (rZeroA rZeroA_ell2 transportPath)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.BridgeInverse (qCLM qCLM_apply CoarseFnL2)

/-! ### §7a — `P_Ax` is blind to odd-slice axis profiles -/

/-- **`P_Ax` ANNIHILATES every axis field whose profile vanishes on the EVEN coordinate-`0`
slices.** General in `L`, general in `X`. The mechanism is §3's contour formula plus
`corner2_apply_zero`: at `ell = 2` the only nonempty direction-`0` segment is the single bond based
at `(y₀, x₁, x₂)`, and `y₀` is even because `y` is a coarse center. -/
theorem pAx_axisField_eq_zero_of_even_vanishing (c : PeriodicLatticeSite L → ℝ) (X : SuTwo)
    (h : ∀ z : PeriodicLatticeSite L, (z 0).val % 2 = 0 → c z = 0) :
    pAx (axisField (0 : Fin 3) c X) (CoarseLattice L 2) 2 = 0 := by
  rw [pAx_eq_zero_iff]
  intro y hy x hx
  have hyeven : (y 0).val % 2 = 0 := mem_CoarseLattice.1 hy 0
  have hb := mem_blockOf.1 (Finset.mem_erase.1 hx).2 0
  rw [pathIntegral_axisField]
  by_cases hcase : (x 0).val = (y 0).val + 1
  · rw [dirZeroSegment_succ y x hcase, Finset.sum_singleton]
    rw [show c ((corner2 y x, (0 : Fin 3)) : Bond L).1 = 0 from
      h (corner2 y x) (by rw [corner2_apply_zero]; exact hyeven), zero_smul]
  · rw [dirZeroSegment_eq_empty y x (by omega)]
    simp

/-! ### §7b — the block-constant potential and its gradient -/

/-- `∂φ` for `φ = 1{x₀ ∈ {0,1}}` on the `6`-site axis: supported on the ODD slices `x₀ ∈ {1,5}`,
value `−1` and `+1`. `φ` is constant on every block of side `2` along the `0`-axis, which is exactly
why `P_Ax` cannot see `∂φ`. -/
noncomputable def blockC (z : PeriodicLatticeSite witL5) : ℝ :=
  (if (z 0).val = 5 then (1 : ℝ) else 0) - (if (z 0).val = 1 then (1 : ℝ) else 0)

theorem blockC_transverse (z : PeriodicLatticeSite witL5) (ν : Fin 3) (hν : ν ≠ (0 : Fin 3)) :
    blockC (periodicLatticeShift z ν) = blockC z := by
  have hshift : (periodicLatticeShift z ν) 0 = z 0 := by
    show (Function.update z ν (z ν + 1)) 0 = z 0
    exact Function.update_of_ne (fun h => hν h.symm) _ _
  unfold blockC
  rw [hshift]

theorem blockC_even_eq_zero (z : PeriodicLatticeSite witL5) (h : (z 0).val % 2 = 0) :
    blockC z = 0 := by
  have h5 : ¬((z 0).val = 5) := by omega
  have h1 : ¬((z 0).val = 1) := by omega
  unfold blockC
  simp [h5, h1]

theorem blockC_top : blockC (fun _ => (5 : Fin (witL5 0 + 1))) = 1 := by
  have h : ((fun _ => (5 : Fin (witL5 0 + 1))) (0 : Fin 3)).val = 5 := by decide
  unfold blockC
  rw [h]
  norm_num

/-- **The block field is a `Δ_k` null direction** — it is an axis field over the link-fixed
`rotGen`, with a transverse-invariant profile, so `BridgeRestricted`'s §8a applies verbatim. -/
theorem deltaK_blockField_eq_zero :
    deltaKQuadFormNormalizedCorrected curvedRegularU (axisField (0 : Fin 3) blockC rotGen) = 0 :=
  deltaKQuadFormNormalizedCorrected_axisField_eq_zero curvedRegularU (0 : Fin 3) blockC rotGen
    curvedRegularU_linkFixes_rotGen blockC_transverse

/-- **And `P_Ax` misses it too** — `blockC` is supported on the odd slices. -/
theorem pAx_blockField_eq_zero :
    pAx (axisField (0 : Fin 3) blockC rotGen) (CoarseLattice witL5 2) 2 = 0 :=
  pAx_axisField_eq_zero_of_even_vanishing blockC rotGen blockC_even_eq_zero

theorem blockField_ne_zero :
    (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) blockC rotGen) : BondFnL2 witL5) ≠ 0 :=
  toLp_axisField_ne_zero (0 : Fin 3) blockC rotGen rotGen_ne_zero
    (fun _ => (5 : Fin (witL5 0 + 1))) (by rw [blockC_top]; norm_num)

/-- **THE NO-GO.** No `γ > 0` makes `⟨A, Δ_k A⟩ + P_Ax(A)` coercive on the whole bond space at
`curvedRegularU`. The two-term form CMP95 p.19 would need is false; the source's own `QA = 0`
clause is doing real work. -/
theorem deltaK_plus_pAx_not_coercive (γ : ℝ) (hγ : 0 < γ) :
    ¬ (∀ A : Bond witL5 → SuTwo,
        γ * ‖(WithLp.toLp 2 A : BondFnL2 witL5)‖ ^ 2
          ≤ deltaKQuadFormNormalizedCorrected curvedRegularU A
            + pAx A (CoarseLattice witL5 2) 2) := by
  intro hcoer
  have h := hcoer (axisField (0 : Fin 3) blockC rotGen)
  rw [deltaK_blockField_eq_zero, pAx_blockField_eq_zero] at h
  have hpos : 0 < ‖(WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) blockC rotGen) :
      BondFnL2 witL5)‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 blockField_ne_zero) 2
  nlinarith [h, hpos]

/-! ### §7c — the same field IS seen by `Q`, so the no-go corroborates the source's scope -/

/-- General-profile companion of `BridgeRestricted.rZeroA_axisField_eq_zero`: the two-term
transported line integral of an axis field over a link-fixed `X`, with NO alternation hypothesis. -/
theorem rZeroA_axisField_ell2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (c : PeriodicLatticeSite L → ℝ) (X : SuTwo) (hfix : LinkFixed U X)
    (cMinus x : PeriodicLatticeSite L) (μ : Fin 3) :
    rZeroA U cMinus x (axisField d c X) μ 2
      = (if μ = d then c x + c (periodicLatticeShift x d) else 0) • X := by
  rw [rZeroA_ell2,
    RMap_axisField_of_fixed _ d c X
      (RMap_periodicPathHolonomy_of_linkFixed U X hfix (transportPath cMinus x μ 0) cMinus) (x, μ),
    RMap_axisField_of_fixed _ d c X
      (RMap_periodicPathHolonomy_of_linkFixed U X hfix (transportPath cMinus x μ 1) cMinus)
      (periodicLatticeShift x μ, μ)]
  by_cases hmu : μ = d
  · subst hmu
    rw [if_pos rfl, if_pos rfl, if_pos rfl, ← add_smul]
  · rw [if_neg hmu, if_neg hmu, if_neg hmu, zero_smul, add_zero]

/-- The block, as a product Finset. -/
theorem blockOf_eq_piFinset (y : PeriodicLatticeSite L) (ell : ℕ) :
    blockOf y ell = Fintype.piFinset (fun μ : Fin 3 =>
      Finset.univ.filter (fun i : Fin (L μ + 1) =>
        (y μ).val ≤ i.val ∧ i.val < (y μ).val + ell)) := by
  ext x
  simp only [mem_blockOf, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A full (untruncated) block of side `2` on `witL5` has `2³ = 8` sites. -/
theorem card_blockOf_witL5 (y : PeriodicLatticeSite witL5)
    (hy : ∀ μ : Fin 3, (y μ).val % 2 = 0) : (blockOf y 2).card = 8 := by
  rw [blockOf_eq_piFinset, Fintype.card_piFinset]
  have key : ∀ j : Fin 3 → Fin 6, (∀ μ : Fin 3, (j μ).val % 2 = 0) →
      (∏ μ : Fin 3, (Finset.univ.filter (fun i : Fin 6 =>
          (j μ).val ≤ i.val ∧ i.val < (j μ).val + 2)).card) = 8 := by
    decide
  exact key y hy

/-- `blockC x + blockC (x + e₀) = −1` at every site of the block based at the origin: at `x₀ = 0`
the second term fires, at `x₀ = 1` the first does. -/
theorem blockC_pair_on_zero_block (x : PeriodicLatticeSite witL5)
    (hx : x ∈ blockOf (fun _ => (0 : Fin (witL5 0 + 1))) 2) :
    blockC x + blockC (periodicLatticeShift x (0 : Fin 3)) = -1 := by
  have hb := mem_blockOf.1 hx 0
  have hshift : (periodicLatticeShift x (0 : Fin 3)) 0 = x 0 + 1 := by
    show (Function.update x (0 : Fin 3) (x 0 + 1)) 0 = x 0 + 1
    exact Function.update_self _ _ _
  have h2 : (x 0).val < 2 := by simpa using (mem_blockOf.1 hx 0).2
  unfold blockC
  rw [hshift]
  have key : ∀ j : Fin (witL5 0 + 1), j.val < 2 →
      ((if j.val = 5 then (1 : ℝ) else 0) - (if j.val = 1 then (1 : ℝ) else 0))
        + ((if (j + 1).val = 5 then (1 : ℝ) else 0)
            - (if (j + 1).val = 1 then (1 : ℝ) else 0)) = -1 := by
    intro j hj
    fin_cases j
    all_goals first
      | (exfalso; revert hj; decide)
      | norm_num [Fin.add_def, witL5]
  exact key (x 0) h2

/-- **`Q` DOES see the block field**, at the coarse bond based at the origin in direction `0`:
`(QA)_b = (1/2⁴)·(−8)·rotGen = −½·rotGen ≠ 0`. -/
theorem lineCoarseRestrictCov_blockField :
    lineCoarseRestrictCov curvedRegularU 2 (axisField (0 : Fin 3) blockC rotGen) zeroCoarseBond
      = (-(1 / 2 : ℝ)) • rotGen := by
  have hzero : (zeroCoarseBond.1.1 : PeriodicLatticeSite witL5)
      = (fun _ => (0 : Fin (witL5 0 + 1))) := rfl
  show (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf zeroCoarseBond.1.1 2,
      rZeroA curvedRegularU zeroCoarseBond.1.1 x (axisField (0 : Fin 3) blockC rotGen)
        zeroCoarseBond.2 2 = _
  rw [zeroCoarseBond_dir]
  have hterm : ∀ x ∈ blockOf zeroCoarseBond.1.1 2,
      rZeroA curvedRegularU zeroCoarseBond.1.1 x (axisField (0 : Fin 3) blockC rotGen)
        (0 : Fin 3) 2 = (-1 : ℝ) • rotGen := by
    intro x hx
    rw [rZeroA_axisField_ell2 curvedRegularU (0 : Fin 3) blockC rotGen
      curvedRegularU_linkFixes_rotGen, if_pos rfl,
      blockC_pair_on_zero_block x (by rw [← hzero]; exact hx)]
  have h8 : (8 : ℕ) • ((-1 : ℝ) • rotGen) = (-8 : ℝ) • rotGen := by module
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_blockOf_witL5 _ (by decide), h8,
    smul_smul]
  norm_num

theorem qCLM_blockField_ne_zero :
    qCLM curvedRegularU 2
        (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) blockC rotGen) : BondFnL2 witL5) ≠ 0 := by
  intro hcon
  have h := congrFun (congrArg (fun u : CoarseFnL2 witL5 2 => WithLp.ofLp u) hcon) zeroCoarseBond
  rw [qCLM_apply, lineCoarseRestrictCov_blockField] at h
  have h0 : (-(1 / 2 : ℝ)) • rotGen = (0 : SuTwo) := h
  rcases smul_eq_zero.1 h0 with h1 | h1
  · norm_num at h1
  · exact rotGen_ne_zero h1

/-- **THE THREE-WAY PICTURE, IN ONE STATEMENT.** At `curvedRegularU`, block scale `2`, on `witL5`:

* the ALTERNATING mode is missed by `Δ_k` and by `Q`, and CAUGHT by `P_Ax` (§4);
* the BLOCK-GRADIENT mode is missed by `Δ_k` and by `P_Ax`, and CAUGHT by `Q` (§7).

So neither `P_Ax` nor `Q` is redundant, and `Δ_k + P_Ax` alone is not coercive. This is exactly the
shape of CMP95 p.19's own claim — positivity on `{QA = 0} ∩ {A(Γ) = 0}` — with the two
non-redundancy witnesses supplied as theorems rather than asserted. -/
theorem both_gauge_clauses_are_load_bearing :
    (deltaKQuadFormNormalizedCorrected curvedRegularU (axisField (0 : Fin 3) altC rotGen) = 0
        ∧ qCLM curvedRegularU 2 altVec = 0
        ∧ 0 < pAx (axisField (0 : Fin 3) altC rotGen) (CoarseLattice witL5 2) 2)
      ∧ (deltaKQuadFormNormalizedCorrected curvedRegularU (axisField (0 : Fin 3) blockC rotGen) = 0
        ∧ pAx (axisField (0 : Fin 3) blockC rotGen) (CoarseLattice witL5 2) 2 = 0
        ∧ qCLM curvedRegularU 2
            (WithLp.toLp 2 (axisField (L := witL5) (0 : Fin 3) blockC rotGen) :
              BondFnL2 witL5) ≠ 0) := by
  obtain ⟨h1, h2, _, h4⟩ := gauge_fixing_sees_the_closed_mode
  exact ⟨⟨h1, h2, h4⟩, ⟨deltaK_blockField_eq_zero, pAx_blockField_eq_zero,
    qCLM_blockField_ne_zero⟩⟩

end JointForm

#print axioms pAx_axisField_eq_zero_of_even_vanishing
#print axioms blockC
#print axioms blockC_transverse
#print axioms blockC_even_eq_zero
#print axioms blockC_top
#print axioms deltaK_blockField_eq_zero
#print axioms pAx_blockField_eq_zero
#print axioms blockField_ne_zero
#print axioms deltaK_plus_pAx_not_coercive
#print axioms rZeroA_axisField_ell2
#print axioms blockOf_eq_piFinset
#print axioms card_blockOf_witL5
#print axioms blockC_pair_on_zero_block
#print axioms lineCoarseRestrictCov_blockField
#print axioms qCLM_blockField_ne_zero
#print axioms both_gauge_clauses_are_load_bearing

/-! ## §8. WHAT `P_Ax` STRUCTURALLY CANNOT SEE — and the answer for the dipole witness

**This section is a NEGATIVE result about the source's own `(1.10)`, stated plainly.**

The `(1.7)` order switches coordinate `0` LAST. So on the first two segments of `Γ_{y,x}` — the
direction-`2` and direction-`1` runs — the bond's base coordinate `0` is pinned to `y₀`, and `y` is
a COARSE center, so `y₀ ≡ 0 (mod ell)`. Consequently **`P_Ax` is identically zero on every field
supported on transverse (`≠ 0`-direction) bonds whose base coordinate `0` is not a multiple of the
block side.** This is not a defect of this formalization: it is a property of `(1.10)`. The union
`⋃_y Ax(y)` is a spanning FOREST (`7` bonds per block at `ell = 2`, `189` of the `648` bonds of
`witL5`), not the whole bond set, and the gauge condition can only constrain what its contours
touch.

**The dipole witness.** `SplitBaseCase.Bax = ThirdLevelWitness.dipole a7 a7' 1 suTwoWitness` on
`witL7`, with `a7 = (1,0,0)` and `a7' = (1,0,1)`, is a direction-`1` dipole whose two bonds both sit
at coordinate-`0` value `1`. `1 % 2 = 1 ≠ 0` and `1 % 4 = 1 ≠ 0`, so
`pAx_dipole_at_odd_slice_eq_zero` applies at BOTH split levels: **`P_Ax(Bax) = 0`.** The axial
gauge-fixing form does NOT see the witness that refuted
`CStarLevelCorrected.LevelCorrectedCoercivityTargetUniform`, and does not repair that defect.
(That witness's own construction says why: `a7`'s docstring records it was chosen because
coordinate `0 = 1` is "OFF every level-4 staircase" — the very contours `(1.10)` is built on.)

This is stated as a general theorem rather than instantiated at `Bax` itself, because
`SplitBaseCase` is a live lane with no `.olean` in `.lake/build` at the time of writing; importing
it would make this module's build depend on a concurrently edited file (LAW-4). The instantiation
is one line once that lane settles. -/

section Blindness

/-- `corner1 y x` keeps `y`'s coordinate `0`. -/
theorem corner1_apply_zero (y x : PeriodicLatticeSite L) : (corner1 y x) 0 = y 0 := by
  show Function.update y 2 (x 2) 0 = y 0
  rw [Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)]

/-- **Coordinate `0` is pinned to `y₀` on every non-direction-`0` bond of `Γ_{y,x}`.** -/
theorem staircasePath_coord_zero {y x : PeriodicLatticeSite L} {b : Bond L}
    (hb : b ∈ staircasePath y x) (hd : b.2 ≠ 0) : b.1 0 = y 0 := by
  unfold staircasePath at hb
  rcases Finset.mem_union.1 hb with hb' | hb'
  · rcases Finset.mem_union.1 hb' with h | h
    · exact (mem_axisSegment.1 h).2.1 0 (by decide)
    · rw [(mem_axisSegment.1 h).2.1 0 (by decide)]
      exact corner1_apply_zero y x
  · exact absurd (mem_axisSegment.1 hb').1 hd

/-- **THE BLINDNESS THEOREM.** `P_Ax` annihilates every field whose support consists of transverse
bonds based OFF the coarse lattice in coordinate `0`. General `L`, general `ell`. -/
theorem pAx_eq_zero_of_support_off_coarse (A : Bond L → SuTwo) (ell : ℕ)
    (hA : ∀ b : Bond L, A b ≠ 0 → b.2 ≠ 0 ∧ (b.1 0).val % ell ≠ 0) :
    pAx A (CoarseLattice L ell) ell = 0 := by
  rw [pAx_eq_zero_iff]
  intro y hy _ _
  unfold pathIntegral
  refine Finset.sum_eq_zero (fun b hb => ?_)
  by_contra hne
  obtain ⟨hd, hmod⟩ := hA b hne
  rw [staircasePath_coord_zero hb hd] at hmod
  exact hmod (mem_CoarseLattice.1 hy 0)

/-- **`P_Ax` MISSES a transverse dipole sitting on the coordinate-`0` slice `1`**, at every block
side `ell ≥ 2`. This is exactly the shape of `SplitBaseCase.Bax` (`μ = 1`, both endpoints at
coordinate-`0` value `1`) at both levels of the `(2,4)` split. -/
theorem pAx_dipole_at_odd_slice_eq_zero
    (s s' : PeriodicLatticeSite L) (μ : Fin 3) (w : SuTwo) (ell : ℕ)
    (hell : 2 ≤ ell) (hμ : μ ≠ 0) (hs : (s 0).val = 1) (hs' : (s' 0).val = 1) :
    pAx (fun e : Bond L =>
      ((if e = (s, μ) then (1 : ℝ) else 0) - (if e = (s', μ) then (1 : ℝ) else 0)) • w)
      (CoarseLattice L ell) ell = 0 := by
  refine pAx_eq_zero_of_support_off_coarse _ ell (fun b hb => ?_)
  have hmod : (1 : ℕ) % ell ≠ 0 := by
    rw [Nat.mod_eq_of_lt (show (1 : ℕ) < ell by omega)]
    exact one_ne_zero
  by_cases h1 : b = (s, μ)
  · subst h1; exact ⟨hμ, by rw [hs]; exact hmod⟩
  · by_cases h2 : b = (s', μ)
    · subst h2; exact ⟨hμ, by rw [hs']; exact hmod⟩
    · exact absurd (by rw [if_neg h1, if_neg h2, sub_self, zero_smul] : _ = (0 : SuTwo)) hb

/-- **NON-VACUITY CONTROL FOR §8** (added after a nested validator flagged that
`pAx_dipole_at_odd_slice_eq_zero`'s hypotheses do not force `s ≠ s'` or `w ≠ 0`, so its statement
formally covers the identically-zero field). The dipole is a genuinely NONZERO field as soon as its
two sites differ and `w ≠ 0` — it takes the value `w` at `(s, μ)`. So §8's blindness result is a
statement about a field with strictly positive energy, not about `0`. `SplitBaseCase.Bax` is the
non-degenerate case: `a7 ≠ a7'` and `w = suTwoWitness ≠ 0`. -/
theorem dipole_field_ne_zero (s s' : PeriodicLatticeSite L) (μ : Fin 3) (w : SuTwo)
    (hss : s ≠ s') (hw : w ≠ 0) :
    (fun e : Bond L =>
        ((if e = (s, μ) then (1 : ℝ) else 0) - (if e = (s', μ) then (1 : ℝ) else 0)) • w)
      ≠ (fun _ => (0 : SuTwo)) := by
  intro h
  have hval := congrFun h (s, μ)
  rw [if_pos rfl, if_neg (by simp [Prod.mk.injEq, hss]), sub_zero, one_smul] at hval
  exact hw hval

/-- **§8's headline, with the non-degeneracy carried in the statement**: a nonzero transverse dipole
on the coordinate-`0` slice `1` is invisible to `P_Ax` at every block side `ell ≥ 2`. -/
theorem pAx_blind_to_nonzero_odd_slice_dipole
    (s s' : PeriodicLatticeSite L) (μ : Fin 3) (w : SuTwo) (ell : ℕ)
    (hell : 2 ≤ ell) (hμ : μ ≠ 0) (hs : (s 0).val = 1) (hs' : (s' 0).val = 1)
    (hss : s ≠ s') (hw : w ≠ 0) :
    (fun e : Bond L =>
        ((if e = (s, μ) then (1 : ℝ) else 0) - (if e = (s', μ) then (1 : ℝ) else 0)) • w)
        ≠ (fun _ => (0 : SuTwo))
      ∧ pAx (fun e : Bond L =>
          ((if e = (s, μ) then (1 : ℝ) else 0) - (if e = (s', μ) then (1 : ℝ) else 0)) • w)
        (CoarseLattice L ell) ell = 0 :=
  ⟨dipole_field_ne_zero s s' μ w hss hw,
    pAx_dipole_at_odd_slice_eq_zero s s' μ w ell hell hμ hs hs'⟩

end Blindness

#print axioms dipole_field_ne_zero
#print axioms pAx_blind_to_nonzero_odd_slice_dipole
#print axioms corner1_apply_zero
#print axioms staircasePath_coord_zero
#print axioms pAx_eq_zero_of_support_off_coarse
#print axioms pAx_dipole_at_odd_slice_eq_zero

/-! ## §9. WHAT `P_Ax` DOES CONTROL — the tree bonds, pointwise

§8 says what `(1.10)` cannot see. This section says what it does: **`P_Ax` bounds the energy of
every bond it does touch**, with an absolute constant, for an ARBITRARY field — no gauge condition,
no closedness, no background. The mechanism is the one CMP96 p.244's telescoping argument uses:
two contours of the same block differing only in the last (coordinate-`0`) step differ by exactly
one bond, so that bond's value is a DIFFERENCE of two contour integrals.

This is the half of CMP95 p.19's positivity claim that needs no curl and no `Q`, made
quantitative. -/

section TreeControl

/-- `Γ_{y,y}` is empty: all three sweeps are degenerate. -/
theorem staircasePath_self (y : PeriodicLatticeSite L) : staircasePath y y = ∅ := by
  unfold staircasePath
  rw [min_self, max_self, min_self, max_self, min_self, max_self,
    axisSegment_self_empty, axisSegment_self_empty, axisSegment_self_empty]
  simp

/-- **THE TELESCOPING IDENTITY.** If `x'` agrees with `x` in the transverse coordinates `1, 2` and
sits at `y`'s coordinate `0`, while `x` sits one step further, then `Γ_{y,x}` is `Γ_{y,x'}` plus the
single bond `((y₀, x₁, x₂), 0)` — so that bond's value is a difference of two contour integrals.
General `A`, general `L`, no coarse-alignment or block hypothesis. -/
theorem pathIntegral_succ_diff (A : Bond L → SuTwo) (y x x' : PeriodicLatticeSite L)
    (hsucc : (x 0).val = (y 0).val + 1)
    (h0 : x' 0 = y 0) (h1 : x' 1 = x 1) (h2 : x' 2 = x 2) :
    pathIntegral A y x - pathIntegral A y x' = A (corner2 y x, (0 : Fin 3)) := by
  have hc1 : corner1 y x' = corner1 y x := by
    show Function.update y 2 (x' 2) = Function.update y 2 (x 2)
    rw [h2]
  have hc2 : corner2 y x' = corner2 y x := by
    show Function.update (corner1 y x') 1 (x' 1) = Function.update (corner1 y x) 1 (x 1)
    rw [hc1, h1]
  have hsp' : staircasePath y x'
      = axisSegment y 2 (min (y 2).val (x 2).val) (max (y 2).val (x 2).val)
        ∪ axisSegment (corner1 y x) 1 (min (y 1).val (x 1).val) (max (y 1).val (x 1).val) := by
    show (axisSegment y 2 (min (y 2).val (x' 2).val) (max (y 2).val (x' 2).val)
        ∪ axisSegment (corner1 y x') 1 (min (y 1).val (x' 1).val) (max (y 1).val (x' 1).val))
        ∪ axisSegment (corner2 y x') 0 (min (y 0).val (x' 0).val)
            (max (y 0).val (x' 0).val) = _
    rw [h2, h1, hc1, hc2, h0, min_self, max_self, axisSegment_self_empty, Finset.union_empty]
  have hdisj : Disjoint (staircasePath y x') (dirZeroSegment y x) := by
    rw [Finset.disjoint_left]
    intro b hb hb0
    have hd0 : b.2 = 0 := (mem_axisSegment.1 hb0).1
    rw [hsp'] at hb
    rcases Finset.mem_union.1 hb with h | h
    · have hdd := (mem_axisSegment.1 h).1
      rw [hd0] at hdd
      exact absurd hdd (by decide)
    · have hdd := (mem_axisSegment.1 h).1
      rw [hd0] at hdd
      exact absurd hdd (by decide)
  have hsplit : staircasePath y x = staircasePath y x' ∪ dirZeroSegment y x := by
    rw [hsp']
    rfl
  unfold pathIntegral
  rw [hsplit, Finset.sum_union hdisj]
  show _ - ∑ b ∈ staircasePath y x', A b = _
  rw [dirZeroSegment_succ y x hsucc, Finset.sum_singleton]
  abel

theorem pAxBlock_le_pAx (A : Bond L → SuTwo) (S : Finset (PeriodicLatticeSite L)) (ell : ℕ)
    {y : PeriodicLatticeSite L} (hy : y ∈ S) : pAxBlock A ell y ≤ pAx A S ell :=
  Finset.single_le_sum (f := fun z => pAxBlock A ell z) (fun z _ => pAxBlock_nonneg A ell z) hy

theorem norm_sq_pathIntegral_le_pAxBlock (A : Bond L → SuTwo) (ell : ℕ)
    {y x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell) :
    ‖pathIntegral A y x‖ ^ 2 ≤ pAxBlock A ell y := by
  by_cases hxy : x = y
  · subst hxy
    unfold pathIntegral
    rw [staircasePath_self, Finset.sum_empty, norm_zero]
    simpa using pAxBlock_nonneg A ell x
  · exact Finset.single_le_sum (f := fun z => ‖pathIntegral A y z‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_erase.2 ⟨hxy, hx⟩)

/-- **`P_Ax` CONTROLS EVERY TREE BOND IT TOUCHES, with the absolute constant `4`.** For an
arbitrary field `A`, an arbitrary center set `S ∋ y` and an arbitrary block side, every bond of the
form `((y₀, x₁, x₂), 0)` reachable as the last step of a contour satisfies
`‖A b‖² ≤ 4 · P_Ax(A)`. No hypothesis on `A` whatsoever. -/
theorem norm_sq_tree_bond_le_pAx (A : Bond L → SuTwo) (S : Finset (PeriodicLatticeSite L))
    (ell : ℕ) (y x x' : PeriodicLatticeSite L) (hy : y ∈ S)
    (hx : x ∈ blockOf y ell) (hx' : x' ∈ blockOf y ell)
    (hsucc : (x 0).val = (y 0).val + 1)
    (h0 : x' 0 = y 0) (h1 : x' 1 = x 1) (h2 : x' 2 = x 2) :
    ‖A (corner2 y x, (0 : Fin 3))‖ ^ 2 ≤ 4 * pAx A S ell := by
  have hd := pathIntegral_succ_diff A y x x' hsucc h0 h1 h2
  have e1 : ‖pathIntegral A y x‖ ^ 2 ≤ pAx A S ell :=
    le_trans (norm_sq_pathIntegral_le_pAxBlock A ell hx) (pAxBlock_le_pAx A S ell hy)
  have e2 : ‖pathIntegral A y x'‖ ^ 2 ≤ pAx A S ell :=
    le_trans (norm_sq_pathIntegral_le_pAxBlock A ell hx') (pAxBlock_le_pAx A S ell hy)
  have htri : ‖A (corner2 y x, (0 : Fin 3))‖
      ≤ ‖pathIntegral A y x‖ + ‖pathIntegral A y x'‖ := by
    rw [← hd]
    exact norm_sub_le _ _
  nlinarith [htri, e1, e2, norm_nonneg (A (corner2 y x, (0 : Fin 3))),
    norm_nonneg (pathIntegral A y x), norm_nonneg (pathIntegral A y x'),
    sq_nonneg (‖pathIntegral A y x‖ - ‖pathIntegral A y x'‖)]

/-- **The control is NOT vacuous.** At the closed alternating mode, `P_Ax = 108‖rotGen‖²` and the
tree bond it touches carries `‖rotGen‖²` — the §9 bound reads `‖rotGen‖² ≤ 432‖rotGen‖²`, true and
with room, so §9's inequality is a genuine bound on a genuinely nonzero quantity rather than a
statement about zeros. -/
theorem tree_control_nonvacuous_at_altField :
    ‖(AdalyFormal.Balaban.BridgeRestricted.axisField (0 : Fin 3)
        AdalyFormal.Balaban.BridgeRestricted.altC
        AdalyFormal.Balaban.BridgeRestricted.rotGen)
      ((fun _ => 0 : PeriodicLatticeSite AdalyFormal.Balaban.RegularUDomainWitness.witL5),
        (0 : Fin 3))‖ ^ 2
      = ‖AdalyFormal.Balaban.BridgeRestricted.rotGen‖ ^ 2 := by
  rw [AdalyFormal.Balaban.BridgeRestricted.axisField_pair, if_pos rfl]
  exact norm_sq_altC_smul _

end TreeControl

#print axioms staircasePath_self
#print axioms pathIntegral_succ_diff
#print axioms pAxBlock_le_pAx
#print axioms norm_sq_pathIntegral_le_pAxBlock
#print axioms norm_sq_tree_bond_le_pAx
#print axioms tree_control_nonvacuous_at_altField

end AdalyFormal.Balaban.AxialCoercivity
