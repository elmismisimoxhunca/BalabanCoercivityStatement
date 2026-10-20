/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.ScaleInduction

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `Weitzenbock.lean` — the DISCRETE ENERGY WEITZENBÖCK IDENTITY on the periodic torus

`‖dA‖² + ‖d*A‖² = ‖∇A‖²` for `𝔰𝔲(2)`-valued bond fields, exactly (an equality, no constant), at
the flat background, on EVERY periodic extent `L` — no divisibility hypothesis, no regularity
hypothesis on a background, no dimension count.

## The three energies, and the normalisation convention (pinned, §0)

Both sides use the SAME `‖·‖` on `𝔰𝔲(2)`: the norm induced by `SuTwoInner.hsInner X Y =
-(1/2)·Tr(XY)` (`SuTwoInner.instNormedAddCommGroupSuTwo`), so `‖X‖² = hsInner X X`
(`inner_eq_hsInner` + `real_inner_self_eq_norm_sq`). That is the norm `bondEnergy`/`plaqEnergy`
already carry (`RegularUPerturbation` imports `SuTwoInner`, and no scoped matrix norm is opened
here — see `SuTwoInner`'s own instance-hazard note).

The RELATIVE normalisation of the three summands is the thing that can silently be off by a
factor, so it is gated by an INDEPENDENT hand count, compiled in §5: on the single-bond field
`w` at one bond,

`gradEnergy = 6‖w‖²`,  `plaqEnergy(curl) = 4‖w‖²`,  `divEnergy = 2‖w‖²`,  and `6 = 4 + 2`.

Those three numbers are computed in §5 from the *definitions*, with no appeal to §3's identity, so
a factor error in any one of the three would break §5 and not merely re-arrange it. Note where the
asymmetry lives: `plaqEnergy` runs over the plaquette type, whose direction component is
`{d : Fin 3 × Fin 3 // d.1 < d.2}` — the THREE UNORDERED pairs, with NO `1/2` — while
`gradEnergy` runs over ALL NINE ORDERED pairs `(μ, ν)`. The identity is true in exactly that
pairing; put a `1/2` on the plaquette side, or restrict `gradEnergy` to `μ < ν`, and it is false
(§5's count is what detects this).

## What is proved here

* §1 `dfwd A μ ν y = A(y+e_μ, ν) − A(y, ν)` — the forward difference of a bond field, over ALL
  ordered `(μ, ν)`; `gradEnergy`, `divEnergy`, and the two bilinear aggregates `Xt`, `Ct`.
* §2 the flat curl as an antisymmetrised difference, `curlValueCovariant (trivialU) A p =
  dfwd A μ ν x − dfwd A ν μ x`, and `plaqEnergy(curl)` expanded into `Xt`/`Ct`.
* §3 the SUMMATION BY PARTS lemma `sbp_cross` — `∑_y ⟪∂⁻_μA_μ, ∂⁻_νA_ν⟫ = ∑_y ⟪∂_μA_ν, ∂_νA_μ⟫`,
  for every ordered pair, on every extent — and `divEnergy = ∑_{μ,ν} Ct μ ν`.
* §4 **`weitzenbock_flat`** : `plaqEnergy (curl_1 A) + divEnergy 1 A = gradEnergy A`.
* §5 the independent numeric denotation gate (`6 = 4 + 2`) and the junk-attack inventory:
  `A = 0`, the one-site torus, and the `‖·‖`-vs-`hsInner` bridge.
* §6 the CONSUMER: `KerQDivFreePoincareAtLevel c` is REDUCED to a pure GRADIENT Poincaré on
  `ker Q_c(1)` — `kerQDivFreePoincareAtLevel_of_gradPoincareOnKerQ`. The reduction is where the
  identity earns its place: on the divergence-free constraint surface `divEnergy = 0`, so the
  curl energy IS the full gradient energy.
* §7 the fixed-level statement's OWN degenerate points, and why the reduction cannot be run
  against the level-UNIFORM statement (which `CoarseCurlPoincare.not_kerQDivFreePoincare`
  refutes).
* §8 the COVARIANT identity: the same computation at general `U`, with the curvature term written
  out as an explicit holonomy pairing (`curvTerm`), plus its vanishing at the flat background.

## Two lemmas re-derived here rather than imported, disclosed (LAW-19)

`Balaban/OneScaleRepaired.lean` already carries `shift_shiftBack_comm` (:627) and
`div_expand_trivialU` (:685; the `/-! §F3 -/` header is :683-684 — corrected after the validator
flagged the off-by-one). Both are re-proved here, with the same short proofs, for ONE reason:
that module is under concurrent edit by another lane, and this file is deliberately a LEAF whose
import closure contains no in-flux module. The statements are identical; the originals are the
first occurrences. ~~Nothing else in this file duplicates in-tree content~~ **SUPERSEDED (S75).
That claim was FALSE, and this lane's nested validator found it: `pathSite_add` was an exact
re-derivation of `FullReparamC.lean:616` and `pathSite_comm` a hypothesis-dropping restatement of
`ThirdLevelStokes.lean:133`. Both re-derivations are now DELETED and both originals are invoked
(§7). The claim that survives is narrower and was the only one actually measured:** `gradEnergy`,
`divEnergy` and the energy identity have no antecedent (exact-word grep, tree-wide, for
`gradEnergy`/`divEnergy`/`Weitzenb`: zero hits before this file), and `shiftVec3`, `Tloc`,
`sum_le_sum_of_surj`, `absorb0/1/2`, `mem_blockOf_eq_shiftVec3`, `pathSite_injective` were
re-checked by the validator with the same result.

`OneScaleRepaired.div_grad_component_eq_zero` (:696) is a DIFFERENT statement: pointwise, and
CONDITIONED on curl `= 0` AND div `= 0` (its `hstep` substitutes both to zero). This file's
identity is unconditional and quadratic.
-/

namespace AdalyFormal.Balaban.Weitzenbock

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer
  (trivialU gradCovariantAdjointValue periodicLatticeShiftBack periodicLatticeShift_shiftBack
    periodicLatticeShiftBack_shift periodicLatticeShiftEquiv)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — the normalisation bridge, stated once and used everywhere

`‖X‖² = hsInner X X` on `𝔰𝔲(2)`. Every squared norm below is this one; `bondEnergy` and
`plaqEnergy` are the tree's own sums of it. -/

theorem norm_sq_eq_hsInner (X : SuTwo) : ‖X‖ ^ 2 = hsInner X X := by
  rw [← inner_eq_hsInner, real_inner_self_eq_norm_sq]

theorem inner_eq_norm_sq_self (X : SuTwo) : inner ℝ X X = ‖X‖ ^ 2 :=
  real_inner_self_eq_norm_sq X

/-- Re-derivation, disclosed: identical to `OneScaleRepaired.shift_shiftBack_comm` (:627). Kept
local so this file's import closure holds no module under concurrent edit. -/
theorem shift_shiftBack_comm' (s : PeriodicLatticeSite L) (μ ν : Fin 3) :
    periodicLatticeShift (periodicLatticeShiftBack s ν) μ =
      periodicLatticeShiftBack (periodicLatticeShift s μ) ν := by
  by_cases h : μ = ν
  · subst h
    rw [periodicLatticeShift_shiftBack, periodicLatticeShiftBack_shift]
  · unfold periodicLatticeShift periodicLatticeShiftBack
    rw [Function.update_of_ne h, Function.update_of_ne (Ne.symm h)]
    exact Function.update_comm (Ne.symm h) _ _ s

/-- Two forward shifts commute, WITHOUT the distinctness hypothesis. `Lattice/Witness.lean`'s
`periodicLatticeShift_comm` (:60) is the same fact for `μ ≠ ν` (and is the original); the `μ = ν`
case is `rfl`, and dropping the hypothesis is what lets §3 run over ALL NINE ordered pairs in one
sum rather than splitting off the diagonal. Proved here rather than imported: `Lattice.Witness` is
outside this file's import closure and adding it would buy one 3-line case split. -/
theorem shift_shift_comm (s : PeriodicLatticeSite L) (μ ν : Fin 3) :
    periodicLatticeShift (periodicLatticeShift s μ) ν =
      periodicLatticeShift (periodicLatticeShift s ν) μ := by
  by_cases h : μ = ν
  · subst h; rfl
  · simp only [periodicLatticeShift]
    rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne h]
    exact Function.update_comm h (s μ + 1) (s ν + 1) s

#print axioms norm_sq_eq_hsInner
#print axioms shift_shiftBack_comm'
#print axioms shift_shift_comm

/-! ## §1 — the forward difference and the three energies -/

/-- **`(∂_μ A_ν)(y) := A(y + e_μ, ν) − A(y, ν)`** — the forward difference of a bond field in
direction `μ` of its `ν`-component, over ALL ordered pairs `(μ, ν)` (the plaquette type only
carries `μ < ν`, and both the gradient energy and the divergence need the unrestricted form). -/
noncomputable def dfwd (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : SuTwo :=
  A (periodicLatticeShift y μ, ν) - A (y, ν)

/-- **The full gradient energy `‖∇A‖² := ∑_y ∑_μ ∑_ν ‖(∂_μ A_ν)(y)‖²`** — all NINE ordered
direction pairs, one squared `𝔰𝔲(2)` norm each, no combinatorial factor. -/
noncomputable def gradEnergy (A : Bond L → SuTwo) : ℝ :=
  ∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, ‖dfwd A μ ν y‖ ^ 2

/-- **The divergence energy `‖d*A‖² := ∑_y ‖(D_U^*A)(y)‖²`**, at a general background `U` so §8
can reuse it; `divEnergy (trivialU L)` is the flat one. -/
noncomputable def divEnergy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  ∑ y : PeriodicLatticeSite L, ‖gradCovariantAdjointValue U A y‖ ^ 2

/-- `Xt A μ ν := ∑_y ‖(∂_μ A_ν)(y)‖²` — the `(μ,ν)` block of the gradient energy. -/
noncomputable def Xt (A : Bond L → SuTwo) (μ ν : Fin 3) : ℝ :=
  ∑ y : PeriodicLatticeSite L, ‖dfwd A μ ν y‖ ^ 2

/-- `Ct A μ ν := ∑_y ⟪(∂_μ A_ν)(y), (∂_ν A_μ)(y)⟫` — the CROSS term. This is the single object the
curl energy and the divergence energy disagree on, and §3 is the proof that they disagree by
exactly the same amount. -/
noncomputable def Ct (A : Bond L → SuTwo) (μ ν : Fin 3) : ℝ :=
  ∑ y : PeriodicLatticeSite L, inner ℝ (dfwd A μ ν y) (dfwd A ν μ y)

theorem gradEnergy_eq_sum_Xt (A : Bond L → SuTwo) :
    gradEnergy A = ∑ μ : Fin 3, ∑ ν : Fin 3, Xt A μ ν := by
  unfold gradEnergy Xt
  calc ∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, ‖dfwd A μ ν y‖ ^ 2
      = ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite L, ∑ ν : Fin 3, ‖dfwd A μ ν y‖ ^ 2 :=
        Finset.sum_comm
    _ = ∑ μ : Fin 3, ∑ ν : Fin 3, ∑ y : PeriodicLatticeSite L, ‖dfwd A μ ν y‖ ^ 2 :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_comm

theorem Ct_symm (A : Bond L → SuTwo) (μ ν : Fin 3) : Ct A μ ν = Ct A ν μ := by
  unfold Ct
  refine Finset.sum_congr rfl fun y _ => ?_
  exact real_inner_comm _ _

theorem Ct_diag (A : Bond L → SuTwo) (μ : Fin 3) : Ct A μ μ = Xt A μ μ := by
  unfold Ct Xt
  refine Finset.sum_congr rfl fun y _ => ?_
  exact inner_eq_norm_sq_self _

theorem Xt_nonneg (A : Bond L → SuTwo) (μ ν : Fin 3) : 0 ≤ Xt A μ ν := by
  unfold Xt
  refine Finset.sum_nonneg fun y _ => ?_
  exact sq_nonneg _

theorem gradEnergy_nonneg (A : Bond L → SuTwo) : 0 ≤ gradEnergy A := by
  unfold gradEnergy
  refine Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => ?_
  exact sq_nonneg _

theorem divEnergy_nonneg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : 0 ≤ divEnergy U A := by
  unfold divEnergy
  refine Finset.sum_nonneg fun y _ => ?_
  exact sq_nonneg _

#print axioms gradEnergy_eq_sum_Xt
#print axioms Ct_symm
#print axioms Ct_diag

/-! ## §2 — the flat curl energy in terms of `Xt` and `Ct` -/

/-- The flat curl is the ANTISYMMETRISED forward difference. -/
theorem curl_trivialU_eq_dfwd_sub (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    curlValueCovariant (trivialU L) A p =
      dfwd A p.2.1.1 p.2.1.2 p.1 - dfwd A p.2.1.2 p.2.1.1 p.1 := by
  have hR : ∀ b : Bond L, RMap (trivialU L b) = LinearMap.id := by
    intro b
    show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = LinearMap.id
    exact RMap_one
  simp only [curlValueCovariant, dfwd, hR, LinearMap.id_coe, id_eq]
  abel

/-- **The curl energy, expanded**: `∑_{μ<ν} (Xt μ ν + Xt ν μ − 2·Ct μ ν)`. The `−2·Ct` is the
cross term that §3 hands to the divergence. -/
theorem plaqEnergy_curl_trivialU (A : Bond L → SuTwo) :
    plaqEnergy (curlCovariantLM (trivialU L) A) =
      ∑ d : PeriodicPlaquetteDirections,
        (Xt A d.1.1 d.1.2 + Xt A d.1.2 d.1.1 - 2 * Ct A d.1.1 d.1.2) := by
  unfold plaqEnergy
  have hcoe : ∀ p : PeriodicLatticePlaquette L,
      curlCovariantLM (trivialU L) A p = curlValueCovariant (trivialU L) A p := fun _ => rfl
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => by
    rw [hcoe p, curl_trivialU_eq_dfwd_sub A p]]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hterm : ∀ y : PeriodicLatticeSite L,
      ‖dfwd A ((y, d) : PeriodicLatticePlaquette L).2.1.1
          ((y, d) : PeriodicLatticePlaquette L).2.1.2 ((y, d) : PeriodicLatticePlaquette L).1
        - dfwd A ((y, d) : PeriodicLatticePlaquette L).2.1.2
            ((y, d) : PeriodicLatticePlaquette L).2.1.1
            ((y, d) : PeriodicLatticePlaquette L).1‖ ^ 2
      = ‖dfwd A d.1.1 d.1.2 y‖ ^ 2 + ‖dfwd A d.1.2 d.1.1 y‖ ^ 2
        - 2 * inner ℝ (dfwd A d.1.1 d.1.2 y) (dfwd A d.1.2 d.1.1 y) := by
    intro y
    show ‖dfwd A d.1.1 d.1.2 y - dfwd A d.1.2 d.1.1 y‖ ^ 2 = _
    rw [norm_sub_sq_real]
    ring
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hterm y]
  unfold Xt Ct
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

#print axioms curl_trivialU_eq_dfwd_sub
#print axioms plaqEnergy_curl_trivialU

/-! ## §3 — SUMMATION BY PARTS: the divergence energy is the SUM of the cross terms

This is the whole content of the identity. The flat divergence at `y` is `−∑_μ ∂⁻_μ A_μ(y)` with
`∂⁻_μ A_μ(y) = A(y,μ) − A(y−e_μ,μ)`, so the divergence energy is `∑_{μ,ν} ∑_y ⟪∂⁻_μA_μ,
∂⁻_νA_ν⟫`. `sbp_cross` says each of those nine sums equals the corresponding curl cross term
`Ct μ ν`. Four terms per side, matched by three site-shift reindexings and one shift commutation;
translation invariance of the torus sum is the only geometric input, and NO hypothesis on `L` is
used. -/

/-- `ubk A μ y := ∂⁻_μ A_μ(y) = A(y, μ) − A(y − e_μ, μ)`, the backward difference of the
`μ`-component in direction `μ`, written as a `dfwd` at the shifted-back site. -/
noncomputable def ubk (A : Bond L → SuTwo) (μ : Fin 3) (y : PeriodicLatticeSite L) : SuTwo :=
  dfwd A μ μ (periodicLatticeShiftBack y μ)

theorem ubk_eq (A : Bond L → SuTwo) (μ : Fin 3) (y : PeriodicLatticeSite L) :
    ubk A μ y = A (y, μ) - A (periodicLatticeShiftBack y μ, μ) := by
  unfold ubk dfwd
  rw [periodicLatticeShift_shiftBack]

/-- Re-derivation, disclosed: identical to `OneScaleRepaired.div_expand_trivialU` (:685). -/
theorem div_expand_trivialU' (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) :
    gradCovariantAdjointValue (trivialU L) A y =
      ∑ ν : Fin 3, (A (periodicLatticeShiftBack y ν, ν) - A (y, ν)) := by
  have hRinv : ∀ b : Bond L, RMap (trivialU L b)⁻¹ = LinearMap.id := by
    intro b
    show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)⁻¹ = LinearMap.id
    rw [inv_one]; exact RMap_one
  unfold gradCovariantAdjointValue
  exact Finset.sum_congr rfl fun ν _ => by rw [hRinv]; simp

theorem div_eq_neg_sum_ubk (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) :
    gradCovariantAdjointValue (trivialU L) A y = - ∑ μ : Fin 3, ubk A μ y := by
  rw [div_expand_trivialU' A y, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [ubk_eq]
  abel

/-- **THE SUMMATION-BY-PARTS IDENTITY.** For every ordered pair `(μ, ν)` and every extent,
`∑_y ⟪∂⁻_μA_μ(y), ∂⁻_νA_ν(y)⟫ = ∑_y ⟪∂_μA_ν(y), ∂_νA_μ(y)⟫`. -/
theorem sbp_cross (A : Bond L → SuTwo) (μ ν : Fin 3) :
    (∑ y : PeriodicLatticeSite L, inner ℝ (ubk A μ y) (ubk A ν y)) = Ct A μ ν := by
  classical
  -- the four sums on the left
  have hleft : ∀ y : PeriodicLatticeSite L,
      inner ℝ (ubk A μ y) (ubk A ν y)
        = inner ℝ (A (y, μ)) (A (y, ν))
          - inner ℝ (A (y, μ)) (A (periodicLatticeShiftBack y ν, ν))
          - inner ℝ (A (periodicLatticeShiftBack y μ, μ)) (A (y, ν))
          + inner ℝ (A (periodicLatticeShiftBack y μ, μ))
              (A (periodicLatticeShiftBack y ν, ν)) := by
    intro y
    rw [ubk_eq, ubk_eq, inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  -- the four sums on the right
  have hright : ∀ y : PeriodicLatticeSite L,
      inner ℝ (dfwd A μ ν y) (dfwd A ν μ y)
        = inner ℝ (A (periodicLatticeShift y μ, ν)) (A (periodicLatticeShift y ν, μ))
          - inner ℝ (A (periodicLatticeShift y μ, ν)) (A (y, μ))
          - inner ℝ (A (y, ν)) (A (periodicLatticeShift y ν, μ))
          + inner ℝ (A (y, ν)) (A (y, μ)) := by
    intro y
    unfold dfwd
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  -- E1: the diagonal-site term, by symmetry of the real inner product
  have E1 : (∑ y : PeriodicLatticeSite L, inner ℝ (A (y, μ)) (A (y, ν)))
      = ∑ y : PeriodicLatticeSite L, (inner ℝ (A (y, ν)) (A (y, μ)) : ℝ) :=
    Finset.sum_congr rfl fun y _ => real_inner_comm _ _
  -- E2: reindex by the shift in direction ν
  have E2 : (∑ y : PeriodicLatticeSite L,
        (inner ℝ (A (y, ν)) (A (periodicLatticeShift y ν, μ)) : ℝ))
      = ∑ y : PeriodicLatticeSite L,
        (inner ℝ (A (y, μ)) (A (periodicLatticeShiftBack y ν, ν)) : ℝ) := by
    refine Fintype.sum_equiv (periodicLatticeShiftEquiv (L := L) ν) _ _ fun y => ?_
    show (inner ℝ (A (y, ν)) (A (periodicLatticeShift y ν, μ)) : ℝ)
      = inner ℝ (A (periodicLatticeShift y ν, μ))
          (A (periodicLatticeShiftBack (periodicLatticeShift y ν) ν, ν))
    rw [periodicLatticeShiftBack_shift]
    exact real_inner_comm _ _
  -- E3: reindex by the shift in direction μ
  have E3 : (∑ y : PeriodicLatticeSite L,
        (inner ℝ (A (periodicLatticeShift y μ, ν)) (A (y, μ)) : ℝ))
      = ∑ y : PeriodicLatticeSite L,
        (inner ℝ (A (periodicLatticeShiftBack y μ, μ)) (A (y, ν)) : ℝ) := by
    refine Fintype.sum_equiv (periodicLatticeShiftEquiv (L := L) μ) _ _ fun y => ?_
    show (inner ℝ (A (periodicLatticeShift y μ, ν)) (A (y, μ)) : ℝ)
      = inner ℝ (A (periodicLatticeShiftBack (periodicLatticeShift y μ) μ, μ))
          (A (periodicLatticeShift y μ, ν))
    rw [periodicLatticeShiftBack_shift]
    exact real_inner_comm _ _
  -- E4: the far-corner term. Reindexed by the DOUBLE shift `y ↦ y + e_μ + e_ν`, so that both
  -- backward differences land on the two forward-shifted sites at once. This is the only place
  -- both commutation lemmas are used.
  have E4 : (∑ y : PeriodicLatticeSite L,
        (inner ℝ (A (periodicLatticeShift y μ, ν)) (A (periodicLatticeShift y ν, μ)) : ℝ))
      = ∑ y : PeriodicLatticeSite L,
        (inner ℝ (A (periodicLatticeShiftBack y μ, μ))
          (A (periodicLatticeShiftBack y ν, ν)) : ℝ) := by
    refine Fintype.sum_equiv
      ((periodicLatticeShiftEquiv (L := L) μ).trans (periodicLatticeShiftEquiv (L := L) ν))
      _ _ fun y => ?_
    show (inner ℝ (A (periodicLatticeShift y μ, ν)) (A (periodicLatticeShift y ν, μ)) : ℝ)
      = inner ℝ
          (A (periodicLatticeShiftBack (periodicLatticeShift (periodicLatticeShift y μ) ν) μ, μ))
          (A (periodicLatticeShiftBack (periodicLatticeShift (periodicLatticeShift y μ) ν) ν, ν))
    rw [periodicLatticeShiftBack_shift, shift_shift_comm y μ ν,
      periodicLatticeShiftBack_shift]
    exact real_inner_comm _ _
  unfold Ct
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hleft y,
    Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hright y]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [E1, E2, E3, E4]
  ring

/-- **The divergence energy is the total cross term**: `divEnergy = ∑_{μ,ν} Ct μ ν`, all nine
ordered pairs. -/
theorem divEnergy_trivialU_eq_sum_Ct (A : Bond L → SuTwo) :
    divEnergy (trivialU L) A = ∑ μ : Fin 3, ∑ ν : Fin 3, Ct A μ ν := by
  unfold divEnergy
  have hterm : ∀ y : PeriodicLatticeSite L,
      ‖gradCovariantAdjointValue (trivialU L) A y‖ ^ 2
        = ∑ μ : Fin 3, ∑ ν : Fin 3, (inner ℝ (ubk A μ y) (ubk A ν y) : ℝ) := by
    intro y
    rw [div_eq_neg_sum_ubk, norm_neg, ← inner_eq_norm_sq_self, sum_inner]
    exact Finset.sum_congr rfl fun μ _ => inner_sum _ _ _
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hterm y]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => sbp_cross A μ ν

#print axioms ubk_eq
#print axioms div_expand_trivialU'
#print axioms div_eq_neg_sum_ubk
#print axioms sbp_cross
#print axioms divEnergy_trivialU_eq_sum_Ct

/-! ## §4 — THE IDENTITY -/

/-- The three unordered direction pairs, enumerated. -/
theorem sum_plaqDirs (f : PeriodicPlaquetteDirections → ℝ) :
    ∑ d : PeriodicPlaquetteDirections, f d
      = f ⟨(0, 1), by decide⟩ + f ⟨(0, 2), by decide⟩ + f ⟨(1, 2), by decide⟩ := by
  have huniv : (Finset.univ : Finset PeriodicPlaquetteDirections)
      = {⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩} := by decide
  rw [huniv]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- **THE DISCRETE ENERGY WEITZENBÖCK IDENTITY, flat background, EXACT.**

`plaqEnergy (curl_1 A) + divEnergy 1 A = gradEnergy A`

for every `𝔰𝔲(2)`-valued bond field `A` on every periodic extent `L`. No divisibility hypothesis,
no smallness hypothesis, no dimension count, no constant. -/
theorem weitzenbock_flat (A : Bond L → SuTwo) :
    plaqEnergy (curlCovariantLM (trivialU L) A) + divEnergy (trivialU L) A = gradEnergy A := by
  rw [plaqEnergy_curl_trivialU, divEnergy_trivialU_eq_sum_Ct, gradEnergy_eq_sum_Xt]
  rw [sum_plaqDirs]
  simp only [Fin.sum_univ_three]
  have c01 := Ct_symm A 0 1
  have c02 := Ct_symm A 0 2
  have c12 := Ct_symm A 1 2
  have d0 := Ct_diag A 0
  have d1 := Ct_diag A 1
  have d2 := Ct_diag A 2
  show Xt A 0 1 + Xt A 1 0 - 2 * Ct A 0 1
      + (Xt A 0 2 + Xt A 2 0 - 2 * Ct A 0 2)
      + (Xt A 1 2 + Xt A 2 1 - 2 * Ct A 1 2) + _ = _
  linarith [c01, c02, c12, d0, d1, d2]

#print axioms sum_plaqDirs
#print axioms weitzenbock_flat

/-! ## §5 — THE INDEPENDENT NUMERIC DENOTATION GATE, and the junk attacks

§4's identity is kernel-checked, so it cannot be "off by a factor and still look right" — but a
DEFINITION can denote something other than what its name says, and the identity would then be a
true statement about the wrong objects. So each of the three energies is evaluated here, from its
own definition and with NO appeal to `weitzenbock_flat`, on the single-bond field: value `w` on one
bond `(y₀, 0)`, zero elsewhere. Hand count (`compute/weitzenbock/PROGRESS.md` Step 3):

* `gradEnergy = 6‖w‖²` — for each of the 3 directions `μ`, exactly two `(y, ν)` pairs see a jump:
  `y = y₀` and `y = y₀ − e_μ`, at `ν = 0`.
* `plaqEnergy(curl) = 4‖w‖²` — the bond `(y₀,0)` sits in 4 plaquettes: base `y₀` and base
  `y₀ − e_ν`, for each of the two directions `ν ∈ {1,2}`. The `(1,2)` plaquettes never see it.
* `divEnergy = 2‖w‖²` — the divergence is `−w` at `y₀` (outflow) and `+w` at `y₀ + e_0` (inflow).

`6 = 4 + 2`. Restrict `gradEnergy` to `μ < ν` and it would be `2`, not `6`; put a `1/2` on the
plaquette side and it would be `2`, not `4`. Either mutation breaks these three theorems.
`0 < L μ` for every `μ` is load-bearing throughout: at `L μ = 0` the direction-`μ` shift is the
identity (`RegularUCurvedWitness.shift_ne_self_fails_at_zero_extent`) and every count above
collapses — that is the one-site-torus junk point, and §5c compiles it. -/

/-- The single-bond field: `w` at `b₀`, `0` at every other bond. -/
noncomputable def sbField (b0 : Bond L) (w : SuTwo) : Bond L → SuTwo :=
  fun b => if b = b0 then w else 0

theorem bondEnergy_sbField (b0 : Bond L) (w : SuTwo) :
    bondEnergy (sbField b0 w) = ‖w‖ ^ 2 := by
  unfold AdalyFormal.Balaban.RegularUPerturbation.bondEnergy sbField
  have hterm : ∀ b : Bond L, ‖(if b = b0 then w else 0)‖ ^ 2
      = if b = b0 then ‖w‖ ^ 2 else 0 := by
    intro b
    by_cases h : b = b0
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, norm_zero]
      ring
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hterm b,
    Finset.sum_ite_eq' Finset.univ b0 (fun _ => ‖w‖ ^ 2), if_pos (Finset.mem_univ _)]

/-- Both indicator conditions in a single forward difference of `sbField` cannot fire at once,
because the shift has no fixed point. This is the ONLY place `0 < L μ` enters §5a. -/
theorem dfwd_sbField_norm_sq (hL : ∀ μ : Fin 3, 0 < L μ) (b0 : Bond L) (w : SuTwo)
    (μ ν : Fin 3) (y : PeriodicLatticeSite L) :
    ‖dfwd (sbField b0 w) μ ν y‖ ^ 2
      = (if ((periodicLatticeShift y μ, ν) : Bond L) = b0 then ‖w‖ ^ 2 else 0)
        + (if ((y, ν) : Bond L) = b0 then ‖w‖ ^ 2 else 0) := by
  unfold dfwd sbField
  by_cases h1 : ((periodicLatticeShift y μ, ν) : Bond L) = b0
  · by_cases h2 : ((y, ν) : Bond L) = b0
    · exact absurd (congrArg Prod.fst (h1.trans h2.symm))
        (AdalyFormal.Balaban.RegularUCurvedWitness.shift_ne_self y μ (hL μ))
    · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, sub_zero]
      ring
  · by_cases h2 : ((y, ν) : Bond L) = b0
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, zero_sub, norm_neg]
      ring
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, sub_zero, norm_zero]
      ring

/-- `∑_y ∑_ν` of a bond indicator is `1` term, and the same after a shift reindexing. -/
theorem sum_bond_indicator (b0 : Bond L) (c : ℝ) :
    (∑ y : PeriodicLatticeSite L, ∑ ν : Fin 3, if ((y, ν) : Bond L) = b0 then c else 0) = c := by
  rw [← Fintype.sum_prod_type (f := fun b : Bond L => if b = b0 then c else 0),
    Finset.sum_ite_eq' Finset.univ b0 (fun _ => c), if_pos (Finset.mem_univ _)]

theorem sum_bond_indicator_shift (b0 : Bond L) (c : ℝ) (μ : Fin 3) :
    (∑ y : PeriodicLatticeSite L, ∑ ν : Fin 3,
        if ((periodicLatticeShift y μ, ν) : Bond L) = b0 then c else 0) = c := by
  rw [show (∑ y : PeriodicLatticeSite L, ∑ ν : Fin 3,
        if ((periodicLatticeShift y μ, ν) : Bond L) = b0 then c else 0)
      = ∑ y : PeriodicLatticeSite L, ∑ ν : Fin 3, if ((y, ν) : Bond L) = b0 then c else 0 from
    Fintype.sum_equiv (periodicLatticeShiftEquiv (L := L) μ) _ _ fun y => rfl]
  exact sum_bond_indicator b0 c

/-- **GATE 1: `gradEnergy` of the single-bond field is `6‖w‖²`** — six, not two: all nine ordered
pairs are summed and the diagonal `(μ, 0)` blocks are what carry the weight. -/
theorem gradEnergy_sbField (hL : ∀ μ : Fin 3, 0 < L μ) (b0 : Bond L) (w : SuTwo) :
    gradEnergy (sbField b0 w) = 6 * ‖w‖ ^ 2 := by
  have key : ∀ μ : Fin 3,
      (∑ y : PeriodicLatticeSite L, ∑ ν : Fin 3, ‖dfwd (sbField b0 w) μ ν y‖ ^ 2)
        = 2 * ‖w‖ ^ 2 := by
    intro μ
    have hin : ∀ y : PeriodicLatticeSite L,
        (∑ ν : Fin 3, ‖dfwd (sbField b0 w) μ ν y‖ ^ 2)
          = (∑ ν : Fin 3, if ((periodicLatticeShift y μ, ν) : Bond L) = b0 then ‖w‖ ^ 2 else 0)
            + ∑ ν : Fin 3, if ((y, ν) : Bond L) = b0 then ‖w‖ ^ 2 else 0 := by
      intro y
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ν _ => dfwd_sbField_norm_sq hL b0 w μ ν y
    rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hin y, Finset.sum_add_distrib,
      sum_bond_indicator_shift b0 (‖w‖ ^ 2) μ, sum_bond_indicator b0 (‖w‖ ^ 2)]
    ring
  unfold gradEnergy
  calc ∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, ‖dfwd (sbField b0 w) μ ν y‖ ^ 2
      = ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite L, ∑ ν : Fin 3,
          ‖dfwd (sbField b0 w) μ ν y‖ ^ 2 := Finset.sum_comm
    _ = 6 * ‖w‖ ^ 2 := by
        rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) => key μ]
        simp only [Fin.sum_univ_three]
        ring

#print axioms bondEnergy_sbField
#print axioms dfwd_sbField_norm_sq
#print axioms gradEnergy_sbField

/-! ### §5b — the curl and divergence counts, at the direction-`0` single bond

The plaquette type's direction component carries `μ < ν`, so the curl count is not symmetric in the
bond's direction as written; it is done at direction `0` and that restriction is disclosed rather
than waved away. `gradEnergy` above needed no such restriction. -/

theorem plaqEnergy_curl_sbField (hL : ∀ μ : Fin 3, 0 < L μ) (y0 : PeriodicLatticeSite L)
    (w : SuTwo) :
    plaqEnergy (curlCovariantLM (trivialU L) (sbField ((y0, 0) : Bond L) w)) = 4 * ‖w‖ ^ 2 := by
  set A := sbField ((y0, 0) : Bond L) w with hA
  -- the curl on a `(0, ν)` plaquette: only the two direction-`0` legs can be nonzero
  have hpair : ∀ ν : Fin 3, ν ≠ 0 → ∀ (h0 : (0 : Fin 3) < ν),
      (∑ x : PeriodicLatticeSite L,
        ‖curlValueCovariant (trivialU L) A (x, ⟨(0, ν), h0⟩)‖ ^ 2) = 2 * ‖w‖ ^ 2 := by
    intro ν hν h0
    have hterm : ∀ x : PeriodicLatticeSite L,
        ‖curlValueCovariant (trivialU L) A (x, ⟨(0, ν), h0⟩)‖ ^ 2
          = (if x = y0 then ‖w‖ ^ 2 else 0)
            + (if periodicLatticeShift x ν = y0 then ‖w‖ ^ 2 else 0) := by
      intro x
      rw [curl_trivialU_eq_dfwd_sub]
      show ‖dfwd A 0 ν x - dfwd A ν 0 x‖ ^ 2 = _
      unfold dfwd
      have hz1 : A (periodicLatticeShift x 0, ν) = 0 := by
        rw [hA]; unfold sbField
        rw [if_neg (fun h => hν (congrArg Prod.snd h))]
      have hz2 : A (x, ν) = 0 := by
        rw [hA]; unfold sbField
        rw [if_neg (fun h => hν (congrArg Prod.snd h))]
      have he1 : A (x, 0) = if x = y0 then w else 0 := by
        rw [hA]; unfold sbField
        by_cases h : x = y0
        · rw [if_pos h, if_pos (by rw [h] : ((x, 0) : Bond L) = (y0, 0))]
        · rw [if_neg h, if_neg (fun hc => h (congrArg Prod.fst hc))]
      have he2 : A (periodicLatticeShift x ν, 0) = if periodicLatticeShift x ν = y0 then w else 0 := by
        rw [hA]; unfold sbField
        by_cases h : periodicLatticeShift x ν = y0
        · rw [if_pos h, if_pos (by rw [h] : ((periodicLatticeShift x ν, 0) : Bond L) = (y0, 0))]
        · rw [if_neg h, if_neg (fun hc => h (congrArg Prod.fst hc))]
      rw [hz1, hz2, he1, he2]
      by_cases h1 : x = y0
      · have h2 : periodicLatticeShift x ν ≠ y0 := by
          rw [h1]
          exact AdalyFormal.Balaban.RegularUCurvedWitness.shift_ne_self y0 ν (hL ν)
        rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
        rw [show (0 : SuTwo) - 0 - ((0 : SuTwo) - w) = w by abel]
        ring
      · by_cases h2 : periodicLatticeShift x ν = y0
        · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
          rw [show (0 : SuTwo) - 0 - (w - 0) = -w by abel, norm_neg]
          ring
        · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
          rw [show (0 : SuTwo) - 0 - ((0 : SuTwo) - 0) = 0 by abel, norm_zero]
          ring
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hterm x, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ y0 (fun _ => ‖w‖ ^ 2), if_pos (Finset.mem_univ _)]
    rw [show (∑ x : PeriodicLatticeSite L, if periodicLatticeShift x ν = y0 then ‖w‖ ^ 2 else 0)
        = ∑ x : PeriodicLatticeSite L, if x = y0 then ‖w‖ ^ 2 else 0 from
      Fintype.sum_equiv (periodicLatticeShiftEquiv (L := L) ν) _ _ fun x => rfl]
    rw [Finset.sum_ite_eq' Finset.univ y0 (fun _ => ‖w‖ ^ 2), if_pos (Finset.mem_univ _)]
    ring
  -- the `(1,2)` plaquettes never see a direction-`0` bond
  have h12 : ∀ (h0 : (1 : Fin 3) < 2),
      (∑ x : PeriodicLatticeSite L,
        ‖curlValueCovariant (trivialU L) A (x, ⟨(1, 2), h0⟩)‖ ^ 2) = 0 := by
    intro h0
    have hterm : ∀ x : PeriodicLatticeSite L,
        ‖curlValueCovariant (trivialU L) A (x, ⟨(1, 2), h0⟩)‖ ^ 2 = 0 := by
      intro x
      rw [curl_trivialU_eq_dfwd_sub]
      show ‖dfwd A 1 2 x - dfwd A 2 1 x‖ ^ 2 = 0
      unfold dfwd
      have hz : ∀ (z : PeriodicLatticeSite L) (d : Fin 3), d ≠ 0 → A (z, d) = 0 := by
        intro z d hd
        rw [hA]; unfold sbField
        rw [if_neg (fun h => hd (congrArg Prod.snd h))]
      rw [hz _ 2 (by decide), hz _ 2 (by decide), hz _ 1 (by decide), hz _ 1 (by decide)]
      rw [show (0 : SuTwo) - 0 - ((0 : SuTwo) - 0) = 0 by abel, norm_zero]
      ring
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hterm x, Finset.sum_const_zero]
  unfold AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy
  have hcoe : ∀ p : PeriodicLatticePlaquette L,
      ‖curlCovariantLM (trivialU L) A p‖ ^ 2 = ‖curlValueCovariant (trivialU L) A p‖ ^ 2 :=
    fun _ => rfl
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hcoe p]
  rw [Fintype.sum_prod_type, Finset.sum_comm, sum_plaqDirs]
  rw [hpair 1 (by decide) (by decide), hpair 2 (by decide) (by decide), h12 (by decide)]
  ring

theorem divEnergy_sbField (hL : ∀ μ : Fin 3, 0 < L μ) (y0 : PeriodicLatticeSite L) (w : SuTwo) :
    divEnergy (trivialU L) (sbField ((y0, 0) : Bond L) w) = 2 * ‖w‖ ^ 2 := by
  set A := sbField ((y0, 0) : Bond L) w with hA
  have hterm : ∀ y : PeriodicLatticeSite L,
      ‖gradCovariantAdjointValue (trivialU L) A y‖ ^ 2
        = (if periodicLatticeShiftBack y 0 = y0 then ‖w‖ ^ 2 else 0)
          + (if y = y0 then ‖w‖ ^ 2 else 0) := by
    intro y
    rw [div_expand_trivialU']
    have hz : ∀ (z : PeriodicLatticeSite L) (d : Fin 3), d ≠ 0 → A (z, d) = 0 := by
      intro z d hd
      rw [hA]; unfold sbField
      rw [if_neg (fun h => hd (congrArg Prod.snd h))]
    have he : ∀ z : PeriodicLatticeSite L, A (z, 0) = if z = y0 then w else 0 := by
      intro z
      rw [hA]; unfold sbField
      by_cases h : z = y0
      · rw [if_pos h, if_pos (by rw [h] : ((z, 0) : Bond L) = (y0, 0))]
      · rw [if_neg h, if_neg (fun hc => h (congrArg Prod.fst hc))]
    rw [Fin.sum_univ_three]
    rw [hz _ 1 (by decide), hz _ 1 (by decide), hz _ 2 (by decide), hz _ 2 (by decide), he, he]
    have hcollapse : (if periodicLatticeShiftBack y 0 = y0 then w else 0)
          - (if y = y0 then w else 0) + ((0 : SuTwo) - 0) + ((0 : SuTwo) - 0)
        = (if periodicLatticeShiftBack y 0 = y0 then w else 0) - (if y = y0 then w else 0) := by
      abel
    rw [hcollapse]
    by_cases h1 : periodicLatticeShiftBack y 0 = y0
    · have h2 : y ≠ y0 := by
        intro hc
        rw [hc] at h1
        have h3 : periodicLatticeShift (periodicLatticeShiftBack y0 0) 0
            = periodicLatticeShift y0 0 :=
          congrArg (fun z => periodicLatticeShift z (0 : Fin 3)) h1
        rw [periodicLatticeShift_shiftBack] at h3
        exact AdalyFormal.Balaban.RegularUCurvedWitness.shift_ne_self y0 0 (hL 0) h3.symm
      rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, sub_zero]
      ring
    · by_cases h2 : y = y0
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, zero_sub, norm_neg]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, sub_zero, norm_zero]
        ring
  unfold divEnergy
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hterm y, Finset.sum_add_distrib]
  rw [show (∑ y : PeriodicLatticeSite L, if periodicLatticeShiftBack y 0 = y0 then ‖w‖ ^ 2 else 0)
      = ∑ y : PeriodicLatticeSite L, if y = y0 then ‖w‖ ^ 2 else 0 from
    Fintype.sum_equiv (periodicLatticeShiftEquiv (L := L) 0).symm _ _ fun y => rfl]
  rw [Finset.sum_ite_eq' Finset.univ y0 (fun _ => ‖w‖ ^ 2), if_pos (Finset.mem_univ _)]
  ring

/-- **THE GATE ITSELF**: the three independently computed numbers satisfy the identity, `4 + 2 = 6`,
on the single-bond field. Redundant with `weitzenbock_flat` as a statement — the point is that its
three inputs are computed from the DEFINITIONS in §5a/§5b and not from the identity. -/
theorem numeric_gate_six_eq_four_add_two (hL : ∀ μ : Fin 3, 0 < L μ)
    (y0 : PeriodicLatticeSite L) (w : SuTwo) :
    plaqEnergy (curlCovariantLM (trivialU L) (sbField ((y0, 0) : Bond L) w))
        + divEnergy (trivialU L) (sbField ((y0, 0) : Bond L) w)
      = gradEnergy (sbField ((y0, 0) : Bond L) w)
    ∧ plaqEnergy (curlCovariantLM (trivialU L) (sbField ((y0, 0) : Bond L) w)) = 4 * ‖w‖ ^ 2
    ∧ divEnergy (trivialU L) (sbField ((y0, 0) : Bond L) w) = 2 * ‖w‖ ^ 2
    ∧ gradEnergy (sbField ((y0, 0) : Bond L) w) = 6 * ‖w‖ ^ 2 := by
  refine ⟨?_, plaqEnergy_curl_sbField hL y0 w, divEnergy_sbField hL y0 w,
    gradEnergy_sbField hL _ w⟩
  rw [plaqEnergy_curl_sbField hL y0 w, divEnergy_sbField hL y0 w, gradEnergy_sbField hL _ w]
  ring

#print axioms plaqEnergy_curl_sbField
#print axioms divEnergy_sbField
#print axioms numeric_gate_six_eq_four_add_two

/-! ### §5c — the junk attacks, compiled

Each of these is a point at which the identity or a count above becomes content-free. They are
theorems so that none can ever be cited as evidence. -/

/-- `A = 0`: all three energies vanish. The identity holds and says nothing. -/
theorem all_energies_zero : plaqEnergy (curlCovariantLM (trivialU L) 0) = 0
    ∧ divEnergy (trivialU L) (0 : Bond L → SuTwo) = 0 ∧ gradEnergy (0 : Bond L → SuTwo) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy
    rw [map_zero]
    simp
  · unfold divEnergy
    have h : ∀ y : PeriodicLatticeSite L,
        gradCovariantAdjointValue (trivialU L) (0 : Bond L → SuTwo) y = 0 := by
      intro y
      rw [div_expand_trivialU']
      simp
    rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => by rw [h y, norm_zero]]
    simp
  · unfold gradEnergy
    have h : ∀ (μ ν : Fin 3) (y : PeriodicLatticeSite L),
        dfwd (0 : Bond L → SuTwo) μ ν y = 0 := by
      intro μ ν y; unfold dfwd; simp
    simp [h]

/-- **The ONE-SITE TORUS (`L = 0` in every direction) is the degenerate point of this whole file**:
every shift is the identity, so every forward difference, the curl, and the divergence are all
identically zero for EVERY field, and the identity reads `0 + 0 = 0`. The single-bond counts of
§5a/§5b are therefore FALSE there (`6‖w‖² ≠ 0` for `w ≠ 0`), which is exactly why `0 < L μ` is a
hypothesis of each of them. -/
theorem oneSiteTorus_collapses (A : Bond (fun _ => 0) → SuTwo) :
    gradEnergy A = 0 ∧ divEnergy (trivialU (fun _ => 0)) A = 0
      ∧ plaqEnergy (curlCovariantLM (trivialU (fun _ => 0)) A) = 0 := by
  have hshift : ∀ (y : PeriodicLatticeSite (fun _ => 0)) (μ : Fin 3),
      periodicLatticeShift y μ = y := fun y μ =>
    AdalyFormal.Balaban.RegularUCurvedWitness.shift_ne_self_fails_at_zero_extent y μ rfl
  have hback : ∀ (y : PeriodicLatticeSite (fun _ => 0)) (μ : Fin 3),
      periodicLatticeShiftBack y μ = y := by
    intro y μ
    have := hshift (periodicLatticeShiftBack y μ) μ
    rw [periodicLatticeShift_shiftBack] at this
    exact this.symm
  have hd : ∀ (μ ν : Fin 3) (y : PeriodicLatticeSite (fun _ => 0)), dfwd A μ ν y = 0 := by
    intro μ ν y; unfold dfwd; rw [hshift y μ, sub_self]
  refine ⟨?_, ?_, ?_⟩
  · unfold gradEnergy; simp [hd]
  · unfold divEnergy
    have h : ∀ y : PeriodicLatticeSite (fun _ => 0),
        gradCovariantAdjointValue (trivialU (fun _ => 0)) A y = 0 := by
      intro y
      rw [div_expand_trivialU']
      refine Finset.sum_eq_zero fun ν _ => ?_
      rw [hback y ν, sub_self]
    rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => by rw [h y, norm_zero]]
    simp
  · unfold AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy
    have h : ∀ p : PeriodicLatticePlaquette (fun _ => 0),
        ‖curlCovariantLM (trivialU (fun _ => 0)) A p‖ ^ 2 = 0 := by
      intro p
      show ‖curlValueCovariant (trivialU (fun _ => 0)) A p‖ ^ 2 = 0
      rw [curl_trivialU_eq_dfwd_sub, hd, hd, sub_zero, norm_zero]
      ring
    rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => h p]
    simp

#print axioms all_energies_zero
#print axioms oneSiteTorus_collapses

/-! ## §6 — THE CONSUMER: `KerQDivFreePoincareAtLevel c` reduces to a GRADIENT Poincaré on `ker Q`

`ScaleInduction.KerQDivFreePoincareAtLevel c` asks for `bondEnergy A ≤ K · plaqEnergy(curl A)` on
`ker Q_c(1) ∩ {d*A = 0}`. On that surface `divEnergy = 0`, so by §4 the curl energy IS the full
gradient energy, and the statement becomes a PURE GRADIENT Poincaré — `bondEnergy A ≤ K ·
gradEnergy A` — which no longer mentions the curl, the plaquette type, or the antisymmetrisation,
and which may be assumed on `ker Q_c(1)` WITHOUT the divergence clause (a strictly larger domain,
hence a strictly stronger hypothesis, so the reduction is sound in the direction claimed).

Nothing here proves the gradient Poincaré. §6b proves the LEVEL-UNIFORM version is FALSE, by
combining §4 with the tree's own refutation. -/

/-- **`[GRAD-POINCARE-ON-KERQ-AT-LEVEL c]`** — a Poincaré inequality for the FULL gradient energy
on `ker Q_c(1)`, at fixed level `c`, with NO divergence clause. `def : Prop` — open. -/
def GradPoincareOnKerQAtLevel (c : ℕ) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ (L : PeriodicLatticeExtent), (∀ μ : Fin 3, c ∣ (L μ + 1)) →
      ∀ (A : Bond L → SuTwo),
        (∀ b : CoarseBond L c, lineCoarseRestrictCov (trivialU L) c A b = 0) →
        bondEnergy A ≤ K * gradEnergy A

/-- **`[GRAD-POINCARE-ON-KERQ]`** — the same, LEVEL-UNIFORM (one `K` for every `ell`), the
analogue of `RegularUGamma0.KerQDivFreePoincare`. §6b refutes it. -/
def GradPoincareOnKerQ : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ (L : PeriodicLatticeExtent) (ell : ℕ), 0 < ell → (∀ μ : Fin 3, ell ∣ (L μ + 1)) →
      ∀ (A : Bond L → SuTwo),
        (∀ b : CoarseBond L ell, lineCoarseRestrictCov (trivialU L) ell A b = 0) →
        bondEnergy A ≤ K * gradEnergy A

theorem divEnergy_eq_zero_of_div_free
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (h : ∀ y : PeriodicLatticeSite L,
      gradCovariantAdjointValue U A y = 0) : divEnergy U A = 0 := by
  unfold divEnergy
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => by rw [h y, norm_zero]]
  simp

/-- **On the divergence-free surface the curl energy IS the gradient energy.** -/
theorem plaqEnergy_curl_eq_gradEnergy_of_div_free (A : Bond L → SuTwo)
    (h : ∀ y : PeriodicLatticeSite L, gradCovariantAdjointValue (trivialU L) A y = 0) :
    plaqEnergy (curlCovariantLM (trivialU L) A) = gradEnergy A := by
  have hw := weitzenbock_flat A
  rw [divEnergy_eq_zero_of_div_free (trivialU L) A h, add_zero] at hw
  exact hw

/-- **THE REDUCTION.** A gradient Poincaré on `ker Q_c(1)` at level `c` yields
`KerQDivFreePoincareAtLevel c` with the SAME constant. -/
theorem kerQDivFreePoincareAtLevel_of_gradPoincareOnKerQAtLevel {c : ℕ}
    (h : GradPoincareOnKerQAtLevel c) :
    AdalyFormal.Balaban.ScaleInduction.KerQDivFreePoincareAtLevel c := by
  obtain ⟨K, hK, hall⟩ := h
  refine ⟨K, hK, fun L hdvd A hker hdiv => ?_⟩
  have hb := hall L hdvd A hker
  rw [plaqEnergy_curl_eq_gradEnergy_of_div_free A hdiv]
  exact hb

/-- The level-uniform gradient Poincaré implies each fixed level. -/
theorem gradPoincareOnKerQAtLevel_of_gradPoincareOnKerQ {c : ℕ} (hc : 0 < c)
    (h : GradPoincareOnKerQ) : GradPoincareOnKerQAtLevel c := by
  obtain ⟨K, hK, hall⟩ := h
  exact ⟨K, hK, fun L hdvd A hker => hall L c hc hdvd A hker⟩

/-! ### §6b — the LEVEL-UNIFORM gradient Poincaré is FALSE

A derived no-go: §4 plus `CoarseCurlPoincare.not_kerQDivFreePoincare`. It says the gradient
Poincaré constant on `ker Q_ell(1)` MUST degrade with the level — consistent with, and independent
of, `ScaleInduction.revPBody_constant_forces_quadratic_growth`'s `K ≥ c²/512` for the reverse
Poincaré. It also localises where the remaining hope lives: FIXED level. -/

theorem kerQDivFreePoincare_of_gradPoincareOnKerQ (h : GradPoincareOnKerQ) :
    AdalyFormal.Balaban.RegularUGamma0.KerQDivFreePoincare := by
  obtain ⟨K, hK, hall⟩ := h
  refine ⟨K, hK, fun L ell hell hdvd A hker hdiv => ?_⟩
  have hb := hall L ell hell hdvd A hker
  rw [plaqEnergy_curl_eq_gradEnergy_of_div_free A hdiv]
  exact hb

theorem not_gradPoincareOnKerQ : ¬ GradPoincareOnKerQ := fun h =>
  AdalyFormal.Balaban.CoarseCurlPoincare.not_kerQDivFreePoincare
    (kerQDivFreePoincare_of_gradPoincareOnKerQ h)

/-! ## §7 — `GradPoincareOnKerQAtLevel 2` IS TRUE, with an ABSOLUTE constant

The constraint, unfolded (`lineCoarseRestrictCov_trivialU` + `lineCoarseRestrictSuTwo`): for every
`c ∈ CoarseLattice L 2` and every `μ`,

`∑_{x ∈ blockOf c 2} ∑_{i<2} A(pathSite x μ i, μ) = 0`

— ONE `𝔰𝔲(2)`-valued equation per (block, direction), i.e. the block average of the doubled line
sum. It is NOT a pointwise condition, and its codimension is a fixed fraction of the bond count.

**The proof, and why it is volume-uniform.** Every site is `shiftVec3 c n₀ n₁ n₂` for some coarse
`c` and offsets `< 2` (`coarseLattice_exists`), and every bond appearing in the constraint at `c` is
`shiftVec3 c m₀ m₁ m₂` with offsets `< 3`. Adding and subtracting `A(y,μ)` under the (vanishing)
constraint sum expresses `2N·A(y,μ)` as a sum of `2N` differences, each of which telescopes along a
FORWARD path from `c` of length `≤ 2` in each direction — so each is controlled by the LOCAL
gradient sum `Tloc c μ` over the `3×3×3` offset box at `c`. Cauchy–Schwarz
(`sq_sum_le_card_mul_sum_sq`) cancels `N` exactly, leaving `‖A(y,μ)‖² ≤ 144·Tloc c μ` with NO
dependence on the block cardinality, hence none on the volume. Summing uses only

* SURJECTIVITY of `(c, n) ↦ shiftVec3 c n` (all terms are `≥ 0`, so no tiling, disjointness or
  cardinality claim is needed anywhere), and
* INJECTIVITY of `c ↦ shiftVec3 c n` at each FIXED offset `n`, which is what keeps the constant
  absolute.

The constant delivered is `31104 = 8 · 144 · 27`. It is not sharp — the Fourier computation
recorded in `compute/weitzenbock/PROGRESS.md` Step 6 suggests the truth is near `6.5` — and no
sharpness is claimed. What matters is that it does not depend on `L`. -/

/-- The triple forward translation `c ↦ c + n₀e₀ + n₁e₁ + n₂e₂`, built from the tree's own
`QOne.pathSite` (LAW-19). Three `ℕ` arguments rather than an offset vector: membership in
`Finset.range 3` is then `Nat` arithmetic instead of `Fin`-function bookkeeping. -/
noncomputable def shiftVec3 (c : PeriodicLatticeSite L) (n0 n1 n2 : ℕ) :
    PeriodicLatticeSite L :=
  AdalyFormal.Balaban.QOne.pathSite
    (AdalyFormal.Balaban.QOne.pathSite
      (AdalyFormal.Balaban.QOne.pathSite c 2 n2) 1 n1) 0 n0

/-- **LAW-19 REUSE, not a re-derivation** — this is `FullReparamC.pathSite_add` (:616), restated
with the summands in the order the call sites below need. This lane's nested validator caught a
first version that re-proved it by induction; that induction is DELETED and the original is used. -/
theorem pathSite_add (z : PeriodicLatticeSite L) (ρ : Fin 3) (m n : ℕ) :
    AdalyFormal.Balaban.QOne.pathSite (AdalyFormal.Balaban.QOne.pathSite z ρ m) ρ n
      = AdalyFormal.Balaban.QOne.pathSite z ρ (n + m) := by
  rw [AdalyFormal.Balaban.FullReparamC.pathSite_add, Nat.add_comm]

/-- **LAW-19**: `ThirdLevelStokes.pathSite_comm` (:133) is the ORIGINAL, with the `ρ ≠ σ`
hypothesis; it is invoked here rather than re-proved. What is added is dropping the hypothesis (the
`ρ = σ` case, via `pathSite_add`) — the same generalization `shift_shift_comm` makes over
`Lattice/Witness.periodicLatticeShift_comm`. Also caught by the nested validator; the previous
`Function.Commute` re-derivation is DELETED. Note every call site in this file uses DISTINCT
directions, so the generalization is a convenience, not load-bearing. -/
theorem pathSite_comm (z : PeriodicLatticeSite L) (ρ σ : Fin 3) (m n : ℕ) :
    AdalyFormal.Balaban.QOne.pathSite (AdalyFormal.Balaban.QOne.pathSite z ρ m) σ n
      = AdalyFormal.Balaban.QOne.pathSite (AdalyFormal.Balaban.QOne.pathSite z σ n) ρ m := by
  by_cases h : ρ = σ
  · subst h
    rw [pathSite_add, pathSite_add, Nat.add_comm n m]
  · exact AdalyFormal.Balaban.ThirdLevelStokes.pathSite_comm z h m n

theorem pathSite_injective (ρ : Fin 3) (n : ℕ) :
    Function.Injective (fun z : PeriodicLatticeSite L =>
      AdalyFormal.Balaban.QOne.pathSite z ρ n) := by
  have hinj : Function.Injective
      (fun y : PeriodicLatticeSite L => periodicLatticeShift y ρ) :=
    (periodicLatticeShiftEquiv (L := L) ρ).injective
  exact hinj.iterate n

theorem shiftVec3_injective (n0 n1 n2 : ℕ) :
    Function.Injective (fun c : PeriodicLatticeSite L => shiftVec3 c n0 n1 n2) :=
  ((pathSite_injective (L := L) 0 n0).comp (pathSite_injective (L := L) 1 n1)).comp
    (pathSite_injective (L := L) 2 n2)

/-! ### §7a — the three coordinate readings of `shiftVec3` -/

theorem shiftVec3_coord0 (c : PeriodicLatticeSite L) (n0 n1 n2 : ℕ) :
    ((shiftVec3 c n0 n1 n2) 0).val = ((c 0).val + n0) % (L 0 + 1) := by
  unfold shiftVec3
  rw [AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_self_val,
    AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_ne _ 1 0 n1 (by decide),
    AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_ne _ 2 0 n2 (by decide)]

theorem shiftVec3_coord1 (c : PeriodicLatticeSite L) (n0 n1 n2 : ℕ) :
    ((shiftVec3 c n0 n1 n2) 1).val = ((c 1).val + n1) % (L 1 + 1) := by
  unfold shiftVec3
  rw [AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_ne _ 0 1 n0 (by decide),
    AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_self_val,
    AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_ne _ 2 1 n2 (by decide)]

theorem shiftVec3_coord2 (c : PeriodicLatticeSite L) (n0 n1 n2 : ℕ) :
    ((shiftVec3 c n0 n1 n2) 2).val = ((c 2).val + n2) % (L 2 + 1) := by
  unfold shiftVec3
  rw [AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_ne _ 0 2 n0 (by decide),
    AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_ne _ 1 2 n1 (by decide),
    AdalyFormal.Balaban.ReparamCDisjoint.pathSite_apply_self_val]

/-- Any site in the block `B(c, 2)` — in fact any site whose coordinates exceed `c`'s by less than
the extent — IS a `shiftVec3` of `c`, with the offsets read off coordinatewise. Only the
no-wraparound bound is used, so this covers the block AND its `+e_μ` translates. -/
theorem eq_shiftVec3_of_coords (c y : PeriodicLatticeSite L) (n0 n1 n2 : ℕ)
    (h0 : (c 0).val + n0 = (y 0).val) (h1 : (c 1).val + n1 = (y 1).val)
    (h2 : (c 2).val + n2 = (y 2).val) : y = shiftVec3 c n0 n1 n2 := by
  funext ρ
  apply Fin.ext
  have hcase : ρ = 0 ∨ ρ = 1 ∨ ρ = 2 := by omega
  rcases hcase with h | h | h
  · subst h
    rw [shiftVec3_coord0, h0, Nat.mod_eq_of_lt (y 0).isLt]
  · subst h
    rw [shiftVec3_coord1, h1, Nat.mod_eq_of_lt (y 1).isLt]
  · subst h
    rw [shiftVec3_coord2, h2, Nat.mod_eq_of_lt (y 2).isLt]

/-- **Every site is a `shiftVec3` of a coarse site, with offsets `< 2`.** This is the only place
`2 ∣ (L μ + 1)` is used (through `coarseLattice_exists`), and it is an EXISTENCE statement — no
tiling, uniqueness or cardinality claim is made or needed. -/
theorem exists_coarse_shiftVec3 (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (y : PeriodicLatticeSite L) :
    ∃ c ∈ CoarseLattice L 2, ∃ n0 n1 n2 : ℕ, n0 < 2 ∧ n1 < 2 ∧ n2 < 2
      ∧ y = shiftVec3 c n0 n1 n2 := by
  obtain ⟨c, hc, hblk⟩ := AdalyFormal.Balaban.AdmissibleSubspace.coarseLattice_exists
    (L := L) 2 (by norm_num) hdvd y
  rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf] at hblk
  refine ⟨c, hc, (y 0).val - (c 0).val, (y 1).val - (c 1).val, (y 2).val - (c 2).val, ?_, ?_, ?_, ?_⟩
  · have := hblk 0; omega
  · have := hblk 1; omega
  · have := hblk 2; omega
  · refine eq_shiftVec3_of_coords c y _ _ _ ?_ ?_ ?_
    · have := hblk 0; omega
    · have := hblk 1; omega
    · have := hblk 2; omega

/-- The `+e_μ` absorption: a unit `μ`-step off a `shiftVec3` is again a `shiftVec3` of the same
base, with the `μ`-offset raised by one. Three cases, because the three legs of `shiftVec3` sit in a
fixed order and the step must be commuted into position. -/
theorem pathSite_shiftVec3 (c : PeriodicLatticeSite L) (n0 n1 n2 i : ℕ) (μ : Fin 3) :
    ∃ m0 m1 m2 : ℕ, m0 ≤ n0 + i ∧ m1 ≤ n1 + i ∧ m2 ≤ n2 + i
      ∧ AdalyFormal.Balaban.QOne.pathSite (shiftVec3 c n0 n1 n2) μ i = shiftVec3 c m0 m1 m2 := by
  have hcase : μ = 0 ∨ μ = 1 ∨ μ = 2 := by omega
  rcases hcase with h | h | h
  · subst h
    refine ⟨n0 + i, n1, n2, by omega, by omega, by omega, ?_⟩
    unfold shiftVec3
    rw [pathSite_add]
    congr 1
    omega
  · subst h
    refine ⟨n0, n1 + i, n2, by omega, by omega, by omega, ?_⟩
    unfold shiftVec3
    rw [pathSite_comm _ 0 1 n0 i, pathSite_add]
    congr 2
    omega
  · subst h
    refine ⟨n0, n1, n2 + i, by omega, by omega, by omega, ?_⟩
    unfold shiftVec3
    rw [pathSite_comm _ 0 2 n0 i, pathSite_comm _ 1 2 n1 i, pathSite_add]
    congr 3
    omega

#print axioms shiftVec3_injective
#print axioms exists_coarse_shiftVec3
#print axioms pathSite_shiftVec3

/-! ### §7b — the local gradient sum, and the path bound -/

/-- `Tloc A c μ` — the gradient energy of the `μ`-component collected over the `3×3×3` forward
offset box at `c`, all three difference directions. Every path bound below lands inside it. -/
noncomputable def Tloc (A : Bond L → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) : ℝ :=
  ∑ ρ : Fin 3, ∑ n0 ∈ Finset.range 3, ∑ n1 ∈ Finset.range 3, ∑ n2 ∈ Finset.range 3,
    ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2

theorem Tloc_nonneg (A : Bond L → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) :
    0 ≤ Tloc A c μ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem single_le_Tloc (A : Bond L → SuTwo) (c : PeriodicLatticeSite L) (μ ρ : Fin 3)
    {n0 n1 n2 : ℕ} (h0 : n0 < 3) (h1 : n1 < 3) (h2 : n2 < 3) :
    ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2 ≤ Tloc A c μ := by
  unfold Tloc
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun r : Fin 3 => ∑ m0 ∈ Finset.range 3, ∑ m1 ∈ Finset.range 3, ∑ m2 ∈ Finset.range 3,
      ‖dfwd A r μ (shiftVec3 c m0 m1 m2)‖ ^ 2)
    (fun r _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ ρ))
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun m0 : ℕ => ∑ m1 ∈ Finset.range 3, ∑ m2 ∈ Finset.range 3,
      ‖dfwd A ρ μ (shiftVec3 c m0 m1 m2)‖ ^ 2)
    (fun m _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.mem_range.mpr h0))
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun m1 : ℕ => ∑ m2 ∈ Finset.range 3, ‖dfwd A ρ μ (shiftVec3 c n0 m1 m2)‖ ^ 2)
    (fun m _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_range.mpr h1))
  exact Finset.single_le_sum
    (f := fun m2 : ℕ => ‖dfwd A ρ μ (shiftVec3 c n0 n1 m2)‖ ^ 2)
    (fun m _ => sq_nonneg _) (Finset.mem_range.mpr h2)

/-- The one-direction telescoping identity: a difference of `A` along a straight forward path is the
sum of the unit forward differences along it. -/
theorem path_telescope (A : Bond L → SuTwo) (μ ρ : Fin 3) (z : PeriodicLatticeSite L) (n : ℕ) :
    A ((AdalyFormal.Balaban.QOne.pathSite z ρ n), μ) - A (z, μ)
      = ∑ i ∈ Finset.range n, dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i) := by
  induction n with
  | zero => rw [AdalyFormal.Balaban.QOne.pathSite_zero]; simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, AdalyFormal.Balaban.QOne.pathSite_succ]
    unfold dfwd
    abel

/-- The squared path bound in one direction, `n ≤ 2`, all sites inside the offset box at `c`. -/
theorem sq_norm_leg_le (A : Bond L → SuTwo) (μ ρ : Fin 3) (c : PeriodicLatticeSite L)
    (n0 n1 n2 n : ℕ) (h0 : n0 < 3) (h1 : n1 < 3) (h2 : n2 < 3) (hn : n ≤ 2)
    (habs : ∀ i, i < n → ∃ m0 m1 m2 : ℕ, m0 < 3 ∧ m1 < 3 ∧ m2 < 3
      ∧ AdalyFormal.Balaban.QOne.pathSite (shiftVec3 c n0 n1 n2) ρ i = shiftVec3 c m0 m1 m2) :
    ‖A ((AdalyFormal.Balaban.QOne.pathSite (shiftVec3 c n0 n1 n2) ρ n), μ)
        - A (shiftVec3 c n0 n1 n2, μ)‖ ^ 2 ≤ 4 * Tloc A c μ := by
  set z := shiftVec3 c n0 n1 n2 with hz
  have hstep : ∀ i ∈ Finset.range n,
      ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖ ^ 2 ≤ Tloc A c μ := by
    intro i hi
    obtain ⟨m0, m1, m2, hm0, hm1, hm2, heq⟩ := habs i (Finset.mem_range.mp hi)
    rw [heq]
    exact single_le_Tloc A c μ ρ hm0 hm1 hm2
  have htri : ‖A ((AdalyFormal.Balaban.QOne.pathSite z ρ n), μ) - A (z, μ)‖
      ≤ ∑ i ∈ Finset.range n, ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖ := by
    rw [path_telescope]
    exact norm_sum_le _ _
  have hsq : (∑ i ∈ Finset.range n, ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖) ^ 2
      ≤ (n : ℝ) * ∑ i ∈ Finset.range n,
        ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range n)
      (f := fun i => ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖)
    simpa using this
  have hsum : (∑ i ∈ Finset.range n, ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖ ^ 2)
      ≤ (n : ℝ) * Tloc A c μ := by
    calc (∑ i ∈ Finset.range n, ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖ ^ 2)
        ≤ ∑ _i ∈ Finset.range n, Tloc A c μ := Finset.sum_le_sum hstep
      _ = (n : ℝ) * Tloc A c μ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range n,
      ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast hn
  have hTnn := Tloc_nonneg A c μ
  calc ‖A ((AdalyFormal.Balaban.QOne.pathSite z ρ n), μ) - A (z, μ)‖ ^ 2
      ≤ (∑ i ∈ Finset.range n, ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ (n : ℝ) * ∑ i ∈ Finset.range n,
          ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖ ^ 2 := hsq
    _ ≤ 4 * Tloc A c μ := by
        have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hnT : (0 : ℝ) ≤ (n : ℝ) * Tloc A c μ := mul_nonneg hcast hTnn
        have s1 : (n : ℝ) * ∑ i ∈ Finset.range n,
              ‖dfwd A ρ μ (AdalyFormal.Balaban.QOne.pathSite z ρ i)‖ ^ 2
            ≤ (n : ℝ) * ((n : ℝ) * Tloc A c μ) := mul_le_mul_of_nonneg_left hsum hcast
        have s2 : (n : ℝ) * ((n : ℝ) * Tloc A c μ) ≤ 2 * ((n : ℝ) * Tloc A c μ) :=
          mul_le_mul_of_nonneg_right hn2 hnT
        have s3 : (n : ℝ) * Tloc A c μ ≤ 2 * Tloc A c μ :=
          mul_le_mul_of_nonneg_right hn2 hTnn
        linarith

#print axioms path_telescope
#print axioms sq_norm_leg_le

/-! ### §7c — the three absorption identities, and the full path bound from the block corner -/

theorem absorb2 (c : PeriodicLatticeSite L) (i : ℕ) :
    AdalyFormal.Balaban.QOne.pathSite (shiftVec3 c 0 0 0) 2 i = shiftVec3 c 0 0 i := by
  simp only [shiftVec3, AdalyFormal.Balaban.QOne.pathSite_zero]

theorem absorb1 (c : PeriodicLatticeSite L) (n2 i : ℕ) :
    AdalyFormal.Balaban.QOne.pathSite (shiftVec3 c 0 0 n2) 1 i = shiftVec3 c 0 i n2 := by
  simp only [shiftVec3, AdalyFormal.Balaban.QOne.pathSite_zero]

theorem absorb0 (c : PeriodicLatticeSite L) (n1 n2 i : ℕ) :
    AdalyFormal.Balaban.QOne.pathSite (shiftVec3 c 0 n1 n2) 0 i = shiftVec3 c i n1 n2 := by
  simp only [shiftVec3, AdalyFormal.Balaban.QOne.pathSite_zero]

theorem shiftVec3_zeros (c : PeriodicLatticeSite L) : shiftVec3 c 0 0 0 = c := by
  simp only [shiftVec3, AdalyFormal.Balaban.QOne.pathSite_zero]

/-- **The path bound from the block corner**: every site of the `3×3×3` offset box at `c` differs
from `c`, in the `μ`-component of `A`, by at most `36·Tloc`. Three legs, each `≤ 2` steps. -/
theorem sq_norm_shiftVec3_sub_le (A : Bond L → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3)
    (n0 n1 n2 : ℕ) (h0 : n0 < 3) (h1 : n1 < 3) (h2 : n2 < 3) :
    ‖A (shiftVec3 c n0 n1 n2, μ) - A (c, μ)‖ ^ 2 ≤ 36 * Tloc A c μ := by
  have hTnn := Tloc_nonneg A c μ
  -- leg 2
  have leg2 : ‖A (shiftVec3 c 0 0 n2, μ) - A (c, μ)‖ ^ 2 ≤ 4 * Tloc A c μ := by
    have := sq_norm_leg_le A μ 2 c 0 0 0 n2 (by norm_num) (by norm_num) (by norm_num)
      (by omega) (fun i hi => ⟨0, 0, i, by norm_num, by norm_num, by omega, absorb2 c i⟩)
    rwa [absorb2, shiftVec3_zeros] at this
  -- leg 1
  have leg1 : ‖A (shiftVec3 c 0 n1 n2, μ) - A (shiftVec3 c 0 0 n2, μ)‖ ^ 2
      ≤ 4 * Tloc A c μ := by
    have := sq_norm_leg_le A μ 1 c 0 0 n2 n1 (by norm_num) (by norm_num) h2
      (by omega) (fun i hi => ⟨0, i, n2, by norm_num, by omega, h2, absorb1 c n2 i⟩)
    rwa [absorb1] at this
  -- leg 0
  have leg0 : ‖A (shiftVec3 c n0 n1 n2, μ) - A (shiftVec3 c 0 n1 n2, μ)‖ ^ 2
      ≤ 4 * Tloc A c μ := by
    have := sq_norm_leg_le A μ 0 c 0 n1 n2 n0 (by norm_num) h1 h2
      (by omega) (fun i hi => ⟨i, n1, n2, by omega, h1, h2, absorb0 c n1 n2 i⟩)
    rwa [absorb0] at this
  have hsum : A (shiftVec3 c n0 n1 n2, μ) - A (c, μ)
      = (A (shiftVec3 c n0 n1 n2, μ) - A (shiftVec3 c 0 n1 n2, μ))
        + (A (shiftVec3 c 0 n1 n2, μ) - A (shiftVec3 c 0 0 n2, μ))
        + (A (shiftVec3 c 0 0 n2, μ) - A (c, μ)) := by abel
  have htri : ‖A (shiftVec3 c n0 n1 n2, μ) - A (c, μ)‖
      ≤ ‖A (shiftVec3 c n0 n1 n2, μ) - A (shiftVec3 c 0 n1 n2, μ)‖
        + ‖A (shiftVec3 c 0 n1 n2, μ) - A (shiftVec3 c 0 0 n2, μ)‖
        + ‖A (shiftVec3 c 0 0 n2, μ) - A (c, μ)‖ := by
    rw [hsum]
    exact le_trans (norm_add_le _ _) (by
      have := norm_add_le (A (shiftVec3 c n0 n1 n2, μ) - A (shiftVec3 c 0 n1 n2, μ))
        (A (shiftVec3 c 0 n1 n2, μ) - A (shiftVec3 c 0 0 n2, μ))
      linarith)
  have key3 : ∀ p q r : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ r → (p + q + r) ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + r ^ 2) := by
    intro p q r _ _ _
    nlinarith [sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (q - r)]
  have hstep : ‖A (shiftVec3 c n0 n1 n2, μ) - A (c, μ)‖ ^ 2
      ≤ (‖A (shiftVec3 c n0 n1 n2, μ) - A (shiftVec3 c 0 n1 n2, μ)‖
          + ‖A (shiftVec3 c 0 n1 n2, μ) - A (shiftVec3 c 0 0 n2, μ)‖
          + ‖A (shiftVec3 c 0 0 n2, μ) - A (c, μ)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hkey := key3 _ _ _ (norm_nonneg (A (shiftVec3 c n0 n1 n2, μ) - A (shiftVec3 c 0 n1 n2, μ)))
    (norm_nonneg (A (shiftVec3 c 0 n1 n2, μ) - A (shiftVec3 c 0 0 n2, μ)))
    (norm_nonneg (A (shiftVec3 c 0 0 n2, μ) - A (c, μ)))
  linarith

#print axioms absorb0
#print axioms sq_norm_shiftVec3_sub_le

/-! ### §7d — the constraint, and the pointwise bound it forces -/

theorem mem_blockOf_eq_shiftVec3 {c x : PeriodicLatticeSite L}
    (h : x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf c 2) :
    ∃ m0 m1 m2 : ℕ, m0 < 2 ∧ m1 < 2 ∧ m2 < 2 ∧ x = shiftVec3 c m0 m1 m2 := by
  rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf] at h
  refine ⟨(x 0).val - (c 0).val, (x 1).val - (c 1).val, (x 2).val - (c 2).val, ?_, ?_, ?_, ?_⟩
  · have := h 0; omega
  · have := h 1; omega
  · have := h 2; omega
  · refine eq_shiftVec3_of_coords c x _ _ _ ?_ ?_ ?_
    · have := h 0; omega
    · have := h 1; omega
    · have := h 2; omega

/-- **The `ker Q_2(1)` constraint, unfolded to the raw block sum.** -/
theorem block_constraint (A : Bond L → SuTwo)
    (hker : ∀ b : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    {c : PeriodicLatticeSite L}
    (hc : c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2) (μ : Fin 3) :
    ∑ x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf c 2,
      ∑ i ∈ Finset.range 2, A (AdalyFormal.Balaban.QOne.pathSite x μ i, μ) = 0 := by
  have h := hker (⟨c, hc⟩, μ)
  rw [AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov_trivialU] at h
  unfold AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo at h
  rw [smul_eq_zero] at h
  rcases h with h | h
  · exfalso
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · norm_num at h
    · norm_num at h
  · exact h

/-- **THE POINTWISE CONSEQUENCE.** On `ker Q_2(1)`, the `μ`-component of `A` at ANY site of the
offset box at a coarse `c` is controlled by the LOCAL gradient sum, with an absolute constant and NO
dependence on the block cardinality (Cauchy–Schwarz cancels it exactly). -/
theorem sq_norm_A_le_Tloc (A : Bond L → SuTwo)
    (hker : ∀ b : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    {c : PeriodicLatticeSite L}
    (hc : c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2) (μ : Fin 3)
    (d0 d1 d2 : ℕ) (hd0 : d0 < 3) (hd1 : d1 < 3) (hd2 : d2 < 3) :
    ‖A (shiftVec3 c d0 d1 d2, μ)‖ ^ 2 ≤ 144 * Tloc A c μ := by
  classical
  set y := shiftVec3 c d0 d1 d2 with hy
  set s := (AdalyFormal.Balaban.AdmissibleSubspace.blockOf c 2) ×ˢ (Finset.range 2) with hs
  have hTnn := Tloc_nonneg A c μ
  -- the constraint as a single sum over `s`
  have hzero : ∑ p ∈ s, A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) = 0 := by
    rw [hs, Finset.sum_product]
    exact block_constraint A hker hc μ
  -- `s` is nonempty: `c` itself is in its own block
  have hcmem : c ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf c 2 := by
    rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf]
    intro ρ
    exact ⟨le_refl _, by omega⟩
  have hcard : 1 ≤ s.card := by
    rw [hs]
    refine Finset.card_pos.mpr ⟨(c, 0), ?_⟩
    rw [Finset.mem_product]
    exact ⟨hcmem, Finset.mem_range.mpr (by norm_num)⟩
  have hcardR : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcard
  -- each of the `2N` differences is controlled
  have hterm : ∀ p ∈ s,
      ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ ^ 2
        ≤ 144 * Tloc A c μ := by
    intro p hp
    rw [hs, Finset.mem_product] at hp
    obtain ⟨m0, m1, m2, hm0, hm1, hm2, hxeq⟩ := mem_blockOf_eq_shiftVec3 hp.1
    have hi2 : p.2 < 2 := Finset.mem_range.mp hp.2
    obtain ⟨k0, k1, k2, hk0, hk1, hk2, hkeq⟩ :=
      pathSite_shiftVec3 c m0 m1 m2 p.2 μ
    have hz : AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2 = shiftVec3 c k0 k1 k2 := by
      rw [hxeq]; exact hkeq
    have hb0 : k0 < 3 := by omega
    have hb1 : k1 < 3 := by omega
    have hb2 : k2 < 3 := by omega
    have h1 := sq_norm_shiftVec3_sub_le A c μ k0 k1 k2 hb0 hb1 hb2
    have h2 := sq_norm_shiftVec3_sub_le A c μ d0 d1 d2 hd0 hd1 hd2
    rw [hz]
    have hsplit : A (shiftVec3 c k0 k1 k2, μ) - A (y, μ)
        = (A (shiftVec3 c k0 k1 k2, μ) - A (c, μ)) - (A (y, μ) - A (c, μ)) := by abel
    have htri : ‖A (shiftVec3 c k0 k1 k2, μ) - A (y, μ)‖
        ≤ ‖A (shiftVec3 c k0 k1 k2, μ) - A (c, μ)‖ + ‖A (y, μ) - A (c, μ)‖ := by
      rw [hsplit]; exact norm_sub_le _ _
    have key2 : ∀ p q : ℝ, (p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by
      intro p q
      nlinarith [sq_nonneg (p - q)]
    have hstep : ‖A (shiftVec3 c k0 k1 k2, μ) - A (y, μ)‖ ^ 2
        ≤ (‖A (shiftVec3 c k0 k1 k2, μ) - A (c, μ)‖ + ‖A (y, μ) - A (c, μ)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hkey := key2 ‖A (shiftVec3 c k0 k1 k2, μ) - A (c, μ)‖ ‖A (y, μ) - A (c, μ)‖
    linarith
  -- add and subtract `A(y,μ)` under the vanishing constraint sum
  have hid : ∑ p ∈ s, (A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ))
      = - (s.card • A (y, μ)) := by
    rw [Finset.sum_sub_distrib, hzero, Finset.sum_const, zero_sub]
  have hnormsmul : ‖s.card • A (y, μ)‖ = (s.card : ℝ) * ‖A (y, μ)‖ := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
    simp
  have hn1 : (s.card : ℝ) * ‖A (y, μ)‖
      ≤ ∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ := by
    rw [← hnormsmul, ← norm_neg, ← hid]
    exact norm_sum_le _ _
  have hn2 : (∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖) ^ 2
      ≤ (s.card : ℝ) * ∑ p ∈ s,
          ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := s)
      (f := fun p => ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖)
    simpa using this
  have hn3 : (∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ ^ 2)
      ≤ (s.card : ℝ) * (144 * Tloc A c μ) := by
    calc (∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ ^ 2)
        ≤ ∑ _p ∈ s, 144 * Tloc A c μ := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * (144 * Tloc A c μ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsq : ((s.card : ℝ) * ‖A (y, μ)‖) ^ 2
      ≤ (s.card : ℝ) * ((s.card : ℝ) * (144 * Tloc A c μ)) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) hn1 2) (le_trans hn2 ?_)
    exact mul_le_mul_of_nonneg_left hn3 (by positivity)
  have hfinal : (s.card : ℝ) ^ 2 * ‖A (y, μ)‖ ^ 2
      ≤ (s.card : ℝ) ^ 2 * (144 * Tloc A c μ) := by
    calc (s.card : ℝ) ^ 2 * ‖A (y, μ)‖ ^ 2 = ((s.card : ℝ) * ‖A (y, μ)‖) ^ 2 := by ring
      _ ≤ (s.card : ℝ) * ((s.card : ℝ) * (144 * Tloc A c μ)) := hsq
      _ = (s.card : ℝ) ^ 2 * (144 * Tloc A c μ) := by ring
  have hpos : (0 : ℝ) < (s.card : ℝ) ^ 2 := by positivity
  exact le_of_mul_le_mul_left (by linarith) hpos

#print axioms mem_blockOf_eq_shiftVec3
#print axioms block_constraint
#print axioms sq_norm_A_le_Tloc

/-! ### §7e — summing: surjectivity for the sites, injectivity for the offsets -/

/-- A nonnegative sum over a `Fintype` is dominated by a sum over ANY index set that surjects onto
it. No injectivity, no partition, no cardinality: this is what removes the need for a tiling law. -/
theorem sum_le_sum_of_surj {ι κ : Type*} [Fintype κ] [DecidableEq κ] (t : Finset ι) (φ : ι → κ)
    (F : κ → ℝ) (hF : ∀ k, 0 ≤ F k) (hsurj : ∀ k : κ, ∃ i ∈ t, φ i = k) :
    ∑ k : κ, F k ≤ ∑ i ∈ t, F (φ i) := by
  classical
  choose g hg hgφ using hsurj
  have hginj : Function.Injective g := by
    intro k k' h
    have hh : φ (g k) = φ (g k') := by rw [h]
    rw [hgφ, hgφ] at hh
    exact hh
  have h1 : ∑ j ∈ Finset.image g Finset.univ, F (φ j) = ∑ k : κ, F k := by
    rw [Finset.sum_image (fun x _ y _ h => hginj h)]
    exact Finset.sum_congr rfl fun k _ => by rw [hgφ]
  rw [← h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hF (φ j))
  intro j hj
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj
  rw [← hk]
  exact hg k

/-- At a FIXED offset, translating the coarse lattice is injective, so its gradient sum is bounded
by the global one. This is the step that keeps the final constant free of `L`. -/
theorem sum_coarse_shift_le (A : Bond L → SuTwo) (ρ μ : Fin 3) (n0 n1 n2 : ℕ) :
    (∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
        ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2)
      ≤ ∑ w : PeriodicLatticeSite L, ‖dfwd A ρ μ w‖ ^ 2 := by
  classical
  have himg : (∑ w ∈ Finset.image (fun c : PeriodicLatticeSite L => shiftVec3 c n0 n1 n2)
        (AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2), ‖dfwd A ρ μ w‖ ^ 2)
      = ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
          ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2 :=
    Finset.sum_image (fun x _ y _ h => shiftVec3_injective (L := L) n0 n1 n2 h)
  rw [← himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

/-- `∑_{c coarse} Tloc ≤ 27 · (the global gradient sum of the `μ`-component)`. -/
theorem sum_coarse_Tloc_le (A : Bond L → SuTwo) (μ : Fin 3) :
    (∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2, Tloc A c μ)
      ≤ 27 * ∑ ρ : Fin 3, Xt A ρ μ := by
  have hswap : (∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2, Tloc A c μ)
      = ∑ ρ : Fin 3, ∑ n0 ∈ Finset.range 3, ∑ n1 ∈ Finset.range 3, ∑ n2 ∈ Finset.range 3,
          ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
            ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2 := by
    unfold Tloc
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n0 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n1 _ => ?_
    rw [Finset.sum_comm]
  rw [hswap]
  have hbound : ∀ ρ : Fin 3,
      (∑ n0 ∈ Finset.range 3, ∑ n1 ∈ Finset.range 3, ∑ n2 ∈ Finset.range 3,
          ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
            ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2) ≤ 27 * Xt A ρ μ := by
    intro ρ
    have hin : ∀ n0 ∈ Finset.range 3, (∑ n1 ∈ Finset.range 3, ∑ n2 ∈ Finset.range 3,
        ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
          ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2) ≤ 9 * Xt A ρ μ := by
      intro n0 _
      have hin2 : ∀ n1 ∈ Finset.range 3, (∑ n2 ∈ Finset.range 3,
          ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
            ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2) ≤ 3 * Xt A ρ μ := by
        intro n1 _
        have hin3 : ∀ n2 ∈ Finset.range 3,
            (∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
              ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2) ≤ Xt A ρ μ := by
          intro n2 _
          exact sum_coarse_shift_le A ρ μ n0 n1 n2
        calc (∑ n2 ∈ Finset.range 3,
              ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
                ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2)
            ≤ ∑ _n2 ∈ Finset.range 3, Xt A ρ μ := Finset.sum_le_sum hin3
          _ = 3 * Xt A ρ μ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      calc (∑ n1 ∈ Finset.range 3, ∑ n2 ∈ Finset.range 3,
            ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
              ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2)
          ≤ ∑ _n1 ∈ Finset.range 3, 3 * Xt A ρ μ := Finset.sum_le_sum hin2
        _ = 9 * Xt A ρ μ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    calc (∑ n0 ∈ Finset.range 3, ∑ n1 ∈ Finset.range 3, ∑ n2 ∈ Finset.range 3,
          ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
            ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2)
        ≤ ∑ _n0 ∈ Finset.range 3, 9 * Xt A ρ μ := Finset.sum_le_sum hin
      _ = 27 * Xt A ρ μ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  calc (∑ ρ : Fin 3, ∑ n0 ∈ Finset.range 3, ∑ n1 ∈ Finset.range 3, ∑ n2 ∈ Finset.range 3,
        ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
          ‖dfwd A ρ μ (shiftVec3 c n0 n1 n2)‖ ^ 2)
      ≤ ∑ ρ : Fin 3, 27 * Xt A ρ μ := Finset.sum_le_sum fun ρ _ => hbound ρ
    _ = 27 * ∑ ρ : Fin 3, Xt A ρ μ := by rw [Finset.mul_sum]

/-- **The `μ`-component bound**: `∑_y ‖A(y,μ)‖² ≤ 31104 · ∑_ρ Xt A ρ μ` on `ker Q_2(1)`. -/
theorem sum_sq_component_le (A : Bond L → SuTwo) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hker : ∀ b : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 A b = 0) (μ : Fin 3) :
    (∑ y : PeriodicLatticeSite L, ‖A (y, μ)‖ ^ 2) ≤ 31104 * ∑ ρ : Fin 3, Xt A ρ μ := by
  classical
  set S := (AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2) ×ˢ
    ((Finset.range 2) ×ˢ ((Finset.range 2) ×ˢ (Finset.range 2))) with hS
  have hsurj : ∀ y : PeriodicLatticeSite L, ∃ q ∈ S,
      shiftVec3 q.1 q.2.1 q.2.2.1 q.2.2.2 = y := by
    intro y
    obtain ⟨c, hc, n0, n1, n2, h0, h1, h2, heq⟩ := exists_coarse_shiftVec3 hdvd y
    refine ⟨(c, n0, n1, n2), ?_, heq.symm⟩
    rw [hS, Finset.mem_product, Finset.mem_product, Finset.mem_product]
    exact ⟨hc, Finset.mem_range.mpr h0, Finset.mem_range.mpr h1, Finset.mem_range.mpr h2⟩
  have hstep1 : (∑ y : PeriodicLatticeSite L, ‖A (y, μ)‖ ^ 2)
      ≤ ∑ q ∈ S, ‖A (shiftVec3 q.1 q.2.1 q.2.2.1 q.2.2.2, μ)‖ ^ 2 :=
    sum_le_sum_of_surj S (fun q => shiftVec3 q.1 q.2.1 q.2.2.1 q.2.2.2)
      (fun y => ‖A (y, μ)‖ ^ 2) (fun _ => sq_nonneg _) hsurj
  have hstep2 : (∑ q ∈ S, ‖A (shiftVec3 q.1 q.2.1 q.2.2.1 q.2.2.2, μ)‖ ^ 2)
      ≤ ∑ q ∈ S, 144 * Tloc A q.1 μ := by
    refine Finset.sum_le_sum fun q hq => ?_
    rw [hS, Finset.mem_product, Finset.mem_product, Finset.mem_product] at hq
    exact sq_norm_A_le_Tloc A hker hq.1 μ _ _ _
      (by have := Finset.mem_range.mp hq.2.1; omega)
      (by have := Finset.mem_range.mp hq.2.2.1; omega)
      (by have := Finset.mem_range.mp hq.2.2.2; omega)
  have hstep3 : (∑ q ∈ S, 144 * Tloc A q.1 μ)
      = 8 * (144 * ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
          Tloc A c μ) := by
    rw [hS, Finset.sum_product]
    have hin : ∀ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
        (∑ _q ∈ (Finset.range 2) ×ˢ ((Finset.range 2) ×ˢ (Finset.range 2)),
          144 * Tloc A c μ) = 8 * (144 * Tloc A c μ) := by
      intro c _
      rw [Finset.sum_const, Finset.card_product, Finset.card_product, Finset.card_range,
        nsmul_eq_mul]
      norm_num
    rw [Finset.sum_congr rfl hin, ← Finset.mul_sum, ← Finset.mul_sum]
  have hstep4 := sum_coarse_Tloc_le A μ
  have hTnn : ∀ c : PeriodicLatticeSite L, 0 ≤ Tloc A c μ := fun c => Tloc_nonneg A c μ
  have hsum : (0 : ℝ) ≤ ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
      Tloc A c μ := Finset.sum_nonneg fun c _ => hTnn c
  calc (∑ y : PeriodicLatticeSite L, ‖A (y, μ)‖ ^ 2)
      ≤ ∑ q ∈ S, ‖A (shiftVec3 q.1 q.2.1 q.2.2.1 q.2.2.2, μ)‖ ^ 2 := hstep1
    _ ≤ ∑ q ∈ S, 144 * Tloc A q.1 μ := hstep2
    _ = 8 * (144 * ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
          Tloc A c μ) := hstep3
    _ ≤ 8 * (144 * (27 * ∑ ρ : Fin 3, Xt A ρ μ)) := by
        have : (144 : ℝ) * ∑ c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2,
            Tloc A c μ ≤ 144 * (27 * ∑ ρ : Fin 3, Xt A ρ μ) := by
          exact mul_le_mul_of_nonneg_left hstep4 (by norm_num)
        exact mul_le_mul_of_nonneg_left this (by norm_num)
    _ = 31104 * ∑ ρ : Fin 3, Xt A ρ μ := by ring

/-- **`GradPoincareOnKerQAtLevel 2` — PROVED, with the absolute constant `31104`.** -/
theorem gradPoincareOnKerQAtLevel_two : GradPoincareOnKerQAtLevel 2 := by
  refine ⟨31104, by norm_num, fun L hdvd A hker => ?_⟩
  have hcomp : bondEnergy A = ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite L, ‖A (y, μ)‖ ^ 2 := by
    unfold AdalyFormal.Balaban.RegularUPerturbation.bondEnergy
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hgrad : gradEnergy A = ∑ μ : Fin 3, ∑ ρ : Fin 3, Xt A ρ μ := by
    rw [gradEnergy_eq_sum_Xt, Finset.sum_comm]
  rw [hcomp, hgrad, Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  exact sum_sq_component_le A hdvd hker μ

/-- **`KerQDivFreePoincareAtLevel 2` — PROVED.** The fixed-level divergence-free reverse Poincaré at
`U = 1`, level `2`, with the absolute constant `31104`: `bondEnergy A ≤ 31104 · plaqEnergy(curl A)`
for every extent with `2 ∣ (L μ + 1)`, every `A ∈ ker Q_2(1)` with `d*A = 0`. It is §4's identity
that turns the curl energy into the full gradient energy, and §7 that bounds the bond energy by the
gradient energy on `ker Q_2(1)`.

This does NOT contradict `CoarseCurlPoincare.not_kerQDivFreePoincare`: that refutes the version with
ONE constant for ALL levels, and `not_gradPoincareOnKerQ` (§6b) shows independently that the
level-uniform form of the gradient Poincaré is false too. The constant here is specific to level
`2`. -/
theorem kerQDivFreePoincareAtLevel_two :
    AdalyFormal.Balaban.ScaleInduction.KerQDivFreePoincareAtLevel 2 :=
  kerQDivFreePoincareAtLevel_of_gradPoincareOnKerQAtLevel gradPoincareOnKerQAtLevel_two

/-! ### §7f — THE LEVEL-2 STATEMENT IS NOT VACUOUS

An `∃ K, ∀ ...` is worthless if the `∀`'s hypotheses are unsatisfiable, and this tree has already
compiled two such collapses at neighbouring levels: `ScaleInduction.kerQDivFreePoincareAtLevel_zero`
(unsatisfiable divisibility) and `_one` (`ker Q_1 = {0}`). So here is a witness at level `2`: a
NONZERO bond field on the two-sites-per-direction torus that is in `ker Q_2(1)` AND divergence-free
AND has nonzero curl energy. Both sides of the proved inequality are then strictly positive, so
`kerQDivFreePoincareAtLevel_two` is a statement about a nonempty domain and is not an instance of
either degeneracy above.

The field is the tree's own `CoarseCurlPoincare.coordField 0 1` with the ALTERNATING profile: all
weight on direction-`0` bonds, value `±w` according to the parity of coordinate `1`. It is
divergence-free for a structural reason — the divergence at `y` compares the direction-`0` bonds at
`y` and `y − e₀`, and shifting in direction `0` does not move coordinate `1` — and it is in
`ker Q_2` because the block sum of the alternating profile vanishes. Its curl does NOT vanish: the
`(0,1)` plaquette sees the profile change sign. -/

/-- The smallest extent admissible at level `2`: two sites per direction. -/
def twoExt : PeriodicLatticeExtent := fun _ => 1

theorem twoExt_dvd : ∀ μ : Fin 3, 2 ∣ (twoExt μ + 1) := by
  intro μ
  show 2 ∣ 2
  exact dvd_refl 2

/-- The alternating profile on the two sites of coordinate `1`. -/
noncomputable def altProfile : Fin (twoExt 1 + 1) → ℝ := fun t => if t = 0 then 1 else -1

theorem sum_altProfile : ∑ t : Fin (twoExt 1 + 1), altProfile t = 0 := by
  show ∑ t : Fin 2, altProfile t = 0
  rw [Fin.sum_univ_two]
  show altProfile 0 + altProfile 1 = 0
  unfold altProfile
  have h1 : ¬ ((1 : Fin (twoExt 1 + 1)) = 0) := by decide
  rw [if_pos rfl, if_neg h1]
  norm_num

/-- The non-vacuity witness. -/
noncomputable def nvField (w : SuTwo) : Bond twoExt → SuTwo :=
  AdalyFormal.Balaban.CoarseCurlPoincare.coordField 0 1 altProfile w

/-- On this extent the block at level `2` is the whole torus, so the `Q_2` block sum is a plain sum
over all sites. -/
theorem blockOf_twoExt_univ {c : PeriodicLatticeSite twoExt}
    (hc : c ∈ AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice twoExt 2) :
    AdalyFormal.Balaban.AdmissibleSubspace.blockOf c 2 = Finset.univ := by
  refine Finset.eq_univ_of_forall fun x => ?_
  rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf]
  intro μ
  have hmod := AdalyFormal.Balaban.AdmissibleSubspace.mem_CoarseLattice.mp hc μ
  have hcl : (c μ).val < 2 := (c μ).isLt
  have hxl : (x μ).val < 2 := (x μ).isLt
  omega

theorem nvField_kerQ (w : SuTwo) (b : CoarseBond twoExt 2) :
    lineCoarseRestrictCov (trivialU twoExt) 2 (nvField w) b = 0 := by
  classical
  rw [nvField, AdalyFormal.Balaban.CoarseCurlPoincare.Q_coordField 2 0 1 (by decide) altProfile w b]
  have hsum : ∑ x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf b.1.1 2,
      altProfile (x 1) = 0 := by
    rw [blockOf_twoExt_univ b.1.2]
    rw [show (∑ x ∈ (Finset.univ : Finset (PeriodicLatticeSite twoExt)), altProfile (x 1))
        = ∑ x : PeriodicLatticeSite twoExt, altProfile (x 1) from rfl,
      AdalyFormal.Balaban.CoarseCurlPoincare.sum_site_coord 1 altProfile, sum_altProfile, mul_zero]
  by_cases hc : b.2 = 0
  · rw [if_pos hc, hsum, mul_zero, mul_zero, zero_smul]
  · rw [if_neg hc, mul_zero, zero_smul]

theorem nvField_divFree (w : SuTwo) (y : PeriodicLatticeSite twoExt) :
    gradCovariantAdjointValue (trivialU twoExt) (nvField w) y = 0 := by
  rw [div_expand_trivialU']
  refine Finset.sum_eq_zero fun ν _ => ?_
  rw [nvField, AdalyFormal.Balaban.CoarseCurlPoincare.coordField_apply,
    AdalyFormal.Balaban.CoarseCurlPoincare.coordField_apply]
  by_cases hν : ν = 0
  · subst hν
    rw [if_pos rfl, if_pos rfl]
    show altProfile ((periodicLatticeShiftBack y 0) 1) • w - altProfile (y 1) • w = 0
    rw [AdalyFormal.Balaban.CoarseCurlPoincare.shiftBack_coord_ne (by decide : (1 : Fin 3) ≠ 0),
      sub_self]
  · rw [if_neg hν, if_neg hν, sub_self]

/-- The origin of the two-site torus. -/
def siteZero : PeriodicLatticeSite twoExt := fun _ => 0

theorem nvField_at_origin (w : SuTwo) : nvField w (siteZero, 0) = w := by
  rw [nvField, AdalyFormal.Balaban.CoarseCurlPoincare.coordField_apply, if_pos rfl]
  show altProfile (siteZero 1) • w = w
  have h : siteZero 1 = 0 := rfl
  rw [h]
  show altProfile 0 • w = w
  unfold altProfile
  rw [if_pos rfl, one_smul]

/-- The curl of the witness at the `(0,1)` plaquette based at the origin is `2w`. -/
theorem nvField_curl_at_origin (w : SuTwo) :
    curlCovariantLM (trivialU twoExt) (nvField w)
        (siteZero, ⟨(0, 1), by decide⟩) = (2 : ℝ) • w := by
  show curlValueCovariant (trivialU twoExt) (nvField w) (siteZero, ⟨(0, 1), by decide⟩) = _
  rw [curl_trivialU_eq_dfwd_sub]
  show dfwd (nvField w) 0 1 siteZero - dfwd (nvField w) 1 0 siteZero = _
  unfold dfwd
  have hz : ∀ z : PeriodicLatticeSite twoExt, nvField w (z, 1) = 0 := by
    intro z
    rw [nvField, AdalyFormal.Balaban.CoarseCurlPoincare.coordField_apply,
      if_neg (by decide : ¬ ((1 : Fin 3) = 0))]
  have h0 : nvField w (siteZero, 0) = w := nvField_at_origin w
  have h1 : nvField w (periodicLatticeShift siteZero 1, 0) = (-1 : ℝ) • w := by
    rw [nvField, AdalyFormal.Balaban.CoarseCurlPoincare.coordField_apply, if_pos rfl]
    show altProfile ((periodicLatticeShift siteZero 1) 1) • w = _
    rw [AdalyFormal.Balaban.CoarseCurlPoincare.shift_coord_self 1 siteZero]
    show altProfile (siteZero 1 + 1) • w = _
    have h : siteZero 1 + 1 = 1 := rfl
    rw [h]
    show altProfile 1 • w = _
    unfold altProfile
    rw [if_neg (by decide : ¬ ((1 : Fin (twoExt 1 + 1)) = 0))]
  rw [hz, hz, h0, h1]
  rw [show ((0 : SuTwo) - 0 - ((-1 : ℝ) • w - w)) = (2 : ℝ) • w by
    rw [neg_smul, one_smul]; module]

theorem bondEnergy_pos_of_ne (A : Bond L → SuTwo) (b0 : Bond L) (h : A b0 ≠ 0) :
    0 < bondEnergy A := by
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum
    (f := fun b : Bond L => ‖A b‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ b0))
  have : 0 < ‖A b0‖ := norm_pos_iff.mpr h
  positivity

theorem plaqEnergy_pos_of_ne (f : PeriodicLatticePlaquette L → SuTwo)
    (p0 : PeriodicLatticePlaquette L) (h : f p0 ≠ 0) : 0 < plaqEnergy f := by
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum
    (f := fun p : PeriodicLatticePlaquette L => ‖f p‖ ^ 2) (fun p _ => sq_nonneg _)
    (Finset.mem_univ p0))
  have : 0 < ‖f p0‖ := norm_pos_iff.mpr h
  positivity

/-- **NON-VACUITY, compiled.** At level `2`, on the two-site torus, the hypotheses of
`KerQDivFreePoincareAtLevel 2` are simultaneously satisfiable by a field with STRICTLY POSITIVE bond
energy AND strictly positive curl energy. So the proved inequality is not `0 ≤ 0`, and level `2` is
not one of `ScaleInduction`'s two degenerate levels. -/
theorem kerQDivFree_level_two_nonvacuous {w : SuTwo} (hw : w ≠ 0) :
    (∀ μ : Fin 3, 2 ∣ (twoExt μ + 1))
      ∧ (∀ b : CoarseBond twoExt 2, lineCoarseRestrictCov (trivialU twoExt) 2 (nvField w) b = 0)
      ∧ (∀ y : PeriodicLatticeSite twoExt,
          gradCovariantAdjointValue (trivialU twoExt) (nvField w) y = 0)
      ∧ 0 < bondEnergy (nvField w)
      ∧ 0 < plaqEnergy (curlCovariantLM (trivialU twoExt) (nvField w)) := by
  refine ⟨twoExt_dvd, nvField_kerQ w, nvField_divFree w, ?_, ?_⟩
  · exact bondEnergy_pos_of_ne (nvField w) (siteZero, 0) (by rw [nvField_at_origin]; exact hw)
  · refine plaqEnergy_pos_of_ne _ (siteZero, ⟨(0, 1), by decide⟩) ?_
    rw [nvField_curl_at_origin]
    intro hc
    rw [smul_eq_zero] at hc
    rcases hc with hc | hc
    · norm_num at hc
    · exact hw hc

#print axioms twoExt_dvd
#print axioms sum_altProfile
#print axioms blockOf_twoExt_univ
#print axioms nvField_kerQ
#print axioms nvField_divFree
#print axioms nvField_at_origin
#print axioms nvField_curl_at_origin
#print axioms bondEnergy_pos_of_ne
#print axioms plaqEnergy_pos_of_ne
#print axioms kerQDivFree_level_two_nonvacuous

#print axioms sum_le_sum_of_surj
#print axioms sum_coarse_shift_le
#print axioms sum_coarse_Tloc_le
#print axioms sum_sq_component_le
#print axioms gradPoincareOnKerQAtLevel_two
#print axioms kerQDivFreePoincareAtLevel_two

#print axioms divEnergy_eq_zero_of_div_free
#print axioms plaqEnergy_curl_eq_gradEnergy_of_div_free
#print axioms kerQDivFreePoincareAtLevel_of_gradPoincareOnKerQAtLevel
#print axioms gradPoincareOnKerQAtLevel_of_gradPoincareOnKerQ
#print axioms kerQDivFreePoincare_of_gradPoincareOnKerQ
#print axioms not_gradPoincareOnKerQ

end AdalyFormal.Balaban.Weitzenbock
