/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BridgeInverseCore
import AdalyFormal.Balaban.FullySupplied

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.longLine false

/-!
# `BridgeInverseAssembly.lean` — the bridge with `hG1` and `hTS` REMOVED, and the real `Q`

## §A — the abstract headline

`bridge_constructed` has the same conclusion as `RecursiveBridge.bridge_bare`, and its hypothesis
list contains **no `G`, no `T`, no `S`, no `hG1` and no `hTS`**. They are replaced by:

* `hDP` — coercivity of the GAUGE-FIXED fine operator `Δ_π + P` on the whole fine space, and
* `hQsurj` — surjectivity of the block average `Q`.

Everything else (`hadj`, symmetry of `Δ_π` and `P`, `0 ≤ a`, `‖Qx‖ ≤ q‖x‖`) already appeared in the
bridge. The operators `G₁ = (Δ_π+P+Q*aQ)⁻¹`, `T = QG₁Q*` and `S = (QG₁Q*)⁻¹` are the ones
`BridgeInverseCore` constructs.

## §B — the real lattice `Q`

`qCLM U ell` is `LineIntegralCovariant.lineCoarseRestrictCov U ell` — the campaign's faithful
covariant `Q_k(U)`, CMP95 (1.18)/CMP98 (125) — promoted to the `L²` carriers
`BondFnL2 L` and `CoarseFnL2 L ell`. `qstarCLM` is its genuine Hilbert-space adjoint, so `hadj` is a
theorem, not a hypothesis.

**Surjectivity of `Q` is discharged at `U = 1`** from `FullySupplied.qc_comp_suTwoLift` (the last-layer
lift is an exact right inverse). At a general background the exact-section identity is NOT available:
`qc_comp_suTwoLift` is stated at `trivialU` only, and the covariant transports along the `ell`
different paths reaching one fine bond do not cancel. §D therefore proves a *general* stability
criterion instead (`surjective_of_perturbation`), and §E carries the general-`U` route that needs no
smallness at all — `K := range Q`.

## Degeneracy, again

`0 < ell` and `∀ μ, ell ∣ L μ + 1` are carried everywhere `blockOf` is used (silent truncation
otherwise). The stronger `∀ μ, 2 * ell ≤ L μ + 1` — which excludes "the block IS the whole torus" —
is carried in `BridgeInverseCarrier.lean` where a single fine bond must be read off without wrap.
-/

namespace AdalyFormal.Balaban.BridgeInverse

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice
  mem_CoarseLattice coarseLattice_mem_fits)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCov_trivialU lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.FullySupplied (suTwoLift lineCoarseRestrictSuTwo_suTwoLift)

/-! ## §A — THE HEADLINE: the bridge with `hG1`, `hTS`, `G`, `T`, `S` all eliminated -/

section Headline

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- **THE BRIDGE, WITH BOTH ASSUMED INVERSES CONSTRUCTED.**

`(γ/q²)‖B‖² ≤ ⟨B, (QG₁Q*)⁻¹ B⟩ − a‖B‖²`, where `(QG₁Q*)⁻¹` is `sOp`, an operator this development
*builds*. `RecursiveBridge.bridge_bare`'s `hG1` and `hTS` do not appear: they are theorems
(`gOne_fineCLM_right`, `tOp_sOp`).

The `a`-cancellation is untouched — `fineCLM_coercive` keeps the `a‖Qx‖²` term, which is what
`bridge_bare` needs to make (3.156)'s `−a⟨B,B⟩` disappear exactly. -/
theorem bridge_constructed
    (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a γ q : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDsym : ∀ u v : H, (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hPsym : ∀ u v : H, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))
    (hQsurj : Function.Surjective Q)
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    (γ / q ^ 2) * ‖B‖ ^ 2
      ≤ (inner ℝ B
          (sOp Delta P Q Qstar a γ hadj hγ ha hDP
            (qstar_injective_of_surjective Q Qstar hadj hQsurj) B) : ℝ) - a * ‖B‖ ^ 2 := by
  have hQstar := qstar_injective_of_surjective Q Qstar hadj hQsurj
  refine AdalyFormal.Balaban.RecursiveBridge.bridge_bare (H := H) (K := K)
    (fun x => Q x) (fun C => Qstar C) (fun x => fineCLM Delta P Q Qstar a x)
    (fun x => gOne Delta P Q Qstar a γ hadj hγ ha hDP x)
    (tOp Delta P Q Qstar a γ hadj hγ ha hDP)
    (sOp Delta P Q Qstar a γ hadj hγ ha hDP hQstar)
    a γ q hadj (fun C => tOp_apply Delta P Q Qstar a γ hadj hγ ha hDP C)
    (fineCLM_symm Delta P Q Qstar a hadj hDsym hPsym)
    (fun x => gOne_fineCLM_right Delta P Q Qstar a γ hadj hγ ha hDP x)
    (fun C => tOp_sOp Delta P Q Qstar a γ hadj hγ ha hDP hQstar C)
    hγ hq ha ?_ hQ B
  intro C
  exact fineCLM_coercive Delta P Q Qstar a γ hadj hDP
    (gOne Delta P Q Qstar a γ hadj hγ ha hDP (Qstar C))

/-- **The (3.156) form with the source term, at the CONSTRUCTED `S`.** Kept separate from the
source-free statement above, exactly as `RecursiveBridge` insists. -/
theorem bridge_constructed_with_source
    (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a γ q ε : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDsym : ∀ u v : H, (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hPsym : ∀ u v : H, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))
    (hQsurj : Function.Surjective Q)
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖) (src : K → ℝ)
    (hsrc : ∀ B : K, |src B| ≤ ε * ‖B‖ ^ 2) (hthr : ε < γ / q ^ 2) (B : K) (hB : ‖B‖ ≠ 0) :
    0 < (inner ℝ B
          (sOp Delta P Q Qstar a γ hadj hγ ha hDP
            (qstar_injective_of_surjective Q Qstar hadj hQsurj) B) : ℝ) - a * ‖B‖ ^ 2 - src B :=
  AdalyFormal.Balaban.RecursiveBridge.deltaK_form_pos_of_threshold _ src (γ / q ^ 2) a ε B
    (bridge_constructed Delta P Q Qstar a γ q hadj hDsym hPsym hγ hq ha hDP hQsurj hQ B)
    (hsrc B) hthr hB

end Headline

/-! ## §D — SURJECTIVITY IS STABLE: a general-`U` criterion that needs no exact section

If `Q₀` has a right inverse `S₀` and `Q` differs from `Q₀` by less than `1` *after composing with
`S₀`*, then `Q` is still surjective. In finite dimension no Neumann series is needed: `id + E` with
`‖E‖ < 1` is injective, hence bijective.

This is the honest general-`U` statement for the block average: `FullySupplied.qc_comp_suTwoLift`
supplies `Q₀ = Q(1)` and `S₀ = suTwoLift`, and the hypothesis becomes the explicit smallness
`‖(Q(U) − Q(1)) ∘ suTwoLift‖ < 1` on the transports. -/

section Perturbation

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- `‖E‖ < 1` ⟹ `id + E` is injective. -/
theorem injective_id_add_of_norm_lt_one (E : K →L[ℝ] K) (hE : ‖E‖ < 1) :
    Function.Injective (ContinuousLinearMap.id ℝ K + E) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hval : x + E x = 0 := by simpa using hx
  have hxe : x = -(E x) := by rwa [add_eq_zero_iff_eq_neg] at hval
  have h1 : ‖E x‖ ≤ ‖E‖ * ‖x‖ := E.le_opNorm x
  have h2 : ‖x‖ = ‖E x‖ := by
    conv_lhs => rw [hxe]
    rw [norm_neg]
  have hle : ‖x‖ ≤ ‖E‖ * ‖x‖ := by linarith
  have hx0 : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x, hE, hle]
  exact norm_eq_zero.1 (le_antisymm hx0 (norm_nonneg x))

/-- **Surjectivity survives a perturbation smaller than the section.** -/
theorem surjective_of_perturbation (Q Q0 : H →L[ℝ] K) (S0 : K →L[ℝ] H)
    (hsec : ∀ B : K, Q0 (S0 B) = B)
    (hsmall : ‖(Q - Q0).comp S0‖ < 1) : Function.Surjective Q := by
  set E : K →L[ℝ] K := (Q - Q0).comp S0 with hE
  have hcomp : ∀ B : K, Q (S0 B) = (ContinuousLinearMap.id ℝ K + E) B := by
    intro B
    have hEB : E B = Q (S0 B) - Q0 (S0 B) := by
      simp [hE]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, hEB, hsec B]
    abel
  have hinj := injective_id_add_of_norm_lt_one E hsmall
  have hsurj : Function.Surjective (ContinuousLinearMap.id ℝ K + E) :=
    LinearMap.injective_iff_surjective.1 hinj
  intro B
  obtain ⟨C, hC⟩ := hsurj B
  exact ⟨S0 C, by rw [hcomp C, hC]⟩

end Perturbation

/-! ## §E — THE GENERAL-`U` ROUTE WITH NO SMALLNESS: corestrict to `range Q`

CMP99b writes `(QG₁Q*)⁻¹` with no domain qualification. On the full coarse space that symbol is
**ill-defined whenever `Q` is not surjective**: `QG₁Q*` annihilates `(ran Q)ᗮ` (proved below). The
only carrier on which the inverse can exist is `ran Q`, and there it exists unconditionally — no
smallness, no `U = 1`.

`Q` corestricted to `ran Q` is surjective by construction, so §A applies verbatim. -/

section RangeCarrier

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- **`Q G₁ Q*` KILLS `(ran Q)ᗮ`** — so `(QG₁Q*)⁻¹` cannot exist on the full coarse space unless `Q`
is surjective. This is a NEGATIVE result about the source's notation, and it is what forces the
corestriction below. It uses only `hadj`; nothing about `G₁`. -/
theorem compression_zero_on_orthogonal (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (G : H →L[ℝ] H)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (B : K) (hB : B ∈ (LinearMap.range (Q : H →ₗ[ℝ] K))ᗮ) :
    Q (G (Qstar B)) = 0 := by
  have hQB : Qstar B = 0 := by
    refine (qstar_eq_zero_iff_orthogonal Q Qstar hadj B).2 fun x => ?_
    have hz2 : (inner ℝ (Q x) B : ℝ) = 0 := hB (Q x) ⟨x, rfl⟩
    rw [← hz2]
    first
      | exact real_inner_comm _ _
      | exact (real_inner_comm _ _).symm
  rw [hQB, map_zero, map_zero]

/-- The corestriction of `Q` to its own range. -/
noncomputable def qRange (Q : H →L[ℝ] K) : H →L[ℝ] (LinearMap.range (Q : H →ₗ[ℝ] K)) :=
  ContinuousLinearMap.codRestrict Q (LinearMap.range (Q : H →ₗ[ℝ] K)) (fun x => ⟨x, rfl⟩)

theorem qRange_surjective (Q : H →L[ℝ] K) : Function.Surjective (qRange Q) := by
  rintro ⟨y, x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

/-- Non-vacuity of the range carrier: `Q ≠ 0` ⟹ `ran Q` is nontrivial. -/
theorem nontrivial_range (Q : H →L[ℝ] K) (hQ : Q ≠ 0) :
    Nontrivial (LinearMap.range (Q : H →ₗ[ℝ] K)) := by
  obtain ⟨x, hx⟩ : ∃ x : H, Q x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hQ (ContinuousLinearMap.ext hc)
  refine ⟨⟨⟨Q x, x, rfl⟩, 0, ?_⟩⟩
  intro hcon
  exact hx (congrArg Subtype.val hcon)

end RangeCarrier

end AdalyFormal.Balaban.BridgeInverse
