/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RecursiveBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `BridgeInverseCore.lean` — CONSTRUCTING the two operators the (3.10)→(3.156) bridge assumed

## What this module is for

`RecursiveBridge.bridge_from_fine_operator` (and every headline downstream of it) carries two
hypotheses that are the actual mathematics of CMP99b's (3.128)→(3.156) step:

* `hG1 : ∀ x, fineMapOf Delta P Q Qstar a (G x) = x` — `G` is a right inverse of the fine operator
  `Δ_π + P + Q*aQ`. Supplying it MEANS constructing Bałaban's `G₁`.
* `hTS : ∀ B, T (S B) = B` with `T = Q ∘ G ∘ Q*` — invertibility of `Q G₁ Q*`, which CMP99b p.421
  (3.129) and p.428 (3.156) USE as notation `(QG₁Q*)⁻¹` with no citation and no proof.

**This module builds both**, on a finite-dimensional carrier, and reduces them to exactly two
elementary facts:

1. **coercivity of the GAUGE-FIXED fine operator `Δ_π + P` on the whole fine space** — note
   `Δ_π + P`, not `Δ_π` alone: the `‖RD*A‖²` term of (3.128) is what restores ellipticity, and the
   campaign's own `RecursiveBridge.h310_unrestricted_forces_zero_norm_at_witnessU` together with
   `RecursiveBridge.toLp_deltaWitnessConfig_ne_zero` shows `Δ` alone has a kernel at `witnessU`.
   ⚠ `RecursiveBridge`'s prose cites this pair under the name
   `h310_unrestricted_impossible_at_witnessU`, which **does not exist as a declaration in that
   file** (nested-validator finding, 2026-07-28: 0 grep hits tree-wide). The combined statement is
   PROVED here, under exactly that name, in `BridgeInverseControls.lean` §12 — the "last
   millimetre" `‖v‖ = 0 → v = 0` that `RecursiveBridge` §9f reported blocked by the `PiLp` instance
   diamond goes through in this module's instance context; and
2. **injectivity of `Q*`, equivalently surjectivity of the block average `Q`** (§5 proves the
   equivalence).

Both are then FULLY discharged in `BridgeInverseAssembly.bridge_constructed`, where `hG1`, `hTS`,
`G`, `T` and `S` are all *eliminated* from `RecursiveBridge.bridge_bare`'s statement and replaced by
(1) and (2).

## Why finite dimension is the right hypothesis and not a dodge

The lattice carrier `BondFnL2 L = PiLp 2 (fun _ : Bond L => 𝔰𝔲(2))` IS finite-dimensional
(~~`DeltaKUnified.instFiniteDimensionalBFL2`~~ **WRONG NAME — corrected 2026-07-28 by a blind Sol
gate, verified here: that instance is declared on `DeltaKUnified.BFL2`, a DISTINCT fresh type
(`DeltaKUnified.lean:172`), NOT on `CovariantOperators.BondFnL2`. The proofs still elaborate because
synthesis finds a different valid chain — `WithLp.instModuleFinite` over
`SuTwoInner.instFiniteDimensionalSuTwo` — so nothing is broken, but the NAMED justification was
false. Claim-is-not-certificate: a docstring citing an instance that does not apply to the type in
question.**; `Bond L` is a `Fintype` and `𝔰𝔲(2)` is 3-dimensional
over `ℝ`). In finite dimension an injective endomorphism is bijective, so a positive-definite
symmetric operator has a genuine two-sided inverse and no Neumann series, no Lax–Milgram and no
spectral theory is required. This is why the two "open" hypotheses collapse to (1) and (2): the
analysis Bałaban defers is *not* needed to produce the inverses — only the two facts above are.

**What this module does NOT do.** It does not prove (1). Coercivity of `Δ_π + P` on the whole fine
space at a general background is Bałaban's gauge-fixed regularity statement, and it is the residual
this module isolates. `BridgeInverseKernel.kernel_criterion` proves the sharp characterisation that
can replace it: for positive-semidefinite symmetric `Δ_π + P` and `0 < a`,
`Δ_π + P + Q*aQ` is injective ⟺ `ker(Δ_π+P) ∩ ker Q = 0` — so (1) can also be met by a
kernel-intersection fact rather than by a uniform constant.

## Degeneracy guards, stated

* `a = 0` is ALLOWED and the construction still works (the `Q*aQ` term is then absent from the
  positivity, which is why (1) is stated on `Δ_π + P` and not on `Δ_π + P + Q*aQ`).
* `P = 0` is ALLOWED; then (1) is coercivity of `Δ_π` alone, which the campaign's own witness
  refutes at `witnessU` (`BridgeInverseControls.h310_unrestricted_impossible_at_witnessU`).
  Nothing here hides that.
* `Q = 0` is EXCLUDED by hypothesis (2) whenever the coarse space is nontrivial:
  `qstar_ne_zero_of_injective` proves it, so the construction cannot be satisfied by the degenerate
  block average.
* The coarse carrier being trivial (`K = EuclideanSpace ℝ (Fin 0)`) is excluded wherever it matters
  by `[Nontrivial K]`, and §6's non-vacuity theorems (`sOp_ne_zero`, `tOp_ne_zero`,
  `invOfInjective_ne_zero`) EXHIBIT `S ≠ 0` and `G ≠ 0` rather than asserting them.
-/

namespace AdalyFormal.Balaban.BridgeInverse

open scoped InnerProductSpace

/-! ## §1 — Inversion of an injective endomorphism of a finite-dimensional space -/

section Inversion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- An injective continuous endomorphism of a finite-dimensional space, as a linear equivalence.
Bijectivity is `LinearMap.injective_iff_surjective`, which is exactly where finite-dimensionality
enters. -/
noncomputable def linEquivOfInjective (M : H →L[ℝ] H) (hM : Function.Injective M) : H ≃ₗ[ℝ] H :=
  LinearEquiv.ofBijective (M : H →ₗ[ℝ] H)
    ⟨hM, LinearMap.injective_iff_surjective.1 hM⟩

theorem linEquivOfInjective_apply (M : H →L[ℝ] H) (hM : Function.Injective M) (x : H) :
    linEquivOfInjective M hM x = M x := rfl

/-- **The two-sided inverse of an injective continuous endomorphism**, as a genuine
`ContinuousLinearMap`. Continuity of the inverse is automatic in finite dimension
(`LinearMap.toContinuousLinearMap`). -/
noncomputable def invOfInjective (M : H →L[ℝ] H) (hM : Function.Injective M) : H →L[ℝ] H :=
  LinearMap.toContinuousLinearMap (linEquivOfInjective M hM).symm.toLinearMap

theorem invOfInjective_apply (M : H →L[ℝ] H) (hM : Function.Injective M) (x : H) :
    invOfInjective M hM x = (linEquivOfInjective M hM).symm x := rfl

/-- **`M ∘ M⁻¹ = id`** — this is the shape `hG1` and `hTS` demand. -/
theorem invOfInjective_right (M : H →L[ℝ] H) (hM : Function.Injective M) (x : H) :
    M (invOfInjective M hM x) = x := by
  rw [invOfInjective_apply, ← linEquivOfInjective_apply M hM]
  exact (linEquivOfInjective M hM).apply_symm_apply x

/-- **`M⁻¹ ∘ M = id`**. -/
theorem invOfInjective_left (M : H →L[ℝ] H) (hM : Function.Injective M) (x : H) :
    invOfInjective M hM (M x) = x := by
  rw [invOfInjective_apply, ← linEquivOfInjective_apply M hM]
  exact (linEquivOfInjective M hM).symm_apply_apply x

theorem invOfInjective_injective (M : H →L[ℝ] H) (hM : Function.Injective M) :
    Function.Injective (invOfInjective M hM) := by
  intro u v huv
  have h := congrArg (fun z => M z) huv
  simpa only [invOfInjective_right] using h

/-- **Non-vacuity: the inverse is not the zero map** whenever the space is nontrivial. -/
theorem invOfInjective_ne_zero [Nontrivial H] (M : H →L[ℝ] H) (hM : Function.Injective M) :
    invOfInjective M hM ≠ 0 := by
  intro hcon
  obtain ⟨y, hy⟩ := exists_ne (0 : H)
  have h : M (invOfInjective M hM y) = y := invOfInjective_right M hM y
  rw [hcon] at h
  simp only [ContinuousLinearMap.zero_apply, map_zero] at h
  exact hy h.symm

/-- A positive-definite quadratic form forces injectivity. No symmetry is used. -/
theorem injective_of_posDef (M : H →L[ℝ] H)
    (hpd : ∀ x : H, x ≠ 0 → 0 < (inner ℝ x (M x) : ℝ)) : Function.Injective M := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have h := hpd x hne
  rw [hx, inner_zero_right] at h
  exact lt_irrefl _ h

/-- Coercivity with a positive constant forces injectivity. -/
theorem injective_of_coercive (M : H →L[ℝ] H) (γ : ℝ) (hγ : 0 < γ)
    (hc : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (M x) : ℝ)) : Function.Injective M := by
  refine injective_of_posDef M fun x hx => ?_
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have : 0 < γ * ‖x‖ ^ 2 := by positivity
  exact lt_of_lt_of_le this (hc x)

end Inversion

/-! ## §2 — Positive-definite ⟹ coercive, in finite dimension

This is the converse direction that lets a KERNEL condition (§6) be used where `bridge_bare` wants a
uniform constant. It is a compactness argument on the unit sphere, and it is the only place in the
module where a non-constructive existence appears. -/

section PosDefCoercive

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem continuous_quadForm (M : H →L[ℝ] H) :
    Continuous fun x : H => (inner ℝ x (M x) : ℝ) :=
  continuous_id.inner M.continuous

/-- **A positive-definite continuous quadratic form on a finite-dimensional space is coercive.**
The constant is the minimum of the form on the unit sphere, which is attained because the sphere is
compact (finite dimension ⟹ `ProperSpace`) and nonempty (`Nontrivial H`). -/
theorem exists_coercive_of_posDef [Nontrivial H] (M : H →L[ℝ] H)
    (hpd : ∀ x : H, x ≠ 0 → 0 < (inner ℝ x (M x) : ℝ)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (M x) : ℝ) := by
  have hcomp : IsCompact (Metric.sphere (0 : H) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : H) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
    hcomp.exists_isMinOn hne (continuous_quadForm M).continuousOn
  have hx₀norm : ‖x₀‖ = 1 := by simpa using mem_sphere_zero_iff_norm.1 hx₀mem
  have hx₀ne : x₀ ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hx₀norm
    exact zero_ne_one hx₀norm
  refine ⟨(inner ℝ x₀ (M x₀) : ℝ), hpd x₀ hx₀ne, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hmem : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : H) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
      field_simp
    have hmin : (inner ℝ x₀ (M x₀) : ℝ)
        ≤ (inner ℝ (‖x‖⁻¹ • x) (M (‖x‖⁻¹ • x)) : ℝ) := hx₀min hmem
    have hval : (inner ℝ (‖x‖⁻¹ • x) (M (‖x‖⁻¹ • x)) : ℝ)
        = (‖x‖⁻¹) ^ 2 * (inner ℝ x (M x) : ℝ) := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hval] at hmin
    have hsq : 0 < ‖x‖ ^ 2 := by positivity
    have hkey : (inner ℝ x₀ (M x₀) : ℝ) * ‖x‖ ^ 2 ≤ (‖x‖⁻¹) ^ 2 * (inner ℝ x (M x) : ℝ) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hmin hsq.le
    have hcancel : (‖x‖⁻¹) ^ 2 * (inner ℝ x (M x) : ℝ) * ‖x‖ ^ 2 = (inner ℝ x (M x) : ℝ) := by
      field_simp
    rw [hcancel] at hkey
    exact hkey

end PosDefCoercive

/-! ## §3 — (3.128)'s fine operator as a bundled `ContinuousLinearMap` -/

section FineOperator

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- **`M = Δ_π + P + Q*aQ`**, CMP99b (3.128)'s fine operator, bundled. `Delta` is a parameter (as in
`RecursiveBridge.fineMapOf`), so no normalization is baked in. -/
noncomputable def fineCLM (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ) :
    H →L[ℝ] H :=
  Delta + P + a • (Qstar.comp Q)

theorem fineCLM_apply (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ) (x : H) :
    fineCLM Delta P Q Qstar a x = Delta x + P x + a • Qstar (Q x) := rfl

/-- The diagonal of `M`: `⟨x,Mx⟩ = ⟨x,Δx⟩ + ⟨x,Px⟩ + a‖Qx‖²`. The `a`-term is kept explicitly —
this is what makes (3.156)'s `−a⟨B,B⟩` cancel downstream. -/
theorem fineCLM_inner (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ)) (x : H) :
    (inner ℝ x (fineCLM Delta P Q Qstar a x) : ℝ)
      = (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ) + a * ‖Q x‖ ^ 2 := by
  have h1 : (inner ℝ x (Qstar (Q x)) : ℝ) = ‖Q x‖ ^ 2 := by
    have h2 : (inner ℝ (Qstar (Q x)) x : ℝ) = ‖Q x‖ ^ 2 := by
      rw [hadj x (Q x), real_inner_self_eq_norm_sq]
    rw [← h2]
    first
      | exact real_inner_comm _ _
      | exact (real_inner_comm _ _).symm
  rw [fineCLM_apply, inner_add_right, inner_add_right, real_inner_smul_right, h1]

/-- **The gauge-fixed coercivity `γ‖x‖² ≤ ⟨x,(Δ_π+P)x⟩` plus `a ≥ 0` gives (3.128)'s operator its
sharp lower bound `γ‖x‖² + a‖Qx‖²`** — exactly the hypothesis `RecursiveBridge.bridge_bare` wants,
at EVERY point, not only along `G∘Q*`. -/
theorem fineCLM_coercive (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a γ : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ)) (x : H) :
    γ * ‖x‖ ^ 2 + a * ‖Q x‖ ^ 2 ≤ (inner ℝ x (fineCLM Delta P Q Qstar a x) : ℝ) := by
  rw [fineCLM_inner Delta P Q Qstar a hadj x]
  linarith [hDP x]

/-- `M` is symmetric when `Δ_π` and `P` are — the `Q*aQ` term is symmetric for free. -/
theorem fineCLM_symm (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDsym : ∀ u v : H, (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hPsym : ∀ u v : H, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ)) (u v : H) :
    (inner ℝ u (fineCLM Delta P Q Qstar a v) : ℝ)
      = (inner ℝ (fineCLM Delta P Q Qstar a u) v : ℝ) := by
  have e1 : (inner ℝ u (Qstar (Q v)) : ℝ) = (inner ℝ (Q v) (Q u) : ℝ) := by
    rw [← hadj u (Q v)]
    first
      | exact real_inner_comm _ _
      | exact (real_inner_comm _ _).symm
  have e2 : (inner ℝ (Qstar (Q u)) v : ℝ) = (inner ℝ (Q u) (Q v) : ℝ) := hadj v (Q u)
  rw [fineCLM_apply, fineCLM_apply, inner_add_right, inner_add_right, inner_add_left,
    inner_add_left, hDsym u v, hPsym u v, real_inner_smul_right, real_inner_smul_left, e1, e2,
    real_inner_comm (Q v) (Q u)]

end FineOperator

/-! ## §4 — `G₁`: the constructed right inverse of (3.128)'s operator -/

section GOne

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- `M = Δ_π + P + Q*aQ` is injective as soon as `Δ_π + P` is coercive and `a ≥ 0`. -/
theorem fineCLM_injective (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a γ : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hγ : 0 < γ) (ha : 0 ≤ a)
    (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ)) :
    Function.Injective (fineCLM Delta P Q Qstar a) := by
  refine injective_of_coercive _ γ hγ fun x => ?_
  have h := fineCLM_coercive Delta P Q Qstar a γ hadj hDP x
  have h2 : (0 : ℝ) ≤ a * ‖Q x‖ ^ 2 := by positivity
  linarith

/-- **`G₁`** — CMP99b's `G₁ = (Δ_π + P + Q*aQ)⁻¹`, CONSTRUCTED, not assumed. -/
noncomputable def gOne (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a γ : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hγ : 0 < γ) (ha : 0 ≤ a)
    (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ)) :
    H →L[ℝ] H :=
  invOfInjective (fineCLM Delta P Q Qstar a)
    (fineCLM_injective Delta P Q Qstar a γ hadj hγ ha hDP)

variable (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a γ : ℝ)
  (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
  (hγ : 0 < γ) (ha : 0 ≤ a)
  (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))

include hadj hγ ha hDP

/-- **`hG1`, DISCHARGED at the operator level**: the constructed `G₁` is a right inverse of
(3.128)'s fine operator. `BridgeInverseCarrier.lean` transports this to the exact
`RecursiveBridge.fineMapOf` shape on the lattice carrier. -/
theorem gOne_fineCLM_right (x : H) :
    fineCLM Delta P Q Qstar a (gOne Delta P Q Qstar a γ hadj hγ ha hDP x) = x :=
  invOfInjective_right _ _ x

/-- `G₁ ∘ M = id` as well: it is a genuine two-sided inverse. -/
theorem gOne_fineCLM_left (x : H) :
    gOne Delta P Q Qstar a γ hadj hγ ha hDP (fineCLM Delta P Q Qstar a x) = x :=
  invOfInjective_left _ _ x

theorem gOne_injective : Function.Injective (gOne Delta P Q Qstar a γ hadj hγ ha hDP) :=
  invOfInjective_injective _ _

/-- **`G₁` is positive definite.** `⟨y, G₁y⟩ = ⟨M x, x⟩ ≥ γ‖x‖² > 0` at `x = G₁ y ≠ 0`. No symmetry
of `M` is used: `real_inner_comm` does the flip. -/
theorem gOne_posDef (y : H) (hy : y ≠ 0) :
    0 < (inner ℝ y (gOne Delta P Q Qstar a γ hadj hγ ha hDP y) : ℝ) := by
  set x : H := gOne Delta P Q Qstar a γ hadj hγ ha hDP y with hx
  have hMx : fineCLM Delta P Q Qstar a x = y := invOfInjective_right _ _ y
  have hxne : x ≠ 0 := by
    intro hc
    rw [hc, map_zero] at hMx
    exact hy hMx.symm
  have hlow := fineCLM_coercive Delta P Q Qstar a γ hadj hDP x
  rw [hMx] at hlow
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hxne
  have hpos : 0 < γ * ‖x‖ ^ 2 := by positivity
  have haq : (0 : ℝ) ≤ a * ‖Q x‖ ^ 2 := by positivity
  have : 0 < (inner ℝ x y : ℝ) := by linarith
  rw [real_inner_comm] at this
  exact this

theorem gOne_ne_zero [Nontrivial H] : gOne Delta P Q Qstar a γ hadj hγ ha hDP ≠ 0 :=
  invOfInjective_ne_zero _ _

end GOne

/-! ## §5 — `Q*` injective ⟺ `Q` surjective, for an adjoint pair -/

section AdjointPair

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- `ker Q* = (range Q)ᗮ`, in the raw form the bridge's `hadj` supplies. -/
theorem qstar_eq_zero_iff_orthogonal (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ)) (B : K) :
    Qstar B = 0 ↔ ∀ x : H, (inner ℝ B (Q x) : ℝ) = 0 := by
  constructor
  · intro h x
    rw [← hadj x B, h, inner_zero_left]
  · intro h
    have h2 : (inner ℝ (Qstar B) (Qstar B) : ℝ) = 0 := by
      rw [hadj (Qstar B) B]; exact h (Qstar B)
    exact inner_self_eq_zero.1 h2

/-- **`Q` surjective ⟹ `Q*` injective.** This is the direction the construction consumes. -/
theorem qstar_injective_of_surjective (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hsurj : Function.Surjective Q) : Function.Injective Qstar := by
  rw [injective_iff_map_eq_zero]
  intro B hB
  have h := (qstar_eq_zero_iff_orthogonal Q Qstar hadj B).1 hB
  obtain ⟨x, hx⟩ := hsurj B
  have hz := h x
  rw [hx] at hz
  exact inner_self_eq_zero.1 hz

/-- **`Q*` injective ⟹ `Q` surjective** — the converse, so the hypothesis is not a strengthening in
disguise. Uses finite-dimensionality of `K` through `Submodule.orthogonal_eq_bot_iff`-style
reasoning packaged as `Submodule.triv_of_orthogonal_eq_bot` / rank comparison. -/
theorem surjective_of_qstar_injective (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hinj : Function.Injective Qstar) : Function.Surjective Q := by
  have hrange : (LinearMap.range (Q : H →ₗ[ℝ] K))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro B hB
    refine hinj ?_
    rw [map_zero]
    refine (qstar_eq_zero_iff_orthogonal Q Qstar hadj B).2 fun x => ?_
    have hz : (inner ℝ (Q x) B : ℝ) = 0 := hB (Q x) ⟨x, rfl⟩
    rw [← hz]
    first
      | exact real_inner_comm _ _
      | exact (real_inner_comm _ _).symm
  have hcl : (LinearMap.range (Q : H →ₗ[ℝ] K)) = ⊤ :=
    (Submodule.orthogonal_eq_bot_iff (K := LinearMap.range (Q : H →ₗ[ℝ] K))).1 hrange
  intro y
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 hcl y
  exact ⟨x, hx⟩

/-- **Anti-degeneracy: `Q = 0` is impossible** once `Q*` is injective and the coarse space is
nontrivial. So the hypothesis genuinely excludes the degenerate block average. -/
theorem qstar_ne_zero_of_injective [Nontrivial K] (Qstar : K →L[ℝ] H)
    (hinj : Function.Injective Qstar) : Qstar ≠ 0 := by
  intro hc
  obtain ⟨B, hB⟩ := exists_ne (0 : K)
  apply hB
  refine hinj ?_
  rw [hc]
  simp

theorem q_ne_zero_of_qstar_injective [Nontrivial K] (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hinj : Function.Injective Qstar) : Q ≠ 0 := by
  intro hc
  obtain ⟨B, hB⟩ := exists_ne (0 : K)
  apply hB
  refine hinj ?_
  rw [map_zero]
  refine (qstar_eq_zero_iff_orthogonal Q Qstar hadj B).2 fun x => ?_
  rw [hc]
  simp

end AdjointPair

/-! ## §6 — `T = QG₁Q*` and its inverse `S`: `hTS` DISCHARGED -/

section TAndS

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

variable (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a γ : ℝ)
  (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
  (hγ : 0 < γ) (ha : 0 ≤ a)
  (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))

include hadj hγ ha hDP

/-- **`T = Q G₁ Q*`**, CMP99b (3.129)/(3.156)'s coarse operator, CONSTRUCTED. -/
noncomputable def tOp : K →L[ℝ] K :=
  Q.comp ((gOne Delta P Q Qstar a γ hadj hγ ha hDP).comp Qstar)

theorem tOp_apply (B : K) :
    tOp Delta P Q Qstar a γ hadj hγ ha hDP B
      = Q (gOne Delta P Q Qstar a γ hadj hγ ha hDP (Qstar B)) := rfl

/-- `⟨B, TB⟩ = ⟨Q*B, G₁ Q*B⟩` — the compression identity. -/
theorem tOp_inner (B : K) :
    (inner ℝ B (tOp Delta P Q Qstar a γ hadj hγ ha hDP B) : ℝ)
      = (inner ℝ (Qstar B) (gOne Delta P Q Qstar a γ hadj hγ ha hDP (Qstar B)) : ℝ) := by
  rw [tOp_apply, ← hadj (gOne Delta P Q Qstar a γ hadj hγ ha hDP (Qstar B)) B]

/-- **`T` is positive definite whenever `Q*` is injective** — because `G₁` is positive definite
(§4) and `Q*B ≠ 0` for `B ≠ 0`. -/
theorem tOp_posDef (hQstar : Function.Injective Qstar) (B : K) (hB : B ≠ 0) :
    0 < (inner ℝ B (tOp Delta P Q Qstar a γ hadj hγ ha hDP B) : ℝ) := by
  rw [tOp_inner]
  refine gOne_posDef Delta P Q Qstar a γ hadj hγ ha hDP (Qstar B) ?_
  intro hc
  exact hB (hQstar (by rw [hc, map_zero]))

theorem tOp_injective (hQstar : Function.Injective Qstar) :
    Function.Injective (tOp Delta P Q Qstar a γ hadj hγ ha hDP) :=
  injective_of_posDef _ (fun B hB => tOp_posDef Delta P Q Qstar a γ hadj hγ ha hDP hQstar B hB)

/-- **`S = (QG₁Q*)⁻¹`**, CMP99b (3.129)/(3.156)'s notation, CONSTRUCTED. -/
noncomputable def sOp (hQstar : Function.Injective Qstar) : K →L[ℝ] K :=
  invOfInjective (tOp Delta P Q Qstar a γ hadj hγ ha hDP)
    (tOp_injective Delta P Q Qstar a γ hadj hγ ha hDP hQstar)

/-- **`hTS`, DISCHARGED**: `T (S B) = B`. -/
theorem tOp_sOp (hQstar : Function.Injective Qstar) (B : K) :
    tOp Delta P Q Qstar a γ hadj hγ ha hDP
      (sOp Delta P Q Qstar a γ hadj hγ ha hDP hQstar B) = B :=
  invOfInjective_right _ _ B

/-- `S ∘ T = id` too. -/
theorem sOp_tOp (hQstar : Function.Injective Qstar) (B : K) :
    sOp Delta P Q Qstar a γ hadj hγ ha hDP hQstar
      (tOp Delta P Q Qstar a γ hadj hγ ha hDP B) = B :=
  invOfInjective_left _ _ B

/-- **Non-vacuity: `S ≠ 0`** on a nontrivial coarse space. -/
theorem sOp_ne_zero [Nontrivial K] (hQstar : Function.Injective Qstar) :
    sOp Delta P Q Qstar a γ hadj hγ ha hDP hQstar ≠ 0 :=
  invOfInjective_ne_zero _ _

/-- **Non-vacuity: `T ≠ 0`** on a nontrivial coarse space. -/
theorem tOp_ne_zero [Nontrivial K] (hQstar : Function.Injective Qstar) :
    tOp Delta P Q Qstar a γ hadj hγ ha hDP ≠ 0 := by
  intro hc
  obtain ⟨B, hB⟩ := exists_ne (0 : K)
  have h := tOp_posDef Delta P Q Qstar a γ hadj hγ ha hDP hQstar B hB
  rw [hc] at h
  simp at h

/-- **`S` is positive definite** — so (3.156)'s `⟨B,(QG₁Q*)⁻¹B⟩` is a genuine positive form, not a
formal symbol. -/
theorem sOp_posDef (hQstar : Function.Injective Qstar) (B : K) (hB : B ≠ 0) :
    0 < (inner ℝ B (sOp Delta P Q Qstar a γ hadj hγ ha hDP hQstar B) : ℝ) := by
  set C : K := sOp Delta P Q Qstar a γ hadj hγ ha hDP hQstar B with hC
  have hTC : tOp Delta P Q Qstar a γ hadj hγ ha hDP C = B := tOp_sOp _ _ _ _ _ _ _ _ _ _ hQstar B
  have hCne : C ≠ 0 := by
    intro hc
    rw [hc, map_zero] at hTC
    exact hB hTC.symm
  have h := tOp_posDef Delta P Q Qstar a γ hadj hγ ha hDP hQstar C hCne
  rw [hTC] at h
  rw [real_inner_comm]
  exact h

end TAndS

end AdalyFormal.Balaban.BridgeInverse
