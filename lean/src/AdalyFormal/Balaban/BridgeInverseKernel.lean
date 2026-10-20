/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BridgeInverseCore

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.longLine false

/-!
# `BridgeInverseKernel.lean` — `hG1`/`hTS` under the WEAKEST hypothesis, and the sharp criterion

`BridgeInverseCore` builds `G₁` and `S` from a uniform coercivity constant `γ` for the gauge-fixed
operator `Δ_π + P`. That is more than the construction needs. What it actually needs is
**injectivity of `M = Δ_π + P + Q*aQ`**, and this module isolates exactly that, with the sharp
criterion attached:

**`kernel_criterion`** (an IFF, at `0 < a`, for a positive-semidefinite `Δ_π + P`):

> `M` is injective  ⟺  no nonzero `x` has `⟨x,Δ_πx⟩ + ⟨x,Px⟩ = 0` and `Qx = 0`
> — i.e. `ker(Δ_π+P) ∩ ker Q = 0`.

So the residual `hDP` of `BridgeInverseControls` can be met EITHER by a uniform coercivity constant
OR by the purely algebraic kernel-intersection fact, whichever is easier at a given background. In
finite dimension the two are equivalent up to the value of the constant
(`exists_coercive_of_kernel_trivial`, via `BridgeInverseCore.exists_coercive_of_posDef`).

⚠ **The one honest cost of taking the kernel route.** `RecursiveBridge.bridge_bare` wants the
coercivity of `Δ_π + P` *separately* from the `a‖Qx‖²` term, because that separation is what makes
(3.156)'s `−a⟨B,B⟩` cancel exactly. The kernel route only produces a constant for the SUM. So the
kernel route gives `hG1` and `hTS` — the two operators — but not the sharp bridge constant. It is
recorded here because the two operators are what CMP99b leaves undefined, and they are now built
under the weakest hypothesis that can possibly build them: `M` is injective. If `M` is not
injective, `G₁` does not exist at all, so nothing weaker is available.

`hG1` in the LITERAL shape `RecursiveBridge.bridge_from_fine_operator` asks for (`fineMapOf`, on
the lattice carrier) is supplied in `BridgeInverseControls.lean` §11, at the concrete coarse carrier
— stating it with an ABSTRACT coarse type fails instance synthesis for
`InnerProductSpace ℝ (BondFnL2 L)`, the diamond `RecursiveBridge` §9b documents (measured here:
`compute/bridge_inverses/` build log b14/b15).
-/

namespace AdalyFormal.Balaban.BridgeInverse

open scoped InnerProductSpace

/-! ## §1 — the kernel criterion -/

section Kernel

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- **`ker(Δ_π+P) ∩ ker Q = 0` ⟹ `M` is positive definite.** `Δ_π+P` must be positive
semidefinite; `a` must be strictly positive (at `a = 0` the `Q`-term is absent and the criterion is
just positive-definiteness of `Δ_π+P`). -/
theorem fineCLM_posDef_of_kernel_trivial (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K)
    (Qstar : K →L[ℝ] H) (a : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (ha : 0 < a)
    (hDPpos : ∀ x : H, (0 : ℝ) ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))
    (hker : ∀ x : H,
      (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ) = 0 → Q x = 0 → x = 0)
    (x : H) (hx : x ≠ 0) :
    0 < (inner ℝ x (fineCLM Delta P Q Qstar a x) : ℝ) := by
  rw [fineCLM_inner Delta P Q Qstar a hadj x]
  rcases lt_or_eq_of_le (hDPpos x) with hlt | heq
  · have h2 : (0 : ℝ) ≤ a * ‖Q x‖ ^ 2 := by positivity
    linarith
  · rcases lt_or_eq_of_le (norm_nonneg (Q x)) with hq | hq
    · have : 0 < a * ‖Q x‖ ^ 2 := by positivity
      linarith
    · exact absurd (hker x heq.symm (norm_eq_zero.1 hq.symm)) hx

/-- **`M` injective ⟹ `ker(Δ_π+P) ∩ ker Q = 0`** — the converse, so §1 is sharp and the criterion
is not a strengthening in disguise. Needs `Δ_π+P` positive semidefinite and `0 ≤ a`. -/
theorem kernel_trivial_of_injective (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K)
    (Qstar : K →L[ℝ] H) (a : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDPsym : ∀ u v : H,
      (inner ℝ u (Delta v) : ℝ) + (inner ℝ u (P v) : ℝ)
        = (inner ℝ (Delta u) v : ℝ) + (inner ℝ (P u) v : ℝ))
    (hDPpos : ∀ x : H, (0 : ℝ) ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))
    (hinj : Function.Injective (fineCLM Delta P Q Qstar a))
    (x : H) (hD : (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ) = 0) (hQ : Q x = 0) :
    x = 0 := by
  -- `Δ_π+P` is a positive-semidefinite SYMMETRIC bilinear form, so a zero diagonal value at `x`
  -- forces `x` into its kernel (the degenerate-Cauchy-Schwarz step, done by hand on the
  -- one-variable quadratic `t ↦ B(u+tx, u+tx) ≥ 0`).
  have hcomm : ∀ p r : H, (inner ℝ p r : ℝ) = (inner ℝ r p : ℝ) := fun p r => by
    first
      | exact real_inner_comm _ _
      | exact (real_inner_comm _ _).symm
  have hsymm2 : ∀ u v : H, (inner ℝ u (Delta v) : ℝ) + (inner ℝ u (P v) : ℝ)
      = (inner ℝ v (Delta u) : ℝ) + (inner ℝ v (P u) : ℝ) := by
    intro u v
    rw [hDPsym u v, hcomm (Delta u) v, hcomm (P u) v]
  have hzero : ∀ u : H, (inner ℝ u (Delta x) : ℝ) + (inner ℝ u (P x) : ℝ) = 0 := by
    intro u
    set c : ℝ := (inner ℝ u (Delta x) : ℝ) + (inner ℝ u (P x) : ℝ) with hc
    set d : ℝ := (inner ℝ u (Delta u) : ℝ) + (inner ℝ u (P u) : ℝ) with hd
    have hd0 : 0 ≤ d := hDPpos u
    have key : ∀ t : ℝ, (0 : ℝ) ≤ d + t * (c + c) := by
      intro t
      have hexp := hDPpos (u + t • x)
      have e1 : (inner ℝ (u + t • x) (Delta (u + t • x)) : ℝ)
            + (inner ℝ (u + t • x) (P (u + t • x)) : ℝ)
          = ((inner ℝ u (Delta u) : ℝ) + (inner ℝ u (P u) : ℝ))
            + t * (((inner ℝ u (Delta x) : ℝ) + (inner ℝ u (P x) : ℝ))
                 + ((inner ℝ x (Delta u) : ℝ) + (inner ℝ x (P u) : ℝ)))
            + t ^ 2 * ((inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ)) := by
        simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right]
        ring
      rw [e1, hD, hsymm2 x u, mul_zero, add_zero, ← hc, ← hd] at hexp
      exact hexp
    by_contra hne
    have hcc : c + c ≠ 0 := by
      intro h0
      exact hne (by linarith)
    have ht := key (-((d + 1) / (c + c)))
    have hrw : (-((d + 1) / (c + c))) * (c + c) = -(d + 1) := by field_simp
    rw [hrw] at ht
    linarith
  have hDx : Delta x + P x = 0 := by
    have h := hzero (Delta x + P x)
    rw [← inner_add_right] at h
    exact inner_self_eq_zero.1 h
  refine hinj ?_
  rw [map_zero, fineCLM_apply, hQ]
  simp only [smul_zero, map_zero, add_zero]
  exact hDx

/-- **THE SHARP CRITERION**, as an iff at `0 < a`. -/
theorem kernel_criterion (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDPsym : ∀ u v : H,
      (inner ℝ u (Delta v) : ℝ) + (inner ℝ u (P v) : ℝ)
        = (inner ℝ (Delta u) v : ℝ) + (inner ℝ (P u) v : ℝ))
    (hDPpos : ∀ x : H, (0 : ℝ) ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))
    (ha : 0 < a) :
    Function.Injective (fineCLM Delta P Q Qstar a)
      ↔ ∀ x : H, (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ) = 0 → Q x = 0 → x = 0 := by
  constructor
  · intro hinj x hD hQ
    exact kernel_trivial_of_injective Delta P Q Qstar a hadj hDPsym hDPpos hinj x hD hQ
  · intro hker
    exact injective_of_posDef _
      (fineCLM_posDef_of_kernel_trivial Delta P Q Qstar a hadj ha hDPpos hker)

end Kernel

/-! ## §2 — `G₁`, `T`, `S` under the WEAKEST hypothesis: `M` injective -/

section WeakestBuild

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

variable (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (a : ℝ)
  (hinj : Function.Injective (fineCLM Delta P Q Qstar a))

/-- `G₁` from bare injectivity of (3.128)'s operator. -/
noncomputable def gOneK : H →L[ℝ] H := invOfInjective (fineCLM Delta P Q Qstar a) hinj

include hinj in
/-- **`hG1`, under the weakest possible hypothesis.** -/
theorem gOneK_right (x : H) :
    fineCLM Delta P Q Qstar a (gOneK Delta P Q Qstar a hinj x) = x :=
  invOfInjective_right _ _ x

include hinj in
theorem gOneK_left (x : H) :
    gOneK Delta P Q Qstar a hinj (fineCLM Delta P Q Qstar a x) = x :=
  invOfInjective_left _ _ x

variable (hMpos : ∀ x : H, x ≠ 0 → 0 < (inner ℝ x (fineCLM Delta P Q Qstar a x) : ℝ))

include hinj hMpos in
theorem gOneK_posDef (y : H) (hy : y ≠ 0) :
    0 < (inner ℝ y (gOneK Delta P Q Qstar a hinj y) : ℝ) := by
  set x : H := gOneK Delta P Q Qstar a hinj y with hx
  have hMx : fineCLM Delta P Q Qstar a x = y := invOfInjective_right _ _ y
  have hxne : x ≠ 0 := by
    intro hc
    rw [hc, map_zero] at hMx
    exact hy hMx.symm
  have h := hMpos x hxne
  rw [hMx] at h
  rw [real_inner_comm]
  exact h

/-- `T = QG₁Q*`, from bare injectivity. -/
noncomputable def tOpK : K →L[ℝ] K :=
  Q.comp ((gOneK Delta P Q Qstar a hinj).comp Qstar)

theorem tOpK_apply (B : K) :
    tOpK Delta P Q Qstar a hinj B = Q (gOneK Delta P Q Qstar a hinj (Qstar B)) := rfl

variable (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
  (hQstar : Function.Injective Qstar)

include hinj hMpos hadj hQstar in
theorem tOpK_posDef (B : K) (hB : B ≠ 0) :
    0 < (inner ℝ B (tOpK Delta P Q Qstar a hinj B) : ℝ) := by
  rw [tOpK_apply, ← hadj (gOneK Delta P Q Qstar a hinj (Qstar B)) B]
  refine gOneK_posDef Delta P Q Qstar a hinj hMpos (Qstar B) ?_
  intro hc
  exact hB (hQstar (by rw [hc, map_zero]))

include hinj hMpos hadj hQstar in
theorem tOpK_injective : Function.Injective (tOpK Delta P Q Qstar a hinj) :=
  injective_of_posDef _ (fun B hB => tOpK_posDef Delta P Q Qstar a hinj hMpos hadj hQstar B hB)

/-- `S = (QG₁Q*)⁻¹`, from bare injectivity. -/
noncomputable def sOpK : K →L[ℝ] K :=
  invOfInjective (tOpK Delta P Q Qstar a hinj)
    (tOpK_injective Delta P Q Qstar a hinj hMpos hadj hQstar)

include hinj hMpos hadj hQstar in
/-- **`hTS`, under the weakest possible hypothesis.** -/
theorem tOpK_sOpK (B : K) :
    tOpK Delta P Q Qstar a hinj (sOpK Delta P Q Qstar a hinj hMpos hadj hQstar B) = B :=
  invOfInjective_right _ _ B

include hinj hMpos hadj hQstar in
theorem sOpK_ne_zero [Nontrivial K] : sOpK Delta P Q Qstar a hinj hMpos hadj hQstar ≠ 0 :=
  invOfInjective_ne_zero _ _

end WeakestBuild

/-! ## §3 — from the kernel criterion to a uniform constant for `M` -/

section UniformConstant

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- **The kernel condition yields a uniform coercivity constant for `M` itself.** ⚠ For `M`, NOT
for `Δ_π + P` separately — see the module header on what that costs. -/
theorem exists_coercive_of_kernel_trivial [Nontrivial H] (Delta P : H →L[ℝ] H) (Q : H →L[ℝ] K)
    (Qstar : K →L[ℝ] H) (a : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (ha : 0 < a)
    (hDPpos : ∀ x : H, (0 : ℝ) ≤ (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ))
    (hker : ∀ x : H,
      (inner ℝ x (Delta x) : ℝ) + (inner ℝ x (P x) : ℝ) = 0 → Q x = 0 → x = 0) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x : H,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (fineCLM Delta P Q Qstar a x) : ℝ) :=
  exists_coercive_of_posDef _
    (fineCLM_posDef_of_kernel_trivial Delta P Q Qstar a hadj ha hDPpos hker)

end UniformConstant

#print axioms fineCLM_posDef_of_kernel_trivial
#print axioms kernel_trivial_of_injective
#print axioms kernel_criterion
#print axioms gOneK
#print axioms gOneK_right
#print axioms gOneK_posDef
#print axioms tOpK_posDef
#print axioms sOpK
#print axioms tOpK_sOpK
#print axioms sOpK_ne_zero
#print axioms exists_coercive_of_kernel_trivial

end AdalyFormal.Balaban.BridgeInverse
