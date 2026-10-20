/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKRecursive
import AdalyFormal.Balaban.DeltaPrimeOperator

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-!
# `RecursiveBridge.lean` — THE BRIDGE FROM CMP99b (3.10) TO CMP99b (3.156)

## What this module answers

The campaign's coercivity results (`LemmaAssembly.deltaK_gaugeRegular_coercive`,
`AlphaAnalyticity.gamma0_uniform_over_family`, `LemmaAssembly.deltaK_lemma_existential_threshold`)
all concern `DeltaKFull.deltaKQuadFormCorrected`, which is CMP99b p.392 **(3.10)**'s
`Δ^η(U) = D*D + Δ′` — an operator carrying **no scale index at all**. `GOAL_LEMMA.md` §1's lemma
is about p.428 **(3.156)**'s `Δ_k`. `TheLemma.lean` §3 records that no bridge existed in this tree.

**This module builds the bridge.** It is elementary: two Cauchy–Schwarz applications and one
positive-semidefinite Cauchy–Schwarz. It needs no Woodbury identity, no Neumann series, no spectral
theory, and — the point — **no `a`-penalty**: the `+a‖QA‖²` that (3.128) puts *into* `G₁⁻¹` and the
`−a⟨B,B⟩` that (3.156) *subtracts* cancel exactly, and the proof below is arranged so that the
cancellation is visible rather than lossy.

## THE SOURCE CHAIN — four equations, verbatim; TWO of the four pages are adjudicated

**(3.10), CMP99b p.392.** ⚠ **`corpus/pages/CMP99b_p392.md` is `verification_status: single-read`,
NOT adjudicated** (corrected 2026-07-28; the earlier blanket claim that all source pages here were
adjudicated was wrong — p.421 and p.428 are, p.392 is not, and p.419 is not in `corpus/pages/` at
all). The machine draft
(`corpus/mathpix/balaban_CMP99_1985_propagators_backgroundfield/normalized/p392.md`) flags this very
display at `conf=0.44`. It was therefore **rendered fresh
at 400 dpi for this module** (`compute/recursive_bridge/renders/CMP99b_p392-04.png`, produced by
`pdftoppm -r 400 -f 4 -l 4` from `balaban_CMP99_1985_propagators_backgroundfield.pdf`,
`sha256 39f8033b…542861`, page offset 388 from `corpus/tools/page_offsets.json`,
`constant_verified: true`; running head "392 / T. Balaban" confirmed) and read from the image:

```
⟨A, Δ A⟩  = ⟨A, D*D A⟩ + ⟨A, Δ′A⟩ ,
⟨A, Δ′A⟩  = Σ_{p ⊂ T_η} η^d tr((D_U^1 A)(p))² η^{-2}(Re U(∂p) − 1)
          + tr Σ_{b₁,b₂ ⊂ ∂(p)_z, b₁ ≺ b₂} i[A′(b₁), A′(b₂)] η^{-2} Im U(∂p) .     (3.10)
```

with the surrounding prose, verbatim: *"The quadratic terms in the expansion (3.7) define the basic
operator generalizing the operator ∂*∂ in the Abelian case. We denote it by Δ^η(U), or simply by Δ."*
and, below the display, *"We have written it this way because with our assumptions on the
configuration U the operator Δ′ will be a bounded, small operator, which will be treated as a small
perturbation of D*D."*

Two readings differ from the machine draft and are recorded rather than normalized:
* the ordering relation under the second sum reads as a **prec-style** glyph `b₁ ≺ b₂` — curved
  arms meeting a vertex with a short horizontal stub, magnified 14× at
  `compute/recursive_bridge/renders/crop_prec_glyph.png` — rather than the straight-armed `b₁ < b₂`
  mathpix rendered. **This reading is NOT adjudicated**: a nested validator viewed the same crop and
  declined to certify prec-versus-less-than by eye, and it is recorded here only as a disclosed
  divergence from the machine draft, never silently normalized. **It is not load-bearing**: no
  theorem in this module depends on which relation orders the bond pairs — the ordering enters only
  the internal structure of `Δ′`, which the bridge consumes solely through symmetry and a
  coercivity constant (§9d). Anyone needing the relation itself must adjudicate it separately;
* as printed the second term carries **neither** a `Σ_{p⊂T_η}` **nor** an `η^d`, yet its index `p`
  occurs free in both `∂(p)_z` and `Im U(∂p)`; elision of the shared `p`-sum is the only consistent
  reading.

**The decisive fact: (3.10) has no `k`.** Its arguments are a fine-lattice bond function `A` on `T_η`
and a fine-lattice link configuration `U`. `DeltaKFull.deltaKQuadFormCorrected` denotes exactly this
object; the `K` in that identifier is a misnomer, and the collision is Bałaban's own `Δ` versus
`Δ_k`, not a translation error.

**(3.128), CMP99b p.421, `verification_status: adjudicated`** (`corpus/pages/CMP99b_p421.md`) — the
equation that makes the bridge possible, because it gives `G₁⁻¹` **as an explicit quadratic form**:

```
⟨A, G₁⁻¹A⟩ = ⟨A, Δ_π A⟩ − 2⟨H C_π^{(2)}(A), J⟩ + ‖RD*A‖² + a‖QA‖² .                 (3.128)
```

Same page, verbatim: *"Let us denote for a moment the operator we have investigated in previous
sections by `G₀`, i.e. `G₀ = (Δ + DRD* + Q*aQ)⁻¹`."* and (3.129) `H₁B = G₁Q*(QG₁Q*)⁻¹B`.

Because (3.128) exhibits `G₁⁻¹` directly, **the Neumann series (3.130)/(3.138) is not on the critical
path** and p.423 — which is *not* adjudicated — is not needed. `C^{(2)}(A)` is, in Bałaban's own
words on that page, *"a second order term in the expansion of `Q_j(ηA)`"*, i.e. quadratic in `A`; so
(3.128) genuinely is a quadratic form, as he says, and `Δ_k` genuinely is an operator.

**(3.156), CMP99b p.428, `verification_status: adjudicated`** (`corpus/pages/CMP99b_p428.md`, whose
`J`-versus-`g` reading was separately adjudicated from a 1.8× crop):

```
⟨B, (QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁ D̃^{(2)}(B), J⟩ = ⟨B, Δ_k B⟩ .                       (3.156)
```

*"This form is considered on the subspace `{B : B=0 on Λᶜ, B=0 on ⋃_{y∈Λ′} Ax(y), Q₁B=0}`."*

## THE STRUCTURAL FACT — why the `a` cancels

Write `M₀` for the `a`-free part of (3.128)'s right-hand side
(`Δ_π + (RD*)*(RD*) − 2⟨H C_π^{(2)}(·), J⟩`) and `M := M₀ + Q*aQ`, so `G₁ = M⁻¹` by (3.128).
⚠ **Note `Δ_π`, not `Δ`** — see §9e. The abstract sections §1–§6 below carry the fine operator as an
opaque `M`, so they are agnostic; §9's `fineMapOf` takes the (3.10)-level object as a PARAMETER and
the headline instantiates it at `piExtendedMap (deltaKCLMNormalized U) Δ′_π = Δ − Δ′_π`. An earlier
version of this paragraph said `Δ_π` while the code built `M` from plain `Δ`; that disagreement was
the defect, and it is now repaired on the code side, not the prose side.
Set `T := Q G₁ Q*` and `S := T⁻¹`, so (3.156) reads
`⟨B, Δ_k B⟩ = ⟨B, S B⟩ − a‖B‖² − 2⟨H₁D̃^{(2)}(B), J⟩`.

The naive route — bound `M ≥ γ`, hence `T ≤ 1/γ · ‖Q‖²`, hence `S ≥ γ/‖Q‖²` — **throws the
`a‖QA‖²` term away**, and then the `−a‖B‖²` of (3.156) is an unpaid debt: one is left needing
`γ/‖Q‖² > a`. §3 below instead *keeps* the `a`-term through the estimate and obtains the sharp

```
⟨B, T B⟩ ≤ ‖B‖² / (γ/q² + a) ,      hence      ⟨B, S B⟩ ≥ (γ/q² + a)‖B‖² ,
```

so that after (3.156)'s subtraction the `a` is gone exactly:

```
⟨B, Δ_k B⟩ ≥ (γ/q²)‖B‖² − 2⟨H₁D̃^{(2)}(B), J⟩ .
```

The `a` is not bounded, not assumed small, and not cancelled by hand — it is carried through the
inequality and disappears. §7's witness exhibits this numerically at `a = 1`.

## WHAT IS HYPOTHESIS AND WHAT IS THEOREM (§LEAN-D, no-success-lie)

Everything below is a **transport theorem**. It does **not** prove the fine-scale coercivity
`γ‖x‖² ≤ ⟨x, M₀x⟩`; that is the hypothesis, and it is exactly the (3.10)-level statement the
campaign already has results about. What is proved is that such a bound **transports to (3.156)'s
`Δ_k` with an explicit constant `γ/q²`, with no `a`-penalty**, where `q` is any bound with
`‖Qx‖ ≤ q‖x‖`. The two remaining inputs are stated as named hypotheses on the family, never assumed:

* `hM` — that `G₁` really is the inverse of `M₀ + Q*aQ`, i.e. (3.128)-faithfulness;
* `hsrc` — a bound `|2⟨H₁D̃^{(2)}(B), J⟩| ≤ ε‖B‖²` on (3.156)'s source term. Bałaban's own reason
  for expecting it is on p.421, verbatim: *"they are small because the configuration `J` is small."*
  At `J = 0` it is `ε = 0`. It is **not** proved here.

`γ`, `q`, `a`, `ε` are all genuine parameters bound *before* `B` — read the binder order in §4/§5.

## LAW-19 — what is reused, not rebuilt

`DeltaKRecursive.RGScaleFamily`/`deltaKQuadForm`/`G1`/`deltaKSubspace` are **imported and consumed**
(§6), not re-declared: that module already carries (3.156)'s shape with every unbuilt ingredient as
an explicit page-cited field, including `invertQGQstar_spec`, which §6 uses to manufacture the
two-sided-inverse hypothesis from `IsUnit` rather than assuming it. §1's positive-semidefinite
Cauchy–Schwarz is, as far as a grep of `Balaban/` shows, not present in the tree; it is written here
in reusable form (`psd_cauchy_schwarz`, over an arbitrary real inner product space).
-/

namespace AdalyFormal.Balaban.RecursiveBridge

open RealInnerProductSpace in
section

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## §1 — Cauchy–Schwarz for the semi-inner product of a positive symmetric operator

Reusable, stated over an arbitrary real inner product space. This is the only genuinely
"analytic" ingredient in the whole module, and it is a discriminant argument. -/

/-- **Cauchy–Schwarz for `[x,y] := ⟪x, T y⟫`** when `T` is symmetric and positive semidefinite.
Note `T` is *not* assumed invertible, bounded below, or self-adjoint in the bundled `.adjoint`
sense — only the two elementwise properties, which is what keeps this usable on the composites
`Q G Q*` appearing in (3.156) without touching the ambient-topology wall `DeltaKFull` §6 records. -/
theorem psd_cauchy_schwarz (T : E →L[ℝ] E)
    (hsym : ∀ u v : E, (inner ℝ u (T v) : ℝ) = (inner ℝ (T u) v : ℝ))
    (hpos : ∀ u : E, (0 : ℝ) ≤ (inner ℝ u (T u) : ℝ)) (x y : E) :
    (inner ℝ x (T y) : ℝ) ^ 2 ≤ (inner ℝ x (T x) : ℝ) * (inner ℝ y (T y) : ℝ) := by
  -- `⟪y, T x⟫ = ⟪x, T y⟫`: symmetry plus real-inner commutativity.
  have hflip : (inner ℝ y (T x) : ℝ) = (inner ℝ x (T y) : ℝ) := by
    rw [hsym y x, real_inner_comm]
  have key : ∀ t : ℝ,
      0 ≤ (inner ℝ y (T y) : ℝ) * (t * t) + 2 * (inner ℝ x (T y) : ℝ) * t
            + (inner ℝ x (T x) : ℝ) := by
    intro t
    have h := hpos (t • y + x)
    have expand : (inner ℝ (t • y + x) (T (t • y + x)) : ℝ)
        = (inner ℝ y (T y) : ℝ) * (t * t) + 2 * (inner ℝ x (T y) : ℝ) * t
            + (inner ℝ x (T x) : ℝ) := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right]
      rw [hflip]
      ring
    rw [expand] at h
    exact h
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

end

/-! ## §2 — THE ENGINE: the inverse of a positive operator bounded ABOVE is bounded BELOW

`T ≤ c` and `T S = 1` give `S ≥ 1/c`. This is the step that converts an upper bound on the
covariance `QG₁Q*` into a lower bound on (3.156)'s `(QG₁Q*)⁻¹`. -/

section Engine

variable {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- **`T ≤ c`, `T ∘ S = 1`  ⟹  `S ≥ 1/c`.** The hypothesis `hTS` is a two-sided-free, purely
pointwise statement `T (S B) = B`; §6 manufactures it from `RGScaleFamily.invertQGQstar_spec`. -/
theorem inner_inv_ge_of_le (T S : K →L[ℝ] K)
    (hsym : ∀ u v : K, (inner ℝ u (T v) : ℝ) = (inner ℝ (T u) v : ℝ))
    (hpos : ∀ u : K, (0 : ℝ) ≤ (inner ℝ u (T u) : ℝ))
    {c : ℝ} (hc : 0 < c) (hub : ∀ u : K, (inner ℝ u (T u) : ℝ) ≤ c * ‖u‖ ^ 2)
    (hTS : ∀ B : K, T (S B) = B) (B : K) :
    ‖B‖ ^ 2 / c ≤ (inner ℝ B (S B) : ℝ) := by
  set C : K := S B with hC
  have hTC : T C = B := hTS B
  -- `⟪B, S B⟫ = ⟪C, T C⟫`, and it is `≥ 0`.
  have hval : (inner ℝ B (S B) : ℝ) = (inner ℝ C (T C) : ℝ) := by
    rw [hTC, ← hC, real_inner_comm]
  have hnn : (0 : ℝ) ≤ (inner ℝ C (T C) : ℝ) := hpos C
  -- `‖B‖² = ⟪C, T B⟫`.
  have hsq : ‖B‖ ^ 2 = (inner ℝ C (T B) : ℝ) := by
    rw [hsym C B, hTC, real_inner_self_eq_norm_sq]
  -- Cauchy–Schwarz in the `T`-form, then the upper bound at `B`.
  have hcs := psd_cauchy_schwarz T hsym hpos C B
  rw [← hsq] at hcs
  have hubB := hub B
  have hstep : (‖B‖ ^ 2) ^ 2 ≤ (inner ℝ C (T C) : ℝ) * (c * ‖B‖ ^ 2) := by
    calc (‖B‖ ^ 2) ^ 2 ≤ (inner ℝ C (T C) : ℝ) * (inner ℝ B (T B) : ℝ) := hcs
    _ ≤ (inner ℝ C (T C) : ℝ) * (c * ‖B‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hubB hnn
  rw [hval, div_le_iff₀ hc]
  rcases eq_or_lt_of_le (sq_nonneg ‖B‖) with h | h
  · rw [← h]; exact mul_nonneg hnn hc.le
  · refine le_of_mul_le_mul_right ?_ h
    nlinarith [hstep]

end Engine

/-! ## §3 — THE SHARP COARSE UPPER BOUND: where the `a` of (3.128) is KEPT

`⟨B, Q G₁ Q* B⟩ ≤ ‖B‖² / (γ/q² + a)`. The `a` term of (3.128) appears in the denominator; a
proof that discarded it would land on `‖B‖²/(γ/q²)` and leave (3.156)'s `−a‖B‖²` unpaid. -/

section Coarse

variable {H K : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The composite `T = Q ∘ G ∘ Q*` of (3.156), as a bundled operator on the coarse space. -/
noncomputable def coarseComposite (Q : H →L[ℝ] K) (G : H →L[ℝ] H) (Qstar : K →L[ℝ] H) :
    K →L[ℝ] K :=
  Q.comp (G.comp Qstar)

@[simp] theorem coarseComposite_apply (Q : H →L[ℝ] K) (G : H →L[ℝ] H) (Qstar : K →L[ℝ] H)
    (B : K) : coarseComposite Q G Qstar B = Q (G (Qstar B)) := rfl

variable (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (M₀ M G : H →L[ℝ] H) (a γ q : ℝ)

/-- The (3.128) shape: `M = M₀ + Q* a Q`, with `M₀` the `a`-free part
`Δ_π + (RD*)*(RD*) − 2⟨H C_π^{(2)}(·),J⟩`. -/
def IsShiftedBy : Prop := ∀ x : H, M x = M₀ x + Qstar (a • Q x)

/-- `Q*` is the adjoint of `Q`, stated pointwise so that no bundled `.adjoint` is needed. -/
def IsAdjointPair : Prop := ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ)

/-- The adjoint relation in the flipped slot: `⟪Q x, B⟫_K = ⟪x, Q* B⟫_H`. -/
theorem adj_flip (hadj : IsAdjointPair Q Qstar) (x : H) (B : K) :
    (inner ℝ (Q x) B : ℝ) = (inner ℝ x (Qstar B) : ℝ) := by
  rw [real_inner_comm B (Q x), ← hadj x B]
  exact real_inner_comm x (Qstar B)

/-- The `a`-shift is symmetric and, for `0 ≤ a`, positive semidefinite. -/
theorem shift_inner (hadj : IsAdjointPair Q Qstar) (x : H) :
    (inner ℝ x (Qstar (a • Q x)) : ℝ) = a * ‖Q x‖ ^ 2 := by
  rw [real_inner_comm, hadj x (a • Q x), real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- **The key expansion**: on the fibre through `x`, the (3.128) form splits into its `a`-free part
and exactly `a‖Qx‖²`. -/
theorem inner_M_eq (hadj : IsAdjointPair Q Qstar) (hM : IsShiftedBy Q Qstar M₀ M a) (x : H) :
    (inner ℝ x (M x) : ℝ) = (inner ℝ x (M₀ x) : ℝ) + a * ‖Q x‖ ^ 2 := by
  rw [hM x, inner_add_right, shift_inner Q Qstar a hadj x]

/-- **§3's headline, PRIMITIVE FORM.** The single quantitative hypothesis is

`hMcoerc : γ‖x‖² + a‖Qx‖² ≤ ⟨x, M x⟩` ,

which is **exactly (3.128) read together with the (3.10)-level bound**: (3.128) says
`⟨A, G₁⁻¹A⟩ = ⟨A,Δ_πA⟩ − 2⟨HC_π^{(2)}(A),J⟩ + ‖RD*A‖² + a‖QA‖²`, so a bound
`γ‖A‖² ≤ ⟨A,Δ_πA⟩ − 2⟨HC_π^{(2)}(A),J⟩ + ‖RD*A‖²` gives `hMcoerc` immediately. No separate `M₀`
and no `IsShiftedBy` relation are needed — the `a`-term enters only through `‖Qx‖²`, which is what
makes the cancellation work.

Conclusion: `(γ/q² + a) · ⟨B, QGQ* B⟩ ≤ ‖B‖²`. `γ`, `q`, `a` are bound before `B`. -/
theorem coarse_le_of_shifted_bound
    (hadj : IsAdjointPair Q Qstar) (hMG : ∀ x : H, M (G x) = x)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hMcoerc : ∀ x : H, γ * ‖x‖ ^ 2 + a * ‖Q x‖ ^ 2 ≤ (inner ℝ x (M x) : ℝ))
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    (γ / q ^ 2 + a) * (inner ℝ B (coarseComposite Q G Qstar B) : ℝ) ≤ ‖B‖ ^ 2 := by
  set x : H := G (Qstar B) with hx
  have hMx : M x = Qstar B := hMG (Qstar B)
  -- `⟨B, T B⟩ = ⟨x, M x⟩`.
  have hTval : (inner ℝ B (coarseComposite Q G Qstar B) : ℝ) = (inner ℝ x (M x) : ℝ) := by
    rw [coarseComposite_apply, ← hx, hMx, ← hadj x B, real_inner_comm]
  -- lower bound: `⟨x, M x⟩ ≥ (γ/q² + a)‖Qx‖²`.
  have hqx : ‖Q x‖ ^ 2 ≤ q ^ 2 * ‖x‖ ^ 2 := by
    have h1 := hQ x
    have h2 : (0 : ℝ) ≤ ‖Q x‖ := norm_nonneg _
    nlinarith [norm_nonneg x, hq.le]
  have hlow : (γ / q ^ 2 + a) * ‖Q x‖ ^ 2 ≤ (inner ℝ x (M x) : ℝ) := by
    have hq2 : (0 : ℝ) < q ^ 2 := by positivity
    have : γ / q ^ 2 * ‖Q x‖ ^ 2 ≤ γ * ‖x‖ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hq2]
      nlinarith [hqx, hγ.le]
    nlinarith [hMcoerc x]
  -- upper bound: `⟨x, M x⟩ = ⟨B, Q x⟩ ≤ ‖B‖ ‖Qx‖`.
  have hup : (inner ℝ x (M x) : ℝ) ≤ ‖B‖ * ‖Q x‖ := by
    rw [hMx, real_inner_comm, hadj x B]
    exact real_inner_le_norm B (Q x)
  -- combine: `βn² ≤ ‖B‖n` gives `βn ≤ ‖B‖`, hence `β⟨B,TB⟩ ≤ β‖B‖n ≤ ‖B‖²`.
  set β : ℝ := γ / q ^ 2 + a with hβ
  have hβpos : 0 < β := by
    have : (0 : ℝ) < γ / q ^ 2 := by positivity
    linarith
  have hn : (0 : ℝ) ≤ ‖Q x‖ := norm_nonneg _
  have hcomb : β * ‖Q x‖ ^ 2 ≤ ‖B‖ * ‖Q x‖ := le_trans hlow hup
  have hnb : β * ‖Q x‖ ≤ ‖B‖ := by
    rcases eq_or_lt_of_le hn with h | h
    · rw [← h]; simpa using norm_nonneg B
    · refine le_of_mul_le_mul_right ?_ h
      nlinarith [hcomb]
  rw [hTval]
  calc β * (inner ℝ x (M x) : ℝ) ≤ β * (‖B‖ * ‖Q x‖) := by
        exact mul_le_mul_of_nonneg_left hup hβpos.le
  _ = ‖B‖ * (β * ‖Q x‖) := by ring
  _ ≤ ‖B‖ * ‖B‖ := by exact mul_le_mul_of_nonneg_left hnb (norm_nonneg B)
  _ = ‖B‖ ^ 2 := by ring

/-- The `M₀`-decomposed corollary: (3.128) split into its `a`-free part `M₀` and the shift, with the
`a`-free coercivity `hcoerc` stated on `M₀`. Derived from the primitive, not proved again. -/
theorem coarse_le_of_fine_coercive
    (hadj : IsAdjointPair Q Qstar) (hM : IsShiftedBy Q Qstar M₀ M a)
    (hMG : ∀ x : H, M (G x) = x)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hcoerc : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (M₀ x) : ℝ))
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    (γ / q ^ 2 + a) * (inner ℝ B (coarseComposite Q G Qstar B) : ℝ) ≤ ‖B‖ ^ 2 :=
  coarse_le_of_shifted_bound Q Qstar M G a γ q hadj hMG hγ hq ha
    (fun x => by rw [inner_M_eq Q Qstar M₀ M a hadj hM x]; linarith [hcoerc x]) hQ B

/-- `T = QGQ*` is symmetric, given `M` symmetric and `G = M⁻¹`. -/
theorem coarse_sym (hadj : IsAdjointPair Q Qstar)
    (hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ))
    (hGM : ∀ x : H, G (M x) = x) (hMG : ∀ x : H, M (G x) = x) (u v : K) :
    (inner ℝ u (coarseComposite Q G Qstar v) : ℝ)
      = (inner ℝ (coarseComposite Q G Qstar u) v : ℝ) := by
  have hGsym : ∀ p r : H, (inner ℝ p (G r) : ℝ) = (inner ℝ (G p) r : ℝ) := by
    intro p r
    calc (inner ℝ p (G r) : ℝ) = (inner ℝ (M (G p)) (G r) : ℝ) := by rw [hMG p]
    _ = (inner ℝ (G p) (M (G r)) : ℝ) := (hMsym (G p) (G r)).symm
    _ = (inner ℝ (G p) r : ℝ) := by rw [hMG r]
  calc (inner ℝ u (coarseComposite Q G Qstar v) : ℝ)
      = (inner ℝ (Qstar u) (G (Qstar v)) : ℝ) := by
        rw [coarseComposite_apply, real_inner_comm, hadj (G (Qstar v)) u, real_inner_comm]
  _ = (inner ℝ (G (Qstar u)) (Qstar v) : ℝ) := hGsym _ _
  _ = (inner ℝ (coarseComposite Q G Qstar u) v : ℝ) := by
        rw [coarseComposite_apply, real_inner_comm, hadj (G (Qstar u)) v, real_inner_comm]

/-- `T = QGQ*` is positive semidefinite under the primitive hypothesis. -/
theorem coarse_pos_of_shifted_bound (hadj : IsAdjointPair Q Qstar)
    (hMG : ∀ x : H, M (G x) = x) (hγ : 0 < γ) (ha : 0 ≤ a)
    (hMcoerc : ∀ x : H, γ * ‖x‖ ^ 2 + a * ‖Q x‖ ^ 2 ≤ (inner ℝ x (M x) : ℝ)) (B : K) :
    (0 : ℝ) ≤ (inner ℝ B (coarseComposite Q G Qstar B) : ℝ) := by
  set x : H := G (Qstar B) with hx
  have hMx : M x = Qstar B := hMG (Qstar B)
  have hTval : (inner ℝ B (coarseComposite Q G Qstar B) : ℝ) = (inner ℝ x (M x) : ℝ) := by
    rw [coarseComposite_apply, ← hx, hMx, ← hadj x B, real_inner_comm]
  rw [hTval]
  have h1 : (0 : ℝ) ≤ γ * ‖x‖ ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ a * ‖Q x‖ ^ 2 := by positivity
  linarith [hMcoerc x]

/-- `M₀`-decomposed corollary. -/
theorem coarse_pos (hadj : IsAdjointPair Q Qstar) (hM : IsShiftedBy Q Qstar M₀ M a)
    (hMG : ∀ x : H, M (G x) = x) (hγ : 0 < γ) (ha : 0 ≤ a)
    (hcoerc : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (M₀ x) : ℝ)) (B : K) :
    (0 : ℝ) ≤ (inner ℝ B (coarseComposite Q G Qstar B) : ℝ) :=
  coarse_pos_of_shifted_bound Q Qstar M G a γ hadj hMG hγ ha
    (fun x => by rw [inner_M_eq Q Qstar M₀ M a hadj hM x]; linarith [hcoerc x]) B

end Coarse

/-! ## §4 — THE BRIDGE, `a`-FREE

`⟨B, S B⟩ − a‖B‖² ≥ (γ/q²)‖B‖²`, i.e. (3.156)'s form minus its `a`-subtraction is coercive with
the fine-scale constant divided by `q²` and **nothing else**. -/

section Bridge

variable {H K : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]

variable (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H) (M₀ M G : H →L[ℝ] H) (S : K →L[ℝ] K) (a γ q : ℝ)

/-- **THE BRIDGE (source-free form).** Fine-scale coercivity `γ` of (3.128)'s `a`-free part
transports to `(3.156)`'s `⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩` with constant `γ/q²`, **with no `a`-penalty and
no smallness assumption on `a`**.

Binder order: `γ q a` are all fixed before `B`. -/
theorem bridge_coercive_prim
    (hadj : IsAdjointPair Q Qstar)
    (hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ))
    (hGM : ∀ x : H, G (M x) = x) (hMG : ∀ x : H, M (G x) = x)
    (hTS : ∀ B : K, coarseComposite Q G Qstar (S B) = B)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hMcoerc : ∀ x : H, γ * ‖x‖ ^ 2 + a * ‖Q x‖ ^ 2 ≤ (inner ℝ x (M x) : ℝ))
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    (γ / q ^ 2) * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 := by
  set T : K →L[ℝ] K := coarseComposite Q G Qstar with hT
  set β : ℝ := γ / q ^ 2 + a with hβ
  have hβpos : 0 < β := by
    have : (0 : ℝ) < γ / q ^ 2 := by positivity
    linarith
  have hsym := coarse_sym Q Qstar M G hadj hMsym hGM hMG
  have hpos := coarse_pos_of_shifted_bound Q Qstar M G a γ hadj hMG hγ ha hMcoerc
  -- `T ≤ 1/β` from §3, in the shape §2 consumes.
  have hub : ∀ u : K, (inner ℝ u (T u) : ℝ) ≤ (1 / β) * ‖u‖ ^ 2 := by
    intro u
    have h := coarse_le_of_shifted_bound Q Qstar M G a γ q hadj hMG hγ hq ha hMcoerc hQ u
    rw [← hβ] at h
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hβpos]
    linarith [h]
  have hc : (0 : ℝ) < 1 / β := by positivity
  have hmain := inner_inv_ge_of_le T S hsym hpos hc hub hTS B
  -- `‖B‖²/(1/β) = β‖B‖²`.
  have hrw : ‖B‖ ^ 2 / (1 / β) = β * ‖B‖ ^ 2 := by
    field_simp
  rw [hrw] at hmain
  have : β * ‖B‖ ^ 2 = (γ / q ^ 2) * ‖B‖ ^ 2 + a * ‖B‖ ^ 2 := by rw [hβ]; ring
  linarith [hmain, this ▸ hmain]

/-- **THE BRIDGE, `M₀`-decomposed corollary.** Identical conclusion; the quantitative hypothesis is
split into `M = M₀ + Q*aQ` plus coercivity of `M₀`. -/
theorem bridge_coercive
    (hadj : IsAdjointPair Q Qstar) (hM : IsShiftedBy Q Qstar M₀ M a)
    (hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ))
    (hGM : ∀ x : H, G (M x) = x) (hMG : ∀ x : H, M (G x) = x)
    (hTS : ∀ B : K, coarseComposite Q G Qstar (S B) = B)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hcoerc : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (M₀ x) : ℝ))
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    (γ / q ^ 2) * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 :=
  bridge_coercive_prim Q Qstar M G S a γ q hadj hMsym hGM hMG hTS hγ hq ha
    (fun x => by rw [inner_M_eq Q Qstar M₀ M a hadj hM x]; linarith [hcoerc x]) hQ B

/-- **THE BRIDGE with (3.156)'s source term, PRIMITIVE FORM.** -/
theorem bridge_coercive_with_source_prim
    (src : K → ℝ) (ε : ℝ)
    (hadj : IsAdjointPair Q Qstar)
    (hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ))
    (hGM : ∀ x : H, G (M x) = x) (hMG : ∀ x : H, M (G x) = x)
    (hTS : ∀ B : K, coarseComposite Q G Qstar (S B) = B)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hMcoerc : ∀ x : H, γ * ‖x‖ ^ 2 + a * ‖Q x‖ ^ 2 ≤ (inner ℝ x (M x) : ℝ))
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖)
    (hsrc : ∀ B : K, |src B| ≤ ε * ‖B‖ ^ 2) (B : K) :
    (γ / q ^ 2 - ε) * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 - src B := by
  have h := bridge_coercive_prim Q Qstar M G S a γ q hadj hMsym hGM hMG hTS hγ hq ha hMcoerc hQ B
  have h2 : src B ≤ ε * ‖B‖ ^ 2 := le_trans (le_abs_self _) (hsrc B)
  nlinarith [h, h2]

/-- **THE BRIDGE with (3.156)'s source term carried explicitly.** `src B` stands for
`2⟨H₁D̃^{(2)}(B), J⟩`; `hsrc` is the bound Bałaban justifies on p.421 (*"they are small because the
configuration `J` is small"*), here a HYPOTHESIS with an explicit `ε`, never a theorem. At `J = 0`,
`ε = 0` and the conclusion is §4's. -/
theorem bridge_coercive_with_source
    (src : K → ℝ) (ε : ℝ)
    (hadj : IsAdjointPair Q Qstar) (hM : IsShiftedBy Q Qstar M₀ M a)
    (hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ))
    (hGM : ∀ x : H, G (M x) = x) (hMG : ∀ x : H, M (G x) = x)
    (hTS : ∀ B : K, coarseComposite Q G Qstar (S B) = B)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hcoerc : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (M₀ x) : ℝ))
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖)
    (hsrc : ∀ B : K, |src B| ≤ ε * ‖B‖ ^ 2) (B : K) :
    (γ / q ^ 2 - ε) * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 - src B := by
  have h := bridge_coercive Q Qstar M₀ M G S a γ q hadj hM hMsym hGM hMG hTS hγ hq ha hcoerc hQ B
  have h2 : src B ≤ ε * ‖B‖ ^ 2 := le_trans (le_abs_self _) (hsrc B)
  nlinarith [h, h2]

end Bridge

/-! ## §6 — DE-ISLANDING: the bridge stated on `DeltaKRecursive.deltaKQuadForm`, the tree's own
(3.156) object

This is the theorem the campaign asked for: it concludes about `deltaKQuadForm`, the declaration
`DeltaKRecursive.lean` built as (3.156)'s left-hand side, not about a local restatement.

Two hypotheses are *manufactured, not assumed*:
* the two-sided-inverse hypothesis `hTS` comes from `RGScaleFamily.invertQGQstar_spec` plus
  `IsUnit`, via `Ring.mul_inverse_cancel` — i.e. from the family's own field-level law;
* the `−a⟨B,B⟩` of `deltaKQuadForm` is matched to `a‖B‖²` by `real_inner_self_eq_norm_sq`. -/

section DeIsland

open DeltaKRecursive

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **THE HEADLINE.** For an `RGScaleFamily` whose level-`k` `G₁` is (3.128)-faithful — i.e. is the
two-sided inverse of `M₀ + Q*aQ` for an `a`-free part `M₀` obeying the (3.10)-level coercivity
`γ‖x‖² ≤ ⟨x, M₀x⟩` — the recursive `Δ_k` of (3.156) obeys

`(γ/q² − ε)‖B‖² ≤ deltaKQuadForm F k B`

with `γ, q, a, ε` all bound before `B`, and with **no `a`-penalty**.

`ε` bounds (3.156)'s source term `2⟨H₁D̃^{(2)}(B), J⟩`; at `F.J k = 0` it may be taken `0`. -/
theorem deltaKQuadForm_coercive_of_G1_inverse
    (F : RGScaleFamily H) (k : ℕ) (M : H →L[ℝ] H) (γ q ε : ℝ)
    (hadj : IsAdjointPair (F.Q k) (F.Qstar k))
    (hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ))
    (hMG : ∀ x : H, M (G1 F k x) = x)
    (hGM : ∀ x : H, G1 F k (M x) = x)
    (hunit : IsUnit ((F.Q k).comp ((G1 F k).comp (F.Qstar k))))
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ F.a k)
    (hMcoerc : ∀ x : H,
      γ * ‖x‖ ^ 2 + (F.a k) * ‖(F.Q k) x‖ ^ 2 ≤ (inner ℝ x (M x) : ℝ))
    (hQ : ∀ x : H, ‖(F.Q k) x‖ ≤ q * ‖x‖)
    (hsrc : ∀ B : H, |2 * (inner ℝ (F.H1 k (F.Dtilde2 k B)) (F.J k) : ℝ)| ≤ ε * ‖B‖ ^ 2)
    (B : H) :
    (γ / q ^ 2 - ε) * ‖B‖ ^ 2 ≤ deltaKQuadForm F k B := by
  set T : H →L[ℝ] H := (F.Q k).comp ((G1 F k).comp (F.Qstar k)) with hTdef
  set S : H →L[ℝ] H := F.invertQGQstar k (F.Q k) (G1 F k) (F.Qstar k) with hSdef
  have hSeq : S = Ring.inverse T := F.invertQGQstar_spec k (G1 F k) hunit
  have hTS : ∀ B : H, coarseComposite (F.Q k) (G1 F k) (F.Qstar k) (S B) = B := by
    intro B
    have hmul : T * Ring.inverse T = 1 := Ring.mul_inverse_cancel T hunit
    have : (T * Ring.inverse T) B = B := by rw [hmul]; rfl
    rw [hSeq]
    exact this
  have hmain := bridge_coercive_with_source_prim (F.Q k) (F.Qstar k) M (G1 F k) S (F.a k) γ q
    (fun B => 2 * (inner ℝ (F.H1 k (F.Dtilde2 k B)) (F.J k) : ℝ)) ε
    hadj hMsym hGM hMG hTS hγ hq ha hMcoerc hQ hsrc B
  have hdk : deltaKQuadForm F k B
      = (inner ℝ B (S B) : ℝ) - (F.a k) * ‖B‖ ^ 2
          - 2 * (inner ℝ (F.H1 k (F.Dtilde2 k B)) (F.J k) : ℝ) := by
    rw [deltaKQuadForm, ← hSdef, real_inner_self_eq_norm_sq]
  rw [hdk]
  exact hmain

/-- The `M₀`-decomposed form of the headline: (3.128) split into its `a`-free part and the
`Q*aQ` shift. Derived from `deltaKQuadForm_coercive_of_G1_inverse`. -/
theorem deltaKQuadForm_coercive_of_fine_coercivity
    (F : RGScaleFamily H) (k : ℕ) (M₀ : H →L[ℝ] H) (γ q ε : ℝ)
    (hadj : IsAdjointPair (F.Q k) (F.Qstar k))
    (hM₀sym : ∀ u v : H, (inner ℝ u (M₀ v) : ℝ) = (inner ℝ (M₀ u) v : ℝ))
    (hMG : ∀ x : H, M₀ (G1 F k x) + (F.Qstar k) ((F.a k) • (F.Q k) (G1 F k x)) = x)
    (hGM : ∀ x : H, G1 F k (M₀ x + (F.Qstar k) ((F.a k) • (F.Q k) x)) = x)
    (hunit : IsUnit ((F.Q k).comp ((G1 F k).comp (F.Qstar k))))
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ F.a k)
    (hcoerc : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (M₀ x) : ℝ))
    (hQ : ∀ x : H, ‖(F.Q k) x‖ ≤ q * ‖x‖)
    (hsrc : ∀ B : H, |2 * (inner ℝ (F.H1 k (F.Dtilde2 k B)) (F.J k) : ℝ)| ≤ ε * ‖B‖ ^ 2)
    (B : H) :
    (γ / q ^ 2 - ε) * ‖B‖ ^ 2 ≤ deltaKQuadForm F k B := by
  -- the (3.128)-shifted operator, bundled
  set M : H →L[ℝ] H := M₀ + (F.Qstar k).comp ((F.a k) • (F.Q k)) with hMdef
  have hMapp : ∀ x : H, M x = M₀ x + (F.Qstar k) ((F.a k) • (F.Q k) x) := by
    intro x; rw [hMdef]; rfl
  have hM : IsShiftedBy (F.Q k) (F.Qstar k) M₀ M (F.a k) := hMapp
  have hMG' : ∀ x : H, M (G1 F k x) = x := by intro x; rw [hMapp]; exact hMG x
  have hGM' : ∀ x : H, G1 F k (M x) = x := by intro x; rw [hMapp]; exact hGM x
  have hshiftsym : ∀ u v : H,
      (inner ℝ u ((F.Qstar k) ((F.a k) • (F.Q k) v)) : ℝ)
        = (inner ℝ ((F.Qstar k) ((F.a k) • (F.Q k) u)) v : ℝ) := by
    intro u v
    rw [real_inner_comm ((F.Qstar k) ((F.a k) • (F.Q k) v)) u,
      hadj u ((F.a k) • (F.Q k) v), hadj v ((F.a k) • (F.Q k) u),
      real_inner_smul_left, real_inner_smul_left,
      real_inner_comm ((F.Q k) u) ((F.Q k) v)]
  have hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ) := by
    intro u v
    rw [hMapp, hMapp, inner_add_right, inner_add_left, hM₀sym u v, hshiftsym u v]
  exact deltaKQuadForm_coercive_of_G1_inverse F k M γ q ε hadj hMsym hMG' hGM' hunit hγ hq ha
    (fun x => by rw [inner_M_eq (F.Q k) (F.Qstar k) M₀ M (F.a k) hadj hM x]; linarith [hcoerc x])
    hQ hsrc B

end DeIsland

/-! ## §7 — A CONCRETE WITNESS: every hypothesis satisfied at once, the bound non-trivial, and the
`a`-cancellation exhibited numerically

`§4`/`§5`/`§6` are implications. Without an instance where the whole hypothesis set holds *and* the
conclusion says something, they could be vacuously true of nothing. §7a builds the instance
abstractly from a single vector `v` with `⟪v,v⟫ = 2`; §7b instantiates it on
`EuclideanSpace ℝ (Fin 2)` at `v = (1,1)`, where `Q` is genuinely **space-changing and
non-injective** — `Q (1,−1) = 0` with `(1,−1) ≠ 0`, so `Q` really is an averaging that loses
information, not a disguised isomorphism.

The witness runs at `a = 1`, **not** `a = 0`: `⟪B,SB⟫ = (3/2)‖B‖²` while
`⟪B,SB⟫ − a‖B‖² = (1/2)‖B‖²`. The `a`-subtraction of (3.156) changes the value, and the bridge's
conclusion survives it — that is the cancellation, exhibited.

§7c is the must-fail control: replacing `S` by `(3/4)·id` — which is **not** the inverse of
`T` — makes §4's conclusion FALSE. So the two-sided-inverse hypothesis is load-bearing, not decoration. -/

section Witness

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Real inner product on `ℝ` is multiplication. -/
theorem inner_real_real (x y : ℝ) : (inner ℝ x y : ℝ) = x * y := by
  simp [RCLike.inner_apply]
  ring

/-- `Q := ⟪v, ·⟫ : H →L[ℝ] ℝ` — the witness averaging map. -/
noncomputable def wQ (v : H) : H →L[ℝ] ℝ := innerSL ℝ v

/-- `Q* := (· • v) : ℝ →L[ℝ] H`. -/
noncomputable def wQstar (v : H) : ℝ →L[ℝ] H :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight v

@[simp] theorem wQ_apply (v x : H) : wQ v x = (inner ℝ v x : ℝ) := rfl

@[simp] theorem wQstar_apply (v : H) (t : ℝ) : wQstar v t = t • v := rfl

/-- The `a`-free fine operator: the identity, so `γ = 1`. -/
noncomputable def wM0 : H →L[ℝ] H := ContinuousLinearMap.id ℝ H

/-- `M = M₀ + Q* a Q` at `a = 1`. -/
noncomputable def wM (v : H) : H →L[ℝ] H :=
  wM0 + (wQstar v).comp ((1 : ℝ) • wQ v)

/-- `G = M⁻¹`, in closed form (Sherman–Morrison at `⟪v,v⟫ = 2`). -/
noncomputable def wG (v : H) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - (1 / 3 : ℝ) • ((wQstar v).comp (wQ v))

/-- `S = (Q G Q*)⁻¹`. -/
noncomputable def wS : ℝ →L[ℝ] ℝ := (3 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

/-- The wrong `S`: `(3/4)·id` is NOT the inverse of `Q G Q* = (2/3)·id`. §7c. -/
noncomputable def wSbad : ℝ →L[ℝ] ℝ := (3 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ

variable (v : H) (hv : (inner ℝ v v : ℝ) = 2)

theorem wM_apply (x : H) : wM v x = x + (inner ℝ v x : ℝ) • v := by
  simp [wM, wM0]

theorem wG_apply (x : H) : wG v x = x - (1 / 3 : ℝ) • ((inner ℝ v x : ℝ) • v) := by
  simp [wG]

include hv

omit hv in
theorem w_adj : IsAdjointPair (wQ v) (wQstar v) := by
  intro x B
  rw [wQstar_apply, wQ_apply, inner_real_real, real_inner_smul_left]

omit hv in
theorem w_shifted : IsShiftedBy (wQ v) (wQstar v) wM0 (wM v) 1 := by
  intro x; rfl

omit hv in
theorem w_M0_sym (u w : H) : (inner ℝ u (wM0 w) : ℝ) = (inner ℝ (wM0 u) w : ℝ) := rfl

theorem w_M_sym (u w : H) : (inner ℝ u (wM v w) : ℝ) = (inner ℝ (wM v u) w : ℝ) := by
  rw [wM_apply, wM_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm u v]
  ring

theorem w_MG (x : H) : wM v (wG v x) = x := by
  rw [wG_apply, wM_apply, inner_sub_right, real_inner_smul_right, real_inner_smul_right, hv]
  module

theorem w_GM (x : H) : wG v (wM v x) = x := by
  rw [wM_apply, wG_apply, inner_add_right, real_inner_smul_right, hv]
  module

/-- **The coarse composite is exactly `(2/3)·id`** — computed, not assumed. -/
theorem w_coarse (B : ℝ) : coarseComposite (wQ v) (wG v) (wQstar v) B = (2 / 3 : ℝ) * B := by
  rw [coarseComposite_apply, wQstar_apply, wG_apply, wQ_apply, inner_sub_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, hv]
  ring

theorem w_TS (B : ℝ) : coarseComposite (wQ v) (wG v) (wQstar v) (wS B) = B := by
  rw [w_coarse v hv]
  show (2 / 3 : ℝ) * ((3 / 2 : ℝ) * B) = B
  ring

theorem w_coerc (x : H) : (1 : ℝ) * ‖x‖ ^ 2 ≤ (inner ℝ x (wM0 x) : ℝ) := by
  rw [wM0]
  show (1 : ℝ) * ‖x‖ ^ 2 ≤ (inner ℝ x x : ℝ)
  rw [real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

/-- `‖v‖ = √2 ≤ 2`, so `q = 2` is a legitimate (non-sharp) bound. -/
theorem w_Q_bound (x : H) : ‖wQ v x‖ ≤ 2 * ‖x‖ := by
  have hnv : ‖v‖ ^ 2 = 2 := by rw [← real_inner_self_eq_norm_sq]; exact hv
  have hnv2 : ‖v‖ ≤ 2 := by nlinarith [norm_nonneg v, hnv]
  have h1 : ‖wQ v x‖ = |(inner ℝ v x : ℝ)| := by rw [wQ_apply, Real.norm_eq_abs]
  rw [h1]
  calc |(inner ℝ v x : ℝ)| ≤ ‖v‖ * ‖x‖ := abs_real_inner_le_norm v x
  _ ≤ 2 * ‖x‖ := by nlinarith [norm_nonneg x, hnv2]

/-- **THE WITNESS, ASSEMBLED**: §4's bridge applies, with `γ = 1`, `q = 2`, `a = 1`. -/
theorem w_bridge (B : ℝ) : (1 / 2 ^ 2 : ℝ) * ‖B‖ ^ 2 ≤ (inner ℝ B (wS B) : ℝ) - 1 * ‖B‖ ^ 2 :=
  bridge_coercive (wQ v) (wQstar v) wM0 (wM v) (wG v) wS 1 1 2
    (w_adj v) (w_shifted v) (w_M_sym v hv) (w_GM v hv) (w_MG v hv) (w_TS v hv)
    one_pos two_pos zero_le_one (w_coerc v hv) (w_Q_bound v hv) B

/-! ### §7c — MUST-FAIL CONTROL: the two-sided-inverse hypothesis is load-bearing -/

/-- `wSbad` is **not** a right inverse of the coarse composite. -/
theorem w_Sbad_not_inverse :
    ¬ (∀ B : ℝ, coarseComposite (wQ v) (wG v) (wQstar v) (wSbad B) = B) := by
  intro hcon
  have h := hcon 1
  rw [w_coarse v hv] at h
  have : ((2 : ℝ) / 3) * ((3 / 4 : ℝ) • (1 : ℝ)) = 1 := h
  norm_num at this

end Witness

/-! ### §7d — the two `v`-independent facts: the exact numbers, and the must-fail control -/

section Numbers

/-- **NON-VACUITY, with the exact numbers**: at `B = 1` the (3.156)-shaped quantity
`⟪B,SB⟫ − a‖B‖²` equals `1/2`, strictly above the bridge's `γ/q² = 1/4`, while the un-subtracted
`⟪B,SB⟫` equals `3/2`. The `a`-term is genuinely present (`3/2 ≠ 1/2`) and the conclusion genuinely
survives its subtraction. -/
theorem w_values : (inner ℝ (1 : ℝ) (wS 1) : ℝ) = 3 / 2
    ∧ (inner ℝ (1 : ℝ) (wS 1) : ℝ) - 1 * ‖(1 : ℝ)‖ ^ 2 = 1 / 2
    ∧ (1 / 2 ^ 2 : ℝ) * ‖(1 : ℝ)‖ ^ 2 = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · show (inner ℝ (1 : ℝ) ((3 / 2 : ℝ) • (1 : ℝ)) : ℝ) = 3 / 2
    rw [inner_real_real]; norm_num
  · show (inner ℝ (1 : ℝ) ((3 / 2 : ℝ) • (1 : ℝ)) : ℝ) - 1 * ‖(1 : ℝ)‖ ^ 2 = 1 / 2
    rw [inner_real_real, Real.norm_eq_abs]; norm_num
  · rw [Real.norm_eq_abs]; norm_num

/-- **And with `wSbad` in place of `wS`, §4's CONCLUSION IS FALSE** — at `B = 1` the left side is
`1/4` and the right side is `−1/4`. A check that could not fail would survive this substitution;
this one does not. -/
theorem w_bridge_fails_for_Sbad :
    ¬ (∀ B : ℝ, (1 / 2 ^ 2 : ℝ) * ‖B‖ ^ 2 ≤ (inner ℝ B (wSbad B) : ℝ) - 1 * ‖B‖ ^ 2) := by
  intro hcon
  have h := hcon 1
  have hb : wSbad (1 : ℝ) = 3 / 4 := by simp [wSbad]
  rw [hb, inner_real_real, Real.norm_eq_abs] at h
  norm_num at h

end Numbers

/-! ### §7b — the witness carrier: `Q` is space-changing AND non-injective -/

section ConcreteCarrier

/-- `v = (1,1) ∈ ℝ²`. -/
noncomputable def vWit : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 1]

/-- `w = (1,−1) ∈ ℝ²`, a nonzero vector `Q` annihilates. -/
noncomputable def wKer : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, -1]

theorem vWit_inner_self : (inner ℝ vWit vWit : ℝ) = 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold vWit
  norm_num [dotProduct, Fin.sum_univ_two]

/-- **`Q` genuinely loses information**: `Q wKer = 0` while `wKer ≠ 0`. So the witness does not
secretly run on an invertible `Q`, and the theorem is not being tested on a disguised
one-dimensional problem. -/
theorem wKer_ne_zero : wKer ≠ 0 := by
  intro hcon
  have h1 := congrFun (congrArg (fun (u : EuclideanSpace ℝ (Fin 2)) => WithLp.ofLp u) hcon) 0
  unfold wKer at h1
  norm_num at h1

theorem wQ_vWit_wKer : wQ vWit wKer = 0 := by
  rw [wQ_apply, EuclideanSpace.inner_eq_star_dotProduct]
  unfold vWit wKer
  norm_num [dotProduct, Fin.sum_univ_two]

/-- **The bridge, on the concrete carrier.** `γ = 1`, `q = 2`, `a = 1`, `H = ℝ²`, `K = ℝ`,
`Q = ⟪(1,1), ·⟫` non-injective.

⚠ **THIS WITNESSES §4's `bridge_coercive`, NOT §9's HEADLINE** (flagged by two independent
prosecutor families, 2026-07-28). It exercises the bundled abstract chain at a concrete carrier; it
does NOT instantiate `bridge_from_piExtended_normalized_threeTen`, whose fine operator is
`deltaKCLMNormalized U` on `BondFnL2 L`. **The headline has no witness, and §9f proves why**
(`fineMapOf_surjective_of_hG1`, `h310_unrestricted_forces_zero_norm_at_witnessU`). Do not read this
declaration as evidence for the headline. -/
theorem bridge_at_concrete_carrier (B : ℝ) :
    (1 / 2 ^ 2 : ℝ) * ‖B‖ ^ 2 ≤ (inner ℝ B (wS B) : ℝ) - 1 * ‖B‖ ^ 2 :=
  w_bridge vWit vWit_inner_self B

end ConcreteCarrier

/-! ## §9 — THE CHAIN CLOSED ON THE CAMPAIGN'S OWN CARRIER: (3.10) ⟹ (3.156)

§4–§6 need the fine-scale operator as a bundled `H →L[ℝ] H`. `DeltaKFull.lean` §6 records the
`.adjoint`/Riesz route to that promotion as a WALL. **That wall has a bypass already in the tree**
(grep before building, LAW-19): `CStarDeltaKCOperator.bondAdjoint` is a handwritten combinatorial
adjoint on `BondFnL2 L`, and `LinearMap.toContinuousLinearMap` promotes on this finite-dimensional
carrier. Composing them, `DeltaPrimeOperator.deltaKCLM U : BondFnL2 L →L[ℝ] BondFnL2 L` already
exists **unconditionally**, with

* `DeltaPrimeOperator.inner_deltaKCLM_eq` :
  `⟪toLp A, deltaKCLM U (toLp A)⟫ = DeltaKFull.deltaKQuadFormCorrected U A` — the (3.10) form;
* `DeltaPrimeOperator.deltaKCLM_symm` : symmetry.

So the promotion is NOT a residual of this lane and NOT an obstruction to the bridge. This section
consumes those two declarations and closes the chain from the campaign's (3.10) results to (3.156).

The coercivity hypothesis `h310` below is stated as `γ · ‖toLp A‖² ≤ deltaKQuadFormCorrected U A`.
That is **exactly** the campaign's `γ · bondEnergy A ≤ …` shape: `‖toLp A‖² = bondEnergy A` is
already proved twice in-tree, at `IslandBridge.norm_sq_bondFnL2` and
`CoercivitySupply.norm_sq_toLp` (cited, not re-derived, and not imported — keeping this module a
two-import leaf).

**WHAT THE (3.10) RESULTS DO GIVE, EXACTLY** — the answer to the dispatch's item 4. Substituting
`h310` into §9's chain, the campaign's existing (3.10)-level coercivity yields (3.156)'s `Δ_k`
coercivity with constant `γ/q² − ε`, on the following three further inputs, each a NAMED hypothesis
of `threeTen_transports_to_deltaK` and none of them proved here:

1. `hPpos`/`hPsym` — that (3.128)'s remainder `‖RD*·‖² − 2⟨H C_π^{(2)}(·), J⟩` is symmetric and
   positive semidefinite. Bałaban's stated reason (p.421, verbatim) is *"they are small because the
   configuration `J` is small"*; at `J = 0` the remainder is `‖RD*·‖² ≥ 0` outright.
2. `hG1L`/`hG1R` — that `G₁` inverts (3.128)'s operator. This is (3.128) itself, read as a
   definition of `G₁`.
3. `hQ` — a bound `‖Q x‖ ≤ q‖x‖` on the block average, and `hTS`, the invertibility of
   `Q G₁ Q*`. ⚠ **CORRECTED 2026-07-28.** An earlier version of this paragraph attributed `hTS` to
   p.428's citation of [4] Lemma 2.4. **That is a misattribution.** Read on the adjudicated page,
   the Lemma 2.4 citation is attached to the POSITIVE-DEFINITENESS OF `C*Δ_kC`, verbatim:
   *"it is defined by a positive definite operator `C*Δ_kC` with a lower bound `γ₀ > 0` independent
   of `k` and `U`. We have proved it in [4], Lemma 2.4, for operators with `U=1`."* The
   invertibility of `QG₁Q*` is USED on p.421 (3.129) and p.428 (3.156) with **no citation at all**.
   So `hTS` is on WEAKER footing than previously written, not stronger: it is not even a deferred
   citation, it is an unremarked assumption of the source.
4. `hpi` — the two-sided bound on (3.120)'s `Δ′_π`, which p.419 explicitly defers (§9e).

Nothing in the chain needs `a` small, and nothing needs a threshold relating `a` to `γ` — the
`a`-cancellation is exact. ⚠ **But that is not the only threshold in play**: whether the transported
bound is a COERCIVITY at all requires `ε < (γ−δ)/q²`, where `ε` prices (3.156)'s source term. That
threshold is separate from the `a` question, it is now an explicit hypothesis of
`deltaK_form_pos_of_threshold`, and the source-free headline avoids it entirely by not mentioning
`src`.
-/

/-! ### §9b — THE SAME CHAIN WITH THE FINE-SIDE MAPS AS BARE FUNCTIONS

§9's `threeTen_transports_to_deltaK` cannot be stated with `Q : BondFnL2 L →L[ℝ] K` and then fed to
§4's machinery: `BondFnL2 L = PiLp 2 (fun _ : Bond L => SuTwo)` carries TWO non-defeq instance paths,
and `ContinuousLinearMap`'s `Module`/`TopologicalSpace` arguments pick different ones on each side —
`WithLp.instModule` / `PiLp.topologicalSpace` when the type is written directly, versus
`InnerProductSpace.toNormedSpace.toModule` / `PseudoMetricSpace.toUniformSpace.toTopologicalSpace`
when it comes through `[InnerProductSpace ℝ H]`. ~~They are only PROPOSITIONALLY equal~~ — that is
exactly what `DeltaKFull.lean` §4 had to prove for `PlaqFnL2` (`plaqL2UniformSpace_bridge`), because
`SuTwo` is a `Submodule` subtype whose uniformity comes from `instUniformSpaceSubtype`, not from its
norm.

**⚠ STALE AS OF 2026-07-28 — MAIN-LOOP CORRECTION (S75 in place, struck above).** The "only
PROPOSITIONALLY equal" claim no longer holds: **both named components are now `rfl`.** The `Module`
component already was (`CoercivityRegular.module_diamond_is_rfl`), and the topology/uniformity
component was closed by repairing the actual cause — `SuTwoInner.instNormedAddCommGroupSuTwo` is now
built through `MetricSpace.replaceUniformity`, so `SuTwo`'s registered uniformity IS its norm
uniformity definitionally. See `SuTwoInner.uniformSpace_diamond_is_rfl`,
`topologicalSpace_diamond_is_rfl`, `pilp_topology_diamond_is_rfl_at_suTwo_fibre`, and at the real
index type `SuTwoDiamondUnblocked.pilp_topology_diamond_is_rfl_at_bond`.

**The norm did NOT change** — `SuTwoInner.norm_unchanged_by_uniformity_repair` and
`dist_unchanged_by_uniformity_repair` are `rfl` against a retained byte-identical `suTwoNormedRaw`,
and Bałaban's `tr 1 = 1` normalization is intact. Only the uniformity FIELD moved.

**Consequence for §9b's workaround:** the "unbundle the fine side and weaken to
`SeminormedAddCommGroup`" manoeuvre below was forced by this diamond and is plausibly no longer
necessary. **That has NOT been tested** — the module is left as-is rather than rewritten on an
untested assumption. The mechanism is fixed; whether this particular consumer can now be simplified is
an open, cheap question for whoever next edits this file.

The error text below is the MEASURED pre-repair failure and is retained as the record of what the
diamond did, not as a current fact. Verbatim from `compute/recursive_bridge/build11.log`:

```
Application type mismatch: Qstar has type ... (BondFnL2 L) (PiLp.topologicalSpace 2 fun x ↦ ↥SuTwo)
  (WithLp.instAddCommGroup ...) (WithLp.instModule 2 ℝ ...)
but is expected to have type ... PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  NormedAddCommGroup.toAddCommGroup.toAddCommMonoid InnerProductSpace.toNormedSpace.toModule
```

**This is not a residual and it is not the mathematics: it is two bundling choices, and removing
both removes it.** The fix has two independent halves, BOTH measured, and the docstring records
both because the first alone is not sufficient:

1. **Unbundle the fine side.** The fine-side maps are used in §3–§5 through APPLICATION ONLY — no
   linearity of any `H`-side map is ever invoked — so §9b restates the chain with `Q`, `Qstar`,
   `M`, `G` as bare functions. This removes `ContinuousLinearMap`'s `Module`/`TopologicalSpace`
   arguments from every `BondFnL2 L` slot. Only `T` and `S` stay bundled; they live on the COARSE
   space, which is left abstract.
2. **Weaken `[NormedAddCommGroup]` to `[SeminormedAddCommGroup]`** throughout §1–§5 and §9b. This
   was necessary, not cosmetic: with `[NormedAddCommGroup H]` Lean reports, verbatim
   (`compute/recursive_bridge/build16.log`), `failed to synthesize instance of type class
   InnerProductSpace ℝ (BondFnL2 L)` — because `PiLp.innerProductSpace` is registered over
   `PiLp.seminormedAddCommGroup`, and the `NormedAddCommGroup` instance Lean picks first carries a
   different `Norm` (`NormedAddCommGroup.toNorm` vs `PiLp.instNorm`). Over
   `SeminormedAddCommGroup` the two paths coincide and the instantiation goes through. Nothing is
   lost: `NormedAddCommGroup.toSeminormedAddCommGroup` is an instance, so §6 — which must stay
   `NormedAddCommGroup` because `DeltaKRecursive.RGScaleFamily` demands it — still consumes §1–§5.

`Inner`, `Norm` and `SMul` on `BondFnL2 L` then have a single instance path, which is why the tree
already applies generic `real_inner_*` lemmas to this carrier (e.g. `IslandBridge.norm_sq_bondFnL2`).

The proofs are the same proofs. -/

section BareFine

variable {H K : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]

variable (Q : H → K) (Qstar : K → H) (M G : H → H) (T S : K →L[ℝ] K) (a γ q : ℝ)

/-- §3's sharp coarse bound, fine side unbundled.

**`hMcoercAt` is required ONLY along `G ∘ Q*`** — the only points at which the proof ever evaluates
the fine form. This is not a cosmetic weakening: the campaign's (3.10)-level coercivity holds on a
RESTRICTED domain (`ker Q₁(U) ∩ axial-gauge`), never on all of `BondFnL2 L`, and an unrestricted
`∀ x` hypothesis here would be false for every background (see `h310_unrestricted_impossible_at_witnessU`). -/
theorem coarse_le_bare
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hMG : ∀ x : H, M (G x) = x)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hMcoercAt : ∀ C : K, γ * ‖G (Qstar C)‖ ^ 2 + a * ‖Q (G (Qstar C))‖ ^ 2
      ≤ (inner ℝ (G (Qstar C)) (M (G (Qstar C))) : ℝ))
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    (γ / q ^ 2 + a) * (inner ℝ B (T B) : ℝ) ≤ ‖B‖ ^ 2 := by
  set x : H := G (Qstar B) with hx
  have hMx : M x = Qstar B := hMG (Qstar B)
  have hTval : (inner ℝ B (T B) : ℝ) = (inner ℝ x (M x) : ℝ) := by
    rw [hT B, ← hx, hMx, ← hadj x B, real_inner_comm]
  have hqx : ‖Q x‖ ^ 2 ≤ q ^ 2 * ‖x‖ ^ 2 := by
    have h1 := hQ x
    have h2 : (0 : ℝ) ≤ ‖Q x‖ := norm_nonneg _
    nlinarith [norm_nonneg x, hq.le]
  have hlow : (γ / q ^ 2 + a) * ‖Q x‖ ^ 2 ≤ (inner ℝ x (M x) : ℝ) := by
    have hq2 : (0 : ℝ) < q ^ 2 := by positivity
    have : γ / q ^ 2 * ‖Q x‖ ^ 2 ≤ γ * ‖x‖ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hq2]
      nlinarith [hqx, hγ.le]
    nlinarith [hMcoercAt B]
  have hup : (inner ℝ x (M x) : ℝ) ≤ ‖B‖ * ‖Q x‖ := by
    rw [hMx, real_inner_comm, hadj x B]
    exact real_inner_le_norm B (Q x)
  set β : ℝ := γ / q ^ 2 + a with hβ
  have hβpos : 0 < β := by
    have : (0 : ℝ) < γ / q ^ 2 := by positivity
    linarith
  have hn : (0 : ℝ) ≤ ‖Q x‖ := norm_nonneg _
  have hcomb : β * ‖Q x‖ ^ 2 ≤ ‖B‖ * ‖Q x‖ := le_trans hlow hup
  have hnb : β * ‖Q x‖ ≤ ‖B‖ := by
    rcases eq_or_lt_of_le hn with h | h
    · rw [← h]; simpa using norm_nonneg B
    · refine le_of_mul_le_mul_right ?_ h
      nlinarith [hcomb]
  rw [hTval]
  calc β * (inner ℝ x (M x) : ℝ) ≤ β * (‖B‖ * ‖Q x‖) :=
        mul_le_mul_of_nonneg_left hup hβpos.le
  _ = ‖B‖ * (β * ‖Q x‖) := by ring
  _ ≤ ‖B‖ * ‖B‖ := mul_le_mul_of_nonneg_left hnb (norm_nonneg B)
  _ = ‖B‖ ^ 2 := by ring

/-- `T` is positive semidefinite, fine side unbundled, `hMcoercAt` required only along `G ∘ Q*`. -/
theorem coarse_pos_bare
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hMG : ∀ x : H, M (G x) = x) (hγ : 0 < γ) (ha : 0 ≤ a)
    (hMcoercAt : ∀ C : K, γ * ‖G (Qstar C)‖ ^ 2 + a * ‖Q (G (Qstar C))‖ ^ 2
      ≤ (inner ℝ (G (Qstar C)) (M (G (Qstar C))) : ℝ)) (B : K) :
    (0 : ℝ) ≤ (inner ℝ B (T B) : ℝ) := by
  set x : H := G (Qstar B) with hx
  have hMx : M x = Qstar B := hMG (Qstar B)
  have hTval : (inner ℝ B (T B) : ℝ) = (inner ℝ x (M x) : ℝ) := by
    rw [hT B, ← hx, hMx, ← hadj x B, real_inner_comm]
  rw [hTval]
  have h1 : (0 : ℝ) ≤ γ * ‖x‖ ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ a * ‖Q x‖ ^ 2 := by positivity
  linarith [hMcoercAt B]

/-- `T` is symmetric, fine side unbundled. -/
theorem coarse_sym_bare
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ))
    (hMG : ∀ x : H, M (G x) = x) (u v : K) :
    (inner ℝ u (T v) : ℝ) = (inner ℝ (T u) v : ℝ) := by
  have hGsym : ∀ p r : H, (inner ℝ p (G r) : ℝ) = (inner ℝ (G p) r : ℝ) := by
    intro p r
    calc (inner ℝ p (G r) : ℝ) = (inner ℝ (M (G p)) (G r) : ℝ) := by rw [hMG p]
    _ = (inner ℝ (G p) (M (G r)) : ℝ) := (hMsym (G p) (G r)).symm
    _ = (inner ℝ (G p) r : ℝ) := by rw [hMG r]
  have hflip : ∀ (w : H) (B : K), (inner ℝ (Q w) B : ℝ) = (inner ℝ w (Qstar B) : ℝ) := by
    intro w B
    rw [real_inner_comm B (Q w), ← hadj w B]
    exact real_inner_comm w (Qstar B)
  calc (inner ℝ u (T v) : ℝ) = (inner ℝ (Qstar u) (G (Qstar v)) : ℝ) := by
        rw [hT v, ← hadj (G (Qstar v)) u]
  _ = (inner ℝ (G (Qstar u)) (Qstar v) : ℝ) := hGsym _ _
  _ = (inner ℝ (T u) v : ℝ) := by
        rw [hT u, hflip (G (Qstar u)) v]

/-- **THE BRIDGE, SOURCE-FREE.** This is the protected statement: it contains **no free-sign term
and no `ε`**, so it cannot be rigged by a source. `(γ/q²)‖B‖² ≤ ⟨B,SB⟩ − a‖B‖²`. -/
theorem bridge_bare
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ))
    (hMG : ∀ x : H, M (G x) = x)
    (hTS : ∀ B : K, T (S B) = B)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hMcoercAt : ∀ C : K, γ * ‖G (Qstar C)‖ ^ 2 + a * ‖Q (G (Qstar C))‖ ^ 2
      ≤ (inner ℝ (G (Qstar C)) (M (G (Qstar C))) : ℝ))
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    (γ / q ^ 2) * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 := by
  set β : ℝ := γ / q ^ 2 + a with hβ
  have hβpos : 0 < β := by
    have : (0 : ℝ) < γ / q ^ 2 := by positivity
    linarith
  have hsym := coarse_sym_bare Q Qstar M G T hadj hT hMsym hMG
  have hpos := coarse_pos_bare Q Qstar M G T a γ hadj hT hMG hγ ha hMcoercAt
  have hub : ∀ u : K, (inner ℝ u (T u) : ℝ) ≤ (1 / β) * ‖u‖ ^ 2 := by
    intro u
    have h := coarse_le_bare Q Qstar M G T a γ q hadj hT hMG hγ hq ha hMcoercAt hQ u
    rw [← hβ] at h
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hβpos]
    linarith [h]
  have hc : (0 : ℝ) < 1 / β := by positivity
  have hmain := inner_inv_ge_of_le T S hsym hpos hc hub hTS B
  have hrw : ‖B‖ ^ 2 / (1 / β) = β * ‖B‖ ^ 2 := by field_simp
  rw [hrw] at hmain
  have hsplit : β * ‖B‖ ^ 2 = (γ / q ^ 2) * ‖B‖ ^ 2 + a * ‖B‖ ^ 2 := by rw [hβ]; ring
  linarith [hmain, hsplit]

/-- **THE BRIDGE with (3.156)'s source term.** ⚠ **This form CAN be true and non-coercive.** With
`src B := c‖B‖²` and `ε := c` the conclusion degenerates to `(γ/q² − c)‖B‖² ≤ …`, which for
`c ≥ γ/q²` asserts nothing. It carries the source honestly but it is NOT a coercivity statement;
`bridge_bare_pos` is. Prefer `bridge_bare` (source-free) when `src` is not needed. -/
theorem bridge_bare_src (src : K → ℝ) (ε : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ))
    (hMG : ∀ x : H, M (G x) = x)
    (hTS : ∀ B : K, T (S B) = B)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hMcoercAt : ∀ C : K, γ * ‖G (Qstar C)‖ ^ 2 + a * ‖Q (G (Qstar C))‖ ^ 2
      ≤ (inner ℝ (G (Qstar C)) (M (G (Qstar C))) : ℝ))
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖)
    (hsrc : ∀ B : K, |src B| ≤ ε * ‖B‖ ^ 2) (B : K) :
    (γ / q ^ 2 - ε) * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 - src B := by
  have h := bridge_bare Q Qstar M G T S a γ q hadj hT hMsym hMG hTS hγ hq ha hMcoercAt hQ B
  have h2 : src B ≤ ε * ‖B‖ ^ 2 := le_trans (le_abs_self _) (hsrc B)
  nlinarith [h, h2]

/-- **THE ONLY FORM THAT IS A COERCIVITY STATEMENT.** It carries the threshold `ε < γ/q²` that the
source term must beat, and concludes STRICT positivity at every `B ≠ 0`. A bound that reads
`(γ/q² − ε)‖B‖² ≤ …` with `ε ≥ γ/q²` cannot be mistaken for this. -/
theorem bridge_bare_pos (src : K → ℝ) (ε : ℝ)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hMsym : ∀ u v : H, (inner ℝ u (M v) : ℝ) = (inner ℝ (M u) v : ℝ))
    (hMG : ∀ x : H, M (G x) = x)
    (hTS : ∀ B : K, T (S B) = B)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hMcoercAt : ∀ C : K, γ * ‖G (Qstar C)‖ ^ 2 + a * ‖Q (G (Qstar C))‖ ^ 2
      ≤ (inner ℝ (G (Qstar C)) (M (G (Qstar C))) : ℝ))
    (hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖)
    (hsrc : ∀ B : K, |src B| ≤ ε * ‖B‖ ^ 2)
    (hthr : ε < γ / q ^ 2) {B : K} (hB : ‖B‖ ≠ 0) :
    0 < (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 - src B := by
  have h := bridge_bare_src Q Qstar M G T S a γ q src ε hadj hT hMsym hMG hTS hγ hq ha
    hMcoercAt hQ hsrc B
  have hn : 0 < ‖B‖ ^ 2 := by
    have := norm_nonneg B
    positivity
  nlinarith [h, hthr, hn]

/-! ### §9c — DEGENERACY BLOCKS, PROVED (not asserted)

The obvious way to make §9b vacuous is `Q := 0` (an "averaging" that forgets everything), which
would make `hadj`, `hQ`, `hPpos`, `hPsym` all trivially true. It is blocked, and the block below
is a proved statement rather than a remark: `hT` together with `hTS` FORCES `Q` to hit every
coarse vector. -/

/-- **`hT` + `hTS` force `Q` to hit `B`, with an EXPLICIT preimage** — stated without an existential
so that this module's S91 surface stays empty. This is surjectivity of `Q`, constructively. -/
theorem hyp_forces_Q_hits
    (hT : ∀ B : K, T B = Q (G (Qstar B))) (hTS : ∀ B : K, T (S B) = B) (B : K) :
    Q (G (Qstar (S B))) = B := by
  rw [← hT (S B)]
  exact hTS B

/-- **`Q := 0` is therefore impossible whenever the coarse space is non-trivial.** If some `B ≠ 0`,
then `Q` is non-zero at an explicitly named point. -/
theorem hyp_blocks_zero_Q
    (hT : ∀ B : K, T B = Q (G (Qstar B))) (hTS : ∀ B : K, T (S B) = B)
    (B : K) (hB : B ≠ 0) : Q (G (Qstar (S B))) ≠ 0 := by
  rw [hyp_forces_Q_hits Q Qstar G T S hT hTS B]
  exact hB

/-- **And `T := 0` is impossible for the same reason**, at an explicitly named point. -/
theorem hyp_blocks_zero_T
    (hTS : ∀ B : K, T (S B) = B) (B : K) (hB : B ≠ 0) : T (S B) ≠ 0 := by
  rw [hTS B]
  exact hB

end BareFine

section CampaignCarrier

open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLM inner_deltaKCLM_eq deltaKCLM_symm
  deltaKCLMNormalized inner_deltaKCLMNormalized_eq deltaKCLMNormalized_symm)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.DeltaKFull (deltaKQuadFormCorrected)
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration)

variable {L : PeriodicLatticeExtent}

/-- **The (3.10) coercivity, lifted from the quadratic form to the bundled operator.** Every
element of `BondFnL2 L` is `toLp` of a bond function, so the `∀ A` hypothesis gives the full
`∀ x : BondFnL2 L` conclusion with no loss. -/
theorem deltaKCLM_coercive_of_quadForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (γ : ℝ)
    (h310 : ∀ A : Bond L → SuTwo,
      γ * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 ≤ deltaKQuadFormCorrected U A)
    (x : BondFnL2 L) : γ * ‖x‖ ^ 2 ≤ (inner ℝ x (deltaKCLM U x) : ℝ) := by
  have hx : (WithLp.toLp 2 (WithLp.ofLp x) : BondFnL2 L) = x := rfl
  have h := h310 (WithLp.ofLp x)
  rw [hx] at h
  have heq : (inner ℝ x (deltaKCLM U x) : ℝ) = deltaKQuadFormCorrected U (WithLp.ofLp x) := by
    rw [← inner_deltaKCLM_eq U (WithLp.ofLp x), hx]
  rw [heq]
  exact h

/-! ### §9d — ⚠ THIS IS A CONDITIONAL TRANSPORT LEMMA, NOT A CLOSED BRIDGE

**Grade-3 ruling, 2026-07-28** (three de-correlated prosecutor families). What survived, and what
did not, stated before anything else in this section:

**UPHELD.** The generic implication is proved and is not vacuous. The `a`-cancellation is genuine
algebra with independent provenance on each side (the `+a` of (3.128) survives division by `‖Qx‖`,
which forces its coefficient to be exactly `1`; the `−a` is (3.156)'s definition). The bound is NOT
sharp at the witness (`3/2` actual vs `5/4` bound), which is itself evidence the two sides were not
defined to agree. `hTS` is not the conclusion restated: `T = S = id` satisfies `hTS` while the bound
fails at `γ=2, q=1, B=1`. The normalization half-factor was re-verified at the bilinear, operator
and quadratic-form levels.

**NOT UPHELD — four defects, all fixed below, and the cost of each fix stated.**

1. **`Δ_π ≠ Δ`** (§9e). Cost: the transported constant degrades from `γ/q²` to `(γ−δ)/q²`, with
   `δ` an undischarged bound that CMP99b p.419 explicitly defers.
2. **`src` could be rigged to cancel the conclusion.** With `src B := (1/2)‖B‖²`, `ε := 1/2` the
   old bundle compiled and read `−(1/4)‖B‖² ≤ 0`. Fix: **the headline is now SOURCE-FREE**
   (`bridge_bare`, `bridge_from_fine_operator`) — no free-sign term, no `ε`. The source version is
   demoted to a separate, explicitly-labelled statement and the coercive version carries a
   threshold. Cost: the headline no longer mentions (3.156)'s source term at all; that term is now
   handled only in `..._with_source` / `..._coercive`.
3. **No `ε < γ/q²` hypothesis existed**, so the advertised coefficient could be made nonpositive
   without touching an operator. Fix: `bridge_bare_pos` and `..._coercive` carry `hthr` and
   conclude STRICT positivity. Cost: coercivity now requires a hypothesis that was previously
   silently assumed. The old docstring's "no threshold relating `a` to `γ`" remains TRUE — the
   `a`-cancellation is untouched — but it was misleading by omission, because a DIFFERENT threshold
   (`ε` versus `γ/q²`) is what positivity needs. Both are now stated.
4. **`K := EuclideanSpace ℝ (Fin 0)` passed the whole bundle** (`hTS` holds because every `B` is
   zero; the conclusion is `0 ≤ 0`), and the three anti-degeneracy blockers could not fire because
   their `B ≠ 0` premise was uninhabited — they prove exactly their conditional names and no more.
   Fix: `[Nontrivial K]` on every headline. Cost: none mathematically. **This kills only the
   zero-dimensional case, NOT the rank-one case.**

**AND THE LIMITATION THAT MATTERS MOST.** The `(3.156)` subspace
`{B : B = 0 on Λᶜ, B = 0 on ⋃_{y∈Λ'} Ax(y), Q₁B = 0}` (p.428, adjudicated) is **NOT encoded**: `K`
is an arbitrary inner-product type with nothing tying it to that subspace. **This is declared OUT
OF SCOPE, not overlooked.** The reason is specific: `Q₁`'s defining formula is not located anywhere
in CMP99b pp.421–430 — checked page by page by `CovarianceG1.lean §0c` and again by
`DeltaKRecursive.lean §1`, which carries `Q₁` as an opaque field for exactly this reason. Encoding
the clause faithfully is blocked on a definition the source does not give in this range. A consumer
must supply the restriction themselves.
-/

/-- **`Δ_π = Δ − Δ′_π`**, CMP99b (3.120). -/
noncomputable def piExtendedMap (Delta DeltaPrimePi : BondFnL2 L → BondFnL2 L) :
    BondFnL2 L → BondFnL2 L :=
  fun x => Delta x - DeltaPrimePi x

theorem piExtendedMap_apply (Delta DeltaPrimePi : BondFnL2 L → BondFnL2 L) (x : BondFnL2 L) :
    piExtendedMap Delta DeltaPrimePi x = Delta x - DeltaPrimePi x := rfl

/-- **Coercivity of `Δ_π` from coercivity of `Δ` and a TWO-SIDED bound on the indefinite `Δ′_π`**,
pointwise. The bound must be two-sided precisely because `Δ′_π` is `J`-paired and has no sign; a
one-sided `0 ≤ ⟨x,Δ′_πx⟩` would be the `P`-treatment and would be unjustified. -/
theorem piExtended_coercive_at (Delta DeltaPrimePi : BondFnL2 L → BondFnL2 L) (γ δ : ℝ)
    (x : BondFnL2 L)
    (hDeltaCoercAt : γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ))
    (hpi : |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2) :
    (γ - δ) * ‖x‖ ^ 2 ≤ (inner ℝ x (piExtendedMap Delta DeltaPrimePi x) : ℝ) := by
  rw [piExtendedMap_apply, inner_sub_right]
  have h2 : (inner ℝ x (DeltaPrimePi x) : ℝ) ≤ δ * ‖x‖ ^ 2 := le_trans (le_abs_self _) hpi
  nlinarith [hDeltaCoercAt, h2]

/-- `Δ_π` is symmetric when `Δ` and `Δ′_π` are. -/
theorem piExtended_sym (Delta DeltaPrimePi : BondFnL2 L → BondFnL2 L)
    (hDeltaSym : ∀ u v : BondFnL2 L, (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hPiSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ))
    (u v : BondFnL2 L) :
    (inner ℝ u (piExtendedMap Delta DeltaPrimePi v) : ℝ)
      = (inner ℝ (piExtendedMap Delta DeltaPrimePi u) v : ℝ) := by
  rw [piExtendedMap_apply, piExtendedMap_apply, inner_sub_right, inner_sub_left,
    hDeltaSym u v, hPiSym u v]

/-- **(3.128)'s fine operator, with the (3.10)-level object as a PARAMETER.**
`M = Δ + P + Q*(a·Q)`. Making `Δ` a parameter is what makes the bridge normalization-insensitive. -/
noncomputable def fineMapOf (Delta P : BondFnL2 L → BondFnL2 L) {K : Type*}
    [SeminormedAddCommGroup K] [InnerProductSpace ℝ K] (Q : BondFnL2 L → K)
    (Qstar : K → BondFnL2 L) (a : ℝ) : BondFnL2 L → BondFnL2 L :=
  fun x => Delta x + P x + Qstar (a • Q x)

theorem fineMapOf_apply (Delta P : BondFnL2 L → BondFnL2 L) {K : Type*}
    [SeminormedAddCommGroup K] [InnerProductSpace ℝ K] (Q : BondFnL2 L → K)
    (Qstar : K → BondFnL2 L) (a : ℝ) (x : BondFnL2 L) :
    fineMapOf Delta P Q Qstar a x = Delta x + P x + Qstar (a • Q x) := rfl

/-- The lift from a quadratic FORM to the bundled operator, for ANY form, on a RESTRICTED domain. -/
theorem operator_coercive_of_quadForm_on
    (Delta : BondFnL2 L →L[ℝ] BondFnL2 L) (f : (Bond L → SuTwo) → ℝ) (γ : ℝ)
    (W : BondFnL2 L → Prop)
    (hform : ∀ A : Bond L → SuTwo,
      (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (Delta (WithLp.toLp 2 A)) : ℝ) = f A)
    (hcoerc : ∀ A : Bond L → SuTwo, W (WithLp.toLp 2 A) →
      γ * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 ≤ f A)
    (x : BondFnL2 L) (hx : W x) : γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ) := by
  have hxe : (WithLp.toLp 2 (WithLp.ofLp x) : BondFnL2 L) = x := rfl
  have h := hcoerc (WithLp.ofLp x) (by rw [hxe]; exact hx)
  rw [hxe] at h
  have heq : (inner ℝ x (Delta x) : ℝ) = f (WithLp.ofLp x) := by
    rw [← hform (WithLp.ofLp x), hxe]
  rw [heq]; exact h

/-- The `Q*aQ` shift's diagonal. -/
theorem shift_inner_bare {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]
    (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L) (a : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (x : BondFnL2 L) :
    (inner ℝ x (Qstar (a • Q x)) : ℝ) = a * ‖Q x‖ ^ 2 := by
  rw [real_inner_comm, hadj x (a • Q x), real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The `Q*aQ` shift is symmetric. -/
theorem shift_sym_bare {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]
    (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L) (a : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (u v : BondFnL2 L) :
    (inner ℝ u (Qstar (a • Q v)) : ℝ) = (inner ℝ (Qstar (a • Q u)) v : ℝ) := by
  rw [real_inner_comm (Qstar (a • Q v)) u, hadj u (a • Q v), hadj v (a • Q u),
    real_inner_smul_left, real_inner_smul_left, real_inner_comm (Q u) (Q v)]

/-- (3.128)'s operator is symmetric, given a symmetric `Δ` and a symmetric remainder `P`. -/
theorem fineMapOf_sym {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]
    (Delta P : BondFnL2 L → BondFnL2 L) (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L) (a : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDeltaSym : ∀ u v : BondFnL2 L, (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (u v : BondFnL2 L) :
    (inner ℝ u (fineMapOf Delta P Q Qstar a v) : ℝ)
      = (inner ℝ (fineMapOf Delta P Q Qstar a u) v : ℝ) := by
  rw [fineMapOf_apply, fineMapOf_apply, inner_add_right, inner_add_right, inner_add_left,
    inner_add_left, hPsym u v, shift_sym_bare Q Qstar a hadj u v, hDeltaSym u v]

/-- **(3.128) + a (3.10)-level bound at ONE point.** The `a`-term is KEPT, which is what makes
(3.156)'s `−a⟨B,B⟩` cancel. -/
theorem fineMapOf_coerc_at {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]
    (Delta P : BondFnL2 L → BondFnL2 L) (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L) (a γ : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (x : BondFnL2 L) (hDeltaCoercAt : γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ)) :
    γ * ‖x‖ ^ 2 + a * ‖Q x‖ ^ 2 ≤ (inner ℝ x (fineMapOf Delta P Q Qstar a x) : ℝ) := by
  rw [fineMapOf_apply, inner_add_right, inner_add_right, shift_inner_bare Q Qstar a hadj x]
  have h2 := hPpos x
  linarith

set_option maxHeartbeats 4000000 in
/-- **THE BRIDGE SCHEMA, SOURCE-FREE, DOMAIN-RESTRICTED, ON A NON-TRIVIAL COARSE CARRIER.**

`Delta` is a bound variable, so the conclusion carries no normalization factor. The (3.10)-level
coercivity is demanded **only on `W`**, and only `G ∘ Q*` need land in `W` — this matters because
the campaign's (3.10) coercivity lives on `ker Q₁(U) ∩ axial-gauge`, never on all of `BondFnL2 L`
(`h310_unrestricted_impossible_at_witnessU` below proves the unrestricted form is FALSE at the
tree's own witness background). No `src`, no `ε`: nothing here can be rigged by a source term. -/
theorem bridge_from_fine_operator
    {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K] [Nontrivial K]
    (Delta P : BondFnL2 L → BondFnL2 L) (W : BondFnL2 L → Prop)
    (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L)
    (G : BondFnL2 L → BondFnL2 L) (T S : K →L[ℝ] K) (a γ q : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : K),
      (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDeltaSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (Delta v) : ℝ) = (inner ℝ (Delta u) v : ℝ))
    (hGW : ∀ B : K, W (G (Qstar B)))
    (hDeltaCoercW : ∀ x : BondFnL2 L, W x → γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Delta x) : ℝ))
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hG1 : ∀ x : BondFnL2 L, fineMapOf Delta P Q Qstar a (G x) = x)
    (hTS : ∀ B : K, T (S B) = B)
    (hγ : 0 < γ) (hq : 0 < q) (ha : 0 ≤ a)
    (hQ : ∀ x : BondFnL2 L, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    (γ / q ^ 2) * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 := by
  refine bridge_bare (H := BondFnL2 L) (K := K) Q Qstar (fineMapOf Delta P Q Qstar a) G T S
    a γ q hadj hT ?_ hG1 hTS hγ hq ha ?_ hQ B
  · exact fineMapOf_sym Delta P Q Qstar a hadj hDeltaSym hPsym
  · intro C
    exact fineMapOf_coerc_at Delta P Q Qstar a γ hadj hPpos (G (Qstar C))
      (hDeltaCoercW _ (hGW C))

set_option maxHeartbeats 4000000 in
/-- **THE HEADLINE, SOURCE-FAITHFUL, GENERAL `U`.** (3.10)'s normalized `Δ` ⟹ (3.120)'s `Δ_π` ⟹
(3.128) ⟹ (3.156), SOURCE-FREE:

`((γ − δ)/q²)‖B‖² ≤ ⟨B,SB⟩ − a‖B‖²` .

* `h310W` — coercivity `γ` of `NormalizationAudit.deltaKQuadFormNormalizedCorrected` **on `W`**,
  consumed through `DeltaPrimeOperator.inner_deltaKCLMNormalized_eq`.
* `hpi` — the **TWO-SIDED** bound `|⟨x,Δ′_πx⟩| ≤ δ‖x‖²` on (3.120)'s indefinite correction. **This
  is the bound CMP99b p.419 defers ("Later we will write bounds for this form"). It is NOT proved
  here and it is NOT hidden inside `P`.**

`γ, δ, q, a` are bound before `B`. The `a`-cancellation is untouched. -/
theorem bridge_from_piExtended_normalized_threeTen
    {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K] [Nontrivial K]
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (DeltaPrimePi P : BondFnL2 L → BondFnL2 L) (W : BondFnL2 L → Prop)
    (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L)
    (G : BondFnL2 L → BondFnL2 L) (T S : K →L[ℝ] K) (a γ δ q : ℝ)
    (hadj : ∀ (x : BondFnL2 L) (B : K),
      (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hPiSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ))
    (hpi : ∀ x : BondFnL2 L, |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hGW : ∀ B : K, W (G (Qstar B)))
    (hT : ∀ B : K, T B = Q (G (Qstar B)))
    (hG1 : ∀ x : BondFnL2 L,
      fineMapOf (piExtendedMap (fun y => deltaKCLMNormalized U y) DeltaPrimePi) P Q Qstar a (G x)
        = x)
    (hTS : ∀ B : K, T (S B) = B)
    (hγδ : 0 < γ - δ) (hq : 0 < q) (ha : 0 ≤ a)
    (h310W : ∀ A : Bond L → SuTwo, W (WithLp.toLp 2 A) →
      γ * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 ≤ deltaKQuadFormNormalizedCorrected U A)
    (hQ : ∀ x : BondFnL2 L, ‖Q x‖ ≤ q * ‖x‖) (B : K) :
    ((γ - δ) / q ^ 2) * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 := by
  have hDeltaSym : ∀ u v : BondFnL2 L,
      (inner ℝ u (deltaKCLMNormalized U v) : ℝ)
        = (inner ℝ (deltaKCLMNormalized U u) v : ℝ) :=
    fun u v => (deltaKCLMNormalized_symm U u v).symm
  exact bridge_from_fine_operator
    (piExtendedMap (fun y => deltaKCLMNormalized U y) DeltaPrimePi) P W Q Qstar G T S
    a (γ - δ) q hadj
    (piExtended_sym (fun y => deltaKCLMNormalized U y) DeltaPrimePi hDeltaSym hPiSym)
    hGW
    (fun x hx => piExtended_coercive_at (fun y => deltaKCLMNormalized U y) DeltaPrimePi γ δ x
      (operator_coercive_of_quadForm_on (deltaKCLMNormalized U)
        (deltaKQuadFormNormalizedCorrected U) γ W (inner_deltaKCLMNormalized_eq U) h310W x hx)
      (hpi x))
    hPpos hPsym hT hG1 hTS hγδ hq ha hQ B

/-- **The (3.156) form with its source term — NOT a coercivity statement.** Kept separate and
labelled so that the free-sign `src` can never sit inside the headline. See `..._coercive`. -/
theorem bridge_with_source_of_sourceFree
    {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]
    (S : K →L[ℝ] K) (src : K → ℝ) (c a ε : ℝ) (B : K)
    (hfree : c * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2)
    (hsrc : |src B| ≤ ε * ‖B‖ ^ 2) :
    (c - ε) * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 - src B := by
  have h2 : src B ≤ ε * ‖B‖ ^ 2 := le_trans (le_abs_self _) hsrc
  nlinarith [hfree, h2]

/-- **THE ONLY FORM THAT IS A COERCIVITY STATEMENT**: it carries the threshold `ε < c` the source
must beat and concludes STRICT positivity at `B ≠ 0`. -/
theorem deltaK_form_pos_of_threshold
    {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]
    (S : K →L[ℝ] K) (src : K → ℝ) (c a ε : ℝ) (B : K)
    (hfree : c * ‖B‖ ^ 2 ≤ (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2)
    (hsrc : |src B| ≤ ε * ‖B‖ ^ 2) (hthr : ε < c) (hB : ‖B‖ ≠ 0) :
    0 < (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 - src B := by
  have h := bridge_with_source_of_sourceFree S src c a ε B hfree hsrc
  have hn : 0 < ‖B‖ ^ 2 := by
    have := norm_nonneg B
    positivity
  nlinarith [h, hthr, hn]

/-! ### §9f — WHY THE HEADLINE HAS NO WITNESS, PROVED

The gate asked for a witness at the exact headline bundle or a plain statement that there is none.
**There is none, and here is the proved reason** — two independent obstructions. -/

/-- **`hG1` FORCES the fine operator to be surjective** — explicit preimage, no existential.
Supplying `hG1` MEANS exhibiting a right inverse of `Δ_π + P + Q*aQ` on the real bond carrier, which
is the content CMP99b defers (p.428's `(QG₁Q*)⁻¹`, p.419's promised bounds).

**⚠ MAIN-LOOP CORRECTION 2026-07-28 (S75 in place).** This declaration previously had the conclusion
`fineMapOf Delta P Q Qstar a (G x) = x` — **character-identical to its own hypothesis `hG1 x`**, with
proof term `hG1 x`. It was a TAUTOLOGY carrying a docstring that billed it as "PROVED … Not
bookkeeping — the mathematics". The observation it was making is correct and worth stating, but a
declaration whose statement restates its hypothesis proves nothing about it, and presenting one as
evidence is the [[claim-is-not-certificate]] defect this project prosecutes elsewhere.

Restated so the conclusion is a proposition DISTINCT from the hypothesis: `Function.Surjective`. That
is genuinely weaker than tautological — it asserts something about the map, discharged by exhibiting
`G y` as the preimage. It is still an easy theorem, and that easiness is the honest point: **the work
is in supplying `hG1`, not in deriving anything from it.** -/
theorem fineMapOf_surjective_of_hG1
    {K : Type*} [SeminormedAddCommGroup K] [InnerProductSpace ℝ K]
    (Delta P : BondFnL2 L → BondFnL2 L) (Q : BondFnL2 L → K) (Qstar : K → BondFnL2 L)
    (G : BondFnL2 L → BondFnL2 L) (a : ℝ)
    (hG1 : ∀ x : BondFnL2 L, fineMapOf Delta P Q Qstar a (G x) = x) :
    Function.Surjective (fineMapOf Delta P Q Qstar a) :=
  fun y => ⟨G y, hG1 y⟩

/-- The single-bond witness field is a nonzero vector of `BondFnL2 witnessL`. -/
theorem toLp_deltaWitnessConfig_ne_zero :
    (WithLp.toLp 2 AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig :
      BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL) ≠ 0 := by
  intro hcon
  have h := congrFun (congrArg
    (fun (u : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL) => WithLp.ofLp u) hcon)
    (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3))
  simp only [WithLp.ofLp_toLp] at h
  rw [AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig_at_e0] at h
  exact AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero (by simpa using h)

/-- **THE UNRESTRICTED `(3.10)` COERCIVITY HYPOTHESIS COLLAPSES AT THE TREE'S OWN WITNESS
BACKGROUND.** `deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig = 0`
(`NormalizationAudit`), so an unrestricted `∀ A` coercivity with `γ > 0` FORCES the single-bond
witness field to have zero norm.

Together with `toLp_deltaWitnessConfig_ne_zero` (that vector is NOT zero) this says the hypothesis
is unsatisfiable there. ~~The two halves are stated separately rather than combined into `False`
because the last millimetre — `‖v‖ = 0 → v = 0` — needs `norm_eq_zero`, which resolves the norm
through `NormedAddCommGroup.toNorm` while this statement's norm comes from `PiLp.instNorm`: the same
non-defeq instance diamond §9b documents and measures.~~ **SUPERSEDED 2026-07-31 (grade-2 repair of
`DeltaPrimeBound`): the combination to outright `False` now EXISTS —
`DeltaPrimeBound.bridge_h310W_slot_unsatisfiable_at_witnessU` composes these two halves through the
diamond, and `DeltaPrimeBound.bridge_at_measured_deltaPi_hypotheses_unsatisfiable_at_witnessU`
derives `False` from the wrapper's entire binder list. The halves remain stated separately HERE only
because that composition lives downstream; the millimetre is closed, not open.** That was a Lean
bundling artifact, not a mathematical gap; no further mathematics was missing between these two
theorems and `False`, and now none is unformalized either.

This is why `bridge_from_fine_operator` demands coercivity only on `W`, and it is the first of two
reasons the headline gets no witness: **the one concrete background in the tree cannot supply the
hypothesis.** It does not rule out other intended `U`. -/
theorem h310_unrestricted_forces_zero_norm_at_witnessU (γ : ℝ) (hγ : 0 < γ)
    (h310 : ∀ A : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo,
      γ * ‖(WithLp.toLp 2 A : BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)‖ ^ 2
        ≤ deltaKQuadFormNormalizedCorrected
            AdalyFormal.Balaban.CovariantOperators.witnessU A) :
    ‖(WithLp.toLp 2 AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig :
      BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)‖ = 0 := by
  have h := h310 AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig
  have hz := AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero
  rw [hz] at h
  have hnn := norm_nonneg (WithLp.toLp 2 AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig :
    BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)
  have hsq : ‖(WithLp.toLp 2 AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig :
      BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)‖ ^ 2 ≤ 0 := by
    nlinarith [h, hγ]
  have hle : ‖(WithLp.toLp 2 AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig :
      BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)‖ ≤ 0 := by
    nlinarith [hsq, hnn]
  exact le_antisymm hle hnn

/-- **The two fine objects are genuinely different** — kernel-linked, so §9d's
normalization-insensitivity claim is not a coincidence of equal objects: `0 ≠ −4` at the witness. -/
theorem fine_objects_genuinely_differ :
    AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected
        AdalyFormal.Balaban.CovariantOperators.witnessU
        AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig
      ≠ deltaKQuadFormCorrected AdalyFormal.Balaban.CovariantOperators.witnessU
          AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig :=
  AdalyFormal.Balaban.NormalizationAudit.deltaKQuadFormNormalizedCorrected_ne_deltaKQuadFormCorrected_at_witness

end CampaignCarrier

/-! ## §8 — AXIOM AUDIT: `#print axioms` on every declaration in this module -/

#print axioms psd_cauchy_schwarz
#print axioms inner_inv_ge_of_le
#print axioms coarseComposite
#print axioms coarseComposite_apply
#print axioms IsShiftedBy
#print axioms IsAdjointPair
#print axioms adj_flip
#print axioms shift_inner
#print axioms inner_M_eq
#print axioms coarse_le_of_shifted_bound
#print axioms coarse_le_of_fine_coercive
#print axioms coarse_sym
#print axioms coarse_pos_of_shifted_bound
#print axioms coarse_pos
#print axioms bridge_coercive_prim
#print axioms bridge_coercive
#print axioms bridge_coercive_with_source_prim
#print axioms bridge_coercive_with_source
#print axioms deltaKQuadForm_coercive_of_G1_inverse
#print axioms deltaKQuadForm_coercive_of_fine_coercivity
#print axioms inner_real_real
#print axioms wQ
#print axioms wQstar
#print axioms wQ_apply
#print axioms wQstar_apply
#print axioms wM0
#print axioms wM
#print axioms wG
#print axioms wS
#print axioms wSbad
#print axioms wM_apply
#print axioms wG_apply
#print axioms w_adj
#print axioms w_shifted
#print axioms w_M0_sym
#print axioms w_M_sym
#print axioms w_MG
#print axioms w_GM
#print axioms w_coarse
#print axioms w_TS
#print axioms w_coerc
#print axioms w_Q_bound
#print axioms w_bridge
#print axioms w_Sbad_not_inverse
#print axioms w_values
#print axioms w_bridge_fails_for_Sbad
#print axioms vWit
#print axioms wKer
#print axioms vWit_inner_self
#print axioms wKer_ne_zero
#print axioms wQ_vWit_wKer
#print axioms bridge_at_concrete_carrier
#print axioms coarse_le_bare
#print axioms coarse_pos_bare
#print axioms coarse_sym_bare
#print axioms bridge_bare
#print axioms bridge_bare_src
#print axioms bridge_bare_pos
#print axioms hyp_forces_Q_hits
#print axioms hyp_blocks_zero_Q
#print axioms hyp_blocks_zero_T
#print axioms deltaKCLM_coercive_of_quadForm
#print axioms piExtendedMap
#print axioms piExtendedMap_apply
#print axioms piExtended_coercive_at
#print axioms piExtended_sym
#print axioms fineMapOf
#print axioms fineMapOf_apply
#print axioms operator_coercive_of_quadForm_on
#print axioms shift_inner_bare
#print axioms shift_sym_bare
#print axioms fineMapOf_sym
#print axioms fineMapOf_coerc_at
#print axioms bridge_from_fine_operator
#print axioms bridge_from_piExtended_normalized_threeTen
#print axioms bridge_with_source_of_sourceFree
#print axioms deltaK_form_pos_of_threshold
#print axioms fineMapOf_surjective_of_hG1
#print axioms toLp_deltaWitnessConfig_ne_zero
#print axioms h310_unrestricted_forces_zero_norm_at_witnessU
#print axioms fine_objects_genuinely_differ

end AdalyFormal.Balaban.RecursiveBridge
