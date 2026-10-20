/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.FullReparamC
import AdalyFormal.Balaban.DeltaKFull
import AdalyFormal.Balaban.NormalizationAudit
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-!
# `C*ΔC` AS A GENUINE OPERATOR — `[CSTAR-OPERATOR]`

## §0 — WHAT THIS MODULE IS, AND WHAT IT IS NOT

**IS.** The `C* ∘ M ∘ C` sandwich built as an honest **operator** (a bundled
`LinearMap`/`ContinuousLinearMap`) on the su(2) bond carrier `BondFnL2 L`, with the reparametrization
`C` being CMP99b (3.157)'s `FullReparamC.fullC` **identified by `rfl`** (§2), and with the *form*
identity `⟪B̃, (C*MC) B̃⟫ = ⟪C B̃, M (C B̃)⟫` **proved** (§3) so that the operator and the tree's
existing quadratic-form objects are the same object rather than two unrelated ones. Self-adjointness
and positive semidefiniteness are proved **from explicitly stated hypotheses on `M`** (§3), and then
supplied **unconditionally** at the one `M` this module also builds: `D_U^*D_U` (§4-§5).

**IS NOT.** No COERCIVITY statement (`γ‖B̃‖² ≤ ⟪B̃, T B̃⟫` over a subspace, with `γ > 0`) is made about
this sandwich anywhere in this file. See §7(a): the obvious such target is *proved false* in-tree.
§9 does prove STRICT POSITIVITY AT ONE NAMED POINT (`0 < ⟪B̃₀, T B̃₀⟫` for an explicit `B̃₀`); that is
a non-degeneracy fact, not a coercivity — it quantifies over no subspace and carries no constant.

## §0a — THE WALL THAT WAS NOT A WALL

~~`Balaban/DeltaKFull.lean` §6 is titled "THE WALL" and demonstrates, correctly, that
`ContinuousLinearMap.adjoint` **cannot** be applied to these carriers: its defining section fixes
`[NormedAddCommGroup E] [InnerProductSpace 𝕜 E]` and derives `E`'s topology *internally* from them,
which collides with the ambient `PiLp.topologicalSpace` already baked into a bundled
`BondFnL2 L →L[ℝ] _`. That demonstration is reproduced accurately there and is not disputed here.~~

**⚠ SUPERSEDED (S75, 2026-08-10, `compute/norm_diamond_install/`) — retained because it records
what was true when written, struck because `cannot` is now FALSE.** `ContinuousLinearMap.adjoint`
applies to `BondFnL2 L` with **no instance override at all**. Measured in THIS tree, after the
norm-diamond deletion and after a full 406-module rebuild, as `A2` of
`compute/norm_diamond_install/probe/AdjointProbe.lean`:

    noncomputable def a2_continuous (f : BondFnL2 L →L[ℝ] BondFnL2 L) :
        BondFnL2 L →L[ℝ] BondFnL2 L :=
      ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := BondFnL2 L) (F := BondFnL2 L) f

`logs/adjoint_probe.log` and the independent re-run `logs/adjoint_probe_r2.log` are byte-identical:
`exit=0`, every declaration on `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. The
obstruction the struck paragraph describes was REAL and is GONE: it was contingent on the frozen
`CovariantOperators.instNormedAddCommGroupBondFnL2`, deleted in this same pass, and was never
intrinsic to `ContinuousLinearMap.adjoint` or to `PiLp.topologicalSpace`. This section's own title
was right about a fact its text denied.

`Balaban/DeltaKFull.lean` §6 therefore now needs the same strike; it is outside this lane's write
scope and is reported, not edited (LAW-4).

~~What §6 never tested is the **bare `LinearMap.adjoint`**, whose type mentions no topology at all
(every one of that file's four `LinearMap.adjoint` occurrences is a *substring* of the continuous
one). This module is built on that observation.~~ **AMENDED:** §6 indeed never tested the bare
`LinearMap.adjoint`, and this module is built on it — but that is now a CHOICE, not a necessity.
The continuous form is available on this carrier (`A2` above); nothing below is forced onto the
bare form any more. It is retained for the §1 reasons, unchanged.

~~On `BondFnL2 L` one extra ingredient is needed and is supplied here:~~

~~`letI : NormedAddCommGroup (BondFnL2 L) := PiLp.normedAddCommGroup 2 (fun _ : Bond L => SuTwo)`~~

~~because `CovariantOperators.lean`'s own top-level `instNormedAddCommGroupBondFnL2` (an
`inferInstance` alias, declared as an `instance`) wins synthesis, after which the Mathlib telescope
`[NormedAddCommGroup E] [InnerProductSpace 𝕜 E]` has `E`'s normed group pinned to that constant and
`InnerProductSpace ℝ (BondFnL2 L)` (stated over `PiLp.normedAddCommGroup`) no longer matches.
`compute/coercivity_v_udep/probeB5.lean` carries the CONTROL: the same declaration without the `letI`
still fails, so the instance choice — not the type spelling — is the cause.~~

~~**The `letI` never escapes into a statement.** Every `letI` in this file sits inside a `def` body
or a tactic block. The *types* of all declarations below mention only `→ₗ[ℝ]` / `→L[ℝ]` /
`inner ℝ`, i.e. only instances found by ordinary ambient synthesis.~~

**⚠ SUPERSEDED (S75, 2026-08-09, `compute/norm_diamond_install/`) — the extra ingredient is gone,
and so are all twelve `letI`s that were in this file.**
`CovariantOperators.instNormedAddCommGroupBondFnL2` and
`CovariantOperators.instNormedSpaceBondFnL2` have been **deleted** (measured beforehand: 0 dependents
among 24090 AdalyFormal declarations, positive control 3092). `BondFnL2 L` now gets its
`NormedAddCommGroup` by ordinary search, and that instance IS the one each `letI` used to install —
`PiLp.normedAddCommGroup 2 (fun _ : Bond L => SuTwo)` — pinned by `rfl` in
`compute/norm_diamond/logs/diamond3.log` P3. Deleting a `letI` therefore could not change a
statement or a proof term, and the lane verified that directly: the fully-elaborated (`pp.all`)
types of all 719 declarations the four workaround files add are byte-identical before and after.
The bare-`LinearMap.adjoint` observation above still stands and is still what this module is built
on; it simply no longer needs an instance override.

The sentence that the `letI`s "never escape into a statement" was true and is now moot. §1's
`bondAdjoint_eq_self_iff` remains the device that converts operator-level self-adjointness into
form symmetry, for its own reasons.

## §0b — ~~THE SYSTEMATIC FIX, REPORTED AND NOT PERFORMED (class (i) residual)~~ THE SYSTEMATIC FIX, **PERFORMED**

~~A prior lane measured that demoting `CovariantOperators.lean`'s
`instNormedAddCommGroupBondFnL2` / `instNormedSpaceBondFnL2` from `instance` to `def` (they are
plain `inferInstance` aliases) would unblock **every** Mathlib inner-product API on this carrier at
once, removing the need for the `letI` everywhere. `CovariantOperators.lean` is widely imported and
is **not this lane's write scope**, so this is REPORTED, not done. It belongs in its own lane with a
full-tree sweep.~~

**⚠ SUPERSEDED (S75, 2026-08-09) — done, in that own lane, with that full-tree sweep.** The prior
lane's diagnosis was right and its prescription was one step too timid: the two instances were not
demoted to `def`, they were **removed entirely**, because nothing in the tree used them. See
`compute/norm_diamond/PATCH_SPEC.md` for the audit and `Balaban/SuTwoInner.lean`'s
`bondFnL2_norm_is_the_registered_norm` for the regression pin that fails if anyone re-registers a
`NormedAddCommGroup (BondFnL2 L)` from a different fibre.

## §0c — SOURCE PINS

* `C` — CMP99b (3.157), the almost-local per-bond reparametrization onto `{Q₁B = 0}`, built in
  `Balaban/FullReparamC.lean` as `fullC` / `fullCLM`. §2 identifies this module's `C` with it BY
  `rfl` (`reparamCL2_apply`), so no object drift can enter through the carrier transport.
* `D*D` — CMP99b (3.10)'s first term, `⟨A, D*DA⟩ = ‖D_U A‖²`, whose form is
  `CovariantHj.dstarDQuadForm`. §4 builds the OPERATOR whose quadratic form is exactly that
  (`inner_dstarDLM_eq_dstarDQuadForm`).
-/

namespace AdalyFormal.Balaban.CStarDeltaKCOperator

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant
  suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2 inner_plaqFnL2_eq_covPlaqInner
  plaqFnEquiv plaqFnEquiv_toLp)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2 curlCovariantCLM_L2
  curlCovariantCLM_L2_toLp)
open AdalyFormal.Balaban.FullReparamC (fullC fullCLM IsDropped fullC_free)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast pathSite_apply_self_val
  coarse_coord_add_ell_le)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE ADJOINT ON `BondFnL2 L`

The object `DeltaKFull` §6 concluded was unreachable, reached. ~~Note the `letI` is confined to the
`def` body: `bondAdjoint f`'s TYPE is `BondFnL2 L →ₗ[ℝ] BondFnL2 L`, which mentions only
`AddCommMonoid`/`Module ℝ` — both ambient, and both `rfl`-equal to the shadowed instance's
(`compute/coercivity_v_udep/probeB2.lean` Q1/Q2 measured exactly this defeq).~~

**⚠ SUPERSEDED (S75, 2026-08-09) — there is no `letI` and no shadowed instance any more** (§0a).
`bondAdjoint f`'s TYPE is unchanged, and so is its VALUE: the instance the `letI` installed is the
one ordinary search now returns.
-/

/-- **`f ↦ f*` on the su(2) bond carrier.** The Hilbert-space adjoint, via Mathlib's
finite-dimensional `LinearMap.adjoint`. -/
noncomputable def bondAdjoint (f : BondFnL2 L →ₗ[ℝ] BondFnL2 L) : BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  LinearMap.adjoint (𝕜 := ℝ) (E := BondFnL2 L) (F := BondFnL2 L) f

/-- **The defining Gram identity** `⟪x, f* y⟫ = ⟪f x, y⟫`, against the tree's AMBIENT `inner ℝ`
(which `BondSU2Space.inner_bondFnL2_eq_covBondInner` proves is CMP99b p.391's own `covBondInner`).
This is the one property everything below consumes. -/
theorem inner_bondAdjoint_right (f : BondFnL2 L →ₗ[ℝ] BondFnL2 L) (x y : BondFnL2 L) :
    (inner ℝ x (bondAdjoint f y) : ℝ) = inner ℝ (f x) y := by
  exact LinearMap.adjoint_inner_right (𝕜 := ℝ) (E := BondFnL2 L) (F := BondFnL2 L) f x y

/-- The other side, `⟪f* y, x⟫ = ⟪y, f x⟫`. Derived from `inner_bondAdjoint_right` by real
symmetry of the inner product rather than by a second Mathlib call (the direct call unifies through
a `(deterministic) timeout at isDefEq` — measured, `compute/cstar_operator/probe1.log`). -/
theorem inner_bondAdjoint_left (f : BondFnL2 L →ₗ[ℝ] BondFnL2 L) (x y : BondFnL2 L) :
    (inner ℝ (bondAdjoint f y) x : ℝ) = inner ℝ y (f x) := by
  rw [real_inner_comm x (bondAdjoint f y), inner_bondAdjoint_right, real_inner_comm y (f x)]

/-- **THE HYGIENE DEVICE.** Operator-level self-adjointness of `T` is EQUIVALENT to symmetry of its
form against the ambient `inner ℝ`. Both sides of this `iff` are statements whose types mention only
ambient instances, so every downstream self-adjointness claim in this file can be proved at the form
level and then transported to the operator level with no shadowed instance appearing anywhere. -/
theorem bondAdjoint_eq_self_iff (T : BondFnL2 L →ₗ[ℝ] BondFnL2 L) :
    bondAdjoint T = T ↔ ∀ x y : BondFnL2 L, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y) := by
  rw [show bondAdjoint T
      = LinearMap.adjoint (𝕜 := ℝ) (E := BondFnL2 L) (F := BondFnL2 L) T from rfl, eq_comm]
  exact LinearMap.eq_adjoint_iff (𝕜 := ℝ) (E := BondFnL2 L) (F := BondFnL2 L) T T

/-- `f** = f`. -/
theorem bondAdjoint_bondAdjoint (f : BondFnL2 L →ₗ[ℝ] BondFnL2 L) :
    bondAdjoint (bondAdjoint f) = f := by
  exact LinearMap.adjoint_adjoint (𝕜 := ℝ) (E := BondFnL2 L) (F := BondFnL2 L) f

/-- **The S91 guard on the adjoint itself**: `f* = 0` only when `f = 0`, so no non-vacuity claim
below can be satisfied by the adjoint silently collapsing. -/
theorem bondAdjoint_eq_zero_iff (f : BondFnL2 L →ₗ[ℝ] BondFnL2 L) :
    bondAdjoint f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hb := bondAdjoint_bondAdjoint f
    rw [h] at hb
    rw [← hb]
    exact map_zero (LinearMap.adjoint (𝕜 := ℝ) (E := BondFnL2 L) (F := BondFnL2 L))
  · intro h
    rw [h]
    exact map_zero (LinearMap.adjoint (𝕜 := ℝ) (E := BondFnL2 L) (F := BondFnL2 L))

#print axioms bondAdjoint
#print axioms inner_bondAdjoint_right
#print axioms inner_bondAdjoint_left
#print axioms bondAdjoint_eq_self_iff
#print axioms bondAdjoint_bondAdjoint
#print axioms bondAdjoint_eq_zero_iff

/-! ## §2 — `C` AND `C*` AT THE REAL CMP99b (3.157)

`fullCLM` lives on the bare Pi type `Bond L → SuTwo`, which carries no inner product. It is
transported to `BondFnL2 L` through `WithLp`'s purely algebraic `linearEquiv` (needing only
`Module ℝ`), exactly the technique `BondSU2Space.lean` §3 and `DeltaKFull.lean` §5 already use.
`reparamCL2_apply` proves BY `rfl` that the transported map IS `fullC` — so the identification with
the source object is definitional, not a claim.
-/

/-- **CMP99b (3.157)'s `C`, on the inner-product carrier.** -/
noncomputable def reparamCL2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).symm.toLinearMap ∘ₗ
    (fullCLM U ell Dinv) ∘ₗ (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L).toLinearMap

/-- **THE `rfl` IDENTIFICATION (task item 4).** `reparamCL2` IS `FullReparamC.fullC`, re-typed:
no object drift entered through the transport. -/
theorem reparamCL2_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (A : Bond L → SuTwo) :
    reparamCL2 U ell Dinv (WithLp.toLp 2 A) = WithLp.toLp 2 (fullC U ell Dinv A) := rfl

/-- **`C*` — the object `[SUPPLY-CSTAR-ADJOINT]` named as the blocker (task item 1).** -/
noncomputable def reparamCStar
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  bondAdjoint (reparamCL2 U ell Dinv)

/-- `C*`'s defining property, spelled at the real `C`. -/
theorem inner_reparamCStar
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (x y : BondFnL2 L) :
    (inner ℝ x (reparamCStar U ell Dinv y) : ℝ) = inner ℝ (reparamCL2 U ell Dinv x) y :=
  inner_bondAdjoint_right _ x y

/-- `C ≠ 0` on the L² carrier, inherited from `FullReparamC.fullCLM_ne_zero` (LAW-19: the witness is
reused, not reinvented). -/
theorem reparamCL2_ne_zero {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    reparamCL2 U ell Dinv ≠ 0 := by
  intro h
  refine AdalyFormal.Balaban.FullReparamC.fullCLM_ne_zero hell2 hdvd U Dinv
    (LinearMap.ext fun A => ?_)
  have h1 : (WithLp.toLp 2 (fullC U ell Dinv A) : BondFnL2 L) = 0 := by
    rw [← reparamCL2_apply, h]; rfl
  have h2 : fullC U ell Dinv A = 0 := by
    funext b
    have := congrFun (congrArg (WithLp.ofLp) h1) b
    simpa using this
  rw [AdalyFormal.Balaban.FullReparamC.fullCLM_apply]
  simpa using h2

/-- **`C* ≠ 0`** — the sandwich below is not secretly built out of a collapsed adjoint. -/
theorem reparamCStar_ne_zero {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    reparamCStar U ell Dinv ≠ 0 :=
  fun h => reparamCL2_ne_zero hell2 hdvd U Dinv ((bondAdjoint_eq_zero_iff _).1 h)

#print axioms reparamCL2
#print axioms reparamCL2_apply
#print axioms reparamCStar
#print axioms inner_reparamCStar
#print axioms reparamCL2_ne_zero
#print axioms reparamCStar_ne_zero

/-! ## §3 — THE SANDWICH `C* ∘ M ∘ C`, AS AN OPERATOR

Generic in the middle operator `M`, deliberately: the tree does not yet carry the full (3.156) `Δ_k`
as an operator (§7(b)), so the sandwich is built once and instantiated at whatever `M` exists —
§4-§5 instantiate it at `D_U^*D_U`, unconditionally.

**Every hypothesis on `M` is explicit** (task item 3): nothing about symmetry or positivity of `M`
is assumed in the DEFINITION, and each of the two consequences names its own hypothesis.
-/

/-- **`C* ∘ M ∘ C` as a genuine endomorphism of `BondFnL2 L`** (task item 2). -/
noncomputable def cStarMC
    (C M : BondFnL2 L →ₗ[ℝ] BondFnL2 L) : BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  (bondAdjoint C) ∘ₗ (M ∘ₗ C)

/-- **THE FORM IDENTITY** `⟪x, (C*MC) x⟫ = ⟪C x, M (C x)⟫` — the operator and the quadratic form are
the SAME object, which is the whole point of building the operator at all. Stated for a general pair
`x, y` first; the diagonal is the coercivity-shaped one. -/
theorem inner_cStarMC (C M : BondFnL2 L →ₗ[ℝ] BondFnL2 L) (x y : BondFnL2 L) :
    (inner ℝ x (cStarMC C M y) : ℝ) = inner ℝ (C x) (M (C y)) := by
  show (inner ℝ x (bondAdjoint C (M (C y))) : ℝ) = _
  rw [inner_bondAdjoint_right]

theorem inner_cStarMC_self (C M : BondFnL2 L →ₗ[ℝ] BondFnL2 L) (x : BondFnL2 L) :
    (inner ℝ x (cStarMC C M x) : ℝ) = inner ℝ (C x) (M (C x)) :=
  inner_cStarMC C M x x

/-- **Self-adjointness of the sandwich, at the FORM level**, from symmetry of `M` — hypothesis
`hM` stated explicitly and in ambient `inner ℝ`. -/
theorem inner_cStarMC_symm (C M : BondFnL2 L →ₗ[ℝ] BondFnL2 L)
    (hM : ∀ z w : BondFnL2 L, (inner ℝ (M z) w : ℝ) = inner ℝ z (M w)) (x y : BondFnL2 L) :
    (inner ℝ (cStarMC C M x) y : ℝ) = inner ℝ x (cStarMC C M y) := by
  rw [real_inner_comm y (cStarMC C M x), inner_cStarMC, inner_cStarMC,
    real_inner_comm (M (C x)) (C y)]
  exact hM (C x) (C y)

/-- **Self-adjointness of the sandwich, at the OPERATOR level**: `(C*MC)* = C*MC`, from the same
explicit hypothesis. Transported through §1's `bondAdjoint_eq_self_iff`, so the statement mentions
no shadowed instance. -/
theorem bondAdjoint_cStarMC (C M : BondFnL2 L →ₗ[ℝ] BondFnL2 L)
    (hM : ∀ z w : BondFnL2 L, (inner ℝ (M z) w : ℝ) = inner ℝ z (M w)) :
    bondAdjoint (cStarMC C M) = cStarMC C M :=
  (bondAdjoint_eq_self_iff _).2 (inner_cStarMC_symm C M hM)

/-- **Positive semidefiniteness of the sandwich**, from positive semidefiniteness of `M` —
hypothesis `hM` stated explicitly. No coercivity is claimed: this is `0 ≤ ⟪x, Tx⟫`, nothing more
(§7(a)). -/
theorem inner_cStarMC_nonneg (C M : BondFnL2 L →ₗ[ℝ] BondFnL2 L)
    (hM : ∀ z : BondFnL2 L, (0 : ℝ) ≤ inner ℝ z (M z)) (x : BondFnL2 L) :
    (0 : ℝ) ≤ inner ℝ x (cStarMC C M x) := by
  rw [inner_cStarMC_self]
  exact hM (C x)

/-- **The `CoercivityHypothesis.Δ`-shaped promotion** `H →L[ℝ] H`. Available because the sandwich is
a bare `LinearMap` on a finite-dimensional space; `LinearMap.toContinuousLinearMap` is the ambient
route `BondSU2Space.lean` §1's closure already makes available on this carrier. -/
noncomputable def cStarMCCLM (C M : BondFnL2 L →ₗ[ℝ] BondFnL2 L) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (cStarMC C M)

/-- The form identity survives the CLM promotion. -/
theorem inner_cStarMCCLM (C M : BondFnL2 L →ₗ[ℝ] BondFnL2 L) (x y : BondFnL2 L) :
    (inner ℝ x (cStarMCCLM C M y) : ℝ) = inner ℝ (C x) (M (C y)) :=
  inner_cStarMC C M x y

/-- **OPS-3 EXHIBIT: `inner_cStarMC_nonneg`'s hypothesis is LOAD-BEARING, and its removal makes the
conclusion FALSE — not merely unproved.** At `C = id`, `M = -id` the sandwich's form is `-‖x‖²`,
strictly negative at every `x ≠ 0`. So no hypothesis-free positivity statement about `cStarMC` is
available, and §5's unconditional PSD really does come from §4's proof about `D_U^*D_U`, not from the
sandwich shape.

~~NOTE for anyone extending this file: the proof deliberately routes through `real_inner_self_pos`
and NEVER through `‖·‖`. Going via `real_inner_self_eq_norm_sq` + `norm_pos_iff` FAILS on this
carrier with `0 < @norm _ NormedAddCommGroup.toNormedAddGroup.toNorm x` vs
`0 < @norm _ (PiLp.instNorm 2 fun x => SuTwo) x` (measured, `compute/cstar_operator/mod5.log`) —
the SAME `PiLp` instance diamond, now visible at the NORM rather than at the topology. And
`real_inner_self_pos` needs the §0a `letI` too — it carries the same
`[NormedAddCommGroup F] [InnerProductSpace ℝ F]` telescope that `LinearMap.adjoint` does, and without
the shadow it reports `synthInstanceFailed: InnerProductSpace ℝ (BondFnL2 L)` (measured, `mod6.log`).
The rule for this carrier: any Mathlib lemma whose binder list pairs `NormedAddCommGroup` with
`InnerProductSpace` needs the `letI`; bare `inner`-algebra lemmas (`inner_neg_right`,
`real_inner_comm`, `inner_add_right`, `real_inner_smul_right`) do not.~~

**⚠ SUPERSEDED (S75, 2026-08-09, `compute/norm_diamond_install/`) — this paragraph described the
norm diamond at exactly the place it lived, and that diamond is now GONE.** The two terms it
contrasts, `@norm _ NormedAddCommGroup.toNormedAddGroup.toNorm x` and
`@norm _ (PiLp.instNorm 2 fun x => SuTwo) x`, are now the SAME TERM on this carrier: that is the
content of `Balaban/SuTwoInner.bondFnL2_norm_is_the_registered_norm`, a `rfl` which FAILED while
`CovariantOperators.instNormedAddCommGroupBondFnL2` existed and passes now that it is deleted. The
`letI` rule stated in the last two sentences is therefore void — there is no `letI` left in this
file, and `real_inner_self_pos` resolves its `[NormedAddCommGroup F] [InnerProductSpace ℝ F]`
telescope by ordinary search.

The proof below still routes through `real_inner_self_pos`, unchanged; that is now a stylistic
fact about this file rather than a forced one. -/
theorem inner_cStarMC_neg_of_neg_id (x : BondFnL2 L) (hx : x ≠ 0) :
    (inner ℝ x (cStarMC (LinearMap.id (R := ℝ) (M := BondFnL2 L))
      (-LinearMap.id (R := ℝ) (M := BondFnL2 L)) x) : ℝ) < 0 := by
  rw [inner_cStarMC_self]
  simp only [LinearMap.neg_apply, LinearMap.id_coe, id_eq, inner_neg_right]
  rw [neg_lt_zero]
  exact real_inner_self_pos.mpr hx

#print axioms inner_cStarMC_neg_of_neg_id
#print axioms cStarMC
#print axioms inner_cStarMC
#print axioms inner_cStarMC_self
#print axioms inner_cStarMC_symm
#print axioms bondAdjoint_cStarMC
#print axioms inner_cStarMC_nonneg
#print axioms cStarMCCLM
#print axioms inner_cStarMCCLM

/-! ## §4 — `D_U^*D_U` AS A GENUINE OPERATOR

`DeltaKFull.lean` §7 **Residual 1** asks for `curlCovariantAdjointValue`, an EXPLICIT combinatorial
adjoint of the covariant curl, on the grounds (§6) that no abstract-adjoint route is available. The
abstract route IS available — across the two DIFFERENT carriers `BondFnL2 L` and `PlaqFnL2 L`,
~~with the `letI` needed only on the bond side (`PlaqFnL2` has no shadowing top-level instance;
`CovariantHjMinimizer.lean` §3 deliberately declined to declare one, and this file is the
beneficiary).~~ **⚠ SUPERSEDED (S75, 2026-08-09): with no `letI` needed on either side.** The
asymmetry the struck clause records was real — `PlaqFnL2` never had a shadowing top-level instance
and `BondFnL2` did — and it is now gone from the other direction: `BondFnL2`'s shadowing instance
was deleted rather than `PlaqFnL2` acquiring one. `CovariantHjMinimizer.lean` §3's decision to
decline was, in hindsight, the correct one for both carriers.

**Honest scope of what this closes.** It closes Residual 1's *operator role* — it produces
`D_U^*` and `D_U^*D_U` as bundled maps with the required Gram identity. It does NOT produce
Residual 1's *explicit combinatorial formula* (the four-role reindexing bijection); that remains
unbuilt and is a genuinely different deliverable, wanted only if someone needs the pointwise value
of `D_U^*F` at a bond. Nothing in this module or in `DeltaKFull` §8's assembly needs it.

`curlCovariantLM_L2` itself is REUSED, not rebuilt (LAW-19).
-/

/-- **`D_U^* : PlaqFnL2 L →ₗ[ℝ] BondFnL2 L`** — the covariant curl's adjoint, abstractly. -/
noncomputable def curlAdjoint
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    PlaqFnL2 L →ₗ[ℝ] BondFnL2 L :=
  LinearMap.adjoint (𝕜 := ℝ) (E := BondFnL2 L) (F := PlaqFnL2 L) (curlCovariantLM_L2 U)

/-- `D_U^*`'s defining Gram identity, across the two carriers. -/
theorem inner_curlAdjoint_right
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : BondFnL2 L) (y : PlaqFnL2 L) :
    (inner ℝ x (curlAdjoint U y) : ℝ) = inner ℝ (curlCovariantLM_L2 U x) y := by
  exact LinearMap.adjoint_inner_right (𝕜 := ℝ) (E := BondFnL2 L) (F := PlaqFnL2 L)
    (curlCovariantLM_L2 U) x y

/-- **`D_U^*D_U` — CMP99b (3.10)'s first term, AS AN OPERATOR.**

Carries **no `k` argument**: this operator is RG-scale-CONSTANT, and
`CoercivitySupply.deltaSupply_fails_rg_scale_dependence` proves the negation of any `k`-dependence
conjunct for it. No `k`-dependence is claimed here or anywhere below; the `k`-dependence of the full
`Δ_k(U)` lives in the coarse `Q_k(U)`/`G₁(U)` factor, which this module does not build. -/
noncomputable def dstarDLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  (curlAdjoint U) ∘ₗ (curlCovariantLM_L2 U)

/-- `⟪x, D*D y⟫ = ⟪D x, D y⟫`. -/
theorem inner_dstarDLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x y : BondFnL2 L) :
    (inner ℝ x (dstarDLM U y) : ℝ)
      = inner ℝ (curlCovariantLM_L2 U x) (curlCovariantLM_L2 U y) := by
  show (inner ℝ x (curlAdjoint U (curlCovariantLM_L2 U y)) : ℝ) = _
  rw [inner_curlAdjoint_right]

/-- **THE FAITHFULNESS PIN FOR `dstarDLM`**: its quadratic form IS `CovariantHj.dstarDQuadForm`,
i.e. CMP99b (3.10)'s `⟨A, D*DA⟩`. Without this the operator would be an unrelated object with a
suggestive name. -/
theorem inner_dstarDLM_eq_dstarDQuadForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (dstarDLM U (WithLp.toLp 2 A)) : ℝ)
      = dstarDQuadForm U A := by
  rw [inner_dstarDLM]
  show (inner ℝ (curlCovariantCLM_L2 U (WithLp.toLp 2 A))
    (curlCovariantCLM_L2 U (WithLp.toLp 2 A)) : ℝ) = _
  rw [curlCovariantCLM_L2_toLp, inner_plaqFnL2_eq_covPlaqInner]
  rfl

/-- `D*D` is symmetric — UNCONDITIONALLY (no hypothesis on the background `U`). -/
theorem inner_dstarDLM_symm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x y : BondFnL2 L) :
    (inner ℝ (dstarDLM U x) y : ℝ) = inner ℝ x (dstarDLM U y) := by
  rw [real_inner_comm y (dstarDLM U x), inner_dstarDLM, inner_dstarDLM,
    real_inner_comm (curlCovariantLM_L2 U x) (curlCovariantLM_L2 U y)]

/-- `D*D` is self-adjoint at the OPERATOR level — unconditionally. -/
theorem bondAdjoint_dstarDLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    bondAdjoint (dstarDLM U) = dstarDLM U :=
  (bondAdjoint_eq_self_iff _).2 (inner_dstarDLM_symm U)

/-- `D*D` is positive semidefinite — unconditionally. -/
theorem inner_dstarDLM_nonneg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x : BondFnL2 L) :
    (0 : ℝ) ≤ inner ℝ x (dstarDLM U x) := by
  rw [inner_dstarDLM]
  exact real_inner_self_nonneg

#print axioms curlAdjoint
#print axioms inner_curlAdjoint_right
#print axioms dstarDLM
#print axioms inner_dstarDLM
#print axioms inner_dstarDLM_eq_dstarDQuadForm
#print axioms inner_dstarDLM_symm
#print axioms bondAdjoint_dstarDLM
#print axioms inner_dstarDLM_nonneg

/-! ## §5 — THE INSTANTIATION: `C*(D_U^*D_U)C`, UNCONDITIONALLY SELF-ADJOINT AND PSD

This is the sandwich of §3 at the one middle operator this module builds. Everything is
unconditional: §4 supplies both hypotheses of §3's two consequences with no side conditions.

**This is `C*(D*D)C`, NOT `C*Δ_kC`.** `Δ_k` = `D*D + Δ′`, and `Δ′`'s operator is not built (§7(b)).
`CStarDeltaKCCoercive` §4 `[CSTAR-SCHUR-GAP]` records that the ordering between the leading `D*D`
sandwich and the full (3.156) `Δ_j` runs the UNUSABLE way, so `C*(D*D)C` is not a lower bound for
`C*Δ_kC`; the two are different objects and are named differently here.
-/

/-- **`C*(D_U^*D_U)C` as an operator**, at CMP99b (3.157)'s `C`. -/
noncomputable def cStarDstarDC
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  cStarMC (reparamCL2 U ell Dinv) (dstarDLM U)

/-- **THE HEADLINE FORM IDENTITY**: the operator's quadratic form at `B̃` is CMP99b (3.10)'s
`⟨A, D*DA⟩` evaluated at `A = C B̃`, with `C` the source's own `fullC`. Operator and form agree, and
both are pinned to named source objects. -/
theorem inner_cStarDstarDC_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
        (cStarDstarDC U ell Dinv (WithLp.toLp 2 B)) : ℝ)
      = dstarDQuadForm U (fullC U ell Dinv B) := by
  rw [show cStarDstarDC U ell Dinv = cStarMC (reparamCL2 U ell Dinv) (dstarDLM U) from rfl,
    inner_cStarMC_self, reparamCL2_apply, inner_dstarDLM_eq_dstarDQuadForm]

/-- Self-adjoint, unconditionally. -/
theorem bondAdjoint_cStarDstarDC
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    bondAdjoint (cStarDstarDC U ell Dinv) = cStarDstarDC U ell Dinv :=
  bondAdjoint_cStarMC _ _ (inner_dstarDLM_symm U)

/-- Positive semidefinite, unconditionally. -/
theorem inner_cStarDstarDC_nonneg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (x : BondFnL2 L) :
    (0 : ℝ) ≤ inner ℝ x (cStarDstarDC U ell Dinv x) :=
  inner_cStarMC_nonneg _ _ (inner_dstarDLM_nonneg U) x

/-- The `H →L[ℝ] H` promotion. -/
noncomputable def cStarDstarDCCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  cStarMCCLM (reparamCL2 U ell Dinv) (dstarDLM U)

theorem inner_cStarDstarDCCLM_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
        (cStarDstarDCCLM U ell Dinv (WithLp.toLp 2 B)) : ℝ)
      = dstarDQuadForm U (fullC U ell Dinv B) :=
  inner_cStarDstarDC_eq U ell Dinv B

/-- **WHERE THE SANDWICH DEGENERATES, EXACTLY.** Its form vanishes at `x` iff the reparametrized
field is covariantly curl-free. This is the sharp contrast with the refuted one-level `C*Δ_kC`
encoding (§7(a)), whose form vanishes on a whole nonzero subspace because `C` annihilates the coarse
data the Schur complement is taken over: here the vanishing locus is `C⁻¹(ker D_U)` and nothing
larger. Any lower bound for this operator is therefore EQUIVALENT to a lower bound on
`‖D_U(C B̃)‖²`, which is what the transport lemma immediately below exposes. -/
theorem inner_cStarDstarDC_eq_zero_iff
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (x : BondFnL2 L) :
    (inner ℝ x (cStarDstarDC U ell Dinv x) : ℝ) = 0
      ↔ curlCovariantLM_L2 U (reparamCL2 U ell Dinv x) = 0 := by
  rw [show cStarDstarDC U ell Dinv = cStarMC (reparamCL2 U ell Dinv) (dstarDLM U) from rfl,
    inner_cStarMC_self, inner_dstarDLM]
  exact inner_self_eq_zero (𝕜 := ℝ)

/-- **THE TRANSPORT LEMMA (§9).** Any lower bound on CMP99b (3.10)'s `⟨A, D*DA⟩` at `A = C B̃`
transports verbatim to the OPERATOR's form. `c` is a free real parameter, so a caller may take
`c := γ · bondEnergy B̃` — this is the bridge by which a form-level bound proved elsewhere becomes an
operator-level bound here, with NO import of the proving module required in this direction. -/
theorem inner_cStarDstarDC_ge_of_dstarDQuadForm_ge
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo) (c : ℝ)
    (h : c ≤ dstarDQuadForm U (fullC U ell Dinv B)) :
    c ≤ inner ℝ (WithLp.toLp 2 B : BondFnL2 L) (cStarDstarDC U ell Dinv (WithLp.toLp 2 B)) := by
  rw [inner_cStarDstarDC_eq]
  exact h

/-- And the converse direction, so the transport is an equivalence rather than a one-way weakening. -/
theorem dstarDQuadForm_ge_of_inner_cStarDstarDC_ge
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo) (c : ℝ)
    (h : c ≤ inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
      (cStarDstarDC U ell Dinv (WithLp.toLp 2 B))) :
    c ≤ dstarDQuadForm U (fullC U ell Dinv B) := by
  rw [← inner_cStarDstarDC_eq]
  exact h

#print axioms cStarDstarDC
#print axioms inner_cStarDstarDC_eq
#print axioms bondAdjoint_cStarDstarDC
#print axioms inner_cStarDstarDC_nonneg
#print axioms cStarDstarDCCLM
#print axioms inner_cStarDstarDCCLM_eq
#print axioms inner_cStarDstarDC_eq_zero_iff
#print axioms inner_cStarDstarDC_ge_of_dstarDQuadForm_ge
#print axioms dstarDQuadForm_ge_of_inner_cStarDstarDC_ge

/-! ## §6 — THE SPINE'S OWN (ℝ-VALUED) CARRIER

`Spine.coerc_u_main` pins `cohyp.V` on `AdalyFormal.Balaban.Coercivity.AnchoredBondSpace Lat`
(NOT `…Coercivity.Anchoring.AnchoredBondSpace` — the declaration lives directly in the `Coercivity`
namespace, in `Balaban/Coercivity.lean`; only the `Anchoring` NAMESPACE, which is a different thing,
also lives in that file). Its definition there, verbatim:

    noncomputable abbrev AnchoredBondSpace (Lat : PeriodicLatticeExtent) : Type :=
      EuclideanSpace ℝ (Bond Lat)

so it is definitionally the type written out below. That file is another lane's write scope and is
deliberately NOT imported here;
the type is written out instead, so this section is usable from `Coercivity.lean`'s side by
`abbrev`-unfolding with no import in this direction.

On this carrier **no `letI` is needed at all** — there is no shadowing top-level instance — so the
whole sandwich chain is plain Mathlib. (S75 note, 2026-08-09: as of the norm-diamond repair that is
no longer a distinction — `BondFnL2 L` needs none either, and this file now carries zero `letI`s.
The sentence is retained because it is still TRUE of this carrier and records why this section was
easy when §1 was not.) Kept here because it is the shape
`CoercivityHypothesis.Δ : ℕ → Uconfig → H →L[ℝ] H` actually wants.

**Why there is no transport lemma between §3's carrier and this one, and why none is possible.** These
are not two presentations of one space: `BondFnL2 L` has a THREE-dimensional real fibre per bond
(`SuTwo ≅ 𝔰𝔲(2) ≅ ℝ³`) while `EuclideanSpace ℝ (Bond Lat)` has a ONE-dimensional fibre. They are not
isomorphic (different finite dimensions whenever `Bond` is nonempty), so no `≃ₗ[ℝ]` can exist to
transport a statement along, and this file does not pretend to have one. What transfers is the
CONSTRUCTION, which is why the chain is instantiated twice. `GOAL_LEMMA.md` §3 records the same fact
from the other side: `cohyp.V`'s carrier "has a one-dimensional real fibre per bond and no `Ad`-action
to carry", which is exactly why the `U`-dependent `ker Q₁(U)` clause is not expressible there.
-/

section EuclideanCarrier

variable {Lat : PeriodicLatticeExtent}

/-- `C* ∘ M ∘ C` on the spine's ℝ-valued bond carrier — plain `LinearMap.adjoint`, no workaround. -/
noncomputable def cStarMCEuclid
    (C M : EuclideanSpace ℝ (Bond Lat) →ₗ[ℝ] EuclideanSpace ℝ (Bond Lat)) :
    EuclideanSpace ℝ (Bond Lat) →ₗ[ℝ] EuclideanSpace ℝ (Bond Lat) :=
  (LinearMap.adjoint C) ∘ₗ (M ∘ₗ C)

theorem inner_cStarMCEuclid
    (C M : EuclideanSpace ℝ (Bond Lat) →ₗ[ℝ] EuclideanSpace ℝ (Bond Lat))
    (x y : EuclideanSpace ℝ (Bond Lat)) :
    (inner ℝ x (cStarMCEuclid C M y) : ℝ) = inner ℝ (C x) (M (C y)) := by
  show (inner ℝ x ((LinearMap.adjoint C) (M (C y))) : ℝ) = _
  rw [LinearMap.adjoint_inner_right]

theorem inner_cStarMCEuclid_self
    (C M : EuclideanSpace ℝ (Bond Lat) →ₗ[ℝ] EuclideanSpace ℝ (Bond Lat))
    (x : EuclideanSpace ℝ (Bond Lat)) :
    (inner ℝ x (cStarMCEuclid C M x) : ℝ) = inner ℝ (C x) (M (C x)) :=
  inner_cStarMCEuclid C M x x

/-- Self-adjointness on this carrier, from an explicit symmetry hypothesis on `M`; stated at the
operator level directly, since `LinearMap.IsSymmetric` is available here without shadowing. -/
theorem adjoint_cStarMCEuclid_eq_self
    (C M : EuclideanSpace ℝ (Bond Lat) →ₗ[ℝ] EuclideanSpace ℝ (Bond Lat))
    (hM : M.IsSymmetric) :
    LinearMap.adjoint (cStarMCEuclid C M) = cStarMCEuclid C M := by
  refine LinearMap.IsSymmetric.adjoint_eq ?_
  intro x y
  show (inner ℝ (cStarMCEuclid C M x) y : ℝ) = inner ℝ x (cStarMCEuclid C M y)
  rw [real_inner_comm y (cStarMCEuclid C M x), inner_cStarMCEuclid, inner_cStarMCEuclid,
    real_inner_comm (M (C x)) (C y)]
  exact hM (C x) (C y)

theorem inner_cStarMCEuclid_nonneg
    (C M : EuclideanSpace ℝ (Bond Lat) →ₗ[ℝ] EuclideanSpace ℝ (Bond Lat))
    (hM : ∀ z : EuclideanSpace ℝ (Bond Lat), (0 : ℝ) ≤ inner ℝ z (M z))
    (x : EuclideanSpace ℝ (Bond Lat)) :
    (0 : ℝ) ≤ inner ℝ x (cStarMCEuclid C M x) := by
  rw [inner_cStarMCEuclid_self]
  exact hM (C x)

/-- The `CoercivityHypothesis.Δ` field shape on the spine's carrier. -/
noncomputable def cStarMCEuclidCLM
    (C M : EuclideanSpace ℝ (Bond Lat) →ₗ[ℝ] EuclideanSpace ℝ (Bond Lat)) :
    EuclideanSpace ℝ (Bond Lat) →L[ℝ] EuclideanSpace ℝ (Bond Lat) :=
  LinearMap.toContinuousLinearMap (cStarMCEuclid C M)

theorem inner_cStarMCEuclidCLM
    (C M : EuclideanSpace ℝ (Bond Lat) →ₗ[ℝ] EuclideanSpace ℝ (Bond Lat))
    (x y : EuclideanSpace ℝ (Bond Lat)) :
    (inner ℝ x (cStarMCEuclidCLM C M y) : ℝ) = inner ℝ (C x) (M (C y)) :=
  inner_cStarMCEuclid C M x y

end EuclideanCarrier

#print axioms cStarMCEuclid
#print axioms inner_cStarMCEuclid
#print axioms inner_cStarMCEuclid_self
#print axioms adjoint_cStarMCEuclid_eq_self
#print axioms inner_cStarMCEuclid_nonneg
#print axioms cStarMCEuclidCLM
#print axioms inner_cStarMCEuclidCLM

/-! ## §7 — HONEST LIMITS

### (a) NO COERCIVITY CLAIM IS MADE, AND THE OBVIOUS ONE IS FALSE

`Balaban/CStarDeltaKCCoercive.lean` §5b `cStarDeltaKC_coercivity_refuted` PROVES that no positive
`γ` bounds the encoded `C*Δ_kC` sandwich below by `γ · bondEnergy B̃`: at `B̃ = witA` on `witL5` the
sandwich is `0` while `bondEnergy witA > 0`. The named cause is `[CSTAR-LEVEL-MISMATCH]` — ONE
level-generic map family instantiated at ONE `ell` for BOTH of Bałaban's roles (`Q`, the Schur fibre
of (3.159), and `Q₁`, the (3.157) constraint), so `C` annihilates exactly the coarse data whose
Schur complement `Δ_k` is. `Balaban/CStarLevelCorrected.lean`'s `LevelSplit` carries the corrected
shape: two levels `ell₀ ∣ ell₁` with `ell₀ < ell₁`.

**Consequence for this module**: `cStarDstarDC` takes a SINGLE `ell`, which is the `ell` of `C`'s
constraint (Bałaban's `ell₁`), and `dstarDLM` carries NO level at all — it is the fine covariant
curl energy. So no statement here pairs one `ell` against itself in the refuted way. **What would be
needed for a coercivity statement, and is not available:** (i) a `LevelSplit`, with the Schur fibre
at `ell₀` and `C`'s constraint at `ell₁`; (ii) the `Δ′` operator, so that the middle map is the
actual (3.156) `Δ_k` rather than its leading term; (iii) a resolution of `[CSTAR-SCHUR-GAP]`, since
`CStarDeltaKCCoercive.deltaJQuadFormCovFaithful_le_dstarDQuadForm` orders the leading term ABOVE the
Schur complement, i.e. the wrong way for transferring a lower bound. None of (i)-(iii) is attempted
here, and no `γ‖·‖²`-shaped lower bound is stated. ~~and no lower bound of any kind is stated~~
**AMENDED IN PLACE (S75)**: §9 was added after this paragraph was written and it DOES prove a lower
bound — `0 < ⟪B̃₀, T B̃₀⟫` at one explicit `B̃₀`, for every `2 ≤ ell`, every `U`, every `Dinv`, on every
tiled extent. It is a single-point positivity with no constant and no domain, which is exactly the
fact whose analogue for the refuted one-level `C*Δ_kC` encoding is FALSE (there the form is `0` at a
nonzero field). It is not a coercivity and must not be cited as one.

### (b) `Δ_k` ITSELF IS STILL NOT AN OPERATOR — one named, sized residual

`Δ_k = D*D + Δ′` (`DeltaPrime.deltaQuadFormFaithful`; note the FAITHFUL assembly uses
`deltaPrimeQuadFormTransported`, which `deltaPrimeQuadFormTransported_eq_neg` proves is
`−deltaPrimeQuadForm` — the sign matters and the wrong-sign `deltaQuadForm` must not be used).
§4 delivers the `D*D` half as an operator. The `Δ′` half is `DeltaKFull` §7 **Residual 2**, and it
is a genuinely different kind of job from anything in this file: `deltaPrimeQuadFormTransported` is
a `Finset.sum` over plaquettes of `Re U(∂p)`-weighted terms and a commutator sum, and it is not a
norm-square, so no adjoint gives it. What is needed is its symmetric BILINEAR form, term by term —
a construction `DeltaKFull` §7 sizes as comparable to `DeltaPrime.lean` itself (~1000 lines).

**What this module DOES contribute to that residual**: §8's `bilinToOperatorBond` (below) closes the
*second* half of Residual 2 — the Riesz representation, which §7 of `DeltaKFull` explicitly flagged
as ALSO blocked (*"must ALSO avoid `InnerProductSpace.toDual` (§6)"*). It is not blocked. So Residual
2 is reduced from two obstructions to ONE purely algebraic one: produce the bilinear form; the
promotion to a self-adjoint operator is then a call to `bilinToOperatorBond`.

### (c) NO `k`-DEPENDENCE IS CLAIMED

`dstarDLM` takes no `k` and is RG-scale-constant. `CoercivitySupply.deltaSupply_fails_rg_scale_dependence`
proves the negation of the `k`-dependence conjunct for exactly this object; that theorem is the
guard and this module does not walk into it.

### (d) `DeltaKSuTwoAssembly` IS NOT IMPORTED

Its `deltaJ − a‖B‖²` shape double-subtracts the averaging mass — `G₁⁻¹` (3.128) already carries it,
so the mass cancels and `Δ_k = deltaJ` at zero source. This module's dependency cone does not
include that module, so the sign error cannot enter.

### (e) THE `ell = 1` DEGENERACY IS NOT ADDRESSED HERE

`reparamCL2_ne_zero` / `reparamCStar_ne_zero` require `2 ≤ ell`; at `ell = 1` `AnchoredVFull` proves
the faithful domain collapses to `⊥`. Nothing in this module states a domain, so `ell = 1` is merely
uninformative here rather than wrong — but any consumer that pairs this operator with the faithful
domain must carry `2 ≤ ell`.
-/

/-! ## §8 — A REUSABLE PRIMITIVE: EVERY BILINEAR FORM ON `BondFnL2 L` IS AN OPERATOR

Closes the Riesz half of `DeltaKFull` §7 Residual 2 (§7(b)). `InnerProductSpace.toDual` is reachable
on this carrier ~~under the same one-line shadow~~ **by ordinary instance search (S75, 2026-08-09 —
there is no shadow any more)**, so a bilinear form needs no basis-by-basis construction to become an
operator.

Offered as a general primitive rather than applied, because the object it is wanted for (`Δ′`'s
bilinear form) does not exist yet.
-/

/-- ~~**MEASURED: `InnerProductSpace.toDual` IS STILL BLOCKED HERE, and `DeltaKFull` §6 is right
about it.** The obvious construction~~

~~`(InnerProductSpace.toDual ℝ (BondFnL2 L)).symm (LinearMap.toContinuousLinearMap φ)`~~

~~fails even under the `letI`, with exactly §6's diagnosis, reproduced verbatim from
`compute/cstar_operator/mod1.log`:
`synthesized type class instance is not definitionally equal to expression inferred by typing rules,
synthesized PiLp.topologicalSpace 2 fun x => ↥SuTwo, inferred
PseudoMetricSpace.toUniformSpace.toTopologicalSpace` — because `toDual`'s codomain
`StrongDual ℝ (BondFnL2 L)` is a BUNDLED `→L[ℝ]`, so the topology enters its TYPE, which is the
precise failure mode §6 documents.~~

**⚠ SUPERSEDED (S75, 2026-08-09) — THE STRUCK CLAIM IS NOW FALSE, RE-MEASURED IN THIS TREE.**
The struck paragraph was an accurate measurement of the tree as it stood, and its diagnosis was
right: the topology entered `StrongDual ℝ (BondFnL2 L)`'s TYPE, and `PiLp.topologicalSpace` did not
unify with `PseudoMetricSpace.toUniformSpace.toTopologicalSpace` because the registered
`NormedAddCommGroup (BondFnL2 L)` was `CovariantOperators.instNormedAddCommGroupBondFnL2`, frozen at
the L²-OPERATOR fibre. **That instance is deleted.** Re-measured with no `letI` and no override, in
a Region-B context, by `compute/norm_diamond_install/probe/AdjointProbe.lean`
(`logs/adjoint_probe.log`, exit=0, 0 errors, every declaration on
`[propext, Classical.choice, Quot.sound]`):

* `A3` — `InnerProductSpace.toDual ℝ (BondFnL2 L)` elaborates;
* `A4` — the exact composite struck above,
  `(InnerProductSpace.toDual ℝ (BondFnL2 L)).symm (LinearMap.toContinuousLinearMap φ)`,
  elaborates;
* `A2` — so does `ContinuousLinearMap.adjoint` on this carrier, and `A6`
  `real_inner_self_eq_norm_mul_norm`, both of which this file records elsewhere as impossible here.

**`bondRiesz` below is NOT retracted and is NOT superseded.** It is a sound, `→L[ℝ]`-free
construction that never needed the topology to unify, and everything downstream of it stands. What
has changed is only that it is no longer the *only* available route: the bundled-dual route is now
open too, and a future extension of this file may take either. -/
noncomputable def bondRiesz (φ : BondFnL2 L →ₗ[ℝ] ℝ) : BondFnL2 L :=
  LinearMap.adjoint (𝕜 := ℝ) (E := BondFnL2 L) (F := ℝ) φ (1 : ℝ)

/-- Its defining property `⟪x, riesz φ⟫ = φ x`. -/
theorem inner_bondRiesz_right (φ : BondFnL2 L →ₗ[ℝ] ℝ) (x : BondFnL2 L) :
    (inner ℝ x (bondRiesz φ) : ℝ) = φ x := by
  have h := LinearMap.adjoint_inner_right (𝕜 := ℝ) (E := BondFnL2 L) (F := ℝ) φ x (1 : ℝ)
  rw [show bondRiesz φ
      = LinearMap.adjoint (𝕜 := ℝ) (E := BondFnL2 L) (F := ℝ) φ (1 : ℝ) from rfl, h,
    Real.inner_apply]
  ring

/-- **The promotion.** Any bilinear form `b` on `BondFnL2 L` is the form of an operator: there is a
`T` with `⟪x, T y⟫ = b x y` for all `x, y`. Linearity of `T` is forced by uniqueness of Riesz
vectors, not assumed. -/
noncomputable def bilinToOperatorBond (b : BondFnL2 L →ₗ[ℝ] BondFnL2 L →ₗ[ℝ] ℝ) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L where
  toFun y := bondRiesz (b.flip y)
  map_add' y₁ y₂ := by
    refine ext_inner_left ℝ (fun v => ?_)
    rw [inner_add_right, inner_bondRiesz_right, inner_bondRiesz_right, inner_bondRiesz_right]
    simp
  map_smul' a y := by
    refine ext_inner_left ℝ (fun v => ?_)
    rw [real_inner_smul_right, inner_bondRiesz_right, inner_bondRiesz_right]
    simp

/-- The promotion's defining identity. -/
theorem inner_bilinToOperatorBond (b : BondFnL2 L →ₗ[ℝ] BondFnL2 L →ₗ[ℝ] ℝ)
    (x y : BondFnL2 L) :
    (inner ℝ x (bilinToOperatorBond b y) : ℝ) = b x y := by
  show (inner ℝ x (bondRiesz (b.flip y)) : ℝ) = _
  rw [inner_bondRiesz_right]
  rfl

/-- A SYMMETRIC bilinear form promotes to a SELF-ADJOINT operator — the shape `Δ′` needs. -/
theorem bondAdjoint_bilinToOperatorBond (b : BondFnL2 L →ₗ[ℝ] BondFnL2 L →ₗ[ℝ] ℝ)
    (hb : ∀ x y : BondFnL2 L, b x y = b y x) :
    bondAdjoint (bilinToOperatorBond b) = bilinToOperatorBond b := by
  refine (bondAdjoint_eq_self_iff _).2 (fun x y => ?_)
  rw [real_inner_comm y (bilinToOperatorBond b x), inner_bilinToOperatorBond,
    inner_bilinToOperatorBond, hb]

#print axioms bondRiesz
#print axioms inner_bondRiesz_right
#print axioms bilinToOperatorBond
#print axioms inner_bilinToOperatorBond
#print axioms bondAdjoint_bilinToOperatorBond


/-! ## §9 — NON-DEGENERACY AT A NAMED WITNESS, AND THE CONTRAST WITH THE REFUTED ONE-LEVEL TARGET

The refutation `CStarDeltaKCCoercive.cStarDeltaKC_coercivity_refuted` works by exhibiting a NONZERO
`B̃` at which the one-level `C*Δ_kC` form is **exactly `0`**. This section proves the corresponding
statement for THIS module's object is the opposite: at a named, explicit `B̃₀` the form is **strictly
positive**, for every `2 ≤ ell`, every background `U`, every `Dinv`, on every tiled extent — no
witness lattice, no numerics.

The mechanism is that all four bonds of the origin plaquette in the `(0,1)` plane are FREE for
`2 ≤ ell` (i.e. `¬ IsDropped`), so `C` acts as the identity on exactly the data the covariant curl at
that plaquette reads. `W1`-`W5` below are the chain; `W2`'s two facts are one-line copies of
`U1Anchor.periodicLatticeShift_apply_ne` and `RegularUCurvedWitness.shift_ne_self` (reproduced rather
than imported, to keep this module's import cone at `FullReparamC` + `DeltaKFull`; the originals are
the primary statements and are cited here, LAW-19).

**This is NOT a coercivity.** It is positivity at one point: no subspace is quantified over and no
constant is produced. §7(a) still stands in full.
-/

/-! ### W1 — a general `¬ IsDropped` criterion -/

/-- **A bond is FREE as soon as its base site's OWN-DIRECTION coordinate is `≡ 0 (mod ell)`.**
This generalizes `FullReparamC.coarseBond_base_not_dropped` (which requires the base to be a full
coarse site, i.e. ALL three coordinates `≡ 0`): only the bond's own direction matters, because a
dropped bond sits at own-direction offset `ell - 1` from its coarse site. The generalization is what
lets the two "far" bonds of a plaquette — based at `x + e_μ`, not at a coarse site — be shown free. -/
theorem bond_not_dropped_of_own_coord {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (x : PeriodicLatticeSite L) (τ : Fin 3) (hx : (x τ).val % ell = 0) :
    ¬ IsDropped ell ((x, τ) : Bond L) := by
  rintro ⟨c, hc⟩
  simp only [droppedBondLast, Prod.mk.injEq] at hc
  obtain ⟨hsite, hdir⟩ := hc
  have hfit : (c.1.1 c.2).val + ell ≤ L c.2 + 1 :=
    coarse_coord_add_ell_le hdvd c.2 _ (mem_CoarseLattice.mp c.1.2 c.2) (c.1.1 c.2).isLt
  have hval : (x c.2).val = ((c.1.1 c.2).val + (ell - 1)) % (L c.2 + 1) := by
    have h1 := congrArg (fun z : PeriodicLatticeSite L => (z c.2).val) hsite
    rwa [pathSite_apply_self_val] at h1
  rw [Nat.mod_eq_of_lt (show (c.1.1 c.2).val + (ell - 1) < L c.2 + 1 by omega)] at hval
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 c.2)
  have hx0 : (x c.2).val % ell = 0 := by rw [← hdir]; exact hx
  rw [hval, hk, Nat.mul_add_mod, Nat.mod_eq_of_lt (show ell - 1 < ell by omega)] at hx0
  omega

/-! ### W2 — two shift facts (copies of the primary statements, cited above) -/

theorem shiftApplyNe (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    periodicLatticeShift x μ ν = x ν :=
  Function.update_of_ne h _ _

theorem shiftNeSelf (x : PeriodicLatticeSite L) (ν : Fin 3) (h : 0 < L ν) :
    periodicLatticeShift x ν ≠ x := by
  intro hcon
  have hv := congrFun hcon ν
  rw [periodicLatticeShift, Function.update_self] at hv
  have hval := congrArg Fin.val hv
  rw [Fin.val_add_one] at hval
  split at hval
  · rename_i hlast
    rw [hlast] at hval
    simp [Fin.last] at hval
    omega
  · omega

/-! ### W3 — the origin plaquette, and its four FREE bonds -/

/-- The origin site. -/
def witOriginSite : PeriodicLatticeSite L := fun _ => 0

/-- The origin plaquette in the `(0,1)` coordinate plane. -/
def witOriginPlaq : PeriodicLatticePlaquette L :=
  ((witOriginSite : PeriodicLatticeSite L), ⟨(0, 1), by decide⟩)

theorem witOriginPlaq_base : (witOriginPlaq (L := L)).1 = witOriginSite := rfl
theorem witOriginPlaq_dir1 : (witOriginPlaq (L := L)).2.1.1 = 0 := rfl
theorem witOriginPlaq_dir2 : (witOriginPlaq (L := L)).2.1.2 = 1 := rfl

theorem witOriginSite_coord (τ : Fin 3) :
    ((witOriginSite : PeriodicLatticeSite L) τ).val = 0 := rfl

/-- `0 < L ν` follows from tileability plus `2 ≤ ell` — needed because `shiftNeSelf` is FALSE at a
degenerate extent (`RegularUCurvedWitness.shift_ne_self_fails_at_zero_extent` proves the failure). -/
theorem witExtentPos {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (ν : Fin 3) : 0 < L ν := by
  obtain ⟨k, hk⟩ := hdvd ν
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0, Nat.mul_zero] at hk; omega
  · have : ell ≤ L ν + 1 := by
      calc ell = ell * 1 := by ring
        _ ≤ ell * k := Nat.mul_le_mul_left ell hk0
        _ = L ν + 1 := hk.symm
    omega

theorem witBond1Free {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ¬ IsDropped ell (((witOriginSite : PeriodicLatticeSite L), (0 : Fin 3)) : Bond L) :=
  bond_not_dropped_of_own_coord hell2 hdvd _ _
    (by rw [witOriginSite_coord]; exact Nat.zero_mod ell)

theorem witBond4Free {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ¬ IsDropped ell (((witOriginSite : PeriodicLatticeSite L), (1 : Fin 3)) : Bond L) :=
  bond_not_dropped_of_own_coord hell2 hdvd _ _
    (by rw [witOriginSite_coord]; exact Nat.zero_mod ell)

theorem witBond2Free {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ¬ IsDropped ell ((periodicLatticeShift (witOriginSite : PeriodicLatticeSite L) 0,
      (1 : Fin 3)) : Bond L) := by
  refine bond_not_dropped_of_own_coord hell2 hdvd _ _ ?_
  rw [shiftApplyNe _ 0 1 (by decide), witOriginSite_coord]
  exact Nat.zero_mod ell

theorem witBond3Free {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ¬ IsDropped ell ((periodicLatticeShift (witOriginSite : PeriodicLatticeSite L) 1,
      (0 : Fin 3)) : Bond L) := by
  refine bond_not_dropped_of_own_coord hell2 hdvd _ _ ?_
  rw [shiftApplyNe _ 1 0 (by decide), witOriginSite_coord]
  exact Nat.zero_mod ell

/-! ### W4 — the covariant curl at a plaquette reads exactly four bonds -/

/-- **`A`-LOCALITY of `curlValueCovariant`** — the complement of
`CovariantHj.curlValueCovariant_congr_of_agree_off_dir0` (which varies `U`, not `A`). -/
theorem curlValueCovariant_congr_on_plaq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A B : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (h1 : A (p.1, p.2.1.1) = B (p.1, p.2.1.1))
    (h2 : A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      = B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
    (h3 : A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)
      = B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
    (h4 : A (p.1, p.2.1.2) = B (p.1, p.2.1.2)) :
    curlValueCovariant U A p = curlValueCovariant U B p := by
  unfold curlValueCovariant
  rw [h1, h2, h3, h4]

/-! ### W5 — the witness, its curl, and the strict positivity -/

/-- **The witness field `B̃₀`**: a single `suTwoWitness` spike at the origin plaquette's first bond. -/
noncomputable def witField : Bond L → SuTwo :=
  Pi.single ((witOriginSite : PeriodicLatticeSite L), (0 : Fin 3)) suTwoWitness

/-- The covariant curl of the BARE witness at the origin plaquette is EXACTLY `suTwoWitness` — the
three other terms vanish because the spike sits at none of the other three bonds. -/
theorem curl_witField_witOriginPlaq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    curlValueCovariant U (witField (L := L)) (witOriginPlaq (L := L)) = suTwoWitness := by
  have hLpos : (0 : ℕ) < L 1 := witExtentPos hell2 hdvd 1
  have hne3 : (periodicLatticeShift (witOriginSite : PeriodicLatticeSite L) 1, (0 : Fin 3))
      ≠ ((witOriginSite : PeriodicLatticeSite L), (0 : Fin 3)) := by
    intro hcon
    exact shiftNeSelf (witOriginSite : PeriodicLatticeSite L) 1 hLpos (congrArg Prod.fst hcon)
  have hdir10 : ¬ ((1 : Fin 3) = (0 : Fin 3)) := by decide
  have hne2 : (periodicLatticeShift (witOriginSite : PeriodicLatticeSite L) 0, (1 : Fin 3))
      ≠ ((witOriginSite : PeriodicLatticeSite L), (0 : Fin 3)) := by
    intro hcon
    exact hdir10 ((Prod.mk.injEq _ _ _ _).mp hcon).2
  have hne4 : ((witOriginSite : PeriodicLatticeSite L), (1 : Fin 3))
      ≠ ((witOriginSite : PeriodicLatticeSite L), (0 : Fin 3)) := by
    intro hcon
    exact hdir10 ((Prod.mk.injEq _ _ _ _).mp hcon).2
  show witField ((witOriginPlaq (L := L)).1, (witOriginPlaq (L := L)).2.1.1)
      + RMap (U ((witOriginPlaq (L := L)).1, (witOriginPlaq (L := L)).2.1.1))
          (witField (periodicLatticeShift (witOriginPlaq (L := L)).1
            (witOriginPlaq (L := L)).2.1.1, (witOriginPlaq (L := L)).2.1.2))
      - RMap (U ((witOriginPlaq (L := L)).1, (witOriginPlaq (L := L)).2.1.2))
          (witField (periodicLatticeShift (witOriginPlaq (L := L)).1
            (witOriginPlaq (L := L)).2.1.2, (witOriginPlaq (L := L)).2.1.1))
      - witField ((witOriginPlaq (L := L)).1, (witOriginPlaq (L := L)).2.1.2) = suTwoWitness
  rw [witOriginPlaq_base, witOriginPlaq_dir1, witOriginPlaq_dir2]
  unfold witField
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne2, Pi.single_eq_of_ne hne3,
    Pi.single_eq_of_ne hne4, map_zero, map_zero]
  abel

/-- **`C` DOES NOT MOVE THE ORIGIN PLAQUETTE**: all four bonds it reads are free, so the curl of
`C B̃₀` there equals the curl of `B̃₀` there. -/
theorem curl_fullC_witField_witOriginPlaq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    curlValueCovariant U (fullC U ell Dinv (witField (L := L))) (witOriginPlaq (L := L))
      = suTwoWitness := by
  rw [curlValueCovariant_congr_on_plaq U _ (witField (L := L)) (witOriginPlaq (L := L))
    (by rw [witOriginPlaq_base, witOriginPlaq_dir1]
        exact fullC_free U Dinv _ (witBond1Free hell2 hdvd))
    (by rw [witOriginPlaq_base, witOriginPlaq_dir1, witOriginPlaq_dir2]
        exact fullC_free U Dinv _ (witBond2Free hell2 hdvd))
    (by rw [witOriginPlaq_base, witOriginPlaq_dir1, witOriginPlaq_dir2]
        exact fullC_free U Dinv _ (witBond3Free hell2 hdvd))
    (by rw [witOriginPlaq_base, witOriginPlaq_dir2]
        exact fullC_free U Dinv _ (witBond4Free hell2 hdvd))]
  exact curl_witField_witOriginPlaq U hell2 hdvd

theorem curl_fullC_witField_ne_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    curlValueCovariant U (fullC U ell Dinv (witField (L := L))) ≠ 0 := by
  intro hcon
  have h := congrFun hcon (witOriginPlaq (L := L))
  rw [curl_fullC_witField_witOriginPlaq U hell2 hdvd Dinv] at h
  exact suTwoWitness_ne_zero h

/-- The unbundled curl, applied at a transported bare field. Same content as
`DeltaKFull.curlCovariantCLM_L2_toLp`, restated for the `LinearMap` (the bundled application is
`rfl`-equal to the unbundled one). -/
theorem curlCovariantLM_L2_toLp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    curlCovariantLM_L2 U (WithLp.toLp 2 A) = WithLp.toLp 2 (curlValueCovariant U A) :=
  curlCovariantCLM_L2_toLp U A

theorem plaqToLp_eq_zero_iff (F : PeriodicLatticePlaquette L → SuTwo) :
    (WithLp.toLp 2 F : PlaqFnL2 L) = 0 ↔ F = 0 := by
  constructor
  · intro h
    have h2 := congrArg (plaqFnEquiv L) h
    rw [plaqFnEquiv_toLp, map_zero] at h2
    exact h2
  · intro h
    rw [h]
    exact map_zero (plaqFnEquiv L).symm

/-- **THE NON-DEGENERACY THEOREM.** `0 < ⟪B̃₀, C*(D_U^*D_U)C B̃₀⟫` at the named `B̃₀ = witField`, for
EVERY `2 ≤ ell`, EVERY background `U`, EVERY `Dinv`, on EVERY tiled extent. No existential quantifier
appears (S91: the witness is a named `def`, not chosen by the prover), no witness lattice is used, and
the constant `2 ≤ ell` is the only arithmetic hypothesis.

Contrast, verbatim from `CStarDeltaKCCoercive` §5b: for the ONE-LEVEL `C*Δ_kC` encoding the form is
`0` at a field with `bondEnergy > 0`. Same `C`, same lattice family, opposite verdict — because the
middle operator here is the FINE covariant curl energy, which `C` does not annihilate, rather than
the Schur complement over the very fibre `C` kills. -/
theorem inner_cStarDstarDC_witField_pos
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    (0 : ℝ) < inner ℝ (WithLp.toLp 2 (witField (L := L)) : BondFnL2 L)
      (cStarDstarDC U ell Dinv (WithLp.toLp 2 (witField (L := L)))) := by
  have hnz : ¬ ((inner ℝ (WithLp.toLp 2 (witField (L := L)) : BondFnL2 L)
      (cStarDstarDC U ell Dinv (WithLp.toLp 2 (witField (L := L)))) : ℝ) = 0) := by
    rw [inner_cStarDstarDC_eq_zero_iff, reparamCL2_apply, curlCovariantLM_L2_toLp,
      plaqToLp_eq_zero_iff]
    exact curl_fullC_witField_ne_zero U hell2 hdvd Dinv
  exact lt_of_le_of_ne (inner_cStarDstarDC_nonneg U ell Dinv _) (Ne.symm hnz)

/-- **THE SAME FACT IN THE LEVEL-CORRECTED SHAPE.** `CStarLevelCorrected.LevelSplit` carries
`fibre_pos : 0 < ell₀`, `refines : ell₀ ∣ ell₁` and `proper : ell₀ < ell₁`; the reparametrization `C`
lives at `ell₁ = S.constr`. This corollary takes the two fields that are actually needed
(`fibre_pos`, `proper`) and DERIVES `2 ≤ ell₁` from them, so a caller holding a `LevelSplit S` applies
it as `… S.fibre_pos S.proper hdvd U Dinv`.

`refines` is deliberately NOT taken: the divisibility between the two levels plays no role in this
particular conclusion, and taking it would be a dead hypothesis. What `LevelSplit` buys here is the
*separation* `ell₀ < ell₁`, which is exactly what forces `2 ≤ ell₁` and hence the free origin
plaquette. `CStarLevelCorrected` is NOT imported (its cone contains `DeltaKSuTwoAssembly`, whose mass
sign is defective) — the hypotheses are spelled out instead, so the dependency runs the other way. -/
theorem inner_cStarDstarDC_witField_pos_at_levelSplit
    {ell₀ ell₁ : ℕ} (hfibre_pos : 0 < ell₀) (hproper : ell₀ < ell₁)
    (hdvd : ∀ μ : Fin 3, ell₁ ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell₁ → (SuTwo →ₗ[ℝ] SuTwo)) :
    (0 : ℝ) < inner ℝ (WithLp.toLp 2 (witField (L := L)) : BondFnL2 L)
      (cStarDstarDC U ell₁ Dinv (WithLp.toLp 2 (witField (L := L)))) :=
  inner_cStarDstarDC_witField_pos U (by omega) hdvd Dinv

/-- And the operator is therefore not the zero map.

**[S75 note, 2026-07-28 — NOT affected by the trace-normalization repair, recorded so a future
grep-follower does not re-open it.]** `compute/norm_propagation/AUDIT.md` listed this in bucket (B)
as a caution entry after a grep hit. Direct reading confirms its own statement is about
`cStarDstarDC` — the `D*D` sandwich ALONE — which the normalization bug never touched:
`dstarDQuadForm` was always correctly normalized via `SuTwoInner.hsInner`. Correct bucket: (D). -/
theorem cStarDstarDC_ne_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) :
    cStarDstarDC U ell Dinv ≠ 0 := by
  intro h
  have hpos := inner_cStarDstarDC_witField_pos U hell2 hdvd Dinv
  rw [h] at hpos
  simp at hpos

#print axioms bond_not_dropped_of_own_coord
#print axioms shiftApplyNe
#print axioms shiftNeSelf
#print axioms witOriginSite
#print axioms witOriginPlaq
#print axioms witOriginPlaq_base
#print axioms witOriginPlaq_dir1
#print axioms witOriginPlaq_dir2
#print axioms witOriginSite_coord
#print axioms witExtentPos
#print axioms witBond1Free
#print axioms witBond2Free
#print axioms witBond3Free
#print axioms witBond4Free
#print axioms curlValueCovariant_congr_on_plaq
#print axioms witField
#print axioms curl_witField_witOriginPlaq
#print axioms curl_fullC_witField_witOriginPlaq
#print axioms curl_fullC_witField_ne_zero
#print axioms curlCovariantLM_L2_toLp
#print axioms plaqToLp_eq_zero_iff
#print axioms inner_cStarDstarDC_witField_pos
#print axioms inner_cStarDstarDC_witField_pos_at_levelSplit
#print axioms cStarDstarDC_ne_zero


/-! ## §10 — `C*Δ_kC` ITSELF, WITH THE `Δ′` HALF AS A TYPED INTERFACE

§5 built the sandwich at the LEADING term `D_U^*D_U`. This section goes to `Δ_k` itself.

`DeltaKFull.lean` §8 already proves the assembly logic: given `T1 T2 : BondFnL2 L →L[ℝ] BondFnL2 L`
whose quadratic forms reproduce `dstarDQuadForm` and `DeltaPrime.deltaPrimeQuadFormTransported`, the
form of `T1 + T2` is `DeltaKFull.deltaKQuadFormCorrected` — the FAITHFUL (3.10) assembly (the
TRANSPORTED `Δ′`, i.e. the sign `DeltaPrime.deltaPrimeQuadFormTransported_eq_neg` pins; the
wrong-sign `deltaQuadForm` is not used anywhere in this module).

`DeltaKFull` §9 lists TWO residuals blocking that assembly. **§4 of this file discharges the first
one's role**: `dstarDCLM` below inhabits the `T1` slot, PROVED, not asserted —
`deltaKFull_T1_discharged` is a call to `DeltaKFull.deltaKFullCLM_assembly_sound` with `T1` supplied.
So the `Δ_k` operator is blocked by exactly ONE remaining input, and that input is now a TYPED
INTERFACE (`T2` + `hT2`) rather than a prose residual.
-/

/-- `D_U^*D_U` in the bundled `H →L[ℝ] H` shape `DeltaKFull` §8 asks for. -/
noncomputable def dstarDCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (dstarDLM U)

theorem inner_dstarDCLM_eq_dstarDQuadForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (dstarDCLM U (WithLp.toLp 2 A)) : ℝ)
      = dstarDQuadForm U A :=
  inner_dstarDLM_eq_dstarDQuadForm U A

/-- **`DeltaKFull` §9 RESIDUAL 1's SLOT IS FILLED.** The assembly theorem
`DeltaKFull.deltaKFullCLM_assembly_sound` is invoked here with `T1 := dstarDCLM U`, discharged by
§4's Gram identity. Only `T2` (the `Δ′` operator) is still a hypothesis.

**⚠ [SUPERSEDED AS A CITATION OF CMP99b (3.10), 2026-07-28, S75 — statement RETAINED, struck only
as a citation. TRUE of the object it names.]** `hT2` fixes `T2`'s form to the RAW
`DeltaPrime.deltaPrimeQuadFormTransported`, and `DeltaKFull.deltaKQuadFormCorrected` mixes trace
normalizations: `dstarDQuadForm` carries Bałaban's `tr 1 = 1` through `SuTwoInner.hsInner =
-(1/2)·Re Tr`, while `DeltaPrime`'s terms use raw `Matrix.trace`. CMP99b p.392 states *"the trace is
normalized, i.e. tr 1 = 1"* immediately before (3.10) and uses that same `tr` in BOTH legs, so this
tree's `Δ′` summand is EXACTLY TWICE the source's. **FAITHFUL TWIN: `§10b.
deltaKFull_T1_discharged_normalized`**, whose `hT2` names `deltaPrimeQuadFormNormalizedTransported`
and whose conclusion is `NormalizationAudit.deltaKQuadFormNormalizedCorrected`.
(This file's generic machinery was UNFLAGGED while the identical logic instantiated downstream in
`DeltaPrimeOperator.lean` was struck — a cross-document desync, closed here.) -/
theorem deltaKFull_T1_discharged
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hT2 : ∀ A : Bond L → SuTwo, (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
      (T2 (WithLp.toLp 2 A)) : ℝ)
      = AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadFormTransported U A)
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) ((dstarDCLM U + T2) (WithLp.toLp 2 A)) : ℝ)
      = AdalyFormal.Balaban.DeltaKFull.deltaKQuadFormCorrected U A :=
  AdalyFormal.Balaban.DeltaKFull.deltaKFullCLM_assembly_sound U (dstarDCLM U) T2
    (inner_dstarDCLM_eq_dstarDQuadForm U) hT2 A

/-- **`C* ∘ Δ_k ∘ C` AS A GENUINE OPERATOR.** `Δ_k` is `dstarDCLM U + T2` with `T2` the `Δ′` operator
(`DeltaKFull` §9 Residual 2 — the ONE remaining input, see §11). This is not a weakening of the
sandwich: `C` is the real (3.157) `C` and the middle map is ~~the real (3.10) assembly the moment
`T2` is supplied~~.

**[S75, 2026-07-28 — the struck clause was FALSE AS PROSE, and this `def` is the one place it
mattered most, being the object everything downstream sandwiches.]** `cStarDeltaKC` is
NORMALIZATION-NEUTRAL: it is `dstarDCLM U + T2` for whatever `T2` a caller supplies, so it becomes
the source's (3.10) assembly only when `T2` is the SOURCE-normalized `Δ′` — supplying the raw one
gives an operator whose `Δ′` leg is twice the source's. The corrected clause: *the middle map is the
real (3.10) assembly the moment the SOURCE-NORMALIZED `T2` is supplied* (`§10b.
inner_cStarDeltaKC_normalized_eq`; the concrete supply is
`DeltaPrimeOperator.deltaPrimeCLMNormalized`). -/
noncomputable def cStarDeltaKC
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  cStarMC (reparamCL2 U ell Dinv) ((dstarDCLM U + T2).toLinearMap)

/-- **THE TASK'S FORM IDENTITY AT THE FULL `Δ_k`**:
`⟪B̃, (C*Δ_kC) B̃⟫ = Δ_k-form evaluated at C B̃`, with `C B̃ = fullC U ell Dinv B̃` (§2's `rfl`
identification) and the `Δ_k` form being `DeltaKFull.deltaKQuadFormCorrected`.

**[SUPERSEDED AS A CITATION, 2026-07-28, S75 — retained struck; TRUE of the raw object it names.]**
`deltaKQuadFormCorrected` is NOT CMP99b's (3.10) (trace-normalization mix, see
`deltaKFull_T1_discharged`'s banner). FAITHFUL TWIN: `§10b.inner_cStarDeltaKC_normalized_eq`. -/
theorem inner_cStarDeltaKC_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hT2 : ∀ A : Bond L → SuTwo, (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
      (T2 (WithLp.toLp 2 A)) : ℝ)
      = AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadFormTransported U A)
    (B : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
        (cStarDeltaKC U ell Dinv T2 (WithLp.toLp 2 B)) : ℝ)
      = AdalyFormal.Balaban.DeltaKFull.deltaKQuadFormCorrected U (fullC U ell Dinv B) := by
  show (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
      (cStarMC (reparamCL2 U ell Dinv) ((dstarDCLM U + T2).toLinearMap)
        (WithLp.toLp 2 B)) : ℝ) = _
  rw [inner_cStarMC_self, reparamCL2_apply]
  exact deltaKFull_T1_discharged U T2 hT2 (fullC U ell Dinv B)

/-- Self-adjointness of `C*Δ_kC` GIVEN symmetry of `Δ_k` — hypothesis explicit (task item 3). -/
theorem bondAdjoint_cStarDeltaKC
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hsym : ∀ z w : BondFnL2 L,
      (inner ℝ ((dstarDCLM U + T2) z) w : ℝ) = inner ℝ z ((dstarDCLM U + T2) w)) :
    bondAdjoint (cStarDeltaKC U ell Dinv T2) = cStarDeltaKC U ell Dinv T2 :=
  bondAdjoint_cStarMC (reparamCL2 U ell Dinv) ((dstarDCLM U + T2).toLinearMap) hsym

/-- Positive semidefiniteness of `C*Δ_kC` GIVEN that of `Δ_k` — hypothesis explicit. -/
theorem inner_cStarDeltaKC_nonneg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hpos : ∀ z : BondFnL2 L, (0 : ℝ) ≤ inner ℝ z ((dstarDCLM U + T2) z))
    (x : BondFnL2 L) :
    (0 : ℝ) ≤ inner ℝ x (cStarDeltaKC U ell Dinv T2 x) :=
  inner_cStarMC_nonneg (reparamCL2 U ell Dinv) ((dstarDCLM U + T2).toLinearMap) hpos x

/-- The `CoercivityHypothesis.Δ`-shaped promotion of the full sandwich. -/
noncomputable def cStarDeltaKCCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L) :
    BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (cStarDeltaKC U ell Dinv T2)

/-- The same identity at the bundled `cStarDeltaKCCLM`.
**[SUPERSEDED AS A CITATION, 2026-07-28, S75 — retained struck; TRUE of the raw object it names.]**
FAITHFUL TWIN: `§10b.inner_cStarDeltaKCCLM_normalized_eq`. -/
theorem inner_cStarDeltaKCCLM_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hT2 : ∀ A : Bond L → SuTwo, (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
      (T2 (WithLp.toLp 2 A)) : ℝ)
      = AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadFormTransported U A)
    (B : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
        (cStarDeltaKCCLM U ell Dinv T2 (WithLp.toLp 2 B)) : ℝ)
      = AdalyFormal.Balaban.DeltaKFull.deltaKQuadFormCorrected U (fullC U ell Dinv B) :=
  inner_cStarDeltaKC_eq U ell Dinv T2 hT2 B

#print axioms dstarDCLM
#print axioms inner_dstarDCLM_eq_dstarDQuadForm
#print axioms deltaKFull_T1_discharged
#print axioms cStarDeltaKC
#print axioms inner_cStarDeltaKC_eq
#print axioms bondAdjoint_cStarDeltaKC
#print axioms inner_cStarDeltaKC_nonneg
#print axioms cStarDeltaKCCLM
#print axioms inner_cStarDeltaKCCLM_eq

/-! ## §10b — THE SAME GENERIC MACHINERY, ON THE SOURCE-FAITHFUL OBJECT (S75 propagation)

**Why this section exists.** A grade-3 finding (blind Sol + blind Kimi + verified) established that
`DeltaKFull.deltaKQuadFormCorrected` mixes trace normalizations, so this tree's `Δ′` summand is
exactly twice CMP99b's, and the source-faithful assembly is
`NormalizationAudit.deltaKQuadFormNormalizedCorrected = dstarDQuadForm + (1/2)·Δ′_transported`.
`DeltaPrimeOperator.lean` was repaired for the CONCRETE supply
(`inner_cStarDeltaKC_normalized_unconditional` at `T2 := deltaPrimeCLMNormalized U`), but §10 —
the file that DEFINES and narrates the generic `T2`-conditional machinery — was never propagated to.
That desync is closed here: every §10 theorem now has a faithful twin at the same generality
(arbitrary `T2` constrained by an `hT2` naming the SOURCE-normalized `Δ′` form).

**These are NOT a rebuild of `DeltaPrimeOperator`'s theorems** (LAW-19). Those are the CONCRETE
`T2 := deltaPrimeCLMNormalized U` specializations and are proved by a different route
(`inner_deltaKCLMNormalized_eq`, bypassing this file's assembly step entirely). §10b is the generic
layer they should have been instances of, and is what any OTHER supply of `T2` needs.

**No positivity, coercivity, symmetry or lower bound is claimed anywhere in §10b** — these are form
identities only, exactly as §10's are. -/

open AdalyFormal.Balaban.NormalizationAudit in
/-- **`deltaKFull_T1_discharged`, FAITHFUL.** `T1 := dstarDCLM U` discharged by §4's Gram identity
exactly as in §10; the only change is that `hT2` names the SOURCE-normalized `Δ′` form and the
conclusion is the source-faithful assembly. Proved directly rather than through
`DeltaKFull.deltaKFullCLM_assembly_sound`, whose conclusion is hard-wired to the raw object. -/
theorem deltaKFull_T1_discharged_normalized
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hT2 : ∀ A : Bond L → SuTwo, (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
      (T2 (WithLp.toLp 2 A)) : ℝ)
      = deltaPrimeQuadFormNormalizedTransported U A)
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) ((dstarDCLM U + T2) (WithLp.toLp 2 A)) : ℝ)
      = deltaKQuadFormNormalizedCorrected U A := by
  unfold deltaKQuadFormNormalizedCorrected
  rw [ContinuousLinearMap.add_apply, inner_add_right, inner_dstarDCLM_eq_dstarDQuadForm, hT2]

open AdalyFormal.Balaban.NormalizationAudit in
/-- **THE FORM IDENTITY AT THE FULL `Δ_k`, FAITHFUL — this is the one that may be cited as
CMP99b (3.10).** `⟪B̃, (C*Δ_kC) B̃⟫ = Δ_k^source-form at `C B̃``, with `C B̃ = fullC U ell Dinv B̃`
and the middle map `dstarDCLM U + T2` for any `T2` supplying the SOURCE-normalized `Δ′`. -/
theorem inner_cStarDeltaKC_normalized_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hT2 : ∀ A : Bond L → SuTwo, (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
      (T2 (WithLp.toLp 2 A)) : ℝ)
      = deltaPrimeQuadFormNormalizedTransported U A)
    (B : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
        (cStarDeltaKC U ell Dinv T2 (WithLp.toLp 2 B)) : ℝ)
      = deltaKQuadFormNormalizedCorrected U (fullC U ell Dinv B) := by
  show (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
      (cStarMC (reparamCL2 U ell Dinv) ((dstarDCLM U + T2).toLinearMap)
        (WithLp.toLp 2 B)) : ℝ) = _
  rw [inner_cStarMC_self, reparamCL2_apply]
  exact deltaKFull_T1_discharged_normalized U T2 hT2 (fullC U ell Dinv B)

open AdalyFormal.Balaban.NormalizationAudit in
/-- The same at the bundled `cStarDeltaKCCLM`, faithful. -/
theorem inner_cStarDeltaKCCLM_normalized_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hT2 : ∀ A : Bond L → SuTwo, (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
      (T2 (WithLp.toLp 2 A)) : ℝ)
      = deltaPrimeQuadFormNormalizedTransported U A)
    (B : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 B : BondFnL2 L)
        (cStarDeltaKCCLM U ell Dinv T2 (WithLp.toLp 2 B)) : ℝ)
      = deltaKQuadFormNormalizedCorrected U (fullC U ell Dinv B) :=
  inner_cStarDeltaKC_normalized_eq U ell Dinv T2 hT2 B

open AdalyFormal.Balaban.NormalizationAudit in
/-- **MUST-FIRE CONTROL (S82 garbage substitution, and the whole point of §10b).**
The two `hT2` interfaces are NOT interchangeable: a `T2` satisfying the RAW `hT2` satisfies the
NORMALIZED one only if its form is identically zero. Concretely — if `T2` supplies the raw `Δ′` form
AND also the normalized one, then `deltaPrimeQuadFormTransported U A = 0` for every `A`. So a caller
who feeds §10's `T2` into §10b's slot cannot typecheck unless the `Δ′` term is trivial, which it is
not (`DeltaPrimeOperator.deltaPrimeOpNormalized_not_nonneg`,
`NormalizationAudit.deltaKQuadFormNormalizedCorrected_ne_deltaKQuadFormCorrected_at_witness`).

This is the check that §10b is a genuine repair rather than a relabelling: without it, "the twin has
a different name" would be the only evidence offered, and that is no evidence at all. -/
theorem raw_and_normalized_hT2_incompatible
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (T2 : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hraw : ∀ A : Bond L → SuTwo, (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
      (T2 (WithLp.toLp 2 A)) : ℝ)
      = AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadFormTransported U A)
    (hnorm : ∀ A : Bond L → SuTwo, (inner ℝ (WithLp.toLp 2 A : BondFnL2 L)
      (T2 (WithLp.toLp 2 A)) : ℝ)
      = deltaPrimeQuadFormNormalizedTransported U A)
    (A : Bond L → SuTwo) :
    AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadFormTransported U A = 0 := by
  have h := (hraw A).symm.trans (hnorm A)
  rw [deltaPrimeQuadFormNormalizedTransported_eq_half_transported] at h
  linarith

#print axioms deltaKFull_T1_discharged_normalized
#print axioms inner_cStarDeltaKC_normalized_eq
#print axioms inner_cStarDeltaKCCLM_normalized_eq
#print axioms raw_and_normalized_hT2_incompatible

/-! ## §11 — THE ONE REMAINING INPUT, AS A TYPED HOLE

`§10`'s `T2` + `hT2` IS `DeltaKFull` §7 Residual 2, restated as a Lean interface. Exactly this is
needed and nothing else:

    T2  : BondFnL2 L →L[ℝ] BondFnL2 L
    hT2 : ∀ A, ⟪toLp A, T2 (toLp A)⟫ = DeltaPrime.deltaPrimeQuadFormTransported U A

**What was blocking it, and what is no longer blocking it.** `DeltaKFull` §7 named TWO obstructions
for Residual 2: (a) build `Δ′`'s symmetric bilinear form, and (b) represent it as a vector/operator
"WITHOUT `InnerProductSpace.toDual` (§6)". Obstruction (b) is REMOVED by §8's
`bilinToOperatorBond`: any bilinear form on `BondFnL2 L` is the form of an operator, and a SYMMETRIC
one of a self-adjoint operator (`bondAdjoint_bilinToOperatorBond`). Note this is NOT achieved by
making `toDual` work — §8's own docstring records the MEASURED failure of `toDual` here and confirms
`DeltaKFull` §6's diagnosis for it — but by taking `LinearMap.adjoint` into the scalar field, where
no bundled `→L` and hence no topology enters any type.

So what remains is (a) alone: `deltaPrimeQuadFormTransported` is a `Finset.sum` over plaquettes of
`Re U(∂p)`-weighted terms plus a commutator sum, and its symmetric bilinear form must be written out
term by term. `DeltaKFull` §7 sizes that at "comparable in size to `DeltaPrime.lean` itself"
(~1000 lines). It is ALGEBRA — no instance obstruction, no adjoint obstruction, no missing Mathlib
API — and it was NOT attempted in this lane. That is the honest state: one input, its type written
down, its two historical blockers reduced to one, and the remaining one is bookkeeping-heavy algebra
in a different module's territory (`DeltaPrime.lean`).

**Not claimed**: that `T2` exists. Nothing in this module asserts it, and §10's theorems all carry it
as a hypothesis. `cStarDeltaKC` is a `def` in `T2`, so it is inhabited for ANY `T2` (including `0`) —
it is `hT2` that pins the mathematics, and every theorem that says anything about `Δ_k` takes `hT2`.

**AND `hT2` DOES NOT DETERMINE `T2` — disclosed, because it is a statement-level fact and no gate here
would catch it.** `hT2` constrains only the DIAGONAL `⟪A, T2 A⟫`, so it fixes `T2`'s quadratic form and
says nothing about a skew-symmetric part: if `T2` satisfies `hT2` then so does `T2 + S` for any `S`
with `⟪A, S A⟫ = 0` for all `A` (over ℝ, any skew `S`). This is harmless for every conclusion drawn in
§10 — `inner_cStarDeltaKC_eq` is a statement about the diagonal too, and the self-adjointness/PSD
theorems take their own hypotheses about the SAME `dstarDCLM U + T2` — but a consumer who needs `Δ_k`
to be a UNIQUELY DETERMINED operator must add `bondAdjoint (dstarDCLM U + T2).toLinearMap =
(dstarDCLM U + T2).toLinearMap` (self-adjointness), which pins it, and which is exactly the `hsym`
hypothesis `bondAdjoint_cStarDeltaKC` already takes. It is not assumed anywhere silently.
-/

end AdalyFormal.Balaban.CStarDeltaKCOperator
