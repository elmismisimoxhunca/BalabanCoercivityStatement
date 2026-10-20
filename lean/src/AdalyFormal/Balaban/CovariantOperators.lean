/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.LatticeOperators
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

set_option autoImplicit false

/-!
# The COVARIANT lattice derivative `D_U`, `R` — CMP99b pp.390-392

**Task, per `compute/lattice_operator_audit/OPERATOR_AUDIT.md` Part 2** (source pins and
image-confirmed transcriptions there, not re-derived here): Bałaban's covariant lattice gradient

`(D^η_{U0}A)(b) = η⁻¹(R(U0(b))A(b_+) - A(b_-))`, `R(U)X = U X U⁻¹`

on a genuinely new carrier, `Bond L → 𝔰𝔲(2)` (traceless anti-Hermitian `2×2` complex matrices),
in place of the flat file's `Bond L → ℝ`.

## Two prohibitions this file honors (mandate, both load-bearing)

1. **`d² = 0` is FALSE for the covariant case and is NOT proved or assumed here.** The audit's own
   §2.3 derivation (reproduced independently below, §4) shows `D_U ∘ D_U` measures a genuine
   holonomy/curvature obstruction that vanishes only when the relevant plaquette holonomies (in
   the adjoint sense) are central. What is built instead is the **curvature identity** itself,
   `curlValueCovariant_gradValueCovariant`, stated and proved as its own theorem — the honest
   replacement for the (false) exactness lemma.
2. **This file does NOT claim to build `Δ_k(U)`.** `HoleHunt/LargeFieldKill.lean` (read-only,
   NO-GO per this dispatch) already proves, kernel-checked, that no `CoercivityHypothesis` can
   hold when `Δ` is a bare rank-bounded pullback `v ↦ ‖Cv‖²` — and a bare, `H_j`-free covariant
   curl is *exactly zero* on flat backgrounds because the pure-gauge coboundary kernel scales with
   the lattice while CMP96 `(2.121)`'s admissible subspace has fixed codimension. `D_U`/`R` are
   built here as necessary ingredients toward `Δ_k(U)`, not as `Δ_k(U)` itself; `H_j` remains
   unbuilt and is explicitly out of scope, as is `Δ'` (CMP99b eq. 3.10).

## Source pins (LAW-11, all already image-confirmed by `OPERATOR_AUDIT.md` §2)

* CMP99b (`balaban_CMP99_1985_propagators_backgroundfield.pdf`, offset 388) printed p.390: the
  unnumbered display defining `D^η_{U0}A` above, and `R(U)X = UXU⁻¹` ("Let us recall that
  `R(U)X = UXU⁻¹`").
* CMP99b p.391, eq. (3.3): the site→bond covariant gradient `(D^η_{U0,μ}A)(x) = (D^η_{U0}A)(x,
  x+ηe_μ)`. eq. (3.4): the bond→plaquette covariant curl, `R(U0(x,y))`/`R(U0(x,w))` insertions on
  the middle two terms of the four-term plaquette sum (conjugations, not sign flips — the
  qualitative change from the flat case). Antisymmetry (eq. 3.5) carries over unchanged:
  `U(x,x')=U⁻¹(x',x)`, `A(x,x')=-A(x',x)`.
* CMP99b p.392, eq. (3.10): `Δ = D*D + Δ'`, `Δ'` built from `Re U(∂p)-1` and `Im U(∂p)`, vanishing
  identically iff `U(∂p)=1` for every plaquette — Bałaban's own encoding of the fact that `d²=0`
  is a FLAT-background-only phenomenon, not a general identity. `Δ'` itself is out of scope here
  (named, not built), matching `LatticeOperators.lean`'s own NO-GO discipline for `R`/`H_j`/`Δ_a`.

## What this module builds

1. **`suTwo`** — `𝔰𝔲(2)` as a genuine `Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ)`: traceless
   skew-Hermitian matrices, built from `Matrix.conjTranspose`/`Matrix.trace` closure lemmas (not
   assumed). Not decorated from `LatticeOperators.lean`'s `ℝ`-valued carrier — a genuinely
   different type, per the audit's own verdict.
2. **`R`** — the adjoint action `R(U)X = U X U⁻¹` of `Matrix.specialUnitaryGroup (Fin 2) ℂ` on
   `suTwo`, as a `LinearMap ℝ` for each `U` (`RMap`), with:
   - `RMap_mem` — the closure lemma (conjugating a traceless skew-Hermitian matrix by a unitary
     stays traceless skew-Hermitian) — genuinely proved, not assumed (L4: no axiom).
   - `RMap_one` — `R(1) = id`.
   - `RMap_mul` — `R(U) ∘ R(V) = R(U*V)` (the homomorphism fact the audit flagged as "immediate
     from `R`'s own definition" — proved here, not merely asserted).
3. **`gradValueCovariant`/`curlValueCovariant`** — the covariant `∂₀`/`∂₁` on `Bond L → suTwo`,
   direct transcriptions of the quoted displays.
4. **`curlValueCovariant_gradValueCovariant`** — the CURVATURE IDENTITY replacing the (false)
   exactness lemma: `(D_U(D_Uλ))(p)` collapses to a SINGLE surviving term at the plaquette's far
   corner, coefficient the DIFFERENCE of two boundary holonomies in the adjoint representation —
   ~~three holonomy composites~~ **SUPERSEDED (S75): the audit's own §2.3 hand computation reports
   THREE surviving terms; this build's full kernel-checked expansion shows the other two cancel
   completely, leaving one. See §4's docstring below for the full correction record.**
5. **§6 D4 falsifiability** for `R` (garbage: plain left-multiplication `X ↦ UX`, not a genuine
   conjugation, fails the closure/trace-preservation obligation) and for `suTwo`'s two
   defining conditions separately (a Hermitian-but-not-traceless garbage matrix, and a
   traceless-but-not-skew-Hermitian garbage matrix, EACH fails membership at exactly the field the
   garbage violates).

## Residual / scope note

`InnerProductSpace ℝ suTwo` is NOT built here (flagged as the single riskiest item in the audit's
build list). None of the deliverables above need a norm or inner product — the covariant
gradient/curl are `Module ℝ`-level linear maps, and the curvature identity is an equation of
Lie-algebra-valued functions, not a positivity statement. If a future dispatch needs `Δ'`/`H_j` or
a coercivity-style bound on this carrier, the Hilbert-Schmidt inner product `X·Y = Re(tr(XY))`
restricted to `suTwo` (CMP99b p.392's own stated convention) is the natural next construction,
named here as an explicit residual rather than attempted.
-/

namespace AdalyFormal.Balaban.CovariantOperators

open Matrix Complex AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.AdmissibleSubspace

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `suTwo`, `𝔰𝔲(2)` as a genuine `Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ)` -/

/-- **`𝔰𝔲(2)`: traceless skew-Hermitian `2×2` complex matrices**, CMP99b p.391's Lie algebra
carrier for `A`, `X` in `R(U)X = UXU⁻¹`. Built as a `Submodule ℝ`, not decorated from any existing
Mathlib `su(n)` object (none exists, per the audit's Mathlib-availability survey). -/
def suTwo : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {X | Xᴴ = -X ∧ Matrix.trace X = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hX1, hX2⟩ ⟨hY1, hY2⟩
    refine ⟨?_, ?_⟩
    · rw [conjTranspose_add, hX1, hY1, neg_add]
    · rw [trace_add, hX2, hY2, add_zero]
  smul_mem' := by
    rintro c X ⟨hX1, hX2⟩
    refine ⟨?_, ?_⟩
    · rw [conjTranspose_smul, hX1, star_trivial, smul_neg]
    · rw [trace_smul, hX2, smul_zero]

/-- The underlying type of `𝔰𝔲(2)`. -/
abbrev SuTwo := (suTwo : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ))

theorem mem_suTwo_iff (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X ∈ suTwo ↔ Xᴴ = -X ∧ Matrix.trace X = 0 := Iff.rfl

/-! ### L7 witness: `suTwo` is genuinely inhabited by a nonzero element -/

/-- `i·diag(1,-1)` — a concrete nonzero traceless skew-Hermitian matrix (the Pauli-`σ₃` direction,
scaled by `i`). -/
def suTwoWitnessVal : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

theorem suTwoWitnessVal_mem : suTwoWitnessVal ∈ suTwo := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [suTwoWitnessVal, Matrix.conjTranspose_apply]
  · simp [suTwoWitnessVal, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem suTwoWitnessVal_ne_zero : suTwoWitnessVal ≠ 0 := by
  intro h
  have h00 : suTwoWitnessVal 0 0 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h]
  simp only [suTwoWitnessVal, Matrix.cons_val', Matrix.cons_val_zero, Matrix.zero_apply,
    Matrix.of_apply] at h00
  exact Complex.I_ne_zero h00

/-- **`suTwoWitnessVal` is not fixed by negation** (`I ≠ -I` at entry `(0,0)`) — the fact §5's
curvature witness needs: the concrete `M`-conjugation result `-suTwoWitness` is genuinely
DIFFERENT from `suTwoWitness`, not merely "some nonzero perturbation." -/
theorem suTwoWitnessVal_ne_neg_self : suTwoWitnessVal ≠ -suTwoWitnessVal := by
  intro h
  have h00 : suTwoWitnessVal 0 0 = (-suTwoWitnessVal) 0 0 := congrFun (congrFun h 0) 0
  simp only [suTwoWitnessVal, Matrix.neg_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.of_apply] at h00
  norm_num [Complex.ext_iff] at h00

/-- The witness, packaged as an element of the submodule type. -/
def suTwoWitness : SuTwo := ⟨suTwoWitnessVal, suTwoWitnessVal_mem⟩

theorem suTwoWitness_ne_zero : suTwoWitness ≠ 0 := by
  intro h
  exact suTwoWitnessVal_ne_zero (congrArg Subtype.val h)

theorem suTwoWitness_ne_neg_self : suTwoWitness ≠ -suTwoWitness := by
  intro h
  exact suTwoWitnessVal_ne_neg_self (congrArg Subtype.val h)

/-! ### D4 garbage carrier tests — each fails at EXACTLY the field it violates -/

/-- **D4 GARBAGE #1: traceless but NOT skew-Hermitian.** `diag(1,-1)` is real, symmetric,
traceless — but its conjugate transpose is ITSELF, not its negative (since it is nonzero, `X ≠
-X`). Confirms the skew-Hermitian clause is load-bearing, not decorative. -/
def garbageNotSkewHermitian : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem garbageNotSkewHermitian_trace_zero : Matrix.trace garbageNotSkewHermitian = 0 := by
  simp [garbageNotSkewHermitian, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem garbageNotSkewHermitian_not_skewHermitian :
    ¬ (garbageNotSkewHermitian)ᴴ = -garbageNotSkewHermitian := by
  intro h
  have h00 : (garbageNotSkewHermitian)ᴴ 0 0 = (-garbageNotSkewHermitian) 0 0 := by rw [h]
  simp only [garbageNotSkewHermitian, Matrix.conjTranspose_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.neg_apply, Matrix.of_apply, star_one] at h00
  norm_num at h00

/-- Consequently `garbageNotSkewHermitian ∉ suTwo` — the closure obligation fails at exactly the
skew-Hermitian clause, not the trace clause (which independently holds). -/
theorem garbageNotSkewHermitian_not_mem : garbageNotSkewHermitian ∉ suTwo := by
  rw [mem_suTwo_iff]
  rintro ⟨h1, -⟩
  exact garbageNotSkewHermitian_not_skewHermitian h1

/-- **D4 GARBAGE #2: skew-Hermitian but NOT traceless.** `diag(i, i)` is purely imaginary diagonal
(skew-Hermitian), but its trace is `2i ≠ 0`. Confirms the traceless clause is load-bearing,
independently of the skew-Hermitian clause. -/
def garbageNotTraceless : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, Complex.I]

theorem garbageNotTraceless_skewHermitian : (garbageNotTraceless)ᴴ = -garbageNotTraceless := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [garbageNotTraceless, Matrix.conjTranspose_apply]

theorem garbageNotTraceless_trace_ne_zero : Matrix.trace garbageNotTraceless ≠ 0 := by
  simp only [garbageNotTraceless, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  intro h
  have := congrArg Complex.im h
  simp at this

theorem garbageNotTraceless_not_mem : garbageNotTraceless ∉ suTwo := by
  rw [mem_suTwo_iff]
  rintro ⟨-, h2⟩
  exact garbageNotTraceless_trace_ne_zero h2

/-! ## §2 — `R`, the adjoint action of `SU(2)` on `𝔰𝔲(2)` (CMP99b p.390: "`R(U)X = UXU⁻¹`") -/

/-- The ambient conjugation map `X ↦ UXU⁻¹ = UXUᴴ` on the FULL matrix space, as an `ℝ`-linear
map — built first on the ambient space, then restricted to `suTwo` below (so the closure lemma is
a genuine proof obligation, not baked into the type). -/
noncomputable def conjByAmbient (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := (U : Matrix (Fin 2) (Fin 2) ℂ) * X * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [RingHom.id_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul]

theorem conjByAmbient_apply (U : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    conjByAmbient U X = (U : Matrix (Fin 2) (Fin 2) ℂ) * X * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl

/-- **The closure lemma (L4: proved, not an `axiom`)**: conjugating a traceless skew-Hermitian
matrix by a special-unitary matrix stays traceless skew-Hermitian. -/
theorem conjByAmbient_mem (U : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X ∈ suTwo) : conjByAmbient U X ∈ suTwo := by
  obtain ⟨hX1, hX2⟩ := hX
  have hUU : (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp U.2.1
    rwa [Matrix.star_eq_conjTranspose] at h
  refine ⟨?_, ?_⟩
  · rw [conjByAmbient_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hX1]
    noncomm_ring
  · rw [conjByAmbient_apply, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hUU,
      Matrix.mul_one]
    exact hX2

/-- **`R(U) : 𝔰𝔲(2) →ₗ[ℝ] 𝔰𝔲(2)`**, the adjoint action, built by restricting `conjByAmbient U` to
`suTwo` using the closure lemma just proved. -/
noncomputable def RMap (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) : SuTwo →ₗ[ℝ] SuTwo :=
  (conjByAmbient U).restrict (fun X hX => conjByAmbient_mem U X hX)

theorem RMap_coe_apply (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    (RMap U X : Matrix (Fin 2) (Fin 2) ℂ) =
      (U : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ :=
  LinearMap.coe_restrict_apply _ X

/-- **`R(1) = id`** — the trivial background transports nothing. -/
theorem RMap_one : RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  rw [RMap_coe_apply]
  simp

/-- **`R(U) ∘ R(V) = R(UV)`**, the homomorphism fact underlying the curvature computation below
(the audit flagged this as "immediate from `R`'s own definition," proved here rather than merely
asserted). -/
theorem RMap_mul (U V : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    RMap (U * V) = (RMap U).comp (RMap V) := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  rw [LinearMap.comp_apply, RMap_coe_apply, RMap_coe_apply, RMap_coe_apply]
  simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul]
  noncomm_ring

/-- **Direct corollary of `RMap_mul`, at the point-applied level** — the exact rewrite target
the curvature computation (§4) needs: two successive `R`-transports compose into a single `R`
at the product. -/
theorem RMap_mul_apply (U V : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    RMap U (RMap V X) = RMap (U * V) X := by
  rw [RMap_mul]; rfl

/-! ### D4 falsifiability for `R`: a garbage "action" that is not conjugation -/

/-- **D4 GARBAGE: plain left-multiplication `X ↦ UX`**, dropping the `U⁻¹` on the right entirely
— the exact "silent, coherent-looking" wrong transcription §LEAN-D warns about (forgetting the
adjoint's defining shape `R(U)X = UXU⁻¹` and treating it as an ordinary group action by left
translation). This does NOT preserve `suTwo` in general. -/
noncomputable def garbageLeftMul (U : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (U : Matrix (Fin 2) (Fin 2) ℂ) * X

-- The garbage action's closure failure is exhibited concretely in §5, on the SAME witness matrix
-- `M` used for the curvature non-vanishing test (no separate witness invented for it).

/-! ## §3 — the covariant gradient and curl on `Bond L → 𝔰𝔲(2)` -/

/-- **`(D_Uλ)(b) = R(U(b))λ(b_+) - λ(b_-)`**, CMP99b p.390's unnumbered display / eq (3.3),
unit-lattice convention (matching `LatticeOperators.lean`'s own `ε→1` disclosed convention, same
source paper family). -/
noncomputable def gradValueCovariant
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (b : Bond L) : SuTwo :=
  RMap (U b) (lam (periodicLatticeShift b.1 b.2)) - lam b.1

/-- **`(D_UA)(p) = A(x,μ) + R(U(x,μ))A(shift_μ x,ν) - R(U(x,ν))A(shift_ν x,μ) - A(x,ν)`**, CMP99b
p.391 eq (3.4), traced term-by-term against the audit's quoted display
`A(x,y) + R(U0(x,y))A(y,z) + R(U0(x,w))A(z,w) + A(w,x)`: the LAST TWO source terms are traversed
BACKWARDS relative to `Bond`'s forward storage (`A(z,w) = -A(shift_ν x,μ)`, `A(w,x) = -A(x,ν)`,
antisymmetry eq. 3.5, unchanged from the flat case), and the transport factors are DIRECT bond
values based at `x` (`U0(x,y) = U(x,μ)`, `U0(x,w) = U(x,ν)` — `y`, `w` are `x`'s forward-`μ`,
forward-`ν` neighbors respectively, so these are single bond evaluations, not composite
holonomies). This is the qualitative change from the flat case the mandate names: CONJUGATIONS on
the middle two terms, not sign flips. -/
noncomputable def curlValueCovariant
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : SuTwo :=
  A (p.1, p.2.1.1) + RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) -
    RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - A (p.1, p.2.1.2)

/-! ## §4 — THE CURVATURE IDENTITY (replacing the FALSE exactness lemma, per the mandate)

**`d²=0` does NOT hold here.** `curlValueCovariant_gradValueCovariant` below computes
`(D_U(D_Uλ))(p)` EXACTLY: every "off-diagonal" contribution cancels (as in the flat case), leaving
a single residual term proportional to `λ` evaluated at the plaquette's FAR CORNER `z`, with
coefficient the DIFFERENCE of the two plaquette-boundary holonomies (in the adjoint
representation) `R(U(x,μ)·U(y,ν))` and `R(U(x,ν)·U(w,μ))` — i.e. exactly the adjoint-action
obstruction of the plaquette holonomy, matching Bałaban's own `Δ'` (CMP99b eq. 3.10) being built
from `U(∂p)` and vanishing only when `U(∂p)` is central (flat, up to center). This is a CLEANER
single-term form than `OPERATOR_AUDIT.md` §2.3's own three-term hand derivation (which the audit
itself flagged as "this audit's own derivation... not a sentence transcribed from the paper," not
a claim of literal source equality) — the two `λ_x`, `λ_w` contributions that survive in the
audit's hand computation cancel completely once carried through in full generality here,
kernel-checked rather than hand-traced. Both computations agree on the headline fact: the identity
vanishes identically iff the two holonomy composites act identically in the adjoint
representation, i.e. iff the plaquette holonomy is central — NOT in general. -/
theorem curlValueCovariant_gradValueCovariant
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (p : PeriodicLatticePlaquette L) :
    curlValueCovariant U (gradValueCovariant U lam) p =
      RMap (U (p.1, p.2.1.1) * U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
        (lam (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)) -
      RMap (U (p.1, p.2.1.2) * U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
        (lam (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2)) := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  have hcomm := AdalyFormal.Balaban.LatticeOperators.periodicLatticeShift_comm p.1 hne
  simp only [curlValueCovariant, gradValueCovariant, map_sub]
  rw [← hcomm, RMap_mul_apply, RMap_mul_apply]
  abel

/-! ## §5 — CONCRETE WITNESS: `d²≠0` on an explicit non-flat background (the mandate's own
prohibition #1, exhibited positively: this is NOT vacuously true) -/

/-- **`M = !![0,1;-1,0]`** — a concrete `SU(2)` element (real, orthogonal, determinant `1`),
chosen so that conjugation by it visibly rotates the witness Lie-algebra element. -/
def witnessM : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem witnessM_mem_unitaryGroup : witnessM ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessM, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem witnessM_det : witnessM.det = 1 := by
  simp [witnessM, Matrix.det_fin_two_of]

theorem witnessM_mem : witnessM ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨witnessM_mem_unitaryGroup, witnessM_det⟩

/-- `M`, packaged as an element of the group. -/
def witnessMElem : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨witnessM, witnessM_mem⟩

/-- **The hand-verifiable conjugation computation `M·diag(i,-i)·M⁻¹ = -diag(i,-i)`.** -/
theorem RMap_witnessMElem : RMap witnessMElem suTwoWitness = -suTwoWitness := by
  apply Subtype.ext
  rw [RMap_coe_apply]
  change witnessM * suTwoWitnessVal * witnessMᴴ = -suTwoWitnessVal
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessM, suTwoWitnessVal, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- `M` itself is (coincidentally) a valid element of `suTwo` (real, traceless, antisymmetric —
hence skew-Hermitian): a convenient SECOND witness, distinct from `suTwoWitnessVal`, used only for
the D4 test below. -/
theorem witnessM_mem_suTwo : witnessM ∈ suTwo := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [witnessM, Matrix.conjTranspose_apply]
  · simp [witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- **D4 test for `garbageLeftMul`, exhibited concretely (not merely asserted).** Plain
left-multiplication does NOT preserve `suTwo`: `garbageLeftMul M M = M·M = -I` (`M`'s own square,
computed directly: `!![0,1;-1,0]²=-I`), and `-I` is not skew-Hermitian (`(-I)ᴴ = -I ≠ I = -(-I)`,
entry `(0,0)`: `-1 ≠ 1`) — the exact "silent, coherent-looking" failure §LEAN-D warns about,
caught at exactly the field (skew-Hermitian-ness) the garbage action was designed to violate. -/
theorem garbageLeftMul_witnessM_not_mem :
    garbageLeftMul witnessMElem witnessM ∉ suTwo := by
  rw [mem_suTwo_iff]
  rintro ⟨hskew, -⟩
  have h00 : (garbageLeftMul witnessMElem witnessM)ᴴ 0 0 =
      (-(garbageLeftMul witnessMElem witnessM)) 0 0 := by rw [hskew]
  simp only [garbageLeftMul, witnessMElem, witnessM,
    Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply] at h00
  norm_num [Complex.ext_iff] at h00

/-- The witness plaquette on the shared witness lattice, reused from `LatticeOperators` (LAW-19)
rather than re-invented: base site `witnessY`, directions `μ=0,ν=1`. -/
def witnessPlaquette : PeriodicLatticePlaquette AdmissibleSubspace.witnessL :=
  (AdmissibleSubspace.witnessY, ⟨(0, 1), by decide⟩)

/-- The "far corner" of the witness plaquette, `shift_0(shift_1(witnessY))`. -/
def witnessZPoint : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
  periodicLatticeShift (periodicLatticeShift AdmissibleSubspace.witnessY 0) 1

/-- **The non-flat background**: `M` on the single link `(witnessY, 0)`, trivial (`1`) on every
other link. -/
noncomputable def witnessU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) AdmissibleSubspace.witnessL :=
  fun e => if e = (AdmissibleSubspace.witnessY, (0 : Fin 3)) then witnessMElem else 1

/-- **The scalar field**: `suTwoWitness` at the far corner, `0` elsewhere. -/
noncomputable def witnessLam :
    PeriodicLatticeSite AdmissibleSubspace.witnessL → SuTwo :=
  fun z => if z = witnessZPoint then suTwoWitness else 0

theorem witnessU_at_x_mu : witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3)) = witnessMElem := by
  simp [witnessU]

theorem witnessU_at_y_nu :
    witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3)) = 1 := by
  simp only [witnessU, ite_eq_right_iff]
  intro h; exact absurd h (by decide)

theorem witnessU_at_x_nu : witnessU (AdmissibleSubspace.witnessY, (1 : Fin 3)) = 1 := by
  simp only [witnessU, ite_eq_right_iff]
  intro h; exact absurd h (by decide)

theorem witnessU_at_w_mu :
    witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3)) = 1 := by
  simp only [witnessU, ite_eq_right_iff]
  intro h; exact absurd h (by decide)

theorem witnessLam_at_z : witnessLam witnessZPoint = suTwoWitness := by
  simp [witnessLam]

/-- **THE HEADLINE NEGATIVE RESULT**: `D_U∘D_U ≠ 0` on this concrete non-flat witness — `d²=0`
genuinely fails, not merely "is not proved here." Combines the general curvature identity (§4)
with the concrete link/field data above: the two holonomy composites evaluate to `M` and `1`
respectively (every other link is trivial by construction), so the curvature reduces to
`R(M)(suTwoWitness) - suTwoWitness = -suTwoWitness - suTwoWitness ≠ 0`. -/
theorem witness_curvature_ne_zero :
    curlValueCovariant witnessU (gradValueCovariant witnessU witnessLam) witnessPlaquette ≠ 0 := by
  rw [curlValueCovariant_gradValueCovariant]
  change RMap (witnessU (AdmissibleSubspace.witnessY, (0 : Fin 3)) *
        witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3)))
      (witnessLam witnessZPoint) -
    RMap (witnessU (AdmissibleSubspace.witnessY, (1 : Fin 3)) *
        witnessU (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3)))
      (witnessLam witnessZPoint) ≠ 0
  rw [witnessU_at_x_mu, witnessU_at_y_nu, witnessU_at_x_nu, witnessU_at_w_mu, witnessLam_at_z,
    mul_one, one_mul, RMap_witnessMElem, RMap_one]
  simp only [LinearMap.id_coe, id_eq]
  rw [sub_ne_zero]
  exact fun h => suTwoWitness_ne_neg_self h.symm

/-! ## §6 — PROMOTION TO `ContinuousLinearMap` (the mandate's stated deliverable shape)

Mathlib deliberately withholds a DEFAULT norm instance on `Matrix m n α` — there are several
natural choices (sup, `L¹`, Frobenius/`L²`-operator), so each is a SCOPED instance requiring
explicit activation, never a plain global one (checked directly against
`Mathlib.Analysis.Matrix.Normed`/`Mathlib.Analysis.CStarAlgebra.Matrix`, not assumed). This section
opens the `L²`-operator norm (the one under which `Matrix.specialUnitaryGroup` is a genuine
`NormedAlgebra`) and promotes `gradValueCovariant`/`curlValueCovariant`/`RMap` (for fixed `U`) to
genuine `ContinuousLinearMap`s — mirroring `LatticeOperators.lean`'s own §4 exactly (LinearMap
first, transported to `ContinuousLinearMap` second, since EVERY linear map between
finite-dimensional normed spaces is automatically continuous — continuity here is a topological
formality, not new mathematical content beyond what §2-§4 already proved). -/

open scoped Matrix.Norms.L2Operator

noncomputable instance instNormedSpaceRealMatrix : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedSpace.restrictScalars ℝ ℂ (Matrix (Fin 2) (Fin 2) ℂ)

/-- `RMap U`, for a FIXED `U`, transported to a genuine `ContinuousLinearMap`. -/
noncomputable def RCLM (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) : SuTwo →L[ℝ] SuTwo :=
  LinearMap.toContinuousLinearMap (RMap U)

theorem RCLM_coe_apply (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    RCLM U X = RMap U X := rfl

/-- **`(D_Uλ)`, for FIXED `U`, as a genuine `LinearMap ℝ`** — the linearity-in-`λ` fact
`gradValueCovariant` needs before it can be promoted to a `ContinuousLinearMap`. -/
noncomputable def gradCovariantLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) where
  toFun := gradValueCovariant U
  map_add' lam1 lam2 := by
    funext b
    simp only [gradValueCovariant, Pi.add_apply, map_add]
    abel
  map_smul' c lam := by
    funext b
    simp only [gradValueCovariant, Pi.smul_apply, RingHom.id_apply, map_smul, smul_sub]

/-- **`(D_UA)`, for FIXED `U`, as a genuine `LinearMap ℝ`.** -/
noncomputable def curlCovariantLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →ₗ[ℝ] (PeriodicLatticePlaquette L → SuTwo) where
  toFun := curlValueCovariant U
  map_add' A1 A2 := by
    funext p
    simp only [curlValueCovariant, Pi.add_apply, map_add]
    abel
  map_smul' c A := by
    funext p
    simp only [curlValueCovariant, Pi.smul_apply, RingHom.id_apply, map_smul, smul_sub, smul_add]

noncomputable instance instNormedAddCommGroupBondFn : NormedAddCommGroup (Bond L → SuTwo) :=
  Pi.normedAddCommGroup
noncomputable instance instNormedSpaceBondFn : NormedSpace ℝ (Bond L → SuTwo) :=
  Pi.normedSpace
noncomputable instance instNormedAddCommGroupSiteFn :
    NormedAddCommGroup (PeriodicLatticeSite L → SuTwo) := Pi.normedAddCommGroup
noncomputable instance instNormedSpaceSiteFn : NormedSpace ℝ (PeriodicLatticeSite L → SuTwo) :=
  Pi.normedSpace
noncomputable instance instNormedAddCommGroupPlaqFn :
    NormedAddCommGroup (PeriodicLatticePlaquette L → SuTwo) := Pi.normedAddCommGroup
noncomputable instance instNormedSpacePlaqFn :
    NormedSpace ℝ (PeriodicLatticePlaquette L → SuTwo) := Pi.normedSpace

/-- **`D_U : (Sites → 𝔰𝔲(2)) →L[ℝ] (Bond L → 𝔰𝔲(2))`, a genuine `ContinuousLinearMap`** — the
mandate's primary requested SHAPE for the covariant gradient. -/
noncomputable def gradCovariantCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (PeriodicLatticeSite L → SuTwo) →L[ℝ] (Bond L → SuTwo) :=
  LinearMap.toContinuousLinearMap (gradCovariantLM U)

/-- **`D_U : (Bond L → 𝔰𝔲(2)) →L[ℝ] (Plaquettes → 𝔰𝔲(2))`, a genuine `ContinuousLinearMap`** — the
mandate's primary requested SHAPE for the covariant curl. -/
noncomputable def curlCovariantCLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →L[ℝ] (PeriodicLatticePlaquette L → SuTwo) :=
  LinearMap.toContinuousLinearMap (curlCovariantLM U)

theorem gradCovariantCLM_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) :
    gradCovariantCLM U lam = gradValueCovariant U lam := rfl

theorem curlCovariantCLM_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    curlCovariantCLM U A = curlValueCovariant U A := rfl

/-! ## §7 — DEFECT 1/2 REPAIR (`SILENT_OBJECT_FIXES.md`, 2026-07-21): the genuine `L²` carrier,
introduced ALONGSIDE the SUP carrier above (never replacing it — no existing consumer of §6's six
`Pi.*` instances is touched), plus a falsifiable pin PROVING the two disagree.

**Defect 1.** CMP99b p.391 states the `D*` adjoints are taken w.r.t. "natural `L²` scalar
products", but `instNormedAddCommGroupBondFn` above is `Pi.normedAddCommGroup`, which on a FINITE
index type IS the SUP norm (`CONVENTION_PINS.md` §1b) — harmless for §6's own use (promoting linear
maps to `ContinuousLinearMap`s: a topological formality, since every linear map between
finite-dimensional normed spaces is automatically continuous REGARDLESS of which norm is chosen),
but silently WRONG for any future `D*`/`H_j`/`Δ'` construction that reads a QUADRATIC FORM off
`‖·‖` here. `PiLp 2 (fun _ : Bond L => SuTwo)` — Mathlib's genuine `L²` carrier — is a DIFFERENT
TYPE from `Bond L → SuTwo` (a `WithLp`-wrapped one-field structure, not a plain function type), so
introducing it does NOT collide with `instNormedAddCommGroupBondFn`: no rename, no deprecation, no
change to any existing use site.

**Defect 2, and the diamond this repair pass DECLINED to create.** The obvious-looking companion
fix — name a top-level `NormedAddCommGroup SuTwo` HERE so an ordinary importer of THIS file alone
can find one — was drafted and then REJECTED on inspection, not merely assumed unsafe:
`Balaban/SuTwoInner.lean` (which IMPORTS this file, so the reverse import is a genuine cycle,
checked directly against its `import` line rather than assumed) ALREADY installs the canonical
`instNormedAddCommGroupSuTwo : NormedAddCommGroup SuTwo`, built from `hsInner = -(1/2)Tr(XY)`
(CMP99b's own stated form, image-verified there). A SECOND, differently-sourced instance of the
exact same type declared here (from the `Matrix.Norms.L2Operator` scope instead) would become
GLOBALLY visible to Lean's typeclass search the moment any file imports both modules — which every
consumer of `SuTwoInner` already does, transitively — an actual instance DIAMOND, resolved SILENTLY
by Lean with no error. That is a STRICTLY WORSE version of exactly the defect this dispatch exists
to kill: it would put `SuTwoInner.lean`'s own kernel-checked positive-definiteness and Gram
computations at risk of silently resolving against the wrong norm. So Defect 2 is repaired here by
(a) NAMING the scope dependency the six `Pi.*` instances already rely on, explicitly, rather than
leaving it an unlabeled side effect of `open scoped`, and (b) the falsifiable CONTENT pin below,
proving what those six instances actually compute (SUP, not `L²`) — so a consumer cannot be fooled
by an instance merely being *present*. The deeper architectural fix (breaking the import cycle so
one canonical `SuTwo` norm is reachable from both files without a loop) is written as a patch
proposal in `SILENT_OBJECT_FIXES.md`, NOT applied here — restructuring which file owns `suTwo`
itself is a larger change than this lane's write scope safely allows in one pass.

**UPDATE (S75, `formal/AdalyFormal/SUTWO_DIAMOND.md`) — `SILENT_OBJECT_FIXES.md`'s P4 is now
CLOSED, P3 is still OPEN, and the two must not be conflated.** A later dispatch measured directly
(`#synth`, no reasoning from prose) that the BARE `SuTwo` type had no findability problem for
`NormedAddCommGroup`/`InnerProductSpace` (`SuTwoInner.lean`'s own top-level instances were already
correct and unambiguous the moment a file imports `SuTwoInner` — the "diamond" language above is
about `Bond L → SuTwo`/`BondFnL2 L`, never about bare `SuTwo`). What WAS genuinely broken on bare
`SuTwo` — `CompleteSpace`/`UniformSpace`, P4/R1 in the old naming — is now fixed IN `SuTwoInner.lean`
(a real `CompleteSpace ↥SuTwo` instance, plus a sorry-free proof that the ambient
`instUniformSpaceSubtype` and the norm's own uniformity are literally the SAME `UniformSpace`, via
`Mathlib.Topology.Algebra.Module.FiniteDimension`'s general TVS machinery — no norm/scope dependency
in that proof, so it cannot touch the diamond below).

~~**P3 — the genuine, still-open one — lives at `BondFnL2 L`, not at bare `SuTwo`**:
`instNormedAddCommGroupBondFnL2` above is baked with the `Matrix.Norms.L2Operator`-scoped fiber
norm (the only one reachable from inside THIS file); a hypothetical second
`NormedAddCommGroup (BondFnL2 L)` sourced from `SuTwoInner`'s canonical `InnerProductSpace ℝ SuTwo`
(e.g. via Mathlib's generic `PiLp.innerProductSpace`, in a file importing both modules) would be a
REAL top-level-instance collision on `BondFnL2 L` — this is exactly the diamond
`CovariantHj.lean`'s own TIER E note names as blocking `dstarDQuadForm`'s promotion to a
`ContinuousLinearMap`, and it is UNCHANGED by the bare-`SuTwo` fix: closing it still needs the same
import-cycle restructuring (moving `suTwo`'s definition below both files) this docstring already
declined to attempt.~~

**⚠ SUPERSEDED (S75, `compute/norm_diamond/PATCH_SPEC.md`, installed by
`compute/norm_diamond_install/`) — the struck paragraph is retained because it correctly DIAGNOSED
the collision, and struck because its last clause is FALSE.** Closing P3 did not need the
import-cycle restructuring. It needed the **deletion of five lines**, carried out below. Three
measurements, none of which the struck paragraph had:

* the two instances it names had **0 dependents** among 24090 AdalyFormal declarations
  (`compute/norm_diamond/logs/audit5.log`; positive control
  `SuTwoInner.instNormedAddCommGroupSuTwo` = 3092, reaching `AdalyFormal.Spine`) — nothing in the
  tree was ever stated or proved through them, so the restructuring would have been performed to
  make a DEAD instance correct;
* the "hypothetical second `NormedAddCommGroup (BondFnL2 L)`" is **not hypothetical**:
  `Balaban/CoercivityCov.lean:231/235` registers exactly that pair (310 / 574 dependents) on the
  same type via `abbrev AnchoredBondSpaceCov`, and being declared later it already **shadowed** the
  pair above in the 66 modules importing it. The tree was coherent there and incoherent only in the
  21 modules that do not (`compute/norm_diamond/logs/diamond4.log` Q3/Q4/Q7);
* the actual failure mechanism was narrower than "collision": `Norm (BondFnL2 L)` — the slot `‖·‖`
  elaborates through — always resolved to `PiLp.instNorm` at the HILBERT–SCHMIDT fibre, so `‖v‖`
  was **not** the `Norm` component of the registered `NormedAddCommGroup` on the same type. That,
  not an ambiguity between two candidates, is why `ContinuousLinearMap.adjoint` and bare
  `LinearMap.adjoint` failed to unify on this carrier.

The regression pin `SuTwoInner.bondFnL2_norm_is_the_registered_norm` now holds that repaired state
as a kernel-checked invariant, and `SuTwoInner.fibre_norms_agree` /
`SuTwoInner.bondFnL2_norms_agree` prove the deletion changed no real number. -/

/-- **Named, not left implicit** (Defect 2, partial repair): the six `Pi.*` instances above resolve
their `SuTwo` fiber to `Matrix.instL2OpNormedAddCommGroup`
(`Mathlib.Analysis.CStarAlgebra.Matrix`), restricted to the submodule `suTwo` by
`Submodule.normedAddCommGroup` — stated here BY NAME so a reader does not have to reconstruct it
from the bare `open scoped` line above. -/
noncomputable example : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  Matrix.instL2OpNormedAddCommGroup

/-- `PiLp 2` on the bond fibre — a DIFFERENT TYPE from `Bond L → SuTwo`, so this does not touch
`instNormedAddCommGroupBondFn`. Its `NormedAddCommGroup`/`NormedSpace` instances are found by
ordinary (anonymous) typeclass search — exactly the same mechanism `instNormedAddCommGroupBondFn`
already relies on — named here as a distinct, addressable TYPE rather than baked invisibly into a
`Pi` instance. -/
abbrev BondFnL2 (L : PeriodicLatticeExtent) : Type := PiLp 2 (fun _ : Bond L => SuTwo)

/-! **DELETED, deliberately: `instNormedAddCommGroupBondFnL2` / `instNormedSpaceBondFnL2`.**

Both were `inferInstance` elaborated in THIS file's context, where `open scoped
Matrix.Norms.L2Operator` (above) is active and `Balaban/SuTwoInner.lean` is not imported (it imports
this file, so the reverse is a cycle), so their `𝔰𝔲(2)` fibre was the L²-OPERATOR norm. In every
consumer, `Norm (BondFnL2 L)` — the slot `‖·‖` actually elaborates through — resolves to
`PiLp.instNorm` at the HILBERT–SCHMIDT fibre (`SuTwoInner.instNormedAddCommGroupSuTwo`). Registering
these two therefore made `‖v‖` NOT be the `Norm` component of the registered `NormedAddCommGroup`
on the same type, which is why `ContinuousLinearMap.adjoint` and bare `LinearMap.adjoint` did not
unify on this carrier and why `CStarDeltaKCOperator` / `DeltaPrimeOperator` /
`BridgeInverseCarrier` carried 18 `letI` workarounds (all removed in the same pass).

Measured before deletion (`compute/norm_diamond/`, installed by `compute/norm_diamond_install/`):
0 dependents in 24090 AdalyFormal declarations (`logs/audit5.log`, positive control 3092); 0
statements anywhere stated through them (`logs/audit3.log`); every structural slot on `BondFnL2 L`
— `Norm`, `NormedAddCommGroup`, `NormedSpace ℝ`, `InnerProductSpace ℝ`, `MetricSpace`,
`TopologicalSpace`, `CompleteSpace`, `FiniteDimensional ℝ`, `Module ℝ`, `AddCommGroup` — still
synthesizes without them (`logs/diamond3.log` P1). `SuTwoInner.lean` §4e proves the two `𝔰𝔲(2)`
fibre norms are the SAME FUNCTION on all of `𝔰𝔲(2)` (`fibre_norms_agree`) and that the
PiLp-at-operator-fibre and PiLp-at-HS-fibre `Norm` structures on `BondFnL2 L` are the SAME TERM
(`bondFnL2_op_fibre_norm_instances_eq`), so nothing here changes any real number.

`BondFnL2 L` keeps its `NormedAddCommGroup` by ordinary search (`PiLp.normedAddCommGroup` at the HS
fibre); **do NOT re-register one here.** The regression pin that fails the moment anyone does is
`SuTwoInner.bondFnL2_norm_is_the_registered_norm`. -/

/-! ### The falsifiability pin: SUP and `L²` genuinely disagree, on a concrete witness -/

/-- Two distinct bonds of the shared witness lattice (base site `AdmissibleSubspace.witnessY`,
directions `0` and `1`) — reused, not a new witness lattice invented (LAW-19). -/
def l2WitnessBond0 : Bond AdmissibleSubspace.witnessL := (AdmissibleSubspace.witnessY, (0 : Fin 3))

def l2WitnessBond1 : Bond AdmissibleSubspace.witnessL := (AdmissibleSubspace.witnessY, (1 : Fin 3))

theorem l2WitnessBond0_ne_l2WitnessBond1 : l2WitnessBond0 ≠ l2WitnessBond1 := by decide

/-- The two-bond spike configuration: `suTwoWitness` on both `l2WitnessBond0`/`l2WitnessBond1`,
zero elsewhere. -/
noncomputable def l2WitnessConfig : Bond AdmissibleSubspace.witnessL → SuTwo :=
  fun e => if e = l2WitnessBond0 then suTwoWitness
    else if e = l2WitnessBond1 then suTwoWitness else 0

theorem l2WitnessConfig_at_bond0 : l2WitnessConfig l2WitnessBond0 = suTwoWitness := by
  simp [l2WitnessConfig]

theorem l2WitnessConfig_at_bond1 : l2WitnessConfig l2WitnessBond1 = suTwoWitness := by
  simp [l2WitnessConfig]

theorem l2WitnessConfig_elsewhere {e : Bond AdmissibleSubspace.witnessL}
    (h0 : e ≠ l2WitnessBond0) (h1 : e ≠ l2WitnessBond1) : l2WitnessConfig e = 0 := by
  simp [l2WitnessConfig, h0, h1]

/-- **The SUP-side value**: `‖l2WitnessConfig‖ = ‖suTwoWitness‖` under
`instNormedAddCommGroupBondFn` — the two-spike configuration reports the SAME norm as a single
spike, the defining feature of the sup convention. -/
theorem l2WitnessConfig_sup_norm : ‖l2WitnessConfig‖ = ‖suTwoWitness‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg suTwoWitness)).2 ?_
    intro e
    by_cases h0 : e = l2WitnessBond0
    · rw [h0, l2WitnessConfig_at_bond0]
    · by_cases h1 : e = l2WitnessBond1
      · rw [h1, l2WitnessConfig_at_bond1]
      · rw [l2WitnessConfig_elsewhere h0 h1]; simp
  · have := norm_le_pi_norm l2WitnessConfig l2WitnessBond0
    rwa [l2WitnessConfig_at_bond0] at this

/-- **The `L²`-side value**: the SAME underlying data, read through `PiLp 2` instead, reports
`2‖suTwoWitness‖²` for the norm SQUARED — CMP99b's own quadratic form on a two-bond
configuration. -/
theorem l2WitnessConfig_l2_normSq :
    ‖(WithLp.toLp 2 l2WitnessConfig : BondFnL2 AdmissibleSubspace.witnessL)‖ ^ 2 =
      2 * ‖suTwoWitness‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hpt : ∀ e : Bond AdmissibleSubspace.witnessL,
      ‖(WithLp.toLp 2 l2WitnessConfig : BondFnL2 AdmissibleSubspace.witnessL) e‖ ^ 2 =
        (if e = l2WitnessBond0 then ‖suTwoWitness‖ ^ 2 else 0) +
          (if e = l2WitnessBond1 then ‖suTwoWitness‖ ^ 2 else 0) := by
    intro e
    by_cases h0 : e = l2WitnessBond0
    · subst h0
      simp [l2WitnessConfig_at_bond0, l2WitnessBond0_ne_l2WitnessBond1]
    · by_cases h1 : e = l2WitnessBond1
      · subst h1
        simp [l2WitnessConfig_at_bond1, Ne.symm l2WitnessBond0_ne_l2WitnessBond1]
      · simp [l2WitnessConfig_elsewhere h0 h1, h0, h1]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ l2WitnessBond0
      (fun _ => ‖suTwoWitness‖ ^ 2),
    Finset.sum_ite_eq' Finset.univ l2WitnessBond1 (fun _ => ‖suTwoWitness‖ ^ 2)]
  simp
  ring

/-- **DEFECT 1's HEADLINE PIN**: the SUP norm (`instNormedAddCommGroupBondFn`, currently the ONLY
norm exported for `Bond L → SuTwo`) and the `L²` norm (`BondFnL2`, this section's repair) report
GENUINELY DIFFERENT numbers on the SAME underlying configuration. Reading a quadratic form off the
sup instance is provably wrong, not merely "a different but equally valid convention." Falsifiable
by construction: delete this section's `PiLp 2` repair and the very STATEMENT below stops
typechecking (the two `‖·‖`s no longer even have a shared alternative to disagree with) — the
strongest form of "make it fail, don't assert it would" available for an ADDITIVE repair. -/
theorem sup_ne_l2_norm_on_witness :
    ‖l2WitnessConfig‖ ≠ ‖(WithLp.toLp 2 l2WitnessConfig : BondFnL2 AdmissibleSubspace.witnessL)‖ := by
  intro heq
  have hsup : ‖l2WitnessConfig‖ = ‖suTwoWitness‖ := l2WitnessConfig_sup_norm
  have hl2sq : ‖(WithLp.toLp 2 l2WitnessConfig : BondFnL2 AdmissibleSubspace.witnessL)‖ ^ 2 =
      2 * ‖suTwoWitness‖ ^ 2 := l2WitnessConfig_l2_normSq
  rw [← heq, hsup] at hl2sq
  have hpos : 0 < ‖suTwoWitness‖ := norm_pos_iff.mpr suTwoWitness_ne_zero
  nlinarith [hpos]

#print axioms l2WitnessBond0_ne_l2WitnessBond1
#print axioms l2WitnessConfig_at_bond0
#print axioms l2WitnessConfig_at_bond1
#print axioms l2WitnessConfig_elsewhere
#print axioms l2WitnessConfig_sup_norm
#print axioms l2WitnessConfig_l2_normSq
#print axioms sup_ne_l2_norm_on_witness

/-! ## Axiom audit (L8/gate stage: every load-bearing declaration, printed for the mandate's
"verify by direct `lake env lean`" instruction) -/

#print axioms suTwoWitnessVal_mem
#print axioms suTwoWitnessVal_ne_zero
#print axioms suTwoWitnessVal_ne_neg_self
#print axioms garbageNotSkewHermitian_not_mem
#print axioms garbageNotTraceless_not_mem
#print axioms conjByAmbient_mem
#print axioms RMap_one
#print axioms RMap_mul
#print axioms RMap_mul_apply
#print axioms curlValueCovariant_gradValueCovariant
#print axioms witnessM_mem
#print axioms witnessM_mem_suTwo
#print axioms RMap_witnessMElem
#print axioms garbageLeftMul_witnessM_not_mem
#print axioms witness_curvature_ne_zero
#print axioms RCLM_coe_apply
#print axioms gradCovariantCLM_apply
#print axioms curlCovariantCLM_apply

end AdalyFormal.Balaban.CovariantOperators
