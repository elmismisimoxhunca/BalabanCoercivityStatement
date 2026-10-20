/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Coercivity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

/-!
# Wall-prover dispatch, `[LEM-COERC-U]` at unrestricted `U` — `compute/coerc_u_large_field_kill/`

**Outcome: SURVIVES (the true bound, as far as this dispatch's arsenal reaches) + one STRUCTURAL
OBSTRUCTION to a NAMED CLASS of candidate `Δ` constructions.** Full numerical record and the two
distinct-angle attacks that did NOT produce a witness (center-blindness, RG-shrinking-radius) are
in `compute/coerc_u_large_field_kill/LARGE_FIELD_KILL_ATTEMPT.md`. This file formalizes the ONE
attack that produced a clean, general, kernel-checkable fact — proved here, not asserted.

## What is proved, precisely

`compute/coerc_u_large_field_kill/numerics/large_field_search_periodic.py` builds a covariant
lattice curl `C : (bonds) → (plaquettes)` on a small periodic 3D SU(2)-adjoint (SO(3)) lattice and
finds, numerically, that `⟨v, Δv⟩ := ‖Cv‖²` restricted to CMP96 `(2.121)`'s admissible subspace `V`
(a FIXED, O(1), scale-independent Dirichlet path) is **exactly degenerate (a genuine zero, not
merely small) at every FLAT/pure-gauge background tested**, because `V`'s tiny fixed codimension is
nowhere near enough to kill the much larger (order-lattice-size) pure-gauge/coboundary kernel of a
bare, `H_j`-free curl. This module proves the GENERAL abstract fact underlying that numerical
finding: **whenever `Δ k U` is built as a bare rank-bounded pullback `v ↦ ‖C v‖²` for some linear
`C` into a space of dimension SMALLER than `V`'s, `Balaban.CoercivityHypothesis` cannot hold — for
ANY `U`, ANY `γ'' > 0`.** This is a class-level obstruction to the "no `H_j`" reading of `Δ_k(U)`,
not a claim that the TRUE bound (which needs `H_j`, unbuilt in this tree — `RGLinearization.lean`'s
own dependency chain, items 4–6) is false. Read the docstring of `CoercivityHypothesis` (`Balaban/
Coercivity.lean`) alongside this: this module gives the PRECISE reason `Δ`'s "coercive" field, taken
in ISOLATION as a bare bilinear form (already flagged there as a "NAMED, DISCLOSED SIMPLIFICATION"
relative to CMP96 `(2.122)`'s three-term sum), can never be proved as stated without either
building `H_j` or restoring the other two terms of `(2.120)`.
-/

namespace AdalyFormal.HoleHunt.LargeFieldKill

open AdalyFormal.Balaban

/-! ## §1 — the abstract obstruction: rank-nullity applied to a submodule -/

/-- **Any linear map into a strictly lower-dimensional target has a nonzero kernel vector inside
ANY submodule whose own dimension already exceeds the target's.** Pure rank-nullity
(`LinearMap.ker_ne_bot_of_finrank_lt`, restricted to `V` via `V.subtype`), stated on the submodule
directly so it composes with `CoercivityHypothesis.V` with no adapter. -/
theorem exists_nonzero_kernel_vector_in_submodule
    {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (V : Submodule ℝ H) (C : H →ₗ[ℝ] W)
    (hdim : Module.finrank ℝ W < Module.finrank ℝ V) :
    ∃ v ∈ V, v ≠ 0 ∧ C v = 0 := by
  set f : V →ₗ[ℝ] W := C ∘ₗ V.subtype with hf
  have hVfr : Module.finrank ℝ V = Module.finrank ℝ ↥V := rfl
  have hlt : Module.finrank ℝ W < Module.finrank ℝ (↥V) := by
    rw [← hVfr]; exact hdim
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨(x : H), x.2, ?_, ?_⟩
  · intro hveq
    exact hx0 (Subtype.ext hveq)
  · have : f x = 0 := hx
    simpa [hf] using this

/-! ## §2 — the class-level obstruction to `CoercivityHypothesis` -/

/-- **STRUCTURAL OBSTRUCTION.** If `Δ k U` is a bare rank-bounded pullback `v ↦ ⟨v, Δ v⟩ = ‖C v‖²`
for a linear `C : H →ₗ[ℝ] W` with `finrank W < finrank V`, no term of `CoercivityHypothesis H
Uconfig` can have that `Δ` at that `(k, U)` — for ANY `γ'' > 0`. This is the exact mechanism the
periodic-lattice numerics exhibit: `C` = the covariant curl, `W` = plaquette space, `V` = CMP96
`(2.121)`'s admissible subspace, and `finrank W < finrank V` holds on every periodic lattice size
tested (`dimV`/`dim_target` in `large_field_search_periodic_results` — recorded in
`LARGE_FIELD_KILL_ATTEMPT.md` — nonetheless gave `gamma_flat_U1 ≈ 0`, confirming the dimension
inequality ALONE is not even the binding constraint at flat backgrounds; the coboundary/pure-gauge
kernel is what actually saturates it. This theorem covers the WEAKER, purely-linear-algebraic
special case of that finding — the part provable with zero lattice geometry.) -/
theorem no_coercivityHypothesis_from_bounded_rank_pullback
    {H W Uconfig : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [Nontrivial Uconfig]
    (h : CoercivityHypothesis H Uconfig) (k : ℕ) (U : Uconfig)
    (C : H →ₗ[ℝ] W) (hΔ : ∀ v, inner ℝ v (h.Δ k U v) = (‖C v‖ : ℝ) ^ 2)
    (hdim : Module.finrank ℝ W < Module.finrank ℝ h.V) : False := by
  obtain ⟨v, hvV, hv0, hCv⟩ := exists_nonzero_kernel_vector_in_submodule h.V C hdim
  have hcoerc := h.coercive k U v hvV
  rw [hΔ v, hCv] at hcoerc
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hcoerc
  have hvpos : 0 < ‖v‖ ^ 2 := by positivity
  have : h.γ'' * ‖v‖ ^ 2 ≤ 0 := hcoerc
  nlinarith [h.γ''_pos]

/-! ## §3 — non-vacuity: the hypotheses (`W`, `V`, `C`, the dimension inequality) are jointly
satisfiable, so §2 is not vacuously true of an empty parameter space (L7). A concrete finite-dim
witness, `H = ℝ³`, `V = ⊤` (finrank 3), `W = ℝ` (finrank 1) via the zero map -- the SMALLEST
instance exhibiting `finrank W < finrank V` with a genuine linear `C`. -/

abbrev WitnessH : Type := EuclideanSpace ℝ (Fin 3)
abbrev WitnessW : Type := EuclideanSpace ℝ (Fin 1)

theorem witness_dim_inequality :
    Module.finrank ℝ WitnessW < Module.finrank ℝ (⊤ : Submodule ℝ WitnessH) := by
  simp [WitnessH, WitnessW]

/-- The zero map witnesses `C` concretely (any `C` works for the dimension-count lemma; the zero
map is the simplest term of the right type, confirming the HYPOTHESIS SHAPE is inhabited, not that
this is claimed to be the campaign's actual curl operator). -/
theorem witness_exists_nonzero_kernel_vector :
    ∃ v ∈ (⊤ : Submodule ℝ WitnessH), v ≠ 0 ∧ (0 : WitnessH →ₗ[ℝ] WitnessW) v = 0 :=
  exists_nonzero_kernel_vector_in_submodule ⊤ 0 witness_dim_inequality

end AdalyFormal.HoleHunt.LargeFieldKill

#print axioms AdalyFormal.HoleHunt.LargeFieldKill.exists_nonzero_kernel_vector_in_submodule
#print axioms AdalyFormal.HoleHunt.LargeFieldKill.no_coercivityHypothesis_from_bounded_rank_pullback
#print axioms AdalyFormal.HoleHunt.LargeFieldKill.witness_dim_inequality
#print axioms AdalyFormal.HoleHunt.LargeFieldKill.witness_exists_nonzero_kernel_vector
