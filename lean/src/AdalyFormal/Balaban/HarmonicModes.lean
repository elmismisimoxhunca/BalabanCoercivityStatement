/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.LatticeOperators
import AdalyFormal.Balaban.CoercivityCov
import AdalyFormal.Balaban.CovariantHjMinimizer
import AdalyFormal.Balaban.BondSU2Space
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# Does `admissibleSubspace`/`admissibleSubspaceCov`'s staircase condition exclude the harmonic
/topological zero-curl modes a numerical experiment found on the periodic torus?

**Dispatch: settle the ONE question deciding whether `CMP96 (2.121)`'s axis-anchored subspace
survives `compute/hj_largelattice/`'s obstruction** (gauge-invariance-verified, drift `~1e-14`):
`H_j` quantitatively repairs the counting obstruction on generic backgrounds, but a background
trivial except on ONE bond drives the coercivity constant to EXACT ZERO, with the minimizing mode
traced to a genuine harmonic/topological zero-curl mode (curl-kernel dimension exceeds
`image(grad)`'s by exactly `3`, the number of independent cycles on `T³`) — NOT the measure-zero
"constant gauge function"/`U ≡ 1` degeneracy already on record. This file settles, IN LEAN, whether
`admissibleSubspace`/`admissibleSubspaceCov`/`anchoredVCov` (`AdmissibleSubspace.lean`,
`CoercivityCov.lean`) exclude these modes.

## VERDICT, stated up front: **PARTIAL, with an EXACT count — for a SINGLE `(y,x)` pair, the
staircase excludes the harmonic mode in a cycle direction `μ` IFF `y μ ≠ x μ`; it ADMITS the
harmonic mode in every direction where `y μ = x μ`.**

Since `staircasePath y x` (`AdmissibleSubspace.lean` §3) is built from exactly THREE axis-parallel
segments, one per coordinate direction, each segment's bond set is EMPTY precisely when `y` and `x`
already agree in that coordinate (`min = max`, an empty half-open range) — §3 below proves this in
general, for ANY periodic extent `L`, not merely the campaign's `witnessL`. Consequently, for a
FIXED pair `(y,x)` with `x ∈ blockOf y ell` (`admissibleSubspace`'s own antecedents), the winding
mode `windingMode L μ` — the exact object the numerics found, "constant along one cycle direction
and zero elsewhere" — is admissible (`B(b) = 0` on `Γ_{y,x}`) EXACTLY in the directions where `y`
and `x` coincide, and excluded in the directions where they differ. On the campaign's own witness
lattice (`AdmissibleSubspace.witnessY = (0,0,0)`, `witnessX = (1,0,1)`), this is `1` admitted
direction (`μ = 1`, since `witnessY 1 = witnessX 1 = 0`) out of `3` — §6 verifies this concretely,
`decide`-checked in both directions.

**This is not the `U ≡ 1`/central-`U` degeneracy already on record.** The winding mode is built and
shown curl-free (harmonic) and NOT in the image of the gradient (topologically nontrivial — a
genuine nonzero class in the discrete `H¹(T³) ≅ ℝ³`) for BOTH the flat/abelian complex
(`LatticeOperators.curlValue`/`gradValue`) AND the `𝔰𝔲(2)`-covariant complex AT THE TRIVIAL
BACKGROUND (`CovariantOperators.curlValueCovariant`/`gradValueCovariant (trivialU L)`, where
`RMap 1 = LinearMap.id` collapses the covariant complex to the same combinatorics) — §2/§4 below,
generic in the lattice size, not a small-lattice artifact.

## Relation to the ALREADY-BANKED `ForcedIntersection.lean` refutation

`ForcedIntersection.lean` already refutes `SpineCovariant.oneScaleCoercivity_su2` at the WITNESS
lattice via ABSTRACT dimension-counting (rank-nullity forces SOME nonzero vector in
`anchoredVCov ⊓ ker(D⁰_U(D⁰_U)^*)`), for the operator `BondSU2Space.bondLaplacianCovCLM_L2` — which
that file's own docstring identifies as `D⁰_U ∘ (D⁰_U)^*`, built from the DEGREE-0 gradient, NOT the
degree-1 CURL (`CovariantHj.dstarDQuadForm`/`curlCovariantCLM`) that `H_j`/the numerics actually
target; that file explicitly discloses the curl-based operator as "NOT checked here."

**This file complements it with the operator that IS the numerically-relevant one.** §7 below
assembles: `windingModeCov L μ` is (a) nonzero, (b) admissible whenever `y μ = x μ`, for EVERY
lattice size and EVERY such pair (not one dimension-counted witness), and (c) killed EXACTLY by the
CURL operator (`curlValueCovariant (trivialU L) (windingModeCov L μ) = 0` identically). So any
future coercivity bound of the shape `γ‖B‖² ≤ ⟨B, curl^*curl B⟩` on `admissibleSubspaceCov`/
`anchoredVCov` for a fixed `(y,x)` pair sharing a coordinate is refuted BY THIS SAME MECHANISM,
independent of lattice size — a GEOMETRIC/TOPOLOGICAL obstruction, not merely a dimension-counting
artifact of one small lattice. `curlValueCovariant`/`bondLaplacianCovCLM_L2` are, per
`SpineCovariant.lean`'s own disclosure, two DIFFERENT pieces of a Hodge-type decomposition
(degree-1 vs degree-0), so this is a genuinely NEW obstruction, not a re-derivation of
`ForcedIntersection.lean`'s.

## Named residual, precisely

**Not attempted here**: whether SOME OTHER admissible-subspace construction (e.g. intersecting
`admissibleSubspace y x ell hy hx` over EVERY valid `(y,x)` pair simultaneously, or CMP99b `(3.156)`'s
own three-condition subspace — `CoercivityCov.lean`'s own disclosed, not-yet-reconciled alternative)
would exclude these modes. The mechanism identified here (§3) shows PRECISELY what such a repair
would need: enough `(y,x)` pairs, or an additional condition, so that EVERY cycle direction is
covered by SOME excluding segment — the staircase for a SINGLE pair structurally cannot do this
alone, since it has only `3` segments (one per direction) and excludes a direction's winding mode
`iff` its own two endpoints differ in that coordinate.
-/

namespace AdalyFormal.Balaban.HarmonicModes

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CoercivityCov
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

variable {L : PeriodicLatticeExtent}

/-! ## §1. The winding mode — "constant along one cycle direction, zero elsewhere" -/

/-- **The flat/abelian winding mode**, direction `μ0`: `1` on every bond of direction `μ0`
(regardless of base site), `0` on every other bond. This is the exact object the numerics found
("a field constant along one cycle direction and zero elsewhere"). -/
def windingMode (L : PeriodicLatticeExtent) (μ0 : Fin 3) : Bond L → ℝ :=
  fun b => if b.2 = μ0 then 1 else 0

/-- **The `𝔰𝔲(2)`-valued analogue**, using the already-proved nonzero Lie-algebra element
`CovariantOperators.suTwoWitness` (LAW-19 reuse) in place of the scalar `1`. -/
noncomputable def windingModeCov (L : PeriodicLatticeExtent) (μ0 : Fin 3) : Bond L → SuTwo :=
  fun b => if b.2 = μ0 then suTwoWitness else 0

/-- A concrete inhabitant of `PeriodicLatticeSite L`, used only to exhibit nonzero-ness / as the
telescoping argument's base point. -/
def anySite (L : PeriodicLatticeExtent) : PeriodicLatticeSite L := fun μ => ⟨0, by omega⟩

theorem windingMode_ne_zero (L : PeriodicLatticeExtent) (μ0 : Fin 3) : windingMode L μ0 ≠ 0 := by
  intro h
  have := congrFun h (anySite L, μ0)
  simp [windingMode] at this

theorem windingModeCov_ne_zero (L : PeriodicLatticeExtent) (μ0 : Fin 3) :
    windingModeCov L μ0 ≠ 0 := by
  intro h
  have hc := congrFun h (anySite L, μ0)
  simp only [windingModeCov, Pi.zero_apply] at hc
  exact suTwoWitness_ne_zero hc

#print axioms windingMode_ne_zero
#print axioms windingModeCov_ne_zero

/-! ## §2. Harmonicity — curl-freeness, for both the flat complex and the covariant complex at the
trivial background `trivialU L` (`RMap 1 = LinearMap.id`, `CovariantOperators.RMap_one`) -/

theorem curlValue_windingMode_eq_zero (L : PeriodicLatticeExtent) (μ0 : Fin 3)
    (p : PeriodicLatticePlaquette L) :
    curlValue (windingMode L μ0) p = 0 := by
  simp only [curlValue, windingMode]
  ring

theorem curlValueCovariant_trivialU_windingModeCov_eq_zero (L : PeriodicLatticeExtent)
    (μ0 : Fin 3) (p : PeriodicLatticePlaquette L) :
    curlValueCovariant (trivialU L) (windingModeCov L μ0) p = 0 := by
  have h1 : RMap (trivialU L (p.1, p.2.1.1)) = LinearMap.id := by
    show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = LinearMap.id
    exact RMap_one
  have h2 : RMap (trivialU L (p.1, p.2.1.2)) = LinearMap.id := by
    show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = LinearMap.id
    exact RMap_one
  simp only [curlValueCovariant, windingModeCov, h1, h2, LinearMap.id_apply]
  abel

#print axioms curlValue_windingMode_eq_zero
#print axioms curlValueCovariant_trivialU_windingModeCov_eq_zero

/-! ## §3. Non-exactness — topological nontriviality: the winding mode is NOT in the image of the
gradient, for ANY periodic extent `L` (not lattice-size-tied). A single generic telescoping/cyclic
-sum argument, instantiated once at `V := ℝ` (flat) and once at `V := SuTwo` (covariant, at
`trivialU`). -/

/-- **The generic obstruction.** If `D` behaves like a genuine site-to-bond gradient
(`D lam b = lam(shift b) - lam(b.1)`, `hD`), then `D` can never hit the winding configuration
`fun b => if b.2 = μ0 then v else 0` for a NONZERO `v` — summing the defining equation around the
full periodic cycle in direction `μ0` telescopes to `0` on one side (`Equiv.sum_comp` along
`finRotate`, a genuine bijection, not an approximation) and to `(L μ0 + 1) • v` on the other,
forcing `v = 0` since `L μ0 + 1 ≠ 0`. This is the Lean-checked form of "the winding number of a
nonzero constant-along-a-cycle field is nonzero." -/
theorem windingLike_not_mem_range {V : Type*} [AddCommGroup V] [Module ℝ V]
    [NoZeroSMulDivisors ℝ V] {L : PeriodicLatticeExtent} (μ0 : Fin 3) (v : V) (hv : v ≠ 0)
    (D : (PeriodicLatticeSite L → V) → (Bond L → V))
    (hD : ∀ lam b, D lam b = lam (periodicLatticeShift b.1 b.2) - lam b.1) :
    ¬ ∃ lam : PeriodicLatticeSite L → V, D lam = (fun b => if b.2 = μ0 then v else 0) := by
  rintro ⟨lam, hlam⟩
  set x0 : PeriodicLatticeSite L := fun μ => (⟨0, by omega⟩ : Fin (L μ + 1)) with hx0def
  have hstep : ∀ k : Fin (L μ0 + 1),
      lam (Function.update x0 μ0 (k + 1)) - lam (Function.update x0 μ0 k) = v := by
    intro k
    have hb0 : D lam (Function.update x0 μ0 k, μ0) = v := by
      have hc := congrFun hlam (Function.update x0 μ0 k, μ0)
      simpa using hc
    rw [hD lam (Function.update x0 μ0 k, μ0)] at hb0
    have hshift : periodicLatticeShift (Function.update x0 μ0 k) μ0 =
        Function.update x0 μ0 (k + 1) := by
      show Function.update (Function.update x0 μ0 k) μ0
          (Function.update x0 μ0 k μ0 + 1) = Function.update x0 μ0 (k + 1)
      rw [Function.update_self]
      exact Function.update_idem _ _ _
    rw [hshift] at hb0
    exact hb0
  have hsum1 : ∑ k : Fin (L μ0 + 1),
      (lam (Function.update x0 μ0 (k + 1)) - lam (Function.update x0 μ0 k)) =
      ∑ _k : Fin (L μ0 + 1), v :=
    Finset.sum_congr rfl (fun k _ => hstep k)
  have hsum2 : ∑ k : Fin (L μ0 + 1), lam (Function.update x0 μ0 (k + 1)) =
      ∑ k : Fin (L μ0 + 1), lam (Function.update x0 μ0 k) := by
    have hrot := Equiv.sum_comp (finRotate (L μ0 + 1))
      (fun k => lam (Function.update x0 μ0 k))
    simpa [finRotate_apply] using hrot
  have hzero : ∑ k : Fin (L μ0 + 1),
      (lam (Function.update x0 μ0 (k + 1)) - lam (Function.update x0 μ0 k)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum2, sub_self]
  rw [hzero] at hsum1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum1
  have hcast : ((L μ0 + 1 : ℕ) : ℝ) • v = (L μ0 + 1) • v := Nat.cast_smul_eq_nsmul ℝ (L μ0 + 1) v
  rw [← hcast] at hsum1
  have hpos : (0 : ℝ) < ((L μ0 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (L μ0)
  rcases smul_eq_zero.mp hsum1.symm with h1 | h1
  · exact hpos.ne' h1
  · exact hv h1

#print axioms windingLike_not_mem_range

/-- **The flat/abelian instantiation.** -/
theorem windingMode_not_mem_range_gradValue (L : PeriodicLatticeExtent) (μ0 : Fin 3) :
    ¬ ∃ lam : PeriodicLatticeSite L → ℝ, gradValue lam = windingMode L μ0 :=
  windingLike_not_mem_range μ0 (1 : ℝ) one_ne_zero gradValue (fun _ _ => rfl)

/-- **The covariant instantiation, at the trivial background.** `gradValueCovariant (trivialU L)`
genuinely reduces to a bare site-to-bond gradient once `RMap 1 = LinearMap.id` collapses the
transport factor (`hD_cov` below), so the SAME generic obstruction applies with `V := SuTwo`. -/
theorem windingModeCov_not_mem_range_gradValueCovariant (L : PeriodicLatticeExtent) (μ0 : Fin 3) :
    ¬ ∃ lam : PeriodicLatticeSite L → SuTwo,
        gradValueCovariant (trivialU L) lam = windingModeCov L μ0 := by
  have hD_cov : ∀ (lam : PeriodicLatticeSite L → SuTwo) (b : Bond L),
      gradValueCovariant (trivialU L) lam b =
        lam (periodicLatticeShift b.1 b.2) - lam b.1 := by
    intro lam b
    show RMap (trivialU L b) (lam (periodicLatticeShift b.1 b.2)) - lam b.1 = _
    have hR : RMap (trivialU L b) = LinearMap.id := by
      show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = LinearMap.id
      exact RMap_one
    rw [hR, LinearMap.id_apply]
  exact windingLike_not_mem_range μ0 suTwoWitness suTwoWitness_ne_zero
    (gradValueCovariant (trivialU L)) hD_cov

#print axioms windingMode_not_mem_range_gradValue
#print axioms windingModeCov_not_mem_range_gradValueCovariant

/-! ## §4. THE MECHANISM — a single `(y,x)` pair's staircase has an empty direction-`μ0` segment
EXACTLY when `y μ0 = x μ0`, for ANY periodic extent `L` -/

/-- **The key combinatorial fact.** If `y` and `x` already agree in coordinate `μ0`, NO bond of the
staircase `Γ_{y,x}` has direction `μ0` — each of the THREE segments only ever contributes bonds of
its OWN fixed direction (`2`, `1`, `0` respectively), and the one that COULD contribute direction
-`μ0` bonds has an EMPTY range (`min = max`) exactly when `y μ0 = x μ0`. General in `L`, `y`, `x` —
not tied to the witness lattice. -/
theorem staircasePath_dir_ne_of_eq {L : PeriodicLatticeExtent} (y x : PeriodicLatticeSite L)
    (μ0 : Fin 3) (heq : y μ0 = x μ0) (b : Bond L) (hb : b ∈ staircasePath y x) :
    b.2 ≠ μ0 := by
  simp only [staircasePath, Finset.mem_union] at hb
  rcases hb with (hseg | hseg) | hseg
  · rw [mem_axisSegment] at hseg
    obtain ⟨hdir, -, ha, hlt⟩ := hseg
    intro hcontra
    have h2 : (2 : Fin 3) = μ0 := hdir ▸ hcontra
    rw [← h2] at heq
    have hval : (y 2).val = (x 2).val := congrArg Fin.val heq
    rw [hval, min_self] at ha
    rw [hval, max_self] at hlt
    omega
  · rw [mem_axisSegment] at hseg
    obtain ⟨hdir, -, ha, hlt⟩ := hseg
    intro hcontra
    have h1 : (1 : Fin 3) = μ0 := hdir ▸ hcontra
    rw [← h1] at heq
    have hval : (y 1).val = (x 1).val := congrArg Fin.val heq
    rw [hval, min_self] at ha
    rw [hval, max_self] at hlt
    omega
  · rw [mem_axisSegment] at hseg
    obtain ⟨hdir, -, ha, hlt⟩ := hseg
    intro hcontra
    have h0 : (0 : Fin 3) = μ0 := hdir ▸ hcontra
    rw [← h0] at heq
    have hval : (y 0).val = (x 0).val := congrArg Fin.val heq
    rw [hval, min_self] at ha
    rw [hval, max_self] at hlt
    omega

#print axioms staircasePath_dir_ne_of_eq

/-- **THE CONVERSE, ALSO GENERAL (nested-verifier repair — the original draft of this file proved
this direction only concretely at the witness lattice, which understated what actually holds; this
is now a real theorem for ANY `L`, `y`, `x`).** Whenever `y` and `x` DIFFER in coordinate `μ0`, the
staircase `Γ_{y,x}` DOES contain a bond of direction `μ0` — the segment for that direction has a
genuinely nonempty range `[min(y μ0,x μ0), max(y μ0,x μ0))`, and its own left endpoint is always a
member. This completes `staircasePath_dir_ne_of_eq` into a full "iff": `Γ_{y,x}` contains a
direction-`μ0` bond IFF `y μ0 ≠ x μ0`, for every periodic extent `L`. -/
theorem staircasePath_exists_dir_of_ne {L : PeriodicLatticeExtent} (y x : PeriodicLatticeSite L)
    (μ0 : Fin 3) (hne : y μ0 ≠ x μ0) : ∃ b ∈ staircasePath y x, b.2 = μ0 := by
  fin_cases μ0
  · -- `fin_cases` enumerates `Fin 3` in order `0, 1, 2` — this bullet is `μ0 = 0`.
    have hval : (y 0).val ≠ (x 0).val := fun h => hne (Fin.ext h)
    have hlt0 : min (y 0).val (x 0).val < L 0 + 1 := by
      have := (y 0).isLt; have := (x 0).isLt; omega
    refine ⟨(Function.update (corner2 y x) 0 ⟨min (y 0).val (x 0).val, hlt0⟩, 0), ?_, rfl⟩
    simp only [staircasePath, Finset.mem_union]
    refine Or.inr ?_
    rw [mem_axisSegment]
    refine ⟨rfl, fun ν hν => Function.update_of_ne hν _ (corner2 y x), ?_, ?_⟩
    · show min (y 0).val (x 0).val ≤
        (Function.update (corner2 y x) 0 ⟨min (y 0).val (x 0).val, hlt0⟩ 0).val
      rw [Function.update_self]
    · show (Function.update (corner2 y x) 0 ⟨min (y 0).val (x 0).val, hlt0⟩ 0).val <
        max (y 0).val (x 0).val
      rw [Function.update_self]
      show min (y 0).val (x 0).val < max (y 0).val (x 0).val
      omega
  · -- `μ0 = 1`.
    have hval : (y 1).val ≠ (x 1).val := fun h => hne (Fin.ext h)
    have hlt1 : min (y 1).val (x 1).val < L 1 + 1 := by
      have := (y 1).isLt; have := (x 1).isLt; omega
    refine ⟨(Function.update (corner1 y x) 1 ⟨min (y 1).val (x 1).val, hlt1⟩, 1), ?_, rfl⟩
    simp only [staircasePath, Finset.mem_union]
    refine Or.inl (Or.inr ?_)
    rw [mem_axisSegment]
    refine ⟨rfl, fun ν hν => Function.update_of_ne hν _ (corner1 y x), ?_, ?_⟩
    · show min (y 1).val (x 1).val ≤
        (Function.update (corner1 y x) 1 ⟨min (y 1).val (x 1).val, hlt1⟩ 1).val
      rw [Function.update_self]
    · show (Function.update (corner1 y x) 1 ⟨min (y 1).val (x 1).val, hlt1⟩ 1).val <
        max (y 1).val (x 1).val
      rw [Function.update_self]
      show min (y 1).val (x 1).val < max (y 1).val (x 1).val
      omega
  · -- `μ0 = 2`.
    have hval : (y 2).val ≠ (x 2).val := fun h => hne (Fin.ext h)
    have hlt2 : min (y 2).val (x 2).val < L 2 + 1 := by
      have := (y 2).isLt; have := (x 2).isLt; omega
    refine ⟨(Function.update y 2 ⟨min (y 2).val (x 2).val, hlt2⟩, 2), ?_, rfl⟩
    simp only [staircasePath, Finset.mem_union]
    refine Or.inl (Or.inl ?_)
    rw [mem_axisSegment]
    refine ⟨rfl, fun ν hν => Function.update_of_ne hν _ y, ?_, ?_⟩
    · show min (y 2).val (x 2).val ≤ (Function.update y 2 ⟨min (y 2).val (x 2).val, hlt2⟩ 2).val
      rw [Function.update_self]
    · show (Function.update y 2 ⟨min (y 2).val (x 2).val, hlt2⟩ 2).val < max (y 2).val (x 2).val
      rw [Function.update_self]
      show min (y 2).val (x 2).val < max (y 2).val (x 2).val
      omega

#print axioms staircasePath_exists_dir_of_ne

/-- **EXCLUDED, general (closes the gap the nested verifier found).** Whenever `y` and `x` differ in
coordinate `μ0`, the winding mode in direction `μ0` is NOT admissible — for ANY `L`, `ell`, `y`, `x`,
not merely the witness lattice's two concrete directions. -/
theorem windingMode_not_mem_admissibleSubspace_of_ne {L : PeriodicLatticeExtent}
    (y x : PeriodicLatticeSite L) (ell : ℕ) (hy : y ∈ CoarseLattice L ell)
    (hx : x ∈ blockOf y ell) (μ0 : Fin 3) (hne : y μ0 ≠ x μ0) :
    windingMode L μ0 ∉ admissibleSubspace y x ell hy hx := by
  rw [mem_admissibleSubspace]
  intro hmem
  obtain ⟨b, hb, hbdir⟩ := staircasePath_exists_dir_of_ne y x μ0 hne
  have hzero := hmem b hb
  rw [windingMode, if_pos hbdir] at hzero
  exact one_ne_zero hzero

/-- **Same fact, `𝔰𝔲(2)`-valued.** -/
theorem windingModeCov_not_mem_admissibleSubspaceCov_of_ne {L : PeriodicLatticeExtent}
    (y x : PeriodicLatticeSite L) (ell : ℕ) (hy : y ∈ CoarseLattice L ell)
    (hx : x ∈ blockOf y ell) (μ0 : Fin 3) (hne : y μ0 ≠ x μ0) :
    windingModeCov L μ0 ∉ admissibleSubspaceCov y x ell hy hx := by
  rw [mem_admissibleSubspaceCov]
  intro hmem
  obtain ⟨b, hb, hbdir⟩ := staircasePath_exists_dir_of_ne y x μ0 hne
  have hzero := hmem b hb
  rw [windingModeCov, if_pos hbdir] at hzero
  exact suTwoWitness_ne_zero hzero

#print axioms windingMode_not_mem_admissibleSubspace_of_ne
#print axioms windingModeCov_not_mem_admissibleSubspaceCov_of_ne

/-- **DOES-NOT-EXCLUDE, general.** Whenever `y` and `x` agree in coordinate `μ0`, the flat winding
mode in direction `μ0` is admissible for `(2.121)`'s subspace at `(y,x)` — for ANY `L`, `ell`, `y`,
`x` satisfying `admissibleSubspace`'s own antecedents, not one witness. -/
theorem windingMode_mem_admissibleSubspace_of_eq {L : PeriodicLatticeExtent}
    (y x : PeriodicLatticeSite L) (ell : ℕ) (hy : y ∈ CoarseLattice L ell)
    (hx : x ∈ blockOf y ell) (μ0 : Fin 3) (heq : y μ0 = x μ0) :
    windingMode L μ0 ∈ admissibleSubspace y x ell hy hx := by
  rw [mem_admissibleSubspace]
  intro b hb
  have hne := staircasePath_dir_ne_of_eq y x μ0 heq b hb
  simp [windingMode, hne]

/-- **Same fact, on the `𝔰𝔲(2)`-valued carrier** — the SAME combinatorial lemma
(`staircasePath_dir_ne_of_eq`) drives it, since `staircasePath` is literally the SAME bond set
regardless of fiber (`CoercivityCov.lean`'s own docstring: "same bond set... only the fiber
changes"). -/
theorem windingModeCov_mem_admissibleSubspaceCov_of_eq {L : PeriodicLatticeExtent}
    (y x : PeriodicLatticeSite L) (ell : ℕ) (hy : y ∈ CoarseLattice L ell)
    (hx : x ∈ blockOf y ell) (μ0 : Fin 3) (heq : y μ0 = x μ0) :
    windingModeCov L μ0 ∈ admissibleSubspaceCov y x ell hy hx := by
  rw [mem_admissibleSubspaceCov]
  intro b hb
  have hne := staircasePath_dir_ne_of_eq y x μ0 heq b hb
  simp [windingModeCov, hne]

#print axioms windingMode_mem_admissibleSubspace_of_eq
#print axioms windingModeCov_mem_admissibleSubspaceCov_of_eq

/-! ## §5. The concrete "excluded" direction, `decide`-checked on the witness lattice — completing
the exact `1`-of-`3` count -/

theorem windingMode_not_mem_witness_dir0 :
    windingMode witnessL 0 ∉
      admissibleSubspace witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block := by
  rw [mem_admissibleSubspace]
  intro hmem
  have hb : ((fun μ : Fin 3 => if μ.val = 2 then (1 : Fin 4) else 0), (0 : Fin 3)) ∈
      staircasePath witnessY witnessX := by
    rw [witness_staircasePath]; decide
  have := hmem _ hb
  simp only [windingMode] at this
  exact one_ne_zero this

theorem windingMode_not_mem_witness_dir2 :
    windingMode witnessL 2 ∉
      admissibleSubspace witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block := by
  rw [mem_admissibleSubspace]
  intro hmem
  have hb : ((fun _ : Fin 3 => (0 : Fin 4)), (2 : Fin 3)) ∈ staircasePath witnessY witnessX := by
    rw [witness_staircasePath]; decide
  have := hmem _ hb
  simp only [windingMode] at this
  exact one_ne_zero this

theorem witnessY_dir1_eq_witnessX : witnessY 1 = witnessX 1 := by decide

/-- **THE EXACT COUNT: `1` of `3` cycle directions survive the witness staircase, `2` of `3` are
excluded.** Direction `1` (where `witnessY`/`witnessX` coincide) is admissible; directions `0` and
`2` (where they differ) are excluded, `decide`-checked directly against the staircase's own computed
value (`witness_staircasePath`). -/
theorem witness_partial_count :
    (windingMode witnessL 1 ∈
      admissibleSubspace witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block) ∧
    (windingMode witnessL 0 ∉
      admissibleSubspace witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block) ∧
    (windingMode witnessL 2 ∉
      admissibleSubspace witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block) :=
  ⟨windingMode_mem_admissibleSubspace_of_eq witnessY witnessX witnessEll witnessY_coarse
      witnessX_mem_block 1 witnessY_dir1_eq_witnessX,
    windingMode_not_mem_witness_dir0, windingMode_not_mem_witness_dir2⟩

#print axioms windingMode_not_mem_witness_dir0
#print axioms windingMode_not_mem_witness_dir2
#print axioms witnessY_dir1_eq_witnessX
#print axioms witness_partial_count

/-! ## §6. Bundling everything at the surviving direction `μ0 = 1`: nonzero, harmonic, topologically
nontrivial, AND admissible — for both carriers -/

theorem windingMode_witness_bundle :
    windingMode witnessL 1 ≠ 0 ∧
    windingMode witnessL 1 ∈
      admissibleSubspace witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block ∧
    (∀ p, curlValue (windingMode witnessL 1) p = 0) ∧
    ¬ ∃ lam : PeriodicLatticeSite witnessL → ℝ, gradValue lam = windingMode witnessL 1 :=
  ⟨windingMode_ne_zero witnessL 1,
    windingMode_mem_admissibleSubspace_of_eq witnessY witnessX witnessEll witnessY_coarse
      witnessX_mem_block 1 witnessY_dir1_eq_witnessX,
    curlValue_windingMode_eq_zero witnessL 1,
    windingMode_not_mem_range_gradValue witnessL 1⟩

theorem windingModeCov_witness_bundle :
    windingModeCov witnessL 1 ≠ 0 ∧
    windingModeCov witnessL 1 ∈
      admissibleSubspaceCov witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block ∧
    (∀ p, curlValueCovariant (trivialU witnessL) (windingModeCov witnessL 1) p = 0) ∧
    ¬ ∃ lam : PeriodicLatticeSite witnessL → SuTwo,
        gradValueCovariant (trivialU witnessL) lam = windingModeCov witnessL 1 :=
  ⟨windingModeCov_ne_zero witnessL 1,
    windingModeCov_mem_admissibleSubspaceCov_of_eq witnessY witnessX witnessEll witnessY_coarse
      witnessX_mem_block 1 witnessY_dir1_eq_witnessX,
    curlValueCovariant_trivialU_windingModeCov_eq_zero witnessL 1,
    windingModeCov_not_mem_range_gradValueCovariant witnessL 1⟩

#print axioms windingMode_witness_bundle
#print axioms windingModeCov_witness_bundle

/-! ## §7. Transported to `anchoredVCov` — the exact Hilbert-space carrier the campaign's stated
coercivity deliverables (`SpineCovariant.oneScaleCoercivity_su2`) quantify over -/

/-- **A nonzero, curl-harmonic, `anchoredVCov`-admissible witness, for the CURL operator** — the
operator `SpineCovariant.lean`'s own docstring identifies as the numerically/`H_j`-relevant one, and
`ForcedIntersection.lean` explicitly disclosed as "NOT checked" by its (different) refutation. -/
theorem anchoredVCov_windingModeCov_ne_bot_witness :
    ∃ B ∈ anchoredVCov witnessY witnessX witnessEll witnessY_coarse witnessX_mem_block, B ≠ 0 := by
  refine ⟨(AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv witnessL).symm
    (windingModeCov witnessL 1), ?_, ?_⟩
  · exact Submodule.mem_map_of_mem windingModeCov_witness_bundle.2.1
  · intro h
    apply windingModeCov_witness_bundle.1
    have hc := congrArg (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv witnessL) h
    simpa using hc

#print axioms anchoredVCov_windingModeCov_ne_bot_witness

end AdalyFormal.Balaban.HarmonicModes
