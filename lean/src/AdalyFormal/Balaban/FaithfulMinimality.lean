import AdalyFormal.Balaban.CovariantHjFaithful

/-!
# `Δ_J` ON THE FAITHFUL CARRIER IS A GENUINE MINIMUM — the certificate the tree never wrote

## Why this module exists

The whole min-swap route (`Balaban/MinSwap.lean`) rests on `total ⟹ Schur` pointing the right way,
and that direction is sound only if `deltaJQuadFormCovFaithful` is the **minimum** of the fine curl
energy over its fibre. If it were merely the *evaluation* at one distinguished extension `H A₀`,
then a lower bound on it would be a lower bound on an UPPER bound for the true distance — and the
implication would be worthless.

The tree asserted this in prose and never named a declaration for it:

* `CovariantHjMinimizer.hjExtensionCov_isMinimal` (`CovariantHjMinimizer.lean:1599`) proves it for
  the **non-Faithful** `deltaJQuadFormCov`.
* `SchurNonzero.lean`'s introduction states `deltaJQuadFormCovFaithful = ‖D A₀ − Π_{D(V)}(D A₀)‖²
  = dist(D A₀, D V)²` — **in a docstring**.
* Grep for `minimal` in `CovariantHjFaithful.lean`: **zero hits.** No Faithful analogue existed
  anywhere in the tree.

That is the "a claim is not a certificate" pattern: the test is NAME THE DECLARATION, and for the
Faithful variant specifically the name did not exist. This module supplies it.

## Provenance

Found by the adversarial prosecution of `MinSwap.lean` (commit `a297d2eb`), which was asked whether
the inequality points the right way. It could not refute the claim — and closed the gap by direct
construction instead, mirroring the non-Faithful minimality proof line-for-line with the Faithful
declarations substituted. The probe (`compute/prosecute_minswap/ProbeMinimality.lean`) was
independently recompiled in the main loop: `EXIT=0`,
`[propext, Classical.choice, Quot.sound]`. Promoted here out of a throwaway probe directory, because
a certificate the route depends on must live in the tree, not in a prosecutor's scratch space.

**This corrects a weaker check of my own.** The main loop had verified the direction by reading
`SchurNonzero.lean`'s prose identification. Prose is not a certificate. §1 is.

## What is proved

* `hjExtensionCovFaithful_isMinimal` — for any two elements `A₀`, `A₁` of the same faithful fibre
  (`Q_ℓ · = B` and `R∂*_U · = 0`), `Δ_J(A₀) ≤ ‖D_U A₁‖²`. So `Δ_J` is a lower bound for the fine
  curl energy across the whole fibre, and in particular does not depend on which fibre element it is
  evaluated at.
* `deltaJ_eq_curlEnergy_hjExtension` — `Δ_J(A₀)` IS the curl energy at `H A₀`.
* `hjExtension_mem_fibreEnergies` — that value is ATTAINED, by `H A₀`, which lies in the fibre.
* `deltaJ_isLeast_fibreEnergies` — the two together: `IsLeast (fibreEnergies …) (Δ_J A₀)`. This is
  the statement the min-swap needs, as a theorem.

## Scope, stated plainly

This settles that `Δ_J` is the minimum **over the fibre this tree defines** — `Q_ℓ · = B` together
with the `R∂*_U` gauge clause. It says NOTHING about whether that fibre is the one CMP99b (3.156)
means. The tree's own adjudicated denotation row `delta_k_unit_p428_3156`
(`compute/denotation_dict/MISMATCHES.tsv`, status `verified`, page-image adjudicated) records a
**MISMATCH**: the source's `Δ_k` is indexed by the UNIT level with the fine level integrated out and
is built from the `j`-step composite `Q_j`, while `deltaJQuadFormCovFaithful` collapses fine and
unit into this tree's single bond level. That is the standing NO-RG-LADDER finding and nothing here
touches it. A minimum over the wrong fibre is still a minimum over the wrong fibre.
-/

set_option autoImplicit false

namespace AdalyFormal.Balaban.FaithfulMinimality

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.KernelSubspace
  AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.Balaban.LineIntegralCovariant
  AdalyFormal.Balaban.Q1Real
  AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `Δ_J` IS A LOWER BOUND ACROSS THE WHOLE FAITHFUL FIBRE

The Pythagorean split: `D_U A₁ = p + q` with `p := hjCorrectionTargetCovFaithful … A₀` and
`q ∈ curlImageCovFaithful`, and `p ⟂ q` by `hjCorrectionTargetCovFaithful_orthogonal`. Then
`‖D_U A₁‖² = ‖p‖² + ‖q‖² ≥ ‖p‖² = Δ_J(A₀)`.

The hypothesis `A₁ − A₀ ∈ gaugeConstraintSubspaceCovFaithful` is DERIVED from the two fibre
conditions rather than assumed — that is what makes this a statement about the fibre and not about a
hand-picked pair. -/

/-- **`Δ_J` ON THE FAITHFUL CARRIER IS THE MINIMUM OVER ITS FIBRE.** For any `A₀`, `A₁` with the
same coarse image `B` and both satisfying the `R∂*_U` gauge clause,
`Δ_J(A₀) ≤ ‖D_U A₁‖²`.

Note what is NOT assumed: `A₀` is an arbitrary fibre element, not the extension. So the bound holds
from every base point, which is why `Δ_J` is a function of the fibre and not of the
representative. -/
theorem hjExtensionCovFaithful_isMinimal {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 A1 : Bond L → SuTwo) (B : CoarseBond L ell → SuTwo)
    (h1 : lineCoarseRestrictCovLM U ell A0 = B)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0)
    (h1' : lineCoarseRestrictCovLM U ell A1 = B)
    (h2' : RcovLM U levels (gradCovariantAdjointLM U A1) = 0) :
    deltaJQuadFormCovFaithful ell levels U A0 ≤
      covPlaqInner (curlCovariantLM U A1) (curlCovariantLM U A1) := by
  have hVmem : A1 - A0 ∈ gaugeConstraintSubspaceCovFaithful ell levels U := by
    rw [mem_gaugeConstraintSubspaceCovFaithful]
    refine ⟨?_, ?_⟩
    · rw [map_sub, h1', h1, sub_self]
    · rw [map_sub, map_sub, h2', h2, sub_self]
  set p := hjCorrectionTargetCovFaithful ell levels U A0 with hp_def
  set q := curlCovariantLM U A1 - p with hq_def
  have hsplit_A1 : curlCovariantLM U A1 = curlCovariantLM U A0 + curlCovariantLM U (A1 - A0) := by
    rw [← map_add]
    congr 1
    abel
  have hwmem : curlCovariantLM U (A1 - A0) ∈ curlImageCovFaithful ell levels U :=
    curl_mem_curlImageCovFaithful_of_mem hVmem
  have hqeq : q = curlCovariantLM U (A1 - A0) +
      curlImageCovProjFaithful ell levels U (curlCovariantLM U A0) := by
    rw [hq_def, hp_def]
    unfold hjCorrectionTargetCovFaithful
    rw [hsplit_A1]
    abel
  have hqmem : q ∈ curlImageCovFaithful ell levels U := by
    rw [hqeq]
    exact Submodule.add_mem _ hwmem
      (curlImageCovProjFaithful_mem ell levels U (curlCovariantLM U A0))
  have hqp0 : covPlaqInner q p = 0 := hjCorrectionTargetCovFaithful_orthogonal ell levels U A0 hqmem
  have hpq0 : covPlaqInner p q = 0 := by rw [covPlaqInner_symm]; exact hqp0
  have hsplit : curlCovariantLM U A1 = p + q := by rw [hq_def]; abel
  have hpyth : covPlaqInner (curlCovariantLM U A1) (curlCovariantLM U A1) =
      covPlaqInner p p + covPlaqInner q q := by
    rw [hsplit, covPlaqInner_add_left, covPlaqInner_add_right, covPlaqInner_add_right, hpq0, hqp0]
    ring
  have hdelta : deltaJQuadFormCovFaithful ell levels U A0 = covPlaqInner p p := by
    unfold deltaJQuadFormCovFaithful
    rw [curlCov_hjExtensionCovFaithful]
  rw [hpyth, hdelta]
  linarith [covPlaqInner_self_nonneg q]

/-! ## §2 — THE VALUE IS ATTAINED, SO IT IS A MINIMUM AND NOT MERELY AN INFIMUM

A lower bound alone would leave open that `Δ_J` sits strictly below everything in the fibre — in
which case it would be an infimum that no fibre element realizes, and `total ⟹ Schur` would still
transfer but the object would not be the source's distance. `H A₀` realizes it. -/

/-- The fine curl energies realized across the faithful fibre over `B`. -/
def fibreEnergies (ell : ℕ) (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : CoarseBond L ell → SuTwo) : Set ℝ :=
  {r | ∃ A : Bond L → SuTwo, lineCoarseRestrictCovLM U ell A = B ∧
    RcovLM U levels (gradCovariantAdjointLM U A) = 0 ∧
    r = covPlaqInner (curlCovariantLM U A) (curlCovariantLM U A)}

/-- `Δ_J(A₀)` IS the fine curl energy at the Bałaban extension `H A₀` — definitional, via
`curlCov_hjExtensionCovFaithful`. -/
theorem deltaJ_eq_curlEnergy_hjExtension {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    deltaJQuadFormCovFaithful ell levels U A0
      = covPlaqInner (curlCovariantLM U (hjExtensionCovFaithful ell levels U A0))
          (curlCovariantLM U (hjExtensionCovFaithful ell levels U A0)) := by
  unfold deltaJQuadFormCovFaithful
  rw [curlCov_hjExtensionCovFaithful]

/-- The minimum is ATTAINED: `H A₀` lies in the fibre and realizes `Δ_J(A₀)`. -/
theorem hjExtension_mem_fibreEnergies {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (B : CoarseBond L ell → SuTwo)
    (h1 : lineCoarseRestrictCovLM U ell A0 = B)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    deltaJQuadFormCovFaithful ell levels U A0 ∈ fibreEnergies ell levels U B := by
  have hbal := hjExtensionCovFaithful_isBalabanExtensionCov ell levels U A0 B h1 h2
  exact ⟨hjExtensionCovFaithful ell levels U A0, hbal.interpolates, hbal.gaugeFixed,
    deltaJ_eq_curlEnergy_hjExtension levels U A0⟩

/-- **THE STATEMENT THE MIN-SWAP NEEDS, AS A THEOREM.** `Δ_J(A₀)` is the LEAST fine curl energy over
the faithful fibre — attained, and a lower bound. So a lower bound on `Δ_J` is a lower bound on the
fibre minimum, and `total ⟹ Schur` transfers soundly. -/
theorem deltaJ_isLeast_fibreEnergies {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (B : CoarseBond L ell → SuTwo)
    (h1 : lineCoarseRestrictCovLM U ell A0 = B)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    IsLeast (fibreEnergies ell levels U B) (deltaJQuadFormCovFaithful ell levels U A0) := by
  refine ⟨hjExtension_mem_fibreEnergies levels U A0 B h1 h2, ?_⟩
  rintro r ⟨A1, hA1Q, hA1R, rfl⟩
  exact hjExtensionCovFaithful_isMinimal levels U A0 A1 B h1 h2 hA1Q hA1R

/-- `Δ_J` does not depend on WHICH fibre element it is evaluated at — an immediate consequence of
`IsLeast` uniqueness, and the sanity check that the object is a function of the fibre. -/
theorem deltaJ_eq_of_same_fibre {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 A1 : Bond L → SuTwo) (B : CoarseBond L ell → SuTwo)
    (h1 : lineCoarseRestrictCovLM U ell A0 = B)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0)
    (h1' : lineCoarseRestrictCovLM U ell A1 = B)
    (h2' : RcovLM U levels (gradCovariantAdjointLM U A1) = 0) :
    deltaJQuadFormCovFaithful ell levels U A0 = deltaJQuadFormCovFaithful ell levels U A1 :=
  IsLeast.unique (deltaJ_isLeast_fibreEnergies levels U A0 B h1 h2)
    (deltaJ_isLeast_fibreEnergies levels U A1 B h1' h2')

#print axioms hjExtensionCovFaithful_isMinimal
#print axioms deltaJ_eq_curlEnergy_hjExtension
#print axioms hjExtension_mem_fibreEnergies
#print axioms deltaJ_isLeast_fibreEnergies
#print axioms deltaJ_eq_of_same_fibre

end AdalyFormal.Balaban.FaithfulMinimality
