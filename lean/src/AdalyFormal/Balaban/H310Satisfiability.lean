/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.BridgeInverseControls

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.longLine false

/-!
# `H310Satisfiability.lean` — is the UNRESTRICTED (3.10) coercivity hypothesis satisfiable?

## The question this module answers

`BridgeInverse.bridge_source_chain_at_curvedRegularU` — the tree's flagship instantiation of
`RecursiveBridge.bridge_from_piExtended_normalized_threeTen`, the one that runs the whole bridge
with `hG1` and `hTS` CONSTRUCTED rather than assumed — takes its (3.10) coercivity hypothesis

  `h310 : ∀ A : Bond witL5 → SuTwo,
      γ₀ * ‖toLp A‖² ≤ deltaKQuadFormNormalizedCorrected curvedRegularU A`

**unrestricted**: the `∀ A` ranges over the whole bond-field space, with no subspace `W`, no
kernel condition, no gauge condition.

`BridgeInverse.h310_unrestricted_impossible_at_witnessU` proves that exact shape UNSATISFIABLE at
`CovariantOperators.witnessU`. Whether it is also unsatisfiable at `curvedRegularU` was recorded as
undecided (`compute/route_audit/ROUTE_AUDIT.md`, §B and "WHAT COULD NOT BE DECIDED FROM THE TREE").

**Answer: it is unsatisfiable, and not for the witness's reason.** §2 below exhibits a
background-generic null field.

## Why the `witnessU` mechanism does NOT transfer

At `witnessU` the refutation runs through
`NormalizationAudit.deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero`: on the
single-bond spike, `dstarDQuadForm = 4` and `½·Δ′ = 4` cancel exactly. That cancellation needs a
MAXIMAL adjoint defect — `witnessM` acts on `suTwoWitness` as `−1`. `curvedRegularU` carries
`rotElem (10⁻⁷)`, whose defect is `8t²/(1+t²) ≈ 8·10⁻¹⁴`
(`NonFlatBackground.defectOfElem_rotElem`), so on any spike the form is `≈ 4 > 0`. The witness
mechanism is specific to a maximally curved bond and says nothing about `curvedRegularU`.

## §2 — the mechanism that DOES transfer: a constant field in one lattice direction

`dirConstField d X b := if b.2 = d then X else 0` — the same Lie-algebra element `X` on every bond
of direction `d`, zero on the other two directions. It is a lattice analogue of the constant
1-form `X dx^d`, and it is closed.

Reading `CovariantOperators.curlValueCovariant`'s own four terms at a plaquette with
`μ = p.2.1.1 < ν = p.2.1.2`:

  `A(x,μ) + R(U(x,μ))A(x+μ,ν) − R(U(x,ν))A(x+ν,μ) − A(x,ν)`

* if `μ = d` then `ν ≠ d`, so this is `X + R(U(x,μ))·0 − R(U(x,ν))·X − 0`;
* if `μ ≠ d` this is `0 + R(U(x,μ))·[ν=d]X − R(U(x,ν))·0 − [ν=d]X`.

Both collapse to `0` under the single hypothesis

  `AxisCompatible U d X : ∀ b : Bond L, b.2 ≠ d → RMap (U b) X = X`,

which holds whenever `U` is trivial on every bond of direction `≠ d` (`RMap 1 = id`). So the
covariant curl vanishes IDENTICALLY, hence `dstarDQuadForm = 0` and `Δ′`'s first term (which is
quadratic in the curl) vanishes plaquette by plaquette. `Δ′`'s second term dies too: the four
`A′` values are `A′₃ = [μ=d]X`, `A′₁ = −[μ=d]X`, `A′₄ = [ν=d]X`, `A′₂ = −[ν=d]X`, so in each case
two of the four are `0` and the remaining two are negatives of each other — every commutator in
`DeltaPrime.commutatorMatrixSum` vanishes.

Result: `deltaKQuadFormNormalizedCorrected U (dirConstField d X) = 0` while
`dirConstField d X ≠ 0`. An unrestricted `∀ A` coercivity with `γ > 0` is therefore impossible.

## §3 — what this covers

`curvedBond.2 = 0` (`RegularUCurvedWitness.curvedBond_dir`) and `curvedRegularU` is `1` off
`curvedBond` (`RegularUCurvedWitness.bondU_off`), so `d := 0` applies. The same `d := 0` applies to
`CovariantOperators.witnessU` (nontrivial only at `(witnessY,0)`) and, trivially, to
`CovariantHjMinimizer.trivialU`. So the unrestricted hypothesis fails at the FLAT background as
well: this is not a statement about curvature, it is a statement about the gauge/closed directions
the unrestricted quantifier fails to exclude. That is exactly why
`RecursiveBridge.bridge_from_fine_operator` demands coercivity only on `W`.

**No `sorry`. No new axiom. Nothing in this module is edited outside it.**
-/

namespace AdalyFormal.Balaban.H310Satisfiability

open scoped InnerProductSpace
open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLatticePlaquette PeriodicLinkConfiguration)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant
  suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm covPlaqInner hsInner_zero_zero)
open AdalyFormal.Balaban.DeltaPrime (AprimeXY AprimeYZ AprimeZW AprimeWX commutatorMatrixSum
  deltaPrimeFirstTerm deltaPrimeSecondTerm deltaPrimePlaqTerm deltaPrimeQuadForm)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.SuTwoInner (hsInner)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the field, and the one hypothesis it needs on the background -/

/-- **The constant field in lattice direction `d`**: the SAME `𝔰𝔲(2)` element `X` on every bond of
direction `d`, `0` on the other two directions. Lattice analogue of the constant 1-form `X dx^d`. -/
noncomputable def dirConstField (d : Fin 3) (X : SuTwo) : Bond L → SuTwo :=
  fun b => if b.2 = d then X else 0

/-- Evaluation at an explicitly-paired bond — the shape every read in `curlValueCovariant` and in
the four `A′` terms actually has. -/
theorem dirConstField_dir (d : Fin 3) (X : SuTwo) (x : PeriodicLatticeSite L) (e : Fin 3) :
    dirConstField d X (x, e) = if e = d then X else 0 := rfl

/-- **The single hypothesis on the background.** `X` is fixed by the adjoint action of every link
whose direction is not `d`. Discharged by `RMap 1 = id` whenever `U` is trivial off direction
`d` — see `axisCompatible_of_trivial_off_dir`. -/
def AxisCompatible (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) : Prop :=
  ∀ b : Bond L, b.2 ≠ d → RMap (U b) X = X

/-- If `U` is `1` on every bond of direction `≠ d`, `AxisCompatible` holds for EVERY `X`. -/
theorem axisCompatible_of_trivial_off_dir
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (hU : ∀ b : Bond L, b.2 ≠ d → U b = 1) :
    AxisCompatible U d X := by
  intro b hb
  rw [hU b hb, RMap_one]
  rfl

/-! ## §2 — the covariant curl of `dirConstField` vanishes identically -/

/-- **`D_U (dirConstField d X) = 0` at EVERY plaquette.** The proof is the four-term read of
`curlValueCovariant` with `μ = p.2.1.1 < ν = p.2.1.2`, so `μ` and `ν` cannot both equal `d`. -/
theorem curl_dirConstField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (hax : AxisCompatible U d X)
    (p : PeriodicLatticePlaquette L) :
    curlValueCovariant U (dirConstField d X) p = 0 := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  show dirConstField d X (p.1, p.2.1.1)
      + RMap (U (p.1, p.2.1.1))
          (dirConstField d X (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.1,
            p.2.1.2))
      - RMap (U (p.1, p.2.1.2))
          (dirConstField d X (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.2,
            p.2.1.1))
      - dirConstField d X (p.1, p.2.1.2) = 0
  rw [dirConstField_dir, dirConstField_dir, dirConstField_dir, dirConstField_dir]
  by_cases hmu : p.2.1.1 = d
  · have hnu : p.2.1.2 ≠ d := fun h => hne (hmu.trans h.symm)
    rw [if_pos hmu, if_neg hnu, map_zero, hax (p.1, p.2.1.2) hnu]
    abel
  · rw [if_neg hmu, map_zero]
    by_cases hnu : p.2.1.2 = d
    · rw [if_pos hnu, hax (p.1, p.2.1.1) hmu]
      abel
    · rw [if_neg hnu, map_zero]
      abel

/-- `⟨A,D*DA⟩ = 0` for the constant field. -/
theorem dstarDQuadForm_dirConstField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (hax : AxisCompatible U d X) :
    dstarDQuadForm U (dirConstField d X) = 0 := by
  unfold dstarDQuadForm covPlaqInner
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rw [curl_dirConstField_eq_zero U d X hax p, hsInner_zero_zero]

/-! ## §3 — `Δ′` vanishes on the constant field too -/

/-- Two of the four `A′` values are `0` and the other two are negatives of each other, in the
`{A′₂ = A′₄ = 0, A′₁ = −A′₃}` pattern: every one of the six commutators dies. -/
theorem commutatorMatrixSum_eq_zero_of_a2a4_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (h2 : (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) = 0)
    (h4 : (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) = 0)
    (h13 : (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ)
             = -(AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ)) :
    commutatorMatrixSum U A p = 0 := by
  unfold commutatorMatrixSum
  simp only [h2, h4, h13, mul_zero, zero_mul, neg_zero, add_zero,
    neg_mul, mul_neg, sub_self, smul_zero]

/-- The mirrored pattern `{A′₁ = A′₃ = 0, A′₂ = −A′₄}`. -/
theorem commutatorMatrixSum_eq_zero_of_a1a3_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (h1 : (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) = 0)
    (h3 : (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) = 0)
    (h24 : (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ)
             = -(AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ)) :
    commutatorMatrixSum U A p = 0 := by
  unfold commutatorMatrixSum
  simp only [h1, h3, h24, mul_zero, zero_mul, neg_zero, add_zero,
    neg_mul, mul_neg, sub_self, smul_zero]

/-- **The commutator sum vanishes on the constant field, at every plaquette.** -/
theorem commutatorMatrixSum_dirConstField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (hax : AxisCompatible U d X)
    (p : PeriodicLatticePlaquette L) :
    commutatorMatrixSum U (dirConstField d X) p = 0 := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  by_cases hmu : p.2.1.1 = d
  · have hnu : p.2.1.2 ≠ d := fun h => hne (hmu.trans h.symm)
    refine commutatorMatrixSum_eq_zero_of_a2a4_zero U _ p ?_ ?_ ?_
    · show ((-(dirConstField d X (p.1, p.2.1.2)) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = 0
      rw [dirConstField_dir, if_neg hnu]
      simp
    · show ((RMap (U (p.1, p.2.1.1))
        (dirConstField d X (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.1,
          p.2.1.2)) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = 0
      rw [dirConstField_dir, if_neg hnu, map_zero]
      simp
    · show ((-(RMap (U (p.1, p.2.1.2))
        (dirConstField d X (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.2,
          p.2.1.1))) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
          = -((dirConstField d X (p.1, p.2.1.1) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
      rw [dirConstField_dir, dirConstField_dir, if_pos hmu, hax (p.1, p.2.1.2) hnu]
      simp
  · refine commutatorMatrixSum_eq_zero_of_a1a3_zero U _ p ?_ ?_ ?_
    · show ((-(RMap (U (p.1, p.2.1.2))
        (dirConstField d X (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.2,
          p.2.1.1))) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = 0
      rw [dirConstField_dir, if_neg hmu, map_zero]
      simp
    · show ((dirConstField d X (p.1, p.2.1.1) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = 0
      rw [dirConstField_dir, if_neg hmu]
      simp
    · show ((-(dirConstField d X (p.1, p.2.1.2)) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
          = -((RMap (U (p.1, p.2.1.1))
            (dirConstField d X (AdalyFormal.Target.ClayStatement.periodicLatticeShift p.1 p.2.1.1,
              p.2.1.2)) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
      by_cases hnu : p.2.1.2 = d
      · rw [dirConstField_dir, dirConstField_dir, if_pos hnu, hax (p.1, p.2.1.1) hmu]
        simp
      · rw [dirConstField_dir, dirConstField_dir, if_neg hnu, map_zero]
        simp

/-- **`Δ′`'s per-plaquette summand vanishes on the constant field.** The first term is quadratic in
the curl (`= 0` by §2); the second is the commutator sum against `Im U(∂p)` (`= 0` just above). -/
theorem deltaPrimePlaqTerm_dirConstField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (hax : AxisCompatible U d X)
    (p : PeriodicLatticePlaquette L) :
    deltaPrimePlaqTerm U (dirConstField d X) p = 0 := by
  have hfirst : deltaPrimeFirstTerm U (dirConstField d X) p = 0 := by
    unfold deltaPrimeFirstTerm
    rw [curl_dirConstField_eq_zero U d X hax p]
    simp
  have hsecond : deltaPrimeSecondTerm U (dirConstField d X) p = 0 := by
    unfold deltaPrimeSecondTerm
    rw [commutatorMatrixSum_dirConstField_eq_zero U d X hax p]
    simp
  unfold deltaPrimePlaqTerm
  rw [hfirst, hsecond, add_zero]

/-- `⟨A,Δ′A⟩ = 0` for the constant field. -/
theorem deltaPrimeQuadForm_dirConstField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (hax : AxisCompatible U d X) :
    deltaPrimeQuadForm U (dirConstField d X) = 0 := by
  unfold deltaPrimeQuadForm
  exact Finset.sum_eq_zero (fun p _ => deltaPrimePlaqTerm_dirConstField_eq_zero U d X hax p)

/-! ## §4 — THE NULL FIELD: the source-normalized `Δ_k` form is exactly `0` on it -/

/-- **`deltaKQuadFormNormalizedCorrected U (dirConstField d X) = 0`**, for every background `U`
satisfying `AxisCompatible U d X`. Both halves of `D*D − ½Δ′` vanish separately. -/
theorem deltaKQuadFormNormalizedCorrected_dirConstField_eq_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (hax : AxisCompatible U d X) :
    deltaKQuadFormNormalizedCorrected U (dirConstField d X) = 0 := by
  rw [AdalyFormal.Balaban.CoercivityRegular.deltaKQuadFormNormalizedCorrected_eq_sub,
    dstarDQuadForm_dirConstField_eq_zero U d X hax,
    deltaPrimeQuadForm_dirConstField_eq_zero U d X hax]
  norm_num

/-- The constant field is a NONZERO vector of `BondFnL2 L` whenever `X ≠ 0` — the must-not-fire
half, so the refutation below is not about an empty test set. -/
theorem toLp_dirConstField_ne_zero (d : Fin 3) (X : SuTwo) (hX : X ≠ 0) :
    (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L) ≠ 0 := by
  intro hcon
  have h : dirConstField (L := L) d X ((fun _ => 0 : PeriodicLatticeSite L), d) = (0 : SuTwo) :=
    congrFun (congrArg (fun u : BondFnL2 L => WithLp.ofLp u) hcon)
      ((fun _ => 0 : PeriodicLatticeSite L), d)
  rw [dirConstField_dir, if_pos rfl] at h
  exact hX h

/-- Positive norm, stated separately because both refutations below use it. -/
theorem norm_toLp_dirConstField_pos (d : Fin 3) (X : SuTwo) (hX : X ≠ 0) :
    0 < ‖(WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ := by
  rcases (norm_nonneg (WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)).lt_or_eq with h | h
  · exact h
  · exact absurd (norm_eq_zero.1 h.symm) (toLp_dirConstField_ne_zero d X hX)

/-! ## §5 — THE REFUTATION, general in the background -/

/-- **THE UNRESTRICTED (3.10) COERCIVITY HYPOTHESIS IS UNSATISFIABLE**, at every background
admitting an axis-compatible direction and for every `γ > 0`. -/
theorem h310_unrestricted_impossible_of_axisCompatible
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (d : Fin 3) (X : SuTwo) (hX : X ≠ 0) (hax : AxisCompatible U d X)
    (γ : ℝ) (hγ : 0 < γ) :
    ¬ (∀ A : Bond L → SuTwo,
        γ * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2 ≤ deltaKQuadFormNormalizedCorrected U A) := by
  intro h310
  have hv := h310 (dirConstField d X)
  rw [deltaKQuadFormNormalizedCorrected_dirConstField_eq_zero U d X hax] at hv
  have hpos := norm_toLp_dirConstField_pos (L := L) d X hX
  have hsq : 0 < ‖(WithLp.toLp 2 (dirConstField (L := L) d X) : BondFnL2 L)‖ ^ 2 :=
    pow_pos hpos 2
  linarith [mul_pos hγ hsq, hv]

/-! ## §6 — THE THREE CONCRETE BACKGROUNDS OF THE TREE

`curvedRegularU`, `witnessU` and `trivialU` are ALL single-bond-or-trivial configurations whose
only possibly-nontrivial link has direction `0`. So `d := 0` works at each of them, with
`X := suTwoWitness`. -/

/-- `curvedRegularU` is `1` on every bond of direction `≠ 0`: its only active bond is `curvedBond`,
whose direction is `0` (`RegularUCurvedWitness.curvedBond_dir`). -/
theorem curvedRegularU_trivial_off_dir0 :
    ∀ b : Bond AdalyFormal.Balaban.RegularUDomainWitness.witL5, b.2 ≠ (0 : Fin 3) →
      AdalyFormal.Balaban.CoercivityRegular.curvedRegularU b = 1 := by
  intro b hb
  have hbne : b ≠ AdalyFormal.Balaban.RegularUCurvedWitness.curvedBond := by
    intro hcon
    exact hb (by rw [hcon]; exact AdalyFormal.Balaban.RegularUCurvedWitness.curvedBond_dir)
  exact AdalyFormal.Balaban.RegularUCurvedWitness.bondU_off _ _ hbne

theorem axisCompatible_curvedRegularU :
    AxisCompatible AdalyFormal.Balaban.CoercivityRegular.curvedRegularU (0 : Fin 3) suTwoWitness :=
  axisCompatible_of_trivial_off_dir _ _ _ curvedRegularU_trivial_off_dir0

/-- **THE ANSWER. The unrestricted `h310` of `bridge_source_chain_at_curvedRegularU` is
UNSATISFIABLE at `curvedRegularU`**, for every `γ₀ > 0` — stated in exactly the shape of
`BridgeInverse.h310_unrestricted_impossible_at_witnessU` so the two compose. -/
theorem h310_unrestricted_impossible_at_curvedRegularU (γ : ℝ) (hγ : 0 < γ) :
    ¬ (∀ A : Bond AdalyFormal.Balaban.RegularUDomainWitness.witL5 → SuTwo,
        γ * ‖(WithLp.toLp 2 A :
              BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5)‖ ^ 2
          ≤ deltaKQuadFormNormalizedCorrected
              AdalyFormal.Balaban.CoercivityRegular.curvedRegularU A) :=
  h310_unrestricted_impossible_of_axisCompatible _ (0 : Fin 3) suTwoWitness suTwoWitness_ne_zero
    axisCompatible_curvedRegularU γ hγ

/-! ### The whole single-active-bond family, at once

`RegularUCurvedWitness.bondU b₀ g` is `g` on the bond `b₀` and `1` on every other bond. Taking
`d := b₀.2` makes EVERY such background axis-compatible for EVERY `X` and EVERY group element `g`:
the only bond that could break `RMap (U b) X = X` is `b₀`, and `b₀.2 = d` excludes it. So the
refutation covers `curvedU`, `tinyU`, `singleBondU`, `witnessU`, and the whole curved family
`curvedFamilyU t` uniformly, not just the two named instances below. -/

theorem axisCompatible_bondU (b₀ : Bond L)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    AxisCompatible (AdalyFormal.Balaban.RegularUCurvedWitness.bondU b₀ g) b₀.2 X :=
  axisCompatible_of_trivial_off_dir _ _ _
    (fun b hb => AdalyFormal.Balaban.RegularUCurvedWitness.bondU_off b₀ g
      (fun hc => hb (by rw [hc])))

/-- **THE UNRESTRICTED `h310` IS UNSATISFIABLE AT EVERY SINGLE-ACTIVE-BOND BACKGROUND**, on every
extent, for every active bond, every `SU(2)` element on it, and every `γ > 0`. -/
theorem h310_unrestricted_impossible_at_bondU (b₀ : Bond L)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (γ : ℝ) (hγ : 0 < γ) :
    ¬ (∀ A : Bond L → SuTwo,
        γ * ‖(WithLp.toLp 2 A : BondFnL2 L)‖ ^ 2
          ≤ deltaKQuadFormNormalizedCorrected
              (AdalyFormal.Balaban.RegularUCurvedWitness.bondU b₀ g) A) :=
  h310_unrestricted_impossible_of_axisCompatible _ b₀.2 suTwoWitness suTwoWitness_ne_zero
    (axisCompatible_bondU b₀ g suTwoWitness) γ hγ

/-- `witnessU` is `1` off direction `0` — its only active bond is `(witnessY, 0)`. -/
theorem witnessU_trivial_off_dir0 :
    ∀ b : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL, b.2 ≠ (0 : Fin 3) →
      AdalyFormal.Balaban.CovariantOperators.witnessU b = 1 := by
  intro b hb
  have hbne : b ≠ (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)) := by
    intro hcon
    exact hb (by rw [hcon])
  show (if b = (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3)) then _ else _) = 1
  rw [if_neg hbne]

/-- **AN INDEPENDENT RE-PROOF of `BridgeInverse.h310_unrestricted_impossible_at_witnessU`**, by a
mechanism that shares nothing with the original: the original cancels `dstarD = 4` against
`½Δ′ = 4` on a single-bond spike; this one makes both terms vanish separately on a constant field.
A cross-check that the general route reproduces the tree's one banked instance. -/
theorem h310_unrestricted_impossible_at_witnessU' (γ : ℝ) (hγ : 0 < γ) :
    ¬ (∀ A : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL → SuTwo,
        γ * ‖(WithLp.toLp 2 A :
              BondFnL2 AdalyFormal.Balaban.AdmissibleSubspace.witnessL)‖ ^ 2
          ≤ deltaKQuadFormNormalizedCorrected
              AdalyFormal.Balaban.CovariantOperators.witnessU A) :=
  h310_unrestricted_impossible_of_axisCompatible _ (0 : Fin 3) suTwoWitness suTwoWitness_ne_zero
    (axisCompatible_of_trivial_off_dir _ _ _ witnessU_trivial_off_dir0) γ hγ

/-- **AND IT FAILS AT THE FLAT BACKGROUND TOO.** `trivialU` is `1` on every bond, so every
direction is axis-compatible. This is the sharpest form of the finding: the unrestricted `∀ A`
hypothesis is not defeated by curvature, it is defeated by the closed/gauge directions that the
missing subspace restriction `W` is there to remove. -/
theorem h310_unrestricted_impossible_at_trivialU
    (Lat : PeriodicLatticeExtent) (γ : ℝ) (hγ : 0 < γ) :
    ¬ (∀ A : Bond Lat → SuTwo,
        γ * ‖(WithLp.toLp 2 A : BondFnL2 Lat)‖ ^ 2
          ≤ deltaKQuadFormNormalizedCorrected
              (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU Lat) A) :=
  h310_unrestricted_impossible_of_axisCompatible _ (0 : Fin 3) suTwoWitness suTwoWitness_ne_zero
    (axisCompatible_of_trivial_off_dir _ _ _ (fun _ _ => rfl)) γ hγ

/-! ## §7 — CONSEQUENCE FOR THE FLAGSHIP INSTANTIATION

`BridgeInverse.bridge_source_chain_at_curvedRegularU` takes `hγδ : 0 < γ₀ − δ`,
`hpi : ∀ x, |⟨x,Δ′_π x⟩| ≤ δ‖x‖²`, and the unrestricted `h310` at `γ₀`. Those three ALONE are
contradictory: `hpi` forces `δ ≥ 0` (evaluate at any nonzero vector), `hγδ` then forces `γ₀ > 0`,
and §6 kills `h310` at every positive `γ₀`.

The remaining hypotheses (`hPiSym`, `hPsym`, `ha`, `hPpos`) are not needed for the contradiction
and are not used below. -/

/-- **THE FLAGSHIP INSTANTIATION'S HYPOTHESES CANNOT BE JOINTLY SATISFIED.** Three of the
hypotheses of `BridgeInverse.bridge_source_chain_at_curvedRegularU`, verbatim, yield `False`. -/
theorem bridge_source_chain_at_curvedRegularU_hypotheses_unsatisfiable
    (DeltaPrimePi : BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5 →L[ℝ]
      BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5)
    (γ₀ δ : ℝ) (hγδ : 0 < γ₀ - δ)
    (h310 : ∀ A : Bond AdalyFormal.Balaban.RegularUDomainWitness.witL5 → SuTwo,
      γ₀ * ‖(WithLp.toLp 2 A :
            BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5)‖ ^ 2
        ≤ deltaKQuadFormNormalizedCorrected
            AdalyFormal.Balaban.CoercivityRegular.curvedRegularU A)
    (hpi : ∀ x : BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5,
      |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2) :
    False := by
  set v : BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5 :=
    WithLp.toLp 2 (dirConstField (L := AdalyFormal.Balaban.RegularUDomainWitness.witL5)
      (0 : Fin 3) suTwoWitness) with hvdef
  have hvpos : 0 < ‖v‖ := norm_toLp_dirConstField_pos (0 : Fin 3) suTwoWitness suTwoWitness_ne_zero
  have hdelta : 0 ≤ δ := by
    have h := hpi v
    have habs : (0 : ℝ) ≤ |(inner ℝ v (DeltaPrimePi v) : ℝ)| := abs_nonneg _
    have hsq : 0 < ‖v‖ ^ 2 := pow_pos hvpos 2
    have hprod : (0 : ℝ) ≤ δ * ‖v‖ ^ 2 := le_trans habs h
    nlinarith [hprod, hsq]
  exact h310_unrestricted_impossible_at_curvedRegularU γ₀ (by linarith) h310

/-- **THE TYPE-IDENTITY CHECK.** The previous theorem is only worth anything if the `h310` it
refutes is LITERALLY the `h310` slot of `BridgeInverse.bridge_source_chain_at_curvedRegularU` and
not a look-alike. This declaration settles that by construction: it takes the flagship's ENTIRE
hypothesis list, FEEDS it to the flagship (the unused `hreal`, which forces the elaborator to accept
our `h310` binder in the flagship's slot — if the two types differed this file would not compile),
and then derives `False` from the same binders. So every application of
`bridge_source_chain_at_curvedRegularU` has contradictory hypotheses. -/
theorem flagship_application_is_vacuous
    (DeltaPrimePi P : BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5 →L[ℝ]
      BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5)
    (a γ₀ δ : ℝ)
    (hPiSym : ∀ u v : BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5,
      (inner ℝ u (DeltaPrimePi v) : ℝ) = (inner ℝ (DeltaPrimePi u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5,
      (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hγδ : 0 < γ₀ - δ) (ha : 0 ≤ a)
    (h310 : ∀ A : Bond AdalyFormal.Balaban.RegularUDomainWitness.witL5 → SuTwo,
      γ₀ * ‖(WithLp.toLp 2 A :
            BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5)‖ ^ 2
        ≤ deltaKQuadFormNormalizedCorrected
            AdalyFormal.Balaban.CoercivityRegular.curvedRegularU A)
    (hpi : ∀ x : BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5,
      |(inner ℝ x (DeltaPrimePi x) : ℝ)| ≤ δ * ‖x‖ ^ 2)
    (hPpos : ∀ x : BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5,
      (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (B : (LinearMap.range (AdalyFormal.Balaban.BridgeInverse.qCLM
      AdalyFormal.Balaban.CoercivityRegular.curvedRegularU 2 :
        BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5 →ₗ[ℝ]
          AdalyFormal.Balaban.BridgeInverse.CoarseFnL2
            AdalyFormal.Balaban.RegularUDomainWitness.witL5 2))) :
    False := by
  have hreal := AdalyFormal.Balaban.BridgeInverse.bridge_source_chain_at_curvedRegularU
    DeltaPrimePi P a γ₀ δ hPiSym hPsym hγδ ha h310 hpi hPpos B
  clear hreal
  exact bridge_source_chain_at_curvedRegularU_hypotheses_unsatisfiable
    DeltaPrimePi γ₀ δ hγδ h310 hpi

/-- The same conclusion phrased on `BridgeInverse.hDP_of_source_chain`'s own hypothesis list: at
`curvedRegularU` the `hDP` it produces is derived from an unsatisfiable premise. -/
theorem hDP_of_source_chain_at_curvedRegularU_premise_unsatisfiable
    (γ₀ : ℝ) (hγ₀ : 0 < γ₀)
    (h310 : ∀ A : Bond AdalyFormal.Balaban.RegularUDomainWitness.witL5 → SuTwo,
      γ₀ * ‖(WithLp.toLp 2 A :
            BondFnL2 AdalyFormal.Balaban.RegularUDomainWitness.witL5)‖ ^ 2
        ≤ deltaKQuadFormNormalizedCorrected
            AdalyFormal.Balaban.CoercivityRegular.curvedRegularU A) :
    False :=
  h310_unrestricted_impossible_at_curvedRegularU γ₀ hγ₀ h310

/-! ## §8 — CONTROLS: the hypothesis is load-bearing and the vanishing is not automatic

Two things must be excluded before any of the above counts as evidence.

**(a) MUST-FIRE — `AxisCompatible` is not decoration.** (Stated precisely: what fails at
`mutBadU` is `AxisCompatible mutBadU 0 suTwoWitness` — the hypothesis AT THE DIRECTION `d = 0`.
`mutBadU` is itself a single-active-bond background, so by `h310_unrestricted_impossible_at_bondU`
its `h310` is refuted too, at `d = 1`. The control is about the LEMMA's hypothesis being
load-bearing, not about `mutBadU` escaping the refutation.) `mutBadU` below is the same
single-active-bond family with the active bond moved to direction `1` and the group element set to
`witnessMElem` (whose adjoint action sends `suTwoWitness ↦ −suTwoWitness`,
`CovariantOperators.RMap_witnessMElem`). It FAILS `AxisCompatible _ 0 suTwoWitness`, and on it the
conclusion of `curl_dirConstField_eq_zero` is FALSE at an explicit plaquette: the curl is
`2·suTwoWitness ≠ 0`. Drop the hypothesis and the lemma is false.

**(b) MUST-NOT-FIRE — the vanishing is a property of the FIELD, not of the form.** On that same
mutated background the `D*D` half is STRICTLY POSITIVE on the very same constant field. So
`dstarDQuadForm_dirConstField_eq_zero` is not an identity about `dirConstField` alone.

**(c) SCOPE.** Nothing in this module touches any `W`-restricted (3.10) statement. The null field
is nonzero on EVERY direction-`0` bond, so it is not in any of the campaign's restricted domains,
and `RecursiveBridge.bridge_from_fine_operator`'s `W`-restricted hypothesis is untouched. Nothing
in this module mentions one. -/

/-- The mutated background: `witnessMElem` on one bond of direction `1`, `1` elsewhere. -/
noncomputable def mutBadU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdalyFormal.Balaban.RegularUDomainWitness.witL5 :=
  AdalyFormal.Balaban.RegularUCurvedWitness.bondU
    (AdalyFormal.Balaban.RegularUDomainWitnessGeneralU.siteZero
      AdalyFormal.Balaban.RegularUDomainWitness.witL5, (1 : Fin 3))
    AdalyFormal.Balaban.CovariantOperators.witnessMElem

/-- **(a) the hypothesis CAN fail.** -/
theorem mutBadU_not_axisCompatible :
    ¬ AxisCompatible mutBadU (0 : Fin 3) suTwoWitness := by
  intro hax
  have h := hax (AdalyFormal.Balaban.RegularUDomainWitnessGeneralU.siteZero
      AdalyFormal.Balaban.RegularUDomainWitness.witL5, (1 : Fin 3)) (by decide)
  rw [show mutBadU (AdalyFormal.Balaban.RegularUDomainWitnessGeneralU.siteZero
        AdalyFormal.Balaban.RegularUDomainWitness.witL5, (1 : Fin 3))
      = AdalyFormal.Balaban.CovariantOperators.witnessMElem from
    AdalyFormal.Balaban.RegularUCurvedWitness.bondU_at _ _,
    AdalyFormal.Balaban.CovariantOperators.RMap_witnessMElem] at h
  have h2 : (2 : ℝ) • (suTwoWitness : SuTwo) = 0 := by
    rw [two_smul]
    have hstep := congrArg (fun z : SuTwo => z + suTwoWitness) h
    simpa using hstep.symm
  rcases smul_eq_zero.1 h2 with h3 | h3
  · norm_num at h3
  · exact suTwoWitness_ne_zero h3

/-- The plaquette at which the mutation is exhibited: base site `0`, directions `(0,1)`. -/
noncomputable def mutBadPlaq :
    PeriodicLatticePlaquette AdalyFormal.Balaban.RegularUDomainWitness.witL5 :=
  (AdalyFormal.Balaban.RegularUDomainWitnessGeneralU.siteZero
    AdalyFormal.Balaban.RegularUDomainWitness.witL5,
   AdalyFormal.Balaban.RegularUCurvedWitness.dir01)

/-- **(a) the conclusion FAILS without the hypothesis**: the curl of the very same constant field
is `2·suTwoWitness ≠ 0` on `mutBadU`. -/
theorem curl_dirConstField_ne_zero_at_mutBadU :
    curlValueCovariant mutBadU (dirConstField (0 : Fin 3) suTwoWitness) mutBadPlaq
      = (2 : ℝ) • (suTwoWitness : SuTwo) := by
  show dirConstField (0 : Fin 3) suTwoWitness (mutBadPlaq.1, mutBadPlaq.2.1.1)
      + RMap (mutBadU (mutBadPlaq.1, mutBadPlaq.2.1.1))
          (dirConstField (0 : Fin 3) suTwoWitness
            (AdalyFormal.Target.ClayStatement.periodicLatticeShift mutBadPlaq.1 mutBadPlaq.2.1.1,
              mutBadPlaq.2.1.2))
      - RMap (mutBadU (mutBadPlaq.1, mutBadPlaq.2.1.2))
          (dirConstField (0 : Fin 3) suTwoWitness
            (AdalyFormal.Target.ClayStatement.periodicLatticeShift mutBadPlaq.1 mutBadPlaq.2.1.2,
              mutBadPlaq.2.1.1))
      - dirConstField (0 : Fin 3) suTwoWitness (mutBadPlaq.1, mutBadPlaq.2.1.2)
      = (2 : ℝ) • (suTwoWitness : SuTwo)
  have hmu : mutBadPlaq.2.1.1 = (0 : Fin 3) := rfl
  have hnu : mutBadPlaq.2.1.2 = (1 : Fin 3) := rfl
  have hU1 : mutBadU (mutBadPlaq.1, (1 : Fin 3))
      = AdalyFormal.Balaban.CovariantOperators.witnessMElem :=
    AdalyFormal.Balaban.RegularUCurvedWitness.bondU_at _ _
  rw [dirConstField_dir, dirConstField_dir, dirConstField_dir, dirConstField_dir,
    hmu, hnu, if_pos rfl, if_neg (by decide : ¬ (1 : Fin 3) = 0), map_zero, hU1,
    AdalyFormal.Balaban.CovariantOperators.RMap_witnessMElem, two_smul]
  abel

theorem curl_dirConstField_ne_zero_at_mutBadU' :
    curlValueCovariant mutBadU (dirConstField (0 : Fin 3) suTwoWitness) mutBadPlaq ≠ 0 := by
  rw [curl_dirConstField_ne_zero_at_mutBadU]
  intro hcon
  rcases smul_eq_zero.1 hcon with h | h
  · norm_num at h
  · exact suTwoWitness_ne_zero h

/-- **(b) the `D*D` half is STRICTLY POSITIVE on the same constant field over the mutated
background** — so §2's vanishing is not an identity about `dirConstField`. -/
theorem dstarDQuadForm_dirConstField_pos_at_mutBadU :
    0 < dstarDQuadForm mutBadU (dirConstField (0 : Fin 3) suTwoWitness) := by
  have hterm : 0 < hsInner (curlValueCovariant mutBadU
      (dirConstField (0 : Fin 3) suTwoWitness) mutBadPlaq)
      (curlValueCovariant mutBadU (dirConstField (0 : Fin 3) suTwoWitness) mutBadPlaq) := by
    rcases (AdalyFormal.Balaban.SuTwoInner.hsInner_self_nonneg
      (curlValueCovariant mutBadU (dirConstField (0 : Fin 3) suTwoWitness) mutBadPlaq)).lt_or_eq
      with h | h
    · exact h
    · exact absurd (AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_zero h.symm)
        curl_dirConstField_ne_zero_at_mutBadU'
  have hle : hsInner (curlValueCovariant mutBadU
      (dirConstField (0 : Fin 3) suTwoWitness) mutBadPlaq)
      (curlValueCovariant mutBadU (dirConstField (0 : Fin 3) suTwoWitness) mutBadPlaq)
      ≤ dstarDQuadForm mutBadU (dirConstField (0 : Fin 3) suTwoWitness) := by
    unfold dstarDQuadForm covPlaqInner
    exact Finset.single_le_sum
      (fun q _ => AdalyFormal.Balaban.SuTwoInner.hsInner_self_nonneg _)
      (Finset.mem_univ mutBadPlaq)
  linarith

/-! ## §9 — axiom audit -/

#print axioms dirConstField
#print axioms dirConstField_dir
#print axioms AxisCompatible
#print axioms axisCompatible_of_trivial_off_dir
#print axioms curl_dirConstField_eq_zero
#print axioms dstarDQuadForm_dirConstField_eq_zero
#print axioms commutatorMatrixSum_eq_zero_of_a2a4_zero
#print axioms commutatorMatrixSum_eq_zero_of_a1a3_zero
#print axioms commutatorMatrixSum_dirConstField_eq_zero
#print axioms deltaPrimePlaqTerm_dirConstField_eq_zero
#print axioms deltaPrimeQuadForm_dirConstField_eq_zero
#print axioms deltaKQuadFormNormalizedCorrected_dirConstField_eq_zero
#print axioms toLp_dirConstField_ne_zero
#print axioms norm_toLp_dirConstField_pos
#print axioms h310_unrestricted_impossible_of_axisCompatible
#print axioms curvedRegularU_trivial_off_dir0
#print axioms axisCompatible_curvedRegularU
#print axioms h310_unrestricted_impossible_at_curvedRegularU
#print axioms axisCompatible_bondU
#print axioms h310_unrestricted_impossible_at_bondU
#print axioms witnessU_trivial_off_dir0
#print axioms h310_unrestricted_impossible_at_witnessU'
#print axioms h310_unrestricted_impossible_at_trivialU
#print axioms bridge_source_chain_at_curvedRegularU_hypotheses_unsatisfiable
#print axioms flagship_application_is_vacuous
#print axioms hDP_of_source_chain_at_curvedRegularU_premise_unsatisfiable
#print axioms mutBadU
#print axioms mutBadU_not_axisCompatible
#print axioms mutBadPlaq
#print axioms curl_dirConstField_ne_zero_at_mutBadU
#print axioms curl_dirConstField_ne_zero_at_mutBadU'
#print axioms dstarDQuadForm_dirConstField_pos_at_mutBadU

end AdalyFormal.Balaban.H310Satisfiability
