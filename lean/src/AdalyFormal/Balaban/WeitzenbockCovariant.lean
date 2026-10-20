/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Weitzenbock
import AdalyFormal.Balaban.LemmaAssembly

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `WeitzenbockCovariant.lean` — the COVARIANT discrete Weitzenböck identity, with the defect
written in HOLONOMIES, and the proof that this defect is **NOT** Bałaban's `Δ′`

## What this file was dispatched to do, and what it found

`Balaban/Weitzenbock.lean` proves the FLAT energy identity `plaqEnergy(curl₁A) + divEnergy₁A =
gradEnergy A` exactly, and its lane localised the obstruction at a general background `U` to the
single far-corner summation-by-parts term (`E4`). `Balaban/LemmaAssembly.lean` proves
`|deltaPrimeQuadForm U A| ≤ 16α₀·dstarDQuadForm U A + 576α₀·bondEnergy A`. Two lanes' PROSE then
identified the `E4` defect with `Δ′` (`compute/weitzenbock/PROGRESS.md` Step 11: *"That is Balaban's
Delta' (CMP99b eq. 3.10) in this presentation"*).

**That identification is FALSE, and §6 proves it in the kernel.** The two objects are different
functionals of `(U, A)`. The separation is not delicate:

* `weitzDefect` (§1) is a sum over sites × ORDERED direction pairs of a pairing of the two
  *transverse-shifted diagonal bond values* `A(y+e_ν, μ)` and `A(y+e_μ, ν)` against the DIFFERENCE
  of the two corner transport words. It therefore VANISHES IDENTICALLY, at every background `U`, on
  every field supported in a single lattice direction
  (`weitzDefect_eq_zero_of_single_direction`) — the two slots need `A_μ ≠ 0` and `A_ν ≠ 0` with
  `μ ≠ ν`.
* `DeltaPrime.deltaPrimeQuadForm` is a sum over PLAQUETTES of `Re tr(curl²·(Re U(∂p) − 1))` plus a
  commutator term, and it is NOT zero on a single-direction field: the tree's own witness
  (`DeltaPrime.deltaPrimeQuadForm_witnessU_deltaWitnessConfig_eq`) evaluates it to `8` on
  `deltaWitnessConfig`, which is supported on the SINGLE bond `(witnessY, 0)`.

`weitzDefect witnessU deltaWitnessConfig = 0 ≠ 8 = deltaPrimeQuadForm witnessU deltaWitnessConfig`
(`weitzDefect_ne_deltaPrimeQuadForm`). The two decompositions are different decompositions:
`grad = curl + div (+ defect)` is a WEITZENBÖCK decomposition of the gradient energy, whereas
`Δ = D*D + Δ′` (CMP99b (3.10)) splits the SECOND VARIATION OF THE WILSON ACTION into its curl part
and the remainder — `dstarDQuadForm`, i.e. `D*D`, is itself the curl energy
(`LemmaAssembly.dstarDQuadForm_eq_sum_norm_sq`), which is the term the Weitzenböck identity has on
its LEFT. Nothing in this file consumes `abs_deltaPrimeQuadForm_le`, and it must not be used to
absorb this defect. The defect is bounded here by its OWN argument (§7), which needs only the
per-bond regularity `frobSupBond U ≤ α` and produces `72·α·bondEnergy A` — no `dstarDQuadForm`
term at all.

## What is proved here

* §0 the transport algebra (`R` is an `hsInner` isometry and a homomorphism, so every transport can
  be pushed into the second slot of the pairing).
* §1 the covariant objects: `dcov`, `ubkcov`, `Xcov`, `Ccov`, `gradEnergyCov`, `divCross`, the two
  CORNER WORDS `cornerWordFst U μ ν y = U(y+e_ν,μ)·U(y+e_μ,ν)⁻¹` and
  `cornerWordSnd U μ ν y = U(y,ν)⁻¹·U(y,μ)`, the per-site `defectTerm`, and `weitzDefect`.
  **No object here is defined as `LHS − RHS`.**
* §2 the covariant curl is still the antisymmetrised covariant difference (no curvature), so the
  curl energy expands exactly as in the flat case.
* §3 **`covariant_sbp`** : `divCross U A μ ν = Ccov U A μ ν + ∑_y defectTerm U A μ ν y`, for every
  ORDERED pair and every extent. Three of the four summation-by-parts terms match verbatim under
  transports; the far-corner term differs by the corner-word difference, and that is the whole
  defect.
* §4 **`weitzenbock_cov`** : `plaqEnergy(curl_U A) + divEnergy U A = gradEnergyCov U A +
  weitzDefect U A`.
* §5 the controls: the defect vanishes on the DIAGONAL `μ = ν`; at `U ≡ 1`, recovering
  `Weitzenbock.weitzenbock_flat` verbatim (`weitzenbock_cov_recovers_flat` — the must-fire control);
  and, more generally, whenever the plaquette word acts trivially in the adjoint representation
  (which includes the CENTRAL case `U(∂p) = −1`), because
  `cornerWordSnd = U(y,ν)⁻¹·U(∂p)·U(y,ν)·cornerWordFst`.
* §6 the SEPARATION from `Δ′` described above.
* §7 **`abs_weitzDefect_le`** : `|weitzDefect U A| ≤ 72·α·bondEnergy A` when
  `frobSupBond U ≤ α`. Constant composition: `72 = 9 · 2 · 2 · 2` = (ordered direction pairs) ×
  (two corner words) × (`RMapLipschitz.norm_RMap_sub_self_le`'s Lipschitz factor `2`) × (the `2α`
  Frobenius bound on a two-bond word). No lattice size, no scale, no `k`.
* §8 gauge covariance of all four terms of the identity, hence gauge INVARIANCE of the defect
  (derived from the identity, not assumed), hence **`abs_weitzDefect_le_of_gaugeRegular`** under
  `AlphaAnalyticity.GaugeRegular α₀ U`, and the TWO-SIDED covariant identity
  `|plaqEnergy(curl_U A) + divEnergy U A − gradEnergyCov U A| ≤ 72α₀·bondEnergy A`.
* §9 the payoff chain, stated exactly as far as it reaches: on the covariant divergence-free
  surface, `gradEnergyCov U A − 72α₀·bondEnergy A ≤ plaqEnergy(curl_U A)`, hence a general-`U`
  fixed-level div-free Poincaré from ANY covariant gradient Poincaré at the same level
  (`kerQDivFreePoincareAtLevel_of_covGradPoincare`); plus the measured comparison
  `gradEnergy A ≤ 2·gradEnergyCov U A + 24α²·bondEnergy A` and the exact statement of the ONE
  remaining input needed to run `Weitzenbock.gradPoincareOnKerQAtLevel_two` at general `U`.

## Normalisation, pinned RELATIVELY (not each summand against itself)

Every squared norm in this file is the `hsInner`-induced one, exactly as in `Weitzenbock.lean`
(`Weitzenbock.norm_sq_eq_hsInner`), and `plaqEnergy`/`bondEnergy` are the tree's own sums of it.
`plaqEnergy` runs over the THREE UNORDERED pairs `μ < ν` with NO `1/2`; `gradEnergyCov` runs over
all NINE ORDERED pairs; `weitzDefect` runs over all NINE ORDERED pairs. The relative normalisation
of the four summands is gated in §5 by `weitzenbock_cov_recovers_flat`, which derives
`Weitzenbock.weitzenbock_flat`'s EXACT statement (an equality with no free constant) from
`weitzenbock_cov` — put a `1/2` on any one of the four summands and that derivation fails.
`deltaPrimeQuadForm`'s own normalisation is a SEPARATE question (`DeltaPrime.lean`'s conviction
banner: those terms use raw `Matrix.trace`, so they are twice the source-normalised `Δ′`) and it
does not enter here, because §6 shows the objects differ by more than any factor: one of them is
identically zero on a family where the other is not.

## LAW-19 disclosure

Measured before writing (exact-word grep, tree-wide): `dcov`, `gradEnergyCov`, `weitzDefect`,
`cornerWord`, `divCross`, `ubkcov`, `Xcov`, `Ccov` — zero hits outside this file. Reused rather
than rebuilt: `CovariantOperators.RMap_mul_apply`/`RMap_one`, `SuTwoInner.hsInner_RMap`,
`Weitzenbock.shift_shift_comm`/`shift_shiftBack_comm'`/`sum_plaqDirs`/`divEnergy`/`gradEnergy`/
`dfwd`/`divEnergy_eq_zero_of_div_free`, `CovariantHjMinimizer.periodicLatticeShift_shiftBack`/
`periodicLatticeShiftBack_shift`/`periodicLatticeShiftEquiv`, `RMapLipschitz.norm_RMap_sub_self_le`/
`frobNorm_sq`/`frobSq_nonneg`, `LemmaAssembly.frobSq_inv_sub_one`/`frobSq_mul_sub_one_le`,
`RegularUPerturbation.frobNorm_le_frobSupBond`/`frobSupBond_nonneg`, `AlphaAnalyticity.norm_RMap`/
`bondEnergy_gauge`/`GaugeRegular`/`curlValueCovariant_gauge`/`gaugeActA`,
`ClayStatement.periodicGaugeTransform`/`periodicPlaquetteHolonomy`,
`DeltaPrime.deltaPrimeQuadForm_witnessU_deltaWitnessConfig_eq`.
-/

namespace AdalyFormal.Balaban.WeitzenbockCovariant

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer
  (trivialU gradCovariantAdjointValue periodicLatticeShiftBack periodicLatticeShift_shiftBack
    periodicLatticeShiftBack_shift periodicLatticeShiftEquiv)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.Weitzenbock (dfwd gradEnergy divEnergy shiftVec3 Tloc Xt)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — the transport algebra: moving `R` across the inner product

Four facts, all consequences of `SuTwoInner.hsInner_RMap` (`R` is an `hsInner` isometry) and
`CovariantOperators.RMap_mul_apply` (`R` is a homomorphism). They are what makes the covariant
summation by parts run: every transport can be pushed into the SECOND slot of the pairing, where it
becomes a single group element. -/

theorem inner_RMap (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X Y : SuTwo) :
    inner ℝ (RMap g X) (RMap g Y) = inner ℝ X Y := by
  rw [inner_eq_hsInner, inner_eq_hsInner]
  exact hsInner_RMap g X Y

theorem RMap_apply_inv_apply (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    RMap g (RMap g⁻¹ X) = X := by
  rw [RMap_mul_apply, mul_inv_cancel, RMap_one]
  rfl

theorem RMap_inv_apply_apply (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    RMap g⁻¹ (RMap g X) = X := by
  rw [RMap_mul_apply, inv_mul_cancel, RMap_one]
  rfl

/-- Move a transport from the LEFT slot to the right one, inverted. -/
theorem inner_RMap_left (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X Y : SuTwo) :
    inner ℝ (RMap g X) Y = inner ℝ X (RMap g⁻¹ Y) := by
  rw [← inner_RMap g X (RMap g⁻¹ Y), RMap_apply_inv_apply]

/-- Two transports collapse into ONE, in the right slot: `⟪R(a)X, R(b)Y⟫ = ⟪X, R(a⁻¹b)Y⟫`. -/
theorem inner_RMap_pair (a b : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X Y : SuTwo) :
    inner ℝ (RMap a X) (RMap b Y) = inner ℝ X (RMap (a⁻¹ * b) Y) := by
  rw [inner_RMap_left, RMap_mul_apply]

#print axioms inner_RMap
#print axioms RMap_apply_inv_apply
#print axioms RMap_inv_apply_apply
#print axioms inner_RMap_left
#print axioms inner_RMap_pair

/-! ## §1 — the covariant objects, and the DEFECT written in holonomies -/

/-- **`(∂^U_μ A_ν)(y) := R(U(y,μ))·A(y+e_μ, ν) − A(y,ν)`** — the covariant forward difference, over
ALL ordered pairs `(μ,ν)`. Reduces to `Weitzenbock.dfwd` at `U ≡ 1` (§5). -/
noncomputable def dcov (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : SuTwo :=
  RMap (U (y, μ)) (A (periodicLatticeShift y μ, ν)) - A (y, ν)

/-- **`(∂^{U,−}_μ A_μ)(y) := R(U(y−e_μ,μ)⁻¹)·A(y−e_μ,μ) − A(y,μ)`** — the `μ`-summand of the
tree's covariant divergence `gradCovariantAdjointValue`, definitionally. -/
noncomputable def ubkcov (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ : Fin 3) (y : PeriodicLatticeSite L) : SuTwo :=
  RMap (U (periodicLatticeShiftBack y μ, μ))⁻¹ (A (periodicLatticeShiftBack y μ, μ)) - A (y, μ)

theorem gradCovariantAdjointValue_eq_sum_ubkcov
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) :
    gradCovariantAdjointValue U A y = ∑ μ : Fin 3, ubkcov U A μ y := rfl

/-- `Xcov U A μ ν := ∑_y ‖(∂^U_μ A_ν)(y)‖²`. -/
noncomputable def Xcov (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) : ℝ :=
  ∑ y : PeriodicLatticeSite L, ‖dcov U A μ ν y‖ ^ 2

/-- `Ccov U A μ ν := ∑_y ⟪(∂^U_μ A_ν)(y), (∂^U_ν A_μ)(y)⟫` — the covariant cross term. -/
noncomputable def Ccov (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) : ℝ :=
  ∑ y : PeriodicLatticeSite L, inner ℝ (dcov U A μ ν y) (dcov U A ν μ y)

/-- **The covariant gradient energy** `∑_y ∑_μ ∑_ν ‖(∂^U_μ A_ν)(y)‖²`, all NINE ordered pairs, no
combinatorial factor. -/
noncomputable def gradEnergyCov
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  ∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, ‖dcov U A μ ν y‖ ^ 2

/-- `divCross U A μ ν := ∑_y ⟪(∂^{U,−}_μ A_μ)(y), (∂^{U,−}_ν A_ν)(y)⟫`. -/
noncomputable def divCross (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) : ℝ :=
  ∑ y : PeriodicLatticeSite L, inner ℝ (ubkcov U A μ y) (ubkcov U A ν y)

/-- **THE FIRST CORNER WORD** `h₁(y,μ,ν) := U(y+e_ν, μ)·U(y+e_μ, ν)⁻¹` — the transport the
DIVERGENCE side puts between the two far-corner bond values `A(y+e_ν,μ)` and `A(y+e_μ,ν)`. -/
noncomputable def cornerWordFst
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (μ ν : Fin 3)
    (y : PeriodicLatticeSite L) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  U (periodicLatticeShift y ν, μ) * (U (periodicLatticeShift y μ, ν))⁻¹

/-- **THE SECOND CORNER WORD** `h₂(y,μ,ν) := U(y,ν)⁻¹·U(y,μ)` — the transport the CURL side puts
between the same two bond values. The two words traverse the plaquette in opposite senses; §5 shows
they differ by the plaquette holonomy conjugated to the base point. -/
noncomputable def cornerWordSnd
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (μ ν : Fin 3)
    (y : PeriodicLatticeSite L) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  (U (y, ν))⁻¹ * U (y, μ)

/-- **THE DEFECT DENSITY** — `⟪A(y+e_ν,μ), (R(h₁) − R(h₂))·A(y+e_μ,ν)⟫`. Written in the two corner
words, NOT as a difference of the two sides of the identity: it is an explicit holonomy pairing of
two raw bond values, and §5/§6/§7 all read their properties off that explicit form. -/
noncomputable def defectTerm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : ℝ :=
  inner ℝ (A (periodicLatticeShift y ν, μ))
    (RMap (cornerWordFst U μ ν y) (A (periodicLatticeShift y μ, ν))
      - RMap (cornerWordSnd U μ ν y) (A (periodicLatticeShift y μ, ν)))

/-- **THE DEFECT** — summed over all sites and all NINE ordered direction pairs (the diagonal
`μ = ν` contributes `0`, §5). -/
noncomputable def weitzDefect
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  ∑ μ : Fin 3, ∑ ν : Fin 3, ∑ y : PeriodicLatticeSite L, defectTerm U A μ ν y

#print axioms gradCovariantAdjointValue_eq_sum_ubkcov

/-! ## §2 — the covariant curl energy in terms of `Xcov` and `Ccov`

The covariant curl is STILL the antisymmetrised covariant difference — no curvature enters here.
This is the fact `compute/weitzenbock/PROGRESS.md` Step 11 records, re-derived. -/

theorem curl_eq_dcov_sub (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    curlValueCovariant U A p = dcov U A p.2.1.1 p.2.1.2 p.1 - dcov U A p.2.1.2 p.2.1.1 p.1 := by
  unfold curlValueCovariant dcov
  abel

theorem plaqEnergy_curl_cov (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    plaqEnergy (curlCovariantLM U A) =
      ∑ d : PeriodicPlaquetteDirections,
        (Xcov U A d.1.1 d.1.2 + Xcov U A d.1.2 d.1.1 - 2 * Ccov U A d.1.1 d.1.2) := by
  unfold AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy
  have hcoe : ∀ p : PeriodicLatticePlaquette L,
      curlCovariantLM U A p = curlValueCovariant U A p := fun _ => rfl
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => by
    rw [hcoe p, curl_eq_dcov_sub U A p]]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hterm : ∀ y : PeriodicLatticeSite L,
      ‖dcov U A ((y, d) : PeriodicLatticePlaquette L).2.1.1
          ((y, d) : PeriodicLatticePlaquette L).2.1.2 ((y, d) : PeriodicLatticePlaquette L).1
        - dcov U A ((y, d) : PeriodicLatticePlaquette L).2.1.2
            ((y, d) : PeriodicLatticePlaquette L).2.1.1
            ((y, d) : PeriodicLatticePlaquette L).1‖ ^ 2
      = ‖dcov U A d.1.1 d.1.2 y‖ ^ 2 + ‖dcov U A d.1.2 d.1.1 y‖ ^ 2
        - 2 * inner ℝ (dcov U A d.1.1 d.1.2 y) (dcov U A d.1.2 d.1.1 y) := by
    intro y
    show ‖dcov U A d.1.1 d.1.2 y - dcov U A d.1.2 d.1.1 y‖ ^ 2 = _
    rw [norm_sub_sq_real]
    ring
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hterm y]
  unfold Xcov Ccov
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem Ccov_symm (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) : Ccov U A μ ν = Ccov U A ν μ := by
  unfold Ccov
  exact Finset.sum_congr rfl fun y _ => real_inner_comm _ _

theorem Ccov_diag (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ : Fin 3) : Ccov U A μ μ = Xcov U A μ μ := by
  unfold Ccov Xcov
  exact Finset.sum_congr rfl fun y _ => real_inner_self_eq_norm_sq _

theorem gradEnergyCov_eq_sum_Xcov
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    gradEnergyCov U A = ∑ μ : Fin 3, ∑ ν : Fin 3, Xcov U A μ ν := by
  unfold gradEnergyCov Xcov
  calc ∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, ‖dcov U A μ ν y‖ ^ 2
      = ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite L, ∑ ν : Fin 3, ‖dcov U A μ ν y‖ ^ 2 :=
        Finset.sum_comm
    _ = ∑ μ : Fin 3, ∑ ν : Fin 3, ∑ y : PeriodicLatticeSite L, ‖dcov U A μ ν y‖ ^ 2 :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_comm

theorem divEnergy_eq_sum_divCross
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    divEnergy U A = ∑ μ : Fin 3, ∑ ν : Fin 3, divCross U A μ ν := by
  unfold AdalyFormal.Balaban.Weitzenbock.divEnergy
  have hterm : ∀ y : PeriodicLatticeSite L,
      ‖gradCovariantAdjointValue U A y‖ ^ 2
        = ∑ μ : Fin 3, ∑ ν : Fin 3, (inner ℝ (ubkcov U A μ y) (ubkcov U A ν y) : ℝ) := by
    intro y
    rw [gradCovariantAdjointValue_eq_sum_ubkcov, ← real_inner_self_eq_norm_sq, sum_inner]
    exact Finset.sum_congr rfl fun μ _ => inner_sum _ _ _
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hterm y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  rfl

theorem gradEnergyCov_nonneg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : 0 ≤ gradEnergyCov U A := by
  unfold gradEnergyCov
  exact Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ =>
    sq_nonneg _

#print axioms curl_eq_dcov_sub
#print axioms plaqEnergy_curl_cov
#print axioms Ccov_symm
#print axioms Ccov_diag
#print axioms gradEnergyCov_eq_sum_Xcov
#print axioms divEnergy_eq_sum_divCross
#print axioms gradEnergyCov_nonneg

/-! ## §3 — THE COVARIANT SUMMATION BY PARTS, and where exactly it breaks

Four terms per side. Written in the normal form "raw bond value in the left slot, a single group
word in the right slot" (§0), with `y⁻μ := y − e_μ`:

LEFT (`divCross`, at site `y`) — `lTerm1 − lTerm2 − lTerm3 + lTerm4` with

* `lTerm1 = ⟪A(y⁻μ,μ), R(U(y⁻μ,μ)·U(y⁻ν,ν)⁻¹) A(y⁻ν,ν)⟫`
* `lTerm2 = ⟪A(y⁻μ,μ), R(U(y⁻μ,μ)) A(y,ν)⟫`
* `lTerm3 = ⟪A(y,μ), R(U(y⁻ν,ν)⁻¹) A(y⁻ν,ν)⟫`
* `lTerm4 = ⟪A(y,μ), A(y,ν)⟫`

RIGHT (`Ccov`, at site `y`) — `rTerm1 − rTerm2 − rTerm3 + rTerm4` with

* `rTerm1 = ⟪A(y+e_μ,ν), R(U(y,μ)⁻¹·U(y,ν)) A(y+e_ν,μ)⟫`
* `rTerm2 = ⟪A(y+e_μ,ν), R(U(y,μ)⁻¹) A(y,μ)⟫`
* `rTerm3 = ⟪A(y,ν), R(U(y,ν)) A(y+e_ν,μ)⟫`
* `rTerm4 = ⟪A(y,ν), A(y,μ)⟫`

`∑lTerm4 = ∑rTerm4` by symmetry of the real inner product; `∑lTerm2 = ∑rTerm2` and
`∑lTerm3 = ∑rTerm3` by ONE site reindexing each plus one transport move — the transports SURVIVE.
`∑lTerm1 − ∑rTerm1` does NOT vanish: after the DOUBLE reindexing `y ↦ y − e_μ − e_ν` both terms
pair the SAME two bond values `A(y+e_ν,μ)` and `A(y+e_μ,ν)`, but through the two different corner
words. That difference is `defectTerm`. -/

noncomputable def lTerm1 (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : ℝ :=
  inner ℝ (A (periodicLatticeShiftBack y μ, μ))
    (RMap (U (periodicLatticeShiftBack y μ, μ) * (U (periodicLatticeShiftBack y ν, ν))⁻¹)
      (A (periodicLatticeShiftBack y ν, ν)))

noncomputable def lTerm2 (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : ℝ :=
  inner ℝ (A (periodicLatticeShiftBack y μ, μ))
    (RMap (U (periodicLatticeShiftBack y μ, μ)) (A (y, ν)))

noncomputable def lTerm3 (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : ℝ :=
  inner ℝ (A (y, μ))
    (RMap (U (periodicLatticeShiftBack y ν, ν))⁻¹ (A (periodicLatticeShiftBack y ν, ν)))

noncomputable def lTerm4 (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : ℝ :=
  inner ℝ (A (y, μ)) (A (y, ν))

noncomputable def rTerm1 (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : ℝ :=
  inner ℝ (A (periodicLatticeShift y μ, ν))
    (RMap ((U (y, μ))⁻¹ * U (y, ν)) (A (periodicLatticeShift y ν, μ)))

noncomputable def rTerm2 (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : ℝ :=
  inner ℝ (A (periodicLatticeShift y μ, ν)) (RMap (U (y, μ))⁻¹ (A (y, μ)))

noncomputable def rTerm3 (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : ℝ :=
  inner ℝ (A (y, ν)) (RMap (U (y, ν)) (A (periodicLatticeShift y ν, μ)))

noncomputable def rTerm4 (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) : ℝ :=
  inner ℝ (A (y, ν)) (A (y, μ))

/-- The LEFT expansion. -/
theorem inner_ubkcov_expand
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) :
    (inner ℝ (ubkcov U A μ y) (ubkcov U A ν y) : ℝ)
      = lTerm1 U A μ ν y - lTerm2 U A μ ν y - lTerm3 U A μ ν y + lTerm4 A μ ν y := by
  unfold ubkcov lTerm1 lTerm2 lTerm3 lTerm4
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_RMap_pair, inner_RMap_left]
  simp only [inv_inv]
  ring

/-- The RIGHT expansion. -/
theorem inner_dcov_expand
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) :
    (inner ℝ (dcov U A μ ν y) (dcov U A ν μ y) : ℝ)
      = rTerm1 U A μ ν y - rTerm2 U A μ ν y - rTerm3 U A μ ν y + rTerm4 A μ ν y := by
  unfold dcov rTerm1 rTerm2 rTerm3 rTerm4
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_RMap_pair, inner_RMap_left]
  ring

/-- **E1** (the diagonal-site term): symmetry of the real inner product, no reindexing. -/
theorem sum_lTerm4_eq (A : Bond L → SuTwo) (μ ν : Fin 3) :
    (∑ y : PeriodicLatticeSite L, lTerm4 A μ ν y)
      = ∑ y : PeriodicLatticeSite L, rTerm4 A μ ν y :=
  Finset.sum_congr rfl fun y _ => real_inner_comm _ _

/-- **E2**: one reindexing by the backward `μ`-shift, then the transport moves across. -/
theorem sum_lTerm2_eq (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) :
    (∑ y : PeriodicLatticeSite L, lTerm2 U A μ ν y)
      = ∑ y : PeriodicLatticeSite L, rTerm2 U A μ ν y := by
  refine Fintype.sum_equiv (periodicLatticeShiftEquiv (L := L) μ).symm _ _ fun y => ?_
  show lTerm2 U A μ ν y = rTerm2 U A μ ν (periodicLatticeShiftBack y μ)
  unfold lTerm2 rTerm2
  rw [periodicLatticeShift_shiftBack, ← inner_RMap_left]
  exact real_inner_comm _ _

/-- **E3**: one reindexing by the backward `ν`-shift, then the transport moves across. -/
theorem sum_lTerm3_eq (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) :
    (∑ y : PeriodicLatticeSite L, lTerm3 U A μ ν y)
      = ∑ y : PeriodicLatticeSite L, rTerm3 U A μ ν y := by
  refine Fintype.sum_equiv (periodicLatticeShiftEquiv (L := L) ν).symm _ _ fun y => ?_
  show lTerm3 U A μ ν y = rTerm3 U A μ ν (periodicLatticeShiftBack y ν)
  unfold lTerm3 rTerm3
  rw [periodicLatticeShift_shiftBack, ← inner_RMap_left]
  exact real_inner_comm _ _

/-- `rTerm1` in corner-word normal form: the same pairing as `lTerm1`'s reindexed form, but through
`cornerWordSnd`. -/
theorem rTerm1_eq_cornerWordSnd
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) :
    rTerm1 U A μ ν y
      = inner ℝ (A (periodicLatticeShift y ν, μ))
          (RMap (cornerWordSnd U μ ν y) (A (periodicLatticeShift y μ, ν))) := by
  unfold rTerm1 cornerWordSnd
  rw [show ((U (y, μ))⁻¹ * U (y, ν)) = ((U (y, ν))⁻¹ * U (y, μ))⁻¹ by
    rw [mul_inv_rev, inv_inv], ← inner_RMap_left]
  exact real_inner_comm _ _

/-- **E4 — THE DEFECT.** The far-corner term, reindexed by the DOUBLE backward shift
`y ↦ y − e_μ − e_ν`: both sides then pair the SAME two bond values, through the two corner words.
This is the ONLY place the two sides disagree, and the disagreement is exactly `defectTerm`. -/
theorem sum_lTerm1_eq (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) :
    (∑ y : PeriodicLatticeSite L, lTerm1 U A μ ν y)
      = (∑ y : PeriodicLatticeSite L, rTerm1 U A μ ν y)
        + ∑ y : PeriodicLatticeSite L, defectTerm U A μ ν y := by
  have hL : (∑ y : PeriodicLatticeSite L, lTerm1 U A μ ν y)
      = ∑ y : PeriodicLatticeSite L,
          (inner ℝ (A (periodicLatticeShift y ν, μ))
            (RMap (cornerWordFst U μ ν y) (A (periodicLatticeShift y μ, ν))) : ℝ) := by
    refine Fintype.sum_equiv
      ((periodicLatticeShiftEquiv (L := L) μ).symm.trans
        (periodicLatticeShiftEquiv (L := L) ν).symm) _ _ fun y => ?_
    show lTerm1 U A μ ν y
      = inner ℝ (A (periodicLatticeShift
            (periodicLatticeShiftBack (periodicLatticeShiftBack y μ) ν) ν, μ))
          (RMap (cornerWordFst U μ ν
              (periodicLatticeShiftBack (periodicLatticeShiftBack y μ) ν))
            (A (periodicLatticeShift
              (periodicLatticeShiftBack (periodicLatticeShiftBack y μ) ν) μ, ν)))
    have hs1 : periodicLatticeShift
        (periodicLatticeShiftBack (periodicLatticeShiftBack y μ) ν) ν
          = periodicLatticeShiftBack y μ := periodicLatticeShift_shiftBack _ _
    have hs2 : periodicLatticeShift
        (periodicLatticeShiftBack (periodicLatticeShiftBack y μ) ν) μ
          = periodicLatticeShiftBack y ν := by
      rw [AdalyFormal.Balaban.Weitzenbock.shift_shiftBack_comm'
        (periodicLatticeShiftBack y μ) μ ν, periodicLatticeShift_shiftBack]
    unfold lTerm1 cornerWordFst
    rw [hs1, hs2]
  rw [hL]
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => rTerm1_eq_cornerWordSnd U A μ ν y]
  unfold defectTerm
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => inner_sub_right
    (𝕜 := ℝ) (A (periodicLatticeShift y ν, μ))
    (RMap (cornerWordFst U μ ν y) (A (periodicLatticeShift y μ, ν)))
    (RMap (cornerWordSnd U μ ν y) (A (periodicLatticeShift y μ, ν)))]
  rw [Finset.sum_sub_distrib]
  ring

/-- **THE COVARIANT SUMMATION-BY-PARTS IDENTITY**, for every ORDERED pair `(μ,ν)` and every
extent: the divergence cross term equals the curl cross term PLUS the holonomy defect. -/
theorem covariant_sbp (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) :
    divCross U A μ ν = Ccov U A μ ν + ∑ y : PeriodicLatticeSite L, defectTerm U A μ ν y := by
  unfold divCross Ccov
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => inner_ubkcov_expand U A μ ν y,
    Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => inner_dcov_expand U A μ ν y]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [sum_lTerm1_eq, sum_lTerm2_eq, sum_lTerm3_eq, sum_lTerm4_eq]
  ring

#print axioms inner_ubkcov_expand
#print axioms inner_dcov_expand
#print axioms sum_lTerm4_eq
#print axioms sum_lTerm2_eq
#print axioms sum_lTerm3_eq
#print axioms rTerm1_eq_cornerWordSnd
#print axioms sum_lTerm1_eq
#print axioms covariant_sbp

/-! ## §4 — THE COVARIANT IDENTITY -/

/-- **THE COVARIANT DISCRETE ENERGY WEITZENBÖCK IDENTITY, EXACT, at EVERY background.**

`plaqEnergy(curl_U A) + divEnergy U A = gradEnergyCov U A + weitzDefect U A`

for every link configuration `U`, every `𝔰𝔲(2)`-valued bond field `A`, and every periodic extent
`L`. No regularity hypothesis, no divisibility hypothesis, no constant. The defect is the explicit
holonomy pairing of §1 — it is NOT defined as the difference of the two sides. -/
theorem weitzenbock_cov (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    plaqEnergy (curlCovariantLM U A) + divEnergy U A
      = gradEnergyCov U A + weitzDefect U A := by
  rw [plaqEnergy_curl_cov, divEnergy_eq_sum_divCross, gradEnergyCov_eq_sum_Xcov]
  rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) =>
    Finset.sum_congr rfl fun ν (_ : ν ∈ Finset.univ) => covariant_sbp U A μ ν]
  unfold weitzDefect
  rw [AdalyFormal.Balaban.Weitzenbock.sum_plaqDirs]
  simp only [Fin.sum_univ_three]
  have c01 := Ccov_symm U A 0 1
  have c02 := Ccov_symm U A 0 2
  have c12 := Ccov_symm U A 1 2
  have d0 := Ccov_diag U A 0
  have d1 := Ccov_diag U A 1
  have d2 := Ccov_diag U A 2
  linarith [c01, c02, c12, d0, d1, d2]

#print axioms weitzenbock_cov

/-! ## §5 — THE CONTROLS: where the defect vanishes, and the flat must-fire -/

/-- If the two corner words agree, the defect density is `0`. -/
theorem defectTerm_eq_zero_of_words_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L)
    (h : cornerWordFst U μ ν y = cornerWordSnd U μ ν y) : defectTerm U A μ ν y = 0 := by
  unfold defectTerm
  rw [h, sub_self, inner_zero_right]

/-- **THE DIAGONAL VANISHES**: at `μ = ν` both corner words are `1`. So `weitzDefect`'s nine
ordered pairs really carry only the six off-diagonal ones. -/
theorem defectTerm_diag (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ : Fin 3) (y : PeriodicLatticeSite L) :
    defectTerm U A μ μ y = 0 := by
  refine defectTerm_eq_zero_of_words_eq U A μ μ y ?_
  unfold cornerWordFst cornerWordSnd
  rw [mul_inv_cancel, inv_mul_cancel]

/-- **THE PLAQUETTE WORD** `U(∂p) = U(y,μ)·U(y+e_μ,ν)·U(y+e_ν,μ)⁻¹·U(y,ν)⁻¹`, for an ORDERED pair
`(μ,ν)` (the plaquette type only carries `μ < ν`; the word makes sense for every ordered pair and
the `μ < ν` instances ARE the tree's own `periodicPlaquetteHolonomy`, next theorem). -/
noncomputable def plaqWord (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (μ ν : Fin 3) (y : PeriodicLatticeSite L) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  U (y, μ) * U (periodicLatticeShift y μ, ν) *
    (U (periodicLatticeShift y ν, μ))⁻¹ * (U (y, ν))⁻¹

theorem plaqWord_eq_holonomy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (d : PeriodicPlaquetteDirections) :
    plaqWord U d.1.1 d.1.2 y = periodicPlaquetteHolonomy U ((y, d) : PeriodicLatticePlaquette L) :=
  rfl

/-- **THE TWO CORNER WORDS DIFFER BY THE PLAQUETTE HOLONOMY**, conjugated by the `ν`-bond at the
base point: `cornerWordSnd = U(y,ν)⁻¹·U(∂p)·U(y,ν)·cornerWordFst`. So the defect is a CURVATURE
term — it vanishes exactly when the plaquette holonomy acts trivially in the adjoint
representation. -/
theorem cornerWordSnd_eq_plaqWord_mul
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (μ ν : Fin 3)
    (y : PeriodicLatticeSite L) :
    cornerWordSnd U μ ν y
      = (U (y, ν))⁻¹ * plaqWord U μ ν y * U (y, ν) * cornerWordFst U μ ν y := by
  unfold cornerWordSnd plaqWord cornerWordFst
  group

/-- **THE DEFECT IS A CURVATURE TERM.** If the plaquette word acts as the identity in the adjoint
representation — which happens not only at `U(∂p) = 1` but at every CENTRAL value, `U(∂p) = −1`
included, since `R` is blind to the centre — the defect density vanishes. -/
theorem defectTerm_eq_zero_of_RMap_plaqWord_id
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L)
    (h : ∀ X : SuTwo, RMap (plaqWord U μ ν y) X = X) : defectTerm U A μ ν y = 0 := by
  unfold defectTerm
  rw [cornerWordSnd_eq_plaqWord_mul]
  rw [show ((U (y, ν))⁻¹ * plaqWord U μ ν y * U (y, ν) * cornerWordFst U μ ν y)
      = (U (y, ν))⁻¹ * (plaqWord U μ ν y * (U (y, ν) * cornerWordFst U μ ν y)) by
    rw [mul_assoc, mul_assoc]]
  rw [← RMap_mul_apply, ← RMap_mul_apply, ← RMap_mul_apply, h,
    RMap_inv_apply_apply, sub_self, inner_zero_right]

theorem weitzDefect_eq_zero_of_all_words_eq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo)
    (h : ∀ (μ ν : Fin 3) (y : PeriodicLatticeSite L),
      cornerWordFst U μ ν y = cornerWordSnd U μ ν y) : weitzDefect U A = 0 := by
  unfold weitzDefect
  refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => Finset.sum_eq_zero fun y _ => ?_
  exact defectTerm_eq_zero_of_words_eq U A μ ν y (h μ ν y)

/-! ### §5a — the flat background: the MUST-FIRE control -/

theorem dcov_trivialU (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) :
    dcov (trivialU L) A μ ν y = dfwd A μ ν y := by
  unfold dcov AdalyFormal.Balaban.Weitzenbock.dfwd
  rw [show RMap (trivialU L (y, μ)) = LinearMap.id from by
    show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = LinearMap.id
    exact RMap_one]
  rfl

theorem gradEnergyCov_trivialU (A : Bond L → SuTwo) :
    gradEnergyCov (trivialU L) A = gradEnergy A := by
  unfold gradEnergyCov AdalyFormal.Balaban.Weitzenbock.gradEnergy
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => by rw [dcov_trivialU]

theorem cornerWord_trivialU (μ ν : Fin 3) (y : PeriodicLatticeSite L) :
    cornerWordFst (trivialU L) μ ν y = cornerWordSnd (trivialU L) μ ν y := by
  unfold cornerWordFst cornerWordSnd trivialU
  simp

theorem weitzDefect_trivialU (A : Bond L → SuTwo) : weitzDefect (trivialU L) A = 0 :=
  weitzDefect_eq_zero_of_all_words_eq (trivialU L) A fun μ ν y => cornerWord_trivialU μ ν y

/-- **THE MUST-FIRE CONTROL.** At `U ≡ 1` the covariant identity DERIVES
`Weitzenbock.weitzenbock_flat`'s exact statement — an equality with no free constant. A factor
`1/2` on any one of the four summands of `weitzenbock_cov` would make this derivation false, so the
RELATIVE normalisation of the four terms is gated here, not assumed.

The three conjuncts are the three separate facts the control needs, and they are proved by
DIFFERENT routes: the first from `weitzenbock_cov` with the defect killed at `U ≡ 1`, the second
from `dcov_trivialU`, and the **third from the IMPORTED `Weitzenbock.weitzenbock_flat` term itself**.
The first two compose to the third, so the control is that two independent derivations land on the
same expression — if `gradEnergyCov`, `weitzDefect`, `plaqEnergy` or `divEnergy` were normalised
differently from `Weitzenbock`'s own objects, conjuncts 1+2 would not compose to conjunct 3 and this
declaration would not typecheck. -/
theorem weitzenbock_cov_recovers_flat (A : Bond L → SuTwo) :
    (plaqEnergy (curlCovariantLM (trivialU L) A) + divEnergy (trivialU L) A
        = gradEnergyCov (trivialU L) A)
      ∧ gradEnergyCov (trivialU L) A = gradEnergy A
      ∧ (plaqEnergy (curlCovariantLM (trivialU L) A) + divEnergy (trivialU L) A
          = gradEnergy A) := by
  refine ⟨?_, gradEnergyCov_trivialU A, AdalyFormal.Balaban.Weitzenbock.weitzenbock_flat A⟩
  have h := weitzenbock_cov (trivialU L) A
  rw [weitzDefect_trivialU, add_zero] at h
  exact h

/-! ### §5b — the junk attacks, compiled -/

/-- `A = 0`: the defect vanishes (and so does every other term). -/
theorem weitzDefect_zero_field
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    weitzDefect U (0 : Bond L → SuTwo) = 0 := by
  unfold weitzDefect defectTerm
  refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => Finset.sum_eq_zero fun y _ => ?_
  show inner ℝ ((0 : Bond L → SuTwo) (periodicLatticeShift y ν, μ)) _ = 0
  rw [show (0 : Bond L → SuTwo) (periodicLatticeShift y ν, μ) = 0 from rfl, inner_zero_left]

/-- **THE ONE-SITE TORUS DOES NOT TRIVIALISE THE COVARIANT STATEMENT** — unlike the flat case
(`Weitzenbock.oneSiteTorus_collapses`, where every difference vanishes because every shift is the
identity). At `L ≡ 0` every shift is the identity, so `dcov` becomes `R(U(y,μ))A(y,ν) − A(y,ν)`,
which is NOT identically zero: the covariant difference of a constant field measures the transport
itself. Recorded so the degenerate point cannot be cited as making §4 content-free. -/
theorem dcov_oneSiteTorus
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (fun _ => 0))
    (A : Bond (fun _ => 0) → SuTwo) (μ ν : Fin 3)
    (y : PeriodicLatticeSite (fun _ => 0)) :
    dcov U A μ ν y = RMap (U (y, μ)) (A (y, ν)) - A (y, ν) := by
  unfold dcov
  rw [AdalyFormal.Balaban.RegularUCurvedWitness.shift_ne_self_fails_at_zero_extent y μ rfl]

#print axioms defectTerm_eq_zero_of_words_eq
#print axioms defectTerm_diag
#print axioms plaqWord_eq_holonomy
#print axioms cornerWordSnd_eq_plaqWord_mul
#print axioms defectTerm_eq_zero_of_RMap_plaqWord_id
#print axioms weitzDefect_eq_zero_of_all_words_eq
#print axioms dcov_trivialU
#print axioms gradEnergyCov_trivialU
#print axioms cornerWord_trivialU
#print axioms weitzDefect_trivialU
#print axioms weitzenbock_cov_recovers_flat
#print axioms weitzDefect_zero_field
#print axioms dcov_oneSiteTorus

/-! ## §6 — THE SEPARATION: this defect is NOT Bałaban's `Δ′`

The dispatch that produced this file asked, first, whether the Weitzenböck `E4` defect and
`DeltaPrime.deltaPrimeQuadForm` are the same object, on the strength of two lanes' agreeing prose.
They are NOT, and the obstruction is structural rather than a normalisation: `weitzDefect` pairs
`A_μ` against `A_ν` with `μ ≠ ν` (the diagonal being `0`, §5), so it annihilates every field
supported in ONE lattice direction, whereas `Δ′` — built from the curl and from the plaquette
commutator sum — does not. `deltaWitnessConfig` is exactly such a field (one bond, direction `0`),
and `DeltaPrime` already evaluates `Δ′` there to `8`. -/

/-- **The defect annihilates single-direction fields, at EVERY background.** -/
theorem weitzDefect_eq_zero_of_single_direction
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (d : Fin 3) (hA : ∀ b : Bond L, b.2 ≠ d → A b = 0) :
    weitzDefect U A = 0 := by
  unfold weitzDefect
  refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => Finset.sum_eq_zero fun y _ => ?_
  by_cases hμ : μ = d
  · by_cases hν : ν = d
    · have hμν : ν = μ := by rw [hν, hμ]
      subst hμν
      exact defectTerm_diag U A ν y
    · unfold defectTerm
      rw [hA (periodicLatticeShift y μ, ν) hν, map_zero, map_zero, sub_zero, inner_zero_right]
  · unfold defectTerm
    rw [hA (periodicLatticeShift y ν, μ) hμ, inner_zero_left]

/-- `deltaWitnessConfig` is supported in direction `0`. -/
theorem deltaWitnessConfig_single_direction
    (b : Bond AdalyFormal.Balaban.AdmissibleSubspace.witnessL) (h : b.2 ≠ (0 : Fin 3)) :
    AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig b = 0 := by
  refine AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig_elsewhere ?_
  intro hc
  exact h (congrArg Prod.snd hc)

/-- **THE SEPARATION, at the tree's own `Δ′` witness.** -/
theorem weitzDefect_witnessU_deltaWitnessConfig :
    weitzDefect witnessU AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig = 0 :=
  weitzDefect_eq_zero_of_single_direction witnessU _ 0 deltaWitnessConfig_single_direction

/-- **THE TWO OBJECTS ARE DIFFERENT.** `0 ≠ 8`. Any argument that absorbs the covariant
Weitzenböck defect using `LemmaAssembly.abs_deltaPrimeQuadForm_le` is unsound: the bound is a bound
on a different functional. (The converse direction is equally instructive: `Δ′` is NOT controlled by
the Weitzenböck defect either, since the defect is `0` where `Δ′` is `8`.) -/
theorem weitzDefect_ne_deltaPrimeQuadForm :
    weitzDefect witnessU AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig
      ≠ AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadForm witnessU
          AdalyFormal.Balaban.DeltaPrime.deltaWitnessConfig := by
  rw [weitzDefect_witnessU_deltaWitnessConfig,
    AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadForm_witnessU_deltaWitnessConfig_eq]
  norm_num

#print axioms weitzDefect_eq_zero_of_single_direction
#print axioms deltaWitnessConfig_single_direction
#print axioms weitzDefect_witnessU_deltaWitnessConfig
#print axioms weitzDefect_ne_deltaPrimeQuadForm

/-! ## §7 — THE DEFECT BOUND: `|weitzDefect U A| ≤ 72·α·bondEnergy A`

Every constant is composed from counted factors, and no lattice size, scale or `k` appears:

* each corner word is a TWO-BOND word, so `frobNorm(word − 1) ≤ 2α` (`frobSq_mul_sub_one_le` +
  `frobSq_inv_sub_one`, both reused from `LemmaAssembly`);
* `RMapLipschitz.norm_RMap_sub_self_le` costs a factor `2`, giving `‖R(h)Q − Q‖ ≤ 4α‖Q‖`;
* TWO corner words: `‖R(h₁)Q − R(h₂)Q‖ ≤ 8α‖Q‖`;
* Cauchy–Schwarz and `2‖P‖‖Q‖ ≤ ‖P‖² + ‖Q‖²`: `|defectTerm| ≤ 4α(‖P‖² + ‖Q‖²)`;
* summing over sites, each of the two slot-sums is a single DIRECTION SLICE of `bondEnergy`
  (shift-reindexed), so each `(μ,ν)` block costs `8α·bondEnergy`;
* NINE ordered pairs: `72α·bondEnergy`. `72 = 9·2·2·2`. -/

theorem frobNorm_word_le {α : ℝ} (hα0 : 0 ≤ α)
    (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hg : frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (hh : frobNorm ((h : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    frobNorm (((g * h⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 2 * α := by
  have hgs : frobSq ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α ^ 2 := by
    have h0 := AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg
      ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    have := AdalyFormal.Balaban.RMapLipschitz.frobNorm_sq
      ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    nlinarith [hg, h0, this]
  have hhs : frobSq ((h : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α ^ 2 := by
    have h0 := AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg
      ((h : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    have := AdalyFormal.Balaban.RMapLipschitz.frobNorm_sq
      ((h : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    nlinarith [hh, h0, this]
  have hinv : frobSq (((h⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α ^ 2 := by
    rw [AdalyFormal.Balaban.LemmaAssembly.frobSq_inv_sub_one]
    exact hhs
  have hmul := AdalyFormal.Balaban.LemmaAssembly.frobSq_mul_sub_one_le g h⁻¹
  have hbound : frobSq (((g * h⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 4 * α ^ 2 := by linarith
  have h0 := AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg
    (((g * h⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
  have hsq := AdalyFormal.Balaban.RMapLipschitz.frobNorm_sq
    (((g * h⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
  nlinarith [hbound, h0, hsq, hα0]

theorem frobNorm_cornerWordFst_le {α : ℝ} (hα0 : 0 ≤ α)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hα : ∀ b : Bond L, frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (μ ν : Fin 3) (y : PeriodicLatticeSite L) :
    frobNorm ((cornerWordFst U μ ν y : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 2 * α :=
  frobNorm_word_le hα0 _ _ (hα _) (hα _)

/-- The Frobenius distance to `1` is inversion-invariant on `SU(2)` (`frobNorm` is the square root
of `LemmaAssembly.frobSq_inv_sub_one`'s quantity). -/
theorem frobNorm_inv_sub_one (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    frobNorm (((g⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      = frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  unfold AdalyFormal.Balaban.RMapLipschitz.frobNorm
  rw [AdalyFormal.Balaban.LemmaAssembly.frobSq_inv_sub_one]

theorem frobNorm_cornerWordSnd_le {α : ℝ} (hα0 : 0 ≤ α)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hα : ∀ b : Bond L, frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (μ ν : Fin 3) (y : PeriodicLatticeSite L) :
    frobNorm ((cornerWordSnd U μ ν y : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 2 * α := by
  have h : cornerWordSnd U μ ν y = (U (y, ν))⁻¹ * ((U (y, μ))⁻¹)⁻¹ := by
    unfold cornerWordSnd; rw [inv_inv]
  rw [h]
  refine frobNorm_word_le hα0 _ _ ?_ ?_
  · rw [frobNorm_inv_sub_one]; exact hα _
  · rw [frobNorm_inv_sub_one]; exact hα _

/-- Per-site defect bound. -/
theorem abs_defectTerm_le {α : ℝ} (hα0 : 0 ≤ α)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hα : ∀ b : Bond L, frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) :
    |defectTerm U A μ ν y|
      ≤ 4 * α * (‖A (periodicLatticeShift y ν, μ)‖ ^ 2
        + ‖A (periodicLatticeShift y μ, ν)‖ ^ 2) := by
  set P := A (periodicLatticeShift y ν, μ) with hP
  set Q := A (periodicLatticeShift y μ, ν) with hQ
  have h1 : ‖RMap (cornerWordFst U μ ν y) Q - Q‖ ≤ 2 * (2 * α) * ‖Q‖ := by
    refine le_trans (AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le _ Q) ?_
    have := frobNorm_cornerWordFst_le hα0 U hα μ ν y
    have hq := norm_nonneg Q
    nlinarith [this, hq]
  have h2 : ‖RMap (cornerWordSnd U μ ν y) Q - Q‖ ≤ 2 * (2 * α) * ‖Q‖ := by
    refine le_trans (AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le _ Q) ?_
    have := frobNorm_cornerWordSnd_le hα0 U hα μ ν y
    have hq := norm_nonneg Q
    nlinarith [this, hq]
  have hdiff : ‖RMap (cornerWordFst U μ ν y) Q - RMap (cornerWordSnd U μ ν y) Q‖ ≤ 8 * α * ‖Q‖ := by
    have hsplit : RMap (cornerWordFst U μ ν y) Q - RMap (cornerWordSnd U μ ν y) Q
        = (RMap (cornerWordFst U μ ν y) Q - Q) - (RMap (cornerWordSnd U μ ν y) Q - Q) := by
      abel
    rw [hsplit]
    refine le_trans (norm_sub_le _ _) ?_
    linarith [h1, h2]
  have hcs : |defectTerm U A μ ν y|
      ≤ ‖P‖ * ‖RMap (cornerWordFst U μ ν y) Q - RMap (cornerWordSnd U μ ν y) Q‖ := by
    unfold defectTerm
    exact abs_real_inner_le_norm _ _
  have hpn := norm_nonneg P
  have hqn := norm_nonneg Q
  have hamgm : 2 * (‖P‖ * ‖Q‖) ≤ ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by nlinarith [sq_nonneg (‖P‖ - ‖Q‖)]
  calc |defectTerm U A μ ν y|
      ≤ ‖P‖ * ‖RMap (cornerWordFst U μ ν y) Q - RMap (cornerWordSnd U μ ν y) Q‖ := hcs
    _ ≤ ‖P‖ * (8 * α * ‖Q‖) := by
        exact mul_le_mul_of_nonneg_left hdiff hpn
    _ ≤ 4 * α * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by nlinarith [hamgm, hα0, hpn, hqn]

/-- One direction slice of the bond energy. -/
theorem sum_dir_sq_le_bondEnergy (A : Bond L → SuTwo) (d : Fin 3) :
    (∑ y : PeriodicLatticeSite L, ‖A (y, d)‖ ^ 2) ≤ bondEnergy A := by
  unfold AdalyFormal.Balaban.RegularUPerturbation.bondEnergy
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun y _ => ?_
  exact Finset.single_le_sum (f := fun e : Fin 3 => ‖A (y, e)‖ ^ 2)
    (fun e _ => sq_nonneg _) (Finset.mem_univ d)

theorem sum_shift_dir_sq_eq (A : Bond L → SuTwo) (d ρ : Fin 3) :
    (∑ y : PeriodicLatticeSite L, ‖A (periodicLatticeShift y ρ, d)‖ ^ 2)
      = ∑ y : PeriodicLatticeSite L, ‖A (y, d)‖ ^ 2 :=
  Fintype.sum_equiv (periodicLatticeShiftEquiv (L := L) ρ) _ _ fun y => rfl

/-- Per-ordered-pair defect bound: `8α·bondEnergy`. -/
theorem abs_sum_defectTerm_le {α : ℝ} (hα0 : 0 ≤ α)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hα : ∀ b : Bond L, frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (A : Bond L → SuTwo) (μ ν : Fin 3) :
    |∑ y : PeriodicLatticeSite L, defectTerm U A μ ν y| ≤ 8 * α * bondEnergy A := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun y _ => abs_defectTerm_le hα0 U hα A μ ν y) ?_
  have hsplit : (∑ y : PeriodicLatticeSite L, 4 * α * (‖A (periodicLatticeShift y ν, μ)‖ ^ 2
        + ‖A (periodicLatticeShift y μ, ν)‖ ^ 2))
      = 4 * α * ((∑ y : PeriodicLatticeSite L, ‖A (periodicLatticeShift y ν, μ)‖ ^ 2)
        + ∑ y : PeriodicLatticeSite L, ‖A (periodicLatticeShift y μ, ν)‖ ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit, sum_shift_dir_sq_eq, sum_shift_dir_sq_eq]
  have h1 := sum_dir_sq_le_bondEnergy A μ
  have h2 := sum_dir_sq_le_bondEnergy A ν
  nlinarith [h1, h2, hα0]

/-- **THE DEFECT BOUND.** `|weitzDefect U A| ≤ 72·α·bondEnergy A` for every background whose bonds
are all within `α` of the identity in Frobenius norm. Absolute: `72 = 9·2·2·2`, no `L`, no scale,
no `k`. -/
theorem abs_weitzDefect_le {α : ℝ} (hα0 : 0 ≤ α)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hα : ∀ b : Bond L, frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (A : Bond L → SuTwo) : |weitzDefect U A| ≤ 72 * α * bondEnergy A := by
  unfold weitzDefect
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun μ _ => Finset.abs_sum_le_sum_abs
    (fun ν => ∑ y : PeriodicLatticeSite L, defectTerm U A μ ν y) Finset.univ) ?_
  refine le_trans (Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ =>
    abs_sum_defectTerm_le hα0 U hα A μ ν) ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbe := AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg A
  push_cast
  nlinarith [hbe, hα0]

/-- `α = 0` (the degenerate parameter): the bound forces the defect to vanish, consistently with
`weitzDefect_trivialU` — a background all of whose bonds are exactly `1` IS the trivial one. -/
theorem weitzDefect_eq_zero_of_frob_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hα : ∀ b : Bond L, frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 0)
    (A : Bond L → SuTwo) : weitzDefect U A = 0 := by
  have h := abs_weitzDefect_le (le_refl (0 : ℝ)) U hα A
  rw [show (72 : ℝ) * 0 * bondEnergy A = 0 by ring] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

#print axioms frobNorm_word_le
#print axioms frobNorm_inv_sub_one
#print axioms frobNorm_cornerWordFst_le
#print axioms frobNorm_cornerWordSnd_le
#print axioms abs_defectTerm_le
#print axioms sum_dir_sq_le_bondEnergy
#print axioms sum_shift_dir_sq_eq
#print axioms abs_sum_defectTerm_le
#print axioms abs_weitzDefect_le
#print axioms weitzDefect_eq_zero_of_frob_zero

/-! ## §8 — GAUGE COVARIANCE, and the bound under the source's own regularity predicate

`AlphaAnalyticity.GaugeRegular α₀ U` is `∃ γ, frobSupBond (U^γ) ≤ α₀` — smallness in SOME gauge.
To consume it, the defect must be a gauge INVARIANT. It is, and the proof does not assume it: each
of the four terms of `weitzenbock_cov` is shown gauge covariant (`R(γ y)` comes out of every
difference), and the defect's invariance is then FORCED by the identity. -/

theorem dcov_gauge (γ : AdalyFormal.Balaban.AlphaAnalyticity.GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ ν : Fin 3) (y : PeriodicLatticeSite L) :
    dcov (periodicGaugeTransform γ U) (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A) μ ν y
      = RMap (γ y) (dcov U A μ ν y) := by
  have hg : periodicGaugeTransform γ U (y, μ) * γ (periodicLatticeShift y μ) = γ y * U (y, μ) := by
    show γ y * U (y, μ) * (γ (periodicLatticeShift y μ))⁻¹ * γ (periodicLatticeShift y μ)
      = γ y * U (y, μ)
    group
  unfold dcov
  rw [AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA_apply,
    AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA_apply, map_sub, RMap_mul_apply, RMap_mul_apply,
    hg]

theorem ubkcov_gauge (γ : AdalyFormal.Balaban.AlphaAnalyticity.GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (μ : Fin 3) (y : PeriodicLatticeSite L) :
    ubkcov (periodicGaugeTransform γ U) (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A) μ y
      = RMap (γ y) (ubkcov U A μ y) := by
  have hs : periodicLatticeShift (periodicLatticeShiftBack y μ) μ = y :=
    periodicLatticeShift_shiftBack y μ
  have hg : (periodicGaugeTransform γ U (periodicLatticeShiftBack y μ, μ))⁻¹
      * γ (periodicLatticeShiftBack y μ) = γ y * (U (periodicLatticeShiftBack y μ, μ))⁻¹ := by
    show (γ (periodicLatticeShiftBack y μ) * U (periodicLatticeShiftBack y μ, μ)
        * (γ (periodicLatticeShift (periodicLatticeShiftBack y μ) μ))⁻¹)⁻¹
      * γ (periodicLatticeShiftBack y μ) = γ y * (U (periodicLatticeShiftBack y μ, μ))⁻¹
    rw [hs]
    group
  unfold ubkcov
  rw [AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA_apply,
    AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA_apply, map_sub, RMap_mul_apply, RMap_mul_apply,
    hg]

theorem gradEnergyCov_gauge (γ : AdalyFormal.Balaban.AlphaAnalyticity.GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    gradEnergyCov (periodicGaugeTransform γ U)
        (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A) = gradEnergyCov U A := by
  unfold gradEnergyCov
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => ?_
  rw [dcov_gauge, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]

theorem divEnergy_gauge (γ : AdalyFormal.Balaban.AlphaAnalyticity.GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    divEnergy (periodicGaugeTransform γ U)
        (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A) = divEnergy U A := by
  unfold AdalyFormal.Balaban.Weitzenbock.divEnergy
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [gradCovariantAdjointValue_eq_sum_ubkcov, gradCovariantAdjointValue_eq_sum_ubkcov]
  rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) => ubkcov_gauge γ U A μ y,
    ← map_sum, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]

theorem plaqEnergy_curl_gauge (γ : AdalyFormal.Balaban.AlphaAnalyticity.GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    plaqEnergy (curlCovariantLM (periodicGaugeTransform γ U)
        (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A))
      = plaqEnergy (curlCovariantLM U A) := by
  unfold AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy
  refine Finset.sum_congr rfl fun p _ => ?_
  show ‖curlValueCovariant (periodicGaugeTransform γ U)
      (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A) p‖ ^ 2
    = ‖curlValueCovariant U A p‖ ^ 2
  rw [AdalyFormal.Balaban.AlphaAnalyticity.curlValueCovariant_gauge,
    AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]

/-- **THE DEFECT IS A GAUGE INVARIANT** — derived from the identity plus the covariance of its
other three terms, not assumed. -/
theorem weitzDefect_gauge (γ : AdalyFormal.Balaban.AlphaAnalyticity.GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    weitzDefect (periodicGaugeTransform γ U)
        (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A) = weitzDefect U A := by
  have h1 := weitzenbock_cov (periodicGaugeTransform γ U)
    (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A)
  have h2 := weitzenbock_cov U A
  rw [plaqEnergy_curl_gauge, divEnergy_gauge, gradEnergyCov_gauge] at h1
  linarith [h1, h2]

/-- **THE DEFECT BOUND UNDER THE SOURCE'S OWN REGULARITY PREDICATE.**
`|weitzDefect U A| ≤ 72·α₀·bondEnergy A` for every `GaugeRegular α₀` background — smallness in SOME
gauge suffices, because both the defect and the bond energy are gauge invariants. -/
theorem abs_weitzDefect_le_of_gaugeRegular {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : AdalyFormal.Balaban.AlphaAnalyticity.GaugeRegular α₀ U) (A : Bond L → SuTwo) :
    |weitzDefect U A| ≤ 72 * α₀ * bondEnergy A := by
  obtain ⟨γ, hγ⟩ := hreg
  set V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
    periodicGaugeTransform γ U with hV
  have hb : ∀ b : Bond L, frobNorm ((V b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α₀ := fun b =>
    le_trans (AdalyFormal.Balaban.RegularUPerturbation.frobNorm_le_frobSupBond V b) hγ
  have h := abs_weitzDefect_le hα₀ V hb (AdalyFormal.Balaban.AlphaAnalyticity.gaugeActA γ A)
  rw [hV] at h
  rwa [weitzDefect_gauge, AdalyFormal.Balaban.AlphaAnalyticity.bondEnergy_gauge] at h

/-- **THE COVARIANT WEITZENBÖCK IDENTITY AS A TWO-SIDED INEQUALITY WITH A CONTROLLED ERROR.**

`|plaqEnergy(curl_U A) + divEnergy U A − gradEnergyCov U A| ≤ 72·α₀·bondEnergy A`

for every `GaugeRegular α₀` background, every field, every extent. All constants outside the
lattice, the scale, `k` and `U`. -/
theorem abs_weitzenbock_cov_error {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : AdalyFormal.Balaban.AlphaAnalyticity.GaugeRegular α₀ U) (A : Bond L → SuTwo) :
    |plaqEnergy (curlCovariantLM U A) + divEnergy U A - gradEnergyCov U A|
      ≤ 72 * α₀ * bondEnergy A := by
  have h := weitzenbock_cov U A
  have hrw : plaqEnergy (curlCovariantLM U A) + divEnergy U A - gradEnergyCov U A
      = weitzDefect U A := by linarith
  rw [hrw]
  exact abs_weitzDefect_le_of_gaugeRegular hα₀ U hreg A

#print axioms dcov_gauge
#print axioms ubkcov_gauge
#print axioms gradEnergyCov_gauge
#print axioms divEnergy_gauge
#print axioms plaqEnergy_curl_gauge
#print axioms weitzDefect_gauge
#print axioms abs_weitzDefect_le_of_gaugeRegular
#print axioms abs_weitzenbock_cov_error

/-! ## §9 — THE PAYOFF CHAIN, exactly as far as it reaches

`Weitzenbock`'s §6 reduction is: on the divergence-free surface the curl energy IS the gradient
energy, so a gradient Poincaré gives a curl Poincaré. Covariantly the same reduction holds up to
the defect, and §8 bounds the defect by `α₀·bondEnergy` — which is exactly the shape that can be
absorbed against a Poincaré constant. -/

/-- On the COVARIANT divergence-free surface, the curl energy is the covariant gradient energy up
to the defect. -/
theorem plaqEnergy_ge_of_div_free {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : AdalyFormal.Balaban.AlphaAnalyticity.GaugeRegular α₀ U) (A : Bond L → SuTwo)
    (hdiv : ∀ y : PeriodicLatticeSite L, gradCovariantAdjointValue U A y = 0) :
    gradEnergyCov U A - 72 * α₀ * bondEnergy A ≤ plaqEnergy (curlCovariantLM U A) := by
  have h := weitzenbock_cov U A
  rw [AdalyFormal.Balaban.Weitzenbock.divEnergy_eq_zero_of_div_free U A hdiv, add_zero] at h
  have hd := abs_weitzDefect_le_of_gaugeRegular hα₀ U hreg A
  have hd' := abs_le.mp hd
  linarith [hd'.1, hd'.2]

/-- **THE GENERAL-`U` FIXED-LEVEL DIVERGENCE-FREE POINCARÉ, from a covariant gradient Poincaré.**

If, at a given level, `bondEnergy A ≤ K · gradEnergyCov U A` on the covariant kernel, and the
background is `GaugeRegular α₀` with `72·α₀·K < 1`, then

`bondEnergy A ≤ (K / (1 − 72·α₀·K)) · plaqEnergy(curl_U A)`

on the divergence-free part of that kernel. This is `[STOKES-COMM-U]`'s denominator at general `U`,
CONDITIONAL on exactly one input (`hpoin`), which §9b names precisely. -/
theorem bondEnergy_le_plaqEnergy_of_covGradPoincare {α₀ K : ℝ} (hα₀ : 0 ≤ α₀) (hK : 0 < K)
    (hsmall : 72 * α₀ * K < 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : AdalyFormal.Balaban.AlphaAnalyticity.GaugeRegular α₀ U) (A : Bond L → SuTwo)
    (hdiv : ∀ y : PeriodicLatticeSite L, gradCovariantAdjointValue U A y = 0)
    (hpoin : bondEnergy A ≤ K * gradEnergyCov U A) :
    bondEnergy A ≤ (K / (1 - 72 * α₀ * K)) * plaqEnergy (curlCovariantLM U A) := by
  have hpos : 0 < 1 - 72 * α₀ * K := by linarith
  have hge := plaqEnergy_ge_of_div_free hα₀ U hreg A hdiv
  have hKge : K * (gradEnergyCov U A - 72 * α₀ * bondEnergy A)
      ≤ K * plaqEnergy (curlCovariantLM U A) :=
    mul_le_mul_of_nonneg_left hge (le_of_lt hK)
  have key : bondEnergy A * (1 - 72 * α₀ * K) ≤ K * plaqEnergy (curlCovariantLM U A) := by
    nlinarith [hKge, hpoin]
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith [key]

/-! ### §9a — the FLAT gradient energy versus the COVARIANT one

The two differ by a per-bond transport error, so they are comparable with an `α²` loss. This is the
first of the two inputs needed to run `Weitzenbock.gradPoincareOnKerQAtLevel_two` at general `U`. -/

theorem sum_sites_dirs_eq_bondEnergy (A : Bond L → SuTwo) :
    (∑ ν : Fin 3, ∑ y : PeriodicLatticeSite L, ‖A (y, ν)‖ ^ 2) = bondEnergy A := by
  unfold AdalyFormal.Balaban.RegularUPerturbation.bondEnergy
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- **`gradEnergy A ≤ 2·gradEnergyCov U A + 24·α²·bondEnergy A`.** `24 = 2·4·3`: the
`(a+b)² ≤ 2a²+2b²` split, the squared Lipschitz constant `(2α)² = 4α²`, and the three difference
directions. -/
theorem gradEnergy_le_gradEnergyCov {α : ℝ} (hα0 : 0 ≤ α)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hα : ∀ b : Bond L, frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (A : Bond L → SuTwo) :
    gradEnergy A ≤ 2 * gradEnergyCov U A + 24 * α ^ 2 * bondEnergy A := by
  have hpt : ∀ (μ ν : Fin 3) (y : PeriodicLatticeSite L),
      ‖dfwd A μ ν y‖ ^ 2
        ≤ 2 * ‖dcov U A μ ν y‖ ^ 2
          + 8 * α ^ 2 * ‖A (periodicLatticeShift y μ, ν)‖ ^ 2 := by
    intro μ ν y
    have hsplit : dfwd A μ ν y
        = dcov U A μ ν y - (RMap (U (y, μ)) (A (periodicLatticeShift y μ, ν))
            - A (periodicLatticeShift y μ, ν)) := by
      unfold AdalyFormal.Balaban.Weitzenbock.dfwd dcov
      abel
    have htri : ‖dfwd A μ ν y‖
        ≤ ‖dcov U A μ ν y‖ + ‖RMap (U (y, μ)) (A (periodicLatticeShift y μ, ν))
            - A (periodicLatticeShift y μ, ν)‖ := by
      rw [hsplit]; exact norm_sub_le _ _
    have hlip : ‖RMap (U (y, μ)) (A (periodicLatticeShift y μ, ν))
        - A (periodicLatticeShift y μ, ν)‖ ≤ 2 * α * ‖A (periodicLatticeShift y μ, ν)‖ := by
      refine le_trans (AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le _ _) ?_
      have := hα (y, μ)
      have hn := norm_nonneg (A (periodicLatticeShift y μ, ν))
      nlinarith [this, hn]
    have hsq : ‖dfwd A μ ν y‖ ^ 2
        ≤ (‖dcov U A μ ν y‖ + ‖RMap (U (y, μ)) (A (periodicLatticeShift y μ, ν))
            - A (periodicLatticeShift y μ, ν)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have h1 := norm_nonneg (RMap (U (y, μ)) (A (periodicLatticeShift y μ, ν))
      - A (periodicLatticeShift y μ, ν))
    have h2 := norm_nonneg (A (periodicLatticeShift y μ, ν))
    have hb2 : ‖RMap (U (y, μ)) (A (periodicLatticeShift y μ, ν))
        - A (periodicLatticeShift y μ, ν)‖ ^ 2
        ≤ (2 * α * ‖A (periodicLatticeShift y μ, ν)‖) ^ 2 :=
      pow_le_pow_left₀ h1 hlip 2
    have key2 : ∀ p q : ℝ, (p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by
      intro p q; nlinarith [sq_nonneg (p - q)]
    calc ‖dfwd A μ ν y‖ ^ 2
        ≤ (‖dcov U A μ ν y‖ + ‖RMap (U (y, μ)) (A (periodicLatticeShift y μ, ν))
            - A (periodicLatticeShift y μ, ν)‖) ^ 2 := hsq
      _ ≤ 2 * (‖dcov U A μ ν y‖ ^ 2
            + ‖RMap (U (y, μ)) (A (periodicLatticeShift y μ, ν))
              - A (periodicLatticeShift y μ, ν)‖ ^ 2) := key2 _ _
      _ ≤ 2 * (‖dcov U A μ ν y‖ ^ 2
            + (2 * α * ‖A (periodicLatticeShift y μ, ν)‖) ^ 2) := by linarith [hb2]
      _ = 2 * ‖dcov U A μ ν y‖ ^ 2
            + 8 * α ^ 2 * ‖A (periodicLatticeShift y μ, ν)‖ ^ 2 := by ring
  have hsum : gradEnergy A
      ≤ ∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
          (2 * ‖dcov U A μ ν y‖ ^ 2
            + 8 * α ^ 2 * ‖A (periodicLatticeShift y μ, ν)‖ ^ 2) := by
    unfold AdalyFormal.Balaban.Weitzenbock.gradEnergy
    exact Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun μ _ =>
      Finset.sum_le_sum fun ν _ => hpt μ ν y
  have hsplit2 : (∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
        (2 * ‖dcov U A μ ν y‖ ^ 2 + 8 * α ^ 2 * ‖A (periodicLatticeShift y μ, ν)‖ ^ 2))
      = 2 * (∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, ‖dcov U A μ ν y‖ ^ 2)
        + 8 * α ^ 2 * ∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
            ‖A (periodicLatticeShift y μ, ν)‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcount : (∑ y : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
      ‖A (periodicLatticeShift y μ, ν)‖ ^ 2) = 3 * bondEnergy A := by
    rw [Finset.sum_comm]
    have hin : ∀ μ : Fin 3, (∑ y : PeriodicLatticeSite L, ∑ ν : Fin 3,
        ‖A (periodicLatticeShift y μ, ν)‖ ^ 2) = bondEnergy A := by
      intro μ
      rw [Finset.sum_comm]
      rw [show (∑ ν : Fin 3, ∑ y : PeriodicLatticeSite L,
            ‖A (periodicLatticeShift y μ, ν)‖ ^ 2)
          = ∑ ν : Fin 3, ∑ y : PeriodicLatticeSite L, ‖A (y, ν)‖ ^ 2 from
        Finset.sum_congr rfl fun ν _ => sum_shift_dir_sq_eq A ν μ]
      exact sum_sites_dirs_eq_bondEnergy A
    rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) => hin μ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [hsplit2, hcount] at hsum
  unfold gradEnergyCov
  linarith [hsum]

/-! ### §9b — WHAT IS STILL MISSING, stated as a predicate rather than described

`Weitzenbock.gradPoincareOnKerQAtLevel_two` gives `bondEnergy A ≤ 31104·gradEnergy A` for
`A ∈ ker Q_2(1)` — the FLAT kernel and the FLAT gradient. §9a converts the flat gradient into the
covariant one at cost `α²·bondEnergy`, which is absorbable. The remaining input is the KERNEL: a
field in `ker Q_2(U)` is not in `ker Q_2(1)`, only within `O(α)` of it, and the flat theorem is
stated on the exact kernel only. `KerQTransferAtLevel` below names exactly that missing statement —
a STABILITY form of the flat Poincaré with the constraint residual on the right — and
`covGradPoincare_of_kerQTransfer` shows it is the ONLY thing between §8 and the general-`U`
fixed-level Poincaré. -/

/-- **The missing input, named.** A flat gradient Poincaré at level `c` that tolerates a
constraint residual: `bondEnergy A ≤ K·gradEnergy A + M·(the squared flat block-sum residual)`,
for EVERY `A` (no kernel hypothesis). `Weitzenbock.gradPoincareOnKerQAtLevel_two` is its
`residual = 0` specialisation. -/
def StableGradPoincareAtLevel (c : ℕ) : Prop :=
  ∃ K M : ℝ, 0 < K ∧ 0 ≤ M ∧
    ∀ (L : PeriodicLatticeExtent), (∀ μ : Fin 3, c ∣ (L μ + 1)) →
      ∀ (A : Bond L → SuTwo),
        bondEnergy A ≤ K * gradEnergy A
          + M * ∑ μ : Fin 3, ∑ x ∈ CoarseLattice L c,
              ‖∑ z ∈ blockOf x c, ∑ i ∈ Finset.range c,
                A (AdalyFormal.Balaban.QOne.pathSite z μ i, μ)‖ ^ 2

#print axioms plaqEnergy_ge_of_div_free
#print axioms bondEnergy_le_plaqEnergy_of_covGradPoincare
#print axioms sum_sites_dirs_eq_bondEnergy
#print axioms gradEnergy_le_gradEnergyCov

/-! ## §10 — `StableGradPoincareAtLevel 2` — PROVED, so §9b names no open residual

§9b's predicate is not left standing: it is discharged here at level `2`, with `K = 62208` and
`M = 16`. The proof mirrors `Weitzenbock`'s §7d/§7f with the block-sum CARRIED instead of set to
zero, and reuses that file's bricks unchanged (`shiftVec3`, `Tloc`, `sq_norm_shiftVec3_sub_le`,
`mem_blockOf_eq_shiftVec3`, `pathSite_shiftVec3`, `exists_coarse_shiftVec3`, `sum_le_sum_of_surj`,
`sum_coarse_Tloc_le`). **LAW-19 disclosure**: the per-pair estimate `hterm` below is a re-derivation
of an INLINE step of `Weitzenbock.sq_norm_A_le_Tloc` (it is not a named declaration there, so it
cannot be invoked); everything else is invoked, not rebuilt.

`62208 = 2 · 31104` — exactly twice `Weitzenbock.gradPoincareOnKerQAtLevel_two`'s constant, the
cost of the `(a+b)² ≤ 2a² + 2b²` split that separates the residual from the telescoping part. The
`residual = 0` specialisation is therefore WEAKER than the exact theorem by a factor `2`, and no
sharpness is claimed. -/

/-- The FLAT level-`2` block sum at a coarse site, in a direction — the quantity `ker Q_2(1)` sets
to zero and `ker Q_2(U)` only makes small. -/
noncomputable def blockResidual (A : Bond L → SuTwo) (c : PeriodicLatticeSite L) (μ : Fin 3) :
    SuTwo :=
  ∑ z ∈ blockOf c 2, ∑ i ∈ Finset.range 2,
    A (AdalyFormal.Balaban.QOne.pathSite z μ i, μ)

/-- **The pointwise bound with the residual carried.** -/
theorem sq_norm_A_le_Tloc_stable (A : Bond L → SuTwo) {c : PeriodicLatticeSite L}
    (μ : Fin 3) (d0 d1 d2 : ℕ) (hd0 : d0 < 3) (hd1 : d1 < 3) (hd2 : d2 < 3) :
    ‖A (shiftVec3 c d0 d1 d2, μ)‖ ^ 2
      ≤ 2 * ‖blockResidual A c μ‖ ^ 2 + 288 * Tloc A c μ := by
  classical
  set y := shiftVec3 c d0 d1 d2 with hy
  set s := (blockOf c 2) ×ˢ (Finset.range 2) with hs
  have hTnn := AdalyFormal.Balaban.Weitzenbock.Tloc_nonneg A c μ
  have hres : ∑ p ∈ s, A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ)
      = blockResidual A c μ := by
    rw [hs, Finset.sum_product]
    rfl
  have hcmem : c ∈ blockOf c 2 := by
    rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf]
    intro ρ
    exact ⟨le_refl _, by omega⟩
  have hcard : 1 ≤ s.card := by
    rw [hs]
    refine Finset.card_pos.mpr ⟨(c, 0), ?_⟩
    rw [Finset.mem_product]
    exact ⟨hcmem, Finset.mem_range.mpr (by norm_num)⟩
  have hcardR : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcard
  -- LAW-19 disclosure: re-derivation of an inline step of `Weitzenbock.sq_norm_A_le_Tloc`
  have hterm : ∀ p ∈ s,
      ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ ^ 2
        ≤ 144 * Tloc A c μ := by
    intro p hp
    rw [hs, Finset.mem_product] at hp
    obtain ⟨m0, m1, m2, hm0, hm1, hm2, hxeq⟩ :=
      AdalyFormal.Balaban.Weitzenbock.mem_blockOf_eq_shiftVec3 hp.1
    obtain ⟨k0, k1, k2, hk0, hk1, hk2, hkeq⟩ :=
      AdalyFormal.Balaban.Weitzenbock.pathSite_shiftVec3 c m0 m1 m2 p.2 μ
    have hi2 : p.2 < 2 := Finset.mem_range.mp hp.2
    have hz : AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2 = shiftVec3 c k0 k1 k2 := by
      rw [hxeq]; exact hkeq
    have hb0 : k0 < 3 := by omega
    have hb1 : k1 < 3 := by omega
    have hb2 : k2 < 3 := by omega
    have h1 := AdalyFormal.Balaban.Weitzenbock.sq_norm_shiftVec3_sub_le A c μ k0 k1 k2 hb0 hb1 hb2
    have h2 := AdalyFormal.Balaban.Weitzenbock.sq_norm_shiftVec3_sub_le A c μ d0 d1 d2 hd0 hd1 hd2
    rw [hz]
    have hsplit : A (shiftVec3 c k0 k1 k2, μ) - A (y, μ)
        = (A (shiftVec3 c k0 k1 k2, μ) - A (c, μ)) - (A (y, μ) - A (c, μ)) := by abel
    have htri : ‖A (shiftVec3 c k0 k1 k2, μ) - A (y, μ)‖
        ≤ ‖A (shiftVec3 c k0 k1 k2, μ) - A (c, μ)‖ + ‖A (y, μ) - A (c, μ)‖ := by
      rw [hsplit]; exact norm_sub_le _ _
    have hstep : ‖A (shiftVec3 c k0 k1 k2, μ) - A (y, μ)‖ ^ 2
        ≤ (‖A (shiftVec3 c k0 k1 k2, μ) - A (c, μ)‖ + ‖A (y, μ) - A (c, μ)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hstep, h1, h2, sq_nonneg (‖A (shiftVec3 c k0 k1 k2, μ) - A (c, μ)‖
      - ‖A (y, μ) - A (c, μ)‖)]
  have hid : ∑ p ∈ s, (A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ))
      = blockResidual A c μ - s.card • A (y, μ) := by
    rw [Finset.sum_sub_distrib, hres, Finset.sum_const]
  have hnormsmul : ‖s.card • A (y, μ)‖ = (s.card : ℝ) * ‖A (y, μ)‖ := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
    simp
  have hn1 : (s.card : ℝ) * ‖A (y, μ)‖
      ≤ ‖blockResidual A c μ‖
        + ∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ := by
    have hrewrite : s.card • A (y, μ)
        = blockResidual A c μ
          - ∑ p ∈ s, (A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)) := by
      rw [hid]; abel
    have hsum := norm_sum_le s
      (fun p => A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ))
    calc (s.card : ℝ) * ‖A (y, μ)‖ = ‖s.card • A (y, μ)‖ := hnormsmul.symm
      _ = ‖blockResidual A c μ
            - ∑ p ∈ s, (A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ))‖ := by
          rw [hrewrite]
      _ ≤ ‖blockResidual A c μ‖
            + ‖∑ p ∈ s, (A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ))‖ :=
          norm_sub_le _ _
      _ ≤ ‖blockResidual A c μ‖
            + ∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ := by
          linarith [hsum]
  have hn2 : (∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖) ^ 2
      ≤ (s.card : ℝ) * ∑ p ∈ s,
          ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := s)
      (f := fun p => ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖)
    simpa using this
  have hn3 : (∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ ^ 2)
      ≤ (s.card : ℝ) * (144 * Tloc A c μ) := by
    calc (∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ ^ 2)
        ≤ ∑ _p ∈ s, 144 * Tloc A c μ := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * (144 * Tloc A c μ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hN0 : (0 : ℝ) ≤ (s.card : ℝ) := le_trans zero_le_one hcardR
  have hNa : (0 : ℝ) ≤ (s.card : ℝ) * ‖A (y, μ)‖ := mul_nonneg hN0 (norm_nonneg _)
  have hsq1 : ((s.card : ℝ) * ‖A (y, μ)‖) ^ 2
      ≤ (‖blockResidual A c μ‖
          + ∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖) ^ 2 :=
    pow_le_pow_left₀ hNa hn1 2
  have h5 : (s.card : ℝ) * ∑ p ∈ s,
        ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖ ^ 2
      ≤ (s.card : ℝ) * ((s.card : ℝ) * (144 * Tloc A c μ)) :=
    mul_le_mul_of_nonneg_left hn3 hN0
  have hchain : ((s.card : ℝ) * ‖A (y, μ)‖) ^ 2
      ≤ 2 * ‖blockResidual A c μ‖ ^ 2 + 288 * ((s.card : ℝ) ^ 2 * Tloc A c μ) := by
    nlinarith [hsq1, hn2, h5, sq_nonneg (‖blockResidual A c μ‖
      - ∑ p ∈ s, ‖A (AdalyFormal.Balaban.QOne.pathSite p.1 μ p.2, μ) - A (y, μ)‖)]
  have hN2 : (1 : ℝ) ≤ (s.card : ℝ) ^ 2 := by nlinarith [hcardR]
  have hR2 : 2 * ‖blockResidual A c μ‖ ^ 2
      ≤ (s.card : ℝ) ^ 2 * (2 * ‖blockResidual A c μ‖ ^ 2) := by
    nlinarith [hN2, sq_nonneg ‖blockResidual A c μ‖]
  have hfinal : (s.card : ℝ) ^ 2 * ‖A (y, μ)‖ ^ 2
      ≤ (s.card : ℝ) ^ 2 * (2 * ‖blockResidual A c μ‖ ^ 2 + 288 * Tloc A c μ) := by
    nlinarith [hchain, hR2]
  have hpos : (0 : ℝ) < (s.card : ℝ) ^ 2 := by nlinarith [hcardR]
  exact le_of_mul_le_mul_left hfinal hpos

/-- **The component bound with the residual carried.** -/
theorem sum_sq_component_le_stable (A : Bond L → SuTwo) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (μ : Fin 3) :
    (∑ y : PeriodicLatticeSite L, ‖A (y, μ)‖ ^ 2)
      ≤ 62208 * (∑ ρ : Fin 3, Xt A ρ μ)
        + 16 * ∑ c ∈ CoarseLattice L 2, ‖blockResidual A c μ‖ ^ 2 := by
  classical
  set S := (CoarseLattice L 2) ×ˢ
    ((Finset.range 2) ×ˢ ((Finset.range 2) ×ˢ (Finset.range 2))) with hS
  have hsurj : ∀ y : PeriodicLatticeSite L, ∃ q ∈ S,
      shiftVec3 q.1 q.2.1 q.2.2.1 q.2.2.2 = y := by
    intro y
    obtain ⟨c, hc, n0, n1, n2, h0, h1, h2, heq⟩ :=
      AdalyFormal.Balaban.Weitzenbock.exists_coarse_shiftVec3 hdvd y
    refine ⟨(c, n0, n1, n2), ?_, heq.symm⟩
    rw [hS, Finset.mem_product, Finset.mem_product, Finset.mem_product]
    exact ⟨hc, Finset.mem_range.mpr h0, Finset.mem_range.mpr h1, Finset.mem_range.mpr h2⟩
  have hstep1 : (∑ y : PeriodicLatticeSite L, ‖A (y, μ)‖ ^ 2)
      ≤ ∑ q ∈ S, ‖A (shiftVec3 q.1 q.2.1 q.2.2.1 q.2.2.2, μ)‖ ^ 2 :=
    AdalyFormal.Balaban.Weitzenbock.sum_le_sum_of_surj S
      (fun q => shiftVec3 q.1 q.2.1 q.2.2.1 q.2.2.2)
      (fun y => ‖A (y, μ)‖ ^ 2) (fun _ => sq_nonneg _) hsurj
  have hstep2 : (∑ q ∈ S, ‖A (shiftVec3 q.1 q.2.1 q.2.2.1 q.2.2.2, μ)‖ ^ 2)
      ≤ ∑ q ∈ S, (2 * ‖blockResidual A q.1 μ‖ ^ 2 + 288 * Tloc A q.1 μ) := by
    refine Finset.sum_le_sum fun q hq => ?_
    rw [hS, Finset.mem_product, Finset.mem_product, Finset.mem_product] at hq
    exact sq_norm_A_le_Tloc_stable A μ _ _ _
      (by have := Finset.mem_range.mp hq.2.1; omega)
      (by have := Finset.mem_range.mp hq.2.2.1; omega)
      (by have := Finset.mem_range.mp hq.2.2.2; omega)
  have hstep3 : (∑ q ∈ S, (2 * ‖blockResidual A q.1 μ‖ ^ 2 + 288 * Tloc A q.1 μ))
      = 8 * ∑ c ∈ CoarseLattice L 2,
          (2 * ‖blockResidual A c μ‖ ^ 2 + 288 * Tloc A c μ) := by
    rw [hS, Finset.sum_product]
    have hin : ∀ c ∈ CoarseLattice L 2,
        (∑ _q ∈ (Finset.range 2) ×ˢ ((Finset.range 2) ×ˢ (Finset.range 2)),
          (2 * ‖blockResidual A c μ‖ ^ 2 + 288 * Tloc A c μ))
          = 8 * (2 * ‖blockResidual A c μ‖ ^ 2 + 288 * Tloc A c μ) := by
      intro c _
      rw [Finset.sum_const, Finset.card_product, Finset.card_product, Finset.card_range,
        nsmul_eq_mul]
      norm_num
    rw [Finset.sum_congr rfl hin, ← Finset.mul_sum]
  have hsplit : (∑ c ∈ CoarseLattice L 2,
        (2 * ‖blockResidual A c μ‖ ^ 2 + 288 * Tloc A c μ))
      = 2 * (∑ c ∈ CoarseLattice L 2, ‖blockResidual A c μ‖ ^ 2)
        + 288 * ∑ c ∈ CoarseLattice L 2, Tloc A c μ := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hTloc := AdalyFormal.Balaban.Weitzenbock.sum_coarse_Tloc_le A μ
  calc (∑ y : PeriodicLatticeSite L, ‖A (y, μ)‖ ^ 2)
      ≤ ∑ q ∈ S, ‖A (shiftVec3 q.1 q.2.1 q.2.2.1 q.2.2.2, μ)‖ ^ 2 := hstep1
    _ ≤ ∑ q ∈ S, (2 * ‖blockResidual A q.1 μ‖ ^ 2 + 288 * Tloc A q.1 μ) := hstep2
    _ = 8 * ∑ c ∈ CoarseLattice L 2,
          (2 * ‖blockResidual A c μ‖ ^ 2 + 288 * Tloc A c μ) := hstep3
    _ = 8 * (2 * (∑ c ∈ CoarseLattice L 2, ‖blockResidual A c μ‖ ^ 2)
          + 288 * ∑ c ∈ CoarseLattice L 2, Tloc A c μ) := by rw [hsplit]
    _ ≤ 62208 * (∑ ρ : Fin 3, Xt A ρ μ)
          + 16 * ∑ c ∈ CoarseLattice L 2, ‖blockResidual A c μ‖ ^ 2 := by
        linarith [hTloc]

/-- **The stable flat Poincaré at level `2`, with explicit constants** — the working form. -/
theorem bondEnergy_le_gradEnergy_add_residual (A : Bond L → SuTwo)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    bondEnergy A ≤ 62208 * gradEnergy A
      + 16 * ∑ μ : Fin 3, ∑ c ∈ CoarseLattice L 2, ‖blockResidual A c μ‖ ^ 2 := by
  have hcomp : bondEnergy A
      = ∑ μ : Fin 3, ∑ y : PeriodicLatticeSite L, ‖A (y, μ)‖ ^ 2 := by
    unfold AdalyFormal.Balaban.RegularUPerturbation.bondEnergy
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hgrad : gradEnergy A = ∑ μ : Fin 3, ∑ ρ : Fin 3, Xt A ρ μ := by
    rw [AdalyFormal.Balaban.Weitzenbock.gradEnergy_eq_sum_Xt, Finset.sum_comm]
  rw [hcomp, hgrad, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun μ _ => ?_
  exact sum_sq_component_le_stable A hdvd μ

/-- **`StableGradPoincareAtLevel 2` — PROVED**, `K = 62208`, `M = 16`. -/
theorem stableGradPoincareAtLevel_two : StableGradPoincareAtLevel 2 :=
  ⟨62208, 16, by norm_num, by norm_num,
    fun _ hdvd A => bondEnergy_le_gradEnergy_add_residual A hdvd⟩

#print axioms blockResidual
#print axioms sq_norm_A_le_Tloc_stable
#print axioms sum_sq_component_le_stable
#print axioms bondEnergy_le_gradEnergy_add_residual
#print axioms stableGradPoincareAtLevel_two

/-! ## §11 — THE CONDITIONAL HYPOTHESIS OF §9 IS REMOVED AT LEVEL `2`

§9's `bondEnergy_le_plaqEnergy_of_covGradPoincare` needed a covariant gradient Poincaré as an
INPUT. At level `2` that input is now supplied, and the general-`U` fixed-level divergence-free
Poincaré follows with NO conditional hypothesis, for backgrounds below an explicit regularity
threshold. The missing transfer — `ker Q_2(U)` versus `ker Q_2(1)` — is **already in the tree**
(`RegularUQChain.coarseDriftEnergy_le`, `∑_b ‖Q₁(1)A(b) − Q₁(U)A(b)‖² ≤ (64/ell)·α²·bondEnergy A`);
it is invoked, not rebuilt (LAW-19). The chain, with every constant composed from counted factors:

* `Q₁(1)A(b) = (1/16)·blockResidual A b₋ b.2` at `ell = 2` (`ell⁴ = 16`);
* on `ker Q_2(U)`, `Q₁(1)A(b) = Q₁(1)A(b) − Q₁(U)A(b)`, so
  `∑_{μ,c} ‖blockResidual‖² = 256·∑_b ‖drift‖² ≤ 256·(64/2)·α²·bondEnergy = 8192·α²·bondEnergy`;
* §10: `bondEnergy ≤ 62208·gradEnergy + 16·(8192 α²·bondEnergy)`;
* §9a: `gradEnergy ≤ 2·gradEnergyCov + 24 α²·bondEnergy`;
* together `bondEnergy ≤ 124416·gradEnergyCov + 1624064·α²·bondEnergy`, and
  `1624064·(1/2000)² = 1624064/4000000 ≤ 1/2`, giving `bondEnergy ≤ 248832·gradEnergyCov`;
* §7: `72·α·248832 ≤ 1/2` once `α ≤ 1/(4·10⁷)`, giving `bondEnergy ≤ 497664·plaqEnergy(curl_U A)`.

The thresholds `1/2000` and `1/(4·10⁷)` are NOT optimised; they are the round numbers at which the
absorption factors drop below `1/2`, and each is verified in exact rational arithmetic by the
kernel. -/

theorem lineCoarseRestrictCov_trivialU_eq_blockResidual (A : Bond L → SuTwo)
    (b : CoarseBond L 2) :
    lineCoarseRestrictCov (trivialU L) 2 A b = (1 / 16 : ℝ) • blockResidual A b.1.1 b.2 := by
  rw [AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov_trivialU]
  unfold AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo blockResidual
  norm_num

theorem norm_blockResidual (A : Bond L → SuTwo) (b : CoarseBond L 2) :
    ‖blockResidual A b.1.1 b.2‖ = 16 * ‖lineCoarseRestrictCov (trivialU L) 2 A b‖ := by
  rw [lineCoarseRestrictCov_trivialU_eq_blockResidual, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  ring

/-- **The `ker Q_2(U)` transfer**: on the COVARIANT kernel the FLAT block residual is `O(α)` in the
bond energy. `8192 = 256 · 32` = (the `ell⁴ = 16` squared) × (`RegularUQChain`'s `64/ell` at
`ell = 2`). -/
theorem sum_blockResidual_sq_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hker : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0) :
    (∑ μ : Fin 3, ∑ c ∈ CoarseLattice L 2, ‖blockResidual A c μ‖ ^ 2)
      ≤ 8192 * frobSupBond U ^ 2 * bondEnergy A := by
  have hidx : (∑ b : CoarseBond L 2, ‖blockResidual A b.1.1 b.2‖ ^ 2)
      = ∑ μ : Fin 3, ∑ c ∈ CoarseLattice L 2, ‖blockResidual A c μ‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    -- the `Fintype` instance on the coarse-site subtype is `LatticeOperators.instFintypeCoarseSite`,
    -- NOT `FinsetCoe.fintype`, so `Finset.sum_coe_sort` does not apply; `Finset.sum_subtype` takes
    -- the instance as an implicit argument and unifies with whichever one is in the goal.
    exact Finset.sum_congr rfl fun μ _ =>
      (Finset.sum_subtype (p := fun y : PeriodicLatticeSite L => y ∈ CoarseLattice L 2)
        (s := CoarseLattice L 2) (fun _ => Iff.rfl)
        (fun c => ‖blockResidual A c μ‖ ^ 2)).symm
  rw [← hidx]
  have hstep : ∀ b : CoarseBond L 2, ‖blockResidual A b.1.1 b.2‖ ^ 2
      = 256 * ‖lineCoarseRestrictCov (trivialU L) 2 A b
          - lineCoarseRestrictCov U 2 A b‖ ^ 2 := by
    intro b
    rw [hker b, sub_zero, norm_blockResidual]
    ring
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hstep b, ← Finset.mul_sum]
  have hdrift := AdalyFormal.Balaban.RegularUQChain.coarseDriftEnergy_le (ell := 2) U
    (by norm_num) hdvd A
  have h32 : (64 / ((2 : ℕ) : ℝ)) * frobSupBond U ^ 2 * bondEnergy A
      = 32 * frobSupBond U ^ 2 * bondEnergy A := by norm_num
  rw [h32] at hdrift
  nlinarith [hdrift]

/-- **The combined estimate, with the two intermediate constants ASSERTED rather than left in
prose** (the nested validator flagged `124416` and `1624064` as appearing only in a docstring; they
are now in a kernel-checked statement). `124416 = 2·62208` and
`1624064 = 62208·24 + 16·8192`, no regularity hypothesis at all. -/
theorem bondEnergy_le_gradEnergyCov_combined
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (hker : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0) :
    bondEnergy A ≤ 124416 * gradEnergyCov U A
      + 1624064 * (frobSupBond U ^ 2 * bondEnergy A) := by
  have hα0 : 0 ≤ frobSupBond U :=
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U
  have hfrob : ∀ b : Bond L,
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ frobSupBond U := fun b =>
    AdalyFormal.Balaban.RegularUPerturbation.frobNorm_le_frobSupBond U b
  have h1 := bondEnergy_le_gradEnergy_add_residual A hdvd
  have h2 := sum_blockResidual_sq_le U hdvd A hker
  have h3 := gradEnergy_le_gradEnergyCov hα0 U hfrob A
  linarith [h1, h2, h3]

/-- **THE COVARIANT GRADIENT POINCARÉ AT LEVEL `2`, UNCONDITIONAL** for `frobSupBond U ≤ 1/2000`.
This is exactly the input §9's `bondEnergy_le_plaqEnergy_of_covGradPoincare` had to assume. -/
theorem bondEnergy_le_gradEnergyCov_level_two
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (hsmall : frobSupBond U ≤ 1 / 2000)
    (A : Bond L → SuTwo)
    (hker : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0) :
    bondEnergy A ≤ 248832 * gradEnergyCov U A := by
  have hbe := AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg A
  have hα0 : 0 ≤ frobSupBond U :=
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U
  have hcomb := bondEnergy_le_gradEnergyCov_combined U hdvd A hker
  have hα2 : frobSupBond U ^ 2 ≤ 1 / 4000000 := by nlinarith [hsmall, hα0]
  have hkey : frobSupBond U ^ 2 * bondEnergy A ≤ (1 / 4000000) * bondEnergy A :=
    mul_le_mul_of_nonneg_right hα2 hbe
  linarith [hcomb, hkey]

/-- **THE GENERAL-`U` FIXED-LEVEL DIVERGENCE-FREE POINCARÉ, UNCONDITIONALLY.**

`bondEnergy A ≤ 497664 · plaqEnergy(curl_U A)` for EVERY background with
`frobSupBond U ≤ 1/(4·10⁷)`, every extent with `2 ∣ (L μ + 1)`, and every field in
`ker Q_2(U)` with `D_U^* A = 0`.

This is `Weitzenbock.kerQDivFreePoincareAtLevel_two` lifted off the flat background: the covariant
identity supplies the curl-versus-gradient step, §7 bounds its defect, §10 supplies the
residual-tolerant flat Poincaré, and `RegularUQChain.coarseDriftEnergy_le` supplies the kernel
transfer. It does NOT contradict `Weitzenbock.not_gradPoincareOnKerQ` or
`CoarseCurlPoincare.not_kerQDivFreePoincare`: both refute the LEVEL-UNIFORM statement, and the level
here is FIXED at `2`. -/
theorem bondEnergy_le_plaqEnergy_level_two_general_U
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (hsmall : frobSupBond U ≤ 1 / (4 * 10 ^ 7))
    (A : Bond L → SuTwo)
    (hker : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0)
    (hdiv : ∀ y : PeriodicLatticeSite L, gradCovariantAdjointValue U A y = 0) :
    bondEnergy A ≤ 497664 * plaqEnergy (curlCovariantLM U A) := by
  have hα0 : 0 ≤ frobSupBond U :=
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U
  have hfrob : ∀ b : Bond L,
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ frobSupBond U := fun b =>
    AdalyFormal.Balaban.RegularUPerturbation.frobNorm_le_frobSupBond U b
  have h2000 : frobSupBond U ≤ 1 / 2000 := by
    refine le_trans hsmall ?_
    norm_num
  have hpoin := bondEnergy_le_gradEnergyCov_level_two U hdvd h2000 A hker
  have hbe := AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg A
  have hge : gradEnergyCov U A - 72 * frobSupBond U * bondEnergy A
      ≤ plaqEnergy (curlCovariantLM U A) := by
    have h := weitzenbock_cov U A
    rw [AdalyFormal.Balaban.Weitzenbock.divEnergy_eq_zero_of_div_free U A hdiv, add_zero] at h
    have hd := abs_le.mp (abs_weitzDefect_le hα0 U hfrob A)
    linarith [hd.1, hd.2]
  have hkey : frobSupBond U * bondEnergy A ≤ (1 / (4 * 10 ^ 7)) * bondEnergy A :=
    mul_le_mul_of_nonneg_right hsmall hbe
  linarith [hpoin, hge, hkey]

/-! ### §11a — NON-VACUITY of the general-`U` theorem's hypothesis set

An `∀`-statement over an empty hypothesis set is worthless, and this tree has compiled collapses of
exactly that kind next door (`ScaleInduction.kerQDivFreePoincareAtLevel_zero`/`_one`). The four
hypotheses of `bondEnergy_le_plaqEnergy_level_two_general_U` are simultaneously satisfiable with
BOTH sides strictly positive, at `Weitzenbock`'s own witness.

**Disclosed limit, stated as a fact and not argued around:** the exhibited witness has `U ≡ 1`
(`frobSupBond = 0`, comfortably inside the threshold). The theorem is proved for every `U` with
`frobSupBond U ≤ 1/(4·10⁷)`, but no NON-trivial such `U` is exhibited here together with a nonzero
field in its covariant kernel — building one needs an explicit `SU(2)` element within `2.5·10⁻⁸` of
`1` AND an explicit nonzero element of `ker Q_2(U)` for that `U`, which is the kernel of a perturbed
operator and not a mechanical construction. -/

theorem frobSupBond_trivialU : frobSupBond (trivialU L) = 0 := by
  unfold AdalyFormal.Balaban.RegularUPerturbation.frobSupBond
  have h : ∀ b : Bond L,
      frobNorm ((trivialU L b : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0 := by
    intro b
    show frobNorm (((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0
    rw [show ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl,
      sub_self]
    unfold AdalyFormal.Balaban.RMapLipschitz.frobNorm AdalyFormal.Balaban.RMapLipschitz.frobSq
    simp
  rw [show (fun b : Bond L => frobNorm ((trivialU L b : Matrix (Fin 2) (Fin 2) ℂ) - 1))
      = fun _ => (0 : ℝ) from funext h]
  exact Finset.sup'_const _ _

/-- **The general-`U` level-2 theorem is inhabited, with both sides strictly positive.** -/
theorem level_two_general_U_nonvacuous {w : SuTwo} (hw : w ≠ 0) :
    0 < bondEnergy (AdalyFormal.Balaban.Weitzenbock.nvField w)
      ∧ bondEnergy (AdalyFormal.Balaban.Weitzenbock.nvField w)
          ≤ 497664 * plaqEnergy (curlCovariantLM
              (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt)
              (AdalyFormal.Balaban.Weitzenbock.nvField w))
      ∧ 0 < plaqEnergy (curlCovariantLM (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt)
          (AdalyFormal.Balaban.Weitzenbock.nvField w)) := by
  obtain ⟨hdvd, hker, hdiv, hbe, hpe⟩ :=
    AdalyFormal.Balaban.Weitzenbock.kerQDivFree_level_two_nonvacuous hw
  refine ⟨hbe, ?_, hpe⟩
  exact bondEnergy_le_plaqEnergy_level_two_general_U
    (trivialU AdalyFormal.Balaban.Weitzenbock.twoExt) hdvd
    (by rw [frobSupBond_trivialU]; norm_num)
    (AdalyFormal.Balaban.Weitzenbock.nvField w) hker hdiv

#print axioms lineCoarseRestrictCov_trivialU_eq_blockResidual
#print axioms norm_blockResidual
#print axioms sum_blockResidual_sq_le
#print axioms bondEnergy_le_gradEnergyCov_combined
#print axioms bondEnergy_le_gradEnergyCov_level_two
#print axioms bondEnergy_le_plaqEnergy_level_two_general_U
#print axioms frobSupBond_trivialU
#print axioms level_two_general_U_nonvacuous

/-! ## §12 — CONSISTENCY WITH THE TREE'S OWN REFUTATIONS, and the load-bearing hypothesis

Two refutations in this tree could collide with §11, and they must be checked rather than waved at.

* `Weitzenbock.not_gradPoincareOnKerQ` and `CoarseCurlPoincare.not_kerQDivFreePoincare` refute the
  LEVEL-UNIFORM statements (one constant for every `ell`). §11 is at the single FIXED level `2`, so
  it cannot bear on them in either direction.
* **`ScaleInduction.not_fibreReversePoincareAtLevel_two` is at the FIXED level `2`** — the dangerous
  one. Its refuting witness is `RegularUGamma0.chiField w`: nonzero, in `ker Q_2(1)`, and CURL-FREE,
  so `bondEnergy > 0 = K · plaqEnergy(curl)` for every `K`. §11's conclusion is exactly of that
  shape. There is no contradiction for one reason only: §11 also assumes `D_U^* A = 0`, and
  `chiField` has NONZERO divergence (`RegularUGamma0.gradAdjoint_chiField_ne_zero`), so it is
  outside §11's hypothesis set.

This is compiled below rather than asserted, and in the strong direction: `divFree_is_load_bearing`
proves that DROPPING the divergence clause makes the level-`2` statement FALSE for EVERY constant —
so the clause is not decoration, and §11's conclusion is not obtainable from the kernel condition
alone. -/

/-- The refuting witness of the fibre reverse Poincaré fails §11's divergence hypothesis. -/
theorem chiField_fails_divFree (h2 : (2 : ℕ) ∣ (L 0 + 1)) {w : SuTwo} (hw : w ≠ 0) :
    ¬ (∀ y : PeriodicLatticeSite L,
        gradCovariantAdjointValue (trivialU L)
          (AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w) y = 0) := fun h =>
  AdalyFormal.Balaban.RegularUGamma0.gradAdjoint_chiField_ne_zero h2 hw (h _)

/-- **THE DIVERGENCE CLAUSE IS LOAD-BEARING.** For EVERY constant `K`, the level-`2` statement
WITHOUT the divergence hypothesis is false — already at the flat background. So §11 is not a
disguised statement about the kernel alone, and it does not contradict
`ScaleInduction.not_fibreReversePoincareAtLevel_two`. -/
theorem divFree_is_load_bearing (h2 : (2 : ℕ) ∣ (L 0 + 1)) {w : SuTwo} (hw : w ≠ 0) (K : ℝ) :
    ¬ (∀ A : Bond L → SuTwo,
        (∀ c : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 A c = 0) →
        bondEnergy A ≤ K * plaqEnergy (curlCovariantLM (trivialU L) A)) := by
  intro h
  obtain ⟨hker, _, hfail⟩ :=
    AdalyFormal.Balaban.RegularUGamma0.no_reverse_poincare_on_kerQ h2 hw K
  exact hfail (h (AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w) hker)

/-- The full consistency statement, as one compiled conjunction: the refuting witness satisfies §11's
KERNEL hypothesis, violates §11's CONCLUSION for every constant, and therefore must — and does —
violate §11's DIVERGENCE hypothesis. -/
theorem consistent_with_fibre_refutation (h2 : (2 : ℕ) ∣ (L 0 + 1)) {w : SuTwo} (hw : w ≠ 0) :
    (∀ c : CoarseBond L 2,
        lineCoarseRestrictCov (trivialU L) 2
          (AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w) c = 0)
      ∧ plaqEnergy (curlCovariantLM (trivialU L)
          (AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w)) = 0
      ∧ ¬ (bondEnergy (AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w)
            ≤ 497664 * plaqEnergy (curlCovariantLM (trivialU L)
              (AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w)))
      ∧ ¬ (∀ y : PeriodicLatticeSite L,
            gradCovariantAdjointValue (trivialU L)
              (AdalyFormal.Balaban.RegularUGamma0.chiField (L := L) w) y = 0) := by
  obtain ⟨hker, hzero, hfail⟩ :=
    AdalyFormal.Balaban.RegularUGamma0.no_reverse_poincare_on_kerQ h2 hw 497664
  exact ⟨hker, hzero, hfail, chiField_fails_divFree h2 hw⟩

#print axioms chiField_fails_divFree
#print axioms divFree_is_load_bearing
#print axioms consistent_with_fibre_refutation

end AdalyFormal.Balaban.WeitzenbockCovariant
