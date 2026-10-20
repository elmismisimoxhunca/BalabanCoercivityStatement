/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.LatticeOperators

set_option autoImplicit false

/-! **IMPORT FIX (substrate-wiring lane, 2026-07-24)**: this file's import was
`AdalyFormal.Balaban.HjMinimizer`, but a grep audit (confirmed: no `Level`, no
`coarseRestrictSite`, no other `KernelSubspace`/`HjMinimizer`-qualified use anywhere in this
file's actual code — only docstring prose mentions) shows the file uses NOTHING from
`HjMinimizer.lean` or `KernelSubspace.lean`; it only needs `LatticeOperators`/`AdmissibleSubspace`
(both already opened below). The import was vestigial. **Fixing it is FORCED, not cosmetic**: the
wiring plan (`GOAL_LEMMA.md` §3 Piece 1, Kimi's `KIMI_VERDICT.md` §J2) requires
`HjMinimizer.lean` to import `LineIntegralAveraging.lean` (for `lineCoarseRestrictCLM`), and
`LineIntegralAveraging.lean` imports `CoarseShiftCovariance`/`U1CommutingSquare`, both of which
import `CoarseCurl.lean` — so the OLD `CoarseCurl → HjMinimizer` edge would have closed a genuine
import CYCLE (`HjMinimizer → LineIntegralAveraging → CoarseShiftCovariance → CoarseCurl →
HjMinimizer`). Removing this dead edge breaks the cycle with zero semantic change to this file
(verified: `lake build AdalyFormal.Balaban.CoarseCurl` succeeds unchanged below). -/

/-!
# The coarse curl `∂₁'` — CMP95 (1.67) / CMP96 (2.118)'s missing operator

**Task** (see the dispatch mandate): `Balaban/HjMinimizer.lean` §6 names, as an explicit residual,
that the quantitative bound `γ₀‖∂₁'B‖² ≤ ⟨B,Δ_jB⟩ ≤ γ₁‖∂₁'B‖²` (CMP95 (1.67)/CMP96 (2.118)) is
stated in terms of a curl of the COARSE bond field `B : CoarseBondSpace L ell`, and that "no
coarse-lattice plaquette structure / coarse curl is built anywhere in this tree yet." This module
closes that gap: it builds the coarse plaquette type, the coarse curl `∂₁'` as a genuine
`ContinuousLinearMap`, proves non-vacuity, and settles (by explicit refutation, not proof) whether
block-averaging commutes with taking the curl.

## What "coarse curl" means, made precise before building it

`CoarseBondSpace L ell = EuclideanSpace ℝ (CoarseBond L ell)` (`LatticeOperators.lean` §8) is
indexed by `CoarseBond L ell := {y // y ∈ CoarseLattice L ell} × Fin 3` — a coarse bond is a
COARSE-LATTICE site plus a direction, i.e. THE COARSE LATTICE'S OWN adjacency structure: a coarse
bond in direction `μ` based at `y` connects `y` to the NEXT coarse-lattice point in direction `μ`,
which is `ell` FINE lattice steps away (coarse-lattice points are spaced `ell` apart along each
axis, by `CoarseLattice`'s own definition, `mem_CoarseLattice`). So the coarse curl's "shift" must
be the ELL-FOLD iterate of the fine shift (`coarseShift` below), not a single fine step — a single
fine step out of a `CoarseLattice` member is generically NOT another `CoarseLattice` member (adding
`1` to a multiple of `ell` is a multiple of `ell` only if `ell ∣ 1`), so it could not even be used
to index into `CoarseBondSpace`. This is genuinely forced by the TYPE `CoarseBondSpace L ell`
already fixed in `HjMinimizer.lean`/`LatticeOperators.lean` — not a free design choice.

## What this module builds

1. **`coarseShift`** (§1) — the `ell`-fold iterate of `periodicLatticeShift`, the coarse lattice's
   own adjacency, together with `coarseShift_mem_coarseLattice`: GIVEN the tileability hypothesis
   `∀ μ, ell ∣ (L μ + 1)` (the SAME hypothesis `AdmissibleSubspace.coarseLattice_exists`/
   `AlignedCoarseCenter` already carry, LAW-19 reuse, not a fresh assumption), shifting a
   `CoarseLattice` member by `ell` steps in any one direction lands back in `CoarseLattice` — a
   genuine (not free) fact about nat-mod arithmetic, proved from `Fin.val_add`/`Nat.mod_mod_of_dvd`,
   not asserted.
2. **`CoarsePlaquette`/`CoarsePlaquetteSpace`** (§2) — indexed EXACTLY the way
   `PeriodicLatticePlaquette L` is (`Target.ClayStatement`'s own convention, LAW-19): a coarse site
   plus an ordered direction pair `μ < ν`.
3. **`coarseCurl`/`coarseCurlCLM`** (§3) — `∂₁' : CoarseBondSpace L ell →L[ℝ] CoarsePlaquetteSpace
   L ell`, built by MIRRORING `LatticeOperators.curlValue`'s exact four-term shape
   (`B(y,μ)+B(shift_μy,ν)-B(shift_νy,μ)-B(y,ν)`), substituting `coarseShift` for the fine
   `periodicLatticeShift` — the literal coarse analogue of the already-audited fine construction
   (LAW-19), not a fresh invention of the plaquette geometry.
4. **Non-vacuity** (§4): `CoarsePlaquette` is INHABITED on the shared witness lattice, and
   `coarseCurlCLM` is NOT the zero map (an explicit, hand-computed nonzero witness).
5. **`coarsePlaquetteRestrict`/`coarsePlaquetteRestrictCLM`** (§5) — the LITERAL analogue of
   `LatticeOperators.coarseRestrict` (same block-average recipe, same `1/ell⁴` coefficient) applied
   to PLAQUETTE-indexed data instead of bond-indexed data — the natural candidate for
   "`coarseRestrictCLM` acting on the fine curl," i.e. the RHS the mandate's item 3 asks about.
6. **THE COMPATIBILITY THEOREM — settled by REFUTATION, not proof** (§6): `coarseCurlCLM` does
   **NOT** commute with `coarseRestrictCLM` in the sense `coarseCurlCLM(coarseRestrictCLM A) =
   coarsePlaquetteRestrictCLM(curlCLM A)`. An explicit witness bond configuration on the shared
   witness lattice is exhibited on which the two sides are PROVABLY DIFFERENT rationals (`-1/16`
   vs. `0`) — kernel-checked, not a numerical approximation. §6's docstring explains PRECISELY why:
   the identity that DOES hold exactly (CMP95 (1.20)'s abelian gradient-telescoping,
   `CovariantHjMinimizer.coarseRestrictCovariant_flat_gradient_telescopes`) uses a SINGLE fine-step
   shift of the base point, whereas `coarseCurl`'s shift (forced by the `CoarseBondSpace` type, see
   above) is the `ell`-FOLD coarse shift — these are two different operations, and the naive
   composite does not identify them. This is exactly the "wrong object" failure mode the mandate's
   warning about proving intertwining "by linearity" was guarding against, made precise here as a
   proved DISAGREEMENT rather than a silently-accepted analogy.

## What this module does NOT build (named, not silently dropped)

* **The su(2)-valued analogue.** The dispatch mandate asks for this "if budget remains." A
  concurrent lane is building a bond-indexed su(2) carrier at `Balaban/BondSU2Space.lean` (READ-ONLY
  for this module, per the dispatch's explicit write-scope restriction) — NOT wired into a
  su(2)-valued coarse curl here. Genuinely NOT attempted: this module's §6 refutation ALREADY shows
  the ℝ-valued (abelian) coarse curl fails to intertwine with block-averaging on the FLAT/abelian
  sector, which is the STRICTLY EASIER case (the su(2)/`Ad`-covariant sector inherits every abelian
  obstruction and adds its own nonabelian ones, per `CovariantHjMinimizer.lean`'s own documented
  `coarseRestrictCovariant_ad_action_witness` finding) — so no positive result is plausible there
  that is not already precluded by this module's abelian-level refutation. Named as the residual the
  mandate anticipated, not attempted.
* **The quantitative bound itself** (CMP95 (1.67)/CMP96 (2.118), `γ₀‖∂₁'B‖² ≤ ⟨B,Δ_jB⟩ ≤
  γ₁‖∂₁'B‖²`): this module supplies the OBJECT (`∂₁'` = `coarseCurl`) the bound needs to even be
  STATED; the bound's own proof (needing the closed-form momentum-space computation,
  `HjMinimizer.lean`'s own already-named residual) is separate, harder content, unchanged in scope
  by this module.
* **Wiring `coarseCurl` into `HjMinimizer.lean`/`Coercivity.lean`** — both files are outside this
  lane's write scope (a concurrent lane holds `HjMinimizer.lean` proving the `A₀`-existence
  residual); the exact statement the wiring would need (`γ₀‖coarseCurl B‖² ≤ deltaJQuadForm ... ≤
  γ₁‖coarseCurl B‖²`) is now STATABLE using this module's `coarseCurlCLM`, but stating/proving it is
  a follow-up lane's job, not this one's.
-/

namespace AdalyFormal.Balaban.CoarseCurl

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators

variable {L : PeriodicLatticeExtent}

/-! ## §1. `coarseShift` — the coarse lattice's OWN adjacency, the `ell`-fold iterate of the fine
shift, and the fact (given tileability) that it preserves `CoarseLattice` membership -/

/-- **`coarseShift y ell μ` — the site `ell` fine-lattice steps from `y` in direction `μ`.** The
coarse lattice's own "next neighbour" operation: `CoarseLattice` members are spaced exactly `ell`
apart (`AdmissibleSubspace.mem_CoarseLattice`), so THIS, not a single fine step, is the shift a
curl operator built on `CoarseBondSpace`'s own indexing must use. A plain (non-`noncomputable`)
`def`, since `periodicLatticeShift` and `Function.iterate` are both computable — needed below so
the non-vacuity witnesses (§4) can be checked by `decide`. -/
def coarseShift {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) (ell : ℕ) (μ : Fin 3) :
    PeriodicLatticeSite L :=
  (fun z => periodicLatticeShift z μ)^[ell] y

#print axioms coarseShift

/-- The `μ`-component of a single fine shift, isolated as its own lemma so it can be `rw`-applied
without `simp`'s blanket unfolding touching the (syntactically similar) `periodicLatticeShift`
occurrence hidden inside the iterating lambda's own definition. -/
theorem periodicLatticeShift_self {L : PeriodicLatticeExtent} (w : PeriodicLatticeSite L)
    (μ : Fin 3) : (periodicLatticeShift w μ) μ = w μ + 1 :=
  Function.update_self μ _ w

#print axioms periodicLatticeShift_self

/-- **`coarseShift` leaves every OTHER coordinate untouched** — each single fine step only updates
coordinate `μ`, so `ell` iterates of it still only ever touch coordinate `μ`. Proved by induction
on `ell`, using `Function.update_of_ne` (the same primitive
`LatticeOperators.periodicLatticeShift_comm` already uses). -/
theorem coarseShift_apply_ne {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) (ell : ℕ)
    (μ ν : Fin 3) (h : ν ≠ μ) : coarseShift y ell μ ν = y ν := by
  unfold coarseShift
  induction ell with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [show periodicLatticeShift ((fun z => periodicLatticeShift z μ)^[n] y) μ ν =
        ((fun z => periodicLatticeShift z μ)^[n] y) ν from
      Function.update_of_ne h _ _]
    exact ih

/-- **`coarseShift`'s `μ`-coordinate advances by `ell`, mod the periodic extent** — the closed-form
value underlying the whole construction, proved by induction using `Fin.val_add`
(`(a+b).val=(a.val+b.val)%n`, Lean core) and `Fin.val_one'` (`(1:Fin n).val = 1 % n`, needing only
the automatic `NeZero (L μ + 1)` instance). -/
theorem coarseShift_val_eq {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) (ell : ℕ)
    (μ : Fin 3) :
    ((coarseShift y ell μ) μ).val = ((y μ).val + ell) % (L μ + 1) := by
  unfold coarseShift
  induction ell with
  | zero => simp [Nat.mod_eq_of_lt (y μ).isLt]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [periodicLatticeShift_self]
    rw [Fin.val_add, ih, Fin.val_one']
    rw [← Nat.add_mod]
    congr 1

/-- **THE GEOMETRIC FACT (given tileability): `coarseShift` preserves `CoarseLattice`
membership.** Every `CoarseLattice` member shifted `ell` steps in any one direction is again a
`CoarseLattice` member — the fact that makes `coarseCurl` (§3) well-typed on `CoarseBondSpace L
ell`'s own subtype-indexing. Needs the SAME tileability hypothesis `∀ μ, ell ∣ (L μ + 1)` that
`AdmissibleSubspace.coarseLattice_exists`/`AlignedCoarseCenter` already require (LAW-19, not a fresh
assumption). Proved via `Nat.mod_mod_of_dvd` (Lean core, `a % b % c = a % c` when `c ∣ b`) and
`Nat.mul_mod_right`. -/
theorem coarseShift_mem_coarseLattice {L : PeriodicLatticeExtent} {ell : ℕ}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) :
    coarseShift y ell μ ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice] at hy ⊢
  intro ν
  by_cases hμν : ν = μ
  · subst hμν
    rw [coarseShift_val_eq]
    rw [Nat.mod_mod_of_dvd _ (hdvd ν)]
    obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero (hy ν)
    have heq : (y ν).val + ell = ell * (j + 1) := by rw [hj]; ring
    rw [heq]
    exact Nat.mul_mod_right ell (j + 1)
  · rw [coarseShift_apply_ne y ell μ ν hμν]
    exact hy ν

#print axioms coarseShift_apply_ne
#print axioms coarseShift_val_eq
#print axioms coarseShift_mem_coarseLattice

/-! ## §2. `CoarsePlaquette`/`CoarsePlaquetteSpace` — indexed exactly as `PeriodicLatticePlaquette`
(`Target.ClayStatement`'s own convention: a base site plus an ordered direction pair `μ < ν`,
LAW-19) -/

/-- **Coarse plaquettes**: a `CoarseLattice`-member base site plus an ordered direction pair —
the LITERAL coarse analogue of `PeriodicLatticePlaquette L := PeriodicLatticeSite L ×
PeriodicPlaquetteDirections`, restricting only the base-site component to `CoarseLattice`, exactly
mirroring how `CoarseBond` (`LatticeOperators.lean` §8) restricts `PeriodicLatticeEdge`. -/
abbrev CoarsePlaquette (L : PeriodicLatticeExtent) (ell : ℕ) :=
  {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell} × PeriodicPlaquetteDirections

/-- `CoarsePlaquette L ell` as a finite-dimensional real Hilbert space, matching
`LatticeOperators.PlaquetteSpace`'s own promotion pattern (LAW-19). -/
abbrev CoarsePlaquetteSpace (L : PeriodicLatticeExtent) (ell : ℕ) :=
  EuclideanSpace ℝ (CoarsePlaquette L ell)

/-- The identity-on-underlying-functions equivalence. -/
noncomputable def coarsePlaquetteEquiv (L : PeriodicLatticeExtent) (ell : ℕ) :
    CoarsePlaquetteSpace L ell ≃ₗ[ℝ] (CoarsePlaquette L ell → ℝ) :=
  (EuclideanSpace.equiv (CoarsePlaquette L ell) ℝ).toLinearEquiv

/-! ## §3. `coarseCurl`/`coarseCurlCLM` — `∂₁'`, mirroring `LatticeOperators.curlValue`'s exact
four-term shape, substituting `coarseShift` for the fine `periodicLatticeShift` -/

/-- **`(∂₁'B)(p) := B(y,μ) + B(coarseShift_μ y,ν) - B(coarseShift_ν y,μ) - B(y,ν)`** — the coarse
curl, the LITERAL coarse analogue of `LatticeOperators.curlValue` (CMP95 eq. 1.2), substituting the
coarse lattice's own adjacency (`coarseShift`, §1) for the fine one. Needs the tileability
hypothesis `hdvd` so `coarseShift_mem_coarseLattice` can supply the membership proofs the two
shifted lookups require. -/
def coarseCurlValue {L : PeriodicLatticeExtent} {ell : ℕ}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : CoarseBond L ell → ℝ)
    (p : CoarsePlaquette L ell) : ℝ :=
  let y := p.1
  let μ := p.2.1.1
  let ν := p.2.1.2
  B (y, μ) +
    B (⟨coarseShift y.1 ell μ, coarseShift_mem_coarseLattice hdvd y.2 μ⟩, ν) -
    B (⟨coarseShift y.1 ell ν, coarseShift_mem_coarseLattice hdvd y.2 ν⟩, μ) -
    B (y, ν)

#print axioms coarseCurlValue

theorem coarseCurlValue_add {L : PeriodicLatticeExtent} {ell : ℕ}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B1 B2 : CoarseBond L ell → ℝ)
    (p : CoarsePlaquette L ell) :
    coarseCurlValue hdvd (B1 + B2) p = coarseCurlValue hdvd B1 p + coarseCurlValue hdvd B2 p := by
  simp only [coarseCurlValue, Pi.add_apply]; ring

theorem coarseCurlValue_smul {L : PeriodicLatticeExtent} {ell : ℕ}
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (c : ℝ) (B : CoarseBond L ell → ℝ)
    (p : CoarsePlaquette L ell) :
    coarseCurlValue hdvd (c • B) p = c * coarseCurlValue hdvd B p := by
  simp only [coarseCurlValue, Pi.smul_apply, smul_eq_mul]; ring

/-- `∂₁'` as a genuine `LinearMap`. -/
def coarseCurlLM (L : PeriodicLatticeExtent) (ell : ℕ) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    (CoarseBond L ell → ℝ) →ₗ[ℝ] (CoarsePlaquette L ell → ℝ) where
  toFun B := coarseCurlValue hdvd B
  map_add' B1 B2 := funext fun p => coarseCurlValue_add hdvd B1 B2 p
  map_smul' c B := funext fun p => coarseCurlValue_smul hdvd c B p

#print axioms coarseCurlValue_add
#print axioms coarseCurlValue_smul
#print axioms coarseCurlLM

/-- `∂₁' : CoarseBondSpace L ell →ₗ[ℝ] CoarsePlaquetteSpace L ell`, transported across
`coarseBondEquiv`/`coarsePlaquetteEquiv`. -/
noncomputable def coarseCurlLMH (L : PeriodicLatticeExtent) (ell : ℕ)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    CoarseBondSpace L ell →ₗ[ℝ] CoarsePlaquetteSpace L ell :=
  (coarsePlaquetteEquiv L ell).symm.toLinearMap.comp
    ((coarseCurlLM L ell hdvd).comp (coarseBondEquiv L ell).toLinearMap)

/-- **`∂₁'`, as a genuine `ContinuousLinearMap`** — the mandate's primary deliverable. Finite-
dimensional domain makes every linear map continuous (`LinearMap.toContinuousLinearMap`), exactly
as `LatticeOperators.curlCLM` is built. -/
noncomputable def coarseCurlCLM (L : PeriodicLatticeExtent) (ell : ℕ)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    CoarseBondSpace L ell →L[ℝ] CoarsePlaquetteSpace L ell :=
  LinearMap.toContinuousLinearMap (coarseCurlLMH L ell hdvd)

theorem coarseCurlCLM_apply (L : PeriodicLatticeExtent) (ell : ℕ)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : CoarseBondSpace L ell) :
    coarsePlaquetteEquiv L ell (coarseCurlCLM L ell hdvd B) =
      coarseCurlValue hdvd (coarseBondEquiv L ell B) := rfl

#print axioms coarseCurlLMH
#print axioms coarseCurlCLM_apply

/-! ## §4. NON-VACUITY — `CoarsePlaquette` is inhabited and `coarseCurl` is NOT the zero map, on
the shared witness lattice (`AdmissibleSubspace.witnessL`, `witnessEll = 2`) -/

/-- The tileability hypothesis, discharged concretely on the shared witness lattice: `witnessEll =
2` divides `witnessL μ + 1 = 4` in every coordinate (the SAME fact
`AdmissibleSubspace.witness_coarseLattice_exists` already exercises). -/
theorem witnessHdvd : ∀ μ : Fin 3, AdmissibleSubspace.witnessEll ∣
    (AdmissibleSubspace.witnessL μ + 1) := by
  intro μ
  fin_cases μ <;> decide

/-- A valid direction pair `μ < ν`, `(0,1)`. -/
def coarseWitnessDirs : PeriodicPlaquetteDirections := ⟨(0, 1), by decide⟩

#print axioms coarseWitnessDirs

/-- **Non-vacuity #1: `CoarsePlaquette` is genuinely inhabited** on the shared witness lattice —
not an empty type that would make every subsequent claim about it vacuous. -/
theorem coarsePlaquette_witness_nonempty :
    Nonempty (CoarsePlaquette AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll) :=
  ⟨⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, coarseWitnessDirs⟩

/-- **A concrete nonzero coarse-bond configuration**, mirroring
`LatticeOperators.witnessBondConfig`'s exact style: the coordinate-`0` reading of the coarse
bond's base site (ignoring direction and the block-average machinery entirely — this is a DIRECT
coarse-bond-level witness, not built via `coarseRestrict`, so no `Finset.sum` reasoning is needed
to evaluate it). -/
noncomputable def coarseWitnessBondConfig :
    CoarseBond AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll → ℝ :=
  fun b => ((b.1.1 0 : Fin 4).val : ℝ)

/-- `coarseShift witnessY witnessEll 0` has coordinate `0` equal to `2` — two fine steps in
direction `0` from `witnessY = (0,0,0)`, no wraparound (`0+2=2 < 4`). Kernel-checked via `decide`
(both `coarseShift` and `Fin 4` equality are computable, no `noncomputable` obstruction). -/
theorem coarseShift_witness_0_coord0 :
    (coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 0) 0 = (2 : Fin 4) := by
  decide

/-- `coarseShift witnessY witnessEll 1` leaves coordinate `0` at its original value `0` — direction
`1`'s shift never touches coordinate `0` (`coarseShift_apply_ne`, specialized concretely here via
`decide` for the acceptance-test's own self-containedness). -/
theorem coarseShift_witness_1_coord0 :
    (coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 1) 0 = (0 : Fin 4) := by
  decide

/-- **Non-vacuity #2 — THE ACCEPTANCE TEST: `coarseCurl` is NOT the zero map.** On the witness
configuration above, at the witness plaquette, `coarseCurlValue` evaluates to `2 ≠ 0` — the coarse
curl genuinely sees this coarse bond configuration; it is not identically zero on trivial/degenerate
input (the exact failure mode the mandate's "NON-VACUITY IS MANDATORY" warning names). -/
theorem coarseCurl_witness_ne_zero :
    coarseCurlValue witnessHdvd coarseWitnessBondConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, coarseWitnessDirs)
      ≠ 0 := by
  simp only [coarseCurlValue, coarseWitnessBondConfig, coarseWitnessDirs]
  show ((AdmissibleSubspace.witnessY 0 : Fin 4).val : ℝ)
      + (((coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 0) 0 : Fin 4).val
          : ℝ)
      - (((coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 1) 0 : Fin 4).val
          : ℝ)
      - ((AdmissibleSubspace.witnessY 0 : Fin 4).val : ℝ) ≠ 0
  rw [coarseShift_witness_0_coord0, coarseShift_witness_1_coord0]
  simp [AdmissibleSubspace.witnessY]

#print axioms coarsePlaquette_witness_nonempty
#print axioms witnessHdvd
#print axioms coarseShift_witness_0_coord0
#print axioms coarseShift_witness_1_coord0
#print axioms coarseCurl_witness_ne_zero

/-! ## §5. `coarsePlaquetteRestrict`/`coarsePlaquetteRestrictCLM` — the LITERAL `coarseRestrict`
recipe (same block average, same `1/ell⁴` coefficient), applied to PLAQUETTE-indexed data instead of
BOND-indexed data. The natural candidate for "`coarseRestrictCLM` acting on the fine curl" — the
mandate's item 3 RHS. -/

/-- **`(Q_ellF)(p) := (1/ell⁴) Σ_{x∈blockOf p.1.1 ell} F(x,p.2)`** — the exact `coarseRestrict`
averaging recipe (`LatticeOperators.coarseRestrict`, LAW-19 reuse of the recipe/normalization),
applied to a PLAQUETTE-valued field `F` instead of a bond-valued one. -/
noncomputable def coarsePlaquetteRestrict {L : PeriodicLatticeExtent} (ell : ℕ)
    (F : PeriodicLatticePlaquette L → ℝ) (p : CoarsePlaquette L ell) : ℝ :=
  (1 / (ell : ℝ) ^ 4) * ∑ x ∈ blockOf p.1.1 ell, F (x, p.2)

theorem coarsePlaquetteRestrict_add {L : PeriodicLatticeExtent} (ell : ℕ)
    (F1 F2 : PeriodicLatticePlaquette L → ℝ) (p : CoarsePlaquette L ell) :
    coarsePlaquetteRestrict ell (F1 + F2) p =
      coarsePlaquetteRestrict ell F1 p + coarsePlaquetteRestrict ell F2 p := by
  simp only [coarsePlaquetteRestrict, Pi.add_apply]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]

theorem coarsePlaquetteRestrict_smul {L : PeriodicLatticeExtent} (ell : ℕ) (c : ℝ)
    (F : PeriodicLatticePlaquette L → ℝ) (p : CoarsePlaquette L ell) :
    coarsePlaquetteRestrict ell (c • F) p = c * coarsePlaquetteRestrict ell F p := by
  simp only [coarsePlaquetteRestrict, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- `coarsePlaquetteRestrict` as a genuine `LinearMap`. -/
noncomputable def coarsePlaquetteRestrictLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    (PeriodicLatticePlaquette L → ℝ) →ₗ[ℝ] (CoarsePlaquette L ell → ℝ) where
  toFun F := coarsePlaquetteRestrict ell F
  map_add' F1 F2 := funext fun p => coarsePlaquetteRestrict_add ell F1 F2 p
  map_smul' c F := funext fun p => coarsePlaquetteRestrict_smul ell c F p

#print axioms coarsePlaquetteRestrict_add
#print axioms coarsePlaquetteRestrict_smul
#print axioms coarsePlaquetteRestrictLM

/-- `coarsePlaquetteRestrict : PlaquetteSpace L →ₗ[ℝ] CoarsePlaquetteSpace L ell`, transported. -/
noncomputable def coarsePlaquetteRestrictLMH (L : PeriodicLatticeExtent) (ell : ℕ) :
    PlaquetteSpace L →ₗ[ℝ] CoarsePlaquetteSpace L ell :=
  (coarsePlaquetteEquiv L ell).symm.toLinearMap.comp
    ((coarsePlaquetteRestrictLM L ell).comp (plaquetteEquiv L).toLinearMap)

/-- **`coarsePlaquetteRestrict`, as a genuine `ContinuousLinearMap`.** -/
noncomputable def coarsePlaquetteRestrictCLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    PlaquetteSpace L →L[ℝ] CoarsePlaquetteSpace L ell :=
  LinearMap.toContinuousLinearMap (coarsePlaquetteRestrictLMH L ell)

theorem coarsePlaquetteRestrictCLM_apply (L : PeriodicLatticeExtent) (ell : ℕ)
    (F : PlaquetteSpace L) :
    coarsePlaquetteEquiv L ell (coarsePlaquetteRestrictCLM L ell F) =
      coarsePlaquetteRestrict ell (plaquetteEquiv L F) := rfl

#print axioms coarsePlaquetteRestrictLMH
#print axioms coarsePlaquetteRestrictCLM_apply

/-! ## §6. THE COMPATIBILITY THEOREM — settled by REFUTATION, not proof

Does `coarseCurlCLM(coarseRestrictCLM A) = coarsePlaquetteRestrictCLM(curlCLM A)`? Answer: **NO** —
an explicit witness on the shared witness lattice makes the two sides PROVABLY DIFFERENT rationals
(`-1/16` vs. `0`). This is NOT a failure of nerve or an unexamined gap: the identity that DOES hold
exactly on this lattice (CMP95 (1.20)'s abelian gradient-telescoping,
`CovariantHjMinimizer.coarseRestrictCovariant_flat_gradient_telescopes`) uses a SINGLE fine-lattice
shift of the base point, while `coarseCurl` (forced by the `CoarseBondSpace` type, see the module
docstring) uses the `ell`-FOLD coarse shift. These are different operations on a general (or even a
FLAT/pure-gauge) bond configuration, and the naive composite does not identify them — exactly the
"prove it by linearity" trap the dispatch mandate warned about, made precise here as a proved
disagreement. -/

/-- `periodicLatticeShift (·) μ` is injective — the standard fact underlying the
`Finset.sum_eq_single`-style block-sum collapses below (which SITE'S single-step shift lands on a
given target). -/
theorem periodicLatticeShift_injective {L : PeriodicLatticeExtent} (μ : Fin 3) :
    Function.Injective (fun x : PeriodicLatticeSite L => periodicLatticeShift x μ) := by
  intro x y hxy
  simp only at hxy
  funext ν
  by_cases h : ν = μ
  · subst h
    have h1 : periodicLatticeShift x ν ν = periodicLatticeShift y ν ν := by rw [hxy]
    rw [periodicLatticeShift_self, periodicLatticeShift_self] at h1
    exact add_right_cancel h1
  · have h1 : periodicLatticeShift x μ ν = periodicLatticeShift y μ ν := by rw [hxy]
    rwa [show periodicLatticeShift x μ ν = x ν from Function.update_of_ne h _ _,
         show periodicLatticeShift y μ ν = y ν from Function.update_of_ne h _ _] at h1

#print axioms periodicLatticeShift_injective

/-- The witness curl bond's SITE — the single fine-step shift of `witnessY` in direction `0`,
DEFINED as this shift (not merely proved equal to it) so `periodicLatticeShift witnessY 0 =
curlWitnessSite` holds by `rfl`. -/
def curlWitnessSite : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
  periodicLatticeShift AdmissibleSubspace.witnessY 0

#print axioms curlWitnessSite

/-- The witness curl bond: `(curlWitnessSite, 1)`. -/
def curlWitnessBond : Bond AdmissibleSubspace.witnessL := (curlWitnessSite, (1 : Fin 3))

#print axioms curlWitnessBond

/-- The witness bond configuration: an indicator on the single bond `curlWitnessBond`. -/
noncomputable def curlWitnessConfig : Bond AdmissibleSubspace.witnessL → ℝ :=
  fun b => if b = curlWitnessBond then 1 else 0

theorem curlWitnessSite_coord0 : curlWitnessSite 0 = (1 : Fin 4) := by decide

/-- **A direction mismatch always forces the indicator to vanish**, regardless of the site. -/
theorem curlWitnessConfig_eq_zero_of_dir_ne {x : PeriodicLatticeSite AdmissibleSubspace.witnessL}
    {d : Fin 3} (hd : d ≠ 1) : curlWitnessConfig (x, d) = 0 := by
  unfold curlWitnessConfig curlWitnessBond
  rw [if_neg]
  intro h
  exact hd (Prod.ext_iff.mp h).2

/-- **Coarse-curl term 1** (`B(y,0)`, `y = witnessY`) — direction mismatch, always `0`. -/
theorem coarseRestrict_witness_term1 :
    coarseRestrict AdmissibleSubspace.witnessEll curlWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) = 0 := by
  unfold coarseRestrict
  rw [Finset.sum_congr rfl
    (fun x (_ : x ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
        AdmissibleSubspace.witnessEll) => curlWitnessConfig_eq_zero_of_dir_ne (x := x) (by decide))]
  simp

/-- **Coarse-curl term 3** (`B(coarseShift_1(y),0)`) — direction mismatch, always `0`. -/
theorem coarseRestrict_witness_term3 :
    coarseRestrict AdmissibleSubspace.witnessEll curlWitnessConfig
        (⟨coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 1,
            coarseShift_mem_coarseLattice witnessHdvd AdmissibleSubspace.witnessY_coarse 1⟩, 0)
      = 0 := by
  unfold coarseRestrict
  rw [Finset.sum_congr rfl
    (fun x (_ : x ∈ AdmissibleSubspace.blockOf
        (coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 1)
        AdmissibleSubspace.witnessEll) =>
      curlWitnessConfig_eq_zero_of_dir_ne (x := x) (by decide))]
  simp

/-- **Coarse-curl term 2** (`B(coarseShift_0(y),1)`) — direction MATCHES, but `curlWitnessSite`
(coordinate `0` equal to `1`) genuinely lies OUTSIDE `blockOf (coarseShift witnessY witnessEll 0)
witnessEll` (coordinate `0` in `[2,4)`), so every term of the block-average is `0`. Mirrors
`LatticeOperators.witness_coarseRestrict_outside_eq_zero`'s exact proof shape. -/
theorem coarseRestrict_witness_term2 :
    coarseRestrict AdmissibleSubspace.witnessEll curlWitnessConfig
        (⟨coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 0,
            coarseShift_mem_coarseLattice witnessHdvd AdmissibleSubspace.witnessY_coarse 0⟩,
          (1 : Fin 3))
      = 0 := by
  unfold coarseRestrict
  have hz : ∀ x ∈ AdmissibleSubspace.blockOf
      (coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 0)
      AdmissibleSubspace.witnessEll, curlWitnessConfig (x, (1 : Fin 3)) = 0 := by
    intro x hx
    unfold curlWitnessConfig curlWitnessBond
    rw [if_neg]
    intro heq
    have hxeq : x = curlWitnessSite := (Prod.ext_iff.mp heq).1
    rw [hxeq] at hx
    revert hx
    decide
  rw [Finset.sum_congr rfl hz]
  simp

/-- **Coarse-curl term 4** (`B(y,1)`, `y = witnessY`) — direction matches AND `curlWitnessSite ∈
blockOf witnessY witnessEll`, giving raw block-sum `1`, normalized `1/16`. Mirrors
`LatticeOperators.witness_block_sum_eq_one`'s exact proof shape. -/
theorem coarseRestrict_witness_term4 :
    coarseRestrict AdmissibleSubspace.witnessEll curlWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, (1 : Fin 3))
      = 1 / 16 := by
  unfold coarseRestrict
  have hmem : curlWitnessSite ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll := by decide
  have hsum : (∑ x ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll, curlWitnessConfig (x, (1 : Fin 3))) = 1 := by
    rw [Finset.sum_eq_single curlWitnessSite]
    · unfold curlWitnessConfig curlWitnessBond
      rw [if_pos rfl]
    · intro x _ hne
      unfold curlWitnessConfig curlWitnessBond
      rw [if_neg]
      intro h
      exact hne (Prod.ext_iff.mp h).1
    · intro h
      exact absurd hmem h
  rw [hsum]
  unfold AdmissibleSubspace.witnessEll
  norm_num

#print axioms curlWitnessSite_coord0
#print axioms curlWitnessConfig_eq_zero_of_dir_ne
#print axioms coarseRestrict_witness_term1
#print axioms coarseRestrict_witness_term2
#print axioms coarseRestrict_witness_term3
#print axioms coarseRestrict_witness_term4

/-- **`coarseCurl(coarseRestrict A)` at the witness plaquette equals `-1/16`.** -/
theorem coarseCurl_of_coarseRestrict_witness_value :
    coarseCurlValue witnessHdvd (coarseRestrict AdmissibleSubspace.witnessEll curlWitnessConfig)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, coarseWitnessDirs)
      = -1 / 16 := by
  simp only [coarseCurlValue, coarseWitnessDirs]
  change coarseRestrict AdmissibleSubspace.witnessEll curlWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, (0 : Fin 3))
      + coarseRestrict AdmissibleSubspace.witnessEll curlWitnessConfig
        (⟨coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 0,
            coarseShift_mem_coarseLattice witnessHdvd AdmissibleSubspace.witnessY_coarse 0⟩,
          (1 : Fin 3))
      - coarseRestrict AdmissibleSubspace.witnessEll curlWitnessConfig
        (⟨coarseShift AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll 1,
            coarseShift_mem_coarseLattice witnessHdvd AdmissibleSubspace.witnessY_coarse 1⟩,
          (0 : Fin 3))
      - coarseRestrict AdmissibleSubspace.witnessEll curlWitnessConfig
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, (1 : Fin 3))
      = -1 / 16
  rw [coarseRestrict_witness_term1, coarseRestrict_witness_term2, coarseRestrict_witness_term3,
      coarseRestrict_witness_term4]
  ring

#print axioms coarseCurl_of_coarseRestrict_witness_value

/-- **`curlValue curlWitnessConfig` at `(witnessY, coarseWitnessDirs)` is `1`** — the `x = witnessY`
term of the discrete-Stokes block sum below. -/
theorem curlValue_witness_at_witnessY :
    curlValue curlWitnessConfig (AdmissibleSubspace.witnessY, coarseWitnessDirs) = 1 := by
  simp only [curlValue, coarseWitnessDirs]
  show curlWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3))
      + curlWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3))
      - curlWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3))
      - curlWitnessConfig (AdmissibleSubspace.witnessY, (1 : Fin 3)) = 1
  rw [curlWitnessConfig_eq_zero_of_dir_ne (x := AdmissibleSubspace.witnessY) (by decide),
      curlWitnessConfig_eq_zero_of_dir_ne
        (x := periodicLatticeShift AdmissibleSubspace.witnessY 1) (by decide)]
  have h2 : curlWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3))
      = 1 := by
    unfold curlWitnessConfig curlWitnessBond curlWitnessSite
    rw [if_pos rfl]
  have h4 : curlWitnessConfig (AdmissibleSubspace.witnessY, (1 : Fin 3)) = 0 := by
    unfold curlWitnessConfig curlWitnessBond
    rw [if_neg]
    intro h
    have : AdmissibleSubspace.witnessY = curlWitnessSite := (Prod.ext_iff.mp h).1
    have h0 : (AdmissibleSubspace.witnessY 0 : Fin 4) = curlWitnessSite 0 := congrFun this 0
    rw [curlWitnessSite_coord0] at h0
    simp [AdmissibleSubspace.witnessY] at h0
  rw [h2, h4]
  ring

/-- **`curlValue curlWitnessConfig` at `(curlWitnessSite, coarseWitnessDirs)` is `-1`** — the
`x = curlWitnessSite` term of the discrete-Stokes block sum below. -/
theorem curlValue_witness_at_curlWitnessSite :
    curlValue curlWitnessConfig (curlWitnessSite, coarseWitnessDirs) = -1 := by
  simp only [curlValue, coarseWitnessDirs]
  show curlWitnessConfig (curlWitnessSite, (0 : Fin 3))
      + curlWitnessConfig (periodicLatticeShift curlWitnessSite 0, (1 : Fin 3))
      - curlWitnessConfig (periodicLatticeShift curlWitnessSite 1, (0 : Fin 3))
      - curlWitnessConfig (curlWitnessSite, (1 : Fin 3)) = -1
  rw [curlWitnessConfig_eq_zero_of_dir_ne (x := curlWitnessSite) (by decide),
      curlWitnessConfig_eq_zero_of_dir_ne
        (x := periodicLatticeShift curlWitnessSite 1) (by decide)]
  have h2 : curlWitnessConfig (periodicLatticeShift curlWitnessSite 0, (1 : Fin 3)) = 0 := by
    unfold curlWitnessConfig curlWitnessBond
    rw [if_neg]
    intro h
    have hs : periodicLatticeShift curlWitnessSite 0 = curlWitnessSite := (Prod.ext_iff.mp h).1
    have hs0 : (periodicLatticeShift curlWitnessSite 0) 0 = curlWitnessSite 0 := congrFun hs 0
    rw [periodicLatticeShift_self, curlWitnessSite_coord0] at hs0
    exact absurd hs0 (by decide)
  have h4 : curlWitnessConfig (curlWitnessSite, (1 : Fin 3)) = 1 := by
    unfold curlWitnessConfig curlWitnessBond
    rw [if_pos rfl]
  rw [h2, h4]
  ring

#print axioms curlValue_witness_at_witnessY
#print axioms curlValue_witness_at_curlWitnessSite

/-- **Everywhere else in the block, `curlValue` vanishes** — the general zero-lemma underlying the
discrete-Stokes cancellation: away from `witnessY` and `curlWitnessSite`, neither the "inflow" term
(via `periodicLatticeShift_injective`) nor the "direct" term can hit the indicator. -/
theorem curlValue_witness_zero_elsewhere {x : PeriodicLatticeSite AdmissibleSubspace.witnessL}
    (h1 : x ≠ AdmissibleSubspace.witnessY) (h2 : x ≠ curlWitnessSite) :
    curlValue curlWitnessConfig (x, coarseWitnessDirs) = 0 := by
  simp only [curlValue, coarseWitnessDirs]
  show curlWitnessConfig (x, (0 : Fin 3))
      + curlWitnessConfig (periodicLatticeShift x 0, (1 : Fin 3))
      - curlWitnessConfig (periodicLatticeShift x 1, (0 : Fin 3))
      - curlWitnessConfig (x, (1 : Fin 3)) = 0
  rw [curlWitnessConfig_eq_zero_of_dir_ne (x := x) (by decide),
      curlWitnessConfig_eq_zero_of_dir_ne (x := periodicLatticeShift x 1) (by decide)]
  have e2 : curlWitnessConfig (periodicLatticeShift x 0, (1 : Fin 3)) = 0 := by
    unfold curlWitnessConfig curlWitnessBond
    rw [if_neg]
    intro h
    have hs : periodicLatticeShift x 0 = curlWitnessSite := (Prod.ext_iff.mp h).1
    have hs' : periodicLatticeShift x 0 =
        periodicLatticeShift AdmissibleSubspace.witnessY 0 := hs
    exact h1 (periodicLatticeShift_injective 0 hs')
  have e4 : curlWitnessConfig (x, (1 : Fin 3)) = 0 := by
    unfold curlWitnessConfig curlWitnessBond
    rw [if_neg]
    intro h
    exact h2 (Prod.ext_iff.mp h).1
  rw [e2, e4]
  ring

#print axioms curlValue_witness_zero_elsewhere

/-- **THE DISCRETE-STOKES CANCELLATION**: summed over the whole block, `curlValue` is `0` —
`witnessY`'s `+1` and `curlWitnessSite`'s `-1` cancel exactly, and every other block element
contributes nothing. -/
theorem curlValue_witness_sum_eq_zero :
    (∑ x ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll,
      curlValue curlWitnessConfig (x, coarseWitnessDirs)) = 0 := by
  have hmemY : AdmissibleSubspace.witnessY ∈ AdmissibleSubspace.blockOf
      AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll := by decide
  have hmemC : curlWitnessSite ∈ (AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll).erase AdmissibleSubspace.witnessY := by
    rw [Finset.mem_erase]
    refine ⟨by decide, by decide⟩
  rw [← Finset.add_sum_erase _ _ hmemY, ← Finset.add_sum_erase _ _ hmemC]
  have hrest : (∑ x ∈ (((AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll).erase AdmissibleSubspace.witnessY).erase curlWitnessSite),
      curlValue curlWitnessConfig (x, coarseWitnessDirs)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    exact curlValue_witness_zero_elsewhere hx.2.1 hx.1
  rw [hrest, curlValue_witness_at_witnessY, curlValue_witness_at_curlWitnessSite]
  ring

#print axioms curlValue_witness_sum_eq_zero

/-- **`coarsePlaquetteRestrict(curlValue)` at the witness plaquette equals `0`.** -/
theorem coarsePlaquetteRestrict_of_curlValue_witness_value :
    coarsePlaquetteRestrict AdmissibleSubspace.witnessEll (curlValue curlWitnessConfig)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, coarseWitnessDirs)
      = 0 := by
  unfold coarsePlaquetteRestrict
  rw [curlValue_witness_sum_eq_zero]
  ring

#print axioms coarsePlaquetteRestrict_of_curlValue_witness_value

/-- **THE VERDICT — item 3, settled by REFUTATION**: `coarseCurl(coarseRestrict A)` and
`coarsePlaquetteRestrict(curlValue A)` are PROVABLY DIFFERENT rationals at the same witness
plaquette, for the same witness bond configuration `A = curlWitnessConfig` — `-1/16 ≠ 0`,
kernel-checked. Block-averaging does NOT commute with taking the curl, in this precise, checkable
sense: the naive composite `coarseRestrictCLM`-then-`coarseCurlCLM` is a strictly different operator
from `curlCLM`-then-`coarsePlaquetteRestrictCLM`. -/
theorem coarseCurl_coarseRestrict_ne_coarsePlaquetteRestrict_curl_witness :
    coarseCurlValue witnessHdvd (coarseRestrict AdmissibleSubspace.witnessEll curlWitnessConfig)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, coarseWitnessDirs) ≠
    coarsePlaquetteRestrict AdmissibleSubspace.witnessEll (curlValue curlWitnessConfig)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, coarseWitnessDirs) := by
  rw [coarseCurl_of_coarseRestrict_witness_value,
      coarsePlaquetteRestrict_of_curlValue_witness_value]
  norm_num

#print axioms coarseCurl_coarseRestrict_ne_coarsePlaquetteRestrict_curl_witness

end AdalyFormal.Balaban.CoarseCurl
