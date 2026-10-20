/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib

/-!
# A corrective statement skeleton for the Clay Yang--Mills target

This standalone module records requirement structures, not a construction or proof of quantum
Yang--Mills theory. It contains no caller-selected `Prop` placeholders. Every structure field is
real mathematical data or evidence about that data. Requirements that cannot yet be stated
faithfully are tracked here and in `TARGET_BURNDOWN.md`, never as per-instance propositions.
The file is intentionally outside the root import chain.

Pinned source: Arthur Jaffe and Edward Witten, *Quantum Yang--Mills Theory*, official Clay
Mathematics Institute problem description, as pinned in `TargetTrack_SOURCES/PIN.md`.

## Burn-down ledger

Each entry is deferred rather than silently weakened. A brick with any entry below is
`PARTIALLY-SETTLED`.

* **B1-CONTINUITY** (settled as a requirement shape): for each common-domain vector, the field map
  is continuous from Mathlib's seminorm topology on `SchwartzMap`. Source: no brick-specific
  verbatim source pinned yet; known-model adequacy remains open.
* **B1-UNBOUNDED-COMMON-DOMAIN** (settled as a requirement shape): every field is a closable
  `LinearPMap` on one dense domain, and both the field and represented group preserve that domain.
  Source: no brick-specific verbatim source pinned yet; known-model adequacy remains open.
* **B1-COVARIANCE-LINK** (settled as a requirement shape): the field and B2a representation are
  indexed by the same instance and obey covariance for the constructed pullback action on Schwartz
  functions. Source: no brick-specific verbatim source pinned yet; known-model adequacy remains
  open.
* **B2A-PHYSICAL-POINCARE-GROUP** (partially settled): the full linear O(1,3) isometry group and
  semidirect product are constructed. F3 adds a faithful physical representation and compatibility
  square, so changing only the equivalence no longer preserves the structure. Source context:
  Jaffe--Witten, extracted lines 227--232; conviction source:
  `Target/prosecution/F2_FAITHFULNESS_PROSECUTION.md`.
* **B2A-PROPER-ORTHOCHRONOUS-COMPONENT** (open, sharpened): full O(1,3) must be replaced by the
  proper orthochronous component with orientation and time-orientation conditions.
* **B2A-TOPOLOGICAL-COMPATIBILITY** (open, sharpened): construct the physical semidirect topology
  and replace the algebraic equivalence by a continuous multiplicative equivalence.
* **B2B-JOINT-PVM** (open, sharpened): four commuting bounded self-adjoint translation-generator
  surrogates and their exact coordinate-spectrum marginals are now required. Mathlib contains no
  `ProjectionValuedMeasure`, `SpectralMeasure`, or `resolutionOfIdentity` declaration in this
  pinned build, so a genuine joint PVM remains deferred. Source quote (Jaffe--Witten, extracted
  lines 272--276): “The positive energy axiom asserts that in any quantum field theory, the
  spectrum of H is supported in the region [0, ∞).”
* **B2B-PVM-SUPPORT-LINK** (open, sharpened): `energyGenerator_spectrum_nonnegative` proves that
  the exact energy marginal and fixed-cone support compose to real nonnegative energy spectrum.
  Equality with the support of a nonexistent joint-PVM object remains deferred.
* **B3-UNBOUNDED-HAMILTONIAN** (future L3 mass-gap batch): replace the bounded surrogate by the
  physical unbounded Hamiltonian. Source quote: Jaffe--Witten, extracted lines 272--276, reproduced
  in the B3 docstring below.
* **B3-FINITE-SUPREMAL-MASS** (future L3 mass-gap batch): formalize the supremum of admissible gaps
  and prove it finite. Source quote: Jaffe--Witten, extracted lines 272--276, reproduced below.
* **B4-PHYSICAL-EUCLIDEAN-GROUP**, **B4-OS-PRIMARY-RP**, **B4-CLUSTERING**, and
  **B4-CORRECTED-GROWTH** are repaired in F5R to `PARTIALLY-SETTLED` requirement shapes: hostile
  Euclidean/group/translation probes are present; RP and clustering use typed positive-time tests
  and exact cross-order Schwinger values; and the moment family consists of Mathlib tempered
  distributions. Concrete tensor-test construction, known-model adequacy, primary-PDF pinning,
  and external confirmation remain open. F5's separate B5 work is unchanged.
* **B5-WILSON-CONSTRUCTION** (F5 requirement shape): canonical periodic-cubic sites, links,
  plaquettes, Wilson action, Haar-product probability measure, M2 weak-limit carrier, and exact
  expectation links are typed. Constructing an inhabitant, renormalization, and the 3D-campaign to
  4D-Clay scope bridge remain open.
* **B5-CURVATURE-CONSTRUCTION** (F5 requirement shape): Wilson-loop polynomials on the same links
  supply nonzero input candidates for later string-tension and glueball constructions. Constructing
  geometric areas/channel projections and then constructing the benchmark observables,
  relating nonlocal loops to local curvature polynomials, and extracting benchmark quantities remain
  open.
* **B5-CONJUNCTION-ADEQUACY** (F5 requirement shape): F4R's three gates remain, while the lattice
  data and cutoff/continuum realizations now live inside the same `YangMillsContent`; both B5 bricks
  project from them. No satisfiability or known-model adequacy is claimed.
* **G-LIE-SIMPLICITY** (future gauge-group batch): replace the present compact topological-group
  interface by finite-dimensional compact Lie-group data and the intended Lie-theoretic simplicity.
  Source quote: Jaffe--Witten, extracted lines 277--280, reproduced in the target docstring below.
* **CROSS-BRICK-COHERENCE** (future L2/L3 reconstruction batch): identify the Minkowski and
  Euclidean objects via OS reconstruction and tie B1--B5 to one reconstructed theory. Source: the
  pinned theorem requires axiomatic properties at least as strong as [45, 35], but no
  brick-specific verbatim source for this identification is pinned yet.
* **ADEQUACY-SANITY-INSTANCES** (future per-brick acceptance batches): prove the free-field Wightman
  instance and lattice-RP bridge while preserving the proved trivial-theory rejection. Source: no
  brick-specific verbatim source pinned yet.
-/

namespace AdalyFormal.Target.ClayStatement

open scoped ComplexConjugate

universe g u v w x

/-- Four-dimensional real spacetime used as the input of the Schwartz test functions.

This is Minkowski spacetime only at the level of its underlying real vector space; no metric is
encoded by this definition.

DECISION-STATUS: `PARAMETRIZED`.
-/
abbrev Spacetime4 := Fin 4 → ℝ

/-- Three spatial coordinate indices; together with the energy coordinate this composes the four
coordinates pinned by the source's `R4`. -/
abbrev SpatialIndex := Fin 3

/-- The fixed positive-energy cone used by B2b; unlike the v1 skeleton it is not caller-selected.
The coordinate `p 0` is energy and the remaining three coordinates are spatial momentum.

DECISION-STATUS: `PARTIALLY-SETTLED` (the physical translation/PVM identification is deferred).
-/
def ForwardLightCone : Set Spacetime4 :=
  {p | 0 ≤ p 0 ∧ (∑ i : SpatialIndex, (p i.succ) ^ 2) ≤ (p 0) ^ 2}

/-- The Minkowski quadratic form with signature `(+,-,-,-)`. Coordinate zero is the positive
energy coordinate, consistently with `ForwardLightCone`.

Pinned source context: Jaffe--Witten, extracted lines 227--232, specifies `R4` with Minkowski
signature and the Poincaré/translation generators. The sign convention is an owned formalization
choice, not quoted from those lines.

DECISION-STATUS: `PARTIALLY-SETTLED` (the full linear isometry group is built; connectedness,
orientation, and time-orientation restrictions are not imposed).
-/
def MinkowskiQuadraticForm : QuadraticForm ℝ Spacetime4 :=
  QuadraticMap.weightedSumSquares ℝ (fun i : Fin 4 => if i = 0 then 1 else -1)

/-- Evaluation of the chosen Minkowski form as energy squared minus spatial momentum squared. -/
theorem minkowskiQuadraticForm_apply (p : Spacetime4) :
    MinkowskiQuadraticForm p = (p 0) ^ 2 - ∑ i : SpatialIndex, (p i.succ) ^ 2 := by
  simp [MinkowskiQuadraticForm, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ]
  ring

/-- The full linear isometry group O(1,3) of `MinkowskiQuadraticForm`, realized directly as a
subgroup of real linear automorphisms. This is deliberately the full indefinite orthogonal group,
not the proper orthochronous Lorentz subgroup.

Pinned source context: Jaffe--Witten, extracted lines 227--232. The source names the Poincaré
(inhomogeneous Lorentz) group; the full-O(1,3) scope is an owned, explicitly partial decision.

DECISION-STATUS: `PARTIALLY-SETTLED`.
-/
def MinkowskiIsometryGroup : Subgroup (Spacetime4 ≃ₗ[ℝ] Spacetime4) where
  carrier := {L | ∀ p, MinkowskiQuadraticForm (L p) = MinkowskiQuadraticForm p}
  one_mem' := by simp
  mul_mem' := by
    intro L K hL hK p
    simp only [LinearEquiv.mul_apply]
    rw [hL, hK]
  inv_mem' := by
    intro L hL p
    change MinkowskiQuadraticForm (L.symm p) = MinkowskiQuadraticForm p
    have h := hL (L.symm p)
    rw [L.apply_symm_apply] at h
    exact h.symm

/-- Minkowski isometries act distributively on the additive translation group, expressed through
`Multiplicative Spacetime4` so the action is a `MulDistribMulAction`. -/
instance minkowskiIsometryMulDistribMulAction :
    MulDistribMulAction MinkowskiIsometryGroup (Multiplicative Spacetime4) where
  smul L p := Multiplicative.ofAdd (L.1 p.toAdd)
  one_smul p := rfl
  mul_smul L K p := rfl
  smul_one L := by
    change Multiplicative.ofAdd (L.1 0) = Multiplicative.ofAdd 0
    rw [map_zero]
  smul_mul L p q := by
    change Multiplicative.ofAdd (L.1 (p.toAdd + q.toAdd)) = _
    rw [map_add]
    rfl

/-- The homomorphism to translation-group automorphisms induced by the distributive action. -/
def minkowskiIsometryAction :
    MinkowskiIsometryGroup →* MulAut (Multiplicative Spacetime4) :=
  MulDistribMulAction.toMulAut MinkowskiIsometryGroup (Multiplicative Spacetime4)

/-- Four-dimensional Poincaré group: translations `(Spacetime4,+)` semidirect the full linear
Minkowski isometry group O(1,3). `Multiplicative` is only Mathlib's encoding of the additive
translation group required by `SemidirectProduct`.

DECISION-STATUS: `PARTIALLY-SETTLED` (full O(1,3), not yet the proper orthochronous component).
-/
abbrev PoincareGroup4 :=
  SemidirectProduct (Multiplicative Spacetime4) MinkowskiIsometryGroup
    minkowskiIsometryAction

/-- The physical Poincaré group is nontrivial already through its translation subgroup. -/
theorem poincareGroup4_nontrivial : Nontrivial PoincareGroup4 := by
  let p : Spacetime4 := fun i => if i = 0 then 1 else 0
  let a : PoincareGroup4 := SemidirectProduct.inl (Multiplicative.ofAdd p)
  let b : PoincareGroup4 := 1
  refine ⟨⟨a, b, ?_⟩⟩
  intro h
  have hleft := congrArg SemidirectProduct.left h
  change Multiplicative.ofAdd p = 1 at hleft
  have hp : p 0 = 0 := congrArg (fun q : Multiplicative Spacetime4 => q.toAdd 0) hleft
  norm_num [p] at hp

/-- The positive-definite Euclidean quadratic form on four-space. Unlike the Minkowski form,
all four coordinate weights are positive.

Source status: OS-I p. 84 and OS-II p. 283 use Euclidean four-space; the all-positive sign
convention is an owned formalization choice. `Matrix.orthogonalGroup (Fin 4) ℝ` exists in the
pinned Mathlib, but is a matrix submonoid. The direct linear-equivalence presentation below is
used because it supplies the action needed by `SemidirectProduct` without an unproved matrix-to-
linear-equivalence bridge.
-/
def EuclideanQuadraticForm : QuadraticForm ℝ Spacetime4 :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin 4 => 1)

/-- Evaluation of the Euclidean form as the sum of four coordinate squares. -/
theorem euclideanQuadraticForm_apply (p : Spacetime4) :
    EuclideanQuadraticForm p = ∑ i : Fin 4, (p i) ^ 2 := by
  simp [EuclideanQuadraticForm, QuadraticMap.weightedSumSquares_apply, pow_two]

/-- The full linear Euclidean isometry group O(4), as form-preserving real linear
automorphisms. -/
def EuclideanIsometryGroup : Subgroup (Spacetime4 ≃ₗ[ℝ] Spacetime4) where
  carrier := {L | ∀ p, EuclideanQuadraticForm (L p) = EuclideanQuadraticForm p}
  one_mem' := by simp
  mul_mem' := by
    intro L K hL hK p
    simp only [LinearEquiv.mul_apply]
    rw [hL, hK]
  inv_mem' := by
    intro L hL p
    change EuclideanQuadraticForm (L.symm p) = EuclideanQuadraticForm p
    have h := hL (L.symm p)
    rw [L.apply_symm_apply] at h
    exact h.symm

/-- Euclidean isometries act distributively on additive translations. -/
instance euclideanIsometryMulDistribMulAction :
    MulDistribMulAction EuclideanIsometryGroup (Multiplicative Spacetime4) where
  smul L p := Multiplicative.ofAdd (L.1 p.toAdd)
  one_smul p := rfl
  mul_smul L K p := rfl
  smul_one L := by
    change Multiplicative.ofAdd (L.1 0) = Multiplicative.ofAdd 0
    rw [map_zero]
  smul_mul L p q := by
    change Multiplicative.ofAdd (L.1 (p.toAdd + q.toAdd)) = _
    rw [map_add]
    rfl

/-- The homomorphism used in the Euclidean semidirect product. -/
def euclideanIsometryAction :
    EuclideanIsometryGroup →* MulAut (Multiplicative Spacetime4) :=
  MulDistribMulAction.toMulAut EuclideanIsometryGroup (Multiplicative Spacetime4)

/-- The physical Euclidean group E(4) = ℝ⁴ ⋊ O(4). -/
abbrev EuclideanGroup4 :=
  SemidirectProduct (Multiplicative Spacetime4) EuclideanIsometryGroup
    euclideanIsometryAction

/-- Embed a translation into E(4). -/
def euclideanTranslation (a : Spacetime4) : EuclideanGroup4 :=
  SemidirectProduct.inl (Multiplicative.ofAdd a)

/-- The affine action of E(4) on Euclidean four-space. -/
def euclideanGroupAct (g : EuclideanGroup4) (x : Spacetime4) : Spacetime4 :=
  g.left.toAdd + g.right.1 x

/-- Three-dimensional spatial vectors used by the OS clustering translation. -/
abbrev SpatialVector3 := Fin 3 → ℝ

/-- Embed a spatial vector with zero Euclidean-time coordinate. -/
def spatialEmbed (a : SpatialVector3) : Spacetime4 :=
  Fin.cases 0 a

/-- Translation by `t a` in a purely spatial direction, as required by OS-I E4. -/
def euclideanSpatialTranslation (t : ℝ) (a : SpatialVector3) : EuclideanGroup4 :=
  euclideanTranslation (t • spatialEmbed a)

/-- The linear map that reverses Euclidean time and fixes all three spatial coordinates. -/
def euclideanTimeReflectionLinearMap : Spacetime4 →ₗ[ℝ] Spacetime4 where
  toFun p i := if i = 0 then -p i else p i
  map_add' p q := by
    funext i
    by_cases h : i = 0 <;> simp [h] <;> ring
  map_smul' c p := by
    funext i
    by_cases h : i = 0 <;> simp [h] <;> ring

/-- Euclidean time reflection is involutive. -/
theorem euclideanTimeReflection_involutive :
    Function.Involutive euclideanTimeReflectionLinearMap := by
  intro p
  funext i
  by_cases hi : i = 0 <;> simp [euclideanTimeReflectionLinearMap, hi]

/-- Euclidean time reflection as a real linear equivalence. -/
def EuclideanTimeReflectionLinearEquiv : Spacetime4 ≃ₗ[ℝ] Spacetime4 :=
  LinearEquiv.ofInvolutive euclideanTimeReflectionLinearMap
    euclideanTimeReflection_involutive

/-- The fixed time reflection belongs to O(4). -/
def EuclideanTimeReflectionIsometry : EuclideanIsometryGroup := by
  refine ⟨EuclideanTimeReflectionLinearEquiv, ?_⟩
  intro p
  rw [euclideanQuadraticForm_apply, euclideanQuadraticForm_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i = 0 <;>
    simp [EuclideanTimeReflectionLinearEquiv, euclideanTimeReflectionLinearMap, h, pow_two]

/-- The fixed physical Euclidean time-reflection element `(0, diag(-1,1,1,1))` of E(4). -/
def EuclideanTimeReflection : EuclideanGroup4 :=
  SemidirectProduct.inr EuclideanTimeReflectionIsometry

/-- The fixed Euclidean time reflection is not the identity element of E(4). -/
theorem euclideanTimeReflection_ne_one : EuclideanTimeReflection ≠ 1 := by
  intro h
  have hr := congrArg SemidirectProduct.right h
  change EuclideanTimeReflectionIsometry = 1 at hr
  let p : Spacetime4 := fun i => if i = 0 then 1 else 0
  have hp := congrArg (fun L : EuclideanIsometryGroup => L.1 p) hr
  have hp0 := congrArg (fun q : Spacetime4 => q 0) hp
  norm_num [EuclideanTimeReflectionIsometry, EuclideanTimeReflectionLinearEquiv,
    euclideanTimeReflectionLinearMap, p] at hp0

/-- E(4) is nontrivial through translations. -/
theorem euclideanGroup4_nontrivial : Nontrivial EuclideanGroup4 := by
  let p : Spacetime4 := fun i => if i = 0 then 1 else 0
  let a : EuclideanGroup4 := euclideanTranslation p
  let b : EuclideanGroup4 := 1
  refine ⟨⟨a, b, ?_⟩⟩
  intro h
  have hleft := congrArg SemidirectProduct.left h
  change Multiplicative.ofAdd p = 1 at hleft
  have hp : p 0 = 0 := congrArg (fun q : Multiplicative Spacetime4 => q.toAdd 0) hleft
  norm_num [p] at hp

/-- The complex coordinate marginal of a set of four-momenta. -/
def CoordinateSpectrum (S : Set Spacetime4) (μ : Fin 4) : Set ℂ :=
  (fun p => (p μ : ℂ)) '' S

/-- Standard unit vector along the `μ`-th spacetime coordinate (R3: used to state the Stone's
-theorem tie between `SpectrumCondition.translationGenerators` and the represented translation
subgroup, below). -/
def spacetimeUnitVector (μ : Fin 4) : Spacetime4 := fun i => if i = μ then 1 else 0

/-- The affine action of the constructed Poincaré group on Minkowski spacetime.

**Moved before `PoincareRepresentation` for the F2 repair** (`Target/prosecution/
F2_DEGENERATE_WITNESSES.lean`): the anti-degeneracy anchor
`PoincareRepresentation.physicalGroupEquiv_spacetime_compatible` refers to this exact action, and
it must be available -- and independent of any Hilbert-space representation -- before that
structure is declared. -/
def poincareGroupAct (g : PoincareGroup4) (x : Spacetime4) : Spacetime4 :=
  g.left.toAdd + g.right.1 x

/-- `poincareGroupAct` is a genuine left `MulAction` of the physical Poincaré group on Minkowski
spacetime, purely geometric data carrying no dependence on any Hilbert space or representation. -/
instance poincareGroupActMulAction : MulAction PoincareGroup4 Spacetime4 where
  smul := poincareGroupAct
  one_smul x := by
    change poincareGroupAct 1 x = x
    simp [poincareGroupAct, SemidirectProduct.one_left, SemidirectProduct.one_right]
  mul_smul g h x := by
    change poincareGroupAct (g * h) x = poincareGroupAct g (poincareGroupAct h x)
    simp only [poincareGroupAct, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      Subgroup.coe_mul, LinearEquiv.mul_apply, toAdd_mul, map_add]
    have haction :
        Multiplicative.toAdd (minkowskiIsometryAction g.right h.left) =
          g.right.1 (Multiplicative.toAdd h.left) := rfl
    rw [haction]
    abel

/-- **The faithfulness of the physical action (F2 repair anchor).** `poincareGroupAct` is
injective: distinct elements of `PoincareGroup4` implement distinct spacetime symmetries.

**R2 CORRECTION (S75 -- supersedes the struck claim below).** ~~Combined with a fixed
`[MulAction P Spacetime4]` instance on the abstract carrier `P` -- ambient data that cannot be
silently swapped by a construction that only varies a `PoincareRepresentation`'s fields, exactly as
`[Group P]`/`[TopologicalSpace P]` cannot -- this is what makes
`physicalGroupEquiv_spacetime_compatible` below a genuine pin rather than another freely-solvable
compatibility square.~~ **This is false when `P` itself is existentially quantified** (Kimi K3
third gate, `compute/KIMI_GATE_CLAYSTATEMENT.md` §1.1-1.2: `mulActionOfEquiv e` manufactures a
matching instance for ANY `e`, so an instance chosen in the SAME breath as `P` pins nothing).
`poincareGroupAct_injective` only becomes a genuine pin at a use site where `P`'s
`[MulAction P Spacetime4]` instance is resolved by ordinary Lean typeclass search against a FIXED
type, not supplied as witness data alongside `P`. `ClayYangMillsPartialSkeletonFor`,
`WightmanRequirementShapes_exist`, and `YangMillsBrickBundle` now fix `P := PoincareGroup4`
with the canonical `poincareGroupActMulAction` instance for exactly this reason (see the R2 repair
note above `PoincareRepresentation` below and `../CLAY_STATEMENT_REPAIR_R2.md`, i.e.
`formal/AdalyFormal/CLAY_STATEMENT_REPAIR_R2.md`, matching where R1's `CLAY_STATEMENT_REPAIR.md`
sits); the general,
abstract-`P` form of `PoincareRepresentation` below remains available for other future consumers,
where the same caution applies. -/
theorem poincareGroupAct_injective : Function.Injective poincareGroupAct := by
  intro g h hgh
  have h0 : g.left.toAdd = h.left.toAdd := by
    have hx0 := congrFun hgh (0 : Spacetime4)
    simpa [poincareGroupAct] using hx0
  have hlin : ∀ x, g.right.1 x = h.right.1 x := by
    intro x
    have hx := congrFun hgh x
    simp only [poincareGroupAct] at hx
    have hcancel : g.left.toAdd + g.right.1 x = h.left.toAdd + h.right.1 x := hx
    rw [h0] at hcancel
    exact add_left_cancel hcancel
  have hleft : g.left = h.left := by
    have hofadd := congrArg Multiplicative.ofAdd h0
    simpa using hofadd
  have hright : g.right = h.right := Subtype.ext (LinearEquiv.ext hlin)
  exact SemidirectProduct.ext hleft hright

/-- **B2a: strongly continuous unitary representation requirement shape.**

There is no brick-specific sentence in the currently pinned Jaffe--Witten excerpt that can
honestly be quoted as a verbatim definition of the Poincaré representation. Streater--Wightman
is the intended future primary source; Osterwalder--Schrader I+II and Glimm--Jaffe are forward
pointers only, and their text was not fetched or pinned in batch 1.

`P` is linked by an actual group equivalence to `PoincareGroup4`; it is not a freely unrelated
abstract group. The representation is a homomorphism into complex linear isometric equivalences,
is strongly continuous on every vector, and acts nontrivially on at least one vector. Thus the old
identity-representation probe remains blocked, while the new physical-identification probe blocks
a trivial abstract carrier independently of comments.

**F2 repair (proved defect, now closed).** Before `physicalGroupEquiv_spacetime_compatible` was
added, `physicalGroupEquiv` floated: `representation_compatibility` alone is algebraically vacuous
in `physicalGroupEquiv`, because for ANY isomorphism `e : P ≃* PoincareGroup4` the square is
solved by recomputing `physicalRepresentation := representation.comp e.symm.toMonoidHom`
(`reidentifyPhysicalGroupRepaired` in `Target/prosecution/F2_DEGENERATE_WITNESSES.lean`, which
compiled for every `e` against the pre-repair structure). The physical content that must pin
`physicalGroupEquiv` cannot live inside the `(representation, physicalGroupEquiv,
physicalRepresentation)` triangle itself, because that triangle is invertible-solvable by
construction; it must come from data external to the Hilbert-space representation.

**R2 CORRECTION (2026-07-21, S75 -- supersedes the struck claim below).** ~~Physically, `P`
denotes the group of spacetime symmetries -- it already acts on spacetime independently of how it
is represented on any particular Hilbert space, exactly the way the Poincaré group in the Wightman
axioms is *the* group of Minkowski isometries, not an abstract group merely isomorphic to it via
unconstrained data. `[MulAction P Spacetime4]` makes that independent action into ambient,
non-floating data (fixed once `P` is fixed, exactly like `[Group P]`/`[TopologicalSpace P]`), and
`physicalGroupEquiv_spacetime_compatible` requires `physicalGroupEquiv` to intertwine it with the
constructed `poincareGroupAct`. Since `poincareGroupAct` is injective
(`poincareGroupAct_injective`), this pins `physicalGroupEquiv` uniquely for a fixed `P`:
`PoincareRepresentation.physicalGroupEquiv_forced` proves any two valid instances on the same `P`
share the same `physicalGroupEquiv`, unconditionally (no side hypotheses on `representation` or
`physicalRepresentation` are needed, unlike the pre-repair partial mitigation
`reidentify_fixedPhysRep_forces_sameEquiv`).~~

**This was false at the level where it was meant to matter.** Two independent statement
prosecutions (`compute/prosecution/PROS_CLAYSTATEMENT_REPAIR.md`, CONVICTED; Kimi K3's
`compute/KIMI_GATE_CLAYSTATEMENT.md`, QUALIFIED-RELOCATED, which built `relocatedReidentifyFromData`
in Lean and ran it) proved `[MulAction P Spacetime4]` is *not* ambient once `P` itself is
existentially quantified in the same witness: `mulActionOfEquiv e` (below) manufactures a matching,
fully valid instance for literally ANY `e : P ≃* PoincareGroup4`, so a prover who supplies `P`,
`[MulAction P Spacetime4]`, and `physicalGroupEquiv` all in one witness (exactly the shape of
`ClayYangMillsPartialSkeletonFor`'s pre-R2 existential) recovers the full pre-repair freedom at the cost of one
`rfl`. `physicalGroupEquiv_forced` below is an honest theorem -- given a FIXED `P` and a FIXED
ambient instance NOT chosen by the same witness, it really does force agreement -- but the F2
repair never fixed `P`, so that hypothesis was never available where the theorem was applied.
**The genuine fix (R2) is at the CONSUMER, not this structure**: the flagship targets
`ClayYangMillsPartialSkeletonFor`, `WightmanRequirementShapes_exist`, and `YangMillsBrickBundle` now fix
`P := PoincareGroup4` with the ALREADY-REGISTERED global instance `poincareGroupActMulAction`
(resolved by ordinary Lean typeclass search, never supplied as existential witness data), so
`physicalGroupEquiv_spacetime_compatible` genuinely has nothing left to choose:
`physicalGroupEquiv_eq_refl_of_canonical` below shows it is forced to `MulEquiv.refl`. This
structure itself is UNCHANGED and remains available in its general, abstract-`P` form for future
non-target consumers, where the same instance-shopping caution documented here still applies until
`P` is fixed at THAT consumer's use site too. **Separately (Kimi's finding (b), not a defect but a
disclosure owed):** the pin's content is exactly as strong as `poincareGroupAct` and no stronger --
`poincareGroupAct_injective`'s proof script is metric-free (verbatim-identical for the Euclidean
group) and never touches `MinkowskiQuadraticForm`; what it pins is the bare-affine-action
identification of `P` with O(1,3) ⋉ ℝ⁴ as it acts on `Fin 4 → ℝ`, not a Minkowski-metric-respecting
identification. The metric content lives in the TYPE `PoincareGroup4` (whose linear parts are by
construction `MinkowskiIsometryGroup`), not in this proof.

DECISION-STATUS: `PARTIALLY-SETTLED`.
-/
structure PoincareRepresentation
    (P : Type v) [Group P] [TopologicalSpace P] [MulAction P Spacetime4]
    (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] where
  /-- The unitary representation as a homomorphism into linear isometric equivalences. -/
  representation : P →* (ℋ ≃ₗᵢ[ℂ] ℋ)
  /-- Concrete algebraic identification of the supplied abstract carrier with the physical group
  built here. Topological compatibility remains a separately tracked debt. -/
  physicalGroupEquiv : P ≃* PoincareGroup4
  /-- **Anti-degeneracy anchor (F2 repair).** `physicalGroupEquiv` must intertwine `P`'s own,
  externally fixed action on physical spacetime with the constructed action `poincareGroupAct` on
  the physical Poincaré group. See the structure docstring for why this -- and not another
  Hilbert-space-representation-theoretic field -- is what genuinely pins the identification. -/
  physicalGroupEquiv_spacetime_compatible :
    ∀ p : P, ∀ x : Spacetime4, p • x = poincareGroupAct (physicalGroupEquiv p) x
  /-- The same represented action, expressed directly on the constructed physical group. -/
  physicalRepresentation : PoincareGroup4 →* (ℋ ≃ₗᵢ[ℂ] ℋ)
  /-- The represented physical-group action is faithful. -/
  physicalRepresentation_injective : Function.Injective physicalRepresentation
  /-- Compatibility square: the abstract representation is the pullback of the physical one
  along `physicalGroupEquiv`. This blocks changing only the equivalence while retaining all
  represented-action data definitionally. -/
  representation_compatibility :
    representation = physicalRepresentation.comp physicalGroupEquiv.toMonoidHom
  /-- Strong continuity of every orbit map. -/
  stronglyContinuous : ∀ ψ : ℋ, Continuous (fun p : P => representation p ψ)
  /-- The representation is not identically the identity on the Hilbert space. -/
  nontriviality : ∃ (p : P) (ψ : ℋ), representation p ψ ≠ ψ

/-- The abstract representation is faithful because it is the pullback of a faithful action along
an equivalence. In particular, translations cannot all act trivially. -/
theorem PoincareRepresentation.representation_injective
    {P : Type v} [Group P] [TopologicalSpace P] [MulAction P Spacetime4]
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (b : PoincareRepresentation P ℋ) : Function.Injective b.representation := by
  intro p q hpq
  apply b.physicalGroupEquiv.injective
  apply b.physicalRepresentation_injective
  have hp := congrArg (fun r => r p) b.representation_compatibility
  have hq := congrArg (fun r => r q) b.representation_compatibility
  exact hp.symm.trans (hpq.trans hq)

/-- **F2's headline theorem, now the load-bearing lemma of the R2 target-level fix.** For a FIXED
carrier `P` and a FIXED `[MulAction P Spacetime4]` instance -- crucially, one NOT re-chosen in the
same witness as `P` and `physicalGroupEquiv` themselves (see the R2 correction above
`PoincareRepresentation`; a `P`/instance pair chosen together defeats this, as
`compute/KIMI_GATE_CLAYSTATEMENT.md` §1.1 demonstrates) -- every valid `PoincareRepresentation P ℋ`
has the SAME `physicalGroupEquiv`, regardless of `representation`, `physicalRepresentation`, or any
other field. Applied at `P := PoincareGroup4` with the globally-registered
`poincareGroupActMulAction` instance (never a witness-supplied `mulActionOfEquiv e`), this is
exactly `physicalGroupEquiv_eq_refl_of_canonical` below, which R2 makes the target-level content:
`ClayYangMillsPartialSkeletonFor`/`WightmanRequirementShapes_exist`/`YangMillsBrickBundle` fix `P` this way,
so a witness for those `Prop`s literally cannot vary `physicalGroupEquiv` away from
`MulEquiv.refl PoincareGroup4`. -/
theorem PoincareRepresentation.physicalGroupEquiv_forced
    {P : Type v} [Group P] [TopologicalSpace P] [MulAction P Spacetime4]
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (b c : PoincareRepresentation P ℋ) : c.physicalGroupEquiv = b.physicalGroupEquiv := by
  apply MulEquiv.ext
  intro p
  apply poincareGroupAct_injective
  funext x
  rw [← c.physicalGroupEquiv_spacetime_compatible p x,
    ← b.physicalGroupEquiv_spacetime_compatible p x]

/-- **Non-over-constraint, part 1 (F2 repair sanity).** The new anchor field never rules out a
candidate `physicalGroupEquiv` in isolation: for ANY isomorphism `e : P ≃* PoincareGroup4`, the
pullback action `p • x := poincareGroupAct (e p) x` is a genuine `MulAction P Spacetime4`
instance. Combined with `physicalGroupEquiv_spacetime_compatible_of_pullback` below, this shows
the field is always satisfiable, so it can never be the reason a `(representation,
physicalGroupEquiv, physicalRepresentation, ...)` tuple that would have satisfied the pre-repair
structure fails to satisfy the post-repair one. -/
@[reducible] def mulActionOfEquiv {P : Type v} [Group P] (e : P ≃* PoincareGroup4) :
    MulAction P Spacetime4 where
  smul p x := poincareGroupAct (e p) x
  one_smul x := by
    change poincareGroupAct (e 1) x = x
    rw [map_one]
    exact poincareGroupActMulAction.one_smul x
  mul_smul p q x := by
    change poincareGroupAct (e (p * q)) x = poincareGroupAct (e p) (poincareGroupAct (e q) x)
    rw [map_mul]
    exact poincareGroupActMulAction.mul_smul (e p) (e q) x

/-- **Non-over-constraint, part 2.** Under `mulActionOfEquiv e`, `e` itself trivially discharges
`physicalGroupEquiv_spacetime_compatible`, by `rfl` -- no representation-theoretic content is
needed to satisfy the new field. -/
theorem physicalGroupEquiv_spacetime_compatible_of_pullback
    {P : Type v} [Group P] (e : P ≃* PoincareGroup4) :
    letI := mulActionOfEquiv e
    ∀ p : P, ∀ x : Spacetime4, p • x = poincareGroupAct (e p) x :=
  fun _ _ => rfl

/-- **Non-over-constraint, part 3 (the tightest case) -- R2: this is now the target-level content.**
When `P` is literally the physical group itself, equipped with its own canonical
`poincareGroupActMulAction` instance resolved by ordinary typeclass search (never supplied as
existential witness data alongside `P`), the repair forces `physicalGroupEquiv` to be exactly the
identity -- confirming the field pins the identification to the one honest choice in the case where
the abstraction does no work, rather than merely narrowing it to some unspecified value. R2 fixes
`P := PoincareGroup4` in `ClayYangMillsPartialSkeletonFor`/`WightmanRequirementShapes_exist`/
`YangMillsBrickBundle` precisely so this theorem, not `physicalGroupEquiv_forced` in isolation,
governs those targets: the relocated exploit `mulActionOfEquiv e` for `e ≠ refl` no longer
typechecks as a `PoincareRepresentation PoincareGroup4 ℋ` at those use sites, because the ambient
instance there is resolved once, globally, not re-chosen per witness (see
`Target/prosecution/R2_INSTANCE_QUANTIFIER_REPAIR.lean` for the machine-checked regression). -/
theorem physicalGroupEquiv_eq_refl_of_canonical
    [TopologicalSpace PoincareGroup4]
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (b : PoincareRepresentation PoincareGroup4 ℋ) :
    b.physicalGroupEquiv = MulEquiv.refl PoincareGroup4 := by
  apply MulEquiv.ext
  intro p
  apply poincareGroupAct_injective
  funext x
  exact (b.physicalGroupEquiv_spacetime_compatible p x).symm

/-- Pullback of scalar Schwartz functions by the inverse affine Poincaré action. Thus the precise
convention used below is `(g • f)(x) = f(g⁻¹ • x)`. Mathlib's continuous linear pullback maps for
translations and finite-dimensional linear equivalences prove that this remains Schwartz. -/
noncomputable def poincareSchwartzPullback (g : PoincareGroup4) :
    SchwartzMap Spacetime4 ℂ →L[ℂ] SchwartzMap Spacetime4 ℂ :=
  let gi := g⁻¹
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ gi.right.1.toContinuousLinearEquiv).comp
    (SchwartzMap.compSubConstCLM ℂ (-gi.left.toAdd))

@[simp]
theorem poincareSchwartzPullback_apply (g : PoincareGroup4)
    (f : SchwartzMap Spacetime4 ℂ) (x : Spacetime4) :
    poincareSchwartzPullback g f x = f (poincareGroupAct g⁻¹ x) := by
  simp [poincareSchwartzPullback, poincareGroupAct]
  congr 1
  abel

/-- The constructed inverse-pullback is a genuine left group action on Schwartz space. -/
noncomputable instance poincareSchwartzMulAction :
    MulAction PoincareGroup4 (SchwartzMap Spacetime4 ℂ) where
  smul g f := poincareSchwartzPullback g f
  one_smul f := by
    change poincareSchwartzPullback 1 f = f
    ext x
    rw [poincareSchwartzPullback_apply]
    simp [poincareGroupAct]
  mul_smul g h f := by
    change poincareSchwartzPullback (g * h) f =
      poincareSchwartzPullback g (poincareSchwartzPullback h f)
    ext x
    rw [poincareSchwartzPullback_apply, poincareSchwartzPullback_apply,
      poincareSchwartzPullback_apply, mul_inv_rev]
    simp only [poincareGroupAct, SemidirectProduct.mul_left, SemidirectProduct.inv_left, map_inv,
      MulAut.inv_apply, SemidirectProduct.inv_right, toAdd_mul, toAdd_inv,
      SemidirectProduct.mul_right, Subgroup.coe_mul, InvMemClass.coe_inv, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, map_add, map_neg]
    congr 1
    have haction :
        Multiplicative.toAdd
            ((minkowskiIsometryAction h.right).symm
              ((minkowskiIsometryAction g.right).symm g.left)) =
          h.right.1.symm
            (Multiplicative.toAdd ((minkowskiIsometryAction g.right).symm g.left)) := rfl
    rw [haction]
    abel

@[simp]
theorem poincare_smul_schwartz_apply (g : PoincareGroup4)
    (f : SchwartzMap Spacetime4 ℂ) (x : Spacetime4) :
    (g • f) x = f (poincareGroupAct g⁻¹ x) :=
  poincareSchwartzPullback_apply g f x

/-- Interpret an endomorphism of an invariant submodule as a partially defined linear operator on
the ambient Hilbert space. This is Mathlib's concrete unbounded-operator representation. -/
def invariantDomainOperator
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (D : Submodule ℂ ℋ) (A : D →ₗ[ℂ] D) : ℋ →ₗ.[ℂ] ℋ where
  domain := D
  toFun := D.subtype.comp A

/-- **B1: Poincaré-covariant operator-valued distribution requirement shape.**

There is no brick-specific sentence in the currently pinned Jaffe--Witten excerpt that can
honestly be quoted as a verbatim definition of an operator-valued distribution. The requirement
below is Mathlib-formalized structure, not a source-pinned quote. Streater--Wightman remains the
intended future primary source, with Osterwalder--Schrader I+II and Glimm--Jaffe as supporting
references; no brick-specific primary text is pinned here.

One dense submodule is shared by every field operator. Returning values in that same submodule
makes field-domain invariance structural rather than propositional. Each field is also exposed as
a Mathlib `LinearPMap` on the ambient Hilbert space and required to be closable. For each fixed
domain vector, dependence on the test function is continuous in Mathlib's Schwartz seminorm
topology. Finally this structure is indexed by one exact B2a representation instance: its domain
is invariant under that action and the typed covariance equation is
`U(p) φ(f) U(p)⁻¹ ψ = φ(physicalGroupEquiv(p) • f) ψ`.

DECISION-STATUS: `PARTIALLY-SETTLED` (the requirement shape is present; a source-equivalence
prosecution and a known-model instance remain open).
-/
structure OperatorValuedDistribution
    {P : Type v} [Group P] [TopologicalSpace P] [MulAction P Spacetime4]
    (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (poincare : PoincareRepresentation P ℋ) where
  /-- The common operator domain. -/
  commonDomain : Submodule ℂ ℋ
  /-- The common domain is dense in the Hilbert space. -/
  commonDomain_dense : Dense (commonDomain : Set ℋ)
  /-- Complex-linearity in the test function and vectors, with image in the same common domain. -/
  field : SchwartzMap Spacetime4 ℂ →ₗ[ℂ] (commonDomain →ₗ[ℂ] commonDomain)
  /-- Distributional continuity in Mathlib's Schwartz topology, for each fixed domain vector. -/
  field_continuous : ∀ ψ : commonDomain,
    Continuous (fun f : SchwartzMap Spacetime4 ℂ => (field f ψ : ℋ))
  /-- Every field, viewed as a partial ambient-space operator with the exact common domain, is
  closable in Mathlib's graph-topology sense. -/
  field_closable : ∀ f : SchwartzMap Spacetime4 ℂ,
    (invariantDomainOperator commonDomain (field f)).IsClosable
  /-- The exact represented Poincaré action preserves the common field domain. -/
  commonDomain_representation_invariant : ∀ p : P, ∀ ψ : commonDomain,
    poincare.representation p ψ ∈ commonDomain
  /-- Covariance for the shared representation/field instance and the constructed physical
  inverse-pullback action on Schwartz functions. -/
  covariance : ∀ (p : P) (f : SchwartzMap Spacetime4 ℂ) (ψ : commonDomain),
    let Uinvψ : commonDomain :=
      ⟨poincare.representation p⁻¹ ψ, commonDomain_representation_invariant p⁻¹ ψ⟩
    (poincare.representation p (field f Uinvψ) : ℋ) =
      field (poincare.physicalGroupEquiv p • f) ψ
  /-- A genuine witness that the field is not the zero operator-valued distribution. -/
  nontriviality : ∃ (f : SchwartzMap Spacetime4 ℂ) (ψ : commonDomain),
    (field f ψ : ℋ) ≠ 0

/-- **B2b: positive-energy / joint-spectrum requirement shape.**

The pinned mass-gap context says verbatim (Jaffe--Witten, extracted lines 272--276):

> The positive energy axiom asserts that in any quantum
> field theory, the spectrum of H is supported in the region [0, ∞).

That quote concerns the Hamiltonian spectrum. The joint translation spectrum and forward-light-
cone inclusion below are a formal requirement-shape restatement, not a re-quote of those words.
The cone is the fixed `ForwardLightCone`, not data selected by an instantiator, and zero momentum
must belong to the spectrum. Four bounded self-adjoint surrogates are pairwise commuting, their
ordinary spectra are exactly the coordinate marginals of the supplied joint-spectrum set, and at
least one generator is nonzero. This anchors the formerly free-standing set to actual operators.
The theorem `energyGenerator_spectrum_nonnegative` derives the Hamiltonian marginal's real
nonnegative support from these fields. A genuine joint PVM remains a ledger obligation because the
pinned Mathlib has no PVM type/API.

DECISION-STATUS: `PARTIALLY-SETTLED`.

**R3 CORRECTION (2026-07-21).** Sol K3's gate-3 statement-prosecution
(`compute/SOL_GATE_CLAYSTATEMENT.md` §2.2, §4.2) proved that pre-R3 NONE of this structure's fields
mentioned `poincare` at all: `relocateSpectrumCondition` compiled, copying `translationGenerators`
and every other field UNCHANGED between two completely unrelated `PoincareRepresentation` values.
The floating-`MassGap.hamiltonian` defect R2 fixed had moved one structure boundary outward, not
been eliminated. **Fixed here**: `translationGenerators_are_stoneGenerators` below requires each
`translationGenerators μ` to be the Stone's-theorem infinitesimal generator of the ACTUAL
one-parameter unitary group `t ↦ poincare.representation(translation by t·e_μ)` that `poincare`
represents -- U(t) = exp(itH), dU/dt|₀ψ = iHψ. A blindly-copied generator from an unrelated
representation no longer has anywhere to attach a proof of this equation against the new
`poincare`, so the relocation exploit no longer type-checks (verified:
`Target/prosecution/R3_SOL_GATE3_REPAIR.lean`). A genuine PVM/Stone's-theorem
CONSTRUCTION (deriving generators from continuity) remains the separately-tracked `B2B-JOINT-PVM`
ledger obligation; this fix only closes the STATEMENT-level gap (nothing previously REQUIRED any
relationship at all).
-/
structure SpectrumCondition
    {P : Type v} [Group P] [TopologicalSpace P] [MulAction P Spacetime4]
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (poincare : PoincareRepresentation P ℋ) where
  /-- Abstract carrier for the joint spectrum of four translation generators. -/
  translationJointSpectrum : Set Spacetime4
  /-- The vacuum's zero four-momentum belongs to the spectrum. -/
  vacuum_momentum_mem : (0 : Spacetime4) ∈ translationJointSpectrum
  /-- Positive-energy support in the fixed forward cone. -/
  joint_spectrum_support : translationJointSpectrum ⊆ ForwardLightCone
  /-- Four bounded translation-generator surrogates, coordinate zero being the Hamiltonian. -/
  translationGenerators : Fin 4 → ℋ →L[ℂ] ℋ
  /-- Every bounded translation generator is self-adjoint. -/
  translationGenerators_selfAdjoint : ∀ μ, IsSelfAdjoint (translationGenerators μ)
  /-- Distinct translation generators commute. -/
  translationGenerators_commute :
    Pairwise (fun μ ν => Commute (translationGenerators μ) (translationGenerators ν))
  /-- Each ordinary operator spectrum is the exact coordinate marginal of the joint set. -/
  generator_spectrum_eq : ∀ μ,
    spectrum ℂ (translationGenerators μ) = CoordinateSpectrum translationJointSpectrum μ
  /-- The translation-generator family is not identically zero. -/
  translationGenerators_nontrivial : ∃ μ, translationGenerators μ ≠ 0
  /-- **R3 anchor.** `translationGenerators μ` is the Stone's-theorem infinitesimal generator of
  the represented translation subgroup along direction `μ`, ties this structure to `poincare`
  itself (not merely to a free-standing `ℋ →L[ℂ] ℋ` family). See the structure docstring. -/
  translationGenerators_are_stoneGenerators : ∀ (μ : Fin 4) (ψ : ℋ),
    HasDerivAt
      (fun t : ℝ => poincare.representation
        (poincare.physicalGroupEquiv.symm
          (SemidirectProduct.inl (Multiplicative.ofAdd (t • spacetimeUnitVector μ)))) ψ)
      (Complex.I • (translationGenerators μ ψ))
      0

/-- The energy generator has real, nonnegative spectrum. This is proved from the exact energy
marginal link and the fixed forward-cone support; it is not another caller-supplied field. -/
theorem energyGenerator_spectrum_nonnegative
    {P : Type v} [Group P] [TopologicalSpace P] [MulAction P Spacetime4]
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    {poincare : PoincareRepresentation P ℋ} (condition : SpectrumCondition poincare)
    {z : ℂ} (hz : z ∈ spectrum ℂ (condition.translationGenerators 0)) :
    0 ≤ z.re ∧ z.im = 0 := by
  rw [condition.generator_spectrum_eq] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact ⟨(condition.joint_spectrum_support hp).1, Complex.ofReal_im (p 0)⟩

/-- **B3: Hamiltonian mass-gap requirement shape.**

Verbatim Jaffe--Witten mass-gap context (extracted lines 272--276):

> Since the vacuum vector Ω is Poincaré invariant, it is an eigenstate with zero
> energy, namely HΩ = 0. The positive energy axiom asserts that in any quantum
> field theory, the spectrum of H is supported in the region [0, ∞). A quantum field
> theory has a mass gap ∆ if H has no spectrum in the interval (0, ∆) for some ∆ > 0.
> The supremum of such ∆ is the mass m, and we require m < ∞.

The Lean inclusion is explicitly a **restatement, not a re-quote**: positive energy together
with absence of spectrum in `(0, ∆)` is rendered as
`spectrum ℂ H ⊆ {0} ∪ {z | z.im = 0 ∧ ∆ ≤ z.re}`. Mathlib's `spectrum` applies here to a
bounded
continuous linear endomorphism on a complete complex Hilbert space. The physical unbounded
Hamiltonian and finite supremal mass are ledger obligations, not fields an instance can choose.

**R2 CORRECTION (2026-07-21).** Pre-R2, `MassGap` was parametrized ONLY by `ℋ` -- no `P`, no
`poincareRepresentation`, no `SpectrumCondition` -- and carried its OWN independent `hamiltonian`
field with no equation tying it to `SpectrumCondition.translationGenerators 0`, the operator this
very docstring identifies (two paragraphs up, "coordinate zero being the Hamiltonian") as the
physical Hamiltonian. `YangMillsBrickBundle`'s `massGap : MassGap ℋ` field carried no linking
field either, unlike `spectrumCondition : SpectrumCondition poincareRepresentation` (indexed by the
exact representation) or `yangMillsContent_gaugeGroupData` (an explicit tying equation). A prover
could therefore supply a `MassGap` whose asserted gap floated free of the theory's own energy
operator -- found independently by the Claude-family statement prosecution
(`compute/prosecution/PROS_CLAYSTATEMENT_REPAIR.md` §5). **Fixed here**: `MassGap` is now indexed
by a `SpectrumCondition` instance, and `hamiltonian` is DELETED as an independent field -- every use
is literally `condition.translationGenerators 0`, so there is no longer any data position for a
disconnected operator to occupy. Self-adjointness of that operator is no longer a separate
caller-supplied field either (`MassGap.hamiltonian_selfAdjoint` below derives it from
`condition.translationGenerators_selfAdjoint`, removing a second field a prover could otherwise
mis-supply). Only the genuinely new physical content -- the vacuum, its zero-energy eigenvalue
equation for the ACTUAL operator, the gap, and the spectrum-exclusion claim -- remain as fields.

DECISION-STATUS: `PARTIALLY-SETTLED`.
-/
structure MassGap
    {P : Type v} [Group P] [TopologicalSpace P] [MulAction P Spacetime4]
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    {poincare : PoincareRepresentation P ℋ} (condition : SpectrumCondition poincare) where
  /-- Distinguished vacuum vector. -/
  vacuum : ℋ
  /-- Vacuum normalization. -/
  vacuum_unit : ‖vacuum‖ = 1
  /-- `H Ω = 0`, where `H` is literally `condition.translationGenerators 0` -- the file's own
  physical Hamiltonian, not a free-floating surrogate (R2 fix). -/
  vacuum_zero_energy : condition.translationGenerators 0 vacuum = 0
  /-- Candidate gap. -/
  gap : ℝ
  /-- Strict positivity required by the pinned statement. -/
  gap_positive : 0 < gap
  /-- Complex-spectrum rendering of the zero eigenvalue plus real energies at least `gap`, for the
  file's own physical Hamiltonian `condition.translationGenerators 0` (R2 fix: no longer an
  independent `hamiltonian` field). -/
  spectrum_inclusion : spectrum ℂ (condition.translationGenerators 0) ⊆
    ({0} : Set ℂ) ∪ {z : ℂ | z.im = 0 ∧ gap ≤ z.re}

/-- Self-adjointness of the mass-gap Hamiltonian is derived, not supplied: it is
`condition.translationGenerators_selfAdjoint 0`, so a `MassGap` instance can no longer carry a
self-adjointness claim disconnected from the `SpectrumCondition` it is indexed by. -/
theorem MassGap.hamiltonian_selfAdjoint
    {P : Type v} [Group P] [TopologicalSpace P] [MulAction P Spacetime4]
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    {poincare : PoincareRepresentation P ℋ} {condition : SpectrumCondition poincare}
    (_m : MassGap condition) :
    IsSelfAdjoint (condition.translationGenerators 0) :=
  condition.translationGenerators_selfAdjoint 0

/-- Schwartz test functions for an `n`-point Euclidean Green function. -/
abbrev SchwingerTestFunction (n : ℕ) := SchwartzMap (Fin n → Spacetime4) ℂ

/-- The integral formula from which an `n`-point Schwinger functional is induced, for `n ≥ 1`. This
raw value is kept separate from `SchwingerMoment`: an unchecked family of such values is not yet a
distribution.

**R3 CORRECTION (2026-07-21).** Sol K3's gate-3 statement-prosecution
(`compute/SOL_GATE_CLAYSTATEMENT.md` §1) proved this definition's pre-R3 `if n = 0 then 1` branch
made `SchwingerMoment` UNINHABITABLE: `distribution 0` is a `TemperedDistribution`, hence a
continuous *linear* functional, so `distribution 0 0 = 0` by linearity, while `integral_eq`
(pre-R3, unconditional in `n`) forced `distribution 0 f = 1` for every `f`, including `f = 0` --
`0 = 1`, machine-checked (`noSchwingerMoment` in Sol's probe, `#print axioms` clean). The primary
source resolves this: Adamo--Moriwaki--Tanimoto, extracted line 999, "(OS0′) (Linear growth)
`S0 = 1` (for `n = 0` there is no upper index)" -- `S₀` is stated as a bare SCALAR, not a
distribution paired against a test function (there is no `S₀(f)` in the source; only `S_n^a(f)` for
`n ≥ 1`). The fix, below: `SchwingerMoment.integral_eq` now applies only for `n ≠ 0`; the genuine
zero-point content is `SchwingerMoment.vacuumNormalization = 1`, a scalar field, matching the
source's own `S₀ = 1` literally rather than manufacturing a functional identity the source never
states. This function's own `n = 0` branch is consequently DEAD for constraint purposes (never
invoked by `integral_eq`); kept only so the function stays total, and documented as such. -/
noncomputable def SchwingerMomentIntegral
    {D : Type w} [MeasurableSpace D] (μ : MeasureTheory.Measure D)
    (fieldConfiguration : D → Spacetime4 → ℝ) (n : ℕ)
    (f : SchwingerTestFunction n) : ℂ :=
  if n = 0 then 1
  else ∫ ω, ∫ x, f x * ∏ i, (fieldConfiguration ω (x i) : ℂ) ∂MeasureTheory.volume ∂μ

/-- A Schwinger-moment family is a family of genuine Mathlib tempered distributions whose
evaluations equal the measure/field integral formula for every `n ≥ 1`, together with the OS-II
zero-point normalization `S₀ = 1` as a bare scalar (R3 fix; see `SchwingerMomentIntegral`'s
docstring for the primary-source citation and the exact defect this repairs). This is the OS-II
distribution-space membership certificate; a bare function family cannot inhabit it. -/
structure SchwingerMoment
    {D : Type w} [MeasurableSpace D] (μ : MeasureTheory.Measure D)
    (fieldConfiguration : D → Spacetime4 → ℝ) where
  distribution : (n : ℕ) → TemperedDistribution (Fin n → Spacetime4) ℂ
  /-- Integral-formula identification, imposed only for `n ≥ 1` (R3 fix: excludes the
  contradictory `n = 0` case; see the structure docstring). -/
  integral_eq : ∀ n, n ≠ 0 → ∀ (f : SchwingerTestFunction n),
    distribution n f = SchwingerMomentIntegral μ fieldConfiguration n f
  /-- `distribution 0` carries no independent content once the zero-point normalization below is
  separated out; pinned to the zero functional so it cannot float unconstrained (R3 fix). -/
  distribution_zero_eq_zero : distribution 0 = 0
  /-- OS-II's zero-point normalization, literally the scalar `S₀` of the primary source (R3 fix).
  Source: Adamo--Moriwaki--Tanimoto, extracted line 999, "(OS0′) (Linear growth) `S0 = 1`".

  **R4 disclosure (2026-07-21).** Sol K3's re-gate (`compute/SOL_GATE_CLAYSTATEMENT_R3.md` §5.1,
  ported machine-checked at `Target/prosecution/R4_SOL_GATE4_REPAIR.lean` Part 2) proved this pair
  of fields is type-theoretically PINNED (`vacuumNormalization_eq_one` forces the value) but
  EXTERNALLY VACUOUS: any distribution family already satisfying `integral_eq` and
  `distribution_zero_eq_zero` extends to a full `SchwingerMoment` for free, by
  `vacuumNormalization := 1; vacuumNormalization_eq_one := rfl`
  (`addVacuousVacuumNormalization`). It rejects no candidate that already satisfies the other
  fields. It is faithful to the source's own bare `S₀ = 1` scalar convention, so this is not a
  contradiction and the field is kept -- but it must **never** be billed as measure normalization
  (it does not constrain `μ Set.univ`) or as evidence of a nontrivial theory. -/
  vacuumNormalization : ℂ
  vacuumNormalization_eq_one : vacuumNormalization = 1

/-- A concrete per-`n` Schwartz-seminorm bound certificate for one fixed Schwinger family. -/
structure SchwingerBoundCertificate
    (S : (n : ℕ) → TemperedDistribution (Fin n → Spacetime4) ℂ) where
  /-- Distribution order used by the bound at each `n`. -/
  order : ℕ → ℕ
  /-- Positive bound constants. -/
  constants : ℕ → ℝ
  constants_positive : ∀ n, 0 < constants n
  /-- The bound uses the certificate's actual order and constant. -/
  bound : ∀ n (f : SchwingerTestFunction n),
    ‖S n f‖ ≤ constants n * SchwartzMap.seminorm ℂ (order n) (order n) f

/-- OS-I-style temperedness: every `n` has some finite seminorm order and bound, without one
uniform linear-in-`n` order slope or a factorial envelope across `n`. -/
def OSITemperedGrowth
    (S : (n : ℕ) → TemperedDistribution (Fin n → Spacetime4) ℂ) : Prop :=
  ∀ n, ∃ p : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ f : SchwingerTestFunction n,
    ‖S n f‖ ≤ C * SchwartzMap.seminorm ℂ p p f

/-- Every explicit bound certificate supplies the weaker OS-I-style per-`n` temperedness. -/
theorem SchwingerBoundCertificate.osITemperedGrowth
    {S : (n : ℕ) → TemperedDistribution (Fin n → Spacetime4) ℂ}
    (certificate : SchwingerBoundCertificate S) : OSITemperedGrowth S := by
  intro n
  exact ⟨certificate.order n, certificate.constants n, certificate.constants_positive n,
    certificate.bound n⟩

/-- Factorial growth in the OS-II sense: one global envelope `α (n!)^β`. -/
def FactorialGrowth (σ : ℕ → ℝ) : Prop :=
  ∃ α β : ℝ, 0 < α ∧ 0 ≤ β ∧ ∀ n,
    σ n ≤ α * (n.factorial : ℝ) ^ β

/-- OS-II E0′, represented on a fixed bound certificate: one positive integer `s` controls the
Schwartz order by `n*s` for every `n`, and the constants have one factorial-growth envelope.

Source status: secondary-source statement, Adamo--Moriwaki--Tanimoto arXiv:2407.18222 equation (22),
pinned at `OS_SOURCES/secondary_moriwaki_tanimoto_2024.txt:999-1003`; corroborated by the
readable OS-II p. 287 web extraction at `os2_projecteuclid_webextract.md:32`. The OS-II primary
PDF pin remains pending, so this is not labeled a verbatim primary transcription. -/
def OSIICorrectedGrowth
    {S : (n : ℕ) → TemperedDistribution (Fin n → Spacetime4) ℂ}
    (certificate : SchwingerBoundCertificate S) : Prop :=
  (∃ s : ℕ, 0 < s ∧ ∀ n, certificate.order n ≤ n * s) ∧
    FactorialGrowth certificate.constants

/-- Positive Euclidean-time support for an `n`-point Schwartz test function. -/
def HasPositiveEuclideanTimeSupport {n : ℕ} (f : SchwingerTestFunction n) : Prop :=
  Function.support f ⊆ {x | ∀ i, 0 < x i 0}

/-- Positive-time Schwinger test functions, retaining the support proof in the type. -/
abbrev PositiveTimeSchwingerTest (n : ℕ) :=
  {f : SchwingerTestFunction n // HasPositiveEuclideanTimeSupport f}

/-- A realization of the same Schwinger distributions as configuration-space observables.
The cross-order field explicitly identifies each reflected product expectation with an
`S_{m+n}` value. `reflectedTensorProduct` is typed but its full source-equivalence construction
remains a named, honest requirement rather than a claimed theorem. -/
structure SchwingerObservableRealization
    {D : Type w} [MeasurableSpace D] (μ : MeasureTheory.Measure D)
    (fieldConfiguration : D → Spacetime4 → ℝ) (reflection : D ≃ᵐ D)
    (moments : SchwingerMoment μ fieldConfiguration) where
  observable : (n : ℕ) → PositiveTimeSchwingerTest n → D → ℂ
  observable_integrable : ∀ n f, MeasureTheory.Integrable (observable n f) μ
  expectation_eq_moment : ∀ n f,
    ∫ ω, observable n f ω ∂μ = moments.distribution n f.1
  reflectedTensorProduct : ∀ {m n},
    PositiveTimeSchwingerTest m → PositiveTimeSchwingerTest n → SchwingerTestFunction (m + n)
  reflected_product_integrable : ∀ {m n} (f : PositiveTimeSchwingerTest m)
    (g : PositiveTimeSchwingerTest n),
      MeasureTheory.Integrable
        (fun ω => star (observable m f (reflection ω)) * observable n g ω) μ
  reflected_product_eq_cross_moment : ∀ {m n} (f : PositiveTimeSchwingerTest m)
    (g : PositiveTimeSchwingerTest n),
      ∫ ω, star (observable m f (reflection ω)) * observable n g ω ∂μ =
        moments.distribution (m + n) (reflectedTensorProduct f g)

/-- The set of field-generated positive-time observables before taking its complex span. -/
def SchwingerObservableRealization.generatorSet
    {D : Type w} [MeasurableSpace D] {μ : MeasureTheory.Measure D}
    {fieldConfiguration : D → Spacetime4 → ℝ} {reflection : D ≃ᵐ D}
    {moments : SchwingerMoment μ fieldConfiguration}
    (realization : SchwingerObservableRealization μ fieldConfiguration reflection moments) :
    Set (D → ℂ) :=
  {F | ∃ n f, realization.observable n f = F}

/-- Finite-sequence (Gram-matrix) reflection positivity on the exact field-generated observable
family. Expanding the quadratic integral gives cross-orders identified by
`reflected_product_eq_cross_moment` with source equation (23)'s `S_{m+n}` terms.

Source status: secondary-source statement, Adamo--Moriwaki--Tanimoto equation (23), pinned at
`OS_SOURCES/secondary_moriwaki_tanimoto_2024.txt:1009-1029`; corroborated by the OCR-normalized
OS-I p. 88 web extraction at `os1_projecteuclid_webextract.md:28`. Not tagged verbatim primary. -/
def OSPrimaryReflectionPositive
    {D : Type w} [MeasurableSpace D] (μ : MeasureTheory.Measure D)
    (reflection : D ≃ᵐ D)
    (observable : (n : ℕ) → PositiveTimeSchwingerTest n → D → ℂ) : Prop :=
  ∀ (k : ℕ) (orders : Fin k → ℕ)
    (tests : (i : Fin k) → PositiveTimeSchwingerTest (orders i)) (c : Fin k → ℂ),
    let H : D → ℂ := ∑ i, c i • observable (orders i) (tests i)
    MeasureTheory.Integrable (fun x => star (H (reflection x)) * H x) μ ∧
      0 ≤ Complex.re (∫ x, star (H (reflection x)) * H x ∂μ)

/-- **B4: architectural Osterwalder--Schrader requirements on a Euclidean measure.**

The primary PDF bytes remain `PIN-PENDING` after direct Project Euclid and Springer `curl`
attempts. Page-separated primary-text extracts and exact failure evidence are hash-pinned in
`TargetTrack_SOURCES/OS_SOURCES/`; all formula descriptions below are explicitly normalized
transcriptions, not claims of visual verbatim fidelity.

The pinned secondary fallback (Adamo--Moriwaki--Tanimoto, extracted lines 999–1048) states E1 Euclidean
invariance, E2 finite-sequence positivity, E4 clustering under a purely spatial translation, and
the uniform E0′ linear/factorial bound. The primary web extracts corroborate that OS-II p. 282
identifies OS-I Lemma 8.8 as wrong and pp. 287–288 replace mere per-`n` temperedness by E0′. This
structure encodes those four architectural clauses and ties them to one probability measure,
one faithful E(4) action, and the Schwinger moments induced by the same field configurations.

DECISION-STATUS: `PARTIALLY-SETTLED` only because the primary PDF/page-image pin and a source-
equivalence prosecution are still open; the architectural clauses themselves are present.
-/
structure OSAxioms (D : Type w) [MeasurableSpace D] where
  /-- Candidate Euclidean probability measure on the distribution-space carrier. -/
  euclideanMeasure : MeasureTheory.Measure D
  /-- Probability normalization; in particular the zero measure cannot qualify. -/
  measure_univ : euclideanMeasure Set.univ = 1
  /-- A measurable action of the constructed physical Euclidean group E(4). -/
  physicalEuclideanAction : EuclideanGroup4 → D ≃ᵐ D
  /-- Identity element acts as the identity measurable equivalence. -/
  physicalEuclideanAction_one :
    physicalEuclideanAction 1 = MeasurableEquiv.refl D
  /-- Compatibility square for multiplication; `trans` applies the right action first. -/
  physicalEuclideanAction_mul : ∀ g h,
    physicalEuclideanAction (g * h) =
      (physicalEuclideanAction h).trans (physicalEuclideanAction g)
  /-- The represented E(4) action is faithful, excluding a trivial physical-group action. -/
  physicalEuclideanAction_injective : Function.Injective physicalEuclideanAction
  /-- Measurable symmetries under which the measure is invariant. -/
  euclideanSymmetries : Set (D ≃ᵐ D)
  /-- The supplied symmetry set is exactly the range of the physical E(4) action. -/
  euclideanSymmetries_eq_range :
    euclideanSymmetries = Set.range physicalEuclideanAction
  /-- At least the identity symmetry is present. -/
  identity_mem_symmetries : MeasurableEquiv.refl D ∈ euclideanSymmetries
  /-- Actual measure invariance under every physical Euclidean symmetry. -/
  euclidean_invariance : ∀ e ∈ euclideanSymmetries,
    MeasureTheory.Measure.map e euclideanMeasure = euclideanMeasure
  /-- Scalar field configurations whose moments are bounded below. -/
  fieldConfiguration : D → Spacetime4 → ℝ
  /-- The scalar field configuration is not identically zero. -/
  fieldConfiguration_nontrivial : ∃ ω x, fieldConfiguration ω x ≠ 0
  /-- The E(4) action on configurations intertwines the concrete affine action on spacetime. -/
  fieldConfiguration_covariant : ∀ g ω x,
    fieldConfiguration (physicalEuclideanAction g ω) (euclideanGroupAct g x) =
      fieldConfiguration ω x
  /-- Euclidean time reflection. -/
  reflection : D ≃ᵐ D
  /-- The supplied reflection is exactly the represented fixed time-reflection element, not an
  arbitrary symmetry or the identity. -/
  reflection_physical :
    reflection = physicalEuclideanAction EuclideanTimeReflection
  /-- Reflection is involutive. -/
  reflection_involutive : Function.Involutive reflection
  /-- The reflection is one of the represented physical Euclidean symmetries. -/
  reflection_mem_symmetries : reflection ∈ euclideanSymmetries
  /-- The measure/field integral family is certified as genuine tempered distributions. -/
  schwingerMoments : SchwingerMoment euclideanMeasure fieldConfiguration
  /-- Positive-time field observables realize those exact distributions and their reflected
  products realize the exact cross-order `S_{m+n}` values. -/
  schwingerRealization : SchwingerObservableRealization euclideanMeasure fieldConfiguration
    reflection schwingerMoments
  /-- Positive-time observables, closed under finite complex linear combinations. -/
  positiveTimeObservables : Submodule ℂ (D → ℂ)
  /-- The sector is not caller-selected: it is exactly the span of the realized positive-time
  Schwinger observables. -/
  positiveTimeObservables_eq_generated :
    positiveTimeObservables = Submodule.span ℂ schwingerRealization.generatorSet
  /-- The positive-time sector contains a nonconstant observable, excluding the constants-only
  degenerate sector. -/
  nonconstant_mem_positiveTime :
    ∃ F ∈ positiveTimeObservables, ∃ x y, F x ≠ F y
  /-- The OS quadratic form is integrable and nonnegative on the supplied sector. -/
  reflection_positive : ∀ F ∈ positiveTimeObservables,
    MeasureTheory.Integrable (fun x => star (F (reflection x)) * F x) euclideanMeasure ∧
      0 ≤ Complex.re (∫ x, star (F (reflection x)) * F x ∂euclideanMeasure)
  /-- Primary finite-sequence OS-I E2 positivity on the exact generated family and measure. -/
  primary_reflection_positive :
    OSPrimaryReflectionPositive euclideanMeasure reflection schwingerRealization.observable
  /-- Typed `S_{m+n}` test produced by translating the second positive-time observable in a
  purely spatial direction. Full construction of this tensor test remains an explicit field. -/
  translatedTensorProduct : ∀ {m n}, PositiveTimeSchwingerTest m →
    PositiveTimeSchwingerTest n → ℝ → SpatialVector3 → SchwingerTestFunction (m + n)
  /-- The translated product expectation is the same cross-order Schwinger distribution value. -/
  translated_product_eq_cross_moment : ∀ {m n} (f : PositiveTimeSchwingerTest m)
    (g : PositiveTimeSchwingerTest n) (t : ℝ) (a : SpatialVector3),
      ∫ x, schwingerRealization.observable m f x *
          schwingerRealization.observable n g (physicalEuclideanAction
            (euclideanSpatialTranslation t a) x) ∂euclideanMeasure =
        schwingerMoments.distribution (m + n) (translatedTensorProduct f g t a)
  /-- OS-I E4 clustering under the correct purely spatial E(4) translation action, stated on
  the exact cross-order Schwinger distribution family rather than a supplied submodule. -/
  clustering : ∀ m (f : PositiveTimeSchwingerTest m),
    ∀ n (g : PositiveTimeSchwingerTest n),
    ∀ a : SpatialVector3, ‖a‖ = 1 →
      Filter.Tendsto
        (fun t : ℝ => schwingerMoments.distribution (m + n)
          (translatedTensorProduct f g t a))
        Filter.atTop
        (nhds ((schwingerMoments.distribution m f.1) *
          (schwingerMoments.distribution n g.1)))
  /-- Concrete bounds on the Schwinger moments of this very measure and field map. -/
  schwingerGrowth : SchwingerBoundCertificate schwingerMoments.distribution
  /-- OS-II's corrected uniform linear/factorial growth requirement. -/
  corrected_growth : OSIICorrectedGrowth schwingerGrowth

/-- Compact topological gauge-group data currently expressible without inventing Lie machinery.

**This structure is WEAKER than the Jaffe–Witten problem statement requires, and its name says so
plainly.** Jaffe–Witten's actual hypothesis is "a compact **simple** [Lie] gauge group G"
(extracted lines 277–280, quoted verbatim below `ClayYangMillsPartialSkeletonFor`). What is
formalized here is exactly seven fields — `compact`, `continuous_mul`, `continuous_inv`,
`nontrivial`, `hausdorff`, `preconnected`, `not_commutative` — and **nothing else**: no
finite-dimensional manifold structure, no Lie bracket, no group-theoretic simplicity predicate
(no `∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤`, and Mathlib's abstract-group
`IsSimpleGroup` is not equivalent to Lie-simplicity and is not used here). **Two named
things are missing: Lie
structure, and simplicity.** Both are tracked by the one open ledger item `G-LIE-SIMPLICITY`
(`TARGET_BURNDOWN.md`), unchanged in scope by this rename. Mathlib supplies the group, topology,
compactness, and continuity predicates used here. F5 requires this exact object in the shared B5
content so that a trivial label group cannot masquerade as the link group.

**R5 RENAME (2026-07-21), the R4 standard applied one level down.** This structure was named
`CompactSimpleGaugeGroupData` through R4. `compute/prosecution/PROS_CLAYSTATEMENT_R4.md` (verdict
QUALIFIED) proved, by machine-checked general construction
(`Target/prosecution/PROD_CIRCLE_NOT_SIMPLE_PORTED.lean`, ported below), that R4's own rename
standard for the flagship target — *"a comment saying 'partial' does not repair what a strong name
causes downstream readers to cite"* — had not been applied to this structure, one level down: for
**any** nonabelian `G` already satisfying all seven fields, the product `G × Circle` also satisfies
all seven fields and is **provably not simple** (it has `{1} × Circle` as a nontrivial proper
normal subgroup), so `not_commutative` cannot be repaired by excluding a special case — the gap is
structural, not a missing witness exclusion. Renamed to
**`CompactConnectedNonabelianGaugeGroupData`**, which claims exactly what the seven fields
enforce (compactness, connectedness via `hausdorff`+`preconnected`, and nonabelian-ness) and
nothing more. **Real Lie/simplicity content was deliberately NOT added here** — that is a
substantial separate formalization program (`G-LIE-SIMPLICITY`), and faking it to fit a strong
name is the exact defect this rename corrects; renaming to match content, not content invented to
match a name, is the honest move (as R4 itself did for the flagship `ClayYangMillsPartialSkeleton`
rename).

**R3 CORRECTION (2026-07-21).** Sol K3's gate-3 statement-prosecution
(`compute/SOL_GATE_CLAYSTATEMENT.md` §4.10) proved this structure was name-only: it constructed
`cyclicFourQualifies : CompactConnectedNonabelianGaugeGroupData (Multiplicative (ZMod 4))` --
a finite cyclic group, discharging `compact`/`continuous_mul`/`continuous_inv` trivially under
the discrete topology (`continuous_of_discreteTopology`). **Partially fixed here** (full
Lie/simplicity content remains the disclosed `G-LIE-SIMPLICITY` obligation): `hausdorff`
and `preconnected` below force `G` to be infinite whenever `nontrivial` holds
(`CompactConnectedNonabelianGaugeGroupData.infinite`, proved below from the elementary fact
that a nontrivial finite Hausdorff space cannot be preconnected -- finite + T1 ⟹ discrete
(`Finite.instDiscreteTopology`), and a nontrivial discrete space has a proper nonempty clopen
subset, contradicting preconnectedness). This directly and generally refutes
`cyclicFourQualifies`-shaped witnesses for ANY topology (not merely the discrete one exhibited):
`ZMod 4`, `ZMod n`, or any other finite nontrivial group can no longer inhabit this structure,
regardless of which topology a witness attempts. Every genuine compact simple Lie group (SU(n),
SO(n), Sp(n), the exceptional groups) is both Hausdorff and connected, so this adds no burden on
the intended models. Machine-checked: `Target/prosecution/R3_SOL_GATE3_REPAIR.lean`.

**R4 CORRECTION (2026-07-21).** Sol K3's de-correlated re-gate on the R3 bytes
(`compute/SOL_GATE_CLAYSTATEMENT_R3.md` §5/§6/§10) built, independently and axiom-clean,
`circleQualifies : CompactConnectedNonabelianGaugeGroupData Circle` -- Mathlib's `Circle`
(the circle group, U(1)) is compact, connected, Hausdorff, and nontrivial, so
`hausdorff`/`preconnected` exclude finite carriers only, **not nonsimple ones**.
`circle_is_abelian` then observed the accepted witness is abelian: "the structure has no
simplicity field and no Lie field at all." **Fixed here**: `not_commutative` below requires
an explicit noncommuting pair, the minimum group-theoretic
content that separates SU(n≥2)/SO(n≥3)/Sp(n)/the exceptional groups (all nonabelian) from every
compact connected abelian Lie group -- every torus of every rank, `Circle` foremost among them.
This is **not** a full simplicity predicate (a nonabelian group need not be simple -- e.g. `SO(4)`
is not simple as an abstract Lie group despite being nonabelian and compact connected); genuine
Lie-theoretic simplicity remains the disclosed `G-LIE-SIMPLICITY` obligation, unchanged in scope.
What R4 buys is the concrete, mechanically-verified exclusion Sol's counterexample demanded:
`Circle` (and every other compact connected abelian carrier) can no longer inhabit this structure
under ANY topology, and the intended SU(2) target is unaffected -- `su2_not_commutative` below
constructs an explicit noncommuting pair in `Matrix.specialUnitaryGroup (Fin 2) ℂ`
(`σ_z`-type and a Weyl-reflection-type generator), so the new field does not over-constrain the
campaign's actual target group. Machine-checked: `Target/prosecution/R4_SOL_GATE4_REPAIR.lean`.

DECISION-STATUS: `PARTIALLY-SETTLED`.
-/
structure CompactConnectedNonabelianGaugeGroupData
    (G : Type g) [Group G] [TopologicalSpace G] where
  /-- Compactness of the underlying topological carrier. -/
  compact : IsCompact (Set.univ : Set G)
  /-- Compatibility of multiplication with the topology. -/
  continuous_mul : Continuous (fun p : G × G => p.1 * p.2)
  /-- Compatibility of inversion with the topology. -/
  continuous_inv : Continuous (fun g : G => g⁻¹)
  /-- Exclude the one-element group while Lie-theoretic simplicity is formalized. -/
  nontrivial : Nontrivial G
  /-- **R3 anchor.** Every compact simple Lie group is Hausdorff; combined with `preconnected`
  below this forces `G` infinite, blocking finite "label" groups (see structure docstring). -/
  hausdorff : T2Space G
  /-- **R3 anchor.** Every compact simple Lie group (in the standard classification) is connected.
  Combined with `hausdorff` above, this forces `G` infinite whenever `nontrivial` holds. -/
  preconnected : PreconnectedSpace G
  /-- **R4 anchor.** An explicit noncommuting pair. Every compact simple Lie group is nonabelian;
  this excludes `Circle`/U(1) and every other compact connected abelian carrier (Sol K3's
  counterexample, see structure docstring), while `su2_not_commutative`
  (`Target/prosecution/R4_SOL_GATE4_REPAIR.lean`) proves the intended SU(2) target is unaffected.
  NOT a full simplicity predicate -- nonabelian compact connected Lie groups need not be simple
  (e.g. `SO(4)`); genuine Lie-simplicity remains `G-LIE-SIMPLICITY`. -/
  not_commutative : ∃ a b : G, a * b ≠ b * a

/-- **R3 fix.** Compact simple gauge-group data forces the underlying carrier to be infinite: a
nontrivial finite group cannot be simultaneously Hausdorff and preconnected. Directly refutes Sol
K3's `cyclicFourQualifies` (`compute/SOL_GATE_CLAYSTATEMENT.md` §4.10) for ANY topology, not only
the discrete witness exhibited there. -/
theorem CompactConnectedNonabelianGaugeGroupData.infinite
    {G : Type g} [Group G] [TopologicalSpace G]
    (data : CompactConnectedNonabelianGaugeGroupData G) :
    Infinite G := by
  by_contra hnotInf
  rw [not_infinite_iff_finite] at hnotInf
  haveI := hnotInf
  haveI := data.hausdorff
  haveI := data.preconnected
  haveI : DiscreteTopology G := Finite.instDiscreteTopology
  have hsub : Subsingleton G := by
    refine ⟨fun a b => ?_⟩
    have hclopen : IsClopen ({a} : Set G) := isClopen_discrete {a}
    rcases isClopen_iff.mp hclopen with h | h
    · exact absurd h (Set.singleton_ne_empty a)
    · have hb : b ∈ ({a} : Set G) := h ▸ Set.mem_univ b
      exact hb.symm
  exact (not_nontrivial_iff_subsingleton.mpr hsub) data.nontrivial

/-- **R4 fix.** Compact simple gauge-group data forces the underlying carrier to be nonabelian:
directly from the `not_commutative` field. Refutes Sol K3's `circleQualifies`
(`compute/SOL_GATE_CLAYSTATEMENT_R3.md` §5) for ANY topology and ANY compact connected abelian
carrier, not only `Circle`. -/
theorem CompactConnectedNonabelianGaugeGroupData.not_commGroup
    {G : Type g} [Group G] [TopologicalSpace G] (data : CompactConnectedNonabelianGaugeGroupData G)
    (hcomm : ∀ a b : G, a * b = b * a) : False := by
  obtain ⟨a, b, hab⟩ := data.not_commutative
  exact hab (hcomm a b)

/-- Side-length parameters for the campaign's three-dimensional periodic cubic lattices. A value
`L μ` represents side length `L μ + 1`, making nonemptiness structural. -/
abbrev PeriodicLatticeExtent := Fin 3 → ℕ

/-- Sites of the periodic cubic lattice `T³_L`. -/
abbrev PeriodicLatticeSite (L : PeriodicLatticeExtent) :=
  (μ : Fin 3) → Fin (L μ + 1)

/-- Positively oriented links, indexed by a site and one of three coordinate directions. -/
abbrev PeriodicLatticeEdge (L : PeriodicLatticeExtent) :=
  PeriodicLatticeSite L × Fin 3

/-- Ordered coordinate-plane directions for a plaquette. -/
abbrev PeriodicPlaquetteDirections := {d : Fin 3 × Fin 3 // d.1 < d.2}

/-- Positively oriented unit plaquettes, indexed by a base site and an ordered direction pair. -/
abbrev PeriodicLatticePlaquette (L : PeriodicLatticeExtent) :=
  PeriodicLatticeSite L × PeriodicPlaquetteDirections

/-- A mod-two plaquette-sheet candidate on the periodic cubic lattice, matching the carrier used
by the campaign's cube-activation/flux-weight enumeration. -/
abbrev PeriodicPlaquetteSheet (L : PeriodicLatticeExtent) :=
  Finset (PeriodicLatticePlaquette L)

/-- Link configurations on the exact periodic cubic edge set. -/
abbrev PeriodicLinkConfiguration (G : Type*) (L : PeriodicLatticeExtent) :=
  PeriodicLatticeEdge L → G

/-- Periodic forward shift by one site in direction `μ`. -/
def periodicLatticeShift {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    PeriodicLatticeSite L :=
  Function.update x μ (x μ + 1)

/-- The oriented four-link plaquette word used by the campaign's Wilson action. -/
def periodicPlaquetteHolonomy {G : Type*} [Group G] {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration G L) (p : PeriodicLatticePlaquette L) : G :=
  let x := p.1
  let μ := p.2.1.1
  let ν := p.2.1.2
  U (x, μ) * U (periodicLatticeShift x μ, ν) *
    (U (periodicLatticeShift x ν, μ))⁻¹ * (U (x, ν))⁻¹

/-- The four unoriented edge carriers of a periodic unit plaquette. -/
def periodicPlaquetteBoundaryEdges {L : PeriodicLatticeExtent}
    (p : PeriodicLatticePlaquette L) : Finset (PeriodicLatticeEdge L) := by
  classical
  let x := p.1
  let μ := p.2.1.1
  let ν := p.2.1.2
  exact {(x, μ), (periodicLatticeShift x μ, ν),
    (periodicLatticeShift x ν, μ), (x, ν)}

/-- Mod-two closed-sheet condition: every edge is incident to an even number of activated
plaquettes. This is the concrete `∂₂S=0` predicate underlying the campaign's `H₂(T³;ℤ₂)` split. -/
def IsClosedPeriodicPlaquetteSheet {L : PeriodicLatticeExtent}
    (S : PeriodicPlaquetteSheet L) : Prop :=
  ∀ e : PeriodicLatticeEdge L,
    Even (S.filter (fun p => e ∈ periodicPlaquetteBoundaryEdges p)).card

/-- Local lattice gauge transformation `U(x,μ) ↦ γ(x)U(x,μ)γ(x+μ)⁻¹`. -/
def periodicGaugeTransform {G : Type*} [Group G] {L : PeriodicLatticeExtent}
    (γ : PeriodicLatticeSite L → G) (U : PeriodicLinkConfiguration G L) :
    PeriodicLinkConfiguration G L := fun e =>
  γ e.1 * U e * (γ (periodicLatticeShift e.1 e.2))⁻¹

/-- A signed coordinate step; `true` is forward and `false` is backward. -/
def periodicLatticeStep {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (step : Fin 3 × Bool) : PeriodicLatticeSite L :=
  Function.update x step.1 (if step.2 then x step.1 + 1 else x step.1 - 1)

/-- Endpoint of a signed coordinate path. -/
def periodicPathEndpoint {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    List (Fin 3 × Bool) → PeriodicLatticeSite L
  | [] => x
  | step :: rest => periodicPathEndpoint (periodicLatticeStep x step) rest

/-- A nonempty closed coordinate path on the same periodic lattice used by the Wilson measure. -/
structure PeriodicLatticeLoop (L : PeriodicLatticeExtent) where
  base : PeriodicLatticeSite L
  steps : List (Fin 3 × Bool)
  nonempty : steps ≠ []
  closed : periodicPathEndpoint base steps = base

/-- Ordered group holonomy along a signed lattice path. -/
def periodicPathHolonomy {G : Type*} [Group G] {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration G L) :
    (x : PeriodicLatticeSite L) → List (Fin 3 × Bool) → G
  | _, [] => 1
  | x, step :: rest =>
      let next := periodicLatticeStep x step
      let factor := if step.2 then U (x, step.1) else (U (next, step.1))⁻¹
      factor * periodicPathHolonomy U next rest

/-- Holonomy of a closed periodic lattice loop. -/
def periodicLoopHolonomy {G : Type*} [Group G] {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration G L) (loop : PeriodicLatticeLoop L) : G :=
  periodicPathHolonomy U loop.base loop.steps

/-- Wilson plaquette energy `1 - (1/d) Re Tr ρ(U_∂p)`. For the campaign's defining SU(2)
representation `d=2`, this is exactly `1 - ½ Re Tr U_∂p`. -/
noncomputable def wilsonPlaquetteEnergy {G : Type*} [Group G] {d : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin d) ℂ) {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration G L) (p : PeriodicLatticePlaquette L) : ℝ :=
  1 - (Matrix.trace (ρ (periodicPlaquetteHolonomy U p)).1).re / d

/-- Wilson plaquette action on the canonical periodic cubic plaquette set. -/
noncomputable def wilsonLatticeAction {G : Type*} [Group G] {d : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin d) ℂ) {L : PeriodicLatticeExtent} (β : ℝ)
    (U : PeriodicLinkConfiguration G L) : ℝ :=
  β * ∑ p : PeriodicLatticePlaquette L, wilsonPlaquetteEnergy ρ U p

/-- Normalized Wilson-loop trace on a link configuration. -/
noncomputable def wilsonLoopValue {G : Type*} [Group G] {d : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin d) ℂ) {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration G L) (loop : PeriodicLatticeLoop L) : ℂ :=
  Matrix.trace (ρ (periodicLoopHolonomy U loop)).1 / d

/-- **F5 campaign lattice data.**

This is pinned to the campaign's actual finite-lattice object, not merely to a generic lattice label:

* `compute/phase1_est60_measurelayer/DERIVATION.md:40-50` gives the Wilson action and the finite
  periodic `T³` bond-space measure `μ_N` on `Q_N ≃ SU(2)^{B_N}`; lines 135-155 prove that the
  product-Haar Wilson density defines a Borel probability measure (near-definitional content).
* `compute/phase2_os2_latticerp/DERIVATION.md:36-44` fixes `d=3`, `G=SU(2)`, the exact four-link
  plaquette word, `β_N=4/(ag²)`, and `μ_N = Z⁻¹ exp(-S) ∏dU`; lines 271-283 state the banked
  even-time-extent link-reflection-positivity theorem. The present structure stores that measure
  object but does **not** yet store its link reflection/positive-half algebra, so it does not claim
  the RP theorem as a Lean field.
* `compute/phase2_prework_osaxioms/PREWORK.md:127-151` identifies lattice RP plus preservation under
  the `a→0` weak limit as the two OS2 links; this prework is explicitly scoping, not a proof.

Thus the fields below state required data and exact relationships on those campaign objects; they do
not construct an inhabitant or prove the weak limit exists. The representation dimension and Wilson
numerator remain abstract for the any-`G` Clay target, with the SU(2) values conditionally pinned by
`YangMillsContent.su2CampaignNormalization`.

Excluding non-simple compact groups beyond the current interface remains `G-LIE-SIMPLICITY` debt.
-/
structure WilsonLatticeData (G : Type g) [Group G] [TopologicalSpace G] where
  /-- Borel measurable structure used by Haar and finite product measures. -/
  [gaugeMeasurableSpace : MeasurableSpace G]
  [gaugeBorelSpace : BorelSpace G]
  /-- Dimension of the unitary representation used in the Wilson trace. -/
  representationDimension : ℕ
  representationDimension_positive : 0 < representationDimension
  /-- Matrix realization supplying the Wilson trace. -/
  matrixRepresentation : G →* Matrix.unitaryGroup (Fin representationDimension) ℂ
  matrixRepresentation_injective : Function.Injective matrixRepresentation
  matrixRepresentation_continuous : Continuous matrixRepresentation
  /-- Normalized Haar measure on the link group. -/
  haarMeasure : MeasureTheory.Measure G
  haarMeasure_probability : haarMeasure Set.univ = 1
  haarMeasure_left_invariant : ∀ g,
    MeasureTheory.Measure.map (fun h => g * h) haarMeasure = haarMeasure
  haarMeasure_right_invariant : ∀ g,
    MeasureTheory.Measure.map (fun h => h * g) haarMeasure = haarMeasure
  /-- Increasing periodic cubic cutoff geometry. -/
  extent : ℕ → PeriodicLatticeExtent
  extent_strictMono : ∀ μ, StrictMono (fun n => extent n μ)
  /-- Even temporal extent is the domain of the banked link-reflection-positivity result. -/
  timeExtent_even : ∀ n, Even (extent n 0 + 1)
  /-- Campaign dyadic spacing and Wilson coupling convention. -/
  latticeSpacing : ℕ → ℝ
  latticeSpacing_eq : ∀ n, latticeSpacing n = ((2 : ℝ) ^ n)⁻¹
  couplingSquared : ℝ
  couplingSquared_positive : 0 < couplingSquared
  wilsonBetaNumerator : ℝ
  wilsonBetaNumerator_positive : 0 < wilsonBetaNumerator
  wilsonBeta : ℕ → ℝ
  wilsonBeta_eq : ∀ n,
    wilsonBeta n = wilsonBetaNumerator /
      (latticeSpacing n * couplingSquared)
  /-- Probability measure on the canonical link-configuration space. -/
  latticeMeasure : ∀ n, MeasureTheory.Measure (PeriodicLinkConfiguration G (extent n))
  latticeMeasure_probability : ∀ n, latticeMeasure n Set.univ = 1
  /-- The associated measure is exactly product Haar tilted by the Wilson plaquette action. -/
  latticeMeasure_eq_wilson : ∀ n,
    latticeMeasure n =
      (MeasureTheory.Measure.pi (fun _ : PeriodicLatticeEdge (extent n) => haarMeasure)).tilted
        (fun U => -wilsonLatticeAction matrixRepresentation (wilsonBeta n) U)
  /-- The same measure is invariant under local link-gauge transformations. -/
  latticeMeasure_gauge_invariant : ∀ n (γ : PeriodicLatticeSite (extent n) → G),
    MeasureTheory.Measure.map (periodicGaugeTransform γ) (latticeMeasure n) = latticeMeasure n
  /-- Common M2 state space receiving every finite lattice. -/
  ContinuumState : Type g
  [continuumTopology : TopologicalSpace ContinuumState]
  [continuumMeasurableSpace : MeasurableSpace ContinuumState]
  [continuumBorelSpace : BorelSpace ContinuumState]
  latticeEmbedding : ∀ n, PeriodicLinkConfiguration G (extent n) → ContinuumState
  latticeEmbedding_measurable : ∀ n, Measurable (latticeEmbedding n)
  /-- The `RED-P-RP-CLOSED` weak-limit measure. Its existence is required, not proved here. -/
  weakLimitMeasure : MeasureTheory.Measure ContinuumState
  weakLimitMeasure_probability : weakLimitMeasure Set.univ = 1
  weakConvergence : ∀ F : BoundedContinuousFunction ContinuumState ℂ,
    Filter.Tendsto
      (fun n => ∫ x, F x ∂MeasureTheory.Measure.map (latticeEmbedding n) (latticeMeasure n))
      Filter.atTop (nhds (∫ x, F x ∂weakLimitMeasure))

/-- Expectation with respect to one exact Wilson cutoff measure. -/
noncomputable def WilsonLatticeData.cutoffExpectation
    {G : Type g} [Group G] [TopologicalSpace G] (data : WilsonLatticeData G) (n : ℕ)
    (F : PeriodicLinkConfiguration G (data.extent n) → ℂ) : ℂ := by
  letI := data.gaugeMeasurableSpace
  exact ∫ U, F U ∂data.latticeMeasure n

/-- The uniform fundamental-representation flux weight on a plaquette sheet, integrated against
product Haar without the Wilson density. At the SU(2), `d=2` staging instance this is exactly the
spin-half weight
`∫ ∏_{p∈S} χ_{1/2}(U_{∂p}) ∏_e dU_e`, the est29 object. -/
noncomputable def WilsonLatticeData.fundamentalFluxWeight
    {G : Type g} [Group G] [TopologicalSpace G] (data : WilsonLatticeData G) (n : ℕ)
    (S : PeriodicPlaquetteSheet (data.extent n)) : ℂ := by
  letI := data.gaugeMeasurableSpace
  exact ∫ U, ∏ p ∈ S,
    Matrix.trace (data.matrixRepresentation (periodicPlaquetteHolonomy U p)).1
    ∂MeasureTheory.Measure.pi
      (fun _ : PeriodicLatticeEdge (data.extent n) => data.haarMeasure)

/-- Expectation with respect to the banked weak-limit measure. -/
noncomputable def WilsonLatticeData.weakLimitExpectation
    {G : Type g} [Group G] [TopologicalSpace G] (data : WilsonLatticeData G)
    (F : data.ContinuumState → ℂ) : ℂ := by
  letI := data.continuumMeasurableSpace
  exact ∫ Φ, F Φ ∂data.weakLimitMeasure

/-- Finite complex linear combinations of Wilson loops on one cutoff lattice. These are the
Wilson-loop polynomial observables used for the anchoring channels. -/
abbrev WilsonLoopPolynomial {G : Type g} [Group G] [TopologicalSpace G]
    (data : WilsonLatticeData G) (n : ℕ) :=
  PeriodicLatticeLoop (data.extent n) →₀ ℂ

/-- Evaluation of a Wilson-loop polynomial on the same cutoff link configuration. -/
noncomputable def wilsonLoopPolynomialValue {G : Type g} [Group G] [TopologicalSpace G]
    (data : WilsonLatticeData G) (n : ℕ) (P : WilsonLoopPolynomial data n)
    (U : PeriodicLinkConfiguration G (data.extent n)) : ℂ :=
  P.sum fun loop coefficient => coefficient * wilsonLoopValue data.matrixRepresentation U loop

/-- **B5 shared gauge-content interface.**

The campaign lattice data, every finite-cutoff observable realization, the M2-limit realization,
and the continuum correlator now live on this one object. The Wilson and curvature bricks below
can no longer select unrelated families. The old infinite-range gate is retained and strengthened
by these exact typed links.

DECISION-STATUS: `PARTIALLY-SETTLED — REQUIREMENT SHAPE IN LEAN, UNPROSECUTED`.
-/
structure YangMillsContent
    (G : Type g) [Group G] [TopologicalSpace G] (Observable : Type x) where
  /-- The exact compact-simple candidate supplied to the any-`G` target. -/
  gaugeGroupData : CompactConnectedNonabelianGaugeGroupData G
  /-- The single campaign lattice/measure family shared by both B5 readings. -/
  latticeData : WilsonLatticeData G
  /-- Gauge action on the common observable carrier. -/
  gaugeAction : G →* Equiv.Perm Observable
  /-- **R3 anchor.** The gauge action must act nontrivially somewhere: some group element moves
  some observable. Blocks Sol K3's `trivializeGlobalGaugeAction`
  (`compute/SOL_GATE_CLAYSTATEMENT.md` §4.6), which replaced `gaugeAction` by the identity
  homomorphism (`1`) while retaining every lattice datum, cutoff observable, continuum observable,
  and correlator -- the whole gauge-symmetry structure disposed of at zero cost. A gauge SYMMETRY
  that acts trivially everywhere is not a symmetry of anything. -/
  gaugeAction_nontrivial : ∃ g : G, gaugeAction g ≠ 1
  /-- Common continuum correlator/expectation interface. -/
  correlator : Observable → ℂ
  /-- Gauge invariance of the correlator. -/
  gauge_invariant : ∀ (g : G) (O : Observable), correlator (gaugeAction g O) = correlator O
  /-- The SU(2) campaign specialization pins the defining two-dimensional representation scale
  and `β=4/(ag²)`. For non-SU(2) groups this conditional field is vacuous rather than imposing an
  SU(N)-specific normalization on the any-`G` target. -/
  su2CampaignNormalization :
    ∀ _e : G ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ,
      latticeData.representationDimension = 2 ∧ latticeData.wilsonBetaNumerator = 4
  /-- Realization of every shared observable on every exact cutoff link space. -/
  cutoffObservable : ∀ n, Observable →
    PeriodicLinkConfiguration G (latticeData.extent n) → ℂ
  /-- Cutoff realizations are invariant under local lattice gauge transformations. -/
  cutoffObservable_gauge_invariant : ∀ n O
    (γ : PeriodicLatticeSite (latticeData.extent n) → G) U,
      cutoffObservable n O (periodicGaugeTransform γ U) = cutoffObservable n O U
  /-- Realization of the same observable on the M2 weak-limit state space. -/
  continuumObservable : Observable → latticeData.ContinuumState → ℂ
  /-- Two observables have different correlators, excluding every constant one-state theory. -/
  nontriviality : ∃ O₁ O₂ : Observable, correlator O₁ ≠ correlator O₂
  /-- Genuine correlator richness is witnessed by pairwise-distinct Wilson-loop polynomials on one
  exact campaign cutoff, realized by shared observables whose continuum correlators are also
  pairwise distinct. Thus infinitude cannot be supplied by an unrelated injective label cast. -/
  correlator_range_infinite : ∃ (n : ℕ)
    (polynomial : ℕ → WilsonLoopPolynomial latticeData n) (observable : ℕ → Observable),
      Function.Injective polynomial ∧
      (∀ k U, cutoffObservable n (observable k) U =
        wilsonLoopPolynomialValue latticeData n (polynomial k) U) ∧
      Function.Injective (fun k => correlator (observable k))

/-- **B5-Wilson: campaign Wilson-lattice continuum-limit reading.**

The cutoff correlator is now definitionally constrained by the exact Wilson probability measure
stored in `content.latticeData`, and the shared continuum correlator is constrained to be the
expectation of the same observable under that object's `RED-P-RP-CLOSED` weak-limit measure.
The bank pins are exact and scope-limited:

* `compute/phase2_rpclosed/DERIVATION.md:50-88` proves that RP is closed under weak limits when the
  reflected pairings are bounded-continuous; this is the abstract `RED-P-RP-CLOSED` limit step.
* `compute/phase2_obscontinuity/DERIVATION.md:147-174` discharges bounded continuity for regularized
  Wilson loops and only that Wilson-loop half; lines 176-195 leave energy-observable RP OPEN.
* `compute/phase2_obscontinuity/DERIVATION.md:327-330` records the honest residuals: energy-sector RP
  and reflection matching. Consequently these fields do not claim the complete OS2 joint algebra.

`continuum_limit` is deliberately a theorem below, not independently supplied data: it is derived from
the stored bounded-continuous representative, lattice embedding, exact Wilson expectation, campaign
weak convergence, and exact weak-limit expectation. Existence and integrability remain requirements,
not claimed constructions.

DECISION-STATUS: `PARTIALLY-SETTLED — REQUIREMENT SHAPE IN LEAN, UNPROSECUTED`.
-/
structure WilsonLatticeContinuum
    {G : Type g} [Group G] [TopologicalSpace G] {Observable : Type x}
    (content : YangMillsContent G Observable) where
  /-- Cutoff/lattice correlators indexed by refinement level. -/
  cutoffCorrelator : ℕ → Observable → ℂ
  /-- The exact cutoff observable is integrable against the exact Wilson measure. -/
  cutoffObservable_integrable : ∀ n O, by
    letI := content.latticeData.gaugeMeasurableSpace
    exact MeasureTheory.Integrable (content.cutoffObservable n O)
      (content.latticeData.latticeMeasure n)
  /-- The continuum realization is genuinely bounded-continuous on the M2 weak-limit carrier. -/
  continuumObservable_boundedContinuous : ∀ O, by
    letI := content.latticeData.continuumTopology
    exact ∃ F : BoundedContinuousFunction content.latticeData.ContinuumState ℂ,
      (F : content.latticeData.ContinuumState → ℂ) = content.continuumObservable O
  /-- The cutoff realization is the pullback of that same continuum observable along the stored
  lattice embedding, so weak convergence applies to the observable rather than an unrelated test. -/
  cutoffObservable_eq_latticeEmbedding : ∀ n O U,
    content.cutoffObservable n O U =
      content.continuumObservable O (content.latticeData.latticeEmbedding n U)
  /-- No floating cutoff family: each value is the Wilson-measure expectation. -/
  cutoffCorrelator_eq_latticeExpectation : ∀ n O,
    cutoffCorrelator n O = content.latticeData.cutoffExpectation n
      (content.cutoffObservable n O)
  /-- The M2-state realization is integrable against the `RED-P-RP-CLOSED` limit measure. -/
  continuumObservable_integrable : ∀ O, by
    letI := content.latticeData.continuumMeasurableSpace
    exact MeasureTheory.Integrable (content.continuumObservable O)
      content.latticeData.weakLimitMeasure
  /-- No floating continuum object: the target correlator is the weak-limit expectation. -/
  correlator_eq_rpClosedWeakLimit : ∀ O,
    content.correlator O = content.latticeData.weakLimitExpectation
      (content.continuumObservable O)
  /-- At least one observable is represented at every cutoff by a Wilson-loop polynomial on the
  stored lattice family and has genuine cutoff dependence at arbitrarily fine levels. The
  polynomial family makes the dependence provenance explicit rather than permitting a floating
  numerical perturbation. -/
  genuine_cutoff_dependence : ∃ (O : Observable)
    (polynomial : ∀ n, WilsonLoopPolynomial content.latticeData n),
      (∀ n U, content.cutoffObservable n O U =
        wilsonLoopPolynomialValue content.latticeData n (polynomial n) U) ∧
      ∀ N : ℕ, ∃ n : ℕ,
        N ≤ n ∧ cutoffCorrelator n O ≠ content.correlator O

/-- The continuum limit is forced by the campaign-pinned weak-convergence chain; it is not a second,
caller-selected convergence certificate. This theorem consumes exactly the `C_b` hypothesis banked by
`RED-P-RP-CLOSED` and the Wilson-observable half of `RED-P-OS2-OBSCONTINUITY`.

DECISION-STATUS: `VERIFIED-SCOPED` as a Lean consequence of the requirement fields. It does not prove
that an inhabitant exists, and it does not repair the convicted B4 `OSAxioms` architecture. -/
theorem WilsonLatticeContinuum.continuum_limit
    {G : Type g} [Group G] [TopologicalSpace G] {Observable : Type x}
    {content : YangMillsContent G Observable} (wilson : WilsonLatticeContinuum content)
    (O : Observable) :
    Filter.Tendsto (fun n : ℕ => wilson.cutoffCorrelator n O) Filter.atTop
      (nhds (content.correlator O)) := by
  letI := content.latticeData.gaugeMeasurableSpace
  letI := content.latticeData.continuumTopology
  letI := content.latticeData.continuumMeasurableSpace
  letI := content.latticeData.continuumBorelSpace
  obtain ⟨F, hF⟩ := wilson.continuumObservable_boundedContinuous O
  have hweak := content.latticeData.weakConvergence F
  have hcutoff : ∀ n, wilson.cutoffCorrelator n O =
      ∫ x, F x ∂MeasureTheory.Measure.map
        (content.latticeData.latticeEmbedding n) (content.latticeData.latticeMeasure n) := by
    intro n
    rw [wilson.cutoffCorrelator_eq_latticeExpectation, WilsonLatticeData.cutoffExpectation]
    rw [MeasureTheory.integral_map (content.latticeData.latticeEmbedding_measurable n).aemeasurable
      F.continuous.aestronglyMeasurable]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with U
    rw [wilson.cutoffObservable_eq_latticeEmbedding]
    exact (congrFun hF (content.latticeData.latticeEmbedding n U)).symm
  have hlimit : content.correlator O = ∫ x, F x ∂content.latticeData.weakLimitMeasure := by
    rw [wilson.correlator_eq_rpClosedWeakLimit, WilsonLatticeData.weakLimitExpectation]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with Φ
    rw [hF]
  simpa only [hcutoff, hlimit] using hweak

/-- **B5-curvature: Wilson-loop-generated gauge-invariant correlator inputs.**

**R6 RENAME (2026-07-21), honesty obligation not cosmetics.** Sol K3's de-correlated re-gate
(`compute/SOL_GATE_COERCIVITY_AND_RENAME.md` §3.4, verdict "CONVICTED on 'Curvature'") proved that
gauge invariance and the correlator ties in this structure are real, and Wilson-loop polynomial
semantics are genuinely delivered -- but **no field anywhere names a local curvature operator `F`,
a covariant derivative, a small-loop/local-curvature limit, an area-law predicate, or a
spin/parity channel-projection operation.** `curvatureObservables` is a bare designated `Set
Observable`; the docstring below already disclosed this (`OPEN construction debt`), but the old
name `GaugeInvariantCurvatureCorrelators` still claimed "Curvature" as delivered content. Renamed
to `GaugeInvariantWilsonLoopCorrelatorInputs`, scoped exactly to what the fields deliver: a
gauge-invariant family of Wilson-loop-POLYNOMIAL-labeled correlator inputs, distinct and nonzero,
not yet a local curvature reading. See `Target/prosecution/NAME_SWEEP_VERIFY.lean` §4 for the
independent field-by-field re-derivation (grep-confirmed: no `curvatureOperator`,
`covariantDerivative`, `smallLoop`, `areaLaw`, or `fieldStrength` identifier occurs anywhere in
this file).

The designated family must contain every supplied Wilson-loop polynomial on the exact same
`content.latticeData` link spaces. This is as far as the bank honestly reaches:

* `compute/phase2_prework_osaxioms/PREWORK.md:38-52` selects regularized Wilson loops plus smoothed
  gauge-invariant local functions as the campaign observable algebra, while explicitly flagging
  definitional faithfulness as unresolved.
* `compute/phase2_obscontinuity/DERIVATION.md:147-174` supplies continuity/boundedness for regularized
  Wilson loops, not numerical string-tension or glueball values.
* `compute/phase1_est55_loopcore/DERIVATION.md:8-14,72-99` supplies exact finite-lattice SU(2)
  recoupling/loop-flux computations, but explicitly leaves the large-β enclosure OPEN; lines 108-120
  likewise leave the general loop-flux sign and large-β construction open.

The ledger search found no banked artifact constructing the three named string-tension/scalar/tensor
families as continuum observables or extracting their values. Accordingly the three fields below remain
nonzero **input candidates only**. Increasing area, channel projection/distinctness, local-curvature
small-loop semantics, decay, and benchmark extraction are OPEN construction debt; no false pin is made.

DECISION-STATUS: `PARTIALLY-SETTLED — REQUIREMENT SHAPE IN LEAN, UNPROSECUTED`.
-/
structure GaugeInvariantWilsonLoopCorrelatorInputs
    {G : Type g} [Group G] [TopologicalSpace G] {Observable : Type x}
    (content : YangMillsContent G Observable) where
  /-- Observables designated as gauge-invariant curvature polynomials. -/
  curvatureObservables : Set Observable
  /-- The designated family is stable under the common gauge action. -/
  gauge_stable : ∀ g O, O ∈ curvatureObservables →
    content.gaugeAction g O ∈ curvatureObservables
  /-- A curvature observable has a genuinely nonzero shared correlator. -/
  nontrivial_curvature : ∃ O ∈ curvatureObservables, content.correlator O ≠ 0
  /-- Every finite Wilson-loop polynomial has an observable in the shared carrier. -/
  wilsonLoopPolynomialObservable : ∀ n,
    WilsonLoopPolynomial content.latticeData n → Observable
  /-- Those loop-polynomial observables belong to the designated curvature family. -/
  wilsonLoopPolynomial_mem_curvature : ∀ n P,
    wilsonLoopPolynomialObservable n P ∈ curvatureObservables
  /-- They are fixed by the same gauge action used by the shared correlator. -/
  wilsonLoopPolynomial_gauge_fixed : ∀ g n P,
    content.gaugeAction g (wilsonLoopPolynomialObservable n P) =
      wilsonLoopPolynomialObservable n P
  /-- Their cutoff semantics is the normalized trace of holonomy on the same links. -/
  wilsonLoopPolynomial_semantics : ∀ n P U,
    content.cutoffObservable n (wilsonLoopPolynomialObservable n P) U =
      wilsonLoopPolynomialValue content.latticeData n P U
  /-- Curvature infinitude is supplied by pairwise-distinct Wilson-loop polynomials at one exact
  campaign cutoff whose realized shared observables are pairwise distinct. An arbitrary infinite
  set, including `Set.univ`, is not by itself a curvature-content certificate. -/
  curvatureObservables_infinite : ∃ (n : ℕ)
    (polynomial : ℕ → WilsonLoopPolynomial content.latticeData n),
      Function.Injective polynomial ∧
      Function.Injective (fun k => wilsonLoopPolynomialObservable n (polynomial k))
  /-- Nonzero Wilson-loop-polynomial input candidate for a future large-area/string-tension
  construction; no area-law property is asserted here. -/
  stringTensionWilsonInput : ∀ n, WilsonLoopPolynomial content.latticeData n
  stringTensionWilsonInput_nonzero : ∀ n, stringTensionWilsonInput n ≠ 0
  /-- Input candidate for a future scalar `0⁺⁺` channel projection and decay construction. -/
  scalarGlueballWilsonInput : ∀ n, WilsonLoopPolynomial content.latticeData n
  scalarGlueballWilsonInput_nonzero : ∀ n, scalarGlueballWilsonInput n ≠ 0
  /-- Input candidate for a future tensor `2⁺⁺` projection paired with the scalar input. -/
  tensorGlueballWilsonInput : ∀ n, WilsonLoopPolynomial content.latticeData n
  tensorGlueballWilsonInput_nonzero : ∀ n, tensorGlueballWilsonInput n ≠ 0
  /-- **R3 anchor.** The three named physical channels must be genuinely distinct, at some shared
  cutoff `n`. Blocks Sol K3's `collapseAdvertisedChannels`
  (`compute/SOL_GATE_CLAYSTATEMENT.md` §4.9), which set `scalarGlueballWilsonInput` and
  `tensorGlueballWilsonInput` definitionally EQUAL to `stringTensionWilsonInput` (proved by `rfl`)
  -- no area growth, spin/parity projection, or decay content was required, so three names could
  point at one polynomial. Distinctness alone does not supply the physical channel content
  (area-law, `0⁺⁺`/`2⁺⁺` projection) -- that remains the disclosed open construction debt -- but it
  does exclude the collapse. -/
  channels_pairwise_distinct : ∃ n,
    stringTensionWilsonInput n ≠ scalarGlueballWilsonInput n ∧
    stringTensionWilsonInput n ≠ tensorGlueballWilsonInput n ∧
    scalarGlueballWilsonInput n ≠ tensorGlueballWilsonInput n

/-- The bundle of B1--B5 instances for one supplied gauge-group carrier.

**R6 RENAME (2026-07-21), honesty obligation not cosmetics.** Sol K3's de-correlated re-gate
(`compute/SOL_GATE_COERCIVITY_AND_RENAME.md` §3.4, verdict "CONVICTED on name") proved that this
structure stores B1--B5 records side by side with **no OS reconstruction, no analytic
continuation, and no equality tying the Minkowski (`poincareRepresentation`,
`operatorValuedDistribution`, `spectrumCondition`, `massGap`) and Euclidean/lattice (`osAxioms`,
`yangMillsContent`, `wilsonLatticeContinuum`, `curvatureCorrelators`) halves into one theory.**
Renamed from `YangMillsTheoryPackage` to `YangMillsBrickBundle`: "Theory Package" claims coherence
this record does not deliver; "brick bundle" claims exactly what is here -- a bundle of the
separately-tracked bricks, indexed by the same `gaugeGroup`.
`Target/prosecution/NAME_SWEEP_VERIFY.lean` §3 gives the machine-checked demonstration:
`yangMillsTheoryPackage_decouples` swaps the entire
Euclidean/lattice half for an UNRELATED instance on a DIFFERENT carrier type `D'` while the
Minkowski half stays untouched, and it still typechecks -- proving no bridging equation exists
anywhere beyond `yangMillsContent_gaugeGroupData` (which ties only the gauge-group DATA, not the
Hilbert-space/measure-space carriers or any of the four B1--B3 fields to the four B4--B5 fields).
This is the same defect the `ClayYangMillsPartialSkeleton*` R4 rename already named one level up
(`CROSS-BRICK-COHERENCE`); it had not yet been applied to this inner structure's own name.

The spectrum brick is indexed by the exact Poincaré representation instance, and the two B5
bricks are indexed by the exact shared Yang--Mills content instance. This removes the v1 drift in
which independent `Nonempty` witnesses could describe unrelated theories. Full OS reconstruction
and remaining covariance links are explicitly tracked by `CROSS-BRICK-COHERENCE`.

**R2 (2026-07-21): `P` is FIXED to `PoincareGroup4`, not existentially quantified.**
Two independent statement prosecutions (`compute/prosecution/PROS_CLAYSTATEMENT_REPAIR.md`,
CONVICTED; `compute/KIMI_GATE_CLAYSTATEMENT.md`, QUALIFIED-RELOCATED with a machine-checked
exploit) proved that quantifying `(P : Type v) (_ : Group P) (_ : TopologicalSpace P)
(_ : MulAction P Spacetime4)` existentially, in the SAME witness as `physicalGroupEquiv`, defeats
the F2 anti-degeneracy anchor: `mulActionOfEquiv e` (defined above `PoincareRepresentation`)
manufactures a matching `[MulAction P Spacetime4]` instance for ANY `e`, so the "pin" never
constrains anything the witness-builder did not already choose. Fixing `P := PoincareGroup4` with
the ALREADY-REGISTERED global instance `poincareGroupActMulAction` (found by ordinary Lean
typeclass search, never supplied as witness data) makes `physicalGroupEquiv_eq_refl_of_canonical`
the target-level content: `physicalGroupEquiv` is forced to `MulEquiv.refl`, with no exploitable
freedom left. `[TopologicalSpace PoincareGroup4]` remains existentially quantified below -- an
honest, UNCHANGED-IN-STATUS open item (`B2A-TOPOLOGICAL-COMPATIBILITY`; no such instance is
registered anywhere in this file), not newly introduced by R2 and not what either prosecution
convicted.

DECISION-STATUS: `PARTIALLY-SETTLED`.
-/
structure YangMillsBrickBundle
    (G : Type g) [Group G] [TopologicalSpace G]
    (gaugeGroup : CompactConnectedNonabelianGaugeGroupData G)
    (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [TopologicalSpace PoincareGroup4]
    (D : Type w) [MeasurableSpace D]
    (Observable : Type x) where
  poincareRepresentation : PoincareRepresentation PoincareGroup4 ℋ
  operatorValuedDistribution : OperatorValuedDistribution ℋ poincareRepresentation
  spectrumCondition : SpectrumCondition poincareRepresentation
  massGap : MassGap spectrumCondition
  osAxioms : OSAxioms D
  yangMillsContent : YangMillsContent G Observable
  yangMillsContent_gaugeGroupData : yangMillsContent.gaugeGroupData = gaugeGroup
  wilsonLatticeContinuum : WilsonLatticeContinuum yangMillsContent
  curvatureCorrelators : GaugeInvariantWilsonLoopCorrelatorInputs yangMillsContent

/-- **R4 RENAME (2026-07-21), honesty obligation not cosmetics.** This declaration and its two
siblings below (`ClayYangMillsPartialSkeleton`, `ClayYangMillsPartialSkeleton_SU2`) were named
`ClayYangMillsFor`/`ClayYangMills`/`ClayYangMills_SU2` through R3. Sol K3's de-correlated re-gate
(`compute/SOL_GATE_CLAYSTATEMENT_R3.md`, verdict QUALIFIED, §6/§10) proved that name was a
material misrepresentation: the declaration sits immediately after a verbatim Jaffe--Witten
quotation while its formal type is materially weaker. The renamed family makes explicit, in the
name itself, that this is a **partial statement skeleton**, not the Clay problem. The quotation
below is retained strictly as **PROVENANCE** (what the eventual target must state), never as a
claim that this `Prop` states it.

**Fidelity checklist (Sol's gate-3/gate-4 table, `compute/SOL_GATE_CLAYSTATEMENT_R3.md` §6,
reproduced here as the standing checklist for whoever next touches this brick).** This type does
**NOT** require:

| requirement (Jaffe--Witten's actual problem) | status in this `Prop` |
|---|---|
| OS reconstruction joining Euclidean, Minkowski, and lattice data into ONE theory | **absent** -- `YangMillsBrickBundle` merely stores independent records side by side; no reconstruction map/equality/analytic continuation exists anywhere in the tree (`Spine.lean` confirms no bridge theorem is even stated, "Finding 4") |
| vacuum invariance under the representation, and uniqueness up to phase | **absent** |
| a genuine PVM / physical unbounded Hamiltonian (only a bounded self-adjoint surrogate family, `SpectrumCondition.translationGenerators`) | **absent**; tracked `B2B-JOINT-PVM` |
| locality / microcausality (spacelike operator commutativity) | **absent** -- `OperatorValuedDistribution` has domain, continuity, closability, covariance, but no commutation-at-spacelike-separation field |
| local gauge-invariant curvature-operator correspondence (an actual local `F`/covariant-derivative operator, small-loop local-curvature semantics) | **absent** -- `GaugeInvariantWilsonLoopCorrelatorInputs` only makes three named Wilson-input channels pairwise distinct and nonzero |
| short-distance asymptotic freedom, perturbative renormalization, OPE, stress tensor | **absent entirely** |
| a genuine compact **simple** Lie group (this file quantifies over `CompactConnectedNonabelianGaugeGroupData` — R5-renamed to state exactly what it enforces: compact, connected, nonabelian; it excludes finite carriers AND abelian carriers via `not_commutative`, but still has no Lie-manifold structure and no group-theoretic simplicity predicate, and its name no longer claims otherwise) | **absent** -- see that structure's own docstring (`G-LIE-SIMPLICITY`) |
| a 4D target | **NOT what the campaign's own lattice construction provides**: `PeriodicLatticeExtent := Fin 3 → ℕ` is the exact carrier used campaign-wide; no 3D-to-4D bridge exists in this file or `Spine.lean` |

Every one of these is either a large separate construction program (tracked in `TARGET_BURNDOWN.md`
and the residual register) or, for the gauge-group brick, partially addressed here in R4. **A
comment saying "partial" does not repair what a strong name causes downstream readers to cite** --
Sol's finding, acted on by this rename.

---

The target package for one compact-simple gauge-group candidate.

This is a target `def : Prop`, not a theorem. The group certificate is a future brick instance,
not a caller-selected proposition. Both B5 readings are conjoined inside one
`YangMillsBrickBundle`.

**R2**: `P` is no longer part of this existential (see `YangMillsBrickBundle`'s docstring); the
Poincaré carrier is fixed to `PoincareGroup4` with its canonical, globally-resolved action.

DECISION-STATUS: `PARTIALLY-SETTLED`.
-/
def ClayYangMillsPartialSkeletonFor
    (G : Type g) [Group G] [TopologicalSpace G]
    (gaugeGroup : CompactConnectedNonabelianGaugeGroupData G) : Prop :=
  ∃ (ℋ : Type u) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
    (_ : CompleteSpace ℋ) (_ : TopologicalSpace PoincareGroup4)
    (D : Type w) (_ : MeasurableSpace D) (Observable : Type x),
      Nonempty (YangMillsBrickBundle G gaugeGroup ℋ D Observable)

/-- **A PARTIAL statement skeleton toward the general Clay Yang--Mills target -- NOT the Clay
problem itself.** See `ClayYangMillsPartialSkeletonFor`'s docstring (R4 rename rationale + the
fidelity checklist naming everything this `Prop` does NOT require) immediately above.

Verbatim pinned theorem statement, quoted here as **PROVENANCE ONLY** -- this `Prop` is materially
weaker than the following paragraph and must never be cited as though it stated it
(Jaffe--Witten, extracted lines 277--280):

> **Yang–Mills Existence and Mass Gap.** Prove that for any compact simple gauge
> group G, a non-trivial quantum Yang–Mills theory exists on R4 and has a mass gap
> ∆ > 0. Existence includes establishing axiomatic properties at least as strong as
> those cited in [45, 35].

The quantifier is deliberately **ANY-G**: every carrier equipped with the compact-simple group
brick must receive a theory package. This is the NO-HOLES-law dominance resolution and the actual
L4 target. The unresolved Lie-theoretic content of that brick is tracked by `G-LIE-SIMPLICITY`;
it is not a proposition selected by a theory-package instantiator.

DECISION-STATUS: `PARTIALLY-SETTLED` (ANY-G scope is `SETTLED-BY-LITERATURE`; brick content
remains).
-/
def ClayYangMillsPartialSkeleton : Prop :=
  ∀ (G : Type g) (_ : Group G) (_ : TopologicalSpace G)
    (gaugeGroup : CompactConnectedNonabelianGaugeGroupData G),
      ClayYangMillsPartialSkeletonFor.{g, u, w, x} G gaugeGroup

/-- Campaign SU(2) staging statement, explicitly **not** the general Clay target and **not** the
Clay problem itself -- see `ClayYangMillsPartialSkeletonFor`'s docstring for the R4 rename
rationale and full fidelity checklist.

Verbatim source scope fragment, quoted as **PROVENANCE ONLY** (Jaffe--Witten, extracted lines
277--280):

> Prove that for any compact simple gauge
> group G, a non-trivial quantum Yang–Mills theory exists on R4 and has a mass gap
> ∆ > 0.

Mathlib's `Matrix.specialUnitaryGroup (Fin 2) ℂ` supplies the concrete SU(2) carrier. This says
that suitable gauge-group data and its fixed-group package exist. It is an instance/staging goal
for the any-G target, not a replacement or weakening of `ClayYangMillsPartialSkeleton`.

DECISION-STATUS: `CAMPAIGN-STAGING`.

**NON-VACUITY, CLOSED 2026-07-21.** Sol's re-gate
(`compute/SOL_GATE_COERCIVITY_AND_RENAME.md` §3.2) established that this existential had never been
shown to range over an inhabited type: no in-tree `CompactConnectedNonabelianGaugeGroupData SU(2)`
existed, and the direct construction failed at four unmet Mathlib obligations (`CompactSpace`,
`ContinuousInv`, `Nontrivial`, `PreconnectedSpace`). **All four are now closed genuinely** —
`AdalyFormal.Target.SU2Instance.su2InstanceData`, axiom-clean, no `sorry`, with preconnectedness via
a two-sided Cayley–Klein `S³ ≃ SU(2)` image equality. See
`AdalyFormal.Target.SU2Instance.su2GaugeGroupData_nonempty` for the witness theorem. (No import is
added here: `SU2Instance.lean` imports THIS file, so the reverse edge would be circular — hence a
pointer rather than an in-file theorem.)

**This closes the group-data half ONLY.** The second conjunct, `ClayYangMillsPartialSkeletonFor`
(i.e. `Nonempty (YangMillsBrickBundle ...)`), remains wide open, so this `def` is NOT proved.
-/
def ClayYangMillsPartialSkeleton_SU2 : Prop :=
  ∃ gaugeGroup : CompactConnectedNonabelianGaugeGroupData (Matrix.specialUnitaryGroup (Fin 2) ℂ),
    ClayYangMillsPartialSkeletonFor.{0, 0, 0, 0} (Matrix.specialUnitaryGroup (Fin 2) ℂ) gaugeGroup

/-- Later-batch statement stub: the generic B1/B2b Wightman requirement shapes are jointly
inhabited for some Poincaré representation. It is a target proposition, not a proof or scalar
construction.

**R6 RENAME (2026-07-21), honesty obligation not cosmetics.** Sol K3's de-correlated re-gate
(`compute/SOL_GATE_COERCIVITY_AND_RENAME.md` §3.4, verdict "CONVICTED") proved that this `Prop`
asks only for an arbitrary Hilbert space, a Poincaré representation, an
`OperatorValuedDistribution`, and a `SpectrumCondition`. **No field says free, scalar,
Gaussian/quasi-free, or Klein--Gordon/equation-of-motion, and it does not even select a scalar
(as opposed to vector or higher-spin) field species.** Renamed from
`FreeScalarField_satisfies_Wightman` to `WightmanRequirementShapes_exist`: it states that SOME
instance of the generic B1+B2b requirement shapes exists, not that a free scalar field has been
constructed. `Target/prosecution/NAME_SWEEP_VERIFY.lean` §2 gives the machine-checked
demonstration (`freeScalarField_decouples`/`freeScalarField_decouples_other_direction`): the exact
same field-operator instance can be paired with an arbitrary, UNRELATED spectrum instance on the
same representation, and vice versa -- proving no dispersion-relation-style equation ties the two
halves together, so nothing here pins down "the" free scalar field (or any specific field at all)
even up to the choice of `rep`. Constructing a genuine free-scalar (or any) inhabitant of this
`Prop` remains the separately-tracked `ADEQUACY-SANITY-INSTANCES` open item.

**R2**: `P` is fixed to `PoincareGroup4`, matching `ClayYangMillsPartialSkeletonFor` -- see that
def's docstring and `YangMillsBrickBundle`'s for why the pre-R2 existential over
`P`/`Group P`/`TopologicalSpace P`/`MulAction P Spacetime4` defeated the F2 anti-degeneracy anchor.

DECISION-STATUS: `PARTIALLY-SETTLED`.
-/
def WightmanRequirementShapes_exist : Prop :=
  ∃ (ℋ : Type u) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
    (_ : CompleteSpace ℋ) (_ : TopologicalSpace PoincareGroup4)
    (rep : PoincareRepresentation PoincareGroup4 ℋ),
      Nonempty (OperatorValuedDistribution ℋ rep) ∧ Nonempty (SpectrumCondition rep)

/-- A real theorem: a constant correlator cannot satisfy B5 non-triviality.

This rejects both the identically-zero candidate and the singleton/identity-only constant-one
candidate. It replaces v1's unproved proposition stub by a proof against the actual redesigned
field.

DECISION-STATUS: `PARTIALLY-SETTLED` (it rejects this degenerate theory; full adequacy is deferred).
-/
theorem TrivialTheory_fails_NonTriviality
    {G : Type g} [Group G] [TopologicalSpace G] {Observable : Type x}
    (content : YangMillsContent G Observable) (c : ℂ)
    (hconstant : content.correlator = fun _ => c) : False := by
  obtain ⟨O₁, O₂, hne⟩ := content.nontriviality
  apply hne
  simp [hconstant]

/-- Later-batch statement stub, ORIGINALLY intended to connect a lattice reflection-positivity
artifact to the actual B4 reflection-positivity form. This target proposition proves neither the
lattice result nor OS reconstruction.

**R6 RENAME (2026-07-21), honesty obligation not cosmetics.** Sol K3's de-correlated re-gate
(`compute/SOL_GATE_COERCIVITY_AND_RENAME.md` §3.4, verdict "CONVICTED -- the strongest [conviction
in the sweep]") proved in Lean (`latticeRP_stub_iff_exists_OSAxioms`) that this `Prop` is exactly
equivalent to the mere existence of an `OSAxioms` record: its displayed nonnegativity conclusion is
already `os.reflection_positive(...).2`, one field `OSAxioms` already requires. **It contains no
lattice datum, no link reflection, no lattice measure, and no bridge** -- `OSAxioms`'s own field
list (immediately above, `ClayStatement.lean:1028-1120`) never mentions `WilsonLatticeData`, a
link, or a plaquette either. Renamed from `LatticeRP_satisfies_OS_RP_form` to
`OSAxiomsReflectionPositivityStub`: the old name asserted a lattice-to-OS bridge result the fields
never built; the new name states plainly that this is a `OSAxioms`-only restatement stub, matching
`TARGET_BURNDOWN.md`'s own `ADEQUACY-SANITY-INSTANCES` row, which already called it "only an
abstract target stub" before this rename made the declaration's name agree.
`Target/prosecution/NAME_SWEEP_VERIFY.lean` §1 reproduces and extends Sol's equivalence
independently, with an OPS-3 mutation record showing the equivalence is forced by the exact field
shape, not a vacuous `True`/`rfl` collapse. The actual lattice-to-OS bridge (a typed link-midplane
measurable involution and the positive-half Wilson observable submodule on `WilsonLatticeData`)
remains the separately-tracked, highest-value `ADEQUACY-SANITY-INSTANCES` open item.

DECISION-STATUS: `PARTIALLY-SETTLED`.
-/
def OSAxiomsReflectionPositivityStub : Prop :=
  ∃ (D : Type u) (_ : MeasurableSpace D) (os : OSAxioms D),
    ∀ F ∈ os.positiveTimeObservables,
      0 ≤ Complex.re (∫ x, star (F (os.reflection x)) * F x ∂os.euclideanMeasure)

#print axioms Spacetime4
#print axioms SpatialIndex
#print axioms ForwardLightCone
#print axioms MinkowskiQuadraticForm
#print axioms minkowskiQuadraticForm_apply
#print axioms MinkowskiIsometryGroup
#print axioms minkowskiIsometryMulDistribMulAction
#print axioms minkowskiIsometryAction
#print axioms PoincareGroup4
#print axioms poincareGroup4_nontrivial
#print axioms EuclideanQuadraticForm
#print axioms euclideanQuadraticForm_apply
#print axioms EuclideanIsometryGroup
#print axioms euclideanIsometryMulDistribMulAction
#print axioms euclideanIsometryAction
#print axioms EuclideanGroup4
#print axioms euclideanTranslation
#print axioms euclideanGroupAct
#print axioms SpatialVector3
#print axioms spatialEmbed
#print axioms euclideanSpatialTranslation
#print axioms euclideanTimeReflectionLinearMap
#print axioms euclideanTimeReflection_involutive
#print axioms EuclideanTimeReflectionLinearEquiv
#print axioms EuclideanTimeReflectionIsometry
#print axioms EuclideanTimeReflection
#print axioms euclideanTimeReflection_ne_one
#print axioms euclideanGroup4_nontrivial
#print axioms CoordinateSpectrum
#print axioms poincareGroupActMulAction
#print axioms poincareGroupAct_injective
#print axioms PoincareRepresentation
#print axioms PoincareRepresentation.representation_injective
#print axioms PoincareRepresentation.physicalGroupEquiv_forced
#print axioms mulActionOfEquiv
#print axioms physicalGroupEquiv_spacetime_compatible_of_pullback
#print axioms physicalGroupEquiv_eq_refl_of_canonical
#print axioms poincareGroupAct
#print axioms poincareSchwartzPullback
#print axioms poincareSchwartzPullback_apply
#print axioms poincareSchwartzMulAction
#print axioms poincare_smul_schwartz_apply
#print axioms invariantDomainOperator
#print axioms OperatorValuedDistribution
#print axioms SpectrumCondition
#print axioms energyGenerator_spectrum_nonnegative
#print axioms MassGap
#print axioms MassGap.hamiltonian_selfAdjoint
#print axioms SchwingerTestFunction
#print axioms SchwingerMomentIntegral
#print axioms SchwingerMoment
#print axioms SchwingerBoundCertificate
#print axioms OSITemperedGrowth
#print axioms SchwingerBoundCertificate.osITemperedGrowth
#print axioms FactorialGrowth
#print axioms OSIICorrectedGrowth
#print axioms HasPositiveEuclideanTimeSupport
#print axioms PositiveTimeSchwingerTest
#print axioms SchwingerObservableRealization
#print axioms SchwingerObservableRealization.generatorSet
#print axioms OSPrimaryReflectionPositive
#print axioms OSAxioms
#print axioms CompactConnectedNonabelianGaugeGroupData
#print axioms CompactConnectedNonabelianGaugeGroupData.infinite
#print axioms CompactConnectedNonabelianGaugeGroupData.not_commGroup
#print axioms PeriodicLatticeExtent
#print axioms PeriodicLatticeSite
#print axioms PeriodicLatticeEdge
#print axioms PeriodicPlaquetteDirections
#print axioms PeriodicLatticePlaquette
#print axioms PeriodicPlaquetteSheet
#print axioms PeriodicLinkConfiguration
#print axioms periodicLatticeShift
#print axioms periodicPlaquetteHolonomy
#print axioms periodicPlaquetteBoundaryEdges
#print axioms IsClosedPeriodicPlaquetteSheet
#print axioms periodicGaugeTransform
#print axioms periodicLatticeStep
#print axioms periodicPathEndpoint
#print axioms PeriodicLatticeLoop
#print axioms periodicPathHolonomy
#print axioms periodicLoopHolonomy
#print axioms wilsonPlaquetteEnergy
#print axioms wilsonLatticeAction
#print axioms wilsonLoopValue
#print axioms WilsonLatticeData
#print axioms WilsonLatticeData.cutoffExpectation
#print axioms WilsonLatticeData.fundamentalFluxWeight
#print axioms WilsonLatticeData.weakLimitExpectation
#print axioms WilsonLoopPolynomial
#print axioms wilsonLoopPolynomialValue
#print axioms YangMillsContent
#print axioms WilsonLatticeContinuum
#print axioms WilsonLatticeContinuum.continuum_limit
#print axioms GaugeInvariantWilsonLoopCorrelatorInputs
#print axioms YangMillsBrickBundle
#print axioms ClayYangMillsPartialSkeletonFor
#print axioms ClayYangMillsPartialSkeleton
#print axioms ClayYangMillsPartialSkeleton_SU2
#print axioms WightmanRequirementShapes_exist
#print axioms TrivialTheory_fails_NonTriviality
#print axioms OSAxiomsReflectionPositivityStub

end AdalyFormal.Target.ClayStatement
