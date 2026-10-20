import AdalyFormal.Target.ClayStatement

/-!
# `Lattice.Witness` — an inhabitant of the periodic-cubic lattice gauge layer

`Target/ClayStatement.lean` states the campaign's full lattice-gauge-theory *requirement shape*
(`PeriodicLatticeSite`/`Edge`/`Plaquette`, `periodicPlaquetteHolonomy`, `periodicGaugeTransform`,
`wilsonPlaquetteEnergy`, `wilsonLatticeAction`, and the much larger `WilsonLatticeData` measure
package) but constructs **no inhabitant anywhere in the tree** — a definition with no witness is
unproved satisfiable (L7 witness debt, Phase-0 REFORM_PROGRAM mandate).

This module discharges that debt for the **concrete, computable lattice-geometry layer**: sites,
links, plaquettes, holonomy, gauge transforms, and the Wilson action formula, on the smallest
periodic extent the definitions admit without degenerating, over the campaign's SU(2) gauge group.
It does **not** attempt an inhabitant of `WilsonLatticeData` itself: that structure additionally
requires a Haar-tilted probability measure, gauge invariance of that measure, and a weak-limit
carrier whose *existence* is the still-open thermodynamic-limit construction flagged by
`compute/RESIDUAL_REGISTER.md`/`PHASE0_DEFS_PLAN.md` §3 (B2/C1/C2) — building that honestly is a
separate, much larger lane, not a witness-instance exercise. See `LATTICE_WITNESS_REPORT.md` §4 for
the precise scoping boundary and why it is drawn there.

## What is proved here

1. **General theorems** (hold for every group `G`, every periodic extent `L`, every unitary
   representation `ρ`, every gauge transform `γ` — not merely the witness):
   * `periodicLatticeShift_comm` — shifts in two distinct coordinate directions commute.
   * `periodicPlaquetteHolonomy_gaugeTransform` — plaquette holonomy transforms by conjugation at
     the plaquette's base site under a gauge transform (the standard lattice-gauge-theory fact
     underlying Wilson-action gauge invariance).
   * `periodicGaugeTransform_comp` / `periodicGaugeTransform_one` — gauge transforms compose as a
     genuine **left group action** on link configurations (not merely "transformed data has the
     right type").
   * `wilsonPlaquetteEnergy_gaugeTransform` / `wilsonLatticeAction_gaugeTransform` — the Wilson
     plaquette energy and the total Wilson action are gauge-invariant, in full generality.
2. **A concrete witness**: the periodic extent `witnessExtent := fun _ => 1` (side length 2 in
   every direction — the smallest extent at which `periodicLatticeShift` is a nontrivial
   involution rather than a fixed point, verified below), the gauge group
   `Matrix.specialUnitaryGroup (Fin 2) ℂ`, a concrete non-identity element `gWitness`, a link
   configuration `UWitness` carrying it on exactly one edge, and a concrete nontrivial gauge
   transform `gammaWitness`. Every field the mandate names is exercised nondegenerately:
   holonomy is evaluated to a genuinely nonzero curvature reading on one plaquette and to the
   flat value on another (`holonomy_hot`, `holonomy_flat`), the Wilson action is evaluated
   (`wilsonPlaquetteEnergy_witness_hot/_flat`), the gauge transform is exercised as a nontrivial
   action (`gammaWitness_ne_one`, `periodicGaugeTransform_comp` specialised), and gauge invariance
   is proved on the witness by specialising the general theorem
   (`wilsonLatticeAction_gaugeTransform_witness`).

`#print axioms` is recorded for every declaration; none depend on `sorryAx`.
-/

namespace AdalyFormal.Lattice.Witness

open AdalyFormal.Target.ClayStatement

/-! ## §1. General theorems (any `G`, any `L`, any `ρ`, any `γ`) -/

/-- Shifts in two distinct coordinate directions commute. This is the standard lattice fact that
makes a plaquette's four corners well-defined independent of the order the two directions are
traversed; it is what the base-site conjugation law below is built on. -/
theorem periodicLatticeShift_comm {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    {μ ν : Fin 3} (hne : μ ≠ ν) :
    periodicLatticeShift (periodicLatticeShift x μ) ν =
      periodicLatticeShift (periodicLatticeShift x ν) μ := by
  simp only [periodicLatticeShift]
  rw [Function.update_of_ne hne.symm, Function.update_of_ne hne]
  exact Function.update_comm hne (x μ + 1) (x ν + 1) x

/-- **The plaquette-holonomy conjugation law.** Under a gauge transform, a plaquette's holonomy
transforms by conjugation at the plaquette's base site: `U'_∂p = γ(x) · U_∂p · γ(x)⁻¹`. This is the
general fact from which Wilson-action gauge invariance follows; it holds for every plaquette on
every periodic extent, not merely the witness below. -/
theorem periodicPlaquetteHolonomy_gaugeTransform {G : Type*} [Group G] {L : PeriodicLatticeExtent}
    (γ : PeriodicLatticeSite L → G) (U : PeriodicLinkConfiguration G L)
    (p : PeriodicLatticePlaquette L) :
    periodicPlaquetteHolonomy (periodicGaugeTransform γ U) p =
      γ p.1 * periodicPlaquetteHolonomy U p * (γ p.1)⁻¹ := by
  obtain ⟨x, ⟨μ, ν⟩, hμν⟩ := p
  have hne : μ ≠ ν := ne_of_lt hμν
  have hcomm := periodicLatticeShift_comm x hne
  simp only [periodicPlaquetteHolonomy, periodicGaugeTransform, mul_inv_rev]
  rw [hcomm]
  group

/-- Gauge transforms compose as a genuine **left group action** on link configurations: applying
`γ₂` then `γ₁` agrees with applying the pointwise product `γ₁ · γ₂`. This is the substantive
content behind "the action of a gauge transform on a configuration is again a configuration" — not
the trivial typing fact (which holds by construction), but genuine action-law composability. -/
theorem periodicGaugeTransform_comp {G : Type*} [Group G] {L : PeriodicLatticeExtent}
    (γ₁ γ₂ : PeriodicLatticeSite L → G) (U : PeriodicLinkConfiguration G L) :
    periodicGaugeTransform γ₁ (periodicGaugeTransform γ₂ U) =
      periodicGaugeTransform (fun x => γ₁ x * γ₂ x) U := by
  funext e
  simp only [periodicGaugeTransform, mul_inv_rev]
  group

/-- The identity gauge transform acts as the identity map — the action's unit law. -/
theorem periodicGaugeTransform_one {G : Type*} [Group G] {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration G L) :
    periodicGaugeTransform (fun _ => (1 : G)) U = U := by
  funext e
  simp [periodicGaugeTransform]

/-- **Wilson plaquette energy is gauge-invariant, in full generality.** A unitary-valued
representation's trace does not see conjugation, so the holonomy conjugation law above forces the
plaquette energy to agree before and after any gauge transform, for any group, any extent, any
representation. -/
theorem wilsonPlaquetteEnergy_gaugeTransform {G : Type*} [Group G] {d : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin d) ℂ) {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration G L) (γ : PeriodicLatticeSite L → G)
    (p : PeriodicLatticePlaquette L) :
    wilsonPlaquetteEnergy ρ (periodicGaugeTransform γ U) p = wilsonPlaquetteEnergy ρ U p := by
  unfold wilsonPlaquetteEnergy
  rw [periodicPlaquetteHolonomy_gaugeTransform]
  have hhom : (ρ (γ p.1 * periodicPlaquetteHolonomy U p * (γ p.1)⁻¹)).1 =
      (ρ (γ p.1)).1 * (ρ (periodicPlaquetteHolonomy U p)).1 * (ρ (γ p.1)⁻¹).1 := by
    rw [map_mul, map_mul]
    rfl
  have hCA : (ρ (γ p.1)⁻¹).1 * (ρ (γ p.1)).1 = 1 := by
    have hg : (γ p.1)⁻¹ * γ p.1 = (1 : G) := inv_mul_cancel _
    have hpush : ρ (γ p.1)⁻¹ * ρ (γ p.1) = 1 := by
      rw [← map_mul, hg, map_one]
    have h2 : (ρ (γ p.1)⁻¹ * ρ (γ p.1)).1 = (ρ (γ p.1)⁻¹).1 * (ρ (γ p.1)).1 := rfl
    rw [← h2, hpush]
    rfl
  rw [hhom, Matrix.trace_mul_cycle, hCA, one_mul]

/-- **Wilson lattice action is gauge-invariant, in full generality** — the campaign's defining
lattice-gauge-theory invariance property, proved (not assumed) directly from the definitions
already in `ClayStatement.lean`, for every group, extent, coupling and representation. -/
theorem wilsonLatticeAction_gaugeTransform {G : Type*} [Group G] {d : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin d) ℂ) {L : PeriodicLatticeExtent} (β : ℝ)
    (U : PeriodicLinkConfiguration G L) (γ : PeriodicLatticeSite L → G) :
    wilsonLatticeAction ρ β (periodicGaugeTransform γ U) = wilsonLatticeAction ρ β U := by
  unfold wilsonLatticeAction
  congr 1
  exact Finset.sum_congr rfl (fun p _ => wilsonPlaquetteEnergy_gaugeTransform ρ U γ p)

#print axioms periodicLatticeShift_comm
#print axioms periodicPlaquetteHolonomy_gaugeTransform
#print axioms periodicGaugeTransform_comp
#print axioms periodicGaugeTransform_one
#print axioms wilsonPlaquetteEnergy_gaugeTransform
#print axioms wilsonLatticeAction_gaugeTransform

/-! ## §2. The concrete witness -/

/-- The smallest periodic extent at which `periodicLatticeShift` is a nontrivial involution rather
than a fixed point: side length `L μ + 1 = 2` in every direction. At `L μ = 0` (side length 1) the
lattice is a single site and shifting is definitionally the identity — a genuinely degenerate
"lattice" with no real periodicity. `witnessExtent` is the minimal nondegenerate choice the
definitions admit. -/
def witnessExtent : PeriodicLatticeExtent := fun _ => 1

/-- The origin site of the witness lattice. -/
def witnessBase : PeriodicLatticeSite witnessExtent := fun _ => 0

/-- Nondegeneracy: the witness lattice has genuinely `2³ = 8` distinct sites, not a collapsed
carrier. -/
theorem witnessExtent_card : Fintype.card (PeriodicLatticeSite witnessExtent) = 8 := by decide

/-- Nondegeneracy: shifting is not the identity map — the lattice has genuine periodic content,
not a phantom direction that folds back on itself immediately. -/
theorem periodicLatticeShift_witnessBase_ne :
    periodicLatticeShift witnessBase 0 ≠ witnessBase := by decide

/-- Nondegeneracy: shifting twice in the same direction returns home after exactly period 2 (not
a fixed point, and not a longer cycle) — the honest signature of the smallest genuine periodic
lattice, matching side length 2. -/
theorem periodicLatticeShift_witnessBase_period_two :
    periodicLatticeShift (periodicLatticeShift witnessBase 0) 0 = witnessBase := by decide

#print axioms witnessExtent_card
#print axioms periodicLatticeShift_witnessBase_ne
#print axioms periodicLatticeShift_witnessBase_period_two

/-- A concrete non-identity element of `SU(2)`: the real rotation-by-`π/2` matrix
`[[0,1],[-1,0]]`. Unitary (it is real orthogonal), determinant `1`, order `4`. -/
noncomputable def sigmaWitness : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem sigmaWitness_mem : sigmaWitness ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sigmaWitness, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two]
  · simp [sigmaWitness, Matrix.det_fin_two]

/-- The chosen `SU(2)` witness element, packaged with its membership proof. -/
noncomputable def gWitness : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨sigmaWitness, sigmaWitness_mem⟩

theorem gWitness_ne_one : gWitness ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  simp [sigmaWitness, gWitness] at this

#print axioms sigmaWitness_mem
#print axioms gWitness_ne_one

/-- The Wilson trace representation used by the campaign's SU(2) staging target: the inclusion of
`SU(2)` into `U(2)`, i.e. `su2CampaignNormalization`'s `representationDimension = 2` case. Uses
`Submonoid.inclusion` against the standard `specialUnitaryGroup ≤ unitaryGroup` containment. -/
noncomputable def suToUWitness :
    Matrix.specialUnitaryGroup (Fin 2) ℂ →* Matrix.unitaryGroup (Fin 2) ℂ :=
  Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup

/-- A link configuration on the witness lattice: `gWitness` on exactly one edge (the `0`-direction
edge based at the origin), the identity everywhere else. This puts genuine, nontrivial curvature
on the lattice without hiding a nondegenerate choice behind an unmotivated construction. -/
noncomputable def UWitness : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessExtent :=
  fun e => if e = (witnessBase, (0 : Fin 3)) then gWitness else 1

/-- The `(0,1)`-plaquette based at the origin: its boundary's first edge is exactly the hot edge. -/
def dir01 : PeriodicPlaquetteDirections := ⟨(0, 1), by decide⟩

/-- The `(1,2)`-plaquette based at the origin: entirely disjoint from the hot edge. -/
def dir12 : PeriodicPlaquetteDirections := ⟨(1, 2), by decide⟩

-- Edge (in)equalities are pure finite/`Fin` combinatorics -- fully decidable without ever
-- touching the `ℂ`-valued group elements, so `decide` is safe and total here (S82: these are
-- structural facts about the extent/index geometry, not algebraically forced group identities).
theorem edge2_ne_hot :
    (periodicLatticeShift witnessBase 0, (1 : Fin 3)) ≠ (witnessBase, (0 : Fin 3)) := by decide
theorem edge3_ne_hot :
    (periodicLatticeShift witnessBase 1, (0 : Fin 3)) ≠ (witnessBase, (0 : Fin 3)) := by decide
theorem edge4_ne_hot : (witnessBase, (1 : Fin 3)) ≠ (witnessBase, (0 : Fin 3)) := by decide
theorem edge2'_ne_hot :
    (periodicLatticeShift witnessBase 1, (2 : Fin 3)) ≠ (witnessBase, (0 : Fin 3)) := by decide
theorem edge3'_ne_hot :
    (periodicLatticeShift witnessBase 2, (1 : Fin 3)) ≠ (witnessBase, (0 : Fin 3)) := by decide
theorem edge4'_ne_hot : (witnessBase, (2 : Fin 3)) ≠ (witnessBase, (0 : Fin 3)) := by decide

#print axioms edge2_ne_hot
#print axioms edge3_ne_hot
#print axioms edge4_ne_hot
#print axioms edge2'_ne_hot
#print axioms edge3'_ne_hot
#print axioms edge4'_ne_hot

/-- **Holonomy exercised nontrivially.** The origin `(0,1)`-plaquette's holonomy is exactly the
witness `SU(2)` element — a genuinely nonzero curvature reading, not a coincidental identity. -/
theorem holonomy_hot : periodicPlaquetteHolonomy UWitness (witnessBase, dir01) = gWitness := by
  show UWitness (witnessBase, 0) * UWitness (periodicLatticeShift witnessBase 0, 1) *
      (UWitness (periodicLatticeShift witnessBase 1, 0))⁻¹ *
      (UWitness (witnessBase, 1))⁻¹ = gWitness
  rw [show UWitness (witnessBase, (0:Fin 3)) = gWitness from if_pos rfl,
    show UWitness (periodicLatticeShift witnessBase 0, (1:Fin 3)) = 1 from if_neg edge2_ne_hot,
    show UWitness (periodicLatticeShift witnessBase 1, (0:Fin 3)) = 1 from if_neg edge3_ne_hot,
    show UWitness (witnessBase, (1:Fin 3)) = 1 from if_neg edge4_ne_hot]
  simp only [inv_one, mul_one]

/-- **Holonomy exercised on a flat plaquette.** The origin `(1,2)`-plaquette avoids the hot edge
entirely, so its holonomy is exactly the identity — the definitions correctly represent zero
curvature as well as nonzero curvature on the same witness, i.e. the Wilson action below is a
genuinely nonconstant functional of the link configuration. -/
theorem holonomy_flat : periodicPlaquetteHolonomy UWitness (witnessBase, dir12) = 1 := by
  show UWitness (witnessBase, 1) * UWitness (periodicLatticeShift witnessBase 1, 2) *
      (UWitness (periodicLatticeShift witnessBase 2, 1))⁻¹ *
      (UWitness (witnessBase, 2))⁻¹ = 1
  rw [show UWitness (witnessBase, (1:Fin 3)) = 1 from if_neg edge4_ne_hot,
    show UWitness (periodicLatticeShift witnessBase 1, (2:Fin 3)) = 1 from if_neg edge2'_ne_hot,
    show UWitness (periodicLatticeShift witnessBase 2, (1:Fin 3)) = 1 from if_neg edge3'_ne_hot,
    show UWitness (witnessBase, (2:Fin 3)) = 1 from if_neg edge4'_ne_hot]
  simp only [inv_one, mul_one]

/-- **The Wilson action evaluated, nondegenerately.** On the hot plaquette the energy is exactly
`1 - Re(tr σ)/2 = 1 - 0/2 = 1`: a genuinely nonzero curvature reading, not the vacuous `0` an
all-identity configuration would force. -/
theorem wilsonPlaquetteEnergy_witness_hot :
    wilsonPlaquetteEnergy suToUWitness UWitness (witnessBase, dir01) = 1 := by
  unfold wilsonPlaquetteEnergy
  rw [holonomy_hot]
  have hcoe : (suToUWitness gWitness).1 = sigmaWitness := rfl
  rw [hcoe]
  norm_num [sigmaWitness, Matrix.trace_fin_two]

/-- **The Wilson action evaluated on the flat plaquette**: exactly `0`, the pure-gauge/no-curvature
value, confirming the two plaquette readings above are genuinely different (nondegenerate). -/
theorem wilsonPlaquetteEnergy_witness_flat :
    wilsonPlaquetteEnergy suToUWitness UWitness (witnessBase, dir12) = 0 := by
  unfold wilsonPlaquetteEnergy
  rw [holonomy_flat]
  have hcoe : (suToUWitness (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)).1 = 1 := rfl
  rw [hcoe]
  norm_num [Matrix.trace_fin_two]

#print axioms holonomy_hot
#print axioms holonomy_flat
#print axioms wilsonPlaquetteEnergy_witness_hot
#print axioms wilsonPlaquetteEnergy_witness_flat

/-! ## §3. The gauge transform exercised on the witness -/

/-- A concrete, genuinely nontrivial gauge transform: `gWitness` at the origin, identity
elsewhere. -/
noncomputable def gammaWitness : PeriodicLatticeSite witnessExtent →
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  fun x => if x = witnessBase then gWitness else 1

/-- `gammaWitness` is not the identity transform, so every invariance statement exercised on it
below is non-vacuous. -/
theorem gammaWitness_ne_one : gammaWitness ≠ (fun _ => 1) := by
  intro h
  have heq : gammaWitness witnessBase = 1 := by rw [h]
  rw [show gammaWitness witnessBase = gWitness from if_pos rfl] at heq
  exact gWitness_ne_one heq

/-- **"The action of a gauge transform on a configuration is again a configuration", exercised as
a genuine action law on the witness**: composing two copies of `gammaWitness` agrees with
transforming by the pointwise-squared transform — not the trivial typing fact, but the general
`periodicGaugeTransform_comp` law specialised to concrete, nontrivial data. -/
theorem periodicGaugeTransform_comp_witness :
    periodicGaugeTransform gammaWitness (periodicGaugeTransform gammaWitness UWitness) =
      periodicGaugeTransform (fun x => gammaWitness x * gammaWitness x) UWitness :=
  periodicGaugeTransform_comp gammaWitness gammaWitness UWitness

/-- The identity transform acts as the identity on the witness (the action's unit law,
specialised). -/
theorem periodicGaugeTransform_one_witness :
    periodicGaugeTransform (fun _ => 1) UWitness = UWitness :=
  periodicGaugeTransform_one UWitness

/-- **"The Wilson action is gauge-invariant on your witness."** The general theorem
`wilsonLatticeAction_gaugeTransform`, specialised to the concrete witness link configuration and
the concrete nontrivial gauge transform `gammaWitness` — for every coupling `β`. -/
theorem wilsonLatticeAction_gaugeTransform_witness (β : ℝ) :
    wilsonLatticeAction suToUWitness β (periodicGaugeTransform gammaWitness UWitness) =
      wilsonLatticeAction suToUWitness β UWitness :=
  wilsonLatticeAction_gaugeTransform suToUWitness β UWitness gammaWitness

#print axioms gammaWitness_ne_one
#print axioms periodicGaugeTransform_comp_witness
#print axioms periodicGaugeTransform_one_witness
#print axioms wilsonLatticeAction_gaugeTransform_witness

end AdalyFormal.Lattice.Witness
