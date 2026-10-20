/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.NormalizedCounterexampleSearch
import AdalyFormal.Balaban.BackgroundAveraging
import AdalyFormal.Balaban.RegularUPerturbation

set_option autoImplicit false

/-!
# `NonFlatBackground.lean` — a background with PROVABLY NONZERO CURVATURE, and the two
degeneracy repairs the 2026-07-26 degenerate-test-point sweep demanded

## ⚠ WHAT THIS FILE FIXES

**(1c) `RegularityHolonomy.pureGaugeU` is labelled "GENUINELY NON-FLAT" and is FLAT.**
`pureGaugeU := periodicGaugeTransform starGaugeFn trivialU`, and the SAME file proves
`holonomyElem (periodicGaugeTransform γ trivialU) p = 1` for every `γ` and every `p`. Its
curvature is identically the identity. All that `pureGaugeU_ne_trivial` establishes is that ONE
BARE LINK VALUE differs from `1` — a gauge-variant fact carrying no field-strength content.
§7 below proves the flatness as a theorem (`pureGaugeU_holonomy_eq_one`,
`pureGaugeU_holonomyDefectSq_eq_zero`) so the mislabelling is a matter of record, not of prose.

**The repair (§2–§5)**: `nonflatU t`, an explicit one-parameter family with
`holonomyElem (nonflatU t) witnessPlaquette ≠ 1` for every `t ≠ 0` — nonzero curvature, PROVED
(`nonflatU_curvature_ne_one`), together with the strictly stronger gauge-invariant statement
that it is not a gauge transform of ANY configuration that is flat at `witnessPlaquette`
(`nonflatU_not_gaugeTransform_of_flat`), `pureGaugeU` and `trivialU` included. The plaquette
holonomy is the distinguishing invariant, and §1 proves it conjugates (rather than being
preserved) under a gauge transformation, which is exactly why it separates these two objects
and a bare link value does not.

Crucially the family is a SMALL-curvature family: `holonomyDefectSq (nonflatU t) = 8t²/(1+t²)`
at the four exceptional plaquettes and `0` elsewhere, so
`IsRegularHolonomy (nonflatU t) (8t²/(1+t²))` with `8t²/(1+t²) ≤ 8t²` arbitrarily small — the
regime the regular-`U`/small-`α₁` results need, which neither of the tree's existing non-flat
witnesses could serve (`witnessU` and `centralHolonomyU` sit at defect `4` and `8`, and the
only witness admitted at a SMALL threshold, `pureGaugeU`, was flat).

**(1) `BackgroundAveraging.R0` is background-blind.** `R0 U = RMap (U (witnessY,0)⁻¹)`: one
fixed path, no `b`, no `c₋`, despite the docstring naming it `R_{0,c₋}(U)`. Since `RMap g` is
a linear automorphism, §8 proves `q1Kernel U = ker qPrimeSuTwoLM` FOR EVERY `U`
(`q1Kernel_eq_ker_qPrimeSuTwoLM`), hence `q1Kernel U = q1Kernel U'` for any two backgrounds
(`q1Kernel_background_blind`) — including the genuinely curved `nonflatU t`. In particular
`BackgroundAveraging.deltaWitnessConfig_notMem_q1Kernel_witnessU`, advertised as a second check
with a "different reason", is proved here to be LOGICALLY EQUIVALENT to the `trivialU` one
(`control_witnessU_iff_trivialU`): it is a falsifiability control that cannot fail
independently. This file does NOT redefine `R0` (other lanes are live, and the faithful
per-bond transport already exists as `Q1Real.rZeroA` — that, not a patch here, is the repair
path).

## ⚠ WHAT IS *NOT* REPAIRED, AND WHY (OPS-1: earned, not elected)

`FaithfulCoercivitySU2.uReg1 : UconfigReg := ⟨pureGaugeU, pureGaugeU_isRegularHolonomy_zero⟩`
CANNOT be re-instantiated at nonzero curvature, and not for want of a witness: `UconfigReg` is
`{U // IsRegularHolonomy U 0}`, i.e. threshold `Mα₀ = 0`, and §6 proves
`IsRegularHolonomy U 0 ↔ ∀ p, holonomyElem U p = 1` (`isRegularHolonomy_zero_iff_flat`). **At
threshold zero the regular set is exactly the flat-holonomy set**, so every element of
`UconfigReg` is curvature-free by construction and `uReg0 ≠ uReg1` can only ever be witnessed by
a gauge-variant link value. The fix is not a witness swap; `UconfigReg` must be re-indexed by a
positive threshold. Stated, not silently worked around.

`TheLemmaNormalized.check3_nonvacuous` IS repairable, and §10 does it:
`check3_nonvacuous_curved` re-proves the same existential at `U := nonflatU (1/4)` (defect
`8/17 < 1`) with an ADDED clause `∃ p, holonomyElem U p ≠ 1`. It is proved here rather than
edited into `TheLemmaNormalized.lean` because that file is outside this lane's write scope.

## OPS-3 — how each new result can FAIL

* `nonflatU_curvature_ne_one` fails at `t = 0` (`nonflatU 0 = trivialU`, holonomy `= 1`); the
  hypothesis `t ≠ 0` is load-bearing and `nonflatU_zero_eq_trivial` exhibits the failure.
* `nonflatU_isRegularHolonomy` is SHARP: `nonflatU_not_isRegularHolonomy_of_lt` proves the
  predicate genuinely fails at every threshold below `8t²/(1+t²)`, so the bound is not slack.
* `singleBondU_isRegularHolonomy` would be false with `defectOfElem` replaced by any smaller
  quantity (same sharpness lemma), and false without `trace_inv_re_eq_trace_re` (the `p3`/`p4`
  plaquettes carry `X⁻¹`, not `X`).
* `q1Kernel_background_blind` would be FALSE if `R0` were the genuinely `c₋`-dependent
  transport it is named after; its proof uses only the invertibility of a single `RMap`, and
  `RMap_apply_eq_zero_iff` is the exact point where a non-invertible (e.g. projection-valued)
  `R0` would break it.
* `isRegularHolonomy_zero_iff_flat`'s forward direction is false for the OLD `IsRegular` proxy
  (`NormalizedCounterexampleSearch.centralHolonomyU_isRegular_zero`: a central background is
  `IsRegular` at `0` and has holonomy `-1 ≠ 1`) — the two predicates genuinely differ here.
-/

namespace AdalyFormal.Balaban.NonFlatBackground

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.DeltaPrime
  AdalyFormal.Balaban.DeltaKFull AdalyFormal.Balaban.LatticeOperators
  AdalyFormal.Balaban.RegularityHolonomy
  AdalyFormal.Balaban.NormalizedCounterexampleSearch

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the plaquette holonomy CONJUGATES under a gauge transformation

This is the general statement of which `RegularityHolonomy.holonomyElem_periodicGaugeTransform_trivialU`
is the `U = trivialU` special case, and it is what makes "the holonomy is `≠ 1`" a
gauge-INVARIANT separation between a genuinely curved background and a pure gauge, whereas the
bare link value `U (witnessY,0)` is gauge-VARIANT and separates nothing. -/

/-- The four-factor expansion of `holonomyElem`, as a rewrite target (definitional). -/
theorem holonomyElem_expand
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyElem U p = U (p.1, p.2.1.1) * U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
      (U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ * (U (p.1, p.2.1.2))⁻¹ := rfl

/-- **Gauge covariance of the plaquette holonomy**: `U(∂p) ↦ γ(x)·U(∂p)·γ(x)⁻¹` where `x` is the
plaquette's base site. The one nontrivial ingredient is `periodicLatticeShift_comm` (LAW-19,
reused), which identifies the two far-corner gauge factors so they cancel. -/
theorem holonomyElem_periodicGaugeTransform
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyElem (periodicGaugeTransform γ U) p = γ p.1 * holonomyElem U p * (γ p.1)⁻¹ := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  rw [holonomyElem_expand, holonomyElem_expand]
  simp only [periodicGaugeTransform]
  rw [periodicLatticeShift_comm p.1 hne]
  group

/-- **Flatness at a plaquette is gauge invariant.** -/
theorem holonomyElem_periodicGaugeTransform_eq_one_iff
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyElem (periodicGaugeTransform γ U) p = 1 ↔ holonomyElem U p = 1 := by
  rw [holonomyElem_periodicGaugeTransform]
  constructor
  · intro h
    have := congrArg (fun g => (γ p.1)⁻¹ * g * γ p.1) h
    simpa [mul_assoc] using this
  · intro h; rw [h]; simp

/-! ## §2 — a rational (Pythagorean) rotation family in `SU(2)`

No transcendental functions: `a(t) = (1-t²)/(1+t²)`, `b(t) = 2t/(1+t²)` satisfy `a²+b²=1`
identically over `ℝ`, giving an explicit ALGEBRAIC one-parameter subgroup-shaped family whose
distance from `1` is a rational function of `t` and hence quantitatively controllable. -/

/-- `a(t) = (1-t²)/(1+t²)`. -/
noncomputable def rotA (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)

/-- `b(t) = 2t/(1+t²)`. -/
noncomputable def rotB (t : ℝ) : ℝ := (2 * t) / (1 + t ^ 2)

theorem one_add_sq_ne_zero (t : ℝ) : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity

theorem rotA_sq_add_rotB_sq (t : ℝ) : rotA t ^ 2 + rotB t ^ 2 = 1 := by
  have h : (1 : ℝ) + t ^ 2 ≠ 0 := one_add_sq_ne_zero t
  show ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + ((2 * t) / (1 + t ^ 2)) ^ 2 = 1
  field_simp
  ring

theorem rotA_le_one (t : ℝ) : rotA t ≤ 1 := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [rotA, div_le_one h]
  nlinarith [sq_nonneg t]

theorem rotA_eq_one_iff (t : ℝ) : rotA t = 1 ↔ t = 0 := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [rotA, div_eq_one_iff_eq h.ne']
  constructor
  · intro hh; nlinarith [sq_nonneg t]
  · intro hh; rw [hh]; ring

/-- The rotation matrix `!![a, b; -b, a]`. -/
noncomputable def rotM (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((rotA t : ℝ) : ℂ), ((rotB t : ℝ) : ℂ); -((rotB t : ℝ) : ℂ), ((rotA t : ℝ) : ℂ)]

theorem rotA_sq_add_rotB_sq_complex (t : ℝ) :
    ((rotA t : ℝ) : ℂ) * ((rotA t : ℝ) : ℂ) + ((rotB t : ℝ) : ℂ) * ((rotB t : ℝ) : ℂ) = 1 := by
  have h : ((rotA t ^ 2 + rotB t ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [rotA_sq_add_rotB_sq]
  push_cast at h
  linear_combination h

theorem rotM_conjTranspose (t : ℝ) :
    (rotM t).conjTranspose = !![((rotA t : ℝ) : ℂ), -((rotB t : ℝ) : ℂ);
                   ((rotB t : ℝ) : ℂ), ((rotA t : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, Matrix.conjTranspose_apply]

theorem rotM_mem_unitaryGroup (t : ℝ) : rotM t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, rotM_conjTranspose]
  have hab := rotA_sq_add_rotB_sq_complex t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first
      | linear_combination hab
      | ring1

theorem rotM_det (t : ℝ) : (rotM t).det = 1 := by
  have hab := rotA_sq_add_rotB_sq_complex t
  rw [rotM, Matrix.det_fin_two_of]
  linear_combination hab

theorem rotM_mem (t : ℝ) : rotM t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨rotM_mem_unitaryGroup t, rotM_det t⟩

/-- The rotation, packaged as an `SU(2)` element. -/
noncomputable def rotElem (t : ℝ) : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨rotM t, rotM_mem t⟩

theorem rotElem_coe (t : ℝ) :
    ((rotElem t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = rotM t := rfl

theorem trace_rotM_re (t : ℝ) : (Matrix.trace (rotM t)).re = 2 * rotA t := by
  rw [rotM, Matrix.trace_fin_two]
  simp
  ring

/-- **`rotElem t = 1` exactly at `t = 0`** — the family is genuinely non-trivial. -/
theorem rotElem_eq_one_iff (t : ℝ) :
    rotElem t = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) ↔ t = 0 := by
  constructor
  · intro h
    have hm : rotM t = (1 : Matrix (Fin 2) (Fin 2) ℂ) := congrArg Subtype.val h
    have h01 := congrFun (congrFun hm 0) 1
    simp only [rotM, Matrix.one_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Matrix.head_fin_const] at h01
    norm_num at h01
    have hb : rotB t = 0 := by exact_mod_cast h01
    have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [rotB, div_eq_zero_iff] at hb
    rcases hb with hb | hb
    · linarith
    · exact absurd hb h1.ne'
  · intro h
    subst h
    apply Subtype.ext
    rw [rotElem_coe, rotM]
    have ha : rotA 0 = 1 := by rw [rotA]; norm_num
    have hb : rotB 0 = 0 := by rw [rotB]; norm_num
    rw [ha, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem rotElem_ne_one {t : ℝ} (ht : t ≠ 0) :
    rotElem t ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := fun h => ht ((rotElem_eq_one_iff t).mp h)

/-! ## §3 — `nonflatU t`: the genuinely CURVED background

Built as an instance of the tree's OWN `NormalizedCounterexampleSearch.singleBondU` family
(LAW-19: not a second single-bond construction — `witnessU` and `centralHolonomyU` are the
`witnessMElem`/`negOneElem` instances of the same `def`, proved `rfl` in that file). -/

/-- **The non-flat background**: `rotElem t` on the single bond `(witnessY, 0)`, `1` elsewhere. -/
noncomputable def nonflatU (t : ℝ) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) AdmissibleSubspace.witnessL :=
  singleBondU (rotElem t)

theorem nonflatU_at_x_mu (t : ℝ) :
    nonflatU t (AdmissibleSubspace.witnessY, (0 : Fin 3)) = rotElem t :=
  singleBondU_at_x_mu _

theorem nonflatU_elsewhere (t : ℝ) {e : Bond AdmissibleSubspace.witnessL}
    (h : e ≠ (AdmissibleSubspace.witnessY, (0 : Fin 3))) : nonflatU t e = 1 :=
  singleBondU_elsewhere _ h

/-- **OPS-3 failure exhibit**: at `t = 0` the background degenerates to the flat one, so the
`t ≠ 0` hypothesis in every curvature statement below is load-bearing. -/
theorem nonflatU_zero_eq_trivial :
    nonflatU 0 = (trivialU (L := AdmissibleSubspace.witnessL)) := by
  funext e
  by_cases h : e = (AdmissibleSubspace.witnessY, (0 : Fin 3))
  · rw [h, nonflatU_at_x_mu, (rotElem_eq_one_iff 0).mpr rfl]; rfl
  · rw [nonflatU_elsewhere 0 h]; rfl

/-- **THE CURVATURE VALUE**: the plaquette holonomy at `witnessPlaquette` is `rotElem t`. -/
theorem holonomyElem_nonflatU_witnessPlaquette (t : ℝ) :
    holonomyElem (nonflatU t) witnessPlaquette = rotElem t :=
  holonomy_singleBondU_witnessPlaquette _

/-- **THE CURVATURE WITNESS — the theorem the dispatch demands.** For every `t ≠ 0` the
background `nonflatU t` has a plaquette whose holonomy is `≠ 1`: its field strength is
genuinely nonzero, not merely "some link value differs from `1`". -/
theorem nonflatU_curvature_ne_one {t : ℝ} (ht : t ≠ 0) :
    holonomyElem (nonflatU t) witnessPlaquette ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [holonomyElem_nonflatU_witnessPlaquette]
  exact rotElem_ne_one ht

theorem nonflatU_has_curved_plaquette {t : ℝ} (ht : t ≠ 0) :
    ∃ p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL,
      holonomyElem (nonflatU t) p ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨witnessPlaquette, nonflatU_curvature_ne_one ht⟩

/-! ## §4 — `nonflatU t` is not `trivialU`, and NOT A GAUGE TRANSFORM of anything flat -/

theorem nonflatU_ne_trivialU {t : ℝ} (ht : t ≠ 0) :
    nonflatU t ≠ (trivialU (L := AdmissibleSubspace.witnessL)) := by
  intro h
  apply nonflatU_curvature_ne_one ht
  rw [h, holonomyElem_trivialU]

/-- **The gauge-invariant separation.** `nonflatU t` is not the gauge transform, by ANY `γ`, of
ANY configuration that is flat at `witnessPlaquette`. This is strictly stronger than
`≠ trivialU`, and it is exactly the statement `pureGaugeU_ne_trivial` could never make: bare
link values are gauge-variant, plaquette holonomies conjugate (§1). -/
theorem nonflatU_not_gaugeTransform_of_flat {t : ℝ} (ht : t ≠ 0)
    (γ : PeriodicLatticeSite AdmissibleSubspace.witnessL →
      Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdmissibleSubspace.witnessL)
    (hU : holonomyElem U witnessPlaquette = 1) :
    nonflatU t ≠ periodicGaugeTransform γ U := by
  intro h
  apply nonflatU_curvature_ne_one ht
  rw [h, holonomyElem_periodicGaugeTransform_eq_one_iff]
  exact hU

/-! ## §5 — generic single-bond regularity, at the SHARP threshold; and the small-`α₁` regime -/

/-- The holonomy defect of a group element, i.e. the value `holonomyDefectSq` takes when the
plaquette holonomy is that element. -/
noncomputable def defectOfElem (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  4 - 2 * (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re

theorem holonomyDefectSq_eq_defectOfElem
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyDefectSq U p = defectOfElem (holonomyElem U p) := rfl

theorem defectOfElem_nonneg (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) : 0 ≤ defectOfElem X := by
  have h := holonomyDefectSq_nonneg (singleBondU X) witnessPlaquette
  rwa [holonomyDefectSq_eq_defectOfElem, holonomy_singleBondU_witnessPlaquette] at h

theorem defectOfElem_inv (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    defectOfElem X⁻¹ = defectOfElem X := by
  unfold defectOfElem
  rw [trace_inv_re_eq_trace_re]

theorem defectOfElem_one : defectOfElem (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = 0 := by
  unfold defectOfElem
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.one_apply]

/-- **`singleBondU X`'s holonomy is trivial off the four exceptional plaquettes**, generic in
`X` — the generalisation of `TheLemmaNormalized.holonomy_witnessU_eq_one` (which is its
`X = witnessMElem` case), obtained by replacing `witnessU_elsewhere` with the already-general
`singleBondU_elsewhere` and reusing the SAME case-covering lemmas (LAW-19). -/
theorem holonomy_singleBondU_eq_one (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (hp1 : p ≠ witnessPlaquette) (hp2 : p ≠ myWitnessPlaquette2) (hp3 : p ≠ p3) (hp4 : p ≠ p4) :
    holonomyElem (singleBondU X) p = 1 := by
  rw [holonomyElem_expand]
  have e1 : singleBondU X (p.1, p.2.1.1) = 1 := by
    apply singleBondU_elsewhere
    intro hcon
    rcases eq_witnessPlaquette_or_myWitnessPlaquette2 (congrArg Prod.fst hcon)
        (congrArg Prod.snd hcon) with h | h
    · exact hp1 h
    · exact hp2 h
  have e2 : singleBondU X (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 1 := by
    apply singleBondU_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)
  have e3 : singleBondU X (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 1 := by
    apply singleBondU_elsewhere
    intro hcon
    rcases eq_p3_or_p4 (congrArg Prod.fst hcon) (congrArg Prod.snd hcon) with h | h
    · exact hp3 h
    · exact hp4 h
  have e4 : singleBondU X (p.1, p.2.1.2) = 1 := by
    apply singleBondU_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)
  rw [e1, e2, e3, e4]
  simp

/-- **The trichotomy**: every plaquette holonomy of `singleBondU X` is `X`, `X⁻¹`, or `1`. -/
theorem holonomy_singleBondU_trichotomy (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL) :
    holonomyElem (singleBondU X) p = X ∨ holonomyElem (singleBondU X) p = X⁻¹ ∨
      holonomyElem (singleBondU X) p = 1 := by
  by_cases h1 : p = witnessPlaquette
  · exact Or.inl (by rw [h1]; exact holonomy_singleBondU_witnessPlaquette X)
  by_cases h2 : p = myWitnessPlaquette2
  · exact Or.inl (by rw [h2]; exact holonomy_singleBondU_myWitnessPlaquette2 X)
  by_cases h3 : p = p3
  · exact Or.inr (Or.inl (by rw [h3]; exact holonomy_singleBondU_p3 X))
  by_cases h4 : p = p4
  · exact Or.inr (Or.inl (by rw [h4]; exact holonomy_singleBondU_p4 X))
  · exact Or.inr (Or.inr (holonomy_singleBondU_eq_one X h1 h2 h3 h4))

/-- **GENERIC REGULARITY AT THE SHARP THRESHOLD.** `singleBondU X` is `IsRegularHolonomy` at
exactly `defectOfElem X`. Subsumes `TheLemmaNormalized.witnessU_isRegularHolonomy_four`
(`defectOfElem witnessMElem = 4`) and covers `centralHolonomyU` (`= 8`). -/
theorem singleBondU_isRegularHolonomy (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    IsRegularHolonomy (singleBondU X) (defectOfElem X) := by
  intro p
  rw [holonomyDefectSq_eq_defectOfElem]
  rcases holonomy_singleBondU_trichotomy X p with h | h | h
  · rw [h]
  · rw [h, defectOfElem_inv]
  · rw [h, defectOfElem_one]; exact defectOfElem_nonneg X

/-- **SHARPNESS (OPS-3)**: the threshold cannot be lowered — the predicate genuinely fails
below `defectOfElem X`, so the bound above is attained, not slack. -/
theorem singleBondU_not_isRegularHolonomy_of_lt (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    {M : ℝ} (h : M < defectOfElem X) : ¬ IsRegularHolonomy (singleBondU X) M := by
  intro hreg
  have hb := hreg witnessPlaquette
  rw [holonomyDefectSq_eq_defectOfElem, holonomy_singleBondU_witnessPlaquette] at hb
  linarith

/-! ### §5.1 — the quantitative small-curvature statement -/

theorem defectOfElem_rotElem (t : ℝ) : defectOfElem (rotElem t) = 8 * t ^ 2 / (1 + t ^ 2) := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  unfold defectOfElem
  rw [rotElem_coe, trace_rotM_re, rotA]
  field_simp
  ring

theorem nonflatU_isRegularHolonomy (t : ℝ) :
    IsRegularHolonomy (nonflatU t) (8 * t ^ 2 / (1 + t ^ 2)) := by
  rw [← defectOfElem_rotElem]
  exact singleBondU_isRegularHolonomy _

theorem nonflatU_not_isRegularHolonomy_of_lt {t M : ℝ} (h : M < 8 * t ^ 2 / (1 + t ^ 2)) :
    ¬ IsRegularHolonomy (nonflatU t) M := by
  apply singleBondU_not_isRegularHolonomy_of_lt
  rwa [defectOfElem_rotElem]

theorem nonflatU_defect_pos {t : ℝ} (ht : t ≠ 0) : 0 < 8 * t ^ 2 / (1 + t ^ 2) := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have ht2 : 0 < t ^ 2 := by positivity
  positivity

theorem nonflatU_defect_le (t : ℝ) : 8 * t ^ 2 / (1 + t ^ 2) ≤ 8 * t ^ 2 := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [div_le_iff₀ h]
  nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]

/-- **The small-`α₁` regime is genuinely populated by CURVED backgrounds**: for every `ε > 0`
there is a background with nonzero curvature that is `IsRegularHolonomy`-regular below `ε`. The
tree previously had no such object — its only witness admitted at a small threshold was the
flat `pureGaugeU`. -/
theorem exists_curved_regular_below {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, t ≠ 0 ∧
      IsRegularHolonomy (nonflatU t) (8 * t ^ 2 / (1 + t ^ 2)) ∧
      8 * t ^ 2 / (1 + t ^ 2) < ε ∧
      holonomyElem (nonflatU t) witnessPlaquette ≠ 1 := by
  refine ⟨Real.sqrt (ε / 16), ?_, nonflatU_isRegularHolonomy _, ?_, ?_⟩
  · have : 0 < Real.sqrt (ε / 16) := Real.sqrt_pos.mpr (by linarith)
    exact this.ne'
  · have hsq : Real.sqrt (ε / 16) ^ 2 = ε / 16 := Real.sq_sqrt (by linarith)
    have hle := nonflatU_defect_le (Real.sqrt (ε / 16))
    rw [hsq] at hle ⊢
    linarith
  · apply nonflatU_curvature_ne_one
    have : 0 < Real.sqrt (ε / 16) := Real.sqrt_pos.mpr (by linarith)
    exact this.ne'

/-! ## §6 — WHY `FaithfulCoercivitySU2.uReg1` CANNOT BE REPAIRED BY A WITNESS SWAP

`UconfigReg = {U // IsRegularHolonomy U 0}`. At threshold `0` the predicate is EQUIVALENT to
flatness of every plaquette holonomy, so no element of `UconfigReg` has curvature, whatever
witness is supplied. -/

/-- **`holonomyDefectSq U p = 0 ↔ U(∂p) = 1`.** The forward direction is the content: for a
unitary `2×2` matrix, `Re tr g = 2` forces `g = 1`. Proved from unitarity of the columns alone
(the same route as `holonomyDefectSq_nonneg`, pushed to the equality case). -/
theorem holonomyDefectSq_eq_zero_iff
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyDefectSq U p = 0 ↔ holonomyElem U p = 1 := by
  constructor
  · intro hzero
    set g : Matrix (Fin 2) (Fin 2) ℂ := (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) with hg
    have hmem : g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
      have hm : g ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := SetLike.coe_mem (holonomyElem U p)
      exact (Matrix.mem_specialUnitaryGroup_iff.mp hm).1
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hmem
    have hrow0 := congrFun (congrFun hmem 0) 0
    have hrow1 := congrFun (congrFun hmem 1) 1
    simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] at hrow0 hrow1
    have e00 : g 0 0 * star (g 0 0) = (Complex.normSq (g 0 0) : ℂ) := by
      rw [← starRingEnd_apply]; exact Complex.mul_conj (g 0 0)
    have e10 : g 0 1 * star (g 0 1) = (Complex.normSq (g 0 1) : ℂ) := by
      rw [← starRingEnd_apply]; exact Complex.mul_conj (g 0 1)
    have e01 : g 1 0 * star (g 1 0) = (Complex.normSq (g 1 0) : ℂ) := by
      rw [← starRingEnd_apply]; exact Complex.mul_conj (g 1 0)
    have e11 : g 1 1 * star (g 1 1) = (Complex.normSq (g 1 1) : ℂ) := by
      rw [← starRingEnd_apply]; exact Complex.mul_conj (g 1 1)
    rw [e00, e10] at hrow0
    rw [e01, e11] at hrow1
    have hr0 : Complex.normSq (g 0 0) + Complex.normSq (g 0 1) = 1 := by
      have := congrArg Complex.re hrow0
      simpa using this
    have hr1 : Complex.normSq (g 1 0) + Complex.normSq (g 1 1) = 1 := by
      have := congrArg Complex.re hrow1
      simpa using this
    have hns00 : Complex.normSq (g 0 0) = (g 0 0).re * (g 0 0).re + (g 0 0).im * (g 0 0).im :=
      Complex.normSq_apply (g 0 0)
    have hns11 : Complex.normSq (g 1 1) = (g 1 1).re * (g 1 1).re + (g 1 1).im * (g 1 1).im :=
      Complex.normSq_apply (g 1 1)
    have htrace : (Matrix.trace g).re = (g 0 0).re + (g 1 1).re := by
      simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Complex.add_re]
    have hsum : (g 0 0).re + (g 1 1).re = 2 := by
      have h' : holonomyDefectSq U p = 4 - 2 * (Matrix.trace g).re := rfl
      rw [h', htrace] at hzero
      linarith
    have hn01 := Complex.normSq_nonneg (g 0 1)
    have hn10 := Complex.normSq_nonneg (g 1 0)
    have hre00 : (g 0 0).re = 1 := by
      nlinarith [sq_nonneg ((g 0 0).im), sq_nonneg ((g 1 1).im), sq_nonneg ((g 0 0).re - 1),
        sq_nonneg ((g 1 1).re - 1)]
    have hre11 : (g 1 1).re = 1 := by linarith
    have him00 : (g 0 0).im = 0 := by nlinarith [sq_nonneg ((g 0 0).im)]
    have him11 : (g 1 1).im = 0 := by nlinarith [sq_nonneg ((g 1 1).im)]
    have hz01 : Complex.normSq (g 0 1) = 0 := by
      rw [hns00, hre00, him00] at hr0; linarith
    have hz10 : Complex.normSq (g 1 0) = 0 := by
      rw [hns11, hre11, him11] at hr1; linarith
    have g01 : g 0 1 = 0 := Complex.normSq_eq_zero.mp hz01
    have g10 : g 1 0 = 0 := Complex.normSq_eq_zero.mp hz10
    have g00 : g 0 0 = 1 := by apply Complex.ext <;> simp [hre00, him00]
    have g11 : g 1 1 = 1 := by apply Complex.ext <;> simp [hre11, him11]
    apply Subtype.ext
    show g = (1 : Matrix (Fin 2) (Fin 2) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, g00, g01, g10, g11]
  · intro h
    rw [holonomyDefectSq_eq_defectOfElem, h, defectOfElem_one]

/-- **THRESHOLD ZERO IS FLATNESS.** Consequently `FaithfulCoercivitySU2.UconfigReg`
(`= {U // IsRegularHolonomy U 0}`) contains ONLY curvature-free configurations: `uReg1` cannot
be re-instantiated at nonzero curvature by any choice of witness. The repair must raise the
threshold. -/
theorem isRegularHolonomy_zero_iff_flat
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    IsRegularHolonomy U (0 : ℝ) ↔ ∀ p : PeriodicLatticePlaquette L, holonomyElem U p = 1 := by
  constructor
  · intro h p
    exact (holonomyDefectSq_eq_zero_iff U p).mp
      (le_antisymm (h p) (holonomyDefectSq_nonneg U p))
  · intro h p
    exact le_of_eq ((holonomyDefectSq_eq_zero_iff U p).mpr (h p))

/-- The contrapositive, in the shape the `UconfigReg` audit needs. -/
theorem no_curved_regular_at_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (hp : holonomyElem U p ≠ 1) :
    ¬ IsRegularHolonomy U (0 : ℝ) := fun h => hp ((isRegularHolonomy_zero_iff_flat U).mp h p)

/-! ## §7 — DEFECT 1c AS A THEOREM: `pureGaugeU` has IDENTICALLY ZERO CURVATURE

`RegularityHolonomy.pureGaugeU`'s docstrings call it "GENUINELY NON-FLAT" and claim
"non-vacuity beyond the flat background". Both are false in the field-strength sense. -/

theorem pureGaugeU_holonomy_eq_one (p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL) :
    holonomyElem pureGaugeU p = 1 :=
  holonomyElem_periodicGaugeTransform_trivialU _ _

theorem pureGaugeU_holonomyDefectSq_eq_zero
    (p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL) :
    holonomyDefectSq pureGaugeU p = 0 :=
  (holonomyDefectSq_eq_zero_iff pureGaugeU p).mpr (pureGaugeU_holonomy_eq_one p)

/-- **`pureGaugeU` and `nonflatU t` are genuinely different objects** — and the separating
invariant is the curvature, not a link value. -/
theorem nonflatU_ne_pureGaugeU {t : ℝ} (ht : t ≠ 0) : nonflatU t ≠ pureGaugeU := by
  intro h
  exact nonflatU_curvature_ne_one ht (h ▸ pureGaugeU_holonomy_eq_one witnessPlaquette)

/-- The exact sense in which `pureGaugeU_ne_trivial` is weaker than it reads: a configuration
can differ from `trivialU` at a link and still be flat at EVERY plaquette. -/
theorem flat_but_link_ne_one :
    (∀ p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL, holonomyElem pureGaugeU p = 1) ∧
      pureGaugeU (AdmissibleSubspace.witnessY, (0 : Fin 3)) ≠ 1 :=
  ⟨pureGaugeU_holonomy_eq_one, pureGaugeU_ne_trivial⟩

/-! ## §8 — DEFECT 1 AS A THEOREM: `q1Kernel` does not see the background at all -/

/-- `RMap g` is injective at `0`: it is a linear automorphism with inverse `RMap g⁻¹`. -/
theorem RMap_apply_eq_zero_iff (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    RMap g X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have h2 : RMap g⁻¹ (RMap g X) = RMap g⁻¹ 0 := by rw [h]
    rw [RMap_mul_apply, inv_mul_cancel, RMap_one, map_zero] at h2
    simpa using h2
  · intro h; rw [h, map_zero]

theorem R0_apply_eq_zero_iff
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdmissibleSubspace.witnessL) (X : SuTwo) :
    AdalyFormal.Balaban.BackgroundAveraging.R0 U X = 0 ↔ X = 0 := by
  unfold AdalyFormal.Balaban.BackgroundAveraging.R0
  exact RMap_apply_eq_zero_iff _ X

/-- **THE DEGENERACY, PROVED**: for EVERY background `U`, the `Q₁(U)B=0` locus is the
background-free `ker Q'₁`. `R0 U` is a single invertible conjugation applied uniformly to every
coarse bond, so it cannot change a kernel. -/
theorem q1Kernel_eq_ker_qPrimeSuTwoLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdmissibleSubspace.witnessL) :
    AdalyFormal.Balaban.BackgroundAveraging.q1Kernel U =
      LinearMap.ker (AdalyFormal.Balaban.BackgroundAveraging.qPrimeSuTwoLM
        AdmissibleSubspace.witnessL AdmissibleSubspace.witnessEll) := by
  ext A
  rw [AdalyFormal.Balaban.BackgroundAveraging.q1Kernel, LinearMap.mem_ker, LinearMap.mem_ker,
    funext_iff, funext_iff]
  constructor
  · intro h b
    have hb := h b
    rw [AdalyFormal.Balaban.BackgroundAveraging.Q1LM_apply] at hb
    exact (R0_apply_eq_zero_iff U _).mp hb
  · intro h b
    rw [AdalyFormal.Balaban.BackgroundAveraging.Q1LM_apply]
    have hb := h b
    show AdalyFormal.Balaban.BackgroundAveraging.R0 U
      (AdalyFormal.Balaban.BackgroundAveraging.qPrimeSuTwo
        AdmissibleSubspace.witnessEll A b) = 0
    rw [(show AdalyFormal.Balaban.BackgroundAveraging.qPrimeSuTwo
        AdmissibleSubspace.witnessEll A b = 0 from hb), map_zero]

/-- **`q1Kernel` is a CONSTANT function of the background.** -/
theorem q1Kernel_background_blind
    (U U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdmissibleSubspace.witnessL) :
    AdalyFormal.Balaban.BackgroundAveraging.q1Kernel U =
      AdalyFormal.Balaban.BackgroundAveraging.q1Kernel U' := by
  rw [q1Kernel_eq_ker_qPrimeSuTwoLM, q1Kernel_eq_ker_qPrimeSuTwoLM]

/-- Instantiated at the genuinely CURVED background built above: even nonzero curvature moves
nothing. -/
theorem q1Kernel_nonflatU_eq_trivialU (t : ℝ) :
    AdalyFormal.Balaban.BackgroundAveraging.q1Kernel (nonflatU t) =
      AdalyFormal.Balaban.BackgroundAveraging.q1Kernel
        (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU AdmissibleSubspace.witnessL) :=
  q1Kernel_background_blind _ _

/-- **THE FALSIFIABILITY CONTROL CANNOT FAIL INDEPENDENTLY.**
`BackgroundAveraging.deltaWitnessConfig_notMem_q1Kernel_witnessU` is advertised as a second check
reaching "the same conclusion, different reason". It is proved here to be LOGICALLY EQUIVALENT
to the `trivialU` check — the same check post-composed with an invertible map. Membership in
`q1Kernel` at any background is equivalent to membership at any other, for any field. -/
theorem control_witnessU_iff_trivialU (A : Bond AdmissibleSubspace.witnessL → SuTwo) :
    A ∈ AdalyFormal.Balaban.BackgroundAveraging.q1Kernel witnessU ↔
      A ∈ AdalyFormal.Balaban.BackgroundAveraging.q1Kernel
        (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU AdmissibleSubspace.witnessL) := by
  rw [q1Kernel_background_blind witnessU
    (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU AdmissibleSubspace.witnessL)]

/-! ## §9 — `frobSupBond` of the curved background: the `α₁` the regular-`U` results consume -/

theorem rotM_sub_one (t : ℝ) :
    rotM t - 1 = !![((rotA t - 1 : ℝ) : ℂ), ((rotB t : ℝ) : ℂ);
                    -((rotB t : ℝ) : ℂ), ((rotA t - 1 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotM, Matrix.one_apply] <;> push_cast <;> ring

theorem frobSq_rotM_sub_one (t : ℝ) :
    AdalyFormal.Balaban.RMapLipschitz.frobSq (rotM t - 1) = 8 * t ^ 2 / (1 + t ^ 2) := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [rotM_sub_one]
  simp only [AdalyFormal.Balaban.RMapLipschitz.frobSq, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.of_apply, Matrix.head_fin_const, Complex.normSq_ofReal, map_neg, neg_neg]
  simp only [Complex.normSq_neg, Complex.normSq_ofReal]
  unfold rotA rotB
  field_simp
  ring

theorem frobSupBond_nonflatU (t : ℝ) :
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond (nonflatU t) =
      Real.sqrt (8 * t ^ 2 / (1 + t ^ 2)) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro b _
    by_cases hb : b = (AdmissibleSubspace.witnessY, (0 : Fin 3))
    · rw [hb, nonflatU_at_x_mu, rotElem_coe,
        AdalyFormal.Balaban.RMapLipschitz.frobNorm, frobSq_rotM_sub_one]
    · rw [nonflatU_elsewhere t hb, AdalyFormal.Balaban.RMapLipschitz.frobNorm,
        show ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1 = 0 by
          simp,
        show AdalyFormal.Balaban.RMapLipschitz.frobSq 0 = 0 by
          simp [AdalyFormal.Balaban.RMapLipschitz.frobSq],
        Real.sqrt_zero]
      exact Real.sqrt_nonneg _
  · have hle := AdalyFormal.Balaban.RegularUPerturbation.frobNorm_le_frobSupBond (nonflatU t)
      (AdmissibleSubspace.witnessY, (0 : Fin 3))
    rwa [nonflatU_at_x_mu, rotElem_coe, AdalyFormal.Balaban.RMapLipschitz.frobNorm,
      frobSq_rotM_sub_one] at hle

theorem sqrt_eight_mul_sq (t : ℝ) : Real.sqrt (8 * t ^ 2) = 2 * Real.sqrt 2 * |t| := by
  have h8 : (8 : ℝ) = 2 ^ 2 * 2 := by norm_num
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8), Real.sqrt_sq_eq_abs, h8,
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ (2:ℝ) ^ 2), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-- **The small-`α₁` bound**: `α₁(nonflatU t) = sup_b ‖U(b) − 1‖_F ≤ 2√2·|t|`, so the curved
background lives in the perturbative regime `RegularUPerturbation`'s `[L2-AGG]` estimates
consume, with `α₁ → 0` as `t → 0` while the curvature stays nonzero for every `t ≠ 0`. -/
theorem frobSupBond_nonflatU_le (t : ℝ) :
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond (nonflatU t) ≤ 2 * Real.sqrt 2 * |t| := by
  rw [frobSupBond_nonflatU, ← sqrt_eight_mul_sq]
  exact Real.sqrt_le_sqrt (nonflatU_defect_le t)

/-! ## §10 — RE-INSTANTIATING A CONTAMINATED CONTROL AT NONZERO CURVATURE

`TheLemmaNormalized.check3_nonvacuous` is currently witnessed by the FLAT `pureGaugeU`. The
same existential is re-proved here at `nonflatU (1/4)` — defect `8·(1/16)/(1+1/16) = 8/17 < 1`,
comfortably inside the threshold — **with an extra clause asserting nonzero curvature**. Proved
in this file rather than edited into `TheLemmaNormalized.lean`, which is outside this lane's
write scope. -/

theorem quarter_defect_lt_one : 8 * (1/4 : ℝ) ^ 2 / (1 + (1/4 : ℝ) ^ 2) < 1 := by norm_num

/-! ## §12 — the curvature statements the tree already COULD have made but never did

`witnessU` and `centralHolonomyU` were curved all along; no declaration anywhere said so in the
`holonomyElem ≠ 1` form. Recorded here so the "no curved background exists in the tree" reading
of the sweep is not overstated: what was genuinely missing is a curved background admitted at a
SMALL threshold (`witnessU` sits at defect `4`, `centralHolonomyU` at `8`), which is `nonflatU`. -/

theorem witnessU_curvature_ne_one :
    holonomyElem witnessU witnessPlaquette ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [holonomy_witnessU_witnessPlaquette]
  exact witnessMElem_ne_one

theorem centralHolonomyU_curvature_ne_one :
    holonomyElem centralHolonomyU witnessPlaquette ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [holonomy_centralHolonomyU_witnessPlaquette]
  exact negOneElem_ne_one

/-- `defectOfElem witnessMElem = 4`: the generic §5 threshold reproduces
`TheLemmaNormalized.witnessU_isRegularHolonomy_four`'s constant, from the generic lemma rather
than the four-plaquette enumeration. -/
theorem defectOfElem_witnessMElem : defectOfElem witnessMElem = 4 := by
  unfold defectOfElem
  norm_num [witnessMElem, witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem witnessU_isRegularHolonomy_four' : IsRegularHolonomy witnessU (4 : ℝ) := by
  have h := singleBondU_isRegularHolonomy witnessMElem
  rwa [defectOfElem_witnessMElem, singleBondU_witnessMElem_eq_witnessU] at h

/-! ## §11 — axiom audit -/

#print axioms holonomyElem_periodicGaugeTransform
#print axioms holonomyElem_periodicGaugeTransform_eq_one_iff
#print axioms rotA_sq_add_rotB_sq
#print axioms rotM_mem
#print axioms rotElem_eq_one_iff
#print axioms nonflatU_zero_eq_trivial
#print axioms holonomyElem_nonflatU_witnessPlaquette
#print axioms nonflatU_curvature_ne_one
#print axioms nonflatU_has_curved_plaquette
#print axioms nonflatU_ne_trivialU
#print axioms nonflatU_not_gaugeTransform_of_flat
#print axioms defectOfElem_nonneg
#print axioms defectOfElem_inv
#print axioms holonomy_singleBondU_eq_one
#print axioms holonomy_singleBondU_trichotomy
#print axioms singleBondU_isRegularHolonomy
#print axioms singleBondU_not_isRegularHolonomy_of_lt
#print axioms defectOfElem_rotElem
#print axioms nonflatU_isRegularHolonomy
#print axioms nonflatU_not_isRegularHolonomy_of_lt
#print axioms nonflatU_defect_pos
#print axioms nonflatU_defect_le
#print axioms exists_curved_regular_below
#print axioms holonomyDefectSq_eq_zero_iff
#print axioms isRegularHolonomy_zero_iff_flat
#print axioms no_curved_regular_at_zero
#print axioms pureGaugeU_holonomy_eq_one
#print axioms pureGaugeU_holonomyDefectSq_eq_zero
#print axioms nonflatU_ne_pureGaugeU
#print axioms flat_but_link_ne_one
#print axioms RMap_apply_eq_zero_iff
#print axioms R0_apply_eq_zero_iff
#print axioms q1Kernel_eq_ker_qPrimeSuTwoLM
#print axioms q1Kernel_background_blind
#print axioms q1Kernel_nonflatU_eq_trivialU
#print axioms control_witnessU_iff_trivialU
#print axioms frobSq_rotM_sub_one
#print axioms frobSupBond_nonflatU
#print axioms frobSupBond_nonflatU_le
#print axioms witnessU_curvature_ne_one
#print axioms centralHolonomyU_curvature_ne_one
#print axioms defectOfElem_witnessMElem
#print axioms witnessU_isRegularHolonomy_four'

end AdalyFormal.Balaban.NonFlatBackground
