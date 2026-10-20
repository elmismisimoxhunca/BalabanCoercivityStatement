/-
Copyright (c) 2026 Project Adaly. All rights reserved.
-/
import AdalyFormal.Balaban.RegularUGamma0

/-!
# The COVARIANT coarse curl `∂'_V`, and the repaired `[SUMMED-TRANSFER-U]`

**Why this module exists.** `RegularUGamma0.SummedTransferRegularU` was registered
`CLAIM-UNATTACKED` by its own author with a named root cause: `ThirdLevelStokes.coarseCurlSuTwo` is
the FLAT four-term coarse curl, nothing transports it, and the tree contained no covariant coarse
curl at all (grep: no `coarseCurlCovariant`). The sharp consequence recorded there:
`RegularUGamma0.lineCoarseRestrictCov_one_eq_self` proves `Q_1(U) = id` for EVERY `U`, so at
`ell₀ = 1` that Prop's left-hand side is the FLAT curl energy of `B` and is `U`-independent while its
right-hand side is covariant — it would fail at any `B` with `∂_U B = 0 ≠ ∂B`.

This module builds the missing object and settles that case.

## What is built

* `coarseCurlCov hdvd V B` (§1) — the four-term coarse curl with adjoint transport by a COARSE link
  configuration `V`, mirroring `CovariantOperators.curlValueCovariant` term-for-term with
  `CoarseCurl.coarseShift` in place of `periodicLatticeShift` (which is exactly how
  `coarseCurlSuTwo` mirrors the flat curl). Parametric in `V`, so the definition itself fixes no
  denotation.
* `coarseBackground U ell` (§2) — the coarse link configuration TIED TO `U`: the holonomy of `U`
  along the straight `ell`-step segment of the coarse bond. No free data (S91), and
  `coarseBackground (trivialU) ell = 1`.
* **MUST-FIRE control** (§2): `coarseCurlCov hdvd (coarseBackground (trivialU L) ell) = coarseCurlSuTwo hdvd`
  — at `U = 1` the new object IS the existing flat one, so everything proved in `RegularUGamma0`
  about `coarseCurlSuTwo` at `U = 1` transfers unchanged.
* **MUST-NOT-FIRE control** (§5): the object is NOT secretly flat — its energy takes different
  values at `myTrivialU` and at `witnessU` on the same field, inherited from
  `CovariantHj.dstarDQuadForm_genuinely_U_dependent`.
* **The `ell = 1` identification** (§3): `coarseCurlCov hdvd₁ (coarseBackground U 1) (Q_1(U)A)` IS
  the fine covariant curl `curlValueCovariant U A`, for EVERY `U` — the coarse-bond/fine-bond and
  coarse-plaquette/fine-plaquette identifications at level `1` are bijections. Hence its energy is
  exactly `Δ_k` at `ell₀ = 1`.
* `SummedTransferRegularUCov` (§4) — `[SUMMED-TRANSFER-U]` restated over the covariant coarse curl,
  and `summedTransferCov_ell1`: **at `ell₀ = 1` it holds with `cT = 1`, as an EQUALITY, at every
  `U` and every `levels`.** That is precisely the case in which the flat statement was suspected
  false. So the `ell₀ = 1` defect was in the STATEMENT (a flat operator where a covariant one
  belongs), and it is repaired here; whether the restated Prop is true at `ell₀ ≥ 2` is open and
  untouched by this module.

## Denotation disclosure — read before using `coarseBackground` at `ell ≥ 2`

Bałaban's coarse background is produced by his block-spin construction (an averaging/minimization),
not by the straight-segment holonomy. `coarseBackground` is the straight-segment holonomy, chosen
because (i) it is a function of `U` alone, (ii) it is the SAME path family
(`Q1Real.straightSegment` = `List.replicate ell (μ, true)`) that `lineCoarseRestrictCov`'s own
transport uses, and (iii) it is the identity exactly when `U` is trivial. It is NOT
source-adjudicated as Bałaban's block spin, and no theorem below depends on it being one:
every theorem here is either parametric in `V` or lives at `ell = 1`, where the straight segment is
the single bond and `coarseBackground U 1 (y,μ) = U (y,μ)` (`coarseBackground_one`, proved).
-/

namespace AdalyFormal.Balaban.CoarseCurlCovariant

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond)
open AdalyFormal.Balaban.RegularUGamma0 (coarseCurlEnergySuTwo lineCoarseRestrictCov_one_eq_self
  covPlaqInner_self_eq_plaqEnergy)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the covariant coarse curl -/

/-- A COARSE link configuration: one `SU(2)` element per coarse bond. -/
abbrev CoarseLinkConfiguration (L : PeriodicLatticeExtent) (ell : ℕ) :=
  CoarseBond L ell → Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- **`(∂'_V B)(p')`** — the four-term coarse curl with adjoint transport, mirroring
`CovariantOperators.curlValueCovariant` term-for-term (`coarseShift` for `periodicLatticeShift`,
`V` for `U`), exactly as `ThirdLevelStokes.coarseCurlSuTwo` mirrors the flat curl (LAW-19: the
plaquette geometry and the `hdvd`-membership mechanism are the existing ones, unchanged). -/
noncomputable def coarseCurlCov {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : CoarseLinkConfiguration L ell) (B : CoarseBond L ell → SuTwo)
    (p : CoarsePlaquette L ell) : SuTwo :=
  B (p.1, p.2.1.1)
    + RMap (V (p.1, p.2.1.1))
        (B (⟨coarseShift p.1.1 ell p.2.1.1,
            coarseShift_mem_coarseLattice hdvd p.1.2 p.2.1.1⟩, p.2.1.2))
    - RMap (V (p.1, p.2.1.2))
        (B (⟨coarseShift p.1.1 ell p.2.1.2,
            coarseShift_mem_coarseLattice hdvd p.1.2 p.2.1.2⟩, p.2.1.1))
    - B (p.1, p.2.1.2)

/-- The covariant coarse-curl `L²` energy, written through `hsInner` exactly as
`RegularUGamma0.coarseCurlEnergySuTwo` is (same normalization, no new inner product). -/
noncomputable def coarseCurlEnergyCov {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : CoarseLinkConfiguration L ell) (B : CoarseBond L ell → SuTwo) : ℝ :=
  ∑ p : CoarsePlaquette L ell, hsInner (coarseCurlCov hdvd V B p) (coarseCurlCov hdvd V B p)

theorem coarseCurlEnergyCov_nonneg {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : CoarseLinkConfiguration L ell) (B : CoarseBond L ell → SuTwo) :
    0 ≤ coarseCurlEnergyCov hdvd V B :=
  Finset.sum_nonneg fun _ _ => hsInner_self_nonneg _

/-- The trivial coarse background. -/
noncomputable def trivialV (L : PeriodicLatticeExtent) (ell : ℕ) : CoarseLinkConfiguration L ell :=
  fun _ => 1

/-- **MUST-FIRE CONTROL (a): at `V = 1` the covariant coarse curl IS `coarseCurlSuTwo`.** -/
theorem coarseCurlCov_trivialV {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) :
    coarseCurlCov hdvd (trivialV L ell) B p = coarseCurlSuTwo hdvd B p := by
  unfold coarseCurlCov coarseCurlSuTwo trivialV
  rw [RMap_one]
  rfl

theorem coarseCurlEnergyCov_trivialV {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) :
    coarseCurlEnergyCov hdvd (trivialV L ell) B = coarseCurlEnergySuTwo hdvd B := by
  unfold coarseCurlEnergyCov coarseCurlEnergySuTwo
  exact Finset.sum_congr rfl fun p _ => by rw [coarseCurlCov_trivialV]

/-! ## §2 — the coarse background TIED TO `U`, and the `U = 1` reduction -/

/-- The straight `ell`-step forward segment in direction `μ` — the same path family as
`Q1Real.straightSegment` (`List.replicate … (μ, true)`), which is what `lineCoarseRestrictCov`'s own
transport is built from. -/
def coarseSegSteps (μ : Fin 3) (ell : ℕ) : List (Fin 3 × Bool) := List.replicate ell (μ, true)

/-- **The coarse background**: the holonomy of `U` along the coarse bond's straight segment. A
function of `U` alone — no free data. -/
noncomputable def coarseBackground
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ) :
    CoarseLinkConfiguration L ell :=
  fun c => periodicPathHolonomy U c.1.1 (coarseSegSteps c.2 ell)

theorem coarseBackground_trivialU (ell : ℕ) :
    coarseBackground (trivialU L) ell = trivialV L ell := by
  funext c
  exact AdalyFormal.Balaban.Q1Real.periodicPathHolonomy_trivialU_eq_one _ _

/-- **MUST-FIRE CONTROL (b): at `U = 1` the covariant coarse curl IS the flat `coarseCurlSuTwo`**,
so every `U = 1` theorem of `RegularUGamma0` about `coarseCurlSuTwo` transfers verbatim. -/
theorem coarseCurlCov_trivialU {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) :
    coarseCurlCov hdvd (coarseBackground (trivialU L) ell) B p = coarseCurlSuTwo hdvd B p := by
  rw [coarseBackground_trivialU]
  exact coarseCurlCov_trivialV hdvd B p

theorem coarseCurlEnergyCov_trivialU {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) :
    coarseCurlEnergyCov hdvd (coarseBackground (trivialU L) ell) B
      = coarseCurlEnergySuTwo hdvd B := by
  rw [coarseBackground_trivialU]
  exact coarseCurlEnergyCov_trivialV hdvd B

/-! ## §3 — `ell = 1`: the covariant coarse curl IS the fine covariant curl -/

theorem coarseSegSteps_one (μ : Fin 3) : coarseSegSteps μ 1 = [(μ, true)] := rfl

/-- At `ell = 1` the coarse background IS the fine link variable: `coarseBackground U 1 (y,μ) = U(y,μ)`. -/
theorem coarseBackground_one
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : CoarseBond L 1) : coarseBackground U 1 c = U (c.1.1, c.2) := by
  unfold coarseBackground
  rw [coarseSegSteps_one]
  show (if (true : Bool) then U (c.1.1, c.2) else _)
      * periodicPathHolonomy U (periodicLatticeStep c.1.1 (c.2, true)) [] = _
  rw [if_pos rfl]
  show U (c.1.1, c.2) * 1 = _
  rw [mul_one]

theorem coarseShift_one (y : PeriodicLatticeSite L) (μ : Fin 3) :
    coarseShift y 1 μ = periodicLatticeShift y μ := rfl

/-- **THE `ell = 1` IDENTIFICATION, EVERY BACKGROUND `U`**: the covariant coarse curl of `Q_1(U)A`
with the coarse background is the fine covariant curl of `A`. Uses
`RegularUGamma0.lineCoarseRestrictCov_one_eq_self` (`Q_1(U) = id`) and `coarseBackground_one`. -/
theorem coarseCurlCov_one_eq_curlCovariant
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd1 : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo) (p : CoarsePlaquette L 1) :
    coarseCurlCov hdvd1 (coarseBackground U 1) (lineCoarseRestrictCovLM U 1 A) p
      = curlValueCovariant U A ((p.1.1, p.2) : PeriodicLatticePlaquette L) := by
  unfold coarseCurlCov
  simp only [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_one_eq_self,
    coarseBackground_one]
  rfl

/-- The `ell = 1` coarse-plaquette type IS the fine-plaquette type. -/
theorem coarsePlaquette_one_bijective :
    Function.Bijective
      (fun p : CoarsePlaquette L 1 => ((p.1.1, p.2) : PeriodicLatticePlaquette L)) := by
  constructor
  · intro p p' h
    have h' : ((p.1.1, p.2) : PeriodicLatticePlaquette L) = ((p'.1.1, p'.2) : _) := h
    rw [Prod.mk.injEq] at h'
    rw [Prod.ext_iff]
    exact ⟨Subtype.ext h'.1, h'.2⟩
  · intro q
    exact ⟨(⟨q.1, AdalyFormal.Balaban.FourierFaithfulU1.mem_coarseLattice_one q.1⟩, q.2), rfl⟩

/-- **…hence the `ell = 1` covariant coarse-curl ENERGY is the fine covariant curl energy.** -/
theorem coarseCurlEnergyCov_one_eq_plaqEnergy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd1 : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    coarseCurlEnergyCov hdvd1 (coarseBackground U 1) (lineCoarseRestrictCovLM U 1 A)
      = plaqEnergy (curlCovariantLM U A) := by
  unfold coarseCurlEnergyCov plaqEnergy
  have hterm : ∀ p : CoarsePlaquette L 1,
      hsInner (coarseCurlCov hdvd1 (coarseBackground U 1) (lineCoarseRestrictCovLM U 1 A) p)
          (coarseCurlCov hdvd1 (coarseBackground U 1) (lineCoarseRestrictCovLM U 1 A) p)
        = ‖curlCovariantLM U A ((p.1.1, p.2) : PeriodicLatticePlaquette L)‖ ^ 2 := by
    intro p
    rw [coarseCurlCov_one_eq_curlCovariant, ← inner_eq_hsInner, real_inner_self_eq_norm_sq]
    rfl
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => hterm p)]
  exact Fintype.sum_bijective _ coarsePlaquette_one_bijective _ _ (fun _ => rfl)

/-- **…and that is exactly `Δ_k` at `ell₀ = 1`**, since the gauge-constraint subspace is `⊥` there
(`CovariantHjFaithful.deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm`). Every `U`, every
`levels`. -/
theorem coarseCurlEnergyCov_one_eq_deltaJ
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd1 : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    [(CovariantHjMinimizer.deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    coarseCurlEnergyCov hdvd1 (coarseBackground U 1) (lineCoarseRestrictCovLM U 1 B)
      = deltaJQuadFormCovFaithful 1 levels U B := by
  rw [coarseCurlEnergyCov_one_eq_plaqEnergy, deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm]
  change plaqEnergy (curlCovariantLM U B)
    = covPlaqInner (curlCovariantLM U B) (curlCovariantLM U B)
  rw [covPlaqInner_self_eq_plaqEnergy]

/-! ## §4 — `[SUMMED-TRANSFER-U]` RESTATED over the covariant coarse curl, and its `ell₀ = 1` case -/

/-- **`[SUMMED-TRANSFER-U-COV]`** — the general-`U` transfer stated over the COVARIANT coarse curl,
with `cT` and the regularity threshold `α₀` quantified OUTSIDE `L`, `ell₀`, `U`, `levels`, `B`, and
the coarse background tied to `U` (no free data). This is `RegularUGamma0.SummedTransferRegularU`
with its named root cause removed. OPEN at `ell₀ ≥ 2`; PROVED at `ell₀ = 1` below. -/
def SummedTransferRegularUCov : Prop :=
  ∃ cT α₀ : ℝ, 0 < cT ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent) (ell₀ : ℕ), 0 < ell₀ →
      ∀ (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
        (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ (levels : List (KernelSubspace.Level L))
          [(CovariantHjMinimizer.deltaKernelImageCovH U levels).HasOrthogonalProjection]
          [(curlImageCovHFaithful ell₀ levels U).HasOrthogonalProjection]
          (B : Bond L → SuTwo),
          cT * coarseCurlEnergyCov hdvd₀ (coarseBackground U ell₀)
              (lineCoarseRestrictCovLM U ell₀ B)
            ≤ deltaJQuadFormCovFaithful ell₀ levels U B

/-- **THE `ell₀ = 1` CASE OF THE RESTATED PRIMITIVE, PROVED WITH `cT = 1`, AT EVERY `U`** — and as
an EQUALITY, not an inequality.

This is exactly the case in which the FLAT statement `RegularUGamma0.SummedTransferRegularU` was
recorded as possibly false (`Q_1(U) = id` makes its left-hand side the `U`-independent flat curl
energy while its right-hand side is covariant). So at `ell₀ = 1` the defect was in the STATEMENT —
a flat operator where a covariant one belongs — and the covariant statement is not merely repaired
but sharp. Nothing here bears on `ell₀ ≥ 2`. -/
theorem summedTransferCov_ell1
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd1 : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1))
    (levels : List (KernelSubspace.Level L))
    [(CovariantHjMinimizer.deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    (1 : ℝ) * coarseCurlEnergyCov hdvd1 (coarseBackground U 1) (lineCoarseRestrictCovLM U 1 B)
      ≤ deltaJQuadFormCovFaithful 1 levels U B := by
  rw [one_mul]
  exact le_of_eq (coarseCurlEnergyCov_one_eq_deltaJ U hdvd1 levels B)

/-! ## §5 — MUST-NOT-FIRE: the covariant coarse curl is NOT secretly the flat one -/

/-- **The new object genuinely depends on the background.** Same field, same lattice, same level;
two backgrounds; different covariant coarse-curl energies. Inherited from
`CovariantHj.dstarDQuadForm_genuinely_U_dependent` through the `ell = 1` identification, so this
control cannot pass by accident of the identification itself. -/
theorem coarseCurlEnergyCov_genuinely_background_dependent :
    coarseCurlEnergyCov (L := AdmissibleSubspace.witnessL) (fun _ => one_dvd _)
        (coarseBackground myTrivialU 1) (lineCoarseRestrictCovLM myTrivialU 1 myWitnessConfig)
      ≠ coarseCurlEnergyCov (L := AdmissibleSubspace.witnessL) (fun _ => one_dvd _)
        (coarseBackground witnessU 1) (lineCoarseRestrictCovLM witnessU 1 myWitnessConfig) := by
  rw [coarseCurlEnergyCov_one_eq_plaqEnergy, coarseCurlEnergyCov_one_eq_plaqEnergy]
  intro hc
  refine dstarDQuadForm_genuinely_U_dependent ?_
  change covPlaqInner (curlCovariantLM myTrivialU myWitnessConfig)
      (curlCovariantLM myTrivialU myWitnessConfig)
    = covPlaqInner (curlCovariantLM witnessU myWitnessConfig)
      (curlCovariantLM witnessU myWitnessConfig)
  rw [covPlaqInner_self_eq_plaqEnergy, covPlaqInner_self_eq_plaqEnergy]
  exact hc

/-! ## §A — AXIOM AUDIT: `#print axioms` on EVERY declaration of this module (22 of them) -/

#print axioms CoarseLinkConfiguration
#print axioms coarseCurlCov
#print axioms coarseCurlEnergyCov
#print axioms coarseCurlEnergyCov_nonneg
#print axioms trivialV
#print axioms coarseCurlCov_trivialV
#print axioms coarseCurlEnergyCov_trivialV
#print axioms coarseSegSteps
#print axioms coarseBackground
#print axioms coarseBackground_trivialU
#print axioms coarseCurlCov_trivialU
#print axioms coarseCurlEnergyCov_trivialU
#print axioms coarseSegSteps_one
#print axioms coarseBackground_one
#print axioms coarseShift_one
#print axioms coarseCurlCov_one_eq_curlCovariant
#print axioms coarsePlaquette_one_bijective
#print axioms coarseCurlEnergyCov_one_eq_plaqEnergy
#print axioms coarseCurlEnergyCov_one_eq_deltaJ
#print axioms SummedTransferRegularUCov
#print axioms summedTransferCov_ell1
#print axioms coarseCurlEnergyCov_genuinely_background_dependent

end AdalyFormal.Balaban.CoarseCurlCovariant
