/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKFull

set_option autoImplicit false

/-!
# `Δ_k(U)` as a genuine operator — the covariant curl Gram operator `D_U^1* D_U^1`

**Dispatch target (CHARACTERIZE-THEN-BUILD)**: build the `U`-carrying kinetic operator the regular-`U`
coercivity construction funnels through — CMP99b (3.10) p.392's `⟨A,D*DA⟩` term, `Δ₁(U) := D_U^{1*}
D_U^1`, the covariant curl Laplacian — as a genuine `(Bond L → SuTwo) →L[ℝ] (Bond L → SuTwo)`
operator. This is the object `DeltaKFull.lean` §7 named as its load-bearing missing residual (the
covariant curl adjoint `D_U^{1*}`) and left "not attempted." **Denotation, stated precisely (the
prosecution surface):** this is the FINE object of (3.10)/(3.159)'s inner Gaussian
`exp[−½⟨A,(Δ+Δ⁽²⁾)A⟩]`, NOT literally (3.156)'s COARSE `(QG₁Q*)⁻¹` (which additionally carries the
block-averaging `Q` and the harmonic extension `H₁` — encoded separately by
`CovariantHjMinimizer.deltaJQuadFormCov = ‖D_U H_j^{cov}(U)B‖²`). `D_U^{1*}D_U^1` is precisely the
`D*D` summand of the fine operator whose Green's function enters (3.156).
⚠ CORRECTED 2026-07-25 (prosecutor QUALIFIED): the earlier "`G₁ = (D*D + Δ' + …)⁻¹` … `D*D` is the kinetic
core, and (3.156)'s coarse operator is built FROM it by the RG steps" OVERSTATES derivational primacy.
Image-read (CMP99b p.421 (3.128)-(3.130)): `G₀ = (Δ + DRD* + Q*aQ)⁻¹` and `G = G₀(I − Δ'_π G₀)⁻¹` — the
transport `R` (`DRD*`) and averaging `Q` (`Q*aQ`) enter `G₀⁻¹` at the SAME defining level as `D*D`, NOT as
later corrections; `G₁` is a further nested Schur/constrained-variational chain (quad-form on the transformed
argument `A − DG'RD*A` plus `‖RD*A‖²`, `a‖QA‖²`). So `D_U*D_U` is a GENUINE INGREDIENT of the fine operator
(inside `Δ` inside `G₀⁻¹`) — but NOT the privileged "core" the coarse `(QG₁Q*)⁻¹` is "built from"; controlling
the `D*D`/`R`/`Q` ENTANGLEMENT is the whole content of pp.420-428. What is honestly built here: a genuine,
U-dependent covariant curl-Laplacian `D_U*D_U`, one term of that chain.

## Characterization (image-verified, `compute/deltaku/NOTES.md`, `compute/gamma0_assembly_check/`)

CMP99b p.428 (3.156), VERBATIM: `⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩ = ⟨B,Δ_kB⟩`, on the
constrained subspace `{B=0 on Λᶜ, B=0 on ∪Ax(y), Q₁B=0}`. The `U`-dependence enters through the
covariant averaging `Q(U)`, covariant Green's function `G₁(U)`, and harmonic extension `H₁(U)`. The
project's faithful encoding of the LEADING term `⟨B,(QG₁Q*)⁻¹B⟩` is the min-curl (Schur) form
`‖D_U H_j^{cov}(U)B‖²` (`CovariantHjMinimizer.deltaJQuadFormCov`, §13), and CMP99b (3.10) p.392
gives the assembled fine object `⟨A,ΔA⟩ = ⟨A,D*DA⟩ + ⟨A,Δ'A⟩` (`DeltaKFull.deltaKQuadFormCorrected`).

**This file builds the `⟨A,D*DA⟩` term AS AN OPERATOR** — `Δ₁(U) := D_U^1* D_U^1`, the covariant
curl Laplacian on bonds, whose quadratic form is `CovariantHj.dstarDQuadForm` (the leading term).
The `Δ'` piece (`DeltaKFull` Residual 2) and the `−a`-shift / `J`-source pieces of the FULL (3.156)
`Δ_k(U)` are separate, named residuals; `DeltaKFull.deltaKFullCLM_assembly_sound` already proved the
assembly logic `⟨A,(T1+T2)A⟩ = deltaKQuadFormCorrected` given both operator terms — this file
supplies the `T1` (`D*D`) term it named.

## What is genuinely `U`-dependent (the `Δ_nonconstant` requirement)

`D_U^1 = curlValueCovariant U` carries `U` through `RMap (U b)` (adjoint transport); `Δ₁(U)` is
proved genuinely `U`-varying at the NON-CENTRAL witness `witnessMElem` (`Ad ≠ id`, `DeltaKFull` §2),
reusing the already-banked witness, satisfying the shape `Coercivity.CoercivityHypothesis` demands.

## Method (§6-wall avoidance)

`.adjoint`/`LinearMap.adjoint`/`toDual` are ALL blocked by the ambient-vs-norm PiLp instance diamond
(`DeltaKFull` §6; re-confirmed this dispatch — `LinearMap.adjoint` fails at the Module-instance
level). This file builds the adjoint by HAND as an explicit combinatorial covariant co-differential
`curlCovariantAdjointValue` (the exact template of `CovariantHjMinimizer.lean` §5's
`gradCovariantAdjointValue`), proves the Gram identity `covPlaqInner (D_U A) F = covBondInner A
(D_U^* F)` by index reindexing (never `.adjoint`), then composes at `LinearMap` level and promotes
to a `ContinuousLinearMap` on the BARE type via `LinearMap.toContinuousLinearMap` (finite dim),
exactly the `RcovCLM`/`siteLaplacianCovLM` route.
-/

namespace AdalyFormal.Balaban.DeltaKU

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.CovariantHj
  AdalyFormal.Balaban.CovariantHjMinimizer AdalyFormal.Balaban.AdmissibleSubspace

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the covariant curl adjoint `D_U^{1*}` (the co-differential `∂₁*` covariantized)

Derived by hand (`compute/deltaku/NOTES.md` §5): for bond `(x,τ)`, the four `curlValueCovariant`
sub-terms `A(z,μ) + R(U(z,μ))A(shift_μz,ν) − R(U(z,ν))A(shift_νz,μ) − A(z,ν)` each contribute to
`(D_U^*F)(x,τ)`, split by whether `τ` plays the SMALLER (`τ<σ`) or LARGER (`σ<τ`) plaquette
direction. -/

/-- **`(D_U^{1*}F)(x,τ)`**, the explicit covariant curl-adjoint. `τ` as smaller direction `μ`
contributes `+F(x,(τ,σ)) − R(U(shiftBack_σx,σ))⁻¹F(shiftBack_σx,(τ,σ))` over `σ>τ`; `τ` as larger
direction `ν` contributes `−F(x,(σ,τ)) + R(U(shiftBack_σx,σ))⁻¹F(shiftBack_σx,(σ,τ))` over `σ<τ`. -/
noncomputable def curlCovariantAdjointValue
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (F : PeriodicLatticePlaquette L → SuTwo) (b : Bond L) : SuTwo :=
  (∑ σ : Fin 3, if hlt : b.2 < σ then
      F (b.1, ⟨(b.2, σ), hlt⟩) -
        RMap (U (periodicLatticeShiftBack b.1 σ, σ))⁻¹
          (F (periodicLatticeShiftBack b.1 σ, ⟨(b.2, σ), hlt⟩))
    else 0)
  + (∑ σ : Fin 3, if hlt : σ < b.2 then
      RMap (U (periodicLatticeShiftBack b.1 σ, σ))⁻¹
          (F (periodicLatticeShiftBack b.1 σ, ⟨(σ, b.2), hlt⟩)) -
        F (b.1, ⟨(σ, b.2), hlt⟩)
    else 0)

theorem curlCovariantAdjointValue_add
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (F G : PeriodicLatticePlaquette L → SuTwo) (b : Bond L) :
    curlCovariantAdjointValue U (F + G) b =
      curlCovariantAdjointValue U F b + curlCovariantAdjointValue U G b := by
  simp only [curlCovariantAdjointValue, Pi.add_apply, map_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> abel

theorem curlCovariantAdjointValue_smul
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (c : ℝ) (F : PeriodicLatticePlaquette L → SuTwo) (b : Bond L) :
    curlCovariantAdjointValue U (c • F) b = c • curlCovariantAdjointValue U F b := by
  simp only [curlCovariantAdjointValue, Pi.smul_apply, map_smul]
  rw [smul_add, Finset.smul_sum, Finset.smul_sum]
  congr 1 <;>
    (apply Finset.sum_congr rfl; intro σ _; split_ifs <;> simp [smul_sub])

/-- **`D_U^{1*}` as a genuine `LinearMap`** (bare pairing). -/
noncomputable def curlCovariantAdjointLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (PeriodicLatticePlaquette L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) where
  toFun F := curlCovariantAdjointValue U F
  map_add' F G := by funext b; exact curlCovariantAdjointValue_add U F G b
  map_smul' c F := by funext b; exact curlCovariantAdjointValue_smul U c F b

theorem curlCovariantAdjointLM_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (F : PeriodicLatticePlaquette L → SuTwo) :
    curlCovariantAdjointLM U F = curlCovariantAdjointValue U F := rfl

#print axioms curlCovariantAdjointValue_add
#print axioms curlCovariantAdjointValue_smul
#print axioms curlCovariantAdjointLM_apply

/-! ## §2 — the operator `Δ₁(U) := D_U^{1*} D_U^1`, a genuine `ContinuousLinearMap`

Composed at `LinearMap` level then promoted via `LinearMap.toContinuousLinearMap` on the BARE
finite-dimensional type (the `curlCovariantCLM`/`gradCovariantCLM`/`RcovCLM` route — NEVER
`.adjoint`, §6-walled). Carrier `H := Bond L → SuTwo`. The `k` index matches
`Coercivity.CoercivityHypothesis.Δ : ℕ → Uconfig → H →L[ℝ] H`'s scale slot; at this unit-lattice
fine-Laplacian level the curl is scale-independent (the `k`-dependence of the FULL `Δ_k(U)` lives in
the coarse `Q(U)`/`G₁(U)`, a separate/deferred residual, see the module docstring). -/

/-- **`Δ₁(U)` as a `LinearMap`**: `D_U^{1*} ∘ D_U^1`. -/
noncomputable def deltaKUCurlLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) :=
  (curlCovariantAdjointLM U).comp (curlCovariantLM U)

/-- **`Δ₁(U)` as a genuine `ContinuousLinearMap`** on `Bond L → SuTwo`, `U`-carrying. -/
noncomputable def deltaKUOp
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →L[ℝ] (Bond L → SuTwo) :=
  LinearMap.toContinuousLinearMap (deltaKUCurlLM U)

/-- **Field-shaped alias** with the SHAPE of `Coercivity.CoercivityHypothesis.Δ : ℕ → Uconfig →
H →L[ℝ] H` (`H := Bond L → SuTwo`, `Uconfig := PeriodicLinkConfiguration (SU(2)) L`). **Wiring
caveat, stated (not papered):** the BARE carrier `Bond L → SuTwo` carries `NormedSpace ℝ`
(`→L[ℝ]` works, `toContinuousLinearMap` route) but NOT `InnerProductSpace ℝ` (measured:
`#synth InnerProductSpace ℝ (Bond L → SuTwo)` FAILS — the sup-norm `Pi` instance, which is exactly
why the fresh `BondFnL2 L := PiLp 2 …` type exists). So `deltaKField` does NOT *directly* inhabit
`CoercivityHypothesis.Δ`, which requires `[InnerProductSpace ℝ H]`. Wiring it needs EITHER (a)
transporting `deltaKUOp` to a `BondFnL2 →L BondFnL2` CLM (the `toCLM`-on-`BondFnL2` step, blocked by
the §6/§8e ambient-vs-norm PiLp diamond — a named formalization residual, NOT open math), OR (b)
restating `CoercivityHypothesis`'s `coercive` field over the bare pairing `covBondInner` (against
which `deltaKUOp_quadForm` is already stated). The genuine `U`-dependence (`deltaKU_nonconstant`) and
faithful quad form (`deltaKUOp_quadForm`) are carrier-independent facts that hold as built. -/
noncomputable def deltaKField (_k : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →L[ℝ] (Bond L → SuTwo) :=
  deltaKUOp U

theorem deltaKUOp_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    deltaKUOp U A = curlCovariantAdjointValue U (curlValueCovariant U A) := rfl

#print axioms deltaKUCurlLM
#print axioms deltaKUOp
#print axioms deltaKField

/-! ## §3 — U=1 CONSISTENCY: at `trivialU` the transport `RMap 1 = id` drops out, so `deltaKUOp (1)` is
the FLAT curl-Laplacian `∂₁* ∂₁` (`‖curlCLM A‖²` in quad-form) — proved here (`deltaKUOp_trivialU`,
`curlValueCovariant_trivialU`).

⚠ CORRECTED 2026-07-25 (prosecutor QUALIFIED, commit 5f6e184f): the earlier claim that this "is the
free-sector object the abelian `deltaJOp`/`deltaJQuadForm` encode one carrier down" is RETRACTED — it was
unproven AND false. `HjMinimizer.deltaJQuadForm = ‖curlCLM (hjExtension …)‖²` is the SCHUR-COMPLEMENTED,
HARMONIC-EXTENDED (coarse) form (built through `hjExtension`), NOT the bare flat `‖curlCLM A‖²`; and the
carriers differ (`Bond L → SuTwo` vs `EuclideanSpace ℝ (Bond L)`, no bridge). So the U=1 reduction proved
here lands on the FLAT curl-Laplacian, which is NOT `deltaJQuadForm`. No theorem states
`deltaKUOp (trivialU) = deltaJOp …` and none should — they are different objects. -/

/-- **`D_U^1` at `U=1` is the flat curl** (no transport factors). -/
theorem curlValueCovariant_trivialU (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    curlValueCovariant (trivialU L) A p =
      A (p.1, p.2.1.1) + A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) -
        A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.2) := by
  simp only [curlValueCovariant, trivialU, RMap_one, LinearMap.id_coe, id_eq]

/-- **`D_U^{1*}` at `U=1` is the flat curl adjoint** (no transport factors); `1⁻¹ = 1` and
`RMap 1 = id`. -/
theorem curlCovariantAdjointValue_trivialU (F : PeriodicLatticePlaquette L → SuTwo) (b : Bond L) :
    curlCovariantAdjointValue (trivialU L) F b =
      (∑ σ : Fin 3, if hlt : b.2 < σ then
          F (b.1, ⟨(b.2, σ), hlt⟩) - F (periodicLatticeShiftBack b.1 σ, ⟨(b.2, σ), hlt⟩)
        else 0)
      + (∑ σ : Fin 3, if hlt : σ < b.2 then
          F (periodicLatticeShiftBack b.1 σ, ⟨(σ, b.2), hlt⟩) - F (b.1, ⟨(σ, b.2), hlt⟩)
        else 0) := by
  simp only [curlCovariantAdjointValue, trivialU, inv_one, RMap_one, LinearMap.id_coe, id_eq]

/-- **`Δ₁(1) = ∂₁*∂₁` acts as the flat curl-Laplacian** (the U=1 consistency, at operator level). -/
theorem deltaKUOp_trivialU_apply (A : Bond L → SuTwo) (b : Bond L) :
    deltaKUOp (trivialU L) A b =
      (∑ σ : Fin 3, if hlt : b.2 < σ then
          curlValueCovariant (trivialU L) A (b.1, ⟨(b.2, σ), hlt⟩) -
            curlValueCovariant (trivialU L) A (periodicLatticeShiftBack b.1 σ, ⟨(b.2, σ), hlt⟩)
        else 0)
      + (∑ σ : Fin 3, if hlt : σ < b.2 then
          curlValueCovariant (trivialU L) A (periodicLatticeShiftBack b.1 σ, ⟨(σ, b.2), hlt⟩) -
            curlValueCovariant (trivialU L) A (b.1, ⟨(σ, b.2), hlt⟩)
        else 0) := by
  rw [deltaKUOp_apply, curlCovariantAdjointValue_trivialU]

#print axioms curlValueCovariant_trivialU
#print axioms curlCovariantAdjointValue_trivialU
#print axioms deltaKUOp_trivialU_apply

/-! ## §4 — the Gram identity certifying `curlCovariantAdjointValue = D_U^{1*}`, and the two
load-bearing checks (quadratic-form faithfulness + genuine `U`-dependence) it unlocks

The Gram identity `covPlaqInner (D_U^1 A) F = covBondInner A (D_U^{1*} F)` is what CERTIFIES the
hand-built `curlCovariantAdjointValue` really is the adjoint of the covariant curl (the property
CMP99b p.391 names but never writes out). It is the exact analogue of
`CovariantHjMinimizer.covBondInner_gradValueCovariant_eq_covSiteInner` (§5, the SITE↔BOND gradient),
one index type over (BOND↔PLAQUETTE). -/

/-- **Direction enumeration** for the plaquette-direction subtype (`Fin 3` has exactly the three
ordered pairs `(0,1),(0,2),(1,2)`) — a reusable helper for plaquette sums. -/
theorem sum_plaqDir {M : Type*} [AddCommMonoid M] (h : PeriodicPlaquetteDirections → M) :
    ∑ d : PeriodicPlaquetteDirections, h d =
      h ⟨(0, 1), by decide⟩ + (h ⟨(0, 2), by decide⟩ + h ⟨(1, 2), by decide⟩) := by
  have hu : (Finset.univ : Finset PeriodicPlaquetteDirections) =
      {⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]

#print axioms sum_plaqDir

/-- **Direction reindex (`τ<σ` family)**: `∑_τ∑_σ [τ<σ] g τ σ = ∑_{d:PlaqDir} g d.1.1 d.1.2` —
dependent in the `τ<σ` proof (to construct the plaquette index `⟨(τ,σ),h⟩`). -/
theorem dir_reindex_lt_dep {M : Type*} [AddCommMonoid M] (g : (τ σ : Fin 3) → τ < σ → M) :
    ∑ τ : Fin 3, ∑ σ : Fin 3, (if h : τ < σ then g τ σ h else 0) =
      ∑ d : PeriodicPlaquetteDirections, g d.1.1 d.1.2 d.2 := by
  rw [sum_plaqDir (fun d => g d.1.1 d.1.2 d.2)]
  simp only [Fin.sum_univ_three]; norm_num [Fin.lt_def]; try abel

/-- **Direction reindex (`σ<τ` family)**: `∑_τ∑_σ [σ<τ] g τ σ = ∑_{d:PlaqDir} g d.1.2 d.1.1`. -/
theorem dir_reindex_gt_dep {M : Type*} [AddCommMonoid M] (g : (τ σ : Fin 3) → σ < τ → M) :
    ∑ τ : Fin 3, ∑ σ : Fin 3, (if h : σ < τ then g τ σ h else 0) =
      ∑ d : PeriodicPlaquetteDirections, g d.1.2 d.1.1 d.2 := by
  rw [sum_plaqDir (fun d => g d.1.2 d.1.1 d.2)]
  simp only [Fin.sum_univ_three]; norm_num [Fin.lt_def]; try abel

/-- **Site-shift reindex** (the `inflow_sum_reindex` pattern, `Equiv.sum_comp`): reindexes the two
TRANSPORTED curl families by the direction-`μ` site shift, moving the shift from the `A`-argument
onto the `RMap`/`F`-arguments as a backward shift. This is the crux of the adjoint identity. -/
theorem transp_reindex
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (F : PeriodicLatticePlaquette L → SuTwo) (μ ν : Fin 3)
    (d : PeriodicPlaquetteDirections) :
    ∑ z : PeriodicLatticeSite L,
        hsInner (A (periodicLatticeShift z μ, ν)) (RMap (U (z, μ))⁻¹ (F (z, d))) =
      ∑ x : PeriodicLatticeSite L,
        hsInner (A (x, ν))
          (RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (F (periodicLatticeShiftBack x μ, d))) := by
  rw [← Equiv.sum_comp (periodicLatticeShiftEquiv μ)
    (fun x => hsInner (A (x, ν))
      (RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (F (periodicLatticeShiftBack x μ, d))))]
  exact Finset.sum_congr rfl (fun z _ => by
    simp only [periodicLatticeShiftEquiv_apply, periodicLatticeShiftBack_shift])

theorem hsInner_zero_right (X : SuTwo) : hsInner X 0 = 0 := by
  have := hsInner_sub_right X 0 0; simpa using this

theorem hsInner_add_right (X Y Z : SuTwo) : hsInner X (Y + Z) = hsInner X Y + hsInner X Z := by
  rw [hsInner_symm X, hsInner_add_left, hsInner_symm Y X, hsInner_symm Z X]

/-- Pushes `hsInner` through the `dite` used by `curlCovariantAdjointValue`. -/
theorem hsInner_dite {c : Prop} [Decidable c] (X : SuTwo) (f : c → SuTwo) :
    hsInner X (dite c f (fun _ => 0)) = dite c (fun h => hsInner X (f h)) (fun _ => 0) := by
  split_ifs with h
  · rfl
  · exact hsInner_zero_right X

#print axioms dir_reindex_lt_dep
#print axioms dir_reindex_gt_dep
#print axioms transp_reindex
#print axioms hsInner_dite

/-- **THE GRAM IDENTITY — `D_U^{1*}` really is the adjoint of `D_U^1`** w.r.t. the bare pairings
`covPlaqInner`/`covBondInner`, PROVED, avoiding entirely the `.adjoint`/`toDual` route (§6-walled).
This is the object CMP99b p.391 names ("adjoint operators to derivatives `D`... w.r.t. natural `L²`
scalar products") but never writes out, and the load-bearing residual `DeltaKFull.lean` §7 left "not
attempted" — now built and closed.

**Proof** (full hand-derivation, `compute/deltaku/NOTES.md` §5): expand
`covPlaqInner (curl U A) F = ∑_p hsInner(curl U A p, F p)` (`Fintype.sum_prod_type`), split `curl`'s
four sub-terms (`hsInner_sub_left`/`hsInner_add_left`), apply `hsInner_RMap_transpose` to the two
TRANSPORTED terms (moving `R(U(z,μ))` from the left slot to `R(U(z,μ))⁻¹` on the right), reindex the
two shifted-site families by `transp_reindex` (`Equiv.sum_comp`); on the other side expand
`covBondInner A (D_U^*F)`, distribute `hsInner` through the `σ`-sums and `dite`s
(`hsInner_sum_right`/`hsInner_dite`/`hsInner_sub_right`) and collapse the direction sums with
`dir_reindex_lt_dep`/`dir_reindex_gt_dep`. Both sides reduce to the same `∑_x∑_d` four-term form. -/
theorem covPlaqInner_curlValueCovariant_eq_covBondInner
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (F : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner (curlValueCovariant U A) F =
      covBondInner A (curlCovariantAdjointValue U F) := by
  have hL : covPlaqInner (curlValueCovariant U A) F =
      ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L,
        ( hsInner (A (x, d.1.1)) (F (x, d))
          + hsInner (A (x, d.1.2))
              (RMap (U (periodicLatticeShiftBack x d.1.1, d.1.1))⁻¹ (F (periodicLatticeShiftBack x d.1.1, d)))
          - hsInner (A (x, d.1.1))
              (RMap (U (periodicLatticeShiftBack x d.1.2, d.1.2))⁻¹ (F (periodicLatticeShiftBack x d.1.2, d)))
          - hsInner (A (x, d.1.2)) (F (x, d)) ) := by
    rw [covPlaqInner, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d _
    have expand : ∀ z : PeriodicLatticeSite L,
        hsInner (curlValueCovariant U A (z, d)) (F (z, d)) =
          hsInner (A (z, d.1.1)) (F (z, d))
          + hsInner (RMap (U (z, d.1.1)) (A (periodicLatticeShift z d.1.1, d.1.2))) (F (z, d))
          - hsInner (RMap (U (z, d.1.2)) (A (periodicLatticeShift z d.1.2, d.1.1))) (F (z, d))
          - hsInner (A (z, d.1.2)) (F (z, d)) := by
      intro z; simp only [curlValueCovariant, hsInner_sub_left, hsInner_add_left]
    have e2 : ∑ z, hsInner (RMap (U (z, d.1.1)) (A (periodicLatticeShift z d.1.1, d.1.2))) (F (z, d)) =
        ∑ x, hsInner (A (x, d.1.2))
          (RMap (U (periodicLatticeShiftBack x d.1.1, d.1.1))⁻¹ (F (periodicLatticeShiftBack x d.1.1, d))) := by
      simp_rw [hsInner_RMap_transpose]; exact transp_reindex U A F d.1.1 d.1.2 d
    have e3 : ∑ z, hsInner (RMap (U (z, d.1.2)) (A (periodicLatticeShift z d.1.2, d.1.1))) (F (z, d)) =
        ∑ x, hsInner (A (x, d.1.1))
          (RMap (U (periodicLatticeShiftBack x d.1.2, d.1.2))⁻¹ (F (periodicLatticeShiftBack x d.1.2, d))) := by
      simp_rw [hsInner_RMap_transpose]; exact transp_reindex U A F d.1.2 d.1.1 d
    rw [Finset.sum_congr rfl (fun z _ => expand z),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, e2, e3,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hR : covBondInner A (curlCovariantAdjointValue U F) =
      ∑ x : PeriodicLatticeSite L, ∑ d : PeriodicPlaquetteDirections,
        ( ( hsInner (A (x, d.1.1)) (F (x, d))
          - hsInner (A (x, d.1.1))
              (RMap (U (periodicLatticeShiftBack x d.1.2, d.1.2))⁻¹ (F (periodicLatticeShiftBack x d.1.2, d))) )
          + ( hsInner (A (x, d.1.2))
              (RMap (U (periodicLatticeShiftBack x d.1.1, d.1.1))⁻¹ (F (periodicLatticeShiftBack x d.1.1, d)))
            - hsInner (A (x, d.1.2)) (F (x, d)) ) ) := by
    rw [covBondInner, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro x _
    simp only [curlCovariantAdjointValue, hsInner_add_right, hsInner_sum_right, hsInner_dite,
      hsInner_sub_right]
    rw [Finset.sum_add_distrib, dir_reindex_lt_dep, dir_reindex_gt_dep, ← Finset.sum_add_distrib]
  rw [hL, hR, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro x _
  abel

/-- **QUADRATIC-FORM FAITHFULNESS (Check 1)**: `⟨A, Δ₁(U)A⟩ = ‖D_U^1 A‖² = dstarDQuadForm U A` — the
LEADING term of CMP99b (3.156)/(3.10), i.e. `Δ₁(U) = D_U^{1*}D_U^1` genuinely REPRESENTS the covariant
curl energy as an OPERATOR. Proved from the Gram identity (with `F := D_U^1 A`). -/
theorem deltaKUOp_quadForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    covBondInner A (deltaKUOp U A) = dstarDQuadForm U A := by
  rw [deltaKUOp_apply, dstarDQuadForm]
  rw [← covPlaqInner_curlValueCovariant_eq_covBondInner U A (curlValueCovariant U A)]

/-- **GENUINE `U`-DEPENDENCE (Check 2 — the `Δ_nonconstant` shape)**: `Δ₁(U)` genuinely varies in
`U` — at the NON-CENTRAL witness (`Ad(witnessMElem) ≠ id`, `DeltaKFull` §2), the operator at
`myTrivialU` differs from the operator at `witnessU`. Proved from Check 1 plus the already-banked
`CovariantHj.dstarDQuadForm_genuinely_U_dependent`. This is exactly the shape
`Coercivity.CoercivityHypothesis.Δ_nonconstant` / `Spine.coerc_u_main`'s `Δ_nonconstant` field
requires, and which the convicted `deltaJOp` (`U`-independent) structurally could NOT satisfy. -/
theorem deltaKUOp_genuinely_U_dependent :
    deltaKUOp (L := AdmissibleSubspace.witnessL) myTrivialU ≠ deltaKUOp witnessU := by
  intro hcon
  apply dstarDQuadForm_genuinely_U_dependent
  rw [← deltaKUOp_quadForm myTrivialU myWitnessConfig,
    ← deltaKUOp_quadForm witnessU myWitnessConfig, hcon]

/-- **`Δ_nonconstant` in the exact existential shape the structure field demands.** -/
theorem deltaKU_nonconstant :
    ∃ (k : ℕ) (U₁ U₂ : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
        AdmissibleSubspace.witnessL),
      U₁ ≠ U₂ ∧ deltaKField k U₁ ≠ deltaKField k U₂ := by
  refine ⟨0, myTrivialU, witnessU, ?_, ?_⟩
  · intro h
    apply dstarDQuadForm_genuinely_U_dependent
    rw [h]
  · exact deltaKUOp_genuinely_U_dependent

#print axioms covPlaqInner_curlValueCovariant_eq_covBondInner
#print axioms deltaKUOp_quadForm
#print axioms deltaKUOp_genuinely_U_dependent
#print axioms deltaKU_nonconstant

end AdalyFormal.Balaban.DeltaKU
