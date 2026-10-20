/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RegularUCoercivityFull
import AdalyFormal.Balaban.ThirdLevelSchurGap
import AdalyFormal.Balaban.FourierFaithfulU1
import AdalyFormal.Balaban.RegularUCurvedWitness

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `RegularUGamma0.lean` — `[LEM-COERC-U-GAMMA0]`: the SUMMED upward transfer against the actual
Schur complement, the `ell₀ = 1` closure at EVERY regular `U`, and the reduction of the general case
to exactly TWO named primitives.

`GOAL_LEMMA.md` §7 item 2: `coercive` for regular `U`, uniform in `k`. What is delivered, plainly:

**1. `schur_ge_ell_coarseCurlEnergy_trivialU` (§3) — NEW, unconditional at `U = 1`.**
`ell · ‖∂₁'(Q_ell B)‖²_{L²(coarse plaq)} ≤ ⟨B, Δ_k B⟩` for EVERY `ell > 0`, EVERY aligned torus,
EVERY `levels`, EVERY `B`, no domain restriction. Two things this does that the tree did not:
* it performs IN THE KERNEL the step `FourierFaithfulU1`'s docstring left as prose ("instantiate at
  `A := H_kB` and use `Q_k H_k B = B`"), against the tree's actual Schur object
  `deltaJQuadFormCovFaithful`, via `lineCoarseRestrictCov_hjExtension`;
* it is the FULL-ENERGY form of `ThirdLevelSchurGap.deltaJ_ge_coarse_curl_sq`, which bounds one
  squared coarse-curl component at a time. The duality route cannot be summed (adjacent coarse
  windows OVERLAP, so the Stokes witnesses are not pairwise orthogonal and no Bessel step exists);
  this route needs no dual witness at all. §9 re-proves the tree's banked witness constant
  `(1/64)·bondEnergy B7` through it, by a proof sharing nothing with the duality route.

**2. `gamma0FibreOneUniform_holds` (§6) — the goal-lemma shape, PROVED, at fibre level `ell₀ = 1`,
for every regular `U`, with `γ₀ = 1/25600` and `α₀ = 1/500` as LITERALS quantified outside `L`,
`levels`, `U`, `B`.** Assembled from `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` plus
two `ell = 1` identifications proved here: `Δ_k` reduces to the raw covariant curl form, and `Q_1(U)`
is an ISOMETRY for every `U` (§4, `covCoarseBondInner_one_eq_bondEnergy`). Non-vacuous at a NONZERO
field for every `U` (§8a) and in particular at the genuinely CURVED `RegularUCurvedWitness.curvedU`.
DISCLOSED: `ell₀ = 1` is where `gaugeConstraintSubspaceCovFaithful = ⊥`, so the Schur projection is a
no-op there — Bałaban's `k = 0` end of the tower. The DOMAIN (`axial ∩ ker Q_2(U)`) is not degenerate.

~~**3. `gamma0UniformTarget_of_two_primitives` (§10) — the general case reduced, in Lean, to TWO named
primitives, each strictly smaller than the lemma and each with its constants OUTSIDE the data:**
`[COARSE-CURL-POINCARE]` (`CoarseCurlPoincareUniform`, no `Δ_k`, no `levels`, no minimizer — a
Poincaré between two explicit finite sums; its `(ell₀,m,U) = (1,2,1)` instance is PROVED in §7a) and
`[SUMMED-TRANSFER-U]` (`SummedTransferRegularU`, no domain restriction — §3 is its `U = 1` case).~~

**⚠ SUPERSEDED 2026-07-27 (S75, struck above, retained verbatim). `[COARSE-CURL-POINCARE]` IS
REFUTED.** `CoarseCurlPoincare.not_coarseCurlPoincareUniform : ¬ CoarseCurlPoincareUniform` (in the
module that imports this one, so it cannot be cited in Lean from here) proves `CoarseCurlPoincareUniform`
FALSE: at `ell₀ = 1`, `m = 2p+1` the witness `W1` forces `γc · 2p ≤ 6`, so no `γc > 0` survives every
coarsening factor. `CoarseCurlScaleTwo.not_coarseCurlPoincareScaled r` additionally kills the
`m^{-r}`-DECAYING relaxation at EVERY rate `r`, for `ell₀ ≥ 2`.
Consequences, stated exactly and no more: `gamma0TrivialUTarget_of_coarseCurlPoincare` (§7) and
`gamma0UniformTarget_of_two_primitives` (§10) remain TRUE THEOREMS — they are implications — but their
`CoarseCurlPoincareUniform` antecedent is UNSATISFIABLE, so they deliver the goal lemma for NO scale
and **must not be built through**. What is NOT refuted: `Gamma0UniformTargetAtScale` (its RHS is
`Δ_k(B)`, strictly positive on the refuting field) and `Gamma0FibreOneUniform` (§6, PROVED); the
`(1,2,U=1)` instance in §7a is also still true — it is a single instance, not the universally
quantified Prop. The `[SUMMED-TRANSFER-U]` half is untouched by these refutations.

**4. §11 — the resistance point of the general-`U` transfer, as a THEOREM with a witness.** Every
general-`U` drift bound measures its error against `bondEnergy` of the MINIMIZER, and converting that
into an error against `‖D_U ·‖²` is a reverse Poincaré on the fibre. `no_reverse_poincare_on_kerQ`
proves that inequality FALSE on `ker Q_2(1)` for EVERY constant: `chiField w` is a nonzero, CURL-FREE
element of `ker Q_2(1)`. The same witness proves the goal lemma's AXIAL-GAUGE clause is load-bearing
(`no_coercivity_without_axial`: drop it and the `ell₀ = 1` statement is false for every `γ₀ > 0`).
§11a is the must-not-fire control: the witness has divergence `−2·chi(y)•w ≠ 0`, so it does NOT refute
the div-free form `[KERQ-DIVFREE-POINCARE]` — ~~which is therefore OPEN, not refuted, and is exactly
what `[SUMMED-TRANSFER-U]` still needs.~~
**⚠ SUPERSEDED 2026-07-27 (S75, struck above, retained verbatim): the div-free form is now REFUTED
TOO**, by a DIFFERENT witness — `CoarseCurlPoincare.not_kerQDivFreePoincare : ¬ KerQDivFreePoincare`.
The must-not-fire control below is still CORRECT as a control (this module's `chiField` witness
genuinely does not refute the div-free form, and that remains worth knowing); what is no longer true is
the CONCLUSION drawn from it, that the div-free form is open. ~~Both escape hatches from
`no_reverse_poincare_on_kerQ` are closed by proof, so the reverse-Poincaré route to
`[SUMMED-TRANSFER-U]` is dead in both its ker-`Q` and its div-free form.~~

**⚠⚠ THE STRUCK SENTENCE ABOVE IS ITSELF OVERSTATED — CORRECTED 2026-07-28 (S75 in place, retained
struck). Reported by the `[STOKES-COMM-U]` lane, which could not fix it (LAW-4, outside its write
scope), and verified here against both statements.**

`not_kerQDivFreePoincare` refutes the **LEVEL-UNIFORM** div-free form ONLY. That predicate demands
**one constant `K` valid at EVERY fibre level `ell`** (`CoarseCurlPoincare.lean:17`, its own words:
*"one `K` for every fibre level `ell`"*), and the refutation works by driving the level to infinity —
it picks `p := max 2 n` with `3K < n` and defeats any single `K`. It says nothing whatever about a
FIXED level.

**At fixed level 2 the div-free reverse-Poincaré is a COMPILED THEOREM at general `U`:**
`WeitzenbockCovariant.bondEnergy_le_plaqEnergy_level_two_general_U` — for every extent with
`2 ∣ (L μ + 1)`, every `U` with `frobSupBond U ≤ 1/(4·10⁷)`, every `A` with `lineCoarseRestrictCov U 2 A = 0`
(ker `Q₂`) and `gradCovariantAdjointValue U A = 0` (div-free): `bondEnergy A ≤ 497664 · plaqEnergy (curl_U A)`.
And as of 2026-07-28 the fibre form at `levels = []` is one too
(`StokesCommU.fibreReversePoincare_nil_level_two`, same constant, extended to every
`GaugeRegular (1/(4·10⁷))` background).

The two results are perfectly consistent: **the constant must GROW with the level.** What is dead is a
level-uniform constant, not the reverse-Poincaré route. Writing "dead in both forms" converted a bound
on ONE quantifier structure into a blanket obituary for a route that is alive and proved at fixed
level — cf. [[m2-wall-count-corrected]] (never relay a leaf-count as a wall-count) and
[[wall-is-a-demolition-target]]. Nothing compiled in this module depends on the struck sentence.

The `Mα₀`-analyticity program (GOAL_LEMMA §4 (b1)-(b3), `Balaban/AlphaAnalyticity.lean`) remains a live
route; it is no longer the ONLY one.

**Degeneracy controls, all proved (§8).** `ell₀ = 0` makes the left-hand side identically `0`
(`Q_0 ≡ 0`); a constraint level of `1` collapses the domain to `{0}` at EVERY background
(`kerQ_one_forces_zero`, so `2 ≤ m` is load-bearing); a constraint level EQUAL to the fibre level
makes the left-hand side `0` (so the content lives strictly at `ell₀ < ell₀·m`).

Every declaration below has `#print axioms ⊆ {propext, Classical.choice, Quot.sound}` — no `sorry`.
Lane record: `compute/gamma0_analyticity/PROGRESS.md`.

**LAW-19 disclosures (found by this lane's nested validator, reported not hidden).**
* `rmap_eq_zero_imp` (§8) DUPLICATES `CoercivitySupply.RMap_eq_zero_iff`. Not reused because
  `CoercivitySupply` is not in this module's import chain (it pulls `DeltaKU` + `Coercivity`), and
  the fact is three lines from `CovariantHjMinimizer.RMap_apply_inv_cancel`, which is.
* `chi`/`chiField` (§11) generalize `BackgroundAveraging.checkerConfigSuTwo` (the same alternating
  sign, fixed to one witness lattice and one `suTwoWitness`) and re-prove its shift-cancellation at
  general `L`/`w`; that module is likewise outside this import chain. The generality is used: §11
  needs the witness at an ARBITRARY compatible torus with an arbitrary `w ≠ 0`.
* `covPlaqInner_self_eq_plaqEnergy` (§1) is the third proof of an identity already appearing as an
  unnamed `have` in `ThirdLevelSchurGap` and `RegularUPerturbation`; naming it here consolidates it.
* **ISLAND**: no module imports `RegularUGamma0`; it is not in `Spine.lean`'s cone. Wiring is the
  glue lane's scope, not claimed here.

**Why the coarse-curl route is the only one that reaches `ell₀ > 1` right now (navigational, and it
is why the flat-vs-covariant question above matters).** There is a second, DENOTATION-CLEAN route to
the same target that never mentions a coarse curl: bound `Δ_k(B) = ‖D_U(H_j B)‖²` below by
`γ''·bondEnergy(H_j B)` with the general-`U` Lemma 2.4, then use the `Q`-contraction
`‖Q_ell(U)A‖² ≤ ell⁻³·bondEnergy A` (Cauchy–Schwarz over the `ell⁴` line-integral terms plus
`FourierFaithfulU1.sum_coarse_blocks`; every operator in it is covariant, so no flat/covariant
ambiguity arises). Its residual is that the minimizer `H_j B` must itself stay in
`axial ∩ ker Q_{ell₀·m}(U)`. That route was NOT built here, and the reason is measured, not
aesthetic: the tree's general-`U` Lemma 2.4 (`RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU`)
exists ONLY at level `2`, so the route needs `ell₀ · m = 2`, i.e. `ell₀ ∈ {1, 2}` — and `ell₀ = 2`
makes fibre = constraint, which §8 PROVES content-free, while `ell₀ = 1` is exactly what §5 already
delivers. So the second route has NO reachable new instance until a general-`U` Lemma 2.4 exists at
some level `> 2`, and building its `Q`-contraction now would add an island with no consumer (LAW-19).
-/

namespace AdalyFormal.Balaban.RegularUGamma0

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU deltaKernelImageCovH)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoGeomU1
open AdalyFormal.Balaban.CovU1Reduction
open AdalyFormal.Balaban.LatticeOperators (CoarseBond curlValue)
open AdalyFormal.Balaban.LineIntegralAveraging (lineCoarseRestrict)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette coarseCurlValue)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)
open AdalyFormal.Balaban.FourierFaithfulU1 (faithful_U1_coercivity_lower)
open AdalyFormal.Balaban.BlockPoincareLemma24 (totalCurlEnergy)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the coarse-curl `L²` energy on the su(2) carrier, and its coordinate decomposition -/

/-- **The coarse-curl `L²` energy of a coarse su(2) bond field**
`= Σ_{P'} ‖(∂₁'B)(P')‖²`, written through `hsInner` exactly as `covPlaqInner`/`covCoarseBondInner`
are (LAW-19: same normalization, no new inner product). -/
noncomputable def coarseCurlEnergySuTwo {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) : ℝ :=
  ∑ p : CoarsePlaquette L ell, hsInner (coarseCurlSuTwo hdvd B p) (coarseCurlSuTwo hdvd B p)

theorem coarseCurlEnergySuTwo_nonneg {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) : 0 ≤ coarseCurlEnergySuTwo hdvd B :=
  Finset.sum_nonneg fun _ _ => hsInner_self_nonneg _

/-- `covPlaqInner X X = plaqEnergy X` — the plaquette-side bridge between the `hsInner` form and the
plain real energy sum (mirrors `RegularUCoercivityFull.covCoarseBondInner_self_eq_sum`). -/
theorem covPlaqInner_self_eq_plaqEnergy (X : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner X X = plaqEnergy X := by
  unfold covPlaqInner plaqEnergy
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← inner_eq_hsInner, real_inner_self_eq_norm_sq]

/-- The su(2) coarse curl is the scalar coarse curl in each Pauli coordinate — the two definitions
are the SAME signed four-term combination (`ThirdLevelStokes.coarseCurlSuTwo` vs
`CoarseCurl.coarseCurlValue`), so the linear coordinate functional passes straight through. -/
theorem suCoordLM_coarseCurlSuTwo {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (i : Fin 3)
    (B : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) :
    suCoordLM i (coarseCurlSuTwo hdvd B p)
      = coarseCurlValue hdvd (fun c => suCoordLM i (B c)) p := by
  show suCoordLM i (coarseCurlSuTwo hdvd B p) = _
  unfold coarseCurlSuTwo coarseCurlValue
  simp only [map_add, map_sub]

/-- **The su(2) coarse-curl energy is the sum of the three scalar coarse-curl energies** — the exact
analogue of `SuTwoGeomU1.covPlaqInner_flatCurl_eq_sum` at the coarse level. -/
theorem coarseCurlEnergySuTwo_eq_sum_coord {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) :
    coarseCurlEnergySuTwo hdvd B
      = ∑ i : Fin 3, ∑ p : CoarsePlaquette L ell,
          (coarseCurlValue hdvd (fun c => suCoordLM i (B c)) p) ^ 2 := by
  unfold coarseCurlEnergySuTwo
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hsInner_eq_sum_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [suCoordLM_coarseCurlSuTwo, sq]

/-- At `U = 1` the `i`-th coordinate of the FAITHFUL covariant average is the scalar faithful
average of the `i`-th component field. -/
theorem coord_lineCoarseRestrictCov_trivialU (i : Fin 3) (ell : ℕ) (A : Bond L → SuTwo)
    (c : CoarseBond L ell) :
    suCoordLM i (lineCoarseRestrictCovLM (trivialU L) ell A c)
      = lineCoarseRestrict ell (suComp i A) c := by
  rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_trivialU,
    suCoordLM_lineCoarseRestrictSuTwo]

/-- At `U = 1` the plaquette energy of the covariant curl is the sum of the three scalar total curl
energies. -/
theorem plaqEnergy_curl_trivialU_eq_sum (A : Bond L → SuTwo) :
    plaqEnergy (curlCovariantLM (trivialU L) A) = ∑ i : Fin 3, totalCurlEnergy (suComp i A) := by
  rw [← covPlaqInner_self_eq_plaqEnergy]
  have hcurl : curlCovariantLM (trivialU L) A = flatCurlValue A := by
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  rw [hcurl]
  exact covPlaqInner_flatCurl_eq_sum A

#print axioms coarseCurlEnergySuTwo_nonneg
#print axioms covPlaqInner_self_eq_plaqEnergy
#print axioms suCoordLM_coarseCurlSuTwo
#print axioms coarseCurlEnergySuTwo_eq_sum_coord
#print axioms coord_lineCoarseRestrictCov_trivialU
#print axioms plaqEnergy_curl_trivialU_eq_sum

/-! ## §2 — the SUMMED upward transfer at `U = 1`, on the su(2) carrier -/

/-- **`ell · ‖∂₁'(Q_ell A)‖² ≤ ‖∂A‖²` on the su(2) carrier, every `ell > 0`, every aligned torus,
every `A`.** The su(2) lift of `FourierFaithfulU1.faithful_U1_coercivity_lower` (the scalar brick,
sharp: an EQUALITY at `ell = 1`), obtained coordinate-wise through the Pauli decomposition exactly
as `SuTwoGeomU1` lifts (2.128). The constant is the literal `ell` — no `k`, no lattice volume, no
existential. -/
theorem ell_coarseCurlEnergy_le_plaqEnergy_trivialU {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    (ell : ℝ) * coarseCurlEnergySuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A)
      ≤ plaqEnergy (curlCovariantLM (trivialU L) A) := by
  rw [coarseCurlEnergySuTwo_eq_sum_coord, plaqEnergy_curl_trivialU_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hco : (fun c => suCoordLM i (lineCoarseRestrictCovLM (trivialU L) ell A c))
      = lineCoarseRestrict ell (suComp i A) :=
    funext fun c => coord_lineCoarseRestrictCov_trivialU i ell A c
  rw [hco]
  exact faithful_U1_coercivity_lower hell hdvd (suComp i A)

#print axioms ell_coarseCurlEnergy_le_plaqEnergy_trivialU

/-! ## §3 — THE SCHUR LOWER BOUND: `Δ_k(B) ≥ ell · ‖∂₁'(Q_ell B)‖²` (`U = 1`, every `ell`, every
`levels`, every `B`, NO domain restriction) -/

/-- **`Q_ell` is blind to the `H_j` correction** — `Q_ell(H_j B) = Q_ell B` unconditionally, because
the correction lies in `gaugeConstraintSubspaceCovFaithful`, whose first clause is `Q_ell(·) = 0`.
This is the kernel form of CMP95 p.29's `Q_k H_k B = B`. -/
theorem lineCoarseRestrictCov_hjExtension {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    lineCoarseRestrictCovLM U ell (hjExtensionCovFaithful ell levels U B)
      = lineCoarseRestrictCovLM U ell B := by
  unfold hjExtensionCovFaithful
  rw [map_add,
    (mem_gaugeConstraintSubspaceCovFaithful.mp (hjCorrectionCovFaithful_mem ell levels U B)).1,
    add_zero]

/-- **The Schur complement IS the plaquette energy of the corrected curl.** -/
theorem deltaJ_eq_plaqEnergy {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    deltaJQuadFormCovFaithful ell levels U B
      = plaqEnergy (curlCovariantLM U (hjExtensionCovFaithful ell levels U B)) := by
  unfold deltaJQuadFormCovFaithful
  exact covPlaqInner_self_eq_plaqEnergy _

/-- **THE SUMMED UPWARD TRANSFER AGAINST THE ACTUAL SCHUR COMPLEMENT (`U = 1`).**
For EVERY `ell > 0`, EVERY aligned torus, EVERY `levels`, EVERY `B`:

  `ell · ‖∂₁'(Q_ell B)‖²_{L²(coarse plaquettes)} ≤ ⟨B, Δ_k B⟩`.

This replaces, IN THE KERNEL, the prose step that `FourierFaithfulU1`'s docstring left open
("instantiate at `A := H_kB` and use `Q_k H_k B = B`"): the instantiation is performed here at the
tree's actual Schur object `deltaJQuadFormCovFaithful`, using
`lineCoarseRestrictCov_hjExtension` for `Q_k H_k B = B`.

It is also the FULL-ENERGY strengthening of `ThirdLevelSchurGap.deltaJ_ge_coarse_curl_sq`, which
bounds ONE squared coarse-curl component (one coarse plaquette, one su(2) direction) at a time; the
duality/Stokes-witness route it uses cannot be summed over coarse plaquettes, because the windows of
adjacent coarse blocks OVERLAP and the witnesses are therefore not pairwise orthogonal (no Bessel
inequality is available). The route here needs no dual witness, no orthogonality and no Bessel step:
the minimizer's own interpolation property carries the whole argument. Both constants agree — at the
split `(2,4)` on `B7` this theorem reproduces `third_level_energy_bound` exactly (see §5). -/
theorem schur_ge_ell_coarseCurlEnergy_trivialU {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels (trivialU L)).HasOrthogonalProjection]
    (B : Bond L → SuTwo) :
    (ell : ℝ) * coarseCurlEnergySuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell B)
      ≤ deltaJQuadFormCovFaithful ell levels (trivialU L) B := by
  rw [deltaJ_eq_plaqEnergy,
    ← lineCoarseRestrictCov_hjExtension (ell := ell) levels (trivialU L) B]
  exact ell_coarseCurlEnergy_le_plaqEnergy_trivialU hell hdvd _

#print axioms lineCoarseRestrictCov_hjExtension
#print axioms deltaJ_eq_plaqEnergy
#print axioms schur_ge_ell_coarseCurlEnergy_trivialU

/-! ## §4 — the `ell = 1` identifications: `Q_1(U)` is an isometry, for EVERY background -/

/-- **`Q_1(U)` is the pointwise adjoint transport of a length-`0` path.** At `ell = 1` the block is a
singleton (`blockOf_one`) and the line integral has one term (`pathSite_zero`), so the faithful
covariant average is `R(hol)` applied to the single bond value. Every `U`. -/
theorem lineCoarseRestrictCov_one_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (c : CoarseBond L 1) :
    lineCoarseRestrictCov U 1 A c
      = RMap (periodicPathHolonomy U c.1.1
          (Q1Real.transportPath c.1.1 c.1.1 c.2 0)) (A (c.1.1, c.2)) := by
  simp only [lineCoarseRestrictCov, Q1Real.rZeroA]
  rw [FourierFaithfulU1.blockOf_one, Finset.sum_singleton, Finset.sum_range_one,
    QOne.pathSite_zero]
  norm_num

/-- **`Q_1(U)` is the IDENTITY, for EVERY background.** The `ell = 1` transport path is
`transportPath y y μ 0 = Γ_{y,y} ++ straightSegment y y μ = []` (`Q1Real.GammaPath_self`,
`Q1Real.straightSegment_self`), so its holonomy is `1` and `RMap 1 = id` — the `U`-dependence of the
faithful covariant average is entirely gone at `ell = 1`. Recorded because it has a CONSEQUENCE that
constrains what the general-`U` primitives of §10 can mean: see the disclosure on
`SummedTransferRegularU`. -/
theorem lineCoarseRestrictCov_one_eq_self
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (c : CoarseBond L 1) :
    lineCoarseRestrictCov U 1 A c = A (c.1.1, c.2) := by
  rw [lineCoarseRestrictCov_one_apply]
  have hpath : Q1Real.transportPath c.1.1 c.1.1 c.2 0 = [] := by
    unfold Q1Real.transportPath
    rw [Q1Real.GammaPath_self, QOne.pathSite_zero, Q1Real.straightSegment_self, List.nil_append]
  rw [hpath]
  show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) (A (c.1.1, c.2)) = _
  rw [RMap_one, LinearMap.id_apply]

#print axioms lineCoarseRestrictCov_one_eq_self

/-- The `ell = 1` coarse-bond type IS the fine-bond type: `c ↦ (c.1.1, c.2)` is a bijection
(`CoarseLattice L 1 = univ`). -/
theorem coarseBond_one_bijective :
    Function.Bijective (fun c : CoarseBond L 1 => ((c.1.1, c.2) : Bond L)) := by
  constructor
  · intro c c' h
    have h' : ((c.1.1, c.2) : Bond L) = ((c'.1.1, c'.2) : Bond L) := h
    rw [Prod.mk.injEq] at h'
    rw [Prod.ext_iff]
    exact ⟨Subtype.ext h'.1, h'.2⟩
  · intro b
    exact ⟨(⟨b.1, FourierFaithfulU1.mem_coarseLattice_one b.1⟩, b.2), rfl⟩

/-- **`‖Q_1(U)A‖²_{L²(coarse)} = ‖A‖²_{L²(bonds)}` for EVERY background `U`.** `Q_1(U)` is a
pointwise `Ad`-transport (§4 above) and `Ad` is an `hsInner` isometry
(`SuTwoInner.hsInner_RMap`), so the coarse `L²` energy at `ell = 1` is exactly `bondEnergy`. This is
what makes the `ell₀ = 1` fibre's coercivity statement carry the FINE bond norm on its right-hand
side — no normalization slack, no `ell`-power. -/
theorem covCoarseBondInner_one_eq_bondEnergy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    covCoarseBondInner (lineCoarseRestrictCovLM U 1 A) (lineCoarseRestrictCovLM U 1 A)
      = bondEnergy A := by
  unfold covCoarseBondInner bondEnergy
  have hterm : ∀ c : CoarseBond L 1,
      hsInner (lineCoarseRestrictCovLM U 1 A c) (lineCoarseRestrictCovLM U 1 A c)
        = ‖A (c.1.1, c.2)‖ ^ 2 := by
    intro c
    rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_one_apply, hsInner_RMap,
      ← inner_eq_hsInner, real_inner_self_eq_norm_sq]
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  exact Fintype.sum_bijective _ coarseBond_one_bijective _ _ (fun _ => rfl)

#print axioms lineCoarseRestrictCov_one_apply
#print axioms coarseBond_one_bijective
#print axioms covCoarseBondInner_one_eq_bondEnergy

/-! ## §5 — `Δ_k ≥ γ'' · ‖Q_{ell₀}B‖²` AT THE FIBRE LEVEL `ell₀ = 1`, FOR EVERY REGULAR `U`

The composition: the `ell = 1` reduction of the Schur complement
(`CovariantHjFaithful.deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm`) plus the `ell = 1`
isometry of `Q_1(U)` (§4) turn `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` — the
general-`U`, `k`-free Lemma-2.4-shaped bound on the axial-gauge intersection `ker Q_2(U)` — into a
statement of exactly the `Δ_k ≥ γ₀·‖Q_{ell₀}B‖²` shape the goal lemma asks for.

**Disclosed scope, plainly.** `ell₀ = 1` is the fibre level at which
`gaugeConstraintSubspaceCovFaithful 1 levels U = ⊥`
(`CovariantHjFaithful.gaugeConstraintSubspaceCovFaithful_ell1_eq_bot`), so the Schur projection is a
no-op and `Δ_k` coincides with the raw covariant curl form. That is Bałaban's `k = 0` end of the
tower — the base case, not the recursion step. What is NOT degenerate here: the DOMAIN is the
`ell₁ = 2` constraint kernel `axial ∩ ker Q_2(U)`, which contains nonzero fields at genuinely curved
backgrounds (§7), and the constant is `k`-free and `U`-uniform over the regular class. -/

/-- **THE `ell₀ = 1` COERCIVITY, EVERY BACKGROUND `U`, `k`-FREE CONSTANT.** For every torus with
`4 ≤ L μ`, `2 ∣ L μ + 1`, every `U`, every `levels`, and every `B` in the axial gauge at level `2`
and in `ker Q_2(U)`, under the two stated `α₁`-smallness hypotheses,

  `(√(γ₀' − 64α₁²) − 4√2·α₁)² · ‖Q_1(U)B‖²_{L²(coarse)} ≤ ⟨B, Δ_k B⟩`,
  `γ₀' = (1/108)(1/2⁴)`, `α₁ = frobSupBond U`,

with `Δ_k = deltaJQuadFormCovFaithful 1 levels U`. Nothing in the constant depends on the RG step,
the lattice size, or the level list. -/
theorem gamma0_coercivity_fibre_one
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels U).HasOrthogonalProjection]
    (B : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, B b = 0)
    (hkerU : ∀ c : CoarseBond L 2, lineCoarseRestrictCov U 2 B c = 0)
    (hthr : 64 * frobSupBond U ^ 2 ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4))
    (hsmall : 0 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond U) :
    (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond U) ^ 2
        * covCoarseBondInner (lineCoarseRestrictCovLM U 1 B) (lineCoarseRestrictCovLM U 1 B)
      ≤ deltaJQuadFormCovFaithful 1 levels U B := by
  rw [covCoarseBondInner_one_eq_bondEnergy, deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm]
  exact AdalyFormal.Balaban.RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU
    hL hdvd U B hadm hkerU hthr hsmall

#print axioms gamma0_coercivity_fibre_one

/-! ## §6 — the NUMERIC uniform slice: one `(γ₀, α₀)` pair for every torus, background and field -/

/-- **The `ell₀ = 1` / `ell₁ = 2` slice of the goal lemma, with BOTH constants quantified OUTSIDE
everything** (`γ₀` and the regularity threshold `α₀` come first, before `L`, `levels`, `U`, `B`).
This is the S91-clean shape: no existential over any data the prover could choose. -/
def Gamma0FibreOneUniform : Prop :=
  ∃ γ₀ α₀ : ℝ, 0 < γ₀ ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent), (∀ μ : Fin 3, 4 ≤ L μ) → (∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) →
      ∀ (levels : List (KernelSubspace.Level L))
        (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
          [(curlImageCovHFaithful 1 levels U).HasOrthogonalProjection]
          (B : Bond L → SuTwo),
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, B b = 0) →
          (∀ c : CoarseBond L 2, lineCoarseRestrictCov U 2 B c = 0) →
          γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U 1 B) (lineCoarseRestrictCovLM U 1 B)
            ≤ deltaJQuadFormCovFaithful 1 levels U B

/-- `√2 ≤ 1.4143`. -/
theorem sqrt_two_le : Real.sqrt 2 ≤ 1.4143 := by
  rw [show (1.4143 : ℝ) = Real.sqrt ((1.4143 : ℝ) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- **The `α₀`-uniform lower bound on the regular-`U` constant.** For `α₁ ≤ 1/500`,
`1/160 ≤ √(γ₀' − 64α₁²) − 4√2·α₁`, hence `1/25600 ≤ (…)²`. Exact rational arithmetic: the
threshold `√(3227/10⁷) ≥ 1757/10⁵` is checked by squaring (`(1757/10⁵)² = 3.0848…e−4 ≤
3.227…e−4`), and `1/160 + 4·1.4143/500 ≤ 1757/10⁵`. -/
theorem regularU_constant_lower {a : ℝ} (ha : 0 ≤ a) (hle : a ≤ 1 / 500) :
    (1 : ℝ) / 160 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * a ^ 2)
      - 4 * Real.sqrt 2 * a := by
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hcast]
  have hgam : (3227 : ℝ) / 10000000 ≤ (1 / 108) * (1 / (2 : ℝ) ^ 4) - 64 * a ^ 2 := by
    nlinarith [ha, hle, sq_nonneg a]
  have hsqrt : (1757 : ℝ) / 100000
      ≤ Real.sqrt ((1 / 108) * (1 / (2 : ℝ) ^ 4) - 64 * a ^ 2) := by
    have h1 := Real.sqrt_le_sqrt
      (le_trans (show ((1757 : ℝ) / 100000) ^ 2 ≤ (3227 : ℝ) / 10000000 by norm_num) hgam)
    rwa [Real.sqrt_sq (by norm_num)] at h1
  have hs2 := sqrt_two_le
  nlinarith [hsqrt, hs2, ha, hle, Real.sqrt_nonneg 2]

/-- **`Gamma0FibreOneUniform` HOLDS, with `γ₀ = 1/25600` and `α₀ = 1/500`.** Both literals; the
witness constants are numerals, not existentials over data. -/
theorem gamma0FibreOneUniform_holds : Gamma0FibreOneUniform := by
  refine ⟨1 / 25600, 1 / 500, by norm_num, by norm_num, ?_⟩
  intro L hL hdvd levels U hreg _ _ B hadm hkerU
  have ha : 0 ≤ frobSupBond U :=
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U
  have hlow := regularU_constant_lower ha hreg
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  -- the two smallness hypotheses, from the numeric threshold
  have hthr : 64 * frobSupBond U ^ 2 ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by
    rw [hcast]; nlinarith [ha, hreg]
  have hsmall : 0 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
      - 4 * Real.sqrt 2 * frobSupBond U := by linarith [hlow]
  have key := gamma0_coercivity_fibre_one hL hdvd U levels B hadm hkerU hthr hsmall
  have hgam : (1 : ℝ) / 25600
      ≤ (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
          - 4 * Real.sqrt 2 * frobSupBond U) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 160) hlow 2
    calc (1 : ℝ) / 25600 = ((1 : ℝ) / 160) ^ 2 := by norm_num
      _ ≤ _ := h
  have hE : 0 ≤ covCoarseBondInner (lineCoarseRestrictCovLM U 1 B)
      (lineCoarseRestrictCovLM U 1 B) := covCoarseBondInner_self_nonneg _
  nlinarith [key, hgam, hE]

#print axioms sqrt_two_le
#print axioms regularU_constant_lower
#print axioms gamma0FibreOneUniform_holds

/-! ## §7 — THE REDUCTION: the general-`ell₀` coercivity at `U = 1` rests on ONE named primitive,
strictly smaller than the lemma

`schur_ge_ell_coarseCurlEnergy_trivialU` (§3) discharges the entire OPERATOR half of the goal lemma
— the Schur complement, the `H_j` minimizer, the level list, the orthogonal projection all disappear.
What remains is a statement with **no `Δ_k` in it at all**: a Poincaré inequality between two
explicit finite sums on the coarse carrier. That is the primitive below.

It is Bałaban's Lemma 2.4 / CMP96 (2.128) READ AT THE COARSE SCALE `ell₀` — exactly the object the
recursion consumes at the next level (`ThirdLevelSchurGap`'s "the coarse curl at level `ℓ` is the
input of the NEXT level's Lemma 2.4"). Its hypotheses are written in the SAME fine-level vocabulary
the goal lemma itself uses (axial gauge and `ker Q` at the constraint level `ell₀·m`), so no new
coarse-lattice notion is introduced and no definition is free to be rigged. -/

/-- **THE NAMED PRIMITIVE `[COARSE-CURL-POINCARE]`.** One constant `γc > 0` for every torus, every
fibre level `ell₀ > 0`, every coarsening factor `m ≥ 2`, every background `U`, every field `B` in
the axial gauge and in `ker Q_{ell₀·m}(U)`:

  `γc · ‖Q_{ell₀}(U)B‖²_{L²(coarse bonds)} ≤ ‖∂₁'(Q_{ell₀}(U)B)‖²_{L²(coarse plaquettes)}`.

`γc` is quantified OUTSIDE `L`, `ell₀`, `m`, `U`, `B` (S91). `def : Prop` — OPEN in general; the
`ell₀ = 1`, `m = 2`, `U = 1` instance is PROVED below
(`coarseCurlPoincare_fibre_one_trivialU`, and `coarseCurlPoincare_body_at_one_two` checks the
specialization in the elaborator), so the primitive is not vacuous and not unreachable.

**⚠ DENOTATION DISCLOSURE, `U ≠ 1` — read before using this at a curved background.**
`coarseCurlSuTwo` is the FLAT four-term coarse curl; nothing transports it. At `U = 1` (where the
proved instance and §3 both live) that is the right object. At `U ≠ 1` this `def` therefore compares
a FLAT coarse curl of a COVARIANT average, and the tree has no covariant coarse curl to compare it
with (grep: no `coarseCurlCovariant` exists). The sharpest consequence, measured not guessed:
`lineCoarseRestrictCov_one_eq_self` proves `Q_1(U) = id` for EVERY `U`, so at `ell₀ = 1` the
left-hand side here is `U`-INDEPENDENT while the goal lemma's right-hand side is not. Nothing in this
module asserts the `U ≠ 1` case of this `def`; its truth there is UNTESTED and its denotation is NOT
source-adjudicated.

**Why this is strictly smaller than the goal lemma.** It mentions neither `Δ_k`
(`deltaJQuadFormCovFaithful`), nor `levels`, nor `hjExtensionCovFaithful`, nor any orthogonal
projection: both sides are explicit finite sums over the coarse bond/plaquette sets. The reduction
`gamma0TrivialUTarget_of_coarseCurlPoincare` proves it suffices at `U = 1`. -/
def CoarseCurlPoincareUniform : Prop :=
  ∃ γc : ℝ, 0 < γc ∧
    ∀ (L : PeriodicLatticeExtent) (ell₀ m : ℕ), 0 < ell₀ → 2 ≤ m →
      (∀ μ : Fin 3, 4 ≤ L μ) →
      ∀ (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1)),
        (∀ μ : Fin 3, (ell₀ * m) ∣ (L μ + 1)) →
        ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
          (B : Bond L → SuTwo),
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (ell₀ * m) →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y (ell₀ * m) →
            ∀ b ∈ staircasePath y x, B b = 0) →
          (∀ c : CoarseBond L (ell₀ * m), lineCoarseRestrictCov U (ell₀ * m) B c = 0) →
          γc * covCoarseBondInner (lineCoarseRestrictCovLM U ell₀ B)
              (lineCoarseRestrictCovLM U ell₀ B)
            ≤ coarseCurlEnergySuTwo hdvd₀ (lineCoarseRestrictCovLM U ell₀ B)

/-- **THE GOAL LEMMA AT `U = 1`, EVERY FIBRE LEVEL** — `γ₀` quantified OUTSIDE `L`, `ell₀`, `m`,
`levels`, `B`. The `U`-dependence is the separate frontier (§5/§6 close `ell₀ = 1` for every
regular `U`); this statement isolates the `ell₀`-generality. -/
def Gamma0TrivialUTarget : Prop :=
  ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (L : PeriodicLatticeExtent) (ell₀ m : ℕ), 0 < ell₀ → 2 ≤ m →
      (∀ μ : Fin 3, 4 ≤ L μ) →
      (∀ μ : Fin 3, ell₀ ∣ (L μ + 1)) →
        (∀ μ : Fin 3, (ell₀ * m) ∣ (L μ + 1)) →
        ∀ (levels : List (KernelSubspace.Level L)),
          ∀ [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
            [(curlImageCovHFaithful ell₀ levels (trivialU L)).HasOrthogonalProjection]
            (B : Bond L → SuTwo),
            (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (ell₀ * m) →
              ∀ x : PeriodicLatticeSite L, x ∈ blockOf y (ell₀ * m) →
              ∀ b ∈ staircasePath y x, B b = 0) →
            (∀ c : CoarseBond L (ell₀ * m),
              lineCoarseRestrictCov (trivialU L) (ell₀ * m) B c = 0) →
            γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) ell₀ B)
                (lineCoarseRestrictCovLM (trivialU L) ell₀ B)
              ≤ deltaJQuadFormCovFaithful ell₀ levels (trivialU L) B

/-- **THE REDUCTION, PROVED.** `[COARSE-CURL-POINCARE]` ⟹ the `U = 1` goal lemma at EVERY fibre
level, with the SAME constant (`ell₀ ≥ 1` only helps). The entire operator-theoretic half — Schur
complement, `H_j` minimizer, gauge-constraint subspace, orthogonal projection — is discharged by §3
and appears nowhere in the primitive.

**⚠ ANTECEDENT UNSATISFIABLE, 2026-07-27 (S75).** The implication below is still a true theorem, but
`CoarseCurlPoincare.not_coarseCurlPoincareUniform` proves its hypothesis FALSE, so it delivers
`Gamma0TrivialUTarget` for no scale. Do not build through it. -/
theorem gamma0TrivialUTarget_of_coarseCurlPoincare :
    CoarseCurlPoincareUniform → Gamma0TrivialUTarget := by
  rintro ⟨γc, hγc, h⟩
  refine ⟨γc, hγc, ?_⟩
  intro L ell₀ m hell₀ hm hL hdvd₀ hdvdm levels _ _ B hadm hker
  have hprim := h L ell₀ m hell₀ hm hL hdvd₀ hdvdm (trivialU L) B hadm hker
  have htransfer := schur_ge_ell_coarseCurlEnergy_trivialU hell₀ hdvd₀ levels B
  have hell₀R : (1 : ℝ) ≤ (ell₀ : ℝ) := by exact_mod_cast hell₀
  have hnn := coarseCurlEnergySuTwo_nonneg hdvd₀ (lineCoarseRestrictCovLM (trivialU L) ell₀ B)
  nlinarith [hprim, htransfer, hnn, hell₀R]

#print axioms gamma0TrivialUTarget_of_coarseCurlPoincare

/-! ### §7a — the primitive is REACHABLE: its `ell₀ = 1`, `m = 2`, `U = 1` instance, PROVED -/

/-- At `ell = 1` and `U = 1` the su(2) coarse-curl energy IS the fine plaquette energy — the su(2)
lift of `FourierFaithfulU1.calibration_ell_one` (an EQUALITY, the sharpness calibration of §2's
constant). -/
theorem coarseCurlEnergySuTwo_one_eq_plaqEnergy (hdvd1 : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1))
    (A : Bond L → SuTwo) :
    coarseCurlEnergySuTwo hdvd1 (lineCoarseRestrictCovLM (trivialU L) 1 A)
      = plaqEnergy (curlCovariantLM (trivialU L) A) := by
  rw [coarseCurlEnergySuTwo_eq_sum_coord, plaqEnergy_curl_trivialU_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hco : (fun c => suCoordLM i (lineCoarseRestrictCovLM (trivialU L) 1 A c))
      = lineCoarseRestrict 1 (suComp i A) :=
    funext fun c => coord_lineCoarseRestrictCov_trivialU i 1 A c
  rw [hco]
  have hcal := FourierFaithfulU1.calibration_ell_one hdvd1 (suComp i A)
  rw [one_mul] at hcal
  rw [hcal]
  rfl

/-- **`[COARSE-CURL-POINCARE]` AT `(ell₀, m) = (1, 2)`, `U = 1`, with `γc = (1/108)(1/2⁴)`.**
The instance is the su(2) `U = 1` additive Lemma 2.4 (`SuTwoGeomU1`) read through the two `ell = 1`
identifications: `‖Q_1(1)B‖² = bondEnergy B` (§4) and `‖∂₁'(Q_1(1)B)‖² = plaqEnergy(∂B)` (§7a).
So the named primitive is INHABITED at a non-degenerate point — the domain
`axial ∩ ker Q_2` contains nonzero fields (§8). -/
theorem coarseCurlPoincare_fibre_one_trivialU
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (hdvd1 : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1)) (B : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, B b = 0)
    (hker : ∀ c : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 B c = 0) :
    ((1 : ℝ) / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4)
        * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) 1 B)
          (lineCoarseRestrictCovLM (trivialU L) 1 B)
      ≤ coarseCurlEnergySuTwo hdvd1 (lineCoarseRestrictCovLM (trivialU L) 1 B) := by
  rw [covCoarseBondInner_one_eq_bondEnergy, coarseCurlEnergySuTwo_one_eq_plaqEnergy]
  -- the U=1 additive base at level 2
  have hbase := suTwoGeomAdditive_trivialU_of_admissible hL hdvd2 B hadm
  rw [CoercivityTargetsCorrected.SuTwoGeomAdditiveInequality] at hbase
  -- the coarse term vanishes: B ∈ ker Q_2(1)
  have hz : lineCoarseRestrictCovLM (trivialU L) 2 B = 0 := by
    funext c
    rw [lineCoarseRestrictCovLM_apply]
    exact hker c
  rw [hz] at hbase
  have hzero : covCoarseBondInner (0 : CoarseBond L 2 → SuTwo) 0 = 0 := by
    unfold covCoarseBondInner
    simp only [Pi.zero_apply, CovariantHj.hsInner_zero_zero, Finset.sum_const_zero]
  rw [hzero,
    AdalyFormal.Balaban.RegularUDirectCoercivity.covPlaqInner_curl1_eq_deltaJ1,
    AdalyFormal.Balaban.RegularUDirectCoercivity.covBondInner_eq_bondEnergy] at hbase
  rw [← covPlaqInner_self_eq_plaqEnergy]
  have hdd : covPlaqInner (curlCovariantLM (trivialU L) B) (curlCovariantLM (trivialU L) B)
      = dstarDQuadForm (trivialU L) B := rfl
  rw [hdd]
  nlinarith [hbase]

/-- **The instance relation, MACHINE-CHECKED rather than eyeballed.** This is literally the body of
`CoarseCurlPoincareUniform` at `ell₀ = 1`, `m = 2`, `U = trivialU`, `γc = 1/1728` — every binder
written with `1 * 2` exactly as the `def` produces it, so the specialization is checked by the
elaborator and not by reading. It is discharged by `coarseCurlPoincare_fibre_one_trivialU`
(`(1/108)·(1/2⁴) = 1/1728`). What it does NOT establish: `CoarseCurlPoincareUniform` itself, which
demands ONE `γc` for every `L`, `ell₀`, `m`, `U`. -/
theorem coarseCurlPoincare_body_at_one_two
    (L : PeriodicLatticeExtent) (hL : ∀ μ : Fin 3, 4 ≤ L μ)
    (hdvd₀ : ∀ μ : Fin 3, (1 : ℕ) ∣ (L μ + 1))
    (hdvdm : ∀ μ : Fin 3, ((1 * 2 : ℕ)) ∣ (L μ + 1))
    (B : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (1 * 2) →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y (1 * 2) →
      ∀ b ∈ staircasePath y x, B b = 0)
    (hker : ∀ c : CoarseBond L (1 * 2), lineCoarseRestrictCov (trivialU L) (1 * 2) B c = 0) :
    (1 / 1728 : ℝ) * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) 1 B)
        (lineCoarseRestrictCovLM (trivialU L) 1 B)
      ≤ coarseCurlEnergySuTwo hdvd₀ (lineCoarseRestrictCovLM (trivialU L) 1 B) := by
  have h := coarseCurlPoincare_fibre_one_trivialU hL hdvdm hdvd₀ B hadm hker
  have hnum : ((1 : ℝ) / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) = 1 / 1728 := by norm_num
  rwa [hnum] at h

#print axioms coarseCurlEnergySuTwo_one_eq_plaqEnergy
#print axioms coarseCurlPoincare_fibre_one_trivialU
#print axioms coarseCurlPoincare_body_at_one_two

/-! ## §8 — ATTACKING THE STATEMENTS: every binder that could evaporate the content, PROVED to

Each item below is a MADE-IT-FAIL control, not an argument that it would fail. -/

/-- **`ell₀ = 0` KILLS the left-hand side**: `Q_0(U) ≡ 0` for every `U` and every field (the `1/ell⁴`
normalization is `1/0 = 0` in Lean, and `blockOf y 0 = ∅`), so at `ell₀ = 0` the coercivity reads
`γ₀·0 ≤ Δ_k` — content-free. This is why `0 < ell₀` is a load-bearing hypothesis in
`CoarseCurlPoincareUniform`/`Gamma0TrivialUTarget`, not a convenience. -/
theorem lineCoarseRestrictCov_zero_level
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (c : CoarseBond L 0) : lineCoarseRestrictCov U 0 A c = 0 := by
  simp only [lineCoarseRestrictCov, Nat.cast_zero]
  norm_num

/-- …hence the whole left-hand side vanishes at `ell₀ = 0`. -/
theorem lhs_vanishes_at_level_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    covCoarseBondInner (lineCoarseRestrictCovLM U 0 A) (lineCoarseRestrictCovLM U 0 A) = 0 := by
  unfold covCoarseBondInner
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_zero_level,
    CovariantHj.hsInner_zero_zero]

/-- `R(g)` is injective (the adjoint action has inverse `R(g⁻¹)`). -/
theorem rmap_eq_zero_imp {g : Matrix.specialUnitaryGroup (Fin 2) ℂ} {X : SuTwo}
    (h : RMap g X = 0) : X = 0 := by
  have hinv := CovariantHjMinimizer.RMap_apply_inv_cancel g⁻¹ X
  rw [inv_inv] at hinv
  calc X = RMap g⁻¹ (RMap g X) := hinv.symm
    _ = RMap g⁻¹ 0 := by rw [h]
    _ = 0 := map_zero _

/-- **A CONSTRAINT LEVEL OF `1` COLLAPSES THE DOMAIN TO `{0}`, at EVERY background.** `Q_1(U)` is a
pointwise `Ad`-transport (§4), and `Ad` is injective, so `Q_1(U)B = 0` forces `B = 0`. Hence
`ker Q_{ell₀·m}(U)` is the zero subspace whenever `ell₀·m = 1`, and any coercivity statement using
it as its domain is content-free there. This is why `2 ≤ m` (equivalently `2 ≤ ell₁`) is load-bearing
in both statements of §7 and in `Gamma0FibreOneUniform`'s `ell₁ = 2` constraint. -/
theorem kerQ_one_forces_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo)
    (h : ∀ c : CoarseBond L 1, lineCoarseRestrictCov U 1 B c = 0) : B = 0 := by
  funext b
  have hc := h (⟨b.1, FourierFaithfulU1.mem_coarseLattice_one b.1⟩, b.2)
  rw [lineCoarseRestrictCov_one_apply] at hc
  exact rmap_eq_zero_imp hc

/-- **A CONSTRAINT LEVEL EQUAL TO THE FIBRE LEVEL (`m = 1`) KILLS the left-hand side**: the domain
clause `Q_{ell₀·m}(U)B = 0` becomes `Q_{ell₀}(U)B = 0`, which is exactly the left-hand side's norm.
So at `m = 1` the statement reads `γ₀·0 ≤ Δ_k` — content-free, whatever `γ₀`. The content of the
lemma lives strictly at `ell₀ < ell₀·m`. -/
theorem lhs_vanishes_when_constraint_equals_fibre {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo)
    (h : ∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell B c = 0) :
    covCoarseBondInner (lineCoarseRestrictCovLM U ell B) (lineCoarseRestrictCovLM U ell B) = 0 := by
  unfold covCoarseBondInner
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [lineCoarseRestrictCovLM_apply, h c, CovariantHj.hsInner_zero_zero]

#print axioms lineCoarseRestrictCov_zero_level
#print axioms lhs_vanishes_at_level_zero
#print axioms rmap_eq_zero_imp
#print axioms kerQ_one_forces_zero
#print axioms lhs_vanishes_when_constraint_equals_fibre

/-! ### §8a — NON-VACUITY: the `ell₀ = 1` closure fires at a NONZERO field, at EVERY background,
and in particular at a genuinely CURVED one -/

/-- **The `ell₀ = 1` coercivity at a NONZERO field, for EVERY regular `U`.** `genWitness U`
(`RegularUDomainWitnessGeneralU`, the (3.157) reparametrization witness at the background `U`
itself) is axial at level `2`, lies in `ker Q_2(U)` BY CONSTRUCTION, and has strictly positive bond
energy at EVERY `U`. So both sides of the `ell₀ = 1` bound are strictly positive: the inequality
constrains, it does not merely hold. -/
theorem gamma0_fibre_one_nondegenerate
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : frobSupBond U ≤ 1 / 500)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels U).HasOrthogonalProjection] :
    0 < (1 / 25600 : ℝ) * covCoarseBondInner
          (lineCoarseRestrictCovLM U 1 (RegularUDomainWitnessGeneralU.genWitness U))
          (lineCoarseRestrictCovLM U 1 (RegularUDomainWitnessGeneralU.genWitness U)) ∧
      (1 / 25600 : ℝ) * covCoarseBondInner
          (lineCoarseRestrictCovLM U 1 (RegularUDomainWitnessGeneralU.genWitness U))
          (lineCoarseRestrictCovLM U 1 (RegularUDomainWitnessGeneralU.genWitness U))
        ≤ deltaJQuadFormCovFaithful 1 levels U (RegularUDomainWitnessGeneralU.genWitness U) := by
  obtain ⟨γ₀, α₀, hγ₀, hα₀, hall⟩ := gamma0FibreOneUniform_holds
  have hE : covCoarseBondInner (lineCoarseRestrictCovLM U 1
      (RegularUDomainWitnessGeneralU.genWitness U))
      (lineCoarseRestrictCovLM U 1 (RegularUDomainWitnessGeneralU.genWitness U))
      = bondEnergy (RegularUDomainWitnessGeneralU.genWitness U) :=
    covCoarseBondInner_one_eq_bondEnergy U _
  have hpos : 0 < bondEnergy (RegularUDomainWitnessGeneralU.genWitness U) :=
    RegularUDomainWitnessGeneralU.bondEnergy_genWitness_pos hdvd U
  refine ⟨by rw [hE]; positivity, ?_⟩
  -- the bound: re-derive at the explicit numerals rather than through the ∃-witness
  have ha : 0 ≤ frobSupBond U :=
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U
  have hlow := regularU_constant_lower ha hreg
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hthr : 64 * frobSupBond U ^ 2 ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by
    rw [hcast]; nlinarith [ha, hreg]
  have hsmall : 0 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
      - 4 * Real.sqrt 2 * frobSupBond U := by linarith [hlow]
  have key := gamma0_coercivity_fibre_one hL hdvd U levels
    (RegularUDomainWitnessGeneralU.genWitness U)
    (RegularUDomainWitnessGeneralU.genWitness_axial hdvd U)
    (RegularUDomainWitnessGeneralU.genWitness_mem_kerQ hdvd U) hthr hsmall
  have hgam : (1 : ℝ) / 25600
      ≤ (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
          - 4 * Real.sqrt 2 * frobSupBond U) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 160) hlow 2
    calc (1 : ℝ) / 25600 = ((1 : ℝ) / 160) ^ 2 := by norm_num
      _ ≤ _ := h
  nlinarith [key, hgam, hE, hpos]

/-- **`frobSupBond curvedU ≤ 1/500`** — the curved witness of `RegularUCurvedWitness` is inside the
`α₀ = 1/500` regular class (`α₁ ≤ √(8/16000001) = 7.07…e−4`). -/
theorem frobSupBond_curvedU_le : frobSupBond RegularUCurvedWitness.curvedU ≤ 1 / 500 := by
  refine le_trans (RegularUDomainWitnessGeneralU.frobSupBond_tinyU_le
    RegularUCurvedWitness.curvedBond) ?_
  rw [show (1 / 500 : ℝ) = Real.sqrt ((1 / 500 : ℝ) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- **The `ell₀ = 1` closure at a GENUINELY CURVED background.** `curvedU` has a plaquette holonomy
`≠ 1` and is not a gauge transform of any flat configuration
(`RegularUCurvedWitness.curved_regularU_coercivity`), it is inside the `α₀ = 1/500` regular class,
and `curvedA = genWitness curvedU` is a nonzero member of `axial ∩ ker Q_2(curvedU)`. So the
`ell₀ = 1` uniform coercivity is not a statement about flat backgrounds in disguise. -/
theorem gamma0_fibre_one_at_curved (levels : List (KernelSubspace.Level RegularUDomainWitness.witL5))
    [(deltaKernelImageCovH RegularUCurvedWitness.curvedU levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels RegularUCurvedWitness.curvedU).HasOrthogonalProjection] :
    DeltaPrime.holonomyElem RegularUCurvedWitness.curvedU RegularUCurvedWitness.curvedPlaq
        ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      0 < (1 / 25600 : ℝ) * covCoarseBondInner
          (lineCoarseRestrictCovLM RegularUCurvedWitness.curvedU 1 RegularUCurvedWitness.curvedA)
          (lineCoarseRestrictCovLM RegularUCurvedWitness.curvedU 1 RegularUCurvedWitness.curvedA) ∧
      (1 / 25600 : ℝ) * covCoarseBondInner
          (lineCoarseRestrictCovLM RegularUCurvedWitness.curvedU 1 RegularUCurvedWitness.curvedA)
          (lineCoarseRestrictCovLM RegularUCurvedWitness.curvedU 1 RegularUCurvedWitness.curvedA)
        ≤ deltaJQuadFormCovFaithful 1 levels RegularUCurvedWitness.curvedU
            RegularUCurvedWitness.curvedA := by
  obtain ⟨hpos, hbound⟩ := gamma0_fibre_one_nondegenerate
    RegularUDomainWitness.witL5_four_le RegularUDomainWitness.witL5_two_dvd
    RegularUCurvedWitness.curvedU frobSupBond_curvedU_le levels
  exact ⟨RegularUCurvedWitness.curvedU_curvature_ne_one, hpos, hbound⟩

#print axioms gamma0_fibre_one_nondegenerate
#print axioms frobSupBond_curvedU_le
#print axioms gamma0_fibre_one_at_curved

/-- One coarse plaquette's squared coarse curl is at most the whole coarse-curl energy. -/
theorem hsInner_coarseCurl_le_energy {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) :
    hsInner (coarseCurlSuTwo hdvd B p) (coarseCurlSuTwo hdvd B p)
      ≤ coarseCurlEnergySuTwo hdvd B :=
  Finset.single_le_sum
    (f := fun q : CoarsePlaquette L ell =>
      hsInner (coarseCurlSuTwo hdvd B q) (coarseCurlSuTwo hdvd B q))
    (fun q _ => hsInner_self_nonneg _) (Finset.mem_univ p)

#print axioms hsInner_coarseCurl_le_energy

/-! ## §9 — the SUMMED transfer reproduces the tree's witness constant EXACTLY (independent proof) -/

/-- **`ThirdLevelSchurGap.third_level_energy_bound` re-proved through the SUMMED route.** The tree's
banked witness bound `(1/64)·bondEnergy B7 ≤ Δ_k(B7)` at the split `(2,4)` follows from §3 plus the
single coarse-plaquette value `coarseCurl_Q2_B7 = (1/8)•w`. The two proofs share NOTHING: the tree's
goes through `deltaJ_ge_dual_pairing_sq` (Cauchy–Schwarz against the Stokes dual witness `stokesU`,
plus the `ℓ⁷` window-multiplicity norm bound), this one through the minimizer's interpolation
property and the scalar Stokes/Cauchy–Schwarz brick of `FourierFaithfulU1`. That the two routes land
on the SAME constant is a calibration check on §2's factor `ell`. -/
theorem third_level_energy_bound_via_summed :
    (1 / 64 : ℝ) * bondEnergy ThirdLevelWitness.B7
      ≤ deltaJQuadFormCovFaithful 2 (CovariantHjMinimizer.oneLevelUniv ThirdLevelWitness.witL7)
          (trivialU ThirdLevelWitness.witL7) ThirdLevelWitness.B7 := by
  have hsum := schur_ge_ell_coarseCurlEnergy_trivialU (L := ThirdLevelWitness.witL7)
    (by norm_num : 0 < 2) ThirdLevelWitness.witL7_two_dvd
    (CovariantHjMinimizer.oneLevelUniv ThirdLevelWitness.witL7) ThirdLevelWitness.B7
  -- one coarse plaquette of the sum, evaluated
  have hterm := hsInner_coarseCurl_le_energy ThirdLevelWitness.witL7_two_dvd
    (lineCoarseRestrictCovLM (trivialU ThirdLevelWitness.witL7) 2 ThirdLevelWitness.B7)
    ((⟨ThirdLevelWitness.y70, ThirdLevelWitness.y70_coarse2⟩,
      ⟨(0, 1), ThirdLevelWitness.hlt01⟩) : CoarsePlaquette ThirdLevelWitness.witL7 2)
  rw [ThirdLevelWitness.coarseCurl_Q2_B7, hsInner_smul_left,
    ThirdLevelStokes.hsInner_smul_right] at hterm
  rw [ThirdLevelWitness.bondEnergy_B7]
  push_cast at hsum
  nlinarith [hsum, hterm, ThirdLevelWitness.hsInner_witness_pos]

#print axioms third_level_energy_bound_via_summed

/-! ## §10 — THE FULL TARGET, and its decomposition into exactly TWO named primitives -/

/-- **THE GOAL LEMMA, general fibre level AND general regular `U`** — `γ₀` and the regularity
threshold `α₀` quantified OUTSIDE `L`, `ell₀`, `m`, `levels`, `U`, `B`. OPEN. -/
def Gamma0UniformTarget : Prop :=
  ∃ γ₀ α₀ : ℝ, 0 < γ₀ ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent) (ell₀ m : ℕ), 0 < ell₀ → 2 ≤ m →
      (∀ μ : Fin 3, 4 ≤ L μ) →
      (∀ μ : Fin 3, ell₀ ∣ (L μ + 1)) → (∀ μ : Fin 3, (ell₀ * m) ∣ (L μ + 1)) →
      ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ (levels : List (KernelSubspace.Level L))
          [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
          [(curlImageCovHFaithful ell₀ levels U).HasOrthogonalProjection]
          (B : Bond L → SuTwo),
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L (ell₀ * m) →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y (ell₀ * m) →
            ∀ b ∈ staircasePath y x, B b = 0) →
          (∀ c : CoarseBond L (ell₀ * m), lineCoarseRestrictCov U (ell₀ * m) B c = 0) →
          γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U ell₀ B)
              (lineCoarseRestrictCovLM U ell₀ B)
            ≤ deltaJQuadFormCovFaithful ell₀ levels U B

/-- **THE SECOND NAMED PRIMITIVE `[SUMMED-TRANSFER-U]`** — the general-`U` analogue of §3, with the
constant `cT` and the regularity threshold `α₀` quantified OUTSIDE everything, and NO domain
restriction on `B` (§3 proves the `U = 1` case with `cT = 1`, for every `ell₀`, every `levels`,
every `B`). This is the only `U`-dependent input the goal lemma still needs.

**⚠ THE SAME DENOTATION DISCLOSURE APPLIES, and here it is sharper.** Since `Q_1(U) = id` for every
`U` (`lineCoarseRestrictCov_one_eq_self`), at `ell₀ = 1` this `def` asserts
`cT·‖∂B‖²_flat ≤ ‖∂_U B‖²_cov` — a comparison of the FLAT curl energy against the COVARIANT one.
That is a genuine `U`-dependent claim which NOTHING here proves and which would FAIL at any `B` with
`∂_U B = 0 ≠ ∂B`; whether such a `B` exists at a regular curved `U` is untested in this tree. So this
`def` is not merely open: at `ell₀ = 1` it may be FALSE as written, and a lane taking it up should
first settle whether the faithful coarse curl at `U ≠ 1` must be transported. Everything PROVED in
this module is at `U = 1` on the coarse-curl side, where the question does not arise. -/
def SummedTransferRegularU : Prop :=
  ∃ cT α₀ : ℝ, 0 < cT ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent) (ell₀ : ℕ), 0 < ell₀ →
      ∀ (hdvd₀ : ∀ μ : Fin 3, ell₀ ∣ (L μ + 1))
        (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ (levels : List (KernelSubspace.Level L))
          [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
          [(curlImageCovHFaithful ell₀ levels U).HasOrthogonalProjection]
          (B : Bond L → SuTwo),
          cT * coarseCurlEnergySuTwo hdvd₀ (lineCoarseRestrictCovLM U ell₀ B)
            ≤ deltaJQuadFormCovFaithful ell₀ levels U B

/-- **THE FULL DECOMPOSITION, PROVED.** `[SUMMED-TRANSFER-U]` + `[COARSE-CURL-POINCARE]` ⟹ the goal
lemma, with `γ₀ = cT · γc`. Neither primitive mentions `Δ_k` and `[COARSE-CURL-POINCARE]`; the
`U`-dependence is entirely inside `[SUMMED-TRANSFER-U]`, and the domain restriction (axial gauge,
`ker Q_{ell₀·m}`) is entirely inside `[COARSE-CURL-POINCARE]`. So the two primitives are
independent: one is an operator inequality with no domain, the other a Poincaré inequality with no
operator.

**⚠ ANTECEDENT UNSATISFIABLE, 2026-07-27 (S75).** `CoarseCurlPoincare.not_coarseCurlPoincareUniform`
refutes the `[COARSE-CURL-POINCARE]` conjunct outright, and
`CoarseCurlScaleTwo.not_coarseCurlPoincareScaled r` refutes every decaying relaxation of it at
`ell₀ ≥ 2`. The decomposition below is therefore a TRUE IMPLICATION WITH AN UNSATISFIABLE HYPOTHESIS:
it yields `Gamma0UniformTarget` for no nontrivial scale, and it must not be used as a route. It is
retained because the DECOMPOSITION is still informative (it localizes exactly which half died: the
Poincaré half, not `[SUMMED-TRANSFER-U]`). The live route is `Balaban/AlphaAnalyticity.lean`. -/
theorem gamma0UniformTarget_of_two_primitives :
    SummedTransferRegularU → CoarseCurlPoincareUniform → Gamma0UniformTarget := by
  rintro ⟨cT, α₀, hcT, hα₀, htrans⟩ ⟨γc, hγc, hpoin⟩
  refine ⟨cT * γc, α₀, mul_pos hcT hγc, hα₀, ?_⟩
  intro L ell₀ m hell₀ hm hL hdvd₀ hdvdm U hreg levels _ _ B hadm hker
  have h1 := hpoin L ell₀ m hell₀ hm hL hdvd₀ hdvdm U B hadm hker
  have h2 := htrans L ell₀ hell₀ hdvd₀ U hreg levels B
  nlinarith [h1, h2, hcT]

#print axioms gamma0UniformTarget_of_two_primitives

/-! ## §11 — WHY `[SUMMED-TRANSFER-U]` RESISTS: the obstruction, as a theorem with a witness

The general-`U` transfer breaks the exact Stokes commutation `∂₁' ∘ Q_ell = P_ell ∘ d` by a curvature
term, and every available bound on that term (`RegularUPerturbation.norm_curlDrift_L2_le_sup`,
`RegularUQChain.coarseDriftEnergy_le`) measures the error against `bondEnergy` of the field it is
applied to — here the MINIMIZER `H_j B`, an element of the fibre `B + ker Q_ell(U)`. Converting that
into an error against `‖D_U(H_j B)‖² = Δ_k(B)` requires a REVERSE Poincaré on the fibre.

`ThirdLevelSchurGap` recorded this as "near-circular" prose, reached through the DUALITY route. The
witness below turns it into a theorem, and shows it is not a duality artifact: **on `ker Q_ell(1)`
alone the reverse Poincaré is FALSE — for every constant.** The field `chiField w` is a nonzero,
CURL-FREE element of `ker Q_2(1)`. So any general-`U` transfer must use the fibre's gauge clause
`R(∂*_U ·) = 0` in an essential way; with `levels` abstract, that clause carries no content, and the
route is blocked at that exact point rather than merely difficult. -/

/-- The alternating sign in coordinate `0`. -/
noncomputable def chi (x : PeriodicLatticeSite L) : ℝ := (-1 : ℝ) ^ ((x 0).val)

/-- `chi` flips under a coordinate-`0` shift, ON THE TORUS: the wrap-around case needs `L 0` ODD,
which is exactly `2 ∣ L 0 + 1`. (Degenerate-point control: without it, `chi` is not alternating
across the seam and the witness below fails.) -/
theorem chi_shift_zero (h2 : (2 : ℕ) ∣ (L 0 + 1)) (x : PeriodicLatticeSite L) :
    chi (periodicLatticeShift x 0) = - chi x := by
  have hcoord : (periodicLatticeShift x (0 : Fin 3)) 0 = x 0 + 1 := by
    simp only [periodicLatticeShift, Function.update_self]
  unfold chi
  rw [hcoord]
  rcases eq_or_lt_of_le (Fin.le_last (x 0)) with heq | hlt
  · -- the seam: `x 0 = L 0`, so the shifted value is `0`
    have hodd : Odd (L 0) := by
      obtain ⟨t, ht⟩ := h2
      refine ⟨t - 1, ?_⟩
      omega
    rw [heq, Fin.last_add_one, Fin.val_zero, Fin.val_last, pow_zero, hodd.neg_one_pow]
    norm_num
  · rw [Fin.val_add_one_of_lt hlt, pow_succ]
    ring

/-- `chi` is unchanged by a shift in any OTHER coordinate. -/
theorem chi_shift_other {μ : Fin 3} (hμ : μ ≠ 0) (x : PeriodicLatticeSite L) :
    chi (periodicLatticeShift x μ) = chi x := by
  unfold chi periodicLatticeShift
  rw [Function.update_of_ne (Ne.symm hμ)]

/-- **The witness field**: `w` on every direction-`0` bond with the alternating sign `chi`, zero on
the other two directions. -/
noncomputable def chiField (w : SuTwo) : Bond L → SuTwo :=
  fun b => if b.2 = 0 then chi b.1 • w else 0

/-- **`chiField w` is CURL-FREE at `U = 1`.** In every plaquette orientation the second direction is
nonzero (`μ < ν` forces `ν ≠ 0`), so only the two direction-`0` terms survive, and they cancel
because `chi` does not depend on the coordinates `1, 2` (`chi_shift_other`). -/
theorem flatCurl_chiField (w : SuTwo) : flatCurlValue (chiField (L := L) w) = 0 := by
  funext p
  obtain ⟨x, ⟨⟨μ, ν⟩, hlt⟩⟩ := p
  have hν : ν ≠ 0 := by
    intro h
    rw [h, Fin.lt_def, Fin.val_zero] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  show chiField w (x, μ) + chiField w (periodicLatticeShift x μ, ν)
      - chiField w (periodicLatticeShift x ν, μ) - chiField w (x, ν) = 0
  unfold chiField
  simp only [if_neg hν]
  by_cases hμ : μ = 0
  · rw [if_pos hμ, if_pos hμ, chi_shift_other hν x]
    abel
  · rw [if_neg hμ, if_neg hμ]
    abel

/-- **`chiField w ∈ ker Q_2(1)`.** Each two-term line integral along direction `0` cancels
(`chi_shift_zero`), and the other two directions carry no field at all. -/
theorem chiField_mem_kerQ2 (h2 : (2 : ℕ) ∣ (L 0 + 1)) (w : SuTwo)
    (c : CoarseBond L 2) : lineCoarseRestrictCov (trivialU L) 2 (chiField w) c = 0 := by
  rw [lineCoarseRestrictCov_trivialU]
  unfold lineCoarseRestrictSuTwo
  have hinner : ∀ x ∈ blockOf c.1.1 2,
      (∑ i ∈ Finset.range 2, chiField w (QOne.pathSite x c.2 i, c.2)) = 0 := by
    intro x _
    rw [Finset.sum_range_succ, Finset.sum_range_one, QOne.pathSite_zero]
    show chiField w (x, c.2) + chiField w (QOne.pathSite x c.2 1, c.2) = 0
    rw [QOne.pathSite_succ, QOne.pathSite_zero]
    unfold chiField
    by_cases hμ : c.2 = 0
    · rw [if_pos hμ, if_pos hμ, hμ, chi_shift_zero h2 x, neg_smul]
      abel
    · rw [if_neg hμ, if_neg hμ]
      abel
  rw [Finset.sum_congr rfl hinner, Finset.sum_const_zero, smul_zero]

/-- `0 < bondEnergy (chiField w)` for `w ≠ 0` — the direction-`0` bond at the origin contributes
`‖w‖² > 0`. -/
theorem bondEnergy_chiField_pos {w : SuTwo} (hw : w ≠ 0) :
    0 < bondEnergy (chiField (L := L) w) := by
  have hb : ((RegularUDomainWitnessGeneralU.siteZero L), (0 : Fin 3)) ∈
      (Finset.univ : Finset (Bond L)) := Finset.mem_univ _
  have hval : chiField (L := L) w ((RegularUDomainWitnessGeneralU.siteZero L), (0 : Fin 3)) = w := by
    unfold chiField chi
    rw [if_pos rfl]
    have h0 : ((RegularUDomainWitnessGeneralU.siteZero L) 0).val = 0 := by
      show ((0 : Fin (L 0 + 1))).val = 0
      exact Fin.val_zero _
    rw [h0, pow_zero, one_smul]
  have hpos : (0 : ℝ) < ‖chiField (L := L) w
      ((RegularUDomainWitnessGeneralU.siteZero L), (0 : Fin 3))‖ ^ 2 := by
    rw [hval]
    have : ‖w‖ ≠ 0 := by
      simpa using hw
    positivity
  unfold bondEnergy
  exact lt_of_lt_of_le hpos
    (Finset.single_le_sum (f := fun b : Bond L => ‖chiField (L := L) w b‖ ^ 2)
      (fun b _ => sq_nonneg _) hb)

/-- **THE OBSTRUCTION, PROVED: no reverse Poincaré on `ker Q_2(1)`, for ANY constant.** `chiField w`
is a nonzero element of `ker Q_2(1)` whose covariant curl energy at `U = 1` is exactly `0`, so
`bondEnergy A ≤ K · ‖∂A‖²` fails on that subspace for every `K`. Consequently the `O(α₁·√bondEnergy)`
error of every general-`U` drift bound CANNOT be converted into an `O(α₁·‖D_U ·‖)` error on the fibre
using the `ker Q` clause alone — which is precisely the point at which `[SUMMED-TRANSFER-U]` (and
`[STOKES-COMM-U]` before it) stops. The gauge clause of the fibre is therefore load-bearing, not
decorative. -/
theorem no_reverse_poincare_on_kerQ (h2 : (2 : ℕ) ∣ (L 0 + 1)) {w : SuTwo} (hw : w ≠ 0) (K : ℝ) :
    (∀ c : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 (chiField w) c = 0)
      ∧ plaqEnergy (curlCovariantLM (trivialU L) (chiField (L := L) w)) = 0
      ∧ ¬ (bondEnergy (chiField (L := L) w)
            ≤ K * plaqEnergy (curlCovariantLM (trivialU L) (chiField (L := L) w))) := by
  have hcurl : curlCovariantLM (trivialU L) (chiField (L := L) w) = 0 := by
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]
    exact flatCurl_chiField w
  have hzero : plaqEnergy (curlCovariantLM (trivialU L) (chiField (L := L) w)) = 0 := by
    rw [hcurl]
    unfold plaqEnergy
    simp
  refine ⟨chiField_mem_kerQ2 h2 w, hzero, ?_⟩
  rw [hzero, mul_zero]
  exact not_le.mpr (bondEnergy_chiField_pos hw)

/-- **AND THE AXIAL-GAUGE CLAUSE IN THE GOAL LEMMA'S DOMAIN IS LOAD-BEARING.** Drop it and the
`ell₀ = 1` statement becomes FALSE, for EVERY positive `γ₀`: `chiField w` satisfies the `ker Q_2(1)`
clause, has strictly positive `‖Q_1(1)·‖²` (= `bondEnergy`, §4), and has `Δ_k = 0`. So the domain
restriction is not a convenience — the lemma is false without it. -/
theorem no_coercivity_without_axial (h2 : (2 : ℕ) ∣ (L 0 + 1)) {w : SuTwo} (hw : w ≠ 0)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels (trivialU L)).HasOrthogonalProjection]
    {γ₀ : ℝ} (hγ₀ : 0 < γ₀) :
    ¬ (γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) 1 (chiField w))
          (lineCoarseRestrictCovLM (trivialU L) 1 (chiField w))
        ≤ deltaJQuadFormCovFaithful 1 levels (trivialU L) (chiField (L := L) w)) := by
  have hcurl : curlCovariantLM (trivialU L) (chiField (L := L) w) = 0 := by
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]
    exact flatCurl_chiField w
  have hdelta : deltaJQuadFormCovFaithful 1 levels (trivialU L) (chiField (L := L) w) = 0 := by
    rw [deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm]
    show covPlaqInner (curlCovariantLM (trivialU L) (chiField (L := L) w))
      (curlCovariantLM (trivialU L) (chiField (L := L) w)) = 0
    rw [hcurl]
    unfold covPlaqInner
    simp [CovariantHj.hsInner_zero_zero]
  rw [hdelta, covCoarseBondInner_one_eq_bondEnergy]
  exact not_le.mpr (mul_pos hγ₀ (bondEnergy_chiField_pos hw))

#print axioms chi_shift_zero
#print axioms chi_shift_other
#print axioms flatCurl_chiField
#print axioms chiField_mem_kerQ2
#print axioms bondEnergy_chiField_pos
#print axioms no_reverse_poincare_on_kerQ
#print axioms no_coercivity_without_axial

/-! ### §11a — the MUST-NOT-FIRE control: the witness does NOT refute the DIV-FREE version

`gaugeConstraintSubspaceCovFaithful`'s second clause is `R(∂*_U A) = 0` with
`R = P_{Δ_U(kernelSubspaceCov levels)}`. At `levels = oneLevelUniv` this is a genuine
divergence-type condition, so the fibre is `ker Q_ell(U) ∩ {gauge}` and the primitive the general-`U`
transfer actually needs is a Poincaré on THAT intersection.

The control below is what stops §11 from over-claiming: `chiField w` has divergence `−2·chi(y)•w ≠ 0`,
so it is NOT in the fibre's gauge clause and does NOT refute the div-free Poincaré. Conclusion, stated
exactly: `[SUMMED-TRANSFER-U]` needs `[KERQ-DIVFREE-POINCARE]` (below), the ker-`Q`-only form of which
is REFUTED (§11) while the div-free form is UNTOUCHED by this witness — ~~open, not refuted~~.
**⚠ SUPERSEDED 2026-07-27 (S75): the div-free form is REFUTED as well**, by a different witness,
`CoarseCurlPoincare.not_kerQDivFreePoincare`. This control is still a correct control — the `chiField`
witness really does not reach the div-free form — but "open, not refuted" is no longer the standing of
`[KERQ-DIVFREE-POINCARE]`. -/

/-- `chi` flips under a BACKWARD coordinate-`0` shift as well. -/
theorem chi_shiftBack_zero (h2 : (2 : ℕ) ∣ (L 0 + 1)) (y : PeriodicLatticeSite L) :
    chi (CovariantHjMinimizer.periodicLatticeShiftBack y 0) = - chi y := by
  have h := chi_shift_zero h2 (CovariantHjMinimizer.periodicLatticeShiftBack y 0)
  rw [CovariantHjMinimizer.periodicLatticeShift_shiftBack] at h
  linarith [h]

/-- **The witness is NOT divergence-free**: `∂*(chiField w)(y) = (−2·chi y)•w`, nonzero for
`w ≠ 0`. So it lies OUTSIDE `gaugeConstraintSubspaceCovFaithful`, and the refutation of §11 does not
extend to the div-free Poincaré — the honest statement of what remains open. -/
theorem gradAdjoint_chiField (h2 : (2 : ℕ) ∣ (L 0 + 1)) (w : SuTwo)
    (y : PeriodicLatticeSite L) :
    CovariantHjMinimizer.gradCovariantAdjointValue (trivialU L) (chiField w) y
      = (-2 * chi y) • w := by
  unfold CovariantHjMinimizer.gradCovariantAdjointValue
  have hone : ∀ b : Bond L, RMap ((trivialU L) b)⁻¹ = LinearMap.id := by
    intro b
    show RMap ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))⁻¹ = _
    rw [inv_one, RMap_one]
  have hterm : ∀ μ : Fin 3,
      (RMap ((trivialU L) (CovariantHjMinimizer.periodicLatticeShiftBack y μ, μ))⁻¹
          (chiField w (CovariantHjMinimizer.periodicLatticeShiftBack y μ, μ))
        - chiField w (y, μ))
      = if μ = 0 then (-2 * chi y) • w else 0 := by
    intro μ
    rw [hone]
    by_cases hμ : μ = 0
    · subst hμ
      show chiField w (CovariantHjMinimizer.periodicLatticeShiftBack y 0, (0 : Fin 3))
        - chiField w (y, (0 : Fin 3)) = _
      unfold chiField
      rw [if_pos rfl, if_pos rfl, if_pos rfl, chi_shiftBack_zero h2 y]
      rw [← sub_smul]
      congr 1
      ring
    · show chiField w (CovariantHjMinimizer.periodicLatticeShiftBack y μ, μ)
        - chiField w (y, μ) = _
      unfold chiField
      rw [if_neg hμ, if_neg hμ, if_neg hμ, sub_zero]
  rw [Finset.sum_congr rfl (fun μ _ => hterm μ)]
  rw [Finset.sum_ite_eq' Finset.univ (0 : Fin 3) (fun _ => (-2 * chi y) • w)]
  rw [if_pos (Finset.mem_univ _)]

/-- …and it is genuinely nonzero, so the witness is strictly outside the gauge clause. -/
theorem gradAdjoint_chiField_ne_zero (h2 : (2 : ℕ) ∣ (L 0 + 1)) {w : SuTwo} (hw : w ≠ 0) :
    CovariantHjMinimizer.gradCovariantAdjointValue (trivialU L) (chiField w)
        (RegularUDomainWitnessGeneralU.siteZero L) ≠ 0 := by
  rw [gradAdjoint_chiField h2]
  have h0 : chi (RegularUDomainWitnessGeneralU.siteZero L) = 1 := by
    unfold chi
    have : ((RegularUDomainWitnessGeneralU.siteZero L) 0).val = 0 := by
      show ((0 : Fin (L 0 + 1))).val = 0
      exact Fin.val_zero _
    rw [this, pow_zero]
  rw [h0]
  intro hzero
  rw [smul_eq_zero] at hzero
  rcases hzero with h | h
  · norm_num at h
  · exact hw h

/-- **THE REMAINING PRIMITIVE `[KERQ-DIVFREE-POINCARE]`**, stated with the constant OUTSIDE
everything: a Poincaré inequality on `ker Q_ell(1) ∩ {∂*A = 0}` at `U = 1`. §11 refutes the version
WITHOUT the divergence clause; §11a shows that refutation does not reach this one. `def : Prop` —
OPEN. This is what `[SUMMED-TRANSFER-U]` needs and does not have. -/
def KerQDivFreePoincare : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ (L : PeriodicLatticeExtent) (ell : ℕ), 0 < ell → (∀ μ : Fin 3, ell ∣ (L μ + 1)) →
      ∀ (A : Bond L → SuTwo),
        (∀ c : CoarseBond L ell, lineCoarseRestrictCov (trivialU L) ell A c = 0) →
        (∀ y : PeriodicLatticeSite L,
          CovariantHjMinimizer.gradCovariantAdjointValue (trivialU L) A y = 0) →
        bondEnergy A ≤ K * plaqEnergy (curlCovariantLM (trivialU L) A)

#print axioms chi_shiftBack_zero
#print axioms gradAdjoint_chiField
#print axioms gradAdjoint_chiField_ne_zero

end AdalyFormal.Balaban.RegularUGamma0
