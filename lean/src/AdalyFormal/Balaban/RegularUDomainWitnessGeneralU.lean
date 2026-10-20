/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.FullReparamC
import AdalyFormal.Balaban.RegularUCoercivityFull

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[REGU-DOMAIN-NONVAC-GENERALU]` — the domain `axial-gauge ∩ ker Q₁(U)` is nonzero at EVERY `U`

`RegularUDomainWitness.lean` closed `[REGU-DOMAIN-NONVAC]` only at `U = trivialU`: its witness
`witA` is a `+w`/`−w` pair whose coarse block-sum cancels, and that cancellation is a `U = 1`
phenomenon (at `U ≠ 1` the two contributions are transported by DIFFERENT path holonomies). Its §7
recorded the general-`U` question as open and named the missing primitive: a construction landing in
`ker Q₁(U)` BY CONSTRUCTION rather than by cancellation.

That primitive now exists — `FullReparamC.fullC`, the full multi-constraint `(3.157)`
reparametrization — and `FullReparamC` §9 already assembles the three properties at arbitrary `U`
(`admissibleWitness_ne_zero`, `admissibleWitness_mem_kerQ`, `admissibleWitness_axialGauge`).

**This module contributes exactly two things and re-derives nothing** (LAW-19):

1. **§1–§2** — the bundle: the three §9 facts, at `ell = 2` and the coarse origin, in the EXACT
   hypothesis shape of `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU`
   (`hadm` / `hkerU`), for `∀ U`, plus strict positivity of `bondEnergy` at the witness (so the
   instantiated inequality is not `0 ≤ deltaJ`).
2. **§3–§4** — an EXPLICIT NON-TRIVIAL background `tinyU b₀` (a rational `SU(2)` rotation
   `M(p,q) = !![p,q; −q,p]` with `p = 15999999/16000001`, `q = 8000/16000001`, placed on a SINGLE
   bond `b₀`) whose `frobSupBond` is small enough to satisfy the target theorem's `hthr`/`hsmall`,
   and the target coercivity INSTANTIATED there. This is the first instance of the regular-`U`
   coercivity at a background that is not `trivialU`.

## What is NOT claimed

* The witness `genWitness U` is the `fullC`-image of a single free bond. It is one named element of
  the domain, not a basis, a dimension count, or a rank statement for `Q₁(U)`. §7 of
  `RegularUDomainWitness` listed the dimension route as an alternative; it is still not built, and
  it is not needed for non-vacuity.
* `tinyU b₀` is a genuinely non-trivial link configuration (`tinyU_ne_trivialU`) supported on ONE
  bond. §4 also records what is NOT proved about it: no statement is made here about its curvature.
* Nothing here changes the honest scope of `deltaJ_regularU_coercive_on_kerQU` itself (leading
  covariant term, single scale, modulo `[UNIF-ALPHA]`) — see that module's docstring.

## S75 propagation note (for the single ledger writer, not actionable in this module's write-scope)

`Balaban/RegularUDomainWitness.lean` §7 (its final docstring block) states that
`[REGU-DOMAIN-NONVAC-GENERALU]` "was attempted in this pass and is NOT closed". That text is
SUPERSEDED by this module; the module is outside this lane's write-scope and was not edited.
-/

namespace AdalyFormal.Balaban.RegularUDomainWitnessGeneralU

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice
  staircasePath)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond frobNorm_le_frobSupBond
  frobSupBond_nonneg)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm)
open AdalyFormal.Balaban.FullReparamC (freeBond admissibleWitness admissibleWitness_at_freeBond
  admissibleWitness_ne_zero admissibleWitness_mem_kerQ admissibleWitness_axialGauge)
open AdalyFormal.Balaban.RegularUCoercivityFull (deltaJ_regularU_coercive_on_kerQU)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the coarse origin, and the named general-`U` witness -/

/-- The origin site. It is coarse for EVERY block side `ell` (all coordinates are `0`), so no
divisibility or size hypothesis is needed to place the witness. -/
def siteZero (L : PeriodicLatticeExtent) : PeriodicLatticeSite L := fun _ => 0

theorem siteZero_coarse (ell : ℕ) : siteZero L ∈ CoarseLattice L ell := by
  rw [mem_CoarseLattice]
  intro μ
  show (0 : Fin (L μ + 1)).val % ell = 0
  simp

/-- **The named general-`U` admissible witness**: the `(3.157)` reparametrization `fullC U 2`
applied to the field supported on the single `freeBond 2 (siteZero L)` — a bond that lies on no
axial staircase and is the dropped bond of no coarse constraint (`FullReparamC` §9). It is a `def`,
not an existential: there is no free data for a prover to choose (S91). -/
noncomputable def genWitness (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    : Bond L → SuTwo :=
  admissibleWitness U 2 (siteZero L)

/-- `genWitness U` takes the value `suTwoWitness` at the free bond — for every `U`. This is the
single source of its non-vanishing, and it is `U`-independent because `fullC` acts as the identity
off the dropped bonds. -/
theorem genWitness_at_freeBond (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    genWitness U (freeBond 2 (siteZero L)) = suTwoWitness :=
  admissibleWitness_at_freeBond (by norm_num) hdvd U (siteZero L) (siteZero_coarse 2)

theorem genWitness_ne_zero (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    genWitness U ≠ 0 :=
  admissibleWitness_ne_zero (by norm_num) hdvd U (siteZero L) (siteZero_coarse 2)

/-- **The axial gauge, at every `U`.** `fullC` preserves vanishing on every staircase `Γ_{y,x}`, and
the seed is supported on a bond that lies on none. Exactly the `hadm` hypothesis of
`deltaJ_regularU_coercive_on_kerQU`. -/
theorem genWitness_axial (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 →
      ∀ b ∈ staircasePath y x, genWitness U b = 0 :=
  admissibleWitness_axialGauge (by norm_num) hdvd U (siteZero L) (siteZero_coarse 2)

/-- **The covariant constraint, at every `U`** — `Q₁(U)·genWitness U = 0` at EVERY coarse bond, BY
CONSTRUCTION (`fullC` solves the constraint on the dropped bonds), not by a `U = 1` cancellation.
Exactly the `hkerU` hypothesis of `deltaJ_regularU_coercive_on_kerQU`. -/
theorem genWitness_mem_kerQ (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ∀ c : CoarseBond L 2, lineCoarseRestrictCov U 2 (genWitness U) c = 0 :=
  admissibleWitness_mem_kerQ (by norm_num) hdvd U (siteZero L)

/-! ## §2 — `[REGU-DOMAIN-NONVAC-GENERALU]`: the bundle -/

/-- **`[REGU-DOMAIN-NONVAC-GENERALU]` CLOSED.** For EVERY compatible extent (`2 ∣ L μ + 1`) and
EVERY background `U`, the domain `axial-gauge ∩ ker Q₁(U)` of
`RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` contains the explicit NONZERO field
`genWitness U`. So the target theorem is non-vacuous at every background, not only at `trivialU`.

Stated in NAMED form (the witness is a `def`); the existential form is the corollary below. -/
theorem regularU_domain_nonvacuous_generalU
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
        ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 →
          ∀ b ∈ staircasePath y x, genWitness U b = 0) ∧
      (∀ c : CoarseBond L 2, lineCoarseRestrictCov U 2 (genWitness U) c = 0) ∧
      genWitness U ≠ 0 :=
  ⟨genWitness_axial hdvd U, genWitness_mem_kerQ hdvd U, genWitness_ne_zero hdvd U⟩

/-- Existential restatement. Kept as a COROLLARY of the named form (S91: the named form is what
carries the content; this one exists only to match the shape a consumer may want). -/
theorem exists_nonzero_admissible_generalU
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ∃ A : Bond L → SuTwo, A ≠ 0 ∧
      (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
        ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 →
          ∀ b ∈ staircasePath y x, A b = 0) ∧
      (∀ c : CoarseBond L 2, lineCoarseRestrictCov U 2 A c = 0) :=
  ⟨genWitness U, genWitness_ne_zero hdvd U, genWitness_axial hdvd U, genWitness_mem_kerQ hdvd U⟩

/-- **The instantiated inequality is not `0 ≤ deltaJ`.** `bondEnergy (genWitness U) > 0` at every
`U`, because the witness equals `suTwoWitness ≠ 0` at the free bond. -/
theorem bondEnergy_genWitness_pos (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    0 < bondEnergy (genWitness U) := by
  have hle : ‖genWitness U (freeBond 2 (siteZero L))‖ ^ 2
      ≤ ∑ b : Bond L, ‖genWitness U b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b : Bond L => ‖genWitness U b‖ ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ _)
  have hpos : (0 : ℝ) < ‖genWitness U (freeBond 2 (siteZero L))‖ ^ 2 := by
    have hne : genWitness U (freeBond 2 (siteZero L)) ≠ 0 := by
      rw [genWitness_at_freeBond hdvd U]; exact suTwoWitness_ne_zero
    have : (0 : ℝ) < ‖genWitness U (freeBond 2 (siteZero L))‖ := norm_pos_iff.mpr hne
    positivity
  unfold bondEnergy
  linarith

/-! ## §3 — an EXPLICIT NON-TRIVIAL background strictly inside the smallness threshold

The target theorem's two hypotheses are `hthr : 64·α₁² ≤ γ₀` and `hsmall : 4√2·α₁ ≤ √(γ₀ − 64·α₁²)`,
`α₁ = frobSupBond U`, `γ₀ = (1/108)(1/2⁴) = 1/1728`. Both are satisfied by `α₁ = 0`, which is why
`RegularUDomainWitness` could instantiate at `trivialU`. Here we exhibit a background with
`α₁ > 0` — strictly positive distance from `1` — that still clears both. -/

/-- `M(p,q) = !![p,q; −q,p]` with the Pythagorean pair `p = 15999999/16000001`,
`q = 8000/16000001`, generated by `(m,n) = (4000,1)` (`m²−n² = 15999999`, `2mn = 8000`,
`m²+n² = 16000001`), so `p² + q² = 1` is a RATIONAL identity — no `Real.cos`/`Real.sin`, everything
`norm_num`-checkable.

LAW-19 note: this REUSES the shape and the membership-proof pattern of
`HolonomyDomination.smallM = M(24/25,7/25)`; only the entries differ, and they must, because
`frobNorm(smallM − 1) = 2/5`, which is three orders of magnitude ABOVE the threshold
`√(γ₀/96) ≈ 1/407` that this section needs. -/
noncomputable def tinyM : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(15999999 / 16000001 : ℂ), (8000 / 16000001 : ℂ);
     (-(8000 / 16000001) : ℂ), (15999999 / 16000001 : ℂ)]

theorem tinyM_mem_unitaryGroup : tinyM ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tinyM, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im] <;>
    norm_num

theorem tinyM_det : tinyM.det = 1 := by
  simp only [tinyM, Matrix.det_fin_two_of]
  norm_num

theorem tinyM_mem : tinyM ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨tinyM_mem_unitaryGroup, tinyM_det⟩

/-- `M(15999999/16000001, 8000/16000001)`, packaged as a group element. -/
noncomputable def tinyMElem : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨tinyM, tinyM_mem⟩

theorem tinyMElem_ne_one : tinyMElem ≠ 1 := by
  intro hcontra
  have h : (tinyMElem : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    congrArg (Subtype.val) hcontra
  have := congrFun (congrFun h 0) 1
  simp [tinyMElem, tinyM] at this

/-- **`frobSq(M − 1) = 8/16000001`, exactly.** `M − 1 = !![p−1, q; −q, p−1]` with `p − 1 = −2/D`,
`q = 8000/D`, `D = 16000001`, so `frobSq = (2·4 + 2·8000²)/D² = 128000008/D² = 8/D` (using
`128000008 = 8·D`). An exact rational value, not a bound. -/
theorem frobSq_tinyM_sub_one :
    AdalyFormal.Balaban.RMapLipschitz.frobSq (tinyM - 1) = 8 / 16000001 := by
  unfold AdalyFormal.Balaban.RMapLipschitz.frobSq
  simp only [Matrix.sub_apply, Matrix.one_apply, tinyM]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.normSq]

/-- **The single-bond non-trivial background.** `tinyU b₀` equals `M` on the bond `b₀` and `1`
everywhere else — a genuinely non-trivial link configuration whose `sup_b`-distance from `1` is
exactly `√(8/16000001) ≈ 7.07·10⁻⁴`, comfortably under the threshold. -/
noncomputable def tinyU (b₀ : Bond L) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
  fun b => if b = b₀ then tinyMElem else 1

theorem tinyU_ne_trivialU (b₀ : Bond L) : tinyU b₀ ≠ trivialU L := by
  intro h
  have := congrFun h b₀
  rw [tinyU, if_pos rfl] at this
  exact tinyMElem_ne_one this

/-- **`α₁ = frobSupBond (tinyU b₀) ≤ √(8/16000001)`** — the upper bound feeding `hthr`/`hsmall`. -/
theorem frobSupBond_tinyU_le (b₀ : Bond L) :
    frobSupBond (tinyU b₀) ≤ Real.sqrt (8 / 16000001) := by
  unfold frobSupBond
  refine Finset.sup'_le _ _ (fun b _ => ?_)
  by_cases hb : b = b₀
  · have hval : ((tinyU b₀ b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = tinyM := by
      rw [tinyU, if_pos hb]; rfl
    rw [hval]
    unfold AdalyFormal.Balaban.RMapLipschitz.frobNorm
    rw [frobSq_tinyM_sub_one]
  · have hval : ((tinyU b₀ b : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [tinyU, if_neg hb]; rfl
    rw [hval, sub_self, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
    positivity

/-- **`α₁ > 0`: the background is genuinely OFF `U = 1`.** `frobSupBond` is a `sup` over bonds and
`b₀` contributes `√(8/16000001) > 0`. This is what makes §4 a non-trivial instance: the smallness
hypotheses are cleared with room to spare, but NOT by `α₁ = 0`. -/
theorem frobSupBond_tinyU_pos (b₀ : Bond L) : 0 < frobSupBond (tinyU b₀) := by
  have hval : ((tinyU b₀ b₀ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = tinyM := by
    rw [tinyU, if_pos rfl]; rfl
  have hle := frobNorm_le_frobSupBond (tinyU b₀) b₀
  rw [hval] at hle
  have hpos : (0 : ℝ) < AdalyFormal.Balaban.RMapLipschitz.frobNorm (tinyM - 1) := by
    unfold AdalyFormal.Balaban.RMapLipschitz.frobNorm
    rw [frobSq_tinyM_sub_one]
    exact Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- `α₁² ≤ 8/16000001` — the squared form actually used by both hypotheses. -/
theorem frobSupBond_tinyU_sq_le (b₀ : Bond L) :
    frobSupBond (tinyU b₀) ^ 2 ≤ 8 / 16000001 := by
  have h1 := frobSupBond_tinyU_le b₀
  have h0 := frobSupBond_nonneg (tinyU b₀)
  have hs : Real.sqrt (8 / 16000001 : ℝ) ^ 2 = 8 / 16000001 :=
    Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (8 / 16000001 : ℝ)]

/-! ## §4 — the target coercivity, INSTANTIATED at a background that is NOT `trivialU` -/

/-- **`hthr` at `tinyU b₀`**: `64·α₁² ≤ 512/16000001 ≤ 1/1728 = γ₀` (`512·1728 = 884736 ≤
16000001`). -/
theorem hthr_tinyU (b₀ : Bond L) :
    64 * frobSupBond (tinyU b₀) ^ 2 ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by
  have h := frobSupBond_tinyU_sq_le b₀
  have : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [this]
  nlinarith

/-- **`hsmall` at `tinyU b₀`**: `(4√2·α₁)² = 32·α₁² ≤ γ₀ − 64·α₁²` because `96·α₁² ≤
768/16000001 ≤ γ₀` (`768·1728 = 1327104 ≤ 16000001`); take square roots. -/
theorem hsmall_tinyU (b₀ : Bond L) :
    0 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond (tinyU b₀) ^ 2)
      - 4 * Real.sqrt 2 * frobSupBond (tinyU b₀) := by
  have hsq := frobSupBond_tinyU_sq_le b₀
  have h0 := frobSupBond_nonneg (tinyU b₀)
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hcast]
  set a : ℝ := frobSupBond (tinyU b₀) with ha
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ 4 * Real.sqrt 2 * a := by positivity
  have hkey : (4 * Real.sqrt 2 * a) ^ 2 ≤ (1 / 108) * (1 / (2 : ℝ) ^ 4) - 64 * a ^ 2 := by
    have hexp : (4 * Real.sqrt 2 * a) ^ 2 = 32 * a ^ 2 := by
      rw [mul_pow, mul_pow, h2]; ring
    rw [hexp]; nlinarith
  have := Real.sqrt_le_sqrt hkey
  rw [Real.sqrt_sq hnn] at this
  linarith

/-- **The coercivity constant at `tinyU b₀` is at least `1/4000`.**
`√(γ₀ − 64α₁²) ≥ 232/10000` (since `(232/10000)² ≤ 1/1728 − 512/16000001`) and
`4√2·α₁ ≤ 4017/1000000` (since `√2 ≤ 141422/100000` and `α₁ ≤ 71/100000`), so the difference is
at least `19183/1000000` and its square exceeds `1/4000`. -/
theorem gamma_tinyU_ge (b₀ : Bond L) :
    (1 / 4000 : ℝ) ≤
      (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond (tinyU b₀) ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond (tinyU b₀)) ^ 2 := by
  have hsq := frobSupBond_tinyU_sq_le b₀
  have h0 := frobSupBond_nonneg (tinyU b₀)
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hcast]
  set a : ℝ := frobSupBond (tinyU b₀) with ha
  -- `a ≤ 71/100000`
  have hale : a ≤ 71 / 100000 := by nlinarith
  -- `√2 ≤ 141422/100000`
  have hs2 : Real.sqrt 2 ≤ 141422 / 100000 := by
    have hrw : (141422 / 100000 : ℝ) = Real.sqrt ((141422 / 100000 : ℝ) ^ 2) :=
      (Real.sqrt_sq (by norm_num)).symm
    rw [hrw]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  -- upper bound on the subtracted term
  have hT : 4 * Real.sqrt 2 * a ≤ 4017 / 1000000 := by nlinarith
  -- lower bound on the square root
  have hS : (232 / 10000 : ℝ) ≤
      Real.sqrt ((1 / 108) * (1 / (2 : ℝ) ^ 4) - 64 * a ^ 2) := by
    have hrw : (232 / 10000 : ℝ) = Real.sqrt ((232 / 10000 : ℝ) ^ 2) :=
      (Real.sqrt_sq (by norm_num)).symm
    rw [hrw]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hdiff : (19183 / 1000000 : ℝ) ≤
      Real.sqrt ((1 / 108) * (1 / (2 : ℝ) ^ 4) - 64 * a ^ 2) - 4 * Real.sqrt 2 * a := by
    linarith
  nlinarith [hdiff]

/-- **`deltaJ_regularU_coercive_on_kerQU`, INSTANTIATED OFF `U = 1`.** On any compatible torus
(`4 ≤ L μ`, `2 ∣ L μ + 1`), at the explicit background `tinyU b₀` — which has
`frobSupBond (tinyU b₀) > 0`, i.e. is genuinely NOT `trivialU` — and at the explicit nonzero
admissible field `genWitness (tinyU b₀)`:

  `(1/4000)·bondEnergy(genWitness) ≤ deltaJ(tinyU b₀)(genWitness)`,   `bondEnergy(genWitness) > 0`.

The left-hand side is strictly positive, so this is a genuine, non-degenerate instance of the
regular-`U` coercivity at a non-trivial background. -/
theorem deltaJ_coercive_at_genWitness_tinyU
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) (b₀ : Bond L) :
    0 < frobSupBond (tinyU b₀) ∧ 0 < bondEnergy (genWitness (tinyU b₀)) ∧
      (1 / 4000 : ℝ) * bondEnergy (genWitness (tinyU b₀))
        ≤ dstarDQuadForm (tinyU b₀) (genWitness (tinyU b₀)) := by
  refine ⟨frobSupBond_tinyU_pos b₀, bondEnergy_genWitness_pos hdvd (tinyU b₀), ?_⟩
  have key := deltaJ_regularU_coercive_on_kerQU hL hdvd (tinyU b₀) (genWitness (tinyU b₀))
    (genWitness_axial hdvd (tinyU b₀)) (genWitness_mem_kerQ hdvd (tinyU b₀))
    (hthr_tinyU b₀) (hsmall_tinyU b₀)
  have hE : (0 : ℝ) ≤ bondEnergy (genWitness (tinyU b₀)) :=
    le_of_lt (bondEnergy_genWitness_pos hdvd (tinyU b₀))
  have hγ := gamma_tinyU_ge b₀
  nlinarith [key, hγ, hE]

#print axioms siteZero_coarse
#print axioms genWitness_at_freeBond
#print axioms genWitness_ne_zero
#print axioms genWitness_axial
#print axioms genWitness_mem_kerQ
#print axioms regularU_domain_nonvacuous_generalU
#print axioms exists_nonzero_admissible_generalU
#print axioms bondEnergy_genWitness_pos
#print axioms tinyM_mem
#print axioms tinyMElem_ne_one
#print axioms frobSq_tinyM_sub_one
#print axioms tinyU_ne_trivialU
#print axioms frobSupBond_tinyU_le
#print axioms frobSupBond_tinyU_pos
#print axioms frobSupBond_tinyU_sq_le
#print axioms hthr_tinyU
#print axioms hsmall_tinyU
#print axioms gamma_tinyU_ge
#print axioms deltaJ_coercive_at_genWitness_tinyU

end AdalyFormal.Balaban.RegularUDomainWitnessGeneralU
