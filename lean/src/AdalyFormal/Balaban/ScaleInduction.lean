/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CoarseCurlScaleTwo

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `ScaleInduction.lean` — is the `[STOKES-COMM-U]` near-circularity breakable by INDUCTION ON SCALE?

The question, restated exactly as dispatched. `[STOKES-COMM-U]`'s denominator needs a REVERSE
Poincaré on the fibre of the `Δ_k` minimizer. That is itself a coercivity statement, so the
general-`U` transfer looks circular. **Is the needed coercivity at the SAME scale as the concluded
one (genuinely circular), or at a DIFFERENT one (an induction)?**

## The answer, and where each half of it is compiled

Write `(f, c)` for `(fibre level, constraint level)`, `c = f·m`, `m ≥ 2`. Three facts already in the
tree fix the dependency completely, and none of them was assembled into a level index before:

* `CovariantHjFaithful.gaugeConstraintSubspaceCovFaithful_ell1_eq_bot` — at `f = 1` the fibre is
  `⊥`;
* `RegularUGamma0.lineCoarseRestrictCov_one_eq_self` — `Q_1(U) = id` for EVERY `U`;
* `CovariantHjFaithful.deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm` — at `f = 1`, `Δ_k` IS the
  raw covariant curl form.

Consequently the coercivity statement at fibre level `1` and constraint level `c` is, VERBATIM,
`bondEnergy B ≤ K·‖D_U B‖²` on `axial(c) ∩ ker Q_c(U)` — i.e. the reverse Poincaré at level `c`.
That is `ReversePoincareAtLevel c` (§1), and `§2` proves the identification in the kernel
(`coercAtLevels_one_of_reversePoincareAtLevel`, `reversePoincareAtLevel_of_coercAtLevels_one`).

So the dependency is

  `Coerc(f, f·m)` consumes the reverse Poincaré at level `f`, which is `Coerc(1, f)`;
  `Coerc(1, ·)` consumes the reverse Poincaré on a `⊥` fibre, i.e. **nothing**.

`1 < f`, so the consumed index is not the concluded index: the implication is **not** `P k → P k`.
And the descent from any `f` reaches the `f = 1` member in ONE step and stops there, so **no product
over scales is formed and no summability condition arises for this dependency.**

**SCOPE OF WHAT IS COMPILED VERSUS WHAT IS ARGUED, stated before the claims, not after.** The
family identification `CoercAtLevels 1 c ↔ ReversePoincareAtLevel c` is COMPILED (§2, both
directions). The reading of the dependency at general fibre level `f`, i.e. that
`Coerc(f, f·m)` consumes `Coerc(1, f)`, is **NOT formalized in this file for `f ≠ 1`**: no theorem
here relates `CoercAtLevels f (f*m)` to `CoercAtLevels 1 f`. It is a reading of the definitions
(the `Δ_k` minimizer's fibre is at level `f`; the domain clause is at level `f·m`) and it is exactly
what §6 then shows CANNOT be closed in the `∀ levels` form. Treat the general-`f` sentence as
navigation, not as a result.

§4 compiles the two
terminal facts (`coercAtLevels_one_one`, `reversePoincareAtLevel_one`) and §3 compiles the
separation: the field satisfying the level-`c` constraints has a NONZERO level-`f` average, at every
`f ≥ 2` (`levels_separated_at_general_fibre`, from another lane's `scField`), and at `(f,c) = (1,2)`
(`levels_separated_at_fibre_one`, from `chiField`). So the two indices carry genuinely different,
genuinely non-trivial data — the reduction is not an identity dressed up as an implication.

## The degradation, which IS real, and is a second and independent obstruction

The dispatch's item 3 asks what the step does to the constant. For the dependency above: nothing,
because there is no iteration. But the FAMILY `ReversePoincareAtLevel c` cannot have a
level-uniform constant, and the tree already knew the qualitative half of this
(`CoarseCurlPoincare.not_gamma0TrivialUTarget`, `not_gamma0UniformTarget`, `not_kerQDivFreePoincare`
— all three pre-existing, none of them this lane's). What is added here is the QUANTITATIVE rate and
its consequence for a tower:

* `revPBody_constant_forces_quadratic_growth` — any `K` serving level `c = 8q+8` obeys
  `(q+1)² ≤ 8K`, i.e. `K ≥ c²/512`. Proved through another lane's sawtooth
  (`CoarseCurlScaleTwo.saw_forces_bound`), reused, not rebuilt (LAW-19).
* `not_reversePoincareTowerUniform_eight_two` — **no constant serves the tower
  `ell_k = 8·2^k`**, so an induction that let the level GROW with `k` gives
  `γ₀(k) ≤ 512/ell_k² → 0` geometrically. That form of the induction is DEAD, proved, not argued.

**The form that survives is FIXED LEVEL**, uniform in the torus and in `U` — which is exactly what
Bałaban's per-step rescaling supplies (CMP99b (3.156)/(3.157) are written with the ONE-step `Q₁`,
not with a growing tower operator). There `ReversePoincareAtLevel 2` is **PROVED for every regular
`U`** (§1, `reversePoincareAtLevel_two`, `K = 25600`, `α₀ = 1/500`, from
`RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU`).

## What remains, and it is NOT a scale question

The gap between what is proved and what the fibre needs is a GAUGE-CLAUSE gap, not a scale gap:
`ReversePoincareAtLevel c` carries the AXIAL clause, while the fibre
`{v : Q_f(U)v = 0 ∧ R(D_U^*v) = 0}` carries the `R`-clause. §6 settles WHICH clause that is, and
the answer overturns an in-tree reading: at `levels = oneLevelUniv` the `R`-clause is VACUOUS, the
fibre is exactly `ker Q_f(U)`, and the reverse Poincaré the transfer needs is therefore FALSE at the
single fixed level `2` (`not_fibreReversePoincareAtLevel_two`). §6a locates the divergence-free
reading at the OPPOSITE level list, `[]`, where `deltaKernelImageCov` is the full `range(Δ_U)`.

So the honest residual is not "a reverse Poincaré at some scale". It is: **the `Δ_k` statements must
PIN `levels`, because over the `∀ levels` they currently quantify the needed fibre inequality is
refuted.** The fixed-level divergence-free candidate is stated as
`KerQDivFreePoincareAtLevel c` and is NOT refuted by the tree's `not_kerQDivFreePoincare`
(`kerQDivFreePoincareAtLevel_of_kerQDivFreePoincare` shows the refuted form is strictly stronger).
What this file does NOT contain, stated plainly: no proof of `KerQDivFreePoincareAtLevel 2`, and no
discrete Weitzenböck identity reducing it to a gradient Poincaré — that reduction is identified in
`compute/scale_induction/PROGRESS.md` as the next reachable brick and was not built here.

Every declaration below has `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
Lane record: `compute/scale_induction/PROGRESS.md`.
-/

namespace AdalyFormal.Balaban.ScaleInduction

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU deltaKernelImageCovH)
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond)
open AdalyFormal.Balaban.RegularUGamma0
open AdalyFormal.Balaban.CoarseCurlPoincare (curl_trivialU_eq_flat)
open AdalyFormal.Balaban.CoarseCurlScaleTwo

variable {L : PeriodicLatticeExtent}

/-! ## §1 — THE LEVEL-INDEXED FAMILY, and its PROVED member at level 2

`RevPBody c K α₀` is the reverse Poincaré at constraint level `c`: on the axial gauge at level `c`
intersected with `ker Q_c(U)`, the bond energy is dominated by the covariant curl energy. The level
`c` is a PARAMETER (this is a family, not an existential over the level); `K` and `α₀` are bound
outside every piece of data (S91). -/

/-- **The body of the reverse Poincaré at constraint level `c`**, with the constant `K` and the
regularity threshold `α₀` supplied. No `Δ_k`, no `levels`, no minimizer, no orthogonal projection:
`dstarDQuadForm U A = ‖D_U A‖²` is the raw covariant curl energy. -/
def RevPBody (c : ℕ) (K α₀ : ℝ) : Prop :=
  ∀ (L : PeriodicLatticeExtent), (∀ μ : Fin 3, 4 ≤ L μ) → (∀ μ : Fin 3, c ∣ (L μ + 1)) →
    ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
      frobSupBond U ≤ α₀ →
      ∀ (A : Bond L → SuTwo),
        (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L c →
          ∀ x : PeriodicLatticeSite L, x ∈ blockOf y c → ∀ b ∈ staircasePath y x, A b = 0) →
        (∀ b : CoarseBond L c, lineCoarseRestrictCov U c A b = 0) →
        bondEnergy A ≤ K * dstarDQuadForm U A

/-- **`[REVERSE-POINCARE-AT-LEVEL c]`** — the level-`c` member of the family, with its constant
quantified outside the torus, the background and the field. -/
def ReversePoincareAtLevel (c : ℕ) : Prop :=
  ∃ K α₀ : ℝ, 0 < K ∧ 0 < α₀ ∧ RevPBody c K α₀

/-- **THE BASE CASE, PROVED, FOR EVERY REGULAR `U`: `ReversePoincareAtLevel 2` with `K = 25600`
and `α₀ = 1/500`.** This is `RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU` read as the
level-`2` member of the family: the constant is a numeral, independent of the torus, of the RG step
and of `U` over the regular class. LAW-19: the numeric threshold arithmetic is
`RegularUGamma0.regularU_constant_lower`, reused verbatim, not re-derived. -/
theorem reversePoincareAtLevel_two : ReversePoincareAtLevel 2 := by
  refine ⟨25600, 1 / 500, by norm_num, by norm_num, ?_⟩
  intro L hL hdvd U hreg A hadm hker
  have ha : 0 ≤ frobSupBond U :=
    AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg U
  have hlow := regularU_constant_lower ha hreg
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hthr : 64 * frobSupBond U ^ 2 ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by
    rw [hcast]; nlinarith [ha, hreg]
  have hsmall : 0 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
      - 4 * Real.sqrt 2 * frobSupBond U := by linarith [hlow]
  have key := AdalyFormal.Balaban.RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU
    hL hdvd U A hadm hker hthr hsmall
  have hgam : (1 : ℝ) / 25600
      ≤ (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) - 64 * frobSupBond U ^ 2)
          - 4 * Real.sqrt 2 * frobSupBond U) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 160) hlow 2
    calc (1 : ℝ) / 25600 = ((1 : ℝ) / 160) ^ 2 := by norm_num
      _ ≤ _ := h
  have hE : 0 ≤ bondEnergy A :=
    AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg A
  nlinarith [key, hgam, hE, mul_le_mul_of_nonneg_right hgam hE]

#print axioms reversePoincareAtLevel_two

/-! ## §2 — THE IDENTIFICATION: the coercivity family AT FIBRE LEVEL 1 *is* this family

This is the step that turns "near-circular" into a level index. At fibre level `1` the Schur
projection is a no-op and `Q_1(U) = id`, so the coercivity statement degenerates — not to something
weaker, but to exactly the reverse Poincaré at the CONSTRAINT level. -/

/-- **The coercivity target at fibre level `f` and constraint level `c`**, with `γ₀` and `α₀`
outside all data. `f = 1`, `c = 2` is `RegularUGamma0.Gamma0FibreOneUniform` (LAW-19: this def
generalizes it in the two level indices; the `(1,2)` content is not re-proved here, it is
composed). -/
def CoercAtLevels (f c : ℕ) : Prop :=
  ∃ γ₀ α₀ : ℝ, 0 < γ₀ ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent), (∀ μ : Fin 3, 4 ≤ L μ) → (∀ μ : Fin 3, c ∣ (L μ + 1)) →
      ∀ (levels : List (KernelSubspace.Level L))
        (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
          [(curlImageCovHFaithful f levels U).HasOrthogonalProjection]
          (B : Bond L → SuTwo),
          (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L c →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y c → ∀ b ∈ staircasePath y x, B b = 0) →
          (∀ b : CoarseBond L c, lineCoarseRestrictCov U c B b = 0) →
          γ₀ * covCoarseBondInner (lineCoarseRestrictCovLM U f B)
              (lineCoarseRestrictCovLM U f B)
            ≤ deltaJQuadFormCovFaithful f levels U B

/-- **`ReversePoincareAtLevel c ⟹ CoercAtLevels 1 c`, with `γ₀ = 1/K`.** The whole operator half
of the coercivity — Schur complement, `H_j` minimizer, gauge-constraint subspace, orthogonal
projection — disappears at fibre level `1`, because the fibre is `⊥` there. -/
theorem coercAtLevels_one_of_reversePoincareAtLevel {c : ℕ} (h : ReversePoincareAtLevel c) :
    CoercAtLevels 1 c := by
  obtain ⟨K, α₀, hK, hα₀, hbody⟩ := h
  refine ⟨1 / K, α₀, by positivity, hα₀, ?_⟩
  intro L hL hdvd levels U hreg _ _ B hadm hker
  have hb := hbody L hL hdvd U hreg B hadm hker
  rw [covCoarseBondInner_one_eq_bondEnergy, deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm]
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  calc (1 : ℝ) * bondEnergy B = bondEnergy B := one_mul _
    _ ≤ K * dstarDQuadForm U B := hb
    _ = dstarDQuadForm U B * K := mul_comm _ _

/-- **The converse: `CoercAtLevels 1 c ⟹ ReversePoincareAtLevel c`.** The `levels` list and the two
orthogonal-projection instances are supplied explicitly rather than assumed available, because
nothing in the tree constructs them; `levels := []` discharges them by synthesis in
`reversePoincareAtLevel_of_coercAtLevels_one'` below. This direction is what makes the two families
the SAME family, hence what makes the dependency a level shift rather than a restatement. -/
theorem reversePoincareAtLevel_of_coercAtLevels_one {c : ℕ}
    (mk : ∀ L : PeriodicLatticeExtent, List (KernelSubspace.Level L))
    (h1 : ∀ (L : PeriodicLatticeExtent)
      (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
      (deltaKernelImageCovH U (mk L)).HasOrthogonalProjection)
    (h2 : ∀ (L : PeriodicLatticeExtent)
      (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
      haveI := h1 L U
      (curlImageCovHFaithful 1 (mk L) U).HasOrthogonalProjection)
    (h : CoercAtLevels 1 c) : ReversePoincareAtLevel c := by
  obtain ⟨γ₀, α₀, hγ₀, hα₀, hall⟩ := h
  refine ⟨1 / γ₀, α₀, by positivity, hα₀, ?_⟩
  intro L hL hdvd U hreg A hadm hker
  haveI := h1 L U
  haveI := h2 L U
  have key := hall L hL hdvd (mk L) U hreg A hadm hker
  rw [covCoarseBondInner_one_eq_bondEnergy, deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm] at key
  rw [div_mul_eq_mul_div, le_div_iff₀ hγ₀]
  calc bondEnergy A * γ₀ = γ₀ * bondEnergy A := mul_comm _ _
    _ ≤ dstarDQuadForm U A := key
    _ = 1 * dstarDQuadForm U A := (one_mul _).symm

/-- The same converse with the `levels`/instance plumbing discharged at `levels := []`. -/
theorem reversePoincareAtLevel_of_coercAtLevels_one' {c : ℕ} (h : CoercAtLevels 1 c) :
    ReversePoincareAtLevel c :=
  reversePoincareAtLevel_of_coercAtLevels_one (fun L => ([] : List (KernelSubspace.Level L)))
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) h

/-- **The composed statement: `CoercAtLevels 1 2` HOLDS for every regular `U`.** The level-`2`
member of the family, read as a coercivity against the actual Schur complement. -/
theorem coercAtLevels_one_two : CoercAtLevels 1 2 :=
  coercAtLevels_one_of_reversePoincareAtLevel reversePoincareAtLevel_two

#print axioms coercAtLevels_one_of_reversePoincareAtLevel
#print axioms reversePoincareAtLevel_of_coercAtLevels_one
#print axioms reversePoincareAtLevel_of_coercAtLevels_one'
#print axioms coercAtLevels_one_two

/-! ## §3 — THE LEVELS ARE GENUINELY SEPARATED

If the level-`c` constraint already annihilated the level-`f` average, the "induction" would be an
identity in disguise: the object the reverse Poincaré is applied to would be `0`. It does not. Both
witnesses below are OTHER LANES' fields, imported and reused (LAW-19), not rebuilt. -/

/-- **`(f, c) = (1, 2)`: `ker Q_2(1)` strictly contains `ker Q_1(1) = {0}`.** `chiField w` satisfies
the level-`2` constraint and is nonzero, hence has nonzero level-`1` average (`Q_1 = id`). So the
level-`1` reverse Poincaré is applied to a genuinely nonzero object even after the level-`2`
constraint is imposed. -/
theorem levels_separated_at_fibre_one (h2 : (2 : ℕ) ∣ (L 0 + 1)) {w : SuTwo} (hw : w ≠ 0) :
    (∀ c : CoarseBond L 2, lineCoarseRestrictCov (trivialU L) 2 (chiField w) c = 0)
      ∧ ¬ (∀ c : CoarseBond L 1,
            lineCoarseRestrictCov (trivialU L) 1 (chiField (L := L) w) c = 0) := by
  refine ⟨chiField_mem_kerQ2 h2 w, ?_⟩
  intro hcontra
  have hzero : chiField (L := L) w = 0 := kerQ_one_forces_zero (trivialU L) _ hcontra
  have hpos := bondEnergy_chiField_pos (L := L) hw
  rw [hzero] at hpos
  have : bondEnergy (0 : Bond L → SuTwo) = 0 := by
    unfold AdalyFormal.Balaban.RegularUPerturbation.bondEnergy
    simp
  rw [this] at hpos
  exact lt_irrefl 0 hpos

/-- **Every fibre level `f = e ≥ 2`: the level-`n` data does NOT annihilate the level-`e` average.**
`scField e n w` (another lane's witness) is in the axial gauge at level `n` and in `ker Q_n(1)`, yet
`‖Q_e(1)·‖² > 0`. So at every `(f, c) = (e, n)` with `2 ≤ e`, `e ∣ n`, `2e ≤ n` the two indices
carry
different non-trivial data, and the reduction `Coerc(f, f·m) ⟸ Coerc(1, f)` is not an identity. -/
theorem levels_separated_at_general_fibre {e n : ℕ} (he : 2 ≤ e) (h2e : 2 * e ≤ n) (hedvd : e ∣ n)
    (hdvdn : ∀ μ : Fin 3, n ∣ (L μ + 1)) {w : SuTwo} (hw : w ≠ 0) :
    (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L n →
        ∀ x : PeriodicLatticeSite L, ∀ b ∈ staircasePath y x, scField e n w b = 0)
      ∧ (∀ c : CoarseBond L n, lineCoarseRestrictCov (trivialU L) n (scField e n w) c = 0)
      ∧ 0 < covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) e (scField e n w))
            (lineCoarseRestrictCovLM (trivialU L) e (scField e n w)) :=
  ⟨fun y hy x b hb => scField_axial w hedvd y hy x b hb,
   fun c => scField_kerQ w (hdvdn 2) c,
   scField_Q_norm_pos he h2e hdvdn hw⟩

#print axioms levels_separated_at_fibre_one
#print axioms levels_separated_at_general_fibre

/-! ## §4 — WHERE THE DESCENT STOPS, and the degenerate points of my own statements

Each item is a MADE-IT-FAIL / made-it-evaporate control, compiled, not argued. -/

/-- **`ReversePoincareAtLevel 1` is TRUE and CONTENT-FREE** — `Q_1(U) = id`, so the level-`1`
constraint forces `A = 0` (`RegularUGamma0.kerQ_one_forces_zero`, every `U`). This is the terminus
of the descent: the level-`1` member needs no input at all, which is why the recursion has depth `1`
and forms no product over scales. It is ALSO the reason `c = 1` may never be cited as evidence. -/
theorem reversePoincareAtLevel_one : ReversePoincareAtLevel 1 := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro L _ _ U _ A _ hker
  have hz : A = 0 := kerQ_one_forces_zero U A hker
  subst hz
  have hb : bondEnergy (0 : Bond L → SuTwo) = 0 := by
    unfold AdalyFormal.Balaban.RegularUPerturbation.bondEnergy; simp
  rw [hb, one_mul]
  exact dstarDQuadForm_nonneg U 0

/-- **`CoercAtLevels 1 1` is TRUE and CONTENT-FREE** — same mechanism, at the coercivity end. -/
theorem coercAtLevels_one_one : CoercAtLevels 1 1 :=
  coercAtLevels_one_of_reversePoincareAtLevel reversePoincareAtLevel_one

/-- **`ReversePoincareAtLevel 0` is VACUOUSLY TRUE, and for a DIFFERENT reason than level `1`** —
the divisibility clause `∀ μ, 0 ∣ (L μ + 1)` is unsatisfiable (`L μ + 1 ≥ 1`), so there is no
lattice to test. Level `0` and level `1` are both content-free and they evaporate in opposite ways;
neither is evidence for anything (`GOAL_LEMMA.md` §7 item 5). -/
theorem reversePoincareAtLevel_zero : ReversePoincareAtLevel 0 := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro L _ hdvd
  exact absurd (Nat.eq_zero_of_zero_dvd (hdvd 0)) (Nat.succ_ne_zero (L 0))

#print axioms reversePoincareAtLevel_one
#print axioms coercAtLevels_one_one
#print axioms reversePoincareAtLevel_zero

/-! ## §5 — THE DEGRADATION: the family's constant must grow like the SQUARE of the level, and no
constant serves a growing tower

This is the dispatch's item 3, and the answer separates cleanly into two statements. The dependency
of §2/§4 forms no product over scales, so it degrades not at all. But the FAMILY is not
level-uniform, and here is the rate. The witness is another lane's sawtooth
(`CoarseCurlScaleTwo.SAW`, `saw_forces_bound`) — imported and reused, not rebuilt (LAW-19). -/

/-- The raw covariant curl energy at `U = 1` IS the flat plaquette energy. (Three-line composition
of `curl_trivialU_eq_flat` and `covPlaqInner_self_eq_plaqEnergy`; the same composition appears
inline in `CoarseCurlPoincare`, named here because §5 uses it three times.) -/
theorem dstarDQuadForm_trivialU_eq_plaqEnergy (A : Bond L → SuTwo) :
    dstarDQuadForm (trivialU L) A = plaqEnergy (flatCurlValue A) := by
  change covPlaqInner (curlCovariantLM (trivialU L) A) (curlCovariantLM (trivialU L) A) = _
  rw [curl_trivialU_eq_flat, covPlaqInner_self_eq_plaqEnergy]

/-- **THE QUADRATIC DEGRADATION, PROVED.** Any `K` for which the reverse Poincaré holds at
constraint level `c = 8q+8` satisfies `(q+1)² ≤ 8K`, i.e. `K ≥ c²/512`. So the level-`c` member of
the family cannot have a constant better than quadratic in `c`. -/
theorem revPBody_constant_forces_quadratic_growth (q : ℕ) {K α₀ : ℝ} (hK : 0 < K) (hα₀ : 0 < α₀)
    (h : RevPBody (8 * q + 8) K α₀) : ((q : ℝ) + 1) ^ 2 ≤ 8 * K := by
  have hw : (suTwoWitness : SuTwo) ≠ 0 := suTwoWitness_ne_zero
  have hL4 : ∀ μ : Fin 3, 4 ≤ sawExt q μ := by
    intro μ; change 4 ≤ 8 * q + 7; omega
  have hdvd : ∀ μ : Fin 3, (8 * q + 8) ∣ (sawExt q μ + 1) := by
    intro μ
    rw [show sawExt q μ + 1 = 8 * q + 8 from by unfold sawExt; omega]
  have hreg : frobSupBond (trivialU (sawExt q)) ≤ α₀ := by
    rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU]; exact le_of_lt hα₀
  have hkey := h (sawExt q) hL4 hdvd (trivialU (sawExt q)) hreg (SAW q suTwoWitness)
    (fun y hy x _ b hb => SAW_axial q suTwoWitness hy x b hb)
    (fun c => SAW_kerQ q suTwoWitness c)
  rw [dstarDQuadForm_trivialU_eq_plaqEnergy] at hkey
  -- `bondEnergy ≤ K · plaqEnergy` becomes `(1/K)·bondEnergy ≤ plaqEnergy`
  have hstep : (1 / K) * bondEnergy (SAW q suTwoWitness)
      ≤ plaqEnergy (flatCurlValue (SAW q suTwoWitness)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    calc (1 : ℝ) * bondEnergy (SAW q suTwoWitness) = bondEnergy (SAW q suTwoWitness) := one_mul _
      _ ≤ K * plaqEnergy (flatCurlValue (SAW q suTwoWitness)) := hkey
      _ = plaqEnergy (flatCurlValue (SAW q suTwoWitness)) * K := mul_comm _ _
  have hb := saw_forces_bound q (by positivity : (0:ℝ) < 1 / K) hw hstep
  -- clear the `1/K`: `(q+1)³ ≤ (8q+8)·K`, then divide by `(q+1) > 0`
  rw [div_mul_eq_mul_div, div_le_iff₀ hK, one_mul] at hb
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  refine le_of_mul_le_mul_right ?_ hq1
  nlinarith [hb]

/-- **`[REVERSE-POINCARE-LEVEL-UNIFORM]` — one constant for EVERY level `c ≥ 2`.** -/
def ReversePoincareLevelUniform : Prop :=
  ∃ K α₀ : ℝ, 0 < K ∧ 0 < α₀ ∧ ∀ c : ℕ, 2 ≤ c → RevPBody c K α₀

/-- **`ReversePoincareLevelUniform` IS FALSE.** Immediate from the quadratic degradation. -/
theorem not_reversePoincareLevelUniform : ¬ ReversePoincareLevelUniform := by
  rintro ⟨K, α₀, hK, hα₀, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * K)
  have hb := revPBody_constant_forces_quadratic_growth n hK hα₀ (hall (8 * n + 8) (by omega))
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith [hb, hn, hn0, sq_nonneg ((n : ℝ))]

/-- `n ≤ 2ⁿ`, by induction — used to make the tower's level unbounded in `k`. LAW-19 note: Mathlib's
`Nat.lt_two_pow_self` gives this in one step; the induction is here only because the name/binder
shape of that lemma moves between Mathlib versions, and this file must build against the pinned one.
Disclosed rather than left as a silent machinery rebuild. -/
theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

/-- **`[REVERSE-POINCARE-TOWER-UNIFORM]` — one constant for the whole RG tower `ell₀·m^k`.** This is
what an induction on scale with a GROWING level would have to deliver: the constant must not
degrade as `k` advances. -/
def ReversePoincareTowerUniform (ell₀ m : ℕ) : Prop :=
  ∃ K α₀ : ℝ, 0 < K ∧ 0 < α₀ ∧ ∀ k : ℕ, RevPBody (ell₀ * m ^ k) K α₀

/-- **THE PROVED NO-GO FOR THE GROWING-TOWER INDUCTION.** No constant serves the tower
`ell_k = 8·2^k`: the level-`ell_k` constant is forced to be `≥ 4^k/8`, so `γ₀(k) = 1/K(ell_k) → 0`
geometrically. An induction on scale that lets the level grow with the RG step therefore cannot
produce the `k`-uniform `γ₀` the goal lemma demands — this is a theorem, not an expectation.

What it does NOT say: it says nothing against the FIXED-level statement. Bałaban's (3.156)/(3.157)
are written with the one-step `Q₁` after rescaling, so his `k`-uniformity is uniformity in the
torus and in `U_k` at a FIXED block factor, and `reversePoincareAtLevel_two` is exactly that
statement at block factor `2`. -/
theorem not_reversePoincareTowerUniform_eight_two : ¬ ReversePoincareTowerUniform 8 2 := by
  rintro ⟨K, α₀, hK, hα₀, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * K)
  -- at step `k = n` the level is `8·2^n = 8·(2^n − 1) + 8`
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hlev : 8 * 2 ^ n = 8 * (2 ^ n - 1) + 8 := by omega
  have hb := revPBody_constant_forces_quadratic_growth (2 ^ n - 1) hK hα₀
    (by rw [← hlev]; exact hall n)
  have hcast : ((2 ^ n - 1 : ℕ) : ℝ) + 1 = ((2 ^ n : ℕ) : ℝ) := by
    have h1 : ((2 ^ n - 1 : ℕ) + 1 : ℕ) = 2 ^ n := by omega
    calc ((2 ^ n - 1 : ℕ) : ℝ) + 1 = (((2 ^ n - 1 : ℕ) + 1 : ℕ) : ℝ) := by push_cast; ring
      _ = ((2 ^ n : ℕ) : ℝ) := by rw [h1]
  rw [hcast] at hb
  -- `(2^n)² ≤ 8K` but `n ≤ 2^n ≤ (2^n)²` and `8K < n`
  have hle : (n : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast nat_le_two_pow n
  have hsq : ((2 ^ n : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hpow
    nlinarith [h1]
  linarith [hb, hn, hle, hsq]

#print axioms dstarDQuadForm_trivialU_eq_plaqEnergy
#print axioms revPBody_constant_forces_quadratic_growth
#print axioms nat_le_two_pow
#print axioms not_reversePoincareLevelUniform
#print axioms not_reversePoincareTowerUniform_eight_two

/-! ## §6 — THE CONSEQUENCE NOBODY DREW: the fibre reverse Poincaré `[STOKES-COMM-U]` needs is
FALSE at level 2

**Attribution first, because this lane rebuilt four lemmas before checking (LAW-19 failure, caught
by this lane's own nested validator and recorded rather than hidden).** The vacuity of the fibre's
gauge clause at `oneLevelUniv` is ALREADY PROVED IN THE TREE, under these exact names, in
`CovariantHjMinimizer.lean` §16b:

  `kernelSubspaceCov_oneLevelUniv_eq_bot`      (:1845)
  `deltaKernelImageCov_oneLevelUniv_eq_bot`    (:1866)
  `deltaKernelImageCovH_oneLevelUniv_eq_bot`   (:1872)
  `RcovFun_oneLevelUniv_eq_zero` / `RcovLM_oneLevelUniv_eq_zero`   (:1893, :1899)
  `gaugeConstraintSubspaceCov_oneLevelUniv_eq_ker`  (:1912) — the fibre IS `ker Q_ell`, every `ell`,
    every `U`, for the NON-faithful subspace

and `SchurNonzero.lean` §6 records it in prose. The four re-derivations are DELETED; what is kept is
the faithful analogue (`mem_fibre_oneLevelUniv_iff`, three lines off `RcovLM_oneLevelUniv_eq_zero`)
and the consequence below.

**The consequence is what is new.** Nobody asked what `R ≡ 0` does to the reverse Poincaré the
general-`U` transfer needs. It kills it: `RegularUGamma0.no_reverse_poincare_on_kerQ`
(`chiField w` —
nonzero, curl-free, in `ker Q_2(1)`) refutes `FibreReversePoincareAtLevel 2` outright
(`not_fibreReversePoincareAtLevel_two`). So the object `[STOKES-COMM-U]`'s denominator needs is
FALSE
in the `∀ levels` form the tree's `Δ_k` statements quantify over, at the single FIXED level `2` —
this is not §5's level-uniformity failing. Any route through it must PIN `levels` to a list whose
`R`-clause has content, and `oneLevelUniv` is provably not such a list. Establishing a convention is
not the same as drawing its consequence.

**FINDING (LAW-4 — `RegularUGamma0.lean` is another lane's write scope; NOT repaired here).**
`RegularUGamma0.lean:1105-1108` prints, verbatim:

  "`gaugeConstraintSubspaceCovFaithful`'s second clause is `R(∂*_U A) = 0` with
   `R = P_{Δ_U(kernelSubspaceCov levels)}`. At `levels = oneLevelUniv` this is a genuine
   divergence-type condition, so the fibre is `ker Q_ell(U) ∩ {gauge}` and the primitive the
   general-`U` transfer actually needs is a Poincaré on THAT intersection."

That is contradicted by `CovariantHjMinimizer` §16b, which PROVES `R ≡ 0` at `oneLevelUniv`: there
the clause is not a divergence-type condition, it is no condition at all. An earlier draft of this
docstring, and of `compute/scale_induction/PROGRESS.md` Step 5, put a PARAPHRASE of that sentence
inside quotation marks — a verbatim-tag violation, corrected here; the text above is the actual
print. Nothing COMPILED in `RegularUGamma0.lean` depends on the sentence: its `oneLevelUniv` uses
are
in `third_level_energy_bound_via_summed`, which runs through the Schur/curl-energy route, and §11a's
compiled content is `gradAdjoint_chiField_ne_zero`, about `chiField`'s divergence, unaffected either
way. -/

/-- **THE FIBRE AT `oneLevelUniv` IS EXACTLY `ker Q_f(U)`, faithful version** — the faithful
analogue
of the tree's `CovariantHjMinimizer.gaugeConstraintSubspaceCov_oneLevelUniv_eq_ker`, discharging its
gauge clause by the SAME lemma (`RcovLM_oneLevelUniv_eq_zero`; LAW-19: reused, not re-derived).
Stated as a membership `iff` because the faithful subspace's first clause is
`lineCoarseRestrictCovLM`, for which the tree carries no `LinearMap.ker` packaging. -/
theorem mem_fibre_oneLevelUniv_iff {f : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U
      (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv L)).HasOrthogonalProjection]
    (A' : Bond L → SuTwo) :
    A' ∈ gaugeConstraintSubspaceCovFaithful f
        (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv L) U
      ↔ lineCoarseRestrictCovLM U f A' = 0 := by
  rw [mem_gaugeConstraintSubspaceCovFaithful]
  exact ⟨fun h => h.1, fun h =>
    ⟨h, AdalyFormal.Balaban.CovariantHjMinimizer.RcovLM_oneLevelUniv_eq_zero U _⟩⟩

def FibreReversePoincareAtLevel (f : ℕ) : Prop :=
  ∃ K α₀ : ℝ, 0 < K ∧ 0 < α₀ ∧
    ∀ (L : PeriodicLatticeExtent), (∀ μ : Fin 3, 4 ≤ L μ) → (∀ μ : Fin 3, f ∣ (L μ + 1)) →
      ∀ (levels : List (KernelSubspace.Level L))
        (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L),
        frobSupBond U ≤ α₀ →
        ∀ [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
          (v : Bond L → SuTwo),
          v ∈ gaugeConstraintSubspaceCovFaithful f levels U →
          bondEnergy v ≤ K * dstarDQuadForm U v

/-- **`FibreReversePoincareAtLevel 2` IS FALSE.** At `levels = oneLevelUniv` the fibre is
`ker Q_2(U)`, and `chiField w` is a nonzero, curl-free member of `ker Q_2(1)`. So the reverse
Poincaré the general-`U` transfer needs on the fibre does not hold in the `∀ levels` form, at ANY
constant. This is not the level-uniformity failing (§5): it fails at the single fixed level `2`. -/
theorem not_fibreReversePoincareAtLevel_two : ¬ FibreReversePoincareAtLevel 2 := by
  rintro ⟨K, α₀, hK, hα₀, hall⟩
  set L : PeriodicLatticeExtent := sawExt 0 with hLdef
  have hL4 : ∀ μ : Fin 3, 4 ≤ L μ := by intro μ; rw [hLdef]; change 4 ≤ 8 * 0 + 7; omega
  have hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1) := by
    intro μ; rw [hLdef]; change (2 : ℕ) ∣ (8 * 0 + 7 + 1); norm_num
  haveI : (deltaKernelImageCovH (trivialU L)
      (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv L)).HasOrthogonalProjection := by
    rw [AdalyFormal.Balaban.CovariantHjMinimizer.deltaKernelImageCovH_oneLevelUniv_eq_bot]
    infer_instance
  have hw : (suTwoWitness : SuTwo) ≠ 0 := suTwoWitness_ne_zero
  have hmem : chiField (L := L) suTwoWitness ∈ gaugeConstraintSubspaceCovFaithful 2
      (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv L) (trivialU L) := by
    rw [mem_fibre_oneLevelUniv_iff]
    funext c
    rw [lineCoarseRestrictCovLM_apply]
    exact chiField_mem_kerQ2 (hdvd 0) suTwoWitness c
  have hkey := hall L hL4 hdvd (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv L)
    (trivialU L)
    (by rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU]; exact le_of_lt hα₀)
    (chiField (L := L) suTwoWitness) hmem
  rw [dstarDQuadForm_trivialU_eq_plaqEnergy, flatCurl_chiField] at hkey
  have hzero : plaqEnergy (0 : PeriodicLatticePlaquette L → SuTwo) = 0 := by
    unfold AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy; simp
  rw [hzero, mul_zero] at hkey
  exact absurd hkey (not_le.mpr (bondEnergy_chiField_pos (L := L) hw))

/-! ### §6a — and the level list that DOES carry the divergence clause is the EMPTY one

The two lists sit at opposite ends. `oneLevelUniv` pins every site, so its kernel subspace is `⊥`
and its `R`-clause is VACUOUS; `[]` pins nothing, so its kernel subspace is `⊤`, its
`deltaKernelImageCov` is the FULL `range(Δ_U)`, and its `R`-clause is the STRONGEST available. So
the
divergence-free reading `RegularUGamma0` §11a attached to `oneLevelUniv` belongs to `[]` instead.
`SchurNonzero.lean` §6 already establishes the `[]` end at its witness lattice
(`kernelSubspaceCov_nil_eq_top`, `Rcov_clause_nonvacuous_nil`, with a NAMED field `gradLamDelta`
that genuinely violates the clause); the two theorems below are the same two facts stated for an
ARBITRARY extent (LAW-19: generalization, with the witness-lattice originals cited, not re-derived).
NOT PROVED ANYWHERE HERE, and stated as background rather than as a result: that `R(D^*A) = 0` at
`levels = []` is EQUIVALENT to `div A = 0` at `U = 1`. That would need `range(Δ)` to be exactly the
zero-sum subspace, which no declaration in this file establishes. -/

/-- `kernelSubspaceCov [] = ⊤` — no level pins anything. -/
theorem kernelSubspaceCov_nil_eq_top (L : PeriodicLatticeExtent) :
    AdalyFormal.Balaban.CovariantHjMinimizer.kernelSubspaceCov
        ([] : List (KernelSubspace.Level L)) = ⊤ := by
  ext lam
  simp only [Submodule.mem_top, iff_true,
    AdalyFormal.Balaban.CovariantHjMinimizer.mem_kernelSubspaceCov]
  simp

/-- …hence at `levels = []` the subspace `R^{cov}(U)` projects onto is the FULL range of the
covariant site Laplacian — the opposite end from `oneLevelUniv`'s `⊥`. -/
theorem deltaKernelImageCov_nil_eq_range
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    AdalyFormal.Balaban.CovariantHjMinimizer.deltaKernelImageCov U
        ([] : List (KernelSubspace.Level L))
      = LinearMap.range (AdalyFormal.Balaban.CovariantHjMinimizer.siteLaplacianCovLM U) := by
  unfold AdalyFormal.Balaban.CovariantHjMinimizer.deltaKernelImageCov
  rw [kernelSubspaceCov_nil_eq_top, Submodule.map_top]

/-- **`[KERQ-DIVFREE-POINCARE-AT-LEVEL c]`** — the FIXED-LEVEL divergence-free reverse Poincaré at
`U = 1`. `CoarseCurlPoincare.not_kerQDivFreePoincare` refutes the version quantified over ALL
levels; `kerQDivFreePoincareAtLevel_of_kerQDivFreePoincare` shows the refuted statement is STRICTLY
stronger than any fixed-level member, so that refutation reaches no fixed `c`. Its witness `W3`
lives
at level `2p+1` with `p ≥ 2` and forces only `2p ≤ 6K`, a finite constraint once `p` is fixed. -/
def KerQDivFreePoincareAtLevel (c : ℕ) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ (L : PeriodicLatticeExtent), (∀ μ : Fin 3, c ∣ (L μ + 1)) →
      ∀ (A : Bond L → SuTwo),
        (∀ b : CoarseBond L c, lineCoarseRestrictCov (trivialU L) c A b = 0) →
        (∀ y : PeriodicLatticeSite L,
          AdalyFormal.Balaban.CovariantHjMinimizer.gradCovariantAdjointValue (trivialU L) A y = 0) →
        bondEnergy A ≤ K * plaqEnergy (curlCovariantLM (trivialU L) A)

/-- The level-uniform div-free primitive implies every fixed level. So its refutation in the tree
does NOT refute any `KerQDivFreePoincareAtLevel c`, and in particular does not refute `c = 2`. -/
theorem kerQDivFreePoincareAtLevel_of_kerQDivFreePoincare {c : ℕ} (hc : 0 < c)
    (h : KerQDivFreePoincare) : KerQDivFreePoincareAtLevel c := by
  obtain ⟨K, hK, hall⟩ := h
  exact ⟨K, hK, fun L hdvd A hker hdiv => hall L c hc hdvd A hker hdiv⟩

/-! ### §6b — THE REST OF THE DEGENERATE-POINT INVENTORY

§4 disclosed levels `0` and `1` for `ReversePoincareAtLevel`. This lane's nested validator found
FOUR
MORE points at which a statement in this file evaporates, none of them disclosed in the first draft.
Each is compiled here, so that none of them can ever be cited as evidence. Recorded as found, with
the mechanism, not paraphrased away. -/

/-- **`CoercAtLevels c c` is trivially true for EVERY `c`, not only `c = 1`.** When the fibre level
equals the constraint level the hypothesis `Q_c(U)B = 0` makes the statement's own LEFT-HAND SIDE
zero, so it reads `γ₀·0 ≤ Δ_k` for any `γ₀`. This is a strictly MORE GENERAL degeneracy than
`coercAtLevels_one_one`'s (which runs through `Q_1 = id ⟹ B = 0`), and it is why the content of the
family lives strictly at `f < c`. Cf. `RegularUGamma0.lhs_vanishes_when_constraint_equals_fibre`,
which proves the same collapse for the left-hand side alone (LAW-19: same fact, packaged here at the
level of the `def` so the `def` itself carries the disclosure). -/
theorem coercAtLevels_diag (c : ℕ) : CoercAtLevels c c := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro L hL hdvd levels U hreg _ _ B hadm hker
  have hz : lineCoarseRestrictCovLM U c B = 0 := by
    funext b
    rw [lineCoarseRestrictCovLM_apply]
    exact hker b
  rw [hz]
  have hzero : covCoarseBondInner (0 : CoarseBond L c → SuTwo) 0 = 0 := by
    unfold covCoarseBondInner
    simp only [Pi.zero_apply, CovariantHj.hsInner_zero_zero, Finset.sum_const_zero]
  rw [hzero, mul_zero]
  exact deltaJQuadFormCovFaithful_nonneg c levels U B

/-- **`FibreReversePoincareAtLevel 1` is VACUOUSLY TRUE** — the fibre is `⊥` at `f = 1`
(`gaugeConstraintSubspaceCovFaithful_ell1_eq_bot`, for EVERY `levels` and `U`), which is one of the
three facts this file's own opening docstring rests on. So `f = 1` is not a base case for the FIBRE
family either, and only `f ≥ 2` carries content — which is exactly where
`not_fibreReversePoincareAtLevel_two` fires. -/
theorem fibreReversePoincareAtLevel_one : FibreReversePoincareAtLevel 1 := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro L _ _ levels U _ _ v hv
  rw [gaugeConstraintSubspaceCovFaithful_ell1_eq_bot, Submodule.mem_bot] at hv
  subst hv
  have hb : bondEnergy (0 : Bond L → SuTwo) = 0 := by
    unfold AdalyFormal.Balaban.RegularUPerturbation.bondEnergy; simp
  rw [hb, one_mul]
  exact dstarDQuadForm_nonneg U 0

/-- **`KerQDivFreePoincareAtLevel 0` is VACUOUS** (unsatisfiable divisibility) and
**`KerQDivFreePoincareAtLevel 1` is CONTENT-FREE** (`kerQ_one_forces_zero` collapses the domain to
`{0}`). Neither may be cited as evidence for the fixed-level div-free primitive; the open case is
`c ≥ 2`. -/
theorem kerQDivFreePoincareAtLevel_zero : KerQDivFreePoincareAtLevel 0 := by
  refine ⟨1, by norm_num, ?_⟩
  intro L hdvd
  exact absurd (Nat.eq_zero_of_zero_dvd (hdvd 0)) (Nat.succ_ne_zero (L 0))

theorem kerQDivFreePoincareAtLevel_one : KerQDivFreePoincareAtLevel 1 := by
  refine ⟨1, by norm_num, ?_⟩
  intro L _ A hker _
  have hz : A = 0 := kerQ_one_forces_zero (trivialU L) A hker
  subst hz
  have hb : bondEnergy (0 : Bond L → SuTwo) = 0 := by
    unfold AdalyFormal.Balaban.RegularUPerturbation.bondEnergy; simp
  rw [hb, one_mul]
  exact AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy_nonneg _

/-- **`ReversePoincareTowerUniform ell₀ 1` HOLDS at `ell₀ = 2`, so `m = 1` is a degenerate tower** —
`2·1^k = 2` for every `k`, i.e. the "tower" never leaves level `2` and the statement is just
`reversePoincareAtLevel_two`. `2 ≤ m` is therefore load-bearing in
`not_reversePoincareTowerUniform_eight_two`'s reading, and `m = 1` may never be cited as a
tower-uniform result. -/
theorem reversePoincareTowerUniform_two_one : ReversePoincareTowerUniform 2 1 := by
  obtain ⟨K, α₀, hK, hα₀, hbody⟩ := reversePoincareAtLevel_two
  refine ⟨K, α₀, hK, hα₀, fun k => ?_⟩
  simpa using hbody

/-- **`ReversePoincareTowerUniform ell₀ 0` HOLDS at `ell₀ = 2` too, by a DIFFERENT degeneracy** —
`k = 0` gives level `2` (proved), and every `k ≥ 1` gives level `0`, which is vacuous. So `m = 0` is
degenerate as well, and for a reason unrelated to `m = 1`'s. -/
theorem reversePoincareTowerUniform_two_zero : ReversePoincareTowerUniform 2 0 := by
  obtain ⟨K, α₀, hK, hα₀, hbody⟩ := reversePoincareAtLevel_two
  refine ⟨K, α₀, hK, hα₀, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simpa using hbody
  · have h0 : (2 : ℕ) * 0 ^ k = 0 := by
      rw [zero_pow (by omega : k ≠ 0), mul_zero]
    rw [h0]
    intro L _ hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd (hdvd 0)) (Nat.succ_ne_zero (L 0))

#print axioms coercAtLevels_diag
#print axioms fibreReversePoincareAtLevel_one
#print axioms kerQDivFreePoincareAtLevel_zero
#print axioms kerQDivFreePoincareAtLevel_one
#print axioms reversePoincareTowerUniform_two_one
#print axioms reversePoincareTowerUniform_two_zero

#print axioms kernelSubspaceCov_nil_eq_top
#print axioms deltaKernelImageCov_nil_eq_range
#print axioms kerQDivFreePoincareAtLevel_of_kerQDivFreePoincare
#print axioms mem_fibre_oneLevelUniv_iff
#print axioms not_fibreReversePoincareAtLevel_two

end AdalyFormal.Balaban.ScaleInduction
