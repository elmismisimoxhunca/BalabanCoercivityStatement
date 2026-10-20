/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.RegularUCoercivityFull
import AdalyFormal.Balaban.RegularUCurvedWitness

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `AlphaAnalyticity.lean` — the REAL regularity condition (CMP99b (3.35)/(3.36)) and the
gauge-covariant transport of the regular-`U` coercivity constant.

## Why this module exists — a DENOTATION defect, fixed rather than inherited

Every regular-`U` result in this tree so far hypothesises `frobSupBond U ≤ α₀`
(`α₁ = sup_b ‖U(b) − 1‖_F`). Two independent blind gates (Sol, Kimi) established that this is
**NOT** Bałaban's regularity condition. The source condition, read at
`corpus/pages/CMP99b_p396.md` (`verification_status: adjudicated`, dual-read, render sha256
`d0f0d665232fc871e005f2e721ea338e96c1a52763e151c3966bf7fcb47568ec`), is, VERBATIM:

> for an arbitrary cube `□` of the described above class, and for a configuration `U` **there
> exists a gauge transformation `u` on `□`** such that `U^u = e^{iηA}`, and if the index of `□` is
> `j`, then
> `|A| < O(1) M α₀ (L^j η)^{-1}`,  `|∇^η A| < O(1) M α₀ (L^j η)^{-2}`  on `□`     (3.35)
> `|∂^{η*}∂^η A| < O(1) M α₀ (L^j η)^{-3}`  on `□`                                (3.36)

and, two sentences later,

> "these regularity conditions do not impose any constraints on `U` outside the domain `Ω₀`"
> "For the operators introduced until now we need only the condition (3.35), but later on we will
> have to assume (3.36) also."

(The second sentence is quoted IN FULL, including its trailing clause: an earlier draft of this
docstring clipped it at "(3.35)." with no ellipsis, which a nested validator caught. The trailing
clause matters — it says (3.36) is needed LATER, not never, which is exactly why `Regular35` carries
the derivative clause instead of dropping it.)

### The mismatch, itemised (each item read off the printed text)

* **(M1) GAUGE ORBIT vs POINT.** The source quantifies `∃ u`. `frobSupBond U ≤ α₀` fixes `u = 1`.
  `frobSupBond` is **not gauge-invariant**, so as a hypothesis it is **strictly stronger**: it
  excludes configurations Bałaban admits. §3/§4 below repair exactly this.
* **(M2) CENTER / LARGE GAUGE.** Concretely: on a torus with `2 ∣ L μ + 1` (the compatibility the
  coercivity theorem already assumes), the constant configuration `U ≡ −1` is gauge-equivalent to
  `U ≡ 1` (`centerGauge`, §6), so it is (3.35)-regular at **every** `α₀ ≥ 0`, while
  `frobSupBond (U ≡ −1) = 2√2` — a factor `≈ 1150` above the threshold `√(γ₀/96) ≈ 2.46e−3` the
  coercivity needs. Proved in §6, not asserted.
* **(M3) DERIVATIVES.** (3.35) carries a `|∇^η A|` clause and (3.36) a `|∂^{η*}∂^η A|` clause.
  `frobSupBond` has **no** derivative clause. Modelled here by `gaugeGradSupBond` (§3), carried as a
  field of `Regular35` and — matching the source's own sentence — **not consumed** by the operator
  bound.
* **(M4) SCALE.** The printed threshold is `(L^j η)^{-1}`, indexed by the cube's index `j`; the
  group-level displacement is `η|A| < O(1) M α₀ L^{-j}`. `frobSupBond U ≤ α₀` is one scale-free
  number. §5 states the `k`/scale-uniform form: one constant, one threshold, quantified outside an
  arbitrary index type, an arbitrary family of lattices, and the backgrounds.
* **(M5) LOCALITY.** The source condition is per-cube inside `B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1})` and is
  **explicitly void** outside `Ω₀`. `frobSupBond` is a global sup over every bond of the torus.
  **NOT REPAIRED HERE** and stated as such. ~~"this tree has no `{Ω_j}` domain sequence, so the
  cube decomposition is not expressible at this carrier"~~ — **STRUCK 2026-08-05
  (`compute/formal_batch/`, S75), retained struck: THE PREMISE IS FALSE, and was already false when
  it was written.** The tree does carry a `{Ω_j}` domain sequence: `Balaban/SG_Geom.lean`'s
  `SourceGeometry.DomainSeq` formalizes CMP96 (2.1)-(2.4) with the nesting, the coarse
  representations and the `RM` margin, and it is INHABITED — `SG_Witness.DW`, `SG_Mge1.D2`,
  `SG_Mge2.D3`, `RC_Witness2.DW2` are four constructed instances — with `SG_Contain.Breg` the
  shells `B^j(Λ_j)` and `SG_Contain.breg_disjoint` their disjointness. Since 2026-08-05
  `Balaban/RegularityGap.lean` §17 additionally carries `DomainTower` / `PrintedOmegaData` on the
  `PeriodicLatticeSite` carrier, i.e. p.396's cube class with its three printed clauses and its
  printed index. **What remains true is the narrower claim, which is what this bullet should have
  said:** the cube decomposition is not expressible in terms of `frobSupBond`, THIS module's
  object, and no module here imports either domain-sequence layer. What is built is the
  **global-cube** specialization (`□ = ` the whole torus, one index `j`), which is the honest
  single-scale reading.

### What this module DELIVERS (and does not)

1. `GaugeRegular α₀ U := ∃ γ, frobSupBond (U^γ) ≤ α₀` — the (M1)/(M2) repair, the gauge-invariant
   hypothesis. `Regular35` packages it with the (M3) derivative clause.
2. A complete **gauge-covariance layer** for the objects the coercivity is stated in: the path
   holonomy, `rZeroA`, the faithful covariant `Q_ell(U) = lineCoarseRestrictCov`, the covariant curl,
   `dstarDQuadForm`, `bondEnergy`, the axial-gauge clause, and `ker Q_ell(U)`.
3. **The transport theorem** `deltaJ_gaugeRegular_coercive` — the regular-`U` single-scale coercivity
   for every `GaugeRegular` background, with the SAME explicit `k`-free constant.
4. **(b3)** `gamma0_uniform_over_family` — one constant and one threshold for an arbitrary family of
   scales/lattices/backgrounds.
5. Junk attacks on this module's own statements (§7) and the strictness witnesses (§6).

**NOT delivered:** the cube decomposition (M5); the exponential chart `U^u = e^{iηA}` (the tree has
no `exp : 𝔰𝔲(2) → SU(2)`, so the algebra-level bounds are modelled at the GROUP level by
`frobSupBond`/`gaugeGradSupBond`, which is a **proxy**, disclosed); (3.36)'s second-derivative clause
(also proxied, also unused); and the full `C*Δ_kC`, which this brick's input
(`RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU`) does not close either.

`#print axioms` on every declaration below.
-/

namespace AdalyFormal.Balaban.AlphaAnalyticity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.Q1Real
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

variable {L : PeriodicLatticeExtent}

/-- Abbreviation for the SU(2) matrix group used throughout. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-! ## §1 — the gauge action on backgrounds and on `𝔰𝔲(2)`-valued bond fields

`U^γ(b) = γ(b₋) U(b) γ(b₊)⁻¹` is `Target.ClayStatement.periodicGaugeTransform` (reused, LAW-19).
The matching action on a bond field is `A^γ(b) = R(γ(b₋)) A(b)` — CMP99b (3.32)/(3.34)'s `R(u)`
conjugation, which is what makes `Δ_a(U^u) = R(u) Δ_a(U) R(u^{-1})` hold. -/

/-- A gauge transformation: an `SU(2)`-valued function on sites. -/
abbrev GaugeFn (L : PeriodicLatticeExtent) := PeriodicLatticeSite L → SU2

/-- **`A^γ(b) = R(γ(b₋)) A(b)`** — the adjoint action of a gauge transformation on an
`𝔰𝔲(2)`-valued bond field, based at the bond's MINUS endpoint (the same base point the covariant
curl and the covariant line integral use). -/
noncomputable def gaugeActA (γ : GaugeFn L) (A : Bond L → SuTwo) : Bond L → SuTwo :=
  fun b => RMap (γ b.1) (A b)

/-- Pointwise inverse of a gauge transformation. -/
def gaugeInv (γ : GaugeFn L) : GaugeFn L := fun x => (γ x)⁻¹

/-- Pointwise product of two gauge transformations. -/
def gaugeMul (γ δ : GaugeFn L) : GaugeFn L := fun x => γ x * δ x

theorem gaugeActA_apply (γ : GaugeFn L) (A : Bond L → SuTwo) (b : Bond L) :
    gaugeActA γ A b = RMap (γ b.1) (A b) := rfl

/-- The gauge action on backgrounds composes: `(U^δ)^γ = U^{γδ}`. -/
theorem gaugeTransform_comp (γ δ : GaugeFn L) (U : PeriodicLinkConfiguration SU2 L) :
    periodicGaugeTransform γ (periodicGaugeTransform δ U)
      = periodicGaugeTransform (gaugeMul γ δ) U := by
  funext b
  simp only [periodicGaugeTransform, gaugeMul, mul_inv_rev]
  group

/-- The trivial gauge transformation acts trivially on backgrounds. -/
theorem gaugeTransform_one (U : PeriodicLinkConfiguration SU2 L) :
    periodicGaugeTransform (fun _ => (1 : SU2)) U = U := by
  funext b; simp [periodicGaugeTransform]

/-- `γ⁻¹ γ = 1` pointwise. -/
theorem gaugeMul_inv_left (γ : GaugeFn L) : gaugeMul (gaugeInv γ) γ = fun _ => (1 : SU2) := by
  funext x; simp [gaugeMul, gaugeInv]

/-- **Undoing a gauge transformation**: `(U^γ)^{γ⁻¹} = U`. -/
theorem gaugeTransform_inv (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2 L) :
    periodicGaugeTransform (gaugeInv γ) (periodicGaugeTransform γ U) = U := by
  rw [gaugeTransform_comp, gaugeMul_inv_left, gaugeTransform_one]

#print axioms gaugeActA_apply
#print axioms gaugeTransform_comp
#print axioms gaugeTransform_one
#print axioms gaugeMul_inv_left
#print axioms gaugeTransform_inv

/-! ## §2 — GAUGE COVARIANCE of every object the coercivity statement mentions

This is the analytic content that makes (M1) repairable: CMP99b (3.34) prints
`Δ_a(U^u) = R(u) Δ_a(U) R(u^{-1})`, and `R(u)` is an isometry, so the coercivity CONSTANT is a
gauge invariant. Each step below is proved, not quoted. -/

/-- A backward step, then a forward shift, returns to the starting site. -/
theorem shift_step_false (x : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShift (periodicLatticeStep x (μ, false)) μ = x := by
  show Function.update (Function.update x μ (x μ - 1)) μ
      (Function.update x μ (x μ - 1) μ + 1) = x
  rw [Function.update_self, Function.update_idem, sub_add_cancel, Function.update_eq_self]

/-- **HOLONOMY GAUGE COVARIANCE.** `hol(U^γ; x, s) = γ(x) · hol(U; x, s) · γ(endpoint)⁻¹`, for any
signed path `s` (forward AND backward steps). This is the primitive every transport covariance
below rests on; it did not previously exist in this tree. -/
theorem periodicPathHolonomy_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2 L)
    (x : PeriodicLatticeSite L) (s : List (Fin 3 × Bool)) :
    periodicPathHolonomy (periodicGaugeTransform γ U) x s
      = γ x * periodicPathHolonomy U x s * (γ (periodicPathEndpoint x s))⁻¹ := by
  induction s generalizing x with
  | nil => simp [periodicPathHolonomy, periodicPathEndpoint]
  | cons step rest ih =>
    show (if step.2 then periodicGaugeTransform γ U (x, step.1)
        else (periodicGaugeTransform γ U (periodicLatticeStep x step, step.1))⁻¹)
        * periodicPathHolonomy (periodicGaugeTransform γ U) (periodicLatticeStep x step) rest
      = γ x * ((if step.2 then U (x, step.1)
        else (U (periodicLatticeStep x step, step.1))⁻¹)
        * periodicPathHolonomy U (periodicLatticeStep x step) rest)
        * (γ (periodicPathEndpoint (periodicLatticeStep x step) rest))⁻¹
    rw [ih]
    have hfactor : (if step.2 then periodicGaugeTransform γ U (x, step.1)
        else (periodicGaugeTransform γ U (periodicLatticeStep x step, step.1))⁻¹)
      = γ x * (if step.2 then U (x, step.1)
        else (U (periodicLatticeStep x step, step.1))⁻¹)
        * (γ (periodicLatticeStep x step))⁻¹ := by
      rcases step with ⟨μ, dir⟩
      cases dir with
      | true =>
        simp only [periodicGaugeTransform]
        show γ x * U (x, μ) * (γ (periodicLatticeShift x μ))⁻¹
          = γ x * U (x, μ) * (γ (periodicLatticeStep x (μ, true)))⁻¹
        rfl
      | false =>
        have hb : periodicLatticeShift (periodicLatticeStep x (μ, false)) μ = x :=
          shift_step_false x μ
        show (γ (periodicLatticeStep x (μ, false)) * U (periodicLatticeStep x (μ, false), μ)
            * (γ (periodicLatticeShift (periodicLatticeStep x (μ, false)) μ))⁻¹)⁻¹
          = γ x * (U (periodicLatticeStep x (μ, false), μ))⁻¹
            * (γ (periodicLatticeStep x (μ, false)))⁻¹
        rw [hb]
        group
    rw [hfactor]
    group

#print axioms shift_step_false
#print axioms periodicPathHolonomy_gauge

/-- `transportPath`'s endpoint is the fine bond's own base site `pathSite x μ i`. -/
theorem transportPath_endpoint (c x : PeriodicLatticeSite L) (μ : Fin 3) (i : ℕ) :
    periodicPathEndpoint c (transportPath c x μ i) = pathSite x μ i := by
  unfold transportPath
  rw [periodicPathEndpoint_append, GammaPath_endpoint, straightSegment_endpoint]
  funext ν
  by_cases h : ν = μ
  · subst h; rw [Function.update_self]
  · rw [Function.update_of_ne h]
    -- off direction `μ`, `pathSite x μ i` agrees with `x`
    have key : ∀ (n : ℕ) (z : PeriodicLatticeSite L), ν ≠ μ → pathSite z μ n ν = z ν := by
      intro n
      induction n with
      | zero => intro z _; rw [pathSite_zero]
      | succ n ihn =>
        intro z hν
        rw [pathSite_succ]
        show Function.update (pathSite z μ n) μ (pathSite z μ n μ + 1) ν = z ν
        rw [Function.update_of_ne hν, ihn z hν]
    exact (key i x h).symm

#print axioms transportPath_endpoint

/-- **`rZeroA` GAUGE COVARIANCE**: `R_{0,c₋}` transports the whole covariant line-integral sum by a
single `R(γ(c₋))`. The per-bond `γ(b₋)` factors from `A^γ` cancel exactly against the per-bond
holonomy endpoints — which is the reason this object is the covariant one. -/
theorem rZeroA_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2 L)
    (c x : PeriodicLatticeSite L) (A : Bond L → SuTwo) (μ : Fin 3) (ell : ℕ) :
    rZeroA (periodicGaugeTransform γ U) c x (gaugeActA γ A) μ ell
      = RMap (γ c) (rZeroA U c x A μ ell) := by
  unfold rZeroA
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [periodicPathHolonomy_gauge, transportPath_endpoint, gaugeActA_apply]
  rw [RMap_mul_apply, RMap_mul_apply]
  congr 1
  group

#print axioms rZeroA_gauge

/-- **`Q_ell(U)` GAUGE COVARIANCE** — the faithful covariant line-integral average transforms by
`R(γ(c₋))` at the coarse bond's base site. -/
theorem lineCoarseRestrictCov_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (A : Bond L → SuTwo) (b : CoarseBond L ell) :
    lineCoarseRestrictCov (periodicGaugeTransform γ U) ell (gaugeActA γ A) b
      = RMap (γ b.1.1) (lineCoarseRestrictCov U ell A b) := by
  unfold lineCoarseRestrictCov
  rw [map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => rZeroA_gauge γ U b.1.1 x A b.2 ell)

#print axioms lineCoarseRestrictCov_gauge

/-- **`ker Q_ell(U)` IS GAUGE EQUIVARIANT**: `A ∈ ker Q_ell(U) → A^γ ∈ ker Q_ell(U^γ)`. -/
theorem mem_kerQ_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : Bond L → SuTwo) (hker : ∀ b : CoarseBond L ell, lineCoarseRestrictCov U ell A b = 0) :
    ∀ b : CoarseBond L ell,
      lineCoarseRestrictCov (periodicGaugeTransform γ U) ell (gaugeActA γ A) b = 0 := by
  intro b
  rw [lineCoarseRestrictCov_gauge, hker b, map_zero]

#print axioms mem_kerQ_gauge

/-- **COVARIANT CURL GAUGE COVARIANCE** — CMP99b (3.34)'s `R(u)`-conjugation, at the level of the
curl itself: `(D_{U^γ} A^γ)(p) = R(γ(p₀)) (D_U A)(p)`, `p₀` the plaquette's base site. -/
theorem curlValueCovariant_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2 L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    curlValueCovariant (periodicGaugeTransform γ U) (gaugeActA γ A) p
      = RMap (γ p.1) (curlValueCovariant U A p) := by
  unfold curlValueCovariant
  simp only [gaugeActA_apply, map_sub, map_add]
  have h1 : RMap (periodicGaugeTransform γ U (p.1, p.2.1.1))
      (RMap (γ (periodicLatticeShift p.1 p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)))
      = RMap (γ p.1) (RMap (U (p.1, p.2.1.1))
          (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))) := by
    have hmul : periodicGaugeTransform γ U (p.1, p.2.1.1) * γ (periodicLatticeShift p.1 p.2.1.1)
        = γ p.1 * U (p.1, p.2.1.1) := by
      show γ p.1 * U (p.1, p.2.1.1) * (γ (periodicLatticeShift p.1 p.2.1.1))⁻¹
          * γ (periodicLatticeShift p.1 p.2.1.1) = γ p.1 * U (p.1, p.2.1.1)
      group
    rw [RMap_mul_apply, RMap_mul_apply, hmul]
  have h2 : RMap (periodicGaugeTransform γ U (p.1, p.2.1.2))
      (RMap (γ (periodicLatticeShift p.1 p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)))
      = RMap (γ p.1) (RMap (U (p.1, p.2.1.2))
          (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))) := by
    have hmul : periodicGaugeTransform γ U (p.1, p.2.1.2) * γ (periodicLatticeShift p.1 p.2.1.2)
        = γ p.1 * U (p.1, p.2.1.2) := by
      show γ p.1 * U (p.1, p.2.1.2) * (γ (periodicLatticeShift p.1 p.2.1.2))⁻¹
          * γ (periodicLatticeShift p.1 p.2.1.2) = γ p.1 * U (p.1, p.2.1.2)
      group
    rw [RMap_mul_apply, RMap_mul_apply, hmul]
  rw [h1, h2]

#print axioms curlValueCovariant_gauge

/-- **THE COERCIVITY FORM IS A GAUGE INVARIANT**: `‖D_{U^γ} A^γ‖² = ‖D_U A‖²`, because `R` is an
isometry for `hsInner` (`SuTwoInner.hsInner_RMap`). -/
theorem dstarDQuadForm_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2 L)
    (A : Bond L → SuTwo) :
    dstarDQuadForm (periodicGaugeTransform γ U) (gaugeActA γ A) = dstarDQuadForm U A := by
  unfold dstarDQuadForm covPlaqInner
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [curlValueCovariant_gauge, hsInner_RMap]

#print axioms dstarDQuadForm_gauge

/-- `‖R(g) X‖ = ‖X‖`. -/
theorem norm_RMap (g : SU2) (X : SuTwo) : ‖RMap g X‖ = ‖X‖ := (RIsometry g).norm_map X

/-- **THE BOND ENERGY IS A GAUGE INVARIANT**: `bondEnergy A^γ = bondEnergy A`. -/
theorem bondEnergy_gauge (γ : GaugeFn L) (A : Bond L → SuTwo) :
    bondEnergy (gaugeActA γ A) = bondEnergy A := by
  unfold bondEnergy
  exact Finset.sum_congr rfl (fun b _ => by rw [gaugeActA_apply, norm_RMap])

#print axioms norm_RMap
#print axioms bondEnergy_gauge

/-- **THE AXIAL GAUGE CLAUSE IS GAUGE EQUIVARIANT** — `R(g)` is linear, so it maps `0` to `0`; the
staircase-vanishing condition transfers verbatim. -/
theorem axialGauge_gauge (γ : GaugeFn L) (ell : ℕ) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell → ∀ b ∈ staircasePath y x, A b = 0) :
    ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell →
        ∀ b ∈ staircasePath y x, gaugeActA γ A b = 0 := by
  intro y hy x hx b hb
  rw [gaugeActA_apply, hadm y hy x hx b hb, map_zero]

#print axioms axialGauge_gauge

/-- `A^γ = 0 ↔ A = 0` — `R(g)` is injective (an isometry), so the gauge action does not create or
destroy nonzero fields. Used for the non-degeneracy of the transported witnesses. -/
theorem gaugeActA_eq_zero_iff (γ : GaugeFn L) (A : Bond L → SuTwo) :
    gaugeActA γ A = 0 ↔ A = 0 := by
  constructor
  · intro h
    funext b
    have hb : RMap (γ b.1) (A b) = 0 := congrFun h b
    have : ‖A b‖ = 0 := by rw [← norm_RMap (γ b.1) (A b), hb, norm_zero]
    exact norm_eq_zero.mp this
  · intro h
    funext b
    rw [gaugeActA_apply, show A b = 0 from congrFun h b, map_zero]
    rfl

#print axioms gaugeActA_eq_zero_iff

/-! ## §3 — THE REAL REGULARITY PREDICATE (CMP99b (3.35), global-cube specialization)

`GaugeRegular` is the (M1)/(M2) repair: the source's `∃ u` restored. `Regular35` adds the (M3)
derivative clause. Both are **hypothesis-position** existentials, so the weaker the `∃` the STRONGER
the theorem that consumes it — the opposite polarity from the S91 free-data defect, which bites when
an `∃` is in the CONCLUSION. Recorded here because it is the first question a prosecutor asks. -/

/-- **(M3) proxy — the group-level discrete derivative sup**, `sup_{b,ν} ‖U(b + e_ν) − U(b)‖_F`,
modelling `|∇^η A|` in (3.35) at the tree's unit-`η` convention. This is a PROXY: the source bounds
the ALGEBRA field `A` in the chart `U^u = e^{iηA}`, ~~and this tree has no
`exp : 𝔰𝔲(2) → SU(2)`~~ **STRUCK 2026-07-30 — FALSE, and false when written.**

`Balaban/SuTwoLogExpCore.lean` defines BOTH halves of that chart: `su2Exp : M2 → SU2` (Mathlib's
`NormedSpace.exp`, guarded into `SU(2)`) and `su2Log : SU2 → M2`, the ordinary anti-Hermitian —
i.e. `𝔰𝔲(2)`-valued — principal logarithm; and `Balaban.RegularityGap.su2_exp_log_of_ne_negOne`
proves `su2Exp (su2Log g) = g` for every `g ≠ −1`. Precisely stated: `SuTwoLogExpCore` is NOT in
THIS module's import closure (measured), but it is in the TREE, and `Balaban/RegularityGap.lean`
imports it alongside this file and uses it to state (3.35)/(3.36) faithfully. The sentence claimed
something about the tree that was not true of the tree.

**The clause may still be a proxy — but not for that reason, and this note does not close it.**
What actually separates this definition from (3.35)'s second clause is that it differences GROUP
elements rather than chart fields (`RegularityGap.gradA` differences the fields), that it carries no
`(L^jη)⁻²` scale factor, and that it uses ONE global gauge where the source takes a per-cube `u`.
`RegularityGap` states the source's clause with all four parameters and settles the CLASS comparison
(`src3536_eta_free`, `src3536Log_of_gaugeRegular_uncond`, `exists_wideness_witness`); no theorem
anywhere relates `gaugeGradSupBond` to `RegularityGap.gradA`, and nothing here should be read as
supplying one. -/
noncomputable def gaugeGradSupBond (U : PeriodicLinkConfiguration SU2 L) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun q : Bond L × Fin 3 =>
      RMapLipschitz.frobNorm
        ((U (periodicLatticeShift q.1.1 q.2, q.1.2) : Matrix (Fin 2) (Fin 2) ℂ)
          - (U q.1 : Matrix (Fin 2) (Fin 2) ℂ)))

/-- **`GaugeRegular α₀ U` — CMP99b (3.35)'s FIRST clause with its `∃ u` restored.**
`∃ γ, sup_b ‖(U^γ)(b) − 1‖_F ≤ α₀`. This is the gauge-invariant hypothesis; `frobSupBond U ≤ α₀`
is its `γ = 1` specialization and is strictly stronger (§6). -/
def GaugeRegular (α₀ : ℝ) (U : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∃ γ : GaugeFn L, frobSupBond (periodicGaugeTransform γ U) ≤ α₀

/-- **`Regular35 α₀ U`** — both clauses of (3.35), on ONE common gauge `γ` (as the source demands:
a single `u` per cube serves both bounds). The value clause is `GaugeRegular`; the derivative clause
is the (M3) proxy. Matching the source's own sentence *"For the operators introduced until now we
need only the condition (3.35)"* — and, inside (3.35), the operator bound of this campaign consumes
only the VALUE clause — the derivative clause is carried and **not used** by §4. -/
def Regular35 (α₀ : ℝ) (U : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∃ γ : GaugeFn L,
    frobSupBond (periodicGaugeTransform γ U) ≤ α₀ ∧
      gaugeGradSupBond (periodicGaugeTransform γ U) ≤ α₀

theorem gaugeRegular_of_regular35 {α₀ : ℝ} {U : PeriodicLinkConfiguration SU2 L}
    (h : Regular35 α₀ U) : GaugeRegular α₀ U := by
  obtain ⟨γ, h1, _⟩ := h; exact ⟨γ, h1⟩

/-- **`frobSupBond U ≤ α₀ ⟹ GaugeRegular α₀ U`** — the campaign's proxy hypothesis is the `γ = 1`
specialization of the real one. (The converse is FALSE: §6.) -/
theorem gaugeRegular_of_frobSupBond_le {α₀ : ℝ} {U : PeriodicLinkConfiguration SU2 L}
    (h : frobSupBond U ≤ α₀) : GaugeRegular α₀ U :=
  ⟨fun _ => 1, by rw [gaugeTransform_one]; exact h⟩

/-- **`GaugeRegular` IS GAUGE-INVARIANT** — the property (M1) says the source condition has and the
proxy lacks. Proved, not asserted. -/
theorem gaugeRegular_gauge_invariant {α₀ : ℝ} (δ : GaugeFn L)
    (U : PeriodicLinkConfiguration SU2 L) :
    GaugeRegular α₀ (periodicGaugeTransform δ U) ↔ GaugeRegular α₀ U := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨gaugeMul γ δ, by rwa [← gaugeTransform_comp]⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨gaugeMul γ (gaugeInv δ), ?_⟩
    rw [← gaugeTransform_comp, gaugeTransform_comp (gaugeInv δ) δ U, gaugeMul_inv_left,
      gaugeTransform_one]
    exact hγ

#print axioms gaugeRegular_of_regular35
#print axioms gaugeRegular_of_frobSupBond_le
#print axioms gaugeRegular_gauge_invariant

/-! ## §4 — THE TRANSPORT: the regular-`U` coercivity constant for every `GaugeRegular` background

The constant, and its `α`-monotonicity, first. `γ₀ = (1/108)(1/2⁴) = 1/1728` is the literal the
`U = 1` su(2) additive base delivers; `coercConst α = (√(γ₀ − 64α²) − 4√2·α)²` is the constant the
single-scale perturbation (b1) + `[QCHAIN-SENS]` (b2) deliver at `α₁ = α`. -/

/-- The `U = 1` base constant `γ₀ = (1/108)·(1/2⁴) = 1/1728`, written exactly as the imported
theorem states it. -/
noncomputable def gammaZeroLit : ℝ := (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4)

theorem gammaZeroLit_def : gammaZeroLit = (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) := rfl

theorem gammaZeroLit_eq : gammaZeroLit = 1 / 1728 := by
  rw [gammaZeroLit]; norm_num

/-- **The coercivity constant as a function of the smallness parameter**, `k`-free and
lattice-free. -/
noncomputable def coercConst (α : ℝ) : ℝ :=
  (Real.sqrt (gammaZeroLit - 64 * α ^ 2) - 4 * Real.sqrt 2 * α) ^ 2

theorem sqrt_thirtytwo : Real.sqrt 32 = 4 * Real.sqrt 2 := by
  rw [show (32 : ℝ) = 4 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]

theorem four_sqrt_two_mul {a : ℝ} (ha : 0 ≤ a) : 4 * Real.sqrt 2 * a = Real.sqrt (32 * a ^ 2) := by
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq ha, sqrt_thirtytwo]

/-- **The `hsmall` clause from the threshold** — `96α² ≤ γ₀` gives the STRICT-DIFFERENCE form, the
one that is a genuine certificate (trap α of `RegularUCurvedWitness.sqrt_neg_trap`). -/
theorem coercConst_hsmall {a : ℝ} (ha : 0 ≤ a) (h : 96 * a ^ 2 ≤ gammaZeroLit) :
    0 ≤ Real.sqrt (gammaZeroLit - 64 * a ^ 2) - 4 * Real.sqrt 2 * a := by
  rw [four_sqrt_two_mul ha, sub_nonneg]
  exact Real.sqrt_le_sqrt (by linarith)

theorem coercConst_pos {a : ℝ} (ha : 0 ≤ a) (h : 96 * a ^ 2 < gammaZeroLit) :
    0 < coercConst a := by
  have hlt : Real.sqrt (32 * a ^ 2) < Real.sqrt (gammaZeroLit - 64 * a ^ 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  rw [coercConst, four_sqrt_two_mul ha]
  exact pow_pos (by linarith) 2

/-- **The constant is ANTITONE in the smallness parameter** — the step that turns the `α₁`-exact
bound into an `α₀`-uniform one. -/
theorem coercConst_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 96 * b ^ 2 ≤ gammaZeroLit) :
    coercConst b ≤ coercConst a := by
  have hb0 : 0 ≤ b := le_trans ha hab
  have h1 : Real.sqrt (gammaZeroLit - 64 * b ^ 2) ≤ Real.sqrt (gammaZeroLit - 64 * a ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h2 : 4 * Real.sqrt 2 * a ≤ 4 * Real.sqrt 2 * b := by
    nlinarith [Real.sqrt_nonneg 2]
  have hDb : 0 ≤ Real.sqrt (gammaZeroLit - 64 * b ^ 2) - 4 * Real.sqrt 2 * b :=
    coercConst_hsmall hb0 hb
  unfold coercConst
  nlinarith [hDb, h1, h2]

/-- **`√γ₀ ≤ 1/41`** — `41² = 1681 < 1728`. -/
theorem sqrt_gammaZeroLit_le : Real.sqrt gammaZeroLit ≤ 1 / 41 := by
  have h1 : gammaZeroLit ≤ (1 / 41 : ℝ) ^ 2 := by rw [gammaZeroLit_eq]; norm_num
  calc Real.sqrt gammaZeroLit ≤ Real.sqrt ((1 / 41 : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
    _ = 1 / 41 := Real.sqrt_sq (by norm_num)

theorem sqrt_two_le : Real.sqrt 2 ≤ 3 / 2 := by
  calc Real.sqrt 2 ≤ Real.sqrt ((3 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 3 / 2 := Real.sqrt_sq (by norm_num)

/-- **THE DEGRADATION IS `O(α₀)`, WITH THE `O`-CONSTANT EQUAL TO `1` — this is the `O(Mα₀)` the
program asks for, as an inequality rather than an inspection.**

`coercConst α ≥ γ₀ − α` for every `0 ≤ α ≤ 1/500`. So the coercivity constant leaves the `U = 1` base
`γ₀ = 1/1728` LINEARLY in the regularity parameter, and the linear rate is bounded by an absolute
number: nothing in the bound depends on the lattice, the RG step, the scale, or the background.

Mechanism, exactly: `coercConst α = γ₀ − 32α² − 8√2·α·√(γ₀ − 64α²)`, and on the stated range
`32α² + 8√2·α·√(γ₀ − 64α²) ≤ α·(32/500 + 8·(3/2)·(1/41)) < α`. -/
theorem coercConst_ge_linear {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 500) :
    gammaZeroLit - a ≤ coercConst a := by
  have hg0 : gammaZeroLit = 1 / 1728 := gammaZeroLit_eq
  have hnn : (0 : ℝ) ≤ gammaZeroLit - 64 * a ^ 2 := by rw [hg0]; nlinarith
  set s := Real.sqrt (gammaZeroLit - 64 * a ^ 2) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = gammaZeroLit - 64 * a ^ 2 := Real.sq_sqrt hnn
  have hbnd : s ≤ 1 / 41 :=
    le_trans (Real.sqrt_le_sqrt (by nlinarith)) sqrt_gammaZeroLit_le
  have h2 : Real.sqrt 2 ≤ 3 / 2 := sqrt_two_le
  have h2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- expand the square, using (4√2)² = 32
  have hexp : (s - 4 * Real.sqrt 2 * a) ^ 2
      = (gammaZeroLit - 64 * a ^ 2) - 8 * (Real.sqrt 2 * a * s) + 32 * a ^ 2 := by
    have hring : (s - 4 * Real.sqrt 2 * a) ^ 2
        = s ^ 2 - 8 * (Real.sqrt 2 * a * s) + 16 * Real.sqrt 2 ^ 2 * a ^ 2 := by ring
    rw [hring, hsq, hsq2]; ring
  -- the cross term, bounded by chaining √2 ≤ 3/2 and s ≤ 1/41 one factor at a time
  have hprod : Real.sqrt 2 * a * s ≤ 3 / 2 * a * (1 / 41) := by
    have hstep1 : Real.sqrt 2 * a ≤ 3 / 2 * a := by nlinarith
    have hstep2 : Real.sqrt 2 * a * s ≤ 3 / 2 * a * s := by nlinarith
    have h32a : (0 : ℝ) ≤ 3 / 2 * a := by positivity
    calc Real.sqrt 2 * a * s ≤ 3 / 2 * a * s := hstep2
      _ ≤ 3 / 2 * a * (1 / 41) := by nlinarith
  have hasq : a ^ 2 ≤ a * (1 / 500) := by nlinarith
  show gammaZeroLit - a ≤ (s - 4 * Real.sqrt 2 * a) ^ 2
  rw [hexp]
  nlinarith [hprod, hasq, ha]

/-- **And it never EXCEEDS the base** — `coercConst α ≤ γ₀`, so `γ₀` is exactly the `U = 1` value and
the perturbation is a genuine degradation, never a free improvement. -/
theorem coercConst_le_base {a : ℝ} (ha : 0 ≤ a) (hthr : 96 * a ^ 2 ≤ gammaZeroLit) :
    coercConst a ≤ gammaZeroLit := by
  have hnn : (0 : ℝ) ≤ gammaZeroLit - 64 * a ^ 2 := by nlinarith
  set s := Real.sqrt (gammaZeroLit - 64 * a ^ 2) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = gammaZeroLit - 64 * a ^ 2 := Real.sq_sqrt hnn
  have h2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hexp : (s - 4 * Real.sqrt 2 * a) ^ 2
      = (gammaZeroLit - 64 * a ^ 2) - 8 * (Real.sqrt 2 * a * s) + 32 * a ^ 2 := by
    have hring : (s - 4 * Real.sqrt 2 * a) ^ 2
        = s ^ 2 - 8 * (Real.sqrt 2 * a * s) + 16 * Real.sqrt 2 ^ 2 * a ^ 2 := by ring
    rw [hring, hsq, hsq2]; ring
  show (s - 4 * Real.sqrt 2 * a) ^ 2 ≤ gammaZeroLit
  rw [hexp]
  nlinarith [mul_nonneg (mul_nonneg h2nn ha) hs0, sq_nonneg a, ha]

#print axioms gammaZeroLit_def
#print axioms gammaZeroLit_eq
#print axioms sqrt_gammaZeroLit_le
#print axioms sqrt_two_le
#print axioms coercConst_ge_linear
#print axioms coercConst_le_base
#print axioms sqrt_thirtytwo
#print axioms four_sqrt_two_mul
#print axioms coercConst_hsmall
#print axioms coercConst_pos
#print axioms coercConst_anti

/-- **THE TRANSPORT THEOREM, exact form.** The regular-`U` single-scale coercivity of `‖D_U A‖²` on
`ker Q₁(U) ∩ axial-gauge` holds for a background `U` whose smallness is measured **in a gauge `γ` of
its own choosing**, with the constant read at `α₁ = frobSupBond (U^γ)` — the same expression the
`frobSupBond U`-hypothesis theorem delivers, now on a strictly larger class of backgrounds.

`A` is the field at `U` itself: no transport is imposed on the user, because the form and the two
domain clauses are gauge invariants (§2). -/
theorem deltaJ_gaugeRegular_coercive_exact
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration SU2 L) (γ : GaugeFn L) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0)
    (hthr : 64 * frobSupBond (periodicGaugeTransform γ U) ^ 2
      ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4))
    (hsmall : 0 ≤ Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4)
        - 64 * frobSupBond (periodicGaugeTransform γ U) ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond (periodicGaugeTransform γ U)) :
    (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4)
        - 64 * frobSupBond (periodicGaugeTransform γ U) ^ 2)
        - 4 * Real.sqrt 2 * frobSupBond (periodicGaugeTransform γ U)) ^ 2 * bondEnergy A
      ≤ dstarDQuadForm U A := by
  have base := RegularUCoercivityFull.deltaJ_regularU_coercive_on_kerQU hL hdvd
    (periodicGaugeTransform γ U) (gaugeActA γ A)
    (axialGauge_gauge γ 2 A hadm) (mem_kerQ_gauge γ U 2 A hkerU) hthr hsmall
  rwa [bondEnergy_gauge, dstarDQuadForm_gauge] at base

#print axioms deltaJ_gaugeRegular_coercive_exact

/-- **THE TRANSPORT THEOREM, `α₀`-uniform form (b2).** For every background in the (3.35) class
`GaugeRegular α₀` — no gauge named, no smallness of `U` itself assumed — the coercivity holds with
the SINGLE constant `coercConst α₀`, which depends on `α₀` alone: not on the lattice `L`, not on the
RG step, not on the background `U`, not on the field `A`. -/
theorem deltaJ_gaugeRegular_coercive
    (hL : ∀ μ : Fin 3, 4 ≤ L μ) (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hthr : 96 * α₀ ^ 2 ≤ gammaZeroLit)
    (U : PeriodicLinkConfiguration SU2 L) (hreg : GaugeRegular α₀ U) (A : Bond L → SuTwo)
    (hadm : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y 2 → ∀ b ∈ staircasePath y x, A b = 0)
    (hkerU : ∀ b : CoarseBond L 2, lineCoarseRestrictCov U 2 A b = 0) :
    coercConst α₀ * bondEnergy A ≤ dstarDQuadForm U A := by
  obtain ⟨γ, hγ⟩ := hreg
  have hα₁0 : 0 ≤ frobSupBond (periodicGaugeTransform γ U) := frobSupBond_nonneg _
  have h96 : 96 * frobSupBond (periodicGaugeTransform γ U) ^ 2 ≤ gammaZeroLit := by nlinarith
  have hthr1 : 64 * frobSupBond (periodicGaugeTransform γ U) ^ 2
      ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by
    rw [← gammaZeroLit_def]; nlinarith
  have hsmall1 := coercConst_hsmall hα₁0 h96
  rw [gammaZeroLit_def] at hsmall1
  have base := deltaJ_gaugeRegular_coercive_exact hL hdvd U γ A hadm hkerU hthr1 hsmall1
  have hmono : coercConst α₀ ≤ coercConst (frobSupBond (periodicGaugeTransform γ U)) :=
    coercConst_anti hα₁0 hγ hthr
  have hbe : 0 ≤ bondEnergy A := bondEnergy_nonneg A
  have hcc : coercConst (frobSupBond (periodicGaugeTransform γ U))
      = (Real.sqrt ((1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4)
          - 64 * frobSupBond (periodicGaugeTransform γ U) ^ 2)
          - 4 * Real.sqrt 2 * frobSupBond (periodicGaugeTransform γ U)) ^ 2 := rfl
  calc coercConst α₀ * bondEnergy A
      ≤ coercConst (frobSupBond (periodicGaugeTransform γ U)) * bondEnergy A :=
        mul_le_mul_of_nonneg_right hmono hbe
    _ ≤ dstarDQuadForm U A := by rw [hcc]; exact base

#print axioms deltaJ_gaugeRegular_coercive

/-! ## §5 — (b3) `[UNIF-ALPHA]`: ONE constant and ONE threshold for a whole family of scales

The `K`-indexed shape makes `k`-uniformity syntactically visible: `γ₀'` and `α₀` are bound BEFORE
the index type, the family of lattices, the backgrounds and the fields. It is equivalent to the
plain `(L, U, A)`-quantified statement precisely because both constants are bound outside — and
that equivalence IS the content of `k`-uniformity at a single scale, stated rather than implied. -/

/-- **The (b3) `k`/scale-uniform coercivity predicate.** -/
def Gamma0ScaleUniform (γ₀' α₀ : ℝ) : Prop :=
  0 < γ₀' ∧ 0 < α₀ ∧
    ∀ (K : Type) (k : K) (Lf : K → PeriodicLatticeExtent)
      (Uf : (j : K) → PeriodicLinkConfiguration SU2 (Lf j))
      (Af : (j : K) → Bond (Lf j) → SuTwo),
      (∀ μ : Fin 3, 4 ≤ Lf k μ) → (∀ μ : Fin 3, (2 : ℕ) ∣ (Lf k μ + 1)) →
      GaugeRegular α₀ (Uf k) →
      (∀ y : PeriodicLatticeSite (Lf k), y ∈ CoarseLattice (Lf k) 2 →
        ∀ x : PeriodicLatticeSite (Lf k), x ∈ blockOf y 2 →
        ∀ b ∈ staircasePath y x, Af k b = 0) →
      (∀ b : CoarseBond (Lf k) 2, lineCoarseRestrictCov (Uf k) 2 (Af k) b = 0) →
      γ₀' * bondEnergy (Af k) ≤ dstarDQuadForm (Uf k) (Af k)

/-- **(b3) PROVED at an explicit threshold.** `α₀ = 1/500` and
`γ₀' = coercConst (1/500) > 0`, both absolute numbers. -/
theorem gamma0_uniform_over_family :
    Gamma0ScaleUniform (coercConst (1 / 500)) (1 / 500) := by
  have hthr : 96 * ((1 : ℝ) / 500) ^ 2 ≤ gammaZeroLit := by
    rw [gammaZeroLit_eq]; norm_num
  have hthrlt : 96 * ((1 : ℝ) / 500) ^ 2 < gammaZeroLit := by
    rw [gammaZeroLit_eq]; norm_num
  refine ⟨coercConst_pos (by norm_num) hthrlt, by norm_num, ?_⟩
  intro K k Lf Uf Af hL hdvd hreg hadm hker
  exact deltaJ_gaugeRegular_coercive hL hdvd (1 / 500) (by norm_num) hthr (Uf k) hreg (Af k)
    hadm hker

#print axioms gamma0_uniform_over_family

/-! ## §6 — THE ENLARGEMENT IS STRICT, exhibited by compiled witnesses

A hypothesis repair is worth nothing unless the repaired class is genuinely bigger. Two witnesses:
a pure-gauge background (the `α₀ = 0` end) and, more importantly, a **genuinely curved** background
carrying an arbitrarily large `frobSupBond`. Both are on `witL5` (`L μ = 5`: `4 ≤ 5` ✓, `2 ∣ 6` ✓). -/

open AdalyFormal.Balaban.RegularUDomainWitness
  (witL5 frobSupBond_trivialU witA regularU_domain_nonvacuous bondEnergy_witA_pos)
open AdalyFormal.Balaban.RegularUDomainWitnessGeneralU (siteZero)
open AdalyFormal.Balaban.NonFlatBackground (rotM rotElem rotElem_coe frobSq_rotM_sub_one)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem holonomyElem_trivialU)
open AdalyFormal.Balaban.RegularUCurvedWitness
  (curvedU curvedA curvedBond curvedBond_dir tinyU_off curvedU_not_gaugeTransform_of_flat
    curved_regularU_coercivity strict_diff_forces_threshold)

/-- A gauge transformation supported at ONE site: `g` at `x₀`, `1` elsewhere. -/
noncomputable def spikeGauge (g : SU2) (x₀ : PeriodicLatticeSite L) : GaugeFn L :=
  fun x => if x = x₀ then g else 1

theorem spikeGauge_at (g : SU2) (x₀ : PeriodicLatticeSite L) : spikeGauge g x₀ x₀ = g := by
  simp [spikeGauge]

theorem spikeGauge_off (g : SU2) (x₀ : PeriodicLatticeSite L) {x : PeriodicLatticeSite L}
    (h : x ≠ x₀) : spikeGauge g x₀ x = 1 := by
  simp [spikeGauge, h]

/-- A forward shift never returns to its own site once the extent is at least `1`. -/
theorem shift_ne_self (x : PeriodicLatticeSite L) (μ : Fin 3) (h : 1 ≤ L μ) :
    periodicLatticeShift x μ ≠ x := by
  intro heq
  have hc : x μ + 1 = x μ := by
    have := congrFun heq μ
    rwa [periodicLatticeShift, Function.update_self] at this
  have h1 : (1 : Fin (L μ + 1)) = 0 := by
    have h2 := congrArg (fun z : Fin (L μ + 1) => z - x μ) hc
    simpa using h2
  have hval : (1 : Fin (L μ + 1)).val = (0 : Fin (L μ + 1)).val := congrArg Fin.val h1
  rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (show 1 < L μ + 1 by omega)] at hval
  omega

/-- At the spike bond, the gauge-transformed background is EXACTLY `g` (when the background itself
is trivial there). -/
theorem gaugeTransform_spike_at (g : SU2) (x₀ : PeriodicLatticeSite L) (μ : Fin 3)
    (U : PeriodicLinkConfiguration SU2 L) (hne : periodicLatticeShift x₀ μ ≠ x₀)
    (hU : U (x₀, μ) = 1) :
    periodicGaugeTransform (spikeGauge g x₀) U (x₀, μ) = g := by
  show spikeGauge g x₀ x₀ * U (x₀, μ) * (spikeGauge g x₀ (periodicLatticeShift x₀ μ))⁻¹ = g
  rw [spikeGauge_at, spikeGauge_off g x₀ hne, hU]
  simp

/-- **The spike gauge drives `frobSupBond` up to `‖g − 1‖_F`**, no matter how small the background
`U` itself is — the quantitative statement of (M1). -/
theorem frobSupBond_spike_ge (g : SU2) (x₀ : PeriodicLatticeSite L) (μ : Fin 3)
    (U : PeriodicLinkConfiguration SU2 L) (hne : periodicLatticeShift x₀ μ ≠ x₀)
    (hU : U (x₀, μ) = 1) :
    RMapLipschitz.frobNorm ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      ≤ frobSupBond (periodicGaugeTransform (spikeGauge g x₀) U) := by
  have h := frobNorm_le_frobSupBond (periodicGaugeTransform (spikeGauge g x₀) U) (x₀, μ)
  rwa [gaugeTransform_spike_at g x₀ μ U hne hU] at h

/-- `‖rotM 1 − 1‖_F = 2` — the explicit "far from the identity" number. -/
theorem frobNorm_rotM_one : RMapLipschitz.frobNorm (rotM 1 - 1) = 2 := by
  rw [RMapLipschitz.frobNorm, frobSq_rotM_sub_one]
  rw [show (8 : ℝ) * 1 ^ 2 / (1 + 1 ^ 2) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

#print axioms spikeGauge_at
#print axioms spikeGauge_off
#print axioms shift_ne_self
#print axioms gaugeTransform_spike_at
#print axioms frobSupBond_spike_ge
#print axioms frobNorm_rotM_one

/-- **WITNESS 1 (the `α₀ = 0` end).** A background that is `GaugeRegular 0` — PERFECTLY regular in
Bałaban's sense, gauge-equivalent to the identity configuration — whose `frobSupBond` is `2`, i.e.
`1000×` the campaign's own threshold `α₀ = 1/500`. Every `frobSupBond`-hypothesis theorem in this
tree is silent about it; §4 covers it with the BEST possible constant `coercConst 0 = γ₀`. -/
theorem gaugeRegular_strictly_weaker :
    ∃ U : PeriodicLinkConfiguration SU2 witL5,
      GaugeRegular 0 U ∧ (2 : ℝ) ≤ frobSupBond U ∧ ¬ (frobSupBond U ≤ 1 / 500) := by
  refine ⟨periodicGaugeTransform (spikeGauge (rotElem 1) (siteZero witL5)) (trivialU witL5),
    ⟨gaugeInv (spikeGauge (rotElem 1) (siteZero witL5)), ?_⟩, ?_, ?_⟩
  · rw [gaugeTransform_inv, frobSupBond_trivialU]
  · have hne : periodicLatticeShift (siteZero witL5) (1 : Fin 3) ≠ siteZero witL5 :=
      shift_ne_self _ _ (by decide)
    have h := frobSupBond_spike_ge (rotElem 1) (siteZero witL5) (1 : Fin 3) (trivialU witL5)
      hne rfl
    rwa [rotElem_coe, frobNorm_rotM_one] at h
  · intro hcon
    have hne : periodicLatticeShift (siteZero witL5) (1 : Fin 3) ≠ siteZero witL5 :=
      shift_ne_self _ _ (by decide)
    have h := frobSupBond_spike_ge (rotElem 1) (siteZero witL5) (1 : Fin 3) (trivialU witL5)
      hne rfl
    rw [rotElem_coe, frobNorm_rotM_one] at h
    linarith

#print axioms gaugeRegular_strictly_weaker

/-- **The gauged CURVED background.** `curvedU` (a genuine field strength, `RegularUCurvedWitness`)
moved by a one-site gauge spike. -/
noncomputable def gaugedCurvedU : PeriodicLinkConfiguration SU2 witL5 :=
  periodicGaugeTransform (spikeGauge (rotElem 1) (siteZero witL5)) curvedU

/-- The transported admissible field. -/
noncomputable def gaugedCurvedA : Bond witL5 → SuTwo :=
  gaugeActA (spikeGauge (rotElem 1) (siteZero witL5)) curvedA

/-- `curvedU` is `1` on every direction-`1` bond: its single defect bond has direction `0`. -/
theorem curvedU_dir_one (x : PeriodicLatticeSite witL5) : curvedU (x, (1 : Fin 3)) = 1 := by
  refine tinyU_off curvedBond ?_
  intro hcon
  have hsnd := congrArg Prod.snd hcon
  rw [curvedBond_dir] at hsnd
  exact absurd (show (1 : Fin 3) = 0 from hsnd) (by decide)

/-- **WITNESS 2 — the headline instance: a GENUINELY CURVED background, at `frobSupBond = 2`,
satisfying the coercivity with the SAME constant `≥ 1/4000`.**

Conjuncts: (i) `gaugedCurvedU` is not a gauge transform of any flat configuration — the
gauge-INVARIANT curvature statement, so this is not a pure-gauge artifact; (ii) its `frobSupBond` is
`2`, so **no `frobSupBond`-hypothesis theorem in this tree applies to it**; (iii) it IS
`GaugeRegular` at `curvedU`'s own tiny parameter `frobSupBond curvedU`; (iv) the coercivity holds at
the transported field with the numeral `1/4000`, against a STRICTLY POSITIVE bond energy. -/
theorem gaugedCurved_coercivity :
    (∀ (δ : GaugeFn witL5) (V : PeriodicLinkConfiguration SU2 witL5),
        (∀ p : PeriodicLatticePlaquette witL5, holonomyElem V p = 1) →
        gaugedCurvedU ≠ periodicGaugeTransform δ V) ∧
      (2 : ℝ) ≤ frobSupBond gaugedCurvedU ∧
      GaugeRegular (frobSupBond curvedU) gaugedCurvedU ∧
      0 < bondEnergy gaugedCurvedA ∧
      (1 / 4000 : ℝ) * bondEnergy gaugedCurvedA ≤ dstarDQuadForm gaugedCurvedU gaugedCurvedA := by
  obtain ⟨_, hflat, _, _, hadm, hker, _, hbe, hstrict, hge4000, _⟩ := curved_regularU_coercivity
  refine ⟨?_, ?_, ⟨gaugeInv (spikeGauge (rotElem 1) (siteZero witL5)), ?_⟩, ?_, ?_⟩
  · -- (i) gauge-invariant non-flatness, transported through the composition law
    intro δ V hV hcon
    refine hflat (gaugeMul (gaugeInv (spikeGauge (rotElem 1) (siteZero witL5))) δ) V hV ?_
    have : periodicGaugeTransform (gaugeInv (spikeGauge (rotElem 1) (siteZero witL5)))
        gaugedCurvedU = curvedU := by
      rw [gaugedCurvedU, gaugeTransform_inv]
    rw [← this, hcon, gaugeTransform_comp]
  · -- (ii) frobSupBond = 2 at the spike bond
    have hne : periodicLatticeShift (siteZero witL5) (1 : Fin 3) ≠ siteZero witL5 :=
      shift_ne_self _ _ (by decide)
    have h := frobSupBond_spike_ge (rotElem 1) (siteZero witL5) (1 : Fin 3) curvedU hne
      (curvedU_dir_one _)
    rwa [rotElem_coe, frobNorm_rotM_one] at h
  · -- (iii) GaugeRegular at curvedU's own parameter
    rw [gaugedCurvedU, gaugeTransform_inv]
  · -- (iv-a) the transported field has the SAME (positive) energy
    rw [gaugedCurvedA, bondEnergy_gauge]; exact hbe
  · -- (iv-b) the coercivity, via the exact-form transport
    have hthr : 64 * frobSupBond curvedU ^ 2 ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) :=
      le_of_lt (strict_diff_forces_threshold (frobSupBond_nonneg _) hstrict)
    have hinv : periodicGaugeTransform (gaugeInv (spikeGauge (rotElem 1) (siteZero witL5)))
        gaugedCurvedU = curvedU := by rw [gaugedCurvedU, gaugeTransform_inv]
    have hadm' : ∀ y : PeriodicLatticeSite witL5, y ∈ CoarseLattice witL5 2 →
        ∀ x : PeriodicLatticeSite witL5, x ∈ blockOf y 2 →
        ∀ b ∈ staircasePath y x, gaugedCurvedA b = 0 :=
      axialGauge_gauge (spikeGauge (rotElem 1) (siteZero witL5)) 2 curvedA hadm
    have hker' : ∀ b : CoarseBond witL5 2,
        lineCoarseRestrictCov gaugedCurvedU 2 gaugedCurvedA b = 0 :=
      mem_kerQ_gauge (spikeGauge (rotElem 1) (siteZero witL5)) curvedU 2 curvedA hker
    have base := deltaJ_gaugeRegular_coercive_exact (L := witL5) (by decide) (by decide)
      gaugedCurvedU (gaugeInv (spikeGauge (rotElem 1) (siteZero witL5))) gaugedCurvedA
      hadm' hker' (by rw [hinv]; exact hthr) (by rw [hinv]; exact le_of_lt hstrict)
    rw [hinv] at base
    have hbe' : 0 < bondEnergy gaugedCurvedA := by rw [gaugedCurvedA, bondEnergy_gauge]; exact hbe
    nlinarith [base, hge4000, hbe']

#print axioms curvedU_dir_one
#print axioms gaugedCurved_coercivity

/-! ### §6b — THE CENTER WITNESS: (M2) as a compiled theorem

The canonical center-blindness instance both blind gates named. `U ≡ −1` is the CONSTANT center
configuration: adjoint-trivially equal to `U ≡ 1` (`R(−1) = id`), zero field strength, and — on any
torus with `2 ∣ L μ + 1`, i.e. **exactly the compatibility the coercivity theorem already assumes** —
gauge-equivalent to the identity configuration by the parity gauge. Yet `frobSupBond (U ≡ −1) = 2√2`,
the largest value the quantity can take, i.e. `1000×` past the `α₀ = 1/500` threshold. -/

/-- `−1 ∈ SU(2)`: unitary (`(−1)(−1)ᴴ = 1`) and `det(−I₂) = (−1)² = 1`.

**LAW-19 DISCLOSURE (found by the nested validator, recorded rather than silently duplicated).**
`AdalyFormal/HoleHunt/CenterBlindness.lean` lines 89–106 ALREADY defines this element as
`negIMat`/`negI`/`negI_coe`, together with `RMap_negI : RMap negI = LinearMap.id`. It is NOT reused
here for one reason, stated so a reader can overrule it: `HoleHunt/*` is a **concurrent lane's
exclusive write scope** for this dispatch, so importing it would couple this module's build to a file
being edited underneath it. The group-multiplicative facts this module needs
(`negOneElem_mul_self`, `negOneElem_inv`) are not among `CenterBlindness`'s lemmas in any case. When
`HoleHunt/*` is quiescent, this pair should be collapsed onto `negI`. -/
theorem negOne_mem_SU2 :
    (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp
  · simp [Matrix.det_neg]

/-- The nontrivial center element of `SU(2)`. -/
noncomputable def negOneElem : SU2 := ⟨-1, negOne_mem_SU2⟩

theorem negOneElem_coe : ((negOneElem : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

theorem negOneElem_mul_self : negOneElem * negOneElem = (1 : SU2) := by
  apply Subtype.ext
  show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (-1) = 1
  simp

theorem negOneElem_inv : negOneElem⁻¹ = negOneElem :=
  inv_eq_of_mul_eq_one_left negOneElem_mul_self

/-- `‖(−1) − 1‖_F = 2√2` — the maximal Frobenius distance from the identity inside `SU(2)`. -/
theorem frobNorm_negOne_sub_one :
    RMapLipschitz.frobNorm ((-1 : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 2 * Real.sqrt 2 := by
  have h8 : RMapLipschitz.frobSq ((-1 : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 8 := by
    simp [RMapLipschitz.frobSq, Matrix.one_apply]
    norm_num
  rw [RMapLipschitz.frobNorm, h8, show (8 : ℝ) = 2 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- **The constant center configuration** `U ≡ −1`. -/
noncomputable def centerU (L : PeriodicLatticeExtent) : PeriodicLinkConfiguration SU2 L :=
  fun _ => negOneElem

/-- **The parity gauge** `γ(x) = (−1)^{|x|}`, written as `1` on even-coordinate-sum sites and `−1`
on odd ones. This is a genuine gauge transformation only because the extents are even, which is
exactly `hdvd`. -/
noncomputable def parityGauge (L : PeriodicLatticeExtent) : GaugeFn L :=
  fun x => if (∑ μ : Fin 3, (x μ).val) % 2 = 0 then 1 else negOneElem

/-- Parity flips across one forward step in `Fin n` when `n` is EVEN — including at the wraparound,
where `n − 1` (odd) maps to `0` (even). This is the whole content of the even-torus hypothesis. -/
theorem parity_flip {n : ℕ} (hn : 2 ∣ n) (v : ℕ) (hv : v < n) :
    ((v + 1) % n) % 2 = 0 ↔ v % 2 ≠ 0 := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hv) with h | h
  · subst h; rw [Nat.mod_self]; omega
  · rw [Nat.mod_eq_of_lt h]; omega

/-- The coordinate sum's parity flips across every bond, on an even torus. -/
theorem coordSum_parity_flip (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((∑ ν : Fin 3, ((periodicLatticeShift x μ) ν).val) % 2 = 0)
      ↔ ((∑ ν : Fin 3, (x ν).val) % 2 ≠ 0) := by
  have hone : ((1 : Fin (L μ + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by have := hdvd μ; omega)
  have hval : ((periodicLatticeShift x μ) μ).val = ((x μ).val + 1) % (L μ + 1) := by
    rw [periodicLatticeShift, Function.update_self, Fin.val_add, hone]
  have hoff : ∀ ν : Fin 3, ν ≠ μ → ((periodicLatticeShift x μ) ν).val = (x ν).val := by
    intro ν hν
    rw [periodicLatticeShift, Function.update_of_ne hν]
  have hsplit1 : (∑ ν : Fin 3, ((periodicLatticeShift x μ) ν).val)
      = ((periodicLatticeShift x μ) μ).val
        + ∑ ν ∈ Finset.univ.erase μ, ((periodicLatticeShift x μ) ν).val :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
  have hsplit2 : (∑ ν : Fin 3, (x ν).val)
      = (x μ).val + ∑ ν ∈ Finset.univ.erase μ, (x ν).val :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
  have heq : (∑ ν ∈ Finset.univ.erase μ, ((periodicLatticeShift x μ) ν).val)
      = ∑ ν ∈ Finset.univ.erase μ, (x ν).val :=
    Finset.sum_congr rfl (fun ν hν => hoff ν (Finset.ne_of_mem_erase hν))
  have hflip := parity_flip (hdvd μ) (x μ).val (x μ).isLt
  rw [hsplit1, hsplit2, heq, hval]
  set w := ((x μ).val + 1) % (L μ + 1) with hw
  set v := (x μ).val with hv
  set S := ∑ ν ∈ Finset.univ.erase μ, (x ν).val with hS
  omega

/-- **THE CENTER WITNESS.** On any torus with `2 ∣ L μ + 1`, the constant center configuration
`U ≡ −1` is gauge-equivalent to the IDENTITY configuration — hence `GaugeRegular 0`, perfectly
regular in Bałaban's sense at every `α₀ ≥ 0` — while `frobSupBond (U ≡ −1) = 2√2 > 1/500`. This is
(M2) as a theorem: `frobSupBond` rejects a configuration Bałaban's condition accepts, and one on
which the coercivity form is LITERALLY the `U = 1` form (`R(−1) = id`). -/
theorem centerU_gaugeRegular_zero (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    periodicGaugeTransform (parityGauge L) (centerU L) = trivialU L := by
  funext b
  show parityGauge L b.1 * negOneElem * (parityGauge L (periodicLatticeShift b.1 b.2))⁻¹ = 1
  have hflip := coordSum_parity_flip hdvd b.1 b.2
  by_cases hpar : (∑ ν : Fin 3, (b.1 ν).val) % 2 = 0
  · have h2 : ((∑ ν : Fin 3, ((periodicLatticeShift b.1 b.2) ν).val) % 2 = 0) = False := by
      simp only [eq_iff_iff, iff_false]
      exact fun hc => (hflip.mp hc) hpar
    rw [parityGauge, parityGauge, if_pos hpar]
    simp only [h2, if_false]
    rw [negOneElem_inv, one_mul, negOneElem_mul_self]
  · have h2 : (∑ ν : Fin 3, ((periodicLatticeShift b.1 b.2) ν).val) % 2 = 0 := hflip.mpr hpar
    rw [parityGauge, parityGauge, if_neg hpar, if_pos h2]
    rw [inv_one, mul_one, negOneElem_mul_self]

theorem centerU_is_gaugeRegular (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    GaugeRegular 0 (centerU L) :=
  ⟨parityGauge L, by
    rw [centerU_gaugeRegular_zero hdvd, AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU]⟩

/-- `frobSupBond (U ≡ −1) = 2√2` — computed, not estimated. -/
theorem frobSupBond_centerU : frobSupBond (centerU L) = 2 * Real.sqrt 2 := by
  unfold frobSupBond centerU
  rw [Finset.sup'_const]
  exact frobNorm_negOne_sub_one

/-- **(M2) AS A SINGLE STATEMENT.** The two hypotheses disagree on the constant center
configuration: Bałaban's accepts it at every threshold, the campaign's proxy rejects it by a factor
of `1000` at the campaign's own `α₀ = 1/500`. -/
theorem center_separates_hypotheses (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    GaugeRegular 0 (centerU L) ∧ ¬ (frobSupBond (centerU L) ≤ 1 / 500) := by
  refine ⟨centerU_is_gaugeRegular hdvd, ?_⟩
  rw [frobSupBond_centerU]
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by norm_num)
  intro hcon
  linarith

#print axioms negOne_mem_SU2
#print axioms negOneElem_coe
#print axioms negOneElem_mul_self
#print axioms negOneElem_inv
#print axioms frobNorm_negOne_sub_one
#print axioms parity_flip
#print axioms coordSum_parity_flip
#print axioms centerU_gaugeRegular_zero
#print axioms centerU_is_gaugeRegular
#print axioms frobSupBond_centerU
#print axioms center_separates_hypotheses

/-! ## §7 — JUNK ATTACKS on this module's own statements

Run BEFORE anything is built above them, per the dispatch. Each item is a compiled theorem, not a
remark: a degenerate point that survives is a defect, and three reached the top-level milestone this
week. -/

/-- **JUNK 1 — `α₀ = 0` is the strongest hypothesis, and the constant there is `γ₀` itself**, not
`0`. So the theorem is not silently vacuous at the sharp end. -/
theorem coercConst_zero : coercConst 0 = 1 / 1728 := by
  unfold coercConst
  have h1 : gammaZeroLit - 64 * (0 : ℝ) ^ 2 = gammaZeroLit := by norm_num
  have h2 : 4 * Real.sqrt 2 * (0 : ℝ) = 0 := by norm_num
  rw [h1, h2, sub_zero, Real.sq_sqrt (by rw [gammaZeroLit_eq]; norm_num), gammaZeroLit_eq]

/-- **JUNK 2 — the `√(negative) = 0` trap FIRES on the unguarded constant.** At `α = 1` the
threshold is violated by a factor of `110000`, yet `coercConst 1 = 32 > 0`: positivity of the
squared expression is NOT a smallness certificate. This is why §4 carries `96α² ≤ γ₀` (which forces
the sqrt argument nonneg) rather than `0 < coercConst α`. -/
theorem coercConst_trap_fires : gammaZeroLit < 64 * (1 : ℝ) ^ 2 ∧ 0 < coercConst 1 := by
  refine ⟨by rw [gammaZeroLit_eq]; norm_num, ?_⟩
  rw [coercConst, Real.sqrt_eq_zero_of_nonpos (by rw [gammaZeroLit_eq]; norm_num)]
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

/-- **JUNK 3 — `A = 0` makes the conclusion trivially true**, so the theorem needs a nonzero-energy
witness to have content. `gaugedCurved_coercivity` supplies one (`0 < bondEnergy gaugedCurvedA`);
this records the degeneracy explicitly so nobody mistakes the general statement for content. -/
theorem coercivity_trivial_at_zero_field (U : PeriodicLinkConfiguration SU2 L) (α₀ : ℝ) :
    coercConst α₀ * bondEnergy (0 : Bond L → SuTwo) ≤ dstarDQuadForm U 0 := by
  have h0 : bondEnergy (0 : Bond L → SuTwo) = 0 := by
    unfold bondEnergy; simp
  rw [h0, mul_zero]
  exact dstarDQuadForm_nonneg U 0

/-- `frobSq M = 0 → M = 0`. Not previously in the tree (checked: no `frobSq_eq_zero`), so it is
proved here from `frobSq`'s own four-term definition. -/
theorem matrix_eq_zero_of_frobSq_zero {M : Matrix (Fin 2) (Fin 2) ℂ}
    (h : RMapLipschitz.frobSq M = 0) : M = 0 := by
  unfold RMapLipschitz.frobSq at h
  have h00 := Complex.normSq_nonneg (M 0 0)
  have h01 := Complex.normSq_nonneg (M 0 1)
  have h10 := Complex.normSq_nonneg (M 1 0)
  have h11 := Complex.normSq_nonneg (M 1 1)
  have e00 : M 0 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e01 : M 0 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e10 : M 1 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  have e11 : M 1 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11

/-- `frobSupBond U ≤ 0` pins `U` to the identity configuration. -/
theorem eq_trivialU_of_frobSupBond_le_zero {U : PeriodicLinkConfiguration SU2 L}
    (h : frobSupBond U ≤ 0) : U = trivialU L := by
  funext b
  have h1 := frobNorm_le_frobSupBond U b
  have h2 : RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0 :=
    le_antisymm (le_trans h1 h) (RMapLipschitz.frobNorm_nonneg _)
  have h3 : RMapLipschitz.frobSq ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) = 0 := by
    have := RMapLipschitz.frobNorm_sq ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    rw [h2] at this
    linarith [this]
  have h4 := matrix_eq_zero_of_frobSq_zero h3
  apply Subtype.ext
  have : (U b : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have := sub_eq_zero.mp h4
    exact this
  rw [this]
  rfl

/-- **JUNK 4 — `GaugeRegular` IS A GENUINE RESTRICTION.** It is not satisfied by every background:
`curvedU` is not `GaugeRegular 0`, because `GaugeRegular 0` forces the configuration to be a pure
gauge, and `curvedU` is provably not a gauge transform of any flat field. Without this, the whole
§4 hypothesis class could have been everything. -/
theorem not_gaugeRegular_zero_curvedU : ¬ GaugeRegular 0 curvedU := by
  rintro ⟨γ, hγ⟩
  have hV : periodicGaugeTransform γ curvedU = trivialU witL5 :=
    eq_trivialU_of_frobSupBond_le_zero hγ
  refine curvedU_not_gaugeTransform_of_flat (gaugeInv γ) (trivialU witL5)
    (fun p => holonomyElem_trivialU p) ?_
  rw [← hV, gaugeTransform_inv]

/-- **JUNK 5 — `Gamma0ScaleUniform` is not vacuously satisfied.** Instantiated at the one-point
index type with the gauged CURVED background, its conclusion is a strictly positive lower bound on a
strictly positive quantity — not `0 ≤ 0`. -/
theorem gamma0_uniform_nonvacuous :
    0 < coercConst (frobSupBond curvedU) * bondEnergy gaugedCurvedA ∧
      coercConst (frobSupBond curvedU) * bondEnergy gaugedCurvedA
        ≤ dstarDQuadForm gaugedCurvedU gaugedCurvedA := by
  obtain ⟨_, _, _, _, hadm, hker, _, hbe, hstrict, _, _⟩ := curved_regularU_coercivity
  have hthr : 64 * frobSupBond curvedU ^ 2 ≤ (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) :=
    le_of_lt (strict_diff_forces_threshold (frobSupBond_nonneg _) hstrict)
  have hinv : periodicGaugeTransform (gaugeInv (spikeGauge (rotElem 1) (siteZero witL5)))
      gaugedCurvedU = curvedU := by rw [gaugedCurvedU, gaugeTransform_inv]
  have hadm' : ∀ y : PeriodicLatticeSite witL5, y ∈ CoarseLattice witL5 2 →
      ∀ x : PeriodicLatticeSite witL5, x ∈ blockOf y 2 →
      ∀ b ∈ staircasePath y x, gaugedCurvedA b = 0 :=
    axialGauge_gauge (spikeGauge (rotElem 1) (siteZero witL5)) 2 curvedA hadm
  have hker' : ∀ b : CoarseBond witL5 2,
      lineCoarseRestrictCov gaugedCurvedU 2 gaugedCurvedA b = 0 :=
    mem_kerQ_gauge (spikeGauge (rotElem 1) (siteZero witL5)) curvedU 2 curvedA hker
  have base := deltaJ_gaugeRegular_coercive_exact (L := witL5) (by decide) (by decide)
    gaugedCurvedU (gaugeInv (spikeGauge (rotElem 1) (siteZero witL5))) gaugedCurvedA
    hadm' hker' (by rw [hinv]; exact hthr) (by rw [hinv]; exact le_of_lt hstrict)
  rw [hinv] at base
  have hbe' : 0 < bondEnergy gaugedCurvedA := by rw [gaugedCurvedA, bondEnergy_gauge]; exact hbe
  have hcc : 0 < coercConst (frobSupBond curvedU) := by
    unfold coercConst
    exact pow_pos hstrict 2
  exact ⟨mul_pos hcc hbe', base⟩

/-- **JUNK 6 — `gamma0_uniform_over_family`'s OWN `∀ K` binder, instantiated at a CONCRETE nonempty
index, with a background OUTSIDE the `frobSupBond`-hypothesis class.**

The nested validator noted that `gamma0_uniform_nonvacuous` proves a parallel fact via the exact-form
transport rather than exercising `Gamma0ScaleUniform` itself. This closes that: `K = Unit`,
`Lf = witL5`, the background is the spike-gauged identity configuration (`GaugeRegular 0`, yet
`frobSupBond = 2`), the field is the gauge-transport of `RegularUDomainWitness.witA`, and the
delivered inequality has a STRICTLY POSITIVE left-hand side. So the `∀ K` form is not vacuous at a
populated index, and the instance it is populated at is one no `frobSupBond`-hypothesis theorem
reaches. -/
theorem gamma0_uniform_at_unit_index :
    0 < bondEnergy (gaugeActA (spikeGauge (rotElem 1) (siteZero witL5)) witA) ∧
      coercConst (1 / 500) * bondEnergy (gaugeActA (spikeGauge (rotElem 1) (siteZero witL5)) witA)
        ≤ dstarDQuadForm
            (periodicGaugeTransform (spikeGauge (rotElem 1) (siteZero witL5)) (trivialU witL5))
            (gaugeActA (spikeGauge (rotElem 1) (siteZero witL5)) witA) := by
  obtain ⟨_, _, huniv⟩ := gamma0_uniform_over_family
  obtain ⟨hax, hker, _⟩ := regularU_domain_nonvacuous
  refine ⟨by rw [bondEnergy_gauge]; exact bondEnergy_witA_pos, ?_⟩
  exact huniv Unit () (fun _ => witL5)
    (fun _ => periodicGaugeTransform (spikeGauge (rotElem 1) (siteZero witL5)) (trivialU witL5))
    (fun _ => gaugeActA (spikeGauge (rotElem 1) (siteZero witL5)) witA)
    (by decide) (by decide)
    ⟨gaugeInv (spikeGauge (rotElem 1) (siteZero witL5)), by
      rw [gaugeTransform_inv, frobSupBond_trivialU]; norm_num⟩
    (axialGauge_gauge (spikeGauge (rotElem 1) (siteZero witL5)) 2 witA hax)
    (mem_kerQ_gauge (spikeGauge (rotElem 1) (siteZero witL5)) (trivialU witL5) 2 witA hker)

#print axioms gamma0_uniform_at_unit_index
#print axioms coercConst_zero
#print axioms coercConst_trap_fires
#print axioms coercivity_trivial_at_zero_field
#print axioms matrix_eq_zero_of_frobSq_zero
#print axioms eq_trivialU_of_frobSupBond_le_zero
#print axioms not_gaugeRegular_zero_curvedU
#print axioms gamma0_uniform_nonvacuous

end AdalyFormal.Balaban.AlphaAnalyticity
