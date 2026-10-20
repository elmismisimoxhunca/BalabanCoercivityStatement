/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKU
import AdalyFormal.Balaban.CovariantHj
import AdalyFormal.Balaban.SuTwoInner
import AdalyFormal.Balaban.RMapLipschitz
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

/-!
# `RegularUPerturbation.lean` — the FIRST single-scale perturbation brick for the regular-`U`,
`k`-uniform coercivity of the leading covariant term `deltaJ(U) = ‖D_U A‖²`

## ⚠ NOMENCLATURE (F6, 2026-07-26) — `deltaJ(U)` HERE IS THE CURL ENERGY,
**NOT** THE SCHUR COMPLEMENT

"`deltaJ(U)`" in this module's prose and declaration names (`deltaJ_sub_eq_inner`,
`abs_deltaJ_sub_le`, `abs_deltaJ_sub_L2_le`, `abs_deltaJ_sub_L2_le_sup`) is a **local nickname** for

    CovariantHj.dstarDQuadForm U A
      := covPlaqInner (curlValueCovariant U A) (curlValueCovariant U A)   =   ‖∂^U A‖²

— the covariant curl / `D_U^*D_U` energy (§1's `dstarDQuadForm_eq_norm_sq` is the
identity), and it is `dstarDQuadForm`, not any `deltaJ…` declaration, that appears in every Lean
statement here.

It is a **DIFFERENT DECLARATION** from `CovariantHjFaithful.deltaJQuadFormCovFaithful`, the Schur
complement / minimized curl energy standing for CMP99b (3.156)'s `Δ_j`. The tree proves
`CStarDeltaKCCoercive.deltaJQuadFormCovFaithful_le_dstarDQuadForm`
(`deltaJQuadFormCovFaithful ≤ dstarDQuadForm`) — the direction that blocks transfer — and
`deltaJQuadFormCovFaithful_eq_zero_of_mem_V` makes the smaller object identically zero on `V`.
Consequently the perturbation bounds proved in this module are estimates on the CURL ENERGY's
`U`-sensitivity, not on the Schur complement's. Filed by the level-collapse sweep as F6
(`compute/level_collapse_sweep/FINDINGS.md`). Statements clean, nickname corrected; no declaration
renamed (a rename is a semantic-risk edit while lanes are live).

**This is the OPEN FRONTIER (do NOT read this file as proving regular-`U` coercivity).** The
regular-`U`, `k`-uniform lower bound `C*Δ_kC ≥ γ₀` is Bałaban's asserted-but-unwritten (for the
`C`-chain) result; three de-correlated wall-hunts (`compute/regularU_walltest/`,
`compute/sol_regularU_gate/`, `compute/kimi_regularU_gate/`) classify it as a DEFINED METHOD with the
one un-displayed inequality being the `C`-chain sensitivity bound
`‖C(U)*Δ_k(U)C(U) − C(1)*Δ_k(1)C(1)‖ ≤ C(d,L,M)·Mα₀` (Kimi's `[M1]`). The multi-scale random-walk
expansion (CMP96 §B (2.141), CMP99b (3.108)) that delivers `k`-uniformity ITERATES a single-scale
perturbation base estimate. **This file builds that base estimate, in Lean, axiom-clean, on the
genuinely-`U`-dependent leading operator `DeltaKU.curlValueCovariant` (the covariant curl `D_U^1`).**

## The source object (CHARACTERIZE-FIRST, image-pinned)

- The single-scale perturbation in Bałaban is the OPERATOR identity (**CMP99b (3.82), printed
  p.407**, this lane's own 600-dpi read `compute/regularU_frontier/CMP99b_p407-19.png`):
  `Δ_a(U'U) = D*_{U'U}D_{U'U} + Δ'(U'U) + D_{U'U}R(U'U)D*_{U'U} + Q*(U'U)aQ(U'U)
            = Δ_a(U) − V₃(A) − P₁(A) − P₂(A) = Δ_a(U) − V(A)`,
  where `V₃(A)` is "a local differential operator of the first order" (verbatim, p.407) — so the
  single-scale perturbation is FIRST ORDER. The Neumann factorization is (3.84)
  `Δ_a(U'U) = (I − V(A)G(U))Δ_a(U)` and the smallness is (3.85)
  `|(V(A)G(U)J)(b)| ≤ O(1)α₁ e^{−(1/2)δ₀d(y,y')}|J|`, hence "V(A)G(U) is a small operator in supremum
  norm", giving the convergent series (3.86) `G(U'U) = G(U)(I − V(A)G(U))⁻¹` for α₁ small. **Base
  point:** this lane takes `U := trivialU` (`= 1`), i.e. exactly Bałaban's `U=1` base case
  (Corollary 3.5, p.407: "`U'` in the domain (3.37) with `U = 1`"), and builds the `D*_{U'U}D_{U'U}`
  summand's realization of `(3.82)`'s first-order perturbation. Its content: the deviation of the
  covariant object from its `U=1` value is first order in the per-bond holonomy deviation
  `RMap(U b) − id`, with a GEOMETRIC (`d,L`-only, NO `k`) constant.
- The leading coercive term at `U=1` is CMP96 (2.128) `deltaJ(1)`; for regular `U` it is the
  covariant version, `deltaJ(U) = ‖D_U A‖²`, `D_U = curlValueCovariant U` (CMP99b (3.4)/(3.10),
  `CovariantHj.dstarDQuadForm`).

## What is delivered (all sorry-free, `#print axioms` clean below each)

1. **§2 — the exact per-plaquette DRIFT IDENTITY** (`curlDrift_apply`): the single-scale
   perturbation `D_U A − D_1 A` is EXACTLY, at every plaquette, the difference of two per-bond
   holonomy-deviation terms `(RMap(U b) − id)·A(neighbour)`. This is the "first term of the Neumann
   series" made literal on the covariant curl: first order in `RMap(U b) − id`, no `k`.
2. **§3 — consistency** (`curlDrift_trivialU`): the drift is identically `0` at `U = 1`.
3. **§4 — the exact PERTURBATION IDENTITY** (`deltaJ_sub_eq_inner`):
   `deltaJ(U)A − deltaJ(1)A = ⟪D_U A − D_1 A, D_U A + D_1 A⟫_{L²}` — the linearization identity the
   multi-scale expansion iterates (`‖a‖² − ‖b‖² = ⟪a−b, a+b⟫`, exact).
4. **§5 — THE SINGLE-SCALE PERTURBATION BOUND** (`abs_deltaJ_sub_le`):
   `|deltaJ(U)A − deltaJ(1)A| ≤ ‖D_U A − D_1 A‖·(√deltaJ(U)A + √deltaJ(1)A)`
   (Cauchy–Schwarz + triangle). The dispatch's `|deltaJ(U) − deltaJ(1)| ≤ (drift)·(energy)` shape,
   with `drift = ‖D_U A − D_1 A‖` (the quantity §2 identifies as first-order-in-holonomy) and
   `energy = √deltaJ(U)A + √deltaJ(1)A`.
5. **§6 — the GEOMETRIC per-bond constant** (`norm_RMap_sub_self_le_two`): `‖RMap(U b)X − X‖ ≤ 2‖X‖`
   for EVERY `U`, purely from `RMap`'s isometry (`SuTwoInner`) — the `d,L`-only, `k`-independent,
   `U`-independent per-step constant (`= 2`) that the source's per-walk bound carries. This is the
   crude (uniform) form; the SHARP `‖U−1‖`-smallness form is the NAMED residual below.

## `[RMAP-LIP-U1]` — CLOSED (2026-07-26, `RMapLipschitz.lean`)

The SHARP per-bond bound is now PROVED, axiom-clean, as
`RMapLipschitz.norm_RMap_sub_self_le : ‖RMap(U)X − X‖ ≤ 2·frobNorm((U:Matrix) − 1)·‖X‖`,
where `frobNorm M = √(Σ|Mᵢⱼ|²)` is the Frobenius norm of the FULL matrix `U − 1`. This gives the
drift the genuine `‖U−1‖` SMALLNESS (vanishes at `U = 1`; source `‖V(A)G‖ = O(α₁)`, (3.85)). The
construction avoids the `SuTwo` matrix-norm instance diamond flagged in `SuTwoInner.lean` by using a
PLAIN `frobSq M := Σ|Mᵢⱼ|²` and the commutator identity `RMap(U)X − X = (V·X − X·V)·Uᴴ`, `V = U−1`;
the three matrix-analysis facts (unitary invariance, `|a−b|²≤2|a|²+2|b|²`, Cauchy–Schwarz
submultiplicativity) are proved by explicit `2×2` `Complex.normSq` algebra. §7 below chains it to
the per-plaquette drift. §6's crude constant-`2` uniform bound is retained (needs no `U`-smallness).

**`[L2-AGG]` — CLOSED (2026-07-26, §8–§12 below).** The per-plaquette bound (§7) is now aggregated
into the `L²`-drift norm, axiom-clean, as
`norm_curlDrift_L2_le_sup : √(plaqEnergy (curlDrift U A)) ≤ 4·√2·(sup_b frobNorm(U b − 1))·√(bondEnergy A)`
and chained onto §4/§5 as
`abs_deltaJ_sub_L2_le_sup : |deltaJ(U)A − deltaJ(1)A| ≤ 4·√2·α₁·√(bondEnergy A)·(√deltaJ(U)A + √deltaJ(1)A)`,
`α₁ = sup_b frobNorm(U b − 1)`. The constant `C = 4·√2` is EXPLICIT, `k`-INDEPENDENT, and in fact
`L`-independent: it is `√(16·(d−1))` at `d = 3` (`Fin 3`), where `d − 1 = 2` is the plaquette→bond
incidence multiplicity — each bond in direction `ρ` is neighbour-1 of exactly `#{μ : μ < ρ} ≤ d−1`
plaquettes and neighbour-2 of exactly `#{ν : ν > ρ} ≤ d−1`, a lattice-combinatorics count with NO
scale `k` and NO lattice size `L`. See §10 (`dir_proj{1,2}_fiber_card_le`, the concrete `d = 3`
multiplicity, `decide`-verified) and the general-`d` note there.

**Remaining (NOT this brick):** the multi-scale random-walk iteration (CMP96 §B (2.141), CMP99b
(3.108)) that turns this single-scale base estimate into `k`-uniformity, and the `C`-chain reduction
(3.156)–(3.158) — the large open program (unchanged).

## Scope honesty

This is ONE single-scale brick of a LARGE program. It does NOT prove coercivity, does NOT iterate to
`k`-uniformity (that is the multi-scale random-walk expansion, entirely unbuilt), and does NOT touch
the `C`-chain reduction (3.156)–(3.158). It supplies the base perturbation estimate those steps
consume. LAW-19: every ingredient (`curlValueCovariant`, `dstarDQuadForm`, `covPlaqInner`, `RMap`,
`hsInner`/`inner`) is imported and reused; nothing is re-derived.
-/

namespace AdalyFormal.Balaban.RegularUPerturbation

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.CovariantHj
  AdalyFormal.Balaban.CovariantHjMinimizer AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.DeltaKU

variable {L : PeriodicLatticeExtent}

/-! ## §0 — the plaquette `L²` space (`PiLp 2`), with `covPlaqInner` as its genuine inner product

Fresh `def` type (mirroring `DeltaKUnified.BFL2`) so anonymous instance search uses Mathlib's
canonical `PiLp.innerProductSpace` and never a competing custom instance. -/

/-- **`L²`-of-plaquettes carrier**: `PiLp 2 (fun _ => 𝔰𝔲(2))`. `abbrev` (reducible) so it inherits
Mathlib's canonical `PiLp.innerProductSpace` and its elements index like functions; no custom
instance is registered on plaquette-`PiLp` anywhere, so there is no diamond to guard against. -/
abbrev PlaqL2 (L : PeriodicLatticeExtent) : Type :=
  PiLp 2 (fun _ : PeriodicLatticePlaquette L => SuTwo)

/-- The `LinearEquiv` between `PlaqL2 L` and the bare function type (`WithLp.linearEquiv`, LAW-19
transport primitive). -/
noncomputable def plaqL2Equiv : PlaqL2 L ≃ₗ[ℝ] (PeriodicLatticePlaquette L → SuTwo) :=
  WithLp.linearEquiv 2 ℝ (PeriodicLatticePlaquette L → SuTwo)

/-- **Promote a bare plaquette function into the `L²` carrier.** -/
noncomputable def toPlaqL2 (f : PeriodicLatticePlaquette L → SuTwo) : PlaqL2 L :=
  (plaqL2Equiv (L := L)).symm f

@[simp] theorem toPlaqL2_apply (f : PeriodicLatticePlaquette L → SuTwo)
    (p : PeriodicLatticePlaquette L) : toPlaqL2 f p = f p := rfl

theorem toPlaqL2_sub (f g : PeriodicLatticePlaquette L → SuTwo) :
    toPlaqL2 (f - g) = toPlaqL2 f - toPlaqL2 g := by
  unfold toPlaqL2; exact map_sub _ f g

theorem toPlaqL2_add (f g : PeriodicLatticePlaquette L → SuTwo) :
    toPlaqL2 (f + g) = toPlaqL2 f + toPlaqL2 g := by
  unfold toPlaqL2; exact map_add _ f g

/-- **`covPlaqInner` IS the `L²` inner product** — the bridge that hands the entire Hilbert-space
toolkit (Cauchy–Schwarz, the norm) to `dstarDQuadForm`. -/
theorem covPlaqInner_eq_inner (A B : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner A B = inner ℝ (toPlaqL2 A) (toPlaqL2 B) := by
  rw [PiLp.inner_apply]
  unfold covPlaqInner
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [toPlaqL2_apply, toPlaqL2_apply, inner_eq_hsInner]

#print axioms toPlaqL2_apply
#print axioms covPlaqInner_eq_inner

/-! ## §1 — `deltaJ(U) = ‖D_U A‖²_{L²}` -/

/-- **The leading covariant term as a squared `L²` norm.** `deltaJ(U)A = ‖toPlaqL2 (D_U A)‖²`. -/
theorem dstarDQuadForm_eq_norm_sq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    dstarDQuadForm U A = ‖toPlaqL2 (curlValueCovariant U A)‖ ^ 2 := by
  unfold dstarDQuadForm
  rw [covPlaqInner_eq_inner, real_inner_self_eq_norm_sq]

#print axioms dstarDQuadForm_eq_norm_sq

/-! ## §2 — the exact per-plaquette DRIFT IDENTITY (first order in `RMap(U b) − id`) -/

/-- **The single-scale drift** `D_U A − D_1 A`, as a bare plaquette function. -/
noncomputable def curlDrift
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : PeriodicLatticePlaquette L → SuTwo :=
  curlValueCovariant U A - curlValueCovariant (trivialU L) A

/-- **THE DRIFT IDENTITY.** At every plaquette `p = (x, μ<ν)`, the single-scale perturbation of the
covariant curl is EXACTLY the difference of two per-bond holonomy-deviation terms:
`(RMap(U(x,μ)) − id) A(shift_μ x, ν) − (RMap(U(x,ν)) − id) A(shift_ν x, μ)`.
First order in the holonomy deviations `RMap(U b) − id`, no `k` — the covariant-curl realization of
the Neumann first term (CMP99b (3.85)–(3.86)). -/
theorem curlDrift_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    curlDrift U A p =
      (RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) -
        A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) -
      (RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) -
        A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) := by
  unfold curlDrift
  rw [Pi.sub_apply, curlValueCovariant, curlValueCovariant_trivialU]
  abel

#print axioms curlDrift_apply

/-! ## §3 — consistency: the drift vanishes at `U = 1` -/

theorem curlDrift_trivialU (A : Bond L → SuTwo) :
    curlDrift (trivialU L) A = 0 := by
  funext p
  rw [curlDrift_apply]
  simp only [trivialU, RMap_one, LinearMap.id_coe, id_eq, Pi.zero_apply]
  abel

#print axioms curlDrift_trivialU

/-! ## §4 — the exact PERTURBATION IDENTITY -/

/-- **THE PERTURBATION IDENTITY.** `deltaJ(U)A − deltaJ(1)A = ⟪D_U A − D_1 A, D_U A + D_1 A⟫_{L²}` —
exact (`‖a‖²−‖b‖² = ⟪a−b, a+b⟫` in a real inner-product space). The linearization the multi-scale
expansion iterates: the difference of the two single-scale forms is the pairing of the drift with the
sum of the two curls. -/
theorem deltaJ_sub_eq_inner
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    dstarDQuadForm U A - dstarDQuadForm (trivialU L) A =
      inner ℝ (toPlaqL2 (curlValueCovariant U A) - toPlaqL2 (curlValueCovariant (trivialU L) A))
        (toPlaqL2 (curlValueCovariant U A) + toPlaqL2 (curlValueCovariant (trivialU L) A)) := by
  set a := toPlaqL2 (curlValueCovariant U A)
  set b := toPlaqL2 (curlValueCovariant (trivialU L) A)
  rw [dstarDQuadForm_eq_norm_sq, dstarDQuadForm_eq_norm_sq,
    inner_sub_left, inner_add_right, inner_add_right,
    real_inner_comm b a, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

#print axioms deltaJ_sub_eq_inner

/-! ## §5 — THE SINGLE-SCALE PERTURBATION BOUND (the deliverable of the dispatch) -/

/-- **THE SINGLE-SCALE PERTURBATION BOUND.**
`|deltaJ(U)A − deltaJ(1)A| ≤ ‖D_U A − D_1 A‖_{L²} · (√deltaJ(U)A + √deltaJ(1)A)`.
The `(drift)·(energy)` shape the dispatch requests: `drift = ‖D_U A − D_1 A‖_{L²}` (the quantity §2
identifies as first order in the per-bond holonomy deviations `RMap(U b) − id`), and
`energy = ‖D_U A‖_{L²} + ‖D_1 A‖_{L²} = √deltaJ(U)A + √deltaJ(1)A`. Uniform in the RG step `k` (a
single scale carries no `k`). -/
theorem abs_deltaJ_sub_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    |dstarDQuadForm U A - dstarDQuadForm (trivialU L) A| ≤
      ‖toPlaqL2 (curlValueCovariant U A) - toPlaqL2 (curlValueCovariant (trivialU L) A)‖ *
        (Real.sqrt (dstarDQuadForm U A) + Real.sqrt (dstarDQuadForm (trivialU L) A)) := by
  set a := toPlaqL2 (curlValueCovariant U A) with ha
  set b := toPlaqL2 (curlValueCovariant (trivialU L) A) with hb
  rw [deltaJ_sub_eq_inner]
  -- Cauchy–Schwarz then triangle inequality on the second factor.
  calc |inner ℝ (a - b) (a + b)|
      ≤ ‖a - b‖ * ‖a + b‖ := abs_real_inner_le_norm (a - b) (a + b)
    _ ≤ ‖a - b‖ * (Real.sqrt (dstarDQuadForm U A) + Real.sqrt (dstarDQuadForm (trivialU L) A)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have hUa : Real.sqrt (dstarDQuadForm U A) = ‖a‖ := by
          rw [dstarDQuadForm_eq_norm_sq, ← ha, Real.sqrt_sq (norm_nonneg _)]
        have hUb : Real.sqrt (dstarDQuadForm (trivialU L) A) = ‖b‖ := by
          rw [dstarDQuadForm_eq_norm_sq, ← hb, Real.sqrt_sq (norm_nonneg _)]
        rw [hUa, hUb]
        exact norm_add_le a b

#print axioms abs_deltaJ_sub_le

/-! ## §6 — the GEOMETRIC per-bond constant (crude, uniform; sharp `‖U−1‖` form is `[RMAP-LIP-U1]`) -/

/-- **`‖RMap(U b)X − X‖ ≤ 2‖X‖` for EVERY `U`.** The per-bond single-scale drift is controlled by a
purely GEOMETRIC constant (`= 2`), independent of the RG step `k`, the scale, and `U` — the qualitative
content of the source's "the per-walk constant `O(1)` depends on `d, L` only" (CMP99b (3.108)) at the
single-bond level, coming entirely from `RMap`'s isometry (`SuTwoInner`). The SHARP form with
`‖U−1‖` smallness is now `RMapLipschitz.norm_RMap_sub_self_le` (`[RMAP-LIP-U1]`, CLOSED — §7). -/
theorem norm_RMap_sub_self_le_two (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    ‖RMap U X - X‖ ≤ 2 * ‖X‖ := by
  have hiso : ‖RMap U X‖ = ‖X‖ := by
    have := inner_RMap U X X
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
    have h2 : ‖RMap U X‖ ^ 2 = ‖X‖ ^ 2 := this
    nlinarith [norm_nonneg (RMap U X), norm_nonneg X, h2]
  calc ‖RMap U X - X‖ ≤ ‖RMap U X‖ + ‖X‖ := norm_sub_le _ _
    _ = 2 * ‖X‖ := by rw [hiso]; ring

#print axioms norm_RMap_sub_self_le_two

/-! ## §7 — the SHARP per-plaquette drift bound (chains `[RMAP-LIP-U1]` onto the curl drift)

The single-scale drift, at every plaquette, is first order in the per-bond holonomy deviation AND
carries the genuine `frobNorm(U b − 1)` smallness — the sharp replacement for §6's crude constant.
This is the pointwise input the multi-scale expansion aggregates; the `L²`-sum aggregation over
plaquettes, with the bond-incidence multiplicity, is now CLOSED in §8–§13 (`[L2-AGG]`). -/

/-- **SHARP per-plaquette drift bound.** At every plaquette `p`, the single-scale drift is
controlled by the two incident per-bond holonomy deviations `frobNorm(U b − 1)` times the
neighbouring field norms:
`‖curlDrift U A p‖ ≤ 2·frobNorm(U(x,μ) − 1)·‖A(x+μ,ν)‖ + 2·frobNorm(U(x,ν) − 1)·‖A(x+ν,μ)‖`.
Both terms VANISH at `U = 1` (`frobNorm 0 = 0`), so the whole drift `→ 0` as `U → 1` — the genuine
`‖U−1‖` first-order smallness. Uniform in the RG step `k`. -/
theorem norm_curlDrift_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖curlDrift U A p‖ ≤
      2 * RMapLipschitz.frobNorm
            ((U (p.1, p.2.1.1) : Matrix (Fin 2) (Fin 2) ℂ) - 1) *
          ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ +
      2 * RMapLipschitz.frobNorm
            ((U (p.1, p.2.1.2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) *
          ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ := by
  rw [curlDrift_apply]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
  · exact RMapLipschitz.norm_RMap_sub_self_le (U (p.1, p.2.1.1))
      (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
  · exact RMapLipschitz.norm_RMap_sub_self_le (U (p.1, p.2.1.2))
      (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))

#print axioms norm_curlDrift_le

/-- **Consistency: the sharp drift bound is `0` at `U = 1`.** At the trivial background every
`frobNorm(U b − 1) = 0`, so the sharp bound forces `‖curlDrift 1 A p‖ ≤ 0`, recovering
`curlDrift_trivialU`. -/
theorem norm_curlDrift_trivialU_le_zero (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖curlDrift (trivialU L) A p‖ ≤ 0 := by
  rw [curlDrift_trivialU]
  simp

#print axioms norm_curlDrift_trivialU_le_zero

/-! ## §8 — the `L²` energies as explicit sums, and the `toPlaqL2`-norm bridge

`[L2-AGG]`. The two `L²` norms the multi-scale expansion consumes, written as plain real sums
(`plaqEnergy`, `bondEnergy`) so nothing depends on a `PiLp` instance on the bond side (the
`CovariantOperators.BondFnL2` diamond, `CovariantHjMinimizer.lean` §3). The plaquette-side norm is
bridged back to `toPlaqL2` (whose Hilbert-space toolkit §4/§5 already use) via `covPlaqInner`. -/

/-- **Plaquette `L²` energy** `= ∑_p ‖f p‖²` (a plain real). `‖·‖_{L²(plaquettes)} = √ plaqEnergy`. -/
noncomputable def plaqEnergy (f : PeriodicLatticePlaquette L → SuTwo) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, ‖f p‖ ^ 2

/-- **Bond `L²` energy** `= ∑_b ‖A b‖²` (a plain real). `‖A‖_{L²(bonds)} = √ bondEnergy`. -/
noncomputable def bondEnergy (A : Bond L → SuTwo) : ℝ :=
  ∑ b : Bond L, ‖A b‖ ^ 2

theorem plaqEnergy_nonneg (f : PeriodicLatticePlaquette L → SuTwo) : 0 ≤ plaqEnergy f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem bondEnergy_nonneg (A : Bond L → SuTwo) : 0 ≤ bondEnergy A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **`‖toPlaqL2 f‖² = plaqEnergy f`** — the bridge from the `PiLp 2` plaquette norm (which §4/§5
carry through Cauchy–Schwarz) to the explicit sum `∑_p ‖f p‖²`. -/
theorem norm_toPlaqL2_sq (f : PeriodicLatticePlaquette L → SuTwo) :
    ‖toPlaqL2 f‖ ^ 2 = plaqEnergy f := by
  rw [← real_inner_self_eq_norm_sq, ← covPlaqInner_eq_inner]
  unfold covPlaqInner plaqEnergy
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact real_inner_self_eq_norm_sq (f p)

theorem norm_toPlaqL2 (f : PeriodicLatticePlaquette L → SuTwo) :
    ‖toPlaqL2 f‖ = Real.sqrt (plaqEnergy f) := by
  rw [← norm_toPlaqL2_sq]; exact (Real.sqrt_sq (norm_nonneg _)).symm

#print axioms norm_toPlaqL2_sq

/-! ## §9 — the per-plaquette SQUARED drift bound with a uniform `sup` bound `α` -/

/-- **Per-plaquette squared drift bound.** With `α` any uniform bound on the per-bond holonomy
deviations (`∀ b, frobNorm(U b − 1) ≤ α`), the squared drift at every plaquette obeys
`‖curlDrift U A p‖² ≤ 8·α²·(‖A(nbr₁)‖² + ‖A(nbr₂)‖²)`, `nbr₁ = (x+μ,ν)`, `nbr₂ = (x+ν,μ)`. The `8`
is `4·2`: `(2αa+2αb)² = 4α²(a+b)² ≤ 8α²(a²+b²)`. `k`-independent. -/
theorem norm_curlDrift_sq_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    ‖curlDrift U A p‖ ^ 2 ≤
      8 * α ^ 2 *
        (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2 +
         ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
  have hbound := norm_curlDrift_le U A p
  have hfμ : RMapLipschitz.frobNorm ((U (p.1, p.2.1.1) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α :=
    hα (p.1, p.2.1.1)
  have hfν : RMapLipschitz.frobNorm ((U (p.1, p.2.1.2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α :=
    hα (p.1, p.2.1.2)
  set fμ := RMapLipschitz.frobNorm ((U (p.1, p.2.1.1) : Matrix (Fin 2) (Fin 2) ℂ) - 1) with hfμd
  set fν := RMapLipschitz.frobNorm ((U (p.1, p.2.1.2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) with hfνd
  set a := ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ with had
  set b := ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ with hbd
  -- hbound : ‖curlDrift U A p‖ ≤ 2*fμ*a + 2*fν*b
  have hstepA : ‖curlDrift U A p‖ ^ 2 ≤ (2 * fμ * a + 2 * fν * b) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hbound 2
  refine le_trans hstepA ?_
  have hfμ0 : 0 ≤ fμ := RMapLipschitz.frobNorm_nonneg _
  have hfν0 : 0 ≤ fν := RMapLipschitz.frobNorm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have h1 : fμ * fμ ≤ α * α := mul_le_mul hfμ hfμ hfμ0 hα0
  have h2 : fν * fν ≤ α * α := mul_le_mul hfν hfν hfν0 hα0
  have h3 : fμ * fν ≤ α * α := mul_le_mul hfμ hfν hfν0 hα0
  nlinarith [h1, h2, h3, sq_nonneg (a - b), mul_nonneg ha0 hb0, sq_nonneg a, sq_nonneg b,
    mul_nonneg hα0 hα0, ha0, hb0]

#print axioms norm_curlDrift_sq_le

/-! ## §10 — the plaquette→bond incidence multiplicity (the `d,L`-only constant)

The whole point of `k`-uniformity: the number of plaquettes for which a fixed bond is a curl-
neighbour is a lattice-combinatorics count with **no scale `k` and no lattice size `L`**. In
dimension `d = 3` (`Fin 3`), a bond `(y, ρ)` is:
- neighbour-1 of exactly `#{μ : μ < ρ}` plaquettes (fibre of `dir ↦ dir.1.2` over `ρ`), and
- neighbour-2 of exactly `#{ν : ν > ρ}` plaquettes (fibre of `dir ↦ dir.1.1` over `ρ`),
each `≤ d − 1 = 2`. For general `d` the same fibres have cardinality `ρ` and `d − 1 − ρ`, both
`≤ d − 1`; here `d = 3` is fixed, so the two `decide`-verified card bounds below carry it. -/

/-- Neighbour-1 fibre bound: `#{dir : ν(dir) = j} ≤ 2` (`= #{μ : μ < j} ≤ d−1`, `d = 3`). -/
theorem dir_proj2_fiber_card_le (j : Fin 3) :
    (Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.2 = j)).card ≤ 2 := by
  revert j; decide

/-- Neighbour-2 fibre bound: `#{dir : μ(dir) = j} ≤ 2` (`= #{ν : ν > j} ≤ d−1`, `d = 3`). -/
theorem dir_proj1_fiber_card_le (j : Fin 3) :
    (Finset.univ.filter (fun dir : PeriodicPlaquetteDirections => dir.1.1 = j)).card ≤ 2 := by
  revert j; decide

/-- **Direction-sum bound via the neighbour-1 multiplicity.** For any nonnegative weight
`w : Fin 3 → ℝ`, `∑_dir w(ν(dir)) ≤ 2 · ∑_ρ w ρ` — the `≤ d−1 = 2` incidence count factored out. -/
theorem sum_dir_proj2_le (w : Fin 3 → ℝ) (hw : ∀ ρ, 0 ≤ w ρ) :
    ∑ dir : PeriodicPlaquetteDirections, w dir.1.2 ≤ 2 * ∑ ρ : Fin 3, w ρ := by
  rw [← Finset.sum_fiberwise' Finset.univ (fun dir : PeriodicPlaquetteDirections => dir.1.2) w,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast dir_proj2_fiber_card_le j) (hw j)

/-- **Direction-sum bound via the neighbour-2 multiplicity.** -/
theorem sum_dir_proj1_le (w : Fin 3 → ℝ) (hw : ∀ ρ, 0 ≤ w ρ) :
    ∑ dir : PeriodicPlaquetteDirections, w dir.1.1 ≤ 2 * ∑ ρ : Fin 3, w ρ := by
  rw [← Finset.sum_fiberwise' Finset.univ (fun dir : PeriodicPlaquetteDirections => dir.1.1) w,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast dir_proj1_fiber_card_le j) (hw j)

#print axioms dir_proj2_fiber_card_le
#print axioms dir_proj1_fiber_card_le

/-! ## §11 — the neighbour-sum reindexings (bond incidence ⇒ `L²(bonds)` energy) -/

/-- **Neighbour-1 energy reindex.** `∑_p ‖A(x+μ,ν)‖² ≤ 2 · bondEnergy A`. Proof: split the plaquette
sum `Site × Directions`, reindex the site sum by the shift `Equiv` (each direction pair contributes
its whole `ν`-slice energy `∑_y ‖A(y,ν)‖²`), then apply the `≤ 2` incidence bound (§10). -/
theorem sum_nbr1_sq_le (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
      ≤ 2 * bondEnergy A := by
  have key : ∑ p : PeriodicLatticePlaquette L,
        ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
      = ∑ dir : PeriodicPlaquetteDirections, ∑ y : PeriodicLatticeSite L, ‖A (y, dir.1.2)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun dir _ => ?_)
    exact Equiv.sum_comp (periodicLatticeShiftEquiv dir.1.1) (fun y => ‖A (y, dir.1.2)‖ ^ 2)
  rw [key]
  have hslice : ∀ ρ : Fin 3, (0 : ℝ) ≤ ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2 :=
    fun ρ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbe : bondEnergy A = ∑ ρ : Fin 3, ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2 := by
    unfold bondEnergy; rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hbe]
  exact sum_dir_proj2_le (fun ρ => ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2) hslice

/-- **Neighbour-2 energy reindex.** `∑_p ‖A(x+ν,μ)‖² ≤ 2 · bondEnergy A`. -/
theorem sum_nbr2_sq_le (A : Bond L → SuTwo) :
    ∑ p : PeriodicLatticePlaquette L, ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2
      ≤ 2 * bondEnergy A := by
  have key : ∑ p : PeriodicLatticePlaquette L,
        ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2
      = ∑ dir : PeriodicPlaquetteDirections, ∑ y : PeriodicLatticeSite L, ‖A (y, dir.1.1)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun dir _ => ?_)
    exact Equiv.sum_comp (periodicLatticeShiftEquiv dir.1.2) (fun y => ‖A (y, dir.1.1)‖ ^ 2)
  rw [key]
  have hslice : ∀ ρ : Fin 3, (0 : ℝ) ≤ ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2 :=
    fun ρ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbe : bondEnergy A = ∑ ρ : Fin 3, ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2 := by
    unfold bondEnergy; rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hbe]
  exact sum_dir_proj1_le (fun ρ => ∑ y : PeriodicLatticeSite L, ‖A (y, ρ)‖ ^ 2) hslice

/-! ## §12 — THE `L²`-AGGREGATED SINGLE-SCALE PERTURBATION BOUND (`[L2-AGG]`, the deliverable) -/

/-- **Squared `L²` aggregate.** `plaqEnergy (curlDrift U A) ≤ 32·α²·bondEnergy A`, `α` any uniform
bound on `frobNorm(U b − 1)`. The `32 = 8·(2 + 2)` is the `8` of §9 times the two `≤ 2` incidence
counts of §11 — `k`-independent, `L`-independent. -/
theorem plaqEnergy_curlDrift_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    plaqEnergy (curlDrift U A) ≤ 32 * α ^ 2 * bondEnergy A := by
  have hstep : plaqEnergy (curlDrift U A)
      ≤ ∑ p : PeriodicLatticePlaquette L,
          8 * α ^ 2 * (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
                     + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
    unfold plaqEnergy
    exact Finset.sum_le_sum (fun p _ => norm_curlDrift_sq_le U A p α hα0 hα)
  refine hstep.trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have h1 := sum_nbr1_sq_le A
  have h2 := sum_nbr2_sq_le A
  have hα2 : (0 : ℝ) ≤ 8 * α ^ 2 := by positivity
  calc 8 * α ^ 2 *
          ((∑ p : PeriodicLatticePlaquette L,
              ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2)
           + ∑ p : PeriodicLatticePlaquette L,
              ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2)
      ≤ 8 * α ^ 2 * (2 * bondEnergy A + 2 * bondEnergy A) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hα2
    _ = 32 * α ^ 2 * bondEnergy A := by ring

#print axioms plaqEnergy_curlDrift_le

/-- **THE `L²`-AGGREGATED SINGLE-SCALE DRIFT BOUND.**
`√(plaqEnergy (curlDrift U A)) ≤ 4·√2·α·√(bondEnergy A)`, i.e.
`‖curlDrift U A‖_{L²(plaq)} ≤ C·α·‖A‖_{L²(bonds)}` with the EXPLICIT, `k`-independent,
`L`-independent constant `C = 4·√2 = √(16·(d−1))` at `d = 3`. `α` is any uniform bound on
`frobNorm(U b − 1)`. -/
theorem norm_curlDrift_L2_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    Real.sqrt (plaqEnergy (curlDrift U A))
      ≤ 4 * Real.sqrt 2 * α * Real.sqrt (bondEnergy A) := by
  have hsq := plaqEnergy_curlDrift_le U A α hα0 hα
  have hrw : Real.sqrt (32 * α ^ 2 * bondEnergy A)
      = 4 * Real.sqrt 2 * α * Real.sqrt (bondEnergy A) := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hb : (32 : ℝ) * α ^ 2 * bondEnergy A = (4 * Real.sqrt 2 * α) ^ 2 * bondEnergy A := by
      have hpow : (4 * Real.sqrt 2 * α) ^ 2 = 32 * α ^ 2 := by rw [mul_pow, mul_pow, h2]; ring
      rw [hpow]
    rw [hb, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) hα0)]
  calc Real.sqrt (plaqEnergy (curlDrift U A))
      ≤ Real.sqrt (32 * α ^ 2 * bondEnergy A) := Real.sqrt_le_sqrt hsq
    _ = 4 * Real.sqrt 2 * α * Real.sqrt (bondEnergy A) := hrw

#print axioms norm_curlDrift_L2_le

/-- **`‖D_U A − D_1 A‖_{L²} = √(plaqEnergy (curlDrift U A))`** — folds the §4/§5 drift factor
(`toPlaqL2`-difference) into the explicit `plaqEnergy` the §12 bound controls. -/
theorem norm_toPlaqL2_curlDrift
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    ‖toPlaqL2 (curlValueCovariant U A) - toPlaqL2 (curlValueCovariant (trivialU L) A)‖
      = Real.sqrt (plaqEnergy (curlDrift U A)) := by
  rw [← toPlaqL2_sub]
  exact norm_toPlaqL2 (curlDrift U A)

/-- **THE `L²`-AGGREGATED SINGLE-SCALE PERTURBATION BOUND** (§5 chained onto §12).
`|deltaJ(U)A − deltaJ(1)A| ≤ 4·√2·α·√(bondEnergy A)·(√deltaJ(U)A + √deltaJ(1)A)`. The exact
`C·α₁·(energy)` shape the multi-scale random-walk iteration consumes, with the EXPLICIT
`k`-independent constant `C = 4·√2` and `α₁ = α` any uniform bound on `frobNorm(U b − 1)`. -/
theorem abs_deltaJ_sub_L2_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : Bond L, RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    |dstarDQuadForm U A - dstarDQuadForm (trivialU L) A| ≤
      4 * Real.sqrt 2 * α * Real.sqrt (bondEnergy A) *
        (Real.sqrt (dstarDQuadForm U A) + Real.sqrt (dstarDQuadForm (trivialU L) A)) := by
  refine le_trans (abs_deltaJ_sub_le U A) ?_
  rw [norm_toPlaqL2_curlDrift]
  refine mul_le_mul_of_nonneg_right (norm_curlDrift_L2_le U A α hα0 hα) ?_
  positivity

#print axioms abs_deltaJ_sub_L2_le

/-! ## §13 — the literal `sup_b` form (`α := sup_b frobNorm(U b − 1)`) -/

/-- **`α₁ = sup_b frobNorm(U b − 1)`** — the least uniform bound, as a `Finset.sup'` over the (finite,
nonempty) bond set. -/
noncomputable def frobSupBond
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun b : Bond L => RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1))

theorem frobNorm_le_frobSupBond
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ frobSupBond U :=
  Finset.le_sup'
    (fun b : Bond L => RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1))
    (Finset.mem_univ b)

theorem frobSupBond_nonneg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    0 ≤ frobSupBond U := by
  obtain ⟨b₀⟩ := (inferInstance : Nonempty (Bond L))
  exact le_trans (RMapLipschitz.frobNorm_nonneg _) (frobNorm_le_frobSupBond U b₀)

/-- **`[L2-AGG]`, literal `sup` form.**
`√(plaqEnergy (curlDrift U A)) ≤ 4·√2·(sup_b frobNorm(U b − 1))·√(bondEnergy A)`. -/
theorem norm_curlDrift_L2_le_sup
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    Real.sqrt (plaqEnergy (curlDrift U A))
      ≤ 4 * Real.sqrt 2 * frobSupBond U * Real.sqrt (bondEnergy A) :=
  norm_curlDrift_L2_le U A (frobSupBond U) (frobSupBond_nonneg U) (frobNorm_le_frobSupBond U)

/-- **`[L2-AGG]`, literal `sup` form, chained perturbation bound.**
`|deltaJ(U)A − deltaJ(1)A| ≤ 4·√2·(sup_b frobNorm(U b − 1))·√(bondEnergy A)·(√deltaJ(U)A + √deltaJ(1)A)`. -/
theorem abs_deltaJ_sub_L2_le_sup
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    |dstarDQuadForm U A - dstarDQuadForm (trivialU L) A| ≤
      4 * Real.sqrt 2 * frobSupBond U * Real.sqrt (bondEnergy A) *
        (Real.sqrt (dstarDQuadForm U A) + Real.sqrt (dstarDQuadForm (trivialU L) A)) :=
  abs_deltaJ_sub_L2_le U A (frobSupBond U) (frobSupBond_nonneg U) (frobNorm_le_frobSupBond U)

#print axioms norm_curlDrift_L2_le_sup
#print axioms abs_deltaJ_sub_L2_le_sup

end AdalyFormal.Balaban.RegularUPerturbation
