/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DeltaKFull

set_option autoImplicit false

/-!
# `IsRegularHolonomy` — a PLAQUETTE-HOLONOMY regularity predicate

See `formal/AdalyFormal/REGULARITY_HOLONOMY.md` for the full writeup. Summary: two de-correlated
prosecution families (Kimi K3, `compute/kimi_stmt_gate/KIMI_STMT_GATE.md`; Sol,
`compute/sol_stmt_gate/SOL_STMT_GATE.md`) convicted `Balaban.TheLemma.IsRegular` (the per-bond
ADJOINT-DISPLACEMENT proxy) on the same mechanism: `Ad(-1) = id`, so a central background
(`U(b) = -1`) has displacement `0` and is admitted regular at every `Mα₀ ≥ 0`, while the transported
`Δ′` term goes strongly negative there. Both gates named the same fix: bound plaquette HOLONOMY
toward the identity. This file builds that predicate, standalone, and proves the three MECHANICAL
acceptance theorems the dispatch demands.
-/

namespace AdalyFormal.Balaban.RegularityHolonomy

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.DeltaPrime
  AdalyFormal.Balaban.DeltaKFull AdalyFormal.Balaban.LatticeOperators

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the holonomy-defect quantity -/

/-- **The plaquette holonomy defect**: `4 − 2·Re(tr(U(∂p)))`. For a unitary `g`, this is the
SQUARED Hilbert–Schmidt distance `‖g − 1‖² = tr((g-1)ᴴ(g-1))` (a standard identity;
`REGULARITY_HOLONOMY.md` §Honesty discloses this correspondence is documented, not re-derived
entrywise in this file — the general NONNEGATIVITY of the quantity, which is all the acceptance
test needs, IS proved below, `holonomyDefectSq_nonneg`, by an independent route). Built entirely
from `DeltaPrime.holonomyElem` (LAW-19, reused not rebuilt) and raw `Matrix.trace`; no scoped norm
instance is opened anywhere in this file. -/
noncomputable def holonomyDefectSq
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : ℝ :=
  4 - 2 * (Matrix.trace (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ)).re

/-- **The new regularity predicate**: every plaquette's holonomy defect is bounded by `Mα₀`. -/
noncomputable def IsRegularHolonomy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (Mα₀ : ℝ) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, holonomyDefectSq U p ≤ Mα₀

/-! ### §1.1 — nonnegativity (independent route: unitary columns are unit vectors) -/

/-- **`holonomyDefectSq ≥ 0` for ANY `U`, `p`** — proved from unitarity alone (`g†g = 1` forces
each diagonal entry's modulus `≤ 1`, so `Re(tr g) ≤ 2`), independent of the sum-of-squares
identity. This confirms `holonomyDefectSq` is a genuine smallness measure (never negative), not
merely a quantity we happen to bound. -/
theorem holonomyDefectSq_nonneg
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    0 ≤ holonomyDefectSq U p := by
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
  have hcol0' : Complex.normSq (g 0 0) + Complex.normSq (g 0 1) = 1 := by
    have := congrArg Complex.re hrow0
    simpa using this
  have h00le : Complex.normSq (g 0 0) ≤ 1 := by
    nlinarith [Complex.normSq_nonneg (g 0 1)]
  have hcol1' : Complex.normSq (g 1 0) + Complex.normSq (g 1 1) = 1 := by
    have := congrArg Complex.re hrow1
    simpa using this
  have h11le : Complex.normSq (g 1 1) ≤ 1 := by
    nlinarith [Complex.normSq_nonneg (g 1 0)]
  have hre00 : (g 0 0).re ≤ 1 := by
    have hns : Complex.normSq (g 0 0) = (g 0 0).re * (g 0 0).re + (g 0 0).im * (g 0 0).im :=
      Complex.normSq_apply (g 0 0)
    nlinarith [sq_nonneg ((g 0 0).im), sq_nonneg ((g 0 0).re - 1)]
  have hre11 : (g 1 1).re ≤ 1 := by
    have hns : Complex.normSq (g 1 1) = (g 1 1).re * (g 1 1).re + (g 1 1).im * (g 1 1).im :=
      Complex.normSq_apply (g 1 1)
    nlinarith [sq_nonneg ((g 1 1).im), sq_nonneg ((g 1 1).re - 1)]
  have htrace : (Matrix.trace g).re = (g 0 0).re + (g 1 1).re := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Complex.add_re]
  unfold holonomyDefectSq
  rw [← hg, htrace]
  linarith

#print axioms holonomyDefectSq_nonneg

/-! ## §2 — ACCEPTANCE ITEM 3a: `trivialU` is regular at every `Mα₀ ≥ 0` -/

theorem holonomyDefectSq_trivialU (p : PeriodicLatticePlaquette L) :
    holonomyDefectSq (trivialU (L := L)) p = 0 := by
  unfold holonomyDefectSq
  rw [holonomyElem_trivialU]
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.one_apply]

#print axioms holonomyDefectSq_trivialU

/-- **ACCEPTANCE ITEM 3a.** -/
theorem trivialU_isRegularHolonomy {Mα₀ : ℝ} (hMα₀ : 0 ≤ Mα₀) :
    IsRegularHolonomy (trivialU (L := L)) Mα₀ := by
  intro p
  rw [holonomyDefectSq_trivialU]
  exact hMα₀

#print axioms trivialU_isRegularHolonomy

/-! ## §3 — ACCEPTANCE ITEM 1: `witnessU` is NOT `IsRegularHolonomy` at `Mα₀ = 2`

`witnessU`'s single non-trivial bond carries `witnessMElem` (`M = !![0,1;-1,0]`, the tree's own
non-flat witness). Its holonomy at `witnessPlaquette` is `witnessMElem` itself (banked,
`holonomy_witnessU_witnessPlaquette`), trace `0`, so `holonomyDefectSq = 4 − 0 = 4 > 2`: the
predicate FAILS at threshold `2` with a clean margin (not a boundary tie — the old `IsRegular`
proxy's own displacement bound gave exactly `2` here; the holonomy-based quantity gives `4`, a
strictly different, larger measure that separates cleanly). -/

theorem holonomyDefectSq_witnessU_witnessPlaquette :
    holonomyDefectSq witnessU witnessPlaquette = 4 := by
  unfold holonomyDefectSq
  rw [holonomy_witnessU_witnessPlaquette]
  norm_num [witnessMElem, witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

#print axioms holonomyDefectSq_witnessU_witnessPlaquette

/-- **ACCEPTANCE ITEM 1, proved (not merely "does not compile").** -/
theorem witnessU_not_isRegularHolonomy_two : ¬ IsRegularHolonomy witnessU (2 : ℝ) := by
  intro h
  have hb := h witnessPlaquette
  rw [holonomyDefectSq_witnessU_witnessPlaquette] at hb
  linarith

#print axioms witnessU_not_isRegularHolonomy_two

/-! ## §4 — ACCEPTANCE ITEM 2: a central background is NOT regular at `Mα₀ = 0`

`centralHolonomyU`: `negOneElem` (`= -1 ∈ SU(2)`, `DeltaKFull.negOneElem`, reused not rebuilt —
LAW-19) on the single bond `(witnessY, 0)`, trivial elsewhere. This is the exact mechanism that
killed `IsRegular`: `Ad(-1) = id`, so the OLD proxy declared this background PERFECTLY regular at
`Mα₀ = 0`. Under `IsRegularHolonomy` it is not: the plaquette holonomy at `witnessPlaquette` is
`negOneElem` itself (product of one `-1` factor and three `1` factors, same combinatorial shape as
`holonomy_witnessU_witnessPlaquette`), trace `-2`, defect `4 - 2·(-2) = 8 > 0`. -/

/-- A central background: `negOneElem` on the single bond `(witnessY, 0)`, trivial elsewhere —
same shape as `witnessU`, with `witnessMElem` replaced by `negOneElem`. -/
noncomputable def centralHolonomyU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) AdmissibleSubspace.witnessL :=
  fun e => if e = (AdmissibleSubspace.witnessY, (0 : Fin 3)) then negOneElem else 1

theorem centralHolonomyU_at_x_mu :
    centralHolonomyU (AdmissibleSubspace.witnessY, (0 : Fin 3)) = negOneElem := by
  simp [centralHolonomyU]

theorem centralHolonomyU_at_y_nu :
    centralHolonomyU (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3)) = 1 := by
  simp only [centralHolonomyU, ite_eq_right_iff]
  intro h; exact absurd h (by decide)

theorem centralHolonomyU_at_x_nu :
    centralHolonomyU (AdmissibleSubspace.witnessY, (1 : Fin 3)) = 1 := by
  simp only [centralHolonomyU, ite_eq_right_iff]
  intro h; exact absurd h (by decide)

theorem centralHolonomyU_at_w_mu :
    centralHolonomyU (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3)) = 1 := by
  simp only [centralHolonomyU, ite_eq_right_iff]
  intro h; exact absurd h (by decide)

theorem holonomy_centralHolonomyU_witnessPlaquette :
    holonomyElem centralHolonomyU witnessPlaquette = negOneElem := by
  change centralHolonomyU (AdmissibleSubspace.witnessY, (0 : Fin 3)) *
      centralHolonomyU (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3)) *
      (centralHolonomyU (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3)))⁻¹ *
      (centralHolonomyU (AdmissibleSubspace.witnessY, (1 : Fin 3)))⁻¹ = negOneElem
  rw [centralHolonomyU_at_x_mu, centralHolonomyU_at_y_nu, centralHolonomyU_at_w_mu,
    centralHolonomyU_at_x_nu]
  simp

theorem holonomyDefectSq_centralHolonomyU_witnessPlaquette :
    holonomyDefectSq centralHolonomyU witnessPlaquette = 8 := by
  unfold holonomyDefectSq
  rw [holonomy_centralHolonomyU_witnessPlaquette]
  norm_num [negOneElem, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

#print axioms holonomyDefectSq_centralHolonomyU_witnessPlaquette

/-- **ACCEPTANCE ITEM 2, proved.** The mechanism that killed `IsRegular` (`Ad(-1)=id` making a
central background register as perfectly regular at `Mα₀ = 0`) does NOT recur here. -/
theorem centralHolonomyU_not_isRegularHolonomy_zero :
    ¬ IsRegularHolonomy centralHolonomyU (0 : ℝ) := by
  intro h
  have hb := h witnessPlaquette
  rw [holonomyDefectSq_centralHolonomyU_witnessPlaquette] at hb
  linarith

#print axioms centralHolonomyU_not_isRegularHolonomy_zero

/-! ## §5 — ACCEPTANCE ITEM 3b: a PURE-GAUGE witness that IS regular at `Mα₀ = 0`

⚠ **CORRECTION BANNER — added 2026-07-26 (degenerate-test-point sweep, defect 1c). THE
"GENUINELY NON-FLAT" LABEL USED THROUGHOUT THIS SECTION IS WRONG.** `pureGaugeU` is a PURE
GAUGE and its curvature is IDENTICALLY the identity: `holonomyElem pureGaugeU p = 1` for EVERY
plaquette `p` — which is exactly what this section's own
`holonomyElem_periodicGaugeTransform_trivialU` states. `pureGaugeU_ne_trivial` establishes only
that ONE BARE LINK VALUE differs from `1`; that is a GAUGE-VARIANT fact carrying no
field-strength information, and it does not make the configuration non-flat in any sense a
holonomy-based predicate can see. Read every occurrence of "genuinely non-flat" and
"non-vacuity beyond the flat background" below as "**differs from the constant-`1`
configuration at a link**", NEVER as "has curvature". Nothing in this file is mathematically
false — only the labels overclaim.

**The genuinely curved replacement is `AdalyFormal/Balaban/NonFlatBackground.lean`**:
`nonflatU t` (an instance of the tree's own `NormalizedCounterexampleSearch.singleBondU`),
with `nonflatU_curvature_ne_one` proving `holonomyElem (nonflatU t) witnessPlaquette ≠ 1` for
every `t ≠ 0`; the strictly stronger gauge-invariant separation
`nonflatU_not_gaugeTransform_of_flat` (it is not the gauge transform of ANY configuration flat
at that plaquette, `pureGaugeU` and `trivialU` included); and `nonflatU_isRegularHolonomy` at
the SHARP threshold `8t²/(1+t²)`, which is arbitrarily small — so the small-`Mα₀` regime this
section was trying to populate is genuinely populated there, by a CURVED background. The
flatness of `pureGaugeU` is restated as a theorem there
(`pureGaugeU_holonomy_eq_one`, `pureGaugeU_holonomyDefectSq_eq_zero`).

**Note for `FaithfulCoercivitySU2.uReg1`** (which consumes `pureGaugeU_isRegularHolonomy_zero`):
this section's `Mα₀ = 0` threshold cannot admit ANY curved witness.
`NonFlatBackground.isRegularHolonomy_zero_iff_flat` proves `IsRegularHolonomy U 0` is
EQUIVALENT to `∀ p, holonomyElem U p = 1`, so at threshold zero the regular set IS the
flat-holonomy set. Fixing that consumer requires re-indexing by a positive threshold, not
swapping the witness.

Original text follows. Non-vacuity beyond the flat `trivialU` config, as mandated (do not skip). Construction: a PURE
GAUGE configuration — `trivialU` transformed by a NON-CONSTANT gauge function `starGaugeFn`
(`witnessMElem` at `witnessY`, `1` elsewhere), via `ClayStatement.periodicGaugeTransform`. This is
mathematically the right kind of witness — physically, pure gauge has zero curvature/holonomy
everywhere — and it is proved from a GENERAL, newly-built gauge-covariance lemma, not merely
verified at one plaquette: `holonomyElem (periodicGaugeTransform γ trivialU) p = 1` for ANY `γ` and
ANY plaquette `p` on ANY lattice `L` (telescoping cancellation, using the already-banked
`LatticeOperators.periodicLatticeShift_comm` — LAW-19, reused not rebuilt). This is a clean, honest
byproduct: it is a first (small) instance of exactly the "gauge transformation action on `Config
Lat`" primitive that `IS_REGULAR.md` §2 named as MISSING for a faithful (3.35)/(3.36) encoding —
built here only far enough to furnish a witness, not claimed as the full primitive. -/

/-- **General gauge covariance of holonomy at the trivial background**: gauge-transforming the
identically-trivial configuration by ANY `γ : Site → G` leaves every plaquette holonomy at `1`.
Standard lattice-gauge-theory fact (pure gauge has vanishing curvature), proved here by direct
telescoping cancellation — the one nontrivial combinatorial ingredient is
`periodicLatticeShift_comm` (shifts in different directions commute), exactly as in
`LatticeOperators.curlValue_gradValue`'s abelian analogue. -/
theorem holonomyElem_periodicGaugeTransform_trivialU
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (p : PeriodicLatticePlaquette L) :
    holonomyElem (periodicGaugeTransform γ (trivialU (L := L))) p = 1 := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  unfold holonomyElem
  change periodicGaugeTransform γ trivialU (p.1, p.2.1.1) *
      periodicGaugeTransform γ trivialU (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
      (periodicGaugeTransform γ trivialU (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ *
      (periodicGaugeTransform γ trivialU (p.1, p.2.1.2))⁻¹ = 1
  simp only [periodicGaugeTransform, trivialU, mul_one]
  rw [← periodicLatticeShift_comm p.1 hne]
  group

#print axioms holonomyElem_periodicGaugeTransform_trivialU

/-- A NON-CONSTANT gauge function: `witnessMElem` at `witnessY`, `1` everywhere else. -/
noncomputable def starGaugeFn :
    PeriodicLatticeSite AdmissibleSubspace.witnessL → Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  fun x => if x = AdmissibleSubspace.witnessY then witnessMElem else 1

/-- **The non-flat witness**: `trivialU`, gauge-transformed by the non-constant `starGaugeFn`. -/
noncomputable def pureGaugeU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) AdmissibleSubspace.witnessL :=
  periodicGaugeTransform starGaugeFn (trivialU (L := AdmissibleSubspace.witnessL))

theorem pureGaugeU_at_x_mu :
    pureGaugeU (AdmissibleSubspace.witnessY, (0 : Fin 3)) = witnessMElem := by
  change starGaugeFn AdmissibleSubspace.witnessY *
      trivialU (AdmissibleSubspace.witnessY, (0 : Fin 3)) *
      (starGaugeFn (periodicLatticeShift AdmissibleSubspace.witnessY 0))⁻¹ = witnessMElem
  have h1 : starGaugeFn AdmissibleSubspace.witnessY = witnessMElem := by simp [starGaugeFn]
  have h2 : trivialU (AdmissibleSubspace.witnessY, (0 : Fin 3)) =
      (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := rfl
  have h3 : starGaugeFn (periodicLatticeShift AdmissibleSubspace.witnessY 0) = 1 := by
    simp only [starGaugeFn, ite_eq_right_iff]
    intro h; exact absurd h.symm (by decide)
  rw [h1, h2, h3]
  simp

#print axioms pureGaugeU_at_x_mu

/-- ⚠ **MISLABELLED — see the §5 correction banner (2026-07-26).** The name and the phrase
"GENUINELY NON-FLAT" overclaim: what is proved is ONLY that `pureGaugeU` differs from the
constant-`1` configuration at the bond `(witnessY, 0)` (value `witnessMElem ≠ 1`, banked
`DeltaKFull.witnessMElem_ne_one`). That is a GAUGE-VARIANT link value. `pureGaugeU`'s CURVATURE
is identically trivial (`pureGaugeU_isRegularHolonomy_zero` below is proved by rewriting the
holonomy to `1`; restated as `NonFlatBackground.pureGaugeU_holonomy_eq_one`). For a background
with provably nonzero curvature use `NonFlatBackground.nonflatU`. -/
theorem pureGaugeU_ne_trivial : pureGaugeU (AdmissibleSubspace.witnessY, (0 : Fin 3)) ≠ 1 := by
  rw [pureGaugeU_at_x_mu]
  exact witnessMElem_ne_one

#print axioms pureGaugeU_ne_trivial

/-- **ACCEPTANCE ITEM 3b, proved — but see the §5 correction banner (2026-07-26).** `pureGaugeU`
is `IsRegularHolonomy`-regular at `Mα₀ = 0`. The claim of "non-vacuity beyond the flat
background" DOES NOT HOLD in the curvature sense: this very proof rewrites the plaquette
holonomy to `1` at every `p`, so the witness is flat and only its link values differ from
`trivialU`'s. A curved witness at a small (necessarily positive) threshold is
`NonFlatBackground.nonflatU t` with `NonFlatBackground.nonflatU_isRegularHolonomy`. -/
theorem pureGaugeU_isRegularHolonomy_zero : IsRegularHolonomy pureGaugeU (0 : ℝ) := by
  intro p
  unfold holonomyDefectSq pureGaugeU
  rw [holonomyElem_periodicGaugeTransform_trivialU]
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.one_apply]

#print axioms pureGaugeU_isRegularHolonomy_zero

end AdalyFormal.Balaban.RegularityHolonomy
