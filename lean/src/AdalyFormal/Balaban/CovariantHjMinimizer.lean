/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CovariantHj
import AdalyFormal.Balaban.LatticeOperators
import AdalyFormal.Balaban.KernelSubspace
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

/-!
# Covariant `H_j` — TIER D of `formal/AdalyFormal/COVARIANT_HJ.md` / `DELTA_J_PINNING.md`

**Task**: build the `U`-dependent analogues of `HjMinimizer.lean`'s `gaugeConstraintSubspace`/
`curlImage`/`RProj`/`hjExtension` for `𝔰𝔲(2)`-valued fields, replacing the flat, `U`-independent
construction `DELTA_J_PINNING.md` proved (in the kernel) cannot satisfy `Δ_nonconstant`.

## Source (CMP95 p.26 eq. (1.47), p.29's three-property characterization — re-read from
`HjMinimizer.lean`'s own already-pinned quotes, cross-checked, not re-rendered a third time)

* p.26: `H_k` sends a coarse configuration `B` to the fine configuration `A` **minimizing**
  `(1/2)⟨∂A,∂A⟩` subject to `Q_kA=B`, `R∂*A=0`.
* p.29: `Q_kH_kB=B`, `R∂*H_kB=0`, and minimality expressed as the orthogonality
  `⟨∂A',∂H_kB⟩=0` for all `A'` in the tangent subspace `{A':Q_kA'=0,R∂*A'=0}`.
The covariant replacement is literal term-substitution: `∂ → D_U`, `∂* → D_U^*` (the genuinely new
object this file builds, §5), everything else (the coarse restriction `Q_k`, the abstract "clear
meaning" of `R` as an orthogonal projection) is `U`-INDEPENDENT and hence PORTABLE unchanged, since
CMP95/96 never make `Q_k`/`R`'s own geometric definitions depend on the background field — only
`∂`/`∂*` (through `D_U`) carry `U`.

## THE INSTANCE HAZARD, and how this file avoids it (mandate's own warning, confirmed firsthand)

`Bond L → SuTwo` (`CovariantOperators.instNormedAddCommGroupBondFn`, SUP norm) and
`PiLp 2 (fun _ : Bond L => SuTwo)` = `BondFnL2` (`CovariantOperators.instNormedAddCommGroupBondFnL2`,
built from the SAME ambient/L2Operator route) are **both already claimed** by
`CovariantOperators.lean` §6/§7. Registering `InnerProductSpace ℝ` on EITHER (via `hsInner`) would
create a genuine diamond (confirmed by re-reading `CovariantHj.lean`'s own "instance hazard" section
and `CovariantOperators.lean` §7's own disclosure of exactly this hazard for `BondFnL2`). This file
therefore:

1. Keeps ALL bond-level pairings as the BARE `Finset.sum` functionals `covBondInner`/`covPlaqInner`
   already built in `CovariantHj.lean` (LAW-19 reuse, no new instance).
2. Builds the `D_U`-adjoint `gradCovariantAdjointValue` **explicitly**, by an EXPLICIT combinatorial
   formula (the discrete covariant divergence), proved (not asserted) to satisfy the defining
   pairing identity `covBondInner (D_Uλ) A = covSiteInner λ (D_U^*A)` — genuinely new content, not a
   call to `ContinuousLinearMap.adjoint` (which would need the forbidden instance).
3. For the TWO places CMP95's construction genuinely needs a Hilbert-space ORTHOGONAL PROJECTION
   (`R`, onto a SITE-indexed subspace; the "closest point" step, onto a PLAQUETTE-indexed subspace),
   introduces `SiteFnL2`/`PlaqFnL2` — **fresh** `PiLp 2`-wrapped types that `CovariantOperators.lean`
   NEVER touches (only `BondFnL2` is pre-claimed there) — with a genuine, non-colliding
   `InnerProductSpace ℝ` instance (`PiLp.innerProductSpace`, LAW-19 reuse of `SuTwoInner.hsInner`'s
   own `InnerProductSpace ℝ SuTwo`), and transports data in/out via `WithLp.linearEquiv` (a plain
   algebraic equivalence needing NO norm compatibility, hence introducing no diamond risk on its
   own). Projections are run entirely inside `SiteFnL2`/`PlaqFnL2`, then the RESULT is carried back
   to the bare `PeriodicLatticeSite L → SuTwo`/`PeriodicLatticePlaquette L → SuTwo` types that
   `gradValueCovariant`/`curlValueCovariant` actually operate on.

## Concurrency note

`Balaban/SuTwoInner.lean` has a live, uncommitted, CURRENTLY BROKEN edit (§9b, a concurrent
diamond-repair lane) — confirmed by direct `lake env lean` on that file (fails) and by no `lean`
process currently running against it. This file imports `SuTwoInner.lean` transitively (via
`CovariantHj.lean`) but never references its broken §9b declarations, and `lake env lean` on
THIS file succeeds because it resolves already-compiled `.olean`s via `LEAN_PATH` rather than
recompiling `SuTwoInner.lean`'s changed source on the fly (confirmed directly, see the progress log
`COVARIANT_HJ_MINIMIZER.md`). `lake build`/`./build_all_modules.sh` will currently fail on
`SuTwoInner.lean` for reasons predating and unrelated to this dispatch (LAW-4 finding, not
remediated here, re-checked at the end).
-/

namespace AdalyFormal.Balaban.CovariantHjMinimizer

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.KernelSubspace

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `periodicLatticeShift` is a bijection in each fixed direction `μ`

Needed for the adjoint construction (§5): summing the covariant gradient's "inflow" term over all
base sites `x` is the same data as summing over all "target" sites `y = shift x μ`, reindexed by the
inverse shift. -/

/-- **The backward shift**: decrement coordinate `μ` by one (wrapping, since `Fin (L μ+1)` carries
its own periodic/mod arithmetic — the SAME ring structure `periodicLatticeShift`'s `+1` already
uses, confirmed directly: `simp` discharges `x μ + 1 - 1 = x μ` generically for `Fin (n+1)`, not
merely on a witness). -/
def periodicLatticeShiftBack {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    PeriodicLatticeSite L :=
  Function.update x μ (x μ - 1)

theorem periodicLatticeShift_shiftBack {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (μ : Fin 3) : periodicLatticeShift (periodicLatticeShiftBack x μ) μ = x := by
  unfold periodicLatticeShift periodicLatticeShiftBack
  simp

theorem periodicLatticeShiftBack_shift {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (μ : Fin 3) : periodicLatticeShiftBack (periodicLatticeShift x μ) μ = x := by
  unfold periodicLatticeShift periodicLatticeShiftBack
  simp

/-- **`periodicLatticeShift · μ` is a genuine `Equiv`** — the bijectivity fact the adjoint
construction's reindexing step (§5) needs. -/
def periodicLatticeShiftEquiv {L : PeriodicLatticeExtent} (μ : Fin 3) :
    PeriodicLatticeSite L ≃ PeriodicLatticeSite L where
  toFun x := periodicLatticeShift x μ
  invFun x := periodicLatticeShiftBack x μ
  left_inv x := periodicLatticeShiftBack_shift x μ
  right_inv x := periodicLatticeShift_shiftBack x μ

theorem periodicLatticeShiftEquiv_apply {L : PeriodicLatticeExtent} (μ : Fin 3)
    (x : PeriodicLatticeSite L) : periodicLatticeShiftEquiv μ x = periodicLatticeShift x μ := rfl

theorem periodicLatticeShiftEquiv_symm_apply {L : PeriodicLatticeExtent} (μ : Fin 3)
    (x : PeriodicLatticeSite L) :
    (periodicLatticeShiftEquiv (L := L) μ).symm x = periodicLatticeShiftBack x μ := rfl

#print axioms periodicLatticeShift_shiftBack
#print axioms periodicLatticeShiftBack_shift
#print axioms periodicLatticeShiftEquiv_apply
#print axioms periodicLatticeShiftEquiv_symm_apply

/-! ## §2 — `covSiteInner`, the missing THIRD bare `L²` pairing (`CovariantHj.lean` built
`covBondInner`/`covPlaqInner`; the adjoint (§5) needs the SITE-indexed sibling). -/

/-- **The `L²` bilinear form on `PeriodicLatticeSite L → 𝔰𝔲(2)`**, same shape as `covBondInner`/
`covPlaqInner` (LAW-19: identical pattern, new index type). -/
noncomputable def covSiteInner (A B : PeriodicLatticeSite L → SuTwo) : ℝ :=
  ∑ x : PeriodicLatticeSite L, hsInner (A x) (B x)

theorem covSiteInner_self_nonneg (A : PeriodicLatticeSite L → SuTwo) : 0 ≤ covSiteInner A A := by
  unfold covSiteInner
  exact Finset.sum_nonneg (fun x _ => hsInner_self_nonneg (A x))

theorem covSiteInner_symm (A B : PeriodicLatticeSite L → SuTwo) :
    covSiteInner A B = covSiteInner B A := by
  unfold covSiteInner
  exact Finset.sum_congr rfl (fun x _ => hsInner_symm (A x) (B x))

theorem covSiteInner_add_left (A1 A2 B : PeriodicLatticeSite L → SuTwo) :
    covSiteInner (A1 + A2) B = covSiteInner A1 B + covSiteInner A2 B := by
  unfold covSiteInner
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => hsInner_add_left (A1 x) (A2 x) (B x))

theorem covSiteInner_smul_left (c : ℝ) (A B : PeriodicLatticeSite L → SuTwo) :
    covSiteInner (c • A) B = c * covSiteInner A B := by
  unfold covSiteInner
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => hsInner_smul_left (A x) (B x) c)

#print axioms covSiteInner_self_nonneg
#print axioms covSiteInner_symm
#print axioms covSiteInner_add_left
#print axioms covSiteInner_smul_left

/-! ## §3 — `SiteFnL2`/`PlaqFnL2`: FRESH `PiLp 2`-wrapped types, safe from the Bond-level diamond

`CovariantOperators.lean` §6/§7 claims `Bond L → SuTwo` and `PiLp 2 (fun _ : Bond L => SuTwo)`
(`BondFnL2`) with instances built from the AMBIENT `Matrix.Norms.L2Operator` route, NOT from
`hsInner`. It never touches a `PiLp`-wrapping of the SITE or PLAQUETTE index types, so those two
types are FRESH: no competing instance exists anywhere in this tree for them. Registering
`InnerProductSpace ℝ` here (via `PiLp.innerProductSpace`, needing `InnerProductSpace ℝ SuTwo`,
`SuTwoInner.lean`'s own, LAW-19) is therefore NOT a diamond — confirmed by grep, not merely assumed
(§9 below, the falsifiability/audit section, re-checks this directly). -/

/-- `PeriodicLatticeSite L → 𝔰𝔲(2)`, `L²`-wrapped — the ambient space `R`'s orthogonal projection
(§6) is safely built on. -/
abbrev SiteFnL2 (L : PeriodicLatticeExtent) : Type := PiLp 2 (fun _ : PeriodicLatticeSite L => SuTwo)

/-- `PeriodicLatticePlaquette L → 𝔰𝔲(2)`, `L²`-wrapped — the ambient space the "closest point"
correction step (§8) is safely built on. -/
abbrev PlaqFnL2 (L : PeriodicLatticeExtent) : Type :=
  PiLp 2 (fun _ : PeriodicLatticePlaquette L => SuTwo)

-- `SiteFnL2 L`/`PlaqFnL2 L` get their `NormedAddCommGroup`/`InnerProductSpace ℝ` instances from
-- Mathlib's own `PiLp.innerProductSpace` (`Mathlib.Analysis.InnerProductSpace.PiL2`) by ORDINARY,
-- ANONYMOUS typeclass search wherever needed — deliberately NOT re-declared as separate top-level
-- `instance`s here. (Diagnosed directly: doing so caused a genuine internal instance mismatch at
-- `Submodule.starProjection`'s `HasOrthogonalProjection`/`CompleteSpace` search, a smaller-scale
-- analogue of the SAME ambient-vs-norm-topology split the concurrent `SuTwo` diamond lane is fighting
-- — confirmed by DELETING the redundant declarations, which resolved it, rather than assumed.)

/-- **`SiteFnL2 L`'s genuine `Fintype`-inner-product REDUCES to `covSiteInner`** on the underlying
data — the bridge lemma making `Submodule.starProjection` (a genuine Hilbert-space fact, §6) usable
against the same bare pairing the rest of this file works with. -/
theorem inner_siteFnL2_eq_covSiteInner (A B : PeriodicLatticeSite L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : SiteFnL2 L) (WithLp.toLp 2 B) : ℝ) = covSiteInner A B := by
  unfold covSiteInner
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun x _ => inner_eq_hsInner (A x) (B x))

theorem inner_plaqFnL2_eq_covPlaqInner (A B : PeriodicLatticePlaquette L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : PlaqFnL2 L) (WithLp.toLp 2 B) : ℝ) = covPlaqInner A B := by
  unfold covPlaqInner
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun p _ => inner_eq_hsInner (A p) (B p))

/-- **The algebraic (no-norm-needed) round-trip**: `WithLp.linearEquiv` transports data between
`SiteFnL2 L` and the bare `PeriodicLatticeSite L → SuTwo`, needing only `Module ℝ` — this is the
mechanism by which a projection computed inside `SiteFnL2` gets carried back OUT to the bare type
`gradValueCovariant`/`covSiteInner` actually operate on, with NO instance registered on the bare
type in the process. -/
noncomputable def siteFnEquiv (L : PeriodicLatticeExtent) :
    SiteFnL2 L ≃ₗ[ℝ] (PeriodicLatticeSite L → SuTwo) :=
  WithLp.linearEquiv 2 ℝ (PeriodicLatticeSite L → SuTwo)

noncomputable def plaqFnEquiv (L : PeriodicLatticeExtent) :
    PlaqFnL2 L ≃ₗ[ℝ] (PeriodicLatticePlaquette L → SuTwo) :=
  WithLp.linearEquiv 2 ℝ (PeriodicLatticePlaquette L → SuTwo)

theorem siteFnEquiv_toLp (A : PeriodicLatticeSite L → SuTwo) :
    siteFnEquiv L (WithLp.toLp 2 A) = A := rfl

theorem siteFnEquiv_symm_apply (A : PeriodicLatticeSite L → SuTwo) :
    (siteFnEquiv L).symm A = WithLp.toLp 2 A := rfl

theorem plaqFnEquiv_toLp (A : PeriodicLatticePlaquette L → SuTwo) :
    plaqFnEquiv L (WithLp.toLp 2 A) = A := rfl

theorem plaqFnEquiv_symm_apply (A : PeriodicLatticePlaquette L → SuTwo) :
    (plaqFnEquiv L).symm A = WithLp.toLp 2 A := rfl

#print axioms inner_siteFnL2_eq_covSiteInner
#print axioms inner_plaqFnL2_eq_covPlaqInner
#print axioms siteFnEquiv_toLp
#print axioms siteFnEquiv_symm_apply
#print axioms plaqFnEquiv_toLp
#print axioms plaqFnEquiv_symm_apply

/-! ## §4 — `Q_ell^{cov}`/`Q_ell'^{cov}`: the coarse-restriction operators — FLAT, ported verbatim,
with an EXPLICIT, PROVED scope limit (STOP-AND-CHECK correction, mid-dispatch, see below)

**Corrected framing.** CMP95 printed p.20, eq. (1.18)/(1.20) (re-read directly from a 300dpi render
of the DEFINING page, `pdftoppm -r 300` on `balaban_CMP95_1984_propagators_I.pdf`
(sha256 `4c879f9f5daa9d5b73ff33f3d4e6710b23616c5491426ecea1a520a12dfffa0f`, matching the hash already
pinned in the corpus's own `p19.md`/`p20.md` front-matter) pages 3-4, printed page HEADERS visually
confirmed "19"/"20"/"T. Balaban" in the rendered image itself — not the
mathpix machine-draft alone), VERBATIM:

> `(Q_kA)_b = Σ_{x∈B^k(b_-)} η^{d+1} A([x,x(b)])` — (1.18), a BARE weighted sum, no transports, no
> `Γ`, no path-ordering (confirmed directly from the image: this specific display has NO group
> elements or contour symbols anywhere in it).
> `A^λ = A - ∂^ηλ`, `(Q_kA^λ)_b = (Q_kA)_b - (Σ_{x∈B^k(b_+)}η^dλ(x) - Σ_{x∈B^k(b_-)}η^dλ(x))`, i.e.
> `Q_kA^λ = Q_kA - ∂Q_k'λ` — (1.20).

So `Q_k`'s bare-sum formula is EXACTLY right, and (1.20)'s gauge action is `A ↦ A - ∂λ`, a LINEAR
SHIFT BY A GRADIENT — the ABELIAN/linearized gauge action of CMP95's FREE (Gaussian) sector, with
**no `Ad(g)`, no conjugation, no `gAg⁻¹` anywhere**. `Q_k` genuinely intertwines THIS action
(`coarseRestrictCovariant_flat_gradient_telescopes` below, proved via the TRANSLATION-BIJECTION
`x↦x(b)` — NOT merely linearity; see the CORRECTION note below for why linearity alone was
INSUFFICIENT and is not the argument used). Also note: eq. (1.8)'s general (first-level) three-term
form is FLAT BUT NOT PATH-FREE — `A(Γ) = Σ_{b⊂Γ}A_b` is an ADDITIVE LINE INTEGRAL over a straight
segment, path content without non-Abelian transport; the AXIAL gauge condition (`A(Γ_{y,x})=0`,
eq. 1.10) is what LEGITIMATELY collapses (1.8) to (1.18)'s central-leg-only bare sum, which is why
citing (1.18) alone (without this gauge-fixing context) would conceal why flatness is correct even
for THIS paper's own `Q_k`. `LatticeOperators.coarseRestrict`/`KernelSubspace.coarseRestrictSite`
are both plain ℝ-linear-combination formulas (sum + scalar mult), hence PORTABLE verbatim to any
`Module ℝ`-valued field (`SuTwo` qualifies). (Terminology note: "`Q_k`" is this campaign's own
dictionary name, matching CMP95's own notation; CMP109's background-field analogue is NOT
literally called `Q` — it is `Ubar(c) = M(U,c)`, eq. (0.4) p.253, a GROUP-valued average over full
contour families weighted `1/|Γ|`, genuinely transport-weighted — a structurally different object
this dispatch does not build, per explicit owner instruction.)

**The scope limit, now PROVED rather than left as an unexamined docstring claim.** CMP95 §1 is the
FREE/Gaussian sector — its `Δ_k` (eq. 1.19) is the `U`-INDEPENDENT object `DELTA_J_PINNING.md`
already kernel-refuted against `Δ_nonconstant`. THIS dispatch's target (CMP109 p.261's `Δ_k(U)`,
the background-field extension `CovariantOperators.lean`/`CovariantHj.lean` build toward) needs
covariance under the DIFFERENT, NONABELIAN action `R_μ(x) ↦ g_xR_μ(x)g_{x+e_μ}^{-1}`,
`A(x,μ) ↦ Ad(g_x)A(x,μ) + [\ldots]` (the action `CovariantOperators.RMap`/`gradValueCovariant`
are built against) — citing (1.18)/(1.20) to justify flat `Q_k` INSIDE that covariant construction
would import the free-theory operator into the background-field theory where the acting group has
changed; both individual facts are true and the COMPOSITION is the wrong object (exactly the
"citation instead of re-derivation" failure mode this campaign's own build discipline exists to
catch). **CORRECTION, mid-dispatch (S75, in place): an earlier draft of this section proved only
`coarseRestrictCovariantLM.map_sub` (pure linearity) and CAPTIONED it as "the abelian intertwining
law holds" — a strictly WEAKER, near-content-free statement than CMP95 (1.20)'s actual chain-map
identity `Q_k∂ = ∂Q_k'` (linearity alone does NOT identify `Q_k(∂λ)` with `∂(Q_k'λ)`; a
de-correlated Sol-family gate exhibited an explicit LINEAR FOIL — `∂=id, Q=id, Q'=0, A=0, λ=1`
giving lhs `=-1` vs rhs `=0` — refuting exactly this conflation). Retracted; replaced below by
`coarseRestrictCovariant_flat_gradient_telescopes`, which proves the REAL geometric identity (the
translation bijection `x↦shift_μx` maps the averaging block onto the SHIFTED block, kernel-checked
via `Finset.image`/`decide` on the concrete witness geometry — general `y`/`ell` would additionally
need to rule out torus wraparound at the block boundary, not attempted here, named as a residual)
— not merely linearity.** `coarseRestrictCovariant_ad_action_witness` below
proves, by an EXPLICIT, KERNEL-CHECKED counterexample, that the ANALOGOUS claim FAILS for the
nonabelian/`Ad` action — flat `Q_k^{cov}` does NOT track a pure-`Ad`-gauge mode `D_Uλ`'s coarse
image correctly once `U` is nontrivial at even ONE link inside the averaging block, confirming
(independently, in the kernel, on THIS Lean encoding) the SAME class of defect the companion Python
prosecution measured on `compute/hj_experiment/hjcov.py` (`compute/hj_prosecution/
PROS_HJ_EXPERIMENT.md`, Attack 4: `0.0%→30.1%` relative gauge-variance growing with distance from
the trivial background). -/

/-- **`(Q_ellA)(b) := (1/ell⁴) • Σ_{x∈blockOf b.1.1 ell} A(x,b.2)`**, CMP95 eq. (1.18), covariant
carrier, `U`-independent — the exact port of `LatticeOperators.coarseRestrict`. -/
noncomputable def coarseRestrictCovariant {L : PeriodicLatticeExtent} (ell : ℕ)
    (A : Bond L → SuTwo) (b : LatticeOperators.CoarseBond L ell) : SuTwo :=
  (1 / (ell : ℝ) ^ 4) • ∑ x ∈ AdmissibleSubspace.blockOf b.1.1 ell, A (x, b.2)

theorem coarseRestrictCovariant_add {L : PeriodicLatticeExtent} (ell : ℕ) (A1 A2 : Bond L → SuTwo)
    (b : LatticeOperators.CoarseBond L ell) :
    coarseRestrictCovariant ell (A1 + A2) b =
      coarseRestrictCovariant ell A1 b + coarseRestrictCovariant ell A2 b := by
  simp only [coarseRestrictCovariant, Pi.add_apply]
  rw [← smul_add]
  congr 1
  rw [← Finset.sum_add_distrib]

theorem coarseRestrictCovariant_smul {L : PeriodicLatticeExtent} (ell : ℕ) (c : ℝ)
    (A : Bond L → SuTwo) (b : LatticeOperators.CoarseBond L ell) :
    coarseRestrictCovariant ell (c • A) b = c • coarseRestrictCovariant ell A b := by
  simp only [coarseRestrictCovariant, Pi.smul_apply]
  rw [smul_comm, ← Finset.smul_sum]

/-- `Q_ell^{cov}` as a genuine `LinearMap` — no `ContinuousLinearMap`/topology needed for the
Submodule-carrier proofs (§7) it feeds. -/
noncomputable def coarseRestrictCovariantLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    (Bond L → SuTwo) →ₗ[ℝ] (LatticeOperators.CoarseBond L ell → SuTwo) where
  toFun A := coarseRestrictCovariant ell A
  map_add' A1 A2 := funext fun b => coarseRestrictCovariant_add ell A1 A2 b
  map_smul' c A := funext fun b => coarseRestrictCovariant_smul ell c A b

/-- **`(Q_ell'λ)(y) := (1/ell³) • Σ_{x∈blockOf y ell} λ(x)`**, CMP95 eq. (1.20), covariant carrier,
`U`-independent — the exact port of `KernelSubspace.coarseRestrictSite`. -/
noncomputable def coarseRestrictSiteCovariant {L : PeriodicLatticeExtent} (ell : ℕ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) : SuTwo :=
  (1 / (ell : ℝ) ^ 3) • ∑ x ∈ AdmissibleSubspace.blockOf y ell, lam x

theorem coarseRestrictSiteCovariant_add {L : PeriodicLatticeExtent} (ell : ℕ)
    (lam1 lam2 : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    coarseRestrictSiteCovariant ell (lam1 + lam2) y =
      coarseRestrictSiteCovariant ell lam1 y + coarseRestrictSiteCovariant ell lam2 y := by
  simp only [coarseRestrictSiteCovariant, Pi.add_apply]
  rw [← smul_add]
  congr 1
  rw [← Finset.sum_add_distrib]

theorem coarseRestrictSiteCovariant_smul {L : PeriodicLatticeExtent} (ell : ℕ) (c : ℝ)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    coarseRestrictSiteCovariant ell (c • lam) y = c • coarseRestrictSiteCovariant ell lam y := by
  simp only [coarseRestrictSiteCovariant, Pi.smul_apply]
  rw [smul_comm, ← Finset.smul_sum]

/-- `Q_ell'^{cov}` as a genuine `LinearMap`. -/
noncomputable def coarseRestrictSiteCovariantLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo) where
  toFun lam := coarseRestrictSiteCovariant ell lam
  map_add' lam1 lam2 := funext fun y => coarseRestrictSiteCovariant_add ell lam1 lam2 y
  map_smul' c lam := funext fun y => coarseRestrictSiteCovariant_smul ell c lam y

/-- **The scalar-splitting reduction**: on a field of the shape `e ↦ f(e) • v` (a fixed `SuTwo`
vector `v`, scalar-weighted by an `ℝ`-valued `f`), `coarseRestrictCovariant` reduces EXACTLY to
`LatticeOperators.coarseRestrict`'s scalar coefficient applied to `v` — the bridge lemma making the
already-proved flat normalization witness (`LatticeOperators.coarseRestrict_witness_value = 1/16`)
directly reusable here (LAW-19), rather than re-deriving the block-sum geometry a second time. -/
theorem coarseRestrictCovariant_smul_fixed {L : PeriodicLatticeExtent} (ell : ℕ)
    (f : Bond L → ℝ) (v : SuTwo) (b : LatticeOperators.CoarseBond L ell) :
    coarseRestrictCovariant ell (fun e => f e • v) b =
      (LatticeOperators.coarseRestrict ell f b) • v := by
  simp only [coarseRestrictCovariant, LatticeOperators.coarseRestrict]
  rw [← Finset.sum_smul, smul_smul]

/-- **D4 falsifiability, cross-checking against the ℝ-VALUED port they mirror**: on the
scalar-weighted witness `e ↦ coarseWitnessConfig e • suTwoWitness`, `coarseRestrictCovariant`'s
output tracks `LatticeOperators.coarseRestrict`'s own already-proved numeric coefficient (`1/16`)
EXACTLY — confirming the `•`-for-`*` substitution did not silently change the normalization
constant (a garbage exponent, e.g. `1/ell³` in place of `1/ell⁴`, would make this witness disagree
with `LatticeOperators.coarseRestrict_witness_value`, exactly as `LatticeOperators.lean` §9's own
D4 test demonstrates on the flat carrier). -/
theorem coarseRestrictCovariant_witness_value :
    coarseRestrictCovariant AdmissibleSubspace.witnessEll
        (fun e => LatticeOperators.coarseWitnessConfig e • suTwoWitness)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) =
      (1 / 16 : ℝ) • suTwoWitness := by
  rw [coarseRestrictCovariant_smul_fixed, LatticeOperators.coarseRestrict_witness_value]

#print axioms coarseRestrictCovariant_add
#print axioms coarseRestrictCovariant_smul
#print axioms coarseRestrictSiteCovariant_add
#print axioms coarseRestrictSiteCovariant_smul
#print axioms coarseRestrictCovariant_smul_fixed
#print axioms coarseRestrictCovariant_witness_value

/-! ## §4b — THE SCOPE PIN (STOP-AND-CHECK correction, addressed mid-dispatch): abelian
intertwining HOLDS, nonabelian/`Ad` intertwining FAILS — both proved, not asserted. -/

/-- The trivial link configuration, generic in `L` (not tied to the witness lattice) — the
`Ad`-action specializes to the abelian shift `A ↦ A - ∂λ` exactly at this background
(`RMap 1 = LinearMap.id`). -/
def trivialU (L : PeriodicLatticeExtent) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L := fun _ => 1

/-- **The translation bijection, at the concrete witness geometry**: the averaging block
`blockOf witnessY witnessEll` is mapped BIJECTIVELY, by a single unit shift in direction `0`, onto
`blockOf (shift_0 witnessY) witnessEll` — CMP95 (1.18)'s own "`x(b)` is a point in `B^k(b_+)`
obtained from `x` by translation by `b`" (p.20), the geometric fact `(1.20)`'s telescoping actually
rests on. Proved by `decide` on this concrete, small (`4³=64`-site) lattice — a GENUINE combinatorial
fact, not a relabeling: at THIS witness point there is no torus wraparound (`witnessY=0`,
`witnessEll=2`, extent `3` per coordinate, so `0,1,2` and their unit shift `1,2,3` both fit inside
`Fin 4` without wrapping), which is exactly the extra hypothesis a fully general (`L`/`y`/`ell`)
version of this lemma would need and which this dispatch does not attempt to supply in general. -/
theorem block_image_shift0 :
    Finset.image (periodicLatticeShiftEquiv (L := AdmissibleSubspace.witnessL) 0)
        (AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll) =
      AdmissibleSubspace.blockOf (periodicLatticeShift AdmissibleSubspace.witnessY 0)
        AdmissibleSubspace.witnessEll := by
  decide

/-- **The block-sum reindexing**, the direct consequence of the bijection above via
`Finset.sum_image`. -/
theorem sum_shift_reindex (lam : PeriodicLatticeSite AdmissibleSubspace.witnessL → SuTwo) :
    (∑ y ∈ AdmissibleSubspace.blockOf (periodicLatticeShift AdmissibleSubspace.witnessY 0)
        AdmissibleSubspace.witnessEll, lam y) =
      ∑ x ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY AdmissibleSubspace.witnessEll,
        lam (periodicLatticeShift x 0) := by
  rw [← block_image_shift0]
  rw [Finset.sum_image (fun x _ y _ hxy =>
    (periodicLatticeShiftEquiv (L := AdmissibleSubspace.witnessL) 0).injective hxy)]
  exact Finset.sum_congr rfl (fun x _ => by rw [periodicLatticeShiftEquiv_apply])

/-- **THE REAL ABELIAN INTERTWINING IDENTITY, CMP95 (1.20)**: `Q_ell^{cov}(D_1λ) = (1/ell)•
[Q_ell'^{cov}λ(shift_0 y) - Q_ell'^{cov}λ(y)]` at the witness coarse bond — NOT merely linearity
(the retracted claim above), but the actual TELESCOPING/translation-bijection identity, using
`sum_shift_reindex` to identify the "inflow" sum with a shifted block, exactly mirroring
`gradCovariantAdjointValue`'s own (§5) reindexing technique one level down. -/
theorem coarseRestrictCovariant_flat_gradient_telescopes
    (lam : PeriodicLatticeSite AdmissibleSubspace.witnessL → SuTwo) :
    coarseRestrictCovariant AdmissibleSubspace.witnessEll
        (gradValueCovariant (trivialU AdmissibleSubspace.witnessL) lam)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 0) =
      (1 / (AdmissibleSubspace.witnessEll : ℝ)) •
        (coarseRestrictSiteCovariant AdmissibleSubspace.witnessEll lam
            (periodicLatticeShift AdmissibleSubspace.witnessY 0) -
          coarseRestrictSiteCovariant AdmissibleSubspace.witnessEll lam
            AdmissibleSubspace.witnessY) := by
  unfold coarseRestrictCovariant coarseRestrictSiteCovariant
  have hgv : ∀ x : PeriodicLatticeSite AdmissibleSubspace.witnessL,
      gradValueCovariant (trivialU AdmissibleSubspace.witnessL) lam (x, 0) =
        lam (periodicLatticeShift x 0) - lam x := by
    intro x
    unfold gradValueCovariant trivialU
    rw [RMap_one]
    rfl
  simp_rw [hgv]
  rw [Finset.sum_sub_distrib, smul_sub, smul_sub, ← sum_shift_reindex]
  rw [smul_smul, smul_smul]
  congr 2 <;> unfold AdmissibleSubspace.witnessEll <;> norm_num

#print axioms block_image_shift0
#print axioms sum_shift_reindex
#print axioms coarseRestrictCovariant_flat_gradient_telescopes

/-- The fine site strictly inside `blockOf witnessY witnessEll` whose `Ad`-transported inflow is
what the witness below toggles — `shift_0(witnessY)`, i.e. `CovariantHj.myWitnessB0.1`, reused
(LAW-19), not a fresh witness. -/
def adWitnessInternalSite : PeriodicLatticeSite AdmissibleSubspace.witnessL :=
  periodicLatticeShift AdmissibleSubspace.witnessY 0

/-- **The background differing from `trivialU` at EXACTLY ONE link, INTERNAL to the averaging
block** (not the coarse bond's own boundary) — `witnessMElem` at `(adWitnessInternalSite, 1)`,
trivial everywhere else. The "far from identity, non-constant across the block" background the
STOP-AND-CHECK demanded (NOT the vacuous constant-`g` case: `trivialU`/`adWitnessU` genuinely
DIFFER at one link and agree at every other link of the SAME block). -/
noncomputable def adWitnessU :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) AdmissibleSubspace.witnessL :=
  fun e => if e = (adWitnessInternalSite, (1 : Fin 3)) then witnessMElem else 1

theorem adWitnessInternalSite_mem_block :
    adWitnessInternalSite ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll := by
  rw [AdmissibleSubspace.mem_blockOf]
  intro μ
  fin_cases μ <;> decide

theorem witnessZPoint_mem_block :
    witnessZPoint ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll := by
  rw [AdmissibleSubspace.mem_blockOf]
  intro μ
  fin_cases μ <;> decide

theorem adWitnessInternalSite_ne_witnessZPoint : adWitnessInternalSite ≠ witnessZPoint := by
  unfold adWitnessInternalSite witnessZPoint
  decide

theorem shift1_adWitnessInternalSite_eq_witnessZPoint :
    periodicLatticeShift adWitnessInternalSite 1 = witnessZPoint := by
  unfold adWitnessInternalSite witnessZPoint
  decide

theorem shift1_witnessZPoint_ne_witnessZPoint :
    periodicLatticeShift witnessZPoint 1 ≠ witnessZPoint := by
  unfold witnessZPoint
  decide

/-- **The pure-`Ad`-gauge mode `D_Uλ` vanishes at EVERY site of the block other than the two
identified** — the mechanical fact making the 8-term block sum collapse to exactly two terms,
for ANY background `U` (the vanishing here uses only injectivity of `shift_1`, not any property
of `U`). -/
theorem gradValueCovariant_witnessLam_vanishes_off_pair
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) AdmissibleSubspace.witnessL)
    {x : PeriodicLatticeSite AdmissibleSubspace.witnessL}
    (hx1 : x ≠ adWitnessInternalSite) (hx2 : x ≠ witnessZPoint) :
    gradValueCovariant U witnessLam (x, 1) = 0 := by
  unfold gradValueCovariant
  have h1 : witnessLam x = 0 := by
    unfold witnessLam
    rw [if_neg hx2]
  have h2 : witnessLam (periodicLatticeShift x 1) = 0 := by
    unfold witnessLam
    rw [if_neg]
    intro hcontra
    apply hx1
    have := congrArg (fun z => periodicLatticeShiftBack z 1) hcontra
    rwa [periodicLatticeShiftBack_shift, show periodicLatticeShiftBack witnessZPoint 1 =
      adWitnessInternalSite from by
        rw [← shift1_adWitnessInternalSite_eq_witnessZPoint, periodicLatticeShiftBack_shift]] at this
  rw [h1, h2, map_zero, sub_zero]

/-- **The full block sum reduces to exactly the two identified terms.** -/
theorem coarseRestrictCovariant_gradValueCovariant_witnessLam
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) AdmissibleSubspace.witnessL) :
    coarseRestrictCovariant AdmissibleSubspace.witnessEll (gradValueCovariant U witnessLam)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 1) =
      (1 / 16 : ℝ) • (RMap (U (adWitnessInternalSite, 1)) suTwoWitness - suTwoWitness) := by
  unfold coarseRestrictCovariant
  have hnorm : (1 / (AdmissibleSubspace.witnessEll : ℝ) ^ 4) = (1 / 16 : ℝ) := by
    unfold AdmissibleSubspace.witnessEll; norm_num
  rw [hnorm]
  congr 1
  set S : Finset (PeriodicLatticeSite AdmissibleSubspace.witnessL) :=
    {adWitnessInternalSite, witnessZPoint} with hS
  have hSsub : S ⊆ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll := by
    rw [hS]
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · rw [hz]; exact adWitnessInternalSite_mem_block
    · rw [hz]; exact witnessZPoint_mem_block
  have hcompl : ∀ x ∈ AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
      AdmissibleSubspace.witnessEll \ S, gradValueCovariant U witnessLam (x, 1) = 0 := by
    intro x hx
    rw [Finset.mem_sdiff, hS, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact gradValueCovariant_witnessLam_vanishes_off_pair U hx.2.1 hx.2.2
  rw [← Finset.sum_sdiff hSsub (f := fun x => gradValueCovariant U witnessLam (x, 1))]
  rw [Finset.sum_congr rfl (fun x hx => hcompl x hx), Finset.sum_const_zero, zero_add]
  rw [hS, Finset.sum_pair adWitnessInternalSite_ne_witnessZPoint]
  have hterm1 : gradValueCovariant U witnessLam (adWitnessInternalSite, 1) =
      RMap (U (adWitnessInternalSite, 1)) suTwoWitness := by
    unfold gradValueCovariant
    rw [shift1_adWitnessInternalSite_eq_witnessZPoint, witnessLam_at_z]
    have : witnessLam adWitnessInternalSite = 0 := by
      unfold witnessLam
      rw [if_neg adWitnessInternalSite_ne_witnessZPoint]
    rw [this, sub_zero]
  have hterm2 : gradValueCovariant U witnessLam (witnessZPoint, 1) = -suTwoWitness := by
    unfold gradValueCovariant
    have h1 : witnessLam (periodicLatticeShift witnessZPoint 1) = 0 := by
      unfold witnessLam
      rw [if_neg shift1_witnessZPoint_ne_witnessZPoint]
    rw [h1, witnessLam_at_z, map_zero, zero_sub]
  rw [hterm1, hterm2]
  abel

/-- **THE REFUTATION WITNESS**: at the TRIVIAL background, the coarse image of this pure-`Ad`-gauge
mode is EXACTLY `0` (matching the abelian/free-sector expectation). -/
theorem coarseRestrictCovariant_gradValueCovariant_witnessLam_trivial :
    coarseRestrictCovariant AdmissibleSubspace.witnessEll
        (gradValueCovariant (trivialU AdmissibleSubspace.witnessL) witnessLam)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 1) = 0 := by
  rw [coarseRestrictCovariant_gradValueCovariant_witnessLam]
  unfold trivialU
  show (1 / 16 : ℝ) • (RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) suTwoWitness -
    suTwoWitness) = 0
  rw [RMap_one]
  simp

/-- **THE REFUTATION WITNESS, continued**: changing the background ONLY at the single link
`(adWitnessInternalSite,1)` — INTERNAL to the SAME averaging block, not touching the block's other
7 sites nor its boundary — flips the coarse image of the SAME pure-`Ad`-gauge mode from `0` to a
NONZERO multiple of `suTwoWitness`. **This is the kernel-checked, non-vacuous counterexample the
abelian intertwining law (`coarseRestrictCovariant_flat_gradient_telescopes`) does NOT extend to the
`Ad` action**: flat `Q_ell^{cov}` does not correctly track a covariant pure-gauge mode once the
background is nontrivial anywhere inside the block, confirming — on THIS Lean encoding,
independently of the companion Python measurement — the STOP-AND-CHECK's diagnosis. -/
theorem coarseRestrictCovariant_ad_action_witness :
    coarseRestrictCovariant AdmissibleSubspace.witnessEll
        (gradValueCovariant adWitnessU witnessLam)
        (⟨AdmissibleSubspace.witnessY, AdmissibleSubspace.witnessY_coarse⟩, 1) ≠ 0 := by
  rw [coarseRestrictCovariant_gradValueCovariant_witnessLam]
  have hU : adWitnessU (adWitnessInternalSite, (1 : Fin 3)) = witnessMElem := by
    unfold adWitnessU
    rw [if_pos rfl]
  rw [hU, RMap_witnessMElem, CovariantHj.neg_sub_self_eq_smul, smul_smul]
  intro hcontra
  have hne : ((1 / 16 : ℝ) * (-2 : ℝ)) ≠ 0 := by norm_num
  rcases smul_eq_zero.mp hcontra with h | h
  · exact hne h
  · exact suTwoWitness_ne_zero h

#print axioms trivialU

#print axioms adWitnessInternalSite_mem_block
#print axioms witnessZPoint_mem_block
#print axioms adWitnessInternalSite_ne_witnessZPoint
#print axioms shift1_adWitnessInternalSite_eq_witnessZPoint
#print axioms shift1_witnessZPoint_ne_witnessZPoint
#print axioms gradValueCovariant_witnessLam_vanishes_off_pair
#print axioms coarseRestrictCovariant_gradValueCovariant_witnessLam
#print axioms coarseRestrictCovariant_gradValueCovariant_witnessLam_trivial
#print axioms coarseRestrictCovariant_ad_action_witness

/-! ## §5a — small `hsInner` bilinearity helpers this construction needs, not already built
elsewhere (LAW-19: builds on `SuTwoInner.lean`'s `hsInner_add_left`/`hsInner_smul_left`/`hsInner_symm`
rather than re-deriving positivity/definiteness). -/

/-- `hsInner (·) Z` as a genuine `LinearMap ℝ` — gets `map_sum`/`map_sub`/`map_neg` for free,
avoiding a manual `Finset.induction`. -/
noncomputable def hsInnerLeftLM (Z : SuTwo) : SuTwo →ₗ[ℝ] ℝ where
  toFun X := hsInner X Z
  map_add' X Y := hsInner_add_left X Y Z
  map_smul' c X := by simp only [RingHom.id_apply]; exact hsInner_smul_left X Z c

theorem hsInnerLeftLM_apply (Z X : SuTwo) : hsInnerLeftLM Z X = hsInner X Z := rfl

theorem hsInner_sub_left (X Y Z : SuTwo) : hsInner (X - Y) Z = hsInner X Z - hsInner Y Z := by
  have := (hsInnerLeftLM Z).map_sub X Y
  simpa only [hsInnerLeftLM_apply] using this

theorem hsInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → SuTwo) (Z : SuTwo) :
    hsInner (∑ i ∈ s, f i) Z = ∑ i ∈ s, hsInner (f i) Z := by
  have := map_sum (hsInnerLeftLM Z) f s
  simpa only [hsInnerLeftLM_apply] using this

theorem hsInner_sum_right {ι : Type*} (s : Finset ι) (X : SuTwo) (f : ι → SuTwo) :
    hsInner X (∑ i ∈ s, f i) = ∑ i ∈ s, hsInner X (f i) := by
  rw [hsInner_symm X, hsInner_sum_left]
  exact Finset.sum_congr rfl (fun i _ => hsInner_symm (f i) X)

/-- **`R(U)`'s two-sided inverse-cancellation**: `R(U)(R(U⁻¹)Y) = Y` — from the homomorphism law
`RMap_mul_apply` plus the group identity `U * U⁻¹ = 1` and `RMap_one`. -/
theorem RMap_apply_inv_cancel (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (Y : SuTwo) :
    RMap U (RMap U⁻¹ Y) = Y := by
  rw [RMap_mul_apply, mul_inv_cancel, RMap_one]
  rfl

/-- **The "transpose" identity for `R`, w.r.t. `hsInner`**: `⟪R(U)X,Y⟫ = ⟪X,R(U⁻¹)Y⟫` — the
discrete analogue of "the adjoint of conjugation by `U` is conjugation by `U⁻¹`", derived from
`Ad`-invariance (`hsInner_RMap`, `SuTwoInner.lean`, LAW-19) plus the cancellation above. -/
theorem hsInner_RMap_transpose (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X Y : SuTwo) :
    hsInner (RMap U X) Y = hsInner X (RMap U⁻¹ Y) := by
  have h : hsInner (RMap U X) (RMap U (RMap U⁻¹ Y)) = hsInner X (RMap U⁻¹ Y) :=
    hsInner_RMap U X (RMap U⁻¹ Y)
  rwa [RMap_apply_inv_cancel] at h

#print axioms hsInnerLeftLM_apply
#print axioms hsInner_sub_left
#print axioms hsInner_sum_left
#print axioms hsInner_sum_right
#print axioms RMap_apply_inv_cancel
#print axioms hsInner_RMap_transpose

/-! ## §5 — THE GENUINELY NEW CONSTRUCTION: `D_U^*`, the EXPLICIT combinatorial adjoint of the
covariant gradient, w.r.t. the bare pairings `covBondInner`/`covSiteInner`

CMP99b p.391's own text ("adjoint operators to derivatives `D`... with respect to natural `L²`
scalar products") NAMES this object but never writes its combinatorial formula — Bałaban's own
route is Fourier-space (CMP95 pp.22-28), not the direct lattice-sum this file needs (since no
`InnerProductSpace`/`ContinuousLinearMap.adjoint` route is safely available here, per the instance
hazard). **Derivation** (worked out by hand, then verified in the kernel below): expanding
`covBondInner (D_Uλ) A = Σ_{x,μ} ⟪R(U(x,μ))λ(shift_μx) - λ(x), A(x,μ)⟫`, splitting the subtraction,
applying `Ad`-invariance (`hsInner_RMap_transpose`) to move `R(U(x,μ))` from the left slot to
`R(U(x,μ)⁻¹)` on the right slot, and reindexing the first double sum by the BIJECTION `shift_μ`
(§1) turns the whole expression into `Σ_y ⟪λ(y), D_U^*A(y)⟫` with

`(D_U^*A)(y) := Σ_μ [R(U(shiftBack_μy,μ)⁻¹)(A(shiftBack_μy,μ)) - A(y,μ)]`

— the discrete COVARIANT DIVERGENCE: backward-transported inflow minus outflow, summed over the
three lattice directions. Genuinely `U`-dependent (the `R(U(...)⁻¹)` factor), and reduces to the
flat divergence `Σ_μ[A(y-e_μ,μ)-A(y,μ)]` when `U≡1` (`RMap_one`). -/

/-- **`(D_U^*A)(y) := Σ_μ [R(U(shiftBack_μ y,μ))⁻¹(A(shiftBack_μ y,μ)) - A(y,μ)]`** — the discrete
covariant divergence, the EXPLICIT adjoint of `gradValueCovariant` (proved below, not asserted). -/
noncomputable def gradCovariantAdjointValue
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (y : PeriodicLatticeSite L) : SuTwo :=
  ∑ μ : Fin 3, (RMap (U (periodicLatticeShiftBack y μ, μ))⁻¹
      (A (periodicLatticeShiftBack y μ, μ)) - A (y, μ))

theorem hsInner_sub_right (X Y Z : SuTwo) : hsInner X (Y - Z) = hsInner X Y - hsInner X Z := by
  rw [hsInner_symm X, hsInner_sub_left, hsInner_symm Y X, hsInner_symm Z X]

/-- **The bond-level bijection `(x,μ) ↦ (shift_μx,μ)`** — a single `Equiv (Bond L) (Bond L)`
reindexing the WHOLE lattice sum in one shot (cleaner than a per-`μ` `Fin 3`-indexed family of
site-equivalences, since `Bond L` is a genuine product type). -/
def bondShiftEquiv {L : PeriodicLatticeExtent} : Bond L ≃ Bond L where
  toFun b := (periodicLatticeShift b.1 b.2, b.2)
  invFun b := (periodicLatticeShiftBack b.1 b.2, b.2)
  left_inv b := by simp [periodicLatticeShiftBack_shift]
  right_inv b := by simp [periodicLatticeShift_shiftBack]

theorem bondShiftEquiv_apply {L : PeriodicLatticeExtent} (b : Bond L) :
    bondShiftEquiv b = (periodicLatticeShift b.1 b.2, b.2) := rfl

theorem bondShiftEquiv_symm_apply {L : PeriodicLatticeExtent} (b : Bond L) :
    (bondShiftEquiv (L := L)).symm b = (periodicLatticeShiftBack b.1 b.2, b.2) := rfl

/-- **Reindexing the "inflow" sum by `bondShiftEquiv`**: the sum over base bonds of the inflow term
equals the sum over target bonds of the corresponding backward-transported term — the ONE genuinely
new combinatorial step (`Equiv.sum_comp`). -/
theorem inflow_sum_reindex
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) :
    ∑ b : Bond L, hsInner (lam (periodicLatticeShift b.1 b.2)) (RMap (U b)⁻¹ (A b)) =
      ∑ c : Bond L,
        hsInner (lam c.1)
          (RMap (U (periodicLatticeShiftBack c.1 c.2, c.2))⁻¹
            (A (periodicLatticeShiftBack c.1 c.2, c.2))) := by
  have := Equiv.sum_comp (bondShiftEquiv (L := L))
    (fun c => hsInner (lam c.1)
      (RMap (U (periodicLatticeShiftBack c.1 c.2, c.2))⁻¹
        (A (periodicLatticeShiftBack c.1 c.2, c.2))))
  simpa only [bondShiftEquiv_apply, periodicLatticeShiftBack_shift] using this

/-- **THE MAIN THEOREM**: `gradCovariantAdjointValue` is the genuine adjoint of `gradValueCovariant`
w.r.t. `covBondInner`/`covSiteInner` — the property CMP99b p.391 names but does not write out, built
here explicitly and proved, not assumed, avoiding the forbidden `InnerProductSpace (Bond L → SuTwo)`
route entirely. -/
theorem covBondInner_gradValueCovariant_eq_covSiteInner
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) :
    covBondInner (gradValueCovariant U lam) A = covSiteInner lam (gradCovariantAdjointValue U A) := by
  unfold covBondInner covSiteInner gradCovariantAdjointValue gradValueCovariant
  have hstep1 : ∀ b : Bond L,
      hsInner (RMap (U b) (lam (periodicLatticeShift b.1 b.2)) - lam b.1) (A b) =
        hsInner (lam (periodicLatticeShift b.1 b.2)) (RMap (U b)⁻¹ (A b)) -
          hsInner (lam b.1) (A b) := by
    intro b
    rw [hsInner_sub_left, hsInner_RMap_transpose]
  simp_rw [hstep1]
  rw [Finset.sum_sub_distrib, inflow_sum_reindex U lam A, ← Finset.sum_sub_distrib]
  rw [Fintype.sum_prod_type
    (f := fun c : PeriodicLatticeSite L × Fin 3 =>
      hsInner (lam c.1)
        (RMap (U (periodicLatticeShiftBack c.1 c.2, c.2))⁻¹
          (A (periodicLatticeShiftBack c.1 c.2, c.2))) - hsInner (lam c.1) (A c))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp_rw [← hsInner_sub_right]
  rw [← hsInner_sum_right]

#print axioms hsInner_sub_right
#print axioms bondShiftEquiv_apply
#print axioms bondShiftEquiv_symm_apply
#print axioms inflow_sum_reindex
#print axioms covBondInner_gradValueCovariant_eq_covSiteInner

/-! ## §6 — `Δ₀^{cov}(U) := D_U^*D_U`, the covariant site Laplacian, GENUINELY `U`-dependent
(unlike the flat `Δ₀ = ∂₀*∂₀`, which carries no `U` at all — `DELTA_J_PINNING.md` FINDING 2), and
`N(Q')^{cov}`, the covariant kernel subspace, `Q'`-flat (§4b: correct for the ABELIAN gauge action
`Q'` itself is covariant under; NOT claimed correct for the nonabelian/`Ad` action — see §4b's
proved scope pin and refutation witness). -/

/-- `D_U^*`, for FIXED `U`, as a genuine `LinearMap ℝ` (needed to compose with `gradCovariantLM U`
below). -/
noncomputable def gradCovariantAdjointLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (Bond L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo) where
  toFun := gradCovariantAdjointValue U
  map_add' A1 A2 := by
    funext y
    simp only [gradCovariantAdjointValue, Pi.add_apply, map_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro μ _
    abel
  map_smul' c A := by
    funext y
    simp only [gradCovariantAdjointValue, Pi.smul_apply, RingHom.id_apply, map_smul]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun μ _ => (smul_sub c _ _).symm)

theorem gradCovariantAdjointLM_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo) :
    gradCovariantAdjointLM U A = gradCovariantAdjointValue U A := rfl

/-- **`Δ₀^{cov}(U) := D_U^* ∘ D_U`, the covariant site Laplacian** — the `U`-dependent replacement
for `LatticeOperators.siteLaplacianCLM`. Genuinely `U`-dependent (its FIRST ingredient, `D_U`, is
already proved `U`-dependent throughout `CovariantOperators.lean`/`CovariantHj.lean`). -/
noncomputable def siteLaplacianCovLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo) :=
  (gradCovariantAdjointLM U).comp (gradCovariantLM U)

/-- **The general identity behind CMP99b's `⟨A,D*DA⟩` term, at SITE level**: `⟪lam,Δ₀^{cov}(U)lam⟫
= ⟪D_Ulam,D_Ulam⟫`, the Gram identity — proved directly from the adjoint identity §5 established
(NOT from a `ContinuousLinearMap.adjoint`/`apply_norm_sq_eq_inner_adjoint_right` route, which needs
the forbidden instance). -/
theorem covSiteInner_siteLaplacianCovLM
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) :
    covSiteInner lam (siteLaplacianCovLM U lam) = covBondInner (gradValueCovariant U lam)
      (gradValueCovariant U lam) := by
  unfold siteLaplacianCovLM
  rw [LinearMap.comp_apply, gradCovariantAdjointLM_apply]
  rw [← covBondInner_gradValueCovariant_eq_covSiteInner]
  rfl

#print axioms gradCovariantAdjointLM_apply
#print axioms covSiteInner_siteLaplacianCovLM

/-! ## §7 — `N(Q')^{cov}`, the covariant kernel subspace — `U`-INDEPENDENT port of
`KernelSubspace.kernelSubspace` (`Q'` itself carries no `U`). **Scope, per §4b's proved pin**: this
is the correct FREE-SECTOR/abelian object; its `Ad`-action behavior is REFUTED (§4b's witness), not
established, and this section does not claim otherwise. -/

/-- **`N(Q')^{cov}`, CMP96 (2.7)/(2.10)'s kernel subspace, covariant carrier** — an explicit
`Submodule ℝ (PeriodicLatticeSite L → SuTwo)`, verbatim structural port of `KernelSubspace.
kernelSubspace` (LAW-19), reusing the SAME `Level`/`List (Level L)` free-data simplification. -/
def kernelSubspaceCov {L : PeriodicLatticeExtent} (levels : List (KernelSubspace.Level L)) :
    Submodule ℝ (PeriodicLatticeSite L → SuTwo) where
  carrier := {lam | ∀ lvl ∈ levels, ∀ y ∈ lvl.2, coarseRestrictSiteCovariant lvl.1 lam y = 0}
  zero_mem' := by
    intro lvl _ y _
    simp [coarseRestrictSiteCovariant]
  add_mem' := by
    intro lam1 lam2 h1 h2 lvl hlvl y hy
    rw [coarseRestrictSiteCovariant_add, h1 lvl hlvl y hy, h2 lvl hlvl y hy, add_zero]
  smul_mem' := by
    intro c lam h lvl hlvl y hy
    rw [coarseRestrictSiteCovariant_smul, h lvl hlvl y hy, smul_zero]

theorem mem_kernelSubspaceCov {L : PeriodicLatticeExtent} {levels : List (KernelSubspace.Level L)}
    {lam : PeriodicLatticeSite L → SuTwo} :
    lam ∈ kernelSubspaceCov levels ↔
      ∀ lvl ∈ levels, ∀ y ∈ lvl.2, coarseRestrictSiteCovariant lvl.1 lam y = 0 := Iff.rfl

/-- **Transported into `SiteFnL2 L`**, mirroring `KernelSubspace.kernelSubspaceH`'s pattern (LAW-19)
— the ambient space `R^{cov}`'s orthogonal-projection construction (§8) runs on. -/
noncomputable def kernelSubspaceCovH {L : PeriodicLatticeExtent}
    (levels : List (KernelSubspace.Level L)) : Submodule ℝ (SiteFnL2 L) :=
  (kernelSubspaceCov levels).map (siteFnEquiv L).symm.toLinearMap

theorem mem_kernelSubspaceCovH {L : PeriodicLatticeExtent} {levels : List (KernelSubspace.Level L)}
    {v : SiteFnL2 L} : v ∈ kernelSubspaceCovH levels ↔ siteFnEquiv L v ∈ kernelSubspaceCov levels := by
  unfold kernelSubspaceCovH
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨lam, hlam, hEq⟩
    have heq2 : (siteFnEquiv L).symm lam = v := hEq
    rw [← heq2]
    simpa using hlam
  · intro hv
    exact ⟨siteFnEquiv L v, hv, by simp⟩

#print axioms mem_kernelSubspaceCov
#print axioms mem_kernelSubspaceCovH

/-! ## §8 — `Δ₀^{cov}(U)(N(Q')^{cov})`, the target subspace `R^{cov}(U)` would project onto —
built, GENUINELY `U`-dependent (§6). **The projection ITSELF (`R^{cov}(U)`, carried back to the
bare type) IS BUILT below (§8a-§8c) — the wall this section's earlier draft characterized is
DEMOLISHED, not merely diagnosed; see §8a's docstring for the technique and §8b for what remains
precisely named.** -/

/-- **`Δ₀^{cov}(U)(N(Q')^{cov})`, bare-type image** — the covariant analogue of
`HjMinimizer.deltaKernelImage`. -/
noncomputable def deltaKernelImageCov {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) : Submodule ℝ (PeriodicLatticeSite L → SuTwo) :=
  Submodule.map (siteLaplacianCovLM U) (kernelSubspaceCov levels)

/-- Transported into `SiteFnL2 L`. -/
noncomputable def deltaKernelImageCovH {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) : Submodule ℝ (SiteFnL2 L) :=
  (deltaKernelImageCov U levels).map (siteFnEquiv L).symm.toLinearMap

theorem mem_deltaKernelImageCovH {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L)) {v : SiteFnL2 L} :
    v ∈ deltaKernelImageCovH U levels ↔ siteFnEquiv L v ∈ deltaKernelImageCov U levels := by
  unfold deltaKernelImageCovH
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨lam, hlam, hEq⟩
    have heq2 : (siteFnEquiv L).symm lam = v := hEq
    rw [← heq2]; simpa using hlam
  · intro hv
    exact ⟨siteFnEquiv L v, hv, by simp⟩

#print axioms mem_deltaKernelImageCovH

/-! ## §8a — THE WALL, DEMOLISHED: `topologicalSpace_bridge`/`uniformSpace_bridge`, then
`RcovCLM`, avoiding the bundled-composition instance mismatch entirely

**The wall, restated exactly as the prior lane characterized it (root cause reproduced verbatim,
then closed, not re-derived from scratch — starts from the prior lane's own diagnosis per this
dispatch's own instruction).** `(deltaKernelImageCovH U levels).starProjection` has type
`SiteFnL2 L →L[ℝ] SiteFnL2 L`. Composing it with `(siteFnEquiv L).symm.toLinearMap` via bundled
`LinearMap.comp` (`∘ₗ`) fails, reproduced directly (`/tmp/check9.lean` in this dispatch's own
working log):

```
error: synthesized type class instance is not definitionally equal to expression inferred by
typing rules
  synthesized: PiLp.topologicalSpace 2 fun x => ↥SuTwo
  inferred:    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
```

**Root cause, now MEASURED rather than merely diagnosed (direct `#synth`/`rfl` probes, not
argument-from-Mathlib-source-reading alone).** Ordinary `#synth TopologicalSpace (SiteFnL2 L)`
resolves to `PiLp.topologicalSpace` built from the AMBIENT `TopologicalSpace SuTwo`
(`instTopologicalSpaceSubtype` — confirmed `rfl` below), NOT the norm/`hsInner`-derived one that
`Submodule.starProjection`'s own `InnerProductSpace ℝ (SiteFnL2 L)`(→`NormedAddCommGroup`→
`PseudoMetricSpace`) internally threads through when INSTANTIATED at the concrete fiber `SuTwo`
(confirmed: holding the fiber instance FIXED at either choice makes the internal
`PseudoMetricSpace.toUniformSpace.toTopologicalSpace = PiLp.topologicalSpace` chain an outright
`rfl` — `/tmp/check3.lean` — so the ENTIRE discrepancy is exactly the SAME ambient-vs-norm diamond
`SuTwoInner.lean` §9b already closed on bare `SuTwo`, now recurring on the PiLp WRAPPING, not a
second, independent defect). -/

/-- **`topologicalSpace_bridge`'s ingredient**: the AMBIENT (ordinarily-`#synth`-findable)
`UniformSpace (SiteFnL2 L)` and the NORM/`hsInner`-derived one (`Submodule.starProjection`'s own)
are the SAME uniformity — lifted from `SuTwoInner.lean` §9b's fiber-level
`ambient_uniformSpace_eq_norm_uniformSpace` by `congrArg`/`funext` over the CONSTANT family
`fun _ : PeriodicLatticeSite L => SuTwo`, since `PiLp.uniformSpace` is a pure function of the
single fiber instance (measured, not assumed: the two `have`s below are each `rfl`, confirming
`PiLp.uniformSpace`'s dependence on the fiber instance is EXACTLY this substitution, no further
divergence hiding downstream). -/
theorem uniformSpace_bridge {L : PeriodicLatticeExtent} :
    (inferInstance : UniformSpace (SiteFnL2 L)) =
      @PseudoMetricSpace.toUniformSpace (SiteFnL2 L) inferInstance := by
  have h1 : (inferInstance : UniformSpace (SiteFnL2 L)) =
      @PiLp.uniformSpace 2 (PeriodicLatticeSite L) (fun _ => SuTwo)
        (fun _ => instUniformSpaceSubtype) := rfl
  have h2 : (@PseudoMetricSpace.toUniformSpace (SiteFnL2 L) inferInstance) =
      @PiLp.uniformSpace 2 (PeriodicLatticeSite L) (fun _ => SuTwo)
        (fun _ => PseudoMetricSpace.toUniformSpace) := rfl
  -- REPAIRED 2026-07-28 (`compute/sutwo_diamond`; out-of-scope one-line fix, DISCLOSED). The
  -- previous script was `rw [h1, h2]; congr 1; funext _; exact
  -- ambient_uniformSpace_eq_norm_uniformSpace`. After `SuTwoInner.lean` §4b closes the FIBRE
  -- diamond BY CONSTRUCTION (`uniformSpace_diamond_is_rfl`), the `rw` already closes the goal and
  -- every following tactic failed with "No goals to be solved". Rewritten as a pure TERM proof:
  -- same mathematical content, no dependence on whether the two fibre instances happen to be
  -- definitionally equal, so it compiles in both the pre- and post-repair worlds.
  have key : @PiLp.uniformSpace 2 (PeriodicLatticeSite L) (fun _ => SuTwo)
        (fun _ => instUniformSpaceSubtype)
      = @PiLp.uniformSpace 2 (PeriodicLatticeSite L) (fun _ => SuTwo)
        (fun _ => PseudoMetricSpace.toUniformSpace) :=
    congrArg
      (fun u : UniformSpace SuTwo =>
        @PiLp.uniformSpace 2 (PeriodicLatticeSite L) (fun _ => SuTwo) (fun _ => u))
      ambient_uniformSpace_eq_norm_uniformSpace
  exact h1.trans (key.trans h2.symm)

/-- **The `TopologicalSpace`-level corollary** — literally the mismatch quoted in the wall's error
message, now an equality rather than an obstruction: the "synthesized" side
(`PiLp.topologicalSpace`, ambient) equals the "inferred" side
(`PseudoMetricSpace.toUniformSpace.toTopologicalSpace`, norm-derived), by `congrArg
UniformSpace.toTopologicalSpace` over `uniformSpace_bridge`. -/
theorem topologicalSpace_bridge {L : PeriodicLatticeExtent} :
    (inferInstance : TopologicalSpace (SiteFnL2 L)) =
      @UniformSpace.toTopologicalSpace (SiteFnL2 L)
        (@PseudoMetricSpace.toUniformSpace (SiteFnL2 L) inferInstance) :=
  congrArg (@UniformSpace.toTopologicalSpace (SiteFnL2 L)) uniformSpace_bridge

/-! **Route (a) (the bridging theorem the dispatch asked for) is thus CLOSED** — `uniformSpace_
bridge`/`topologicalSpace_bridge` are the exact PiLp-level analogues of `SuTwoInner.lean` §9b's
fiber-level bridge, kernel-checked. But CARRYING `starProjection` back to the bare type does NOT,
in the end, need to invoke them: bundled composition (`∘ₗ`/`∘L`) forces Lean to unify the WHOLE
instance-argument list baked into each bundled map's type, and `LinearMap.comp`'s unification
attempt is what surfaces the mismatch even though the underlying `Module ℝ (SiteFnL2 L)` instances
DO already agree (`#synth Module ℝ (SiteFnL2 L) = WithLp.instModule`, unique, confirmed directly —
this was never a `Module`-level diamond). The ROBUST fix, mirroring `ce4033ac`'s OWN
"identity-map-both-ways" spirit at one further remove: apply the three pieces
(`siteFnEquiv`, `starProjection`, `(siteFnEquiv).symm`) as BARE FUNCTIONS (function application
needs no instance-argument unification at all — a term's type is already fixed once elaborated),
then prove `LinearMap`-hood MANUALLY from each piece's own, already-established linearity
(`siteFnEquiv`'s own `map_add`/`map_smul` as a `LinearEquiv`, `starProjection`'s own as a
`ContinuousLinearMap`), and finally upgrade to `ContinuousLinearMap` via
`LinearMap.continuous_of_finiteDimensional`/`LinearMap.toContinuousLinearMap` applied DIRECTLY on
the BARE type's OWN ambient topology (`Pi.t2Space`/`FiniteDimensional.finiteDimensional_pi'`,
needing NO `InnerProductSpace` on the bare type at all) — sidestepping the diamond for the
CONSTRUCTION entirely, rather than resolving it. Confirmed empirically (`/tmp/check8.lean`
reproduces the wall via bundled `∘ₗ`; `/tmp/check11.lean`–`/tmp/check14.lean` confirm the bare-
function route is clean) before landing this. -/

/-- **`R^{cov}(U)`, as a bare function** — the wall's target object, carried back to
`PeriodicLatticeSite L → SuTwo` by ordinary (unbundled) function application through
`siteFnEquiv`/`starProjection`/`siteFnEquiv.symm`. -/
noncomputable def RcovFun {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    (PeriodicLatticeSite L → SuTwo) → (PeriodicLatticeSite L → SuTwo) :=
  fun lam => siteFnEquiv L ((deltaKernelImageCovH U levels).starProjection ((siteFnEquiv L).symm lam))

/-- **`R^{cov}(U)` is ℝ-linear** — proved directly from `siteFnEquiv`'s/`starProjection`'s OWN
additivity/homogeneity (`map_add`/`map_smul`, available on both since one is a `LinearEquiv` and
the other a `ContinuousLinearMap`), with NO bundled composition anywhere in the proof. -/
noncomputable def RcovLM {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo) where
  toFun := RcovFun U levels
  map_add' a b := by
    unfold RcovFun
    rw [map_add, map_add, map_add]
  map_smul' c a := by
    unfold RcovFun
    rw [map_smul, map_smul, map_smul, RingHom.id_apply]

#print axioms uniformSpace_bridge
#print axioms topologicalSpace_bridge
#print axioms RcovLM

/-! ## §8b — `RcovCLM`: THE WALL'S TARGET OBJECT, `H →L[ℝ] H` typed to match `Coercivity.lean`'s
own `Δ : ℕ → Uconfig → H →L[ℝ] H` field shape (line 195), the downstream consumer this dispatch's
brief names as the reason the operator level (not just the quadratic-form level) matters -/

/-- **`R^{cov}(U)`, upgraded to a `ContinuousLinearMap`** — via `LinearMap.toContinuousLinearMap`,
which needs only `[T2Space][FiniteDimensional ℝ]` on the DOMAIN `PeriodicLatticeSite L → SuTwo`
(the bare Pi type: `Pi.t2Space`/`FiniteDimensional.finiteDimensional_pi'`, both ordinarily
`#synth`-findable, confirmed directly, no `InnerProductSpace` on the bare type needed at all) —
`R^{cov}(U)` is automatically continuous because a finite-dimensional domain forces it, the SAME
general fact (`LinearMap.continuous_of_finiteDimensional`) `SuTwoInner.lean` §9b used one level
down. This is the object the wall's own docstring named as not-yet-built; it is now built, with
`#print axioms` below confirming no `sorry`/extra axiom crept in. -/
noncomputable def RcovCLM {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    (PeriodicLatticeSite L → SuTwo) →L[ℝ] (PeriodicLatticeSite L → SuTwo) :=
  LinearMap.toContinuousLinearMap (RcovLM U levels)

theorem RcovCLM_apply {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (lam : PeriodicLatticeSite L → SuTwo) :
    RcovCLM U levels lam = RcovFun U levels lam := rfl

#print axioms RcovCLM
#print axioms RcovCLM_apply

/-! ## §8c — `R^{cov}(U)` genuinely IS an orthogonal projection, not merely a type-correct map:
membership, idempotence, fixing, and self-adjointness w.r.t. the BARE pairing `covSiteInner`,
each ported from `Submodule.starProjection`'s own characterizing Mathlib lemmas (S91 discipline:
these are EQUALITIES/membership facts tied to the SPECIFIC construction, not a free existential). -/

/-- **Range**: `R^{cov}(U)` lands in `Δ₀^{cov}(U)(N(Q')^{cov})`, the target subspace the wall's own
§8 built and named — confirming `RcovFun` is not merely SOME linear map, but one whose image is
the intended one. -/
theorem RcovFun_mem {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (lam : PeriodicLatticeSite L → SuTwo) :
    RcovFun U levels lam ∈ deltaKernelImageCov U levels := by
  unfold RcovFun
  exact (mem_deltaKernelImageCovH U levels).mp (Submodule.starProjection_apply_mem _ _)

/-- **Idempotence**: `R^{cov}(U) ∘ R^{cov}(U) = R^{cov}(U)`, ported from `Submodule.
isIdempotentElem_starProjection`. -/
theorem RcovFun_idem {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (lam : PeriodicLatticeSite L → SuTwo) :
    RcovFun U levels (RcovFun U levels lam) = RcovFun U levels lam := by
  unfold RcovFun
  rw [siteFnEquiv_symm_apply, WithLp.toLp_ofLp]
  congr 1
  exact congrFun (congrArg DFunLike.coe (Submodule.isIdempotentElem_starProjection
    (deltaKernelImageCovH U levels))) _

/-- **Fixes points already in the target subspace**, ported from `Submodule.
starProjection_eq_self_iff` — the "projection" behavior a mere idempotent-linear-map claim would
not by itself guarantee. -/
theorem RcovFun_fixes {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {lam : PeriodicLatticeSite L → SuTwo} (h : lam ∈ deltaKernelImageCov U levels) :
    RcovFun U levels lam = lam := by
  unfold RcovFun
  have hmem : (siteFnEquiv L).symm lam ∈ deltaKernelImageCovH U levels := by
    rw [mem_deltaKernelImageCovH]
    simpa using h
  rw [Submodule.starProjection_eq_self_iff.mpr hmem]
  simp

/-- **Self-adjoint w.r.t. the BARE pairing `covSiteInner`** — ported from `Submodule.
starProjection_isSymmetric` via `inner_siteFnL2_eq_covSiteInner` (§3), confirming `R^{cov}(U)` is a
genuine ORTHOGONAL projection for CMP95/96's own bilinear form on `PeriodicLatticeSite L → SuTwo`,
not merely for `SiteFnL2 L`'s bundled inner product. -/
theorem RcovFun_selfAdjoint {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (lam1 lam2 : PeriodicLatticeSite L → SuTwo) :
    covSiteInner (RcovFun U levels lam1) lam2 = covSiteInner lam1 (RcovFun U levels lam2) := by
  unfold RcovFun
  rw [← inner_siteFnL2_eq_covSiteInner, ← inner_siteFnL2_eq_covSiteInner]
  rw [siteFnEquiv_symm_apply, siteFnEquiv_symm_apply, WithLp.toLp_ofLp, WithLp.toLp_ofLp]
  exact Submodule.starProjection_isSymmetric (deltaKernelImageCovH U levels) _ _

#print axioms RcovFun_mem
#print axioms RcovFun_idem
#print axioms RcovFun_fixes
#print axioms RcovFun_selfAdjoint

/-! ## §8d — the `[HasOrthogonalProjection]` hypothesis is ALWAYS DISCHARGEABLE, not a hidden
residual: `deltaKernelImageCovH U levels` is a submodule of a FINITE-DIMENSIONAL space
(`SiteFnL2 L`, finite `Fintype` index × finite-dim `SuTwo` fiber), so ordinary `#synth
(deltaKernelImageCovH U levels).HasOrthogonalProjection` ALREADY succeeds (confirmed directly,
`/tmp/check25.lean`, resolving to `Submodule.HasOrthogonalProjection.ofCompleteSpace` via Mathlib's
own standing `CompleteSpace`-for-finite-dimensional-submodules instance chain) — no additional
instance needed here; named so no downstream consumer mistakes the `[...]` bracket on `RcovLM`/
`RcovCLM`/`RcovFun_*` for an unclosed hypothesis that must be manually discharged at each call
site. -/

/-! ## §8e — the P3 question ("does the fresh-type trick make the `suTwo`-carrier import-cycle
refactor unnecessary?"), ANSWERED: **P3 is unnecessary.**

Measured, not merely argued: (1) `RcovCLM` above is built ENTIRELY on the bare SITE-indexed type
`PeriodicLatticeSite L → SuTwo` plus the FRESH `SiteFnL2 L` (§3's already-landed trick) — no
`BondFnL2`, no bond-level type at all, is touched by the wall's demolition. `Coercivity.lean`'s own
`Δ : ℕ → Uconfig → H →L[ℝ] H` field (line 195) is generic in `H`; `siteLaplacianCovLM` (§6, already
a bare-type `LinearMap`, no `InnerProductSpace` needed to BUILD it) is the object CMP99b's own
`Δ_k(U)` actually names — a SITE operator, not a bond operator — so the natural instantiation is
`H := SiteFnL2 L` (already has a genuine, non-colliding `InnerProductSpace ℝ`, §3), never
`BondFnL2 L` (`CovariantOperators.lean`'s ALREADY-CLAIMED, `L2Operator`-sourced type P3 worried
about colliding with). (2) Separately, ATTEMPTING to upgrade an operator built ON `SiteFnL2 L`
itself (rather than the bare type) to `ContinuousLinearMap` via the SAME finite-dimensionality
route hits a DIFFERENT, machine-confirmed gap: `#synth IsTopologicalAddGroup (SiteFnL2 L)` FAILS
outright (checked directly, `/tmp/check22.lean`) — a further manifestation of the SAME
ambient-vs-norm diamond family (one level deeper: `IsTopologicalAddGroup`, not `TopologicalSpace`),
reproducible with or WITHOUT `BondFnL2`/P3's proposed refactor, since it is intrinsic to `PiLp`'s
instance architecture for THIS fiber, not to which FILE `suTwo`'s carrier is defined in — moving
`suTwo`'s definition would not change which `TopologicalSpace`/`IsTopologicalAddGroup` instances
Lean's typeclass search finds for `PiLp 2 (fun _ => SuTwo)`. An attempted closure via
`topologicalSpace_bridge ▸ ...`/`rw [topologicalSpace_bridge]` did NOT go through in the time
available — `▸`/`rw` need the ambient instance to appear SYNTACTICALLY in the elaborated goal, and
`IsTopologicalAddGroup (SiteFnL2 L)`'s displayed goal does not expose it for direct rewriting;
closing it needs either an explicit `@`-elaborated goal statement or building `ContinuousAdd`/
`ContinuousNeg` fields by hand from `Continuous`-level transport — NAMED HERE, not attempted further
(§8b's `RcovCLM`, on the bare type, needs no such instance and is unaffected). **Conclusion: if a
genuinely bond-indexed `H` is ever needed by a `Coercivity.lean`-style consumer, the fix is (i) the
SAME fresh-type trick at bond level (a `BondFnL2'` distinct from `CovariantOperators.lean`'s, no
refactor of `suTwo`'s carrier needed), composed with (ii) building the OPERATOR on the bare bond
type first (as `RcovLM`/`siteLaplacianCovLM` already do — no `InnerProductSpace` needed for that
step) before any `SiteFnL2`-style upgrade; P3's queued import-cycle refactor addresses neither
gap and should not be run.** -/

/-! ## §9 — `V^{cov}(U) := ker(Q_1^{cov}) ⊓ ker(R^{cov}(U)∘D_U^*)`, the covariant gauge-tangent
subspace, and `W^{cov}(U) := D_U(V^{cov}(U))`, its curl-image — the `U`-dependent analogues of
`HjMinimizer.lean`'s §2 (`gaugeConstraintSubspace`/`curlImage`), CMP95 p.29's
`{A':Q_kA'=0,R∂*A'=0}` with `Q_k → coarseRestrictCovariantLM`, `∂* → gradCovariantAdjointLM`,
`R → RcovLM`, `∂ → curlCovariantLM` (`CovariantOperators.lean` §6, REUSED, not rebuilt — LAW-19).
`Submodule` here needs only `AddCommGroup`/`Module ℝ` on the bare Pi carrier — already present
(via `CovariantOperators.lean`'s `Pi.normedAddCommGroup`/`Pi.normedSpace`, which subsume the
algebraic structure without any diamond, since `Submodule` never inspects the norm). -/

/-- **`V^{cov}(U) := {A' : Q_ell^{cov}A'=0, R^{cov}(U)(D_U^*A')=0}`**, the covariant gauge-tangent
subspace. -/
noncomputable def gaugeConstraintSubspaceCov {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    Submodule ℝ (Bond L → SuTwo) where
  carrier := {A' | coarseRestrictCovariantLM L ell A' = 0 ∧
    RcovLM U levels (gradCovariantAdjointLM U A') = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · rw [map_add, ha1, hb1, add_zero]
    · rw [map_add, map_add, ha2, hb2, add_zero]
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · rw [map_smul, ha1, smul_zero]
    · rw [map_smul, map_smul, ha2, smul_zero]

theorem mem_gaugeConstraintSubspaceCov {L : PeriodicLatticeExtent} {ell : ℕ}
    {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {A' : Bond L → SuTwo} :
    A' ∈ gaugeConstraintSubspaceCov ell levels U ↔
      coarseRestrictCovariantLM L ell A' = 0 ∧
        RcovLM U levels (gradCovariantAdjointLM U A') = 0 := Iff.rfl

#print axioms mem_gaugeConstraintSubspaceCov

/-- **`W^{cov}(U) := D_U(V^{cov}(U))`**, the curl-image of the gauge-tangent subspace. -/
noncomputable def curlImageCov {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    Submodule ℝ (PeriodicLatticePlaquette L → SuTwo) :=
  Submodule.map (curlCovariantLM U) (gaugeConstraintSubspaceCov ell levels U)

theorem mem_curlImageCov_iff {L : PeriodicLatticeExtent} {ell : ℕ}
    {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {y : PeriodicLatticePlaquette L → SuTwo} :
    y ∈ curlImageCov ell levels U ↔
      ∃ v ∈ gaugeConstraintSubspaceCov ell levels U, curlCovariantLM U v = y := by
  unfold curlImageCov
  exact Submodule.mem_map

theorem curl_mem_curlImageCov_of_mem {L : PeriodicLatticeExtent} {ell : ℕ}
    {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {v : Bond L → SuTwo} (hv : v ∈ gaugeConstraintSubspaceCov ell levels U) :
    curlCovariantLM U v ∈ curlImageCov ell levels U :=
  mem_curlImageCov_iff.mpr ⟨v, hv, rfl⟩

#print axioms mem_curlImageCov_iff
#print axioms curl_mem_curlImageCov_of_mem

/-! ## §10 — `curlImageCovH`/`curlImageCovProj`: the covariant closest-point projection onto
`W^{cov}(U)ᗮ`, mirroring §8a-§8c's `RcovFun` construction EXACTLY (bare-function route through the
FRESH `PlaqFnL2 L` type, avoiding the same `BondFnL2`/ambient-vs-norm diamond `RcovFun` avoided). -/

/-- `curlImageCov`, transported into `PlaqFnL2 L`. -/
noncomputable def curlImageCovH {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    Submodule ℝ (PlaqFnL2 L) :=
  (curlImageCov ell levels U).map (plaqFnEquiv L).symm.toLinearMap

theorem mem_curlImageCovH {L : PeriodicLatticeExtent} {ell : ℕ}
    {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {v : PlaqFnL2 L} :
    v ∈ curlImageCovH ell levels U ↔ plaqFnEquiv L v ∈ curlImageCov ell levels U := by
  unfold curlImageCovH
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hEq⟩
    have heq2 : (plaqFnEquiv L).symm y = v := hEq
    rw [← heq2]
    simpa using hy
  · intro hv
    exact ⟨plaqFnEquiv L v, hv, by simp⟩

#print axioms mem_curlImageCovH

/-- **`W^{cov}(U)`'s closest-point projection, as a bare function**, mirroring `RcovFun`. -/
noncomputable def curlImageCovProj {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection] :
    (PeriodicLatticePlaquette L → SuTwo) → (PeriodicLatticePlaquette L → SuTwo) :=
  fun A => plaqFnEquiv L ((curlImageCovH ell levels U).starProjection ((plaqFnEquiv L).symm A))

/-- **`curlImageCovProj` is ℝ-linear**, mirroring `RcovLM`. -/
noncomputable def curlImageCovProjLM {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection] :
    (PeriodicLatticePlaquette L → SuTwo) →ₗ[ℝ] (PeriodicLatticePlaquette L → SuTwo) where
  toFun := curlImageCovProj ell levels U
  map_add' a b := by
    unfold curlImageCovProj
    rw [map_add, map_add, map_add]
  map_smul' c a := by
    unfold curlImageCovProj
    rw [map_smul, map_smul, map_smul, RingHom.id_apply]

#print axioms curlImageCovProjLM

/-- **`curlImageCovProj` distributes over `+`** — the bare-function analogue of `map_add`, since
`curlImageCovProj` is NOT itself a bundled `LinearMap` (only `curlImageCovProjLM` is), so generic
`map_add`-rewriting does not fire on it directly; this restates `curlImageCovProjLM`'s own `map_add`
in terms of the bare function. -/
theorem curlImageCovProj_add {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A B : PeriodicLatticePlaquette L → SuTwo) :
    curlImageCovProj ell levels U (A + B) =
      curlImageCovProj ell levels U A + curlImageCovProj ell levels U B :=
  (curlImageCovProjLM ell levels U).map_add A B

#print axioms curlImageCovProj_add

/-- Range: `curlImageCovProj` lands in `curlImageCov`. -/
theorem curlImageCovProj_mem {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A : PeriodicLatticePlaquette L → SuTwo) :
    curlImageCovProj ell levels U A ∈ curlImageCov ell levels U := by
  unfold curlImageCovProj
  exact mem_curlImageCovH.mp (Submodule.starProjection_apply_mem _ _)

/-- Fixes points already in `curlImageCov`. -/
theorem curlImageCovProj_fixes {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    {A : PeriodicLatticePlaquette L → SuTwo} (h : A ∈ curlImageCov ell levels U) :
    curlImageCovProj ell levels U A = A := by
  unfold curlImageCovProj
  have hmem : (plaqFnEquiv L).symm A ∈ curlImageCovH ell levels U := by
    rw [mem_curlImageCovH]
    simpa using h
  rw [Submodule.starProjection_eq_self_iff.mpr hmem]
  simp

/-- **Self-adjoint w.r.t. the BARE pairing `covPlaqInner`.** -/
theorem curlImageCovProj_selfAdjoint {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A1 A2 : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner (curlImageCovProj ell levels U A1) A2 =
      covPlaqInner A1 (curlImageCovProj ell levels U A2) := by
  unfold curlImageCovProj
  rw [← inner_plaqFnL2_eq_covPlaqInner, ← inner_plaqFnL2_eq_covPlaqInner]
  rw [plaqFnEquiv_symm_apply, plaqFnEquiv_symm_apply, WithLp.toLp_ofLp, WithLp.toLp_ofLp]
  exact Submodule.starProjection_isSymmetric (curlImageCovH ell levels U) _ _

#print axioms curlImageCovProj_mem
#print axioms curlImageCovProj_fixes
#print axioms curlImageCovProj_selfAdjoint

/-! ## §11 — `IsBalabanExtensionCov`: the covariant THREE-property characterization, `U`-dependent
term-for-term substitution of `HjMinimizer.lean`'s `IsBalabanExtension` (CMP95 p.29 verbatim,
`∂ → D_U`, `∂* → D_U^*`, `R → R^{cov}(U)`, `Q_k → Q_ell^{cov}`). -/

structure IsBalabanExtensionCov {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (B : LatticeOperators.CoarseBond L ell → SuTwo) (A : Bond L → SuTwo) : Prop where
  interpolates : coarseRestrictCovariantLM L ell A = B
  gaugeFixed : RcovLM U levels (gradCovariantAdjointLM U A) = 0
  orthogonal : ∀ A' ∈ gaugeConstraintSubspaceCov ell levels U,
    covPlaqInner (curlCovariantLM U A') (curlCovariantLM U A) = 0

#print axioms IsBalabanExtensionCov.mk

/-! ## §12 — `H_j^{cov}`: built from a particular solution, unconditional existence, mirroring
`HjMinimizer.lean` §4 with the flat closest-point projection replaced by `curlImageCovProj`. First,
the `covPlaqInner` bilinearity helpers this needs (NOT built in `CovariantHj.lean`, which only has
`self_nonneg`/`symm` — LAW-19 reuse of `hsInner_add_left`/`hsInner_sub_right`, already built §2/§5
of THIS file). -/

theorem covPlaqInner_add_left {L : PeriodicLatticeExtent}
    (A1 A2 B : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner (A1 + A2) B = covPlaqInner A1 B + covPlaqInner A2 B := by
  unfold covPlaqInner
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun p _ => hsInner_add_left (A1 p) (A2 p) (B p))

theorem covPlaqInner_add_right {L : PeriodicLatticeExtent}
    (A B1 B2 : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner A (B1 + B2) = covPlaqInner A B1 + covPlaqInner A B2 := by
  rw [covPlaqInner_symm A (B1 + B2), covPlaqInner_add_left, covPlaqInner_symm B1 A,
    covPlaqInner_symm B2 A]

theorem covPlaqInner_sub_right {L : PeriodicLatticeExtent}
    (A B C : PeriodicLatticePlaquette L → SuTwo) :
    covPlaqInner A (B - C) = covPlaqInner A B - covPlaqInner A C := by
  unfold covPlaqInner
  simp_rw [Pi.sub_apply, hsInner_sub_right]
  rw [Finset.sum_sub_distrib]

#print axioms covPlaqInner_add_left
#print axioms covPlaqInner_add_right
#print axioms covPlaqInner_sub_right

/-- The target correction: `D_UA0 - W^{cov}(U).proj(D_UA0)`, chosen so the result lands in
`W^{cov}(U)ᗮ`. -/
noncomputable def hjCorrectionTargetCov {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : PeriodicLatticePlaquette L → SuTwo :=
  curlCovariantLM U A0 - curlImageCovProj ell levels U (curlCovariantLM U A0)

/-- **The correction target is `covPlaqInner`-orthogonal to `curlImageCov`** — the bare-pairing
analogue of `Submodule.sub_starProjection_mem_orthogonal`, derived by hand from
`curlImageCovProj_selfAdjoint`/`curlImageCovProj_fixes` (no ambient `InnerProductSpace` on the bare
carrier is available to invoke the Mathlib lemma directly). -/
theorem hjCorrectionTargetCov_orthogonal {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) {A' : PeriodicLatticePlaquette L → SuTwo}
    (hA' : A' ∈ curlImageCov ell levels U) :
    covPlaqInner A' (hjCorrectionTargetCov ell levels U A0) = 0 := by
  unfold hjCorrectionTargetCov
  rw [covPlaqInner_sub_right]
  have hstep : covPlaqInner A' (curlImageCovProj ell levels U (curlCovariantLM U A0)) =
      covPlaqInner (curlImageCovProj ell levels U A') (curlCovariantLM U A0) :=
    (curlImageCovProj_selfAdjoint ell levels U A' (curlCovariantLM U A0)).symm
  rw [hstep, curlImageCovProj_fixes ell levels U hA', sub_self]

#print axioms hjCorrectionTargetCov_orthogonal

theorem negCurlImageCovProj_mem_curlImageCov {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    -(curlImageCovProj ell levels U (curlCovariantLM U A0)) ∈ curlImageCov ell levels U :=
  Submodule.neg_mem _ (curlImageCovProj_mem ell levels U (curlCovariantLM U A0))

/-- **`hjCorrectionCov` — a chosen `v ∈ V^{cov}(U)`** with `D_Uv = -W^{cov}(U).proj(D_UA0)`,
mirroring `hjCorrection`. -/
noncomputable def hjCorrectionCov {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : Bond L → SuTwo :=
  (mem_curlImageCov_iff.mp (negCurlImageCovProj_mem_curlImageCov ell levels U A0)).choose

theorem hjCorrectionCov_mem {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    hjCorrectionCov ell levels U A0 ∈ gaugeConstraintSubspaceCov ell levels U :=
  (mem_curlImageCov_iff.mp (negCurlImageCovProj_mem_curlImageCov ell levels U A0)).choose_spec.1

theorem hjCorrectionCov_curl {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    curlCovariantLM U (hjCorrectionCov ell levels U A0) =
      -(curlImageCovProj ell levels U (curlCovariantLM U A0)) :=
  (mem_curlImageCov_iff.mp (negCurlImageCovProj_mem_curlImageCov ell levels U A0)).choose_spec.2

#print axioms negCurlImageCovProj_mem_curlImageCov
#print axioms hjCorrectionCov_mem
#print axioms hjCorrectionCov_curl

/-- **`H_j^{cov}`, built from a particular solution `A0`.** -/
noncomputable def hjExtensionCov {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : Bond L → SuTwo :=
  A0 + hjCorrectionCov ell levels U A0

theorem curlCov_hjExtensionCov {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    curlCovariantLM U (hjExtensionCov ell levels U A0) = hjCorrectionTargetCov ell levels U A0 := by
  unfold hjExtensionCov hjCorrectionTargetCov
  rw [map_add, hjCorrectionCov_curl]
  abel

#print axioms curlCov_hjExtensionCov

/-- **THE MAIN THEOREM: `hjExtensionCov` satisfies `IsBalabanExtensionCov`**, GIVEN that the
particular solution `A0` already interpolates `B` and is gauge-fixed — the SAME honest hypothesis
shape `HjMinimizer.hjExtension_isBalabanExtension` needs (NOT a Poincaré/coercivity assumption).
The SEPARATE, harder content — existence of such an `A0` for an ARBITRARY `B` — is the SAME named
residual `HjMinimizer.lean` already carries (dispatch's own "DO NOT block on it" instruction),
inherited here unchanged, NOT discharged. -/
theorem hjExtensionCov_isBalabanExtensionCov {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (B : LatticeOperators.CoarseBond L ell → SuTwo)
    (h1 : coarseRestrictCovariantLM L ell A0 = B)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0) :
    IsBalabanExtensionCov ell levels U B (hjExtensionCov ell levels U A0) := by
  obtain ⟨hVQ, hVR⟩ := mem_gaugeConstraintSubspaceCov.mp (hjCorrectionCov_mem ell levels U A0)
  refine ⟨?_, ?_, ?_⟩
  · unfold hjExtensionCov
    simp only [map_add, hVQ, h1, add_zero]
  · unfold hjExtensionCov
    simp only [map_add, hVR, h2, add_zero]
  · intro A' hA'
    rw [curlCov_hjExtensionCov]
    exact hjCorrectionTargetCov_orthogonal ell levels U A0 (curl_mem_curlImageCov_of_mem hA')

#print axioms hjExtensionCov_isBalabanExtensionCov

/-! ## §13 — `Δ_j^{cov}(U)`: the Schur complement `⟨B,Δ_j(U)B⟩ := ‖D_U H_j^{cov}(U)B‖²_{L²}`,
CMP99b's `Δ_k(U)` restricted to the `H_j^{cov}` construction — a BOND-indexed object (the dispatch's
own denotation warning: `B`/`A0` here are BOND configurations, matching `dstarDQuadForm`'s own
`⟨A,D*DA⟩ = ‖DA‖²` convention, CMP95 (1.65)/CMP96 (2.116)/CMP99b (3.10)). -/

/-- **`⟨B, Δ_j^{cov}(U)B⟩ := ‖D_U H_j^{cov}(U)B‖²_{L²}`** — the single-bond-`Q` Schur complement
(the faithful-`Q` twin is `CovariantHjFaithful.deltaJQuadFormCovFaithful`).

**[CSTAR-LEVEL-MISMATCH] — LEVEL INDEX OF `A0`, RECORDED (denotation-dictionary finding, not
re-litigated here).** `A0 : Bond L → SuTwo` is a field on this tree's SINGLE fine/unit bond level,
whereas the source objects are UNIT-lattice (`Λ`) forms with the fine level already integrated out:
`compute/denotation_dict/DENOTATION_DICT.tsv` row `delta_k_unit_p428_3156` (CMP99b p.428 (3.156)
`Δ_k`, `src_level = tgt_level = unit (Lambda)`, sector `bond`, dictionary verdict `MISMATCH`) and
row `delta96_j_unit_2118` (CMP96 p.243 (2.118) `Δ_j`, unit→unit). The typed separation that makes
the fine/unit collapse unstateable is `AdalyFormal.Balaban.CStarLevelCorrected.LevelSplit`
(`LevelSplit.ne`), and it is NOT used here. Nothing in this declaration or its proofs is changed by
this note. -/
noncomputable def deltaJQuadFormCov {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : ℝ :=
  covPlaqInner (curlCovariantLM U (hjExtensionCov ell levels U A0))
    (curlCovariantLM U (hjExtensionCov ell levels U A0))

theorem deltaJQuadFormCov_nonneg {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) : 0 ≤ deltaJQuadFormCov ell levels U A0 :=
  covPlaqInner_self_nonneg _

#print axioms deltaJQuadFormCov_nonneg

/-- **`hjCorrectionTargetCov` is invariant under adding a `V^{cov}(U)`-element to `A0`.** -/
theorem hjCorrectionTargetCov_add_of_mem {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 v : Bond L → SuTwo) (hv : v ∈ gaugeConstraintSubspaceCov ell levels U) :
    hjCorrectionTargetCov ell levels U (A0 + v) = hjCorrectionTargetCov ell levels U A0 := by
  unfold hjCorrectionTargetCov
  have hWv : curlCovariantLM U v ∈ curlImageCov ell levels U := curl_mem_curlImageCov_of_mem hv
  have hfix : curlImageCovProj ell levels U (curlCovariantLM U v) = curlCovariantLM U v :=
    curlImageCovProj_fixes ell levels U hWv
  rw [map_add, curlImageCovProj_add, hfix]
  abel

#print axioms hjCorrectionTargetCov_add_of_mem

/-- **`deltaJQuadFormCov` is independent of the choice of particular solution `A0`.** -/
theorem deltaJQuadFormCov_indep_of_particular_solution {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 A0' : Bond L → SuTwo) (B : LatticeOperators.CoarseBond L ell → SuTwo)
    (h1 : coarseRestrictCovariantLM L ell A0 = B)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0)
    (h1' : coarseRestrictCovariantLM L ell A0' = B)
    (h2' : RcovLM U levels (gradCovariantAdjointLM U A0') = 0) :
    deltaJQuadFormCov ell levels U A0 = deltaJQuadFormCov ell levels U A0' := by
  have hVmem : A0' - A0 ∈ gaugeConstraintSubspaceCov ell levels U := by
    rw [mem_gaugeConstraintSubspaceCov]
    refine ⟨?_, ?_⟩
    · rw [map_sub, h1', h1, sub_self]
    · rw [map_sub, map_sub, h2', h2, sub_self]
  have hkey : hjCorrectionTargetCov ell levels U A0' = hjCorrectionTargetCov ell levels U A0 := by
    have heq : A0 + (A0' - A0) = A0' := by abel
    have hstep := hjCorrectionTargetCov_add_of_mem ell levels U A0 (A0' - A0) hVmem
    rw [heq] at hstep
    exact hstep
  unfold deltaJQuadFormCov
  rw [curlCov_hjExtensionCov, curlCov_hjExtensionCov, hkey]

#print axioms deltaJQuadFormCov_indep_of_particular_solution

/-! ## §14 — `H_j^{cov}` is genuinely MINIMAL — the covariant Pythagorean-decomposition theorem,
mirroring `HjMinimizer.lean` §7, with `covPlaqInner` replacing `‖·‖²`/`⟪·,·⟫` throughout (no ambient
`InnerProductSpace` on the bare Pi carrier is used — the Pythagorean identity is derived directly
from `covPlaqInner_add_left`/`covPlaqInner_add_right`, not `norm_add_sq_real`). -/

theorem hjExtensionCov_isMinimal {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 A1 : Bond L → SuTwo) (B : LatticeOperators.CoarseBond L ell → SuTwo)
    (h1 : coarseRestrictCovariantLM L ell A0 = B)
    (h2 : RcovLM U levels (gradCovariantAdjointLM U A0) = 0)
    (h1' : coarseRestrictCovariantLM L ell A1 = B)
    (h2' : RcovLM U levels (gradCovariantAdjointLM U A1) = 0) :
    deltaJQuadFormCov ell levels U A0 ≤
      covPlaqInner (curlCovariantLM U A1) (curlCovariantLM U A1) := by
  have hVmem : A1 - A0 ∈ gaugeConstraintSubspaceCov ell levels U := by
    rw [mem_gaugeConstraintSubspaceCov]
    refine ⟨?_, ?_⟩
    · rw [map_sub, h1', h1, sub_self]
    · rw [map_sub, map_sub, h2', h2, sub_self]
  set p := hjCorrectionTargetCov ell levels U A0 with hp_def
  set q := curlCovariantLM U A1 - p with hq_def
  have hsplit_A1 : curlCovariantLM U A1 = curlCovariantLM U A0 + curlCovariantLM U (A1 - A0) := by
    rw [← map_add]
    congr 1
    abel
  have hwmem : curlCovariantLM U (A1 - A0) ∈ curlImageCov ell levels U :=
    curl_mem_curlImageCov_of_mem hVmem
  have hqeq : q = curlCovariantLM U (A1 - A0) +
      curlImageCovProj ell levels U (curlCovariantLM U A0) := by
    rw [hq_def, hp_def]
    unfold hjCorrectionTargetCov
    rw [hsplit_A1]
    abel
  have hqmem : q ∈ curlImageCov ell levels U := by
    rw [hqeq]
    exact Submodule.add_mem _ hwmem (curlImageCovProj_mem ell levels U (curlCovariantLM U A0))
  have hqp0 : covPlaqInner q p = 0 := hjCorrectionTargetCov_orthogonal ell levels U A0 hqmem
  have hpq0 : covPlaqInner p q = 0 := by rw [covPlaqInner_symm]; exact hqp0
  have hsplit : curlCovariantLM U A1 = p + q := by rw [hq_def]; abel
  have hpyth : covPlaqInner (curlCovariantLM U A1) (curlCovariantLM U A1) =
      covPlaqInner p p + covPlaqInner q q := by
    rw [hsplit, covPlaqInner_add_left, covPlaqInner_add_right, covPlaqInner_add_right, hpq0, hqp0]
    ring
  have hdelta : deltaJQuadFormCov ell levels U A0 = covPlaqInner p p := by
    unfold deltaJQuadFormCov
    rw [curlCov_hjExtensionCov]
  rw [hpyth, hdelta]
  linarith [covPlaqInner_self_nonneg q]

#print axioms hjExtensionCov_isMinimal

/-- **Corollary**: `hjExtensionCov`'s own curl-norm equals `deltaJQuadFormCov` by definition —
confirming `deltaJQuadFormCov`/`hjExtensionCov` are not merely "a solution" but genuinely THE
minimum among ALL competitors (`hjExtensionCov_isMinimal`). -/
theorem hjExtensionCov_achieves_own_minimum {L : PeriodicLatticeExtent} (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    covPlaqInner (curlCovariantLM U (hjExtensionCov ell levels U A0))
      (curlCovariantLM U (hjExtensionCov ell levels U A0)) = deltaJQuadFormCov ell levels U A0 := by
  unfold deltaJQuadFormCov
  rfl

#print axioms hjExtensionCov_achieves_own_minimum

/-! ## §15 — THE `U`-DEPENDENCE WITNESS (the property that justifies the whole exercise): at
`ell = 1`, `Q_1^{cov}` is INJECTIVE (a block of side `1` is a singleton, `KernelSubspace.
blockOf_one_eq_singleton`, LAW-19), so `V^{cov}(U) = ⊥` for EVERY `U`/`levels` — the correction step
vanishes IDENTICALLY, and `deltaJQuadFormCov` reduces EXACTLY to `CovariantHj.dstarDQuadForm`,
transferring the ALREADY-PROVED `dstarDQuadForm_genuinely_U_dependent` (concrete values `0`
at `myTrivialU`, `4` at `witnessU`, on `myWitnessConfig` — CovariantHj.lean §4) DIRECTLY.

**Named limitation, disclosed, not hidden**: this witness sits at a DEGENERATE corner of the general
`(ell,levels)` parameter space, where `H_j^{cov}`'s correction/minimality machinery is VACUOUS (not
merely small) — `ell=1` makes `Q_1^{cov}` an isomorphism (up to the `CoarseLattice`/`Bond`
relabeling), so there is no genuine gauge freedom left to correct against. A witness at a
NONTRIVIAL `ell` (where `V^{cov}(U) ≠ ⊥` and the correction genuinely acts, requiring a concrete
particular solution `A0` satisfying `gaugeFixed` for a NONTRIVIAL `R^{cov}(U)`, and a hand computation
of `curlImageCovProj`'s actual nonzero value) is NOT built here — genuinely harder, needing the SAME
inherited "existence of a particular solution" residual `HjMinimizer.lean` already names, PLUS an
explicit nonzero `curlImageCovProj` computation, neither attempted. The BACKGROUND comparison itself
(`myTrivialU` vs `witnessU`: identity vs one-link-perturbed) is NOT degenerate — it is the SAME
non-identity witness pattern already used throughout this tree for genuine `U`-dependence claims
(§4b/§4's own `adWitnessU`/`trivialU` witnesses), not the "test only at `U=1`" trap the dispatch
warned against. -/

theorem mem_CoarseLattice_one {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) :
    y ∈ AdmissibleSubspace.CoarseLattice L 1 :=
  AdmissibleSubspace.mem_CoarseLattice.mpr (fun _ => Nat.mod_one _)

#print axioms mem_CoarseLattice_one

/-- **`Q_1^{cov}` is injective (kernel trivial)**: a block of side `1` is a singleton
(`KernelSubspace.blockOf_one_eq_singleton`, LAW-19), so the coarse-restriction at `ell=1` recovers
`A'` pointwise EXACTLY. -/
theorem coarseRestrictCovariantLM_one_eq_zero_imp {L : PeriodicLatticeExtent}
    {A' : Bond L → SuTwo} (h : coarseRestrictCovariantLM L 1 A' = 0) : A' = 0 := by
  funext e
  have hy : e.1 ∈ AdmissibleSubspace.CoarseLattice L 1 := mem_CoarseLattice_one e.1
  have hcongr := congrFun h (⟨⟨e.1, hy⟩, e.2⟩)
  simp only [coarseRestrictCovariantLM, coarseRestrictCovariant, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply] at hcongr
  rw [KernelSubspace.blockOf_one_eq_singleton, Finset.sum_singleton] at hcongr
  simpa using hcongr

#print axioms coarseRestrictCovariantLM_one_eq_zero_imp

/-- **`V^{cov}(U) = ⊥` at `ell=1`, for ANY `levels`/`U`** — since membership already REQUIRES the
`Q_1^{cov}A'=0` clause alone, and that clause forces `A'=0` regardless of the second (`R`) clause. -/
theorem gaugeConstraintSubspaceCov_ell1_eq_bot {L : PeriodicLatticeExtent}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    gaugeConstraintSubspaceCov 1 levels U = ⊥ := by
  ext A'
  rw [Submodule.mem_bot, mem_gaugeConstraintSubspaceCov]
  constructor
  · rintro ⟨h1, _⟩
    exact coarseRestrictCovariantLM_one_eq_zero_imp h1
  · rintro rfl
    exact ⟨map_zero _, by rw [map_zero, map_zero]⟩

theorem curlImageCov_ell1_eq_bot {L : PeriodicLatticeExtent}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    curlImageCov 1 levels U = ⊥ := by
  unfold curlImageCov
  rw [gaugeConstraintSubspaceCov_ell1_eq_bot]
  exact Submodule.map_bot _

theorem curlImageCovH_ell1_eq_bot {L : PeriodicLatticeExtent}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    curlImageCovH 1 levels U = ⊥ := by
  unfold curlImageCovH
  rw [curlImageCov_ell1_eq_bot]
  exact Submodule.map_bot _

#print axioms gaugeConstraintSubspaceCov_ell1_eq_bot
#print axioms curlImageCov_ell1_eq_bot
#print axioms curlImageCovH_ell1_eq_bot

/-- **`curlImageCovProj ≡ 0` at `ell=1`, for ANY `A`/`levels`/`U`** — projecting onto the trivial
target subspace is the zero map. -/
theorem curlImageCovProj_ell1_eq_zero {L : PeriodicLatticeExtent}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH 1 levels U).HasOrthogonalProjection]
    (A : PeriodicLatticePlaquette L → SuTwo) :
    curlImageCovProj 1 levels U A = 0 := by
  unfold curlImageCovProj
  have hmem : (curlImageCovH 1 levels U).starProjection ((plaqFnEquiv L).symm A) ∈
      curlImageCovH 1 levels U := Submodule.starProjection_apply_mem _ _
  have hzero : (curlImageCovH 1 levels U).starProjection ((plaqFnEquiv L).symm A) = 0 := by
    have hbot := curlImageCovH_ell1_eq_bot (L := L) (levels := levels) (U := U)
    rw [Submodule.eq_bot_iff] at hbot
    exact hbot _ hmem
  rw [hzero, map_zero]

#print axioms curlImageCovProj_ell1_eq_zero

/-- **The correction step is a NO-OP at `ell=1`**: `hjCorrectionTargetCov` reduces to the bare curl
of `A0`, no projection subtracted. -/
theorem hjCorrectionTargetCov_ell1_eq_curl {L : PeriodicLatticeExtent}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH 1 levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    hjCorrectionTargetCov 1 levels U A0 = curlCovariantLM U A0 := by
  unfold hjCorrectionTargetCov
  rw [curlImageCovProj_ell1_eq_zero]
  abel

#print axioms hjCorrectionTargetCov_ell1_eq_curl

/-- **THE REDUCTION**: at `ell=1`, `deltaJQuadFormCov` equals `CovariantHj.dstarDQuadForm` EXACTLY —
`H_j^{cov}`'s Schur complement collapses to CMP99b (3.10)'s bare `⟨A,D*DA⟩` term, since there is no
gauge freedom left to correct against. -/
theorem deltaJQuadFormCov_ell1_eq_dstarDQuadForm {L : PeriodicLatticeExtent}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovH 1 levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    deltaJQuadFormCov 1 levels U A0 = CovariantHj.dstarDQuadForm U A0 := by
  unfold deltaJQuadFormCov CovariantHj.dstarDQuadForm
  rw [curlCov_hjExtensionCov, hjCorrectionTargetCov_ell1_eq_curl]
  rfl

#print axioms deltaJQuadFormCov_ell1_eq_dstarDQuadForm

/-- **THE HEADLINE RESULT: `deltaJQuadFormCov` is genuinely `U`-DEPENDENT.** Two backgrounds
`myTrivialU ≠ witnessU`, same underlying bond field `myWitnessConfig`, same `(ell,levels) = (1,[])`
covariant `H_j`-construction, DIFFERENT `Δ_j^{cov}(U)` values (`0` vs `4`, transferred verbatim from
`CovariantHj.dstarDQuadForm_genuinely_U_dependent` via the exact reduction above) — the property
`HjMinimizer.deltaJQuadForm` was PROVED to structurally LACK (`DELTA_J_PINNING.md`'s flat
`U`-independence pin), now genuinely present in the covariant `H_j^{cov}` construction assembled in
this file. -/
theorem deltaJQuadFormCov_genuinely_U_dependent :
    deltaJQuadFormCov 1 ([] : List (KernelSubspace.Level AdmissibleSubspace.witnessL))
        myTrivialU myWitnessConfig ≠
      deltaJQuadFormCov 1 ([] : List (KernelSubspace.Level AdmissibleSubspace.witnessL))
        witnessU myWitnessConfig := by
  rw [deltaJQuadFormCov_ell1_eq_dstarDQuadForm, deltaJQuadFormCov_ell1_eq_dstarDQuadForm]
  exact dstarDQuadForm_genuinely_U_dependent

#print axioms deltaJQuadFormCov_genuinely_U_dependent

/-! ## §16 — CLOSING THE §15 RESIDUAL: THE NON-DEGENERACY THRESHOLD

§15 disclosed, honestly, that its `U`-dependence witness sits at `ell=1`, where `Q_1^{cov}` is
INJECTIVE, so `V^{cov}(U) = ⊥` for every `U` and the correction step is a NO-OP: `deltaJQuadFormCov`
transfers verbatim from `CovariantHj.dstarDQuadForm`, so the covariant `H_j` MINIMIZATION machinery
(§9-§14, the reason this file exists) was never actually exercised. This section finds the
threshold where that stops being true, and exercises the machinery for real.

**The threshold.** `blockOf y ell` is a singleton (hence `Q_ell^{cov}` injective, `KernelSubspace.
blockOf_one_eq_singleton`, already used at §15) ONLY at `ell=1`. Already at `ell=2 =
AdmissibleSubspace.witnessEll` — the SMALLEST `ell>1` this tree's witness lattice supports, already
used elsewhere (`KernelSubspace.witnessLevel1`, `CoarseCurl.lean`'s own `witnessEll=2` docstring) —
`blockOf witnessY witnessEll` has `8` sites (`AdmissibleSubspace.card_blockOf`), so `Q_2^{cov}` is
FAR from injective: §16d below exhibits an EXPLICIT nonzero element of its kernel.

**Scope pin, stated up front (S83/OPS-1 discipline — not discovered mid-proof).** The witness below
uses a SPECIFIC, disclosed choice of `levels`: `oneLevelUniv L := [(1, Finset.univ)]`, chosen because
it forces `kernelSubspaceCov (oneLevelUniv L) = ⊥` (§16a), which forces `R^{cov}(U) ≡ 0`
UNIVERSALLY — for every input, every `U` (§16b). Consequently `V^{cov}(U)`'s SECOND (gauge-fixing)
defining clause collapses to a TAUTOLOGY and its FIRST clause is exactly `ker(Q_ell^{cov})`, for
EVERY `U` simultaneously (§16c). **This is a genuine, disclosed SIMPLIFICATION**: it demonstrates
`V^{cov}(U) ≠ ⊥` via the coarse-restriction kernel ALONE, exercising a DIFFERENT sub-family of the
`(ell,levels)` parameter space than `witnessLevels`/`[]` used elsewhere in this tree — it does NOT
exhibit a case where the gauge-fixing clause does genuine additional cutting-down work. §21 below
states precisely what this simplification costs (why it is not yet enough to witness `deltaJQuadFormCov`
itself differing across backgrounds) and names the exact residual, per OPS-1 ("evidence of
resistance", not a bare label). -/

/-- **`oneLevelUniv L := [(1, univ)]`** — the single "every site pinned at `ell=1`" level, for ANY
`L`. -/
def oneLevelUniv (L : PeriodicLatticeExtent) : List (KernelSubspace.Level L) :=
  [(1, (Finset.univ : Finset (PeriodicLatticeSite L)))]

/-- `Q_1'^{cov} = id` — the covariant analogue of `KernelSubspace.coarseRestrictSite_one_eq_self`
(same proof shape, `SuTwo`-valued carrier). -/
theorem coarseRestrictSiteCovariant_one_eq_self {L : PeriodicLatticeExtent}
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    coarseRestrictSiteCovariant 1 lam y = lam y := by
  unfold coarseRestrictSiteCovariant
  rw [KernelSubspace.blockOf_one_eq_singleton, Finset.sum_singleton]
  norm_num

#print axioms coarseRestrictSiteCovariant_one_eq_self

/-- **`kernelSubspaceCov (oneLevelUniv L) = ⊥`** — forcing the covariant site-level kernel
subspace trivial, for ANY `L`. -/
theorem kernelSubspaceCov_oneLevelUniv_eq_bot {L : PeriodicLatticeExtent} :
    kernelSubspaceCov (oneLevelUniv L) = ⊥ := by
  ext lam
  rw [Submodule.mem_bot, mem_kernelSubspaceCov]
  constructor
  · intro h
    funext y
    have hy := h (1, Finset.univ) (by simp [oneLevelUniv]) y (Finset.mem_univ y)
    rw [coarseRestrictSiteCovariant_one_eq_self] at hy
    exact hy
  · rintro rfl
    intro lvl hlvl y _
    simp only [oneLevelUniv, List.mem_singleton] at hlvl
    subst hlvl
    simp [coarseRestrictSiteCovariant]

#print axioms kernelSubspaceCov_oneLevelUniv_eq_bot

/-- **`Δ₀^{cov}(U)(N(Q')^{cov}) = ⊥` at `oneLevelUniv L`, for ANY `U`** — the target subspace of the
closest-point projection `R^{cov}(U)` collapses, universally in `U`, once the site-level kernel is
forced trivial. -/
theorem deltaKernelImageCov_oneLevelUniv_eq_bot {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    deltaKernelImageCov U (oneLevelUniv L) = ⊥ := by
  unfold deltaKernelImageCov
  rw [kernelSubspaceCov_oneLevelUniv_eq_bot, Submodule.map_bot]

theorem deltaKernelImageCovH_oneLevelUniv_eq_bot {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    deltaKernelImageCovH U (oneLevelUniv L) = ⊥ := by
  unfold deltaKernelImageCovH
  rw [deltaKernelImageCov_oneLevelUniv_eq_bot, Submodule.map_bot]

#print axioms deltaKernelImageCov_oneLevelUniv_eq_bot
#print axioms deltaKernelImageCovH_oneLevelUniv_eq_bot

/-- **`R^{cov}(U) ≡ 0` universally at `oneLevelUniv L`** — projecting onto the (now trivial) target
subspace is the zero map, for ANY input, ANY `U` — the direct covariant analogue of
`curlImageCovProj_ell1_eq_zero`'s own bot-collapse argument, one construction stage earlier. -/
theorem RcovFun_oneLevelUniv_eq_zero {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection]
    (A : PeriodicLatticeSite L → SuTwo) :
    RcovFun U (oneLevelUniv L) A = 0 := by
  unfold RcovFun
  have hmem : (deltaKernelImageCovH U (oneLevelUniv L)).starProjection ((siteFnEquiv L).symm A) ∈
      deltaKernelImageCovH U (oneLevelUniv L) := Submodule.starProjection_apply_mem _ _
  have hzero : (deltaKernelImageCovH U (oneLevelUniv L)).starProjection ((siteFnEquiv L).symm A)
      = 0 := by
    have hbot := deltaKernelImageCovH_oneLevelUniv_eq_bot (L := L) U
    rw [Submodule.eq_bot_iff] at hbot
    exact hbot _ hmem
  rw [hzero, map_zero]

theorem RcovLM_oneLevelUniv_eq_zero {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection]
    (A : PeriodicLatticeSite L → SuTwo) :
    RcovLM U (oneLevelUniv L) A = 0 :=
  RcovFun_oneLevelUniv_eq_zero U A

#print axioms RcovFun_oneLevelUniv_eq_zero
#print axioms RcovLM_oneLevelUniv_eq_zero

/-- **`V^{cov}(U) = ker(Q_ell^{cov})` at `oneLevelUniv L`, for ANY `ell`, ANY `U`** — the covariant
gauge-tangent subspace collapses to EXACTLY the coarse-restriction kernel, decoupled from `U`
entirely, once the gauge-fixing clause is forced trivial (§16b). -/
theorem gaugeConstraintSubspaceCov_oneLevelUniv_eq_ker {L : PeriodicLatticeExtent} (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U (oneLevelUniv L)).HasOrthogonalProjection] :
    gaugeConstraintSubspaceCov ell (oneLevelUniv L) U =
      LinearMap.ker (coarseRestrictCovariantLM L ell) := by
  ext A'
  rw [LinearMap.mem_ker, mem_gaugeConstraintSubspaceCov]
  constructor
  · rintro ⟨h1, -⟩
    exact h1
  · intro h1
    exact ⟨h1, RcovLM_oneLevelUniv_eq_zero U _⟩

#print axioms gaugeConstraintSubspaceCov_oneLevelUniv_eq_ker

/-! ## §17 — THE NONZERO KERNEL WITNESS, at `ell = witnessEll = 2`

Reuses `KernelSubspace.kernelWitnessSiteA`/`kernelWitnessSiteB` (LAW-19) — the SAME two-site
cancelling pair already used for the flat/site-level kernel witness (`KernelSubspace.
kernelWitnessLam_block_sum_eq_zero`) and for `compute/pros_a0/ProsA0Test.lean`'s non-vacuity
certificate on the flat side — promoted here to a DIRECTION-`0` BOND field, and re-proves the SAME
"block-sum cancels" fact against `coarseRestrictCovariant`'s bond-level formula instead of
`coarseRestrictSite`'s site-level one. -/

/-- **`nonDegenBondConfig`**: `+suTwoWitness` at `(kernelWitnessSiteA,0)`, `-suTwoWitness` at
`(kernelWitnessSiteB,0)`, `0` elsewhere. -/
noncomputable def nonDegenBondConfig : Bond AdmissibleSubspace.witnessL → SuTwo :=
  fun e => if e = (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3)) then suTwoWitness
    else if e = (KernelSubspace.kernelWitnessSiteB, (0 : Fin 3)) then -suTwoWitness
    else 0

theorem nonDegenBondConfig_at_A :
    nonDegenBondConfig (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3)) = suTwoWitness := by
  simp [nonDegenBondConfig]

theorem kernelWitnessSiteA0_ne_B0 :
    (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3)) ≠
      (KernelSubspace.kernelWitnessSiteB, (0 : Fin 3)) := by
  intro h
  exact KernelSubspace.kernelWitnessSiteA_ne_B (congrArg Prod.fst h)

theorem nonDegenBondConfig_at_B :
    nonDegenBondConfig (KernelSubspace.kernelWitnessSiteB, (0 : Fin 3)) = -suTwoWitness := by
  simp [nonDegenBondConfig, Ne.symm kernelWitnessSiteA0_ne_B0]

theorem nonDegenBondConfig_ne_zero : nonDegenBondConfig ≠ 0 := by
  intro h
  have hc := congrFun h (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3))
  rw [nonDegenBondConfig_at_A] at hc
  exact suTwoWitness_ne_zero hc

#print axioms nonDegenBondConfig_at_A
#print axioms kernelWitnessSiteA0_ne_B0
#print axioms nonDegenBondConfig_at_B
#print axioms nonDegenBondConfig_ne_zero

/-- **THE NON-VACUITY CERTIFICATE**: `nonDegenBondConfig ∈ ker(Q_witnessEll^{cov})` — `Q_2^{cov}`
sends it to `0` on EVERY coarse bond: the two nonzero terms cancel inside `blockOf witnessY
witnessEll`'s own direction-`0` coarse bond (mirroring `KernelSubspace.
kernelWitnessLam_block_sum_eq_zero`'s cancellation exactly), and `AdmissibleSubspace.
coarseLattice_unique` rules out `kernelWitnessSiteA`/`kernelWitnessSiteB` belonging to any OTHER
coarse block, so every other coarse bond sees an all-zero sum. -/
theorem nonDegenBondConfig_mem_ker :
    nonDegenBondConfig ∈
      LinearMap.ker (coarseRestrictCovariantLM AdmissibleSubspace.witnessL
        AdmissibleSubspace.witnessEll) := by
  rw [LinearMap.mem_ker]
  funext b
  show coarseRestrictCovariant AdmissibleSubspace.witnessEll nonDegenBondConfig b = 0
  unfold coarseRestrictCovariant
  by_cases hmu : b.2 = (0 : Fin 3)
  · rw [hmu]
    by_cases hy : b.1.1 = AdmissibleSubspace.witnessY
    · rw [hy]
      rw [← Finset.insert_erase KernelSubspace.kernelWitnessSiteA_mem_block,
        Finset.sum_insert (Finset.notMem_erase _ _)]
      have hBmem' : KernelSubspace.kernelWitnessSiteB ∈
          (AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
            AdmissibleSubspace.witnessEll).erase KernelSubspace.kernelWitnessSiteA :=
        Finset.mem_erase.mpr ⟨KernelSubspace.kernelWitnessSiteA_ne_B.symm,
          KernelSubspace.kernelWitnessSiteB_mem_block⟩
      rw [← Finset.insert_erase hBmem', Finset.sum_insert (Finset.notMem_erase _ _)]
      have hrest : ∀ x ∈ ((AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
          AdmissibleSubspace.witnessEll).erase KernelSubspace.kernelWitnessSiteA).erase
            KernelSubspace.kernelWitnessSiteB,
          nonDegenBondConfig (x, (0 : Fin 3)) = 0 := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_erase] at hx
        obtain ⟨hxB, hxA, -⟩ := hx
        simp only [nonDegenBondConfig]
        have hne1 : (x, (0 : Fin 3)) ≠ (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3)) := by
          intro h; exact hxA (congrArg Prod.fst h)
        have hne2 : (x, (0 : Fin 3)) ≠ (KernelSubspace.kernelWitnessSiteB, (0 : Fin 3)) := by
          intro h; exact hxB (congrArg Prod.fst h)
        rw [if_neg hne1, if_neg hne2]
      have hsum0 : nonDegenBondConfig (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3)) +
          (nonDegenBondConfig (KernelSubspace.kernelWitnessSiteB, (0 : Fin 3)) +
            ∑ x ∈ ((AdmissibleSubspace.blockOf AdmissibleSubspace.witnessY
              AdmissibleSubspace.witnessEll).erase KernelSubspace.kernelWitnessSiteA).erase
                KernelSubspace.kernelWitnessSiteB, nonDegenBondConfig (x, (0 : Fin 3))) = 0 := by
        rw [Finset.sum_eq_zero hrest, nonDegenBondConfig_at_A, nonDegenBondConfig_at_B]
        abel
      rw [hsum0, smul_zero]
    · have hAnot : KernelSubspace.kernelWitnessSiteA ∉
          AdmissibleSubspace.blockOf b.1.1 AdmissibleSubspace.witnessEll := by
        intro hmemA
        exact hy (AdmissibleSubspace.coarseLattice_unique AdmissibleSubspace.witnessEll b.1.2
          AdmissibleSubspace.witnessY_coarse hmemA KernelSubspace.kernelWitnessSiteA_mem_block)
      have hBnot : KernelSubspace.kernelWitnessSiteB ∉
          AdmissibleSubspace.blockOf b.1.1 AdmissibleSubspace.witnessEll := by
        intro hmemB
        exact hy (AdmissibleSubspace.coarseLattice_unique AdmissibleSubspace.witnessEll b.1.2
          AdmissibleSubspace.witnessY_coarse hmemB KernelSubspace.kernelWitnessSiteB_mem_block)
      have hzero : ∀ x ∈ AdmissibleSubspace.blockOf b.1.1 AdmissibleSubspace.witnessEll,
          nonDegenBondConfig (x, (0 : Fin 3)) = 0 := by
        intro x hx
        simp only [nonDegenBondConfig]
        have hne1 : (x, (0 : Fin 3)) ≠ (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3)) := by
          intro h
          have hxA : x = KernelSubspace.kernelWitnessSiteA := congrArg Prod.fst h
          exact hAnot (hxA ▸ hx)
        have hne2 : (x, (0 : Fin 3)) ≠ (KernelSubspace.kernelWitnessSiteB, (0 : Fin 3)) := by
          intro h
          have hxB : x = KernelSubspace.kernelWitnessSiteB := congrArg Prod.fst h
          exact hBnot (hxB ▸ hx)
        rw [if_neg hne1, if_neg hne2]
      rw [Finset.sum_eq_zero hzero, smul_zero]
  · have hzero : ∀ x ∈ AdmissibleSubspace.blockOf b.1.1 AdmissibleSubspace.witnessEll,
        nonDegenBondConfig (x, b.2) = 0 := by
      intro x _
      simp only [nonDegenBondConfig]
      have hne1 : (x, b.2) ≠ (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3)) := by
        intro h; exact hmu (congrArg Prod.snd h)
      have hne2 : (x, b.2) ≠ (KernelSubspace.kernelWitnessSiteB, (0 : Fin 3)) := by
        intro h; exact hmu (congrArg Prod.snd h)
      rw [if_neg hne1, if_neg hne2]
    rw [Finset.sum_eq_zero hzero, smul_zero]

#print axioms nonDegenBondConfig_mem_ker

/-! ## §18 — REQUIREMENT 1 MET: `V^{cov}(U) ≠ ⊥` AT THE NON-DEGENERACY THRESHOLD, for EVERY `U`
simultaneously (STRONGER than "a concrete choice") -/

theorem gaugeConstraintSubspaceCov_witnessEll_ne_bot
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdmissibleSubspace.witnessL)
    [(deltaKernelImageCovH U (oneLevelUniv AdmissibleSubspace.witnessL)).HasOrthogonalProjection] :
    gaugeConstraintSubspaceCov AdmissibleSubspace.witnessEll
        (oneLevelUniv AdmissibleSubspace.witnessL) U ≠ ⊥ := by
  rw [gaugeConstraintSubspaceCov_oneLevelUniv_eq_ker]
  intro hbot
  apply nonDegenBondConfig_ne_zero
  rw [← Submodule.mem_bot (R := ℝ), ← hbot]
  exact nonDegenBondConfig_mem_ker

#print axioms gaugeConstraintSubspaceCov_witnessEll_ne_bot

/-! ## §19 — THE WITNESS BACKGROUND IS GENUINELY NON-CENTRAL (Sol-family gate correction,
`compute/sol_carrier_gate/SOL_CARRIER_GATE.md`): `Ad(-I) = Ad(I) = id`, so "differs from the
identity" is NOT sufficient — the background must move a Lie-algebra element. `witnessMElem`
(`CovariantOperators.lean`, the single differing link of BOTH `witnessU` and `BondSU2Space.lean`'s
`adWitnessU`) already does: `RMap_witnessMElem` sends `suTwoWitness ↦ -suTwoWitness`, so `Ad
(witnessMElem) ≠ id` — proved directly below, not asserted, closing the exact gap the correction
named. This is the SAME `witnessMElem` `adWitnessU` uses (§4b of this file), so that witness passes
the same check; reported, not edited (out of write scope). -/

theorem RMap_witnessMElem_ne_id : RMap witnessMElem ≠ LinearMap.id := by
  intro h
  have hpt := DFunLike.congr_fun h suTwoWitness
  rw [RMap_witnessMElem, LinearMap.id_apply] at hpt
  exact suTwoWitness_ne_neg_self hpt.symm

#print axioms RMap_witnessMElem_ne_id

/-- The witness plaquette this section's curl computation runs at: based at `kernelWitnessSiteA`,
directions `(0,1)`. -/
def nonDegenWitnessPlaquette : PeriodicLatticePlaquette AdmissibleSubspace.witnessL :=
  (KernelSubspace.kernelWitnessSiteA, ⟨(0, 1), by decide⟩)

/-- **`curl_{witnessU}(nonDegenBondConfig) ≠ 0`** — the raw covariant curl of the kernel witness is
nonzero at the genuinely non-central background `witnessU` (§19's own non-centrality proof applies
to it). Every `U`-slot this plaquette's curl formula touches is based at `kernelWitnessSiteA`, which
is `≠ witnessY`, so `witnessU` (nontrivial ONLY at `(witnessY,0)`) evaluates to `1` at every slot
here — the value is consequently the SAME one a flat computation would give; disclosed, not hidden
(§21 states exactly what this does and does not establish). -/
theorem curlValueCovariant_witnessU_nonDegenBondConfig_ne_zero :
    curlValueCovariant witnessU nonDegenBondConfig nonDegenWitnessPlaquette ≠ 0 := by
  have hval : curlValueCovariant witnessU nonDegenBondConfig nonDegenWitnessPlaquette
      = suTwoWitness := by
    have hA0 : witnessU (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3)) = 1 := by
      simp only [witnessU, ite_eq_right_iff]
      intro h; exact absurd h (by decide)
    have hA1 : witnessU (KernelSubspace.kernelWitnessSiteA, (1 : Fin 3)) = 1 := by
      simp only [witnessU, ite_eq_right_iff]
      intro h; exact absurd h (by decide)
    have hshiftA0 : nonDegenBondConfig
        (periodicLatticeShift KernelSubspace.kernelWitnessSiteA 0, (1 : Fin 3)) = 0 := by
      simp only [nonDegenBondConfig]
      rw [if_neg (by decide), if_neg (by decide)]
    have hshiftA1 : nonDegenBondConfig
        (periodicLatticeShift KernelSubspace.kernelWitnessSiteA 1, (0 : Fin 3)) = 0 := by
      simp only [nonDegenBondConfig]
      rw [if_neg (by decide), if_neg (by decide)]
    have hA1val : nonDegenBondConfig (KernelSubspace.kernelWitnessSiteA, (1 : Fin 3)) = 0 := by
      simp only [nonDegenBondConfig]
      rw [if_neg (by decide), if_neg (by decide)]
    show nonDegenBondConfig (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3)) +
        RMap (witnessU (KernelSubspace.kernelWitnessSiteA, (0 : Fin 3)))
          (nonDegenBondConfig
            (periodicLatticeShift KernelSubspace.kernelWitnessSiteA 0, (1 : Fin 3))) -
        RMap (witnessU (KernelSubspace.kernelWitnessSiteA, (1 : Fin 3)))
          (nonDegenBondConfig
            (periodicLatticeShift KernelSubspace.kernelWitnessSiteA 1, (0 : Fin 3))) -
        nonDegenBondConfig (KernelSubspace.kernelWitnessSiteA, (1 : Fin 3)) = suTwoWitness
    simp only [hA0, hA1, hshiftA0, hshiftA1, hA1val, nonDegenBondConfig_at_A, map_zero]
    abel
  rw [hval]
  exact suTwoWitness_ne_zero

#print axioms curlValueCovariant_witnessU_nonDegenBondConfig_ne_zero

theorem curlCovariantLM_witnessU_nonDegenBondConfig_ne_zero :
    curlCovariantLM witnessU nonDegenBondConfig ≠ 0 := by
  intro h
  have hpt := congrFun h nonDegenWitnessPlaquette
  exact curlValueCovariant_witnessU_nonDegenBondConfig_ne_zero hpt

#print axioms curlCovariantLM_witnessU_nonDegenBondConfig_ne_zero

/-! ## §20 — REQUIREMENT 3 MET (THE LOAD-BEARING CHECK): THE CORRECTION GENUINELY ACTS

`hjExtensionCov nonDegenBondConfig ≠ nonDegenBondConfig` at `witnessU` — unlike `ell=1` (§15, where
`gaugeConstraintSubspaceCov = ⊥` forces `hjCorrectionCov ≡ 0` for EVERY input), the correction vector
added here is PROVABLY NONZERO, not merely its curl-target. -/

theorem nonDegenBondConfig_mem_gaugeConstraintSubspaceCov
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdmissibleSubspace.witnessL)
    [(deltaKernelImageCovH U (oneLevelUniv AdmissibleSubspace.witnessL)).HasOrthogonalProjection] :
    nonDegenBondConfig ∈ gaugeConstraintSubspaceCov AdmissibleSubspace.witnessEll
      (oneLevelUniv AdmissibleSubspace.witnessL) U := by
  rw [gaugeConstraintSubspaceCov_oneLevelUniv_eq_ker]
  exact nonDegenBondConfig_mem_ker

#print axioms nonDegenBondConfig_mem_gaugeConstraintSubspaceCov

theorem curlImageCovProj_witnessU_fixes_nonDegenBondConfig_curl
    [(deltaKernelImageCovH witnessU
        (oneLevelUniv AdmissibleSubspace.witnessL)).HasOrthogonalProjection]
    [(curlImageCovH AdmissibleSubspace.witnessEll (oneLevelUniv AdmissibleSubspace.witnessL)
        witnessU).HasOrthogonalProjection] :
    curlImageCovProj AdmissibleSubspace.witnessEll (oneLevelUniv AdmissibleSubspace.witnessL)
        witnessU (curlCovariantLM witnessU nonDegenBondConfig) =
      curlCovariantLM witnessU nonDegenBondConfig := by
  apply curlImageCovProj_fixes
  exact curl_mem_curlImageCov_of_mem (nonDegenBondConfig_mem_gaugeConstraintSubspaceCov witnessU)

#print axioms curlImageCovProj_witnessU_fixes_nonDegenBondConfig_curl

theorem hjCorrectionCov_witnessU_nonDegenBondConfig_ne_zero
    [(deltaKernelImageCovH witnessU
        (oneLevelUniv AdmissibleSubspace.witnessL)).HasOrthogonalProjection]
    [(curlImageCovH AdmissibleSubspace.witnessEll (oneLevelUniv AdmissibleSubspace.witnessL)
        witnessU).HasOrthogonalProjection] :
    hjCorrectionCov AdmissibleSubspace.witnessEll (oneLevelUniv AdmissibleSubspace.witnessL)
      witnessU nonDegenBondConfig ≠ 0 := by
  intro h
  apply curlCovariantLM_witnessU_nonDegenBondConfig_ne_zero
  have hcurl := hjCorrectionCov_curl AdmissibleSubspace.witnessEll
    (oneLevelUniv AdmissibleSubspace.witnessL) witnessU nonDegenBondConfig
  rw [h, map_zero] at hcurl
  rw [curlImageCovProj_witnessU_fixes_nonDegenBondConfig_curl] at hcurl
  have hzero : curlCovariantLM witnessU nonDegenBondConfig = 0 := by
    have hneg := hcurl.symm
    rwa [neg_eq_zero] at hneg
  exact hzero

#print axioms hjCorrectionCov_witnessU_nonDegenBondConfig_ne_zero

/-- **THE HEADLINE CLOSURE**: at `ell = witnessEll = 2`, the covariant `H_j` construction genuinely
DOES something — `hjExtensionCov` moves its particular solution, not merely its curl-image. -/
theorem hjExtensionCov_witnessU_nonDegenBondConfig_ne_self
    [(deltaKernelImageCovH witnessU
        (oneLevelUniv AdmissibleSubspace.witnessL)).HasOrthogonalProjection]
    [(curlImageCovH AdmissibleSubspace.witnessEll (oneLevelUniv AdmissibleSubspace.witnessL)
        witnessU).HasOrthogonalProjection] :
    hjExtensionCov AdmissibleSubspace.witnessEll (oneLevelUniv AdmissibleSubspace.witnessL)
      witnessU nonDegenBondConfig ≠ nonDegenBondConfig := by
  intro h
  apply hjCorrectionCov_witnessU_nonDegenBondConfig_ne_zero
  have h1 : nonDegenBondConfig +
      hjCorrectionCov AdmissibleSubspace.witnessEll (oneLevelUniv AdmissibleSubspace.witnessL)
        witnessU nonDegenBondConfig = nonDegenBondConfig := h
  have h3 : hjCorrectionCov AdmissibleSubspace.witnessEll (oneLevelUniv AdmissibleSubspace.witnessL)
      witnessU nonDegenBondConfig =
      (nonDegenBondConfig +
        hjCorrectionCov AdmissibleSubspace.witnessEll (oneLevelUniv AdmissibleSubspace.witnessL)
          witnessU nonDegenBondConfig) - nonDegenBondConfig := by abel
  rw [h3, h1, sub_self]

#print axioms hjExtensionCov_witnessU_nonDegenBondConfig_ne_self

/-! ## §21 — REQUIREMENT 2, NAMED PRECISELY AS A RESIDUAL (OPS-1: evidence of resistance, not a
bare label)

The dispatch's Step 2 additionally asks for `deltaJQuadFormCov` itself (the POST-minimization Schur
complement, not the raw curl) to take DIFFERENT values across two backgrounds at this nontrivial
`ell`. **This is NOT established here** — here is exactly what was tried and why it falls short.

**What holds unconditionally** (proved below, `deltaJQuadFormCov_eq_zero_of_mem_ker`): for `oneLevelUniv`,
ANY `A0 ∈ ker(Q_ell^{cov})` gives `deltaJQuadFormCov ell (oneLevelUniv L) U A0 = 0`, for EVERY `U`.
Reason: `A0` is already its own gauge-fixed representative of `B := 0`, so `curl_U(A0)` already lies
in `curlImageCov(...,U)` (§20's own `curl_mem_curlImageCov_of_mem`), and `curlImageCovProj` FIXES
points already inside the subspace it projects onto (`curlImageCovProj_fixes`) — so the correction
exactly cancels `curl_U(A0)` regardless of whether that curl is zero or not, and regardless of `U`.

**Why `nonDegenBondConfig` itself cannot witness Step 2.** It is exactly such an `A0` (§18's own
membership proof) — so `deltaJQuadFormCov ell (oneLevelUniv L) trivialU nonDegenBondConfig =
deltaJQuadFormCov ell (oneLevelUniv L) witnessU nonDegenBondConfig = 0` identically, by the lemma
below. A genuine `U`-dependence witness for `deltaJQuadFormCov` needs an `A0` OUTSIDE
`ker(Q_ell^{cov})` (representing a genuinely nonzero coarse bond `B`), for which `hjExtensionCov_
isMinimal`'s reflexive bound only gives `0 ≤ deltaJQuadFormCov(...,A0) ≤ ‖curl_U(A0)‖²` — an upper
bound, not an exact value, when `curl_U(A0) ≠ 0`. Pinning the EXACT value (in particular, proving it
is strictly POSITIVE at one background while `0` at the other) needs ONE of: (a) the closest-point
projection formula onto `curlCovariantLM(U) '' ker(Q_2^{cov})` in closed form — this subspace's
dimension was not computed here but is large (the coarse-restriction map onto `24` scalar-`SuTwo`-
valued coarse bonds out of `192` fine bonds, so the kernel is generically codimension `≤72`, i.e.
dimension `≥120`, no compact basis/Gram matrix built); or (b) a linear functional vanishing
identically on the WHOLE of that image subspace but nonzero on `curl_U(A0)` for the chosen witness —
NEITHER attempted. This is the exact transpose of the "existence of a particular solution" residual
`HjMinimizer.lean`/§12's docstring already carry: THAT residual is existence of a minimizer for an
ARBITRARY coarse target; THIS one is POSITIVITY of the resulting minimized quadratic form for a
SPECIFIC target, one stage further into the same construction, genuinely harder, not attempted
further within this dispatch's scope. -/

theorem deltaJQuadFormCov_eq_zero_of_mem_ker
    (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
      AdmissibleSubspace.witnessL)
    [(deltaKernelImageCovH U (oneLevelUniv AdmissibleSubspace.witnessL)).HasOrthogonalProjection]
    [(curlImageCovH ell (oneLevelUniv AdmissibleSubspace.witnessL) U).HasOrthogonalProjection]
    (A0 : Bond AdmissibleSubspace.witnessL → SuTwo)
    (hA0 : A0 ∈ LinearMap.ker (coarseRestrictCovariantLM AdmissibleSubspace.witnessL ell)) :
    deltaJQuadFormCov ell (oneLevelUniv AdmissibleSubspace.witnessL) U A0 = 0 := by
  have hmem : A0 ∈ gaugeConstraintSubspaceCov ell (oneLevelUniv AdmissibleSubspace.witnessL) U := by
    rw [gaugeConstraintSubspaceCov_oneLevelUniv_eq_ker]
    exact hA0
  have hfix := curlImageCovProj_fixes ell (oneLevelUniv AdmissibleSubspace.witnessL) U
    (curl_mem_curlImageCov_of_mem hmem)
  unfold deltaJQuadFormCov
  rw [curlCov_hjExtensionCov]
  show covPlaqInner (hjCorrectionTargetCov ell (oneLevelUniv AdmissibleSubspace.witnessL) U A0)
    (hjCorrectionTargetCov ell (oneLevelUniv AdmissibleSubspace.witnessL) U A0) = 0
  unfold hjCorrectionTargetCov
  rw [hfix, sub_self]
  have hz : hsInner (0 : SuTwo) (0 : SuTwo) = 0 := by
    rw [← hsInnerLeftLM_apply]
    exact map_zero _
  unfold covPlaqInner
  simp only [Pi.zero_apply, hz, Finset.sum_const_zero]

#print axioms deltaJQuadFormCov_eq_zero_of_mem_ker

end AdalyFormal.Balaban.CovariantHjMinimizer
