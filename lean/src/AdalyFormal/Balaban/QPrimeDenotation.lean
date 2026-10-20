/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.GammaContourTree
import AdalyFormal.Balaban.CoarseRestrictTransported
import AdalyFormal.Balaban.QjComposite
import AdalyFormal.Balaban.ComposedCoercivity
import AdalyFormal.Balaban.ReparamCDisjoint

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

/-!
# `QPrimeDenotation.lean` — `Q′` PINNED AT ITS DEFINING EQUATION, and `hmean` WIRED OUT

Lane record: `compute/qprime_denotation/PROGRESS.md`.
Denotation authority: `compute/qprime_denotation/QPRIME_READ.md`.

## §0 — THE SOURCE, quoted

**CMP99b printed p.393**, the three-line display tagged (3.18) (first line) / (3.19) (last line).
The one-step operator is the MIDDLE line, which carries **no printed equation tag** — read at
`corpus/renders/CMP99b_p393-05.png`, sha256
`bfab586ad2ebd8dea88c5aa93bdabe4622bacc3c28535603b5f6af17ec71383d`, whole page at 400 dpi and again
at 2x zoom on the display:

```
where Q'λ is defined on 𝔅 = ⋃_{j=0}^{k} Λ_j by the formulas

    (Q'λ)(y)      = (Q'_j(U)λ)(y)     for y ∈ Λ_j,                                        (3.18)

    (Q'(V)λ)(y)   = Σ_{x ∈ B(y)} L^{-d} R(V(Γ_{y,x})) λ(x),                    [NO PRINTED TAG]

    (Q'_j(U)λ)(y) = (Q'(Ū^{j-1})· … ·Q'(Ū)Q'(U)λ)(y)
                  = Σ_{x ∈ B^j(y)} L^{-jd} R(U(Γ^{(j)}_{y,x})) λ(x),   y ∈ T^{(j)}_{L^jη}. (3.19)
```

and, on the same page, fixing the SPACE: *"The norm ‖·‖ in (3.17) is determined by the scalar
product ⟨λ,λ'⟩ = Σ_{x∈Ω₀} η^d tr λ(x)λ'(x) in the Hilbert space L²(Ω₀, 𝔤)"* — `λ` is a SITE-indexed,
LIE-ALGEBRA-valued gauge parameter, and `Q'λ` lives on the COARSE set `𝔅`.

`Q′` enters through the gauge-fixing density (3.17) as `δ(Q′λ)`, so the object with content is the
KERNEL `N(Q′)`, not the operator's scale.

**Independent earlier printing — CMP95 printed p.19 (1.13)**, read at
`corpus/renders/CMP95_p19-03.png`, sha256
`487414cfbd696d345de8ede6f6e74f9e9c1bd160fb32221fbe4b23c50cee00b9`:

```
B^λ_c = B_c − L^{-1}( Σ_{x∈B(c₊)} L^{-d}λ(x) − Σ_{x∈B(c₋)} L^{-d}λ(x) )
      = B_c − L^{-1}((Q'λ)(c₊) − (Q'λ)(c₋)) = B_c − (∂Q'λ)(c).                            (1.13)

Fixing it we restrict the gauge transformations by the condition (Q'λ)(y) = 0.
```

i.e. `(Q'λ)(y) = Σ_{x∈B(y)} L^{-d} λ(x)` at trivial background — same index set `B(y)`, same
prefactor `L^{-d}`, same argument `λ`, and the same KERNEL role. §6 below proves our operator
reduces to exactly this at `U = 1`.

**Correction of an in-tree citation (finding, not repaired here — write-scope).**
`GammaContourTree.lean:823` attributes the `ell^{-d}` prefactor to *"CMP95 (1.8)/(1.11)"*. Read at
the image, CMP95 (1.8) and (1.11) are the UNPRIMED, BOND-sector operator: they act on the bond field
`A`, are indexed by coarse bonds `c = ⟨c₋,c₊⟩`, and print `L^{-(d+1)}`, not `L^{-d}`. The exponent
named is right for `Q′`; the equations cited are the wrong ones. The correct loci are CMP99b p.393's
untagged middle line and CMP95 (1.13). `GammaContourTree.lean` is NOT edited by this lane.

## §1 — WHAT THIS FILE ESTABLISHES

1. **The faithful `Q′` is ALREADY IN THE TREE** (LAW-19 — nothing is rebuilt here):
   `CovarianceG1.QMap (CoarseRestrictTransported.transportedQData U 2 hdvd)` is, item for item,
   the printed formula — sum over `B(y)`, prefactor `L^{-d}`, transport `R(U(Γ_{y,x}))`, and a
   codomain indexed by `AlignedCoarseCenter` (the printed `𝔅`), not by all sites. `QprimeBalaban`
   below is a one-line `abbrev` for its bundled `LinearMap`, introduced only to name it.
2. **`GammaContourTree.QprimeTwo` is NOT that operator**, and the difference is not only the
   dropped scalar: `QprimeTwo` imposes its equation at EVERY site, the printed `Q′` only on `𝔅`.
   §7 exhibits a concrete `λ ≠ 0` on a `4×4×4` torus that lies in `N(Q′)` and NOT in
   `ker QprimeTwo` — so wiring the discharge through `QprimeTwo` would impose a STRICTLY stronger
   hypothesis than Bałaban's gauge-fixing condition.
3. **The bridge, as a kernel theorem** (§3–§4): `staircaseTransport U y (gCorner y p) =
   gammaTransport U y p` for all eight corners, and — §3b, the object `GammaContourTree` §0b names
   VERBATIM — `periodicPathHolonomy U y (Q1Real.GammaPath y (gCorner y p)) = gammaTransport U y p`.
   §0b's exact words are *"This module does NOT prove `gammaTransport = periodicPathHolonomy ∘
   Q1Real.GammaPath`"*; that is the statement closed in §3b, not a nearby substitute. And hence
   `coarseRestrictSiteCovariantU U 2 lam y = (2^3)⁻¹ • Σ_p gammaM U lam y p`, with `2^3` proved
   equal to `(blockOf y 2).card`, never typed in as a magic `8`.
4. **The normalization independence the dead branch ASSUMED, as a theorem** (§5):
   `lam ∈ ker (QprimeBalaban U hdvd) ↔ ∀ y ∈ CoarseLattice L 2, Σ_p gammaM U lam y p = 0`.
   This is the exact `hmean` of `GammaContourTree.gamma_poincare_assembly`.
5. **THE WIRING** (§6): `hlam_at_kappa_sq_768_qprime` and
   `kappa_bound_and_criterion_closes_qprime` carry NO raw `hmean` — only
   `lam ∈ ker (QprimeBalaban U hdvd)`; and `kappa_768_for_gaugeParam_qprime` composes
   `KappaBound.gaugeParam_mem_ker_and_solves` AT THIS OPERATOR so that `λ = G′Rf` discharges it.
   `KappaBound.gaugeParam_mem_ker_and_solves` is stated for `Q : E →ₗ[ℝ] F` with `F` a SEPARATE
   space, so the coarse-indexed codomain is exactly what it wants — no adaptation.

## §1a — WHAT IS NOT CLOSED HERE, STATED AS FACT

* `ell = 2`, `d = 3`, ONE renormalization step (`j = 1`). ~~No `k`-step ladder is built here, and
  none exists in this tree.~~ **CORRECTED IN PLACE (S75), same pass, before this module was
  returned.** The struck sentence was FALSE about the tree: `Balaban/QjComposite.lean` already
  builds the composite `Q'_j` of (3.19)'s FIRST equality, `Qcomposite bg ell j`, with its own
  linearity, locality and tower-dependence controls. Rather than leave a same-shaped operator
  undisclosed, §5a below CLOSES the overlap as a theorem: `QprimeBalaban_eq_Qcomposite_one` proves
  this module's `QprimeBalaban U hdvd` IS `QjComposite.Qcomposite (fun _ => U) 2 1` restricted to
  the coarse centers, i.e. the `j = 1` level of that composite, not a rival object. What is
  genuinely absent is the `Δ_k` RG ladder: (3.19)'s SECOND (`direct`) form is not proved equal to
  the composite there, and no `Δ_k` recursion exists in this tree.
* `Γ_{y,x}` itself is NOT re-adjudicated here: CMP99b p.393 defers it to "(52),(53) in [5]"
  (LAW-12). This lane relies on the `gamma_denotation` lane's first-hand read of CMP95 p.18 (1.7)
  and on `CoarseRestrictTransported`'s `staircaseBonds`, and adds only the identification of the
  two in-tree encodings of it.
* The three hypotheses `hM`/`hG`/`hR` of `gaugeParam_mem_ker_and_solves` remain hypotheses; this
  lane changes WHICH operator they are stated at, not whether they are discharged.
-/

namespace AdalyFormal.Balaban.QPrimeDenotation

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.GeneralUHodgeDrift (siteEnergy)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice
  mem_CoarseLattice coarseLattice_mem_fits card_blockOf AlignedCoarseCenter corner1 corner2)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU coarseRestrictSiteCovariant)
open AdalyFormal.Balaban.GammaContourTree (gInner gCorner gOff gCorner_val gCorner_inj
  blockOf_two_eq_image corner1_gCorner corner2_gCorner gammaTransport gammaM sum_bool3
  site_eq_of_val_eq gamma_poincare_assembly hlam_at_kappa_sq_768_gamma QprimeTwo QprimeTwo_apply)
open AdalyFormal.Balaban.CoarseRestrictTransported (axisBonds pathTransport pathTransport_nil
  pathTransport_append staircaseBonds staircaseTransport coarseRestrictSiteCovariantU
  transportedQData QMap_transportedQData)
open AdalyFormal.Balaban.CovarianceG1 (QMap QLinearMap QLinearMap_apply)
open AdalyFormal.Balaban.FibreCoercivity (zeroSite zeroSite_val zeroSite_coarse)
open AdalyFormal.Balaban.AlphaAnalyticity (norm_RMap)
open AdalyFormal.Balaban.DeltaPrimeBound (deltaPiConst deltaPrimePiForm)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeRegular)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.AxialCoercivity (pAx)
open AdalyFormal.Balaban.GammaRecursion (gammaSeq)
open AdalyFormal.Balaban.ComposedCoercivity (kappaTree gammaFibre AggregateFibreBound bondSup
  deltaPrimePi_bound_kappa_discharged deltaPrimePi_bound_at_regular_U composed_coercivity_general)

variable {L : PeriodicLatticeExtent}

/-! ## §2 — THE INDEX SET: `Σ_{p : Bool³}` IS `Σ_{x ∈ B(y)}`, for values in ANY commutative monoid

`GammaContourTree.sum_block_eq` proves exactly this for `ℝ`-valued `F`. The summands of `Q′` are
`SuTwo`-valued, so the statement is re-proved here at the general `AddCommMonoid` (same two
ingredients, `blockOf_two_eq_image` and `gCorner_inj`, reused unchanged — LAW-19: this is a
generalisation of an existing lemma, not a second copy of its proof idea). -/

/-- Summing over the eight `(1.7)`-ordered corners IS summing over `B(y)`. -/
theorem sum_block_eq_sum_corners {M : Type*} [AddCommMonoid M]
    (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (F : PeriodicLatticeSite L → M) :
    ∑ x ∈ blockOf y 2, F x = ∑ p : Bool × Bool × Bool, F (gCorner y p) := by
  rw [blockOf_two_eq_image y hlt, Finset.sum_image (fun p _ q _ h => gCorner_inj y hlt h)]

/-- The block really has `2³` sites, so the printed prefactor `L^{-d}` at `L = 2`, `d = 3` is the
reciprocal of the COUNTED block size. The `8` used below is this number, not a typed-in constant. -/
theorem card_blockOf_two (y : PeriodicLatticeSite L)
    (hfit : ∀ μ : Fin 3, (y μ).val + 2 ≤ L μ + 1) :
    (blockOf y 2).card = 2 ^ 3 :=
  card_blockOf y 2 hfit

theorem card_blockOf_two_real (y : PeriodicLatticeSite L)
    (hfit : ∀ μ : Fin 3, (y μ).val + 2 ≤ L μ + 1) :
    (((blockOf y 2).card : ℝ)) = (2 : ℝ) ^ (3 : ℕ) := by
  rw [card_blockOf_two y hfit]
  norm_num

/-! ## §3 — THE TWO IN-TREE ENCODINGS OF `Γ_{y,x}` ARE THE SAME TRANSPORT

`GammaContourTree`'s own §0b states as fact that it does NOT prove its corner-indexed
`gammaTransport` equal to any list-based holonomy. This section proves it against
`CoarseRestrictTransported.staircaseTransport`, the general-`ell` ordered product along the
adjudicated `(1.7)` staircase. -/

/-- The `ℕ` offset the staircase's leg lengths use is exactly `gOff`. -/
theorem gCorner_off (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (p : Bool × Bool × Bool) (μ : Fin 3) :
    ((gCorner y p) μ).val - (y μ).val = gOff p μ := by
  rw [gCorner_val y hlt p μ]
  omega

/-- The staircase bond list from `y` to the corner `p`, with both intermediate corners resolved to
`gInner` points and all three leg lengths resolved to `gOff`. -/
theorem staircaseBonds_gCorner (y : PeriodicLatticeSite L)
    (hlt : ∀ μ : Fin 3, (y μ).val < L μ) (p : Bool × Bool × Bool) :
    staircaseBonds y (gCorner y p)
      = axisBonds y 2 (gOff p 2) ++ axisBonds (gInner y false p.2.2) 1 (gOff p 1)
          ++ axisBonds (gInner y p.2.1 p.2.2) 0 (gOff p 0) := by
  unfold staircaseBonds
  rw [corner1_gCorner y hlt p, corner2_gCorner y hlt p, gCorner_off y hlt p 0,
    gCorner_off y hlt p 1, gCorner_off y hlt p 2]

theorem axisBonds_zero (base : PeriodicLatticeSite L) (μ : Fin 3) :
    axisBonds base μ 0 = ([] : List (Bond L)) := rfl

theorem axisBonds_one (base : PeriodicLatticeSite L) (μ : Fin 3) :
    axisBonds base μ 1 = [((base, μ) : Bond L)] := rfl

/-- **THE IDENTIFICATION.** The `ell = 2` corner-indexed transport of `GammaContourTree` IS the
general-`ell` ordered staircase product of `CoarseRestrictTransported`, at every one of the eight
corners. Proved by evaluating both sides; the eight cases are the eight `(a,b,c)`. -/
theorem gammaTransport_eq_staircaseTransport
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (p : Bool × Bool × Bool) :
    staircaseTransport U y (gCorner y p) = gammaTransport U y p := by
  unfold staircaseTransport
  rw [staircaseBonds_gCorner y hlt p]
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;>
    simp [gOff, axisBonds_zero, axisBonds_one, pathTransport, gInner, gammaTransport, mul_assoc]

/-! ### §3b — THE IDENTIFICATION `GammaContourTree` §0b NAMES VERBATIM

§0b of `GammaContourTree.lean` states, in these words: *"This module does NOT prove `gammaTransport
= periodicPathHolonomy ∘ Q1Real.GammaPath`; the anchor it does prove is to `staircasePath` (bond
set) and to `corner1`/`corner2` (intermediate points)."* §3 above connects `gammaTransport` to
`CoarseRestrictTransported.staircaseTransport`, which is a DIFFERENT list-holonomy from the one that
sentence names. This subsection closes the named statement itself, so that the disclosure is
discharged rather than approximated. -/

/-- Coordinate `μ` of a corner is `y μ` shifted by one exactly when `p`'s `μ`-bit is set. -/
theorem gCorner_apply_axis (y : PeriodicLatticeSite L) (p : Bool × Bool × Bool) (μ : Fin 3) :
    (gCorner y p) μ = if gOff p μ = 1 then (periodicLatticeShift y μ) μ else y μ := by
  obtain ⟨a, b, c⟩ := p
  fin_cases μ <;> cases a <;> cases b <;> cases c <;>
    simp [gCorner, gInner, gOff, periodicLatticeShift, Function.update] <;> try rfl

/-- `gInner` never touches coordinate `0`. -/
theorem gInner_apply_zero (y : PeriodicLatticeSite L) (b c : Bool) : (gInner y b c) 0 = y 0 := by
  cases b <;> cases c <;> simp [gInner, periodicLatticeShift, Function.update]

/-- The axis-`2`-only intermediate corner never touches coordinate `1`. -/
theorem gInner_false_apply_one (y : PeriodicLatticeSite L) (c : Bool) :
    (gInner y false c) 1 = y 1 := by
  cases c <;> simp [gInner, periodicLatticeShift, Function.update]

/-- The leg length `Q1Real.coordSteps` computes for a corner IS `gOff`. -/
theorem coordSteps_gCorner (y : PeriodicLatticeSite L)
    (hlt : ∀ μ : Fin 3, (y μ).val < L μ) (p : Bool × Bool × Bool) (μ : Fin 3) :
    AdalyFormal.Balaban.Q1Real.coordSteps y (gCorner y p) μ = gOff p μ := by
  have hL : 0 < L μ := lt_of_le_of_lt (Nat.zero_le _) (hlt μ)
  have hg := gCorner_apply_axis y p μ
  by_cases h : gOff p μ = 1
  · rw [show AdalyFormal.Balaban.Q1Real.coordSteps y (gCorner y p) μ
        = AdalyFormal.Balaban.Q1Real.coordSteps y (periodicLatticeShift y μ) μ by
      simp only [AdalyFormal.Balaban.Q1Real.coordSteps, hg, if_pos h],
      AdalyFormal.Balaban.ReparamCDisjoint.coordSteps_shift_self y μ hL, h]
  · have h0 : gOff p μ = 0 := by
      have := AdalyFormal.Balaban.GammaContourTree.gOff_le_one p μ
      omega
    simp only [AdalyFormal.Balaban.Q1Real.coordSteps, hg, h0]
    simp

/-- **`Γ_{y,x}` AS `Q1Real.GammaPath`, AT THE EIGHT CORNERS.** -/
theorem gammaPath_gCorner (y : PeriodicLatticeSite L)
    (hlt : ∀ μ : Fin 3, (y μ).val < L μ) (p : Bool × Bool × Bool) :
    AdalyFormal.Balaban.Q1Real.GammaPath y (gCorner y p)
      = List.replicate (gOff p 2) ((2 : Fin 3), true)
        ++ List.replicate (gOff p 1) ((1 : Fin 3), true)
        ++ List.replicate (gOff p 0) ((0 : Fin 3), true) := by
  have h1 : (Function.update y 2 ((gCorner y p) 2)) = gInner y false p.2.2 := corner1_gCorner y hlt p
  have h2 : (Function.update (Function.update y 2 ((gCorner y p) 2)) 1 ((gCorner y p) 1))
      = gInner y p.2.1 p.2.2 := corner2_gCorner y hlt p
  have hc1 : AdalyFormal.Balaban.Q1Real.coordSteps
      (Function.update y 2 ((gCorner y p) 2)) (gCorner y p) 1 = gOff p 1 := by
    rw [show AdalyFormal.Balaban.Q1Real.coordSteps
          (Function.update y 2 ((gCorner y p) 2)) (gCorner y p) 1
        = AdalyFormal.Balaban.Q1Real.coordSteps y (gCorner y p) 1 by
      simp only [AdalyFormal.Balaban.Q1Real.coordSteps, h1, gInner_false_apply_one],
      coordSteps_gCorner y hlt p 1]
  have hc0 : AdalyFormal.Balaban.Q1Real.coordSteps
      (Function.update (Function.update y 2 ((gCorner y p) 2)) 1 ((gCorner y p) 1))
      (gCorner y p) 0 = gOff p 0 := by
    rw [show AdalyFormal.Balaban.Q1Real.coordSteps
          (Function.update (Function.update y 2 ((gCorner y p) 2)) 1 ((gCorner y p) 1))
          (gCorner y p) 0
        = AdalyFormal.Balaban.Q1Real.coordSteps y (gCorner y p) 0 by
      simp only [AdalyFormal.Balaban.Q1Real.coordSteps, h2, gInner_apply_zero],
      coordSteps_gCorner y hlt p 0]
  unfold AdalyFormal.Balaban.Q1Real.GammaPath AdalyFormal.Balaban.Q1Real.straightSegment
  rw [coordSteps_gCorner y hlt p 2, hc1, hc0]

/-- **THE STATEMENT §0b NAMES, PROVED.** `gammaTransport U y p` is the `periodicPathHolonomy` of
`Q1Real.GammaPath y (gCorner y p)`. -/
theorem gammaTransport_eq_periodicPathHolonomy_gammaPath
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (y : PeriodicLatticeSite L) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (p : Bool × Bool × Bool) :
    periodicPathHolonomy U y (AdalyFormal.Balaban.Q1Real.GammaPath y (gCorner y p))
      = gammaTransport U y p := by
  rw [gammaPath_gCorner y hlt p]
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;>
    simp [gOff, periodicPathHolonomy, periodicLatticeStep, periodicLatticeShift, gammaTransport,
      mul_assoc]

/-! ## §4 — THE BRIDGE: the faithful `Q′` at `ell = 2` IS `L^{-d}` times the `gammaM` block sum -/

/-- **`Q′(U)λ(y) = (2³)⁻¹ · Σ_{p} R(Γ_{y,p})λ(corner p)`** — the tree's adjudicated general-`ell`
covariant block average, specialised to `ell = 2` and rewritten over the eight `(1.7)` corners. -/
theorem coarseRestrictSiteCovariantU_two_eq_gammaSum
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L)
    (hlt : ∀ μ : Fin 3, (y μ).val < L μ) :
    coarseRestrictSiteCovariantU U 2 lam y
      = ((2 : ℝ) ^ (3 : ℕ))⁻¹ • ∑ p : Bool × Bool × Bool, gammaM U lam y p := by
  unfold coarseRestrictSiteCovariantU
  rw [sum_block_eq_sum_corners y hlt (fun x => RMap (staircaseTransport U y x) (lam x))]
  have hsum : (∑ p : Bool × Bool × Bool,
      RMap (staircaseTransport U y (gCorner y p)) (lam (gCorner y p)))
      = ∑ p : Bool × Bool × Bool, gammaM U lam y p := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [gammaTransport_eq_staircaseTransport U y hlt p]
    rfl
  rw [hsum]
  congr 1
  norm_num

/-! ## §5 — THE OPERATOR, NAMED; AND THE KERNEL CHARACTERISATION

`QprimeBalaban` introduces NO new mathematical object: it is `CovarianceG1.QLinearMap` at
`CoarseRestrictTransported.transportedQData`, i.e. the tree's existing faithful `Q′`. It is named
here so that downstream statements can say `lam ∈ LinearMap.ker (QprimeBalaban U hdvd)`. -/

/-- **BAŁABAN'S `Q′` AT `ell = 2`, FAITHFULLY**: `(Q′λ)(y) = Σ_{x∈B(y)} L^{-d} R(U(Γ_{y,x}))λ(x)`,
defined on the coarse centers `𝔅`, as a bundled `ℝ`-linear map. -/
noncomputable abbrev QprimeBalaban
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (AlignedCoarseCenter L 2 hdvd → SuTwo) :=
  QLinearMap (transportedQData U 2 hdvd)

theorem QprimeBalaban_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (lam : PeriodicLatticeSite L → SuTwo)
    (c : AlignedCoarseCenter L 2 hdvd) :
    QprimeBalaban U hdvd lam c = coarseRestrictSiteCovariantU U 2 lam c.1 := by
  rw [show QprimeBalaban U hdvd lam = QMap (transportedQData U 2 hdvd) lam from rfl]
  exact QMap_transportedQData U 2 hdvd lam c

/-- A coarse center's block fits, hence its corner walk never wraps. -/
theorem coarse_hlt {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (hell : 2 ≤ ell) :
    ∀ μ : Fin 3, (y μ).val < L μ := by
  intro μ
  have h := coarseLattice_mem_fits hdvd hy μ
  omega

/-- **THE NORMALIZATION-INDEPENDENCE THEOREM the dead branch ASSUMED.** Membership in the kernel of
the faithfully normalized, coarse-indexed `Q′` is EXACTLY `GammaContourTree`'s `hmean`. The `L^{-d}`
prefactor is a nonzero scalar, so it cancels — proved, not asserted. -/
theorem mem_ker_QprimeBalaban_iff
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (lam : PeriodicLatticeSite L → SuTwo) :
    lam ∈ LinearMap.ker (QprimeBalaban U hdvd)
      ↔ ∀ y ∈ CoarseLattice L 2, ∑ p : Bool × Bool × Bool, gammaM U lam y p = 0 := by
  have hne : ((2 : ℝ) ^ (3 : ℕ))⁻¹ ≠ 0 := by norm_num
  constructor
  · intro hker y hy
    have h0 : QprimeBalaban U hdvd lam = 0 := LinearMap.mem_ker.mp hker
    have hc := congrFun h0 (⟨y, hy⟩ : AlignedCoarseCenter L 2 hdvd)
    rw [QprimeBalaban_apply U hdvd lam ⟨y, hy⟩,
      coarseRestrictSiteCovariantU_two_eq_gammaSum U lam y (coarse_hlt hdvd hy (by norm_num))] at hc
    exact (smul_eq_zero.mp hc).resolve_left hne
  · intro hmean
    refine LinearMap.mem_ker.mpr ?_
    funext c
    rw [QprimeBalaban_apply U hdvd lam c,
      coarseRestrictSiteCovariantU_two_eq_gammaSum U lam c.1 (coarse_hlt hdvd c.2 (by norm_num)),
      hmean c.1 c.2, smul_zero]
    rfl

/-! ### §5a — DISCLOSED OVERLAP, CLOSED AS A THEOREM (LAW-19)

`Balaban/QjComposite.lean` builds `Qcomposite bg ell j`, the `j`-fold composite of (3.19). Its
`Qcomposite_one` already proves the `j = 1` composite is `coarseRestrictSiteCovariantU (bg 0) ell`.
Chaining that with `QprimeBalaban_apply` shows this module introduces NO new operator: the named
`QprimeBalaban` is the composite's level-one factor, read on the coarse centers. -/

/-- **`Q′` HERE IS `Q'_1` THERE.** -/
theorem QprimeBalaban_eq_Qcomposite_one
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (lam : PeriodicLatticeSite L → SuTwo)
    (c : AlignedCoarseCenter L 2 hdvd) :
    QprimeBalaban U hdvd lam c
      = AdalyFormal.Balaban.QjComposite.Qcomposite (fun _ => U) 2 1 lam c.1 := by
  rw [QprimeBalaban_apply U hdvd lam c,
    AdalyFormal.Balaban.QjComposite.Qcomposite_one (fun _ => U) 2 lam]

/-! ## §6 — THE WIRING: the headline theorems with NO raw `hmean`

`GammaContourTree.hlam_at_kappa_sq_768_gamma` and `kappa_bound_and_criterion_closes` take `hmean`
as a bare per-block equation. Here the same conclusions are reached from
`lam ∈ ker (QprimeBalaban U hdvd)` — the hypothesis that
`KappaBound.gaugeParam_mem_ker_and_solves` actually delivers. -/

/-- The Poincaré inequality on `N(Q′)`, at the FAITHFUL `Q′`. -/
theorem gamma_poincare_of_mem_ker_balaban
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → SuTwo) (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hker : lam ∈ LinearMap.ker (QprimeBalaban U hdvd)) :
    siteEnergy lam ≤ 8 * bondEnergy (gradValueCovariant U lam) :=
  gamma_poincare_assembly U lam hdvd ((mem_ker_QprimeBalaban_iff U hdvd lam).mp hker)

/-- **`κ² ≤ 768` WITH `hmean` DISCHARGED INTO A KERNEL MEMBERSHIP.** No hypothesis of this theorem
is a bare block-mean equation: the Poincaré input is `λ ∈ N(Q′)` for the operator whose defining
formula is quoted in §0. -/
theorem hlam_at_kappa_sq_768_qprime
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam src dstarA : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hker : lam ∈ LinearMap.ker (QprimeBalaban U hdvd))
    (hweak : bondEnergy (gradValueCovariant U lam)
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner (gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA) :
    siteEnergy lam ≤ 768 * bondEnergy A :=
  hlam_at_kappa_sq_768_gamma U lam src dstarA A hdvd
    ((mem_ker_QprimeBalaban_iff U hdvd lam).mp hker) hweak hadj hproj

/-- The composed statement, `hmean`-free. -/
theorem kappa_bound_and_criterion_closes_qprime
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam src dstarA : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (hker : lam ∈ LinearMap.ker (QprimeBalaban U hdvd))
    (hweak : bondEnergy (gradValueCovariant U lam)
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner (gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA) :
    siteEnergy lam ≤ 768 * bondEnergy A
      ∧ AdalyFormal.Balaban.GammaRecursion.UniformStepGamma
          (KappaBound.deltaPiConstLocal (24 * (4 / 10 ^ 10 : ℝ)) (Real.sqrt 768)) (1/2 : ℝ) :=
  ⟨hlam_at_kappa_sq_768_qprime U lam src dstarA A hdvd hker hweak hadj hproj,
    KappaBound.uniformStepGamma_at_four_e_minus_ten⟩

/-- **`KappaBound` §2's STRUCTURAL THEOREM AT THE FAITHFUL `Q′`.** `gaugeParam_mem_ker_and_solves`
is stated for `Q : E →ₗ[ℝ] F` with `F` an INDEPENDENT space, so the coarse-indexed codomain needs no
adaptation: instantiated at `Q := QprimeBalaban U hdvd` it says `λ = G′Rf ∈ N(Q′)` and
`Δ(G′Rf) = Rf`. -/
theorem gaugeParam_mem_ker_QprimeBalaban
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (Δ M G R : (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo))
    (hM : ∀ x : PeriodicLatticeSite L → SuTwo, QprimeBalaban U hdvd x = 0 → M x = 0)
    (hG : ∀ x : PeriodicLatticeSite L → SuTwo, G ((Δ + M) x) = x)
    (hR : LinearMap.range R = Submodule.map Δ (LinearMap.ker (QprimeBalaban U hdvd)))
    (f : PeriodicLatticeSite L → SuTwo) :
    G (R f) ∈ LinearMap.ker (QprimeBalaban U hdvd) ∧ Δ (G (R f)) = R f := by
  obtain ⟨h1, h2⟩ :=
    KappaBound.gaugeParam_mem_ker_and_solves (QprimeBalaban U hdvd) Δ M G R hM hG hR f
  exact ⟨LinearMap.mem_ker.mpr h1, h2⟩

/-- **END TO END, `hmean` GONE.** For `λ = G′Rf` the Poincaré hypothesis is not assumed at all: it
is produced by the structural theorem at the same operator. -/
theorem kappa_768_for_gaugeParam_qprime
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (Δ M G R : (PeriodicLatticeSite L → SuTwo) →ₗ[ℝ] (PeriodicLatticeSite L → SuTwo))
    (hM : ∀ x : PeriodicLatticeSite L → SuTwo, QprimeBalaban U hdvd x = 0 → M x = 0)
    (hG : ∀ x : PeriodicLatticeSite L → SuTwo, G ((Δ + M) x) = x)
    (hR : LinearMap.range R = Submodule.map Δ (LinearMap.ker (QprimeBalaban U hdvd)))
    (f src dstarA : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo)
    (hweak : bondEnergy (gradValueCovariant U (G (R f)))
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner (G (R f)) src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner (gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA) :
    siteEnergy (G (R f)) ≤ 768 * bondEnergy A :=
  hlam_at_kappa_sq_768_qprime U (G (R f)) src dstarA A hdvd
    (gaugeParam_mem_ker_QprimeBalaban U hdvd Δ M G R hM hG hR f).1 hweak hadj hproj

/-! ## §6a — CMP95 (1.13): the `U = 1` reduction, as a theorem

At the trivial background every transport is `1` and `R(1) = id`, so the operator collapses to the
flat block average `Σ_{x∈B(y)} L^{-d} λ(x)` — CMP95 (1.13) verbatim. Two papers, one object. -/

theorem gammaTransport_trivialU (y : PeriodicLatticeSite L) (p : Bool × Bool × Bool) :
    gammaTransport (trivialU L) y p = 1 := by
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;> simp [gammaTransport, trivialU]

theorem gammaM_trivialU (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L)
    (p : Bool × Bool × Bool) : gammaM (trivialU L) lam y p = lam (gCorner y p) := by
  show RMap (gammaTransport (trivialU L) y p) (lam (gCorner y p)) = lam (gCorner y p)
  rw [gammaTransport_trivialU, RMap_one]
  rfl

/-- **CMP95 (1.13).** `(Q′λ)(y) = Σ_{x∈B(y)} L^{-d} λ(x)` at `U = 1`, `L = 2`, `d = 3`. -/
theorem qprime_trivialU_is_flat_block_average
    (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L)
    (hlt : ∀ μ : Fin 3, (y μ).val < L μ) :
    coarseRestrictSiteCovariantU (trivialU L) 2 lam y
      = ∑ x ∈ blockOf y 2, ((2 : ℝ) ^ (3 : ℕ))⁻¹ • lam x := by
  rw [coarseRestrictSiteCovariantU_two_eq_gammaSum (trivialU L) lam y hlt,
    sum_block_eq_sum_corners y hlt (fun x => ((2 : ℝ) ^ (3 : ℕ))⁻¹ • lam x), Finset.smul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [gammaM_trivialU]

/-! ## §7 — THE SEPARATION: `ker QprimeTwo` is STRICTLY SMALLER than `N(Q′)`

The two operators differ in their DOMAIN OF DEFINITION, and that difference is not inert.
`QprimeTwo` imposes the block-mean equation at EVERY site; the printed `Q′` imposes it only on the
coarse set `𝔅`. This section builds a concrete `λ ≠ 0` that satisfies the printed condition and
violates `QprimeTwo`'s.

Lattice: `sepL μ = 3` for every axis, i.e. the `4×4×4` torus (`L μ + 1 = 4`), which satisfies the
tileability guard `2 ∣ (L μ + 1)`. `λ` is supported on the two sites `(0,0,0)` and `(1,0,0)` with
opposite values. -/

/-- The `4 × 4 × 4` periodic extent. -/
def sepL : PeriodicLatticeExtent := fun _ => 3

theorem sepL_hdvd : ∀ μ : Fin 3, 2 ∣ (sepL μ + 1) := by decide

/-- The site `(0,0,0)`. -/
def sepS0 : PeriodicLatticeSite sepL := fun _ => (0 : Fin 4)

/-- The site `(1,0,0)` — inside the SAME `ell = 2` block as `sepS0`, and the base of a shifted
unit cube that contains `sepS0` NOT at all. -/
def sepS1 : PeriodicLatticeSite sepL := fun μ => if μ = 0 then (1 : Fin 4) else (0 : Fin 4)

theorem sepS0_val (μ : Fin 3) : (sepS0 μ).val = 0 := rfl

theorem sepS1_val (μ : Fin 3) : (sepS1 μ).val = if μ = 0 then 1 else 0 := by
  unfold sepS1
  split <;> rfl

theorem sepS1_hlt : ∀ μ : Fin 3, (sepS1 μ).val < sepL μ := by decide

theorem sepS0_hlt : ∀ μ : Fin 3, (sepS0 μ).val < sepL μ := by decide

theorem sepS0_coarse : sepS0 ∈ CoarseLattice sepL 2 := by decide

/-- Corner equality is a coordinate-value identity — the form every case below is decided in. -/
theorem gCorner_eq_iff_val (y z : PeriodicLatticeSite L)
    (hlt : ∀ μ : Fin 3, (y μ).val < L μ) (p : Bool × Bool × Bool) :
    gCorner y p = z ↔ ∀ μ : Fin 3, (y μ).val + gOff p μ = (z μ).val := by
  constructor
  · intro h μ
    rw [← gCorner_val y hlt p μ, h]
  · intro h
    refine site_eq_of_val_eq (fun μ => ?_)
    rw [gCorner_val y hlt p μ]
    exact h μ

noncomputable section SepWitness

open Classical

/-- `λ = w·δ_{(0,0,0)} − w·δ_{(1,0,0)}`. Its two masses cancel inside the single `ell = 2` block
based at `(0,0,0)`, and do NOT cancel inside the unit cube based at `(1,0,0)`. -/
noncomputable def sepLam : PeriodicLatticeSite sepL → SuTwo :=
  fun x => if x = sepS0 then suTwoWitness else if x = sepS1 then -suTwoWitness else 0

theorem sepLam_ne_zero : sepLam ≠ 0 := by
  intro h
  have := congrFun h sepS0
  rw [show sepLam sepS0 = suTwoWitness by simp [sepLam]] at this
  exact suTwoWitness_ne_zero this

/-- On a coarse block whose base has ANY coordinate equal to `2`, neither special site is reached. -/
theorem sepLam_corner_of_far {y : PeriodicLatticeSite sepL}
    (hlt : ∀ μ : Fin 3, (y μ).val < sepL μ) {ν : Fin 3} (hν : (y ν).val = 2)
    (p : Bool × Bool × Bool) : sepLam (gCorner y p) = 0 := by
  have h0 : gCorner y p ≠ sepS0 := by
    intro h
    have := (gCorner_eq_iff_val y sepS0 hlt p).mp h ν
    rw [sepS0_val, hν] at this
    omega
  have h1 : gCorner y p ≠ sepS1 := by
    intro h
    have := (gCorner_eq_iff_val y sepS1 hlt p).mp h ν
    rw [sepS1_val, hν] at this
    split at this <;> omega
  simp [sepLam, h0, h1]

/-- Every coarse base is either `(0,0,0)` or has a coordinate equal to `2`. -/
theorem sep_coarse_dichotomy {y : PeriodicLatticeSite sepL} (hy : y ∈ CoarseLattice sepL 2) :
    y = sepS0 ∨ ∃ ν : Fin 3, (y ν).val = 2 := by
  rw [mem_CoarseLattice] at hy
  by_cases hall : ∀ μ : Fin 3, (y μ).val = 0
  · exact Or.inl (site_eq_of_val_eq (fun μ => by rw [hall μ]; rfl))
  · rw [not_forall] at hall
    obtain ⟨ν, hν⟩ := hall
    refine Or.inr ⟨ν, ?_⟩
    have hlt : (y ν).val < 4 := (y ν).isLt
    have := hy ν
    omega

theorem sepLam_block_sum_at_sepS0 :
    ∑ p : Bool × Bool × Bool, sepLam (gCorner sepS0 p) = 0 := by
  have key : ∀ p : Bool × Bool × Bool,
      sepLam (gCorner sepS0 p)
        = if p = (false, false, false) then suTwoWitness
          else if p = (true, false, false) then -suTwoWitness else 0 := by
    intro p
    have h0 : gCorner sepS0 p = sepS0 ↔ p = (false, false, false) := by
      rw [gCorner_eq_iff_val sepS0 sepS0 sepS0_hlt p]
      obtain ⟨a, b, c⟩ := p
      cases a <;> cases b <;> cases c <;> simp [gOff, sepS0_val] <;> decide
    have h1 : gCorner sepS0 p = sepS1 ↔ p = (true, false, false) := by
      rw [gCorner_eq_iff_val sepS0 sepS1 sepS0_hlt p]
      obtain ⟨a, b, c⟩ := p
      cases a <;> cases b <;> cases c <;> simp [gOff, sepS0_val, sepS1_val] <;> decide
    simp only [sepLam]
    by_cases hA : p = (false, false, false)
    · subst hA
      rw [if_pos (h0.mpr rfl), if_pos rfl]
    · by_cases hB : p = (true, false, false)
      · subst hB
        rw [if_neg (h0.not.mpr hA), if_pos (h1.mpr rfl), if_neg hA, if_pos rfl]
      · rw [if_neg (h0.not.mpr hA), if_neg (h1.not.mpr hB), if_neg hA, if_neg hB]
  rw [Finset.sum_congr rfl (fun p _ => key p)]
  rw [sum_bool3]
  norm_num

/-- **`sepLam` LIES IN THE PRINTED `Q′`'s KERNEL.** -/
theorem sepLam_mem_ker_balaban :
    sepLam ∈ LinearMap.ker (QprimeBalaban (trivialU sepL) sepL_hdvd) := by
  refine (mem_ker_QprimeBalaban_iff (trivialU sepL) sepL_hdvd sepLam).mpr ?_
  intro y hy
  have hlt := coarse_hlt sepL_hdvd hy (by norm_num)
  have hg : ∀ p : Bool × Bool × Bool,
      gammaM (trivialU sepL) sepLam y p = sepLam (gCorner y p) :=
    fun p => gammaM_trivialU sepLam y p
  rw [Finset.sum_congr rfl (fun p _ => hg p)]
  rcases sep_coarse_dichotomy hy with h | ⟨ν, hν⟩
  · subst h
    exact sepLam_block_sum_at_sepS0
  · rw [Finset.sum_congr rfl (fun p _ => sepLam_corner_of_far hlt hν p)]
    simp

/-- **`sepLam` DOES NOT LIE IN `ker QprimeTwo`.** The unit cube based at `(1,0,0)` contains
`(1,0,0)` and not `(0,0,0)`, so its transported sum is `w ≠ 0`. -/
theorem sepLam_not_mem_ker_QprimeTwo :
    sepLam ∉ LinearMap.ker (QprimeTwo (trivialU sepL)) := by
  intro hker
  have h0 : QprimeTwo (trivialU sepL) sepLam = 0 := LinearMap.mem_ker.mp hker
  have hc := congrFun h0 sepS1
  rw [QprimeTwo_apply] at hc
  have hg : ∀ p : Bool × Bool × Bool,
      gammaM (trivialU sepL) sepLam sepS1 p = sepLam (gCorner sepS1 p) :=
    fun p => gammaM_trivialU sepLam sepS1 p
  rw [Finset.sum_congr rfl (fun p _ => hg p)] at hc
  have key : ∀ p : Bool × Bool × Bool,
      sepLam (gCorner sepS1 p) = if p = (false, false, false) then -suTwoWitness else 0 := by
    intro p
    have hone : (sepS1 (0 : Fin 3)).val = 1 := by decide
    have h0' : gCorner sepS1 p ≠ sepS0 := by
      intro h
      have hz := (gCorner_eq_iff_val sepS1 sepS0 sepS1_hlt p).mp h 0
      rw [sepS0_val, hone] at hz
      omega
    have h1' : gCorner sepS1 p = sepS1 ↔ p = (false, false, false) := by
      rw [gCorner_eq_iff_val sepS1 sepS1 sepS1_hlt p]
      obtain ⟨a, b, c⟩ := p
      cases a <;> cases b <;> cases c <;> simp [gOff, sepS1_val] <;> decide
    unfold sepLam
    by_cases hA : p = (false, false, false)
    · rw [if_neg h0', if_pos (h1'.mpr hA)]
      simp [hA]
    · rw [if_neg h0', if_neg (h1'.not.mpr hA)]
      simp [hA]
  rw [Finset.sum_congr rfl (fun p _ => key p), sum_bool3] at hc
  norm_num at hc
  exact suTwoWitness_ne_zero hc

/-- **THE SEPARATION, in one statement.** `ker QprimeTwo ⊊ N(Q′)`: the inclusion holds, and it is
strict. So `QprimeTwo`'s hypothesis is STRICTLY STRONGER than Bałaban's gauge-fixing condition. -/
theorem ker_QprimeTwo_lt_ker_QprimeBalaban :
    LinearMap.ker (QprimeTwo (trivialU sepL))
      < LinearMap.ker (QprimeBalaban (trivialU sepL) sepL_hdvd) := by
  refine lt_of_le_of_ne ?_ ?_
  · intro lam hlam
    refine (mem_ker_QprimeBalaban_iff (trivialU sepL) sepL_hdvd lam).mpr (fun y _ => ?_)
    have h0 : QprimeTwo (trivialU sepL) lam = 0 := LinearMap.mem_ker.mp hlam
    have hc := congrFun h0 y
    rwa [QprimeTwo_apply] at hc
  · intro hEq
    exact sepLam_not_mem_ker_QprimeTwo (hEq ▸ sepLam_mem_ker_balaban)

/-! ### §7a — MUST-FIRE and MUST-NOT-FIRE for `QprimeBalaban` itself

Both controls are required or the kernel condition is void: without the must-fire the operator
could be identically zero (every `λ` in its kernel, the hypothesis vacuous); without the
must-not-fire the kernel could be `{0}` (the hypothesis unsatisfiable except trivially). -/

/-- `λ = w·δ_{(0,0,0)}` — a single unbalanced mass in one coarse block. -/
noncomputable def sepLamPos : PeriodicLatticeSite sepL → SuTwo :=
  fun x => if x = sepS0 then suTwoWitness else 0

/-- **MUST-FIRE: `Q′` IS NOT THE ZERO OPERATOR.** -/
theorem qprimeBalaban_ne_zero_at_sepLamPos :
    QprimeBalaban (trivialU sepL) sepL_hdvd sepLamPos ≠ 0 := by
  intro h
  have hmean := (mem_ker_QprimeBalaban_iff (trivialU sepL) sepL_hdvd sepLamPos).mp
    (LinearMap.mem_ker.mpr h) sepS0 sepS0_coarse
  have hg : ∀ p : Bool × Bool × Bool,
      gammaM (trivialU sepL) sepLamPos sepS0 p = sepLamPos (gCorner sepS0 p) :=
    fun p => gammaM_trivialU sepLamPos sepS0 p
  rw [Finset.sum_congr rfl (fun p _ => hg p)] at hmean
  have key : ∀ p : Bool × Bool × Bool,
      sepLamPos (gCorner sepS0 p) = if p = (false, false, false) then suTwoWitness else 0 := by
    intro p
    have h0 : gCorner sepS0 p = sepS0 ↔ p = (false, false, false) := by
      rw [gCorner_eq_iff_val sepS0 sepS0 sepS0_hlt p]
      obtain ⟨a, b, c⟩ := p
      cases a <;> cases b <;> cases c <;> simp [gOff, sepS0_val] <;> decide
    unfold sepLamPos
    by_cases hA : p = (false, false, false)
    · rw [if_pos (h0.mpr hA)]; simp [hA]
    · rw [if_neg (h0.not.mpr hA)]; simp [hA]
  rw [Finset.sum_congr rfl (fun p _ => key p), sum_bool3] at hmean
  norm_num at hmean
  exact suTwoWitness_ne_zero hmean

/-- **MUST-NOT-FIRE: `N(Q′)` IS NOT `{0}`** — `sepLam` is a nonzero element of it, so the wired
hypothesis `lam ∈ ker (QprimeBalaban U hdvd)` is satisfiable at a `λ` with `siteEnergy λ > 0`
(nonzero `λ`), not only at `λ = 0`. -/
theorem ker_QprimeBalaban_ne_bot :
    LinearMap.ker (QprimeBalaban (trivialU sepL) sepL_hdvd) ≠ ⊥ := by
  intro h
  have := (Submodule.mem_bot ℝ).mp (h ▸ sepLam_mem_ker_balaban)
  exact sepLam_ne_zero this

end SepWitness

/-! ## §7b — THE CONTROLS AT **EVERY** BACKGROUND AND **EVERY** ADMISSIBLE EXTENT

§7a's two controls live at one lattice and one background (`trivialU sepL`). A control that only
fires at `U = 1` is a weak control: the wired hypothesis is quantified over ALL `U`, so the
non-vacuity must be too. This section re-proves both for an ARBITRARY `L` satisfying the tileability
guard and an ARBITRARY `U`.

Both rest on one geometric fact: a coarse center whose block reaches a site with every coordinate
`≤ 1` must BE the origin, because its coordinates are even and an offset is at most `1`. -/

/-- **LAW-19 — `zeroSite` IS NOT REDEFINED HERE.** An earlier revision of this module defined its
own `zeroSite`/`zeroSite_val`/`zeroSite_coarse`, which are literally
`FibreCoercivity.zeroSite`/`zeroSite_val`/`zeroSite_coarse`. Found by grepping `def zeroSite` across
the tree before returning; the three duplicates are DELETED and the existing ones are opened above.
Recorded rather than silently removed, because a rebuilt object is the defect LAW-19 names.

The tileability guard forces every axis to carry at least two sites, so the origin's block
does not wrap. -/
theorem zeroSite_hlt (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    ∀ μ : Fin 3, ((zeroSite L) μ).val < L μ := by
  intro μ
  obtain ⟨k, hk⟩ := hdvd μ
  rw [zeroSite_val]
  rcases Nat.eq_zero_or_pos k with h | h
  · omega
  · omega

/-- **THE GEOMETRIC FACT.** A coarse center can reach a site all of whose coordinates are `≤ 1`
only if the center is the origin. (Even coordinate `+` offset `≤ 1` cannot land in `{0,1}` unless
the coordinate is `0`.) -/
theorem coarse_reaches_small_imp_zero {y z : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L 2) (hlt : ∀ μ : Fin 3, (y μ).val < L μ)
    (hz : ∀ μ : Fin 3, (z μ).val ≤ 1) {p : Bool × Bool × Bool} (h : gCorner y p = z) :
    y = zeroSite L := by
  rw [mem_CoarseLattice] at hy
  refine site_eq_of_val_eq (fun μ => ?_)
  rw [zeroSite_val]
  have hval := (gCorner_eq_iff_val y z hlt p).mp h μ
  have hoff : gOff p μ ≤ 1 := AdalyFormal.Balaban.GammaContourTree.gOff_le_one p μ
  have := hy μ
  have := hz μ
  omega

/-- The corner index is determined at the origin: `gCorner (zeroSite L) p = zeroSite L` exactly at
`p = (false,false,false)`. -/
theorem gCorner_zeroSite_eq_zero_iff (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (p : Bool × Bool × Bool) :
    gCorner (zeroSite L) p = zeroSite L ↔ p = (false, false, false) := by
  constructor
  · intro h
    have hroot : gCorner (zeroSite L) (false, false, false) = zeroSite L := rfl
    exact gCorner_inj (zeroSite L) (zeroSite_hlt hdvd) (h.trans hroot.symm)
  · intro h; subst h; rfl

noncomputable section GeneralControls

open Classical

/-- `λ = w·δ₀`, one unbalanced mass at the origin. -/
noncomputable def deltaOrigin (L : PeriodicLatticeExtent) : PeriodicLatticeSite L → SuTwo :=
  fun x => if x = zeroSite L then suTwoWitness else 0

/-- **MUST-FIRE, GENERAL: `Q′` IS NOT THE ZERO OPERATOR AT ANY BACKGROUND.** For every `U` and
every extent satisfying the tileability guard, `Q′(U)` is nonzero — so the hypothesis
`lam ∈ ker (QprimeBalaban U hdvd)` is a genuine restriction, never satisfied by every `λ`. -/
theorem qprimeBalaban_ne_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    QprimeBalaban U hdvd (deltaOrigin L) ≠ 0 := by
  intro h
  have hmean := (mem_ker_QprimeBalaban_iff U hdvd (deltaOrigin L)).mp
    (LinearMap.mem_ker.mpr h) (zeroSite L) zeroSite_coarse
  have key : ∀ p : Bool × Bool × Bool,
      gammaM U (deltaOrigin L) (zeroSite L) p
        = if p = (false, false, false) then suTwoWitness else 0 := by
    intro p
    show RMap (gammaTransport U (zeroSite L) p) (deltaOrigin L (gCorner (zeroSite L) p)) = _
    by_cases hp : p = (false, false, false)
    · subst hp
      rw [show gammaTransport U (zeroSite L) (false, false, false) = 1 from rfl, RMap_one]
      simp only [deltaOrigin, if_pos ((gCorner_zeroSite_eq_zero_iff hdvd _).mpr rfl)]
      rfl
    · simp only [deltaOrigin,
        if_neg ((gCorner_zeroSite_eq_zero_iff hdvd p).not.mpr hp), if_neg hp, map_zero]
  rw [Finset.sum_congr rfl (fun p _ => key p), sum_bool3] at hmean
  norm_num at hmean
  exact suTwoWitness_ne_zero hmean

/-- The axis-`0` neighbour of the origin — the second support site of the kernel witness. -/
def originNbr (L : PeriodicLatticeExtent) : PeriodicLatticeSite L :=
  gCorner (zeroSite L) (true, false, false)

theorem originNbr_ne_zeroSite (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    originNbr L ≠ zeroSite L := by
  intro h
  exact absurd ((gCorner_zeroSite_eq_zero_iff hdvd (true, false, false)).mp h) (by decide)

theorem originNbr_small (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    ∀ μ : Fin 3, ((originNbr L) μ).val ≤ 1 := by
  intro μ
  unfold originNbr
  rw [gCorner_val (zeroSite L) (zeroSite_hlt hdvd) _ μ, zeroSite_val]
  simpa using AdalyFormal.Balaban.GammaContourTree.gOff_le_one (true, false, false) μ

theorem zeroSite_small : ∀ μ : Fin 3, ((zeroSite L) μ).val ≤ 1 := by
  intro μ; rw [zeroSite_val]; omega

/-- `λ = w·δ₀ − R(Γ₍₀,e₀₎)⁻¹w·δ_{e₀}` — two masses inside the SAME coarse block, arranged so that
the TRANSPORTED sum cancels at the background `U`. This is the nontrivial element of `N(Q′(U))`. -/
noncomputable def kerWitness
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    PeriodicLatticeSite L → SuTwo :=
  fun x => if x = zeroSite L then suTwoWitness
    else if x = originNbr L then
      RMap ((gammaTransport U (zeroSite L) (true, false, false))⁻¹) (-suTwoWitness)
    else 0

theorem kerWitness_ne_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    kerWitness U ≠ 0 := by
  intro h
  have hv := congrFun h (zeroSite L)
  rw [show kerWitness U (zeroSite L) = suTwoWitness by simp [kerWitness]] at hv
  exact suTwoWitness_ne_zero hv

/-- **MUST-NOT-FIRE, GENERAL: `N(Q′(U)) ≠ {0}` AT EVERY BACKGROUND.** So the wired hypothesis is
satisfiable at a NONZERO `λ` for every `U` and every admissible extent — it is not a disguised
`λ = 0`. -/
theorem kerWitness_mem_ker
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    kerWitness U ∈ LinearMap.ker (QprimeBalaban U hdvd) := by
  refine (mem_ker_QprimeBalaban_iff U hdvd (kerWitness U)).mpr ?_
  intro y hy
  have hlt := coarse_hlt hdvd hy (by norm_num)
  by_cases hy0 : y = zeroSite L
  · subst hy0
    have key : ∀ p : Bool × Bool × Bool,
        gammaM U (kerWitness U) (zeroSite L) p
          = if p = (false, false, false) then suTwoWitness
            else if p = (true, false, false) then -suTwoWitness else 0 := by
      intro p
      show RMap (gammaTransport U (zeroSite L) p) (kerWitness U (gCorner (zeroSite L) p)) = _
      by_cases hA : p = (false, false, false)
      · subst hA
        rw [show gammaTransport U (zeroSite L) (false, false, false) = 1 from rfl, RMap_one]
        simp only [kerWitness, if_pos ((gCorner_zeroSite_eq_zero_iff hdvd _).mpr rfl)]
        rfl
      · by_cases hB : p = (true, false, false)
        · subst hB
          have hnb : gCorner (zeroSite L) (true, false, false) = originNbr L := rfl
          simp only [kerWitness, if_neg ((gCorner_zeroSite_eq_zero_iff hdvd _).not.mpr hA),
            if_pos hnb, if_neg hA]
          simpa using
            AdalyFormal.Balaban.CovariantHjMinimizer.RMap_apply_inv_cancel
              (gammaTransport U (zeroSite L) (true, false, false)) (-suTwoWitness)
        · have hz : gCorner (zeroSite L) p ≠ zeroSite L :=
            (gCorner_zeroSite_eq_zero_iff hdvd p).not.mpr hA
          have hn : gCorner (zeroSite L) p ≠ originNbr L := by
            intro hc
            exact hB (gCorner_inj (zeroSite L) (zeroSite_hlt hdvd) hc)
          simp only [kerWitness, if_neg hz, if_neg hn, if_neg hA, if_neg hB, map_zero]
    rw [Finset.sum_congr rfl (fun p _ => key p), sum_bool3]
    norm_num
  · have key : ∀ p : Bool × Bool × Bool, gammaM U (kerWitness U) y p = 0 := by
      intro p
      show RMap (gammaTransport U y p) (kerWitness U (gCorner y p)) = 0
      have hz : gCorner y p ≠ zeroSite L := by
        intro hc
        exact hy0 (coarse_reaches_small_imp_zero hy hlt zeroSite_small hc)
      have hn : gCorner y p ≠ originNbr L := by
        intro hc
        exact hy0 (coarse_reaches_small_imp_zero hy hlt (originNbr_small hdvd) hc)
      simp only [kerWitness, if_neg hz, if_neg hn, map_zero]
    rw [Finset.sum_congr rfl (fun p _ => key p)]
    simp

/-- The kernel is nontrivial at EVERY background. -/
theorem ker_QprimeBalaban_ne_bot_general
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) :
    LinearMap.ker (QprimeBalaban U hdvd) ≠ ⊥ := by
  intro h
  exact kerWitness_ne_zero U ((Submodule.mem_bot ℝ).mp (h ▸ kerWitness_mem_ker U hdvd))

/-! ### §7c — THE SEPARATION, GENERAL: `ker QprimeTwo ⊊ N(Q′(U))` AT EVERY BACKGROUND

§7's strictness is proved at one `4×4×4` torus and one background. If the mismatch between the two
operators were an artifact of that particular small torus it would not be worth acting on, so it is
proved here for an ARBITRARY background `U` and an arbitrary extent with at least four sites per
axis. The witness is the SAME `kerWitness` used for the must-not-fire control: its two masses cancel
inside the coarse block based at the origin, and do NOT cancel inside the unit cube based at the
origin's axis-`0` neighbour — a cube `QprimeTwo` constrains and the printed `Q′` does not.

The extent hypothesis `hbig` is not decoration. At `L μ + 1 = 2` the axis-`0` neighbour's own cube
WRAPS back onto the origin, both masses land in it, and the sum vanishes — the separation genuinely
fails there. `hbig` with `hdvd` gives `L μ + 1 ≥ 4`. -/

theorem RMap_eq_zero_iff (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : SuTwo) :
    RMap g X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hn := norm_RMap g X
    rw [h, norm_zero] at hn
    exact norm_eq_zero.mp hn.symm
  · intro h; rw [h, map_zero]

theorem originNbr_hlt (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (hbig : ∀ μ : Fin 3, 2 ≤ L μ) :
    ∀ μ : Fin 3, ((originNbr L) μ).val < L μ := by
  intro μ
  have h := originNbr_small (L := L) hdvd μ
  have := hbig μ
  omega

/-- **`kerWitness` VIOLATES `QprimeTwo`'s CONDITION** — at the unit cube based at the origin's
axis-`0` neighbour, which contains that neighbour and not the origin. -/
theorem kerWitness_not_mem_ker_QprimeTwo
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (hbig : ∀ μ : Fin 3, 2 ≤ L μ) :
    kerWitness U ∉ LinearMap.ker (QprimeTwo U) := by
  intro hker
  have h0 : QprimeTwo U (kerWitness U) = 0 := LinearMap.mem_ker.mp hker
  have hc := congrFun h0 (originNbr L)
  rw [QprimeTwo_apply] at hc
  have hlt := originNbr_hlt (L := L) hdvd hbig
  have hval0 : ((originNbr L) (0 : Fin 3)).val = 1 := by
    show ((gCorner (zeroSite L) (true, false, false)) (0 : Fin 3)).val = 1
    rw [gCorner_val (zeroSite L) (zeroSite_hlt hdvd) _ 0, zeroSite_val]
    rfl
  -- no corner of the neighbour's cube is the ORIGIN: coordinate `0` there is `1 + offset ≥ 1`
  have hz : ∀ p : Bool × Bool × Bool, gCorner (originNbr L) p ≠ zeroSite L := by
    intro p h
    have hv := (gCorner_eq_iff_val (originNbr L) (zeroSite L) hlt p).mp h 0
    rw [zeroSite_val, hval0] at hv
    omega
  -- the neighbour itself is reached only at the identity corner
  have hn : ∀ p : Bool × Bool × Bool,
      gCorner (originNbr L) p = originNbr L ↔ p = (false, false, false) := by
    intro p
    refine ⟨fun h => ?_, fun h => by subst h; rfl⟩
    have hroot : gCorner (originNbr L) (false, false, false) = originNbr L := rfl
    exact gCorner_inj (originNbr L) hlt (h.trans hroot.symm)
  have hoff : ∀ p : Bool × Bool × Bool, p ≠ (false, false, false) →
      gammaM U (kerWitness U) (originNbr L) p = 0 := by
    intro p hp
    show RMap (gammaTransport U (originNbr L) p) (kerWitness U (gCorner (originNbr L) p)) = 0
    simp only [kerWitness, if_neg (hz p), if_neg ((hn p).not.mpr hp), map_zero]
  have hroot : gammaM U (kerWitness U) (originNbr L) (false, false, false)
      = RMap ((gammaTransport U (zeroSite L) (true, false, false))⁻¹) (-suTwoWitness) := by
    show RMap (gammaTransport U (originNbr L) (false, false, false))
      (kerWitness U (gCorner (originNbr L) (false, false, false))) = _
    rw [show gammaTransport U (originNbr L) (false, false, false) = 1 from rfl, RMap_one]
    simp only [kerWitness, if_neg (hz (false, false, false)),
      if_pos ((hn (false, false, false)).mpr rfl)]
    rfl
  rw [sum_bool3, hroot, hoff (true, false, false) (by decide),
    hoff (false, true, false) (by decide), hoff (true, true, false) (by decide),
    hoff (false, false, true) (by decide), hoff (true, false, true) (by decide),
    hoff (false, true, true) (by decide), hoff (true, true, true) (by decide)] at hc
  simp only [add_zero] at hc
  exact suTwoWitness_ne_zero (neg_eq_zero.mp ((RMap_eq_zero_iff _ _).mp hc))

/-- **THE SEPARATION AT EVERY BACKGROUND.** `ker QprimeTwo ⊊ N(Q′(U))` for every `U` and every
extent with at least four sites per axis. So the over-strength of `QprimeTwo` is a structural
feature of imposing the block-mean equation at every site, not an artifact of one small torus. -/
theorem ker_QprimeTwo_lt_ker_QprimeBalaban_general
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (hbig : ∀ μ : Fin 3, 2 ≤ L μ) :
    LinearMap.ker (QprimeTwo U) < LinearMap.ker (QprimeBalaban U hdvd) := by
  refine lt_of_le_of_ne ?_ ?_
  · intro lam hlam
    refine (mem_ker_QprimeBalaban_iff U hdvd lam).mpr (fun y _ => ?_)
    have h0 : QprimeTwo U lam = 0 := LinearMap.mem_ker.mp hlam
    have hc := congrFun h0 y
    rwa [QprimeTwo_apply] at hc
  · intro hEq
    exact kerWitness_not_mem_ker_QprimeTwo U hdvd hbig (hEq ▸ kerWitness_mem_ker U hdvd)

end GeneralControls

/-! ## §9 — THE DISCHARGE REACHES THE DOWNSTREAM CONSUMER, NOT ONLY THE HEADLINE

`Balaban/ComposedCoercivity.lean` is where `κ` is discharged into `δ` and where the composed
coercivity statement is assembled. Its §4 header states, as its own reason for carrying `hmean`
RAW: *"the ker-membership derivation (`GammaContourTree.poincare_for_gaugeParam`) is not on the path
of `hlam_at_kappa_sq_768_gamma`, and `Q′` is not yet pinned at source."* Both clauses are addressed
above — the operator is pinned at CMP99b p.393 and CMP95 (1.13), and §6's chain is on the path.

This section restates ComposedCoercivity's three `hmean`-carrying theorems with `hmean` REPLACED by
`lam ∈ ker (QprimeBalaban U hdvd)`. Nothing about their mathematics changes: each is the original
theorem applied to `mem_ker_QprimeBalaban_iff`. `ComposedCoercivity.lean` is NOT edited (write
scope); these are additive wrappers, and they are what a consumer should call. -/

/-- **`δ` WITH `κ` DISCHARGED, AND NO RAW `hmean`.** -/
theorem deltaPrimePi_bound_kappa_discharged_qprime
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (lam src dstarA : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo) (Jsup : ℝ)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (hker : lam ∈ LinearMap.ker (QprimeBalaban U hdvd))
    (hweak : bondEnergy (gradValueCovariant U lam)
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner (gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA)
    (hJ : ∀ b, frobNorm (J b) ≤ Jsup) :
    |deltaPrimePiForm U J lam A| ≤ deltaPiConst Jsup kappaTree * bondEnergy A :=
  deltaPrimePi_bound_kappa_discharged U J lam src dstarA A Jsup hdvd
    ((mem_ker_QprimeBalaban_iff U hdvd lam).mp hker) hweak hadj hproj hJ

/-- **THE SAME AT A REGULAR BACKGROUND, `Jsup` DISCHARGED TOO, AND NO RAW `hmean`.** -/
theorem deltaPrimePi_bound_at_regular_U_qprime
    {α₀ etaInvSq : ℝ} (hα₀ : 0 ≤ α₀) (hη : 0 ≤ etaInvSq)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (pl : Bond L → Fin 4 → PeriodicLatticePlaquette L)
    (hJdef : ∀ b, J b = (etaInvSq : ℂ) •
      (AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 0)
        - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 1)
        + AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 2)
        - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 3)))
    (lam src dstarA : PeriodicLatticeSite L → SuTwo) (A : Bond L → SuTwo)
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (hker : lam ∈ LinearMap.ker (QprimeBalaban U hdvd))
    (hweak : bondEnergy (gradValueCovariant U lam)
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner (gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA) :
    |deltaPrimePiForm U J lam A|
      ≤ deltaPiConst (24 * etaInvSq * α₀) kappaTree * bondEnergy A :=
  deltaPrimePi_bound_at_regular_U hα₀ hη U hreg J pl hJdef lam src dstarA A hdvd
    ((mem_ker_QprimeBalaban_iff U hdvd lam).mp hker) hweak hadj hproj

/-- **THE COMPOSED COERCIVITY STATEMENT, WITH NO RAW `hmean`.** Identical to
`ComposedCoercivity.composed_coercivity_general` except that the `λ`-side input is membership in the
kernel of the operator pinned at CMP99b p.393 — the hypothesis
`KappaBound.gaugeParam_mem_ker_and_solves` delivers, rather than a bare block-mean equation. -/
theorem composed_coercivity_general_qprime
    (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    {α₀ etaInvSq : ℝ} (hα₀ : 0 ≤ α₀) (hη : 0 ≤ etaInvSq)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (pl : Bond L → Fin 4 → PeriodicLatticePlaquette L)
    (hJdef : ∀ b, J b = (etaInvSq : ℂ) •
      (AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 0)
        - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 1)
        + AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 2)
        - AdalyFormal.Balaban.DeltaPrime.imHolonomy U (pl b 3)))
    (A : Bond L → SuTwo)
    (hQ : ∀ b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 2,
      lineCoarseRestrictCov (trivialU L) 2 A b = 0)
    (lam src dstarA : PeriodicLatticeSite L → SuTwo)
    (hker : lam ∈ LinearMap.ker (QprimeBalaban U hdvd))
    (hweak : bondEnergy (gradValueCovariant U lam)
      = AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner lam src)
    (hadj : ∀ w : PeriodicLatticeSite L → SuTwo,
      AdalyFormal.Balaban.CovariantHjMinimizer.covSiteInner w dstarA
        = AdalyFormal.Balaban.CovariantHj.covBondInner (gradValueCovariant U w) A)
    (hproj : siteEnergy src ≤ siteEnergy dstarA)
    {γstar : ℝ} (hγstar : 0 < γstar) (hagg : AggregateFibreBound L U γstar)
    (hcrit : deltaPiConst (24 * etaInvSq * α₀) kappaTree ≤ γstar * (1 - (1 / 2 : ℝ) ^ 2)) :
    γstar * bondEnergy A
        ≤ deltaKQuadFormNormalizedCorrected U A + pAx A (CoarseLattice L 2) 2
      ∧ gammaFibre * bondSup A
        ≤ deltaKQuadFormNormalizedCorrected (trivialU L) A + pAx A (CoarseLattice L 2) 2
      ∧ |deltaPrimePiForm U J lam A|
        ≤ deltaPiConst (24 * etaInvSq * α₀) kappaTree * bondEnergy A
      ∧ ∀ k : ℕ,
          0 < gammaSeq γstar (deltaPiConst (24 * etaInvSq * α₀) kappaTree) (1 / 2 : ℝ) k
            ∧ γstar
              ≤ gammaSeq γstar (deltaPiConst (24 * etaInvSq * α₀) kappaTree) (1 / 2 : ℝ) k :=
  composed_coercivity_general hdvd hα₀ hη U hreg J pl hJdef A hQ lam src dstarA
    ((mem_ker_QprimeBalaban_iff U hdvd lam).mp hker) hweak hadj hproj hγstar hagg hcrit

#print axioms deltaPrimePi_bound_kappa_discharged_qprime
#print axioms deltaPrimePi_bound_at_regular_U_qprime
#print axioms composed_coercivity_general_qprime

/-! ## §7d — A MUST-FIRE THAT ACTUALLY EXERCISES THE TRANSPORT

§7b's `qprimeBalaban_ne_zero` is a genuine must-fire — a zero operator would fail it — but it fires
through the IDENTITY corner, where `gammaTransport U y (false,false,false) = 1` holds for every `U`
by definition. So it never tests the `R(V(Γ_{y,x}))` factor, which is the one ingredient of CMP99b
p.393's formula that a wrong encoding is most likely to drop. Recorded plainly rather than left for
a prosecutor to find.

The control below closes that hole using the tree's OWN separation witnesses (LAW-19, nothing
rebuilt): `CoarseRestrictTransported.sepU` is a non-constant pure-gauge background and
`CoarseRestrictTransported.sepLam` a field whose two masses cancel in the FLAT block average. At the
same coarse center, `Q′` is ZERO at the trivial background and NONZERO at `sepU`. **Delete the
transport factor and the two values coincide — the conjunction becomes false.** That is the
mutation this control catches and the previous one does not. -/

theorem witnessL_hdvd :
    ∀ μ : Fin 3, 2 ∣ (AdalyFormal.Balaban.AdmissibleSubspace.witnessL μ + 1) := by decide

/-- **MUST-FIRE ON THE TRANSPORT ITSELF.** -/
theorem qprimeBalaban_transport_load_bearing :
    QprimeBalaban AdalyFormal.Balaban.CoarseRestrictTransported.sepU witnessL_hdvd
        AdalyFormal.Balaban.CoarseRestrictTransported.sepLam
        ⟨AdalyFormal.Balaban.AdmissibleSubspace.witnessY, by decide⟩ ≠ 0
      ∧ QprimeBalaban (trivialU AdalyFormal.Balaban.AdmissibleSubspace.witnessL) witnessL_hdvd
        AdalyFormal.Balaban.CoarseRestrictTransported.sepLam
        ⟨AdalyFormal.Balaban.AdmissibleSubspace.witnessY, by decide⟩ = 0 := by
  constructor
  · rw [QprimeBalaban_apply]
    exact AdalyFormal.Balaban.CoarseRestrictTransported.sepLam_transported_ne_zero
  · rw [QprimeBalaban_apply,
      AdalyFormal.Balaban.CoarseRestrictTransported.coarseRestrictSiteCovariantU_trivialU]
    exact AdalyFormal.Balaban.CoarseRestrictTransported.sepLam_flat_value

#print axioms witnessL_hdvd
#print axioms qprimeBalaban_transport_load_bearing

/-! ## §8 — AXIOM AUDIT -/

#print axioms sum_block_eq_sum_corners
#print axioms card_blockOf_two_real
#print axioms gCorner_off
#print axioms staircaseBonds_gCorner
#print axioms gammaTransport_eq_staircaseTransport
#print axioms coarseRestrictSiteCovariantU_two_eq_gammaSum
#print axioms QprimeBalaban_apply
#print axioms coarse_hlt
#print axioms mem_ker_QprimeBalaban_iff
#print axioms gamma_poincare_of_mem_ker_balaban
#print axioms hlam_at_kappa_sq_768_qprime
#print axioms kappa_bound_and_criterion_closes_qprime
#print axioms gaugeParam_mem_ker_QprimeBalaban
#print axioms kappa_768_for_gaugeParam_qprime
#print axioms gammaTransport_trivialU
#print axioms gammaM_trivialU
#print axioms qprime_trivialU_is_flat_block_average
#print axioms gCorner_eq_iff_val
#print axioms sepLam_ne_zero
#print axioms sep_coarse_dichotomy
#print axioms sepLam_block_sum_at_sepS0
#print axioms sepLam_mem_ker_balaban
#print axioms sepLam_not_mem_ker_QprimeTwo
#print axioms ker_QprimeTwo_lt_ker_QprimeBalaban
#print axioms qprimeBalaban_ne_zero_at_sepLamPos
#print axioms ker_QprimeBalaban_ne_bot
#print axioms zeroSite_hlt
#print axioms coarse_reaches_small_imp_zero
#print axioms gCorner_zeroSite_eq_zero_iff
#print axioms qprimeBalaban_ne_zero
#print axioms originNbr_ne_zeroSite
#print axioms originNbr_small
#print axioms kerWitness_ne_zero
#print axioms kerWitness_mem_ker
#print axioms ker_QprimeBalaban_ne_bot_general
#print axioms RMap_eq_zero_iff
#print axioms originNbr_hlt
#print axioms kerWitness_not_mem_ker_QprimeTwo
#print axioms ker_QprimeTwo_lt_ker_QprimeBalaban_general
#print axioms gCorner_apply_axis
#print axioms coordSteps_gCorner
#print axioms gammaPath_gCorner
#print axioms gammaTransport_eq_periodicPathHolonomy_gammaPath
#print axioms QprimeBalaban_eq_Qcomposite_one

end AdalyFormal.Balaban.QPrimeDenotation
