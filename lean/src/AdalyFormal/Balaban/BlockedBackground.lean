/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.UbarTowerCovariance
import AdalyFormal.Balaban.BlockingLinkEstimate
import AdalyFormal.Balaban.RegularUPerturbation
import AdalyFormal.Balaban.CovariantFibreTransfer
import AdalyFormal.Balaban.CurvedTower
import AdalyFormal.Balaban.U1AnchorCoarse

set_option autoImplicit false
-- maxRecDepth 8000 STRIPPED 2026-08-01 (prosecution hygiene finding: not load-bearing; a bump that
-- changes nothing is dead weight and an unflagged refactor hazard -- §S class 6).

/-!
# `Ū` PINNED AT `SU(2)` — the blocked background as an ACTUAL MAP, and what it does to `frobSupBond`

## What the source says, and what it does NOT defer

CMP98 printed p.19 (`corpus/pages/CMP98_p19.md`, `verification_status: adjudicated`, 400 dpi
render `corpus/renders/CMP98_p19-03.png`) defines the averaging operation VERBATIM as

```
\bar{U}_c = \exp\Big[i \sum_{x\in B(c_-)} L^{-d}\frac{1}{i}\log U(\Gamma_{c,x})U(c)^{-1}\Big] U(c). \tag{15}
```

immediately after stating the two conditions it must satisfy — (11) gauge covariance
`(\overline{U^u})(y,y') = u(y)\bar{U}(y,y')u^{-1}(y'), \quad \text{or} \quad \overline{U^u} =
(\bar{U})^u.` (the overline SCOPE here is load-bearing and is what the corpus page's own
adjudication confirms against the machine draft), and that `(1/i)log Ū` approximate the
LINEAR averaging (14) `\bar{A}_c = \sum_{x\in B(c_-)} L^{-(d+1)}\big(A(\Gamma_{c_-,x}) + A([x,x(c)])
+ A(\Gamma_{x(c),c_+})\big).` — and after the framing sentence *"There are many ways of implementing
these two conditions. We will write now a definition of an average which satisfies these
conditions and which has some other advantages."*

**The `SU(2)` obstruction that (15) is designed to solve is the one the naive average has, and
(15) solves it in print.** A naive mean of group elements leaves `SU(2)`; (15) never forms one.
It averages in the LIE ALGEBRA, of the RELATIVE variable `U(Γ_{c,x})U(c)^{-1}` — a closed loop
based at `c_-`, hence near `1` for a regular configuration — and returns to the group by `exp`,
then multiplies `U(c)` back on the right. The output is in `SU(2)` by construction. There is no
deferral here, and neither a path-ordered-product fallback nor a minimizer is needed or used:
the right factor `U(c)` (the straight `ell`-fold bond product) is the only "designated path" in
the formula, and it enters as a REFERENCE POINT, not as the average.

## What was already in the tree, and what this module adds (LAW-19)

Searched before declaring anything (`grep Ubar|blocked|barU`, then by shape):

* `UbarTowerCov.stridedBlockedGauge P s ell V c` (`UbarTowerCovariance.lean:237`) IS eq. (15) at
  stride `s`, and `UbarTowerCov.UbarTower P ell U l` (`:310`) is (43)'s level-`l` recursion. Gauge
  covariance is PROVED there, unconditionally, for every `P : LogExpAd G 𝔤`.
* `SuTwoLogExp.su2LogExp : LogExpAd SU2 M2` (`SuTwoLogExpCore.lean:277`) is the genuine principal
  `SU(2)` logarithm `log g = (κ(g)/2)•(g − gᴴ)` with Mathlib's matrix exponential.
* `BlockingLinkEstimate` carries the `SU(2)` norm analysis — `frobNorm_su2Log_le_pi_div_two`
  (`‖log g‖_F ≤ (π/2)‖g−1‖_F`, unconditional), `frobNorm_su2Exp_sub_one_le`,
  `frobNorm_prod_sub_one_le` — and `blockedLink`/`blockedLink_sub_one_le`, which is (43) with the
  estimate `‖Ū_c − 1‖ ≤ Lreal·eps + (π/2·Nplaq)·beta` in an ABSTRACT
  `(Finset ι, weights, loops, Uc)` form with **no lattice geometry**.

Nothing here re-derives any of that; every norm fact used below is imported. Two holes are what
this module closes.

**Hole 1 — `Ū` was never a map.** `stridedBlockedGauge` is a function OF a free
`P : LogExpAd G 𝔤`, and `UbarTowerCovariance`'s own header records the consequence: *"`LogExpAd`
has degenerate inhabitants making `Ū = U`"*, with `BlockedGaugeGuard.lean` compiling three of them
(`trivialLogExp` with `log = 0, exp = 1`; `discardingRatLogExp`; `twistedRatLogExp q`). Against a
free `P`, EVERY statement about `Ū` is satisfiable by `Ū = U`, so no estimate about blocking can
have content. §1's `ubarSU2` instantiates at the concrete `su2LogExp`, so those inhabitants are
not available against any statement below.

**Hole 2 — the estimate was an ISLAND.** §4's `ubarSU2_eq_blockedLink` is an unconditional
identity carrying `BlockingLinkEstimate`'s abstract `(43)` onto the actual lattice object, so
`blockedLink_sub_one_le` becomes a statement about `ubarSU2` (§4's `ubarSU2_sub_one_le`).

## THE RESULT — blocking does NOT contract `frobSupBond`; it EXPANDS it

The task this module was dispatched for asked which way the key inequality goes:
`frobSupBond Ū ≤ f(frobSupBond U)` with `f(α) ≤ cα`, `c < 1`, or `c = O(ell)`? The answer is
not an estimate but an **exact identity** (§3):

  `ubarSU2 s ell (constU g) = constU (g ^ ell)`     (`ubarSU2_constU`)

for EVERY `s`, `ell`, `g` and `L`, with no regularity, divisibility or branch hypothesis. On
constant configurations the blocking map is *literally the `ell`-th power map on `SU(2)`*. Every
loop variable `U(Γ_{c,x})U(c)⁻¹` is `1` on the nose there — the staircase legs cancel as
`g^m · g^ell · g^{−m}` against `g^ell`, and powers of one element commute — so the algebra average
is `0`, `exp 0 = 1`, and only the reference factor `U(c) = g^ell` survives.

Consequences, all proved below:

* `frobSupBond (ubarSU2 s 2 (constU (gOf (24/25)))) = (7√2/5) · frobSupBond (constU (gOf (24/25)))`
  — an explicit **expansion by `7√2/5 = 1.97989…` at the campaign's stride `ell = 2`** (§5),
    with the decimal itself asserted by `expansion_factor_bounds` (`1.9798 < 7√2/5 < 1.9799`).
* `no_contraction_constant`: for EVERY `c < 2`, `∀ V, frobSupBond (ubarSU2 s 2 V) ≤ c ·
  frobSupBond V` is FALSE (§6). In particular no `c < 1` exists, and no `c = 1` either; and `2`
  is the exact supremum, since `frobNorm_pow_sub_one_le` gives `≤ 2` on constants.
* `no_contraction_at_any_ell`: at EVERY `ell ≥ 1` the same holds for every `c < 2·ell/π`, so the
  expansion is not a stride-2 artefact — it grows linearly in `ell` (§6).
* `threshold_not_preserved`: an explicit configuration satisfying the tree's OWN regularity
  threshold `frobSupBond U ≤ 1/(100·ell⁴)` at `ell = 2` whose blocking VIOLATES it (§7).

**Why this matters for the depth question, stated exactly.** Every coercivity hypothesis in this
tree is of the form `frobSupBond U ≤ α₀` with a FIXED threshold (e.g.
`GeneralUHodgeControls`'s `1/(100·ell⁴)`). §7 makes the consequence a theorem: a configuration can
satisfy the threshold while its blocking does not. So the per-level renormalization route — feed
`Ū` to the next level and hope the regularity improves — **cannot work in this functional**: the
functional is not merely non-contracted, it is multiplied by up to `ell` per level, and the tower
iterates that (`ubarTowerSU2_constU`: `Ū^l (constU g) = constU (g ^ ell^l)`).

**Three honest limits on that reading, stated so nobody over-reads it.**

1. **This is the UNRESCALED functional.** Bałaban's renormalization group rescales the lattice
   spacing at each step, and a coarse bond spans `ell` fine bonds, so a factor of `ell` in
   `‖U(c) − 1‖` is exactly what a smooth field must produce — it is dimensionally forced, not a
   pathology of (15). What §3–§7 establish is that `frobSupBond` AS THIS TREE USES IT (no
   rescaling, fixed `α₀`) is the wrong bookkeeping for a multi-level statement, not that
   Bałaban's scheme fails. The named missing object is a per-level rescaled regularity functional;
   none exists in this tree and this module does not build one.
2. **The expansion SATURATES.** `frobNorm (g − 1) ≤ 2√2` for every `g : SU2`
   (`frobNorm_sub_one_le_two_sqrt_two`, §4), so growth cannot compound past that ceiling; the
   `ell`-per-level factor is a small-deviation statement. The naive reading "the deviation grows
   like `ell^l` forever" is FALSE and is not asserted here.
3. **§3 is exact only on CONSTANTS.** For general `V` the upper bound is §4's
   `ubarSU2_sub_one_le`, which is conditional on a loop bound and a branch condition; §8 records
   what blocked the unconditional version.

## What is NOT claimed

* No claim that `ell` is the SHARP expansion constant for `ell ≠ 2`. §6 proves `≥ 2·ell/π` at
  every `ell` and the sharp `2` at `ell = 2`; §8 states the exact analytic gap between them.
* Nothing here weakens `TowerLawCov.tower_law_cov_refuted`, which refutes the covariant tower law
  for the AVERAGING operator at a curved background. That is a different statement.
-/

namespace AdalyFormal.Balaban.BlockedBackground

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2LogExp su2Log su2Exp)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge UbarTower coarseBondVar
  gammaVarStrided loopVar cPlusS)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.CovariantFibreTransfer (constU)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.BlockingLinkEstimate (su2Of su2Of_mem blockExponent blockedLink)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `Ū` AT `SU(2)`: the map `U ↦ Ū` that the tree did not have -/

/-- **`Ū` — CMP98 (15), with `log`/`exp` PINNED to `SU(2)`.**

`Ū_c = exp[ Σ_{x ∈ B_s(c_-)} ell^{-3} · log (V(Γ_{c,x}) V(c)⁻¹) ] · V(c)`

with `log` the genuine principal `SU(2)` logarithm `(κ(g)/2)•(g − gᴴ)` and `exp` Mathlib's matrix
exponential (`SuTwoLogExp.su2LogExp`). This is a CONCRETE map on configurations: unlike
`stridedBlockedGauge P`, it is not a function of a free `LogExpAd`, so the degenerate inhabitants
that force `Ū = U` (`BlockedGaugeGuard.lean`'s `trivialLogExp`, `discardingRatLogExp`,
`twistedRatLogExp`) are not available against any statement below. -/
noncomputable def ubarSU2 (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L) :
    PeriodicLinkConfiguration SU2 L :=
  stridedBlockedGauge su2LogExp s ell V

@[simp] theorem ubarSU2_apply (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) :
    ubarSU2 s ell V c = stridedBlockedGauge su2LogExp s ell V c := rfl

/-- **The level-`l` blocked background at `SU(2)`** — CMP98 (43)'s recursion, `Ū^0 = U`,
`Ū^{l+1}` the one-step blocking of `Ū^l` at stride `ell^l`. -/
noncomputable def ubarTowerSU2 (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) (l : ℕ) :
    PeriodicLinkConfiguration SU2 L :=
  UbarTower su2LogExp ell U l

@[simp] theorem ubarTowerSU2_zero (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) :
    ubarTowerSU2 ell U 0 = U := rfl

@[simp] theorem ubarTowerSU2_succ (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) (l : ℕ) :
    ubarTowerSU2 ell U (l + 1) = ubarSU2 (ell ^ l) ell (ubarTowerSU2 ell U l) := rfl

/-! ## §2 — gauge covariance, INHERITED (not re-derived)

CMP98 p.19 (11) is `UbarTowerCov.stridedBlockedGauge_gauge`, proved there for every `LogExpAd`.
Specialising it is a one-liner; it is recorded so that a consumer of `ubarSU2` can cite covariance
without unfolding the definition. -/

/-- **CMP98 (11) at the pinned `SU(2)` blocking.** -/
theorem ubarSU2_gauge (s ell : ℕ) (γ : PeriodicLatticeSite L → SU2)
    (V : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) :
    ubarSU2 s ell (AdalyFormal.Balaban.QjComposite.coarseGaugeTransform s γ V) c
      = AdalyFormal.Balaban.QjComposite.coarseGaugeTransform (s * ell) γ (ubarSU2 s ell V) c :=
  AdalyFormal.Balaban.UbarTowerCov.stridedBlockedGauge_gauge su2LogExp s ell γ V c

/-! ## §3 — THE EXACT IDENTITY: on constants, blocking IS the `ell`-th power map -/

/-- Transport of a CONSTANT configuration along any strided path is `g` to the path's length. -/
theorem coarsePathHolonomy_constU (s : ℕ) (g : SU2) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) :
    coarsePathHolonomy s (constU g L) y p = g ^ p.length := by
  induction p generalizing y with
  | nil => rfl
  | cons μ rest ih =>
      show constU g L (y, μ) * coarsePathHolonomy s (constU g L) _ rest = _
      rw [ih]
      show g * g ^ rest.length = g ^ (rest.length + 1)
      rw [pow_succ]
      exact (Commute.refl g).pow_right _

/-- `V(c) = g^ell` on a constant configuration: the coarse bond variable is the `ell`-fold product
of the constant link. -/
theorem coarseBondVar_constU (s ell : ℕ) (g : SU2) (c : PeriodicLatticeEdge L) :
    coarseBondVar s ell (constU g L) c = g ^ ell := by
  show coarsePathHolonomy s (constU g L) c.1 (List.replicate ell c.2) = _
  rw [coarsePathHolonomy_constU, List.length_replicate]

/-- **The contour variable equals the straight bond variable on constants.** Both legs of the
`Γ_{c,x}` staircase contribute `g^m` and `g^{−m}` around the middle `g^ell`, and powers of one
element commute, so the staircase cancels IDENTICALLY — for every `x`, with no hypothesis on `x`,
on `ell`, on `s`, or on the lattice. -/
theorem gammaVarStrided_constU (s ell : ℕ) (g : SU2) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) :
    gammaVarStrided s ell (constU g L) c x = g ^ ell := by
  show coarsePathHolonomy s (constU g L) c.1 (coarseGammaPath s c.1 x)
      * coarsePathHolonomy s (constU g L) x (List.replicate ell c.2)
      * (coarsePathHolonomy s (constU g L) (cPlusS s ell c) (coarseGammaPath s c.1 x))⁻¹ = _
  rw [coarsePathHolonomy_constU, coarsePathHolonomy_constU, coarsePathHolonomy_constU,
    List.length_replicate]
  have hcomm : g ^ (coarseGammaPath s c.1 x).length * g ^ ell
      = g ^ ell * g ^ (coarseGammaPath s c.1 x).length := by
    rw [← pow_add, ← pow_add, Nat.add_comm]
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

/-- **Every CMP98 (15) loop variable is trivial on a constant configuration.** This is what makes
§3's identity exact rather than approximate: the algebra average is a sum of `log 1 = 0`. -/
theorem loopVar_constU (s ell : ℕ) (g : SU2) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) :
    loopVar s ell (constU g L) c x = 1 := by
  show gammaVarStrided s ell (constU g L) c x * (coarseBondVar s ell (constU g L) c)⁻¹ = 1
  rw [gammaVarStrided_constU, coarseBondVar_constU, mul_inv_cancel]

/-- **THE IDENTITY. `Ū(constant g) = constant g^ell`, exactly, for every `s`, `ell`, `g`, `L`.**

The blocking map, restricted to constant configurations, IS the `ell`-th power map on `SU(2)`.
No regularity hypothesis, no divisibility, no branch-domain condition: the logarithm is only ever
evaluated at `1`, where it is `0` unambiguously, so the branch obstruction
(`SuTwoLogExpTorus.exp_log_fails_at_center`) is not in play. -/
theorem ubarSU2_constU (s ell : ℕ) (g : SU2) :
    ubarSU2 s ell (constU g L) = constU (g ^ ell) L := by
  funext c
  show su2LogExp.exp (∑ x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell,
      ((ell : ℚ) ^ 3)⁻¹ • su2LogExp.log (loopVar s ell (constU g L) c x))
      * coarseBondVar s ell (constU g L) c = g ^ ell
  have hzero : ∀ x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell,
      ((ell : ℚ) ^ 3)⁻¹ • su2LogExp.log (loopVar s ell (constU g L) c x) = (0 : M2) := by
    intro x _
    rw [loopVar_constU]
    show ((ell : ℚ) ^ 3)⁻¹ • su2Log (1 : SU2) = 0
    rw [AdalyFormal.Balaban.SuTwoLogExp.su2Log_one, smul_zero]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, coarseBondVar_constU]
  show (su2Exp (0 : M2) : SU2) * g ^ ell = g ^ ell
  rw [AdalyFormal.Balaban.SuTwoLogExp.su2Exp_zero, one_mul]

/-- **MUST-NOT-FIRE CONTROL.** At the flat background the blocking is the identity: `Ū(1) = 1`.
If this failed, every statement below would be measuring an artefact of the encoding rather than
the blocking. It is the `g = 1` case of `ubarSU2_constU`. -/
theorem ubarSU2_trivialU (s ell : ℕ) : ubarSU2 s ell (trivialU L) = trivialU L := by
  have h : (trivialU L) = constU (1 : SU2) L := rfl
  rw [h, ubarSU2_constU, one_pow]

/-- **The tower on constants: `Ū^l (constant g) = constant g^(ell^l)`.** -/
theorem ubarTowerSU2_constU (ell : ℕ) (g : SU2) (l : ℕ) :
    ubarTowerSU2 ell (constU g L) l = constU (g ^ ell ^ l) L := by
  induction l with
  | zero => simp
  | succ n ih =>
      rw [ubarTowerSU2_succ, ih, ubarSU2_constU, ← pow_mul, ← pow_succ]

/-! ## §4 — `frobSupBond` on constants, the ceiling, and the BRIDGE to `BlockingLinkEstimate` -/

/-- `frobSupBond` of a constant configuration is the single link's deviation. -/
theorem frobSupBond_constU (g : SU2) :
    frobSupBond (constU g L) = frobNorm ((g : M2) - 1) := by
  unfold frobSupBond
  exact Finset.sup'_const _ (frobNorm ((g : M2) - 1))

/-- **`‖g^n − 1‖_F ≤ n·‖g − 1‖_F`** — the upper half of the blocking estimate ON CONSTANTS. With
`ubarSU2_constU` this says `frobSupBond (ubarSU2 s ell (constU g)) ≤ ell · frobSupBond (constU g)`;
§5–§6 show the constant `ell` cannot be lowered at `ell = 2`. -/
theorem frobNorm_pow_sub_one_le (g : SU2) (n : ℕ) :
    frobNorm (((g ^ n : SU2) : M2) - 1) ≤ (n : ℝ) * frobNorm ((g : M2) - 1) := by
  induction n with
  | zero =>
      rw [pow_zero, Nat.cast_zero, zero_mul]
      rw [AdalyFormal.Balaban.SuTwoLogExp.coe_one, sub_self]
      exact le_of_eq AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero
  | succ k ih =>
      have hstep : frobNorm (((g ^ (k + 1) : SU2) : M2) - 1)
          ≤ frobNorm (((g ^ k : SU2) : M2) - 1) + frobNorm ((g : M2) - 1) := by
        rw [pow_succ]
        exact AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le _ _
      refine le_trans hstep ?_
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [ih]

/-- **`frobSupBond` at a blocked CONSTANT background is at most `ell` times the input.** The
combination of §3's identity with the telescoping bound: the honest `f` of the task's question,
on constants. -/
theorem frobSupBond_ubarSU2_constU_le (s ell : ℕ) (g : SU2) :
    frobSupBond (ubarSU2 s ell (constU g L)) ≤ (ell : ℝ) * frobSupBond (constU g L) := by
  rw [ubarSU2_constU, frobSupBond_constU, frobSupBond_constU]
  exact frobNorm_pow_sub_one_le g ell

/-- **THE CEILING.** `‖g − 1‖_F ≤ 2√2` for every `g : SU(2)`, attained at `g = −1`. Growth in
`frobSupBond` therefore cannot compound indefinitely; §3's `ell`-per-level factor is a
small-deviation statement, and this theorem is why the header refuses to assert `ell^l` growth. -/
theorem frobNorm_sub_one_le_two_sqrt_two (g : SU2) :
    frobNorm ((g : M2) - 1) ≤ 2 * Real.sqrt 2 := by
  rw [AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sub_one_eq g]
  have h1 : Real.sin (AdalyFormal.Balaban.SuTwoLogExp.su2Angle g / 2) ≤ 1 := Real.sin_le_one _
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- **THE BRIDGE — `ubarSU2` IS `BlockingLinkEstimate.blockedLink` at the lattice data.**

`BlockingLinkEstimate`'s (43) is stated over an abstract `(Finset ι, weights, loops, Uc)` with no
lattice geometry; this identity supplies the geometry, so every estimate proved there is a
statement about the actual blocked background. Unconditional in `s`, `ell`, `V`, `c`, `L`. -/
theorem qsmul_eq_csmul (ell : ℕ) (X : M2) :
    ((ell : ℚ) ^ 3)⁻¹ • X = (((((ell : ℝ) ^ 3)⁻¹ : ℝ)) : ℂ) • X := by
  rw [← Rat.cast_smul_eq_qsmul ℂ (((ell : ℚ) ^ 3)⁻¹) X]
  congr 1
  push_cast
  ring

theorem ubarSU2_eq_blockedLink (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) :
    ubarSU2 s ell V c
      = blockedLink (AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell)
          (fun _ => ((ell : ℝ) ^ 3)⁻¹) (fun x => loopVar s ell V c x)
          (coarseBondVar s ell V c) := by
  show su2Exp (∑ x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell,
      ((ell : ℚ) ^ 3)⁻¹ • su2Log (loopVar s ell V c x)) * coarseBondVar s ell V c
    = blockedLink _ _ _ _
  unfold blockedLink blockExponent
  congr 2
  exact Finset.sum_congr rfl (fun x _ => qsmul_eq_csmul ell _)

/-! ### §4a — the two hypotheses of the abstract estimate that the LATTICE discharges

`blockedLink_sub_one_le` takes `hsum` (the `L^{-d}` normalisation) and `hUc` (the coarse bond
spans `ell` fine bonds) as hypotheses because it has no geometry. Here there IS geometry, so both
are theorems rather than assumptions. What remains genuinely assumed is only `hloop` (the
closed-loop curvature bound, which needs a spanning surface) and `hbranch` (the principal-branch
condition, which is the known `[BLOCKED-BRANCH-DOMAIN]` obstruction) — see §8. -/

/-- **Path telescoping at stride `s`.** `‖coarsePathHolonomy s V y p − 1‖_F ≤ |p|·frobSupBond V`. -/
theorem frobNorm_coarsePathHolonomy_sub_one_le (s : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    frobNorm (((coarsePathHolonomy s V y p : SU2) : M2) - 1) ≤ (p.length : ℝ) * frobSupBond V := by
  induction p generalizing y with
  | nil =>
      show frobNorm (((1 : SU2) : M2) - 1) ≤ _
      rw [AdalyFormal.Balaban.SuTwoLogExp.coe_one, sub_self, List.length_nil, Nat.cast_zero,
        zero_mul]
      exact le_of_eq AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero
  | cons μ rest ih =>
      show frobNorm (((V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) rest : SU2) : M2)
        - 1) ≤ _
      refine le_trans (AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le _ _) ?_
      have h1 : frobNorm ((V (y, μ) : M2) - 1) ≤ frobSupBond V :=
        AdalyFormal.Balaban.RegularUPerturbation.frobNorm_le_frobSupBond V (y, μ)
      have h2 := ih (coarseShift y s μ)
      rw [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- **`hUc`, DISCHARGED.** `‖V(c) − 1‖_F ≤ ell·frobSupBond V`: the coarse bond variable is the
product of the `ell` strided links along `c`. -/
theorem frobNorm_coarseBondVar_sub_one_le (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) :
    frobNorm (((coarseBondVar s ell V c : SU2) : M2) - 1) ≤ (ell : ℝ) * frobSupBond V := by
  have h := frobNorm_coarsePathHolonomy_sub_one_le s V c.1 (List.replicate ell c.2)
  rwa [List.length_replicate] at h

/-- **`hsum`, DISCHARGED.** The `ell^{-3}` weights sum to `1` exactly when the block really has
`ell³` sites — i.e. under `QjComposite.card_stepBlockOf`'s hypotheses. This is the
`[BLOCKED-BLOCK-DOMAIN]` condition made explicit rather than assumed: without `hfit` the block
TRUNCATES (`QjComposite.card_stepBlockOf_truncates`: `8` sites where `27` are expected) and the
weights sum to less than `1`. -/
theorem weight_sum_eq_one {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell)
    (y : PeriodicLatticeSite L) (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1) :
    ∑ _x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf y s ell, ((ell : ℝ) ^ 3)⁻¹ = 1 := by
  rw [Finset.sum_const, AdalyFormal.Balaban.QjComposite.card_stepBlockOf y s ell hs hfit,
    nsmul_eq_mul]
  have : ((ell : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  push_cast
  field_simp

/-- **The blocking estimate, TRANSPORTED to the lattice object.** `blockedLink_sub_one_le` applied
through the bridge: `‖Ū_c − 1‖_F ≤ ell·eps + (π/2·Nplaq)·beta`, where `eps` bounds the fine links
along `c` and `beta` the loop variables. The three hypotheses are exactly the source's: `hsum` is
the `L^{-d}` normalisation (i.e. `|B(c_-)| = ell³`), `hloop` is the closed-loop curvature bound,
`hbranch` is (23)'s principal branch. -/
theorem ubarSU2_sub_one_le (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) (Lreal eps Nplaq beta : ℝ)
    (hsum : ∑ _x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell,
      ((ell : ℝ) ^ 3)⁻¹ = 1)
    (hUc : frobNorm (((coarseBondVar s ell V c : SU2) : M2) - 1) ≤ Lreal * eps)
    (hloop : ∀ x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell,
      frobNorm (((loopVar s ell V c x : SU2) : M2) - 1) ≤ Nplaq * beta)
    (hbranch : su2Log (su2Exp (blockExponent
        (AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell)
        (fun _ => ((ell : ℝ) ^ 3)⁻¹) (fun x => loopVar s ell V c x)))
      = blockExponent (AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell)
        (fun _ => ((ell : ℝ) ^ 3)⁻¹) (fun x => loopVar s ell V c x)) :
    frobNorm ((ubarSU2 s ell V c : M2) - 1) ≤ Lreal * eps + (Real.pi / 2 * Nplaq) * beta := by
  rw [ubarSU2_eq_blockedLink]
  exact AdalyFormal.Balaban.BlockingLinkEstimate.blockedLink_sub_one_le _ _ _ _
    Lreal eps Nplaq beta (fun _ _ => by positivity) hsum hUc hloop hbranch

/-- **THE BLOCKING ESTIMATE AT THE LATTICE OBJECT, with only the two SOURCE-LEVEL inputs left.**

`‖Ū(c) − 1‖_F ≤ ell·frobSupBond V + (π/2 · Nplaq)·beta`

`hsum` and `hUc` are gone: §4a proves them from the geometry. The two remaining hypotheses are
exactly the two things the source supplies and this tree does not yet have (§8):

* `hloop` — each `W_x = V(Γ_{c,x})V(c)⁻¹` is a closed loop, so it is controlled by
  (plaquettes of a spanning surface)×(curvature). `BlockingLinkEstimate.plaqCount 3 ell` COUNTS
  the plaquettes (`= 7` at `ell = 2`); what is missing is the surface itself.
* `hbranch` — the principal branch of (23). This is `[BLOCKED-BRANCH-DOMAIN]`, and
  `SuTwoLogExpTorus.exp_log_fails_at_center` shows it is not removable.

Note that `hfit` is not decoration: without it the averaging block truncates and the weights do
not sum to `1`. -/
theorem ubarSU2_sub_one_le_lattice {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell)
    (V : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) (Nplaq beta : ℝ)
    (hfit : ∀ μ, (c.1 μ).val + s * ell ≤ L μ + 1)
    (hloop : ∀ x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell,
      frobNorm (((loopVar s ell V c x : SU2) : M2) - 1) ≤ Nplaq * beta)
    (hbranch : su2Log (su2Exp (blockExponent
        (AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell)
        (fun _ => ((ell : ℝ) ^ 3)⁻¹) (fun x => loopVar s ell V c x)))
      = blockExponent (AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell)
        (fun _ => ((ell : ℝ) ^ 3)⁻¹) (fun x => loopVar s ell V c x)) :
    frobNorm (((ubarSU2 s ell V c : SU2) : M2) - 1)
      ≤ (ell : ℝ) * frobSupBond V + (Real.pi / 2 * Nplaq) * beta :=
  ubarSU2_sub_one_le s ell V c (ell : ℝ) (frobSupBond V) Nplaq beta
    (weight_sum_eq_one hs hell c.1 hfit)
    (frobNorm_coarseBondVar_sub_one_le s ell V c) hloop hbranch

/-! ## §5 — THE EXPANSION, COMPUTED EXACTLY

The witnesses are the diagonal one-parameter family `gOf t = diag(e^{iφ}, e^{-iφ})` with
`cos φ = t`. Everything below is exact: `frobSq (gOf t ^ n − 1) = 4(1 − cos(n·arccos t))`, and at
`n = 2` the double-angle formula makes it a RATIONAL function of `t`. -/

/-- The unit complex number `e^{iφ}`. -/
noncomputable def zc (φ : ℝ) : ℂ := Complex.exp ((φ : ℂ) * Complex.I)

theorem zc_re (φ : ℝ) : (zc φ).re = Real.cos φ := by
  rw [zc, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem zc_im (φ : ℝ) : (zc φ).im = Real.sin φ := by
  rw [zc, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem zc_normSq (φ : ℝ) : Complex.normSq (zc φ) = 1 := by
  rw [Complex.normSq_apply, zc_re, zc_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem zc_mul_star (φ : ℝ) : zc φ * star (zc φ) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, zc_normSq]
  norm_num

theorem zc_add (φ ψ : ℝ) : zc φ * zc ψ = zc (φ + ψ) := by
  rw [zc, zc, zc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem zc_zero : zc 0 = 1 := by
  rw [zc]
  norm_num

/-- **The diagonal `SU(2)` element of angle `φ`.** -/
noncomputable def diagSU2 (φ : ℝ) : SU2 :=
  ⟨su2Of (zc φ) 0, su2Of_mem _ _ (by rw [zc_mul_star]; simp)⟩

@[simp] theorem coe_diagSU2 (φ : ℝ) : ((diagSU2 φ : SU2) : M2) = su2Of (zc φ) 0 := rfl

theorem su2Of_mul_su2Of (a a' : ℂ) :
    su2Of a 0 * su2Of a' 0 = su2Of (a * a') 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Of, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagSU2_pow (φ : ℝ) (n : ℕ) : (diagSU2 φ) ^ n = diagSU2 ((n : ℝ) * φ) := by
  induction n with
  | zero =>
      apply Subtype.ext
      rw [pow_zero, AdalyFormal.Balaban.SuTwoLogExp.coe_one, coe_diagSU2, Nat.cast_zero, zero_mul,
        zc_zero]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [su2Of]
  | succ k ih =>
      apply Subtype.ext
      rw [pow_succ]
      show ((diagSU2 φ ^ k : SU2) : M2) * ((diagSU2 φ : SU2) : M2) = _
      rw [ih, coe_diagSU2, coe_diagSU2, coe_diagSU2, su2Of_mul_su2Of, zc_add]
      congr 2
      push_cast
      ring

/-- `frobSq` of a DIAGONAL `SU(2)` element minus `1`, in terms of the real part alone. -/
theorem frobSq_su2Of_diag_sub_one (z : ℂ) (hz : Complex.normSq z = 1) :
    frobSq (su2Of z 0 - 1) = 4 * (1 - z.re) := by
  have h01 : ((1 : M2) 0 1) = 0 := Matrix.one_apply_ne (by decide)
  have h10 : ((1 : M2) 1 0) = 0 := Matrix.one_apply_ne (by decide)
  have h00 : ((1 : M2) 0 0) = 1 := Matrix.one_apply_eq _
  have h11 : ((1 : M2) 1 1) = 1 := Matrix.one_apply_eq _
  simp only [frobSq, Matrix.sub_apply,
    AdalyFormal.Balaban.BlockingLinkEstimate.su2Of_00,
    AdalyFormal.Balaban.BlockingLinkEstimate.su2Of_01,
    AdalyFormal.Balaban.BlockingLinkEstimate.su2Of_10,
    AdalyFormal.Balaban.BlockingLinkEstimate.su2Of_11, h00, h01, h10, h11]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, star_zero, neg_zero, Complex.zero_re,
    Complex.zero_im]
  simp only [Complex.normSq_apply] at hz
  nlinarith [hz]

/-- **THE MASTER FORMULA.** `frobSq (g^n − 1) = 4(1 − cos(nφ))` for `g = diagSU2 φ`. Both the
input deviation (`n = 1`) and the blocked deviation (`n = ell`) are read off this one line. -/
theorem frobSq_diagSU2_pow (φ : ℝ) (n : ℕ) :
    frobSq (((diagSU2 φ ^ n : SU2) : M2) - 1) = 4 * (1 - Real.cos ((n : ℝ) * φ)) := by
  rw [diagSU2_pow, coe_diagSU2, frobSq_su2Of_diag_sub_one _ (zc_normSq _), zc_re]

theorem frobNorm_diagSU2_pow (φ : ℝ) (n : ℕ) :
    frobNorm (((diagSU2 φ ^ n : SU2) : M2) - 1) = Real.sqrt (4 * (1 - Real.cos ((n : ℝ) * φ))) := by
  unfold frobNorm
  rw [frobSq_diagSU2_pow]

/-- The witness family indexed by the COSINE of the angle: `gOf t` has `‖gOf t − 1‖²_F = 4(1−t)`. -/
noncomputable def gOf (t : ℝ) : SU2 := diagSU2 (Real.arccos t)

theorem frobSq_gOf (t : ℝ) (ht : -1 ≤ t) (ht' : t ≤ 1) :
    frobSq (((gOf t : SU2) : M2) - 1) = 4 * (1 - t) := by
  have h := frobSq_diagSU2_pow (Real.arccos t) 1
  rw [pow_one] at h
  rw [gOf, h, Nat.cast_one, one_mul, Real.cos_arccos ht ht']

theorem frobSq_gOf_sq (t : ℝ) (ht : -1 ≤ t) (ht' : t ≤ 1) :
    frobSq ((((gOf t) ^ 2 : SU2) : M2) - 1) = 8 * (1 - t) * (1 + t) := by
  have h := frobSq_diagSU2_pow (Real.arccos t) 2
  rw [gOf, h]
  have h2 : ((2 : ℕ) : ℝ) * Real.arccos t = 2 * Real.arccos t := by push_cast; ring
  rw [h2, Real.cos_two_mul, Real.cos_arccos ht ht']
  ring

/-- **THE EXPANSION RATIO AT `ell = 2`, EXACTLY.** For `−1 ≤ t < 1`,

  `frobSupBond (ubarSU2 s 2 (constU (gOf t))) = √(2(1+t)) · frobSupBond (constU (gOf t))`.

`√(2(1+t)) → 2` as `t → 1⁻`. The `t = 24/25` instance below is `7√2/5 = 1.97989…` (`expansion_factor_bounds`). -/
theorem blocking_ratio_two (s : ℕ) (t : ℝ) (ht : -1 ≤ t) (ht' : t < 1) :
    frobSupBond (ubarSU2 s 2 (constU (gOf t) L))
      = Real.sqrt (2 * (1 + t)) * frobSupBond (constU (gOf t) L) := by
  rw [ubarSU2_constU, frobSupBond_constU, frobSupBond_constU]
  unfold frobNorm
  rw [frobSq_gOf_sq t ht (le_of_lt ht'), frobSq_gOf t ht (le_of_lt ht')]
  rw [← Real.sqrt_mul (by nlinarith : (0:ℝ) ≤ 2 * (1 + t))]
  congr 1
  ring

/-- The input deviation is nonzero away from `t = 1`: the ratio statement has teeth. -/
theorem frobSupBond_constU_gOf_pos (t : ℝ) (ht : -1 ≤ t) (ht' : t < 1) :
    0 < frobSupBond (constU (gOf t) L) := by
  rw [frobSupBond_constU]
  unfold frobNorm
  rw [frobSq_gOf t ht (le_of_lt ht')]
  exact Real.sqrt_pos.mpr (by nlinarith)

/-- **THE HEADLINE NUMBER.** At `t = 24/25` the blocking at stride `2` multiplies `frobSupBond`
by exactly `7√2/5 = 1.97989…`. Exact algebra, no limit. -/
theorem blocking_expands_at_24_25 (s : ℕ) :
    frobSupBond (ubarSU2 s 2 (constU (gOf (24/25)) L))
      = (7 * Real.sqrt 2 / 5) * frobSupBond (constU (gOf (24/25)) L) := by
  rw [blocking_ratio_two s (24/25) (by norm_num) (by norm_num)]
  congr 1
  rw [show (2 : ℝ) * (1 + 24/25) = (7/5) ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  ring

/-- **The decimal the header quotes, ASSERTED.** `1.9798 < 7√2/5 < 1.9799`. A docstring is not a
certificate: without this, "an expansion by `1.9799…`" would be a number no declaration proves. -/
theorem expansion_factor_bounds :
    (1.9798 : ℝ) < 7 * Real.sqrt 2 / 5 ∧ 7 * Real.sqrt 2 / 5 < 1.9799 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

/-! ## §6 — NO CONTRACTION CONSTANT EXISTS -/

/-- **`2` IS THE SUPREMUM, AND IT IS NOT ATTAINED BY ANY BOUND BELOW IT.**

For every `c < 2`, the claim "blocking at stride `2` contracts `frobSupBond` by `c`" is FALSE.
In particular there is no `c < 1` (no contraction), and not even `c = 1` (no non-expansion).
The statement is a REFUTATION of a universally quantified claim, so no existential over free data
is being handed to the prover (S91): the witness is constructed inside the proof from `c` itself,
as `constU (gOf (c²/4))`. -/
theorem no_contraction_constant (s : ℕ) {c : ℝ} (hc : c < 2) :
    ¬ (∀ V : PeriodicLinkConfiguration SU2 L,
        frobSupBond (ubarSU2 s 2 V) ≤ c * frobSupBond V) := by
  intro hall
  rcases le_or_gt c 0 with hneg | hpos
  · -- `t = 0`: ratio `√2 > 0 ≥ c`, and the input deviation is positive.
    have hpos0 : 0 < frobSupBond (constU (gOf 0) L) :=
      frobSupBond_constU_gOf_pos 0 (by norm_num) (by norm_num)
    have h := hall (constU (gOf 0) L)
    rw [blocking_ratio_two s 0 (by norm_num) (by norm_num)] at h
    have h2 : (1 : ℝ) ≤ Real.sqrt (2 * (1 + 0)) := by
      rw [show (2 : ℝ) * (1 + 0) = 2 by ring]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
    nlinarith
  · -- `t = c²/4 ∈ [0,1)`: ratio `√(2 + c²/2) > c`.
    have ht0 : (0 : ℝ) ≤ c ^ 2 / 4 := by positivity
    have ht1 : c ^ 2 / 4 < 1 := by nlinarith
    have hpos0 : 0 < frobSupBond (constU (gOf (c ^ 2 / 4)) L) :=
      frobSupBond_constU_gOf_pos _ (by linarith) ht1
    have h := hall (constU (gOf (c ^ 2 / 4)) L)
    rw [blocking_ratio_two s (c ^ 2 / 4) (by linarith) ht1] at h
    have hsq : Real.sqrt (2 * (1 + c ^ 2 / 4)) ^ 2 = 2 * (1 + c ^ 2 / 4) :=
      Real.sq_sqrt (by nlinarith)
    have hgt : c < Real.sqrt (2 * (1 + c ^ 2 / 4)) := by
      nlinarith [Real.sqrt_nonneg (2 * (1 + c ^ 2 / 4)), hsq]
    nlinarith

/-- **NO CONTRACTION AT ANY STRIDE, with a LINEARLY GROWING lower bound.**

At every `ell ≥ 1`, blocking fails every contraction constant `c < 2·ell/π`. The witness is the
angle `φ = π/ell`, whose `ell`-th power is the centre element `−1` (maximal deviation `2√2`),
while the input deviation is `2√2·sin(π/(2ell)) ≤ 2√2·π/(2ell)`. So the expansion is not an
artefact of stride `2`: it grows linearly in `ell`, which is exactly the dimensional factor a
coarse bond spanning `ell` fine bonds must carry. -/
theorem no_contraction_at_any_ell (s ell : ℕ) (hell : 1 ≤ ell) {c : ℝ}
    (hc : c < 2 * (ell : ℝ) / Real.pi) :
    ¬ (∀ V : PeriodicLinkConfiguration SU2 L,
        frobSupBond (ubarSU2 s ell V) ≤ c * frobSupBond V) := by
  intro hall
  have hpi := Real.pi_pos
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set φ : ℝ := Real.pi / (ell : ℝ) with hφ
  have hφpos : 0 < φ := by positivity
  have hφle : φ ≤ Real.pi := by
    rw [hφ]
    exact div_le_self (le_of_lt hpi) (by exact_mod_cast hell)
  -- input deviation
  have hin : frobSupBond (constU (diagSU2 φ) L) = Real.sqrt (4 * (1 - Real.cos φ)) := by
    rw [frobSupBond_constU]
    have := frobNorm_diagSU2_pow φ 1
    rw [pow_one, Nat.cast_one, one_mul] at this
    exact this
  -- blocked deviation: `φ·ell = π`, so `cos = −1`
  have hcos : Real.cos ((ell : ℝ) * φ) = -1 := by
    rw [hφ, mul_div_cancel₀ _ (ne_of_gt hellR), Real.cos_pi]
  have hout : frobSupBond (ubarSU2 s ell (constU (diagSU2 φ) L)) = Real.sqrt 8 := by
    rw [ubarSU2_constU, frobSupBond_constU]
    have := frobNorm_diagSU2_pow φ ell
    rw [hcos] at this
    rw [this]
    norm_num
  have h := hall (constU (diagSU2 φ) L)
  rw [hout, hin] at h
  -- `1 − cos φ = 2 sin²(φ/2) ≤ φ²/2`, via the double-angle formula only
  have hhalf : Real.sin (φ / 2) ≤ φ / 2 := Real.sin_le (by positivity)
  have hsinpos : 0 < Real.sin (φ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hcosφ : 1 - Real.cos φ = 2 * Real.sin (φ / 2) ^ 2 := by
    have h2 : Real.cos (2 * (φ / 2)) = 2 * Real.cos (φ / 2) ^ 2 - 1 := Real.cos_two_mul _
    have h3 : (2 : ℝ) * (φ / 2) = φ := by ring
    rw [h3] at h2
    have h4 := Real.sin_sq_add_cos_sq (φ / 2)
    linarith
  have hbound : 4 * (1 - Real.cos φ) ≤ φ ^ 2 * 2 := by rw [hcosφ]; nlinarith
  have hin_le : Real.sqrt (4 * (1 - Real.cos φ)) ≤ Real.sqrt (φ ^ 2 * 2) :=
    Real.sqrt_le_sqrt hbound
  have hφ2 : Real.sqrt (φ ^ 2 * 2) = φ * Real.sqrt 2 := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hφpos)]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hinpos : 0 < Real.sqrt (4 * (1 - Real.cos φ)) := by
    refine Real.sqrt_pos.mpr ?_
    rw [hcosφ]
    nlinarith
  rw [h8] at h
  -- `c > 0`, else the RHS is nonpositive while the LHS is positive
  have hcpos : 0 < c := by
    rcases le_or_gt c 0 with hc0 | hc0
    · exfalso; nlinarith
    · exact hc0
  -- `2√2 ≤ c·A ≤ c·φ√2`, hence `2 ≤ cφ = cπ/ell`
  have hchain : 2 * Real.sqrt 2 ≤ c * (φ * Real.sqrt 2) := by
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hcpos)
    rw [← hφ2]; exact hin_le
  have hcφ : 2 ≤ c * φ := by nlinarith
  have hA1 : 2 * (ell : ℝ) ≤ c * Real.pi := by
    rw [hφ] at hcφ
    rw [div_eq_mul_inv, ← mul_assoc] at hcφ
    have := mul_le_mul_of_nonneg_right hcφ (le_of_lt hellR)
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hellR), mul_one] at this
    linarith
  have hA2 : c * Real.pi < 2 * (ell : ℝ) := by
    rw [lt_div_iff₀ hpi] at hc
    linarith
  linarith

/-! ## §7 — THE THRESHOLD CONSEQUENCE -/

/-- **THE TREE'S OWN REGULARITY THRESHOLD IS NOT PRESERVED BY THE TREE'S OWN BLOCKING.**

`GeneralUHodgeControls` and the coercivity chain hypothesise `frobSupBond U ≤ 1/(100·ell⁴)`, which
at `ell = 2` is `1/1600`. The configuration `constU (gOf t)` with `t = 1 − 1/(2·1600²·2)` satisfies
it, and its blocking VIOLATES it.

Concretely `t := 1 − 1/10240000`:
* `frobSupBond (constU (gOf t)) = √(4·(1−t)) = √(1/2560000) = 1/1600`, exactly the threshold;
* `frobSupBond (ubarSU2 s 2 (constU (gOf t))) = √(2(1+t))·(1/1600) ≥ 1.99/1600 > 1/1600`.

So one blocking step takes a configuration ON the admissible boundary to one outside it. Any
multi-level statement that re-uses a FIXED `α₀` at every level is therefore not fed by blocking —
the named missing object is a per-level rescaled regularity functional. -/
theorem threshold_not_preserved (s : ℕ) :
    frobSupBond (constU (gOf (1 - 1/10240000)) L) ≤ 1 / (100 * (2 : ℝ) ^ 4)
      ∧ ¬ (frobSupBond (ubarSU2 s 2 (constU (gOf (1 - 1/10240000)) L))
            ≤ 1 / (100 * (2 : ℝ) ^ 4)) := by
  have ht : (-1 : ℝ) ≤ 1 - 1/10240000 := by norm_num
  have ht' : (1 : ℝ) - 1/10240000 < 1 := by norm_num
  have hin : frobSupBond (constU (gOf (1 - 1/10240000)) L) = 1 / 1600 := by
    rw [frobSupBond_constU]
    unfold frobNorm
    rw [frobSq_gOf _ ht (le_of_lt ht')]
    rw [show (4 : ℝ) * (1 - (1 - 1/10240000)) = (1/1600) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  constructor
  · rw [hin]; norm_num
  · intro hle
    rw [blocking_ratio_two s _ ht ht', hin] at hle
    -- `√(2(1+t)) ≥ √3 > 1`, so the product exceeds `1/1600`
    -- `√(2(1+t)) ≥ 1.99`, so the blocked value is at least `1.99/1600`
    have hge : (1.99 : ℝ) ≤ Real.sqrt (2 * (1 + (1 - 1/10240000))) := by
      rw [show (1.99 : ℝ) = Real.sqrt (1.99 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have : (1 : ℝ) / 1600 < Real.sqrt (2 * (1 + (1 - 1/10240000))) * (1 / 1600) := by
      nlinarith
    rw [show (1 : ℝ) / (100 * (2:ℝ)^4) = 1/1600 by norm_num] at hle
    linarith

/-- **THE GROWTH RECURSION, WITH THE BLOCKING ESTIMATE INSERTED.** The task asked what the
`ρ`-recursion becomes at blocked backgrounds. On constants the answer is unconditional and it is
the WRONG direction: writing `α_l := frobSupBond (ubarTowerSU2 ell (constU g) l)`, we have
`α_{l+1} ≤ ell·α_l` and `α_l` is EXACTLY `‖g^(ell^l) − 1‖_F` — a quantity that grows with `l`
until it saturates at `2√2`, never a quantity that decreases. There is therefore no `l`-uniform
smallness that blocking supplies to `CurvedTower`'s per-level hypotheses. -/
theorem ubarTowerSU2_frobSupBond (ell : ℕ) (g : SU2) (l : ℕ) :
    frobSupBond (ubarTowerSU2 ell (constU g L) l) = frobNorm (((g ^ ell ^ l : SU2) : M2) - 1) := by
  rw [ubarTowerSU2_constU, frobSupBond_constU]

theorem ubarTowerSU2_step_le (ell : ℕ) (g : SU2) (l : ℕ) :
    frobSupBond (ubarTowerSU2 ell (constU g L) (l + 1))
      ≤ (ell : ℝ) * frobSupBond (ubarTowerSU2 ell (constU g L) l) := by
  rw [ubarTowerSU2_succ, ubarTowerSU2_constU]
  exact frobSupBond_ubarSU2_constU_le _ _ _

/-! ## §7b — `CurvedTower`'s `Ū`-SLOT, FILLED

`CurvedTower.lean`'s header states the gap this module was dispatched against, verbatim:

> **`Ū` at depth is a second, independent gap**: no blocking map `U ↦ Ū` exists in this tree, so
> §10's recursion is stated with `Ū` UNIVERSALLY QUANTIFIED at each level and is NOT instantiated.

`ubarSU2 s 2 U` has EXACTLY the type of `CurvedTower.fibre_bound_on_VCurved`'s `Ubar` parameter
(`PeriodicLinkConfiguration SU2 Λ`, same extent — the coarseness is carried by the stride `s`, not
by a smaller lattice). §7b instantiates that theorem at the map, discharging both of its background
hypotheses (`habar`, `hsup`) rather than assuming them.

What this does and does not settle: it fills the slot for the theorems that take `Ū` on `Λ`. The
theorems that take `Ū` on `coarseExtent Λ 2` need the re-indexed `ubarCoarse` below; that map is
supplied, but the `hsup` bound for it is proved only on constants, for the same reason as §4. -/

/-- **The Ū-slot filled, at a constant background.** `CurvedTower.fibre_bound_on_VCurved` with
`Ubar := ubarSU2 s 2 (constU g Λ)` — the ACTUAL CMP98 (15) blocking of a background, not a free
configuration — and with `abar := 2·frobSupBond (constU g Λ)` DERIVED from
`frobSupBond_ubarSU2_constU_le` rather than assumed.

The `2` is the finding: the regularity parameter the next level must be handed is twice the one
below, and `no_contraction_constant` proves no smaller factor is available.

**DEGENERATE POINT, DISCLOSED.** `CurvedTower.VCurved` is `True ∧ (A vanishes on the axial set)
∧ (lineCoarseRestrictCov Ū 2 A = 0)`, and `A = 0` satisfies all three for ANY `Ū`. At `A = 0` the
conclusion reads `γ·bondEnergy 0 ≤ curlEnergy 0`, i.e. `0 ≤ 0`, and carries no content. That
degeneracy is inherited from `CurvedTower.VCurved`'s own definition, not introduced here, and this
module does not prove `VCurved L (ubarSU2 s 2 (constU g L))` is inhabited by any `A ≠ 0` — that is
a separate question about the curved subspace and is NOT claimed. What §7b does establish is that
the `Ū` ARGUMENT is no longer free data: it is the actual blocking map, at a background proved
non-flat by `ubarSU2_constU_ne_trivialU`, with `abar` derived rather than assumed. -/
theorem fibre_bound_at_blockedBackground (hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1))
    (s : ℕ) (g : SU2) {ε : ℝ} (hε : 0 < ε) {A : Bond L → SuTwo}
    (hA : AdalyFormal.Balaban.CurvedTower.VCurved L (ubarSU2 s 2 (constU g L)) A) :
    AdalyFormal.Balaban.CovariantFibreTransfer.gammaCurved
        (2 * frobSupBond (constU g L)) ε
      * AdalyFormal.Balaban.RegularUPerturbation.bondEnergy A
      ≤ AdalyFormal.Balaban.FibreCoercivity.curlEnergy A := by
  refine AdalyFormal.Balaban.CurvedTower.fibre_bound_on_VCurved hdvd
    (ubarSU2 s 2 (constU g L)) ?_ ?_ hε hA
  · have := AdalyFormal.Balaban.RegularUPerturbation.frobSupBond_nonneg (constU g L)
    linarith
  · have h := frobSupBond_ubarSU2_constU_le s 2 (L := L) g
    norm_num at h
    linarith

/-- **NON-DEGENERACY of §7b.** The background fed to `fibre_bound_on_VCurved` above is genuinely
CURVED — it is not the flat configuration in disguise. At `g = gOf (24/25)` the blocked background
is `constU (g²)` with `‖g² − 1‖_F = 14√2/25 ≠ 0`, so `ubarSU2 s 2 (constU g Λ) ≠ trivialU Λ`.
Without this, §7b could be `vCurved_trivialU_eq_vLat` wearing a costume. -/
theorem ubarSU2_constU_ne_trivialU (s : ℕ) :
    ubarSU2 s 2 (constU (gOf (24/25)) L) ≠ trivialU L := by
  intro hEq
  have hfs : frobSupBond (ubarSU2 s 2 (constU (gOf (24/25)) L)) = frobSupBond (trivialU L) := by
    rw [hEq]
  rw [ubarSU2_constU, frobSupBond_constU] at hfs
  have htriv : frobSupBond (trivialU L) = 0 := by
    show frobSupBond (constU (1 : SU2) L) = 0
    rw [frobSupBond_constU, AdalyFormal.Balaban.SuTwoLogExp.coe_one, sub_self]
    exact AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero
  rw [htriv] at hfs
  have hsq : frobSq ((((gOf (24/25) : SU2) ^ 2 : SU2) : M2) - 1) = 392/625 := by
    rw [frobSq_gOf_sq (24/25) (by norm_num) (by norm_num)]; norm_num
  have : frobNorm ((((gOf (24/25) : SU2) ^ 2 : SU2) : M2) - 1) ^ 2 = 392/625 := by
    rw [AdalyFormal.Balaban.RMapLipschitz.frobNorm_sq, hsq]
  rw [hfs] at this
  norm_num at this

/-- **`Ū` RE-INDEXED ONTO THE COARSE EXTENT.** `CurvedTower`'s deeper theorems take
`Ubar : PeriodicLinkConfiguration SU2 (coarseExtent Λ 2)`. This is `ubarSU2 1 ell` read at the
coarse index, using `U1AnchorCoarse.toFine` (LAW-19: the embedding already exists, and is not
rebuilt here). -/
noncomputable def ubarCoarse (ell : ℕ) (V : PeriodicLinkConfiguration SU2 L) :
    PeriodicLinkConfiguration SU2 (AdalyFormal.Balaban.U1AnchorCoarse.coarseExtent L ell) :=
  fun c => ubarSU2 1 ell V (AdalyFormal.Balaban.U1AnchorCoarse.toFine L ell c.1, c.2)

/-- The exact identity survives the re-indexing. -/
theorem ubarCoarse_constU (ell : ℕ) (g : SU2) :
    ubarCoarse ell (constU g L)
      = constU (g ^ ell) (AdalyFormal.Balaban.U1AnchorCoarse.coarseExtent L ell) := by
  funext c
  show ubarSU2 1 ell (constU g L) _ = _
  rw [ubarSU2_constU]
  rfl

/-- The `hsup` bound for the coarse-extent slot, on constants. -/
theorem frobSupBond_ubarCoarse_constU_le (ell : ℕ) (g : SU2) :
    frobSupBond (ubarCoarse ell (constU g L))
      ≤ (ell : ℝ) * frobSupBond (constU g L) := by
  rw [ubarCoarse_constU, frobSupBond_constU, frobSupBond_constU]
  exact frobNorm_pow_sub_one_le g ell

/-! ### §7a — CONTROLS: the conditional estimate is not vacuous, and `hfit` has teeth -/

/-- **NONVACUITY of `ubarSU2_sub_one_le_lattice`'s two remaining hypotheses.**

A conditional theorem whose hypotheses are undischargeable proves nothing and passes every gate
(the "dangerous residuals carry no sorry" class). Both remaining hypotheses are SATISFIED at every
constant configuration, for every `s`, `ell`, `g`, `c`: the loop variables are all `1` (§3), so the
loop bound holds with room to spare and the block exponent is `0`, where `su2Log (su2Exp 0) =
su2Log 1 = 0` discharges the branch condition on the nose. So the estimate has instances. -/
theorem estimate_hypotheses_hold_at_constU (s ell : ℕ) (g : SU2) (c : PeriodicLatticeEdge L)
    (Nplaq beta : ℝ) (hN : 0 ≤ Nplaq * beta) :
    (∀ x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell,
        frobNorm (((loopVar s ell (constU g L) c x : SU2) : M2) - 1) ≤ Nplaq * beta)
      ∧ su2Log (su2Exp (blockExponent
          (AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell)
          (fun _ => ((ell : ℝ) ^ 3)⁻¹) (fun x => loopVar s ell (constU g L) c x)))
        = blockExponent (AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell)
          (fun _ => ((ell : ℝ) ^ 3)⁻¹) (fun x => loopVar s ell (constU g L) c x) := by
  have hexp : blockExponent (AdalyFormal.Balaban.QjComposite.stepBlockOf c.1 s ell)
      (fun _ => ((ell : ℝ) ^ 3)⁻¹) (fun x => loopVar s ell (constU g L) c x) = (0 : M2) := by
    unfold blockExponent
    refine Finset.sum_eq_zero (fun x _ => ?_)
    simp only [loopVar_constU, AdalyFormal.Balaban.SuTwoLogExp.su2Log_one, smul_zero]
  refine ⟨fun x _ => ?_, ?_⟩
  · rw [loopVar_constU, AdalyFormal.Balaban.SuTwoLogExp.coe_one, sub_self,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
    exact hN
  · rw [hexp, AdalyFormal.Balaban.SuTwoLogExp.su2Exp_zero,
      AdalyFormal.Balaban.SuTwoLogExp.su2Log_one]

/-- **MUST-FIRE CONTROL on `weight_sum_eq_one`'s `hfit`.** The hypothesis is not decoration. At
the tree's own recorded truncating instance (`QjComposite.card_stepBlockOf_truncates`: the block
`stepBlockOf witnessY 2 3` has `8` sites where `3³ = 27` are expected, because the lattice does not
fit the block), the `ell^{-3}` weights sum to `8/27`, NOT `1` — so `blockedLink_sub_one_le`'s
normalisation genuinely fails there and `weight_sum_eq_one` would be false without `hfit`. -/
theorem weight_sum_ne_one_at_truncation :
    ∑ _x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf
      AdalyFormal.Balaban.AdmissibleSubspace.witnessY 2 3, ((3 : ℝ) ^ 3)⁻¹ ≠ 1 := by
  rw [Finset.sum_const, AdalyFormal.Balaban.QjComposite.card_stepBlockOf_truncates, nsmul_eq_mul]
  norm_num

/-! ## §8 — EVIDENCE OF RESISTANCE: what was attempted and where it broke

Two hypotheses of `ubarSU2_sub_one_le_lattice` were NOT discharged. Both were attempted; neither
is a label.

**(a) `hloop` — the closed-loop curvature bound. Attempted, broke at the SPANNING SURFACE.**
`BlockingLinkEstimate` already supplies both halves of what is needed EXCEPT one object:
`frobNorm_conjProd_sub_one_le` gives `‖(∏ q₁ q₂ q₁⁻¹) − 1‖ ≤ |ps|·beta` for a list of
(transport, plaquette) pairs, and §6 there COUNTS the plaquettes of the surface
(`plaqCount 3 2 = 7`, `surfCount`, `gammaPathLength`) directly from CMP98 p.19's definition of
`Γ_{c,x}`. `loop_bound_of_surface` assembles them. What none of that provides, and what this lane
could not construct, is the FUNCTION producing, for each `x ∈ stepBlockOf c.1 s ell`, an explicit
`ps : List (SU2 × SU2)` with
`loopVar s ell V c x = (ps.map (fun q => q.1 * q.2 * q.1⁻¹)).prod` and `ps.length = surfCount …`.
That is a lattice-homotopy construction: it must exhibit the surface swept when the staircase
`Γ_{c_-,x}` is translated through `c` (the cylinder) together with the reversal surface between the
two extreme monotone staircases, AS AN ORDERED WORD, and prove the word telescopes. The count is
known; the word is not. The concrete break: `coarseGammaPath` is a `List (Fin 3)` built by
`++` of three `coarseStraightSegment`s, and reassociating a product over that concatenation into
conjugated plaquettes requires an induction on TWO segments simultaneously with the base point
moving in both — the induction hypothesis needed is not the statement being proved, and no
strengthening tried here closed under the `++` split. This is a genuine construction, not a
missing lemma name.

**(b) `hbranch` — the principal branch. Attempted, and it is PROVABLY NOT REMOVABLE.**
`SuTwoLogExpTorus.exp_log_fails_at_center` and `log_center_forced` already prove that for ANY
`P : LogExpAd SU(2) M₂(ℂ)` with the genuine adjoint, `log` must send the centre element to `0`,
so `exp (log g) = g` FAILS there. So `hbranch` cannot be discharged in general — it is a domain
condition, exactly `BlockedGaugeGuard`'s `[BLOCKED-BRANCH-DOMAIN]`. What CAN be said, and is said
by §3, is that the branch point is never reached on constant configurations (every loop variable
is `1`), which is why §3–§7 are unconditional. Notably the sharpest witness of §6
(`diagSU2 (π/ell)`) has `Ū` EQUAL to the centre element `−1`: the configuration that maximises the
expansion is exactly the one at which the NEXT blocking step's logarithm is singular. That is a
fact about the pair, recorded here, not a claim about its significance.

**(c) General-`ell` SHARPNESS. Attempted, closed only to `2·ell/π`.**
§6 proves no contraction constant below `2·ell/π` at every `ell`, and `2` exactly at `ell = 2`.
The gap between `2·ell/π ≈ 0.6366·ell` and the conjectured sharp `ell` is one analytic step:
`‖g^n − 1‖_F/‖g − 1‖_F = sin(nφ/2)/sin(φ/2) → n` as `φ → 0`. The `ell = 2` case closes by the
double-angle formula alone (`Real.cos_two_mul`), which is why it is sharp here; general `n`
needs `sin(nθ) = sin θ · U_{n−1}(cos θ)` (Mathlib's `Polynomial.Chebyshev.U`) plus continuity of
`U_{n−1}` at `1`, where `U_{n−1}(1) = n`. That route was not carried out. The bound actually
proved is enough for every use made of it below: it is unbounded in `ell`, so no `ell`-uniform
contraction constant exists either.
-/

/-! ## §9 — axiom audit -/

#print axioms ubarSU2
#print axioms ubarSU2_gauge
#print axioms coarsePathHolonomy_constU
#print axioms coarseBondVar_constU
#print axioms gammaVarStrided_constU
#print axioms loopVar_constU
#print axioms ubarSU2_constU
#print axioms ubarSU2_trivialU
#print axioms ubarTowerSU2_constU
#print axioms frobSupBond_constU
#print axioms frobNorm_pow_sub_one_le
#print axioms frobSupBond_ubarSU2_constU_le
#print axioms frobNorm_sub_one_le_two_sqrt_two
#print axioms qsmul_eq_csmul
#print axioms ubarSU2_eq_blockedLink
#print axioms frobNorm_coarsePathHolonomy_sub_one_le
#print axioms frobNorm_coarseBondVar_sub_one_le
#print axioms weight_sum_eq_one
#print axioms ubarSU2_sub_one_le
#print axioms ubarSU2_sub_one_le_lattice
#print axioms zc_normSq
#print axioms diagSU2_pow
#print axioms frobSq_su2Of_diag_sub_one
#print axioms frobSq_diagSU2_pow
#print axioms frobSq_gOf
#print axioms frobSq_gOf_sq
#print axioms blocking_ratio_two
#print axioms frobSupBond_constU_gOf_pos
#print axioms blocking_expands_at_24_25
#print axioms expansion_factor_bounds
#print axioms no_contraction_constant
#print axioms no_contraction_at_any_ell
#print axioms threshold_not_preserved
#print axioms ubarTowerSU2_frobSupBond
#print axioms ubarTowerSU2_step_le
#print axioms estimate_hypotheses_hold_at_constU
#print axioms weight_sum_ne_one_at_truncation
#print axioms fibre_bound_at_blockedBackground
#print axioms ubarSU2_constU_ne_trivialU
#print axioms ubarCoarse
#print axioms ubarCoarse_constU
#print axioms frobSupBond_ubarCoarse_constU_le
-- remaining definitions and helper lemmas, so that coverage is TOTAL (57/57)
#print axioms ubarSU2_apply
#print axioms ubarTowerSU2
#print axioms ubarTowerSU2_zero
#print axioms ubarTowerSU2_succ
#print axioms zc
#print axioms zc_re
#print axioms zc_im
#print axioms zc_mul_star
#print axioms zc_add
#print axioms zc_zero
#print axioms diagSU2
#print axioms coe_diagSU2
#print axioms su2Of_mul_su2Of
#print axioms frobNorm_diagSU2_pow
#print axioms gOf

end AdalyFormal.Balaban.BlockedBackground
