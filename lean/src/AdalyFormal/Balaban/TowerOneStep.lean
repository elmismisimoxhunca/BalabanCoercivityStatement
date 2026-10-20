/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.GammaRecursion
import AdalyFormal.Balaban.BridgeInverseKernel
import AdalyFormal.Balaban.DeltaPrimeBound
import AdalyFormal.Balaban.ComposedCoercivity
import AdalyFormal.Balaban.ExtentUniformCoercivity

set_option autoImplicit false
-- No `maxHeartbeats` bump. The convicted version carried `set_option maxHeartbeats 1000000`;
-- `compute/tower_repair/strip_maxheartbeats.log` measures that the file (including everything added
-- by the item-B repair) compiles at the DEFAULT budget with 0 errors, so the bump was decorative and
-- is removed rather than inherited.

/-!
# `TowerOneStep` — the ONE-STEP RG MAP AS AN OPERATOR, and the ladder it generates

Lane record: `compute/tower_onestep/PROGRESS.md`.

## §0 — THE HOLE THIS FILE FILLS, STATED FIRST

`GammaRecursion.chain_gamma` transports the coercivity constant along a chain of operators, but its
hypothesis is

```
hstep : ∀ k, StepsWith δ q (Δ k) (Δ (k+1))
```

and **nothing in this tree makes that hypothesis a theorem**, because nothing defines `Δ (k+1)`
*from* `Δ k`. Measured before building (`compute/tower_onestep/PROGRESS.md` §0):

* `DeltaKSuTwoCarrier.deltaKTowerCLM ell k levels U` is `k`-indexed, but its `k` is the CLOSED-FORM
  block side `ell^k` (`towerNorm_pow`) — a one-shot Schur complement against the level-`k`
  averaging. `deltaKTowerCLM (k+1)` is not built from `deltaKTowerCLM k`.
* `RGLadderCoarse.rgDelta n = deltaOf (blockRepBond n)` is likewise one-shot in `n`.
* `CoercivityRegular.regularDelta` is `k`-inert (`regularDelta_k_constant`).
* `GammaRecursion.coarse156` and `BridgeInverse.sOpK` — the two halves of the step — had **no
  consumer anywhere** outside their defining files.

So the campaign's position "no `k`-varying ladder of operators exists" is exactly: *the RG step has
never been written down as a map on operators.* This file writes it down.

## §0b — ⚠ THE CONVICTION THIS FILE WAS REBUILT UNDER, STATED BEFORE ANY CLAIM

`compute/tower_prosecution/VERDICT.md` (PROS-TOWERONESTEP-01) **CONVICTED** the previous version of
this module on three counts. Repair record: `compute/tower_repair/PROGRESS.md`.

**Item B — the map's fidelity (CONVICTED).** The old §1 quoted (3.128) with `Δ_π` and then, in the
next sentence, silently substituted `Δ_k`; `Rung.M` was built from the raw incoming `Δ`. Two
independent load-bearing sources in this same tree say that substitution is a real, costly defect:
`corpus/pages/CMP99b_p421.md` (adjudicated) records *"Δ_π / Δ'_π … distinguished from plain Δ"*,
and `RecursiveBridge.lean:1158-1161` lists `Δ_π ≠ Δ` as its own caught defect #1 with the price:
*"the transported constant degrades from `γ/q²` to `(γ−δ)/q²`, with `δ` an undischarged bound that
CMP99b p.419 explicitly defers."* The old `δ`-shaped channel (`Rung.StepsHet`) did not pay that
price — it was pure monotonicity and never touched a correction operator.

**THE REPAIR (this version).** `Δ_π = Δ − Δ′_π` is now an object in the file (`piOp`, CMP99b
(3.120), the CLM twin of `RecursiveBridge.piExtendedMap`), the corrected rung
`RungPi H K Δ Δ′_π := Rung H K (piOp Δ Δ′_π)` feeds `Δ_π` — not `Δ` — into (3.128)'s `fineCLM`, and
the tower law it carries is the **TAXED** one, `Rung.nextPi_coercive_gf : (γ − δ)/q²`, with `δ`
bound to `Δ′_π` by the **two-sided** `|⟨x,Δ′_πx⟩| ≤ δ‖x‖²` that `RecursiveBridge.piExtended_coercive_at`
and `DeltaPrimeBound.abs_inner_le_of_piForm` both use. The untaxed `γ/q²` survives ONLY as the
`Δ′_π = 0` case, and that is proved, not asserted (`nextPi_coercive_gf_at_zero`,
`scalarRungPi_next_at_zero`).

**Item C — "chain_gamma's `hstep` DISCHARGED" (OVERCLAIMED).** True fact: `chain_gamma`'s carrier is
a single fixed `H`, so it cannot be applied to a dimension-dropping ladder at all. It is now APPLIED
FOR REAL, on constant-carrier ladders, in `Ladder.coercive_chain_gamma`, whose `hstep` comes from
`Ladder.stepsWith_const` — a theorem, not a hypothesis. For the heterogeneous ladder,
`Ladder.coercive` remains a SEPARATE induction and is described as such below; the old blanket
"discharged" wording is struck.

**Item D — `latticeRung`'s "no hypothesis beyond `hDP`" (CONVICTED).** The signature carries NINE
Prop-valued hypotheses. They are all enumerated at §10 and in the definition's own docstring, and
the `trivialU` restriction on `Q` is now stated in the summary, not only in-line.

## §1 — THE MAP, READ OFF THE SOURCE

Four displays of CMP99b, in the readings this tree has already pinned (re-quoted here with their
locators; none is re-adjudicated by this module, and none is newly transcribed):

* **(3.128), p.421, `verification_status: adjudicated`** (quoted verbatim in
  `RecursiveBridge.lean`'s header):
  `⟨A, G₁⁻¹A⟩ = ⟨A, Δ_π A⟩ − 2⟨H C_π^{(2)}(A), J⟩ + ‖RD*A‖² + a‖QA‖²`.
  So the fine operator at level `k` is `M_k = Δ_π,k + P_k + Q_k* a Q_k` — **`Δ_π`, not `Δ_k`** —
  which is exactly `BridgeInverse.fineCLM Δ_π P Q Qstar a` (reused, LAW-19; that definition's own
  docstring, `BridgeInverseCore.lean:218`, already reads *"`M = Δ_π + P + Q*aQ`"*, so the kit was
  right and the old caller was wrong). `P` carries `‖RD*A‖²`, and the `J`-term is the `src` channel,
  kept out of the operator as `RecursiveBridge` does.
  ~~So the fine operator at level `k` is `M_k = Δ_k + P_k + Q_k* a Q_k`.~~ **STRUCK — item B.**
* **(3.120), p.421**: `Δ_π = Δ − Δ′_π`. `Δ′_π` is `J`-paired and INDEFINITE, so the only admissible
  bound on it is two-sided, `|⟨x,Δ′_πx⟩| ≤ δ‖x‖²`; a one-sided `0 ≤ ⟨x,Δ′_πx⟩` would be the
  `P`-treatment and is not justified (`RecursiveBridge.lean:1198-1200`). CMP99b p.419 **defers**
  the bound itself (*"Later we will write bounds for this form"*); this tree's own measured value
  is `DeltaPrimeBound.deltaPiConst Jsup κ = Jsup·κ·(28+48κ)`.
* **(3.156), p.428, `verification_status: adjudicated`**:
  `⟨B, (QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃^{(2)}(B), J⟩ = ⟨B, Δ_k B⟩`.
  At `J = 0` this says the NEXT level's operator is `(Q G₁ Q*)⁻¹ − a·I`.
* **(3.16), p.393** — ⚠ `verification_status: **single-read**`, not adjudicated: `a` is the same
  constant at every scale (`ConstantA.usedAt_const`, re-derived there); so no `a_k` sequence is
  needed. What this module actually uses from (3.16) is only that `a` carries NO `j` index — it
  sits outside the `∑_{j=0}^{k}` in the transcribed display — and **§10e's weight ruling does not
  rest on it**: that ruling is forced by (3.128)+(3.129)+(3.155), all on ADJUDICATED pages.

Put together, **the one-step RG map on operators is**

```
      Δ_{k+1}  =  ( Q_k · ((Δ_k − Δ′_π,k) + P_k + Q_k* a Q_k)⁻¹ · Q_k* )⁻¹  −  a · I
```

with `Δ_k` living on the level-`k` carrier and `Δ_{k+1}` on the level-`(k+1)` carrier. That is
`Rung.next` applied to a `RungPi`, i.e. to a rung whose index operator is `piOp Δ_k Δ′_π,k`.
Everything on the right-hand side is CONSTRUCTED from `BridgeInverse`'s kit (`gOneK`, `tOpK`,
`sOpK` — genuine two-sided inverses in finite dimension), never assumed.

~~`Δ_{k+1} = ( Q_k · (Δ_k + P_k + Q_k* a Q_k)⁻¹ · Q_k* )⁻¹ − a·I`~~ — **STRUCK, item B**: that is
the map with the (3.120) correction dropped. It is retained in the file only as the `Δ′_π = 0`
special case, where it is correct and where the constant `γ/q²` is honest.

**Structural corroboration, not a premise — AND ITS SOURCE STATUS, STATED EXACTLY.** The `Q`-side of
the same tower is already in the tree and has the same shape: CMP99b p.393's
`Q'_j(U) = Q'(Ū^{j-1})·…·Q'(Ū)Q'(U)` is built as `QjComposite.Qcomposite` with `Qcomposite_succ`,
over the background tower `UbarTowerCov.UbarTower`.

⚠ **`corpus/pages/CMP99b_p393.md` is `verification_status: single-read`, NOT adjudicated**, and its
own ANNOTATION records that the `(3.19)` line quoted above is *"transcribed and indexed here but no
interpretive/adjudicative note is recorded about it — a concurrent lane is tracing the (3.19)/(3.55)
chain into CMP98 and adjudicating `Γ^{(j)}`."* Per the LAW-11 correction, a single-read page is a
strong lead, not citable ground truth. **This sentence is corroboration only; nothing below is
derived from it.**

⚠ **AND THERE IS A KNOWN OCR TRAP ON EXACTLY THIS KIND OF OBJECT.** The CMP98 adjudication
(`compute/cmp98_adjudication/`, `corpus/EQUATION_INDEX.md` rows for pp.26/29/30/50) confirms that
equation-mode OCR SYSTEMATICALLY DROPS the superscript `j` and the prime on `Ũ′^j` — at (67), (68),
(72) and (208) the printed object is `Ũ′^j Ū₀^j` under one overline while the machine draft reads a
bare `Ũ′`; the "Let us denote" sentence's `(j)` was misread as `(i)`; and (214)'s exponent `L^j·η`
was garbled. `Ū^{j-1}` above is an overline-plus-superscript locus of precisely that type, on a
page that has NOT had a second read. It is flagged here rather than relied on.

The `j`-step contour `Γ^{(j)}` behind that composite is defined in CMP98 by an UNNUMBERED
telescoping-product display beginning on printed p.29 between (76) and (77) — *"Let us denote
`U₀(Γ^{(j)}_{x_j,x}) = Ū₀^{j-1}(Γ_{x_j,x_{j-1}})·…·Ū₀(Γ_{x_2,x_1})U₀(Γ_{x_1,x})`"* — and resolving
on p.30 at (77) into the compact symbol `(R_{0,x_{j+1}}U_1)(Γ^{(j+1)}_{x_{j+1},x})`, whose direct
linearized use is p.50 (212). Those four pages (`CMP98_p26`, `_p29`, `_p30`, `_p50`) ARE
`verification_status: adjudicated`; the one-step contour sits at CMP98 p.19 just after (14) (p.19
adjudicated as a page, though its `EQUATION_INDEX` rows carry no notes).
**CMP99b's own onward pointer "(52),(53) in [5]" is a dead pointer** — CMP98's printed (52)/(53)
are, confirmed on the adjudicated p.26, a single-plaquette deviation hypothesis and an inductive
plaquette bound, not a contour definition — so it is not used here.

**NON-DEPENDENCE, STATED AS A FACT ABOUT THE QUANTIFIERS, NOT AS REASSURANCE.** `Q` is a FIELD of
`Rung`, constrained by exactly four hypotheses — `hadj`, `hq`, `hQ`, `hQstarInj` — none of which
mentions a contour, a background tower, or `Ū`. Every theorem in this file is therefore universally
quantified over `Q`, and §6–§8 exhibit two structurally unrelated instances carrying the same law
(`scalarRung`'s `θ·id` and `blockRung`'s printed block average). **Whether the source's `Γ^{(j)}`
convention matches `QjComposite`'s is left deliberately un-adjudicated by the CMP98 lane
(`compute/cmp98_adjudication/NOTES.md`, observation-only); this module does not need that
identification and does not assert it.** A module that DID need it — one instantiating `Q` at a
`j`-step composite rather than at `qCLM (trivialU L) ell` — would owe that adjudication first.

## §2 — WHAT IS PROVED

* `Rung` — one RG step's data, **tied to the incoming operator `Δ`**: the inverse fields are not
  free, they are the constructed inverses of `fineCLM Δ P Q Qstar a`.
* `Rung.next` — the map above, as a `ContinuousLinearMap` on the coarse carrier.
* `Rung.next_coercive_gf` — **THE ONE-STEP TOWER LAW**: `γ`-coercivity of the GAUGE-FIXED operator
  `Δ_k + P_k` on the fine carrier gives `(γ/q²)`-coercivity of `Δ_{k+1}` on the coarse carrier.
  Proved by feeding `RecursiveBridge.bridge_coercive_prim`; nothing is re-derived.
  `Rung.next_coercive` is the corollary from the stronger `Δ`-alone hypothesis — **which this tree
  REFUTES at `witnessU`** (`BridgeInverseControls.h310_unrestricted_impossible_at_witnessU`), which
  is why every lattice-facing statement below uses the gauge-fixed form.
* **`piOp Δ Dpi = Δ − Dpi`** — (3.120), as a `ContinuousLinearMap`. `piOp_eq_piExtendedMap` proves
  it is pointwise the same map as `RecursiveBridge.piExtendedMap` on the lattice carrier, so the
  corrected rung consumes the SAME object the honest bridge chain uses.
* **`Rung.nextPi_coercive_gf` — THE TAXED ONE-STEP TOWER LAW.** From (i) `γ`-coercivity of the
  gauge-fixed UNCORRECTED operator `Δ_k + P_k` (the (3.10)-level statement, the only one the
  lattice can supply) and (ii) a two-sided `|⟨x,Δ′_πx⟩| ≤ δ‖x‖²`, the level-`(k+1)` operator is
  `(γ−δ)/q²`-coercive. `δ` is not free: it is bounded BELOW by the actual size of `Δ′_π`
  (`pi_bound_forces_delta` shows a `δ` smaller than `Δ′_π`'s diagonal is unavailable), and the
  operator `next` genuinely moves with `Δ′_π`.
* `Rung.nextPi_coercive_gf_at_zero` — at `Δ′_π = 0` the tax is exactly zero and the constant is
  `γ/q²`. **Flat = untaxed, curved = taxed, and both are theorems.**
* `Rung.gf_of_defect` — a Poincaré-with-defect bound `γ₀‖x‖² ≤ ⟨x,Δx⟩+⟨x,Px⟩+C‖Qx‖²` yields the
  gauge-fixed hypothesis at `γ = γ₀ − Cq²`. ⚠ This `Cq²` is a **second, independent** subtraction —
  it is the fibre-to-whole-space defect, NOT the (3.120) correction. Do not confuse it with the
  `δ` of `(γ−δ)/q²`. ~~"This is where the campaign's `δ` in `(γ−δ)/q²` comes from: `δ = Cq²`."~~
  **STRUCK** — that sentence conflated two different subtractions; the campaign's `δ` in the
  transported constant is (3.120)'s `deltaPiConst`, and `Cq²` is a separate loss on the input side.
* `Rung.StepsPi` / `Rung.stepsPi` (and the `_gf` twin) — the step relation **carrying the correction
  operator**: the `δ` slot is usable only together with a two-sided bound on a named `Δ′_π`.
* ~~`Rung.stepsHet` / `Rung.stepsHetGF` — the same in the shape `GammaRecursion.StepsWith` uses,
  with the `δ` channel.~~ **STRUCK, item B**: those two are pure monotonicity. They are retained,
  relabelled, with `stepsHet_delta_is_free` proving the `δ` in them is unconstrained by any
  operator, and they are used by nothing.
* `Ladder` — a family `op : ∀ k, E k →L[ℝ] E k`, a family of (3.120) corrections
  `dpi : ∀ k, E k →L[ℝ] E k`, a rung at `piOp (op k) (dpi k)` for every `k`, and the LAW
  `op (k+1) = (rung k).next`. This is the object whose absence was the campaign's stated position.
* `Ladder.coercive`, `Ladder.coercive_gf`, `Ladder.coercive_succ_gf` —
  `∀ k, CoerciveOn (op k) (gammaSeq γ₀ δ q k)`, i.e. the taxed recursion
  `γ_{k+1} = (γ_k − δ)/q²` iterated, with the per-level two-sided bound on `dpi k` as the only new
  input. This is an INDEPENDENT induction, not an application of `chain_gamma` (see the next item).
  The `_gf` versions take only the gauge-fixed input at level `0`; levels `≥ 1` need no separate
  gauge-fixed hypothesis, because the previous step's conclusion is whole-space coercivity of
  `op (k+1)` and the next rung's `hPpos` upgrades it.
* `Ladder.stepsWith_const` / `Ladder.coercive_chain_gamma` — **`GammaRecursion.chain_gamma`
  APPLIED**, on a ladder whose carriers are all one fixed `H`, with its `hstep` hypothesis supplied
  by a theorem of this file. `chain_gamma`'s carrier is a single fixed type, so it cannot be
  applied to a dimension-dropping ladder at all; that is a fact about its signature, and it is why
  the heterogeneous statement above is a separate induction.
* `Ladder.coercive_uniform` — **the `k`-UNIFORM tower**: if `0 < q < 1` and `δ ≤ γ₀(1−q²)`, then
  every level is `γ₀`-coercive, with no decay. The floor is `ComposedCoercivity.gammaSeq_floor_pinned`
  (imported, not re-proved), and the criterion is the one `criterion_closes_at_gammaFibre`
  discharges at the tree's own numbers.
* `scalarLadder` — an inhabitant of `Ladder` of unbounded depth on nontrivial carriers whose
  operators are pairwise distinct, with `a > 0` allowed, exhibiting the `−a·I` cancellation
  (`scalarRung_next_independent_of_a`).
* `blockRung` — a rung whose carriers genuinely DROP DIMENSION (`ℝ² → ℝ`) with `Q` the CMP95
  (1.13) / CMP99b p.393 block average `x ↦ Σ_{x∈B(y)} L^{-d} x` at `ell = 2, d = 1`, its `q`
  computed, and `Δ_1` computed exactly; `blockRung_bound_sharp` shows the tower law is attained
  with equality there, so the step is not lossy.
* `twoStep_tie` / `twoStep_coercive` / `twoStep_sharp` — the two-step composite `ℝ² → ℝ → ℝ`, with
  the SECOND rung sitting at the operator the FIRST rung produced (`twoStep_tie` is that
  identification), demonstrating that the iteration composes rather than merely typechecking once.
* `taxedScalarLadder` — a ladder with a **NON-ZERO correction operator at every level**, whose
  level-`k` operator is multiplication by `gammaSeq γ₀ δ q k` on the nose
  (`taxedScalarLadder_op_eq_gammaSeq`): the ladder's own operators ARE the taxed recursion. At
  `δ > 0` its constants are strictly below the untaxed ones (`taxed_lt_untaxed`), and the taxed
  constant is ATTAINED (`taxedScalarLadder_sharp`), so the tax is exact, not slack.
* `campaignTaxedLadder` — the same at the campaign's own `(γ₀, δ, q) = (gammaFibre,
  deltaPiConst (24·10⁻¹¹) √768, 1/2)`, with uniformity supplied by
  `ComposedCoercivity.criterion_closes_at_gammaFibre`. ⚠ Its CARRIER is `ℝ`, not the su(2) bond
  space: it witnesses that those three numbers support a `k`-uniform tower, and it does **not**
  build the lattice tower (§10b).
* `latticeRung` / `latticeRung_tower_law` — the FIRST rung BUILT at the tree's own su(2) lattice
  data (`qCLM`, `qstarCLM`, `qCLM_hadj`, `qCLM_le`, `qCLM_norm_pos`,
  `qCLM_surjective_trivialU`). ⚠ **NINE Prop-valued hypotheses**, listed at §10; `Q` is fixed at
  `trivialU` because surjectivity of `Q` is proved only there.
  ~~"adding no hypothesis beyond the `hDP` that `BridgeInverseControls` already carries as the
  bridge's one surviving hypothesis."~~ **STRUCK — item D, false as a statement about the
  argument list.**
* `latticeRungPi` / `latticeRungPi_tower_law` / `latticeRungPi_tower_law_at_deltaPiConst` — the
  same first rung on the **CORRECTED** operator, delivering `(γ−δ)/‖Q‖²`, and then with `δ`
  instantiated at `DeltaPrimeBound.deltaPiConst Jsup κ` through
  `DeltaPrimeBound.abs_inner_le_of_piForm`. ELEVEN hypotheses, listed at §10.
* ⚠ **`Rung.next_coercive_gf_on_range` / `nextPi_coercive_gf_on_range` (§4b′) — READ §10e BEFORE
  USING THE WHOLE-SPACE FORMS.** The whole-space gauge-fixed hypothesis is THIS CAMPAIGN'S
  strengthening, not CMP99b's, and at the tree's own lattice operators it is **REFUTED**
  (`ExtentUniformCoercivity.un_augmented_coercivity_false`), which makes `latticeRungAtDeltaK` and
  `latticeRungPiAtDeltaK` **VACUOUS** at `trivialU` — proved and disclosed at §10e as
  `latticeRungAtDeltaK_hDP_refuted_at_trivialU`. The `_on_range` forms carry the same conclusions
  from the hypothesis `RecursiveBridge.bridge_bare` actually uses (points `G(Q*C)` only), which the
  refutation does not touch. §10e also adjudicates, from (3.155)+(3.129)+(3.128), that (3.128)'s
  `a` and (3.156)'s subtracted `a` **must be the same number**, and computes
  (`Rung.shifted_subtraction_costs`, `Rung.shifted_route_yields_nothing`) that the shifted-weight
  alternative transports nothing about the source's operator.
* `defect_from_kernel` — in finite dimension the kernel condition gives a defect bound, with the
  constant EXISTENTIAL and carrying no uniformity in the lattice extent (§10c).

## §3 — WHAT IS **NOT** PROVED (binder audit; the known failure mode)

The registry records `TowerUniformSuTwo` being inhabited by a content-free term, so every binder
here is audited in §9 rather than trusted.

1. **`Ladder` is a Π/equation structure, not an `∃`.** There is no existential over free data for a
   prover to instantiate cheaply: the rung's `G` and `S` are *definitions* applied to the incoming
   `Δ`, and `law` pins `op (k+1)` on the nose.
2. **But `Ladder` IS inhabited vacuously on trivial carriers** — if every `E k` is a zero space
   every field holds. §9 therefore proves the witnesses have `Nontrivial (E k)` and pairwise
   distinct `op k`; without that, the structure alone would say nothing. This is stated up front,
   not buried.
3. **`q` is an upper bound, so it is free upward** (`GammaRecursion.hQ_mono`). A large `q` makes the
   conclusion weak, never false. The witnesses therefore compute `q` and show it attained.
4. **No FULL su(2) lattice ladder is claimed here.** §10 builds the FIRST rung at the lattice; §10b
   records exactly which object is missing for the second, and §10c records where the tree's own
   fibre-only coercivity sits relative to the hypothesis a rung needs — including that the
   finite-dimensional repair produces a NON-EXPLICIT constant carrying no uniformity in the
   lattice extent.
5. **`Rung.next_coercive` (the `Δ`-alone form) has a hypothesis this tree REFUTES on the lattice.**
   `BridgeInverseControls.h310_unrestricted_impossible_at_witnessU` proves whole-space coercivity of
   the bare (3.10) operator unsatisfiable at `witnessU`. That theorem is kept because the abstract
   witnesses of §6–§8 do satisfy it, but it is never used on the lattice side —
   `next_coercive_gf` is.
6. **`Ladder.dpi` IS FREE DATA, and that is where a consumer can still go wrong.** Nothing in this
   file forces `dpi k` to be CMP99b's `Δ′_π` at level `k`; a consumer may supply `dpi k = 0` and
   recover the untaxed law. The file therefore proves the *conditional* statement and nothing more:
   *given* a family of correction operators with a uniform two-sided bound `δ`, the constants
   iterate as `gammaSeq γ₀ δ q`. Whether the supplied family IS (3.120)'s is the consumer's
   obligation; `latticeRungPi_tower_law_at_deltaPiConst` discharges it at the lattice by demanding
   `hT`, the identity that pins the operator's diagonal to `deltaPrimePiForm`.
7. **`δ` is an UPPER bound on the correction, so it is free upward, exactly like `q`.** A large `δ`
   makes the conclusion weak, never false, and at `δ ≥ γ` the hypothesis `0 < γ − δ` empties the
   statement. It is NOT free downward: `pi_bound_forces_delta` exhibits, on a nontrivial carrier,
   a correction operator for which no `δ` below its diagonal satisfies the two-sided bound.
-/

namespace AdalyFormal.Balaban.TowerOneStep

open scoped InnerProductSpace
open AdalyFormal.Balaban.BridgeInverse
open AdalyFormal.Balaban.RecursiveBridge
open AdalyFormal.Balaban.GammaRecursion

/-! ## §4 — ONE RUNG -/

section OneRung

/-- **CMP99b (3.120), `Δ_π = Δ − Δ′_π`, as a `ContinuousLinearMap`.**

This is the CLM twin of `RecursiveBridge.piExtendedMap` (`RecursiveBridge.lean:1190-1196`,
`piExtendedMap Delta DeltaPrimePi := fun x => Delta x - DeltaPrimePi x`), which is defined only on
`BondFnL2 L`; `piOp_eq_piExtendedMap` in §10 proves the two agree pointwise there, so the corrected
rung consumes the same object the honest bridge chain does.

**Why this exists at all:** `BridgeInverse.fineCLM`'s first argument is (3.128)'s `Δ_π`
(`BridgeInverseCore.lean:218`, its own docstring). The convicted version of this file passed the
raw `Δ`. -/
def piOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Δ Dpi : H →L[ℝ] H) : H →L[ℝ] H := Δ - Dpi

@[simp] theorem piOp_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Δ Dpi : H →L[ℝ] H) (x : H) : piOp Δ Dpi x = Δ x - Dpi x := rfl

/-- At a vanishing correction the π-extended operator IS the plain one. -/
theorem piOp_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Δ : H →L[ℝ] H) : piOp Δ 0 = Δ := sub_zero Δ

/-- `Δ_π` is symmetric when `Δ` and `Δ′_π` are — the CLM twin of
`RecursiveBridge.piExtended_sym`. -/
theorem piOp_symm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Δ Dpi : H →L[ℝ] H)
    (hDsym : ∀ u v : H, (inner ℝ u (Δ v) : ℝ) = (inner ℝ (Δ u) v : ℝ))
    (hPiSym : ∀ u v : H, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    (u v : H) :
    (inner ℝ u (piOp Δ Dpi v) : ℝ) = (inner ℝ (piOp Δ Dpi u) v : ℝ) := by
  rw [piOp_apply, piOp_apply, inner_sub_right, inner_sub_left, hDsym u v, hPiSym u v]

/-- **The two-sided bound on (3.120)'s indefinite correction**, named once so every consumer below
reads the same shape. It is exactly `RecursiveBridge.piExtended_coercive_at`'s `hpi` and
`DeltaPrimeBound.abs_inner_le_of_piForm`'s conclusion. -/
def PiCorrectionBound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Dpi : H →L[ℝ] H) (δ : ℝ) : Prop :=
  ∀ x : H, |(inner ℝ x (Dpi x) : ℝ)| ≤ δ * ‖x‖ ^ 2

/-- **The `(γ−δ)`-coercivity of `Δ_π`**, from `γ`-coercivity of `Δ` and the two-sided bound. CLM
twin of `RecursiveBridge.piExtended_coercive_at`; the bound must be two-sided because `Δ′_π` is
`J`-paired and has no sign. -/
theorem piOp_coercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Δ Dpi : H →L[ℝ] H) (γ δ : ℝ) (hpi : PiCorrectionBound Dpi δ) (x : H)
    (hΔ : γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ)) :
    (γ - δ) * ‖x‖ ^ 2 ≤ (inner ℝ x (piOp Δ Dpi x) : ℝ) := by
  have h2 : (inner ℝ x (Dpi x) : ℝ) ≤ δ * ‖x‖ ^ 2 := le_trans (le_abs_self _) (hpi x)
  rw [piOp_apply, inner_sub_right]
  nlinarith

/-- **A vanishing correction bounds at `δ = 0`.** This is the flat end of the family. -/
theorem piCorrectionBound_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    PiCorrectionBound (0 : H →L[ℝ] H) 0 := by
  intro x
  simp

/-- **THE TAX, ON THE GAUGE-FIXED PAIR.** From `γ`-coercivity of the UNCORRECTED `Δ + P` and the
two-sided bound on `Δ′_π`, the CORRECTED pair `Δ_π + P` is `(γ − δ)`-coercive. Stated free of any
`Rung` so it can be used to BUILD a rung (its `hinj`/`hMpos` fields need exactly this). -/
theorem gf_pi_of_gf {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Δ Dpi P : H →L[ℝ] H) (γ δ : ℝ) (hpi : PiCorrectionBound Dpi δ)
    (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (P x) : ℝ)) (x : H) :
    (γ - δ) * ‖x‖ ^ 2 ≤ (inner ℝ x (piOp Δ Dpi x) : ℝ) + (inner ℝ x (P x) : ℝ) := by
  have h1 := hDP x
  have h2 : (inner ℝ x (Dpi x) : ℝ) ≤ δ * ‖x‖ ^ 2 := le_trans (le_abs_self _) (hpi x)
  rw [piOp_apply, inner_sub_right]
  nlinarith

/-- **One RG step's data, tied to the incoming level-`k` operator `Δ`.**

`Q`, `Qstar`, `P`, `a` are the level-`k` averaging, its adjoint, the gauge-fixing form `‖RD*·‖²` of
(3.128), and the constant `a` of (3.16). The inverses are NOT fields: `G` and `S` below are
*constructed* from these by `BridgeInverse`'s kit, so a rung cannot smuggle in a fake inverse.

`hinj` and `hMpos` are the two facts that make `M = Δ + P + Q*aQ` invertible and `T = QGQ*`
positive definite; `BridgeInverse.kernel_criterion` shows `hinj` is EQUIVALENT (at `a > 0`) to
`ker(Δ+P) ∩ ker Q = 0`, so this is not a strengthening in disguise. -/
structure Rung (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] (Δ : H →L[ℝ] H) where
  /-- The level-`k` averaging operator `Q_k(U)`. -/
  Q : H →L[ℝ] K
  /-- Its adjoint. -/
  Qstar : K →L[ℝ] H
  /-- The gauge-fixing form `‖RD*·‖²` of (3.128). -/
  P : H →L[ℝ] H
  /-- CMP99b (3.16)'s constant `a`, the same at every scale. -/
  a : ℝ
  /-- An upper bound for `‖Q‖`. -/
  q : ℝ
  hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ)
  ha : 0 ≤ a
  hq : 0 < q
  hQ : ∀ x : H, ‖Q x‖ ≤ q * ‖x‖
  hDsym : ∀ u v : H, (inner ℝ u (Δ v) : ℝ) = (inner ℝ (Δ u) v : ℝ)
  hPsym : ∀ u v : H, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ)
  hPpos : ∀ x : H, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ)
  hinj : Function.Injective (fineCLM Δ P Q Qstar a)
  hMpos : ∀ x : H, x ≠ 0 → 0 < (inner ℝ x (fineCLM Δ P Q Qstar a x) : ℝ)
  hQstarInj : Function.Injective Qstar

namespace Rung

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {Δ : H →L[ℝ] H}

/-- `M = Δ + P + Q*aQ`, CMP99b (3.128)'s fine operator at this rung. -/
noncomputable def M (r : Rung H K Δ) : H →L[ℝ] H := fineCLM Δ r.P r.Q r.Qstar r.a

/-- `G₁ = M⁻¹`, CONSTRUCTED. -/
noncomputable def G (r : Rung H K Δ) : H →L[ℝ] H := gOneK Δ r.P r.Q r.Qstar r.a r.hinj

/-- `S = (Q G₁ Q*)⁻¹`, CONSTRUCTED. -/
noncomputable def S (r : Rung H K Δ) : K →L[ℝ] K :=
  sOpK Δ r.P r.Q r.Qstar r.a r.hinj r.hMpos r.hadj r.hQstarInj

/-- **THE ONE-STEP RG MAP.** `Δ_{k+1} = (Q G₁ Q*)⁻¹ − a·I`, CMP99b (3.156) at `J = 0`, as an
operator on the level-`(k+1)` carrier. -/
noncomputable def next (r : Rung H K Δ) : K →L[ℝ] K :=
  r.S - r.a • ContinuousLinearMap.id ℝ K

@[simp] theorem next_apply (r : Rung H K Δ) (B : K) : r.next B = r.S B - r.a • B := rfl

theorem next_eq_coarse156 (r : Rung H K Δ) (B : K) : r.next B = coarse156 r.S r.a B := rfl

/-- `⟨B, Δ_{k+1} B⟩ = ⟨B, S B⟩ − a‖B‖²`, i.e. (3.156)'s right-hand side verbatim. -/
theorem inner_next (r : Rung H K Δ) (B : K) :
    (inner ℝ B (r.next B) : ℝ) = (inner ℝ B (r.S B) : ℝ) - r.a * ‖B‖ ^ 2 := by
  rw [next_eq_coarse156]
  exact inner_coarse156 r.S r.a B

theorem M_G_right (r : Rung H K Δ) (x : H) : r.M (r.G x) = x :=
  gOneK_right Δ r.P r.Q r.Qstar r.a r.hinj x

theorem G_M_left (r : Rung H K Δ) (x : H) : r.G (r.M x) = x :=
  gOneK_left Δ r.P r.Q r.Qstar r.a r.hinj x

theorem M_sym (r : Rung H K Δ) (u v : H) :
    (inner ℝ u (r.M v) : ℝ) = (inner ℝ (r.M u) v : ℝ) :=
  fineCLM_symm Δ r.P r.Q r.Qstar r.a r.hadj r.hDsym r.hPsym u v

/-- `T ∘ S = id` on the coarse carrier, with `T` the bridge's `coarseComposite`. -/
theorem coarse_S (r : Rung H K Δ) (B : K) :
    coarseComposite r.Q r.G r.Qstar (r.S B) = B :=
  tOpK_sOpK Δ r.P r.Q r.Qstar r.a r.hinj r.hMpos r.hadj r.hQstarInj B

/-- `T = Q G₁ Q*`, the composite whose inverse (3.156) takes. -/
noncomputable def T (r : Rung H K Δ) : K →L[ℝ] K := coarseComposite r.Q r.G r.Qstar

theorem T_apply (r : Rung H K Δ) (B : K) : r.T B = r.Q (r.G (r.Qstar B)) := rfl

theorem T_S (r : Rung H K Δ) (B : K) : r.T (r.S B) = B := r.coarse_S B

theorem T_injective (r : Rung H K Δ) : Function.Injective r.T :=
  tOpK_injective Δ r.P r.Q r.Qstar r.a r.hinj r.hMpos r.hadj r.hQstarInj

/-- **`G₁` is identified by any explicit right inverse of `M`.** This is the tool the witnesses use
to COMPUTE the constructed inverse rather than reason about `invOfInjective` directly. -/
theorem G_eq (r : Rung H K Δ) (N : H →L[ℝ] H) (h : ∀ x : H, r.M (N x) = x) (x : H) :
    r.G x = N x := by
  refine r.hinj ?_
  show r.M (r.G x) = r.M (N x)
  rw [r.M_G_right, h]

/-- **`S` is identified by any explicit right inverse of `T`.** -/
theorem S_eq (r : Rung H K Δ) (N : K →L[ℝ] K) (h : ∀ B : K, r.T (N B) = B) (B : K) :
    r.S B = N B := by
  refine r.T_injective ?_
  rw [r.T_S, h]

/-- **THE HYPOTHESIS THE SOURCE ACTUALLY OFFERS.** `γ‖x‖² ≤ ⟨x,Δx⟩ + ⟨x,Px⟩`: coercivity of the
GAUGE-FIXED operator `Δ + P` — (3.128)'s `Δ_π + ‖RD*·‖²` — not of `Δ` alone.

**This distinction is not cosmetic and is not this module's invention.**
`BridgeInverseControls.h310_unrestricted_impossible_at_witnessU` proves in this tree that
`γ‖A‖² ≤ ⟨A, Δ^η(U) A⟩` on the WHOLE space is UNSATISFIABLE at `witnessU` for every `γ > 0`. So a
tower law stated with `CoerciveOn Δ γ` as its lattice hypothesis would be vacuous at that
background. Every lattice-facing statement below therefore uses this form. -/
def GaugeFixedCoercive (r : Rung H K Δ) (γ : ℝ) : Prop :=
  ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (r.P x) : ℝ)

/-- Whole-space coercivity of `Δ` alone is STRONGER (it implies the gauge-fixed form, since
`P ≥ 0`). Stated so the direction of the implication is on the record. -/
theorem gf_of_coercive (r : Rung H K Δ) {γ : ℝ} (hΔ : CoerciveOn (⇑Δ) γ) :
    r.GaugeFixedCoercive γ := by
  intro x
  have h1 := hΔ x
  have h2 := r.hPpos x
  linarith

/-- **THE ONE-STEP TOWER LAW.** If the level-`k` GAUGE-FIXED operator `Δ_k + P_k` is `γ`-coercive on
the whole level-`k` carrier, the level-`(k+1)` operator produced by the RG map is `(γ/q²)`-coercive
on the level-`(k+1)` carrier. The `a` of (3.16) cancels exactly: it appears in `M`, survives into
`S`, and is subtracted again in `next`, and does not appear in the constant. -/
theorem next_coercive_gf (r : Rung H K Δ) {γ : ℝ} (hγ : 0 < γ)
    (hDP : r.GaugeFixedCoercive γ) : CoerciveOn (⇑r.next) (γ / r.q ^ 2) := by
  intro B
  have hMcoerc : ∀ x : H,
      γ * ‖x‖ ^ 2 + r.a * ‖r.Q x‖ ^ 2 ≤ (inner ℝ x (r.M x) : ℝ) :=
    fineCLM_coercive Δ r.P r.Q r.Qstar r.a γ r.hadj hDP
  have hmain :=
    bridge_coercive_prim r.Q r.Qstar r.M r.G r.S r.a γ r.q r.hadj r.M_sym r.G_M_left r.M_G_right
      r.coarse_S hγ r.hq r.ha hMcoerc r.hQ B
  rw [inner_next]
  exact hmain

/-- The tower law in the stronger (and at `witnessU` unsatisfiable) `Δ`-alone form, kept because the
abstract witnesses of §6–§8 do satisfy it. -/
theorem next_coercive (r : Rung H K Δ) {γ : ℝ} (hγ : 0 < γ)
    (hΔ : CoerciveOn (⇑Δ) γ) : CoerciveOn (⇑r.next) (γ / r.q ^ 2) :=
  r.next_coercive_gf hγ (r.gf_of_coercive hΔ)

/-- **FROM A POINCARÉ-WITH-DEFECT BOUND TO THE RUNG'S HYPOTHESIS.** If the gauge-fixed form is
coercive only up to a defect proportional to `‖Qx‖²` — the shape a FIBRE bound naturally
extends to — the rung's hypothesis holds with the constant reduced by exactly `C q²`.

⚠ ~~"This is the `(γ − δ)/q²` shape of the campaign's bridge recursion with `δ = C q²`
identified."~~ **STRUCK.** `C q²` and the recursion's `δ` are two DIFFERENT subtractions:
`C q²` is the fibre-to-whole-space defect on the INPUT side (§10c), while `δ` is CMP99b (3.120)'s
correction `Δ′_π` (§4b), measured by `DeltaPrimeBound.deltaPiConst`. A statement that pays only one
of them has paid half the bill. -/
theorem gf_of_defect (r : Rung H K Δ) {γ₀ C : ℝ} (hC : 0 ≤ C)
    (hdef : ∀ x : H,
      γ₀ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (r.P x) : ℝ) + C * ‖r.Q x‖ ^ 2) :
    r.GaugeFixedCoercive (γ₀ - C * r.q ^ 2) := by
  intro x
  have h1 := hdef x
  have hQ := r.hQ x
  have hq0 : (0 : ℝ) ≤ r.q := r.hq.le
  have h2 : ‖r.Q x‖ ^ 2 ≤ r.q ^ 2 * ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg (r.Q x), norm_nonneg x]
  nlinarith

/-- ⚠ **SUPERSEDED BY `StepsPi` — this relation's `δ` IS A DECOY, and that is now on the record.**

~~"THE STEP RELATION, with the `(3.120)` correction channel `δ`."~~ **STRUCK** — item B of
`compute/tower_prosecution/VERDICT.md`. The `δ` here is bound to nothing: `stepsHet` derives
`CoerciveOn Δ'' (γ−δ)/q²` from `CoerciveOn Δ'' γ/q²` by pure monotonicity, so it holds for EVERY
`δ ≥ 0` whether or not any correction operator exists. `stepsHet_delta_is_free` below proves that.

Retained (not deleted) so the convicted object stays visible and so the contrast with `StepsPi` can
be stated as a theorem. **Nothing in this file consumes it.**

What it correctly is: the heterogeneous shape of `GammaRecursion.StepsWith` — input operator on the
fine carrier, output on the coarse one — with a free downward slack `δ`. -/
def StepsHet (δ q : ℝ) (Δ' : H →L[ℝ] H) (Δ'' : K →L[ℝ] K) : Prop :=
  ∀ γ : ℝ, 0 < γ - δ → CoerciveOn (⇑Δ') γ → CoerciveOn (⇑Δ'') ((γ - δ) / q ^ 2)

/-- Every rung satisfies the (decorative) relation at its own `q`, for any `δ ≥ 0` whatsoever. -/
theorem stepsHet (r : Rung H K Δ) {δ : ℝ} (hδ : 0 ≤ δ) : StepsHet δ r.q Δ r.next := by
  intro γ hγδ hc
  refine r.next_coercive (γ := γ - δ) hγδ ?_
  intro x
  have h1 := hc x
  have h2 : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
  nlinarith

/-- ⚠ **SUPERSEDED BY `StepsPiGF`, same defect as `StepsHet`.** The gauge-fixed variant of the
decorative relation. Nothing in this file consumes it. -/
def StepsHetGF (δ q : ℝ) (r : Rung H K Δ) (Δ'' : K →L[ℝ] K) : Prop :=
  ∀ γ : ℝ, 0 < γ - δ → r.GaugeFixedCoercive γ → CoerciveOn (⇑Δ'') ((γ - δ) / q ^ 2)

theorem stepsHetGF (r : Rung H K Δ) {δ : ℝ} (hδ : 0 ≤ δ) : StepsHetGF δ r.q r r.next := by
  intro γ hγδ hc
  refine r.next_coercive_gf (γ := γ - δ) hγδ ?_
  intro x
  have h1 := hc x
  have h2 : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
  nlinarith

end Rung

/-! ### §4b — THE CORRECTED STEP: (3.128) FED `Δ_π`, AND THE `δ` TAX PAID

This is the repair of item B. A **corrected rung** is literally a `Rung` whose index operator is
`piOp Δ Δ′_π`, so `Rung.M` unfolds to `(Δ − Δ′_π) + P + Q*aQ` — CMP99b (3.128) verbatim. Nothing in
`Rung` changes; what changes is what is passed in. -/

namespace Rung

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {D Dpi : H →L[ℝ] H}

/-- **`Rung.M` at a corrected rung is (3.128)'s operator, spelled out.** Stated so that "the fine
operator is `Δ_π + P + Q*aQ`" is a checkable equation in this file and not a claim in a docstring. -/
theorem M_apply_pi (r : Rung H K (piOp D Dpi)) (x : H) :
    r.M x = (D x - Dpi x) + r.P x + r.a • r.Qstar (r.Q x) := by
  show fineCLM (piOp D Dpi) r.P r.Q r.Qstar r.a x = _
  rw [fineCLM_apply, piOp_apply]

/-- **THE TAX, AS A HYPOTHESIS TRANSFER.** The (3.10)-level gauge-fixed coercivity of the
UNCORRECTED `Δ + P` at constant `γ`, together with the two-sided bound `δ` on `Δ′_π`, gives the
corrected rung its own gauge-fixed hypothesis at constant `γ − δ`. This is the whole cost of item
B, and it is paid here. -/
theorem gf_of_pi (r : Rung H K (piOp D Dpi)) {γ δ : ℝ}
    (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (D x) : ℝ) + (inner ℝ x (r.P x) : ℝ))
    (hpi : PiCorrectionBound Dpi δ) :
    r.GaugeFixedCoercive (γ - δ) := by
  intro x
  have h1 := hDP x
  have h2 : (inner ℝ x (Dpi x) : ℝ) ≤ δ * ‖x‖ ^ 2 := le_trans (le_abs_self _) (hpi x)
  have h3 : (inner ℝ x (piOp D Dpi x) : ℝ)
      = (inner ℝ x (D x) : ℝ) - (inner ℝ x (Dpi x) : ℝ) := by
    rw [piOp_apply, inner_sub_right]
  rw [h3]
  nlinarith

/-- **THE TAXED ONE-STEP TOWER LAW.** CMP99b (3.128) with `Δ_π` (not `Δ_k`) + (3.156) + (3.16):
if the level-`k` gauge-fixed UNCORRECTED operator `Δ_k + P_k` is `γ`-coercive and (3.120)'s
correction obeys the two-sided `|⟨x,Δ′_πx⟩| ≤ δ‖x‖²`, then the level-`(k+1)` operator produced by
the RG map is `((γ − δ)/q²)`-coercive.

`(γ − δ)/q²` is exactly the constant `RecursiveBridge.lean:1158-1161` names as the honest price of
`Δ_π ≠ Δ`. The `a` of (3.16) still cancels exactly and does not appear. -/
theorem nextPi_coercive_gf (r : Rung H K (piOp D Dpi)) {γ δ : ℝ} (hγδ : 0 < γ - δ)
    (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (D x) : ℝ) + (inner ℝ x (r.P x) : ℝ))
    (hpi : PiCorrectionBound Dpi δ) :
    CoerciveOn (⇑r.next) ((γ - δ) / r.q ^ 2) :=
  r.next_coercive_gf hγδ (r.gf_of_pi hDP hpi)

/-- The taxed law from whole-space coercivity of `Δ` alone (stronger input; used by the abstract
witnesses, never on the lattice — see §3 item 5). -/
theorem nextPi_coercive (r : Rung H K (piOp D Dpi)) {γ δ : ℝ} (hγδ : 0 < γ - δ)
    (hD : CoerciveOn (⇑D) γ) (hpi : PiCorrectionBound Dpi δ) :
    CoerciveOn (⇑r.next) ((γ - δ) / r.q ^ 2) := by
  refine r.nextPi_coercive_gf hγδ (fun x => ?_) hpi
  have h1 := hD x
  have h2 := r.hPpos x
  linarith

/-- **FLAT = UNTAXED, AS A THEOREM.** At `Δ′_π = 0` the two-sided bound holds at `δ = 0` and the
taxed law returns `γ/q²` on the nose. So the untaxed constant is not wrong — it is the `Δ′_π = 0`
special case, and this is the only place the file is entitled to it. -/
theorem nextPi_coercive_gf_at_zero (r : Rung H K (piOp D 0)) {γ : ℝ} (hγ : 0 < γ)
    (hDP : ∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (D x) : ℝ) + (inner ℝ x (r.P x) : ℝ)) :
    CoerciveOn (⇑r.next) (γ / r.q ^ 2) := by
  have h := r.nextPi_coercive_gf (γ := γ) (δ := 0) (by linarith) hDP piCorrectionBound_zero
  simpa using h

/-- **THE STEP RELATION THAT CARRIES THE CORRECTION OPERATOR.** Compare `StepsHet`: there the `δ`
slot is bound to nothing at all. Here it can only be used together with a named `Δ′_π` and a
two-sided bound on it, and the output operator `Δ''` is built from `Δ − Δ′_π`. -/
def StepsPi (δ q : ℝ) (D Dpi : H →L[ℝ] H) (Δ'' : K →L[ℝ] K) : Prop :=
  PiCorrectionBound Dpi δ →
    ∀ γ : ℝ, 0 < γ - δ → CoerciveOn (⇑D) γ → CoerciveOn (⇑Δ'') ((γ - δ) / q ^ 2)

/-- Every CORRECTED rung satisfies the corrected step relation at its own `q`. Note what is NOT
here: no `0 ≤ δ` hypothesis. On a nontrivial carrier the two-sided bound forces `δ ≥ 0` by itself
(`piCorrectionBound_nonneg`), which is one way to see that this `δ` is tied to an object and
`StepsHet`'s is not. -/
theorem stepsPi (r : Rung H K (piOp D Dpi)) {δ : ℝ} : StepsPi δ r.q D Dpi r.next :=
  fun hpi γ hγδ hc => r.nextPi_coercive hγδ hc hpi

/-! #### §4b′ — THE SAME LAWS ON THE SOURCE'S OWN RESTRICTED DOMAIN

⚠ **WHY THIS EXISTS.** `next_coercive_gf` above demands the gauge-fixed bound on the WHOLE fine
carrier. That demand is **this campaign's strengthening, not CMP99b's**: (3.156) is stated *"on the
subspace `{B : B=0 on Λᶜ, B=0 on ⋃_{y∈Λ′} Ax(y), Q₁B=0}`"* (p.428, adjudicated), and
`RecursiveBridge.bridge_bare` — the primitive under all of this — only ever evaluates its
coercivity hypothesis at points of the form `G(Q*C)`:

```
hMcoercAt : ∀ C : K, γ‖G(Q*C)‖² + a‖Q(G(Q*C))‖² ≤ ⟨G(Q*C), M(G(Q*C))⟩
```

The whole-space form is strictly stronger, and at the tree's own lattice operators it is **REFUTED**
(§10e). So the laws are restated here against the range of `G ∘ Q*` — the honest domain — and it is
these, not the whole-space ones, that a lattice consumer should aim at. -/

variable {Δ : H →L[ℝ] H}

/-- **THE ONE-STEP TOWER LAW ON `range(G ∘ Q*)`.** Identical conclusion to `next_coercive_gf`, but
the gauge-fixed hypothesis is demanded ONLY at the points `RecursiveBridge.bridge_bare` actually
uses. Strictly weaker hypothesis, same constant. -/
theorem next_coercive_gf_on_range (r : Rung H K Δ) {γ : ℝ} (hγ : 0 < γ)
    (hDPrange : ∀ C : K,
      γ * ‖r.G (r.Qstar C)‖ ^ 2
        ≤ (inner ℝ (r.G (r.Qstar C)) (Δ (r.G (r.Qstar C))) : ℝ)
          + (inner ℝ (r.G (r.Qstar C)) (r.P (r.G (r.Qstar C))) : ℝ)) :
    CoerciveOn (⇑r.next) (γ / r.q ^ 2) := by
  intro B
  have hMcoercAt : ∀ C : K,
      γ * ‖r.G (r.Qstar C)‖ ^ 2 + r.a * ‖r.Q (r.G (r.Qstar C))‖ ^ 2
        ≤ (inner ℝ (r.G (r.Qstar C)) (r.M (r.G (r.Qstar C))) : ℝ) := by
    intro C
    have hinner := fineCLM_inner Δ r.P r.Q r.Qstar r.a r.hadj (r.G (r.Qstar C))
    have h := hDPrange C
    show _ ≤ (inner ℝ (r.G (r.Qstar C))
      (fineCLM Δ r.P r.Q r.Qstar r.a (r.G (r.Qstar C))) : ℝ)
    rw [hinner]
    linarith
  have hmain :=
    bridge_bare r.Q r.Qstar r.M r.G r.T r.S r.a γ r.q r.hadj r.T_apply r.M_sym r.M_G_right
      r.T_S hγ r.hq r.ha hMcoercAt r.hQ B
  rw [inner_next]
  exact hmain

/-- **THE TAXED LAW ON `range(G ∘ Q*)`.** The item-B repair and the domain repair composed: the
(3.120) tax is paid, and the (3.10)-level hypothesis is demanded only where the primitive uses it.
This is the shape a lattice consumer should target. -/
theorem nextPi_coercive_gf_on_range (r : Rung H K (piOp D Dpi)) {γ δ : ℝ} (hγδ : 0 < γ - δ)
    (hpi : PiCorrectionBound Dpi δ)
    (hDPrange : ∀ C : K,
      γ * ‖r.G (r.Qstar C)‖ ^ 2
        ≤ (inner ℝ (r.G (r.Qstar C)) (D (r.G (r.Qstar C))) : ℝ)
          + (inner ℝ (r.G (r.Qstar C)) (r.P (r.G (r.Qstar C))) : ℝ)) :
    CoerciveOn (⇑r.next) ((γ - δ) / r.q ^ 2) := by
  refine r.next_coercive_gf_on_range hγδ (fun C => ?_)
  have h1 := hDPrange C
  have h2 : (inner ℝ (r.G (r.Qstar C)) (Dpi (r.G (r.Qstar C))) : ℝ)
      ≤ δ * ‖r.G (r.Qstar C)‖ ^ 2 := le_trans (le_abs_self _) (hpi _)
  have h3 : (inner ℝ (r.G (r.Qstar C)) (piOp D Dpi (r.G (r.Qstar C))) : ℝ)
      = (inner ℝ (r.G (r.Qstar C)) (D (r.G (r.Qstar C))) : ℝ)
        - (inner ℝ (r.G (r.Qstar C)) (Dpi (r.G (r.Qstar C))) : ℝ) := by
    rw [piOp_apply, inner_sub_right]
  rw [h3]
  nlinarith

/-- The corrected step relation on the GAUGE-FIXED hypothesis — the form the lattice can supply. -/
def StepsPiGF (δ q : ℝ) (D Dpi : H →L[ℝ] H) (r : Rung H K (piOp D Dpi))
    (Δ'' : K →L[ℝ] K) : Prop :=
  PiCorrectionBound Dpi δ →
    ∀ γ : ℝ, 0 < γ - δ →
      (∀ x : H, γ * ‖x‖ ^ 2 ≤ (inner ℝ x (D x) : ℝ) + (inner ℝ x (r.P x) : ℝ)) →
      CoerciveOn (⇑Δ'') ((γ - δ) / q ^ 2)

theorem stepsPiGF (r : Rung H K (piOp D Dpi)) {δ : ℝ} : StepsPiGF δ r.q D Dpi r r.next :=
  fun hpi γ hγδ hc => r.nextPi_coercive_gf hγδ hc hpi

/-! #### §4b″ — WHAT A MISMATCHED `a` WOULD COST, COMPUTED

`Rung` carries ONE `a`: it is the weight inside `M = Δ_π + P + Q*aQ` AND the constant subtracted in
`next = S − a·I`. §10e adjudicates, from the source's own derivation, that these two MUST be the
same number. The theorems here compute what would happen if they were not, so the adjudication is
backed by arithmetic rather than asserted. -/

/-- **THE SHIFT IS A SECOND TAX, AND HERE IT IS.** If a rung's `M` carries weight `a + c` while
`(3.156)`'s subtraction uses `a`, the operator produced is `S − a·I`, which is
`(S − (a+c)·I) + c·I` — i.e. the source's `Δ_{k+1}` at weight `a+c`, **shifted up by `c·I`**. A
`γ`-coercivity bound on the shifted object therefore yields only `γ − c` on the source's operator.
Elementary; the point is that `c` is SUBTRACTED, not free. -/
theorem shifted_subtraction_costs (S : K →L[ℝ] K) (a c γ : ℝ)
    (h : CoerciveOn (⇑(S - a • ContinuousLinearMap.id ℝ K)) γ) :
    CoerciveOn (⇑(S - (a + c) • ContinuousLinearMap.id ℝ K)) (γ - c) := by
  intro B
  have hB := h B
  have e1 : (inner ℝ B ((S - a • ContinuousLinearMap.id ℝ K) B) : ℝ)
      = (inner ℝ B (S B) : ℝ) - a * ‖B‖ ^ 2 := by
    show (inner ℝ B (S B - a • B) : ℝ) = _
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have e2 : (inner ℝ B ((S - (a + c) • ContinuousLinearMap.id ℝ K) B) : ℝ)
      = (inner ℝ B (S B) : ℝ) - (a + c) * ‖B‖ ^ 2 := by
    show (inner ℝ B (S B - (a + c) • B) : ℝ) = _
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [e1] at hB
  rw [e2]
  nlinarith

/-- **AND THE SECOND TAX IS FATAL AT THE TREE'S OWN NUMBERS.** `ExtentUniformCoercivity.cExt`
exceeds `1024` (`cExt_between`), while the transported constant available at the lattice is at most
`γ₀/q²` with `γ₀ = 1/13264896` and `q² = 1/4`, i.e. `≤ 4/13264896 < 10⁻⁶`. So `γ/q² − c_ext` is
NEGATIVE by more than three orders of magnitude: the shifted route transports nothing about the
source's `Δ_{k+1}`. Stated as arithmetic so it cannot be argued down. -/
theorem shifted_route_yields_nothing :
    (4 / 13264896 : ℝ) - 1024 < 0 ∧ (4 / 13264896 : ℝ) < 1 / 1000000 := by
  constructor <;> norm_num

end Rung

/-! ### §4c — CONTROLS ON THE `δ` CHANNEL ITSELF

Three facts that separate the repaired channel from the convicted one. -/

section DeltaChannelControls

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **`δ` IS NOT FREE DOWNWARD.** On a carrier with a nonzero vector, a correction operator's own
diagonal is a lower bound for any admissible `δ`: nothing can be bounded by less than it is. -/
theorem piCorrectionBound_forces {Dpi : H →L[ℝ] H} {δ : ℝ} (h : PiCorrectionBound Dpi δ)
    (x : H) (hx : x ≠ 0) : |(inner ℝ x (Dpi x) : ℝ)| / ‖x‖ ^ 2 ≤ δ := by
  have hn : (0 : ℝ) < ‖x‖ ^ 2 := by
    have := norm_pos_iff.2 hx
    positivity
  rw [div_le_iff₀ hn]
  have := h x
  linarith

/-- **The two-sided bound forces `δ ≥ 0` by itself** on a nontrivial carrier — no `0 ≤ δ`
hypothesis is needed anywhere in §4b. -/
theorem piCorrectionBound_nonneg {Dpi : H →L[ℝ] H} {δ : ℝ} (h : PiCorrectionBound Dpi δ)
    (x : H) (hx : x ≠ 0) : 0 ≤ δ := by
  have hn : (0 : ℝ) < ‖x‖ ^ 2 := by
    have := norm_pos_iff.2 hx
    positivity
  have h1 := h x
  have h2 : (0 : ℝ) ≤ |(inner ℝ x (Dpi x) : ℝ)| := abs_nonneg _
  nlinarith

/-- **THE DECOY, EXHIBITED.** `StepsHet`'s `δ` is satisfied by EVERY `δ ≥ 0` at once, at a rung
whose correction operator is zero — i.e. the relation is true at a `δ` for which no operator of
that size exists anywhere in the picture. That is what makes it evidence of nothing.
Contrast `piCorrectionBound_forces`. -/
theorem stepsHet_delta_is_free {K : Type*}
    [FiniteDimensional ℝ H] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] {Δ : H →L[ℝ] H} (r : Rung H K Δ) :
    ∀ δ : ℝ, 0 ≤ δ → Rung.StepsHet δ r.q Δ r.next :=
  fun _ hδ => r.stepsHet hδ

end DeltaChannelControls

end OneRung

/-! ## §5 — THE LADDER

A `Ladder` is a family of carriers `E : ℕ → Type*`, a family of operators, a rung at every level,
and the LAW that the level-`(k+1)` operator IS the RG image of the level-`k` one. The law is an
equation, not an existential: given `op 0` and the rungs, every `op k` is determined. -/

section Ladder

variable (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℝ (E k)]
  [∀ k, FiniteDimensional ℝ (E k)]

/-- **THE RG LADDER, ON THE CORRECTED OPERATOR.** `law` is the content: `op (k+1)` is not free
data, it is the one-step RG image of `op k`.

**STATEMENT CHANGE (item B repair, recorded in `compute/tower_repair/PROGRESS.md` §2).** The rung at
level `k` now sits at `piOp (op k) (dpi k) = Δ_k − Δ′_π,k`, so `(rung k).M` is CMP99b (3.128)'s
`Δ_π + P + Q*aQ`. The previous version had `rung k : Rung (E k) (E (k+1)) (op k)` — the raw `Δ_k` —
which is the substitution the prosecution convicted.

⚠ **`dpi` is FREE DATA** (§3 item 6): the structure does not, and cannot, force `dpi k` to be
(3.120)'s correction at level `k`. Every theorem below is conditional on the family the consumer
supplies. -/
structure Ladder where
  /-- The level-`k` operator `Δ_k`. -/
  op : ∀ k : ℕ, E k →L[ℝ] E k
  /-- The level-`k` correction `Δ′_π,k` of CMP99b (3.120). Free data — see the ⚠ above. -/
  dpi : ∀ k : ℕ, E k →L[ℝ] E k
  /-- The level-`k` RG step, sitting at the CORRECTED operator `Δ_k − Δ′_π,k`. -/
  rung : ∀ k : ℕ, Rung (E k) (E (k + 1)) (piOp (op k) (dpi k))
  /-- **The tower law.** -/
  law : ∀ k : ℕ, op (k + 1) = (rung k).next

variable {E}

@[simp] theorem Ladder.op_succ (Lad : Ladder E) (k : ℕ) :
    Lad.op (k + 1) = (Lad.rung k).next := Lad.law k

/-- A ladder's per-level two-sided bound on its corrections, at a single uniform `δ`. -/
def Ladder.PiBounded (Lad : Ladder E) (δ : ℝ) : Prop :=
  ∀ k : ℕ, PiCorrectionBound (Lad.dpi k) δ

/-- **Coercivity is antitone in the constant.** Used to read the uniform floor off the iterate.
Elementary; stated because `GammaRecursion` does not export it. -/
theorem coerciveOn_mono {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {Δ : F → F} {γ γ' : ℝ} (h : γ' ≤ γ) (hc : CoerciveOn Δ γ) : CoerciveOn Δ γ' := fun x =>
  le_trans (mul_le_mul_of_nonneg_right h (sq_nonneg _)) (hc x)

/-- **THE TAXED TOWER LAW, ITERATED.** For a ladder whose rungs all have the same `q` and whose
(3.120) corrections all obey the same two-sided bound `δ`, the level-`k` operator is
`gammaSeq γ₀ δ q k`-coercive — i.e. the constants iterate as `γ_{k+1} = (γ_k − δ)/q²`, **paying the
`δ` tax at every step**.

This is an induction of its own, NOT an application of `GammaRecursion.chain_gamma`: that theorem's
carrier is a single fixed type and cannot receive a dimension-dropping family. See
`Ladder.coercive_chain_gamma` for the constant-carrier case, where `chain_gamma` IS applied.

`hpos` is the bridge's own `0 < γ − δ` at every level; §5 of `GammaRecursion` shows it is not free,
and that is a fact about the constants, not about this construction. No `0 ≤ δ` hypothesis appears:
`hpi` forces it (`piCorrectionBound_nonneg`). -/
theorem Ladder.coercive (Lad : Ladder E) {γ₀ δ q : ℝ}
    (hq : ∀ k : ℕ, (Lad.rung k).q = q)
    (hpi : Lad.PiBounded δ)
    (h0 : CoerciveOn (⇑(Lad.op 0)) γ₀)
    (hpos : ∀ k : ℕ, 0 < gammaSeq γ₀ δ q k - δ) :
    ∀ k : ℕ, CoerciveOn (⇑(Lad.op k)) (gammaSeq γ₀ δ q k) := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ n ih =>
      have hs := (Lad.rung n).nextPi_coercive (γ := gammaSeq γ₀ δ q n) (δ := δ)
        (hpos n) ih (hpi n)
      rw [hq n] at hs
      rw [Lad.law n, gammaSeq_succ]
      exact hs

/-- The ladder's gauge-fixed hypothesis at level `k`, on the **UNCORRECTED** operator `Δ_k + P_k` —
the (3.10)-level statement, the only one the lattice can supply. -/
def Ladder.GF (Lad : Ladder E) (k : ℕ) (γ : ℝ) : Prop :=
  ∀ x : E k, γ * ‖x‖ ^ 2
    ≤ (inner ℝ x (Lad.op k x) : ℝ) + (inner ℝ x ((Lad.rung k).P x) : ℝ)

/-- **THE TAXED TOWER LAW FROM THE HYPOTHESIS THE LATTICE CAN SUPPLY.** Same conclusion as
`Ladder.coercive`, but the level-0 input is the GAUGE-FIXED coercivity of the uncorrected
`Δ₀ + P₀` rather than coercivity of `Δ₀` alone — the latter being refuted at `witnessU` by
`BridgeInverseControls.h310_unrestricted_impossible_at_witnessU`.

Levels `≥ 1` need no separate gauge-fixed input: the previous step's conclusion is coercivity of
`op (k+1)` on the whole carrier, and `hPpos` of the next rung upgrades it. -/
theorem Ladder.coercive_gf (Lad : Ladder E) {γ₀ δ q : ℝ}
    (hq : ∀ k : ℕ, (Lad.rung k).q = q)
    (hpi : Lad.PiBounded δ)
    (h0 : Lad.GF 0 γ₀)
    (hpos : ∀ k : ℕ, 0 < gammaSeq γ₀ δ q k - δ) :
    ∀ k : ℕ, Lad.GF k (gammaSeq γ₀ δ q k) := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ n ih =>
      have hs := (Lad.rung n).nextPi_coercive_gf (γ := gammaSeq γ₀ δ q n) (δ := δ)
        (hpos n) ih (hpi n)
      rw [hq n] at hs
      have h1 : CoerciveOn (⇑(Lad.op (n + 1))) (gammaSeq γ₀ δ q (n + 1)) := by
        rw [Lad.law n, gammaSeq_succ]
        exact hs
      intro x
      have h2 := h1 x
      have h3 := (Lad.rung (n + 1)).hPpos x
      linarith

/-- The same, read off at the operators: every level above the base is coercive on its own carrier
with the TAXED constant, from a base hypothesis the lattice can supply. -/
theorem Ladder.coercive_succ_gf (Lad : Ladder E) {γ₀ δ q : ℝ}
    (hq : ∀ k : ℕ, (Lad.rung k).q = q)
    (hpi : Lad.PiBounded δ)
    (h0 : Lad.GF 0 γ₀)
    (hpos : ∀ k : ℕ, 0 < gammaSeq γ₀ δ q k - δ) :
    ∀ k : ℕ, CoerciveOn (⇑(Lad.op (k + 1))) (gammaSeq γ₀ δ q (k + 1)) := by
  intro k
  have hs := (Lad.rung k).nextPi_coercive_gf (γ := gammaSeq γ₀ δ q k) (δ := δ) (hpos k)
    (Lad.coercive_gf hq hpi h0 hpos k) (hpi k)
  rw [hq k] at hs
  rw [Lad.law k, gammaSeq_succ]
  exact hs

/-- The `δ = 0` closed form: with NO correction the ladder's constants are exactly `γ₀ / q^{2k}`.
⚠ This is the flat/untaxed branch and it is available only because `hpi` is supplied at `δ = 0`,
i.e. `|⟨x, Δ′_π,k x⟩| ≤ 0` at every level — the correction's DIAGONAL vanishes identically. (That
is the whole of what any theorem here uses. It forces `Δ′_π,k = 0` only for a symmetric correction,
by polarisation, and `Ladder` does not carry symmetry of `dpi`; so the precise reading is the
diagonal one, and it is stated that way rather than rounded up.) -/
theorem Ladder.coercive_geom (Lad : Ladder E) {γ₀ q : ℝ} (hγ : 0 < γ₀) (hq0 : 0 < q)
    (hq : ∀ k : ℕ, (Lad.rung k).q = q)
    (hpi : Lad.PiBounded 0)
    (h0 : CoerciveOn (⇑(Lad.op 0)) γ₀) :
    ∀ k : ℕ, CoerciveOn (⇑(Lad.op k)) (γ₀ / q ^ (2 * k)) := by
  intro k
  have h := Lad.coercive (δ := 0) (γ₀ := γ₀) (q := q) hq hpi h0
    (fun j => by
      rw [sub_zero]
      exact gammaSeq_pos_of_delta_zero hγ hq0 j) k
  rwa [gammaSeq_delta_zero] at h

/-! ### §5b — `chain_gamma`, ACTUALLY APPLIED (item C)

`GammaRecursion.chain_gamma`'s signature is `Δ : ℕ → (H → H)` — **one fixed carrier `H`**. A ladder
with genuinely dimension-dropping steps (`blockRung : ℝ² → ℝ`) cannot be presented in that shape at
all, which is why `Ladder.coercive` above is a separate induction. On a ladder whose carriers are
all one type, however, the rungs DO produce `GammaRecursion.StepsWith`, and then `chain_gamma`
applies literally, with its `hstep` hypothesis supplied by a theorem rather than assumed. -/

/-- **`hstep` AS A THEOREM.** Each rung of a constant-carrier ladder realises
`GammaRecursion.StepsWith δ q`. -/
theorem Ladder.stepsWith_const {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (Lad : Ladder (fun _ : ℕ => F)) {δ q : ℝ}
    (hq : ∀ k : ℕ, (Lad.rung k).q = q) (hpi : Lad.PiBounded δ) (k : ℕ) :
    StepsWith δ q (⇑(Lad.op k)) (⇑(Lad.op (k + 1))) := by
  intro γ hγδ hc
  have hs := (Lad.rung k).nextPi_coercive (γ := γ) (δ := δ) hγδ hc (hpi k)
  rw [hq k] at hs
  rw [Lad.law k]
  exact hs

/-- **`GammaRecursion.chain_gamma`, APPLIED.** This is item C of
`compute/tower_prosecution/VERDICT.md` repaired: the theorem is invoked, not merely resembled, and
its `hstep` comes from `Ladder.stepsWith_const`. -/
theorem Ladder.coercive_chain_gamma {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (Lad : Ladder (fun _ : ℕ => F)) {γ₀ δ q : ℝ}
    (hq : ∀ k : ℕ, (Lad.rung k).q = q) (hpi : Lad.PiBounded δ)
    (h0 : CoerciveOn (⇑(Lad.op 0)) γ₀)
    (hpos : ∀ k : ℕ, 0 < gammaSeq γ₀ δ q k - δ) :
    ∀ k : ℕ, CoerciveOn (⇑(Lad.op k)) (gammaSeq γ₀ δ q k) :=
  chain_gamma (fun k => ⇑(Lad.op k)) (Lad.stepsWith_const hq hpi) h0 hpos

/-! ### §5c — THE `k`-UNIFORM TOWER

The taxed recursion `γ_{k+1} = (γ_k − δ)/q²` is EXPANDING at `q < 1`, so a `δ` small enough
relative to `γ₀` leaves the constants above their starting value forever. The floor is
`ComposedCoercivity.gammaSeq_floor_pinned` (imported, not re-proved — LAW-19), and the criterion
`δ ≤ γ₀(1 − q²)` is exactly the one `ComposedCoercivity.criterion_closes_at_gammaFibre` discharges
at the tree's own numbers with margin `375/304`. -/

/-- **THE TAX IS AFFORDABLE, AS A THEOREM.** `0 < q < 1` and `δ ≤ γ₀(1 − q²)` give
`0 < gammaSeq γ₀ δ q k − δ` at every level, so the bridge's own positivity hypothesis is not an
extra assumption once the criterion holds. -/
theorem gammaSeq_pos_of_criterion {γ₀ δ q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - q ^ 2)) (k : ℕ) : 0 < gammaSeq γ₀ δ q k - δ := by
  have hq2 : (0 : ℝ) < q ^ 2 := by positivity
  have hq2' : q ^ 2 < 1 := by nlinarith
  have hfloor := AdalyFormal.Balaban.ComposedCoercivity.gammaSeq_floor_pinned hq0 hq1 hfix k
  nlinarith

/-- **THE `k`-UNIFORM TAXED TOWER.** Under the criterion, EVERY level of the ladder is
`γ₀`-coercive — the constant does not decay, tax and all. -/
theorem Ladder.coercive_uniform (Lad : Ladder E) {γ₀ δ q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hγ : 0 < γ₀) (hfix : δ ≤ γ₀ * (1 - q ^ 2))
    (hq : ∀ k : ℕ, (Lad.rung k).q = q) (hpi : Lad.PiBounded δ)
    (h0 : CoerciveOn (⇑(Lad.op 0)) γ₀) :
    ∀ k : ℕ, CoerciveOn (⇑(Lad.op k)) γ₀ := by
  intro k
  refine coerciveOn_mono
    (AdalyFormal.Balaban.ComposedCoercivity.gammaSeq_floor_pinned hq0 hq1 hfix k) ?_
  exact Lad.coercive hq hpi h0 (gammaSeq_pos_of_criterion hq0 hq1 hγ hfix) k

end Ladder

/-! ## §6 — THE SCALAR WITNESS: unbounded depth, `a > 0` allowed, and the `a`-cancellation

`E k = ℝ` at every level. This witness is deliberately the simplest carrier on which the whole
step — inverse of `M`, inverse of `QGQ*`, and the `−a·I` subtraction — can be computed in closed
form, so that `next` can be checked against hand arithmetic rather than trusted. -/

section ScalarWitness

/-- Multiplication by `t`, as a continuous linear map on `ℝ`. -/
noncomputable def mulCLM (t : ℝ) : ℝ →L[ℝ] ℝ := t • ContinuousLinearMap.id ℝ ℝ

@[simp] theorem mulCLM_apply (t x : ℝ) : mulCLM t x = t * x := by
  simp [mulCLM, smul_eq_mul]

theorem mulCLM_injective {t : ℝ} (ht : t ≠ 0) : Function.Injective (mulCLM t) := by
  intro u v huv
  simp only [mulCLM_apply] at huv
  exact mul_left_cancel₀ ht huv

theorem inner_real (x y : ℝ) : (inner ℝ x y : ℝ) = x * y := by
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem norm_sq_real (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by
  rw [Real.norm_eq_abs, sq_abs]

/-- The inverse of an injective operator, identified by an explicit right inverse. -/
theorem invOfInjective_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (Mop N : H →L[ℝ] H) (hM : Function.Injective Mop)
    (h : ∀ x : H, Mop (N x) = x) (y : H) : invOfInjective Mop hM y = N y := by
  refine hM ?_
  rw [invOfInjective_right, h]

variable (c θ a : ℝ)

/-- The scalar rung's fine operator, computed: `M = (c + aθ²)·id`, for ANY index operator that acts
as multiplication by `c`.

**Generic in the index operator on purpose**: the CORRECTED rung of §6b sits at
`piOp (mulCLM c) (mulCLM ε)`, which acts as multiplication by `c − ε` but is not syntactically a
`mulCLM`. Without this generalisation the taxed witness would need a type-level transport. -/
theorem scalarGen_M_apply (D : ℝ →L[ℝ] ℝ) (hD : ∀ x : ℝ, D x = c * x) (x : ℝ) :
    fineCLM D 0 (mulCLM θ) (mulCLM θ) a x = (c + a * θ ^ 2) * x := by
  rw [fineCLM_apply, hD]
  simp only [mulCLM_apply, ContinuousLinearMap.zero_apply, smul_eq_mul]
  ring

theorem scalarGen_M_injective (D : ℝ →L[ℝ] ℝ) (hD : ∀ x : ℝ, D x = c * x)
    (h : c + a * θ ^ 2 ≠ 0) :
    Function.Injective (fineCLM D 0 (mulCLM θ) (mulCLM θ) a) := by
  intro u v huv
  rw [scalarGen_M_apply c θ a D hD, scalarGen_M_apply c θ a D hD] at huv
  exact mul_left_cancel₀ h huv

/-- **The scalar rung, at an arbitrary index operator acting as `c·id`.** `Q = Q* = θ·id`, `P = 0`,
`a ≥ 0` arbitrary. -/
noncomputable def scalarRungGen (D : ℝ →L[ℝ] ℝ) (hD : ∀ x : ℝ, D x = c * x)
    (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) :
    Rung ℝ ℝ D where
  Q := mulCLM θ
  Qstar := mulCLM θ
  P := 0
  a := a
  q := θ
  hadj := by
    intro x B
    rw [inner_real, inner_real, mulCLM_apply, mulCLM_apply]
    ring
  ha := ha
  hq := hθ
  hQ := by
    intro x
    rw [mulCLM_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hθ]
  hDsym := by
    intro u v
    rw [inner_real, inner_real, hD, hD]
    ring
  hPsym := by
    intro u v
    simp [inner_real]
  hPpos := by
    intro x
    simp [inner_real]
  hinj := scalarGen_M_injective c θ a D hD (by positivity)
  hMpos := by
    intro x hx
    rw [inner_real, scalarGen_M_apply c θ a D hD]
    have h1 : 0 < c + a * θ ^ 2 := by positivity
    have h2 : 0 < x ^ 2 := by positivity
    nlinarith
  hQstarInj := mulCLM_injective (ne_of_gt hθ)

/-- The scalar rung's fine operator at the plain index `c·id`. -/
theorem scalar_M_apply (x : ℝ) :
    fineCLM (mulCLM c) 0 (mulCLM θ) (mulCLM θ) a x = (c + a * θ ^ 2) * x :=
  scalarGen_M_apply c θ a (mulCLM c) (mulCLM_apply c) x

theorem scalar_M_injective (h : c + a * θ ^ 2 ≠ 0) :
    Function.Injective (fineCLM (mulCLM c) 0 (mulCLM θ) (mulCLM θ) a) :=
  scalarGen_M_injective c θ a (mulCLM c) (mulCLM_apply c) h

/-- **The scalar rung.** `Δ = c·id` on `ℝ`, `Q = Q* = θ·id`, `P = 0`, `a ≥ 0` arbitrary. -/
noncomputable def scalarRung (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) :
    Rung ℝ ℝ (mulCLM c) :=
  scalarRungGen c θ a (mulCLM c) (mulCLM_apply c) hc hθ ha

@[simp] theorem scalarRung_q (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) :
    (scalarRung c θ a hc hθ ha).q = θ := rfl

theorem scalarRung_Q (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) :
    (scalarRung c θ a hc hθ ha).Q = mulCLM θ := rfl

theorem scalarRung_Qstar (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) :
    (scalarRung c θ a hc hθ ha).Qstar = mulCLM θ := rfl

theorem scalarRung_a_eq (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) :
    (scalarRung c θ a hc hθ ha).a = a := rfl

/-- `G₁ = (c + aθ²)⁻¹·id`, computed, at an arbitrary index acting as `c·id`. -/
theorem scalarRungGen_G (D : ℝ →L[ℝ] ℝ) (hD : ∀ x : ℝ, D x = c * x)
    (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (y : ℝ) :
    (scalarRungGen c θ a D hD hc hθ ha).G y = (c + a * θ ^ 2)⁻¹ * y := by
  have hpos : (0 : ℝ) < c + a * θ ^ 2 := by positivity
  have hMN : ∀ x : ℝ,
      (scalarRungGen c θ a D hD hc hθ ha).M (mulCLM (c + a * θ ^ 2)⁻¹ x) = x := by
    intro x
    show fineCLM D 0 (mulCLM θ) (mulCLM θ) a (mulCLM (c + a * θ ^ 2)⁻¹ x) = x
    rw [scalarGen_M_apply c θ a D hD, mulCLM_apply, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
  rw [(scalarRungGen c θ a D hD hc hθ ha).G_eq (mulCLM (c + a * θ ^ 2)⁻¹) hMN y, mulCLM_apply]

/-- `T = QG₁Q* = θ²/(c+aθ²)·id`, computed. -/
theorem scalarRungGen_T (D : ℝ →L[ℝ] ℝ) (hD : ∀ x : ℝ, D x = c * x)
    (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (B : ℝ) :
    (scalarRungGen c θ a D hD hc hθ ha).T B = (θ ^ 2 * (c + a * θ ^ 2)⁻¹) * B := by
  show (scalarRungGen c θ a D hD hc hθ ha).Q
      ((scalarRungGen c θ a D hD hc hθ ha).G
        ((scalarRungGen c θ a D hD hc hθ ha).Qstar B)) = _
  show mulCLM θ ((scalarRungGen c θ a D hD hc hθ ha).G (mulCLM θ B)) = _
  simp only [mulCLM_apply, scalarRungGen_G]
  ring

/-- `S = (c+aθ²)/θ²·id`, computed. -/
theorem scalarRungGen_S (D : ℝ →L[ℝ] ℝ) (hD : ∀ x : ℝ, D x = c * x)
    (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (B : ℝ) :
    (scalarRungGen c θ a D hD hc hθ ha).S B = ((c + a * θ ^ 2) / θ ^ 2) * B := by
  have hpos : (0 : ℝ) < c + a * θ ^ 2 := by positivity
  have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
  have hTN : ∀ B' : ℝ,
      (scalarRungGen c θ a D hD hc hθ ha).T (mulCLM ((c + a * θ ^ 2) / θ ^ 2) B') = B' := by
    intro B'
    rw [mulCLM_apply, scalarRungGen_T]
    field_simp
  rw [(scalarRungGen c θ a D hD hc hθ ha).S_eq (mulCLM ((c + a * θ ^ 2) / θ ^ 2)) hTN B,
    mulCLM_apply]

/-- `G₁ = (c + aθ²)⁻¹·id`, at the plain index. -/
theorem scalarRung_G (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (y : ℝ) :
    (scalarRung c θ a hc hθ ha).G y = (c + a * θ ^ 2)⁻¹ * y :=
  scalarRungGen_G c θ a (mulCLM c) (mulCLM_apply c) hc hθ ha y

/-- `T = QG₁Q* = θ²/(c+aθ²)·id`, at the plain index. -/
theorem scalarRung_T (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (B : ℝ) :
    (scalarRung c θ a hc hθ ha).T B = (θ ^ 2 * (c + a * θ ^ 2)⁻¹) * B :=
  scalarRungGen_T c θ a (mulCLM c) (mulCLM_apply c) hc hθ ha B

/-- `S = (c+aθ²)/θ²·id`, at the plain index. -/
theorem scalarRung_S (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (B : ℝ) :
    (scalarRung c θ a hc hθ ha).S B = ((c + a * θ ^ 2) / θ ^ 2) * B :=
  scalarRungGen_S c θ a (mulCLM c) (mulCLM_apply c) hc hθ ha B

/-- The arithmetic of the `−a·I` subtraction, isolated. -/
theorem aCancel {c' θ' a' : ℝ} (hθ2 : (0 : ℝ) < θ' ^ 2) :
    (c' + a' * θ' ^ 2) / θ' ^ 2 - a' = c' / θ' ^ 2 := by
  rw [add_div, mul_div_assoc, div_self (ne_of_gt hθ2), mul_one, add_sub_cancel_right]

/-- **`Δ_{k+1} = (c/θ²)·id` — AND IT DOES NOT DEPEND ON `a`.** This is the `−a·I` cancellation of
(3.128)+(3.156) exhibited on a carrier where both sides are computable: `a` enters `M`, survives
into `S`, and is removed exactly by `next`'s subtraction. A step that dropped the `a` term
anywhere would land on a different operator. -/
theorem scalarRungGen_next (D : ℝ →L[ℝ] ℝ) (hD : ∀ x : ℝ, D x = c * x)
    (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (B : ℝ) :
    (scalarRungGen c θ a D hD hc hθ ha).next B = (c / θ ^ 2) * B := by
  have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
  rw [Rung.next_apply, scalarRungGen_S]
  show (c + a * θ ^ 2) / θ ^ 2 * B - a • B = c / θ ^ 2 * B
  rw [smul_eq_mul, ← sub_mul, aCancel hθ2]

theorem scalarRung_next (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (B : ℝ) :
    (scalarRung c θ a hc hθ ha).next B = (c / θ ^ 2) * B :=
  scalarRungGen_next c θ a (mulCLM c) (mulCLM_apply c) hc hθ ha B

/-- The `a`-independence, stated on its own so it cannot be missed. -/
theorem scalarRung_next_independent_of_a (hc : 0 < c) (hθ : 0 < θ) {a₁ a₂ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (B : ℝ) :
    (scalarRung c θ a₁ hc hθ ha₁).next B = (scalarRung c θ a₂ hc hθ ha₂).next B := by
  rw [scalarRung_next, scalarRung_next]

end ScalarWitness

/-! ## §6b — THE CORRECTED SCALAR RUNG, AND THE TAXED/UNTAXED PAIR

The two-sided control the repair owes: at a NON-ZERO `Δ′_π` the corrected step lands on a strictly
smaller operator, and at `Δ′_π = 0` the two steps coincide exactly. Both are computed in closed
form, so neither is an inequality that could be slack. -/

section CorrectedScalarWitness

/-- **The CORRECTED scalar rung.** Index operator `piOp (c·id) (ε·id) = (c−ε)·id`, i.e. CMP99b
(3.120)'s `Δ_π` with `Δ = c·id` and `Δ′_π = ε·id`. Its fine operator is
`(c−ε)·id + 0 + Q*aQ` — (3.128) with `Δ_π`, not with `Δ`. -/
noncomputable def scalarRungPi (c ε θ a : ℝ) (hcε : 0 < c - ε) (hθ : 0 < θ) (ha : 0 ≤ a) :
    Rung ℝ ℝ (piOp (mulCLM c) (mulCLM ε)) :=
  scalarRungGen (c - ε) θ a (piOp (mulCLM c) (mulCLM ε))
    (fun x => by rw [piOp_apply, mulCLM_apply, mulCLM_apply]; ring) hcε hθ ha

/-- **`Δ_1 = ((c−ε)/θ²)·id`, computed.** The tax lands on the operator itself, not only on the
constant. -/
theorem scalarRungPi_next (c ε θ a : ℝ) (hcε : 0 < c - ε) (hθ : 0 < θ) (ha : 0 ≤ a) (B : ℝ) :
    (scalarRungPi c ε θ a hcε hθ ha).next B = ((c - ε) / θ ^ 2) * B :=
  scalarRungGen_next (c - ε) θ a (piOp (mulCLM c) (mulCLM ε)) _ hcε hθ ha B

/-- **MUST-FIRE: THE CORRECTION MOVES THE OPERATOR.** At `ε > 0` the corrected step lands STRICTLY
below the uncorrected one. If the `Δ_π → Δ` substitution were harmless, these two would agree. -/
theorem corrected_rung_moves_operator {c ε θ a : ℝ} (hcε : 0 < c - ε) (hε : 0 < ε) (hθ : 0 < θ)
    (ha : 0 ≤ a) (hc : 0 < c) :
    (scalarRungPi c ε θ a hcε hθ ha).next 1 < (scalarRung c θ a hc hθ ha).next 1 := by
  rw [scalarRungPi_next, scalarRung_next, mul_one, mul_one]
  have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
  rw [div_lt_div_iff_of_pos_right hθ2]
  linarith

/-- **MUST-NOT-FIRE: AT `Δ′_π = 0` THE TWO STEPS COINCIDE EXACTLY.** So the untaxed law is not
wrong — it is the flat special case, and `γ/q²` is honest exactly there. -/
theorem corrected_rung_eq_at_zero_correction {c θ a : ℝ} (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a)
    (B : ℝ) :
    (scalarRungPi c 0 θ a (by linarith) hθ ha).next B = (scalarRung c θ a hc hθ ha).next B := by
  rw [scalarRungPi_next, scalarRung_next, sub_zero]

/-- **THE TAX IS EXACT, NOT SLACK.** With `Δ = c·id` (best constant `c`) and `Δ′_π = ε·id` (best
two-sided bound `ε`), the taxed law promises `(c−ε)/θ²` and the operator it produces has best
coercivity constant EXACTLY `(c−ε)/θ²`. So the `δ` subtraction is not a lossy estimate: it is
attained. -/
theorem corrected_rung_bound_sharp {c ε θ a : ℝ} (hcε : 0 < c - ε) (hθ : 0 < θ) (ha : 0 ≤ a) :
    (∀ B : ℝ, (inner ℝ B ((scalarRungPi c ε θ a hcε hθ ha).next B) : ℝ)
        = ((c - ε) / θ ^ 2) * ‖B‖ ^ 2)
    ∧ (∀ γ : ℝ, CoerciveOn (⇑(scalarRungPi c ε θ a hcε hθ ha).next) γ →
        γ ≤ (c - ε) / θ ^ 2) := by
  constructor
  · intro B
    rw [inner_real, scalarRungPi_next, norm_sq_real]
    ring
  · intro γ hγ
    have h := hγ 1
    rw [inner_real, scalarRungPi_next] at h
    simp only [norm_one, one_pow, mul_one] at h
    linarith

/-- **THE TAXED LAW AT THE CORRECTED RUNG, INSTANTIATED.** `Δ = c·id` is `c`-coercive, `Δ′_π = ε·id`
is bounded by `ε`, and the coarse operator is `((c−ε)/θ²)`-coercive. Every ingredient is computed;
nothing is an upper bound in disguise. -/
theorem corrected_rung_tower_law {c ε θ a : ℝ} (hcε : 0 < c - ε) (hε : 0 ≤ ε) (hθ : 0 < θ)
    (ha : 0 ≤ a) :
    CoerciveOn (⇑(scalarRungPi c ε θ a hcε hθ ha).next) ((c - ε) / θ ^ 2) := by
  have hD : CoerciveOn (⇑(mulCLM c)) c := by
    intro x
    rw [inner_real, mulCLM_apply, norm_sq_real]
    exact le_of_eq (by ring)
  have hpi : PiCorrectionBound (mulCLM ε) ε := by
    intro x
    rw [inner_real, mulCLM_apply, norm_sq_real]
    have h : x * (ε * x) = ε * x ^ 2 := by ring
    rw [h, abs_of_nonneg (mul_nonneg hε (sq_nonneg x))]
  have h := (scalarRungPi c ε θ a hcε hθ ha).nextPi_coercive (γ := c) (δ := ε) hcε hD hpi
  have hq : (scalarRungPi c ε θ a hcε hθ ha).q = θ := rfl
  rwa [hq] at h

end CorrectedScalarWitness

/-! ## §7 — THE SCALAR LADDER: unbounded depth, genuinely `k`-dependent -/

section ScalarLadder

variable {c θ a : ℝ}

/-- The level-`k` operator of the scalar ladder: `Δ_k = (c/θ^{2k})·id`. -/
noncomputable def scalarOp (c θ : ℝ) (k : ℕ) : ℝ →L[ℝ] ℝ := mulCLM (c / θ ^ (2 * k))

@[simp] theorem scalarOp_apply (c θ : ℝ) (k : ℕ) (x : ℝ) :
    scalarOp c θ k x = (c / θ ^ (2 * k)) * x := mulCLM_apply _ _

theorem scalarOp_pos (hc : 0 < c) (hθ : 0 < θ) (k : ℕ) : 0 < c / θ ^ (2 * k) := by positivity

/-- The scalar ladder's index operator at level `k`: `piOp (Δ_k) 0`, which acts as multiplication
by `c/θ^{2k}`. Spelled out because the ladder's rung must sit at `piOp (op k) (dpi k)`, not at
`op k`. -/
theorem scalarOp_piOp_zero_apply (c θ : ℝ) (k : ℕ) (x : ℝ) :
    piOp (scalarOp c θ k) 0 x = (c / θ ^ (2 * k)) * x := by
  rw [piOp_apply, scalarOp_apply]
  simp

/-- **THE SCALAR LADDER** — an inhabitant of `Ladder` of unbounded depth on nontrivial carriers,
with `a > 0` permitted at every rung. The `law` field is a THEOREM here, not an assumption:
`scalarRungGen_next` computes the RG image and it equals the next operator on the nose.

⚠ **This is the UNTAXED branch**: `dpi k = 0` at every level, so its constants are the flat
`γ₀/q^{2k}`. The TAXED ladder, with a genuine non-zero correction at every level, is
`taxedScalarLadder` in §7b. -/
noncomputable def scalarLadder (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) :
    Ladder (fun _ : ℕ => ℝ) where
  op := fun k => scalarOp c θ k
  dpi := fun _ => 0
  rung := fun k =>
    scalarRungGen (c / θ ^ (2 * k)) θ a (piOp (scalarOp c θ k) 0)
      (scalarOp_piOp_zero_apply c θ k) (scalarOp_pos hc hθ k) hθ ha
  law := by
    intro k
    refine ContinuousLinearMap.ext fun B => ?_
    show scalarOp c θ (k + 1) B
        = (scalarRungGen (c / θ ^ (2 * k)) θ a (piOp (scalarOp c θ k) 0)
            (scalarOp_piOp_zero_apply c θ k) (scalarOp_pos hc hθ k) hθ ha).next B
    rw [scalarRungGen_next, scalarOp_apply]
    have hpow : θ ^ (2 * (k + 1)) = θ ^ (2 * k) * θ ^ 2 := by
      rw [← pow_add, show 2 * (k + 1) = 2 * k + 2 from by ring]
    rw [hpow, ← div_div]

theorem scalarLadder_q (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (k : ℕ) :
    ((scalarLadder hc hθ ha).rung k).q = θ := rfl

/-- The untaxed ladder's corrections really are zero, so it bounds at `δ = 0`. -/
theorem scalarLadder_piBounded (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) :
    (scalarLadder hc hθ ha).PiBounded 0 := fun _ => piCorrectionBound_zero

/-- The ladder's carriers are nontrivial at every level — so the structure is not inhabited here by
the degenerate zero-space route flagged in §3. -/
theorem scalarLadder_carrier_nontrivial (k : ℕ) : Nontrivial ((fun _ : ℕ => ℝ) k) :=
  inferInstanceAs (Nontrivial ℝ)

/-- The level-`k` operator of the ladder at `c = 1, θ = 1/2`, computed in closed form: `4^k`. -/
theorem scalarOp_half_value (k : ℕ) : scalarOp 1 (1 / 2 : ℝ) k 1 = (4 : ℝ) ^ k := by
  have h1 : ((1 : ℝ) / 2) ^ (2 * k) = ((1 : ℝ) / 4) ^ k := by
    rw [pow_mul]
    norm_num
  rw [scalarOp_apply, mul_one, h1, one_div, ← inv_pow]
  norm_num

/-- **THE LADDER IS GENUINELY `k`-DEPENDENT.** At `c = 1, θ = 1/2` the operators are pairwise
distinct — the level-`k` operator is multiplication by `4^k`. The scale index is not decorative.
Contrast `CoercivityRegular.regularDelta_k_constant` and `RGLadderCoarse.flatLadder_k_constant`. -/
theorem scalarLadder_k_dependent {k j : ℕ} (hkj : k ≠ j) :
    scalarOp 1 (1 / 2 : ℝ) k ≠ scalarOp 1 (1 / 2 : ℝ) j := by
  intro hcon
  have h : scalarOp 1 (1 / 2 : ℝ) k 1 = scalarOp 1 (1 / 2 : ℝ) j 1 := by rw [hcon]
  rw [scalarOp_half_value, scalarOp_half_value] at h
  have hnat : ((4 ^ k : ℕ) : ℝ) = ((4 ^ j : ℕ) : ℝ) := by push_cast; exact h
  exact hkj (Nat.pow_right_injective (by norm_num) (Nat.cast_injective hnat))

/-- The scalar ladder's level-0 coercivity, isolated so both the untaxed and the `chain_gamma`
readings can consume it. -/
theorem scalarLadder_coercive_zero (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) :
    CoerciveOn (⇑((scalarLadder hc hθ ha).op 0)) c := by
  intro x
  show c * ‖x‖ ^ 2 ≤ (inner ℝ x (scalarOp c θ 0 x) : ℝ)
  rw [inner_real, scalarOp_apply, norm_sq_real]
  have hz : θ ^ (2 * 0) = 1 := by norm_num
  rw [hz, div_one]
  exact le_of_eq (by ring)

/-- **THE TOWER LAW ON THE (UNTAXED) SCALAR LADDER, ITERATED.**
~~"`chain_gamma`'s conclusion with `hstep` discharged by construction."~~ **STRUCK, item C** — this
is `Ladder.coercive_geom`'s conclusion; `chain_gamma` itself is applied in
`scalarLadder_chain_gamma` below. -/
theorem scalarLadder_coercive (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (k : ℕ) :
    CoerciveOn (⇑((scalarLadder hc hθ ha).op k)) (c / θ ^ (2 * k)) :=
  (scalarLadder hc hθ ha).coercive_geom hc hθ (scalarLadder_q hc hθ ha)
    (scalarLadder_piBounded hc hθ ha) (scalarLadder_coercive_zero hc hθ ha) k

/-- **`GammaRecursion.chain_gamma` APPLIED to this ladder** — the carriers are all `ℝ`, so its
fixed-carrier signature fits, and its `hstep` is supplied by `Ladder.stepsWith_const`. Item C of
`compute/tower_prosecution/VERDICT.md`, made true where it can be true. -/
theorem scalarLadder_chain_gamma (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (k : ℕ) :
    CoerciveOn (⇑((scalarLadder hc hθ ha).op k)) (gammaSeq c 0 θ k) :=
  (scalarLadder hc hθ ha).coercive_chain_gamma (scalarLadder_q hc hθ ha)
    (scalarLadder_piBounded hc hθ ha) (scalarLadder_coercive_zero hc hθ ha)
    (fun j => by rw [sub_zero]; exact gammaSeq_pos_of_delta_zero hc hθ j) k

end ScalarLadder

/-! ## §7b — THE **TAXED** SCALAR LADDER: a non-zero (3.120) correction at every level

This is the witness that separates the repaired `δ` channel from the convicted one. `Δ_k` is
multiplication by `gammaSeq γ₀ δ θ k` and `Δ′_π,k` is multiplication by `δ` — a genuine, non-zero
correction operator, bounded two-sidedly by exactly `δ` and by nothing smaller. The RG image of
level `k` is then multiplication by `(γ_k − δ)/θ²`, i.e. by `gammaSeq γ₀ δ θ (k+1)`:
**the ladder's operators ARE the taxed recursion.** -/

section TaxedLadder

variable {γ₀ δ θ a : ℝ}

/-- The taxed ladder's level-`k` operator: multiplication by `gammaSeq γ₀ δ θ k`. -/
noncomputable def taxedOp (γ₀ δ θ : ℝ) (k : ℕ) : ℝ →L[ℝ] ℝ := mulCLM (gammaSeq γ₀ δ θ k)

@[simp] theorem taxedOp_apply (γ₀ δ θ : ℝ) (k : ℕ) (x : ℝ) :
    taxedOp γ₀ δ θ k x = gammaSeq γ₀ δ θ k * x := mulCLM_apply _ _

/-- The taxed ladder's index operator at level `k` is `Δ_k − δ·id`, acting as multiplication by
`γ_k − δ`. -/
theorem taxedOp_piOp_apply (γ₀ δ θ : ℝ) (k : ℕ) (x : ℝ) :
    piOp (taxedOp γ₀ δ θ k) (mulCLM δ) x = (gammaSeq γ₀ δ θ k - δ) * x := by
  rw [piOp_apply, taxedOp_apply, mulCLM_apply]
  ring

/-- **THE TWO-SIDED BOUND IS EXACT HERE.** `|⟨x, δ·x⟩| = δ‖x‖²`: the correction is bounded by `δ`
and by nothing smaller, so this ladder cannot pretend its tax away. -/
theorem taxedDpi_bound (hδ : 0 ≤ δ) : PiCorrectionBound (mulCLM δ) δ := by
  intro x
  rw [inner_real, mulCLM_apply, norm_sq_real]
  have h : x * (δ * x) = δ * x ^ 2 := by ring
  rw [h, abs_of_nonneg (mul_nonneg hδ (sq_nonneg x))]

/-- **MUST-FIRE: NO SMALLER `δ` WORKS AT THIS WITNESS.** The two-sided bound on `δ·id` fails for
every `δ' < δ` (test point `x = 1`). So the taxed ladder's `δ` is pinned from below by its own
correction operator — the exact property `StepsHet`'s `δ` lacks. -/
theorem taxedDpi_no_smaller {δ' : ℝ} (h : δ' < δ) : ¬ PiCorrectionBound (mulCLM δ) δ' := by
  intro hcon
  have h1 := hcon 1
  rw [inner_real, mulCLM_apply, norm_sq_real, one_pow, mul_one] at h1
  rw [show (1 : ℝ) * δ = δ from one_mul δ] at h1
  rcases le_or_gt 0 δ with hδ | hδ
  · rw [abs_of_nonneg hδ] at h1; linarith
  · rw [abs_of_neg hδ] at h1; linarith

/-- **THE TAXED SCALAR LADDER.** Requires the criterion `δ ≤ γ₀(1−θ²)` with `0 < θ < 1`, which is
what keeps `γ_k − δ > 0` at every level (`gammaSeq_pos_of_criterion`) — without it the recursion
runs the constant negative and no rung exists. -/
noncomputable def taxedScalarLadder (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - θ ^ 2)) (ha : 0 ≤ a) :
    Ladder (fun _ : ℕ => ℝ) where
  op := fun k => taxedOp γ₀ δ θ k
  dpi := fun _ => mulCLM δ
  rung := fun k =>
    scalarRungGen (gammaSeq γ₀ δ θ k - δ) θ a (piOp (taxedOp γ₀ δ θ k) (mulCLM δ))
      (taxedOp_piOp_apply γ₀ δ θ k) (gammaSeq_pos_of_criterion hθ0 hθ1 hγ hfix k) hθ0 ha
  law := by
    intro k
    refine ContinuousLinearMap.ext fun B => ?_
    show taxedOp γ₀ δ θ (k + 1) B
        = (scalarRungGen (gammaSeq γ₀ δ θ k - δ) θ a (piOp (taxedOp γ₀ δ θ k) (mulCLM δ))
            (taxedOp_piOp_apply γ₀ δ θ k) (gammaSeq_pos_of_criterion hθ0 hθ1 hγ hfix k)
            hθ0 ha).next B
    rw [scalarRungGen_next, taxedOp_apply, gammaSeq_succ]

/-- **THE LADDER'S OPERATORS ARE THE TAXED RECURSION, ON THE NOSE.** This is the identification
between the tower and the gated composition: `Ladder`'s level-`k` operator is multiplication by
`GammaRecursion.gammaSeq γ₀ δ q k`, the same sequence `ComposedCoercivity` iterates. -/
theorem taxedScalarLadder_op_eq_gammaSeq (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - θ ^ 2)) (ha : 0 ≤ a) (k : ℕ) :
    (taxedScalarLadder hθ0 hθ1 hγ hfix ha).op k = mulCLM (gammaSeq γ₀ δ θ k) := rfl

theorem taxedScalarLadder_q (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - θ ^ 2)) (ha : 0 ≤ a) (k : ℕ) :
    ((taxedScalarLadder hθ0 hθ1 hγ hfix ha).rung k).q = θ := rfl

/-- The taxed ladder's correction is NON-ZERO at every level whenever `δ > 0` — it is not the
untaxed ladder in disguise. -/
theorem taxedScalarLadder_dpi_ne_zero (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - θ ^ 2)) (ha : 0 ≤ a) (hδ : 0 < δ) (k : ℕ) :
    (taxedScalarLadder hθ0 hθ1 hγ hfix ha).dpi k ≠ 0 := by
  intro hcon
  have h : (taxedScalarLadder hθ0 hθ1 hγ hfix ha).dpi k 1 = 0 := by rw [hcon]; rfl
  show False
  rw [show (taxedScalarLadder hθ0 hθ1 hγ hfix ha).dpi k 1 = mulCLM δ 1 from rfl,
    mulCLM_apply, mul_one] at h
  linarith

theorem taxedScalarLadder_piBounded (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - θ ^ 2)) (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    (taxedScalarLadder hθ0 hθ1 hγ hfix ha).PiBounded δ := fun _ => taxedDpi_bound hδ

theorem taxedScalarLadder_coercive_zero (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - θ ^ 2)) (ha : 0 ≤ a) :
    CoerciveOn (⇑((taxedScalarLadder hθ0 hθ1 hγ hfix ha).op 0)) γ₀ := by
  intro x
  show γ₀ * ‖x‖ ^ 2 ≤ (inner ℝ x (taxedOp γ₀ δ θ 0 x) : ℝ)
  rw [inner_real, taxedOp_apply, norm_sq_real]
  have h0 : gammaSeq γ₀ δ θ 0 = γ₀ := rfl
  rw [h0]
  exact le_of_eq (by ring)

/-- **THE TAXED TOWER, ITERATED**: the level-`k` constant is `gammaSeq γ₀ δ θ k`, tax paid at every
step against a correction operator that is genuinely there. -/
theorem taxedScalarLadder_coercive (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - θ ^ 2)) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (k : ℕ) :
    CoerciveOn (⇑((taxedScalarLadder hθ0 hθ1 hγ hfix ha).op k)) (gammaSeq γ₀ δ θ k) :=
  (taxedScalarLadder hθ0 hθ1 hγ hfix ha).coercive (taxedScalarLadder_q hθ0 hθ1 hγ hfix ha)
    (taxedScalarLadder_piBounded hθ0 hθ1 hγ hfix ha hδ)
    (taxedScalarLadder_coercive_zero hθ0 hθ1 hγ hfix ha)
    (gammaSeq_pos_of_criterion hθ0 hθ1 hγ hfix) k

/-- **THE `k`-UNIFORM TAXED TOWER, INSTANTIATED.** Every level is `γ₀`-coercive: the tax is paid at
every step and the constant still does not decay. -/
theorem taxedScalarLadder_uniform (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - θ ^ 2)) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (k : ℕ) :
    CoerciveOn (⇑((taxedScalarLadder hθ0 hθ1 hγ hfix ha).op k)) γ₀ :=
  (taxedScalarLadder hθ0 hθ1 hγ hfix ha).coercive_uniform hθ0 hθ1 hγ hfix
    (taxedScalarLadder_q hθ0 hθ1 hγ hfix ha)
    (taxedScalarLadder_piBounded hθ0 hθ1 hγ hfix ha hδ)
    (taxedScalarLadder_coercive_zero hθ0 hθ1 hγ hfix ha) k

/-- **`chain_gamma` APPLIED to the TAXED ladder** — the `δ` that `chain_gamma` carries is now the
two-sided bound on an actual correction operator, not a free slack. -/
theorem taxedScalarLadder_chain_gamma (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - θ ^ 2)) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (k : ℕ) :
    CoerciveOn (⇑((taxedScalarLadder hθ0 hθ1 hγ hfix ha).op k)) (gammaSeq γ₀ δ θ k) :=
  (taxedScalarLadder hθ0 hθ1 hγ hfix ha).coercive_chain_gamma
    (taxedScalarLadder_q hθ0 hθ1 hγ hfix ha)
    (taxedScalarLadder_piBounded hθ0 hθ1 hγ hfix ha hδ)
    (taxedScalarLadder_coercive_zero hθ0 hθ1 hγ hfix ha)
    (gammaSeq_pos_of_criterion hθ0 hθ1 hγ hfix) k

/-- **THE TAXED CONSTANTS ARE ATTAINED AT EVERY LEVEL.** The ladder's level-`k` operator has best
coercivity constant EXACTLY `gammaSeq γ₀ δ θ k`, so the recursion is not a lossy estimate of a
better truth: `(γ_k − δ)/q²` is what the operator actually has. Compare
`GammaRecursion.chain_attains`, which proves the same at `δ = 0`. -/
theorem taxedScalarLadder_sharp (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ₀)
    (hfix : δ ≤ γ₀ * (1 - θ ^ 2)) (ha : 0 ≤ a) (k : ℕ) :
    (∀ B : ℝ, (inner ℝ B ((taxedScalarLadder hθ0 hθ1 hγ hfix ha).op k B) : ℝ)
        = gammaSeq γ₀ δ θ k * ‖B‖ ^ 2)
    ∧ (∀ γ : ℝ, CoerciveOn (⇑((taxedScalarLadder hθ0 hθ1 hγ hfix ha).op k)) γ →
        γ ≤ gammaSeq γ₀ δ θ k) := by
  constructor
  · intro B
    show (inner ℝ B (taxedOp γ₀ δ θ k B) : ℝ) = _
    rw [inner_real, taxedOp_apply, norm_sq_real]
    ring
  · intro γ hγc
    have h := hγc 1
    rw [show (⇑((taxedScalarLadder hθ0 hθ1 hγ hfix ha).op k) : ℝ → ℝ)
        = ⇑(taxedOp γ₀ δ θ k) from rfl] at h
    rw [inner_real, taxedOp_apply] at h
    simp only [norm_one, one_pow, mul_one] at h
    linarith

/-- **MUST-FIRE: THE TAX BITES.** At `δ > 0` the taxed constant at level 1 is STRICTLY below the
untaxed one. The whole cost of item B in one inequality. -/
theorem taxed_lt_untaxed {γ₀ δ θ : ℝ} (hθ0 : 0 < θ) (hδ : 0 < δ) :
    gammaSeq γ₀ δ θ 1 < gammaSeq γ₀ 0 θ 1 := by
  have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
  rw [gammaSeq_succ, gammaSeq_succ]
  simp only [gammaSeq_zero, sub_zero]
  rw [div_lt_div_iff_of_pos_right hθ2]
  linarith

/-- **MUST-NOT-FIRE: AT `δ = 0` THE TAXED AND UNTAXED SEQUENCES COINCIDE AT EVERY LEVEL.** -/
theorem taxed_eq_untaxed_at_zero {γ₀ θ : ℝ} (k : ℕ) :
    gammaSeq γ₀ 0 θ k = γ₀ / θ ^ (2 * k) := gammaSeq_delta_zero k

end TaxedLadder

/-! ## §7c — THE TAXED LADDER AT THE CAMPAIGN'S OWN `(γ₀, δ, q)`

⚠ **READ THIS BEFORE READING THE THEOREMS.** The carrier below is `ℝ`, **not** the su(2) bond
space. What is instantiated is the ARITHMETIC of the criterion, at the three numbers the campaign
actually measured:

* `γ₀ = ComposedCoercivity.gammaFibre = 1/69088` — the level-0 constant the composition has;
* `δ = DeltaPrimeBound.deltaPiConst (24·10⁻¹¹) √768` — the measured (3.120) bound;
* `q = 1/2` — the weighted `Q`-norm at `ell = 2` (`DeltaPrimeBound.weightedQ_two`).

`ComposedCoercivity.criterion_closes_at_gammaFibre` says these satisfy `δ ≤ γ₀(1 − q²)`. The
theorems below say: **at those numbers a `k`-uniform taxed tower EXISTS**, with a non-zero
correction operator at every level and the tax paid at every step. They do **NOT** say the su(2)
lattice tower exists — §10b names the object still missing for that (a strided bond-sector
averaging operator), and no theorem here supplies it. -/

section CampaignLadder

open AdalyFormal.Balaban.ComposedCoercivity (gammaFibre gammaFibre_pos kappaTree
  criterion_closes_at_gammaFibre deltaPiConst_pos_at_used_point)
open AdalyFormal.Balaban.DeltaPrimeBound (deltaPiConst)

/-- The campaign's measured (3.120) bound, named here so every statement below reads as a claim
about THAT number and not about a literal. -/
noncomputable def campaignDelta : ℝ := deltaPiConst (24 * (1 / 10 ^ 11 : ℝ)) kappaTree

theorem campaignDelta_pos : 0 < campaignDelta := deltaPiConst_pos_at_used_point

theorem campaignDelta_criterion : campaignDelta ≤ gammaFibre * (1 - (1 / 2 : ℝ) ^ 2) :=
  criterion_closes_at_gammaFibre

/-- **THE TAXED LADDER AT THE CAMPAIGN'S NUMBERS**, with `a = 1` so the `a`-cancellation of
(3.128)+(3.156) is exercised rather than avoided. -/
noncomputable def campaignTaxedLadder : Ladder (fun _ : ℕ => ℝ) :=
  taxedScalarLadder (γ₀ := gammaFibre) (δ := campaignDelta) (θ := 1 / 2) (a := 1)
    (by norm_num) (by norm_num) gammaFibre_pos campaignDelta_criterion (by norm_num)

/-- The correction operator is NON-ZERO at every level: this ladder genuinely pays the tax. -/
theorem campaignTaxedLadder_dpi_ne_zero (k : ℕ) : campaignTaxedLadder.dpi k ≠ 0 :=
  taxedScalarLadder_dpi_ne_zero (by norm_num) (by norm_num) gammaFibre_pos
    campaignDelta_criterion (by norm_num) campaignDelta_pos k

/-- **EVERY LEVEL IS `gammaFibre`-COERCIVE.** The taxed recursion at the campaign's own
`(γ₀, δ, q)` does not decay. ⚠ On the carrier `ℝ` — see this section's header. -/
theorem campaignTaxedLadder_uniform (k : ℕ) :
    CoerciveOn (⇑(campaignTaxedLadder.op k)) gammaFibre :=
  taxedScalarLadder_uniform (by norm_num) (by norm_num) gammaFibre_pos campaignDelta_criterion
    (by norm_num) campaignDelta_pos.le k

/-- The level-`k` constant in closed form: `gammaSeq gammaFibre campaignDelta (1/2) k`, and it is
ATTAINED. -/
theorem campaignTaxedLadder_sharp (k : ℕ) :
    (∀ B : ℝ, (inner ℝ B (campaignTaxedLadder.op k B) : ℝ)
        = gammaSeq gammaFibre campaignDelta (1 / 2 : ℝ) k * ‖B‖ ^ 2)
    ∧ (∀ γ : ℝ, CoerciveOn (⇑(campaignTaxedLadder.op k)) γ →
        γ ≤ gammaSeq gammaFibre campaignDelta (1 / 2 : ℝ) k) :=
  taxedScalarLadder_sharp (by norm_num) (by norm_num) gammaFibre_pos campaignDelta_criterion
    (by norm_num) k

end CampaignLadder

/-! ## §8 — THE BLOCK-AVERAGE RUNG: a GENUINE DIMENSION DROP `ℝ² → ℝ`

`Q` here is the printed averaging operator of CMP99b p.393's untagged middle line
`(Q'(V)λ)(y) = Σ_{x∈B(y)} L^{-d} R(V(Γ_{y,x})) λ(x)`, equivalently CMP95 p.19 (1.13) at `V = 1`,
specialised to `ell = 2`, `d = 1`, trivial transport: `Q x = 2^{-1}(x₀ + x₁)`. The prefactor is the
printed `L^{-d} = 1/2`, not an arbitrary normalisation — see §9's rescaling control. -/

section BlockWitness

open EuclideanSpace

/-- The `ell = 2`, `d = 1` block average with its printed `L^{-d}` prefactor. -/
noncomputable def blockQ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => (2 : ℝ)⁻¹ * (x 0 + x 1)
      map_add' := by intro x y; simp; ring
      map_smul' := by intro t x; simp; ring }

@[simp] theorem blockQ_apply (x : EuclideanSpace ℝ (Fin 2)) :
    blockQ x = (2 : ℝ)⁻¹ * (x 0 + x 1) := rfl

/-- Its adjoint: spread the coarse value back over the block with the same prefactor. -/
noncomputable def blockQstar : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => (WithLp.toLp 2 (fun _ : Fin 2 => (2 : ℝ)⁻¹ * B))
      map_add' := by intro x y; ext i; simp [WithLp.toLp]; ring
      map_smul' := by intro t x; ext i; simp [WithLp.toLp]; ring }

@[simp] theorem blockQstar_apply (B : ℝ) (i : Fin 2) :
    blockQstar B i = (2 : ℝ)⁻¹ * B := rfl

theorem blockQ_hadj (x : EuclideanSpace ℝ (Fin 2)) (B : ℝ) :
    (inner ℝ (blockQstar B) x : ℝ) = (inner ℝ B (blockQ x) : ℝ) := by
  have hL : (inner ℝ (blockQstar B) x : ℝ)
      = (2 : ℝ)⁻¹ * B * x 0 + (2 : ℝ)⁻¹ * B * x 1 := by
    simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]
    ring
  rw [hL, inner_real, blockQ_apply]
  ring

theorem blockQstar_injective : Function.Injective blockQstar := by
  intro u v huv
  have h := congrFun (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => WithLp.ofLp z) huv) 0
  simp only [blockQstar_apply] at h
  have : (2 : ℝ)⁻¹ ≠ 0 := by norm_num
  exact mul_left_cancel₀ this h

/-- `‖Qx‖ ≤ √(1/2)·‖x‖`, from `(x₀+x₁)² ≤ 2(x₀²+x₁²)`. -/
theorem blockQ_bound (x : EuclideanSpace ℝ (Fin 2)) :
    ‖blockQ x‖ ≤ Real.sqrt (1 / 2) * ‖x‖ := by
  have hnx : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    rw [Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  have hs : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hsnn : (0 : ℝ) ≤ Real.sqrt (1 / 2) := Real.sqrt_nonneg _
  have hsq : ‖blockQ x‖ ^ 2 ≤ (Real.sqrt (1 / 2) * ‖x‖) ^ 2 := by
    rw [mul_pow, hs, blockQ_apply, Real.norm_eq_abs, sq_abs, hnx]
    nlinarith [sq_nonneg (x 0 - x 1)]
  calc ‖blockQ x‖ = Real.sqrt (‖blockQ x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt (1 / 2) * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (1 / 2) * ‖x‖ := Real.sqrt_sq (by positivity)

/-- The block rung at `Δ = c·id`, `P = 0`, `a = 0`. Its coarse carrier is `ℝ`: the dimension
genuinely drops from `2` to `1`, which the scalar witness of §6/§7 does not exhibit. -/
noncomputable def blockRung (c : ℝ) (hc : 0 < c) :
    Rung (EuclideanSpace ℝ (Fin 2)) ℝ (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
    where
  Q := blockQ
  Qstar := blockQstar
  P := 0
  a := 0
  q := Real.sqrt (1 / 2)
  hadj := blockQ_hadj
  ha := le_rfl
  hq := Real.sqrt_pos.2 (by norm_num)
  hQ := blockQ_bound
  hDsym := by
    intro u v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_right, real_inner_smul_left]
  hPsym := by intro u v; simp
  hPpos := by intro x; simp
  hinj := by
    intro u v huv
    rw [fineCLM_apply, fineCLM_apply] at huv
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, add_zero, zero_smul, smul_zero] at huv
    exact smul_right_injective _ (ne_of_gt hc) huv
  hMpos := by
    intro x hx
    rw [fineCLM_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, add_zero, zero_smul, smul_zero, inner_add_right,
      inner_zero_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have : 0 < ‖x‖ ^ 2 := by
      have := norm_pos_iff.2 hx
      positivity
    nlinarith
  hQstarInj := blockQstar_injective

/-- `q² = 1/2` at the block rung — the number the tower law divides by, computed, not posited. -/
theorem blockRung_q_sq (c : ℝ) (hc : 0 < c) : (blockRung c hc).q ^ 2 = 1 / 2 :=
  Real.sq_sqrt (by norm_num)

/-- **`Δ_1 = 2c` on the coarse carrier, computed.** -/
theorem blockRung_next (c : ℝ) (hc : 0 < c) (B : ℝ) :
    (blockRung c hc).next B = (2 * c) * B := by
  have hMinv : ∀ y : EuclideanSpace ℝ (Fin 2),
      (blockRung c hc).G y = c⁻¹ • y := by
    intro y
    have hMN : ∀ x : EuclideanSpace ℝ (Fin 2),
        (blockRung c hc).M ((c⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) x) = x := by
      intro x
      show fineCLM (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) 0 blockQ blockQstar 0
          ((c⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) x) = x
      rw [fineCLM_apply]
      show c • (c⁻¹ • x) + (0 : EuclideanSpace ℝ (Fin 2))
          + (0 : ℝ) • blockQstar (blockQ (c⁻¹ • x)) = x
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul, add_zero, zero_smul, add_zero]
    rw [(blockRung c hc).G_eq (c⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) hMN y]
    rfl
  have hT : ∀ B' : ℝ, (blockRung c hc).T (mulCLM (2 * c) B') = B' := by
    intro B'
    rw [Rung.T_apply, mulCLM_apply]
    show blockQ ((blockRung c hc).G (blockQstar ((2 * c) * B'))) = B'
    rw [hMinv, blockQ_apply]
    have h0 : (c⁻¹ • blockQstar ((2 * c) * B')) 0 = c⁻¹ * ((2 : ℝ)⁻¹ * ((2 * c) * B')) := rfl
    have h1 : (c⁻¹ • blockQstar ((2 * c) * B')) 1 = c⁻¹ * ((2 : ℝ)⁻¹ * ((2 * c) * B')) := rfl
    rw [h0, h1]
    field_simp
    ring
  have hSval : ∀ B' : ℝ, (blockRung c hc).S B' = (2 * c) * B' := by
    intro B'
    rw [(blockRung c hc).S_eq (mulCLM (2 * c)) hT B', mulCLM_apply]
  rw [Rung.next_apply, hSval]
  show (2 * c) * B - (0 : ℝ) • B = _
  rw [zero_smul, sub_zero]

/-- **THE STEP IS SHARP AT THE BLOCK RUNG.** The tower law delivers `γ/q² = 2γ`, and the operator it
delivers is exactly `2c`, whose best coercivity constant is exactly `2c`. So at `Δ = c·id` the
one-step bound loses nothing: it is attained with equality, not merely valid. -/
theorem blockRung_bound_sharp (c : ℝ) (hc : 0 < c) :
    c / (blockRung c hc).q ^ 2 = 2 * c
    ∧ (∀ B : ℝ, (inner ℝ B ((blockRung c hc).next B) : ℝ) = (2 * c) * ‖B‖ ^ 2)
    ∧ (∀ γ : ℝ, CoerciveOn (⇑(blockRung c hc).next) γ → γ ≤ 2 * c) := by
  refine ⟨by rw [blockRung_q_sq]; ring, ?_, ?_⟩
  · intro B
    rw [inner_real, blockRung_next, norm_sq_real]
    ring
  · intro γ hγ
    have h := hγ 1
    rw [inner_real, blockRung_next] at h
    simp only [norm_one, one_pow, mul_one] at h
    linarith

/-- The one-step tower law INSTANTIATED at the block rung: the coarse operator is `(2γ)`-coercive
whenever the fine one is `γ`-coercive. -/
theorem blockRung_tower_law (c : ℝ) (hc : 0 < c) {γ : ℝ} (hγ : 0 < γ)
    (hΔ : CoerciveOn (⇑(c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))) γ) :
    CoerciveOn (⇑(blockRung c hc).next) (2 * γ) := by
  have h := (blockRung c hc).next_coercive hγ hΔ
  rw [blockRung_q_sq] at h
  have hrw : γ / (1 / 2 : ℝ) = 2 * γ := by ring
  rwa [hrw] at h

/-- The first rung's output as an OPERATOR EQUALITY, so it can be fed to a second rung. -/
theorem blockRung_next_eq (c : ℝ) (hc : 0 < c) : (blockRung c hc).next = mulCLM (2 * c) :=
  ContinuousLinearMap.ext fun B => by rw [blockRung_next, mulCLM_apply]

end BlockWitness

/-! ## §8b — THE TWO-STEP COMPOSITE `ℝ² → ℝ → ℝ`

The dispatch's control: compose the one-step map TWICE, with the SECOND rung sitting at the
operator the FIRST rung produced. The first step drops dimension `2 → 1` at the printed block
average; the second is a scalar rung at an arbitrary `θ`. Nothing here is a re-statement of §8: the
level-2 operator is computed from the level-1 operator, which is computed from the level-0 one. -/

section TwoStep

variable (c θ a : ℝ)

/-- The level-2 operator of the composite, computed: `Δ₂ = (2c/θ²)·id`. -/
theorem twoStep_op (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) (B : ℝ) :
    (scalarRung (2 * c) θ a (by linarith) hθ ha).next B = ((2 * c) / θ ^ 2) * B :=
  scalarRung_next (2 * c) θ a (by linarith) hθ ha B

/-- **THE SECOND RUNG SITS AT THE FIRST RUNG'S OUTPUT.** `mulCLM (2c)` is not a fresh choice: it IS
`(blockRung c hc).next`. So `scalarRung (2*c) …` is a rung at the level-1 operator, and the
composite is a genuine two-step ladder. -/
theorem twoStep_tie (hc : 0 < c) : (blockRung c hc).next = mulCLM (2 * c) :=
  blockRung_next_eq c hc

/-- **THE TWO-STEP TOWER LAW.** `γ` at level 0 on `ℝ²` ⟹ `2γ` at level 1 on `ℝ` ⟹ `2γ/θ²` at
level 2. Each arrow is `Rung.next_coercive`; the middle operator is transported across
`twoStep_tie`, not re-chosen. -/
theorem twoStep_coercive (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) {γ : ℝ} (hγ : 0 < γ)
    (hΔ : CoerciveOn (⇑(c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))) γ) :
    CoerciveOn (⇑((blockRung c hc).next)) (2 * γ)
    ∧ CoerciveOn (⇑((scalarRung (2 * c) θ a (by linarith) hθ ha).next)) ((2 * γ) / θ ^ 2) := by
  have h1 : CoerciveOn (⇑((blockRung c hc).next)) (2 * γ) := blockRung_tower_law c hc hγ hΔ
  refine ⟨h1, ?_⟩
  have h2 : CoerciveOn (⇑(mulCLM (2 * c))) (2 * γ) := by
    rw [← twoStep_tie c hc]
    exact h1
  have h3 := (scalarRung (2 * c) θ a (by linarith) hθ ha).next_coercive
    (γ := 2 * γ) (by linarith) h2
  simpa using h3

/-- The composite's own sharpness at `Δ₀ = c·id`: the two-step constant `2c/θ²` is exactly the best
constant of the two-step operator. -/
theorem twoStep_sharp (hc : 0 < c) (hθ : 0 < θ) (ha : 0 ≤ a) :
    (∀ B : ℝ, (inner ℝ B ((scalarRung (2 * c) θ a (by linarith) hθ ha).next B) : ℝ)
        = ((2 * c) / θ ^ 2) * ‖B‖ ^ 2)
    ∧ (∀ γ : ℝ, CoerciveOn (⇑((scalarRung (2 * c) θ a (by linarith) hθ ha).next)) γ →
        γ ≤ (2 * c) / θ ^ 2) := by
  constructor
  · intro B
    rw [inner_real, twoStep_op c θ a hc hθ ha, norm_sq_real]
    ring
  · intro γ hγ
    have h := hγ 1
    rw [inner_real, twoStep_op c θ a hc hθ ha] at h
    simp only [norm_one, one_pow, mul_one] at h
    linarith

end TwoStep

/-! ## §9 — CONTROLS AND THE BINDER AUDIT

Each item here answers one way the construction could be content-free.

**INDEX OF THE ITEM-B CONTROLS** (the `δ` channel), which live next to the objects they control:

| control | says | where |
|---------|------|-------|
| `piCorrectionBound_forces` | `δ` is bounded BELOW by the correction's own diagonal | §4c |
| `piCorrectionBound_nonneg` | the two-sided bound forces `δ ≥ 0` unaided | §4c |
| `stepsHet_delta_is_free` | the CONVICTED channel's `δ` is satisfied by every `δ ≥ 0` | §4c |
| `taxedDpi_no_smaller` | at `Δ′_π = δ·id`, no `δ' < δ` is admissible | §7b |
| `corrected_rung_moves_operator` | MUST-FIRE: at `ε > 0` the corrected step lands strictly lower | §6b |
| `corrected_rung_eq_at_zero_correction` | MUST-NOT-FIRE: at `ε = 0` the two steps coincide exactly | §6b |
| `corrected_rung_bound_sharp` | the taxed constant is ATTAINED — the tax is exact, not slack | §6b |
| `taxed_lt_untaxed` | MUST-FIRE at the sequence level: `δ > 0` strictly lowers `γ₁` | §7b |
| `taxed_eq_untaxed_at_zero` | MUST-NOT-FIRE: at `δ = 0` the sequences agree at every level | §7b |
| `taxedScalarLadder_dpi_ne_zero` | the taxed ladder's correction is genuinely non-zero | §7b |
| `deltaPiConst_zero` | the tax vanishes exactly when the (3.120) current does | §10bis |
-/

section Controls

/-- **MUST-FIRE 1: the step is not the identity.** At `θ ≠ 1` the scalar rung moves the operator. -/
theorem step_moves_operator {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ ≠ 1) :
    ∃ B : ℝ, (scalarRung c θ 0 hc hθ le_rfl).next B ≠ mulCLM c B := by
  refine ⟨1, ?_⟩
  rw [scalarRung_next, mulCLM_apply, mul_one, mul_one]
  intro hcon
  have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
  have h1 : c = c * θ ^ 2 := (div_eq_iff (ne_of_gt hθ2)).1 hcon
  have h2 : (1 : ℝ) = θ ^ 2 :=
    mul_left_cancel₀ (ne_of_gt hc) (show c * 1 = c * θ ^ 2 by linarith)
  have h3 : (θ - 1) * (θ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 h3 with h | h
  · exact hθ1 (by linarith)
  · linarith

/-- **MUST-FIRE 2: the `a`-term is load-bearing INSIDE the step.** Dropping the `−a·I` subtraction
changes the coarse operator whenever `a > 0` — so the cancellation proved in
`scalarRung_next_independent_of_a` is a real cancellation of two present terms, not the absence of
both. -/
theorem a_term_is_load_bearing {c θ a : ℝ} (hc : 0 < c) (hθ : 0 < θ) (ha : 0 < a) :
    (scalarRung c θ a hc hθ ha.le).S 1 ≠ (scalarRung c θ a hc hθ ha.le).next 1 := by
  rw [scalarRung_S, scalarRung_next, mul_one, mul_one]
  intro hcon
  have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
  have key : (c + a * θ ^ 2) / θ ^ 2 - a = c / θ ^ 2 := aCancel hθ2
  rw [hcon] at key
  linarith

/-- **MUST-NOT-FIRE: the block average's prefactor is not free.** The printed prefactor is
`L^{-d} = 1/2`. Replacing it by `1` (a "sum" instead of an "average") changes `q²` from `1/2` to
`2`, hence the tower law's factor from `×2` to `×(1/2)` — the OPPOSITE direction. So the
normalisation this module takes from the source decides the sign of the RG flow of the constant,
and no rescaling is inert here. -/
theorem prefactor_decides_flow_direction :
    (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 ∧ (Real.sqrt 2) ^ 2 = 2
    ∧ (1 : ℝ) / (1 / 2) = 2 ∧ (1 : ℝ) / 2 ≠ 2 := by
  refine ⟨Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num), by norm_num, by norm_num⟩

/-- **BINDER AUDIT: the ladder's `law` really pins `op (k+1)`.** Two ladders on the same carriers
with the same rung data have the same operators at every level. There is no free choice above level
`0` — which is exactly what a vacuous `k`-quantifier would have. -/
theorem ladder_determined {E : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)]
    [∀ k, InnerProductSpace ℝ (E k)] [∀ k, FiniteDimensional ℝ (E k)]
    (Lad : Ladder E) (k : ℕ) :
    Lad.op (k + 1) = (Lad.rung k).next := Lad.law k

/-- **BINDER AUDIT: the ladder's carriers may be trivial, and then it says nothing.** Disclosed, not
hidden: `Ladder` on zero-dimensional carriers is inhabited and its coercivity conclusion is empty.
The witnesses of §7/§8 are what make the structure non-vacuous, and this states the contrast. -/
theorem trivial_carrier_makes_coercivity_empty
    (Δ : (⊥ : Submodule ℝ ℝ) →L[ℝ] (⊥ : Submodule ℝ ℝ)) (γ : ℝ) :
    CoerciveOn (⇑Δ) γ := by
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  simp

end Controls

/-! ## §10 — THE FIRST RUNG AT THE su(2) LATTICE, BUILT

`Rung (BondFnL2 L) (CoarseFnL2 L ell) Δ` is not merely "reachable": it is CONSTRUCTED below from
the tree's own lattice data. The `Q`-side fields (`hadj`, `hQ`, `hq`, `hQstarInj`) are theorems
already in the tree.

⚠ **ITEM D OF `compute/tower_prosecution/VERDICT.md` — THE HYPOTHESIS COUNT, STATED HONESTLY.**
~~"Every field is a theorem already in the tree except `hDP` … So this module adds no new
assumption on the lattice side; it packages what is there into a rung."~~ **STRUCK: false as a
statement about the argument list.** `latticeRung` takes **NINE** Prop-valued hypotheses:

| # | hypothesis | about |
|---|------------|-------|
| 1 | `hell : 0 < ell` | the block side |
| 2 | `hdvd : ∀ μ, ell ∣ (L μ + 1)` | the block side vs the torus |
| 3 | `hwide : ∀ μ, 2 * ell ≤ L μ + 1` | the block side vs the torus |
| 4 | `hDsym` | the CALLER-SUPPLIED `Δ` |
| 5 | `hPsym` | the CALLER-SUPPLIED `P` |
| 6 | `hPpos` | the CALLER-SUPPLIED `P` |
| 7 | `hγ : 0 < γ` | the constant |
| 8 | `ha : 0 ≤ a` | the constant |
| 9 | `hDP` | the genuine (3.10)-level mathematics CMP99b defers |

Eight of the nine are beyond `hDP`. Items 4–6 are independent facts about operators this module
never instantiates: **no application of `latticeRung` to a concrete campaign operator (e.g.
`deltaKTowerCLM`, `deltaKQuadFormCorrected`) appears anywhere in this file.** The "one surviving
hypothesis" framing is inherited from `BridgeInverseControls.lean:83`, which says it of the FINE
OPERATOR only; dropping that qualifier was this module's own amplification, and it is withdrawn.

⚠ **AND `Q` IS PINNED AT `trivialU`.** `Q := qCLM (trivialU L) ell`, because `hQstarInj` needs
surjectivity of `Q` and `BridgeInverseCarrier.qCLM_surjective_trivialU` is the only such theorem —
its own docstring calls itself *"the ONLY statement in this module that uses `trivialU`"*. This is
a restriction to the FLAT background on the `Q` side, and it is stated here at summary level, not
only in-line. -/

section LatticeRung

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration
  PeriodicLatticeSite)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.GeneralUHodgeDrift (siteEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.DeltaPrimeBound (deltaPiConst deltaPrimePiForm abs_inner_le_of_piForm)

variable {L : PeriodicLatticeExtent}

/-- **`piOp` IS `RecursiveBridge.piExtendedMap`.** The corrected rung of §4b consumes the same
(3.120) object the honest bridge chain (`bridge_from_piExtended_normalized_threeTen`) consumes;
this is the identification, on the campaign carrier, and it is definitional. -/
theorem piOp_eq_piExtendedMap (Δ Dpi : BondFnL2 L →L[ℝ] BondFnL2 L) (x : BondFnL2 L) :
    piOp Δ Dpi x = piExtendedMap (⇑Δ) (⇑Dpi) x := rfl

/-- **THE LEVEL-ZERO RUNG AT THE REAL LATTICE `Q`.** `Q := qCLM (trivialU L) ell`,
`Qstar := qstarCLM (trivialU L) ell`, `q := ‖qCLM (trivialU L) ell‖`; `hadj`, `hQ`, `hq`,
`hQstarInj` are the tree's `qCLM_hadj`, `qCLM_le`, `qCLM_norm_pos`,
`qstar_injective_of_surjective ∘ qCLM_surjective_trivialU`.

⚠ **NINE hypotheses** (`hell`, `hdvd`, `hwide`, `hDsym`, `hPsym`, `hPpos`, `hγ`, `ha`, `hDP`),
eight of them beyond `hDP`; `Q` pinned at `trivialU`. See the table in §10's header.

⚠ **This is the UNCORRECTED rung** — its index operator is the raw `Δ`, so it is CMP99b (3.128)
only at a background where `Δ′_π = 0`. The corrected rung is `latticeRungPi` below. -/
noncomputable def latticeRung {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (Δ P : BondFnL2 L →L[ℝ] BondFnL2 L) (a γ : ℝ)
    (hDsym : ∀ u v : BondFnL2 L, (inner ℝ u (Δ v) : ℝ) = (inner ℝ (Δ u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hγ : 0 < γ) (ha : 0 ≤ a)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (P x) : ℝ)) :
    Rung (BondFnL2 L) (CoarseFnL2 L ell) Δ where
  Q := qCLM (trivialU L) ell
  Qstar := qstarCLM (trivialU L) ell
  P := P
  a := a
  q := ‖qCLM (trivialU L) ell‖
  hadj := qCLM_hadj (trivialU L) ell
  ha := ha
  hq := qCLM_norm_pos hell hdvd hwide _
  hQ := qCLM_le (trivialU L) ell
  hDsym := hDsym
  hPsym := hPsym
  hPpos := hPpos
  hinj := fineCLM_injective Δ P _ _ a γ (qCLM_hadj (trivialU L) ell) hγ ha hDP
  hMpos := by
    intro x hx
    have h := fineCLM_coercive Δ P (qCLM (trivialU L) ell) (qstarCLM (trivialU L) ell) a γ
      (qCLM_hadj (trivialU L) ell) hDP x
    have h1 : 0 < γ * ‖x‖ ^ 2 := by
      have : 0 < ‖x‖ := norm_pos_iff.2 hx
      positivity
    have h2 : (0 : ℝ) ≤ a * ‖qCLM (trivialU L) ell x‖ ^ 2 := by positivity
    linarith
  hQstarInj :=
    qstar_injective_of_surjective _ _ (qCLM_hadj (trivialU L) ell)
      (qCLM_surjective_trivialU hell hdvd)

/-- **THE UNTAXED ONE-STEP TOWER LAW AT THE su(2) LATTICE.** The coarse operator
`Δ₁ = (Q G₁ Q*)⁻¹ − a·I` on `CoarseFnL2 L ell` is `(γ/‖Q‖²)`-coercive whenever the GAUGE-FIXED fine
operator `Δ + P` is `γ`-coercive on `BondFnL2 L`.

⚠ **THIS IS THE `Δ′_π = 0` READING** (item B). The constant `γ/‖Q‖²` is honest only where CMP99b
(3.120)'s correction vanishes; at a general background the honest constant is `(γ−δ)/‖Q‖²`, which
is `latticeRungPi_tower_law` below. Nothing here is wrong — it is narrower than it looks, and this
is the notice.

This theorem adds no hypothesis to `latticeRung`'s own NINE (see §10's table): the `hDP` that
builds the rung is exactly the hypothesis the conclusion consumes. In particular it does NOT ask
for coercivity of `Δ` alone, which
`BridgeInverseControls.h310_unrestricted_impossible_at_witnessU` refutes at `witnessU`. -/
theorem latticeRung_tower_law {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (Δ P : BondFnL2 L →L[ℝ] BondFnL2 L) (a γ : ℝ)
    (hDsym : ∀ u v : BondFnL2 L, (inner ℝ u (Δ v) : ℝ) = (inner ℝ (Δ u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hγ : 0 < γ) (ha : 0 ≤ a)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (P x) : ℝ)) :
    CoerciveOn
      (⇑(latticeRung hell hdvd hwide Δ P a γ hDsym hPsym hPpos hγ ha hDP).next)
      (γ / ‖qCLM (trivialU L) ell‖ ^ 2) :=
  (latticeRung hell hdvd hwide Δ P a γ hDsym hPsym hPpos hγ ha hDP).next_coercive_gf hγ hDP

/-! ### §10bis — THE CORRECTED LATTICE RUNG, AND THE `δ` TAX AT THE LATTICE

This is item B's repair on the lattice side. The rung's index operator is `piOp Δ Dpi = Δ − Δ′_π`,
so `Rung.M` is CMP99b (3.128)'s `Δ_π + P + Q*aQ`, and the transported constant is `(γ−δ)/‖Q‖²`. -/

/-- **THE CORRECTED LEVEL-ZERO RUNG AT THE su(2) LATTICE.** Same `Q`-side data as `latticeRung`
(hence the same `trivialU` restriction on `Q`), but sitting at `Δ_π = Δ − Δ′_π`.

⚠ **ELEVEN Prop-valued hypotheses**, counted one by one: `hell`, `hdvd`, `hwide` (geometry),
`hDsym`, `hPiSym`, `hPsym`, `hPpos` (the four caller-supplied operators), `hγδ : 0 < γ − δ`, `ha`
(constants), `hpi` (the two-sided bound on `Δ′_π`), `hDP` (the (3.10)-level coercivity). Two more
than `latticeRung`'s nine, and the two extra are exactly the price of the correction. `hDsym`, `hPiSym`, `hPsym`, `hPpos` are facts about CALLER-SUPPLIED
operators and are not proved here for any concrete campaign operator. -/
noncomputable def latticeRungPi {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (Δ Dpi P : BondFnL2 L →L[ℝ] BondFnL2 L) (a γ δ : ℝ)
    (hDsym : ∀ u v : BondFnL2 L, (inner ℝ u (Δ v) : ℝ) = (inner ℝ (Δ u) v : ℝ))
    (hPiSym : ∀ u v : BondFnL2 L, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hγδ : 0 < γ - δ) (ha : 0 ≤ a)
    (hpi : PiCorrectionBound Dpi δ)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (P x) : ℝ)) :
    Rung (BondFnL2 L) (CoarseFnL2 L ell) (piOp Δ Dpi) where
  Q := qCLM (trivialU L) ell
  Qstar := qstarCLM (trivialU L) ell
  P := P
  a := a
  q := ‖qCLM (trivialU L) ell‖
  hadj := qCLM_hadj (trivialU L) ell
  ha := ha
  hq := qCLM_norm_pos hell hdvd hwide _
  hQ := qCLM_le (trivialU L) ell
  hDsym := piOp_symm Δ Dpi hDsym hPiSym
  hPsym := hPsym
  hPpos := hPpos
  hinj := fineCLM_injective (piOp Δ Dpi) P _ _ a (γ - δ) (qCLM_hadj (trivialU L) ell) hγδ ha
    (gf_pi_of_gf Δ Dpi P γ δ hpi hDP)
  hMpos := by
    intro x hx
    have h := fineCLM_coercive (piOp Δ Dpi) P (qCLM (trivialU L) ell)
      (qstarCLM (trivialU L) ell) a (γ - δ) (qCLM_hadj (trivialU L) ell)
      (gf_pi_of_gf Δ Dpi P γ δ hpi hDP) x
    have h1 : 0 < (γ - δ) * ‖x‖ ^ 2 := by
      have : 0 < ‖x‖ := norm_pos_iff.2 hx
      positivity
    have h2 : (0 : ℝ) ≤ a * ‖qCLM (trivialU L) ell x‖ ^ 2 := by positivity
    linarith
  hQstarInj :=
    qstar_injective_of_surjective _ _ (qCLM_hadj (trivialU L) ell)
      (qCLM_surjective_trivialU hell hdvd)

/-- **THE TAXED ONE-STEP TOWER LAW AT THE su(2) LATTICE.** The coarse operator produced from
CMP99b (3.128)'s `Δ_π + P + Q*aQ` is `((γ−δ)/‖Q‖²)`-coercive, with `γ` the (3.10)-level constant of
the UNCORRECTED `Δ + P` and `δ` the two-sided bound on (3.120)'s `Δ′_π`.

`(γ−δ)/q²` is the constant `RecursiveBridge.lean:1158-1161` names as the honest price of `Δ_π ≠ Δ`.
The `a` of (3.16) still cancels and does not appear. -/
theorem latticeRungPi_tower_law {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (Δ Dpi P : BondFnL2 L →L[ℝ] BondFnL2 L) (a γ δ : ℝ)
    (hDsym : ∀ u v : BondFnL2 L, (inner ℝ u (Δ v) : ℝ) = (inner ℝ (Δ u) v : ℝ))
    (hPiSym : ∀ u v : BondFnL2 L, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hγδ : 0 < γ - δ) (ha : 0 ≤ a)
    (hpi : PiCorrectionBound Dpi δ)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (P x) : ℝ)) :
    CoerciveOn
      (⇑(latticeRungPi hell hdvd hwide Δ Dpi P a γ δ hDsym hPiSym hPsym hPpos hγδ ha hpi
          hDP).next)
      ((γ - δ) / ‖qCLM (trivialU L) ell‖ ^ 2) :=
  (latticeRungPi hell hdvd hwide Δ Dpi P a γ δ hDsym hPiSym hPsym hPpos hγδ ha hpi
    hDP).nextPi_coercive_gf hγδ hDP hpi

/-- **`hpi` DISCHARGED AT (3.120)'s OWN FORM.** Any bundled operator whose diagonal is
`DeltaPrimeBound.deltaPrimePiForm` satisfies the two-sided bound at
`δ = deltaPiConst Jsup κ = Jsup·κ·(28+48κ)` — this is `DeltaPrimeBound.abs_inner_le_of_piForm`,
reused, not re-proved. So the `δ` slot of the taxed law is filled by a THEOREM of this tree at the
lattice, not by a free parameter. -/
theorem piCorrectionBound_of_piForm
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (Lam : (Bond L → SuTwo) → PeriodicLatticeSite L → SuTwo)
    (Dpi : BondFnL2 L →L[ℝ] BondFnL2 L) (Jsup kappa : ℝ)
    (hT : ∀ A : Bond L → SuTwo,
      (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (Dpi (WithLp.toLp 2 A)) : ℝ)
        = deltaPrimePiForm U J (Lam A) A)
    (hJ : ∀ b, frobNorm (J b) ≤ Jsup) (hk0 : 0 ≤ kappa)
    (hlam : ∀ A : Bond L → SuTwo, siteEnergy (Lam A) ≤ kappa ^ 2 * bondEnergy A) :
    PiCorrectionBound Dpi (deltaPiConst Jsup kappa) :=
  fun x => abs_inner_le_of_piForm U J Lam (⇑Dpi) Jsup kappa hT hJ hk0 hlam x

/-- **THE TAXED LATTICE TOWER LAW AT THE TREE'S OWN `δ`.** Same as `latticeRungPi_tower_law` with
the `hpi` slot filled by `piCorrectionBound_of_piForm`: the transported constant is
`(γ − Jsup·κ·(28+48κ))/‖Q‖²`, every ingredient a theorem of this tree except the (3.10)-level `hDP`
that CMP99b defers. -/
theorem latticeRungPi_tower_law_at_deltaPiConst {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (Lam : (Bond L → SuTwo) → PeriodicLatticeSite L → SuTwo)
    (Δ Dpi P : BondFnL2 L →L[ℝ] BondFnL2 L) (a γ Jsup kappa : ℝ)
    (hDsym : ∀ u v : BondFnL2 L, (inner ℝ u (Δ v) : ℝ) = (inner ℝ (Δ u) v : ℝ))
    (hPiSym : ∀ u v : BondFnL2 L, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    (hPsym : ∀ u v : BondFnL2 L, (inner ℝ u (P v) : ℝ) = (inner ℝ (P u) v : ℝ))
    (hPpos : ∀ x : BondFnL2 L, (0 : ℝ) ≤ (inner ℝ x (P x) : ℝ))
    (hγδ : 0 < γ - deltaPiConst Jsup kappa) (ha : 0 ≤ a)
    (hT : ∀ A : Bond L → SuTwo,
      (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (Dpi (WithLp.toLp 2 A)) : ℝ)
        = deltaPrimePiForm U J (Lam A) A)
    (hJ : ∀ b, frobNorm (J b) ≤ Jsup) (hk0 : 0 ≤ kappa)
    (hlam : ∀ A : Bond L → SuTwo, siteEnergy (Lam A) ≤ kappa ^ 2 * bondEnergy A)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (P x) : ℝ)) :
    CoerciveOn
      (⇑(latticeRungPi hell hdvd hwide Δ Dpi P a γ (deltaPiConst Jsup kappa) hDsym hPiSym hPsym
          hPpos hγδ ha (piCorrectionBound_of_piForm U J Lam Dpi Jsup kappa hT hJ hk0 hlam)
          hDP).next)
      ((γ - deltaPiConst Jsup kappa) / ‖qCLM (trivialU L) ell‖ ^ 2) :=
  latticeRungPi_tower_law hell hdvd hwide Δ Dpi P a γ (deltaPiConst Jsup kappa) hDsym hPiSym
    hPsym hPpos hγδ ha (piCorrectionBound_of_piForm U J Lam Dpi Jsup kappa hT hJ hk0 hlam) hDP

/-- **THE FLAT END, WIRED TO THE SOURCE OF THE TAX.** `deltaPiConst 0 κ = 0`: if the (3.120) current
`J` vanishes identically then `Jsup = 0` is admissible, the measured bound is `0`, and the untaxed
constant `γ/q²` is exactly right. `JointInstantiation.jointJ_trivialU_eq_zero` (a different module,
NOT imported here) proves `J ≡ 0` at `trivialU`; the arithmetic half is this theorem, and the two
together are what makes "flat = untaxed" a fact rather than a hope. -/
theorem deltaPiConst_zero (kappa : ℝ) : deltaPiConst 0 kappa = 0 := by
  unfold AdalyFormal.Balaban.DeltaPrimeBound.deltaPiConst
  ring

/-- **AN ANTI-JUNK CONSTRAINT ON THE `hT` INTERFACE.** `hT` is not a free label: it forces the
supplied `Δ′_π` to inherit (3.120)'s own structural zero. `Δ′_π` vanishes identically when its
gauge parameter `λ = G′RD*A` does (`DeltaPrimeBound.deltaPrimePiForm_eq_zero_of_lam_zero`: every
term of (3.120) carries a `λ` factor), so any operator whose diagonal IS that form must vanish on
the gauge slice too. An operator that is nonzero there cannot satisfy `hT`, whatever its bound.

⚠ **AND THIS IS WHY `hT` IS A HYPOTHESIS AND NOT A CONSTRUCTION.** The tree carries (3.120) as a
FORM (`deltaPrimePiForm`), not as a bundled operator, and this module cannot promote it: the form
is `Σ_b Re tr(piBondValue U λ A b · J b)` where `piBondValue`'s third term
(`iComm (λ b.1) (gradValueCovariant U λ b)`) carries NO `A` at all. It is therefore quadratic in
`(λ, A)` jointly, and a Riesz promotion in `A` exists only once `Λ : A ↦ λ` is known LINEAR — which
the tree's `Lam` binder does not assume. That construction (polarisation + `bilinToOperatorBond`,
the route `AxialCoercivity` already takes for `pAx`) belongs in `DeltaPrimeBound`, which is outside
this lane's write scope. NAMED, with its blocking condition, not merely deferred. -/
theorem piForm_interface_vanishes_on_gauge_slice
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (Lam : (Bond L → SuTwo) → PeriodicLatticeSite L → SuTwo)
    (Dpi : BondFnL2 L →L[ℝ] BondFnL2 L)
    (hT : ∀ A : Bond L → SuTwo,
      (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (Dpi (WithLp.toLp 2 A)) : ℝ)
        = deltaPrimePiForm U J (Lam A) A)
    (A : Bond L → SuTwo) (hlam : Lam A = fun _ => 0) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (Dpi (WithLp.toLp 2 A)) : ℝ) = 0 := by
  rw [hT A, hlam]
  exact AdalyFormal.Balaban.DeltaPrimeBound.deltaPrimePiForm_eq_zero_of_lam_zero U J A

/-- The same, transported: a correction operator whose (3.120) current vanishes carries NO tax. -/
theorem piCorrectionBound_zero_of_zero_current
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (J : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (Lam : (Bond L → SuTwo) → PeriodicLatticeSite L → SuTwo)
    (Dpi : BondFnL2 L →L[ℝ] BondFnL2 L) (kappa : ℝ)
    (hT : ∀ A : Bond L → SuTwo,
      (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (Dpi (WithLp.toLp 2 A)) : ℝ)
        = deltaPrimePiForm U J (Lam A) A)
    (hJ : ∀ b, frobNorm (J b) ≤ 0) (hk0 : 0 ≤ kappa)
    (hlam : ∀ A : Bond L → SuTwo, siteEnergy (Lam A) ≤ kappa ^ 2 * bondEnergy A) :
    PiCorrectionBound Dpi 0 := by
  have h := piCorrectionBound_of_piForm U J Lam Dpi 0 kappa hT hJ hk0 hlam
  rwa [deltaPiConst_zero] at h

/-! ### §10d — THE RUNG AT THE TREE'S OWN OPERATORS (the other half of item D)

The prosecution observed, correctly, that **no application of `latticeRung` to a concrete campaign
operator appeared anywhere in the file**, so the four operator-side hypotheses were carried but
never discharged by anything. They are discharged here, at the tree's own objects:

* `Δ := DeltaPrimeOperator.deltaKCLMNormalized U` — the normalized (3.10) operator, the same one
  `RecursiveBridge.bridge_from_piExtended_normalized_threeTen` instantiates; `hDsym` is
  `deltaKCLMNormalized_symm`.
* `P := AxialCoercivity.pAxCLM S ell` — CMP95 (1.10)'s axial gauge-fixing form as an operator, with
  `⟨A, P A⟩ = pAx A S ell` on the nose (`inner_pAxCLM_eq`); `hPsym`/`hPpos` are `pAxCLM_symm` and
  `pAxCLM_pos`.

**Hypothesis count for `latticeRungAtDeltaK`: SIX** — `hell`, `hdvd`, `hwide` (lattice geometry),
`hγ`, `ha` (constants), `hDP` (the (3.10)-level mathematics CMP99b defers). **ZERO of them are
about caller-supplied operators.** That is the honest form of the claim item D withdrew, and it is
true of this declaration and not of `latticeRung` itself. -/

open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized deltaKCLMNormalized_symm
  deltaPrimeCLMNormalized)
open AdalyFormal.Balaban.CStarDeltaKCOperator (dstarDCLM)
open AdalyFormal.Balaban.AxialCoercivity (pAxCLM pAxCLM_symm pAxCLM_pos)

/-- ⚠ **A DENOTATION GUARD, NOT A CONVENIENCE.** `Δ′_source` (`deltaPrimeCLMNormalized`) is a
SUMMAND of the (3.10) operator — this identity is definitional. It is therefore **NOT** the
(3.120) correction `Δ′_π`, and a `piOp (deltaKCLMNormalized U) (deltaPrimeCLMNormalized U)` would
subtract a term that the (3.10) coercivity constant `γ` has ALREADY accounted for: a double count,
not a tax.

The tree's `DeltaPrimeBound.abs_inner_deltaPrimeCLMNormalized_le` (`δ = 272·α₀`) bounds this
operator, and it is tempting to plug that discharged bound into the `hpi` slot. **Do not.** The
`hpi` slot wants `Δ′_π`, whose bound is `deltaPiConst Jsup κ` and whose diagonal is
`deltaPrimePiForm` — that is what `piCorrectionBound_of_piForm` demands via `hT`. -/
theorem deltaPrimeSource_is_a_summand_of_deltaK
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x : BondFnL2 L) :
    deltaKCLMNormalized U x = dstarDCLM U x + deltaPrimeCLMNormalized U x := rfl

/-- **THE RUNG AT `deltaKCLMNormalized U` AND `pAxCLM S ell`.** Six hypotheses, none about a
caller-supplied operator. -/
noncomputable def latticeRungAtDeltaK {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (S : Finset (PeriodicLatticeSite L)) (a γ : ℝ) (hγ : 0 < γ) (ha : 0 ≤ a)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (deltaKCLMNormalized U x) : ℝ)
        + (inner ℝ x (pAxCLM S ell x) : ℝ)) :
    Rung (BondFnL2 L) (CoarseFnL2 L ell) (deltaKCLMNormalized U) :=
  latticeRung hell hdvd hwide (deltaKCLMNormalized U) (pAxCLM S ell) a γ
    (fun u v => (deltaKCLMNormalized_symm U u v).symm) (pAxCLM_symm S ell) (pAxCLM_pos S ell)
    hγ ha hDP

/-- The untaxed tower law at the tree's own operators. ⚠ Honest only where `Δ′_π = 0`. -/
theorem latticeRungAtDeltaK_tower_law {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (S : Finset (PeriodicLatticeSite L)) (a γ : ℝ) (hγ : 0 < γ) (ha : 0 ≤ a)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (deltaKCLMNormalized U x) : ℝ)
        + (inner ℝ x (pAxCLM S ell x) : ℝ)) :
    CoerciveOn (⇑(latticeRungAtDeltaK hell hdvd hwide U S a γ hγ ha hDP).next)
      (γ / ‖qCLM (trivialU L) ell‖ ^ 2) :=
  latticeRung_tower_law hell hdvd hwide (deltaKCLMNormalized U) (pAxCLM S ell) a γ
    (fun u v => (deltaKCLMNormalized_symm U u v).symm) (pAxCLM_symm S ell) (pAxCLM_pos S ell)
    hγ ha hDP

/-- **THE CORRECTED RUNG AT THE TREE'S OWN OPERATORS.** `Δ_π = deltaKCLMNormalized U − Δ′_π`, with
`Δ′_π` the only operator still supplied by the caller — necessarily so: the tree carries no bundled
`Δ′_π`, only its FORM `DeltaPrimeBound.deltaPrimePiForm`, and `piCorrectionBound_of_piForm`'s `hT`
is exactly the demand that the supplied operator's diagonal BE that form.

**EIGHT Prop-valued hypotheses**, counted one by one: `hell`, `hdvd`, `hwide` (geometry),
`hγδ`, `ha` (constants), `hPiSym` (the ONE remaining caller-supplied operator), `hpi`, `hDP`.
Three fewer than `latticeRungPi`'s eleven, and the operator-side count drops from four to one. -/
noncomputable def latticeRungPiAtDeltaK {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dpi : BondFnL2 L →L[ℝ] BondFnL2 L)
    (S : Finset (PeriodicLatticeSite L)) (a γ δ : ℝ) (hγδ : 0 < γ - δ) (ha : 0 ≤ a)
    (hPiSym : ∀ u v : BondFnL2 L, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    (hpi : PiCorrectionBound Dpi δ)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (deltaKCLMNormalized U x) : ℝ)
        + (inner ℝ x (pAxCLM S ell x) : ℝ)) :
    Rung (BondFnL2 L) (CoarseFnL2 L ell) (piOp (deltaKCLMNormalized U) Dpi) :=
  latticeRungPi hell hdvd hwide (deltaKCLMNormalized U) Dpi (pAxCLM S ell) a γ δ
    (fun u v => (deltaKCLMNormalized_symm U u v).symm) hPiSym (pAxCLM_symm S ell)
    (pAxCLM_pos S ell) hγδ ha hpi hDP

/-- **THE TAXED TOWER LAW AT THE TREE'S OWN OPERATORS.** `(γ−δ)/‖Q‖²` from (3.10)'s `γ` and
(3.120)'s `δ`, at `Δ = deltaKCLMNormalized U`, `P = pAxCLM S ell`. -/
theorem latticeRungPiAtDeltaK_tower_law {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hwide : ∀ μ : Fin 3, 2 * ell ≤ L μ + 1)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dpi : BondFnL2 L →L[ℝ] BondFnL2 L)
    (S : Finset (PeriodicLatticeSite L)) (a γ δ : ℝ) (hγδ : 0 < γ - δ) (ha : 0 ≤ a)
    (hPiSym : ∀ u v : BondFnL2 L, (inner ℝ u (Dpi v) : ℝ) = (inner ℝ (Dpi u) v : ℝ))
    (hpi : PiCorrectionBound Dpi δ)
    (hDP : ∀ x : BondFnL2 L,
      γ * ‖x‖ ^ 2 ≤ (inner ℝ x (deltaKCLMNormalized U x) : ℝ)
        + (inner ℝ x (pAxCLM S ell x) : ℝ)) :
    CoerciveOn
      (⇑(latticeRungPiAtDeltaK hell hdvd hwide U Dpi S a γ δ hγδ ha hPiSym hpi hDP).next)
      ((γ - δ) / ‖qCLM (trivialU L) ell‖ ^ 2) :=
  latticeRungPi_tower_law hell hdvd hwide (deltaKCLMNormalized U) Dpi (pAxCLM S ell) a γ δ
    (fun u v => (deltaKCLMNormalized_symm U u v).symm) hPiSym (pAxCLM_symm S ell)
    (pAxCLM_pos S ell) hγδ ha hpi hDP

/-! ### §10e — ⚠ THE `a`-WEIGHT ADJUDICATION, AND THE WALL IT EXPOSES AT `hDP`

**THE QUESTION.** `Rung` carries one `a`: the weight inside `M = Δ_π + P + Q*aQ` (CMP99b (3.128))
and the constant subtracted in `next = S − a·I` ((3.156)). May those two be DIFFERENT numbers —
`M` at `a₂ + c`, subtraction at `a₂`? If yes, `ExtentUniformCoercivity.M_coercive_with_slack`
supplies the primitive's hypothesis at the lattice with an `L`-free constant and the tower
composes. If no, the primitive's hypothesis is the un-augmented two-term bound, which that module
REFUTES at the tree's own operators.

**THE ANSWER: NO — THE WEIGHTS MUST COINCIDE, AND THIS IS FORCED BY THE SOURCE'S OWN DERIVATION,
NOT BY A CHOICE OF NOTATION.** Three adjudicated displays, quoted verbatim from the corpus:

* `corpus/pages/CMP99b_p427.md` (adjudicated), **(3.155)** — the Gaussian integral (3.156) is read
  off:
  `e^{(1/2)⟨g,C^{(k)}(Λ)g⟩} = (Z^{(k)}(Λ))⁻¹ ∫ dB↾_Λ δ(Q₁B)δ_Ax(B)
   · exp[−½⟨H₁B, G₁⁻¹H₁B⟩ + ½a⟨B,B⟩ + ⟨H₁D̃^{(2)}(B), J⟩ + ⟨B,g⟩]`
* `corpus/pages/CMP99b_p421.md` (adjudicated), **(3.129)**: `H₁B = G₁Q*(QG₁Q*)⁻¹B`, hence
  `Q H₁ B = (QG₁Q*)(QG₁Q*)⁻¹B = B`.
* `corpus/pages/CMP99b_p421.md` (adjudicated), **(3.128)**:
  `⟨A, G₁⁻¹A⟩ = ⟨A, Δ_π A⟩ − 2⟨HC_π^{(2)}(A),J⟩ + ‖RD*A‖² + a‖QA‖²`.

Put them together. Evaluate (3.128) at `A = H₁B`. Its last term is `a‖Q H₁ B‖² = a‖B‖²` — a
constant on the constraint surface, by (3.129). **That is exactly what (3.155)'s `+½a⟨B,B⟩` is
there to cancel**, and it is why (3.156) reads `⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ … = ⟨B,Δ_kB⟩`. The
subtracted constant is not an independent parameter: it is (3.128)'s augmentation weight,
evaluated on `QA = B`. Give them different values and the cancellation leaves a residual
`(a_M − a_sub)‖B‖²` inside `Δ_k`, i.e. (3.156) then defines a DIFFERENT operator.
`ConstantA.usedAt_const` ((3.16), p.393) additionally fixes that one `a` across scales — but
⚠ `corpus/pages/CMP99b_p393.md` is `single-read`, not adjudicated, so that sentence is
SUPPLEMENTARY and the ruling above does not depend on it. **The ruling rests only on
`corpus/pages/CMP99b_p421.md` and `corpus/pages/CMP99b_p427.md`, both `adjudicated`**, and it would
stand verbatim even if (3.16) turned out to license a `j`-dependent `a_j`: the cancellation argument
is between (3.128) and (3.155) AT ONE SCALE, and it forces the weight and the subtraction at THAT
scale to be the same number.

**WHAT THAT COSTS, COMPUTED, NOT ASSERTED.** `Rung.shifted_subtraction_costs` (§4b″) proves the
shifted route produces `Δ_{k+1} + c·I`, so converting to the source's `Δ_{k+1}` costs `−c`; and
`Rung.shifted_route_yields_nothing` proves that at the tree's own numbers
(`c = ExtentUniformCoercivity.cExt > 1024`, transported constant `≤ 4/13264896 < 10⁻⁶`) that
subtraction is negative by more than three orders of magnitude. **The shifted route is statable,
true, and transports nothing about the source's operator.**

**THE WALL, STATED LOUDLY.** With the weights equal, the whole-space hypothesis of
`next_coercive_gf` — and hence the `hDP` slot of `latticeRungAtDeltaK` and
`latticeRungPiAtDeltaK` — is `ExtentUniformCoercivity.un_augmented_coercivity_false`'s refuted
statement at the tree's own flat instance. It is therefore **UNSATISFIABLE**, and those two
definitions are **VACUOUS** at `U := trivialU L`, `S := CoarseLattice L 2`, `ell := 2` — the
instance they were built for. That is proved immediately below rather than left as a remark.

**WHAT IS NOT WALLED, AND IS THE ROUTE.** The whole-space demand is THIS CAMPAIGN'S, not CMP99b's:
(3.156) is stated on a subspace (p.428, quoted at §10bis), and `RecursiveBridge.bridge_bare`
evaluates its coercivity hypothesis ONLY at points `G(Q*C)`. §4b′'s
`Rung.next_coercive_gf_on_range` / `nextPi_coercive_gf_on_range` carry the same conclusions from
that strictly weaker hypothesis. The refutation below does **not** touch them: its witness is
`ExtentUniformCoercivity.liftedAxisField suTwoWitness`, and nothing in this tree places that
vector in `range(G ∘ Q*)`. **That is the open question a lattice consumer must now answer, and it
is a different question from the one that was just refuted.** -/

/-- **`latticeRungAtDeltaK`'s `hDP` SLOT IS REFUTED AT THE TREE'S OWN FLAT INSTANCE.** This is
`ExtentUniformCoercivity.un_augmented_coercivity_false`, re-stated in the exact shape this module's
own `latticeRungAtDeltaK hell hdvd hwide (trivialU L) (CoarseLattice L 2) a γ …` demands. So that
definition has NO inhabitant there, for any `γ > 0`, at any admissible extent.

It is compiled here, against this module's own binder, so that the vacuity cannot be discovered
later by a prosecutor: it is disclosed by the module that carries the defect. -/
theorem latticeRungAtDeltaK_hDP_refuted_at_trivialU
    (hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) {γ : ℝ} (hγ : 0 < γ) :
    ¬ (∀ x : BondFnL2 L, γ * ‖x‖ ^ 2
        ≤ (inner ℝ x (deltaKCLMNormalized (trivialU L) x) : ℝ)
          + (inner ℝ x (pAxCLM (AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice L 2) 2 x)
              : ℝ)) :=
  AdalyFormal.Balaban.ExtentUniformCoercivity.un_augmented_coercivity_false hdvd2 hγ

/-- **AND THE DEFECT ROUTE CANNOT RESCUE IT EITHER.** `Rung.gf_of_defect` turns a
`γ₀‖x‖² ≤ ⟨x,Δx⟩+⟨x,Px⟩+C‖Qx‖²` bound into the gauge-fixed hypothesis at `γ₀ − Cq²`. At the tree's
own operators that number is `≤ 0` — `ExtentUniformCoercivity.gf_of_defect_yields_nothing_here`,
re-exported here so the two halves of the wall sit together. The rung needs `0 < γ`, so this route
supplies nothing. -/
theorem gf_of_defect_gives_no_positive_constant_here
    (hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1)) :
    (1 / 13264896 : ℝ) - (13583253568 / 13264896 : ℝ) * ‖qCLM (trivialU L) 2‖ ^ 2 ≤ 0 :=
  AdalyFormal.Balaban.ExtentUniformCoercivity.gf_of_defect_yields_nothing_here hdvd2

/-! ### §10c — WHERE THE LATTICE'S OWN COERCIVITY SITS RELATIVE TO `hDP`

`FibreAggregate.aggregate_fibre_bound_gamma` proves `γ_agg·bondEnergy A ≤ ⟨A,Δ_kA⟩ + P_Ax(A)` with
`γ_agg = 1/3316224` **on the fibre `{Q A = 0}`**, not on the whole space. `hDP` is a whole-space
statement. The gap between them is exactly one step, and it is recorded here rather than papered:

* `Rung.gf_of_defect` above converts a POINCARÉ-WITH-DEFECT bound
  `γ₀‖x‖² ≤ ⟨x,Δx⟩+⟨x,Px⟩+C‖Qx‖²` into `hDP` at `γ = γ₀ − Cq²`. A fibre bound is the `C = ∞` end of
  that family, so a fibre bound alone does not supply `hDP`.
* In FINITE dimension a defect bound with `C = 1` DOES follow from the kernel condition
  `ker(Δ+P) ∩ ker Q = 0` plus `Δ+P ≥ 0` — this is `defect_from_kernel` below, obtained from the
  tree's `BridgeInverse.exists_coercive_of_kernel_trivial` (reused, not re-proved).
* **But the `γ₀` it produces is not explicit and carries no dependence on the lattice extent.** It
  comes from compactness of the unit sphere, so it is a constant per lattice, with no uniformity in
  `L`. A `k`-uniform tower needs an EXTENT-UNIFORM `γ₀`, and that is not supplied by this route. -/

/-- **A defect bound from the kernel condition, in finite dimension.** Reuses
`BridgeInverse.exists_coercive_of_kernel_trivial` at `a = 1`; the identity
`⟨x,fineCLM Δ P Q Q* 1 x⟩ = ⟨x,Δx⟩+⟨x,Px⟩+‖Qx‖²` is `fineCLM_inner`.

⚠ `γ₀` here is EXISTENTIAL and non-explicit — it is produced by a compactness argument on the unit
sphere. It is therefore a constant *for one lattice*, and this theorem supplies no uniformity in
the lattice extent. Stated so it cannot be mistaken for one. -/
theorem defect_from_kernel {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [Nontrivial H] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (Δ P : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qstar : K →L[ℝ] H)
    (hadj : ∀ (x : H) (B : K), (inner ℝ (Qstar B) x : ℝ) = (inner ℝ B (Q x) : ℝ))
    (hDPpos : ∀ x : H, (0 : ℝ) ≤ (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (P x) : ℝ))
    (hker : ∀ x : H,
      (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (P x) : ℝ) = 0 → Q x = 0 → x = 0) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ x : H,
      γ₀ * ‖x‖ ^ 2 ≤ (inner ℝ x (Δ x) : ℝ) + (inner ℝ x (P x) : ℝ) + 1 * ‖Q x‖ ^ 2 := by
  obtain ⟨γ₀, hγ₀, h⟩ :=
    exists_coercive_of_kernel_trivial Δ P Q Qstar 1 hadj one_pos hDPpos hker
  refine ⟨γ₀, hγ₀, fun x => ?_⟩
  have hx := h x
  rwa [fineCLM_inner Δ P Q Qstar 1 hadj x] at hx

end LatticeRung

/-! ## §10b — WHAT IS STILL MISSING FOR A FULL su(2) LATTICE LADDER

§10 builds the FIRST rung. **The second rung is not buildable here**, and the missing object is
definite:

> a bond-sector one-step averaging operator between two CONSECUTIVE coarse levels,
> `Q^{(s)} : CoarseFnL2 L s →L[ℝ] CoarseFnL2 L (s * ell)`,
> i.e. `lineCoarseRestrictCov` with a stride.

What the tree has instead:
* `LineIntegralCovariant.lineCoarseRestrictCov U ell` — this operator at stride `1` only (fine
  lattice in, level-one coarse lattice out);
* `QjComposite.stepAverage s U ell` — exactly the strided one-step average, but in the **SITE**
  sector (acting on the gauge parameter `λ`), with `stepBlockOf y s ell` as its index set and
  `coarsePathHolonomy` as its transport;
* `DeltaKSuTwoCarrier.deltaKTowerCLM ell k` — the level-`k` operator in CLOSED form (stride `ell^k`
  in one shot), which is the composite's *value*, not a rung.

So the missing primitive is the BOND-sector twin of `QjComposite.stepAverage`: the same
`stepBlockOf`/`coarsePathHolonomy` data applied to a bond field. That is a construction task with no
identified obstruction — it is named here because this module does not carry it, not because it is
believed hard.
-/

/-! ## §11 — AXIOM AUDIT: every declaration in this module.

The list is generated mechanically from the file's own declaration headers by
`compute/tower_repair/gen_axiom_list.py`, so it cannot silently fall behind the code:
173 declarations, 173 prints. -/

#print axioms piOp
#print axioms piOp_apply
#print axioms piOp_zero
#print axioms piOp_symm
#print axioms PiCorrectionBound
#print axioms piOp_coercive
#print axioms piCorrectionBound_zero
#print axioms gf_pi_of_gf
#print axioms Rung
#print axioms Rung.M
#print axioms Rung.G
#print axioms Rung.S
#print axioms Rung.next
#print axioms Rung.next_apply
#print axioms Rung.next_eq_coarse156
#print axioms Rung.inner_next
#print axioms Rung.M_G_right
#print axioms Rung.G_M_left
#print axioms Rung.M_sym
#print axioms Rung.coarse_S
#print axioms Rung.T
#print axioms Rung.T_apply
#print axioms Rung.T_S
#print axioms Rung.T_injective
#print axioms Rung.G_eq
#print axioms Rung.S_eq
#print axioms Rung.GaugeFixedCoercive
#print axioms Rung.gf_of_coercive
#print axioms Rung.next_coercive_gf
#print axioms Rung.next_coercive
#print axioms Rung.gf_of_defect
#print axioms Rung.StepsHet
#print axioms Rung.stepsHet
#print axioms Rung.StepsHetGF
#print axioms Rung.stepsHetGF
#print axioms Rung.M_apply_pi
#print axioms Rung.gf_of_pi
#print axioms Rung.nextPi_coercive_gf
#print axioms Rung.nextPi_coercive
#print axioms Rung.nextPi_coercive_gf_at_zero
#print axioms Rung.StepsPi
#print axioms Rung.stepsPi
#print axioms Rung.next_coercive_gf_on_range
#print axioms Rung.nextPi_coercive_gf_on_range
#print axioms Rung.StepsPiGF
#print axioms Rung.stepsPiGF
#print axioms Rung.shifted_subtraction_costs
#print axioms Rung.shifted_route_yields_nothing
#print axioms piCorrectionBound_forces
#print axioms piCorrectionBound_nonneg
#print axioms stepsHet_delta_is_free
#print axioms Ladder
#print axioms Ladder.op_succ
#print axioms Ladder.PiBounded
#print axioms coerciveOn_mono
#print axioms Ladder.coercive
#print axioms Ladder.GF
#print axioms Ladder.coercive_gf
#print axioms Ladder.coercive_succ_gf
#print axioms Ladder.coercive_geom
#print axioms Ladder.stepsWith_const
#print axioms Ladder.coercive_chain_gamma
#print axioms gammaSeq_pos_of_criterion
#print axioms Ladder.coercive_uniform
#print axioms mulCLM
#print axioms mulCLM_apply
#print axioms mulCLM_injective
#print axioms inner_real
#print axioms norm_sq_real
#print axioms invOfInjective_eq
#print axioms scalarGen_M_apply
#print axioms scalarGen_M_injective
#print axioms scalarRungGen
#print axioms scalar_M_apply
#print axioms scalar_M_injective
#print axioms scalarRung
#print axioms scalarRung_q
#print axioms scalarRung_Q
#print axioms scalarRung_Qstar
#print axioms scalarRung_a_eq
#print axioms scalarRungGen_G
#print axioms scalarRungGen_T
#print axioms scalarRungGen_S
#print axioms scalarRung_G
#print axioms scalarRung_T
#print axioms scalarRung_S
#print axioms aCancel
#print axioms scalarRungGen_next
#print axioms scalarRung_next
#print axioms scalarRung_next_independent_of_a
#print axioms scalarRungPi
#print axioms scalarRungPi_next
#print axioms corrected_rung_moves_operator
#print axioms corrected_rung_eq_at_zero_correction
#print axioms corrected_rung_bound_sharp
#print axioms corrected_rung_tower_law
#print axioms scalarOp
#print axioms scalarOp_apply
#print axioms scalarOp_pos
#print axioms scalarOp_piOp_zero_apply
#print axioms scalarLadder
#print axioms scalarLadder_q
#print axioms scalarLadder_piBounded
#print axioms scalarLadder_carrier_nontrivial
#print axioms scalarOp_half_value
#print axioms scalarLadder_k_dependent
#print axioms scalarLadder_coercive_zero
#print axioms scalarLadder_coercive
#print axioms scalarLadder_chain_gamma
#print axioms taxedOp
#print axioms taxedOp_apply
#print axioms taxedOp_piOp_apply
#print axioms taxedDpi_bound
#print axioms taxedDpi_no_smaller
#print axioms taxedScalarLadder
#print axioms taxedScalarLadder_op_eq_gammaSeq
#print axioms taxedScalarLadder_q
#print axioms taxedScalarLadder_dpi_ne_zero
#print axioms taxedScalarLadder_piBounded
#print axioms taxedScalarLadder_coercive_zero
#print axioms taxedScalarLadder_coercive
#print axioms taxedScalarLadder_uniform
#print axioms taxedScalarLadder_chain_gamma
#print axioms taxedScalarLadder_sharp
#print axioms taxed_lt_untaxed
#print axioms taxed_eq_untaxed_at_zero
#print axioms campaignDelta
#print axioms campaignDelta_pos
#print axioms campaignDelta_criterion
#print axioms campaignTaxedLadder
#print axioms campaignTaxedLadder_dpi_ne_zero
#print axioms campaignTaxedLadder_uniform
#print axioms campaignTaxedLadder_sharp
#print axioms blockQ
#print axioms blockQ_apply
#print axioms blockQstar
#print axioms blockQstar_apply
#print axioms blockQ_hadj
#print axioms blockQstar_injective
#print axioms blockQ_bound
#print axioms blockRung
#print axioms blockRung_q_sq
#print axioms blockRung_next
#print axioms blockRung_bound_sharp
#print axioms blockRung_tower_law
#print axioms blockRung_next_eq
#print axioms twoStep_op
#print axioms twoStep_tie
#print axioms twoStep_coercive
#print axioms twoStep_sharp
#print axioms step_moves_operator
#print axioms a_term_is_load_bearing
#print axioms prefactor_decides_flow_direction
#print axioms ladder_determined
#print axioms trivial_carrier_makes_coercivity_empty
#print axioms piOp_eq_piExtendedMap
#print axioms latticeRung
#print axioms latticeRung_tower_law
#print axioms latticeRungPi
#print axioms latticeRungPi_tower_law
#print axioms piCorrectionBound_of_piForm
#print axioms latticeRungPi_tower_law_at_deltaPiConst
#print axioms deltaPiConst_zero
#print axioms piForm_interface_vanishes_on_gauge_slice
#print axioms piCorrectionBound_zero_of_zero_current
#print axioms deltaPrimeSource_is_a_summand_of_deltaK
#print axioms latticeRungAtDeltaK
#print axioms latticeRungAtDeltaK_tower_law
#print axioms latticeRungPiAtDeltaK
#print axioms latticeRungPiAtDeltaK_tower_law
#print axioms latticeRungAtDeltaK_hDP_refuted_at_trivialU
#print axioms gf_of_defect_gives_no_positive_constant_here
#print axioms defect_from_kernel

end AdalyFormal.Balaban.TowerOneStep
