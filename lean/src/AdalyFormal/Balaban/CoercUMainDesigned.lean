/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.GeneralEllAssembly
import AdalyFormal.Balaban.FullReparamC
import AdalyFormal.Balaban.SpineCoercivityInstance
import AdalyFormal.Balaban.IslandBridge
import AdalyFormal.Balaban.CoercUMainRegular
-- §2a cites `Balaban/RegularityGap.lean` by declaration name for the settled class comparison.
-- A citation of a module this file does not import is a citation of nothing checkable, so the
-- import is here. It adds no proof-term dependency: `#print axioms` on every declaration in this
-- file and in `Spine.lean` is bit-identical before and after this line
-- (`compute/regularity_propagate/axioms_diff.txt`, 3737 records, 0 differences).
import AdalyFormal.Balaban.RegularityGap

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `CoercUMainDesigned.lean` — one-scale coercivity in p.428's SHAPE, on p.392's OBJECT

Additive module. Nothing outside this file is edited. **This file does not touch
`Spine.coerc_u_main`.**

## §00 — WHAT THIS FILE ESTABLISHES, AND WHAT IT DOES NOT (read this before §1)

**Corrected 2026-07-30 after three prosecutions (Claude, Sol, Kimi) convicted this file's prose.**
The mathematics below was not convicted; every theorem here is proved and axiom-clean. Three
sentences of the old header, and one row of the §2 clause table, were false. They are struck in
place and replaced. Do not restore them.

**Every claim below is tagged `[THEOREM]` (a named declaration in this file establishes it) or
`[ASSESSMENT]` (a reading of the source or of definitions; NO theorem in this tree establishes it,
and it may not be cited as if one did). The tagging is the repair: the three convicted sentences
were
all assessments written in the grammar of theorems.**

**The honest headline.** `[THEOREM]` (`p428Coercivity_holds`) A PROVED coercivity theorem for the
tree's normalized CMP99b **p.392 eq. (3.10)** one-scale quadratic form `D*_U D_U + Δ′(U)`, on the
whole periodic torus, after the `C`-reparametrization onto the `Λ̃` variables, under the smallness
hypothesis `GaugeRegular (alphaEll ell)`; plus `[THEOREM]` (§6) proofs that selected PSD junk
families fail its quadratic-form denotation predicate. **`GaugeRegular` is NOT the source's
(3.35)/(3.36)**, and **`[ASSESSMENT]` the containment between the two classes is UNSETTLED — in
neither direction.** §2a, and read §2a before quoting this headline.

~~and is not known to be comparable with it in either direction~~ ~~**STRUCK 2026-07-30, false; the
comparison was done and it is `[THEOREM]` (`Balaban/RegularityGap.lean`).** The two classes are
**WIDER-OR-INCOMPARABLE**: proved incomparable, and in the small-`O(1)Mα₀` regime CMP99b itself
demands the realized direction is **WIDE** — this file's hypothesis admits backgrounds on which
p.428 asserts nothing.~~
**BOTH THE ORIGINAL SENTENCE AND ITS 2026-07-30 STRIKE ARE STRUCK, 2026-07-30 (second correction).**
The strike was wrong: the "comparison" it cited compares `GaugeRegular` against a tree-local
COORDINATEWISE PROXY, not against (3.35)/(3.36). A de-correlated prosecution
(`compute/sol_regularity/SOL_VERDICT.md`, Sol/gpt-5.6-sol) convicted the source-fidelity claim on
three defects, all mechanical, none about the proof terms. The first sentence's cautious wording was
closer to true than what replaced it, and is the operative status again — see §2a.

**It is NOT the statement p.428 makes.** p.428's object is `C*Δ_kC` with `Δ_k` *defined by*
(3.156) out of `(QG₁Q*)⁻¹`, `a`, `H₁`, `D̃⁽²⁾`, `J` and the RG index `k`.

* `[CHECKABLE, mechanically]` **None of those five ingredients occurs in any DECLARATION in this
  file, and neither does the RG recursion.** Grep for `QG₁Q`, `invertQGQstar`, `Dtilde2`: the only
  occurrence in the whole file is the line above, which names them in order to say they are absent.
  That is the intended check. The tree's
  `deltaKQuadFormNormalizedCorrected U A` takes only `(U, A)` and **has no `k` argument at all** —
  read its signature. The `k`-dependence here is supplied by a free, universally quantified `Ladder`
  parameter: a stand-in for the RG flow, not the RG flow.
* `[CHECKABLE]` A (3.156)-shaped recursive object exists elsewhere in this tree
  (`Balaban/DeltaKRecursive.lean`) and is **not** imported or used here.

**What it IS, stated positively — a real result, not a concession — but stated at its evidential
grade.** `[ASSESSMENT]` The coercivity proved here is naturally read as the **general-`U` analogue
of
CMP96 [4] Lemma 2.4 / eq. (2.128)**: a Poincaré-type lower bound on a constrained subspace, for the
LOCAL one-scale fluctuation operator (leading term the covariant Maxwell operator `D*_U D_U`, plus
the plaquette correction `Δ′(U)` — which (2.128) does not have). `[ASSESSMENT]` That is the
input-level mechanism p.428's own sentence invokes — *"We have proved it in [4], Lemma 2.4, for
operators with `U = 1`. **Localizing the operators in `Δ_k`** and using the methods of Sect. B we
can
prove it for `C*Δ_kC` with an arbitrary configuration `U` …"*. Right phenomenon, wrong denotation
for
the billed claim.

**Both of those are ASSESSMENTS and neither is a theorem here.** No declaration in this tree relates
this file's bound to CMP96 (2.128): the constant is not compared (`gammaEll ell = 1/(60·ell⁵)`
versus
(2.128)'s printed `(1/12d²)L^{−d−1}`), the operators are not identified, and (2.128) is not
formalized. Whoever cites the analogy owes that comparison.

**The missing piece is the LOCALIZATION STEP** that reduces `C*Δ_kC ≥ γ₀` to the one-scale form's
coercivity. It is nowhere in this tree, nothing in this file supplies it, and no theorem here may be
cited as evidence for p.428's printed claim.

## §0 — WHY A REDESIGN AND NOT A STRENGTHENING

`Spine.coerc_u_main` occupies the worst position a statement can occupy, and both halves are
kernel-checked elsewhere in this tree:

* **it admits junk** — `CoercUMainKernel.jDelta` (`id + (k + colour U) • P_{single bond}`) satisfies
  all five of its live conjuncts at every lattice, every `ell`, every nontrivial `Uconfig`;
* **it is FALSE of the faithful operator** — `CoercUMainPinned.pinnedConclusion_false_three_ways`
  refutes three of its demands (global PSD, RG-scale dependence, and the `coercive`/`γ''_pos` field
  pair the existential supplies) at a background the tree's regularity predicate accepts at its
  tightest threshold, on a nonzero vector of the very subspace `(2.121)` names.

Adding conjuncts cannot fix that, and this file does not try. The reason is measured, not asserted:
**the two known junk families are separated by CROSSED conditions.**

| condition set | `CoercUMainKernel.jDelta` (id + decoration) | `CoercUMainKernel.chainDelta` (scaled projector) |
|---|---|---|
| K1 `HasKernel` ∧ K2 `KernelMono` ∧ K3 `KernelGrows` | REJECTED (`jDelta_fails_HasKernel`) | ADMITTED (`kernelStrengthened_of_chain`) |
| K5 `NotScaledProjection` | ADMITTED (`jDelta_satisfies_NotScaledProjection`) | REJECTED (`chainDelta_fails_NotScaledProjection`) |

Each family is content-free, and each escapes the condition set that kills the other. Both are
constraints on the **shape of the operator**. So this file changes axis: it constrains **what the
operator DENOTES**, and it restores **the source's own hypotheses on the background and the
domain**. Those two moves close two DIFFERENT requirements, and §6 proves that neither closes both.

## §1 — WHAT p.428 SAYS, VERBATIM (image-verified, LAW-11)

Render `corpus/renders/CMP99b_p428-40.png`, sha256
`128b1172e7090661d2c2ead70d9514244567c17a43c709ff87b18603b3012d54` — equal to the `render_sha256`
in `corpus/pages/CMP99b_p428.md`, whose `verification_status` is `adjudicated`. Crops used are at
`compute/coercumain_design/renders/`. Four sentences carry the whole claim:

* **[S-SUBSPACE]** "This form is considered on the subspace
  `{B: B=0 on Λᶜ, B=0 on ∪_{y∈Λ'} Ax(y), Q₁B=0}`."
  ⚠ The printed subscript is **`Q₁`**, not `Q_k`. This tree's dispatch notes have called it
  "`Q_k B = 0`"; the page says `Q₁B = 0`, and it is recorded here rather than normalised away.
* **[S-PARAM]** "These are variables `B` restricted to the set of bonds
  `Λ̃ = Λ \ (∪_{y∈Λ'} Ax(y) ∪ ∪_{c∈Λ'} B(c)∩c)`" … "we have `B = CB̃`, where `C` is a linear
  operator. It is an identity operator on almost all bonds, except the bonds `b₀` for which a value
  `(CB̃)(b₀)` is equal to a solution of the equation `(QB)(c) = 0`".
* **[S-BOUND]** "It is more convenient to work with the operator `C̃⁽ᵏ⁾(Λ)`, because it is defined
  by a positive definite operator `C*Δ_kC` with a lower bound `γ₀ > 0` independent of `k` and `U`."
* **[S-HYP]** "We have proved it in [4], Lemma 2.4, for operators with `U = 1`. Localizing the
  operators in `Δ_k` and using the methods of Sect. B we can prove it for `C*Δ_kC` with an
  arbitrary configuration `U` satisfying (3.35), (3.36) with `Mα₀` sufficiently small."

### §1a — what the live statement DROPS (five items, not two)

`CoercUMainPinned` names two. There are five, and the largest is not among the two.

| # | source demand | locator | in `coerc_u_main`? |
|---|---|---|---|
| **D1** | `U` restricted to "(3.35), (3.36) with `Mα₀` sufficiently small" | [S-HYP] | **NO** — no regularity field anywhere in the signature. What THIS file restores in its place is a DIFFERENT condition, `GaugeRegular`, **whose class has NOT been compared with (3.35)/(3.36) in either direction. `[ASSESSMENT]`, and the honest word is UNCOMPARED.** ~~STRUCK 2026-07-30, false — the comparison was done. The classes are **WIDER-OR-INCOMPARABLE**: proved incomparable, with the WIDE direction realized in the small-`O(1)Mα₀` regime the source demands (`RegularityGap.exists_wideness_witness_at_alphaEll` — RETIRED NAME, no longer resolves; now `exists_proxyWideness_witness_at_alphaEll`). So D1 is not merely absent — its substitute reaches PAST it.~~ **THAT STRIKE IS ITSELF STRUCK 2026-07-30 (second correction): what was compared was a tree-local coordinatewise PROXY, not (3.35)/(3.36) — §2a.** |
| **D2** | `Q₁B = 0` in the domain | [S-SUBSPACE] | **NO** — `anchoredVInter` is the axial clause ALONE |
| **D3** | `B = 0` on `Λᶜ` in the domain | [S-SUBSPACE] | **NO** (vacuous once `Λ` is the whole torus — see §5c) |
| **D4** | the object is `C*Δ_kC`, on the `B̃` variables of `Λ̃` | [S-BOUND], [S-PARAM] | **NO** — no reparametrization `C` and no `Λ̃` occur in it at all |
| **D5** | `γ₀` independent of `k` **and** `U` | [S-BOUND] | shape present, but `γ''` sits INSIDE the `∃ Δ`, so the inhabitant chooses it |

### §1b — what the live statement ADDS (three items, none in the source)

| # | live clause | in p.428? | status in this tree |
|---|---|---|---|
| **A1** | global PSD on the WHOLE carrier | **NO** — [S-BOUND]/[S-SUBSPACE] positivity is *on the subspace* | REFUTED (`CoercUMainPinned.pinned_fails_global_psd`) |
| **A2** | non-scalarity `∀ c, Δ ≠ c • id` | **NO** | anti-junk decoration; admits `chainDelta`-shaped families |
| **A3** | RG-scale dependence `∃ k₁ ≠ k₂, Δ k₁ ≠ Δ k₂` | **NO** | REFUTED at every unconditional faithful pin (`CoercUMainPinned` §1b) |

A1 and A3 are exactly the two clauses `CoercUMainPinned` refutes. **They are also exactly two of the
three clauses the source does not ask for.** That is the diagnosis this file is built on: the live
statement is false *because* it over-demands, and junk-inhabited *because* it under-denotes.

## §2 — THE DESIGN, clause by clause

`P428Coercivity L ell` (§5) is:

```
∃ γ₀ : ℝ, 0 < γ₀ ∧
  ∀ (Δ : DeltaFam L) (bg : Ladder L),
    AnchoredLadder bg → RegularityPreserving ell bg → DenotesDeltaK Δ bg →
    ∀ (k : ℕ) (U : LinkCfg L), GaugeRegular (alphaEll ell) U →
      ∀ Btil, OnLambdaTilde ell Btil →
        γ₀ * bondEnergy Btil ≤ sandwichForm Δ ell bg k U Btil
```

| clause | p.428 text it comes from | why it is there |
|---|---|---|
| `∃ γ₀, 0 < γ₀`, **outside every other binder** | [S-BOUND] "a lower bound `γ₀ > 0` independent of `k` and `U`" | D5. Uniform in `k`, in `U`, in the ladder, AND in the realization of `Δ` — strictly more uniform than the source asks |
| `∀ Δ` (universal, NOT `∃ Δ`) | [S-BOUND] "it **is** defined by a positive definite operator `C*Δ_kC`" — a property OF a named object | kills the S91 hole: there is no slot for junk to occupy |
| `DenotesDeltaK Δ bg` | [S-BOUND] the operator is `Δ_k` | the anti-junk clause. §6 proves it rejects both junk families |
| `AnchoredLadder bg` (`bg 0 U = U`) | [S-BOUND] "independent of … `U`" | without it `bg` may never look at `U`, and "independent of `U`" becomes vacuous. Also what makes junk-rejection provable (§6) |
| `RegularityPreserving ell bg` | [S-HYP], **via the same UNCOMPARED substitute as the row below** (~~struck 2026-07-30: the comparison was done, §2a~~ — that strike is itself struck 2026-07-30, second correction; the class comparison is UNSETTLED, §2a) | D1's substitute, propagated along the ladder |
| `GaugeRegular (alphaEll ell) U` | [S-HYP] — ~~same sentence~~ **STRUCK: NOT the same condition.** See the REPRESENTATION GAP note immediately below. | D1's proxy only |

### §2a — THE REPRESENTATION GAP: `GaugeRegular` is NOT (3.35)/(3.36), and the containment is UNSETTLED

**READ THIS PARAGRAPH BEFORE ANY OTHER IN §2a.** Opened by Kimi 2026-07-30 as a gap of unknown
direction. Claimed **SETTLED** the same day, in the direction "`GaugeRegular` is WIDER, so this file
asserts coercivity where p.428 asserts nothing". **THAT SETTLEMENT IS RETRACTED, 2026-07-30**, after
a de-correlated Sol-family prosecution (`compute/sol_regularity/SOL_VERDICT.md`, gpt-5.6-sol xhigh,
against `compute/regularity_gap/` at commit `e19d84eb`) convicted it. **The operative status is the
one this row carried BEFORE the settlement: `GaugeRegular` is a DIFFERENT hypothesis from the
source's, of a different logical shape, and the two classes HAVE NOT BEEN COMPARED — in either
direction.**

**What was convicted, precisely — it is not a technicality.** The settlement's formal predicate is
not a formalization of printed (3.35)/(3.36). Three independent defects, all in the DEFINITION, none
in any proof term:

1. **Wrong operator.** (3.36) bounds `∂^{η*}∂^η A`, where `∂^η` is the lattice EXTERIOR derivative
   (it maps `0`-forms to `1`-forms — CMP95's `A^λ = A − ∂^η λ` — hence `1`-forms to `2`-forms), so
   `∂^{η*}∂^η A` sums plaquette components over `ν`. The predicate used a COORDINATEWISE forward
   second difference instead. These are different operators, not different conventions:
   `Balaban.RegularityGap.coordSecondDiff_ne_extDStarD` kernel-checks a configuration on which every
   coordinatewise second difference vanishes while the exterior operator does not. CMP99a p.99
   prints `|∂^{η*}∂^η A|` and `|Δ^η A|` as SEPARATE quantities in the same display, which is direct
   source evidence that the exterior operator is not a coordinatewise Laplacian.
2. **The printed cube class was dropped**, and the predicate's cube carrier was an unconstrained
   `Finset (Bond L)` with no tie to `j`, `Ω`, `Λ`, `B^j`, block geometry, size or nonemptiness —
   so **the EMPTY `Finset` satisfies every obligation vacuously**, at arbitrary `η`, `L^j`, `c`.
3. **The "source class ⊄ `GaugeRegular`" direction used a SINGLETON cube**, which is not in the
   printed class either, so it did not establish what it was billed as establishing.

A fourth conviction is arithmetic and is corrected below: the numbers quoted for `Mα₀` treated the
printed floor `O(1) ≥ 10` as the equality `O(1) = 10`.

**What SURVIVES the prosecution, and must not be discarded with the overclaim.** The one-bond
curvature witness and the narrowness threshold are `[THEOREM]`, and Sol's verdict on them is
CANNOT REFUTE. Holonomy covariance, conjugation-invariance and the four-link estimate genuinely
supply the conditional curvature floor, and `g = 1` is blocked by the hypotheses. What those
theorems compare `GaugeRegular` against is `Balaban.RegularityGap.CoordProxy3536Log` — a
TREE-LOCAL COORDINATEWISE PROXY, renamed 2026-07-30 from a name that said "3536". The mathematics
is real; the identification of that predicate with the source's condition is what failed.

**Nothing in this file's mathematics moves.** `p428Coercivity_holds` is proved under `GaugeRegular`
and stays proved; the retraction is entirely about what may be SAID about the relation between
`GaugeRegular` and p.428's hypothesis. What it may be said to be is: **uncompared**.

The row above previously read "[S-HYP] same sentence". That was false and is struck.

* **The source's condition is GAUGE-ORBIT LOCAL SMALLNESS.** (3.35)/(3.36), printed on p.396:
  *"for an arbitrary cube `□` of the described above class, and for a configuration `U` there exists
  a gauge transformation `u` on `□` such that `U^u = e^{iηA}`"*, with
  `|A| < O(1)Mα₀(L^jη)⁻¹` and `|∇^ηA| < O(1)Mα₀(L^jη)⁻²` on `□` (3.35), and
  `|∂^{η*}∂^ηA| < O(1)Mα₀(L^jη)⁻³` on `□` (3.36). Three separate things: a **per-cube** gauge
  transformation, an **exponential chart** `U^u = e^{iηA}`, and bounds on `A` **and its first and
  second derivatives**.
* **`GaugeRegular α₀ U` is a single global Frobenius-style bound**:
  `∃ γ, frobSupBond (periodicGaugeTransform γ U) ≤ α₀` (`AlphaAnalyticity.lean`). One global gauge,
  no cube decomposition, no exponential chart, and **no derivative control at all** — neither
  `∇^ηA` nor `∂^{η*}∂^ηA`.
* ~~**Direction of the gap — NOT ESTABLISHED, IN EITHER DIRECTION, and this correction is
  deliberate.** The prosecution that found this gap concluded `GaugeRegular` is a *strictly stronger*
  hypothesis, so the theorem would be merely "narrower in its domain of backgrounds". **This file
  does not adopt that conclusion, because the lane that applied the repair could not establish it
  and the inference it rests on does not go through on a lattice.** The inference was: `GaugeRegular`
  has no derivative control, therefore it cannot reach (3.35)'s `|∇^ηA|` and (3.36)'s
  `|∂^{η*}∂^ηA|`. But `∇^η` here is a finite difference, so a sup bound on `A` DOES control it up to
  the scale factors `η`, `L^j` — and those factors, together with `M` and `α₀`, do not occur
  anywhere in this tree. So the containment turns on a comparison of thresholds that cannot even be
  *stated* in this tree, let alone proved.~~
  ~~**What follows from that, stated plainly because it is the sharper risk.** With no containment
  known in EITHER direction, two things are simultaneously possible and neither is excluded here:
  the theorem may **miss** backgrounds the source's hypothesis admits (narrower, the benign case),
  and it may **cover** backgrounds the source's hypothesis excludes — in which case it asserts
  coercivity where the source claims nothing, which is the *non*-benign case and is not licensed by
  p.428.~~
  ~~**What would settle it:** formalize (3.35)/(3.36) with their scale parameters and prove an
  implication between that predicate and `GaugeRegular (alphaEll ell)`, in whichever direction
  holds. Until then the only defensible statement is the one this table row now makes:
  **`GaugeRegular` is a DIFFERENT hypothesis from the source's, of a different logical shape, and
  their classes have not been compared.**~~

  ~~**ALL THREE BULLETS STRUCK 2026-07-30. THE QUESTION IS SETTLED, IT WAS SETTLABLE IN THIS TREE ALL
  ALONG, AND THE ANSWER IS THE NON-BENIGN ONE.** `Balaban/RegularityGap.lean` — imported by this
  file, zero `sorry`, every declaration `[propext, Classical.choice, Quot.sound]` — did exactly what
  the third bullet asked for: it formalizes (3.35)∧(3.36) with all four of their parameters (`η`,
  `L^j`, `M`, `α₀`) as `RegularityGap.Src3536` (RETIRED NAME, no longer resolves; now
  `CoordProxy3536`), and proves the comparison in both directions. The
  first bullet's stated obstruction was false in both halves, and the second bullet's "two things
  are simultaneously possible" is now one thing that is PROVED.~~

  **THAT PARAGRAPH IS ITSELF STRUCK, 2026-07-30 (second correction), and the reader should now
  apportion the three original bullets as follows — two of the three stand, one does not.**

  * The FIRST bullet's stated obstruction ("cannot even be *stated* in this tree") **remains
    refuted**, and more strongly than before: the ingredients are in the tree (inventory below), the
    scale parameters can be carried explicitly, and `Balaban/RegularityGap.lean` §12-§13 now DOES
    state a faithful predicate with the exterior operator and a cube class
    (`RegularityGap.Src3536Faithful`, `RegularityGap.IsSourceCube`; the latter is a RELAXATION of the
    printed class — `RegularityGap` §16). Statability was never the
    problem.
  * The SECOND bullet — *"two things are simultaneously possible and neither is excluded here"* —
    **stands, and is again the operative statement.** It was struck on the strength of a settlement
    that has been convicted. Nothing since has excluded either possibility for the SOURCE's class.
  * The THIRD bullet's *"what would settle it"* **stands as the open task**, now sharpened by the
    prosecution: the predicate must carry the exterior `∂^{η*}∂^η` (not a coordinatewise second
    difference) AND a cube class that excludes the empty and singleton `Finset`s.

* `[THEOREM]` **`η` CANCELS IDENTICALLY from the coordinatewise proxy. The comparison never depended
  on the lattice spacing.** `RegularityGap.coordProxy3536_eta_free`: for every `η > 0`,
  `CoordProxy3536 η Lj c cube U ↔ CoordProxy3536Log Lj c cube U`, and `η` does not occur in
  `CoordProxy3536Log`. It enters the three bounds as `(L^jη)⁻¹, (L^jη)⁻², (L^jη)⁻³` and enters
  `A, ∇^ηA` and the second-difference clause as exactly `η⁻¹, η⁻², η⁻³` — they cancel clause by
  clause. What survives is `L^j` and the single product `c = O(1)Mα₀`. This is a fact about the
  PROXY. `[ASSESSMENT]` The same cancellation is expected for the faithful predicate on dimensional
  grounds (the exterior stencil carries the same `η⁻²`), and
  `RegularityGap.src3536Faithful_eta_free` proves it — but that theorem is about
  `Src3536Faithful`, and it settles no containment by itself.

* ~~`[THEOREM]` **THE ANSWER: the classes are INCOMPARABLE, and which containment fails is decided by
  the single dimensionless ratio `α·(L^j)³ / c`.**~~ **STRUCK 2026-07-30 (second correction): the
  three rows below are theorems about `CoordProxy3536Log`, NOT about (3.35)∧(3.36). They settle no
  containment against the source. Retained struck, with their true subject substituted, because
  their content is real and was not refuted.**

  | direction | statement (subject corrected to the PROXY) | declaration |
  |---|---|---|
  | narrow | `2π·α < c·(L^j)⁻³` ⟹ `GaugeRegular α ⊆ CoordProxy3536Log`, for EVERY cube — including the empty one, on which the right-hand side is vacuously true | `RegularityGap.coordProxy3536Log_of_gaugeRegular_uncond` |
  | wide | `4·c·(L^j)⁻¹ ≤ α` ⟹ a configuration EXISTS that is `GaugeRegular α` and fails `CoordProxy3536Log` at `cube = univ`, **in every gauge** | `RegularityGap.exists_proxyWideness_witness` |
  | and not the other way either | `CoordProxy3536Log ⊄ GaugeRegular` — but at a SINGLETON cube, which is outside the printed class (defect 3) | `RegularityGap.proxyRegion_witness` |

  The `2π` is composed, not tuned: `π/2` is CMP98 (25)
  (`BlockingLinkEstimate.frobNorm_su2Log_le_pi_div_two`) and `1, 2, 4` count the `log` terms in the
  proxy's three clauses; the binding one is `4·(π/2) = 2π`, from the coordinatewise second
  difference. For the FAITHFUL (3.36) clause the count is not `4`:
  `RegularityGap.src3536FaithfulLog_of_gaugeRegular` carries `24 = 3·2·4` (three directions `ν`, the
  two terms of `∂^{η*}`, the four terms of `∂^η`), so the faithful narrow threshold is
  `12π·α < c·(L^j)⁻³`, not `2π·α < c·(L^j)⁻³`.

* `[THEOREM]` **THE BENIGN DIRECTION IS REPAIRED, AND IT IS THE ONLY ONE THAT IS.**
  `RegularityGap.src3536FaithfulLog_of_gaugeRegular` proves
  `12π·α < c·(L^j)⁻³ ⟹ GaugeRegular α ⊆ Src3536FaithfulLog`, **for EVERY cube** — and a `∀` over
  every `Finset` of bonds covers every printed cube whatever the domain-sequence clauses are. So
  this file's hypothesis being CONTAINED in p.428's is a live possibility that is now supported by
  a theorem about the right operator. The reverse containment is not, and §16 of
  `Balaban/RegularityGap.lean` states exactly what would settle it.

* `[THEOREM]` **NO GAUGE CAN REPAIR THE WIDE WITNESS — that is the mechanism, not a detail.** The
  witness is a single excited bond: `U(b₀) = g`, `U ≡ 1` elsewhere (`RegularityGap.oneBondU`). Its
  plaquette holonomy IS `g` (`RegularityGap.holonomy_oneBondU`); plaquette holonomy is
  gauge-COVARIANT (`NonFlatBackground.holonomyElem_periodicGaugeTransform`); and `‖· − 1‖_F` is
  conjugation-INVARIANT (`BlockingLinkEstimate.frobNorm_conj_sub_one`). Composing them,
  `RegularityGap.curvature_floor` gives `‖U(∂p) − 1‖_F ≤ 4·sup_b ‖U^γ(b) − 1‖_F` for EVERY `γ`.
  Curvature is a floor under the bond sup that no gauge choice gets below, so the source's own
  `∃ u` cannot rescue the witness — which is why the wide direction is provable without knowing
  which gauge an adversary picks.

* `[THEOREM]` **THE WITNESS EXISTS; it is not a hypothesis.**
  `RegularityGap.exists_proxyWideness_witness` builds the group element rather than assuming one:
  `exists_su2_frobNorm_sub_one_eq` realizes every value in `[0, 2√2]` as `‖g − 1‖_F` on the maximal
  torus, and `2√2 = ‖(−1) − 1‖_F` is the exact top of the range. The only lattice hypothesis is
  `1 ≤ L 1` (direction-`1` must admit a genuine shift, or there is no plaquette to carry curvature).
  **Subject correction (2026-07-30):** what it exits is `CoordProxy3536Log`, not (3.35)∧(3.36).
  `RegularityGap.exists_faithfulWideness_witness_onSourceCube` carries the same construction against
  `Src3536FaithfulLog` at a box of the MODELLED cube class `RegularityGap.IsSourceCube` instead of
  at `Finset.univ`, and `RegularityGap.exists_faithfulRegion_witness_onSourceCube` does the same
  for the other direction instead of at a singleton. **Neither settles a containment against the
  source**, and `RegularityGap` §16 says why in a table: `IsSourceCube` is a RELAXATION of the
  printed class (it omits the domain-sequence clauses), while the source's condition is `∀ □ of the
  class` — so a one-box failure inside a superset does not negate the `∀`, and a one-box success
  does not establish it. What IS repaired is the benign direction, below.

* ~~`[THEOREM]` **AND THE WIDE COLUMN IS THE REGIME THE SOURCE ITSELF DEMANDS.** At this file's own
  values — `α = alphaEll ell = 10⁻⁵·ell⁻⁵`, `L^j = ell` — both conditions are pure-number
  comparisons on `c = O(1)Mα₀`:~~ **STRUCK 2026-07-30 (second correction) — CONVICTED, and on two
  independent counts.**

  | | condition on `c = O(1)Mα₀` | at `ell = 2` | declaration |
  |---|---|---|---|
  | narrow | `c > 2π·10⁻⁵·ell⁻²` | `c > 1.5708·10⁻⁵` | `RegularityGap.narrow_condition_at_alphaEll` |
  | wide | `4c ≤ 10⁻⁵·ell⁻⁴` | `c ≤ 1.5625·10⁻⁷` | `RegularityGap.wide_condition_at_alphaEll` |

  **The arithmetic in that table is correct and is retained. The inference drawn from it was not.**
  Two counts:

  1. **Both rows are conditions for the PROXY**, so neither says anything about the source's regime.
  2. **The `O(1) ≥ 10` floor was used as if it were `O(1) = 10`.** It is a lower bound only, and
     inverting it inverts instances. At `O(1) = 100`: `Mα₀ = 1/64,000,000` gives `c = 1/640,000`,
     which is **NOT** in the wide column even though it meets the advertised `Mα₀` upper bound; and
     `Mα₀ = 2·10⁻⁷` gives `c = 2·10⁻⁵`, which **IS** in the narrow column even though it sits below
     the advertised necessary `Mα₀` lower bound. So "sufficiently small `Mα₀` is the wide column"
     does not follow. `[ASSESSMENT]` CMP99b never gives `O(1)Mα₀` a number
     (p.396: *"We will need `α₀` so small that `O(1)Mα₀` is still a sufficiently small number"*), so
     no threshold in this tree can be shown to bracket the source's own choice.

* ~~**WHAT THIS COSTS THE THEOREM, plainly.** `p428Coercivity_holds` is untouched — it is proved under
  `GaugeRegular` and it stays proved. What changes is what may be SAID about it. It may **not** be
  described as p.428's claim restricted to a smaller class of backgrounds; that description is now
  refuted in the source's own small-`c` regime. In that regime this file asserts coercivity on
  backgrounds p.428 claims nothing about, and the assertion on those extra backgrounds is THIS
  TREE'S, carrying no support from p.428. This is not a scope shortfall; it is a scope OVERHANG.~~
  **STRUCK 2026-07-30 (second correction).** `p428Coercivity_holds` is indeed untouched and stays
  proved — that half was never at issue. What is retracted is the rest: no scope OVERHANG has been
  demonstrated against p.428, because the predicate the demonstration ran against is not p.428's
  condition. **The correct statement of cost is the one the file carried before: this file's
  hypothesis is a DIFFERENT hypothesis from p.428's, and it is UNCOMPARED, so this file's coercivity
  result may not be described as p.428's claim at all — neither restricted to a smaller class nor
  extended to a larger one.**

* ~~**The one thing not pinned down, and it does not move the answer.** Between `2π·α < c·(L^j)⁻³` and
  `4c(L^j)⁻¹ ≤ α` lies an undetermined band of exactly `8π·(L^j)²` … so closing the band cannot move
  the conclusion in either direction.~~ **STRUCK 2026-07-30 (second correction): "it does not move
  the answer" presupposed an answer.** The band is real and its width is
  `[THEOREM]`-grade arithmetic (`8π·(L^j)²`, narrowed to `4√2π·(L^j)²` by §11's sharpening), but it
  is a band between two PROXY thresholds. **The thing genuinely not pinned down is now larger: the
  containment itself.**

* `GeneralEllAssembly.lean` describes `GaugeRegular` in its own words, and that description is still
  accurate about `GaugeRegular`: *"`GaugeRegular` is (3.35)'s first clause at the global-cube
  specialization; the cube decomposition (M5), the exponential chart and (3.36) remain proxied."*
  **What is no longer true is the implicature that the proxied clauses could not be STATED.**
  `RegularityGap.Src3536Faithful` carries a cube CLASS (`RegularityGap.IsSourceCube`, which excludes
  the empty and singleton `Finset`s), the exponential chart (as an explicit conjunct
  `su2Exp (su2Log (U^γ b)) = U^γ b`, proved to be the source's `U^u = e^{iηA}` by
  `RegularityGap.chart_equation`) and the exterior (3.36) operator
  (`RegularityGap.extDStarD`). ~~and (3.36)~~ **Correction 2026-07-30 (second): the earlier
  `RegularityGap.Src3536` did NOT carry (3.36) — it carried a coordinatewise second difference and
  an unconstrained `Finset`, and it is renamed `CoordProxy3536`. Statability is settled; the
  COMPARISON is not.** That file's own sentence has not been edited here — it is outside this
  file — and this note is the correction of record.

* **THE INGREDIENTS WERE ALREADY IN THE TREE, AND THIS IS RECORDED SO THE NEXT LANE SEARCHES
  SHORTER.** The struck first bullet asserted the comparison "cannot even be *stated* in this tree".
  Everything it needed was already built and sitting unconnected:

  | ingredient the comparison needs | already in the tree as | built for |
  |---|---|---|
  | `‖log g‖_F ≤ (π/2)·‖g − 1‖_F` — CMP98 (25) | `BlockingLinkEstimate.frobNorm_su2Log_le_pi_div_two` | the blocking estimate |
  | `‖g − 1‖_F ≤ ‖log g‖_F` off the antipode — CMP98 (24) | `BlockingLinkEstimate.frobNorm_sub_one_le_frobNorm_su2Log` | the blocking estimate |
  | `‖g − 1‖_F = 2√2·sin(θ(g)/2)`, exact | `BlockingLinkEstimate.frobNorm_sub_one_eq` | the blocking estimate |
  | conjugation-invariance of `‖· − 1‖_F` | `BlockingLinkEstimate.frobNorm_conj_sub_one` | the blocking estimate |
  | gauge-covariance of plaquette holonomy | `NonFlatBackground.holonomyElem_periodicGaugeTransform` | non-flat backgrounds |
  | `exp : 𝔰𝔲(2) → SU(2)` and its log | `SuTwoLogExpCore.su2Exp` / `su2Log` | the `LogExpAd` instance |

  `BlockingLinkEstimate` carries BOTH chart-comparison inequalities of CMP98 (24)/(25) with explicit
  constants — the exact two-sided bridge between `‖g − 1‖_F` (what `GaugeRegular` measures) and
  `‖log g‖_F` (what (3.35)/(3.36) measure) — and it had **zero importers anywhere in the tree**. The
  only genuinely new lemma the settlement needed was the branch condition
  `RegularityGap.su2_exp_log_of_ne_negOne` (`exp ∘ log = id` off `−1`, via Cayley–Hamilton), and
  even that replaced an assumption rather than adding one. **The claim was not unstatable; it was
  unsearched.** ~~settlement~~ — read "settlement" here as "the proxy comparison"; this inventory
  bullet is about STATABILITY and survives the 2026-07-30 retraction intact.

* **AND THE INGREDIENT THAT WAS MISSING, NAMED.** The inventory above is complete for the FIRST
  clause of (3.35). It is NOT complete for (3.36): nothing in the tree carried the lattice EXTERIOR
  derivative on `1`-forms, which is why the settlement substituted a coordinatewise second
  difference and why that substitution went unnoticed through a build, an axiom audit, an S91 sweep
  and a nested validator. `Balaban/RegularityGap.lean` §12 now carries it
  (`RegularityGap.extD`, `RegularityGap.extDStar`, `RegularityGap.extDStarD`, with the adjoint
  identity `RegularityGap.extD_adjoint` proved rather than asserted, and
  `RegularityGap.coordSecondDiff_ne_extDStarD` kernel-checking that the substituted stencil is a
  DIFFERENT operator, not a different convention). **The lesson recorded for the
  next lane: an operator NAME is not an operator, and no gate in this tree reads a definition.**
| `OnLambdaTilde ell Btil` clause 1 (axial) | [S-SUBSPACE] "`B = 0` on `∪_{y∈Λ'} Ax(y)`" and [S-PARAM]'s `Λ̃ ⊇` removal of `∪Ax(y)` | the one clause the live statement already had |
| `OnLambdaTilde ell Btil` clause 2 (no dropped bonds) | [S-PARAM] `Λ̃` removes `∪_{c∈Λ'} B(c)∩c`, "exactly the one bond `b₀` of `B(c)` contained in `c`" | D4 |
| `sandwichForm` = the form of `Δ_k` at `C B̃` | [S-BOUND] `C*Δ_kC`; [S-PARAM] `B = CB̃` | D4. `⟪B̃, C*Δ_kC B̃⟫ = ⟪CB̃, Δ_k CB̃⟫` is the *definition* of the sandwich, so no adjoint of `C` need be constructed |
| `Q₁B = 0` — **NOT a hypothesis; a THEOREM about `C`** | [S-SUBSPACE] `Q₁B = 0` | D2, and it is *stronger* here than as a hypothesis: `FullReparamC.fullC_unconditional_mem_kerQ` proves `Q₁(C B̃) = 0` for EVERY `B̃`, which is precisely why the source parametrizes by `B̃` at all |

**Deliberately ABSENT, each because the source does not ask for it and the faithful operator refutes
it or is indifferent to it:** global PSD (A1), non-scalarity (A2), RG-scale variation (A3),
and every kernel condition (§7).

## §3 — WHAT IS PROVED HERE, and the four requirements

| requirement | verdict | declaration |
|---|---|---|
| (a) not junk-inhabitable | the denotation clause rejects EVERY family whose form is `≥ 0` at one witness pair — a class containing BOTH junk families | `nonneg_at_central_fails_denotation`, `psdFamily_fails_denotation`, `junkId_fails_denotation`, `idPlusScaledProjector_fails_denotation`, `scaledProjectorFamily_fails_denotation` |
| (b) not refuted by the faithful `Δ_k` | the faithful family INHABITS it, at general `ell ≥ 2`, general tiled `L`, general regular `U`, and every anchored regularity-preserving ladder | `p428Coercivity_holds`, `faithfulFamily_denotes` |
| (c) satisfiable / non-vacuous | `γ₀ = gammaEll ell` witnesses it; the domain `Λ̃` carries a field of strictly positive energy; and the ladder hypotheses do not collapse the `k` index (§7e, read its limits) | `p428Coercivity_holds`, `lambdaTilde_nonvacuous`, `varyingLadder_is_admissible`, `varyingLadder_faithfulFamily_k_dependent` |
| (d) faithful to p.428 | **NO — see §00.** ~~clause table §2; every hypothesis is a printed one, every printed hypothesis is present modulo D3 (§5c)~~ **STRUCK 2026-07-30, false.** Faithful in SHAPE (the `C`-sandwich, the `Λ̃` domain, the `γ₀` uniformity); NOT faithful in OBJECT (p.392 (3.10), not p.428 (3.156)), NOT faithful in HYPOTHESIS (a different condition, **UNCOMPARED — and the direction of the difference is unknown, so this row may understate the problem**; ~~STRUCK 2026-07-30 — the comparison was done and the row DID understate it: the classes are **WIDER-OR-INCOMPARABLE**, and in the source's own small-`O(1)Mα₀` regime the hypothesis is WIDE, so this file asserts coercivity where p.428 asserts nothing~~ **THAT STRIKE IS ITSELF STRUCK 2026-07-30, second correction: what was compared was a coordinatewise proxy, not (3.35)/(3.36) — §2a. The original UNCOMPARED wording is restored as the operative text**, §2a), NOT faithful in REGION (whole torus, §5c) | — |

**And the anatomy, which is the finding**: (a) and (b) are closed by DIFFERENT clauses and
**neither closes both**.

* the source's hypotheses ALONE (regularity + `Λ̃` + the `C` sandwich) still admit the identity —
  `existentialForm_withoutDenotation_holds_by_junk`;
* the denotation clause ALONE says nothing about coercivity.

So the coordinator's conjecture that "a statement whose hypotheses are the source's may exclude both
families for free" is **FALSE as stated, and this file proves it false**. It excludes the FALSITY,
not the junk.

## §4 — CARRIER: this is not on `coerc_u_main`'s carrier, and cannot be

`IslandBridge.no_linearEquiv_euclid_bondFnL2 L : IsEmpty (EuclideanSpace ℝ (Bond L) ≃ₗ[ℝ] BondFnL2 L)`
— for EVERY `L`. `coerc_u_main`'s `H` is `Anchoring.AnchoredBondSpace Lat = EuclideanSpace ℝ (Bond Lat)`
(fibre dimension 1); the faithful `Δ_k`, the faithful `Q₁` (`lineCoarseRestrictCov`), the faithful
`C` (`fullC`) and the coercivity theorem all live on `BondFnL2 L` (`𝔰𝔲(2)` fibre, dimension 3).
There is no adapter and there cannot be one: it is a dimension count, not a missing lemma.

**Consequence for the live declaration, stated as an argument and not a preference (dispatch item
4): `coerc_u_main` should be RETIRED, not restated.** Three independent reasons:

1. Its carrier cannot host the object p.428 is about, and that is a proved obstruction
   (`carrier_obstruction`, re-exported below), not formalization debt. Bałaban's `B` is
   Lie-algebra-valued; a 1-dimensional fibre denotes something else.
2. Two of its five clauses (A1, A3) are refuted of the faithful operator AND absent from the source,
   so no repair of the remaining clauses reaches a true statement about `Δ_k`.
3. Its existential over `Δ` is the S91 hole, and removing it changes the declaration's TYPE, so
   every one of its type-ascription call sites breaks anyway. There is no edit to `coerc_u_main`
   that is smaller than replacing it.

What replaces it is `P428Coercivity` on the `𝔰𝔲(2)` carrier — plus, for the consumers that need
something on `AnchoredBondSpace`, an honest statement that those consumers are consuming a scalar
proxy. That second half is NOT built here and is NOT claimed.
-/

namespace AdalyFormal.Balaban.CoercUMainDesigned

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf staircasePath witnessL)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeRegular gaugeRegular_of_frobSupBond_le)
open AdalyFormal.Balaban.GeneralEllAssembly (alphaEll gammaEll alphaEll_pos gammaEll_pos
  deltaKNormalized_gaugeRegular_coercive_generalEll)
open AdalyFormal.Balaban.FullReparamC (fullC dinvC IsDropped fullC_free freeBond
  freeBond_not_dropped freeBond_not_mem_staircase fullC_unconditional_axialGauge
  fullC_unconditional_mem_kerQ)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.DeltaPrimeOperator (deltaKCLMNormalized inner_deltaKCLMNormalized_eq
  deltaKCLMNormalized_symm)
open AdalyFormal.Balaban.CovariantHj (dstarDQuadForm dstarDQuadForm_nonneg)
open AdalyFormal.Balaban.CoercivityRegular (deltaKQuadFormNormalizedCorrected_eq_sub)
open AdalyFormal.Balaban.IslandBridge (norm_sq_bondFnL2 no_linearEquiv_euclid_bondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUDomainWitness (frobSupBond_trivialU)
open AdalyFormal.Balaban.RegularUDomainWitnessGeneralU (siteZero siteZero_coarse tinyU
  tinyU_ne_trivialU)
open AdalyFormal.Balaban.DeltaPrime (deltaWitnessConfig)
open AdalyFormal.Balaban.RegularityHolonomy (centralHolonomyU)
open AdalyFormal.Balaban.SpineCoercivityInstance (inner_deltaKCLMNormalized_centralHolonomyU)
open AdalyFormal.Balaban.CoercUMainRegular (inner_starProjection_nonneg)

variable {L : PeriodicLatticeExtent}

/-! ## §5 — THE OBJECTS AND THE DESIGNED STATEMENT -/

/-- The gauge-configuration type. -/
abbrev LinkCfg (L : PeriodicLatticeExtent) : Type :=
  PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L

/-- An RG family of operators on the `𝔰𝔲(2)` bond `L²` space — the shape `CoercivityHypothesis.Δ`
demands, at the carrier the faithful operator actually lives on. -/
abbrev DeltaFam (L : PeriodicLatticeExtent) : Type :=
  ℕ → LinkCfg L → (BondFnL2 L →L[ℝ] BondFnL2 L)

/-- A **background ladder**: the configuration each RG rung's `Δ_k` is built at. In Bałaban `Δ_k`
depends on `k` through the accumulated background field; here that dependence is a PARAMETER, not
free data, because the designed statement quantifies over it universally. -/
abbrev Ladder (L : PeriodicLatticeExtent) : Type :=
  ℕ → LinkCfg L → LinkCfg L

/-- **[S-BOUND], "independent of … `U`"**: rung `0` of the ladder is the configuration one is
handed. Without this the ladder need never look at `U` at all, and `U`-independence says nothing. -/
def AnchoredLadder (bg : Ladder L) : Prop := ∀ U : LinkCfg L, bg 0 U = U

/-- **[S-HYP]**, propagated along the ladder: if the input configuration satisfies the source's
regularity restriction, so does every rung's background. -/
def RegularityPreserving (ell : ℕ) (bg : Ladder L) : Prop :=
  ∀ (k : ℕ) (U : LinkCfg L), GaugeRegular (alphaEll ell) U → GaugeRegular (alphaEll ell) (bg k U)

/-- **THE DENOTATION CLAUSE — the anti-junk device.** Rung `k`'s operator IS Bałaban's `Δ_k`, in the
only sense a statement can demand: its quadratic form is the source's `Δ_k` form at that rung's
background. An IDENTITY, hence unconditional in `U` — the regularity restriction constrains the
CONCLUSION's domain, never what the operator denotes. That asymmetry is what makes §6 work. -/
def DenotesDeltaK (Δ : DeltaFam L) (bg : Ladder L) : Prop :=
  ∀ (k : ℕ) (U : LinkCfg L) (A : Bond L → SuTwo),
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (Δ k U (WithLp.toLp 2 A)) : ℝ)
      = deltaKQuadFormNormalizedCorrected (bg k U) A

/-! ### §5a — THE PINNING CONJUNCT (added 2026-07-30; **INERT — read why**)

`DenotesDeltaK` constrains only the real quadratic DIAGONAL, so it does **not** pin the operator:
`DenotesDeltaK Δ bg` holds iff `Δ k U − faithfulFamily bg k U` has vanishing diagonal, and §7a.1
exhibits an explicit **nonzero** such shift (`S0`). Two operators that differ at every rung and
every
configuration can both denote.

**THIS IS NOT A SOUNDNESS FIX, AND IT IS IMPORTANT NOT TO READ IT AS ONE.** The repair is proved
INERT, twice over and in this file:

* `p428Coercivity_iff_unpinned` (§7b) — adding the conjunct changes the statement's truth value by
  **nothing**; the pre-repair statement and the repaired one are equivalent.
* `p428Coercivity_iff_deltaFree` (§7c) — stronger: `Δ` does not occur essentially in
  `P428Coercivity` at all. Every value the statement asserts is a diagonal, so it is equivalent to a
  statement in which the operator variable has been eliminated.

**What the conjunct is FOR is PINNING, and that is the whole payoff**: with it,
`denotesDeltaKPinned_unique` gives **operator equality** `Δ = faithfulFamily bg` — the certification
Sol's verdict 5 recorded as missing — rather than equality of quadratic forms. A later reader who
takes this clause for a plugged hole will have mis-read it: there was no hole; there was an
uncertified identification.

`DenotesDeltaK` itself is deliberately left UNCHANGED. The junk rejections of §6 conclude
`¬ DenotesDeltaK …`, which is strictly sharper than `¬ (DenotesDeltaK ∧ SelfAdjointFam)`; folding
the conjunct into `DenotesDeltaK` would have silently weakened every one of them. §6g bridges. -/

/-- The real quadratic diagonal vanishes identically. Equivalent to skewness of the associated
bilinear form over `ℝ` (`zeroDiag_skew` / `zeroDiag_of_skew`, §7a). -/
def ZeroDiag (S : BondFnL2 L →L[ℝ] BondFnL2 L) : Prop :=
  ∀ A : BondFnL2 L, (inner ℝ A (S A) : ℝ) = 0

/-- Self-adjointness of the whole family, **stated at the FORM level** — `⟪Δx, y⟫ = ⟪x, Δy⟫` — and
deliberately not as `bondAdjoint (Δ k U).toLinearMap = (Δ k U).toLinearMap`: both sides here mention
only ambient instances, so no `letI` enters any type.
(`CStarDeltaKCOperator.bondAdjoint_eq_self_iff` proves the two formulations equivalent, so nothing
is
lost by the weaker-looking spelling.) -/
def SelfAdjointFam (Δ : DeltaFam L) : Prop :=
  ∀ (k : ℕ) (U : LinkCfg L) (x y : BondFnL2 L),
    (inner ℝ (Δ k U x) y : ℝ) = inner ℝ x (Δ k U y)

/-- **THE PINNED DENOTATION CLAUSE.** Denotation plus form-level self-adjointness. By
`denotesDeltaKPinned_unique` this pins the operator UNIQUELY; by `p428Coercivity_iff_unpinned` it
changes nothing the statement asserts. -/
def DenotesDeltaKPinned (Δ : DeltaFam L) (bg : Ladder L) : Prop :=
  DenotesDeltaK Δ bg ∧ SelfAdjointFam Δ

/-- **`Λ̃` — [S-PARAM]'s `Λ̃ = Λ \ (∪_{y∈Λ'} Ax(y) ∪ ∪_{c∈Λ'} B(c)∩c)`, term for term.** Clause 1 is
the removal of the axial staircases `∪Ax(y)`; clause 2 is the removal of the dropped bonds
`∪_{c} B(c)∩c` — "exactly the one bond `b₀` of `B(c)` contained in `c`", which is
`FullReparamC.IsDropped`. `Λ` is the whole (periodic) lattice here, so `Λᶜ = ∅` and D3 is vacuous;
§5c says this explicitly. -/
def OnLambdaTilde (ell : ℕ) (Btil : Bond L → SuTwo) : Prop :=
  (∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell →
      ∀ b ∈ staircasePath y x, Btil b = 0)
  ∧ (∀ b : Bond L, IsDropped ell b → Btil b = 0)

/-- **`C` of (3.157)** — the tree's reparametrization, with the source's own solved value on the
dropped bonds (`FullReparamC`). Named here so the clause table's `C` has a referent. -/
noncomputable def Creparam (U : LinkCfg L) (ell : ℕ) : (Bond L → SuTwo) → (Bond L → SuTwo) :=
  fullC U ell (dinvC U ell)

/-- **`⟪B̃, C*Δ_kC B̃⟫`**, which is by definition of the sandwich `⟪C B̃, Δ_k (C B̃)⟫`. No adjoint of
`C` is constructed, and none is needed: the source's object is a quadratic form. -/
noncomputable def sandwichForm (Δ : DeltaFam L) (ell : ℕ) (bg : Ladder L) (k : ℕ) (U : LinkCfg L)
    (Btil : Bond L → SuTwo) : ℝ :=
  (inner ℝ (WithLp.toLp 2 (Creparam (bg k U) ell Btil) : BondFnL2 L)
    (Δ k U (WithLp.toLp 2 (Creparam (bg k U) ell Btil))) : ℝ)

/-- **THE DESIGNED STATEMENT.**

~~CMP99b p.428's coercivity claim, with the source's own hypotheses present, the source's own object
(`C*Δ_kC` on the `B̃` variables of `Λ̃`), the source's own uniformity, and NO clause the source does
not make.~~ **STRUCK 2026-07-30 — false on two counts, per §00.** The object is p.392 (3.10)'s
one-scale `D*_U D_U + Δ′(U)`, not p.428 (3.156)'s `Δ_k`; and `GaugeRegular` is a different
**UNCOMPARED** proxy for (3.35)/(3.36), not that hypothesis (§2a). ~~**WIDER-OR-INCOMPARABLE** …
the comparison was completed 2026-07-30 and the wide direction is the one realized in the source's
own small-`O(1)Mα₀` regime~~ **— STRUCK 2026-07-30 (second correction); that comparison was against
a coordinatewise proxy and was convicted, §2a. `uncompared` is restored as the operative word.**

**What it is, accurately:** coercivity of the tree's normalized p.392 one-scale quadratic form,
sandwiched through the `C`-reparametrization, on the `Λ̃` variables of the whole periodic torus,
uniformly in `k`, in `U`, in the ladder and in the realization of `Δ`. It has p.428's SHAPE. See §2
for the clause-by-clause map, §2a for the hypothesis gap, and §00 for what it does and does not
license.

**Two binder notes, both proved, neither cosmetic:**
* `DenotesDeltaKPinned` (not `DenotesDeltaK`) — the pinning conjunct of §5a. Proved INERT:
  `p428Coercivity_iff_unpinned` (§7b).
* the `∀ Δ` binder is **ELIMINABLE** — `p428Coercivity_iff_deltaFree` (§7c) proves this statement
  equivalent to one in which `Δ` does not occur. It was advertised as uniformity over realizations;
  it is decoration. It is retained (not dropped) only because `Spine.coerc_u_main_su2` and
  `HoleHunt/TrivialInhabitation` are stated against this type; the annotation is the honest record,
  and §7c is the pointer. -/
def P428Coercivity (L : PeriodicLatticeExtent) (ell : ℕ) : Prop :=
  ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (Δ : DeltaFam L) (bg : Ladder L),
      AnchoredLadder bg → RegularityPreserving ell bg → DenotesDeltaKPinned Δ bg →
      ∀ (k : ℕ) (U : LinkCfg L), GaugeRegular (alphaEll ell) U →
        ∀ Btil : Bond L → SuTwo, OnLambdaTilde ell Btil →
          γ₀ * bondEnergy Btil ≤ sandwichForm Δ ell bg k U Btil

/-! ### §5b — the one new inequality the design needs: `C` does not lose energy on `Λ̃`

`C` is the identity off the dropped bonds and a `B̃`-supported field vanishes ON the dropped bonds,
so `C` can only ADD energy. This is what lets the source's bound on the `B̃` variables be read off
the ambient coercivity with **no** norm-equivalence constant: the transfer constant is `1`. -/

/-- **`bondEnergy B̃ ≤ bondEnergy (C B̃)`** whenever `B̃` vanishes on every dropped bond. -/
theorem bondEnergy_le_fullC {ell : ℕ} (U : LinkCfg L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo)
    (hB : ∀ b : Bond L, IsDropped ell b → B b = 0) :
    bondEnergy B ≤ bondEnergy (fullC U ell Dinv B) := by
  unfold bondEnergy
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hb : IsDropped ell b
  · rw [hB b hb]
    simp
  · rw [fullC_free U Dinv B hb]

/-- The same statement at the named `C`. -/
theorem bondEnergy_le_Creparam {ell : ℕ} (U : LinkCfg L) (Btil : Bond L → SuTwo)
    (hB : ∀ b : Bond L, IsDropped ell b → Btil b = 0) :
    bondEnergy Btil ≤ bondEnergy (Creparam U ell Btil) :=
  bondEnergy_le_fullC U (dinvC U ell) Btil hB

#print axioms bondEnergy_le_fullC
#print axioms bondEnergy_le_Creparam

/-! ### §5c — D3 (`B = 0` on `Λᶜ`), stated rather than dropped silently

The source's `Λ` is a finite region of a larger lattice; this tree's lattice is the whole periodic
torus, i.e. the case `Λ = ` everything. In that case `Λᶜ = ∅` and "`B = 0` on `Λᶜ`" holds for every
field, so `OnLambdaTilde` omits it WITHOUT weakening the statement AT THAT `Λ`. It is a genuine
scope restriction — the designed statement is p.428 at one region, the whole torus — and it is a
restriction the whole `Balaban/` directory already carries ~~(there is no `Λ`-region type in this
tree)~~. Recorded, not claimed closed.

**STRUCK 2026-07-30: "there is no `Λ`-region type in this tree" was FALSE when written.**
`Balaban/DomainSequence.lean` has carried one since 2026-07-22:
`AdalyFormal.Balaban.DomainSequence.LambdaKDomain`, a structure supplying `Λ ⊂ Λ_k`
(`LambdaKDomain.IsValid`'s first conjunct), both regions as unions of big blocks
(`LambdaKDomain.Lambda` and `LambdaKDomain.LambdaK`, each a `DomainSequence.bigBlockUnion` over a
freely chosen center set), and CMP96 (2.2)'s `RM` margin (`DomainSequence.MarginCondition`), with a
non-vacuity theorem exhibiting a concrete valid instance with nonempty `Λ`
(`DomainSequence.domainSequence_nonvacuous`). What is TRUE, and is the operative statement, is
narrower and is about THIS file: this file's `OnLambdaTilde` is not parametrized by a region at all,
and `Balaban/DomainSequence.lean` is not imported here. **A lane extending §5c should CONSUME
`LambdaKDomain`, not rebuild it** (LAW-19). -/

/-! ## §6 — REQUIREMENT (a): THE DENOTATION CLAUSE REJECTS BOTH JUNK FAMILIES

The discriminator is a REUSE of the very fact that refutes `coerc_u_main`'s clause 3: the faithful
`Δ_k` form is **negative** at `(centralHolonomyU, deltaWitnessConfig)`
(`SpineCoercivityInstance.inner_deltaKCLMNormalized_centralHolonomyU` gives `-4`). In the live
statement that fact is a REFUTATION, because clause 3 demands global PSD. Moved into the denotation
clause it becomes a DISCRIMINATOR, because a content-free operator cannot be negative there. Same
fact, opposite sign of usefulness — that is the design in one line.

Note where the anchor earns its place: without `bg 0 U = U` the identity `DenotesDeltaK` could be
satisfied at a ladder that never evaluates `Δ_k` at `centralHolonomyU` at all. -/

/-- **The discriminating value, named once and consumed twice** (§6's master rejection and §7e's
`k`-dependence witness): the faithful `Δ_k` form is `-4` at `(centralHolonomyU,
deltaWitnessConfig)`. -/
theorem deltaK_centralHolonomyU_eq_neg_four :
    deltaKQuadFormNormalizedCorrected centralHolonomyU deltaWitnessConfig = -4 := by
  rw [← inner_deltaKCLMNormalized_eq]
  exact inner_deltaKCLMNormalized_centralHolonomyU

#print axioms deltaK_centralHolonomyU_eq_neg_four

/-- **THE MASTER REJECTION.** Any family whose form is `≥ 0` at the single pair
`(k = 0, U = centralHolonomyU)` on the single vector `toLp deltaWitnessConfig` fails the denotation
clause, for EVERY anchored ladder. One theorem; §6a-§6c are instances. -/
theorem nonneg_at_central_fails_denotation
    (Δ : DeltaFam witnessL) (bg : Ladder witnessL) (hanch : AnchoredLadder bg)
    (hnn : 0 ≤ (inner ℝ (WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL)
      (Δ 0 centralHolonomyU (WithLp.toLp 2 deltaWitnessConfig)) : ℝ)) :
    ¬ DenotesDeltaK Δ bg := by
  intro hden
  have h := hden 0 centralHolonomyU deltaWitnessConfig
  rw [hanch centralHolonomyU] at h
  rw [deltaK_centralHolonomyU_eq_neg_four] at h
  rw [h] at hnn
  norm_num at hnn

#print axioms nonneg_at_central_fails_denotation

/-! ### §6a — every globally PSD family is rejected -/

/-- Any family that is positive semidefinite anywhere near the witness is rejected. This is the
class every "identity plus a nonnegative decoration" witness in this tree belongs to. -/
theorem psdFamily_fails_denotation
    (Δ : DeltaFam witnessL) (bg : Ladder witnessL) (hanch : AnchoredLadder bg)
    (hpsd : ∀ (k : ℕ) (U : LinkCfg witnessL) (v : BondFnL2 witnessL),
      0 ≤ (inner ℝ v (Δ k U v) : ℝ)) :
    ¬ DenotesDeltaK Δ bg :=
  nonneg_at_central_fails_denotation Δ bg hanch
    (hpsd 0 centralHolonomyU (WithLp.toLp 2 deltaWitnessConfig))

/-- **The bare identity family.** -/
theorem junkId_fails_denotation (bg : Ladder witnessL) (hanch : AnchoredLadder bg) :
    ¬ DenotesDeltaK (fun _ _ => ContinuousLinearMap.id ℝ (BondFnL2 witnessL)) bg := by
  refine psdFamily_fails_denotation _ bg hanch fun k U v => ?_
  show (0:ℝ) ≤ inner ℝ v v
  rw [real_inner_self_eq_norm_sq]
  positivity

#print axioms psdFamily_fails_denotation
#print axioms junkId_fails_denotation

/-! ### §6b — JUNK FAMILY 1 (`CoercUMainKernel.jDelta`-shaped): `id + c • P_W`

The tree's family 1 is `CoercUMainKernel.jDelta k U = id + jg k U • (jW).starProjection` with
`jg k U = (k : ℝ) + ucoef U`, on `AnchoredBondSpace`. Transplanted to the faithful carrier and
GENERALIZED — the coefficient is an arbitrary nonnegative function of `(k, U)` and the subspace is
arbitrary, so this covers `jDelta` and every reweighting of it at once.

**COVERAGE IS MECHANICAL, NOT RHETORICAL.** The nonnegativity side condition below is discharged for
the tree's actual family by the tree's own theorem `CoercUMainKernel.jg_pos : 0 < jg k U`. So the
instantiation is `c := jg`, `W := jW`, `hc := fun k U => le_of_lt (jg_pos k U)` — nothing about
`jDelta` is left to a reader's judgement. -/

/-- `id + c k U • P_W` is PSD whenever `c ≥ 0`. -/
theorem idPlusScaledProjector_psd (W : Submodule ℝ (BondFnL2 L)) [W.HasOrthogonalProjection]
    (c : ℕ → LinkCfg L → ℝ) (hc : ∀ k U, 0 ≤ c k U) (k : ℕ) (U : LinkCfg L)
    (v : BondFnL2 L) :
    0 ≤ (inner ℝ v ((ContinuousLinearMap.id ℝ (BondFnL2 L) + c k U • W.starProjection) v) : ℝ) := by
  have hsplit : (inner ℝ v ((ContinuousLinearMap.id ℝ (BondFnL2 L)
        + c k U • W.starProjection) v) : ℝ)
      = (inner ℝ v v : ℝ) + c k U * (inner ℝ v (W.starProjection v) : ℝ) := by
    rw [ContinuousLinearMap.add_apply, inner_add_right, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, real_inner_smul_right]
    rfl
  rw [hsplit]
  have h1 : (0:ℝ) ≤ inner ℝ v v := by
    rw [real_inner_self_eq_norm_sq]; positivity
  have h2 : (0:ℝ) ≤ c k U * (inner ℝ v (W.starProjection v) : ℝ) :=
    mul_nonneg (hc k U) (inner_starProjection_nonneg W v)
  linarith

/-- **JUNK FAMILY 1 IS REJECTED**, at every subspace, every nonnegative coefficient function, and
every anchored ladder. -/
theorem idPlusScaledProjector_fails_denotation
    (W : Submodule ℝ (BondFnL2 witnessL)) [W.HasOrthogonalProjection]
    (c : ℕ → LinkCfg witnessL → ℝ) (hc : ∀ k U, 0 ≤ c k U)
    (bg : Ladder witnessL) (hanch : AnchoredLadder bg) :
    ¬ DenotesDeltaK
        (fun k U => ContinuousLinearMap.id ℝ (BondFnL2 witnessL) + c k U • W.starProjection) bg :=
  psdFamily_fails_denotation _ bg hanch fun k U v =>
    idPlusScaledProjector_psd W c hc k U v

#print axioms idPlusScaledProjector_psd
#print axioms idPlusScaledProjector_fails_denotation

/-! ### §6c — JUNK FAMILY 2 (`CoercUMainKernel.chainDelta`-shaped): `c U • P_{K k}`

The tree's family 2 is `CoercUMainKernel.chainDelta K k U = ucoef U • (K k)ᗮ.starProjection` — a
scaled orthogonal projector on a monotone chain, which K5 rejects but K1∧K2∧K3 admits. Here the chain
is an ARBITRARY family of submodules (so `K k` and `(K k)ᗮ` are both covered, and monotonicity is not
even needed) and the coefficient is an arbitrary nonnegative function of `U`.

**COVERAGE IS MECHANICAL, NOT RHETORICAL.** The instantiation for the tree's actual family is
`c := ucoef`, the submodule family `fun k => (K k)ᗮ`, and `hc := fun U => le_of_lt (ucoef_pos U)`,
discharged by the tree's own `CoercUMainKernel.ucoef_pos : 0 < ucoef U`. -/

/-- **JUNK FAMILY 2 IS REJECTED**, at every submodule chain, every nonnegative coefficient, and
every anchored ladder. Note this needs NO condition on the chain: monotonicity, the strict jump and
the `V^⊥` containment — the three things `KernelStrengthened` reasons about — are all irrelevant to
the rejection, because the rejection is on the denotation axis, not the shape axis. -/
theorem scaledProjectorFamily_fails_denotation
    (K : ℕ → Submodule ℝ (BondFnL2 witnessL)) [∀ k, (K k).HasOrthogonalProjection]
    (c : LinkCfg witnessL → ℝ) (hc : ∀ U, 0 ≤ c U)
    (bg : Ladder witnessL) (hanch : AnchoredLadder bg) :
    ¬ DenotesDeltaK (fun k U => c U • (K k).starProjection) bg := by
  refine psdFamily_fails_denotation _ bg hanch fun k U v => ?_
  have hsplit : (inner ℝ v ((c U • (K k).starProjection) v) : ℝ)
      = c U * (inner ℝ v ((K k).starProjection v) : ℝ) := by
    rw [ContinuousLinearMap.coe_smul', Pi.smul_apply, real_inner_smul_right]
  rw [hsplit]
  exact mul_nonneg (hc U) (inner_starProjection_nonneg (K k) v)

#print axioms scaledProjectorFamily_fails_denotation

/-! ### §6g — BRIDGE TO THE STATEMENT'S ACTUAL HYPOTHESIS

`P428Coercivity` binds `DenotesDeltaKPinned`, while §6a-§6c reject on the sharper `DenotesDeltaK`.
One line carries every rejection across, and it goes only in this direction — which is exactly why
`DenotesDeltaK` was left unchanged when the pinning conjunct was added (§5a). -/

/-- Every `¬ DenotesDeltaK` rejection above is also a `¬ DenotesDeltaKPinned` rejection. -/
theorem not_denotesPinned_of_not_denotes {Δ : DeltaFam L} {bg : Ladder L}
    (h : ¬ DenotesDeltaK Δ bg) : ¬ DenotesDeltaKPinned Δ bg := fun hp => h hp.1

#print axioms not_denotesPinned_of_not_denotes

/-! ### §6d — MUST-NOT-FIRE: the discriminator does NOT reject the faithful family

If §6's mechanism fired on everything it would be worthless. It does not: the faithful family is
precisely a family whose form is NEGATIVE at the witness pair, so the hypothesis of
`nonneg_at_central_fails_denotation` FAILS for it. Stated as a theorem, not asserted. -/

/-- The faithful family's form at the witness pair is `-4`, hence NOT `≥ 0`: the master rejection's
hypothesis is false for it. -/
theorem faithful_not_nonneg_at_central :
    ¬ (0 ≤ (inner ℝ (WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL)
      ((fun (_ : ℕ) (U : LinkCfg witnessL) => deltaKCLMNormalized U) 0 centralHolonomyU
        (WithLp.toLp 2 deltaWitnessConfig)) : ℝ)) := by
  show ¬ (0 ≤ (inner ℝ (WithLp.toLp 2 deltaWitnessConfig : BondFnL2 witnessL)
    (deltaKCLMNormalized centralHolonomyU (WithLp.toLp 2 deltaWitnessConfig)) : ℝ))
  rw [inner_deltaKCLMNormalized_centralHolonomyU]
  norm_num

#print axioms faithful_not_nonneg_at_central

/-! ### §6e — WHAT "NOT JUNK-INHABITABLE" MEANS FOR A `∀`-STATEMENT (read before scoring (a))

`coerc_u_main` is `∃ Δ, …`, so "junk inhabits it" is literally a witness for its existential.
`P428Coercivity` is `∃ γ₀, ∀ Δ …`, so there is no `Δ`-slot to inhabit, and the requirement has to be
scored in the two halves it actually decomposes into. Both are theorems above, neither is an
argument:

1. **Junk cannot enter the statement's range.** §6a-§6c: no family whose form is `≥ 0` at the witness
   pair satisfies `DenotesDeltaK`, so `jDelta`- and `chainDelta`-shaped families are outside every
   instance of the `∀`. They cannot be used to make the statement true and they cannot be used to
   make it look true.
2. **The statement is not empty of content once junk is excluded.** §7f
   (`p428Coercivity_forces_strict_positivity`): it FORCES a strictly positive value of the source's
   own quadratic form at a named nonzero `Λ̃`-field, at every `γ₀` it can supply.

The failure mode this pair rules out is the one a `∀`-statement is actually vulnerable to — not a
junk witness, but *empty hypotheses*. §7f Attack 1 is that attack, run and blocked. -/

/-! ## §7 — REQUIREMENT (b) AND (c): THE FAITHFUL FAMILY INHABITS THE DESIGNED STATEMENT -/

/-- **The faithful family**: rung `k` is Bałaban's normalized `Δ_k` at rung `k`'s background. Not
free data — it is DEFINED from the ladder. -/
noncomputable def faithfulFamily (bg : Ladder L) : DeltaFam L :=
  fun k U => deltaKCLMNormalized (bg k U)

/-- **It denotes** — by construction, `DeltaPrimeOperator.inner_deltaKCLMNormalized_eq`. -/
theorem faithfulFamily_denotes (bg : Ladder L) : DenotesDeltaK (faithfulFamily bg) bg :=
  fun k U A => inner_deltaKCLMNormalized_eq (bg k U) A

#print axioms faithfulFamily
#print axioms faithfulFamily_denotes

/-! ### §7a — THE PINNING CONJUNCT, PROVED: the whole §5a block

**PORTED, not re-derived** (LAW-19) — with the exceptions named, because an unqualified "all of this
was already proved" is the same class of over-claim this file is being repaired for. Almost every
declaration in §7a-§7c was first proved in `compute/designed_skew/DesignedSkew.lean` (§2, §3, §4,
§5,
§6, §7, §7b) and is transplanted verbatim modulo namespace. **Not ported, written here:**
`bondZeroA`/`bondZeroB`/`bondZeroA_ne_bondZeroB` (that exhibit imported `CoercUMainKernel.bondA`/
`bondB`, which this module cannot — see the disclosure in §7a.1); and `P428CoercivityUnpinned` with
`p428Coercivity_iff_unpinned`, which are the MIRROR IMAGES of that exhibit's `P428CoercivityPinned`
/
`p428Coercivity_iff_pinned` — same content, reversed, because there the conjunct was proposed and
here it is applied, so it is the UNPINNED form that must now be retained as the referent. Everything
else below is that exhibit's proof term.

Four things are established, in order:
1. `ZeroDiag` ⟺ skew bilinear form, and a zero-diagonal SELF-ADJOINT operator is `0` (the pincer);
2. an explicit **nonzero** `S0 : BondFnL2 L →L[ℝ] BondFnL2 L` with `⟪A, S0 A⟫ = 0` for all `A`;
3. therefore `DenotesDeltaK` does **not** pin — `denotesDeltaK_not_pinned` — and the looseness is
   EXACTLY the zero-diagonal shift, no less and no more (`denotesDeltaK_iff_zeroDiag_sub`);
4. the pinning conjunct closes it: `faithfulFamily_denotesPinned` (it does not empty the statement),
   `denotesDeltaKPinned_unique` (operator EQUALITY), `skewShifted_fails_pinned` (it is effective).
   -/

/-- **Zero diagonal ⟹ skew form.** Polarization over `ℝ`. This is what licenses the word "skew". -/
theorem zeroDiag_skew {S : BondFnL2 L →L[ℝ] BondFnL2 L} (hS : ZeroDiag S) (x y : BondFnL2 L) :
    (inner ℝ x (S y) : ℝ) = - inner ℝ y (S x) := by
  have h := hS (x + y)
  rw [map_add, inner_add_left, inner_add_right, inner_add_right] at h
  have hx := hS x
  have hy := hS y
  linarith

/-- The converse, so `ZeroDiag` and "skew bilinear form" are interchangeable. -/
theorem zeroDiag_of_skew {S : BondFnL2 L →L[ℝ] BondFnL2 L}
    (h : ∀ x y : BondFnL2 L, (inner ℝ x (S y) : ℝ) = - inner ℝ y (S x)) : ZeroDiag S := by
  intro A
  have := h A A
  linarith

theorem zeroDiag_neg {S : BondFnL2 L →L[ℝ] BondFnL2 L} (hS : ZeroDiag S) : ZeroDiag (-S) := by
  intro A
  rw [ContinuousLinearMap.neg_apply, inner_neg_right, hS]
  ring

/-- **A zero-diagonal SELF-ADJOINT operator is zero.** The other half of the pincer: the ambiguity
lives entirely in the skew part, and dies the moment self-adjointness is demanded. -/
theorem eq_zero_of_zeroDiag_of_symm {T : BondFnL2 L →L[ℝ] BondFnL2 L} (hd : ZeroDiag T)
    (hs : ∀ x y : BondFnL2 L, (inner ℝ (T x) y : ℝ) = inner ℝ x (T y)) : T = 0 := by
  have key : ∀ x y : BondFnL2 L, (inner ℝ x (T y) : ℝ) = 0 := by
    intro x y
    have h1 : (inner ℝ x (T y) : ℝ) = - inner ℝ y (T x) := zeroDiag_skew hd x y
    have h2 : (inner ℝ (T y) x : ℝ) = inner ℝ y (T x) := hs y x
    have h3 : (inner ℝ (T y) x : ℝ) = inner ℝ x (T y) := real_inner_comm _ _
    linarith
  refine ContinuousLinearMap.ext fun y => ?_
  have h0 := key (T y) y
  exact inner_self_eq_zero.mp h0

/-! #### §7a.1 — the explicit nonzero skew map

Built from Mathlib pieces only (`WithLp.linearEquiv`, `LinearMap.single`, `PiLp.projₗ`,
`LinearMap.toContinuousLinearMap`).

**Disclosure (LAW-19).** `CoercUMainKernel.bondA`/`bondB`/`bondA_ne_bondB` are the two distinct
bonds
`DesignedSkew.lean` used. That module is NOT in this file's import closure, and adding an import
edge
into it purely for two `Prod.mk`s is a worse trade than the three lines below; the pair is therefore
re-declared locally at the origin site rather than imported. -/

/-- The coordinate inclusion `SuTwo → BondFnL2 L` at one bond. -/
noncomputable def inclB (b : Bond L) : SuTwo →ₗ[ℝ] BondFnL2 L :=
  (WithLp.linearEquiv 2 ℝ (Bond L → SuTwo)).symm.toLinearMap ∘ₗ
    LinearMap.single ℝ (fun _ : Bond L => SuTwo) b

theorem ofLp_inclB (b : Bond L) (X : SuTwo) :
    WithLp.ofLp (inclB b X) = Pi.single b X := rfl

/-- `⟪A, inclB b X⟫ = ⟪A b, X⟫`. The one computation the construction needs. -/
theorem inner_inclB (b : Bond L) (A : BondFnL2 L) (X : SuTwo) :
    (inner ℝ A (inclB b X) : ℝ) = inner ℝ (WithLp.ofLp A b) X := by
  rw [PiLp.inner_apply]
  have hsingle : ∀ i : Bond L,
      (WithLp.ofLp (inclB b X)) i = (Pi.single b X : Bond L → SuTwo) i :=
    fun i => congrFun (ofLp_inclB b X) i
  have hsum := Finset.sum_eq_single_of_mem
      (f := fun i : Bond L => (inner ℝ (WithLp.ofLp A i) (WithLp.ofLp (inclB b X) i) : ℝ))
      b (Finset.mem_univ b)
      (fun c _ hc => by rw [hsingle c, Pi.single_eq_of_ne hc, inner_zero_right])
  rw [hsum, hsingle b, Pi.single_eq_same]

theorem inclB_ne_zero (b : Bond L) {X : SuTwo} (hX : X ≠ 0) : inclB b X ≠ 0 := by
  intro h
  apply hX
  have h1 : (Pi.single b X : Bond L → SuTwo) b = (WithLp.ofLp (0 : BondFnL2 L)) b := by
    rw [← ofLp_inclB b X, h]
  rw [Pi.single_eq_same] at h1
  exact h1

/-- **`S = e_{b₁} ⊗ ⟪e_{b₂}, ·⟫ − e_{b₂} ⊗ ⟪e_{b₁}, ·⟫`** — the rank-two rotation generator. -/
noncomputable def skewLM (b₁ b₂ : Bond L) : BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  inclB b₁ ∘ₗ (PiLp.projₗ 2 (fun _ : Bond L => SuTwo) b₂)
    - inclB b₂ ∘ₗ (PiLp.projₗ 2 (fun _ : Bond L => SuTwo) b₁)

noncomputable def skewCLM (b₁ b₂ : Bond L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (skewLM b₁ b₂)

theorem skewCLM_apply (b₁ b₂ : Bond L) (A : BondFnL2 L) :
    skewCLM b₁ b₂ A = inclB b₁ (WithLp.ofLp A b₂) - inclB b₂ (WithLp.ofLp A b₁) := rfl

/-- **IT IS SKEW.** `⟪A, S A⟫ = ⟪A b₁, A b₂⟫ − ⟪A b₂, A b₁⟫ = 0` by real symmetry of the inner
product. No hypothesis on `b₁, b₂`. -/
theorem skewCLM_zeroDiag (b₁ b₂ : Bond L) : ZeroDiag (skewCLM (L := L) b₁ b₂) := by
  intro A
  rw [skewCLM_apply, inner_sub_right, inner_inclB, inner_inclB]
  have := real_inner_comm (WithLp.ofLp A b₂) (WithLp.ofLp A b₁)
  linarith

/-- **IT IS NONZERO** whenever the two bonds differ. -/
theorem skewCLM_ne_zero {b₁ b₂ : Bond L} (h : b₁ ≠ b₂) : skewCLM (L := L) b₁ b₂ ≠ 0 := by
  intro hz
  have hval : skewCLM (L := L) b₁ b₂ (inclB b₂ suTwoWitness) = 0 := by
    rw [hz]; rfl
  rw [skewCLM_apply] at hval
  have e2 : WithLp.ofLp (inclB (L := L) b₂ suTwoWitness) b₂ = suTwoWitness := by
    rw [ofLp_inclB, Pi.single_eq_same]
  have e1 : WithLp.ofLp (inclB (L := L) b₂ suTwoWitness) b₁ = 0 := by
    rw [ofLp_inclB, Pi.single_eq_of_ne h]
  rw [e2, e1, map_zero, sub_zero] at hval
  exact inclB_ne_zero b₁ suTwoWitness_ne_zero hval

/-- **MUST-NOT-FIRE CONTROL for `skewCLM_ne_zero`.** At `b₁ = b₂` the construction DEGENERATES to
the
zero map, so the `b₁ ≠ b₂` hypothesis is load-bearing rather than decorative. -/
theorem skewCLM_self_eq_zero (b : Bond L) : skewCLM (L := L) b b = 0 := by
  refine ContinuousLinearMap.ext fun A => ?_
  rw [skewCLM_apply, sub_self]
  rfl

/-- Two distinct bonds at the origin site: same site, different coordinate direction. -/
def bondZeroA (L : PeriodicLatticeExtent) : Bond L := (siteZero L, (0 : Fin 3))

/-- The second of the pair. -/
def bondZeroB (L : PeriodicLatticeExtent) : Bond L := (siteZero L, (1 : Fin 3))

theorem bondZeroA_ne_bondZeroB : bondZeroA L ≠ bondZeroB L := by
  intro h
  have h2 : (0 : Fin 3) = 1 := congrArg Prod.snd h
  exact absurd h2 (by decide)

/-- **THE WITNESS.** -/
noncomputable def S0 (L : PeriodicLatticeExtent) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  skewCLM (bondZeroA L) (bondZeroB L)

theorem S0_zeroDiag : ZeroDiag (S0 L) := skewCLM_zeroDiag _ _

theorem S0_ne_zero : S0 L ≠ 0 := skewCLM_ne_zero bondZeroA_ne_bondZeroB

/-- **MUST-NOT-FIRE CONTROL for `eq_zero_of_zeroDiag_of_symm`.** `ZeroDiag` alone does NOT force
`T = 0` — `S0` is the counterexample — so the symmetry hypothesis of that lemma is load-bearing.
Equivalently: `S0` is genuinely NOT self-adjoint, which is why §7a.2's repair can reject it. -/
theorem S0_not_symm :
    ¬ (∀ x y : BondFnL2 L, (inner ℝ (S0 L x) y : ℝ) = inner ℝ x (S0 L y)) := fun h =>
  S0_ne_zero (eq_zero_of_zeroDiag_of_symm S0_zeroDiag h)

#print axioms zeroDiag_skew
#print axioms zeroDiag_of_skew
#print axioms zeroDiag_neg
#print axioms eq_zero_of_zeroDiag_of_symm
#print axioms inclB
#print axioms inner_inclB
#print axioms inclB_ne_zero
#print axioms skewCLM
#print axioms skewCLM_zeroDiag
#print axioms skewCLM_ne_zero
#print axioms skewCLM_self_eq_zero
#print axioms bondZeroA_ne_bondZeroB
#print axioms S0
#print axioms S0_zeroDiag
#print axioms S0_ne_zero
#print axioms S0_not_symm

/-! #### §7a.2 — `DenotesDeltaK` does not pin, `DenotesDeltaKPinned` does -/

/-- **The general fact.** Any predicate constraining only the `toLp`-diagonal is blind to a
zero-diagonal shift. -/
theorem diagonalForm_add_zeroDiag {f : (Bond L → SuTwo) → ℝ}
    {T S : BondFnL2 L →L[ℝ] BondFnL2 L} (hS : ZeroDiag S)
    (hT : ∀ A : Bond L → SuTwo,
      (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) (T (WithLp.toLp 2 A)) : ℝ) = f A)
    (A : Bond L → SuTwo) :
    (inner ℝ (WithLp.toLp 2 A : BondFnL2 L) ((T + S) (WithLp.toLp 2 A)) : ℝ) = f A := by
  rw [ContinuousLinearMap.add_apply, inner_add_right, hT A, hS]
  ring

/-- Adding a zero-diagonal operator preserves denotation. -/
theorem denotesDeltaK_add_skew {Δ : DeltaFam L} {bg : Ladder L}
    {S : BondFnL2 L →L[ℝ] BondFnL2 L} (hS : ZeroDiag S) (hden : DenotesDeltaK Δ bg) :
    DenotesDeltaK (fun k U => Δ k U + S) bg :=
  fun k U A => diagonalForm_add_zeroDiag hS (fun A' => hden k U A') A

/-- And it is a BIJECTION of the denoting set, not merely an inclusion — so the skew shift cannot
smuggle a new family in either, and the NEGATED junk-rejection forms of §6 are invariant too. -/
theorem denotesDeltaK_add_skew_iff {Δ : DeltaFam L} {bg : Ladder L}
    {S : BondFnL2 L →L[ℝ] BondFnL2 L} (hS : ZeroDiag S) :
    DenotesDeltaK (fun k U => Δ k U + S) bg ↔ DenotesDeltaK Δ bg := by
  constructor
  · intro h
    have h2 := denotesDeltaK_add_skew (Δ := fun k U => Δ k U + S) (zeroDiag_neg hS) h
    intro k U A
    have := h2 k U A
    simpa using this
  · exact denotesDeltaK_add_skew hS

/-- **THE UNPINNEDNESS, AS A THEOREM.** Two families that both satisfy `DenotesDeltaK` at the same
ladder and differ at EVERY rung and EVERY configuration. -/
theorem denotesDeltaK_not_pinned (bg : Ladder L) :
    ∃ Δ₁ Δ₂ : DeltaFam L, DenotesDeltaK Δ₁ bg ∧ DenotesDeltaK Δ₂ bg ∧
      ∀ (k : ℕ) (U : LinkCfg L), Δ₁ k U ≠ Δ₂ k U := by
  refine ⟨faithfulFamily bg, fun k U => faithfulFamily bg k U + S0 L,
    faithfulFamily_denotes bg,
    denotesDeltaK_add_skew S0_zeroDiag (faithfulFamily_denotes bg), ?_⟩
  intro k U h
  have h' : faithfulFamily bg k U + S0 L = faithfulFamily bg k U + 0 := by
    rw [add_zero]; exact h.symm
  exact S0_ne_zero (add_left_cancel h')

/-- **THE EXACT CHARACTERIZATION** — not "at least a skew shift" but "exactly a skew shift": the
solution set of `DenotesDeltaK` at a ladder is the affine set `faithfulFamily bg + {zero-diagonal}`,
and nothing else. -/
theorem denotesDeltaK_iff_zeroDiag_sub (Δ : DeltaFam L) (bg : Ladder L) :
    DenotesDeltaK Δ bg ↔ ∀ (k : ℕ) (U : LinkCfg L), ZeroDiag (Δ k U - faithfulFamily bg k U) := by
  constructor
  · intro hden k U A
    have h1 := hden k U (WithLp.ofLp A)
    have h2 := faithfulFamily_denotes bg k U (WithLp.ofLp A)
    rw [show (WithLp.toLp 2 (WithLp.ofLp A) : BondFnL2 L) = A from rfl] at h1 h2
    show (inner ℝ A ((Δ k U - faithfulFamily bg k U) A) : ℝ) = 0
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, h1, h2]
    ring
  · intro h k U A
    have hz := h k U (WithLp.toLp 2 A)
    rw [ContinuousLinearMap.sub_apply, inner_sub_right,
      faithfulFamily_denotes bg k U A] at hz
    linarith

/-- **THE REPAIR DOES NOT EMPTY THE STATEMENT.** `deltaKCLMNormalized_symm` is unconditional in `U`,
so the faithful family satisfies the pinned clause at EVERY ladder. Without this,
`P428Coercivity` would have been strengthened into vacuity. -/
theorem faithfulFamily_denotesPinned (bg : Ladder L) :
    DenotesDeltaKPinned (faithfulFamily bg) bg :=
  ⟨faithfulFamily_denotes bg, fun k U x y => deltaKCLMNormalized_symm (bg k U) x y⟩

/-- **THE PAYOFF: THE PINNED CLAUSE PINS THE OPERATOR.** Under it the family is *equal* to the
faithful one — operator equality, not equality of quadratic forms. -/
theorem denotesDeltaKPinned_unique {Δ : DeltaFam L} {bg : Ladder L}
    (h : DenotesDeltaKPinned Δ bg) : Δ = faithfulFamily bg := by
  funext k U
  have hz : ZeroDiag (Δ k U - faithfulFamily bg k U) :=
    (denotesDeltaK_iff_zeroDiag_sub Δ bg).1 h.1 k U
  have hs : ∀ x y : BondFnL2 L,
      (inner ℝ ((Δ k U - faithfulFamily bg k U) x) y : ℝ)
        = inner ℝ x ((Δ k U - faithfulFamily bg k U) y) := by
    intro x y
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, inner_sub_left,
      inner_sub_right, h.2 k U x y]
    have := deltaKCLMNormalized_symm (bg k U) x y
    show _ - (inner ℝ (deltaKCLMNormalized (bg k U) x) y : ℝ)
      = _ - (inner ℝ x (deltaKCLMNormalized (bg k U) y) : ℝ)
    rw [this]
  exact sub_eq_zero.mp (eq_zero_of_zeroDiag_of_symm hz hs)

/-- **THE REPAIR IS EFFECTIVE** — it rejects the very family that convicts the unpinned clause. A
repair that admitted it would be decoration. -/
theorem skewShifted_fails_pinned (bg : Ladder L) :
    ¬ DenotesDeltaKPinned (fun k U => faithfulFamily bg k U + S0 L) bg := by
  intro h
  have heq := denotesDeltaKPinned_unique h
  have hk := congrFun (congrFun heq 0) (trivialU L)
  have hk' : faithfulFamily bg 0 (trivialU L) + S0 L
      = faithfulFamily bg 0 (trivialU L) + 0 := by
    rw [add_zero]; exact hk
  exact S0_ne_zero (add_left_cancel hk')

/-- **The NEW conjunct is what does the rejecting**, not the denotation clause: the shifted family
DENOTES and fails ONLY `SelfAdjointFam`. Stated directly so nobody reads `skewShifted_fails_pinned`
as the denotation clause having quietly tightened. -/
theorem skewShifted_not_selfAdjoint (bg : Ladder L) :
    ¬ SelfAdjointFam (fun k U => faithfulFamily bg k U + S0 L) := fun hs =>
  skewShifted_fails_pinned bg
    ⟨denotesDeltaK_add_skew S0_zeroDiag (faithfulFamily_denotes bg), hs⟩

#print axioms diagonalForm_add_zeroDiag
#print axioms denotesDeltaK_add_skew
#print axioms denotesDeltaK_add_skew_iff
#print axioms denotesDeltaK_not_pinned
#print axioms denotesDeltaK_iff_zeroDiag_sub
#print axioms faithfulFamily_denotesPinned
#print axioms denotesDeltaKPinned_unique
#print axioms skewShifted_fails_pinned
#print axioms skewShifted_not_selfAdjoint

/-- **THE CORE INEQUALITY, WITHOUT THE ANCHOR.** Stated separately for a reason a nested validator
made visible: `p428Coercivity_holds` binds `AnchoredLadder bg` and NEVER USES IT. That is not slack
in the proof, it is a fact about the design, and it is better as a theorem than as a docstring note:
**the positive half needs only regularity-preservation, so `AnchoredLadder` is present in
`P428Coercivity` PURELY as the junk-rejection device of §6** — it costs the positive result nothing,
which is exactly the property an anti-junk clause should have. This declaration is therefore
strictly stronger than the anchored form, and `p428Coercivity_holds` is its corollary.

The proof is a three-step chain and every step is a printed one:
1. the denotation clause turns `⟪B̃, C*Δ_kC B̃⟫` into the source's `Δ_k` form at `C B̃`;
2. `C B̃` is admissible for FREE — axial by `fullC_unconditional_axialGauge` and in `ker Q₁` by
   `fullC_unconditional_mem_kerQ`, which is exactly why [S-PARAM] parametrizes by `B̃`;
3. `C` does not lose energy on `Λ̃` (§5b), so the ambient bound transfers with constant `1`. -/
theorem coercivity_on_lambdaTilde_of_regular_ladder {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (Δ : DeltaFam L) (bg : Ladder L) (hreg : RegularityPreserving ell bg)
    (hden : DenotesDeltaK Δ bg) (k : ℕ) (U : LinkCfg L)
    (hU : GaugeRegular (alphaEll ell) U)
    (Btil : Bond L → SuTwo) (hBtil : OnLambdaTilde ell Btil) :
    gammaEll ell * bondEnergy Btil ≤ sandwichForm Δ ell bg k U Btil := by
  have hUk : GaugeRegular (alphaEll ell) (bg k U) := hreg k U hU
  have hCB : Creparam (bg k U) ell Btil
      = fullC (bg k U) ell (dinvC (bg k U) ell) Btil := rfl
  -- step 1: the denotation clause
  have h1 : sandwichForm Δ ell bg k U Btil
      = deltaKQuadFormNormalizedCorrected (bg k U) (Creparam (bg k U) ell Btil) :=
    hden k U (Creparam (bg k U) ell Btil)
  -- step 2: `C B̃` is admissible, unconditionally
  have hax : ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y ell →
      ∀ b ∈ staircasePath y x, Creparam (bg k U) ell Btil b = 0 := by
    rw [hCB]
    exact fullC_unconditional_axialGauge (by omega) hdvd (bg k U) Btil hBtil.1
  have hker : ∀ c : CoarseBond L ell,
      lineCoarseRestrictCov (bg k U) ell (Creparam (bg k U) ell Btil) c = 0 := by
    rw [hCB]
    exact fullC_unconditional_mem_kerQ (by omega) hdvd (bg k U) Btil
  have h2 : gammaEll ell * bondEnergy (Creparam (bg k U) ell Btil)
      ≤ deltaKQuadFormNormalizedCorrected (bg k U) (Creparam (bg k U) ell Btil) :=
    deltaKNormalized_gaugeRegular_coercive_generalEll hell2 hstrict hdvd (bg k U) hUk
      (Creparam (bg k U) ell Btil) hax hker
  -- step 3: `C` does not lose energy
  have h3 : bondEnergy Btil ≤ bondEnergy (Creparam (bg k U) ell Btil) :=
    bondEnergy_le_Creparam (bg k U) Btil hBtil.2
  have hγ : (0:ℝ) < gammaEll ell := gammaEll_pos hell2
  rw [h1]
  calc gammaEll ell * bondEnergy Btil
      ≤ gammaEll ell * bondEnergy (Creparam (bg k U) ell Btil) := by
        exact mul_le_mul_of_nonneg_left h3 (le_of_lt hγ)
    _ ≤ deltaKQuadFormNormalizedCorrected (bg k U) (Creparam (bg k U) ell Btil) := h2

/-- **THE DESIGNED STATEMENT IS TRUE**, at `γ₀ = gammaEll ell`, for every block scale `ell ≥ 2` and
every tiled extent — uniformly in `k`, in `U`, in the ladder, and in the realization of `Δ`.
A corollary of the anchor-free `coercivity_on_lambdaTilde_of_regular_ladder`: the anchor binder is
discarded here because the POSITIVE half does not need it, and that is recorded as a theorem
immediately above rather than asserted in prose. -/
theorem p428Coercivity_holds {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1)) :
    P428Coercivity L ell :=
  ⟨gammaEll ell, gammaEll_pos hell2, fun Δ bg _ hreg hden k U hU Btil hBtil =>
    coercivity_on_lambdaTilde_of_regular_ladder hell2 hstrict hdvd Δ bg hreg hden.1 k U hU
      Btil hBtil⟩

#print axioms coercivity_on_lambdaTilde_of_regular_ladder
#print axioms p428Coercivity_holds

/-! ### §7b — THE PINNING REPAIR IS INERT, AND THIS IS THE PROOF

The §5a conjunct is not a plugged hole. `sandwichForm` is a diagonal, so no property of `Δ` beyond
its DENOTATION can change any value `P428Coercivity` asserts — and therefore the pre-repair
statement
(`P428CoercivityUnpinned`, retained below exactly as it was) and the repaired one are EQUIVALENT.
A campaign reader must not score the conjunct as having closed anything. -/

/-- The pre-repair statement, retained verbatim so the inertness claim has a referent. -/
def P428CoercivityUnpinned (L : PeriodicLatticeExtent) (ell : ℕ) : Prop :=
  ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (Δ : DeltaFam L) (bg : Ladder L),
      AnchoredLadder bg → RegularityPreserving ell bg → DenotesDeltaK Δ bg →
      ∀ (k : ℕ) (U : LinkCfg L), GaugeRegular (alphaEll ell) U →
        ∀ Btil : Bond L → SuTwo, OnLambdaTilde ell Btil →
          γ₀ * bondEnergy Btil ≤ sandwichForm Δ ell bg k U Btil

/-- The sandwich of ANY denoting family is the source's own quadratic form at `C B̃` — no `Δ` left
on
the right-hand side. (LAW-19: this is `coercivity_on_lambdaTilde_of_regular_ladder`'s step `h1`,
named rather than re-proved.) -/
theorem sandwichForm_eq_quadForm {Δ : DeltaFam L} {bg : Ladder L} (hden : DenotesDeltaK Δ bg)
    (ell k : ℕ) (U : LinkCfg L) (Btil : Bond L → SuTwo) :
    sandwichForm Δ ell bg k U Btil
      = deltaKQuadFormNormalizedCorrected (bg k U) (Creparam (bg k U) ell Btil) :=
  hden k U (Creparam (bg k U) ell Btil)

/-- **THE INERTNESS MECHANISM.** Any two families denoting the same ladder give the SAME sandwich,
at
every `ell, k, U, B̃`. The `∀ Δ` binder ranges over a set on which its own conclusion is constant.
-/
theorem sandwichForm_indep_of_denoting {Δ₁ Δ₂ : DeltaFam L} {bg : Ladder L}
    (h1 : DenotesDeltaK Δ₁ bg) (h2 : DenotesDeltaK Δ₂ bg)
    (ell k : ℕ) (U : LinkCfg L) (Btil : Bond L → SuTwo) :
    sandwichForm Δ₁ ell bg k U Btil = sandwichForm Δ₂ ell bg k U Btil := by
  rw [sandwichForm_eq_quadForm h1, sandwichForm_eq_quadForm h2]

/-- The skew-shift special case, proved WITHOUT any denotation hypothesis — so it is a fact about
`sandwichForm`'s shape, not about the denoting set. -/
theorem sandwichForm_add_zeroDiag {Δ : DeltaFam L} {bg : Ladder L}
    {S : BondFnL2 L →L[ℝ] BondFnL2 L} (hS : ZeroDiag S)
    (ell k : ℕ) (U : LinkCfg L) (Btil : Bond L → SuTwo) :
    sandwichForm (fun k U => Δ k U + S) ell bg k U Btil = sandwichForm Δ ell bg k U Btil := by
  show (inner ℝ (WithLp.toLp 2 (Creparam (bg k U) ell Btil) : BondFnL2 L)
      ((Δ k U + S) (WithLp.toLp 2 (Creparam (bg k U) ell Btil))) : ℝ)
    = (inner ℝ (WithLp.toLp 2 (Creparam (bg k U) ell Btil) : BondFnL2 L)
      (Δ k U (WithLp.toLp 2 (Creparam (bg k U) ell Btil))) : ℝ)
  rw [ContinuousLinearMap.add_apply, inner_add_right, hS]
  ring

/-- **THE PINNING REPAIR IS A NO-OP ON THE STATEMENT'S TRUTH VALUE.** Both directions proved; the
non-trivial one routes every denoting `Δ` through `faithfulFamily bg`, which IS pinned. -/
theorem p428Coercivity_iff_unpinned (ell : ℕ) :
    P428Coercivity L ell ↔ P428CoercivityUnpinned L ell := by
  constructor
  · rintro ⟨γ₀, hγ, hb⟩
    refine ⟨γ₀, hγ, fun Δ bg ha hr hden k U hU Btil hBtil => ?_⟩
    have hf := hb (faithfulFamily bg) bg ha hr (faithfulFamily_denotesPinned bg) k U hU Btil hBtil
    rwa [sandwichForm_indep_of_denoting (faithfulFamily_denotes bg) hden] at hf
  · rintro ⟨γ₀, hγ, hb⟩
    exact ⟨γ₀, hγ, fun Δ bg ha hr hp => hb Δ bg ha hr hp.1⟩

#print axioms P428CoercivityUnpinned
#print axioms sandwichForm_eq_quadForm
#print axioms sandwichForm_indep_of_denoting
#print axioms sandwichForm_add_zeroDiag
#print axioms p428Coercivity_iff_unpinned

/-! ### §7c — THE `∀ Δ` BINDER IS ELIMINABLE (the sharpest form of §7b)

§7b says every denoting `Δ` gives the same sandwich. The consequence is stronger than "the skew part
is harmless": **the operator variable carries no content at all.** `P428Coercivity` is equivalent to
a statement in which `Δ` does not occur — a bound on `deltaKQuadFormNormalizedCorrected` alone.

Both edges of this are facts, not verdicts:
* it is why the §5a residual is inert — a variable that can be ELIMINATED cannot be under-pinned in
a
  way that changes anything the statement asserts;
* it is also the exact sense in which whatever `deltaKQuadFormNormalizedCorrected` denotes is the
  WHOLE content of the statement. Since §00 records that what it denotes is p.392 (3.10) and not
  p.428 (3.156), this theorem is precisely where that defect bites hardest.

`∀ Δ` was advertised (old §2 clause table) as killing the S91 hole by uniformity over realizations.
The S91 half is real — there is no `Δ`-SLOT to inhabit, because the binder is universal. The
UNIFORMITY half is decoration, and this is the proof. -/

/-- `P428Coercivity` with the operator variable removed. -/
def P428CoercivityDeltaFree (L : PeriodicLatticeExtent) (ell : ℕ) : Prop :=
  ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ bg : Ladder L, AnchoredLadder bg → RegularityPreserving ell bg →
      ∀ (k : ℕ) (U : LinkCfg L), GaugeRegular (alphaEll ell) U →
        ∀ Btil : Bond L → SuTwo, OnLambdaTilde ell Btil →
          γ₀ * bondEnergy Btil
            ≤ deltaKQuadFormNormalizedCorrected (bg k U) (Creparam (bg k U) ell Btil)

theorem p428Coercivity_iff_deltaFree (ell : ℕ) :
    P428Coercivity L ell ↔ P428CoercivityDeltaFree L ell := by
  constructor
  · rintro ⟨γ₀, hγ, hb⟩
    refine ⟨γ₀, hγ, fun bg ha hr k U hU Btil hBtil => ?_⟩
    have hf := hb (faithfulFamily bg) bg ha hr (faithfulFamily_denotesPinned bg) k U hU Btil hBtil
    rwa [sandwichForm_eq_quadForm (faithfulFamily_denotes bg)] at hf
  · rintro ⟨γ₀, hγ, hb⟩
    refine ⟨γ₀, hγ, fun Δ bg ha hr hden k U hU Btil hBtil => ?_⟩
    rw [sandwichForm_eq_quadForm hden.1]
    exact hb bg ha hr k U hU Btil hBtil

#print axioms P428CoercivityDeltaFree
#print axioms p428Coercivity_iff_deltaFree

/-! ### §7d — NON-VACUITY of the domain: `Λ̃` carries a field of strictly positive energy

A coercivity statement whose domain is `{0}` is satisfied by anything. It is not: the seed
`Pi.single (freeBond ell y) suTwoWitness` lies on `Λ̃` — `freeBond` is on no axial staircase
(`freeBond_not_mem_staircase`) and is the dropped bond of no coarse constraint
(`freeBond_not_dropped`) — and has positive energy. -/

/-- The seed field supported on the single free bond at the origin block. -/
noncomputable def tildeSeed (ell : ℕ) : Bond L → SuTwo :=
  Pi.single (freeBond ell (siteZero L)) suTwoWitness

/-- Its value at the free bond. -/
theorem tildeSeed_at (ell : ℕ) :
    tildeSeed (L := L) ell (freeBond ell (siteZero L)) = suTwoWitness := by
  unfold tildeSeed
  exact Pi.single_eq_same _ _

/-- It vanishes at every other bond. -/
theorem tildeSeed_off {ell : ℕ} {b : Bond L} (h : b ≠ freeBond ell (siteZero L)) :
    tildeSeed (L := L) ell b = 0 := by
  unfold tildeSeed
  exact Pi.single_eq_of_ne h _

/-- **The seed lies on `Λ̃`** — both clauses, at every `ell ≥ 2` and every tiled extent. -/
theorem tildeSeed_onLambdaTilde {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    OnLambdaTilde ell (tildeSeed (L := L) ell) := by
  refine ⟨?_, ?_⟩
  · -- axial: the free bond is on no staircase
    intro y hy x hx b hb
    refine tildeSeed_off ?_
    intro hEq
    exact freeBond_not_mem_staircase hell2 hdvd (siteZero L) (siteZero_coarse ell) y hy x hx
      (hEq ▸ hb)
  · -- no dropped bond is in the support
    intro b hb
    refine tildeSeed_off ?_
    intro hEq
    exact freeBond_not_dropped hell2 hdvd (siteZero L) (siteZero_coarse ell) (hEq ▸ hb)

/-- **The seed has strictly positive energy.** -/
theorem bondEnergy_tildeSeed_pos (ell : ℕ) : 0 < bondEnergy (tildeSeed (L := L) ell) := by
  have hpos : 0 < ‖tildeSeed (L := L) ell (freeBond ell (siteZero L))‖ ^ 2 := by
    rw [tildeSeed_at]
    have : suTwoWitness ≠ 0 := suTwoWitness_ne_zero
    positivity
  have hle : ‖tildeSeed (L := L) ell (freeBond ell (siteZero L))‖ ^ 2
      ≤ ∑ b : Bond L, ‖tildeSeed (L := L) ell b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b : Bond L => ‖tildeSeed (L := L) ell b‖ ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ _)
  unfold bondEnergy
  linarith

/-- **The domain of the designed statement is non-degenerate**: it contains a field of strictly
positive `bondEnergy`, at every `ell ≥ 2` and every tiled extent. -/
theorem lambdaTilde_nonvacuous {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ∃ Btil : Bond L → SuTwo, OnLambdaTilde ell Btil ∧ 0 < bondEnergy Btil :=
  ⟨tildeSeed ell, tildeSeed_onLambdaTilde hell2 hdvd, bondEnergy_tildeSeed_pos ell⟩

/-- **THE S91 MUST-FIRE CONTROL on `lambdaTilde_nonvacuous`.** The zero field — the degenerate
inhabitant of every "there exists an admissible field" statement — does NOT witness it, because
`bondEnergy 0 = 0`. So that existential is not satisfiable by the empty configuration. -/
theorem zeroField_fails_nonvacuity :
    ¬ (0 < bondEnergy (0 : Bond L → SuTwo)) := by
  have h : bondEnergy (0 : Bond L → SuTwo) = 0 := by
    unfold bondEnergy
    simp
  rw [h]
  norm_num

#print axioms tildeSeed
#print axioms tildeSeed_at
#print axioms tildeSeed_off
#print axioms tildeSeed_onLambdaTilde
#print axioms bondEnergy_tildeSeed_pos
#print axioms lambdaTilde_nonvacuous
#print axioms zeroField_fails_nonvacuity

/-! ### §7e — NON-VACUITY of the LADDER hypotheses, and EXACTLY WHAT `varyingLadder` DEMONSTRATES

**Corrected 2026-07-30.** The old text here said `p428Coercivity_holds` "would be worth much less if
the only ladder satisfying its hypotheses were the constant one". Sol compiled the refutation:

```text
constantLadder_makes_faithfulFamily_k_independent :
  faithfulFamily (constLadder L) k₁ U = faithfulFamily (constLadder L) k₂ U
```

and observed that swapping `constLadder` for `varyingLadder` anywhere in this file leaves the same
hypotheses and the same theorem standing. That is correct, and it is recorded as a THEOREM below
(`constLadder_faithfulFamily_k_independent`) rather than paraphrased.

**What `varyingLadder` does NOT demonstrate — do not claim any of this:**
* it does **not** model the source's recursive RG construction. `varyingLadder` uses the input `U`
at
  rung `0` and the FLAT configuration at every later rung. Nothing accumulates; there is no RG map;
* it is **not necessary** to `p428Coercivity_holds`, which is proved uniformly in `bg` and never
  inspects `k` beyond selecting a rung. Every theorem in this file that mentions `varyingLadder`
  also
  holds at `constLadder`;
* consequently the `k` binder of `P428Coercivity` carries **no RG content**. §00's first paragraph
is
  the reason: the tree's quadratic form has no `k` argument at all.

**What it DOES demonstrate, and this is a fact `constLadder` provably cannot supply:** the ladder
hypotheses `AnchoredLadder ∧ RegularityPreserving` do **not** force the operator family to be
`k`-constant. Below, at the same lattice and at a background this file already uses, the varying
ladder produces `faithfulFamily` values that are genuinely DIFFERENT operators at rungs `0` and `1`
(`varyingLadder_faithfulFamily_k_dependent`), while at `constLadder` they are provably EQUAL
(`constLadder_faithfulFamily_k_independent`). So the hypothesis class does not secretly collapse the
`k` index — which is all a non-vacuity control may claim, and less than the old prose claimed. -/

/-- The constant ladder — every rung at the given configuration. -/
def constLadder (L : PeriodicLatticeExtent) : Ladder L := fun _ U => U

theorem constLadder_anchored : AnchoredLadder (constLadder L) := fun _ => rfl

theorem constLadder_regularityPreserving (ell : ℕ) :
    RegularityPreserving ell (constLadder L) := fun _ _ h => h

/-- `trivialU` is regular at the source's threshold, at every extent — needed for the varying
ladder. `frobSupBond (trivialU L) = 0 ≤ alphaEll ell`. -/
theorem trivialU_gaugeRegular_alphaEll {ell : ℕ} (hell2 : 2 ≤ ell) :
    GaugeRegular (alphaEll ell) (trivialU L) :=
  gaugeRegular_of_frobSupBond_le
    (by rw [frobSupBond_trivialU]; exact le_of_lt (alphaEll_pos hell2))

/-- **A ladder that genuinely MOVES with `k`**: rung `0` is the given configuration (the anchor),
every later rung is the flat one. -/
def varyingLadder (L : PeriodicLatticeExtent) : Ladder L :=
  fun k U => if k = 0 then U else trivialU L

theorem varyingLadder_anchored : AnchoredLadder (varyingLadder L) := fun _ => by
  simp [varyingLadder]

theorem varyingLadder_regularityPreserving {ell : ℕ} (hell2 : 2 ≤ ell) :
    RegularityPreserving ell (varyingLadder L) := by
  intro k U h
  by_cases hk : k = 0
  · simpa [varyingLadder, hk] using h
  · simpa [varyingLadder, hk] using trivialU_gaugeRegular_alphaEll (L := L) hell2

/-- **The varying ladder is not the constant one** — at `U = tinyU b₀` its rungs `0` and `1`
differ, so the `k` binder of the designed statement is not carrying a fixed background. -/
theorem varyingLadder_not_constant (b₀ : Bond L) :
    varyingLadder L 1 (tinyU b₀) ≠ varyingLadder L 0 (tinyU b₀) := by
  show (if (1:ℕ) = 0 then tinyU b₀ else trivialU L)
      ≠ (if (0:ℕ) = 0 then tinyU b₀ else trivialU L)
  simp only [if_neg (by decide : ¬ (1:ℕ) = 0)]
  exact fun h => tinyU_ne_trivialU b₀ h.symm

/-- **Both ladders satisfy the designed statement's ladder hypotheses.** -/
theorem varyingLadder_is_admissible {ell : ℕ} (hell2 : 2 ≤ ell) :
    AnchoredLadder (varyingLadder L) ∧ RegularityPreserving ell (varyingLadder L) :=
  ⟨varyingLadder_anchored, varyingLadder_regularityPreserving hell2⟩

/-- **SOL'S REFUTATION, BANKED AS A THEOREM IN THE FILE IT REFUTES.** At the constant ladder the
faithful family does not move with `k` — at ANY pair of rungs, ANY configuration, ANY extent. So the
`k` binder of `P428Coercivity` is carrying nothing whenever `constLadder` is the ladder in play, and
`constLadder` is the ladder every other witness in this file uses. -/
theorem constLadder_faithfulFamily_k_independent (k₁ k₂ : ℕ) (U : LinkCfg L) :
    faithfulFamily (constLadder L) k₁ U = faithfulFamily (constLadder L) k₂ U := rfl

/-- **`Δ_k` at the FLAT background is positive semidefinite**, because `Δ′` vanishes there and what
remains is the covariant Maxwell form `D*D`.

**DAG-FORCED DUPLICATION, disclosed (LAW-19).** `CoercUMainPinned.`
`deltaKQuadFormNormalizedCorrected_trivialU_eq_dstarD` proves the stronger identity, but that module
IMPORTS this one, so the fact cannot be imported back here. Only nonnegativity is needed, and both
ingredients (`CoercivityRegular.deltaKQuadFormNormalizedCorrected_eq_sub`,
`DeltaPrime.deltaPrimeQuadForm_vanishes_at_trivial`) are reachable. The `have` below is what
discharges the defeq between `CovariantHjMinimizer.trivialU` and `DeltaPrime.trivialU` — this tree
carries two syntactically distinct `trivialU`s, and `rw` cannot find the pattern without it. -/
theorem deltaK_trivialU_nonneg (A : Bond L → SuTwo) :
    0 ≤ deltaKQuadFormNormalizedCorrected (trivialU L) A := by
  have h0 : AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadForm (trivialU L) A = 0 :=
    AdalyFormal.Balaban.DeltaPrime.deltaPrimeQuadForm_vanishes_at_trivial A
  rw [deltaKQuadFormNormalizedCorrected_eq_sub, h0]
  have hd := dstarDQuadForm_nonneg (trivialU L) A
  linarith

/-- **WHAT `varyingLadder` IS NECESSARY FOR, and `constLadder` provably cannot supply.** At the
central-holonomy background the varying ladder's faithful family is a genuinely DIFFERENT OPERATOR
at
rung `1` than at rung `0`. Discriminator: the faithful form is `-4` at `(centralHolonomyU,
deltaWitnessConfig)` (`SpineCoercivityInstance.inner_deltaKCLMNormalized_centralHolonomyU`) and is
`≥ 0` at the flat background, so the two operators cannot be equal.

Read together with `constLadder_faithfulFamily_k_independent` this says exactly one thing and no
more: the ladder hypotheses do not force `k`-constancy of the operator family. It is NOT the
source's
RG recursion — see §7e's header for the list of things this does not demonstrate. -/
theorem varyingLadder_faithfulFamily_k_dependent :
    faithfulFamily (varyingLadder witnessL) 1 centralHolonomyU
      ≠ faithfulFamily (varyingLadder witnessL) 0 centralHolonomyU := by
  intro h
  have hden := faithfulFamily_denotes (varyingLadder witnessL)
  have e1 : deltaKQuadFormNormalizedCorrected
        (varyingLadder witnessL 1 centralHolonomyU) deltaWitnessConfig
      = deltaKQuadFormNormalizedCorrected
        (varyingLadder witnessL 0 centralHolonomyU) deltaWitnessConfig := by
    rw [← hden 1 centralHolonomyU deltaWitnessConfig,
      ← hden 0 centralHolonomyU deltaWitnessConfig, h]
  have hv1 : varyingLadder witnessL 1 centralHolonomyU = trivialU witnessL :=
    if_neg (by decide : ¬ (1:ℕ) = 0)
  have hv0 : varyingLadder witnessL 0 centralHolonomyU = centralHolonomyU :=
    if_pos rfl
  rw [hv1, hv0, deltaK_centralHolonomyU_eq_neg_four] at e1
  have hnn := deltaK_trivialU_nonneg (L := witnessL) deltaWitnessConfig
  rw [e1] at hnn
  norm_num at hnn

#print axioms constLadder_faithfulFamily_k_independent
#print axioms deltaK_trivialU_nonneg
#print axioms varyingLadder_faithfulFamily_k_dependent
#print axioms constLadder_anchored
#print axioms constLadder_regularityPreserving
#print axioms trivialU_gaugeRegular_alphaEll
#print axioms varyingLadder_anchored
#print axioms varyingLadder_regularityPreserving
#print axioms varyingLadder_not_constant
#print axioms varyingLadder_is_admissible

/-! ### §7f — THE S91 ATTACK ON `P428Coercivity` ITSELF, RUN AND BLOCKED

`P428Coercivity` has exactly one existential binder: `γ₀`. Two degenerate-inhabitation attacks are
available against a statement of this shape, and both are run here rather than argued.

**Attack 1 — VACUOUS HYPOTHESES.** If no `(Δ, bg)` satisfied `AnchoredLadder ∧ RegularityPreserving
∧ DenotesDeltaK`, or no `U` satisfied `GaugeRegular`, or no field lay on `Λ̃`, the `∀`-body would be
vacuously true and any `γ₀ > 0` would inhabit the statement with no mathematics.
BLOCKED by `p428_hypotheses_satisfiable` (a ladder AND an operator family), by
`trivialU_gaugeRegular_alphaEll` (a regular background at every extent), and by
`lambdaTilde_nonvacuous` (a field of positive energy on `Λ̃`).

**Attack 2 — `γ₀` CHOSEN TO EMPTY THE CLAIM.** BLOCKED by
`p428Coercivity_forces_strict_positivity`: for EVERY `γ₀` the statement can supply, it forces the
source's own quadratic form to be STRICTLY POSITIVE at the named nonzero field `tildeSeed`. Since
`bondEnergy ≥ 0` and `bondEnergy (tildeSeed) > 0`, shrinking `γ₀` weakens the constant but can never
weaken the statement past positivity. There is no admissible `γ₀` at which it says nothing. -/

/-- **Attack 1, blocked**: the `∀`-body's hypotheses are simultaneously satisfiable, by a family that
DENOTES the faithful operator (not by a content-free one). -/
theorem p428_hypotheses_satisfiable (ell : ℕ) :
    ∃ (Δ : DeltaFam L) (bg : Ladder L),
      AnchoredLadder bg ∧ RegularityPreserving ell bg ∧ DenotesDeltaK Δ bg :=
  ⟨faithfulFamily (constLadder L), constLadder L, constLadder_anchored,
    constLadder_regularityPreserving ell, faithfulFamily_denotes (constLadder L)⟩

/-- **Attack 1, blocked at a `k`-VARYING ladder too.** Read this at the strength §7e establishes and
no higher: it shows the hypothesis class does not force `k`-constancy of the background (and, via
`varyingLadder_faithfulFamily_k_dependent`, not of the operator either). It does NOT show the
statement needs `k`-variation — `constLadder_faithfulFamily_k_independent` proves the same theorem
stands at a `k`-constant family. -/
theorem p428_hypotheses_satisfiable_varying {ell : ℕ} (hell2 : 2 ≤ ell) :
    AnchoredLadder (varyingLadder L) ∧ RegularityPreserving ell (varyingLadder L) ∧
      DenotesDeltaK (faithfulFamily (varyingLadder L)) (varyingLadder L) :=
  ⟨varyingLadder_anchored, varyingLadder_regularityPreserving hell2,
    faithfulFamily_denotes (varyingLadder L)⟩

/-- **Attack 2, blocked.** Whatever `γ₀` the designed statement supplies, it forces
`⟪B̃, C*Δ_kC B̃⟫ > 0` at the named nonzero `Λ̃`-field. So no admissible `γ₀` makes it content-free. -/
theorem p428Coercivity_forces_strict_positivity {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (h : P428Coercivity L ell)
    (k : ℕ) (U : LinkCfg L) (hU : GaugeRegular (alphaEll ell) U) :
    0 < sandwichForm (faithfulFamily (constLadder L)) ell (constLadder L) k U
      (tildeSeed (L := L) ell) := by
  obtain ⟨γ₀, hγ, hbound⟩ := h
  have hb := hbound (faithfulFamily (constLadder L)) (constLadder L) constLadder_anchored
    (constLadder_regularityPreserving ell) (faithfulFamily_denotesPinned (constLadder L)) k U hU
    (tildeSeed ell) (tildeSeed_onLambdaTilde hell2 hdvd)
  have hE : 0 < bondEnergy (tildeSeed (L := L) ell) := bondEnergy_tildeSeed_pos ell
  have hprod : 0 < γ₀ * bondEnergy (tildeSeed (L := L) ell) := mul_pos hγ hE
  linarith

#print axioms p428_hypotheses_satisfiable
#print axioms p428_hypotheses_satisfiable_varying
#print axioms p428Coercivity_forces_strict_positivity

/-! ## §8 — THE ANATOMY: the source hypotheses do NOT reject junk, and this is the proof

The coordinator's live hypothesis when this lane was dispatched was that restoring the source's
hypotheses "may exclude both families for free, because neither junk operator has anything to do
with a regular background or a constrained subspace". **That is false, and the falsity is one
theorem.** The identity family satisfies the FULL designed inequality — the source's regularity
restriction, the source's `Λ̃` domain, the source's `C` sandwich, every rung, every ladder — with
`γ₀ = 1`, and it does not even need the regularity hypothesis.

The reason is structural: restricting the DOMAIN can only make a coercivity clause easier, and
restricting the BACKGROUND can only make it easier. Junk-rejection therefore cannot come from
hypotheses at all; it can only come from a clause that pins what the operator IS. -/

/-- **The designed statement with the denotation clause DELETED and `Δ` existentially quantified —
i.e. `coerc_u_main`'s own shape, with all of the source's hypotheses restored.** -/
def ExistentialFormWithoutDenotation (L : PeriodicLatticeExtent) (ell : ℕ) : Prop :=
  ∃ (Δ : DeltaFam L) (γ₀ : ℝ), 0 < γ₀ ∧
    ∀ bg : Ladder L, AnchoredLadder bg → RegularityPreserving ell bg →
      ∀ (k : ℕ) (U : LinkCfg L), GaugeRegular (alphaEll ell) U →
        ∀ Btil : Bond L → SuTwo, OnLambdaTilde ell Btil →
          γ₀ * bondEnergy Btil ≤ sandwichForm Δ ell bg k U Btil

/-- **THE CONTROL, and the load-bearing negative of this file.** The source's hypotheses restored in
full still leave the statement inhabited by the IDENTITY, at every `ell` and every extent, with no
regularity used. So requirement (a) is NOT bought by requirement (d): a statement can be perfectly
faithful in its hypotheses and still say nothing. -/
theorem existentialForm_withoutDenotation_holds_by_junk (ell : ℕ) :
    ExistentialFormWithoutDenotation L ell := by
  refine ⟨fun _ _ => ContinuousLinearMap.id ℝ (BondFnL2 L), 1, one_pos, ?_⟩
  intro bg _ _ k U _ Btil hBtil
  have hform : sandwichForm (fun _ _ => ContinuousLinearMap.id ℝ (BondFnL2 L)) ell bg k U Btil
      = bondEnergy (Creparam (bg k U) ell Btil) := by
    show (inner ℝ (WithLp.toLp 2 (Creparam (bg k U) ell Btil) : BondFnL2 L)
      (WithLp.toLp 2 (Creparam (bg k U) ell Btil)) : ℝ) = _
    rw [real_inner_self_eq_norm_sq, norm_sq_bondFnL2]
  rw [hform, one_mul]
  exact bondEnergy_le_Creparam (bg k U) Btil hBtil.2

#print axioms ExistentialFormWithoutDenotation
#print axioms existentialForm_withoutDenotation_holds_by_junk

/-! ## §9 — RECONCILIATION WITH `CoercUMainKernel` (dispatch item 5)

**Verdict: `HasKernel`/`KernelMono`/`KernelGrows`/`NotScaledProjection` were addressing the WRONG
AXIS, and this file does not adopt any of them.** Three reasons, each a fact and not a preference.

1. **They are shape conditions, and shape conditions provably cannot separate the two junk
   families.** The tree's own controls cross (§0's table): K1∧K2∧K3 admits `chainDelta`, K5 admits
   `jDelta`. `CoercUMainKernel`'s own docstring reaches the same conclusion from the other side —
   *"Content has to come from pinning `Δ` itself"* — and `Spine.lean` states that adopting
   `KernelStrengthened` "would therefore not repair the `sorry`". The denotation clause is that
   pinning, and it kills BOTH families with ONE theorem (§6a-§6c), needing no condition whatever on
   the chain.
2. **A kernel demand pulls AGAINST the source's own conclusion.** `CoercivityHypothesis.coercive`
   is a strict lower bound on `V`, so any conjunct forcing `Δ` to annihilate a nonzero vector OF
   `V` makes the statement false, not merely open (`Spine.lean` §1a-R (R3) says this in full). The
   designed statement therefore does not demand a kernel — and it does not FORBID one either: it is
   silent about `ker Δ`, which is the correct posture, because `ker Δ_k` is a computable property of
   a pinned operator and not a design choice.
3. **They are on the wrong carrier as well.** `HasKernel` etc. are stated over
   `Anchoring.AnchoredBondSpace` (fibre dimension 1); the faithful operator provably does not live
   there (§4). So even if a kernel condition were the right axis, it could not be evaluated at the
   object p.428 is about.

**What IS retained from that work**: its two negative results are load-bearing inputs to this
design, and this file cites them rather than re-deriving them. `no_kernel_growth_at_every_rung`
(a finite-dimensional ceiling on kernel growth) and `kernelStrengthened_of_chain` (a content-free
projector inhabits the whole strengthened conclusion) are together the proof that the shape axis is
exhausted. Without them, this file's choice of axis would be a guess.

## §10 — THE CARRIER OBSTRUCTION, re-exported so §4's argument carries its evidence -/

/-- **`coerc_u_main`'s carrier cannot host the faithful operator** — for every extent. The theorem
is `IslandBridge`'s; it is re-exported at this file's own naming so §4's retirement argument is one
`#check` away from its evidence, not one file away (LAW-19: the term is not re-derived). -/
theorem carrier_obstruction (L : PeriodicLatticeExtent) :
    IsEmpty (EuclideanSpace ℝ (Bond L) ≃ₗ[ℝ] BondFnL2 L) :=
  no_linearEquiv_euclid_bondFnL2 L

#print axioms carrier_obstruction

end AdalyFormal.Balaban.CoercUMainDesigned
