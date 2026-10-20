/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib
import AdalyFormal.Balaban.Blocks
import AdalyFormal.Balaban.DeltaKRecursive

set_option autoImplicit false

/-!
# `Q` (specialized) and `G₁` (the (3.138) Neumann series) — CMP99b's covariance chain

## ⚠ BANNER — `QData`/`QMap`/`QLinearMap` REALIZE THE **PRIMED** `Q'`, THE GAUGE/SITE-SECTOR
## OPERATOR, NOT THE BOND-SECTOR `Q`. THE PRIME WAS DROPPED FROM THE NAMES. (denotation-dictionary
## finding; NAMES DELIBERATELY NOT CHANGED — several lanes touch this file family)

**What is actually built here.** `QMap`'s body is `∑ x ∈ Qd.B y, (L^d)⁻¹ • Rconj y x (μ x)`, of
type `(Site → 𝔤) → (Center → 𝔤)`. That is, verbatim, the PRIMED operator of CMP99b p.430 (3.169),
`(Q'μ)(y) = Σ_{x∈B(y)} L⁻ᵈ R(V(Γ_{y,x}))μ(x)` — quoted correctly in §0 below, image-verified again
by the repair lane at 300 dpi (`compute/mismatch_repairs/p430_b.png`, rendered from
`compute/balaban_su2_papers/balaban_CMP99_1985_propagators_backgroundfield.pdf` pdf-page 42, printed
header "430  T. Balaban" visible at `p430_header.png`). Dictionary rows:
`compute/denotation_dict/DENOTATION_DICT.tsv` → `qprime_defining_p430_3169` (`printed_symbol = Q'`,
`sector = gauge_site`, `weight = L^-d`, `lean_status = MISMATCH`, `lean_decl =
CovarianceG1.QMap / QLinearMap`) and `qprime_onestep_gauge_QprimeV` (CMP99b p.393 (3.18), `Q'(V)`,
`sector = gauge_site`, `weight = L^-d`, also `MISMATCH`, naming `QMap / QLinearMap / QData`).

**THE PRIME IS NOT A DECORATION, AND NOT A TYPOGRAPHIC SLIP.** `Q'` and `Q` are DIFFERENT
OPERATORS in Bałaban's own notation: different sector (gauge/site-valued `λ`,`μ` versus bond-valued
`A`), different codomain, and a different weight — `η^d` versus `η^{d+1}`. The split is stated
outright on a single page of the earliest paper of the series, CMP95 printed p.20, now confirmed at
600 dpi (`compute/cmp98_defining/RENDER_HASHES.txt`, cmp95 renders; independently at 300 dpi by
this repair lane, `compute/mismatch_repairs/p20_eq118.png`, `p20_prose.png`): (1.18)
`(Q_kA)_b = Σ_{x∈B^k(b₋)} η^{d+1} A([x,x(b)])` for the BOND sector, and (1.20)
`(Q'_kλ)(y) = Σ_{x∈B^k(y)} η^d λ(x)` for the GAUGE/SITE sector. Dropping the prime therefore
silently swaps one operator for another, and it is exactly the loss of this `η^{d+1}` vs `η^d`
distinction that the denotation dictionary flagged here. Evidence rows for the two CMP95 readings:
`compute/cmp98_defining/NEW_DICT_ROWS.tsv` `cmp95_qk_bond_118` and `cmp95_qkprime_gauge_120`.

**What the bond-sector `Q` is, and why the weight differs.** The unprimed bond-sector one-step
operator is dictionary row `q_onestep_template_QV` (CMP99b p.393 (3.15): `Q_j(U) =
Q(Ū^{j-1})⋯Q(Ū)Q(U)`, "where `Q(V)` is given by the explicit formula (124) in [5]" — the prefactor
is NOT printed on p.393, it is deferred to CMP98 (124); image-verified by the repair lane at
`compute/mismatch_repairs/p393_a.png`). The sector split is explicit in the earliest paper of the
series, CMP95 printed p.20, image-verified by the repair lane
(`compute/mismatch_repairs/p20_eq118.png`, `p20_prose.png`): eq. (1.18) gives the BOND-sector `Q_k`
with coefficient `η^{d+1}`, and (1.20) gives the SITE/gauge-sector `Q_k'λ(y) = Σ_{x∈B^k(y)} η^d λ(x)`
with coefficient `η^d`. So the weight is fixed by the SECTOR (bond vs gauge-site), not by the domain
scale: `L^{-(d+1)}` for bonds, `L^{-d}` for gauge parameters. Dictionary rows recording
`L^{-(d+1)}` for the bond-sector `Q_1`: `q96_q1_defining_2125`, `q1_unit_to_coarse_p427_3155`,
`q1_unit_to_coarse_p428_subspace`, `q96_qbare_unit_to_coarse_2153`.

**The correctly-named flat twin already exists (LAW-19).**
`AdalyFormal.Balaban.KernelSubspace.coarseRestrictSite` is the `U=1` (flat) `Q'` with the correct
`L^{-d} = 1/ell³` weight and the correct site→site typing, and it is correctly NAMED `Q'_j`
(dictionary row `qprime_bare_p418_generic`, `lean_status = partial`, whose note reads: "It is the
right home for the covariant `Q'`; `CovarianceG1.QMap` duplicates it covariantly under the WRONG
name"). This file's `QMap` is therefore the COVARIANT `Q'`, under a `Q`-family name.

**Consumer instruction.** Read every `Q…` name in this file as `Q'…` (gauge/site sector, weight
`L^{-d}`). Do NOT instantiate these declarations for a BOND-sector `Q`/`Q₁`: the bond-sector
operator carries the extra `L^{-1}` line-mean factor (CMP95 (1.18); the bond-sector Lean objects are
`LineIntegralAveraging.lineCoarseRestrict` and `LineIntegralCovariant.lineCoarseRestrictCov`). No
declaration, statement or proof in this file is changed by this banner; it is a denotation
disclosure only.

**Dispatch target**: `DeltaKRecursive.lean`'s ingredient inventory named `Q` as **CLOSE**
(`Averaging.lean` has a generic block-average FRAMEWORK never specialized to CMP99b's own `Q`) and
`G₁` as **LACK** (needing "the (3.138)-derived construction"). This file closes both, and then
characterizes PRECISELY what happens when the result is threaded into `RGScaleFamily.feed`.

## §0 — sources, rendered/read directly (LAW-11), not assumed from prior lanes

* **(3.138) itself is NOT on CMP99b pp.427–429** (the pages the dispatch pointed at, and the only
  CMP99b pages this tree had already rendered/adjudicated under `corpus/pages/`). It is on **printed
  p.423** (pdf page 35 of `compute/balaban_su2_papers/balaban_CMP99_1985_propagators_backgroundfield.pdf`,
  offset 388 per `corpus/tools/page_offsets.json`'s CMP99b entry, confirmed `constant_verified` and
  reused here, not re-derived). Rendered fresh at 400 dpi this session:
  `compute/g1_renders/CMP99b_pdf35-35.png` (also `pdf34,36,37,38` for context/cross-check).
  **Printed header verified**: "Propagators for Lattice Gauge Theories / 423" visible at the top of
  the render — the exact trap the dispatch warned about (a prior render mislabelled pp.18-20 while
  its header read p.18) is checked and clean here.

* **(3.138), VERBATIM** (p.423, top of page, immediately after (3.137)):

  ```
  G₁ = G₀(I − (Δ'_π + Δ⁽²⁾_π)G₀)⁻¹ = Σ_{n=0}^∞ G₀((Δ'_π + Δ⁽²⁾_π)G₀)ⁿ.        (3.138)
  ```

  Ingredients, all page-cited and read directly (`compute/g1_renders/CMP99b_pdf34-34.png` =
  printed p.422, `CMP99b_pdf35-35.png` = printed p.423, `corpus/pages/CMP99b_p421.md` = printed
  p.421, already adjudicated):
  * `G₀ = (Δ + DRD* + Q*aQ)⁻¹` — p.421, "the operator we have investigated in previous sections."
  * `Δ⁽²⁾` — p.422, (3.134): `⟨A,Δ⁽²⁾A⟩ = 2⟨HC⁽²⁾(A),J⟩`.
  * `Δ'_π` — p.421 (3.128)'s second quadratic form (the analogue used for the UN-subscripted `G`'s
    own (3.130) recursion, `G = G₀(I − Δ'_π G₀)⁻¹`; (3.138) is the SAME shape, generalized by
    replacing the single perturbation `Δ'_π` with the SUM `Δ'_π + Δ⁽²⁾_π`).
  * `Δ⁽²⁾_π` — p.423, (3.135): `Δ⁽²⁾_π = Δ⁽²⁾ − DRG'D*Δ⁽²⁾ − Δ⁽²⁾DG'RD* + DRG'D*Δ⁽²⁾DG'RD*`.

  **(3.130), for comparison** (p.421, the UN-subscripted `G`'s own Neumann series, same shape,
  ONE perturbation term): `G = G₀(I − Δ'_π G₀)⁻¹ = Σ_{n=0}^∞ G₀(Δ'_π G₀)ⁿ`. (3.138) is this same
  algebraic pattern with the combined perturbation `Δ'_π + Δ⁽²⁾_π` in place of `Δ'_π` alone —
  confirmed directly against the source, not inferred.

* **`Q`'s defining formula — printed p.430** (`corpus/pages/CMP99b_p430.md`, `verification_status:
  adjudicated`), the ONLY place in this tree's currently-rendered CMP99b page set where a `Q`-family
  operator's arithmetic action is spelled out (as opposed to merely named/used):

  ```
  (Q'μ)(y) = Σ_{x∈B(y)} L⁻ᵈ R(V(Γ_{y,x})) μ(x),     y ∈ Λ′.
  ```

  This is `Q'` (the Faddeev-Popov gauge-fixing instance, one RG-level up, acting on the coarse
  gauge parameter `μ`), not literally the base-level `Q`/`Q₁` of (3.156) — ~~Bałaban never
  re-derives the `Q`-family's arithmetic shape from scratch at each occurrence; every occurrence
  (`Q`, `Q₁`, `Q'`, `Q̃`, …) is the SAME defining pattern (linear block-average, weight `L⁻ᵈ`, each
  summand conjugated by the parallel-transport-by-holonomy operator `R(·)`) instantiated at a
  different domain scale.~~ **← SUPERSEDED (denotation-dictionary repair; see the BANNER at the top
  of this header). RETAINED STRUCK, NOT DELETED.** The struck sentence is FALSE in its weight
  clause: the weight is fixed by the SECTOR, not by the domain scale. CMP95 printed p.20 gives
  `η^{d+1}` for the BOND-sector `Q_k` (1.18) and `η^d` for the GAUGE/SITE-sector `Q'_k` (1.20) on
  one and the same page (600 dpi: `compute/cmp98_defining/RENDER_HASHES.txt`; 300 dpi:
  `compute/mismatch_repairs/p20_eq118.png`, `p20_prose.png`). What IS shared across occurrences is
  the LINEAR BLOCK-AVERAGE-WITH-`R(·)`-CONJUGATION SHAPE; the prefactor is not. This file builds
  that shared shape AT THE GAUGE/SITE SECTOR's weight `L⁻ᵈ`, i.e. it builds `Q'`, and the
  bond-sector `Q`/`Q₁` (weight `L^{-(d+1)}`) is NOT an instance of it — see §1's docstring for
  exactly what is and is not claimed, and the top banner for the consumer instruction.

## §0b — Q is **NOT** the same object as `Averaging.lean`'s `averageAt`/`linearAverageAt`

Checked directly (LAW-19's mandate: never assume a same-shaped object in the tree matches):

| | `averageAt` (eq. 15) | `linearAverageAt` (eq. 14) | `Q'` (this file, p.430 — PRIMED, see BANNER) |
|---|---|---|---|
| Codomain | group `G` (nonlinear: `exp(Σ log(·))·U(c)`) | Lie algebra `𝔤` (linear) | Lie algebra `𝔤` (linear) |
| Weight | `L⁻ᵈ` | `L⁻⁽ᵈ⁺¹⁾` | `L⁻ᵈ` |
| Conjugation | n/a (nonlinear log/exp already carries it) | **none** — plain sum of `Γcontour` | **`R(V(Γ_{y,x}))`** on every summand |

`Q` shares its WEIGHT with `averageAt` (both `L⁻ᵈ`, both the "adopted going forward" convention) but
is LINEAR where `averageAt` is not; `Q` shares LINEARITY with `linearAverageAt` but differs in BOTH
weight (`L⁻ᵈ` vs `L⁻⁽ᵈ⁺¹⁾`) and structure (`linearAverageAt` sums a bare contour value with no
conjugation factor at all; `Q` conjugates every summand by `R(V(Γ_{y,x}))`, the holonomy-dependent
piece that is the exact load-bearing ingredient `Averaging.lean`'s own docstring predicted would be
needed and did not build). **Verdict: `Q` is a third, genuinely distinct operator** — the CLOSE
verdict in `DeltaKRecursive.lean`'s inventory ("framework exists, this specific instance does not")
is confirmed precisely, and sharpened: the missing ingredient is specifically the `R(·)`-conjugation,
not merely a domain restriction.

## ⚖ CANONICAL RULING ON `Q` vs `Q₁` — READ THIS BEFORE §0c (2026-07-26)

**Adjudication document: `compute/q1_adjudication/RULING.md`** (verbatim quotes + 600-dpi renders,
every load-bearing page image-verified). **Counterpart header: `Balaban/BackgroundAveraging.lean`
lines 16-20**, which banked the OPPOSITE ruling ("`Q₁(U) = Q(U)`"). The tree carried both,
unreconciled, and the `C*Δ_kC` line was built on that one. Both are PARTIALLY RIGHT.

**VERDICT: SAME MAP, DIFFERENT LEVELS.**

| symbol in (3.155)-(3.159) | domain | codomain |
|---|---|---|
| `Q` (in `δ(QA−B)`, `(QG₁Q*)⁻¹`) | **fine** lattice `T_η` (variable `A`) | unit lattice `Λ ⊂ Λ_k = Ω_k^{(k)}` |
| `Q₁` (in `δ(Q₁B)`, `Q₁B=0`) | **unit** lattice `Λ` (variable `B`) | `Λ'`, one level ABOVE the unit lattice |

§0c below is **RIGHT that they are different arrows** — that is the half the other header missed,
and it is the load-bearing half. It is **WRONG that `Q₁` is an unlocated seventh ingredient**: it is
the SAME one-step averaging template one level up, and §0c's own guess ("or in [4] (CMP96)") was
correct. **`Q₁`'s defining formula is CMP96 p.245 (2.125)** — image-verified at 600 dpi:
`(Q₁B)(c) = Σ_{x∈B(c₋)} L^{−(d+1)} B([x, x+Le_μ])`, a unit-lattice bond field averaged onto coarse
bonds — exactly where CMP99b p.428 sends the reader (*"in the same way as in [4] (2.154-2.155)"*).
CMP96 p.241 (2.103) gives the composition law `Q'_{j+1} = Q'₁ ∘ Q'_j` with `Q'₁` applied to `μ`
*"defined on the unit lattice"*; that law is what makes both banked readings simultaneously true.
And CMP99b p.428 itself writes the SAME constraint's component form as bare **`(QB)(c) = 0`**, two
lines under `Q₁B = 0`, while the display above uses bare `Q` for the fine→unit arrow — **on one page
the bare symbol denotes two different arrows.** That is the trap, in the author's own hand.

**⚠ SEPARATE CORRECTION TO §0c'S SECOND BULLET (S75, in place):** §0c reads the prime in
`Q'`/`Q'₁` on pp.429-430 as *"one level up"*. **It is not a level.** The prime marks the
**GAUGE-FUNCTION (site/scalar) sector**: CMP99b p.393 **(3.18)-(3.19)** define `Q'` acting on gauge
functions `λ` with weight `L^{−d}`, whereas the unprimed operators act on **bond** fields with
weight `L^{−(d+1)}` (CMP96 (2.125)). The `Q`-vs-`Q₁` pairing does recur on pp.429-430, but as the
*same* fine-vs-unit level pair inside the gauge sector.

**⚠ CONSEQUENCE FOR §1 BELOW — FINDING, NOT REPAIRED (comment-only write scope).** `QMap`/
`QLinearMap` is `(Qμ)(y) = Σ_{x∈B(y)} (L^d)⁻¹ • Rconj y x (μ x)`: weight `L^{−d}`, source's own
variable name `μ`, site-indexed output. Measured against source that is **`Q'(V)` of (3.18)/(3.19),
the one-step GAUGE-FUNCTION averaging** — faithful to that object, but **mis-labelled as the
bond-sector `Q`** of `(QG₁Q*)⁻¹`, which is a different sector (bond, weight `L^{−(d+1)}`) AND a
composite (fine→unit) rather than a one-step map. §0c even quotes the formula *with* the prime and
§1 then drops it.

**AND THE BOND-SECTOR `Q` DOES EXIST IN THE TREE** — `LineIntegralCovariant.lineCoarseRestrictCov
U ell` / `QOne.qOnePathSum ell` / `BackgroundAveraging.qPrimeSuTwo ell`, all
`(1/(ell:ℝ)^4) • ∑ x ∈ blockOf …`, are ONE **level-generic** template with the block side `ell`
free. **`ell` IS Bałaban's level index**, as (3.19) requires: the `j`-step operator is the one-step
formula with `L → L^j`, so `1/ell⁴ = (L^j)^{−(d+1)}` at `d = 3` is correct at every level.
`[CSTAR-LEVEL-MISMATCH]` was therefore **not a missing object** but that one family instantiated at
**ONE `ell` for BOTH roles**; the repair is `ell₀ ∣ ell₁`, `ell₁/ell₀ ≥ 2` — see
`Balaban/CStarLevelCorrected.lean`, which reached this verdict independently.
(An earlier draft of this note claimed no such object exists; **wrong**, struck — RULING.md §5a.)

**Residual left open (earned, not elected): `[Q1-BACKGROUND-ARG]`** — which configuration `V` enters
`Q₁`'s `R(V(Γ))`. Inference from (3.15)'s pattern (NOT verbatim): `Q(Ū^k)`. See RULING.md §3.

## §0c — **`Q₁` IS A SEVENTH INGREDIENT, GENUINELY DISTINCT FROM `Q`, AND ITS DEFINITION IS NOT
LOCATED in the currently-rendered page set (checked directly, not assumed)

**⚠ S75 — PARTIALLY SUPERSEDED 2026-07-26 by `compute/q1_adjudication/RULING.md` §4. Retained
struck, not deleted.** Read the ruling above first: the "different arrows" finding STANDS; the
"~~genuinely distinct seventh ingredient~~" and "~~currently-UNLOCATED~~" conclusions are CLOSED
(same map, one level up; defined at CMP96 (2.125)), and the "~~one level up, with a prime~~" reading
of `Q'`/`Q'₁` is corrected to *gauge-function sector* above.

A concurrent prosecution of `DeltaKRecursive.lean` (commit `0c1dc1bf`) flagged, correctly, that
(3.156)'s own restriction clause reads `{B : B=0 on Λ^c, B=0 on ∪_{y∈Λ'}Ax(y), **Q₁B=0**}` — a
DIFFERENT symbol from the `Q` inside `(QG₁Q*)⁻¹` in the SAME equation — and that `RGScaleFamily` has
no `Q₁` field at all. Checked here directly against every page rendered/read this session
(pp.421–430, `compute/g1_renders/CMP99b_pdf34-38.png`, `corpus/pages/CMP99b_p427-430.md`):

* **`Q` and `Q₁` are used as visibly distinct symbols in the SAME equation, repeatedly, at TWO
  different scales**: base scale, p.427/428, `(QG₁Q*)⁻¹` vs. `δ(Q₁B)`/`Q₁B=0` (eqs. 3.155, 3.156);
  extended scale, p.429/430, `(Q'μ)` (spelled out, (3.169)) vs. `δ(Q₁'μ)` (used, (3.168)) — the SAME
  `Q`-vs-`Q₁` pairing recurs ~~one level up, with a prime on both symbols~~ **[S75: in the
  GAUGE-FUNCTION sector; the prime is a sector marker, not a level — (3.18)-(3.19)]**. This internal
  consistency
  (two visually distinct symbols, paired the same way at two different scales) is strong evidence
  they are ~~genuinely different operators~~ **[S75: genuinely different ARROWS of one operator
  template — same map, different levels]**, not a notational accident.
* **`Q`'s own arithmetic action is recoverable from the text** — p.428: *"the equation `(QB)(c) = 0`,
  considered as an equation on the variable `B(b₀)`"* (`Q` applied directly to `B`, block-index `c`),
  and p.430 spells out `(Q'μ)(y) = Σ_{x∈B(y)} L⁻ᵈR(V(Γ_{y,x}))μ(x)` for the one-level-up analogue —
  this is what §1 above builds.
* **`Q₁`'s own arithmetic action is NOT spelled out anywhere in pp.421–430** (checked page-by-page,
  including the two pages between (3.138) and (3.155), pp.424–426, `CMP99b_pdf36-38.png`, which
  develop `𝔓`, `𝔊`, (3.139)–(3.153) — none of it defines `Q₁`). `Q₁`/`Q₁'` appear only INSIDE
  gauge-fixing delta-functions (`δ(Q₁B)`, `δ(Q₁'μ)`), always alongside `Q`/`Q'`, never independently
  introduced or expanded on these pages.

~~**Verdict: `Q₁` is a genuinely distinct, currently-UNLOCATED seventh ingredient**~~ (alongside the
six
already named in `THE_LEMMA.md`'s inventory: `Q`, `G₁`, `a`, `H₁`, `D̃⁽²⁾`, `J`) — not built by this
file, not fabricated here, precisely because its defining formula was not found in the page range
this session actually rendered and read. It most likely lives earlier in the paper (§A–D, pp.392–420,
where the base `Q`-family and the gauge-fixing conditions (3.109)/(3.110) are first set up) or in [4]
(CMP96) — outside this dispatch's write scope and this session's render budget. **Named, not hidden,
not guessed at.**

**⚠ S75 — VERDICT SUPERSEDED 2026-07-26 (`compute/q1_adjudication/RULING.md`).** The guess in the
last sentence was RIGHT: it is in **[4] (CMP96), p.245 (2.125)**, image-verified at 600 dpi.
`Q₁` is **NOT a seventh ingredient** and is **NOT unlocated**: it is the SAME one-step block-average
template as `Q`, applied one level up (**unit lattice → `Λ'`**, weight `L^{−(d+1)}`, bond sector),
while `Q`'s domain in `(QG₁Q*)⁻¹`/`δ(QA−B)` is the **fine** lattice. What the tree actually lacks is
a Lean object for **`Q` itself** (fine → unit, bond sector) — that one does not exist anywhere.
-/

namespace AdalyFormal.Balaban.CovarianceG1

/-! ## §1 — `Q`, specialized: a genuine linear, `R`-conjugated, weight-`L⁻ᵈ` block average

**What is and is not claimed.** This section builds the SHARED ARITHMETIC SHAPE of CMP99b's
`Q`-family (linear, block-summed, `L⁻ᵈ`-weighted, `R`-conjugated), reusing `Blocks.lean`'s
`BlockGeometry` (`B`, `L`, `d`, `card_block` — LAW-19, not rebuilt) and carrying the conjugation
family `Rconj` as an explicit field, standing for CMP99b's `R(V(Γ_{y,x}))` (page-cited above). It
does **not** re-derive the SU(2)-specific `RMap`/holonomy/periodic-lattice machinery
(`CovariantOperators.lean`) that would be needed to instantiate `Rconj` concretely for the actual
Yang-Mills lattice — doing so here would re-import the whole `PeriodicLattice`/`SuTwo` stack this
file, like `DeltaKRecursive.lean` before it, deliberately stays clear of (§0's own docstring
precedent). The bridge is real but left as a named residual (§1's closing remark below), not papered
over as already built. -/

variable {Site Center 𝔤 : Type*} [Fintype Site] [DecidableEq Site] [Fintype Center]
  [DecidableEq Center] [NormedAddCommGroup 𝔤] [InnerProductSpace ℝ 𝔤]

/-- **`Q`'s full data**: a `BlockGeometry` (`B`, `L`, `d`, reused unchanged from `Blocks.lean`) plus
the conjugation family `Rconj : Center → Site → (𝔤 →ₗ[ℝ] 𝔤)`, standing for `R(V(Γ_{y,x}))` — the ONE
ingredient `Averaging.lean`'s generic framework never carried (§0b).

**DENOTATION (banner, top of file): this is `Q'`-DATA — the PRIMED, gauge/site-sector operator's
data, weight `L⁻ᵈ`.** The name drops the prime. Dictionary rows `qprime_defining_p430_3169`,
`qprime_onestep_gauge_QprimeV` (both `sector = gauge_site`, `weight = L^-d`, both `MISMATCH`,
`lean_decl = CovarianceG1.QMap / QLinearMap / QData`). Not renamed in this pass by design. -/
structure QData (Site Center 𝔤 : Type*) [Fintype Site] [DecidableEq Site] [Fintype Center]
    [DecidableEq Center] [NormedAddCommGroup 𝔤] [InnerProductSpace ℝ 𝔤]
    extends AdalyFormal.Balaban.BlockGeometry Site Center where
  /-- `R(V(Γ_{y,x}))`, p.430 — the parallel-transport-by-holonomy conjugation, linear because it is
  the adjoint action of a fixed group element (matching `CovariantOperators.RMap`'s own linearity,
  reused here only at the level of its SHAPE, not its concrete SU(2) instance — see §1's closing
  remark). -/
  Rconj : Center → Site → (𝔤 →ₗ[ℝ] 𝔤)

/-- **`(Q'μ)(y) = Σ_{x∈B(y)} L⁻ᵈ • R(V(Γ_{y,x}))(μ(x))`**, CMP99b p.430 (3.169), literally — the
PRIMED, gauge/site-sector operator (image-verified 300 dpi, `compute/mismatch_repairs/p430_b.png`;
600 dpi `compute/cmp98_defining/RENDER_HASHES.txt`). The Lean NAME drops the prime; the BODY is
correct for `Q'`.

**Do not instantiate this for a bond-sector `Q`/`Q₁`.** Bond-sector averaging carries the extra
line-mean factor: CMP95 (1.18) `η^{d+1}` versus (1.20)'s `η^d` here. The bond-sector Lean objects
are `LineIntegralAveraging.lineCoarseRestrict` (flat) and
`LineIntegralCovariant.lineCoarseRestrictCov` (covariant). The correctly-NAMED flat twin of THIS
declaration is `KernelSubspace.coarseRestrictSite` (dictionary row `qprime_bare_p418_generic`).
Dictionary rows for this declaration: `qprime_defining_p430_3169`, `qprime_onestep_gauge_QprimeV`
(both `MISMATCH`, on the NAME only). Not renamed in this pass by design (banner, top of file). -/
noncomputable def QMap (Qd : QData Site Center 𝔤) (μ : Site → 𝔤) (y : Center) : 𝔤 :=
  ∑ x ∈ Qd.B y, ((Qd.L : ℝ) ^ Qd.d)⁻¹ • Qd.Rconj y x (μ x)

/-- **`Q` is genuinely `ℝ`-linear in `μ`** — bundled as a `LinearMap`, matching CMP99b's own
treatment of `Q` as a linear operator (used with `Q*`, `(QG₁Q*)⁻¹`, etc. throughout (3.155)-(3.156)),
not merely a function.

**DENOTATION (banner, top of file): the bundled map is `Q'`, the PRIMED gauge/site-sector operator
(weight `L⁻ᵈ`, CMP99b (3.169)/(3.18)), NOT the bond-sector `Q` of (3.155)-(3.156) (weight
`L^{-(d+1)}`, dictionary rows `q1_unit_to_coarse_p427_3155`, `q_fine_to_unit_p428_3156`).** The
reference to (3.155)-(3.156) above is to Bałaban's TREATMENT of `Q`-family operators as linear
maps, not a claim that this declaration is that `Q`. Dictionary rows: `qprime_defining_p430_3169`,
`qprime_onestep_gauge_QprimeV`. Not renamed in this pass by design. -/
noncomputable def QLinearMap (Qd : QData Site Center 𝔤) : (Site → 𝔤) →ₗ[ℝ] (Center → 𝔤) where
  toFun := QMap Qd
  map_add' μ ν := by
    funext y
    simp only [QMap, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_add, smul_add]
  map_smul' c μ := by
    funext y
    simp only [QMap, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_comm]

theorem QLinearMap_apply (Qd : QData Site Center 𝔤) (μ : Site → 𝔤) :
    QLinearMap Qd μ = QMap Qd μ := rfl

#print axioms QLinearMap

/-! ### §1a — non-degeneracy witness: `Q` genuinely differs from the "no conjugation" collapse

**S82 garbage substitution**: `Rconj := fun _ _ => LinearMap.id` (identity conjugation everywhere)
is exactly the "I forgot the `R`-factor" mutation, structurally the SAME defect class the standing
traps warn about ("never justify an intertwining/covariance identity by linearity" — the collapsed
object below IS the naive "just sum linearly" guess, and it gives the WRONG number). -/

private noncomputable def qWitnessData : QData (Fin 2) Unit ℝ where
  B := fun _ => Finset.univ
  L := 2
  d := 1
  card_block := fun _ => by simp
  -- the GENUINE, nontrivial conjugation: identity on site 0, negation on site 1 — a concrete
  -- stand-in for "the holonomy at site 1 conjugates by a nontrivial group element", exactly the
  -- kind of factor `linearAverageAt`/naive block-averaging omits.
  Rconj := fun _ x => if x = 0 then LinearMap.id else -LinearMap.id

private noncomputable def qWitnessCollapsed : QData (Fin 2) Unit ℝ where
  B := fun _ => Finset.univ
  L := 2
  d := 1
  card_block := fun _ => by simp
  Rconj := fun _ _ => LinearMap.id

private def qWitnessConfig : Fin 2 → ℝ := fun _ => 1

/-- **The genuine, `R`-conjugated `Q` gives `0`** — the two summands `1` and `-1` cancel, since the
conjugation at site `1` is genuinely non-trivial. -/
theorem qWitness_eq_zero : QMap qWitnessData qWitnessConfig () = 0 := by
  unfold QMap qWitnessData qWitnessConfig
  simp [Fin.sum_univ_two]

/-- **The collapsed ("forgot the conjugation") version gives `1`, not `0`** — the falsifiability
exhibit: replacing the genuinely non-trivial `Rconj` by the identity everywhere changes the answer,
so `qWitness_eq_zero` is not a tautology forced by `QMap`'s type alone. -/
theorem qWitnessCollapsed_eq_one : QMap qWitnessCollapsed qWitnessConfig () = 1 := by
  unfold QMap qWitnessCollapsed qWitnessConfig
  simp

/-- **The two witnesses genuinely disagree** — `Q`'s `R`-conjugation is load-bearing, not
cosmetic. -/
theorem qWitness_ne_qWitnessCollapsed :
    QMap qWitnessData qWitnessConfig () ≠ QMap qWitnessCollapsed qWitnessConfig () := by
  rw [qWitness_eq_zero, qWitnessCollapsed_eq_one]
  norm_num

#print axioms qWitness_eq_zero
#print axioms qWitnessCollapsed_eq_one
#print axioms qWitness_ne_qWitnessCollapsed

/-! ### §1b — named residual: the SU(2)/lattice instantiation of `Rconj`

`CovariantOperators.RMap` (`RMap : Matrix.specialUnitaryGroup (Fin 2) ℂ → SuTwo →ₗ[ℝ] SuTwo`,
already built and banked elsewhere in this tree) is EXACTLY the right SHAPE to instantiate
`Rconj y x := RMap (holonomy along Γ_{y,x})` for the real Yang-Mills lattice, and already carries
the needed algebraic laws (`RMap_one`, multiplicativity) that make `Q` well-behaved. **This bridge
is not built in this file** — doing so needs the periodic-lattice contour object `Γ_{y,x}` (a
path/bond-sequence between a coarse point and a fine site, p.430's own annotation flags this symbol
as "not defined on this page itself... presumably defined earlier in the paper or in [4]"), which is
a separate, currently-unlocated construction, not a `QData`-internal gap. Named, not hidden. -/

/-! ## §2 — `G₁`, CMP99b (3.138), as a genuine Neumann series of bounded operators

`Δ'_π` and `Δ⁽²⁾_π` are carried as OPAQUE operators `G0 P : H →L[ℝ] H` (building them from
(3.130)-(3.137)'s own machinery — which itself needs `H`, the harmonic-projector operator of
p.421, and `Δ⁽²⁾`'s own random-walk expansion — is a separate, large, currently-unbuilt
construction; see `DeltaKRecursive.lean`'s inventory, unchanged by this file). What THIS section
builds, genuinely, is the **Neumann-series construction itself**: given `G₀` and the perturbation
`P` (standing for `Δ'_π + Δ⁽²⁾_π`), `G₁ := G₀(I − PG₀)⁻¹` is CONSTRUCTED (not asserted) as the
literal `tsum` `Σ_n G₀(PG₀)ⁿ`, using Mathlib's Banach-algebra geometric-series machinery
(`NormedRing`/`HasSummableGeomSeries` instances on `H →L[ℝ] H`, automatic from `CompleteSpace H`),
under the standard convergence hypothesis `‖PG₀‖ < 1` (which is exactly what (3.130)-(3.137)'s own
norm estimates, p.421-423, are FOR — Bałaban's own text: "the series (3.138) is convergent for `α₀`
restricted by a small, absolute constant", i.e. this hypothesis is not invented here, it is the
literal content of the surrounding estimates, carried as a hypothesis rather than re-derived). -/

section GOneNeumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **`G₁ := G₀(I − PG₀)⁻¹`**, CMP99b (3.138)'s left-hand expression, literally. `*` on
`H →L[ℝ] H` is composition (`ContinuousLinearMap.mul_def : f * g = f ∘L g`, i.e. `(f*g)(x) =
f(g(x))`) — matching operator notation `PG₀` meaning "apply `G₀` first, then `P`" exactly.
Total (uses `Ring.inverse`, which defaults to `0` off the unit group); the theorem below shows it
equals the literal (3.138) series exactly under the stated convergence hypothesis. -/
noncomputable def gOneOfNeumann (G0 P : H →L[ℝ] H) : H →L[ℝ] H :=
  G0 * Ring.inverse (1 - P * G0)

/-- **THE (3.138) IDENTITY, as a theorem**: `gOneOfNeumann G0 P` equals the literal right-hand
Neumann series `Σ'_n G₀(PG₀)ⁿ`, under (3.138)'s own stated convergence regime. -/
theorem gOneOfNeumann_eq_tsum (G0 P : H →L[ℝ] H) (hconv : ‖P * G0‖ < 1) :
    gOneOfNeumann G0 P = ∑' n : ℕ, G0 * (P * G0) ^ n := by
  unfold gOneOfNeumann
  rw [← geom_series_eq_inverse (P * G0) hconv]
  exact (Summable.tsum_mul_left G0 (summable_geometric_of_norm_lt_one hconv)).symm

/-- **The defining relation**, as a theorem: `G₁ (I − PG₀) = G₀` — the two-sided-inverse content
of (3.138)'s `(·)⁻¹`, DERIVED from the geometric-series cancellation law, not asserted. -/
theorem gOneOfNeumann_cancel_right (G0 P : H →L[ℝ] H) (hconv : ‖P * G0‖ < 1) :
    gOneOfNeumann G0 P * (1 - P * G0) = G0 := by
  unfold gOneOfNeumann
  rw [mul_assoc, ← geom_series_eq_inverse (P * G0) hconv, geom_series_mul_neg (P * G0) hconv,
    mul_one]

#print axioms gOneOfNeumann_eq_tsum
#print axioms gOneOfNeumann_cancel_right

/-! ### §2a — S82 mutation: `P = 0` collapses `G₁` to `G₀` exactly

The meaningful degenerate case: if the perturbation vanishes, (3.138) reduces to `G₁ = G₀` (no RG
step content at all) — the check "`G₁ ≠ G₀`" (proved below on a concrete nonzero-perturbation
witness) is FALSE exactly on this mutation, confirming it is not a vacuous/tautological check. -/

omit [CompleteSpace H] in
theorem gOneOfNeumann_zero_perturbation (G0 : H →L[ℝ] H) : gOneOfNeumann G0 0 = G0 := by
  unfold gOneOfNeumann
  simp

#print axioms gOneOfNeumann_zero_perturbation

end GOneNeumann

/-! ### §2b — concrete numeric witness, `H := ℝ`: `G₁ ≠ G₀` when the perturbation is genuinely
nonzero, computed exactly (not merely asserted convergent). -/

section Witness

/-- `a • id : ℝ →L[ℝ] ℝ`, a concrete one-parameter family of operators on the simplest carrier. -/
noncomputable def smulId (a : ℝ) : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ

theorem smulId_mul (a b : ℝ) : smulId a * smulId b = smulId (a * b) := by
  ext
  simp only [smulId, ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp,
    Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul]
  ring

theorem smulId_one : smulId 1 = 1 := by
  ext
  simp [smulId]

theorem smulId_sub (a b : ℝ) : smulId a - smulId b = smulId (a - b) := by
  ext
  simp only [smulId, sub_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

/-- `smulId (1/2)` is a unit with inverse `smulId 2` — the concrete two-sided cancellation
`(1/2)·2 = 1`. -/
noncomputable def smulIdHalfUnit : (ℝ →L[ℝ] ℝ)ˣ where
  val := smulId (1 / 2)
  inv := smulId 2
  val_inv := by rw [smulId_mul]; norm_num [smulId_one]
  inv_val := by rw [smulId_mul]; norm_num [smulId_one]

theorem ring_inverse_smulId_half : Ring.inverse (smulId (1 / 2 : ℝ)) = smulId 2 := by
  have h := Ring.inverse_unit smulIdHalfUnit
  exact h

/-- **The concrete instance**: `G₀ := 1` (no renormalization yet), `P := smulId (1/2)` (a genuine,
nonzero perturbation, `‖P·G₀‖ = 1/2 < 1`). -/
theorem gOneOfNeumann_witness_eq : gOneOfNeumann (1 : ℝ →L[ℝ] ℝ) (smulId (1 / 2)) = smulId 2 := by
  unfold gOneOfNeumann
  rw [one_mul, mul_one, ← smulId_one, smulId_sub]
  norm_num
  exact ring_inverse_smulId_half

theorem gOneOfNeumann_witness_hconv : ‖smulId (1 / 2) * (1 : ℝ →L[ℝ] ℝ)‖ < 1 := by
  rw [mul_one, smulId, norm_smul, ContinuousLinearMap.norm_id]
  norm_num

/-- **`G₁ ≠ G₀` on this witness**: `smulId 2 ≠ 1 = smulId 1` (as `2 ≠ 1` in `ℝ`, and `a ↦ smulId a`
is injective at `x = 1`). The renormalized propagator is genuinely different from the base one —
the perturbation is load-bearing, not cosmetic. -/
theorem gOneOfNeumann_witness_ne_G0 :
    gOneOfNeumann (1 : ℝ →L[ℝ] ℝ) (smulId (1 / 2)) ≠ (1 : ℝ →L[ℝ] ℝ) := by
  rw [gOneOfNeumann_witness_eq, ← smulId_one]
  intro h
  apply_fun (fun f => f 1) at h
  simp [smulId] at h

#print axioms gOneOfNeumann_witness_eq
#print axioms gOneOfNeumann_witness_hconv
#print axioms gOneOfNeumann_witness_ne_G0

end Witness

/-! ### §2c — S82 mutation targeting the EXACT defect a sibling prosecution just caught elsewhere in
this campaign: `DeltaKRecursive.witnessFamily.invertQGQstar := fun _ _ G _ => G` — a field NAMED
"invert" whose BODY never inverts (it returns its `G`-argument unchanged). This file's own
`gOneOfNeumann` uses a genuine `Ring.inverse` (established, via `geom_series_eq_inverse`, to be the
actual two-sided Banach-algebra inverse under the stated norm hypothesis — not a placeholder), but
the coordinator's finding demands this be TESTED, not merely asserted: mutate the one field doing the
actual inverting into a non-inverting placeholder, and confirm the defining identity BREAKS. -/

section FakeInverse

/-- **The caught defect, reproduced**: `gOneOfNeumannFake` replaces `Ring.inverse (1 - P*G0)` by the
constant `1` — "pretends" `(I − PG₀)⁻¹ = I` regardless of `P`, exactly
`witnessFamily.invertQGQstar`'s shape (a name claiming inversion, a body that ignores the operator it
is supposed to invert). -/
noncomputable def gOneOfNeumannFake (G0 _P : ℝ →L[ℝ] ℝ) : ℝ →L[ℝ] ℝ := G0 * 1

/-- **The fake construction FAILS the defining cancellation relation** on the exact witness
(`G0 := 1`, `P := smulId (1/2)`) where the GENUINE `gOneOfNeumann` (via `gOneOfNeumann_cancel_right`)
succeeds: `gOneOfNeumannFake 1 (smulId (1/2)) * (1 − smulId(1/2)·1) = 1 − smulId(1/2) = smulId(1/2)
≠ 1`. Mutating the one field that does the actual inverting breaks the identity that field exists to
establish — the falsifiability exhibit the coordinator's finding required. -/
theorem gOneOfNeumannFake_cancel_fails :
    gOneOfNeumannFake (1 : ℝ →L[ℝ] ℝ) (smulId (1 / 2)) *
        (1 - smulId (1 / 2) * (1 : ℝ →L[ℝ] ℝ)) ≠ (1 : ℝ →L[ℝ] ℝ) := by
  unfold gOneOfNeumannFake
  rw [mul_one, one_mul, mul_one, ← smulId_one, smulId_sub]
  intro h
  apply_fun (fun f => f 1) at h
  simp [smulId] at h

#print axioms gOneOfNeumannFake_cancel_fails

end FakeInverse

/-! ## §3 — wiring into `RGScaleFamily`: a PRECISE, PROVED type-signature mismatch, not a gap papered
over

`DeltaKRecursive.lean`'s `RGScaleFamily.feed : ℕ → (H → ℝ) → (H →L[ℝ] H)` is documented there as
"THE RECURSIVE STEP... (3.138) is not rendered or ingested anywhere in this repository" — i.e. the
file's own author expected `feed` to eventually BE built from (3.138). Having now built (3.138)
genuinely (§2), the honest finding is that **`feed`'s stated TYPE cannot be faithfully instantiated
by (3.138)'s actual content**: (3.138)'s `G₁` at level `k+1` is a function of level `k+1`'s OWN
operator data `(G₀, Δ'_π, Δ⁽²⁾_π)` — it does **not** consume level `k`'s `Δ_k` QUADRATIC FORM
(`H → ℝ`) as an argument anywhere in the source formula. Any instantiation of `feed` via
`gOneOfNeumann` is therefore **forced to ignore its second argument** — which is EXACTLY
`DeltaKRecursive.degenerateFamily`'s own already-proved-bad shape (its §3b: a `feed` ignoring `g`
collapses the recursion to a sequence independent of `Δ_k`). This is proved below directly, reusing
`DeltaKRecursive.G1_succ_eq_feed_deltaKQuadForm` (LAW-19, not re-derived). -/

open AdalyFormal.Balaban.DeltaKRecursive in
/-- **The forced shape**: if `F.feed` is built from (3.138)'s actual content — i.e. as a function
`C : ℕ → H →L[ℝ] H` of the LEVEL ALONE, ignoring the quadratic-form argument entirely (the only way
`gOneOfNeumann`'s inputs, which never mention `Δ_k`'s values, can populate `feed`'s stated type) —
then `G1 F (k+1) = C k` REGARDLESS of `deltaKQuadForm F k`, i.e. regardless of `F.a`, `F.H1`,
`F.Dtilde2`, `F.J`, `F.Q`, `F.Qstar`, `F.invertQGQstar` at level `k`. Proved directly from
`G1_succ_eq_feed_deltaKQuadForm`, not asserted. -/
theorem feedFromNeumann_forces_argument_independence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : RGScaleFamily H) (C : ℕ → H →L[ℝ] H)
    (hfeed : F.feed = fun k (_ : H → ℝ) => C k) (k : ℕ) :
    G1 F (k + 1) = C k := by
  rw [G1_succ_eq_feed_deltaKQuadForm, hfeed]

open AdalyFormal.Balaban.DeltaKRecursive in
/-- **The concrete consequence**: two `RGScaleFamily` instances that differ ARBITRARILY in every
field that feeds `deltaKQuadForm` (`a`, `H1`, `Dtilde2`, `J`, `Q`, `Qstar`, `invertQGQstar`,
`Lambda`, `G1base`) at level `k`, but share the SAME (3.138)-faithful `feed`, are FORCED to produce
the identical `G1` at level `k+1`. This is the precise, provable content of "the recursion claim
(`G1_succ_eq_feed_deltaKQuadForm`'s own billing, 'level k+1 is a genuine function of level k's
`Δ_k`') becomes vacuous under any literal (3.138)-based `feed`" — not an assertion, a corollary. -/
theorem G1_indep_of_deltaK_affecting_fields
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F1 F2 : RGScaleFamily H) (C : ℕ → H →L[ℝ] H)
    (hfeed1 : F1.feed = fun k (_ : H → ℝ) => C k)
    (hfeed2 : F2.feed = fun k (_ : H → ℝ) => C k) (k : ℕ) :
    G1 F1 (k + 1) = G1 F2 (k + 1) := by
  rw [feedFromNeumann_forces_argument_independence F1 C hfeed1 k,
    feedFromNeumann_forces_argument_independence F2 C hfeed2 k]

#print axioms feedFromNeumann_forces_argument_independence
#print axioms G1_indep_of_deltaK_affecting_fields

/-! **Residual, named precisely**: (3.138)'s `G₁` genuinely depends on `k` only through the level's
OWN `(G₀,Δ'_π,Δ⁽²⁾_π)` — which, in Bałaban's actual construction, are themselves built from `Δ_k`
(the PREVIOUS level's operator, not its quadratic-form VALUES) via the far larger renormalization-
transformation apparatus (the Gaussian-integral / block-spin machinery of (3.155)-(3.170), not a
single functional evaluation). `RGScaleFamily.feed`'s type `(H → ℝ) → (H →L[ℝ] H)` is too narrow to
carry that dependency faithfully; a faithful `feed` would need to consume `Δ_k` **as an operator**
(or the whole renormalization-step data), not as one real number per test vector. This is a
STRUCTURAL finding about `RGScaleFamily`'s own abstraction (already self-flagged there as a
simplification), sharpened here from "not yet built" to "cannot be built at this exact type without
either the `degenerateFamily` collapse above, or widening `feed`'s domain" — genuinely established,
not papered over, and NOT a defect of this file's own `Q`/`G₁` constructions, both of which are
complete and non-degenerate on their own terms (§1, §2). -/

end AdalyFormal.Balaban.CovarianceG1
