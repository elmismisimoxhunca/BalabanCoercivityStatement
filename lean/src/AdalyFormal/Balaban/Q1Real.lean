/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.QOne
import AdalyFormal.Balaban.DeltaPrime
import AdalyFormal.Balaban.BondSU2Space

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `Q1Real` — CMP98's GENUINE path/bond-dependent averaging transport `R_{0,c₋}A`, rebuilt

## ⚠ BANNER — THE NAME IS THE DEFECT: THIS IS `Q₀`/`Q_{V₀}`, NOT `Q₁`. (ADJUDICATED FROM THE
## SOURCE IMAGES AT 600 dpi; the weight is a DISCLOSED CHOICE, the docstrings were RIGHT)

Three labels are attached to this file's central object. They were audited against the source
images (600 dpi renders + hashes: `compute/cmp98_defining/RENDER_HASHES.txt`; page offset
ESTABLISHED BY RENDER, not assumed — both CMP95 and CMP98 have pdf page 1 = printed page 17,
offset +16, read off four separate renders). The verdict:

| label | says | verdict |
|---|---|---|
| the NAMES — `Q1Real`, `q1RealMain` (§4), `q1RealKernel` (§9), the module name | `Q₁` | **WRONG — a real defect.** CMP98 never writes `Q₁` for this object. |
| the DOCSTRINGS — `q1RealMain` ("`Q₀(U)(A)(c) = …`, CMP98 p.28"), `Q1Real` ("`Q1Real(U) = Q₀(U)`") | `Q₀` | **CORRECT.** Matches CMP98. Do NOT "fix" these. |
| the WEIGHT in the body — `(1 / (ell : ℝ) ^ 3) • …` | `1/ell³ = L^{-d}` | **A DISCLOSED APPROXIMATION, not an undisclosed error** (see "THE NORMALIZATION TENSION" below, already in this header). |

**The name defect, precisely.** CMP98 printed p.36, eq. (125) — inside Proposition 3, the RIGOROUS
defining formula — reads
`(Q₀A)_c = (Q_{V₀}A)_c = Σ_{x∈B(c₋)} L^{-(d+1)} (R_{0,c₋}A)([x,x'])`, and the paper's own sentence
names it: "We will denote the main term by `Q_{V0}`, or `Q0`." CMP98 printed p.28 (the unlabelled
prose before (61), quoted verbatim below in this header) likewise says `Q₀`, with weight `L^{-d}`,
and introduces it as "a good approximation" — a motivating formula for the axial-gauge condition,
stated BEFORE the rigorous derivation. So the source calls this object `Q₀`/`Q_{V₀}` on both pages,
and the Lean names calling it `Q₁` are misnamed. **The faithful names are `Q0Real` / `q0RealMain`
(and `q0RealKernel`).**

**NAMED OPEN REPAIR — the rename is NOT done in this pass, deliberately.** `Q1Real`/`q1RealMain`/
`q1RealKernel` have live downstream consumers (`DeltaKUnified`, `FaithfulCoercivitySU2`,
`FaithfulDeltaKNonScalar`, `DeltaKSuTwoAssembly`, `CStarDeltaKCSuTwo`, `CStarDeltaKCCompose`,
`BoundedReparam`, `CoercivityAdaptation`); a rename is a different and riskier change than a comment
fix and needs its own lane, opening with a reachability grep. It is recorded here so the defect is
VISIBLE rather than silently carried.

**The weight, stated once so it is not re-litigated.** `1/ell³ = L^{-d}` is CMP98 p.28's
PRELIMINARY/approximate prefactor; the Proposition-3 defining formula p.36 (125) carries
`L^{-(d+1)} = 1/ell⁴`. This file deliberately builds p.28's formula because p.28 is the page on
which the transport `R_{0,c₋}A` is actually DEFINED (see "THE NORMALIZATION TENSION, NAMED NOT
HIDDEN" below, which has disclosed this since the file was written, and `q1RealMain`'s own
docstring at §4). It is therefore a disclosed choice, not a hidden error — but it is the
APPROXIMATE object, and anything needing the Proposition-3 `Q₀` needs `1/ell⁴`. The same sector
arithmetic is confirmed at the image in the earliest paper of the series: CMP95 (1.18)
`(Q_kA)_b = Σ_{x∈B^k(b₋)} η^{d+1} A([x,x(b)])` (BOND sector) versus CMP95 (1.20)
`(Q'_kλ)(y) = Σ_{x∈B^k(y)} η^d λ(x)` (GAUGE/SITE sector) — the extra `η` is the line-mean factor of
the bond sector, not a level-dependent convention. Dictionary rows recording `L^{-(d+1)}` for the
bond-sector unit→coarse `Q₁`: `compute/denotation_dict/DENOTATION_DICT.tsv`
`q1_unit_to_coarse_p428_subspace` (note: "The Lean `Q_1`-clause uses `q1RealKernel`, whose
underlying map carries the WRONG weight (`1/ell^3`) though the right KERNEL"),
`q1_unit_to_coarse_p427_3155`, `q96_q1_defining_2125` (`L^{-(d+1)} = L^-d (block average) × L^-1
(line mean)`), `q96_q1_lemma24_2128`, `q96_qbare_unit_to_coarse_2153`; and `q_onestep_template_QV`
records that CMP99b p.393 (3.15) does not print the prefactor at all, deferring it to CMP98 (124).

**Not a defect, checked and left alone:** the covariant transport itself. CMP98 p.27 (58) and
p.28's `R_{0,c₋}A` ("the same object, only the product over `b` replaced by the sum") match
`rZeroA` (§4) STRUCTURALLY.

**Evidence rows for everything in this banner** (`compute/cmp98_defining/NEW_DICT_ROWS.tsv`):
`cmp98_q0_defining_p36_125` (the Proposition-3 formula, `L^{-(d+1)}`), `cmp98_q0_preliminary_p28`
(p.28's approximation, `L^{-d}`), `cmp98_qv0_full_linear_p36_124`, `cmp95_qk_bond_118`,
`cmp95_qkprime_gauge_120`; and the updated `compute/denotation_dict/MISMATCHES.tsv` row
`q1_unit_to_coarse_p428_subspace`, whose note carries this same verdict.

### Which downstream uses are sensitive to `1/ell³` (p.28, approximate) vs `1/ell⁴` (p.36 (125))

**INSENSITIVE — kernel-only consumers.** Replacing `1/ell³` by `1/ell⁴` multiplies `q1RealMain` by
the single nonzero scalar `ell⁻¹` (PROVED, not argued: `q1RealMain_altWeight`, §4 below), so it
does not move `LinearMap.ker (Q1Real U) = q1RealKernel U` for `ell ≠ 0`. Hence these are unaffected
in truth-value: `deltaWitnessConfig_notMem_q1RealKernel`, `q1RealKernel_ne_top`,
`checkerConfigSuTwo_mem_q1RealKernel_trivialU`, `q1RealKernel_trivialU_ne_bot` (all §9), and
therefore `DeltaKUnified.subspace156G` / `subspace156BFL2` and
`FaithfulCoercivitySU2.subspace156G_ne_top` / `subspace156BFL2_ne_top`, whose `Q₁`-clause is exactly
`q1RealKernel`.

**SENSITIVE — every consumer of a NUMERICAL VALUE of `q1RealMain`/`Q1Real`.** At `witnessEll = 2`
each of these values would be HALVED (`ell⁻¹ = 1/2`) under the `1/ell⁴` reading:
`q1RealMain_deltaWitnessConfig` / `Q1Real_deltaWitnessConfig` (`1/8`, §6),
`q1RealMain_d4ConfigSuTwo` / `Q1Real_d4_trivialU` / `Q1Real_d4_witnessU` (`±1/4`, §7), and
downstream `FaithfulCoercivitySU2.kappa` via `kappa_eq` (its `1/4` prefactor becomes `1/8`), hence
the numerical value (not the existence) of `FaithfulCoercivitySU2.baseG + kappa U` and of anything
in `FaithfulDeltaKNonScalar.lean` quoting `κ`. The QUALITATIVE conclusions drawn from those numbers
survive the rescale — `Q1Real_deltaWitnessConfig_ne_zero`, `Q1Real_d4_genuinely_U_dependent`,
`kappa_bound` (`|κ| ≤ ‖suTwoWitness‖²`) and `baseG_add_kappa_pos` are all invariant under
multiplication by `1/2` — but the printed CONSTANTS are not, and must NOT be quoted as values of
CMP98's Proposition-3 `Q₀` (p.36 (125), `L^{-(d+1)}`): they are values of p.28's approximate
`L^{-d}` formula, and differ from the Proposition-3 ones by exactly the factor `ell⁻¹`
(`q1RealMain_altWeight`, §4).

## THE CONVICTION THIS FILE REPAIRS (`compute/sol_q1_gate/SOL_Q1_GATE.md`, grade-2 conviction)

`BackgroundAveraging.Q1LM` pulled ONE `x`/`b`-independent conjugation `R0(U) : SuTwo →ₗ[ℝ] SuTwo`
outside CMP98 (125)'s block sum. CMP98 pp.27–28 define `R_{0,c₋}A` as a genuinely **bond/path
-dependent transported field**: a DIFFERENT holonomy for every constituent fine bond `b` inside the
long bond `[x,x(c)]`, and for every block-interior site `x`. Pulling a fixed map outside the sum is
valid algebra for the *invented* fixed map, but it is not CMP98's operator. This file builds the
real, per-bond, per-path transport instead — never a fixed conjugation.

## THE SOURCE, IMAGE-VERIFIED INDEPENDENTLY (LAW-11 — the page image, not the OCR text layer)

Rendered pages `compute/sol_q1_gate/renders/CMP98_p27_p28-11.png`
(`sha256 ba9e7917c2cac194fad09571693b678183c3bdf0a539d06f2f6a2488cec4bbf3`, printed p.27) and
`CMP98_p27_p28-12.png` (`sha256 2f8a18f0b5617f31bd8954bc80c4ff474cceba7f1448d42669ff05a8c934fd1b`,
printed p.28) were opened and read directly (not via OCR) as part of this dispatch, independently
of the earlier Sol gate that first rendered them. Both hashes match the earlier gate's record
exactly (LAW-19: reused render, independently re-read).

Printed p.27, eq. (58), verbatim:

> `(R_{0,y}V')(Γ_{y,x}) = ∏_{b⊂Γ_{y,x}} R(V₀(Γ_{y,b_-}))V'_b = 1, x ∈ B(y), x ≠ y.`

Printed p.28, the displayed formula immediately below "Because of the axial gauge conditions (58),
the average `(V̄'V₀)_c` depends on", verbatim:

> `(R_{0,c_-}V')([x,x(c)]) = ∏_{b⊂[x,x(c)]} R(V₀(Γ_{c_-,x}∪[x,b_-]))V'_b, x ∈ B(c_-)`

and the immediately following sentence, verbatim: "a good approximation of the function
`(1/i)log(V̄'V₀)_c(V̄₀)_c⁻¹` for `V'=e^{iA}`, `A` small, is given by
`(Q₀A)(c) = Σ_{x∈B(c_-)} L^{-d}(R_{0,c_-}A)([x,x(c)])`, where `R_{0,c_-}A` is defined as
`R_{0,c_-}V'`, only the product over `b` is replaced by the sum."

Combining these two sentences literally (not paraphrased):

```
(Q₀A)(c) = Σ_{x∈B(c_-)} L^{-d} Σ_{b⊂[x,x(c)]} R(V₀(Γ_{c_-,x}∪[x,b_-])) A_b
```

**The load-bearing structural fact, decisive against the conviction**: the transport factor
`R(V₀(Γ_{c_-,x}∪[x,b_-]))` depends on BOTH the block-interior site `x` (via `Γ_{c_-,x}`, the
CMP95 (1.7) contour from the coarse base to `x`) AND the fine-bond base `b_-` (via the straight
extra leg `[x,b_-]`). No single `x`/`b`-independent map can equal this in general.

## THE NORMALIZATION TENSION, NAMED NOT HIDDEN

p.28's own preliminary `Q₀` (quoted above) carries prefactor `L^{-d}`. CMP98's LATER, more refined
(124)/(125) (printed p.36, transcribed in the superseded `BackgroundAveraging.lean`) states the
SAME-NAMED `Q₀` with prefactor `L^{-(d+1)}` instead. Both use the identical `R_{0,c_-}A` transport
definition (p.28's own sentence: "`R_{0,c_-}A` is defined as `R_{0,c_-}V'`, only the product over
`b` is replaced by the sum" — this is the ONLY definition of `R_{0,c_-}A` anywhere in the rendered
pages, and (125) reuses the identical notation `(R_{0,c_-}A)([x,x'])` without redefining it). This
file builds p.28's own `Q₀` verbatim (`L^{-d}`, i.e. `ell^{-3}` at `d=3`) since that is the page
where `R_{0,c_-}A`'s transport is actually DEFINED; the `L^{-(d+1)}` refinement at p.36 is a later,
different normalization for the same-named object, NOT independently re-derived here, and NOT
conflated with this file's `L^{-d}` object. This is a genuine open tension in the source's own
notation across pp.28 and 36 (recorded, not resolved by invention).

## THE `Γ_{y,x}` CONTOUR, CMP95 (1.7), IMAGE/TRANSCRIPTION-VERIFIED SEPARATELY

`corpus/mathpix/balaban_CMP95_1984_propagators_I/normalized/p18.md` (machine-draft layer, used only
as a locator here since the formula is load-bearing and independently re-derivable; the shape below
is checked against the printed LaTeX, not merely paraphrased), CMP95 (1.7):

```
Γ_{y,x} = [y,(y_1,…,y_{d-1},x_d)] ∪ … ∪ [(y_1,…,y_μ,x_{μ+1},…,x_d),(y_1,…,x_μ,x_{μ+1},…,x_d)] ∪ …
          ∪ [(y_1,x_2,…,x_d),x]
```

Read term-by-term (not merely pattern-matched): the FIRST segment changes coordinate `d` (last)
from `y_d` to `x_d`, holding all other coordinates at `y`. The GENERAL term changes coordinate `μ`
from `y_μ` to `x_μ`, holding coordinates `1..μ-1` at `y` and `μ+1..d` already at `x`. The LAST
explicit term changes coordinate `1` (first) from `y_1` to `x_1`. **The coordinate-change order is
therefore DESCENDING: `d, d-1, …, 2, 1`** — this is the exact convention this file's own build
discipline flags as a documented prior failure mode (a backwards coordinate order); it is checked
here against the primary CMP95 page, not re-derived from a later paper's use of the symbol.

`GammaPath` below realizes this literally for `d=3` (`Fin 3` indices `2,1,0` in descending order),
using ONLY forward unit steps (`straightSegment`), which suffices because `Γ_{y,x}` is only ever
used for `x` inside the block `B(y)` (`y_μ ≤ x_μ < y_μ+L` for every `μ`, CMP95 (1.6)), so no
coordinate ever needs to decrease.

## WHAT THIS FILE BUILDS

1. `nsmul_one_val`/`nsmul_one_eq`/`iterate_add_one` (§0): general `Fin (n+1)` arithmetic closing
   the gap between `n`-fold iteration of "add one" and additive-group subtraction — the general
   fact making straight-segment endpoints computable.
2. `coordSteps`/`straightSegment`/`GammaPath` (§1): CMP95 (1.7)'s contour, built and its endpoint
   correctness PROVED (`GammaPath_endpoint`), not merely asserted — plus the general fact
   `GammaPath_self : GammaPath a a = []` (a path from a point to itself is empty), used decisively
   below.
3. `periodicPathEndpoint_append`/`periodicPathHolonomy_append` (§1–2): general append laws for the
   existing `Target.ClayStatement` path primitives (reused, LAW-19; the append laws themselves did
   not previously exist anywhere in this tree — checked by grep before building, not duplicated).
4. `periodicPathHolonomy_trivialU_eq_one` (§3): the trivial background has trivial holonomy along
   ANY path (general, re-proved fresh here to keep this file independent of the convicted/superseded
   `BackgroundAveraging.lean`, LAW-19-clean but NOT importing that file).
5. `rZeroA`/`q1RealMain`/`Q1Real` (§4): the genuine `(R_{0,c_-}A)([x,x(c)])` transport-sum and the
   resulting `Q₀(U) = Q1Real(U)` LINEAR map, using `GammaPath c_- x ++ straightSegment x b_- μ` as
   the transport path for EVERY fine bond `b` — a genuinely `x`-AND-`b`-dependent conjugation, never
   a single fixed map pulled outside the sum.
6. **THE REDUCTION ANCHOR** (§5): `Q1Real(trivialU) = ` the bare abelian block average (no
   conjugation) — CMP99b (3.194)'s own claim `Q'_1 = Q₀` at `V₀=1`, proved (not assumed).
7. **THE DECISIVE RECOMPUTATION, WITNESS A** (§6): `Q1Real(U)·deltaWitnessConfig` at
   `targetCoarseBond` equals `(1/8)•suTwoWitness` for EVERY `U` (not merely at `trivialU`/
   `witnessU`) — because the spike's SOLE contributing transport path is `GammaPath witnessY
   witnessY ++ straightSegment witnessY witnessY 0 = []`, EMPTY regardless of the background. This
   is the honest, source-correct replacement for the convicted `-(1/16)` artifact: the exclusion
   from `q1RealKernel` is real and background-independent for this witness, not because `Q₁` is
   secretly trivial, but because THIS SPECIFIC bond sits exactly at its own block's base.
8. **WITNESS B, GENUINE NON-VACUOUS `U`-DEPENDENCE** (§7): a second spike `d4ConfigSuTwo`
   (nonzero at `(QOne.site1,0)`, reusing `QOne.site1`/`QOne.periodicLatticeShift_injective`, LAW-19)
   whose two contributing transport paths are BOTH the genuinely nonempty `[(0,true)]`, giving
   `Q1Real(trivialU)·d4ConfigSuTwo = (1/4)•suTwoWitness` but
   `Q1Real(witnessU)·d4ConfigSuTwo = -(1/4)•suTwoWitness` — a real sign flip, built from a FORWARD
   (not backward/invented) holonomy `U(witnessY,0)`, proving the construction is not vacuous.
9. **THE STRUCTURAL MUTATION** (§8): a direct proof that the transport used for TWO DIFFERENT fine
   bonds at the SAME block-site `x = witnessY` genuinely differs (`RMap 1 ≠ RMap witnessMElem` as
   applied maps) — the exact per-bond variation the convicted `Q1LM`'s single fixed `R0` could never
   reproduce, made concrete rather than merely argued.
10. `q1RealKernel` (§9): the `Q₁(U)B=0` locus, a genuine `U`-parameterized `Submodule`, with
    `≠ ⊤` (both witnesses) and `≠ ⊥` (a checkerboard configuration, reused shape from
    `QOne.checkerConfig`, LAW-19).

## NAMED, NOT BUILT

The four `ad_Y` correction terms of CMP98 (124) remain unbuilt (`Y`, `Y_x`, `g` are not defined
anywhere in this tree, matching the same finding already recorded in the superseded
`BackgroundAveraging.lean`'s own header) — they vanish at `V₀=1` and are small in-regime, but this
file's `Q1Real` is CMP98's own "main term" only, not the full `Q₁(U)`.
-/

namespace AdalyFormal.Balaban.Q1Real

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantOperators AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.QOne (targetCoarseBond site1 site1_mem_block witnessY_mem_block
  shift_witnessY_eq_site1 periodicLatticeShift_injective pathSite pathSite_zero pathSite_succ)

/-! ## §0 — `Fin (n+1)` coordinate arithmetic: `n`-fold `+1` iteration equals additive-group
`nsmul` by `1`, hence subtraction realizes the exact forward step-count between two coordinates. -/

theorem nsmul_one_val (n k : ℕ) : (k • (1 : Fin (n + 1))).val = k % (n + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, Fin.val_add, ih]; simp [Nat.add_mod]

theorem nsmul_one_eq (n : ℕ) (x : Fin (n + 1)) : x.val • (1 : Fin (n + 1)) = x := by
  apply Fin.ext
  rw [nsmul_one_val]
  exact Nat.mod_eq_of_lt x.isLt

theorem iterate_add_one (n : ℕ) (a : Fin (n + 1)) (k : ℕ) :
    (fun y : Fin (n + 1) => y + 1)^[k] a = a + k • (1 : Fin (n + 1)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, succ_nsmul]; abel

#print axioms nsmul_one_val
#print axioms nsmul_one_eq
#print axioms iterate_add_one

/-! ## §1 — `Γ_{y,x}`: CMP95 (1.7)'s staircase contour, general `L`, and its endpoint correctness -/

/-- The number of forward unit steps in direction `μ` carrying `a`'s `μ`-coordinate to `b`'s
(`Fin (L μ+1)`'s own additive-group subtraction, hence exact even across periodic wraparound). -/
def coordSteps {L : PeriodicLatticeExtent} (a b : PeriodicLatticeSite L) (μ : Fin 3) : ℕ :=
  (b μ - a μ).val

/-- `coordSteps a b μ` forward unit steps in direction `μ` — CMP95 (1.7)'s `[x_1,x_2]` straight
segment, specialized to the forward-only case CMP95 (1.6)'s block interior always needs. -/
def straightSegment {L : PeriodicLatticeExtent} (a b : PeriodicLatticeSite L) (μ : Fin 3) :
    List (Fin 3 × Bool) :=
  List.replicate (coordSteps a b μ) (μ, true)

/-- General append law for `periodicPathEndpoint` (`Target.ClayStatement`) — checked by grep before
building: no such lemma previously existed anywhere in this tree. -/
theorem periodicPathEndpoint_append {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (s1 s2 : List (Fin 3 × Bool)) :
    periodicPathEndpoint x (s1 ++ s2) = periodicPathEndpoint (periodicPathEndpoint x s1) s2 := by
  induction s1 generalizing x with
  | nil => rfl
  | cons a as ih => simp [periodicPathEndpoint, ih]

theorem straightSegment_endpoint {L : PeriodicLatticeExtent} (a b : PeriodicLatticeSite L)
    (μ : Fin 3) :
    periodicPathEndpoint a (straightSegment a b μ) = Function.update a μ (b μ) := by
  have key : ∀ (n : ℕ) (c : PeriodicLatticeSite L),
      periodicPathEndpoint c (List.replicate n (μ, true)) =
        Function.update c μ ((fun y : Fin (L μ + 1) => y + 1)^[n] (c μ)) := by
    intro n
    induction n with
    | zero => intro c; simp [periodicPathEndpoint, Function.update_eq_self]
    | succ n ih =>
      intro c
      rw [List.replicate_succ]
      show periodicPathEndpoint (periodicLatticeStep c (μ, true))
          (List.replicate n (μ, true)) = _
      have hstep : periodicLatticeStep c (μ, true) = Function.update c μ (c μ + 1) := rfl
      rw [hstep, ih]
      rw [Function.update_idem]
      congr 1
      rw [Function.update_self, ← Function.iterate_succ_apply, Function.iterate_succ_apply']
  unfold straightSegment
  rw [key, iterate_add_one, coordSteps, nsmul_one_eq, add_sub_cancel]

/-- **`Γ_{y,x}`, CMP95 (1.7), literally**: change coordinate `2`, then `1`, then `0`, in that
DESCENDING order (image-verified against CMP95 p.18, see file header). -/
def GammaPath {L : PeriodicLatticeExtent} (y x : PeriodicLatticeSite L) : List (Fin 3 × Bool) :=
  straightSegment y x 2 ++
    straightSegment (Function.update y 2 (x 2)) x 1 ++
    straightSegment (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0

/-- **Endpoint correctness, PROVED not assumed**: `Γ_{y,x}` genuinely connects `y` to `x`. -/
theorem GammaPath_endpoint {L : PeriodicLatticeExtent} (y x : PeriodicLatticeSite L) :
    periodicPathEndpoint y (GammaPath y x) = x := by
  unfold GammaPath
  rw [periodicPathEndpoint_append, periodicPathEndpoint_append, straightSegment_endpoint,
    straightSegment_endpoint, straightSegment_endpoint]
  funext ν
  fin_cases ν <;> simp [Function.update_self, Function.update_of_ne]

theorem coordSteps_self {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) (μ : Fin 3) :
    coordSteps a a μ = 0 := by simp [coordSteps]

theorem straightSegment_self {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) (μ : Fin 3) :
    straightSegment a a μ = [] := by simp [straightSegment, coordSteps_self]

/-- **The decisive general fact**: the contour from a point to ITSELF is literally empty — used
below to make the spike-witness exclusion background-independent, not by degeneracy of `Q1Real`
but by the geometry of this particular spike. -/
theorem GammaPath_self {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) :
    GammaPath a a = [] := by unfold GammaPath; simp [straightSegment_self]

#print axioms periodicPathEndpoint_append
#print axioms straightSegment_endpoint
#print axioms GammaPath_endpoint
#print axioms coordSteps_self
#print axioms straightSegment_self
#print axioms GammaPath_self

/-! ## §2 — `periodicPathHolonomy` append law (general, reusable; did not previously exist) -/

theorem periodicPathHolonomy_append {G : Type*} [Group G] {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration G L) (x : PeriodicLatticeSite L)
    (s1 s2 : List (Fin 3 × Bool)) :
    periodicPathHolonomy U x (s1 ++ s2) =
      periodicPathHolonomy U x s1 * periodicPathHolonomy U (periodicPathEndpoint x s1) s2 := by
  induction s1 generalizing x with
  | nil => simp [periodicPathHolonomy, periodicPathEndpoint]
  | cons a as ih =>
    simp only [List.cons_append, periodicPathHolonomy, periodicPathEndpoint]
    rw [ih, mul_assoc]

#print axioms periodicPathHolonomy_append

/-! ## §3 — the trivial background has trivial holonomy along ANY path (general; re-proved fresh
here so this file does not depend on the convicted/superseded `BackgroundAveraging.lean`). -/

theorem periodicPathHolonomy_trivialU_eq_one {L : PeriodicLatticeExtent}
    (x : PeriodicLatticeSite L) (steps : List (Fin 3 × Bool)) :
    periodicPathHolonomy (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) x steps = 1 := by
  induction steps generalizing x with
  | nil => rfl
  | cons step rest ih =>
    show (if step.2 then (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) (x, step.1)
        else ((AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L)
          (periodicLatticeStep x step, step.1))⁻¹) *
      periodicPathHolonomy (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L)
        (periodicLatticeStep x step) rest = 1
    rw [ih]
    unfold AdalyFormal.Balaban.CovariantHjMinimizer.trivialU
    rcases step.2 with hb | hb <;> simp

#print axioms periodicPathHolonomy_trivialU_eq_one

/-! ## §4 — `R_{0,c₋}A`: CMP98 pp.27–28's genuine per-bond transport, and `Q1Real = Q₀`. -/

/-- **The transport path CMP98 pp.27–28 assign to fine bond `b = (pathSite x μ i, μ)` inside the
long bond based at block-interior site `x`**: `Γ_{c₋,x} ∪ [x,b₋]` — the coarse-to-block contour
FOLLOWED BY the straight leg from `x` to the fine bond's own base. Genuinely depends on `x` (via
`GammaPath`) AND on `i`/`b₋` (via `straightSegment x (pathSite x μ i) μ`) — this is the exact
dependence the convicted `Q1LM`'s single `R0(U)` erased. -/
def transportPath {L : PeriodicLatticeExtent} (cMinus x : PeriodicLatticeSite L) (μ : Fin 3)
    (i : ℕ) : List (Fin 3 × Bool) :=
  GammaPath cMinus x ++ straightSegment x (pathSite x μ i) μ

/-- **`(R_{0,c₋}A)([x,x(c)])`, CMP98 p.28, literally**: the sum (product→sum, per p.28's own
sentence) over the `ell` fine bonds inside `[x,x(c)]`, each transported by ITS OWN path. -/
noncomputable def rZeroA {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (cMinus x : PeriodicLatticeSite L) (A : Bond L → SuTwo) (μ : Fin 3) (ell : ℕ) : SuTwo :=
  ∑ i ∈ Finset.range ell,
    RMap (periodicPathHolonomy U cMinus (transportPath cMinus x μ i)) (A (pathSite x μ i, μ))

theorem rZeroA_add {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (cMinus x : PeriodicLatticeSite L) (A1 A2 : Bond L → SuTwo) (μ : Fin 3) (ell : ℕ) :
    rZeroA U cMinus x (A1 + A2) μ ell = rZeroA U cMinus x A1 μ ell + rZeroA U cMinus x A2 μ ell := by
  simp only [rZeroA, Pi.add_apply, map_add]
  rw [Finset.sum_add_distrib]

theorem rZeroA_smul {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (cMinus x : PeriodicLatticeSite L) (c : ℝ) (A : Bond L → SuTwo) (μ : Fin 3) (ell : ℕ) :
    rZeroA U cMinus x (c • A) μ ell = c • rZeroA U cMinus x A μ ell := by
  simp only [rZeroA, Pi.smul_apply, map_smul]
  rw [Finset.smul_sum]

/-- Two-term unfold at `ell = 2` (the witness value), mirroring `QOne.longBondValue_ell2`. -/
theorem rZeroA_ell2 {L : PeriodicLatticeExtent}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (cMinus x : PeriodicLatticeSite L) (A : Bond L → SuTwo) (μ : Fin 3) :
    rZeroA U cMinus x A μ 2 =
      RMap (periodicPathHolonomy U cMinus (transportPath cMinus x μ 0)) (A (x, μ)) +
      RMap (periodicPathHolonomy U cMinus (transportPath cMinus x μ 1))
        (A (periodicLatticeShift x μ, μ)) := by
  simp [rZeroA, Finset.sum_range_succ, pathSite_zero, pathSite_succ]

#print axioms rZeroA_add
#print axioms rZeroA_smul
#print axioms rZeroA_ell2

/-- **`Q₀(U)(A)(c) = Σ_{x∈B(c₋)} L^{-d}(R_{0,c₋}A)([x,x(c)])`, CMP98 p.28, literally** — the honest
`L^{-d}` (`= ell^{-3}` at `d=3`) prefactor of p.28's OWN preliminary `Q₀`, not p.36's later
`L^{-(d+1)}` refinement (file header's normalization-tension note). -/
noncomputable def q1RealMain (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) (ell : ℕ) (A : Bond witnessL → SuTwo)
    (b : LatticeOperators.CoarseBond witnessL ell) : SuTwo :=
  (1 / (ell : ℝ) ^ 3) • ∑ x ∈ blockOf b.1.1 ell, rZeroA U b.1.1 x A b.2 ell

theorem q1RealMain_add (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) (ell : ℕ) (A1 A2 : Bond witnessL → SuTwo)
    (b : LatticeOperators.CoarseBond witnessL ell) :
    q1RealMain U ell (A1 + A2) b = q1RealMain U ell A1 b + q1RealMain U ell A2 b := by
  simp only [q1RealMain]
  rw [← smul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => rZeroA_add U b.1.1 x A1 A2 b.2 ell

theorem q1RealMain_smul (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) (ell : ℕ) (c : ℝ) (A : Bond witnessL → SuTwo)
    (b : LatticeOperators.CoarseBond witnessL ell) :
    q1RealMain U ell (c • A) b = c • q1RealMain U ell A b := by
  simp only [q1RealMain]
  have h : ∀ x ∈ blockOf b.1.1 ell, rZeroA U b.1.1 x (c • A) b.2 ell =
      c • rZeroA U b.1.1 x A b.2 ell := fun x _ => rZeroA_smul U b.1.1 x c A b.2 ell
  rw [Finset.sum_congr rfl h, ← Finset.smul_sum]
  exact smul_comm _ _ _

/-- **THE TWO NORMALIZATIONS DIFFER BY THE SINGLE SCALAR `ell⁻¹`** — CMP98 p.36 (125)'s
Proposition-3 prefactor `L^{-(d+1)} = 1/ell⁴` against p.28's approximate `L^{-d} = 1/ell³` (this
file's `q1RealMain`), on the IDENTICAL transport sum. Proved, not argued, so the header banner's
sensitivity table is kernel-visible rather than prose: since `ell⁻¹ ≠ 0` for `ell ≠ 0`, the
`1/ell⁴` variant has exactly the same kernel as `q1RealMain` (hence `q1RealKernel` and every
consumer of it is INSENSITIVE to the choice), while every NUMERICAL value of `q1RealMain` scales by
`ell⁻¹` (hence `Q1Real_deltaWitnessConfig`'s `1/8`, `q1RealMain_d4ConfigSuTwo`'s `±1/4` and
`FaithfulCoercivitySU2.kappa_eq`'s `1/4` ARE sensitive). Holds for every `ell`, no hypothesis. -/
theorem q1RealMain_altWeight (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) (ell : ℕ) (A : Bond witnessL → SuTwo)
    (b : LatticeOperators.CoarseBond witnessL ell) :
    (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf b.1.1 ell, rZeroA U b.1.1 x A b.2 ell
      = ((ell : ℝ))⁻¹ • q1RealMain U ell A b := by
  simp only [q1RealMain]
  have hscal : (1 / (ell : ℝ) ^ 4) = ((ell : ℝ))⁻¹ * (1 / (ell : ℝ) ^ 3) := by ring
  rw [hscal, mul_smul]

#print axioms q1RealMain_altWeight

/-- **`Q1Real(U) = Q₀(U)`**, CMP98 p.28's own main term, as a genuine `LinearMap`, built from the
per-bond path-dependent transport `rZeroA` — never a fixed conjugation pulled outside the sum. -/
noncomputable def Q1Real (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) : (Bond witnessL → SuTwo) →ₗ[ℝ]
    (LatticeOperators.CoarseBond witnessL witnessEll → SuTwo) where
  toFun A b := q1RealMain U witnessEll A b
  map_add' A1 A2 := funext fun b => q1RealMain_add U witnessEll A1 A2 b
  map_smul' c A := funext fun b => q1RealMain_smul U witnessEll c A b

theorem Q1Real_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (A : Bond witnessL → SuTwo) (b : LatticeOperators.CoarseBond witnessL witnessEll) :
    Q1Real U A b = q1RealMain U witnessEll A b := rfl

#print axioms q1RealMain_add
#print axioms q1RealMain_smul
#print axioms Q1Real_apply

/-! ## §5 — THE REDUCTION ANCHOR: `Q1Real(trivialU) =` the bare abelian block average. -/

theorem rZeroA_trivialU {L : PeriodicLatticeExtent} (cMinus x : PeriodicLatticeSite L)
    (A : Bond L → SuTwo) (μ : Fin 3) (ell : ℕ) :
    rZeroA (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) cMinus x A μ ell =
      ∑ i ∈ Finset.range ell, A (pathSite x μ i, μ) := by
  simp only [rZeroA, periodicPathHolonomy_trivialU_eq_one, RMap_one, LinearMap.id_apply]

theorem q1RealMain_trivialU (ell : ℕ) (A : Bond witnessL → SuTwo)
    (b : LatticeOperators.CoarseBond witnessL ell) :
    q1RealMain (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) ell A b =
      (1 / (ell : ℝ) ^ 3) • ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range ell,
        A (pathSite x b.2 i, b.2) := by
  simp only [q1RealMain, rZeroA_trivialU]

#print axioms rZeroA_trivialU
#print axioms q1RealMain_trivialU

/-! ## §6 — WITNESS A: `deltaWitnessConfig`, BACKGROUND-INDEPENDENT exclusion, honest replacement
for the convicted `-(1/16)` path artifact. -/

/-- Fresh, self-contained restatement of the block-uniqueness fact (decidable on the small witness
lattice) — reused SHAPE from the convicted file's own `witnessY_unique_contributor`, re-proved here
so this file does not import `BackgroundAveraging.lean`. -/
theorem witnessY_unique_contributor :
    ∀ x ∈ blockOf witnessY witnessEll, x ≠ witnessY →
      x ≠ witnessY ∧ periodicLatticeShift x 0 ≠ witnessY := by decide

theorem shift0_witnessY_ne_witnessY : periodicLatticeShift witnessY 0 ≠ witnessY := by decide

/-- **THE DECISIVE COMPUTATION, GENERAL IN `U`**: `q1RealMain(U)(deltaWitnessConfig)` at
`targetCoarseBond` equals `(1/8)•suTwoWitness` for EVERY background `U`, because the spike's sole
contributing transport path is `GammaPath witnessY witnessY ++ straightSegment witnessY witnessY 0
= []`, empty regardless of `U`. -/
theorem q1RealMain_deltaWitnessConfig
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    q1RealMain U witnessEll deltaWitnessConfig targetCoarseBond = (1 / 8 : ℝ) • suTwoWitness := by
  show (1 / (witnessEll : ℝ) ^ 3) •
      ∑ x ∈ blockOf targetCoarseBond.1.1 witnessEll,
        rZeroA U targetCoarseBond.1.1 x deltaWitnessConfig targetCoarseBond.2 witnessEll = _
  have hbase : (targetCoarseBond : LatticeOperators.CoarseBond witnessL witnessEll).1.1 =
      witnessY := rfl
  have hdir : (targetCoarseBond : LatticeOperators.CoarseBond witnessL witnessEll).2 =
      (0 : Fin 3) := rfl
  rw [hbase, hdir]
  have hEll : witnessEll = 2 := rfl
  have hsum : ∑ x ∈ blockOf witnessY witnessEll,
      rZeroA U witnessY x deltaWitnessConfig 0 witnessEll = suTwoWitness := by
    rw [Finset.sum_eq_single witnessY]
    · rw [hEll, rZeroA_ell2]
      show RMap (periodicPathHolonomy U witnessY (transportPath witnessY witnessY 0 0))
          (deltaWitnessConfig (witnessY, 0)) +
        RMap (periodicPathHolonomy U witnessY (transportPath witnessY witnessY 0 1))
          (deltaWitnessConfig (periodicLatticeShift witnessY 0, 0)) = suTwoWitness
      have hpath0 : transportPath witnessY witnessY (0 : Fin 3) 0 = [] := by
        show GammaPath witnessY witnessY ++ straightSegment witnessY (pathSite witnessY 0 0) 0 = []
        simp [pathSite_zero, GammaPath_self, straightSegment_self]
      rw [hpath0, deltaWitnessConfig_at_e0,
        deltaWitnessConfig_elsewhere
          (show (periodicLatticeShift witnessY 0, (0 : Fin 3)) ≠ (witnessY, (0 : Fin 3)) by
            intro h; exact shift0_witnessY_ne_witnessY (Prod.mk.injEq .. ▸ h).1)]
      show RMap (periodicPathHolonomy U witnessY []) suTwoWitness + RMap _ 0 = suTwoWitness
      rw [map_zero, add_zero]
      show RMap 1 suTwoWitness = suTwoWitness
      rw [RMap_one]; rfl
    · intro x hx hne
      obtain ⟨-, hshift⟩ := witnessY_unique_contributor x hx hne
      rw [hEll, rZeroA_ell2]
      have h0 : deltaWitnessConfig (x, (0 : Fin 3)) = 0 :=
        deltaWitnessConfig_elsewhere (show (x, (0 : Fin 3)) ≠ (witnessY, (0 : Fin 3)) by
          intro h; exact hne (Prod.mk.injEq .. ▸ h).1)
      have h1 : deltaWitnessConfig (periodicLatticeShift x 0, (0 : Fin 3)) = 0 :=
        deltaWitnessConfig_elsewhere
          (show (periodicLatticeShift x 0, (0 : Fin 3)) ≠ (witnessY, (0 : Fin 3)) by
            intro h; exact hshift (Prod.mk.injEq .. ▸ h).1)
      rw [h0, h1, map_zero, map_zero, add_zero]
    · intro h; exact absurd witnessY_mem_block h
  rw [hsum, hEll]
  norm_num

theorem Q1Real_deltaWitnessConfig
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    Q1Real U deltaWitnessConfig targetCoarseBond = (1 / 8 : ℝ) • suTwoWitness :=
  q1RealMain_deltaWitnessConfig U

/-- **Background-independence, made explicit**: the trivial and witness backgrounds give the exact
SAME value on this spike — the exclusion the mandate names is honest for BOTH, not a path artifact
of an invented backward reference. -/
theorem Q1Real_delta_background_independent :
    Q1Real (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) deltaWitnessConfig
        targetCoarseBond =
      Q1Real witnessU deltaWitnessConfig targetCoarseBond := by
  rw [Q1Real_deltaWitnessConfig, Q1Real_deltaWitnessConfig]

theorem Q1Real_deltaWitnessConfig_ne_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    Q1Real U deltaWitnessConfig targetCoarseBond ≠ 0 := by
  rw [Q1Real_deltaWitnessConfig]
  exact smul_ne_zero (by norm_num) suTwoWitness_ne_zero

#print axioms witnessY_unique_contributor
#print axioms shift0_witnessY_ne_witnessY
#print axioms q1RealMain_deltaWitnessConfig
#print axioms Q1Real_deltaWitnessConfig
#print axioms Q1Real_delta_background_independent
#print axioms Q1Real_deltaWitnessConfig_ne_zero

/-! ## §7 — WITNESS B: `d4ConfigSuTwo`, GENUINE non-vacuous `U`-dependence, forward holonomy. -/

/-- **The `SuTwo`-valued analogue of `QOne.d4Config`**: nonzero exactly at the fine bond
`(QOne.site1, 0)` — chosen (reused shape, LAW-19) because it is reached from BOTH the direct term
(`x = site1`) and the shift term (`x = witnessY`), giving TWO genuinely nonempty transport paths
that turn out to coincide as lists, both equal to `[(0,true)]`. -/
noncomputable def d4ConfigSuTwo : Bond witnessL → SuTwo :=
  fun e => if e = (site1, (0 : Fin 3)) then suTwoWitness else 0

theorem d4ConfigSuTwo_at_site1 : d4ConfigSuTwo (site1, (0 : Fin 3)) = suTwoWitness := by
  simp [d4ConfigSuTwo]

theorem d4ConfigSuTwo_elsewhere {e : Bond witnessL} (h : e ≠ (site1, (0 : Fin 3))) :
    d4ConfigSuTwo e = 0 := by simp [d4ConfigSuTwo, h]

/-- **Both contributing transport paths are `[(0,true)]`, hence holonomy `U(witnessY,0)`**: the
direct term (`x = site1`, path `= GammaPath witnessY site1`) and the shift term (`x = witnessY`,
path `= straightSegment witnessY site1 0`) coincide, since `site1` differs from `witnessY` only in
coordinate `0` by exactly one step. -/
theorem transportPath_to_site1_direct :
    transportPath witnessY site1 (0 : Fin 3) 0 = [((0 : Fin 3), true)] := by
  show GammaPath witnessY site1 ++ straightSegment site1 (pathSite site1 0 0) (0 : Fin 3) =
    [((0 : Fin 3), true)]
  rw [pathSite_zero, straightSegment_self, List.append_nil]
  show straightSegment witnessY site1 2 ++
      straightSegment (Function.update witnessY 2 (site1 2)) site1 1 ++
      straightSegment (Function.update (Function.update witnessY 2 (site1 2)) 1 (site1 1))
        site1 0 = [((0 : Fin 3), true)]
  have h2 : coordSteps witnessY site1 (2 : Fin 3) = 0 := by decide
  have h1 : coordSteps (Function.update witnessY 2 (site1 2)) site1 (1 : Fin 3) = 0 := by decide
  have h0 : coordSteps (Function.update (Function.update witnessY 2 (site1 2)) 1 (site1 1))
      site1 (0 : Fin 3) = 1 := by decide
  simp only [straightSegment, h2, h1, h0, List.replicate_zero, List.replicate_one,
    List.nil_append]

theorem transportPath_to_site1_shift :
    transportPath witnessY witnessY (0 : Fin 3) 1 = [((0 : Fin 3), true)] := by
  show GammaPath witnessY witnessY ++
      straightSegment witnessY (pathSite witnessY 0 1) (0 : Fin 3) = [((0 : Fin 3), true)]
  rw [GammaPath_self, List.nil_append, pathSite_succ, pathSite_zero, shift_witnessY_eq_site1]
  unfold straightSegment coordSteps
  have hval : site1 (0 : Fin 3) - witnessY (0 : Fin 3) = 1 := by decide
  rw [hval]; rfl

/-- **`q1RealMain(U)(d4ConfigSuTwo)` at `targetCoarseBond`**: reduces to exactly TWO terms, both
transported by `RMap (U (witnessY,0))`, giving `(1/4)•(RMap(U(witnessY,0)) suTwoWitness)`. -/
theorem q1RealMain_d4ConfigSuTwo
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    q1RealMain U witnessEll d4ConfigSuTwo targetCoarseBond =
      (1 / 4 : ℝ) • RMap (U (witnessY, (0 : Fin 3))) suTwoWitness := by
  show (1 / (witnessEll : ℝ) ^ 3) •
      ∑ x ∈ blockOf targetCoarseBond.1.1 witnessEll,
        rZeroA U targetCoarseBond.1.1 x d4ConfigSuTwo targetCoarseBond.2 witnessEll = _
  have hbase : (targetCoarseBond : LatticeOperators.CoarseBond witnessL witnessEll).1.1 =
      witnessY := rfl
  have hdir : (targetCoarseBond : LatticeOperators.CoarseBond witnessL witnessEll).2 =
      (0 : Fin 3) := rfl
  rw [hbase, hdir]
  have hEll : witnessEll = 2 := rfl
  -- split the block sum into the "direct-term" part and the "shift-term" part, each a single
  -- nonzero contributor, using rZeroA_ell2 + Finset.sum_add_distrib.
  have hsplit : ∀ x ∈ blockOf witnessY witnessEll,
      rZeroA U witnessY x d4ConfigSuTwo 0 witnessEll =
        RMap (periodicPathHolonomy U witnessY (transportPath witnessY x 0 0))
          (d4ConfigSuTwo (x, 0)) +
        RMap (periodicPathHolonomy U witnessY (transportPath witnessY x 0 1))
          (d4ConfigSuTwo (periodicLatticeShift x 0, 0)) := by
    intro x _; rw [hEll, rZeroA_ell2]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hdirect : ∑ x ∈ blockOf witnessY witnessEll,
      RMap (periodicPathHolonomy U witnessY (transportPath witnessY x 0 0))
        (d4ConfigSuTwo (x, 0)) = RMap (U (witnessY, (0:Fin 3))) suTwoWitness := by
    rw [Finset.sum_eq_single site1]
    · rw [transportPath_to_site1_direct, d4ConfigSuTwo_at_site1]
      show RMap (periodicPathHolonomy U witnessY [((0:Fin 3),true)]) suTwoWitness = _
      show RMap (U (witnessY,(0:Fin 3)) *
        periodicPathHolonomy U (periodicLatticeShift witnessY 0) []) suTwoWitness = _
      rw [show periodicPathHolonomy U (periodicLatticeShift witnessY 0) ([] :
        List (Fin 3 × Bool)) = 1 from rfl, mul_one]
    · intro x _ hx
      have : d4ConfigSuTwo (x, (0:Fin 3)) = 0 :=
        d4ConfigSuTwo_elsewhere (fun h => hx (Prod.mk.injEq .. ▸ h).1)
      rw [this, map_zero]
    · intro h; exact absurd site1_mem_block h
  have hshift : ∑ x ∈ blockOf witnessY witnessEll,
      RMap (periodicPathHolonomy U witnessY (transportPath witnessY x 0 1))
        (d4ConfigSuTwo (periodicLatticeShift x 0, 0)) = RMap (U (witnessY,(0:Fin 3))) suTwoWitness := by
    rw [Finset.sum_eq_single witnessY]
    · rw [transportPath_to_site1_shift, shift_witnessY_eq_site1, d4ConfigSuTwo_at_site1]
      show RMap (periodicPathHolonomy U witnessY [((0:Fin 3),true)]) suTwoWitness = _
      show RMap (U (witnessY,(0:Fin 3)) *
        periodicPathHolonomy U (periodicLatticeShift witnessY 0) []) suTwoWitness = _
      rw [show periodicPathHolonomy U (periodicLatticeShift witnessY 0) ([] :
        List (Fin 3 × Bool)) = 1 from rfl, mul_one]
    · intro x _ hne
      have hshiftne : periodicLatticeShift x (0:Fin 3) ≠ site1 := by
        intro h
        exact hne (periodicLatticeShift_injective (0:Fin 3) (h.trans shift_witnessY_eq_site1.symm))
      have : d4ConfigSuTwo (periodicLatticeShift x 0, (0:Fin 3)) = 0 :=
        d4ConfigSuTwo_elsewhere (fun h => hshiftne (Prod.mk.injEq .. ▸ h).1)
      rw [this, map_zero]
    · intro h; exact absurd witnessY_mem_block h
  rw [hdirect, hshift, hEll]
  show (1 / (2:ℝ)^3) • (RMap (U (witnessY,(0:Fin 3))) suTwoWitness +
    RMap (U (witnessY,(0:Fin 3))) suTwoWitness) = _
  rw [← two_smul ℝ, smul_smul]
  norm_num

theorem Q1Real_d4_trivialU :
    Q1Real (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) d4ConfigSuTwo
        targetCoarseBond = (1 / 4 : ℝ) • suTwoWitness := by
  rw [Q1Real_apply, q1RealMain_d4ConfigSuTwo]
  show (1/4:ℝ) • RMap ((AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL)
    (witnessY,(0:Fin 3))) suTwoWitness = _
  have : (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) (witnessY,(0:Fin 3)) = 1 :=
    rfl
  rw [this, RMap_one]; rfl

theorem Q1Real_d4_witnessU :
    Q1Real witnessU d4ConfigSuTwo targetCoarseBond = -((1 / 4 : ℝ) • suTwoWitness) := by
  rw [Q1Real_apply, q1RealMain_d4ConfigSuTwo, witnessU_at_x_mu, RMap_witnessMElem, smul_neg]

/-- **GENUINE, NON-VACUOUS `U`-dependence, built from a FORWARD holonomy** (not the convicted
file's invented backward reference path): the values at `trivialU` and `witnessU` genuinely
differ. -/
theorem Q1Real_d4_genuinely_U_dependent :
    Q1Real (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) d4ConfigSuTwo
        targetCoarseBond ≠
      Q1Real witnessU d4ConfigSuTwo targetCoarseBond := by
  rw [Q1Real_d4_trivialU, Q1Real_d4_witnessU]
  intro h
  apply suTwoWitness_ne_zero
  have h2 : (1 / 4 : ℝ) • suTwoWitness + (1 / 4 : ℝ) • suTwoWitness = 0 := by
    nth_rewrite 1 [h]; exact neg_add_cancel _
  rw [← add_smul] at h2
  have h3 : (1 / 4 + 1 / 4 : ℝ) = 1 / 2 := by norm_num
  rw [h3] at h2
  rcases smul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

#print axioms d4ConfigSuTwo_at_site1
#print axioms d4ConfigSuTwo_elsewhere
#print axioms transportPath_to_site1_direct
#print axioms transportPath_to_site1_shift
#print axioms q1RealMain_d4ConfigSuTwo
#print axioms Q1Real_d4_trivialU
#print axioms Q1Real_d4_witnessU
#print axioms Q1Real_d4_genuinely_U_dependent

/-! ## §8 — THE STRUCTURAL MUTATION (S82): the transport genuinely varies BY FINE BOND within a
SINGLE block-site `x`, the exact per-bond dependence a single fixed conjugation cannot reproduce. -/

/-- At `x = c₋ = witnessY`, the `i=0` fine bond's transport is EMPTY (holonomy `1`, `RMap 1 = id`),
while the `i=1` fine bond's transport is the nonempty `[(0,true)]` (holonomy `witnessU(witnessY,0)
= witnessMElem`, `RMap witnessMElem suTwoWitness = -suTwoWitness ≠ suTwoWitness`) — the SAME
block-site `x`, a DIFFERENT transport per bond. A single fixed `R0(U)` (the convicted `Q1LM`'s own
construction) could never distinguish these two bonds; this operator genuinely does. -/
theorem transport_varies_within_single_x :
    RMap (periodicPathHolonomy witnessU witnessY (transportPath witnessY witnessY 0 0))
        suTwoWitness ≠
      RMap (periodicPathHolonomy witnessU witnessY (transportPath witnessY witnessY 0 1))
        suTwoWitness := by
  have h0 : transportPath witnessY witnessY (0 : Fin 3) 0 = [] := by
    show GammaPath witnessY witnessY ++ straightSegment witnessY (pathSite witnessY 0 0) 0 = []
    simp [pathSite_zero, GammaPath_self, straightSegment_self]
  have h1 : transportPath witnessY witnessY (0 : Fin 3) 1 = [((0 : Fin 3), true)] := by
    show GammaPath witnessY witnessY ++
        straightSegment witnessY (pathSite witnessY 0 1) (0 : Fin 3) = [((0 : Fin 3), true)]
    rw [GammaPath_self, List.nil_append, pathSite_succ, pathSite_zero, shift_witnessY_eq_site1]
    unfold straightSegment coordSteps
    have hval : site1 (0 : Fin 3) - witnessY (0 : Fin 3) = 1 := by decide
    rw [hval]; rfl
  rw [h0, h1]
  show RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) suTwoWitness ≠
    RMap (witnessU (witnessY,(0:Fin 3)) *
      periodicPathHolonomy witnessU (periodicLatticeShift witnessY 0) []) suTwoWitness
  rw [show periodicPathHolonomy witnessU (periodicLatticeShift witnessY 0) ([] :
    List (Fin 3 × Bool)) = 1 from rfl, mul_one, RMap_one, witnessU_at_x_mu, RMap_witnessMElem,
    LinearMap.id_apply]
  intro h
  apply suTwoWitness_ne_zero
  have h2 : suTwoWitness + suTwoWitness = 0 := by
    nth_rewrite 1 [h]; exact neg_add_cancel _
  rw [← two_smul ℝ] at h2
  rcases smul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

#print axioms transport_varies_within_single_x

/-! ## §9 — `q1RealKernel`: the `Q₁(U)B=0` locus, a genuine `U`-parameterized `Submodule`. -/

noncomputable def q1RealKernel (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) : Submodule ℝ (Bond witnessL → SuTwo) := LinearMap.ker (Q1Real U)

theorem deltaWitnessConfig_notMem_q1RealKernel
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL) :
    deltaWitnessConfig ∉ q1RealKernel U := by
  intro hmem
  rw [q1RealKernel, LinearMap.mem_ker] at hmem
  exact Q1Real_deltaWitnessConfig_ne_zero U (congrFun hmem targetCoarseBond)

theorem q1RealKernel_ne_top (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ)
    witnessL) : q1RealKernel U ≠ ⊤ := fun h =>
  deltaWitnessConfig_notMem_q1RealKernel U (h ▸ Submodule.mem_top)

/-- The checkerboard alternator (reused SHAPE from `BackgroundAveraging.checkerConfigSuTwo`/
`QOne.checkerConfig`, LAW-19, re-proved fresh so this file stays independent of the convicted
file). Cancels pointwise BEFORE any transport is applied (`d4`/`delta` are not needed here since the
cancellation is at the level of the RAW fine-bond values, and `RMap` is linear so it commutes with
the pointwise-zero collapse termwise). -/
noncomputable def checkerConfigSuTwo : Bond witnessL → SuTwo :=
  fun e => if e.2 = (0 : Fin 3) then ((-1 : ℝ) ^ (e.1 0).val) • suTwoWitness else 0

theorem checkerConfigSuTwo_ne_zero : checkerConfigSuTwo ≠ 0 := by
  intro h
  have := congrFun h (witnessY, (0 : Fin 3))
  simp only [checkerConfigSuTwo, witnessY, Pi.zero_apply] at this
  norm_num at this
  exact suTwoWitness_ne_zero this

theorem checkerConfigSuTwo_pointwise_cancel (x : PeriodicLatticeSite witnessL) :
    checkerConfigSuTwo (x, (0 : Fin 3)) +
      checkerConfigSuTwo (periodicLatticeShift x 0, (0 : Fin 3)) = 0 := by
  have hshift : (periodicLatticeShift x 0) 0 = x 0 + 1 := by
    simp [periodicLatticeShift, Function.update_self]
  have h1 : checkerConfigSuTwo (x, (0 : Fin 3)) = ((-1 : ℝ) ^ (x 0).val) • suTwoWitness := by
    simp [checkerConfigSuTwo]
  have h2 : checkerConfigSuTwo (periodicLatticeShift x 0, (0 : Fin 3)) =
      ((-1 : ℝ) ^ ((periodicLatticeShift x 0) 0).val) • suTwoWitness := by
    simp [checkerConfigSuTwo]
  rw [h1, h2, hshift, ← add_smul]
  generalize hv : x 0 = v
  have : ((-1 : ℝ) ^ v.val + (-1 : ℝ) ^ (v + 1).val) = 0 := by
    fin_cases v <;> norm_num [Fin.add_def, witnessL]
  rw [this, zero_smul]

/-- **PROVED ONLY AT `trivialU`** (named honestly, not silently generalized): at a genuinely
non-flat `U`, the two `rZeroA_ell2` addends carry DIFFERENT transports (`RMap` of two different
holonomies), so the RAW pointwise cancellation `checkerConfigSuTwo_pointwise_cancel` does NOT
transfer term-by-term — a real mathematical obstruction distinct from anything the convicted file
faced (its `R0` was `x`/`b`-independent, so the SAME cancellation trick worked at every `U`; THIS
operator's genuine path-dependence means that trick is only available where every transport is the
identity, i.e. at `trivialU`). Attempted and abandoned for general `U`; recorded as a named residual
below, not silently dropped. -/
theorem checkerConfigSuTwo_mem_q1RealKernel_trivialU :
    checkerConfigSuTwo ∈
      q1RealKernel (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) := by
  rw [q1RealKernel, LinearMap.mem_ker, Q1Real, LinearMap.coe_mk, AddHom.coe_mk]
  funext b
  show q1RealMain (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) witnessEll
      checkerConfigSuTwo b = 0
  unfold q1RealMain
  rcases eq_or_ne b.2 0 with hmu | hmu
  · have hzero : ∀ x ∈ blockOf b.1.1 witnessEll,
        rZeroA (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) b.1.1 x
          checkerConfigSuTwo b.2 witnessEll = 0 := by
      intro x _
      rw [hmu, rZeroA_trivialU]
      show ∑ i ∈ Finset.range 2, checkerConfigSuTwo (pathSite x 0 i, 0) = 0
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pathSite_zero,
        pathSite_succ]
      exact checkerConfigSuTwo_pointwise_cancel x
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, smul_zero]
  · have hzero : ∀ x ∈ blockOf b.1.1 witnessEll,
        rZeroA (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) b.1.1 x
          checkerConfigSuTwo b.2 witnessEll = 0 := by
      intro x _
      rw [rZeroA_trivialU]
      apply Finset.sum_eq_zero
      intro i _
      simp only [checkerConfigSuTwo]
      rw [if_neg hmu]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, smul_zero]

theorem q1RealKernel_trivialU_ne_bot :
    q1RealKernel (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) ≠ ⊥ := by
  intro hbot
  apply checkerConfigSuTwo_ne_zero
  rw [← Submodule.mem_bot ℝ (x := checkerConfigSuTwo), ← hbot]
  exact checkerConfigSuTwo_mem_q1RealKernel_trivialU

#print axioms deltaWitnessConfig_notMem_q1RealKernel
#print axioms q1RealKernel_ne_top
#print axioms checkerConfigSuTwo_ne_zero
#print axioms checkerConfigSuTwo_pointwise_cancel
#print axioms checkerConfigSuTwo_mem_q1RealKernel_trivialU
#print axioms q1RealKernel_trivialU_ne_bot

end AdalyFormal.Balaban.Q1Real
