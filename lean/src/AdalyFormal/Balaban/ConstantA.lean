/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib

set_option autoImplicit false

/-!
# CMP99b's constant `a` (eq. (3.156)) — source trail, and its two distinct formal objects

**Dispatch target**: `Balaban/DeltaKRecursive.lean`'s `RGScaleFamily.a : ℕ → ℝ` field carries the
constant `a` of CMP99b (3.156) as an OPAQUE, `k`-indexed field (a conservative placeholder — see
that file's docstring). This file re-derives, from the primary source (not from that placeholder's
shape), what `a` actually IS, and builds the two genuinely distinct mathematical objects the source
trail turns up under that one symbol.

## THE SOURCE TRAIL, PAGE BY PAGE, VERBATIM

**Where `a` is bare-quoted at the point of use** (`corpus/pages/CMP99b_p428.md`, adjudicated):
CMP99b (3.156), p.428: `⟨B,(QG₁Q*)⁻¹B⟩ − a⟨B,B⟩ − 2⟨H₁D̃⁽²⁾(B),J⟩ = ⟨B,Δ_kB⟩`. No definition of
`a` appears on p.427/p.428 itself — both are USE sites, following LAW-1 of this dispatch ("search
the earliest paper in the series that carries the object").

**Where `a` is DEFINED** (rendered at 400dpi, `compute/a_renders/CMP99b_p393-05.png` /
`CMP99b_p393-06.png`, printed pp.393-394, cross-checked against
`compute/w5_decider/extract/balaban_CMP99_1985_propagators_backgroundfield.txt` and confirmed
image-correct — the pdftotext OCR mangles the Greek/subscript-heavy lines but the *content* of the
formulas is legible and unambiguous on the 400dpi render):

CMP99b p.393, eq. (3.16) — the operator `Q*aQ` used to build `Δ_a`:
```
⟨A, Q*aQA⟩ = Σ_{j=0}^k a Σ_{b∈Λⱼ} (Lʲη)^{d-2}|(Qⱼ(U)A)(b)|²                         (3.16)
```
— a single CONSTANT `a` (no subscript), summed identically at every `j = 0,…,k`.

CMP99b p.393, eq. (3.26): `Δ_a(U) = Δ^η(U) + D^ηR(U)D^η* + Q*(U)aQ(U)`, "or simply
`Δ_a = Δ + DRD* + Q*aQ`. **It coincides with `Δ_a` in (2.19) if `U = 1`**." — this is the operator
whose inverse is `G` (3.27), and CMP99b (3.128)'s `G₁` ("a‖QA‖²" term) and (3.155)/(3.156)'s `a` are
built from exactly this same bare, unsubscripted symbol.

CMP99b p.394, eq. (3.24) — a DIFFERENT, SIBLING operator `Q'*aQ'` (used for the λ-gauge-fixing
average, not the `A`-average):
```
⟨λ, Q'*aQ'λ⟩ = Σ_{j=0}^k aⱼ Σ_{y∈Λⱼ} (Lʲη)^{d-2}|(Q'ⱼ(U)λ)(y)|²                      (3.24)
```
"the numbers `aⱼ` satisfy the recursive equations `a_{j+1} = a·aⱼ/(a·L⁻² + aⱼ)`, `a₁ = a₀ = a > 0`."
— here the coefficient genuinely VARIES with the scale index `j` (recursively defined), with base
value the SAME `a`.

**CMP95 cross-reference** (rendered `compute/a_renders` is CMP99b-only; CMP95's locus was already
transcribed at `compute/coercivity_corpus_map/txt/balaban_CMP95_1984_propagators_I.txt`, lines
648-696, matching CMP95 (1.65)-(1.73)): CMP95 (1.68)-(1.69), "Propagators for Lattice Gauge
Theories I" p.394 (CMP95's OWN printed pagination, a different paper from CMP99b despite the
coincidental page-number overlap):
```
exp[−½⟨A,ΔA⟩ − (1/2α)‖RD*A‖² − ½a‖B−QₖA‖²]                                          (1.68)
⟨A,Δ_aA⟩ = ⟨A,Δ*ΔA⟩+⟨A,DRD*A⟩+a⟨A,Q*QA⟩ = ⟨A,ΔA⟩−⟨A,DPD*A⟩+a⟨A,Q*QA⟩, R=I−P            (1.69)
```
and the text immediately after (1.69): "it is non-negative as a sum of two non-negative operators
`Δ−DPD*` and `aQ*Q`, `a>0`."

## VERDICT — does `a` depend on `k`? (the load-bearing question)

**NO, for the bare symbol `a` used at every one of (3.16)/(3.26)/(3.128)/(3.155)/(3.156)/CMP95
(1.68)-(1.69): it is a single FIXED positive real number, chosen once, carried unchanged through
every scale `j = 0,…,k` and every renormalization step `k`.** This is not an inference from silence
— (3.16) literally sums the SAME symbol `a` (no subscript) over `j`, and CMP99b states its `Δ_a`
"coincides with `Δ_a` in (2.19) if `U=1`" — i.e. the SAME object CMP95 already built at `U=1`,
confirming the constant is carried, unchanged, across the whole paper series, not re-chosen per
paper or per scale.

**Same symbol, different object trap (avoided): `aⱼ` in (3.24) is NOT the `a` of (3.156).** It is a
genuinely `j`-indexed (hence in Balaban's outer construction, effectively `k`-indexed) SEQUENCE,
defined by an explicit recursion, used only in the SIBLING gauge-fixing operator `Q'*aQ'` — a
structurally distinct object from `Q*aQ`'s bare `a`, sharing only the base value (`a₁=a₀=a`). §2
below builds and analyzes this sequence on its own terms, because it is the one place in this whole
trail where a `k`-dependent degradation of a Balaban constant is a real, provable, non-trivial fact
— directly on point for "is a bound uniform in `k`", even though it answers a DIFFERENT `a`.

**CMP95 (1.68)'s `a` is the SAME `a` as CMP99b's, by the source's own cross-reference, not merely
same-named.** CMP99b (3.26) explicitly identifies its `Δ_a` with "`Δ_a` in (2.19) of [4]" at `U=1`;
CMP95's own `Δ_a` (1.69) plays exactly this `U=1`-specialization role (CMP95 is titled "Propagators
for Lattice Gauge Theories **I**" — the abelian/free warm-up paper the later background-field papers
generalize). Both loci use `a` for the identical algebraic role: a strictly positive scalar weight
on the `Q*Q` quadratic form, added to make `Δ_a` (hence its inverse `G`) positive-definite/invertible
— confirmed by BOTH papers' own text making the identical positivity argument ("non-negative as a
sum of `Δ−DPD*`/`Δ+DRD*` and `aQ*Q`, `a>0`"). §3 below builds this shared TEMPLATE once and
instantiates both loci from it, and proves `a>0` is load-bearing for positivity (not vacuous).

## WHAT THIS FILE DOES NOT DO

It does not assign a NUMERICAL value to `a` — none of the rendered pages state one; `a` is a free
regularization-weight parameter of Balaban's whole RG scheme (like `M`, `α₀`, `L`), constrained only
by `a > 0` on every page it appears. It does not re-derive CMP99b (3.16)'s FULL multi-block sum (the
`Λⱼ`-indexed geometric content) — only the SCALAR role of `a`/`aⱼ` inside it, which is this
dispatch's actual target.
-/

namespace AdalyFormal.Balaban.ConstantA

/-! ## §1 — the bare `a`: a fixed positive real, genuinely NOT `k`-indexed by construction

CMP99b (3.16)/(3.26)/(3.128)/(3.155)/(3.156) and CMP95 (1.68)/(1.69) all use one bare symbol `a`,
never `a_k`. We build this as a plain `ℝ` field (not `ℕ → ℝ`) and prove the "value used at scale
`k`" is literally constant — CONTRASTED against a mutation where a hypothetical `k`-dependent
weight genuinely varies, so the constancy claim is falsifiable (S82), not forced by the type. -/

/-- CMP99b/CMP95's constant `a`: a single fixed positive real, page-cited above. -/
structure BaseConstant where
  a : ℝ
  a_pos : 0 < a

/-- **The value CMP99b's `Q*aQ`/`Δ_a`/(3.156) actually uses at RG step `k`**: literally `bc.a`,
with `k` appearing only as an unused argument — the Lean-checked form of "the source formula has no
`k`-subscript on `a`, ever." -/
def usedAt (bc : BaseConstant) (_k : ℕ) : ℝ := bc.a

/-- **THE ANSWER, as a theorem**: the coefficient CMP99b's actual construction uses is identical at
every scale `k`. -/
theorem usedAt_const (bc : BaseConstant) (k k' : ℕ) : usedAt bc k = usedAt bc k' := rfl

/-! ### §1b — GARBAGE SUBSTITUTION (S82): this constancy claim is not forced by the type

`usedAt`'s codomain `ℕ → ℝ` (via its argument shape) COULD carry genuine `k`-dependence — a
hypothetical construction that degraded `a` with scale would live in the very same type. We exhibit
one, and show the constancy check genuinely FAILS on it, proving `usedAt_const` is a real fact
about CMP99b's specific choice, not a tautology of the signature. -/

/-- A hypothetical DEGRADING weight `a/(k+1)` — the mutation. -/
noncomputable def usedAtMutant (bc : BaseConstant) (k : ℕ) : ℝ := bc.a / (k + 1)

/-- The mutation genuinely varies with `k` (the constancy check FAILS on it), given `bc.a > 0`. -/
theorem usedAtMutant_not_const (bc : BaseConstant) :
    usedAtMutant bc 0 ≠ usedAtMutant bc 1 := by
  have ha := bc.a_pos
  simp only [usedAtMutant]
  intro h
  norm_num at h
  linarith

#print axioms usedAt_const
#print axioms usedAtMutant_not_const

/-! ## §2 — the SIBLING object `aⱼ` (CMP99b (3.24), p.394): a genuine, scale-varying recursion

`aⱼ` is used in `Q'*aQ'`, the gauge-fixing average operator — a DIFFERENT operator from `Q*aQ`
(§1's constant `a`). Its recursion `a_{j+1} = a·aⱼ/(a·L⁻² + aⱼ)`, `a₁=a₀=a>0` is abstracted below
with `d := a/L²` held as an explicit parameter, so the induction is pure algebra (no `L`-power
bookkeeping inside the recursive step). -/

/-- `aSeqAux a d n` computes the sequence `a₁, a₂, a₃, …` of CMP99b (3.24) (`aSeqAux a d 0 = a₁`),
with `d` standing for `a/L²`. -/
noncomputable def aSeqAux (a d : ℝ) : ℕ → ℝ
  | 0 => a
  | (n + 1) => a * aSeqAux a d n / (d + aSeqAux a d n)

/-- CMP99b's own instantiation: `d = a/L²`, matching `a_{j+1} = a·aⱼ/(a·L⁻² + aⱼ)` verbatim. -/
noncomputable def aSeq (a L : ℝ) : ℕ → ℝ := aSeqAux a (a / (L * L))

/-- **THE UNIFORM-IN-`j` BOUND** (the genuinely load-bearing recursive fact this trail turns up):
given `0 < d < a` (CMP99b's own case, `d = a/L² < a` whenever `L > 1`), the sequence stays in the
CLOSED interval `[a-d, a]` at every step — in particular NEVER degrades below the fixed positive
constant `a - d`, uniformly in `j`. -/
theorem aSeqAux_invariant (a d : ℝ) (ha : 0 < a) (hd : 0 < d) (hda : d < a) :
    ∀ n, (a - d) ≤ aSeqAux a d n ∧ aSeqAux a d n ≤ a := by
  intro n
  induction n with
  | zero =>
    have h0 : aSeqAux a d 0 = a := rfl
    rw [h0]; exact ⟨by linarith, le_refl a⟩
  | succ k ih =>
    obtain ⟨hlo, hhi⟩ := ih
    have hx_pos : 0 < aSeqAux a d k := by linarith
    have hdenom_pos : 0 < d + aSeqAux a d k := by linarith
    have hstep : aSeqAux a d (k + 1) = a * aSeqAux a d k / (d + aSeqAux a d k) := rfl
    refine ⟨?_, ?_⟩
    · rw [hstep, le_div_iff₀ hdenom_pos]
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hd.le]
    · rw [hstep, div_le_iff₀ hdenom_pos]
      nlinarith [mul_pos ha hd]

/-- **Positivity**, a direct corollary of the lower bound. -/
theorem aSeqAux_pos (a d : ℝ) (ha : 0 < a) (hd : 0 < d) (hda : d < a) (n : ℕ) :
    0 < aSeqAux a d n := by
  have := (aSeqAux_invariant a d ha hd hda n).1
  linarith

/-- **Monotone non-increasing**: the sequence only ever decreases (or stays put at the fixed
point), matching CMP99b's own description of a shrinking-weight recursion. -/
theorem aSeqAux_monotone (a d : ℝ) (ha : 0 < a) (hd : 0 < d) (hda : d < a) (n : ℕ) :
    aSeqAux a d (n + 1) ≤ aSeqAux a d n := by
  obtain ⟨hlo, hhi⟩ := aSeqAux_invariant a d ha hd hda n
  have hx_pos : 0 < aSeqAux a d n := by linarith
  have hdenom_pos : 0 < d + aSeqAux a d n := by linarith
  have hstep : aSeqAux a d (n + 1) = a * aSeqAux a d n / (d + aSeqAux a d n) := rfl
  rw [hstep, div_le_iff₀ hdenom_pos]
  nlinarith [mul_le_mul_of_nonneg_left hlo hx_pos.le]

#print axioms aSeqAux_invariant
#print axioms aSeqAux_pos
#print axioms aSeqAux_monotone

/-! ### §2b — `L > 1` is genuinely load-bearing: the degenerate `L = 1` mutation (standing trap)

At `L = 1`, `d = a/L² = a`, violating `hda : d < a` — exactly the boundary CMP99b's own recursion
excludes (Balaban's `L` is always an integer coarse-graining factor `> 1`). We compute the `a=1,L=1`
sequence in CLOSED FORM and show it decays to `0` — i.e. the uniform positive lower bound genuinely
FAILS at this degenerate value, proving `hda`/`L > 1` is doing real work, not padding. -/

/-- At `a=1, d=1` (the `a=1,L=1` degenerate instance), the sequence has the exact closed form
`1/(n+1)`. -/
theorem aSeqAux_one_one_eq (n : ℕ) : aSeqAux 1 1 n = 1 / (n + 1 : ℝ) := by
  induction n with
  | zero => simp [aSeqAux]
  | succ k ih =>
    have hstep : aSeqAux (1:ℝ) 1 (k + 1) = 1 * aSeqAux 1 1 k / (1 + aSeqAux 1 1 k) := rfl
    rw [hstep, ih]
    have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
    push_cast
    field_simp

/-- **The degeneracy, as a theorem**: unlike the `L>1` case (bounded away from `0` uniformly by
`aSeqAux_pos`'s companion lower bound), the `L=1` sequence gets arbitrarily close to `0` — for
every `ε>0` some term of the sequence is below it. This is the exact contrast the "standing traps"
(`ell = 1`-type degeneracies) warn about, exhibited concretely rather than merely asserted. -/
theorem aSeqAux_one_one_not_bounded_away_from_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, aSeqAux 1 1 n < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  refine ⟨n, ?_⟩
  rw [aSeqAux_one_one_eq]
  rw [div_lt_iff₀ (by positivity)]
  have hn1 : (1:ℝ) / ε < (n:ℝ) + 1 := by linarith
  rw [div_lt_iff₀ hε] at hn1
  linarith

#print axioms aSeqAux_one_one_eq
#print axioms aSeqAux_one_one_not_bounded_away_from_zero

/-- **The `L=2, a=1` non-degenerate contrast, computed exactly for two steps**: `aSeq 1 2 0 = 1`,
`aSeq 1 2 1 = 4/5`, both `≥ a-d = 1 - 1/4 = 3/4` (`aSeqAux_invariant`'s guaranteed floor) —
concretely witnessing the bound is not vacuous even at the smallest admissible `L`. -/
example : aSeq 1 2 0 = 1 := by simp [aSeq, aSeqAux]

example : aSeq 1 2 1 = 4 / 5 := by
  show aSeqAux 1 (1 / (2 * 2)) 1 = 4 / 5
  have hstep : aSeqAux (1:ℝ) (1 / (2*2)) (0 + 1)
      = 1 * aSeqAux 1 (1/(2*2)) 0 / ((1/(2*2)) + aSeqAux 1 (1/(2*2)) 0) := rfl
  rw [hstep]
  norm_num [aSeqAux]

/-! ## §3 — the SHARED TEMPLATE across CMP95 (1.69) and CMP99b (3.26): `a>0` is load-bearing

Both loci build `Δ_a` as (a base/cross term) `+ a · (Q*Q-type quadratic term)`, and both papers'
own text makes the identical positivity argument ("non-negative as a sum of two non-negative
operators … and `aQ*Q`, `a>0`" — CMP95 p.394, quoted verbatim in the file docstring). We build this
template once, generically, and show `a > 0` is genuinely necessary (not decorative) via a concrete
sign-flip counterexample. -/

/-- The shared template: `Δ_a`'s quadratic form value `= baseTerm + a · qqTerm`, where `baseTerm`
stands for CMP95's `⟨A,ΔA⟩-⟨A,DPD*A⟩` / CMP99b's `⟨A,Δ^ηA⟩+⟨A,D^ηR(U)D^η*A⟩`, and `qqTerm` for
`⟨A,Q*QA⟩` resp. `⟨A,Q*(U)Q(U)A⟩`. -/
def deltaAQuadForm (baseTerm qqTerm a : ℝ) : ℝ := baseTerm + a * qqTerm

/-- **Positivity, exactly as both papers argue it**: a sum of two non-negatives (given `a>0` and
`qqTerm≥0`) is non-negative. -/
theorem deltaAQuadForm_nonneg {baseTerm qqTerm a : ℝ}
    (hbase : 0 ≤ baseTerm) (hqq : 0 ≤ qqTerm) (ha : 0 < a) :
    0 ≤ deltaAQuadForm baseTerm qqTerm a := by
  unfold deltaAQuadForm
  have : 0 ≤ a * qqTerm := mul_nonneg ha.le hqq
  linarith

/-- **`a > 0` is load-bearing, not decorative** (S82 garbage substitution): at `baseTerm=0,
qqTerm=1`, taking `a=-1` (violating `a>0`) makes the SAME quadratic form strictly negative — the
positivity theorem's hypothesis is not vacuous. -/
example : deltaAQuadForm 0 1 (-1) < 0 := by unfold deltaAQuadForm; norm_num

/-- CMP99b (3.26)'s instantiation of the template: `baseTerm := ⟨A,Δ^ηA⟩+⟨A,D^ηR(U)D^η*A⟩`,
`qqTerm := ⟨A,Q*(U)Q(U)A⟩`. -/
def CMP99b_DeltaA_quadForm (etaLaplacianTerm DRDstarTerm QstarQTerm a : ℝ) : ℝ :=
  deltaAQuadForm (etaLaplacianTerm + DRDstarTerm) QstarQTerm a

/-- CMP95 (1.69)'s instantiation: `baseTerm := ⟨A,ΔA⟩-⟨A,DPD*A⟩`, `qqTerm := ⟨A,Q*QA⟩`. -/
def CMP95_DeltaA_quadForm (laplacianTerm DPDstarTerm QstarQTerm a : ℝ) : ℝ :=
  deltaAQuadForm (laplacianTerm - DPDstarTerm) QstarQTerm a

/-- **The two papers' `Δ_a` are literally the same template, instantiated**: this is the formal
witness that the algebraic ROLE of `a` (a positive scalar weight on a `Q*Q`-type quadratic term,
added to a base/cross term to secure positivity) is identical at both loci — `rfl`, since both
definitions unfold to `deltaAQuadForm` with the same third argument `a`. -/
theorem CMP99b_and_CMP95_share_template
    (etaLap DRDstar DPDstar QstarQ a : ℝ) :
    CMP99b_DeltaA_quadForm etaLap DRDstar QstarQ a
      = deltaAQuadForm (etaLap + DRDstar) QstarQ a
    ∧ CMP95_DeltaA_quadForm (etaLap + DRDstar + DPDstar) DPDstar QstarQ a
      = deltaAQuadForm (etaLap + DRDstar) QstarQ a := by
  constructor
  · rfl
  · unfold CMP95_DeltaA_quadForm deltaAQuadForm; ring

#print axioms deltaAQuadForm_nonneg
#print axioms CMP99b_and_CMP95_share_template

end AdalyFormal.Balaban.ConstantA
