/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DiscretePoincare
import AdalyFormal.Balaban.CrossSectionPositivity

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The mesh-uniform 2-D discrete Poincaré, and CMP96 `(2.127)`'s operator bound ~~UNDER A NAMED
# (UNRESOLVED) NORMALIZATION~~ AT THE NORMALIZATION THE OPERATOR'S DEFINING PAGE FIXES — `d = 3`
#
# (Title amended S75, 2026-08-09: the normalization `c = 1` is no longer named-and-unresolved. It is
# derived from CMP89 (1.3), p.572, image-verified. See the ⚠ block.)

This file lifts the 1-D crude discrete Poincaré inequality
(`DiscretePoincare.discrete_poincare_crude`) to the 2-D cross-section by the ANOVA / law-of-total-
variance argument, obtaining the **unconditional, kernel-checked, mesh-uniform** bound
`var2 ≤ n²·gradEnergy2`, and feeds it through `CrossSectionPositivity.cross_section_2127_iff_poincare`
to prove the inequality `gradEnergy2/n² + (sum2/n²)²/n² ≥ sumSq2/n⁴` about the **plain grid
quantities**. Both are TRUE without qualification (see `#print axioms`: no `sorryAx`).

## ⚠ STATUS OF THE `(2.127)` IDENTIFICATION — ~~REDUCED, **NOT CLOSED**~~ NORMALIZATION DERIVED; ONE CITATION INFERENCE REMAINS
## (prosecutor finding 2026-07-24; normalization settled 2026-08-09, `compute/mesh_substitution/`)

**Read this block with its amendments.** It is retained in full, struck where superseded (S75),
because the three-way fork it records is the reason the derivation below was worth doing, and
because one of its three bullets was not merely unresolved but **mathematically wrong** — a defect
worth leaving visible.

Whether `cross_section_2127_operator_bound` **is** CMP96 `(2.127)`'s deferred operator positivity
depends on ~~ONE unpinned interpretive step: the quadratic-form normalization~~ the quadratic-form
normalization `c := ⟨B,Δ_{Λ'}^{L^{-1},N}B⟩ / G_plain` of the cross-sectional operator,
`G_plain := Σ_{b⊂Λ'}|∂B_μ(b)|²` the plain bond-difference energy. This file proves the operator
bound with the first term rendered as `L^{-2}·G_plain`, i.e. it assumes **c = 1**. ~~Three source
readings give THREE DIFFERENT values, and the identification is faithful only under `c = 1`, which
the source does not unambiguously supply:~~

**AMENDED (S75, 2026-08-09): `c = 1` IS what the source supplies.** The three "readings" below are
not three conventions between which the source is silent. Read against the operator's own defining
page — CMP89 (1.3), p.572, image-verified at 300 dpi — exactly one of them is the operator's
normalization (`c = 1`, third bullet, now derived rather than assumed); one contains an arithmetic
error (`c = L^{-2}`, second bullet, which dropped the `η^{-1}` inside `D^η`); and one is a
term-match against a printed display that **no** weight can satisfy (`c = L^{-1}`, first bullet).
The step that is still an inference is not the normalization but the cross-paper identification of
`Δ_{Λ'}^{L^{-1},N}` with `Δ^{η,N}`; it is stated with its image-verified evidence in the Conclusion.
The original three bullets follow, each with its amendment:

* **Literal p.245 display** (`compute/xsec_operator_recon/renders/CMP96_p245-23.png`): the (2.126)
  parenthesis first term is `L^{-d}Σ_{b}|∂B_μ|² = L^{-3}G_plain`, stated `= L^{-2}⟨B,Δ^{L^{-1},N}B⟩`.
  Term-matching forces `⟨B,Δ^{L^{-1},N}B⟩ = L^{-(d-2)}G_plain = L^{-1}G_plain` → **c = L^{-1}**. Under
  this, `(2.127)` reduces to `Var ≤ L·G_plain`, which is **FALSE for L ≥ 16** (sharp cross-sectional
  Poincaré constant `C_P = 1/(2(1−cos(π/L))) ≈ L²/π² > L`; `compute/eq2127/numeric_2127.py`).

  **AMENDED (S75, 2026-08-09): this reading is not a rival CONVENTION — it is a printing/derivation
  error in the source, and that is now a theorem.** `MeshSubstitution.no_uniform_weight` proves that
  for every `L = n ≥ 2` and **every real weight `w`**, no single `w` reproduces both printed
  summands of `(2.126)`'s parenthesis simultaneously (witnesses: `witGrad` with `ΣB = 0, G > 0`, and
  `witConst` with `G = 0, ΣB = n²`) — so the display cannot be term-matched against any
  normalization at all, and `c = L^{-1}` is an artefact of trying. `grad_term_match_iff` isolates
  where: the printed gradient summand demands `w·n³ = 1` (`w = η^d`) while the `Q'` summand demands
  `w²n⁴ = 1` (`w = η^{d-1}`), and `grad_summand_off_by_exactly_L` /`clause1_gap` give the size of the
  discrepancy in closed form — the substituted form exceeds the printed parenthesis by exactly
  `(n−1)G/n³`, i.e. clause 1's gradient term is off by exactly one factor of `L`, in the direction
  that makes the printed statement STRONGER than what the operator supports
  (`substParen_ge_printedParen`, strict for `n ≥ 2, G > 0`).
* ~~**Balaban's generic inner product** (CMP95 p.21, `⟨f,g⟩ = Σ_x η^d f g`, `∂` = plain difference):
  a `(d−1)`-dim cross-section carries measure `η^{d-1} = L^{-2}`, giving `⟨B,ΔB⟩ = L^{-2}G_plain`
  → **c = L^{-2}** (even more false).~~

  **⚠ THIS BULLET IS MATHEMATICALLY WRONG. SUPERSEDED (S75, 2026-08-09,
  `compute/mesh_substitution/`, installed by `compute/norm_diamond_install/`). Corrected value:
  `c = 1`, and it is the SAME `c = 1` the third bullet calls "imported by analogy".** The error is
  a dropped `η^{-1}`, and it is inside the operator, not in the measure.

  `Δ^{η,N}` is not defined by "the generic inner product with `∂` the plain difference". It is
  defined by CMP89 **(1.3)**, p.572, which fixes BOTH factors at once (image-verified at 300 dpi,
  `compute/mesh_substitution/renders/CMP89_pdf02_printed572-02.png`, and re-read for this
  correction — the transcription below is `[VERBATIM]` from that render):

  > `⟨φ,(−Δ^{η,N}_{A,Ω})φ⟩ = Σ_{b⊂Ω} η^d |(D^η_A φ)(b)|² = Σ_{b⊂Ω} η^d |η^{-1}(U(A_b)φ(b_+) − φ(b_-))|²`

  The summand is `|D^η φ|²` with **`D^η = η^{-1}∂`**, the SCALED difference — not `|∂φ|²`. So the
  struck bullet applied the measure and then, in the same breath, used a different operator from the
  one whose normalization it was computing. Carrying the `η^{-1}` through on a `(d−1)`-dimensional
  cross-section:

  `⟨B,Δ^{η,N}B⟩ = Σ_{b⊂Λ'} η^{d-1}·|η^{-1}∂B|² = η^{d-1}·η^{-2}·G_plain = η^{d-3}·G_plain`,

  which at `d = 3` is `η^0·G_plain = G_plain` — **for every `L`, mesh-uniformly**. The `η^{-2}` from
  the scaled difference cancels the `η^{d-1} = η² = L^{-2}` cross-sectional measure exactly. Hence
  **`c = 1`**, which is the normalization THIS FILE ASSUMES, now derived from the operator's own
  defining page rather than imported from p.242 by analogy.

  In the kernel, staged (not yet a tree module) at
  `compute/mesh_substitution/stage/AdalyFormal/Balaban/MeshSubstitution.lean`, sorry-free, all 71
  declarations on `[propext, Classical.choice, Quot.sound]`:
  * `meshBondEnergy` writes (1.3) at `U ≡ 1` on the `n×n` face with the weight `w` left FREE and
    `η^{-1} = 1/etaOf n = n` explicit inside the difference;
  * `meshBondEnergy_closed : meshBondEnergy w n f = w · n² · gradEnergy2 n f` — the two factors of
    `n` ARE the `η^{-1}` squared, which is exactly what the struck bullet dropped;
  * `avg_weight_forced` / `meshAvg_preserves_constants_iff` force `w = η^m` on an `m`-dimensional
    face, i.e. `w = η^{d-1} = 1/n²` at `m = d−1 = 2` — the measure the struck bullet got RIGHT;
  * so `meshBondEnergy (1/n²) n f = gradEnergy2 n f`: `⟨B,ΔB⟩ = G_plain`, `c = 1`;
  * `substParen_at_forced_weight` states the consequence for `L^{-2}⟨B,(−Δ+Q'^*Q')B⟩` — first term
    `G/n²`, which is precisely the `L^{-2}·G_plain` this file's `cross_section_2127_operator_bound`
    proves;
  * `clause2_fails_at_weight_eta_d` is the must-fire control: at the rival weight `η^d` clause 2 is
    FALSE on the constant field, so the weight is not a free choice.

  **Scope, stated (S88).** All of the above is about CMP89's `Δ^{η,N}`. That CMP96 p.245's
  `Δ_{Λ'}^{L^{-1},N}` IS that operator at `η = L^{-1}` remains an INFERENCE, not a citation: CMP96
  never defines it (two-layer whole-paper search, all found loci image-verified), but p.229 says the
  Neumann conditions are "as in [3]" and p.250's reference list gives `[3]` = CMP89 — both
  image-verified. The `c = 1` value is therefore pinned as firmly as that identification, which is
  strictly better than "unpinned pending a page nobody has read", and is stated as an inference
  rather than banked as a fact.
* **c = 1** (the reading THIS file assumes): the operator's quadratic form is exactly `G_plain`, gap
  `π²/L²` w.r.t. the plain sum `Σ` — matching CMP96 p.242 (2.110)'s `γ₀' = π²/L²` and CMP89 p.580's
  Neumann operator `Δ^{η,N}` (identical notation). It is the **only** reading under which `(2.127)`
  is TRUE (`Var ≤ L²·G_plain`, `C_P ≤ L²/π² < L²`, mesh-uniform) — and Balaban USES `(2.127)` to
  prove his Lemma 2.4 — ~~but p.242 is a *different* operator (`Δ'_j = H'*Δ²H'`, not
  `Δ_{Λ'}^{L^{-1},N}`), so c = 1 is IMPORTED by analogy, not derived from the (2.127) page or the
  operator's definition.~~

  **AMENDED (S75, 2026-08-09): `c = 1` is now DERIVED from the operator's own defining page, not
  imported by analogy.** The p.242 corroboration stands and is no longer load-bearing; see the
  second bullet for the derivation from CMP89 (1.3) and the kernel declarations that carry it. The
  struck clause's caution about p.242 being a different operator was correct and is retained for
  exactly that reason — nothing here rests on it any more.

**~~Conclusion.~~ Conclusion — REWRITTEN (S75, 2026-08-09).** ~~`[RES-CMP96-2127-XSEC-POINCARE]` is
**not closed by this file**. It is REDUCED to a single precisely-named source question: *the
quadratic-form normalization of `Δ_{Λ'}^{L^{-1},N}` on its CMP96/CMP95 **defining page** (not yet
located/read by this campaign)*. If that page fixes c = 1, this file is the faithful closure;
otherwise `(2.127)` as printed is not literally true and the correct statement must be reconstructed
from the operator's true normalization.~~

**Both struck claims are now false.** The defining page HAS been located and read: it is CMP89
p.572, equation **(1.3)**, image-verified at 300 dpi. It fixes `c = 1` on a `(d−1)`-dimensional
cross-section at `d = 3` (second bullet). And the normalization is therefore no longer "unpinned":
the reading this file assumes is the one the operator's definition supplies. What survives as a
scoped limit is not a normalization question but an IDENTIFICATION question — that CMP96's
`Δ_{Λ'}^{L^{-1},N}` is CMP89's `Δ^{η,N}` at `η = L^{-1}` — stated as an inference with its evidence
(notation match on all three slots; CMP96 p.229's "as in [3]"; p.250's `[3]` = CMP89; no definition
anywhere in CMP96 by a two-layer whole-paper search with every found locus image-verified). That
inference is the ONLY thing between this file and an unconditional identification, and it is a
citation question, not an open mathematical one.

**And the alternative branch of the struck sentence turned out to be the true one anyway.**
`(2.127)` as printed is NOT literally true, and the correct statement HAS been reconstructed from
the operator's true normalization: `MeshSubstitution.clause2_true` is exactly
`cross_section_2127_operator_bound` after the CMP89 substitution, while
`MeshSubstitution.no_uniform_weight` proves no weight whatsoever reproduces the printed parenthesis
of `(2.126)`. Three distinct formulas were kept apart and separately decided
(`three_formulas_distinct_at_ten`, on `erratum_2127`'s own `L = 10` witness): the printed literal is
FALSE from `L = 10`; the CMP89-substituted form (this file's theorem) is TRUE for all `L ≥ 1`; the
erratum's exponent repair is TRUE by a different weakening. `printed_step_does_not_transfer` is the
headline: every field refuting the printed step still satisfies the substituted bound.

The scalar displays on p.245 are still mutually inconsistent — that was and remains the finding,
routed to statement-prosecution and not silently fixed. What has changed is that the inconsistency
is now localized and quantified (clause 1's gradient term, off by exactly one factor of `L`) rather
than being a fork between three candidate conventions for us to choose among.

## What is PROVED here (UNCONDITIONAL, kernel-checked, `#print axioms` sorry-free)

* `var1_le` — the 1-D variance form of `discrete_poincare_crude`: `Σ(g−ḡ)² ≤ (n(n−1)/2)·E_1D(g)`.
* `var2_le_crude` / `var2_le_nsq` — **the 2-D mesh-uniform Poincaré**: `var2 ≤ (n(n−1)/2)·gradEnergy2
  ≤ n²·gradEnergy2`, via ANOVA (row-mean decomposition + 1-D bound applied to rows and to the column
  of row-means + one Cauchy–Schwarz). Mesh-uniform: `n(n−1)/2 ≤ n²`, sharp up to a π² margin
  (`var2/(n²·gradEnergy2) → 1/π²` at the gap mode, `compute/neumann_poincare/verify_bound.py`). This
  is a genuine, unconditional result — a discrete-Poincaré brick with an explicit mesh-uniform
  constant, independent of the `(2.127)` normalization question above.
* `cross_section_2127_operator_bound` — the inequality `gradEnergy2/n² + (sum2/n²)²/n² ≥ sumSq2/n⁴`
  about the plain grid quantities. TRUE unconditionally; **equals `(2.127)` under c = 1, which the
  operator's defining page CMP89 (1.3) supplies** (⚠ block, second bullet — amended 2026-08-09;
  it previously read "only under c = 1", when c = 1 was assumed rather than derived).

## What is NOT closed (named, not faked)

* `[RES-CMP96-2127-XSEC-POINCARE]` — ~~reduced, not closed (the c = 1 normalization; see the ⚠
  block).~~ **AMENDED (S75, 2026-08-09): the NORMALIZATION half is closed — `c = 1` is derived from
  CMP89 (1.3), the operator's image-verified defining page. What remains is not a normalization
  question but the cross-paper IDENTIFICATION of CMP96's `Δ_{Λ'}^{L^{-1},N}` with CMP89's
  `Δ^{η,N}`, held as a stated inference with image-verified evidence. See the ⚠ block.**
* `BlockPoincareLemma24.Lemma24Conclusion` / `(2.128)` — additionally needs the slab-incidence
  combination of `(2.123)` and `(2.127)` with the boundary-correction terms, plus the geometric
  instantiation of this abstract bound onto each coarse bond's `Λ'`. The SEPARATE residual
  `[RES-CMP96-2128-SLABLOCAL]`; both live in `BlockPoincareLemma24.lean` (a different lane's file),
  not addressed here.

## L12 / S91 note
No `Nonempty`/`∃`-concluding declaration is introduced — every theorem is a plain `∀`-statement with
explicit constants, so no `S91_REGISTRY.tsv` row is triggered.
-/

namespace AdalyFormal.Balaban.DiscreteNeumannPoincare

open Finset
open AdalyFormal.Balaban.DiscretePoincare
open AdalyFormal.Balaban.CrossSectionPositivity

/-! ## §1. The 1-D variance form of the crude discrete Poincaré inequality. -/

/-- **1-D variance Poincaré (crude, mesh-uniform).** For arbitrary `g` on `n` points,
`Σ_i (g i − ḡ)² ≤ (n(n−1)/2)·E_1D(g)`, `ḡ = (Σg)/n`. Obtained from `discrete_poincare_crude` by the
constant shift `g ↦ g − ḡ` (which is mean-zero and has the same Dirichlet energy). -/
theorem var1_le (n : ℕ) (g : ℕ → ℝ) :
    ∑ i ∈ range n, (g i - (∑ k ∈ range n, g k) / (n : ℝ)) ^ 2
      ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * dirichletEnergy n g := by
  set gbar : ℝ := (∑ k ∈ range n, g k) / (n : ℝ) with hgbar
  set g' : ℕ → ℝ := fun i => g i - gbar with hg'
  have hmz : meanZero n g' := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [meanZero]
    · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [meanZero]
      have h1 : ∑ i ∈ range n, g' i = (∑ i ∈ range n, g i) - (n : ℝ) * gbar := by
        simp only [hg']
        rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
      rw [h1, hgbar]
      field_simp
      ring
  have hDE : dirichletEnergy n g' = dirichletEnergy n g := by
    simp only [dirichletEnergy, hg']
    apply Finset.sum_congr rfl
    intro i _; ring
  have hSS : sumSq n g' = ∑ i ∈ range n, (g i - gbar) ^ 2 := by
    simp only [sumSq, hg']
  have hb := discrete_poincare_crude n g' hmz
  rw [hSS, hDE] at hb
  exact hb

/-! ## §2. The 2-D cross-section: definitions. -/

/-- Total sum over the `n×n` cross-section. -/
def sum2 (n : ℕ) (f : ℕ → ℕ → ℝ) : ℝ := ∑ i ∈ range n, ∑ j ∈ range n, f i j

/-- Sum of squares over the `n×n` cross-section (`‖B‖²` of the operator statement). -/
def sumSq2 (n : ℕ) (f : ℕ → ℕ → ℝ) : ℝ := ∑ i ∈ range n, ∑ j ∈ range n, (f i j) ^ 2

/-- Horizontal (within-row) Dirichlet energy. -/
def horEnergy (n : ℕ) (f : ℕ → ℕ → ℝ) : ℝ := ∑ i ∈ range n, dirichletEnergy n (fun j => f i j)

/-- Vertical (within-column) Dirichlet energy. -/
def verEnergy (n : ℕ) (f : ℕ → ℕ → ℝ) : ℝ := ∑ j ∈ range n, dirichletEnergy n (fun i => f i j)

/-- **`G_plain`**, the plain nearest-neighbour bond-difference energy on the cross-section,
`= Σ_{b⊂Λ'}|∂B_μ(b)|²`, split into horizontal + vertical bonds. This IS `⟨B,Δ_{Λ'}^{L^{-1},N}B⟩`
in the source's normalization (`c=1`, gap `π²/L²`, p.242). -/
def gradEnergy2 (n : ℕ) (f : ℕ → ℕ → ℝ) : ℝ := horEnergy n f + verEnergy n f

/-- The cross-sectional variance `Σ_{x}(B(x) − mean)²`, mean over the `n² = |Λ'|` sites. -/
noncomputable def var2 (n : ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ range n, ∑ j ∈ range n, (f i j - sum2 n f / (n : ℝ) ^ 2) ^ 2

/-! ## §3. The 2-D mesh-uniform Poincaré via ANOVA. -/

/-- **THE 2-D MESH-UNIFORM DISCRETE POINCARÉ.** `var2 ≤ (n(n−1)/2)·gradEnergy2`, hence (see
`var2_le_nsq`) `≤ n²·gradEnergy2`. Proof: ANOVA row-mean decomposition
`var2 = Σ_i Σ_j (f−r_i)² + Σ_i n(r_i−m)²`; bound the within-row term by the 1-D `var1_le` per row
(→ `(n(n−1)/2)·horEnergy`) and the between-row term by `var1_le` on the row-means `r` plus one
Cauchy–Schwarz `(Σ_j a_j)² ≤ n Σ_j a_j²` (→ `(n(n−1)/2)·verEnergy`). -/
theorem var2_le_crude (n : ℕ) (f : ℕ → ℕ → ℝ) :
    var2 n f ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * gradEnergy2 n f := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [var2, gradEnergy2, horEnergy, verEnergy]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
  rw [var2]
  set m : ℝ := sum2 n f / (n : ℝ) ^ 2 with hm
  set r : ℕ → ℝ := fun i => (∑ j ∈ range n, f i j) / (n : ℝ) with hr
  -- ANOVA per-row decomposition
  have hper : ∀ i ∈ range n, ∑ j ∈ range n, (f i j - m) ^ 2
      = (∑ j ∈ range n, (f i j - r i) ^ 2) + (n : ℝ) * (r i - m) ^ 2 := by
    intro i _
    have hrow : ∑ j ∈ range n, (f i j - r i) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
      simp only [hr]
      field_simp
      ring
    calc ∑ j ∈ range n, (f i j - m) ^ 2
        = ∑ j ∈ range n,
            ((f i j - r i) ^ 2 + 2 * (r i - m) * (f i j - r i) + (r i - m) ^ 2) := by
          apply Finset.sum_congr rfl; intro j _; ring
      _ = (∑ j ∈ range n, (f i j - r i) ^ 2)
            + 2 * (r i - m) * (∑ j ∈ range n, (f i j - r i)) + (n : ℝ) * (r i - m) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, card_range, nsmul_eq_mul]
      _ = (∑ j ∈ range n, (f i j - r i) ^ 2) + (n : ℝ) * (r i - m) ^ 2 := by
          rw [hrow]; ring
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib]
  -- within-row term ≤ C·horEnergy
  have hA : (∑ i ∈ range n, ∑ j ∈ range n, (f i j - r i) ^ 2)
      ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * horEnergy n f := by
    rw [horEnergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h1 := var1_le n (fun j => f i j)
    simp only [hr]
    exact h1
  -- between-row term ≤ C·verEnergy
  have hB : (∑ i ∈ range n, (n : ℝ) * (r i - m) ^ 2)
      ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * verEnergy n f := by
    have hrsum : ∑ i ∈ range n, r i = sum2 n f / (n : ℝ) := by
      simp only [hr]
      rw [← Finset.sum_div, sum2]
    have hm_r : (∑ i ∈ range n, r i) / (n : ℝ) = m := by
      rw [hrsum, hm, pow_two, div_div]
    have hvar_r : ∑ i ∈ range n, (r i - m) ^ 2
        ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * dirichletEnergy n r := by
      have h2 := var1_le n r
      rw [hm_r] at h2
      exact h2
    have hDEr : dirichletEnergy n r ≤ verEnergy n f / (n : ℝ) := by
      have hpt : ∀ i ∈ range (n - 1), (r (i + 1) - r i) ^ 2
          ≤ (1 / (n : ℝ)) * ∑ j ∈ range n, (f (i + 1) j - f i j) ^ 2 := by
        intro i _
        have hdiff : r (i + 1) - r i
            = (∑ j ∈ range n, (f (i + 1) j - f i j)) / (n : ℝ) := by
          simp only [hr]
          rw [Finset.sum_sub_distrib, sub_div]
        rw [hdiff, div_pow]
        have hCS := sq_sum_le_card_mul_sum_sq (s := range n)
          (f := fun j => f (i + 1) j - f i j)
        rw [card_range] at hCS
        have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
        rw [div_le_iff₀ hn2]
        have hrw : (1 / (n : ℝ)) * (∑ j ∈ range n, (f (i + 1) j - f i j) ^ 2) * (n : ℝ) ^ 2
            = (n : ℝ) * (∑ j ∈ range n, (f (i + 1) j - f i j) ^ 2) := by
          field_simp
        rw [hrw]; exact hCS
      calc dirichletEnergy n r
          = ∑ i ∈ range (n - 1), (r (i + 1) - r i) ^ 2 := by rw [dirichletEnergy]
        _ ≤ ∑ i ∈ range (n - 1), (1 / (n : ℝ)) * ∑ j ∈ range n, (f (i + 1) j - f i j) ^ 2 :=
            Finset.sum_le_sum hpt
        _ = (1 / (n : ℝ)) * ∑ i ∈ range (n - 1), ∑ j ∈ range n, (f (i + 1) j - f i j) ^ 2 := by
            rw [Finset.mul_sum]
        _ = (1 / (n : ℝ)) * verEnergy n f := by
            rw [verEnergy]
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _; rw [dirichletEnergy]
        _ = verEnergy n f / (n : ℝ) := by ring
    -- assemble hB
    rw [← Finset.mul_sum]
    have hC_nonneg : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by nlinarith [h1n]
    have hstep1 : (n : ℝ) * ∑ i ∈ range n, (r i - m) ^ 2
        ≤ (n : ℝ) * (((n : ℝ) * ((n : ℝ) - 1) / 2) * dirichletEnergy n r) :=
      mul_le_mul_of_nonneg_left hvar_r (le_of_lt hnpos)
    have hstep2 : (n : ℝ) * (((n : ℝ) * ((n : ℝ) - 1) / 2) * dirichletEnergy n r)
        ≤ (n : ℝ) * (((n : ℝ) * ((n : ℝ) - 1) / 2) * (verEnergy n f / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDEr hC_nonneg) (le_of_lt hnpos)
    have hfinal : (n : ℝ) * (((n : ℝ) * ((n : ℝ) - 1) / 2) * (verEnergy n f / (n : ℝ)))
        = ((n : ℝ) * ((n : ℝ) - 1) / 2) * verEnergy n f := by
      field_simp
    linarith [hstep1, hstep2, hfinal.le, hfinal.ge]
  rw [gradEnergy2, mul_add]
  linarith [hA, hB]

/-- **The `n²` form**, directly matching `(2.127)`'s `Var ≤ L·G = L²·G_plain`. -/
theorem var2_le_nsq (n : ℕ) (f : ℕ → ℕ → ℝ) :
    var2 n f ≤ (n : ℝ) ^ 2 * gradEnergy2 n f := by
  have hb := var2_le_crude n f
  have hge : 0 ≤ gradEnergy2 n f := by
    apply add_nonneg <;>
      exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hcoef : (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  nlinarith [hb, hge, hcoef, mul_le_mul_of_nonneg_right hcoef hge]

/-! ## §4. Closing `(2.127)`'s operator positivity. -/

/-- **The `(2.126)→(2.127)` operator-form inequality about the plain grid quantities — UNCONDITIONAL,
and equal to CMP96 `(2.127)` under the normalization `c = 1`, which is now DERIVED (see module ⚠
block).** For every `n = L ≥ 1`, `gradEnergy2/n² + (sum2/n²)²/n² ≥ sumSq2/n⁴`. Obtained by feeding
the mesh-uniform 2-D Poincaré `var2 ≤ n²·gradEnergy2` (`= Var ≤ L·G`, `G := L·gradEnergy2`) through
`CrossSectionPositivity.cross_section_2127_iff_poincare`. This IS `L^{-2}⟨B,Δ_{Λ'}^{L^{-1},N}B⟩ +
L^{-2}|mean|² ≥ L^{-(d+1)}‖B‖²` at `d=3` **iff** `⟨B,Δ_{Λ'}^{L^{-1},N}B⟩ = gradEnergy2 = G_plain`
(c = 1).

~~The literal p.245 display and Balaban's CMP95 inner-product convention give c = L^{-1} and
c = L^{-2} respectively, under which `(2.127)` is FALSE; c = 1 is the only reading making it true but
is unpinned pending the operator's defining page. So this **REDUCES, does not close**,
`[RES-CMP96-2127-XSEC-POINCARE]` to that normalization question.~~

**⚠ SUPERSEDED (S75, 2026-08-09, `compute/mesh_substitution/`, installed by
`compute/norm_diamond_install/`) — both struck sentences are false.**

* `c = L^{-2}` was arithmetically WRONG: it applied the `(d−1)`-dimensional measure `η^{d-1}` but
  kept `∂` as the plain difference, whereas the operator's defining page CMP89 **(1.3)** (p.572,
  image-verified) uses the SCALED difference `D^η = η^{-1}∂`. The `η^{-2}` cancels the `η^{d-1}`
  exactly at `d = 3`, giving **`c = 1`** for every `L`. Kernel:
  `MeshSubstitution.meshBondEnergy_closed` (`= w·n²·G`, the `n²` being `η^{-1}` squared) at the
  weight `avg_weight_forced` forces (`w = η^{d-1} = 1/n²`).
* `c = L^{-1}` is not a rival convention but a term-match against a display no weight can satisfy:
  `MeshSubstitution.no_uniform_weight`.
* The defining page is no longer "pending" — it has been located, rendered and read.

What remains scoped is the cross-paper IDENTIFICATION of CMP96's `Δ_{Λ'}^{L^{-1},N}` with CMP89's
`Δ^{η,N}` at `η = L^{-1}`, an inference with image-verified evidence (CMP96 p.229 "as in [3]",
p.250 `[3]` = CMP89, no definition anywhere in CMP96). `MeshSubstitution.clause2_true` is this very
theorem, reached from the substituted parenthesis by `substParen_at_forced_weight`. Those
declarations are STAGED at
`compute/mesh_substitution/stage/AdalyFormal/Balaban/MeshSubstitution.lean` and are not yet a module
of this tree, so nothing in THIS file's proof depends on them. -/
theorem cross_section_2127_operator_bound (n : ℕ) (hn : 1 ≤ n) (f : ℕ → ℕ → ℝ) :
    gradEnergy2 n f / (n : ℝ) ^ 2 + (sum2 n f / (n : ℝ) ^ 2) ^ 2 / (n : ℝ) ^ 2
      ≥ sumSq2 n f / (n : ℝ) ^ 4 := by
  have hpos : 0 < n := hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
  set f' : ℕ × ℕ → ℝ := fun p => f p.1 p.2 with hf'
  set s : Finset (ℕ × ℕ) := (range n) ×ˢ (range n) with hs_def
  have hcardnat : s.card = n * n := by rw [hs_def, Finset.card_product, card_range]
  have hcard : (s.card : ℝ) = (n : ℝ) ^ 2 := by rw [hcardnat, Nat.cast_mul, ← pow_two]
  have hs : s.Nonempty :=
    ⟨(0, 0), by rw [hs_def, Finset.mem_product]; exact ⟨mem_range.mpr hpos, mem_range.mpr hpos⟩⟩
  have hsum : ∑ p ∈ s, f' p = sum2 n f := by
    rw [hs_def, Finset.sum_product]; rfl
  have hsumsq : ∑ p ∈ s, (f' p) ^ 2 = sumSq2 n f := by
    rw [hs_def, Finset.sum_product]; rfl
  have hvar : ∑ x ∈ s, (f' x - (∑ y ∈ s, f' y) / (s.card : ℝ)) ^ 2 = var2 n f := by
    rw [hsum, hcardnat, Nat.cast_mul, ← pow_two, hs_def, Finset.sum_product, var2]
  set G : ℝ := (n : ℝ) * gradEnergy2 n f with hG
  have hpoin : ∑ x ∈ s, (f' x - (∑ y ∈ s, f' y) / (s.card : ℝ)) ^ 2 ≤ (n : ℝ) * G := by
    rw [hvar, hG]
    have h := var2_le_nsq n f
    calc var2 n f ≤ (n : ℝ) ^ 2 * gradEnergy2 n f := h
      _ = (n : ℝ) * ((n : ℝ) * gradEnergy2 n f) := by ring
  have key := (cross_section_2127_iff_poincare s f' hs (n : ℝ) G hnR hcard).mpr hpoin
  rw [hsum, hsumsq, hG] at key
  have hcoef : (n : ℝ) * gradEnergy2 n f / (n : ℝ) ^ 3 = gradEnergy2 n f / (n : ℝ) ^ 2 := by
    have hn : (n : ℝ) ≠ 0 := ne_of_gt hnR
    field_simp
  rw [ge_iff_le] at key ⊢
  rw [hcoef] at key
  exact key

#print axioms var1_le
#print axioms var2_le_crude
#print axioms var2_le_nsq
#print axioms cross_section_2127_operator_bound

end AdalyFormal.Balaban.DiscreteNeumannPoincare
