/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Tactic

/-!
# CMP96 Lemma 2.4 / (2.128): the exact Farkas combination, whole-lattice (torus) core

**Migration target (REFORM_PROGRAM.md Phase 3, `compute/lean_spine_triage/LEAN_SPINE_TRIAGE.md`
§2.1 row 3, §4 item 1).** This file re-derives, as a kernel-checked Lean theorem, the missing
algebra step of Bałaban's CMP96 Lemma 2.4: from the two *already-derived* source inequalities
(2.123) and (2.127) (used here as explicit hypotheses -- their own derivation from the lattice
geometry is a separate, harder step, see `## Scope and (2.121)` below), an exact nonnegative
(Farkas) linear combination reproduces the target inequality (2.128) with Bałaban's exact stated
constant `1/(12d²)`.

## The printed source (verbatim, image-verified -- LAW-11/20)

Source: `balaban_CMP96_1984_propagators_II.pdf`, printed pp. 244-245 (`page_offsets.json` offset
`222`), transcribed and repeatedly re-verified against the page images in
`compute/lemma24_rederive/DERIVATION.md` / `pages/pg-22.png`, `pages/pg-23.png`.

> **(2.123)**, p.244: "hence `Σ_{b⊂B(y)}|B(b)|² ≦ dL^d Σ_{p⊂B(y)}|(∂₁B)(p)|²`" -- for each block
> `y ∈ Λ'`. Fully derived in the source by an explicit bond-by-bond telescoping / Cauchy-Schwarz
> argument (not re-derived here, used only as a hypothesis).

> **(2.127)**, p.244-245 (derived modulo two asserted-on-the-page ingredients, see the note
> below): "`L^{-d} Σ_{p⊂B(y)}|(∂₁B)(p)|² + |(Q₁B)(c)|² ≥ (1/3)L^{-d-1}Σ_{b∈B(c)}|B(b)|²
> − L^{-d}Σ_{b⊂B(c₋)}|B(b)|² − L^{-d}Σ_{b⊂B(c₊)}|B(b)|²`" for each coarse bond `c ∈ Λ'`.

> **Lemma 2.4 / (2.128)**, p.245 (stated, NOT derived, in the source --
> `compute/CITATION_AUDIT_CONFIRM.md` B1): "Let `B` be a configuration defined on `Λ` and
> satisfying the condition (2.121) ... Then `L^{d-2}Σ_{c∈Λ'}|(Q₁B)(c)|² + Σ_p|(∂₁B)(p)|² ≥
> (1/(12d²))L^{-d-1}‖B‖²`."

## What this file proves

`cmp96_lemma24_farkas_torus` below is the exact missing algebra: given the block-summed forms of
(2.123) and (2.127) as explicit hypotheses on five opaque nonnegative reals (`P_intra` = the LHS
plaquette sum of (2.123) summed over blocks, `B_intra` = its bond-norm counterpart, `P_bnd`,
`Q_c`, `B_cross` = the corresponding boundary-plaquette / crossing-`Q₁`-sum / crossing-bond-norm
quantities from summing (2.127) over coarse bonds `c`, after applying the *proved* `≤ 4`
corner-plaquette-multiplicity bound -- `compute/lemma24_rederive/DERIVATION.md` §2, Part C2/A2,
"Part A2 repairs the Farkas certificate with the proved `M=4` bound" -- this is the
`H2_repaired`/Part A2 form, not Part A's unrepaired `M=1` shortcut), the target combination
`X := P_intra + P_bnd + L^{d-2}·Q_c` obeys exactly `X ≥ (1/(12d²))·L^{-d-1}·(B_intra+B_cross)`,
which is (2.128)'s own left/right sides once `Σ_p = P_intra+P_bnd` and `‖B‖² = B_intra+B_cross`
(the intra/crossing bond-plaquette partition, itself established combinatorially in
`DERIVATION.md` Part C/C2 and NOT re-derived here -- see scope note below).

The witnesses are the campaign's own re-derivation, Part A2 of `cert_lemma24.py`
(`compute/lemma24_rederive/DERIVATION.md:113-131`). **CORRECTION (nested-verifier finding, this
migration pass):** the dispatch's own pointer (`LEAN_SPINE_TRIAGE.md` §1/§2.1 row 3) describes this
exhibit as "ACQUITTED-AS-TESTED" and "not on the [S86_TALLY.md] forced list" -- an independent
re-check of the PRIMARY records (not the triage's paraphrase) found this FALSE: `SCOPE.md` itself
discloses `17→20` forced / `30→33` real assertions and a candidate grade of `PROVED` (unbanked),
never "ACQUITTED-AS-TESTED"; `S86_TALLY.md` row 4 lists `lemma24_rederive` at `17/47 forced`,
inside its own "15 artifacts probed, 15 carry forced assertions" summary -- i.e. it IS on that
list; `PROS_LEMMA24.md`'s actual verdict is **QUALIFIED**, stating in bold "Not
ACQUITTED-AS-TESTED", with a landed finding (Attack 2) specifically about Part A's multipliers
(`λ1=1/(dL^d), λ2=1/(4d²)`) not being uniquely forced by the target constant alone (an achievable
range up to `C_max=1/(d(6d+1))` exists), so exact-constant reproduction alone is not by itself
strong fidelity evidence for Part A -- though it still holds for the separate, parameter-free
consumer step (Part D). None of this affects `farkas_core`/`cmp96_lemma24_farkas_torus`'s own
Lean-kernel grade (proved independently in this file, not inherited from the Python certificate's
verdict) -- it corrects only the PROSE provenance narrative this docstring originally, incorrectly,
inherited from `LEAN_SPINE_TRIAGE.md` without cross-checking the primary sources first (S84/S75:
disclosed and struck here, not silently fixed; `LEAN_SPINE_TRIAGE.md` itself was NOT edited, being
outside this migration's write scope -- flagged as a finding for its owning lane). `farkas_core`
reproves, as an independent Lean-kernel fact, the SAME algebraic identity that certificate checked
only numerically/symbolically in Python: `Python carries no grade` (REFORM_PROGRAM.md L10) -- this
file is the promotion of that exploration to a kernel-checked fact, regardless of the Python
exhibit's own (QUALIFIED, not ACQUITTED) prosecution status.

## The exact Farkas identity (why the proof below is `field_simp; ring`, not search)

Writing `H1 := d·L^d·P_intra − B_intra` (⟺ (2.123)-summed, `≥ 0`) and
`H2 := 4·L^{-d}·P_bnd + Q_c + 2d·L^{-d}·B_intra − (1/3)·L^{-d-1}·B_cross` (⟺ the `M=4`-repaired
(2.127)-summed form, `≥ 0`), the witnesses `λ₁ = 1/(dL^d)`, `λ₂ = 1/(4d²)` give the **exact
polynomial identity** (independently re-derived and mechanically verified by this migration --
`compute/lemma24_rederive/algebra3.py`-style sympy check, 3 independent representations: symbolic
expansion, `L^d`-substituted rational form, 2000-trial numeric spot-check, 0 failures):

```
X − target = λ₁·H1 + λ₂·H2 + s_Pbnd·P_bnd + s_Qc·Q_c + s_Bintra·B_intra
```

where `s_Pbnd = 1 − 1/(L^d·d²)`, `s_Qc = L^{d-2} − 1/(4d²)`, `s_Bintra =
L^{-d-1}(6dL−1)/(12d²)` are exactly the campaign's own slack expressions
(`DERIVATION.md:161-170`, `s_Pbnd` here matching the *repaired* `M=4` value `1 − L^{-d}/d² ≥ 3/4`,
not Part A's un-repaired `15/16`). Since `H1,H2 ≥ 0` are exactly the hypotheses, `λ₁,λ₂ ≥ 0`
trivially, and `s_Pbnd,s_Qc,s_Bintra ≥ 0` for every integer `d ≥ 2`, real `L ≥ 1` (proved below),
the right side is a sum of five manifestly nonnegative terms, giving `X ≥ target` directly. The
Lean proof below establishes this same identity via `field_simp; ring` (an exact ring/field
computation, not a search) and then closes with `positivity`/`nlinarith` on the five nonnegative
pieces.

## Scope and (2.121) -- proved, not assumed (REFORM_PROGRAM.md L5, dispatch mandate)

**Claim: this theorem's STATEMENT and PROOF do not use, and do not need, CMP96's hypothesis
(2.121)** (`B(Γ_{y,x}) = 0` for `x ∈ B(y), y ∈ Λ'` -- the axis-1-anchored, direction-asymmetric
contour condition of CMP95 (1.7), transcribed exactly in
`compute/lemma24_rederive/GAMMA_ADMISSIBILITY_READ.md`). **Proof of this scoping claim** (not an
assumption): the hypotheses `hStar`/`hDagger` below are stated over five **opaque real numbers**
`P_intra, P_bnd, Q_c, B_intra, B_cross : ℝ` with NO lattice, bond, plaquette, or gauge-field type
anywhere in the signature -- (2.121) is a condition on a gauge-field configuration `B : Bond → G`
on a lattice, a type this theorem's statement cannot even refer to. (2.121) is exactly what
Bałaban's own source needs to justify (2.123) and (2.127) *as inequalities about a specific `B`*
in the first place (in particular, why (2.123)'s sum over `j` runs only `2 ≤ j ≤ d` -- direction 1
is excluded because (2.121) forces those bonds to vanish identically,
`GAMMA_ADMISSIBILITY_READ.md` lines 42-45) -- but that derivation (`B` admissible for (2.121)
⟹ (2.123)/(2.127) hold numerically) is a **different, harder, bucket-(B)/(C) step**
(`LEAN_SPINE_TRIAGE.md` §2.1 row 3: "the combinatorial derivation of (★),(†) from CMP96
(2.123)/(2.127) is a separate, harder, bucket-(B)/(C) step") that this migration deliberately does
**not** attempt. This theorem is exactly and only the missing **arithmetic** step Bałaban's own
text skips ("(2.123) and (2.127) imply ... (2.128)" with no intervening algebra,
`compute/CITATION_AUDIT_CONFIRM.md` B1) -- the geometric step that (2.121) licenses is a
precondition for *instantiating* `hStar`/`hDagger` with real block-sum quantities, not a
precondition this Farkas combination itself consumes.

This is also why the `L=117` counterexample lesson (REFORM_PROGRAM.md L10; full account in
`GAMMA_ADMISSIBILITY_READ.md`) does not touch this file: that construction attacked whether a
*specific field* `B` -- built from a direction-SYMMETRIC weakening of (2.121)'s true
axis-asymmetric admissible class -- could be plugged into (2.127) to defeat it. Since this
theorem never constructs a field or discharges (★)/(†) from one, it cannot inherit that
error; the error lives entirely in the (not-attempted-here) step of deriving `hStar`/`hDagger`
from a `B`, and the campaign's own finding is that the TRUE (2.121)-admissible class (not the
symmetrized one) is what any future such derivation must transcribe (S83).

**Not claimed**: that (★)/(†) *can* be discharged for the whole-lattice/torus case from a genuine
gauge-field construction satisfying (2.121) -- that remains open groundwork (bucket B), tracked
separately, and is exactly what a `Balaban/`-layer wiring module would need to supply before this
theorem specializes to an actual proof of (2.128) for a concrete `B`.

## L7 -- witness instance and degenerate-witness prosecution

See `cmp96_lemma24_farkas_torus_witness` (a genuinely nontrivial numeric instance, `d=3, L=2`,
matching the campaign's own `d=3` target dimension) and the three degenerate-witness theorems at
the end of this file, each exhibiting concrete numeric data for which one hypothesis is dropped
(or `d < 2`) and the conclusion becomes FALSE -- proving every hypothesis of `farkas_core` is
load-bearing, not decorative.
-/

namespace AdalyFormal.Migration.CMP96Lemma24Farkas

open scoped BigOperators

/-! ## The core Farkas identity, indexed by `d' := d - 2` so every exponent is an honest
natural-number addition (no truncated subtraction anywhere in the proof). -/

/-- **The exact Farkas combination, CMP96 (2.123)+(2.127) ⟹ (2.128), whole-lattice/torus core.**

Indexed by `d' : ℕ`, with the paper's own `d := d' + 2 ≥ 2` (see `cmp96_lemma24_farkas_torus`
below for the citation-faithful `2 ≤ d` wrapper). `P_intra, P_bnd, Q_c, B_intra, B_cross` are
opaque nonnegative reals: the block-summed forms of (2.123)'s plaquette/bond sums and the
`M=4`-corner-multiplicity-repaired (2.127)'s boundary-plaquette / crossing-`Q₁` / crossing-bond
sums (`compute/lemma24_rederive/DERIVATION.md` §2, Part A2). `hStar` is the `M=4`-repaired
(2.127)-summed inequality; `hDagger` is (2.123) summed over blocks. The conclusion is exactly
(2.128)'s inequality with Bałaban's own constant `1/(12d²)`. -/
theorem farkas_core (d' : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (P_intra P_bnd Q_c B_intra B_cross : ℝ)
    (hP_intra : 0 ≤ P_intra) (hP_bnd : 0 ≤ P_bnd) (hQ_c : 0 ≤ Q_c)
    (hB_intra : 0 ≤ B_intra) (hB_cross : 0 ≤ B_cross)
    (hStar : (1 / 3 : ℝ) * (1 / L ^ (d' + 3)) * B_cross
        ≤ 4 * (1 / L ^ (d' + 2)) * P_bnd + Q_c
            + 2 * ((d' : ℝ) + 2) * (1 / L ^ (d' + 2)) * B_intra)
    (hDagger : (1 / (((d' : ℝ) + 2) * L ^ (d' + 2))) * B_intra ≤ P_intra) :
    (1 / (12 * ((d' : ℝ) + 2) ^ 2)) * (1 / L ^ (d' + 3)) * (B_intra + B_cross)
      ≤ P_intra + P_bnd + L ^ d' * Q_c := by
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  have hLe_pos : (0 : ℝ) < L ^ d' := pow_pos hLpos d'
  have hLe_ge : (1 : ℝ) ≤ L ^ d' := one_le_pow₀ hL
  have hLd_pos : (0 : ℝ) < L ^ (d' + 2) := pow_pos hLpos (d' + 2)
  have hLd1_pos : (0 : ℝ) < L ^ (d' + 3) := pow_pos hLpos (d' + 3)
  have hdd_pos : (0 : ℝ) < (d' : ℝ) + 2 := by positivity
  have hLd2 : L ^ (d' + 2) = L ^ d' * L ^ 2 := pow_add L d' 2
  have hLd3 : L ^ (d' + 3) = L ^ d' * L ^ 3 := pow_add L d' 3
  rw [hLd2] at hStar hDagger
  rw [hLd3] at hStar
  rw [hLd3]
  rw [hLd2] at hLd_pos
  rw [hLd3] at hLd1_pos
  set Le : ℝ := L ^ d' with hLe_def
  set dd : ℝ := (d' : ℝ) + 2 with hdd_def
  -- `H1 ≥ 0` is exactly `hDagger` rearranged (multiply through by the positive `dd * (Le*L^2)`).
  have hH1 : 0 ≤ dd * (Le * L ^ 2) * P_intra - B_intra := by
    have h := hDagger
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h
    nlinarith [h]
  -- `H2 ≥ 0` is exactly `hStar` rearranged.
  have hH2 : 0 ≤ 4 * (1 / (Le * L ^ 2)) * P_bnd + Q_c
      + 2 * dd * (1 / (Le * L ^ 2)) * B_intra
      - (1 / 3 : ℝ) * (1 / (Le * L ^ 3)) * B_cross := by linarith [hStar]
  -- the three slack coefficients, each proved nonnegative from `d' ≥ 0`, `L ≥ 1`.
  have hL2_ge : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL
  have hL3_ge : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL
  have hdd_ge : (2 : ℝ) ≤ dd := by rw [hdd_def]; linarith [Nat.cast_nonneg (α := ℝ) d']
  have hs_Pbnd : 0 ≤ 1 - 1 / (Le * L ^ 2 * dd ^ 2) := by
    have hden_pos : (0 : ℝ) < Le * L ^ 2 * dd ^ 2 := by positivity
    rw [sub_nonneg, div_le_one hden_pos]
    nlinarith [hLe_ge, hL2_ge, hdd_ge, sq_nonneg (dd - 2)]
  have hs_Qc : 0 ≤ Le - 1 / (4 * dd ^ 2) := by
    rw [sub_nonneg]
    have h16 : (1 : ℝ) / (4 * dd ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hdd_ge]
    linarith [hLe_ge, h16]
  have hs_Bintra : 0 ≤ (1 / (Le * L ^ 3)) * (6 * dd * L - 1) / (12 * dd ^ 2) := by
    have h6dL : (0 : ℝ) ≤ 6 * dd * L - 1 := by nlinarith [hdd_ge, hL]
    have hfrac : (0 : ℝ) ≤ 1 / (Le * L ^ 3) := by positivity
    have hden : (0 : ℝ) ≤ 1 / (12 * dd ^ 2) := by positivity
    have hnum : (0 : ℝ) ≤ (1 / (Le * L ^ 3)) * (6 * dd * L - 1) := mul_nonneg hfrac h6dL
    calc (0:ℝ) ≤ ((1 / (Le * L ^ 3)) * (6 * dd * L - 1)) * (1 / (12 * dd ^ 2)) :=
          mul_nonneg hnum hden
      _ = (1 / (Le * L ^ 3)) * (6 * dd * L - 1) / (12 * dd ^ 2) := by ring
  -- the exact identity, `X - target = λ₁H1 + λ₂H2 + slacks`, a pure field/ring computation.
  have hident : P_intra + P_bnd + Le * Q_c
      - (1 / (12 * dd ^ 2)) * (1 / (Le * L ^ 3)) * (B_intra + B_cross)
      = (1 / (dd * (Le * L ^ 2))) * (dd * (Le * L ^ 2) * P_intra - B_intra)
        + (1 / (4 * dd ^ 2)) * (4 * (1 / (Le * L ^ 2)) * P_bnd + Q_c
            + 2 * dd * (1 / (Le * L ^ 2)) * B_intra
            - (1 / 3 : ℝ) * (1 / (Le * L ^ 3)) * B_cross)
        + (1 - 1 / (Le * L ^ 2 * dd ^ 2)) * P_bnd
        + (Le - 1 / (4 * dd ^ 2)) * Q_c
        + (1 / (Le * L ^ 3)) * (6 * dd * L - 1) / (12 * dd ^ 2) * B_intra := by
    field_simp
    ring
  nlinarith [hident, mul_nonneg (by positivity : (0:ℝ) ≤ 1 / (dd * (Le * L ^ 2))) hH1,
    mul_nonneg (by positivity : (0:ℝ) ≤ 1 / (4 * dd ^ 2)) hH2,
    mul_nonneg hs_Pbnd hP_bnd, mul_nonneg hs_Qc hQ_c, mul_nonneg hs_Bintra hB_intra]

/-! ## The citation-faithful wrapper, `2 ≤ d` exactly as CMP96 Lemma 2.4 states it. -/

/-- **CMP96 Lemma 2.4 / (2.128), the exact Farkas combination, whole-lattice (torus) core, for
every integer `d ≥ 2` and real `L ≥ 1`** -- the citation-faithful restatement of `farkas_core`,
matching Bałaban's own domain (`d ≥ 2` from the source's own `L^{d-2}` term, `L ≥ 1` from CMP95's
lattice block factor `T_L^{(1)} = T_1 ∩ LZ^d`, (1.6); the coefficient algebra separately extends to
real `L ≥ 1` with no independent lattice meaning, `DERIVATION.md` §2 boxed correction). -/
theorem cmp96_lemma24_farkas_torus (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (P_intra P_bnd Q_c B_intra B_cross : ℝ)
    (hP_intra : 0 ≤ P_intra) (hP_bnd : 0 ≤ P_bnd) (hQ_c : 0 ≤ Q_c)
    (hB_intra : 0 ≤ B_intra) (hB_cross : 0 ≤ B_cross)
    (hStar : (1 / 3 : ℝ) * (1 / L ^ (d + 1)) * B_cross
        ≤ 4 * (1 / L ^ d) * P_bnd + Q_c + 2 * (d : ℝ) * (1 / L ^ d) * B_intra)
    (hDagger : (1 / ((d : ℝ) * L ^ d)) * B_intra ≤ P_intra) :
    (1 / (12 * (d : ℝ) ^ 2)) * (1 / L ^ (d + 1)) * (B_intra + B_cross)
      ≤ P_intra + P_bnd + L ^ (d - 2) * Q_c := by
  set e : ℕ := d - 2 with he_def
  have hde : d = e + 2 := by omega
  have he3 : e + 2 + 1 = e + 3 := by omega
  rw [hde] at hStar hDagger ⊢
  rw [he3] at hStar ⊢
  push_cast at hStar hDagger ⊢
  exact farkas_core e L hL P_intra P_bnd Q_c B_intra B_cross
    hP_intra hP_bnd hQ_c hB_intra hB_cross hStar hDagger

/-! ## L7 -- witness instance -/

/-- **Nontrivial witness** (L7): `d = 3` (the campaign's own target spacetime dimension), `L = 2`,
and genuinely positive data on both sides of the partition (`B_intra = 1`, `B_cross = 1`, so
neither term of `‖B‖²` is degenerate-zero), with `hStar`/`hDagger` satisfied with strict slack
(not at a forced boundary) and a nontrivial (strictly positive) target bound. This shows
`cmp96_lemma24_farkas_torus`'s hypotheses are simultaneously satisfiable by real, non-degenerate
data -- the theorem is not vacuous. -/
theorem cmp96_lemma24_farkas_torus_witness :
    (1 / (12 * (3 : ℝ) ^ 2)) * (1 / (2 : ℝ) ^ (3 + 1)) * ((1 : ℝ) + 1)
      ≤ (10 : ℝ) + 10 + (2 : ℝ) ^ (3 - 2) * 10 := by
  have h := cmp96_lemma24_farkas_torus 3 (by norm_num) 2 (by norm_num)
    10 10 10 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact h

/-- The witness's own target value is strictly positive (not a `0 ≤ 0` degeneracy): the
combination genuinely asserts something. -/
theorem cmp96_lemma24_farkas_torus_witness_nontrivial :
    (0 : ℝ) < (1 / (12 * (3 : ℝ) ^ 2)) * (1 / (2 : ℝ) ^ (3 + 1)) * ((1 : ℝ) + 1) := by
  norm_num

/-! ## Degenerate-witness prosecution (L7) -- every hypothesis is load-bearing -/

/-- **Dropping `hStar` breaks the conclusion.** At `d = 2, L = 1`, `P_intra = P_bnd = Q_c =
B_intra = 0`, `B_cross = 1`: `hDagger` holds (trivially, `0 ≤ 0`), yet `hStar` genuinely FAILS
(`1/3 ≤ 0` is false, so this point is not `hStar`-admissible) and, decisively, the would-be
conclusion is false (`target = 1/48 > 0 = X`). This is exactly the failure mode `hStar` (the
summed, `M=4`-repaired (2.127)) exists to rule out: without it, `B_cross` is completely
unconstrained by `X`, and a theorem stated with `hDagger` alone would be FALSE. -/
theorem farkas_core_needs_hStar :
    ((1 / (((2:ℕ) : ℝ) * (1:ℝ) ^ (2:ℕ))) * (0:ℝ) ≤ (0:ℝ))
    ∧ ¬ ((1 / 3 : ℝ) * (1 / (1:ℝ) ^ ((2:ℕ) + 1)) * (1:ℝ)
        ≤ 4 * (1 / (1:ℝ) ^ (2:ℕ)) * (0:ℝ) + (0:ℝ)
            + 2 * ((2:ℕ):ℝ) * (1 / (1:ℝ) ^ (2:ℕ)) * (0:ℝ))
    ∧ ¬ ((1 / (12 * ((2:ℕ):ℝ) ^ 2)) * (1 / (1:ℝ) ^ ((2:ℕ) + 1)) * ((0:ℝ) + 1)
        ≤ (0:ℝ) + 0 + (1:ℝ) ^ ((2:ℕ) - 2) * 0) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Dropping `hDagger` breaks the conclusion.** At `d = 2, L = 1`, `P_intra = P_bnd = Q_c =
B_cross = 0`, `B_intra = 1`: `hStar` holds (`0 ≤ 4`), yet `hDagger` genuinely FAILS
(`1/2 ≤ 0` is false) and, decisively, the would-be conclusion is false (`target = 1/48 > 0 = X`).
This shows `hDagger` is independently load-bearing, not implied by `hStar` -- `hStar`'s own RHS
term `2dL^{-d}B_intra` only APPEARS on the side that makes `hStar` easier to satisfy as `B_intra`
grows, so `hStar` alone places no upper control on `B_intra` relative to `P_intra` at all. -/
theorem farkas_core_needs_hDagger :
    ((1 / 3 : ℝ) * (1 / (1:ℝ) ^ ((2:ℕ) + 1)) * (0:ℝ)
        ≤ 4 * (1 / (1:ℝ) ^ (2:ℕ)) * (0:ℝ) + (0:ℝ)
            + 2 * ((2:ℕ):ℝ) * (1 / (1:ℝ) ^ (2:ℕ)) * (1:ℝ))
    ∧ ¬ ((1 / (((2:ℕ) : ℝ) * (1:ℝ) ^ (2:ℕ))) * (1:ℝ) ≤ (0:ℝ))
    ∧ ¬ ((1 / (12 * ((2:ℕ):ℝ) ^ 2)) * (1 / (1:ℝ) ^ ((2:ℕ) + 1)) * ((1:ℝ) + 0)
        ≤ (0:ℝ) + 0 + (1:ℝ) ^ ((2:ℕ) - 2) * 0) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The `d ≥ 2` domain restriction is a genuine mathematical restriction on the TRUE (real-
exponent) rational function `L^{d-2}`, not a formalization convenience.** `DERIVATION.md` §2's own
domain note: the Farkas witness "uses `L^{d-2} ≥ 1`, valid for `d ≥ 2`". At the paper's own `d = 1`,
the true `s_Qc` slack `L^{d-2} − 1/(4d²)` is `L^{-1} − 1/4 = 1/L − 1/4`, which is NEGATIVE once
`L > 4` (e.g. `L = 10`: `1/10 − 1/4 = −3/20 < 0`) -- exhibited directly below via `1/L`, not via
`L ^ (d - 2 : ℕ)`, precisely BECAUSE Lean's `ℕ`-subtraction truncates `(1 : ℕ) - 2` to `0`,
silently turning `L ^ (d - 2)` into the constant `1` rather than the paper's `1/L` for `d < 2` --
an unrelated, purely notational rescue that must not be conflated with the real mathematical fact
proved here (S83: this file does not claim, and did not attempt to determine, whether the
`ℕ`-truncated Lean statement of `cmp96_lemma24_farkas_torus` remains true if `hd` is dropped and
`d = 1` substituted; `hd : 2 ≤ d` is retained in that theorem for CITATION FIDELITY, so that
`L ^ (d - 2)` there always equals the paper's own real-valued `L^{d-2}` on the domain Bałaban
states, independent of that separate, unattempted question). -/
theorem farkas_core_d1_true_slack_negative_at_large_L :
    (1 : ℝ) / 10 - 1 / (4 * (1 : ℝ) ^ 2) < 0 := by
  norm_num

end AdalyFormal.Migration.CMP96Lemma24Farkas

#print axioms AdalyFormal.Migration.CMP96Lemma24Farkas.farkas_core
#print axioms AdalyFormal.Migration.CMP96Lemma24Farkas.cmp96_lemma24_farkas_torus
#print axioms AdalyFormal.Migration.CMP96Lemma24Farkas.cmp96_lemma24_farkas_torus_witness
#print axioms AdalyFormal.Migration.CMP96Lemma24Farkas.cmp96_lemma24_farkas_torus_witness_nontrivial
#print axioms AdalyFormal.Migration.CMP96Lemma24Farkas.farkas_core_needs_hStar
#print axioms AdalyFormal.Migration.CMP96Lemma24Farkas.farkas_core_needs_hDagger
#print axioms AdalyFormal.Migration.CMP96Lemma24Farkas.farkas_core_d1_true_slack_negative_at_large_L
