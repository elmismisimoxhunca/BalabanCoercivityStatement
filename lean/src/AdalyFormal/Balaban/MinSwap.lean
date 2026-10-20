/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import AdalyFormal.Balaban.RegularUGamma0
import AdalyFormal.Balaban.U1LeadingCoercivity
import AdalyFormal.Balaban.RegularUCoercivityFull
import AdalyFormal.Balaban.NilLevelTarget
import AdalyFormal.Balaban.TransverseClass

set_option autoImplicit false

/-!
# `MinSwap.lean` — the MIN-SWAP: a Schur-complement lower bound is a total-space inequality

**Source of the statement.** `compute/crazy_transverse/SEEDS.md` SEED 1 (generator lane,
`CONJECTURED / generator-seed`). This module turns the seed's central claim into a theorem, states
exactly which hypothesis each direction consumes, and proves each of those hypotheses NECESSARY by
counterexample.

## §1 — the abstract equivalence (no lattice, no gauge field, no inner product)

For a function `q : E → ℝ` ("the fine energy"), a set `S ⊆ E` ("the slice"), a map `Q : E → F`
("the level map"), a "squared unit norm" `n : F → ℝ` and a class `𝒜 ⊆ F` of unit-level data, set

  `schur q S Q B := sInf { q A | A ∈ S, Q A = B }`.

Then, for every fixed `γ`:

  `(∀ B ∈ 𝒜, γ * n B ≤ schur q S Q B)  ↔  (∀ A ∈ S, Q A ∈ 𝒜 → γ * n (Q A) ≤ q A)`

**provided** (a) `∀ B ∈ 𝒜`, the fibre over `B` is NONEMPTY (`Q(S) ⊇ 𝒜`), and (b) `q ≥ 0` on `S`.
`minSwap_iff` is that theorem. It is not analysis: the entire content is `csInf` bookkeeping
(`le_csInf` needs (a), `csInf_le` needs (b) through `BddBelow`). Every parameter — `γ`, `𝒜`, `Q`,
`n`, `q`, `S` — is UNIVERSALLY quantified; there is no existential and hence no free datum a prover
could choose to make the statement cheap.

**Hypothesis necessity, both directions, PROVED (not asserted):**

* `minSwap_mpr_needs_nonempty` — drop (a) and the `←` direction is FALSE. In Lean (and in ℝ)
  `sInf ∅ = 0`, so an empty fibre makes `schur B = 0` while the total-space side is VACUOUSLY true
  over that fibre. This is the seed's own flagged hazard, discharged as a theorem.
* `minSwap_mp_needs_bddBelow` — drop (b) and the `→` direction is FALSE: `sInf` of a set unbounded
  below is `0` by convention, which makes the Schur side true for junk reasons.

## §2 — why a fibre element with positive fine energy cannot refute the min-swap form

`fibre_datum_satisfies_total` : if `A ∈ S` and `Q A = 0` and `n 0 = 0` and `0 ≤ q A`, then
`γ * n (Q A) ≤ q A` for EVERY `γ`. So an element of the slice whose UNIT SHADOW VANISHES tests only
`0 ≤ q A`. In the one-space encodings this datum was fatal (`NilLevelTarget.targetAt_refuted` uses
`bondEnergy Btil > 0` on the right); in the min-swap form it is inert. The mechanism is the level
separation, nothing else.

`schur_eq_zero_of_zero_mem` records the companion fact: `schur q S Q 0 = 0` whenever `0 ∈ S`,
`Q 0 = 0`, `q 0 = 0` and `q ≥ 0` on `S` — so the min-swap statement at `B = 0` says exactly
`γ * n 0 ≤ 0`, i.e. nothing when `n 0 = 0`. The fibre over `0` is not a test space.

## §3 — the shape the seed asked for (inner-product / linear / submodule specialization)

`minSwap_iff_inner` is `minSwap_iff` with `E` a real inner product space, `S` a submodule, `Q` a
continuous linear map, `n B = ‖B‖ ^ 2` and `q` any nonnegative function. Nothing is gained
mathematically; it exists so consumers can apply the brick without re-deriving the specialization,
and it records that the abstract form really does cover the seed's stated setting.

## §4–§10 — the lattice half, in one line each

* **§4** `minSwap_transfer` — the tree's `Δ_k` is NOT an `sInf`, it is `‖D_U(H A₀)‖²`, so the
  surjectivity step never arises: `Q_ell H = Q_ell` plus slice-preservation carry the transfer.
  The real requirement is `H`-INVARIANCE of the class, and clauses on the UNIT image are
  `H`-invariant for free (`unitClause_hjExtension_invariant`).
* **§5** `loopField_unit_shadow_eq_zero` — the datum that refutes every one-space encoding has unit
  shadow `0`, so it tests only `0 ≤ ‖D_U(loop)‖²`. Checked, not assumed.
* **§6** `minSwap_total_on_bare_slice_refuted` / `minSwap_schur_on_bare_slice_refuted` — the
  min-swap on the BARE gauge slice is FALSE at `U = 1`: a nonzero constant bond field is div-free,
  curl-free, and `Q_ell(constant c) = c`.
* **§7** the quantifier domain is inhabited with strictly positive left-hand side.
* **§8** `total_forces_curlFree_unit_shadow_zero` — §6 in `U`-GENERAL form: the min-swap forces
  `Q_ell` to annihilate the covariant-curl-free part of the slice, so the admissible class must
  exclude those unit shadows. The seed's mechanism (ii) (`Q₁B = 0`) is FORCED, not optional.
* **§9** `MinSwapTotalTarget` / `MinSwapSchurTarget` / `MinSwapTotalTarget.toSchur`, and
  `MinSwapSchurTarget_univ_false` (the Schur target is FALSE at `𝒜 = univ`, so `toSchur` is not
  vacuous). **The DENOTATION docstring on `MinSwapSchurTarget` was CORRECTED 2026-07-29** — it claimed
  identity with CMP99b (3.156) and the tree's own adjudicated `MISMATCH` row contradicts that; the
  qualified statement, with locators, is on the declaration.
* **§9a** the raw §9 targets are VACUOUSLY INHABITED **six ways**, now as theorems in this module
  (`𝒜 = ∅`; `γ ≤ 0`; `𝒜 = {0}` for EVERY `γ`; any class missing `Q_ell(slice)`; `ell = 0` with a
  nonempty positive-weight class; each transported to the Schur side). Hence the GUARDED targets
  `MinSwapTotalTargetNV` / `MinSwapSchurTargetNV`, whose guard is a WITNESS in the domain with
  positive coarse energy — `0 < γ ∧ 𝒜.Nonempty` is NOT sufficient and §9a proves it is not. The
  eight `not_…` theorems of §9a.3 are the regression, one per vacuity.
* **§10** a second domain datum with nonzero unit shadow at `ell = 1` that is not a harmonic zero
  mode.
* **§10a** the guard is SATISFIABLE: `MinSwapTotalTargetNV` HOLDS at the explicit sharp constant
  `sharpGammaLoopEllOne m > 0` on an explicit nonempty class with strictly positive left-hand side,
  FAILS above that constant, and its class survives §8's forced exclusion. At `ell = 1` only — the
  degeneracy is disclosed there, and the general-`ell` version cannot live in this file (import
  cycle with `MinSwapWitness.lean`).

## Relation to `Balaban/TransverseClass.lean` (written CONCURRENTLY — overlap DISCLOSED, not papered)

`TransverseClass.lean` was under active edit by another lane while this module was written, and it
reaches the same conclusion as §5 from the other side: its `coarseUnitEnergy_eq_zero_of_mem_fibre`
and `loopField_coarseUnitEnergy_zero` say that every fibre element, and `loopField` in particular,
has zero corrected (unit-level) left-hand side. **§5 of this module is therefore SUBSTANTIVELY
DUPLICATED work** — same fact, different carrier (`covCoarseBondInner` + the reused
`RegularUCoercivityFull.covCoarseBondInner_self_eq_sum`, rather than a fresh `coarseUnitEnergy`
definition). Recorded here rather than quietly dropped; the duplication is a fact about how the two
lanes were dispatched, not a defect in either proof.

What is NOT duplicated: §1 (the abstract brick and the necessity of both of its hypotheses), §4 (the
transfer to `deltaJQuadFormCovFaithful` through `H`-invariance — `TransverseClass` states its target
over `cStarDeltaKCFormCorr` and proves no transfer), §6, §8, §9.

**A second, PARTIAL overlap, found by this module's own nested validator and recorded rather than
left implicit:** `LineIntegralCovariant.lineCoarseRestrictCov_const_witness` already proves
`Q_ell(constant v) = v` — but only at ONE fixed extent, ONE fixed `ell = witnessEll = 2` and ONE
fixed coarse bond, as a falsifiability pin against the convicted single-bond operator. §6's
`Q_constField` is the general statement (every `L`, every `ell` with `0 < ell` and `ell ∣ L μ + 1`,
every coarse bond, every value), which is what a refutation quantified over `ell` needs; the
witness-point lemma cannot be lifted to it. Likewise
`CovariantHjFaithful.deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm` is the `ell = 1`,
extension-free special case of §4's `deltaJ_eq_dstarDQuadForm_hjExtension`, not the same statement.

**And the two lanes CONVERGE on §8.** §8 proves the exclusion of curl-free unit shadows is
NECESSARY, for every `U`. `TransverseClass.class_transverse_to_curlFree` proves that the class
CMP99b p.428 PRINTS (`B = 0` on `⋃ Ax(y)` together with `Q₁B = 0`) is transverse to the curl-free
subspace — at `U = 1`, in the real sector. So the clause §8 forces is a clause the source already
prints. Neither half is a proof of the min-swap target; together they say the forced constraint is
not an obstruction.

## What this module does NOT claim

* NOT a claim about CMP99b p.428, about Bałaban's Lemma, or about any lattice object, in §1–§3:
  those are pure order theory. §4–§10 are about THIS TREE's declarations
  (`deltaJQuadFormCovFaithful`, `lineCoarseRestrictCovLM`, `dstarDQuadForm`), not about the printed
  page; the page-level reading is `TransverseClass.lean`'s, quoted there with locators.
* **NOT a proof of `MinSwapTotalTarget` for any `γ > 0` and any nonempty `𝒜`.** That inequality —
  a covariant discrete Poincaré estimate on the gauge slice — is the entire mathematical content and
  is untouched here. §8 constrains `𝒜`; §5 shows the standing counterexample does not reach the
  statement; neither is progress toward proving it.
  **AND THIS DISCLAIMER WAS CONVICTED, 2026-07-29, on two counts** (two de-correlated prosecutions;
  see §9a). (i) It is PROSE, and prose is not a type-checked obligation: both raw targets were
  inhabited by compiling, axiom-clean, content-free terms, exactly the `Spine.FULL3DTarget` pattern.
  (ii) Its own side condition — "any `γ > 0` and any nonempty `𝒜`" — is the WRONG condition:
  `𝒜 = {0}` is nonempty, has an inhabited quantifier domain, and satisfies the target for every
  `γ > 0` however large (`MinSwapTotalTarget_holds_at_zero_class`). The §1 NON-VACUITY WARNING below
  had already named that mechanism for the abstract brick; nobody applied it to §9's lattice targets.
  §9a fixes both: the vacuities are theorems, and the guarded targets carry a domain witness with
  positive coarse energy inside the `Prop`.
* NOT delivered: a domain witness at general `ell` that survives §8's forced exclusion. §7's witness
  IS §6's refuting datum, and §10's is at `ell = 1`, a degenerate renormalisation step (`V = ⊥`).
  **Two cheap routes were tried and both FAIL, for the same reason, and the reason is worth
  recording** — it sharpens what any witness must look like:

  - `constField c + loopField` (in the slice by linearity; not curl-free because
    `curl(const) = 0`; unit shadow `= c + 0 = c ≠ 0` by §6 and §5) — **FAILS**: its shadow is the
    CONSTANT coarse field, which is the shadow of `constField c`, a curl-free slice element. §8
    excludes shadows, not fields, so this datum's shadow is excluded.
  - a one-direction constant `A b = if b.2 = 0 then c else 0` (div-free and curl-free at `U = 1`,
    shadow non-constant ACROSS DIRECTIONS) — **FAILS** for the identical reason: it is itself
    curl-free, so its own shadow is an excluded curl-free image.

  So the excluded set contains every PER-DIRECTION-CONSTANT coarse field, and a surviving witness
  must have a shadow that varies WITH POSITION. The construction that does it is a transverse shear
  `A(x,μ) = g(x_ν)·c` (`ν ≠ μ`): div-free at `U = 1` (shifting along `μ` does not change `x_ν`),
  curl `= (g(x_ν) − g(x_ν+1))·c ≠ 0` for non-constant `g`, and
  `Q_ell A(y,μ) = (1/ell)·(Σ_{j<ell} g(y_ν+j))·c`, so `g` with alternating block sums gives a
  position-varying nonzero shadow whose NEXT-level average vanishes. **The exact point where this
  module cannot reach it**: that `Q_ell` value needs `Σ_{x ∈ blockOf y ell} g(x_ν) = ell² · Σ_{j<ell}
  g((y ν).val + j)`, i.e. a factorization of a sum over `blockOf` along one coordinate.
  `AdmissibleSubspace.card_blockOf` builds exactly the required bijection
  `blockOf y ell ≃ (Fin 3 → Fin ell)` — but INSIDE its own proof, as a `Finset.image` equality; it is
  not exported as an `Equiv` and no `Finset.sum` version exists in the tree. That export is the whole
  gap, and it is a mechanical lemma, not mathematics.
  **CLOSED 2026-07-29 in `Balaban/MinSwapWitness.lean`** (a downstream module, so this file cannot
  cite the theorems without an import cycle): `sum_blockOf_coord` exports the reindexing,
  `shear`/`Q_shear` build the transverse shear, and `shear_survives_forced_exclusion` composes the
  witness. The `∀ ell` statement is NOT thereby proved — that module delivers the shadow formula at
  general `ell`, and the surviving-witness composition at one concrete `(L, ell) = (witnessL, 2)`.
* NON-VACUITY WARNING for consumers of §1: if `n (Q A) = 0` for every `A ∈ S` with `Q A ∈ 𝒜`, the
  right-hand side degenerates to `0 ≤ q A`. `minSwap_nonvacuous_witness` shows the hypothesis set of
  `minSwap_iff` is satisfiable with `γ > 0`, `𝒜 ≠ ∅` and both sides non-vacuous and TRUE.
-/

namespace AdalyFormal.Balaban.MinSwap

/-! ## §1 — the abstract min-swap -/

section Abstract

variable {E F : Type*}

/-- **The fibre of the slice `S` over a unit-level datum `B`.** -/
def fibre (S : Set E) (Q : E → F) (B : F) : Set E := {A | A ∈ S ∧ Q A = B}

theorem mem_fibre {S : Set E} {Q : E → F} {B : F} {A : E} :
    A ∈ fibre S Q B ↔ A ∈ S ∧ Q A = B := Iff.rfl

/-- **The Schur complement.** The infimum of the fine energy over the fibre. With `sInf ∅ = 0` in
`ℝ`, this is `0` at every `B` outside `Q(S)` — which is exactly why `minSwap_iff` needs the
surjectivity hypothesis and why it cannot be silent. -/
noncomputable def schur (q : E → ℝ) (S : Set E) (Q : E → F) (B : F) : ℝ :=
  sInf (q '' fibre S Q B)

theorem bddBelow_image_of_nonneg {q : E → ℝ} {S : Set E} {Q : E → F} (B : F)
    (hq : ∀ A ∈ S, 0 ≤ q A) : BddBelow (q '' fibre S Q B) := by
  refine ⟨0, ?_⟩
  rintro y ⟨A, ⟨hA, -⟩, rfl⟩
  exact hq A hA

/-- **`→` (take the infimum): the Schur bound implies the total-space inequality.** Consumes
nonnegativity of `q` on `S` (through `BddBelow`), NOT surjectivity. -/
theorem total_of_schur {q : E → ℝ} {S : Set E} {Q : E → F} {n : F → ℝ} {γ : ℝ} {𝒜 : Set F}
    (hq : ∀ A ∈ S, 0 ≤ q A)
    (h : ∀ B ∈ 𝒜, γ * n B ≤ schur q S Q B) :
    ∀ A ∈ S, Q A ∈ 𝒜 → γ * n (Q A) ≤ q A := by
  intro A hA hQA
  refine le_trans (h (Q A) hQA) ?_
  exact csInf_le (bddBelow_image_of_nonneg (Q A) hq) ⟨A, ⟨hA, rfl⟩, rfl⟩

/-- **`←` (plug a fibre element): the total-space inequality implies the Schur bound.** Consumes
NONEMPTY FIBRES (`Q(S) ⊇ 𝒜`), NOT nonnegativity. -/
theorem schur_of_total {q : E → ℝ} {S : Set E} {Q : E → F} {n : F → ℝ} {γ : ℝ} {𝒜 : Set F}
    (hsurj : ∀ B ∈ 𝒜, (fibre S Q B).Nonempty)
    (h : ∀ A ∈ S, Q A ∈ 𝒜 → γ * n (Q A) ≤ q A) :
    ∀ B ∈ 𝒜, γ * n B ≤ schur q S Q B := by
  intro B hB
  obtain ⟨A₀, hA₀⟩ := hsurj B hB
  refine le_csInf ⟨q A₀, A₀, hA₀, rfl⟩ ?_
  rintro y ⟨A, ⟨hA, hQ⟩, rfl⟩
  have := h A hA (by rw [hQ]; exact hB)
  rwa [hQ] at this

/-- **THE MIN-SWAP.** A Schur-complement lower bound over an admissible class is EXACTLY the
total-space inequality on the slice, given nonempty fibres and a nonnegative fine energy. -/
theorem minSwap_iff {q : E → ℝ} {S : Set E} {Q : E → F} {n : F → ℝ} {γ : ℝ} {𝒜 : Set F}
    (hsurj : ∀ B ∈ 𝒜, (fibre S Q B).Nonempty)
    (hq : ∀ A ∈ S, 0 ≤ q A) :
    (∀ B ∈ 𝒜, γ * n B ≤ schur q S Q B)
      ↔ (∀ A ∈ S, Q A ∈ 𝒜 → γ * n (Q A) ≤ q A) :=
  ⟨total_of_schur hq, schur_of_total hsurj⟩

end Abstract

/-! ## §1b — hypothesis necessity: BOTH hypotheses of `minSwap_iff` are load-bearing

Each is refuted by an explicit two-element configuration over `ℝ`. These are the L7 degenerate-
witness prosecutions for `minSwap_iff`: a reader may not drop either hypothesis. -/

/-- **SURJECTIVITY IS NECESSARY for `←`.** With `E = F = ℝ`, `S = {0}`, `Q = id`, `q = n = (·^2)`,
`γ = 1`, `𝒜 = {1}`: the fibre over `1` is EMPTY, so `schur = sInf ∅ = 0` and the Schur side is
`1 ≤ 0`, FALSE; while the total-space side is vacuously TRUE (the only slice element is `0`, whose
image `0` is not in `𝒜`). So `schur_of_total` genuinely needs `hsurj`, and a consumer that asserts
the min-swap without it has asserted something false. -/
theorem minSwap_mpr_needs_nonempty :
    (∀ A ∈ ({0} : Set ℝ), (id A) ∈ ({1} : Set ℝ) → (1 : ℝ) * (id A) ^ 2 ≤ A ^ 2) ∧
    ¬ (∀ B ∈ ({1} : Set ℝ), (1 : ℝ) * B ^ 2
        ≤ schur (fun x : ℝ => x ^ 2) ({0} : Set ℝ) id B) := by
  classical
  refine ⟨?_, ?_⟩
  · intro A hA hQ
    rw [Set.mem_singleton_iff] at hA
    subst hA
    exact absurd hQ (by norm_num)
  · intro h
    have h1 := h 1 rfl
    have hempty : fibre ({0} : Set ℝ) id (1 : ℝ) = ∅ := by
      ext A
      simp only [mem_fibre, Set.mem_singleton_iff, id_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro hA
      rw [hA]
      norm_num
    rw [schur, hempty, Set.image_empty, Real.sInf_empty] at h1
    norm_num at h1

/-- **NONNEGATIVITY (`BddBelow`) IS NECESSARY for `→`.** With `E = F = ℝ`, `S = univ`,
`Q = fun _ => 0`, `n = fun _ => 0`, `q = id`, `𝒜 = {0}`, `γ = 1`: the image of `q` over the fibre is
all of `ℝ`, not bounded below, so `sInf` returns the junk value `0` and the Schur side reads
`0 ≤ 0`, TRUE; while the total-space side reads `0 ≤ A` for every real `A`, FALSE at `A = -1`. -/
theorem minSwap_mp_needs_bddBelow :
    (∀ B ∈ ({0} : Set ℝ), (1 : ℝ) * (0 : ℝ)
        ≤ schur id (Set.univ : Set ℝ) (fun _ => (0 : ℝ)) B) ∧
    ¬ (∀ A ∈ (Set.univ : Set ℝ), (1 : ℝ) * (0 : ℝ) ≤ id A) := by
  classical
  refine ⟨?_, ?_⟩
  · intro B hB
    have himg : (id : ℝ → ℝ) '' fibre (Set.univ : Set ℝ) (fun _ => (0 : ℝ)) B = Set.univ := by
      ext y
      simp only [Set.mem_univ, iff_true]
      exact ⟨y, ⟨Set.mem_univ y, by rw [Set.mem_singleton_iff] at hB; rw [hB]⟩, rfl⟩
    have hnb : ¬ BddBelow (Set.univ : Set ℝ) := by
      intro ⟨c, hc⟩
      have := hc (Set.mem_univ (c - 1))
      linarith
    rw [schur, himg, Real.sInf_of_not_bddBelow hnb]
    norm_num
  · intro h
    have := h (-1) (Set.mem_univ _)
    norm_num at this

/-! ## §2 — the fibre over `0` is not a test space -/

section FibreZero

variable {E F : Type*}

/-- **A SLICE ELEMENT WHOSE UNIT SHADOW VANISHES SATISFIES THE TOTAL-SPACE INEQUALITY, for every
`γ`.** Four lines, and it is the whole reason the min-swap is immune to the datum that refuted the
one-space encodings: there the right-hand side was the datum's own FINE energy (`bondEnergy Btil`,
strictly positive); here it is the fine energy of its UNIT IMAGE, which is `0`. -/
theorem fibre_datum_satisfies_total {q : E → ℝ} {Q : E → F} {n : F → ℝ} (γ : ℝ)
    {A : E} [Zero F] (hQ : Q A = 0) (hn : n 0 = 0) (hqA : 0 ≤ q A) :
    γ * n (Q A) ≤ q A := by
  rw [hQ, hn, mul_zero]
  exact hqA

/-- **`schur q S Q 0 = 0`** whenever the zero field lies in the slice with zero energy and zero unit
shadow, and `q ≥ 0` on `S`. Hence the min-swap requirement AT `B = 0` is exactly `γ * n 0 ≤ 0`,
which is a tautology when `n 0 = 0`: no element of the fibre over `0`, however large its fine
energy, imposes any constraint. -/
theorem schur_eq_zero_of_zero_mem {q : E → ℝ} {S : Set E} {Q : E → F} [Zero E] [Zero F]
    (h0 : (0 : E) ∈ S) (hQ0 : Q 0 = 0) (hq0 : q 0 = 0) (hq : ∀ A ∈ S, 0 ≤ q A) :
    schur q S Q 0 = 0 := by
  refine le_antisymm ?_ ?_
  · refine le_of_le_of_eq (csInf_le (bddBelow_image_of_nonneg (0 : F) hq) ?_) hq0
    exact ⟨0, ⟨h0, hQ0⟩, rfl⟩
  · refine le_csInf ⟨q 0, 0, ⟨h0, hQ0⟩, rfl⟩ ?_
    rintro y ⟨A, ⟨hA, -⟩, rfl⟩
    exact hq A hA

end FibreZero

/-! ## §3 — the specialization the seed asked for -/

section Inner

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The min-swap in the seed's stated setting**: `S` a submodule of a real inner product space,
`Q` a continuous linear map, unit-level weight `‖B‖ ^ 2`, `q` any nonnegative fine energy. -/
theorem minSwap_iff_inner {q : E → ℝ} (S : Submodule ℝ E) (Q : E →L[ℝ] F) {γ : ℝ} {𝒜 : Set F}
    (hsurj : ∀ B ∈ 𝒜, (fibre (S : Set E) (fun A => Q A) B).Nonempty)
    (hq : ∀ A ∈ S, 0 ≤ q A) :
    (∀ B ∈ 𝒜, γ * ‖B‖ ^ 2 ≤ schur q (S : Set E) (fun A => Q A) B)
      ↔ (∀ A ∈ S, Q A ∈ 𝒜 → γ * ‖Q A‖ ^ 2 ≤ q A) :=
  minSwap_iff (n := fun B => ‖B‖ ^ 2) hsurj hq

end Inner

/-! ## §3b — the hypotheses are jointly satisfiable with BOTH sides non-vacuous and TRUE

Necessity counterexamples show a hypothesis cannot be dropped; they do not show the theorem has a
non-degenerate instance. This does. -/

/-- **NON-VACUITY WITNESS.** `E = F = ℝ`, `S = univ`, `Q = id`, `q = n = (·^2)`, `γ = 1`,
`𝒜 = univ`: every hypothesis of `minSwap_iff` holds, `γ > 0`, the admissible class contains a datum
`B = 1` with `n B = 1 > 0` and a nonempty fibre over it, and BOTH sides of the equivalence are TRUE.
So the equivalence is not being verified over an empty or content-free configuration. -/
theorem minSwap_nonvacuous_witness :
    (∀ B : ℝ, B ∈ fibre (Set.univ : Set ℝ) id B) ∧
    (∀ A ∈ (Set.univ : Set ℝ), (0 : ℝ) ≤ A ^ 2) ∧
    (0 : ℝ) < (1 : ℝ) ^ 2 ∧
    (∀ B ∈ (Set.univ : Set ℝ), (1 : ℝ) * B ^ 2 ≤ schur (fun x : ℝ => x ^ 2) Set.univ id B) ∧
    (∀ A ∈ (Set.univ : Set ℝ), id A ∈ (Set.univ : Set ℝ) →
      (1 : ℝ) * (id A) ^ 2 ≤ (fun x : ℝ => x ^ 2) A) := by
  classical
  refine ⟨fun B => ⟨Set.mem_univ B, rfl⟩, fun A _ => sq_nonneg A, by norm_num, ?_,
    fun A _ _ => by simp⟩
  refine schur_of_total (fun B _ => ⟨B, Set.mem_univ B, rfl⟩) ?_
  intro A _ _
  simp

/-! ## §4 — THE TREE'S SCHUR COMPLEMENT IS NOT AN `sInf`, AND THAT KILLS THE SURJECTIVITY STEP

The seed names `Q(S) ⊇ 𝒜` as its hardest step. **In this tree the step does not arise.**
`CovariantHjFaithful.deltaJQuadFormCovFaithful ell levels U A₀` is not
`sInf {q A | …}`; it is `‖D_U (H A₀)‖²` for the explicit Bałaban extension
`H A₀ = A₀ + hjCorrectionCovFaithful …`. Two facts about `H`, both already theorems, replace the
infimum entirely:

* `RegularUGamma0.lineCoarseRestrictCov_hjExtension` — `Q_ell (H A₀) = Q_ell A₀` (the correction
  lies in `V`, whose first clause is `Q_ell(·) = 0`). REUSED, not rebuilt (LAW-19).
* `CovariantHjFaithful.hjExtensionCovFaithful_isBalabanExtensionCov (…).gaugeFixed` — `H` preserves
  the gauge slice `{A | R^{cov}(D*_U A) = 0}`.

So a total-space inequality on ANY `H`-invariant class transfers to the Schur complement, with no
fibre, no infimum, no empty-fibre hazard and no surjectivity lemma. `minSwap_iff` (§1) remains the
statement for anyone who works with the `sInf` form — and it is precisely there that surjectivity is
proved NECESSARY (`minSwap_mpr_needs_nonempty`).

**What §4 also exposes, and is the real constraint:** the transfer needs the class to be
`H`-INVARIANT. Clauses on the UNIT-level image are free (`unitClause_hjExtension_invariant`, because
`Q_ell H = Q_ell`); the gauge slice is fine (`slice_hjExtension_invariant`). A clause imposed at the
FINE level that is not one of these — the axial-staircase gauge `∀ e ∈ staircasePath y x, A e = 0`
above all — has NO such theorem in this tree, and therefore cannot feed this transfer. That is a
statement about what is available, not a proof that it is impossible. -/

section Tree

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjFaithful
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice blockOf
  card_blockOf_of_coarse)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU deltaKernelImageCovH RcovLM
  gradCovariantAdjointLM)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RegularUGamma0 (lineCoarseRestrictCov_hjExtension)
open AdalyFormal.Balaban.U1LeadingCoercivity (deltaJQuadFormCovFaithful_eq_zero_of_curl_zero)
open AdalyFormal.Balaban.RegularUCoercivityFull (covCoarseBondInner_self_eq_sum)
open AdalyFormal.Balaban.Q1Real (rZeroA rZeroA_trivialU)
open AdalyFormal.Balaban.QOne (pathSite)

variable {L : PeriodicLatticeExtent}

/-- **The Schur complement IS the fine curl energy of the Bałaban extension.** Definitional; stated
because every theorem in §4 is a rewrite along it. -/
theorem deltaJ_eq_dstarDQuadForm_hjExtension {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) :
    deltaJQuadFormCovFaithful ell levels U A0
      = dstarDQuadForm U (hjExtensionCovFaithful ell levels U A0) := rfl

/-- **THE MIN-SWAP TRANSFER, class form.** For ANY class `C` closed under the Bałaban extension and
ANY unit-level weight `n`, a total-space inequality on `C` gives the Schur-complement lower bound on
`C`. No infimum, no fibre, no surjectivity. -/
theorem deltaJ_ge_of_total_on_hjInvariant {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (C : Set (Bond L → SuTwo)) (n : (CoarseBond L ell → SuTwo) → ℝ) (γ : ℝ)
    (hinv : ∀ A ∈ C, hjExtensionCovFaithful ell levels U A ∈ C)
    (htot : ∀ A ∈ C, γ * n (lineCoarseRestrictCovLM U ell A) ≤ dstarDQuadForm U A)
    (A0 : Bond L → SuTwo) (hA0 : A0 ∈ C) :
    γ * n (lineCoarseRestrictCovLM U ell A0) ≤ deltaJQuadFormCovFaithful ell levels U A0 := by
  have h1 := htot _ (hinv A0 hA0)
  rw [lineCoarseRestrictCov_hjExtension levels U A0] at h1
  rwa [deltaJ_eq_dstarDQuadForm_hjExtension]

/-- **The gauge slice** `{A | R^{cov}_U(D*_U A) = 0}`. At `levels = []` this is exactly
`{A | D*_U A = 0}` (`StokesCommU.Rcov_nil_clause_iff_divFree`). -/
def slice (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] : Set (Bond L → SuTwo) :=
  {A | RcovLM U levels (gradCovariantAdjointLM U A) = 0}

/-- **THE GAUGE SLICE IS `H`-INVARIANT.** Straight from `IsBalabanExtensionCovFaithful.gaugeFixed`.
-/
theorem slice_hjExtension_invariant {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A : Bond L → SuTwo) (hA : A ∈ slice levels U) :
    hjExtensionCovFaithful ell levels U A ∈ slice levels U :=
  (hjExtensionCovFaithful_isBalabanExtensionCov ell levels U A
    (lineCoarseRestrictCovLM U ell A) rfl hA).gaugeFixed

/-- **EVERY CLAUSE ON THE UNIT-LEVEL IMAGE IS `H`-INVARIANT, for free** — because `Q_ell H = Q_ell`.
This is the structural reason the seed's mechanism (ii) (`Q₁ B = 0`, a clause on `B`) is the RIGHT
KIND of clause, while a fine-level staircase clause is not: the class does not have to be preserved,
the image is literally unchanged. -/
theorem unitClause_hjExtension_invariant {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (A : Bond L → SuTwo)
    (hA : lineCoarseRestrictCovLM U ell A ∈ 𝒜) :
    lineCoarseRestrictCovLM U ell (hjExtensionCovFaithful ell levels U A) ∈ 𝒜 := by
  rwa [lineCoarseRestrictCov_hjExtension levels U A]

/-- The class the min-swap route actually uses: the gauge slice cut by a UNIT-level admissible
class. -/
def sliceOver {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) : Set (Bond L → SuTwo) :=
  {A | A ∈ slice levels U ∧ lineCoarseRestrictCovLM U ell A ∈ 𝒜}

theorem sliceOver_hjExtension_invariant {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (A : Bond L → SuTwo) (hA : A ∈ sliceOver levels U 𝒜) :
    hjExtensionCovFaithful ell levels U A ∈ sliceOver levels U 𝒜 :=
  ⟨slice_hjExtension_invariant levels U A hA.1,
    unitClause_hjExtension_invariant levels U 𝒜 A hA.2⟩

/-- **THE MIN-SWAP, INSTANTIATED AT THE TREE'S OBJECTS.** For every `ell`, `levels`, `U`, every
unit-level admissible class `𝒜`, every unit-level weight `n` and every `γ`:

  `(∀ A in the gauge slice with Q_ell A ∈ 𝒜,  γ · n(Q_ell A) ≤ ‖D_U A‖²)`
     ⟹ `(∀ A₀ in the gauge slice with Q_ell A₀ ∈ 𝒜,  γ · n(Q_ell A₀) ≤ ⟨A₀, Δ_k A₀⟩)`.

Every parameter is universally quantified; `𝒜` is FREE, so this is not a claim that any particular
admissible class works. §6 proves that `𝒜` cannot be everything. -/
theorem minSwap_transfer {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (n : (CoarseBond L ell → SuTwo) → ℝ) (γ : ℝ)
    (htot : ∀ A, A ∈ slice levels U → lineCoarseRestrictCovLM U ell A ∈ 𝒜 →
      γ * n (lineCoarseRestrictCovLM U ell A) ≤ dstarDQuadForm U A)
    (A0 : Bond L → SuTwo) (h1 : A0 ∈ slice levels U)
    (h2 : lineCoarseRestrictCovLM U ell A0 ∈ 𝒜) :
    γ * n (lineCoarseRestrictCovLM U ell A0) ≤ deltaJQuadFormCovFaithful ell levels U A0 :=
  deltaJ_ge_of_total_on_hjInvariant levels U (sliceOver levels U 𝒜) n γ
    (fun A hA => sliceOver_hjExtension_invariant levels U 𝒜 A hA)
    (fun A hA => htot A hA.1 hA.2) A0 ⟨h1, h2⟩

/-! ## §5 — THE REFUTING DATUM'S UNIT SHADOW IS ZERO, AND THAT IS WHY IT CANNOT REFUTE THE MIN-SWAP

`NilLevelTarget.targetAt_refuted` kills every `levels`-restriction of the level-corrected target
using `loopField`, a plaquette circulation with `bondEnergy (loopField m) > 0`. The refutation works
because the target's right-hand side is the datum's own FINE energy. Under the min-swap the
right-hand side is a function of the datum's UNIT IMAGE — and that image is `0`. -/

/-- **THE UNIT SHADOW OF THE REFUTING LOOP IS ZERO.** Re-export of
`NilLevelTarget.Q_loopField_fibre`, named for what it means here: `Q_ell(loopField) = 0`, so the
loop's unit-level datum is the zero field. Checked, not assumed. -/
theorem loopField_unit_shadow_eq_zero (m : ℕ) :
    lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) (WitnessInequality.wEll m)
      (NilLevelTarget.loopField m) = 0 :=
  NilLevelTarget.Q_loopField_fibre m

/-- **THE LOOP SATISFIES THE MIN-SWAP TOTAL-SPACE INEQUALITY, for EVERY `γ` and every weight `n`
with `n 0 = 0`.** So no choice of `γ` is refuted by this datum: it tests `0 ≤ ‖D_U(loop)‖²`. -/
theorem loopField_satisfies_minSwap_total (m : ℕ) (γ : ℝ)
    (n : (CoarseBond (WitnessInequality.wExt m) (WitnessInequality.wEll m) → SuTwo) → ℝ)
    (hn : n 0 = 0) :
    γ * n (lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m))
        (WitnessInequality.wEll m) (NilLevelTarget.loopField m))
      ≤ dstarDQuadForm (trivialU (WitnessInequality.wExt m)) (NilLevelTarget.loopField m) := by
  rw [loopField_unit_shadow_eq_zero m, hn, mul_zero]
  exact dstarDQuadForm_nonneg _ _

/-- **THE SHARP CONTRAST, AS ONE THEOREM.** At the same datum, at the same extent:
the refuted encoding's left-hand side `bondEnergy (loopField)` is STRICTLY POSITIVE, while the
min-swap's left-hand side `n (Q_ell (loopField))` is `0` for every weight `n` with `n 0 = 0`. The
refutation mechanism is the fine norm, and nothing else. -/
theorem loopField_refutes_fine_but_not_unit (m : ℕ)
    (n : (CoarseBond (WitnessInequality.wExt m) (WitnessInequality.wEll m) → SuTwo) → ℝ)
    (hn : n 0 = 0) :
    0 < RegularUPerturbation.bondEnergy (NilLevelTarget.loopField m) ∧
    n (lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) (WitnessInequality.wEll m)
      (NilLevelTarget.loopField m)) = 0 :=
  ⟨NilLevelTarget.bondEnergy_loopField_pos m, by rw [loopField_unit_shadow_eq_zero m, hn]⟩

/-! ## §6 — ATTACKING THE MIN-SWAP: THE CONSTANT FIELD KILLS THE SLICE-ONLY FORM

The min-swap dissolves the loop. It does not survive on the gauge slice ALONE. At `U = 1` a nonzero
CONSTANT bond field is
* divergence-free (`div_constField_trivialU`) — hence in the slice for every `levels`;
* curl-free (`curl_constField_trivialU`) — hence `‖D_U A‖² = 0` AND `⟨A, Δ_k A⟩ = 0`
  (`U1LeadingCoercivity.deltaJQuadFormCovFaithful_eq_zero_of_curl_zero`);
* and its unit shadow is the SAME nonzero constant (`Q_constField`), so the coarse energy on the
  left is strictly positive.

Therefore the total-space inequality on the bare slice is FALSE for every `γ > 0`, and so is the
Schur form. The consequence is not "the route is dead": it is that the unit-level admissible class
`𝒜` MUST exclude the coarse-constant field — the seed's mechanism (ii) is FORCED, not optional
(`unitClass_must_exclude_coarse_const`). -/

/-- The constant bond field with value `c`. -/
def constField (L : PeriodicLatticeExtent) (c : SuTwo) : Bond L → SuTwo := fun _ => c

/-- A constant field is curl-free at `U = 1`: `c + c - c - c = 0`. -/
theorem curl_constField_trivialU (c : SuTwo) :
    curlCovariantLM (trivialU L) (constField L c) = 0 := by
  funext p
  show curlValueCovariant (trivialU L) (constField L c) p = 0
  unfold curlValueCovariant constField
  have h1 : ∀ b : Bond L, RMap ((trivialU L) b) = LinearMap.id := by
    intro b
    change RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = LinearMap.id
    exact RMap_one
  simp only [h1, LinearMap.id_coe, id_eq]
  abel

/-- A constant field is divergence-free at `U = 1`: each direction contributes `c - c`. -/
theorem div_constField_trivialU (c : SuTwo) :
    gradCovariantAdjointLM (trivialU L) (constField L c) = 0 := by
  funext y
  rw [CovariantHjMinimizer.gradCovariantAdjointLM_apply]
  show CovariantHjMinimizer.gradCovariantAdjointValue (trivialU L) (constField L c) y = 0
  unfold CovariantHjMinimizer.gradCovariantAdjointValue constField
  have h1 : ∀ b : Bond L, RMap ((trivialU L) b)⁻¹ = LinearMap.id := by
    intro b
    change RMap ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))⁻¹ = LinearMap.id
    rw [inv_one]; exact RMap_one
  simp only [h1, LinearMap.id_coe, id_eq, sub_self, Finset.sum_const_zero]

/-- A constant field lies in the gauge slice, for EVERY `levels` (the divergence itself vanishes, so
`R^{cov}` of it vanishes by linearity — exactly the mechanism of
`NilLevelTarget.loopField_mem_fibre`'s second clause). -/
theorem constField_mem_slice (c : SuTwo) (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection] :
    constField L c ∈ slice levels (trivialU L) := by
  show RcovLM (trivialU L) levels (gradCovariantAdjointLM (trivialU L) (constField L c)) = 0
  rw [div_constField_trivialU c, map_zero]

/-- **`Q_ell(constant c) = c`.** The block average of the length-`ell` line integral of a constant
field is `(1/ell⁴) · ell³ · ell · c = c`: `ell³` sites in the block
(`AdmissibleSubspace.card_blockOf_of_coarse`) times `ell` steps along the path, against the `1/ell⁴`
normalization. Requires the source-admissible domain `0 < ell` and `ell ∣ L μ + 1` — the same
compatibility `lineCoarseRestrictCov`'s own docstring names. -/
theorem Q_constField {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (c : SuTwo)
    (b : CoarseBond L ell) :
    lineCoarseRestrictCov (trivialU L) ell (constField L c) b = c := by
  have hcast : ((ell : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  unfold lineCoarseRestrictCov
  have hinner : ∀ x ∈ blockOf b.1.1 ell,
      rZeroA (trivialU L) b.1.1 x (constField L c) b.2 ell = (ell : ℝ) • c := by
    intro x _
    rw [rZeroA_trivialU]
    show ∑ _i ∈ Finset.range ell, c = (ell : ℝ) • c
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, card_blockOf_of_coarse hdvd b.1.2,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  rw [show (1 / (ell : ℝ) ^ 4) * (((ell : ℕ) ^ 3 : ℕ) : ℝ) * (ell : ℝ) = 1 by
    push_cast
    field_simp]
  rw [one_smul]

/-- The unit shadow of a constant fine field is the constant coarse field. -/
theorem Q_constField_eq {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (c : SuTwo) :
    lineCoarseRestrictCovLM (trivialU L) ell (constField L c)
      = (fun _ : CoarseBond L ell => c) :=
  funext fun b => Q_constField hell hdvd c b

/-- **A curl-free field has zero fine curl energy — for EVERY `U`.** `dstarDQuadForm` IS the curl
energy, so this is immediate; it is stated because §8 turns it into a `U`-general obstruction. -/
theorem dstarDQuadForm_eq_zero_of_curl_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (h : curlCovariantLM U A = 0) :
    dstarDQuadForm U A = 0 := by
  unfold dstarDQuadForm covPlaqInner
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [show curlValueCovariant U A p = 0 from congrFun h p, hsInner_zero_zero]

/-- The fine curl energy of a constant field is `0` at `U = 1`. -/
theorem dstarDQuadForm_constField (c : SuTwo) :
    dstarDQuadForm (trivialU L) (constField L c) = 0 :=
  dstarDQuadForm_eq_zero_of_curl_zero (trivialU L) (constField L c) (curl_constField_trivialU c)

/-- The Schur complement of a constant field is `0` at `U = 1`. -/
theorem deltaJ_constField_eq_zero {ell : ℕ} (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels (trivialU L)).HasOrthogonalProjection] (c : SuTwo) :
    deltaJQuadFormCovFaithful ell levels (trivialU L) (constField L c) = 0 :=
  deltaJQuadFormCovFaithful_eq_zero_of_curl_zero ell levels (trivialU L) (constField L c)
    (curl_constField_trivialU c)

/-- The origin is a coarse site, so `CoarseBond L ell` is inhabited — needed to know the coarse
energy of a nonzero constant coarse field is strictly positive, not an empty sum. -/
theorem zeroSite_mem_CoarseLattice (ell : ℕ) :
    (fun _ : Fin 3 => (0 : Fin (L _ + 1))) ∈ CoarseLattice L ell := by
  refine mem_CoarseLattice.mpr fun μ => ?_
  simp

/-- **The coarse `L²` energy is a genuine norm: it is strictly positive off `0`.** Needed so that
"the left-hand side vanishes" can be converted into "the unit shadow vanishes" — the step that turns
§8's obstruction from a statement about a number into a statement about the OPERATOR `Q_ell`. -/
theorem covCoarseBondInner_pos_of_ne_zero {ell : ℕ} {B : CoarseBond L ell → SuTwo}
    (hB : B ≠ 0) : 0 < covCoarseBondInner B B := by
  rw [covCoarseBondInner_self_eq_sum]
  obtain ⟨c, hc⟩ : ∃ c : CoarseBond L ell, B c ≠ 0 := by
    by_contra hcon
    exact hB (funext fun c => not_not.mp (not_exists.mp hcon c))
  refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨c, Finset.mem_univ _, ?_⟩
  have h : 0 < ‖B c‖ := norm_pos_iff.mpr hc
  positivity

/-- A nonzero constant coarse field is a nonzero function — the coarse-bond type is inhabited by the
origin bond. -/
theorem const_coarse_ne_zero {ell : ℕ} {c : SuTwo} (hc : c ≠ 0) :
    (fun _ : CoarseBond L ell => c) ≠ (0 : CoarseBond L ell → SuTwo) := fun h =>
  hc (congrFun h
    ((⟨fun _ : Fin 3 => (0 : Fin (L _ + 1)), zeroSite_mem_CoarseLattice ell⟩, 0) :
      CoarseBond L ell))

/-- **The coarse energy of a nonzero constant coarse field is strictly positive.** -/
theorem covCoarseBondInner_const_pos {ell : ℕ} {c : SuTwo} (hc : c ≠ 0) :
    0 < covCoarseBondInner (fun _ : CoarseBond L ell => c) (fun _ : CoarseBond L ell => c) :=
  covCoarseBondInner_pos_of_ne_zero (const_coarse_ne_zero hc)

/-- **THE TOTAL-SPACE INEQUALITY ON THE BARE GAUGE SLICE IS FALSE**, at `U = 1`, for every
compatible `ell`, every `levels` and every `γ > 0`, against the coarse `L²` energy. Witness: the
constant field `suTwoWitness`. -/
theorem minSwap_total_on_bare_slice_refuted {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    {γ : ℝ} (hγ : 0 < γ) :
    ¬ (∀ A, A ∈ slice levels (trivialU L) →
        γ * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) ell A)
              (lineCoarseRestrictCovLM (trivialU L) ell A)
          ≤ dstarDQuadForm (trivialU L) A) := by
  intro h
  have hA := h (constField L suTwoWitness) (constField_mem_slice suTwoWitness levels)
  rw [Q_constField_eq hell hdvd suTwoWitness, dstarDQuadForm_constField] at hA
  have hpos : 0 < γ * covCoarseBondInner (fun _ : CoarseBond L ell => suTwoWitness)
      (fun _ : CoarseBond L ell => suTwoWitness) :=
    mul_pos hγ (covCoarseBondInner_const_pos suTwoWitness_ne_zero)
  linarith

/-- **THE SCHUR FORM ON THE BARE GAUGE SLICE IS ALSO FALSE** — same datum, through
`deltaJQuadFormCovFaithful_eq_zero_of_curl_zero`. So the failure is not an artifact of replacing
`Δ_k` by the larger fine energy. -/
theorem minSwap_schur_on_bare_slice_refuted {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels (trivialU L)).HasOrthogonalProjection]
    {γ : ℝ} (hγ : 0 < γ) :
    ¬ (∀ A, A ∈ slice levels (trivialU L) →
        γ * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) ell A)
              (lineCoarseRestrictCovLM (trivialU L) ell A)
          ≤ deltaJQuadFormCovFaithful ell levels (trivialU L) A) := by
  intro h
  have hA := h (constField L suTwoWitness) (constField_mem_slice suTwoWitness levels)
  rw [Q_constField_eq hell hdvd suTwoWitness, deltaJ_constField_eq_zero levels suTwoWitness] at hA
  have hpos : 0 < γ * covCoarseBondInner (fun _ : CoarseBond L ell => suTwoWitness)
      (fun _ : CoarseBond L ell => suTwoWitness) :=
    mul_pos hγ (covCoarseBondInner_const_pos suTwoWitness_ne_zero)
  linarith

/-- **THE FORCED CLAUSE.** If the min-swap total-space inequality holds on the slice over a
unit-level class `𝒜` with `γ > 0`, then `𝒜` does NOT contain the constant coarse field. So any
admissible class that can carry this route must exclude coarse-constant unit data — which is exactly
the seed's mechanism (ii) (`Q₁ B = 0`, the vanishing of the NEXT level's block averages: a constant
coarse field has nonzero averages at every level). Stated as a constraint on `𝒜`, which is where the
statement gate must now look. -/
theorem unitClass_must_exclude_coarse_const {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) {γ : ℝ} (hγ : 0 < γ)
    (h : ∀ A, A ∈ slice levels (trivialU L) → lineCoarseRestrictCovLM (trivialU L) ell A ∈ 𝒜 →
      γ * covCoarseBondInner (lineCoarseRestrictCovLM (trivialU L) ell A)
            (lineCoarseRestrictCovLM (trivialU L) ell A)
        ≤ dstarDQuadForm (trivialU L) A) :
    (fun _ : CoarseBond L ell => suTwoWitness) ∉ 𝒜 := by
  intro hmem
  have hA := h (constField L suTwoWitness) (constField_mem_slice suTwoWitness levels)
    (by rw [Q_constField_eq hell hdvd suTwoWitness]; exact hmem)
  rw [Q_constField_eq hell hdvd suTwoWitness, dstarDQuadForm_constField] at hA
  have hpos : 0 < γ * covCoarseBondInner (fun _ : CoarseBond L ell => suTwoWitness)
      (fun _ : CoarseBond L ell => suTwoWitness) :=
    mul_pos hγ (covCoarseBondInner_const_pos suTwoWitness_ne_zero)
  linarith

/-! ## §7 — the quantifier domain of the min-swap total-space statement is INHABITED with a
STRICTLY POSITIVE left-hand side

A refutation shows the statement is not vacuously true; this shows it is not vacuously FALSE either
— i.e. the `∀` really does range over data with nonzero unit shadow, so `minSwap_transfer` is not
being applied over an empty or content-free domain. The constant field is the witness (it is also
§6's refuting datum: the SAME configuration both inhabits the domain and kills the bare-slice form,
which is precisely why the clause on `𝒜` is forced rather than cosmetic). -/

theorem minSwap_domain_inhabited_with_positive_lhs {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection] :
    constField L suTwoWitness ∈ slice levels (trivialU L) ∧
      0 < covCoarseBondInner
            (lineCoarseRestrictCovLM (trivialU L) ell (constField L suTwoWitness))
            (lineCoarseRestrictCovLM (trivialU L) ell (constField L suTwoWitness)) := by
  refine ⟨constField_mem_slice suTwoWitness levels, ?_⟩
  rw [Q_constField_eq hell hdvd suTwoWitness]
  exact covCoarseBondInner_const_pos suTwoWitness_ne_zero

/-! ## §8 — THE OBSTRUCTION IN ITS GENERAL, `U`-INDEPENDENT FORM

§6's constant field is one instance of a mechanism that does not depend on `U`, on `ell`, on
`levels`, or on the choice of witness:

  **`dstarDQuadForm U` IS the covariant curl energy.** So on the covariant-curl-free part of the
  gauge slice the min-swap total-space inequality reads `γ · ‖Q_ell A‖²_coarse ≤ 0`, and with
  `γ > 0` and the coarse energy a genuine norm (`covCoarseBondInner_pos_of_ne_zero`) that FORCES
  `Q_ell A = 0`.

`total_forces_curlFree_unit_shadow_zero` is that theorem, for every `U`. Read as a design
constraint it says: **the min-swap route is available exactly to the extent that `Q_ell` annihilates
the curl-free part of the slice**; where it does not, the admissible class must exclude the images
(`unitClass_must_exclude_curlFree_image`).

At `U = 1` the slice's curl-free part is NOT annihilated: constant fields are div-free, curl-free,
and `Q_ell(constant c) = c` (§6). So the exclusion is not hypothetical — it is forced, and the
seed's mechanism (ii) (`Q₁ B = 0`, vanishing of the NEXT level's block averages) is exactly the
right shape of clause for it, because a nonzero constant coarse field has nonzero averages at every
level. **This attack therefore does not kill the seed; it converts one of the seed's three listed
mechanisms from optional into forced, and it does so for every `U`.**

What is NOT settled here: whether an admissible class that excludes these images leaves the
inequality TRUE. That is the total-space inequality itself, and it is not addressed anywhere in this
module. -/

/-- **`U`-GENERAL.** If the min-swap total-space inequality holds on the slice over `𝒜` with
`γ > 0`, then every covariant-curl-free element of the slice whose unit datum is admissible has
VANISHING unit shadow. -/
theorem total_forces_curlFree_unit_shadow_zero {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) {γ : ℝ} (hγ : 0 < γ)
    (htot : ∀ A, A ∈ slice levels U → lineCoarseRestrictCovLM U ell A ∈ 𝒜 →
      γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A)
            (lineCoarseRestrictCovLM U ell A)
        ≤ dstarDQuadForm U A)
    (A : Bond L → SuTwo) (hA : A ∈ slice levels U)
    (hmem : lineCoarseRestrictCovLM U ell A ∈ 𝒜)
    (hcurl : curlCovariantLM U A = 0) :
    lineCoarseRestrictCovLM U ell A = 0 := by
  by_contra hne
  have h1 := htot A hA hmem
  rw [dstarDQuadForm_eq_zero_of_curl_zero U A hcurl] at h1
  have hpos := mul_pos hγ (covCoarseBondInner_pos_of_ne_zero hne)
  linarith

/-- **`U`-GENERAL, contrapositive form: the constraint the admissible class must satisfy.** If a
curl-free slice element has NONZERO unit shadow, its unit shadow cannot be admissible. -/
theorem unitClass_must_exclude_curlFree_image {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) {γ : ℝ} (hγ : 0 < γ)
    (htot : ∀ A, A ∈ slice levels U → lineCoarseRestrictCovLM U ell A ∈ 𝒜 →
      γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A)
            (lineCoarseRestrictCovLM U ell A)
        ≤ dstarDQuadForm U A)
    (A : Bond L → SuTwo) (hA : A ∈ slice levels U) (hcurl : curlCovariantLM U A = 0)
    (hne : lineCoarseRestrictCovLM U ell A ≠ 0) :
    lineCoarseRestrictCovLM U ell A ∉ 𝒜 := fun hmem =>
  hne (total_forces_curlFree_unit_shadow_zero levels U 𝒜 hγ htot A hA hmem hcurl)

/-! ## §9 — the two targets as named `Prop`s, and the transfer between them

Both are stated with `γ` and `𝒜` as ORDINARY PARAMETERS, not existentials: there is no free datum
for a prover to choose, and no `∃`/`Nonempty` conclusion anywhere in this module (so no S91 row is
required). A consumer that wants the `∃ γ₀ > 0` form must quantify OUTSIDE these predicates, and at
that point `unitClass_must_exclude_curlFree_image` applies to whatever `γ₀` it produces. -/

/-- **THE MIN-SWAP TOTAL-SPACE TARGET.** The whole mathematical content of the route: a covariant
discrete Poincaré-type inequality on the gauge slice, with the COARSE energy of the unit shadow on
the small side. NOT proved anywhere in this module; §8 constrains it, §5 shows the standing
counterexample does not reach it. -/
def MinSwapTotalTarget {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (γ : ℝ) : Prop :=
  ∀ A, A ∈ slice levels U → lineCoarseRestrictCovLM U ell A ∈ 𝒜 →
    γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A)
          (lineCoarseRestrictCovLM U ell A)
      ≤ dstarDQuadForm U A

/-- **THE SCHUR TARGET** — the same inequality against this tree's `deltaJQuadFormCovFaithful`.

**DENOTATION CLAIM CORRECTED 2026-07-29 (S75: the wrong sentence is retained, struck).** Until
2026-07-29 this docstring read

> ~~the same inequality against the tree's actual `Δ_k` (`deltaJQuadFormCovFaithful`), which is the
> object CMP99b (3.156) stands for.~~

That is an unqualified identity claim between a Lean declaration and a printed source object, and
**this tree's own adjudicated record contradicts it.** The theorems below are unchanged; only the
denotation claim was wrong.

**What `deltaJQuadFormCovFaithful ell levels U` IS, in this tree.** The curl-relative Schur
complement `‖D_U H_j^{cov}_faithful(U) A‖²_{L²}` of a field `A : Bond L → SuTwo` living on this
tree's SINGLE fine/unit bond level, with constraint subspace `V = ker Q_ell` for the SAME `Q_ell`
(`lineCoarseRestrictCovLM U ell`) that supplies the left-hand side above. One averaging step, two
lattice levels.

**What it is NOT, at the source.** CMP99b p.428 (3.156)'s `Δ_k` is a UNIT-lattice (`Λ`) quadratic
form acting on UNIT-level fields `B`, with the FINE level already integrated out — the fine field
enters only inside `(Q G_1 Q*)^{-1}`, as the Schur complement over the fibre `{A : QA = B}` — and its
`Q` is the `j`-STEP COMPOSITE `Q_j(U) = Q(Ū^{j-1}) ⋯ Q(Ū) Q(U)` of CMP99b p.393 (3.15).

**The adjudicated rows (page-image evidence, `status = verified`):**
* `compute/denotation_dict/MISMATCHES.tsv` line 10 = `compute/denotation_dict/DENOTATION_DICT.tsv`
  line 46, row `delta_k_unit_p428_3156`: `lean_status = MISMATCH`, evidence
  `renders/bands/CMP99b_p428_pdf40_b0.png`
  (`382c72ff3b637798b1b6a9b1f185c0ac2ced2cb70fde604fe4f3b67ad4bc44f3`),
  `src_level = tgt_level = unit (Lambda)`. Its note names THIS form as the carrier of the collapse:
  the concrete Lean object "is built from `deltaJQuadFormCovFaithful`, whose subspace `V` is
  `ker(`the same `Q_1)`. The source object is indexed by the UNIT level with the FINE level
  integrated out."
* `compute/denotation_dict/DENOTATION_DICT.tsv` line 3, row `q_jstep_composite_Qj` (CMP99b p.393
  (3.15), `status = verified`, evidence `renders/bands/CMP99b_p393_pdf5_b0.png`). Its verdict is
  `lean_status = UNBUILT`, **not** `MISMATCH` — there is no Lean object for it to mismatch — and its
  note is: "No Lean object in the tree is a composite of `>1` averaging step for BOND fields." So the
  multi-step index of the source's `Q_j`, and hence of its `Δ_k`, has no carrier in this tree at all.
  (Recorded precisely because a relayed summary of this repair called that row `MISMATCH`; it is
  `UNBUILT`.)
* `Balaban/CovariantHjFaithful.lean`, the `[CSTAR-LEVEL-MISMATCH]` disclosure attached to the
  DEFINITION of `deltaJQuadFormCovFaithful` — a module this one imports transitively. It also names
  the typed separation that would make the collapse unstateable and is NOT used here:
  `Balaban.CStarLevelCorrected.LevelSplit` (with `LevelSplit.ne : S.fibre ≠ S.constr`).

**THREE FURTHER DIVERGENCES, beyond the level index, each read off the same verified rows.** The
level collapse is not the only gap between this form and (3.156), and a reader who fixed only the
level index would still not have the source's object:
1. **The minimand is the CURL ONLY.** `deltaJQuadFormCovFaithful` minimises `‖D_U A‖²` over the
   fibre. The source's fine operator is `Δ^η(U)`, and row `delta_fine_eta_U` (CMP99b p.392 (3.10),
   `lean_status = MISMATCH-DISCLOSED`) records its content as `⟨A,Δ A⟩ = ⟨A,D*D A⟩ + ⟨A,Δ' A⟩`. The
   `Δ'` half is absent here.
2. **No `−a⟨B,B⟩` counterterm.** Row `delta_k_unit_p428_3156`'s own denotation field is
   `⟨B,(Q G_1 Q*)^{-1} B⟩ − a⟨B,B⟩ − 2⟨H_1 D̃^{(2)}(B), J⟩ = ⟨B, Δ_k B⟩`. There is no `a`-term in
   this module.
3. **No `J`-term.** Same row: the `−2⟨H_1 D̃^{(2)}(B), J⟩` piece has no carrier here either.

**What the object IS, positively: a PULLBACK along `Q_ell`.** `deltaJQuadFormCovFaithful ell levels U`
is the pullback along `Q_ell` of a function of the unit-level datum: it depends on `A` only through
`Q_ell A`, and it is the LEAST fibre energy. Both halves are theorems, in
`Balaban/FaithfulMinimality.lean` — `deltaJ_isLeast_fibreEnergies` and `deltaJ_eq_of_same_fibre`.
(Cited by locator and NOT imported here: no proof in this module needs them, and adding an import
shifts the instance graph in files that neither import this one nor are imported by it — see
`compute/BUILD_STANDARDS.md` §PIN-INSTANCE.) "Pullback of a unit-level form along one averaging step"
is the honest description; "the source's `Δ_k`" is not.

**TWO DE-CORRELATED FAMILIES AGREE.** The `MISMATCH` verdict is not one lane's reading. A blind
prosecution in a different model family (Kimi K3, `compute/kimi_minswap/`, pinned to `a297d2eb`) read
(3.156) independently and formed its view BEFORE opening the denotation dictionary, then reached the
same conclusion: `Δ_k`'s arguments are `B` on both sides, unit-indexed, fine level integrated out,
with `(Q G_1 Q*)^{-1}` the Schur complement over the fibre `{A : QA = B}`.

**Consequence, stated plainly.** This is the standing NO-RG-LADDER position: no `Δ_k` ladder exists in
this tree, so every statement in this module is SINGLE-SCALE. `MinSwapSchurTarget` is this tree's
single-scale analogue of the (3.156) inequality; it is not that inequality, and a proof of it would
not by itself be a proof of the source's. -/
def MinSwapSchurTarget {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (γ : ℝ) : Prop :=
  ∀ A, A ∈ slice levels U → lineCoarseRestrictCovLM U ell A ∈ 𝒜 →
    γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A)
          (lineCoarseRestrictCovLM U ell A)
      ≤ deltaJQuadFormCovFaithful ell levels U A

/-- **THE MIN-SWAP, AS THE SEED PROMISED IT: total-space ⟹ Schur.** For every `ell`, `levels`, `U`,
`𝒜` and `γ`. No fibre, no infimum, no surjectivity hypothesis. -/
theorem MinSwapTotalTarget.toSchur {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (γ : ℝ)
    (h : MinSwapTotalTarget levels U 𝒜 γ) :
    MinSwapSchurTarget levels U 𝒜 γ :=
  fun A h1 h2 => minSwap_transfer levels U 𝒜
    (fun B => covCoarseBondInner B B) γ h A h1 h2

/-- **AND THE CONVERSE FAILS TO BE FREE** — the reverse implication is NOT proved here and is not
expected: `Δ_k ≤ ‖D_U ·‖²` (`CStarDeltaKCCoercive.deltaJQuadFormCovFaithful_le_dstarDQuadForm`) runs
the wrong way, so a Schur lower bound does not return a total-space lower bound pointwise. What §1's
`minSwap_iff` gives as an `↔` is the `sInf`-formulated Schur complement, a DIFFERENT object from
`deltaJQuadFormCovFaithful`. This is recorded so no consumer reads `toSchur` as an equivalence: the
tree-level statement is an IMPLICATION, and only that.

`MinSwapSchurTarget` is FALSE at `𝒜 = univ`, `U = 1`, every compatible `ell` and every `γ > 0`
(`minSwap_schur_on_bare_slice_refuted`), so `toSchur` is not vacuously true either: its hypothesis
is a genuinely restrictive statement about `𝒜`. -/
theorem MinSwapSchurTarget_univ_false {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (levels : List (KernelSubspace.Level L))
    [(deltaKernelImageCovH (trivialU L) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels (trivialU L)).HasOrthogonalProjection]
    {γ : ℝ} (hγ : 0 < γ) :
    ¬ MinSwapSchurTarget levels (trivialU L) (Set.univ : Set (CoarseBond L ell → SuTwo)) γ := by
  intro h
  exact minSwap_schur_on_bare_slice_refuted hell hdvd levels hγ
    fun A hA => h A hA (Set.mem_univ _)

/-! ## §9a — THE RAW TARGETS ARE VACUOUSLY INHABITED (six ways, as THEOREMS), AND THE GUARDED FORM

**CONVICTED 2026-07-29** by two de-correlated prosecutions of this module — a Claude family
(`compute/prosecute_minswap/ProbeVacuous.lean`) and a blind Kimi K3 family
(`compute/kimi_minswap/scratch/probe_vacuity.lean`, pinned to `a297d2eb`, mutation-tested). Both
compiled axiom-clean inhabitations of `MinSwapTotalTarget` / `MinSwapSchurTarget` carrying no
mathematical content, because neither `Prop` has any side condition INSIDE it. The module disclaimed
exactly this in PROSE — see "What this module does NOT claim", and the §1 NON-VACUITY WARNING already
named the mechanism ("if `n (Q A) = 0` for every `A ∈ S` with `Q A ∈ 𝒜`, the right-hand side
degenerates to `0 ≤ q A`") — but prose is not a type-checked obligation, and the §1 warning was never
applied to §9's LATTICE targets. That is the `Spine.FULL3DTarget` pattern verbatim.

**The vacuities are now THEOREMS IN THIS MODULE**, so they can never again be a footnote, and so any
future edit that claims to remove them has to make these declarations fail:

| # | degenerate instance | theorem | what fails |
|---|---|---|---|
| 1 | `𝒜 = ∅`, ANY `γ` | `MinSwapTotalTarget_holds_at_empty_class` | domain empty |
| 2 | `γ ≤ 0`, ANY `𝒜` incl. `univ` | `MinSwapTotalTarget_holds_of_gamma_nonpos` | LHS `≤ 0 ≤` RHS |
| 3 | `𝒜 = {0}`, ANY `γ` incl. `γ > 0` | `MinSwapTotalTarget_holds_at_zero_class` | LHS `≡ γ·0` |
| 4 | any `𝒜` missing `Q_ell(slice)` | `MinSwapTotalTarget_holds_of_class_misses_image` | domain empty |
| 5 | `ell = 0`, `𝒜` NONEMPTY with POSITIVE weight | `MinSwapTotalTarget_holds_at_ell_zero_const_class` | `Q_0 ≡ 0` |
| 6 | each of 1–5, transported to the Schur target | the `MinSwapSchurTarget_*` twins | same |

Instance 3 is the one that kills the obvious repair: `𝒜 = {0}` is NONEMPTY, its quantifier domain is
INHABITED (`zero_field_in_domain_of_zero_class`: the zero field is in the slice with shadow `0`), and
the target still holds for every `γ`, however large. So the defect is **vacuity-by-always-zero-LHS**,
not vacuity-by-empty-domain, and a guard of `0 < γ ∧ 𝒜.Nonempty` PASSES instances 3, 4 and 5. That
guard is not a repair, and it is not the guard added below.

**WHY THE GUARD BELOW IS THE RIGHT ONE.** What has to be excluded is a class on which the unit-level
WEIGHT vanishes identically over the domain. The weakest condition that names the weight is
`∃ B ∈ 𝒜, 0 < n B`; that is still NOT enough, and instance 5 is the proof — there `𝒜` is a nonempty
singleton whose one member has strictly positive coarse energy, and the target is still content-free,
because that member is not the shadow of ANY slice element. The condition has to be about the DOMAIN,
not about `𝒜` alone:

  **there is a slice element whose unit shadow is admissible AND has positive coarse energy.**

That single clause implies `0 < γ` is meaningful, implies `𝒜.Nonempty`, kills instance 3 (a shadow in
`{0}` has zero energy), kills instance 4 and instance 5 (no slice element has an admissible shadow),
and kills `ell = 0` outright (`Q_0 ≡ 0`, so no shadow has positive energy —
`not_MinSwapTotalTargetNV_ell_zero`). So the guarded target needs NEITHER a `0 < ell` hypothesis NOR
the torus divisibility hypothesis `ell ∣ L μ + 1`: a witness-form guard is self-certifying about the
geometry, because where the geometry degenerates the guard becomes UNSATISFIABLE rather than silently
true. That is the whole reason to state the guard as a witness rather than as a hypothesis on `ell`.

**The witness is an EXPLICIT PARAMETER `A₀`, not an `∃`.** No `∃` and no `Nonempty` is introduced
anywhere (so no `formal/S91_REGISTRY.tsv` row is required, and nothing hands a prover a free datum);
the witness is visible in the statement of every consumer instead of being chosen inside a proof.

**WHY THE RAW `Prop`s ARE NOT SIMPLY EDITED — a write-scope fact, not a preference.**
`Balaban/MinSwapComposition.lean` proves `MinSwap.MinSwapTotalTarget` and `MinSwap.MinSwapSchurTarget`
in TERM MODE, in `composed_MinSwapTotalTarget` and `composed_MinSwapSchurTarget` (cited BY DECLARATION
NAME on purpose: that module is under concurrent edit and a line range goes stale within minutes — an
earlier draft of this docstring cited `:970-1000` and the declarations had already moved to `:1031`
and `:1048` by commit `05169664`), and is owned by another lane. Adding a conjunct to the raw
bodies breaks those two proofs, and that module cannot supply the guard: its hypothesis on the class is
`𝒜 ⊆ …`, which `∅` satisfies. `MinSwapTotalTarget.toNV` below is the bridge, and it states exactly
what such a producer must ADD to reach a non-vacuous statement — a slice element whose unit shadow is
admissible with positive coarse energy. Flipping the raw `Prop`s is a coordinated cross-module edit and
is not performed here. -/

/-- The coarse energy of the ZERO coarse field is `0`. (Kimi's probe carries the same lemma in its own
scratch scope; it is not in the tree, so it is proved here rather than cited.) -/
theorem covCoarseBondInner_zero_eq_zero {ell : ℕ} :
    covCoarseBondInner (0 : CoarseBond L ell → SuTwo) 0 = 0 := by
  rw [covCoarseBondInner_self_eq_sum]
  simp

/-- **VACUITY 1 — `𝒜 = ∅`, EVERY `γ`.** Strictly stronger than the prosecutor's probe, which fixed
`γ = 1000000`: this covers every real `γ`, negative included, with no hypothesis on `ell`, `levels`,
`U` or `γ`. -/
theorem MinSwapTotalTarget_holds_at_empty_class {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] (γ : ℝ) :
    MinSwapTotalTarget levels U (∅ : Set (CoarseBond L ell → SuTwo)) γ :=
  fun _ _ hmem => absurd hmem (Set.notMem_empty _)

/-- **VACUITY 2 — `γ ≤ 0`, EVERY class including `univ`.** Strictly stronger than Kimi's `γ = 0`
probe. The left side is `≤ 0` and the curl energy is `≥ 0`. -/
theorem MinSwapTotalTarget_holds_of_gamma_nonpos {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) {γ : ℝ} (hγ : γ ≤ 0) :
    MinSwapTotalTarget levels U 𝒜 γ := by
  intro A _ _
  exact le_trans (mul_nonpos_of_nonpos_of_nonneg hγ (covCoarseBondInner_self_nonneg _))
    (dstarDQuadForm_nonneg U A)

/-- **VACUITY 3 — `𝒜 = {0}`, EVERY `γ`, `γ > 0` INCLUDED.** THE strong one: the class is NONEMPTY,
the quantifier domain is INHABITED (`zero_field_in_domain_of_zero_class`), and the statement still
carries no coercivity content, because the only admissible shadow has zero coarse energy. -/
theorem MinSwapTotalTarget_holds_at_zero_class {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] (γ : ℝ) :
    MinSwapTotalTarget levels U ({0} : Set (CoarseBond L ell → SuTwo)) γ := by
  intro A _ hmem
  rw [Set.mem_singleton_iff] at hmem
  rw [hmem, covCoarseBondInner_zero_eq_zero, mul_zero]
  exact dstarDQuadForm_nonneg U A

/-- The `𝒜 = {0}` vacuity is NOT vacuity-by-empty-domain: the zero bond field is in the slice for
every `levels` and `U`, and its unit shadow is `0 ∈ {0}`. -/
theorem zero_field_in_domain_of_zero_class {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] :
    (0 : Bond L → SuTwo) ∈ slice levels U ∧
      lineCoarseRestrictCovLM U ell (0 : Bond L → SuTwo)
        ∈ ({0} : Set (CoarseBond L ell → SuTwo)) :=
  ⟨by show RcovLM U levels (gradCovariantAdjointLM U 0) = 0
      rw [map_zero, map_zero],
    by rw [map_zero]; rfl⟩

/-- **VACUITY 4 — any class DISJOINT from the shadow of the slice.** Covers instance 1 (`𝒜 = ∅`) and
instance 5 (`ell = 0`) as special cases, and shows that `𝒜.Nonempty` is orthogonal to the defect. -/
theorem MinSwapTotalTarget_holds_of_class_misses_image {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (γ : ℝ)
    (hmiss : ∀ A, A ∈ slice levels U → lineCoarseRestrictCovLM U ell A ∉ 𝒜) :
    MinSwapTotalTarget levels U 𝒜 γ :=
  fun A hA hmem => absurd hmem (hmiss A hA)

/-- **`Q_0 ≡ 0`.** At `ell = 0` the normalization is `1 / (0:ℝ)^4 = 0`, so the faithful covariant
average annihilates every field. `CoarseBond L 0` is NOT empty (`zeroSite_mem_CoarseLattice 0`), so
this is a genuine collapse of the operator, not an empty-type artifact. -/
theorem lineCoarseRestrictCovLM_ell_zero
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    lineCoarseRestrictCovLM U 0 A = 0 := by
  funext b
  rw [lineCoarseRestrictCovLM_apply, Pi.zero_apply]
  unfold lineCoarseRestrictCov
  simp

/-- **VACUITY 5 — the `∃ B ∈ 𝒜, 0 < n B` GUARD IS NOT ENOUGH, and here is the compiled proof.** At
`ell = 0`, take `𝒜 = {the constant coarse field suTwoWitness}`. It is NONEMPTY; its one member has
STRICTLY POSITIVE coarse energy (`covCoarseBondInner_const_pos`); and the target still holds for
EVERY `γ`, however large — because `Q_0` annihilates the slice, so that member is the shadow of
nothing. A guard phrased on `𝒜` alone cannot see this; the witness guard of `MinSwapTotalTargetNV`
does, and `not_MinSwapTotalTargetNV_ell_zero` proves it does. -/
theorem MinSwapTotalTarget_holds_at_ell_zero_const_class
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection] (γ : ℝ) :
    MinSwapTotalTarget levels U
      ({fun _ : CoarseBond L 0 => suTwoWitness} : Set (CoarseBond L 0 → SuTwo)) γ := by
  refine MinSwapTotalTarget_holds_of_class_misses_image levels U _ γ ?_
  intro A _ hmem
  rw [Set.mem_singleton_iff, lineCoarseRestrictCovLM_ell_zero] at hmem
  exact const_coarse_ne_zero suTwoWitness_ne_zero hmem.symm

/-- The `ell = 0` class of VACUITY 5 is nonempty and its member has strictly positive coarse energy —
so the two conditions a class-only guard could impose are both SATISFIED there. -/
theorem ell_zero_const_class_nonempty_with_positive_weight :
    ({fun _ : CoarseBond L 0 => suTwoWitness} : Set (CoarseBond L 0 → SuTwo)).Nonempty ∧
      0 < covCoarseBondInner (fun _ : CoarseBond L 0 => suTwoWitness)
            (fun _ : CoarseBond L 0 => suTwoWitness) :=
  ⟨⟨_, rfl⟩, covCoarseBondInner_const_pos suTwoWitness_ne_zero⟩

/-- **VACUITY 6 — every one of 1–5 transports to the Schur target.** Stated once, as an implication
from the total target, which is exactly `MinSwapTotalTarget.toSchur`; the named twins below are the
four instances a future edit has to break. -/
theorem MinSwapSchurTarget_holds_at_empty_class {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection] (γ : ℝ) :
    MinSwapSchurTarget levels U (∅ : Set (CoarseBond L ell → SuTwo)) γ :=
  MinSwapTotalTarget.toSchur levels U ∅ γ (MinSwapTotalTarget_holds_at_empty_class levels U γ)

theorem MinSwapSchurTarget_holds_of_gamma_nonpos {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) {γ : ℝ} (hγ : γ ≤ 0) :
    MinSwapSchurTarget levels U 𝒜 γ :=
  MinSwapTotalTarget.toSchur levels U 𝒜 γ
    (MinSwapTotalTarget_holds_of_gamma_nonpos levels U 𝒜 hγ)

theorem MinSwapSchurTarget_holds_at_zero_class {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection] (γ : ℝ) :
    MinSwapSchurTarget levels U ({0} : Set (CoarseBond L ell → SuTwo)) γ :=
  MinSwapTotalTarget.toSchur levels U {0} γ (MinSwapTotalTarget_holds_at_zero_class levels U γ)

theorem MinSwapSchurTarget_holds_of_class_misses_image {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (γ : ℝ)
    (hmiss : ∀ A, A ∈ slice levels U → lineCoarseRestrictCovLM U ell A ∉ 𝒜) :
    MinSwapSchurTarget levels U 𝒜 γ :=
  MinSwapTotalTarget.toSchur levels U 𝒜 γ
    (MinSwapTotalTarget_holds_of_class_misses_image levels U 𝒜 γ hmiss)

theorem MinSwapSchurTarget_holds_at_ell_zero_const_class
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 0 levels U).HasOrthogonalProjection] (γ : ℝ) :
    MinSwapSchurTarget levels U
      ({fun _ : CoarseBond L 0 => suTwoWitness} : Set (CoarseBond L 0 → SuTwo)) γ :=
  MinSwapTotalTarget.toSchur levels U _ γ
    (MinSwapTotalTarget_holds_at_ell_zero_const_class levels U γ)

/-! ### §9a.2 — the GUARDED targets -/

/-- **THE GUARDED MIN-SWAP TOTAL-SPACE TARGET.** The raw target of §9 CONJOINED with the guard that
`A₀` is a slice element whose unit shadow is admissible and has STRICTLY POSITIVE coarse energy, and
that `γ > 0`. `A₀` is an explicit parameter, so there is no `∃` and no free datum.

By construction this `Prop` implies `0 < γ · n(Q_ell A₀) ≤ ‖D_U A₀‖²` (`MinSwapTotalTargetNV.lhs_pos`)
— a lower bound with a STRICTLY POSITIVE left-hand side at a named point. That is the property the raw
target lacks, and it is what rules out all six vacuities of §9a. -/
def MinSwapTotalTargetNV {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (γ : ℝ) (A₀ : Bond L → SuTwo) : Prop :=
  0 < γ ∧ A₀ ∈ slice levels U ∧ lineCoarseRestrictCovLM U ell A₀ ∈ 𝒜 ∧
    0 < covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
          (lineCoarseRestrictCovLM U ell A₀) ∧
    MinSwapTotalTarget levels U 𝒜 γ

/-- **THE GUARDED SCHUR TARGET** — same guard, against `deltaJQuadFormCovFaithful`. See the
denotation qualification on `MinSwapSchurTarget`: this is a SINGLE-SCALE statement about this tree's
pullback form, not about CMP99b (3.156)'s `Δ_k`. -/
def MinSwapSchurTargetNV {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (γ : ℝ) (A₀ : Bond L → SuTwo) : Prop :=
  0 < γ ∧ A₀ ∈ slice levels U ∧ lineCoarseRestrictCovLM U ell A₀ ∈ 𝒜 ∧
    0 < covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
          (lineCoarseRestrictCovLM U ell A₀) ∧
    MinSwapSchurTarget levels U 𝒜 γ

/-- **THE GUARD DOES WHAT IT CLAIMS.** The guarded target forces a STRICTLY POSITIVE left-hand side at
its own witness, hence also `0 < ‖D_U A₀‖²`. No instance of §9a's table can satisfy this. -/
theorem MinSwapTotalTargetNV.lhs_pos {ell : ℕ} {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {𝒜 : Set (CoarseBond L ell → SuTwo)} {γ : ℝ} {A₀ : Bond L → SuTwo}
    (h : MinSwapTotalTargetNV levels U 𝒜 γ A₀) :
    0 < γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
          (lineCoarseRestrictCovLM U ell A₀) ∧
      γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
            (lineCoarseRestrictCovLM U ell A₀)
        ≤ dstarDQuadForm U A₀ ∧
      0 < dstarDQuadForm U A₀ := by
  obtain ⟨hγ, hA₀, hmem, hc, htot⟩ := h
  have hlhs : 0 < γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
      (lineCoarseRestrictCovLM U ell A₀) := mul_pos hγ hc
  exact ⟨hlhs, htot A₀ hA₀ hmem, lt_of_lt_of_le hlhs (htot A₀ hA₀ hmem)⟩

/-- **THE BRIDGE.** What a producer of the RAW target must ADD to reach the guarded one. This is the
patch `Balaban/MinSwapComposition.lean` needs, stated here so it needs no edit to this module. -/
theorem MinSwapTotalTarget.toNV {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) {γ : ℝ} (hγ : 0 < γ) (A₀ : Bond L → SuTwo)
    (hA₀ : A₀ ∈ slice levels U) (hmem : lineCoarseRestrictCovLM U ell A₀ ∈ 𝒜)
    (hc : 0 < covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
            (lineCoarseRestrictCovLM U ell A₀))
    (h : MinSwapTotalTarget levels U 𝒜 γ) :
    MinSwapTotalTargetNV levels U 𝒜 γ A₀ :=
  ⟨hγ, hA₀, hmem, hc, h⟩

/-- The guarded target still yields the raw one — nothing is lost by strengthening. -/
theorem MinSwapTotalTargetNV.toRaw {ell : ℕ} {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    {𝒜 : Set (CoarseBond L ell → SuTwo)} {γ : ℝ} {A₀ : Bond L → SuTwo}
    (h : MinSwapTotalTargetNV levels U 𝒜 γ A₀) : MinSwapTotalTarget levels U 𝒜 γ := h.2.2.2.2

/-- **THE MIN-SWAP, GUARDED: total-space ⟹ Schur, guard and witness carried through.** -/
theorem MinSwapTotalTargetNV.toSchur {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (γ : ℝ) (A₀ : Bond L → SuTwo)
    (h : MinSwapTotalTargetNV levels U 𝒜 γ A₀) :
    MinSwapSchurTargetNV levels U 𝒜 γ A₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    MinSwapTotalTarget.toSchur levels U 𝒜 γ h.2.2.2.2⟩

/-- **THE BRIDGE, SCHUR SIDE.** The twin of `MinSwapTotalTarget.toNV`: what a producer of the RAW
Schur target must ADD to reach the guarded Schur target. Needed by a consumer that already holds
`MinSwapSchurTarget` directly (e.g. one that proved it through `minSwap_transfer` rather than through
`MinSwapTotalTarget`) and therefore cannot route through `MinSwapTotalTargetNV.toSchur`.

The guard components are the SAME four as on the total side — `A₀` explicit, no `∃` — so nothing
about the denotation qualification on `MinSwapSchurTarget` changes: this is a statement about this
tree's single-scale pullback form, not about CMP99b (3.156)'s `Δ_k`. -/
theorem MinSwapSchurTarget.toNV {ell : ℕ} (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) {γ : ℝ} (hγ : 0 < γ) (A₀ : Bond L → SuTwo)
    (hA₀ : A₀ ∈ slice levels U) (hmem : lineCoarseRestrictCovLM U ell A₀ ∈ 𝒜)
    (hc : 0 < covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
            (lineCoarseRestrictCovLM U ell A₀))
    (h : MinSwapSchurTarget levels U 𝒜 γ) :
    MinSwapSchurTargetNV levels U 𝒜 γ A₀ :=
  ⟨hγ, hA₀, hmem, hc, h⟩

/-- The guarded Schur target still yields the raw one — the twin of `MinSwapTotalTargetNV.toRaw`. -/
theorem MinSwapSchurTargetNV.toRaw {ell : ℕ} {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    {𝒜 : Set (CoarseBond L ell → SuTwo)} {γ : ℝ} {A₀ : Bond L → SuTwo}
    (h : MinSwapSchurTargetNV levels U 𝒜 γ A₀) : MinSwapSchurTarget levels U 𝒜 γ := h.2.2.2.2

/-- **THE GUARD DOES WHAT IT CLAIMS, SCHUR SIDE.** The twin of `MinSwapTotalTargetNV.lhs_pos`: the
guarded Schur target forces a STRICTLY POSITIVE left-hand side at its own witness, hence also
`0 < Δ_k A₀` for this tree's pullback form. No instance of §9a's table can satisfy this. -/
theorem MinSwapSchurTargetNV.lhs_pos {ell : ℕ} {levels : List (KernelSubspace.Level L)}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    {𝒜 : Set (CoarseBond L ell → SuTwo)} {γ : ℝ} {A₀ : Bond L → SuTwo}
    (h : MinSwapSchurTargetNV levels U 𝒜 γ A₀) :
    0 < γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
          (lineCoarseRestrictCovLM U ell A₀) ∧
      γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
            (lineCoarseRestrictCovLM U ell A₀)
        ≤ deltaJQuadFormCovFaithful ell levels U A₀ ∧
      0 < deltaJQuadFormCovFaithful ell levels U A₀ := by
  obtain ⟨hγ, hA₀, hmem, hc, hsch⟩ := h
  have hlhs : 0 < γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
      (lineCoarseRestrictCovLM U ell A₀) := mul_pos hγ hc
  exact ⟨hlhs, hsch A₀ hA₀ hmem, lt_of_lt_of_le hlhs (hsch A₀ hA₀ hmem)⟩

/-! ### §9a.3 — REGRESSION: every §9a vacuity FAILS to inhabit the guarded target

Each theorem below is the exact negation of one row of §9a's table. Together they are the proof that
the guard is not cosmetic: the compiled vacuous inhabitations cannot be retyped against
`MinSwapTotalTargetNV` / `MinSwapSchurTargetNV`.

**The must-fire / must-not-fire pair is on disk, not asserted.** `compute/minswap_repair/` carries
THREE expected-fail probes — `EXPECTED_FAIL_1_empty_class.lean` (the prosecutor's verbatim `𝒜 = ∅`
term), `EXPECTED_FAIL_2_zero_class.lean` (Kimi's `𝒜 = {0}` instance, with EVERY guard component
supplied honestly except the weight, which reduces to `(0:ℝ) < 0`), `EXPECTED_FAIL_3_gamma_zero.lean`
(`γ = 0` on `univ`) — each of which MUST NOT compile, with the error text recorded in
`expected_fail.log`; and `probe_pos_control.lean`, which MUST compile and certifies that the raw
targets were NOT weakened (the vacuous terms still inhabit them) and that the guarded target is usable
off-module. Vacuities 4 and 5 have no separate probe file because their negations
(`not_MinSwapTotalTargetNV_of_class_misses_image`, `not_MinSwapTotalTargetNV_ell_zero`) are stated
below at full generality, which is strictly stronger than a single failing term. -/

/-- REGRESSION vs VACUITY 1: `𝒜 = ∅` cannot inhabit the guarded target, for ANY `γ` and ANY
witness — the witness's shadow would have to be a member of `∅`. -/
theorem not_MinSwapTotalTargetNV_empty_class {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (γ : ℝ) (A₀ : Bond L → SuTwo) :
    ¬ MinSwapTotalTargetNV levels U (∅ : Set (CoarseBond L ell → SuTwo)) γ A₀ :=
  fun h => absurd h.2.2.1 (Set.notMem_empty _)

/-- REGRESSION vs VACUITY 2: `γ ≤ 0` cannot inhabit the guarded target, for ANY class. -/
theorem not_MinSwapTotalTargetNV_of_gamma_nonpos {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) {γ : ℝ} (hγ : γ ≤ 0) (A₀ : Bond L → SuTwo) :
    ¬ MinSwapTotalTargetNV levels U 𝒜 γ A₀ :=
  fun h => absurd h.1 (not_lt.mpr hγ)

/-- **REGRESSION vs VACUITY 3 — the one that matters.** `𝒜 = {0}` is nonempty with an inhabited
domain, and it still cannot inhabit the guarded target for ANY `γ`, because the only admissible shadow
has ZERO coarse energy. This is the check that a `0 < γ ∧ 𝒜.Nonempty` guard would fail. -/
theorem not_MinSwapTotalTargetNV_zero_class {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (γ : ℝ) (A₀ : Bond L → SuTwo) :
    ¬ MinSwapTotalTargetNV levels U ({0} : Set (CoarseBond L ell → SuTwo)) γ A₀ := by
  intro h
  obtain ⟨-, -, hmem, hc, -⟩ := h
  rw [Set.mem_singleton_iff] at hmem
  rw [hmem, covCoarseBondInner_zero_eq_zero] at hc
  exact absurd hc (lt_irrefl 0)

/-- REGRESSION vs VACUITY 4: a class disjoint from the shadow of the slice cannot inhabit the guarded
target — the guard demands a slice element with an admissible shadow. -/
theorem not_MinSwapTotalTargetNV_of_class_misses_image {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) (γ : ℝ) (A₀ : Bond L → SuTwo)
    (hmiss : ∀ A, A ∈ slice levels U → lineCoarseRestrictCovLM U ell A ∉ 𝒜) :
    ¬ MinSwapTotalTargetNV levels U 𝒜 γ A₀ :=
  fun h => absurd h.2.2.1 (hmiss A₀ h.2.1)

/-- **REGRESSION vs VACUITY 5 / the `ell = 0` question.** At `ell = 0` the guarded target is
UNINHABITABLE for EVERY class (including the nonempty positive-weight class of VACUITY 5), every `γ`
and every witness, because `Q_0 ≡ 0` has zero coarse energy. So the guard needs no `0 < ell`
hypothesis: it already implies it wherever `Q_ell` degenerates. -/
theorem not_MinSwapTotalTargetNV_ell_zero
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L 0 → SuTwo)) (γ : ℝ) (A₀ : Bond L → SuTwo) :
    ¬ MinSwapTotalTargetNV levels U 𝒜 γ A₀ := by
  intro h
  obtain ⟨-, -, -, hc, -⟩ := h
  rw [lineCoarseRestrictCovLM_ell_zero, covCoarseBondInner_zero_eq_zero] at hc
  exact absurd hc (lt_irrefl 0)

/-- REGRESSION vs VACUITY 6: the Schur guard rejects the same five instances. Stated as the single
fact that carries all of them — the guarded Schur target has the SAME guard, so any of the five
arguments above applies verbatim; `𝒜 = ∅` and `𝒜 = {0}` are spelled out because those are the two the
prosecutors compiled against the Schur side directly. -/
theorem not_MinSwapSchurTargetNV_empty_class {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (γ : ℝ) (A₀ : Bond L → SuTwo) :
    ¬ MinSwapSchurTargetNV levels U (∅ : Set (CoarseBond L ell → SuTwo)) γ A₀ :=
  fun h => absurd h.2.2.1 (Set.notMem_empty _)

theorem not_MinSwapSchurTargetNV_zero_class {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (γ : ℝ) (A₀ : Bond L → SuTwo) :
    ¬ MinSwapSchurTargetNV levels U ({0} : Set (CoarseBond L ell → SuTwo)) γ A₀ := by
  intro h
  obtain ⟨-, -, hmem, hc, -⟩ := h
  rw [Set.mem_singleton_iff] at hmem
  rw [hmem, covCoarseBondInner_zero_eq_zero] at hc
  exact absurd hc (lt_irrefl 0)

theorem not_MinSwapSchurTargetNV_of_gamma_nonpos {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (𝒜 : Set (CoarseBond L ell → SuTwo)) {γ : ℝ} (hγ : γ ≤ 0) (A₀ : Bond L → SuTwo) :
    ¬ MinSwapSchurTargetNV levels U 𝒜 γ A₀ :=
  fun h => absurd h.1 (not_lt.mpr hγ)

/-! ### §9a.4 — A GUARD THAT NOTHING SATISFIES IS ALSO NOT A REPAIR: the SHARP singleton instance

The generic tool for inhabiting the guarded target NON-vacuously. At a singleton class `{Q_ell A₀}`
the sharp constant is `γ* = ‖D_U A₀‖² / n(Q_ell A₀)`, and the guarded target holds at `γ*` and FAILS
for every `γ > γ*`. So on such a class the guarded target is a genuine, two-sided constraint on `γ`,
not a triviality. `hmin` is exactly the Schur-minimality of `A₀` in its own fibre — the honest price
of non-vacuity, made visible as a hypothesis rather than hidden. -/

/-- **THE GUARDED TARGET HOLDS AT THE SHARP CONSTANT of a singleton class.** -/
theorem MinSwapTotalTargetNV_singleton_at_sharp_gamma {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (A₀ : Bond L → SuTwo) (hA₀ : A₀ ∈ slice levels U)
    (hc : 0 < covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
            (lineCoarseRestrictCovLM U ell A₀))
    (hpos : 0 < dstarDQuadForm U A₀)
    (hmin : ∀ A, A ∈ slice levels U →
      lineCoarseRestrictCovLM U ell A = lineCoarseRestrictCovLM U ell A₀ →
      dstarDQuadForm U A₀ ≤ dstarDQuadForm U A) :
    MinSwapTotalTargetNV levels U
      ({lineCoarseRestrictCovLM U ell A₀} : Set (CoarseBond L ell → SuTwo))
      (dstarDQuadForm U A₀ / covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
        (lineCoarseRestrictCovLM U ell A₀)) A₀ := by
  refine ⟨div_pos hpos hc, hA₀, rfl, hc, ?_⟩
  intro A hA hmem
  rw [Set.mem_singleton_iff] at hmem
  rw [hmem, div_mul_cancel₀ _ (ne_of_gt hc)]
  exact hmin A hA hmem

/-- **AND IT FAILS ABOVE THE SHARP CONSTANT** — so the guarded target on a singleton class is a real
constraint on `γ`, with no `hmin` hypothesis needed (the positivity comes from the guard itself). -/
theorem not_MinSwapTotalTargetNV_singleton_above_sharp {ell : ℕ}
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    (A₀ : Bond L → SuTwo) {γ : ℝ}
    (hγ : dstarDQuadForm U A₀ / covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
            (lineCoarseRestrictCovLM U ell A₀) < γ) :
    ¬ MinSwapTotalTargetNV levels U
        ({lineCoarseRestrictCovLM U ell A₀} : Set (CoarseBond L ell → SuTwo)) γ A₀ := by
  intro h
  obtain ⟨-, hA₀, hmem, hc, htot⟩ := h
  have h1 := htot A₀ hA₀ hmem
  have h2 : dstarDQuadForm U A₀ < γ * covCoarseBondInner (lineCoarseRestrictCovLM U ell A₀)
      (lineCoarseRestrictCovLM U ell A₀) := (div_lt_iff₀ hc).mp hγ
  linarith

/-! ## §10 — a second datum in the domain, with NONZERO unit shadow, that is not a zero mode

§7's witness (the constant field) inhabits the domain but is exactly §6's refuting datum, so on its
own it leaves open whether anything SURVIVES the forced exclusion of §8. At `ell = 1`,
`Q_1(U) = id` for every `U` (`RegularUGamma0.lineCoarseRestrictCov_one_eq_self`), and
`NilLevelTarget.loopField` is divergence-free at `U = 1`, so it lies in the slice for every `levels`
with unit shadow `≠ 0`.

`ell = 1` IS degenerate as a renormalisation step — at `ell = 1` the constraint subspace is `⊥`
(`CovariantHjFaithful.gaugeConstraintSubspaceCovFaithful_ell1_eq_bot`) and `Δ_k` collapses to the
bare curl energy. It is stated anyway because non-vacuity of a quantifier DOMAIN is a statement about
the domain, and this is the cheapest honest point in it that is not a harmonic zero mode. The
general-`ell` analogue is NOT delivered here (see the module's closing note). -/

/-- **THE LOOP HAS NONZERO UNIT SHADOW AT `ell = 1`** — evaluated at its own base bond `(pA, 1)`,
where it equals `suTwoWitness ≠ 0`. Contrast `loopField_unit_shadow_eq_zero`: the shadow vanishes at
`ell = wEll m ≥ 3` (the loop is smaller than a block) and does NOT vanish at `ell = 1`. -/
theorem loopField_unit_shadow_ne_zero_ell_one (m : ℕ) :
    lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
      (NilLevelTarget.loopField m) ≠ 0 := by
  intro h
  have hy : NilLevelTarget.pA m ∈ CoarseLattice (WitnessInequality.wExt m) 1 :=
    CovariantHjMinimizer.mem_CoarseLattice_one _
  have hc := congrFun h ((⟨NilLevelTarget.pA m, hy⟩, 1) :
    CoarseBond (WitnessInequality.wExt m) 1)
  rw [lineCoarseRestrictCovLM_apply,
    RegularUGamma0.lineCoarseRestrictCov_one_eq_self (trivialU (WitnessInequality.wExt m))
      (NilLevelTarget.loopField m),
    NilLevelTarget.loopField_at_pA_one m] at hc
  exact suTwoWitness_ne_zero hc

/-- The loop lies in the gauge slice, for every `levels`, at `U = 1` — its divergence itself
vanishes (`NilLevelTarget.loopField_div_eq_zero`). -/
theorem loopField_mem_slice (m : ℕ)
    (levels : List (KernelSubspace.Level (WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (WitnessInequality.wExt m)) levels).HasOrthogonalProjection] :
    NilLevelTarget.loopField m ∈ slice levels (trivialU (WitnessInequality.wExt m)) := by
  show RcovLM (trivialU (WitnessInequality.wExt m)) levels
    (gradCovariantAdjointLM (trivialU (WitnessInequality.wExt m))
      (NilLevelTarget.loopField m)) = 0
  rw [NilLevelTarget.loopField_div_eq_zero m, map_zero]

/-- **THE DOMAIN CONTAINS A DATUM WITH POSITIVE LEFT-HAND SIDE AT `ell = 1`.** Stated at the explicit
witness (no `∃`, no free datum). -/
theorem minSwap_domain_positive_lhs_ell_one (m : ℕ)
    (levels : List (KernelSubspace.Level (WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (WitnessInequality.wExt m)) levels).HasOrthogonalProjection] :
    NilLevelTarget.loopField m ∈ slice levels (trivialU (WitnessInequality.wExt m)) ∧
    0 < covCoarseBondInner
        (lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
          (NilLevelTarget.loopField m))
        (lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
          (NilLevelTarget.loopField m)) :=
  ⟨loopField_mem_slice m levels,
    covCoarseBondInner_pos_of_ne_zero (loopField_unit_shadow_ne_zero_ell_one m)⟩

/-- **THE LOOP IS NOT COVARIANT-CURL-FREE, as an operator statement.** The `LinearMap`-level form of
`TransverseClass.loopField_curl_ne_zero` (which is stated pointwise, at the plaquette `loopPlaq m`):
a function is nonzero as soon as it is nonzero at one point. REUSED, not re-proved (LAW-19) — the
`4·suTwoWitness` computation lives in `TransverseClass.lean` §6. -/
theorem loopField_curlLM_ne_zero (m : ℕ) :
    curlCovariantLM (trivialU (WitnessInequality.wExt m)) (NilLevelTarget.loopField m) ≠ 0 := by
  intro h
  refine TransverseClass.loopField_curl_ne_zero m ?_
  have hc := congrFun h (TransverseClass.loopPlaq m)
  rwa [Pi.zero_apply] at hc

/-- **AND IT IS NOT A ZERO MODE** — the loop is not covariant-curl-free, so the datum of
`minSwap_domain_positive_lhs_ell_one` is outside the class §8 forces the admissible set to exclude.

**No hypothesis.** Until 2026-07-29 this theorem carried `hcurl` as an explicit hypothesis, because
`TransverseClass.lean` was under concurrent edit when this module was written (write-scope isolation,
LAW-4) and re-proving its `4·suTwoWitness` computation here would have duplicated a landed proof
(LAW-19). `TransverseClass.lean` is now imported and the hypothesis is DISCHARGED by
`loopField_curlLM_ne_zero` above. -/
theorem minSwap_domain_non_curlFree_ell_one (m : ℕ)
    (levels : List (KernelSubspace.Level (WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (WitnessInequality.wExt m)) levels).HasOrthogonalProjection] :
    NilLevelTarget.loopField m ∈ slice levels (trivialU (WitnessInequality.wExt m)) ∧
    lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
      (NilLevelTarget.loopField m) ≠ 0 ∧
    curlCovariantLM (trivialU (WitnessInequality.wExt m)) (NilLevelTarget.loopField m) ≠ 0 :=
  ⟨loopField_mem_slice m levels, loopField_unit_shadow_ne_zero_ell_one m,
    loopField_curlLM_ne_zero m⟩

/-! ## §10a — THE GUARDED TARGET IS NON-VACUOUSLY INHABITED, CONCRETELY (`ell = 1`)

§9a's guard is worth nothing if NOTHING satisfies it — a guard that makes the target unsatisfiable is
not a repair either. This section discharges that, with no hypotheses beyond the ambient
`HasOrthogonalProjection` instances, at the `ell = 1` loop datum of §10:

* `minSwap_guarded_holds_at_sharp_gamma_ell_one` — `MinSwapTotalTargetNV` HOLDS, at the explicit
  constant `sharpGammaLoopEllOne m > 0`, on the explicit nonempty class
  `{Q_1(loopField m)}`, with witness `loopField m`.
* `minSwap_guarded_lhs_pos_ell_one` — at that instance the left-hand side is STRICTLY POSITIVE, so
  none of §9a's six vacuities is what is being satisfied.
* `not_minSwap_guarded_above_sharp_gamma_ell_one` — and it FAILS for every `γ` above the sharp
  constant. So the guarded target here is a two-sided constraint on `γ`: satisfied at `γ*`, refuted
  above it. That is the difference between content and vacuity, as a pair of theorems.
* `witnessClass_ell_one_not_excluded` — and §8's FORCED exclusion does not empty this class: every
  slice element with an admissible shadow is non-curl-free. So the instance is not smuggled past §8.
* `minSwap_guarded_schur_holds_at_sharp_gamma_ell_one` — all of it transports to the guarded SCHUR
  target through `MinSwapTotalTargetNV.toSchur`.

**TWO DISCLOSURES, both of which a prosecutor should press.**

1. **`ell = 1` is a DEGENERATE renormalisation step** — at `ell = 1` the constraint subspace is `⊥`
   (`CovariantHjFaithful.gaugeConstraintSubspaceCovFaithful_ell1_eq_bot`) and the Schur form collapses
   to the bare curl energy, exactly as §10 already discloses for its own witness. So this section
   establishes that the GUARD IS SATISFIABLE, not that it is satisfiable at a non-degenerate scale.
2. **A general-`ell` analogue exists but CANNOT be cited here.** `Balaban/MinSwapWitness.lean`
   (`shear_survives_forced_exclusion_general`, `witnessClass_not_excluded`) builds the transverse-shear
   witness at general `ell`, and it IMPORTS this module — citing it here would be an import cycle. The
   general-`ell` guarded instance therefore belongs in that module or a later one, composed through
   `MinSwapTotalTarget.toNV`; it is not deliverable from inside this file. `witnessClass_ell_one_not_excluded`
   below is the `ell = 1`, in-module analogue of that module's `witnessClass_not_excluded`, and the
   overlap is DISCLOSED rather than papered (LAW-19).

The whole section rests on one structural fact about `ell = 1`: `Q_1` is INJECTIVE, so a fibre is a
SINGLETON and the Schur minimality hypothesis `hmin` of §9a.4 is free. At `ell ≥ 2` it is not free, and
that is the honest price of a non-vacuous instance at a real scale. -/

/-- **`Q_1` IS INJECTIVE, for EVERY background `U`.** At `ell = 1` the transport path is empty and
`Q_1 = id` (`RegularUGamma0.lineCoarseRestrictCov_one_eq_self`), so each fibre is a singleton. -/
theorem lineCoarseRestrictCovLM_one_injective
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Function.Injective (lineCoarseRestrictCovLM U 1) := by
  intro A A' h
  funext b
  have hc := congrFun h
    ((⟨b.1, CovariantHjMinimizer.mem_CoarseLattice_one b.1⟩, b.2) : CoarseBond L 1)
  rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCovLM_apply,
    RegularUGamma0.lineCoarseRestrictCov_one_eq_self,
    RegularUGamma0.lineCoarseRestrictCov_one_eq_self] at hc
  exact hc

/-- **THE SHARP MIN-SWAP CONSTANT at the `ell = 1` loop datum**, as an explicit closed form:
`‖D_1 loop‖² / n(Q_1 loop)`. Both numerator and denominator are strictly positive
(`TransverseClass.loopField_dstarD_pos`, `loopField_unit_shadow_ne_zero_ell_one`). -/
noncomputable def sharpGammaLoopEllOne (m : ℕ) : ℝ :=
  dstarDQuadForm (trivialU (WitnessInequality.wExt m)) (NilLevelTarget.loopField m) /
    covCoarseBondInner
      (lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
        (NilLevelTarget.loopField m))
      (lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
        (NilLevelTarget.loopField m))

theorem sharpGammaLoopEllOne_pos (m : ℕ) : 0 < sharpGammaLoopEllOne m :=
  div_pos (TransverseClass.loopField_dstarD_pos m)
    (covCoarseBondInner_pos_of_ne_zero (loopField_unit_shadow_ne_zero_ell_one m))

/-- **THE GUARDED TARGET IS INHABITED, NON-VACUOUSLY.** `γ = sharpGammaLoopEllOne m > 0`, the class is
the nonempty singleton `{Q_1(loopField m)}`, the witness is `loopField m` — in the slice, admissible
shadow, strictly positive coarse energy. -/
theorem minSwap_guarded_holds_at_sharp_gamma_ell_one (m : ℕ)
    (levels : List (KernelSubspace.Level (WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (WitnessInequality.wExt m)) levels).HasOrthogonalProjection] :
    MinSwapTotalTargetNV levels (trivialU (WitnessInequality.wExt m))
      ({lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
          (NilLevelTarget.loopField m)} :
        Set (CoarseBond (WitnessInequality.wExt m) 1 → SuTwo))
      (sharpGammaLoopEllOne m) (NilLevelTarget.loopField m) := by
  unfold sharpGammaLoopEllOne
  exact MinSwapTotalTargetNV_singleton_at_sharp_gamma levels
    (trivialU (WitnessInequality.wExt m)) (NilLevelTarget.loopField m)
    (loopField_mem_slice m levels)
    (covCoarseBondInner_pos_of_ne_zero (loopField_unit_shadow_ne_zero_ell_one m))
    (TransverseClass.loopField_dstarD_pos m)
    (fun A _ hQ => le_of_eq
      (congrArg (dstarDQuadForm (trivialU (WitnessInequality.wExt m)))
        (lineCoarseRestrictCovLM_one_injective _ hQ).symm))

/-- **AND THE LEFT-HAND SIDE IS STRICTLY POSITIVE THERE** — so what is satisfied is a genuine lower
bound at a named point, not any of §9a's zero-left-hand-side degeneracies. -/
theorem minSwap_guarded_lhs_pos_ell_one (m : ℕ)
    (levels : List (KernelSubspace.Level (WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (WitnessInequality.wExt m)) levels).HasOrthogonalProjection] :
    0 < sharpGammaLoopEllOne m *
        covCoarseBondInner
          (lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
            (NilLevelTarget.loopField m))
          (lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
            (NilLevelTarget.loopField m)) ∧
      0 < dstarDQuadForm (trivialU (WitnessInequality.wExt m)) (NilLevelTarget.loopField m) :=
  ⟨(minSwap_guarded_holds_at_sharp_gamma_ell_one m levels).lhs_pos.1,
    (minSwap_guarded_holds_at_sharp_gamma_ell_one m levels).lhs_pos.2.2⟩

/-- **AND IT FAILS ABOVE THE SHARP CONSTANT.** With the previous theorem this is the two-sided
statement: the guarded target on this class is satisfied at `γ*` and REFUTED for every `γ > γ*`. A
vacuous target cannot do that — every one of §9a's six instances holds for arbitrarily large `γ`. -/
theorem not_minSwap_guarded_above_sharp_gamma_ell_one (m : ℕ)
    (levels : List (KernelSubspace.Level (WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (WitnessInequality.wExt m)) levels).HasOrthogonalProjection]
    {γ : ℝ} (hγ : sharpGammaLoopEllOne m < γ) :
    ¬ MinSwapTotalTargetNV levels (trivialU (WitnessInequality.wExt m))
        ({lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
            (NilLevelTarget.loopField m)} :
          Set (CoarseBond (WitnessInequality.wExt m) 1 → SuTwo))
        γ (NilLevelTarget.loopField m) :=
  not_MinSwapTotalTargetNV_singleton_above_sharp levels
    (trivialU (WitnessInequality.wExt m)) (NilLevelTarget.loopField m) hγ

/-- **§8's FORCED EXCLUSION DOES NOT EMPTY THIS CLASS.** Every slice element whose unit shadow is
admissible for the witness class is NOT covariant-curl-free — by injectivity of `Q_1` it IS the loop,
and the loop's circulation is `4·suTwoWitness ≠ 0` (`loopField_curlLM_ne_zero`). So the non-vacuous
instance above is not obtained by ignoring the constraint §8 forces.

The `ell = 2`/general-`ell` analogue is `MinSwapWitness.witnessClass_not_excluded`; that module imports
this one, so the overlap is disclosed, not shared. -/
theorem witnessClass_ell_one_not_excluded (m : ℕ)
    (levels : List (KernelSubspace.Level (WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (WitnessInequality.wExt m)) levels).HasOrthogonalProjection] :
    ∀ A, A ∈ slice levels (trivialU (WitnessInequality.wExt m)) →
      lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1 A ∈
        ({lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
            (NilLevelTarget.loopField m)} :
          Set (CoarseBond (WitnessInequality.wExt m) 1 → SuTwo)) →
      curlCovariantLM (trivialU (WitnessInequality.wExt m)) A ≠ 0 := by
  intro A _ hmem
  rw [Set.mem_singleton_iff] at hmem
  rw [lineCoarseRestrictCovLM_one_injective _ hmem]
  exact loopField_curlLM_ne_zero m

/-- **THE GUARDED SCHUR TARGET IS INHABITED, NON-VACUOUSLY** — the whole `ell = 1` instance
transported through `MinSwapTotalTargetNV.toSchur`. Read against the denotation qualification on
`MinSwapSchurTarget`: this is a statement about this tree's single-scale pullback form, and at
`ell = 1` that form collapses to the bare curl energy. -/
theorem minSwap_guarded_schur_holds_at_sharp_gamma_ell_one (m : ℕ)
    (levels : List (KernelSubspace.Level (WitnessInequality.wExt m)))
    [(deltaKernelImageCovH (trivialU (WitnessInequality.wExt m)) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 1 levels
        (trivialU (WitnessInequality.wExt m))).HasOrthogonalProjection] :
    MinSwapSchurTargetNV levels (trivialU (WitnessInequality.wExt m))
      ({lineCoarseRestrictCovLM (trivialU (WitnessInequality.wExt m)) 1
          (NilLevelTarget.loopField m)} :
        Set (CoarseBond (WitnessInequality.wExt m) 1 → SuTwo))
      (sharpGammaLoopEllOne m) (NilLevelTarget.loopField m) :=
  MinSwapTotalTargetNV.toSchur levels (trivialU (WitnessInequality.wExt m)) _
    (sharpGammaLoopEllOne m) (NilLevelTarget.loopField m)
    (minSwap_guarded_holds_at_sharp_gamma_ell_one m levels)

end Tree

#print axioms mem_fibre
#print axioms bddBelow_image_of_nonneg
#print axioms zeroSite_mem_CoarseLattice
#print axioms Q_constField_eq
#print axioms minSwap_iff
#print axioms total_of_schur
#print axioms schur_of_total
#print axioms minSwap_mpr_needs_nonempty
#print axioms minSwap_mp_needs_bddBelow
#print axioms fibre_datum_satisfies_total
#print axioms schur_eq_zero_of_zero_mem
#print axioms minSwap_iff_inner
#print axioms minSwap_nonvacuous_witness

#print axioms deltaJ_eq_dstarDQuadForm_hjExtension
#print axioms deltaJ_ge_of_total_on_hjInvariant
#print axioms slice_hjExtension_invariant
#print axioms unitClause_hjExtension_invariant
#print axioms sliceOver_hjExtension_invariant
#print axioms minSwap_transfer
#print axioms loopField_unit_shadow_eq_zero
#print axioms loopField_satisfies_minSwap_total
#print axioms loopField_refutes_fine_but_not_unit
#print axioms curl_constField_trivialU
#print axioms div_constField_trivialU
#print axioms constField_mem_slice
#print axioms Q_constField
#print axioms dstarDQuadForm_constField
#print axioms deltaJ_constField_eq_zero
#print axioms covCoarseBondInner_const_pos
#print axioms minSwap_total_on_bare_slice_refuted
#print axioms minSwap_schur_on_bare_slice_refuted
#print axioms unitClass_must_exclude_coarse_const
#print axioms minSwap_domain_inhabited_with_positive_lhs

#print axioms covCoarseBondInner_pos_of_ne_zero
#print axioms const_coarse_ne_zero
#print axioms dstarDQuadForm_eq_zero_of_curl_zero
#print axioms total_forces_curlFree_unit_shadow_zero
#print axioms unitClass_must_exclude_curlFree_image
#print axioms MinSwapTotalTarget.toSchur
#print axioms MinSwapSchurTarget_univ_false

#print axioms loopField_unit_shadow_ne_zero_ell_one
#print axioms loopField_curlLM_ne_zero
#print axioms loopField_mem_slice
#print axioms minSwap_domain_positive_lhs_ell_one
#print axioms minSwap_domain_non_curlFree_ell_one

-- §9 target `Prop`s: statements UNCHANGED, `MinSwapSchurTarget`'s DENOTATION docstring corrected
-- 2026-07-29; audited here because the correction is load-bearing for every consumer.
#print axioms MinSwapTotalTarget
#print axioms MinSwapSchurTarget

-- §9a — the six vacuities of the raw targets, as theorems
#print axioms covCoarseBondInner_zero_eq_zero
#print axioms MinSwapTotalTarget_holds_at_empty_class
#print axioms MinSwapTotalTarget_holds_of_gamma_nonpos
#print axioms MinSwapTotalTarget_holds_at_zero_class
#print axioms zero_field_in_domain_of_zero_class
#print axioms MinSwapTotalTarget_holds_of_class_misses_image
#print axioms lineCoarseRestrictCovLM_ell_zero
#print axioms MinSwapTotalTarget_holds_at_ell_zero_const_class
#print axioms ell_zero_const_class_nonempty_with_positive_weight
#print axioms MinSwapSchurTarget_holds_at_empty_class
#print axioms MinSwapSchurTarget_holds_of_gamma_nonpos
#print axioms MinSwapSchurTarget_holds_at_zero_class
#print axioms MinSwapSchurTarget_holds_of_class_misses_image
#print axioms MinSwapSchurTarget_holds_at_ell_zero_const_class

-- §9a.2 — the guarded targets and the transfers
#print axioms MinSwapTotalTargetNV
#print axioms MinSwapSchurTargetNV
#print axioms MinSwapTotalTargetNV.lhs_pos
#print axioms MinSwapTotalTarget.toNV
#print axioms MinSwapTotalTargetNV.toRaw
#print axioms MinSwapTotalTargetNV.toSchur
#print axioms MinSwapSchurTarget.toNV
#print axioms MinSwapSchurTargetNV.toRaw
#print axioms MinSwapSchurTargetNV.lhs_pos

-- §9a.3 — regression: each vacuity FAILS against the guard
#print axioms not_MinSwapTotalTargetNV_empty_class
#print axioms not_MinSwapTotalTargetNV_of_gamma_nonpos
#print axioms not_MinSwapTotalTargetNV_zero_class
#print axioms not_MinSwapTotalTargetNV_of_class_misses_image
#print axioms not_MinSwapTotalTargetNV_ell_zero
#print axioms not_MinSwapSchurTargetNV_empty_class
#print axioms not_MinSwapSchurTargetNV_zero_class
#print axioms not_MinSwapSchurTargetNV_of_gamma_nonpos

-- §9a.4 — the sharp singleton instance, both directions
#print axioms MinSwapTotalTargetNV_singleton_at_sharp_gamma
#print axioms not_MinSwapTotalTargetNV_singleton_above_sharp

-- §10a — the guard is SATISFIABLE: the concrete `ell = 1` instance
#print axioms lineCoarseRestrictCovLM_one_injective
#print axioms sharpGammaLoopEllOne
#print axioms sharpGammaLoopEllOne_pos
#print axioms minSwap_guarded_holds_at_sharp_gamma_ell_one
#print axioms minSwap_guarded_lhs_pos_ell_one
#print axioms not_minSwap_guarded_above_sharp_gamma_ell_one
#print axioms witnessClass_ell_one_not_excluded
#print axioms minSwap_guarded_schur_holds_at_sharp_gamma_ell_one

end AdalyFormal.Balaban.MinSwap
