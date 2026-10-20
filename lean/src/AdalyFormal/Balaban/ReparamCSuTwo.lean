/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.LineIntegralCovariant

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[REPARAM-C-SU2]` — the CONCRETE CMP99b (3.157) reparametrization `C` on the su(2) carrier

## ⚠ CORRECTION BANNER (2026-07-26) — `droppedBond` IS NOT THE SOURCE'S `b₀` FOR `ell ≥ 2`

**Read this before using anything in this module that mentions `droppedBond`.**

`def droppedBond ell c := (c.1.1, c.2)` (§1 below) — the fine bond of `c` at `μ`-OFFSET `0` — is
**NOT** CMP99b p.428's `b₀`, and the module text below that calls it "Balaban's bond of `B(c)`
contained in `c`" is **WRONG for every `ell ≥ 2`**. What is right is the offset-`ell−1` bond,
`ReparamCDisjoint.droppedBondLast ell c = (QOne.pathSite c.1.1 c.2 (ell-1), c.2)`, equivalently
`ReparamCWiring.lastFineBond` (two lanes named the same object independently). **The three known
grounds, each carried by a NAMED kernel-checked declaration elsewhere in this tree — not by this
prose:**

1. **It violates the defining property this module's own §1 docstring quotes.** p.428:
   `B(c) = {`bonds `b` : `b₋ ∈ B(c₋)`, `b₊ ∈ B(c₊)}`, and `B(c) ∩ c` is "the exactly one bond `b₀`
   of `B(c)` contained in `c`". For the fine bond of `c` at offset `s` (`b₋ = y + s e_μ`,
   `b₊ = y + (s+1) e_μ`): `b₋ ∈ B(c₋) ⟺ s ∈ [0, ell)` and `b₊ ∈ B(c₊) ⟺ s ≥ ell − 1`, whose UNIQUE
   solution is `s = ell − 1` — and the source's own uniqueness assertion is exactly that count.
   `droppedBond` is `s = 0`: its head `y + e_μ` lies in `B(c₋)`, not `B(c₊)`. (This is the S83
   pattern: transcribe the definition, then build an object violating it.)
   Derivation: `compute/cstar_roadmap/GAP2_DECOUPLING.md`.
2. **At offset `0` the coarse constraints are COUPLED and the full `C` does not exist.**
   `ReparamCDisjoint.droppedBond_couples_witness` / `droppedBond_not_decoupled` (in-kernel
   refutations: the decoupling statement is FALSE at this bond), while
   `ReparamCDisjoint.droppedBondLast_not_reads` proves decoupling at offset `ell−1` for general `L`.
   With offset `0` the coupling digraph is a disjoint union of directed cycles and
   `ReparamCJoint.witnessMain_joint_kernel_nonzero` (`∀ U`, no regularity hypothesis) makes the
   joint system SINGULAR on `witnessL`.
3. **At offset `0` the bond is not even a free variable.** `(y, μ)` is the whole of
   `staircasePath y (y + e_μ)`, so the axial gauge already forces it to `0`:
   `ReparamCWiring.droppedBond_mem_some_staircase` (general `ell ≥ 2`),
   `droppedBond_mem_staircase_witness`, `droppedBond_hb0_fails`; and
   `ReparamCDisjoint.droppedBondLast_not_mem_staircase` /
   `ReparamCWiring.lastFineBond_notMem_staircase` prove the corrected bond is off every staircase.

**Why `droppedBond` is NOT redefined here.** A silent semantic change to a `def` that live lanes
are mid-flight against is the concurrent-lane hazard this project has been bitten by, and the
corrected object ALREADY EXISTS downstream (`ReparamCDisjoint.droppedBondLast`), which this module
cannot import without a cycle. So `droppedBond` is **RETAINED, DEPRECATED, and annotated in place**
(S75: correction propagated, old statements retained struck), and every consumer is redirected.

**Scope of the damage inside THIS module — measured, not asserted.** §2/§3/§4
(`constraintFunctional`,
`dropZero`, `coeffDc`, `restFunctional`, `reparamCSuTwo`, `reparamCSuTwo_apply`,
`reparamCSuTwo_free_bond`, `reparamCSuTwo_at_b0`, `constraintFunctional_reparamC_split`,
**`reparamCSuTwo_constraint`** — the crux) are **parameterized on a GENERAL `b₀ : Bond L` and are
UNAFFECTED**: they hold verbatim at `ReparamCDisjoint.droppedBondLast ell c`, and the whole
single-constraint solve transfers by instantiation, given `hinv` there. What IS about the wrong
object: the §4b witness discharge (`coeffDc_witness`, `coeffDc_witness_eq_smul_id`,
`coeffDc_witness_hinv`, `reparamCSuTwo_witness_constraint`), §5 (`reparamCSuTwo_ne_zero`), §6
(`restFunctional_genuinely_U_dependent`, `reparamCSuTwo_genuinely_U_dependent`), and
`droppedBond_targetCoarseBond` / `site1_ne_droppedBond` / `IsFreeBond` — all of these remain TRUE
THEOREMS, but they are theorems about the DEGENERATE offset-`0` bond, so they do NOT discharge the
corresponding facts for the source's `C`. Each carries its own scope line below.

**`ell = 1` is exempt**: there `ell − 1 = 0`, and `droppedBond_eq_lastOffset_of_le_one` (§1b) proves
the two notions coincide. `droppedBond_ne_lastOffset_witness` (§1b) proves they genuinely differ at
`witnessEll = 2`, so this correction is not vacuous.

**Next brick of the su(2) `C*Δ_kC` assembly (de-islanding the covariant coercivity).** Where
`CStarDeltaKCSuTwo.lean` built the (3.157) SANDWICH over a *generic* `C` and PROVED (S91 guard
`free_C_coercivity_target_vacuous_at_zero_C`) that a *free* `C` makes any coercivity target
vacuous, this module builds the **CONCRETE constrained (3.157) `C`** on `Bond L → SuTwo`, curing
that vacuity: the `C` here is the identity off a single dropped bond and SOLVES the covariant
constraint `(Q₁(U)·B)(c)=0` on the dropped bond.

## SOURCE PIN (CMP99b p.428, adjudicated `corpus/pages/CMP99b_p428.md`, image 400 dpi)

> "Variables `B` depend linearly on `B̃` and we have `B = C B̃`, where `C` is a linear operator. It
> is an identity operator on almost all bonds, except the bonds `b₀` for which a value
> `(C B̃)(b₀)` is equal to a solution of the equation `(QB)(c) = 0`, considered as an equation on
> the variable `B(b₀)`."

The free bonds are `Λ̃ = Λ \ (∪_{y∈Λ'} Ax(y) ∪ ∪_{c∈Λ'} B(c)∩c)`, and `B(c)∩c` is "the exactly one
bond `b₀` of `B(c)` contained in `c`". So per coarse bond `c`, ONE fine bond `b₀ ⊂ c` is dropped;
`C` is the identity on the rest and reconstructs `B(b₀)` from the covariant constraint. `Q₁(U)` is
covariant, so the reconstruction is genuinely `U`-dependent (this is the whole point — the scalar
carrier of the convicted `FaithfulCoercivity.lean` provably could not host it).

**On the bare `Q` in the quoted constraint `(QB)(c)=0`:** p.428 writes the per-coarse-bond equation
with a bare `Q`, but the SAME page fixes its meaning — the subspace on which (3.156) is considered is
`{B : B=0 on Λᶜ, B=0 on ∪Ax(y), Q₁B=0}` (verbatim `Q_1B=0`). So the constraint being solved bond-by-
bond is `(Q₁B)(c)=0`; this module reads `Q = Q₁` (the sole coarse-graining map at this scale) and uses
the FAITHFUL `Q₁(U) = lineCoarseRestrictCov U ell` (LAW-19). This is an identification of the page's
bare `Q` with its own `Q₁`, not a verbatim quote of a subscript.

## THE CONSTRUCTION, and the ONE remaining geometric lemma

~~For a fixed coarse bond `c` we take `b₀ := (c₋, μ) = (c.1.1, c.2)` — the fine bond at the coarse
base site in the coarse direction, i.e. Balaban's "bond of `B(c)` contained in `c`".~~
**SUPERSEDED (2026-07-26, see the CORRECTION BANNER above; retained struck).** That identification
is FALSE for `ell ≥ 2`: Balaban's bond is the offset-`ell−1` one,
`ReparamCDisjoint.droppedBondLast ell c`. The construction below is stated for a **general**
`b₀ : Bond L` and is unaffected — instantiate it at `droppedBondLast`, not at `droppedBond`. Write
the covariant constraint functional `L_c(B) := (Q₁(U)B)(c) = lineCoarseRestrictCov U ell B c`
(FAITHFUL `Q₁(U)`, `LineIntegralCovariant.lean`, LAW-19). Decompose, linearly and exactly,
`L_c(B) = coeffDc(B(b₀)) + rest_c(B)` where
* `coeffDc := L_c ∘ single_{b₀}` is the `SuTwo →ₗ SuTwo` coefficient of `B(b₀)` in `(Q₁B)(c)`, and
* `rest_c := L_c ∘ dropZero_{b₀}` reads `B` with its `b₀`-component zeroed (so it does NOT depend on
  `B(b₀)`).

Balaban's phrase *"considered as an equation on the variable `B(b₀)`"* is exactly the assertion that
`coeffDc` is invertible. GIVEN a right inverse `Dc_inv` of `coeffDc` (`hinv : coeffDc ∘ Dc_inv = id`)
we set

  `(C B̃)(b) = B̃(b)` for `b ≠ b₀`,   `(C B̃)(b₀) = − Dc_inv(rest_c(B̃))`,

i.e. `reparamCSuTwo := dropZero_{b₀} + single_{b₀} ∘ (−(Dc_inv ∘ rest_c))`. Then the defining
constraint holds **by construction and PROVED** (`reparamCSuTwo_constraint`, the crux):
`L_c(C B̃) = rest_c(B̃) + coeffDc(−Dc_inv(rest_c B̃)) = rest_c(B̃) − rest_c(B̃) = 0`.

**The one remaining geometric lemma** is that `coeffDc` is genuinely invertible.
~~equivalently that `b₀ = (c₋, μ)` is hit EXACTLY ONCE in the `Q₁(U)`-block-sum for `c`, with
trivial
transport, so that `coeffDc = (1/ell⁴)·id`. On the witness lattice this is discharged
UNCONDITIONALLY below (`coeffDc_witness`, `hinv` then holds with `Dc_inv = ell⁴·id`); in general it
is the block-enumeration fact `∀ (x,i) with x∈B(c₋), i<ell : pathSite x μ i = c₋ ↔ (x,i)=(c₋,0)`.~~
**SUPERSEDED (2026-07-26; retained struck).** The multiplicity-`1`/trivial-transport picture, and
hence `coeffDc = (1/ell⁴)·id`, is a property of the WRONG offset-`0` bond. At the source's
offset-`ell−1` bond the block-sum reaches `b₀` TWICE (at `(x,i) = (y, ell−1)` and
`(y + e_μ, ell−2)`), and at `ell = 2` the coefficient is `(1/ell⁴)·(2 • RMap (U_μ(y)))` —
still invertible (`RMap` of an `SU(2)` element is orthogonal), with no numerical computation needed.
That is `ReparamCDisjoint.readers_ell2` + `transport_terms_eq` (kernel-checked there, and carrying a
side condition `0 < L μ` that this module never carried). `coeffDc_witness` below remains a TRUE
theorem, but ONLY about the degenerate offset-`0` bond. The `blockOf`-truncation caveat (MEMORY
`torus-blockof-truncation-artifact`) still applies to any general-`L` version.

## WHAT IS AND IS NOT DONE (honesty / scope)

* **PROVED, unconditional, kernel-checked** (`#print axioms` = {propext, Classical.choice, Quot.sound}):
  `reparamCSuTwo` is a genuine `LinearMap`; the pointwise formulas; the CONSTRAINT
  `(Q₁(U)(C B̃))(c)=0` given `hinv`; the free-bond identity; `C ≠ 0` (it is NOT the S91-vacuous
  `C=0`); genuine `U`-dependence of `C` on the witness lattice; and the witness discharge
  `coeffDc_witness` making `hinv` UNCONDITIONAL there (so the whole `C` is unconditional on witness).
  **SCOPE (2026-07-26):** of these, only the general-`b₀` items (the `LinearMap` structure, the
  pointwise formulas, the CONSTRAINT, the free-bond identity) are statements about the source's
  object. The witness-instantiated items (`coeffDc_witness`, `hinv`, `C ≠ 0`, `U`-dependence) are
  true theorems **at the DEGENERATE offset-`0` bond** — see the CORRECTION BANNER. They are not
  refuted; they simply do not discharge the corresponding facts for Balaban's `b₀`.
* **This is a SINGLE-constraint `C`** — it drops the ONE bond `b₀` of ONE coarse bond `c`. The full
  (3.157) `C` drops one bond per coarse bond (plus the axial `Ax(y)` bonds). Assembling the full `C`
  additionally needs (i) the DECOUPLING fact that the `c`-block-sum reads no OTHER coarse bond's
  dropped bond (almost-locality), and (ii) `coeffDc` invertibility per `c`.
  ~~Both are NAMED, not built.~~ **UPDATED (2026-07-26; retained struck):** at the CORRECTED bond
  `ReparamCDisjoint.droppedBondLast`, (i) is now BUILT and general in `L`
  (`ReparamCDisjoint.droppedBondLast_not_reads`, `constraint_indep_of_other_droppedBond`, under
  `0 < ell ∧ ∀ μ, ell ∣ L μ + 1`), and (ii) is built at `ell = 2` (`readers_ell2`,
  `transport_terms_eq`: coefficient `2 • RMap (U_μ(y))`, needing also `0 < L μ`). At the offset-`0`
  bond of THIS module, (i) is FALSE (`ReparamCDisjoint.droppedBond_not_decoupled`). The remaining
  unbuilt piece is the definitional plumbing of the pointwise `fullC` and the per-`c` solve for
  general `ell`.
* **ISLAND.** Nothing here is wired to `coerc_u_main` or any consumed spine declaration. NO coercivity
  is claimed; the coercivity target stays the OPEN `def : Prop` in `CovariantHjFaithful` §5. Item 4 of
  the dispatch (how `C` makes `leadingReparamForm`'s target non-vacuous) is STATED in §7's remark, not
  proved.
-/

namespace AdalyFormal.Balaban.ReparamCSuTwo

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.Balaban.LineIntegralCovariant
  AdalyFormal.Balaban.Q1Real
open AdalyFormal.Balaban.QOne (site1 targetCoarseBond witnessY_mem_block pathSite_zero)
open AdalyFormal.Balaban.AdmissibleSubspace
  (Bond witnessL witnessEll witnessY witnessY_coarse blockOf mem_blockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the dropped-bond selector and the free-bond predicate (source-pinned) -/

/-- **⚠ DEPRECATED / NOT THE SOURCE'S `b₀` (2026-07-26).**
~~**The dropped bond `b₀(c) := (c₋, μ)`** — CMP99b p.428's "the exactly one bond `b₀` of `B(c)`
contained in `c`": the fine bond at the coarse base site `c₋ = c.1.1` in the coarse direction
`μ = c.2`.~~ **The identification with p.428's `b₀` is FALSE for every `ell ≥ 2`** (retained struck;
see this module's CORRECTION BANNER for the full statement and the three named refutations).

This is the fine bond of `c` at `μ`-offset **`0`** (`droppedBond_eq_offset_zero`, §1b). p.428's `b₀`
is the unique fine bond of `c` with `b₋ ∈ B(c₋)` AND `b₊ ∈ B(c₊)`, i.e. offset **`ell − 1`**:

* **CANONICAL REPLACEMENT:**
  `ReparamCDisjoint.droppedBondLast ell c = (QOne.pathSite c.1.1 c.2 (ell-1), c.2)`
  (equivalently `ReparamCWiring.lastFineBond`). This module cannot import either without an import
  cycle, which is why the correction is an annotation + redirect rather than a redefinition.
* At offset `0` the coarse constraints COUPLE and the joint system is singular:
  `ReparamCDisjoint.droppedBond_not_decoupled`, `ReparamCJoint.witnessMain_joint_kernel_nonzero`.
* At offset `0` the bond lies ON `staircasePath c₋ (c₋ + e_μ)`, hence is pinned to `0` by the axial
  gauge and is not a free variable: `ReparamCWiring.droppedBond_mem_some_staircase`,
  `ReparamCDisjoint.droppedBond_not_off_staircases`.
* Exempt at `ell ≤ 1` (`droppedBond_eq_lastOffset_of_le_one`); genuinely different at `ell = 2`
  (`droppedBond_ne_lastOffset_witness`).

RETAINED (not deleted) because live downstream declarations are stated at it and are true theorems
about it; every such declaration carries a scope line below. -/
def droppedBond (ell : ℕ) (c : CoarseBond L ell) : Bond L := (c.1.1, c.2)

/-- **The free-bond predicate for the single coarse bond `c`**: every bond except `droppedBond c`.
(The full (3.157) `Λ̃` also removes the axial `Ax(y)` bonds and the dropped bonds of ALL coarse
bonds; here we treat one `c`.)
**SCOPE (2026-07-26):** inherits `droppedBond`'s defect — for `ell ≥ 2` this excludes the WRONG
bond. The (3.157) `Λ̃` excludes `ReparamCDisjoint.droppedBondLast ell c` (and the axial bonds, which
this predicate never removed anyway). No declaration in this module consumes `IsFreeBond`
(`reparamCSuTwo_free_bond` is stated as `b ≠ b₀` at a general `b₀`), so nothing is built on it. -/
def IsFreeBond (ell : ℕ) (c : CoarseBond L ell) (b : Bond L) : Prop := b ≠ droppedBond ell c

/-- On the witness lattice the dropped bond of `targetCoarseBond` is `(witnessY, 0)`.
**SCOPE (2026-07-26):** true, and it is precisely the computation exhibiting the defect — the
source's `b₀` at `witnessEll = 2` is `(periodicLatticeShift witnessY 0, 0)`, not `(witnessY, 0)`
(`droppedBond_ne_lastOffset_witness`, §1b). -/
theorem droppedBond_targetCoarseBond :
    droppedBond witnessEll targetCoarseBond = (witnessY, (0 : Fin 3)) := rfl

/-- The witness config bond `(site1, 0)` is a FREE bond (distinct from `b₀ = (witnessY, 0)`).
**SCOPE (2026-07-26):** true, but "free" here means "≠ the offset-`0` bond". -/
theorem site1_ne_droppedBond :
    ((site1 : PeriodicLatticeSite witnessL), (0 : Fin 3)) ≠
      droppedBond witnessEll targetCoarseBond := by
  rw [droppedBond_targetCoarseBond]
  intro h
  exact absurd (congrArg (fun p => (p.1) 0) h) (by decide)

/-! ## §1b — CORRECTION PINS: `droppedBond` is the OFFSET-`0` bond, and that differs from p.428's
offset-`ell−1` bond exactly when `ell ≥ 2`

These three declarations exist so that the CORRECTION BANNER is **kernel-backed rather than prose**
("a claim is not a certificate" — the test is NAME THE DECLARATION). They pin the offset, the
`ell ≤ 1` exemption, and non-vacuity of the correction at the witness lattice. They deliberately do
NOT restate the decoupling / staircase refutations, which already exist as named theorems in
`ReparamCDisjoint` and `ReparamCWiring` (LAW-19: reuse, do not rebuild); this module cannot import
either without an import cycle, so it refers to them by name only. -/

/-- **`droppedBond` is the fine bond of `c` at `μ`-OFFSET `0`** — made explicit in the kernel, so
the offset is not merely a claim in a docstring. (p.428's `b₀` is the offset-`ell−1` bond.) -/
theorem droppedBond_eq_offset_zero (ell : ℕ) (c : CoarseBond L ell) :
    droppedBond ell c = (AdalyFormal.Balaban.QOne.pathSite c.1.1 c.2 0, c.2) := rfl

/-- **The `ell ≤ 1` exemption.** At `ell ≤ 1` we have `ell − 1 = 0` in `ℕ`, so `droppedBond`
coincides with the source's offset-`ell−1` bond and the correction is a no-op. Hence the deprecation
is scoped exactly to `ell ≥ 2` (and `witnessEll = 2` is in that range). -/
theorem droppedBond_eq_lastOffset_of_le_one {ell : ℕ} (hell : ell ≤ 1) (c : CoarseBond L ell) :
    droppedBond ell c = (AdalyFormal.Balaban.QOne.pathSite c.1.1 c.2 (ell - 1), c.2) := by
  have h0 : ell - 1 = 0 := by omega
  rw [h0]
  rfl

/-- **NON-VACUITY OF THE CORRECTION.** At the witness lattice (`witnessEll = 2`) the offset-`0` bond
`droppedBond` and the source's offset-`ell−1` bond are DIFFERENT bonds — `(witnessY, 0)` versus
`(periodicLatticeShift witnessY 0, 0)`. So the deprecation above is not a relabeling: every witness
theorem in §4b/§5/§6 is about a bond that is provably not Balaban's `b₀`. -/
theorem droppedBond_ne_lastOffset_witness :
    droppedBond witnessEll targetCoarseBond ≠
      (AdalyFormal.Balaban.QOne.pathSite
        (targetCoarseBond : CoarseBond witnessL witnessEll).1.1
        (targetCoarseBond : CoarseBond witnessL witnessEll).2 (witnessEll - 1),
       (targetCoarseBond : CoarseBond witnessL witnessEll).2) := by
  intro h
  have hc := congrArg (fun p : Bond witnessL => (p.1) (0 : Fin 3)) h
  simp only [droppedBond] at hc
  revert hc
  decide

/-! ## §2 — the covariant constraint functional and its `b₀`-decomposition -/

/-- **`L_c(B) := (Q₁(U)B)(c)`**, the covariant constraint functional at coarse bond `c`, as a
`SuTwo`-valued real-linear functional of the full bond field — `lineCoarseRestrictCovLM U ell`
(faithful `Q₁(U)`, LAW-19) post-composed with evaluation at `c`. -/
noncomputable def constraintFunctional
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) : (Bond L → SuTwo) →ₗ[ℝ] SuTwo :=
  (LinearMap.proj c).comp (lineCoarseRestrictCovLM U ell)

theorem constraintFunctional_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (B : Bond L → SuTwo) :
    constraintFunctional U ell c B = lineCoarseRestrictCov U ell B c := rfl

/-- **`dropZero_{b₀}`**: zero out the `b₀`-component of a bond field, `id − single_{b₀}∘proj_{b₀}`. -/
noncomputable def dropZero (b₀ : Bond L) : (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) :=
  LinearMap.id - (LinearMap.single ℝ (fun _ : Bond L => SuTwo) b₀).comp (LinearMap.proj b₀)

theorem dropZero_apply (b₀ : Bond L) (B : Bond L → SuTwo) (b : Bond L) :
    dropZero b₀ B b = if b = b₀ then 0 else B b := by
  simp only [dropZero, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.single_apply, LinearMap.proj_apply, Pi.sub_apply, Pi.single_apply]
  by_cases h : b = b₀
  · subst h; simp
  · simp [h]

/-- **`coeffDc := L_c ∘ single_{b₀}`**, the `SuTwo →ₗ SuTwo` coefficient of `B(b₀)` in `(Q₁B)(c)`. -/
noncomputable def coeffDc
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (b₀ : Bond L) : SuTwo →ₗ[ℝ] SuTwo :=
  (constraintFunctional U ell c).comp (LinearMap.single ℝ (fun _ : Bond L => SuTwo) b₀)

theorem coeffDc_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (b₀ : Bond L) (v : SuTwo) :
    coeffDc U ell c b₀ v = lineCoarseRestrictCov U ell (Pi.single b₀ v) c := by
  simp only [coeffDc, LinearMap.comp_apply, LinearMap.single_apply, constraintFunctional_apply]

/-- **`rest_c := L_c ∘ dropZero_{b₀}`**, the part of `(Q₁B)(c)` NOT depending on `B(b₀)`. -/
noncomputable def restFunctional
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (b₀ : Bond L) : (Bond L → SuTwo) →ₗ[ℝ] SuTwo :=
  (constraintFunctional U ell c).comp (dropZero b₀)

/-! ## §3 — the CONCRETE (3.157) reparametrization `C`

**UNAFFECTED BY THE 2026-07-26 CORRECTION.** Everything in §2, §3 and §4 takes `b₀ : Bond L` as a
free parameter and never mentions `droppedBond`. Instantiate at
`ReparamCDisjoint.droppedBondLast ell c` to obtain the source's `C`; the crux
`reparamCSuTwo_constraint` then holds verbatim, given `hinv` at that bond. -/

/-- **The concrete (3.157) `C`**, parametrized by a right inverse `Dc_inv` of the coefficient
`coeffDc` (whose existence is Balaban's "considered as an equation on `B(b₀)`"). `C` is the identity
off `b₀` and puts `−Dc_inv(rest_c(B̃))` on `b₀`. This is a genuine `LinearMap` by construction. -/
noncomputable def reparamCSuTwo
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (b₀ : Bond L) (Dc_inv : SuTwo →ₗ[ℝ] SuTwo) :
    (Bond L → SuTwo) →ₗ[ℝ] (Bond L → SuTwo) :=
  dropZero b₀ +
    (LinearMap.single ℝ (fun _ : Bond L => SuTwo) b₀).comp (-(Dc_inv.comp (restFunctional U ell c b₀)))

theorem reparamCSuTwo_apply
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (b₀ : Bond L) (Dc_inv : SuTwo →ₗ[ℝ] SuTwo) (B : Bond L → SuTwo)
    (b : Bond L) :
    reparamCSuTwo U ell c b₀ Dc_inv B b =
      (if b = b₀ then 0 else B b) +
        (if b = b₀ then -(Dc_inv (restFunctional U ell c b₀ B)) else 0) := by
  simp only [reparamCSuTwo, LinearMap.add_apply, Pi.add_apply, LinearMap.comp_apply,
    LinearMap.single_apply, LinearMap.neg_apply, dropZero_apply, Pi.single_apply]

/-- **`C` acts as the identity on every free bond** `b ≠ b₀`. -/
theorem reparamCSuTwo_free_bond
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (b₀ : Bond L) (Dc_inv : SuTwo →ₗ[ℝ] SuTwo) (B : Bond L → SuTwo)
    {b : Bond L} (hb : b ≠ b₀) :
    reparamCSuTwo U ell c b₀ Dc_inv B b = B b := by
  rw [reparamCSuTwo_apply]
  simp [hb]

/-- **`C`'s value on the dropped bond `b₀` is the SOLVE** `−Dc_inv(rest_c(B̃))`. -/
theorem reparamCSuTwo_at_b0
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (b₀ : Bond L) (Dc_inv : SuTwo →ₗ[ℝ] SuTwo) (B : Bond L → SuTwo) :
    reparamCSuTwo U ell c b₀ Dc_inv B b₀ = -(Dc_inv (restFunctional U ell c b₀ B)) := by
  rw [reparamCSuTwo_apply]
  simp

/-! ## §4 — THE CRUX: the (3.157) defining constraint `(Q₁(U)(C B̃))(c) = 0` holds -/

/-- **`L_c(C B̃) = rest_c(B̃) + coeffDc(C B̃ at b₀)`** — the exact linear split of `(Q₁B)(c)` into its
`b₀`-independent part plus the coefficient of the `b₀`-value, evaluated at `B = C B̃`. Uses that
`rest_c` only reads bonds `≠ b₀`, on which `C B̃` agrees with `B̃`, so `rest_c(C B̃) = rest_c(B̃)`. -/
theorem constraintFunctional_reparamC_split
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (b₀ : Bond L) (Dc_inv : SuTwo →ₗ[ℝ] SuTwo) (B : Bond L → SuTwo) :
    constraintFunctional U ell c (reparamCSuTwo U ell c b₀ Dc_inv B) =
      restFunctional U ell c b₀ B + coeffDc U ell c b₀
        (reparamCSuTwo U ell c b₀ Dc_inv B b₀) := by
  -- `L_c = rest_c ∘? ...`: split `C B̃ = dropZero(C B̃) + single_{b₀}((C B̃) b₀)` and apply `L_c`.
  have hsplit : reparamCSuTwo U ell c b₀ Dc_inv B =
      dropZero b₀ (reparamCSuTwo U ell c b₀ Dc_inv B) +
        Pi.single b₀ (reparamCSuTwo U ell c b₀ Dc_inv B b₀) := by
    funext b
    rw [Pi.add_apply, dropZero_apply, Pi.single_apply]
    by_cases h : b = b₀ <;> simp [h]
  -- `rest_c(C B̃) = rest_c(B̃)`, since `dropZero` reads only bonds ≠ b₀ where `C B̃ = B̃`.
  have hrest : restFunctional U ell c b₀ (reparamCSuTwo U ell c b₀ Dc_inv B) =
      restFunctional U ell c b₀ B := by
    unfold restFunctional
    simp only [LinearMap.comp_apply]
    congr 1
    funext b
    rw [dropZero_apply, dropZero_apply]
    by_cases h : b = b₀
    · simp [h]
    · simp [h, reparamCSuTwo_free_bond U ell c b₀ Dc_inv B h]
  calc constraintFunctional U ell c (reparamCSuTwo U ell c b₀ Dc_inv B)
      = constraintFunctional U ell c
          (dropZero b₀ (reparamCSuTwo U ell c b₀ Dc_inv B) +
            Pi.single b₀ (reparamCSuTwo U ell c b₀ Dc_inv B b₀)) := by rw [← hsplit]
    _ = constraintFunctional U ell c (dropZero b₀ (reparamCSuTwo U ell c b₀ Dc_inv B)) +
          constraintFunctional U ell c (Pi.single b₀ (reparamCSuTwo U ell c b₀ Dc_inv B b₀)) := by
          rw [map_add]
    _ = restFunctional U ell c b₀ (reparamCSuTwo U ell c b₀ Dc_inv B) +
          coeffDc U ell c b₀ (reparamCSuTwo U ell c b₀ Dc_inv B b₀) := by
          rw [show restFunctional U ell c b₀ (reparamCSuTwo U ell c b₀ Dc_inv B) =
                constraintFunctional U ell c (dropZero b₀ (reparamCSuTwo U ell c b₀ Dc_inv B))
              from rfl,
            show coeffDc U ell c b₀ (reparamCSuTwo U ell c b₀ Dc_inv B b₀) =
                constraintFunctional U ell c
                  (Pi.single b₀ (reparamCSuTwo U ell c b₀ Dc_inv B b₀)) from rfl]
    _ = restFunctional U ell c b₀ B +
          coeffDc U ell c b₀ (reparamCSuTwo U ell c b₀ Dc_inv B b₀) := by rw [hrest]

/-- **THE (3.157) CONSTRAINT, PROVED (crux).** For the concrete `C = reparamCSuTwo` with a right
inverse `Dc_inv` of `coeffDc` (`hinv : coeffDc ∘ Dc_inv = id`), the defining covariant constraint
`(Q₁(U)(C B̃))(c) = 0` HOLDS for every `B̃`. This is Balaban's "`(C B̃)(b₀)` is a solution of
`(QB)(c)=0`", not asserted but derived: `L_c(C B̃) = rest_c(B̃) + coeffDc(−Dc_inv(rest_c B̃)) =
rest_c(B̃) − rest_c(B̃) = 0`. -/
theorem reparamCSuTwo_constraint
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (b₀ : Bond L) (Dc_inv : SuTwo →ₗ[ℝ] SuTwo)
    (hinv : (coeffDc U ell c b₀).comp Dc_inv = LinearMap.id) (B : Bond L → SuTwo) :
    lineCoarseRestrictCov U ell (reparamCSuTwo U ell c b₀ Dc_inv B) c = 0 := by
  have hsplit := constraintFunctional_reparamC_split U ell c b₀ Dc_inv B
  rw [reparamCSuTwo_at_b0] at hsplit
  rw [show lineCoarseRestrictCov U ell (reparamCSuTwo U ell c b₀ Dc_inv B) c =
        constraintFunctional U ell c (reparamCSuTwo U ell c b₀ Dc_inv B) from rfl, hsplit]
  rw [map_neg]
  have hcancel : coeffDc U ell c b₀ (Dc_inv (restFunctional U ell c b₀ B)) =
      restFunctional U ell c b₀ B := by
    have := LinearMap.congr_fun hinv (restFunctional U ell c b₀ B)
    simpa using this
  rw [hcancel]
  abel

/-! ## §4b — DISCHARGING `hinv` ON THE WITNESS LATTICE: `coeffDc = (1/ell⁴)·id`, UNCONDITIONALLY

**⚠ SCOPE (2026-07-26): this whole section is about the DEGENERATE offset-`0` bond.** The theorems
are TRUE and are NOT refuted, but they discharge `hinv` at `droppedBond`, which is not CMP99b
p.428's `b₀` for `ell ≥ 2` (CORRECTION BANNER; `droppedBond_ne_lastOffset_witness`). At the source's
bond `ReparamCDisjoint.droppedBondLast` the multiplicity is `2`, not `1`, and the coefficient is
`(1/ell⁴)·(2 • RMap (U_μ(y)))` at `ell = 2` — still invertible, but by a DIFFERENT computation
(`ReparamCDisjoint.readers_ell2`, `transport_terms_eq`, which additionally need `0 < L μ`). So
`coeffDc_witness_hinv` below does NOT discharge `hinv` for the corrected `C`; that discharge is a
named open step (`compute/cstar_roadmap/ROADMAP.md` §GAP 2).

This is the "remaining geometric lemma" of the module docstring, PROVED on the witness lattice
(`witnessL`, `witnessEll = 2`): the dropped bond `b₀ = (witnessY,0)` is hit EXACTLY ONCE in the
`Q₁(U)`-block-sum for `targetCoarseBond` — the DIRECT term at `x = witnessY, i = 0`, whose transport
path is empty (`hol = 1`), while EVERY shift term (`i = 1`) misses `b₀` because no block site shifts
onto `witnessY` (`x₀ ∈ {0,1} ⇒ x₀+1 ∈ {1,2} ≠ 0`). Hence `coeffDc = (1/16)·id` is invertible, so
`hinv` holds with `Dc_inv = ell⁴·id` and the witness `C` is UNCONDITIONAL (no assumed inverse). -/

theorem coeffDc_witness (v : SuTwo) :
    coeffDc witnessU witnessEll targetCoarseBond (droppedBond witnessEll targetCoarseBond) v
      = (1 / (witnessEll : ℝ) ^ 4) • v := by
  rw [coeffDc_apply, droppedBond_targetCoarseBond]
  show (1 / (witnessEll : ℝ) ^ 4) •
      ∑ x ∈ blockOf targetCoarseBond.1.1 witnessEll,
        rZeroA witnessU targetCoarseBond.1.1 x (Pi.single (witnessY, (0 : Fin 3)) v)
          targetCoarseBond.2 witnessEll = _
  have hbase : (targetCoarseBond : CoarseBond witnessL witnessEll).1.1 = witnessY := rfl
  have hdir : (targetCoarseBond : CoarseBond witnessL witnessEll).2 = (0 : Fin 3) := rfl
  rw [hbase, hdir]
  congr 1
  have hEll : witnessEll = 2 := rfl
  have hsplit : ∀ x ∈ blockOf witnessY witnessEll,
      rZeroA witnessU witnessY x (Pi.single (witnessY, (0 : Fin 3)) v) 0 witnessEll =
        RMap (periodicPathHolonomy witnessU witnessY (transportPath witnessY x 0 0))
          ((Pi.single (witnessY, (0 : Fin 3)) v : Bond witnessL → SuTwo) (x, 0)) +
        RMap (periodicPathHolonomy witnessU witnessY (transportPath witnessY x 0 1))
          ((Pi.single (witnessY, (0 : Fin 3)) v : Bond witnessL → SuTwo) (periodicLatticeShift x 0, 0)) := by
    intro x _; rw [hEll, rZeroA_ell2]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hdirect : ∑ x ∈ blockOf witnessY witnessEll,
      RMap (periodicPathHolonomy witnessU witnessY (transportPath witnessY x 0 0))
        ((Pi.single (witnessY, (0 : Fin 3)) v : Bond witnessL → SuTwo) (x, 0)) = v := by
    rw [Finset.sum_eq_single witnessY]
    · rw [Pi.single_eq_same]
      have htp : transportPath witnessY witnessY (0 : Fin 3) 0 = [] := by
        simp only [transportPath, pathSite_zero, GammaPath_self, straightSegment_self,
          List.append_nil]
      rw [htp]
      show RMap (periodicPathHolonomy witnessU witnessY ([] : List (Fin 3 × Bool))) v = v
      rw [show periodicPathHolonomy witnessU witnessY ([] : List (Fin 3 × Bool)) = 1 from rfl,
        RMap_one]
      rfl
    · intro x _ hx
      have hne : (x, (0 : Fin 3)) ≠ (witnessY, (0 : Fin 3)) := fun h => hx (congrArg Prod.fst h)
      rw [Pi.single_eq_of_ne hne, map_zero]
    · intro h; exact absurd witnessY_mem_block h
  have hshift : ∑ x ∈ blockOf witnessY witnessEll,
      RMap (periodicPathHolonomy witnessU witnessY (transportPath witnessY x 0 1))
        ((Pi.single (witnessY, (0 : Fin 3)) v : Bond witnessL → SuTwo) (periodicLatticeShift x 0, 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx0 : (x (0 : Fin 3)).val < 2 := by
      have h := ((mem_blockOf.mp hx) (0 : Fin 3)).2
      have hy : (witnessY (0 : Fin 3)).val = 0 := rfl
      have he : witnessEll = 2 := rfl
      rw [hy, he] at h
      omega
    have hshiftne : periodicLatticeShift x (0 : Fin 3) ≠ witnessY := by
      intro heq
      have hcoord : (periodicLatticeShift x (0 : Fin 3)) (0 : Fin 3) = witnessY (0 : Fin 3) := by
        rw [heq]
      rw [periodicLatticeShift, Function.update_self] at hcoord
      have hw : witnessL (0 : Fin 3) = 3 := rfl
      have hlt : x (0 : Fin 3) < Fin.last (witnessL (0 : Fin 3)) := by
        rw [Fin.lt_def, Fin.val_last]
        omega
      have hone : (x (0 : Fin 3) + 1).val = (x (0 : Fin 3)).val + 1 :=
        Fin.val_add_one_of_lt hlt
      have hvv : (x (0 : Fin 3) + 1).val = (witnessY (0 : Fin 3)).val := by rw [hcoord]
      have hy : (witnessY (0 : Fin 3)).val = 0 := rfl
      rw [hone, hy] at hvv
      omega
    have hne : (periodicLatticeShift x 0, (0 : Fin 3)) ≠ (witnessY, (0 : Fin 3)) :=
      fun h => hshiftne (congrArg Prod.fst h)
    rw [Pi.single_eq_of_ne hne, map_zero]
  rw [hdirect, hshift, add_zero]

/-- **`coeffDc` as an operator IS `(1/ell⁴)·id` on the witness lattice** — hence invertible. -/
theorem coeffDc_witness_eq_smul_id :
    coeffDc witnessU witnessEll targetCoarseBond (droppedBond witnessEll targetCoarseBond)
      = (1 / (witnessEll : ℝ) ^ 4) • LinearMap.id := by
  ext v
  rw [coeffDc_witness]
  simp

/-- **`hinv` HOLDS UNCONDITIONALLY on the witness lattice** with `Dc_inv = ell⁴·id`: the (3.157)
per-`b₀` equation is genuinely solvable because its coefficient `coeffDc = (1/ell⁴)·id` is invertible.
This is the discharge of the module's one named remaining lemma, on the witness lattice. -/
theorem coeffDc_witness_hinv :
    (coeffDc witnessU witnessEll targetCoarseBond
        (droppedBond witnessEll targetCoarseBond)).comp
      ((witnessEll : ℝ) ^ 4 • LinearMap.id) = LinearMap.id := by
  rw [coeffDc_witness_eq_smul_id]
  ext v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  have hne : (witnessEll : ℝ) ^ 4 ≠ 0 := by norm_num [witnessEll]
  rw [one_div_mul_cancel hne, one_smul]

/-- **THE (3.157) CONSTRAINT, UNCONDITIONAL ON THE WITNESS LATTICE.** No assumed inverse: the
concrete `C = reparamCSuTwo witnessU … (ell⁴·id)` satisfies `(Q₁(witnessU)(C B̃))(targetCoarseBond)=0`
for EVERY `B̃`, via `coeffDc_witness_hinv`. -/
theorem reparamCSuTwo_witness_constraint (B : Bond witnessL → SuTwo) :
    lineCoarseRestrictCov witnessU witnessEll
      (reparamCSuTwo witnessU witnessEll targetCoarseBond
        (droppedBond witnessEll targetCoarseBond)
        ((witnessEll : ℝ) ^ 4 • LinearMap.id) B) targetCoarseBond = 0 :=
  reparamCSuTwo_constraint witnessU witnessEll targetCoarseBond
    (droppedBond witnessEll targetCoarseBond) ((witnessEll : ℝ) ^ 4 • LinearMap.id)
    coeffDc_witness_hinv B

/-! ## §5 — NON-VACUITY: this `C` is NOT the S91-vacuous `C = 0`

**SCOPE (2026-07-26):** stated at `droppedBond` (the offset-`0` bond). The proof only uses that
`(site1,0) ≠ b₀` and that `C` is the identity off `b₀`, so the SAME argument runs verbatim at
`ReparamCDisjoint.droppedBondLast` once a witness free bond distinct from it is exhibited — but that
instance is NOT built here. -/

/-- **`C ≠ 0`** (as a `LinearMap`): it is the identity on free bonds, so on the witness lattice it
sends `Pi.single (site1,0) suTwoWitness` (a config on the FREE bond `(site1,0) ≠ b₀ = (witnessY,0)`)
to a field with nonzero value at `(site1,0)`. This is the concrete cure of the S91 vacuity guard
`CStarDeltaKCSuTwo.free_C_coercivity_target_vacuous_at_zero_C`: the constrained (3.157) `C` is
provably distinct from the degenerate `C=0` that made the free-`C` coercivity target vacuous. -/
theorem reparamCSuTwo_ne_zero (Dc_inv : SuTwo →ₗ[ℝ] SuTwo) :
    reparamCSuTwo witnessU witnessEll targetCoarseBond
        (droppedBond witnessEll targetCoarseBond) Dc_inv ≠ 0 := by
  intro hzero
  have hval := reparamCSuTwo_free_bond witnessU witnessEll targetCoarseBond
    (droppedBond witnessEll targetCoarseBond) Dc_inv
    (Pi.single ((site1 : PeriodicLatticeSite witnessL), (0 : Fin 3)) suTwoWitness)
    site1_ne_droppedBond
  rw [hzero] at hval
  simp only [LinearMap.zero_apply, Pi.zero_apply] at hval
  rw [Pi.single_eq_same] at hval
  exact suTwoWitness_ne_zero hval.symm

/-! ## §6 — GENUINE `U`-DEPENDENCE of the concrete `C` (scalar-carrier root-defect cure)

**SCOPE (2026-07-26):** both theorems are stated at `droppedBond` (offset `0`). They establish that
the su(2) carrier HOSTS `U`-dependence — a statement about the carrier, which does not depend on
which bond is dropped — but the specific maps they compare are built from the wrong `b₀`. The
corresponding statements at `ReparamCDisjoint.droppedBondLast` are NOT built here. -/

/-- **`rest_c` is genuinely `U`-dependent** on the witness data. Since `d4ConfigSuTwo` is supported
only at `(site1,0) ≠ b₀ = (witnessY,0)`, `dropZero_{b₀}` fixes it, so `rest_c(d4ConfigSuTwo) =
(Q₁(U)·d4ConfigSuTwo)(targetCoarseBond)`, which differs between `trivialU` and `witnessU`
(`lineCoarseRestrictCov_genuinely_U_dependent`, LAW-19). -/
theorem restFunctional_genuinely_U_dependent :
    restFunctional (trivialU witnessL) witnessEll targetCoarseBond
        (droppedBond witnessEll targetCoarseBond) d4ConfigSuTwo ≠
      restFunctional witnessU witnessEll targetCoarseBond
        (droppedBond witnessEll targetCoarseBond) d4ConfigSuTwo := by
  have hfix : dropZero (droppedBond witnessEll targetCoarseBond) d4ConfigSuTwo = d4ConfigSuTwo := by
    funext b
    rw [dropZero_apply]
    by_cases h : b = droppedBond witnessEll targetCoarseBond
    · rw [if_pos h, h]
      symm
      exact d4ConfigSuTwo_elsewhere site1_ne_droppedBond.symm
    · rw [if_neg h]
  have hval : ∀ U, restFunctional U witnessEll targetCoarseBond
      (droppedBond witnessEll targetCoarseBond) d4ConfigSuTwo =
      lineCoarseRestrictCov U witnessEll d4ConfigSuTwo targetCoarseBond := by
    intro U
    show constraintFunctional U witnessEll targetCoarseBond
        (dropZero (droppedBond witnessEll targetCoarseBond) d4ConfigSuTwo) = _
    rw [hfix, constraintFunctional_apply]
  rw [hval, hval]
  exact lineCoarseRestrictCov_genuinely_U_dependent

/-- **THE CONCRETE `C` IS GENUINELY `U`-DEPENDENT.** With the (natural) inverse `Dc_inv = ell⁴·id`,
the value of `C` on the dropped bond `b₀` is `−ell⁴·rest_c(B̃)`, which differs between `trivialU`
and `witnessU` on the witness input `d4ConfigSuTwo`. This is the su(2)-carrier cure of the convicted
`FaithfulCoercivity.lean` ROOT defect: the concrete (3.157) reparametrization genuinely HOSTS
`U`-dependence, which the scalar carrier provably could not. -/
theorem reparamCSuTwo_genuinely_U_dependent :
    reparamCSuTwo (trivialU witnessL) witnessEll targetCoarseBond
        (droppedBond witnessEll targetCoarseBond)
        ((witnessEll : ℝ)^4 • LinearMap.id) d4ConfigSuTwo
        (droppedBond witnessEll targetCoarseBond) ≠
      reparamCSuTwo witnessU witnessEll targetCoarseBond
        (droppedBond witnessEll targetCoarseBond)
        ((witnessEll : ℝ)^4 • LinearMap.id) d4ConfigSuTwo
        (droppedBond witnessEll targetCoarseBond) := by
  rw [reparamCSuTwo_at_b0, reparamCSuTwo_at_b0]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  intro hcontra
  apply restFunctional_genuinely_U_dependent
  have hne : ((witnessEll : ℝ)^4) ≠ 0 := by norm_num [witnessEll]
  have := neg_injective hcontra
  exact smul_right_injective SuTwo hne this

/-! ## §7 — how the concrete `C` makes `leadingReparamForm`'s target NON-VACUOUS (STATED, not proved)

`CStarDeltaKCSuTwo.free_C_coercivity_target_vacuous_at_zero_C` shows the degenerate `C = 0` makes
both the sandwich form AND the coarse-field RHS vanish, so a coercivity target over a FREE `C` is
vacuous. The concrete `C = reparamCSuTwo` here is provably NOT that degenerate map
(`reparamCSuTwo_ne_zero`): it is the identity on every free bond, so for a bond field `B̃` with a
nonzero free-bond component the reconstructed field `C B̃` is nonzero and its covariant coarse
average `Q_k(U)(C B̃) = lineCoarseRestrictCovLM U ell (C B̃)` is generically nonzero — hence the
coercivity inequality `γ₀ · ‖Q_k(U)(C B̃)‖² ≤ leadingReparamForm C B̃` has genuine content (its RHS
is not forced to `0`). Instantiating `CStarDeltaKCSuTwo.leadingReparamForm` at this concrete `C`
(rather than the generic `C` there) is the next brick; it is NOT done here, and NO coercivity
(`C*Δ_kC ≥ γ₀`) is claimed — that target stays the OPEN `def : Prop` in `CovariantHjFaithful` §5.
This remains an ISLAND. -/

#print axioms reparamCSuTwo_constraint
#print axioms coeffDc_witness
#print axioms coeffDc_witness_hinv
#print axioms reparamCSuTwo_witness_constraint
#print axioms constraintFunctional_reparamC_split
#print axioms reparamCSuTwo_free_bond
#print axioms reparamCSuTwo_at_b0
#print axioms reparamCSuTwo_ne_zero
#print axioms restFunctional_genuinely_U_dependent
#print axioms reparamCSuTwo_genuinely_U_dependent
#print axioms site1_ne_droppedBond
#print axioms droppedBond_eq_offset_zero
#print axioms droppedBond_eq_lastOffset_of_le_one
#print axioms droppedBond_ne_lastOffset_witness

end AdalyFormal.Balaban.ReparamCSuTwo
